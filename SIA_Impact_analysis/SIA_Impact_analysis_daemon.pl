#!/usr/bin/perl

###############################################################################
# Perl script to process SIA impact analysis and do the processing outside the 
# netcool processing tree as netcool is single threaded and uses the DB as
# its storage mechanism. 
# The goal is to enhance the processing times during an alarm storm.
#
# Design Notes:
# Store the Cramer data in a HASH and keep process alive to prevent reloading from DB 
# every 5 minutes. 
# Make all temp tables HOH tables for speed of processing and have a single write to 
# the DB at the end of the process.
# Set to run every 5 minutes. 
# Use Perl module Schedule::Cron to do process control and sleep between runs.
#
# Author:	Henri de Graaf
# Date:		08/08/2011
# Revision History
# 08/08/2011	V0.1 - Henri de Graaf - First Draft
# 19/09/2011	V0.2 - Richard Welter - Rework Circuit Data structure
# 28/09/2011	V0.3 - Richard Welter - Tele Protection processing added
# 03/10/2011	V0.4 - Richard Welter - fix empty BusPriority/superfluous comma
# 11/10/2011	V0.5 - Richard Welter - cleaned Synthetic_si_alarm_Trigger
# 17/10/2011	V0.6 - Richard Welter - fixes and convert prints to log messages
# 20/10/2011	V0.7 - Richard Welter - limit select from alerts.status DBtable
# 25/10/2011	V0.8 - Satish Kumar   - Updated buildLastAlarmIDHash to include scheme_tmp and sr_down_tmp, and updated TP services to use SR instance
# 25/10/2011	V0.9 - Satish Kumar   - Updated ResetRawEquipmentAlarm_newCycle method to include alerts of all Severity
# 25/10/2011	V0.10 - Satish Kumar  - Updated downgraded schemeroutes to have buspriority and subservice
# 26/10/2011	V0.11 - Richard Welter - added DB health check to deal with DB connection resets
# 07/11/2011	V0.12 - Richard Welter - fixes and added recursion loop protection
# 11/11/2011	V0.13 - Richard Welter - added mechanism to prevent duplicate FMSAlertKeys is alert_status_tmp
###############################################################################
use 5.8.5;
$|=1;

delete $ENV{PATH};
delete $ENV{BASH_ENV};

$ENV{'FREETDSCONF'}='/opt/alu/fms/config/tds.conf';

use DBI;
use File::Copy;
use IO::Socket;
use POSIX qw(strftime);
use Schedule::Cron;
use Time::Local;
use File::stat;
use strict;

# set Constants
use constant nl=>"\n";
use constant dl=>",";
use constant simpactUser=>'root';
use constant transpowerPort=>4111;
use constant simpactPwd=>'';
use constant transpowerServer=>'FMSOSP';
#use constant transpowerHost=>'xatsvr01app';
use constant transpowerHost=>'aalsun61';
use constant PrimaryQuery=>"select SvcInstance,ServerName_ServerSerial,BusPriority,ServicesImpacted,ImpactedStatus,SuppressEscl,Type,Severity,ServiceImpactingFlag,FMSAlertKey,ServiceID,SubService,LastOccurrence,ProtectingCircuit,ProtectedCircuit from alerts.status where Type = 1 and Severity > 3 and ServiceImpactingFlag = 1 and FMSAlertKey<>''";
use constant HealthCheck=>"select FMSAlertKey from alerts.status";

# Set Global Variables
my $Debug=0;
my $Dev = 0;
my $updatedInterval='0-59/3 * * * *';
my $serviceFileName = 'circuitProtection.lookup';
my $circuitFileName = 'cirlInfo.lookup';
my $schemeInfoFileName = 'schemeInfo.lookup';
my $schemeRouteFileName = 'schemeRoute.lookup';
my $schemeGroupFileName = 'schemeGroup.lookup';
my $LookupDir='/opt/alu/fms/data/';
my $LookupTimeStampFile='/opt/alu/fms/data/servImpactTSP.txt';
my $LogDir='/opt/alu/fms/logs/';
my $validationError="";
my %filesAndTimestamp =();
my %circuitProtection_HOH = ();
my %cirlInfo_HOH = ();
my %schemeInfo_HOH = ();
my %schemeRoute_HOH = ();
my %schemeGroup_HOH = ();
my %alerts_status_tmp = ();
my %circuits_tmp = ();
my $epochStore = 0;
my %cirlInfo_H;
my %cirlInfo_AK;
my %cirlInfo_CID;
my @circuitProtection_AOA;
my %circuitProtection_HOA;
my @schemeInfo_AOA;
my @schemeRoute_AOA;
my @schemeGroup_AOA;
my @alerts_status_tmp_AOA;
my @cirlInfo_AOA;
my %circuits_tmp_HOH = ();
my %circuits_tmp_sec_HOH = ();
my %svc_inst_tmp_HOH = ();
my %service_tmp_HOH = ();
my %sr_down_tmp_HOH = ();
my %scheme_tmp_HOH = ();
my %Synthetic_alarm_storage_HOH = ();
my %last_alarm_id = ();
my $Null_Summary = undef;
my $dbHandle = undef;
my $recursion = 0;

# set Development Headers
if ($Dev == 1) {
	$LookupDir='/opt/cramer/alu/fms/data/';
#	$LogDir='D:\\customer\\Transpower\\netcool perl project\\EProject\\';
#	$LookupDir='D:\\customer\\Transpower\\netcool perl project\\testData\\';
#	$LookupTimeStampFile='D:\\customer\\Transpower\\netcool perl project\\testData\\servImpactTSP.txt';
}

# Subroutines

sub dbInsert($$)
{
  my ($dbHandle,$statement)=@_;
  my $rst=0;
  if ($dbHandle) {
     $rst=$dbHandle->do($statement) or logWarn($dbHandle.', Failed to insert a record '.$!.$statement.nl);
  }
  return $rst;
}

sub dbUpdate($$)
{
  my ($dbHandle,$statement)=@_;
  my $rst=0;
  if ($dbHandle) {
     $rst=$dbHandle->do($statement) or logWarn($dbHandle.', Failed to insert a record '.$!.$statement.nl);
  }
  return $rst;
}

sub printTimeMarker($) {
    my ($TMarkerT) = @_;
  	my $tmarker = `date`;
        logInfo($TMarkerT.' '.$tmarker.nl);
}

sub checkServer($$)
{
  my ($host,$port)=@_;
  my $rc=0;
  $host=$host||'';
  $port=$port||0;
  my $socket=new IO::Socket::INET (PeerAddr=>"$host:$port",
                                   Proto=>'tcp',
                                   Timeout=>'3' ); # Timeout.
  if ($socket) {
    close($socket);
    $rc=1;
  }
  return($rc);
}

sub initDatabase($$$)
{
  my ($objServer,$host,$port)=@_;
  my $dbHandle=undef;
  if (checkServer($host,$port)) {
    $dbHandle=DBI->connect('DBI:Sybase:server='.$objServer,simpactUser,simpactPwd);
    if (not $dbHandle) {
	  logWarn($DBI::err.nl,$DBI::errstr.nl);
    }
  } else {
    	logWarn('Not available object server '.$objServer.' on '.$host.':'.$port.'.'.nl);
  }
  if (not $dbHandle) {
 	 logWarn('Failed to connect to object server '.$objServer.' on '.$host.':'.$port.'.'.nl);
  }
  return $dbHandle;
}

sub dbTest($)
{
  my ($dbHandle)=@_;
  my $rst=0;
  if ($dbHandle) {
     $rst=$dbHandle->do(HealthCheck) or logWarn($dbHandle.', Failed to run HealthCheck '.$!.HealthCheck.nl);
  }
  return $rst;
}

sub closeDatabase($)
{
  my ($dbHandleRef)=@_;
  if ($dbHandleRef) {
     $dbHandleRef->disconnect();
  }
}

sub exportAlertStatus() {
	my $alertExportFilename = $LookupDir . "alert.csv";
	open(ALERTFILE, '>'.$alertExportFilename) or logWarn('Unable to  open '.$alertExportFilename.nl);
	foreach my $hash_keyA(keys %alerts_status_tmp) {
	   my $Identifier = $alerts_status_tmp{$hash_keyA}->{'Identifier'};
       my $Serial = $alerts_status_tmp{$hash_keyA}->{'Serial'};
       my $Node = $alerts_status_tmp{$hash_keyA}->{'Node'};
       my $NodeAlias = $alerts_status_tmp{$hash_keyA}->{'NodeAlias'};
       my $Manager = $alerts_status_tmp{$hash_keyA}->{'Manager'};
       my $Agent = $alerts_status_tmp{$hash_keyA}->{'Agent'};
       my $AlertGroup = $alerts_status_tmp{$hash_keyA}->{'AlertGroup'};
       my $AlertKey = $alerts_status_tmp{$hash_keyA}->{'AlertKey'};
       my $Severity = $alerts_status_tmp{$hash_keyA}->{'Severity'};
       my $Summary = $alerts_status_tmp{$hash_keyA}->{'Summary'};
       my $StateChange = $alerts_status_tmp{$hash_keyA}->{'StateChange'};
       my $FirstOccurrence = $alerts_status_tmp{$hash_keyA}->{'FirstOccurrence'};
       my $LastOccurrence = $alerts_status_tmp{$hash_keyA}->{'LastOccurrence'};
       my $InternalLast = $alerts_status_tmp{$hash_keyA}->{'InternalLast'};
       my $Poll = $alerts_status_tmp{$hash_keyA}->{'Poll'};
       my $Type = $alerts_status_tmp{$hash_keyA}->{'Type'};
       my $Tally = $alerts_status_tmp{$hash_keyA}->{'Tally'};
       my $Class = $alerts_status_tmp{$hash_keyA}->{'Class'};
       my $Grade = $alerts_status_tmp{$hash_keyA}->{'Grade'};
       my $Location = $alerts_status_tmp{$hash_keyA}->{'Location'};
       my $OwnerUID = $alerts_status_tmp{$hash_keyA}->{'OwnerUID'};
       my $OwnerGID = $alerts_status_tmp{$hash_keyA}->{'OwnerGID'};
       my $Acknowledged = $alerts_status_tmp{$hash_keyA}->{'Acknowledged'};
       my $Flash = $alerts_status_tmp{$hash_keyA}->{'Flash'};
       my $EventId = $alerts_status_tmp{$hash_keyA}->{'EventId'};
       my $ExpireTime = $alerts_status_tmp{$hash_keyA}->{'ExpireTime'};
       my $ProcessReq = $alerts_status_tmp{$hash_keyA}->{'ProcessReq'};
       my $SuppressEscl = $alerts_status_tmp{$hash_keyA}->{'SuppressEscl'};
       my $Customer = $alerts_status_tmp{$hash_keyA}->{'Customer'};
       my $Service = $alerts_status_tmp{$hash_keyA}->{'Service'};
       my $PhysicalSlot = $alerts_status_tmp{$hash_keyA}->{'PhysicalSlot'};
       my $PhysicalPort = $alerts_status_tmp{$hash_keyA}->{'PhysicalPort'};
       my $PhysicalCard = $alerts_status_tmp{$hash_keyA}->{'PhysicalCard'};
       my $TaskList = $alerts_status_tmp{$hash_keyA}->{'TaskList'};
       my $NmosSerial = $alerts_status_tmp{$hash_keyA}->{'NmosSerial'};
       my $NmosObjInst = $alerts_status_tmp{$hash_keyA}->{'NmosObjInst'};
       my $NmosCauseType = $alerts_status_tmp{$hash_keyA}->{'NmosCauseType'};
       my $LocalNodeAlias = $alerts_status_tmp{$hash_keyA}->{'LocalNodeAlias'};
       my $LocalPriObj = $alerts_status_tmp{$hash_keyA}->{'LocalPriObj'};
       my $LocalSecObj = $alerts_status_tmp{$hash_keyA}->{'LocalSecObj'};
       my $LocalRootObj = $alerts_status_tmp{$hash_keyA}->{'LocalRootObj'};
       my $RemoteNodeAlias = $alerts_status_tmp{$hash_keyA}->{'RemoteNodeAlias'};
       my $RemotePriObj = $alerts_status_tmp{$hash_keyA}->{'RemotePriObj'};
       my $RemoteSecObj = $alerts_status_tmp{$hash_keyA}->{'RemoteSecObj'};
       my $RemoteRootObj = $alerts_status_tmp{$hash_keyA}->{'RemoteRootObj'};
       my $X733EventType = $alerts_status_tmp{$hash_keyA}->{'X733EventType'};
       my $X733ProbableCause = $alerts_status_tmp{$hash_keyA}->{'X733ProbableCause'};
       my $X733SpecificProb = $alerts_status_tmp{$hash_keyA}->{'X733SpecificProb'};
       my $X733CorrNotif = $alerts_status_tmp{$hash_keyA}->{'X733CorrNotif'};
       my $URL = $alerts_status_tmp{$hash_keyA}->{'URL'};
       my $AlertStatus = $alerts_status_tmp{$hash_keyA}->{'AlertStatus'};
       my $AlertType= $alerts_status_tmp{$hash_keyA}->{'AlertType'};
       my $ManagedObjClass = $alerts_status_tmp{$hash_keyA}->{'ManagedObjClass'};
       my $CorrNotif = $alerts_status_tmp{$hash_keyA}->{'CorrNotif'};
       my $EventType = $alerts_status_tmp{$hash_keyA}->{'EventType'};
       my $ProbableCause = $alerts_status_tmp{$hash_keyA}->{'ProbableCause'};
       my $SpecificProb = $alerts_status_tmp{$hash_keyA}->{'SpecificProb'};
       my $CommissionedState = $alerts_status_tmp{$hash_keyA}->{'CommissionedState'};
       my $EquipmentKey = $alerts_status_tmp{$hash_keyA}->{'EquipmentKey'};
       my $EquipmentRole = $alerts_status_tmp{$hash_keyA}->{'EquipmentRole'};
       my $EquipmentType = $alerts_status_tmp{$hash_keyA}->{'EquipmentType'};
       my $ProbeSerial = $alerts_status_tmp{$hash_keyA}->{'ProbeSerial'};
       my $ParentPointer= $alerts_status_tmp{$hash_keyA}->{'ParentPointer'};
       my $ServerName_ServerSerial = $alerts_status_tmp{$hash_keyA}->{'ServerName_ServerSerial'};
       my $SourceServerName = $alerts_status_tmp{$hash_keyA}->{'SourceServerName'};
       my $SourceServerSerial = $alerts_status_tmp{$hash_keyA}->{'SourceServerSerial'};
       my $SourceStateChange= $alerts_status_tmp{$hash_keyA}->{'SourceStateChange'};
       my $SrcDomain = $alerts_status_tmp{$hash_keyA}->{'SrcDomain'};
       my $SwVersion = $alerts_status_tmp{$hash_keyA}->{'SwVersion'};
       my $TopologyKey= $alerts_status_tmp{$hash_keyA}->{'TopologyKey'};
       my $ClearTally= $alerts_status_tmp{$hash_keyA}->{'ClearTally'};
       my $ClearTimestamp = $alerts_status_tmp{$hash_keyA}->{'ClearTimestamp'};
       my $OriginalSeverity = $alerts_status_tmp{$hash_keyA}->{'OriginalSeverity'};
       my $ServiceID = $alerts_status_tmp{$hash_keyA}->{'ServiceID'};
       my $ServiceTitle = $alerts_status_tmp{$hash_keyA}->{'ServiceTitle'};
       my $SubService = $alerts_status_tmp{$hash_keyA}->{'SubService'};
       my $ProtectedCircuit = $alerts_status_tmp{$hash_keyA}->{'ProtectedCircuit'};
       my $ProtectingCircuit = $alerts_status_tmp{$hash_keyA}->{'ProtectingCircuit'};
       my $ServiceImpactingFlag = $alerts_status_tmp{$hash_keyA}->{'ServiceImpactingFlag'};
       my $ServicesImpacted = $alerts_status_tmp{$hash_keyA}->{'ServicesImpacted'};
       my $ServiceType = $alerts_status_tmp{$hash_keyA}->{'ServiceType'};
       my $SvcInstance = $alerts_status_tmp{$hash_keyA}->{'SvcInstance'};
       my $BusPriority = $alerts_status_tmp{$hash_keyA}->{'BusPriority'};
       my $ImpactedStatus = $alerts_status_tmp{$hash_keyA}->{'ImpactedStatus'};
       my $PossibleRootCause = $alerts_status_tmp{$hash_keyA}->{'PossibleRootCause'};
       my $TTFlag = $alerts_status_tmp{$hash_keyA}->{'TTFlag'};
       my $TTPriority = $alerts_status_tmp{$hash_keyA}->{'TTPriority'};
       my $TTProblemDesc= $alerts_status_tmp{$hash_keyA}->{'TTProblemDesc'};
       my $TTRequestTime= $alerts_status_tmp{$hash_keyA}->{'TTRequestTime'};
       my $TTSequence = $alerts_status_tmp{$hash_keyA}->{'TTSequence'};
       my $TTServer = $alerts_status_tmp{$hash_keyA}->{'TTServer'};
       my $TTServiceAffected = $alerts_status_tmp{$hash_keyA}->{'TTServiceAffected'};
       my $TTSLACommit = $alerts_status_tmp{$hash_keyA}->{'TTSLACommit'};
       my $TTStatus = $alerts_status_tmp{$hash_keyA}->{'TTStatus'};
       my $TTUpdate = $alerts_status_tmp{$hash_keyA}->{'TTUpdate'};
       my $TTUser = $alerts_status_tmp{$hash_keyA}->{'TTUser'};
       my $TTWaitTime = $alerts_status_tmp{$hash_keyA}->{'TTWaitTime'};
       my $ProblemId = $alerts_status_tmp{$hash_keyA}->{'ProblemId'};
       my $ProblemStatus = $alerts_status_tmp{$hash_keyA}->{'ProblemStatus'};
       my $OutageAdviceTime= $alerts_status_tmp{$hash_keyA}->{'OutageAdviceTime'};
       my $OutagePlannedEndTime = $alerts_status_tmp{$hash_keyA}->{'OutagePlannedEndTime'};
       my $OutagePlannedStartTime = $alerts_status_tmp{$hash_keyA}->{'OutagePlannedStartTime'};
       my $Region = $alerts_status_tmp{$hash_keyA}->{'Region'};
       my $AdditionalText = $alerts_status_tmp{$hash_keyA}->{'AdditionalText'};
       my $AlarmDetails = $alerts_status_tmp{$hash_keyA}->{'AlarmDetails'};
       my $FMSAlertKey = $alerts_status_tmp{$hash_keyA}->{'FMSAlertKey'};
       my $RawAlarmID = $alerts_status_tmp{$hash_keyA}->{'RawAlarmID'};
       my $ServerName = $alerts_status_tmp{$hash_keyA}->{'ServerName'};
       my $ServerSerial = $alerts_status_tmp{$hash_keyA}->{'ServerSerial'};
       my $TTGroup = $alerts_status_tmp{$hash_keyA}->{'TTGroup'};
       my $TTParentPointer = $alerts_status_tmp{$hash_keyA}->{'TTParentPointer'}; 

       # Print variables into export file
       print ALERTFILE $Identifier.dl.$Serial.dl.$Node.dl.$NodeAlias.dl.$Manager.dl.
       $Agent.dl.$AlertGroup.dl.$AlertKey.dl.$Severity.dl.$Summary.dl.$StateChange.dl.
       $FirstOccurrence.dl.$LastOccurrence.dl.$InternalLast.dl.$Poll.dl.$Type.dl.
       $Tally.dl.$Class.dl.$Grade.dl.$Location.dl.$OwnerUID.dl.$OwnerGID.dl.
       $Acknowledged.dl.$Flash.dl.$EventId.dl.$ExpireTime.dl.$ProcessReq.dl.
       $SuppressEscl.dl.$Customer.dl.$Service.dl.$PhysicalSlot.dl.$PhysicalPort.dl.
       $PhysicalCard.dl.$TaskList.dl.$NmosSerial.dl.$NmosObjInst.dl.$NmosCauseType.dl.
       $LocalNodeAlias.dl.$LocalPriObj.dl.$LocalSecObj.dl.$LocalRootObj.dl.$RemoteNodeAlias.dl.
       $RemotePriObj.dl.$RemoteSecObj.dl.$RemoteRootObj.dl.
       $X733EventType.dl.$X733ProbableCause.dl.$X733SpecificProb.dl.$X733CorrNotif.dl.
       $URL.dl.$AlertStatus.dl.$AlertType.dl.$ManagedObjClass.dl.$CorrNotif.dl.
       $EventType.dl.$ProbableCause.dl.$SpecificProb.dl.$CommissionedState.dl.
       $EquipmentKey.dl.$EquipmentRole.dl.$EquipmentType.dl.$ProbeSerial.dl.$ParentPointer.dl.
       $ServerName_ServerSerial.dl.$SourceServerName.dl.$SourceServerSerial.dl.
       $SourceStateChange.dl.$SrcDomain.dl.$SwVersion.dl.$TopologyKey.dl.$ClearTally.dl.
       $ClearTimestamp.dl.$OriginalSeverity.dl.$ServiceID.dl.$ServiceTitle.dl.
       $SubService.dl.$ProtectedCircuit.dl.$ProtectingCircuit.dl.$ServiceImpactingFlag.dl.
       $ServicesImpacted.dl.$ServiceType.dl.$SvcInstance.dl.$BusPriority.dl.
       $ImpactedStatus.dl.$PossibleRootCause.dl.$TTFlag.dl.$TTPriority.dl.$TTProblemDesc.dl.
       $TTRequestTime.dl.$TTSequence.dl.$TTServer.dl.$TTServiceAffected.dl.
       $TTSLACommit.dl.$TTStatus.dl.$TTUpdate.dl.$TTUser.dl.$TTWaitTime.dl.
       $ProblemId.dl.$ProblemStatus.dl.$OutageAdviceTime.dl.$OutagePlannedEndTime.dl.
       $OutagePlannedStartTime.dl.$Region.dl.$AdditionalText.dl.$AlarmDetails.dl.
       $FMSAlertKey.dl.$RawAlarmID.dl.$ServerName.dl.$ServerSerial.dl.$TTGroup.dl.
       $TTParentPointer.nl;
	}
	close(ALERTFILE);
}

sub dbSelect($$)
{
  my ($dbHandle,$statement)=@_;
  my $rst=0;
  my $RecordCount = 0;
  if ($dbHandle) {
     my @data;
     my $sth = $dbHandle->prepare($statement);
     $sth->execute();
     my $TMarkerT = "Loading alerts.status"; 
     printTimeMarker($TMarkerT);
     while (@data = $sth->fetchrow_array) {
     	# use array for like matching speed 
        # clean the data and import
		my $AData = ConvertArrayToCleanString(@data);
#		logInfo($RecordCount.' '.$AData.nl);
#	   { push @alerts_status_tmp_AOA, [ split(/~/,$AData) ]; }
	   #Clean the data for HASH
	   my @Cdata = split(/~/,$AData);
# we only want to store 1 of each FMSAlertKey, the largest LastOccurence
       my $newFMSAlertKey = checkData($Cdata[9]);
       my $newLastOccurrence = checkData($Cdata[12]);
       my $store = 1;
       foreach my $hash_keyA(keys %alerts_status_tmp) {
          my $AS_FMSAlertKey = $alerts_status_tmp{$hash_keyA}->{'FMSAlertKey'};
          my $AS_LastOccurrence = $alerts_status_tmp{$hash_keyA}->{'LastOccurrence'};
          if ($newFMSAlertKey eq $AS_FMSAlertKey) {
            if ($newLastOccurrence gt $AS_LastOccurrence) {
	          $alerts_status_tmp{$hash_keyA}->{'SvcInstance'} = checkData($Cdata[0]);
	          $alerts_status_tmp{$hash_keyA}->{'ServerName_ServerSerial'} = checkData($Cdata[1]);
	          $alerts_status_tmp{$hash_keyA}->{'BusPriority'} = checkData($Cdata[2]);
	          $alerts_status_tmp{$hash_keyA}->{'ServicesImpacted'} = checkData($Cdata[3]);
	          $alerts_status_tmp{$hash_keyA}->{'ImpactedStatus'} = checkData($Cdata[4]);
	          $alerts_status_tmp{$hash_keyA}->{'SuppressEscl'} = checkData($Cdata[5]);
	          $alerts_status_tmp{$hash_keyA}->{'Type'} = checkData($Cdata[6]);
	          $alerts_status_tmp{$hash_keyA}->{'Severity'} = checkData($Cdata[7]);
	          $alerts_status_tmp{$hash_keyA}->{'ServiceImpactingFlag'} = checkData($Cdata[8]);
	          $alerts_status_tmp{$hash_keyA}->{'FMSAlertKey'} = checkData($Cdata[9]);
	          $alerts_status_tmp{$hash_keyA}->{'ServiceID'} = checkData($Cdata[10]);
	          $alerts_status_tmp{$hash_keyA}->{'SubService'} = checkData($Cdata[11]);
	          $alerts_status_tmp{$hash_keyA}->{'LastOccurrence'} = checkData($Cdata[12]);
	          $alerts_status_tmp{$hash_keyA}->{'ProtectingCircuit'} = checkData($Cdata[13]);
	          $alerts_status_tmp{$hash_keyA}->{'ProtectedCircuit'} = checkData($Cdata[14]);
              $store = 1;
            }
            else { $store = 0 }
            last;
          }
       }
	   # use hash for exact matching speed
	   if ($store) {
	       $alerts_status_tmp{$RecordCount}->{'SvcInstance'} = checkData($Cdata[0]);
	       $alerts_status_tmp{$RecordCount}->{'ServerName_ServerSerial'} = checkData($Cdata[1]);
	       $alerts_status_tmp{$RecordCount}->{'BusPriority'} = checkData($Cdata[2]);
	       $alerts_status_tmp{$RecordCount}->{'ServicesImpacted'} = checkData($Cdata[3]);
	       $alerts_status_tmp{$RecordCount}->{'ImpactedStatus'} = checkData($Cdata[4]);
	       $alerts_status_tmp{$RecordCount}->{'SuppressEscl'} = checkData($Cdata[5]);
	       $alerts_status_tmp{$RecordCount}->{'Type'} = checkData($Cdata[6]);
	       $alerts_status_tmp{$RecordCount}->{'Severity'} = checkData($Cdata[7]);
	       $alerts_status_tmp{$RecordCount}->{'ServiceImpactingFlag'} = checkData($Cdata[8]);
	       $alerts_status_tmp{$RecordCount}->{'FMSAlertKey'} = checkData($Cdata[9]);
	       $alerts_status_tmp{$RecordCount}->{'ServiceID'} = checkData($Cdata[10]);
	       $alerts_status_tmp{$RecordCount}->{'SubService'} = checkData($Cdata[11]);
	       $alerts_status_tmp{$RecordCount}->{'LastOccurrence'} = checkData($Cdata[12]);
	       $alerts_status_tmp{$RecordCount}->{'ProtectingCircuit'} = checkData($Cdata[13]);
	       $alerts_status_tmp{$RecordCount}->{'ProtectedCircuit'} = checkData($Cdata[14]);
           $RecordCount++;
	   }
     }
     $TMarkerT = "Loaded alerts.status";
     printTimeMarker($TMarkerT);
     logInfo($RecordCount.' rows loaded into alerts.status'.nl);
#     printFMSAlertKey();
  }
}

sub openLogFileHandle()
{
  my $logFileHandle;
  if ($LogDir) {
    my $timePrefix=strftime("%Y-%m-%d",localtime(time())).'_';
    open($logFileHandle,'>>'.$LogDir.$timePrefix.'SIA_Impact_analysis.log') or $logFileHandle=undef;
  }
  return($logFileHandle);
}

sub closeLogFileHandle($)
{
  my ($logFileHandle)=@_;
  close($logFileHandle);
}

sub emptyDataStores() {
   my $TMarkerT = "emptying the data stores";
   printTimeMarker($TMarkerT);
   %circuitProtection_HOH = ();
   %cirlInfo_HOH = ();
   %schemeInfo_HOH = ();
   %schemeRoute_HOH = ();
   %schemeGroup_HOH = ();
   %alerts_status_tmp = ();
   %circuits_tmp = ();
   %cirlInfo_H = ();
   %cirlInfo_AK = ();
   %cirlInfo_CID = ();
   %circuits_tmp_HOH = ();
   %circuits_tmp_sec_HOH = ();
   %svc_inst_tmp_HOH = ();
   %service_tmp_HOH = ();
   %sr_down_tmp_HOH = ();
   %scheme_tmp_HOH = ();
   %Synthetic_alarm_storage_HOH = ();
   %circuitProtection_HOA = ();
   %last_alarm_id = ();
   undef(@circuitProtection_AOA);
   undef(@schemeInfo_AOA);
   undef(@schemeRoute_AOA);
   undef(@schemeGroup_AOA);
#   undef(@alerts_status_tmp_AOA);
   undef(@cirlInfo_AOA);
}

sub perfCalc($$){
	# Simple time calc. Only does a single event per time.
	my ($category,$module) = @_;
	my $time = time();
	if ($category eq 'start') {
		$epochStore = $time;
	}
	if ($category eq 'end') {
		my $diff = $time - $epochStore ;
		logInfo('Time Taken for '.$module.' is '.$diff.' seconds'.nl);
	}
}

sub print_sr_down_tmp_HOH() {
    logInfo('Printing sr_down_tmp'.nl);
    foreach my $hash_key(keys %sr_down_tmp_HOH) {
       my $count = $sr_down_tmp_HOH{$hash_key}->{'count'};
       my $FMSAlertKey = $sr_down_tmp_HOH{$hash_key}->{'FMSAlertKey'};
       my $RawAlarmID = $sr_down_tmp_HOH{$hash_key}->{'RawAlarmID'};
       my $ProtectingCircuit = $sr_down_tmp_HOH{$hash_key}->{'ProtectingCircuit'};
       my $ProtectedCircuit = $sr_down_tmp_HOH{$hash_key}->{'ProtectedCircuit'};
       my $protected = $sr_down_tmp_HOH{$hash_key}->{'IsCirProtected'};
       my $SRInstance = $sr_down_tmp_HOH{$hash_key}->{'SRInstance'};
       my $SSInstance = $sr_down_tmp_HOH{$hash_key}->{'SSInstance'};
       my $SvcInstance = $sr_down_tmp_HOH{$hash_key}->{'SvcInstance'};
       my $SRProvisionStatus = $sr_down_tmp_HOH{$hash_key}->{'SRProvisionStatus'};
       my $SSProvisionStatus = $sr_down_tmp_HOH{$hash_key}->{'SSProvisionStatus'};
       my $SvcProvisionStatus = $sr_down_tmp_HOH{$hash_key}->{'SvcProvisionStatus'};
       my $SS_Status = $sr_down_tmp_HOH{$hash_key}->{'SS_Status'};
       my $Svc_Status = $sr_down_tmp_HOH{$hash_key}->{'Svc_Status'};
       my $Svc_ServiceID = $sr_down_tmp_HOH{$hash_key}->{'Svc_ServiceID'};
       my $Svc_SubSvcName = $sr_down_tmp_HOH{$hash_key}->{'Svc_SubSvcName'};
       my $Svc_BusPriority = $sr_down_tmp_HOH{$hash_key}->{'Svc_BusPriority'};
       my $SGInstance = $sr_down_tmp_HOH{$hash_key}->{'SGInstance'};
       my $SGProvisionStatus = $sr_down_tmp_HOH{$hash_key}->{'SGProvisionStatus'};
       my $SG_Status = $sr_down_tmp_HOH{$hash_key}->{'SG_Status'};
       my $Summary = $sr_down_tmp_HOH{$hash_key}->{'Summary'};
       my $SR_Status = $sr_down_tmp_HOH{$hash_key}->{'SR_Status'};
       logInfo("$count,$FMSAlertKey,$RawAlarmID,$ProtectingCircuit,$ProtectedCircuit,$protected,$SRInstance".
       ",$SSInstance,$SvcInstance,$SRProvisionStatus,$SSProvisionStatus,$SvcProvisionStatus,$SS_Status,".
       "$Svc_Status,$Svc_ServiceID,$Svc_SubSvcName,$Svc_BusPriority,$SGInstance,$SGProvisionStatus,".
       "$SG_Status,$Summary,$SR_Status".nl);
    }
}

sub print_scheme_tmp_HOH() {
    logInfo('Printing scheme_tmp'.nl);
    foreach my $hash_key(keys %scheme_tmp_HOH) {
       logInfo("$scheme_tmp_HOH{$hash_key}->{'count'},$scheme_tmp_HOH{$hash_key}->{'FMSAlertKey'},".
       "$scheme_tmp_HOH{$hash_key}->{'RawAlarmID'},$scheme_tmp_HOH{$hash_key}->{'ProtectingCircuit'},".
       "$scheme_tmp_HOH{$hash_key}->{'ProtectedCircuit'},$scheme_tmp_HOH{$hash_key}->{'IsCirProtected'},".
       "$scheme_tmp_HOH{$hash_key}->{'SRInstance'},$scheme_tmp_HOH{$hash_key}->{'SSInstance'},".
       "$scheme_tmp_HOH{$hash_key}->{'SvcInstance'},$scheme_tmp_HOH{$hash_key}->{'SRProvisionStatus'},".
       "$scheme_tmp_HOH{$hash_key}->{'SSProvisionStatus'},$scheme_tmp_HOH{$hash_key}->{'SvcProvisionStatus'}".
       ",$scheme_tmp_HOH{$hash_key}->{'SS_Status'},$scheme_tmp_HOH{$hash_key}->{'Svc_Status'},".
       "$scheme_tmp_HOH{$hash_key}->{'Svc_ServiceID'},$scheme_tmp_HOH{$hash_key}->{'Svc_SubSvcName'},".
       "$scheme_tmp_HOH{$hash_key}->{'Svc_BusPriority'},$scheme_tmp_HOH{$hash_key}->{'SGInstance'},".
       "$scheme_tmp_HOH{$hash_key}->{'SGProvisionStatus'},$scheme_tmp_HOH{$hash_key}->{'SG_Status'},".
       "$scheme_tmp_HOH{$hash_key}->{'Summary'},$scheme_tmp_HOH{$hash_key}->{'SR_Status'}".nl);
    }
}

sub print_Synthetic_alarm_HOH() {
	logInfo('Printing Synthetic_alarm'.nl);
	my $rowcount =0;
	my $maxrows = scalar(keys %Synthetic_alarm_storage_HOH);
	foreach my $hash_key(keys %Synthetic_alarm_storage_HOH) {
		my $SA_SvcInstance = $Synthetic_alarm_storage_HOH{$hash_key}->{'SvcInstance'};
		my $SA_ServiceStatus = $Synthetic_alarm_storage_HOH{$hash_key}->{'ServiceStatus'};
		my $SA_FMSAlertKey = $Synthetic_alarm_storage_HOH{$hash_key}->{'FMSAlertKey'};
		my $SA_ProvisionStatus = $Synthetic_alarm_storage_HOH{$hash_key}->{'ProvisionStatus'};
		my $SA_ProtectedCircuit = $Synthetic_alarm_storage_HOH{$hash_key}->{'ProtectedCircuit'} ;
		my $SA_ProtectingCircuit = $Synthetic_alarm_storage_HOH{$hash_key}->{'ProtectingCircuit'};
		my $SA_BusPriority = $Synthetic_alarm_storage_HOH{$hash_key}->{'BusPriority'};
		my $SA_BusSvcName = $Synthetic_alarm_storage_HOH{$hash_key}->{'BusSvcName'};
		my $SA_SubSvcName = $Synthetic_alarm_storage_HOH{$hash_key}->{'SubSvcName'};
		my $SA_RawAlarmID = $Synthetic_alarm_storage_HOH{$hash_key}->{'RawAlarmID'};
		my $SA_Number = $Synthetic_alarm_storage_HOH{$hash_key}->{'Number'};
		
		$rowcount++;
		#logInfo('synthetic alarm count '.$rowcount.' out of '.$maxrows.nl);
		logInfo("$SA_SvcInstance $SA_ServiceStatus $SA_FMSAlertKey $SA_ProvisionStatus $SA_ProtectedCircuit".
		" $SA_ProtectingCircuit $SA_BusPriority $SA_BusSvcName $SA_SubSvcName $SA_RawAlarmID $SA_Number".nl);
		$rowcount++;
	}
}

sub printcircuits_tmp() {
	logInfo('Printing circuits_tmp'.nl);
	foreach my $Hash_key(keys %circuits_tmp_HOH) {
		my $count = $circuits_tmp_HOH{$Hash_key}->{'count'};
		my $FMSAlertKey = $circuits_tmp_HOH{$Hash_key}->{'FMSAlertKey'};
   		my $CircuitID = $circuits_tmp_HOH{$Hash_key}->{'CircuitID'};
    	my $RawAlarmID = $circuits_tmp_HOH{$Hash_key}->{'RawAlarmID'};
		logInfo($count,$FMSAlertKey,$CircuitID,$RawAlarmID.nl);
	}
}

sub printFMSAlertKey() {
	foreach my $Hash_key(keys %alerts_status_tmp) {
		my $FMSAK = $alerts_status_tmp{$Hash_key}->{'FMSAlertKey'};
		logInfo($FMSAK.nl);
	}
}

sub printRawAlarmID {
	foreach my $Hash_key(keys %last_alarm_id) {
		my $FMSAK = $last_alarm_id{$Hash_key}->{'FMSAlertKey'};
		my $alarm = $last_alarm_id{$Hash_key}->{'RawAlarmID'};
		logInfo('-- last alarm ID for service: '.$Hash_key.'->'.$alarm.' AlertKey: '.$FMSAK.nl);
	}
}

sub PrintFourArrays(){
	my $SVI_count = scalar(keys %svc_inst_tmp_HOH);
	my $ST_count = scalar(keys %service_tmp_HOH);
	my $SRD_count = scalar(keys %sr_down_tmp_HOH);
	my $Scheme_tmp_count = scalar(keys %scheme_tmp_HOH);
	logInfo("Temp table basic analysis of data".nl.
	 "Number of records in svc_inst_tmp is $SVI_count".nl.
	 "Number of records in service_tmp is $ST_count".nl.
	 "Number of records in sr_down_tmp is $SRD_count".nl.
	 "Number of records in scheme_tmp is $Scheme_tmp_count".nl);
}

sub printservice_tmp() {
	logInfo('Printing service_tmp'.nl);
	foreach my $Hash_key(keys %service_tmp_HOH) {
		my $count = $service_tmp_HOH{$Hash_key}->{'count'};
		my $FMSAlertKey = $service_tmp_HOH{$Hash_key}->{'FMSAlertKey'};
   		my $SvcInstance = $service_tmp_HOH{$Hash_key}->{'SvcInstance'};
     	my $ProvisionStatus = $service_tmp_HOH{$Hash_key}->{'ProvisionStatus'}; 
     	my $ProtectedCircuit = $service_tmp_HOH{$Hash_key}->{'ProtectedCircuit'}; 
     	my $ProtectingCircuit = $service_tmp_HOH{$Hash_key}->{'ProtectingCircuit'}; 
     	my $BusSvcName = $service_tmp_HOH{$Hash_key}->{'BusSvcName'}; 
     	my $SubSvcName = $service_tmp_HOH{$Hash_key}->{'SubSvcName'}; 
     	my $ServicePriority = $service_tmp_HOH{$Hash_key}->{'BusPriority'};  		
    	my $RawAlarmID = $service_tmp_HOH{$Hash_key}->{'RawAlarmID'};
		logInfo("$count,$FMSAlertKey,$SvcInstance,$ProvisionStatus,$ProtectedCircuit,".
		"$ProtectingCircuit,$BusSvcName,$SubSvcName,$ServicePriority,$RawAlarmID".nl);
	}
}

sub printsvc_inst_tmp() {
	logInfo('Printing svc_inst_tmp'.nl);
	foreach my $Hash_key(keys %svc_inst_tmp_HOH) {
		my $count = $svc_inst_tmp_HOH{$Hash_key}->{'count'};
		my $FMSAlertKey = $svc_inst_tmp_HOH{$Hash_key}->{'FMSAlertKey'};
   		my $SvcInstance = $svc_inst_tmp_HOH{$Hash_key}->{'SvcInstance'};
   		my $ProvisionStatus = $svc_inst_tmp_HOH{$Hash_key}->{'ProvisionStatus'};
   		my $ProtectedCircuit = $svc_inst_tmp_HOH{$Hash_key}->{'ProtectedCircuit'};
   		my $ProtectingCircuit = $svc_inst_tmp_HOH{$Hash_key}->{'ProtectingCircuit'};
   		my $BusSvcName = $svc_inst_tmp_HOH{$Hash_key}->{'BusSvcName'};
   		my $SubSvcName = $svc_inst_tmp_HOH{$Hash_key}->{'SubSvcName'};
   		my $ServicePriority = $svc_inst_tmp_HOH{$Hash_key}->{'BusPriority'};
    	my $RawAlarmID = $svc_inst_tmp_HOH{$Hash_key}->{'RawAlarmID'};
		logInfo("$count,$FMSAlertKey,$SvcInstance,$ProvisionStatus,$ProtectedCircuit,".
		"$ProtectingCircuit,$BusSvcName,$SubSvcName,$ServicePriority,$RawAlarmID".nl);
	}
}

sub update_tp_summary() {
    foreach my $hash_keyA(keys %scheme_tmp_HOH) {
       my $ss_status = '';
       my $svc_status = '';
       my $ST_Svc_Status = $scheme_tmp_HOH{$hash_keyA}->{'Svc_Status'};
       my $ST_SvcInstance = $scheme_tmp_HOH{$hash_keyA}->{'SvcInstance'};
       if ($ST_Svc_Status eq '') {
          $svc_status = 'Normal';
       } elsif ($ST_Svc_Status =~ /Svc Loss/) {
          $svc_status = 'Loss';
       } elsif ($ST_Svc_Status =~ /Svc Downgraded/) {
          $svc_status = 'Downgraded';
       }
       
       my $summary = $ST_SvcInstance . ' ' . $svc_status . ' : ';
       # Get All SchemeGroups under BS
       foreach my $hash_keyB(keys %schemeGroup_HOH) {
          my $SG_SvcInstance = $schemeGroup_HOH{$hash_keyB}->{'SvcInstance'};
          if ($SG_SvcInstance eq $ST_SvcInstance) {
             my $SG_ProtectedScheme = $schemeGroup_HOH{$hash_keyB}->{'ProtectedScheme'};
             $summary = $summary . $SG_ProtectedScheme . ' : ';
             # Get All SchemeService under SG
             foreach my $hash_keyC(keys %schemeInfo_HOH) {
                my $SS_SvcInstance = $schemeInfo_HOH{$hash_keyC}->{'SvcInstance'};
                if ($SS_SvcInstance eq $SG_ProtectedScheme) {
                   my $SS_ProtectedSS_Status = $schemeInfo_HOH{$hash_keyC}->{'ProtectedSS_Status'};
                   my $SS_ProtectedScheme = $schemeInfo_HOH{$hash_keyC}->{'ProtectedScheme'};
                   if ($SS_ProtectedSS_Status eq '') {
                      $ss_status = 'Normal';
                   } elsif ($SS_ProtectedSS_Status =~ /SS Loss/) {
                      $ss_status = 'Loss';
                   } elsif ($SS_ProtectedSS_Status =~ /SS Downgraded/) {
                      $ss_status = 'Downgraded';
                   }
                   $summary = $summary . $SS_ProtectedScheme . ' ' . $ss_status . ' ';
                }
             }
          }
       }
       $scheme_tmp_HOH{$hash_keyA}->{'Summary'} = $summary;
    }
}

sub SIA_process_TP_svcs1($){
	# this is for teleprotection (TP) services.
	my ($dbHandle)= @_;
	logInfo('Starting SIA Process TP svcs 1'.nl); 
	perfCalc('start','SIA_process_TP_svcs1');
               logInfo('TP step 1'.nl);
               print_scheme_tmp_HOH();
               print_sr_down_tmp_HOH();

  my $change = 0;
  do {
	$change = 0;
	foreach my $hash_keyA(keys %sr_down_tmp_HOH) {
	  my $SRD_SRInstance = $sr_down_tmp_HOH{$hash_keyA}->{'SRInstance'};
	  my $SRD_FMSAlertKey = $sr_down_tmp_HOH{$hash_keyA}->{'FMSAlertKey'};
	  my $SRD_ProtectedCircuit = $sr_down_tmp_HOH{$hash_keyA}->{'ProtectedCircuit'};
	  my $SRD_SvcInstance = $sr_down_tmp_HOH{$hash_keyA}->{'SvcInstance'};
	  foreach my $hash_keyB(keys %scheme_tmp_HOH) {
	  	my $ST_FMSAlertKey = $scheme_tmp_HOH{$hash_keyB}->{'FMSAlertKey'};
	  	my $ST_SRInstance = $scheme_tmp_HOH{$hash_keyB}->{'SRInstance'};
	  	my $ST_ProtectedCircuit = $scheme_tmp_HOH{$hash_keyB}->{'ProtectedCircuit'};
	  	my $ST_SvcInstance = $scheme_tmp_HOH{$hash_keyB}->{'SvcInstance'};
	  	if ( ($SRD_SRInstance eq $ST_SRInstance) &&
	  	     (($ST_FMSAlertKey =~ /$SRD_FMSAlertKey/) || ($SRD_FMSAlertKey =~ /$ST_FMSAlertKey/)) &&
	  	     (isInHierarchy($SRD_ProtectedCircuit,$ST_ProtectedCircuit,$SRD_SRInstance)) &&
	  	     (HierarchySafe($SRD_ProtectedCircuit,$ST_ProtectedCircuit,$SRD_SRInstance,'scheme_tmp')) ) {
	  		#logInfo('Match moved'.nl);
	  		$change = 1;
	  		copy_scheme_tmp_to_sr_down_tmp($scheme_tmp_HOH{$hash_keyB});
	  		delete $scheme_tmp_HOH{$hash_keyB}; # actually moved to $sr_down_tmp_HOH
	  	}
	  }
	}
               logInfo('TP step 2'.nl);
               print_scheme_tmp_HOH();
               print_sr_down_tmp_HOH();
	
	###########################################################
	# Some services that have now been removed from service_tmp need to be revisited as they no longer 
	# cause their protected circuit to be down. 
 	# Once the protected circuits are removed, Remove all underlying circuits from scheme_tmp as well.
 	############################################################
	foreach my $hash_keyA(keys %scheme_tmp_HOH) {
		my $lossfound = "FALSE";
		my $CTS_ProtectingCircuit = $scheme_tmp_HOH{$hash_keyA}->{'ProtectingCircuit'};
		my $CTS_ProtectedCircuit = $scheme_tmp_HOH{$hash_keyA}->{'ProtectedCircuit'};
		if (!defined $CTS_ProtectedCircuit) {
		   delete $scheme_tmp_HOH{$hash_keyA}; # already moved to $sr_down_tmp_HOH below, cleaning up
		   next;
		}
		my $CTS_FMSAlertKey = $scheme_tmp_HOH{$hash_keyA}->{'FMSAlertKey'};
		my $CTS_RawAlarmID = $scheme_tmp_HOH{$hash_keyA}->{'RawAlarmID'};
		my $CTS_SRInstance = $scheme_tmp_HOH{$hash_keyA}->{'SRInstance'};
		my $CTS_SRProvisionStatus = $scheme_tmp_HOH{$hash_keyA}->{'SRProvisionStatus'};
		my $CTS_SvcInstance = $scheme_tmp_HOH{$hash_keyA}->{'SvcInstance'};
		foreach my $hash_keyB(keys %scheme_tmp_HOH) {
			my $CTD_ProtectedCircuit = $scheme_tmp_HOH{$hash_keyB}->{'ProtectedCircuit'};
			my $CTD_ProtectingCircuit = $scheme_tmp_HOH{$hash_keyB}->{'ProtectingCircuit'};
			if (($CTS_ProtectingCircuit eq $CTD_ProtectedCircuit) && ($CTD_ProtectingCircuit ne ''))  {
				$lossfound = "TRUE";
			}
		}
		if (($lossfound eq "FALSE") && ($CTS_ProtectingCircuit ne '')) {
			#logInfo('loading sr_down_tmp'.nl);
			Load_sr_down_tmp(0,$CTS_FMSAlertKey,$CTS_RawAlarmID,$CTS_ProtectingCircuit,$CTS_ProtectedCircuit,
			"TRUE",$CTS_SRInstance,'','',$CTS_SRProvisionStatus,'','','','','','',0,'','','','','');
			foreach my $hash_keyB(keys %scheme_tmp_HOH) {
				my $CTD_ProtectedCircuit = $scheme_tmp_HOH{$hash_keyB}->{'ProtectedCircuit'};
				my $CTD_SvcInstance = $scheme_tmp_HOH{$hash_keyB}->{'SvcInstance'};
				my $CTD_SRInstance = $scheme_tmp_HOH{$hash_keyB}->{'SRInstance'};
				my $CTD_FMSAlertKey = $scheme_tmp_HOH{$hash_keyB}->{'FMSAlertKey'};
				if ( ($CTD_ProtectedCircuit eq $CTS_ProtectedCircuit) ||
				   ( ($CTD_SRInstance ne '') &&
				     ($CTD_SRInstance eq $CTS_SRInstance) && ( $CTD_FMSAlertKey =~ /$CTS_FMSAlertKey/) &&
				     (isInHierarchy($CTS_ProtectedCircuit,$CTD_ProtectedCircuit,$CTD_SRInstance)) &&
				     (HierarchySafe($CTS_ProtectedCircuit,$CTD_ProtectedCircuit,$CTD_SRInstance,'scheme_tmp')) ) ) {
					#logInfo('Match2 moved'.nl);
					copy_scheme_tmp_to_sr_down_tmp($scheme_tmp_HOH{$hash_keyB});
			  		delete $scheme_tmp_HOH{$hash_keyB}; # actually moved to $sr_down_tmp_HOH
			  	}
			}
		}
	}
  } until !$change;
               logInfo('TP step 3'.nl);
               print_scheme_tmp_HOH();
               print_sr_down_tmp_HOH();
	
	#-----------------------------
	logInfo('Number of entries in sr_down_tmp_HOH at start is '.scalar(keys %sr_down_tmp_HOH).nl);
	foreach my $hash_keyA(keys %scheme_tmp_HOH) {
		my $STL_SRInstance = $scheme_tmp_HOH{$hash_keyA}->{'SRInstance'};
		my $STL_RawAlarmID = $scheme_tmp_HOH{$hash_keyA}->{'RawAlarmID'};
		if (!defined $STL_SRInstance) {
		   delete $scheme_tmp_HOH{$hash_keyA}; # already deleted by the loop below, cleaning up
		   next;
		}
		foreach my $hash_keyB(keys %sr_down_tmp_HOH) {
			my $SRD_SRInstance = $sr_down_tmp_HOH{$hash_keyB}->{'SRInstance'};
			if ($SRD_SRInstance eq $STL_SRInstance) {
				#logInfo('delete match part 3'.nl);
				delete $sr_down_tmp_HOH{$hash_keyB};
			}
		}
		# remove the duplicated info in service_tmp
		foreach my $hash_keyC(keys %scheme_tmp_HOH) {
			my $ST_SRInstance = $scheme_tmp_HOH{$hash_keyC}->{'SRInstance'};
			my $ST_RawAlarmID = $scheme_tmp_HOH{$hash_keyC}->{'RawAlarmID'};
			if ( ($ST_SRInstance eq $STL_SRInstance) && ($ST_RawAlarmID eq $STL_RawAlarmID) &&
			     ($hash_keyA !=  $hash_keyC) ) {
				#logInfo('removing duplicate in service tmp'.nl);
				delete $scheme_tmp_HOH{$hash_keyC};
			}
		}
	}
	logInfo('Number of entries in sr_down_tmp_HOH at end is '.scalar(keys %sr_down_tmp_HOH).nl);
               logInfo('TP step 4'.nl);
               print_scheme_tmp_HOH();
               print_sr_down_tmp_HOH();
	
	###########################################################
	# Enrich the scheme_tmp table for each of the lost Scheme Routes 
 	############################################################
 	foreach my $hash_keyA(keys %scheme_tmp_HOH) {
 	   # get the Scheme Service associated to the Scheme Route which is down
 	   # label all the Scheme Routes affected
 	   my $ST_SRInstance = $scheme_tmp_HOH{$hash_keyA}->{'SRInstance'};
 	   foreach my $hash_keyB(keys %schemeRoute_HOH) {
 	      my $SR_ProtectedSchemeRoute = $schemeRoute_HOH{$hash_keyB}->{'ProtectedSchemeRoute'};
 	      if ($SR_ProtectedSchemeRoute eq $ST_SRInstance) {
 	          $scheme_tmp_HOH{$hash_keyA}->{'SSInstance'} = $schemeRoute_HOH{$hash_keyB}->{'SvcInstance'};
 	          $scheme_tmp_HOH{$hash_keyA}->{'SSProvisionStatus'} = $schemeRoute_HOH{$hash_keyB}->{'ProvisionStatus'};
  	          # update Cramer table, must be cleaned up via SIA_Cleanup()
	          $schemeRoute_HOH{$hash_keyB}->{'IsSRAffected'} = "TRUE";
 	      }
 	   }
  	   my $ST_SSInstance = $scheme_tmp_HOH{$hash_keyA}->{'SSInstance'};
 	   foreach my $hash_keyB(keys %schemeInfo_HOH) {
 	      my $SS_ProtectedScheme = $schemeInfo_HOH{$hash_keyB}->{'ProtectedScheme'};
 	      if ($SS_ProtectedScheme eq $ST_SSInstance) {
 	          $scheme_tmp_HOH{$hash_keyA}->{'SGInstance'} = $schemeInfo_HOH{$hash_keyB}->{'SvcInstance'};
 	          $scheme_tmp_HOH{$hash_keyA}->{'SGProvisionStatus'} = $schemeInfo_HOH{$hash_keyB}->{'ProvisionStatus'};
 	          last;
 	      }
 	   }
  	   my $ST_SGInstance = $scheme_tmp_HOH{$hash_keyA}->{'SGInstance'};
 	   foreach my $hash_keyB(keys %schemeGroup_HOH) {
 	      my $SG_ProtectedScheme = $schemeGroup_HOH{$hash_keyB}->{'ProtectedScheme'};
 	      if ($SG_ProtectedScheme eq $ST_SGInstance) {
 	          $scheme_tmp_HOH{$hash_keyA}->{'SvcInstance'} = $schemeGroup_HOH{$hash_keyB}->{'SvcInstance'};
 	          $scheme_tmp_HOH{$hash_keyA}->{'SvcProvisionStatus'} = $schemeGroup_HOH{$hash_keyB}->{'ProvisionStatus'};
 	          $scheme_tmp_HOH{$hash_keyA}->{'Svc_ServiceID'} = $schemeGroup_HOH{$hash_keyB}->{'BusSvcName'};
 	          $scheme_tmp_HOH{$hash_keyA}->{'Svc_SubSvcName'} = $schemeGroup_HOH{$hash_keyB}->{'SubSvcName'};
 	          $scheme_tmp_HOH{$hash_keyA}->{'Svc_BusPriority'} = $schemeGroup_HOH{$hash_keyB}->{'ServicePriority'};
 	          last;
 	      }
 	   }
 	   # All SR must be lost (if downgraded, it will be stored in sr_down_tmp, a different syn alarm would be raised)
 	   $scheme_tmp_HOH{$hash_keyA}->{'SR_Status'} = 'SR Loss';
 	}
	###########################################################
	# now for each SS affected, go through each SR which meet the SIARule A/B 
 	############################################################
 	foreach my $hash_keyA(keys %scheme_tmp_HOH) {
 	   my $hasLossA = "FALSE";
 	   my $hasLossB = "FALSE";
 	   my $notAffectedSR = 0;
 	   my $ST_SSInstance = $scheme_tmp_HOH{$hash_keyA}->{'SSInstance'};
 	   # must assume each SR within the same SS group must all have the same SIARule (it cannot be mixed)
 	   foreach my $hash_keyB(keys %schemeRoute_HOH) {
 	       my $SR_SvcInstance = $schemeRoute_HOH{$hash_keyB}->{'SvcInstance'};
 	       if ($SR_SvcInstance eq $ST_SSInstance) {
 	          my $SR_SIARule = $schemeRoute_HOH{$hash_keyB}->{'SIARule'};
 	          my $SR_IsSRAffected = $schemeRoute_HOH{$hash_keyB}->{'IsSRAffected'};
 	          if ($SR_SIARule eq 'B') {
 	            if ($SR_IsSRAffected eq "TRUE") {
 	             $hasLossB = "TRUE";
 	             last;
 	            }
 	          } else {
 	            # Default treated as Rule A, eg a blank rule
 	            if ($SR_IsSRAffected eq "TRUE") {
 	             $hasLossA = "TRUE";
 	            } else {
 	             $notAffectedSR += 1;
 	             last;
 	            }
 	          }
 	       }
 	   }
 	   # Rule A - all routes are lost - SS loss
 	   if ( ($hasLossA eq "TRUE") && ($notAffectedSR == 0) ) {
 	     $scheme_tmp_HOH{$hash_keyA}->{'SS_Status'} = 'SS Loss - A';
 	   }
 	   # Rule A - at least 1 SR is operational - SS downgraded
 	   if ($notAffectedSR > 0) {
 	     $scheme_tmp_HOH{$hash_keyA}->{'SS_Status'} = 'SS Downgraded - A';
 	   }
 	   # Rule B - at least 1 SR is lost - SS loss
 	   if ($hasLossB eq "TRUE") {
 	     $scheme_tmp_HOH{$hash_keyA}->{'SS_Status'} = 'SS Loss - B';
 	   }
 	}
	###########################################################
	# now for each SvcInstance affected, go through each SS state, based on SS Lost/SS Degrade
 	############################################################
 	foreach my $hash_keyA(keys %scheme_tmp_HOH) {
 	   my $ST_SGInstance = $scheme_tmp_HOH{$hash_keyA}->{'SGInstance'};
 	   my $ST_SSInstance = $scheme_tmp_HOH{$hash_keyA}->{'SSInstance'};
 	   my $ST_SS_Status = $scheme_tmp_HOH{$hash_keyA}->{'SS_Status'};
 	   # multiple SS may belong to only 1 SvcInstance (child->parent)
 	   foreach my $hash_keyB(keys %schemeInfo_HOH) {
 	      my $SS_SvcInstance = $schemeInfo_HOH{$hash_keyB}->{'SvcInstance'};
 	      if ($SS_SvcInstance eq $ST_SGInstance) {
 	         my $SS_ProtectedScheme = $schemeInfo_HOH{$hash_keyB}->{'ProtectedScheme'};
 	         if ($SS_ProtectedScheme eq $ST_SSInstance) {
 	            $schemeInfo_HOH{$hash_keyB}->{'ProtectedSS_Status'} = $ST_SS_Status;
 	         }
 	         my $SS_ProtectingScheme = $schemeInfo_HOH{$hash_keyB}->{'ProtectingScheme'};
 	         if ($SS_ProtectingScheme eq $ST_SSInstance) {
 	            $schemeInfo_HOH{$hash_keyB}->{'ProtectingSS_Status'} = $ST_SS_Status;
 	         }
 	      }
 	   }
 	}
 	foreach my $hash_keyA(keys %scheme_tmp_HOH) {
 	   my $foundSvc = "FALSE";
 	   my $foundLoss = "FALSE";
 	   my $foundDegraded = "FALSE";
 	   my $foundOperational = "FALSE";
 	   my $ST_SGInstance = $scheme_tmp_HOH{$hash_keyA}->{'SGInstance'};
 	   my $ST_SSInstance = $scheme_tmp_HOH{$hash_keyA}->{'SSInstance'};
 	   # Added condition to fetch Scheme Services which are affected under Scheme Group
 	   foreach my $hash_keyB(keys %schemeInfo_HOH) {
 	      my $SS_SvcInstance = $schemeInfo_HOH{$hash_keyB}->{'SvcInstance'};
 	      my $SS_ProtectedScheme = $schemeInfo_HOH{$hash_keyB}->{'ProtectedScheme'};
 	      if ( ($SS_SvcInstance eq $ST_SGInstance) && ($SS_ProtectedScheme eq $ST_SSInstance) ) {
 	         $foundSvc = "TRUE";
 	         my $SS_ProtectedScheme = $schemeInfo_HOH{$hash_keyB}->{'ProtectedScheme'};
 	         my $SS_ProtectingScheme = $schemeInfo_HOH{$hash_keyB}->{'ProtectingScheme'};
 	         my $SS_ProtectedSS_Status = $schemeInfo_HOH{$hash_keyB}->{'ProtectedSS_Status'};
 	         my $SS_ProtectingSS_Status = $schemeInfo_HOH{$hash_keyB}->{'ProtectingSS_Status'};
 	         if ((($SS_ProtectingSS_Status eq '') && ($SS_ProtectingScheme ne '')) || (($SS_ProtectedSS_Status eq '') && ($SS_ProtectedScheme ne ''))) {
 	            # has empty status, but doesnt mean SS is up. need to make sure the SS exists too
 	            # (could be non-protecting SS)
 	            $foundOperational = "TRUE";
 	         }
 	         if (($SS_ProtectingSS_Status =~ /SS Loss/) || ($SS_ProtectedSS_Status =~ /SS Loss/)) {
 	            $foundLoss = "TRUE";
 	         }
 	         if (($SS_ProtectingSS_Status =~ /SS Downgraded/) || ($SS_ProtectedSS_Status =~ /SS Downgraded/)) {
 	            $foundDegraded = "TRUE";
 	         }
 	      }
 	   }
 	   if ($foundSvc eq "TRUE") {
 	      if ($foundOperational eq "TRUE") {
 	        # at least 1 operational -> svc downgraded
 	        $scheme_tmp_HOH{$hash_keyA}->{'SG_Status'} = 'SG Downgraded';
 	      } else {
 	        if (($foundLoss eq "TRUE") && ($foundDegraded eq "FALSE")) {
 	          # all ss lost, none ss degraded -> svc loss
 	          $scheme_tmp_HOH{$hash_keyA}->{'SG_Status'} = 'SG Loss';
 	        } else {
 	          # some ss lost, some ss degraded -> svc downgraded
 	          # none ss lost, all ss degraded -> svc downgraded
 	          $scheme_tmp_HOH{$hash_keyA}->{'SG_Status'} = 'SG Downgraded All';
 	        }
 	      }
 	   }
 	}
	###########################################################
	# Update SchemeGroup status based on Scheme service status and update Scheme_tmp table Svc_Status
	# now for each SvcInstance affected, go through each SS state, based on SS Lost/SS Degrade
 	############################################################
 	foreach my $hash_keyA(keys %scheme_tmp_HOH) {
  	   my $ST_SvcInstance = $scheme_tmp_HOH{$hash_keyA}->{'SvcInstance'};
 	   my $ST_SGInstance = $scheme_tmp_HOH{$hash_keyA}->{'SGInstance'};
 	   my $ST_SG_Status = $scheme_tmp_HOH{$hash_keyA}->{'SG_Status'};
 	   # multiple SS may belong to only 1 SvcInstance (child->parent)
 	   foreach my $hash_keyB(keys %schemeGroup_HOH) {
 	      my $SG_SvcInstance = $schemeGroup_HOH{$hash_keyB}->{'SvcInstance'};
 	      if ($SG_SvcInstance eq $ST_SvcInstance) {
 	         my $SG_ProtectedScheme = $schemeGroup_HOH{$hash_keyB}->{'ProtectedScheme'};
 	         if ($SG_ProtectedScheme eq $ST_SGInstance) {
 	            $schemeGroup_HOH{$hash_keyB}->{'ProtectedSG_Status'} = $ST_SG_Status;
 	         }
 	         my $SG_ProtectingScheme = $schemeGroup_HOH{$hash_keyB}->{'ProtectingScheme'};
 	         if ($SG_ProtectingScheme eq $ST_SGInstance) {
 	            $schemeGroup_HOH{$hash_keyB}->{'ProtectingSG_Status'} = $ST_SG_Status;
 	         }
 	      }
 	   }
 	}
 	foreach my $hash_keyA(keys %scheme_tmp_HOH) {
 	   my $foundSvc = "FALSE";
 	   my $foundLoss = "FALSE";
 	   my $foundDegraded = "FALSE";
 	   my $foundOperational = "FALSE";
 	   my $ST_SGInstance = $scheme_tmp_HOH{$hash_keyA}->{'SGInstance'};
 	   my $ST_SvcInstance = $scheme_tmp_HOH{$hash_keyA}->{'SvcInstance'};
 	   # Added condition to fetch Scheme Services which are affected under Scheme Group
 	   foreach my $hash_keyB(keys %schemeGroup_HOH) {
 	      my $SG_SvcInstance = $schemeGroup_HOH{$hash_keyB}->{'SvcInstance'};
 	      my $SG_ProtectedScheme = $schemeGroup_HOH{$hash_keyB}->{'ProtectedScheme'};
 	      my $SG_ProtectingScheme = $schemeGroup_HOH{$hash_keyB}->{'ProtectingScheme'};
 	      if ( ($SG_SvcInstance eq $ST_SvcInstance) && (($SG_ProtectedScheme eq $ST_SGInstance) || ($SG_ProtectingScheme eq $ST_SGInstance)) ) {
 	         $foundSvc = "TRUE";
 	         my $SG_ProtectedSG_Status = $schemeGroup_HOH{$hash_keyB}->{'ProtectedSG_Status'};
 	         my $SG_ProtectingSG_Status = $schemeGroup_HOH{$hash_keyB}->{'ProtectingSG_Status'};
 	         if ((($SG_ProtectingSG_Status eq '') && ($SG_ProtectingScheme ne '')) || (($SG_ProtectedSG_Status eq '') && ($SG_ProtectedScheme ne ''))) {
 	            # has empty status, but doesnt mean SS is up. need to make sure the SS exists too
 	            # (could be non-protecting SS)
 	            $foundOperational = "TRUE";
 	         }
 	         if ( ($SG_ProtectingSG_Status =~ /SG Loss/) && (($SG_ProtectedSG_Status =~ /SG Loss/) || ($SG_ProtectedScheme eq '')) ) {
 	            $foundLoss = "TRUE";
 	         }
 	         if ( ($SG_ProtectedSG_Status =~ /SG Loss/) && (($SG_ProtectingSG_Status =~ /SG Loss/) || ($SG_ProtectingScheme eq '')) ) {
 	            $foundLoss = "TRUE";
 	         }
 	         if (($SG_ProtectingSG_Status =~ /SG Downgraded/) || ($SG_ProtectedSG_Status =~ /SG Downgraded/)) {
 	            $foundDegraded = "TRUE";
 	         }
 	      }
 	   }
 	   if ($foundSvc eq "TRUE") {
 	      if ($foundOperational eq "TRUE") {
 	        # at least 1 operational -> svc downgraded
 	        $scheme_tmp_HOH{$hash_keyA}->{'Svc_Status'} = 'Svc Downgraded';
 	      } else {
 	        if (($foundLoss eq "TRUE") && ($foundDegraded eq "FALSE")) {
 	          # all ss lost, none ss degraded -> svc loss
 	          $scheme_tmp_HOH{$hash_keyA}->{'Svc_Status'} = 'Svc Loss';
 	        } else {
 	          # some sg lost, some ss degraded -> svc downgraded
 	          # none sg lost, all ss degraded -> svc downgraded
 	          $scheme_tmp_HOH{$hash_keyA}->{'Svc_Status'} = 'Svc Downgraded All';
 	        }
 	      }
 	   }
 	}
	perfCalc('end','SIA_process_TP_svcs1');
	update_tp_summary();
    SIA_process_TP_svcs2($dbHandle);
}

sub SIA_process_TP_svcs2($){
	my ($dbHandle)= @_;
	my %svc_inst_counted = ();
	logInfo('Starting SIA Process TP svcs 2'.nl); 
	perfCalc('start','SIA_process_TP_svcs2');
    foreach my $hash_keyA(keys %scheme_tmp_HOH) {
       my $ST_SvcInstance = $scheme_tmp_HOH{$hash_keyA}->{'SvcInstance'};
       my $ST_Svc_Status = $scheme_tmp_HOH{$hash_keyA}->{'Svc_Status'};
       my $ST_Svc_BusPriority = $scheme_tmp_HOH{$hash_keyA}->{'Svc_BusPriority'};
       my $ST_Svc_ServiceID = $scheme_tmp_HOH{$hash_keyA}->{'Svc_ServiceID'};
       my $ST_Svc_SubSvcName = $scheme_tmp_HOH{$hash_keyA}->{'Svc_SubSvcName'};
       my $ST_FMSAlertKey = $scheme_tmp_HOH{$hash_keyA}->{'FMSAlertKey'};
       my $ST_RawAlarmID = $scheme_tmp_HOH{$hash_keyA}->{'RawAlarmID'};
       my $ST_ProtectedCircuit = $scheme_tmp_HOH{$hash_keyA}->{'ProtectedCircuit'};
       my $ST_ProtectingCircuit = $scheme_tmp_HOH{$hash_keyA}->{'ProtectingCircuit'};
       my $ST_SRInstance = $scheme_tmp_HOH{$hash_keyA}->{'SRInstance'};
       my $ST_SR_Status = $scheme_tmp_HOH{$hash_keyA}->{'SR_Status'};
       # Svc Loss/Downgrade
       if (($ST_SvcInstance ne '') && ($ST_Svc_Status ne '')) {
          my $ST_SvcProvisionStatus = $scheme_tmp_HOH{$hash_keyA}->{'SvcProvisionStatus'};
          my $ST_Summary = $scheme_tmp_HOH{$hash_keyA}->{'Summary'};
          my $Last_RawAlarmID = $last_alarm_id{$ST_SRInstance}->{'RawAlarmID'};
          my $Last_FMSAlertKey = $last_alarm_id{$ST_SRInstance}->{'FMSAlertKey'};
          # insert syn alarm
          if ($ST_Svc_Status =~ /Svc Downgraded/) {
             UpdateSynthetic_alarm_storage_HOH($ST_SvcInstance,'Service Downgraded',$Last_FMSAlertKey,$ST_SvcProvisionStatus,$ST_ProtectedCircuit,$ST_ProtectingCircuit,$ST_Svc_BusPriority,$ST_Svc_ServiceID,$ST_Svc_SubSvcName,$Last_RawAlarmID,4,$ST_Summary);
          } elsif ($ST_Svc_Status eq 'Svc Loss') {
             UpdateSynthetic_alarm_storage_HOH($ST_SvcInstance,'Service Loss',$Last_FMSAlertKey,$ST_SvcProvisionStatus,$ST_ProtectedCircuit,$ST_ProtectingCircuit,$ST_Svc_BusPriority,$ST_Svc_ServiceID,$ST_Svc_SubSvcName,$Last_RawAlarmID,5,$ST_Summary);
          }
          # Update summary is moved to InsertSyntheticAlarms
          # UpdateAlerts_status_Summary($dbHandle,$ST_Summary,$ST_SvcInstance,$ST_RawAlarmID);
          # enrich the raw alarm
          my $impactStatus = '';
          if ($ST_Svc_Status =~ /Svc Downgraded/) {
             $impactStatus = 'Service Downgraded';
          } elsif ($ST_Svc_Status eq 'Svc Loss') {
             $impactStatus = 'Service Loss';
          }
		  foreach my $hash_keyB(keys %alerts_status_tmp) {
			 my $AS_ServerName_ServerSerial = $alerts_status_tmp{$hash_keyB}->{'ServerName_ServerSerial'};
			 my $AS_SuppressEscl = $alerts_status_tmp{$hash_keyB}->{'SuppressEscl'};
             if ($AS_ServerName_ServerSerial eq $ST_RawAlarmID) {
                # a service downgrade can still overwrite service loss info on raw alarm, due to highest BIR rule
                # any one of the protecting/protected circuit of the affected the scheme routes is used
			    my $AS_BusPriority = $alerts_status_tmp{$hash_keyB}->{'BusPriority'};
                if ($AS_BusPriority < $ST_Svc_BusPriority) {
                   UpdateAlerts_status($dbHandle,$ST_ProtectingCircuit,$ST_ProtectedCircuit,$ST_SvcInstance,$ST_Svc_BusPriority,$ST_Svc_ServiceID,$ST_Svc_SubSvcName,$ST_RawAlarmID,$impactStatus);
                   UpdateAlerts_status_tmp($ST_ProtectingCircuit,$ST_ProtectedCircuit,$ST_SvcInstance,$ST_Svc_BusPriority,$ST_Svc_ServiceID,$ST_Svc_SubSvcName,$ST_RawAlarmID,$impactStatus);
                }
                # increment on each service loss, but only if this SvcInstance was not yet counted
                if ( ($impactStatus eq 'Service Loss') && (!defined $svc_inst_counted{$ST_SvcInstance.$AS_ServerName_ServerSerial}) ) {
			       my $AS_ServicesImpacted = $alerts_status_tmp{$hash_keyB}->{'ServicesImpacted'};
			       $AS_ServicesImpacted++;
                   UpdateAlerts_status_ServiceLosscounter($dbHandle,$AS_ServicesImpacted,$ST_RawAlarmID);
                   $alerts_status_tmp{$hash_keyB}->{'ServicesImpacted'} = $AS_ServicesImpacted;
                   $svc_inst_counted{$ST_SvcInstance.$AS_ServerName_ServerSerial} = "TRUE";
                }
                # a live/in service provision status of the loss BSVC will move the raw alarm out of maintenance suppression, allowing AutoTT to be raised against it
				# however, a non-live provision status of the loss BSVC will NOT move the raw alarm into maintenance suppression, AutoTT can still be triggered
				if ( ($ST_SvcProvisionStatus eq 'Live') || ($ST_SvcProvisionStatus eq 'In Service') || ($ST_SvcProvisionStatus eq '') ) {
				   UpdateAlerts_status_SuppressEscl($dbHandle,0,$ST_RawAlarmID,6);
				}
				last;
             }
          }
       }
       
       my $ST_SGInstance = $scheme_tmp_HOH{$hash_keyA}->{'SGInstance'};
       my $ST_SG_Status = $scheme_tmp_HOH{$hash_keyA}->{'SG_Status'};
       # SG Loss/Downgrade
       if (($ST_SGInstance ne '') && ($ST_SG_Status ne '')) {
          my $ST_SGProvisionStatus = $scheme_tmp_HOH{$hash_keyA}->{'SGProvisionStatus'};
          my $Last_RawAlarmID = $last_alarm_id{$ST_SRInstance}->{'RawAlarmID'};
          my $Last_FMSAlertKey = $last_alarm_id{$ST_SRInstance}->{'FMSAlertKey'};
          # insert syn alarm
          if ($ST_SG_Status eq 'SG Downgraded') {
             UpdateSynthetic_alarm_storage_HOH($ST_SGInstance,'SchemeGroup Downgraded',$Last_FMSAlertKey,$ST_SGProvisionStatus,$ST_ProtectedCircuit,$ST_ProtectingCircuit,$ST_Svc_BusPriority,$ST_Svc_ServiceID,$ST_Svc_SubSvcName,$Last_RawAlarmID,4,$Null_Summary);
          } elsif ($ST_SG_Status eq 'SG Loss') {
             UpdateSynthetic_alarm_storage_HOH($ST_SGInstance,'SchemeGroup Loss',$Last_FMSAlertKey,$ST_SGProvisionStatus,$ST_ProtectedCircuit,$ST_ProtectingCircuit,$ST_Svc_BusPriority,$ST_Svc_ServiceID,$ST_Svc_SubSvcName,$Last_RawAlarmID,5,$Null_Summary);
          } elsif ($ST_SG_Status eq 'SG Downgraded All') {
             UpdateSynthetic_alarm_storage_HOH($ST_SGInstance,'SchemeGroup Downgraded (All SchemeGroup Affected With At Least 1 SchemeGroup Degraded)',$Last_FMSAlertKey,$ST_SGProvisionStatus,$ST_ProtectedCircuit,$ST_ProtectingCircuit,$ST_Svc_BusPriority,$ST_Svc_ServiceID,$ST_Svc_SubSvcName,$Last_RawAlarmID,4,$Null_Summary);
          }
          # enrich the raw alarm
          my $impactStatus = '';
          if ($ST_SG_Status =~ /SG Downgraded/) {
             $impactStatus = 'SchemeGroup Downgraded';
          } elsif ($ST_SG_Status eq 'SG Loss') {
             $impactStatus = 'SchemeGroup Loss';
          }
		  foreach my $hash_keyB(keys %alerts_status_tmp) {
			 my $AS_ServerName_ServerSerial = $alerts_status_tmp{$hash_keyB}->{'ServerName_ServerSerial'};
			 my $AS_SuppressEscl = $alerts_status_tmp{$hash_keyB}->{'SuppressEscl'};
			 my $AS_ImpactedStatus = $alerts_status_tmp{$hash_keyB}->{'ImpactedStatus'};
             if (($AS_ServerName_ServerSerial eq $ST_RawAlarmID) && ($AS_ImpactedStatus eq '')) {
				my $statement = "update alerts.status set ".
            	"ServiceImpactingFlag = 2 , ImpactedStatus = '$impactStatus', SvcInstance = '$ST_SGInstance',".
            	" ProtectingCircuit = '$ST_ProtectingCircuit', ProtectedCircuit = '$ST_ProtectedCircuit'".
            	" where ServerName_ServerSerial = '$ST_RawAlarmID'";
            	dbUpdate($dbHandle,$statement);
				if ( ($ST_SGProvisionStatus eq 'Live') || ($ST_SGProvisionStatus eq 'In Service') || ($ST_SGProvisionStatus eq '') ) {
				   UpdateAlerts_status_SuppressEscl($dbHandle,0,$ST_RawAlarmID,6);
				}
				last;
             }
          }
       }
       
       my $ST_SSInstance = $scheme_tmp_HOH{$hash_keyA}->{'SSInstance'};
       my $ST_SS_Status = $scheme_tmp_HOH{$hash_keyA}->{'SS_Status'};
       # SS Loss/Downgrade
       if (($ST_SSInstance ne '') && ($ST_SS_Status ne '')) {
          my $ST_SSProvisionStatus = $scheme_tmp_HOH{$hash_keyA}->{'SSProvisionStatus'};
          my $Last_RawAlarmID = $last_alarm_id{$ST_SRInstance}->{'RawAlarmID'};
          my $Last_FMSAlertKey = $last_alarm_id{$ST_SRInstance}->{'FMSAlertKey'};
          # insert syn alarm
          if ($ST_SS_Status eq 'SS Loss - A') {
             UpdateSynthetic_alarm_storage_HOH($ST_SSInstance,'Scheme Service Loss',$Last_FMSAlertKey,$ST_SSProvisionStatus,$ST_ProtectedCircuit,$ST_ProtectingCircuit,$ST_Svc_BusPriority,$ST_Svc_ServiceID,$ST_Svc_SubSvcName,$Last_RawAlarmID,5,$Null_Summary);
          } elsif ($ST_SS_Status eq 'SS Downgraded - A') {
             UpdateSynthetic_alarm_storage_HOH($ST_SSInstance,'Scheme Service Downgraded',$Last_FMSAlertKey,$ST_SSProvisionStatus,$ST_ProtectedCircuit,$ST_ProtectingCircuit,$ST_Svc_BusPriority,$ST_Svc_ServiceID,$ST_Svc_SubSvcName,$Last_RawAlarmID,4,$Null_Summary);
          } elsif ($ST_SS_Status eq 'SS Loss - B') {
             UpdateSynthetic_alarm_storage_HOH($ST_SSInstance,'Scheme Service Loss',$Last_FMSAlertKey,$ST_SSProvisionStatus,$ST_ProtectedCircuit,$ST_ProtectingCircuit,$ST_Svc_BusPriority,$ST_Svc_ServiceID,$ST_Svc_SubSvcName,$Last_RawAlarmID,5,$Null_Summary);
          }
          # enrich the raw alarm
          my $impactStatus = '';
          if ($ST_SS_Status =~ /SS Loss - /) {
             $impactStatus = 'Scheme Service Loss';
          } elsif ($ST_SS_Status eq 'SS Downgraded') {
             $impactStatus = 'Scheme Service Downgraded';
          }
		  foreach my $hash_keyB(keys %alerts_status_tmp) {
			 my $AS_ServerName_ServerSerial = $alerts_status_tmp{$hash_keyB}->{'ServerName_ServerSerial'};
			 my $AS_SuppressEscl = $alerts_status_tmp{$hash_keyB}->{'SuppressEscl'};
			 my $AS_ImpactedStatus = $alerts_status_tmp{$hash_keyB}->{'ImpactedStatus'};
             if (($AS_ServerName_ServerSerial eq $ST_RawAlarmID) && ($AS_ImpactedStatus eq '')) {
				my $statement = "update alerts.status set ".
            	"ServiceImpactingFlag = 2 , ImpactedStatus = '$impactStatus', SvcInstance = '$ST_SSInstance',".
            	" ProtectingCircuit = '$ST_ProtectingCircuit', ProtectedCircuit = '$ST_ProtectedCircuit'".
            	" where ServerName_ServerSerial = '$ST_RawAlarmID'";
            	dbUpdate($dbHandle,$statement);
				if ( ($ST_SSProvisionStatus eq 'Live') || ($ST_SSProvisionStatus eq 'In Service') || ($ST_SSProvisionStatus eq '') ) {
				   UpdateAlerts_status_SuppressEscl($dbHandle,0,$ST_RawAlarmID,6);
				}
				last;
             }
          }
       }
       
       # SR Loss
       if (($ST_SRInstance ne '') && ($ST_SR_Status eq 'SR Loss')) {
          my $ST_SRProvisionStatus = $scheme_tmp_HOH{$hash_keyA}->{'SRProvisionStatus'};
          my $Last_RawAlarmID = $last_alarm_id{$ST_SRInstance}->{'RawAlarmID'};
          my $Last_FMSAlertKey = $last_alarm_id{$ST_SRInstance}->{'FMSAlertKey'};
          # insert syn alarm
          UpdateSynthetic_alarm_storage_HOH($ST_SRInstance,'Scheme Route Loss',$Last_FMSAlertKey,$ST_SRProvisionStatus,$ST_ProtectedCircuit,$ST_ProtectingCircuit,$ST_Svc_BusPriority,$ST_Svc_ServiceID,$ST_Svc_SubSvcName,$Last_RawAlarmID,5,$Null_Summary);
          # enrich the raw alarm
          my $impactStatus = '';
          if ($ST_SR_Status =~ /SR Loss - /) {
             $impactStatus = 'Scheme Route Loss';
          }
		  foreach my $hash_keyB(keys %alerts_status_tmp) {
			 my $AS_ServerName_ServerSerial = $alerts_status_tmp{$hash_keyB}->{'ServerName_ServerSerial'};
			 my $AS_SuppressEscl = $alerts_status_tmp{$hash_keyB}->{'SuppressEscl'};
			 my $AS_ImpactedStatus = $alerts_status_tmp{$hash_keyB}->{'ImpactedStatus'};
			 my $AS_BusPriority = $alerts_status_tmp{$hash_keyB}->{'BusPriority'};
             if (($AS_ServerName_ServerSerial eq $ST_RawAlarmID) && ($AS_ImpactedStatus eq '')) {
			    if ($AS_BusPriority < $ST_Svc_BusPriority) {
			      UpdateAlerts_status($dbHandle,$ST_ProtectingCircuit,$ST_ProtectedCircuit,$ST_SRInstance,
			      $ST_Svc_BusPriority,$ST_Svc_ServiceID,$ST_Svc_SubSvcName,$ST_RawAlarmID,$impactStatus);
			      UpdateAlerts_status_tmp($ST_ProtectingCircuit,$ST_ProtectedCircuit,$ST_SRInstance,
			      $ST_Svc_BusPriority,$ST_Svc_ServiceID,$ST_Svc_SubSvcName,$ST_RawAlarmID,$impactStatus);
			    }
				if ( ($ST_SRProvisionStatus eq 'Live') || ($ST_SRProvisionStatus eq 'In Service') || ($ST_SRProvisionStatus eq '') ) {
				   UpdateAlerts_status_SuppressEscl($dbHandle,0,$ST_RawAlarmID,6);
				}
				last;
             }
          }
       }
    }
    # Raise Synthetic Alarms for degraded scheme routes
	perfCalc('end','SIA_process_TP_svcs2');
    SIA_process_TP_svcs3($dbHandle);
}

sub SIA_process_TP_svcs3($){
	my ($dbHandle)= @_;
	logInfo('Starting SIA Process TP svcs 3'.nl); 
	perfCalc('start','SIA_process_TP_svcs3');
    foreach my $hash_keyA(keys %sr_down_tmp_HOH) {
       # get the SS associated to the SR which is down
       # label all the SR affected
       $sr_down_tmp_HOH{$hash_keyA}->{'SR_Status'} = 'SR Downgraded';
       my $SRD_SRInstance = $sr_down_tmp_HOH{$hash_keyA}->{'SRInstance'};
       foreach my $hash_keyB(keys %schemeRoute_HOH) {
          my $SR_ProtectedSchemeRoute = $schemeRoute_HOH{$hash_keyB}->{'ProtectedSchemeRoute'};
          if ($SR_ProtectedSchemeRoute eq $SRD_SRInstance) {
             my $SR_SvcInstance = $schemeRoute_HOH{$hash_keyB}->{'SvcInstance'};
             my $SR_ProvisionStatus = $schemeRoute_HOH{$hash_keyB}->{'ProvisionStatus'};
             $sr_down_tmp_HOH{$hash_keyA}->{'SSInstance'} = $SR_SvcInstance;
             $sr_down_tmp_HOH{$hash_keyA}->{'SSProvisionStatus'} = $SR_ProvisionStatus;
             # update Cramer table, must be cleaned up via SIA_Cleanup()
             $schemeRoute_HOH{$hash_keyB}->{'IsSRAffected'} = "TRUE";
          }
       }
       my $SRD_SSInstance = $sr_down_tmp_HOH{$hash_keyA}->{'SSInstance'};
       foreach my $hash_keyB(keys %schemeInfo_HOH) {
          my $SS_ProtectedScheme = $schemeInfo_HOH{$hash_keyB}->{'ProtectedScheme'};
          if ($SS_ProtectedScheme eq $SRD_SSInstance) {
             my $SS_SvcInstance = $schemeInfo_HOH{$hash_keyB}->{'SvcInstance'};
             my $SS_ProvisionStatus = $schemeInfo_HOH{$hash_keyB}->{'ProvisionStatus'};
             $sr_down_tmp_HOH{$hash_keyA}->{'SGInstance'} = $SS_SvcInstance;
             $sr_down_tmp_HOH{$hash_keyA}->{'SGProvisionStatus'} = $SS_ProvisionStatus;
             last;
          }
       }
       my $SRD_SGInstance = $sr_down_tmp_HOH{$hash_keyA}->{'SGInstance'};
       foreach my $hash_keyB(keys %schemeGroup_HOH) {
          my $SG_ProtectedScheme = $schemeGroup_HOH{$hash_keyB}->{'ProtectedScheme'};
          if ($SG_ProtectedScheme eq $SRD_SGInstance) {
             my $SG_SvcInstance = $schemeGroup_HOH{$hash_keyB}->{'SvcInstance'};
             my $SG_ProvisionStatus = $schemeGroup_HOH{$hash_keyB}->{'ProvisionStatus'};
             my $SG_BusSvcName = $schemeGroup_HOH{$hash_keyB}->{'BusSvcName'};
             my $SG_SubSvcName = $schemeGroup_HOH{$hash_keyB}->{'SubSvcName'};
             my $SG_ServicePriority = $schemeGroup_HOH{$hash_keyB}->{'ServicePriority'};
             $sr_down_tmp_HOH{$hash_keyA}->{'SvcInstance'} = $SG_SvcInstance;
             $sr_down_tmp_HOH{$hash_keyA}->{'SvcProvisionStatus'} = $SG_ProvisionStatus;
             $sr_down_tmp_HOH{$hash_keyA}->{'Svc_ServiceID'} = $SG_BusSvcName;
             $sr_down_tmp_HOH{$hash_keyA}->{'Svc_SubSvcName'} = $SG_SubSvcName;
             $sr_down_tmp_HOH{$hash_keyA}->{'Svc_BusPriority'} = $SG_ServicePriority;
             last;
          }
       }
       # Check scheme_tmp table for SS,SG and BS status. If it is already set it implies
       # some other scheme route under SS is loss
       my $ssloss = "FALSE";
       my $sgloss = "FALSE";
       my $bsloss = "FALSE";
       my $ss_status = '';
       my $sg_status = '';
       my $bs_status = '';
       foreach my $hash_keyB(keys %scheme_tmp_HOH) {
          # Check Scheme service status
          my $ST_SSInstance = $scheme_tmp_HOH{$hash_keyB}->{'SSInstance'};
          my $ST_SS_Status = $scheme_tmp_HOH{$hash_keyB}->{'SS_Status'};
          if (($SRD_SSInstance eq $ST_SSInstance) && ($ST_SS_Status ne '')) {
             $ssloss = "TRUE";
             $ss_status = $ST_SS_Status;
          }
          # Check Scheme group status
          my $ST_SGInstance = $scheme_tmp_HOH{$hash_keyB}->{'SGInstance'};
          my $ST_SG_Status = $scheme_tmp_HOH{$hash_keyB}->{'SG_Status'};
          if (($SRD_SGInstance eq $ST_SGInstance) && ($ST_SG_Status ne '')) {
             $sgloss = "TRUE";
             $sg_status = $ST_SG_Status;
          }
          # Check business service status
          my $ST_SvcInstance = $scheme_tmp_HOH{$hash_keyB}->{'SvcInstance'};
          my $ST_Svc_Status = $scheme_tmp_HOH{$hash_keyB}->{'Svc_Status'};
          my $SRD_SvcInstance = $sr_down_tmp_HOH{$hash_keyA}->{'SvcInstance'};
          if (($SRD_SvcInstance eq $ST_SvcInstance) && ($ST_Svc_Status ne '')) {
             $bsloss = "TRUE";
             $bs_status = $ST_Svc_Status;
          }
       } # scheme_tmp
       if ($ssloss eq "TRUE") {
          $sr_down_tmp_HOH{$hash_keyA}->{'SS_Status'} = $ss_status;
       } else {
          $sr_down_tmp_HOH{$hash_keyA}->{'SS_Status'} = 'SS Downgraded';
       }
       if ($sgloss eq "TRUE") {
          $sr_down_tmp_HOH{$hash_keyA}->{'SG_Status'} = $sg_status;
       } else {
          $sr_down_tmp_HOH{$hash_keyA}->{'SG_Status'} = 'SG Downgraded';
       }
       if ($bsloss eq "TRUE") {
          $sr_down_tmp_HOH{$hash_keyA}->{'Svc_Status'} = $bs_status;
       } else {
          $sr_down_tmp_HOH{$hash_keyA}->{'Svc_Status'} = 'Svc Downgraded';
       }
    }
    # Update SchemeGroup status based Scheme service status and update Scheme_tmp table Svc_Status
    # now for each SvcInstance affected, go through the each SS state, based on SS Lost/SS Degrade of SS
    foreach my $hash_keyA(keys %sr_down_tmp_HOH) {
       my $SRD_SRInstance = $sr_down_tmp_HOH{$hash_keyA}->{'SRInstance'};
       my $SRD_SSInstance = $sr_down_tmp_HOH{$hash_keyA}->{'SSInstance'};
       my $SRD_SGInstance = $sr_down_tmp_HOH{$hash_keyA}->{'SGInstance'};
       my $SRD_SvcInstance = $sr_down_tmp_HOH{$hash_keyA}->{'SvcInstance'};
       # multiple SS may belong to only 1 SchemeGroup (child->parent)
       foreach my $hash_keyB(keys %schemeInfo_HOH) {
          my $SS_SvcInstance = $schemeInfo_HOH{$hash_keyB}->{'SvcInstance'};
          if ($SS_SvcInstance eq $SRD_SGInstance) {
             my $SRD_SS_Status = $sr_down_tmp_HOH{$hash_keyA}->{'SS_Status'};
             my $SS_ProtectedScheme = $schemeInfo_HOH{$hash_keyB}->{'ProtectedScheme'};
             my $SS_ProtectedSS_Status = $schemeInfo_HOH{$hash_keyB}->{'ProtectedSS_Status'};
             if (($SS_ProtectedScheme eq $SRD_SSInstance) && ($SS_ProtectedSS_Status eq '')) {
                $schemeInfo_HOH{$hash_keyB}->{'ProtectedSS_Status'} = $SRD_SS_Status;
             }
             my $SS_ProtectingScheme = $schemeInfo_HOH{$hash_keyB}->{'ProtectingScheme'};
             my $SS_ProtectingSS_Status = $schemeInfo_HOH{$hash_keyB}->{'ProtectingSS_Status'};
             if (($SS_ProtectingScheme eq $SRD_SSInstance) && ($SS_ProtectingSS_Status eq '')) {
                $schemeInfo_HOH{$hash_keyB}->{'ProtectingSS_Status'} = $SRD_SS_Status;
             }
          }
       }
       # multiple SG may belong to only 1 SvcInstance (child->parent)
       foreach my $hash_keyB(keys %schemeGroup_HOH) {
          my $SG_SvcInstance = $schemeGroup_HOH{$hash_keyB}->{'SvcInstance'};
          if ($SG_SvcInstance eq $SRD_SvcInstance) {
             my $SRD_SG_Status = $sr_down_tmp_HOH{$hash_keyA}->{'SG_Status'};
             my $SG_ProtectedScheme = $schemeGroup_HOH{$hash_keyB}->{'ProtectedScheme'};
             my $SG_ProtectedSG_Status = $schemeGroup_HOH{$hash_keyB}->{'ProtectedSG_Status'};
             if (($SG_ProtectedScheme eq $SRD_SGInstance) && ($SG_ProtectedSG_Status eq '')) {
                $schemeGroup_HOH{$hash_keyB}->{'ProtectedSG_Status'} = $SRD_SG_Status;
             }
             my $SG_ProtectingScheme = $schemeGroup_HOH{$hash_keyB}->{'ProtectingScheme'};
             my $SG_ProtectingSG_Status = $schemeGroup_HOH{$hash_keyB}->{'ProtectingSG_Status'};
             if (($SG_ProtectingScheme eq $SRD_SGInstance) && ($SG_ProtectingSG_Status eq '')) {
                $schemeGroup_HOH{$hash_keyB}->{'ProtectingSG_Status'} = $SRD_SG_Status;
             }
          }
       }
    }
    # Summary format for degraded alarms
    foreach my $hash_keyA(keys %sr_down_tmp_HOH) {
       my $ss_status = '';
       my $svc_status = '';
       my $SRD_Svc_Status = $sr_down_tmp_HOH{$hash_keyA}->{'Svc_Status'};
       my $SRD_SvcInstance = $sr_down_tmp_HOH{$hash_keyA}->{'SvcInstance'};
       if ($SRD_Svc_Status eq '') {
          $svc_status = 'Normal';
       } elsif ($SRD_Svc_Status =~ /Svc Loss/) {
          $svc_status = 'Loss';
       } elsif ($SRD_Svc_Status =~ /Svc Downgraded/) {
          $svc_status = 'Downgraded';
       }
       
       my $summary = $SRD_SvcInstance . ' ' . $svc_status . ' : ';
       # Get All SchemeGroups under BS
       foreach my $hash_keyB(keys %schemeGroup_HOH) {
          my $SG_SvcInstance = $schemeGroup_HOH{$hash_keyB}->{'SvcInstance'};
          if ($SG_SvcInstance eq $SRD_SvcInstance) {
             my $SG_ProtectedScheme = $schemeGroup_HOH{$hash_keyB}->{'ProtectedScheme'};
             $summary = $summary . $SG_ProtectedScheme . ' : ';
             # Get All SchemeService under SG
             foreach my $hash_keyC(keys %schemeInfo_HOH) {
                my $SS_SvcInstance = $schemeInfo_HOH{$hash_keyC}->{'SvcInstance'};
                if ($SS_SvcInstance eq $SG_ProtectedScheme) {
                   my $SS_ProtectedSS_Status = $schemeInfo_HOH{$hash_keyC}->{'ProtectedSS_Status'};
                   my $SS_ProtectedScheme = $schemeInfo_HOH{$hash_keyC}->{'ProtectedScheme'};
                   if ($SS_ProtectedSS_Status eq '') {
                      $ss_status = 'Normal';
                   } elsif ($SS_ProtectedSS_Status =~ /SS Loss/) {
                      $ss_status = 'Loss';
                   } elsif ($SS_ProtectedSS_Status =~ /SS Downgraded/) {
                      $ss_status = 'Downgraded';
                   }
                   $summary = $summary . $SS_ProtectedScheme . ' ' . $ss_status . ' ';
                }
             }
          }
       }
       $sr_down_tmp_HOH{$hash_keyA}->{'Summary'} = $summary;
    }
    # End of Summary format for degraded alarms
    
    # Generate Scheme Service degrade Alarm
    foreach my $hash_keyA(keys %sr_down_tmp_HOH) {
       # Check scheme_tmp table for SS,SG and BS status. If it is already set it implies
       # some other scheme route under SS is loss
       my $ssloss = "FALSE";
       my $sgloss = "FALSE";
       my $bsloss = "FALSE";
       my $SRD_Summary = $sr_down_tmp_HOH{$hash_keyA}->{'Summary'};
       my $SRD_SSInstance = $sr_down_tmp_HOH{$hash_keyA}->{'SSInstance'};
       my $SRD_SGInstance = $sr_down_tmp_HOH{$hash_keyA}->{'SGInstance'};
       my $SRD_SvcInstance = $sr_down_tmp_HOH{$hash_keyA}->{'SvcInstance'};
       foreach my $hash_keyB(keys %scheme_tmp_HOH) {
          # Check Scheme service status
          my $ST_SSInstance = $scheme_tmp_HOH{$hash_keyB}->{'SSInstance'};
          my $ST_SS_Status = $scheme_tmp_HOH{$hash_keyB}->{'SS_Status'};
          if (($SRD_SSInstance eq $ST_SSInstance) && ($ST_SS_Status ne '')) {
             $ssloss = "TRUE";
          }
          # Check Scheme group status
          my $ST_SGInstance = $scheme_tmp_HOH{$hash_keyB}->{'SGInstance'};
          my $ST_SG_Status = $scheme_tmp_HOH{$hash_keyB}->{'SG_Status'};
          if (($SRD_SGInstance eq $ST_SGInstance) && ($ST_SG_Status ne '')) {
             $sgloss = "TRUE";
          }
          # Check business service status
          my $ST_SvcInstance = $scheme_tmp_HOH{$hash_keyB}->{'SvcInstance'};
          my $ST_Svc_Status = $scheme_tmp_HOH{$hash_keyB}->{'Svc_Status'};
          if (($SRD_SvcInstance eq $ST_SvcInstance) && ($ST_Svc_Status ne '')) {
             $bsloss = "TRUE";
          }
       } # scheme_tmp
       my $SRD_SRInstance = $sr_down_tmp_HOH{$hash_keyA}->{'SRInstance'};
       my $SRD_SR_Status = $sr_down_tmp_HOH{$hash_keyA}->{'SR_Status'};
       my $SRD_FMSAlertKey = $sr_down_tmp_HOH{$hash_keyA}->{'FMSAlertKey'};
       my $SRD_SRProvisionStatus = $sr_down_tmp_HOH{$hash_keyA}->{'SRProvisionStatus'};
       my $SRD_RawAlarmID = $sr_down_tmp_HOH{$hash_keyA}->{'RawAlarmID'};
       my $SRD_ProtectedCircuit = $sr_down_tmp_HOH{$hash_keyA}->{'ProtectedCircuit'};
       my $SRD_ProtectingCircuit = $sr_down_tmp_HOH{$hash_keyA}->{'ProtectingCircuit'};
       my $SRD_Svc_BusPriority = $sr_down_tmp_HOH{$hash_keyA}->{'Svc_BusPriority'};
       my $SRD_Svc_ServiceID = $sr_down_tmp_HOH{$hash_keyA}->{'Svc_ServiceID'};
       my $SRD_Svc_SubSvcName = $sr_down_tmp_HOH{$hash_keyA}->{'Svc_SubSvcName'};
       if (($SRD_SRInstance ne '') && ($SRD_SR_Status ne '')) {
          my $Last_RawAlarmID = $last_alarm_id{$SRD_SRInstance}->{'RawAlarmID'};
          my $Last_FMSAlertKey = $last_alarm_id{$SRD_SRInstance}->{'FMSAlertKey'};
          # insert syn alarm
          UpdateSynthetic_alarm_storage_HOH($SRD_SRInstance,'Scheme Route Downgraded',$Last_FMSAlertKey,$SRD_SRProvisionStatus,
          $SRD_ProtectedCircuit,$SRD_ProtectingCircuit,$SRD_Svc_BusPriority,$SRD_Svc_ServiceID,$SRD_Svc_SubSvcName,$Last_RawAlarmID,4,$Null_Summary);
       }
       
       my $SRD_SS_Status = $sr_down_tmp_HOH{$hash_keyA}->{'SS_Status'};
       my $SRD_SSProvisionStatus = $sr_down_tmp_HOH{$hash_keyA}->{'SSProvisionStatus'};
       if ((($SRD_SSInstance ne '') && ($SRD_SS_Status ne '')) && ($ssloss eq "FALSE")) {
          my $Last_RawAlarmID = $last_alarm_id{$SRD_SRInstance}->{'RawAlarmID'};
          my $Last_FMSAlertKey = $last_alarm_id{$SRD_SRInstance}->{'FMSAlertKey'};
          # insert syn alarm
          UpdateSynthetic_alarm_storage_HOH($SRD_SSInstance,'Scheme Service Downgraded',$Last_FMSAlertKey,$SRD_SSProvisionStatus,
          $SRD_ProtectedCircuit,$SRD_ProtectingCircuit,$SRD_Svc_BusPriority,$SRD_Svc_ServiceID,
          $SRD_Svc_SubSvcName,$Last_RawAlarmID,4,$Null_Summary);
       }
       
       # Generate Scheme Group degrade Alarm
       my $SRD_SG_Status = $sr_down_tmp_HOH{$hash_keyA}->{'SG_Status'};
       my $SRD_SGProvisionStatus = $sr_down_tmp_HOH{$hash_keyA}->{'SGProvisionStatus'};
       if ((($SRD_SGInstance ne '') && ($SRD_SG_Status ne '')) && ($sgloss eq "FALSE")) {
          my $Last_RawAlarmID = $last_alarm_id{$SRD_SRInstance}->{'RawAlarmID'};
          my $Last_FMSAlertKey = $last_alarm_id{$SRD_SRInstance}->{'FMSAlertKey'};
          # insert syn alarm
          UpdateSynthetic_alarm_storage_HOH($SRD_SGInstance,'Scheme Group Downgraded',$Last_FMSAlertKey,$SRD_SGProvisionStatus,
          $SRD_ProtectedCircuit,$SRD_ProtectingCircuit,$SRD_Svc_BusPriority,$SRD_Svc_ServiceID,
          $SRD_Svc_SubSvcName,$Last_RawAlarmID,4,$Null_Summary);
       }
       
       # Generate Business Service degrade Alarm
       my $SRD_Svc_Status = $sr_down_tmp_HOH{$hash_keyA}->{'Svc_Status'};
       my $SRD_SvcProvisionStatus = $sr_down_tmp_HOH{$hash_keyA}->{'SvcProvisionStatus'};
       if ((($SRD_SvcInstance ne '') && ($SRD_Svc_Status ne '')) && ($bsloss eq "FALSE")) {
          my $Last_RawAlarmID = $last_alarm_id{$SRD_SRInstance}->{'RawAlarmID'};
          my $Last_FMSAlertKey = $last_alarm_id{$SRD_SRInstance}->{'FMSAlertKey'};
          # insert syn alarm
          UpdateSynthetic_alarm_storage_HOH($SRD_SvcInstance,'Service Downgraded',$Last_FMSAlertKey,$SRD_SvcProvisionStatus,
          $SRD_ProtectedCircuit,$SRD_ProtectingCircuit,$SRD_Svc_BusPriority,$SRD_Svc_ServiceID,
          $SRD_Svc_SubSvcName,$Last_RawAlarmID,4,$SRD_Summary);
          # Update the raw alarm with as much info as it can get (note no Svc level info available)
          foreach my $hash_keyB(keys %alerts_status_tmp) {
		     my $AS_ServerName_ServerSerial = $alerts_status_tmp{$hash_keyB}->{'ServerName_ServerSerial'};
		     my $AS_ImpactedStatus = $alerts_status_tmp{$hash_keyB}->{'ImpactedStatus'};
		     my $AS_BusPriority = $alerts_status_tmp{$hash_keyB}->{'BusPriority'};
             if ($AS_ServerName_ServerSerial eq $SRD_RawAlarmID) {
			   if ($AS_BusPriority < $SRD_Svc_BusPriority) {
			      UpdateAlerts_status($dbHandle,$SRD_ProtectingCircuit,$SRD_ProtectedCircuit,$SRD_SvcInstance,
			      $SRD_Svc_BusPriority,$SRD_Svc_ServiceID,$SRD_Svc_SubSvcName,$SRD_RawAlarmID,'Service Downgraded');
			      UpdateAlerts_status_tmp($SRD_ProtectingCircuit,$SRD_ProtectedCircuit,$SRD_SvcInstance,
			      $SRD_Svc_BusPriority,$SRD_Svc_ServiceID,$SRD_Svc_SubSvcName,$SRD_RawAlarmID,'Service Downgraded');
			   }
               if (($SRD_SRProvisionStatus eq 'Live') || ($SRD_SRProvisionStatus eq 'In Service') || ($SRD_SRProvisionStatus eq '')) {
                UpdateAlerts_status_SuppressEscl($dbHandle,0,$SRD_RawAlarmID,6);
               }
               last;
             }
          }
       }
    }
	perfCalc('end','SIA_process_TP_svcs3');
}

sub copy_service_tmp_to_svc_inst_tmp {
   my ($service_tmp_hash) = @_;
   
   #print "-- In copy_service_tmp_to_svc_inst_tmp sub, service_tmp_hash content:\n--$service_tmp_hash->{'FMSAlertKey'},$service_tmp_hash->{'SvcInstance'},$service_tmp_hash->{'ProvisionStatus'},$service_tmp_hash->{'ProtectedCircuit'},$service_tmp_hash->{'ProtectingCircuit'},$service_tmp_hash->{'BusSvcName'},$service_tmp_hash->{'SubSvcName'},$service_tmp_hash->{'BusPriority'},$service_tmp_hash->{'RawAlarmID'}\n";
    
   Load_svc_inst_tmp(0,$service_tmp_hash->{'FMSAlertKey'},
    $service_tmp_hash->{'SvcInstance'},
    $service_tmp_hash->{'ProvisionStatus'},
    $service_tmp_hash->{'ProtectedCircuit'},
    $service_tmp_hash->{'ProtectingCircuit'},
    $service_tmp_hash->{'BusSvcName'},
    $service_tmp_hash->{'SubSvcName'},
    $service_tmp_hash->{'BusPriority'},
    $service_tmp_hash->{'RawAlarmID'});
}

sub copy_scheme_tmp_to_sr_down_tmp {
   my ($scheme_tmp_hash) = @_;
   
   #print "-- In copy_scheme_tmp_to_sr_down_tmp sub, scheme_tmp_hash content:\n--$scheme_tmp_hash->{'FMSAlertKey'},$scheme_tmp_hash->{'RawAlarmID'},$scheme_tmp_hash->{'ProtectingCircuit'},$scheme_tmp_hash->{'ProtectedCircuit'},$scheme_tmp_hash->{'IsCirProtected'},$scheme_tmp_hash->{'SRInstance'},$scheme_tmp_hash->{'SSInstance'},$scheme_tmp_hash->{'SvcInstance'},$scheme_tmp_hash->{'SRProvisionStatus'},$scheme_tmp_hash->{'SSProvisionStatus'},$scheme_tmp_hash->{'SvcProvisionStatus'},$scheme_tmp_hash->{'SS_Status'},$scheme_tmp_hash->{'Svc_Status'},$scheme_tmp_hash->{'Svc_ServiceID'},$scheme_tmp_hash->{'Svc_SubSvcName'},$scheme_tmp_hash->{'Svc_BusPriority'},$scheme_tmp_hash->{'SGInstance'},$scheme_tmp_hash->{'SGProvisionStatus'},$scheme_tmp_hash->{'SG_Status'},$scheme_tmp_hash->{'Summary'},$scheme_tmp_hash->{'SR_Status'}\n";
   
   Load_svc_inst_tmp(0,$scheme_tmp_hash->{'FMSAlertKey'},
    $scheme_tmp_hash->{'RawAlarmID'},
    $scheme_tmp_hash->{'ProtectingCircuit'},
    $scheme_tmp_hash->{'ProtectedCircuit'},
    $scheme_tmp_hash->{'IsCirProtected'},
	$scheme_tmp_hash->{'SRInstance'},
    $scheme_tmp_hash->{'SSInstance'},
    $scheme_tmp_hash->{'SvcInstance'},
    $scheme_tmp_hash->{'SRProvisionStatus'},
    $scheme_tmp_hash->{'SSProvisionStatus'},
    $scheme_tmp_hash->{'SvcProvisionStatus'},
    $scheme_tmp_hash->{'SS_Status'},
    $scheme_tmp_hash->{'Svc_Status'},
    $scheme_tmp_hash->{'Svc_ServiceID'},
    $scheme_tmp_hash->{'Svc_SubSvcName'},
    $scheme_tmp_hash->{'Svc_BusPriority'},
    $scheme_tmp_hash->{'SGInstance'},
    $scheme_tmp_hash->{'SGProvisionStatus'},
    $scheme_tmp_hash->{'SG_Status'},
    $scheme_tmp_hash->{'Summary'},
    $scheme_tmp_hash->{'SR_Status'});
}

sub SIA_process_svcs($) {
	my ($dbHandle)= @_;
	logInfo('Starting SIA Process svcs '.nl); 
	perfCalc('start','SIA_process_svcs');
               logInfo('step 1'.nl);
               printservice_tmp();
               printsvc_inst_tmp();

	#-----------------------------
	# remove the overlap part which is protected.
	# this means even though service_tmp service is not circuit protected, on a higher level of it maybe 
	# circuit protected. Therefore delete the duplicated services from service_tmp
	#-----------------------------
  my $change = 0;
  do {
	$change = 0;
	my $loop_cnt = 0;
	foreach my $hash_keyA(keys %svc_inst_tmp_HOH) {
	  my $SI_SvcInstance = $svc_inst_tmp_HOH{$hash_keyA}->{'SvcInstance'};
	  my $SI_FMSAlertKey = $svc_inst_tmp_HOH{$hash_keyA}->{'FMSAlertKey'};
	  my $SI_ProtectedCircuit = $svc_inst_tmp_HOH{$hash_keyA}->{'ProtectedCircuit'};
	  foreach my $hash_keyB(keys %service_tmp_HOH) {
	  	my $ST_FMSAlertKey = $service_tmp_HOH{$hash_keyB}->{'FMSAlertKey'};
	  	my $ST_SvcInstance = $service_tmp_HOH{$hash_keyB}->{'SvcInstance'};
	  	my $ST_ProtectedCircuit = $service_tmp_HOH{$hash_keyB}->{'ProtectedCircuit'};
	  	if ( ($ST_SvcInstance eq $SI_SvcInstance) && 
	  	     (($ST_FMSAlertKey =~ /$SI_FMSAlertKey/) || ($SI_FMSAlertKey =~ /$ST_FMSAlertKey/)) &&
	  	     (isInHierarchy($SI_ProtectedCircuit,$ST_ProtectedCircuit,$SI_SvcInstance)) &&
	  	     (HierarchySafe($SI_ProtectedCircuit,$ST_ProtectedCircuit,$SI_SvcInstance,'service_tmp')) ) {
	  	    $loop_cnt++;
	  	    logInfo('Match moved - '.$loop_cnt.nl);
	  	    $change = 1;
	  	    copy_service_tmp_to_svc_inst_tmp($service_tmp_HOH{$hash_keyB});
	  	    delete $service_tmp_HOH{$hash_keyB}; # actually moved to $svc_inst_tmp_HOH
	  	}
	  }
	}
               logInfo('step 2'.nl);
               printservice_tmp();
               printsvc_inst_tmp();

	#-----------------------------
	# Some services that have now been removed from service_tmp need to be revisited as they no longer cause
	# their protected circuit to be down. 
	# Once the protected circuits are removed, Remove all underlying circuits from service_tmp as well.
	#-----------------------------
	foreach my $hash_keyA(keys %service_tmp_HOH) {
		my $lossfound = "FALSE";
		
		my $CTL_ProtectedCircuit = $service_tmp_HOH{$hash_keyA}->{'ProtectedCircuit'};
		if (!defined $CTL_ProtectedCircuit) {
		   delete $service_tmp_HOH{$hash_keyA}; # already moved to $svc_inst_tmp_HOH below, cleaning up
		   next;
		}
		my $CTL_ProtectingCircuit = $service_tmp_HOH{$hash_keyA}->{'ProtectingCircuit'};
		my $CTL_FMSAlertKey = $service_tmp_HOH{$hash_keyA}->{'FMSAlertKey'};
		my $CTL_SvcInstance = $service_tmp_HOH{$hash_keyA}->{'SvcInstance'};
		my $CTL_ProvisionStatus = $service_tmp_HOH{$hash_keyA}->{'ProvisionStatus'};
		my $CTL_BusSvcName = $service_tmp_HOH{$hash_keyA}->{'BusSvcName'};
		my $CTL_SubSvcName = $service_tmp_HOH{$hash_keyA}->{'SubSvcName'};
		my $CTL_BusPriority = $service_tmp_HOH{$hash_keyA}->{'BusPriority'};
		my $CTL_RawAlarmID = $service_tmp_HOH{$hash_keyA}->{'RawAlarmID'};
		foreach my $hash_keyB(keys %service_tmp_HOH) {
			my $CTD_ProtectedCircuit = $service_tmp_HOH{$hash_keyB}->{'ProtectedCircuit'};
			my $CTD_SvcInstance = $service_tmp_HOH{$hash_keyB}->{'SvcInstance'};
			my $CTD_FMSAlertKey = $service_tmp_HOH{$hash_keyB}->{'FMSAlertKey'};
			if ( ($CTD_ProtectedCircuit =~ /$CTL_ProtectingCircuit/) && ($CTD_ProtectedCircuit ne '') ) {
# This pattern match breaks when there are regex characters (eg +)in the $CTL_ProtectingCircuit
				$lossfound = "TRUE"; # set to TRUE
			}
		}
		# if lossfound equals false
		if ($lossfound eq "FALSE") {
			#logInfo('loading svc_inst_tmp'.nl);
			foreach my $hash_keyB(keys %service_tmp_HOH) {
				my $CTD_ProtectedCircuit = $service_tmp_HOH{$hash_keyB}->{'ProtectedCircuit'};
				my $CTD_SvcInstance = $service_tmp_HOH{$hash_keyB}->{'SvcInstance'};
				my $CTD_FMSAlertKey = $service_tmp_HOH{$hash_keyB}->{'FMSAlertKey'};
				if ( ($CTD_ProtectedCircuit ne '') &&
				($CTD_SvcInstance eq $CTL_SvcInstance) && ( $CTD_FMSAlertKey =~ /$CTL_FMSAlertKey/) &&
	  	     (isInHierarchy($CTL_ProtectedCircuit,$CTD_ProtectedCircuit,$CTD_SvcInstance)) &&
	  	     (HierarchySafe($CTL_ProtectedCircuit,$CTD_ProtectedCircuit,$CTD_SvcInstance,'service_tmp')) ) {
					logInfo('Match2 moved'.nl);
					$change = 1;
					copy_service_tmp_to_svc_inst_tmp($service_tmp_HOH{$hash_keyB});
			  		delete $service_tmp_HOH{$hash_keyB}; # actually moved to $svc_inst_tmp_HOH
			  	}
			}
		}
	}
  } until !$change;
               logInfo('step 3'.nl);
               printservice_tmp();
               printsvc_inst_tmp();
  
	#-----------------------------	
	# remove the service with part protection in svc_inst_tmp but other segment unprotected.
	# remove the protected services in svc_inst_tmp, because the same service is already lost in service_tmp,
	# doesnt consider the same FMSAlertKey point of failure, because if one point is lost elsewhere, the whole 
	# service is lost
	#-----------------------------
	logInfo('Number of entries in service_tmp_HOH at start is '.scalar(keys %service_tmp_HOH).nl);
	foreach my $hash_keyA(keys %service_tmp_HOH) {
		my $STL_SvcInstance = $service_tmp_HOH{$hash_keyA}->{'SvcInstance'};
		my $STL_RawAlarmID = $service_tmp_HOH{$hash_keyA}->{'RawAlarmID'};
		foreach my $hash_keyB(keys %svc_inst_tmp_HOH) {
			my $SI_SvcInstance = $svc_inst_tmp_HOH{$hash_keyB}->{'SvcInstance'};
			if ($SI_SvcInstance eq $STL_SvcInstance) {
				#logInfo('delete match part 3'.nl);
				delete $svc_inst_tmp_HOH{$hash_keyB};
			}
		}
		# remove the duplicated info in service_tmp
		foreach my $hash_keyC(keys %service_tmp_HOH) {
			my $ST_SvcInstance = $service_tmp_HOH{$hash_keyC}->{'SvcInstance'};
			my $ST_RawAlarmID = $service_tmp_HOH{$hash_keyC}->{'RawAlarmID'};
			if ( ($ST_SvcInstance eq $STL_SvcInstance) && ($ST_RawAlarmID eq $STL_RawAlarmID) &&
			($hash_keyA !=  $hash_keyC)  ) {
				#logInfo('removing duplicate in service tmp'.nl);
				delete $service_tmp_HOH{$hash_keyC};
			}
		}
	}
	logInfo('Number of entries in service_tmp_HOH at end is '.scalar(keys %service_tmp_HOH).nl);
               logInfo('step 4'.nl);
               printservice_tmp();
               printsvc_inst_tmp();
	
	#-----------------------------
	# loss service related alarm (service_tmp)
	#-----------------------------
	foreach my $hash_keyA(keys %service_tmp_HOH) {
		my $protectedCircuit = '';
		my $STL_ProtectingCircuit = $service_tmp_HOH{$hash_keyA}->{'ProtectingCircuit'};
		my $STL_RawAlarmID = $service_tmp_HOH{$hash_keyA}->{'RawAlarmID'};
		my $STL_BusPriority = $service_tmp_HOH{$hash_keyA}->{'BusPriority'};
		my $STL_SvcInstance = $service_tmp_HOH{$hash_keyA}->{'SvcInstance'};
		my $STL_BusSvcName = $service_tmp_HOH{$hash_keyA}->{'BusSvcName'}; 
		my $STL_SubSvcName = $service_tmp_HOH{$hash_keyA}->{'SubSvcName'};
		my $STL_ProvisionStatus = $service_tmp_HOH{$hash_keyA}->{'ProvisionStatus'};

		foreach my $hash_keyB(keys %alerts_status_tmp) {
			my $AS_ServerName_ServerSerial = $alerts_status_tmp{$hash_keyB}->{'ServerName_ServerSerial'};
			my $AS_BusPriority = $alerts_status_tmp{$hash_keyB}->{'BusPriority'};
			my $AS_ServicesImpacted = $alerts_status_tmp{$hash_keyB}->{'ServicesImpacted'};
			my $AS_FMSAlertKey = $alerts_status_tmp{$hash_keyB}->{'FMSAlertKey'};
			my $AS_SuppressEscl = $alerts_status_tmp{$hash_keyB}->{'SuppressEscl'};

			if ($AS_ServerName_ServerSerial eq $STL_RawAlarmID) {
				if ($STL_ProtectingCircuit ne '') {
					$protectedCircuit = $STL_ProtectingCircuit;
				}
				# mark the alarm with service impacted with highest BIR, default is 0	
				if ($AS_BusPriority < $STL_BusPriority) {
					#logInfo('Service loss update triggered'.nl);
					UpdateAlerts_status($dbHandle,$STL_ProtectingCircuit,$protectedCircuit,$STL_SvcInstance,
					$STL_BusPriority,$STL_BusSvcName,$STL_SubSvcName,$STL_RawAlarmID,'Service Loss');
					UpdateAlerts_status_tmp($STL_ProtectingCircuit,$protectedCircuit,$STL_SvcInstance,
					$STL_BusPriority,$STL_BusSvcName,$STL_SubSvcName,$STL_RawAlarmID,'Service Loss');
				}
				# increment on each service loss
				$AS_ServicesImpacted++;
				UpdateAlerts_status_ServiceLosscounter($dbHandle,$AS_ServicesImpacted,$STL_RawAlarmID);
				$alerts_status_tmp{$hash_keyB}->{'ServicesImpacted'} = $AS_ServicesImpacted;
				
				# Load a synthetic alarm into HOH 
				#logInfo('Load synthetic alarm'.nl);
                my $Last_RawAlarmID = $last_alarm_id{$STL_SvcInstance}->{'RawAlarmID'};
                my $Last_FMSAlertKey = $last_alarm_id{$STL_SvcInstance}->{'FMSAlertKey'};
				UpdateSynthetic_alarm_storage_HOH($STL_SvcInstance,'Service Loss',$Last_FMSAlertKey,$STL_ProvisionStatus,
				$protectedCircuit,$STL_ProtectingCircuit,$STL_BusPriority,$STL_BusSvcName,$STL_SubSvcName,$Last_RawAlarmID,'5',$Null_Summary);
				
				# a live/in service provision status of the loss BSVC will move the raw alarm out of maintenance 
				# suppression, allowing AutoTT to be raised against it. However, a non-live provision status of 
				# the loss BSVC will NOT move the raw alarm into maintenance suppression, AutoTT can still be triggered
				if (($STL_ProvisionStatus eq 'Live') || ($STL_ProvisionStatus eq 'In Service') ||
				 ($STL_ProvisionStatus eq '') && ($AS_SuppressEscl == 6 )) {
				 	#logInfo('Inserting into alerts status'.nl);
				 	UpdateAlerts_status_SuppressEscl($dbHandle,0,$STL_RawAlarmID,6);
				 }
			}
			last if ($AS_ServerName_ServerSerial eq $STL_RawAlarmID);
		}
	}

	#-----------------------------
	# degraded service related alarm (svc_inst_tmp)
	#-----------------------------
	# svc_inst_tmp_HOH
	foreach my $hash_keyA(keys %svc_inst_tmp_HOH) {
		my $protectedCircuit = '';
		my $SID_ProtectedCircuit = $svc_inst_tmp_HOH{$hash_keyA}->{'ProtectedCircuit'};
		my $SID_ProtectingCircuit = $svc_inst_tmp_HOH{$hash_keyA}->{'ProtectingCircuit'};
		my $SID_RawAlarmID = $svc_inst_tmp_HOH{$hash_keyA}->{'RawAlarmID'};
		my $SID_BusPriority = $svc_inst_tmp_HOH{$hash_keyA}->{'BusPriority'};
		my $SID_ProvisionStatus = $svc_inst_tmp_HOH{$hash_keyA}->{'ProvisionStatus'};
		my $SID_SvcInstance = $svc_inst_tmp_HOH{$hash_keyA}->{'SvcInstance'};
		my $SID_BusSvcName  = $svc_inst_tmp_HOH{$hash_keyA}->{'BusSvcName'};
		my $SID_SubSvcName  = $svc_inst_tmp_HOH{$hash_keyA}->{'SubSvcName'};
		if ($SID_ProtectedCircuit ne '') {
			$protectedCircuit = $SID_ProtectedCircuit;
		}
		
		foreach my $hash_keyB(keys %alerts_status_tmp) {
			my $AS_ServerName_ServerSerial = $alerts_status_tmp{$hash_keyB}->{'ServerName_ServerSerial'}; # this is always blank
			my $AS_BusPriority = $alerts_status_tmp{$hash_keyB}->{'BusPriority'};
			my $AS_SuppressEscl = $alerts_status_tmp{$hash_keyB}->{'SuppressEscl'};
			my $AS_FMSAlertKey = $alerts_status_tmp{$hash_keyB}->{'FMSAlertKey'};
			
			if ($AS_ServerName_ServerSerial eq $SID_RawAlarmID){
				# a service downgrade can still overwrite service loss info on raw alarm, due to highest BIR rule
				if ($AS_BusPriority < $SID_BusPriority) {
					# Update alert status 
					#logInfo('updating Alert status'.nl);
					UpdateAlerts_status($dbHandle,$SID_ProtectingCircuit,$protectedCircuit,$SID_SvcInstance,
					$SID_BusPriority,$SID_BusSvcName,$SID_SubSvcName,$SID_RawAlarmID,'Service Downgraded');
					UpdateAlerts_status_tmp($SID_ProtectingCircuit,$protectedCircuit,$SID_SvcInstance,
					$SID_BusPriority,$SID_BusSvcName,$SID_SubSvcName,$SID_RawAlarmID,'Service Downgraded');
				}
				# Load a synthetic alarm into HOH 
				#logInfo('Loading synthetic alarm'.nl);
                my $Last_RawAlarmID = $last_alarm_id{$SID_SvcInstance}->{'RawAlarmID'};
                my $Last_FMSAlertKey = $last_alarm_id{$SID_SvcInstance}->{'FMSAlertKey'};
				UpdateSynthetic_alarm_storage_HOH($SID_SvcInstance,'Service Downgraded',$Last_FMSAlertKey,$SID_ProvisionStatus,
				$protectedCircuit,$SID_ProtectingCircuit,$SID_BusPriority,$SID_BusSvcName,$SID_SubSvcName,$Last_RawAlarmID,'4',$Null_Summary);
				
				if (($SID_ProvisionStatus eq 'Live') || ($SID_ProvisionStatus eq 'In Service') ||
				 ($SID_ProvisionStatus eq '') && ($AS_SuppressEscl == 6 )) {
				 	UpdateAlerts_status_SuppressEscl($dbHandle,0,$SID_RawAlarmID,6);
				 }
			}
			last if ($AS_ServerName_ServerSerial eq $SID_RawAlarmID);
		}
	}
	perfCalc('end','SIA_process_svcs');
	my $SVI_count = scalar(keys %svc_inst_tmp_HOH);
	my $ST_count = scalar(keys %service_tmp_HOH);
	my $SRD_count = scalar(keys %sr_down_tmp_HOH);
	my $Scheme_tmp_count = scalar(keys %scheme_tmp_HOH);
	my $Synthetic_alarm_storage_count = scalar(keys %Synthetic_alarm_storage_HOH);
	logInfo("Temp table basic analysis of data".nl.
	 "Number of records in svc_inst_tmp is $SVI_count".nl.
	 "Number of records in service_tmp is $ST_count".nl.
	 "Number of records in sr_down_tmp is $SRD_count".nl.
	 "Number of records in scheme_tmp is $Scheme_tmp_count".nl.
	 "Number of records in Synthetic_alarm_storage is $Synthetic_alarm_storage_count".nl);;
}

sub Check_alerts_status_dataset(){
	my $ASforcount = 0;
	my $alerts_status_tmp_AOA_count = scalar(@alerts_status_tmp_AOA); # alerts_status_tmp_AOA
	for ( $ASforcount ; $ASforcount < $alerts_status_tmp_AOA_count  ; $ASforcount++ ) {
		my $AS_Type = $alerts_status_tmp_AOA[$ASforcount][15];
		my $AS_Severity = $alerts_status_tmp_AOA[$ASforcount][8];
		my $AS_ServiceImpactingFlag = $alerts_status_tmp_AOA[$ASforcount][78];
		my $AS_FMSAlertKey = $alerts_status_tmp_AOA[$ASforcount][105];
		my $AS_SpecificProb = $alerts_status_tmp_AOA[$ASforcount][56];
		my $AS_ManagedObjClass = $alerts_status_tmp_AOA[$ASforcount][52];
		my $AS_AlarmDetails = $alerts_status_tmp_AOA[$ASforcount][104];
		my $AS_ServerName_ServerSerial = $alerts_status_tmp_AOA[$ASforcount][63];
		my $AS_Indentifier = $alerts_status_tmp_AOA[$ASforcount][0];
	}
	foreach my $hash_keyA(keys %alerts_status_tmp) {
		my $Type = $alerts_status_tmp{$hash_keyA}->{'Type'};
		my $Severity = $alerts_status_tmp{$hash_keyA}->{'Severity'};
		my $ServiceImpactingFlag = $alerts_status_tmp{$hash_keyA}->{'ServiceImpactingFlag'};
		my $Identifier = $alerts_status_tmp{$hash_keyA}->{'Identifier'};
	}
}

sub Synthetic_si_alarm_Trigger() {
	my $PrimaryMatchCount = 0;
	my $PrimaryDetectionCount = 0;
	my $SecondaryDetectionCount = 0;
	my $ASforcount = 0;
#	my $alerts_status_tmp_AOA_count = scalar(@alerts_status_tmp_AOA); # alerts_status_tmp_AOA
	logInfo('Starting Synthetic si alarm Trigger analysis '.nl); 
	#logInfo('size of array: '.@alerts_status_tmp_AOA.nl);
	perfCalc('start','synthethic_si_alarm_trigger');
	foreach my $hash_keyA(keys %alerts_status_tmp) {
		my $AS_Type = $alerts_status_tmp{$hash_keyA}->{'Type'};
		my $AS_Severity = $alerts_status_tmp{$hash_keyA}->{'Severity'};
		my $AS_ServiceImpactingFlag = $alerts_status_tmp{$hash_keyA}->{'ServiceImpactingFlag'};
		my $AS_FMSAlertKey = $alerts_status_tmp{$hash_keyA}->{'FMSAlertKey'};
		my $AS_ServerName_ServerSerial = $alerts_status_tmp{$hash_keyA}->{'ServerName_ServerSerial'};
		#logInfo("$AS_Type,$AS_Severity,$AS_ServiceImpactingFlag,$AS_FMSAlertKey,$AS_SpecificProb,$AS_ManagedObjClass".nl);
		if ( ($AS_Type == 1) && ($AS_Severity > 3) && ($AS_ServiceImpactingFlag == 1) &&
             ($AS_FMSAlertKey ne '') ) {
			$PrimaryMatchCount++;
			my $matchfound = 0;
			# check for already encountered $AS_FMSAlertKey, if true then skip
			foreach my $CI_FMSAlertKey (keys %cirlInfo_AK) {
			    my $AS_FMSAlertKey1 = $AS_FMSAlertKey . ":";
			    if ( ($CI_FMSAlertKey eq $AS_FMSAlertKey) || ($CI_FMSAlertKey =~ /^$AS_FMSAlertKey1/) ) {
			        foreach my $CI_CircuitID (@{$cirlInfo_AK{$CI_FMSAlertKey}}) {
			            LoadCircuits_tmp(0,$AS_FMSAlertKey,$CI_CircuitID,$AS_ServerName_ServerSerial);
			            $matchfound = 1;
			            $PrimaryDetectionCount++;
			        }
			    }
			}
		}
	}
	printcircuits_tmp;
	perfCalc('end','synthethic_si_alarm_trigger_part1');
	perfCalc('start','synthethic_si_alarm_trigger_part2');
	# Go through the affected circuits (circuits_tmp), and see if any service are attached
	# to it via circuitprotected.lookup (servInfo) file.
	my $count_circuits_tmp_HOH = scalar(keys %circuits_tmp_HOH);
	
	logInfo('There are ' .$count_circuits_tmp_HOH. ' rows in circuits_tmp '.nl);
	my $primarycount = 1;
	foreach my $hash_keyA(keys %circuits_tmp_HOH) {
	logInfo('foreach circuits_tmp_key A - '.$primarycount.nl);
		my $CT_count = 	$circuits_tmp_HOH{$hash_keyA}->{'count'};
		my $CT_FMSAlertKey = $circuits_tmp_HOH{$hash_keyA}->{'FMSAlertKey'};
		my $CT_CircuitID = $circuits_tmp_HOH{$hash_keyA}->{'CircuitID'};
		my $CT_RawAlarmID = $circuits_tmp_HOH{$hash_keyA}->{'RawAlarmID'};
		#logInfo("$CT_FMSAlertKey,$CT_CircuitID,$CT_RawAlarmID".nl);
		my $secondarycount = 0;
		foreach my $hash_keyB(keys %circuitProtection_HOH){
			my $CP_ProtectedCircuit = $circuitProtection_HOH{$hash_keyB}->{'ProtectedCircuit'};
			my $CP_ProtectingCircuit = $circuitProtection_HOH{$hash_keyB}->{'ProtectingCircuit'};
			my $CP_SchemeRoute = $circuitProtection_HOH{$hash_keyB}->{'SchemeRoute'};
			my $CP_SvcInstance = $circuitProtection_HOH{$hash_keyB}->{'SvcInstance'};
			my $CP_ProvisionStatus = $circuitProtection_HOH{$hash_keyB}->{'ProvisionStatus'};
			my $CP_BusSvcName = $circuitProtection_HOH{$hash_keyB}->{'BusSvcName'};
            my $CP_SubSvcName = $circuitProtection_HOH{$hash_keyB}->{'SubSvcName'};                                   
			my $CP_ServicePriority = $circuitProtection_HOH{$hash_keyB}->{'Priority'};

			if ($CP_ProtectedCircuit eq $CT_CircuitID) {
				my $protected = "TRUE";
				my $tertiarycount = 0;
				#logInfo("CP is $CP_ProtectedCircuit, CT is $CT_CircuitID".nl);
				if ($CP_ProtectingCircuit eq '') {
					$protected = "FALSE";
				} else {
					foreach my $hash_keyC(keys %circuits_tmp_HOH) {
						my $CTC_CircuitID = $circuits_tmp_HOH{$hash_keyC}->{'CircuitID'};
						if ($CP_ProtectingCircuit eq $CTC_CircuitID) {
							$protected = "FALSE";
							last;
						}
						#last if ($protected eq "FALSE");
						$tertiarycount++;
					}
	 logInfo('foreach circuits_tmp_key C - '.$tertiarycount.' '.$protected.nl);
				}

				if ($CP_SchemeRoute eq "FALSE") {
					# Other services
					if ($protected eq "TRUE") {
						#logInfo("Protection status is $protected and scheme $CP_SchemeRoute".nl);
				        #logInfo("$CP_ProtectedCircuit $CP_ProtectingCircuit $CP_SchemeRoute $CP_SvcInstance".
				        #"$CP_ProvisionStatus $CP_BusSvcName $CP_SubSvcName $CP_ServicePriority".nl);
						Load_svc_inst_tmp(0,$CT_FMSAlertKey,$CP_SvcInstance,$CP_ProvisionStatus,$CP_ProtectedCircuit,
						$CP_ProtectingCircuit,$CP_BusSvcName,$CP_SubSvcName,$CP_ServicePriority,$CT_RawAlarmID);
					} else {
						Load_service_tmp(0,$CT_FMSAlertKey,$CP_SvcInstance,$CP_ProvisionStatus,$CP_ProtectedCircuit,
						$CP_ProtectingCircuit,$CP_BusSvcName,$CP_SubSvcName,$CP_ServicePriority,$CT_RawAlarmID);
					}
				} else {
					# Teleprot service  - scheme route
					if ($protected eq "TRUE"){
						Load_sr_down_tmp(0,$CT_FMSAlertKey,$CT_RawAlarmID,$CP_ProtectingCircuit,$CP_ProtectedCircuit,
						$protected,$CP_SvcInstance,'','',$CP_ProvisionStatus,'','','','','','','',0,'','','','');
					} else {
						Load_scheme_tmp(0,$CT_FMSAlertKey,$CT_RawAlarmID,$CP_ProtectingCircuit,$CP_ProtectedCircuit,
						$protected,$CP_SvcInstance,'','',$CP_ProvisionStatus,'','','','','','','',0,'','','','');
					}
				}
			}
			$secondarycount++;
		}
	 logInfo('foreach circuitProtection_key B - '.$secondarycount.nl);
		$primarycount++;
	}
	buildLastAlarmIDHash();
	printRawAlarmID();
	perfCalc('end','synthethic_si_alarm_trigger_part2');
	PrintFourArrays();
               logInfo('step 0'.nl);
               printservice_tmp();
               printsvc_inst_tmp();
}

sub logDebug(@)
{
  my $logFileHandle=openLogFileHandle();
  if ($logFileHandle) {
    print($logFileHandle scalar(localtime(time()))." Debug   : ",@_);
    closeLogFileHandle($logFileHandle);
  }
  if ($Debug){
    print(STDERR scalar(localtime(time()))." Debug   : ",@_);
  }
}

sub logDie(@)
{
  my $logFileHandle=openLogFileHandle();
  if ($logFileHandle) {
    print($logFileHandle scalar(localtime(time()))." Fatal   : ",@_);
    print($logFileHandle scalar(localtime(time()))." Fatal   : exiting now!".nl);
    closeLogFileHandle($logFileHandle);
  }
  print(STDERR scalar(localtime(time()))." Fatal   : ",@_);
  print(STDERR scalar(localtime(time()))." Fatal   : exiting now!".nl);
  exit(1);
}

sub logWarn(@)
{
  my $logFileHandle=openLogFileHandle();
  if ($logFileHandle) {
    print($logFileHandle scalar(localtime(time()))." Warning : ",@_);
    closeLogFileHandle($logFileHandle);
  }
  if ($Debug) {
    print(STDERR scalar(localtime(time()))." Warning : ",@_);
  }
}

sub logInfo(@)
{
  my $logFileHandle=openLogFileHandle();
  if ($logFileHandle) {
    print($logFileHandle scalar(localtime(time()))." Info    : ",@_);
    closeLogFileHandle($logFileHandle);
  }
  if ($Debug) {
    print(STDERR scalar(localtime(time()))." Info    : ",@_);
  }
}

sub dispatcher()
{
  logDebug('no subroutine passed to Schedule::Cron. Existing now!'.nl);
  exit(1);
}

sub _trim($)
{
	my $string = shift;
	chomp $string;
	#$string =~ s/circuit-//g;
	$string =~ s/\]//g;
	$string =~ s/^\s+//;
	$string =~ s/\s+$//;
	$string =~ s/\t//g;
	$string =~ s/\000//g; # remove null characters
	return $string;
}

sub checkData($){
	my ($data) = @_;
	if (defined $data) {
	    return $data;
	} else {
	    return '';
	}
}

sub checkNum($){
	my ($data) = @_;
	if ($data =~ /\d/) {
	    return $data;
	} else {
	    return '1';
	}
} 

sub ConvertArrayToCleanString($){
	my (@Cdata) = @_;
	my $returnString = "";
	my $count = 0;
	for (@Cdata) {
		#logInfo($_);
		my $TempData = _trim($_);
		$TempData = checkData($TempData);
		#logInfo($TempData);
		if ($count > 0){
			$returnString = $returnString . "~" . $TempData ;
		}
		$count++;
	}
	return $returnString;
}

sub LoadCircuitProtectionData($) {
	my $stime = $_[0];
	my $RecordCount = 0;
	if ($stime) {
	  	open(SERVFILE, '<'.$LookupDir.$serviceFileName) or logWarn('Unable to  open '.$serviceFileName.nl);
		logInfo('Populate ServInfo table'.nl);
		while (<SERVFILE>) {
             chomp $_;
             my @DataSet1 = split(/\t/,$_);
	         $circuitProtection_HOH{$RecordCount}->{'SvcInstance'} = checkData($DataSet1[0]);
	         my $SvcInstance = checkData($DataSet1[0]);
	         $circuitProtection_HOH{$RecordCount}->{'ProvisionStatus'} = checkData($DataSet1[1]);
	         $circuitProtection_HOH{$RecordCount}->{'ProtectingCircuit'} = checkData($DataSet1[2]);
			 $circuitProtection_HOH{$RecordCount}->{'ProtectedCircuit'} = checkData($DataSet1[3]);
			 my $ProtectedCircuit = checkData($DataSet1[3]);
	         push @{ $circuitProtection_HOA{$ProtectedCircuit} }, $SvcInstance;
			 $circuitProtection_HOH{$RecordCount}->{'BusSvcName'} = checkData($DataSet1[4]);
			 $circuitProtection_HOH{$RecordCount}->{'SubSvcName'} = checkData($DataSet1[5]);
	         if (defined $DataSet1[6]){
	             $circuitProtection_HOH{$RecordCount}->{'Priority'} = $DataSet1[6];
	         }else{
	             $circuitProtection_HOH{$RecordCount}->{'Priority'} = 0;
	         }
	         $circuitProtection_HOH{$RecordCount}->{'SchemeRoute'} = checkData($DataSet1[7]);
	         $circuitProtection_HOH{$RecordCount}->{'RelevantCircuit'} = checkData($DataSet1[8]);
	         my $RelevantCircuit = checkData($DataSet1[8]);
	         push @{ $circuitProtection_HOA{$ProtectedCircuit} }, $RelevantCircuit;
	         $circuitProtection_HOH{$RecordCount}->{'E2ECircuit'} = checkData($DataSet1[9]);
	         my $E2ECircuit = checkData($DataSet1[9]);
	         push @{ $circuitProtection_HOA{$ProtectedCircuit} }, $E2ECircuit;
	         $RecordCount++;
        }
        close(SERVFILE);
	}
}

sub LoadCircuits_tmp($$$$) {
	my ($count,$FMSAlertKey,$CircuitID,$ServerName_ServerSerial) = @_;
    my $Hcount = scalar(keys %circuits_tmp_HOH);
	if (%circuits_tmp_HOH) {} else { $Hcount = 0;}
    $circuits_tmp_HOH{$Hcount}->{'count'} = $count;
    $circuits_tmp_HOH{$Hcount}->{'FMSAlertKey'} = checkData($FMSAlertKey);
    $circuits_tmp_HOH{$Hcount}->{'CircuitID'} = checkData($CircuitID);
    $circuits_tmp_HOH{$Hcount}->{'RawAlarmID'} = checkData($ServerName_ServerSerial);
}

sub LoadCircuits_tmp_sec_HOH($$$$) {
	my ($count,$FMSAlertKey,$CircuitID,$ServerName_ServerSerial) = @_;
	my $Hcount = scalar(keys %circuits_tmp_sec_HOH);
    if (%circuits_tmp_sec_HOH) {} else { $Hcount = 0;}
	$circuits_tmp_sec_HOH{$Hcount}->{'count'} = $count;
    $circuits_tmp_sec_HOH{$Hcount}->{'FMSAlertKey'} = $FMSAlertKey;
    $circuits_tmp_sec_HOH{$Hcount}->{'CircuitID'} = $CircuitID;
    $circuits_tmp_sec_HOH{$Hcount}->{'ServerName_ServerSerial'} = $ServerName_ServerSerial;
}

sub LoadCircuits_tmpFromSec(){
	foreach my $hash_keyA(keys %circuits_tmp_sec_HOH) {
		my $S_count = $circuits_tmp_sec_HOH{$hash_keyA}->{'count'};
		my $S_FMSAlertKey = $circuits_tmp_sec_HOH{$hash_keyA}->{'FMSAlertKey'};
		my $S_CircuitID = $circuits_tmp_sec_HOH{$hash_keyA}->{'$CircuitID'};
		my $C_ServerName_ServerSerial = $circuits_tmp_sec_HOH{$hash_keyA}->{'ServerName_ServerSerial'};
		LoadCircuits_tmp($S_count,$S_FMSAlertKey,$S_CircuitID,$C_ServerName_ServerSerial);
	}
}

sub CountCirlInfoData($) {
    my $RecordCount = $_;
    my $eltCount = 0;
    foreach my $k (keys %cirlInfo_CID) {
       foreach (@{$cirlInfo_CID{$k}}) {
          $eltCount++;
       }
    }
    logInfo('there are '.$eltCount.' elements in the CircuitID Hash of Arrays '.nl);
    my $eltCount2 = 0;
    foreach my $k (keys %cirlInfo_AK) {
       foreach (@{$cirlInfo_AK{$k}}) {
          $eltCount2++;
       }
    }
    logInfo('there are '.$eltCount2.' elements in the FMSAlertKey Hash of Arrays '.nl);
    if (($eltCount == $eltCount2) && ($eltCount == $RecordCount)) {
       logInfo('Both element counts match the record count, load was complete.'.nl);
    }
}

sub LoadCirlInfoData($) {
	my $ctime = $_[0];
	my $RecordCount = 0;
	if ($ctime) {
	  	open(CIRFILE, '<'.$LookupDir.$circuitFileName
					) or logWarn('Unable to  open '.$circuitFileName.nl);
		logInfo('Populate Ciruit Information table'.nl);
		while (<CIRFILE>) {
			my @DataSet1 = split/\t/,$_;
			my $FMSAlertKey = $DataSet1[0];
			my $CircuitID = $DataSet1[1];
			chomp $CircuitID;
			push @{ $cirlInfo_AK{$FMSAlertKey} }, $CircuitID;
			push @{ $cirlInfo_CID{$CircuitID} }, $FMSAlertKey;
			$RecordCount++;
		}
		close(CIRFILE);
#        my $max_AK = scalar(keys %cirlInfo_AK);
#        my $max_CID = scalar(keys %cirlInfo_CID);
#        logInfo('there are '.$max_AK.' unique AlertKeys '.nl);
#        logInfo('there are '.$max_CID.' unique CircuitIDs '.nl);
#        logInfo('the file contains '.$RecordCount.' lines '.nl);
        CountCirlInfoData($RecordCount);
	} 
}

sub LoadSchemeServiceData($) {
	my $sstime = $_[0];
	my $RecordCount = 0;
	if ($sstime) {
	  	open(SSFILE, '<'.$LookupDir.$schemeInfoFileName
	  				) or logWarn('Unable to  open '.$schemeInfoFileName.nl);
		logInfo('Populate Scheme Service table'.nl);
		while (<SSFILE>) {
			my @DataSet1 = split(/\t/,$_);
			$schemeInfo_HOH{$RecordCount}->{'SvcInstance'} = $DataSet1[0];
			$schemeInfo_HOH{$RecordCount}->{'ProtectingScheme'} = $DataSet1[1];
			$schemeInfo_HOH{$RecordCount}->{'ProtectedScheme'} = $DataSet1[2];
			$schemeInfo_HOH{$RecordCount}->{'ProvisionStatus'} = $DataSet1[3];
			$RecordCount++;
		}	
		close(SSFILE);
	} 
}

sub LoadSchemeGroupData($) {
	my $sgtime = $_[0];
	my $RecordCount = 0;
	if ($sgtime) {
	  	open(SGFILE, '<'.$LookupDir.$schemeGroupFileName
	  				) or logWarn('Unable to  open '.$schemeGroupFileName.nl);
		logInfo('Populate Scheme Route table'.nl);
		while (<SGFILE>) {
			my @DataSet1 = split(/\t/,$_);
			$schemeGroup_HOH{$RecordCount}->{'SvcInstance'} = $DataSet1[0];
			$schemeGroup_HOH{$RecordCount}->{'ProtectingScheme'} = $DataSet1[1];
			$schemeGroup_HOH{$RecordCount}->{'ProtectedScheme'} = $DataSet1[2];
			$schemeGroup_HOH{$RecordCount}->{'BusSvcName'} = $DataSet1[3];
			$schemeGroup_HOH{$RecordCount}->{'SubSvcName'} = $DataSet1[4];
			$schemeGroup_HOH{$RecordCount}->{'ServicePriority'} = $DataSet1[5];
			$schemeGroup_HOH{$RecordCount}->{'ProvisionStatus'} = $DataSet1[6];
			$RecordCount++;
		}	
		close(SGFILE);
	} 
}

sub LoadSchemeRouteData($) {
	my $srtime = $_[0];
	my $RecordCount = 0;
	if ($srtime) {
		open(SRFILE, '<'.$LookupDir.$schemeRouteFileName
	  				) or logWarn('Unable to  open '.$schemeRouteFileName.nl);
		logInfo('Populate Scheme Route table'.nl);
		while (<SRFILE>) {
			my @DataSet1 = split(/\t/,$_);
			$schemeRoute_HOH{$RecordCount}->{'SvcInstance'} = $DataSet1[0];
			$schemeRoute_HOH{$RecordCount}->{'ProtectingSchemeRoute'} = $DataSet1[1];
			$schemeRoute_HOH{$RecordCount}->{'ProtectedSchemeRoute'} = $DataSet1[2];
			$schemeRoute_HOH{$RecordCount}->{'SIARule'} = 'B';
			$schemeRoute_HOH{$RecordCount}->{'ProvisionStatus'} = $DataSet1[3];
			$RecordCount++;
		}	
		close(SRFILE);
	} 
}

sub writeTimeStamp()
{
  open( FILE, '>'.$LookupTimeStampFile ) or logDie('Unable to open '.$LookupTimeStampFile.'. ',$!.nl);
  logInfo("Write time stamp into the lookup time stamp file".nl);
  while ( my ($fn,$ts) = each %filesAndTimestamp) {
      print FILE $fn.','.$ts.nl if ($fn&&$ts);
  }
  close(FILE);
}

sub getTimeStamp()
{
  my ($file) = @_;
  open( FILE, '<'.$LookupTimeStampFile ) or logDie('Unable to open '.$LookupTimeStampFile.'. ',$!.nl);
  while(<FILE>){
  	my ($filename,$timestamp) = split(/,/);
 	$filesAndTimestamp{$filename} = int($timestamp);
  }
  close(FILE);
}

sub checkForNewFiles($)
{
  my ($filename) = @_;
  if ($LookupDir) {
    my ($dev,$ino,$mode,$nlink,$uid,$gid,$rdev,$size,$atime,$mtime,$ctime,$blksize,$blocks)=stat($LookupDir.$filename);
    logInfo('The last modified time stamp for '.$filename.' file is : '.$mtime.nl) if $mtime;
    if(exists $filesAndTimestamp{$filename}&&$mtime){
  	return 0 if($mtime eq $filesAndTimestamp{$filename});
    } elsif(!$mtime)  {
		logWarn('Unable to find '.$filename.nl);
	}
    return $mtime;
  }else{
  	logWarn('The directory $LookupDir does not exist'.nl);
  	return 0;
  }
}

sub dbInsertSyntheticAlarm($$) {
	my ($dbHandle,$statement)=@_;
	my $rst=0;
	if ($dbHandle) {
	   $rst=$dbHandle->do($statement) or logWarn($dbHandle.', Failed to insert a record '.$!.$statement.nl);
	}
  	return $rst;
}

sub InsertSyntheticAlarms($) {
	my ($dbHandle)=@_;
	foreach my $Hash_key(keys %Synthetic_alarm_storage_HOH) {
		my $SA_SvcInstance = $Synthetic_alarm_storage_HOH{$Hash_key}->{'SvcInstance'};
		my $SA_ServiceStatus = $Synthetic_alarm_storage_HOH{$Hash_key}->{'ServiceStatus'};
		my $SA_FMSAlertKey = $Synthetic_alarm_storage_HOH{$Hash_key}->{'FMSAlertKey'};
		my $SA_ProvisionStatus = $Synthetic_alarm_storage_HOH{$Hash_key}->{'ProvisionStatus'};
		my $SA_ProtectedCircuit = $Synthetic_alarm_storage_HOH{$Hash_key}->{'ProtectedCircuit'};
		my $SA_ProtectingCircuit = $Synthetic_alarm_storage_HOH{$Hash_key}->{'ProtectingCircuit'};
		my $SA_BusPriority = checkNum($Synthetic_alarm_storage_HOH{$Hash_key}->{'BusPriority'});
		my $SA_BusSvcName = $Synthetic_alarm_storage_HOH{$Hash_key}->{'BusSvcName'};
		my $SA_SubSvcName = $Synthetic_alarm_storage_HOH{$Hash_key}->{'SubSvcName'};
		my $SA_RawAlarmID = $Synthetic_alarm_storage_HOH{$Hash_key}->{'RawAlarmID'};
		my $SA_Number = $Synthetic_alarm_storage_HOH{$Hash_key}->{'Number'};
		my $Summary = $Synthetic_alarm_storage_HOH{$Hash_key}->{'Summary'};
		
		# determine it's SuppressEscl flag based on ProvisionStatus info of synth SIA alarm
		my $vSuppressEscl = 0;
		if (($SA_ProvisionStatus eq 'Live') || ($SA_ProvisionStatus eq 'In Service') ||
		($SA_ProvisionStatus eq '') ) {
			$vSuppressEscl = 0;
		} else {
			$vSuppressEscl = 6;
		}
		
		my $timeMarker = time();
		if (!defined $Summary) { 
		   $Summary = "$SA_SvcInstance $SA_ServiceStatus ";
		}
		my $Identifier = "$SA_SvcInstance $SA_ServiceStatus $vSuppressEscl";
		my $AlarmDetails = "$SA_FMSAlertKey caused this synthetic SIA alarm $SA_SvcInstance";
		
		my $statement = "insert into alerts.status ".
		"(Summary,Identifier,Manager,AlertGroup,Severity,OriginalSeverity,FirstOccurrence,LastOccurrence,StateChange,".
		"Type,Tally,FMSAlertKey,SvcInstance,BusPriority,AlarmDetails,ImpactedStatus,ServiceID,SubService,ProtectingCircuit,".
		"ProtectedCircuit,RawAlarmID,ParentPointer,SuppressEscl,CommissionedState)".
		" values ".
		"('$Summary','$Identifier','Service Impact Alarm','Service Impact Alarm Group',$SA_Number,".
		"$SA_Number,$timeMarker,$timeMarker,$timeMarker,1,1,'$SA_FMSAlertKey','$SA_SvcInstance',$SA_BusPriority,".
		"'$AlarmDetails','$SA_ServiceStatus','$SA_BusSvcName','$SA_SubSvcName','$SA_ProtectingCircuit',".
		"'$SA_ProtectedCircuit','$SA_RawAlarmID','$SA_RawAlarmID',$vSuppressEscl,'$SA_ProvisionStatus')";
		dbInsertSyntheticAlarm($dbHandle,$statement);
	}
	logInfo('Completed inserting Synthetic alarm records into netcool'.nl);
}

sub SIA_Impact()
{
	logInfo('##### Running SIA'.nl);
	logInfo('Loading base data.'.nl);
	my $stime = 1;
	my $ctime = 1;
	my $sstime = 1;
	my $srtime = 1;
	my $sgtime = 1;

	getTimeStamp();
	#$stime=checkForNewFiles($serviceFileName);
	#$ctime=checkForNewFiles($circuitFileName);
	#$sstime=checkForNewFiles($schemeInfoFileName);
	#$srtime=checkForNewFiles($schemeRouteFileName);
	#$sgtime=checkForNewFiles($schemeGroupFileName);

    my $TMarkerT = "Loading Cramer Data ";
    printTimeMarker($TMarkerT);

	if($stime || $ctime || $sstime || $srtime || $sgtime){
		logInfo('Loading Cramer Data into HOH Tables'.nl);
		if($stime){
			LoadCircuitProtectionData($stime);
		}
		if($ctime){
			LoadCirlInfoData($ctime);
		}
		if($sstime){
			LoadSchemeServiceData($sstime);
		}
		if($srtime){
			LoadSchemeRouteData($srtime);
		}
		if($sgtime){
			LoadSchemeGroupData($srtime);
		}
	}
	writeTimeStamp();
    $TMarkerT = "Loaded Cramer Data ";
    printTimeMarker($TMarkerT);
    load_analysis();
    if (!$dbHandle) {
        $TMarkerT = "Opening Database connection ";
        printTimeMarker($TMarkerT);
        $dbHandle = initDatabase(transpowerServer,transpowerHost,transpowerPort);
    }

    my $dbHealth = dbTest($dbHandle);
    
    if ($dbHealth) {
       logInfo('DB health is OK'.nl);
       $TMarkerT = "database open ";
       printTimeMarker($TMarkerT);
       #test
       #runInsertTest($dbHandle,50);
	   ResetRawEquipmentAlarm_newCycle($dbHandle);
	   load_analysis();
	   dbSelect($dbHandle,PrimaryQuery);
	   #Check_alerts_status_dataset();
	   load_analysis();
	   Synthetic_si_alarm_Trigger();
	   load_analysis();
	   SIA_process_svcs($dbHandle);
	   load_analysis();
	   SIA_process_TP_svcs1($dbHandle);
	   load_analysis();
	   ResetSyntheticSIAalarm($dbHandle);
	   load_analysis();
	   InsertSyntheticAlarms($dbHandle);
       load_analysis();
    } else {
       logWarn('DB Handle not valid'.nl);
       logInfo('reset Database connection'.nl);
       closeDatabase($dbHandle);
       $dbHandle = initDatabase(transpowerServer,transpowerHost,transpowerPort);
    }
    load_analysis();
        
    $TMarkerT = "Creating temp store of effecting circuits ";
    printTimeMarker($TMarkerT);
    $TMarkerT = "Created temp store of effecting circuits ";
    printTimeMarker($TMarkerT);
	logInfo('##### Finished running SIA '.nl);
	emptyDataStores();
}

sub UpdateAlerts_status_SuppressEscl($$$$){
	my ($dbHandle,$S_SuppressEscl_value,$S_RawAlarmID,$S_SuppressEscl) = @_;
	my $statement = "update alerts.status set ".
	"SuppressEscl = $S_SuppressEscl_value where ServerName_ServerSerial = '$S_RawAlarmID' ".
	"and SuppressEscl = $S_SuppressEscl ";
	dbUpdate($dbHandle,$statement);
}

sub UpdateAlerts_status_Summary($$$$){
	my ($dbHandle,$S_Summary,$S_SvcInstance,$S_RawAlarmID) = @_;
	my $statement = "update alerts.status set ".
	"Summary = '$S_Summary' where SvcInstance = '$S_SvcInstance' and ParentPointer = '$S_RawAlarmID' ";
	dbUpdate($dbHandle,$statement);
}

sub UpdateSynthetic_alarm_storage_HOH($$$$$$$$$$$$) {
	my ($SA_SvcInstance,$SA_ServiceStatus,$SA_FMSAlertKey,$SA_ProvisionStatus,$SA_ProtectedCircuit,$SA_ProtectingCircuit,$SA_BusPriority,$SA_BusSvcName,$SA_SubSvcName,$SA_RawAlarmID,$SA_Number,$SA_Summary) = @_;
	my $Hcount = scalar(keys %Synthetic_alarm_storage_HOH);
	if (%Synthetic_alarm_storage_HOH) {} else { $Hcount = 0;}
    #load data into HOH
	$Synthetic_alarm_storage_HOH{$Hcount}->{'SvcInstance'} = $SA_SvcInstance;
	$Synthetic_alarm_storage_HOH{$Hcount}->{'ServiceStatus'} = $SA_ServiceStatus;
	$Synthetic_alarm_storage_HOH{$Hcount}->{'FMSAlertKey'} = $SA_FMSAlertKey;
	$Synthetic_alarm_storage_HOH{$Hcount}->{'ProvisionStatus'} = $SA_ProvisionStatus;
	$Synthetic_alarm_storage_HOH{$Hcount}->{'ProtectedCircuit'} = $SA_ProtectedCircuit;
	$Synthetic_alarm_storage_HOH{$Hcount}->{'ProtectingCircuit'} = $SA_ProtectingCircuit;
	$Synthetic_alarm_storage_HOH{$Hcount}->{'BusPriority'} = $SA_BusPriority;
	$Synthetic_alarm_storage_HOH{$Hcount}->{'BusSvcName'} = $SA_BusSvcName;
	$Synthetic_alarm_storage_HOH{$Hcount}->{'SubSvcName'} = $SA_SubSvcName;
	$Synthetic_alarm_storage_HOH{$Hcount}->{'RawAlarmID'} = $SA_RawAlarmID;
	$Synthetic_alarm_storage_HOH{$Hcount}->{'Number'} = $SA_Number;
	$Synthetic_alarm_storage_HOH{$Hcount}->{'Summary'} = $SA_Summary;
}

sub UpdateAlerts_status_ServiceLosscounter($$$) {
	my ($dbHandle,$ServicesImpacted_value,$RawAlarmID) = @_;
	#$ServicesImpacted_value++;
	
	my $statement = "update alerts.status set ".
	"ServicesImpacted=$ServicesImpacted_value where ServerName_ServerSerial = '$RawAlarmID'";
	dbUpdate($dbHandle,$statement);
}

sub UpdateAlerts_status($$$$$$$$$){
	my ($dbHandle,$protectingCircuit,$protectedCircuit,$SvcInstance,$BusPriority,$BusSvcName,$SubSvcName,$RawAlarmID,$ImpactedStatus) = @_;
	my $statement = "update alerts.status set ".
	"ServiceImpactingFlag = 2 , ImpactedStatus = '$ImpactedStatus', ProtectingCircuit = '$protectingCircuit',".
	" ProtectedCircuit = '$protectedCircuit', SvcInstance = '$SvcInstance', BusPriority = $BusPriority,".
	" ServiceID = '$BusSvcName', SubService = '$SubSvcName' where ServerName_ServerSerial = '$RawAlarmID'";
	dbUpdate($dbHandle,$statement);
}

sub UpdateAlerts_status_tmp($$$$$$$$$) {
	my ($ProtectingCircuit,$ProtectedCircuit,$SvcInstance,$BusPriority,$ServiceID,
	$SubService,$RawAlarmID,$ImpactedStatus) = @_;
	foreach my $hash_keyA(keys %alerts_status_tmp) {
		my $AS_ServerName_ServerSerial = $alerts_status_tmp{$hash_keyA}->{'ServerName_ServerSerial'};
		if ($AS_ServerName_ServerSerial eq $RawAlarmID ) {
			$alerts_status_tmp{$hash_keyA}->{'ServiceImpactingFlag'} = 2;
			$alerts_status_tmp{$hash_keyA}->{'ImpactedStatus'} = $ImpactedStatus;
			$alerts_status_tmp{$hash_keyA}->{'ProtectingCircuit'} = $ProtectingCircuit; 
			$alerts_status_tmp{$hash_keyA}->{'ProtectedCircuit'} = $ProtectedCircuit; 
			$alerts_status_tmp{$hash_keyA}->{'SvcInstance'}= $SvcInstance;
			$alerts_status_tmp{$hash_keyA}->{'BusPriority'} = $BusPriority;
		 	$alerts_status_tmp{$hash_keyA}->{'ServiceID'} = $ServiceID; # issue variable called does not exists in originator.
			$alerts_status_tmp{$hash_keyA}->{'SubService'} = $SubService; 			
		}
	}
}

sub runInsertTest($$) {
	my ($dbHandle,$Wcountmax)=@_;
	my $rst=0;
	my $Wcount = 0;
	my $TMarkerT = "Started Writing records to alert.status ";
	        printTimeMarker($TMarkerT);
	        while ($Wcount<=$Wcountmax) {
	        	my $testIdentifier = "HenriTest".$Wcount."Test2" ;
	        	my $WriteTestStatement = "insert into alerts.status 
	       	    (Summary,
					Identifier,
					Manager, 
					AlertGroup, 
					Severity, 
					OriginalSeverity, 
					FirstOccurrence, 
					LastOccurrence,
					StateChange, 
					Type,
					Tally,
					FMSAlertKey, 
					SvcInstance,
					BusPriority,
					AlarmDetails,
					ImpactedStatus,
					ServiceID,
					SubService,
					ProtectingCircuit,
					ProtectedCircuit,
					RawAlarmID,
					ParentPointer,
					SuppressEscl,
					CommissionedState) 
					
					values 
			 		
			 		('Test_For_henri',
					'$testIdentifier',
					'Service Impact Alarm',
					'Service Impact Alarm Group',
					1,
					1,
					1313112946,
					1313112946,
					1313112946, 
					1,
					1,
					'pFMSAlertKey',
					'pSvcInstance',
					1,
					'pFMSAlertKey',
					'pImpactedStatus',
					'pBusSvcName',
					'pSubSvcName',
					'pProtectingCircuit',
					'pProtectedCircuit',
					'pRawAlarmID',
					'pRawAlarmID',
					1,
					'pProvisionStatus')";
	        	    $dbHandle->do($WriteTestStatement) or logWarn($dbHandle.', Failed to insert a record'.$!.$WriteTestStatement.nl);
	                $Wcount++;
	        }
	        $TMarkerT = "Completed writing $Wcountmax records to alert.status ";
			printTimeMarker($TMarkerT);
	        
	        $Wcount = 0;
	        $TMarkerT = "Started Updating records to alert.status ";
	        printTimeMarker($TMarkerT);
	        while ($Wcount<=$Wcountmax) {
	        	my $testIdentifier = "HenriTest".$Wcount."Test2" ;
	        	my $WriteTestStatement = "update alerts.status set 
	       	    Severity = 2 where  Identifier = '$testIdentifier' " ;
	        	    dbUpdate($dbHandle,$WriteTestStatement);
	                $Wcount++;
	        }
	        $TMarkerT = "Completed Updating $Wcount records to alert.status ";
	        printTimeMarker($TMarkerT);
}

sub log_method($$)
{
  my ($level,$msg)=@_;
  my $DBG_MAP={0=>'INFO',1=>'WARN',2=>'ERROR'};
  print($DBG_MAP->{$level}.$msg.nl);
}

sub load_analysis() {
	my $PData = `ps -efo fname,vsz,pcpu,pset | grep SIA`;
        chomp $PData;
	logInfo('process details: '.$PData.nl);
}

sub followRelevantCircuit {
   my ($RelevantCircuit,$E2ECircuit,$SvcName,$ProtectingCrt2) = @_;
   my $count = 0;
   my $SvcInstance = undef;
   my $E2ECircuit1 = undef;
   my $RelevantCircuit1 = undef;
   $recursion++;
   
#   logInfo('entering followRelevantCircuit - recursion level: '.$recursion.nl);
   if ($recursion > 10) {
     logInfo('isInHierarchy recursion level exceeded limit, breaking loop'.nl);
     return (0);
   }
   do {
      $SvcInstance = @{$circuitProtection_HOA{$RelevantCircuit}}[$count];
      $E2ECircuit1 = @{$circuitProtection_HOA{$RelevantCircuit}}[$count+2];
#logInfo('InRelevantCircuit:$recursion rel: $RelevantCircuit, svc: $SvcInstance, e2e: $E2ECircuit1'.nl);
      if (($SvcInstance eq $SvcName) && ($E2ECircuit1 eq $E2ECircuit)) {
          $RelevantCircuit1 = @{$circuitProtection_HOA{$RelevantCircuit}}[$count+1];
          if ( ($RelevantCircuit1 eq '') || ($RelevantCircuit1 eq $RelevantCircuit) ) {
#            logInfo('rel empty'.nl);
#            logInfo('exiting followRelevantCircuit -FALSE- '.$recursion.nl);
            return (0);
          }
# Step 2/3 - try to match input 2 to relevant overlying circuit
          if ($RelevantCircuit1 eq $ProtectingCrt2) {
#            logInfo('match found'.nl);
#            logInfo('exiting followRelevantCircuit -TRUE- '.$recursion.nl);
            return (1);
          }
# Step 4 - match protected circuit to relevant overlying circuit and service name
          followRelevantCircuit($RelevantCircuit1,$E2ECircuit1,$SvcName,$ProtectingCrt2);
       }
       $count += 3; # the increment MUST be equal to the number of items pushed into
                    # $circuitProtection_HOA in sub LoadCircuitProtectionData
# Step 5 - repeat until we run out of relevant overlying circuits
   } until !defined @{$circuitProtection_HOA{$RelevantCircuit}}[$count];
#   logInfo('exiting followRelevantCircuit -FALSE- '.$recursion.nl);
}

sub isInHierarchy($$$) {
   my ($ProtectingCrt1,$ProtectingCrt2,$SvcName) = @_;
   
# Step 0 - check for direct match of the 2 inputs, otherwise go to next steps
   if (($ProtectingCrt1 eq $ProtectingCrt2) ||
        matchProtectingCircuits($ProtectingCrt1,$ProtectingCrt2,$SvcName) ||
        matchProtectingCircuits($ProtectingCrt2,$ProtectingCrt1,$SvcName)) { # Step 6 - switch inputs
#     logInfo('Found a match'.nl);
     return (1);
   } else {
#     logInfo('Found NO match'.nl);
     return (0);
   }
}

sub matchProtectingCircuits($$$) {
#This function returns a true or false depending on matching the input strings
# and the data in the circuit protection file.
#Step 1)Find the entry in the circuitprotection file that has input 1 as the protected circuit
#       and the same servicename in the svcinstance column
#Step 2/3) Try to match input 2 to relevant overlying circuit and e2ecircuit
#Step 4) Using the relevant overlying circuit value, search the circuitProtection file for a row
#  which has the values as:
#        Protected circuit of this row = relevant overlying circuit of the original row
#        E2ecircuit of this row = e2e circuit of original row
#        svcinstance of this row  = svcinstance of original row
#Step 5) Repeat until we run out of relevant overlying circuits or svcinstances
#Step 6) Switch input1 and input 2, then repeat the entire function
   my ($ProtectingCrt1,$ProtectingCrt2,$SvcName) = @_;
   my $SvcInstance = undef;
   my $RelevantCircuit = undef;
   my $E2ECircuit = undef;
   my $count = 0;
   
# Step 1 - match protected circuit to protecting circuit and service name
   do {
      $recursion = 0;
      $SvcInstance = @{$circuitProtection_HOA{$ProtectingCrt1}}[$count];
#      logInfo('$count - svc: $SvcInstance'.nl);
      if ($SvcInstance eq $SvcName) {
         $E2ECircuit = @{$circuitProtection_HOA{$ProtectingCrt1}}[$count+2];
         $RelevantCircuit = @{$circuitProtection_HOA{$ProtectingCrt1}}[$count+1];
#         logInfo('$count - svc: $SvcInstance, e2e: $E2ECircuit, rel: $RelevantCircuit'.nl);
         if (!defined $RelevantCircuit) {
#           logInfo('rel undefined'.nl);
           return (0);
         }
# Step 2/3 - try to match input 2 to relevant overlying circuit and e2ecircuit
         if (($E2ECircuit eq $ProtectingCrt2) || ($RelevantCircuit eq $ProtectingCrt2)) {
#           logInfo('match found'.nl);
           return (1);
         }
# Step 4 - iterate with relevant overlying circuit as protected circuit
         followRelevantCircuit($RelevantCircuit,$E2ECircuit,$SvcName,$ProtectingCrt2);
      }
      $count += 3;
# Step 5 - Repeat until we run out of svcinstances
   } until !defined @{$circuitProtection_HOA{$ProtectingCrt1}}[$count];
#   logInfo('NO match found in part'.nl);
   return (0);
}

sub HierarchySafe($$$$) {
   my ($SI_ProtectedCircuit,$ST_ProtectedCircuit,$SvcInstance,$Hash)=@_;
   
   if ($Hash eq 'service_tmp') {
     foreach my $hash_keyC(keys %service_tmp_HOH) {
       my $ST2_ProtectedCircuit = $service_tmp_HOH{$hash_keyC}->{'ProtectedCircuit'};
       if (isInHierarchy($ST_ProtectedCircuit,$ST2_ProtectedCircuit,$SvcInstance)) {
         if (!isInHierarchy($SI_ProtectedCircuit,$ST2_ProtectedCircuit,$SvcInstance)) {
           return (0);
         }
       }
     }
   }
   if ($Hash eq 'scheme_tmp') {
     foreach my $hash_keyC(keys %scheme_tmp_HOH) {
       my $ST2_ProtectedCircuit = $scheme_tmp_HOH{$hash_keyC}->{'ProtectedCircuit'};
       if (isInHierarchy($ST_ProtectedCircuit,$ST2_ProtectedCircuit,$SvcInstance)) {
         if (!isInHierarchy($SI_ProtectedCircuit,$ST2_ProtectedCircuit,$SvcInstance)) {
           return (0);
         }
       }
     }
   }
   logInfo('exiting HierarchySafe - TRUE'.nl);
   return (1);
}

sub buildLastAlarmIDHash {
# This traverses the svc_inst_tmp and service_tmp HOH arrays and finds the raw alarm id for
# each svcInstance which has the highest last occurrence time. The last occurrence time
# is in the alerts_status_tmp array.
   my %raw_alarm_ids = ();
   
   logInfo('-- Starting buildLastAlarmIDHash'.nl);
# build array of all RawAlarmIDs
   foreach my $hash_keyA(keys %service_tmp_HOH) {
      my $ST_SvcInstance = $service_tmp_HOH{$hash_keyA}->{'SvcInstance'};
      my $ST_RawAlarmID = $service_tmp_HOH{$hash_keyA}->{'RawAlarmID'};
      push @{ $raw_alarm_ids{$ST_SvcInstance} }, $ST_RawAlarmID;
   }
   foreach my $hash_keyA(keys %svc_inst_tmp_HOH) {
      my $SI_SvcInstance = $svc_inst_tmp_HOH{$hash_keyA}->{'SvcInstance'};
      my $SI_RawAlarmID = $svc_inst_tmp_HOH{$hash_keyA}->{'RawAlarmID'};
      push @{ $raw_alarm_ids{$SI_SvcInstance} }, $SI_RawAlarmID;
   }
   foreach my $hash_keyA(keys %scheme_tmp_HOH) {
      my $ST_SRInstance = $scheme_tmp_HOH{$hash_keyA}->{'SRInstance'};
      my $ST_RawAlarmID = $scheme_tmp_HOH{$hash_keyA}->{'RawAlarmID'};
      push @{ $raw_alarm_ids{$ST_SRInstance} }, $ST_RawAlarmID;
   }
   foreach my $hash_keyA(keys %sr_down_tmp_HOH) {
      my $SRD_SRInstance = $sr_down_tmp_HOH{$hash_keyA}->{'SRInstance'};
      my $SRD_RawAlarmID = $sr_down_tmp_HOH{$hash_keyA}->{'RawAlarmID'};
      push @{ $raw_alarm_ids{$SRD_SRInstance} }, $SRD_RawAlarmID;
   }

# loop through the array we built above and find last occurrence in alerts_status   
   foreach my $SvcInstance (keys %raw_alarm_ids) {
      my $lastOccurrence = 0;
      foreach my $Svc_RawAlarmID (@{$raw_alarm_ids{$SvcInstance}}) {
        foreach my $hash_keyB(keys %alerts_status_tmp) {
	      my $AS_ServerName_ServerSerial = $alerts_status_tmp{$hash_keyB}->{'ServerName_ServerSerial'};
	      if ($Svc_RawAlarmID eq $AS_ServerName_ServerSerial) {
	        my $AS_LastOccurrence = $alerts_status_tmp{$hash_keyB}->{'LastOccurrence'};
	        if ($AS_LastOccurrence gt $lastOccurrence) {
	          my $AS_FMSAlertKey = $alerts_status_tmp{$hash_keyB}->{'FMSAlertKey'};
	          $last_alarm_id{$SvcInstance}->{'RawAlarmID'} = $Svc_RawAlarmID;
	          $last_alarm_id{$SvcInstance}->{'FMSAlertKey'} = $AS_FMSAlertKey;
	          $lastOccurrence = $AS_LastOccurrence;
	        }
	      }
        }
      }
   }
}

sub ResetRawEquipmentAlarm_newCycle($){
	my ($dbHandle)=@_;
	logInfo('resetting alerts.status for run'.nl);
	# Reset raw equipment alarm marked for SIA for a new recalculation cycle
	my $ResetRawAlarmStatement = "update alerts.status set ServiceImpactingFlag=1, ServicesImpacted=0, ImpactedStatus='',
	 SvcInstance='', ProtectedCircuit='', ProtectingCircuit='', BusPriority=0, ServiceID='', SubService='' 
	 where ServiceImpactingFlag<>0 and Severity>0";
	dbUpdate($dbHandle,$ResetRawAlarmStatement);
}

sub ResetSyntheticSIAalarm($) {
	my ($dbHandle)=@_;
	logInfo('resetting synthetic alarms'.nl);
    my $ResetsyntheticAlarmStatement = "update alerts.status set Severity=0 where Manager='Service Impact Alarm' and Severity>0";
    dbUpdate($dbHandle,$ResetsyntheticAlarmStatement);
}

sub Load_scheme_tmp($$$$$$$$$$$$$$$$$$$$$$) {
	my ($count,$FMSAlertKey,$RawAlarmID,$ProtectingCircuit,$ProtectedCircuit,$protected,$SvcInstance,$F8,
	$F9,$ProvisionStatus,$F11,$F12,$F13,$F14,$F15,$F16,$F17,$F18,$F19,$F20,$F21,$F22) = @_;
    my $Hcount = scalar(keys %scheme_tmp_HOH);
    if (%scheme_tmp_HOH) {} else { $Hcount = 0;}
    $scheme_tmp_HOH{$Hcount}->{'count'} = $count;
    $scheme_tmp_HOH{$Hcount}->{'FMSAlertKey'} = $FMSAlertKey;
    $scheme_tmp_HOH{$Hcount}->{'RawAlarmID'} = $RawAlarmID;
    $scheme_tmp_HOH{$Hcount}->{'ProtectingCircuit'} = $ProtectingCircuit;
    $scheme_tmp_HOH{$Hcount}->{'ProtectedCircuit'} = $ProtectedCircuit;
    $scheme_tmp_HOH{$Hcount}->{'IsCirProtected'} = $protected;
	$scheme_tmp_HOH{$Hcount}->{'SRInstance'} = $SvcInstance;
    $scheme_tmp_HOH{$Hcount}->{'SSInstance'} = $F8;
    $scheme_tmp_HOH{$Hcount}->{'SvcInstance'} = $F9;
    $scheme_tmp_HOH{$Hcount}->{'SRProvisionStatus'} = $ProvisionStatus;
    $scheme_tmp_HOH{$Hcount}->{'SSProvisionStatus'} = $F11;
    $scheme_tmp_HOH{$Hcount}->{'SvcProvisionStatus'} = $F12;
    $scheme_tmp_HOH{$Hcount}->{'SS_Status'} = $F13;
    $scheme_tmp_HOH{$Hcount}->{'Svc_Status'} = $F14;
    $scheme_tmp_HOH{$Hcount}->{'Svc_ServiceID'} = $F15;
    $scheme_tmp_HOH{$Hcount}->{'Svc_SubSvcName'} = $F16;
    $scheme_tmp_HOH{$Hcount}->{'Svc_BusPriority'} = $F17;
    $scheme_tmp_HOH{$Hcount}->{'SGInstance'} = $F18;
    $scheme_tmp_HOH{$Hcount}->{'SGProvisionStatus'} = $F19;
    $scheme_tmp_HOH{$Hcount}->{'SG_Status'} = $F20;
    $scheme_tmp_HOH{$Hcount}->{'Summary'} = $F21;
    $scheme_tmp_HOH{$Hcount}->{'SR_Status'} = $F22;
}

sub Load_service_tmp($$$$$$$$$$) {
	my ($count,$FMSAlertKey,$SvcInstance,$ProvisionStatus,$ProtectedCircuit,$ProtectingCircuit,$BusSvcName,
	$SubSvcName,$ServicePriority,$RawAlarmID) = @_;
    my $Hcount = scalar(keys %service_tmp_HOH);
	if (%service_tmp_HOH) {} else { $Hcount = 0;}
    $service_tmp_HOH{$Hcount}->{'count'} = $count;
    $service_tmp_HOH{$Hcount}->{'FMSAlertKey'} = $FMSAlertKey;
    $service_tmp_HOH{$Hcount}->{'SvcInstance'} = $SvcInstance;
    $service_tmp_HOH{$Hcount}->{'ProvisionStatus'} = $ProvisionStatus;
    $service_tmp_HOH{$Hcount}->{'ProtectedCircuit'} = $ProtectedCircuit;
    $service_tmp_HOH{$Hcount}->{'ProtectingCircuit'} = $ProtectingCircuit;
    $service_tmp_HOH{$Hcount}->{'BusSvcName'} = $BusSvcName;
    $service_tmp_HOH{$Hcount}->{'SubSvcName'} = $SubSvcName;
    $service_tmp_HOH{$Hcount}->{'BusPriority'} = $ServicePriority;
    $service_tmp_HOH{$Hcount}->{'RawAlarmID'} = $RawAlarmID;
}

sub Load_sr_down_tmp($$$$$$$$$$$$$$$$$$$$$$) {
	my ($count,$FMSAlertKey,$RawAlarmID,$ProtectingCircuit,$ProtectedCircuit,$protected,$SvcInstance,$F8,
	$F9,$ProvisionStatus,$F11,$F12,$F13,$F14,$F15,$F16,$F17,$F18,$F19,$F20,$F21,$F22) = @_;
	
    my $Hcount = scalar(keys %sr_down_tmp_HOH);
	if (%sr_down_tmp_HOH) {} else { $Hcount = 0;}
    $sr_down_tmp_HOH{$Hcount}->{'count'} = $count;
    $sr_down_tmp_HOH{$Hcount}->{'FMSAlertKey'} = $FMSAlertKey;
    $sr_down_tmp_HOH{$Hcount}->{'RawAlarmID'} = $RawAlarmID;
    $sr_down_tmp_HOH{$Hcount}->{'ProtectingCircuit'} = $ProtectingCircuit;
    $sr_down_tmp_HOH{$Hcount}->{'ProtectedCircuit'} = $ProtectedCircuit;
    $sr_down_tmp_HOH{$Hcount}->{'IsCirProtected'} = $protected;
	$sr_down_tmp_HOH{$Hcount}->{'SRInstance'} = $SvcInstance;
    $sr_down_tmp_HOH{$Hcount}->{'SSInstance'} = $F8;
    $sr_down_tmp_HOH{$Hcount}->{'SvcInstance'} = $F9;
    $sr_down_tmp_HOH{$Hcount}->{'SRProvisionStatus'} = $ProvisionStatus;
    $sr_down_tmp_HOH{$Hcount}->{'SSProvisionStatus'} = $F11;
    $sr_down_tmp_HOH{$Hcount}->{'SvcProvisionStatus'} = $F12;
    $sr_down_tmp_HOH{$Hcount}->{'SS_Status'} = $F13;
    $sr_down_tmp_HOH{$Hcount}->{'Svc_Status'} = $F14;
    $sr_down_tmp_HOH{$Hcount}->{'Svc_ServiceID'} = $F15;
    $sr_down_tmp_HOH{$Hcount}->{'Svc_SubSvcName'} = $F16;
    $sr_down_tmp_HOH{$Hcount}->{'Svc_BusPriority'} = $F17;
    $sr_down_tmp_HOH{$Hcount}->{'SGInstance'} = $F18;
    $sr_down_tmp_HOH{$Hcount}->{'SGProvisionStatus'} = $F19;
    $sr_down_tmp_HOH{$Hcount}->{'SG_Status'} = $F20;
    $sr_down_tmp_HOH{$Hcount}->{'Summary'} = $F21;
    $sr_down_tmp_HOH{$Hcount}->{'SR_Status'} = $F22;
}

sub Load_svc_inst_tmp($$$$$$$$$$) {
	my ($count,$FMSAlertKey,$SvcInstance,$ProvisionStatus,$ProtectedCircuit,$ProtectingCircuit,$BusSvcName,
	$SubSvcName,$ServicePriority,$RawAlarmID) = @_;
	my $Hcount = scalar(keys %svc_inst_tmp_HOH);
	if (%svc_inst_tmp_HOH) {} else { $Hcount = 0;}
    $svc_inst_tmp_HOH{$Hcount}->{'count'} = $count;
    $svc_inst_tmp_HOH{$Hcount}->{'FMSAlertKey'} = $FMSAlertKey;
    $svc_inst_tmp_HOH{$Hcount}->{'SvcInstance'} = $SvcInstance;
    $svc_inst_tmp_HOH{$Hcount}->{'ProvisionStatus'} = $ProvisionStatus;
    $svc_inst_tmp_HOH{$Hcount}->{'ProtectedCircuit'} = $ProtectedCircuit;
    $svc_inst_tmp_HOH{$Hcount}->{'ProtectingCircuit'} = $ProtectingCircuit;
    $svc_inst_tmp_HOH{$Hcount}->{'BusSvcName'} = $BusSvcName;
    $svc_inst_tmp_HOH{$Hcount}->{'SubSvcName'} = $SubSvcName;
    $svc_inst_tmp_HOH{$Hcount}->{'BusPriority'} = $ServicePriority;
    $svc_inst_tmp_HOH{$Hcount}->{'RawAlarmID'} = $RawAlarmID;
}

#-----------------------------------------------------------------
# Main
# The main method reads the configuration.
# It then starts the cron process to execute the parsing
# of the input directory at the interval configured.
# If a storm input file was placed in the input directory
# during the last interval then it will be parsed and
# outage or cancellation alerts inserted to the Object
# Server.
#-----------------------------------------------------------------

sub main() {
  logInfo('Starting Service Impact Update Agent (Process='.$0.', PID='.$$.').'.nl);
  # Create new cron object
  my $cron=new Schedule::Cron(\&dispatcher,{nofork=>1,catch=>1,skip=>1});
  # Put new schedule in place - run every 3 minutes
  $cron->add_entry($updatedInterval,\&SIA_Impact);
  # Kick of the first iteration before we hand over to Schedule::Cron.
  logInfo('Calling SIA Impact'.nl);
  SIA_Impact();
  # Hand over to Schedule::Cron start the scheduler
  $cron->run();
  closeDatabase($dbHandle);
}

main();
#exportAlertStatus();

if ($Dev == 1 ) {
	# print the row count of the tables from cramer to console
    logInfo('The number of records in Alerts_status_tmp is '.scalar(keys %alerts_status_tmp).nl);
    my $TMarkerT = "Finished ";
    printTimeMarker($TMarkerT);
    load_analysis();
}

