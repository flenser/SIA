#!/usr/bin/perl -w

use 5.8.5;	# Request the one it was developed with and is known to work.

use strict;	# Safety belt

$|=1;

delete $ENV{PATH};
delete $ENV{BASH_ENV};

$ENV{'FREETDSCONF'}='/opt/alu/fms/config/tds.conf';

# Imports
#########

use DBI;
use File::Copy;
use IO::Socket;
use POSIX qw(strftime);
use Schedule::Cron;
use Time::Local;


# Constants
###########
use constant transpowerServer=>'FMSOSP';
use constant transpowerHost=>'Xatsvr01app';
use constant transpowerPort=>4111;
use constant simpactUser=>'root';
use constant simpactPwd=>'';
use constant nl=>"\n";

# Global variables
##################

=head1 ATTRIBUTES / VARIABLES

=head2 $Debug

The defines if the POA is run in Debug mode.

=cut

my $Debug=0;

=head2 $updatedInterval

the time the sImpact agent run every day.

=cut

my $updatedInterval='0-59/1 * * * *';

=head2 $serviceFileName

service Impact File Name. Note, servInfo and circuitProtection maybe used interchangeably.

=cut

my $serviceFileName = 'circuitProtection.lookup';


=head2 $circuitFileName

service Impact File Name.

=cut

my $circuitFileName = 'cirlInfo.lookup';

=head2 $schemeInfoFileName

Scheme Info file name containaing scheme services

=cut

my $schemeInfoFileName = 'schemeInfo.lookup';

=head2 $schemeRouteFileName

Scheme Route file name containaing scheme routes

=cut

my $schemeRouteFileName = 'schemeRoute.lookup';

=head2 $schemeGroupFileName

Scheme Group file name containaing scheme groups

=cut

my $schemeGroupFileName = 'schemeGroup.lookup';

=head2 $LookupDir

The main directory for the sImpact cramer lookup.

=cut

my $LookupDir='/opt/cramer/alu/fms/data/';

=head2 $LogDir

The directory where the POA will place its log files.

=cut

my $LogDir='/opt/alu/fms/logs/';

=head2 $LookupTimeStampFile

The file for the sImpact timestamp reference

=cut

my $LookupTimeStampFile='/opt/alu/fms/data/servImpactTSP.txt';

=head2 $validationError

Stores validation error message

=cut

my $validationError="";
=head2 %filesAndTimestamp

The hashtable contain files and its last modified time stamp

=cut

my %filesAndTimestamp =();

# Generic Subroutines
#############

=head1 SUBROUTINES

=head2 openLogFileHandle()

Returns the log file handle.

=cut

sub openLogFileHandle()
{
  my $logFileHandle;
  if ($LogDir) {
    my $timePrefix=strftime("%Y-%m-%d",localtime(time())).'_';
    open($logFileHandle,'>>'.$LogDir.$timePrefix.'simpact.log') or $logFileHandle=undef;
  }
  return($logFileHandle);
}

=head2 closeLogFileHandle($logFileHandle)

Closes the log file handle.

=cut

sub closeLogFileHandle($)
{
  my ($logFileHandle)=@_;
  close($logFileHandle);
}

=head2 logDebug(@logOutput)

=cut

sub logDebug(@)
{
  my $logFileHandle=openLogFileHandle();
  if ($logFileHandle) {
    print($logFileHandle scalar(localtime(time()))." Debug   : ",@_);
    closeLogFileHandle($logFileHandle);
  }
  if ($Debug) {
    print(STDERR scalar(localtime(time()))." Debug   : ",@_);
  }
}

=head2 logWarn(@logOutput)

=cut

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

=head2 logWarn(@logOutput)

=cut

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

=head2 logInfo(@logOutput)

=cut

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

=head2 checkServer($host,$port)

Checks if a server is reachable under a certain port.

=cut

sub checkServer($$)
{
  my ($host,$port)=@_;
  my $rc=0;
  $host=$host||'';
  $port=$port||0;
  my $socket=new IO::Socket::INET (PeerAddr=>"$host:$port",
                                   Proto=>'tcp',
                                   Timeout=>'1' ); # Timeout.
  if ($socket) {
    close($socket);
    $rc=1;
  }
  return($rc);
}

=head2 initDatabase($objServer,$host,$port)

Initialises dbHandle for the selected object server.

=cut

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

=head2 closeDatabase($dbHandleRef)

Closes the dbHandle.

=cut

sub closeDatabase($)
{
  my ($dbHandleRef)=@_;
  if ($dbHandleRef) {
   $dbHandleRef->disconnect();
  }
}

=head3 dbInsert($dbHandle,$statement)

Insert rows in a database.

=cut

sub dbInsert($$)
{
  my ($dbHandle,$statement)=@_;
  my $rst=0;
  if ($dbHandle) {
     $rst=$dbHandle->do($statement) or raise_data_error($dbHandle,'Failed to insert a record'.$!.$statement);
  }
  return $rst;
}

=head3 dbDelete($dbHandle,$alertsTable)

Delete rows in a database.

=cut

sub dbDelete($$)
{
  my ($dbHandle,$alertsTable)=@_;
  my $rst=0;
  if ($dbHandle) {
    $rst=$dbHandle->do('delete from '.$alertsTable) or logWarn('Failed to perform '.$alertsTable.nl);
    if ($rst) {
    	logInfo('Successfully delete all data in '.$alertsTable.nl);
    }
  }
  return $rst;
}

sub insertServInfoTable($$$)
{
  my ($dbHandle,$primaryKey, $content) = @_;
  my $rc=0;
  chomp($content);
  my ($serviceInstance,$provisionStatus,$protectingCircuit,$protectedCircuit,$busSvcName,$subSvcName,$priority,$schemeRoute)=split(/\t/,$content);
  $schemeRoute=lc($schemeRoute);
  if (not $priority)
  {
    $priority=0;
  }
  $rc=dbInsert($dbHandle,"insert into alerts.servInfo values($primaryKey*2-1,'$serviceInstance','$provisionStatus','$protectingCircuit','$protectedCircuit','$busSvcName','$subSvcName',$priority,$schemeRoute)");
  $rc=dbInsert($dbHandle,"insert into alerts.servInfo values($primaryKey*2,'$serviceInstance','$provisionStatus','$protectedCircuit','$protectingCircuit','$busSvcName','$subSvcName',$priority,$schemeRoute)");
  $rc=dbInsert($dbHandle,"delete from alerts.servInfo where ProtectedCircuit=''");
  return $rc;
}

sub insertCirlInfoTable($$$)
{
  my ($dbHandle,$primaryKey, $content) = @_;
  my $rc=0;
  chomp($content);
  my ($alertKey,$circuitID)=split(/\t/,$content);
  $rc=dbInsert($dbHandle,"insert into alerts.cirlInfo values($primaryKey,'$alertKey','$circuitID')");
  return $rc;
}

sub insertServProtectTable($$$)
{
  my ($dbHandle,$primaryKey, $content) = @_;
  my $rc=0;
  chomp($content);
  my ($protectedService,$protectingService)=split(/\t/,$content);
  $rc=dbInsert($dbHandle,"insert into alerts.servProtection values($primaryKey,'$protectedService','$protectingService',true)");
  return $rc;
}

sub insertSchemeServiceTable($$$)
{
  my ($dbHandle,$primaryKey, $content) = @_;
  my $rc=0;
  chomp($content);
  my ($serviceInstance,$protectingScheme,$protectedScheme,$provisionStatus)=split(/\t/,$content);
  $rc=dbInsert($dbHandle,"insert into alerts.schemeService values($primaryKey,'$serviceInstance','$provisionStatus','$protectingScheme','$protectedScheme')");
  return $rc;
}

sub insertSchemeRouteTable($$$)
{
  my ($dbHandle,$primaryKey, $content) = @_;
  my $rc=0;
  chomp($content);
  my ($serviceInstance,$protectingSchemeRoute,$protectedSchemeRoute,$siaRule,$provisionStatus)=split(/\t/,$content);
  $rc=dbInsert($dbHandle,"insert into alerts.schemeRoute values($primaryKey,'$serviceInstance','$provisionStatus','$protectingSchemeRoute','$protectedSchemeRoute','$siaRule')");
  return $rc;
}

sub insertSchemeGroupTable($$$)
{
  my ($dbHandle,$primaryKey, $content) = @_;
  my $rc=0;
  chomp($content);
  my ($serviceInstance,$protectingScheme,$protectedScheme,$busSvcName,$subSvcName,$priority,$provisionStatus)=split(/\t/,$content);
  $rc=dbInsert($dbHandle,"insert into alerts.schemeGroup values($primaryKey,'$serviceInstance','$provisionStatus','$protectingScheme','$protectedScheme','$busSvcName','$subSvcName',$priority)");
  return $rc;
}

sub insertAlertsStatusTable($$$$)
{
  my ($dbHandle,$type,$Summary,$severity) = @_;
  chomp($Summary);
  my $rc=0;
  my $identifier = 'sImpactAgent.pl:'.transpowerHost .':'.transpowerServer;
  my $Node=transpowerHost;
  my $statement= "insert into alerts.status (Identifier,AlertKey,Summary,Agent,AlertGroup,Node,Manager,Severity,FirstOccurrence, LastOccurrence,Type) values ('$identifier', 'sImpactAgent.pl','$Summary','sImpactAgent.pl','Cramer export Perl Script' ,'$Node','SIA Export Perl Script', $severity,getdate(),getdate(),$type)";
  $rc=$dbHandle->do($statement) or logWarn('Failed to insert alert'.$!.nl);
  return $rc;
}

=head2 checkForNewFiles()

=cut

sub checkForNewFiles($)
{
  my ($filename) = @_;
  if ($LookupDir) {
    my ($dev,$ino,$mode,$nlink,$uid,$gid,$rdev,$size,$atime,$mtime,$ctime,$blksize,$blocks)=stat($LookupDir.$filename);
    logInfo ('The last modified time stamp for '.$filename.' file is : '.$mtime.nl) if $mtime;
    if(exists $filesAndTimestamp{$filename}&&$mtime){
  	return 0 if($mtime eq $filesAndTimestamp{$filename});
    } elsif(!$mtime)  {
		raise_error_alert('Unable to find '.$filename);
	}

    return $mtime;
  }else{
  	logWarn('The directory $LookupDir does not exist'.nl);
  	return 0;
  }
}

=head2 checkForOldFile()

=cut

sub checkForOldFile()
{
  my ($file) = @_;
  my $fage=-1;
  my $error_cnt=1;
  my $oldfiles="NO";
  open( FILE, '<'.$LookupTimeStampFile ) or logDie('Unable to open '.$LookupTimeStampFile.'. ',$!.nl);
  while(<FILE>){
		my ($filename,$timestamp) = split(/,/);
		if ($LookupDir) {
		$fage= -M ($LookupDir.$filename);
		#print ('Age of file '.$filename.' is : '.$fage.' days'.nl);
		
			if ($fage>1) {
				$validationError = $validationError.'Error '.$error_cnt.') '.$filename.' older than 24hours ';
				$error_cnt++;
				$oldfiles="YES"
			}
		}else{
  	logWarn('The directory $LookupDir does not exist'.nl);
  	
  }
  
  }
  close(FILE);
  if   ($oldfiles eq "YES") {
	my $type = 1;
	my $Summary = 'Cramer export files are older than 24hours ';
	my $severity = 5;
	#print "open dbhandle";
	my $dbHandle =initDatabase(transpowerServer,transpowerHost,transpowerPort);
	if ($dbHandle) {
	my $rc=insertAlertsStatusTable($dbHandle,$type,$Summary,$severity);
    
	#print ("validation failed");
	logWarn('Validation Error -'. $validationError.nl);
	$validationError = $Summary;
	}
  }

  } 

=head2  raise_data_error($dbhandle$error_message)
Raise error alert
=cut  
sub raise_data_error($$)
{
my ($dbHandle,$msg) = @_;
    logWarn($msg.nl);
	my $type = 1;
	my $Summary = $validationError.'Error while inserting record ';
	my $severity = 4;
	if ($dbHandle) {
	my $rc=insertAlertsStatusTable($dbHandle,$type,$Summary,$severity);
	}
}

=head2  raise_error_alert($error_message)
Raise error alert and exit
=cut  
sub raise_error_alert($)
{
my ($msg) = @_;
    logWarn($msg);
	my $type = 1;
	my $Summary = $validationError.$msg;
	my $severity = 5;
	my $dbHandle =initDatabase(transpowerServer,transpowerHost,transpowerPort);
	if ($dbHandle) {
	my $rc=insertAlertsStatusTable($dbHandle,$type,$Summary,$severity);
	$validationError = $Summary;
	logDie($validationError,'Validation error '.nl);
	}
}
=head2  writeTimeStamp($filename,$timestamp)

=cut

sub writeTimeStamp()
{
  open( FILE, '>'.$LookupTimeStampFile ) or logDie('Unable to open '.$LookupTimeStampFile.'. ',$!.nl);
  logInfo("Write time stamp into the lookup time stamp file".nl);
  while ( my ($fn,$ts) = each %filesAndTimestamp) {
      print FILE $fn.','.$ts.nl if ($fn&&$ts);
  }
  close(FILE);
}

=head2  getTimeStamp($filename)

=cut

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

=head2 sImpact()

The process that will be executed by Schedule::Cron
5 minutes after midle night per day.

=cut

sub sImpact()
{
	logInfo('##### Running Service Impact parsing iteration.'.nl);
	logInfo('Checking for Serivce Impact files.'.nl);
	my $dbHandle;
	my $stime;
	my $ctime;
	my $sstime;
	my $srtime;
	my $sgtime;

	getTimeStamp();
	$stime=checkForNewFiles($serviceFileName);
	$ctime=checkForNewFiles($circuitFileName);
	$sstime=checkForNewFiles($schemeInfoFileName);
	$srtime=checkForNewFiles($schemeRouteFileName);
	$sgtime=checkForNewFiles($schemeGroupFileName);
    checkForOldFile();
	if ($stime) {
	  	open(SERVFILE, '<'.$LookupDir.$serviceFileName) or raise_error_alert('Unable to  open '.$serviceFileName);
	} 



	if ($ctime) {
		open(CIRFILE, '<'.$LookupDir.$circuitFileName
					) or raise_error_alert('Unable to  open '.$circuitFileName);
	} 

	if ($sstime) {
	  	open(SSFILE, '<'.$LookupDir.$schemeInfoFileName
	  				) or raise_error_alert('Unable to  open '.$schemeInfoFileName);
	} 

	if ($srtime) {
	  	open(SRFILE, '<'.$LookupDir.$schemeRouteFileName
	  				) or raise_error_alert('Unable to  open '.$schemeRouteFileName);
	}
	if ($sgtime) {
	  	open(SGFILE, '<'.$LookupDir.$schemeGroupFileName
	  				) or raise_error_alert('Unable to  open '.$schemeGroupFileName);
	}     
   
	if($stime||$ctime||$sstime||$srtime || $sgtime){
		logInfo('Open DB handle '.nl);
		$dbHandle =initDatabase(transpowerServer,transpowerHost,transpowerPort);
		if($dbHandle){
				my $count = 1;
				my $rc = 1;
				my $Summary = '';
				my $severity = 0;
				my $type = 0;
				if($stime){
					dbDelete($dbHandle,'alerts.servInfo');
					logInfo('Populate ServInfo table '.nl);
					while(<SERVFILE>){
						$rc=$rc&&insertServInfoTable($dbHandle,$count,$_);
						$count++;
					}
					if($rc){
						$filesAndTimestamp{$serviceFileName} = $stime;
						logInfo('the circuit protection table has been successfully updated.'.nl);
					}
				}

				if($ctime){
					$count = 1;
					$rc =1;
					dbDelete($dbHandle,'alerts.cirlInfo');
					logInfo('Populate cirInfo table '.nl);
					while(<CIRFILE>){
						$rc=$rc&&insertCirlInfoTable($dbHandle,$count,$_);
						$count++;
					}
					if($rc){
						$filesAndTimestamp{$circuitFileName} = $ctime;
						logInfo('the circuit information table has been successfully updated.'.nl);
					}
				}
				if($sstime){
					$count = 1;
					$rc =1;
					logInfo('Populate schemeService table '.nl);
					dbDelete($dbHandle,'alerts.schemeService');
					while(<SSFILE>){
						$rc=$rc&&insertSchemeServiceTable($dbHandle,$count,$_);
						$count++;
					}
					if($rc){
						$filesAndTimestamp{$schemeInfoFileName} = $sstime;
						logInfo('Scheme service information table has been successfully updated.'.nl);
					}
				}
				if($srtime){
					$count = 1;
					$rc =1;
					logInfo('Populate schemeRoute table '.nl);
					dbDelete($dbHandle,'alerts.schemeRoute');
					while(<SRFILE>){
						$rc=$rc&&insertSchemeRouteTable($dbHandle,$count,$_);
						$count++;
					}
					if($rc){
						$filesAndTimestamp{$schemeRouteFileName} = $srtime;
						logInfo('the scheme route information table has been successfully updated.'.nl);
					}
				}
				if($sgtime){
					$count = 1;
					$rc =1;
					logInfo('Populate schemeGroup table '.nl);
					dbDelete($dbHandle,'alerts.schemeGroup');
					while(<SGFILE>){
						$rc=$rc&&insertSchemeGroupTable($dbHandle,$count,$_);
						$count++;
					}
					if($rc){
						$filesAndTimestamp{$schemeGroupFileName} = $sgtime;
						logInfo('the scheme group information table has been successfully updated.'.nl);
					}
				}
			if (!$validationError) {
			$type = 2;
			$Summary = 'Cramer data imported sucessfully';
			$severity = 1;
			$rc=insertAlertsStatusTable($dbHandle,$type,$Summary,$severity);
			}
		}
		logInfo('Close DB Handle '.nl);
		closeDatabase($dbHandle);
	}
	writeTimeStamp();
	logInfo('Close File Handles '.nl);
	close(SERVFILE) if ($stime);
	close(CIRFILE) if ($ctime);
	close(SSFILE) if ($sstime);
	close(SRFILE) if ($srtime);
	close(SGFILE) if ($sgtime);
}

=head2 dispatcher()

The default Schedule::Cron dispatcher.

=cut

sub dispatcher()
{
  logDebug('no subroutine passed to Schedule::Cron. Existing now!'.nl);
  exit(1);
}

=head2 log_method()

The Schedule::Cron logger.
Add the log option to the constructor if you want logging.
new Schedule::Cron(.... , log => $log_method);

=cut

sub log_method($$)
{
  my ($level,$msg)=@_;
  my $DBG_MAP={0=>'INFO',1=>'WARN',2=>'ERROR'};
  print($DBG_MAP->{$level}.$msg.nl);
}


# Main
######

=head2 main()

The main method reads the configuration.
It then starts the cron process to execute the parsing
of the input directory at the interval configured.
If a storm input file was placed in the input directory
during the last interval then it will be parsed and
outage or cancellation alerts inserted to the Object
Server.

=cut


sub main() {
  logInfo('Starting Service Impact Update Agent (Process='.$0.', PID='.$$.').'.nl);
  # Create new cron object
  my $cron=new Schedule::Cron(\&dispatcher,{nofork=>1,catch=>1,skip=>1});
  #five minutes after midnight, every day
  $cron->add_entry($updatedInterval,\&sImpact);
  # Kick of the first iteration before we hand over to Schedule::Cron.
  logInfo('Calling sImpact '.nl);
  sImpact();
  # Hand over to Schedule::Cron start the scheduler
  $cron->run();
}

main();
