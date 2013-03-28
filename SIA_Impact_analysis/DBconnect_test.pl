#!/usr/bin/perl

use 5.8.5;
$|=1;

use DBI;
use File::Copy;
use IO::Socket;
use POSIX qw(strftime);
#use Schedule::Cron;
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
use constant transpowerHost=>'aalsun61';
use constant PrimaryQuery=>"select SvcInstance,ServerName_ServerSerial,BusPriority,ServicesImpacted,ImpactedStatus,SuppressEscl,Type,Severity,ServiceImpactingFlag,FMSAlertKey,ServiceID,SubService,LastOccurrence,ProtectingCircuit,ProtectedCircuit from alerts.status where Type = 1 and Severity > 3 and ServiceImpactingFlag = 1 and FMSAlertKey<>''";

my $serviceFileName = 'circuitProtection.lookup';
my $LookupDir='D:\\UserData\\testData\\';
my %svc_inst_tmp_HOH = ();
my %service_tmp_HOH = ();
my %alerts_status_tmp = ();
my %last_alarm_id = ();
my %HashOfHash = ();
my %svc_inst_counted = ();

sub logInfo(@)
{
    print(STDERR scalar(localtime(time()))." Info    : ",@_);
}
sub logWarn(@)
{
    print(STDERR scalar(localtime(time()))." Warning    : ",@_);
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
sub buildLastAlarmIDHash {
# This traverses the svc_inst_tmp and service_tmp HOH arrays and finds the raw alarm id for
# each svcInstance which has the highest last occurrence time. The last occurrence time
# is in the alerts_status_tmp array.
   my %raw_alarm_ids = ();
   
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
   
   foreach my $SvcInstance (keys %raw_alarm_ids) {
      my $lastOccurrence = 0;
      foreach my $Svc_RawAlarmID (@{$raw_alarm_ids{$SvcInstance}}) {
        foreach my $hash_keyB(keys %alerts_status_tmp) {
	      my $AS_ServerName_ServerSerial = $alerts_status_tmp{$hash_keyB}->{'ServerName_ServerSerial'};
	      my $AS_LastOccurrence = $alerts_status_tmp{$hash_keyB}->{'LastOccurrence'};
	      if ($Svc_RawAlarmID eq $AS_ServerName_ServerSerial) {
	        if ($AS_LastOccurrence gt $lastOccurrence) {
	          $last_alarm_id{$SvcInstance}->{'RawAlarmID'} = $Svc_RawAlarmID;
	          $lastOccurrence = $AS_LastOccurrence;
	        }
	      }
        }
      }
   }
}
sub fillHOH {
   print "start fill\n";
   
   for (my $i=0;$i<5;$i++) {
      $HashOfHash{$i}->{'name'} = "Name".$i;
      $HashOfHash{$i}->{'count'} = $i;
      my $multi = $i * 3;
      $HashOfHash{$i}->{'multi'} = $multi;
      $HashOfHash{$i}->{'family'} = "Some hashes";
      if ($i == 2 || $i == 3) {
         $svc_inst_counted{$HashOfHash{$i}->{'name'}} = "TRUE";
      }
   }
   print "hash filled\n";
}
sub printHash {
   print "hash content:\n";
   foreach my $hashkey(keys %HashOfHash) {
      my $Count = $HashOfHash{$hashkey}->{'count'};
      my $Name = $HashOfHash{$hashkey}->{'name'};
      my $Multi = $HashOfHash{$hashkey}->{'multi'};
      my $Family = $HashOfHash{$hashkey}->{'family'};
      print "$Count - $Family,$Name - $Multi\n";
      if (defined $svc_inst_counted{$Name}) {
         print "Counted? $svc_inst_counted{$Name}\n";
      }
   }
}
sub findMatch4Delete {
   my ($toDelete)=@_;
   
   foreach my $outer(keys %HashOfHash) {
     my $Outside = $HashOfHash{$outer}->{'count'};
     if (!defined $Outside) {
       delete $HashOfHash{$outer};
       last;
     }
     print "\nouter loop: $Outside\n";
     foreach my $inner(keys %HashOfHash) {
        my $Count = $HashOfHash{$inner}->{'count'};
        print "inner loop: $Count ";
        if ($Count eq $toDelete) {
           delete $HashOfHash{$inner};
        }
     }
   }
}

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

sub closeDatabase($)
{
  my ($dbHandleRef)=@_;
  if ($dbHandleRef) {
     $dbHandleRef->disconnect();
  }
}


#my $TMarkerT = "Opening Database connection ";
#printTimeMarker($TMarkerT);
#my $dbHandle = initDatabase(transpowerServer,transpowerHost,transpowerPort);
#
#if ($dbHandle) {
#   logInfo('Db handle is OK'.nl);
#   $TMarkerT = "database open ";
#   printTimeMarker($TMarkerT);
#}
fillHOH;
printHash;
#findMatch4Delete(2);
#printHash;
#getHighestAlertforService(svcInstance);
