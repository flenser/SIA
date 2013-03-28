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

use constant nl=>"\n";

my $LogDir='D:\\UserData\\testData\\';
my %Synthetic_alarm_storage_HOH = ();

my $ST_Svc_Status = 'Svc Downgraded';

print "--- ST_Svc_Status: $ST_Svc_Status\n";
          if ($ST_Svc_Status =~ m/'Svc Downgraded'/) {
print "--- in Downgraded....\n";
          } elsif ($ST_Svc_Status eq 'Svc Loss') {
print "--- in Loss....\n";
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

sub logInfo(@)
{
  my $logFileHandle=openLogFileHandle();
  if ($logFileHandle) {
    print($logFileHandle scalar(localtime(time()))." Info    : ",@_);
    closeLogFileHandle($logFileHandle);
  }
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
	if (defined $data) {
	    return $data;
	} else {
	    return 0;
	}
} 

sub UpdateSynthetic_alarm_storage_HOH($$$$) {
        my ($SA_ProvisionStatus,$SA_BusPriority,$SA_BusSvcName,$SA_Number) = @_;
        my $Hcount = scalar(keys %Synthetic_alarm_storage_HOH);
        if (%Synthetic_alarm_storage_HOH) {} else { $Hcount = 0;}
    #load data into HOH
        $Synthetic_alarm_storage_HOH{$Hcount}->{'ProvisionStatus'} = $SA_ProvisionStatus;
        $Synthetic_alarm_storage_HOH{$Hcount}->{'BusPriority'} = $SA_BusPriority;
        $Synthetic_alarm_storage_HOH{$Hcount}->{'BusSvcName'} = $SA_BusSvcName;
        $Synthetic_alarm_storage_HOH{$Hcount}->{'Number'} = $SA_Number;
}

UpdateSynthetic_alarm_storage_HOH("TRUE",undef,'Bus 1',99);
UpdateSynthetic_alarm_storage_HOH("FALSE",0,'Bus 2',23);
UpdateSynthetic_alarm_storage_HOH("TRUE",undef,'Bus 3',1);
UpdateSynthetic_alarm_storage_HOH("FALSE",3,'Bus 4',9689);
UpdateSynthetic_alarm_storage_HOH("TRUE",5,'Bus 5',111);
UpdateSynthetic_alarm_storage_HOH("TRUE",undef,'Bus 6',959);

print "status,priority,name,number\n";

foreach my $hash_keyA(keys %Synthetic_alarm_storage_HOH) {
   my $status = $Synthetic_alarm_storage_HOH{$hash_keyA}->{'ProvisionStatus'};
   my $priority = checkNum($Synthetic_alarm_storage_HOH{$hash_keyA}->{'BusPriority'});
   my $name = $Synthetic_alarm_storage_HOH{$hash_keyA}->{'BusSvcName'};
   my $number = $Synthetic_alarm_storage_HOH{$hash_keyA}->{'Number'};
   print "$status,$priority,$name,$number\n";
   logInfo("$status,".
   "$priority,".
   "$name,".
   "$number".nl);
}

