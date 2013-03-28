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

my $serviceFileName = 'circuitProtection.lookup';
my $LookupDir='D:\\UserData\\testData\\';
my %svc_inst_tmp_HOH = ();
my %service_tmp_HOH = ();
my %alerts_status_tmp = ();
my %last_alarm_id = ();

sub logInfo(@)
{
    print(STDERR scalar(localtime(time()))." Info    : ",@_);
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

#getHighestAlertforService(svcInstance);

