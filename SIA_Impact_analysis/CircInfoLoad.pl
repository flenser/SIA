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
use constant transpowerHost=>'xatsvr01app';
use constant PrimaryQuery=>"select * from alerts.status where Type = 1 and Severity > 3 and ServiceImpactingFlag = 1 and FMSAlertKey<>''";

# Set Global Variables
my $Debug=0;
my $Dev = 1; 
my $updatedInterval='0-59/5 * * * *';
my $serviceFileName = 'circuitProtection.lookup';
my $circuitFileName = 'cirlInfo.lookup';
my $schemeInfoFileName = 'schemeInfo.lookup';
my $schemeRouteFileName = 'schemeRoute.lookup';
my $schemeGroupFileName = 'schemeGroup.lookup';
my $LookupDir='/opt/cramer/alu/fms/data/';
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

# set Developement Headers
if ($Dev == 1 ) {
#	$LookupDir='/opt/alu/fms/data/perlperftestdata/';
#	$LogDir='D:\\customer\\Transpower\\netcool perl project\\EProject\\';
	$LookupDir='D:\\UserData\\testData\\';
#	$LookupTimeStampFile='D:\\customer\\Transpower\\netcool perl project\\testData\\servImpactTSP.txt';
}

sub logInfo(@)
{
    print(STDERR scalar(localtime(time()))." Info    : ",@_);
}

#sub LoadCirlInfoData($) {
#	my $ctime = $_[0];
#	my $RecordCount = 0;
#	  	open(CIRFILE, '<'.$LookupDir.$circuitFileName
#					) or print "Unable to  open " .$circuitFileName . nl;
#		logInfo('Populate Ciruit Information table ');
#		while (<CIRFILE>) {
#			my @DataSet1 = split/\t/,$_;
#			my $FMSAlertKey = $DataSet1[0];
#			my $CircuitID = $DataSet1[1];
#			chomp $CircuitID;
#			$cirlInfo_AOA[$RecordCount]= @DataSet1;	
#			$RecordCount += 1;
#		}
#		close(CIRFILE);
#        my $maxrows_CP = $RecordCount;
#        logInfo('there are '.$maxrows_CP.' rows '.nl);
#}

sub LoadCirlInfoData() {
	my $RecordCount = 0;
	  	open(CIRFILE, '<'.$LookupDir.$circuitFileName
					) or print "Unable to  open " .$circuitFileName . nl;
		logInfo('Populate Ciruit Information table '.nl);
		while (<CIRFILE>) {
			my @DataSet1 = split/\t/,$_;
			my $FMSAlertKey = $DataSet1[0];
			my $CircuitID = $DataSet1[1];
			chomp $CircuitID;
			#$cirlInfo_AK{$FMSAlertKey}= $CircuitID;
			#$cirlInfo_CID{$CircuitID}= $FMSAlertKey;
			push @{ $cirlInfo_AK{$FMSAlertKey} }, $CircuitID;
			push @{ $cirlInfo_CID{$CircuitID} }, $FMSAlertKey;
		}
		close(CIRFILE);
        my $max_AK = scalar(keys %cirlInfo_AK);
        my $max_CID = scalar(keys %cirlInfo_CID);
        logInfo('there are '.$max_AK.' AlertKeys '.nl);
        logInfo('there are '.$max_CID.' CircuitIDs '.nl);
}

sub PrintHashContent() {
    my $k = '';
    print "Hash content\n";
    foreach $k (keys %cirlInfo_CID) {
       print "$k";
       foreach (@{$cirlInfo_CID{$k}}) {
          print " : $_";
       }
       print "\n";
    }
}

LoadCirlInfoData();
PrintHashContent();
