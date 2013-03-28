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
my %circuitProtection_HOH = ();
my %circuitProtection_HOA;
my $recursion = 0;

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

sub LoadCircuitProtectionData($) {
	my $stime = $_[0];
	my $RecordCount = 0;
	if ($stime) {
	  	open(SERVFILE, '<'.$LookupDir.$serviceFileName) or print "Unable to  open ".$serviceFileName.nl;
		logInfo('Populate ServInfo table '.nl);
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

sub followRelevantCircuit {
   my ($RelevantCircuit,$E2ECircuit,$SvcName,$ProtectingCrt2) = @_;
   my $count = 0;
   my $SvcInstance = undef;
   my $E2ECircuit1 = undef;
   my $RelevantCircuit1 = undef;
   $recursion++;
   
   do {
      $SvcInstance = @{$circuitProtection_HOA{$RelevantCircuit}}[$count];
      $E2ECircuit1 = @{$circuitProtection_HOA{$RelevantCircuit}}[$count+2];
print "InRelevantCircuit:$recursion rel: $RelevantCircuit, svc: $SvcInstance, e2e: $E2ECircuit1\n";
      if (($SvcInstance eq $SvcName) && ($E2ECircuit1 eq $E2ECircuit)) {
          $RelevantCircuit1 = @{$circuitProtection_HOA{$RelevantCircuit}}[$count+1];
          if ($RelevantCircuit1 eq '') {
            print "rel empty\n";
            return (0);
          }
          if ($RelevantCircuit1 eq $ProtectingCrt2) {
            print "match found\n";
            return (1);
          }
# Step 4 - match protected circuit to relevant overlying circuit and service name
          followRelevantCircuit($RelevantCircuit1,$E2ECircuit1,$SvcName,$ProtectingCrt2);
          $count += 3;
       }
   } until !defined @{$circuitProtection_HOA{$RelevantCircuit}}[$count];
}

sub isInHierarchy($$$) {
   my ($ProtectingCrt1,$ProtectingCrt2,$SvcName) = @_;
   
# Step 0 - check for direct match of the 2 inputs, otherwise go to next steps
   if (($ProtectingCrt1 eq $ProtectingCrt2) ||
        matchProtectingCircuits($ProtectingCrt1,$ProtectingCrt2,$SvcName) ||
        matchProtectingCircuits($ProtectingCrt2,$ProtectingCrt1,$SvcName)) {
     print "Found a match\n";
     return (1);
   } else {
     print "Found NO match\n";
     return (0);
   }
}

sub matchProtectingCircuits($$$) {
#This function returns a true or false based on the input strings and the data in the circuit protection
#file. In order to determine what to return the following processing needs to be done:
#
#2 lists are created , one for each protecting circuit
#For each circuit the list is created as follows:
#
#Step 1)Find the first entry in the circuitprotection file that has the value of the protected circuit
#       and the same service name in the svcinstance column
#Step 2)Add the protected circuit to the list
#Step3) Record the e2ecircuit value of this row in the list.
#Step4) Using the relevant overlying circuit value, search the circuitProtection file for a row
#  which has the values as:
#        Protected circuit of this row = relevant overlying circuit of the original row
#        E2ecircuit of this row = e2e circuit of original row
#        svcinstance of this row  = svcinstance of original row
#Step 5) Add the relevant overlying circuit value of this row to the list and continue from step 2,
#  repeat the step till the relevant overlying circuit value becomes null.             
#
#When the above steps are run for input1 and input2, check if the list of input1 has input2 in it
# OR the list of input2 has input1 in it. If it does then return true, else return false
   my ($ProtectingCrt1,$ProtectingCrt2,$SvcName) = @_;
   my $SvcInstance = undef;
   my $RelevantCircuit = undef;
   my $E2ECircuit = undef;
   my $count = 0;
   $recursion = 0;
   
# Step 1 - match protected circuit to protecting circuit and service name
   do {
      $SvcInstance = @{$circuitProtection_HOA{$ProtectingCrt1}}[$count];
#      print "$count - svc: $SvcInstance";
      if ($SvcInstance eq $SvcName) {
         $E2ECircuit = @{$circuitProtection_HOA{$ProtectingCrt1}}[$count+2];
         $RelevantCircuit = @{$circuitProtection_HOA{$ProtectingCrt1}}[$count+1];
         print "$count - svc: $SvcInstance, e2e: $E2ECircuit, rel: $RelevantCircuit\n";
         if (!defined $RelevantCircuit) {
           print "rel undefined\n";
           return (0);
         }
         if (($E2ECircuit eq $ProtectingCrt2) || ($RelevantCircuit eq $ProtectingCrt2)) {
           print "match found\n";
           return (1);
         }
# Step 4 - match protected circuit to relevant overlying circuit and service name
         followRelevantCircuit($RelevantCircuit,$E2ECircuit,$SvcName,$ProtectingCrt2);
      }
      $count += 3;
   } until !defined @{$circuitProtection_HOA{$ProtectingCrt1}}[$count];
   print "NO match found in part\n";
   return (0);
}

LoadCircuitProtectionData(1);
isInHierarchy("MGMRTE001-TPTRTC001-PATH-2","EMSSX006-MGMRTE001-EC-75241","UHT Metering Service-12142");

#isInHierarchy("BPEMXS002-HAYMXS002-VC12-M0082","RCSMXP913-SFDMXP901-2400bps-3187A","SFD NCC SCADA");


