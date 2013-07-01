/*******************************************************************************************/
/* Name        : Corrupt.c                                                                 */
/* Description : This file contains code for corrupting data and pointer. It is linked at  */
/*               compiled time to the target code where fault(s) need to be injected       */
/*      									   */
/* Owner       : This tool is owned by Gauss Research Group at School of Computing,        */
/*               University of Utah, Salt Lake City, USA.                                  */
/*               Please send your queries to: gauss@cs.utah.edu                            */
/*               Researh Group Home Page: http://www.cs.utah.edu/formal_verification/      */
/* Version     : beta									   */
/* Last Edited : 03/12/2013                                                                */
/* Copyright   : Refer to LICENSE document for details 					   */
/*******************************************************************************************/

#include <stdio.h>
#include <stdlib.h>
#include <time.h>

// Interval can at most be how many instructions?
int max_fault_interval = -1;
static int next_fault_countdown = -1;
// Next fault falls into this BB
static int next_fault_bb_countdown = -1;

/*random seed initialization flag*/
int rand_flag=1;

/*Inject Once Status for data and pointer errors*/
int ijo_flag_data=0;
int ijo_flag_add=0;

/*fault injection count*/
int fault_injection_count=0;

/*Fault Injection Statistics*/
int fault_site_count=0;
int fault_site_intData8bit=0;
int fault_site_intData16bit=0;
int fault_site_intData32bit=0;
int fault_site_intData64bit=0;
int fault_site_float32bit=0;
int fault_site_float64bit=0;
int fault_site_adr=0;

// Program Statistics
// "Instruction" here means LLVM instructions
//    not real machine instructions
//
long num_insts_executed = -1;

static void onCountDownReachesZero() {
	if(max_fault_interval > 0)
		next_fault_countdown= (int)(rand()*1.0f/RAND_MAX*max_fault_interval);
	else
		next_fault_countdown = -1; // Effectively disabling FI
}

void incrementInstCount(int delta) {
	num_insts_executed += delta;
}

#ifdef __cplusplus
extern "C" {
#endif
void initializeFaultInjectionCampaign(int ef, int tf) {
	printf("[Fault Injection Campaign details]\n");
	max_fault_interval = ((tf - 1) / ef) + 1;
	printf("   Max interval: %d\n", max_fault_interval);

	// Read the specified fault site from configuration file.
	{
		FILE* f = fopen("fault_injection.conf", "r");
		if(!f) {
			printf("   Injection campaign configuration not found.\n");
		} else {
			printf("   Injection campaign configuration found.\n");
			ssize_t read;
			size_t len = 0;
			char* line = NULL;
			while((read = getline(&line, &len, f))!=-1) {
				if(sscanf(line, "-initial_next_fault_countdown=%d",
					&next_fault_countdown) == 1) {
					printf("   Next fault CountDown = %d\n",
						next_fault_countdown);
				}
			}
			fclose(f);
		}
	}
}

__attribute__((noinline))
void __printInstCount() {
	printf("Total # instructions exec'ed: %lu\n", num_insts_executed);
}

void printFaultInfo(const char* error_type, unsigned bPos, int fault_index,
	int ef, int tf) {
	 fprintf(stderr, "\n/*********************************Start**************************************/");
	 fprintf(stderr, "\nSucceffully injected %s!!", error_type);
	 fprintf(stderr, "\nTotal # faults injected : %d",fault_injection_count);
	 fprintf(stderr, "\nBit position is: %u",bPos);
	 fprintf(stderr, "\nIndex of the fault site : %d",fault_index);
	 fprintf(stderr, "\nUser defined probablity is: %d/%d",ef,tf);
	 fprintf(stderr, "\n# of instructions exec'ed: %lu\n", num_insts_executed);
	 fprintf(stderr, "\n/*********************************End**************************************/\n");
}


int print_faultStatistics(int inject_once, int ef, int tf, int byte_val){
	printf("\n/*********************Program Statistics****************************/");
	printf("\n# of instructions exec'ed: %lu\n", num_insts_executed);
	printf("\n/*********************Fault Injection Statistics****************************/");
	printf("\nTotal # fault sites enumerated : %d",fault_site_count);
	printf("\nFurther sub-categorization of fault sites below:");
	printf("\nTotal # 8-bit  Int Data fault sites enumerated : %d",fault_site_intData8bit);
	printf("\nTotal # 16-bit Int Data fault sites enumerated : %d",fault_site_intData16bit);
	printf("\nTotal # 32-bit Int Data fault sites enumerated : %d",fault_site_intData32bit);
	printf("\nTotal # 64-bit Int Data fault sites enumerated : %d",fault_site_intData64bit);
	printf("\nTotal # 32-bit IEEE Float Data fault sites enumerated : %d",fault_site_float32bit);
	printf("\nTotal # 64-bit IEEE Float Data fault sites enumerated : %d",fault_site_float64bit);
	printf("\nTotal # Ptr fault sites enumerated : %d",fault_site_adr);
	printf("\n/*********************************End**************************************/\n");
	return 0;
}

// For performance, avoid calling rand() too frequently
static int shouldInject(int ef, int tf) {
	if(next_fault_countdown < 0) return 0;
	next_fault_countdown--;
	if(next_fault_countdown == 0) {
		onCountDownReachesZero();
		return 1;
	} else return 0;
}

char corruptIntData_8bit(int fault_index, int inject_once, int ef, int tf, int byte_val, char inst_data){
	unsigned int bPos;

	fault_site_count++;
	fault_site_intData8bit++;
	if(inject_once == 1)
		ijo_flag_data=1;
	if(ijo_flag_data == 1 && fault_injection_count>0)
		return inst_data;
	if(!shouldInject(ef, tf)) return inst_data;
	
	bPos=rand()%8;
	fault_injection_count++;
	 printFaultInfo("8-bit Int Data Error", bPos, fault_index, ef, tf);
	return inst_data ^ (~((short)0x1<< (bPos)));   
}

short corruptIntData_16bit(int fault_index, int inject_once, int ef, int tf, int byte_val, short inst_data){
	 unsigned int bPos;
	 int rp;
	 fault_site_count++;
	 fault_site_intData16bit++;
	 if(inject_once == 1)
		 ijo_flag_data=1;
	 if(ijo_flag_data == 1 && fault_injection_count>0)
		 return inst_data;
	 
	if(!shouldInject(ef, tf)) return inst_data;

	 if(byte_val>1)
		bPos=(8*(byte_val%2))+rand()%8;
	 else
		bPos=(8*byte_val)+rand()%8;

	 fault_injection_count++;
	 printFaultInfo("16-bit Int Data Error", bPos, fault_index, ef, tf);
	return inst_data ^ (~((short)0x1<< (bPos)));   
}

int corruptIntData_32bit(int fault_index, int inject_once, int ef, int tf, int byte_val, int inst_data){
	 unsigned int bPos;
	 int rp;
	 fault_site_count++;
	 fault_site_intData32bit++;
	 if(inject_once == 1)
		 ijo_flag_data=1;

	 if(ijo_flag_data == 1 && fault_injection_count>0)
			 return inst_data;
	 
	if(!shouldInject(ef, tf)) return inst_data;
	 if(byte_val>3)
			bPos=(8*(byte_val%4))+rand()%8;
	 else
			bPos=(8*byte_val)+rand()%8;
	 fault_injection_count++;
	 printFaultInfo("32-bit Int Data Error", bPos, fault_index, ef, tf);
	return inst_data ^ (~((int)0x1<< (bPos)));   
}

float corruptFloatData_32bit(int fault_index, int inject_once, int ef, int tf, int byte_val, float inst_data){
	 unsigned int bPos;
	 int rp;
	 fault_site_count++;
	 fault_site_float32bit++;
	 if(inject_once == 1)
		 ijo_flag_data=1;

	 if(ijo_flag_data == 1 && fault_injection_count>0)
			 return inst_data;
	 
	if(!shouldInject(ef, tf)) return inst_data;
	 if(byte_val>3)
			bPos=(8*(byte_val%4))+rand()%8;
	 else
			bPos=(8*byte_val)+rand()%8;
	 fault_injection_count++;
	 printFaultInfo("32-bit IEEE Float Data Error", bPos, fault_index, ef, tf);
	 return (float)((int)inst_data ^ (~((int)0x1<< (bPos))));   
}

long long corruptIntData_64bit(int fault_index, int inject_once, int ef, int tf,  int byte_val, long long inst_data){
	 unsigned int bPos;
	 int rp;
	 fault_site_count++;
	 fault_site_intData64bit++;
	 if(inject_once == 1)
		 ijo_flag_data=1;

	 if(ijo_flag_data == 1 && fault_injection_count>0)
			 return inst_data;        
	 
	if(!shouldInject(ef, tf)) return inst_data;
	 bPos=(8*byte_val)+rand()%8;
	 fault_injection_count++;
	 printFaultInfo("64-bit Int Data Error", bPos, fault_index, ef, tf);
	return inst_data ^ (~((long long)0x1<< (bPos)));   
}

double corruptFloatData_64bit(int fault_index, int inject_once, int ef, int tf,  int byte_val, double inst_data){
	 unsigned int bPos;
	 int rp;
	 fault_site_count++;
	 fault_site_float64bit++;
	 if(inject_once == 1)
		 ijo_flag_data=1;

	 if(ijo_flag_data == 1 && fault_injection_count>0)
			 return inst_data;        

	if(!shouldInject(ef, tf)) return inst_data;
	 bPos=(8*byte_val)+rand()%8;
	 fault_injection_count++;
	 printFaultInfo("64-bit IEEE Float Data Error", bPos, fault_index, ef, tf);
	 return (double)((long long)inst_data ^ (~((long long)0x1<< (bPos))));   
}

int* corruptIntAdr_32bit(int fault_index, int inject_once, int ef, int tf,  int byte_val, int* inst_add){
	 unsigned int bPos;
	 int rp;
	 fault_site_count++;
	 fault_site_adr++;
	 if(inject_once == 1)
		 ijo_flag_add=1;

	 if(ijo_flag_add == 1 && fault_injection_count>0)
			 return inst_add;           

	if(!shouldInject(ef, tf)) return inst_add;

	 bPos=(8*byte_val)+rand()%8;
	 fault_injection_count++;

	 printFaultInfo("Ptr32 Error", bPos, fault_index, ef, tf);
	 return (int *)((long long)inst_add ^ (~((long long)0x1<< (bPos))));   
}

long long* corruptIntAdr_64bit(int fault_index, int inject_once, int ef, int tf,  int byte_val, long long* inst_add){
	 unsigned int bPos;
	 int rp;
	 fault_site_count++;
	 fault_site_adr++;
	 if(inject_once == 1)
		 ijo_flag_add=1;

	 if(ijo_flag_add == 1 && fault_injection_count>0)
			 return inst_add;           

	if(!shouldInject(ef, tf)) return inst_add;

	 bPos=(8*byte_val)+rand()%8;
	 fault_injection_count++;

	 printFaultInfo("Ptr64 Error", bPos, fault_index, ef, tf);
	 return (long long *)((long long)inst_add ^ (~((long long)0x1<< (bPos))));   
}

float* corruptFloatAdr_32bit(int fault_index, int inject_once, int ef, int tf,  int byte_val, float* inst_add){
	 unsigned int bPos;
	 int rp;
	 fault_site_count++;
	 fault_site_adr++;
	 if(inject_once == 1)
		 ijo_flag_add=1;

	 if(ijo_flag_add == 1 && fault_injection_count>0)
			 return inst_add;           

	if(!shouldInject(ef, tf)) return inst_add;

	 bPos=(8*byte_val)+rand()%8;
	 fault_injection_count++;

	 printFaultInfo("Float Addr32 Error", bPos, fault_index, ef, tf);
	 return (float *)((long long)inst_add ^ (~((long long)0x1<< (bPos))));   
}

double* corruptFloatAdr_64bit(int fault_index, int inject_once, int ef, int tf,  int byte_val, double* inst_add){
	 unsigned int bPos;
	 int rp;
	 fault_site_count++;
	 fault_site_adr++;
	 if(inject_once == 1)
		 ijo_flag_add=1;

	 if(ijo_flag_add == 1 && fault_injection_count>0)
			 return inst_add;           

	if(!shouldInject(ef, tf)) return inst_add;

	 bPos=(8*byte_val)+rand()%8;
	 fault_injection_count++;
	 printFaultInfo("Float Addr64 Error", bPos, fault_index, ef, tf);
	 return (double *)((long long)inst_add ^ (~((long long)0x1<< (bPos))));   
}

#ifdef __cplusplus
}
#endif
