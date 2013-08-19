/*******************************************************************************************/
/* Name        : Corrupt.c                                                                 */
/* Description : This file contains code for corrupting data and pointer. It is linked at  */
/*               compiled time to the target code where fault(s) need to be injected       */
/*      																				   */
/* Owner       : This tool is owned by Gauss Research Group at School of Computing,        */
/*               University of Utah, Salt Lake City, USA.                                  */
/*               Please send your queries to: gauss@cs.utah.edu                            */
/*               Researh Group Home Page: http://www.cs.utah.edu/formal_verification/      */
/* Version     : beta																	   */
/* Last Edited : 07/13/2013                                                                */
/* Copyright   : Refer to LICENSE document for details 									   */
/*******************************************************************************************/
// Changes on Jul 2: Byteval==-1 --> Randomly choose injection bit
// Changes on Jul 11: Reads function name whitelist from funclist.txt; this will only enable error injection in those functions.
// Changes on Jul 23: Added "incrementFaultSiteCount" call. This function is used
//                   in conjunction with updated faults.cpp. It is called at the beginning
//                   of each BasicBlock of the original bytecode.
// Changes on Jul 31: Need specify bit position.

#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <map>

#ifdef __cplusplus
extern "C" {
#else
	#error "Please compile Corrupt.cpp with a C++ compiler."
	This is a syntax error placed here to stop the compiler
#endif

// Interval can at most be how many instructions?
static unsigned curr_bb_fs_count = 0;
static bool curr_bb_no_fault = true;
int max_fault_interval = -1;
static long next_fault_countdown = -1;
// Next fault falls into this BB

/*random seed initialization flag*/
int rand_flag=1;

/*Inject Once Status for data and pointer errors*/
int ijo_flag_data=0;
int ijo_flag_add=0;

/*fault injection count*/
int fault_injection_count=0;

/* Fault Injection Statistics */
// Tommy: On 20130723, the meaning of the counts have changed a bit
//   Since I've added branch instructions to bypass calls to corrupt* functions
//   in hope for accelerating the resultant binaries, fault_site_count_[type]
//   are not incremented unless the next fault site is in "this basicblock"
//   of the original binary (i.e. not injected)
unsigned long fault_site_count = 0;
unsigned long fault_site_next_count = 0; // The count when the current BB ends
int fault_site_intData1bit = 0;
int fault_site_intData8bit = 0;
int fault_site_intData16bit = 0;
int fault_site_intData32bit = 0;
int fault_site_intData64bit = 0;
int fault_site_float32bit = 0;
int fault_site_float64bit = 0;
int fault_site_adr = 0;

int bit_position = -1;

int enable_fault_site_hist = 0;
static unsigned curr_hist_size = 1000;
static unsigned* fault_site_hist;

static bool is_dump_bb_trace = false;

// This guy should be idempotent
static void incrementFaultSiteHit(int fsid) {
	if(enable_fault_site_hist == 0) return;
	if(fsid >= curr_hist_size) {
		unsigned* tmp = (unsigned*)(malloc(sizeof(unsigned) * curr_hist_size * 2));
		for(int i=0; i<curr_hist_size; i++) { tmp[i] = fault_site_hist[i]; }
		for(int i=curr_hist_size; i < curr_hist_size*2; i++) tmp[i] = 0;
		curr_hist_size *= 2;
		free(fault_site_hist);
		fault_site_hist = tmp;
	}
	fault_site_hist[fsid] = fault_site_hist[fsid] + 1;
}

void writeFaultSiteHitHistogram() {
	const char* filename = "fault_site_histogram.txt";
	FILE* f = fopen("fault_site_histogram.txt", "w");
	if(!f) f = stderr;

	fprintf(f, "FaultSiteIndex\tNumOfEnumeration\n");
	for(int i=0; i<curr_hist_size; i++) {
		if(fault_site_hist[i] > 0)
			fprintf(f, "%d\t%u\n", i, fault_site_hist[i]);
	}
/*
	for(std::map<int, unsigned>::iterator itr = fault_site_hist.begin();
		itr != fault_site_hist.end(); itr++) {
		int fsid = itr->first;
		unsigned count = itr->second;
		fprintf(f, "%d\t%u\n", fsid, count);
	}
*/

	fclose(f);
	printf("Fault site hit histogram saved to %s.\n", filename);
}

// Program Statistics
// "Instruction" here means LLVM instructions
//    not real machine instructions
//
static void onCountDownReachesZero() {
	bool is_ijo = ((ijo_flag_data!=0) || (ijo_flag_add!=0));
	if((!is_ijo) && max_fault_interval > 0) {
		next_fault_countdown= (int)(rand()*1.0f/RAND_MAX*max_fault_interval);
	} else {
		next_fault_countdown = -1; // Effectively disabling FI
	}
	curr_bb_no_fault = true;
}

void incrementFaultSiteCount(char* bbname, int bb_fs_count) {
	// When "logging fault site hit histograms" option is enabled,
	//   must always set "curr_bb_no_fault" to false
	if(is_dump_bb_trace) {
		fprintf(stderr, "[KULFI] Entered BB \"%s\"\n", bbname);
	}
	
	if(enable_fault_site_hist) {
		curr_bb_no_fault = false;
	} else {
		if(next_fault_countdown <= bb_fs_count) {
			if(next_fault_countdown >= 0) {
				curr_bb_no_fault = false;
				// in this case, fault site count is not incremented here. should be incremented by corrupt*().
			} else {
				// This shall only happen when the USER specifies an
				//   initial countdown which is < 0
				fault_site_count += bb_fs_count;
			}
		} else {
			// Increment this BB's FS count. Data integrity is guaranteed
			// because the next fault should not be in this BB
			fault_site_count += bb_fs_count;
			next_fault_countdown -= bb_fs_count;
			curr_bb_no_fault = true;
		}
	}
}

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
				if(sscanf(line, "-initial_next_fault_countdown=%ld",
					&next_fault_countdown) == 1) {
					printf("   Next fault CountDown = %ld\n", next_fault_countdown);
				}
				if(sscanf(line, "-rand_flag=%d",
					&rand_flag) == 1) {
					printf("   Should initialize randseed = %d\n", rand_flag);
				}
				if(sscanf(line, "-enable_fault_site_hist=%d",
					&enable_fault_site_hist) == 1) {
					printf("   Will print fault site histogram to fault_site_histogram.txt\n");
					fault_site_hist = (unsigned*)(malloc(sizeof(unsigned) * curr_hist_size));
					for(int i=0; i<curr_hist_size; i++) fault_site_hist[i] = 0;
				}
				if(sscanf(line, "-bit_position=%d",
					&bit_position) == 1) {
					printf("   Bit position for faults=%d\n", bit_position);
				}
				if(sscanf(line, "-dump_bb_trace=%d", &is_dump_bb_trace)==1) {
					printf("   Dump BB Trace=%d\n", is_dump_bb_trace);
				}
			}
			fclose(f);
		}
	}
	
	if(rand_flag) {
		printf("   Initialized randomization seed.\n");
		srand(time(0));
	}
}

// This thing may be confusing
//   because 1 instruction can have 2 error sites
__attribute__((noinline))
void __printInstCount() {
	printf("\n***********************************************************\n");
	printf("\nTotal # of fault sites enumerated: %lu\n", fault_site_count);
	printf("\n***********************************************************\n");
}

void printFaultInfo(const char* error_type, unsigned bPos, int fault_index,
	int ef, int tf) {
	 fprintf(stderr, "\n/*********************************Start**************************************/");
	 fprintf(stderr, "\nSucceffully injected %s!!", error_type);
	 fprintf(stderr, "\nTotal # faults injected : %d",fault_injection_count);
	 fprintf(stderr, "\nBit position is: %u",bPos);      
	 fprintf(stderr, "\nIndex of the fault site : %d",fault_index);
	 fprintf(stderr, "\nUser defined probablity is: %d/%d",ef,tf);
	 fprintf(stderr, "\nTotal # of fault sites enumerated: %lu\n", fault_site_count);
	 fprintf(stderr, "\n/*********************************End**************************************/\n");
}
                                             
__attribute__((destructor))
int print_faultStatistics(){
	fprintf(stderr, "\n/*********************Fault Injection Statistics****************************/");
	fprintf(stderr, "\nTotal # fault sites enumerated : %lu",fault_site_count);
	fprintf(stderr, "\nFurther sub-categorization of fault sites below:");
	fprintf(stderr, "\nTotal # 8-bit  Int Data fault sites enumerated : %d",fault_site_intData8bit);
	fprintf(stderr, "\nTotal # 16-bit Int Data fault sites enumerated : %d",fault_site_intData16bit);
	fprintf(stderr, "\nTotal # 32-bit Int Data fault sites enumerated : %d",fault_site_intData32bit);
	fprintf(stderr, "\nTotal # 64-bit Int Data fault sites enumerated : %d",fault_site_intData64bit);
	fprintf(stderr, "\nTotal # 32-bit IEEE Float Data fault sites enumerated : %d",fault_site_float32bit);
	fprintf(stderr, "\nTotal # 64-bit IEEE Float Data fault sites enumerated : %d",fault_site_float64bit);
	fprintf(stderr, "\nTotal # Ptr fault sites enumerated : %d",fault_site_adr);
	fprintf(stderr, "\n/*********************************End**************************************/\n");
	if(enable_fault_site_hist) writeFaultSiteHitHistogram();
	return 0;
}

bool isNextFaultInThisBB() {
	return (!curr_bb_no_fault);
}

static int shouldInject(int ef, int tf) {
	if(next_fault_countdown < 0) return 0;
	next_fault_countdown--;
	if(next_fault_countdown <= 0) {
		onCountDownReachesZero();
		return 1;
	} else return 0;
}

// Changed in order for PHINode to work
// (If there is no PHINode, it's legal to use an i32 where an i1 is required)
// but with PHINode, this has become illegal
bool corruptIntData_1bit(int fault_index, int inject_once, int ef, int tf, int byte_val, char inst_data) {
	unsigned int bPos;
	incrementFaultSiteHit(fault_index);
	fault_site_count++;
	fault_site_intData1bit++;
	if(inject_once == 1)
		ijo_flag_data = 1;
	if(ijo_flag_data == 1 && fault_injection_count>0)
		return inst_data;
	if(!shouldInject(ef, tf)) return inst_data;
	if(bit_position == 0) {	
		fault_injection_count++;
		printFaultInfo("1-bit Int Data Error", bPos, fault_index, ef, tf);
		if(inst_data) return false;
		else return true;
	} else {
		printf("Fault not injected because the set bit position is > 0");
		return inst_data;
	}
}

char corruptIntData_8bit(int fault_index, int inject_once, int ef, int tf, int byte_val, char inst_data) {
	unsigned int bPos;
	incrementFaultSiteHit(fault_index);
	fault_site_count++;
	fault_site_intData8bit++;
	if(inject_once == 1)
		ijo_flag_data=1;
	if(ijo_flag_data == 1 && fault_injection_count>0)
		return inst_data;
	if(!shouldInject(ef, tf)) return inst_data;
	
	if(bit_position == -1)
		bPos = rand()%8;
	else if(bit_position < 8 && bit_position >= 0)
		bPos = bit_position;
	else return inst_data;
	
	fault_injection_count++;
	printFaultInfo("8-bit Int Data Error", bPos, fault_index, ef, tf);
	return (char)((inst_data & 0xFF) ^ (0x1 << bPos));   
}

short corruptIntData_16bit(int fault_index, int inject_once, int ef, int tf, int byte_val, short inst_data) {
	unsigned int bPos;
	incrementFaultSiteHit(fault_index);
	int rp;
	fault_site_count++;
	fault_site_intData16bit++;
	if(inject_once == 1)
		ijo_flag_data=1;
	if(ijo_flag_data == 1 && fault_injection_count>0)
		return inst_data;
	
	if(!shouldInject(ef, tf)) return inst_data;
                                         
	if(bit_position == -1)                                       
		bPos=rand() % 16;
	else if(bit_position >= 0 && bit_position < 16)
		bPos = bit_position;
	else
		return inst_data;

	fault_injection_count++;
	printFaultInfo("16-bit Int Data Error", bPos, fault_index, ef, tf);
	return (short)((inst_data & 0xFFFF) ^ (0x1 << bPos));   
}

int corruptIntData_32bit(int fault_index, int inject_once, int ef, int tf, int byte_val, int inst_data) {
	unsigned int bPos;
	incrementFaultSiteHit(fault_index);
	int rp;
	fault_site_count++;
	fault_site_intData32bit++;
	if(inject_once == 1)
		ijo_flag_data=1;

	if(ijo_flag_data == 1 && fault_injection_count>0)
		return inst_data;
	 
	if(!shouldInject(ef, tf)) return inst_data;
	
	if(bit_position == -1)
		bPos = rand() % 32;
	else if(bit_position >= 0 && bit_position < 32)
		bPos = bit_position;
	else
		return inst_data;
	
	fault_injection_count++;
	printFaultInfo("32-bit Int Data Error", bPos, fault_index, ef, tf);
	return (int)((inst_data & 0xFFFFFFFF) ^ (0x1 << bPos));   
}

float corruptFloatData_32bit(int fault_index, int inject_once, int ef, int tf, int byte_val, float inst_data) {
	unsigned int bPos;
	incrementFaultSiteHit(fault_index);
	int rp;
	fault_site_count++;
	fault_site_float32bit++;
	if(inject_once == 1)
		ijo_flag_data=1;

	if(ijo_flag_data == 1 && fault_injection_count>0)
		return inst_data;
	 
	if(!shouldInject(ef, tf)) return inst_data;

	if(bit_position == -1)
		bPos = rand() % 32;
	else if(bit_position >= 0 && bit_position < 32)
		bPos = bit_position;
	else
		return inst_data;
		
	fault_injection_count++;
	printFaultInfo("32-bit IEEE Float Data Error", bPos, fault_index, ef, tf);
	return (float)((int)inst_data ^ (0x1 << bPos));   
}

long long corruptIntData_64bit(int fault_index, int inject_once, int ef, int tf,  int byte_val, long long inst_data) {
	unsigned int bPos;
	incrementFaultSiteHit(fault_index);
	int rp;
	fault_site_count++;
	fault_site_intData64bit++;
	if(inject_once == 1)
		 ijo_flag_data=1;

	if(ijo_flag_data == 1 && fault_injection_count>0)
			 return inst_data;        
	 
	if(!shouldInject(ef, tf)) return inst_data;
	
	if(bit_position == -1)
		bPos = rand() % 64;
	else if(bit_position >= 0 && bit_position < 64)
		bPos = bit_position;
	else
		return inst_data;
	
	fault_injection_count++;
	printFaultInfo("64-bit Int Data Error", bPos, fault_index, ef, tf);
	return inst_data ^ (0x1L << bPos);   
}

double corruptFloatData_64bit(int fault_index, int inject_once, int ef, int tf,  int byte_val, double inst_data){
	unsigned int bPos;
	incrementFaultSiteHit(fault_index);
	int rp;
	fault_site_count++;
	fault_site_float64bit++;
	if(inject_once == 1)
		ijo_flag_data=1;

	if(ijo_flag_data == 1 && fault_injection_count>0)
		return inst_data;        

	if(!shouldInject(ef, tf)) return inst_data;
	
	if(bit_position == -1)
		bPos = rand() % 64;
	else if(bit_position >= 0 && bit_position < 64)
		bPos = bit_position;
	else
		return inst_data;
	
	fault_injection_count++;
	printFaultInfo("64-bit IEEE Float Data Error", bPos, fault_index, ef, tf);
	return (double)((long long)inst_data ^ (0x1L << bPos));   
}

int* corruptIntAdr_32bit(int fault_index, int inject_once, int ef, int tf,  int byte_val, int* inst_add){
	unsigned int bPos;
	incrementFaultSiteHit(fault_index);
	int rp;
	fault_site_count++;
	fault_site_adr++;
	if(inject_once == 1)
		ijo_flag_add=1;

	if(ijo_flag_add == 1 && fault_injection_count>0)
		return inst_add;           

	if(!shouldInject(ef, tf)) return inst_add;

	if(bit_position == -1)
		bPos = rand() % 64;
	else if(bit_position >= 0 && bit_position < 64)
		bPos = bit_position;
	else
		return inst_add;
	
	fault_injection_count++;

	printFaultInfo("Ptr32 Error", bPos, fault_index, ef, tf);
	return (int *)((long long)inst_add ^ (0x1L << bPos));   
}

long long* corruptIntAdr_64bit(int fault_index, int inject_once, int ef, int tf,  int byte_val, long long* inst_add){
	unsigned int bPos;
	incrementFaultSiteHit(fault_index);
	int rp;
	fault_site_count++;
	fault_site_adr++;
	if(inject_once == 1)
		ijo_flag_add=1;

	if(ijo_flag_add == 1 && fault_injection_count>0)
		return inst_add;           

	if(!shouldInject(ef, tf)) return inst_add;

	if(bit_position == -1)
		bPos = rand() % 64;
	else if(bit_position >= 0 && bit_position < 64)
		bPos = bit_position;
	else
		return inst_add;
	
	fault_injection_count++;

	printFaultInfo("Ptr64 Error", bPos, fault_index, ef, tf);
	return (long long *)((long long)inst_add ^ (0x1L << bPos));   
}

float* corruptFloatAdr_32bit(int fault_index, int inject_once, int ef, int tf,  int byte_val, float* inst_add){
	unsigned int bPos;
	incrementFaultSiteHit(fault_index);
	int rp;
	fault_site_count++;
	fault_site_adr++;
	if(inject_once == 1)
		ijo_flag_add=1;

	if(ijo_flag_add == 1 && fault_injection_count>0)
		return inst_add;           

	if(!shouldInject(ef, tf)) return inst_add;
	
	if(bit_position == -1)
		bPos = rand() % 64;
	else if(bit_position >= 0 && bit_position < 64)
		bPos = bit_position;
	else
		return inst_add;
	
	fault_injection_count++;

	printFaultInfo("Float Addr32 Error", bPos, fault_index, ef, tf);
	return (float *)((long long)inst_add ^ (0x1L << (bPos)));   
}

double* corruptFloatAdr_64bit(int fault_index, int inject_once, int ef, int tf,  int byte_val, double* inst_add){
	unsigned int bPos;
	incrementFaultSiteHit(fault_index);
	int rp;
	fault_site_count++;
	fault_site_adr++;
	if(inject_once == 1)
		ijo_flag_add=1;

	if(ijo_flag_add == 1 && fault_injection_count>0)
		return inst_add;           

	if(!shouldInject(ef, tf)) return inst_add;
	
	if(bit_position == -1)
		bPos = rand() % 64;
	else if(bit_position >= 0 && bit_position < 64)
		bPos = bit_position;
	else
		return inst_add;
	
	fault_injection_count++;
	printFaultInfo("Float Addr64 Error", bPos, fault_index, ef, tf);
	return (double *)((long long)inst_add ^ (0x1L << bPos));   
}

#ifdef __cplusplus
}
#endif
