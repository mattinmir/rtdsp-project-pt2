/*************************************************************************************
			       DEPARTMENT OF ELECTRICAL AND ELECTRONIC ENGINEERING
					   		     IMPERIAL COLLEGE LONDON 

 				      EE 3.19: Real Time Digital Signal Processing
					       Dr Paul Mitcheson and Daniel Harvey

				        		 PROJECT: Frame Processing

 				            ********* ENHANCE. C **********
							 Shell for speech enhancement 

  		Demonstrates overlap-add frame processing (interrupt driven) on the DSK. 

 *************************************************************************************
 				             By Danny Harvey: 21 July 2006
							 Updated for use on CCS v4 Sept 2010
 ************************************************************************************/
/*
 *	You should modify the code so that a speech enhancement project is built 
 *  on top of this template.
 */
/**************************** Pre-processor statements ******************************/
//  library required when using calloc
#include <stdlib.h>
//  Included so program can make use of DSP/BIOS configuration tool.  
#include "dsp_bios_cfg.h"

/* The file dsk6713.h must be included in every program that uses the BSL.  This 
   example also includes dsk6713_aic23.h because it uses the 
   AIC23 codec module (audio interface). */
#include "dsk6713.h"
#include "dsk6713_aic23.h"

// math library (trig functions)
#include <math.h>
#include <float.h>

/* Some functions to help with Complex algebra and FFT. */
#include "cmplx.h"      
#include "fft_functions.h"  

// Some functions to help with writing/reading the audio ports when using interrupts.
#include <helper_functions_ISR.h>

#define WINCONST 0.85185			/* 0.46/0.54 for Hamming window */
#define FSAMP 8000.0		/* sample frequency, ensure this matches Config for AIC */
#define FFTLEN 256					/* fft length = frame length 256/8000 = 32 ms*/
#define NFREQ (1+FFTLEN/2)			/* number of frequency bins from a real FFT */
#define OVERSAMP 4					/* oversampling ratio (2 or 4) */  
#define FRAMEINC (FFTLEN/OVERSAMP)	/* Frame increment */
#define CIRCBUF (FFTLEN+FRAMEINC)	/* length of I/O buffers */

#define OUTGAIN 16000.0				/* Output gain for DAC */
#define INGAIN  (1.0/16000.0)		/* Input gain for ADC  */
// PI defined here for use in your code 
#define PI 3.141592653589793
#define TFRAME FRAMEINC/FSAMP       /* time between calculation of each frame */




/* Number of frames that are compared per nmb candidate
 * (10 seconds/frame time)/number of nmb candidates
 */
#define QUARTER_FRAMES_PER_CAND (int)(10.0/(float)TFRAME) // Not sure if cast to int is correct, will lose info -> significant? 
#define NMB_SIZE FFTLEN
/******************************* Global declarations ********************************/

/* Audio port configuration settings: these values set registers in the AIC23 audio 
   interface to configure it. See TI doc SLWS106D 3-3 to 3-10 for more info. */
DSK6713_AIC23_Config Config = { \
			 /**********************************************************************/
			 /*   REGISTER	            FUNCTION			      SETTINGS         */ 
			 /**********************************************************************/\
    0x0017,  /* 0 LEFTINVOL  Left line input channel volume  0dB                   */\
    0x0017,  /* 1 RIGHTINVOL Right line input channel volume 0dB                   */\
    0x01f9,  /* 2 LEFTHPVOL  Left channel headphone volume   0dB                   */\
    0x01f9,  /* 3 RIGHTHPVOL Right channel headphone volume  0dB                   */\
    0x0011,  /* 4 ANAPATH    Analog audio path control       DAC on, Mic boost 20dB*/\
    0x0000,  /* 5 DIGPATH    Digital audio path control      All Filters off       */\
    0x0000,  /* 6 DPOWERDOWN Power down control              All Hardware on       */\
    0x0043,  /* 7 DIGIF      Digital audio interface format  16 bit                */\
    0x008d,  /* 8 SAMPLERATE Sample rate control        8 KHZ-ensure matches FSAMP */\
    0x0001   /* 9 DIGACT     Digital interface activation    On                    */\
			 /**********************************************************************/
};

// Codec handle:- a variable used to identify audio interface  
DSK6713_AIC23_CodecHandle H_Codec;
 
float *inbuffer, *outbuffer;   		/* Input/output circular buffers */
float *inframe, *outframe;          /* Input and output frames */
float *inwin, *outwin;              /* Input and output windows */
float ingain, outgain;				/* ADC and DAC gains */ 
float cpufrac; 						/* Fraction of CPU time used */
volatile int io_ptr=0;              /* Input/ouput pointer for circular buffers */ // index to each sample, not quarter frame
volatile int frame_ptr=0;           /* Frame pointer */ // index to quarter frame

complex inframe_cmplx[FFTLEN];
complex outframe_cmplx[FFTLEN];

float nmb_cands[NMB_SIZE*OVERSAMP]; // Noise Minimisation Buffer Candidates 
float nmb[NMB_SIZE];
int cands_index = 0 ;
int frames_processed = 0;

volatile float lambda = 0.1;
volatile float alpha = 20;
 /******************************* Function prototypes *******************************/
void init_hardware(void);    	/* Initialize codec */ 
void init_HWI(void);            /* Initialize hardware interrupts */
void ISR_AIC(void);             /* Interrupt service routine for codec */
void process_frame(void);       /* Frame processing routine */
float min(float x, float y);
float max(float x, float y);
/********************************** Main routine ************************************/
void main()
{      

  	int k; // used in various for loops
  
/*  Initialize and zero fill arrays */  

	inbuffer	= (float *) calloc(CIRCBUF, sizeof(float));	/* Input array */
    outbuffer	= (float *) calloc(CIRCBUF, sizeof(float));	/* Output array */
	inframe		= (float *) calloc(FFTLEN, sizeof(float));	/* Array for processing*/
    outframe	= (float *) calloc(FFTLEN, sizeof(float));	/* Array for processing*/
    inwin		= (float *) calloc(FFTLEN, sizeof(float));	/* Input window */
    outwin		= (float *) calloc(FFTLEN, sizeof(float));	/* Output window */
	
	/* initialize board and the audio port */
  	init_hardware();
  
  	/* initialize hardware interrupts */
  	init_HWI();    
  
/* initialize algorithm constants */  
                       
  	for (k=0;k<FFTLEN;k++)
	{                           
		inwin[k] = sqrt((1.0-WINCONST*cos(PI*(2*k+1)/FFTLEN))/OVERSAMP);
		outwin[k] = inwin[k]; 
	} 
  	ingain=INGAIN;
  	outgain=OUTGAIN;        
	
	for(k = 0; k < NMB_SIZE; k++)
		nmb[k] = FLT_MAX;
	for(k = 0; k < NMB_SIZE*OVERSAMP; k++)
		nmb_cands[k] = FLT_MAX;
	
 							
  	/* main loop, wait for interrupt */  
  	while(1) 	
  		process_frame();
}
    
/********************************** init_hardware() *********************************/  
void init_hardware()
{
    // Initialize the board support library, must be called first 
    DSK6713_init();
    
    // Start the AIC23 codec using the settings defined above in config 
    H_Codec = DSK6713_AIC23_openCodec(0, &Config);

	/* Function below sets the number of bits in word used by MSBSP (serial port) for 
	receives from AIC23 (audio port). We are using a 32 bit packet containing two 
	16 bit numbers hence 32BIT is set for  receive */
	MCBSP_FSETS(RCR1, RWDLEN1, 32BIT);	

	/* Configures interrupt to activate on each consecutive available 32 bits 
	from Audio port hence an interrupt is generated for each L & R sample pair */	
	MCBSP_FSETS(SPCR1, RINTM, FRM);

	/* These commands do the same thing as above but applied to data transfers to the 
	audio port */
	MCBSP_FSETS(XCR1, XWDLEN1, 32BIT);	
	MCBSP_FSETS(SPCR1, XINTM, FRM);	
	

}
/********************************** init_HWI() **************************************/ 
void init_HWI(void)
{
	IRQ_globalDisable();			// Globally disables interrupts
	IRQ_nmiEnable();				// Enables the NMI interrupt (used by the debugger)
	IRQ_map(IRQ_EVT_RINT1,4);		// Maps an event to a physical interrupt
	IRQ_enable(IRQ_EVT_RINT1);		// Enables the event
	IRQ_globalEnable();				// Globally enables interrupts

}
        
/******************************** process_frame() ***********************************/  
void process_frame(void)
{
	int k, m, i, new_cands_index; 
	int io_ptr0;   // index of samples
	float nmb_value, inframe_value;

	/* work out fraction of available CPU time used by algorithm */    
	// FRAMEINC-1 is 63, ANDing with io_ptr will repeat the output everytime io_ptr passes 64
	// essenstially doing io_ptr % FRAMEINC
	cpufrac = ((float) (io_ptr & (FRAMEINC - 1)))/FRAMEINC;  
		
	/* wait until io_ptr is at the start of the current frame */ 	
	while((io_ptr/FRAMEINC) != frame_ptr); 
	
	/* then increment the framecount (wrapping if required) */ 
	// CIRCBUF/FRAMEINC is no of quarter frames in buffer = 5
	if (++frame_ptr >= (CIRCBUF/FRAMEINC)) frame_ptr=0;
 	
 	/* save a pointer to the position in the I/O buffers (inbuffer/outbuffer) where the 
 	data should be read (inbuffer) and saved (outbuffer) for the purpose of processing */
 	// io_ptr0 set to a multiple of FRAMEINC (64) to know where to start writing outputs 
 	io_ptr0=frame_ptr * FRAMEINC;
	
	/* copy input data from inbuffer into inframe (starting from the pointer position) */ 
	 
	m=io_ptr0;
    for (k=0;k<FFTLEN;k++)
	{                           
		inframe[k] = inbuffer[m] * inwin[k]; // apply window and put into processing frame
		if (++m >= CIRCBUF) m=0; /* wrap if required */
	} 
	
/******************************** DO PROCESSING OF FRAME  HERE *******************************************************************/
	
	
	/***************** Applying fft ****************/ 
	for(i = 0; i < FFTLEN; i++)
		inframe_cmplx[i] = cmplx(inframe[i],0);
		
	fft (FFTLEN, inframe_cmplx);
	
	// For each frame you calculate the fft of, check each frequency bin's magnitude against the 
	// min values in the current 2.5sec candidate of min values. Swap values in if they are lower than the min.
	// After processing 2.5sec wortth of frames (1250/4), check between all 4 candidates to find the minimum for each
	// frequency bin. Put these values into the NMB.
	// Now these NMB values will be used to attenuate the output each cycle using the noise subtraction algorithm.
	
	
	// - inframe_cmplx has 256 elements but each NMB Candidate will have 129 (NFREQ) samples. How to compare them?
	// -> NFREQ is 129 because we disregard samples <0hz. So just use inframe_cmplx[127-255] and discard the rest
	
	/************ Updating nmb candidates ***********/
	for(i = 0; i < NMB_SIZE; i++)
	{
		// If cand value for that freq bin is higher than input frame value, replace the value
		
		// Find magnitude of frequency bin
		inframe_value = cabs(inframe_cmplx[i]);
		nmb_value = nmb_cands[cands_index + i];
		
		nmb_cands[cands_index + i] = min(inframe_value, nmb_value);
	}
	
	// Count number of frames processed so far so we know when to move to the next section
	// Wraparound when it has surpassed the size of the candidate buffer
	frames_processed++;
	frames_processed -= (frames_processed >= NMB_SIZE*OVERSAMP) ? NMB_SIZE*OVERSAMP : 0; // Check for wraparound
	
	// If frames_processed is between 0 and QUARTER_FRAMES_PER_CAND, then the for loop should be comparing with the first candidate,
	// so cands_index should start at the start of that candidate (index 0)
	// If it is between QUARTER_FRAMES_PER_CAND and 2*QUARTER_FRAMES_PER_CAND, it should be comparing with the second candidate, 
	// so cands_index should start at the start of that candidate (index NMB_SIZE)
	// And so on until the start of the last candidate 
	// This integer division will only return values in multiples of NMB_SIZE, ensuring it always starts at the right place
	new_cands_index = (frames_processed / QUARTER_FRAMES_PER_CAND) * NMB_SIZE ;
	
	// If we have moved to the next candidate, change the index, and reset the values in the candidate
	if(new_cands_index != cands_index)
	{
		cands_index = new_cands_index;
		
		// Check for wraparound
		cands_index -= (cands_index >= NMB_SIZE*OVERSAMP) ?  NMB_SIZE*OVERSAMP : 0;
		
		//Reset values
		for(k = cands_index; k < NMB_SIZE; k++)
			nmb_cands[k] = FLT_MAX;
	}
	
	
	
	/********** Updating nmb from candidates ***********/
	
	// Find min value for each frequency bin from each candidate
	
	// When OVERSAMP = 4
	for (i = 0; i < NMB_SIZE; i++)
	{
		nmb[i] = alpha * min(min(nmb_cands[i], nmb_cands[NMB_SIZE+i]), min(nmb_cands[2*NMB_SIZE+i], nmb_cands[3*NMB_SIZE+i]));
	}
	
	/********** Applying noise subtraction ***************/
	for (i = 0; i < FFTLEN; i++)
		outframe_cmplx[i] = rmul(max(lambda, 1-(nmb[i]/cabs(inframe_cmplx[i]) )), inframe_cmplx[i]);
	/*
	for (i = 0; i < FFTLEN; i++)
		outframe_cmplx[i] = inframe_cmplx[i];
	*/
	
	ifft(FFTLEN, outframe_cmplx);
	
	for(i= 0; i < FFTLEN; i++)
		outframe[i] = outframe_cmplx[i].r;
		

	
	
	
	/********************************************************************************/
	
    /* multiply outframe by output window and overlap-add into output buffer */   
                           
	m=io_ptr0;
    
    for (k=0;k<(FFTLEN-FRAMEINC);k++) 
	{    										/* this loop adds into outbuffer */                       
	  	outbuffer[m] = outbuffer[m]+outframe[k]*outwin[k];   
		if (++m >= CIRCBUF) m=0; /* wrap if required */
	}         
    for (;k<FFTLEN;k++) 
	{                           
		outbuffer[m] = outframe[k]*outwin[k];   /* this loop over-writes outbuffer */        
	    m++;
	}	                                   
}        
/*************************** INTERRUPT SERVICE ROUTINE  ******************************************************************/

// Map this to the appropriate interrupt in the CDB file
   
void ISR_AIC(void)
{       
	short sample;
	/* Read and write the ADC and DAC using inbuffer and outbuffer */
	
	sample = mono_read_16Bit();
	inbuffer[io_ptr] = ((float)sample)*ingain;
		/* write new output data */
	mono_write_16Bit((int)(outbuffer[io_ptr]*outgain)); 
	
	/* update io_ptr and check for buffer wraparound */    
	
	if (++io_ptr >= CIRCBUF) io_ptr=0;
}

/************************************************************************************/

float min(float x, float y)
{
	return (x <= y) ? x : y;
}

float max(float x, float y)
{
	return (x >= y) ? x : y;
}
