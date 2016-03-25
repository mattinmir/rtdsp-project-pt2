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
#define TFRAME (float)FRAMEINC/FSAMP       /* time between calculation of each frame */




/* Number of frames that are compared per nmb candidate
 * (10 seconds/frame time)/number of nmb candidates
 */
#define QUARTER_FRAMES_PER_CAND 312//(int)(10.0/(float)TFRAME) // Not sure if cast to int is correct, will lose info -> significant? 
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

// Post-fft input
complex inframe_cmplx[FFTLEN];
// Pre-ifft output
complex outframe_cmplx[FFTLEN];

// Noise Minimum Buffer Candidates
float *m1;
float *m2;
float *m3;
float *m4;

// Noise Minimum Buffer
float *nmb;

// Counter to check when to rotate buffers 
int quarter_frames_processed = 0;

// Noise Floor
volatile float lambda = 0.06;
// Noise Estimate Coefficient
volatile float alpha = 2.5;
// Time constant for low pass filter
volatile float tau = 0.06;

// Low Pass Filter Coefficient 
float q;

// Controls Noise Subtraction
int noise_subtraction = 1;

// Suggested Optimisation Switches
int opt1 = 1; // LPF of X when calculating noise estimate
int opt2 = 1; // Modify opt1 do do calculation in power domain
int opt3 = 1; // LPF when calculating nmb value
int opt4 = 4; 	/*
					case 0:
					case 1:
					case 2: Requires opt1
					case 3: Requires opt1
					case 4: Requires opt1
				*/
int opt5 = 0;
int opt6 = 1;
int opt7 = 0;
int opt8 = 0;

// Self-suggested optimisations
int opta = 0;

// Iterator used in various for loops
int i;

// Stores absolute value of input
float magx;

// Arrays used in calculating low pass filters
float P[NMB_SIZE];
float P_prev[NMB_SIZE];
float nmb_prev[NMB_SIZE];

// Filter coefficient
float g;

/* For opt5*/
// For holding power domain values
float magxsq;
float nmbisq;
float Pisq;
// Used to scale alpha
float alpha_coef = 1;


float snr = 1;

/* For opt 8*/
// Holds previous, current, and next inputs
complex outframe_hist[3][FFTLEN] = {0};
// Index of the current input
int hist_index = 0;
int next, prev, curr;
// Perform optimisation when n/x is over this threshold
float thresh = 0.5;
unsigned int musical_noise[FFTLEN] = {0};

 /******************************* Function prototypes *******************************/
void init_hardware(void);    					/* Initialize codec */ 
void init_HWI(void);         				 	/* Initialize hardware interrupts */
void ISR_AIC(void);             				/* Interrupt service routine for codec */
void process_frame(void);       				/* Frame processing routine */
float min(float x, float y);					/* min of 2 real floats */ 
float max(float x, float y);					/* max of 2 real floats */
float lpf(float x, float lpf_prev[], int i);	/* lpf of array of samples */
complex cmin(complex x, complex y);				/* min of 2 complex values */
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
    m1			= (float *) calloc(NMB_SIZE, sizeof(float)); // nmb candidate 1
	m2			= (float *) calloc(NMB_SIZE, sizeof(float)); // nmb candidate 2
	m3			= (float *) calloc(NMB_SIZE, sizeof(float)); // nmb candidate 3
	m4			= (float *) calloc(NMB_SIZE, sizeof(float)); // nmb candidate 4
	nmb 		= (float *) calloc(NMB_SIZE, sizeof(float)); // Noise Minimum Buffer
	
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
	{
		 nmb[k] = m1[k] = m2[k] = m3[k] = m4[k] = FLT_MAX;
		 nmb_prev[k] = P_prev[k] = 0;					
	}
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
	int k, m; 
	int io_ptr0;   // index of samples
	
	float* temp;

	/* work out fraction of available CPU time used by algorithm */    
	// FRAMEINC-1 is 63, ANDing with io_ptr will repeat the output everytime io_ptr passes 64
	// essenstially doing io_ptr % FRAMEINC
	cpufrac = ((float) (io_ptr & (FRAMEINC - 1)))/FRAMEINC;  
	q = exp(-(float)TFRAME/tau);	
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
	if(noise_subtraction)
	{
		if(quarter_frames_processed == QUARTER_FRAMES_PER_CAND) 
		{		
			quarter_frames_processed = 0;

			
		/************ Rotate candidate pointers around  ***************/
			// m1 newest, m2 oldest
			temp = m1;
			m1 = m2;
			m2 = m3;
			m3 = m4;
			m4 = temp;
			
			// Re-initialise m1 with large values so that minimum magnitude values are fresh
			for(k = 0; k < NMB_SIZE; k++)
				m1[k] = FLT_MAX;
		}
		
		/***************** Applying fft ****************/ 
		
		// fft() takes a complex array as argument so create new array of complex structs
		// with input as the real part and 0 imaginary part
		for(i = 0; i < FFTLEN; i++)
			inframe_cmplx[i] = cmplx(inframe[i],0);
			
		fft(FFTLEN, inframe_cmplx);

		
		/************ Updating nmb candidates ***********/
		for(i = 0; i < NMB_SIZE; i++)	
		{	
			// Calculate magnitude of input
			magx = cabs(inframe_cmplx[i]);
			
			// Low pass filter the input
			if(opt1)
			{
				// Square magx to put in power domain
				if(opt2)
					magx *= magx;
				
				// Perform low pass filter	
				P[i] = lpf(magx, P_prev, i); 
				
				// Store value for next lpf equation
				P_prev[i] = P[i];
				
				// sqrt to bring back to time domain
				if(opt2)					
					P[i] = sqrt(P[i]);
			}
			else
				P[i] = magx;
			
			// Update candiate with the minimum of its current value and the input	
			m1[i] = min(P[i], m1[i]);
		}
		
		/********** Updating nmb from candidates ***********/
			
			// Find min value for each frequency bin from each candidate
			
			// Assuming OVERSAMP = 4
			for (i = 0; i < NMB_SIZE; i++)
			{				
				// Update nmb from candidates
				nmb[i] = alpha * min(min(m1[i], m2[i]), min(m3[i], m4[i]));
				
				// Attempt to attenuate all frequencies outside of human vocal range
				if(opta)
				{
					if(i >= 5 && i <= 57) // Bwetween 300 and 3500Hz
						nmb[i] /= 10000;
					else
						nmb[i] = FLT_MAX;
				}
				
					// Scale alpha inversely proportional to SNR
				if (opt6 && i < 20)
				{
					// x = y + n
					// x/n = y/n + 1
					// y^2/n^2 = (x/n - 1)^2
					magx = cabs(inframe_cmplx[i]);
					snr = (magx/nmb[i] - 1) * (magx/nmb[i] - 1);
				
					// -log increases with decreasing SNR
					// Cap at FLT_MAX as the function diverges to infinity
					alpha_coef = min(FLT_MAX, -log(snr)); 
					
					// Multiply by scaling factor and also prevent overflow
					nmb[i] = min(FLT_MAX, nmb[i]*alpha_coef);
				}	
					// Low pass filter the nmb using the previous value at that freq bin
				if(opt3)
				{
					nmb[i] = lpf(nmb[i], nmb_prev, i);
					nmb_prev[i] = nmb[i];
				}
			}
		
		// Increment counter, rotate candidates at QUARTER_FRAMES_PER_CAND count
		quarter_frames_processed++;		
		
		/********** Applying noise subtraction ***************/
		for (i = 0; i < FFTLEN; i++)
		{
			// Calculating square values for use in opt5, which overlfow check
			if(opt5)
			{
				magx = min(FLT_MAX, cabs(inframe_cmplx[i]));
				magxsq = min(FLT_MAX, magx*magx);
				nmbisq = min(FLT_MAX, nmb[i]*nmb[i]);
				Pisq = min(FLT_MAX, P[i]*P[i]);
			}
			
			// Different ways of calculating g (filter coefficient)
			switch(opt4)
			{
				case 0:
					// Calculate g in power domain
					if (opt5)
						g = max(lambda, sqrt(1-(nmbisq/magxsq)));
					else
						g = max(lambda, 1-(nmb[i]/magx));
					break;
				case 1:
					// Calculate g in power domain
					if(opt5)
						g = max(lambda*sqrt(nmbisq/magxsq), sqrt(1-(nmbisq/magxsq)));
					else 
						g = max(lambda*nmb[i]/magx, 1-(nmb[i]/magx));
					break;
				case 2:
					// Calculate g in power domain
					if(opt5)
						g = max(lambda*sqrt(Pisq/magxsq), sqrt(1-(nmbisq/magxsq)));
					else
						g = max(lambda*P[i]/magx, 1-(nmb[i]/magx));
					break;
				case 3: 
					// Calculate g in power domain
					if(opt5)
						g = max(lambda*sqrt(nmbisq/Pisq), sqrt(1-(nmbisq/Pisq)));
					else	
						g = max(lambda*nmb[i]/P[i], 1-(nmb[i]/P[i]));
					break;
				case 4:
					// Calculate g in power domain
					if(opt5)
						g = max(lambda, sqrt(1-(nmbisq/Pisq)));
					else	
						g = max(lambda, 1-(nmb[i]/P[i]));
					break;
			}
			
			// If there is muscial noise, replace that bin with the minimum of its neighbours
			// Delays output by a frame as wee need future data
			if(opt8)
			{
				// Enter this frame's data into the history
				outframe_hist[hist_index][i] = rmul(g, inframe_cmplx[i]);
				
				// If flag was set in previous cycle apply optimisation, else don't		
				if(musical_noise[i])
					outframe_cmplx[i] = cmin(outframe_hist[curr][i], cmin(outframe_hist[prev][i],outframe_hist[next][i]));
				else
					 outframe_cmplx[i] = outframe_hist[curr][i];
	
				// Sets flag for next cycle
				musical_noise[i] = (nmb[i]/cabs(inframe_cmplx[i]) > thresh);
			}
			
			// Apply filter to input to produce output
			else
				outframe_cmplx[i] = rmul(g, inframe_cmplx[i]);
		}
		
		// Increment hist_index with bounds check
		if (opt8)
		{
			hist_index = (hist_index == 2) ? 0 : hist_index + 1;
			
			//Getting index values for next/prev outputs and bounds checking
			next = hist_index;
			curr = (hist_index == 0) ? 2 : hist_index - 1;
			prev = (curr == 0) ? 2 : curr - 1;
		}
		
		ifft(FFTLEN, outframe_cmplx);
		
		// Ouput of ifft is still a complex array, so need to conver to a float array
		for(i= 0; i < FFTLEN; i++)
			outframe[i] = outframe_cmplx[i].r;
	}
	
	// For testing effect of noise subtraction 
	else
	{
		for (k=0;k<FFTLEN;k++)
		{                           
			outframe[k] = inframe[k];/* copy input straight into output */ 
		} 
	}
	/******************************************************************************************************************************/
	
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

complex cmin(complex x, complex y)
{
	return (cabs(x) <= cabs(y)) ? x : y;
}

float min(float x, float y)
{
	return (x <= y) ? x : y;
}

float max(float x, float y)
{
	return (x >= y) ? x : y;
}

float lpf(float x, float lpf_prev[], int i)
{
	return (1-q)*x + q*lpf_prev[i];
}
