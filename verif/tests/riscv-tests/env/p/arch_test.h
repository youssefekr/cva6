// -----------
// Copyright (c) 2020-2023. RISC-V International. All rights reserved.
// SPDX-License-Identifier: BSD-3-Clause
// -----------


// This file is divided into the following sections:
//      RV Arch Test Constants
//      general test and helper macros, required,  optional, or just useful
//         _ARGn, SIG[BASE/UPD[_F/ID]],BASEUPD,BIT,LA ,LI,RVTEST_[INIT/SAVE]_GPRS, XCSR_RENAME
//      RV ARCH Test Interrupt Macros ****FIXME:spec which regs must not be altered
//      primary macros used by handle: RVTEST_TRAP{_PROLOG/_HANDLER/_EPILOG/SAVEAREA}
//      required test format spec macros:      RVTEST_{Code/DATA/SIG}{_BEGIN/_END}
//      macros from Andrew Waterman's risc-v test macros
//      deprecated macro name aliases, just for migration ease

//  The resulting memory layout of the trap handler is (MACRO_NAME, label [function])
//****************************************************************
//  (code section)
// RVMODEL_BOOT
//      rvtest_entry_point: [boot code]
// RVTEST_CODE_BEGIN
//      rvtest_init:       [TRAP_PROLOG]   (m, ms, or msv)
//                         [INIT_GPRS]
//      rvtest_code_begin:
//*****************************
//********(body of tests)******
//*****************************
// RVTEST_CODE_END
//      rvtest_code_end:   [*optional* SAVE_GPRS routine]
//                         [RVTEST_GOTO_MMODE ] **FIXME** this won't work if MMU enabled unless VA=PA
//      cleanup_epilogs    [TRAP_EPILOG   (m, ms, or msv)] (jump to exit_cleanup)
//                         [TRAP_HANDLER  (m, ms, or msv)]
//      exit_cleanup:      [RVMODEL_HALT macro or a branch to it.]
//
//--------------------------------this could start a new section--------------------------------
//  (Data section) - align to 4K boundary
// RVTEST_DATA_BEGIN
//**************************************
//*****(Ld/St test data is here)********
//**************************************
//
//**************************************
//*****(trap handler data is here)******
//**************************************
//
//    rvtest_trap_sig:   [global trap signature start (shared by all modes) inited to mtrap_sigptr] **FIXME: needs VA=PA
//    RVTEST_TRAP_SAVEAREA      [handler sv area(m, ms, or msv) temp reg save, CSRs, tramp table, ptrs]
//      rvtest_data_begin: [input data     (shared by all modes)]
//    RVTEST_DATA_END
//      rvtest_data_end:
//    RVTEST_ROOT_PG_TBL [sets up identity map (VA=PA)
//      sroot_pg_tbl:   (if smode)
//      vroot_pg_tbl:   (if hypervisor)
//--------------------------------this could start a new section--------------------------------
// RVTEST_SIG_BEGIN
//    RVMODEL_DATA_BEGIN
//      rvtest_sig_begin:  [beginning of signature, used by signature dump, can be used by tests]
//      mtrap_sigptr:      [global trap signature start (shared by all modes)] - defined by tests
//      gpr_save:          [gpr save area (optional, enabled if rvtest_gpr_save is defined)]
// RVTEST_SIG_END
//    rvtest_sig_end:   [global test   end signature (shared by all modes)] (shouldn't matter what RVMODEL_DATA_END does)
//    RVMODEL_DATA_END
//--------------------------------end of test--------------------------------

/* The following macros are optional if interrupt tests are enabled (defaulted if not defined):
        RVMODEL_SET_[M/V/S]_[SW]_INT
        RVMODEL_CLR_[M/V/S]_[SW/TIMTER/EXT]_INT
        rvtest_[M/V/S]trap_routine
        GOTO_[M/S/U]MODE, INSTANTIATE_MODE_MACRO (prolog/handler/epilog/savearea)
   The following macro is optional, and defaults to fence.i if not defined
        RVMODEL.FENCEI
   The following variables are used     if interrupt tests are enabled (defaulted if not defined):
         NUM_SPECD_INTCAUSES
   The following variables are optional if exception tests are enabled (defaulted if not defined):
         DATA_REL_TVAL_MSK     CODE_REL_TVAL_MSK
   The following variables are optional:
         rvtest_gpr_save: if defined, stores GPR contents into signature at test end (for debug)
   The following labels are required and defined by required macros:
          rvtest_code_begin:   defined by RVTEST_CODE_BEGIN  macro (boot code can precede this)
          rvtest_code_end:     defined by RVTEST_CODE_END    macro (trap handlers follow this)
          rvtest_data_begin:   defined by RVTEST_DATA_BEGIN  macro
          rvtest_data_end:     defined by RVTEST_DATA_END    macro
          rvtest_sig_begin:    defined by RVTEST_SIG_BEGIN   macro (after  RVMODEL_DATA_BEGIN) defines signature begin
          rvtest_sig_end:      defined by RVTEST_SIG_END     macro (before RVMODEL_DATA_END)   defines signature end
          rvtest_Sroot_pg_tbl: defined by RVTEST_PTE_IDENT_MAP macro inside RVTEST_DATA_BEGIN if  Smode implemented
          rvtest_Vroot_pg_tbl: defined by RVTEST_PTE_IDENT_MAP macro inside RVTEST_DATA_BEGIN if VSmode implemented
    labels/variables that must be defined by the DUT in model specific macros or #defines
           mtrap_sigptr:       defined by test if traps are possible, else is defaulted
*/
// don't put C-style macros (#define xxx) inside assembly macros; C-style is evaluated before assembly

#include "../encoding.h"
#include "test_macros.h"
#define RVTEST_ISA(_STR)         //empty macro used by framework

#define T1      x6
#define T2      x7
#define T3      x8
#define T4      x9
#define T5      x10
#define T6      x11

#define MIN(a,b) (((a)<(b))?(a):(b))
#define MAX(a,b) (((a)>(b))?(a):(b))
#define BIT(addr, bit) (((addr)>>(bit))&1)
#define MASK (((1<<(XLEN-1))-1) + (1<<(XLEN-1))) // XLEN bits of 1s

#define REGWIDTH   (XLEN>>3)     // in units of #bytes

#define WDSZ       32
#define WDSGN      (       WDSZ  -1)
#define WDMSK      ( (1 << WDSZ) -1)
#define SEXT_WRD(x)  ((x & WDMSK) | (-BIT((x), WRDSGN)<< WRDSZ))

#define IMMSZ      12
#define IMMSGN            (IMMSZ -1)
#define IMMMSK     ( (1 << IMMSZ)-1)

#define LIMMSZ     (WDSZ - IMMSZ)
#define LIMMSGN          (LIMMSZ -1)
#define LIMMMSK    ( (1 <<LIMMSZ)-1)
#define SEXT_LIMM(x) ((x &LIMMMSK) | (-BIT((x),LIMMSGN)<<LIMMSZ))

#define WDBYTSZ    (WDSZ >> 3)  // in units of #bytes
#define WDBYTMSK         (WDBYTSZ-1)

#define ALIGNSZ ((XLEN>>5)+2)   // log2(XLEN): 2,3,4 for XLEN 32,64,128
#if XLEN>FLEN
  #define SIGALIGN REGWIDTH
#else
  #define SIGALIGN FREGWIDTH
#endif

#ifndef RVMODEL_MTVEC_ALIGN
  #define MTVEC_ALIGN 6    // ensure that a trampoline is on a typical cacheline boundary, just in case
#else
  #define MTVEC_ALIGN RVMODEL_MTVEC_ALIGN  //Let the model defined value be used for required trap handler alignment based on implemented MTVEC
#endif

//==============================================================================
// this section has RV Arch Test Constants, mostly YAML based.
// It ensures they're defined  & defaulted if necessary)
//==============================================================================

// set defaults
#ifndef   NUM_SPECD_INTCAUSES
  #define NUM_SPECD_INTCAUSES 16
  #define INT_CAUSE_MSK ((1<<4)-1)
#endif

        // set defaults
#ifndef   NUM_SPECD_EXCPTCAUSES
  #define NUM_SPECD_EXCPTCAUSES 16
  #define EXCPT_CAUSE_MSK ((1<<4)-1)
#endif

//==========================================================================================
// By default, it is defined as nop for the implementation that does not support Zifencei
// Implementations that support Zifencei may use the fence.i instruction.
// This only gets executed if xTVEC is not writable to point to the trap trampoline, 
// and if it isn't writable, the model better have the zifencei extension implemented.
//==========================================================================================

#ifndef   RVMODEL_FENCEI
  #ifndef ZIFENCE
       #define RVMODEL_FENCEI nop
  #else                            
       #define RVMODEL_FENCEI fence.i 
    #endif
#endif

#ifndef UNROLLSZ
  #define UNROLLSZ 5
#endif

// **Note** that this is different that previous DATA_REL_TVAL_MASK! This is the OR of Code_Rel+Data_Rel
// if xTVAL is set to zero for some cause, then the corresponding bit in SET_REL_TVAL_MSK should be cleared

#ifndef SET_REL_TVAL_MSK
#define SET_REL_TVAL_MSK ((1<<CAUSE_MISALIGNED_FETCH | 1<<CAUSE_FETCH_ACCESS                             | 1<<CAUSE_BREAKPOINT   | \
                           1<<CAUSE_MISALIGNED_LOAD  | 1<<CAUSE_LOAD_ACCESS  | 1<<CAUSE_MISALIGNED_STORE | 1<<CAUSE_STORE_ACCESS | \
                           1<<CAUSE_FETCH_PAGE_FAULT | 1<<CAUSE_LOAD_PAGE_FAULT                          | 1<<CAUSE_STORE_PAGE_FAULT) \
                        & 0xFFFFFFFF)
#endif

#ifndef GOTO_M_OP
    #define GOTO_M_OP   ecall
#endif

//this is a valid global pte entry with all permissions. IF at the root entry, it forms an identity map.
#define RVTEST_PTE_IDENT_MAP  .fill   4096/REGWIDTH, REGWIDTH, (PTE_G | PTE_U | PTE_X | PTE_W | PTE_R | PTE_V)
#define RVTEST_PTE_NOACC_MAP  .fill   4096/REGWIDTH, REGWIDTH, (PTE_G | PTE_U )

//_ADDR_SZ_ is a global variable extracted from YAML; set a default if it isn't defined
// This should be the MAX(phy_addr_size, VADDR_SZ) from YAML, where VADDR_SZ is derived from SATP.mode at reset
#ifndef _ADDR_SZ_
  #if XLEN==64
    #define _ADDR_SZ_ 57
  #else
    #define _ADDR_SZ_ 32
  #endif
#endif

// define a bunch of XLEN dependent constants
#if   XLEN==32
    #define SREG sw
    #define LREG lw
    #define XLEN_WIDTH 5
    #define LREGWU lw
#elif XLEN==64
    #define SREG sd
    #define LREG ld
    #define XLEN_WIDTH 6
    #define LREGWU lwu
#else
    #define SREG sq
    #define LREG lq
    #define XLEN_WIDTH 7
#endif

#if FLEN==32
    #define FLREG flw
    #define FSREG fsw
    #define FREGWIDTH 4
#elif FLEN==64
    #define FLREG fld
    #define FSREG fsd
    #define FREGWIDTH 8
#else
    #define FLREG flq
    #define FSREG fsq
    #define FREGWIDTH 16
#endif


#if SIGALIGN==8
  #define CANARY \
      .dword 0x6F5CA309E7D4B281
#else
  #define CANARY \
      .word 0x6F5CA309 
#endif

//---------------------------mode encoding definitions-----------------------------
.set MMODE_SIG, 3
.set SMODE_SIG, 1
.set VMODE_SIG, 2
        /* these macros need to be defined because mode is uppercase in mode specific macros */
        /* note that vs mode uses smode return */

#define MPP_LSB   11    //bit pos of LSB of the mstatus.MPP field
#define MPP_SMODE  (1<<MPP_LSB)
#define MPV_LSB    7    // bit pos of prev vmod mstatush.MPV in either mstatush or upper half of mstatus
//define sizes
#define actual_tramp_sz ((XLEN + 3* NUM_SPECD_INTCAUSES + 5) * 4)     // 5 is added ops before common entry pt
#define tramp_sz        ((actual_tramp_sz+4) & -8)                     // round up to keep aligment
#define ptr_sv_sz       (16*8)
#define reg_sv_sz       ( 8*REGWIDTH)
#define sv_area_sz      (tramp_sz + ptr_sv_sz + reg_sv_sz)           // force dblword alignment
#define int_hndlr_tblsz (XLEN*2*WDBYTSZ)
/*
//#define sv_area_sz      (Msv_area_end-Mtramptbl_sv)           //sv_area start with aligned tramp_tbl
//#define tramp_sz        (((common_Mentry-Mtrampoline)+4)& -8) // #ops from Mend..Mentry, forced to dblword size
*/
//define a fixed offsets into the save area
#define tramp_sv_off                  ( 0*8)  // (Mtramptbl_sv    -Mtrapreg_sv) algned to dblwd

#define code_bgn_off         (tramp_sz+ 0*8)  // (Mcode_bgn_ptr   -Mtrapreg_sv)
#define code_seg_siz         (tramp_sz+ 1*8)  // (Mcode_seg_siz   -Mtrapreg_sv)
#define data_bgn_off         (tramp_sz+ 2*8)  // (Mdata_bgn_ptr   -Mtrapreg_sv)
#define data_seg_siz         (tramp_sz+ 3*8)  // (Mdata_seg_siz   -Mtrapreg_sv)
#define sig_bgn_off          (tramp_sz+ 4*8)  // ( Msig_bgn_ptr   -Mtrapreg_sv)
#define sig_seg_siz          (tramp_sz+ 5*8)  // ( Msig_seg_siz   -Mtrapreg_sv)
#define vmem_bgn_off         (tramp_sz+ 6*8)  // (Mvmem_bgn_ptr   -Mtrapreg_sv)
#define vmem_seg_siz         (tramp_sz+ 7*8)  // (Mvmem_seg_siz   -Mtrapreg_sv)

#define trapsig_ptr_off      (tramp_sz+ 8*8)  //  (Mtrap_sig      -Mtrapreg_sv)
#define xsatp_sv_off         (tramp_sz+ 9*8)  //  (Msatp_sv       -Mtrapreg_sv)
#define trampend_addr        (tramp_sz+10*8)  //  (Mtrampend_sv   -Mtrapreg_sv) 
#define tentry_addr          (tramp_sz+11*8) //   (Mtentry_sv     -Mtrapreg_sv) 
#define xedeleg_sv_off       (tramp_sz+12*8)  //  (Medeleg_sv     -Mtrapreg_sv)
#define xtvec_new_off        (tramp_sz+13*8)  //  (tvec_new       -Mtrapreg_sv)
#define xtvec_sav_off        (tramp_sz+14*8)  //  (tvec_save      -Mtrapreg_sv)
#define xscr_save_off        (tramp_sz+15*8)  //  (scratch_save   -Mtrapreg_sv)
#define trap_sv_off          (tramp_sz+16*8)  //  (trapreg_sv     -Mtrapreg_sv) 8 registers long

//==============================================================================
// this section has  general test helper macros, required,  optional, or just useful
//==============================================================================

#define _ARG5(_1ST,_2ND, _3RD,_4TH,_5TH,...) _5TH
#define _ARG4(_1ST,_2ND, _3RD,_4TH,...) _4TH
#define _ARG3(_1ST,_2ND, _3RD, ...) _3RD
#define _ARG2(_1ST,_2ND, ...) _2ND
#define _ARG1(_1ST,...) _1ST
#define NARG(...) _ARG5(__VA_OPT__(__VA_ARGS__,)4,3,2,1,0)
#define RVTEST_CASE(_PNAME,_DSTR,...)

//-----------------------------------------------------------------------
//Fixed length la, li macros; # of ops is ADDR_SZ dependent, not data dependent
//-----------------------------------------------------------------------

// this generates a constants using the standard addi or lui/addi sequences
// but also handles cases that are contiguous bit masks in any position,
// and also constants handled with the addi/lui/addi but are shifted left

/**** fixed length LI macro ****/
#if (XLEN<64)
  #define LI(reg, imm)                                                            ;\
  .set immx,    (imm & MASK)    /* trim to XLEN (noeffect on RV64)      */      ;\
  .set absimm,  ((immx^(-BIT(immx,XLEN-1)))&MASK) /* cvt to posnum to simplify code */  ;\
  .set cry,     (BIT(imm, IMMSGN))                                              ;\
  .set imm12,   (SEXT_IMM(immx))                                                ;\
  .if     ((absimm>>IMMSGN)==0) /* fits 12b signed imm (properly sgnext)? */    ;\
        li   reg, imm12         /* yes, <= 12bit, will be simple li       */    ;\
  .else                                                                         ;\
        lui  reg, (((immx>>IMMSZ)+cry) & LIMMMSK) /* <= 32b, use lui/addi */    ;\
    .if   ((imm&IMMMSK)!=0)     /* but skip this if lower bits are zero   */    ;\
        addi reg, reg, imm12                                                    ;\
    .endif                                                                      ;\
  .endif
  #else
#define LI(reg, imm)                                                            ;\
  .option push                                                                  ;\
  .option norvc                                                                 ;\
  .set immx,    (imm & MASK)    /* trim to XLEN (noeffect on RV64)      */      ;\
/***************** used in loop that detects bitmasks                   */      ;\
  .set edge1,   1               /* 1st "1" bit pos scanning r to l      */      ;\
  .set edge2,   0               /* 1st "0" bit pos scanning r to l      */      ;\
  .set fnd1,    -1              /* found 1st "1" bit pos scanning r to l */     ;\
  .set fnd2,    -1              /* found 1st "0" bit pos scanning r to l */     ;\
  .set imme,    ((immx^(-BIT(immx,0     )))&MASK) /* cvt to even, cvt back at end */    ;\
  .set pos,      0                                                              ;\
/***************** used in code that checks for 32b immediates          */      ;\
  .set absimm,  ((immx^(-BIT(immx,XLEN-1)))&MASK) /* cvt to posnum to simplify code */  ;\
  .set cry,     (BIT(immx, IMMSGN))                                             ;\
  .set imm12,   (SEXT_IMM(immx))                                                ;\
/***************** used in code that gnerates bitmasks                  */      ;\
  .set even,    (1-BIT(imm, 0)) /* imm has at least 1 trailing zero     */      ;\
  .set cryh,    (BIT(immx, IMMSGN+32))                                          ;\
/******** loop finding rising/falling edge fm LSB-MSB given even operand ****/  ;\
  .rept XLEN                                                                    ;\
    .if     (fnd1<0)            /* looking for first edge?              */      ;\
      .if (BIT(imme,pos)==1)    /* look for falling edge[pos]           */      ;\
        .set  edge1,pos         /* fnd falling edge, don’t chk for more */      ;\
	.set  fnd1,0                                                            ;\
      .endif                                                                    ;\
    .elseif (fnd2<0)            /* looking for second edge?             */      ;\
      .if (BIT(imme,pos)==0)    /* yes, found rising edge[pos]?         */      ;\
         .set  edge2, pos       /* fnd rising  edge, don’t chk for more */      ;\
	 .set  fnd2,0                                                           ;\
      .endif                                                                    ;\
    .endif                                                                      ;\
    .set    pos,  pos+1         /* keep looking (even if already found) */      ;\
  .endr                                                                         ;\
/***************** used in code that generates shifted 32b values       */      ;\
  .set immxsh, (immx>>edge1)    /* *sh variables only used if positive  */      ;\
  .set imm12sh,(SEXT_IMM(immxsh))/* look @1st 12b of shifted imm val    */      ;\
  .set crysh,     (BIT(immxsh, IMMSGN))                                         ;\
  .set absimmsh, immxsh         /* pos, no inversion needed, just shift */      ;\
/*******does it fit into std li or lui+li sequence****************************/ ;\
  .if     ((absimm>>IMMSGN)==0) /* fits 12b signed imm (properly sgnext)? */    ;\
        li   reg, imm12         /* yes, <= 12bit, will be simple li       */    ;\
  .elseif ((absimm+ (cry << IMMSZ) >> WDSGN)==0)/*fits 32b sgnimm?(w/ sgnext)?*/;\
        lui  reg, (((immx>>IMMSZ)+cry) & LIMMMSK) /* <= 32b, use lui/addi */    ;\
    .if   ((imm&IMMMSK)!=0)     /* but skip this if lower bits are zero   */    ;\
        addi reg, reg, imm12                                                    ;\
    .endif                                                                      ;\
 /*********** look for  0->1->0 masks, or inverse sgl/multbit *************/    ;\
  .elseif ( even && (fnd2<0))           /* only rising  edge, so 111000   */    ;\
        li      reg, -1                                                         ;\
        slli    reg, reg, edge1         /* make 111s --> 000s mask        */    ;\
  .elseif (!even && (fnd2<0))           /* only falling edge, so 000111   */    ;\
        li      reg, -1                                                         ;\
        srli    reg, reg, XLEN-edge1    /* make 000s --> 111s mask        */    ;\
  .elseif (imme == (1<<edge1))          /* check for single bit case      */    ;\
        li      reg, 1                                                          ;\
        slli    reg, reg, edge1         /* make 0001000 sgl bit mask      */    ;\
    .if   (!even)                                                               ;\
        xori    reg, reg, -1            /* orig odd, cvt to 1110111 mask  */    ;\
    .endif                                                                      ;\
  .elseif (imme == ((1<<edge2) - (1<<edge1))) /* chk for multibit case    */    ;\
        li      reg, -1                                                         ;\
        srli    reg, reg, XLEN-(edge2-edge1) /* make multibit 1s mask     */    ;\
        slli    reg, reg, edge1         /* and put it into position       */    ;\
    .if   (!even)                                                               ;\
        xori    reg, reg, -1            /* orig odd, cvt to 1110111 mask  */    ;\
    .endif                                                                      ;\
  /************** look for 12b or 32b imms with trailing zeroes ***********/    ;\
  .elseif ((immx==imme)&&((absimmsh>>IMMSGN)==0))/* fits 12b after shift? */    ;\
        li      reg, imm12sh            /* <= 12bit, will be simple li    */    ;\
        slli    reg, reg, edge1         /* add trailing zeros             */    ;\
  .elseif ((immx==imme)&&(((absimmsh>>WDSGN)+crysh)==0)) /* fits 32 <<shft? */  ;\
        lui     reg, ((immxsh>>IMMSZ)+crysh)&LIMMMSK /* <=32b, use lui/addi */  ;\
    .if   ((imm12sh&IMMMSK)!=0)         /* but skip this if low bits ==0  */    ;\
        addi    reg, reg, imm12sh                                               ;\
    .endif                                                                      ;\
        slli    reg, reg, edge1         /* add trailing zeros             */    ;\
  .else                                 /* give up, use fixed 8op sequence*/    ;\
  /******* TBD add sp case of zero short imms, rmv add/merge shifts  ******/    ;\
        lui     reg, ((immx>>(XLEN-LIMMSZ))+cryh)&LIMMMSK /* 1st 20b (63:44) */ ;\
        addi    reg, reg, SEXT_IMM(immx>>32)            /* nxt 12b (43:32) */   ;\
        slli    reg, reg, 11    /* following are <12b, don't need SEXT     */   ;\
        addi    reg, reg, (immx>>21) & (IMMMSK>>1)      /* nxt 11b (31:21) */   ;\
        slli    reg, reg, 11                            /* mk room for 11b */   ;\
        addi    reg, reg, (immx>>10) & (IMMMSK>>1)      /* nxt 11b (20:10) */   ;\
        slli    reg, reg, 10                            /* mk room for 10b */   ;\
    .if   ((imm&(IMMMSK>>2))!=0) /* but skip this if lower bits are zero   */   ;\
        addi    reg, reg, (immx)     & (IMMMSK>>2)      /* lst 10b (09:00) */   ;\
    .endif                                                                      ;\
    .if (XLEN==32)                                                              ;\
        .warning "Should never get here for RV32"                               ;\
    .endif                                                                      ;\
 .endif                                                                         ;\
 .option pop
 #endif

/**** fixed length LA macro; alignment and rvc/norvc unknown before execution ****/
#define LA(reg,val)     ;\
        .option push    ;\
        .option rvc     ;\
        .align UNROLLSZ ;\
        .option norvc   ;\
        la reg,val      ;\
        .align UNROLLSZ ;\
        .option pop

#define ADDI(dst, src, imm) /* helper*/ ;\
.if (imm<2048 && imm >=-2048)                         ;\
        addi    dst, src, imm           ;\
.else                                   ;\
        LI(     dst, imm)               ;\
        add    dst, src, dst           ;\
.endif

