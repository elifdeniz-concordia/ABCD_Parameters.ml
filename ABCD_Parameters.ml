
(* ===============================================================*)
(*                                                                *)
(*    Formalization of ABCD Parameters and Transmission Lines     *)
(*                                                                *)
(*        (c) Copyright, Adnan Rashid* & Elif Deniz*              *)
(*                                                                *)
(*                   *Hardware Verification Group,                *)
(*         Department of Electrical and Computer Engineering      *)
(*                        Concordia University                    *) 
(*                        Montreal, Canada                        *)
(*                                                                *)
(*                                                                *)
(*           Contact:   *<e_deniz@encs.concordia.ca>              *) 
(*                       *<rashid@encs.concordia.ca>              *)
(*                                                                *)
(* ============================================================== *)

(*===================== Theories to load==========================*)

needs "Multivariate/cauchy.ml";;
needs "Multivariate/cmatrix.ml";;


let tl_models_IND,tl_models_REC = define_type
                          "tl_models = ShortTL_SerImp |
                                       ShortTL_ShuAdm |
                                       MediumTL_TCir |
                                       MediumTL_PiCir ";;

(* ------------------------------------------------------------------------- *)
(* For the above type definition HOL Light auotmatically proves two theorems *)
(* ------------------------------------------------------------------------- *)

(*---------------------------------------------------------------------------*)
(*         Theorem 1 (Transmission Lines `tl_models` Induction)              *)
(*---------------------------------------------------------------------------*)

|- !P. P ShortTL_SerImp /\
         P ShortTL_ShuAdm /\
         P MediumTL_TCir /\
         P MediumTL_PiCir
         ==> (!x. P x)

g `!P. P ShortTL_SerImp /\
         P ShortTL_ShuAdm /\
         P MediumTL_TCir /\
         P MediumTL_PiCir
         ==> (!x. P x)`;;

e (SIMP_TAC [tl_models_IND]);;

let TL_MODELS_IND = top_thm ();;

(*---------------------------------------------------------------------------*)
(*         Theorem 2 (Transmission Lines `tl_models` Recursion)              *)
(*---------------------------------------------------------------------------*)

|- !f0 f1 f2 f3.
         ?fn. fn ShortTL_SerImp = f0 /\
              fn ShortTL_ShuAdm = f1 /\
              fn MediumTL_TCir = f2 /\
              fn MediumTL_PiCir = f3


g `!f0 f1 f2 f3.
         ?fn. fn ShortTL_SerImp = f0 /\
              fn ShortTL_ShuAdm = f1 /\
              fn MediumTL_TCir = f2 /\
              fn MediumTL_PiCir = f3`;;

e (SIMP_TAC [tl_models_REC]);;

let TL_MODELS_REC = top_thm ();;

(*--------------------------------------------------------------------------*)

new_type_abbrev ("vol_fun",`:(complex -> complex)`);;
new_type_abbrev ("cur_fun",`:(complex -> complex)`);;
new_type_abbrev ("comp_vec",`:(complex^2)`);;
new_type_abbrev ("comp_mat",`:(complex^2^2)`);;

new_type_abbrev ("R",`:real`);;
new_type_abbrev ("L",`:real`);;
new_type_abbrev ("Ca",`:real`);;
new_type_abbrev ("G",`:real`);;
new_type_abbrev 
     ("trans_lines_const",`:R # L # Ca # G`);;
     
new_type_abbrev ("A",`:complex`);;
new_type_abbrev ("B",`:complex`);;
new_type_abbrev ("C",`:complex`);;
new_type_abbrev ("D",`:complex`);;
new_type_abbrev 
     ("abcd_param",`:A # B # C # D`);;

new_type_abbrev ("Vs",`:vol_fun`);;
new_type_abbrev ("Is",`:cur_fun`);;
new_type_abbrev ("send_end_quan",`:Vs # Is`);;

new_type_abbrev ("VR",`:vol_fun`);;
new_type_abbrev ("IR",`:cur_fun`);;
new_type_abbrev ("recei_end_quan",`:VR # IR`);;

new_type_abbrev ("send_recei_quan",`:send_end_quan # recei_end_quan`);;

(*---------------------------------------------------------------------------*)
(*                Forall (∀) Theorems for Type Abbreviations                 *)
(*---------------------------------------------------------------------------*)

let FORALL_TL_CONST_THM = prove
  (`!P. (!tlc:trans_lines_const. P tlc) <=> !R L CA G. P (R,L,CA,G)`,
  REWRITE_TAC[FORALL_PAIR_THM]);;

let EXISTS_TL_CONST_THM = prove
  (`!P. (?tlc:trans_lines_const. P tlc) <=> ?R L Ca G. P (R,L,Ca,G)`,
  REWRITE_TAC[EXISTS_PAIR_THM]);;

let FORALL_ABCD_PARAM_THM = prove
  (`!P. (!tlp:abcd_param. P tlp) <=> !A B C D. P (A,B,C,D)`,
  REWRITE_TAC[FORALL_PAIR_THM]);;

let EXISTS_ABCD_PARAM_THM = prove
  (`!P. (?tlp:abcd_param. P tlp) <=> ?A B C D. P (A,B,C,D)`,
  REWRITE_TAC[EXISTS_PAIR_THM]);;

let FORALL_SEND_END_QUAN_THM = prove
  (`!P. (!seq:send_end_quan. P seq) <=> !Vs Is. P (Vs,Is)`,
  REWRITE_TAC[FORALL_PAIR_THM]);;

let EXISTS_SEND_END_QUAN_THM = prove
  (`!P. (?seq:send_end_quan. P seq) <=> ?Vs Is. P (Vs,Is)`,
  REWRITE_TAC[EXISTS_PAIR_THM]);;

let FORALL_RECEI_END_QUAN_THM = prove
  (`!P. (!req:send_end_quan. P req) <=> !VR IR. P (VR,IR)`,
  REWRITE_TAC[FORALL_PAIR_THM]);;

let EXISTS_RECEI_END_QUAN_THM = prove
  (`!P. (?req:send_end_quan. P req) <=> ?VR IR. P (VR,IR)`,
  REWRITE_TAC[EXISTS_PAIR_THM]);;

(*---------------------------------------------------------------------------*)
(*           General Relationship between
                                the sending and receiving quantities         *)
(*---------------------------------------------------------------------------*)

let send_end_vec = new_definition `
    send_end_vec ((Vs,Is):send_end_quan) z = 
        vector [Vs z; Is z]:comp_vec`;;

let recei_end_vec = new_definition `
    recei_end_vec ((VR,IR):recei_end_quan) z = 
        vector [VR z; IR z]:comp_vec`;;

let abcd_mat_gen = new_definition `
    abcd_mat_gen ((A,B,C,D):abcd_param) = 
        ((vector [vector [A;B]; vector [C;D]]):comp_mat)`;;

let relat_send_receiv_quan_gen = new_definition `
    relat_send_receiv_quan_gen ((Vs,Is):send_end_quan)
            ((VR,IR):recei_end_quan) ((A,B,C,D):abcd_param) z =
       ((send_end_vec ((Vs,Is):send_end_quan) z) =
          ((abcd_mat_gen ((A,B,C,D):abcd_param)):comp_mat) ** 
                      (recei_end_vec ((VR,IR):recei_end_quan) z))`;;

(*---------------------------------------------------------------------------*)
(*                Definition (Valid Transmission Line Constants)             *)
(*---------------------------------------------------------------------------*)   
       
let valid_tl_const = new_definition `
    valid_tl_const 
        ((R,L,Ca,G):trans_lines_const) = 
                  ((&0 < R) /\ (&0 < L) /\ (&0 < Ca) /\ (&0 < G))`;;

(*---------------------------------------------------------------------------*)
(*                Definition (Valid Transmission Line Model)                 *)
(*---------------------------------------------------------------------------*)   

let valid_transm_line_model1a = define
  `(valid_transm_line_model1a (ShortTL_SerImp) <=> T) /\
   (valid_transm_line_model1a (ShortTL_ShuAdm) <=> T) /\
   (valid_transm_line_model1a (MediumTL_TCir) <=> T) /\
   (valid_transm_line_model1a (MediumTL_PiCir) <=> T)`;;

(*---------------------------------------------------------------------------*)
(*               Definition (Valid Transmission Line)                        *)
(*---------------------------------------------------------------------------*) 
   
let valid_transmission_line = new_definition
  `valid_transmission_line (tlm,tlc) <=>
    valid_transm_line_model1a tlm /\ valid_tl_const tlc`;;

(*---------------------------------------------------------------------------*)
(*              Formalization of kcl and kvl in frequency domain             *)
(*---------------------------------------------------------------------------*)

let kcl = new_definition `
    kcl (cur_list:cur_fun list) (z:complex) =
	  ((vsum (0..(LENGTH (cur_list) - 1)) (\n. EL n cur_list z)) = Cx (&0))`;;

let kvl = new_definition `
    kvl (vol_list:vol_fun list) (z:complex) =
	  ((vsum (0..(LENGTH (vol_list) - 1)) (\n. EL n vol_list z)) = Cx (&0))`;;

(*---------------------------------------------------------------------------*)
(*           Component models in Phasor domain (frequency domain)            *)
(*---------------------------------------------------------------------------*)

let resis_volt = new_definition 
    	     `resis_volt (R:real) (Ir:cur_fun) = (\z. Ir z * Cx R)`;;

let conductr = new_definition 
    	     `conductr (R:real) = Cx (&1 / R)`;;

let resis_curr = new_definition 
    	     `resis_curr (R:real) (V:vol_fun) = (\z. V z * conductr R)`;;

let induct_volt = new_definition
      `induct_volt (L:real) (w:real) (Il:cur_fun) =
                                  (\z. ii * Cx w * Cx L * (Il z))`;;

let series_imped_volt = new_definition
      `series_imped_volt (R:real) (L:real) (w:real) (Isi:cur_fun) =
                   (\z. (resis_volt R Isi) z + (induct_volt L w Isi) z)`;;

let induct_curr = new_definition
      `induct_curr (V:vol_fun) (L:real) (w:real) = 
                       (\z. (Cx (&1) / (ii * Cx w * Cx L)) * (V z))`;;

let capacit_volt = new_definition
      `capacit_volt (Ic:vol_fun) (C:real) (w:real) = 
                       (\z. (Cx (&1) / (ii * Cx w * Cx C)) * (Ic z))`;;

let capacit_curr = new_definition
      `capacit_curr (V:vol_fun) (C:real) (w:real) = 
                                  (\z. ii * Cx w * Cx C * (V z))`;;
				  
let shunt_admit_curr = new_definition
      `shunt_admit_curr (R:real) (Ca:real) (w:real) (Vsa:vol_fun) =
                   (\z. (resis_curr R Vsa) z + (capacit_curr Vsa Ca w) z)`;;

(*---------------------------------------------------------------------------*)
(*                         Helping Theorems/Lemmas                           *)
(*---------------------------------------------------------------------------*)

let THREE = 
	prove (`3  = SUC 2`, ARITH_TAC);;

let FOUR = 
	prove (`4  = SUC 3`, ARITH_TAC);;
	
let FIVE = 
	prove (`5  = SUC 4`, ARITH_TAC);;
	
let SIX = 
	prove (`6  = SUC 5`, ARITH_TAC);;
	
let SEVEN = 
	prove (`7  = SUC 6`, ARITH_TAC);;
	
let EIGHT = 
	prove (`8  = SUC 7`, ARITH_TAC);;
	

let VSUM_2_LIST = prove(
`!f1 f2 z. vsum (0..1) (\n. EL n [(f1:complex->complex); f2] z) = f1 z + f2 z`,

REPEAT GEN_TAC THEN
 ONCE_REWRITE_TAC [ONE] THEN REWRITE_TAC [VSUM_CLAUSES_NUMSEG]
  THEN SIMP_TAC [EL; TL; HD] THEN SUBGOAL_THEN ` 0 <= SUC 0` ASSUME_TAC THENL [ARITH_TAC;ALL_TAC]
  THEN ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC));;

let VSUM_3_LIST = prove (
  `!f1 f2 f3 z.
        vsum (0..2) (\n. EL n [(f1:complex->complex); f2; f3] z) = f1 z + f2 z + f3 z`,

 REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [TWO] THEN REWRITE_TAC [VSUM_CLAUSES_NUMSEG] THEN
  SIMP_TAC [EL; TL] THEN SUBGOAL_THEN ` 0 <= SUC 1` ASSUME_TAC THENL [ARITH_TAC;ALL_TAC] THEN 
   ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN ONCE_REWRITE_TAC [ONE] THEN SIMP_TAC [EL;TL;HD]
   THEN SUBGOAL_THEN ` 0 <= SUC 0` ASSUME_TAC THENL [ARITH_TAC;ALL_TAC] THEN
     ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN REWRITE_TAC [VSUM_CLAUSES_NUMSEG] THEN
   SUBGOAL_THEN ` 0 <= SUC 0` ASSUME_TAC THENL [ARITH_TAC;ALL_TAC] THEN
    ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
     SIMP_TAC [EL;TL;HD] THEN CONV_TAC COMPLEX_FIELD);;


let VSUM_4_LIST = prove(
 `!f1 f2 f3 f4 z.
        vsum (0..3) (\n. EL n [(f1:complex->complex); f2; f3; f4] z) = f1 z + f2 z + f3 z + f4 z`,

 REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [THREE]
   THEN REWRITE_TAC [VSUM_CLAUSES_NUMSEG] THEN SIMP_TAC [EL; TL] THEN
    SUBGOAL_THEN ` 0 <= SUC 2` ASSUME_TAC THENL [ARITH_TAC;ALL_TAC]
   THEN ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
    ONCE_REWRITE_TAC [TWO] THEN SIMP_TAC [EL;TL;HD] THEN REWRITE_TAC [VSUM_CLAUSES_NUMSEG]
    THEN SUBGOAL_THEN ` 0 <= SUC 1` ASSUME_TAC THENL [ARITH_TAC;ALL_TAC]
    THEN ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
     SIMP_TAC [EL;TL;HD] THEN ONCE_REWRITE_TAC [ONE] THEN SIMP_TAC [EL;TL;HD]
   THEN SUBGOAL_THEN ` 0 <= SUC 0` ASSUME_TAC THENL [ARITH_TAC;ALL_TAC]
    THEN ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) 
      THEN REWRITE_TAC [VSUM_CLAUSES_NUMSEG] THEN
   SUBGOAL_THEN ` 0 <= SUC 0` ASSUME_TAC THENL [ARITH_TAC;ALL_TAC] THEN
    ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN SIMP_TAC [EL;TL;HD] THEN
     CONV_TAC COMPLEX_FIELD);;

let VSUM_5_LIST = prove(
 `!f1 f2 f3 f4 f5 z.
        vsum (0..4) (\n. EL n [(f1:complex->complex); f2; f3; f4; f5] z) = 
                                             f1 z + f2 z + f3 z + f4 z + f5 z`,

REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [FOUR] THEN
  REWRITE_TAC [VSUM_CLAUSES_NUMSEG] THEN SIMP_TAC [EL; TL] THEN
   SUBGOAL_THEN ` 0 <= SUC 3` ASSUME_TAC THENL [ARITH_TAC;ALL_TAC]
   THEN ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC)
   THEN ONCE_REWRITE_TAC [THREE] THEN SIMP_TAC [EL;TL;HD] 
   THEN REWRITE_TAC [VSUM_CLAUSES_NUMSEG] THEN
    SUBGOAL_THEN ` 0 <= SUC 2` ASSUME_TAC THENL [ARITH_TAC;ALL_TAC] THEN 
    ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
    ONCE_REWRITE_TAC [TWO] THEN SIMP_TAC [EL;TL;HD] THEN
     REWRITE_TAC [VSUM_CLAUSES_NUMSEG] THEN 
   SUBGOAL_THEN ` 0 <= SUC 1` ASSUME_TAC THENL [ARITH_TAC;ALL_TAC]
   THEN ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN SIMP_TAC [EL;TL;HD] THEN
    ONCE_REWRITE_TAC [ONE] THEN SIMP_TAC [EL;TL;HD] THEN
     SUBGOAL_THEN ` 0 <= SUC 0` ASSUME_TAC THENL [ARITH_TAC;ALL_TAC]
     THEN ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
   REWRITE_TAC [VSUM_CLAUSES_NUMSEG] THEN SUBGOAL_THEN ` 0 <= SUC 0` ASSUME_TAC
     THENL [ARITH_TAC;ALL_TAC] THEN 
   ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN SIMP_TAC [EL;TL;HD] THEN
    CONV_TAC COMPLEX_FIELD);;

let VSUM_6_LIST = prove (
 `!f1 f2 f3 f4 f5 f6 z.
        vsum (0..5) (\n. EL n [(f1:complex->complex); f2; f3; f4; f5; f6] z) =
	                              f1 z + f2 z + f3 z + f4 z + f5 z + f6 z`,

REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [FIVE] THEN
REWRITE_TAC [VSUM_CLAUSES_NUMSEG] THEN SIMP_TAC [EL; TL] THEN
SUBGOAL_THEN ` 0 <= SUC 4` ASSUME_TAC THENL [ARITH_TAC;ALL_TAC]
 THEN ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
  ONCE_REWRITE_TAC [FOUR] THEN REWRITE_TAC [VSUM_CLAUSES_NUMSEG] THEN 
   SIMP_TAC [EL; TL] THEN SUBGOAL_THEN ` 0 <= SUC 3` ASSUME_TAC THENL [ARITH_TAC;ALL_TAC]
   THEN ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN ONCE_REWRITE_TAC [THREE] THEN
   SIMP_TAC [EL;TL;HD] THEN REWRITE_TAC [VSUM_CLAUSES_NUMSEG] THEN 
    SUBGOAL_THEN ` 0 <= SUC 2` ASSUME_TAC THENL [ARITH_TAC;ALL_TAC] THEN
   ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
    ONCE_REWRITE_TAC [TWO] THEN SIMP_TAC [EL;TL;HD] THEN
    REWRITE_TAC [VSUM_CLAUSES_NUMSEG] THEN 
     SUBGOAL_THEN ` 0 <= SUC 1` ASSUME_TAC THENL [ARITH_TAC;ALL_TAC]
  THEN ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
   SIMP_TAC [EL;TL;HD] THEN ONCE_REWRITE_TAC [ONE] THEN
    SIMP_TAC [EL;TL;HD] THEN
    SUBGOAL_THEN ` 0 <= SUC 0` ASSUME_TAC THENL [ARITH_TAC;ALL_TAC]
    THEN ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
     REWRITE_TAC [VSUM_CLAUSES_NUMSEG] THEN
      SUBGOAL_THEN ` 0 <= SUC 0` ASSUME_TAC THENL [ARITH_TAC;ALL_TAC]
      THEN ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
       SIMP_TAC [EL;TL;HD] THEN CONV_TAC COMPLEX_FIELD);;


let VSUM_8_LIST = prove(
`!f1 f2 f3 f4 f5 f6 f7 f8 z.
        vsum (0..7) (\n. EL n [(f1:complex->complex); f2; f3; f4; f5; f6; f7; f8] z) =
	                      f1 z + f2 z + f3 z + f4 z + f5 z + f6 z + f7 z + f8 z`,

REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC [SEVEN] THEN
 REWRITE_TAC [VSUM_CLAUSES_NUMSEG] THEN
  SIMP_TAC [EL; TL] THEN  SUBGOAL_THEN ` 0 <= SUC 6` ASSUME_TAC THENL [ARITH_TAC;ALL_TAC]
  THEN ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN ONCE_REWRITE_TAC [SIX]
  THEN REWRITE_TAC [VSUM_CLAUSES_NUMSEG] THEN SIMP_TAC [EL; TL] THEN
  SUBGOAL_THEN ` 0 <= SUC 5` ASSUME_TAC THENL [ARITH_TAC;ALL_TAC] THEN
    ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN ONCE_REWRITE_TAC [FIVE] THEN
     REWRITE_TAC [VSUM_CLAUSES_NUMSEG] THEN SIMP_TAC [EL; TL] THEN
      SUBGOAL_THEN ` 0 <= SUC 4` ASSUME_TAC THENL [ARITH_TAC;ALL_TAC] THEN
  ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN ONCE_REWRITE_TAC [FOUR] THEN 
   REWRITE_TAC [VSUM_CLAUSES_NUMSEG] THEN SIMP_TAC [EL; TL] THEN
    SUBGOAL_THEN ` 0 <= SUC 3` ASSUME_TAC THENL [ARITH_TAC;ALL_TAC] THEN
  ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN ONCE_REWRITE_TAC [THREE] THEN
   SIMP_TAC [EL;TL;HD] THEN REWRITE_TAC [VSUM_CLAUSES_NUMSEG] THEN
    SUBGOAL_THEN ` 0 <= SUC 2` ASSUME_TAC THENL [ARITH_TAC;ALL_TAC] THEN
  ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN ONCE_REWRITE_TAC [TWO]
  THEN SIMP_TAC [EL;TL;HD] THEN REWRITE_TAC [VSUM_CLAUSES_NUMSEG]
  THEN SUBGOAL_THEN ` 0 <= SUC 1` ASSUME_TAC THENL [ARITH_TAC;ALL_TAC]
  THEN ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN SIMP_TAC [EL;TL;HD]
  THEN ONCE_REWRITE_TAC [ONE] THEN SIMP_TAC [EL;TL;HD] THEN
  SUBGOAL_THEN ` 0 <= SUC 0` ASSUME_TAC THENL [ARITH_TAC;ALL_TAC]
  THEN ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN REWRITE_TAC [VSUM_CLAUSES_NUMSEG]
  THEN SUBGOAL_THEN ` 0 <= SUC 0` ASSUME_TAC THENL [ARITH_TAC;ALL_TAC] THEN
   ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
   SIMP_TAC [EL;TL;HD] THEN CONV_TAC COMPLEX_FIELD);;

 
let VEC_MAT_SIMP_TAC xs =
  SIMP_TAC (xs @ [CART_EQ;VECTOR_1;VECTOR_2;VECTOR_3;VECTOR_4; 
                       DIMINDEX_1;DIMINDEX_2;DIMINDEX_3;DIMINDEX_4;
                         FORALL_1; FORALL_2;FORALL_3;FORALL_4;
			  DOT_1; DOT_2;DOT_3;DOT_4;
                           SUM_1;SUM_2;SUM_3;SUM_4]);;

let MAT2x2_MUL_VEC2 = prove (
 `!x y (a:complex) b c d.
    ((vector [vector [a; b]; vector [c; d]]):complex^2^2) ** vector [x; y] =
    vector [a * x + b * y ; c * x + d * y]`,

REPEAT GEN_TAC THEN CVEC_CMAT_SIMP_TAC [CMATRIX_CVECTOR_MUL_COMPONENT]
  THEN CCOMMON_TAC [CMATRIX_CVECTOR_MUL_COMPONENT]);;


let CMAT_TAC xs =
  SIMP_TAC (xs @ [CART_EQ;VECTOR_2;DIMINDEX_2;FORALL_2;CMULT_2;SUM_2] );;

let CVECTOR2_EQ = prove
  (`!x y z t. vector [x ;y] :complex^2 = vector [z;t] <=> x=z /\ y=t`,
  CMAT_TAC[]);;


(*---------------------------------------------------------------------------*)
(*                 All Transmission Lines KVL Implementations                *)
(*---------------------------------------------------------------------------*)

let admit_curr_med = new_definition
      `admit_curr_med (V:vol_fun) (C:real) (w:real) = 
                                  (\z. Cx w * (Cx C / Cx (&2)) * (V z))`;;

let imped_volt_med = new_definition
      `imped_volt_med (Iz:vol_fun) (R:real) (L:real) (w:real) = 
                                  (\z. ((Cx R + ii * Cx w * Cx L) / Cx (&2)) * (Iz z))`;;


let kvl_implem_1a = define `
   (kvl_implem_1a ShortTL_SerImp
	    ((Vs,Is):send_end_quan) ((VR,IR):recei_end_quan)
            ((R,L,Ca,G):trans_lines_const) (w:real) (z:complex) =
	    (kvl [(\z. Vs z);
		  (\z. --(VR z));
		  resis_volt R (\z. --(IR z));
		  induct_volt L w (\z. --(IR z))] z)) /\
    (kvl_implem_1a ShortTL_ShuAdm (Vs,Is) (VR,IR) (R,L,Ca,G) w z =
         (kvl [(\z. Vs z); (\z. --(VR z))] z))   /\
    (kvl_implem_1a MediumTL_PiCir (Vs,Is) (VR,IR) (R,L,Ca,G) w z =
	    (kvl [(\z. Vs z);
		 (\z. --(VR z));
		 resis_volt R (\z. --(IR z));
		 induct_volt L w (\z. --(IR z));
	         resis_volt R (admit_curr_med (\z. --(VR z)) Ca w);
	         induct_volt L w (admit_curr_med (\z. --(VR z)) Ca w)] z))   /\
    (kvl_implem_1a MediumTL_TCir (Vs,Is) (VR,IR) (R,L,Ca,G) w z =
	    (kvl [(\z. Vs z);
		 imped_volt_med (\z. --(Is z)) R L w;
		 (\z. --(VR z));
	         imped_volt_med (\z. --(IR z)) R L w] z))`;;

(*---------------------------------------------------------------------------*)
(*               Short Transmission Lines (Series Impedence                  *)
(*---------------------------------------------------------------------------*)
(*---------------------------------------------------------------------------*)
(*                      KVL Implementation Equivalence                       *)
(*---------------------------------------------------------------------------*)

let SHORT_TL_SERIES_IMPED_KVL_ALT = prove(
`!Vs Is VR IR Ca G L R w z.
   kvl_implem_1a ShortTL_SerImp ((Vs,Is):send_end_quan) ((VR,IR):recei_end_quan)
              ((R,L,Ca,G):trans_lines_const) (w:real) (z:complex) =
	(Vs z = ((series_imped_volt R L w (IR:cur_fun)) z) + VR z)`,

REPEAT GEN_TAC THEN SIMP_TAC [series_imped_volt] THEN
 REWRITE_TAC [kvl_implem_1a; kvl] THEN REWRITE_TAC [LENGTH] THEN
  SIMP_TAC [GSYM ONE; GSYM TWO; GSYM THREE] THEN
   SIMP_TAC [SUC_SUB1] THEN SIMP_TAC [VSUM_4_LIST] THEN
 SUBGOAL_THEN `induct_volt L w (\z. --(IR:cur_fun) z) z = -- (induct_volt L w (\z. IR z) z)` ASSUME_TAC
  THENL [REWRITE_TAC [induct_volt] THEN CONV_TAC COMPLEX_FIELD;ALL_TAC] THEN
   ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
    SUBGOAL_THEN `resis_volt R (\z. --(IR:cur_fun) z) z = -- (resis_volt R (\z. IR z) z)` ASSUME_TAC
     THENL [REWRITE_TAC [resis_volt] THEN CONV_TAC COMPLEX_FIELD;ALL_TAC]
     THEN ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
       SIMP_TAC [ETA_AX] THEN CONV_TAC COMPLEX_FIELD);;

(*=============================================================*)
(*            Let, in, and form of the above theorem           *)
(*=============================================================*)

let SHORT_TL_SERIES_IMPED_KVL = prove (
 `!Vs Is VR IR Ca G L R w z.
   let se = ((Vs,Is):send_end_quan) and
       re = ((VR,IR):recei_end_quan) and
       tlc = ((R,L,Ca,G):trans_lines_const) in
   (kvl_implem_1a ShortTL_SerImp se re tlc (w:real) (z:complex) =
	(Vs z = ((series_imped_volt R L w (IR:cur_fun)) z) + VR z))`,

LET_TAC THEN REWRITE_TAC [SHORT_TL_SERIES_IMPED_KVL_ALT]);;

(*---------------------------------------------------------------------------*)
(*                    KCL Implementation Equivalence all                     *)
(*---------------------------------------------------------------------------*)

let kcl_implem_1a = define `
    (kcl_implem_1a ShortTL_SerImp
         ((Vs,Is):send_end_quan) ((VR,IR):recei_end_quan)
          ((R,L,Ca,G):trans_lines_const) (w:real) z =
                   (kcl [(\z. Is z); (\z. --(IR z))] z))   /\
    (kcl_implem_1a ShortTL_ShuAdm
         (Vs,Is) (VR,IR) (R,L,Ca,G) w z =
                   (kcl [(\z. Is z);
		         resis_curr R (\z. --(VR z));
			 capacit_curr (\z. --(VR z)) Ca w;
			 (\z. --(IR z))] z))   /\
    (kcl_implem_1a MediumTL_PiCir
             (Vs,Is) (VR,IR) (R,L,Ca,G) w z =
	           (kcl [(\z. Is z);
		         (\z. --(IR z));
	                 admit_curr_med (\z. --(VR z)) Ca w;
			 admit_curr_med (\z. --(Vs z)) Ca w] z))   /\
    (kcl_implem_1a MediumTL_TCir
             (Vs,Is) (VR,IR) (R,L,Ca,G) w z =
                   (kcl [(\z. Is z);
		         (\z. --(IR z));
	                 (\z. (Cx w * Cx Ca) * ((\z. --(VR z)) z +
			     (imped_volt_med (\z. --(IR z)) R L w) z))] z))`;;

(*---------------------------------------------------------------------------*)
(*                      KCL Implementation Equivalence                       *)
(*---------------------------------------------------------------------------*)

 let SHORT_TL_SERIES_IMPED_KCL_ALT = prove(
 `!Vs Is VR IR Ca G L R w z.
   kcl_implem_1a ShortTL_SerImp
        ((Vs,Is):send_end_quan) ((VR,IR):recei_end_quan)
         ((R,L,Ca,G):trans_lines_const) (w:real) z = (Is z  = IR z)`,

REPEAT GEN_TAC THEN REWRITE_TAC [kcl_implem_1a; kcl;LENGTH]
 THEN SIMP_TAC [GSYM ONE; GSYM TWO; SUC_SUB1;VSUM_2_LIST] THEN
CONV_TAC COMPLEX_FIELD);;

(*=============================================================*)
(*            Let, in, and form of the above theorem           *)
(*=============================================================*)

let SHORT_TL_SERIES_IMPED_KCL = prove(
`!Vs Is VR IR Ca G L R w z.
  let se = ((Vs,Is):send_end_quan) and
      re = ((VR,IR):recei_end_quan) and
      tlc = ((R,L,Ca,G):trans_lines_const) in
   kcl_implem_1a ShortTL_SerImp se re tlc (w:real) z = (Is z = IR z)`,

LET_TAC THEN REWRITE_TAC [SHORT_TL_SERIES_IMPED_KCL_ALT]);;

(*---------------------------------------------------------------------------*)
(*            Verification of the Short Transmisison Lines Models            *)
(*---------------------------------------------------------------------------*)

let SHORT_TL_SERIES_IMPED_KVL_KCL_IMP_IMPLEM_ALT = prove(
`!VR Vs IR Is R L Ca G w z.
   ((kvl_implem_1a ShortTL_SerImp
       ((Vs,Is):send_end_quan) ((VR,IR):recei_end_quan)
        ((R,L,Ca,G):trans_lines_const) (w:real) z) /\
   (kcl_implem_1a ShortTL_SerImp
       ((Vs,Is):send_end_quan) ((VR,IR):recei_end_quan)
        ((R,L,Ca,G):trans_lines_const) w z)) =
   ((Vs z = (Cx (&1) * VR z + (series_imped_volt R L w (IR:cur_fun)) z)) /\
    (Is z  = Cx (&0) * VR z + Cx (&1) * IR z))`,

REPEAT GEN_TAC THEN
 SIMP_TAC [SHORT_TL_SERIES_IMPED_KVL_ALT; SHORT_TL_SERIES_IMPED_KCL_ALT] THEN
  CONV_TAC COMPLEX_FIELD);;

(*---------------------------------------------------------------------------*)

let SHORT_TL_SERIES_IMPED_KVL_KCL_IMP_IMPLEM = prove(
`!VR Vs IR Is R L Ca G w z.
  let se = ((Vs,Is):send_end_quan) and
      re = ((VR,IR):recei_end_quan) and
      tlc = ((R,L,Ca,G):trans_lines_const) in
   ((kvl_implem_1a ShortTL_SerImp se re tlc (w:real) z) /\
   (kcl_implem_1a ShortTL_SerImp se re tlc w z)) =
   ((Vs z = (Cx (&1) * VR z + (series_imped_volt R L w (IR:cur_fun)) z)) /\
    (Is z  = Cx (&0) * VR z + Cx (&1) * IR z))`,

LET_TAC THEN REWRITE_TAC [SHORT_TL_SERIES_IMPED_KVL_KCL_IMP_IMPLEM_ALT]);;

(*--------------------------------------------------------------------------*)
(*               ABCD matrices for all transmission lines                   *)
(*--------------------------------------------------------------------------*)

let abcd_mat_1a = define `
    (abcd_mat_1a ShortTL_SerImp ((R,L,Ca,G):trans_lines_const) w =
        ((vector [vector [Cx (&1); (Cx R + ii * Cx w * Cx L)];
	          vector [Cx (&0); Cx (&1)]]):comp_mat))   /\
    (abcd_mat_1a ShortTL_ShuAdm ((R,L,Ca,G):trans_lines_const) w =
        ((vector [vector [Cx (&1); Cx (&0)];
	          vector [(Cx (&1 / R) + ii * Cx w * Cx Ca); Cx (&1)]]):comp_mat)) /\
   (abcd_mat_1a MediumTL_TCir ((R,L,Ca,G):trans_lines_const) w =
        ((vector [vector [(Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&2));
	                  ((Cx R + ii * Cx w * Cx L) *
	        (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&4)))];
	          vector [(Cx w * Cx Ca);
	       (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&2))]]):comp_mat)) /\
   (abcd_mat_1a MediumTL_PiCir ((R,L,Ca,G):trans_lines_const) w =
        ((vector [vector [(Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&2));
	                  (Cx R + ii * Cx w * Cx L)];
	          vector [((Cx w * Cx Ca) *
                             (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&4)));
	                  (Cx (&1) +
			     ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&2))]]):comp_mat))`;;
	     

(*------Some useful lemmas proved using definition rewriting------*)


let ABCD_MAT_SHORTTL_SER_IMP = prove(
`!R L Ca G w.
      (abcd_mat_1a ShortTL_SerImp ((R,L,Ca,G):trans_lines_const) w =
         ((vector [vector [Cx (&1); (Cx R + ii * Cx w * Cx L)];
  	           vector [Cx (&0); Cx (&1)]]):comp_mat))`,

REPEAT STRIP_TAC THEN REWRITE_TAC [abcd_mat_1a]);;


let ABCD_MAT_SHORTTL_SHU_ADM = prove(
`!R L Ca G w.
    (abcd_mat_1a ShortTL_ShuAdm ((R,L,Ca,G):trans_lines_const) w =
        ((vector [vector [Cx (&1); Cx (&0)];
	          vector [(Cx (&1 / R) + ii * Cx w * Cx Ca); Cx (&1)]]):comp_mat))`,

REPEAT STRIP_TAC THEN REWRITE_TAC [abcd_mat_1a]);;


let ABCD_MAT_MEDIUMTL_TCIR = prove(
`!R L Ca G w.
     (abcd_mat_1a MediumTL_TCir ((R,L,Ca,G):trans_lines_const) w =
        ((vector [vector [(Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&2));
	                  ((Cx R + ii * Cx w * Cx L) *
	        (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&4)))];
	          vector [(Cx w * Cx Ca);
	       (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&2))]]):comp_mat))`,

REPEAT STRIP_TAC THEN REWRITE_TAC [abcd_mat_1a]);;


let ABCD_MAT_MEDIUMTL_PICIR = prove(
`!R L Ca G w.
      (abcd_mat_1a MediumTL_PiCir ((R,L,Ca,G):trans_lines_const) w =
        ((vector [vector [(Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&2));
	                  (Cx R + ii * Cx w * Cx L)];
	          vector [((Cx w * Cx Ca) *
                             (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&4)));
	                  (Cx (&1) +
			     ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&2))]]):comp_mat))`,

REPEAT STRIP_TAC THEN REWRITE_TAC [abcd_mat_1a]);;

(*------------------------------------------------------------------------*)

let abcd_mat_short_tl_series_imped = new_definition `
    abcd_mat_short_tl_series_imped ((R,L,Ca,G):trans_lines_const) w =
        ((vector [vector [Cx (&1); (Cx R + ii * Cx w * Cx L)];
	          vector [Cx (&0); Cx (&1)]]):comp_mat)`;;

let relat_send_receiv_quan_short_tl_series_imped = new_definition `
    relat_send_receiv_quan_short_tl_series_imped ShortTL ((Vs,Is):send_end_quan)
            ((VR,IR):recei_end_quan) ((R,L,Ca,G):trans_lines_const) w z =
       ((send_end_vec ((Vs,Is):send_end_quan) z) =
          ((abcd_mat_short_tl_series_imped ((R,L,Ca,G):trans_lines_const) w):comp_mat) **
	     (recei_end_vec ((VR,IR):recei_end_quan) z))`;;

let relat_send_receiv_quan_1a = define `
    (relat_send_receiv_quan_1a ShortTL_SerImp ((Vs,Is):send_end_quan)
            ((VR,IR):recei_end_quan) ((R,L,Ca,G):trans_lines_const) w z =
       ((send_end_vec ((Vs,Is):send_end_quan) z) =
          ((abcd_mat_1a ShortTL_SerImp ((R,L,Ca,G):trans_lines_const) w):comp_mat) **
	     (recei_end_vec ((VR,IR):recei_end_quan) z)))   /\
    (relat_send_receiv_quan_1a ShortTL_ShuAdm ((Vs,Is):send_end_quan)
            ((VR,IR):recei_end_quan) ((R,L,Ca,G):trans_lines_const) w z =
       ((send_end_vec ((Vs,Is):send_end_quan) z) =
          ((abcd_mat_1a ShortTL_ShuAdm ((R,L,Ca,G):trans_lines_const) w):comp_mat) **
	     (recei_end_vec ((VR,IR):recei_end_quan) z))) /\
   (relat_send_receiv_quan_1a MediumTL_PiCir ((Vs,Is):send_end_quan)
            ((VR,IR):recei_end_quan) ((R,L,Ca,G):trans_lines_const) w z =
       ((send_end_vec ((Vs,Is):send_end_quan) z) =
          ((abcd_mat_1a MediumTL_PiCir ((R,L,Ca,G):trans_lines_const) w):comp_mat) **
	     (recei_end_vec ((VR,IR):recei_end_quan) z))) /\
   (relat_send_receiv_quan_1a MediumTL_TCir ((Vs,Is):send_end_quan)
            ((VR,IR):recei_end_quan) ((R,L,Ca,G):trans_lines_const) w z =
       ((send_end_vec ((Vs,Is):send_end_quan) z) =
          ((abcd_mat_1a MediumTL_TCir ((R,L,Ca,G):trans_lines_const) w):comp_mat) **
	     (recei_end_vec ((VR,IR):recei_end_quan) z)))`;;

(*-----------------------------------------------------------------------------*)

let SHORT_TL_SERIES_IMPED_IMPLEM_EQ_MAT_REP_ALT = prove(
`!Vs Is VR IR R L Ca G w z.
    ((kvl_implem_1a ShortTL_SerImp (Vs,Is) (VR,IR) (R,L,Ca,G) w z) /\
     (kcl_implem_1a ShortTL_SerImp (Vs,Is) (VR,IR) (R,L,Ca,G) w z))
  = (relat_send_receiv_quan_1a ShortTL_SerImp ((Vs,Is):send_end_quan)
            ((VR,IR):recei_end_quan) ((R,L,Ca,G):trans_lines_const) w z)`,

REPEAT GEN_TAC THEN
 REWRITE_TAC [SHORT_TL_SERIES_IMPED_KVL_KCL_IMP_IMPLEM_ALT; series_imped_volt;
                resis_volt; induct_volt] THEN
 REWRITE_TAC [relat_send_receiv_quan_1a;
                send_end_vec; abcd_mat_1a; recei_end_vec] THEN
 REWRITE_TAC [MAT2x2_MUL_VEC2; CVECTOR2_EQ] THEN
  CONV_TAC COMPLEX_FIELD);;

(*--------------------------------------------------------------------------*)

let SHORT_TL_SERIES_IMPED_IMPLEM_EQ_MAT_REP = prove(
`!Vs Is VR IR R L Ca G w z.
  let se = ((Vs,Is):send_end_quan) and
      re = ((VR,IR):recei_end_quan) and
      tlc = ((R,L,Ca,G):trans_lines_const) in
    ((kvl_implem_1a ShortTL_SerImp se re tlc w z) /\
     (kcl_implem_1a ShortTL_SerImp se re tlc w z))
  = (relat_send_receiv_quan_1a ShortTL_SerImp se re tlc w z)`,

LET_TAC THEN REWRITE_TAC [SHORT_TL_SERIES_IMPED_IMPLEM_EQ_MAT_REP_ALT]);;

(*--------------------------------------------------------------------------*)

let ABCD_PAR_SHORT_TL_SERIES_IMPED_ALT = prove(
`!Vs Is VR IR A B C D R L Ca G w z.
     A = Cx(&1) /\
     B = Cx R + ii * Cx w * Cx L /\
     C = Cx(&0) /\
     D = Cx(&1)
      ==> ((relat_send_receiv_quan_gen ((Vs,Is):send_end_quan)
            ((VR,IR):recei_end_quan) ((A,B,C,D):abcd_param) z) =
      ((relat_send_receiv_quan_1a ShortTL_SerImp ((Vs,Is):send_end_quan)
            ((VR,IR):recei_end_quan) ((R,L,Ca,G):trans_lines_const) w z)))`,

REPEAT STRIP_TAC THEN
 REWRITE_TAC [relat_send_receiv_quan_gen; relat_send_receiv_quan_1a;abcd_mat_gen; abcd_mat_1a]
 THEN ASM_SIMP_TAC []);;

(*--------------------------------------------------------------------------*)

let ABCD_PAR_SHORT_TL_SERIES_IMPED = prove(
`!Vs Is VR IR A B C D R L Ca G w z.
  let se = ((Vs,Is):send_end_quan) and
      re = ((VR,IR):recei_end_quan) and
      tlc = ((R,L,Ca,G):trans_lines_const) and
      abcd = ((A,B,C,D):abcd_param) in
     A = Cx(&1) /\
     B = Cx R + ii * Cx w * Cx L /\
     C = Cx(&0) /\
     D = Cx(&1)
      ==> ((relat_send_receiv_quan_gen se re abcd z) =
      (relat_send_receiv_quan_1a ShortTL_SerImp se re tlc w z))`,

LET_TAC THEN REWRITE_TAC [ABCD_PAR_SHORT_TL_SERIES_IMPED_ALT]);;

(*---------------------------------------------------------------------------*)

let ABCD_PAR_EQ_IMPLEM_SHORT_TL_SERIES_IMP_ALT = prove(
`!Vs Is VR IR A B C D R L Ca G w z.
     A = Cx(&1) /\
     B = Cx R + ii * Cx w * Cx L /\
     C = Cx(&0) /\
     D = Cx(&1)
      ==> ((relat_send_receiv_quan_gen ((Vs,Is):send_end_quan)
            ((VR,IR):recei_end_quan) ((A,B,C,D):abcd_param) z) =
      (kvl_implem_1a ShortTL_SerImp (Vs,Is) (VR,IR) (R,L,Ca,G) w z /\
       kcl_implem_1a ShortTL_SerImp (Vs,Is) (VR,IR) (R,L,Ca,G) w z))`,

REPEAT STRIP_TAC THEN
 REWRITE_TAC [SHORT_TL_SERIES_IMPED_IMPLEM_EQ_MAT_REP_ALT] THEN
  ASM_SIMP_TAC [ABCD_PAR_SHORT_TL_SERIES_IMPED_ALT]);;

(*---------------------------------------------------------------------------*)

let ABCD_PAR_EQ_IMPLEM_SHORT_TL_SERIES_IMP = prove(
`!Vs Is VR IR A B C D R L Ca G w z.
  let se = ((Vs,Is):send_end_quan) and
      re = ((VR,IR):recei_end_quan) and
      tlc = ((R,L,Ca,G):trans_lines_const) and
      abcd = ((A,B,C,D):abcd_param) in
     A = Cx(&1) /\
     B = Cx R + ii * Cx w * Cx L /\
     C = Cx(&0) /\
     D = Cx(&1)
      ==> ((relat_send_receiv_quan_gen se re abcd z) =
      (kvl_implem_1a ShortTL_SerImp se re tlc w z /\
       kcl_implem_1a ShortTL_SerImp se re tlc w z))`,

LET_TAC THEN REWRITE_TAC [ABCD_PAR_EQ_IMPLEM_SHORT_TL_SERIES_IMP_ALT]);;

(*---------------------------------------------------------------------------*)
(*---------------------------------------------------------------------------*)
(*                 Short Transmission Lines (Shunt Admittance)               *)
(*---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------*)
(*                      KVL Implementation Equivalence                       *)
(*---------------------------------------------------------------------------*)

let SHORT_TL_SHUNT_ADMIT_KVL_ALT = prove(
`!Vs Is VR IR R L Ca G w z.
   kvl_implem_1a ShortTL_ShuAdm
      ((Vs,Is):send_end_quan) ((VR,IR):recei_end_quan)
        ((R,L,Ca,G):trans_lines_const) w z =
	(Vs z = VR z)`,

REPEAT GEN_TAC THEN REWRITE_TAC [kvl_implem_1a;kvl;LENGTH] THEN
 SIMP_TAC [GSYM ONE;SUC_SUB1;VSUM_2_LIST] THEN CONV_TAC COMPLEX_FIELD);;

(*---------------------------------------------------------------------------*)

let SHORT_TL_SHUNT_ADMIT_KVL = prove(
`!Vs Is VR IR R L Ca G w z.
  let se = ((Vs,Is):send_end_quan) and
      re = ((VR,IR):recei_end_quan) and
      tlc = ((R,L,Ca,G):trans_lines_const) in
   kvl_implem_1a ShortTL_ShuAdm se re tlc w z = (Vs z = VR z)`,

LET_TAC THEN REWRITE_TAC [SHORT_TL_SHUNT_ADMIT_KVL_ALT]);;

(*---------------------------------------------------------------------------*)
(*                     KCL Implementation Equivalence                        *)
(*---------------------------------------------------------------------------*)

let SHORT_TL_SHUNT_ADMIT_KCL_ALT = prove(
`!Vs Is VR IR Ca G L R w z.
    kcl_implem_1a ShortTL_ShuAdm ((Vs,Is):send_end_quan) ((VR,IR):recei_end_quan)
              ((R,L,Ca,G):trans_lines_const) (w:real) z =
	(Is z = ((shunt_admit_curr R Ca w (VR:vol_fun)) z) + IR z)`,

REPEAT GEN_TAC THEN SIMP_TAC [shunt_admit_curr] THEN
 REWRITE_TAC [kcl_implem_1a; kcl;LENGTH] THEN SIMP_TAC [GSYM ONE; GSYM TWO; GSYM THREE;SUC_SUB1]
  THEN SIMP_TAC [VSUM_4_LIST] THEN
   SUBGOAL_THEN `resis_curr R (\z. --(VR:cur_fun) z) z = -- (resis_curr R) (\z. VR z) z` ASSUME_TAC THENL
      [REWRITE_TAC [resis_curr] THEN CONV_TAC COMPLEX_FIELD;ALL_TAC] THEN
   ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
    SUBGOAL_THEN `capacit_curr (\z. --(VR:cur_fun) z) Ca w z = -- (capacit_curr (\z. VR z) Ca w z)` ASSUME_TAC
     THENL [REWRITE_TAC [capacit_curr] THEN CONV_TAC COMPLEX_FIELD;ALL_TAC]
     THEN ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN SIMP_TAC [ETA_AX] THEN
      CONV_TAC COMPLEX_FIELD);;

(*---------------------------------------------------------------------------*)

let SHORT_TL_SHUNT_ADMIT_KCL = prove(
`!Vs Is VR IR R L Ca G w z.
  let se = ((Vs,Is):send_end_quan) and
      re = ((VR,IR):recei_end_quan) and
      tlc = ((R,L,Ca,G):trans_lines_const) in
    kcl_implem_1a ShortTL_ShuAdm se re tlc (w:real) z =
	(Is z = ((shunt_admit_curr R Ca w (VR:vol_fun)) z) + IR z)`,

LET_TAC THEN REWRITE_TAC [SHORT_TL_SHUNT_ADMIT_KCL_ALT]);;

(*---------------------------------------------------------------------------*)
(*   Verification of the Short Transmisison Lines Models (Shunt Admittance)  *)
(*---------------------------------------------------------------------------*)

let SHORT_TL_SHUNT_ADMIT_KVL_KCL_IMP_IMPLEM_ALT = prove(
`!VR Vs IR Is R L Ca G w z.
   ((kvl_implem_1a ShortTL_ShuAdm ((Vs,Is):send_end_quan)
    ((VR,IR):recei_end_quan) ((R,L,Ca,G):trans_lines_const) w z) /\
   (kcl_implem_1a ShortTL_ShuAdm ((Vs,Is):send_end_quan)
    ((VR,IR):recei_end_quan) ((R,L,Ca,G):trans_lines_const) (w:real) z)) =
	((Vs z  = Cx (&1) * VR z + Cx (&0) * IR z) /\
	 ((Is z = ((shunt_admit_curr (R:real) (Ca:real) (w:real) (VR:vol_fun)) z) + Cx (&1) * IR z)))`,

REPEAT GEN_TAC THEN
  SIMP_TAC [SHORT_TL_SHUNT_ADMIT_KVL_ALT; SHORT_TL_SHUNT_ADMIT_KCL_ALT] THEN
   CONV_TAC COMPLEX_FIELD);;

(*--------------------------------------------------------------------------*)

let SHORT_TL_SHUNT_ADMIT_KVL_KCL_IMP_IMPLEM = prove(
`!VR Vs IR Is R L Ca G w z.
  let se = ((Vs,Is):send_end_quan) and
      re = ((VR,IR):recei_end_quan) and
      tlc = ((R,L,Ca,G):trans_lines_const) in
   ((kvl_implem_1a ShortTL_ShuAdm se re tlc w z) /\
    (kcl_implem_1a ShortTL_ShuAdm se re tlc (w:real) z)) =
	((Vs z  = Cx (&1) * VR z + Cx (&0) * IR z) /\
	 ((Is z = ((shunt_admit_curr (R:real) (Ca:real) (w:real) (VR:vol_fun)) z) + Cx (&1) * IR z)))`,

LET_TAC THEN REWRITE_TAC [SHORT_TL_SHUNT_ADMIT_KVL_KCL_IMP_IMPLEM_ALT]);;

(*--------------------------------------------------------------------------*)

let SHORT_TL_SHUNT_ADMIT_IMPLEM_EQ_MAT_REP_ALT = prove(
`!Vs Is VR IR R L Ca G w z.
  valid_transmission_line (ShortTL_ShuAdm,(R,L,Ca,G))
    ==> ((kvl_implem_1a ShortTL_ShuAdm (Vs,Is) (VR,IR) (R,L,Ca,G) w z) /\
       (kcl_implem_1a ShortTL_ShuAdm (Vs,Is) (VR,IR) (R,L,Ca,G) w z))
     = (relat_send_receiv_quan_1a ShortTL_ShuAdm ((Vs,Is):send_end_quan)
           ((VR,IR):recei_end_quan) ((R,L,Ca,G):trans_lines_const) w z)`,

REWRITE_TAC [valid_transmission_line; valid_tl_const; valid_transm_line_model1a]
 THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC [SHORT_TL_SHUNT_ADMIT_KVL_KCL_IMP_IMPLEM_ALT; shunt_admit_curr;
                resis_curr; capacit_curr] THEN
  REWRITE_TAC [relat_send_receiv_quan_1a;
                send_end_vec; abcd_mat_1a; recei_end_vec] THEN
  REWRITE_TAC [conductr;MAT2x2_MUL_VEC2;CVECTOR2_EQ] THEN
  CONV_TAC COMPLEX_FIELD);;

(*--------------------------------------------------------------------------*)

let SHORT_TL_SHUNT_ADMIT_IMPLEM_EQ_MAT_REP = prove(
`!Vs Is VR IR R L Ca G w z.
  let se = ((Vs,Is):send_end_quan) and
      re = ((VR,IR):recei_end_quan) and
      tlc = ((R,L,Ca,G):trans_lines_const) in
  valid_transmission_line (ShortTL_ShuAdm,tlc)
    ==> ((kvl_implem_1a ShortTL_ShuAdm se re tlc w z) /\
         (kcl_implem_1a ShortTL_ShuAdm se re tlc w z))
     = (relat_send_receiv_quan_1a ShortTL_ShuAdm se re tlc w z)`,

LET_TAC THEN REWRITE_TAC [SHORT_TL_SHUNT_ADMIT_IMPLEM_EQ_MAT_REP_ALT]);;

(*--------------------------------------------------------------------------*)

let ABCD_PAR_SHORT_TL_SHUNT_ADMIT_ALT = prove(
`!Vs Is VR IR A B C D R L Ca G w z.
     A = Cx(&1) /\
     B = Cx(&0) /\
     C = Cx (&1 / R) + ii * Cx w * Cx (Ca) /\
     D = Cx(&1)
      ==> ((relat_send_receiv_quan_gen ((Vs,Is):send_end_quan)
            ((VR,IR):recei_end_quan) ((A,B,C,D):abcd_param) z) =
      (relat_send_receiv_quan_1a ShortTL_ShuAdm
       ((Vs,Is):send_end_quan)
         ((VR,IR):recei_end_quan) ((R,L,Ca,G):trans_lines_const) w z))`, 

REPEAT STRIP_TAC THEN
 REWRITE_TAC [relat_send_receiv_quan_gen; relat_send_receiv_quan_1a;abcd_mat_gen; abcd_mat_1a]
  THEN ASM_SIMP_TAC []);;

 
let ABCD_PAR_SHORT_TL_SHUNT_ADMIT = prove(
`!Vs Is VR IR A B C D R L Ca G w z.
  let se = ((Vs,Is):send_end_quan) and
      re = ((VR,IR):recei_end_quan) and
      tlc = ((R,L,Ca,G):trans_lines_const) and
      abcd = ((A,B,C,D):abcd_param) in
     A = Cx(&1) /\
     B = Cx(&0) /\
     C = Cx (&1 / R) + ii * Cx w * Cx (Ca) /\
     D = Cx(&1)
      ==> ((relat_send_receiv_quan_gen se re abcd z) =
      (relat_send_receiv_quan_1a ShortTL_ShuAdm se re tlc w z))`, 

LET_TAC THEN REWRITE_TAC [ABCD_PAR_SHORT_TL_SHUNT_ADMIT_ALT]);;


(*--------------------------------------------------------------------------*)

let ABCD_PAR_EQ_IMPLEM_SHORT_TL_SHUNT_ADMIT_ALT = prove(
`!Vs Is VR IR A B C D R L Ca G w z.
  valid_transmission_line (ShortTL_ShuAdm,(R,L,Ca,G)) /\
     A = Cx(&1) /\
     B = Cx(&0) /\
     C = Cx (&1 / R) + ii * Cx w * Cx (Ca) /\
     D = Cx(&1)
      ==> ((relat_send_receiv_quan_gen ((Vs,Is):send_end_quan)
            ((VR,IR):recei_end_quan) ((A,B,C,D):abcd_param) z) =
      ((kvl_implem_1a ShortTL_ShuAdm (Vs,Is) (VR,IR) (R,L,Ca,G) w z) /\
       (kcl_implem_1a ShortTL_ShuAdm (Vs,Is) (VR,IR) (R,L,Ca,G) w z)))`, 

REWRITE_TAC [valid_transmission_line; valid_tl_const; valid_transm_line_model1a] THEN
 REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `((kvl_implem_1a ShortTL_ShuAdm (Vs,Is) (VR,IR) (R,L,Ca,G) w z) /\
       (kcl_implem_1a ShortTL_ShuAdm (Vs,Is) (VR,IR) (R,L,Ca,G) w z))
     = (relat_send_receiv_quan_1a ShortTL_ShuAdm ((Vs,Is):send_end_quan)
            ((VR,IR):recei_end_quan) ((R,L,Ca,G):trans_lines_const) w z)` ASSUME_TAC THENL   
      [MATCH_MP_TAC SHORT_TL_SHUNT_ADMIT_IMPLEM_EQ_MAT_REP_ALT THEN
       ASM_SIMP_TAC [valid_transmission_line; valid_tl_const; valid_transm_line_model1a];ALL_TAC]
       THEN ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC)
       THEN ASM_SIMP_TAC [ABCD_PAR_SHORT_TL_SHUNT_ADMIT_ALT]);;

(*---------------------------------------------------------------------------*)

let ABCD_PAR_EQ_IMPLEM_SHORT_TL_SHUNT_ADMIT = prove(
`!Vs Is VR IR A B C D R L Ca G w z.
  let se = ((Vs,Is):send_end_quan) and
      re = ((VR,IR):recei_end_quan) and
      tlc = ((R,L,Ca,G):trans_lines_const) and
      abcd = ((A,B,C,D):abcd_param) in
  valid_transmission_line (ShortTL_ShuAdm,tlc) /\
     A = Cx(&1) /\
     B = Cx(&0) /\
     C = Cx (&1 / R) + ii * Cx w * Cx Ca /\
     D = Cx(&1)
      ==> ((relat_send_receiv_quan_gen se re abcd z) =
      ((kvl_implem_1a ShortTL_ShuAdm se re tlc w z) /\
       (kcl_implem_1a ShortTL_ShuAdm se re tlc w z)))`,

LET_TAC THEN REWRITE_TAC [ABCD_PAR_EQ_IMPLEM_SHORT_TL_SHUNT_ADMIT_ALT]);;


(*---------------------------------------------------------------------------*)
(*---------------------------------------------------------------------------*)
(*               Medium Transmission Lines (Nominal Pi Circuit)              *)
(*---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------*)
(*                      KVL Implementation Equivalence                       *)
(*---------------------------------------------------------------------------*)

let MEDIUM_TL_NOMINAL_PI_KVL_ALT = prove(
`!Vs Is VR IR R L Ca G w z.
   kvl_implem_1a MediumTL_PiCir ((Vs,Is):send_end_quan) ((VR,IR):recei_end_quan)
            ((R,L,Ca,G):trans_lines_const) w z =
	(Vs z = VR z + (Cx R + ii * Cx w * Cx L) * IR z +
	      (Cx R + ii * Cx w * Cx L) * ((Cx w * Cx Ca) / Cx (&2)) * VR z)`,

REPEAT GEN_TAC THEN
 REWRITE_TAC [kvl_implem_1a;kvl;LENGTH] THEN
  SIMP_TAC [GSYM ONE; GSYM TWO; GSYM THREE; GSYM FOUR; GSYM FIVE;SUC_SUB1]
   THEN SIMP_TAC [VSUM_6_LIST] THEN
    SUBGOAL_THEN `resis_volt R (\z. --(IR:cur_fun) z) z = -- (resis_volt R (\z. IR z) z)` ASSUME_TAC
     THENL [REWRITE_TAC [resis_volt] THEN CONV_TAC COMPLEX_FIELD;ALL_TAC]
     THEN ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
      SUBGOAL_THEN `(resis_volt R (admit_curr_med (\z. --(VR:vol_fun) z) Ca w) z) =
       -- (resis_volt R (admit_curr_med (\z. VR z) Ca w) z)` ASSUME_TAC THENL[
      REWRITE_TAC [resis_volt; admit_curr_med] THEN CONV_TAC COMPLEX_FIELD;ALL_TAC]
      THEN ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
       REWRITE_TAC [resis_volt; admit_curr_med] THEN
 SUBGOAL_THEN `(induct_volt L w (\z. Cx w * Cx Ca / Cx (&2) * --(VR:vol_fun) z) z) =
  -- (induct_volt L w (\z. Cx w * Cx Ca / Cx (&2) * VR z) z)` ASSUME_TAC THENL
       [REWRITE_TAC [induct_volt] THEN CONV_TAC COMPLEX_FIELD;ALL_TAC]
       THEN
         ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
	  REWRITE_TAC [induct_volt] THEN SIMP_TAC [ETA_AX] THEN
	  CONV_TAC COMPLEX_FIELD);;

(*---------------------------------------------------------------------------*)

let MEDIUM_TL_NOMINAL_PI_KVL = prove(
`!Vs Is VR IR R L Ca G w z.
  let se = ((Vs,Is):send_end_quan) and
      re = ((VR,IR):recei_end_quan) and
      tlc = ((R,L,Ca,G):trans_lines_const) in
   kvl_implem_1a MediumTL_PiCir se re tlc w z =
	(Vs z = VR z + (Cx R + ii * Cx w * Cx L) * IR z +
	      (Cx R + ii * Cx w * Cx L) * ((Cx w * Cx Ca) / Cx (&2)) * VR z)`,

LET_TAC THEN REWRITE_TAC [MEDIUM_TL_NOMINAL_PI_KVL_ALT]);;

(*---------------------------------------------------------------------------*)
(*                     KCL Implementation Equivalence                        *)
(*---------------------------------------------------------------------------*)
(*---------------------------------------------------------------------------*)
(*                          KCL on the sending end                           *)
(*---------------------------------------------------------------------------*)

let kcl_implem_s_end_1a = new_definition
  `kcl_implem_s_end_1a MediumTL_PiCir
       ((Vs,Is):send_end_quan) ((VR,IR):recei_end_quan)
               (Iz:cur_fun) (w:real) z ((R,L,Ca,G):trans_lines_const) =
        (kcl [(\z. Is z); (\z. --(Iz z)); admit_curr_med (\z. --(Vs z)) Ca w] z)`;;

(*---------------------------------------------------------------------------*)

let MEDIUM_TL_NOMINAL_PI_KCL_SENDING_ALT = prove(
`!Vs Is VR IR Iz Ca G L R w z.
    kcl_implem_s_end_1a MediumTL_PiCir
        ((Vs,Is):send_end_quan) ((VR,IR):recei_end_quan)
               (Iz:cur_fun) (w:real) z ((R,L,Ca,G):trans_lines_const) =
	(Is z = Iz z + (admit_curr_med Vs Ca w) z)`,

REPEAT GEN_TAC THEN SIMP_TAC [admit_curr_med] THEN
 REWRITE_TAC [kcl_implem_s_end_1a; kcl;LENGTH] THEN
  SIMP_TAC [GSYM ONE; GSYM TWO;SUC_SUB1;VSUM_3_LIST]
   THEN
 SUBGOAL_THEN `!V. admit_curr_med (\z. --V z) Ca w z  = -- (admit_curr_med (\z. V z) Ca w z) ` ASSUME_TAC
  THENL [REWRITE_TAC [admit_curr_med] THEN CONV_TAC COMPLEX_FIELD;ALL_TAC]
  THEN ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
   SIMP_TAC [ETA_AX] THEN REWRITE_TAC [admit_curr_med]
   THEN CONV_TAC COMPLEX_FIELD);;

(*---------------------------------------------------------------------------*)

let MEDIUM_TL_NOMINAL_PI_KCL_SENDING = prove(
`!Vs Is VR IR Iz Ca G L R w z.
  let se = ((Vs,Is):send_end_quan) and
      re = ((VR,IR):recei_end_quan) and
      tlc = ((R,L,Ca,G):trans_lines_const) in
    kcl_implem_s_end_1a MediumTL_PiCir se re Iz w z tlc =
	(Is z = Iz z + (admit_curr_med Vs Ca w) z)`,

LET_TAC THEN REWRITE_TAC [MEDIUM_TL_NOMINAL_PI_KCL_SENDING_ALT]);;

(*---------------------------------------------------------------------------*)
(*                         KCL on the receiving end                          *)
(*---------------------------------------------------------------------------*)

let kcl_implem_r_end_1a = new_definition
  `kcl_implem_r_end_1a MediumTL_PiCir
     ((Vs,Is):send_end_quan) ((VR,IR):recei_end_quan)
              (Iz:cur_fun) (w:real) z ((R,L,Ca,G):trans_lines_const) =
        (kcl [(\z. Iz z); (\z. --(IR z));
	       admit_curr_med (\z. --(VR z)) Ca w] z)`;;

let MEDIUM_TL_NOMINAL_PI_KCL_RECEIVING_ALT = prove(
 `!Vs Is VR IR Iz Ca G L R w z.
    kcl_implem_r_end_1a MediumTL_PiCir
      ((Vs,Is):send_end_quan) ((VR,IR):recei_end_quan)
              (Iz:cur_fun) (w:real) z ((R,L,Ca,G):trans_lines_const) =
	(Iz z = IR z + (admit_curr_med VR Ca w) z)`,

REPEAT GEN_TAC THEN
  SIMP_TAC [admit_curr_med] THEN
   REWRITE_TAC [kcl_implem_r_end_1a; kcl;LENGTH] THEN
     SIMP_TAC [GSYM ONE; GSYM TWO;SUC_SUB1;VSUM_3_LIST]
     THEN
 SUBGOAL_THEN `!V. admit_curr_med (\z. --V z) Ca w z  = -- (admit_curr_med (\z. V z) Ca w z) ` ASSUME_TAC
  THENL [REWRITE_TAC [admit_curr_med] THEN CONV_TAC COMPLEX_FIELD;ALL_TAC]
  THEN ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
   SIMP_TAC [ETA_AX] THEN REWRITE_TAC [admit_curr_med] THEN
    CONV_TAC COMPLEX_FIELD);;

(*---------------------------------------------------------------------------*)

let MEDIUM_TL_NOMINAL_PI_KCL_RECEIVING = prove(
`!Vs Is VR IR Iz Ca G L R w z.
  let se = ((Vs,Is):send_end_quan) and
      re = ((VR,IR):recei_end_quan) and
      tlc = ((R,L,Ca,G):trans_lines_const) in
    kcl_implem_r_end_1a MediumTL_PiCir se re
              (Iz:cur_fun) (w:real) z tlc =
	(Iz z = IR z + (admit_curr_med VR Ca w) z)`,

LET_TAC THEN REWRITE_TAC [MEDIUM_TL_NOMINAL_PI_KCL_RECEIVING_ALT]);;


(*---------------------------------------------------------------------------*)

let MEDIUM_TL_NOMINAL_PI_KCL_ALT = prove(
`!Vs Is VR IR Ca G L R w z.
    kcl_implem_1a MediumTL_PiCir
        ((Vs,Is):send_end_quan) ((VR,IR):recei_end_quan)
           ((R,L,Ca,G):trans_lines_const) (w:real) z  =
	(Is z = IR z + (admit_curr_med VR Ca w) z  +
	                 (admit_curr_med Vs Ca w) z)`,

REPEAT GEN_TAC THEN
 SIMP_TAC [admit_curr_med] THEN
  REWRITE_TAC [kcl_implem_1a; kcl;LENGTH] THEN
   SIMP_TAC [GSYM ONE; GSYM TWO; GSYM THREE;SUC_SUB1;VSUM_4_LIST] THEN
    SUBGOAL_THEN `!V. admit_curr_med (\z. --V z) Ca w z  = -- (admit_curr_med (\z. V z) Ca w z) ` ASSUME_TAC
     THENL [REWRITE_TAC [admit_curr_med] THEN CONV_TAC COMPLEX_FIELD;ALL_TAC]
     THEN ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
      SIMP_TAC [ETA_AX] THEN REWRITE_TAC [admit_curr_med] THEN CONV_TAC COMPLEX_FIELD);;

(*---------------------------------------------------------------------------*)

let MEDIUM_TL_NOMINAL_PI_KCL = prove(
`!Vs Is VR IR Ca G L R w z.
  let se = ((Vs,Is):send_end_quan) and
      re = ((VR,IR):recei_end_quan) and
      tlc = ((R,L,Ca,G):trans_lines_const) in
    kcl_implem_1a MediumTL_PiCir se re tlc (w:real) z  =
	(Is z = IR z + (admit_curr_med VR Ca w) z  +
	                 (admit_curr_med Vs Ca w) z)`,

LET_TAC THEN REWRITE_TAC [MEDIUM_TL_NOMINAL_PI_KCL_ALT]);;

(*---------------------------------------------------------------------------*)

let MEDIUM_TL_NOMINAL_PI_SR_IMP_KCL_ALT = prove(
`!Vs Is VR IR Iz Ca G L R w z.
    ((kcl_implem_s_end_1a MediumTL_PiCir ((Vs,Is):send_end_quan)
          ((VR,IR):recei_end_quan) (Iz:cur_fun) (w:real) z
                 ((R,L,Ca,G):trans_lines_const)) /\
    (kcl_implem_r_end_1a MediumTL_PiCir (Vs,Is) (VR,IR) Iz w z
         (R,L,Ca,G))) ==>
      (kcl_implem_1a MediumTL_PiCir (Vs,Is) (VR,IR) (R,L,Ca,G) w z)`,

REPEAT GEN_TAC THEN
 SIMP_TAC [MEDIUM_TL_NOMINAL_PI_KCL_ALT; MEDIUM_TL_NOMINAL_PI_KCL_SENDING_ALT;
  MEDIUM_TL_NOMINAL_PI_KCL_RECEIVING_ALT] THEN
   CONV_TAC COMPLEX_FIELD);;

(*---------------------------------------------------------------------------*)

let MEDIUM_TL_NOMINAL_PI_SR_IMP_KCL = prove(
`!Vs Is VR IR Iz Ca G L R w z.
  let se = ((Vs,Is):send_end_quan) and
      re = ((VR,IR):recei_end_quan) and
      tlc = ((R,L,Ca,G):trans_lines_const) in
    ((kcl_implem_s_end_1a MediumTL_PiCir se re (Iz:cur_fun) (w:real) z tlc) /\
    (kcl_implem_r_end_1a MediumTL_PiCir se re Iz w z tlc)) ==>
      (kcl_implem_1a MediumTL_PiCir se re tlc w z)`,

LET_TAC THEN REWRITE_TAC [MEDIUM_TL_NOMINAL_PI_SR_IMP_KCL_ALT]);;


(*---------------------------------------------------------------------------*)
(*    Verification of the Medium Transmission Lines (Nominal Pi Circuit)     *)
(*---------------------------------------------------------------------------*)

let MEDIUM_TL_NOMINAL_PI_KVL_KCL_IMP_IMPLEM_ALT = prove(
`!VR Vs IR Is R L Ca G w z.
    ((kvl_implem_1a MediumTL_PiCir
       ((Vs,Is):send_end_quan) ((VR,IR):recei_end_quan)
                ((R,L,Ca,G):trans_lines_const) w z) /\
    (kcl_implem_1a MediumTL_PiCir (Vs,Is) (VR,IR)
               (R,L,Ca,G) (w:real) z)) =
    ((Vs z  = (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&2)) * VR z +
               (Cx R + ii * Cx w * Cx L) * IR z) /\
     (Is z = ((Cx w * Cx Ca) *
                 (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&4))) * VR z +
              (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&2)) * IR z))`,

REPEAT GEN_TAC THEN
 SIMP_TAC [MEDIUM_TL_NOMINAL_PI_KVL_ALT;MEDIUM_TL_NOMINAL_PI_KCL_ALT;admit_curr_med] THEN
  CONV_TAC COMPLEX_FIELD);;
  
(*--------------------------------------------------------------------------*)

let MEDIUM_TL_NOMINAL_PI_KVL_KCL_IMP_IMPLEM = prove(
`!VR Vs IR Is R L Ca G w z.
  let se = ((Vs,Is):send_end_quan) and
      re = ((VR,IR):recei_end_quan) and
      tlc = ((R,L,Ca,G):trans_lines_const) in
    ((kvl_implem_1a MediumTL_PiCir se re tlc w z) /\
    (kcl_implem_1a MediumTL_PiCir se re tlc (w:real) z)) =
    ((Vs z  = (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&2)) * VR z +
               (Cx R + ii * Cx w * Cx L) * IR z) /\
     (Is z = ((Cx w * Cx Ca) *
                 (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&4))) * VR z +
              (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&2)) * IR z))`,

LET_TAC THEN REWRITE_TAC [MEDIUM_TL_NOMINAL_PI_KVL_KCL_IMP_IMPLEM_ALT]);;


(*--------------------------------------------------------------------------*)

let MEDIUM_TL_NOMINAL_PI_IMPLEM_EQ_MAT_REP_ALT = prove(
`!Vs Is VR IR R L Ca G w z.
  valid_transmission_line (MediumTL_PiCir,((R,L,Ca,G):trans_lines_const))
  ==> ((kvl_implem_1a MediumTL_PiCir (Vs,Is) (VR,IR) (R,L,Ca,G) w z) /\
       (kcl_implem_1a MediumTL_PiCir (Vs,Is) (VR,IR) (R,L,Ca,G) w z))
     = (relat_send_receiv_quan_1a MediumTL_PiCir ((Vs,Is):send_end_quan)
            ((VR,IR):recei_end_quan) (R,L,Ca,G) w z)`,

REWRITE_TAC [valid_transmission_line; valid_tl_const; valid_transm_line_model1a]
 THEN REPEAT STRIP_TAC THEN
 REWRITE_TAC [MEDIUM_TL_NOMINAL_PI_KVL_KCL_IMP_IMPLEM_ALT;relat_send_receiv_quan_1a;
                send_end_vec; abcd_mat_1a; recei_end_vec;MAT2x2_MUL_VEC2;CVECTOR2_EQ]);;

(*--------------------------------------------------------------------------*)

 let MEDIUM_TL_NOMINAL_PI_IMPLEM_EQ_MAT_REP = prove(
 `!Vs Is VR IR R L Ca G w z.
  let se = ((Vs,Is):send_end_quan) and
      re = ((VR,IR):recei_end_quan) and
      tlc = ((R,L,Ca,G):trans_lines_const) in
  valid_transmission_line (MediumTL_PiCir,tlc)
  ==> ((kvl_implem_1a MediumTL_PiCir se re tlc w z) /\
       (kcl_implem_1a MediumTL_PiCir se re tlc w z))
     = (relat_send_receiv_quan_1a MediumTL_PiCir se re tlc w z)`,

LET_TAC THEN REWRITE_TAC [MEDIUM_TL_NOMINAL_PI_IMPLEM_EQ_MAT_REP_ALT]);;

(*--------------------------------------------------------------------------*)

let ABCD_PAR_MEDIUM_TL_NOMIN_PI_CIRC_ALT = prove(
`!Vs Is VR IR A B C D R L Ca G w z.
     A = (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&2)) /\
     B = (Cx R + ii * Cx w * Cx L) /\
     C = ((Cx w * Cx Ca) *
           (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&4))) /\
     D = (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&2))
      ==> ((relat_send_receiv_quan_gen ((Vs,Is):send_end_quan)
            ((VR,IR):recei_end_quan) ((A,B,C,D):abcd_param) z) =
          (relat_send_receiv_quan_1a MediumTL_PiCir (Vs,Is) (VR,IR)
             (R,L,Ca,G) w z))`,

REPEAT STRIP_TAC THEN
 REWRITE_TAC [relat_send_receiv_quan_gen; relat_send_receiv_quan_1a;abcd_mat_gen; abcd_mat_1a]
  THEN ASM_SIMP_TAC []);;


let ABCD_PAR_MEDIUM_TL_NOMIN_PI_CIRC = prove(
`!Vs Is VR IR A B C D R L Ca G w z.
  let se = ((Vs,Is):send_end_quan) and
      re = ((VR,IR):recei_end_quan) and
      tlc = ((R,L,Ca,G):trans_lines_const) and
      abcd = ((A,B,C,D):abcd_param) in
     A = (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&2)) /\
     B = (Cx R + ii * Cx w * Cx L) /\
     C = ((Cx w * Cx Ca) *
           (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&4))) /\
     D = (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&2))
      ==> ((relat_send_receiv_quan_gen se re abcd z) =
          (relat_send_receiv_quan_1a MediumTL_PiCir se re tlc w z))`, 

LET_TAC THEN REWRITE_TAC [ABCD_PAR_MEDIUM_TL_NOMIN_PI_CIRC_ALT]);;

(*--------------------------------------------------------------------------*)

let ABCD_PAR_EQ_IMPLEM_MEDIUM_TL_NOMIN_PI_CIRC_ALT = prove(
`!Vs Is VR IR A B C D R L Ca G w z.
  valid_transmission_line (MediumTL_PiCir,((R,L,Ca,G):trans_lines_const)) /\
     A = (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&2)) /\
     B = (Cx R + ii * Cx w * Cx L) /\
     C = ((Cx w * Cx Ca) *
           (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&4))) /\
     D = (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&2)) 
      ==> ((relat_send_receiv_quan_gen ((Vs,Is):send_end_quan)
            ((VR,IR):recei_end_quan) ((A,B,C,D):abcd_param) z) =
          ((kvl_implem_1a MediumTL_PiCir (Vs,Is) (VR,IR)
              (R,L,Ca,G) w z) /\
	   (kcl_implem_1a MediumTL_PiCir (Vs,Is) (VR,IR)
              (R,L,Ca,G) w z)))`,

REPEAT STRIP_TAC THEN
 SUBGOAL_THEN `((kvl_implem_1a MediumTL_PiCir ((Vs,Is):send_end_quan)
            ((VR,IR):recei_end_quan) ((R,L,Ca,G):trans_lines_const) w z) /\
       (kcl_implem_1a MediumTL_PiCir (Vs,Is) (VR,IR) (R,L,Ca,G) w z))
     = (relat_send_receiv_quan_1a MediumTL_PiCir (Vs,Is) (VR,IR)
         (R,L,Ca,G) w z)` ASSUME_TAC THENL	    
      [MATCH_MP_TAC MEDIUM_TL_NOMINAL_PI_IMPLEM_EQ_MAT_REP_ALT THEN
        ASM_SIMP_TAC [];ALL_TAC] THEN
  ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
  ASM_SIMP_TAC [ABCD_PAR_MEDIUM_TL_NOMIN_PI_CIRC_ALT]);;


let ABCD_PAR_EQ_IMPLEM_MEDIUM_TL_NOMIN_PI_CIRC = prove(
`!Vs Is VR IR A B C D R L Ca G w z.
  let se = ((Vs,Is):send_end_quan) and
      re = ((VR,IR):recei_end_quan) and
      tlc = ((R,L,Ca,G):trans_lines_const) and
      abcd = ((A,B,C,D):abcd_param) in
  valid_transmission_line (MediumTL_PiCir,tlc) /\
     A = (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&2)) /\
     B = (Cx R + ii * Cx w * Cx L) /\
     C = ((Cx w * Cx Ca) *
           (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&4))) /\
     D = (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&2)) 
      ==> ((relat_send_receiv_quan_gen se re abcd z) =
          ((kvl_implem_1a MediumTL_PiCir se re tlc w z) /\
	   (kcl_implem_1a MediumTL_PiCir se re tlc w z)))`, 

LET_TAC THEN REWRITE_TAC [ABCD_PAR_EQ_IMPLEM_MEDIUM_TL_NOMIN_PI_CIRC_ALT]);;


let ABCD_PAR_RELAT_MEDIUM_TL_NOMIN_PI_CIRC = prove(
`!A B C D R L Ca G w.
     A = (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&2)) /\
     B = (Cx R + ii * Cx w * Cx L) /\
     C = ((Cx w * Cx Ca) *
           (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&4))) /\
     D = (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&2)) 
      ==> ((A * D - B * C) = Cx (&1))`,

REPEAT STRIP_TAC THEN ASM_SIMP_TAC [] THEN CONV_TAC COMPLEX_FIELD);;


let ABCD_PAR_RELAT2_MEDIUM_TL_NOMIN_PI_CIRC = prove(
`!A B C D R L Ca G w.
     A = (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&2)) /\
     B = (Cx R + ii * Cx w * Cx L) /\
     C = ((Cx w * Cx Ca) *
           (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&4))) /\
     D = (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&2)) 
      ==> (A = D)`,

REPEAT STRIP_TAC THEN ASM_SIMP_TAC []);;

(*---------------------------------------------------------------------------*)
(*---------------------------------------------------------------------------*)
(*               Medium Transmission Lines (Nominal T Circuit)               *)
(*---------------------------------------------------------------------------*)

let kvl_implem_loop1_1a = new_definition
  `kvl_implem_loop1_1a MediumTL_TCir
     ((Vs,Is):send_end_quan) ((VR,IR):recei_end_quan)
            (Vy:vol_fun) ((R,L,Ca,G):trans_lines_const) w z =
         (kvl [(\z. Vs z); (\z. --(Vy z)); imped_volt_med (\z. --(Is z)) R L w] z)`;;

let kvl_implem_loop2_1a = new_definition
  `kvl_implem_loop2_1a MediumTL_TCir
       ((Vs,Is):send_end_quan) ((VR,IR):recei_end_quan)
            (Vy:vol_fun) ((R,L,Ca,G):trans_lines_const) w z =
         (kvl [(\z. Vy z); (\z. --(VR z)); imped_volt_med (\z. --(IR z)) R L w] z)`;;


(*---------------------------------------------------------------------------*)
(*                      KVL Implementation Equivalence                       *)
(*---------------------------------------------------------------------------*)

let MEDIUM_TL_NOMINAL_T_KVL_LOOP1_ALT = prove(
`!Vs Is VR IR Vy R L Ca G w z.
   kvl_implem_loop1_1a MediumTL_TCir
      ((Vs,Is):send_end_quan) ((VR,IR):recei_end_quan)
            (Vy:vol_fun) ((R,L,Ca,G):trans_lines_const) w z =
	(Vs z = Vy z + ((Cx R + ii * Cx w * Cx L) / Cx (&2)) * Is z)`,

REPEAT GEN_TAC THEN
 REWRITE_TAC [kvl_implem_loop1_1a;kvl;LENGTH] THEN
   SIMP_TAC [GSYM ONE; GSYM TWO;SUC_SUB1;VSUM_3_LIST] THEN
 SUBGOAL_THEN `imped_volt_med (\z. --(Is:cur_fun) z) R L w z =
   -- (imped_volt_med (\z. Is z) R L w z)` ASSUME_TAC THENL
       [REWRITE_TAC [imped_volt_med] THEN
         CONV_TAC COMPLEX_FIELD;ALL_TAC] THEN
  ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
   REWRITE_TAC [imped_volt_med] THEN
    CONV_TAC COMPLEX_FIELD);;


let MEDIUM_TL_NOMINAL_T_KVL_LOOP1 = prove(
`!Vs Is VR IR Vy R L Ca G w z.
  let se = ((Vs,Is):send_end_quan) and
      re = ((VR,IR):recei_end_quan) and
      tlc = ((R,L,Ca,G):trans_lines_const) in
   kvl_implem_loop1_1a MediumTL_TCir se re (Vy:vol_fun) tlc w z =
	(Vs z = Vy z + ((Cx R + ii * Cx w * Cx L) / Cx (&2)) * Is z)`,

LET_TAC THEN REWRITE_TAC [MEDIUM_TL_NOMINAL_T_KVL_LOOP1_ALT]);;


let MEDIUM_TL_NOMINAL_T_KVL_LOOP2_ALT = prove(
`!Vs Is VR IR Vy R L Ca G w z.
   kvl_implem_loop2_1a MediumTL_TCir
       ((Vs,Is):send_end_quan) ((VR,IR):recei_end_quan)
            (Vy:vol_fun) ((R,L,Ca,G):trans_lines_const) w z =
	(Vy z = VR z + ((Cx R + ii * Cx w * Cx L) / Cx (&2)) * IR z)`,

REPEAT GEN_TAC THEN
 REWRITE_TAC [kvl_implem_loop2_1a;kvl;LENGTH] THEN
   SIMP_TAC [GSYM ONE; GSYM TWO;SUC_SUB1;VSUM_3_LIST]
   THEN SUBGOAL_THEN `imped_volt_med (\z. --(Is:cur_fun) z) R L w z =
      -- (imped_volt_med (\z. Is z) R L w z)` ASSUME_TAC THENL
      [REWRITE_TAC [imped_volt_med] THEN CONV_TAC COMPLEX_FIELD;ALL_TAC]
      THEN ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
  REWRITE_TAC [imped_volt_med] THEN CONV_TAC COMPLEX_FIELD);;


let MEDIUM_TL_NOMINAL_T_KVL_LOOP2 = prove(
`!Vs Is VR IR Vy R L Ca G w z.
  let se = ((Vs,Is):send_end_quan) and
      re = ((VR,IR):recei_end_quan) and
      tlc = ((R,L,Ca,G):trans_lines_const) in
   kvl_implem_loop2_1a MediumTL_TCir se re (Vy:vol_fun) tlc w z =
	(Vy z = VR z + ((Cx R + ii * Cx w * Cx L) / Cx (&2)) * IR z)`,

LET_TAC THEN REWRITE_TAC [MEDIUM_TL_NOMINAL_T_KVL_LOOP2_ALT]);;




let MEDIUM_TL_NOMINAL_T_KVL_ALT = prove(
`!Vs Is VR IR R L Ca G w z.
   kvl_implem_1a MediumTL_TCir
   ((Vs,Is):send_end_quan) ((VR,IR):recei_end_quan)
            ((R,L,Ca,G):trans_lines_const) w z =
	(Vs z = ((Cx R + ii * Cx w * Cx L) / Cx (&2)) * Is z +
	  VR z + ((Cx R + ii * Cx w * Cx L) / Cx (&2)) * IR z)`,

REPEAT GEN_TAC THEN
 REWRITE_TAC [kvl_implem_1a;kvl;LENGTH] THEN
  SIMP_TAC [GSYM ONE; GSYM TWO; GSYM THREE;SUC_SUB1;VSUM_4_LIST]
  THEN SUBGOAL_THEN `!Is. imped_volt_med (\z. --(Is:cur_fun) z) R L w z =
                  -- (imped_volt_med (\z. Is z) R L w z)` ASSUME_TAC THENL
      [REWRITE_TAC [imped_volt_med] THEN
                    CONV_TAC COMPLEX_FIELD;ALL_TAC]
 THEN ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
         REWRITE_TAC [imped_volt_med] THEN CONV_TAC COMPLEX_FIELD);;

 


let MEDIUM_TL_NOMINAL_T_KVL = prove(
`!Vs Is VR IR R L Ca G w z.
  let se = ((Vs,Is):send_end_quan) and
      re = ((VR,IR):recei_end_quan) and
      tlc = ((R,L,Ca,G):trans_lines_const) in
   kvl_implem_1a MediumTL_TCir se re tlc w z =
	(Vs z = ((Cx R + ii * Cx w * Cx L) / Cx (&2)) * Is z +
	  VR z + ((Cx R + ii * Cx w * Cx L) / Cx (&2)) * IR z)`,

LET_TAC THEN REWRITE_TAC [MEDIUM_TL_NOMINAL_T_KVL_ALT]);;



let MEDIUM_TL_NOMINAL_T_LOOP12_IMP_KVL_ALT = prove(
`!Vs Is VR IR Vy R L Ca G w z.
   (kvl_implem_loop1_1a MediumTL_TCir
    ((Vs,Is):send_end_quan) ((VR,IR):recei_end_quan)
            (Vy:vol_fun) ((R,L,Ca,G):trans_lines_const) w z) /\
   (kvl_implem_loop2_1a MediumTL_TCir
   ((Vs,Is):send_end_quan) ((VR,IR):recei_end_quan)
            (Vy:vol_fun) ((R,L,Ca,G):trans_lines_const) w z) ==>
   (kvl_implem_1a MediumTL_TCir
      ((Vs,Is):send_end_quan) ((VR,IR):recei_end_quan)
            ((R,L,Ca,G):trans_lines_const) w z)`,

REPEAT GEN_TAC THEN
 REWRITE_TAC [MEDIUM_TL_NOMINAL_T_KVL_LOOP1_ALT;
  MEDIUM_TL_NOMINAL_T_KVL_LOOP2_ALT; MEDIUM_TL_NOMINAL_T_KVL_ALT] THEN
 CONV_TAC COMPLEX_FIELD);;



let MEDIUM_TL_NOMINAL_T_LOOP12_IMP_KVL = prove(
`!Vs Is VR IR Vy R L Ca G w z.
  let se = ((Vs,Is):send_end_quan) and
      re = ((VR,IR):recei_end_quan) and
      tlc = ((R,L,Ca,G):trans_lines_const) in
   (kvl_implem_loop1_1a MediumTL_TCir se re (Vy:vol_fun) tlc w z) /\
   (kvl_implem_loop2_1a MediumTL_TCir se re (Vy:vol_fun) tlc w z) ==>
   (kvl_implem_1a MediumTL_TCir se re tlc w z)`,

LET_TAC THEN REWRITE_TAC [MEDIUM_TL_NOMINAL_T_LOOP12_IMP_KVL_ALT]);;


(*---------------------------------------------------------------------------*)
(*                     KCL Implementation Equivalence                        *)
(*---------------------------------------------------------------------------*)

let MEDIUM_TL_NOMINAL_T_KCL_ALT = prove(
`!Vs Is VR IR Ca G L R w z.
    kcl_implem_1a MediumTL_TCir
       ((Vs,Is):send_end_quan) ((VR,IR):recei_end_quan)
               ((R,L,Ca,G):trans_lines_const) (w:real) z =
	(Is z = (Cx w * Cx Ca) * VR z + IR z + (Cx w * Cx Ca) * (imped_volt_med IR R L w) z)`,

REPEAT GEN_TAC THEN
 SIMP_TAC [imped_volt_med] THEN
  REWRITE_TAC [kcl_implem_1a; kcl;LENGTH] THEN
   SIMP_TAC [GSYM ONE; GSYM TWO;SUC_SUB1;VSUM_3_LIST] THEN
 SUBGOAL_THEN `imped_volt_med (\z. --IR z) R L w z  =
       -- (imped_volt_med (\z. IR z) R L w z) ` ASSUME_TAC THENL
      [REWRITE_TAC [imped_volt_med] THEN CONV_TAC COMPLEX_FIELD;ALL_TAC]
      THEN ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN 
       SIMP_TAC [ETA_AX] THEN REWRITE_TAC [imped_volt_med] THEN
                 CONV_TAC COMPLEX_FIELD);;
		 

let MEDIUM_TL_NOMINAL_T_KCL = prove(
`!Vs Is VR IR Ca G L R w z.
  let se = ((Vs,Is):send_end_quan) and
      re = ((VR,IR):recei_end_quan) and
      tlc = ((R,L,Ca,G):trans_lines_const) in
    kcl_implem_1a MediumTL_TCir se re tlc (w:real) z =
	(Is z = (Cx w * Cx Ca) * VR z + IR z + (Cx w * Cx Ca) * (imped_volt_med IR R L w) z)`,

LET_TAC THEN REWRITE_TAC [MEDIUM_TL_NOMINAL_T_KCL_ALT]);;


(*---------------------------------------------------------------------------*)
(*     Verification of the Medium Transmission Lines (Nominal T Circuit)     *)
(*---------------------------------------------------------------------------*)

let MEDIUM_TL_NOMINAL_T_KVL_KCL_IMP_IMPLEM_ALT = prove(
`!VR Vs IR Is R L Ca G w z.
    ((kvl_implem_1a MediumTL_TCir
      ((Vs,Is):send_end_quan) ((VR,IR):recei_end_quan)
            ((R,L,Ca,G):trans_lines_const) w z) /\
    (kcl_implem_1a MediumTL_TCir
      ((Vs,Is):send_end_quan) ((VR,IR):recei_end_quan)
              ((R,L,Ca,G):trans_lines_const)) (w:real) z)  =
    ((Vs z  = (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&2)) * VR z +
               (Cx R + ii * Cx w * Cx L) *
	        (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&4)) * IR z) /\
     (Is z = (Cx w * Cx Ca) * VR z +
              (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&2)) * IR z))`,

REPEAT GEN_TAC THEN
  SIMP_TAC [MEDIUM_TL_NOMINAL_T_KVL_ALT; MEDIUM_TL_NOMINAL_T_KCL_ALT;imped_volt_med]
   THEN CONV_TAC COMPLEX_FIELD);;



let MEDIUM_TL_NOMINAL_T_KVL_KCL_IMP_IMPLEM = prove(
`!VR Vs IR Is R L Ca G w z.
  let se = ((Vs,Is):send_end_quan) and
      re = ((VR,IR):recei_end_quan) and
      tlc = ((R,L,Ca,G):trans_lines_const) in
    ((kvl_implem_1a MediumTL_TCir se re tlc w z) /\
    (kcl_implem_1a MediumTL_TCir se re tlc (w:real) z))  =
    ((Vs z  = (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&2)) * VR z +
               (Cx R + ii * Cx w * Cx L) *
	        (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&4)) * IR z) /\
     (Is z = (Cx w * Cx Ca) * VR z +
              (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&2)) * IR z))`,

LET_TAC THEN REWRITE_TAC [MEDIUM_TL_NOMINAL_T_KVL_KCL_IMP_IMPLEM_ALT]);;


(*--------------------------------------------------------------------------*)

let MEDIUM_TL_NOMINAL_T_IMPLEM_EQ_MAT_REP_ALT1_ALT = prove(
`!Vs Is VR IR R L Ca G w z.
  valid_transmission_line (MediumTL_TCir,(R,L,Ca,G))
  ==> ((kvl_implem_1a MediumTL_TCir (Vs,Is) (VR,IR) (R,L,Ca,G) w z) /\
       (kcl_implem_1a MediumTL_TCir (Vs,Is) (VR,IR) (R,L,Ca,G) w z))
     = (relat_send_receiv_quan_1a MediumTL_TCir ((Vs,Is):send_end_quan)
            ((VR,IR):recei_end_quan) ((R,L,Ca,G):trans_lines_const) w z)`,

REWRITE_TAC [valid_transmission_line] THEN
 REPEAT STRIP_TAC THEN
  REWRITE_TAC [MEDIUM_TL_NOMINAL_T_KVL_KCL_IMP_IMPLEM_ALT;relat_send_receiv_quan_1a;
   send_end_vec; abcd_mat_1a; recei_end_vec;MAT2x2_MUL_VEC2;CVECTOR2_EQ]
   THEN CONV_TAC COMPLEX_FIELD);;


let MEDIUM_TL_NOMINAL_T_IMPLEM_EQ_MAT_REP_ALT1 = prove(
`!Vs Is VR IR R L Ca G w z.
  let se = ((Vs,Is):send_end_quan) and
      re = ((VR,IR):recei_end_quan) and
      tlc = ((R,L,Ca,G):trans_lines_const) in
  valid_transmission_line (MediumTL_TCir,tlc)
  ==> ((kvl_implem_1a MediumTL_TCir se re tlc w z) /\
       (kcl_implem_1a MediumTL_TCir se re tlc w z))
     = (relat_send_receiv_quan_1a MediumTL_TCir se re tlc w z)`,

LET_TAC THEN REWRITE_TAC [MEDIUM_TL_NOMINAL_T_IMPLEM_EQ_MAT_REP_ALT1_ALT]);;



(*--------------------------------------------------------------------------*)

let ABCD_PAR_MEDIUM_TL_NOMIN_T_CIRC_ALT = prove(
`!Vs Is VR IR A B C D R L Ca G w z.
     A = (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&2)) /\
     B = ((Cx R + ii * Cx w * Cx L) *
           (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&4))) /\
     C = (Cx w * Cx Ca) /\
     D = (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&2))
      ==> ((relat_send_receiv_quan_gen ((Vs,Is):send_end_quan)
            ((VR,IR):recei_end_quan) ((A,B,C,D):abcd_param) z) =
          (relat_send_receiv_quan_1a MediumTL_TCir
	    (Vs,Is) (VR,IR) (R,L,Ca,G) w z))`, 

REPEAT STRIP_TAC THEN
 REWRITE_TAC [relat_send_receiv_quan_gen; relat_send_receiv_quan_1a;abcd_mat_gen; abcd_mat_1a]
 THEN ASM_SIMP_TAC []);;



let ABCD_PAR_MEDIUM_TL_NOMIN_T_CIRC = prove(
`!Vs Is VR IR A B C D R L Ca G w z.
  let se = ((Vs,Is):send_end_quan) and
      re = ((VR,IR):recei_end_quan) and
      tlc = ((R,L,Ca,G):trans_lines_const) and
      abcd = ((A,B,C,D):abcd_param) in
     A = (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&2)) /\
     B = ((Cx R + ii * Cx w * Cx L) *
           (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&4))) /\
     C = (Cx w * Cx Ca) /\
     D = (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&2))
      ==> ((relat_send_receiv_quan_gen se re abcd z) =
          (relat_send_receiv_quan_1a MediumTL_TCir se re tlc w z))`, 

LET_TAC THEN REWRITE_TAC [ABCD_PAR_MEDIUM_TL_NOMIN_T_CIRC_ALT]);;



let ABCD_PAR_EQ_IMPLEM_MEDIUM_TL_NOMIN_T_CIRC_ALT = prove(
`!Vs Is VR IR A B C D R L Ca G w z.
     valid_transmission_line (MediumTL_TCir,((R,L,Ca,G):trans_lines_const)) /\
     A = (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&2)) /\
     B = ((Cx R + ii * Cx w * Cx L) *
           (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&4))) /\
     C = (Cx w * Cx Ca) /\
     D = (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&2))
      ==> ((relat_send_receiv_quan_gen ((Vs,Is):send_end_quan)
            ((VR,IR):recei_end_quan) ((A,B,C,D):abcd_param) z) =
          ((kvl_implem_1a MediumTL_TCir (Vs,Is) (VR,IR) (R,L,Ca,G) w z) /\
	   (kcl_implem_1a MediumTL_TCir (Vs,Is) (VR,IR) (R,L,Ca,G) w z)))`,

REPEAT STRIP_TAC THEN
 SUBGOAL_THEN `((kvl_implem_1a MediumTL_TCir (Vs,Is) (VR,IR) (R,L,Ca,G) w z) /\
       (kcl_implem_1a MediumTL_TCir (Vs,Is) (VR,IR) (R,L,Ca,G) w z))
     = (relat_send_receiv_quan_1a MediumTL_TCir (Vs,Is) (VR,IR) (R,L,Ca,G) w z)` ASSUME_TAC
     THENL [MATCH_MP_TAC MEDIUM_TL_NOMINAL_T_IMPLEM_EQ_MAT_REP_ALT1_ALT THEN
      ASM_SIMP_TAC [];ALL_TAC] THEN
  ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
   ASM_SIMP_TAC [ABCD_PAR_MEDIUM_TL_NOMIN_T_CIRC_ALT]);;



let ABCD_PAR_EQ_IMPLEM_MEDIUM_TL_NOMIN_T_CIRC = prove(
`!Vs Is VR IR A B C D R L Ca G w z.
  let se = ((Vs,Is):send_end_quan) and
      re = ((VR,IR):recei_end_quan) and
      tlc = ((R,L,Ca,G):trans_lines_const) and
      abcd = ((A,B,C,D):abcd_param) in
     valid_transmission_line (MediumTL_TCir,tlc) /\
     A = (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&2)) /\
     B = ((Cx R + ii * Cx w * Cx L) *
           (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&4))) /\
     C = (Cx w * Cx Ca) /\
     D = (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&2))
      ==> ((relat_send_receiv_quan_gen se re abcd z) =
          ((kvl_implem_1a MediumTL_TCir se re tlc w z) /\
	   (kcl_implem_1a MediumTL_TCir se re tlc w z)))`,

LET_TAC THEN REWRITE_TAC [ABCD_PAR_EQ_IMPLEM_MEDIUM_TL_NOMIN_T_CIRC_ALT]);;


let ABCD_PAR_RELAT_MEDIUM_TL_NOMIN_T_CIRC = prove(
`!A B C D R L Ca G w.
     A = (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&2)) /\
     B = ((Cx R + ii * Cx w * Cx L) *
           (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&4))) /\
     C = (Cx w * Cx Ca) /\
     D = (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&2))
      ==> ((A * D - B * C) = Cx (&1))`,

REPEAT STRIP_TAC THEN ASM_SIMP_TAC [] 
 THEN CONV_TAC COMPLEX_FIELD);;

 

let ABCD_PAR_RELAT2_MEDIUM_TL_NOMIN_T_CIRC = prove(
`!A B C D R L Ca G w.
     A = (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&2)) /\
     B = ((Cx R + ii * Cx w * Cx L) *
           (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&4))) /\
     C = (Cx w * Cx Ca) /\
     D = (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&2))
      ==> (A = D)`,

REPEAT STRIP_TAC THEN
ASM_SIMP_TAC []);;


(*--------------------------------------------------------------------------*)

new_type_abbrev ("w",`:real`);;

new_type_abbrev 
     ("tl_models_param",`: tl_models # trans_lines_const`);;

new_type_abbrev ("tl_models_param_all",`:tl_models_param list # w`);;

(*======================================================================*)

let cidentity_mat = new_definition
   `cidentity_mat =
       (vector [vector [Cx (&1); Cx (&0)];
        vector [Cx (&0); Cx (&1)]]):complex^2^2`;;

let COMPLEX_CART_EQ = prove
  (`!x y:complex^N. x = y <=> !i. 1 <= i /\ i <= dimindex (:N) ==> x$i = y$i`,
  REWRITE_TAC[CART_EQ]);;

let CCOMMON_TAC xs =
  SIMP_TAC (xs @ [cmatrix_cvector_mul;COMPLEX_CART_EQ;LAMBDA_BETA;
           CART_EQ;VECTOR_2;DIMINDEX_2;FORALL_2;DOT_2;VSUM_2]);;

let CMAT_MUL_LID = prove(
`!(A:complex^2^2). A ** cidentity_mat = A`,

GEN_TAC THEN REWRITE_TAC [cidentity_mat] THEN
CCOMMON_TAC[cmatrix_mul;VECTOR_2;VECTOR_1;LAMBDA_BETA;COMPLEX_MUL_LID;
            COMPLEX_MUL_RID;COMPLEX_MUL_LZERO;COMPLEX_MUL_RZERO;COMPLEX_ADD_LID;
           COMPLEX_ADD_RID]);;

 
let CMAT_CMAT_MUL = prove
  (`!a b c d p q r (s:complex).
    ((vector [vector [a;b]; vector [c;d]]):complex^2^2) ** ((vector [vector [p;q]; vector [r;s]]):complex^2^2) =
      ((vector [vector [a * p + b * r; a * q + b * s]; vector [c * p + d * r; c * q + d * s]]):complex^2^2)`,

CCOMMON_TAC[cmatrix_mul;VECTOR_2;VECTOR_1;LAMBDA_BETA]);;

let CVECTOR2_EQ = prove
  (`!x y z t:complex. vector [x;y] :complex^2 = vector [z;t] <=> x=z /\ y=t`,
  CCOMMON_TAC[]);;

let CMAT2_EQ = prove
  (`!a b c d p q r (s:complex).
       ((vector [vector [a;b]; vector [c;d]]):complex^2^2) =
       ((vector [vector [p;q]; vector [r;s]]):complex^2^2) <=>
                a = p /\ b = q /\ c = r /\ d = s`,
  CCOMMON_TAC [] THEN CONV_TAC TAUT);;  


(*======================================================================*)
(* The following definition models the cascaded transmission lines.
    It accepts list of parameters of all tranmsision lines that are
     cascaded, i.e., the type "tl_models_param_all" and define the
      cascaded ABCD matrices in term of base case and the induction
       case. For the base case, i.e., no cascaded case, it gives the
        identity matrix, which provides the same output vector
	 corresponding to the input vector. It means that we don't have
	  any transmission line.                                        *)
(*----------------------------------------------------------------------*)
	
let cascaded_abcd_matrix_1a = define 
  `cascaded_abcd_matrix_1a ([],w) = cidentity_mat /\ 
   cascaded_abcd_matrix_1a (CONS (tlms,(R,L,Ca,G)) tlmpa,w) =
   (abcd_mat_1a tlms (R,L,Ca,G) w) ** 
     cascaded_abcd_matrix_1a (tlmpa,w)`;;

(*======================================================================*)
(*     Verification of the ABCD matrix for the cascaded two-ports
	        a Medium line pi circuit model is cascaded with a
	             short line series impedence model                  *)
(*----------------------------------------------------------------------*)

(*---------------------------------------------------------------------------*)
(*               Validity of a Cascaded Transmission Line                    *)
(*---------------------------------------------------------------------------*)

	
let valid_cascaded_tl_model_1b = define 
  `valid_cascaded_tl_model_1b ([],w) = T /\ 
   (valid_cascaded_tl_model_1b (CONS (tlms,tlc) tlmpa,w) =
   ((valid_transm_line_model1a tlms) /\
     (valid_cascaded_tl_model_1b (tlmpa,w))))`;;

	
let valid_cascaded_tl_const_1b = define 
  `valid_cascaded_tl_const_1b ([],w) = T /\ 
   (valid_cascaded_tl_const_1b (CONS (tlms,tlc) tlmpa,w) =
   ((valid_tl_const tlc) /\
     (valid_cascaded_tl_const_1b (tlmpa,w))))`;;


let valid_cascaded_tl_1b = define 
  `valid_cascaded_tl_1b (l:tl_models_param_all) =
    (valid_cascaded_tl_model_1b l /\ valid_cascaded_tl_const_1b l)`;;


(*---------------------------------------------------------------------------*)

let VALID_CASCADED_TL_MODEL_ALT = prove(
`!Ca1 Ca2 G1 G2 L1 L2 R1 R2 w.
   valid_cascaded_tl_model_1b ([MediumTL_PiCir,(R1,L1,Ca1,G1);
                             ShortTL_SerImp,(R2,L2,Ca2,G2)], w) = T`,

REPEAT GEN_TAC THEN
 REWRITE_TAC [valid_cascaded_tl_model_1b;valid_transm_line_model1a]);;

 
let VALID_CASCADED_TL_MODEL = prove(
 `! R1 R2 L1 L2 Ca1 Ca2 G1 G2 w.
  let tlc1 = (R1,L1,Ca1,G1) and
      tlc2 = (R2,L2,Ca2,G2) in
   valid_cascaded_tl_model_1b ([MediumTL_PiCir,tlc1;
                             ShortTL_SerImp,tlc2], w) = T`,

LET_TAC THEN REWRITE_TAC [VALID_CASCADED_TL_MODEL_ALT]);;


let VALID_CASCADED_TL_CONST_ALT = prove(
`!Ca1 Ca2 G1 G2 L1 L2 R1 R2 w.
   valid_cascaded_tl_const_1b ([MediumTL_PiCir,(R1,L1,Ca1,G1);
                                ShortTL_SerImp,(R2,L2,Ca2,G2)], w) =
		(&0 < R1 /\ &0 < L1 /\ &0 < Ca1 /\ &0 < G1 /\
		 &0 < R2 /\ &0 < L2 /\ &0 < Ca2 /\ &0 < G2)`,

REPEAT GEN_TAC THEN
 REWRITE_TAC [valid_cascaded_tl_const_1b;valid_tl_const] THEN CONV_TAC REAL_FIELD);;


let VALID_CASCADED_TL_CONST = prove(
`! R1 R2 L1 L2 Ca1 Ca2 G1 G2 w.
  let tlc1 = (R1,L1,Ca1,G1) and
      tlc2 = (R2,L2,Ca2,G2) in
   valid_cascaded_tl_const_1b ([MediumTL_PiCir,(R1,L1,Ca1,G1);
                                ShortTL_SerImp,(R2,L2,Ca2,G2)], w) =
		(&0 < R1 /\ &0 < L1 /\ &0 < Ca1 /\ &0 < G1 /\
		 &0 < R2 /\ &0 < L2 /\ &0 < Ca2 /\ &0 < G2)`,

LET_TAC THEN REWRITE_TAC [VALID_CASCADED_TL_CONST_ALT]);;



let VALID_CASCADED_TL_ALT = prove(
`!Ca1 Ca2 G1 G2 L1 L2 R1 R2 w.
   valid_cascaded_tl_1b ([MediumTL_PiCir,(R1,L1,Ca1,G1);
                             ShortTL_SerImp,(R2,L2,Ca2,G2)], w) =
	        (&0 < R1 /\ &0 < L1 /\ &0 < Ca1 /\ &0 < G1 /\
		 &0 < R2 /\ &0 < L2 /\ &0 < Ca2 /\ &0 < G2)`,

REPEAT GEN_TAC THEN REWRITE_TAC [valid_cascaded_tl_1b;VALID_CASCADED_TL_MODEL_ALT; VALID_CASCADED_TL_CONST_ALT]);;

 

let VALID_CASCADED_TL = prove(
`! R1 R2 L1 L2 Ca1 Ca2 G1 G2 w.
  let tlc1 = (R1,L1,Ca1,G1) and
      tlc2 = (R2,L2,Ca2,G2) in
   valid_cascaded_tl_1b ([MediumTL_PiCir,(R1,L1,Ca1,G1);
                                ShortTL_SerImp,(R2,L2,Ca2,G2)], w) =
		(&0 < R1 /\ &0 < L1 /\ &0 < Ca1 /\ &0 < G1 /\
		 &0 < R2 /\ &0 < L2 /\ &0 < Ca2 /\ &0 < G2)`,

LET_TAC THEN REWRITE_TAC [VALID_CASCADED_TL_ALT]);;

 
(*---------------------------------------------------------------------------*)

let ABCD_MAT_CASCADED_TWO_PORT_ALT = prove(
`! R1 R2 L1 L2 Ca1 Ca2 G1 G2 w.
   cascaded_abcd_matrix_1a ([MediumTL_PiCir,(R1,L1,Ca1,G1);
                             ShortTL_SerImp,(R2,L2,Ca2,G2)], w) =
      (vector [vector [Cx (&1) + ((Cx w * Cx Ca1) * (Cx R1 + ii * Cx w * Cx L1)) / Cx (&2);
               ((Cx (&1) + ((Cx w * Cx Ca1) * (Cx R1 + ii * Cx w * Cx L1)) / Cx (&2)) *
	        (Cx R2 + ii * Cx w * Cx L2)) +
		 (Cx R1 + ii * Cx w * Cx L1)];
	       vector [((Cx w * Cx Ca1) *
                       (Cx (&1) + ((Cx w * Cx Ca1) * (Cx R1 + ii * Cx w * Cx L1)) / Cx (&4)));
	       (((Cx w * Cx Ca1) *
                 (Cx (&1) + ((Cx w * Cx Ca1) * (Cx R1 + ii * Cx w * Cx L1)) / Cx (&4))) *
                (Cx R2 + ii * Cx w * Cx L2)) +
		(Cx (&1) + ((Cx w * Cx Ca1) * (Cx R1 + ii * Cx w * Cx L1)) / Cx (&2))]]):complex^2^2`,

REPEAT GEN_TAC THEN
 REWRITE_TAC [cascaded_abcd_matrix_1a;abcd_mat_1a;CMAT_MUL_LID;CMAT_CMAT_MUL;CMAT2_EQ]
 THEN CONV_TAC COMPLEX_FIELD);;

 
let ABCD_MAT_CASCADED_TWO_PORT = prove(
`! R1 R2 L1 L2 Ca1 Ca2 G1 G2 w.
  let tlc1 = (R1,L1,Ca1,G1) and
      tlc2 = (R2,L2,Ca2,G2) in
   cascaded_abcd_matrix_1a ([MediumTL_PiCir,tlc1;
                             ShortTL_SerImp,tlc2], w) =
      (vector [vector [Cx (&1) + ((Cx w * Cx Ca1) * (Cx R1 + ii * Cx w * Cx L1)) / Cx (&2);
               ((Cx (&1) + ((Cx w * Cx Ca1) * (Cx R1 + ii * Cx w * Cx L1)) / Cx (&2)) *
	        (Cx R2 + ii * Cx w * Cx L2)) +
		 (Cx R1 + ii * Cx w * Cx L1)];
	       vector [((Cx w * Cx Ca1) *
                       (Cx (&1) + ((Cx w * Cx Ca1) * (Cx R1 + ii * Cx w * Cx L1)) / Cx (&4)));
	       (((Cx w * Cx Ca1) *
                 (Cx (&1) + ((Cx w * Cx Ca1) * (Cx R1 + ii * Cx w * Cx L1)) / Cx (&4))) *
                (Cx R2 + ii * Cx w * Cx L2)) +
		(Cx (&1) + ((Cx w * Cx Ca1) * (Cx R1 + ii * Cx w * Cx L1)) / Cx (&2))]]):complex^2^2`,

LET_TAC THEN REWRITE_TAC [ABCD_MAT_CASCADED_TWO_PORT_ALT]);;


(*---------------------------------------------------------------------------*)
(*          Case Study: Wireless Power Transfer (WPT) System                 *)
(*---------------------------------------------------------------------------*)
(*---------------------------------------------------------------------------*)
(*                                    KCL                                    *)
(*---------------------------------------------------------------------------*)

let imped_volt_wpt = new_definition
      `imped_volt_wpt (R:real) Lk Ca w (Iz:vol_fun) = 
               (\z. (Cx R + ii * Cx w * Cx Lk + (Cx (&1) / (ii * Cx w * Cx Ca))) * (Iz z))`;;


let kcl_implem_wpt = define `
    (kcl_implem_wpt MediumTL_TCir
             (Vs,Is) (VR,IR) (R,L,Ca,G) M12 Lk w z =
	 (kcl [(\z. Is z);
	    (induct_curr (imped_volt_wpt R Lk Ca w (\z. --(IR z))) M12 w);
            (induct_curr (\z. --(VR z)) M12 w);
		         (\z. --(IR z))] z))`;;

(*---------------------------------------------------------------------------*)
(*                      KCL Implementation Equivalence                       *)
(*---------------------------------------------------------------------------*)

let WPT_KCL_NEW_ALT = prove(
`!Vs Is VR IR Ca G L R M12 Lk w z.
   kcl_implem_wpt MediumTL_TCir
        ((Vs,Is):send_end_quan) ((VR,IR):recei_end_quan)
         ((R,L,Ca,G):trans_lines_const) M12 Lk (w:real) z =
	    (Is z  = Cx (&1) / (ii * Cx w * Cx M12) * VR z +
 (Cx (&1) +
  (Cx R + ii * Cx w * Cx Lk + (Cx (&1) / (ii * Cx w * Cx Ca))) /
  (ii * Cx w * Cx M12)) *
 IR z)`,


 REPEAT GEN_TAC THEN
  REWRITE_TAC [kcl_implem_wpt; kcl] THEN
   REWRITE_TAC [LENGTH] THEN
    SIMP_TAC [GSYM ONE; GSYM TWO; GSYM THREE; SUC_SUB1] THEN
     SIMP_TAC [VSUM_4_LIST] THEN
   REWRITE_TAC [imped_volt_wpt; induct_curr] THEN
   CONV_TAC COMPLEX_FIELD);;

(*---------------------------------------------------------------------------*)
(*---------------------------------------------------------------------------*)

let kvl_implem_wpt_loop1 = define `
   (kvl_implem_wpt_loop1 MediumTL_TCir
       ((Vs,Is):send_end_quan) ((VR,IR):recei_end_quan)
            ((R,L,Ca,G):trans_lines_const) Vm Lk w z =
	    (kvl [(\z. Vs z);
		  (\z. --(Vm z));
	          resis_volt R (\z. --(Is z));
		  induct_volt Lk w (\z. --(Is z));
		  capacit_volt (\z. --(Is z)) Ca w] z))`;;

let kvl_implem_wpt_loop2 = define `
   (kvl_implem_wpt_loop2 MediumTL_TCir
       ((Vs,Is):send_end_quan) ((VR,IR):recei_end_quan)
            ((R,L,Ca,G):trans_lines_const) Vm Lk w z =
	    (kvl [(\z. Vm z);
		  (\z. --(VR z));
	          resis_volt R (\z. --(IR z));
		  induct_volt Lk w (\z. --(IR z));
		  capacit_volt (\z. --(IR z)) Ca w] z))`;;

(*---------------------------------------------------------------------------*)
(*                      KVL Implementation Equivalence                       *)
(*---------------------------------------------------------------------------*)

 let WPT_KVL_LOOP1_ALT = prove(
 `!Vs Is VR IR Vm Vy R L Ca G Lk w z.
   kvl_implem_wpt_loop1 MediumTL_TCir
      ((Vs,Is):send_end_quan) ((VR,IR):recei_end_quan)
          ((R,L,Ca,G):trans_lines_const) (Vm:vol_fun) Lk w z =
	(Vs z = Vm z + Cx R * Is z
	              + (ii * Cx w * Cx Lk) * Is z
	            + (Cx (&1) / (ii * Cx w * Cx Ca)) * Is z)`,

REPEAT GEN_TAC THEN
 REWRITE_TAC [kvl_implem_wpt_loop1;kvl] THEN
  REWRITE_TAC [LENGTH] THEN
  SIMP_TAC [GSYM ONE; GSYM TWO; GSYM THREE; GSYM FOUR] THEN
  SIMP_TAC [SUC_SUB1;VSUM_5_LIST] THEN
  REWRITE_TAC [resis_volt; induct_volt; capacit_volt] THEN
    CONV_TAC COMPLEX_FIELD);;



let WPT_KVL_LOOP2_ALT = prove(
`!Vs Is VR IR Vm Vy R L Ca G Lk w z.
   kvl_implem_wpt_loop2 MediumTL_TCir
      ((Vs,Is):send_end_quan) ((VR,IR):recei_end_quan)
          ((R,L,Ca,G):trans_lines_const) (Vm:vol_fun) Lk w z =
	(Vm z = VR z + Cx R * IR z
	              + (ii * Cx w * Cx Lk) * IR z
	            + (Cx (&1) / (ii * Cx w * Cx Ca)) * IR z)`,

REPEAT GEN_TAC THEN
  REWRITE_TAC [kvl_implem_wpt_loop2;kvl;LENGTH] THEN
   SIMP_TAC [GSYM ONE; GSYM TWO; GSYM THREE; GSYM FOUR;SUC_SUB1;VSUM_5_LIST]
   THEN REWRITE_TAC [resis_volt; induct_volt; capacit_volt] THEN CONV_TAC COMPLEX_FIELD);;


let kvl_implem_wpt = define `
   (kvl_implem_wpt MediumTL_TCir
       (Vs,Is) (VR,IR) (R,L,Ca,G) Lk w z =
	    (kvl [(\z. Vs z);
	          resis_volt R (\z. --(Is z));
		  induct_volt Lk w (\z. --(Is z));
		  capacit_volt (\z. --(Is z)) Ca w;	    
		 (\z. --(VR z));
	          resis_volt R (\z. --(IR z));
		  induct_volt Lk w (\z. --(IR z));
		  capacit_volt (\z. --(IR z)) Ca w] z))`;;


let WPT_KVL_ALT = prove(
`!Vs Is VR IR R L Ca G Lk w z.
   kvl_implem_wpt MediumTL_TCir
   ((Vs,Is):send_end_quan) ((VR,IR):recei_end_quan)
            ((R,L,Ca,G):trans_lines_const) Lk w z =
 (Vs z = Cx R * Is z + (ii * Cx w * Cx Lk) * Is z
	             + (Cx (&1) / (ii * Cx w * Cx Ca)) * Is z
		     +  VR z + Cx R * IR z + (ii * Cx w * Cx Lk) * IR z
	             + (Cx (&1) / (ii * Cx w * Cx Ca)) * IR z)`,


REPEAT GEN_TAC THEN REWRITE_TAC [kvl_implem_wpt;kvl;LENGTH] THEN
 SIMP_TAC [GSYM ONE; GSYM TWO; GSYM THREE; GSYM FOUR; GSYM FIVE; GSYM SIX; GSYM SEVEN]
  THEN SIMP_TAC [SUC_SUB1;VSUM_8_LIST] THEN REWRITE_TAC [resis_volt; induct_volt; capacit_volt]
   THEN CONV_TAC COMPLEX_FIELD);;


let WPT_LOOP12_IMP_KVL_ALT = prove(
`!Vs Is VR IR Vm R L Ca G Lk w z.
   (kvl_implem_wpt_loop1 MediumTL_TCir
    ((Vs,Is):send_end_quan) ((VR,IR):recei_end_quan)
           ((R,L,Ca,G):trans_lines_const) (Vm:vol_fun) Lk w z) /\
   (kvl_implem_wpt_loop2 MediumTL_TCir
   ((Vs,Is):send_end_quan) ((VR,IR):recei_end_quan)
          ((R,L,Ca,G):trans_lines_const) (Vm:vol_fun) Lk w z) ==>
   (kvl_implem_wpt MediumTL_TCir
      ((Vs,Is):send_end_quan) ((VR,IR):recei_end_quan)
            ((R,L,Ca,G):trans_lines_const) Lk w z)`,

REPEAT GEN_TAC THEN
 REWRITE_TAC [WPT_KVL_LOOP1_ALT; WPT_KVL_LOOP2_ALT; WPT_KVL_ALT] THEN
 CONV_TAC COMPLEX_FIELD);;


(*---------------------------------------------------------------------------*)
(*                Verification of the WPT System (T Circuit)                 *)
(*---------------------------------------------------------------------------*)

let WPT_KVL_KCL_IMP_IMPLEM_NEW_ALT = prove(
`!VR Vs IR Is Vm R L Ca G Lk M12 w z.
    ((kvl_implem_wpt MediumTL_TCir
      ((Vs,Is):send_end_quan) ((VR,IR):recei_end_quan)
            ((R,L,Ca,G):trans_lines_const) Lk w z) /\
    (kcl_implem_wpt MediumTL_TCir
      ((Vs,Is):send_end_quan) ((VR,IR):recei_end_quan)
              ((R,L,Ca,G):trans_lines_const) M12 Lk (w:real) z))  =
    ((Vs z = Cx R * Is z + (ii * Cx w * Cx Lk) * Is z
	             + (Cx (&1) / (ii * Cx w * Cx Ca)) * Is z
		     +  VR z + Cx R * IR z + (ii * Cx w * Cx Lk) * IR z
	             + (Cx (&1) / (ii * Cx w * Cx Ca)) * IR z) /\
     (Is z = Cx (&1) / (ii * Cx w * Cx M12) * VR z +
         (Cx (&1) +
          (Cx R + ii * Cx w * Cx Lk + Cx (&1) / (ii * Cx w * Cx Ca)) /
          (ii * Cx w * Cx M12)) * IR z))`,

REPEAT GEN_TAC THEN SIMP_TAC [WPT_KVL_ALT; WPT_KCL_NEW_ALT]);;


(*--------------------------------------------------------------------------*)

let abcd_mat_wpt = define `
   (abcd_mat_wpt MediumTL_TCir ((R,L,Ca,G):trans_lines_const) Lk M12 w =
        ((vector [vector [(Cx (&1) + ((Cx R + (ii * Cx w * Cx Lk) + (Cx (&1) / (ii * Cx w * Cx Ca))) / (ii * Cx w * Cx M12)));
	                  ((Cx R + (ii * Cx w * Cx Lk) + (Cx (&1) / (ii * Cx w * Cx Ca))) *
	(Cx (&2) + ((Cx R + (ii * Cx w * Cx Lk) + (Cx (&1) / (ii * Cx w * Cx Ca))) / (ii * Cx w * Cx M12))))];
	          vector [(Cx (&1) / (ii * Cx w * Cx M12));
	       ((Cx (&1) + ((Cx R + (ii * Cx w * Cx Lk) + (Cx (&1) / (ii * Cx w * Cx Ca))) / (ii * Cx w * Cx M12))))]]):comp_mat))`;;


let relat_send_receiv_quan_wpt = define `
   (relat_send_receiv_quan_wpt MediumTL_TCir
      ((Vs,Is):send_end_quan) ((VR,IR):recei_end_quan)
        ((R,L,Ca,G):trans_lines_const) Lk M12 w z =
       ((send_end_vec ((Vs,Is):send_end_quan) z) =
          ((abcd_mat_wpt MediumTL_TCir ((R,L,Ca,G):trans_lines_const) Lk M12 w):comp_mat) **
	     (recei_end_vec ((VR,IR):recei_end_quan) z)))`;;

(*--------------------------------------------------------------------------*)

let WPT_IMPLEM_EQ_MAT_REP_ALT1_ALT = prove(
`!Vs Is VR IR Vm R L Ca G Lk M12 w z.
  valid_transmission_line (MediumTL_TCir,(R,L,Ca,G))
  /\ (kvl_implem_wpt MediumTL_TCir (Vs,Is) (VR,IR) (R,L,Ca,G) Lk w z) /\
       (kcl_implem_wpt MediumTL_TCir (Vs,Is) (VR,IR) (R,L,Ca,G) M12 Lk w z)
     ==> (relat_send_receiv_quan_wpt MediumTL_TCir ((Vs,Is):send_end_quan)
            ((VR,IR):recei_end_quan) ((R,L,Ca,G):trans_lines_const) Lk M12 w z)`,

REPEAT GEN_TAC THEN
  REWRITE_TAC [valid_transmission_line;WPT_KVL_KCL_IMP_IMPLEM_NEW_ALT;relat_send_receiv_quan_wpt;
    send_end_vec; abcd_mat_wpt; recei_end_vec;MAT2x2_MUL_VEC2;CVECTOR2_EQ] THEN
CONV_TAC COMPLEX_FIELD);;


let WPT_IMPLEM_EQ_MAT_REP_ALT1_ALT = prove(
`!Vs Is VR IR Vm R L Ca G Lk M12 w z.
  valid_transmission_line (MediumTL_TCir,(R,L,Ca,G))
  ==> ((kvl_implem_wpt MediumTL_TCir (Vs,Is) (VR,IR) (R,L,Ca,G) Lk w z) /\
       (kcl_implem_wpt MediumTL_TCir (Vs,Is) (VR,IR) (R,L,Ca,G) M12 Lk w z))
     = (relat_send_receiv_quan_wpt MediumTL_TCir ((Vs,Is):send_end_quan)
            ((VR,IR):recei_end_quan) ((R,L,Ca,G):trans_lines_const) Lk M12 w z)`,

REPEAT GEN_TAC THEN
 REWRITE_TAC [valid_transmission_line;WPT_KVL_KCL_IMP_IMPLEM_NEW_ALT;relat_send_receiv_quan_wpt;
  send_end_vec; abcd_mat_wpt; recei_end_vec;MAT2x2_MUL_VEC2;CVECTOR2_EQ] THEN
CONV_TAC COMPLEX_FIELD);;


let ABCD_PAR_WPT_ALT = prove(
`!Vs Is VR IR A B C D R L Ca G Lk M12 w z.
     A = (Cx (&1) +
       (Cx R + (ii * Cx w * Cx Lk) + Cx (&1) / (ii * Cx w * Cx Ca)) /
       (ii * Cx w * Cx M12)) /\
     B = ((Cx R + (ii * Cx w * Cx Lk) + Cx (&1) / (ii * Cx w * Cx Ca)) *
       (Cx (&2) +
        (Cx R + (ii * Cx w * Cx Lk) + Cx (&1) / (ii * Cx w * Cx Ca)) /
        (ii * Cx w * Cx M12))) /\
     C = (Cx (&1) / (ii * Cx w * Cx M12)) /\
     D = (Cx (&1) +
       (Cx R + (ii * Cx w * Cx Lk) + Cx (&1) / (ii * Cx w * Cx Ca)) /
       (ii * Cx w * Cx M12))
      ==> ((relat_send_receiv_quan_gen ((Vs,Is):send_end_quan)
            ((VR,IR):recei_end_quan) ((A,B,C,D):abcd_param) z) =
          (relat_send_receiv_quan_wpt MediumTL_TCir
	    (Vs,Is) (VR,IR) (R,L,Ca,G) Lk M12 w z))`, 

REPEAT STRIP_TAC THEN
  REWRITE_TAC [relat_send_receiv_quan_gen; relat_send_receiv_quan_wpt;abcd_mat_gen; abcd_mat_wpt]
   THEN ASM_SIMP_TAC []);;


(*--------------------------------------------------------------------------*)
(*                       End of the Verification                            *)
(*--------------------------------------------------------------------------*)