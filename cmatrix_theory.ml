(* ========================================================================= *)
(*                                                                           *)
(*                           COMPLEX MATRICES                                *)
(*                                                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Matrix notation. NB: an MxN matrix is of type 
                                           complex^N^M, not complex^M^N.     *)
(*                                                                           *)
(* ------------------------------------------------------------------------- *)

overload_interface ("--",`(cmatrix_neg):complex^N^M->complex^N^M`);;
overload_interface ("+",`(cmatrix_add):complex^N^M->complex^N^M->complex^N^M`);;
overload_interface ("-",`(cmatrix_sub):complex^N^M->complex^N^M->complex^N^M`);;

make_overloadable "**" `:A->B->C`;;

overload_interface ("**",`(cvector_cmatrix_mul):complex^M->complex^N^M->complex^N`);;
overload_interface ("**",`(cmatrix_mul):complex^N^M->complex^P^N->complex^P^M`);;
overload_interface ("**",`(cmatrix_vector_mul):complex^N^M->complex^N->complex^M`);;

parse_as_infix("%%%",(21,"right"));;

prioritize_complex();;

let cmatrix_cmul = new_definition
  `((%%%):complex->complex^N^M->complex^N^M) c A = lambda i j. c * A$i$j`;;

let cmatrix_neg = new_definition
  `!A:complex^N^M. --A = lambda i j. --(A$i$j)`;;

let cmatrix_add = new_definition
  `!A:complex^N^M B:complex^N^M. A + B = lambda i j. A$i$j + B$i$j`;;

let cmatrix_sub = new_definition
  `!A:complex^N^M B:complex^N^M. A - B = lambda i j. A$i$j - B$i$j`;;

let cmatrix_mul = new_definition
  `!A:complex^N^M B:complex^P^N.
        A ** B =
          lambda i j. vsum(1..dimindex(:N)) (\k. A$i$k * B$k$j)`;;

let cmatrix_cvector_mul = new_definition
  `!A:complex^N^M x:complex^N.
        A ** x = lambda i. vsum(1..dimindex(:N)) (\j. A$i$j * x$j)`;;

let cvector_cmatrix_mul = new_definition
  `!A:complex^N^M x:complex^M.
        x ** A = lambda j. vsum(1..dimindex(:M)) (\i. A$i$j * x$i)`;;

let cmat = new_definition
  `(cmat:complex->complex^N^M) k = lambda i j. if i = j then k else Cx (&0)`;;

let cmatrix_cnj = new_definition
 `(cmatrix_cnj:complex^N^M->complex^N^M) A = lambda i j. cnj(A$i$j)`;;


let ctransp = new_definition
  `(ctransp:complex^N^M->complex^M^N) A = lambda i j. A$j$i`;;

let conj_ctransp = new_definition
  `(conj_ctransp:complex^N^M->complex^M^N) A = lambda i j. cnj(A$j$i)`;;


let CMATRIX_CMUL_COMPONENT = prove
 (`!c A:complex^N^M i. (c %%% A)$i$j = c * A$i$j`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:M) /\ !A:complex^N^M. A$i = A$k`
  CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  SUBGOAL_THEN `?l. 1 <= l /\ l <= dimindex(:N) /\ !z:complex^N. z$j = z$l`
  CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  ASM_SIMP_TAC[cmatrix_cmul; CART_EQ; LAMBDA_BETA]);;

let CMATRIX_ADD_COMPONENT = prove
 (`!A B:complex^N^M i j. (A + B)$i$j = A$i$j + B$i$j`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:M) /\ !A:complex^N^M. A$i = A$k`
  CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  SUBGOAL_THEN `?l. 1 <= l /\ l <= dimindex(:N) /\ !z:complex^N. z$j = z$l`
  CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  ASM_SIMP_TAC[cmatrix_add; LAMBDA_BETA]);;

let CMATRIX_SUB_COMPONENT = prove
 (`!A B:complex^N^M i j. (A - B)$i$j = A$i$j - B$i$j`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:M) /\ !A:complex^N^M. A$i = A$k`
  CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  SUBGOAL_THEN `?l. 1 <= l /\ l <= dimindex(:N) /\ !z:complex^N. z$j = z$l`
  CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  ASM_SIMP_TAC[cmatrix_sub; LAMBDA_BETA]);;

let CMATRIX_NEG_COMPONENT = prove
 (`!A:complex^N^M i j. (--A)$i$j = --(A$i$j)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:M) /\ !A:complex^N^M. A$i = A$k`
  CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  SUBGOAL_THEN `?l. 1 <= l /\ l <= dimindex(:N) /\ !z:complex^N. z$j = z$l`
  CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  ASM_SIMP_TAC[cmatrix_neg; LAMBDA_BETA]);;

let CMAT_COMPONENT = prove
 (`!n i j.
        1 <= i /\ i <= dimindex(:M) /\
        1 <= j /\ j <= dimindex(:N)
        ==> (cmat n:complex^N^M)$i$j = if i = j then n else Cx (&0)`,
  SIMP_TAC[cmat; LAMBDA_BETA]);;

let CMAT_0_COMPONENT = prove
 (`!i j. (cmat (Cx(&0)):complex^N^M)$i$j = Cx (&0)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:M) /\ !A:complex^N^M. A$i = A$k`
  CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  SUBGOAL_THEN `?l. 1 <= l /\ l <= dimindex(:N) /\ !z:complex^N. z$j = z$l`
  CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  ASM_SIMP_TAC[cmat; COND_ID; LAMBDA_BETA]);;

let CMAT_CMUL = prove
 (`!a. (cmat a:complex^N^M) = a %%% (cmat (Cx(&1)):complex^N^M)`,
  SIMP_TAC[CART_EQ; CMAT_COMPONENT; CMATRIX_CMUL_COMPONENT] THEN
  MESON_TAC[COMPLEX_MUL_RID; COMPLEX_MUL_RZERO]);;

(* ------------------------------------------------------------------------- *)
(*                           Complex Product                                 *)
(* ------------------------------------------------------------------------- *)

let cproduct = new_definition
  `cproduct = iterate (( * ):complex->complex->complex)`;;


let CPRODUCT_EQ_0_NUMSEG = prove
 (`!f m n. cproduct(m..n) f = Cx(&0) <=> ?x. m <= x /\ x <= n /\ f(x) = Cx(&0)`,
  SIMP_TAC[CPRODUCT_EQ_0; FINITE_NUMSEG; IN_NUMSEG; GSYM CONJ_ASSOC]);;


let CPRODUCT_CLAUSES = prove
 (`(!f. cproduct {} f = Cx(&1)) /\
   (!x f s. FINITE(s)
            ==> (cproduct (x INSERT s) f =
                 if x IN s then cproduct s f else f(x) * cproduct s f))`,
  REWRITE_TAC[cproduct; GSYM NEUTRAL_COMPLEX_MUL] THEN
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  MATCH_MP_TAC ITERATE_CLAUSES THEN REWRITE_TAC[MONOIDAL_COMPLEX_MUL]);;


let CPRODUCT_SING = prove
 (`!f x. cproduct {x} f = f(x)`,
  SIMP_TAC[CPRODUCT_CLAUSES; FINITE_RULES; NOT_IN_EMPTY;
            COMPLEX_MUL_RID]);;


let CPRODUCT_SING_NUMSEG = prove
 (`!f n. cproduct(n..n) f = f(n)`,
  REWRITE_TAC[NUMSEG_SING; CPRODUCT_SING]);;


let CPRODUCT_CLAUSES_NUMSEG = prove
 (`(!m. cproduct(m..0) f = if m = 0 then f(0) else Cx(&1)) /\
   (!m n. cproduct(m..SUC n) f = if m <= SUC n then cproduct(m..n) f * f(SUC n)
                                else cproduct(m..n) f)`,
  REWRITE_TAC[NUMSEG_CLAUSES] THEN REPEAT STRIP_TAC THEN
  COND_CASES_TAC THEN
  ASM_SIMP_TAC[CPRODUCT_SING; CPRODUCT_CLAUSES; FINITE_NUMSEG; IN_NUMSEG] THEN
  REWRITE_TAC[ARITH_RULE `~(SUC n <= n)`; COMPLEX_MUL_AC]);;


let CPRODUCT_2 = prove
 (`!t. cproduct(1..2) t = t(1) * t(2)`,
  REWRITE_TAC[num_CONV `2`; CPRODUCT_CLAUSES_NUMSEG] THEN
  REWRITE_TAC[CPRODUCT_SING_NUMSEG; ARITH; COMPLEX_MUL_ASSOC]);;

let CPRODUCT_3 = prove
 (`!t. cproduct(1..3) t = t(1) * t(2) * t(3)`,
  REWRITE_TAC[num_CONV `3`; num_CONV `2`; CPRODUCT_CLAUSES_NUMSEG] THEN
  REWRITE_TAC[CPRODUCT_SING_NUMSEG; ARITH; COMPLEX_MUL_ASSOC]);;


(* ------------------------------------------------------------------------- *)
(*                       Complex Determinant & Properties                    *)
(* ------------------------------------------------------------------------- *)


let csign = new_definition
` (csign p):complex = if evenperm p then Cx(&1) else 
   -- Cx(&1)`;;


let CSIGN_I = prove
 (`csign I = Cx(&1)`,
  REWRITE_TAC[csign; EVENPERM_I]);;


 g`!(p:A->A) q. permutation p /\ permutation q ==> csign(p o q) = csign(p) * csign(q)`;;

e (SIMP_TAC[csign; EVENPERM_COMPOSE]);; 
e (REPEAT STRIP_TAC);;
e (COND_CASES_TAC);;
e (ASM_SIMP_TAC[]);;
e (COND_CASES_TAC);;
e (SIMPLE_COMPLEX_ARITH_TAC);;
e (SIMPLE_COMPLEX_ARITH_TAC);;
e ( UNDISCH_TAC ` ~(evenperm (p:A->A) <=> evenperm (q:A->A)) `);;
e (REPEAT COND_CASES_TAC);;
e (SIMPLE_COMPLEX_ARITH_TAC);;
e (SIMPLE_COMPLEX_ARITH_TAC);;
e (SIMPLE_COMPLEX_ARITH_TAC);;
e (SIMPLE_COMPLEX_ARITH_TAC);; 

let CSIGN_COMPOSE = top_thm();;


let CSIGN_SWAP = prove
 (`!a b. csign(swap(a,b)) = if a = b then Cx(&1) else -- Cx(&1)`,
  REWRITE_TAC[csign; EVENPERM_SWAP]);;
 

let cdet = new_definition
 `cdet (A:complex^N^N) =
        vsum { p | p permutes 1..dimindex(:N) }
            (\p. csign(p) * cproduct (1..dimindex(:N)) 
            (\i. A$i$(p i)))`;;


let diagonal_cmatrix = new_definition
 `diagonal_cmatrix (A:complex^N^M) <=>
        !i j. 1 <= i /\ i <= dimindex(:M) /\
              1 <= j /\ j <= dimindex(:N) /\
              ~(i = j)
              ==> A$i$j = Cx(&0)`;;


let lt_cmatrix = new_definition
 `lt_cmatrix (A:complex^N^M) <=>
               !i j. 1 <= i /\ i <= dimindex(:N) /\
               1 <= j /\ j <= dimindex(:N) /\ i < j
	       ==> (A$i$j) = Cx(&0)`;;


let ut_cmatrix = new_definition
 `ut_cmatrix(A:complex^N^M) <=>
               !i j. 1 <= i /\ i <= dimindex(:N) /\
               1 <= j /\ j <= dimindex(:N) /\ j < i
	       ==> A$i$j = Cx(&0)`;;


let CDET_LOWERTRIANGULAR = prove
 (`!A:complex^N^N.
        (!i j. 1 <= i /\ i <= dimindex(:N) /\
               1 <= j /\ j <= dimindex(:N) /\ i < j ==> A$i$j = Cx(&0))
        ==> cdet(A) = cproduct(1..dimindex(:N)) (\i. A$i$i)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cdet] THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `vsum {I}
     (\p. csign p * cproduct(1..dimindex(:N)) (\i. (A:complex^N^N)$i$p(i)))` THEN
  CONJ_TAC THENL
   [ALL_TAC; REWRITE_TAC[VSUM_SING; CSIGN_I; COMPLEX_MUL_LID; I_THM]] THEN
  MATCH_MP_TAC VSUM_SUPERSET THEN
  SIMP_TAC[IN_SING; FINITE_RULES; SUBSET; IN_ELIM_THM; PERMUTES_I] THEN
  X_GEN_TAC `p:num->num` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[COMPLEX_VEC_0;CPRODUCT_EQ_0_NUMSEG; COMPLEX_ENTIRE] THEN
  DISJ2_TAC THEN
  MP_TAC(SPECL [`p:num->num`; `1..dimindex(:N)`] PERMUTES_NUMSET_LE) THEN
  ASM_MESON_TAC[PERMUTES_IN_IMAGE; IN_NUMSEG; NOT_LT]);;



let CDET_UPPERTRIANGULAR = prove
 (`!A:complex^N^N.
        (!i j. 1 <= i /\ i <= dimindex(:N) /\
               1 <= j /\ j <= dimindex(:N) /\ j < i ==> A$i$j = Cx(&0))
        ==> cdet(A) = cproduct(1..dimindex(:N)) (\i. A$i$i)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cdet] THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `vsum {I}
     (\p. csign p * cproduct(1..dimindex(:N)) (\i. (A:complex^N^N)$i$p(i)))` THEN
  CONJ_TAC THENL
   [ALL_TAC; REWRITE_TAC[VSUM_SING; CSIGN_I; COMPLEX_MUL_LID; I_THM]] THEN
  MATCH_MP_TAC VSUM_SUPERSET THEN
  SIMP_TAC[IN_SING; FINITE_RULES; SUBSET; IN_ELIM_THM; PERMUTES_I] THEN
  X_GEN_TAC `p:num->num` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[COMPLEX_VEC_0; CPRODUCT_EQ_0_NUMSEG; COMPLEX_ENTIRE] THEN
  DISJ2_TAC THEN
  MP_TAC(SPECL [`p:num->num`; `1..dimindex(:N)`] PERMUTES_NUMSET_GE) THEN
  ASM_MESON_TAC[PERMUTES_IN_IMAGE; IN_NUMSEG; NOT_LT]);;


let CDET_DIAGONAL = prove
 (`!A:complex^N^N.
        diagonal_cmatrix A
        ==> cdet(A) = cproduct(1..dimindex(:N)) (\i. A$i$i)`,
  REWRITE_TAC[diagonal_cmatrix] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CDET_LOWERTRIANGULAR THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[LT_REFL]);;



let CDET_2 = prove
 (`!A:complex^2^2. cdet A = A$1$1 * A$2$2 - A$1$2 * A$2$1`,
  GEN_TAC THEN REWRITE_TAC[cdet; DIMINDEX_2] THEN
  CONV_TAC(LAND_CONV(RATOR_CONV(ONCE_DEPTH_CONV NUMSEG_CONV))) THEN
  SIMP_TAC [vsum;CART_EQ;LAMBDA_BETA] THEN REPEAT STRIP_TAC THEN
  SIMP_TAC[SUM_OVER_PERMUTATIONS_INSERT; FINITE_INSERT; FINITE_EMPTY;
           ARITH_EQ; IN_INSERT; NOT_IN_EMPTY] THEN
  REWRITE_TAC[PERMUTES_EMPTY; SUM_SING; SET_RULE `{x | x = a} = {a}`] THEN
  REWRITE_TAC[SWAP_REFL; I_O_ID] THEN
  REWRITE_TAC[GSYM(NUMSEG_CONV `1..2`); SUM_2] THEN
  REWRITE_TAC[CSIGN_SWAP; ARITH] THEN REWRITE_TAC[CPRODUCT_2] THEN
  REWRITE_TAC[o_THM; swap; ARITH] THEN 
  REWRITE_TAC[SIMPLE_COMPLEX_ARITH ` Cx(&1) * a * b = a * b`] THEN 
  REWRITE_TAC[GSYM VECTOR_ADD_COMPONENT] THEN REWRITE_TAC [GSYM COMPLEX_NEG_MINUS1] THEN
  REWRITE_TAC[GSYM complex_sub]);;



let CDET_3 = prove
 (`!A:complex^3^3.
       cdet(A) = A$1$1 * A$2$2 * A$3$3 +
                 A$1$2 * A$2$3 * A$3$1 +
                 A$1$3 * A$2$1 * A$3$2 -
                 A$1$1 * A$2$3 * A$3$2 -
                 A$1$2 * A$2$1 * A$3$3 -
                 A$1$3 * A$2$2 * A$3$1`,
  GEN_TAC THEN REWRITE_TAC[cdet; DIMINDEX_3] THEN
  CONV_TAC(LAND_CONV(RATOR_CONV(ONCE_DEPTH_CONV NUMSEG_CONV))) THEN
  SIMP_TAC [vsum;CART_EQ;LAMBDA_BETA] THEN REPEAT STRIP_TAC THEN
  SIMP_TAC[SUM_OVER_PERMUTATIONS_INSERT; FINITE_INSERT; FINITE_EMPTY;
           ARITH_EQ; IN_INSERT; NOT_IN_EMPTY] THEN
  REWRITE_TAC[PERMUTES_EMPTY; SUM_SING; SET_RULE `{x | x = a} = {a}`] THEN
  REWRITE_TAC[SWAP_REFL; I_O_ID] THEN
  REWRITE_TAC[GSYM(NUMSEG_CONV `1..3`); SUM_3] THEN
  SIMP_TAC[SUM_CLAUSES; FINITE_INSERT; FINITE_EMPTY;
           ARITH_EQ; IN_INSERT; NOT_IN_EMPTY] THEN
  SIMP_TAC[CSIGN_COMPOSE; PERMUTATION_SWAP] THEN
  REWRITE_TAC[CSIGN_SWAP; ARITH] THEN REWRITE_TAC[CPRODUCT_3] THEN
  REWRITE_TAC[o_THM; swap; ARITH] THEN REWRITE_TAC [COMPLEX_MUL_LID] THEN
  REWRITE_TAC [GSYM COMPLEX_NEG_MINUS1; COMPLEX_MUL_LID; COMPLEX_NEG_NEG] THEN 
  REWRITE_TAC[SIMPLE_COMPLEX_ARITH ` a + &0 = a`] THEN
  REWRITE_TAC[GSYM VECTOR_ADD_COMPONENT] THEN
  REWRITE_TAC[GSYM complex_sub] THEN
  REWRITE_TAC[SIMPLE_COMPLEX_ARITH ` -- a + b = b - a`] THEN
  REWRITE_TAC[SIMPLE_COMPLEX_ARITH ` A$1$1 * A$2$2 * A$3$3 -
  A$1$1 * A$2$3 * A$3$2 +
  A$1$2 * A$2$3 * A$3$1 - 
  A$1$2 * A$2$1 * A$3$3 +
  A$1$3 * A$2$1 * A$3$2 -
  A$1$3 * A$2$2 * A$3$1 = 
  A$1$1 * A$2$2 * A$3$3 +
  A$1$2 * A$2$3 * A$3$1 +
  A$1$3 * A$2$1 * A$3$2 -
  A$1$1 * A$2$3 * A$3$2 -
  A$1$2 * A$2$1 * A$3$3 -
  A$1$3 * A$2$2 * A$3$1`]);;


let MATRIX_2x2 = prove
(`! a b c d. (vector [vector [a; b] ; vector [ c; d]]:A^2^2)$1$1 = a /\
              (vector [vector [a; b] ; vector [c; d]]:A^2^2)$1$2 = b /\
              (vector [vector [a; b] ; vector [c; d]]:A^2^2)$2$1 = c /\
	      (vector [vector [a; b] ; vector [c; d]]:A^2^2)$2$2 = d `,
         SIMP_TAC [vector; LAMBDA_BETA; DIMINDEX_2; ARITH; LENGTH; EL; TL; HD] THEN
          REWRITE_TAC [ONE ;EL; TL; HD] THEN
         SIMP_TAC [LAMBDA_BETA; DIMINDEX_2; ARITH; LENGTH; EL; TL; HD] THEN
          REWRITE_TAC [ONE ;EL; TL; HD]);;
 

let MATRIX_3x3 = prove
(`! a b c d e f g h i. (vector [vector [a; b; c] ; vector [d; e; f]; vector [g; h; i]]:A^3^3)$1$1 = a /\
              (vector [vector [a; b; c] ; vector [d; e; f]; vector [g; h; i]]:A^3^3)$1$2 = b /\
              (vector [vector [a; b; c] ; vector [d; e; f]; vector [g; h; i]]:A^3^3)$1$3 = c /\
	      (vector [vector [a; b; c] ; vector [d; e; f]; vector [g; h; i]]:A^3^3)$2$1 = d /\ 
              (vector [vector [a; b; c] ; vector [d; e; f]; vector [g; h; i]]:A^3^3)$2$2 = e /\
              (vector [vector [a; b; c] ; vector [d; e; f]; vector [g; h; i]]:A^3^3)$2$3 = f /\
	      (vector [vector [a; b; c] ; vector [d; e; f]; vector [g; h; i]]:A^3^3)$3$1 = g /\
              (vector [vector [a; b; c] ; vector [d; e; f]; vector [g; h; i]]:A^3^3)$3$2 = h /\
              (vector [vector [a; b; c] ; vector [d; e; f]; vector [g; h; i]]:A^3^3)$3$3 = i `,
         SIMP_TAC [vector; LAMBDA_BETA; DIMINDEX_3; ARITH; LENGTH; EL; TL; HD] THEN
          REWRITE_TAC [TWO;ONE ;EL; TL; HD] THEN
         SIMP_TAC [LAMBDA_BETA; DIMINDEX_3; ARITH; LENGTH; EL; TL; HD] THEN
          REWRITE_TAC [TWO;ONE ;EL; TL; HD]);;


(* ------------------------------------------------------------------------- *)
(*                       Complex Vector & Properties                         *)
(* ------------------------------------------------------------------------- *)


parse_as_infix("cmult",(20,"right"));;

let cmult = new_definition
  `(cmult) (x:complex^N) (y:complex^N) =
    vsum (1..dimindex(:N)) (\i. x$i * y$i)`;;


let CMATRIX_CVECTOR_MUL_COMPONENT = prove
 (`!A:complex^N^M x k.
    1 <= k /\ k <= dimindex(:M) ==> ((A ** x)$k = (A$k) cmult x)`,
  SIMP_TAC[cmatrix_cvector_mul; LAMBDA_BETA; cmult]);;


let CMULT_1 = prove
 (`(x:complex^1) cmult (y:complex^1) = x$1 * y$1`,
  REWRITE_TAC[cmult; DIMINDEX_1; VSUM_1]);;

let CMULT_2 = prove
 (`(x:complex^2) cmult (y:complex^2) = x$1 * y$1 + x$2 * y$2`,
  REWRITE_TAC[cmult; DIMINDEX_2; VSUM_2]);;

let CMULT_3 = prove
 (`(x:complex^3) cmult (y:complex^3) = x$1 * y$1 + x$2 * y$2 + x$3 * y$3`,
  REWRITE_TAC[cmult; DIMINDEX_3; VSUM_3]);;

let CMULT_4 = prove
 (`(x:complex^4) cmult (y:complex^4) =  
     x$1 * y$1 + x$2 * y$2 + x$3 * y$3 + x$4 * y$4`,
  REWRITE_TAC[cmult; DIMINDEX_4; VSUM_4]);;

let CVEC_CMAT_SIMP_TAC xs =
  SIMP_TAC (xs @ [CART_EQ;VECTOR_1;VECTOR_2;VECTOR_3;VECTOR_4; 
                       DIMINDEX_1;DIMINDEX_2;DIMINDEX_3;DIMINDEX_4;
                         FORALL_1; FORALL_2;FORALL_3;FORALL_4;
			 CMULT_1;CMULT_2;CMULT_3;CMULT_4;
                           VSUM_1;VSUM_2;VSUM_3;VSUM_4]);;

(* -------------------------------------------------------------------------------- *)

