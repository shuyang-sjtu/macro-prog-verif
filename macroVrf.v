Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import omega.Omega.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
Import ListNotations.

Definition State := nat -> nat.

Module lang0.

Inductive EXP : Type :=
| Num  (n: nat)
| Poi  (loc: EXP)
| Plus (a1 a2: EXP)
| Minus(a1 a2: EXP)
| Mult (a1 a2: EXP)
| Eq   (a1 a2: EXP)
| Le   (a1 a2: EXP) (*<=*)
| Not  (a: EXP) (*0->1 x->0*)
| And  (a1 a2: EXP)
| Inv.

Coercion Num : nat >-> EXP.

Fixpoint EXP_eval (st : State) (a : EXP) : nat :=
match a with
| Num n => n
| Poi a1=> st (EXP_eval st a1)
| Plus a1 a2 => (EXP_eval st a1) + (EXP_eval st a2)
| Minus a1 a2 => (EXP_eval st a1) - (EXP_eval st a2)
| Mult a1 a2 => (EXP_eval st a1) * (EXP_eval st a2)
| Eq a1 a2 => if (EXP_eval st a1) =? (EXP_eval st a2) then 1 else 0
| Le a1 a2 => if (EXP_eval st a1) <=? (EXP_eval st a2) then 1 else 0
| Not a1 => if (EXP_eval st a1) =? 0 then 1 else 0
| And a1 a2 => if ((EXP_eval st a1) =? 0) || ((EXP_eval st a2) =? 0) then 0 else 1
| Inv => 0
end.

Example text_EXP_eval1:
  forall st: State, EXP_eval st (Minus (Mult (Num 2) (Num 4)) (Num 2)) = 6.
Proof. auto.  Qed.

Example text_EXP_eval2:
  forall st: State, EXP_eval st (Le (Mult (Num 2) (Num 4)) (Num 2)) = 0.
Proof. auto.  Qed.

Definition S_empty (v : nat) : nat -> nat :=
  (fun _ => v).

Definition S_update (m : nat -> nat)
                    (x : nat) (v : nat) :=
  fun x' => if x =? x' then v else m x'.

Notation "'_' '!->' v" := (S_empty v)
  (at level 100, right associativity).

Notation "x '!->' v ';' m" := (S_update m x v)
                              (at level 100, v at next level, right associativity).

Definition bool_to_EXP (b : bool) : EXP :=
if b then 1 else 0.
Coercion bool_to_EXP : bool >-> EXP.

Bind Scope lang0_scope with EXP.
Delimit Scope lang0_scope with lang0.

Notation "x + y" := (Plus x y) (at level 50, left associativity) : lang0_scope.
Notation "x - y" := (Minus x y) (at level 50, left associativity) : lang0_scope.
Notation "x * y" := (Mult x y) (at level 40, left associativity) : lang0_scope.
Notation "x <= y" := (Le x y) (at level 70, no associativity) : lang0_scope.
Notation "x = y" := (Eq x y) (at level 70, no associativity) : lang0_scope.
Notation "x && y" := (And x y) (at level 40, left associativity) : lang0_scope.
Notation "'~' b" := (Not b) (at level 75, right associativity) : lang0_scope.
Notation "^ b" := (Poi b) (at level 35, no associativity) : lang0_scope.

Definition example_EXP1 := (3 + ( ^ 1 * 2 )) %lang0 : EXP.

Example EXP_eva1 : 
  EXP_eval (S_empty 5) example_EXP1 = 13.
Proof.
 unfold example_EXP1.
 simpl. auto.
Qed.

Definition empty_st := (_ !-> 0).

Notation "a '!->' x" := (S_update empty_st a x) (at level 100).

Example AEXP1 :
    EXP_eval (1 !-> 5) (3 + (^1 * 2))%lang0
  = 13.
Proof. reflexivity. Qed.

Example BEXP1 :
    EXP_eval (1 !-> 5) (true && ~(^1 <= 4))%lang0
  = 1.
Proof. reflexivity. Qed.

Inductive COM : Type :=
  | Skip
  | Ass (x : EXP) (a : EXP)
  | Seq (c1 c2 : COM)
  | If (b : EXP) (c1 c2 : COM)
  | While (b : EXP) (c : COM)
  | Invc.

Bind Scope lang0_scope with COM.
Notation "'SKIP'" :=
   Skip : lang0_scope.
Notation "x '::=' a" :=
  (Ass x a) (at level 60) : lang0_scope.
Notation "c1 ;; c2" :=
  (Seq c1 c2) (at level 80, right associativity) : lang0_scope.
Notation "'WHILE' b 'DO' c 'END'" :=
  (While b c) (at level 80, right associativity) : lang0_scope.
Notation "'TEST' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (If c1 c2 c3) (at level 80, right associativity) : lang0_scope.

Definition W : EXP := ^0.
Definition X : EXP := ^1.
Definition Y : EXP := ^2.
Definition Z : EXP := ^3.

Definition fact_in_coq : COM :=
  (Z ::= X;;
  Y ::= 1;;
  WHILE ~(Z = 0) DO
    Y ::= Y * Z;;
    Z ::= Z - 1
  END)%lang0.

Print fact_in_coq.


Unset Printing Notations.
Print fact_in_coq.
(* ===>
   fact_in_coq =
   CSeq (CAss Z X)
        (CSeq (CAss Y (S O))
              (CWhile (BNot (BEq Z O))
                      (CSeq (CAss Y (AMult Y Z))
                            (CAss Z (AMinus Z (S O))))))
        : com *)
Set Printing Notations.

Set Printing Coercions.
Print fact_in_coq.
(* ===>
   fact_in_coq =
   (Z ::= AId X;;
   Y ::= ANum 1;;
   WHILE ~ (AId Z = ANum 0) DO
     Y ::= AId Y * AId Z;;
     Z ::= AId Z - ANum 1
   END)%imp
       : com *)
Unset Printing Coercions.

Locate "&&".

Locate EXP.

Definition plus2 : COM :=
  X ::= X + 2.

Definition XtimesYinZ : COM :=
  Z ::= X * Y.

Definition subtract_slowly_body : COM :=
  Z ::= Z - 1 ;;
  X ::= X - 1.

Definition subtract_slowly : COM :=
  (WHILE ~(X = 0) DO
    subtract_slowly_body
  END)%lang0.

Definition subtract_3_from_5_slowly : COM :=
  X ::= 3 ;;
  Z ::= 5 ;;
  subtract_slowly.

Definition loop : COM :=
  WHILE true DO
    SKIP
  END.

Open Scope lang0_scope.


Reserved Notation "st '=[[' c ']]=>' st'"
                  (at level 40).

Inductive COM_eval : COM -> State -> State -> Prop :=
  | E_Skip : forall st,
      st =[[ SKIP ]]=> st
  | E_Ass  : forall st a1 n x x0,
      EXP_eval st a1 = n ->
      EXP_eval st x = x0 ->
      st =[[ ^x ::= a1 ]]=> (x0 !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st  =[[ c1 ]]=> st'  ->
      st' =[[ c2 ]]=> st'' ->
      st  =[[ c1 ;; c2 ]]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      EXP_eval st b <> 0 ->
      st =[[ c1 ]]=> st' ->
      st =[[ TEST b THEN c1 ELSE c2 FI ]]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      EXP_eval st b = 0 ->
      st =[[ c2 ]]=> st' ->
      st =[[ TEST b THEN c1 ELSE c2 FI ]]=> st'
  | E_WhileFalse : forall b st c,
      EXP_eval st b = 0 ->
      st =[[ WHILE b DO c END ]]=> st
  | E_WhileTrue : forall st st' st'' b c,
      EXP_eval st b <> 0 ->
      st  =[[ c ]]=> st' ->
      st' =[[ WHILE b DO c END ]]=> st'' ->
      st  =[[ WHILE b DO c END ]]=> st''

  where "st =[[ c ]]=> st'" := (COM_eval c st st').

Close Scope lang0_scope.


Example COM_eval_example1:
  empty_st =[[
     X ::= 2;;
     TEST X <= 1
       THEN Y ::= 3
       ELSE Z ::= 4
     FI
  ]]=> (3 !-> 4 ; 1 !-> 2).
Proof.
  intros.
  apply E_Seq with (1 !-> 2).
  - apply E_Ass. simpl. reflexivity.
    simpl. auto.
  - apply E_IfFalse. simpl. auto. apply E_Ass; auto. 
Qed.


Module lang1.

Inductive exp : Type := 
| num (n: nat)
| poi (loc: exp)
| plus (a1 a2: exp)
| minus(a1 a2: exp)
| mult (a1 a2: exp)
| eq (a1 a2: exp)
| le (a1 a2: exp)
| not (a1: exp)
| and (a1 a2: exp)
| macro (macro_id: nat) (param : nat -> exp)
| inv.

Inductive com : Type :=
| skip
| ass (x : exp) (a : exp)
| seq (c1 c2 : com)
| iif (b : exp) (c1 c2 : com)
| while (b : exp) (c : com)
| cmacro (cmacro_id: nat) (param: nat -> exp) (cparam: nat -> com)
| invc.

Coercion num : nat >-> exp.

Definition bool_to_exp (b : bool) : exp :=
  if b then 1 else 0.
Coercion bool_to_exp : bool >-> exp.

Bind Scope lang1_scope with exp.
Delimit Scope lang1_scope with lang1.

Notation "x + y" := (plus x y) (at level 50, left associativity) : lang1_scope.
Notation "x - y" := (minus x y) (at level 50, left associativity) : lang1_scope.
Notation "x * y" := (mult x y) (at level 40, left associativity) : lang1_scope.
Notation "x <= y" := (le x y) (at level 70, no associativity) : lang1_scope.
Notation "x = y" := (eq x y) (at level 70, no associativity) : lang1_scope.
Notation "x && y" := (and x y) (at level 40, left associativity) : lang1_scope.
Notation "'~' b" := (not b) (at level 75, right associativity) : lang1_scope.
Notation "^ b" := (poi b) (at level 35, no associativity) : lang1_scope.

Bind Scope lang1_scope with com.
Notation "'SKIP'" :=
   skip : lang1_scope.
Notation "x '::=' a" :=
  (ass x a) (at level 60) : lang1_scope.
Notation "c1 ;; c2" :=
  (seq c1 c2) (at level 80, right associativity) : lang1_scope.
Notation "'WHILE' b 'DO' c 'END'" :=
  (while b c) (at level 80, right associativity) : lang1_scope.
Notation "'TEST' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (iif c1 c2 c3) (at level 80, right associativity) : lang1_scope.

Definition w : exp := ^0.
Definition x : exp := ^1.
Definition y : exp := ^2.
Definition z : exp := ^3.

Close Scope lang1_scope.

Definition example_aexp := (3 + (x * 2))%lang1 : exp.

Print example_aexp.


Module macro_lang.

Inductive exp_m : Type := 
| num_m (n: nat)
| poi_m (loc: exp_m)
| plus_m (a1 a2: exp_m)
| minus_m(a1 a2: exp_m)
| mult_m (a1 a2: exp_m)
| eq_m (a1 a2: exp_m)
| le_m (a1 a2: exp_m)
| not_m (a1: exp_m)
| and_m (a1 a2: exp_m)
| macro_m (macro_id: nat) (param : nat -> exp_m)
| param_m (n: nat)
| inv_m.

Inductive com_m : Type :=
| skip_m
| ass_m (x : exp_m) (a : exp_m)
| seq_m (c1 c2 : com_m)
| iif_m (b : exp_m) (c1 c2 : com_m)
| while_m (b : exp_m) (c : com_m)
| cmacro_m (cmacro_id: nat) (param: nat -> exp_m) (cparam: nat -> com_m)
| cparam_m (n: nat)
| invc_m.

Definition mstate : Type := (nat -> exp_m) * (nat -> com_m).

Definition EXP_params : Type := nat -> EXP.
Definition COM_params : Type := nat -> COM.
Definition exp_params : Type := nat -> exp.
Definition com_params : Type := nat -> com.
Definition exp_m_params : Type := nat -> exp_m.
Definition com_m_params : Type := nat -> com_m.

Module unfolding.

(**
Fixpoint unfold_macro_exp (m: mstate) (a: exp_m) (param : EXP_params) (tl : nat) : EXP :=
match a, tl with
| (num_m n), _ => Num n
| (poi_m loc),_ => Poi (unfold_macro_exp m loc param tl)
| (plus_m a1 a2),_ => (unfold_macro_exp m a1 param tl) + (unfold_macro_exp m a2 param tl)
| (minus_m a1 a2),_ => (unfold_macro_exp m a1 param tl) - (unfold_macro_exp m a2 param tl)
| (mult_m a1 a2),_ => (unfold_macro_exp m a1 param tl) * (unfold_macro_exp m a2 param tl)
| (eq_m a1 a2),_ => Eq (unfold_macro_exp m a1 param tl) (unfold_macro_exp m a2 param tl)
| (le_m a1 a2),_ => Le (unfold_macro_exp m a1 param tl) (unfold_macro_exp m a2 param tl)
| (not_m a1),_ => Not (unfold_macro_exp m a1 param tl)
| (and_m a1 a2),_ => (unfold_macro_exp m a1 param tl) && (unfold_macro_exp m a2 param tl)
| (macro_m macro_id param'), S tl' => unfold_macro_exp m ((fst m) macro_id) (fun x=>unfold_macro_exp m (param' x) param tl') tl'
| (macro_m macro_id param'), 0 => Inv
| (param_m n),_ => param n
| (inv_m),_ => Inv
end.
 **)


 
Inductive exp_m_unfold : mstate -> exp_m -> EXP_params -> EXP -> Prop :=
  | AU_num : forall m param n,  exp_m_unfold m (num_m n) param (Num n)
  | AU_poi : forall m param x x0, exp_m_unfold m x param x0 -> 
                                  exp_m_unfold m (poi_m x) param (Poi x0)
  | AU_plus: forall m e1 e2 p a1 a2,
      exp_m_unfold m e1 p a1 -> exp_m_unfold m e2 p a2 ->
      exp_m_unfold m (plus_m e1 e2) p (Plus a1 a2)
  | AU_minus: forall m e1 e2 p a1 a2,
      exp_m_unfold m e1 p a1 -> exp_m_unfold m e2 p a2 ->
      exp_m_unfold m (minus_m e1 e2) p (Minus a1 a2)
  | AU_mult: forall m e1 e2 p a1 a2,
      exp_m_unfold m e1 p a1 -> exp_m_unfold m e2 p a2 ->
      exp_m_unfold m (mult_m e1 e2) p (Mult a1 a2)
  | AU_eq: forall m e1 e2 p a1 a2,
      exp_m_unfold m e1 p a1 -> exp_m_unfold m e2 p a2 ->
      exp_m_unfold m (eq_m e1 e2) p (Eq a1 a2)
  | AU_le: forall m e1 e2 p a1 a2,
      exp_m_unfold m e1 p a1 -> exp_m_unfold m e2 p a2 ->
      exp_m_unfold m (le_m e1 e2) p (Le a1 a2)
  | AU_not: forall m e p a,
      exp_m_unfold m e p a ->
      exp_m_unfold m (not_m e) p (Not a)
  | AU_and: forall m e1 e2 p a1 a2,
      exp_m_unfold m e1 p a1 -> exp_m_unfold m e2 p a2 ->
      exp_m_unfold m (and_m e1 e2) p (And a1 a2)
  | AU_param: forall m p n,
      exp_m_unfold m (param_m n) p (p n)
  | AU_macro: forall m p mx pm pm' RES,
      (forall x, exp_m_unfold m (pm x) p (pm' x)) ->
      exp_m_unfold m ((fst m) mx) pm' RES ->
      exp_m_unfold m (macro_m mx pm) p RES.
  
Inductive com_m_unfold : mstate -> com_m -> EXP_params -> COM_params -> COM -> Prop :=
  | CU_skip:  forall m pa pc, com_m_unfold m skip_m pa pc Skip
  | CU_ass :  forall m pa pc x X a A,
      exp_m_unfold m a pa A -> exp_m_unfold m x pa X ->
      com_m_unfold m (ass_m x a) pa pc (Ass X A)
  | CU_seq :  forall m pa pc c1 c2 C1 C2,
      com_m_unfold m c1 pa pc C1 -> com_m_unfold m c2 pa pc C2 ->
      com_m_unfold m (seq_m c1 c2) pa pc (Seq C1 C2)
  | CU_iif :  forall m pa pc b B c1 c2 C1 C2,
      exp_m_unfold m b pa B ->
      com_m_unfold m c1 pa pc C1 -> com_m_unfold m c2 pa pc C2 ->
      com_m_unfold m (iif_m b c1 c2) pa pc (If B C1 C2)
  | CU_while: forall m pa pc b B c C,
      exp_m_unfold m b pa B -> com_m_unfold m c pa pc C ->
      com_m_unfold m (while_m b c) pa pc (While B C)
  | CU_cparam:forall m pa pc n,
      com_m_unfold m (cparam_m n) pa pc (pc n)
  | CU_cmacro:forall m pa pc mx pma pmc pma' pmc' RES,
      (forall x, exp_m_unfold m (pma x) pa (pma' x)) ->
      (forall x, com_m_unfold m (pmc x) pa pc (pmc' x)) ->
      com_m_unfold m ((snd m) mx) pma' pmc' RES ->
      com_m_unfold m (cmacro_m mx pma pmc) pa pc RES.

Inductive unfold_exp : mstate -> exp -> EXP -> Prop :=
  | a_num : forall m n, unfold_exp m (num n) (Num n)
  | a_poi : forall m x x0, unfold_exp m x x0 -> unfold_exp m (poi x) (Poi x0)
  | a_plus: forall m e1 e2 a1 a2,
      unfold_exp m e1 a1 -> unfold_exp m e2 a2 -> unfold_exp m (e1+e2)%lang1 (a1+a2)%lang0
  | a_minus: forall m e1 e2 a1 a2,
      unfold_exp m e1 a1 -> unfold_exp m e2 a2 -> unfold_exp m (e1-e2)%lang1 (a1-a2)%lang0
  | a_mult: forall m e1 e2 a1 a2,
      unfold_exp m e1 a1 -> unfold_exp m e2 a2 -> unfold_exp m (e1*e2)%lang1 (a1*a2)%lang0
  | a_eq: forall m e1 e2 a1 a2,
      unfold_exp m e1 a1 -> unfold_exp m e2 a2 -> unfold_exp m (e1=e2)%lang1 (a1=a2)%lang0
  | a_le: forall m e1 e2 a1 a2,
      unfold_exp m e1 a1 -> unfold_exp m e2 a2 -> unfold_exp m (e1<=e2)%lang1 (a1<=a2)%lang0
  | a_not: forall m e a,
      unfold_exp m e a -> unfold_exp m (~e)%lang1 (~a)%lang0
  | a_and: forall m e1 e2 a1 a2,
      unfold_exp m e1 a1 -> unfold_exp m e2 a2 -> unfold_exp m (e1 && e2)%lang1 (a1 && a2)%lang0
  | a_macro: forall m mx p p' RES,
      (forall x, unfold_exp m (p x) (p' x)) ->
      exp_m_unfold m ((fst m) mx) p' RES ->
      unfold_exp m (macro mx p) RES.

Inductive unfold_com : mstate -> com -> COM -> Prop :=
  | c_skip : forall m, unfold_com m skip Skip
  | c_ass  : forall m x X a A,
      unfold_exp m a A -> unfold_exp m x X -> unfold_com m (ass x a) (Ass X A)
  | c_seq  : forall m c1 c2 C1 C2,
      unfold_com m c1 C1 -> unfold_com m c2 C2 -> unfold_com m (seq c1 c2) (Seq C1 C2)
  | c_iif  : forall m b B c1 c2 C1 C2,
      unfold_exp m b B ->
      unfold_com m c1 C1 -> unfold_com m c2 C2 ->
      unfold_com m (iif b c1 c2) (If B C1 C2)
  | c_while: forall m b B c C,
      unfold_exp m b B -> unfold_com m c C ->
      unfold_com m (while b c) (While B C)
  | c_cmacro: forall m mx pa pc pa' pc' RES,
      (forall x, unfold_exp m (pa x) (pa' x)) ->
      (forall x, unfold_com m (pc x) (pc' x)) ->
      com_m_unfold m ((snd m) mx) pa' pc' RES ->
      unfold_com m (cmacro mx pa pc) RES.

Axiom function_equal: forall {X:Type} {Y:Type} (f: X->Y) (g: X->Y),
    (forall x, f x = g x) -> f = g.

Lemma exp_m_unfold_uniqueness : forall m e a b p,
    exp_m_unfold m e p a ->
    exp_m_unfold m e p b -> a = b.
Proof.
  intros.
  generalize dependent b.
  induction H.
  ++ intros. inversion H0; subst. auto.
  ++ intros. inversion H0; subst; auto.
     apply IHexp_m_unfold in H3.
     rewrite H3; auto.
  ++ intros.
     inversion H1; subst.
     apply IHexp_m_unfold1 in H5.
     apply IHexp_m_unfold2 in H8.
     rewrite H5. rewrite H8. reflexivity.
  ++ intros.
     inversion H1; subst.
     apply IHexp_m_unfold1 in H5.
     apply IHexp_m_unfold2 in H8.
     rewrite H5. rewrite H8. reflexivity.
  ++ intros.
     inversion H1; subst.
     apply IHexp_m_unfold1 in H5.
     apply IHexp_m_unfold2 in H8.
     rewrite H5. rewrite H8. reflexivity.
  ++ intros.
     inversion H1; subst.
     apply IHexp_m_unfold1 in H5.
     apply IHexp_m_unfold2 in H8.
     rewrite H5. rewrite H8. reflexivity.
  ++ intros.
     inversion H1; subst.
     apply IHexp_m_unfold1 in H5.
     apply IHexp_m_unfold2 in H8.
     rewrite H5. rewrite H8. reflexivity.
  ++ intros.
     inversion H0; subst.
     apply IHexp_m_unfold in H3.
     rewrite H3; reflexivity.
  ++ intros.
     inversion H1; subst.
     apply IHexp_m_unfold1 in H5.
     apply IHexp_m_unfold2 in H8.
     rewrite H5. rewrite H8. reflexivity.
  ++ intros.
     inversion H0; subst.
     reflexivity.
  ++ intros.
     inversion H2; subst.
     assert (pm' = pm'0).
     {
       apply function_equal.
       intros.
       apply H0 with (x:=x0) in H6.
       exact H6.
     }
     rewrite <- H3 in H9.
     apply IHexp_m_unfold in H9.
     exact H9.
Qed.

Lemma unfold_exp_uniqueness : forall m e a b,
    unfold_exp m e a -> unfold_exp m e b -> a = b.
Proof.
  intros.
  generalize dependent b.
  induction H; try solve [intros; inversion H0; subst; auto].
  ++ intros.
     inversion H0; subst.
     apply IHunfold_exp in H3.
     rewrite H3; reflexivity.
  ++ intros.
     inversion H1; subst.
     apply IHunfold_exp1 in H5.
     apply IHunfold_exp2 in H7.
     rewrite H5; rewrite H7; reflexivity.
  ++ intros.
     inversion H1; subst.
     apply IHunfold_exp1 in H5.
     apply IHunfold_exp2 in H7.
     rewrite H5; rewrite H7; reflexivity.
  ++ intros.
     inversion H1; subst.
     apply IHunfold_exp1 in H5.
     apply IHunfold_exp2 in H7.
     rewrite H5; rewrite H7; reflexivity.
  ++ intros.
     inversion H1; subst.
     apply IHunfold_exp1 in H5.
     apply IHunfold_exp2 in H7.
     rewrite H5; rewrite H7; reflexivity.
  ++ intros.
     inversion H1; subst.
     apply IHunfold_exp1 in H5.
     apply IHunfold_exp2 in H7.
     rewrite H5; rewrite H7; reflexivity.
  ++ intros.
     inversion H0; subst.
     apply IHunfold_exp in H3.
     rewrite H3; reflexivity.
  ++ intros.
     inversion H1; subst.
     apply IHunfold_exp1 in H5.
     apply IHunfold_exp2 in H7.
     rewrite H5; rewrite H7; reflexivity.
  ++ intros.
     inversion H2; subst.
     assert (p' = p'0).
     {
       apply function_equal.
       intros x.
       apply H0.
       apply H6.
     }
     rewrite H3 in H1.
     apply exp_m_unfold_uniqueness with (m:=m) (e:=(fst m mx)) (p:=p'0).
     - exact H1.
     - exact H8.
Qed.

Lemma com_m_unfold_uniqueness : forall m e a b pa pc,
    com_m_unfold m e pa pc a ->
    com_m_unfold m e pa pc b ->
    a = b.
Proof.
  intros.
  generalize dependent b.
  induction H.
  ++ intros. inversion H0. reflexivity.
  ++ intros. inversion H1; subst.
     assert(A0=A).
     {
       apply exp_m_unfold_uniqueness with (m:=m) (e:=a) (p:=pa).
       assumption.
       assumption.
     }
     assert(X0=X1).
     {
       apply exp_m_unfold_uniqueness with (m:=m) (e:=x0) (p:=pa).
       assumption.
       assumption.
     }
     rewrite H2, H3.
     reflexivity.
  ++ intros; inversion H1; subst.
     assert(C1=C0).
     {
       apply IHcom_m_unfold1 in H5.
       assumption.
     }
     assert(C2=C3).
     {
       apply IHcom_m_unfold2 in H9.
       assumption.
     }
     rewrite H2, H3.
     reflexivity.
  ++ intros. inversion H2; subst.
     assert(B=B0).
     {
       apply exp_m_unfold_uniqueness with (m:=m) (e:=b) (p:=pa).
       exact H. exact H7.
     }
     assert(C1=C0).
     {
       apply IHcom_m_unfold1 in H11. exact H11.
     }
     assert(C2=C3).
     {
       apply IHcom_m_unfold2 in H12. exact H12.
     }
     rewrite H3, H4, H5.
     reflexivity.
  ++ intros. inversion H1; subst.
     assert(B=B0).
     {
       apply exp_m_unfold_uniqueness with (m:=m) (e:=b) (p:=pa).
       exact H. exact H5.
     }
     assert(C=C0).
     {
       apply IHcom_m_unfold in H9.
       exact H9.
     }
     rewrite H2, H3.
     reflexivity.
  ++ intros. inversion H0; subst.
     reflexivity.
  ++ intros. inversion H3; subst.
     apply IHcom_m_unfold with (b:=b).
     assert(pma'0 = pma').
     {
       apply function_equal.
       intros x.
       specialize H8 with (x:=x).
       specialize H with (x:=x).
       apply exp_m_unfold_uniqueness with (m:=m) (e:=pma x) (p:=pa).
       assumption. assumption.
     }
     assert(pmc'0 = pmc').
     {
       apply function_equal.
       intros x.
       specialize H12 with (x:=x).
       specialize H0 with (x:=x).
       apply H1 in H12.
       symmetry in H12. exact H12.
     }
     rewrite <- H4. rewrite <- H5.
     exact H13.
Qed.
  
Lemma unfold_com_uniqueness : forall m e a b,
    unfold_com m e a -> unfold_com m e b ->
    a = b.
Proof.
  intros.
  generalize dependent b.
  induction H.
  ++ intros. inversion H0; subst; auto.
  ++ intros. inversion H1; subst.
     assert(A0=A).
     {
       apply unfold_exp_uniqueness with (m:=m) (e:=a).
       assumption.
       assumption.
     }
     assert(X0=X1).
     {
       apply unfold_exp_uniqueness with (m:=m) (e:=x0).
       assumption.
       assumption.
     }
     rewrite H2, H3.
     reflexivity.
  ++ intros; inversion H1; subst.
     assert(C1=C0).
     {
       apply IHunfold_com1 in H5.
       assumption.
     }
     assert(C2=C3).
     {
       apply IHunfold_com2 in H7.
       assumption.
     }
     rewrite H2, H3.
     reflexivity.
  ++ intros. inversion H2; subst.
     assert(B=B0).
     {
       apply unfold_exp_uniqueness with (m:=m) (e:=b).
       exact H. exact H7.
     }
     assert(C1=C0).
     {
       apply IHunfold_com1 in H9. exact H9.
     }
     assert(C2=C3).
     {
       apply IHunfold_com2 in H10. exact H10.
     }
     rewrite H3, H4, H5.
     reflexivity.
  ++ intros. inversion H1; subst.
     assert(B=B0).
     {
       apply unfold_exp_uniqueness with (m:=m) (e:=b).
       exact H. exact H5.
     }
     assert(C=C0).
     {
       apply IHunfold_com in H7.
       exact H7.
     }
     rewrite H2, H3.
     reflexivity.
  ++ intros. inversion H3; subst.
     apply com_m_unfold_uniqueness with (m:=m) (e:=snd m mx) (pa:=pa') (pc:=pc').
     - assumption.
     - assert (pa'=pa'0).
       {
         apply function_equal.
         intros x.
         specialize H with (x:=x).
         specialize H8 with (x:=x).
         apply unfold_exp_uniqueness with (m:=m) (e:=pa x).
         assumption. assumption.
       }
       assert (pc'=pc'0).
       {
         apply function_equal.
         intros x.
         specialize H10 with (x:=x).
         apply H1 in H10.
         exact H10.
       }
       rewrite <- H4, <- H5 in H11.
       exact H11.
Qed.


Definition assertion : Type := mstate -> State -> Prop.

Definition hoare_triple_o (P: assertion) (c: COM) (Q: assertion) : assertion :=
  fun ms _ => forall st st',  P ms st -> st =[[ c ]]=> st'-> Q ms st'.

Definition hoare_triple (P: assertion) (c: com) (Q: assertion) : assertion :=
  fun ms _ => forall st st' C, unfold_com ms c C -> P ms st -> st =[[ C ]]=> st' -> Q ms st'.

Definition hoare_triple_prop (P: assertion) (c: com) (Q: assertion) (ms : mstate) : Prop :=
  forall st, (hoare_triple P c Q) ms st.

Definition assert_implies (m : mstate) (P Q : assertion) : Prop :=
  forall st, P m st -> Q m st.

Notation "[[ P ]]  c  [[ Q ]] ms" :=
  (hoare_triple_prop P c Q ms) (at level 90, c at next level)
  : hoare_spec_scope.

Notation "{{ P }}  c  {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c at next level)
  : hoare_spec_scope.


Open Scope hoare_spec_scope.

Theorem hoare_post_true : forall (P Q : assertion) c ms,
  (forall st, Q ms st) ->
  hoare_triple_prop P c Q ms.
Proof.
  intros. 
  unfold hoare_triple_prop.
  unfold hoare_triple. 
  intros.
  apply H.
Qed.

Theorem hoare_pre_false : forall (P Q : assertion) c ms,
  (forall st, ~ (P ms st)) -> 
  hoare_triple_prop P c Q ms.
Proof.
  intros; unfold hoare_triple_prop; unfold hoare_triple; simpl.
  intros.
  apply H in H1.
  inversion H1.
Qed.


Definition assn_sub X a P : assertion :=
  fun (ms : mstate) (st : State) =>
    P ms (X !-> EXP_eval st a ; st).

Notation "P [ X |-> a ]" := (assn_sub X a P)
                              (at level 10, X at next level).

Lemma EXP_eval_const :
  forall st x,  EXP_eval st (Num x) = x.
Proof.
  intros. simpl.
  reflexivity.
Qed.

Theorem hoare_asgn0 : forall Q X a ms,
  [[Q [X |-> (Num a)%lang0] ]] (^(num X) ::= num a)%lang1 [[Q]]ms.
Proof.
  intros.
  unfold hoare_triple_prop.
  unfold hoare_triple; simpl.
  intros.
  assert(C = (^X0 ::= a)%lang0).
  {
    apply unfold_com_uniqueness with (m:=ms) (e:=(^X0 ::= a)%lang1).
    - assumption.
    - apply c_ass.
      + apply a_num.
      + apply a_poi, a_num.
  }
  rewrite H2 in H1.
  inversion H1; subst.
  repeat rewrite EXP_eval_const in H1.
  repeat rewrite EXP_eval_const. 
  unfold assn_sub in H0.
  exact H0.
Qed.

Example assn_sub_example : forall ms,
  [[(fun ms st => st 1 < 5) [1 |-> ^1 + 1] ]]
  ^(num 1) ::= ^(num 1) + 1
  [[fun ms st => st 1 < 5]] ms.
Proof.
  intros.
  unfold hoare_triple_prop.
  unfold hoare_triple; simpl.
  intros.
  inversion H; subst.
  unfold assn_sub in H0.
  simpl in H0.
  inversion H5; subst.
  inversion H9; subst.
  inversion H6; subst. inversion H4; subst.
  inversion H7; subst.
  inversion H1; subst.
  inversion H8; subst.
  simpl.
  exact H0.
Qed.

Axiom equality_bool : forall a b,
    (a=?b)=true <-> a=b.

Lemma equality_stupid_coq : forall a b,
    (a=?b) = (b=?a).
Proof.
  intros a b.
  destruct (a=?b) eqn:eq.
  + symmetry.
    apply equality_bool.
    apply equality_bool in eq.
    rewrite eq; reflexivity.
  + assert(a=b->False).
    {
      intros.
      apply equality_bool in H.
      rewrite eq in H.
      inversion H.
    }
    destruct (b=?a) eqn:eq1.
    - apply equality_bool in eq1.
      symmetry in eq1.
      apply H in eq1.
      inversion eq1.
    - reflexivity.
Qed.

Lemma S_update_same : forall X a st,
    (X !-> a; st) X = a.
Proof.
  intros.
  unfold S_update; simpl.
  destruct (X0=?X0) eqn:eq.
  - auto.
  - assert((X0=?X0)=true). apply equality_bool; auto.
    rewrite eq in H.
    inversion H.
Qed.

Lemma S_update_shadow : forall X a b st,
    (X !-> a; X !-> b; st) = (X !-> a; st).
Proof.
  intros X a b st.
  apply function_equal.
  intros x.
  destruct (x=?X) eqn:eq.
  + apply equality_bool in eq. rewrite eq.
    rewrite S_update_same.
    rewrite S_update_same.
    reflexivity.
  + unfold S_update.
    assert((X=?x)=false).
    rewrite <- eq.
    rewrite equality_stupid_coq; auto.
    simpl.
    repeat rewrite H.
    reflexivity.
Qed.

Theorem hoare_asgn_fwd0 :
  forall m a P ms X,
  [[fun ms st => P ms st /\ st X = m]]
    ^X ::= num a
  [[fun ms st => P ms (X !-> m ; st)
           /\ st X = EXP_eval (X !-> m ; st) (Num a) ]] ms.
Proof.
  unfold hoare_triple_prop; unfold hoare_triple; intros; simpl.
  inversion H. inversion H5; inversion H7; subst.
  inversion H13; subst.
  inversion H1; subst.
  simpl.
  destruct H0.
  split.
  - rewrite S_update_shadow.
    assert ( (X0 !-> m; st0) = st0 ).
    {
      apply function_equal.
      intros x.
      destruct (x =? X0) eqn:eq.
      + assert (x=X0). apply equality_bool. exact eq.
        rewrite H3.
        unfold S_update; simpl.
        rewrite H2. 
        assert ((if X0 =? X0 then m else m)=m).
        destruct (X0=?X0); auto.
        exact H4.
      + unfold S_update; simpl.
        assert ((if X0 =? x then m else st0 x)=st0 x).
        destruct (X0=?x) eqn:eq1.
        assert(X0=x). apply equality_bool in eq1.
        rewrite eq1 in eq.
        rewrite eq1.
        auto.
        rewrite <- H2.
        rewrite H3; auto.
        auto. auto.
    }
    rewrite H3.
    apply H0.
  - unfold S_update; simpl.
    destruct (X0 =? X0) eqn:eq.
    + reflexivity.
    + assert((X0=X0)->False).
      intros.
      apply equality_bool in H3.
      rewrite H3 in eq.
      inversion eq.
      assert(X0=X0). auto.
      apply H3 in H4.
      inversion H4.
Qed.

Close Scope hoare_spec_scope.
