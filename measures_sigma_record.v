(*Version 1.4.2 - 25-05-2020
  finite_additivity_meas now finished
  additivty_meas also proven, incl. all lemmas
  proof complete!
*)

Require Import Sets.Ensembles.
Require Import Sets.Classical_sets.
Require Import Sets.Powerset.
Require Import Logic. 
Require Import ClassicalFacts. 
Require Import Omega. 
Require Import Coq.Arith.Wf_nat. 

(**** WP tactics library ****)
Require Import Rbase.
Require Import Rfunctions.
Require Import SeqSeries.
Require Import Rtrigo.
Require Import Ranalysis.
Require Import Integration.
Require Import micromega.Lra.
Require Import Omega.
Require Import Max.
(* Require Import Unicode.Utf8. *)
Require Import Sets.Ensembles.
Require Import Sets.Classical_sets.

(** Guarantee indentation and introduce custom notation for forall *)
Notation "'for' 'all' x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[ ' '[ ' for  all  x .. y ']' , '//'  P ']'") : type_scope.

Notation "∀ x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 200, x binder, y binder, right associativity,
  only parsing) : type_scope.

Notation "'there' 'exists' x .. y , P " := (exists x, .. (exists y, P) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[ ' '[ ' there  exists  x .. y  ']' , '//'  P ']'") : type_scope.

Notation "∃ x .. y , P " := (exists x, .. (exists y, P) ..)
  (at level 200, x binder, y binder, right associativity,
  only parsing) : type_scope.

Notation "'fun' x .. y '↦' t" := (fun x => .. (fun y => t) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[ ' '[ ' 'fun' x .. y ']' '↦' '/' t ']'").

Notation "x ∨ y" := (x \/ y) (at level 85, right associativity) : type_scope.
Notation "x ∧ y" := (x /\ y) (at level 80, right associativity) : type_scope.
Notation "x → y" := (x -> y)
  (at level 99, y at level 200, right associativity,
   only parsing): type_scope.
Notation "x ⇒ y" := (x -> y)
  (at level 99, y at level 200, right associativity,
   only parsing): type_scope.
(* the notation below is fun, but is no good for functions *)
(* need to see if this can be adapted so it only uses 
   this notation for propositions *)
(*Notation "'if' x 'then' y" := (x -> y)
  (at level 99, y at level 200, right associativity): prop_scope.*)
Notation "x ⇨ y" := (x -> y)
  (at level 99, y at level 200, right associativity): type_scope.

Notation "x ↔ y" := (x <-> y) (at level 95, no associativity): type_scope.
Notation "x ⇔ y" := (x <-> y) (at level 95, no associativity): type_scope.
Notation "¬ x" := (~x) (at level 75, right associativity) : type_scope.
Notation "x ≠ y" := (x <> y) (at level 70) : type_scope.

Notation "x ≤ y" := (le x y) (at level 70, no associativity) : nat_scope.
Notation "x ≥ y" := (ge x y) (at level 70, no associativity) : nat_scope.

Notation "x ≤ y" := (x <= y)%R (at level 70, no associativity) : R_scope.
Notation "x ≥ y" := (x >= y)%R (at level 70, no associativity) : R_scope.

Open Scope nat_scope.
Open Scope R_scope.

(* TODO: the below definition doesn't work very nicely *)
Notation "x ↦ y" := (fun x => y) (at level 0).

Notation "'ℕ'" := (nat).
Notation "'ℝ'" := (R).

(** Add field and lra to tactics to try automatically *)

Hint Extern 3 ( _ = _ ) => field : real.
Hint Extern 3 ( _ <= _ ) => lra : real.
Hint Extern 3 ( _ >= _ ) => lra : real.
Hint Extern 3 ( _ < _ ) => lra : real.
Hint Extern 3 ( _ > _ ) => lra : real.


Ltac wp_power :=
  timeout 5 (first [ solve [auto with *]
        | solve [eauto with *]
        | solve [firstorder (auto with *)]
        | solve [firstorder (eauto with *)]]).

Ltac intro_strict s t :=
  match goal with
    | [ |- forall _ : t, _ ] => intro s
  end.

Tactic Notation "Take" ident(s) ":" constr(t):=
  intro_strict s t.

Ltac assume_strict s t :=
  match goal with
    | [ |- ?u -> _ ] => (change u with t; intro s)
  end.

Tactic Notation "Assume" ident(s) :=
  intro s.

Tactic Notation "Assume" ident(s) ":" constr(t) :=
  assume_strict s t.

Ltac goal_check t :=
  tryif (change t) 
    then (idtac "We indeed need to show that" t)
    else fail "This is not the current goal".

(** Make it possible to verify the goal t by writing
    "We need to show that t". *)
Tactic Notation "We" "need" "to" "show" "that" constr(t) :=
  goal_check t.

(** Make it possible to verify the goal t by writing
    "To show : t". *)
Tactic Notation "To" "show" ":" constr(t) :=
  goal_check t.

(** The tactic (hypo_check s t) checks if t is one of the 
    current hypothesis, and if so, it renames it into s *)
Ltac hypo_check s t:=
match goal with 
| [H : t |- _] => rename H into s
| _ => fail
end.

Tactic Notation "Choose" constr(t):=
  exists t.

Tactic Notation "Choose" ident(s) ":=" constr(t) :=
  pose (s := t);
  exists s.

Tactic Notation "Choose" ident(s) 
                "such" "that" ident(u)
                "according" "to" constr(v) (*":" constr(t)*):=
  destruct v as [s u].

(*Tactic Notation "Choose" ident(s)
                "such" "that" ident(u)
                "according" "to" ident(v)
                "with" constr(t) :=
  destruct v with t as [s u]. *)

Tactic Notation "Choose" ident(s)
                "such" "that" ident(u)
                "according" "to" constr(v)
                "with" constr(t) :=
  destruct v with t as [s u].


Tactic Notation "Because" ident(s) 
  "both" ident(u) "and" ident(v) :=
  destruct s as [u v].

Tactic Notation "Because" ident(s) 
  "both" ident(u) ":" constr(t_u)
  "and"  ident(v) ":" constr(t_v):=
  destruct s as [u v].

Tactic Notation "Because" ident(s)
  "either" ident(u) "or" ident(v) :=
  destruct s as [u | v].

(** Apply with goal check
    The next tactics verify whether certain steps have the desired effect. *)
Ltac new_goal_verified_apply s t :=
  apply s;
  match goal with 
  | [|- t] => idtac "Expected goal was produced"
  | _ => fail "Lemma did not produce expected outcome"
  end.

(*Tactic Notation "By" constr(s) 
  "it" "suffices" "to" "show" "that"
  constr(t) :=
  new_goal_verified_apply s t.*)

(** A powerful forward reasoning tactic. 
    The sequential trying of auto and eauto 
    is there because eauto can be much slower. 
    TODO: is this what we want? *)
Ltac new_hyp_verified_pose_proof s t u:=
  assert (u : t) by timeout 5 (first [ solve [auto using s with *]
                          | solve [eauto using s with *]
                          | solve [firstorder using s]
                          | solve [firstorder (eauto with *) using s]
                          | idtac "Waterproof could not find a proof. If you believe the statement should hold, try making a smaller step"]).

Tactic Notation "By" constr(s)
  "it" "holds" "that" constr(t) "("ident(u)")"
  := new_hyp_verified_pose_proof s t u.

(*Tactic Notation "By" constr(s0) "," constr(s1)
  "it" "holds" "that" constr(t) "("ident(u)")"
  :=*)

(* TODO: align syntax with "By ... it holds that" *)
Tactic Notation "It" "holds" "that"
  constr(t) "(" ident(u) ")" :=
  assert (u : t) by first [ wp_power
                          | idtac "Waterproof could not find a proof. If you believe the statement should hold, try making a smaller step"].

Ltac conclude_proof t :=
  match goal with
  | [|-t] => idtac
  | _ => (idtac "Warning: The statement you provided does not exactly correspond to the current goal. This can make your proof less readable."; change t || fail "The provided statement cannot be converted to the current goal. If you are trying to prove an intermediate step, add a name to your hypothesis between brackets at the end of the sentence.")
  end; first [wp_power | fail "Waterproof could not find a proof. Try making a smaller step."].

Tactic Notation "It" "holds" "that" constr(t) :=
  conclude_proof t.

Tactic Notation "It" "follows" "that" constr(t) :=
  conclude_proof t.

Tactic Notation "It" "suffices" "to" "show" "that"
  constr(t) :=
  enough t by ( wp_power || fail "Waterproof could not confirm that proving the statement would be enough.").


Tactic Notation "It" "suffices" "to" "show" "that"
  constr(t) "by" tactic(tac) :=
  enough t by tac.


Tactic Notation "Write" "goal" "using" constr(t) "as" 
  constr(s) :=
  let u := fresh in
    assert (u : t) by wp_power;
  rewrite u;
  enough s by wp_power;
  clear u.

Tactic Notation "Write" ident(H) "using" constr(t) "as"
  constr(s) :=
  let u := fresh in
    assert (u : t) by wp_power;
  rewrite u in H;
  clear u.

Tactic Notation "This" "follows" "by" "assumption" := 
  assumption.

Tactic Notation "We" "claim" "that" 
  constr(t) "(" ident(u) ")" :=
  assert (u : t).

Tactic Notation "Rewrite" "using" constr(t) :=
  let u := fresh in
    assert (u : t) by wp_power;
  rewrite u;
  clear u.

Tactic Notation "rewrite" "using" constr(t) :=
  let u := fresh in
    assert (u : t) by wp_power;
  rewrite u;
  clear u.

Tactic Notation "Rewrite" "using" constr(t) "in" ident(s):=
  let u := fresh in
    assert (u : t) by wp_power;
  rewrite u in s;
  clear u.

Tactic Notation "rewrite" "using" constr(t) "in" ident(s):=
  let u := fresh in
    assert (u : t) by wp_power;
  rewrite u in s;
  clear u.

Tactic Notation "Rewrite" "<-" "using" constr(t) :=
  let u := fresh in 
    assert (u : t) by wp_power;
  rewrite<-u;
  clear u.

Tactic Notation "replacing" constr(s) "with" constr(t) :=
  replace s with t by wp_power.

Tactic Notation "Apply" uconstr(t) :=
  apply t.


Tactic Notation "Unfold" constr(t) :=
  unfold t.

Tactic Notation "Unfold" constr(t) "in" ident(s):=
  unfold t in s.

Tactic Notation "Expand" "the" "definition" "of" reference(t) :=
  unfold t.

Tactic Notation "Expand" "the" "definition" "of" 
  reference(t) "in" ident(s) :=
  unfold t in s.

Tactic Notation "Write" ident(s) "as" constr(t) :=
  change t in s.

Ltac trans_ineq eq_or_ineq := 
  match goal with 
  | [|-?x ≤ ?z] => 
    match (type of eq_or_ineq) with 
    | (x ≤ ?y) => apply (Rle_trans x y z eq_or_ineq)
    | _ => idtac "not a less-than-or-equal-to inequality"
    end
  | _ => idtac "Goal is not a less-than-or-equal-to inequality."
  end.

Tactic Notation "Define" ident(u) ":=" constr(t) :=
  set (u := t).


Tactic Notation "This" "follows" "by" "reflexivity" :=
  reflexivity.

Tactic Notation "Simplify" "what" "we" "need" "to" "show" :=
  simpl.

Hint Resolve Rmult_gt_0_compat : real.
Hint Resolve Rmult_lt_0_compat : real.

Ltac contra :=
  match goal with
  | [|- ?X] => destruct (classic X); try assumption
  | _ => idtac "failure of tactic"
  end.

Tactic Notation "We" "argue" "by" "contradiction" :=
  contra.
  
Tactic Notation "Contradiction" := contradiction.

Hint Resolve not_all_not_ex : contra_hints.
Hint Resolve not_all_ex_not : contra_hints.
Hint Resolve not_ex_all_not : contra_hints.
Hint Resolve ex_not_not_all : contra_hints.
Hint Resolve all_not_not_ex : contra_hints.


(********* own notations *************)

(*
Notation "'subset' U" := 
  (Ensemble U) (at level 50). 

Notation "'setOfSubsets' U" := 
  (Ensemble (subset U)) (at level 50). *)

Definition subset (U : Type) := 
  (Ensemble U). 

Definition setOfSubsets (U : Type) := 
  (Ensemble (subset U)).

Variable U : Type. 


Notation "∅" := 
  (Empty_set U). 

Notation "'Ω'" := 
  (Full_set U) (at level 0). 

Notation "A ∩ B" := 
  (Intersection _ A B) (at level 50). 

Notation "A ∪ B" := 
  (Union _ A B) (at level 50). 

Notation "A \ B" := 
  (Setminus _ A B) (at level 50). 

Notation "x ∈ A" := 
  (In _ A x) (at level 55). 

Notation "x ∉ A" :=  
  (¬ In _ A x) (at level 55). 

Notation "A ⊂ B" := 
  (Included _ A B) (at level 50). 

Notation "A B 'are disjoint'" := 
  (Disjoint _ A B) (at level 50). 

Notation "｛ x : T | P ｝" := 
  (fun (x : T) ↦ P) (x at level 99).

Tactic Notation "We" "prove" "equality" "by" "proving" "two" "inclusions" :=
   apply Extensionality_Ensembles; 
   unfold Same_set; 
   unfold Included;
   split.

Tactic Notation "We" "prove" "by" "induction" "on" ident(x) := 
  induction x. 
(*Not nicest formulation, but 'Proof' is already taken*)

(* horrible notation, just to test and probably to be 
   replaced. Problem is that 
  writing 'By ... it holds that ... (name)' does not 
  conclude the proof. 
*)
Tactic Notation "By" constr(u) "it" "holds" "that" constr(t) "which" "concludes" ident(the) "proof":= 
  By u it holds that t (the); 
  apply the. 


Ltac intros_strict x y t :=
  match goal with
    | [ |- forall _ _ : t, _] => intros x y
  end.

Tactic Notation "Take" ident(x) ident(y) ":" constr(t):=
  intros_strict x y t. 
(*
Tactic Notation "Let" ident(A) "be" "a" "set" := 
  Take A : (subset U).

Tactic Notation "Let" ident(F) "be" "a" "set" "of" "sets" := 
  Take F : (setOfSubsets U).
*)
Hint Resolve Full_intro : measure_theory.  (*nieuwe database measure theory*)
Hint Resolve Intersection_intro : measure_theory. 
Hint Resolve Union_introl Union_intror : measure_theory. 
Hint Resolve Disjoint_intro : measure_theory. 


Definition is_π_system (Π : setOfSubsets U) 
  : Prop := 
    ∀ A : subset U, A ∈ Π ⇒ 
      ∀ B : subset U, B ∈ Π ⇒ 
         (A ∩ B) ∈ Π. 

Notation "A is_a_π-system" := 
  (is_π_system A) (at level 50). 

Definition Countable_union (A : (ℕ → subset U) ) 
  : subset U := 
    ｛ x:U | ∃n : ℕ, x ∈ (A n)｝.

Definition full_set_in_set (Λ : setOfSubsets U) 
  : Prop :=
    Ω ∈ Λ. 

Definition complement_in_set (Λ : setOfSubsets U) 
  : Prop := 
    ∀A  : subset U, A ∈ Λ 
      ⇒ (Ω \ A) ∈ Λ. 

Definition closed_under_disjoint_countable_union (Λ : setOfSubsets U) 
  : Prop :=
    ∀C : (ℕ → (subset U)), 
      (∀ m n : ℕ, m ≠ n ⇒ Disjoint _ (C m) (C n)) 
        ⇒ (∀ n : ℕ, (C n) ∈ Λ) ⇒  (Countable_union C) ∈ Λ.

Definition closed_under_countable_union (Λ : setOfSubsets U) 
  : Prop :=  
    ∀C : (ℕ → (subset U)), (∀ n : ℕ, (C n) ∈ Λ) 
      ⇒ (Countable_union C) ∈ Λ.

Definition is_λ_system (Λ : setOfSubsets U) 
  : Prop :=
    full_set_in_set Λ ∧ 
    complement_in_set Λ ∧
    closed_under_disjoint_countable_union Λ. 

Notation "A is_a_λ-system" := 
  (is_λ_system A) (at level 50). 

Definition is_σ_algebra (F : setOfSubsets U) 
  : Prop := 
    full_set_in_set F ∧ 
    complement_in_set F ∧
    closed_under_countable_union F.
(*
Inductive σ_algebra : setOfSubsets U := 
  | σ_alg_omeg : full_set_in_set σ_algebra
  | σ_alg_comp : complement_in_set σ_algebra
  | σ_alg_cuCU : closed_under_countable_union σ_algebra. 
*)

Notation "A is_a_σ-algebra" := 
  (is_σ_algebra A) (at level 50). 

Definition  σ_algebra_generated_by (A : setOfSubsets U) 
  : (setOfSubsets U) := 
    ｛B : subset U | ∀ F : setOfSubsets U, F is_a_σ-algebra ⇒ (A ⊂ F ⇒ B ∈ F)｝ . 

Notation "σ( A )" := 
 (σ_algebra_generated_by A) (at level 50). 

Definition restriction (F : setOfSubsets U) (A : (subset U)) 
  : (setOfSubsets U) := 
    ｛C : subset U | ∃B : subset U, B ∈ F ⇒ C = A ∩ B｝. 

(* ≤ only works for Reals *)
Definition finite_union (C : (ℕ ⇨ subset U) ) (n : ℕ) 
  : subset U := 
    ｛x:U | (∃i : ℕ,  ((i ≤ n)%nat ∧ x ∈ (C i)))｝.

Definition finite_union_up_to (C : (ℕ ⇨ subset U) ) (n : ℕ) 
  : (subset U) := 
    ｛x : U | (∃i : ℕ,  ((i < n)%nat ∧ x ∈ (C i)))｝.

Definition disjoint_seq (C : (ℕ ⇨ subset U) ) 
  : (ℕ ⇨ subset U)  := 
    fun (n:ℕ) ↦ (C n \ (finite_union_up_to C n)). 


Lemma intersection_empty : ∀A : subset U, 
  (A ∩ ∅) = ∅. 

Proof. 
Take A : (subset U). 
We prove equality by proving two inclusions. 
Take x : U; Assume x_in_intersection. 
destruct x_in_intersection. 
Contradiction. 

Take x : U; Assume x_in_empty. 
Contradiction. 
Qed. 

Lemma empty_disjoint : ∀A : subset U, 
  Disjoint _ A ∅. 

Proof. 
Take A : (subset U).
It suffices to show that (∀ x:U, x ∉ (A ∩ ∅)).
Take x : U. 
By intersection_empty it holds that 
  ((A ∩ ∅) = ∅) (int_empty). 
Write goal using ((A ∩ ∅) = ∅) as (x ∉ ∅). 
It holds that (x ∉ ∅). 
Qed. 


Lemma neq_equiv : ∀ x y : ℕ,
  (x ≠ y) ⇒ ((x < y)%nat ∨ (y < x)%nat).

Proof. 
intros x y. omega.
Qed. 


Lemma leq_equiv : ∀ x y : ℕ,
  (x ≤ y)%nat ⇒ ((x < y)%nat ∨ x = y).

Proof. 
intros x y. omega. 
Qed. 


Lemma geq_equiv : ∀ x y : ℕ,
  (x ≥ y)%nat ⇒ (x = y ∨ (x > y)%nat).

Proof. 
intros x y. omega. 
Qed. 


Lemma l_equiv : ∀ x y : ℕ,
  (x < y)%nat ⇒ (x = (y - 1)%nat ∨ (x < y - 1)%nat).

Proof. 
intros x y. omega. 
Qed. 


Lemma union_to_or : 
  ∀ A B : (subset U), ∀ x : U, 
    x ∈ (A ∪ B) ⇒ (x ∈ A ∨ x ∈ B).

Proof. 
Take A B : (subset U). 
Take x : U; Assume x_in_union. 
destruct x_in_union. 
(* x ∈ A: *)
It follows that (x ∈ A ∨ x ∈ B).
(* x ∈ B: *) 
It follows that (x ∈ A ∨ x ∈ B). 
Qed. 


Lemma intersection_symmetric : 
  ∀ A B : subset U, A ∩ B = B ∩ A. 

Proof. 
Take A B : (subset U). 
We prove equality by proving two inclusions. 
Take x : U; Assume x_in_AB. 
destruct x_in_AB. 
It holds that (x ∈ (B ∩ A)). 

Take x : U; Assume x_in_BA. 
destruct x_in_BA. 
It holds that (x ∈ (A ∩ B)). 
Qed. 


Lemma disjoint_symmetric : 
  ∀ A B : subset U, (Disjoint _ A B) ⇒ (Disjoint _ B A). 

Proof. 
Take A B : (subset U). 
Assume A_B_disjoint. 
destruct A_B_disjoint.
By intersection_symmetric it holds that 
  ((A ∩ B) = (B ∩ A)) (AB_is_BA).
Write H using ((A ∩ B) = (B ∩ A)) 
  as (∀ x : U, x ∉ (B ∩ A)). 
It follows that (Disjoint U B A). 
Qed. 
(*include last two in library? Should be trivial. *)


Lemma FU_up_to_0_empty : 
  ∀ C : (ℕ ⇨ subset U) , finite_union_up_to C 0 = ∅. 

Proof. 
Take C : (ℕ ⇨ subset U) . 
We prove equality by proving two inclusions. 
Take x : U; Assume x_in_FU_0. 
Write x_in_FU_0 as 
  (x ∈ ｛x : U | ∃ i : ℕ , (i < 0)%nat ∧ x ∈ C i｝). 
It holds that (¬(∃i : ℕ, (i<0)%nat ∧ x ∈ C i)) (no_N_l_0). 
Contradiction.

Take x : U; Assume x_in_empty. 
Contradiction. 
Qed.


Lemma disj_seq_disjoint : 
  ∀ C : (ℕ ⇨ subset U) , 
    (∀ m n : ℕ, m ≠ n ⇒ Disjoint _ 
      (disjoint_seq C m) (disjoint_seq C n)). 

Proof. 
Take C : (ℕ ⇨ subset U) . 
Take m n : ℕ. 
Assume m_neq_n.
By neq_equiv it holds that 
  (m ≠ n ⇒ (m < n)%nat ∨ (m > n)%nat) (m_l_g_n).
It holds that ((m < n)%nat ∨ (m > n)%nat) (m_lg_n). 
We argue by contradiction. 
It holds that (∃ x: U, 
  x ∈ ((disjoint_seq C m) ∩ (disjoint_seq C n))) (int_not_empty).
Choose x such that x_in_int according to int_not_empty.
By x_in_int it holds that 
  (x ∈ disjoint_seq C m 
    ∧ x ∈ disjoint_seq C n) (x_in_m_and_n). 
By x_in_m_and_n it holds that 
  (x ∈ disjoint_seq C m) (x_in_m). 
By x_in_m_and_n it holds that 
  (x ∈ disjoint_seq C n) (x_in_n). 
It holds that 
  ((x ∉ finite_union_up_to C m) 
    ∧ (x ∉ finite_union_up_to C m)) (x_not_in_FU_mn).
It holds that 
  (¬(∃i : ℕ,  ((i < m)%nat ∧ x ∈ (C i)))
    ∧ ¬(∃i : ℕ,  ((i < n)%nat ∧ x ∈ (C i)))) (no_i).
Because no_i both no_i_m and no_i_n. 
Because m_lg_n either m_l_n or m_g_n. 
(* m < n: *)
By no_i_m it holds that ((x ∉  C m)) (x_not_in_Cm). 
By x_in_m it holds that (x ∈ C m) (x_in_Cm).
Contradiction. 
(* m > n: *)
By no_i_n it holds that ((x ∉ C n)) (x_not_in_Cn). 
By x_in_m it holds that (x ∈ C n) (x_in_Cn).
Contradiction.  
Qed. 


Lemma CU_sets_disjointsets_equal : 
  ∀ C : (ℕ ⇨ subset U) , 
    Countable_union (disjoint_seq C) = Countable_union C.

Proof. 
Take C : (ℕ ⇨ subset U) .
Define D := (disjoint_seq C). 
We prove equality by proving two inclusions. 

(* CU disjoint sets in CU C: *)
Take x : U; Assume x_in_CU_D. 
It holds that (x ∈ Countable_union C). 

(* CU C in CU disjoint sets: *)
Take x : U; Assume x_in_CU_C. 
(*now choose minimal n such that x is in disj_C n*)
Choose n such that x_in_C_n according to x_in_CU_C.
Define aux_prop := (fun (n : ℕ) ↦ (x ∈ C n)).
By classic it holds that 
  (∀ n, aux_prop n ∨ ¬aux_prop n) (aux_prop_decidable). 
By dec_inh_nat_subset_has_unique_least_element it holds that
  (has_unique_least_element le aux_prop) (exists_least_n). 
Choose n1 such that x_in_C_minimal_n according to exists_least_n. 

It holds that (x ∈ Countable_union D). 
Qed. 


Lemma complement_as_intersection : 
  ∀ A B : subset U, 
    A \ B = (Ω \ B) ∩ A. 

Proof. 
Take A B : (subset U). 
We prove equality by proving two inclusions. 

Take x : U. 
Assume x_in_A_without_B. 
It holds that (x ∈ ((Ω \ B) ∩ A)). 

Take x : U. 
Assume x_in_rhs. 
By x_in_rhs it holds that 
  (x ∈ (Ω \ B) ∧ (x ∈ A)) (x_in_A_and_comp_B). 
It holds that (x ∈ (A \ B)). 
Qed. 


Lemma complements_in_π_and_λ : 
  ∀ F : setOfSubsets U, 
    F is_a_π-system ∧ F is_a_λ-system
    ⇒ ∀ A B : subset U, A ∈ F ∧ B ∈ F
      ⇒ A \ B ∈ F. 

Proof. 
Take F : (setOfSubsets U). 
Assume F_is_π_and_λ_system.
By F_is_π_and_λ_system 
  it holds that (F is_a_π-system) (F_is_π_system). 
By F_is_π_and_λ_system 
  it holds that (F is_a_λ-system) (F_is_λ_system). 
Take A B : (subset U). 
Assume A_and_B_in_F. 
By F_is_λ_system it holds that 
  (Ω \ B ∈ F) (comp_B_in_F). 
By F_is_π_system it holds that 
  (A ∩ (Ω \ B) ∈ F) (set_in_F). 
By complement_as_intersection it holds that 
  (A \ B = (Ω \ B) ∩ A) (set_is_complement). 
Write goal using (A \ B = ((Ω \ B) ∩ A)) 
  as (((Ω \ B) ∩ A) ∈ F). 
It holds that (((Ω \ B) ∩ A) ∈ F). 
Qed. 


Lemma union_as_complements : 
  ∀ A B : subset U, 
    (A ∪ B) = (Ω \ ((Ω \ A) ∩ (Ω \ B))). 

Proof. 
Take A B : (subset U). 
We prove equality by proving two inclusions. 
Take x : U; Assume x_in_union. 
By union_to_or it holds that 
  (x ∈ A ∨ x ∈ B) (x_in_A_or_B). 
By classic it holds that 
  (¬((x ∉ A) ∧ (x ∉ B))) (not_not_A_and_not_B). 
By not_not_A_and_not_B it holds that 
  (¬(x ∈ (Ω \ A) ∧ x ∈ (Ω \ B))) (not_compA_and_compB). 
By not_compA_and_compB it holds that 
  (x ∉ ((Ω \ A) ∩ (Ω \ B))) (not_compA_int_compB). 
It holds that (x ∈ (Ω \ ((Ω \ A) ∩ (Ω \ B)))). 

Take x : U; Assume x_in_comp. 
We argue by contradiction. 
By union_to_or it holds that (¬ (x ∈ A ∨ x ∈ B)) (not_A_or_B).

It holds that 
  (x ∉ ((Ω \ A) ∩ (Ω \ B))) (not_compA_int_compB). 
By not_compA_int_compB it holds that 
  (¬(x ∈ (Ω \ A) ∧ x ∈ (Ω \ B))) (not_compA_and_compB). 
By not_compA_and_compB it holds that 
  (¬((x ∉ A) ∧ (x ∉ B))) (not_not_A_and_not_B). 
By not_not_A_and_not_B it holds that 
  ((x ∈ A ∨ x ∈ B)) (A_or_B). 
Contradiction. 
Qed. 

Lemma unions_in_π_and_λ : 
  ∀ F : setOfSubsets U, 
    F is_a_π-system ⇒ F is_a_λ-system
    ⇒ ∀ A B : subset U, A ∈ F ⇒ B ∈ F
      ⇒ A ∪ B ∈ F.

Proof. 
Take F : (setOfSubsets U). 
Assume F_is_π_system; Assume F_is_λ_system. 
Take A B : (subset U). 
Assume A_in_F; Assume B_in_F.

By union_as_complements it holds that 
  ((A ∪ B) = (Ω \ ((Ω \ A) ∩ (Ω \ B)))) (union_is_comp). 
Write goal using 
  ((A ∪ B) = (Ω \ ((Ω \ A) ∩ (Ω \ B)))) 
    as ((Ω \ ((Ω \ A) ∩ (Ω \ B))) ∈ F). 
By F_is_λ_system it holds that 
  ((Ω \ A) ∈ F) (comp_A_in_F). 
By F_is_λ_system it holds that 
  ((Ω \ B) ∈ F) (comp_B_in_F). 
By F_is_π_system it holds that 
  ((Ω \ A) ∩ (Ω \ B) ∈ F) (int_in_F). 
It holds that ((Ω \ ((Ω \ A) ∩ (Ω \ B))) ∈ F). 
Qed. 
 

Lemma complement_full_is_empty : 
  ∅ = (Ω \ Ω). 

Proof. 
We prove equality by proving two inclusions. 
Take x : U; Assume x_in_empty.
Contradiction. 

Take x : U; Assume x_in_complement_full.
Because x_in_complement_full 
  both x_in_full and not_x_in_full. 
Contradiction. 
Qed.


Lemma empty_in_λ : 
  ∀ F : setOfSubsets U, 
    F is_a_λ-system ⇒ ∅ ∈ F. 

Proof.  
Take F : (setOfSubsets U); Assume F_is_λ_system. 
By complement_full_is_empty it holds that 
  (∅ = (Ω \ Ω)) (comp_full_empty).
Write goal using (∅ = (Ω \ Ω)) as ((Ω \ Ω) ∈ F). 
It holds that ((Ω \ Ω) ∈ F). 
Qed.  


Lemma FU_S_as_union : 
  ∀ C : (ℕ → (subset U)), ∀ n : ℕ,
    finite_union_up_to C (S n) 
      = (finite_union_up_to C n) ∪ (C n). 

Proof. 
Take C : (ℕ → (subset U)). 
Take n : ℕ. 
We prove equality by proving two inclusions. 
Take x : U; Assume x_in_FU_S. 
Choose n0 such that x_in_C_n0 according to x_in_FU_S.
It holds that ((n0 ≤ n)%nat) (n0_le_n). (*avoid %nat? *) 
By leq_equiv it holds that 
  ((n0 < n)%nat ∨ n0 = n) (n0_l_e_n).
Because  n0_l_e_n either n0_l_n or n0_is_n. 
(*n0 < n*)
It holds that (x ∈ (finite_union_up_to C n)) (x_in_FU). 
It holds that (x ∈ (finite_union_up_to C n ∪ C n)). 
(*n0 = n*)
Write goal using (n = n0) as 
  (x ∈ (finite_union_up_to C n0 ∪ C n0)). 
It holds that (x ∈ C n0) (x_in_Cn0).
It holds that ( x ∈ (finite_union_up_to C n0 ∪ C n0)). 

Take x : U; Assume x_in_FU_with_Cn. 
By union_to_or it holds that 
  ((x ∈ (finite_union_up_to C n)) ∨ (x ∈ C n)) (x_in_FU_or_Cn).
It holds that (x ∈ finite_union_up_to C (S n)). 
Qed. 


Lemma FU_in_π_and_λ : 
  ∀ F : setOfSubsets U, 
    F is_a_π-system ⇒ F is_a_λ-system
    ⇒ ∀ C : (ℕ → (subset U)), (∀ n : ℕ, (C n) ∈ F) 
      ⇒ ∀ n : ℕ, (finite_union_up_to C n) ∈ F.

Proof. 
Take F : (setOfSubsets U). 
Assume F_is_π_system.
Assume F_is_λ_system.  
Take C : (ℕ ⇨ subset U). 
Assume all_Cn_in_F.
Take n : ℕ. 
We prove by induction on n.
(* Base case: *)
By FU_up_to_0_empty it holds that 
  (finite_union_up_to C 0 = ∅) (FU0_is_empty). 
Write goal using (finite_union_up_to C 0 = ∅) 
  as (∅ ∈ F). 
Apply empty_in_λ; Apply F_is_λ_system. 
(* Induction step: *)
By FU_S_as_union it holds that 
  (finite_union_up_to C (S n) 
    = (finite_union_up_to C n) ∪ (C n)) (FU_union).  
Write goal using 
  (finite_union_up_to C (S n) 
    = (finite_union_up_to C n) ∪ (C n)) 
      as ((finite_union_up_to C n) ∪ (C n) ∈ F).
By all_Cn_in_F it holds that (C n ∈ F) (Cn_in_F). 
By unions_in_π_and_λ it holds that 
  ((finite_union_up_to C n ∪ C n) ∈ F) which concludes the proof. 
  
Qed. 

Fixpoint aux_seq (A B : subset U) (n : ℕ) {struct n}
  : (subset U) :=
    match n with 
      0 => A 
    | 1 => B
    | n => ∅ 
    end. 


Lemma CU_aux_is_union : 
  ∀ A B : subset U, Countable_union (aux_seq A B) = A ∪ B. 

Proof. 
Take A B : (subset U). 
We prove equality by proving two inclusions. 
Take x : U; Assume x_in_CU. 
Choose n such that x_in_C_n according to x_in_CU. 
We prove by induction on n. 
It holds that (x ∈ (A ∪ B)). 
We prove by induction on n. 
It holds that (x ∈ (A ∪ B)). 

(* Write x_in_C_n as (x ∈ ∅).  *)
Contradiction. 

Take x : U; Assume x_in_intersection. 
destruct x_in_intersection. 
It holds that (x ∈ aux_seq A B 0) (x_in_aux0). 
We need to show that 
  (x ∈ ｛x0 : U | ∃ n : ℕ, x0 ∈ aux_seq A B n｝). 
It holds that (∃ n : ℕ, x ∈ aux_seq A B n) (exists_n_A). 
It follows that (x ∈ Countable_union (aux_seq A B)).

It holds that (x ∈ aux_seq A B 1) (x_in_aux0). 
We need to show that 
  (x ∈ ｛x0 : U | ∃ n : ℕ, x0 ∈ aux_seq A B n｝). 
It holds that (∃ n : ℕ, x ∈ aux_seq A B n) (exists_n_B). 
It follows that (x ∈ Countable_union (aux_seq A B)).
Qed. 


Lemma disjoint_aux : 
  ∀ A B : subset U, (Disjoint _ A B) 
    ⇒ (∀ m n : ℕ, m ≠ n ⇒ Disjoint _ (aux_seq A B m) (aux_seq A B n)). 

Proof. 
Take A B : (subset U). 
Assume A_B_disjoint. 
Take m n : ℕ. 
Assume m_neq_n. 
We prove by induction on m. 
We prove by induction on n.
(*Case m = n = 0:*)
Contradiction. 
(*Case m=0, n=1:*)
We prove by induction on n.
Write goal using (aux_seq A B 1 = B) as (Disjoint U (aux_seq A B 0) B).
Write goal using (aux_seq A B 0 = A) as (Disjoint U A B).
It holds that (Disjoint U A B).
(*Case m=0, n>1*)
Write goal using (aux_seq A B (S (S n)) = ∅) 
  as (Disjoint U (aux_seq A B 0) ∅). 
By empty_disjoint it holds that 
  (Disjoint U (aux_seq A B 0) ∅) which concludes the proof. 
  
(*Case m =1, n=0: *)
We prove by induction on m. 
We prove by induction on n. 
Write goal using (aux_seq A B 1 = B) 
  as (Disjoint U B (aux_seq A B 0)).
Write goal using (aux_seq A B 0 = A) 
  as (Disjoint U B A).
By disjoint_symmetric it holds that 
  ((Disjoint _ B A)) which concludes the proof.
  
(*Case m=n=1: *)
We prove by induction on n. 
Contradiction. 
(*Case m=1, n>1: *)
Write goal using (aux_seq A B (S (S n)) = ∅) 
  as (Disjoint U (aux_seq A B 1) ∅). 
By empty_disjoint it holds that 
  (Disjoint U (aux_seq A B 1) ∅) which concludes the proof. 
 
(*Case m>n: *)
Write goal using (aux_seq A B (S (S m)) = ∅) 
  as (Disjoint U ∅ (aux_seq A B n)). 
By disjoint_symmetric it holds that 
  (Disjoint U (aux_seq A B n) ∅ 
    ⇒ Disjoint U ∅ (aux_seq A B n)) (disj_symm). 
It suffices to show that (Disjoint U (aux_seq A B n) ∅). 
Apply empty_disjoint. 
Qed. 

(***********************************************************)
Require Import Reals. 

(*** NEW ***)
Record σ_algebra := make_sigma_algebra
  { underlying_set_of_subsets : setOfSubsets U;
    proof_is_sigma_algebra : is_σ_algebra underlying_set_of_subsets}.
Variable G : σ_algebra.
Coercion underlying_set_of_subsets : σ_algebra >-> setOfSubsets.
Definition F : setOfSubsets U := G.
Hint Resolve proof_is_sigma_algebra : measure_theory.
Hint Resolve underlying_set_of_subsets : measure_theory.

Lemma F_is_σ_algebra : is_σ_algebra F.

Proof. 
It holds that (is_σ_algebra (underlying_set_of_subsets G)) (xx). 
It holds that (is_σ_algebra F).
Qed.
Hint Resolve F_is_σ_algebra : measure_theory.


Definition σ_additive_on F (μ : (subset U ⇨ ℝ)) : Prop := 
  ∀C : (ℕ → (subset U)), (∀n : ℕ, C n ∈ F) 
    ⇒ (∀ m n : ℕ, m ≠ n ⇒ Disjoint _ (C m) (C n)) 
      ⇒ infinite_sum (fun (n:ℕ) ↦ (μ (C n))) (μ (Countable_union C)).
(*infinite_sum fn l is the proposition 'the sum of all terms of fn converges to l'*)

Notation "μ is_σ-additive_on F" := 
  (σ_additive_on F μ) (at level 50). 

Notation "｜ x - y ｜" := (R_dist x y) (at level 20).


Definition is_measure_on (F : setOfSubsets U) (μ : (subset U → ℝ)) : Prop := 
  is_σ_algebra F ∧ μ ∅ = 0 ∧ μ is_σ-additive_on F.

Definition set_function {U} := (subset U ⇨ ℝ).

Record measure_on {F} := make_measure 
  { underlying_function : set_function; 
    proof_is_measure : is_measure_on F underlying_function}.
Variable ν : @measure_on F.
Coercion underlying_function : measure_on >-> set_function.
Definition μ : set_function := ν.
Hint Resolve underlying_function : measure_theory.
Hint Resolve proof_is_measure : measure_theory.

Lemma μ_is_measure_on_F : is_measure_on F μ.

Proof. 
It holds that (is_measure_on F (underlying_function ν)) (xx). 
It holds that (is_measure_on F μ).
Qed.
Hint Resolve μ_is_measure_on_F : measure_theory.

Definition is_probability_measure_on (F : setOfSubsets U) (μ : (subset U → ℝ)) 
  : Prop := 
    is_measure_on F μ ∧ μ Ω = 1.

Definition is_increasing_seq_sets (C : (ℕ → (subset U)))
  : Prop := 
    ∀n : ℕ, (C n) ⊂ C (S n).

Lemma increasing_seq_mn : 
     ∀ C : (ℕ → (subset U)), 
      is_increasing_seq_sets C 
        ⇒ (∀m n : ℕ, (m ≤ n)%nat 
          ⇒ C m ⊂ C n).

Proof. 
Take C : (ℕ ⇨ subset U). 
Assume C_is_increasing.
Take m n : ℕ; Assume m_le_n. 
induction n.
It holds that ((m = 0)%nat) (m0).
Write goal using ((m = 0)%nat) 
  as (C 0%nat ⊂ C 0%nat).
It holds that (C 0%nat ⊂ C 0%nat).
By leq_equiv it holds that 
  (((m < (S n))%nat ∨ m = (S n))) (m_l_eq_Sn).
Because m_l_eq_Sn either m_l_Sn or m_eq_Sn.
By IHn it holds that 
  (C m ⊂ C n) (Cm_subs_Cn). 
By C_is_increasing it holds that
  (C n ⊂ C (S n)) (Cn_subs_CSn).
It follows that (C m ⊂ C (S n)). 

Write goal using (m = S n) 
  as (C (S n) ⊂ C (S n)). 
It holds that (C (S n) ⊂ C (S n)). 
Qed.   



Lemma empty_in_σ : 
  F is_a_σ-algebra ⇒ ∅ ∈ F. 

Proof.  
(*Assume F_is_σ_algebra. *)
By complement_full_is_empty it holds that 
  (∅ = (Ω \ Ω)) (comp_full_empty).
Write goal using (∅ = (Ω \ Ω)) as ((Ω \ Ω) ∈ F). 
By F_is_σ_algebra it holds that ((Ω \ Ω) ∈ F) which concludes the proof. 
Qed.  


Lemma unions_in_σ : 
  F is_a_σ-algebra
    ⇒  ∀ A B : subset U, A ∈ F ∧ B ∈ F
      ⇒ A ∪ B ∈ F.

Proof. 
Assume F_is_σ_algebra. 
Take A B : (subset U). 
Assume A_and_B_in_F. 

We claim that (∀ n : ℕ, aux_seq A B n ∈ F) (all_aux_in_F). 
Take n : ℕ. 
We prove by induction on n. 
It holds that (aux_seq A B 0 ∈ F). 
We prove by induction on n. (*0 and 1 defined, rest inductively. Other way? *)
It holds that (aux_seq A B 1 ∈ F). 
Write goal using (aux_seq A B (S (S n)) = ∅) 
  as (∅ ∈ F). 
By empty_in_σ it holds that 
  (∅ ∈ F) (empty_in_F).
Apply empty_in_F.  

By CU_aux_is_union it holds that 
  (A ∪ B = Countable_union (aux_seq A B)) (union_to_CU). 
Write goal using (A ∪ B = Countable_union (aux_seq A B))
  as (Countable_union (aux_seq A B) ∈ F).
It holds that (Countable_union (aux_seq A B) ∈ F). 
Qed.




Lemma FU_in_sigma : 
  F is_a_σ-algebra
    ⇒ ∀ C : (ℕ → (subset U)), (∀ n : ℕ, (C n) ∈ F) 
      ⇒ ∀ n : ℕ, (finite_union_up_to C n) ∈ F.

Proof. 
Assume F_is_σ.  
Take C : (ℕ ⇨ subset U). 
Assume all_Cn_in_F.
Take n : ℕ. 
We prove by induction on n.
(* Base case: *)
By FU_up_to_0_empty it holds that 
  (finite_union_up_to C 0 = ∅) (FU0_is_empty). 
Write goal using (finite_union_up_to C 0 = ∅) 
  as (∅ ∈ F). 
Apply empty_in_σ; Apply F_is_σ. 
(* Induction step: *)
By FU_S_as_union it holds that 
  (finite_union_up_to C (S n) 
    = (finite_union_up_to C n) ∪ (C n)) (FU_union).  
Write goal using 
  (finite_union_up_to C (S n) 
    = (finite_union_up_to C n) ∪ (C n)) 
      as ((finite_union_up_to C n) ∪ (C n) ∈ F).
By all_Cn_in_F it holds that (C n ∈ F) (Cn_in_F). 
By unions_in_σ it holds that 
  ((finite_union_up_to C n ∪ C n) ∈ F) (xx); Apply xx. 
Qed. 

Chapter add_and_cont. 
Variable μ : (subset U → ℝ).
 
Section finite_additivity. 
Variable A B : subset U.

Lemma aux_additive : 
  is_measure_on F μ 
    ⇒ A ∈ F ⇒ B ∈ F
      ⇒ Disjoint _ A B  
         ⇒ (infinite_sum (fun (n:ℕ) ↦ (μ ((aux_seq A B) n))) 
  (μ (Countable_union (aux_seq A B)))).

Proof. 
Assume μ_is_measure_on_F. 
Assume A_in_F; Assume B_in_F.
Assume A_B_disjoint.
Define C := (aux_seq A B).
By μ_is_measure_on_F it holds that 
  (μ is_σ-additive_on F) (add_on_F).
Apply add_on_F.
Take n : ℕ. 
We prove by induction on n.
It holds that (C 0%nat ∈ F).
We prove by induction on n.
It holds that (C 1%nat ∈ F).

It holds that (C (S (S n)) = ∅) (CSS_empty). 
By empty_in_σ it holds that 
  (C (S (S n)) ∈ F) which concludes the proof. 
 

By disjoint_aux it holds that 
  ( ∀ m n : ℕ,
    m ≠ n ⇨ Disjoint U (C m) (C n)) which concludes the proof. 
  
Qed.


Lemma aux_ge2_empty : 
  ∀ n : ℕ, 
    (n > 1)%nat ⇒ aux_seq A B n = ∅. 

Proof.
Take n : ℕ; Assume n_g_1. 
Expand the definition of aux_seq.
(*More case distinction than induction, but 
  this works far better for 'Fixpoint' definitions*)
We prove by induction on n. 
It holds that (¬(0 > 1)%nat) (not_0_g_1). 
Contradiction.
We prove by induction on n. 
It holds that (¬(1 > 1)%nat) (not_1_g_1). 
Contradiction. 
It holds that (∅ = ∅). 
Qed. 


Lemma FUn_disj_is_Cn : 
  is_increasing_seq_sets C
    ⇒ ∀ n : ℕ, finite_union_up_to (disjoint_seq C) (S n) = C n.

Proof. 
Assume C_is_incr_seq.
Define D := (disjoint_seq C). 
Take n : ℕ. 
We prove equality by proving two inclusions. 
Take x : U; Assume x_in_FU. 
Choose n0 such that x_in_Dn0 according to x_in_FU. 
By x_in_Dn0 it holds that 
  (x ∈ C n0) (x_in_Cn0).
(*It holds that ((n0 < n)%nat) (n0_l_n). 
By l_equiv it holds that 
  (n0 = (n - 1)%nat ∨ (n < n - 1)%nat) (n0_eq_l_n1).*) 
By increasing_seq_mn it holds that 
  (C n0 ⊂ C n) (Cn0_subs_Cn). 
It follows that (x ∈ C n). 

Take x : U; Assume x_in_C.
Define aux_prop := (fun (n : ℕ) ↦ (x ∈ C n)). (*n-1?*)
By classic it holds that 
  (∀ n, aux_prop n ∨ ¬aux_prop n) (aux_prop_decidable). 
By dec_inh_nat_subset_has_unique_least_element it holds that
  (has_unique_least_element le aux_prop) (exists_least_n). 
Choose n1 such that x_in_C_minimal_n according to exists_least_n. 
It holds that ( aux_prop n1 
  ∧ ( ∀ n2 : ℕ, aux_prop n2 
    ⇒ (n1 ≤ n2)%nat)) (aux_n1_and_n1_le_n2).
Because aux_n1_and_n1_le_n2 both aux_n1 and n1_le_n2. 
It holds that (x ∈ D n1) (x_in_Dn1). 
We claim that ( (n1 < S n)%nat ) (n1_l_n).
By x_in_C it holds that (aux_prop n) (aux_n_min_1). 
By n1_le_n2 it holds that 
  ((n1 ≤ n)%nat) (n1_leq_n_min_1). 
It holds that 
  ((n1 < S n)%nat). 
  
It holds that (∃i : ℕ,  
  ((i < (S n))%nat ∧ x ∈ (D i))) (exists_i). 
It follows that (x ∈ finite_union_up_to D (S n)).
Qed.


Lemma intersection_to_complement : 
   ∀ A B : subset U, 
    A ∩ B = Ω \ ((Ω \ A) ∪ (Ω \ B)). 

Proof. (*analogous to complement_as_union_intersection, could be combined? *)
Take A B : (subset U). 
We prove equality by proving two inclusions. 
Take x : U; Assume x_in_lhs. 
destruct x_in_lhs. (*"Because x_in_rhs both x_in_comp_A and x_in_B" doesn't work*)
By H it holds that (x ∉ Ω \ A) (x_not_in_A). 
By H0 it holds that (x ∉ Ω \ B) (x_not_in_comp). 

We claim that (x ∉ (Ω \ A) ∪ (Ω \ B)) (x_not_in_AB).
We argue by contradiction. 
We claim that (x ∈ (Ω \ A) ∪ (Ω \ B)) (x_in_AB).
Apply NNPP; Apply H1.   
destruct x_in_AB. 
Contradiction.
Contradiction. 
It follows that (x ∈ Ω \ ((Ω \ A) ∪ (Ω \ B))). 

Take x : U; Assume x_in_rhs. 
destruct x_in_rhs.
By H0 it holds that 
  ((x ∉ Ω \ A) ∧ (x ∉ Ω \ B)) (x_not_in_int_comp). 
Because x_not_in_int_comp 
  both x_not_in_compA and x_not_in_compB.
We claim that (x ∈ A) (x_in_A).
We argue by contradiction. 
By H1 it holds that (x ∈ Ω \ A) (x_in_compA).
Contradiction.  

We claim that (x ∈ B) (x_in_B).
We argue by contradiction. 
By H1 it holds that (x ∈ Ω \ B) (x_in_compB).
Contradiction. 
It follows that (x ∈ A ∩ B). 
Qed.  


Lemma intersections_in_σ : 
  F is_a_σ-algebra 
    ⇒  ∀ A B : subset U, A ∈ F ∧ B ∈ F
      ⇒ A ∩ B ∈ F.

Proof. 
Assume F_is_σ_algebra. 
Take A B : (subset U). 
Assume A_and_B_in_F. 
By intersection_to_complement it holds that 
  (A ∩ B = Ω \ ((Ω \ A) ∪ (Ω \ B))) (int_is_comp). 
Write goal using (A ∩ B = Ω \ ((Ω \ A) ∪ (Ω \ B)))
  as (Ω \ ((Ω \ A) ∪ (Ω \ B)) ∈ F). 
By unions_in_σ it holds that 
 ((Ω \ A) ∪ (Ω \ B) ∈ F) (compA_compB_in_F). 
It follows that (Ω \ ((Ω \ A) ∪ (Ω \ B)) ∈ F).
Qed.


Lemma complements_in_σ : 
  F is_a_σ-algebra
    ⇒ ∀ A B : subset U, A ∈ F ∧ B ∈ F
      ⇒ A \ B ∈ F. 

Proof. 
Assume F_is_σ.
Take A B : (subset U). 
Assume A_and_B_in_F. 
By F_is_σ it holds that 
  (Ω \ B ∈ F) (comp_B_in_F). 
By intersections_in_σ it holds that 
  ((Ω \ B) ∩ A ∈ F) (set_in_F). 
By complement_as_intersection it holds that 
  (A \ B = (Ω \ B) ∩ A) (set_is_complement). 
Write goal using (A \ B = ((Ω \ B) ∩ A)) 
  as (((Ω \ B) ∩ A) ∈ F). 
It holds that ((Ω \ B) ∩ A ∈ F). 
Qed. 


Lemma disj_seq_in_F : 
  F is_a_σ-algebra 
    ⇒ ∀C : (ℕ → (subset U)), is_increasing_seq_sets C
      ⇒ (∀ n : ℕ, C n ∈ F)
        ⇒ (∀n : ℕ, (disjoint_seq C) n ∈ F). 

Proof. 
Assume F_is_σ. 
Take C : (ℕ ⇨ subset U) . 
Assume C_is_incr_seq.
Assume all_Cn_in_F.
Define D := (disjoint_seq C). 

Take n : ℕ. 
We need to show that (C n \ (finite_union_up_to C n) ∈ F).
We claim that ((finite_union_up_to C n) ∈ F) (FU_in_F). 
Apply FU_in_sigma.
Apply F_is_σ. 
Apply all_Cn_in_F. 
It holds that (C n ∈ F) (Cn_in_F).
By complements_in_σ it holds that 
  (C n \ finite_union_up_to C n ∈ F) which concludes the proof.
Qed. 



Lemma additivity_meas : 
  is_measure_on F μ 
    ⇒ A ∈ F ⇒ B ∈ F
      ⇒ Disjoint _ A B  
         ⇒ μ (A ∪ B) = μ A + μ B. 

Proof. 
Assume μ_is_measure_on_F. 
Assume A_in_F; Assume B_in_F.
Assume A_B_disjoint.
Define C := (aux_seq A B).
Define seq_μC := (fun (n:ℕ) ↦ (μ (C n))).
By CU_aux_is_union it holds that 
  (A ∪ B = Countable_union C) (union_is_CU).
Write goal using (A ∪ B = Countable_union C)
  as (μ (Countable_union C) = μ A + μ B).
By aux_additive it holds that 
  (infinite_sum seq_μC 
    (μ (Countable_union C))) (sum_meas_is_meas_CU).

We claim that (infinite_sum seq_μC 
  (μ A + μ B)) (series_is_sumAB). 
We need to show that (
   ∀ ε : ℝ, ε > 0
    ⇒ ∃ N : ℕ ,
       ∀ n : ℕ, (n ≥ N)%nat 
        ⇒ R_dist (sum_f_R0 seq_μC n) (μ A + μ B) < ε).
        (*⇒ ｜ (sum_f_R0 seq_μC n) - (μ A + μ B) ｜ < ε). *)
Take ε : R; Assume ε_g0. 

We claim that ( ∀ n : ℕ, (n ≥ 1)%nat 
  ⇒ R_dist (sum_f_R0 seq_μC n) 
    (μ A + μ B) < ε) (holds_for_ge_1).
We prove by induction on n. 
(* n=0: *)
It holds that (¬(0 ≥ 1)%nat) (not_0_geq_1). 
Contradiction.
(* induction step *)
It holds that ((n ≥ 0)%nat) (n_geq_0). 
By geq_equiv it holds that 
  (n = 0%nat ∨ (n > 0)%nat) (n_0_or_n_g0).
Because n_0_or_n_g0 either n_0 or n_g0. 
(* n=0: *)
It holds that (S n = 1%nat) (Sn_is_1).
Write goal using (S n = 1%nat)
  as ((1 ≥ 1)%nat 
  ⇒ R_dist (sum_f_R0 seq_μC 1) 
    (μ A + μ B) < ε).
Write goal using (sum_f_R0 seq_μC 1 = μ A + μ B)
  as (R_dist (μ A + μ B) (μ A + μ B) < ε). 
By R_dist_eq it holds that 
  (R_dist (μ A + μ B)  (μ A + μ B) = 0) (dist_is_0).
It follows that (R_dist (μ A + μ B) (μ A + μ B) < ε).
(* n>0: *)
It holds that ((n ≥ 1)%nat) (n_geq_1).
By IHn it holds that 
  (R_dist (sum_f_R0 seq_μC n) (μ A + μ B) < ε) (dist_l_eps). 
We claim that (seq_μC (S n) = 0) (µSn_0).
By aux_ge2_empty it holds that 
  (C (S n) = ∅) (CSn_empty).
By μ_is_measure_on_F it holds that 
  (μ ∅ = 0) (µ_empty_0). 
We need to show that (μ (C (S n)) = 0).
Write goal using (C (S n) = ∅)
  as (μ ∅ = 0).
Apply µ_empty_0. 

Write goal using (sum_f_R0 seq_μC (S n)
  = sum_f_R0 seq_μC n + seq_μC (S n))
    as (R_dist (sum_f_R0 seq_μC n + seq_μC (S n)) 
      (μ A + μ B) < ε). 
Write goal using (seq_μC (S n) = 0) 
  as (R_dist (sum_f_R0 seq_μC n + 0) (μ A + μ B) < ε).
Write goal using (sum_f_R0 seq_μC n + 0 = sum_f_R0 seq_μC n)
  as (R_dist (sum_f_R0 seq_μC n ) (μ A + μ B) < ε).
Apply dist_l_eps.

It follows that (∃ N : ℕ ,
  ∀ n : ℕ, (n ≥ N)%nat 
    ⇒ R_dist (sum_f_R0 seq_μC n) 
      (μ A + μ B) < ε). 
By uniqueness_sum it holds that 
  (μ (Countable_union C) = μ A + μ B) which concludes the proof.
Qed.

End finite_additivity. 



Section finite_additivityy.
Variable C : (ℕ → (subset U)).


Lemma FU_up_to_1_is_0 : 
  finite_union_up_to C 1 = C 0%nat.

Proof. 
We prove equality by proving two inclusions. 
Take x : U; Assume x_in_FU.
destruct x_in_FU. 
It holds that (x0 = 0%nat) (x0_is_0).
Write goal using (0%nat = x0) 
  as (x ∈ C x0). 
It holds that (x ∈ C x0).

Take x : U; Assume x_in_C0. 
It holds that (x ∈ finite_union_up_to C 1). 
Qed. 

Lemma finite_additivity_meas : 
  is_measure_on F μ 
    ⇒ (∀n : ℕ, C n ∈ F) 
      ⇒ (∀ m n : ℕ, m ≠ n ⇒ Disjoint _ (C m) (C n))  
         ⇒ ∀ N : ℕ,  μ (finite_union_up_to C (S N))
          = sum_f_R0 (fun (n : ℕ) ↦ (μ (C n))) N.

Proof. 
Assume μ_is_measure_on_F. 
Assume all_Cn_in_F.  
Assume C_n_disjoint. 
Define seq_μC := (fun (n : ℕ) ↦ μ (C n)). 
Define FU_C := (finite_union_up_to C). 
Take N : ℕ.
We prove by induction on N. 
(* Base case: *)
By FU_up_to_1_is_0 it holds that 
  (finite_union_up_to C 1 = C 0%nat) (FU1_is_C0).
Write goal using (FU_C 1%nat = C 0%nat)
  as (μ (C 0%nat) = sum_f_R0 seq_μC 0%nat).
It holds that (μ (C 0%nat) = sum_f_R0 seq_μC 0). 
(*Induction step: *)
It holds that (sum_f_R0 seq_μC (S N) 
  = sum_f_R0 seq_μC N + seq_μC (S N)) (sum_to_sum).
Write goal using (sum_f_R0 seq_μC (S N) 
  = sum_f_R0 seq_μC N + seq_μC (S N)) 
    as (μ (FU_C (S (S N)))
      = sum_f_R0 seq_μC N + seq_μC (S N)). 

By FU_S_as_union it holds that 
  (FU_C (S (S N)) 
    = (FU_C (S N)) ∪ (C (S N))) (FU_to_union). 
We claim that (Disjoint _ 
  (FU_C (S N)) (C (S N))) (FUSn_CSn_disj). 
We argue by contradiction. 
By H it holds that (∃ x : U, 
  x ∈ ((FU_C (S N)) ∩ (C (S N)))) (int_not_empty).
Choose x such that x_in_int 
  according to int_not_empty. 
destruct x_in_int. (*how to destruct with certain names?*)
Choose n0 such that x_in_Cn 
  according to H0.
It holds that (x ∈ C n0 ∧ x ∈ C (S N)) (x_in_Cn0_and_CSN). 
By C_n_disjoint it holds that 
  (Disjoint _ (C n0) (C (S N))) (Cn0_CSN_disj). 
destruct Cn0_CSN_disj. 
It holds that (x ∉ C n0 ∩ C (S N)) (not_x_in_int_Cn0_CSN).
By not_x_in_int_Cn0_CSN it holds that 
  (¬ (x ∈ C n0 ∧ x ∈ C (S N))) (not_x_in_Cn0_and_CSN).
Contradiction. 
(*now show: both sets in F *)
It holds that (C (S N) ∈ F) (CSN_in_F). 
By FU_in_sigma it holds that 
  (FU_C (S N) ∈ F) (FU_C_in_F). 
  
By additivity_meas it holds that
  (μ ((FU_C (S N)) ∪ (C (S N))) 
    = μ (FU_C (S N)) + μ (C (S N))) (muFUS_is_muFU_muS).

Write goal using (FU_C (S (S N)) 
  = (FU_C (S N)) ∪ (C (S N)))
    as (μ ((FU_C (S N)) ∪ (C (S N))) 
      = sum_f_R0 seq_μC N + seq_μC (S N)).
Write goal using (μ ((FU_C (S N)) ∪ (C (S N))) 
  = μ (FU_C (S N)) + μ (C (S N)))
    as (μ (FU_C (S N)) + μ (C (S N)) 
      = sum_f_R0 seq_μC N + seq_μC (S N)). 
It holds that (μ (FU_C (S N)) + μ (C (S N)) 
  = sum_f_R0 seq_μC N + seq_μC (S N)). 
Qed.



Lemma incr_cont_meas : 
  ∀μ : (subset U → ℝ), is_measure_on F μ 
    ⇒ ∀C : (ℕ → (subset U)), is_increasing_seq_sets C
      ⇒ (∀ n : ℕ, C n ∈ F)
        ⇒ Un_cv (fun (n : ℕ) ↦ (μ (C n))) (μ (Countable_union C)). 
(*Un_cv Cn l is the proposition 'sequence Cn converges to limit l'*)
(*Proof using alternative sequence from pi-lambda proof; not the one in lecture notes*)
Proof. 
Take μ : (subset U ⇨ ℝ). 
Assume μ_is_measure_on_F. 
Take C : (ℕ ⇨ subset U) . 
Assume C_is_incr_seq.
Assume all_Cn_in_F.
Define D := (disjoint_seq C). 
Define seq_μC := (fun (n : ℕ) ↦ μ (C n)). 
Define seq_μD := (fun (n : ℕ) ↦ μ (D n)).
By CU_sets_disjointsets_equal it holds that 
  ((Countable_union C) = (Countable_union D)) (CUC_is_CUD).
Write goal using 
  ((Countable_union C) = (Countable_union D)) 
    as (Un_cv seq_μC (μ (Countable_union D))). 
By μ_is_measure_on_F it holds that 
  (μ is_σ-additive_on F) (μ_is_σ_additive). 
By disj_seq_disjoint it holds that 
  (∀ m n : ℕ, m ≠ n ⇒ Disjoint _ (D m) (D n)) (D_disj). 
By disj_seq_in_F it holds that 
  (∀n : ℕ, D n ∈ F) (all_Dn_in_F).
By μ_is_σ_additive it holds that 
  (infinite_sum (fun (n:ℕ) ↦ (μ (D n))) 
    (μ (Countable_union D))) (μDn_is_μCUD).

We need to show that (
  ∀ ε : ℝ, ε > 0
    ⇒ ∃ N : ℕ , ∀ n : ℕ,  (n ≥ N)%nat 
      ⇒ R_dist (μ (C n)) (μ (Countable_union D)) < ε).
Take ε : ℝ; Assume ε_g0. 
By μDn_is_μCUD it holds that (
  ∃ N : ℕ , ∀ n : ℕ,  (n ≥ N)%nat 
    ⇒ R_dist (sum_f_R0 seq_μD n)
     (μ (Countable_union D)) < ε) (exists_N_μSumD_μCUD_l_ε).
Choose N such that μSumN_μCU_l_ε 
  according to exists_N_μSumD_μCUD_l_ε.

We claim that (∀ n : ℕ,
  (n ≥ N)%nat ⇨ R_dist (μ (C n)) 
    (μ (Countable_union D)) < ε) (holds_forall_n_geq_N). 
Take n : ℕ; Assume n_geq_N.
We claim that (μ(C n) = 
  (sum_f_R0 seq_μD n) ) (μCn_is_sum_μDn). 
By FUn_disj_is_Cn it holds that 
  (finite_union_up_to D (S n) = C n) (FUD_is_C).
Write goal using (C n = finite_union_up_to D (S n))
  as (μ (finite_union_up_to D (S n)) 
    = sum_f_R0 seq_μD n). 
By finite_additivity_meas it holds that 
  (μ (finite_union_up_to D (S n)) 
    = sum_f_R0 (fun (n : ℕ) ↦ μ (D n)) n) (xx); Apply xx. 

Write goal using (μ (C n) = sum_f_R0 seq_μD n) 
  as (R_dist (sum_f_R0 ｛ n0 : ℕ | μ (D n0) ｝ n) 
    (μ (Countable_union D)) < ε).
It holds that (R_dist (sum_f_R0 seq_μD n) 
  (μ (Countable_union D)) < ε). 
It follows that (∃ N0 : ℕ ,
   ∀ n : ℕ, (n ≥ N0)%nat 
    ⇒ R_dist (μ (C n)) (μ (Countable_union D)) < ε). 
Qed. 





Lemma monotonicity_meas :
  ∀μ : (subset U → ℝ), is_measure_on F μ 
    ⇒ ∀ A B : subset U, A ⊂ B 
      ⇒ μ A ≤ μ B. 

Proof. 

Admitted. 




Theorem uniqueness_of_prob_meas : 
  ∀μ1 : (subset U → ℝ), is_measure_on F μ1 
    ⇒ ∀μ2 : (subset U → ℝ), is_measure_on F μ2 
      ⇒ ∀Π, Π is_a_π-system (* ⇒ Π ⊂ F *)
        ⇒ ∀ A : subset U, A ∈ Π ⇒ μ1 A = μ2 A
          ⇒ ∀ B : subset U, B ∈ (σ(Π)) ⇒ μ1 A = μ2 A. 
Proof. 
Admitted. 



