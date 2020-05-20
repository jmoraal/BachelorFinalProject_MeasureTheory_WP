(*Version 1.1.4 - 15-05-2020
  new brackets as not to conflict coq notation {x : A | P}
  imported lemmas on CU, disjointness and disjoint sets
  proof of incr_cont_meas continued
  notations for set and setOfSets adapted to subsets of U
  adapted notation improved, dependent on U
  WP library added manually to continue for now
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
  | [|-?x <= ?z] => 
    match (type of eq_or_ineq) with 
    | (x <= ?y) => apply (Rle_trans x y z eq_or_ineq)
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


Notation "'subset' U" := 
  (Ensemble U) (at level 50). 

Notation "'setOfSubsets' U" := 
  (Ensemble (subset U)) (at level 50). 

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
  (~ In _ A x) (at level 55). 

Notation "A ⊂ B" := 
  (Included _ A B) (at level 50). 

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

Inductive σ_algebra : setOfSubsets U := 
  | σ_alg_omeg : full_set_in_set σ_algebra
  | σ_alg_comp : complement_in_set σ_algebra
  | σ_alg_cuCU : closed_under_countable_union σ_algebra. 


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

(***********************************************************)
Require Import Reals. 
Variable F : setOfSubsets U. 
(*Definition σ_algebras := (sig (is_σ_algebra)). *)

(*
Definition σ_algebra1 := sig is_σ_algebra. 
Variable F : σ_algebra1. 
Definition myclass :=  Ensemble (Ensemble U). 
Definition myprojection : (σ_algebra1 -> myclass) := (@proj1_sig myclass is_σ_algebra). 
Coercion myprojection : σ_algebra1 >-> myclass.  
*)
Definition σ_additive_on (F : setOfSubsets U) (μ : (subset U ⇨ ℝ)) : Prop := 
  ∀C : (ℕ → (subset U)), (∀n : ℕ, C n ∈ F) 
    ⇒ (∀ m n : ℕ, m ≠ n ⇒ Disjoint _ (C m) (C n)) 
      ⇒ infinite_sum (fun (n:ℕ) ↦ (μ (C n))) (μ (Countable_union C)).
(*infinite_sum fn l is the proposition 'the sum of all terms of fn converges to l'*)
Notation "μ is_σ-additive_on F" := 
  (σ_additive_on F μ) (at level 50). 


Definition is_measure_on (F : setOfSubsets U) (μ : (subset U → ℝ)) : Prop := 
  is_σ_algebra F ∧ μ ∅ = 0 ∧ μ is_σ-additive_on F.

Definition is_probability_measure_on (F : setOfSubsets U) (μ : (subset U → ℝ)) 
  : Prop := 
    (is_measure_on F μ) ∧ (μ Ω = 1).

Definition is_increasing_seq_sets (C : (ℕ → (subset U)))
  : Prop := 
    ∀n : ℕ, (C n) ⊂ C (S n).
(*
Fixpoint finite_seq (C : (ℕ → (subset U))) (p : Prop) (n : ℕ) {struct p}
  : (subset U) :=
    match p with 
      0 => C 0
    | S p => (fun  ↦ ∅)
    end.  
*)
Lemma finite_additivity_meas : 
  ∀μ : (subset U → ℝ), is_measure_on F μ 
    ⇒ ∀C : (ℕ → (subset U)), 
      (∀ m n : ℕ, m ≠ n ⇒ Disjoint _ (C m) (C n))  
         ⇒ ∀ N : ℕ, μ (finite_union_up_to C N) 
          = sum_f_R0 (fun (n : ℕ) ↦ (μ (C n))) (N-1).

Proof. 
Take μ : (subset U ⇨ ℝ). 
Assume μ_is_measure_on_F. 
Take C : (ℕ ⇨ subset U) . 
Assume C_n_disjoint. 
Take N : ℕ.


Admitted.
 

Lemma monotonicity_meas :
  ∀μ : (subset U → ℝ), is_measure_on F μ 
    ⇒ ∀ A B : subset U, A ⊂ B 
      ⇒ μ A ≤ μ B. 
Admitted. 

(*Proof using alternative sequence from pi-lambda proof*)
Lemma incr_cont_meas : 
  ∀μ : (subset U → ℝ), is_measure_on F μ 
    ⇒ ∀C : (ℕ → (subset U)), is_increasing_seq_sets C
      ⇒ Un_cv (fun (n : ℕ) ↦ (μ (C n))) (μ (Countable_union C)). 
(*Un_cv Cn l is the proposition 'sequence Cn converges to limit l'*)
Proof. 
Take μ : (subset U ⇨ ℝ). 
Assume μ_is_measure_on_F. 
Take C : (ℕ ⇨ subset U) . 
Assume C_is_incr_seq.
(*We need to show that (
  ∀ ε : ℝ, ε > 0
    ⇒ ∃ N : ℕ , ∀ n : ℕ,  (n ≥ N)%nat 
      ⇒ R_dist (μ (C n)) (μ (Countable_union C)) < ε). 
(*notation |.| for R_dist?*)
Take ε : ℝ; Assume ε_g0. *)
Define D := (disjoint_seq C). 
By CU_sets_disjointsets_equal it holds that 
  ((Countable_union C) = (Countable_union D)) (CUC_is_CUD).
Write goal using 
  ((Countable_union C) = (Countable_union D)) 
    (*as (∃ N : ℕ , ∀ n : ℕ,  (n ≥ N)%nat 
      ⇒ R_dist (μ (C n)) (μ (Countable_union D)) < ε).*) 
    as (Un_cv (fun (n : ℕ) ↦ (μ (C n))) (μ (Countable_union D))). 
By μ_is_measure_on_F it holds that 
  (μ is_σ-additive_on F) (μ_is_σ_additive). 
By disj_seq_disjoint it holds that 
  (∀ m n : ℕ, m ≠ n ⇒ Disjoint _ (D m) (D n)) (D_disj). 
(*To show: all D n in F*)
By μ_is_σ_additive it holds that 
  (infinite_sum (fun (n:ℕ) ↦ (μ (D n))) 
    (μ (Countable_union D))) (μDn_is_μCUD).



Admitted. 







Theorem uniqueness_of_prob_meas : 
  ∀μ1 : (subset U → ℝ), is_measure μ1 
    ⇒ ∀μ2 : (subset U → ℝ), is_measure μ2 
      ⇒ ∀Π, Π is_a_π-system (* ⇒ Π ⊂ F *)
        ⇒ ∀ A : subset U, A ∈ Π ⇒ μ1 A = μ2 A
          ⇒ ∀ B : subset U, B ∈ (σ(Π)) ⇒ μ1 A = μ2 A. 
Admitted. 

(************)
(*   Old:   *)
(************)
Definition aux_seq (C : (ℕ → (subset U))) 
  : ℕ → (subset U) := 
    fun (n : nat) ↦ (C (S n) \ C n).

Lemma aux_set_disjoint : 
  ∀ C : (ℕ → (subset U)), 
    is_increasing_seq_sets C 
      ⇒ (∀ m n : ℕ, m ≠ n ⇒ Disjoint _ (aux_seq C m) (aux_seq C n)). 

Proof. 
Take C : (ℕ ⇨ subset U) . 
Assume C_is_incr_seq.
Take m n : ℕ; Assume m_neq_n. 
Define E := (aux_seq C). 
It suffices to show that 
  (∀ x:U, x ∉ (E m ∩ E n)).
Take x : U. 
We argue by contradiction.
We claim that (x ∈(E m ∩ E n)) (x_in_EmEn). 
Apply NNPP; Apply H. 
Admitted. 

Lemma CU_aux_is_CU : 
  ∀ C : (ℕ → (subset U)), 
    is_increasing_seq_sets C 
      ⇒ Countable_union (aux_seq C) = Countable_union C.

Proof. 
Take C  : (ℕ ⇨ subset U) . 
Assume C_is_incr_seq.
Define E := (aux_seq C). 
We prove equality by proving two inclusions. 
Take x : U; Assume x_in_CU_E. 
Choose n such that x_in_En according to x_in_CU_E.
It holds that (x ∈ C (S n)) (x_in_Cn). 
It follows that (x ∈ Countable_union C). 

Take x : U; Assume x_in_CU_C. 
Choose n such that x_in_Cn according to x_in_CU_C.
Define aux_prop := (fun (n : ℕ) ↦ (x ∈ C n)).
By classic it holds that 
  (∀ n, aux_prop n ∨ ¬aux_prop n) (aux_prop_decidable). 
By dec_inh_nat_subset_has_unique_least_element it holds that
  (has_unique_least_element le aux_prop) (exists_least_n). 
Choose n1 such that x_in_C_minimal_n according to exists_least_n. 
We prove by induction on n1. 


It holds that (x ∈ Countable_union E). 




