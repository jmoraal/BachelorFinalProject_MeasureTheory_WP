
(** # Tactics for Waterproof*)
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


Hint Unfold In Included Same_set Strict_Included Add Setminus Subtract: sets.

Hint Resolve Union_introl Union_intror Intersection_intro In_singleton
  Couple_l Couple_r Triple_l Triple_m Triple_r Disjoint_intro
  Extensionality_Ensembles: sets.
Hint Resolve Full_intro : measure_theory.  (*nieuwe database measure theory*)
Hint Resolve Intersection_intro : measure_theory. 
Hint Resolve Union_introl Union_intror : measure_theory. 
Hint Resolve Disjoint_intro : measure_theory. 

(** *)
(** ## Custom notations*)
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


(** ## A powertool*)
(* TODO: in some cases, eauto has left some existentials.
   this may be undesired, but eauto can be very powerful...
   one option is to let waterproof check whether 
   existentials are created and block this behavior. *)

Ltac wp_power :=
  timeout 60 (first [ solve [auto with *]
        | solve [eauto with *]
        | solve [firstorder (auto with *)]
        | solve [firstorder (eauto with *)]]).
(** *)
(** ## Introducing variables

The following is a strict version of `intro`, that checks the type of the variable to introduce.*)
Ltac intro_strict s t :=
  match goal with
    | [ |- forall _ : t, _ ] => intro s
  end.

(** *)
(** Take an arbitrary element of a certain type.*)
Tactic Notation "Take" ident(s) ":" constr(t):=
  intro_strict s t.


(** *)
(** *)
(** *)
(** Taking two elements of the same type. (To be generalised?)*)
Ltac intros_strict x y t :=
  match goal with
    | [ |- forall _ _ : t, _] => intros x y
  end.

Tactic Notation "Take" ident(x) ident(y) ":" constr(t):=
  intros_strict x y t. 
(** 
Variation of intro tactic that allows one to check that what you assume is really what you need to assume.*)
Ltac assume_strict s t :=
  match goal with
    | [ |- ?u -> _ ] => (change u with t; intro s)
  end.

(** *)
(** Assuming hypotheses.*)
Tactic Notation "Assume" ident(s) :=
  intro s.

Tactic Notation "Assume" ident(s) ":" constr(t) :=
  assume_strict s t.
(** ## Checking the context

The following tactics let the user record in the proof script various aspects of the current context.

The tactic call `goal_check t` checks if the current goal can equivalently be written as `t`, otherwise it fails.*)
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
(** *)
(** ## Choosing variables that exist*)
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
(** *)
(** ## Forward reasoning*)
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


(** *)
(** ## Forward reasoning by automation*)
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
  assert (u : t) by timeout 60 (first [ solve [auto using s with *]
                          | solve [eauto using s with *]
                          | solve [firstorder using s]
                          | solve [firstorder (eauto with *) using s]
                          | idtac "Waterproof could not find a proof. If you believe the statement should hold, try making a smaller step"]).

Ltac new_hyp_verified_pose_proof_no_name s t:=
  assert t by timeout 60 (first [ solve [auto using s with *]
                          | solve [eauto using s with *]
                          | solve [firstorder using s]
                          | solve [firstorder (eauto with *) using s]
                          | idtac "Waterproof could not find a proof. If you believe the statement should hold, try making a smaller step"]).

Tactic Notation "By" constr(s)
  "it" "holds" "that" constr(t) "("ident(u)")"
  := new_hyp_verified_pose_proof s t u.

Tactic Notation "By" constr(s)
  "it" "holds" "that" constr(t)
  := new_hyp_verified_pose_proof_no_name s t.

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
(** *)
(** Now a somewhat experimental and non-standard notation to resolve a goal using another assumption/lemma. The usual `By ... it holds that ...` does not do this, even without adding a name.*)
Tactic Notation "By" constr(u) "it" "holds" "that" constr(t) "which" "concludes" ident(the) "proof":= 
  By u it holds that t (the); 
  apply the. 
(** TODO: preferably deprecate this notation.*)
Tactic Notation "This" "follows" "immediately" :=
  wp_power.

Tactic Notation "follows" "immediately" := 
  wp_power.
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




(** *)
(** ## Applying one of the assumptions*)
Tactic Notation "This" "follows" "by" "assumption" := 
  assumption.
(** *)
(** ## Claims*)
Tactic Notation "We" "claim" "that" 
  constr(t) "(" ident(u) ")" :=
  assert (u : t).
(** ## Rewriting

TODO: add rewrite with at
TODO: add support for rewriting in and at multiple places at once*)
(** *)
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
(** *)
Tactic Notation "replacing" constr(s) "with" constr(t) :=
  replace s with t by wp_power.
(** ## Applying lemmas and theorems*)
Tactic Notation "Apply" uconstr(t) :=
  apply t.
(** *)
(** Note: when using `constr(t)` instead of `uconstr(t)`, the use of wildcareds is no longer possible.

TODO: add option to do an 'apply with'.*)
(** ## Expanding definitions

TODO: add more options for these tactics.*)
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

(** *)
(** ## Strings of (in)equalities

The following tactics should help in situations where in a pen-and-paper proof we would write a string equalities and inequalites.

**Note:** As of now, forward reasoning by "it holds that" seems to be a better option.

The tactic `trans_ineq eq_or_ineq` reduces the inequality in the goal to a new one by using `eq_or_ineq`.*)
Ltac trans_ineq eq_or_ineq := 
  match goal with 
  | [|-?x <= ?z] => 
    match (type of eq_or_ineq) with 
    | (x <= ?y) => apply (Rle_trans x y z eq_or_ineq)
    | _ => idtac "not a less-than-or-equal-to inequality"
    end
  | _ => idtac "Goal is not a less-than-or-equal-to inequality."
  end.
(** *)
(** ## Defining new variables*)
Tactic Notation "Define" ident(u) ":=" constr(t) :=
  set (u := t).
(** *)
(** ## Reflexivity*)
Tactic Notation "This" "follows" "by" "reflexivity" :=
  reflexivity.
(** ## Simplification

TODO: the following tactic notation may need to be improved.*)
Tactic Notation "Simplify" "what" "we" "need" "to" "show" :=
  simpl.
(** ## Proving by induction

Very basic notation, room for improvement. Also not the nicest formulation, but `Proof` is already used. *)
Tactic Notation "We" "prove" "by" "induction" "on" ident(x) := 
  induction x. 
(** ## A tool for set equalities and inclusions*)
Ltac destruct_intersec :=
  match goal with 
    | [H : In _ (Intersection _ _ _) _ |- _] => destruct H
  end.

Ltac trivial_set_inclusion := 
  try intro x;
  try intro H;
  try destruct_intersec;
  try contradiction;
  try wp_power.

Ltac trivial_set_equality := 
  try intros A;
  try intros B;
  try apply Extensionality_Ensembles;
  try unfold Same_set;
  try unfold Included;
  split;
  trivial_set_inclusion;
  trivial_set_inclusion.


Tactic Notation "This" "equality" "is" "trivial" := 
   trivial_set_equality.
(** 

## Hints*)
Hint Resolve Rmult_gt_0_compat : real.
Hint Resolve Rmult_lt_0_compat : real.
Hint Resolve R_dist_eq : real.
(** *)

(** * Syntax extensions for Computer programs for analysis

      This document contains some very preliminary experiments with 
      notations, ltac definitions and tactic notations to make it possible 
      to stay closer to mathematical language when writing proofs in Coq. *)

(** This file is supposed to be put in a folder 
    wplib/Tactics/ and intended to be compiled, 
    with 
    sercomp --mode=vo 
           -R "wplib","wplib"
           "wplib/Tactics/TacticsContra.v"*)

Require Import Rbase.
Require Import Rfunctions.
Require Import SeqSeries.
Require Import Rtrigo.
Require Import Ranalysis.
Require Import Integration.
Require Import micromega.Lra.
Require Import Omega.
Require Import Max.
Require Import Classical.
(* Require Import Unicode.Utf8. *)

(** * Classical tactics *)
    
(** TODO: problem with current implementation is that 
    the assumption is not explicitly named. *)
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
(** # Notations for Waterproof*)
Require Import Reals.

(** ## Real numbers*)
Notation "｜ x ｜" := (Rabs x) (at level 20).
(** ## Suprema and infima*)
Notation is_sup := is_lub.
Notation is_bdd_above := bound.
(** ## Sequences*)
Notation "an 'converges' 'to' a" := 
  (Un_cv an a) (at level 50). 
(** ## Sums and series*)
Notation "'Σ' Cn 'equals' x" := 
  (infinite_sum Cn x) (at level 50).
  
Notation "'Σ' 'of' Cn 'up' 'to' n" := 
  (sum_f_R0 Cn n) (at level 50). 
(* Sum and series also defined in series.wpn. What to adapt? *)
(** ## Sets*)
Definition is_in {D : Set} := fun (A : (D → Prop)) ↦ (fun (x : D) ↦ A x).
Notation "x ∈ A" := (@is_in _ A x) (at level 50) : analysis_scope.

(** # Set notations
For Coq's Ensembles library*)
Require Import Sets.Ensembles. 

Definition subset (U : Type) := 
  (Ensemble U). 

Definition set_of_subsets (U : Type) := 
  (Ensemble (subset U)).

Variable U : Type.

Notation "∅" := 
  (Empty_set U). 
  
Notation "'Ω'" := 
  (Full_set U) (at level 0). 

Notation "A ∩ B" := 
  (Intersection _ A B) (at level 45). 

Notation "A ∪ B" := 
  (Union _ A B) (at level 45). 

Notation "A \ B" := 
  (Setminus _ A B) (at level 45). 

Notation "x ∈ A" := 
  (In _ A x) (at level 50) : ensemble_scope. 

Notation "x ∉ A" :=  
  (~ In _ A x) (at level 50). 

Notation "A ⊂ B" := 
  (Included _ A B) (at level 45). 
  
Notation "A 'and' B 'are' 'disjoint'" := 
  (Disjoint _ A B) (at level 50).   
  
Notation "C 'is' 'an' 'increasing' 'sequence' 'of' 'sets'" := 
  (forall n : ℕ, (C n) ⊂ C (S n)) (at level 50).

Notation "｛ x : T | P ｝" := 
  (fun (x : T) ↦ P) (x at level 99).
(*these brackets are not the same as {}, and are not yet included in shortcuts! *)

Tactic Notation "We" "prove" "equality" "by" "proving" "two" "inclusions" :=
   apply Extensionality_Ensembles; 
   unfold Same_set; 
   unfold Included;
   split.
  
(*Open Scope ensemble_scope.*)


(** # Measure theory definitions & notations*)
Require Import Sets.Ensembles.
Require Import Sets.Classical_sets.
Require Import Sets.Powerset.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import Reals.

Open Scope ensemble_scope.


(** ## Collections of sets
### Definitions 
Concerning π-systems, λ-systems, σ-algebras and their properties: *)
(*Variable U : Type. *)

Definition is_π_system (Π : set_of_subsets U) 
  : Prop := 
    ∀ A : subset U, A ∈ Π ⇒ 
      ∀ B : subset U, B ∈ Π ⇒ 
         (A ∩ B) ∈ Π. 
         
Definition countable_union (A : (ℕ → subset U) ) 
  : subset U := 
    ｛ x:U | ∃n : ℕ, x ∈ (A n)｝. 

Definition full_set_in_set (Λ : set_of_subsets U) 
  : Prop :=
    Ω ∈ Λ. 

Definition complement_in_set (Λ : set_of_subsets U) 
  : Prop := 
    ∀ A  : subset U, A ∈ Λ 
      ⇒ (Ω \ A) ∈ Λ. 

Definition closed_under_disjoint_countable_union (Λ : set_of_subsets U) 
  : Prop :=
    ∀ C : (ℕ → (subset U)), 
      (∀ m n : ℕ, m ≠ n ⇒ Disjoint _ (C m) (C n)) 
        ⇒ (∀ n : ℕ, (C n) ∈ Λ) ⇒  (countable_union C) ∈ Λ.

Definition closed_under_countable_union (Λ : set_of_subsets U) 
  : Prop :=  
    ∀ C : (ℕ → (subset U)), (∀ n : ℕ, (C n) ∈ Λ) 
      ⇒ (countable_union C) ∈ Λ.

Definition is_λ_system (Λ : set_of_subsets U) 
  : Prop :=
    full_set_in_set Λ ∧ 
    complement_in_set Λ ∧
    closed_under_disjoint_countable_union Λ. 

Definition λ_system_generated_by (A : set_of_subsets U) 
  : (set_of_subsets U) := 
    ｛B : subset U | (∀ Λ : set_of_subsets U, is_λ_system Λ 
       ⇒ (A ⊂ Λ ⇒ B ∈ Λ))｝. 

Definition is_σ_algebra (F : set_of_subsets U) 
  : Prop := 
    full_set_in_set F ∧ 
    complement_in_set F ∧
    closed_under_countable_union F.

Definition σ_algebra_generated_by (A : set_of_subsets U) 
  : (set_of_subsets U) := 
    ｛B : subset U | ∀ F : set_of_subsets U, is_σ_algebra F ⇒ (A ⊂ F ⇒ B ∈ F)｝. 

Definition restriction (F : set_of_subsets U) (A : (subset U)) 
  : (set_of_subsets U) := 
    ｛C : subset U | ∃B : subset U, B ∈ F ⇒ C = A ∩ B｝. 
(** ### Notations 
To make the definitions above more useable/readable:*)
Notation "A 'is' 'a' 'π-system'" := 
  (is_π_system A) (at level 50). 
  
Notation "A 'is' 'a' 'λ-system'" := 
  (is_λ_system A) (at level 50).

Notation "A 'is' 'a' 'σ-algebra'" := 
  (is_σ_algebra A) (at level 50).
(*TODO: general tactic for the form above? *)

Notation "λ( A )" := 
 (λ_system_generated_by A) (at level 50).
 
Notation "σ( A )" := 
 (σ_algebra_generated_by A) (at level 50).
(** ### Record types*)
(** TO DO: The following four procedures are completely analogous. More efficient way?

π-systems:*)
Record π_system := make_π_system
  { underlying_set_of_subsets_π : set_of_subsets U;
    proof_is_π_system : is_π_system underlying_set_of_subsets_π}.
    
Coercion underlying_set_of_subsets_π : 
  π_system >-> set_of_subsets.

Hint Resolve proof_is_π_system : measure_theory.
Hint Resolve underlying_set_of_subsets_π : measure_theory.

Variable P : π_system.

Definition Π : set_of_subsets U := P.


Lemma Π_is_π_system : is_π_system Π.

Proof. 
It holds that (is_π_system (underlying_set_of_subsets_π P)) (xx). 
It holds that (is_π_system Π).
Qed.
Hint Resolve Π_is_π_system : measure_theory.
(** λ-systems:*)

Record λ_system := make_λ_system
  { underlying_set_of_subsets_λ : set_of_subsets U;
    proof_is_λ_system : is_λ_system underlying_set_of_subsets_λ}.
    
Variable L : λ_system.

Coercion underlying_set_of_subsets_λ : 
  λ_system >-> set_of_subsets.

Definition Λ : set_of_subsets U := L.

Hint Resolve proof_is_λ_system : measure_theory.
Hint Resolve underlying_set_of_subsets_λ : measure_theory.


Lemma Λ_is_λ_system : is_λ_system L.

Proof. 
It holds that (is_λ_system (underlying_set_of_subsets_λ L)) (xx). 
It holds that (is_λ_system Λ).
Qed.
Hint Resolve Λ_is_λ_system : measure_theory.

(** σ-algebras:*)
Record σ_algebra := make_σ_algebra
  { underlying_set_of_subsets_σ : set_of_subsets U;
    proof_is_σ_algebra : is_σ_algebra underlying_set_of_subsets_σ}.


Variable G : σ_algebra.

Coercion underlying_set_of_subsets_σ : 
  σ_algebra >-> set_of_subsets.

Definition F : set_of_subsets U := G.
Hint Resolve proof_is_σ_algebra : measure_theory.
Hint Resolve underlying_set_of_subsets_σ : measure_theory.


Lemma F_is_σ_algebra : is_σ_algebra F.

Proof. 
It holds that (is_σ_algebra (underlying_set_of_subsets_σ G)) (G_sets_σ). 
It holds that (is_σ_algebra F).
Qed.
(** A collection that is both a π-system and a λ-system (mostly for proof of π_and_λ_is_σ): *)
Record π_and_λ_system := make_π_and_λ_system
  { underlying_set_of_subsets_π_and_λ : set_of_subsets U;
    proof_is_π_and_λ_system : (is_λ_system underlying_set_of_subsets_π_and_λ 
      /\ is_π_system underlying_set_of_subsets_π_and_λ)}.
      
Variable J : π_and_λ_system.

Coercion underlying_set_of_subsets_π_and_λ : 
  π_and_λ_system >-> set_of_subsets.

Definition K : set_of_subsets U := J. 

Hint Resolve proof_is_π_and_λ_system : measure_theory.
Hint Resolve underlying_set_of_subsets_π_and_λ : measure_theory.


Lemma K_is_π_system : (is_π_system K).

Proof. 
It holds that ((is_λ_system (underlying_set_of_subsets_π_and_λ J))
            /\ (is_π_system (underlying_set_of_subsets_π_and_λ J))) (xx). 
It holds that (is_π_system K).
Qed.
Hint Resolve K_is_π_system : measure_theory.


Lemma K_is_λ_system : (is_λ_system K).

Proof. 
It holds that ((is_λ_system (underlying_set_of_subsets_π_and_λ J))
            /\ (is_π_system (underlying_set_of_subsets_π_and_λ J))) (xx). 
It holds that (is_λ_system K).
Qed.
Hint Resolve K_is_λ_system : measure_theory.
(** ## Measures*)
(** ### Definitions 
Of σ-additivity, measure and probability measure:*)
Definition σ_additive_on F (μ : (subset U ⇨ ℝ)) : Prop := 
  ∀ C : (ℕ → (subset U)), (∀ n : ℕ, C n ∈ F) 
    ⇒ (∀ m n : ℕ, m ≠ n ⇒ Disjoint _ (C m) (C n)) 
      ⇒ infinite_sum (fun (n:ℕ) ↦ (μ (C n))) (μ (countable_union C)).
      
Definition is_measure_on F (μ : (subset U → ℝ)) : Prop := 
  μ ∅ = 0 ∧ σ_additive_on F μ.
  
Definition is_probability_measure_on F (μ : (subset U → ℝ)) 
  : Prop := 
    is_measure_on F μ ∧ μ Ω = 1.
(** ### Notations*)
Notation "μ 'is' 'σ-additive' 'on' F" := 
  (σ_additive_on F μ) (at level 50). 
  
Notation "μ 'is' 'a' 'measure' 'on' F" := 
  (is_measure_on F μ) (at level 50). 
(** ### Measures as record types*)
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
(** # Hints*)
Hint Resolve Full_intro : measure_theory.  
Hint Resolve Intersection_intro : measure_theory. 
Hint Resolve Union_introl Union_intror : measure_theory. 
Hint Resolve Disjoint_intro : measure_theory. 
Hint Resolve F_is_σ_algebra : measure_theory.


(** # Sets & sequences
In this document, we state and prove lemmas that have to do with sets, collections of sets and sequences of sets. : 


## Basic lemmas about sets
We start of with some simple statements on relatively simple sets:*)
Require Import Sets.Ensembles.
Require Import Sets.Classical_sets.
Require Import Sets.Powerset.
Require Import Logic. 
Require Import ClassicalFacts. 
Require Import Omega. 
Require Import Coq.Arith.Wf_nat. 

Open Scope nat.
Open Scope ensemble_scope.
(*We do not want this, but otherwise notations 
  such as Ω and ∅ do not work. How to fix? *)

Section basic_set_lemmas.
Variable A B : subset U.


Lemma complement_full_is_empty : 
  ∅ = (Ω \ Ω). 

Proof. 
We prove equality by proving two inclusions. 
Take x : U. 
Assume x_in_empty.
Contradiction. 

Take x : U; Assume x_in_complement_full.
Because x_in_complement_full 
  both x_in_full and not_x_in_full. 
Contradiction. 
Qed.


Lemma complement_empty_is_full : 
  Ω = (Ω \ ∅). 

Proof. 
We prove equality by proving two inclusions. 
Take x : U; Assume x_in_full. 
It holds that (x ∈ (Ω \ ∅)).

Take x : U; Assume x_in_complement_empty.
It holds that (x ∈ Ω). 
Qed. 


Lemma setminus_empty : 
  A \ ∅ = A. 

Proof. 
We prove equality by proving two inclusions.
Take x : U; Assume x_in_A_wo_empty. 
It holds that (x ∈ A). 

Take x : U; Assume x_in_A. 
It holds that (x ∈ (A \ ∅)). 
Qed. 


Lemma intersection_full : 
  (Ω ∩ A) = A. 

Proof. 
We prove equality by proving two inclusions. 
Take x : U; Assume x_in_intersection. 
destruct x_in_intersection. 
It holds that (x ∈ A). 

Take x : U; Assume x_in_A. 
It holds that (x ∈ Ω) (x_in_omega). 
It follows that (x ∈ (Ω ∩ A)). 
Qed. 


Lemma intersection_empty : 
  (A ∩ ∅) = ∅. 

Proof. 
We prove equality by proving two inclusions. 
Take x : U; Assume x_in_intersection. 
destruct x_in_intersection. 
Contradiction. 

Take x : U; Assume x_in_empty. 
Contradiction. 
Qed. 


Lemma empty_disjoint : 
  Disjoint _ A ∅. 

Proof. 
It suffices to show that (∀ x:U, x ∉ (A ∩ ∅)).
Take x : U. 
By intersection_empty it holds that 
  ((A ∩ ∅) = ∅) (int_empty). 
Write goal using ((A ∩ ∅) = ∅) as (x ∉ ∅). 
It holds that (x ∉ ∅). 
Qed. 


Lemma intersection_symmetric : 
  A ∩ B = B ∩ A. 

Proof. 
We prove equality by proving two inclusions. 
Take x : U; Assume x_in_AB. 
destruct x_in_AB. 
It holds that (x ∈ (B ∩ A)). 

Take x : U; Assume x_in_BA. 
destruct x_in_BA. 
It holds that (x ∈ (A ∩ B)). 
Qed. 


Lemma disjoint_symmetric : 
  (Disjoint _ A B) ⇒ (Disjoint _ B A). 

Proof. 
Assume A_B_disjoint. 
destruct A_B_disjoint.
By intersection_symmetric it holds that 
  ((A ∩ B) = (B ∩ A)) (AB_is_BA).
Write H using ((A ∩ B) = (B ∩ A)) 
  as (∀ x : U, x ∉ (B ∩ A)). 
It follows that (Disjoint U B A). 
Qed. 


Lemma union_to_or : 
  ∀ x : U, 
    x ∈ (A ∪ B) ⇒ (x ∈ A ∨ x ∈ B).

Proof. 
Take x : U; Assume x_in_union. 
destruct x_in_union. 
(* x ∈ A: *)
It follows that (x ∈ A ∨ x ∈ B).
(* x ∈ B: *) 
It follows that (x ∈ A ∨ x ∈ B). 
Qed. 


Lemma not_in_comp : 
  ∀ x : U, 
    x ∉ (Ω \ A) ⇒ x ∈ A.

Proof. 
Take x : U. 
Assume x_not_in_complement. 
We argue by contradiction. 
It holds that (x ∈ (Ω \ A)) (x_in_complement).
Contradiction. 
Qed. 
(** The following two lemmas should follow immediately, but need to be stated explicitly in order for proofs to work (improvement for library?)*)
Lemma neq_equiv : ∀ x y : ℕ,
  (x ≠ y) ⇒ ((x < y) ∨ (x > y)).

Proof. 
intros x y. omega.
Qed. 


Lemma leq_equiv : ∀ x y : ℕ,
  (x <= y) ⇒ (x < y ∨ x = y).

Proof. 
intros x y. omega. 
Qed. 


Lemma geq_equiv : ∀ x y : ℕ,
  (x ≥ y) ⇒ (x = y ∨ (x > y)).

Proof. 
intros x y. omega. 
Qed. 

End basic_set_lemmas.
(** ## Sequences of sets
Next, we turn to sequences of sets and some of their properties. Previous lemmas were very basic, such that they are often used without proof; hence they are added as hints at the bottom of this document. For the next lemmas, we do not do this, as it might be relevant to let students prove (parts of) them themselves. 

There are several definitions that we consider in particular. The first takes in two sets $A$ and $B$, turns it into the sequence $(A,B,∅,∅,...)$. Second, we define the finite union of a number of sets from a sequence. 
This is used in our third definition, which takes in a sequence of sets and turns it into a disjoint sequence of sets with the same union. 
Last, we show some properties of increasing sequences of sets. 

All of these have properties that are often used without proof, but that are more technical and involved than you might expect. *)
(** ### The two-set sequence
First, we show some properties of the sequence $(A,B,∅,∅,...)$ for two sets $A$ and $B$, first in general and then under the condition that they are disjoint. This is an auxiliary sequence that is for example used in the proof that a σ-algebra is not only closed under countable union, but also under finite union; the idea is that the countable union of this sequence is simply $A ∪ B$. The same goes for a λ-system if the two sets are disjoint. 
Later, we will also use the sequence to show that measures are finitely additive. *)
Fixpoint aux_seq (A B : subset U) (n : ℕ) {struct n}
  : (subset U) :=
    match n with 
      0 => A 
    | 1 => B
    | n => ∅ 
    end. 


Lemma CU_aux_is_union : 
  ∀ A B : subset U, countable_union (aux_seq A B) = A ∪ B. 

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
It follows that (x ∈ countable_union (aux_seq A B)).

It holds that (x ∈ aux_seq A B 1) (x_in_aux0). 
We need to show that 
  (x ∈ ｛x0 : U | ∃ n : ℕ, x0 ∈ aux_seq A B n｝). 
It holds that (∃ n : ℕ, x ∈ aux_seq A B n) (exists_n_B). 
It follows that (x ∈ countable_union (aux_seq A B)).
Qed.
(** Now follows the proof that the sequence is indeed disjoint. Although it is correct, it is unfortunately not very elegant. *)
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
  (Disjoint U (aux_seq A B 0) ∅) (xx). 
Apply xx. 
(*Case m =1, n=0: *)
We prove by induction on m. 
We prove by induction on n. 
Write goal using (aux_seq A B 1 = B) 
  as (Disjoint U B (aux_seq A B 0)).
Write goal using (aux_seq A B 0 = A) 
  as (Disjoint U B A).
By disjoint_symmetric it holds that 
  ((Disjoint _ B A)) (xx).
Apply xx. 
(*Case m=n=1: *)
We prove by induction on n. 
Contradiction. 
(*Case m=1, n>1: *)
Write goal using (aux_seq A B (S (S n)) = ∅) 
  as (Disjoint U (aux_seq A B 1) ∅). 
By empty_disjoint it holds that 
  (Disjoint U (aux_seq A B 1) ∅) (xx). 
Apply xx.
(*Case m>n: *)
Write goal using (aux_seq A B (S (S m)) = ∅) 
  as (Disjoint U ∅ (aux_seq A B n)). 
By disjoint_symmetric it holds that 
  (Disjoint U (aux_seq A B n) ∅ 
    ⇒ Disjoint U ∅ (aux_seq A B n)) (disj_symm). 
It suffices to show that (Disjoint U (aux_seq A B n) ∅). 
Apply empty_disjoint. 
Qed. 
(** One last property we sometimes want to use is that for $n>1$, all elements of our sequence are the empty set (note that Waterproof starts counting at 0):*)
Lemma aux_ge2_empty : 
  ∀ A B : subset U, ∀ n : ℕ, 
    (n > 1) ⇒ aux_seq A B n = ∅. 

Proof.
Take A B : (subset U). 

Take n : ℕ; Assume n_g_1. 
Expand the definition of aux_seq.
(*More case distinction than induction, but 
  this works far better for 'Fixpoint' definitions*)
We prove by induction on n. 
It holds that (¬(0 > 1)) (not_0_g_1). 
Contradiction.
We prove by induction on n. 
It holds that (¬(1 > 1)) (not_1_g_1). 
Contradiction. 
It holds that (∅ = ∅). 
Qed. 
(** ### On finite unions
With the previous lemmas and definitions, we can prove results on countable unions and unions of two sets. There is one category inbetween, which is that of the finite union of a sequence of sets. This is to the countable union what a partial sum is to a series; you can already imagine that it will be helpful at least, possibly inavoidable in several proofs. We now state two definitions, as both have their benefits and drawbacks in different scenarios. (TODO: unify these?)*)
Definition finite_union (C : (ℕ ⇨ subset U)) (n : ℕ) 
  : subset U := 
    ｛x : U | (∃ i : ℕ,  (i <= n ∧ x ∈ (C i)))｝.

Definition finite_union_up_to (C : (ℕ ⇨ subset U)) (n : ℕ) 
  : (subset U) := 
    ｛x : U | (∃ i : ℕ,  (i < n ∧ x ∈ (C i)))｝.
(** We will also see it as an aid when defining our disjoint sequence of sets; to show that this sequence is in a σ-algebra, we need some of the following results. *)
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
It holds that (n0 <= n) (n0_le_n).  
By leq_equiv it holds that 
  (n0 < n ∨ n0 = n) (n0_l_e_n).
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
(** 
### The disjoint sequence
This definition is, for example, used in the proof that a collection of sets that is both a π-system and a λ-system is also a σ-algebra. (More explanation?)*)
Definition disjoint_seq (C : (ℕ ⇨ subset U)) 
  : (ℕ ⇨ subset U) := 
    fun (n : ℕ) ↦ (C n \ (finite_union_up_to C n)). 
(** That this sequence is disjoint and that the countable union of this sequence is equal to that of the original sequence is proven in `disj_seq_disjoint` and `CU_sets_disjointsets_equal` respectively. First, we prove a smaller result that we will need in these proofs: *)
Lemma FU_up_to_0_empty : 
  ∀ C : (ℕ ⇨ subset U), finite_union_up_to C 0 = ∅. 

Proof. 
Take C : (ℕ ⇨ subset U). 
We prove equality by proving two inclusions. 
Take x : U; Assume x_in_FU_0. 
Write x_in_FU_0 as 
  (x ∈ ｛x : U | ∃ i : ℕ , i < 0 ∧ x ∈ C i｝). 
It holds that (¬(∃i : ℕ, i<0 ∧ x ∈ C i)) (no_N_l_0). 
Contradiction.

Take x : U; Assume x_in_empty. 
Contradiction. 
Qed.


Lemma disj_seq_disjoint : 
  ∀ C : ((ℕ ⇨ subset U)), 
    (∀ m n : ℕ, m ≠ n ⇒ Disjoint _ 
      (disjoint_seq C m) (disjoint_seq C n)). 

Proof. 
Take C : ((ℕ ⇨ subset U)). 
Take m n : ℕ. 
Assume m_neq_n.
By neq_equiv it holds that 
  (m ≠ n ⇒ (m < n) ∨ (m > n)) (m_l_g_n).
It holds that ((m < n) ∨ (m > n)) (m_lg_n). 
We argue by contradiction. 
It holds that (∃ x : U, 
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
  (¬(∃i : ℕ,  (i < m ∧ x ∈ (C i)))
    ∧ ¬(∃i : ℕ,  (i < n ∧ x ∈ (C i)))) (no_i).
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
  ∀ C : ((ℕ ⇨ subset U)), 
    countable_union (disjoint_seq C) = countable_union C.

Proof. 
Take C : ((ℕ ⇨ subset U)).
Define D := (disjoint_seq C). 
We prove equality by proving two inclusions. 

(* CU disjoint sets in CU C: *)
Take x : U; Assume x_in_CU_D. 
It holds that (x ∈ countable_union C). 

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

It holds that (x ∈ countable_union D). 
Qed. 
(** A similar result to `FU_up_to_0_empty` is the following: *)
Lemma FU_up_to_1_is_0 : 
  ∀ C : (ℕ → (subset U)), 
      finite_union_up_to C 1 = C 0.

Proof. 
Take C : (ℕ ⇨ subset U).
We prove equality by proving two inclusions. 
Take x : U; Assume x_in_FU.
destruct x_in_FU. 
It holds that (x0 = 0) (x0_is_0).
Write goal using (0 = x0) 
  as (x ∈ C x0). 
It holds that (x ∈ C x0).

Take x : U; Assume x_in_C0. 
It holds that (x ∈ finite_union_up_to C 1). 
Qed. 
(** ### Increasing sequences of sets

It is easy to picture convergence of a sequence of numbers. But how does this work for sets? We would like to use some sense of convergence for sets for example to proving that measures are continuous. A way to do this is to use an increasing sequence of sets. We will now give the definition, and prove some properties. *)
Definition is_increasing_seq_sets (C : (ℕ → (subset U)))
  : Prop := 
    ∀ n : ℕ, (C n) ⊂ C (S n).

Lemma increasing_seq_mn : 
     ∀ C : (ℕ → (subset U)), 
      is_increasing_seq_sets C 
        ⇒ (∀m n : ℕ, (m ≤ n) 
          ⇒ C m ⊂ C n).

Proof. 
Take C : (ℕ ⇨ subset U). 
Assume C_is_increasing.
Take m n : ℕ; Assume m_le_n. 
induction n.
It holds that (m = 0) (m0).
Write goal using (m = 0) 
  as (C 0 ⊂ C 0).
It holds that (C 0 ⊂ C 0).
By leq_equiv it holds that 
  (((m < (S n)) ∨ m = (S n))) (m_l_eq_Sn).
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

(** In proofs involving increasing sequences of sets, a common argument is that the finite union up to and including a certain set is equal to the set itself. The same still holds if we take the finite union over the sequence `disjoint_seq` instead of the original sequence, which is what we prove next: *)
Lemma FUn_aux_is_Cn : 
  ∀C : (ℕ → (subset U)), is_increasing_seq_sets C
    ⇒ ∀ n : ℕ, finite_union_up_to (disjoint_seq C) (S n) = C n.

Proof. 
Take C : (ℕ ⇨ subset U) . 
Assume C_is_incr_seq.
Define D := (disjoint_seq C). 
Take n : ℕ. 
We prove equality by proving two inclusions. 
Take x : U; Assume x_in_FU. 
Choose n0 such that x_in_Dn0 according to x_in_FU. 
By x_in_Dn0 it holds that 
  (x ∈ C n0) (x_in_Cn0).
By increasing_seq_mn it holds that 
  (C n0 ⊂ C n) (Cn0_subs_Cn). 
It follows that (x ∈ C n). 

Take x : U; Assume x_in_C.
Define aux_prop := (fun (n : ℕ) ↦ (x ∈ C n)).
By classic it holds that 
  (∀ n, aux_prop n ∨ ¬aux_prop n) (aux_prop_decidable). 
By dec_inh_nat_subset_has_unique_least_element it holds that
  (has_unique_least_element le aux_prop) (exists_least_n). 
Choose n1 such that x_in_C_minimal_n according to exists_least_n. 
It holds that ( aux_prop n1 
  ∧ ( ∀ n2 : ℕ, aux_prop n2 
    ⇒ (n1 ≤ n2))) (aux_n1_and_n1_le_n2).
Because aux_n1_and_n1_le_n2 both aux_n1 and n1_le_n2. 
It holds that (x ∈ D n1) (x_in_Dn1). 
We claim that (n1 < S n) (n1_l_n).
By x_in_C it holds that (aux_prop n) (aux_n_min_1). 
By n1_le_n2 it holds that 
  (n1 ≤ n) (n1_leq_n_min_1). 
It holds that 
  (n1 < S n). 
  
It holds that (∃i : ℕ,  
  ((i < (S n)) ∧ x ∈ (D i))) (exists_i). 
It follows that (x ∈ finite_union_up_to D (S n)).
Qed.
(** ## Hints*)
Hint Resolve classic.
(*Hint Resolve NNPP*)

(* Basic set theory results: *)
Hint Resolve complement_full_is_empty : sets.
Hint Resolve complement_empty_is_full : sets.
Hint Resolve setminus_empty : sets.
Hint Resolve intersection_full : sets.
Hint Resolve intersection_empty : sets.
Hint Resolve empty_disjoint : sets.
Hint Resolve intersection_symmetric : sets.
Hint Resolve disjoint_symmetric : sets.
Hint Resolve union_to_or : sets.
Hint Resolve not_in_comp : sets.


Hint Resolve neq_equiv leq_equiv geq_equiv : real.

(* Concerning sequences of sets: *)
Hint Resolve disj_seq_disjoint : sets. 
Hint Resolve disjoint_aux : sets. 
Hint Resolve CU_aux_is_union : sets. 
Hint Resolve FU_up_to_0_empty : sets. 
Hint Resolve FU_up_to_1_is_0 : sets. 
Hint Resolve FU_S_as_union : sets.

(*Possibly add disjoint_aux, increasing_seq_mn? *)


(** # Continuity of measure
An extremely important result in measure theory is the continuity of measures. There are multiple formulations and variants to state it. The one that we aim to prove in this notebook is continuity from below, that is, continuity of measure for an increasing sequence of sets. This result is used over and over in measure theory, and for example forms the basis of the monotone convergence theorem. 

The proof can roughly be divided into four parts, of which only the last two involve measures; the first two are purely set-theoretical.  
First, we show that a σ-algebra is closed under taking finite unions. Next, we prove some more properties of the disjoint sequence also used in the proof of the π-λ theorem. Then we show that measures are finitely additive and finally, we use all prior results to prove our main result, the lemma `incr_cont_meas`. 

We begin with importing some libraries and introducing some variables and notations. *)
Require Import ClassicalFacts. 
Require Import Coq.Arith.Wf_nat. 
Require Import Logic. 
Require Import Omega. 
Require Import Reals.
Require Import Sets.Classical_sets.
Require Import Sets.Ensembles.
Require Import Sets.Powerset.

Open Scope nat.

(*We may not want this, but otherwise notations 
  such as Ω and ∅ do not work. How to fix? *)

Variable F : σ_algebra.
Variable μ : (@measure_on F).
Open Scope measure_theory_scope.
(** ## Finite unions in σ-algebras

At several points of the upcoming proofs, we use finite unions. The following lemmas are similar to ones in the π-λ theorem proof, but are now stated for a σ-algebra, $F$. We want to prove that the finite union of elements of $F$ is again an element of $F$. For this, we first need two lemmas:*)

Lemma empty_in_σ : 
  ∅ ∈ F. 

Proof.  
Write goal using (∅ = (Ω \ Ω)) as ((Ω \ Ω) ∈ F). 
By F_is_σ_algebra it holds that ((Ω \ Ω) ∈ F)
  which concludes the proof. 
Qed.  


Lemma unions_in_σ : 
  ∀ A B : subset U, A ∈ F ∧ B ∈ F
    ⇒ A ∪ B ∈ F.

Proof. 
Take A B : (subset U). 
Define D := (aux_seq A B).
Assume A_and_B_in_F. 

We claim that (∀ n : ℕ, D n ∈ F) (all_aux_in_F). 
Take n : ℕ. 
We prove by induction on n. 
It holds that (D 0 ∈ F). 
We prove by induction on n. 
It holds that (D 1 ∈ F). 
Write goal using (D (S (S n)) = ∅) 
  as (∅ ∈ F). 
By empty_in_σ it holds that 
  (∅ ∈ F) (empty_in_F).
Apply empty_in_F.  

By CU_aux_is_union it holds that 
  (A ∪ B = countable_union D) (union_to_CU). 
Write goal using (A ∪ B = countable_union (aux_seq A B))
  as (countable_union D ∈ F).
By F_is_σ_algebra it holds that (countable_union D ∈ F)
  which concludes the proof. 
Qed.
(** These two lemmas will help us prove that if $F$ is a σ-algebra, it is closed under taking countable unions: *)
Lemma FU_in_σ : 
  ∀ C : (ℕ → (subset U)), (∀ n : ℕ, (C n) ∈ F) 
      ⇒ ∀ n : ℕ, (finite_union_up_to C n) ∈ F.

Proof. 
Take C : (ℕ ⇨ subset U). 
Assume all_Cn_in_F.
Take n : ℕ. 
We prove by induction on n.
(* Base case: *)
Write goal using (finite_union_up_to C 0 = ∅) 
  as (∅ ∈ F). 
Apply empty_in_σ; Apply F_is_σ_algebra. 
(* Induction step: *)
Write goal using 
  (finite_union_up_to C (S n) 
    = (finite_union_up_to C n) ∪ (C n)) 
      as ((finite_union_up_to C n) ∪ (C n) ∈ F).
By all_Cn_in_F it holds that (C n ∈ F) (Cn_in_F). 
By unions_in_σ it holds that 
  ((finite_union_up_to C n ∪ C n) ∈ F) 
    which concludes the proof. 
Qed. 
(** ## The disjoint sequence
As mentioned before, the disjoint sequence `disjoint_seq` as defined in the `sets` library will play an important role in this proof. But of course we can only use it properly if, given a sequence of non-disjoint sets in $F$, all of the elements of the sequence it represents are in $F$ as well. This is what we prove in the next five lemmas. After that, we show what the union of the first $n$ elements of the disjoint sequence turns out to be. 

### σ-algebras and the disjoint sequence
We now prove the five lemmas. The first two show that $F$ is closed under taking intersections: the first one rewrites the intersection of two sets to a combination of a union and complements of these sets, the second uses properties of a σ-algebra to show that for $A$ and $B$ in $F$, the result is again in $F$. *)
Chapter disjoint_sequence.
Variable C : (ℕ → (subset U)).

Section disjoint_sets.
Variable A B : subset U.

Lemma intersection_to_complement : 
  A ∩ B = Ω \ ((Ω \ A) ∪ (Ω \ B)). 

Proof. 
We prove equality by proving two inclusions. 
Take x : U; Assume x_in_lhs. 
destruct x_in_lhs. 
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
  A ∈ F ∧ B ∈ F
    ⇒ A ∩ B ∈ F.

Proof. 
Assume A_and_B_in_F. 
By F_is_σ_algebra it holds that 
  (F is a σ-algebra) (F_is_σ). 
By intersection_to_complement it holds that 
  (A ∩ B = Ω \ ((Ω \ A) ∪ (Ω \ B))) (int_is_comp). 
Write goal using (A ∩ B = Ω \ ((Ω \ A) ∪ (Ω \ B)))
  as (Ω \ ((Ω \ A) ∪ (Ω \ B)) ∈ F). 
By unions_in_σ it holds that 
 ((Ω \ A) ∪ (Ω \ B) ∈ F) (compA_compB_in_F). 
It follows that (Ω \ ((Ω \ A) ∪ (Ω \ B)) ∈ F).
Qed.
(** These now serve to prove that $F$ is also closed under taking complements. We need one more lemma for this, which rewrites the complement of a set with respect to another set. *)

Lemma complement_as_intersection : 
  A \ B = (Ω \ B) ∩ A. 

Proof. 
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

End disjoint_sets.


Lemma complements_in_σ : 
  ∀ A B : subset U, A ∈ F ∧ B ∈ F
    ⇒ A \ B ∈ F. 

Proof. 
Take A B : (subset U). 
Assume A_and_B_in_F. 
By F_is_σ_algebra it holds that 
  (F is a σ-algebra) (F_is_σ). 
It holds that 
  (Ω \ B ∈ F) (comp_B_in_F). 
By intersections_in_σ it holds that 
  ((Ω \ B) ∩ A ∈ F) (set_in_F). 
By complement_as_intersection it holds that 
  (A \ B = (Ω \ B) ∩ A) (set_is_complement). 
Write goal using (A \ B = ((Ω \ B) ∩ A)) 
  as (((Ω \ B) ∩ A) ∈ F). 
It holds that ((Ω \ B) ∩ A ∈ F). 
Qed. 
(** Now, we can show what we set out to do this section, which is that al elements of the sequence constructed from the definition `disjoint_seq` are in $F$:*)
Lemma disj_seq_in_F : 
  is_increasing_seq_sets C
    ⇒ (∀ n : ℕ, C n ∈ F)
      ⇒ (∀n : ℕ, (disjoint_seq C) n ∈ F). 

Proof. 
Assume C_is_incr_seq.
Assume all_Cn_in_F.
Define D := (disjoint_seq C). 

Take n : ℕ. 
We need to show that (C n \ (finite_union_up_to C n) ∈ F).
We claim that ((finite_union_up_to C n) ∈ F) (FU_in_F). 
Apply FU_in_σ.
By F_is_σ_algebra it holds that 
  (F is a σ-algebra) (F_is_σ). 
Apply all_Cn_in_F. 
It holds that (C n ∈ F) (Cn_in_F).
By complements_in_σ it holds that 
  (C n \ finite_union_up_to C n ∈ F) 
    which concludes the proof.
Qed. 
(** ### Finite unions of the disjoint sequence
A useful consequence of the construction of a disjoint sequence using `disjoint_seq` is that, when given some sequence of sets $(C_n)$, the union of the first $n$ elements of this sequence is equal to the set $C_n$ itself. This will come in handy during our final proof, when rewriting the measure of some set $C_n$ to a sum of measures of disjoint sets. *)
Open Scope nat.
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
By increasing_seq_mn it holds that 
  (C n0 ⊂ C n) (Cn0_subs_Cn). 
It follows that (x ∈ C n). 

Take x : U; Assume x_in_C.
Define aux_prop := (fun (n : ℕ) ↦ (x ∈ C n)).
It holds that 
  (∀ n, aux_prop n ∨ ¬aux_prop n) (aux_prop_decidable). 
By dec_inh_nat_subset_has_unique_least_element it holds that
  (has_unique_least_element le aux_prop) (exists_least_n). 
Choose n1 such that x_in_C_minimal_n according to exists_least_n. 
It holds that ( aux_prop n1 
  ∧ ( ∀ n2 : ℕ, aux_prop n2 
    ⇒ (n1 ≤ n2))) (aux_n1_and_n1_le_n2).
Because aux_n1_and_n1_le_n2 both aux_n1 and n1_le_n2. 
It holds that (x ∈ D n1) (x_in_Dn1). 
We claim that (n1 < S n) (n1_l_n).
By x_in_C it holds that (aux_prop n) (aux_n_min_1). 
By n1_le_n2 it holds that 
  (n1 ≤ n) (n1_leq_n_min_1). 
It holds that 
  (n1 < S n). 
  
It holds that (∃i : ℕ,  
  ((i < (S n)) ∧ x ∈ (D i))) (exists_i). 
It follows that (x ∈ finite_union_up_to D (S n)).
Qed.

End disjoint_sequence.
(** ## Finite additivity of measure
Finally, we turn to measures. For our continuity proof at the end of this document, we need the property of finite additivity of measures. We now prove this in two steps: first, we show that for disjoint sets $A, B ∈ F$, we have that $μ(A∪B) = μ(A) + μ(B)$. Then, by induction, we show that this holds for an arbitrary number of mutually disjoint sets.

### Additivity of measure
We again make use of the auxiliary sequence (denoted by $C$ here) that was also used, among others, to show that σ-algebras are closed under taking the union of two sets. In the same way that we went from closedness under countable union to closedness under 'regular' union, we now go from σ-additivity to  additivity. 

For this, we first show that we may evaluate a measure on $F$ in $A$ and $B$ if both are in $F$ and if they are disjoint; this enables us to apply the σ-additivity property of the measure to show that $\sum_{n=0}^{∞} μ(C_n) = μ \left(∪_{n=0}^{∞} C_n \right)$:*)
Section additivity. 
Variable A B : subset U.
Open Scope nat.


Lemma aux_additive : 
  A ∈ F ⇒ B ∈ F
    ⇒ A and B are disjoint 
      ⇒ (Σ (fun (n:ℕ) ↦ (μ ((aux_seq A B) n))) 
        equals (μ (countable_union (aux_seq A B)))).

Proof. 
Assume A_in_F; Assume B_in_F.
Assume A_B_disjoint.
Define D := (aux_seq A B).
By μ_is_measure_on_F it holds that 
  (μ is σ-additive on F) (add_on_F).
Apply add_on_F.
Take n : ℕ. 
We prove by induction on n.
It holds that (D 0 ∈ F).
We prove by induction on n.
It holds that (D 1 ∈ F).

It holds that (D (S (S n)) = ∅) (DSS_empty). 
By empty_in_σ it holds that 
  (D (S (S n)) ∈ F) 
    which concludes the proof.
 
By disjoint_aux it holds that 
  ( ∀ m n : ℕ,
    m ≠ n ⇨ Disjoint U (D m) (D n)) 
      which concludes the proof.  
Qed.
(** Next, we prove the additivity property itself. It is a rather long proof, so we split it into three parts, and give explanation in between. 

The beginning is straightforward: we make all necessary assumptions, rewrite our goal and state two properties that we will use later. Then, we state a claim, proving which takes up most of the proof.*)
Open Scope R_scope. 

Lemma additivity_meas : 
  A ∈ F ⇒ B ∈ F
    ⇒ A and B are disjoint
       ⇒ μ (A ∪ B) = μ A + μ B. 

Proof. 
Assume A_in_F; Assume B_in_F.
Assume A_B_disjoint.
Define D := (aux_seq A B).
Define seq_μD := (fun (n:ℕ) ↦ (μ (D n))).
By CU_aux_is_union it holds that 
  (A ∪ B = countable_union D) (union_is_CU).
Write goal using (A ∪ B = countable_union D)
  as (μ (countable_union D) = μ A + μ B).
By aux_additive it holds that 
  (Σ seq_μD equals 
    (μ (countable_union D))) (sum_meas_is_meas_CU).

We claim that (Σ seq_μD equals
  (μ A + μ B)) (series_is_sumAB). 
We need to show that (
   ∀ ε : ℝ, ε > 0
    ⇒ ∃ N : ℕ ,
       ∀ n : ℕ, (n ≥ N)%nat 
        ⇒ ｜(Σ of seq_μD up to n) - (μ A + μ B)｜ < ε).
Take ε : R; Assume ε_g0. 
(** But proving this claim mostly comes down to the proof of a smaller claim.
For us it is obvious that (counting from 0, as WaterProof does) for $n ≥ 1$, it holds that $\sum_{i=0}^{n} μ(C_i) = μ \left(∪_{i=0}^{n} C_i \right)$, since for larger $n$, $C_n$ is empty so neither the sum on the left nor the union on the right change. In Waterproof this is far from trivial, and proving this is the hard work of the proof.*)
We claim that ( ∀ n : ℕ, (n ≥ 1)%nat 
  ⇒ ｜ (Σ of seq_μD up to n) -  
    (μ A + μ B) ｜ < ε) (holds_for_ge_1).
We prove by induction on n. 
(* n=0: *)
It holds that (¬(0 ≥ 1)%nat) (not_0_geq_1). 
Contradiction.
(* induction step *)
It holds that 
  (n = 0%nat ∨ (n > 0)%nat) (n_0_or_n_g0).
Because n_0_or_n_g0 either n_0 or n_g0. 
(* n=1: *)
It holds that (S n = 1%nat) (Sn_is_1).
Write goal using (S n = 1%nat)
  as ((1 ≥ 1)%nat 
  ⇒ ｜ (Σ of seq_μD up to 1) -
    (μ A + μ B) ｜ < ε).
Write goal using (Σ of seq_μD up to 1 = μ A + μ B)
  as (｜ (μ A + μ B) - (μ A + μ B) ｜ < ε). 
By R_dist_eq it holds that 
  (｜ (μ A + μ B) - (μ A + μ B) ｜ = 0) (dist_is_0).
It follows that (｜ (μ A + μ B) - (μ A + μ B) ｜ < ε).
(* n>1: *)
It holds that ((n ≥ 1)%nat) (n_geq_1).
By IHn it holds that 
  (｜ (Σ of seq_μD up to n) - (μ A + μ B) ｜ < ε) (dist_l_eps). 
We claim that (seq_μD (S n) = 0) (µSn_0).
By aux_ge2_empty it holds that 
  (D (S n) = ∅) (DSn_empty).
By μ_is_measure_on_F it holds that 
  (μ ∅ = 0) (µ_empty_0). 
We need to show that (μ (D (S n)) = 0).
Write goal using (D (S n) = ∅)
  as (μ ∅ = 0).
Apply µ_empty_0. 

Write goal using (Σ of seq_μD up to (S n)
  = Σ of seq_μD up to n + seq_μD (S n))
    as (｜ (Σ of seq_μD up to n + seq_μD (S n)) -
      (μ A + μ B) ｜ < ε). 
Write goal using (seq_μD (S n) = 0) 
  as (｜ (Σ of seq_μD up to n + 0) - (μ A + μ B) ｜ < ε).
Write goal using 
  (Σ of seq_μD up to n + 0 = Σ of seq_μD up to n)
    as (｜ (Σ of seq_μD up to n) - (μ A + μ B) ｜ < ε).
Apply dist_l_eps.
(** Only now do we come back to the claim made in the first block of this proof. Once this is resolved, we know that $\sum_{n=0}^{∞} μ (C_n) = μ \left(∪_{n=0}^{∞} C_n \right)$ (from earlier) and $\sum_{n=0}^{∞} μ (C_n) = μ(A) + μ(B)$, from which  our rewritten goal immediately follows:*)

It follows that (∃ N : ℕ ,
  ∀ n : ℕ, (n ≥ N)%nat 
    ⇒ ｜ (Σ of seq_μD up to n) -
      (μ A + μ B) ｜ < ε). 
By uniqueness_sum it holds that 
  (μ (countable_union D) = μ A + μ B) 
    which concludes the proof. 
Qed.

End additivity.
(** ### From  additivity to finite additivity

Having proven additivity for two sets, we now consider an arbitrary number of sets, and prove that the property still holds. We do this by induction, using the additivity result proven above. *)
Open Scope R_scope.
Section finite_additivity.
Variable C : (ℕ → (subset U)).

Lemma finite_additivity_meas : 
  (∀n : ℕ, C n ∈ F) 
    ⇒ (∀ m n : ℕ, m ≠ n ⇒ (C m) and (C n) are disjoint)  
      ⇒ ∀ N : ℕ,  μ (finite_union_up_to C (S N))
        = Σ of (fun (n : ℕ) ↦ (μ (C n))) up to N.

Proof. 
Assume all_Cn_in_F.  
Assume C_n_disjoint. 
Define seq_μC := (fun (n : ℕ) ↦ μ (C n)). 
Define FU_C := (finite_union_up_to C). 
Take N : ℕ.
We prove by induction on N. 
(* Base case: *)
It holds that 
  (finite_union_up_to C 1 = C 0%nat) (FU1_is_C0).
Write goal using (FU_C 1%nat = C 0%nat)
  as (μ (C 0%nat) = Σ of seq_μC up to 0%nat).
It holds that (μ (C 0%nat) = Σ of seq_μC up to 0). 
(*Induction step: *)
It holds that (Σ of seq_μC up to (S N) 
  = Σ of seq_μC up to N + seq_μC (S N)) (sum_to_sum).
Write goal using (Σ of seq_μC up to (S N) 
  = Σ of seq_μC up to N + seq_μC (S N)) 
    as (μ (FU_C (S (S N)))
      = Σ of seq_μC up to N + seq_μC (S N)). 

By FU_S_as_union it holds that 
  (FU_C (S (S N)) 
    = (FU_C (S N)) ∪ (C (S N))) (FU_to_union). 
We claim that ((FU_C (S N)) and 
  (C (S N)) are disjoint) (FUSn_CSn_disj). 
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
  ((C n0) and (C (S N)) are disjoint) (Cn0_CSN_disj). 
destruct Cn0_CSN_disj. 
It holds that (x ∉ C n0 ∩ C (S N)) (not_x_in_int_Cn0_CSN).
By not_x_in_int_Cn0_CSN it holds that 
  (¬ (x ∈ C n0 ∧ x ∈ C (S N))) (not_x_in_Cn0_and_CSN).
Contradiction. 
(*now show: both sets in F *)
It holds that (C (S N) ∈ F) (CSN_in_F). 
By FU_in_σ it holds that 
  (FU_C (S N) ∈ F) (FU_C_in_F). 
  
By additivity_meas it holds that
  (μ ((FU_C (S N)) ∪ (C (S N))) 
    = μ (FU_C (S N)) + μ (C (S N))) (muFUS_is_muFU_muS).

Write goal using (FU_C (S (S N)) 
  = (FU_C (S N)) ∪ (C (S N)))
    as (μ ((FU_C (S N)) ∪ (C (S N))) 
      = Σ of seq_μC up to N + seq_μC (S N)).
Write goal using (μ ((FU_C (S N)) ∪ (C (S N))) 
  = μ (FU_C (S N)) + μ (C (S N)))
    as (μ (FU_C (S N)) + μ (C (S N)) 
      = Σ of seq_μC up to N + seq_μC (S N)). 
It holds that (μ (FU_C (S N)) + μ (C (S N)) 
  = Σ of seq_μC up to N + seq_μC (S N)). 
Qed.

End finite_additivity.
(** ## The continuity lemma*)
(** Now we are ready to prove our main result.*)
Lemma incr_cont_meas : 
  ∀ C : (ℕ → (subset U)), is_increasing_seq_sets C
    ⇒ (∀ n : ℕ, C n ∈ F)
      ⇒ (fun (n : ℕ) ↦ (μ (C n))) 
        converges to (μ (countable_union C)). 

Proof. 
Take C_ : (ℕ ⇨ subset U) . 
Assume C_is_incr_seq.
Assume all_Cn_in_F.
Define D_ := (disjoint_seq C_). 
Define D := (countable_union D_).
Define seq_μC := (fun (n : ℕ) ↦ μ (C_ n)). 
Define seq_μD := (fun (n : ℕ) ↦ μ (D_ n)).
By CU_sets_disjointsets_equal it holds that 
  ((countable_union C_) = D) (CUC_is_CUD).
Write goal using 
  ((countable_union C_) = D) 
    as (seq_μC converges to (μ (D))). 
By μ_is_measure_on_F it holds that 
  (μ is σ-additive on F) (μ_is_σ_additive). 
By disj_seq_disjoint it holds that 
  (∀ m n : ℕ, m ≠ n ⇒ (D_ m) 
    and (D_ n) are disjoint) (D_disj). 
By disj_seq_in_F it holds that 
  (∀ n : ℕ, D_ n ∈ F) (all_Dn_in_F).
By μ_is_σ_additive it holds that 
  (Σ seq_μD equals
    (μ (D))) (μDn_is_μCUD).

We need to show that (
  ∀ ε : ℝ, ε > 0
    ⇒ ∃ N : ℕ , ∀ n : ℕ,  (n ≥ N)%nat 
      ⇒ ｜ (μ (C_ n)) - (μ (D)) ｜ < ε).
Take ε : ℝ; Assume ε_g0. 
By μDn_is_μCUD it holds that (
  ∃ N : ℕ , ∀ n : ℕ,  (n ≥ N)%nat 
    ⇒ ｜ (Σ of seq_μD up to n) -
     (μ (D)) ｜ < ε) (exists_N_μSumD_μCUD_l_ε).
Choose N such that μSumN_μCU_l_ε 
  according to exists_N_μSumD_μCUD_l_ε.

It suffices to show that (∀ n : ℕ,
  (n ≥ N)%nat ⇨ ｜ (μ (C_ n)) -
    (μ (D)) ｜ < ε).
Take n : ℕ; Assume n_geq_N.
We claim that (μ(C_ n) = 
  (Σ of seq_μD up to n) ) (μCn_is_sum_μDn). 
By FUn_disj_is_Cn it holds that 
  (finite_union_up_to D_ (S n) = C_ n) (FUD_is_C).
Write goal using (C_ n = finite_union_up_to D_ (S n))
  as (μ (finite_union_up_to D_ (S n)) 
    = Σ of seq_μD up to n). 
By finite_additivity_meas it holds that 
  (μ (finite_union_up_to D_ (S n)) 
    = Σ of seq_μD up to n) 
      which concludes the proof. 

Write goal using (μ (C_ n) = Σ of seq_μD up to n) 
  as (｜ (Σ of seq_μD up to n) -
    (μ (D)) ｜ < ε).
It holds that (｜ (Σ of seq_μD up to n) -
  (μ (D)) ｜ < ε). 
Qed. 
