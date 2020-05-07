Require Import Sets.Ensembles.
Require Import Sets.Classical_sets.
Require Import wplib.Tactics.Tactics.
Require Import wplib.Tactics.TacticsContra.
Require Import Sets.Powerset.
Require Import Logic. 
Require Import ClassicalFacts. 
Require Import Omega. 
Require Import Coq.Arith.Wf_nat. 

Variable U : Type.

Notation "'set'" := 
  (Ensemble U) (at level 50). 

Notation "'setOfSets'" := 
  (Ensemble (set)) (at level 50). 

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
  (In _ A x) (at level 50). 

Notation "x ∉ A" :=  
  (~ In _ A x) (at level 50). 

Notation "A ⊂ B" := 
  (Included _ A B) (at level 50). 

Notation "{ x : T | P }" := 
  (fun (x : T) ↦ P) (x at level 99).

Tactic Notation "We" "prove" "equality" "by" "proving" "two" "inclusions" :=
   apply Extensionality_Ensembles; 
   unfold Same_set; 
   unfold Included;
   split.

Tactic Notation "We" "prove" "by" "induction" "on" ident(x) := 
  induction x. 
(*Not nicest formulation, but 'Proof' is already taken*)
(*
Tactic Notation "Let" ident(A) "be" "a" "set" := 
  Take A : (set).

Tactic Notation "Let" ident(F) "be" "a" "set" "of" "sets" := 
  Take F : (setOfSets).
*)
Hint Resolve Full_intro : measure_theory.  (*nieuwe database measure theory*)
Hint Resolve Intersection_intro : measure_theory. 
Hint Resolve Union_introl Union_intror : measure_theory. 
Hint Resolve Disjoint_intro : measure_theory. 


Definition is_π_system (Π : setOfSets) 
  : Prop := 
    ∀ A : set, A ∈ Π ⇒ 
      ∀ B : set, B ∈ Π ⇒ 
         (A ∩ B) ∈ Π. 

Notation "A is_a_π-system" := 
  (is_π_system A) (at level 50). 

Definition Countable_union (A : (ℕ → set)) 
  : set := 
    { x:U | ∃n : ℕ, x ∈ (A n)}.

Definition full_set_in_set (Λ : setOfSets) 
  : Prop :=
    Ω ∈ Λ. 

Definition complement_in_set (Λ : setOfSets) 
  : Prop := 
    ∀A  : set, A ∈ Λ 
      ⇒ (Ω \ A) ∈ Λ. 

Definition closed_under_disjoint_countable_union (Λ : setOfSets) 
  : Prop :=
    ∀C : (ℕ → (set)), 
      (∀ m n : ℕ, m ≠ n ⇒ Disjoint _ (C m) (C n)) 
        ⇒ (∀ n : ℕ, (C n) ∈ Λ) ⇒  (Countable_union C) ∈ Λ.

Definition closed_under_countable_union (Λ : setOfSets) 
  : Prop :=  
    ∀C : (ℕ → (set)), (∀ n : ℕ, (C n) ∈ Λ) 
      ⇒ (Countable_union C) ∈ Λ.

Definition is_λ_system (Λ : setOfSets) 
  : Prop :=
    full_set_in_set Λ ∧ 
    complement_in_set Λ ∧
    closed_under_disjoint_countable_union Λ. 

Notation "A is_a_λ-system" := 
  (is_λ_system A) (at level 50). 

Definition is_σ_algebra (F : setOfSets) 
  : Prop := 
    full_set_in_set F ∧ 
    complement_in_set F ∧
    closed_under_countable_union F.

Notation "A is_a_σ-algebra" := 
  (is_σ_algebra A) (at level 50). 

Definition  σ_algebra_generated_by (A : setOfSets) 
  : (setOfSets) := 
    {B : set | ∀ F : setOfSets, F is_a_σ-algebra ⇒ (A ⊂ F ⇒ B ∈ F)} . 

Notation "σ( A )" := 
 (σ_algebra_generated_by A) (at level 50). 

Definition restriction (F : setOfSets) (A : (set)) 
  : (setOfSets) := 
    {C : set | ∃B : set, B ∈ F ⇒ C = A ∩ B}. 

(* ≤ only works for Reals *)
Definition finite_union (C : (ℕ ⇨ set)) (n : ℕ) 
  : set := 
    {x:U | (∃i : ℕ,  (i <= n ∧ x ∈ (C i)))}.

Definition finite_union_up_to (C : (ℕ ⇨ set)) (n : ℕ) 
  : (set) := 
    {x : U | (∃i : ℕ,  (i < n ∧ x ∈ (C i)))}.

Definition disjoint_seq (C : (ℕ ⇨ set)) 
  : (ℕ ⇨ set) := 
    fun (n:ℕ) ↦ (C n \ (finite_union_up_to C n)). 

(***********************************************************)
Require Import Reals. 
(* Variable setfunction  : ((Ensemble (Ensemble U)) ⇨ ℝ). *)

Definition σ_additive (μ : (set → ℝ)) : Prop := 
  ∀C : (ℕ → (set)), 
    (∀ m n : ℕ, m ≠ n ⇒ Disjoint _ (C m) (C n)) 
      ⇒ infinite_sum (fun (n:ℕ) ↦ (μ (C n))) (μ (Countable_union C)).
(*infinite_sum fn l is the proposition 'the sum of all terms of fn converges to l'*)
Notation "μ is_σ-additive" := 
  (σ_additive μ) (at level 50). 

Definition is_measure (μ : (set → ℝ)) : Prop := 
  μ ∅ = 0 ∧ μ is_σ-additive.
(*requirement that domain is sigma-algebra? *) 

Definition is_probability_measure (μ : (set → ℝ)) 
  : Prop := 
    (is_measure μ) ∧ (μ Ω = 1).

Lemma finite_additivity_meas : 
  ∀μ : (set → ℝ), is_measure μ 
    ⇒ ∀ A B : set, A ⊂ B 
      ⇒ μ A ≤ μ B. 
Admitted. 

Definition is_increasing_seq_sets (C : (ℕ → (set)))
  : Prop := 
    ∀n : ℕ, (C n) ⊂ C (S n).

Lemma incr_cont_meas : 
  ∀μ : (set → ℝ), is_measure μ 
    ⇒ ∀C : (ℕ → (set)), is_increasing_seq_sets C
      ⇒ Un_cv (fun (n : ℕ) ↦ (μ (C n))) (μ (Countable_union C)). 
(*Un_cv Cn l is the proposition 'sequence Cn converges to limit l'*)
Admitted.

Theorem uniqueness_of_prob_meas : 
  ∀μ1 : (set → ℝ), is_measure μ1 
    ⇒ ∀μ2 : (set → ℝ), is_measure μ2 
      ⇒ ∀Π, Π is_a_π-system (* ⇒ Π ⊂ F *)
        ⇒ ∀ A : set, A ∈ Π ⇒ μ1 A = μ2 A
          ⇒ ∀ B : set, B ∈ (σ(Π)) ⇒ μ1 A = μ2 A. 
Admitted. 
(*definition of open not suitable?
Definition Borel_σ_alg : (Ensemble (Ensemble ℝ)) := 
  σ(fun (A:(ℝ ⇨ Prop)) ↦ open_set A). 
*)







