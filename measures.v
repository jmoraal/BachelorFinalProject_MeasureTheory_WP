(*Version 1.1.2 - 11-05-2020
  new brackets as not to conflict coq notation {x : A | P}
  imported lemmas on CU, disjointness and disjoint sets
  proof of incr_cont_meas continued
*)

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
    ｛ x:U | ∃n : ℕ, x ∈ (A n)｝.

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

Inductive σ_algebra : setOfSets := 
  | σ_alg_omeg : full_set_in_set σ_algebra
  | σ_alg_comp : complement_in_set σ_algebra
  | σ_alg_cuCU : closed_under_countable_union σ_algebra. 


Notation "A is_a_σ-algebra" := 
  (is_σ_algebra A) (at level 50). 

Definition  σ_algebra_generated_by (A : setOfSets) 
  : (setOfSets) := 
    ｛B : set | ∀ F : setOfSets, F is_a_σ-algebra ⇒ (A ⊂ F ⇒ B ∈ F)｝ . 

Notation "σ( A )" := 
 (σ_algebra_generated_by A) (at level 50). 

Definition restriction (F : setOfSets) (A : (set)) 
  : (setOfSets) := 
    ｛C : set | ∃B : set, B ∈ F ⇒ C = A ∩ B｝. 

(* ≤ only works for Reals *)
Definition finite_union (C : (ℕ ⇨ set)) (n : ℕ) 
  : set := 
    ｛x:U | (∃i : ℕ,  (i <= n ∧ x ∈ (C i)))｝.

Definition finite_union_up_to (C : (ℕ ⇨ set)) (n : ℕ) 
  : (set) := 
    ｛x : U | (∃i : ℕ,  (i < n ∧ x ∈ (C i)))｝.

Definition disjoint_seq (C : (ℕ ⇨ set)) 
  : (ℕ ⇨ set) := 
    fun (n:ℕ) ↦ (C n \ (finite_union_up_to C n)). 


Lemma intersection_empty : ∀A : set, 
  (A ∩ ∅) = ∅. 

Proof. 
Take A : (set). 
We prove equality by proving two inclusions. 
Take x : U; Assume x_in_intersection. 
destruct x_in_intersection. 
Contradiction. 

Take x : U; Assume x_in_empty. 
Contradiction. 
Qed. 

Lemma empty_disjoint : ∀A : set, 
  Disjoint _ A ∅. 

Proof. 
Take A : (set).
It suffices to show that (∀ x:U, x ∉ (A ∩ ∅)).
Take x : U. 
By intersection_empty it holds that 
  ((A ∩ ∅) = ∅) (int_empty). 
Write goal using ((A ∩ ∅) = ∅) as (x ∉ ∅). 
It holds that (x ∉ ∅). 
Qed. 


Lemma neq_equiv : ∀ x y : ℕ,
  (x ≠ y) ⇒ (x < y ∨ y < x).

Proof. 
intros x y. omega.
Qed. 


Lemma leq_equiv : ∀ x y : ℕ,
  (x <= y) ⇒ (x < y ∨ x = y).

Proof. 
intros x y. omega. 
Qed. 


Lemma union_to_or : 
  ∀ A B : (set), ∀ x : U, 
    x ∈ (A ∪ B) ⇒ (x ∈ A ∨ x ∈ B).

Proof. 
Take A B : (set). 
Take x : U; Assume x_in_union. 
destruct x_in_union. 
(* x ∈ A: *)
It follows that (x ∈ A ∨ x ∈ B).
(* x ∈ B: *) 
It follows that (x ∈ A ∨ x ∈ B). 
Qed. 


Lemma FU_up_to_0_empty : 
  ∀ C : (ℕ ⇨ set), finite_union_up_to C 0 = ∅. 

Proof. 
Take C : (ℕ ⇨ set). 
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
  ∀ C : (ℕ ⇨ set), 
    (∀ m n : ℕ, m ≠ n ⇒ Disjoint _ 
      (disjoint_seq C m) (disjoint_seq C n)). 

Proof. 
Take C : (ℕ ⇨ set). 
Take m n : ℕ. 
Assume m_neq_n.
By neq_equiv it holds that 
  (m ≠ n ⇒ (m < n) ∨ (m > n)) (m_l_g_n).
It holds that ((m < n) ∨ (m > n)) (m_lg_n). 
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
  ∀ C : (ℕ ⇨ set), 
    Countable_union (disjoint_seq C) = Countable_union C.

Proof. 
Take C : (ℕ ⇨ set).
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

(*Definition σ_algebras := (sig (is_σ_algebra)). *)

Variable F : setOfSets.


Definition σ_additive (μ : (set ⇨ ℝ)) : Prop := 
  ∀C : (ℕ → (set)), 
    (∀ m n : ℕ, m ≠ n ⇒ Disjoint _ (C m) (C n)) 
      ⇒ infinite_sum (fun (n:ℕ) ↦ (μ (C n))) (μ (Countable_union C)).
(*infinite_sum fn l is the proposition 'the sum of all terms of fn converges to l'*)
Notation "μ is_σ-additive" := 
  (σ_additive μ) (at level 50). 
(*incorrect domain*)
Definition is_measure_on (F : setOfSets) (μ : (set → ℝ)) : Prop := 
  is_σ_algebra F ∧ μ ∅ = 0 ∧ μ is_σ-additive.

Definition is_probability_measure (μ : (set → ℝ)) 
  : Prop := 
    (is_measure_on F μ) ∧ (μ Ω = 1).

Definition is_increasing_seq_sets (C : (ℕ → (set)))
  : Prop := 
    ∀n : ℕ, (C n) ⊂ C (S n).

Lemma finite_additivity_meas : 
  ∀μ : (set → ℝ), is_measure_on F μ 
    ⇒ ∀ A B : set, A ⊂ B 
      ⇒ μ A ≤ μ B. 
Admitted. 

(*Proof using alternative sequence from pi-lambda proof*)
Lemma incr_cont_meas : 
  ∀μ : (set → ℝ), is_measure_on F μ 
    ⇒ ∀C : (ℕ → (set)), is_increasing_seq_sets C
      ⇒ Un_cv (fun (n : ℕ) ↦ (μ (C n))) (μ (Countable_union C)). 
(*Un_cv Cn l is the proposition 'sequence Cn converges to limit l'*)
Proof. 
Take μ : (set ⇨ ℝ). 
Assume μ_is_measure_on_F. 
Take C : (ℕ ⇨ set). 
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
  (μ is_σ-additive) (μ_is_σ_additive). 
By disj_seq_disjoint it holds that 
  (∀ m n : ℕ, m ≠ n ⇒ Disjoint _ (D m) (D n)) (D_disj). 
By μ_is_σ_additive it holds that 
  (infinite_sum (fun (n:ℕ) ↦ (μ (D n))) 
    (μ (Countable_union D))) (μDn_is_μCUD).



Admitted. 







Theorem uniqueness_of_prob_meas : 
  ∀μ1 : (set → ℝ), is_measure μ1 
    ⇒ ∀μ2 : (set → ℝ), is_measure μ2 
      ⇒ ∀Π, Π is_a_π-system (* ⇒ Π ⊂ F *)
        ⇒ ∀ A : set, A ∈ Π ⇒ μ1 A = μ2 A
          ⇒ ∀ B : set, B ∈ (σ(Π)) ⇒ μ1 A = μ2 A. 
Admitted. 

(************)
(*   Old:   *)
(************)
Definition aux_seq (C : (ℕ → (set))) 
  : ℕ → (set) := 
    fun (n : nat) ↦ (C (S n) \ C n).

Lemma aux_set_disjoint : 
  ∀ C : (ℕ → (set)), 
    is_increasing_seq_sets C 
      ⇒ (∀ m n : ℕ, m ≠ n ⇒ Disjoint _ (aux_seq C m) (aux_seq C n)). 

Proof. 
Take C : (ℕ ⇨ set). 
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
  ∀ C : (ℕ → (set)), 
    is_increasing_seq_sets C 
      ⇒ Countable_union (aux_seq C) = Countable_union C.

Proof. 
Take C  : (ℕ ⇨ set). 
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




