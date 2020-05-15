(*Version 1.1.4 - 15-05-2020
  new brackets as not to conflict coq notation {x : A | P}
  imported lemmas on CU, disjointness and disjoint sets
  proof of incr_cont_meas continued
  notations for set and setOfSets adapted to subsets of U
  adapted notation improved, dependent on U
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

Notation "subset_of U" := 
  (Ensemble U) (at level 50). 

Notation "'setOfSubsetsU'" := 
  (Ensemble (subsetU)) (at level 50). 

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
  Take A : (subsetU).

Tactic Notation "Let" ident(F) "be" "a" "set" "of" "sets" := 
  Take F : (setOfSubsetsU).
*)
Hint Resolve Full_intro : measure_theory.  (*nieuwe database measure theory*)
Hint Resolve Intersection_intro : measure_theory. 
Hint Resolve Union_introl Union_intror : measure_theory. 
Hint Resolve Disjoint_intro : measure_theory. 


Definition is_π_system (Π : setOfSubsetsU) 
  : Prop := 
    ∀ A : subsetU, A ∈ Π ⇒ 
      ∀ B : subsetU, B ∈ Π ⇒ 
         (A ∩ B) ∈ Π. 

Notation "A is_a_π-system" := 
  (is_π_system A) (at level 50). 

Definition Countable_union (A : (ℕ → subsetU) ) 
  : subsetU := 
    ｛ x:U | ∃n : ℕ, x ∈ (A n)｝.

Definition full_set_in_set (Λ : setOfSubsetsU) 
  : Prop :=
    Ω ∈ Λ. 

Definition complement_in_set (Λ : setOfSubsetsU) 
  : Prop := 
    ∀A  : subsetU, A ∈ Λ 
      ⇒ (Ω \ A) ∈ Λ. 

Definition closed_under_disjoint_countable_union (Λ : setOfSubsetsU) 
  : Prop :=
    ∀C : (ℕ → (subsetU)), 
      (∀ m n : ℕ, m ≠ n ⇒ Disjoint _ (C m) (C n)) 
        ⇒ (∀ n : ℕ, (C n) ∈ Λ) ⇒  (Countable_union C) ∈ Λ.

Definition closed_under_countable_union (Λ : setOfSubsetsU) 
  : Prop :=  
    ∀C : (ℕ → (subsetU)), (∀ n : ℕ, (C n) ∈ Λ) 
      ⇒ (Countable_union C) ∈ Λ.

Definition is_λ_system (Λ : setOfSubsetsU) 
  : Prop :=
    full_set_in_set Λ ∧ 
    complement_in_set Λ ∧
    closed_under_disjoint_countable_union Λ. 

Notation "A is_a_λ-system" := 
  (is_λ_system A) (at level 50). 

Definition is_σ_algebra (F : setOfSubsetsU) 
  : Prop := 
    full_set_in_set F ∧ 
    complement_in_set F ∧
    closed_under_countable_union F.

Inductive σ_algebra : setOfSubsetsU := 
  | σ_alg_omeg : full_set_in_set σ_algebra
  | σ_alg_comp : complement_in_set σ_algebra
  | σ_alg_cuCU : closed_under_countable_union σ_algebra. 


Notation "A is_a_σ-algebra" := 
  (is_σ_algebra A) (at level 50). 

Definition  σ_algebra_generated_by (A : setOfSubsetsU) 
  : (setOfSubsetsU) := 
    ｛B : subsetU | ∀ F : setOfSubsetsU, F is_a_σ-algebra ⇒ (A ⊂ F ⇒ B ∈ F)｝ . 

Notation "σ( A )" := 
 (σ_algebra_generated_by A) (at level 50). 

Definition restriction (F : setOfSubsetsU) (A : (subsetU)) 
  : (setOfSubsetsU) := 
    ｛C : subsetU | ∃B : subsetU, B ∈ F ⇒ C = A ∩ B｝. 

(* ≤ only works for Reals *)
Definition finite_union (C : (ℕ ⇨ subsetU) ) (n : ℕ) 
  : subsetU := 
    ｛x:U | (∃i : ℕ,  (i <= n ∧ x ∈ (C i)))｝.

Definition finite_union_up_to (C : (ℕ ⇨ subsetU) ) (n : ℕ) 
  : (subsetU) := 
    ｛x : U | (∃i : ℕ,  (i < n ∧ x ∈ (C i)))｝.

Definition disjoint_seq (C : (ℕ ⇨ subsetU) ) 
  : (ℕ ⇨ subsetU)  := 
    fun (n:ℕ) ↦ (C n \ (finite_union_up_to C n)). 


Lemma intersection_empty : ∀A : subsetU, 
  (A ∩ ∅) = ∅. 

Proof. 
Take A : (subsetU). 
We prove equality by proving two inclusions. 
Take x : U; Assume x_in_intersection. 
destruct x_in_intersection. 
Contradiction. 

Take x : U; Assume x_in_empty. 
Contradiction. 
Qed. 

Lemma empty_disjoint : ∀A : subsetU, 
  Disjoint _ A ∅. 

Proof. 
Take A : (subsetU).
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
  ∀ A B : (subsetU), ∀ x : U, 
    x ∈ (A ∪ B) ⇒ (x ∈ A ∨ x ∈ B).

Proof. 
Take A B : (subsetU). 
Take x : U; Assume x_in_union. 
destruct x_in_union. 
(* x ∈ A: *)
It follows that (x ∈ A ∨ x ∈ B).
(* x ∈ B: *) 
It follows that (x ∈ A ∨ x ∈ B). 
Qed. 


Lemma FU_up_to_0_empty : 
  ∀ C : (ℕ ⇨ subsetU) , finite_union_up_to C 0 = ∅. 

Proof. 
Take C : (ℕ ⇨ subsetU) . 
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
  ∀ C : (ℕ ⇨ subsetU) , 
    (∀ m n : ℕ, m ≠ n ⇒ Disjoint _ 
      (disjoint_seq C m) (disjoint_seq C n)). 

Proof. 
Take C : (ℕ ⇨ subsetU) . 
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
  ∀ C : (ℕ ⇨ subsetU) , 
    Countable_union (disjoint_seq C) = Countable_union C.

Proof. 
Take C : (ℕ ⇨ subsetU) .
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
Variable F : setOfSubsetsU. 
(*Definition σ_algebras := (sig (is_σ_algebra)). *)

(*
Definition σ_algebra1 := sig is_σ_algebra. 
Variable F : σ_algebra1. 
Definition myclass :=  Ensemble (Ensemble U). 
Definition myprojection : (σ_algebra1 -> myclass) := (@proj1_sig myclass is_σ_algebra). 
Coercion myprojection : σ_algebra1 >-> myclass.  
*)
Definition σ_additive_on (F : setOfSubsetsU) (μ : (subsetU ⇨ ℝ)) : Prop := 
  ∀C : (ℕ → (subsetU)), (∀n : ℕ, C n ∈ F) 
    ⇒ (∀ m n : ℕ, m ≠ n ⇒ Disjoint _ (C m) (C n)) 
      ⇒ infinite_sum (fun (n:ℕ) ↦ (μ (C n))) (μ (Countable_union C)).
(*infinite_sum fn l is the proposition 'the sum of all terms of fn converges to l'*)
Notation "μ is_σ-additive_on F" := 
  (σ_additive_on F μ) (at level 50). 


Definition is_measure_on (F : setOfSubsetsU) (μ : (subsetU → ℝ)) : Prop := 
  is_σ_algebra F ∧ μ ∅ = 0 ∧ μ is_σ-additive_on F.

Definition is_probability_measure_on (F : setOfSubsetsU) (μ : (subsetU → ℝ)) 
  : Prop := 
    (is_measure_on F μ) ∧ (μ Ω = 1).

Definition is_increasing_seq_sets (C : (ℕ → (subsetU)))
  : Prop := 
    ∀n : ℕ, (C n) ⊂ C (S n).
(*
Fixpoint finite_seq (C : (ℕ → (subsetU))) (p : Prop) (n : ℕ) {struct p}
  : (subsetU) :=
    match p with 
      0 => C 0
    | S p => (fun  ↦ ∅)
    end.  
*)
Lemma finite_additivity_meas : 
  ∀μ : (subsetU → ℝ), is_measure_on F μ 
    ⇒ ∀C : (ℕ → (subsetU)), 
      (∀ m n : ℕ, m ≠ n ⇒ Disjoint _ (C m) (C n))  
         ⇒ ∀ N : ℕ, μ (finite_union_up_to C N) 
          = sum_f_R0 (fun (n : ℕ) ↦ (μ (C n))) (N-1).

Proof. 
Take μ : (subsetU ⇨ ℝ). 
Assume μ_is_measure_on_F. 
Take C : (ℕ ⇨ subsetU) . 
Assume C_n_disjoint. 
Take N : ℕ. 

Admitted.
 

Lemma monotonicity_meas :
  ∀μ : (subsetU → ℝ), is_measure_on F μ 
    ⇒ ∀ A B : subsetU, A ⊂ B 
      ⇒ μ A ≤ μ B. 
Admitted. 

(*Proof using alternative sequence from pi-lambda proof*)
Lemma incr_cont_meas : 
  ∀μ : (subsetU → ℝ), is_measure_on F μ 
    ⇒ ∀C : (ℕ → (subsetU)), is_increasing_seq_sets C
      ⇒ Un_cv (fun (n : ℕ) ↦ (μ (C n))) (μ (Countable_union C)). 
(*Un_cv Cn l is the proposition 'sequence Cn converges to limit l'*)
Proof. 
Take μ : (subsetU ⇨ ℝ). 
Assume μ_is_measure_on_F. 
Take C : (ℕ ⇨ subsetU) . 
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
  ∀μ1 : (subsetU → ℝ), is_measure μ1 
    ⇒ ∀μ2 : (subsetU → ℝ), is_measure μ2 
      ⇒ ∀Π, Π is_a_π-system (* ⇒ Π ⊂ F *)
        ⇒ ∀ A : subsetU, A ∈ Π ⇒ μ1 A = μ2 A
          ⇒ ∀ B : subsetU, B ∈ (σ(Π)) ⇒ μ1 A = μ2 A. 
Admitted. 

(************)
(*   Old:   *)
(************)
Definition aux_seq (C : (ℕ → (subsetU))) 
  : ℕ → (subsetU) := 
    fun (n : nat) ↦ (C (S n) \ C n).

Lemma aux_set_disjoint : 
  ∀ C : (ℕ → (subsetU)), 
    is_increasing_seq_sets C 
      ⇒ (∀ m n : ℕ, m ≠ n ⇒ Disjoint _ (aux_seq C m) (aux_seq C n)). 

Proof. 
Take C : (ℕ ⇨ subsetU) . 
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
  ∀ C : (ℕ → (subsetU)), 
    is_increasing_seq_sets C 
      ⇒ Countable_union (aux_seq C) = Countable_union C.

Proof. 
Take C  : (ℕ ⇨ subsetU) . 
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




