(*Version 1.5.6 - 21-05-2020
  all proofs finished
  new tactic to introduce two variables at once
  all 'Expand the definition of...' replaced
  proof of CU_sets_disjointsets_equal slightly shortened
  consistent spacing after ∀ and ∃
  document order slightly changed (notations and set-related lemmas grouped together)
  notations 'set' and 'setOfSets' fixed to depend on U
  last fixes to subset U
  brackets for set notation fixed as not to conflict sig notation
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

Hint Resolve Full_intro : measure_theory.  (*nieuwe database measure theory*)
Hint Resolve Intersection_intro : measure_theory. 
Hint Resolve Union_introl Union_intror : measure_theory. 
Hint Resolve Disjoint_intro : measure_theory. 

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

Definition is_π_system (Π : setOfSubsets U) 
  : Prop := 
    ∀ A : subset U, A ∈ Π 
      ⇒ ∀ B : subset U, B ∈ Π 
        ⇒ (A ∩ B) ∈ Π. 

Definition Countable_union (A : (ℕ → subset U)) 
  : set := 
    ｛ x:U | ∃ n : ℕ, x ∈ (A n)｝.

Definition full_set_in_set (Λ : setOfSubsets U) 
  : Prop :=
    Ω ∈ Λ. 

Definition complement_in_set (Λ : setOfSubsets U) 
  : Prop := 
    ∀ A  : subset U, A ∈ Λ 
      ⇒ (Ω \ A) ∈ Λ. 

Definition closed_under_disjoint_countable_union (Λ : setOfSubsets U) 
  : Prop :=
    ∀ C : (ℕ → (subset U)), 
      (∀ m n : ℕ, m ≠ n ⇒ Disjoint _ (C m) (C n)) 
        ⇒ (∀ n : ℕ, (C n) ∈ Λ) ⇒ (Countable_union C) ∈ Λ.

Definition closed_under_countable_union (Λ : setOfSubsets U) 
  : Prop :=  
    ∀ C : (ℕ → (subset U)), (∀ n : ℕ, (C n) ∈ Λ) 
      ⇒ (Countable_union C) ∈ Λ.

Definition is_λ_system (Λ : setOfSubsets U) 
  : Prop :=
    full_set_in_set Λ ∧ 
    complement_in_set Λ ∧
    closed_under_disjoint_countable_union Λ. 

Definition λ_system_generated_by (A : setOfSubsets U) 
  : (setOfSubsets U) := 
    ｛B : set | (∀ Λ : setOfSubsets U, Λ is_a_λ-system 
       ⇒ (A ⊂ Λ ⇒ B ∈ Λ))｝. 

Definition is_σ_algebra (F : setOfSubsets U) 
  : Prop := 
    full_set_in_set F ∧ 
    complement_in_set F ∧
    closed_under_countable_union F.

Definition  σ_algebra_generated_by (A : setOfSubsets U) 
  : (setOfSubsets U) := 
    ｛B : set | ∀ F : setOfSubsets U, F is_a_σ-algebra ⇒ (A ⊂ F ⇒ B ∈ F)｝ . 

Definition restriction (F : setOfSubsets U) (A : (subset U)) 
  : (setOfSubsets U) := 
    ｛C : set | ∃ B : subset U, B ∈ F ⇒ C = A ∩ B｝. 

(* ≤ only works for Reals *)
Definition finite_union (C : (ℕ ⇨ subset U)) (n : ℕ) 
  : set := 
    ｛x : U | (∃ i : ℕ,  (i <= n ∧ x ∈ (C i)))｝.

Definition finite_union_up_to (C : (ℕ ⇨ subset U)) (n : ℕ) 
  : (subset U) := 
    ｛x : U | (∃ i : ℕ,  (i < n ∧ x ∈ (C i)))｝.

Definition disjoint_seq (C : (ℕ ⇨ subset U)) 
  : (ℕ ⇨ subset U) := 
    fun (n : ℕ) ↦ (C n \ (finite_union_up_to C n)). 

(*measure theory-related notations: *)
Notation "A is_a_π-system" := 
  (is_π_system A) (at level 50).
  
Notation "A is_a_λ-system" := 
  (is_λ_system A) (at level 50). 

Notation "A is_a_σ-algebra" := 
  (is_σ_algebra A) (at level 50).
(*TODO: general tactic for the form above? *)

Notation "λ( A )" := 
 (λ_system_generated_by A) (at level 50).
 
Notation "σ( A )" := 
 (σ_algebra_generated_by A) (at level 50).


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


Lemma setminus_empty : 
  ∀ A : subset U, A \ ∅ = A. 

Proof. 
Take A : (subset U). 
We prove equality by proving two inclusions.
Take x : U; Assume x_in_A_wo_empty. 
It holds that (x ∈ A). 

Take x : U; Assume x_in_A. 
It holds that (x ∈ (A \ ∅)). 
Qed. 


Lemma intersection_full : 
  ∀ A : subset U, (Ω ∩ A) = A. 

Proof. 
Take A : (subset U). 
We prove equality by proving two inclusions. 
Take x : U; Assume x_in_intersection. 
destruct x_in_intersection. 
It holds that (x ∈ A). 

Take x : U; Assume x_in_A. 
It holds that (x ∈ Ω) (x_in_omega). 
It follows that (x ∈ (Ω ∩ A)). 
Qed. 


Lemma intersection_empty : 
  ∀ A : subset U, (A ∩ ∅) = ∅. 

Proof. 
Take A : (subset U). 
We prove equality by proving two inclusions. 
Take x : U; Assume x_in_intersection. 
destruct x_in_intersection. 
Contradiction. 

Take x : U; Assume x_in_empty. 
Contradiction. 
Qed. 

Lemma empty_disjoint : 
  ∀ A : subset U, Disjoint _ A ∅. 

Proof. 
Take A : (subset U).
It suffices to show that (∀ x:U, x ∉ (A ∩ ∅)).
Take x : U. 
By intersection_empty it holds that 
  ((A ∩ ∅) = ∅) (int_empty). 
Write goal using ((A ∩ ∅) = ∅) as (x ∉ ∅). 
It holds that (x ∉ ∅). 
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


Lemma not_in_comp : 
  ∀ A : subset U, ∀ x : U, 
    x ∉ (Ω \ A) ⇒ x ∈ A.

Proof. 
Take A : (subset U); Take x : U. 
Assume x_not_in_complement. 
We argue by contradiction. 
It holds that (x ∈ (Ω \ A)) (x_in_complement).
Contradiction. 
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


Lemma geq_equiv : ∀ x y : ℕ,
  (x >= y) ⇒ (x = y ∨ x > y).

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
  ∀ C : (ℕ ⇨ subset U), 
    (∀ m n : ℕ, m ≠ n ⇒ Disjoint _ 
      (disjoint_seq C m) (disjoint_seq C n)). 

Proof. 
Take C : (ℕ ⇨ subset U). 
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
  ∀ C : (ℕ ⇨ subset U), 
    Countable_union (disjoint_seq C) = Countable_union C.

Proof. 
Take C : (ℕ ⇨ subset U).
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
It holds that (n0 <= n) (n0_le_n). (*avoid %nat? *) 
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
  ((finite_union_up_to C n ∪ C n) ∈ F) (xx). 
Apply xx. 
Qed. 


Lemma π_and_λ_is_σ : 
  ∀ F : setOfSubsets U, 
    F is_a_π-system ⇒ F is_a_λ-system 
      ⇒ F is_a_σ-algebra. 

Proof. 
Take F : (setOfSubsets U).
Assume F_is_π_system. 
Assume F_is_λ_system. 
It holds that 
  (closed_under_disjoint_countable_union F) (cu_disj_CU). 
We need to show that (full_set_in_set F 
  ∧ complement_in_set F 
    ∧ closed_under_countable_union F). 
split. (*WP version for split?*)
It holds that (full_set_in_set F) .
split.
It holds that (complement_in_set F). 

We need to show that (∀ C : ℕ ⇨ set,
  (∀ n : ℕ, C n ∈ F) 
    ⇒ Countable_union C ∈ F). 
Take C : (ℕ ⇨ subset U); Assume all_C_n_in_F. 
By classic it holds that 
  ((∀ m n : ℕ, m ≠ n ⇒ Disjoint _ (C m) (C n)) ∨ 
  ¬(∀ m n : ℕ, m ≠ n ⇒ Disjoint _ (C m) (C n))) (all_or_not_all_disjoint). 
Because all_or_not_all_disjoint 
  either all_disjoint or not_all_disjoint. 
(*Case 1: all C_n disjoint.*) 
It holds that (Countable_union C ∈ F). 
(*Case 2: not all C_n disjoint. *)
By CU_sets_disjointsets_equal it holds that 
  (Countable_union (disjoint_seq C) = Countable_union C) (CUdisj_is_CU).
Write goal using 
  (Countable_union C = Countable_union (disjoint_seq C)) 
    as (Countable_union (disjoint_seq C) ∈ F). 

We claim that (∀ n : ℕ, disjoint_seq C n ∈ F) (disj_in_F). 
Take n : ℕ. 
By FU_in_π_and_λ it holds that 
  ((finite_union_up_to C n) ∈ F) (FU_in_F).
By complements_in_π_and_λ it holds that 
  ((C n) \ (finite_union_up_to C n) ∈ F) (comp_in_F).
Write goal using 
  (disjoint_seq C n = (C n \ finite_union_up_to C n)) 
    as ((C n \ finite_union_up_to C n) ∈ F). 
Apply comp_in_F. 

By disj_seq_disjoint it holds that 
  ((∀ m n : ℕ, m ≠ n ⇒ 
    Disjoint _ 
      (disjoint_seq C m) (disjoint_seq C n))) (disj_seq_disj). 
It holds that (Countable_union (disjoint_seq C) ∈ F).
Qed. 


Lemma generated_system_is_λ : 
  ∀ A : setOfSubsets U, 
    λ(A) is_a_λ-system.

Proof. 
Take A : (setOfSubsets U). 
We need to show that (full_set_in_set (λ(A))
  ∧ complement_in_set (λ(A)) 
    ∧ closed_under_disjoint_countable_union (λ(A))). 
It holds that (∀ Λ : setOfSubsets U, 
  Λ is_a_λ-system ⇒ (full_set_in_set Λ)
    ∧ complement_in_set Λ
      ∧ closed_under_disjoint_countable_union Λ) 
        (lambda_props_for_all). 
split. 
It follows that (full_set_in_set (λ(A))). 
split. 
It follows that (complement_in_set (λ(A))). 

We need to show that (∀ C : ℕ ⇨ set,
  (∀ m n : ℕ, m ≠ n ⇒ Disjoint U (C m) (C n))
    ⇒ (∀ n : ℕ, C n ∈ λ(A)) 
      ⇒ Countable_union C ∈ λ(A)). 
Take C : (ℕ ⇨ subset U). 
Assume all_Cn_disjoint. 
Assume all_Cn_in_λA.

We claim that (∀ Λ : setOfSubsets U, 
  Λ is_a_λ-system ⇒ A ⊂ Λ 
    ⇒ (Countable_union C) ∈ Λ) (CU_in_all).
Take Λ : (setOfSubsets U). 
Assume Λ_is_λ_system. 
Assume A_subs_Λ. 
It holds that 
  (closed_under_disjoint_countable_union Λ) 
    (closed_under_disj_CU). 
It holds that (
  (∀ m n : ℕ, m ≠ n ⇨ Disjoint U (C m) (C n))  
    ⇒ ∀ n : ℕ, C n ∈ Λ) (disj_implies_all_Cn_in_Λ).
It follows that (Countable_union C ∈ Λ). 
It follows that (Countable_union C ∈ λ(A)). 
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


Lemma disj_union_in_λ_system : 
  ∀ Λ : setOfSubsets U, Λ is_a_λ-system
    ⇒ ∀ A B : subset U, A ∈ Λ ⇒ B ∈ Λ 
      ⇒ Disjoint _ A B ⇒ A ∪ B ∈ Λ. 

Proof. 
Take Λ : (setOfSubsets U); Assume Λ_is_a_λ_system. 
Take A B : (subset U). 
Assume A_in_Λ; Assume B_in_Λ. 
Assume A_B_disjoint. 

We claim that (∀ n : ℕ, aux_seq A B n ∈ Λ) (all_aux_in_Λ). 
Take n : ℕ. 
We prove by induction on n. 
It holds that (aux_seq A B 0 ∈ Λ). 
We prove by induction on n. (*0 and 1 defined, rest inductively. Other way? *)
It holds that (aux_seq A B 1 ∈ Λ). 
Write goal using (aux_seq A B (S (S n)) = ∅) 
  as (∅ ∈ Λ). 
By empty_in_λ it holds that 
  (∅ ∈ Λ) (empty_in_Λ).
Apply empty_in_Λ.  

By CU_aux_is_union it holds that 
  (A ∪ B = Countable_union (aux_seq A B)) (union_to_CU). 
Write goal using (A ∪ B = Countable_union (aux_seq A B))
  as (Countable_union (aux_seq A B) ∈ Λ). 

By disjoint_aux it holds that 
  (∀ m n : ℕ, m ≠ n ⇒ Disjoint _ (aux_seq A B m) (aux_seq A B n)) (aux_disjoint).
By Λ_is_a_λ_system it holds that 
  (closed_under_disjoint_countable_union Λ) (closed_under_disj_CU). 
It holds that ((∀ m n : ℕ, m ≠ n ⇒ Disjoint U (aux_seq A B m) (aux_seq A B n))
    ⇒ (for all n : ℕ, aux_seq A B n ∈ Λ)) (props_cu_disj_CU). 
By closed_under_disj_CU it holds that ((Countable_union (aux_seq A B)) ∈ Λ) (xx). 
Apply xx. 
Qed. 

Lemma intersection_and_complement_disjoint : 
  ∀ A B : subset U, Disjoint _ (A ∩ B) (Ω \ B). 

Proof. 
Take A B : (subset U). 
It suffices to show that (∀ x : U, x ∉ ((A ∩ B) ∩ (Ω \ B))). 
Take x : U. 
We argue by contradiction. 
We claim that (x ∈ ((A ∩ B) ∩ (Ω \ B))) (x_in_AB_and_comp).
Apply NNPP; Apply H. 
destruct x_in_AB_and_comp. 
destruct H0. 
By H1 it holds that (x ∉ B) (x_not_in_B).
Contradiction.  
Qed.


Lemma complement_as_union_intersection : 
  ∀ A B : subset U, (Ω \ ((A ∩ B) ∪ (Ω \ B))) = (Ω \ A) ∩ B.

Proof. 
Take A B : (subset U). 
We prove equality by proving two inclusions. 
Take x : U; Assume x_in_lhs. 
destruct x_in_lhs.
By H0 it holds that 
  ((x ∉ (A ∩ B)) ∧ (x ∉ (Ω \ B))) (x_not_in_int_comp). 
Because x_not_in_int_comp 
  both x_not_in_int and x_not_in_comp. 
By x_not_in_int it holds that 
  (x ∉ A) (x_not_in_A). 
It holds that (x ∈ (Ω \ A)) (x_in_comp_A). 
By not_in_comp it holds that (x ∈ B) (x_in_B).
It follows that (x ∈ ((Ω \ A) ∩ B)). 

Take x : U; Assume x_in_rhs. 
destruct x_in_rhs. (*"Because x_in_rhs both x_in_comp_A and x_in_B" doesn't work*)
By H it holds that (x ∉ A) (x_not_in_A). 
By H0 it holds that (x ∉ (Ω \ B)) (x_not_in_comp). 

We claim that (x ∉ (A ∩ B)) (x_not_in_AB).
We argue by contradiction. 
We claim that (x ∈ (A ∩ B)) (x_in_AB).
Apply NNPP; Apply H1.   
destruct x_in_AB. 
Contradiction. 

We claim that (x ∉ ((A ∩ B) ∪ (Ω \ B))) (x_not_in_union).
We argue by contradiction. 
We claim that (x ∈ ((A ∩ B) ∪ (Ω \ B))) (x_in_union). 
Apply NNPP; Apply H1. 
Because x_in_union either x_in_AB or x_in_comp. 
Contradiction. 
Contradiction. (*tactic 'contradiction in both cases'? *)
It follows that (x ∈ (Ω \ ((A ∩ B) ∪ (Ω \ B)))). 
Qed.  

Definition H (B : subset U) (λΠ : setOfSubsets U)
  : setOfSubsets U := 
    ｛A : (subset U) | (A ∩ B ∈ λΠ) ｝. 

Definition seq_intersection (C : (ℕ ⇨ subset U)) (B : subset U)
  : ℕ ⇨ set := 
    fun (n : ℕ) ↦ ((C n) ∩ B).

Lemma C_int_B_disjoint : 
  ∀ C : (ℕ ⇨ subset U), ∀ B : subset U, 
    (∀ m n : ℕ, m ≠ n ⇨ Disjoint U (C m) (C n))
      ⇒ ∀ m n : ℕ, m ≠ n 
        ⇒ Disjoint U (seq_intersection C B m) (seq_intersection C B n). 

Proof. 
Take C : (ℕ ⇨ subset U); Take B : (subset U). 
Assume all_Cn_disjoint. 
Take m n : ℕ. 
Assume m_neq_n. 
By all_Cn_disjoint it holds that 
  (Disjoint U (C m) (C n)) (Cm_Cn_disj).
We argue by contradiction. 
By H0 it holds that 
  (∃ x : U, x ∈ ((C m ∩ B) ∩ (C n ∩ B))) (exists_x_in_CmB_CnB).
Choose x such that x_in_CmB_CnB 
  according to exists_x_in_CmB_CnB.
By x_in_CmB_CnB it holds that 
  (x ∈ (C m ∩ B) ∧ x ∈ (C n ∩ B)) (x_in_CmB_and_CnB). 
Because x_in_CmB_and_CnB 
  both x_in_CmB and x_in_CnB. 
By x_in_CmB it holds that 
  (x ∈ C m ∧ x ∈ B) (x_in_Cm_and_B).
It holds that (x ∈ C m) (x_in_Cm). 
By x_in_CnB it holds that 
  (x ∈ C n ∧ x ∈ B) (x_in_Cn_and_B).
It holds that (x ∈ C n) (x_in_Cn).
It holds that 
  (x ∈ C n ∧ x ∈ C m) (x_in_Cm_and_Cn). 
By x_in_Cm_and_Cn it holds that 
  (x ∈ (C m ∩ C n)) (x_in_Cm_Cn). 
destruct Cm_Cn_disj.
By H1 it holds that (x ∉ (C m ∩ C n)) (x_not_in_Cm_Cn). 
Contradiction. 
Qed. 

Lemma CU_seq_int_is_CU_int : 
  ∀ C : (ℕ ⇨ subset U), ∀ B : subset U, 
    Countable_union (seq_intersection C B) = (Countable_union C) ∩ B. 

Proof. 
Take C : (ℕ ⇨ subset U); Take B : (subset U). 
We prove equality by proving two inclusions. 
Take x : U; Assume x_in_lhs. 
Choose n such that x_in_seq_Cn according to x_in_lhs.
destruct x_in_seq_Cn. 
By H0 it holds that (x ∈ Countable_union C) (x_in_CU). 
By H1 it holds that (x ∈ B) (x_in_B). 
It follows that (x ∈ (Countable_union C ∩ B)). 

Take x : U; Assume x_in_rhs. 
By x_in_rhs it holds that 
  (x ∈ Countable_union C ∧ x ∈ B) (x_in_CU_and_B).
Because x_in_CU_and_B both x_in_CU and x_in_B. 
Choose n such that x_in_Cn according to x_in_CU. 
It holds that (x ∈ C n ∧ x ∈ B) (x_in_Cn_and_B). 
By x_in_Cn_and_B it holds that 
  (x ∈ ((C n) ∩ B)) (x_in_CnB). 
It holds that (x ∈ (seq_intersection C B n)) (x_in_seq_n). 
It follows that (x ∈ Countable_union (seq_intersection C B)). 
Qed.


Lemma H_is_λ_system : 
  ∀ Π : setOfSubsets U, Π is_a_π-system
    ⇒ ∀ B : subset U, B ∈ (λ(Π)) 
      ⇒ (H B (λ(Π))) is_a_λ-system.

Proof. 
Take Π : (setOfSubsets U); Assume Π_is_a_π_system.
Take B : (subset U); Assume B_in_λΠ. 
Define H := (H B (λ(Π))). 
We need to show that (full_set_in_set H 
  ∧ complement_in_set H 
    ∧ closed_under_disjoint_countable_union H). 
split.

We claim that (Ω ∩ B ∈ λ(Π)) (omega_int_B_in_λΠ). 
By intersection_full it holds that 
  (Ω ∩ B = B) (omega_int_B_is_B). 
Write goal using (Ω ∩ B = B) as (B ∈ λ(Π)). 
It holds that (B ∈ (λ(Π))). 
It follows that (full_set_in_set H). 

split. 
We need to show that (∀ A : subset U,
  A ∈ H ⇒ (Ω \ A) ∈ H). 
Take A : (subset U); Assume A_in_H.
We claim that (((A ∩ B) ∪ (Ω \ B)) ∈ λ(Π)) (union_in_λΠ). 
Apply disj_union_in_λ_system. 
By generated_system_is_λ it holds that 
  ((λ(Π)) is_a_λ-system) (xx). 
Apply xx. 
It holds that (A ∩ B ∈ λ(Π)).
It holds that (Ω \ B ∈ λ(Π)). 
By intersection_and_complement_disjoint it holds that 
  (Disjoint _ (A ∩ B) (Ω \ B)) (xx).
Apply xx. 

It holds that ((Ω \ ((A ∩ B) ∪ (Ω \ B))) ∈ λ(Π)) (comp_in_λΠ).
By complement_as_union_intersection it holds that 
  ((Ω \ ((A ∩ B) ∪ (Ω \ B))) = (Ω \ A) ∩ B) (to_int).
Write comp_in_λΠ using 
  ((Ω \ ((A ∩ B) ∪ (Ω \ B))) = (Ω \ A) ∩ B)
    as ((Ω \ A) ∩ B ∈ λ(Π)). 
By comp_in_λΠ it holds that ((Ω \ A) ∈ H) (xx).
Apply xx.  

We need to show that (∀ C : ℕ ⇨ set,
  (∀ m n : ℕ, m ≠ n ⇒ Disjoint U (C m) (C n)) 
    ⇒ (∀ n : ℕ, C n ∈ H) 
      ⇒ Countable_union C ∈ H). 
Take C : (ℕ ⇨ subset U). 
Assume all_Cn_disjoint; Assume all_Cn_in_H. 
By all_Cn_in_H it holds that 
  (∀ n : ℕ, ((C n) ∩ B) ∈ λ(Π)) (all_CnB_in_λΠ).
By C_int_B_disjoint it holds that 
  (∀ m n : ℕ, m ≠ n ⇒ Disjoint _ 
    (seq_intersection C B m) 
      (seq_intersection C B n)) (all_CnB_disjoint). 
We claim that (Countable_union (seq_intersection C B) ∈ λ(Π)) (CU_in_λΠ).
By generated_system_is_λ it holds that 
  ((λ(Π)) is_a_λ-system) (λΠ_is_λ).
By λΠ_is_λ it holds that 
  (closed_under_disjoint_countable_union (λ(Π))) (λΠ_closed_under_CU). 
It follows that (Countable_union (seq_intersection C B) ∈ (λ( Π))). 
By CU_seq_int_is_CU_int it holds that 
  (Countable_union (seq_intersection C B) = (Countable_union C) ∩ B) (CUs_equal).
Write CU_in_λΠ using 
  (Countable_union (seq_intersection C B) = (Countable_union C) ∩ B)
    as ((Countable_union C) ∩ B ∈ (λ( Π))). 
It follows that (Countable_union C ∈ H). 
Qed.


Lemma Π_subset_H : 
  ∀ Π : setOfSubsets U, Π is_a_π-system
    ⇒ ∀ B : subset U, B ∈ Π
        ⇒ Π ⊂ H B (λ(Π)).

Proof. 
Take Π : (setOfSubsets U); Assume Π_is_π_system.
Take B : (subset U); Assume B_in_Π. 
We need to show that (∀ C : subset U,
  C ∈ Π ⇒ C ∈ H B (λ( Π))).
Take C : (subset U); Assume C_in_Π.
By Π_is_π_system it holds that 
  (C ∩ B ∈ Π) (CB_in_Π).
It follows that (C ∈ H B (λ(Π))). 
Qed. 


Lemma int_in_λΠ : 
  ∀ Π : setOfSubsets U, Π is_a_π-system
    ⇒ ∀ A : subset U, A ∈(λ(Π))
      ⇒ ∀ B : subset U, B ∈ Π
        ⇒ (A ∩ B) ∈ (λ(Π)).

Proof. 
Take Π : (setOfSubsets U); Assume Π_is_π_system.
Take A : (subset U); Assume A_in_λΠ. 
Take B : (subset U); Assume B_in_Π. 
It holds that (B ∈ λ(Π)) (B_in_λΠ). 
By H_is_λ_system it holds that 
  ((H B (λ(Π))) is_a_λ-system) (H_is_λ_system).
By Π_subset_H it holds that 
  (Π ⊂ H B (λ(Π))) (Π_subs_H).
It holds that (λ(Π) ⊂ H B (λ(Π))) (λΠ_subs_H).
It holds that (A ∈ H B (λ(Π))) (A_in_H). 
It follows that ((A ∩ B) ∈ λ(Π)). 
Qed. 


Lemma λΠ_is_σ_algebra : 
  ∀ Π : setOfSubsets U, Π is_a_π-system
    ⇒ λ(Π) is_a_σ-algebra.

Proof. 
Take Π : (setOfSubsets U).
Assume Π_is_π_system.
We claim that (λ(Π) is_a_π-system) (λΠ_is_π). 
We need to show that (
  ∀ A : subset U, A ∈ (λ(Π)) 
    ⇒ ∀ B : subset U, B ∈ (λ(Π))
      ⇒ (A ∩ B) ∈ (λ(Π))).
Take A : (subset U); Assume A_in_λΠ. 
Take B : (subset U); Assume B_in_λΠ. 
We claim that (Π ⊂ H B (λ(Π))) (Π_subs_H).
We need to show that 
  (∀ C : subset U, C ∈ Π ⇒ C ∈ H B (λ(Π))). 
Take C : (subset U); Assume C_in_Π. 
By int_in_λΠ it holds that 
  ((B ∩ C) ∈ λ(Π)) (BC_in_λΠ). 
By intersection_symmetric it holds that 
  (B ∩ C = C ∩ B) (CB_is_BC). 
Write BC_in_λΠ using (B ∩ C = C ∩ B)
  as ((C ∩ B) ∈ λ(Π)). 
It follows that (C ∈ H B (λ(Π))).

By H_is_λ_system it holds that 
  ((H B (λ(Π))) is_a_λ-system) (H_is_λ_system).
It holds that (λ(Π) ⊂ H B (λ(Π))) (λΠ_subs_H).
It holds that (A ∈ H B (λ(Π))) (A_in_H). 
It follows that ((A ∩ B) ∈ (λ(Π))). 
By generated_system_is_λ it holds that 
  (λ(Π) is_a_λ-system) (λΠ_is_λ). 
By π_and_λ_is_σ it holds that 
  ((λ(Π)) is_a_σ-algebra) (xx).
Apply xx. 
Qed. 


Theorem π_λ_theorem : 
  ∀ Π Λ : setOfSubsets U, 
    Π is_a_π-system ∧ Λ is_a_λ-system ∧ Π ⊂ Λ
    ⇒ (σ(Π)) ⊂ Λ. 

Proof. 
Take Π : (setOfSubsets U); Take Λ : (setOfSubsets U). 
Assume Π_Λ_included_systems. 

We need to show that (∀ x : subset U,
  x ∈ (σ(Π)) ⇒ x ∈ Λ). 
Take A : (subset U); Assume A_in_σΠ.
By Π_Λ_included_systems it holds that 
  (Π is_a_π-system) (Π_is_π). 
By λΠ_is_σ_algebra it holds that 
  (λ(Π) is_a_σ-algebra) (λΠ_is_σ_algebra).
By A_in_σΠ it holds that 
  (∀ F : setOfSubsets U, 
    F is_a_σ-algebra ⇒ Π ⊂ F 
      ⇒ A ∈ F) (A_in_all_σ).
It holds that 
  (λ(Π) is_a_σ-algebra 
    ⇒ Π ⊂ (λ(Π))) (Π_in_λΠ). 
By A_in_all_σ it holds that 
  (A ∈(λ(Π))) (A_in_λΠ). 
It holds that (Λ is_a_λ-system ⇒ Π ⊂ Λ) (Π_in_Λ). 
It holds that (A ∈ Λ). 
Qed. 