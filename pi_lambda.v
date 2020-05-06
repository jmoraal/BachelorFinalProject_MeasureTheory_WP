(*Version 1.4.3 - 06-05-2020
  CU_sets_disjointsets_equal proven using minimal n
  
*)
Require Import Sets.Ensembles.
Require Import Sets.Classical_sets.
Require Import wplib.Tactics.Tactics.
Require Import wplib.Tactics.TacticsContra.
Require Import Sets.Powerset.
Require Import Coq.Logic.Classical_Pred_Type. 
Require Import ClassicalFacts. 
Require Import Omega. 
Require Import Coq.Arith.Wf_nat. 

Add LoadPath "../". (*import v-file from same directory*)
(*Require Import trivial_sigma_algebra.v. *)

Variable U : Type.
(*notations for generated sigma-alg and lambda-syst?*)
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

Tactic Notation "Let" ident(A) "be" "a" "set" := 
  Take A : (set).

Tactic Notation "Let" ident(F) "be" "a" "set" "of" "sets" := 
  Take A : (setOfSets).

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

(* 
Fixpoint disjoint_seq (C : (ℕ ⇨ set)) (n : ℕ) {struct n}
  : (set) :=
    match n with 
      0 => C 0 
    | S p => (C (S p)) \ (finite_union C p)
    end. 
*)

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


Lemma complement_empty : 
  ∀ A : set, A \ ∅ = A. 

Proof. 
Take A : (set). 
We prove equality by proving two inclusions.
Take x : U; Assume x_in_A_wo_empty. 
It holds that (x ∈ A). 

Take x : U; Assume x_in_A. 
It holds that (x ∈ (A \ ∅)). 
Qed. 


Lemma intersection_full : ∀A : set, 
  (Ω ∩ A) = A. 

Proof. 
Take A : (set). 
We prove equality by proving two inclusions. 
Take x : U; Assume x_in_intersection. 
destruct x_in_intersection. 
It holds that (x ∈ A). 

Take x : U; Assume x_in_A. 
It holds that (x ∈ Ω) (x_in_omega). 
It follows that (x ∈ (Ω ∩ A)). 
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
Take A : (set); Take B : (set). 
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
Expand the definition of finite_union_up_to in x_in_FU_0. 
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
Take m : ℕ; Take n : ℕ. (*tactic voor 2 in een keer?*)
Assume m_neq_n.
By neq_equiv it holds that 
  (m ≠ n ⇒ (m < n) ∨ (m > n)) (m_l_g_n).
It holds that ((m < n) ∨ (m > n)) (m_lg_n). 
We argue by contradiction. 
It holds that (exists x: U, 
  x ∈ ((disjoint_seq C m) ∩ (disjoint_seq C n))) (int_not_empty).
Choose x such that x_in_int according to int_not_empty.
By x_in_int it holds that 
  (x ∈ disjoint_seq C m 
    ∧ x ∈ disjoint_seq C n) (x_in_m_and_n). 
By x_in_m_and_n it holds that (x ∈ disjoint_seq C m) (x_in_m). 
By x_in_m_and_n it holds that (x ∈ disjoint_seq C n) (x_in_n). 
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

Definition aux_prop (C : (ℕ ⇨ set)) (x : U) : 
  ℕ ⇨ Prop := 
    fun (n : ℕ) ↦ (x ∈ C n). 

Lemma CU_sets_disjointsets_equal : 
  ∀ C : (ℕ ⇨ set), 
    Countable_union (disjoint_seq C) = Countable_union C.

Proof. 
Take C : (ℕ ⇨ set).
We prove equality by proving two inclusions. 

(* CU disjoint sets in CU C: *)
Take x : U; Assume x_in_CU_disj. 
It holds that (x ∈ Countable_union C). 


(* CU C in CU disjoint sets: *)
Take x : U; Assume x_in_CU_C. 
(*now choose minimal n such that x is in disj_C n*)
Choose n such that x_in_C_n according to x_in_CU_C.
By classic it holds that 
  (∀ n, (aux_prop C x) n ∨ ¬(aux_prop C x) n) (aux_prop_decidable). 
By dec_inh_nat_subset_has_unique_least_element it holds that
  (has_unique_least_element le (aux_prop C x)) (exists_least_n). 
Choose n1 such that x_in_C_minimal_n according to exists_least_n. 

We prove by induction on n1. 

(*Base case: *)
It holds that (x ∈ Countable_union (disjoint_seq C)). 
(*Induction step: *)
It holds that (x ∈ Countable_union (disjoint_seq C)). 
Qed. 


Lemma complement_as_intersection : 
  ∀ A B : set, 
    A \ B = (Ω \ B) ∩ A. 

Proof. 
Take A : (set); Take B : (set). 
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
  ∀ F : setOfSets, 
    F is_a_π-system ∧ F is_a_λ-system
    ⇒ ∀ A B : set, A ∈ F ∧ B ∈ F
      ⇒ A \ B ∈ F. 

Proof. 
Take F : (setOfSets). 
Assume F_is_π_and_λ_system.
By F_is_π_and_λ_system 
  it holds that (F is_a_π-system) (F_is_π_system). 
By F_is_π_and_λ_system 
  it holds that (F is_a_λ-system) (F_is_λ_system). 
Take A : (set); Take B : (set). 
Assume A_and_B_in_F. 
By F_is_λ_system it holds that (Ω \ B ∈ F) (comp_B_in_F). 
By F_is_π_system it holds that (A ∩ (Ω \ B) ∈ F) (set_in_F). 
By complement_as_intersection it holds that 
  (A \ B = (Ω \ B) ∩ A) (set_is_complement). 
Write goal using (A \ B = ((Ω \ B) ∩ A)) as (((Ω \ B) ∩ A) ∈ F). 
It holds that (((Ω \ B) ∩ A) ∈ F). 

Qed. 


Lemma union_as_complements : 
  ∀ A B : set, 
    (A ∪ B) = (Ω \ ((Ω \ A) ∩ (Ω \ B))). 

Proof. 
Take A : (set); Take B : (set). 
We prove equality by proving two inclusions. 
Take x : U; Assume x_in_union. 
By union_to_or it holds that (x ∈ A ∨ x ∈ B) (x_in_A_or_B). 
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
  ∀ F : setOfSets, 
    F is_a_π-system ⇒ F is_a_λ-system
    ⇒ ∀ A B : set, A ∈ F ⇒ B ∈ F
      ⇒ A ∪ B ∈ F.

Proof. 
Take F : (setOfSets). 
Assume F_is_π_system; Assume F_is_λ_system. 
Take A : (set); Take B : (set). 
Assume A_in_F; Assume B_in_F.

By union_as_complements it holds that 
  ((A ∪ B) = (Ω \ ((Ω \ A) ∩ (Ω \ B)))) (union_is_comp). 
Write goal using 
  ((A ∪ B) = (Ω \ ((Ω \ A) ∩ (Ω \ B)))) 
    as ((Ω \ ((Ω \ A) ∩ (Ω \ B))) ∈ F). 
By F_is_λ_system it holds that ((Ω \ A) ∈ F) (comp_A_in_F). 
By F_is_λ_system it holds that ((Ω \ B) ∈ F) (comp_B_in_F). 
By F_is_π_system it holds that 
  ((Ω \ A) ∩ (Ω \ B) ∈ F) (int_in_F). 
It holds that ((Ω \ ((Ω \ A) ∩ (Ω \ B))) ∈ F). 
Qed. 
 

Lemma empty_in_λ : 
  ∀ F : setOfSets, 
    F is_a_λ-system ⇒ ∅ ∈ F. 

Proof.  
Take F : (setOfSets); Assume F_is_λ_system. 
By complement_full_is_empty it holds that 
  (∅ = (Ω \ Ω)) (comp_full_empty).
Write goal using (∅ = (Ω \ Ω)) as ((Ω \ Ω) ∈ F). 
It holds that ((Ω \ Ω) ∈ F). 
Qed.  


Lemma FU_S_as_union : 
  ∀C : (ℕ → (set)), ∀n : ℕ,
    finite_union_up_to C (S n) 
      = (finite_union_up_to C n) ∪ (C n). 

Proof. 
Take C : (ℕ → (set)). 
Take n : ℕ. 
We prove equality by proving two inclusions. 
Take x : U; Assume x_in_FU_S. 
Choose n0 such that x_in_C_n0 according to x_in_FU_S.
It holds that (n0 <= n) (n0_le_n). (*avoid %nat? *) 
By leq_equiv it holds that (n0 < n ∨ n0 = n) (n0_l_e_n).
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
  ∀ F : setOfSets, 
    F is_a_π-system ⇒ F is_a_λ-system
    ⇒ ∀C : (ℕ → (set)), (∀ n : ℕ, (C n) ∈ F) 
      ⇒ ∀n : ℕ, (finite_union_up_to C n) ∈ F.

Proof. 
Take F : (setOfSets). 
Assume F_is_π_system.
Assume F_is_λ_system.  
Take C : (ℕ ⇨ set). 
Assume all_Cn_in_F.
Take n : ℕ. 

We prove by induction on n.
(* Base case: *)
By FU_up_to_0_empty it holds that 
  (finite_union_up_to C 0 = ∅) (FU0_is_empty). 
Write goal using (finite_union_up_to C 0 = ∅) as (∅ ∈ F). 
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
By unions_in_π_and_λ it holds that ((finite_union_up_to C n ∪ C n) ∈ F) (xx). 
Apply xx. 

Qed. 


Lemma π_and_λ_is_σ : 
  ∀ F : setOfSets, 
    F is_a_π-system ⇒ F is_a_λ-system 
      ⇒ F is_a_σ-algebra. 

Proof. 
Take F : (setOfSets).
Assume F_is_π_system. 
Assume F_is_λ_system. 
It holds that 
  (closed_under_disjoint_countable_union F) (cu_disj_CU). 
(*Somehow doesn't work later, tactic time-out. Too much in environment?*)
Expand the definition of is_σ_algebra.
split.
It holds that (full_set_in_set F) .
split.
It holds that (complement_in_set F). 

Expand the definition of closed_under_countable_union. 
Take C : (ℕ ⇨ set); Assume all_C_n_in_F. 
By classic it holds that 
  ((∀ m n : ℕ, m ≠ n ⇒ Disjoint _ (C m) (C n)) ∨ 
  ¬(∀ m n : ℕ, m ≠ n ⇒ Disjoint _ (C m) (C n))) (all_or_not_all_disjoint). 
Because all_or_not_all_disjoint either all_disjoint or not_all_disjoint. 

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
(*By F_is_λ_system it holds that 
  (closed_under_disjoint_countable_union F) (CU_disj_CU2). Doesn't work here*)
It holds that (Countable_union (disjoint_seq C) ∈ F).
Qed. 
 

Definition λ_system_generated_by (A : setOfSets) 
  : (setOfSets) := 
    {B : set | (∀ Λ : setOfSets, Λ is_a_λ-system 
       ⇒ (A ⊂ Λ ⇒ B ∈ Λ))}. 

Notation "λ( A )" := 
 (λ_system_generated_by A) (at level 50). 
 
Lemma generated_system_is_λ : 
  ∀ A : setOfSets, 
    λ(A) is_a_λ-system.

Proof. 
Take A : (setOfSets). 
Expand the definition of is_λ_system. (*write goal as*)
It holds that (∀ Λ : setOfSets, 
  Λ is_a_λ-system ⇒ (full_set_in_set Λ)
    ∧ complement_in_set Λ
      ∧ closed_under_disjoint_countable_union Λ) 
        (lambda_props_for_all). 
split. 
It follows that (full_set_in_set (λ(A))). 
split. 
It follows that (complement_in_set (λ(A))). 

Expand the definition of 
  closed_under_disjoint_countable_union. 
Take C : (ℕ ⇨ set). 
Assume all_Cn_disjoint. 
Assume all_Cn_in_λA.

We claim that (∀ Λ : setOfSets, 
  Λ is_a_λ-system ⇒ A ⊂ Λ 
    ⇒ (Countable_union C) ∈ Λ) (CU_in_all).
Take Λ : (setOfSets). 
Assume Λ_is_λ_system. 
Assume A_subs_Λ. 
It holds that 
  (closed_under_disjoint_countable_union Λ) 
    (closed_under_disj_CU). 
Expand the definition of 
  closed_under_disjoint_countable_union 
    in closed_under_disj_CU. 
It holds that (
  (∀ m n : ℕ, m ≠ n ⇨ Disjoint U (C m) (C n))  
    ⇒ ∀ n : ℕ, C n ∈ Λ) (disj_implies_all_Cn_in_Λ).
It follows that (Countable_union C ∈ Λ). 
It follows that (Countable_union C ∈ λ(A)). 
Qed.

(*global variables? As not to re-define Π and others each time. *)
(*yes, with 'Variable;*)
Fixpoint aux_seq (A B : set) (n : ℕ) {struct n}
  : (set) :=
    match n with 
      0 => A 
    | 1 => B
    | n => ∅ 
    end. 

Lemma geq_equiv : ∀ x y : ℕ,
  (x >= y) ⇒ (x = y ∨ x > y).

Proof. 
intros x y. omega. 
Qed. 

Lemma CU_aux_is_union : 
  ∀ A B : set, Countable_union (aux_seq A B) = A ∪ B. 

Proof. 
Take A : (set); Take B : (set). 
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
Expand the definition of Countable_union. 
It holds that (∃ n : nat, x ∈ aux_seq A B n) (exists_n_A). 
It follows that (x ∈ Countable_union (aux_seq A B)).

It holds that (x ∈ aux_seq A B 1) (x_in_aux0). 
Expand the definition of Countable_union. 
It holds that (∃ n : nat, x ∈ aux_seq A B n) (exists_n_B). 
It follows that (x ∈ Countable_union (aux_seq A B)).
Qed. 

Lemma disjoint_aux : 
  ∀ A B : set, (Disjoint _ A B) 
    ⇒ (∀ m n : ℕ, m ≠ n ⇒ Disjoint _ (aux_seq A B m) (aux_seq A B n)). 

Proof. 
Take A : (set); Take B : (set). 
Assume A_B_disjoint. 
Take m : ℕ; Take n : ℕ. 
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


Admitted. 


Lemma disj_union_in_λ_system : 
  ∀ Λ : setOfSets, Λ is_a_λ-system
    ⇒ ∀ A B : set, A ∈ Λ ⇒ B ∈ Λ 
      ⇒ Disjoint _ A B ⇒ A ∪ B ∈ Λ. 

Proof. 
Take Λ : (setOfSets); Assume Λ_is_a_λ_system. 
Take A : (set); Take B : (set). 
Assume A_in_Λ; Assume B_in_Λ. 
Assume A_B_disjoint. 

We claim that (∀ n : ℕ, aux_seq A B n ∈ Λ) (all_aux_in_Λ). 
Take n : ℕ. 
We prove by induction on n. 
It holds that (aux_seq A B 0 ∈ Λ). 
We prove by induction on n. (*0 and 1 defined, rest inductively. Other way? *)
It holds that (aux_seq A B 1 ∈ Λ). 
Write goal using (aux_seq A B (S (S n)) = ∅) as (∅ ∈ Λ). 
By empty_in_λ it holds that (∅ ∈ Λ) (empty_in_Λ).
Apply empty_in_Λ.  

By CU_aux_is_union it holds that 
  (A ∪ B = Countable_union (aux_seq A B)) (union_to_CU). 
Write goal using (A ∪ B = Countable_union (aux_seq A B))
  as (Countable_union (aux_seq A B) ∈ Λ). 

By disjoint_aux it holds that 
  (∀ m n : ℕ, m ≠ n ⇒ Disjoint _ (aux_seq A B m) (aux_seq A B m)) (aux_disjoint).
By Λ_is_a_λ_system it holds that 
  (closed_under_disjoint_countable_union Λ) (closed_under_disj_CU). 
Expand the definition of closed_under_disjoint_countable_union in closed_under_disj_CU. 
It holds that ((∀ m n : ℕ, m ≠ n ⇒ Disjoint U (aux_seq A B m) (aux_seq A B n))
    ⇒ (for all n : ℕ, aux_seq A B n ∈ Λ)) (props_cu_disj_CU). 
(*By closed_under_disj_CU it holds that ((Countable_union (aux_seq A B)) ∈ Λ) (xx). *)

Admitted. 

Definition H (B : set) (λΠ : setOfSets)
  : setOfSets := 
    {A : (set) | (A ∩ B ∈ λΠ) }. 

Lemma H_is_λ_system : 
  ∀ Π : setOfSets, Π is_a_π-system
    ⇒ ∀ B : set, B ∈ (λ(Π)) 
      ⇒ (H B (λ(Π))) is_a_λ-system.

Proof. 
Take Π : (setOfSets); Assume Π_is_a_π_system.
Take B : (set); Assume B_in_λΠ. 
Expand the definition of is_λ_system. 
split.

We claim that (Ω ∩ B ∈λ(Π)) (omega_int_B_in_λΠ). 
By intersection_full it holds that 
  (Ω ∩ B = B) (omega_int_B_is_B). 
Write goal using (Ω ∩ B = B) as (B ∈ λ(Π)). 
This follows immediately. 
It follows that (full_set_in_set (H B (λ(Π)))). 
split. 
Expand the definition of complement_in_set. 
Take A : (set); Assume A_in_H.
It holds that (A ∩ B ∈λ(Π)) (A_int_B_in_λΠ). 


Admitted. 

Lemma int_in_λΠ : 
  ∀ Π : setOfSets, Π is_a_π-system
    ⇒ ∀ A : set, A ∈(λ(Π))
      ⇒ ∀ B : set, B ∈ Π
        ⇒ (A ∩ B) ∈ (λ(Π)).

Proof. 

Admitted. 


Lemma λΠ_is_σ_algebra : 
  ∀ Π : setOfSets, Π is_a_π-system
    ⇒ λ(Π) is_a_σ-algebra.
(*Suffices to show that λ(Π) is a π-system *)
Proof. 
Take Π : (setOfSets).
Assume Π_is_π_system. 
(*
We claim that (λ(Π) is_a_π-system) (λΠ_is_π_system). 
We need to show that (∀ A : set, A ∈ (λ(Π)) ⇒ 
      ∀ B : set, B ∈ (λ(Π)) ⇒ 
         (A ∩ B) ∈ (λ(Π))).
Take A : (set). 
Assume A_in_λΠ. 
Take B : (set). 
Assume B_in_λΠ.

By classic it holds that (B ∈ Π ∨ B ∉ Π) (B_in_Π_or_not).
Because B_in_Π_or_not either B_in_Π or B_not_in_Π. 
(* B ∈ Π *)
By int_in_λΠ it holds that ((A ∩ B) ∈ λ(Π)) (xx). (*extra tactic so that this can conclude proof?*) 
This follows immediately. 

(* B ∉ Π *)
*)

Admitted. 

Theorem π_λ_theorem : 
  ∀ Π Λ : setOfSets, 
    Π is_a_π-system ∧ Λ is_a_λ-system ∧ Π ⊂ Λ
    ⇒ (σ(Π)) ⊂ Λ. 

Proof. 
Take Π : (setOfSets); Take Λ : (setOfSets). 
Assume Π_Λ_included_systems. 

Expand the definition of Included. 
Take A : (set); Assume A_in_σΠ.
By Π_Λ_included_systems it holds that (Π is_a_π-system) (Π_is_π). 
By λΠ_is_σ_algebra it holds that (λ(Π) is_a_σ-algebra) (λΠ_is_σ_algebra).
By A_in_σΠ it holds that 
  (∀ F : setOfSets, 
    F is_a_σ-algebra ⇨ Π ⊂ F 
      ⇨ A ∈ F) (A_in_all_σ).
It holds that 
  (λ(Π) is_a_σ-algebra 
    ⇨ Π ⊂ (λ(Π))) (Π_in_λΠ). 
By A_in_all_σ it holds that (A ∈(λ(Π))) (A_in_λΠ). 
It holds that (Λ is_a_λ-system ⇒ Π ⊂ Λ) (Π_in_Λ). 
It holds that (A ∈ Λ). 
Qed. 