(*Version 1.2.1 - 24-04-2020
  Progress in inductive steps in CU_sets_disjointsets_equal
*)
Require Import Sets.Ensembles.
Require Import Sets.Classical_sets.
Require Import wplib.Tactics.Tactics.
Require Import wplib.Tactics.TacticsContra.
Require Import Sets.Powerset.
Require Import Coq.Logic.Classical_Pred_Type. 

Add LoadPath "../". (*import v-file from same directory*)
(*Require Import trivial_sigma_algebra.v. *)

Variable U : Type.

Notation "∅" := 
  (Empty_set U). 

Notation "'Ω'" := 
  (Full_set U) (at level 0). 

Tactic Notation "We" "prove" "equality" "by" "proving" "two" "inclusions" :=
   apply Extensionality_Ensembles; 
   unfold Same_set; 
   unfold Included;
   split.

Notation "x ∩ y" := 
  (Intersection _ x y) (at level 50). (*change level if brackets occur in wrong places*)

Notation "x ∪ y" := 
  (Union _ x y) (at level 50). 


Notation "x \ y" := 
  (Setminus _ x y) (at level 50). 

Notation "x ∈ A" := 
  (In _ A x) (at level 50). 

Notation "x ⊂ y" := 
  (Included _ x y) (at level 50). 

Tactic Notation "We" "prove" "by" "induction" "on" ident(x) := 
  induction x. 
(*Not nicest formulation, but 'Proof' is already taken*)

Hint Resolve Full_intro : measure_theory.  (*nieuwe database measure theory*)
Hint Resolve Intersection_intro : measure_theory. 

Definition is_π_system (Π : Ensemble (Ensemble U)) 
  : Prop := 
    ∀ A : Ensemble U, A ∈ Π ⇒ 
      ∀ B : Ensemble U, B ∈ Π ⇒ 
         (A ∩ B) ∈ Π. 

Definition Countable_union (A : (ℕ → Ensemble U)) 
  : Ensemble U := 
    fun (x:U) ↦ ∃n : ℕ, x ∈ (A n).

Definition full_set_in_set (Λ : Ensemble (Ensemble U)) 
  : Prop :=
    Ω ∈ Λ. 

Definition complement_in_set (Λ : Ensemble (Ensemble U)) 
  : Prop := 
    ∀A  : Ensemble U, A ∈ Λ 
      ⇒ (Ω \ A) ∈ Λ. 

Definition closed_under_disjoint_countable_union (Λ : Ensemble (Ensemble U)) 
  : Prop :=
    ∀C : (ℕ → (Ensemble U)), 
      (∀ m n : ℕ, m ≠ n ⇒ Disjoint _ (C m) (C n)) 
        ⇒ (∀ n : ℕ, (C n) ∈ Λ) ⇒  (Countable_union C) ∈ Λ.

Definition closed_under_countable_union (Λ : Ensemble (Ensemble U)) 
  : Prop :=  
    ∀C : (ℕ → (Ensemble U)), (∀ n : ℕ, (C n) ∈ Λ) 
      ⇒ (Countable_union C) ∈ Λ.

Definition is_λ_system (Λ : Ensemble (Ensemble U)) 
  : Prop :=
    full_set_in_set Λ ∧ 
    complement_in_set Λ ∧
    closed_under_disjoint_countable_union Λ. 

Definition is_σ_algebra (F : Ensemble (Ensemble U)) 
  : Prop := 
    full_set_in_set F ∧ 
    complement_in_set F ∧
    closed_under_countable_union F.

Definition  σ_algebra_generated_by (A : Ensemble (Ensemble U)) 
  : (Ensemble (Ensemble U)) := 
    fun (B : Ensemble U) ↦ 
    (∀ F : Ensemble (Ensemble U), is_σ_algebra F ⇒ (A ⊂ F ⇒ B ∈ F)). 

Definition restriction (F : Ensemble (Ensemble U)) (A : (Ensemble U)) 
  : (Ensemble (Ensemble U)) := 
    fun (C : Ensemble U) ↦ (exists B : Ensemble U, B ∈ F ⇒ C = A ∩ B). 

Definition finite_union (C : (ℕ ⇨ Ensemble U)) (n : ℕ) 
  : (Ensemble U) := 
    fun (x:U) ↦ (∃i : ℕ,  (i <= n ∧ x ∈ (C n))).
(* ≤ only works for Reals*)

Fixpoint disjoint_seq (C : (ℕ ⇨ Ensemble U)) (n : ℕ) {struct n}
  : (Ensemble U) :=
    match n with 
      0 => C 0 
    | S p => (C (S p)) \ (finite_union C p)
    end. 


Lemma CU_sets_disjointsets_equal : 
  ∀ C : (ℕ ⇨ Ensemble U), 
    Countable_union (disjoint_seq C) = Countable_union C.

Proof. 
Take C : (ℕ ⇨ Ensemble U).
We prove equality by proving two inclusions. 

Take x : U; Assume x_in_CU_disj. 
Choose n0 such that x_in_disj_n according to x_in_CU_disj.
It holds that (x ∈ ((C n0) \ (finite_union C (n0-1))) \/ x ∈ C 0) (xxx). 
It holds that ((disjoint_seq C n0) ⊂ (C n0)) (disj_subs_original). 
It holds that (x ∈ Countable_union C). 

Take x : U; Assume x_in_CU_C.

Choose n0 such that x_in_Cn according to x_in_CU_C. 

We prove by induction on n0. 
(*Base case: *)
It holds that ( (disjoint_seq_sets C) 0 = (C 0) \ ∅) (disj0_is_C0).
By disj0_is_C0 it holds that (x ∈(disjoint_seq_sets C) 0) (x_in_disj0). 
It holds that (x ∈ Countable_union (disjoint_seq_sets C)). 

(*Induction step:*)
By classic it holds that ((x ∈ C n0) ∨ ~(x ∈ C n0)) (in_Cn0_or_not). 
Because in_Cn0_or_not either x_in_Cn0 or x_not_in_Cn0. 
(*x in C_n0: *)
It holds that (x ∈ Countable_union (disjoint_seq_sets C)). 
(*x not in C_n0: *)
By classic it holds that ((x ∈auxiliary_seq C n0) ∨ ~(x ∈ auxiliary_seq C n0)) (in_aux_or_not). 
Because in_aux_or_not either x_in_aux or x_not_in_aux.
 
It holds that (x ∈ C n \ auxiliary_seq C n.


(*Alternative: *)
We argue by contradiction. 
It holds that (forall n : nat, ~(In _ (disjoint_seq_sets C n) x)) (x_in_no_disj).

By x_in_no_disCn it holds that (~ (exists n : nat, (In _ (C n) x))) (x_in_no_Cn).
Contradiction. 


Admitted.  

Lemma complement_as_intersection : 
  ∀ A B : Ensemble U, 
    A \ B = A ∩ (Ω \ B). 

Proof. 
Take A : (Ensemble U); Take B : (Ensemble U). 
We prove equality by proving two inclusions. 

Take x : U. 
Assume x_in_A_without_B. 
It holds that (x ∈ (A ∩ (Ω \ B))). 

Take x : U. 
Assume x_in_rhs. 
By x_in_rhs it holds that ((x ∈ A) ∧ x ∈ (Ω \ B)) (x_in_A_and_comp_B). 
It holds that (x ∈ (A \ B)). 

Qed. 

Lemma complements_in_pi_lambda_system : 
  ∀ F : Ensemble (Ensemble U), 
    is_π_system F ∧ is_λ_system F 
    ⇒ ∀ A B : Ensemble U, A ∈ F ∧ B ∈ F
      ⇒ A \ B ∈ F. 

Proof. 
Take F : (Ensemble (Ensemble U)). 
Assume F_is_π_and_λ_system.
By F_is_π_and_λ_system 
  it holds that (is_π_system F) (F_is_π_system). 
By F_is_π_and_λ_system 
  it holds that (is_λ_system F) (F_is_λ_system). 
Take A : (Ensemble U); Take B : (Ensemble U). 
Assume A_and_B_in_F. 
By F_is_λ_system it holds that (Ω \ B ∈ F) (comp_B_in_F). 
By F_is_π_system it holds that (A ∩ (Ω \ B) ∈ F) (set_in_F). 
By complement_as_intersection it holds that (A \ B = A ∩ (Ω \ B)) (set_is_complement). 
Write goal using (A \ B = A ∩ (Ω \ B)) as ((A ∩ (Ω \ B)) ∈ F). 
It holds that ((A ∩ (Ω \ B)) ∈ F). 

Qed. 


Lemma π_and_λ_is_σ : 
  ∀ F : Ensemble (Ensemble U), 
    is_π_system F ∧ is_λ_system F 
    ⇒ is_σ_algebra F. 

Proof. 
Take F : (Ensemble (Ensemble U)).
Assume F_is_π_and_λ_system. 
By F_is_π_and_λ_system 
  it holds that (is_π_system F) (F_is_π_system). 
By F_is_π_and_λ_system 
  it holds that (is_λ_system F) (F_is_λ_system). 
Expand the definition of is_σ_algebra.
split.
It holds that (full_set_in_set F) .
split.
It holds that (complement_in_set F). 

Expand the definition of closed_under_countable_union. 
Take C : (ℕ ⇨ Ensemble U); Assume all_C_n_in_F. 
By classic it holds that 
  ((∀ m n : ℕ, m ≠ n ⇒ Disjoint _ (C m) (C n)) ∨ 
  ¬(∀ m n : ℕ, m ≠ n ⇒ Disjoint _ (C m) (C n))) (all_or_not_all_disjoint). 
Because all_or_not_all_disjoint either all_disjoint or not_all_disjoint. 

(*Case 1: all C_n disjoint.*) 
It holds that (Countable_union C ∈ F). 

(*Case 2: not all C_n disjoint. *)
(*Newer approach: *)

(*Former approach: *)
By not_all_disjoint it holds that 
  (∃m n : ℕ, m ≠ n 
    ⇨ ¬(Disjoint U (C m) (C n))) (two_not_disjoint). 
Choose m 
  such that one_not_disjoint_with_m 
    according to two_not_disjoint. 
Choose n 
  such that C_m_n_not_disjoint 
    according to one_not_disjoint_with_m.
(*Nu nog m ≠ n? *)
It holds that ((C m) ∈ F ∧ (C n) ∈ F) (C_m_and_C_m_in_F). 
By F_is_π_system it holds that 
  ((Intersection _ (C m) (C n)) ∈ F) (intersection_in_F).
(*Dead end? *)

(* Usual proof method: 
   Let B_n := C_n \ (union i=1 to n-1 of C_i). 
    (or: A_n := A_n-1 ∪ B_n-1, A_0 = empty
         B_n := C_n \ A_n, B_0 = C_0)
   These are in F by F_is_π_system, and their union
   is in F by F_is_λ_system
*)

 
(*Qed. *) Admitted. 

Theorem π_λ_theorem : 
  ∀ Π Λ : Ensemble (Ensemble U), 
    is_π_system Π ∧ is_λ_system Λ ∧ Π ⊂ Λ
    ⇒ (σ_algebra_generated_by Π) ⊂ Λ. 





