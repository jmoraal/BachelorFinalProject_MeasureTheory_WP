(*Version 1.5.5 - 23-04-2020
  new notations 
*)
Require Import Sets.Ensembles.
Require Import Sets.Classical_sets.
Require Import wplib.Tactics.Tactics.
Require Import wplib.Tactics.TacticsContra.
Require Import wplib.Notations.Notations.
Require Import Sets.Powerset.
Require Import Coq.Logic.Classical_Pred_Type. 

Variable U : Type.

Notation "∅" := 
  (Empty_set U). (*Watch out: type Ensemble _, not Ensemble Ensemble _*)

Notation "'Ω'" := 
  (Full_set U). (*Which level to choose for these two?*)

Tactic Notation "We" "prove" "equality" "by" "proving" "two" "inclusions" :=
   apply Extensionality_Ensembles; 
   unfold Same_set; 
   unfold Setminus; 
   unfold Included;
   split.

Notation "x ∩ y" := 
  (Intersection _ x y) (at level 50). (*again, level?*)

Notation "x ∪ y" := 
  (Union _ x y) (at level 50). 


Notation "x \ y" := 
  (Setminus _ x y) (at level 50). 

Notation "x ∈ y" := 
  (In _ y x) (at level 50). 
(*notation already used in 'Notations', but differently*)

Notation "x ⊂ y" := 
  (Included _ x y) (at level 50). 

Definition is_π_system (Π : Ensemble (Ensemble U)) 
  : Prop := 
    ∀ A : Ensemble U, A ∈ Π ⇒ 
      ∀ B : Ensemble U, B ∈ Π ⇒ 
         (A ∩ B) ∈ Π. 
       (*In (Ensemble U) Π (A ∩ B). *)

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
    (∀ F : Ensemble (Ensemble U), (is_σ_algebra F ∧ A ⊂ F) ⇒ B ∈ F). 
(*
Definition restriction (F : Ensemble (Ensemble U)) (A : (Ensemble U)) 
  : (Ensemble (Ensemble U)) := 
    fun (B : Ensemble U) ↦ 
*)
Definition empty_and_full (A : Ensemble U) 
  : Prop := 
    (A = Ω) ∨ (A = ∅).  


Lemma complement_empty_is_full : 
  Ω = (Ω \ ∅). 

Proof. 
We prove equality by proving two inclusions. 
Take x : U; Assume x_in_full. 
It holds that (In U Ω x ∧ ¬ In U ∅ x).

Take x : U; Assume x_in_complement_empty.
Because x_in_complement_empty both x_in_full and not_x_in_empty. 
It holds that (In _ Ω x). 
Qed. 


Lemma complement_full_is_empty : 
  ∅ = (Ω \ Ω). 

Proof. 
We prove equality by proving two inclusions. 
Take x : U; Assume x_in_empty.
contradiction. 

Take x : U; Assume x_in_complement_full.
Because x_in_complement_full 
  both x_in_full and not_x_in_full. 
contradiction. 
Qed.


Lemma trivial_salgebra : is_σ_algebra empty_and_full. 

Proof. 
Expand the definition of is_σ_algebra. 
split. 

(* First point: Prove that Omega is in empty_and_full *)
It holds that (full_set_in_set empty_and_full). 
split.

(* Second point: Prove that empty_and_full is closed under complement*)
Expand the definition of complement_in_set. 
Take A : (Ensemble U). 
Assume A_in_F : (A ∈ empty_and_full). 
Write A_in_F as ( (A = Ω) 
  ∨ (A = ∅) ).
Because A_in_F either A_is_full or A_is_empty. 
rewrite -> A_is_full. 
(*does the same as: 
  Write goal using (A = Ω) as 
    (In (Ensemble U) empty_and_full (Ω \ Ω)). 
  Could use Write goal as ..., but becomes very long. What to do?
*) 
replace (Ω \ Ω) 
  with ∅. (*alternative from WPlib?*)
It holds that (∅ ∈ empty_and_full). 
Apply complement_full_is_empty. 

rewrite -> A_is_empty. 
replace (Ω \ ∅) 
  with Ω. 
It holds that (Ω ∈ empty_and_full). 
Apply complement_empty_is_full. 

(* Third point: Prove that empty_and_full is closed under countable union*)
Expand the definition of closed_under_countable_union. 
Take C : (ℕ → (Ensemble U)). 
Assume C_n_in_empty_and_full.
By classic it holds that ((∀ n : ℕ, (C n) = ∅) 
  ∨ ¬(∀ n : ℕ, (C n) = ∅)) (all_or_not_all_empty). 
Because all_or_not_all_empty 
  either all_empty or not_all_empty. 
It suffices to show that (Countable_union C = ∅). 
We prove equality by proving two inclusions. 

Expand the definition of Countable_union. 
Take x : U; Assume x_in_countable_union_C. 
Choose n such that x_in_C_n according to x_in_countable_union_C. 
Write x_in_C_n using (C n = ∅) as (∅ x).
It holds that (x ∈ ∅). 

Take x : U; Assume x_in_empty. 
Contradiction. 


It suffices to show that (Countable_union C = Ω). 
We prove equality by proving two inclusions. 
Take x : U; Assume x_in_countable_union_C. 
Choose n0 such that x_in_C_n0 
   according to x_in_countable_union_C. 
It holds that ((C n0 = Ω)
   ∨ (C n0 = ∅)) (C_n0_empty_or_full). 
Because C_n0_empty_or_full either C_n0_full or C_n0_empty. 
Write goal using (Ω = C n0) 
  as (x ∈ C n0). 
(*rewrite <- C_n0_full. *)
Apply x_in_C_n0. 
Write x_in_C_n0 using (C n0 = ∅) 
  as (∅ x).
Contradiction. 
(*of ook: It holds that (In U Ω x). Uit iets onwaars kan alles volgen. *)

By not_all_empty it holds that 
  (∃n : ℕ, ¬ (C n = ∅)) (one_not_empty). 
By C_n_in_empty_and_full it holds that 
  (∃n : ℕ, (C n = Ω)) (one_full).
Choose n1 such that C_n1_full according to one_full. 
rewrite <- C_n1_full. 
It holds that ((C n1) ⊂ (Countable_union C)). 
Qed. 

Inductive auxiliary_seq (C : (ℕ ⇨ Ensemble U)) 
  : (ℕ ⇨ Ensemble U) := 
    | aux_first : (auxiliary_seq C) 1 = ∅ 
    | aux_ind : ∀ n : ℕ, (auxiliary_seq C) n = (C n) ∪ ((auxiliary_seq C) (n-1)). 

(* Waarom werkt deze niet? Vergelijk met deze: 
   Inductive Couple (x y:U) : Ensemble :=
    | Couple_l : In (Couple x y) x
    | Couple_r : In (Couple x y) y.
*)

Inductive make_disjoint_seq_sets (C : (ℕ ⇨ Ensemble U)) 
  : (ℕ ⇨ Ensemble U) := 
    | first_set : (make_disjoint_seq_sets C 1 = C 0) 
    | induction_sets : ∀ n : ℕ, make_disjoint_seq_sets C n = (C n) \ (auxiliary_seq C n). 

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
(*It holds that (closed_under_disjoint_countable_union F) (F_closed_under_disjoint). 
Expand the definition of 
  closed_under_disjoint_countable_union 
    in F_closed_under_disjoint. *)
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





