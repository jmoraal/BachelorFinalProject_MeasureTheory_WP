(*Version 1.5.6 - 23-04-2020
  Lemma's for pi&lambda => sigma moved to other file. 
  U as universe, so that Om = full set (already in previous versions)
*)
Require Import Sets.Ensembles.
Require Import Sets.Classical_sets.
Require Import wplib.Tactics.Tactics.
Require Import wplib.Tactics.TacticsContra.
Require Import Sets.Powerset.
Require Import Coq.Logic.Classical_Pred_Type. 

Variable U : Type. 

Notation "∅" := 
  (Empty_set U). 
(*Watch out: type Ensemble _, not Ensemble Ensemble _. 
  But the latter is (almost) never needed, 
  so this difference should not cause problems. *)

Notation "'Ω'" := 
  (Full_set U) (at level 0). (*Which level to choose for these two?*)

Tactic Notation "We" "prove" "equality" "by" "proving" "two" "inclusions" :=
   apply Extensionality_Ensembles; 
   unfold Same_set; 
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
It holds that (x ∈ (Ω \ ∅)).

Take x : U; Assume x_in_complement_empty.
It holds that (x ∈ Ω). 
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
Write A_in_F as 
  ((A = Ω) ∨ (A = ∅) ).
Because A_in_F either A_is_full or A_is_empty. 
rewrite -> A_is_full. 
(*does the same as: 
  Write goal using (A = Ω) as 
    (In (Ensemble U) empty_and_full (Ω \ Ω)). 
  Could use Write goal as ..., but becomes very long. What to do?
*) 
(* now want to apply complement_full_is_empty, but does not work:
Write goal using ((Ω \ Ω) = ∅) as (∅ ∈ empty_and_full).  *)
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

(*All empty:*)
It suffices to show that (Countable_union C = ∅). 
We prove equality by proving two inclusions. 

Take x : U; Assume x_in_countable_union_C. 
Choose n such that x_in_C_n according to x_in_countable_union_C. 
Write x_in_C_n using (C n = ∅) as (x ∈ ∅).
Contradiction. 

Take x : U; Assume x_in_empty. 
Contradiction. 

(*Not all empty:*)
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