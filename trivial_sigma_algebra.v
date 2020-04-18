(*Version 1.5.1 - 18-04-2020
  Further proof cleanup, w/ a few questions
  Progress lost due to PC crash, despite saving :( 
  Generated sigma algebra defined
  pi-lambda theorem and lemma stated. 
*)
Require Import Sets.Ensembles.
Require Import Sets.Classical_sets.
Require Import wplib.Tactics.Tactics.
Require Import wplib.Tactics.TacticsContra.
Require Import wplib.Notations.Notations.
Require Import Sets.Powerset.
Require Import Coq.Logic.Classical_Pred_Type. 

Variable Ω : Type.

Definition is_π_system (Π : Ensemble (Ensemble Ω)) 
  : Prop := 
    ∀ A : Ensemble Ω, In _ Π A ⇒ 
      ∀ B : Ensemble Ω, In (Ensemble Ω) Π B ⇒ 
       In (Ensemble Ω) Π (Intersection Ω A B).  

Definition Countable_union (A : (ℕ → Ensemble Ω)) 
  : Ensemble Ω := 
    fun (x:Ω) ↦ ∃n : ℕ, In Ω (A n) x.

Definition full_set_in_set (Λ : Ensemble (Ensemble Ω)) 
  : Prop :=
    In _ Λ (Full_set Ω). 

Definition complement_in_set (Λ : Ensemble (Ensemble Ω)) 
  : Prop := 
    ∀A  : Ensemble Ω, In _ Λ A 
      ⇒ In _ Λ (Setminus _ (Full_set Ω) A). 

Definition closed_under_disjoint_countable_union (Λ : Ensemble (Ensemble Ω)) 
  : Prop :=
    ∀C : (ℕ → (Ensemble Ω)), 
      (∀ m n : ℕ, m ≠ n ⇒ Disjoint _ (C m) (C n)) 
        ⇒ (∀ n : ℕ, In _ Λ (C n)) ⇒  In _ Λ ( Countable_union C).

Definition closed_under_countable_union (Λ : Ensemble (Ensemble Ω)) 
  : Prop :=  
    ∀C : (ℕ → (Ensemble Ω)), (∀ n : ℕ, In _ Λ (C n)) 
      ⇒  In _ Λ ( Countable_union C).


Definition is_λ_system (Λ : Ensemble (Ensemble Ω)) 
  : Prop :=
    full_set_in_set Λ ∧ 
    complement_in_set Λ ∧
    closed_under_disjoint_countable_union Λ. 

Definition is_σ_algebra (F : Ensemble (Ensemble Ω)) 
  : Prop := 
    full_set_in_set F ∧ 
    complement_in_set F ∧
    closed_under_countable_union F.

Definition  σ_algebra_generated_by (A : Ensemble (Ensemble Ω)) 
  : (Ensemble (Ensemble Ω)) := 
    fun (B : Ensemble Ω) ↦ 
    (∀ F : Ensemble (Ensemble Ω), (is_σ_algebra F ∧ Included _ A F) ⇒ In _ F B). 
(*
Definition restriction (F : Ensemble (Ensemble Ω)) (A : (Ensemble Ω)) 
  : (Ensemble (Ensemble Ω)) := 
    fun (B : Ensemble Ω) ↦ 
*)
Definition empty_and_full (A : Ensemble Ω) 
  : Prop := 
    (A = (Full_set Ω)) ∨ 
    (A = (Empty_set Ω)).  


Tactic Notation "We" "prove" "equality" "by" "proving" "two" "inclusions" :=
   apply Extensionality_Ensembles; 
   unfold Same_set; 
   unfold Setminus; 
   unfold Included;
   split.

Lemma complement_empty_is_full : 
  (Full_set Ω) = (Setminus _ (Full_set Ω ) (Empty_set Ω)). 

Proof. 
We prove equality by proving two inclusions. 
Take x : Ω; Assume x_in_full. 
It holds that (In Ω (Full_set Ω) x ∧ ¬ In Ω (Empty_set Ω) x).

Take x : Ω; Assume x_in_complement_empty.
Because x_in_complement_empty both x_in_full and not_x_in_empty. 
It holds that (In _ (Full_set Ω) x). 
Qed. 


Lemma complement_full_is_empty : 
  (Empty_set Ω) = (Setminus _ (Full_set Ω) (Full_set Ω)). 

Proof. 
We prove equality by proving two inclusions. 
Take x : Ω; Assume x_in_empty.
contradiction. 

Take x : Ω; Assume x_in_complement_full.
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
Take A : (Ensemble Ω). 
Assume A_in_F : (In _ empty_and_full A). 
Write A_in_F as ( (A = (Full_set Ω)) 
  ∨ (A = (Empty_set Ω)) ).
Because A_in_F either A_is_full or A_is_empty. 
rewrite -> A_is_full. 
(*does the same as: 
  Write goal using (A = (Full_set Ω)) as 
    (In (Ensemble Ω) empty_and_full (Setminus Ω (Full_set Ω) (Full_set Ω))). 
  Could use Write goal as ..., but becomes very long. What to do?
*) 
replace (Setminus Ω (Full_set Ω) (Full_set Ω)) 
  with (Empty_set Ω). (*alternative from WPlib?*)
It holds that (In _ empty_and_full (Empty_set Ω)). 
Apply complement_full_is_empty. 

rewrite -> A_is_empty. 
replace (Setminus Ω (Full_set Ω) (Empty_set Ω)) 
  with (Full_set Ω). 
It holds that (In _ empty_and_full (Full_set Ω)). 
Apply complement_empty_is_full. 

(* Third point: Prove that empty_and_full is closed under countable union*)
Expand the definition of closed_under_countable_union. 
Take C : (ℕ → (Ensemble Ω)). 
Assume C_n_in_empty_and_full.
By classic it holds that ((forall n : ℕ, (C n) = (Empty_set Ω)) 
  ∨ ¬(forall n : ℕ, (C n) = (Empty_set Ω))) (all_or_not_all_empty). 
Because all_or_not_all_empty either all_empty or not_all_empty. 
It suffices to show that (Countable_union C = (Empty_set Ω)). 
We prove equality by proving two inclusions. 

Expand the definition of Countable_union. 
Take x : Ω; Assume x_in_countable_union_C. 
Choose n such that x_in_C_n according to x_in_countable_union_C. 
Write x_in_C_n using (C n = Empty_set Ω) as ((Empty_set Ω) x).
It holds that (In Ω (Empty_set Ω) x). 

Take x : Ω; Assume x_in_empty. 
contradiction. 
(*It holds that (In Ω (Countable_union C) x).*)

It suffices to show that (Countable_union C = (Full_set Ω)). 
We prove equality by proving two inclusions. 
Take x : Ω; Assume x_in_countable_union_C. 
Choose n0 such that x_in_C_n0 
   according to x_in_countable_union_C. 
It holds that ((C n0 = Full_set Ω)
   ∨ (C n0 = Empty_set Ω)) (C_n0_empty_or_full). 
Because C_n0_empty_or_full either C_n0_full or C_n0_empty. 
Write goal using (Full_set Ω = C n0) as (In Ω (C n0) x). 
(*rewrite <- C_n0_full. *)
Apply x_in_C_n0. 
Write x_in_C_n0 using (C n0 = Empty_set Ω) as (Empty_set Ω x).
Contradiction. 
(*of ook: It holds that (In Ω (Full_set Ω) x). Uit iets onwaars kan alles volgen. *)

By not_all_empty it holds that (∃n : ℕ, ¬ (C n = Empty_set Ω)) (one_not_empty). 
By C_n_in_empty_and_full it holds that (∃n : ℕ, (C n = Full_set Ω)) (one_full).
Choose n1 such that C_n1_full according to one_full. 
rewrite <- C_n1_full. 
It holds that (Included Ω (C n1) (Countable_union C)). 
Qed.


Lemma π_and_λ_is_σ : 
  ∀ F : Ensemble (Ensemble Ω), 
    is_π_system F ∧ is_λ_system F 
    ⇒ is_σ_algebra F. 

Theorem π_λ_theorem : 
  ∀ Π Λ : Ensemble (Ensemble Ω), 
    is_π_system Π ∧ is_λ_system Λ ∧ Included _ Π Λ
    ⇒ Included _ (σ_algebra_generated_by Π) Λ. 





