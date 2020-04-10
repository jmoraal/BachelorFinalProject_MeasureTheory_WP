(*Version 1.4.4 - 10-04-2020
  Proof complete. 
*)
Require Import Sets.Ensembles.
Require Import Sets.Classical_sets.
Require Import wplib.Tactics.Tactics.
Require Import wplib.Tactics.TacticsContra.
Require Import wplib.Notations.Notations.
Require Import Sets.Powerset.
Require Import Coq.Logic.Classical_Pred_Type. 

Variable Ω : Type.

Definition is_pi_system (Π : Ensemble (Ensemble Ω)) 
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


Definition is_lambda_system (Λ : Ensemble (Ensemble Ω)) 
  : Prop :=
    full_set_in_set Λ ∧ 
    complement_in_set Λ ∧
    closed_under_disjoint_countable_union Λ. 

Definition is_σ_algebra (Λ : Ensemble (Ensemble Ω)) 
  : Prop := 
    full_set_in_set Λ ∧ 
    complement_in_set Λ ∧
    closed_under_countable_union Λ.

Definition empty_and_full (A : Ensemble Ω) 
  : Prop := 
    (A = (Full_set Ω)) ∨ 
    (A = (Empty_set Ω)).  

Lemma complement_empty_is_full : 
  (Full_set Ω) = (Setminus _ (Full_set Ω ) (Empty_set Ω)). 

Proof. 
Apply Extensionality_Ensembles. 
Expand the definition of Same_set. 
Expand the definition of Setminus. 
split. 
Expand the definition of Included. 
Take x : Ω. 
Assume x_in_full. 
Expand the definition of In in x_in_full. 
It holds that (In Ω (Full_set Ω) x ∧ ¬ In Ω (Empty_set Ω) x).

Expand the definition of Included. 
Take x : Ω.
Assume x_in_complement_empty.
Expand the definition of In in x_in_complement_empty. 
Because x_in_complement_empty both x_in_full and not_x_in_empty. 
It holds that (In _ (Full_set Ω) x). 
Qed. 


Lemma complement_full_is_empty : 
  (*∀ A B : Ensemble Ω, Same_set _ A (Full_set Ω) -> Same_set _ B (Full_set Ω) -> *)
  (Empty_set Ω) = (Setminus _ (Full_set Ω) (Full_set Ω)). 
(*complement_full_is_empty niet commutatief?*)

Proof. 
Apply Extensionality_Ensembles.
Expand the definition of Same_set. 
split. 
Expand the definition of Included. 
Take x : Ω.
Assume x_in_empty.
contradiction. 
(*alternatively: 
Expand the definition of Included. 
Take x : Ω. 
Assume x_in_empty. 
Expand the definition of In in x_in_empty. 
Check Empty_set_ind.  (* not necessary, but good to remember this is possible*)
induction x_in_empty.  (* or 'destruct'*) *)

Expand the definition of Included. 
Take x : Ω.
Assume x_in_complement_full.
Expand the definition of In 
  in x_in_complement_full. 
Because x_in_complement_full 
  both x_in_full and not_x_in_full. 
contradiction. 

Qed.


Lemma trivial_salgebra : is_σ_algebra empty_and_full. 

Proof. 
Expand the definition of is_σ_algebra. 
split. 

(* First point: Prove that Omega is in empty_and_full *)
Expand the definition of full_set_in_set. 
It holds that (In _ empty_and_full (Full_set Ω)).
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
*) 
replace (Setminus Ω (Full_set Ω) (Full_set Ω)) 
  with (Empty_set Ω). 
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
Assume C_n_in_empty_and_full : (for all n : ℕ,
   In (Ensemble Ω) empty_and_full (C n)).

Expand the definition of In. 
Expand the definition of empty_and_full. 


By classic it holds that ((forall n : ℕ, (C n) = (Empty_set Ω)) 
  ∨ ¬(forall n : ℕ, (C n) = (Empty_set Ω))) (all_or_not_all_empty). 
Because all_or_not_all_empty either all_empty or not_all_empty. 
It suffices to show that (Countable_union C = (Empty_set Ω)). 
Expand the definition of Countable_union. 
Apply Extensionality_Ensembles. 
Expand the definition of Same_set. 
split. 
Expand the definition of Included. (*gebruik write as ipv steeds Expand*)
Take x : Ω. 
Assume x_in_countable_union_C : (In Ω (x0) ↦ (there exists n : ℕ ,
               In Ω (C n) x0) x). 
Expand the definition of In in x_in_countable_union_C. 
Choose n such that x_in_C_n according to x_in_countable_union_C. 
Write x_in_C_n using (C n = Empty_set Ω) as ((Empty_set Ω) x).
It holds that (In Ω (Empty_set Ω) x). 

Expand the definition of Included.  
Take x : Ω.
Assume x_in_empty : (In _ (Empty_set Ω) x). 
It holds that ((In Ω (x0) ↦ (∃n : ℕ,
               In Ω (C n) x0) x)).

It suffices to show that (Countable_union C = (Full_set Ω)). 
(*Expand the definition of Countable_union. *)
Apply Extensionality_Ensembles. 
Expand the definition of Same_set. 
split. 
Expand the definition of Included. 
(*tot hier: write goal as ..*)
Take x : Ω.
Assume x_in_countable_union_C : 
   (In Ω (x0) ↦ (there exists n : ℕ, In Ω (C n) x0) x). 
Expand the definition of In in x_in_countable_union_C. 
Choose n0 such that x_in_C_n0 
   according to x_in_countable_union_C. 
It holds that ((C n0 = Full_set Ω)
   \/(C n0 = Empty_set Ω)) (C_n0_empty_or_full). 
Because C_n0_empty_or_full either C_n0_full or C_n0_empty. 
rewrite <- C_n0_full. (*write goal as*)
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

(*
Verder: tip vorige keer was 'gebruik write as ipv steeds Expand'. 
Maar over het algemeen lijkt het daar juist onleesbaarder van 
te worden (het deel 'as ...' wordt erg lang). Toch doen? 
Oplossing: tactics definiëren, volgordes veranderen etc; wees creatief. 
*)
