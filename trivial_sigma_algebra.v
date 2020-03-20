(*Version 1.2 - 20-03-2020
  Definitions split up in sub-definitions
  Complement defined using library, not Setminus
  Assume extensionality to use = instead of Same_set
  Definitions of (disjoint) countable union fixed
  Second part of trivial_salgebra simplified (yet to do)
*)
Require Import Sets.Ensembles.
Require Import Sets.Classical_sets.
Require Import wplib.Tactics.Tactics.
Require Import wplib.Notations.Notations.
Require Import Sets.Powerset.

Variable Ω : Type.

Definition is_pi_system (Π : Ensemble (Ensemble Ω)): Prop := 
  ∀ A : Ensemble Ω, In _ Π A ⇒ 
    ∀ B : Ensemble Ω, In (Ensemble Ω) Π B ⇒ 
      In (Ensemble Ω) Π (Intersection Ω A B).  

Definition Countable_union (A : (ℕ → Ensemble Ω)) : Ensemble Ω := 
  fun (x:Ω) ↦ ∃n : ℕ, In Ω (A n) x.

Definition full_set_in_set (Λ : Ensemble (Ensemble Ω)) : Prop :=
  In _ Λ (Full_set Ω). 

Definition complement_in_set (Λ : Ensemble (Ensemble Ω)) : Prop := 
  ∀A  : Ensemble Ω, In _ Λ A 
    ⇒ In _ Λ (Setminus _ (Full_set Ω) A). 

Definition disjoint_countable_union_in_set (Λ : Ensemble (Ensemble Ω)) : Prop :=  (*nog aanpassen, zie hieronder *)
  ∀C : (ℕ → (Ensemble Ω)), 
    (∀ m n : ℕ, m ≠ n ⇒ Disjoint _ (C m) (C n)) 
      ⇒ (∀ n : ℕ, In _ Λ (C n)) ⇒  In _ Λ ( Countable_union C).

Definition closed_under_countable_union (Λ : Ensemble (Ensemble Ω)) : Prop :=  
  ∀C : (ℕ → (Ensemble Ω)), (∀ n : ℕ, In _ Λ (C n)) 
    ⇒  In _ Λ ( Countable_union C).


Definition is_lambda_system (Λ : Ensemble (Ensemble Ω)) : Prop :=
  full_set_in_set Λ /\ 
  complement_in_set Λ /\
  disjoint_countable_union_in_set Λ. 
  
  
Definition is_sigma_algebra (Λ : Ensemble (Ensemble Ω)) : Prop := 
  full_set_in_set Λ /\ 
  complement_in_set Λ /\
  disjoint_countable_union_in_set Λ.

Definition empty_and_full (A : Ensemble Ω) : Prop := 
  (Same_set _ A (Full_set Ω)) \/ (Same_set _ A (Empty_set Ω)).  


Lemma complement_full_is_empty : 
  (*forall A B : Ensemble Ω, Same_set _ A (Full_set Ω) -> Same_set _ B (Full_set Ω) -> *)
  Same_set _ (Empty_set Ω) (Setminus _ (Full_set Ω) (Full_set Ω)). 
(*complement_full_is_empty niet commutatief?*)

Proof. 
Expand the definition of Setminus. 
(*Apply Extensionality_Ensembles.  (only necessary when using = instead of Same_set)*)
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
Expand the definition of In in x_in_complement_full. 
Because x_in_complement_full both x_in_full and not_x_in_full. 
contradiction. 
Qed. 


Lemma complement_empty_is_full : 
  Same_set _ (Full_set Ω) (Setminus _ (Full_set Ω ) (Empty_set Ω)). 

Proof. 
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


(* Dit is het derde deel van het bewijs van trivial_salgebra, maar staat
   hierboven zodat het gecontroleerd kan worden terwijl het tweede deel
   nog niet af is.
*) 
Lemma empty_and_full_countable_union : 
  closed_under_countable_union empty_and_full. 

Proof. 
Expand the definition of closed_under_countable_union. 
(*dit is wat je eigenlijk wil, maar 'niet convertible':*)
(*Assume C_n_in_empty_and_full : 
  (for all n : ℕ, In _ empty_and_full (C n)). *)
(*of: *)
(*Choose (C : (ℕ → (Ensemble Ω))) such that 
  (for all n : ℕ, In _ empty_and_full (C n)). *)

(*maar in plaats daarvan, nu maar het voor de hand liggende: *)
Take C : (ℕ → (Ensemble Ω)). 
Assume C_n_in_empty_and_full : (for all n : ℕ,
   In (Ensemble Ω) empty_and_full (C n)). 
(*probleem: later komt n0, maar dan geldt niet 
  per se dat In _ empty_and_full (C n0). 
*) 

Expand the definition of Countable_union. 
Expand the definition of In. 
Expand the definition of empty_and_full. 
(*hoe nu verder?
  Gebruik tacticsContra. *)
Qed. 


Lemma trivial_salgebra : is_sigma_algebra empty_and_full. 

Proof. 
Expand the definition of is_sigma_algebra. 
split. 
Expand the definition of full_set_in_set. 
It holds that (In _ empty_and_full (Full_set Ω)).
split.

Expand the definition of complement_in_set. 
Take A : (Ensemble Ω). 
Assume A_in_F : (In _ empty_and_full A). 
Write A_in_F as ( (Same_set _ A (Full_set Ω)) 
  \/ (Same_set _ A (Empty_set Ω)) ).
Because A_in_F either A_is_full or A_is_empty. 
We claim that (A = (Full_set Ω)) (A_equals_full). 
Apply Extensionality_Ensembles. 
Apply A_is_full. 
Write goal using (A = (Full_set Ω)) as 
  (In (Ensemble Ω) empty_and_full (Setminus Ω (Full_set Ω) (Full_set Ω))). 
Apply (*... gebruik gelijkheden ipv Same_set*)
(*
We claim that ((Same_set _ A (Full_set Ω)) 
  -> In _ empty_and_full 
      (Setminus _ (Full_set Ω) A)) (comp_full_in_F).

Assume A_is_full : (Same_set _ A (Full_set Ω)). *)
replace A with (Full_set Ω). 
(* ^ creates extra subgoal; how to avoid this?*)
replace (Setminus Ω (Full_set Ω) (Full_set Ω)) 
  with (Empty_set Ω). 
It holds that (In _ empty_and_full (Empty_set Ω)). 
Apply Extensionality_Ensembles. 
(*We need to show that (Same_set Ω (Empty_set Ω) (Setminus Ω (Full_set Ω) (Full_set Ω))). *)
Apply complement_full_is_empty. 
(* ^ complement_full_is_empty is blijkbaar niet commutatief*)
Apply Extensionality_Ensembles. 
It holds that (Same_set Ω (Full_set Ω) A). (*only there to resolve remaining goal*)

We claim that ((Same_set _ A (Empty_set Ω)) 
  -> In _ empty_and_full 
      (Setminus _ (Full_set Ω) A)) (comp_empty_in_F).
Assume A_is_empty : (Same_set _ A (Empty_set Ω)). 
replace A with (Empty_set Ω). 
(* ^ creates extra subgoal; how to avoid this?*)
replace (Setminus Ω (Full_set Ω) (Empty_set Ω)) 
  with (Full_set Ω). 
(* ^ now replaced, later proven. Shorter way?*)
It holds that (In _ empty_and_full (Full_set Ω)). 
Apply Extensionality_Ensembles. 
(*We need to show that (Same_set Ω (Empty_set Ω) (Setminus Ω (Full_set Ω) (Full_set Ω))). *)
Apply complement_empty_is_full. 
Apply Extensionality_Ensembles. 
It holds that (Same_set Ω (Empty_set Ω) A). (*only there to resolve remaining goal. Avoidable?*) 

(*A_in_F, comp_full_in_F en comp_empty_in_F zou nu genoeg 
  moeten zijn, maar het lukt me niet ze te combineren. 
*)

(*Verder, zijn If .. then .. (else ..) statements mogelijk 
  in deze situatie? Ik heb wat voorbeelden gevonden op  
  internet, maar het is me niet gelukt de tactic te gebruiken 
(*   zonder error. Bijvoorbeeld: 
*) *)
If (Same_set _ A (Empty_set Ω)) then (In (Ensemble Ω) empty_and_full (Setminus Ω (Full_set Ω) A)). 

Qed. 
