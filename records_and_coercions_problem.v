Require Import Sets.Ensembles.

Definition set_of_subsets (U : Type) := 
  (Ensemble (Ensemble U)).

Variable U : Type.

Definition is_σ_algebra_on U (F : set_of_subsets U) := True.

Record σ_algebra V := make_sigma_algebra
  { underlying_set_of_subsets_sigma : set_of_subsets V;
    proof_is_sigma_algebra : is_σ_algebra_on V underlying_set_of_subsets_sigma}.

Coercion underlying_set_of_subsets_sigma : σ_algebra >-> set_of_subsets.

Hint Resolve proof_is_sigma_algebra : measure_theory.
Hint Resolve underlying_set_of_subsets_sigma : measure_theory.

Variable x : U.
Variable A : Ensemble U. 
Variable G : Ensemble (Ensemble U).
Variable F : σ_algebra U.

Check In _ A x.
Check In _ G A. 
Fail Check In _ F A.
(* Even does not work if type does not need to be inferred: *)
Fail Check In (Ensemble U) F A.

(* Does work if 'in' is a function of set_of_subsets: *)
Definition my_in U (G : set_of_subsets U) (A : Ensemble U) 
  := In (Ensemble U) G A.
Check my_in _ F A. 

(* But not for Ensemble (Ensemble U), even though this is the same: *)
Definition my_in1 U (G : Ensemble (Ensemble U)) (A : Ensemble U) 
  := In (Ensemble U) G A.
Fail Check my_in1 _ F A. 


(* This also causes it not to work when generalising: *)
(** The definition below is how 'In' is defined in the Ensembles
    library, only in an explicit form **)
Definition my_in2 (V : Type) (G : Ensemble V) (A : V) 
  := In V G A.

Check my_in2 _ A x.
Check my_in2 _ G A.
Fail Check my_in2 _ F (Empty_set U). 
Fail Check my_in2 (Ensemble U) F (Empty_set U). 