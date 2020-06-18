(** Pattern-matching for type of set (subset/sigma-algebra): **)
Definition inn (V : Type) (A : Type) (x : Type)  := 
  match (type of V) with 
    σ_algebra => True
  | λ_system => True
  end.

Definition innn (V : Type) (A : Type) (x : Type) := 
  

Definition inn (G : σ_algebra) (A : subset U) := 
  A ∈ underlying_set_of_subsets_sigma G.


Notation "A 'is_in' a F" := 
  match a with 
    0 => In _ F A
  | (S n) => inn F A
  end (at level 50).
Variable A : Ensemble U. 
Variable G : Ensemble (Ensemble U). 
Lemma test : A is_in 0 G.

Notation "A 'is' 'in' F" := 
  A is in _ F (at level 50). 


Definition elem {G : σ_algebra} := true.
Definition elem {H : setOfSubsets U} := true.





(** Type-dependent 'in' definition: **)

Definition my_in {V : Type} (A : Type) (x : Type) := 
  



(** Several 'in' notations using modules: **)
Module ensemble.
Definition Inn {V : Type} (A : Ensemble V) (x : V) := In V A x.
End ensemble. 
Module ensensemble.
Definition Inn {V : Type} (F : Ensemble (Ensemble V)) (A : Ensemble V) := In (Ensemble V) F A.
End ensensemble.

Import ensemble.
Import ensensemble.

Notation "x 'inn' A" := (@Inn _ A x) (at level 50).

Variable x : U.
Variable A : Ensemble U. 
Variable G : Ensemble (Ensemble U).
Lemma test : x inn A.






(** Pi and Lambda systems **)

Record π_system := make_pi_system
  { underlying_set_of_subsets_pi : setOfSubsets U;
    proof_is_pi_system : is_π_system underlying_set_of_subsets_pi}.
Coercion underlying_set_of_subsets_pi : π_system >-> setOfSubsets.
Hint Resolve proof_is_pi_system : measure_theory.
Hint Resolve underlying_set_of_subsets_pi : measure_theory.

Variable Π : π_system.

Lemma Π_is_π_system : is_π_system Π.

Proof. 
It holds that (is_π_system Π).
Qed.
Hint Resolve Π_is_π_system : measure_theory.


Record λ_system := make_lambda_system
  { underlying_set_of_subsets_lambda : setOfSubsets U;
    proof_is_lambda_system : is_λ_system underlying_set_of_subsets_lambda}.
(*Variable L : λ_system.*)
Coercion underlying_set_of_subsets_lambda : λ_system >-> setOfSubsets.
(*Definition Λ : setOfSubsets U := L.*)
Hint Resolve proof_is_lambda_system : measure_theory.
Hint Resolve underlying_set_of_subsets_lambda : measure_theory.
Variable L : λ_system.
Lemma Λ_is_λ_system : is_λ_system L.

Proof. 
It holds that (is_λ_system L).
Qed.
Hint Resolve Λ_is_λ_system : measure_theory.


Record π_and_λ_system := make_pi_and_lambda_system
  { underlying_set_of_subsets_pi_and_lambda : setOfSubsets U;
    proof_is_pi_and_lambda_system : (is_λ_system underlying_set_of_subsets_pi_and_lambda 
                                  /\ is_π_system underlying_set_of_subsets_pi_and_lambda)}.
Variable J : π_and_λ_system.
Coercion underlying_set_of_subsets_pi_and_lambda : π_and_λ_system >-> setOfSubsets.
Definition K : setOfSubsets U := J.
Hint Resolve proof_is_pi_and_lambda_system : measure_theory.
Hint Resolve underlying_set_of_subsets_pi_and_lambda : measure_theory.

Lemma Λ_is_π_and_λ_system : (is_λ_system K /\ is_π_system K).

Proof. 
It holds that ((is_λ_system (underlying_set_of_subsets_pi_and_lambda J))
            /\ (is_π_system (underlying_set_of_subsets_pi_and_lambda J))) (xx). 
It holds that (is_λ_system K /\ is_π_system K).
Qed.
Hint Resolve Λ_is_π_and_λ_system : measure_theory.
