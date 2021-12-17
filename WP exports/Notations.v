(** # Notations for Waterproof*)
Require Import Reals.

Require Import wplib.Tactics.Tactics.
(** ## Real numbers*)
Notation "｜ x ｜" := (Rabs x) (at level 20).
(** ## Suprema and infima*)
Notation is_sup := is_lub.
Notation is_bdd_above := bound.
(** ## Sequences*)
Notation "an 'converges' 'to' a" := 
  (Un_cv an a) (at level 50). 
(** ## Sums and series*)
Notation "'Σ' Cn 'equals' x" := 
  (infinite_sum Cn x) (at level 50).
  
Notation "'Σ' 'of' Cn 'up' 'to' n" := 
  (sum_f_R0 Cn n) (at level 50). 
(* Sum and series also defined in series.wpn. What to adapt? *)
(** ## Functions*)
(** For the composition of a sequence and a function (e.g. for the sequence of measures of a sequence of sets):*)
Notation "μ ◦ C" := 
  (fun (n:ℕ) ↦ (μ (C n))) (at level 45).
(** ## Sets*)
Definition is_in {D : Set} := fun (A : (D → Prop)) ↦ (fun (x : D) ↦ A x).
Notation "x ∈ A" := (@is_in _ A x) (at level 50) : analysis_scope.
