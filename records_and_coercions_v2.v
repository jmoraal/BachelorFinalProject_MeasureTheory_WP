Require Import Coq.Sets.Classical_sets.

(* I don't know in how far these are necessary:*)

Set Primitive Projections.
Set Nonrecursive Elimination Schemes.


(* This needs to be replaced by the actual definition *)
Definition is_sigma_algebra {U : Type} (F : Ensemble (Ensemble U)) := True.

Definition set_of_subsets {U : Type} := Ensemble (Ensemble U).

(* Implicit dependence by curly brackets, 
   used @ to explicitly specify implicit arguments.*)
Record sigma_algebra {U : Type} := make_sigma_algebra
  { underlying_set_of_subsets : @set_of_subsets U;
    proof_is_sigma_algebra : is_sigma_algebra underlying_set_of_subsets}.

Variable V : Type.

Variable F : @sigma_algebra V.

Coercion underlying_set_of_subsets : sigma_algebra >-> set_of_subsets.

(* The special aspect to the line below is that we want to define 
   a variable G which is just a set of subsets, and do so by 
   assigning F, which is not of that type. It works because 
   F is coerced to the right type. *)
Definition G : @set_of_subsets V := F.


(*
Variable my_in : @set_of_subsets V -> Prop.
*)

Definition my_in (G : @set_of_subsets V) (A : Ensemble V) : Prop := 
  G A.
Variable A : Ensemble V.
Lemma empty_in_G : Prop.
exact (my_in G A).
Qed.

Lemma empty_in_F : Prop.
exact (my_in F A).
Qed.

Lemma empty_in_F2 : my_in F (Empty_set V).
Admitted.
(*
Definition my_ensemble := V -> Prop.
Definition my_ensemble_in 
  (A:my_ensemble) (x:V) : Prop := A x.

Lemma empty_in_σ : my_ensemble_in F (Empty_set V). 
*)
Definition my_in2 {V} (G : @set_of_subsets V) (A : Ensemble V) 
  
    := In (Ensemble V) G A.
Check my_in. 
Check my_in2.
Lemma empty_in_σ : my_in2 F (Empty_set V). 



(*** As sigma type ***)
Definition my_universe := Type.
Definition my_sig {U : my_universe} {P : U -> Prop } := sig P.

Definition new_sigma_algebra { U : Type } :=
  @sig (Ensemble (Ensemble U)) (is_sigma_algebra).

Definition my_coercion {U : Type} : 
  @new_sigma_algebra U -> (@set_of_subsets U) :=
  (@proj1_sig (Ensemble (Ensemble U)) (is_sigma_algebra)).

Coercion my_coercion : new_sigma_algebra >-> set_of_subsets.



Variable F_2 : @new_sigma_algebra V.

Definition H : @set_of_subsets V := F_2.

Record total2 { T: my_universe } ( P: T -> Prop )
  := tpair { pr1 : T; pr2 : P pr1 }.

Arguments tpair {_} _ _ _.
Arguments pr1 {_ _} _.
Arguments pr2 {_ _} _.

(*Definition my_proj {T : my_universe} {P: T -> my_universe} 
  := @pr1 T P.

Check my_proj. 

Variable A : my_universe.
Variable Pred : A -> my_universe.

Definition my_space := (total2 Pred).
Variable b : my_space.
(* This does not work: Definition test : A := b. *)
Definition my_coercion_2 : my_space -> A := pr1.
Coercion my_coercion_2 : my_space >-> A.
(* The next line does work: *)
Definition test : A := b.*)

Definition isaset (X : my_universe) : Prop := True.

(* This gives a universe inconsistency! 
Definition hSet : my_universe := @total2 my_universe (fun X : my_universe => isaset X). *)
(*
Definition isaset (X : UU) : UU := ∏ x x' : X, isaprop (x = x').
Definition hSet : UU := total2 (λ X : UU, isaset X).

Definition make_hSet (X : UU) (i : isaset X) := tpair isaset X i : hSet.
Definition pr1hSet : hSet -> UU := @pr1 UU (λ X : UU, isaset X).
Coercion pr1hSet: hSet >-> UU.*)

(** * Try to get subsets to work with coercions. *)
Set Primitive Projections.
Set Nonrecursive Elimination Schemes.
(* These arguments can also be made implicit. *)
Definition my_carrier (U : my_universe) := U.
Record subset (U : my_universe)
              (subset_condition : U -> Prop) := mk_subset_element {
  proj_element : @my_carrier U;
  proj_witness : subset_condition proj_element }.

Definition proj_from_subset {U : my_universe}
                            {subset_condition : U->Prop}
  := @proj_element U subset_condition.
Check proj_from_subset.

Lemma U_is_carrier_U : forall U : Type, U = @my_carrier U.
Proof.
intro.
reflexivity.
Qed.

Coercion proj_from_subset : subset >-> my_carrier.

(* This does not work yet

Record subset_2 := mk_subset {
    subset_carrier : my_universe;
    subset_condition : subset_carrier -> Prop
  }.



Definition my_coercion_2 := subset_carrier.
Check subset_carrier.

Coercion my_coercion_2 : subset_2 >-> my_universe.

Variable U : subset_2.

Definition x : U :=

Variable U : my_universe.

Variable x : (@subset U (fun x => True)).

Definition y : U.
  pose proof (U_is_carrier_U U).
  rewrite H0.
  exact x.
Qed.

Definition x : 
Variable x : A.

Definition a_type {U : Type} := U.

Definition my_subset {U : Type} {P : U -> Prop} :=
  sig P.

Definition my_coercion_2 {U : my_universe} 
  {P : U -> Prop}
  : (@my_subset U P) -> @a_type U.
intro.
apply (@proj1_sig _ P).
apply X.
Qed.

Coercion my_coercion_2 : my_subset >-> a_type.

Variable condition : V -> Prop.

Variable my_set : @my_subset V condition.

Variable A : @my_subset V condition.

Variable x : A.*)







