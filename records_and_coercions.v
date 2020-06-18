Require Import Coq.Sets.Classical_sets.

(* I don't know in how far these are necessary:

Set Primitive Projections.
Set Nonrecursive Elimination Schemes.
*)

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

Definition my_universe := Type.
Definition my_sig {U : my_universe} {P : my_universe -> Prop } := sig P.

Definition new_sigma_algebra { U : Type } :=
  @sig (Ensemble (Ensemble U)) (is_sigma_algebra).

Definition my_coercion {U : Type} : 
  @new_sigma_algebra U -> (@set_of_subsets U) :=
  (@proj1_sig (Ensemble (Ensemble U)) (is_sigma_algebra)).

Coercion my_coercion : new_sigma_algebra >-> set_of_subsets.

Variable F_2 : @new_sigma_algebra V.

Definition H : @set_of_subsets V := F_2.