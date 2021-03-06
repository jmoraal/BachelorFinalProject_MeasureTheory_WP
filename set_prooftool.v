

Require Import Sets.Ensembles.
Require Import Sets.Classical_sets.
Require Import Sets.Powerset.
Require Import Logic.  
Require Import ClassicalFacts. 
Require Import Omega. 
Require Import Coq.Arith.Wf_nat. 
(*
Hint Unfold In Included Same_set Strict_Included Add Setminus Subtract : sets.
(*Hint Constructors Union Intersection Disjoint Full_set : sets.*)
Hint Resolve Union_introl Union_intror Intersection_intro In_singleton
  Couple_l Couple_r Triple_l Triple_m Triple_r Disjoint_intro
  Extensionality_Ensembles Full_intro: sets.
Hint Resolve Setminus Extensionality_Ensembles : sets.
*)
(*
Hint Unfold In Included Same_set Strict_Included Add Setminus Subtract: sets.

Hint Resolve Union_introl Union_intror Intersection_intro In_singleton
  Couple_l Couple_r Triple_l Triple_m Triple_r Disjoint_intro
  Extensionality_Ensembles: sets.
*)
Hint Constructors Union Intersection Disjoint Full_set : sets.
(*
Hint Resolve Setminus : sets.
Hint Resolve Union_introl Union_intror Intersection_intro In_singleton
  Couple_l Couple_r Triple_l Triple_m Triple_r Disjoint_intro
  Extensionality_Ensembles: sets.
Hint Resolve Full_intro : sets.  
Hint Resolve Intersection_intro : sets. 
Hint Resolve Union_introl Union_intror : sets. 
Hint Resolve Disjoint_intro : sets. 
*)

(**** WP tactics library ****)
Require Import Rbase.
Require Import Rfunctions.
Require Import SeqSeries.
Require Import Rtrigo.
Require Import Ranalysis.
Require Import Integration.
Require Import micromega.Lra.
Require Import Omega.
Require Import Max.
(* Require Import Unicode.Utf8. *)
Require Import Sets.Ensembles.
Require Import Sets.Classical_sets.

(** Guarantee indentation and introduce custom notation for forall *)
Notation "'for' 'all' x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[ ' '[ ' for  all  x .. y ']' , '//'  P ']'") : type_scope.

Notation "∀ x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 200, x binder, y binder, right associativity,
  only parsing) : type_scope.

Notation "'there' 'exists' x .. y , P " := (exists x, .. (exists y, P) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[ ' '[ ' there  exists  x .. y  ']' , '//'  P ']'") : type_scope.

Notation "∃ x .. y , P " := (exists x, .. (exists y, P) ..)
  (at level 200, x binder, y binder, right associativity,
  only parsing) : type_scope.

Notation "'fun' x .. y '↦' t" := (fun x => .. (fun y => t) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[ ' '[ ' 'fun' x .. y ']' '↦' '/' t ']'").

Notation "x ∨ y" := (x \/ y) (at level 85, right associativity) : type_scope.
Notation "x ∧ y" := (x /\ y) (at level 80, right associativity) : type_scope.
Notation "x → y" := (x -> y)
  (at level 99, y at level 200, right associativity,
   only parsing): type_scope.
Notation "x ⇒ y" := (x -> y)
  (at level 99, y at level 200, right associativity,
   only parsing): type_scope.
(* the notation below is fun, but is no good for functions *)
(* need to see if this can be adapted so it only uses 
   this notation for propositions *)
(*Notation "'if' x 'then' y" := (x -> y)
  (at level 99, y at level 200, right associativity): prop_scope.*)
Notation "x ⇨ y" := (x -> y)
  (at level 99, y at level 200, right associativity): type_scope.

Notation "x ↔ y" := (x <-> y) (at level 95, no associativity): type_scope.
Notation "x ⇔ y" := (x <-> y) (at level 95, no associativity): type_scope.
Notation "¬ x" := (~x) (at level 75, right associativity) : type_scope.
Notation "x ≠ y" := (x <> y) (at level 70) : type_scope.

Notation "x ≤ y" := (le x y) (at level 70, no associativity) : nat_scope.
Notation "x ≥ y" := (ge x y) (at level 70, no associativity) : nat_scope.

Notation "x ≤ y" := (x <= y)%R (at level 70, no associativity) : R_scope.
Notation "x ≥ y" := (x >= y)%R (at level 70, no associativity) : R_scope.

Open Scope nat_scope.
Open Scope R_scope.

(* TODO: the below definition doesn't work very nicely *)
Notation "x ↦ y" := (fun x => y) (at level 0).

Notation "'ℕ'" := (nat).
Notation "'ℝ'" := (R).

(** Add field and lra to tactics to try automatically *)

Hint Extern 3 ( _ = _ ) => field : real.
Hint Extern 3 ( _ <= _ ) => lra : real.
Hint Extern 3 ( _ >= _ ) => lra : real.
Hint Extern 3 ( _ < _ ) => lra : real.
Hint Extern 3 ( _ > _ ) => lra : real.


Ltac wp_power :=
  timeout 5 (first [ solve [auto with *]
        | solve [eauto with *]
        | solve [firstorder (auto with *)]
        | solve [firstorder (eauto with *)]]).

Ltac set_power :=
  timeout 1 (first [ solve [auto with sets]
        | solve [eauto with sets]
        | solve [firstorder (auto with sets)]
        | solve [firstorder (eauto with sets)]]).


(*** NEW ***)
Ltac destruct_intersec :=
  match goal with 
    | [H : In _ (Intersection _ _ _) _  |- _] => destruct H
    | [H : In _ (Union _ _ _) _  |- _] => destruct H; try set_power
  end.
(*_ ∈ _ ∩ _*)
Ltac trivial_set_inclusion := 
  try intro x;
  try intro H;
  try destruct_intersec;
  try contradiction;
  set_power.

Ltac trivial_set_equality := 
  try intros A;
  try intros B;
  try apply Extensionality_Ensembles;
  try unfold Same_set;
  try unfold Included;
  split;
  trivial_set_inclusion;
  trivial_set_inclusion.
(*To do: 
    destruct
    error message if no succes
*)
Tactic Notation "This" "equality" "is" "trivial" := 
   trivial_set_equality.

Hint Extern 5 (_ = _) => trivial_set_equality : sets. 


Ltac intro_strict s t :=
  match goal with
    | [ |- forall _ : t, _ ] => intro s
  end.

Tactic Notation "Take" ident(s) ":" constr(t):=
  intro_strict s t.

Ltac assume_strict s t :=
  match goal with
    | [ |- ?u -> _ ] => (change u with t; intro s)
  end.

Tactic Notation "Assume" ident(s) :=
  intro s.

Tactic Notation "Assume" ident(s) ":" constr(t) :=
  assume_strict s t.

Ltac goal_check t :=
  tryif (change t) 
    then (idtac "We indeed need to show that" t)
    else fail "This is not the current goal".

(** Make it possible to verify the goal t by writing
    "We need to show that t". *)
Tactic Notation "We" "need" "to" "show" "that" constr(t) :=
  goal_check t.

(** Make it possible to verify the goal t by writing
    "To show : t". *)
Tactic Notation "To" "show" ":" constr(t) :=
  goal_check t.

(** The tactic (hypo_check s t) checks if t is one of the 
    current hypothesis, and if so, it renames it into s *)
Ltac hypo_check s t:=
match goal with 
| [H : t |- _] => rename H into s
| _ => fail
end.

Tactic Notation "Choose" constr(t):=
  exists t.

Tactic Notation "Choose" ident(s) ":=" constr(t) :=
  pose (s := t);
  exists s.

Tactic Notation "Choose" ident(s) 
                "such" "that" ident(u)
                "according" "to" constr(v) (*":" constr(t)*):=
  destruct v as [s u].

(*Tactic Notation "Choose" ident(s)
                "such" "that" ident(u)
                "according" "to" ident(v)
                "with" constr(t) :=
  destruct v with t as [s u]. *)

Tactic Notation "Choose" ident(s)
                "such" "that" ident(u)
                "according" "to" constr(v)
                "with" constr(t) :=
  destruct v with t as [s u].


Tactic Notation "Because" ident(s) 
  "both" ident(u) "and" ident(v) :=
  destruct s as [u v].

Tactic Notation "Because" ident(s) 
  "both" ident(u) ":" constr(t_u)
  "and"  ident(v) ":" constr(t_v):=
  destruct s as [u v].

Tactic Notation "Because" ident(s)
  "either" ident(u) "or" ident(v) :=
  destruct s as [u | v].

(** Apply with goal check
    The next tactics verify whether certain steps have the desired effect. *)
Ltac new_goal_verified_apply s t :=
  apply s;
  match goal with 
  | [|- t] => idtac "Expected goal was produced"
  | _ => fail "Lemma did not produce expected outcome"
  end.

(*Tactic Notation "By" constr(s) 
  "it" "suffices" "to" "show" "that"
  constr(t) :=
  new_goal_verified_apply s t.*)

(** A powerful forward reasoning tactic. 
    The sequential trying of auto and eauto 
    is there because eauto can be much slower. 
    TODO: is this what we want? *)
Ltac new_hyp_verified_pose_proof s t u:=
  assert (u : t) by timeout 5 (first [ solve [auto using s with *]
                          | solve [eauto using s with *]
                          | solve [firstorder using s]
                          | solve [firstorder (eauto with *) using s]
                          | idtac "Waterproof could not find a proof. If you believe the statement should hold, try making a smaller step"]).

Tactic Notation "By" constr(s)
  "it" "holds" "that" constr(t) "("ident(u)")"
  := new_hyp_verified_pose_proof s t u.

(*Tactic Notation "By" constr(s0) "," constr(s1)
  "it" "holds" "that" constr(t) "("ident(u)")"
  :=*)

(* TODO: align syntax with "By ... it holds that" *)
Tactic Notation "It" "holds" "that"
  constr(t) "(" ident(u) ")" :=
  assert (u : t) by first [ wp_power
                          | idtac "Waterproof could not find a proof. If you believe the statement should hold, try making a smaller step"].

Ltac conclude_proof t :=
  match goal with
  | [|-t] => idtac
  | _ => (idtac "Warning: The statement you provided does not exactly correspond to the current goal. This can make your proof less readable."; change t || fail "The provided statement cannot be converted to the current goal. If you are trying to prove an intermediate step, add a name to your hypothesis between brackets at the end of the sentence.")
  end; first [wp_power | fail "Waterproof could not find a proof. Try making a smaller step."].

Tactic Notation "It" "holds" "that" constr(t) :=
  conclude_proof t.

Tactic Notation "It" "follows" "that" constr(t) :=
  conclude_proof t.

Tactic Notation "It" "suffices" "to" "show" "that"
  constr(t) :=
  enough t by ( wp_power || fail "Waterproof could not confirm that proving the statement would be enough.").


Tactic Notation "It" "suffices" "to" "show" "that"
  constr(t) "by" tactic(tac) :=
  enough t by tac.


Tactic Notation "Write" "goal" "using" constr(t) "as" 
  constr(s) :=
  let u := fresh in
    assert (u : t) by wp_power;
  rewrite u;
  enough s by wp_power;
  clear u.

Tactic Notation "Write" ident(H) "using" constr(t) "as"
  constr(s) :=
  let u := fresh in
    assert (u : t) by wp_power;
  rewrite u in H;
  clear u.

Tactic Notation "This" "follows" "by" "assumption" := 
  assumption.

Tactic Notation "We" "claim" "that" 
  constr(t) "(" ident(u) ")" :=
  assert (u : t).

Tactic Notation "Rewrite" "using" constr(t) :=
  let u := fresh in
    assert (u : t) by wp_power;
  rewrite u;
  clear u.

Tactic Notation "rewrite" "using" constr(t) :=
  let u := fresh in
    assert (u : t) by wp_power;
  rewrite u;
  clear u.

Tactic Notation "Rewrite" "using" constr(t) "in" ident(s):=
  let u := fresh in
    assert (u : t) by wp_power;
  rewrite u in s;
  clear u.

Tactic Notation "rewrite" "using" constr(t) "in" ident(s):=
  let u := fresh in
    assert (u : t) by wp_power;
  rewrite u in s;
  clear u.

Tactic Notation "Rewrite" "<-" "using" constr(t) :=
  let u := fresh in 
    assert (u : t) by wp_power;
  rewrite<-u;
  clear u.

Tactic Notation "replacing" constr(s) "with" constr(t) :=
  replace s with t by wp_power.

Tactic Notation "Apply" uconstr(t) :=
  apply t.


Tactic Notation "Unfold" constr(t) :=
  unfold t.

Tactic Notation "Unfold" constr(t) "in" ident(s):=
  unfold t in s.

Tactic Notation "Expand" "the" "definition" "of" reference(t) :=
  unfold t.

Tactic Notation "Expand" "the" "definition" "of" 
  reference(t) "in" ident(s) :=
  unfold t in s.

Tactic Notation "Write" ident(s) "as" constr(t) :=
  change t in s.

Ltac trans_ineq eq_or_ineq := 
  match goal with 
  | [|-?x ≤ ?z] => 
    match (type of eq_or_ineq) with 
    | (x ≤ ?y) => apply (Rle_trans x y z eq_or_ineq)
    | _ => idtac "not a less-than-or-equal-to inequality"
    end
  | _ => idtac "Goal is not a less-than-or-equal-to inequality."
  end.

Tactic Notation "Define" ident(u) ":=" constr(t) :=
  set (u := t).


Tactic Notation "This" "follows" "by" "reflexivity" :=
  reflexivity.

Tactic Notation "Simplify" "what" "we" "need" "to" "show" :=
  simpl.

Hint Resolve Rmult_gt_0_compat : real.
Hint Resolve Rmult_lt_0_compat : real.

Ltac contra :=
  match goal with
  | [|- ?X] => destruct (classic X); try assumption
  | _ => idtac "failure of tactic"
  end.

Tactic Notation "We" "argue" "by" "contradiction" :=
  contra.
  
Tactic Notation "Contradiction" := contradiction.

Hint Resolve not_all_not_ex : contra_hints.
Hint Resolve not_all_ex_not : contra_hints.
Hint Resolve not_ex_all_not : contra_hints.
Hint Resolve ex_not_not_all : contra_hints.
Hint Resolve all_not_not_ex : contra_hints.


(********* own notations *************)


Notation "'subset' U" := 
  (Ensemble U) (at level 50). 

Notation "'setOfSubsets' U" := 
  (Ensemble (subset U)) (at level 50). 

Variable U : Type. 


Notation "∅" := 
  (Empty_set U). 

Notation "'Ω'" := 
  (Full_set U) (at level 60). 

Notation "A ∩ B" := 
  (Intersection _ A B) (at level 50). 

Notation "A ∪ B" := 
  (Union _ A B) (at level 50). 

Notation "A \ B" := 
  (Setminus _ A B) (at level 50). 

Notation "x ∈ A" := 
  (In _ A x) (at level 55). 

Notation "x ∉ A" :=  
  (¬ In _ A x) (at level 55). 

Notation "A ⊂ B" := 
  (Included _ A B) (at level 50). 

Notation "A B 'are disjoint'" := 
  (Disjoint _ A B) (at level 50). 

Notation "｛ x : T | P ｝" := 
  (fun (x : T) ↦ P) (x at level 99).

Tactic Notation "We" "prove" "equality" "by" "proving" "two" "inclusions" :=
   apply Extensionality_Ensembles; 
   unfold Same_set; 
   unfold Included;
   split.



Lemma complement_empty_is_full : 
  Ω = (Ω \ ∅). 
It holds that (Ω = (Ω \ ∅)). 
Qed. 

Lemma complement_full_is_empty : 
  ∅ = (Ω \ Ω). 
This equality is trivial.
Qed.

Lemma setminus_empty : 
  ∀ A : subset U, A \ ∅ = A. 
This equality is trivial.
Qed. 

Lemma intersection_full : 
  ∀ A : subset U, (Ω ∩ A) = A. 
This equality is trivial.
Qed.

Lemma intersection_empty : 
  ∀ A : subset U, (A ∩ ∅) = ∅. 
This equality is trivial.
Qed. 

Lemma complement_as_intersection : 
  ∀ A B : subset U, 
    A \ B = (Ω \ B) ∩ A. 
This equality is trivial.
Qed. 

Lemma intersection_symmetric : 
  ∀ A B : subset U, A ∩ B = B ∩ A. 
This equality is trivial.
Qed. 

Section set_lemmas.
Variable A B : subset U.
Lemma sets_1 : A ∪ B = B ∪ A.
This equality is trivial.
Qed.

Lemma domination_union : Ω ∪ A = Ω.
This equality is trivial.
Qed.

Lemma sets_3 : ∅ ∪ A = A.
This equality is trivial.
Qed.

Lemma idempotent_union : A ∪ A = A.
This equality is trivial.
Qed. 

Lemma idempotent_intersection : A ∩ A = A.
This equality is trivial.
Qed. 

Lemma complement_law_union : A ∩ (Ω \ A) = Ω.
This equality is trivial.
End set_lemmas.

(*
Hint Rewrite intersection_empty.
Hint Rewrite <- complement_full_is_empty.
Hint Rewrite <- complement_empty_is_full.
Hint Rewrite setminus_empty.
Hint Rewrite intersection_full.
Hint Resolve intersection_symmetric : sets.
*)

Lemma empty_disjoint : 
  ∀ A B : subset U, Disjoint _ A ∅. 

Proof. 
try intro A;
try intro B(*; 
disjoint_tool;*)
(*intros x*).
We claim that (A ∩ B = B ∩ A) (xx).
This equality is trivial.
(*try rewrite using .*)
It holds that 
  ((A ∩ ∅) = ∅) (int_empty). 
Write goal using ((A ∩ ∅) = ∅) as (x ∉ ∅). 
It holds that (x ∉ ∅). 
Qed. 



Lemma disjoint_symmetric : 
  ∀ A B : subset U, (Disjoint _ A B) ⇒ (Disjoint _ B A). 

Proof. 
Take A : (subset U). 
Take B : (subset U). 
Assume A_B_disjoint. 
It holds that 
  ((A ∩ B) = (B ∩ A)) (AB_is_BA).
destruct A_B_disjoint.
Write H using ((A ∩ B) = (B ∩ A)) 
  as (∀ x : U, x ∉ (B ∩ A)). 
It follows that (Disjoint U B A). 
Qed. 
Hint Resolve disjoint_symmetric : sets.
(*include last two in library? Should be trivial. *)

Ltac destruct_element := 
  match goal with 
    | [H : ?v ∈ ?A |- _ ] 
      => destruct H; wp_power; try wp_power
  end.

Ltac sets_to_logic := 
  try intro A;
  try intro B;
  try intro C;
  try intro H;
  try destruct_element; 
  try contra.

Lemma union_to_or : 
  ∀ A B : (subset U), ∀ x : U, 
    x ∈ (A ∪ B) ⇒ (x ∈ A ∨ x ∈ B).

Proof. 
sets_to_logic.
Qed. 



Lemma not_in_comp : 
  ∀ A : subset U, ∀ x : U, 
    x ∉ (Ω \ A) ⇒ x ∈ A.

Proof. 
try intro A.
  try intro x.
  try intro C.
  try intro H.
  try destruct_element.
  try contra. (*
  try contradiction.
sets_to_logic.
Take A : (subset U); Take x : U. 
Assume x_not_in_complement. 
We argue by contradiction.
*)
It holds that (x ∈ (Ω \ A)) (x_in_complement).

Contradiction. 
Qed.

Chapter trivial_σ_algebra. 
(*First of course we need to define $\{Ω,∅\}$: *) 

Definition F := 
    ｛ A : subset U | (A = Ω) ∨ (A = ∅)｝.  

(*For ``F`` to be a σ-algebra, we need to check three conditions: Ω needs to be in the set, the set must be closed under taking complements and it must be closed under taking the countable union of a collection of sets. *) 

Lemma trivial_salgebra : 
  ∀ A  : subset U, A ∈ F 
    ⇒ (Ω \ A) ∈ F.
Proof.
(* Second point: Prove that F is closed under complement*)
We need to show that 
  (∀ A  : subset U, A ∈ F 
    ⇒ (Ω \ A) ∈ F). 
Take A : (subset U). 
Assume A_in_F : (A ∈ F). 
Write A_in_F as 
  ((A = Ω) ∨ (A = ∅)).
Because A_in_F either A_is_full or A_is_empty. 
(* A = Ω: *)
Write goal using (A = Ω) 
  as ((Ω \ Ω) ∈ F ). 
Write goal using ((Ω \ Ω) = ∅) 
  as (∅ ∈ F). 
It holds that (∅ ∈ F). 

(* A = ∅: *)
Write goal using (A = ∅) 
  as ((Ω \ ∅) ∈ F). 
Write goal using (Ω \ ∅ = Ω) as (Ω ∈ F). 
It holds that (Ω ∈ F). 
