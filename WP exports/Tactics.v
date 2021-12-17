(** # Tactics for Waterproof*)
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
(** *)
(** ## Custom notations*)
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


(** ## A powertool*)
(* TODO: in some cases, eauto has left some existentials.
   this may be undesired, but eauto can be very powerful...
   one option is to let waterproof check whether 
   existentials are created and block this behavior. *)

Ltac wp_power :=
  timeout 60 (first [ solve [auto with *]
        | solve [eauto with *]
        | solve [firstorder (auto with *)]
        | solve [firstorder (eauto with *)]]).
(** *)
(** ## Introducing variables

The following is a strict version of `intro`, that checks the type of the variable to introduce.*)
Ltac intro_strict s t :=
  match goal with
    | [ |- forall _ : t, _ ] => intro s
  end.

(** *)
(** Take an arbitrary element of a certain type.*)
Tactic Notation "Take" ident(s) ":" constr(t):=
  intro_strict s t.


(** *)
(** *)
(** *)
(** Taking two elements of the same type. (To be generalised?)*)
Ltac intros_strict x y t :=
  match goal with
    | [ |- forall _ _ : t, _] => intros x y
  end.

Tactic Notation "Take" ident(x) ident(y) ":" constr(t):=
  intros_strict x y t. 
(** 
Variation of intro tactic that allows one to check that what you assume is really what you need to assume.*)
Ltac assume_strict s t :=
  match goal with
    | [ |- ?u -> _ ] => (change u with t; intro s)
  end.

(** *)
(** Assuming hypotheses.*)
Tactic Notation "Assume" ident(s) :=
  intro s.

Tactic Notation "Assume" ident(s) ":" constr(t) :=
  assume_strict s t.
(** ## Checking the context

The following tactics let the user record in the proof script various aspects of the current context.

The tactic call `goal_check t` checks if the current goal can equivalently be written as `t`, otherwise it fails.*)
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
(** *)
(** ## Choosing variables that exist*)
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
(** *)
(** ## Forward reasoning*)
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


(** *)
(** ## Forward reasoning by automation*)
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
  assert (u : t) by timeout 60 (first [ solve [auto using s with *]
                          | solve [eauto using s with *]
                          | solve [firstorder using s]
                          | solve [firstorder (eauto with *) using s]
                          | idtac "Waterproof could not find a proof. If you believe the statement should hold, try making a smaller step"]).

Ltac new_hyp_verified_pose_proof_no_name s t:=
  assert t by timeout 60 (first [ solve [auto using s with *]
                          | solve [eauto using s with *]
                          | solve [firstorder using s]
                          | solve [firstorder (eauto with *) using s]
                          | idtac "Waterproof could not find a proof. If you believe the statement should hold, try making a smaller step"]).

Tactic Notation "By" constr(s)
  "it" "holds" "that" constr(t) "("ident(u)")"
  := new_hyp_verified_pose_proof s t u.

Tactic Notation "By" constr(s)
  "it" "holds" "that" constr(t)
  := new_hyp_verified_pose_proof_no_name s t.

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
(** *)
(** Now a somewhat experimental and non-standard notation to resolve a goal using another assumption/lemma. The usual `By ... it holds that ...` does not do this, even without adding a name.*)
Tactic Notation "By" constr(u) "it" "holds" "that" constr(t) "which" "concludes" ident(the) "proof":= 
  By u it holds that t (the); 
  apply the. 
(** TODO: preferably deprecate this notation.*)
Tactic Notation "This" "follows" "immediately" :=
  wp_power.

Tactic Notation "follows" "immediately" := 
  wp_power.
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




(** *)
(** ## Applying one of the assumptions*)
Tactic Notation "This" "follows" "by" "assumption" := 
  assumption.
(** *)
(** ## Claims*)
Tactic Notation "We" "claim" "that" 
  constr(t) "(" ident(u) ")" :=
  assert (u : t).
(** ## Rewriting

TODO: add rewrite with at
TODO: add support for rewriting in and at multiple places at once*)
(** *)
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
(** *)
Tactic Notation "replacing" constr(s) "with" constr(t) :=
  replace s with t by wp_power.
(** ## Applying lemmas and theorems*)
Tactic Notation "Apply" uconstr(t) :=
  apply t.
(** *)
(** Note: when using `constr(t)` instead of `uconstr(t)`, the use of wildcareds is no longer possible.

TODO: add option to do an 'apply with'.*)
(** ## Expanding definitions

TODO: add more options for these tactics.*)
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

(** *)
(** ## Strings of (in)equalities

The following tactics should help in situations where in a pen-and-paper proof we would write a string equalities and inequalites.

**Note:** As of now, forward reasoning by "it holds that" seems to be a better option.

The tactic `trans_ineq eq_or_ineq` reduces the inequality in the goal to a new one by using `eq_or_ineq`.*)
Ltac trans_ineq eq_or_ineq := 
  match goal with 
  | [|-?x <= ?z] => 
    match (type of eq_or_ineq) with 
    | (x <= ?y) => apply (Rle_trans x y z eq_or_ineq)
    | _ => idtac "not a less-than-or-equal-to inequality"
    end
  | _ => idtac "Goal is not a less-than-or-equal-to inequality."
  end.
(** *)
(** ## Defining new variables*)
Tactic Notation "Define" ident(u) ":=" constr(t) :=
  set (u := t).
(** *)
(** ## Reflexivity*)
Tactic Notation "This" "follows" "by" "reflexivity" :=
  reflexivity.
(** ## Simplification

TODO: the following tactic notation may need to be improved.*)
Tactic Notation "Simplify" "what" "we" "need" "to" "show" :=
  simpl.
(** ## Proving by induction

Very basic notation, room for improvement. Also not the nicest formulation, but `Proof` is already used. *)
Tactic Notation "We" "prove" "by" "induction" "on" ident(x) := 
  induction x. 
(** ## A tool for set equalities and inclusions*)
(** TODO This tool works well in separate lemmas, but not always in larger contexts. Also, no error message is built in yet.*)
Ltac set_power :=
  timeout 1 (first [ solve [auto with sets]
        | solve [eauto with sets]
        | solve [firstorder (auto with sets)]
        | solve [firstorder (eauto with sets)]]).

Ltac destruct_sets :=
  match goal with 
    | [H : In _ (Intersection _ _ _) _ |- _] => destruct H
    | [H : In _ (Union _ _ _) _  |- _] => destruct H; try set_power
  end.

Ltac trivial_set_inclusion := 
  try intro x;
  try intro H;
  try destruct_sets;
  try contradiction;
  try set_power.

Ltac trivial_set_equality := 
  try intros A;
  try intros B;
  try apply Extensionality_Ensembles;
  try unfold Same_set;
  try unfold Included;
  split;
  trivial_set_inclusion;
  trivial_set_inclusion.


Tactic Notation "This" "equality" "is" "trivial" := 
   trivial_set_equality.
(** 

## Hints*)
Hint Resolve Rmult_gt_0_compat : real.
Hint Resolve Rmult_lt_0_compat : real.
Hint Resolve R_dist_eq : real.
Hint Constructors Union Intersection Disjoint Full_set : sets. 

(*Would like to add the following hint, but this undesirably interferes with workings of e.g. wp_power. Also, what weight to use?
Hint Extern 5 (_ = _) => try trivial_set_equality : sets. 
*)
(** *)
