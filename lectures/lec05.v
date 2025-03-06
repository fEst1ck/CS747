Require Import List CpdtTactics Lia Utf8.
Require Import PeanoNat Lia.
Require Import Wf_nat.
Import ListNotations.
Set Implicit Arguments.

Module gcd.
(* Here is an attempt to define the [gcd] function in Rocq, using the  Euclidean Algorithm. *)

Fail Fixpoint gcd_rec (a b: nat): nat :=
  if Nat.eq_dec b 0 then a else gcd_rec b (a mod b).
(* It fails because the recursive call is not structurally decreasing. Rocq needs convincing that the recursive call is decreasing. *)

(* Let's use well-founded induction on [Acc] to define [gcd].

First, let's review the idea of well-founded induction.
What does it mean for a relation to be well-founded?

    well_founded = λ (A : Type) (R : A → A → Prop), ∀ a : A, Acc R a

    Inductive Acc (A : Type) (R : A → A → Prop) (x : A) : Prop :=
      Acc_intro : (∀ y : A, R y x → Acc R y) → Acc R x.
  
  The "accessible" notion is capturing the idea that our relation has no infinite descending chains. "Well-founded" means that every element is accessible.

  In the case of <, there is a least element, namely 0.  So if we are always going down in the relation, we will eventually get to 0.  We can prove that < is well-founded (see last lecture).  *)

Fixpoint gcd_rec (a b: nat) (ACC: Acc lt b) {struct ACC}: nat.
Proof.
  refine (if Nat.eq_dec b 0 then a else gcd_rec b (a mod b) _).
  (* need to put a subproof of [ACC] in the hole *)
  inversion ACC as [H].
  apply H.
  apply Nat.mod_bound_pos; lia.
  (* There is a lemma we can use to streamline Acc proofs like this *)
Abort.

About Acc_inv.
(* Acc_inv : ∀ [A : Type] [R : A → A → Prop] [x : A], Acc R x → 
             ∀ [y : A], R y x → Acc R y *)

Fixpoint gcd_rec (a b: nat) (ACC: Acc lt b) : nat.
Proof.
  refine (
    if Nat.eq_dec b 0 then a else
      gcd_rec b (a mod b) (Acc_inv ACC _)
  ).
  apply Nat.mod_bound_pos; lia.
  Show Proof. (* that's a giant proof term *)
Abort.

Program Fixpoint gcd_rec (a b: nat) (ACC: Acc lt b) {struct ACC} : nat :=
if Nat.eq_dec b 0 then a else
  @gcd_rec b (a mod b) (Acc_inv ACC _).
Next Obligation.
apply Nat.mod_bound_pos; lia.
Defined.

Print gcd_rec. (* nice and clean! *)

(* Rocq determines that argument [b] can be made implicit. We don't want that. *)
Arguments gcd_rec a b ACC: clear implicits.

(* Test [gcd_rec] *)
Eval compute in @gcd_rec 12 15 (lt_wf _).
Eval compute in @gcd_rec 320 128 (lt_wf _).

(* We can extract the recursive function to OCaml. *)
Require Import Extraction.
Extraction "gcd" gcd_rec.

(* We want to prove that [gcd_rec] is correct.
   First, we need a notion of the greatest common divisor. *)

Notation "( n | m )" := (Nat.divide n m) (at level 0).
About Nat.divide.

Definition is_gcd (d a b: nat) : Prop :=
  0 ≤ d ∧ (d | a) ∧ (d | b) ∧
  (∀ d', (d' | a) → (d' | b) → d' ≤ d).

(* Properties of the recursive function [gcd_rec] can be proved by "well-founded induction". *)

Check (well_founded_induction lt_wf).
(*
  well_founded_induction lt_wf
     : ∀ P : nat → Set, (∀ x : nat, (∀ y : nat, y < x → P y) → P x)
        → ∀ a : nat, P a
*)

Definition gcd a b := gcd_rec a b (lt_wf _).

Theorem gcd_correct:
  ∀ a b, 0 < a → is_gcd (gcd a b) a b.
Proof.
  intros a b Pos.
  induction b.
  + admit. (* Base case should be easy. Let's skip it for now. *)
  + cbn.
Abort.

Local Hint Resolve
  Nat.divide_refl Nat.divide_0_r Nat.divide_pos_le : core.

Lemma gcd_rec_correct:
  ∀ b ACC a, 0 < a → is_gcd (gcd_rec a b ACC) a b.
Proof.
  induction b as [b IH] using (well_founded_induction lt_wf).
  destruct ACC as [Acc_Inv]. (* Important, as we want the proof term to be structurally recursive *)

  intros a Pos.
  destruct (Nat.eq_dec b 0) as [ Heq | Heq ] eqn:Heq_dec.
  - subst. repeat split; intuition (auto || lia).
  - cbn. rewrite Heq_dec.

    (* Let's shorten the proof term [gcd_rec_obligation_1 a Heq] *)
    pose (gcd_rec_obligation_1 a Heq) as Lt. simpl in Lt.
    fold Lt.

    (* We use the IH to assert the result of the recursive call is correct *)
    assert
      (is_gcd (gcd_rec b (a mod b) (Acc_Inv _ Lt)) b (a mod b)) as H
      by (apply IH; lia).
    destruct H as [H1 [H2 [H3 H4]]].
    repeat split.
    + lia.
    + (* H2 and H3 are enough to prove the subgoal. *)
      generalize H2 H3.
      (* Abstract away the common subexpression *)
      generalize (gcd_rec b (a mod b) (Acc_Inv (a mod b) Lt)).
      clear.  intros n H2 H3.
      (*  H2:             n * z1 = b
          H3:             n * z2 = a mod b
          Nat.div_mod_eq: a mod b + b * floor(a/b) = a
          So:
          n * z2 + n * z1 * floor(a/b) = a
          n * (z2 + z1 * floor(a/b)) = a
      *)
      destruct H2 as [z1 H2]. destruct H3 as [z2 H3].
      specialize (Nat.div_mod_eq a (z1 * n)) as H.
      exists (z2 + z1 * (a / b)).
      subst.
      lia.
    + apply H2.
    + intros d Ha Hb.  apply H4; [apply Hb | ].
      clear - Ha Hb.
      (* Ha:             d * k1 = a
         Hb:             d * k2 = b
         Nat.div_mod_eq: a - b * floor(a/b)) = a mod b
         So:
         d * (k1 - k2 * floor(a/b)) = a mod b
      *)
      destruct Ha as [k1 Ha]. destruct Hb as [k2 Hb].
      exists (k1 - k2 * (a / b)).
      specialize (Nat.div_mod_eq a b) as H.
      rewrite Nat.mul_comm.
      rewrite Nat.mul_sub_distr_l.
      lia.
Qed.

Theorem gcd_correct:
  ∀ a b, 0 < a → is_gcd (gcd a b) a b.
Proof.
  intros.
  apply gcd_rec_correct.
  lia.
Qed.

(* Turns out that Rocq is now smart enough to allow this definition
of gcd to go through! *)
Fixpoint gcd_rec' a b :=
  match b with
   | O => a
   | S b' => gcd_rec' b (a mod (S b'))
  end.

End gcd.

(*******************************************************)
(* Lambda calculus *)
(*******************************************************)

(** Formal Reasoning About Programs <http://adam.chlipala.net/frap/> *)
Require Import Frap.

Module Ulc.
Inductive exp : Set :=
| Var (x : var)
| Abs (x : var) (body : exp)
| App (e1 e2 : exp).

(* Key operation: within [e], changing every occurrence of variable [x] into
   [rep]. *)
Fixpoint subst (rep : exp) (x : var) (e : exp) : exp :=
  match e with
  | Var y =>
    if y ==v x then rep else Var y
  | Abs y e1 =>
    Abs y (if y ==v x then e1 else subst rep x e1)
    (* capture-avoiding substitution *)
  | App e1 e2 =>
    App (subst rep x e1) (subst rep x e2)
  end.

(** * Big-step semantics *)

(* We evaluate any closed term into a value (that is, an [Abs]). *)
Inductive eval : exp → exp → Prop :=
| BigAbs : ∀ x e,
  eval (Abs x e) (Abs x e)
| BigApp : ∀ e1 x e1' e2 v2 v,
  eval e1 (Abs x e1')
  → eval e2 v2
  → eval (subst v2 x e1') v
  → eval (App e1 e2) v.

(* Note that we omit a [Var] case, since variable terms can't be *closed*,
   and therefore they aren't meaningful as top-level programs.
   Also, we're cheating a bit here, *assuming* that the term is also closed. *)

(* Which terms are values, that is, final results of execution? *)
Inductive value : exp → Prop :=
| Value : ∀ x e, value (Abs x e).

Local Hint Constructors eval value : core.

(* Every value executes to itself. *)
Theorem value_eval : ∀ v, value v → eval v v.
Proof.
  inversion 1; eauto.
Qed.

Local Hint Resolve value_eval : core.

(* Conversely, let's prove that [eval] only produces values. *)
Theorem eval_value : ∀ e v, eval e v → value v.
Proof.
  induction 1; eauto.
Qed.

Local Hint Resolve eval_value : core.

(* Some notations, to let us write more normal-looking lambda terms *)
Coercion Var : var >-> exp.
Notation "\ x , e" := (Abs x e) (at level 50).
Infix "@" := App (at level 49, left associativity).

(* Believe it or not, this is a Turing-complete language!  Here's an example
   nonterminating program. *)
Example omega := (\"x", "x" @ "x") @ (\"x", "x" @ "x").

Theorem omega_no_eval : ∀ v, eval omega v → False.
Proof.
  intros v.
  remember omega as e eqn:He.
  induction 1.
  { discriminate He. }
  invert He.
  invert H.
  invert H0.
  simplify.
  apply IHeval3.
  trivial.
Qed.

(** Church Numerals, everyone's favorite example of lambda terms in
    action *)
Module Church_Numerals.

(* Here are some curious definitions. *)
Definition zero := \"f", \"x", "x". (* [λf. λx. f^0 (x)] *)
Definition one := \"f", \"x", "f" @ "x". (* [λf. λx. f^1 (x)] *)
Definition two := \"f", \"x", "f" @ ("f" @ "x"). (* [λf. λx. f^2 (x)] *)
(* A number [n] is represented as a function [λf. λx. f^n (x)] which,
   given a function [f], returns a function that is the [n]-fold
   composition of [f]. *)
   
(* The successor function *)
Definition succ := \"n", \"f", \"x", "f" @ ("n" @ "f" @ "x"). (* [λn. λf. λx. f (f^n (x))] *)

(* We can build up any natural number [n] as [succ^n @ zero].  Let's prove
  * that, in fact, these definitions constitute a workable embedding of the
  * natural numbers in lambda-calculus. *)

(* Church encoding of natural numbers *)
Fixpoint church (n : nat) : exp :=
  match n with
  | O => \"f", \"x", "x"
  | S n' => \"f", \"x", "f" @ (church n' @ "f" @ "x")
  end.

(* Let's formalize our definition of what it means to represent a number. *)
Definition represents (e : exp) (n : nat) :=
  eval e (church n).

(* Zero passes the test. *)
Theorem zero_ok : represents zero 0.
Proof.
  unfold zero, represents, church.
  econstructor.
Qed.

(* So does our successor operation. *)
Theorem succ_ok : ∀ e n, represents e n → represents (succ @ e) (S n).
Proof.
  unfold succ, represents.
  simplify.
  econstructor; eauto.
Qed.

(* What's basically going on here?  The representation of number [n] is [N]
  * such that, for any function [f]:
  *   N(f) = f^n
  * That is, we represent a number as its repeated-composition operator.
  * So, given a number, we can use it to repeat any operation.  In particular,
  * to implement addition, we can just repeat [succ]! *)
Definition add := \"n", \"m", "n" @ succ @ "m".

(* Our addition works properly on this test case. *)
Example add_1_2 : exists v,
  eval (add @ (succ @ zero) @ (succ @ (succ @ zero))) v
  /\ eval (succ @ (succ @ (succ @ zero))) v.
Proof.
  eexists; propositional.
  + repeat (econstructor; simplify).
  + repeat econstructor.
Qed.

(* Multiplication is just repeated addition. *)
Definition mult := \"n", \"m", "n" @ (add @ "m") @ zero.

Example mult_1_2 : exists v,
  eval (mult @ (succ @ zero) @ (succ @ (succ @ zero))) v
  /\ eval (succ @ (succ @ zero)) v.
Proof.
  eexists; propositional.
  + repeat (econstructor; simplify).
  + repeat econstructor.
Qed.

End Church_Numerals.

(** * Small-step semantics *)

Inductive step : exp → exp → Prop :=
(* The Beta rule is the real action of the semantics. *)
| Beta : ∀ x e v,
  value v → step (App (Abs x e) v) (subst v x e)
(* APP1 and APP2: two bureaucractic rules *)
| App1 : ∀ e1 e1' e2,
  step e1 e1' ->
  step (App e1 e2) (App e1' e2)
| App2 : ∀ v e2 e2',
  value v → step e2 e2' ->
  step (App v e2) (App v e2').
(* Note how that last rule enforces a deterministic evaluation order!  We call it *call-by-value*. *)

Local Hint Constructors step : core.

(* Here we now go through a proof of equivalence between big- and small-step semantics, though we won't spend any further commentary on it. *)

Lemma small_to_big' : ∀ e1 e2,
  step e1 e2 → ∀ v, eval e2 v → eval e1 v.
Proof.
  induct 1; simplify; eauto.
  + invert H0.
    econstructor.
    apply IHstep.
    eassumption.
    eassumption.
    assumption.
  + invert H1.
    econstructor.
    eassumption.
    apply IHstep.
    eassumption.
    assumption.
Qed.

Theorem small_to_big : ∀ e v,
  step^* e v → value v → eval e v.
Proof.
  induct 1.
  + eauto.
  + intro; eapply small_to_big'; eauto.
Qed.

Lemma step_app1 : ∀ e1 e1' e2,
  step^* e1 e1' → step^* (App e1 e2) (App e1' e2).
Proof.
  induct 1; eauto.
Qed.

Lemma step_app2 : ∀ e2 e2' v,
  value v → step^* e2 e2' → step^* (App v e2) (App v e2').
Proof.
  induct 2; eauto.
Qed.

Theorem big_to_small : ∀ e v,
  eval e v → step^* e v.
Proof.
  induct 1; eauto.
  eapply trc_trans.
  + apply step_app1.
    eassumption.
  + eapply trc_trans.
    - eapply step_app2; eauto.
    - econstructor; eauto.
Qed.
End Ulc.

(*******************************************************)
(* Simpliy Typed Lambda calculus *)
(*******************************************************)

(** * Now we turn to a variant of lambda calculus with static type-checking.  This variant is called *simply typed* lambda calculus, and *simple* has a technical meaning, basically meaning "no type-level polymorphism". *)

Module Stlc.

(* We add expression forms for numeric constants and addition. *)
Inductive exp : Set :=
| Var (x : var)
| Const (n : nat)    (* new construct *)
| Plus (e1 e2 : exp) (* new construct *)
| Abs (x : var) (e1 : exp)
| App (e1 e2 : exp).

(* Values (final results of evaluation) *)
Inductive value : exp → Prop :=
| VConst : ∀ n, value (Const n)
| VAbs : ∀ x e1, value (Abs x e1).

(* Substitution. Assumes [e1] is closed. *)
Fixpoint subst (e1 : exp) (x : string) (e2 : exp) : exp :=
  match e2 with
    | Var y => if y ==v x then e1 else Var y
    | Const n => Const n
    | Plus e2' e2'' => Plus (subst e1 x e2') (subst e1 x e2'')
    | Abs y e2' => Abs y (if y ==v x then e2' else subst e1 x e2')
    | App e2' e2'' => App (subst e1 x e2') (subst e1 x e2'')
  end.

(* Small-step, call-by-value evaluation *)

Inductive step : exp → exp → Prop :=
(* These rules are the real action of the semantics. *)
| Beta : ∀ x e v,
    value v
    → step (App (Abs x e) v) (subst v x e)
| Add : ∀ n1 n2,
    step (Plus (Const n1) (Const n2)) (Const (n1 + n2))
(* Bureaucratic rules encoding evaluation order. *)
| App1 : ∀ e1 e1' e2,
    step e1 e1'
    → step (App e1 e2) (App e1' e2)
| App2 : ∀ v e2 e2',
    value v
    → step e2 e2'
    → step (App v e2) (App v e2')
| Plus1 : ∀ e1 e1' e2,
    step e1 e1'
    → step (Plus e1 e2) (Plus e1' e2)
| Plus2 : ∀ v e2 e2',
    value v
    → step e2 e2'
    → step (Plus v e2) (Plus v e2').

(* That language is suitable to describe with a static *type system*. Here's our modest, but countably infinite, set of types. *)
Inductive type :=
| Nat : type               (* Numbers *)
| Fun : type → type → type (* Functions *).

Locate "_ $? _".
Locate "_ $+ ( _ , _ )".

(* Our typing relation (also often called a "judgment") uses *typing contexts to map free variables to their types. *)
Inductive has_ty : fmap var type → exp → type → Prop :=
| HtVar : ∀ Γ x t,
  Γ $? x = Some t
  → has_ty Γ (Var x) t
| HtConst : ∀ Γ n,
  has_ty Γ (Const n) Nat
| HtPlus : ∀ Γ e1 e2,
  has_ty Γ e1 Nat
  → has_ty Γ e2 Nat
  → has_ty Γ (Plus e1 e2) Nat
| HtAbs : ∀ Γ x e1 t1 t2,
  has_ty (Γ $+ (x, t1)) e1 t2
  → has_ty Γ (Abs x e1) (Fun t1 t2)
| HtApp : ∀ Γ e1 e2 t1 t2,
  has_ty Γ e1 (Fun t1 t2)
  → has_ty Γ e2 t1
  → has_ty Γ (App e1 e2) t2.

Local Hint Constructors value step has_ty : core.

(* Some notation to make it more pleasant to write programs *)
Infix "-->" := Fun (at level 60, right associativity).
Coercion Const : nat >-> exp.
Infix "^+^" := Plus (at level 50).
Coercion Var : var >-> exp.
Notation "\ x , e" := (Abs x e) (at level 51).
Infix "@" := App (at level 49, left associativity).

(* Some examples of well-typed programs *)

Example one_plus_one : has_ty $0 (1 ^+^ 1) Nat.
Proof.
  repeat (econstructor; simplify).
Qed.

Example add : has_ty $0 (\"n", \"m", "n" ^+^ "m") (Nat --> Nat --> Nat).
Proof.
  repeat (econstructor; simplify).
Qed.

Example eleven : has_ty $0 ((\"n", \"m", "n" ^+^ "m") @ 7 @ 4) Nat.
Proof.
  repeat (econstructor; simplify).
Qed.

Example seven_the_long_way : has_ty $0 ((\"x", "x") @ (\"x", "x") @ 7) Nat.
Proof.
  repeat (econstructor; simplify).
Qed.

(** What is a type system good for?  Well, for one thing, it helps guarantee that the program always runs without getting into undefined behaviour – that is, the program never goes wrong.  If a type system provides that guarantee, we say it is "type-safe".  More precisely, we say that a type system is *type-safe* if every well-typed program is guaranteed not to go wrong.  Let's prove that property for our type system. *)

(* First, we formalize the notion of "unstuck". *)
Definition unstuck e := value e \/ (∃ e', step e e').

(* What we want to show eventually: well-typed programs never gets stuck, at this time or in the future.

      has_ty $0 e t /\ e -->* e'
      → unstuck e'

   We are going to use a classic proof technique to establish this invariant.  There are two steps involved:

   - *Progress*: Well-typed programs are always unstuck at this time.

      has_ty $0 e t → unstuck e.

   - *Preservation*: If a well-typed program takes a step, the result is also well-typed.

      has_ty $0 e t → e --> e' → has_ty $0 e' t.

   Together, these two properties imply that well-typed programs never gets stuck, at this time or in the future.
*)

Lemma progress : ∀ e t, has_ty $0 e t → unstuck e.
Proof.
unfold unstuck; induct 1; simplify; try equality.

+ left.
  constructor.

+ destruct IHhas_ty2; destruct IHhas_ty1; simplify; try reflexivity.
  (* intuition idtac. *)
  (* propositional. *)

  - right.
    (* Some automation is needed here to maintain compatibility with
       name generation in different Rocq versions. *)
    match goal with
    | [ H1 : value e1, H2 : has_ty $0 e1 _ |- _ ] => invert H1; invert H2
    end.
    match goal with
    | [ H1 : value e2, H2 : has_ty $0 e2 _ |- _ ] => invert H1; invert H2
    end.
    exists (Const (n + n0)).
    constructor.

  - match goal with
    | [ H : exists x, _ |- _ ] => invert H
    end.
    right.
    exists (x ^+^ e2).
    constructor.
    assumption.

  - match goal with
    | [ H : exists x, _ |- _ ] => invert H
    end.
    right.
    exists (e1 ^+^ x).
    apply Plus2.
    assumption.
    assumption.

  - match goal with
    | [ H : exists x, _ |- _ ] => invert H
    end.
    right.
    exists (x ^+^ e2).
    constructor.
    assumption.

+ left.
  constructor.

+ propositional.

  - right.
    match goal with
    | [ H1 : value e1, H2 : has_ty $0 e1 _ |- _ ] => invert H1; invert H2
    end.
    exists (subst e2 x e0).
    constructor.
    assumption.

  - match goal with
    | [ H : exists x, _ |- _ ] => invert H
    end.
    right.
    exists (x @ e2).
    constructor.
    assumption.

  - match goal with
    | [ H : exists x, _ |- _ ] => invert H
    end.
    right.
    exists (e1 @ x).
    constructor.
    assumption.
    assumption.

  - match goal with
    | [ H : exists x, step e1 _ |- _ ] => invert H
    end.
    right.
    exists (App x e2).
    constructor.
    assumption.
Qed.

(* Inclusion between typing contexts is preserved by adding the same new mapping to both. *)
Lemma weakening_override : ∀ (Γ Γ' : fmap var type) x t,
  (∀ x' t', Γ $? x' = Some t' → Γ' $? x' = Some t')
  → (∀ x' t', Γ $+ (x, t) $? x' = Some t'
                    → Γ' $+ (x, t) $? x' = Some t').
Proof.
  simplify.
  cases (x ==v x'); simplify; eauto.
Qed.

(* This lemma lets us transplant a typing derivation into a new context that includes the old one. *)
Lemma weakening : ∀ Γ e t,
  has_ty Γ e t
  → ∀ Γ', (∀ x t, Γ $? x = Some t → Γ' $? x = Some t)
    → has_ty Γ' e t.
Proof.
  induct 1; simplify.

  constructor.
  apply H0.
  assumption.

  constructor.

  constructor.
  apply IHhas_ty1.
  assumption.
  apply IHhas_ty2.
  assumption.

  constructor.
  apply IHhas_ty.
  apply weakening_override.
  assumption.

  econstructor.
  apply IHhas_ty1.
  assumption.
  apply IHhas_ty2.
  assumption.
Qed.

(* Replacing a variable with a properly typed term preserves typing. *)
Lemma substitution : ∀ Γ x t' e t e',
  has_ty (Γ $+ (x, t')) e t
  → has_ty $0 e' t'
  → has_ty Γ (subst e' x e) t.
Proof.
  induct 1; simplify.

  cases (x0 ==v x).

  simplify.
  invert H.
  eapply weakening.
  eassumption.
  simplify.
  equality.

  simplify.
  constructor.
  assumption.

  constructor.

  constructor.
  eapply IHhas_ty1; equality.
  eapply IHhas_ty2; equality.

  cases (x0 ==v x).

  constructor.
  eapply weakening.
  eassumption.
  simplify.
  cases (x0 ==v x1).

  simplify.
  assumption.

  simplify.
  assumption.

  constructor.
  eapply IHhas_ty.
  maps_equal.
  assumption.

  econstructor.
  eapply IHhas_ty1; equality.
  eapply IHhas_ty2; equality.
Qed.

(* OK, now we're almost done. Let's prove [step] preserves typing! *)
Lemma preservation : ∀ e1 e2,
  step e1 e2 → ∀ t, has_ty $0 e1 t
  → has_ty $0 e2 t.
Proof.
  induct 1; simplify.

  invert H0.
  invert H4.
  eapply substitution.
  eassumption.
  assumption.
  
  invert H.
  constructor.

  invert H0.
  econstructor.
  apply IHstep.
  eassumption.
  assumption.

  invert H1.
  econstructor.
  eassumption.
  apply IHstep.
  assumption.

  invert H0.
  constructor.
  apply IHstep.
  assumption.
  assumption.

  invert H1.
  constructor.
  assumption.
  apply IHstep.
  assumption.
Qed.

(* Now we can put it all together to prove that well-typed programs never get stuck, at this time or in the future.

      has_ty $0 e t /\ e -->* e' → unstuck e'

We can reformulate this as a property about a transition system:

      invariantFor (trsys_of e) unstuck

Define the transition system first. *)
Definition trsys_of (e : exp) := {|
  Initial := {e};
  Step := step
|}.

Print invariantFor.

(* Now we can state and prove the main theorem. *)
Theorem type_safety : ∀ e t, has_ty $0 e t
  → invariantFor (trsys_of e) unstuck.
Proof.
  simplify.

  (* Step 1: strengthen the invariant.  In particular, the typing relation is exactly the right stronger invariant!  Our progress theorem proves the required invariant inclusion. *)
  apply invariant_weaken with (invariant1 := fun e' => has_ty $0 e' t).

  + (* Step 2: apply invariant induction, whose induction step turns out to match our preservation theorem exactly! *)
    apply invariant_induction; simplify.
    - (* Base case of invariant induction: initial state satisfies invariant. *)
      equality.
    - (* Inductive case of invariant induction: if one state satisfies invariant and takes a step, the next state satisfies invariant. *)
      eapply preservation; eassumption.

  + (* Step 3: prove the strengthened invariant is indeed stronger. *)
    simplify.
    eapply progress.
    eassumption.
Qed.


(** Let's do that again with more automation... *)

Ltac t0 := match goal with
            | [ H : ex _ |- _ ] => invert H
            | [ H : _ /\ _ |- _ ] => invert H
            | [ |- context[?x ==v ?y] ] => cases (x ==v y)
            | [ H : Some _ = Some _ |- _ ] => invert H

            | [ H : step _ _ |- _ ] => invert1 H
            | [ H : has_ty _ ?e _, H' : value ?e |- _ ] => invert H'; invert H
            | [ H : has_ty _ _ _ |- _ ] => invert1 H
            end; subst.

Ltac t := simplify; propositional; repeat (t0; simplify); try equality; eauto 6.

Lemma progress_snazzy : ∀ e t,
  has_ty $0 e t
  → value e
  \/ (exists e' : exp, step e e').
Proof.
  induct 1; t.
Qed.

Local Hint Resolve weakening_override : core.

Lemma weakening_snazzy : ∀ Γ e t,
  has_ty Γ e t
  → ∀ Γ', (∀ x t, Γ $? x = Some t → Γ' $? x = Some t)
    → has_ty Γ' e t.
Proof.
  induct 1; t.
Qed.

Local Hint Resolve weakening_snazzy : core.

(* Replacing a typing context with an equal one has no effect (useful to guide proof search as a hint). *)
Lemma has_ty_change : ∀ Γ e t,
  has_ty Γ e t
  → ∀ Γ', Γ' = Γ
    → has_ty Γ' e t.
Proof.
  t.
Qed.

Local Hint Resolve has_ty_change : core.

Lemma substitution_snazzy : ∀ Γ x t' e t e',
  has_ty (Γ $+ (x, t')) e t
  → has_ty $0 e' t'
  → has_ty Γ (subst e' x e) t.
Proof.
  induct 1; t.
Qed.

Local Hint Resolve substitution_snazzy : core.

Lemma preservation_snazzy : ∀ e1 e2,
  step e1 e2
  → ∀ t, has_ty $0 e1 t
    → has_ty $0 e2 t.
Proof.
  induct 1; t.
Qed.

Local Hint Resolve progress_snazzy preservation_snazzy : core.

Theorem safety_snazzy : ∀ e t, has_ty $0 e t
  → invariantFor (trsys_of e)
                  (fun e' => value e'
                              \/ exists e'', step e' e'').
Proof.
  simplify.
  apply invariant_weaken with (invariant1 := fun e' => has_ty $0 e' t); eauto.
  apply invariant_induction; simplify; eauto; equality.
Qed.
End Stlc.
