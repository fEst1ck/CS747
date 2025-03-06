(** * Review of IMP semantics *)

Require Import Bool Arith String List CpdtTactics Utf8.
Open Scope string_scope.

(** IMP syntax -- any CFG -- is just inductive definitions. *)

Definition var := string.

Inductive binop := Plus | Times | Minus.

Inductive aexp : Type := 
| Const : nat -> aexp
| Var : var -> aexp
| Binop : aexp -> binop -> aexp -> aexp.

Inductive bexp : Type := 
| Tt : bexp
| Ff : bexp
| Eq : aexp -> aexp -> bexp
| Lt : aexp -> aexp -> bexp
| And : bexp -> bexp -> bexp
| Or : bexp -> bexp -> bexp
| Not : bexp -> bexp.

Inductive com : Type := 
| Skip : com
| Assign : var -> aexp -> com
| Seq : com -> com -> com
| If : bexp -> com -> com -> com
| While : bexp -> com -> com.


(** Okay, now let's start defining some semantics.
    For aexp and bexp we can directly give a denotation
    to expressions by implementing an interpreter in Rocq.
    However, the meaning of these expressions depends
    on the current state, which maps variables to numbers: *)

Definition state : Type := var -> nat.

Definition get (x:var) (s:state) : nat := s x.

Definition set (x:var) (n:nat) (s:state) : state := 
  fun y => 
    match string_dec x y with 
        | left _ => n 
        | right _ => get y s
    end.

About string_dec.

(* We map binary operator expressions to underlying Rocq
   operators on nat. *)

Definition eval_binop (b:binop) : nat -> nat -> nat := 
  match b with 
    | Plus => Nat.add
    | Times => Nat.mul
    | Minus => Nat.sub
  end.

(* The implementations of eval_aexp and eval_bexp are
   recursive translations into Rocq terms. *)

Fixpoint eval_aexp (e:aexp) (s:state) : nat := 
  match e with 
    | Const n => n
    | Var x => get x s
    | Binop e1 b e2 => (eval_binop b) (eval_aexp e1 s) (eval_aexp e2 s)
  end.

Fixpoint eval_bexp (b:bexp) (s:state) : bool := 
  match b with 
    | Tt => true
    | Ff => false
    | Eq e1 e2 => Nat.eqb (eval_aexp e1 s) (eval_aexp e2 s)
    | Lt e1 e2 => Nat.ltb (eval_aexp e1 s) (eval_aexp e2 s)
    | And b1 b2 => eval_bexp b1 s && eval_bexp b2 s
    | Or b1 b2 => eval_bexp b1 s || eval_bexp b2 s
    | Not b => negb (eval_bexp b s)
  end.

(** We can define notation if we feel like seeing semantic
    brackets in our proofs:
*)

Notation "⟦ A ⟧" := (eval_aexp A).
Notation "⟦ B ⟧" := (eval_bexp B).
Print eval_bexp.

Compute
  eval_aexp (Binop (Const 17) Plus (Var "x"))
  (fun v => if string_dec v "x" then 3 else 0).


(** What goes wrong when we try to give a semantics to
    commands in the same denotational style?
Fixpoint eval_com (c:com) (s: state) : state :=
  match c with
    | Skip => s
    | Assign v a => set v (eval_aexp a s) s
    | Seq c1 c2 =>
        eval_com c2 (eval_com c1 s)
    | If b c1 c2 =>
        match eval_bexp b s with
          | true => eval_com c1 s
          | false => eval_com c2 s
        end
    | While b c =>
        match eval_bexp b s with
          | false => s
          | true => eval_com (Seq c (While b c)) s
        end
  end.
*)

(** * Big-step operational semantics *)

(** The computational/denotational approach to the semantics is
    hopeless, because IMP is Turing-complete. We can't decide whether
    a program terminates, in general, so we can't expect Rocq to
    evaluate commands directly – otherwise we'd be able to decide
    the halting problem.  Instead, we can define a (big-step)
    semantics as an _inductive relation_.

    The elements of [eval_com] are the big-step proof trees for the elements of
    that relation. From the programming perspective, all we are doing is
    defining the data structure of proof trees; dependent types in Rocq let us
    enforce the property that valid program evaluations and proof trees
    correspond.
*)
Inductive eval_com : com -> state -> state -> Prop := 
| Eval_skip : forall s, eval_com Skip s s
| Eval_assign : forall s x e, eval_com (Assign x e) s (set x (eval_aexp e s) s)
| Eval_seq : forall c1 s0 s1 c2 s2, 
               eval_com c1 s0 s1 -> eval_com c2 s1 s2 -> eval_com (Seq c1 c2) s0 s2
| Eval_if_true : forall b c1 c2 s s',
                   eval_bexp b s = true -> 
                   eval_com c1 s s' -> eval_com (If b c1 c2) s s'
| Eval_if_false : forall b c1 c2 s s',
                   eval_bexp b s = false -> 
                   eval_com c2 s s' -> eval_com (If b c1 c2) s s'
| Eval_while_false : forall b c s, 
                       eval_bexp b s = false -> 
                       eval_com (While b c) s s
| Eval_while_true : forall b c s1 s2 s3, 
                      eval_bexp b s1 = true -> 
                      eval_com c s1 s2 -> 
                      eval_com (While b c) s2 s3 -> 
                      eval_com (While b c) s1 s3.

(* Notation "⟨ C , S ⟩ ⇓ S'" := (eval_com C S S') (at level 100). *)

(* y := 1; x := 2; while 0 < x { y := y * 2; x := x - 1 } *)
Definition prog1 := 
  Seq (Assign "y" (Const 1))
  (Seq (Assign "x" (Const 2))
       (While (Lt (Const 0) (Var "x"))
              (Seq (Assign "y" (Binop (Var "y") Times (Const 2)))
                   (Assign "x" (Binop (Var "x") Minus (Const 1)))))).

Fact prog1_prop : forall s, eval_com prog1 (fun _ => 0) s ->
                4 = get "y" s.
Proof.
(** We can use the semantics to prove the results of evaluation.
    But it's quite tedious. Looks ripe for automation! *)
  intros.
  unfold prog1 in H.
  inversion H. clear H. subst.
  inversion H2; clear H2; subst.
  simpl in *.
  inversion H5; clear H5; subst.
  inversion H1; clear H1; subst.
  simpl in *.
  inversion H4; clear H4; subst.
  - cbn in *. (* simpl does not unfold set/get *)
    discriminate.
  - cbn in *.
    clear H1.
    inversion H2; clear H2; subst.
    inversion H1; clear H1; subst.
    cbn in *.
    inversion H5; clear H5; subst.
    cbn in *.
    inversion H6; clear H6; subst; cbn in *.
    + discriminate.
    + clear H1.
      inversion H2; clear H2; subst.
      inversion H1; clear H1; subst.
      cbn in *.
      inversion H6; clear H6; subst.
      cbn in *.
      inversion H5; clear H5; subst; cbn in *.
      * reflexivity.
      * clear - H1.
        discriminate.
Qed.

(** The relational approach also has the advantage that it
   can express nondeterministic semantics, e.g., a "havoc"
   command that arbitrarily changes the state:

| Eval_havoc : forall s s', eval_com Havoc s s'

   A construct like this is not as useless as it might appear.
   For example, it might allow modeling an adversary who can damage the
   contents of memory.
 *)

Definition prog2 := While Tt Skip.

Lemma prog2_div : forall c s1 s2, eval_com c s1 s2 -> c = prog2 -> False.
Proof.
  intros c s1 s2.
  unfold prog2.
  induction 1; crush.
Qed.

Lemma prog2_div' : forall s1 s2, eval_com prog2 s1 s2 -> False.
Proof.
  intros s1 s2.
  unfold prog2.
  induction 1.
Abort.

(** Requires dependent induction (aka induction-inversion) *)
Require Import Program.Equality.
Lemma prog2_div' : forall s1 s2, eval_com prog2 s1 s2 -> False.
Proof.
  intros s1 s2.
  unfold prog2.
  intro H.
  dependent induction H. crush.
Qed.

(** A simple chained tactic *)
Ltac myinv H := inversion H ; subst ; clear H ; cbn in *.

(** This tactic applies when we have a hypothesis involving
   [eval_com] of either a [Seq] or an [Assign].  It inverts the
   hypothesis, and performs substitution, simplifying things.
*)
Ltac eval_inv := 
match goal with 
| [ H : eval_com (Seq _ _) _ _ |- _ ] =>
  myinv H; try (discriminate || reflexivity)
| [ H : eval_com (Assign _ _) _ _ |- _ ] =>
  myinv H; try (discriminate || reflexivity)
| [ H : eval_com (While _ _) _ _ |- _ ] =>
  myinv H; try (discriminate || reflexivity)
end.

Fact prog1_prop' : forall s, eval_com prog1 (fun _ => 0) s ->
                4 = get "y" s.
Proof.
  intros s H.
  unfold prog1 in H.
  repeat eval_inv.
Qed.

(* y := 1; x := 10; while 0 < x { y := y * 2; x := x - 1 } *)
Definition prog10 := 
  Seq (Assign "y" (Const 1))
  (Seq (Assign "x" (Const 10))
       (While (Lt (Const 0) (Var "x"))
              (Seq (Assign "y" (Binop (Var "y") Times (Const 2)))
                   (Assign "x" (Binop (Var "x") Minus (Const 1)))))).

Fact prog10_prop : forall s, eval_com prog10 (fun _ => 0) s ->
                1024 = get "y" s.
Proof.
  intros s H.
  unfold prog10 in H.
  repeat eval_inv.
Qed. (* slow! *)

Theorem seq_assoc : 
  forall c1 c2 c3 s1 s2, 
    eval_com (Seq (Seq c1 c2) c3) s1 s2 -> 
    eval_com (Seq c1 (Seq c2 c3)) s1 s2.
Proof.
  intros c1 c2 c3 s1 s2.
  induction 1.
  (* no induction hypothesis we can use! *)
Abort.

Lemma seq_assoc' : 
  forall c s1 s2, 
    eval_com c s1 s2 -> 
    forall c1 c2 c3,
    (* forall-quantify c1 c2 c3 after the hypothesis that induction is on *)
      c = Seq (Seq c1 c2) c3 -> 
      eval_com (Seq c1 (Seq c2 c3)) s1 s2.
Proof.
  induction 1 ; crush.
  inversion H ; clear H ; subst.
  apply Eval_seq with (s1 := s4).
  - assumption.
  - apply Eval_seq with (s1 := s1).
    + assumption.
    + assumption.
Qed.

Lemma seq_assoc'' : 
  forall c s1 s2, 
    eval_com c s1 s2 -> 
    forall c1 c2 c3,
      c = Seq (Seq c1 c2) c3 -> 
      eval_com (Seq c1 (Seq c2 c3)) s1 s2.
Proof.
  induction 1 ; crush.
  inversion H ; clear H ; subst.
  eapply Eval_seq. (* generates an existential variable to be solved *)
  - eassumption.
  - eapply Eval_seq; eassumption.
Qed.

(** Adds all of the eval_com constructors as hints for auto/crush *)
Hint Constructors eval_com : mydb.

Lemma seq_assoc''' : 
  forall c s1 s2, 
    eval_com c s1 s2 -> 
    forall c1 c2 c3,
      c = Seq (Seq c1 c2) c3 -> 
      eval_com (Seq c1 (Seq c2 c3)) s1 s2.
Proof.
  induction 1 ; crush.
  inversion H ; clear H ; subst.
  econstructor; eauto with mydb.
Qed.

Theorem seq_assoc : 
  forall c1 c2 c3 s1 s2, 
    eval_com (Seq (Seq c1 c2) c3) s1 s2 -> 
    eval_com (Seq c1 (Seq c2 c3)) s1 s2.
Proof.
  intros.
  eapply seq_assoc'''; eauto.
Qed.

(** Returns true when the variable [x] occurs as a subexpression of [a] *)
Fixpoint contains (x:var) (a:aexp) : bool := 
  match a with 
    | Const _ => false
    | Var y => if string_dec x y then true else false
    | Binop a1 _ a2 => contains x a1 || contains x a2
  end.

(** Changing a variable [x] that doesn't occur in [a] doesn't effect the 
   value of [a]. *)
Lemma eval_exp_set : 
  forall s x n a,
    contains x a = false -> 
    eval_aexp a (set x n s) = eval_aexp a s.
Proof.
  induction a; cbn in *.
  - trivial.
  - intro.
    destruct (string_dec x v). (* destruct is a case analysis on a decidable proposition *)
    + discriminate.
    + unfold get, set.
      destruct (string_dec x v) ; crush.
  - intro H.
    destruct (contains x a1).
    + cbn in H. discriminate H.
    + cbn in H. auto.
Qed.  

(** We can commute assignments x:=ax; y:=ay as long as the
   variables don't overlap. *)
Lemma assign_comm : 
  forall x ax y ay s1 s2,
    eval_com (Seq (Assign x ax) (Assign y ay)) s1 s2 -> 
    contains x ay = false -> 
    contains y ax = false -> 
    x <> y -> 
    forall s3, eval_com (Seq (Assign y ay) (Assign x ax)) s1 s3 -> s2 = s3.
(*
               forall z, get z s3 = get z s2.
*)
Proof.
  intros.
  repeat eval_inv.

  Require Import Logic.FunctionalExtensionality.

  apply functional_extensionality.
  intro z.
  unfold set, get.
  destruct (string_dec x z) ; destruct (string_dec y z) ; subst.
  - exfalso.
    auto.
  - erewrite <- eval_exp_set; eauto.
    unfold set, get.
    eauto.
  - apply eq_sym.
    erewrite <- eval_exp_set; eauto.
    unfold set, get.
    eauto.
  - reflexivity.
Qed.


(** * Small-step operational semantics *)

(** Another option for semantics: _small-step_ *)

Inductive step_com : com -> state -> com -> state -> Prop := 
| Step_assign: forall s x e,
       step_com (Assign x e) s
                (Skip) (set x (eval_aexp e s) s)
| Step_seqL: forall c1 c2 c1' s s', step_com c1 s c1' s' ->
                step_com (Seq c1 c2) s (Seq c1' c2) s'
| Step_seqR: forall c s, step_com (Seq Skip c) s c s
| Step_if_true:  forall b c1 c2 s, eval_bexp b s = true ->
                 step_com (If b c1 c2) s c1 s
| Step_if_false: forall b c1 c2 s, eval_bexp b s = false ->
                 step_com (If b c1 c2) s c2 s
| Step_while: forall b c s,
                 step_com (While b c) s
                          (If b (Seq c (While b c)) Skip) s.

(** Alternatively, we could define step_com as a function that just
   produces the very next configuration, since there
   is no recursion in the 'while' case. The only recursion is
   in Step_seqL, and that is well-founded.
 *)
Fixpoint step_com' (c:com) (s:state) : option (com * state) :=
match c with
  | Skip => None
  | Assign x e => Some (Skip, set x (eval_aexp e s) s)
  | Seq c1 c2 => 
    match step_com' c1 s with (* recursive call *)
      | Some (c1', s') => Some (Seq c1' c2, s')
      | None => Some (c2, s)
    end
  | If b c1 c2 => 
    if eval_bexp b s then Some (c1, s) else Some (c2, s)
  | While b c => Some (If b (Seq c (While b c)) Skip, s)
end.

(**
   However, one of the main reasons why we use small-step
   semantics is because we want to model nondeterminism
   (e.g., concurrent) systems. Making step_com a function
   would prevent extending IMP in that direction.
*)

(** Now let's define steps_com as the reflexive, transitive
    closure of step_com: *)

Inductive steps_com : com -> state -> com -> state -> Prop :=
| No_step : forall c s, steps_com c s c s
| One_step : forall c s c' s' c'' s'', step_com c s c' s' ->
                steps_com c' s' c'' s'' -> steps_com c s c'' s''.

(** Alternatively, we can use the inductive definition of
   the reflexive, transitive closure directly. *)
Require Import Relations.
Definition steps_com' (cfg : com * state) (cfg' : com * state) : Prop :=
  clos_refl _ (fun cfg cfg' => step_com (fst cfg) (snd cfg) (fst cfg') (snd cfg')) cfg cfg'.

(** Finally, we would hope that the semantics agree
    with each other. *)

Theorem big_small_agree :
   forall c s s', 
     eval_com c s s' <-> steps_com c s Skip s'.
Admitted.
