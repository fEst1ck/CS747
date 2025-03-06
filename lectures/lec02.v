(************************************************)
(** The mysteries of equality and induction... **)
(************************************************)

Require Import Arith.

Check 3 = 3.
Locate "_ = _".

(** The symbol "=" is just infix notation for the identifier [eq]. *)
Check eq.
Check @eq.
About eq.
(** And when we print out the definition of [eq]: *)
Print eq.

(**
  We see something like this:  

    Inductive eq (A : Type) (x : A) : A -> Prop :=  eq_refl : x = x

  What's going on here? The definition says [eq] is parameterized by a
  type [A] and a value [x:A], and returns a predicate on [A] values
  (i.e., [A -> Prop]).  
*)
Check @eq nat 3.

(**
  So for instance, [3 = 4] is short-hand for [@eq nat 3 4] and this is
  a [Prop].  Obviously, this [3 = 4] is something that we should not
  be able to prove.  

  Now the only way to prove an equality (i.e., construct a proof of [eq])
  is to use the data constructor [eq_refl].  Let's check [eq_refl]'s type:
*)
Check @eq_refl.
(**
  So [eq_refl] requires us to pass in a type [A] and a value [x:A] and
  returns a proof that [x = x].  So we can only seem to construct proofs
  of equality for the same object.  For instance:
*)
Check eq_refl 3.

(**
  Okay, so we managed to construct a proof that [3 = 3].  How do we
  prove [x = y] where [x] and [y] aren't exactly the same term?  
  For instance, we ought to be able to prove that [1+2 = 3].  

  Let's try this using tactics:
*)
Lemma one_plus_two_equals_three : 1 + 2 = 3.
Proof.
  apply eq_refl.
Qed.
(**
   What proof term did we actually construct?  Let's print it out
   and see...
*)
Print one_plus_two_equals_three.
(**
  This is confusing, but it's hard to see what's going on because Rocq
  is not printing out all of the implicit arguments.  We can rectify
  this by writing:
*)

Set Printing All.
(**
  This just tells Rocq we want to see all of the implicit arguments,
  and to turn off the notation. 
*)
Print one_plus_two_equals_three.

(** 
  So now we see that Rocq is claiming that [@eq_refl nat (S (S (S 0)))]
  is an object that has type [@eq nat (plus (S 0) (S (S 0))) (S (S (S 0)))].

  Or, using notation, we are claiming that [@eq_refl nat 3] is an object
  that has type [1+2 = 3] which is just notation for [@eq nat (1 + 2) 3].

  When Rocq is type-checking, it knows from the definition of [eq] that
  [@eq_refl nat 3] has type [3 = 3], but this is not the same as 
  [1+2 = 3], at least syntactically.  That is, Rocq will try to compare
  [3 = 3] and [1+2 = 3] to see if they are the same.  Since they are
  not, it will try to simplify these types.  In particular, it will
  simplify [1+2] into [3], and then it is obvious that they are the same.

  Another way to say this is that Rocq doesn't see any difference between
  [1 + 2] and [3] when it is type-checking.  We say that these two terms
  are _definitionally equal_.  In general, if we have two terms [M] and
  [N], and if [M] reduces to [P] and [N] reduces to [P], then Rocq 
  considers [M] and [N] to be definitionally equal.

  What do we mean by reduce?  We'll talk about this more later, but
  informally, to reduce a term, Rocq will:

  a) inline definitions of functions (such as +)

  b) beta-reduce: substitute an actual argument for a formal one, such 
     as reducing [(fun x => 1 + x) 2] to [1 + 2].

  c) match-reduce: reduce a pattern match on a known constructor.
     For instance, [match S 0 with | 0 => M | S x => N] will 
     reduce to [N[0/x]] (N with 0 substituted for x).

  d) unroll a recursive function [fix] if it needs to, but only
     if the unrolling will lead to a match reduction.

  So that's why as far as Rocq is concerned [1 + 2] is the same thing
  as [3].  Similarly, we can prove:
*)
Lemma L1 : ((fun x => match x with | None => 0 | Some y => 1 + y end) (Some 2)) = 3.
  reflexivity.  (** Note that [reflexivity] is a tactic that is the same as [apply eq_refl]. *)
Qed.

Unset Printing All.  (** Turn fancy printing back on. *)

(** 
   How about proving something like this though, which should obviously 
   be true, but where the terms are not the same?
*)
Lemma eq_symmetric : forall (x y:nat), x = y -> y = x.
Proof.
  intros x y H.
  rewrite H.
  (** When [H : x = y], then [rewrite H] substitutes [x] for [y] in the goal.
     In contrast, [rewrite <- H] substitutes y for x in the goal.  And 
     [rewrite H in H'] substitutes x for y in the hypothesis H'. *)
  reflexivity.
Qed.

(** How is [rewrite] achieving the goal?  That is, what proof term do we
   get out?  We'll see in a second, but we can actually prove something
   more generic such as this:
*)
Lemma leibniz : forall {A:Type} (x y:A), 
                  (x = y) ->
                  forall (P : A -> Prop), P x -> P y.
Proof.
  intros A x y H P.
  rewrite H.
  auto.
Qed.

Lemma leibniz_the_other_way :
  forall {A:Type} (x y:A), 
  (forall (P : A -> Prop), P y -> P x) -> (x = y).
Proof.
  intros A x y H.
  apply (H (fun x => x = y)).
  apply eq_refl.
Qed.

(** In English, what [leibniz] says is that whenever we have two
   [eq] terms [x] and [y], then for any proposition [P], such that
   [P] holds on [x], we can prove [P] holds on [y].  

   Given [leibniz], it's now easy to prove something like 
   [eq_symmetric] without using our magic [rewrite] tactic:
*)
Lemma eq_symmetric' : forall (x y:nat), x = y -> y = x.
Proof.
  intros x y H.
  Check (leibniz x y H (fun y => y = x)).
  (** Notice that when we choose [P] to be [fun x' => x' = x], then this
     this specializes [leibniz] to have type:
       [(fun x' => x' = x) x -> (fun x' => x' = x) y]
     which if we simplify, is the same as:
       [x = x -> y = x]
     In short, [leibniz x y H (fun x' => x' = x) : x = x -> y = x]
     So if we apply this to our goal [y = x]:
   *)
  apply (leibniz x y H (fun x' => x' = x)).
   (** Then we are left proving [x = x]: *)
  reflexivity.
Qed.

(**
   As the name suggests, [leibniz] shows that Rocq respects 
   substitution of [eq]-related terms in an arbitrary
   proposition.  And that's exactly what we would expect out of
   a notion of equality -- we can substitute equal terms without
   changing whether something is true or not.

   But still, how do we prove something like [leibniz] without
   using a magic tactic like [rewrite]?  The answer is a little
   complicated but boils down to the fact that when we do 
   a [match] on a proof that [x = y], then we know that the only
   way to construct such a proof is an [eq_refl] and hence,
   [y] must be [x]!  

   Now the way this is captured in Rocq is not very intuitive.
   Let us take a look at this particular term which is automatically
   generated when we defined the [eq] Inductive type:
*)
Print leibniz.
Print eq_ind_r.
Print eq_ind.
Check eq_ind.
(**
  eq_ind 
     : forall (A : Type) (x : A) (P : A -> Prop),
       P x -> forall y : A, x = y -> P y

  The term [eq_ind] has a type very similar to [leibniz].  It says
  that for any type [A], any value [x:A], and any proposition [P] over
  [A] values, if [P] holds on [x], then for any [y:A], such that [x=y],
  then [P] holds on [y].  This is just a re-ordering of the assumptions
  we had in [leibniz]. And indeed, we can use it to prove [leibniz]:
*)
Lemma leibniz' : forall {A:Type} (x y:A), 
                  (x = y) ->
                  forall (P : A -> Prop), P x -> P y.
Proof.
  intros A x y H P H1.
  apply (@eq_ind A x P H1 y H).
Qed.

Definition leibniz'' : forall {A:Type} (x y:A), 
                  (x = y) ->
                  forall (P : A -> Prop), P x -> P y :=
  fun A x y H P H1 =>
    match H with
    | @eq_refl _ _ => H1
    end.
(** Stepping back, what all of this mechanism lets you do is exactly
   what Leibniz equality requires:  subsitute equal terms for equal
   terms.  Critical to this is the fact that we can only build a proof
   of equality using [eq_refl] and it only allows us to prove the
   same object is equal to itself.  

   TL;DR:  rewrite isn't magic.  It's just doing a fancy pattern match.
*)

(** Okay, so let's prove a few more things using [rewrite] *)
Lemma eq_trans : forall {A:Type} (x y z:A), x = y -> y = z -> x = z.
Proof.
  intros A x y z H1 H2.
  rewrite <- H2.
  apply H1.
Qed.

(** Here's a surprising lemma... *)
Lemma one_plus : forall (x:nat), x + 1 = S x.
Proof.
  intro x.
  simpl.  (** Oops!  This doesn't seem to simplify things... *)
  unfold plus.  (** unfolds the definition of [plus] *)
  (** Aha!  We can't make progress with this.  So how to proceed? *)
  fold plus.  (** fold back the definition of [plus] *)

(** If we could prove that [x + 1 = 1 + x] then maybe we can make
   progress.  Perhaps there's a library lemma that already establishes
   the fact that [add] is commutative?  
*)
  Search (?a + _ = _ + ?a).
(** The [Search] command takes a meta-level pattern and tries to
   find any definitions in scope whose type matches that pattern.  
   Here, the [?a] and [?b] are pattern variables which can match
   any term.  Notice that the pattern captures just what we are looking
   for -- some term that is a proof that "+" is commutative.  
   And indeed, there is one such proof, called [Nat.add_comm].  

   You might play around with Search to see what other goodies
   are just lying around.  Certainly, you don't want to reprove
   things that you don't have to.  
*)
  Search (_ + _).  (** Whoa!  That's a long list of things... *)
  Search (?a * (?b + ?c) = _).  (** Aha! Distributivity! *)
  Search (?a + (?b + ?c) = (?a + ?b) + ?c).  (** Aha! Associativity! *)
(**
  The libraries have lots and lots of stuff.  I can never remember
  their names.  Search is wonderful.

  Anyway, we can rewrite using [add_comm] to simplify our goal:
*)
   rewrite Nat.add_comm.
(** Did this improve our situation?  Let's unfold [plus] and see: *)
   simpl.  (** yes!  Now the match can reduce and it does.  *)
   reflexivity.
Qed.

(** But how do we prove something like [plus] is commutative or associative?
   Induction!
*)
Check nat_ind.
(**   nat_ind
       : forall P : nat -> Prop,
           P 0 -> (forall n : nat, P n -> P (S n)) -> forall n : nat, P n

  In English, [nat_ind] takes some proposition [P] over numbers,
  asks us to provie a proof that [P] holds on [0], and a proof
  that for any [n], whenever [P n] holds, then [P] holds on the
  successor of [n].  If we manage to do that, then we can prove
  that [P] holds on all numbers.  This is quite literally the
  natural number induction we are taught when we do paper-and-
  pencil proofs.  

  So let's use [nat_ind] to construct a proof that [plus] is 
  associative.
*)


Lemma plus_associative : forall n m p, n + (m + p) = (n + m) + p.
Proof.
  apply (nat_ind (fun n => forall m p, n + (m + p) = (n + m) + p)).
  + (** base case:  n = 0 *)
    simpl.
    reflexivity.
  + intros n IH m p.
    simpl.
    rewrite IH.
    (* rename m into m'.
    rename p into p'.
    rewrite IH with (m:=m') (p:=p'). *)
    reflexivity.
Qed.
(** 
   Actually, there's a tactic that will take care of doing
   the first step for you. It's called (surprise) [induction]:
*)
Lemma plus_associative' : forall p m n, n + (m + p) = (n + m) + p.
Proof.
  induction n.
  * simpl. (** base case *)
    auto.
  * simpl. (** inductive case *)
    rewrite IHn.
    auto.
Qed.
(**
   The [induction] tactic looks at the goal's type (in this case a universal
   over a [nat]), and uses that to find the appropriate [???_ind] function,
   in this case [nat_ind], and then applies that for you.  

   But what does [nat_ind] look like? 
*)
Print nat_ind.
Fixpoint my_nat_ind {P: nat -> Prop} (H_0 : P 0) (H_S : forall n, P n -> P (S n)) (n:nat) : P n :=
    match n with
      | 0 => H_0 
      | S n' => H_S n' (my_nat_ind H_0 H_S n' : P n')
    end.
(** 
   It's just a frickin' recursive function (!) where when [n] is 0, we return 
   the base case, and when [n] is [S n'], we call [my_nat_ind] recursively
   on [n'] to get a term of type [P n'] and then use the induction hypothesis
   [H_S] to transform that to a term of type [P (S n')].  

   Now when you define an inductive definition, such as [nat], Rocq will automatically
   generate four functions for you.  Let's try it:
*)
Inductive mynat : Type := 
| ZERO : mynat
| SUCC : mynat -> mynat.
(*
   mynat is defined
   mynat_rect is defined
   mynat_ind is defined
   mynat_rec is defined
   mynat_sind is defined
*)
Check mynat_rect.
(** forall P:mynat->Type, P ZERO -> (forall m, P m -> P (SUCC m)) -> forall m, P m *)
Check mynat_ind.
(** forall P:mynat->Prop, P ZERO -> (forall m, P m -> P (SUCC m)) -> forall m, P m *)
Check mynat_rec.
(** forall P:mynat->Set, P ZERO -> (forall m, P m -> P (SUCC m)) -> forall m, P m *)
Check mynat_sind.
(** forall P:mynat->SProp, P ZERO -> (forall m, P m -> P (SUCC m)) -> forall m, P m *)
(* SProp "proof irrelevant propositions" aka "strict propositions".  Experimental feature. *)

(** There's nothing magical about them, they are just there for convenience. 
   Try looking at some other Inductive's induction principles:
*)
Check bool_rect.
Check list_rect.
Print list_rect.
Print option.
Check option_rect.

Inductive tree(A:Type) : Type := 
| Leaf : tree A
| Node : tree A -> A -> tree A -> tree A.

Check tree_rect.
Print tree_rect.


(************************************************)
(******* Let's build a certified compiler! ******)
(************************************************)

(** Let's build a provably correct (but very simple) compiler! We'll see
   that with the right tactic automation, the proof can be extremely simple. 

   We will use a tactic from the CPDT book.  You'll need the tarball
   of open-source libraries from CPDT, which can be obtained from Adam
   Chlipala's website:

      [http://adam.chlipala.net/cpdt/cpdtlib.tgz]

   You will need to compile the source, which can be done as follows in
   the cpdtlib:

      coqc -R [<cpdtlib>] Cpdt *.v

   where [<cpdtlib>] is the full pathname of the cpdtlib directory.
   You may need to make minor modifications to the source files to get
   them to compile with Rocq version 8.20.
*)

Require Import Bool Arith List Cpdt.CpdtTactics.
Require Import Utf8.

(** This command tells Rocq to automatically make some arguments implicit when
   you write definitions.  In general, it will make implicit something that
   it can easily figure out from the other arguments (e.g., types often)
   and saves you from using curly braces and so forth.  Figuring out what
   it decides to make implicit isn't always easy.  When you Print a definition,
   it tells you what arguments are implicit, so that helps.  You will get used
   to what it decides to make implicit pretty quickly... *)
Set Implicit Arguments.

(** Let's start by defining some syntax for a simple language of
  arithmetic expressions.  This is just an abstract syntax tree -- not
  a computation but a data structure representing one.
*)
Inductive binop : Type := Plus | Times.

Inductive exp : Type := 
| Const : nat -> exp
| Binop : binop -> exp -> exp -> exp
| If : exp -> exp -> exp -> exp
.


(** Using Rocq, we can describe the _meaning_ of the computation
    denoted by an abstract syntax tree.
    
    We can think of this as giving a mathematical description of the
    computation (or as a compilation directly into Rocq).
*)
Definition binopDenote (b:binop) : nat -> nat -> nat := 
  match b with 
    | Plus => plus
    | Times => mult
  end.

Notation "binop⟦ b ⟧" := (binopDenote b).

Fixpoint expDenote (e:exp) : nat := 
  match e with 
  | Const n => n
  | Binop b e1 e2 => (binopDenote b) (expDenote e1) (expDenote e2)
  | If e1 e2 e3 =>
      match expDenote e1, expDenote e2, expDenote e3 with
      | O, _, n => n
      | _, n, _ => n
      end
  end.

Notation "exp⟦ e ⟧" := (expDenote e).

(** Now let's define a stack-machine target language for a
    compiler. A program is a list of instructions that
    manipulate a stack of operands.
  *)

Inductive instr : Type := 
| iConst : nat -> instr
| iBinop : binop -> instr
| iIf : instr
.

Definition prog := list instr.
Definition stack := list nat.

(** We can also give a denotation for stack-machine programs, as stack
    transformers.
    However, not all stack-machine programs make sense, since there
    might not be enough arguments on the stack for a binary/ternary
    operator.  We give these programs the denotation [None].
  *)

Definition instrDenote (i:instr) (s:stack) : option stack := 
  match i with 
    | iConst n => Some (n::s)
    | iBinop b =>
      match s with
        | arg1 :: arg2 :: s' => Some ((binop⟦b⟧ arg1 arg2) :: s')
        | _ => None
      end
    | iIf =>
      match s with
      | arg1 :: arg2 :: arg3 :: s' =>
        Some ((match arg1 with | O => arg3 | S _ => arg2 end) :: s')
      | _ => None
      end
  end.

Notation "instr⟦ i , s ⟧" := (instrDenote i s).

Fixpoint progDenote (p:prog) (s:stack) : option stack := 
  match p with 
    | nil => Some s
    | i::p' => 
      match instr⟦i,s⟧ with 
        | None => None
        | Some s' => progDenote p' s'
      end
  end.

Notation "prog⟦ p , s ⟧" := (progDenote p s).

Eval compute in progDenote (iConst 3::iConst 4::iBinop Times::nil) nil.
Import ListNotations.
Eval compute in progDenote [iConst 3; iConst 4; iBinop Times] [].
Eval compute in progDenote [iConst 3; iConst 4; iConst 1; iIf] [].

(** Now let's write a compiler from the source language
    to the target language! *)

Fixpoint compile (e:exp) : prog := 
  match e with 
    | Const n => [iConst n]
    | Binop b e1 e2 => compile e2 ++ compile e1 ++ [iBinop b]
    | If e1 e2 e3 => compile e3 ++ compile e2 ++ compile e1 ++ [iIf]
  end.

(** Wouldn't it be great if our compiler were correct? We can
    prove that by relating the denotations of the source program
    and its compilation. *)

Lemma compile_correct' : forall e p s, 
  prog⟦(compile e) ++ p, s⟧ = prog⟦p, expDenote e::s⟧.
Proof.
  induction e ; simpl ; auto ; intros ; repeat rewrite <- app_assoc;
  repeat match goal with
  | [ H : forall p s, prog⟦_, _⟧ = _ |- _ ] => rewrite H; clear H
  end; reflexivity.
Qed.

Lemma compile_correct'' : forall e p s, 
  prog⟦(compile e) ++ p, s⟧ = prog⟦p, expDenote e::s⟧.
Proof.
  (** [crush] is a magic tactic provided by [CPDT] that manages to knock off
     a lot of obligations for us.  You can check out how [crush] is
     defined to build your own proof-automation.  In some sense,
     this is the ideal proof in a readability-sense.  It's the
     equivalent of writing "by induction on e".  *)
  induction e ; crush.
Qed.

Theorem compile_correct : forall e, 
  prog⟦ compile e, [] ⟧ = Some [exp⟦ e ⟧].
Proof.
  (** And now we can use this lemma to prove our desired theorem. *)  
  intros.
  About app_nil_r.
  rewrite <- app_nil_r with (l:=compile e).
  rewrite compile_correct'.
  simpl.
  reflexivity.
Qed.

(***** Second example ******)

Inductive type : Set := TNat | TBool.

(** Notice that both [tbinop] and [texp] are *indexed* by [type]s.  That is
   to say, we are reflecting some structure in the types of the constructors.

   For example, in the case of [TBinop], we are requiring that we pass in
   a [binop] indexed by [t1], [t2], and [t], and that the sub-expressions
   were built from constructors that are indexed by [t1] and [t2] respectively,
   and we get out a [texp] indexed by [t].

   This pattern is known as "intrinsically-typed syntax": the syntax definition
   itself captures the typing constraints.

   GHC Haskell and OCaml provide support for this kind of indexed data type now,
   though it's called "generalized abstract data types" (GADTs) in those
   contexts.  Rocq (and type theory) have had them for a long time...
*)
Inductive tbinop : type -> type -> type -> Type :=
| TPlus  : tbinop TNat TNat TNat
| TTimes : tbinop TNat TNat TNat
| TEq    : forall t, tbinop t t TBool
| TLt    : tbinop TNat TNat TBool.

Inductive texp : type -> Type :=
| TNConst : nat -> texp TNat
| TBConst : bool -> texp TBool
| TBinop : forall (t1 t2 t:type), tbinop t1 t2 t -> texp t1 -> 
                                  texp t2 -> texp t.

(** This is a kind of a funny function -- it's mapping our names for
   types, [TNat] and [TBool], to actual Rocq types.  This is not something
   you can write in OCaml or Haskell.
*)
Definition typeDenote (t : type) : Type :=
  match t with
    | TNat => nat
    | TBool => bool
  end.

(** Look carefully at the type of [tbinopDenote] and see how this
   matches up with the definition. *)
Definition tbinopDenote T1 T2 T3 (b : tbinop T1 T2 T3)
  : typeDenote T1 -> typeDenote T2 -> typeDenote T3 :=
  match b with
    | TPlus => Nat.add
    | TTimes => Nat.mul
    | TEq TNat => Nat.eqb
    | TEq TBool => Bool.eqb
    | TLt => Nat.leb
  end.

Check tbinopDenote.
Check TBinop.

(** Similarly, here we can see that [texpDenote] takes an [texp] indexed
   by a [type] named [t], and returns a value of the Rocq type [typeDenote t].
   It's the ability to
   (a) use dependent types,
   (b) write functions from values to types,
   (c) index data constructor types with other data
   that really provides the power to capture this here.  

   In essence, we are proving that our interpreter preserves types
   appropriately when we use this kind of indexing.  And it's all
   happening more or less for free.
*)
Fixpoint texpDenote (t:type) (e : texp t) : typeDenote t :=
  match e with
    | TNConst n => n
    | TBConst b => b
    | TBinop b e1 e2 => (tbinopDenote b) (texpDenote e1) (texpDenote e2)
  end.

Definition tstack := list type.

(** Instruction syntax and typing.  A [tinstr] describes how one stack
  (at the type level) is mapped to another stack by a single
  instruction.
*)
Inductive tinstr : tstack -> tstack -> Type :=
| TiNConst : forall s, nat -> tinstr s (TNat :: s)
| TiBConst : forall s, bool -> tinstr s (TBool :: s)
| TiBinop : forall T1 T2 T3 s,
  tbinop T1 T2 T3
  -> tinstr (T1 :: T2 :: s) (T3 :: s).

(** Program syntax and typing. *)
Inductive tprog : tstack -> tstack -> Type :=
| TNil : forall s, tprog s s
| TCons : forall s1 s2 s3,
  tinstr s1 s2
  -> tprog s2 s3
  -> tprog s1 s3.

(** [tstackDenote] maps a [tstack] into a tuple containing the
    denotations of all the types in the stack *)
Fixpoint tstackDenote (ts : tstack) : Type :=
  match ts with
    | nil => unit
    | t :: ts' => (typeDenote t) * (tstackDenote ts')
  end%type.

(** We can lift the action of an instruction to
    a mapping over real types.
 *)
Definition tinstrDenote ts ts' (i : tinstr ts ts') : tstackDenote ts -> tstackDenote ts' :=
  match i with
    | TiNConst _ n => fun s => (n, s)
    | TiBConst _ b => fun s => (b, s)
    | TiBinop  _ b => fun s =>
      let '(arg1, (arg2, s')) := s in
        ((tbinopDenote b) arg1 arg2, s')
  end.

(** Then, concatenating with a program or instruction is just composition of the denotations. *)
Fixpoint tprogDenote ts ts' (p : tprog ts ts') : tstackDenote ts -> tstackDenote ts' :=
  match p with
    | TNil _ => fun s => s
    | TCons i p' => fun s => tprogDenote p' (tinstrDenote i s)
  end.

(** Dependent types sometimes bite us... Rocq does not work hard enough to 
    figure out that [ts] and [ts'] are the same in the [TNil] case.  *)
Fail Fixpoint tconcat ts ts' ts'' (p : tprog ts ts') (p' : tprog ts' ts'') : tprog ts ts'' :=
  match p with
    | TNil _ => p'
    | TCons i p1 => TCons i (tconcat p1 p')
  end.

(** This works *)
Fixpoint tconcat ts ts' ts'' (p : tprog ts ts') : tprog ts' ts'' -> tprog ts ts'' :=
  match p with
    | TNil _ => fun p' => p'
    | TCons i p1 => fun p' => TCons i (tconcat p1 p')
  end.

(** This also works *)
Definition tconcat' ts ts' ts'' (p : tprog ts ts') (p' : tprog ts' ts'') : tprog ts ts''.
induction p as [| s1 s2 s3 i p].
+ apply p'.
+ apply (TCons i (tconcat p p')).
Defined.

Fixpoint tcompile t (e : texp t) (ts : tstack) : tprog ts (t :: ts) :=
  match e with
    | TNConst n => TCons (TiNConst _ n) (TNil _)
    | TBConst b => TCons (TiBConst _ b) (TNil _)
    | TBinop b e1 e2 => (tconcat (tcompile e2 _)
                        (tconcat (tcompile e1 _)
                                 (TCons (TiBinop _ b) (TNil _))))
  end.

Lemma tconcat_correct : forall ts ts' ts''
  (p : tprog ts ts') (p' : tprog ts' ts'') (s : tstackDenote ts),
  tprogDenote (tconcat p p') s = tprogDenote p' (tprogDenote p s).
Proof.
  induction p; crush.
Qed.

(** A [Hint] is a way of registering a definition, such as [tconcat_correct],
   as something we want to use within certain tactics, such as [crush] or
   [auto].  Effectively, by registering [tconcat_correct] as a [Hint Rewrite],
   we are telling [crush] (and [auto]) that it should try to rewrite the
   goal using this lemma as part of the search for a proof.  

   Adding hints is a great way to get more powerful tactics.  But it does
   have a downside in that it can blow up the time it takes for a tactic to
   find a proof.
*)
Hint Rewrite tconcat_correct.

Lemma tcompile_correct' : forall t (e : texp t) ts (s : tstackDenote ts),
  tprogDenote (tcompile e ts) s = (texpDenote e, s).
Proof.
  induction e ; crush.
Qed.
Hint Rewrite tcompile_correct'.

Theorem tcompile_correct : forall t (e : texp t),
  tprogDenote (tcompile e nil) (tt : tstackDenote []) = (texpDenote e, tt : tstackDenote []).
Proof.
  crush.
Qed.

(** [Extraction] and [Recursive Extraction] allow us to extract OCaml
   code from a Rocq development.
   Look carefully at the extracted code and compare with the Rocq
   definitions. *)
(* Recursive Extraction eq. *)
Require Extraction.
Recursive Extraction tcompile.
