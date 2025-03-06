(** Comments in Rocq are as in Ocaml and SML: they start with a left-paren 
   and asterisk, and are closed with an asterisk and right-paren. *)

(**

# Why this course?

  Formally, machine-checked proofs are an increasingly important way to obtain trust in the computing systems we depend on.

  This course: proving in a machine-checkable way that code respects specifications/policy

# Trends and portents

  Proof assistants (Rocq, Agda, Lean,  Isabelle/HOL, etc.) have matured and can be used to proved deep correctness properties of complex software (compilers, OSes), programming languages, and cryptography.

  Approaching a tipping point where use of formal verification is routine (Possibly in conjunction with more automatic techniques like SMT verifiers, model checking)

  In PL community, mechanically verified proofs are becoming an expected part of research contributions.
    
    Also increasingly frequent in OS community!

    Expertise in using proof assistants will be an enabling capability.

# Who is this for?

  Pitched not only towards PL people per se, but also to "systems" people interested in the topic

  Prerequisites: familiarity with functional programming, type systems, formal notions of proof, general mathematical maturity.
    
  Aimed at graduate students but undergrads with right background are welcome.
  (If you've done a “Software Foundations” course, may be too much overlap?)

# Coursework

  Attend and participate in lectures

  Do problem sets to become familiar with Rocq (must keep up!)

  The major effort: final project during second half (solo)
  see https://cs.uwaterloo.ca/~yizhou/courses/cs747-2025wi/#course-project for details

*)

(* v20.0 ro Rocq *)
Require Import Arith.

(** [Require Import Arith.] is a top-level command that tells Rocq to import
   the definitions from the [Arith] library (arithmetic) and to make the
   definitions available at the top-level.  All top-level commands end
   with a period.
*)

Definition four : nat := 4.

(** A top-level definition begins with the keyword [Definition], followed
   by an identifier (in this case [four]) that we want to use, a colon,
   a type, [:=], and then an expression followed by a period.  
   Here the type of the number [4] is [nat] which stands for natural number.  *)

Definition four' := 2 + 2.
(** You can leave off the type information and Rocq can often infer it.  
   But it can't always infer types, and it's good documentation to put
   the types on complicated definitions. *)

Eval compute in four'.
Eval compute in four + four'.
Eval lazy in let _ := four + four in four'.
(** [Eval compute in <exp>.] lets you evaluate an expression to see the 
   resulting value and type. *)

Check four'.
(** [Check <exp>] lets you check the type of an expression. *)

Print four'.
(** [Print <identifier>] lets you see the definition of the identifier. *)

Definition four'' := (6 - 4) * 2.

Check four''.
Eval compute in four''.
Print four''.

Definition inc (x:nat) : nat := x + 1.
(** To define a function, we just make a parameterized definition.*)

Check inc.
Print inc.
Eval compute in inc.
Eval compute in inc four.

Definition inc' x := x + 1.
(** As in Ocaml, we can leave off the types and Rocq can usually infer them,
   but not always. *)

Check inc'.
Print inc'.
Eval compute in inc' four.

Definition inc'' := fun (x:nat) => x + 1.
(** Parameterized definitions are just short-hand for a regular definition
   using a lambda expression. *)

Check inc''.
Eval compute in inc'' four.


Definition add1 x y := x + y.
Definition add2 (x:nat) (y:nat) := x + y.
Definition add3 (x y:nat) := x + y.
(** When the types are the same, we can group parameters as in [add']. *)
Definition add4 := fun x => fun y => x + y.
(** Multiple parameters are just iterated lambdas. *)

Check add1.
Check add2.
Check add3.
Check add4.
Eval compute in add1 5 4.
Eval compute in add2 5 4.

Definition inc''' := add1 1.
Check inc'''.
Eval compute in inc'''.
Eval compute in inc''' 4.

Inductive bool : Type := 
| true 
| false.
(** An inductive definition is just like an Ocaml datatype definition,
   though the syntax is a little different.  Here, we are defining
   a new [Type] called [bool] with constructors [true] and [false].
   Unlike Ocaml, we can (and generally need to) provide the type of 
   each data constructor, hence both [true] and [false] are defined
   as constructors that immediately return a [bool].  

   Notice that when we evaluate this definition, Rocq says that not
   only is [bool] defined, but also [bool_rect], [bool_ind], and 
   [bool_rec].  We'll discuss those later on when we start talking
   about proving things.
*)
Check true.
Check false.
Print bool.

Definition negb (b:bool) : bool := 
  match b with 
    | true => false
    | false => true 
  end.
(** The definition above shows how we use pattern-matching to tear apart
   an inductive type, in this case a [bool].  The syntax is similar to 
   Ocaml except that we use "=>" for the guard instead of "->" and we
   have to put an "end" to terminate the "match". *)

Check negb.
Eval compute in negb true.
Eval compute in negb false.

Definition andb (b1 b2:bool) : bool := 
  match b1 with 
    | true => b2
    | false => false
  end.

Eval compute in andb true false.
Eval compute in andb true true.

Definition orb b1 b2 := 
  match b1 with
    | true => true
    | _ => b2
  end.

Eval compute in orb true false.
Eval compute in orb true true.

(** The [Arith] module defines this [nat] type already.  It is a way to
   represent the natural numbers, with a base case of zero, "0" and 
   successor constructor [S]. Notice that the type of [S] declares
   it to take a [nat] as an argument, before returning a [nat]. 

Inductive nat : Type := 
  | O : nat
  | S : nat -> nat.

type nat = O | S of nat
*)

Print nat.

(** 
   A digression:

   In informal math, we tend to think of a "type" as a set of
   objects.  For instance, we think of [nat] as the set of
   objects {0,1,2,3,...}.  But we can also form sets out of
   sets.  For instance, we can have {nat,bool,string}.  Technically,
   to avoid circularities, [nat] is considered a "small" set,
   and {nat,bool,string} is considered a "large" set, sometimes
   called a class.  Stratifying our sets is necessary to avoid
   constructions such as S = { s : set | s is not contained in s }
   (Russell's paradox.)  

   In Rocq, the identifier [Set] refers to a universe of 
   types, including {nat,bool,string,...}.  So in some sense, 
   the identifier [Set] names a class of types.  We sometimes
   say that [Set] is the type of the collection 
   {nat,bool,string,...}. When we build 
   certain kinds of new types out of elements of [Set], then we 
   have to move up to a new universe.  Internally, that universe
   is called Type_1.  (Actually, [Set] is represented as Type_0
   internally.)  And if we build certain types out of Type_1,
   we have to move up to Type_2.  So Rocq has an infinite hierarchy
   Set a.k.a. Type_0, Type_1, Type_2, ...   

   Now figuring out where in this hierarchy a definition should go
   isn't that hard, and in fact, Rocq automagically infers this
   for you.  When you write [Type], you are really writing [Type_x]
   and Rocq is later solving for [x] to make sure your definitions
   don't contain a circularity.  In fact, with the exception of
   [Set] and one more very special universe, [Prop], you can't
   even explicitly say at what level you want a given definition.
   
   For now, we can just ignore this and use [Type] everywhere.
*)
Check O.
Check 0.   (** the numeral 0 is just notation for the constructor O *)
Eval compute in 0.
Eval compute in 3.
Check S.
Check S 0. (** 1,2,3 are short-hand for (S O), (S (S O)) and (S (S (S O))). *)
Check S (S (S 0)).

Definition is_zero (n:nat) : bool := 
  match n with 
    | 0 => true
    | S _ => false
  end.

Fixpoint add'' (n m:nat) : nat := 
  match m with 
    | 0 => n
    | S m' => S (add'' n m')
  end.
(** We construct recursive functions by using the keyword "Fixpoint". *)

Eval compute in add'' 4 3.
Print add''.

Definition add5 :=
  fix local_add (n m:nat) : nat := 
  match n with 
    | 0 => m
    | S n' => S (local_add n' m)
  end.
(** Alternatively, we can use a "fix" expression which builds a recursive
   functions, similar to the way "fun" builds a non-recursive function.
*)

Eval compute in add5 4 3.
Print add5.

(** Pairs *)
Definition p1 : nat * nat := (3,4).  (** pair of nats *)
Definition p1' : prod nat nat := (3,4). (** same thing *)

Check p1.
Check p1'.

Definition p2 : nat * bool := (3, true).  (** nat and bool *)
Definition p3 : nat * bool * nat := (3,true,2).

Eval compute in add3 (fst p1) (snd p1).  
(** [fst] extracts the first component of a pair, and [snd]
   extracts the second component. *)

Eval compute in fst p3.
Eval compute in snd (fst p3).
(** Notice that [(3,true,2)] is really short-hand for [((3,true),2)]. 
   and [nat * bool * nat] is short for [(nat * bool) * nat]. *)

Print pair.
Eval compute in match p1 with 
                  | pair x y => x + y
                end.
Locate "_ * _".

(** Options *)
Definition opt1 : option nat := None.
Definition opt2 : option nat := Some 4.
(** An [option t] is either [None] or [Some] applied to a value of type [t]. 
   Notice that unlike Ocaml, we write [option nat] instead of [nat option].
*)
Print option.

Fixpoint subtract (m n:nat) : option nat := 
  match m, n with 
    | _, 0 => Some m
    | 0, S _ => None
    | S m', S n' => subtract m' n'
  end.
Eval compute in subtract 5 2.
Eval compute in subtract 2 5.

(** Sums *)
Locate "_ + _".
Print sum.

Definition s1 : nat + bool := inl 3.
Definition s2 : nat + bool := inr true.
(** We build something of type [t1 + t2] by using either [inl] or 
   [inr].  It's important to provide Rocq enough type information
   that it can figure out what the other type is. *)

Definition add_nat_or_bool (s1 s2: nat + bool) : nat + bool := 
  match s1, s2 with 
    | inl n1, inl n2 => inl (n1 + n2)
    | inr b1, inr b2 => inr (orb b1 b2)
    | _, _ => inr false
  end.

(** Lists *)
Require Import List.
Print list.
(*
    Inductive list (A:Type) : Type := 
    | nil : list A
    | cons : A -> list A -> list A.
*)
Definition l1 : list nat := nil.
Definition l2 : list nat := 3::2::1::nil.
Locate "_ :: _".
Definition l3 : list bool := true::false::nil.
Definition l4 : list (nat + bool) := (inl 3)::(inr true)::nil.

Fixpoint append (l1 l2:list nat) : list nat := 
  match l1 with 
    | nil => l2
    | h::t => h::(append t l2)
  end.

Eval compute in append l2 l2.

Fixpoint add_list (l1 l2:list nat) : option (list nat) := 
  match l1, l2 with 
    | nil, nil => Some nil
    | n1::l1, n2::l2 => 
      match add_list l1 l2 with
        | None => None
        | Some l => Some ((n1+n2)::l)
      end
    | _, _ => None
  end.

Eval compute in add_list l2 l2.
Eval compute in add_list l2 l1.

(** Polymorphism *)

Fixpoint generic_append (A:Type) (l1 l2: list A) : list A := 
  match l1 with 
    | nil => l2
    | h::t => h::(generic_append A t l2)
  end.
(** Unlike Ocaml, we make type parameters explicit in Rocq.  Here, 
  we've defined a generic append function, which abstracts over
  a type [A].  Notice that the types of the arguments [l1] and
  [l2] depend upon [A], as does the result type.  Notice also
  that when we call this function, we must provide an actual
  type for the instantiation of [A].
*)

Eval compute in generic_append bool l3 l3.
Eval compute in generic_append nat l1 l2.
Eval compute in generic_append _ l3 l3.  
(** Rocq can usually figure out what the types are, and we can
   leave out the type by just putting an underscore there 
   instead.  But there are cases where it can't figure it
   out (e.g., generic_append _ nil nil).
*)

Fixpoint generic_append' {A:Type} (l1 l2:list A) : list A := 
  match l1 with 
    | nil => l2
    | h::t => h::(generic_append' t l2)
  end.
(** The curly braces tell Rocq to make an argument implicit.  That
   means it's up to Rocq to fill in the argument for you.  Notice
   that in the recursive call, we didn't have to specify the type. *)

(** This won't work though:
Definition foo := generic_append' nil nil.
   We can fix it by either giving enough information in the context
   or by using "@" to override the implicit arguments:
*)
Fail Definition foo := generic_append' nil nil.
Definition foo : list nat := generic_append' nil nil.
Definition foo1 := @generic_append' nat nil nil.

Fixpoint generic_append'' [A:Type] (l1 l2:list A) : list A := 
  match l1 with 
    | nil => l2
    | h::t => h::(generic_append'' t l2)
  end.
Eval compute in generic_append'' l1 l1.
Eval compute in generic_append'' l2 l2.
(** No need to specify type arguments. *)

Fail Definition generic_append'_copy := generic_append'.
Check generic_append'.
(** 
  generic_append' : list ?A -> list ?A -> list ?A where ?A : [ |- Type]
  type argument is maximally inserted
*)
Check generic_append''.
(** 
  generic_append'' : forall A : Type, list A -> list A -> list A)
  no maximal insertion of type arguments
*)
Definition generic_append''_copy := generic_append''.

(**********************************************)
(** Programs as Proofs, Types as Propositions *)
(**********************************************)

(** The top-level command [Check <exp>] tells you the type of the given exp. *)
Check True.
Check False.

(** [True] and [False] are propositions or something classified by the type [Prop].  
   They are not to be confused with [true] and [false] which are booleans.
   The distinction is roughly, that [true] and [false] are objects, whereas
   [True] and [False] are types.  What are the elements of the type [True]?
   They are all the *proofs* that allow us to conclude "True".  In contrast,
   the object [true] doesn't really name a collection of things.  

   So what are some of the elements or proof objects in the special 
   type [True]?
*)
Print True.
(** Aha!  We see that one element is the constructor [I].  It's a way 
   (in fact, the best way) to build a proof whose conclusion is the
   trivial theorem [True].  
*)
Check I.
(** But [I] is not the only way to build an object of type [True].  Another
   example is:
*)
Check (fun x => x) I.
(** And we will see many more examples of ways to construct a proof of [True].
   However, it will turn out that if a (closed) expression e : True, then

   So in general, an element of [Prop], such as [True], is the 
   name of a theorem, and at the same type, names a collection of terms that
   correspond to proofs of that theorem. 

   What about [False]?
*)
Print False.
(** [False] is a funny inductive definition which has no
   constructors.  So, there's no easy way to build an object that
   has type [False].  A very, very deep result about Rocq is that in
   fact, there is no closed term E such that E : False.  In other
   words, there's no way construct a proof of False, and that's a
   very good thing.

   All functions in Rocq must terminate. One reason why is that if we
   had diverging computations, a la OCaml, then we would have a way to
   build a term E of type False.  For instance, in OCaml, we can
   define:

   letrec loop () : t = loop ()

   for any type [t] that we like, includng an empty type.  This
   means that in OCaml, every type has an element and thus we
   can't use OCaml types to represent propositions such as [False].
   Another way to say this is that in OCaml, the "logic" of the 
   language is "inconsistent." 

   There are other good reasons why Rocq functions are required
   to terminate.  One is that the type-checker must sometimes
   normalize (i.e., simplify) expressions to see if they are equal.  
   If that normalization process could diverge, then so could
   type-checking.

   Later on, we'll see how it's possible to *model* computations
   that might diverge.
*)

(** The top-level command [Locate "..."] helps to locate a symbol
   that's defined with notation.  In this case, we are searching for
   the notation for logical "and". *)
Locate "_ /\ _".

(** The top-level command [Print <id>] prints the definition of a 
   given identifier.  Note that [and] is just an inductive definition
   with one constructor, [conj] which takes two [Prop]s as arguments,
   and produces a [Prop] as a result. *)
Print and.

Locate "_ \/ _".

(** Logical [or] is also just an inductive definition, but this
   time it has two constructors, one for the left and one for 
   the right. *)
Print or.

(** I'm going to start a new module named [M1] so that I don't
   pollute the top-level namespace.  We end the module by writing
   [end M1.] -- see below. *)
Module M1.

  (** Now we can start building some interesting proofs. *)
  Definition proof_of_true_and_true : True /\ True := 
    conj I I.

  Definition proof_of_true_or_false : True \/ False := 
    or_introl I.

  Definition proof_of_false_or_true : False \/ True := 
    or_intror I.
  
  (** What about implication?  This can be represented as a
     function.  That is, we can think of "A implies B" as 
     a function which takes evidence of A and constructs
     evidence of B from it.  In fact, we will use the notation
     "->" to denote both functions and implication.  And we
     will use [fun x => ...] to build a function, or evidence
     of an implication.  For instance: *)
  Definition t0 {A:Prop} : A -> True := 
    fun (H:A) => I.

  Definition t1 {A B:Prop} : A -> B -> A /\ B := 
    fun (HA:A) (HB:B) => conj HA HB.
  
  (** This example shows taking apart some evidence.  In this
     case, we are given evidence of [A /\ B] and we need to
     construct from it evidence of [A].  So we use a pattern
     match to tear apart the proof of [A /\ B], since we know
     that it must've been built from [conj HA HB] where [HA]
     is a proof of [A] and [HB] is a proof of [B].  *)
  Definition t2 {A B:Prop} : A /\ B -> A := 
    fun (H : A /\ B) => 
      match H with 
        | conj H1 H2 => H1
      end.
  
  Definition t3 {A B:Prop} : A /\ B -> B :=
    fun (H: A /\ B) => 
      match H with
        | conj H1 H2 => H2
      end.

  Definition t4 {A B C:Prop} : 
    (A -> C) /\ (B -> C) -> (A \/ B) -> C := 
    fun (H1:(A->C)/\(B->C)) (H2:A\/B) => 
      match H1 with 
        | conj H3 H4 => match H2 with 
                          | or_introl H5 => H3 H5
                          | or_intror H6 => H4 H6
                        end
      end.

  Definition t5 {A:Prop} : False -> A := 
    fun (H:False) => 
      match H with 
      end.

  Definition t6 {A B C D:Prop} (H1:A -> B \/ C) : 
    (B -> D) -> (C -> D) -> (A -> D) := 
    fun H2 H3 H4 => 
      let H5 := H1 H4 in 
      t4 (conj H2 H3) H5.

  Locate "~ _".
  Check not.
  Print not.
  (** Negation [~A] is just an abbreviation for [A -> False]. *)

  Definition t7 {A B C : Prop} : 
    ~ (A /\ B) -> A -> B -> C := 
    fun (H1 : (A/\B) -> False) (H2:A) (H3:B) => 
      match H1 (conj H2 H3) with
      end.
  
  Definition t7' : forall {A B C:Prop}, 
    ~ (A /\ B) -> A -> B -> C := 
    fun {A B C} (H1 : (A/\B) -> False) (H2:A) (H3:B) => 
      match H1 (conj H2 H3) with
      end.
  
  Definition t7'' : 
    forall {A B C : Prop} (H1:~ (A /\ B)) (H2 : A) (H3 : B), C := 
    fun {A B C} (H1 : (A/\B) -> False) (H2:A) (H3:B) => 
      match H1 (conj H2 H3) with
      end.

  Check t7.
  Check t7'.
  Check t7''.

  Locate "exists".
  Check unique.
  Print unique.
  Check ex.
  Print ex.

  Print ex_intro.
  (** Notice that exists is not primitive and is in fact encoded using forall. Notice that the
      variable mentioned in forall is really a parameter to the [exists_intro] constructor, allowing
      us to construct a proof of an existential claim using _any_ witness.
      The [A] and [P] parameters to [ex_intro] are implicit. We can force ourselves to
      provide them explicitly by using [@ex_intro] instead. *)
    

  Definition t8 : exists x:nat, x + 1 = 3 := 
    ex_intro _ 2 eq_refl.
  (** Sometimes, Rocq can figure out what a missing argument is and
     we can omit it by putting in an underscore "_" as in the 
     example below. *)

End M1.

(** Building proof objects by hand can be extremely difficult.
   So instead, we're going to use some *tactics* to construct
   these objects.  Some useful tactics include the following:

   auto   -- solves trivial goals such as "True" and "3 = 3" or
             "x = x".

   intro  -- given a goal A -> B, introduces A as an assumption,
             leaving B as the result.  It's the same as writing
             [refine (fun H:A => _)].

   intros -- same as above but introduces a bunch of assumptions.
             For instance, if our goal is A -> B -> C -> D, then
             intros will introduce hypotheses H1:A, H2:B, and
             H3:C and leave us with the goal D.  You can also
             give explicit names for the hypotheses as in 
             intros H1 H2 H3.

   split --  if the goal is A /\ B, breaks this into two sub-goals,
             first A and then B.

   destruct -- if we have a hypothesis [H : A /\ B] then we can 
               break it into two hypotheses [H1 : A] and [H2 : B].
               using [destruct].  

   simpl --  simplifies the goal by reducing expressions as much 
             as possible.  For instance, if our goal is
             [1 + 3 = 2 + 2], then calling [simpl] will reduce
             the goal to [4 = 4] which we can solve by auto.

   left --   given the goal A \/ B, reduces the goal to proving
             just A.  

   right --  given goal A \/ B, reduces the goal to proving B.

   apply H -- apply the hypothesis H to solve the current goal.
              This only works when H names a hypothesis that
              matches the given goal.

   See also http://adam.chlipala.net/itp/tactic-reference.html
   for a better list.
*)

(** Re-doing the examples above using tactics. *)
Module M2.

  (** Notice that I didn't use ":=" but terminated the definition
     with a period.  This drops you into tactic mode. *)
  Definition proof_of_true_and_true : True /\ True.
  Proof.  (** not necessary, but a good visual indicator. *)
    (** prove True /\ True *)
    split. (** leaves us with two goals *)
    - (** First goal:  True *)
      apply I.
    - (** Second goal: True *)
      auto.
   Qed.  (** claim that we've solved all goals. *)

  (** We can print out the proof object that the tactics
     constructed for us... *)
  Print proof_of_true_and_true.

  (** Instead of using the keyword [Definition] we can also
     use the keywords [Lemma] and [Theorem].  *)
  Lemma proof_of_true_and_true' : True /\ True.
  Proof.  
    auto.  (** actually, auto will knock this off. *)
  Qed.

  Theorem prof_of_true_and_true'' : True /\ True.
  Proof.
    (** we can use previously existing proofs. *)
    apply proof_of_true_and_true'.
  Qed.

  Definition proof_of_true_or_false : True \/ False.
  Proof.
    auto.
  Qed.

  Definition proof_of_false_or_true : False \/ True.
  Proof.
    auto.
  Qed.
    
  Lemma t0 {A:Prop} : A -> True.
  Proof.
    intro.
    auto.
  Qed.

  Lemma t1 {A B:Prop} : A -> B -> A /\ B.
  Proof.
    auto.
  Qed.

  Lemma t2 {A B:Prop} : A /\ B -> A.
  Proof.
    (** It's generally a bad idea to let Rocq pick the names for you. 
       We can usually give names that we want. *)
    intro H.
    destruct H as [H1 H2].
    apply H1.
  Qed.

  Lemma t3 {A B:Prop} : A /\ B -> B.
  Proof.
    destruct 1 as [H1 H2].
    assumption.
  Qed.

  Lemma t3' {A B:Prop} : A /\ B -> B.
  Proof.
    (** We can also do some destruction as we introduce things. *)
    intros [H1 H2].
    apply H2.
  Qed.

  Lemma t3'' {A B:Prop} : A /\ B -> B.
  Proof.
    (** There are some fancier decision procedures that can knock this
       sort of thing off, such as [firstorder].  For now, try to avoid
       using these so that you can understand the basic tactics --- you
       will need them. *)
    firstorder.
  Qed.

  Definition t4 {A B C:Prop} : 
    (A -> C) /\ (B -> C) -> (A \/ B) -> C.
  Proof.
    firstorder.
  Qed.

  Definition t5 {A:Prop} : False -> A.
  Proof.
    firstorder.
  Qed.

  Definition t6 {A B C D:Prop} : 
    (A -> B \/ C) -> (B -> D) -> (C -> D) -> (A -> D).
  Proof.
    firstorder.
  Qed.

  Locate "~ _".
  Check not.
  Print not.

  (** Negation [~A] is just an abbreviation for [A -> False]. *)
  Definition t7 {A B C : Prop} : 
    ~ (A /\ B) -> A -> B -> C.
  Proof.
    firstorder.
  Qed.
  
  (** We can write the type of [t7] using [forall], which shows that
      arrow types are really just a special case of a more powerful
      dependent type construct in which the type on the right-hand
      side of the arrow can mention the name of the argument. *)
  Definition t7' : forall {A B C:Prop}, 
    ~ (A /\ B) -> A -> B -> C.                   
  Proof.
    firstorder.
  Qed.

  Definition t7'' : 
    forall {A B C : Prop} (H1:~ (A /\ B)) (H2 : A) (H3 : B), C.
  Proof.
    firstorder.
  Qed.

  Locate "exists".
  Check ex.
  Print ex.

  Definition t8 : exists x:nat, x + 1 = 3.
  Proof.
    exists 2.
  (** The [exists] tactic is the way to solve an existential goal. 
      You have to give the witness. *)
    reflexivity.
  Qed.

End M2.
