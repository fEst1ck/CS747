Require Import List CpdtTactics Lia Utf8.
Import ListNotations.
Set Implicit Arguments.

(* Correctness of sorting algorithms *)

(* Let's start with insertion sort.  The idea is simple:
   we take the last element of the list and insert it
   into the empty list.  Then we take the second last element
   and insert it into the list with the last element
   inserted.  We continue in this way until we've inserted
   all the elements. *)

(* First, we need a way to compare nats. *)

Print le.
(* [le] is an inductively defined Prop. We need something computable. *)

(* An abbreviation which given two nats n and m, 
   decides whether {n ≤ m} or {n > m}. *)
Definition nat_lte := Compare_dec.le_gt_dec.
About nat_lte.

(* Insert a number into a list.
   Assumes the list is sorted in non-decreasing order. *)
Fixpoint insert (n:nat) (xs:list nat) : list nat := 
  match xs with 
    | [] => [n]
    | h::t => if nat_lte n h then n::h::t else h::(insert n t)
  end.

(* Insertion sort. *)
Fixpoint insert_sort (xs:list nat) : list nat := 
  match xs with
  | [] => []
  | h :: t => insert h (insert_sort t)
  end.

(* Simple test. *)
Eval compute in insert_sort [3;2;5;1;7;3].

(* Define [insert_sort] using [fold_right] *)
Definition insert_sort' (xs:list nat) : list nat := 
  fold_right insert [] xs.
Eval compute in insert_sort' [3;2;5;1;7;3].

(* A useful predicate on lists.
   [list_all P xs] holds when [P] holds on each element of [xs]. *)
Definition list_all (A:Type) (P:A → Prop) (xs:list A) : Prop := 
  fold_right (λ h t, P h /\ t) True xs.

(* We can use [list_all] to define a notion of a sorted list. *)
Fixpoint sorted (xs:list nat) : Prop := 
  match xs with 
    | [] => True
    | h::t => sorted t /\ list_all (le h) t
  end.

(* Notice that [sorted] produces a [Prop] (which we can't evaluate!) *)
Eval compute in sorted [3;1;2].

(* We can prove propositions though. *)
Example sorted_123 : sorted [1;2;3].
Proof.
simpl. 
auto.
auto 100.
Qed.

(* Here's an alternative definition of "sortedness" using a
   couple of inductive definitions.

   [list_lte n l] holds when [n] is less than or equal to each
    element of [l]. *)
Inductive list_lte : nat → list nat → Prop := 
| nil_list_lte : ∀ n, list_lte n nil
| cons_list_lte : ∀ n h t, n ≤ h → list_lte n t → list_lte n (h::t).

Inductive sorted' : list nat → Prop := 
| nil_is_sorted : sorted' nil
| cons_is_sorted : ∀ h t, list_lte h t → sorted' t → sorted' (h::t).

(* And here's an example proof that the list [1;2;3] is sorted'. *)
Example sorted'_123 : sorted' [1;2;3].
Proof.
repeat constructor.
Qed.

(* Prove the two definitions of sorted'ness are equivalent.

   First, we prove a lemma that estalishes equivalence between
   [list_lte n] and [list_all (le n)].
*)
Lemma list_lte_iff_list_all_lte : 
∀ n (xs:list nat), list_lte n xs <-> list_all (le n) xs.
Proof.
induction xs; simpl; split; intro H.
- apply I.
- constructor.
- inversion H. crush.
- constructor; crush.
Qed.

Lemma sorted_iff_sorted' : 
  ∀ (xs : list nat), sorted xs <-> sorted' xs.
Proof.
induction xs; simpl; split; intro H.
- constructor.
- trivial.
- constructor.
  + rewrite list_lte_iff_list_all_lte. crush.
  + crush.
- inversion H. split.
  + crush.
  + rewrite <- list_lte_iff_list_all_lte. crush.
Qed.

(* Let's try to prove that [insert_sort] is CORRECT! *)
Lemma insert_sort_sorted : ∀ xs, sorted (insert_sort xs).
Proof.
induction xs as [ | a xs IHxs ] ; crush.
simpl in *.
(* We're stuck since Rocq doesn't know if (insert a (insert_sort xs))
  is empty or a cons.

  What we need to do first is prove something useful about 
  [insert]. For example, if [xs] is sorted and we insert [a] into
  it, we should get back a sorted list.
   
  Lemma insert_sorted : ∀ a xs, sorted xs → sorted (insert a xs).
   
  Before juming into that, let me define some useful lemmas.
  Let's abort... *)
Abort.

(* A useful lemma that lifts implication to list_all.  It says
   that if P x → Q x for any x, then list_all P xs → list_all Q xs.
*)
Lemma list_all_imp A: 
∀ (P Q : A → Prop),
(∀ (x:A), P x → Q x) → 
∀ (xs:list A), list_all P xs → list_all Q xs.
Proof.
intros P Q H.
induction xs ; crush.
Qed.

(* So let's try to prove this fact now... *)
Lemma insert_sorted : ∀ n xs, sorted xs → sorted (insert n xs).
Proof.
induction xs; simpl; [ crush | ].
destruct (nat_lte n a) ; simpl.
+ intros. repeat split.
  - crush.
  - crush. 
  - crush.
  - apply list_all_imp with (P := le a).
    * intros. lia.
    * crush.
+ intros. split.
  - crush.
  - (* Ugh!  How are we supposed to prove that a ≤ insert n xs?
     Intuitively it's true, but how can we show this?  We need
     to know that if we insert n into xs, then the elements [In] 
     the resulting list are either equal to n or one of the xs.
    *)

    About In.
    Print In.

    (*
    Lemma in_list_all A (P:A → Prop) (xs:list A) : 
    (∀ x, In x xs → P x) <-> list_all P xs.

    Lemma in_insert :
    ∀ (x:nat) (xs:list nat) (n:nat)
    In x (insert n xs) <-> x = n \/ In x xs.
    *)
Abort.

(* An equivalent way to capture "list_all" *)
Lemma in_list_all A (P:A → Prop) (xs:list A) : 
(∀ x, In x xs → P x) <-> list_all P xs.
Proof.
induction xs ; crush.
Qed.

(* Now we can prove that if you insert [n] into [xs], then
   any element of the resulting list is either equal to
   [n] or one of the [xs]. *)
Lemma in_insert :
∀ (x:nat) (xs:list nat) (n:nat), 
In x (insert n xs) → x = n \/ In x xs.
Proof.
induction xs as [ | a xs IHxs ]; simpl in *; intros n H.
{ crush. }
destruct (nat_lte n a); simpl in *.
{ crush. }
destruct H.
{ crush. }
specialize (IHxs _ H). crush.
Qed.

(* The opposite fact will also be useful. *)
Lemma insert_in : 
∀ (x:nat) (xs:list nat) (n:nat), 
x = n \/ In x xs → In x (insert n xs).
Proof.
induction xs as [ | a xs IHxs]; simpl in *; intros n H.
{ crush. }
destruct (nat_lte n a) ; crush.
Qed.

(* Now let's try to prove this fact again... *)
Lemma insert_sorted : ∀ n xs, sorted xs → sorted (insert n xs).
Proof.
induction xs as [ | a xs IHxs ]; simpl in *; intros H.
{ crush. }
destruct (nat_lte n a) ; simpl.
+ repeat split.
  - crush.
  - crush. 
  - crush.
  - apply list_all_imp with (P := le a).
    * intros. lia.
    * crush.
+ intros. split.
  - (* uses IH *)
    crush.
  - (* we were stuck here *)
    clear IHxs. (* we don't need IH; get it out of our sight *)
    
    (* here's where in_list_all comes into play -- we turn the
    list_all into reasoning about an arbitrary element in 
    (insert n xs). *)
    apply in_list_all.
    intros x Hx.

    (* here's where in_insert comes into play -- we can now
    reason about the element x, which has to be either n or
    one of the xs. *)
    apply in_insert in Hx.
    destruct Hx.
    { lia. }

    (* here's where the opposite direction of in_list_all comes into play. *)
    destruct H as [_ H].
    rewrite <- in_list_all in H.
    crush.
Qed.

(* Once we've proved that insert produces a sorted list, we
   can easily prove that [insert_sort] produces a sorted list. *)
Lemma insert_sort_sorted : ∀ xs, sorted (insert_sort xs).
Proof.
  induction xs as [ | a xs IHxs ].
  { crush. }
  apply insert_sorted; auto.
Qed.

(* Can we declare we have proven [insert_sort] is CORRECT?

   note that the following function also produces a sorted list:
*)
Definition bogus_sort (xs:list nat) : list nat := nil.

Lemma bogus_sort_sorted (xs:list nat) : sorted (bogus_sort xs).
Proof.
  apply I.
Qed.

(* Here's an attempt to capture what it means for a sort
   function to actually be correct.   The output should
   be sorted, the length of the input should equal the
   length of the output, and every member of the input
   should be in the output (and vice versa, though this
   can be shown given that the lengths are the same.)
*)
Definition sublist A (xs ys:list A) : Prop := 
  ∀ (x:A), In x xs → In x ys.

Definition sort_corr (xs ys:list nat) : Prop := 
  sorted ys /\ sublist xs ys /\ length xs = length ys.

(* There are, of course, alternative definitions.  For
   instance, we might specify that the output is a sorted
   permutation of the input.
*)
Require Import Sorting.Permutation.
Definition sort_corr' (xs ys:list nat) : Prop := 
  sorted ys /\ Permutation xs ys.

(* Let's prove now that our insertion sort is "correct",
   according to [sort_corr].
   We have already shown insert_sort produces a sorted list. 
   Now we just need to establish the other two properties: *)
Lemma insert_sort_sublist : ∀ xs, sublist xs (insert_sort xs).
Proof.
  unfold sublist.
  induction xs ; crush ; apply insert_in ; crush.
Qed.

Lemma insert_length : ∀ xs n, length (insert n xs) = S (length xs).
Proof.
  induction xs as [ | a xs IHxs ]; simpl in *; intro n.
  { crush. }
  destruct (nat_lte n a) ; crush.
Qed.

Lemma insert_sort_length : ∀ xs, length xs = length (insert_sort xs).
Proof.
  induction xs as [ | a xs IHxs ]; simpl in *.
  { crush. }
  rewrite IHxs.
  rewrite insert_length.
  reflexivity.
Qed.

(* And finally, we can show insertion sort is correct. *)
Lemma insert_sort_corr : ∀ xs, sort_corr xs (insert_sort xs).
Proof.
unfold sort_corr. intro.
repeat split.
- apply insert_sort_sorted.
- apply insert_sort_sublist.
- apply insert_sort_length.
Qed.

(********************************************************)

(* Of course, we don't want to use an O(n^2) sort in practice.
   So here, I develop a merge sort.  This shows off something
   new -- defining a recursive function using something besides
   structural induction to establish termination.
*)


(* First, we need to define a function to merge two (already
   sorted lists).  Now normally, we'd write this as follows:
*)


(* Fixpoint merge (xs ys:list nat) : list nat := 
  match xs, ys with 
  | [], ys => ys
  | xs, [] => xs
  | h1::t1, h2::t2 => if nat_lte h1 h2 then 
                        h1 :: (merge t1 ys)
                      else
                        h2 :: (merge xs t2)
  end. *)


(*
   Unfortunately, Rocq rejects this because it's
   not the case that xs is always getting smaller, nor
   the case that ys is always getting smaller.  Of course,
   *one* of them is always getting smaller, so eventually,
   this will terminate.  

   But in this case, we can hack around the problem by
   simply re-organizing the function as follows:
*)
Fixpoint merge (xs:list nat) : list nat → list nat := 
  match xs with 
    | nil => fun ys => ys
    | (x::xs') => 
      (fix inner_merge (ys:list nat) : list nat := 
         match ys with 
           | nil => xs
           | y::ys' => if nat_lte x y then 
                         x :: (merge xs' ys)
                       else 
                         y :: (inner_merge ys')
         end)
  end.
(* Note that for the outer loop, we only call it with a
   smaller xs, and for the inner loop, we only call it
   with a smaller ys.  So Rocq can see by structural
   induction on the loops that the definition terminates.

   Note that if you tried to pull inner_merge out and
   define it as a top-level function, Rocq would no 
   longer be able to tell that merge terminates.  
   In this sense, Rocq's termination checking isn't
   modular.
*)

(* Test that merge works. *)
Eval compute in merge [1;3;5] [2;4;6].
Eval compute in merge [5] [0;5;10;15].

(* Now we can define a function that merges a list of lists. *)

(* This function takes a list of lists of nats, and 
   merges each pair of lists.  See the example below. *)
Fixpoint merge_pairs (xs:list (list nat)) : list (list nat) := 
  match xs with 
    | h1::h2::t => (merge h1 h2) :: (merge_pairs t)
    | xs' => xs'
  end.

Eval compute in merge_pairs [[1;3];[2;4;9];[0];[2;3]].
Eval compute in merge_pairs [[1;3];[2;4;9];[0]].

(* To define our actual merge sort, we want to take the
   initial list [n1;n2;...;nm] and turn it into a list of 
   singleton lists: [[n1];[n2];...;[nm]] and then successively
   call merge_pairs until we get a single list out. *)

(* This function takes a list and turns it into a list
   of singleton lists of the elements. *)
Definition make_lists (xs:list nat) : list (list nat) := 
  List.map (fun x => [x]) xs.

Eval compute in make_lists [5; 1; 4; 2; 3].
Eval compute in merge_pairs (make_lists [5; 1; 4; 2; 3]).
Eval compute in merge_pairs (merge_pairs (make_lists [5; 1; 4; 2; 3])).
Eval compute in merge_pairs (merge_pairs (merge_pairs (make_lists [5; 1; 4; 2; 3]))).

(* As with merge, I would like to write the following function
   which is intended to iterate merging the pairs of a list of
   lists until we get a single list out:
*)

(* Fixpoint merge_iter (xs:list (list nat)) : list nat := 
  match xs with 
  | [] => []
  | [h] => h
  | h1::h2::xs' => merge_iter (merge_pairs (h1::h2::xs'))
  end. *)

(*
  But Rocq can't tell that this terminates.  The problem is
  that we are calling merge_iter on (merge_pairs (h1::h2::xs'))
  instead of xs'.  Since in principle, merge_pairs could return
  a list no smaller than the input, Rocq rejects the definition.

  All is not lost, though.  In Rocq, we can define functions
  that use an arbitrary measure (or really, any well-founded
  relation) and show that the measure is always decreasing
  to convince Rocq the function terminates.  

  Before doing that, I need to establish a lemma that:

    length (merge_pairs (h1::h2::xs)) < length (h1::h2::xs)
*)

(*
  This is a little tricky to prove since we are peeling off
  two elements instead of one. Here's one way.
*)
Lemma merge_pairs_length : 
∀ xs h1 h2, length (merge_pairs (h1::h2::xs)) < length (h1::h2::xs).
Proof.
  induction xs as [ | h3 xs IHxs ]; intros.
  { simpl. lia. }
  specialize (IHxs h2 h3).
  (* we are stuck — our IH is not precise enough. *)
Abort.

Lemma merge_pairs_length' : 
  ∀ xs,
  (∀ h1 h2, length (merge_pairs (h1::h2::xs)) < length (h1::h2::xs)) /\
  (∀ h, length (merge_pairs (h::xs)) ≤ length (h::xs)).
Proof.
  induction xs ; crush.
Qed.
(* 
  Notice the second part of the lemma.
  What merge_pairs_length' does is generalize the desired
  property to one that holds regardless of the number of elements
  in the list.
*)

(* The decreasing measure is now easy to establish from the
   lemma above. *)
Lemma merge_pairs_length : 
  ∀ h1 h2 xs, length (merge_pairs (h1::h2::xs)) < length (h1::h2::xs).
Proof.
  intros.
  specialize (merge_pairs_length' xs) as [H _].
  apply H.
Qed.

(* Now we define our merge_iter function.  Since it's
   not structurally recursive, but rather, defined using a measure,
   we first need to import a couple of libraries. *)
Require Import Recdef.

(* The [Function] construct is similar to the [Fixpoint]
   construct.  The big difference is that we must state
   a [{measure ...}] clause to tell Rocq what is going
   down.  In this case, the length of the argument list is always
   going down when we do a recursive call.
 *)
Function merge_iter (xs: list (list nat)) { measure length xs } : list nat :=
  match xs with 
    | nil => nil
    | h::nil => h
    | h1::h2::xs' => merge_iter (merge_pairs (h1::h2::xs'))
  end.
Proof.
(* Notice that Rocq spits out a bunch of stuff here and says
   there's 1 obligation remaining.  This obligation arises
   as a result of the recursive call -- we need to show that
   the measure is actually decreasing.  *)
intros.
apply merge_pairs_length.
Defined.


(* Alternatively, you can use [Program Fixpoint], but this doesn't
  generate all of the same useful features. 
*)
Require Import Program.
Program Fixpoint
  merge_iter' (xs : list (list nat)) {measure (length xs)} : list nat :=
  match xs with 
    | nil => nil
    | h::nil => h
    | h1::h2::xs' => merge_iter' (merge_pairs (h1::h2::xs'))
  end.
(* The command [Next Obligation] let's us provide a proof of the
  needed fact.  Note that until we finish the proofs of all obligations,
  the function [merge_iter] is not defined. *)
Next Obligation.
apply merge_pairs_length.
Qed.

(* Once we've defined our merge_iter, we can finally define
   our merge_sort: *)
Definition merge_sort (xs:list nat) := 
  merge_iter (make_lists xs).

(* Let's test that it's working... *)
Eval compute in merge_sort [7;8;3;5;1;2;6;4].
Eval compute in merge_sort [3;2;7;8].

(* Exercise: Show that merge_sort is CORRECT! *)

(********************************************************)

(* If we print out merge_iter... *)
Print merge_iter.
Print merge_iter_terminate.
(* ...we see that the [Function] did a lot of work for us
   to translate our definition into the real core of Rocq. *)

Print well_founded.
Print Acc.

(* What does it mean for a relation to be well-founded?

    well_founded = λ (A : Type) (R : A → A → Prop), ∀ a : A, Acc R a

    Inductive Acc (A : Type) (R : A → A → Prop) (x : A) : Prop :=
      Acc_intro : (∀ y : A, R y x → Acc R y) → Acc R x.
  
  The "accessible" notion is capturing the idea that our relation has
  no infinite descending chains. "Well-founded" means that every element
  is accessible.
  
  In the case of <, there is a least element, namely 0.  So if we are
  always going down in the relation, we will eventually get to 0.
*)

(* Prove that [lt] is well-founded *)
Lemma lt_wf : well_founded lt.
Proof.
unfold well_founded.
intro n.
induction n as [ | n IHn].
{ constructor. intros. lia. }
constructor.
intros m H.

inversion IHn.
destruct (PeanoNat.Nat.eq_dec m n).
+ subst. apply IHn.
+ apply H0. lia.
Defined.

Print well_founded_induction.
(*
  well_founded_induction
     : ∀ (A : Type) (R : A → A → Prop) (Rwf : well_founded R) (P : A → Type),
       (∀ x : A, (∀ y : A, R y x → P y) → P x) → ∀ x : A, P x
*)
Print well_founded_induction_type.
Print Acc_rect.
(* It's just the induction principle for the Acc inductive type!!! *)

(* Define merge_iter by structural induction on ACC *)
Fixpoint merge_iter'' (xs: list (list nat)) (ACC : Acc lt (length xs)) : list nat.
Proof.
  refine (
    (match xs as l return xs = l → list nat with
      | nil => fun Hyp => nil
      | h::nil => fun Hyp => h
      | h1::h2::xs' => fun Hyp => merge_iter'' (merge_pairs (h1::h2::xs')) _
    end) eq_refl
  ).
  subst.
  (* Need a subterm of ACC to fill in the hole! *)
  inversion ACC as [H].
  apply H.
  apply merge_pairs_length.
Defined.

(* Define merge_sort *)
Definition merge_sort'' (xs:list nat) : list nat :=
  merge_iter'' (make_lists xs) (lt_wf _).

(* Let's test that it's working... *)
Eval compute in merge_sort'' [19;5;43;77;81;89;29;1;20;94;38;66;35;83;8;84;92;13;42;55;62;80;41;87;16;57;53;58;11;15;74;48;21;32;67;64;97;40;71;93;54;9;39;7;76;72;27;34;78;68;99;65;46;25;17;88;63;91;24;69;6;49;70;85;30;79;95;47;82;75;45;44;100;14;0;4;96;50;31;90;56;59;86;51;52;33;10;98;23;28;2;60;12;37;26;18;22;36;73;61;3].

(* Exercise: Show that merge_sort'' is CORRECT! *)
