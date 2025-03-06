(***************************************************)
(* Provide the following meta-data first.          *)
(* Your Name:   Zekun Wang                         *)
(* Your WatIAM ID: z2358wan                        *)
(* Your Student ID: 20814732                       *)
(***************************************************)

(* 
   Submit ONLY this file (`A3Impl.v`) to Marmoset.
   
   Make sure that your submission compiles by running `make` in the
   directory containing your submission and the provided files. Use
   `Admitted.` if unsure how to complete a proof.

   The version of Coq you should use for this assignment is 8.20.0.

   This file is last updated on 2025-02-16.
*)

Require Import Arith Nat List Utf8 Permutation.
Require Import CpdtTactics.
Import ListNotations.
Set Implicit Arguments.
Require Import Coq.Program.Equality.

Module A3Impl.

Definition nat_lte := Compare_dec.le_gt_dec.
Definition nat_eq := Nat.eq_dec.

Print Acc.

Print well_founded.

(** In lecture we defined a merge sort function [merge_sort].
    There, the [merge] function was defined by stratifying
    recursion:

    Fixpoint merge (xs:list nat) : list nat → list nat := 
      match xs with 
        | nil => fun ys => ys
        | (x::xs') => 
          (fix inner_merge (ys:list nat) : list nat := 
            match ys with 
              | nil => x::xs'
              | y::ys' => if nat_lte x y then 
                            x :: (merge xs' (y::ys'))
                          else 
                            y :: (inner_merge ys')
            end)
      end.
*)

(** Alternatively, we can define [merge] by well-founded induction on
   the relation [list2_sub]. *)
Inductive list2_sub: list nat * list nat -> list nat * list nat -> Prop :=
| list2_sub_l: ∀ x xs ys, list2_sub (xs, ys) (x::xs, ys)
| list2_sub_r: ∀ y xs ys, list2_sub (xs, ys) (xs, y::ys).

(** Prove that [list2_sub] is well-founded. *)
Lemma list2_sub_wf: well_founded list2_sub.
Proof.
  unfold well_founded.
  intro a.
  destruct a as [xs ys].
  generalize ys.
  induction xs.
  + induction ys.
    - intro ys.
      induction ys.
      * constructor.
        intros y Contra.
        inversion Contra.
      * constructor.
        intros y H.
        inversion H.
        subst.
        assumption.
    - assumption. 
  + intro r.
    constructor.
    intros l H.
    inversion H; subst.
    - apply IHxs.
    - induction ys0.
      * constructor.
        intros.
        inversion H0; subst.
        apply IHxs.
      * constructor.
        intros.
        inversion H0; subst.
        {
          apply IHxs.
        }
        {
          apply IHys0.
          constructor.
        }
Defined.

(** Define [merge_rec] by well-founded induction on [Acc list2_sub]. *)
Program Fixpoint merge_rec (xs_ys : list nat * list nat)
(ACC: Acc list2_sub xs_ys) {struct ACC} : list nat :=
  match xs_ys with
  | (nil, ys) => ys
  | (xs, nil) => xs
  | (x::xs', y::ys') =>
    if nat_lte x y then x :: @merge_rec (xs', y::ys') (Acc_inv ACC _)
    else y :: @merge_rec (x::xs', ys') (Acc_inv ACC _)
  end.
Next Obligation.
constructor.
Defined.
Next Obligation.
constructor.
Defined.

(* Make the [xs_ys] argument of [merge_rec] explicit. *)
Arguments merge_rec xs_ys ACC : clear implicits.

(* Test [merge_rec]. *)
(* Eval compute in merge_rec ([1;3;5], [2;4;6]) (list2_sub_wf _). *)
(* Eval compute in merge_rec ([5], [0;5;10;15]) (list2_sub_wf _). *)

Definition merge (xs ys : list nat) : list nat :=
  merge_rec (xs, ys) (list2_sub_wf _).

(* Eval compute in merge [1;3;5] [2;4;6]. *)
(* Eval compute in merge [5] [0;5;10;15]. *)

(* Let's prove some properties about [merge] *)

(** [list_all P xs] holds when [P] holds on each element of [xs] *)
Definition list_all {A:Type} (P:A→Prop) (xs:list A) : Prop :=
  fold_right (fun h t => P h ∧ t) True xs.

(* We can use list_all to define a notion of a sorted list. *)
Fixpoint sorted (xs:list nat) : Prop :=
  match xs with
    | nil => True
    | h::t => sorted t /\ list_all (le h) t
  end.

Definition count := count_occ nat_eq.

(** To prove [merge_preserves_list_all] for [merge], it is helpful to first prove [merge_rec_preserves_list_all] for [merge_rec] by well-founded induction.  Mutatis mutandis, for the other properties you will prove below about [merge]. *)
Lemma merge_rec_preserves_list_all : ∀ P xs_ys ACC,
  list_all P (fst xs_ys) → list_all P (snd xs_ys) → list_all P (@merge_rec xs_ys ACC).
Proof.
  intros P xs_ys.
  destruct xs_ys as [xs ys].
  generalize ys.
  induction xs.
  + intro ys'.
    intro ACC.
    assert (merge_rec ([], ys') ACC = ys').
    {
      destruct ACC.
      cbn.
      reflexivity.
    }
    rewrite H.
    crush.
  + simpl in *.
    assert (
      ∀ (ys : list nat) (ACC : Acc list2_sub (a :: xs, ys)),
        list_all P (a :: xs) → list_all P ys → list_all P (merge_rec (a :: xs, ys) ACC)
    ).
    {
      intros.
      induction ys0.
      + destruct ACC.
        crush.
      + destruct ACC.
        simpl.
        destruct (nat_lte a a0).
        * simpl.
          split. { crush. }
          apply IHxs; crush.
        * split. { crush. }
          apply IHys0.
          crush.
    }
    intros.
    destruct ys0.
    - destruct ACC.
      cbn.
      crush.
    - destruct ACC.
      simpl.
      destruct (nat_lte a n).
      * simpl.
        split. { crush. }
        apply IHxs; crush.
      * split. { crush. }
        apply H; crush.
Qed.

Lemma merge_preserves_list_all : ∀ P xs ys,
  list_all P xs → list_all P ys → list_all P (merge xs ys).
Proof.
  intros P xs ys Hxs Hys.
  apply merge_rec_preserves_list_all; crush.
Qed.

Lemma merge_preserves_sorted : ∀ xs ys,
   sorted xs → sorted ys → sorted (merge xs ys).
Admitted.

Lemma merge_preserves_length : ∀ xs ys,
   (length xs + length ys) = length (merge xs ys).
Admitted.

Lemma merge_preserves_In : ∀ xs ys x,
  In x xs \/ In x ys ↔ In x (merge xs ys).
Admitted.

Lemma merge_preserves_permutation_app : ∀ xs ys,
  Permutation (xs ++ ys) (merge xs ys).
Admitted.

Lemma perm_preserves_count : ∀  n xs ys, Permutation xs ys →
  count xs n = count ys n.
Admitted.

Lemma app_preserves_count :
  ∀  x xs ys, count xs x + count ys x = count (xs ++ ys) x.
Admitted.

Lemma merge_preserves_count : ∀ (xs ys : list nat) x,
   count xs x + count ys x = count (merge xs ys) x.
Admitted.

End A3Impl.

(***************************************************)
(* END OF ASSIGNMENT *)
(***************************************************)
