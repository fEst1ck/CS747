Require Import Arith Nat List Utf8 Permutation.
Require Import CpdtTactics.
Import ListNotations.
Set Implicit Arguments.

Module Type A3Sig.

Definition nat_lte := Compare_dec.le_gt_dec.
Definition nat_eq := Nat.eq_dec.

Inductive list2_sub: list nat * list nat -> list nat * list nat -> Prop :=
| list2_sub_l: ∀ x xs ys, list2_sub (xs, ys) (x::xs, ys)
| list2_sub_r: ∀ y xs ys, list2_sub (xs, ys) (xs, y::ys).

Lemma list2_sub_wf: well_founded list2_sub.
Admitted.

Fixpoint merge_rec (xs_ys : list nat * list nat)
(ACC: Acc list2_sub xs_ys) {struct ACC} : list nat.
Admitted.

Arguments merge_rec xs_ys ACC : clear implicits.

Definition merge (xs ys : list nat) : list nat :=
  merge_rec (xs, ys) (list2_sub_wf _).

Definition list_all {A:Type} (P:A→Prop) (xs:list A) : Prop :=
  fold_right (fun h t => P h ∧ t) True xs.

Fixpoint sorted (xs:list nat) : Prop :=
  match xs with
    | nil => True
    | h::t => sorted t /\ list_all (le h) t
  end.

Definition count := count_occ nat_eq.

Lemma merge_preserves_list_all : ∀ P xs ys,
  list_all P xs → list_all P ys → list_all P (merge xs ys).
Admitted.

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

End A3Sig.
