(***************************************************)
(* Provide the following meta-data first.          *)
(* Your Name: Zekun Wang                           *)
(* Your WatIAM ID: z2358wan                        *)
(* Your Student ID: 20814732                       *)
(***************************************************)

(* 
   Submit ONLY this file (`A1Impl.v`) to Marmoset.
   
   Make sure that your submission compiles by running `make` in the
   directory containing your submission and the provided files. Use
   `Admitted.` if unsure how to complete a proof.

   The version of Coq you should use for this assignment is 8.20.0.

   This file is last updated on 2025-01-14.
*)

Require Import Utf8.
Require Import A1Sig.

(**
   ** Proving with proof terms

   For the first part of this assignment, write proof terms manually,
   as we did in the first lecture, instead of using tactics.  

   For each Definition provided, replace the "[.]" with
   "[:= <exp>.]" for some expression of the appropriate type.
   Remove the "[Admitted]" when you are done.
*)

Module Part1_Impl_ProofTerms.

Definition X1 : ∀ {A B C D:Prop}, (B ∧ (B → C ∧ D)) → D :=
  fun (A B C D:Prop) (H: B ∧ (B → C ∧ D)) =>
    match H with
      | conj H1 H2 =>
        match H2 H1 with
          | conj _ Hd => Hd
        end
    end.

Definition X2 : ∀ {A B C:Prop}, ¬(A ∨ B) → B → C :=
  fun (A B C:Prop) (H : ¬(A ∨ B)) (HB : B) =>
    match H (or_intror HB) with
    end.

Definition X3 : ∀ {A B C:Prop}, A ∧ (B ∨ C) → (A ∧ B) ∨ (A ∧ C) :=
  fun (A B C:Prop) (H:A ∧ (B ∨ C)) =>
    match H with
      | conj HA HBorC =>
        match HBorC with
          | or_introl HB => or_introl (conj HA HB)
          | or_intror HC => or_intror (conj HA HC)
        end
    end.

(** To solve the following, you will need to figure out what
   the definition of "[↔]" is and how to work with it. *)

Locate "↔".
Check iff.
Print iff.

Definition X4 : ∀ {A:Prop}, A ↔ A :=
  fun (A:Prop) =>
    conj (fun x => x) (fun x => x).

Definition X5 : ∀ {A B:Prop}, (A ↔ B) ↔ (B ↔ A) :=
  fun (A B:Prop) =>
    conj
      (fun AeqvB =>
        match AeqvB with
          | conj AimplB BimplA => conj BimplA AimplB
        end)
      (fun BeqvA =>
        match BeqvA with
          | conj BimplA AimplB => conj AimplB BimplA
        end).

Definition X6 : ∀ {A B C:Prop}, (A ↔ B) → (B ↔ C) → (A ↔ C) :=
  fun (A B C:Prop) (AeqvB:A ↔ B) (BeqvC:B ↔ C) =>
    match AeqvB with
      | conj AimplB BimplA =>
        match BeqvC with
        | conj BimplC CimplB =>
          conj
            (fun HA => BimplC (AimplB HA))
            (fun HC => BimplA (CimplB HC))
        end
    end.

(** Thought exercise:

   This is not provable in Coq without adding an axiom, even
   though in classical logic, we take this for granted:

   [P ∨ ¬P]

   Try to prove it and see what goes wrong...  Interestingly,
   this will almost never bite us.
*)

End Part1_Impl_ProofTerms.

(** The following line checks that your module implements the right
signature. Make sure that it works. *)
Module Part1_Impl_ProofTerms_correct : Part1_Sig := Part1_Impl_ProofTerms.

(** ** Proving with tactics
   
   Now redo these problems using only the following tactics:

   [intros, apply, destruct, unfold, split, contradiction, left, right]

   Replace the [Admitted.]'s with an appropriate proof.
   Don't forget to write [Qed.] to terminate your proofs.

   (Hopefully we haven't left off any that you may need.  In general,
   don't use things like [firstorder] or [tauto] that automatically
   solves goals.  We want you to perform the basic steps to see what
   is going on.)
*)
Module Part1_Impl_Tactics.

Fact X1 : ∀ {A B C D:Prop}, (B ∧ (B → C ∧ D)) → D.
Proof.
Admitted.

Fact X2 : ∀ {A B C:Prop}, ¬(A ∨ B) → B → C.
Proof.
Admitted.

Fact X3 : ∀ {A B C:Prop}, A ∧ (B ∨ C) → (A ∧ B) ∨ (A ∧ C).
Proof.
Admitted.

Fact X4 : ∀ {A:Prop}, A ↔ A. 
Proof.
Admitted.

Fact X5 : ∀ {A B:Prop}, (A ↔ B) ↔ (B ↔ A).
Proof.
Admitted.

Fact X6 : ∀ {A B C:Prop}, (A ↔ B) → (B ↔ C) → (A ↔ C).
Proof.
Admitted.

End Part1_Impl_Tactics.

Module Part1_Impl_Tactics_correct : Part1_Sig := Part1_Impl_Tactics.


(** ** Induction.
Next, we're going to exercise the [simpl], [induction], and
[rewrite] tactics.  It goes without saying that you shouldn't just
   prove these by using a library lemma :-)  However, if you get stuck
   proving one of these, then it is sometimes useful to look for one
   that does solve this, using the top-level [Search] command, and
   then [Print] the corresponding proof.
*)
Require Import List.

Module Part2_Impl.

Fact zero_plus_x : ∀ n, 0 + n = n.
Admitted.

Fact x_plus_zero : ∀ n, n + 0 = n.
Admitted.

Fact map_map : ∀ {A B C} (f : A → B) (g : B → C) (xs : list A), 
   map g (map f xs) = map (fun x => g (f x)) xs.
Admitted.

Fact app_assoc : ∀ {A} (xs ys zs : list A), 
   xs ++ (ys ++ zs) = (xs ++ ys) ++ zs.
Admitted.

Fact map_is_fold : ∀ {A B} (f : A → B) (xs : list A),
   map f xs = fold_right (fun x y => (f x) :: y) nil xs.
Admitted.

Definition list_sum (xs : list nat) : nat := fold_right plus 0 xs.

Fact list_sum_app : ∀ (t1 t2 : list nat), 
   list_sum (t1 ++ t2) = list_sum t1 + list_sum t2.
Admitted.

Inductive tree (A : Type) : Type := 
| Leaf : tree A
| Node : tree A → A → tree A → tree A.
Arguments Leaf {A}.
Arguments Node {A}.

Fixpoint mirror {A : Type} (t : tree A) : tree A := 
   match t with
   | Leaf => Leaf
   | Node lft v rgt => Node (mirror rgt) v (mirror lft)
   end.

Fact mirror_mirror : ∀ A (t:tree A), mirror (mirror t) = t.
Admitted.

Fixpoint flatten {A} (t : tree A) : list A := 
   match t with 
   | Leaf => nil
   | Node lft v rgt => (flatten lft) ++ v :: (flatten rgt)
   end.

Fixpoint tree_sum t : nat := 
   match t with 
   | Leaf => 0
   | Node lft v rgt => (tree_sum lft) + v + (tree_sum rgt)
   end.

Fact tree_flatten_sum : ∀ t, tree_sum t = list_sum (flatten t).
Admitted.

End Part2_Impl.

Module Part2_Impl_correct : Part2_Sig := Part2_Impl.


(**
   ** Modelling.
    
   Formalize the following puzzle:

   Three caskets (Gold, Silver, Lead) each have an inscription:
   - Gold: "The treasure is in this casket."
   - Silver: "The treasure is not in this casket."
   - Lead: "The treasure is not in the gold casket."

   At most one inscription is true. Prove which casket contains the
   treasure.
*)
Module Part3_Impl.

Inductive chest : Type := Silver | Gold | Lead.

Definition inChest (location c : chest) : Prop := location = c.

(** Formalize the inscriptions on the chests. *)
Definition chestInscription (location c : chest) : Prop.
Admitted.

Definition atMostOneInscriptionIsTrue location : Prop :=
  ∀ (c1 c2:chest), (chestInscription location c1) → (chestInscription location c2) → c1 = c2.

(** Prove the solution. *)
Theorem ItsSilver location :
  atMostOneInscriptionIsTrue location → inChest location Silver.
Admitted.

End Part3_Impl.

Module Part3_Impl_correct : Part3_Sig := Part3_Impl.

(***************************************************)
(* END OF ASSIGNMENT *)
(***************************************************)
