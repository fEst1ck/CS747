(*
  The file that you are currently reading (`A1Sig.v`) contains only
  the signatures of the programs that we will implement.  Your job is
  to write modules that implement the signatures.
  
  Your `A1Impl.v` file is what you upload to Marmoset to get credit
  for doing the assignment.

  This file is last updated on 2025-01-14.
*)

Require Import Utf8.

Module Type Part1_Sig.

  Parameter X1 : ∀ {A B C D:Prop}, (B ∧ (B → C ∧ D)) → D.

  Parameter X2 : ∀ {A B C:Prop}, ¬(A ∨ B) → B → C.

  Parameter X3 : ∀ {A B C:Prop}, A ∧ (B ∨ C) → (A ∧ B) ∨ (A ∧ C).

  Parameter X4 : ∀ {A:Prop}, A ↔ A. 

  Parameter X5 : ∀ {A B:Prop}, (A ↔ B) ↔ (B ↔ A).

  Parameter X6 : ∀ {A B C:Prop}, (A ↔ B) → (B ↔ C) → (A ↔ C).

End Part1_Sig.


Require Import List.

Module Type Part2_Sig.

  Parameter zero_plus_x : ∀ n, 0 + n = n.

  Parameter x_plus_zero : ∀ n, n + 0 = n.

  Parameter map_map : ∀ {A B C} (f : A → B) (g : B → C) (xs : list A), 
    map g (map f xs) = map (fun x => g (f x)) xs.

  Parameter app_assoc : ∀ {A} (xs ys zs : list A), 
    xs ++ (ys ++ zs) = (xs ++ ys) ++ zs.

  Parameter map_is_fold : ∀ {A B} (f : A → B) (xs : list A),
    map f xs = fold_right (fun x y => (f x) :: y) nil xs.

  Definition list_sum (xs : list nat) : nat := fold_right plus 0 xs.

  Parameter list_sum_app : ∀ (t1 t2 : list nat), 
     list_sum (t1 ++ t2) = list_sum t1 + list_sum t2.

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

  Parameter mirror_mirror : ∀ A (t:tree A), mirror (mirror t) = t.

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

  Parameter tree_flatten_sum : ∀ t, tree_sum t = list_sum (flatten t).

End Part2_Sig.


Module Type Part3_Sig.

Inductive chest : Type := Silver | Gold | Lead.

Definition inChest (location c : chest) : Prop := location = c.

Parameter chestInscription: ∀ (location c : chest), Prop.

Definition atMostOneInscriptionIsTrue (location : chest) : Prop :=
  ∀ (c1 c2:chest), (chestInscription location c1) → (chestInscription location c2) → c1 = c2.

Parameter ItsSilver : ∀ location, atMostOneInscriptionIsTrue location → inChest location Silver.

End Part3_Sig.
