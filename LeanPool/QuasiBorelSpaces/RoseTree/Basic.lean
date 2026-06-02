/-
Copyright (c) 2026 Anthony Vandikas, Kiarash Sotoudeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Vandikas, Kiarash Sotoudeh
-/

import LeanPool.QuasiBorelSpaces.RoseTree.Defs
import Mathlib.Tactic.NthRewrite
import Mathlib.Control.Traversable.Instances

/-!
# LeanPool.QuasiBorelSpaces.RoseTree.Basic

Imported Lean Pool material for `LeanPool.QuasiBorelSpaces.RoseTree.Basic`.
-/


universe u

variable {A B C D : Type*}

namespace Rose

@[simp]
lemma eta (t : Rose A) : mk t.label t.children = t := by
  cases t
  rfl

@[simp]
lemma label_bind (f : A → Rose B) (t : Rose A) : (bind f t).label = (f t.label).label := by
  cases t
  simp only [bind.eq_1]

@[simp]
lemma children_bind
    (f : A → Rose B) (t : Rose A)
    : (bind f t).children = (f t.label).children ++ List.map (bind f) t.children := by
  cases t
  simp only [bind.eq_1]

@[simp]
lemma label_map (f : A → B) (t : Rose A) : (map f t).label = f t.label := by
  simp only [map, label_bind]

@[simp]
lemma children_map
    (f : A → B) (t : Rose A)
    : (map f t).children = List.map (map f) t.children := by
  simp only [map, children_bind, List.nil_append]

@[induction_eliminator]
lemma induction
    (motive : Rose A → Prop)
    (mk : (label : A)
        → (children : List (Rose A))
        → (ih : ∀ t ∈ children, motive t)
        → motive (.mk label children))
    (t : Rose A)
    : motive t := by
  induction t using rec with
  | mk label children ih =>
    apply mk
    apply ih
  | nil =>
    simp only [List.not_mem_nil, false_implies, implies_true]
  | cons label children ih tail_ih =>
    simp only [List.mem_cons, forall_eq_or_imp, ih, true_and]
    exact tail_ih

lemma induction'
    (motive : Rose A → Prop)
    (mk : (label : A)
        → (children : List (Rose A))
        → (ih : ∀ i : Fin children.length, motive children[i])
        → motive (.mk label children))
    (t : Rose A)
    : motive t := by
  induction t with | mk label children ih =>
  grind

lemma bind_pure (t : Rose A) : bind (fun x ↦ ⟨x, []⟩) t = t := by
  induction t with | mk label children ih =>
  simp only [bind, List.nil_append, mk.injEq, true_and]
  nth_rw 2 [← List.map_id' children]
  simp only [List.map_inj_left]
  exact ih

@[simp]
lemma bind_pure_fun : bind (A := A) (fun x ↦ ⟨x, []⟩) = id := by
  ext
  apply bind_pure

@[simp]
lemma bind_bind
    (f : B → Rose C) (g : A → Rose B) (t : Rose A)
    : bind f (bind g t) = bind (fun x ↦ bind f (g x)) t := by
  induction t with | mk label children ih =>
  simp_all only [
    bind.eq_1, List.map_append, List.map_map, label_bind, children_bind,
    List.append_assoc, mk.injEq, List.append_cancel_left_eq, List.map_inj_left,
    Function.comp_apply, implies_true, and_self]

@[simp]
lemma bind_comp
    (f : B → Rose C) (g : A → Rose B)
    : bind f ∘ bind g = bind (bind f ∘ g) := by
  ext t
  apply bind_bind

@[simp]
lemma bind_comp_r
    (f : B → Rose C) (g : A → Rose B) (h : D → Rose A)
    : bind f ∘ bind g ∘ h = bind (bind f ∘ g) ∘ h := by
  ext t
  apply bind_bind

@[simp]
lemma fold_eq_bind
    (f : A → Rose B)
    : fold (fun x xs ↦ ⟨(f x).label, (f x).children ++ xs⟩) = bind f := by
  ext t
  induction t with | mk label children ih
  simp only [
    fold.eq_1, bind.eq_1, mk.injEq, List.append_cancel_left_eq,
    List.map_inj_left, true_and]
  exact ih

@[simp]
lemma map_mk
    (f : A → B) (x : A) (xs : List (Rose A))
    : map f ⟨x, xs⟩ = ⟨f x, List.map (map f) xs⟩ := by
  unfold map
  simp only [bind.eq_1, List.nil_append]

@[simp]
lemma map_id {f : A → A} (hf : ∀ x, f x = x) (t) : map f t = t := by
  unfold map
  simp only [hf, bind_pure_fun, id_eq]

@[simp]
lemma map_map
    (f : B → C) (g : A → B) (t : Rose A)
    : map f (map g t) = map (fun x ↦ f (g x)) t := by
  unfold map
  simp only [bind_bind, bind.eq_1, List.map_nil, List.append_nil]

@[simp]
lemma map_bind
    (f : B → C) (g : A → Rose B) (t : Rose A)
    : map f (bind g t) = bind (fun x ↦ map f (g x)) t := by
  unfold map
  simp only [bind_bind]

@[simp]
lemma bind_map
    (f : B → Rose C) (g : A → B) (t : Rose A)
    : bind f (map g t) = bind (fun x ↦ f (g x)) t := by
  unfold map
  simp only [bind_bind, bind.eq_1, List.map_nil, List.append_nil, eta]

@[simp]
lemma bind_eq_map (f : A → B) (t : Rose A) : bind (fun x ↦ ⟨f x, []⟩) t = map f t := by rfl

@[simp]
lemma fold_map
    (f : B → List C → C) (g : A → B) (t : Rose A)
    : fold f (map g t) = fold (fun x ↦ f (g x)) t := by
  induction t with | mk label children ih =>
  simp only [map_mk, fold.eq_1, List.map_map]
  congr 1
  simp only [List.map_inj_left, Function.comp_apply]
  exact ih

@[simp]
lemma bind_eq {B} (t : Rose A) (f : A → Rose B) : Bind.bind t f = bind f t := rfl

@[simp]
lemma pure_eq (x : A) : (pure x : Rose A) = ⟨x, []⟩ := rfl

@[simp]
lemma seq_eq {B} (f : Rose (A → B)) (t : Rose A) : f <*> t = bind (fun f ↦ map f t) f := rfl

@[simp]
lemma map_eq {B} (f : A → B) (t : Rose A) : f <$> t = map f t := rfl

@[simp]
lemma seqLeft_eq {B} (t : Rose A) (u : Rose B) : t <* u = bind (fun x ↦ map (fun _ ↦ x) u) t := rfl

@[simp]
lemma seqRight_eq {B} (t : Rose A) (u : Rose B) : t *> u = bind (fun _ ↦ u) t := rfl

instance : LawfulMonad Rose where
  bind_pure_comp := by
    simp only [pure_eq, bind_eq, bind_eq_map, map_eq, implies_true]
  bind_map := by
    simp only [map_eq, bind_eq, seq_eq, implies_true]
  pure_bind := by
    simp only [pure_eq, bind_eq, bind, List.map_nil, List.append_nil, eta, implies_true]
  bind_assoc := by
    simp only [bind_eq, bind_bind, implies_true]
  seqLeft_eq := by
    simp (unfoldPartialApp := true) only [
      seqLeft_eq, Function.const, map_eq, seq_eq, bind_map, implies_true]
  seqRight_eq := by
    simp only [seqRight_eq, map_eq, seq_eq, bind_map, Function.const_apply, id_eq, implies_true,
      map_id]
  pure_seq := by
    simp only [pure_eq, seq_eq, map_eq, bind.eq_1, List.map_nil, List.append_nil, eta, implies_true]
  id_map := by
    simp only [map_eq, id_eq, implies_true, map_id]
  map_const := rfl

@[simp]
private lemma traverse_map
    {F : Type _ → Type _} [Applicative F] [LawfulApplicative F]
    (f : B → F C)
    (g : A → B) (xs : List A)
    : List.traverse f (List.map g xs) = List.traverse (fun x ↦ f (g x)) xs := by
  induction xs with
  | nil => simp only [List.map_nil, List.traverse.eq_1]
  | cons head tail ih => simp only [List.map_cons, List.traverse, ih]

@[simp]
private lemma traverse_pure
    {F : Type _ → Type _} [Applicative F] [LawfulApplicative F]
    (xs : List A)
    : List.traverse (pure : _ → F _) xs = pure xs := by
  induction xs with
  | nil => simp [List.traverse.eq_1]
  | cons head tail ih => simp [List.traverse.eq_2, ih]

@[simp]
lemma decode_encode [Encodable A] (t : Rose A) : decode (encode t) = some t := by
  induction t with | mk label children ih =>
  simp only [encode]
  unfold decode
  simp only [
    Nat.unpair_pair, Encodable.decode₂_encode, Fin.getElem_fin,
    List.ofFn_getElem_eq_map, Option.pure_def, Option.bind_eq_bind,
    Option.bind_some]
  rw [Nat.unpair_pair, Encodable.encodek]
  simp only [List.map_map]
  rw [←List.ofFn_getElem_eq_map]
  simp only [
    Function.comp_apply, List.getElem_mem, ih,
    List.ofFn_getElem_eq_map, traverse_map, id_eq]
  change Option.bind (List.traverse pure children) _ = _
  simp only [traverse_pure]
  simp only [Option.pure_def, Option.bind_some]

instance [Encodable A] : Encodable (Rose A) where
  encode := encode
  decode := decode
  encodek := decode_encode

instance [Countable A] : Countable (Rose A) := by
  have := Encodable.ofCountable A
  infer_instance

@[simp]
lemma le_mk
    [LE A] (x y : A) (xs ys : List (Rose A))
    : mk x xs ≤ mk y ys ↔ x ≤ y ∧ List.Forall₂ (· ≤ ·) xs ys := by
  simp only [LE.le, fold.eq_1, List.forall₂_map_left_iff, id_eq]

instance [Preorder A] : Preorder (Rose A) where
  le_refl x := by
    induction x with | mk label children ih =>
    simp only [le_mk, le_refl, List.forall₂_same, true_and]
    exact ih
  le_trans t u v h₁ h₂ := by
    induction t generalizing u v with | mk _ xs ih =>
    cases u with | mk _ ys =>
    cases v with | mk _ zs =>
    simp only [le_mk] at ⊢ h₁ h₂
    apply And.intro
    · trans
      · apply h₁.1
      · apply h₂.1
    · induction xs generalizing ys zs with
      | nil =>
        simp_all only [
          List.not_mem_nil, IsEmpty.forall_iff, implies_true,
          List.forall₂_nil_left_iff, List.forall₂_same]
      | cons _ _ ih' =>
        cases ys with
        | nil => simp only [List.forall₂_nil_right_iff, reduceCtorEq, and_false] at h₁
        | cons _ _ =>
          cases zs with
          | nil => simp only [List.forall₂_nil_right_iff, reduceCtorEq, and_false] at h₂
          | cons _ _ =>
            simp only [List.forall₂_cons] at ⊢ h₁ h₂
            grind

instance [PartialOrder A] : PartialOrder (Rose A) where
  le_antisymm t u := by
    induction t generalizing u with | mk _ xs ih =>
    cases u with | mk _ ys =>
    simp only [le_mk, mk.injEq, and_imp]
    intro h₁ h₂ h₃ h₄
    apply And.intro
    · apply le_antisymm h₁ h₃
    · induction xs generalizing ys with
      | nil =>
        simp only [List.forall₂_nil_left_iff] at h₂
        simp only [h₂]
      | cons _ _ ih' =>
        cases ys with
        | nil => simp only [List.forall₂_nil_left_iff, reduceCtorEq] at h₄
        | cons _ _ =>
          simp only [List.forall₂_cons] at h₂ h₄
          grind

end Rose
