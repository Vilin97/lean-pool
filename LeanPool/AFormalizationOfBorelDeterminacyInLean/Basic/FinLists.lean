/-
Copyright (c) 2026 Sven Manthe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sven Manthe
-/

import LeanPool.AFormalizationOfBorelDeterminacyInLean.Basic.General

/-!
# LeanPool.AFormalizationOfBorelDeterminacyInLean.Basic.FinLists

Auxiliary declarations for the Borel determinacy formalization.
-/


variable {α β γ : Type*} {a : α} {m n : ℕ}

namespace List
variable (x y z : List α)

@[simp] lemma append_compose (x y : List α) : (x ++ ·) ∘ (y ++ ·) = ((x ++ y) ++ ·) := by
  ext1; simp [List.append_assoc]
@[simp] lemma subAtFin_append (T : Set (List α)) (x y : List α) :
  (y ++ ·)⁻¹' ((x ++ ·)⁻¹' T) = ((x ++ y) ++ ·)⁻¹' T := by
  simp [← Set.preimage_comp]

lemma eq_take_concat (x : List α) n (h : x.length = n + 1) :
  x = x.take n ++ [x[n]] := by
  rw [take_concat_get', ← h, take_length]
lemma head_eq_get (x : List α) h : x.head h = x[0]'(List.length_pos_iff.mpr h) :=
  (getElem_zero (List.length_pos_iff.mpr h)).symm
lemma tail_eq_drop : ∀ x : List α, x.tail = x.drop 1
  | [] => by simp
  | _ :: _ => by simp
lemma tail_take : (x.take (n + 1)).tail = x.tail.take n := by
  cases x <;> simp
lemma head_tail_take (x : List α) h : x.head h :: x.tail.take n = x.take (n + 1) := by
  cases x <;> simp at h ⊢
lemma tail_getElem (x : List α) n (h : n < x.tail.length) :
  x.tail[n] = x[n + 1]'(by as_aux_lemma => simp at h; omega) := by
  simp_rw [tail_eq_drop, getElem_drop, add_comm]
lemma zipWith_left : ∀ (x : List α) (z : List β), List.zipWith (fun a _ ↦ a) x z = x.take z.length
  | [], _ => by simp
  | _, [] => by simp
  | x :: xs, z :: zs => by simpa [zipWith_cons_cons] using zipWith_left xs zs
end List

namespace List
/-- Auxiliary declaration for the Borel determinacy formalization. -/
abbrev mapEval {α : Type*} {β : α → Type*} (a : α) (x : List (∀ a, β a)) := x.map (fun f ↦ f a)
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def zipFun {α : Type*} {β : α → Type*} {n : ℕ} (f : (a : α) → List (β a))
  (h : ∀ a, (f a).length = n) :
   List ((a : α) → β a) := match n with
  | 0 => []
  | n + 1 => (fun a ↦ (f a).head (ne_nil_of_length_eq_add_one (h a)))
    :: zipFun (fun a ↦ (f a).tail) ((by simp [h]) : ∀ a, length _ = n)
@[simp] lemma mapEval_zip {β : α → Type*} (f : (a : α) → List (β a)) (h : ∀ a, (f a).length = n) :
 (zipFun f h).mapEval a = f a := by
  induction n generalizing f with
  | zero =>
    specialize h a; simp at h; simp [zipFun, h]
  | succ n ih =>
    simp [zipFun, ih]
@[simp] lemma zip_mapEval {β : α → Type*} (x : List ((a : α) → β a)) :
  zipFun x.mapEval (n := x.length) (by simp) = x := by induction x <;> simp [zipFun, *]
lemma mapEval_joint_epi {β : α → Type*} {x y : List (∀ a, β a)} (hl : x.length = y.length)
  (h : ∀ a, x.mapEval a = y.mapEval a) : x = y := by
  rw [← zip_mapEval x, ← zip_mapEval y]; simp_rw [hl, h]
@[simp, simp_lengths] lemma zipFun_len {β : α → Type*} (f : (a : α) → List (β a))
  (h : ∀ a, (f a).length = n) : (zipFun f h).length (α := no_index _) = n := by
  induction n generalizing f with
  | zero => simp [zipFun]
  | succ n ih => simp [zipFun, ih]
@[simp] lemma zipFun_zero {β : α → Type*} (f : (a : α) → List (β a)) (h : ∀ a, (f a).length = 0) :
  zipFun f h = [] := by apply eq_nil_of_length_eq_zero; simp
@[simp] lemma zipFun_append {β : α → Type*} (f g : (a : α) → List (β a))
  (hf : ∀ a, (f a).length = m) (hg : ∀ a, (g a).length = n) :
  zipFun f hf ++ zipFun g hg = zipFun (n := m + n) (fun a ↦ f a ++ g a) (by simp [hf, hg]) := by
  induction m generalizing f with
  | zero =>
    simp [eq_nil_of_length_eq_zero (hf _)]
  | succ m ih =>
    have hf' a : f a ≠ [] := by intro h; simpa [h] using hf a
    simp [zipFun, Nat.succ_add, ih, hf']
@[gcongr] lemma zipFun_mono {β : α → Type*} (f g : (a : α) → List (β a))
  (hf : ∀ a, (f a).length = m) (hg : ∀ a, (g a).length = n) (hm : m ≤ n) (h : ∀ a, f a <+: g a) :
  zipFun f hf <+: zipFun g hg := by
  use zipFun (n := n - m) (fun a ↦ drop m (g a)) (by simp [hg]); rw [zipFun_append]
  congr
  · omega
  · ext a; nth_rw 2 [← take_append_drop m (g a)]
    rw [← hf a, ← prefix_iff_eq_take.mp (h a)]

variable (x y : List α) (a : α) (f : α → List α → β)
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def zipInitsMap := x.zipWith f x.inits.tail
@[simp] lemma zipInitsMap_nil : [].zipInitsMap f = [] := by simp [zipInitsMap]
@[simp] lemma zipInitsMap_singleton : [a].zipInitsMap f = [f a [a]] := rfl
lemma zipInitsMap_append : (x ++ y).zipInitsMap f
  = x.zipInitsMap f ++ y.zipInitsMap (fun a z ↦ f a (x ++ z)) := by
  have h : ¬ x.inits.isEmpty := by rw [List.isEmpty_iff_length_eq_zero]; simp
  simp [zipInitsMap, tail_append, h, zipWith_append, - map_tail, zipWith_map_right]
lemma IsPrefix.zipInitsMap (h : x <+: y) : x.zipInitsMap f <+: y.zipInitsMap f := by
  obtain ⟨_, rfl⟩ := h; rw [zipInitsMap_append]; constructor; rfl
@[simp] lemma zipInitsMap_concat :
  (x ++ [a]).zipInitsMap f = x.zipInitsMap f ++ [f a (x ++ [a])] := by
  simp [zipInitsMap_append]
@[simp, simp_lengths] lemma zipInitsMap_length :
  (x.zipInitsMap f).length (α := no_index _) = x.length := by simp [zipInitsMap]
lemma zipInitsMap_take : (x.zipInitsMap f).take n = (x.take n).zipInitsMap f := by
  simp [zipInitsMap, take_zipWith, take_inits, tail_take]
lemma map_zipInitsMap (f : α → β) (g : β → List β → γ) :
  x.zipInitsMap (fun a y ↦ g (f a) (y.map f)) = (x.map f).zipInitsMap g := by
  simp [zipInitsMap, map_inits, ← map_tail]
lemma zipInitsMap_map (g : β → γ) :
  x.zipInitsMap (fun a b ↦ g (f a b)) = (x.zipInitsMap f).map g := by
  simp [zipInitsMap, map_zipWith]
@[simp] lemma zipInitsMap_eq_map (g : α → β) :
  x.zipInitsMap (fun a _ ↦ g a) = x.map g := by
  simp [zipInitsMap, ← map_zipWith, zipWith_left]
@[simp] lemma zipInitsMap_get n (h : n < (x.zipInitsMap f).length) : (x.zipInitsMap f)[n]
  = f (x[n]'(by simpa using h)) (x.take (n + 1)) := by
  simp [zipInitsMap]

end List
