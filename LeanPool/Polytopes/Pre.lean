/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/

import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Data.Vector.Basic
import Mathlib.LinearAlgebra.Basis.Submodule

/-!
Preliminary lemmas and definitions used by the Polytopes formalization.
-/

open Pointwise Module

/-- Lifts a set whose elements satisfy `property` to the corresponding subtype. -/
lemma Set.Subtype {α : Type*} {property : α → Prop} (S : Set α) (hS : ∀ s ∈ S, property s) :
    ∃ S' : Set {x : α // property x}, Subtype.val '' S' = S ∧ Subtype.val ⁻¹' S = S' := by
  have : ∃ S' : Set {x : α // property x}, Subtype.val '' S' = S := CanLift.prf S hS
  rcases this with ⟨S', hS'⟩
  refine ⟨S', hS', ?_⟩
  ext x
  rw [Set.mem_preimage, ← hS', Set.mem_image]
  constructor
  · -- 1.
    rintro ⟨x', hx', hxx⟩
    rw [Subtype.coe_inj] at hxx
    exact hxx ▸ hx'
  · -- 2.
    intro hx
    exact ⟨x, hx, rfl⟩

lemma Set.Finite.translation {α : Type} [AddGroup α] {S : Set α} (hS : S.Finite) (x : α) :
  (S + ({x} : Set α)).Finite := by
  rw [Set.add_singleton]
  exact Set.Finite.image _ hS

lemma Set.mem_translation {α : Type} [AddGroup α] {S : Set α} (x s : α) :
  s ∈ S + ({x} : Set α) ↔ s - x ∈ S := by
  rw [Set.add_singleton, Set.mem_image]
  constructor
  · -- 1.
    rintro ⟨y, hy, rfl⟩
    rwa [add_sub_cancel_right]
  · -- 2.
    intro h
    exact ⟨s - x, h, by rw [sub_add_cancel]⟩

theorem Set.vsub_eq_sub {G : Type} [AddGroup G] (g1 g2 : Set G)
  : g1 -ᵥ g2 = g1 - g2 := rfl

lemma Set.sub_eq_neg_add {α : Type} [AddGroup α] (S : Set α) (x : α) :
  S - {x} = S + {(-x)} := by
  ext y
  simp only [sub_singleton, mem_image, add_singleton, image_add_right, neg_neg, mem_preimage]
  refine ⟨ ?_, fun h => ⟨y + x, h, by rw [add_sub_cancel_right]⟩ ⟩
  rintro ⟨z, hz, rfl⟩
  rwa [sub_add_cancel]

lemma Set.neg_add_cancel_right' {α : Type} [AddGroup α] {S : Set α} (x : α) :
  S - {x} + {x} = S := by
  ext y
  simp only [sub_singleton, add_singleton, mem_image, exists_exists_and_eq_and, sub_add_cancel,
    exists_eq_right]

lemma Set.Nonempty.sInter_inter_comm {α : Type u_1} {s : Set (Set α)} (hs : s.Nonempty)
    {t : Set α} : ⋂₀ ((· ∩ t) '' s) = (⋂₀ s) ∩ t := by
  ext x
  simp only [mem_sInter, mem_inter_iff]
  constructor
  · -- 1.
    intro h
    have : Nonempty.some hs ∩ t ∈ (fun x => x ∩ t) '' s := by
      rw [mem_image]
      exact ⟨Nonempty.some hs, hs.some_mem, rfl⟩
    refine ⟨ ?_, (h (hs.some ∩ t) this).2⟩
    intro y hy
    have : y ∩ t ∈ (fun x => x ∩ t) '' s := by
      rw [mem_image]
      exact ⟨y, hy, rfl⟩
    exact (h (y ∩ t) this).1
  · -- 2.
    rintro h y ⟨ z, hz, rfl ⟩
    exact mem_inter (h.1 z hz) h.2

lemma Set.Nonempty.image_sInter {α β : Type*} {S : Set (Set α)} (hS : S.Nonempty)
  {f : α → β} (hf : f.Injective) :
  f '' ⋂₀ S = ⋂ s ∈ S, f '' s := by
  refine subset_antisymm (image_sInter_subset S f) ?_
  intro y hy
  simp only [mem_iInter, mem_image] at hy ⊢
  rcases hy hS.some hS.some_mem with ⟨x, _hxInhSsome_, rfl⟩
  refine ⟨x, ?_, rfl⟩
  intro s hsInS
  rcases hy s hsInS with ⟨z, hzIns, hfzEqfx⟩
  convert hzIns
  exact hf hfzEqfx.symm

/-- The equivalence `P ≃ E` sending a point `p` to the vector `p -ᵥ x`. -/
def Equiv.VSubconst {E P : Type} [AddCommGroup E] [AddTorsor E P] (x : P) : P ≃ E where
  toFun := (· -ᵥ x)
  invFun := (· +ᵥ x)
  left_inv := fun y => by simp
  right_inv := fun y => by simp

lemma Equiv.coe_VSubconst {E P : Type} [AddCommGroup E] [AddTorsor E P]
    (x : P) : ↑(Equiv.VSubconst x) = (· -ᵥ x) := rfl

/-- The affine equivalence `P ≃ᵃ[𝕜] E` sending a point `p` to the vector `p -ᵥ x`. -/
def AffineEquiv.VSubconst (𝕜 : Type) {E P : Type} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [AddTorsor E P] (x : P) : P ≃ᵃ[𝕜] E where
  toEquiv := Equiv.VSubconst x
  linear := LinearEquiv.refl 𝕜 _
  map_vadd' p' v := by simp [(Equiv.coe_VSubconst), vadd_vsub_assoc]

lemma AffineEquiv.Vsubconst_toEquiv (𝕜 : Type) {E P : Type} [Field 𝕜] [AddCommGroup E]
    [Module 𝕜 E] [AddTorsor E P] (x : P) :
    (AffineEquiv.VSubconst 𝕜 x).toEquiv = Equiv.VSubconst x := rfl

lemma AffineEquiv.Vsubconst_linear_apply (𝕜 : Type) {E P : Type} [Field 𝕜] [AddCommGroup E]
    [Module 𝕜 E] [AddTorsor E P] (x : P) (v : E) : (AffineEquiv.VSubconst 𝕜 x).linear v = v := rfl

lemma AffineEquiv.coe_VSubconst (𝕜 : Type) {E P : Type} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [AddTorsor E P] (x : P) : ↑(AffineEquiv.VSubconst 𝕜 x) = (· -ᵥ x) := rfl

/-- The affine isometry equivalence `P ≃ᵃⁱ[𝕜] E` sending a point `p` to the vector `p -ᵥ x`. -/
def AffineIsometryEquiv.VSubconst (𝕜 : Type) {E P : Type} [NormedField 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [PseudoMetricSpace P] [NormedAddTorsor E P] (x : P) : P ≃ᵃⁱ[𝕜] E where
  toAffineEquiv := AffineEquiv.VSubconst 𝕜 x
  norm_map := by simp [AffineEquiv.Vsubconst_linear_apply]

@[simp]
lemma AffineIsometryEquiv.coe_VSubconst (𝕜 : Type) {E P : Type} [NormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [PseudoMetricSpace P] [NormedAddTorsor E P] (x : P) :
    ↑(AffineIsometryEquiv.VSubconst 𝕜 x) = (· -ᵥ x) := rfl


lemma Submodule.mem_orthogonal_Basis {𝕜 : Type u_1} {E : Type u_2} {ι : Type u_3} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (K : Submodule 𝕜 E) (b : Basis ι 𝕜 K) (v : E) :
  v ∈ Kᗮ ↔ ∀ i : ι, inner 𝕜 (↑(b i)) v = (0:𝕜) := by
  rw [Submodule.mem_orthogonal]
  constructor
  · intro h i
    exact h _ (Submodule.coe_mem (b i))
  · intro h x hx
    rw [Basis.mem_submodule_iff b] at hx
    rcases hx with ⟨ a, rfl ⟩
    rw [Finsupp.sum_inner]
    apply Finset.sum_eq_zero
    intro i _
    simp only [inner_smul_left, h i, mul_zero]

lemma AffineMap.preimage_convexHull {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [Ring 𝕜]
  [PartialOrder 𝕜] [AddCommGroup E] [AddCommGroup F] [Module 𝕜 E] [Module 𝕜 F] {s : Set F}
  {f : E →ᵃ[𝕜] F} (hf : f.toFun.Injective) (hs : s ⊆ Set.range f) :
  ↑f ⁻¹' (convexHull 𝕜) s = (convexHull 𝕜) (↑f ⁻¹' s) := by
  have h1 := Set.image_preimage_eq_of_subset hs
  ext x
  rw [Set.mem_preimage, ← Function.Injective.mem_set_image hf, AffineMap.toFun_eq_coe,
    AffineMap.image_convexHull, h1]

/-- The affine span of a nontrivial set is nontrivial. -/
lemma affineSpan_nontrivial (k : Type u_1) {V : Type u_2} {P : Type u_3} [Ring k] [AddCommGroup V]
    [Module k V] [AddTorsor V P] {s : Set P} (h : Nontrivial s) :
    Nontrivial (affineSpan k s) := by
  have := @CanLift.prf (Set P) (Set {x // x ∈ affineSpan k s}) _ _ _ s (subset_affineSpan k s)
  rcases this with ⟨ s', hs' ⟩
  rw [Set.nontrivial_coe_sort, ← hs'] at h
  exact Set.nontrivial_of_nontrivial <| Set.nontrivial_of_image _ _ h

/-- A nontrivial affine subspace has nontrivial direction. -/
lemma AffineSubspace.direction_nontrivial_of_nontrivial (k : Type u_1) {V : Type u_2} {P : Type u_3}
    [Ring k] [AddCommGroup V] [Module k V] [AddTorsor V P] (Q : AffineSubspace k P) :
    Nontrivial Q → Nontrivial Q.direction := by
  intro h
  rcases nontrivial_iff.mp h with ⟨ p, q, hpq ⟩
  have := AffineSubspace.toAddTorsor Q
  exact ⟨ 0, p -ᵥ q, Ne.symm <| vsub_ne_zero.mpr hpq ⟩

/-- If two sets are contained in an affine subspace, their difference lies in its direction. -/
lemma AffineSubspace.direction_subset_subset {k : Type u_1} {V : Type u_2} {P : Type u_3} [Ring k]
    [AddCommGroup V] [Module k V] [AddTorsor V P] {Q : AffineSubspace k P} {S T : Set P}
    (hS : S ⊆ Q) (hT : T ⊆ Q) : S -ᵥ T ⊆ Q.direction := by
  rintro x ⟨ a, b, haS, hbT, rfl ⟩
  exact AffineSubspace.vsub_mem_direction (hS b) (hT hbT)

/-- The row operation that normalizes a pivot row and clears the pivot column. -/
def Matrix.rowOpPivot {R : Type*} [Field R] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) R) (i : Fin m) (x : Fin n) (h : A i x ≠ 0) :
    Matrix (Fin m) (Fin n) R :=
  have _ : A i x ≠ 0 := h
  let v : Fin n → R := (A i x)⁻¹ • A i
  fun j => if j = i then v else (-A j x) • v + A j

/-- The list of all elements of `Fin n`, in increasing order. -/
def Nat.finListRange (n : ℕ) : List (Fin n) :=
  match n with
  | 0 => []
  | Nat.succ m => 0 :: (m.finListRange).map Fin.succ

lemma Fin.mem_fin_list_range {n : ℕ} (i : Fin n) : i ∈ n.finListRange := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    match i with
    | 0 => exact List.mem_cons_self
    | mk (Nat.succ m) h =>
      have : m < n := by omega
      let m' : Fin n := ⟨m, this⟩
      unfold Nat.finListRange
      apply List.mem_cons_of_mem
      simp only [List.mem_map]
      use m'
      use ih m'
      rfl

/-- Drops the first `m` entries from a length-indexed vector. -/
def Vector.Listdrop {R : Type*} {n : ℕ} (m : ℕ) : Vector R n → Vector R (n - m) :=
  fun v => v.drop m
