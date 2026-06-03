/-
Copyright (c) 2026 Jiazhen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiazhen Xia
-/

import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.Fintype.Lattice
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Topology.Homotopy.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Square
import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# LeanPool.WhiteheadTheorem.Auxiliary

Imported Lean Pool material for `LeanPool.WhiteheadTheorem.Auxiliary`.
-/


namespace CategoryTheory

-- #check CategoryTheory.eq_of_comp_right_eq
lemma eq_of_comp_right_iso_eq {C : Type*} [Category C] {X Y Z : C}
    (h : X ⟶ Y) [IsIso h] {f g : Y ⟶ Z} (e : h ≫ f = h ≫ g) : f = g := by
  have := congrArg (inv h ≫ ·) e
  simp only [IsIso.inv_hom_id_assoc] at this
  exact this
lemma eq_of_comp_left_iso_eq {C : Type*} [Category C] {X Y Z : C}
    (h : Y ⟶ Z) [IsIso h] {f g : X ⟶ Y} (e : f ≫ h = g ≫ h) : f = g := by
  have := congrArg (· ≫ inv h) e
  simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id] at this
  exact this

end CategoryTheory


namespace TopCat

open CategoryTheory

instance isIso_of_isEmpty {X Y : TopCat.{u}} [IsEmpty X] [IsEmpty Y] (f : X ⟶ Y) : IsIso f := by
  use ofHom ⟨isEmptyElim, by fun_prop⟩
  constructor
  all_goals ext x; exact isEmptyElim x

instance isEmpty_sigmaObj_of_isEmpty_dom
    {β : Type w} (f : β → TopCat.{u}) [Limits.HasCoproduct f] [IsEmpty β] : IsEmpty ↑(∐ f) :=
  have i : ∐ f ⟶ TopCat.of PEmpty.{u + 1} := Limits.Sigma.desc isEmptyElim
  ⟨fun z ↦ isEmptyElim (i z)⟩

end TopCat


namespace ContinuousMap

lemma eq_of_topCat_ofHom {A B : Type u} [TopologicalSpace A] [TopologicalSpace B]
    {f g : C(A, B)} (e : TopCat.ofHom f = TopCat.ofHom g) : f = g :=
  TopCat.hom_ext_iff.mp e

namespace Homotopic

lemma of_eq (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y]
    (f g : C(X, Y)) (hfg : f = g) : f.Homotopic g :=
  hfg ▸ ContinuousMap.Homotopic.refl f

end Homotopic

end ContinuousMap


/-!
Auxiliary lemmas used in `largeCubeHomeoPDisk` and `largeCubeBoundaryHomeoPDiskBoundary`
-/

lemma Real.forall_le_of_iSup_le_of_bddAbove {ι : Sort*} {f : ι → ℝ} {a : ℝ}
    (hbdd : BddAbove (Set.range f)) (hf : ⨆ i, f i ≤ a) : ∀ (i : ι), f i ≤ a := fun i ↦ by
  cases (Set.range f).eq_empty_or_nonempty
  · exact Set.range_eq_empty_iff.mp ‹_› |>.false i |>.elim
  · exact Real.isLUB_sSup ‹_› hbdd |>.left (Set.mem_range_self i) |>.trans hf

lemma Real.range_bddAbove_of_finite_domain {ι : Type*} (f : ι → ℝ) [Finite ι] :
    BddAbove (Set.range f) := by
  cases isEmpty_or_nonempty ι
  · exact ⟨0, fun y hy ↦ (IsEmpty.exists_iff.mp hy).elim⟩
  · obtain ⟨i, hi⟩ := Finite.exists_max f
    exact ⟨f i, fun y hy ↦ by
      obtain ⟨j, hj⟩ := Set.mem_range.mp hy
      rw [← hj]; exact hi j⟩

lemma Real.forall_le_of_iSup_le_of_finite_domain {ι : Type*} {f : ι → ℝ} {a : ℝ}
    [Finite ι] (hf : ⨆ i, f i ≤ a) : ∀ (i : ι), f i ≤ a :=
  forall_le_of_iSup_le_of_bddAbove (range_bddAbove_of_finite_domain f) hf

lemma Real.le_iSup_of_exists_ge_of_bddAbove {ι : Sort*} {f : ι → ℝ} {a : ℝ}
    (hbdd : BddAbove (Set.range f)) (hf : ∃ i, a ≤ f i) : a ≤ ⨆ i, f i := by
  obtain ⟨i, hi⟩ := hf
  cases (Set.range f).eq_empty_or_nonempty
  · exact Set.range_eq_empty_iff.mp ‹_› |>.false i |>.elim
  · exact hi.trans <| (Real.isLUB_sSup ‹_› hbdd).left (Set.mem_range_self i)

lemma Real.le_iSup_of_exists_ge_of_finite_domain {ι : Type*} {f : ι → ℝ} {a : ℝ}
    [Finite ι] (hf : ∃ i, a ≤ f i) : a ≤ ⨆ i, f i :=
  le_iSup_of_exists_ge_of_bddAbove (range_bddAbove_of_finite_domain f) hf

lemma Real.exists_eq_of_iSup_eq_of_finite_domain {ι : Type*} {f : ι → ℝ} {a : ℝ}
    [Finite ι] (hfz : ∃ i, f i ≥ 0) (hf : ⨆ i, f i = a) : ∃ i, f i = a := by
  have : Nonempty ι := hfz.nonempty
  have iSup_lt_iff : ⨆ i ∈ (Set.univ : Set ι), f i < a ↔ ∀ i ∈ Set.univ, f i < a := by
    apply Set.Finite.ciSup_lt_iff Set.finite_univ
    rw [Real.sSup_empty]   -- The supremum `sSup ∅` is defined to be 0 for `ℝ`
    simp only [Set.mem_univ, true_and]
    exact hfz
  have lt_iSup_iff : a < ⨆ i, f i ↔ ∃ i, a < f i :=
    lt_ciSup_iff (range_bddAbove_of_finite_domain f)
  by_contra nex; simp only [not_exists] at nex
  have : ∀ (i : ι), f i < a := fun i ↦ by
    obtain h | h | h := lt_trichotomy (f i) a
    · exact h
    · exfalso; exact nex i h
    · exfalso; exact ne_of_lt (lt_iSup_iff.mpr ⟨i, h⟩) hf.symm
  replace : ∀ i ∈ Set.univ, f i < a := fun i _ ↦ this i
  replace := iSup_lt_iff.mpr this
  rw [(by simp only [Set.mem_univ, ciSup_unique] : ⨆ i ∈ Set.univ, f i = ⨆ i, f i)] at this
  exact ne_of_lt this hf



-- /-- The result of embedding `i : Fin n` in `Fin (n+1)` is not equal to `n : Fin (n+1)` -/
-- lemma Fin.castSucc_ne_last {n : ℕ} (i : Fin n) : i.castSucc ≠ Fin.last n :=
--   fun heq ↦ Nat.ne_of_lt i.isLt (congrArg Fin.val heq)



namespace ContinuousMap

-- #check ContinuousMap.liftCover -- gluing lemma for an open cover

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]

variable {ι : Type*} [Finite ι] (S : ι → Set α) (φ : ∀ i : ι, C(S i, β))
variable
  (hφ : ∀ (i j) (x : α) (hxi : x ∈ S i) (hxj : x ∈ S j),
    φ i ⟨x, hxi⟩ = φ j ⟨x, hxj⟩)
  (hS_cover : ∀ x : α, ∃ i, x ∈ S i) (hS_closed : ∀ i, IsClosed (S i))

/-- `liftCoverClosed` -/
noncomputable def liftCoverClosed : C(α, β) :=
  have H : ⋃ i, S i = Set.univ := Set.iUnion_eq_univ_iff.2 hS_cover
  let Φ := Set.liftCover S (fun i ↦ φ i) hφ H
  ContinuousMap.mk Φ <| continuous_iff_isClosed.mpr fun Y hY ↦ by
    have : ∀ i, φ i ⁻¹' Y = S i ∩ Φ ⁻¹' Y := fun i ↦ by
      ext x
      simp only [Set.mem_image, Set.mem_preimage, Subtype.exists, exists_and_right, exists_eq_right,
        Set.mem_inter_iff]
      conv => lhs; rhs; ext hxi; arg 2; equals Φ x => exact Eq.symm (Set.liftCover_of_mem hxi)
      tauto
    have : Φ ⁻¹' Y = ⋃ i, Subtype.val '' (φ i ⁻¹' Y) := by
      conv_rhs => ext x; arg 1; ext i; rw [this]
      conv_rhs => ext x; rw [← Set.iUnion_inter, H, Set.univ_inter]
    rw [this]
    exact isClosed_iUnion_of_finite fun i ↦
      IsClosed.trans (IsClosed.preimage (φ i).continuous hY) (hS_closed i)

theorem liftCoverClosed_coe {i : ι} (x : S i) :
    liftCoverClosed S φ hφ hS_cover hS_closed x = φ i x := by
  rw [liftCoverClosed, ContinuousMap.coe_mk, Set.liftCover_coe _]

theorem liftCoverClosed_coe' {i : ι} (x : α) (hx : x ∈ S i) :
    liftCoverClosed S φ hφ hS_cover hS_closed x = φ i ⟨x, hx⟩ := by
  rw [← liftCoverClosed_coe]

end ContinuousMap




-- namespace CategoryTheory.IsPushout

-- variable {C : Type*} [Category C] {Z X Y P : C}
--   {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P}

-- lemma uniq (hP : IsPushout f g inl inr) {W : C} (h : X ⟶ W) (k : Y ⟶ W) (w : f ≫ h = g ≫ k)
--     (d : P ⟶ W) (hl : inl ≫ d = h) (hr : inr ≫ d = k) : d = hP.desc h k w :=
--   hP.isColimit.uniq (CommSq.mk w).cocone d fun j => match j with
--     | none => by simp; congr
--     | some Limits.WalkingPair.left => by simp; congr
--     | some Limits.WalkingPair.right => by simp; congr

-- end CategoryTheory.IsPushout
