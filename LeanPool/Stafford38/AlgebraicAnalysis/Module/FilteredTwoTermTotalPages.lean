/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.AlgebraicAnalysis.Module.FilteredTwoTermPageEquivalences
public import LeanPool.Stafford38.AlgebraicAnalysis.Module.FilteredTwoTermPageActions
public import Mathlib.Algebra.DirectSum.Module


/-!
# Total direct sums of the filtered two-term pages

The page differential has target component indexed by `p + r`.  This file
packages the component maps into one direct-sum map; no successor-page
interface is assumed here.
-/

@[expose] public section

namespace AlgebraicAnalysis.FilteredTwoTermPages

universe u v

variable {k : Type u} [Ring k]
variable {M : Type v} [AddCommGroup M] [Module k M]

namespace FilteredTwoTerm

variable (K : FilteredTwoTerm k M)

/-- The direct sum of the source pages at page `r`. -/
abbrev SourceTotal (r : ℕ) :=
  DirectSum ℤ (fun p : ℤ => K.SourcePage r p)

/-- The direct sum of the target pages at page `r`. -/
abbrev TargetTotal (r : ℕ) :=
  DirectSum ℤ (fun p : ℤ => K.TargetPage r p)

/-- The total page differential, with the component at `p` landing at `p+r`.

The reindexing is expressed by the corresponding direct-sum inclusion, so the
formula keeps the target shift visible at the definition site.
-/
def totalDrop (r : ℕ) : K.SourceTotal r →ₗ[k] K.TargetTotal r :=
  DirectSum.toModule k ℤ (K.TargetTotal r) (fun p : ℤ =>
    (DirectSum.lof k ℤ (fun q : ℤ => K.TargetPage r q) (p + r)).comp
      (K.drop r p))

/-- Component formula for the total differential. -/
@[simp]
theorem totalDrop_lof (r : ℕ) (p : ℤ) (x : K.SourcePage r p) :
    K.totalDrop r (DirectSum.lof k ℤ (fun q : ℤ => K.SourcePage r q) p x) =
      DirectSum.lof k ℤ (fun q : ℤ => K.TargetPage r q) (p + r) (K.drop r p x) := by
  rw [totalDrop, DirectSum.toModule_lof]
  rfl

/-- Representative formula for a source-page quotient representative.

This compatibility lemma intentionally retains the quotient representative on
the right-hand side, although the simplifier can reduce it further. -/
theorem totalDrop_lof_mk (r : ℕ) (p : ℤ)
    (x : K.cycles r p) :
    K.totalDrop r
        (DirectSum.lof k ℤ (fun q : ℤ => K.SourcePage r q) p
          (Submodule.Quotient.mk x)) =
      DirectSum.lof k ℤ (fun q : ℤ => K.TargetPage r q) (p + r)
        (K.drop r p (Submodule.Quotient.mk x)) := by
  rw [K.totalDrop_lof, K.drop_mk]

private theorem totalDrop_apply_component (r : ℕ) (p : ℤ)
    (x : K.SourceTotal r) :
    K.totalDrop r x (p + r) = K.drop r p (x p) := by
  classical
  induction x using DirectSum.induction_on with
  | zero => simp
  | of q y =>
      rw [show DirectSum.of (fun q : ℤ => K.SourcePage r q) q y =
        DirectSum.lof k ℤ (fun q : ℤ => K.SourcePage r q) q y from rfl,
        K.totalDrop_lof]
      by_cases h : q = p
      · subst q
        simp
      · have hshift : q + (r : ℤ) ≠ p + (r : ℤ) := by omega
        change (DFinsupp.single (q + (r : ℤ)) (K.drop r q y)) (p + r) =
          K.drop r p ((DFinsupp.single q y) p)
        rw [DFinsupp.single_apply, DFinsupp.single_apply, dite_eq_right hshift, dite_eq_right h]
        simp
  | add x y hx hy => simpa using congrArg₂ (· + ·) hx hy


/-- The componentwise successor map on the total source page. -/
noncomputable def sourceTotalSuccMap (r : ℕ) :
    K.SourceTotal (r + 1) →ₗ[k] K.SourceTotal r :=
  DirectSum.lmap (fun p =>
    (LinearMap.ker (K.drop r p)).subtype.comp
      (K.sourceSuccEquivKerDrop r p).toLinearMap)

theorem totalSourceSuccMap_injective (r : ℕ) :
    Function.Injective (K.sourceTotalSuccMap r) := by
  apply (DirectSum.lmap_injective _).mpr
  intro p
  exact (Submodule.subtype_injective _).comp
    (K.sourceSuccEquivKerDrop r p).injective

theorem range_totalSourceSuccMap (r : ℕ) :
    (K.sourceTotalSuccMap r).range = (K.totalDrop r).ker := by
  rw [sourceTotalSuccMap, DirectSum.range_lmap]
  ext x
  change (∀ p ∈ Set.univ, x p ∈ LinearMap.range
    ((LinearMap.ker (K.drop r p)).subtype.comp
      (K.sourceSuccEquivKerDrop r p).toLinearMap)) ↔ K.totalDrop r x = 0
  constructor
  · intro hx
    apply DFinsupp.ext
    intro q
    have hq : q = (q - r) + r := by omega
    rw [hq, K.totalDrop_apply_component]
    obtain ⟨y, hy⟩ := hx (q - r) (Set.mem_univ _)
    have hmem := (K.sourceSuccEquivKerDrop r (q - r) y).property
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      Submodule.subtype_apply] using hy ▸ hmem
  · intro hx p _
    have hzero : K.drop r p (x p) = 0 := by
      rw [← K.totalDrop_apply_component, hx]
      rfl
    refine ⟨(K.sourceSuccEquivKerDrop r p).symm ⟨x p, hzero⟩, ?_⟩
    simp

/-- The total successor source is the actual kernel of the total differential. -/
noncomputable def sourceTotalSuccEquivKerDrop (r : ℕ) :
    K.SourceTotal (r + 1) ≃ₗ[k] (K.totalDrop r).ker :=
  LinearEquiv.ofInjective (K.sourceTotalSuccMap r)
      (K.totalSourceSuccMap_injective r) ≪≫ₗ
    LinearEquiv.ofEq _ _ (K.range_totalSourceSuccMap r)

private def targetReindex (r : ℕ) :
    K.TargetTotal r ≃ₗ[k] DirectSum ℤ (fun p => K.TargetPage r (p + r)) :=
  DirectSum.lequivCongrLeft k
    { toFun := fun p : ℤ => p - r
      invFun := fun p => p + r
      left_inv := by intro p; dsimp; omega
      right_inv := by intro p; dsimp; omega }

private theorem targetReindex_totalDrop (r : ℕ) (x : K.SourceTotal r) :
    K.targetReindex r (K.totalDrop r x) = DirectSum.lmap (K.drop r) x := by
  ext p
  exact K.totalDrop_apply_component r p x

/-- The componentwise quotient map on the total target page. -/
def targetTotalSuccMap (r : ℕ) :
    K.TargetTotal r →ₗ[k] K.TargetTotal (r + 1) :=
  DirectSum.lmap (K.targetSuccMap r)

theorem ker_totalTargetSuccMap (r : ℕ) :
    (K.targetTotalSuccMap r).ker = (K.totalDrop r).range := by
  ext y
  constructor
  · intro hy
    have hlocal : ∀ p, K.targetSuccMap r p (y p) = 0 := by
      intro p
      exact congrArg (fun z => z p) (LinearMap.mem_ker.mp hy)
    have hmem : K.targetReindex r y ∈ (DirectSum.lmap (K.drop r)).range := by
      rw [DirectSum.range_lmap]
      change ∀ p ∈ Set.univ, y (p + r) ∈ (K.drop r p).range
      intro p _
      rw [← K.ker_targetSuccMap_eq_range_drop]
      exact hlocal (p + r)
    obtain ⟨x, hx⟩ := hmem
    refine ⟨x, (K.targetReindex r).injective ?_⟩
    rw [K.targetReindex_totalDrop]
    exact hx
  · rintro ⟨x, rfl⟩
    apply LinearMap.mem_ker.mpr
    apply DFinsupp.ext
    intro q
    have hq : q = (q - r) + r := by omega
    change K.targetSuccMap r q (K.totalDrop r x q) = 0
    rw [hq, K.totalDrop_apply_component]
    apply LinearMap.mem_ker.mp
    rw [K.ker_targetSuccMap_eq_range_drop]
    exact ⟨x (q - r), rfl⟩

/-- The total successor target is the actual cokernel of the total differential. -/
noncomputable def targetTotalSuccEquivCokerDrop (r : ℕ) :
    K.TargetTotal (r + 1) ≃ₗ[k] (K.TargetTotal r ⧸ (K.totalDrop r).range) :=
  ((Submodule.quotEquivOfEq _ _ (K.ker_totalTargetSuccMap r).symm) ≪≫ₗ
    (K.targetTotalSuccMap r).quotKerEquivOfSurjective
      ((DirectSum.lmap_surjective _).mpr (K.targetSuccMap_surjective r))).symm


end FilteredTwoTerm

end AlgebraicAnalysis.FilteredTwoTermPages
