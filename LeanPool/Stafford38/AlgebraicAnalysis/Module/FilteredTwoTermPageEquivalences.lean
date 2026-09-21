/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.AlgebraicAnalysis.Module.FilteredTwoTermPages
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Successor equivalences for the filtered two-term pages

This file proves, from the concrete representative definitions in
`FilteredTwoTermPages`, that the next source page is the kernel of the page
differential and that the next target page is its cokernel.
-/

namespace AlgebraicAnalysis.FilteredTwoTermPages

universe u v

variable {k : Type u} [Ring k]
variable {M : Type v} [AddCommGroup M] [Module k M]

namespace FilteredTwoTerm

variable (K : FilteredTwoTerm k M)

private abbrev sourceDenominator (r : ℕ) (p : ℤ) :
    Submodule k (K.cycles r p) :=
  (K.G (p + 1)).comap (K.cycles r p).subtype

private abbrev targetDenominator (r : ℕ) (p : ℤ) :
    Submodule k (K.G p) :=
  (K.boundaries r p).comap (K.G p).subtype

private def sourceSuccInclusion (r : ℕ) (p : ℤ) :
    K.cycles (r + 1) p →ₗ[k] K.cycles r p :=
  Submodule.inclusion (K.cycles_succ_le r p)

private theorem sourceSuccInclusion_denominator (r : ℕ) (p : ℤ) :
    K.sourceDenominator (r + 1) p ≤
      (K.sourceDenominator r p).comap (K.sourceSuccInclusion r p) := by
  intro x hx
  exact hx

/-- The map from the next source page to the current source page. -/
def sourceSuccMap (r : ℕ) (p : ℤ) :
    K.SourcePage (r + 1) p →ₗ[k] K.SourcePage r p :=
  Submodule.mapQ _ _ (K.sourceSuccInclusion r p)
    (K.sourceSuccInclusion_denominator r p)

@[simp]
theorem sourceSuccMap_mk (r : ℕ) (p : ℤ)
    (x : K.cycles (r + 1) p) :
    K.sourceSuccMap r p (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (K.sourceSuccInclusion r p x) :=
  Submodule.mapQ_apply _ _ _ _

private theorem drop_sourceSuccMap_eq_zero (r : ℕ) (p : ℤ)
    (x : K.SourcePage (r + 1) p) :
    K.drop r p (K.sourceSuccMap r p x) = 0 := by
  refine Submodule.Quotient.induction_on (K.sourceDenominator (r + 1) p) x ?_
  intro z
  rw [K.sourceSuccMap_mk]
  exact K.drop_mk_eq_zero_of_mem_cycles_succ r p
    (K.sourceSuccInclusion r p z) z.property

/-- The canonical map from the next source page into the kernel of `d_r`. -/
def sourceSuccKernelMap (r : ℕ) (p : ℤ) :
    K.SourcePage (r + 1) p →ₗ[k] LinearMap.ker (K.drop r p) :=
  (K.sourceSuccMap r p).codRestrict (LinearMap.ker (K.drop r p))
    (K.drop_sourceSuccMap_eq_zero r p)

private theorem sourceSuccMap_injective (r : ℕ) (p : ℤ) :
    Function.Injective (K.sourceSuccMap r p) := by
  intro a b
  revert b
  refine Submodule.Quotient.induction_on (K.sourceDenominator (r + 1) p) a ?_
  intro x b
  refine Submodule.Quotient.induction_on (K.sourceDenominator (r + 1) p) b ?_
  intro y hab
  rw [K.sourceSuccMap_mk, K.sourceSuccMap_mk] at hab
  apply (Submodule.Quotient.eq (K.sourceDenominator (r + 1) p)).2
  have hmem :=
    (Submodule.Quotient.eq (K.sourceDenominator r p)).1 hab
  exact hmem

private theorem sourceSuccKernelMap_surjective (r : ℕ) (p : ℤ) :
    Function.Surjective (K.sourceSuccKernelMap r p) := by
  rintro ⟨y, hy⟩
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective
    (K.sourceDenominator r p) y
  have hxzero : K.drop r p (Submodule.Quotient.mk x) = 0 := hy
  obtain ⟨z, hz, hxz⟩ :=
    K.exists_cycles_succ_rep_of_drop_mk_eq_zero r p x hxzero
  let w : K.cycles (r + 1) p := ⟨(x : M) - z, hxz⟩
  refine ⟨Submodule.Quotient.mk w, Subtype.ext ?_⟩
  rw [show ((K.sourceSuccKernelMap r p
      (Submodule.Quotient.mk w) : LinearMap.ker (K.drop r p)) :
        K.SourcePage r p) = K.sourceSuccMap r p (Submodule.Quotient.mk w) from rfl]
  rw [K.sourceSuccMap_mk]
  apply (Submodule.Quotient.eq (K.sourceDenominator r p)).2
  change ((w : M) - (x : M)) ∈ K.G (p + 1)
  simpa [w] using (K.G (p + 1)).neg_mem hz

/-- On the source, the next page is the kernel of the current page
differential. -/
noncomputable def sourceSuccEquivKerDrop (r : ℕ) (p : ℤ) :
    K.SourcePage (r + 1) p ≃ₗ[k] LinearMap.ker (K.drop r p) :=
  LinearEquiv.ofBijective (K.sourceSuccKernelMap r p)
    ⟨fun _ _ h => K.sourceSuccMap_injective r p (congrArg Subtype.val h),
      K.sourceSuccKernelMap_surjective r p⟩

/-- The quotient map from a target page to its successor page. -/
def targetSuccMap (r : ℕ) (p : ℤ) :
    K.TargetPage r p →ₗ[k] K.TargetPage (r + 1) p :=
  Submodule.mapQ _ _ LinearMap.id (by
    intro x hx
    exact K.boundaries_le_succ r p hx)

@[simp]
private theorem targetSuccMap_mk (r : ℕ) (p : ℤ)
    (x : K.G p) :
    K.targetSuccMap r p (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk x :=
  Submodule.mapQ_apply _ _ _ _

theorem targetSuccMap_surjective (r : ℕ) (p : ℤ) :
    Function.Surjective (K.targetSuccMap r p) := by
  intro y
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective
    (K.targetDenominator (r + 1) p) y
  exact ⟨Submodule.Quotient.mk x, K.targetSuccMap_mk r p x⟩

private theorem targetSuccMap_drop_eq_zero (r : ℕ) (p : ℤ)
    (x : K.SourcePage r p) :
    K.targetSuccMap r (p + r) (K.drop r p x) = 0 := by
  refine Submodule.Quotient.induction_on (K.sourceDenominator r p) x ?_
  intro z
  rw [K.drop_mk, K.targetSuccMap_mk, Submodule.Quotient.mk_eq_zero]
  change K.f (z : M) ∈ K.boundaries (r + 1) (p + r)
  apply Submodule.mem_sup.mpr
  refine ⟨K.f (z : M), ⟨z.property.2, ?_⟩,
    0, Submodule.zero_mem _, by simp⟩
  refine ⟨(z : M), ?_, rfl⟩
  have hind : p + (r : ℤ) - ((r + 1 : ℕ) : ℤ) + 1 = p := by
    push_cast
    omega
  rw [hind]
  exact z.property.1

private theorem range_drop_le_ker_targetSuccMap (r : ℕ) (p : ℤ) :
    LinearMap.range (K.drop r p) ≤
      LinearMap.ker (K.targetSuccMap r (p + r)) := by
  rintro _ ⟨x, rfl⟩
  exact LinearMap.mem_ker.mpr (K.targetSuccMap_drop_eq_zero r p x)

private theorem ker_targetSuccMap_le_range_drop (r : ℕ) (p : ℤ) :
    LinearMap.ker (K.targetSuccMap r (p + r)) ≤
      LinearMap.range (K.drop r p) := by
  intro y hy
  change K.targetSuccMap r (p + r) y = 0 at hy
  revert hy
  refine Submodule.Quotient.induction_on (K.targetDenominator r (p + r)) y ?_
  intro y hy
  rw [K.targetSuccMap_mk, Submodule.Quotient.mk_eq_zero] at hy
  change (y : M) ∈ K.boundaries (r + 1) (p + r) at hy
  obtain ⟨z, hz, e, he, hsum⟩ := K.mem_boundaries_succ_rep r (p + r) hy
  have hindex : p + (r : ℤ) - (r : ℤ) = p := by omega
  have hzp : z ∈ K.G p := by simpa [hindex] using hz
  have he' : e ∈ K.G (p + r) := K.next_le (p + r) he
  have hfz : K.f z ∈ K.G (p + r) := by
    have : K.f z = (y : M) - e := by rw [hsum]; simp
    rw [this]
    exact Submodule.sub_mem _ y.property he'
  let x : K.cycles r p := ⟨z, hzp, hfz⟩
  refine ⟨Submodule.Quotient.mk x, ?_⟩
  rw [K.drop_mk]
  apply (Submodule.Quotient.eq (K.targetDenominator r (p + r))).2
  change K.f z - (y : M) ∈ K.boundaries r (p + r)
  have hdifference : K.f z - (y : M) = -e := by
    rw [hsum]
    abel
  rw [hdifference]
  apply (K.boundaries r (p + r)).neg_mem
  exact Submodule.mem_sup.mpr
    ⟨0, Submodule.zero_mem _, e, he, by simp⟩

theorem ker_targetSuccMap_eq_range_drop (r : ℕ) (p : ℤ) :
    LinearMap.ker (K.targetSuccMap r (p + r)) =
      LinearMap.range (K.drop r p) :=
  le_antisymm (K.ker_targetSuccMap_le_range_drop r p)
    (K.range_drop_le_ker_targetSuccMap r p)

/-- The map from the cokernel of `d_r` to the next target page. -/
def targetCokernelMap (r : ℕ) (p : ℤ) :
    (K.TargetPage r (p + r) ⧸ LinearMap.range (K.drop r p)) →ₗ[k]
      K.TargetPage (r + 1) (p + r) :=
  (LinearMap.range (K.drop r p)).liftQ (K.targetSuccMap r (p + r))
    (K.range_drop_le_ker_targetSuccMap r p)

private theorem targetCokernelMap_injective (r : ℕ) (p : ℤ) :
    Function.Injective (K.targetCokernelMap r p) := by
  rw [← LinearMap.ker_eq_bot]
  exact Submodule.ker_liftQ_eq_bot _ _
    (K.range_drop_le_ker_targetSuccMap r p)
    (K.ker_targetSuccMap_eq_range_drop r p).le

private theorem targetCokernelMap_surjective (r : ℕ) (p : ℤ) :
    Function.Surjective (K.targetCokernelMap r p) := by
  intro y
  obtain ⟨x, rfl⟩ := K.targetSuccMap_surjective r (p + r) y
  exact ⟨Submodule.Quotient.mk x, Submodule.liftQ_apply _ _ _⟩

/-- On the target, the next page is the cokernel of the current page
differential. -/
noncomputable def targetSuccEquivCokerDrop (r : ℕ) (p : ℤ) :
    K.TargetPage (r + 1) (p + r) ≃ₗ[k]
      K.TargetPage r (p + r) ⧸ LinearMap.range (K.drop r p) :=
  (LinearEquiv.ofBijective (K.targetCokernelMap r p)
    ⟨K.targetCokernelMap_injective r p,
      K.targetCokernelMap_surjective r p⟩).symm


end FilteredTwoTerm

end AlgebraicAnalysis.FilteredTwoTermPages
