/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.AlgebraicAnalysis.Module.FilteredTwoTermTotalActions

/-!
# Naturality of the total successor maps

The concrete successor maps on the source and target pages commute with the
page action.  The proof is by direct-sum induction and quotient
representatives; no abstract successor-page interface is used.
-/

namespace AlgebraicAnalysis.FilteredTwoTermPages

universe u v

variable {k : Type u} [Ring k]
variable {M : Type v} [AddCommGroup M] [Module k M]

namespace FilteredTwoTerm

namespace PageOperator

variable {K : FilteredTwoTerm k M} {d : ℤ} (P : K.PageOperator d)

theorem sourceTotalSuccMap_naturality (r : ℕ) :
    K.sourceTotalSuccMap r ∘ₗ P.sourceTotalMap (r + 1) =
      P.sourceTotalMap r ∘ₗ K.sourceTotalSuccMap r := by
  apply LinearMap.ext
  intro x
  induction x using DirectSum.induction_on with
  | zero => simp
  | of p x =>
      rw [show DirectSum.of (fun q : ℤ => K.SourcePage (r + 1) q) p x =
        DirectSum.lof k ℤ (fun q : ℤ => K.SourcePage (r + 1) q) p x from rfl]
      rw [LinearMap.comp_apply, LinearMap.comp_apply]
      simp only [sourceTotalSuccMap, DirectSum.lmap_lof]
      rw [P.sourceTotalMap_lof]
      change K.sourceTotalSuccMap r
          (DirectSum.lof k ℤ (fun q : ℤ => K.SourcePage (r + 1) q) (p - d)
            (P.sourceMap (r + 1) p x)) =
        P.sourceTotalMap r
          (DirectSum.lof k ℤ (fun q : ℤ => K.SourcePage r q) p
            (K.sourceSuccMap r p x))
      rw [sourceTotalSuccMap, DirectSum.lmap_lof]
      rw [P.sourceTotalMap_lof]
      apply congrArg (fun z =>
        DirectSum.lof k ℤ (fun q : ℤ => K.SourcePage r q) (p - d) z)
      refine Submodule.Quotient.induction_on
        ((K.G (p + 1)).comap (K.cycles (r + 1) p).subtype) x ?_
      intro z
      rw [K.sourceSuccMap_mk, P.sourceMap_mk]
      simp? [sourceSuccEquivKerDrop, sourceSuccKernelMap, sourceSuccMap]
      apply (Submodule.Quotient.eq _).2
      change P.g (z : M) - P.g (z : M) ∈ K.G (p - d + 1)
      simp
  | add x y hx hy => simpa using congrArg₂ (· + ·) hx hy

theorem targetTotalSuccMap_naturality (r : ℕ) :
    K.targetTotalSuccMap r ∘ₗ P.targetTotalMap r =
      P.targetTotalMap (r + 1) ∘ₗ K.targetTotalSuccMap r := by
  apply LinearMap.ext
  intro x
  induction x using DirectSum.induction_on with
  | zero => simp
  | of p x =>
      rw [show DirectSum.of (fun q : ℤ => K.TargetPage r q) p x =
        DirectSum.lof k ℤ (fun q : ℤ => K.TargetPage r q) p x from rfl]
      rw [LinearMap.comp_apply, LinearMap.comp_apply]
      simp only [targetTotalSuccMap, DirectSum.lmap_lof]
      rw [P.targetTotalMap_lof]
      change K.targetTotalSuccMap r
          (DirectSum.lof k ℤ (fun q : ℤ => K.TargetPage r q) (p - d)
            (P.targetMap r p x)) =
        P.targetTotalMap (r + 1)
          (DirectSum.lof k ℤ (fun q : ℤ => K.TargetPage (r + 1) q) p
            (K.targetSuccMap r p x))
      rw [targetTotalSuccMap, DirectSum.lmap_lof]
      rw [P.targetTotalMap_lof]
      apply congrArg (fun z =>
        DirectSum.lof k ℤ (fun q : ℤ => K.TargetPage (r + 1) q) (p - d) z)
      refine Submodule.Quotient.induction_on
        ((K.boundaries r p).comap (K.G p).subtype) x ?_
      intro z
      rw [P.targetMap_mk]
      change K.targetSuccMap r (p - d)
          (Submodule.Quotient.mk (P.targetRestricted p z)) =
        Submodule.Quotient.mk (P.targetRestricted p z)
      rw [targetSuccMap, Submodule.mapQ_apply]
      rfl
  | add x y hx hy => simpa using congrArg₂ (· + ·) hx hy

end PageOperator

end FilteredTwoTerm

end AlgebraicAnalysis.FilteredTwoTermPages
