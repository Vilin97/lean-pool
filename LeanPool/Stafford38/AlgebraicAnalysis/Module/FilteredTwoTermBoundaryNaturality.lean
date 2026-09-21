/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.AlgebraicAnalysis.Module.FilteredTwoTermTotalActions
import LeanPool.Stafford38.AlgebraicAnalysis.Module.FilteredTwoTermBoundaryExhaustion

/-!
# Naturality of the target boundary maps

The quotient maps from page one to later target pages commute with every
filtered operator.
-/

namespace AlgebraicAnalysis.FilteredTwoTermPages

universe u v

variable {k : Type u} [Ring k]
variable {M : Type v} [AddCommGroup M] [Module k M]

namespace FilteredTwoTerm

variable (K : FilteredTwoTerm k M)

namespace PageOperator

variable {K} {d : ℤ} (P : K.PageOperator d)

theorem targetBoundaryMap_naturality (r : ℕ) (p : ℤ) :
    K.targetBoundaryMap r (p - d) ∘ₗ P.targetMap 1 p =
      P.targetMap (r + 1) p ∘ₗ K.targetBoundaryMap r p := by
  apply LinearMap.ext
  intro y
  refine Submodule.Quotient.induction_on
    ((K.boundaries 1 p).comap (K.G p).subtype) y ?_
  intro x
  simp only [LinearMap.comp_apply, P.targetMap_mk, K.targetBoundaryMap_mk]

theorem totalBoundaryMap_naturality (r : ℕ) :
    K.totalBoundaryMap r ∘ₗ P.targetTotalMap 1 =
      P.targetTotalMap (r + 1) ∘ₗ K.totalBoundaryMap r := by
  apply LinearMap.ext
  intro x
  induction x using DirectSum.induction_on with
  | zero => simp
  | of p y =>
      rw [show DirectSum.of (fun q : ℤ => K.TargetPage 1 q) p y =
        DirectSum.lof k ℤ (fun q : ℤ => K.TargetPage 1 q) p y from rfl]
      change K.totalBoundaryMap r (P.targetTotalMap 1
        (DirectSum.lof k ℤ (fun q : ℤ => K.TargetPage 1 q) p y)) =
        P.targetTotalMap (r + 1) (K.totalBoundaryMap r
          (DirectSum.lof k ℤ (fun q : ℤ => K.TargetPage 1 q) p y))
      rw [P.targetTotalMap_lof, K.totalBoundaryMap_lof,
        K.totalBoundaryMap_lof, P.targetTotalMap_lof]
      exact congrArg (fun z =>
        DirectSum.lof k ℤ (fun q : ℤ => K.TargetPage (r + 1) q) (p - d) z)
        (LinearMap.congr_fun (P.targetBoundaryMap_naturality r p) y)
  | add x y hx hy => simpa using congrArg₂ (· + ·) hx hy


end PageOperator

end FilteredTwoTerm

end AlgebraicAnalysis.FilteredTwoTermPages
