/-
Copyright (c) 2026 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Module.LinearMap.Defs
import LeanPool.VirasoroProject.ToMathlib.Topology.Algebra.BigOperators.FinProd

/-!
# LeanPool.VirasoroProject.ToMathlib.Topology.Algebra.Module.LinearMap.Defs
-/

section

-- NOTE: Should be in Mathlib! But Generalize to semilinear maps first...
lemma LinearMap.map_finsum {ι 𝕜 : Type*} [Semiring 𝕜]
    {V : Type*} [AddCommMonoid V] [Module 𝕜 V] {W : Type*} [AddCommMonoid W] [Module 𝕜 W]
    (f : V →ₗ[𝕜] W) (a : ι → V) (ha : (Function.support a).Finite) :
    f (∑ᶠ i, a i) = ∑ᶠ i, f (a i) := by
  rw [finsum_eq_sum _ ha, map_sum, ← finsum_eq_sum_of_support_subset (fun i ↦ f (a i))]
  intro i hi
  simp only [Function.mem_support, ne_eq, Set.Finite.coe_toFinset] at hi ⊢
  intro con
  simp [con] at hi

-- NOTE: Mathlib naming is inconsistent:

-- Should these just be `finsum_add` and `finsum_sub` and `finsum_neg`?
-- Compare with `tsum_add` and `tsum_sub` and `tsum_neg` (and `finsum_smul` and `smul_finsum`).

end
