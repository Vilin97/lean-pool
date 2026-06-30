/-
Copyright (c) 2026 Vico Bonfioli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vico Bonfioli
-/

import LeanPool.ThreeGap.ModTwoGrowth
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The Euclidean growth inequality (instantiating the any-norm mod-2 theorem)

Instantiating `SimApprox.growth_additive_modTwo` at the **Euclidean (L²) norm** gives the growth
inequality for best simultaneous approximations in the Euclidean norm:

  `q_{n + 2^{d+1}} ≥ 2 q_{n+1} + q_n`.

For `d = 2` this is `q_{n+8} ≥ 2 q_{n+1} + q_n`, the denominator-growth input behind the Euclidean
five-distance theorem on `𝕋²`. The Euclidean norm on `Fin d → ℝ` is obtained by transporting the
`EuclideanSpace ℝ (Fin d)` norm along `EuclideanSpace.equiv`; its triangle inequality and
homogeneity come for free from that being a (continuous) linear equivalence.

Axiom-clean.
-/

namespace ThreeGap.SimApprox

variable {d : ℕ}

/-- The **Euclidean (L²) norm** on `Fin d → ℝ`, transported from `EuclideanSpace ℝ (Fin d)` along
`EuclideanSpace.equiv`. Concretely `euclNorm x = √(∑ i, (x i)²)`. -/
noncomputable def euclNorm (d : ℕ) (x : Fin d → ℝ) : ℝ :=
  ‖(EuclideanSpace.equiv (Fin d) ℝ).symm x‖

theorem euclNorm_nonneg (x : Fin d → ℝ) : 0 ≤ euclNorm d x := norm_nonneg _

theorem euclNorm_tri (x y : Fin d → ℝ) : euclNorm d (x + y) ≤ euclNorm d x + euclNorm d y := by
  unfold euclNorm
  rw [map_add]
  exact norm_add_le _ _

theorem euclNorm_smul (c : ℝ) (x : Fin d → ℝ) : euclNorm d (c • x) = |c| * euclNorm d x := by
  unfold euclNorm
  rw [map_smul, norm_smul, Real.norm_eq_abs]

/-- **The Euclidean growth inequality** (the mod-2 theorem at `N = euclNorm`). With the Euclidean
defect `δ = deltaN (euclNorm d) α` and the best-approximation record structure, the denominators
satisfy `2 q_{n+1} + q_n ≤ q_{n + 2^{d+1}}`. For `d = 2`: `q_{n+8} ≥ 2 q_{n+1} + q_n`. -/
theorem euclidean_growth_additive (α : Fin d → ℝ) (q : ℕ → ℤ) (p : ℕ → Fin d → ℤ)
    (hmono : StrictMono q)
    (hattain : ∀ k, euclNorm d (rem α (q k) (p k)) ≤ deltaN (euclNorm d) α (q k))
    (hdec : ∀ k, deltaN (euclNorm d) α (q (k + 1)) < deltaN (euclNorm d) α (q k))
    (hbest : ∀ (k : ℕ) (m : ℤ), 0 < m → m < q (k + 1) →
      deltaN (euclNorm d) α (q k) ≤ deltaN (euclNorm d) α m)
    (n : ℕ) : 2 * q (n + 1) + q n ≤ q (n + 2 ^ (d + 1)) :=
  growth_additive_modTwo (euclNorm d) euclNorm_tri euclNorm_smul α q p (deltaN (euclNorm d) α) hmono
    (fun m P => deltaN_le (euclNorm d) euclNorm_nonneg α m P) hattain hdec hbest n

end ThreeGap.SimApprox
