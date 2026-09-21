/-
Copyright (c) 2026 Yoshito Ishiki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoshito Ishiki
-/
import Mathlib.Analysis.Normed.Lp.lpSpace
import LeanPool.ScottishBook155.Paper1

/-!
# An unrestricted Kuratowski injectivity coordinate

The paper uses the bounded distance-difference function on the metric quotient.
Here the same functions are represented in `ℓ∞(P, ℝ)`, indexed by every point
of `P`.  Unlike Mathlib's countable Kuratowski embedding, this construction
does not require separability.
-/

namespace ScottishBook155

open ENNReal lp

universe u

/-- The distance-difference Kuratowski coordinate based at `base`. -/
noncomputable def fullKuratowski {P : Type u} [MetricSpace P] (base z : P) :
    ℓ^∞(P, ℝ) :=
  ⟨fun u => dist z u - dist base u, by
    apply memℓp_infty
    use dist z base
    rintro - ⟨u, rfl⟩
    exact abs_dist_sub_le z base u⟩

theorem fullKuratowski_apply {P : Type u} [MetricSpace P] (base z u : P) :
    fullKuratowski base z u = dist z u - dist base u := rfl

theorem fullKuratowski_base {P : Type u} [MetricSpace P] (base : P) :
    fullKuratowski base base = 0 := by
  ext u
  simp [fullKuratowski_apply]

theorem fullKuratowski_dist_le {P : Type u} [MetricSpace P] (base z w : P) :
    dist (fullKuratowski base z) (fullKuratowski base w) ≤ dist z w := by
  rw [dist_eq_norm]
  refine lp.norm_le_of_forall_le dist_nonneg fun u => ?_
  simp only [lp.coeFn_sub, Pi.sub_apply, fullKuratowski_apply]
  convert! abs_dist_sub_le z w u using 2
  ring

/-- The unrestricted distance-difference coordinate is an isometry. -/
theorem fullKuratowski_isometry {P : Type u} [MetricSpace P] (base : P) :
    Isometry (fullKuratowski base) := by
  refine Isometry.of_dist_eq fun z w => (fullKuratowski_dist_le base z w).antisymm ?_
  rw [dist_eq_norm]
  have heval := lp.norm_apply_le_norm ENNReal.top_ne_zero
    (fullKuratowski base z - fullKuratowski base w) z
  simp only [lp.coeFn_sub, Pi.sub_apply, fullKuratowski_apply, dist_self,
    zero_sub, Real.norm_eq_abs] at heval
  calc
    dist z w = |-dist base z - (dist w z - dist base z)| := by
      rw [dist_comm w z, abs_of_nonpos]
      · ring
      · have hd : 0 ≤ dist z w := dist_nonneg
        linarith
    _ ≤ ‖fullKuratowski base z - fullKuratowski base w‖ := heval

theorem fullKuratowski_injective {P : Type u} [MetricSpace P] (base : P) :
    Function.Injective (fullKuratowski base) :=
  (fullKuratowski_isometry base).injective

end ScottishBook155
