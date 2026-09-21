/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

public import LeanPool.PoincareGeometry.LichnerowiczObata.RoundAmbientDirections
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-! # Smooth Cartesian graphs at the two round poles -/

@[expose] public noncomputable section
open scoped ContDiff
namespace LichnerowiczObata
variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]

/-- With sign `1` or `-1`, this is the graph of the corresponding round
hemisphere over its equatorial tangent plane. -/
def roundPoleGraph (ε R : ℝ) (z : P) : RoundAmbient P :=
  roundAngularInclusion z + (ε * Real.sqrt (R ^ 2 - ‖z‖ ^ 2)) • roundNorth

theorem roundPoleGraph_zero (ε : ℝ) {R : ℝ} (hR : 0 ≤ R) :
    roundPoleGraph (P := P) ε R 0 = (ε * R) • roundNorth := by
  simp [roundPoleGraph, Real.sqrt_sq hR]

/-- Cartesian projection is an exact left inverse, including at the pole. -/
theorem roundPoleGraph_project (ε R : ℝ) (z : P) :
    (WithLp.fstL 2 ℝ P ℝ) (roundPoleGraph ε R z) = z := by
  simp [roundPoleGraph, roundAngularInclusion_apply, roundNorth]

theorem roundPoleGraph_height (ε R : ℝ) (z : P) :
    inner ℝ roundNorth (roundPoleGraph ε R z) = ε * Real.sqrt (R ^ 2 - ‖z‖ ^ 2) := by
  rw [roundPoleGraph, inner_add_right, roundNorth_inner_angular, real_inner_smul_right,
    real_inner_self_eq_norm_sq, roundNorth_norm]
  ring

/-- Every point in the specified closed hemisphere is reconstructed
from its Cartesian projection, so the graph describes the actual sphere. -/
theorem roundPoleGraph_reconstruct {ε R : ℝ} (hε : ε ^ 2 = 1)
    (x : RoundAmbient P) (hx : ‖x‖ = R)
    (hsign : 0 ≤ ε * inner ℝ roundNorth x) :
    roundPoleGraph ε R ((WithLp.ofLp x).1) = x := by
  have hn := WithLp.prod_norm_sq_eq_of_L2 x
  rw [hx] at hn
  change R ^ 2 = ‖(WithLp.ofLp x).1‖ ^ 2 + ‖(WithLp.ofLp x).2‖ ^ 2 at hn
  rw [Real.norm_eq_abs, sq_abs] at hn
  have he : R ^ 2 - ‖(WithLp.ofLp x).1‖ ^ 2 = (WithLp.ofLp x).2 ^ 2 := by linarith
  apply (WithLp.equiv 2 (P × ℝ)).injective
  apply Prod.ext
  · exact roundPoleGraph_project ε R (WithLp.ofLp x).1
  · change (WithLp.ofLp (roundPoleGraph ε R (WithLp.ofLp x).1)).2 = (WithLp.ofLp x).2
    rw [← roundNorth_inner, roundPoleGraph_height, he, Real.sqrt_sq_eq_abs]
    rw [roundNorth_inner] at hsign
    rcases sq_eq_one_iff.mp hε with rfl | rfl
    · simpa only [one_mul] using abs_of_nonneg (by simpa using hsign)
    · have hneg : (WithLp.ofLp x).2 ≤ 0 := by linarith
      rw [abs_of_nonpos hneg]
      ring

theorem roundPoleGraph_mem_sphere {ε R : ℝ} (hε : ε ^ 2 = 1) (hR : 0 ≤ R)
    (z : P) (hz : ‖z‖ ≤ R) : roundPoleGraph ε R z ∈ Metric.sphere (0 : RoundAmbient P) R := by
  have hsq : 0 ≤ R ^ 2 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have ho : inner ℝ (roundAngularInclusion z)
      ((ε * Real.sqrt (R ^ 2 - ‖z‖ ^ 2)) • (roundNorth : RoundAmbient P)) = 0 := by
    rw [real_inner_smul_right, real_inner_comm, roundNorth_inner_angular, mul_zero]
  rw [mem_sphere_zero_iff_norm]
  apply (sq_eq_sq₀ (norm_nonneg _) hR).mp
  rw [roundPoleGraph, norm_add_sq_real, ho, roundAngularInclusion_norm, norm_smul,
    roundNorth_norm, mul_one, Real.norm_eq_abs, sq_abs, mul_pow, hε, one_mul, Real.sq_sqrt hsq]
  ring

/-- The graph is smooth on the open equatorial ball, in particular at
the pole itself; no inverse angular coordinate appears. -/
theorem contDiffAt_roundPoleGraph (ε : ℝ) {R : ℝ} (hR : 0 < R)
    (z : P) (hz : ‖z‖ < R) : ContDiffAt ℝ ∞ (roundPoleGraph ε R) z := by
  have hsq : R ^ 2 - ‖z‖ ^ 2 ≠ 0 := by nlinarith [norm_nonneg z]
  have hs : ContDiffAt ℝ ∞ (fun z : P => Real.sqrt (R ^ 2 - ‖z‖ ^ 2)) z :=
    (contDiffAt_const.sub (contDiff_norm_sq ℝ).contDiffAt).sqrt hsq
  exact roundAngularInclusion.contDiff.contDiffAt.add
    ((contDiffAt_const.mul hs).smul contDiffAt_const)

/-- At either pole the graph derivative is the angular linear inclusion,
with no singular radial factor. -/
theorem hasFDerivAt_roundPoleGraph_zero (ε : ℝ) {R : ℝ} (hR : 0 < R) :
    HasFDerivAt (roundPoleGraph (P := P) ε R) roundAngularInclusion 0 := by
  have hn : HasFDerivAt (fun z : P => ‖z‖ ^ 2) (0 : P →L[ℝ] ℝ) 0 := by
    simpa using (hasStrictFDerivAt_norm_sq (0 : P)).hasFDerivAt
  have hs : HasFDerivAt (fun z : P => Real.sqrt (R ^ 2 - ‖z‖ ^ 2))
      (0 : P →L[ℝ] ℝ) 0 := by
    simpa using ((hasFDerivAt_const (R ^ 2) (0 : P)).sub hn).sqrt
      (by simpa using pow_ne_zero 2 hR.ne')
  convert roundAngularInclusion.hasFDerivAt.add
    (((hasFDerivAt_const ε (0 : P)).mul hs).smul_const (roundNorth : RoundAmbient P)) using 1
  all_goals first | rfl | simp

theorem roundPoleGraph_derivative_inner (ε : ℝ) {R : ℝ} (hR : 0 < R) (v w : P) :
    inner ℝ (fderiv ℝ (roundPoleGraph ε R) 0 v)
      (fderiv ℝ (roundPoleGraph ε R) 0 w) = inner ℝ v w := by
  rw [(hasFDerivAt_roundPoleGraph_zero ε hR).fderiv, roundAngularInclusion_inner]

end LichnerowiczObata
