/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Opus 5
-/
module

public import LeanPool.DavisKahan.DavisKahan.SpectralTheory.CircleRieszProjection
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Normed.Algebra.Spectrum

/-!
# The two endpoints of the circle Riesz projection

`circleRieszProjection A center radius` is the contour integral
`(2 π i)⁻¹ ∮_{|z - c| = r} (z - A)⁻¹ dz`.  This file evaluates it in the two
degenerate positions of the circle relative to the spectrum:

* `circleRieszProjection_eq_zero`: the closed disc misses the spectrum
  entirely, so the integrand is holomorphic there and Cauchy's theorem gives
  `0`;
* `circleRieszProjection_eq_one`: the open disc contains the whole spectrum,
  so the projection is the identity.

Neither statement needs self-adjointness, and neither goes through the
measurable functional calculus: they are Cauchy theory for the resolvent, and
they hold for any bounded operator.  That is what makes them usable as the two
endpoints of the Rosenblum contour argument for the Sylvester equation
(`DavisKahan.Sylvester.RosenblumExistence`), which has no self-adjointness to
appeal to.

The `= 1` endpoint is the one with content.  The integrand is deformed to a
large circle by the Cauchy--Goursat theorem for an annulus; there the
principal part `(z - c)⁻¹ • 1` integrates to `2 π i`, and the remainder
`(z - c)⁻¹ • (A - c) (z - A)⁻¹` is uniformly small because the resolvent
tends to `0` at infinity.  The deformation is what turns "small for large
circles" into "zero for the given circle": the remainder integral does not
depend on the radius.

## Ambient generality

Everything here is stated for a complex **Banach** space.  No proof below uses
an inner product: they run on `Ring.inverse`, `DiffContOnCl.circleIntegral_eq_zero`,
the annulus deformation, and `spectrum.resolvent_tendsto_cobounded`.
-/

@[expose] public section

open Metric Set Filter Complex
open scoped Topology Real

namespace TauCeti
namespace DavisKahan

universe u

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]

section Pencil

omit [CompleteSpace H] in
/-- Off the spectrum the resolvent pencil `z • 1 - A` is a unit.  This is
`spectrum.notMem_iff` in the `z • 1` normalisation that `circleRieszProjection`
uses. -/
theorem isUnit_smul_one_sub_of_notMem_spectrum {A : H →L[ℂ] H} {z : ℂ}
    (hz : z ∉ spectrum ℂ A) : IsUnit (z • (1 : H →L[ℂ] H) - A) := by
  have h := spectrum.notMem_iff.mp hz
  rwa [Algebra.algebraMap_eq_smul_one] at h

omit [CompleteSpace H] in
/-- The integrand of `circleRieszProjection` is Mathlib's `resolvent`. -/
theorem ringInverse_smul_one_sub_eq_resolvent (A : H →L[ℂ] H) (z : ℂ) :
    Ring.inverse (z • (1 : H →L[ℂ] H) - A) = resolvent A z := by
  rw [resolvent, Algebra.algebraMap_eq_smul_one]

/-- The resolvent is complex differentiable off the spectrum. -/
theorem differentiableAt_ringInverse_smul_one_sub (A : H →L[ℂ] H) {z : ℂ}
    (hz : z ∉ spectrum ℂ A) :
    DifferentiableAt ℂ
      (fun w : ℂ => Ring.inverse (w • (1 : H →L[ℂ] H) - A)) z := by
  have haff : DifferentiableAt ℂ (fun w : ℂ => w • (1 : H →L[ℂ] H) - A) z :=
    (differentiableAt_id.smul_const _).sub_const _
  exact (differentiableAt_inverse
    (isUnit_smul_one_sub_of_notMem_spectrum hz)).comp z haff

end Pencil

section Zero

/-- **The vanishing endpoint.**  A circle whose closed disc misses the spectrum
carries no Riesz projection: the resolvent is holomorphic on the disc, so
Cauchy's theorem applies. -/
theorem circleRieszProjection_eq_zero (A : H →L[ℂ] H) {center radius : ℝ}
    (hr : 0 < radius)
    (hspec : ∀ z : ℂ, z ∈ closedBall (center : ℂ) radius → z ∉ spectrum ℂ A) :
    circleRieszProjection A center radius = 0 := by
  have hdiff : DiffContOnCl ℂ
      (fun z : ℂ => Ring.inverse (z • (1 : H →L[ℂ] H) - A))
      (ball (center : ℂ) radius) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ hr.ne']
    intro z hz
    exact (differentiableAt_ringInverse_smul_one_sub A
      (hspec z hz)).differentiableWithinAt
  rw [circleRieszProjection, DiffContOnCl.circleIntegral_eq_zero hr.le hdiff,
    smul_zero]

end Zero

section One

variable (A : H →L[ℂ] H) {center radius : ℝ}

omit [CompleteSpace H] in
/-- The resolvent, split into its principal part at the centre and a remainder.
This is the algebraic heart of the `= 1` endpoint: the principal part carries
the whole `2 π i`, and the remainder is `O(|z - c|⁻¹)` times the resolvent, so
it dies at infinity. -/
theorem ringInverse_smul_one_sub_eq_principal_add_remainder
    {z : ℂ} (hz : z ∉ spectrum ℂ A) (hzc : z ≠ (center : ℂ)) :
    Ring.inverse (z • (1 : H →L[ℂ] H) - A) =
      (z - (center : ℂ))⁻¹ • (1 : H →L[ℂ] H) +
        (z - (center : ℂ))⁻¹ •
          ((A - (center : ℂ) • (1 : H →L[ℂ] H)) *
            Ring.inverse (z • (1 : H →L[ℂ] H) - A)) := by
  have hne : z - (center : ℂ) ≠ 0 := sub_ne_zero.mpr hzc
  set R := Ring.inverse (z • (1 : H →L[ℂ] H) - A) with hR
  have hcancel : (z • (1 : H →L[ℂ] H) - A) * R = 1 :=
    Ring.mul_inverse_cancel _ (isUnit_smul_one_sub_of_notMem_spectrum hz)
  -- `(z - c) • R = 1 + (A - c) * R`, then divide by `z - c`.
  have hkey : (z - (center : ℂ)) • R =
      1 + (A - (center : ℂ) • (1 : H →L[ℂ] H)) * R := by
    have hsplit : z • (1 : H →L[ℂ] H) - A =
        (z - (center : ℂ)) • (1 : H →L[ℂ] H) -
          (A - (center : ℂ) • (1 : H →L[ℂ] H)) := by
      rw [sub_smul]; abel
    rw [hsplit, sub_mul, smul_mul_assoc, one_mul] at hcancel
    exact sub_eq_iff_eq_add.mp hcancel
  rw [← smul_add, ← hkey, smul_smul, inv_mul_cancel₀ hne, one_smul]

omit [CompleteSpace H] in
/-- The remainder term is bounded by the resolvent, uniformly on a circle. -/
theorem norm_remainder_le {z : ℂ} (hz : z ∉ spectrum ℂ A) (hzc : z ≠ (center : ℂ)) :
    ‖Ring.inverse (z • (1 : H →L[ℂ] H) - A) -
        (z - (center : ℂ))⁻¹ • (1 : H →L[ℂ] H)‖ ≤
      ‖z - (center : ℂ)‖⁻¹ * ‖A - (center : ℂ) • (1 : H →L[ℂ] H)‖ *
        ‖Ring.inverse (z • (1 : H →L[ℂ] H) - A)‖ := by
  conv_lhs => rw [ringInverse_smul_one_sub_eq_principal_add_remainder A hz hzc]
  rw [add_sub_cancel_left, norm_smul, norm_inv, mul_assoc]
  exact mul_le_mul_of_nonneg_left (norm_mul_le _ _) (by positivity)

end One

section RemainderVanishes

/-- The resolvent with its principal part at the centre of the circle removed.
Its integral over the circle is what has to vanish for the `= 1` endpoint. -/
private noncomputable def rieszRemainder (A : H →L[ℂ] H) (center : ℝ) (z : ℂ) :
    H →L[ℂ] H :=
  Ring.inverse (z • (1 : H →L[ℂ] H) - A) - (z - (center : ℂ))⁻¹ • (1 : H →L[ℂ] H)

variable (A : H →L[ℂ] H) {center radius : ℝ}

private theorem differentiableAt_rieszRemainder (hr : 0 < radius)
    (hspec : spectrum ℂ A ⊆ ball ((center : ℂ)) radius)
    {z : ℂ} (hz : radius ≤ ‖z - (center : ℂ)‖) :
    DifferentiableAt ℂ (rieszRemainder A center) z := by
  have hzc : z - (center : ℂ) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hz
    linarith
  have hznot : z ∉ spectrum ℂ A := by
    intro hmem
    have hb := hspec hmem
    rw [mem_ball, dist_eq_norm] at hb
    linarith
  have h1 := differentiableAt_ringInverse_smul_one_sub A hznot
  have hinv : DifferentiableAt ℂ (fun w : ℂ => (w - (center : ℂ))⁻¹) z := by
    have hsub : DifferentiableAt ℂ (fun w : ℂ => w - (center : ℂ)) z := by fun_prop
    exact hsub.inv hzc
  have h2 : DifferentiableAt ℂ
      (fun w : ℂ => (w - (center : ℂ))⁻¹ • (1 : H →L[ℂ] H)) z :=
    hinv.smul_const (1 : H →L[ℂ] H)
  exact h1.sub h2

/-- The remainder integral does not depend on the radius, once the circle is
outside the spectrum: Cauchy--Goursat for an annulus.  This is what upgrades
"small for large circles" to "zero". -/
private theorem circleIntegral_rieszRemainder_eq (hr : 0 < radius) {R : ℝ}
    (hR : radius ≤ R) (hspec : spectrum ℂ A ⊆ ball ((center : ℂ)) radius) :
    (∮ z in C((center : ℂ), R), rieszRemainder A center z) =
      ∮ z in C((center : ℂ), radius), rieszRemainder A center z := by
  refine Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable hr hR
    Set.countable_empty ?_ ?_
  · intro z hz
    have hz' : radius ≤ ‖z - (center : ℂ)‖ := by
      have := hz.2
      rw [mem_ball, dist_eq_norm, not_lt] at this
      exact this
    exact (differentiableAt_rieszRemainder A hr hspec hz').continuousAt.continuousWithinAt
  · intro z hz
    have hz' : radius ≤ ‖z - (center : ℂ)‖ := by
      have := hz.1.2
      rw [mem_closedBall, dist_eq_norm, not_le] at this
      exact this.le
    exact differentiableAt_rieszRemainder A hr hspec hz'

private theorem circleIntegrable_rieszRemainder (hr : 0 < radius) {R : ℝ}
    (hR : radius ≤ R) (hspec : spectrum ℂ A ⊆ ball ((center : ℂ)) radius) :
    CircleIntegrable (rieszRemainder A center) (center : ℂ) R := by
  refine ContinuousOn.circleIntegrable (by linarith) fun z hz => ?_
  have hz' : radius ≤ ‖z - (center : ℂ)‖ := by
    rw [mem_sphere, dist_eq_norm] at hz
    rw [hz]
    exact hR
  exact (differentiableAt_rieszRemainder A hr hspec hz').continuousAt.continuousWithinAt

/-- The remainder integral is bounded by `2 π ‖A - c‖ ε` for every `ε > 0`,
because the resolvent tends to `0` at infinity and the remainder integral is
radius-independent. -/
private theorem norm_circleIntegral_rieszRemainder_le (hr : 0 < radius)
    (hspec : spectrum ℂ A ⊆ ball ((center : ℂ)) radius) {ε : ℝ} (hε : 0 < ε) :
    ‖∮ z in C((center : ℂ), radius), rieszRemainder A center z‖ ≤
      2 * Real.pi * ‖A - (center : ℂ) • (1 : H →L[ℂ] H)‖ * ε := by
  -- A radius beyond which the resolvent is uniformly smaller than `ε`.
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ b : ℝ, M ≤ b → ∀ z : ℂ, ‖z‖ = b →
      ‖resolvent A z‖ ≤ ε := by
    have hten : ∀ᶠ z : ℂ in Bornology.cobounded ℂ, ‖resolvent A z‖ ≤ ε := by
      have h := (spectrum.resolvent_tendsto_cobounded (𝕜 := ℂ) (a := A)).norm
      rw [norm_zero] at h
      exact h.eventually_le_const hε
    rw [← comap_norm_atTop, Filter.eventually_comap] at hten
    exact Filter.eventually_atTop.mp hten
  set A₀ : H →L[ℂ] H := A - (center : ℂ) • (1 : H →L[ℂ] H) with hA₀
  set R : ℝ := max radius (M + ‖(center : ℂ)‖) with hRdef
  have hrR : radius ≤ R := le_max_left _ _
  have hR0 : 0 < R := lt_of_lt_of_le hr hrR
  rw [← circleIntegral_rieszRemainder_eq A hr hrR hspec]
  have hbound : ∀ z ∈ sphere ((center : ℂ)) R,
      ‖rieszRemainder A center z‖ ≤ R⁻¹ * ‖A₀‖ * ε := by
    intro z hz
    rw [mem_sphere, dist_eq_norm] at hz
    have hzc : z ≠ (center : ℂ) := by
      intro h
      rw [h, sub_self, norm_zero] at hz
      exact absurd hz.symm hR0.ne'
    have hznot : z ∉ spectrum ℂ A := by
      intro hmem
      have hb := hspec hmem
      rw [mem_ball, dist_eq_norm] at hb
      rw [hz] at hb
      linarith [le_max_left radius (M + ‖(center : ℂ)‖)]
    have hres : ‖Ring.inverse (z • (1 : H →L[ℂ] H) - A)‖ ≤ ε := by
      rw [ringInverse_smul_one_sub_eq_resolvent]
      refine hM ‖z‖ ?_ z rfl
      have hge : R ≤ ‖z‖ + ‖(center : ℂ)‖ := by
        calc R = ‖z - (center : ℂ)‖ := hz.symm
          _ ≤ ‖z‖ + ‖(center : ℂ)‖ := norm_sub_le _ _
      have : M + ‖(center : ℂ)‖ ≤ R := le_max_right _ _
      linarith
    calc ‖rieszRemainder A center z‖
        ≤ ‖z - (center : ℂ)‖⁻¹ * ‖A₀‖ *
            ‖Ring.inverse (z • (1 : H →L[ℂ] H) - A)‖ :=
          norm_remainder_le A hznot hzc
      _ ≤ R⁻¹ * ‖A₀‖ * ε := by
          rw [hz]
          exact mul_le_mul_of_nonneg_left hres (by positivity)
  have hle := circleIntegral.norm_integral_le_of_norm_le_const hR0.le hbound
  calc ‖∮ z in C((center : ℂ), R), rieszRemainder A center z‖
      ≤ 2 * Real.pi * R * (R⁻¹ * ‖A₀‖ * ε) := hle
    _ = 2 * Real.pi * ‖A₀‖ * ε := by
        field_simp

/-- The remainder integral vanishes. -/
private theorem circleIntegral_rieszRemainder_eq_zero (hr : 0 < radius)
    (hspec : spectrum ℂ A ⊆ ball ((center : ℂ)) radius) :
    (∮ z in C((center : ℂ), radius), rieszRemainder A center z) = 0 := by
  set K : ℝ := 2 * Real.pi * ‖A - (center : ℂ) • (1 : H →L[ℂ] H)‖ with hK
  have hK0 : 0 ≤ K := by
    rw [hK]; positivity
  refine norm_le_zero_iff.mp (le_of_forall_pos_le_add fun ε hε => ?_)
  have h := norm_circleIntegral_rieszRemainder_le A hr hspec
    (ε := ε / (K + 1)) (by positivity)
  have hstep : K * (ε / (K + 1)) ≤ ε := by
    rw [mul_div_assoc', div_le_iff₀ (by linarith)]
    nlinarith
  linarith

end RemainderVanishes

section OneEndpoint

/-- **The identity endpoint.**  A circle whose open disc contains the whole
spectrum carries the identity: `(2 π i)⁻¹ ∮ (z - A)⁻¹ dz = 1`.

The proof splits the resolvent into its principal part `(z - c)⁻¹ • 1`, which
contributes the whole `2 π i`, and a remainder whose integral is
radius-independent by Cauchy--Goursat and arbitrarily small on large circles
because the resolvent vanishes at infinity. -/
theorem circleRieszProjection_eq_one (A : H →L[ℂ] H) {center radius : ℝ}
    (hr : 0 < radius) (hspec : spectrum ℂ A ⊆ ball ((center : ℂ)) radius) :
    circleRieszProjection A center radius = 1 := by
  have hprin : CircleIntegrable
      (fun z : ℂ => (z - (center : ℂ))⁻¹ • (1 : H →L[ℂ] H)) (center : ℂ) radius := by
    refine ContinuousOn.circleIntegrable hr.le fun z hz => ?_
    rw [mem_sphere, dist_eq_norm] at hz
    have hzc : z - (center : ℂ) ≠ 0 := by
      intro h
      rw [h, norm_zero] at hz
      exact hr.ne hz
    have hinv : DifferentiableAt ℂ (fun w : ℂ => (w - (center : ℂ))⁻¹) z := by
      have hsub : DifferentiableAt ℂ (fun w : ℂ => w - (center : ℂ)) z := by fun_prop
      exact hsub.inv hzc
    exact (hinv.smul_const (1 : H →L[ℂ] H)).continuousAt.continuousWithinAt
  have hrem := circleIntegrable_rieszRemainder A hr le_rfl hspec
  have hsplit : (fun z : ℂ => Ring.inverse (z • (1 : H →L[ℂ] H) - A)) =
      fun z : ℂ => rieszRemainder A center z +
        (z - (center : ℂ))⁻¹ • (1 : H →L[ℂ] H) := by
    funext z
    simp [rieszRemainder]
  have hprin_val : (∮ z in C((center : ℂ), radius),
      (z - (center : ℂ))⁻¹ • (1 : H →L[ℂ] H)) =
      (2 * Real.pi * Complex.I) • (1 : H →L[ℂ] H) := by
    rw [circleIntegral.integral_smul_const,
      circleIntegral.integral_sub_inv_of_mem_ball (mem_ball_self hr)]
  simp only [circleRieszProjection, hsplit, circleIntegral.integral_add hrem hprin,
    circleIntegral_rieszRemainder_eq_zero A hr hspec, zero_add, hprin_val,
    smul_smul, inv_mul_cancel₀ Complex.two_pi_I_ne_zero, one_smul]

end OneEndpoint

end DavisKahan
end TauCeti
