/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.AxisymmetricResidual
import LeanPool.NavierStokesAndEuler.NavierStokes.LocalAxisymmetricResidual
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Radial flux coordinates for the actual axisymmetric residual

Write `s = r²/2` and `V = r u_r`.  The convention in
`AxisymmetricResidual` is `u_r = -r B`, hence `B = -V/(2s)`.
All quotient derivatives in this file are genuine Fréchet derivatives,
and their hypotheses are local at a point with positive `s`.
-/

@[expose] public section


namespace NavierStokes.RadialFluxResidual

noncomputable section

open ProblemStatement AxisymmetricFields AxisymmetricResidual Filter
open scoped BigOperators ContDiff Topology

/-- Radial B, defined pointwise by `-V p / (2 * p.2.1)`. -/
noncomputable def radialB (V : Profile) : Profile :=
  fun p => -V p / (2 * p.2.1)

private noncomputable def sProjection : ProfilePoint →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).comp
    (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))

@[simp] private theorem sProjection_apply (p : ProfilePoint) : sProjection p = p.2.1 := rfl

theorem contDiffAt_radialB {V : Profile} {p : ProfilePoint} {n : WithTop ℕ∞}
    (hV : ContDiffAt ℝ n V p) (hs : p.2.1 ≠ 0) :
    ContDiffAt ℝ n (radialB V) p :=
  hV.neg.div (contDiffAt_const.mul sProjection.contDiff.contDiffAt)
    (mul_ne_zero (by norm_num) hs)

theorem fderiv_radialB_apply {V : Profile} {p : ProfilePoint}
    (hV : DifferentiableAt ℝ V p) (hs : p.2.1 ≠ 0) (v : ProfilePoint) :
    fderiv ℝ (radialB V) p v =
      -fderiv ℝ V p v / (2 * p.2.1) + V p * v.2.1 / (2 * p.2.1 ^ 2) := by
  have hi := (hasDerivAt_inv hs).comp_hasFDerivAt p sProjection.hasFDerivAt
  simp only [Function.comp_def] at hi
  have hb := (hV.hasFDerivAt.fun_mul hi).const_mul (-(1 / 2 : ℝ))
  have he : radialB V = (fun q => -(1 / 2 : ℝ) * (V q * (sProjection q)⁻¹)) := by
    funext q
    simp only [radialB, sProjection_apply, div_eq_mul_inv, mul_inv_rev]
    ring
  rw [he, hb.fderiv]
  simp only [_root_.smul_apply, _root_.add_apply, sProjection_apply, smul_eq_mul]
  field_simp [hs]; ring

theorem differentiableAt_radialB {V : Profile} {p : ProfilePoint}
    (hV : DifferentiableAt ℝ V p) (hs : p.2.1 ≠ 0) :
    DifferentiableAt ℝ (radialB V) p := by
  have hi := (hasDerivAt_inv hs).comp_hasFDerivAt p sProjection.hasFDerivAt
  simp only [Function.comp_def] at hi
  have hb := (hV.hasFDerivAt.fun_mul hi).const_mul (-(1 / 2 : ℝ))
  convert! hb.differentiableAt using 1
  funext q
  simp only [radialB, sProjection_apply, div_eq_mul_inv, mul_inv_rev]
  ring

theorem partialT_radialB {V : Profile} {p : ProfilePoint}
    (hV : DifferentiableAt ℝ V p) (hs : p.2.1 ≠ 0) :
    partialT (radialB V) p = radialB (partialT V) p := by
  rw [partialT, fderiv_radialB_apply hV hs]
  simp [radialB, partialT]

theorem partialZ_radialB {V : Profile} {p : ProfilePoint}
    (hV : DifferentiableAt ℝ V p) (hs : p.2.1 ≠ 0) :
    partialZ (radialB V) p = radialB (partialZ V) p := by
  rw [partialZ, fderiv_radialB_apply hV hs]
  simp [radialB, partialZ]

theorem partialS_radialB_explicit {V : Profile} {p : ProfilePoint}
    (hV : DifferentiableAt ℝ V p) (hs : p.2.1 ≠ 0) :
    partialS (radialB V) p =
      -partialS V p / (2 * p.2.1) + V p / (2 * p.2.1 ^ 2) := by
  rw [partialS, fderiv_radialB_apply hV hs]
  simp [partialS]

theorem partialS_radialB {V : Profile} {p : ProfilePoint}
    (hV : DifferentiableAt ℝ V p) (hs : p.2.1 ≠ 0) :
    partialS (radialB V) p =
      radialB (partialS V) p + 2 * radialB (radialB V) p := by
  rw [partialS_radialB_explicit hV hs]
  unfold radialB
  field_simp [hs]

private theorem differentiableAt_partialS {V : Profile} {p : ProfilePoint}
    (hV : ContDiffAt ℝ 2 V p) : DifferentiableAt ℝ (partialS V) p :=
  (((hV.fderiv_right (m := 1) (by norm_num)).clm_apply
    contDiffAt_const).differentiableAt (by norm_num))

private theorem differentiableAt_partialZ {V : Profile} {p : ProfilePoint}
    (hV : ContDiffAt ℝ 2 V p) : DifferentiableAt ℝ (partialZ V) p :=
  (((hV.fderiv_right (m := 1) (by norm_num)).clm_apply
    contDiffAt_const).differentiableAt (by norm_num))

theorem partialS_partialS_radialB {V : Profile} {p : ProfilePoint}
    (hV : ContDiffAt ℝ 2 V p) (hs : p.2.1 ≠ 0) :
    partialS (partialS (radialB V)) p =
      -partialS (partialS V) p / (2 * p.2.1) +
        partialS V p / p.2.1 ^ 2 - V p / p.2.1 ^ 3 := by
  have hd := hV.differentiableAt (by norm_num)
  have hds := differentiableAt_partialS hV
  have hdb := differentiableAt_radialB hd hs
  have hdbs := differentiableAt_radialB hds hs
  have hdbb := differentiableAt_radialB hdb hs
  have he : partialS (radialB V) =ᶠ[𝓝 p]
      (fun q => radialB (partialS V) q + 2 * radialB (radialB V) q) := by
    filter_upwards [hV.eventually (by norm_num),
      sProjection.continuous.continuousAt.eventually_ne hs] with q hq hsq
    exact partialS_radialB (hq.differentiableAt (by norm_num)) hsq
  change fderiv ℝ (partialS (radialB V)) p (0, (1, 0)) = _
  rw [he.fderiv_eq, fderiv_fun_add hdbs (hdbb.const_mul 2), fderiv_const_mul hdbb]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  change partialS (radialB (partialS V)) p +
    2 * partialS (radialB (radialB V)) p = _
  rw [partialS_radialB hds hs, partialS_radialB hdb hs]
  simp only [radialB]
  rw [partialS_radialB_explicit hd hs]
  field_simp [hs]; ring

theorem partialZ_partialZ_radialB {V : Profile} {p : ProfilePoint}
    (hV : ContDiffAt ℝ 2 V p) (hs : p.2.1 ≠ 0) :
    partialZ (partialZ (radialB V)) p = radialB (partialZ (partialZ V)) p := by
  have he : partialZ (radialB V) =ᶠ[𝓝 p] radialB (partialZ V) := by
    filter_upwards [hV.eventually (by norm_num),
      sProjection.continuous.continuousAt.eventually_ne hs] with q hq hsq
    exact partialZ_radialB (hq.differentiableAt (by norm_num)) hsq
  change fderiv ℝ (partialZ (radialB V)) p (0, (0, 1)) = _
  rw [he.fderiv_eq]
  exact partialZ_radialB (differentiableAt_partialZ hV) hs

/-- The `4 B_s` connection term cancels the extra radial quotient terms. -/
theorem laplaceWeighted_radialB {V : Profile} {p : ProfilePoint}
    (hV : ContDiffAt ℝ 2 V p) (hs : p.2.1 ≠ 0) :
    laplaceWeighted (radialB V) p =
      -partialS (partialS V) p - partialZ (partialZ V) p / (2 * p.2.1) := by
  have hd := hV.differentiableAt (by norm_num)
  unfold laplaceWeighted
  rw [partialS_partialS_radialB hV hs, partialS_radialB_explicit hd hs,
    partialZ_partialZ_radialB hV hs]
  unfold radialB
  field_simp [hs]; ring

theorem divergence_coefficient {V : Profile} (U : Profile) {p : ProfilePoint}
    (hV : DifferentiableAt ℝ V p) (hs : p.2.1 ≠ 0) :
    partialZ U p - 2 * radialB V p - 2 * p.2.1 * partialS (radialB V) p =
      partialS V p + partialZ U p := by
  rw [partialS_radialB_explicit hV hs]
  unfold radialB
  field_simp [hs]; ring

private theorem hasFDerivAt_velocity_at {B F U : Profile} {t : ℝ} {x : Space}
    (hB : DifferentiableAt ℝ B (profilePoint t x))
    (hF : DifferentiableAt ℝ F (profilePoint t x))
    (hU : DifferentiableAt ℝ U (profilePoint t x)) :
    HasFDerivAt (fun y => AxisymmetricResidual.velocity B F U (t, y))
      (velocityJacobian B F U t x) x := by
  have hb := hasFDerivAt_profile_composition B t x hB
  have hf := hasFDerivAt_profile_composition F t x hF
  have hu := hasFDerivAt_profile_composition U t x hU
  exact hasFDerivAt_pack
    ((((projection 0).hasFDerivAt.mul hb).add ((projection 1).hasFDerivAt.mul hf)).neg)
    (((projection 0).hasFDerivAt.mul hf).sub ((projection 1).hasFDerivAt.mul hb)) hu

theorem divergence_velocity_at {B F U : Profile} {t : ℝ} {x : Space}
    (hB : DifferentiableAt ℝ B (profilePoint t x))
    (hF : DifferentiableAt ℝ F (profilePoint t x))
    (hU : DifferentiableAt ℝ U (profilePoint t x)) :
    spatialDivergence (AxisymmetricResidual.velocity B F U) t x =
      partialZ U (profilePoint t x) - 2 * B (profilePoint t x) -
        2 * radialEnergy x * partialS B (profilePoint t x) := by
  unfold spatialDivergence spatialDerivative
  rw [(hasFDerivAt_velocity_at hB hF hU).fderiv, Fin.sum_univ_three]
  simp [velocityJacobian, packDerivative_apply, profileDerivative_apply,
    coordinateVector, profilePoint, radialEnergy, lift]
  ring

/-- Actual Cartesian divergence, needing regularity only at the evaluated
profile point. No smooth extension of the quotient across the axis is assumed. -/
theorem divergence_radialB {V F U : Profile} {t : ℝ} {x : Space}
    (hV : DifferentiableAt ℝ V (profilePoint t x))
    (hF : DifferentiableAt ℝ F (profilePoint t x))
    (hU : DifferentiableAt ℝ U (profilePoint t x)) (hs : 0 < radialEnergy x) :
    spatialDivergence (AxisymmetricResidual.velocity (radialB V) F U) t x =
      partialS V (profilePoint t x) + partialZ U (profilePoint t x) := by
  have hne : (profilePoint t x).2.1 ≠ 0 := ne_of_gt hs
  rw [divergence_velocity_at (differentiableAt_radialB hV hne) hF hU]
  exact divergence_coefficient U hV hne

/-- The substitution has exactly the intended physical radial flux. -/
theorem radial_flux_velocity (V F U : Profile) (t : ℝ) (x : Space)
    (hs : 0 < radialEnergy x) :
    x 0 * AxisymmetricResidual.velocity (radialB V) F U (t, x) 0 +
      x 1 * AxisymmetricResidual.velocity (radialB V) F U (t, x) 1 =
        V (profilePoint t x) := by
  calc
    _ = -2 * radialEnergy x * radialB V (profilePoint t x) := by
      simp [AxisymmetricResidual.velocity, componentX, componentY, lift, radialEnergy]
      ring
    _ = _ := by
      change -2 * radialEnergy x * (-V (profilePoint t x) / (2 * radialEnergy x)) = _
      field_simp [ne_of_gt hs]

/-- Flux residual, constructed using `partialT`. -/
noncomputable def fluxResidual (V F U P : Profile) (p : ProfilePoint) : ℝ :=
  partialT V p + V p * (partialS V p - V p / (2 * p.2.1)) + U p * partialZ V p -
    2 * p.2.1 * partialS (partialS V) p - partialZ (partialZ V) p +
      2 * p.2.1 * (partialS P p - (F p) ^ 2)

/-- The radial residual coefficient in `AxisymmetricResidual` multiplies
`(x₀,x₁,0)`. Thus its product with `2s=r²` is `r` times the cylindrical
radial residual, with the positive sign in this identity. -/
theorem residualRadial_radialB {V : Profile} (F U P : Profile) {p : ProfilePoint}
    (hV : ContDiffAt ℝ 2 V p) (hs : 0 < p.2.1) :
    2 * p.2.1 * residualRadial (radialB V) F U P p = fluxResidual V F U P p := by
  have hne := ne_of_gt hs
  have hd := hV.differentiableAt (by norm_num)
  unfold residualRadial advectionRadial
  rw [partialT_radialB hd hne, partialS_radialB_explicit hd hne,
    partialZ_radialB hd hne, laplaceWeighted_radialB hV hne]
  unfold fluxResidual radialB
  field_simp [hne]; ring

/-- The actual physical radial residual multiplied by `r`, expressed
without introducing a square root or a radial unit vector. All regularity
hypotheses are local at the evaluated point with `s > 0`. -/
theorem physical_radial_flux_residual {V F U P : Profile} {t : ℝ} {x : Space}
    (hV : ContDiffAt ℝ 2 V (profilePoint t x))
    (hF : ContDiffAt ℝ 2 F (profilePoint t x))
    (hU : ContDiffAt ℝ 2 U (profilePoint t x))
    (hP : DifferentiableAt ℝ P (profilePoint t x)) (hs : 0 < radialEnergy x) :
    x 0 * navierStokesResidual (AxisymmetricResidual.velocity (radialB V) F U)
        (pressure P) t x 0 +
      x 1 * navierStokesResidual (AxisymmetricResidual.velocity (radialB V) F U)
        (pressure P) t x 1 = fluxResidual V F U P (profilePoint t x) := by
  have hB := contDiffAt_radialB hV (ne_of_gt hs)
  have hR := LocalAxisymmetricResidual.navierStokesResidual_velocity hB hF hU hP
  simp only [hR, pack_zero, pack_one]
  calc
    _ = 2 * radialEnergy x * residualRadial (radialB V) F U P (profilePoint t x) := by
      unfold radialEnergy
      ring
    _ = _ := residualRadial_radialB F U P hV hs

end

end NavierStokes.RadialFluxResidual
