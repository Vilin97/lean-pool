/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Caccioppoli.Conversions
public import LeanPool.CaffarelliKohnNirenberg.Setting.Finiteness
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Slice Norm Bounds

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration

noncomputable section
namespace CKN

/-!
# Slice norm bounds

This module formalizes paper equation `eq:slice-norm-bounds` of `paper/ckn.tex`.
The five dimensionless scale quantities `alpha`, `beta`, `gamma`, `delta` and
`lambda` are defined in `CKN/Statements/*.lean` by normalizing a nonnegative
space-time integral by a power of the radius; `eq:slice-norm-bounds` is the
inverse reading of those definitions, expressing the unnormalized slice
integrals directly in terms of the scale quantities:

* the time-slice energy essential supremum of `u` is `r * α(z,r)²`,
* the Dirichlet energy `∫∫_{Q_r} |∇u|²` is `r * β(z,r)²`,
* the pressure integral `∫∫_{Q_r} |p|^{3/2}` is `r² * δ(z,r)³`,
* the force integral `∫∫_{Q_r} |f|^q` is `(r^{5/q-3} λ(z,r))^q`, where
  `σ = 3 - 5/q` is the exponent of `paper/ckn.tex` equation `eq:lambda`.

The definitions pass the underlying `ℝ≥0∞` integral to `ℝ≥0` with
`ENNReal.toReal`, so each identity requires the relevant integral at radius `r`
to be finite; this is the `hfin` hypothesis below, discharged for suitable weak
solutions by the finiteness lemmas of `CKN/Setting/Finiteness.lean`.

Each identity is stated twice: as an identity of `ℝ≥0∞` integrals, and as an
identity of Bochner set integrals for the (nonnegative) real density, using the
conversion `setIntegral_eq_toReal_setLIntegral_of_nonneg` of
`CKN/Core/Caccioppoli/Conversions.lean`.
-/

/-! ### Nonnegativity of the densities -/

/-- The squared spatial-gradient density is nonnegative, being a sum of squares. -/
private lemma spatialGradientSq_nonneg (u : ParabolicPoint → Vec3)
    (Du : ParabolicPoint → Fin 3 → Vec3) (z : ParabolicPoint) :
    0 ≤ spatialGradientSq u Du z := by
  unfold spatialGradientSq
  positivity

/-- The force quantity `lambda` is nonnegative at a positive radius. -/
private lemma lambda_nonneg (q : ℝ) (f : ParabolicPoint → Vec3) (z : ParabolicPoint)
    {r : ℝ} (hr : 0 < r) :
    0 ≤ lambda q f z r := by
  unfold lambda
  exact mul_nonneg (Real.rpow_nonneg hr.le _)
    (Real.rpow_nonneg ENNReal.toReal_nonneg _)

/-- The pressure quantity `delta` is nonnegative at a positive radius. -/
private lemma delta_nonneg (p : ParabolicPoint → ℝ) (z : ParabolicPoint) {r : ℝ}
    (hr : 0 < r) :
    0 ≤ delta p z r := by
  unfold delta
  exact Real.rpow_nonneg
    (mul_nonneg (Real.rpow_nonneg hr.le _) ENNReal.toReal_nonneg) _

/-- A real function with a Bochner set integral has a finite `ofReal` lintegral,
so the `toReal` reading of that lintegral is faithful. -/
private lemma lintegral_ofReal_ne_top_of_integrableOn {s : Set ParabolicPoint}
    {g : ParabolicPoint → ℝ} (hg : IntegrableOn g s volume) :
    (∫⁻ w in s, ENNReal.ofReal (g w)) ≠ ⊤ := by
  have hle := lintegral_ofReal_le_lintegral_enorm (μ := volume.restrict s) g
  exact ne_of_lt (lt_of_le_of_lt hle hg.2)

/-! ### The time-slice energy identity for `alpha` -/

/-- Paper equation `eq:slice-norm-bounds`, velocity line: the essential supremum
of the time-slice energy of `u` over the cylinder is `r * α(z,r)²`. -/
theorem timeSliceEnergyEssSup_eq_ofReal_alpha_sq
    (u : ParabolicPoint → Vec3) (z : ParabolicPoint) {r : ℝ} (hr : 0 < r)
    (hfin : timeSliceEnergyEssSup z.1 z.2 r (fun w => vec3EuclideanNorm (u w)) ≠ ⊤) :
    timeSliceEnergyEssSup z.1 z.2 r (fun w => vec3EuclideanNorm (u w)) =
      ENNReal.ofReal (r * alpha u z r ^ 2) := by
  have hsq := alpha_sq_eq u z r hr
  have hmul : r * alpha u z r ^ 2 =
      (timeSliceEnergyEssSup z.1 z.2 r (fun w => vec3EuclideanNorm (u w))).toReal := by
    rw [hsq, ← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul]
  rw [hmul, ENNReal.ofReal_toReal hfin]

/-! ### The Dirichlet energy identity for `beta` -/

/-- Paper equation `eq:slice-norm-bounds`, gradient line: the Dirichlet energy of
`u` over the cylinder is `r * β(z,r)²`. -/
theorem lintegral_spatialGradientSq_eq_ofReal_beta_sq
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (z : ParabolicPoint) {r : ℝ} (hr : 0 < r)
    (hfin : (∫⁻ w in parabolicCylinder z.1 z.2 r,
        ENNReal.ofReal (spatialGradientSq u Du w)) ≠ ⊤) :
    (∫⁻ w in parabolicCylinder z.1 z.2 r,
        ENNReal.ofReal (spatialGradientSq u Du w)) =
      ENNReal.ofReal (r * beta u Du z r ^ 2) := by
  have hsq := beta_sq_eq u Du z r hr
  have hmul : r * beta u Du z r ^ 2 =
      (∫⁻ w in parabolicCylinder z.1 z.2 r,
        ENNReal.ofReal (spatialGradientSq u Du w)).toReal := by
    rw [hsq, ← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul]
  rw [hmul, ENNReal.ofReal_toReal hfin]

/-- The real Bochner form of the gradient line of `eq:slice-norm-bounds`: the
Dirichlet energy of `u` over the cylinder is `r * β(z,r)²`. -/
theorem integral_spatialGradientSq_eq_beta_sq
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (z : ParabolicPoint) {r : ℝ} (hr : 0 < r)
    (hint : IntegrableOn (fun w => spatialGradientSq u Du w)
      (parabolicCylinder z.1 z.2 r) volume) :
    ∫ w in parabolicCylinder z.1 z.2 r, spatialGradientSq u Du w =
      r * beta u Du z r ^ 2 := by
  rw [setIntegral_eq_toReal_setLIntegral_of_nonneg hint
    (Eventually.of_forall (fun w => spatialGradientSq_nonneg u Du w))]
  rw [lintegral_spatialGradientSq_eq_ofReal_beta_sq u Du z hr
    (lintegral_ofReal_ne_top_of_integrableOn hint)]
  exact ENNReal.toReal_ofReal (mul_nonneg hr.le (sq_nonneg _))

/-! ### The pressure integral identity for `delta` -/

/-- Paper equation `eq:slice-norm-bounds`, pressure line: the pressure integral
`∫∫_{Q_r} |p|^{3/2}` is `r² * δ(z,r)³`. -/
theorem lintegral_abs_pow_eq_ofReal_delta_cube
    (p : ParabolicPoint → ℝ) (z : ParabolicPoint) {r : ℝ} (hr : 0 < r)
    (hfin : (∫⁻ w in parabolicCylinder z.1 z.2 r,
        ENNReal.ofReal |p w| ^ (3 / 2 : ℝ)) ≠ ⊤) :
    (∫⁻ w in parabolicCylinder z.1 z.2 r,
        ENNReal.ofReal |p w| ^ (3 / 2 : ℝ)) =
      ENNReal.ofReal (r ^ 2 * delta p z r ^ 3) := by
  have hcube := delta_cube_eq p z r hr
  have hpow : r ^ 2 * r ^ (-2 : ℝ) = (1 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hr]
    norm_num
  have hmul : r ^ 2 * delta p z r ^ 3 =
      (∫⁻ w in parabolicCylinder z.1 z.2 r,
        ENNReal.ofReal |p w| ^ (3 / 2 : ℝ)).toReal := by
    rw [hcube, ← mul_assoc, hpow, one_mul]
  rw [hmul, ENNReal.ofReal_toReal hfin]

/-- The real Bochner form of the pressure line of `eq:slice-norm-bounds`: the
pressure integral `∫∫_{Q_r} |p|^{3/2}` is `r² * δ(z,r)³`. -/
theorem integral_abs_pow_eq_delta_cube
    (p : ParabolicPoint → ℝ) (z : ParabolicPoint) {r : ℝ} (hr : 0 < r)
    (hint : IntegrableOn (fun w => |p w| ^ (3 / 2 : ℝ))
      (parabolicCylinder z.1 z.2 r) volume) :
    ∫ w in parabolicCylinder z.1 z.2 r, |p w| ^ (3 / 2 : ℝ) =
      r ^ 2 * delta p z r ^ 3 := by
  have hcongr : (∫⁻ w in parabolicCylinder z.1 z.2 r, ENNReal.ofReal (|p w| ^ (3 / 2 : ℝ))) =
      ∫⁻ w in parabolicCylinder z.1 z.2 r, ENNReal.ofReal |p w| ^ (3 / 2 : ℝ) :=
    lintegral_congr (fun w =>
      (ENNReal.ofReal_rpow_of_nonneg (abs_nonneg (p w)) (by norm_num : (0 : ℝ) ≤ 3 / 2)).symm)
  have hfin : (∫⁻ w in parabolicCylinder z.1 z.2 r,
      ENNReal.ofReal |p w| ^ (3 / 2 : ℝ)) ≠ ⊤ := by
    rw [← hcongr]
    exact lintegral_ofReal_ne_top_of_integrableOn hint
  rw [setIntegral_eq_toReal_setLIntegral_of_nonneg hint
    (Eventually.of_forall (fun w => Real.rpow_nonneg (abs_nonneg (p w)) _))]
  rw [hcongr, lintegral_abs_pow_eq_ofReal_delta_cube p z hr hfin]
  exact ENNReal.toReal_ofReal (mul_nonneg (sq_nonneg _) (pow_nonneg (delta_nonneg p z hr) _))

/-! ### The force integral identity for `lambda` -/

/-- Paper equation `eq:slice-norm-bounds`, force line: with `σ = 3 - 5/q`, the
force integral `∫∫_{Q_r} |f|^q` is `(r^{-σ} λ(z,r))^q`. -/
theorem lintegral_vec3EuclideanNorm_pow_eq_ofReal_lambda_pow
    (q : ℝ) (f : ParabolicPoint → Vec3) (z : ParabolicPoint) {r : ℝ}
    (hr : 0 < r) (hq : 0 < q)
    (hfin : (∫⁻ w in parabolicCylinder z.1 z.2 r,
        ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q) ≠ ⊤) :
    (∫⁻ w in parabolicCylinder z.1 z.2 r,
        ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q) =
      ENNReal.ofReal ((r ^ (5 / q - 3) * lambda q f z r) ^ q) := by
  have hpow := lambda_pow_eq q f z r hr hq
  have hexp0 : (3 - 5 / q) * q = 3 * q - 5 := by
    rw [sub_mul, div_mul_cancel₀ 5 hq.ne']
  have hexp1 : (5 / q - 3) * q = 5 - 3 * q := by
    rw [sub_mul, div_mul_cancel₀ 5 hq.ne']
  have hA0 : (r ^ (3 - 5 / q)) ^ q = r ^ (3 * q - 5) := by
    rw [← Real.rpow_mul hr.le, hexp0]
  have hAne : (r ^ (3 - 5 / q)) ^ q ≠ 0 :=
    ne_of_gt (by rw [hA0]; exact Real.rpow_pos_of_pos hr _)
  have hI : (∫⁻ w in parabolicCylinder z.1 z.2 r,
        ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q).toReal =
      lambda q f z r ^ q * r ^ (5 - 3 * q) := by
    have hdiv : (∫⁻ w in parabolicCylinder z.1 z.2 r,
          ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q).toReal =
        lambda q f z r ^ q / (r ^ (3 - 5 / q)) ^ q := by
      rw [eq_div_iff hAne, mul_comm]
      exact hpow.symm
    rw [hdiv, hA0, div_eq_mul_inv]
    rw [show r ^ (5 - 3 * q) = (r ^ (3 * q - 5))⁻¹ by
      rw [show 5 - 3 * q = -(3 * q - 5) by ring, Real.rpow_neg hr.le]]
  have hrpow : r ^ (5 - 3 * q) = (r ^ (5 / q - 3)) ^ q := by
    rw [← Real.rpow_mul hr.le, hexp1]
  have hfinal : (∫⁻ w in parabolicCylinder z.1 z.2 r,
        ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q).toReal =
      (r ^ (5 / q - 3) * lambda q f z r) ^ q := by
    rw [hI, hrpow, Real.mul_rpow (Real.rpow_nonneg hr.le _) (lambda_nonneg q f z hr)]
    exact mul_comm _ _
  rw [← ENNReal.ofReal_toReal hfin, hfinal]

/-! ### The identities for suitable weak solutions -/

/-- Paper equation `eq:slice-norm-bounds`, velocity line, for a suitable weak
solution whose cylinder has closure in the carrier: the essential supremum of the
time-slice energy of `u` is `r * α(z,r)²`. -/
theorem sws_timeSliceEnergyEssSup_eq_ofReal_alpha_sq
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (h : IsSuitableWeakSolutionIntegrable Ω I q u Du p f) (z : ParabolicPoint) {r : ℝ}
    (hr : 0 < r) (hsub : closure (parabolicCylinder z.1 z.2 r) ⊆ spaceTimeSet Ω I) :
    timeSliceEnergyEssSup z.1 z.2 r (fun w => vec3EuclideanNorm (u w)) =
      ENNReal.ofReal (r * alpha u z r ^ 2) :=
  timeSliceEnergyEssSup_eq_ofReal_alpha_sq u z hr
    (ne_of_lt (sws_timeSliceEnergyEssSup_lt_top h hr hsub))

/-- Paper equation `eq:slice-norm-bounds`, gradient line, for a suitable weak
solution whose cylinder has closure in the carrier: the Dirichlet energy of `u`
is `r * β(z,r)²`. -/
theorem sws_lintegral_spatialGradientSq_eq_ofReal_beta_sq
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (h : IsSuitableWeakSolutionIntegrable Ω I q u Du p f) (z : ParabolicPoint) {r : ℝ}
    (hr : 0 < r) (hsub : closure (parabolicCylinder z.1 z.2 r) ⊆ spaceTimeSet Ω I) :
    (∫⁻ w in parabolicCylinder z.1 z.2 r,
        ENNReal.ofReal (spatialGradientSq u Du w)) =
      ENNReal.ofReal (r * beta u Du z r ^ 2) :=
  lintegral_spatialGradientSq_eq_ofReal_beta_sq u Du z hr
    (ne_of_lt (sws_gradient_integral_lt_top h hr hsub))

/-- Paper equation `eq:slice-norm-bounds`, pressure line, for a suitable weak
solution whose cylinder has closure in the carrier: the pressure integral
`∫∫_{Q_r} |p|^{3/2}` is `r² * δ(z,r)³`. -/
theorem sws_lintegral_abs_pow_eq_ofReal_delta_cube
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (h : IsSuitableWeakSolutionIntegrable Ω I q u Du p f) (z : ParabolicPoint) {r : ℝ}
    (hr : 0 < r) (hsub : closure (parabolicCylinder z.1 z.2 r) ⊆ spaceTimeSet Ω I) :
    (∫⁻ w in parabolicCylinder z.1 z.2 r,
        ENNReal.ofReal |p w| ^ (3 / 2 : ℝ)) =
      ENNReal.ofReal (r ^ 2 * delta p z r ^ 3) :=
  lintegral_abs_pow_eq_ofReal_delta_cube p z hr
    (ne_of_lt (sws_pressure_integral_lt_top h hr hsub))

/-- Paper equation `eq:slice-norm-bounds`, force line, for a suitable weak
solution whose cylinder has closure in the carrier: with `σ = 3 - 5/q`, the force
integral `∫∫_{Q_r} |f|^q` is `(r^{-σ} λ(z,r))^q`. -/
theorem sws_lintegral_vec3EuclideanNorm_pow_eq_ofReal_lambda_pow
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (h : IsSuitableWeakSolutionIntegrable Ω I q u Du p f) (z : ParabolicPoint) {r : ℝ}
    (hr : 0 < r) (hsub : closure (parabolicCylinder z.1 z.2 r) ⊆ spaceTimeSet Ω I) :
    (∫⁻ w in parabolicCylinder z.1 z.2 r,
        ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q) =
      ENNReal.ofReal ((r ^ (5 / q - 3) * lambda q f z r) ^ q) :=
  lintegral_vec3EuclideanNorm_pow_eq_ofReal_lambda_pow q f z hr
    (lt_trans (by norm_num : (0 : ℝ) < 5 / 2) h.2.2.2.1)
    (ne_of_lt (sws_force_integral_lt_top h hr hsub))

/-! ### The real Bochner identities for suitable weak solutions -/

/-- Paper equation `eq:slice-norm-bounds`, pressure line, in real Bochner form for
a suitable weak solution: the pressure integral `∫∫_{Q_r} |p|^{3/2}` is
`r² * δ(z,r)³`. -/
theorem sws_integral_abs_pow_eq_delta_cube
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (h : IsSuitableWeakSolutionIntegrable Ω I q u Du p f) (z : ParabolicPoint) {r : ℝ}
    (hr : 0 < r) (hsub : closure (parabolicCylinder z.1 z.2 r) ⊆ spaceTimeSet Ω I) :
    ∫ w in parabolicCylinder z.1 z.2 r, |p w| ^ (3 / 2 : ℝ) =
      r ^ 2 * delta p z r ^ 3 := by
  obtain ⟨Ω', J, hbox, hcyl⟩ := exists_localBox_of_closure_subset h.1 h.2.1 hr hsub
  have hp : AEStronglyMeasurable p (volume.restrict (spaceTimeSet Ω' J)) :=
    (h.2.2.2.2.2.1 Ω' J hbox).2.2.1
  have hpabs : AEStronglyMeasurable (fun w => |p w|)
      (volume.restrict (spaceTimeSet Ω' J)) :=
    continuous_abs.comp_aestronglyMeasurable hp
  have hmeasBox : AEStronglyMeasurable (fun w => |p w| ^ (3 / 2 : ℝ))
      (volume.restrict (spaceTimeSet Ω' J)) := by
    have := (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 3 / 2)).comp_aestronglyMeasurable
      hpabs
    simpa [Function.comp_def] using this
  have hmeas : AEStronglyMeasurable (fun w => |p w| ^ (3 / 2 : ℝ))
      (volume.restrict (parabolicCylinder z.1 z.2 r)) :=
    hmeasBox.mono_measure (Measure.restrict_mono hcyl le_rfl)
  have hnonneg : 0 ≤ᵐ[volume.restrict (parabolicCylinder z.1 z.2 r)]
      fun w => |p w| ^ (3 / 2 : ℝ) :=
    Eventually.of_forall (fun w => Real.rpow_nonneg (abs_nonneg (p w)) _)
  have hcongr : (∫⁻ w in parabolicCylinder z.1 z.2 r, ENNReal.ofReal (|p w| ^ (3 / 2 : ℝ))) =
      ∫⁻ w in parabolicCylinder z.1 z.2 r, ENNReal.ofReal |p w| ^ (3 / 2 : ℝ) :=
    lintegral_congr (fun w =>
      (ENNReal.ofReal_rpow_of_nonneg (abs_nonneg (p w)) (by norm_num : (0 : ℝ) ≤ 3 / 2)).symm)
  have hfin : (∫⁻ w in parabolicCylinder z.1 z.2 r, ENNReal.ofReal (|p w| ^ (3 / 2 : ℝ))) < ⊤ := by
    rw [hcongr]
    exact sws_pressure_integral_lt_top h hr hsub
  have hint : IntegrableOn (fun w => |p w| ^ (3 / 2 : ℝ))
      (parabolicCylinder z.1 z.2 r) volume :=
    (lintegral_ofReal_ne_top_iff_integrable hmeas hnonneg).mp (ne_of_lt hfin)
  exact integral_abs_pow_eq_delta_cube p z hr hint

end CKN
