/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.StartCaccioppoli
public import Mathlib.Analysis.Real.Pi.Bounds
public import LeanPool.CaffarelliKohnNirenberg.Setting.SliceNormBounds
public import LeanPool.CaffarelliKohnNirenberg.Setting.ScalingQuantityNonneg

/-! # Unit-data control of interior Dirichlet energy

The force coefficient in the gamma-form Caccioppoli estimate has an absolute
upper bound. Applying the display on a doubled interior cylinder produces
an explicit energy coefficient before any solution is chosen.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal Topology
open CKN CKN.Foundation.Parabolic CKN.Core.Endgame
noncomputable section
namespace CKN.Core.Step4

/-- An absolute bound for the force coefficient in the gamma display. -/
def caccioppoliForceAbsolute : ℝ := Real.sqrt (12000000 * (4*Real.pi/3))

/-- The force coefficient is bounded uniformly for every admissible exponent. -/
theorem caccioppoli_force_coefficient_le_absolute {q : ℝ} (hq : 5 / 2 < q) :
    caccioppoliC₂₆ q ≤ caccioppoliForceAbsolute := by
  have hq0 : 0 < q := by linarith only [hq]
  have hq1 : q - 1 ≠ 0 := by linarith only [hq]
  have he : 1/(q/(q-1)) - 1/3 = 2/3 - 1/q := by field_simp; ring
  have hbase : 1 ≤ 4*Real.pi/3 := by linarith only [Real.pi_gt_three]
  have hp : (4*Real.pi/3) ^ (1/(q/(q-1)) - 1/3 : ℝ) ≤ 4*Real.pi/3 := by
    rw [he]
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hbase
      (show (2/3 : ℝ)-1/q ≤ 1 by have h := one_div_pos.mpr hq0; linarith only [h])
  unfold caccioppoliC₂₆ caccioppoliForceAbsolute
  apply Real.sqrt_le_sqrt
  nlinarith only [hp]

/-- The explicit half-radius beta coefficient. -/
def interiorBetaDataConstant (ρ : ℝ) : ℝ :=
  let A := (ρ ^ (-2 : ℝ)) ^ (1/3 : ℝ)
  startGammaConstant * (A/2 + 4*A^(3/2 : ℝ)) +
    caccioppoliForceAbsolute * (1/2 : ℝ)^(-1/2 : ℝ) * A^(1/2 : ℝ)

/-- The corresponding explicit Dirichlet-energy coefficient. -/
def interiorDirichletDataConstant (ρ : ℝ) : ℝ :=
  (ρ/2) * interiorBetaDataConstant ρ ^ 2

private theorem gamma_delta_bound {m ε ρ : ℝ} (hm : 0 ≤ m) (hmε : m ≤ ε)
    (hρ : 0 < ρ) :
    (ρ ^ (-2 : ℝ) * m) ^ (1/3 : ℝ) ≤
      (ρ ^ (-2 : ℝ)) ^ (1/3 : ℝ) * (ε+1) ^ (1/3 : ℝ) := by
  rw [Real.mul_rpow (Real.rpow_nonneg hρ.le _) hm]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow hm (hmε.trans (by linarith only [])) (by norm_num))
    (Real.rpow_nonneg (Real.rpow_nonneg hρ.le _) _)

private theorem force_lambda_bound {m ε ρ q : ℝ} (hm : 0 ≤ m) (hmε : m ≤ ε)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hq : 5 / 2 < q) :
    ρ ^ (3-5/q) * m ^ (1/q) ≤ (ε+1) ^ (1/q) := by
  have hq0 : 0 < q := by linarith only [hq]
  have he : 0 ≤ 3-5/q := by
    have ht : 5/q < 3 := (div_lt_iff₀ hq0).mpr (by linarith only [hq])
    linarith only [ht]
  calc
    _ ≤ 1 * (ε+1) ^ (1/q) := mul_le_mul
      (Real.rpow_le_one hρ.le hρ1 he)
      (Real.rpow_le_rpow hm (hmε.trans (by linarith only [])) (one_div_nonneg.mpr hq0.le))
      (Real.rpow_nonneg hm _) (by norm_num)
    _ = _ := one_mul _

private theorem normalized_gamma_rhs_bound {G D L E A q : ℝ}
    (hG0 : 0 ≤ G) (hL0 : 0 ≤ L) (hA : 0 < A)
    (hE : 1 ≤ E) (hq : 5 / 2 < q)
    (hG : G ≤ A * E ^ (1 / 3 : ℝ)) (hD : D ≤ A * E ^ (1 / 3 : ℝ))
    (hL : L ≤ E ^ (1 / q)) :
    startGammaConstant * ((1/2 : ℝ)*G + 2*G^(3/2 : ℝ) + 2*D*G^(1/2 : ℝ)) +
      caccioppoliC₂₆ q * (1/2 : ℝ)^(-1/2 : ℝ) * G^(1/2 : ℝ) * L^(1/2 : ℝ) ≤
    (startGammaConstant * (A/2+4*A^(3/2 : ℝ)) +
      caccioppoliForceAbsolute * (1/2 : ℝ)^(-1/2 : ℝ) * A^(1/2 : ℝ)) * E^(1/2 : ℝ) := by
  have hE0 : 0 < E := lt_of_lt_of_le zero_lt_one hE
  have hq0 : 0 < q := by linarith only [hq]
  have hG1 : G ≤ A*E^(1/2 : ℝ) := hG.trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hE (by norm_num)) hA.le)
  have hGp : G^(3/2 : ℝ) ≤ A^(3/2 : ℝ)*E^(1/2 : ℝ) := by
    have h := Real.rpow_le_rpow hG0 hG (by norm_num : (0 : ℝ) ≤ 3/2)
    rw [Real.mul_rpow hA.le (Real.rpow_nonneg hE0.le _), ← Real.rpow_mul hE0.le] at h
    norm_num at h
    exact h
  have hDG : D*G^(1/2 : ℝ) ≤ A^(3/2 : ℝ)*E^(1/2 : ℝ) := by
    have h := mul_le_mul hD (Real.rpow_le_rpow hG0 hG (by norm_num : (0 : ℝ) ≤ 1/2))
      (Real.rpow_nonneg hG0 _) (mul_nonneg hA.le (Real.rpow_nonneg hE0.le _))
    rw [Real.mul_rpow hA.le (Real.rpow_nonneg hE0.le _), ← Real.rpow_mul hE0.le] at h
    have heq : A*E^(1/3 : ℝ)*(A^(1/2 : ℝ)*E^((1/3 : ℝ)*(1/2))) =
        A^(3/2 : ℝ)*E^(1/2 : ℝ) := by
      calc
        _ = (A*A^(1/2 : ℝ)) * (E^(1/3 : ℝ)*E^((1/3 : ℝ)*(1/2))) := by ring
        _ = _ := by
          have ha : A*A^(1/2 : ℝ) = A^(3/2 : ℝ) := by
            calc
              _ = A^(1 : ℝ)*A^(1/2 : ℝ) := by rw [Real.rpow_one]
              _ = _ := by rw [← Real.rpow_add hA]; norm_num
          rw [ha, ← Real.rpow_add hE0]
          norm_num
    exact h.trans_eq heq
  have hGL : G^(1/2 : ℝ)*L^(1/2 : ℝ) ≤ A^(1/2 : ℝ)*E^(1/2 : ℝ) := by
    have h := mul_le_mul (Real.rpow_le_rpow hG0 hG (by norm_num : (0 : ℝ) ≤ 1/2))
      (Real.rpow_le_rpow hL0 hL (by norm_num : (0 : ℝ) ≤ 1/2)) (Real.rpow_nonneg hL0 _)
      (Real.rpow_nonneg (mul_nonneg hA.le (Real.rpow_nonneg hE0.le _)) _)
    rw [Real.mul_rpow hA.le (Real.rpow_nonneg hE0.le _),
      ← Real.rpow_mul hE0.le, ← Real.rpow_mul hE0.le, mul_assoc, ← Real.rpow_add hE0] at h
    apply h.trans
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hA.le _)
    apply Real.rpow_le_rpow_of_exponent_le hE
    have hi : 1/q < 2/5 := (div_lt_iff₀ hq0).mpr (by linarith only [hq])
    linarith only [hi]
  have hC : 0 ≤ startGammaConstant := Real.sqrt_nonneg _
  have hCf : 0 ≤ caccioppoliForceAbsolute := Real.sqrt_nonneg _
  have hLHS := add_le_add
    (mul_le_mul_of_nonneg_left
      (add_le_add (add_le_add (mul_le_mul_of_nonneg_left hG1 (by norm_num : (0 : ℝ) ≤ 1/2))
        (mul_le_mul_of_nonneg_left hGp (by norm_num : (0 : ℝ) ≤ 2)))
        (by nlinarith only [hDG] : 2*D*G^(1/2 : ℝ) ≤ 2*(A^(3/2 : ℝ)*E^(1/2 : ℝ)))) hC)
    (mul_le_mul_of_nonneg_left hGL
      (mul_nonneg hCf (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 1/2) (-1/2 : ℝ))))
  have hforce := caccioppoli_force_coefficient_le_absolute hq
  calc
    _ ≤ startGammaConstant * ((1/2 : ℝ)*G+2*G^(3/2 : ℝ)+2*D*G^(1/2 : ℝ)) +
        (caccioppoliForceAbsolute*(1/2 : ℝ)^(-1/2 : ℝ)) * (G^(1/2 : ℝ)*L^(1/2 : ℝ)) := by
      have h := mul_le_mul_of_nonneg_right hforce
        (show 0 ≤ (1/2 : ℝ)^(-1/2 : ℝ)*G^(1/2 : ℝ)*L^(1/2 : ℝ) by positivity)
      convert add_le_add_left h
        (startGammaConstant * ((1/2 : ℝ)*G+2*G^(3/2 : ℝ)+2*D*G^(1/2 : ℝ))) using 1 <;> ring
    _ ≤ _ := hLHS.trans_eq (by ring)

/-- A doubled cylinder inside the unit data cylinder has an explicit
Dirichlet bound independent of the velocity and gradient Morrey budgets. -/
theorem interior_dirichlet_bound_of_unit_data
    (ε : ℝ) (hε : 0 ≤ ε) {z : ParabolicPoint} {ρ : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hdom : closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I)
    (hsmall : (∫⁻ w in parabolicCylinder (0 : Vec3) 0 1,
      ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ) +
        ENNReal.ofReal |p w| ^ (3 / 2 : ℝ) +
        ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q) ≤ ENNReal.ofReal ε)
    (hQ : parabolicCylinder z.1 z.2 ρ ⊆ parabolicCylinder (0 : Vec3) 0 1) :
    (∫⁻ w in parabolicCylinder z.1 z.2 (ρ/2),
      ENNReal.ofReal (spatialGradientSq u Du w)) ≤
      ENNReal.ofReal (interiorDirichletDataConstant ρ) * (ENNReal.ofReal ε + 1) := by
  have hsub := (closure_mono hQ).trans hdom
  have hhalf : 0 < ρ/2 := by positivity
  have hinner := (closure_mono (parabolicCylinder_mono hhalf.le
    (show ρ/2 ≤ ρ by linarith only [hρ]))).trans hsub
  have hU : (∫⁻ w in parabolicCylinder z.1 z.2 ρ,
      ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) ≤ ENNReal.ofReal ε :=
    (lintegral_mono_set hQ).trans ((lintegral_mono
      (fun _ => (le_add_right le_rfl).trans (le_add_right le_rfl))).trans hsmall)
  have hP : (∫⁻ w in parabolicCylinder z.1 z.2 ρ,
      ENNReal.ofReal |p w| ^ (3/2 : ℝ)) ≤ ENNReal.ofReal ε :=
    (lintegral_mono_set hQ).trans ((lintegral_mono
      (fun _ => (le_add_left le_rfl).trans (le_add_right le_rfl))).trans hsmall)
  have hF : (∫⁻ w in parabolicCylinder z.1 z.2 ρ,
      ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q) ≤ ENNReal.ofReal ε :=
    (lintegral_mono_set hQ).trans ((lintegral_mono (fun _ => le_add_left le_rfl)).trans hsmall)
  have hreal {m : ℝ≥0∞} (hm : m ≤ ENNReal.ofReal ε) : m.toReal ≤ ε := by
    simpa only [ENNReal.toReal_ofReal hε] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hm
  have hg := gamma_delta_bound ENNReal.toReal_nonneg (hreal hU) hρ
  have hp := gamma_delta_bound ENNReal.toReal_nonneg (hreal hP) hρ
  have hf := force_lambda_bound ENNReal.toReal_nonneg (hreal hF) hρ hρ1 hsol.2.2.2.1
  have hb := caccioppoli_gamma_display_fixed hsol hρ hhalf le_rfl hsub
  have hratio : (ρ/2)/ρ = (1/2 : ℝ) := by field_simp
  rw [hratio] at hb
  norm_num only [Real.rpow_neg_one, inv_div, div_one] at hb
  have hn := normalized_gamma_rhs_bound (gamma_nonneg u z hρ.le)
    (lambda_nonneg q f z hρ.le) (Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hρ _) _)
    (show 1 ≤ ε+1 by linarith only [hε]) hsol.2.2.2.1 hg hp hf
  have hbeta : beta u Du z (ρ/2) ≤ interiorBetaDataConstant ρ * (ε+1)^(1/2 : ℝ) := by
    have hα := alpha_nonneg u z hhalf.le
    exact (le_add_of_nonneg_left hα).trans (hb.trans (by simpa only [interiorBetaDataConstant,
      neg_div, delta] using hn))
  have hc : 0 ≤ interiorBetaDataConstant ρ := by
    unfold interiorBetaDataConstant
    have hcg : 0 ≤ startGammaConstant := Real.sqrt_nonneg _
    have hcf : 0 ≤ caccioppoliForceAbsolute := Real.sqrt_nonneg _
    positivity
  have hs : beta u Du z (ρ/2)^2 ≤ interiorBetaDataConstant ρ ^ 2 * (ε+1) := by
    have hh := mul_self_le_mul_self (beta_nonneg u Du z hhalf.le) hbeta
    have he : ((ε+1)^(1/2 : ℝ))^2 = ε+1 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith only [hε] : 0 ≤ ε+1)]
      norm_num
    simpa only [← sq, mul_pow, he] using hh
  rw [sws_lintegral_spatialGradientSq_eq_ofReal_beta_sq hsol z hhalf hinner,
    show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by norm_num,
    ← ENNReal.ofReal_add hε (by norm_num),
    ← ENNReal.ofReal_mul (show 0 ≤ interiorDirichletDataConstant ρ by
      unfold interiorDirichletDataConstant; positivity)]
  apply ENNReal.ofReal_le_ofReal
  exact (mul_le_mul_of_nonneg_left hs hhalf.le).trans_eq (by
    unfold interiorDirichletDataConstant; ring)

end CKN.Core.Step4
