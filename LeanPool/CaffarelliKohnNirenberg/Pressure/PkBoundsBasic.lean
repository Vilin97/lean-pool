/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.DecompositionPotentials
public import LeanPool.CaffarelliKohnNirenberg.Setting.TimeHolder
public import LeanPool.CaffarelliKohnNirenberg.Setting.SliceNormBounds
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Pk Bounds Basic

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat

noncomputable section

namespace CKN

/-! Common annular and time-integration facts for the pressure terms. -/

/-- Spatial annulus supporting derivatives of the pressure cutoff. -/
@[expose] def pressureAnnulus (x₀ : Vec3) (ρ : ℝ) : Set Vec3 :=
  vec3Ball x₀ (3 * ρ / 4) \ vec3Ball x₀ (13 * ρ / 20)

theorem pressure_annulus_subset_ball {x₀ : Vec3} {ρ : ℝ} {y : Vec3}
    (hy : y ∈ pressureAnnulus x₀ ρ) : y ∈ vec3Ball x₀ (3 * ρ / 4) :=
  hy.1

theorem pressure_kernel_bound_on_annulus {x₀ x y : Vec3} {ρ r : ℝ}
    (hρ : 0 < ρ) (hr : 0 < r) (hhalf : r ≤ ρ / 2)
    (hx : x ∈ vec3Ball x₀ r) (hy : y ∈ pressureAnnulus x₀ ρ) :
    |CKN.Foundation.Heat.newtonianKernel (x - y)| ≤ 2 / ρ := by
  have hdist := cutoff_annulus_separation hρ hr hhalf hx hy
  have heuc : spaceEuclideanNorm (x - y) = vec3EuclideanNorm (x - y) := rfl
  have hnorm : ρ / 20 ≤ ‖x - y‖ := by
    have hle := euclideanNorm_le_three_mul_space_norm (x - y)
    rw [heuc] at hle
    nlinarith only [hdist, hle]
  have hne : x - y ≠ 0 := by
    intro hzero
    rw [hzero] at hdist
    simp only [vec3EuclideanNorm_zero] at hdist
    linarith only [hdist, hρ]
  have hbound := CKN.Foundation.Heat.newtonianKernel_size_bound hne
  have hinv : ‖x - y‖⁻¹ ≤ (ρ / 20)⁻¹ := by
    exact (inv_le_inv₀ (by positivity) (by positivity)).2 hnorm
  have hpi : (4 * Real.pi)⁻¹ * (ρ / 20)⁻¹ ≤ 2 / ρ := by
    have hπ : 3 < Real.pi := Real.pi_gt_three
    rw [inv_div]
    have hρ' : 0 < ρ := hρ
    field_simp [hρ'.ne']
    nlinarith only [hπ]
  exact hbound.trans ((mul_le_mul_of_nonneg_left hinv (by positivity)).trans hpi)

theorem pressure_kernel_deriv_bound_on_annulus {x₀ x y : Vec3} {ρ r : ℝ}
    (hρ : 0 < ρ) (hr : 0 < r) (hhalf : r ≤ ρ / 2)
    (hx : x ∈ vec3Ball x₀ r) (hy : y ∈ pressureAnnulus x₀ ρ) (i : Fin 3) :
    |CKN.spatialDeriv CKN.Foundation.Heat.newtonianKernel i (x - y)| ≤ 40 / ρ ^ 2 := by
  have hdist := cutoff_annulus_separation hρ hr hhalf hx hy
  have heuc : spaceEuclideanNorm (x - y) = vec3EuclideanNorm (x - y) := rfl
  have hnorm : ρ / 20 ≤ ‖x - y‖ := by
    have hle := euclideanNorm_le_three_mul_space_norm (x - y)
    rw [heuc] at hle
    nlinarith only [hdist, hle]
  have hne : x - y ≠ 0 := by
    intro hzero
    rw [hzero] at hdist
    simp only [vec3EuclideanNorm_zero] at hdist
    linarith only [hdist, hρ]
  have hbound := CKN.Foundation.Heat.newtonianKernel_spatialDeriv_size_bound hne i
  have hsq : (ρ / 20) ^ 2 ≤ ‖x - y‖ ^ 2 := by
    nlinarith only [hnorm, hρ]
  have hinv : (‖x - y‖ ^ 2)⁻¹ ≤ ((ρ / 20) ^ 2)⁻¹ := by
    exact (inv_le_inv₀ (by positivity) (by positivity)).2 hsq
  have hpi : (4 * Real.pi)⁻¹ * ((ρ / 20) ^ 2)⁻¹ ≤ 40 / ρ ^ 2 := by
    have hπ : 3 < Real.pi := Real.pi_gt_three
    field_simp [hρ.ne']
    nlinarith only [hπ]
  exact hbound.trans ((mul_le_mul_of_nonneg_left hinv (by positivity)).trans hpi)

theorem pressure_newtonian_potential_bound {g : Vec3 → ℝ} {x : Vec3} {K : ℝ}
    (_ : 0 ≤ K) (hg : Integrable g volume)
    (hprod : Integrable
      (fun y => (-CKN.Foundation.Heat.newtonianKernel (x - y)) * g y) volume)
    (hpoint : ∀ y, g y ≠ 0 →
      |CKN.Foundation.Heat.newtonianKernel (x - y)| ≤ K) :
    |pressureNewtonianPotential g x| ≤ K * ∫ y, |g y| := by
  unfold pressureNewtonianPotential
  calc
    |∫ y, (-CKN.Foundation.Heat.newtonianKernel (x - y)) * g y| ≤
        ∫ y, |(-CKN.Foundation.Heat.newtonianKernel (x - y)) * g y| :=
      by simpa only [Real.norm_eq_abs] using
        (MeasureTheory.norm_integral_le_integral_norm
          (fun y => (-CKN.Foundation.Heat.newtonianKernel (x - y)) * g y))
    _ ≤ ∫ y, K * |g y| := by
      have hmono := integral_mono hprod.norm (hg.norm.const_mul K) (fun y => by
        by_cases hgy : g y = 0
        · simp [hgy]
        · simpa only [Real.norm_eq_abs, abs_mul, abs_neg] using
            (mul_le_mul_of_nonneg_right (hpoint y hgy) (abs_nonneg (g y))))
      simpa only [Real.norm_eq_abs, abs_mul, abs_neg] using hmono
    _ = K * ∫ y, |g y| := by rw [integral_const_mul]

theorem pressure_newtonian_derivative_potential_bound {g : Vec3 → ℝ} {x : Vec3}
    {K : ℝ} (_ : 0 ≤ K) (i : Fin 3) (hg : Integrable g volume)
    (hprod : Integrable
      (fun y => CKN.spatialDeriv CKN.Foundation.Heat.newtonianKernel i
        (x - y) * g y) volume)
    (hpoint : ∀ y, g y ≠ 0 →
      |CKN.spatialDeriv CKN.Foundation.Heat.newtonianKernel i (x - y)| ≤ K) :
    |pressureNewtonianDerivativePotential i g x| ≤ K * ∫ y, |g y| := by
  unfold pressureNewtonianDerivativePotential
  calc
    |∫ y, CKN.spatialDeriv CKN.Foundation.Heat.newtonianKernel i
          (x - y) * g y| ≤
        ∫ y, |CKN.spatialDeriv CKN.Foundation.Heat.newtonianKernel i
          (x - y) * g y| :=
      by simpa only [Real.norm_eq_abs] using
        (MeasureTheory.norm_integral_le_integral_norm
          (fun y => CKN.spatialDeriv CKN.Foundation.Heat.newtonianKernel i
            (x - y) * g y))
    _ ≤ ∫ y, K * |g y| := by
      have hmono := integral_mono hprod.norm (hg.norm.const_mul K) (fun y => by
        by_cases hgy : g y = 0
        · simp [hgy]
        · simpa only [Real.norm_eq_abs, abs_mul] using
            (mul_le_mul_of_nonneg_right (hpoint y hgy) (abs_nonneg (g y))))
      simpa only [Real.norm_eq_abs, abs_mul] using hmono
    _ = K * ∫ y, |g y| := by rw [integral_const_mul]

theorem pressure_cylinder_eLpNorm_le {P : Vec3 × ℝ → ℝ} {G : ℝ → ℝ}
    {x₀ : Vec3} {t r q K : ℝ} (_ : 0 < r) (hq : 0 < q) (hK : 0 ≤ K)
    (hGmeas : AEStronglyMeasurable G
      (volume.restrict (Ioc (t - r ^ 2) t)))
    (hpoint : ∀ᵐ z ∂(volume.restrict (parabolicCylinder x₀ t r)),
      ‖P z‖ₑ ≤ ENNReal.ofReal K * ‖G z.2‖ₑ) :
    eLpNorm' P q (volume.restrict (parabolicCylinder x₀ t r)) ≤
      ((ENNReal.ofReal K) ^ q * volume (vec3Ball x₀ r) *
        (∫⁻ s in Ioc (t - r ^ 2) t, ‖G s‖ₑ ^ q)) ^ (1 / q) := by
  let μx : Measure Vec3 := volume.restrict (vec3Ball x₀ r)
  let μt : Measure ℝ := volume.restrict (Ioc (t - r ^ 2) t)
  have hμ : μx.prod μt = volume.restrict (parabolicCylinder x₀ t r) := by
    dsimp [μx, μt, parabolicCylinder]
    exact Measure.prod_restrict _ _
  have hGprodS : AEStronglyMeasurable (fun z : Vec3 × ℝ => G z.2) (μx.prod μt) := by
    exact hGmeas.comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_snd (μ := μx) (ν := μt))
  let H : Vec3 × ℝ → ℝ := fun z => K * G z.2
  have hHprodS : AEStronglyMeasurable H (μx.prod μt) := by
    simpa only [H] using hGprodS.const_mul K
  have hHnorm (z : Vec3 × ℝ) :
      ‖H z‖ₑ = ENNReal.ofReal K * ‖G z.2‖ₑ := by
    dsimp [H]
    rw [← ofReal_norm, norm_mul, Real.norm_eq_abs, abs_of_nonneg hK,
      ENNReal.ofReal_mul hK, ofReal_norm]
  have hpoint' : ∀ᵐ z ∂(μx.prod μt),
      ‖P z‖ₑ ≤ ENNReal.ofReal K * ‖G z.2‖ₑ := by
    rw [hμ]
    exact hpoint
  have hmono : eLpNorm' P q (μx.prod μt) ≤ eLpNorm' H q (μx.prod μt) := by
    have hineq : ∀ᵐ z ∂(μx.prod μt), ‖P z‖ₑ ≤
        (1 : ℝ≥0∞) * ‖H z‖ₑ := by
      filter_upwards [hpoint'] with z hz
      calc
        ‖P z‖ₑ ≤ ENNReal.ofReal K * ‖G z.2‖ₑ := hz
        _ = ‖H z‖ₑ := (hHnorm z).symm
        _ = (1 : ℝ≥0∞) * ‖H z‖ₑ := by rw [one_mul]
    have h := eLpNorm'_le_mul_eLpNorm'_of_ae_le_mul
      (μ := μx.prod μt) (f := P) (g := H) (c := (1 : ℝ≥0∞))
      hHprodS hineq hq
    simpa only [one_mul] using h
  have htime : AEMeasurable (fun s : ℝ => ‖G s‖ₑ ^ q) μt :=
    hGmeas.enorm.pow_const q
  have hlin : (∫⁻ z, ‖H z‖ₑ ^ q ∂(μx.prod μt)) =
      (ENNReal.ofReal K) ^ q * μx Set.univ *
        (∫⁻ s, ‖G s‖ₑ ^ q ∂μt) := by
    calc
      (∫⁻ z, ‖H z‖ₑ ^ q ∂(μx.prod μt)) =
          ∫⁻ z, (ENNReal.ofReal K) ^ q *
            (‖G z.2‖ₑ ^ q) ∂(μx.prod μt) := by
        apply lintegral_congr_ae
        filter_upwards [] with z
        rw [hHnorm z, ENNReal.mul_rpow_of_nonneg _ _ hq.le]
      _ = (∫⁻ x, (ENNReal.ofReal K) ^ q ∂μx) *
          (∫⁻ s, ‖G s‖ₑ ^ q ∂μt) :=
        MeasureTheory.lintegral_prod_mul measurable_const.aemeasurable htime
      _ = (ENNReal.ofReal K) ^ q * μx Set.univ *
          (∫⁻ s, ‖G s‖ₑ ^ q ∂μt) := by
        rw [lintegral_const]
  calc
    eLpNorm' P q (volume.restrict (parabolicCylinder x₀ t r)) =
        eLpNorm' P q (μx.prod μt) := by
      exact congrArg (fun m : Measure (Vec3 × ℝ) => eLpNorm' P q m) hμ.symm
    _ ≤ eLpNorm' H q (μx.prod μt) := hmono
    _ = (∫⁻ z, ‖H z‖ₑ ^ q ∂(μx.prod μt)) ^ (1 / q) :=
      eLpNorm'_eq_lintegral_enorm H q (μx.prod μt)
    _ = ((ENNReal.ofReal K) ^ q * volume (vec3Ball x₀ r) *
        (∫⁻ s in Ioc (t - r ^ 2) t, ‖G s‖ₑ ^ q)) ^ (1 / q) := by
      rw [hlin]
      simp [μx, μt]

/-- Euclidean tensor norm of the partially centered pressure source. -/
@[expose]
def pressureUTensorNorm (u : ParabolicPoint → Vec3) (c : ℝ → Vec3)
    (s : ℝ) (y : Vec3) : ℝ :=
  Real.sqrt (∑ i : Fin 3, ∑ j : Fin 3,
    (pressureUTensor u c (y, s) i j) ^ (2 : ℕ))

theorem pressure_component_abs_le_utensorNorm
    (u : ParabolicPoint → Vec3) (c : ℝ → Vec3) (s : ℝ)
    (y : Vec3) (i j : Fin 3) :
    |pressureUTensor u c (y, s) i j| ≤ pressureUTensorNorm u c s y := by
  unfold pressureUTensorNorm
  apply Real.abs_le_sqrt
  have hrow : ∑ l : Fin 3, (pressureUTensor u c (y, s) i l) ^ (2 : ℕ) ≤
        ∑ k : Fin 3, ∑ l : Fin 3, (pressureUTensor u c (y, s) k l) ^ (2 : ℕ) :=
      Finset.single_le_sum (fun k _ => Finset.sum_nonneg fun l _ =>
        sq_nonneg (pressureUTensor u c (y, s) k l)) (Finset.mem_univ i)
  exact (Finset.single_le_sum (fun l _ => sq_nonneg
    (pressureUTensor u c (y, s) i l)) (Finset.mem_univ j)).trans hrow

end CKN
