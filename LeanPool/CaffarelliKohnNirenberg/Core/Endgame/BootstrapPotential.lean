/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.PotentialFiniteness
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PointwisePotential
public import LeanPool.CaffarelliKohnNirenberg.Core.HeatPotential.FarShell

/-! # Almost-everywhere pointwise bounds for the localized heat potential

Finite extended-real Riesz potentials give integrable real majorants at almost
every evaluation point. All conversions to real numbers are made only after
this finiteness has been established.
-/

public section

open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Core.HeatPotential CKN.Core.Step3 CKN.Core.Step4

noncomputable section
namespace CKN.Core.Endgame

/-- Componentwise almost-everywhere measurability supplies measurability of
the Euclidean norm used as the nonnegative potential source. -/
theorem aemeasurable_euclidean_norm_of_components
    {g : ParabolicPoint → Vec3}
    (hg : ∀ i, AEMeasurable (fun w => g w i) volume) :
    AEMeasurable (fun w => vec3EuclideanNorm (g w)) volume := by
  have hcont : Continuous (fun x : Vec3 => vec3EuclideanNorm x) := by
    unfold vec3EuclideanNorm
    fun_prop
  exact hcont.measurable.comp_aemeasurable (aemeasurable_pi_iff.mpr hg)

private theorem scalar_integral_le_finite_riesz
    {β C : ℝ} {z : ParabolicPoint} {K f N : ParabolicPoint → ℝ}
    (hC : 0 ≤ C) (hK : Measurable K) (hf : AEMeasurable f volume)
    (hN : AEMeasurable N volume) (hN0 : ∀ w, 0 ≤ N w) (hfN : ∀ w, |f w| ≤ N w)
    (hbound : ∀ w, |K w| ≤ C * (parabolicRieszKernel β z w).toReal)
    (hfinite : parabolicRieszPotential β N z < ∞) :
    |∫ w, K w * f w| ≤ C * (parabolicRieszPotential β N z).toReal := by
  let A : ParabolicPoint → ℝ≥0∞ := fun w =>
    parabolicRieszKernel β z w * ENNReal.ofReal |N w|
  have hA : AEMeasurable A volume := by
    exact (((measurable_parabolicRho₂ z).ennreal_ofReal).pow_const _).aemeasurable.mul
      (continuous_abs.measurable.comp_aemeasurable hN).ennreal_ofReal
  have hAfin : (∫⁻ w, A w) ≠ ∞ := hfinite.ne
  have hAint := integrable_toReal_of_lintegral_ne_top hA hAfin
  have hAeq : ∀ w, (A w).toReal = (parabolicRieszKernel β z w).toReal * N w := by
    intro w
    change (parabolicRieszKernel β z w * ENNReal.ofReal |N w|).toReal = _
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _), abs_of_nonneg (hN0 w)]
  have hdom : ∀ w, |K w * f w| ≤ C * (A w).toReal := by
    intro w
    rw [abs_mul, hAeq]
    calc
      |K w| * |f w| ≤ (C * (parabolicRieszKernel β z w).toReal) * N w :=
        mul_le_mul (hbound w) (hfN w) (abs_nonneg _) (mul_nonneg hC ENNReal.toReal_nonneg)
      _ = C * ((parabolicRieszKernel β z w).toReal * N w) := by ring
  have hKf : Integrable (fun w => K w * f w) volume :=
    (hAint.const_mul C).mono' (hK.aemeasurable.mul hf).aestronglyMeasurable
      (Filter.Eventually.of_forall fun w => by simpa only [Real.norm_eq_abs] using hdom w)
  have hmono := integral_mono_ae hKf.norm (hAint.const_mul C)
    (Filter.Eventually.of_forall fun w => by simpa only [Real.norm_eq_abs] using hdom w)
  have hAe : (∫ w, (A w).toReal) = (parabolicRieszPotential β N z).toReal :=
    integral_toReal hA (ae_lt_top' hA hAfin)
  calc
    |∫ w, K w * f w| ≤ ∫ w, |K w * f w| := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (μ := volume) (fun w => K w * f w)
    _ ≤ ∫ w, C * (A w).toReal := hmono
    _ = C * (parabolicRieszPotential β N z).toReal := by
      rw [integral_const_mul, hAe]

private theorem component_le_euclidean_norm (v : Vec3) (i : Fin 3) :
    |v i| ≤ vec3EuclideanNorm v := by
  unfold vec3EuclideanNorm
  exact Real.abs_le_sqrt
    (Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i))

private theorem euclidean_norm_le_sum (v : Vec3) : vec3EuclideanNorm v ≤ ∑ i, |v i| := by
  rw [vec3EuclideanNorm]
  apply Real.sqrt_le_iff.mpr
  constructor
  · exact Finset.sum_nonneg fun i _ => abs_nonneg _
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change v 0 ^ 2 + (v 1 ^ 2 + v 2 ^ 2) ≤
      (|v 0| + (|v 1| + |v 2|)) ^ 2
    nlinarith only [sq_abs (v 0), sq_abs (v 1), sq_abs (v 2),
      mul_nonneg (abs_nonneg (v 0)) (abs_nonneg (v 1)),
      mul_nonneg (abs_nonneg (v 0)) (abs_nonneg (v 2)),
      mul_nonneg (abs_nonneg (v 1)) (abs_nonneg (v 2))]

/-- At every point where the norm-source Riesz potentials are finite, the
actual Duhamel integral is bounded by its pointwise potential majorant. -/
theorem duhamel_bound_of_finite_riesz
    {g : ParabolicPoint → Vec3} {h : Fin 3 → ParabolicPoint → Vec3}
    (hg : ∀ i, AEMeasurable (fun w => g w i) volume)
    (hh : ∀ j i, AEMeasurable (fun w => h j w i) volume)
    (hgn : AEMeasurable (fun w => vec3EuclideanNorm (g w)) volume)
    (hhn : ∀ j, AEMeasurable (fun w => vec3EuclideanNorm (h j w)) volume)
    {z : ParabolicPoint}
    (hgfin : parabolicRieszPotential 2 (fun w => vec3EuclideanNorm (g w)) z < ∞)
    (hhfin : ∀ j, parabolicRieszPotential 1 (fun w => vec3EuclideanNorm (h j w)) z < ∞) :
    vec3EuclideanNorm (duhamelPotential g h z) ≤ pointwisePotentialMajorant g h z := by
  have hgb : ∀ i, |∫ w, heatPotentialKernel z w * g w i| ≤
      1000 * (parabolicRieszPotential 2 (fun w => vec3EuclideanNorm (g w)) z).toReal := by
    intro i
    exact scalar_integral_le_finite_riesz (by norm_num)
      (measurable_heatPotentialKernel_translate z) (hg i) hgn
      (fun _ => vec3EuclideanNorm_nonneg _) (fun _ => component_le_euclidean_norm _ i)
      (CKN.Core.Step4.heatPotentialKernel_abs_le_riesz₂ z) hgfin
  have hhb : ∀ j i, |∫ w, heatPotentialSpatialKernel j z w * h j w i| ≤
      300000 * (parabolicRieszPotential 1 (fun w => vec3EuclideanNorm (h j w)) z).toReal := by
    intro j i
    exact scalar_integral_le_finite_riesz (by norm_num)
      (measurable_heatPotentialSpatialKernel_translate j z) (hh j i) (hhn j)
      (fun _ => vec3EuclideanNorm_nonneg _) (fun _ => component_le_euclidean_norm _ i)
      (CKN.Core.Step4.heatPotentialSpatialKernel_abs_le_riesz₁ j z) (hhfin j)
  have hcoord : ∀ i, |duhamelPotential g h z i| ≤
      1000 * (parabolicRieszPotential 2 (fun w => vec3EuclideanNorm (g w)) z).toReal +
        ∑ j, 300000 * (parabolicRieszPotential 1 (fun w => vec3EuclideanNorm (h j w)) z).toReal :=
          by
    intro i
    unfold duhamelPotential
    calc
      _ ≤ |∫ w, heatPotentialKernel z w * g w i| +
          |∑ j, ∫ w, heatPotentialSpatialKernel j z w * h j w i| := abs_sub _ _
      _ ≤ |∫ w, heatPotentialKernel z w * g w i| +
          ∑ j, |∫ w, heatPotentialSpatialKernel j z w * h j w i| :=
        add_le_add_right (Finset.abs_sum_le_sum_abs _ _) _
      _ ≤ _ := add_le_add (hgb i) (Finset.sum_le_sum fun j _ => hhb j i)
  calc
    _ ≤ ∑ i, |duhamelPotential g h z i| := euclidean_norm_le_sum _
    _ ≤ ∑ _i : Fin 3,
        (1000 * (parabolicRieszPotential 2 (fun w => vec3EuclideanNorm (g w)) z).toReal +
          ∑ j, 300000 * (parabolicRieszPotential 1 (fun w => vec3EuclideanNorm (h j w)) z).toReal)
            :=
      Finset.sum_le_sum fun i _ => hcoord i
    _ = pointwisePotentialMajorant g h z := by
      simp only [pointwisePotentialMajorant, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
      ring

/-- Almost-everywhere potential finiteness suffices; there is no all-point
integrability premise on the heat or Riesz convolutions. -/
theorem pointwisePotentialBound_ae
    {v g : ParabolicPoint → Vec3} {h : Fin 3 → ParabolicPoint → Vec3}
    (hg : ∀ i, AEMeasurable (fun w => g w i) volume)
    (hh : ∀ j i, AEMeasurable (fun w => h j w i) volume)
    (hgn : AEMeasurable (fun w => vec3EuclideanNorm (g w)) volume)
    (hhn : ∀ j, AEMeasurable (fun w => vec3EuclideanNorm (h j w)) volume)
    (hgfin : ∀ᵐ z, parabolicRieszPotential 2 (fun w => vec3EuclideanNorm (g w)) z < ∞)
    (hhfin : ∀ j, ∀ᵐ z, parabolicRieszPotential 1 (fun w => vec3EuclideanNorm (h j w)) z < ∞)
    (hrep : v =ᵐ[volume] duhamelPotential g h) :
    ∀ᵐ z, vec3EuclideanNorm (v z) ≤ pointwisePotentialMajorant g h z := by
  filter_upwards [hrep, hgfin, ae_all_iff.mpr hhfin] with z hz hgz hhz
  rw [hz]
  exact duhamel_bound_of_finite_riesz hg hh hgn hhn hgz hhz

/-- Boundedly supported sources at the first bootstrap exponents supply the
almost-everywhere finiteness required by the pointwise potential estimate. -/
theorem pointwisePotentialBound_ae_of_bootstrap_sources
    {v g : ParabolicPoint → Vec3} {h : Fin 3 → ParabolicPoint → Vec3}
    {z₀ : ParabolicPoint} {R : ℝ} (hR : 0 < R)
    (hg : ∀ i, AEMeasurable (fun w => g w i) volume)
    (hh : ∀ j i, AEMeasurable (fun w => h j w i) volume)
    (hgn : AEMeasurable (fun w => vec3EuclideanNorm (g w)) volume)
    (hhn : ∀ j, AEMeasurable (fun w => vec3EuclideanNorm (h j w)) volume)
    (hgN : morreyNorm (6 / 5) (25 / 11) (fun w => vec3EuclideanNorm (g w)) < ∞)
    (hhN : ∀ j, morreyNorm 3 (25 / 6) (fun w => vec3EuclideanNorm (h j w)) < ∞)
    (hgsupp : ∀ w ∉ parabolicCylinder z₀.1 z₀.2 R, g w = 0)
    (hhsupp : ∀ j w, w ∉ parabolicCylinder z₀.1 z₀.2 R → h j w = 0)
    (hrep : v =ᵐ[volume] duhamelPotential g h) :
    ∀ᵐ z, vec3EuclideanNorm (v z) ≤ pointwisePotentialMajorant g h z := by
  apply pointwisePotentialBound_ae hg hh hgn hhn _ _ hrep
  · apply riesz_potential_ae_lt_top_of_aemeasurable_morrey (β := 2) (P := 6 / 5) (τ := 25 / 11)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hR hgn hgN
    on_goal 1 => intro w hw
    rw [hgsupp w hw, vec3EuclideanNorm_zero]
  · intro j
    apply riesz_potential_ae_lt_top_of_aemeasurable_morrey (β := 1) (P := 3) (τ := 25 / 6)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hR (hhn j) (hhN j)
    on_goal 1 => intro w hw
    rw [hhsupp j w hw, vec3EuclideanNorm_zero]

end CKN.Core.Endgame
