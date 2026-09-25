/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.EuclideanWspSmoothDual
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.ContinuousInterpolation.UnitCubeGeometry
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.MeasureTheory.Constructions.HaarToSphere

/-!
# Fractional Sobolev membership of smooth cube tests

The only analytic input in this file is the local integrability of a radial
power kernel with positive gain over the dimension.  It is then applied to the
Lipschitz bound supplied by global smoothness on the bounded cube.
-/

@[expose] public section

namespace Homogenization

open MeasureTheory Metric
open scoped ENNReal

noncomputable section

private noncomputable def smoothWspPowerKernel {d : ℕ} (a : ℝ)
    (x y : Vec d) : ℝ :=
  ‖x - y‖ ^ (a - (d : ℝ))

private theorem smoothWspPowerKernel_integrableOn_ball {d : ℕ} [NeZero d]
    {a R : ℝ} (ha : 0 < a) (hR : 0 < R) :
    IntegrableOn (fun x : Vec d => ‖x‖ ^ (a - (d : ℝ)))
      (Metric.ball (0 : Vec d) R) volume := by
  let g : ℝ → ℝ := fun r => if r < R then r ^ (a - (d : ℝ)) else 0
  have hag :
      (fun x : Vec d => ‖x‖ ^ (a - (d : ℝ))) =ᵐ[
          volume.restrict (Metric.ball (0 : Vec d) R)]
        (g ∘ (‖·‖)) := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    simp only [Function.comp_apply, g, mem_ball, dist_zero_right] at hx ⊢
    rw [if_pos hx]
  rw [IntegrableOn, integrable_congr hag]
  suffices h : Integrable (fun x : Vec d => g ‖x‖) volume from h.integrableOn
  have hradial :
      IntegrableOn
        (fun r : ℝ => r ^ (Module.finrank ℝ (Vec d) - 1) • g r)
        (Set.Ioi 0) := by
    have hfin : Module.finrank ℝ (Vec d) = d := by simp [Vec]
    let hInd : ℝ → ℝ :=
      (Set.Ioo (0 : ℝ) R).indicator (fun r => r ^ (a - 1))
    have heq : Set.EqOn
        (fun r : ℝ => r ^ (Module.finrank ℝ (Vec d) - 1) • g r)
        hInd (Set.Ioi 0) := by
      intro r hr
      have hrpos : 0 < r := hr
      simp only [g, hInd, smul_eq_mul, Set.indicator, Set.mem_Ioo]
      by_cases hrR : r < R
      · rw [if_pos hrR, if_pos ⟨hrpos, hrR⟩, hfin,
          ← Real.rpow_natCast r (d - 1),
          Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)),
          ← Real.rpow_add hrpos]
        congr 1
        ring
      · rw [if_neg hrR, if_neg (not_and_of_not_right _ hrR), mul_zero]
    have hInd_int : IntegrableOn hInd (Set.Ioi 0) := by
      have hwhole : Integrable hInd volume := by
        dsimp [hInd]
        exact ((intervalIntegral.integrableOn_Ioo_rpow_iff hR).mpr (by linarith)).integrable_indicator
          measurableSet_Ioo
      exact hwhole.mono_measure Measure.restrict_le_self
    exact hInd_int.congr_fun heq.symm measurableSet_Ioi
  exact (integrable_fun_norm_addHaar (μ := volume) (f := g)).mpr hradial

private theorem smoothWspPowerKernel_integrableOn_translated_ball {d : ℕ} [NeZero d]
    {a R : ℝ} (ha : 0 < a) (hR : 0 < R) (x : Vec d)
    (hx : x ∈ Metric.ball (0 : Vec d) R) :
    IntegrableOn (fun y : Vec d => smoothWspPowerKernel a x y)
      (Metric.ball (0 : Vec d) R) volume := by
  have hsub : Metric.ball (0 : Vec d) R ⊆ Metric.ball x (2 * R) := by
    intro y hy
    rw [mem_ball, dist_eq_norm] at hy ⊢
    have hxnorm : ‖x‖ < R := by simpa [mem_ball, dist_zero_right] using hx
    have hynorm : ‖y‖ < R := by simpa using hy
    calc
      ‖y - x‖ ≤ ‖y‖ + ‖x‖ := norm_sub_le _ _
      _ < R + R := add_lt_add hynorm hxnorm
      _ = 2 * R := by ring
  have hmp := MeasureTheory.measurePreserving_add_right (volume : Measure (Vec d)) x
  have hemb := (MeasurableEquiv.addRight x : Vec d ≃ᵐ Vec d).measurableEmbedding
  have hpre :
      (· + x) ⁻¹' Metric.ball x (2 * R) = Metric.ball (0 : Vec d) (2 * R) := by
    ext z
    simp [mem_ball]
  have hbig :
      IntegrableOn (fun y : Vec d => smoothWspPowerKernel a x y)
        (Metric.ball x (2 * R)) volume := by
    rw [← hmp.integrableOn_comp_preimage hemb, hpre]
    exact (smoothWspPowerKernel_integrableOn_ball (d := d) ha
      (by linarith : 0 < 2 * R)).congr
      (Filter.Eventually.of_forall fun z => by
        unfold smoothWspPowerKernel
        show ‖z‖ ^ (a - (d : ℝ)) = ‖x - (z + x)‖ ^ (a - (d : ℝ))
        simp)
  exact hbig.mono_set hsub

private theorem smoothWspPowerKernel_integrable_gagliardoCubeMeasure {d : ℕ} [NeZero d]
    (Q : TriadicCube d) {a : ℝ} (ha : 0 < a) :
    Integrable (fun z : Vec d × Vec d => smoothWspPowerKernel a z.1 z.2)
      (Gagliardo.gagliardoCubeMeasure Q) := by
  let U := cubeSet Q
  let μ := cubeMeasure Q
  let hUbd : IsBoundedDomain U :=
    Bornology.IsBounded.isBoundedDomain (Homogenization.isBounded_cubeSet Q)
  let C : ℝ := Classical.choose hUbd
  have hC : 0 < C := (Classical.choose_spec hUbd).1
  have hU_meas : MeasurableSet U := measurableSet_cubeSet Q
  let : IsFiniteMeasure μ := by
    simpa only [μ, cubeMeasure, U] using hUbd.isFiniteMeasure_restrict_volume
  let : SFinite μ := inferInstance
  have hsub : U ⊆ Metric.ball (0 : Vec d) (2 * C) := by
    intro x hx
    rw [mem_ball, dist_zero_right]
    exact hUbd.norm_le_choose hx |>.trans_lt (by linarith)
  have hradial : Integrable (fun z : Vec d => ‖z‖ ^ (a - (d : ℝ)))
      (volume.restrict (Metric.ball (0 : Vec d) (4 * C))) := by
    simpa only [IntegrableOn] using smoothWspPowerKernel_integrableOn_ball (d := d)
      ha (by linarith : 0 < 4 * C)
  let B : ℝ := ∫ z in Metric.ball (0 : Vec d) (4 * C), ‖z‖ ^ (a - (d : ℝ))
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact setIntegral_nonneg measurableSet_ball fun z _ => Real.rpow_nonneg (norm_nonneg _) _
  have hkernel_meas : Measurable (fun z : Vec d × Vec d =>
      smoothWspPowerKernel a z.1 z.2) := by
    unfold smoothWspPowerKernel
    fun_prop
  have hsections : ∀ᵐ y ∂μ, Integrable
      (fun x : Vec d => smoothWspPowerKernel a x y) μ := by
    change ∀ᵐ y ∂volume.restrict U, Integrable
      (fun x : Vec d => smoothWspPowerKernel a x y) μ
    filter_upwards [ae_restrict_mem hU_meas] with y hy
    have hyball : y ∈ Metric.ball (0 : Vec d) (2 * C) := hsub hy
    have hlarge : IntegrableOn (fun x : Vec d => smoothWspPowerKernel a x y)
        (Metric.ball (0 : Vec d) (2 * C)) volume := by
      simpa only [smoothWspPowerKernel, norm_sub_rev] using
        smoothWspPowerKernel_integrableOn_translated_ball (d := d) ha
          (by linarith : 0 < 2 * C) y hyball
    simpa only [μ, cubeMeasure, IntegrableOn] using hlarge.mono_set hsub
  have houter_meas : AEStronglyMeasurable
      (fun y : Vec d => ∫ x, ‖smoothWspPowerKernel a x y‖ ∂μ) μ := by
    have hswap : Measurable (fun z : Vec d × Vec d =>
        ‖smoothWspPowerKernel a z.2 z.1‖) := by
      simpa only [smoothWspPowerKernel, norm_sub_rev] using hkernel_meas.norm
    exact hswap.aemeasurable.aestronglyMeasurable.integral_prod_right'
  have houter_bound : ∀ᵐ y ∂μ,
      ‖∫ x, ‖smoothWspPowerKernel a x y‖ ∂μ‖ ≤ B := by
    change ∀ᵐ y ∂volume.restrict U,
      ‖∫ x, ‖smoothWspPowerKernel a x y‖ ∂μ‖ ≤ B
    filter_upwards [ae_restrict_mem hU_meas] with y hy
    have hyball : y ∈ Metric.ball (0 : Vec d) (2 * C) := hsub hy
    have hlarge : IntegrableOn (fun x : Vec d => smoothWspPowerKernel a x y)
        (Metric.ball (0 : Vec d) (2 * C)) volume := by
      simpa only [smoothWspPowerKernel, norm_sub_rev] using
        smoothWspPowerKernel_integrableOn_translated_ball (d := d) ha
          (by linarith : 0 < 2 * C) y hyball
    have hlarge' : Integrable (fun x : Vec d => smoothWspPowerKernel a x y)
        (volume.restrict (Metric.ball (0 : Vec d) (2 * C))) := hlarge
    have hbig : IntegrableOn (fun x : Vec d => smoothWspPowerKernel a x y)
        (Metric.ball y (4 * C)) volume := by
      have hmp := MeasureTheory.measurePreserving_add_right (volume : Measure (Vec d)) y
      have hemb := (MeasurableEquiv.addRight y : Vec d ≃ᵐ Vec d).measurableEmbedding
      have hpre :
          (· + y) ⁻¹' Metric.ball y (4 * C) = Metric.ball (0 : Vec d) (4 * C) := by
        ext z
        simp [mem_ball]
      rw [← hmp.integrableOn_comp_preimage hemb, hpre]
      exact hradial.congr (Filter.Eventually.of_forall fun z => by
        unfold smoothWspPowerKernel
        simp)
    have htrans :
        ∫ x in Metric.ball (0 : Vec d) (2 * C), smoothWspPowerKernel a x y ≤ B := by
      have hmp := MeasureTheory.measurePreserving_add_right (volume : Measure (Vec d)) y
      have hemb := (MeasurableEquiv.addRight y : Vec d ≃ᵐ Vec d).measurableEmbedding
      have hpre :
          (· + y) ⁻¹' Metric.ball y (4 * C) = Metric.ball (0 : Vec d) (4 * C) := by
        ext z
        simp [mem_ball]
      have hmove :
          ∫ x in Metric.ball y (4 * C), smoothWspPowerKernel a x y = B := by
        rw [← hmp.setIntegral_preimage_emb hemb, hpre]
        dsimp [B]
        congr 1 with z
        unfold smoothWspPowerKernel
        simp
      have hsubball : Metric.ball (0 : Vec d) (2 * C) ⊆ Metric.ball y (4 * C) := by
        intro x hx
        rw [mem_ball, dist_eq_norm] at hx ⊢
        have hynorm : ‖y‖ < 2 * C := by simpa [mem_ball, dist_zero_right] using hyball
        calc
          ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le _ _
          _ < 2 * C + 2 * C := add_lt_add (by simpa [mem_ball, dist_zero_right] using hx) hynorm
          _ = 4 * C := by ring
      exact (setIntegral_mono_set hbig
        (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (norm_nonneg _) _)
        hsubball.eventuallyLE).trans_eq hmove
    have hnonneg : 0 ≤ ∫ x, ‖smoothWspPowerKernel a x y‖ ∂μ :=
      integral_nonneg fun x => norm_nonneg _
    rw [Real.norm_of_nonneg hnonneg]
    calc
      ∫ x, ‖smoothWspPowerKernel a x y‖ ∂μ =
          ∫ x in U, smoothWspPowerKernel a x y := by
            apply integral_congr_ae
            filter_upwards with x
            exact Real.norm_of_nonneg (by
              unfold smoothWspPowerKernel
              exact Real.rpow_nonneg (norm_nonneg _) _)
      _ ≤ ∫ x in Metric.ball (0 : Vec d) (2 * C), smoothWspPowerKernel a x y := by
            exact setIntegral_mono_set hlarge
              (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (norm_nonneg _) _) hsub.eventuallyLE
      _ ≤ B := htrans
  have houter_int : Integrable (fun _ : Vec d => B) μ := integrable_const B
  have hnorm_int : Integrable (fun y => ∫ x, ‖smoothWspPowerKernel a x y‖ ∂μ) μ :=
    houter_int.mono' houter_meas houter_bound
  have hprod : Integrable (fun z : Vec d × Vec d => smoothWspPowerKernel a z.1 z.2)
      (μ.prod μ) :=
    (integrable_prod_iff' hkernel_meas.aestronglyMeasurable).2 ⟨hsections, hnorm_int⟩
  rw [Gagliardo.gagliardoCubeMeasure, normalizedCubeMeasure, Measure.prod_smul_left]
  exact hprod.smul_measure ENNReal.ofReal_ne_top

private noncomputable def smoothWspLpMajorant {d : ℕ}
    (s : FractionalOrder) (p : FiniteLpExponent) : Vec d × Vec d → ℝ :=
  fun z => ‖z.1 - z.2‖ ^ (1 - s.1 - (d : ℝ) / p.exponent.toReal)

private theorem memLp_smoothWspLpMajorant {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (s : FractionalOrder) (p : FiniteLpExponent) :
    MemLp (smoothWspLpMajorant s p) p.exponent
      (Gagliardo.gagliardoCubeMeasure Q) := by
  have hp : 0 < p.exponent.toReal :=
    ENNReal.toReal_pos (ne_of_gt (lt_trans zero_lt_one p.one_lt)) p.lt_top.ne
  have hmeas : Measurable (smoothWspLpMajorant (d := d) s p) := by
    unfold smoothWspLpMajorant
    fun_prop
  rw [← integrable_norm_rpow_iff hmeas.aestronglyMeasurable
    (ne_of_gt (lt_trans zero_lt_one p.one_lt)) p.lt_top.ne]
  convert smoothWspPowerKernel_integrable_gagliardoCubeMeasure Q
    (a := p.exponent.toReal * (1 - s.1)) (mul_pos hp (sub_pos.mpr s.2.2)) using 1
  ext z
  simp only [smoothWspLpMajorant, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  rw [← Real.rpow_mul (norm_nonneg _)]
  congr 1
  field_simp [hp.ne']

private theorem convex_cubeSet_for_smoothMembership {d : ℕ} (Q : TriadicCube d) :
    Convex ℝ (cubeSet Q) := by
  rw [cubeSet_eq_pi_Ico]
  refine convex_pi ?_
  intro i hi
  exact convex_Ico _ _

private theorem smoothTest_euclideanNorm_sub_le_lipschitz {d : ℕ} [NeZero d]
    (Q : TriadicCube d) {s : FractionalOrder} {p : FiniteLpExponent}
    (h : CubeEuclideanWspSmoothTest Q s p) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x ∈ cubeSet Q, ∀ y ∈ cubeSet Q,
      euclideanNorm (h.toField x - h.toField y) ≤ L * ‖x - y‖ := by
  have hderiv_cont : Continuous (fderiv ℝ h.toField) :=
    h.contDiff.continuous_fderiv (by norm_num)
  have hcompact : IsCompact (closure (cubeSet Q)) :=
    (isBounded_cubeSet Q).isCompact_closure
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn hderiv_cont.norm.continuousOn
  let L := max C 0
  have hL : 0 ≤ L := le_max_right _ _
  refine ⟨(d : ℝ) * L, mul_nonneg (Nat.cast_nonneg _) hL, ?_⟩
  intro x hx y hy
  have hderiv_bound : ∀ z ∈ cubeSet Q, ‖fderiv ℝ h.toField z‖ ≤ L := by
    intro z hz
    simpa only [L, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using
      (hC z (subset_closure hz)).trans (le_max_left C 0)
  have hambient : ‖h.toField x - h.toField y‖ ≤ L * ‖x - y‖ := by
    simpa [mul_comm] using
      (Convex.norm_image_sub_le_of_norm_fderiv_le
        (𝕜 := ℝ) (f := h.toField) (s := cubeSet Q) (C := L) (x := y) (y := x)
        (fun z _ => h.contDiff.differentiable (by norm_num) z)
        (fun z hz => hderiv_bound z hz)
        (convex_cubeSet_for_smoothMembership Q) hy hx)
  calc
    euclideanNorm (h.toField x - h.toField y) ≤
        (d : ℝ) * ‖h.toField x - h.toField y‖ :=
      euclideanNorm_le_dimension_mul_norm _
    _ ≤ (d : ℝ) * (L * ‖x - y‖) :=
      mul_le_mul_of_nonneg_left hambient (Nat.cast_nonneg _)
    _ = ((d : ℝ) * L) * ‖x - y‖ := by ring

private theorem smoothTest_kernel_norm_le_lipschitz_majorant {d : ℕ} [NeZero d]
    (Q : TriadicCube d) {s : FractionalOrder} {p : FiniteLpExponent}
    (h : CubeEuclideanWspSmoothTest Q s p) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x ∈ cubeSet Q, ∀ y ∈ cubeSet Q,
      ‖cubeEuclideanWspKernel s p h.toField (x, y)‖ ≤
        L * smoothWspLpMajorant s p (x, y) := by
  obtain ⟨L, hL, hLip⟩ := smoothTest_euclideanNorm_sub_le_lipschitz Q h
  refine ⟨L, hL, ?_⟩
  intro x hx y hy
  let b : ℝ := s.1 + (d : ℝ) / p.exponent.toReal
  have hb : 0 < b := add_pos_of_pos_of_nonneg s.2.1
    (div_nonneg (Nat.cast_nonneg _) ENNReal.toReal_nonneg)
  by_cases hxy : x = y
  · subst y
    rw [norm_cubeEuclideanWspKernel]
    simp only [sub_self, euclideanNorm_zero, mul_zero]
    exact mul_nonneg hL (Real.rpow_nonneg (norm_nonneg _) _)
  · have hsub : x - y ≠ 0 := sub_ne_zero.mpr hxy
    have hdist : 0 < ‖x - y‖ := norm_pos_iff.mpr hsub
    have hpow : euclideanDist x y ^ (-b) ≤ ‖x - y‖ ^ (-b) := by
      exact Real.rpow_le_rpow_of_nonpos hdist (dist_le_euclideanDist x y)
        (neg_nonpos.mpr hb.le)
    rw [norm_cubeEuclideanWspKernel]
    have hfirst :
        euclideanDist x y ^ (-b) * euclideanNorm (h.toField x - h.toField y) ≤
          euclideanDist x y ^ (-b) * (L * ‖x - y‖) :=
      mul_le_mul_of_nonneg_left (hLip x hx y hy)
        (Real.rpow_nonneg (euclideanDist_nonneg _ _) _)
    calc
      euclideanDist x y ^ (-(s.1 + (d : ℝ) / p.exponent.toReal)) *
          euclideanNorm (h.toField x - h.toField y) =
          euclideanDist x y ^ (-b) * euclideanNorm (h.toField x - h.toField y) := by rfl
      _ ≤ euclideanDist x y ^ (-b) * (L * ‖x - y‖) := hfirst
      _ ≤ ‖x - y‖ ^ (-b) * (L * ‖x - y‖) :=
        mul_le_mul_of_nonneg_right hpow (mul_nonneg hL hdist.le)
      _ = L * ‖x - y‖ ^ (1 - s.1 - (d : ℝ) / p.exponent.toReal) := by
        calc
          ‖x - y‖ ^ (-b) * (L * ‖x - y‖) =
              L * (‖x - y‖ ^ (-b) * ‖x - y‖) := by ring
          _ = L * (‖x - y‖ ^ (-b) * ‖x - y‖ ^ (1 : ℝ)) := by
            rw [Real.rpow_one]
          _ = L * ‖x - y‖ ^ (-b + 1) := by rw [← Real.rpow_add hdist]
          _ = L * ‖x - y‖ ^ (1 - s.1 - (d : ℝ) / p.exponent.toReal) := by
            congr 2
            dsimp [b]
            ring

private theorem gagliardoCubeMeasure_diagonal_eq_zero {d : ℕ} [NeZero d]
    (Q : TriadicCube d) :
    Gagliardo.gagliardoCubeMeasure Q (Set.diagonal (Vec d)) = 0 := by
  let : IsFiniteMeasure (cubeMeasure Q) :=
    ⟨lt_top_iff_ne_top.mpr (cubeMeasure_apply_univ_ne_top Q)⟩
  rw [Gagliardo.gagliardoCubeMeasure]
  apply Measure.measure_prod_null isClosed_diagonal.measurableSet |>.mpr
  filter_upwards with x
  have hpre : Prod.mk x ⁻¹' Set.diagonal (Vec d) = {x} := by
    ext y
    simp [Set.mem_diagonal_iff, eq_comm]
  rw [hpre]
  simp [cubeMeasure]

private theorem continuousOn_cubeEuclideanWspKernel_offDiagonal {d : ℕ}
    {Q : TriadicCube d} {s : FractionalOrder} {p : FiniteLpExponent}
    (h : CubeEuclideanWspSmoothTest Q s p) :
    ContinuousOn (cubeEuclideanWspKernel s p h.toField)
      (Set.diagonal (Vec d))ᶜ := by
  have hdist : Continuous (fun z : Vec d × Vec d => euclideanDist z.1 z.2) := by
    have hh : Continuous (fun z : Vec d × Vec d => HilbertVec.ofVec (z.1 - z.2)) :=
      (HilbertVec.ofVecL d).continuous.comp (continuous_fst.sub continuous_snd)
    simpa only [euclideanDist, euclideanNorm_eq_norm_ofVec] using hh.norm
  have hfield : Continuous (fun z : Vec d × Vec d =>
      HilbertVec.ofVec (h.toField z.1 - h.toField z.2)) :=
    (HilbertVec.ofVecL d).continuous.comp
      ((h.contDiff.continuous.comp continuous_fst).sub
        (h.contDiff.continuous.comp continuous_snd))
  unfold cubeEuclideanWspKernel
  exact (hdist.continuousOn.rpow_const fun z hz => Or.inl (by
    intro hzero
    apply hz
    exact Set.mem_diagonal_iff.mpr (euclideanDist_eq_zero_iff.mp hzero))).smul
      hfield.continuousOn

private theorem aestronglyMeasurable_cubeEuclideanWspKernel_of_smoothTest
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {s : FractionalOrder}
    {p : FiniteLpExponent} (h : CubeEuclideanWspSmoothTest Q s p) :
    AEStronglyMeasurable (cubeEuclideanWspKernel s p h.toField)
      (Gagliardo.gagliardoCubeMeasure Q) := by
  let μ := Gagliardo.gagliardoCubeMeasure Q
  let D : Set (Vec d × Vec d) := (Set.diagonal (Vec d))ᶜ
  have hcont : ContinuousOn (cubeEuclideanWspKernel s p h.toField) D := by
    exact continuousOn_cubeEuclideanWspKernel_offDiagonal h
  have hDmeas : MeasurableSet D := isClosed_diagonal.measurableSet.compl
  have hdiag : μ (Set.diagonal (Vec d)) = 0 :=
    gagliardoCubeMeasure_diagonal_eq_zero Q
  have hDae : ∀ᵐ z ∂μ, z ∈ D := by
    rw [ae_iff]
    simpa [D] using! hdiag
  have hrestrict : μ.restrict D = μ := Measure.restrict_eq_self_of_ae_mem hDae
  have hmeas : AEStronglyMeasurable (cubeEuclideanWspKernel s p h.toField)
      (μ.restrict D) :=
    hcont.aestronglyMeasurable hDmeas
  simpa only [hrestrict] using hmeas

private theorem ae_mem_cubeSet_prod_gagliardoCubeMeasure {d : ℕ}
    (Q : TriadicCube d) :
    ∀ᵐ z ∂Gagliardo.gagliardoCubeMeasure Q, z.1 ∈ cubeSet Q ∧ z.2 ∈ cubeSet Q := by
  let : IsFiniteMeasure (cubeMeasure Q) :=
    ⟨lt_top_iff_ne_top.mpr (cubeMeasure_apply_univ_ne_top Q)⟩
  have hbase : ∀ᵐ z ∂(cubeMeasure Q).prod (cubeMeasure Q),
      z.1 ∈ cubeSet Q ∧ z.2 ∈ cubeSet Q := by
    change ∀ᵐ z ∂(cubeMeasure Q).prod (cubeMeasure Q), z ∈ cubeSet Q ×ˢ cubeSet Q
    refine (Measure.ae_prod_iff_ae_ae
      (μ := cubeMeasure Q) (ν := cubeMeasure Q)
      (p := fun z : Vec d × Vec d => z.1 ∈ cubeSet Q ∧ z.2 ∈ cubeSet Q)
      ((measurableSet_cubeSet Q).prod (measurableSet_cubeSet Q))).mpr ?_
    filter_upwards [ae_restrict_mem (measurableSet_cubeSet Q)] with x hx
    filter_upwards [ae_restrict_mem (measurableSet_cubeSet Q)] with y hy
    exact ⟨hx, hy⟩
  rw [Gagliardo.gagliardoCubeMeasure, normalizedCubeMeasure, Measure.prod_smul_left]
  exact Measure.ae_smul_measure hbase (ENNReal.ofReal ((cubeVolume Q)⁻¹))

private theorem memCubeEuclideanWsp_of_smoothTest_neZero {d : ℕ} [NeZero d]
    {Q : TriadicCube d} {s : FractionalOrder} {p : FiniteLpExponent}
    (h : CubeEuclideanWspSmoothTest Q s p) :
    MemCubeEuclideanWsp Q s p h.toField := by
  obtain ⟨L, hL, hbound⟩ := smoothTest_kernel_norm_le_lipschitz_majorant Q h
  have hmajor : MemLp (L • smoothWspLpMajorant s p) p.exponent
      (Gagliardo.gagliardoCubeMeasure Q) :=
    (memLp_smoothWspLpMajorant Q s p).const_smul L
  apply hmajor.mono'
    (aestronglyMeasurable_cubeEuclideanWspKernel_of_smoothTest h)
  filter_upwards [ae_mem_cubeSet_prod_gagliardoCubeMeasure Q] with z hz
  calc
    ‖cubeEuclideanWspKernel s p h.toField z‖ ≤
        L * smoothWspLpMajorant s p z := hbound z.1 hz.1 z.2 hz.2
    _ = (L • smoothWspLpMajorant s p) z := rfl

namespace CubeEuclideanWspSmoothTest

/-- A globally smooth vector field has finite cube fractional-Sobolev seminorm.

The positive-dimensional proof controls the off-diagonal kernel by a Lipschitz
majorant; in dimension zero the target vector space is subsingleton, so the
kernel vanishes identically. -/
theorem memCubeEuclideanWsp {d : ℕ} {Q : TriadicCube d} {s : FractionalOrder}
    {p : FiniteLpExponent} (h : CubeEuclideanWspSmoothTest Q s p) :
    MemCubeEuclideanWsp Q s p h.toField := by
  classical
  by_cases hd : d = 0
  · subst d
    have hkernel : cubeEuclideanWspKernel s p h.toField = 0 := by
      funext z
      have hsub : h.toField z.1 - h.toField z.2 = 0 := Subsingleton.elim _ _
      simp [cubeEuclideanWspKernel_apply, hsub]
    unfold MemCubeEuclideanWsp
    rw [hkernel]
    exact MemLp.zero
  · let : NeZero d := ⟨hd⟩
    exact memCubeEuclideanWsp_of_smoothTest_neZero h

end CubeEuclideanWspSmoothTest

end

end Homogenization
