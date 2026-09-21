/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.FiniteLpGradientLimit

/-!
# Calderón--Zygmund control of the canonical finite-`L^p` gradient limit

The supplied-data estimate is stable under the canonical bounded-data
approximation.  This module records that passage to the limit with the same
constant and the exact normalized Euclidean norm.
-/

namespace Homogenization

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace CubeCalderonZygmund

namespace INTERNAL

private theorem centeredCube_normalizedVolume_eq_smul_openCubeVolume
    {d : ℕ} (m : ℤ) :
    (centeredCubeDomain d m).normalizedVolume =
      ENNReal.ofReal ((cubeVolume (originCube d m))⁻¹) •
        volume.restrict (openCubeSet (originCube d m)) := by
  change (cubeBoundedMeasurableDomain (originCube d m)).normalizedVolume = _
  rw [cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure,
    normalizedCubeMeasure, cubeMeasure,
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]

private theorem tendsto_eLpNorm_of_tendsto_sub
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {f : ℕ → α → E} {g : α → E}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (hg : AEStronglyMeasurable g μ) (hg_top : eLpNorm g p μ ≠ ∞)
    (hfg : Tendsto (fun n => eLpNorm (fun x => f n x - g x) p μ)
      atTop (nhds 0)) :
    Tendsto (fun n => eLpNorm (f n) p μ) atTop (nhds (eLpNorm g p μ)) := by
  have hupper : ∀ n, eLpNorm (f n) p μ ≤
      eLpNorm g p μ + eLpNorm (fun x => f n x - g x) p μ := by
    intro n
    refine (le_of_eq ?_).trans (eLpNorm_add_le hg ((hf n).sub hg) hp)
    congr 1
    funext x
    simp only [Pi.add_apply]
    abel
  have hreverse : ∀ n,
      eLpNorm (fun x => g x - f n x) p μ =
        eLpNorm (fun x => f n x - g x) p μ := by
    intro n
    rw [show (fun x => g x - f n x) = -(fun x => f n x - g x) by
      funext x
      simp only [Pi.neg_apply]
      abel, eLpNorm_neg]
  have hlower : ∀ n,
      eLpNorm g p μ - eLpNorm (fun x => f n x - g x) p μ ≤
        eLpNorm (f n) p μ := by
    intro n
    rw [tsub_le_iff_right]
    calc
      eLpNorm g p μ = eLpNorm (fun x => f n x + (g x - f n x)) p μ := by
        congr 1
        funext x
        abel
      _ ≤ eLpNorm (f n) p μ + eLpNorm (fun x => g x - f n x) p μ :=
        eLpNorm_add_le (hf n) (hg.sub (hf n)) hp
      _ = eLpNorm (f n) p μ + eLpNorm (fun x => f n x - g x) p μ := by
        rw [hreverse]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    (g := fun n => eLpNorm g p μ - eLpNorm (fun x => f n x - g x) p μ)
    (h := fun n => eLpNorm g p μ + eLpNorm (fun x => f n x - g x) p μ)
    ?_ ?_ hlower hupper
  · have hsub := ENNReal.Tendsto.sub
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => eLpNorm g p μ) atTop
        (nhds (eLpNorm g p μ))) hfg (Or.inl hg_top)
    simpa using hsub
  · simpa using Tendsto.const_add (eLpNorm g p μ) hfg

private theorem finiteLpSolutionApproximation_grad_memLp_normalized
    {d : ℕ} [NeZero d] {q : FiniteLpExponent} (m : ℤ) {sigma0 : ℝ}
    (hsigma0 : 0 < sigma0) (h : CubeEuclideanLpField (originCube d m) q)
    (n : ℕ) :
    MemLp (fun x => HilbertVec.ofVec
      ((finiteLpSolutionApproximation m hsigma0 h n).toH1Function.grad x))
      q.exponent (centeredCubeDomain d m).normalizedVolume := by
  have hraw : MemLp (fun x => HilbertVec.ofVec
      ((finiteLpSolutionApproximation m hsigma0 h n).toH1Function.grad x))
      q.exponent (volume.restrict (openCubeSet (originCube d m))) := by
    apply MemLp.of_eval_piLp
    intro i
    simpa only [HilbertVec.ofVec, PiLp.toLp_apply] using
      finiteLpSolutionApproximation_gradMemLp m hsigma0 h n i
  rw [centeredCube_normalizedVolume_eq_smul_openCubeVolume]
  exact hraw.smul_measure ENNReal.ofReal_ne_top

private theorem finiteLpGradientLimit_memLp_normalized
    {d : ℕ} [NeZero d] (q : FiniteLpExponent) (m : ℤ) {sigma0 : ℝ}
    (hsigma0 : 0 < sigma0) (h : CubeEuclideanLpField (originCube d m) q) :
    MemLp (fun x => HilbertVec.ofVec (finiteLpGradientLimit q m hsigma0 h x))
      q.exponent (centeredCubeDomain d m).normalizedVolume := by
  have hraw : MemLp (fun x => HilbertVec.ofVec (finiteLpGradientLimit q m hsigma0 h x))
      q.exponent (volume.restrict (openCubeSet (originCube d m))) := by
    apply MemLp.of_eval_piLp
    intro i
    simpa only [HilbertVec.ofVec, PiLp.toLp_apply] using
      finiteLpGradientLimit_gradMemLp q m hsigma0 h i
  rw [centeredCube_normalizedVolume_eq_smul_openCubeVolume]
  exact hraw.smul_measure ENNReal.ofReal_ne_top

private theorem tendsto_normalizedEuclideanLpENorm_finiteLpSolutionApproximation_grad_sub_limit
    {d : ℕ} [NeZero d] (q : FiniteLpExponent) (m : ℤ) {sigma0 : ℝ}
    (hsigma0 : 0 < sigma0) (h : CubeEuclideanLpField (originCube d m) q) :
    Tendsto (fun N =>
      (centeredCubeDomain d m).normalizedEuclideanLpENorm q.exponent
        (fun x =>
          (finiteLpSolutionApproximation m hsigma0 h
            (finiteLpGradientLimitSubsequence q m hsigma0 h N)).toH1Function.grad x -
              finiteLpGradientLimit q m hsigma0 h x)) atTop (nhds 0) := by
  let c : ℝ≥0∞ := ENNReal.ofReal ((cubeVolume (originCube d m))⁻¹)
  have hc : c ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr
    (inv_pos.mpr (cubeVolume_pos (originCube d m))))
  have hfactor_top : c ^ (1 / q.exponent).toReal ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top
  have hraw :=
    tendsto_eLpNorm_finiteLpSolutionApproximation_grad_sub_finiteLpGradientLimit
      q m hsigma0 h
  have hscaled : Tendsto (fun N => c ^ (1 / q.exponent).toReal *
      eLpNorm (fun x => HilbertVec.ofVec
        ((finiteLpSolutionApproximation m hsigma0 h
          (finiteLpGradientLimitSubsequence q m hsigma0 h N)).toH1Function.grad x -
            finiteLpGradientLimit q m hsigma0 h x)) q.exponent
        (volume.restrict (openCubeSet (originCube d m)))) atTop (nhds 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul
      (a := c ^ (1 / q.exponent).toReal) hraw (Or.inr hfactor_top)
  simpa only [BoundedMeasurableDomain.normalizedEuclideanLpENorm,
    BoundedMeasurableDomain.normalizedLpENorm, euclideanNorm_eq_norm_ofVec,
    eLpNorm_norm, centeredCube_normalizedVolume_eq_smul_openCubeVolume,
    eLpNorm_smul_measure_of_ne_zero hc, c] using! hscaled

private theorem tendsto_normalizedEuclideanLpENorm_finiteLpSolutionApproximation_grad
    {d : ℕ} [NeZero d] (q : FiniteLpExponent) (m : ℤ) {sigma0 : ℝ}
    (hsigma0 : 0 < sigma0) (h : CubeEuclideanLpField (originCube d m) q) :
    Tendsto (fun N =>
      (centeredCubeDomain d m).normalizedEuclideanLpENorm q.exponent
        (finiteLpSolutionApproximation m hsigma0 h
          (finiteLpGradientLimitSubsequence q m hsigma0 h N)).toH1Function.grad)
      atTop (nhds ((centeredCubeDomain d m).normalizedEuclideanLpENorm q.exponent
        (finiteLpGradientLimit q m hsigma0 h))) := by
  have htend : Tendsto (fun N => eLpNorm (fun x => HilbertVec.ofVec
      ((finiteLpSolutionApproximation m hsigma0 h
        (finiteLpGradientLimitSubsequence q m hsigma0 h N)).toH1Function.grad x))
      q.exponent (centeredCubeDomain d m).normalizedVolume) atTop
      (nhds (eLpNorm (fun x => HilbertVec.ofVec (finiteLpGradientLimit q m hsigma0 h x))
        q.exponent (centeredCubeDomain d m).normalizedVolume)) := by
    apply tendsto_eLpNorm_of_tendsto_sub q.one_lt.le
    · intro N
      exact (finiteLpSolutionApproximation_grad_memLp_normalized m hsigma0 h
        (finiteLpGradientLimitSubsequence q m hsigma0 h N)).aestronglyMeasurable
    · exact (finiteLpGradientLimit_memLp_normalized q m hsigma0 h).aestronglyMeasurable
    · exact (finiteLpGradientLimit_memLp_normalized q m hsigma0 h).eLpNorm_lt_top.ne
    · simpa only [BoundedMeasurableDomain.normalizedEuclideanLpENorm,
        BoundedMeasurableDomain.normalizedLpENorm, euclideanNorm_eq_norm_ofVec,
        eLpNorm_norm] using!
        tendsto_normalizedEuclideanLpENorm_finiteLpSolutionApproximation_grad_sub_limit
          q m hsigma0 h
  simpa only [BoundedMeasurableDomain.normalizedEuclideanLpENorm,
    BoundedMeasurableDomain.normalizedLpENorm, euclideanNorm_eq_norm_ofVec,
    eLpNorm_norm] using htend

private theorem tendsto_normalizedEuclideanLpENorm_finiteLpDataApproximation
    {d : ℕ} {q : FiniteLpExponent} (m : ℤ)
    (h : CubeEuclideanLpField (originCube d m) q) :
    Tendsto (fun n =>
      (centeredCubeDomain d m).normalizedEuclideanLpENorm q.exponent
        (finiteLpDataApproximation h n).toField) atTop
      (nhds ((centeredCubeDomain d m).normalizedEuclideanLpENorm q.exponent h.toField)) := by
  have htend : Tendsto (fun n => eLpNorm
      (fun x => HilbertVec.ofVec ((finiteLpDataApproximation h n).toField x))
      q.exponent (normalizedCubeMeasure (originCube d m))) atTop
      (nhds (eLpNorm (fun x => HilbertVec.ofVec (h.toField x)) q.exponent
        (normalizedCubeMeasure (originCube d m)))) := by
    apply tendsto_eLpNorm_of_tendsto_sub q.one_lt.le
    · intro n
      exact (finiteLpDataApproximation h n).euclideanMemLp.aestronglyMeasurable
    · exact h.euclideanMemLp.aestronglyMeasurable
    · exact h.euclideanMemLp.eLpNorm_lt_top.ne
    · have hsub := tendsto_eLpNorm_sub_finiteLpDataApproximation h
      have hneg : Tendsto (fun n => eLpNorm
          (fun x => HilbertVec.ofVec
            ((finiteLpDataApproximation h n).toField x - h.toField x))
          q.exponent (normalizedCubeMeasure (originCube d m))) atTop (nhds 0) := by
        refine hsub.congr' ?_
        filter_upwards [] with n
        rw [show (fun x => HilbertVec.ofVec
            ((finiteLpDataApproximation h n).toField x - h.toField x)) =
              -(fun x => HilbertVec.ofVec
                (h.toField x - (finiteLpDataApproximation h n).toField x)) by
              funext x
              simp only [Pi.neg_apply]
              rw [show (finiteLpDataApproximation h n).toField x - h.toField x =
                -(h.toField x - (finiteLpDataApproximation h n).toField x) by abel]
              exact (HilbertVec.ofVecL d).map_neg _, eLpNorm_neg]
      exact hneg
  simpa only [BoundedMeasurableDomain.normalizedEuclideanLpENorm,
    BoundedMeasurableDomain.normalizedLpENorm, euclideanNorm_eq_norm_ofVec,
    eLpNorm_norm, centeredCubeDomain,
    cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure] using htend

/-- The canonical limiting gradient for arbitrary finite-`L^p` cube data
obeys the supplied-solution Calderón--Zygmund estimate with the same constant.
The constant is chosen before the cube, ellipticity scale, and datum. -/
theorem finiteLpGradientLimit_cz
    (d : ℕ) [NeZero d] (q : FiniteLpExponent) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ (m : ℤ) (sigma0 : ℝ)
      (h : CubeEuclideanLpField (originCube d m) q) (hsigma0 : 0 < sigma0),
      (centeredCubeDomain d m).normalizedEuclideanLpENorm q.exponent
          (finiteLpGradientLimit q m hsigma0 h) ≤
        C * (ENNReal.ofReal sigma0)⁻¹ *
          (centeredCubeDomain d m).normalizedEuclideanLpENorm q.exponent h.toField := by
  obtain ⟨C, hCtop, hC⟩ := centeredCubeH10ScalarDivergence_cz d q
  refine ⟨C, hCtop, ?_⟩
  intro m sigma0 h hsigma0
  let r := finiteLpGradientLimitSubsequence q m hsigma0 h
  have hleft :=
    tendsto_normalizedEuclideanLpENorm_finiteLpSolutionApproximation_grad
      q m hsigma0 h
  have hdata :=
    (tendsto_normalizedEuclideanLpENorm_finiteLpDataApproximation m h).comp
      (finiteLpGradientLimitSubsequence_strictMono q m hsigma0 h).tendsto_atTop
  have hfactor_top : C * (ENNReal.ofReal sigma0)⁻¹ ≠ ∞ :=
    ENNReal.mul_ne_top hCtop.ne
      (ENNReal.inv_ne_top.mpr (ne_of_gt (ENNReal.ofReal_pos.mpr hsigma0)))
  have hright : Tendsto (fun N => C * (ENNReal.ofReal sigma0)⁻¹ *
      (centeredCubeDomain d m).normalizedEuclideanLpENorm q.exponent
        (finiteLpDataApproximation h (r N)).toField) atTop
      (nhds (C * (ENNReal.ofReal sigma0)⁻¹ *
        (centeredCubeDomain d m).normalizedEuclideanLpENorm q.exponent h.toField)) := by
    simpa only [mul_assoc, r] using!
      ENNReal.Tendsto.const_mul (a := C * (ENNReal.ofReal sigma0)⁻¹)
        hdata (Or.inr hfactor_top)
  refine le_of_tendsto_of_tendsto' hleft hright (fun N => ?_)
  exact hC m sigma0
    (finiteLpDataApproximation h (finiteLpGradientLimitSubsequence q m hsigma0 h N))
    (finiteLpSolutionApproximation m hsigma0 h
      (finiteLpGradientLimitSubsequence q m hsigma0 h N)) hsigma0
    (finiteLpSolutionApproximation_normalized_weak m hsigma0 h
      (finiteLpGradientLimitSubsequence q m hsigma0 h N))

end INTERNAL

end CubeCalderonZygmund

end
end Homogenization
