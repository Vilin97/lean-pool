/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.FiniteLpDataDensity
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.FiniteLpSolutionStability

/-!
# Canonical finite-`L^p` approximating solutions on centered cubes

For arbitrary finite-exponent cube data, this module packages the bounded
`L² ∩ Lᵖ` data approximants together with their canonical zero-trace `H¹`
solutions.  It stops before selecting a limit: the later arbitrary-data
assembly is responsible for both the high-exponent zero-trace bridge and the
weak-equation limit passage.
-/

@[expose] public section

namespace Homogenization

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace CubeCalderonZygmund

namespace INTERNAL

private theorem memVectorL2_openCubeSet_of_euclideanMemLpTwo
    {d : ℕ} (Q : TriadicCube d) {F : Vec d → Vec d}
    (hF : MemLp (fun x => HilbertVec.ofVec (F x)) 2 (normalizedCubeMeasure Q)) :
    MemVectorL2 (openCubeSet Q) F := by
  have hvec : MemLp F 2 (normalizedCubeMeasure Q) := by
    apply MemLp.of_eval
    intro i
    simpa only [HilbertVec.ofVec, PiLp.toLp_apply] using hF.eval_piLp i
  have hle :
      cubeMeasure Q ≤ ENNReal.ofReal (cubeVolume Q) • normalizedCubeMeasure Q := by
    have hvol_nonneg : 0 ≤ cubeVolume Q := cubeVolume_nonneg Q
    have hmul :
        ENNReal.ofReal (cubeVolume Q) * ENNReal.ofReal ((cubeVolume Q)⁻¹) = 1 := by
      rw [← ENNReal.ofReal_mul hvol_nonneg]
      have hreal : cubeVolume Q * (cubeVolume Q)⁻¹ = 1 := by
        field_simp [(cubeVolume_pos Q).ne']
      rw [hreal]
      norm_num
    have heq : ENNReal.ofReal (cubeVolume Q) • normalizedCubeMeasure Q = cubeMeasure Q := by
      rw [normalizedCubeMeasure]
      ext s
      rw [Measure.smul_apply, Measure.smul_apply]
      change ENNReal.ofReal (cubeVolume Q) *
          (ENNReal.ofReal ((cubeVolume Q)⁻¹) * cubeMeasure Q s) = cubeMeasure Q s
      rw [← mul_assoc, hmul, one_mul]
    exact le_of_eq heq.symm
  have hcube : MemLp F 2 (cubeMeasure Q) :=
    hvec.of_measure_le_smul (c := ENNReal.ofReal (cubeVolume Q))
      ENNReal.ofReal_ne_top hle
  simpa only [MemVectorL2, volumeMeasureOn, cubeMeasure,
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet] using hcube

/-- The canonical `H¹₀` solution associated to the bounded `L² ∩ Lᵖ`
approximation of finite-`Lᵖ` centered-cube data. -/
noncomputable def finiteLpSolutionApproximation
    {d : ℕ} [NeZero d] {q : FiniteLpExponent} (m : ℤ) {sigma0 : ℝ}
    (hsigma0 : 0 < sigma0) (h : CubeEuclideanLpField (originCube d m) q)
    (n : ℕ) : H10Function (openCubeSet (originCube d m)) :=
  openCubeSetScalarDivergenceSolution (originCube d m) hsigma0
    (finiteLpDataApproximation h n).toField
    (memVectorL2_openCubeSet_of_euclideanMemLpTwo (originCube d m)
      (finiteLpDataApproximation h n).euclideanMemL2)

/-- Each canonical approximate solution satisfies the exact normalized weak
equation on the centered cube. -/
theorem finiteLpSolutionApproximation_normalized_weak
    {d : ℕ} [NeZero d] {q : FiniteLpExponent} (m : ℤ) {sigma0 : ℝ}
    (hsigma0 : 0 < sigma0) (h : CubeEuclideanLpField (originCube d m) q)
    (n : ℕ) (psi : H10Function (openCubeSet (originCube d m))) :
    sigma0 * ∫ x,
        vecDot ((finiteLpSolutionApproximation m hsigma0 h n).toH1Function.grad x)
          (psi.toH1Function.grad x) ∂(centeredCubeDomain d m).normalizedVolume =
      -∫ x, vecDot ((finiteLpDataApproximation h n).toField x)
        (psi.toH1Function.grad x) ∂(centeredCubeDomain d m).normalizedVolume := by
  exact openCubeSetScalarDivergenceSolution_normalized_weak m hsigma0
    (finiteLpDataApproximation h n).toField
    (memVectorL2_openCubeSet_of_euclideanMemLpTwo (originCube d m)
      (finiteLpDataApproximation h n).euclideanMemL2) psi

private theorem tendsto_eLpNorm_sub_finiteLpDataApproximation_pair
    {d : ℕ} {Q : TriadicCube d} {q : FiniteLpExponent}
    (h : CubeEuclideanLpField Q q) :
    Tendsto (fun nk : ℕ × ℕ => eLpNorm
      (fun x => HilbertVec.ofVec
        ((finiteLpDataApproximation h nk.1).toField x -
          (finiteLpDataApproximation h nk.2).toField x))
      q.exponent (normalizedCubeMeasure Q)) atTop (nhds 0) := by
  have htend := tendsto_eLpNorm_sub_finiteLpDataApproximation h
  have hfst : Tendsto (Prod.fst : ℕ × ℕ → ℕ) atTop atTop := by
    simpa only [prod_atTop_atTop_eq] using
      (tendsto_fst : Tendsto (Prod.fst : ℕ × ℕ → ℕ) (atTop ×ˢ atTop) atTop)
  have hsnd : Tendsto (Prod.snd : ℕ × ℕ → ℕ) atTop atTop := by
    simpa only [prod_atTop_atTop_eq] using
      (tendsto_snd : Tendsto (Prod.snd : ℕ × ℕ → ℕ) (atTop ×ˢ atTop) atTop)
  have htend_fst : Tendsto (fun nk : ℕ × ℕ => eLpNorm
      (fun x => HilbertVec.ofVec
        (h.toField x - (finiteLpDataApproximation h nk.1).toField x))
      q.exponent (normalizedCubeMeasure Q)) atTop (nhds 0) :=
    htend.comp hfst
  have htend_snd : Tendsto (fun nk : ℕ × ℕ => eLpNorm
      (fun x => HilbertVec.ofVec
        (h.toField x - (finiteLpDataApproximation h nk.2).toField x))
      q.exponent (normalizedCubeMeasure Q)) atTop (nhds 0) :=
    htend.comp hsnd
  have hsum : Tendsto (fun nk : ℕ × ℕ =>
      eLpNorm (fun x => HilbertVec.ofVec
        (h.toField x - (finiteLpDataApproximation h nk.1).toField x))
        q.exponent (normalizedCubeMeasure Q) +
      eLpNorm (fun x => HilbertVec.ofVec
        (h.toField x - (finiteLpDataApproximation h nk.2).toField x))
        q.exponent (normalizedCubeMeasure Q)) atTop (nhds 0) := by
    simpa using htend_fst.add htend_snd
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => zero_le) (fun nk => ?_)
  let hn := finiteLpDataApproximation h nk.1
  let hk := finiteLpDataApproximation h nk.2
  have hhn : MemLp (fun x => HilbertVec.ofVec (h.toField x - hn.toField x))
      q.exponent (normalizedCubeMeasure Q) := by
    simpa only [HilbertVec.ofVecL_apply] using! h.euclideanMemLp.sub hn.euclideanMemLp
  have hhk : MemLp (fun x => HilbertVec.ofVec (h.toField x - hk.toField x))
      q.exponent (normalizedCubeMeasure Q) := by
    simpa only [HilbertVec.ofVecL_apply] using! h.euclideanMemLp.sub hk.euclideanMemLp
  have heq : (fun x => HilbertVec.ofVec (hn.toField x - hk.toField x)) =
      (fun x => -HilbertVec.ofVec (h.toField x - hn.toField x)) +
        fun x => HilbertVec.ofVec (h.toField x - hk.toField x) := by
    funext x
    rw [show hn.toField x - hk.toField x =
      -(h.toField x - hn.toField x) + (h.toField x - hk.toField x) by abel]
    simpa only [Pi.add_apply, Pi.neg_apply] using!
      (HilbertVec.ofVecL d).map_add
        (-(h.toField x - hn.toField x)) (h.toField x - hk.toField x)
  rw [heq]
  exact (eLpNorm_add_le hhn.neg.aestronglyMeasurable hhk.aestronglyMeasurable
    q.one_lt.le).trans (by rw [eLpNorm_neg])

/-- One constant depending only on the dimension and exponent controls the
canonical approximate solutions uniformly, and their gradients are Cauchy in
the exact centered normalized Euclidean `L^p` norm. -/
theorem exists_tendsto_normalizedEuclideanLpENorm_finiteLpSolutionApproximation_grad_sub
    (d : ℕ) [NeZero d] (q : FiniteLpExponent) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ (m : ℤ) (sigma0 : ℝ)
      (h : CubeEuclideanLpField (originCube d m) q) (hsigma0 : 0 < sigma0),
      Tendsto (fun nk : ℕ × ℕ =>
        (centeredCubeDomain d m).normalizedEuclideanLpENorm q.exponent
          (fun x =>
            (finiteLpSolutionApproximation m hsigma0 h nk.1).toH1Function.grad x -
              (finiteLpSolutionApproximation m hsigma0 h nk.2).toH1Function.grad x))
        atTop (nhds 0) := by
  obtain ⟨C, hCtop, hC⟩ := centeredCubeH10ScalarDivergence_solution_stability d q
  refine ⟨C, hCtop, ?_⟩
  intro m sigma0 h hsigma0
  have hdata : Tendsto (fun nk : ℕ × ℕ =>
      (centeredCubeDomain d m).normalizedEuclideanLpENorm q.exponent
        (fun x =>
          (finiteLpDataApproximation h nk.1).toField x -
            (finiteLpDataApproximation h nk.2).toField x)) atTop (nhds 0) := by
    simpa only [BoundedMeasurableDomain.normalizedEuclideanLpENorm,
      BoundedMeasurableDomain.normalizedLpENorm, euclideanNorm_eq_norm_ofVec,
      MeasureTheory.eLpNorm_norm, centeredCubeDomain,
      cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure] using
      (tendsto_eLpNorm_sub_finiteLpDataApproximation_pair h)
  have hright : Tendsto (fun nk : ℕ × ℕ =>
      C * (ENNReal.ofReal sigma0)⁻¹ *
        (centeredCubeDomain d m).normalizedEuclideanLpENorm q.exponent
          (fun x =>
            (finiteLpDataApproximation h nk.1).toField x -
              (finiteLpDataApproximation h nk.2).toField x)) atTop (nhds 0) := by
    have hfactor_ne_top : C * (ENNReal.ofReal sigma0)⁻¹ ≠ ∞ :=
      ENNReal.mul_ne_top hCtop.ne
        (ENNReal.inv_ne_top.mpr (ne_of_gt (ENNReal.ofReal_pos.mpr hsigma0)))
    simpa only [mul_zero, mul_assoc] using
      ENNReal.Tendsto.const_mul (a := C * (ENNReal.ofReal sigma0)⁻¹)
        hdata (Or.inr hfactor_ne_top)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hright
    (fun _ => zero_le) (fun nk => ?_)
  exact hC m sigma0 (finiteLpDataApproximation h nk.1) (finiteLpDataApproximation h nk.2)
    (finiteLpSolutionApproximation m hsigma0 h nk.1)
    (finiteLpSolutionApproximation m hsigma0 h nk.2) hsigma0
    (fun psi => finiteLpSolutionApproximation_normalized_weak m hsigma0 h nk.1 psi)
    (fun psi => finiteLpSolutionApproximation_normalized_weak m hsigma0 h nk.2 psi)

end INTERNAL

end CubeCalderonZygmund

end
end Homogenization
