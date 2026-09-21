/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.FiniteLpGradientLimit

/-!
# The finite-`L^p` limiting weak equation

This internal module passes the canonical finite-data weak equations to the
`L^p` gradient limit.  Smooth compactly supported tests supply all conjugate
integrability needed for the two Hölder estimates; no regularity or boundary
witness for the limiting gradient is assumed here.
-/

namespace Homogenization

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace CubeCalderonZygmund

namespace INTERNAL

private theorem memLp_hilbertOfVec_of_gradMemLpOn
    {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞} {F : Vec d → Vec d}
    (hF : GradMemLpOn U p F) :
    MemLp (fun x => HilbertVec.ofVec (F x)) p (volume.restrict U) := by
  rw [memLp_piLp_iff]
  intro i
  simpa only [Function.comp_apply, HilbertVec.ofVec, PiLp.toLp_apply] using hF i

private theorem smoothCompactSupport_gradient_memLp
    {d : ℕ} {Omega : TopologicalSpace.Opens (Vec d)} (p : ℝ≥0∞)
    (phi : SmoothCompactSupportFunction Omega) :
    MemLp (fun x => HilbertVec.ofVec (phi.gradient x)) p volume := by
  have hgradient_cont : Continuous phi.gradient := by
    apply continuous_pi
    intro i
    exact (phi.contDiff.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hgradient_support : HasCompactSupport
      (fun x => HilbertVec.ofVec (phi.gradient x)) := by
    apply HasCompactSupport.mono' (phi.hasCompactSupport.fderiv ℝ)
    intro x hx
    apply subset_tsupport (fderiv ℝ (phi : Vec d → ℝ))
    rw [Function.mem_support] at hx ⊢
    intro hzero
    apply hx
    ext i
    simpa only [SmoothCompactSupportFunction.gradient, HilbertVec.ofVecL_apply,
      HilbertVec.ofVec, PiLp.toLp_apply, zero_apply] using!
      congrArg (fun L : Vec d →L[ℝ] ℝ => L (basisVec i)) hzero
  exact ((HilbertVec.ofVecL d).continuous.comp hgradient_cont).memLp_of_hasCompactSupport
    hgradient_support

private theorem tendsto_integral_vecDot_of_tendsto_eLpNorm_finiteLp
    {alpha : Type*} {d : ℕ} [MeasurableSpace alpha]
    (p : FiniteLpExponent) {mu : Measure alpha}
    {F : ℕ → alpha → Vec d} {G H : alpha → Vec d}
    (hF : ∀ n, MemLp (fun x => HilbertVec.ofVec (F n x)) p.exponent mu)
    (hG : MemLp (fun x => HilbertVec.ofVec (G x)) p.exponent mu)
    (hH : MemLp (fun x => HilbertVec.ofVec (H x)) p.conjugate.exponent mu)
    (htend : Tendsto (fun n => eLpNorm (fun x => HilbertVec.ofVec (F n x - G x))
      p.exponent mu) atTop (nhds 0)) :
    Tendsto (fun n => ∫ x, vecDot (F n x) (H x) ∂mu)
      atTop (nhds (∫ x, vecDot (G x) (H x) ∂mu)) := by
  let : ENNReal.HolderConjugate p.exponent p.conjugate.exponent :=
    p.holderConjugate
  have hdiff : ∀ n,
      MemLp (fun x => HilbertVec.ofVec (F n x - G x)) p.exponent mu := by
    intro n
    simpa only [HilbertVec.ofVecL_apply] using! (hF n).sub hG
  have hpair_mem : ∀ n,
      MemLp (fun x => vecDot (F n x) (H x)) 1 mu := by
    intro n
    have hbound : ∀ᵐ x ∂mu,
        ‖inner ℝ (HilbertVec.ofVec (F n x)) (HilbertVec.ofVec (H x))‖₊ ≤
          1 * ‖HilbertVec.ofVec (F n x)‖₊ * ‖HilbertVec.ofVec (H x)‖₊ := by
      filter_upwards with x
      simpa only [one_mul] using nnnorm_inner_le_nnnorm (𝕜 := ℝ)
        (HilbertVec.ofVec (F n x)) (HilbertVec.ofVec (H x))
    have hpair := MemLp.of_bilin (r := 1)
      (b := fun x y : HilbertVec d => inner ℝ x y) (c := 1)
      (hF n) hH ((hF n).aestronglyMeasurable.inner hH.aestronglyMeasurable) hbound
    simpa only [HilbertVec.inner_def] using hpair
  have hlimit_pair_mem : MemLp (fun x => vecDot (G x) (H x)) 1 mu := by
    have hbound : ∀ᵐ x ∂mu,
        ‖inner ℝ (HilbertVec.ofVec (G x)) (HilbertVec.ofVec (H x))‖₊ ≤
          1 * ‖HilbertVec.ofVec (G x)‖₊ * ‖HilbertVec.ofVec (H x)‖₊ := by
      filter_upwards with x
      simpa only [one_mul] using nnnorm_inner_le_nnnorm (𝕜 := ℝ)
        (HilbertVec.ofVec (G x)) (HilbertVec.ofVec (H x))
    have hpair := MemLp.of_bilin (r := 1)
      (b := fun x y : HilbertVec d => inner ℝ x y) (c := 1)
      hG hH (hG.aestronglyMeasurable.inner hH.aestronglyMeasurable) hbound
    simpa only [HilbertVec.inner_def] using hpair
  have hholder : ∀ n,
      eLpNorm (fun x => vecDot (F n x - G x) (H x)) 1 mu ≤
        eLpNorm (fun x => HilbertVec.ofVec (F n x - G x)) p.exponent mu *
          eLpNorm (fun x => HilbertVec.ofVec (H x)) p.conjugate.exponent mu :=
    fun n => eLpNorm_vecDot_le_mul (hdiff n) hH
  have hproduct : Tendsto (fun n =>
      eLpNorm (fun x => HilbertVec.ofVec (F n x - G x)) p.exponent mu *
        eLpNorm (fun x => HilbertVec.ofVec (H x)) p.conjugate.exponent mu)
      atTop (nhds 0) := by
    simpa only [zero_mul] using ENNReal.Tendsto.mul_const htend (Or.inr hH.eLpNorm_ne_top)
  have hL1 : Tendsto (fun n => eLpNorm
      (fun x => vecDot (F n x) (H x) - vecDot (G x) (H x)) 1 mu)
      atTop (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hproduct
      (fun _ => zero_le) (fun n => ?_)
    have heq : (fun x => vecDot (F n x) (H x) - vecDot (G x) (H x)) =
        fun x => vecDot (F n x - G x) (H x) := by
      funext x
      simp only [sub_eq_add_neg, vecDot_add_left, vecDot_neg_left]
    rw [heq]
    exact hholder n
  exact tendsto_integral_of_L1' (fun x => vecDot (G x) (H x))
    (memLp_one_iff_integrable.mp hlimit_pair_mem).aestronglyMeasurable
    (Eventually.of_forall fun n => memLp_one_iff_integrable.mp (hpair_mem n)) hL1

private theorem tendsto_normalized_gradient_difference
    {d : ℕ} [NeZero d] (q : FiniteLpExponent) (m : ℤ) {sigma0 : ℝ}
    (hsigma0 : 0 < sigma0) (h : CubeEuclideanLpField (originCube d m) q) :
    Tendsto (fun N => eLpNorm (fun x => HilbertVec.ofVec
      ((finiteLpSolutionApproximation m hsigma0 h
        (finiteLpGradientLimitSubsequence q m hsigma0 h N)).toH1Function.grad x -
          finiteLpGradientLimit q m hsigma0 h x)) q.exponent
      (centeredCubeDomain d m).normalizedVolume) atTop (nhds 0) := by
  let c : ℝ≥0∞ := ENNReal.ofReal ((cubeVolume (originCube d m))⁻¹)
  have hc : c ≠ 0 := by
    exact ENNReal.ofReal_ne_zero_iff.mpr (inv_pos.mpr (cubeVolume_pos _))
  have hraw :=
    tendsto_eLpNorm_finiteLpSolutionApproximation_grad_sub_finiteLpGradientLimit
      q m hsigma0 h
  have hscaled : Tendsto (fun N => c ^ (1 / q.exponent).toReal *
      eLpNorm (fun x => HilbertVec.ofVec
        ((finiteLpSolutionApproximation m hsigma0 h
          (finiteLpGradientLimitSubsequence q m hsigma0 h N)).toH1Function.grad x -
            finiteLpGradientLimit q m hsigma0 h x)) q.exponent
        (volume.restrict (openCubeSet (originCube d m)))) atTop (nhds 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul hraw
      (Or.inr (ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top))
  have hmeasure : (centeredCubeDomain d m).normalizedVolume =
      c • volume.restrict (openCubeSet (originCube d m)) := by
    simp only [c, centeredCubeDomain,
      cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure,
      normalizedCubeMeasure, cubeMeasure,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
  rw [hmeasure]
  have heq : (fun N => eLpNorm (fun x => HilbertVec.ofVec
      ((finiteLpSolutionApproximation m hsigma0 h
        (finiteLpGradientLimitSubsequence q m hsigma0 h N)).toH1Function.grad x -
          finiteLpGradientLimit q m hsigma0 h x)) q.exponent
      (c • volume.restrict (openCubeSet (originCube d m)))) =
      fun N => c ^ (1 / q.exponent).toReal *
        eLpNorm (fun x => HilbertVec.ofVec
          ((finiteLpSolutionApproximation m hsigma0 h
            (finiteLpGradientLimitSubsequence q m hsigma0 h N)).toH1Function.grad x -
              finiteLpGradientLimit q m hsigma0 h x)) q.exponent
          (volume.restrict (openCubeSet (originCube d m))) := by
    funext N
    simpa only [smul_eq_mul] using eLpNorm_smul_measure_of_ne_zero hc
      (fun x => HilbertVec.ofVec
        ((finiteLpSolutionApproximation m hsigma0 h
          (finiteLpGradientLimitSubsequence q m hsigma0 h N)).toH1Function.grad x -
            finiteLpGradientLimit q m hsigma0 h x)) q.exponent
      (volume.restrict (openCubeSet (originCube d m)))
  rw [heq]
  exact hscaled

/-- The canonical finite-`L^p` gradient limit satisfies the source-facing
normalized weak equation against every smooth compactly supported cube test. -/
theorem finiteLpGradientLimit_normalized_weak
    (d : ℕ) [NeZero d] (q : FiniteLpExponent) (m : ℤ) {sigma0 : ℝ}
    (hsigma0 : 0 < sigma0) (h : CubeEuclideanLpField (originCube d m) q)
    (phi : SmoothCompactSupportFunction
      ⟨openCubeSet (originCube d m), isOpen_openCubeSet (originCube d m)⟩) :
    sigma0 * ∫ x, vecDot (finiteLpGradientLimit q m hsigma0 h x) (phi.gradient x)
        ∂(centeredCubeDomain d m).normalizedVolume =
      -∫ x, vecDot (h.toField x) (phi.gradient x)
        ∂(centeredCubeDomain d m).normalizedVolume := by
  let U : Set (Vec d) := openCubeSet (originCube d m)
  let mu : Measure (Vec d) := (centeredCubeDomain d m).normalizedVolume
  let r : ℕ → ℕ := finiteLpGradientLimitSubsequence q m hsigma0 h
  let Du : Vec d → Vec d := finiteLpGradientLimit q m hsigma0 h
  let psi : H10Function U := H10Function.ofContDiff
    (isOpen_openCubeSet (originCube d m)) phi.contDiff phi.hasCompactSupport phi.tsupport_subset
  have htest : MemLp (fun x => HilbertVec.ofVec (phi.gradient x))
      q.conjugate.exponent mu := by
    change MemLp _ q.conjugate.exponent (centeredCubeDomain d m).normalizedVolume
    rw [show (centeredCubeDomain d m).normalizedVolume =
      ENNReal.ofReal ((cubeVolume (originCube d m))⁻¹) •
        volume.restrict (openCubeSet (originCube d m)) by
      simp only [centeredCubeDomain,
        cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure,
        normalizedCubeMeasure, cubeMeasure,
        volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]]
    exact ((smoothCompactSupport_gradient_memLp q.conjugate.exponent phi).restrict U).smul_measure
      ENNReal.ofReal_ne_top
  have hgrad_approx : ∀ N,
      MemLp (fun x => HilbertVec.ofVec
        ((finiteLpSolutionApproximation m hsigma0 h (r N)).toH1Function.grad x))
        q.exponent mu := by
    intro N
    change MemLp _ q.exponent (centeredCubeDomain d m).normalizedVolume
    rw [show (centeredCubeDomain d m).normalizedVolume =
      ENNReal.ofReal ((cubeVolume (originCube d m))⁻¹) •
        volume.restrict (openCubeSet (originCube d m)) by
      simp only [centeredCubeDomain,
        cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure,
        normalizedCubeMeasure, cubeMeasure,
        volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]]
    exact (memLp_hilbertOfVec_of_gradMemLpOn
      (finiteLpSolutionApproximation_gradMemLp m hsigma0 h (r N))).smul_measure
        ENNReal.ofReal_ne_top
  have hgrad_limit : MemLp (fun x => HilbertVec.ofVec (Du x)) q.exponent mu := by
    change MemLp _ q.exponent (centeredCubeDomain d m).normalizedVolume
    rw [show (centeredCubeDomain d m).normalizedVolume =
      ENNReal.ofReal ((cubeVolume (originCube d m))⁻¹) •
        volume.restrict (openCubeSet (originCube d m)) by
      simp only [centeredCubeDomain,
        cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure,
        normalizedCubeMeasure, cubeMeasure,
        volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]]
    exact (memLp_hilbertOfVec_of_gradMemLpOn
      (finiteLpGradientLimit_gradMemLp q m hsigma0 h)).smul_measure
        ENNReal.ofReal_ne_top
  have hgrad_pairing : Tendsto (fun N => ∫ x,
      vecDot ((finiteLpSolutionApproximation m hsigma0 h (r N)).toH1Function.grad x)
        (phi.gradient x) ∂mu) atTop
      (nhds (∫ x, vecDot (Du x) (phi.gradient x) ∂mu)) := by
    apply tendsto_integral_vecDot_of_tendsto_eLpNorm_finiteLp q
      hgrad_approx hgrad_limit htest
    simpa only [r, Du, mu] using tendsto_normalized_gradient_difference q m hsigma0 h
  have hdata_approx : ∀ N,
      MemLp (fun x => HilbertVec.ofVec ((finiteLpDataApproximation h (r N)).toField x))
        q.exponent mu := by
    intro N
    simpa only [mu, centeredCubeDomain,
      cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure] using
      (finiteLpDataApproximation h (r N)).euclideanMemLp
  have hdata : MemLp (fun x => HilbertVec.ofVec (h.toField x)) q.exponent mu := by
    simpa only [mu, centeredCubeDomain,
      cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure] using
      h.euclideanMemLp
  have hdata_norm : Tendsto (fun N => eLpNorm (fun x => HilbertVec.ofVec
      ((finiteLpDataApproximation h (r N)).toField x - h.toField x)) q.exponent mu)
      atTop (nhds 0) := by
    have hbase := (tendsto_eLpNorm_sub_finiteLpDataApproximation h).comp
      (finiteLpGradientLimitSubsequence_strictMono q m hsigma0 h).tendsto_atTop
    have hbase' : Tendsto (fun N => eLpNorm (fun x => HilbertVec.ofVec
        (h.toField x - (finiteLpDataApproximation h (r N)).toField x)) q.exponent
        (normalizedCubeMeasure (originCube d m))) atTop (nhds 0) := by
      simpa only [Function.comp_apply, r] using! hbase
    have hneg : Tendsto (fun N => eLpNorm (fun x => HilbertVec.ofVec
        ((finiteLpDataApproximation h (r N)).toField x - h.toField x)) q.exponent
        (normalizedCubeMeasure (originCube d m))) atTop (nhds 0) := by
      refine hbase'.congr' (Eventually.of_forall fun N => ?_)
      symm
      change eLpNorm (fun x => HilbertVec.ofVec
          ((finiteLpDataApproximation h (r N)).toField x - h.toField x)) q.exponent
          (normalizedCubeMeasure (originCube d m)) =
        eLpNorm (fun x => HilbertVec.ofVec
          (h.toField x - (finiteLpDataApproximation h (r N)).toField x)) q.exponent
          (normalizedCubeMeasure (originCube d m))
      rw [show (fun x => HilbertVec.ofVec
          ((finiteLpDataApproximation h (r N)).toField x - h.toField x)) =
        fun x => -HilbertVec.ofVec
          (h.toField x - (finiteLpDataApproximation h (r N)).toField x) by
        funext x
        rw [show (finiteLpDataApproximation h (r N)).toField x - h.toField x =
          -(h.toField x - (finiteLpDataApproximation h (r N)).toField x) by abel]
        exact (HilbertVec.ofVecL d).map_neg _]
      exact eLpNorm_neg _ _ _
    simpa only [r, mu, centeredCubeDomain,
      cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure] using hneg
  have hdata_pairing : Tendsto (fun N => ∫ x,
      vecDot ((finiteLpDataApproximation h (r N)).toField x) (phi.gradient x) ∂mu)
      atTop (nhds (∫ x, vecDot (h.toField x) (phi.gradient x) ∂mu)) := by
    exact tendsto_integral_vecDot_of_tendsto_eLpNorm_finiteLp q
      hdata_approx hdata htest hdata_norm
  have hequation : ∀ N,
      sigma0 * ∫ x,
          vecDot ((finiteLpSolutionApproximation m hsigma0 h (r N)).toH1Function.grad x)
            (phi.gradient x) ∂mu =
        -∫ x, vecDot ((finiteLpDataApproximation h (r N)).toField x)
          (phi.gradient x) ∂mu := by
    intro N
    simpa only [psi, H10Function.ofContDiff, H1Function.ofContDiff,
      SmoothCompactSupportFunction.gradient, U, mu, r] using!
      finiteLpSolutionApproximation_normalized_weak m hsigma0 h (r N) psi
  have hleft : Tendsto (fun N => sigma0 * ∫ x,
      vecDot ((finiteLpSolutionApproximation m hsigma0 h (r N)).toH1Function.grad x)
        (phi.gradient x) ∂mu) atTop
      (nhds (sigma0 * ∫ x, vecDot (Du x) (phi.gradient x) ∂mu)) :=
    tendsto_const_nhds.mul hgrad_pairing
  have hright : Tendsto (fun N => -∫ x,
      vecDot ((finiteLpDataApproximation h (r N)).toField x) (phi.gradient x) ∂mu)
      atTop (nhds (-∫ x, vecDot (h.toField x) (phi.gradient x) ∂mu)) :=
    hdata_pairing.neg
  have hleft_as_right := hleft.congr' (Eventually.of_forall hequation)
  simpa only [Du, mu] using tendsto_nhds_unique hleft_as_right hright

end INTERNAL

end CubeCalderonZygmund

end
end Homogenization
