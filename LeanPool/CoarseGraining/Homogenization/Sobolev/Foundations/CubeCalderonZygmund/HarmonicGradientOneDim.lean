/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.HarmonicInteriorHessian
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.HarmonicDerivative
import LeanPool.CoarseGraining.Homogenization.Besov.Duality.ProjectionLimit
import LeanPool.CoarseGraining.Homogenization.Sobolev.FiniteLpExponent
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.HarmonicGradientIterationGeometry

/-! # Harmonic Gradient One Dim -/

namespace Homogenization

open scoped ENNReal

noncomputable section

/-!
# One-dimensional harmonic gradient gain

In one dimension, the fixed-radius weak Hessian of a weakly harmonic function
vanishes.  Thus its only gradient coordinate is constant almost everywhere on
the central triadic child.  This supplies every finite normalized `L^r` gain
without an endpoint Sobolev embedding.
-/

namespace CubeCalderonZygmund

private theorem hessian_zero_ae_on_innerHalf {Q : TriadicCube 1}
    {u : H1Function (openCubeSet Q)}
    (h : WeakPoissonEquationOn (openCubeSet Q) u (fun _ => 0))
    {uS : H1Function (scaledOpenCubeSet Q (1 / 2 : ℝ))}
    (huSgrad : uS.grad = u.grad)
    (H : HasWeakHessianOn (scaledOpenCubeSet Q (1 / 2 : ℝ)) uS) :
    H.hess 0 0 =ᵐ[MeasureTheory.volume.restrict (scaledOpenCubeSet Q (1 / 2 : ℝ))]
      fun _ => 0 := by
  let V := scaledOpenCubeSet Q (1 / 2 : ℝ)
  have hVopen : IsOpen V :=
    (isOpenBoundedConvexDomain_scaledOpenCubeSet_of_pos Q (by norm_num)).isOpen
  have hVU : V ⊆ openCubeSet Q := by
    intro x hx
    apply scaledClosedCubeSet_subset_openCubeSet_of_nonneg_of_lt_one Q
      (ρ := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
    intro i
    exact le_of_lt (hx i)
  have hres := h.restrict hVopen hVU
  have hloc : MeasureTheory.LocallyIntegrableOn (H.hess 0 0) V MeasureTheory.volume :=
    MeasureTheory.locallyIntegrableOn_of_locallyIntegrable_restrict
      ((H.hess_memL2 0 0).locallyIntegrable (by norm_num))
  rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' hVopen.measurableSet]
  refine hVopen.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc ?_
  intro φ hφ hφs hφsub
  have htest := hres.test φ hφ hφs hφsub
  have hsecond := H.weak_second 0 0 φ hφ hφs hφsub
  have hgrad_zero :
      ∫ x in V, uS.grad x 0 * (fderiv ℝ φ x) (basisVec 0) ∂MeasureTheory.volume = 0 := by
    simpa [H1Function.restrict, huSgrad, vecDot, euclideanGradient,
      euclideanCoordDeriv] using htest
  have hhess_zero : ∫ x in V, H.hess 0 0 x * φ x ∂MeasureTheory.volume = 0 := by
    simpa [V] using (neg_eq_zero.mp (by linarith [hsecond, hgrad_zero]))
  calc
    ∫ x, φ x * H.hess 0 0 x ∂MeasureTheory.volume =
        ∫ x, H.hess 0 0 x * φ x ∂MeasureTheory.volume := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with x
          ring
    _ = ∫ x in V, H.hess 0 0 x * φ x ∂MeasureTheory.volume := by
      symm
      apply MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have hxnot : x ∉ tsupport φ := fun hxt => hx (hφsub hxt)
      simp [image_eq_zero_of_notMem_tsupport hxnot]
    _ = 0 := hhess_zero

private theorem exists_gradCoord_const_ae_on_innerHalf {Q : TriadicCube 1}
    {u : H1Function (openCubeSet Q)}
    (h : WeakPoissonEquationOn (openCubeSet Q) u (fun _ => 0)) :
    ∃ c : ℝ, (fun x => u.grad x 0) =ᵐ[MeasureTheory.volume.restrict
      (scaledOpenCubeSet Q (1 / 2 : ℝ))] fun _ => c := by
  obtain ⟨uS, huSval, huSgrad, H, hHbound⟩ :=
    exists_innerHalf_hasWeakHessianOn_harmonic h
  let V := scaledOpenCubeSet Q (1 / 2 : ℝ)
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn V) := by
    dsimp [V, volumeMeasureOn]
    exact (isOpenBoundedConvexDomain_scaledOpenCubeSet_of_pos Q
      (by norm_num)).isFiniteMeasure_restrict_volume
  let v := H.gradCoordH1Function 0
  have hhess : H.hess 0 0 =ᵐ[MeasureTheory.volume.restrict V] fun _ => 0 := by
    simpa [V] using hessian_zero_ae_on_innerHalf h huSgrad H
  have hvfieldzero : v.grad =ᵐ[MeasureTheory.volume.restrict V] fun _ => 0 := by
    filter_upwards [hhess] with x hh
    funext j
    fin_cases j
    simpa [v, HasWeakHessianOn.gradCoordH1Function] using hh
  have hvgradzero : v.gradToVectorL2 = 0 := by
    apply MeasureTheory.Lp.ext
    filter_upwards [H1Function.coeFn_gradToVectorL2 v, hvfieldzero,
      MeasureTheory.Lp.coeFn_zero (Vec 1) (2 : ℝ≥0∞) (volumeMeasureOn V)]
      with x hv hfield hzero
    exact hv.trans (hfield.trans hzero.symm)
  have hp := (h1CoerciveEstimate_of_isOpenBoundedConvexDomain
    (isOpenBoundedConvexDomain_scaledOpenCubeSet_of_pos Q (by norm_num))).bound v.toMeanZero
  have hvsubzero_norm : ‖v.subAverage.toScalarL2‖ = 0 := by
    change ‖v.subAverage.toScalarL2‖ ≤
      (h1CoerciveEstimate_of_isOpenBoundedConvexDomain
        (isOpenBoundedConvexDomain_scaledOpenCubeSet_of_pos Q (by norm_num))).constant *
        ‖v.subAverage.gradToVectorL2‖ at hp
    rw [H1Function.gradToVectorL2_subAverage_eq, hvgradzero] at hp
    simp only [norm_zero, mul_zero] at hp
    exact le_antisymm hp (norm_nonneg _)
  have hvsubzero : v.subAverage.toScalarL2 = 0 := norm_eq_zero.mp hvsubzero_norm
  have hvsub_ae : v.subAverage =ᵐ[MeasureTheory.volume.restrict V] fun _ => 0 := by
    filter_upwards [H1Function.coeFn_toScalarL2 v.subAverage,
      MeasureTheory.Lp.coeFn_zero ℝ (2 : ℝ≥0∞) (volumeMeasureOn V)] with x hv hzero
    rw [hvsubzero] at hv
    exact hv.symm.trans hzero
  refine ⟨integralAverage V v, ?_⟩
  filter_upwards [hvsub_ae] with x hx
  have hx' : v x - integralAverage V v = 0 := by
    simpa [V, H1Function.subAverage_apply] using hx
  simpa [v, huSgrad] using sub_eq_zero.mp hx'

private theorem middleChildCube_subset_innerHalf (Q : TriadicCube 1) :
    cubeSet ({ scale := Q.scale - 1, index := fun i => 3 * Q.index i } : TriadicCube 1) ⊆
      scaledOpenCubeSet Q (1 / 2 : ℝ) := by
  intro x hx i
  have hscale : cubeScaleFactor
      ({ scale := Q.scale - 1, index := fun i => 3 * Q.index i } : TriadicCube 1) =
      cubeScaleFactor Q / 3 := by
    simpa using cubeScaleFactor_childCube Q (fun _ => (1 : Fin 3))
  have hpos : 0 < cubeScaleFactor Q := by
    simpa [cubeScaleFactor] using zpow_pos (by norm_num : (0 : ℝ) < 3) Q.scale
  have hx' := hx i
  rw [hscale] at hx'
  norm_num [Int.cast_mul] at hx'
  change |x i - cubeCenter Q i| < (1 / 2 : ℝ) * cubeRadius Q
  rw [cubeCenter, cubeRadius, abs_lt]
  constructor <;> nlinarith

/-- The one-dimensional constant-gradient construction supplies actual finite
`L^p` membership on the central child, not merely a real-valued norm bound.
This is the finiteness witness required by the later ENNReal CZ carrier. -/
theorem harmonic_gradCoord_memLp_centralDescendant_oneDim
    (p : FiniteLpExponent) (Q : TriadicCube 1) (u : H1Function (openCubeSet Q))
    (h : WeakPoissonEquationOn (openCubeSet Q) u (fun _ => 0)) :
    MeasureTheory.MemLp (fun x => u.grad x 0) p.exponent
      (normalizedCubeMeasure (centralDescendant Q 1)) := by
  obtain ⟨c, hc⟩ := exists_gradCoord_const_ae_on_innerHalf h
  let R : TriadicCube 1 := centralDescendant Q 1
  have hRsub : cubeSet R ⊆ scaledOpenCubeSet Q (1 / 2 : ℝ) := by
    simpa [R, centralDescendant] using! middleChildCube_subset_innerHalf Q
  have hRac : MeasureTheory.Measure.AbsolutelyContinuous (normalizedCubeMeasure R)
      (MeasureTheory.volume.restrict (scaledOpenCubeSet Q (1 / 2 : ℝ))) := by
    rw [normalizedCubeMeasure, cubeMeasure]
    exact MeasureTheory.Measure.smul_absolutelyContinuous.trans
      (MeasureTheory.Measure.absolutelyContinuous_of_le
        (MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume hRsub))
  have hcR : (fun x => u.grad x 0) =ᵐ[normalizedCubeMeasure R] fun _ => c :=
    hRac.ae_eq hc
  exact (MeasureTheory.memLp_congr_ae hcR).mpr (MeasureTheory.memLp_const c)

private theorem cubeLpNorm_two_middleChild_le_three_mul (Q : TriadicCube 1)
    (f : Vec 1 → ℝ) (hf : MeasureTheory.MemLp f 2 (normalizedCubeMeasure Q)) :
    cubeLpNorm ({ scale := Q.scale - 1, index := fun i => 3 * Q.index i } : TriadicCube 1) 2 f ≤
      3 * cubeLpNorm Q 2 f := by
  let R : TriadicCube 1 := { scale := Q.scale - 1, index := fun i => 3 * Q.index i }
  have hR : R ∈ descendantsAtDepth Q 1 := by
    rw [mem_descendantsAtDepth_succ_iff]
    exact ⟨Q, by simp, by simpa [R] using middleChild_mem_childCubes Q⟩
  have hvol : cubeVolume Q / cubeVolume R = 3 := by
    have h := cubeVolume_eq_card_mul_cubeVolume_of_mem_descendantsAtDepth hR
    have hcard : (descendantsAtDepth Q 1).card = 3 := by
      simp [descendantsAtDepth, childCubes_card]
    rw [hcard] at h
    norm_num at h
    calc
      cubeVolume Q / cubeVolume R = (3 * cubeVolume R) / cubeVolume R := by rw [h]
      _ = 3 := by field_simp [(cubeVolume_pos R).ne']
  have hsmul : ENNReal.ofReal (cubeVolume Q / cubeVolume R) ≠ 0 := by
    exact ENNReal.ofReal_ne_zero_iff.2 (div_pos (cubeVolume_pos Q) (cubeVolume_pos R))
  have hle : MeasureTheory.eLpNorm f 2 (normalizedCubeMeasure R) ≤
      3 * MeasureTheory.eLpNorm f 2 (normalizedCubeMeasure Q) := by
    calc
      MeasureTheory.eLpNorm f 2 (normalizedCubeMeasure R) =
          (ENNReal.ofReal (cubeVolume Q / cubeVolume R) ^ (1 / (2 : ℝ≥0∞)).toReal) •
            MeasureTheory.eLpNorm f 2 ((normalizedCubeMeasure Q).restrict (cubeSet R)) := by
        rw [normalizedCubeMeasure_descendant_eq_smul_restrict hR]
        exact MeasureTheory.eLpNorm_smul_measure_of_ne_zero hsmul f 2 _
      _ ≤ 3 * MeasureTheory.eLpNorm f 2 ((normalizedCubeMeasure Q).restrict (cubeSet R)) := by
        rw [hvol]
        norm_num
        apply mul_le_mul_left
        calc
          (3 : ℝ≥0∞) ^ (1 / (2 : ℝ)) ≤ (3 : ℝ≥0∞) ^ (1 : ℝ) :=
            ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
          _ = 3 := by norm_num
      _ ≤ 3 * MeasureTheory.eLpNorm f 2 (normalizedCubeMeasure Q) := by
        exact mul_le_mul_right (MeasureTheory.eLpNorm_mono_measure f
          MeasureTheory.Measure.restrict_le_self) _
  have hfinR := memLp_on_descendant_of_memLp hR hf
  have hfinQ := hf.eLpNorm_ne_top
  have htop : 3 * MeasureTheory.eLpNorm f 2 (normalizedCubeMeasure Q) ≠ ∞ :=
    ENNReal.mul_ne_top (by norm_num) hfinQ
  have hreal := ENNReal.toReal_mono htop hle
  simpa [R, cubeLpNorm, ENNReal.toReal_mul] using hreal

private theorem cubeLpNorm_eq_abs_of_ae_eq_const (Q : TriadicCube 1)
    (p : FiniteLpExponent) (f : Vec 1 → ℝ) (c : ℝ)
    (h : f =ᵐ[normalizedCubeMeasure Q] fun _ => c) :
    cubeLpNorm Q p.exponent f = |c| := by
  unfold cubeLpNorm
  rw [MeasureTheory.eLpNorm_congr_ae h,
    MeasureTheory.eLpNorm_const' c (ne_of_gt (lt_trans zero_lt_one p.one_lt)) p.lt_top.ne,
    normalizedCubeMeasure_apply_univ]
  simp

/-- In one dimension a weakly harmonic gradient has every finite normalized
`L^r` gain on the central child.  The displayed proof uses the universal
constant `3`; in particular it is uniform in the exponent and cube scale. -/
theorem exists_harmonic_gradCoord_finiteLp_bound_oneDim (p : FiniteLpExponent) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Q : TriadicCube 1) (u : H1Function (openCubeSet Q)),
        WeakPoissonEquationOn (openCubeSet Q) u (fun _ => 0) →
          cubeLpNorm
              ({ scale := Q.scale - 1, index := fun i => 3 * Q.index i } : TriadicCube 1)
              p.exponent (fun x => u.grad x 0) ≤
            C * cubeLpNorm Q 2 (fun x => u.grad x 0) := by
  refine ⟨3, by norm_num, ?_⟩
  intro Q u h
  let R : TriadicCube 1 := { scale := Q.scale - 1, index := fun i => 3 * Q.index i }
  obtain ⟨c, hc⟩ := exists_gradCoord_const_ae_on_innerHalf h
  have hRsub : cubeSet R ⊆ scaledOpenCubeSet Q (1 / 2 : ℝ) := by
    simpa [R] using middleChildCube_subset_innerHalf Q
  have hRac : MeasureTheory.Measure.AbsolutelyContinuous (normalizedCubeMeasure R)
      (MeasureTheory.volume.restrict (scaledOpenCubeSet Q (1 / 2 : ℝ))) := by
    rw [normalizedCubeMeasure, cubeMeasure]
    exact MeasureTheory.Measure.smul_absolutelyContinuous.trans
      (MeasureTheory.Measure.absolutelyContinuous_of_le
        (MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume hRsub))
  have hcR : (fun x => u.grad x 0) =ᵐ[normalizedCubeMeasure R] fun _ => c :=
    hRac.ae_eq hc
  have hleft : cubeLpNorm R p.exponent (fun x => u.grad x 0) = |c| :=
    cubeLpNorm_eq_abs_of_ae_eq_const R p _ c hcR
  have hleftTwo : cubeLpNorm R 2 (fun x => u.grad x 0) = |c| := by
    simpa using cubeLpNorm_eq_abs_of_ae_eq_const R FiniteLpExponent.two _ c hcR
  have hmem : MeasureTheory.MemLp (fun x => u.grad x 0) 2 (normalizedCubeMeasure Q) := by
    exact u.grad_memL2_normalizedCubeMeasure 0
  have hchild := cubeLpNorm_two_middleChild_le_three_mul Q _ hmem
  rw [hleftTwo] at hchild
  simpa [R, hleft] using hchild

end CubeCalderonZygmund

end

end Homogenization
