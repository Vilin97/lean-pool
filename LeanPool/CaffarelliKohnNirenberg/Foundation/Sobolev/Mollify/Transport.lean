/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Mollify.Basic

/-!
# Interior transport of weak derivatives through mollification

Adapted from PDEFoundation (EllipticRegularity, 2026) with the author's
permission. The translated `ContDiffBump` is used as the test function in the
defining weak-derivative identity, while Mathlib supplies the convolution
derivative and measure-preserving change of variables.

The transport theorem below is pointwise on a closed-ball interior condition,
with a compact-set wrapper. The general local `L^p` approximation theorem is
not asserted here because the available Mathlib API does not provide the
needed local convolution bound and translation-continuity package.
-/

public section

open scoped Convolution Topology
open MeasureTheory

namespace CKN

theorem fderiv_mollify_eq_mollify_of_hasWeakPartialDerivOn
    {d : ℕ} {U : Set (Vec d)} (_ : IsOpen U)
    {u gi : Vec d → ℝ} {i : Fin d} (hu : MeasureTheory.LocallyIntegrable u volume)
    (_ : MeasureTheory.LocallyIntegrable gi volume)
    (hweak : HasWeakPartialDerivOn U i u gi) {ε : ℝ} (hε : 0 < ε)
    {x : Vec d} (hx : Metric.closedBall x ε ⊆ U) :
    (fderiv ℝ (mollify u ε hε) x) (basisVec i) = mollify gi ε hε x := by
  let k : Vec d → ℝ := mollifier (d := d) ε hε
  let φ : Vec d → ℝ := fun y => k (x - y)
  have hk : ContDiff ℝ (⊤ : ℕ∞) k := mollifier_contDiff hε
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := by
    exact hk.comp (contDiff_const.sub contDiff_id)
  have hφSupport : HasCompactSupport φ := by
    simpa [φ, Function.comp_def] using
      (mollifier_hasCompactSupport (d := d) hε).comp_homeomorph (Homeomorph.subLeft x)
  have hφSubset : tsupport φ ⊆ U := by
    have hts : tsupport φ = (Homeomorph.subLeft x) ⁻¹' tsupport k := by
      simpa [φ, Function.comp_def] using
        (tsupport_comp_eq_preimage k (Homeomorph.subLeft x))
    rw [hts, show tsupport k = Metric.closedBall (0 : Vec d) ε by
      exact (standardMollifier (d := d) ε hε).tsupport_normed_eq]
    intro y hy
    apply hx
    change x - y ∈ Metric.closedBall (0 : Vec d) ε at hy
    rw [Metric.mem_closedBall, dist_zero_right] at hy
    rw [Metric.mem_closedBall, dist_eq_norm]
    calc
      ‖y - x‖ = ‖-(y - x)‖ := (norm_neg _).symm
      _ = ‖x - y‖ := by
        congr 1
        abel
      _ ≤ ε := hy
  have hfd := (mollifier_hasCompactSupport (d := d) hε).hasFDerivAt_convolution_left
    (L := ContinuousLinearMap.lsmul ℝ ℝ) (mollifier_contDiff hε (n := 1)) hu x
  rw [(by simpa [mollify] using hfd.fderiv :
    fderiv ℝ (mollify u ε hε) x =
      (MeasureTheory.convolution (fderiv ℝ (mollifier (d := d) ε hε)) u
        ((ContinuousLinearMap.lsmul ℝ ℝ).precompL (Vec d)) volume) x)]
  simp only [MeasureTheory.convolution, ContinuousLinearMap.lsmul_apply, mollify]
  dsimp [k]
  have hconv : ConvolutionExists (fderiv ℝ (mollifier (d := d) ε hε)) u
      ((ContinuousLinearMap.lsmul ℝ ℝ).precompL (Vec d)) volume := by
    exact HasCompactSupport.convolutionExists_left
      (𝕜 := ℝ) (G := Vec d) (E := Vec d →L[ℝ] ℝ) (E' := ℝ)
      (F := Vec d →L[ℝ] ℝ)
      ((ContinuousLinearMap.lsmul ℝ ℝ).precompL (Vec d))
      ((mollifier_hasCompactSupport (d := d) hε).fderiv (𝕜 := ℝ))
      ((mollifier_contDiff (d := d) hε (n := 2)).continuous_fderiv (by simp)) hu
  rw [ContinuousLinearMap.integral_apply (hconv x) (basisVec i)]
  simp only [ContinuousLinearMap.precompL_apply, ContinuousLinearMap.lsmul_apply]
  change (∫ t, (fderiv ℝ (mollifier (d := d) ε hε) t) (basisVec i) * u (x - t)
      ∂volume) =
    ∫ t, mollifier (d := d) ε hε t * gi (x - t) ∂volume
  have hφDeriv (y : Vec d) :
      (fderiv ℝ φ y) (basisVec i) =
        - (fderiv ℝ k (x - y)) (basisVec i) := by
    have hinner : HasFDerivAt (fun z : Vec d => x - z)
        (-(1 : Vec d →L[ℝ] Vec d)) y :=
      (hasFDerivAt_id y).const_sub x
    have houter : HasFDerivAt k (fderiv ℝ k (x - y)) (x - y) :=
      (hk.differentiable (by simp) (x - y)).hasFDerivAt
    have hcomp := houter.comp y hinner
    simpa [φ, Function.comp_def, ContinuousLinearMap.comp_apply] using
      congrArg (fun L : Vec d →L[ℝ] ℝ => L (basisVec i)) hcomp.fderiv
  have hφOutside : ∀ y, y ∉ U → φ y = 0 := by
    intro y hy
    exact image_eq_zero_of_notMem_tsupport (fun hy' => hy (hφSubset hy'))
  have hφDerivOutside : ∀ y, y ∉ U → (fderiv ℝ φ y) (basisVec i) = 0 := by
    intro y hy
    have hy' : y ∉ tsupport φ := fun hy' => hy (hφSubset hy')
    rw [fderiv_of_notMem_tsupport (𝕜 := ℝ) hy']
    simp
  have hweakGlobal :
      (∫ y, u y * (fderiv ℝ φ y) (basisVec i) ∂volume) =
        -∫ y, gi y * φ y ∂volume := by
    calc
      (∫ y, u y * (fderiv ℝ φ y) (basisVec i) ∂volume) =
          ∫ y in U, u y * (fderiv ℝ φ y) (basisVec i) ∂volume := by
        symm
        apply MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        intro y hy
        simp [hφDerivOutside y hy]
      _ = -∫ y in U, gi y * φ y ∂volume :=
        hweak φ hφ hφSupport hφSubset
      _ = -∫ y, gi y * φ y ∂volume := by
        congr 1
        apply MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        intro y hy
        simp [hφOutside y hy]
  have hchange :
      (∫ t, (fderiv ℝ (mollifier (d := d) ε hε) t) (basisVec i) * u (x - t)
          ∂volume) =
        ∫ y, u y * (fderiv ℝ (mollifier (d := d) ε hε) (x - y))
          (basisVec i) ∂volume := by
    calc
      (∫ t, (fderiv ℝ (mollifier (d := d) ε hε) t) (basisVec i) * u (x - t)
          ∂volume) =
          ∫ t, u (x - t) * (fderiv ℝ (mollifier (d := d) ε hε) t)
            (basisVec i) ∂volume := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [] with t
        ring
      _ = ∫ y, u y * (fderiv ℝ (mollifier (d := d) ε hε) (x - y))
          (basisVec i) ∂volume := by
        let F : Vec d → ℝ := fun y =>
          u y * (fderiv ℝ (mollifier (d := d) ε hε) (x - y)) (basisVec i)
        simpa [F, sub_sub_cancel] using
          (MeasureTheory.Measure.measurePreserving_sub_left volume x).integral_comp
            (Homeomorph.subLeft x).measurableEmbedding F
  have hright :
      (∫ t, mollifier (d := d) ε hε t * gi (x - t) ∂volume) =
        ∫ y, gi y * φ y ∂volume := by
    let F : Vec d → ℝ := fun y => φ y * gi y
    calc
      (∫ t, mollifier (d := d) ε hε t * gi (x - t) ∂volume) =
          ∫ t, F (x - t) ∂volume := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [] with t
        simp [F, φ, k]
      _ = ∫ y, F y ∂volume :=
        (MeasureTheory.Measure.measurePreserving_sub_left volume x).integral_comp
          (Homeomorph.subLeft x).measurableEmbedding F
      _ = ∫ y, gi y * φ y ∂volume := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [] with y
        simp [F, mul_comm]
  calc
    (∫ t, (fderiv ℝ (mollifier (d := d) ε hε) t) (basisVec i) * u (x - t)
        ∂volume) =
        ∫ y, u y * (fderiv ℝ (mollifier (d := d) ε hε) (x - y))
          (basisVec i) ∂volume := hchange
    _ = -∫ y, u y * (fderiv ℝ φ y) (basisVec i) ∂volume := by
      rw [show (fun y => u y * (fderiv ℝ (mollifier (d := d) ε hε) (x - y))
          (basisVec i)) =
          (fun y => -(u y * (fderiv ℝ φ y) (basisVec i))) by
            funext y
            rw [hφDeriv]
            ring]
      rw [MeasureTheory.integral_neg]
    _ = ∫ y, gi y * φ y ∂volume := by rw [hweakGlobal]; simp
    _ = ∫ t, mollifier (d := d) ε hε t * gi (x - t) ∂volume := hright.symm

theorem fderiv_mollify_eq_mollify_on_compact
    {d : ℕ} {U K : Set (Vec d)} (hU : IsOpen U) (_ : IsCompact K)
    {u gi : Vec d → ℝ} {i : Fin d} (hu : MeasureTheory.LocallyIntegrable u volume)
    (hgi : MeasureTheory.LocallyIntegrable gi volume)
    (hweak : HasWeakPartialDerivOn U i u gi) {ε : ℝ} (hε : 0 < ε)
    (hK : ∀ x ∈ K, Metric.closedBall x ε ⊆ U) {x : Vec d} (hx : x ∈ K) :
    (fderiv ℝ (mollify u ε hε) x) (basisVec i) = mollify gi ε hε x := by
  exact fderiv_mollify_eq_mollify_of_hasWeakPartialDerivOn
    hU hu hgi hweak hε (hK x hx)

end CKN
