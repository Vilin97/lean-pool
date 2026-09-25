/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Mollify.Transport

/-!
# The mollified weak-derivative identity as an explicit integral

Adapted from PDEFoundation (EllipticRegularity, 2026) with the author's
permission. Integrating the derivative of the normalized bump kernel against
`u` reproduces the mollification of a weak partial derivative of `u`, at every
point whose closed `ε`-ball lies in the domain of the weak derivative. The
result is the integral form of the transport identity, stated on its own so
that it can be used without unfolding the convolution derivative.
-/

@[expose] public section

open scoped Convolution Topology
open MeasureTheory


noncomputable section

namespace CKN

/-- Integrating the mollifier's derivative against `u` reproduces the mollification of a weak
partial derivative `gi` of `u`, at every point whose closed `ε`-ball lies in the domain. -/
theorem integral_fderiv_mollifier_mul_eq_mollify
    {d : ℕ} {U : Set (Vec d)} {u gi : Vec d → ℝ} {i : Fin d}
    (_ : MeasureTheory.LocallyIntegrable u MeasureTheory.volume)
    (_ : MeasureTheory.LocallyIntegrable gi MeasureTheory.volume)
    (hweak : HasWeakPartialDerivOn U i u gi) {ε : ℝ} (hε : 0 < ε) {x : Vec d}
    (hx : Metric.closedBall x ε ⊆ U) :
    (∫ y, (fderiv ℝ (mollifier (d := d) ε hε) y) (basisVec i) * u (x - y)
        ∂MeasureTheory.volume) = mollify gi ε hε x := by
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
  have hmoll :
      mollify gi ε hε x =
        ∫ t, mollifier (d := d) ε hε t * gi (x - t) ∂MeasureTheory.volume := by
    simp only [mollify, MeasureTheory.convolution, ContinuousLinearMap.lsmul_apply,
      smul_eq_mul]
  rw [hmoll]
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

end CKN

end
