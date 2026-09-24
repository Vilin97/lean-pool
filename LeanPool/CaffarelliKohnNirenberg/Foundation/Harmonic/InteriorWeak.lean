/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.InteriorGradient
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Mollify.Basic
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Mollify.LpApproximation
public import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Interior Weak

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open scoped BigOperators ENNReal NNReal Topology Convolution
open MeasureTheory MeasureTheory.Measure Set Filter
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Foundation.Heat

/-! Distributional harmonicity and the mollifier identities used below. -/

/-- A locally integrable function is weakly harmonic when its Laplacian pairing
with every compactly supported smooth test function vanishes. -/
def WeaklyHarmonicOn (U : Set Vec3) (h : Vec3 → ℝ) : Prop :=
  ∀ ψ : Vec3 → ℝ,
    ContDiff ℝ (⊤ : ℕ∞) ψ →
    HasCompactSupport ψ →
    tsupport ψ ⊆ U →
    ∫ y in U, h y * CKN.spatialLaplacian ψ y = 0

private lemma mollifier_second_direction_formula
    {g : Vec3 → ℝ} (hg : LocallyIntegrable g volume)
    {ε : ℝ} (hε : 0 < ε) (x : Vec3) (i : Fin 3) :
    (fderiv ℝ (CKN.spatialDeriv (mollify g ε hε) i) x)
        (basisVec i) =
      ∫ t : Vec3, g (x - t) *
        ((fderiv ℝ (fderiv ℝ (mollifier (d := 3) ε hε)) t)
          (basisVec i)) (basisVec i) := by
  let k : Vec3 → ℝ := mollifier (d := 3) ε hε
  let ki : Vec3 → ℝ := fun t => (fderiv ℝ k t) (basisVec i)
  have hk : ContDiff ℝ (⊤ : ℕ∞) k := mollifier_contDiff hε
  have hki : ContDiff ℝ (1 : ℕ∞) ki := by
    have h := hk.contDiff_fderiv_apply (m := (1 : ℕ∞))
      (n := (⊤ : ℕ∞)) (by simp)
    have hc : ContDiff ℝ (1 : ℕ∞)
        (fun z : Vec3 => (z, basisVec i)) := by
      fun_prop
    simpa only [ki, Function.comp_def] using h.comp hc
  have hkisupp : HasCompactSupport ki := by
    simpa only [ki] using
      ((mollifier_hasCompactSupport hε).fderiv_apply
        (𝕜 := ℝ) (basisVec i))
  have hkiD := hkisupp.hasFDerivAt_convolution_left
    (L := ContinuousLinearMap.lsmul ℝ ℝ) hki hg x
  have hconvKi := (hkisupp.fderiv (𝕜 := ℝ)).convolutionExists_left
    (L := (ContinuousLinearMap.lsmul ℝ ℝ).precompL (Vec 3))
    (hki.continuous_fderiv (by norm_num)) hg
  have hDk : ContDiff ℝ (1 : ℕ∞) (fderiv ℝ k) := by
    exact hk.fderiv_right (by simp)
  have hDcompact : HasCompactSupport (fderiv ℝ k) :=
    (mollifier_hasCompactSupport hε).fderiv (𝕜 := ℝ)
  have hconvD := hDcompact.convolutionExists_left
    (L := (ContinuousLinearMap.lsmul ℝ ℝ).precompL (Vec 3))
    hDk.continuous hg
  have hcoord : (fun z : Vec3 =>
      (fderiv ℝ (mollify g ε hε) z) (basisVec i)) =
      MeasureTheory.convolution ki g
        (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
    funext z
    have hz := (mollifier_hasCompactSupport hε).hasFDerivAt_convolution_left
      (L := ContinuousLinearMap.lsmul ℝ ℝ)
      (mollifier_contDiff hε (n := 1)) hg z
    rw [show mollify g ε hε =
        MeasureTheory.convolution k g
          (ContinuousLinearMap.lsmul ℝ ℝ) volume by rfl]
    rw [hz.fderiv]
    rw [MeasureTheory.convolution_def]
    rw [ContinuousLinearMap.integral_apply (hconvD z)]
    simp [MeasureTheory.convolution_def, ki, ContinuousLinearMap.precompL_apply,
      ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  have heq : CKN.spatialDeriv (mollify g ε hε) i =
      MeasureTheory.convolution ki g
        (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
    change (fun z : Vec3 => (fderiv ℝ (mollify g ε hε) z)
      (basisVec i)) = _
    exact hcoord
  have hscalar := hkiD
  change HasFDerivAt
    (MeasureTheory.convolution ki g
      (ContinuousLinearMap.lsmul ℝ ℝ) volume) _ x at hscalar
  rw [← heq] at hscalar
  have hkiDeriv (t : Vec3) :
      (fderiv ℝ ki t) (basisVec i) =
        (fderiv ℝ (fderiv ℝ k) t (basisVec i))
          (basisVec i) := by
    have hfd : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ k) :=
      (contDiff_infty_iff_fderiv.mp hk).2
    have hdiff : DifferentiableAt ℝ (fderiv ℝ k) t :=
      (hfd.differentiable (by simp)) t
    have hcomp := hdiff.hasFDerivAt.clm_apply
      (hasFDerivAt_const (x := t) (basisVec i))
    have hfa' := congrArg
      (fun L : Vec3 →L[ℝ] ℝ => L (basisVec i)) hcomp.fderiv
    simpa [ki, ContinuousLinearMap.comp_apply] using hfa'
  have hi := congrArg (fun L : Vec3 →L[ℝ] ℝ => L (basisVec i))
    hscalar.fderiv
  rw [MeasureTheory.convolution_def] at hi
  rw [ContinuousLinearMap.integral_apply (hconvKi x)] at hi
  simpa [ki, ContinuousLinearMap.precompL_apply,
    ContinuousLinearMap.lsmul_apply, smul_eq_mul, hkiDeriv, mul_comm] using hi

private lemma mollify_spatialLaplacian_eq_zero
    {U : Set Vec3} {g : Vec3 → ℝ} (hg : LocallyIntegrable g volume)
    (hweak : ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      HasCompactSupport ψ → tsupport ψ ⊆ U →
      ∫ y, g y * CKN.spatialLaplacian ψ y = 0)
    {ε : ℝ} (hε : 0 < ε) {x : Vec3}
    (hx : Metric.closedBall x ε ⊆ U) :
    CKN.spatialLaplacian (mollify g ε hε) x = 0 := by
  let k : Vec3 → ℝ := mollifier (d := 3) ε hε
  let φ : Vec3 → ℝ := fun y => k (x - y)
  have hk : ContDiff ℝ (⊤ : ℕ∞) k := mollifier_contDiff hε
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := by
    exact hk.comp (contDiff_const.sub contDiff_id)
  have hφSupport : HasCompactSupport φ := by
    simpa [φ, Function.comp_def] using
      (mollifier_hasCompactSupport hε).comp_homeomorph (Homeomorph.subLeft x)
  have hφSubset : tsupport φ ⊆ U := by
    have hts : tsupport φ = (Homeomorph.subLeft x) ⁻¹' tsupport k := by
      simpa [φ, Function.comp_def] using
        (tsupport_comp_eq_preimage k (Homeomorph.subLeft x))
    rw [hts, show tsupport k = Metric.closedBall (0 : Vec3) ε by
      exact (standardMollifier (d := 3) ε hε).tsupport_normed_eq]
    intro y hy
    apply hx
    change x - y ∈ Metric.closedBall (0 : Vec3) ε at hy
    rw [Metric.mem_closedBall, dist_zero_right] at hy
    rw [Metric.mem_closedBall, dist_eq_norm]
    calc
      ‖y - x‖ = ‖-(y - x)‖ := (norm_neg _).symm
      _ = ‖x - y‖ := by congr 1; abel
      _ ≤ ε := hy
  have hφDeriv (y : Vec3) (i : Fin 3) :
      (fderiv ℝ φ y) (basisVec i) =
        - (fderiv ℝ k (x - y)) (basisVec i) := by
    have hinner : HasFDerivAt (fun z : Vec3 => x - z)
        (-(1 : Vec3 →L[ℝ] Vec3)) y :=
      (hasFDerivAt_id y).const_sub x
    have houter : HasFDerivAt k (fderiv ℝ k (x - y)) (x - y) :=
      (hk.differentiable (by simp) (x - y)).hasFDerivAt
    have hcomp := houter.comp y hinner
    simpa [φ, Function.comp_def, ContinuousLinearMap.comp_apply] using
      congrArg (fun L : Vec3 →L[ℝ] ℝ => L (basisVec i)) hcomp.fderiv
  have hsecond (y : Vec3) (i : Fin 3) :
      (fderiv ℝ (CKN.spatialDeriv φ i) y) (basisVec i) =
        ((fderiv ℝ (fderiv ℝ k) (x - y)) (basisVec i)) (basisVec i) := by
    have hcoord : CKN.spatialDeriv φ i =
        (fun z : Vec3 => - (fderiv ℝ k (x - z)) (basisVec i)) := by
      funext z
      exact hφDeriv z i
    have hfd : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ k) :=
      (contDiff_infty_iff_fderiv.mp hk).2
    have hdiff : DifferentiableAt ℝ (fderiv ℝ k) (x - y) :=
      (hfd.differentiable (by simp)) (x - y)
    have hinner : HasFDerivAt (fun z : Vec3 => x - z)
        (-(1 : Vec3 →L[ℝ] Vec3)) y :=
      (hasFDerivAt_id y).const_sub x
    have hcomp := hdiff.hasFDerivAt.clm_apply
      (hasFDerivAt_const (x := x - y) (basisVec i))
    have hcomp' := hcomp.comp y hinner
    have hfa := congrArg
      (fun L : Vec3 →L[ℝ] ℝ => L (basisVec i)) hcomp'.fderiv
    have hfa' :
        (fderiv ℝ (fun z : Vec3 =>
          (fderiv ℝ k (x - z)) (basisVec i)) y) (basisVec i) =
          -((fderiv ℝ (fderiv ℝ k) (x - y)) (basisVec i))
            (basisVec i) := by
      simpa [Function.comp_def, ContinuousLinearMap.comp_apply] using hfa
    have hcoordfd := congrArg (fun f : Vec3 → ℝ => fderiv ℝ f y) hcoord
    have hcoordapply := congrArg
      (fun L : Vec3 →L[ℝ] ℝ => L (basisVec i)) hcoordfd
    rw [hcoordapply]
    rw [show (fun z : Vec3 => -(fderiv ℝ k (x - z)) (basisVec i)) =
        -(fun z : Vec3 => (fderiv ℝ k (x - z)) (basisVec i)) by
          funext z; simp, fderiv_neg]
    change -((fderiv ℝ (fun z : Vec3 =>
      (fderiv ℝ k (x - z)) (basisVec i)) y) (basisVec i)) = _
    rw [hfa']
    ring
  have hzero : ∫ y, g y * CKN.spatialLaplacian φ y = 0 :=
    hweak φ hφ hφSupport hφSubset
  have hchange (i : Fin 3) :
      ∫ y, g y * (fderiv ℝ (CKN.spatialDeriv φ i) y) (basisVec i) =
        ∫ t, g (x - t) *
          ((fderiv ℝ (fderiv ℝ k) t) (basisVec i)) (basisVec i) := by
    have hleft : (fun y : Vec3 =>
        g y * (fderiv ℝ (CKN.spatialDeriv φ i) y) (basisVec i)) =
        (fun y : Vec3 => g y *
          (((fderiv ℝ (fderiv ℝ k) (x - y)) (basisVec i)) (basisVec i))) := by
      funext y
      rw [hsecond y i]
    rw [hleft]
    let F : Vec3 → ℝ := fun y => g (x - y) *
      ((fderiv ℝ (fderiv ℝ k) y) (basisVec i)) (basisVec i)
    simpa [F, sub_sub_cancel] using
      (Measure.measurePreserving_sub_left (volume : Measure Vec3) x).integral_comp
        (Homeomorph.subLeft x).measurableEmbedding F
  have hsum : ∫ y, g y * CKN.spatialLaplacian φ y =
      ∑ i : Fin 3, ∫ y, g y *
        (fderiv ℝ (CKN.spatialDeriv φ i) y) (basisVec i) := by
    have hInt (i : Fin 3) : Integrable (fun y : Vec3 => g y *
        (fderiv ℝ (CKN.spatialDeriv φ i) y) (basisVec i)) volume := by
      let q : Vec3 → ℝ := fun y =>
        (fderiv ℝ (CKN.spatialDeriv φ i) y) (basisVec i)
      have hqCont : Continuous q := by
        exact (contDiff_spatialDeriv_smooth
          (contDiff_spatialDeriv_smooth hφ i) i).continuous
      have hfirstSupport : HasCompactSupport (CKN.spatialDeriv φ i) := by
        change HasCompactSupport (fun y : Vec3 =>
          (fderiv ℝ φ y) (basisVec i))
        exact hφSupport.fderiv_apply (𝕜 := ℝ) (basisVec i)
      have hqSupport : HasCompactSupport q := by
        simpa only [q] using
          (hfirstSupport.fderiv_apply (𝕜 := ℝ) (basisVec i))
      have hqK : IntegrableOn g (tsupport q) volume :=
        hg.integrableOn_isCompact hqSupport.isCompact
      have hprodK : IntegrableOn (fun y : Vec3 => g y * q y)
          (tsupport q) volume :=
        hqK.mul_continuousOn hqCont.continuousOn hqSupport.isCompact
      have hprod : Integrable (fun y : Vec3 => g y * q y) volume :=
        hprodK.integrable_of_forall_notMem_eq_zero (fun y hy => by
          rw [image_eq_zero_of_notMem_tsupport hy, mul_zero])
      simpa [q] using hprod
    simp only [CKN.spatialLaplacian, spatialDeriv, Fin.sum_univ_three]
    simp_rw [mul_add]
    change (∫ y, (g y * (fderiv ℝ (CKN.spatialDeriv φ 0) y)
        (basisVec 0) + g y * (fderiv ℝ (CKN.spatialDeriv φ 1) y)
        (basisVec 1)) + g y * (fderiv ℝ (CKN.spatialDeriv φ 2) y)
        (basisVec 2)) = _
    calc
      _ = (∫ y, g y * (fderiv ℝ (CKN.spatialDeriv φ 0) y)
          (basisVec 0) + g y * (fderiv ℝ (CKN.spatialDeriv φ 1) y)
          (basisVec 1)) + ∫ y, g y *
          (fderiv ℝ (CKN.spatialDeriv φ 2) y) (basisVec 2) :=
        MeasureTheory.integral_add ((hInt 0).add (hInt 1)) (hInt 2)
      _ = _ := by
        rw [MeasureTheory.integral_add (hInt 0) (hInt 1)]
  have hzero' : ∑ i : Fin 3, ∫ y, g y *
      (fderiv ℝ (CKN.spatialDeriv φ i) y) (basisVec i) = 0 := by
    rw [← hsum]
    exact hzero
  have hzero'' : ∑ i : Fin 3, ∫ t, g (x - t) *
      ((fderiv ℝ (fderiv ℝ k) t) (basisVec i)) (basisVec i) = 0 := by
    calc
      _ = ∑ i : Fin 3, ∫ y, g y *
          (fderiv ℝ (CKN.spatialDeriv φ i) y) (basisVec i) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact (hchange i).symm
      _ = 0 := hzero'
  calc
    CKN.spatialLaplacian (mollify g ε hε) x =
        ∑ i : Fin 3, (fderiv ℝ
          (CKN.spatialDeriv (mollify g ε hε) i) x) (basisVec i) := rfl
    _ = ∑ i : Fin 3, ∫ t, g (x - t) *
        ((fderiv ℝ (fderiv ℝ k) t) (basisVec i)) (basisVec i) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact mollifier_second_direction_formula hg hε x i
    _ = 0 := hzero''

theorem weaklyHarmonicOn_mollify_spatialLaplacian_eq_zero
    {U : Set Vec3} (hU : MeasurableSet U) {h : Vec3 → ℝ}
    (hmem : MemLp h (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict U))
    (hweak : WeaklyHarmonicOn U h) {ε : ℝ} (hε : 0 < ε)
    {x : Vec3} (hx : Metric.closedBall x ε ⊆ U) :
    CKN.spatialLaplacian (mollify (U.indicator h) ε hε) x = 0 := by
  let g : Vec3 → ℝ := U.indicator h
  have hgmem : MemLp g (ENNReal.ofReal (3 / 2 : ℝ)) volume := by
    exact (memLp_indicator_iff_restrict hU).2 hmem
  have hgloc : LocallyIntegrable g volume :=
    hgmem.locallyIntegrable (by norm_num)
  have hweakGlobal : ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      HasCompactSupport ψ → tsupport ψ ⊆ U →
      ∫ y, g y * CKN.spatialLaplacian ψ y = 0 := by
    intro ψ hψ hsupp hsub
    have hind : (fun y : Vec3 => U.indicator h y *
        CKN.spatialLaplacian ψ y) =
        U.indicator (fun y => h y * CKN.spatialLaplacian ψ y) := by
      funext y
      by_cases hy : y ∈ U <;> simp [hy]
    rw [show g = U.indicator h by rfl, hind, integral_indicator hU]
    exact hweak ψ hψ hsupp hsub
  exact mollify_spatialLaplacian_eq_zero hgloc hweakGlobal hε hx

end CKN.Foundation.Heat
