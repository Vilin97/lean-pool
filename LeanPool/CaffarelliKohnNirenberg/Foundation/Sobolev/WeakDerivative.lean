/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Measure.RestrictedVolume
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.TestFunction
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Weak first derivatives on native vector domains

Adapted from PDEFoundation (EllipticRegularity, 2026) with the author's
permission. This port preserves the raw integration-by-parts predicates,
a.e. uniqueness, restriction, and smooth-function constructors, while using
the `CKN` namespace and the reduced weak-derivative dependency surface.
-/

public section

namespace CKN

/-- `gi` is the `i`th weak derivative of `u` on `U`. -/
@[expose]
def HasWeakPartialDerivOn {d : ℕ} (U : Set (Vec d)) (i : Fin d)
    (u gi : Vec d → ℝ) : Prop :=
  ∀ φ : Vec d → ℝ,
    ContDiff ℝ (⊤ : ℕ∞) φ →
    HasCompactSupport φ →
    tsupport φ ⊆ U →
    ∫ x in U, u x * (fderiv ℝ φ x) (basisVec i) ∂MeasureTheory.volume =
      -∫ x in U, gi x * φ x ∂MeasureTheory.volume

/-- `Du` is a coordinate weak gradient of `u` on `U`. -/
@[expose]
def HasWeakGradientOn {d : ℕ}
    (U : Set (Vec d)) (u : Vec d → ℝ) (Du : Vec d → Vec d) : Prop :=
  ∀ i : Fin d, HasWeakPartialDerivOn U i u (fun x => Du x i)

theorem hasWeakPartialDerivOn_iff_forall_testFunction
    {d : ℕ} {U : Set (Vec d)} {i : Fin d}
    {u gi : Vec d → ℝ} :
    HasWeakPartialDerivOn U i u gi ↔
      ∀ φ : WeakTestFunction U,
        ∫ x in U, u x * φ.partialDeriv i x ∂MeasureTheory.volume =
          -∫ x in U, gi x * φ x ∂MeasureTheory.volume := by
  constructor
  · intro h φ
    exact h φ.toFun φ.contDiff φ.hasCompactSupport φ.tsupport_subset
  · intro h φ hφSmooth hφCompact hφSupport
    exact h
      { toFun := φ
        contDiff := hφSmooth
        hasCompactSupport := hφCompact
        tsupport_subset := hφSupport }

namespace HasWeakPartialDerivOn

/-- Locally integrable weak partial derivatives are unique almost everywhere. -/
theorem ae_eq {d : ℕ} {U : Set (Vec d)} (hU : IsOpen U)
    {i : Fin d} {u gi hi : Vec d → ℝ}
    (hgiLoc : MeasureTheory.LocallyIntegrableOn gi U MeasureTheory.volume)
    (hhiLoc : MeasureTheory.LocallyIntegrableOn hi U MeasureTheory.volume)
    (hgi : HasWeakPartialDerivOn U i u gi)
    (hhi : HasWeakPartialDerivOn U i u hi) :
    gi =ᵐ[volumeOn U] hi := by
  have hdiffZero :
      ∀ᵐ x ∂MeasureTheory.volume, x ∈ U → gi x - hi x = 0 := by
    refine hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (f := fun x => gi x - hi x) (hgiLoc.sub hhiLoc) ?_
    intro φ hφSmooth hφCompact hφSub
    have hφCont : Continuous φ := hφSmooth.continuous
    have hgiK :
        MeasureTheory.IntegrableOn gi (tsupport φ) MeasureTheory.volume :=
      hgiLoc.integrableOn_compact_subset hφSub hφCompact.isCompact
    have hhiK :
        MeasureTheory.IntegrableOn hi (tsupport φ) MeasureTheory.volume :=
      hhiLoc.integrableOn_compact_subset hφSub hφCompact.isCompact
    have hgiφK :
        MeasureTheory.IntegrableOn (fun x => gi x * φ x) (tsupport φ)
          MeasureTheory.volume := by
      simpa [smul_eq_mul] using
        hgiK.smul_continuousOn hφCont.continuousOn hφCompact.isCompact
    have hhiφK :
        MeasureTheory.IntegrableOn (fun x => hi x * φ x) (tsupport φ)
          MeasureTheory.volume := by
      simpa [smul_eq_mul] using
        hhiK.smul_continuousOn hφCont.continuousOn hφCompact.isCompact
    have hgiφZero :
        ∀ x ∈ U \ tsupport φ, gi x * φ x = 0 := by
      intro x hx
      simp [image_eq_zero_of_notMem_tsupport hx.2]
    have hhiφZero :
        ∀ x ∈ U \ tsupport φ, hi x * φ x = 0 := by
      intro x hx
      simp [image_eq_zero_of_notMem_tsupport hx.2]
    have hgiInt :
        MeasureTheory.Integrable (fun x => gi x * φ x) (volumeOn U) := by
      simpa [MeasureTheory.IntegrableOn, volumeOn] using
        hgiφK.of_forall_sdiff_eq_zero hU.measurableSet hgiφZero
    have hhiInt :
        MeasureTheory.Integrable (fun x => hi x * φ x) (volumeOn U) := by
      simpa [MeasureTheory.IntegrableOn, volumeOn] using
        hhiφK.of_forall_sdiff_eq_zero hU.measurableSet hhiφZero
    have hsetEq :
        ∫ x in U, gi x * φ x ∂MeasureTheory.volume =
          ∫ x in U, hi x * φ x ∂MeasureTheory.volume := by
      have hgi' := hgi φ hφSmooth hφCompact hφSub
      have hhi' := hhi φ hφSmooth hφCompact hφSub
      apply neg_injective
      rw [← hgi', ← hhi']
    have hsetZero :
        ∫ x in U, φ x * (gi x - hi x) ∂MeasureTheory.volume = 0 := by
      calc
        ∫ x in U, φ x * (gi x - hi x) ∂MeasureTheory.volume =
            ∫ x in U, (gi x * φ x - hi x * φ x)
              ∂MeasureTheory.volume := by
                apply MeasureTheory.setIntegral_congr_fun hU.measurableSet
                intro x hx
                ring
        _ = ∫ x in U, gi x * φ x ∂MeasureTheory.volume -
              ∫ x in U, hi x * φ x ∂MeasureTheory.volume := by
                rw [MeasureTheory.integral_sub hgiInt hhiInt]
        _ = 0 := by rw [hsetEq, sub_self]
    have hzeroOut :
        ∀ x, x ∉ U → φ x * (gi x - hi x) = 0 := by
      intro x hx
      have hxNotIn : x ∉ tsupport φ := fun hx' => hx (hφSub hx')
      simp [image_eq_zero_of_notMem_tsupport hxNotIn]
    calc
      ∫ x, φ x • (gi x - hi x) ∂MeasureTheory.volume =
          ∫ x, φ x * (gi x - hi x) ∂MeasureTheory.volume := by
            simp [smul_eq_mul]
      _ = ∫ x in U, φ x * (gi x - hi x) ∂MeasureTheory.volume := by
            rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
              hzeroOut]
      _ = 0 := hsetZero
  rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' hU.measurableSet]
  filter_upwards [hdiffZero] with x hx hxu
  exact sub_eq_zero.mp (hx hxu)

end HasWeakPartialDerivOn

theorem HasWeakPartialDerivOn.restrict {d : ℕ}
    {U V : Set (Vec d)} (_ : IsOpen V) (hVU : V ⊆ U)
    {i : Fin d} {u gi : Vec d → ℝ}
    (h : HasWeakPartialDerivOn U i u gi) :
    HasWeakPartialDerivOn V i u gi := by
  intro φ hφSmooth hφCompact hφSupport
  have hφSupportU : tsupport φ ⊆ U := hφSupport.trans hVU
  have hWeak := h φ hφSmooth hφCompact hφSupportU
  have hValueZero :
      ∀ x, x ∉ V → u x * (fderiv ℝ φ x) (basisVec i) = 0 := by
    intro x hx
    have hxNotIn : x ∉ tsupport φ := fun hx' => hx (hφSupport hx')
    have hφEq : φ =ᶠ[nhds x] 0 :=
      (isClosed_tsupport (f := φ)).isOpen_compl.eventually_mem hxNotIn |>.mono
        (fun y hy => image_eq_zero_of_notMem_tsupport hy)
    rw [Filter.EventuallyEq.fderiv_eq hφEq]
    simp
  have hGradZero :
      ∀ x, x ∉ V → gi x * φ x = 0 := by
    intro x hx
    simp [image_eq_zero_of_notMem_tsupport
      (fun hx' => hx (hφSupport hx'))]
  have hValueZeroU :
      ∀ x, x ∉ U → u x * (fderiv ℝ φ x) (basisVec i) = 0 :=
    fun x hx => hValueZero x (fun hx' => hx (hVU hx'))
  have hGradZeroU :
      ∀ x, x ∉ U → gi x * φ x = 0 :=
    fun x hx => hGradZero x (fun hx' => hx (hVU hx'))
  rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        hValueZero,
    MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hGradZero,
    ← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        hValueZeroU,
    ← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        hGradZeroU,
    hWeak]

theorem HasWeakGradientOn.restrict {d : ℕ}
    {U V : Set (Vec d)} (hVOpen : IsOpen V) (hVU : V ⊆ U)
    {u : Vec d → ℝ} {Du : Vec d → Vec d}
    (h : HasWeakGradientOn U u Du) :
    HasWeakGradientOn V u Du := by
  intro i
  exact (h i).restrict hVOpen hVU

theorem HasWeakPartialDerivOn.of_contDiff {d : ℕ}
    {U : Set (Vec d)} {i : Fin d} {f : Vec d → ℝ}
    (hf : ContDiff ℝ 1 f) :
    HasWeakPartialDerivOn U i f
      (fun x => (fderiv ℝ f x) (basisVec i)) := by
  intro φ hφSmooth hφSupport hφSubset
  let ei : Vec d := basisVec i
  have hfDiff : Differentiable ℝ f := hf.differentiable (by simp)
  have hφDiff : Differentiable ℝ φ :=
    hφSmooth.differentiable (by simp)
  have hfCont : Continuous f := hfDiff.continuous
  have hφCont : Continuous φ := hφDiff.continuous
  have hfderivφCont :
      Continuous (fun x => (fderiv ℝ φ x) ei) := by
    simpa [ei] using
      (hφSmooth.continuous_fderiv (by simp)).clm_apply continuous_const
  have hfderivfCont :
      Continuous (fun x => (fderiv ℝ f x) ei) := by
    simpa [ei] using
      (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hφFderivSupport :
      HasCompactSupport (fun x => (fderiv ℝ φ x) ei) := by
    simpa [ei] using hφSupport.fderiv_apply (𝕜 := ℝ) ei
  rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero,
    MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero]
  · simpa [ei] using
      integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
        ((hfderivfCont.mul hφCont).integrable_of_hasCompactSupport
          hφSupport.mul_left)
        ((hfCont.mul hfderivφCont).integrable_of_hasCompactSupport
          hφFderivSupport.mul_left)
        ((hfCont.mul hφCont).integrable_of_hasCompactSupport
          hφSupport.mul_left)
        (fun x _hx => hfDiff x) (fun x _hx => hφDiff x)
  · intro x hx
    have hxNotIn : x ∉ tsupport φ := fun hx' => hx (hφSubset hx')
    simp [image_eq_zero_of_notMem_tsupport hxNotIn]
  · intro x hx
    have hxNotIn : x ∉ tsupport φ := fun hx' => hx (hφSubset hx')
    have hφEq : φ =ᶠ[nhds x] 0 :=
      (isClosed_tsupport (f := φ)).isOpen_compl.eventually_mem hxNotIn |>.mono
        (fun y hy => image_eq_zero_of_notMem_tsupport hy)
    rw [Filter.EventuallyEq.fderiv_eq hφEq]
    simp

theorem HasWeakGradientOn.of_contDiff {d : ℕ}
    {U : Set (Vec d)} {f : Vec d → ℝ}
    (hf : ContDiff ℝ 1 f) :
    HasWeakGradientOn U f
      (fun x i => (fderiv ℝ f x) (basisVec i)) := by
  intro i
  exact HasWeakPartialDerivOn.of_contDiff hf

end CKN
