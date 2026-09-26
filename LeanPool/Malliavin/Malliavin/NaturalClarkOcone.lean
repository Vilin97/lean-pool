/-
Copyright (c) 2026 The lean-malliavin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-malliavin contributors
-/
module

public import LeanPool.Malliavin.Malliavin.KernelIdentification

/-!
# The remaining inputs for the natural Clark--Ocone family

This file records exact formulations of the analytic inputs still required to construct a
`ClarkOconeFamily` from the natural Brownian Itô integral.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace

noncomputable
section

namespace Malliavin

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
/-- The interval kernel used for elementary predictable processes is the difference of the two
initial-interval kernels. -/
theorem iocIndicator_eq_intervalIndicator_sub
    (hB : IsPreBrownianReal B P) {a b : ℝ≥0} (hab : a ≤ b) :
    iocIndicator a b = intervalIndicator b - intervalIndicator a := by
  apply (wienerIntegralₗᵢ hB).injective
  change wienerIntegral hB (iocIndicator a b) =
    wienerIntegral hB (intervalIndicator b - intervalIndicator a)
  rw [iocIndicator, wienerIntegral_indicatorConstLp_Ioc hB hab, map_sub,
    wienerIntegral_intervalIndicator, wienerIntegral_intervalIndicator]

/-- Conditional expectation onto constants, bundled as a continuous linear map. -/
noncomputable def expectationL2CLM : RandomL2 P →L[ℝ] RandomL2 P :=
  (Lp.constL 2 P ℝ).comp (CameronMartin.expectationMap P)

omit [CompleteSpace W] [BorelSpace W] [SecondCountableTopology W] in
@[simp]
theorem expectationL2CLM_apply (G : RandomL2 P) :
    expectationL2CLM G = expectationL2 G := by
  rw [expectationL2CLM, ContinuousLinearMap.comp_apply,
    CameronMartin.expectationMap_apply, expectationL2, Lp.constL_apply]

/-- Subtract expectation, bundled as a continuous linear map. -/
noncomputable def centeredPartCLM : RandomL2 P →L[ℝ] RandomL2 P :=
  ContinuousLinearMap.id ℝ (RandomL2 P) - expectationL2CLM

omit [CompleteSpace W] [BorelSpace W] [SecondCountableTopology W] in
@[simp]
theorem centeredPartCLM_apply (G : RandomL2 P) :
    centeredPartCLM G = G - expectationL2 G := by
  rw [centeredPartCLM, sub_apply,
    ContinuousLinearMap.id_apply, expectationL2CLM_apply]

/-- The concrete Clark--Ocone identity restricted to the smooth core used to define `D12`. -/
def SmoothNaturalClarkOcone
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm) : Prop :=
  ∀ (G : W → ℝ) (hG : IsSmoothBounded G),
    hG.toLp P = expectationL2 (hG.toLp P) +
      naturalItoIntegral hB hsm hnat
        (predictableProjection 𝓅
          (Malliavin.timeDerivative hB coordinate coordinate_apply generated
            (hG.mderivLp P)))

/-- Malliavin--Itô duality restricted to the smooth core used to define `D12`. -/
def SmoothNaturalItoDuality
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm) : Prop :=
  ∀ (G : W → ℝ) (hG : IsSmoothBounded G) (U : PredictableProcessL2 𝓅 P),
    inner ℝ (hG.toLp P - expectationL2 (hG.toLp P))
        (naturalItoIntegral hB hsm hnat U) =
      inner ℝ
        (predictableProjection 𝓅
          (Malliavin.timeDerivative hB coordinate coordinate_apply generated
            (hG.mderivLp P))) U

/-- Smooth-core duality restricted further to one-step adapted predictable processes. -/
def SmoothElementaryNaturalItoDuality
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm) : Prop :=
  ∀ (G : W → ℝ) (hG : IsSmoothBounded G) (a b : ℝ≥0) (hab : a ≤ b)
    (Z : lpMeas ℝ ℝ (𝓅 a) 2 P),
    inner ℝ (hG.toLp P - expectationL2 (hG.toLp P))
        (elementaryBrownianValue hB hsm hnat hab Z) =
      inner ℝ
        (predictableProjection 𝓅
          (Malliavin.timeDerivative hB coordinate coordinate_apply generated
            (hG.mderivLp P)))
        (elementaryPredictable 𝓅 a b Z)

/-- A smooth bounded function of finitely many Brownian coordinates from times at most `a`,
regarded as an `L²` coefficient measurable at time `a`. -/
noncomputable def pastCylinderLpMeas
    (_hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    {n : ℕ} (f : (Fin n → ℝ) → ℝ) (hf : ContDiff ℝ 1 f)
    (hb : ∃ C, ∀ y, |f y| ≤ C)
    (hb' : ∃ C, ∀ y, ‖fderiv ℝ f y‖ ≤ C)
    (t : Fin n → ℝ≥0) (a : ℝ≥0) (ht : ∀ i, t i ≤ a) :
    lpMeas ℝ ℝ (𝓅 a) 2 P := by
  let hZ := isSmoothBounded_cylinder coordinate coordinate_apply f hf hb hb' t
  refine ⟨hZ.toLp P, ?_⟩
  rw [mem_lpMeas_iff_aestronglyMeasurable]
  have hcoord (i : Fin n) : Measurable[𝓅 a] (B (t i)) := by
    apply measurable_iff_comap_le.mpr
    rw [hnat]
    exact le_iSup₂
      (f := fun (j : ℝ≥0) (_ : j ≤ a) ↦
        MeasurableSpace.comap (B j) inferInstance) (t i) (ht i)
  have hvec : Measurable[𝓅 a] (fun w ↦ fun i ↦ B (t i) w) :=
    by
      let _ : MeasurableSpace W := 𝓅 a
      exact measurable_pi_iff.mpr hcoord
  have hZmeas : StronglyMeasurable[𝓅 a]
      (fun w ↦ f (fun i ↦ B (t i) w)) :=
    (hf.continuous.measurable.comp hvec).stronglyMeasurable
  exact hZmeas.aestronglyMeasurable.congr
    (MemLp.coeFn_toLp (hZ.memLp P 2)).symm

/-- Malliavin--Itô duality against an elementary predictable process whose coefficient is a
smooth bounded cylinder in Brownian coordinates from the past. -/
theorem smoothElementaryNaturalItoDuality_pastCylinder
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (G : W → ℝ) (hG : IsSmoothBounded G)
    {n : ℕ} (f : (Fin n → ℝ) → ℝ) (hf : ContDiff ℝ 1 f)
    (hb : ∃ C, ∀ y, |f y| ≤ C)
    (hb' : ∃ C, ∀ y, ‖fderiv ℝ f y‖ ≤ C)
    (t : Fin n → ℝ≥0) (a b : ℝ≥0) (hab : a ≤ b)
    (ht : ∀ i, t i ≤ a) :
    let Z := pastCylinderLpMeas hB coordinate coordinate_apply hsm hnat
      f hf hb hb' t a ht
    inner ℝ (hG.toLp P - expectationL2 (hG.toLp P))
        (elementaryBrownianValue hB hsm hnat hab Z) =
      inner ℝ
        (predictableProjection 𝓅
          (Malliavin.timeDerivative hB coordinate coordinate_apply generated
            (hG.mderivLp P)))
        (elementaryPredictable 𝓅 a b Z) := by
  let hZ := isSmoothBounded_cylinder coordinate coordinate_apply f hf hb hb' t
  let Z := pastCylinderLpMeas hB coordinate coordinate_apply hsm hnat
    f hf hb hb' t a ht
  let h : CameronMartin.Space P :=
    CameronMartin.ofDual P (coordinate b) - CameronMartin.ofDual P (coordinate a)
  change inner ℝ (hG.toLp P - expectationL2 (hG.toLp P))
      (elementaryBrownianValue hB hsm hnat hab Z) =
    inner ℝ
      (predictableProjection 𝓅
        (Malliavin.timeDerivative hB coordinate coordinate_apply generated
          (hG.mderivLp P)))
      (elementaryPredictable 𝓅 a b Z)
  have hhLp : (h : RandomL2 P) = brownianLp hB b - brownianLp hB a := by
    dsimp [h]
    have hbLp : CameronMartin.centeredDualToLp P (coordinate b) = brownianLp hB b :=
      (brownianLp_eq_ofDual hB coordinate coordinate_apply b).symm
    have haLp : CameronMartin.centeredDualToLp P (coordinate a) = brownianLp hB a :=
      (brownianLp_eq_ofDual hB coordinate coordinate_apply a).symm
    rw [hbLp, haLp]
  have hhKernel :
      (wienerIntegralEquiv hB).symm
          (LinearIsometryEquiv.ofEq _ _
            (space_eq_firstChaos hB coordinate coordinate_apply generated) h) =
        iocIndicator a b := by
    dsimp [h]
    simp only [map_sub]
    rw [
      wienerIntegralEquiv_symm_ofDual hB coordinate coordinate_apply generated b,
      wienerIntegralEquiv_symm_ofDual hB coordinate coordinate_apply generated a,
      iocIndicator_eq_intervalIndicator_sub hB hab]
  have horth (i : Fin n) :
      inner ℝ (CameronMartin.ofDual P (coordinate (t i))) h = 0 := by
    dsimp [h]
    have htiLp : CameronMartin.centeredDualToLp P (coordinate (t i)) =
        brownianLp hB (t i) :=
      (brownianLp_eq_ofDual hB coordinate coordinate_apply (t i)).symm
    have hbLp : CameronMartin.centeredDualToLp P (coordinate b) = brownianLp hB b :=
      (brownianLp_eq_ofDual hB coordinate coordinate_apply b).symm
    have haLp : CameronMartin.centeredDualToLp P (coordinate a) = brownianLp hB a :=
      (brownianLp_eq_ofDual hB coordinate coordinate_apply a).symm
    rw [inner_sub_right, htiLp, hbLp, haLp,
      inner_brownianLp, inner_brownianLp,
      min_eq_left (by exact_mod_cast (ht i).trans hab),
      min_eq_left (by exact_mod_cast ht i), sub_self]
  have hcontract (w : W) :
      inner ℝ
          (mderiv P (fun y ↦ f (fun i ↦ B (t i) y)) w) h = 0 := by
    have hfun : (fun y ↦ f (fun i ↦ B (t i) y)) =
        fun y ↦ f (fun i ↦ coordinate (t i) y) := by
      funext y
      simp only [coordinate_apply]
    rw [hfun, mderiv_cylindrical P f (fun i ↦ coordinate (t i)) w
      ((hf.differentiable one_ne_zero) _), Submodule.coe_inner,
      Submodule.coe_sum, sum_inner]
    simp only [Submodule.coe_smul, real_inner_smul_left,
      ← Submodule.coe_inner, horth, mul_zero, Finset.sum_const_zero]
  have hsmul :
      hZ.smulLp P h = Malliavin.smulLp h (hZ.toLp P) := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (hZ.memLp_smul P h 2),
      coeFn_smulLp h (hZ.toLp P), MemLp.coeFn_toLp (hZ.memLp P 2)]
      with w hleft hright hcoeff
    change ((hZ.memLp_smul P h 2).toLp
        (fun x ↦ f (fun i ↦ B (t i) x) • h)) w =
      (Malliavin.smulLp h (hZ.toLp P)) w
    rw [hleft, hright]
    exact congrArg (fun c : ℝ ↦ c • h) hcoeff.symm
  have htime :
      Malliavin.timeDerivative hB coordinate coordinate_apply generated
          (hZ.smulLp P h) =
        (elementaryPredictable 𝓅 a b Z : TimeProcessL2 P) := by
    rw [hsmul, timeDerivative_smulLp hB coordinate coordinate_apply generated,
      hhKernel, elementaryPredictable_coeLp]
    rfl
  have hhCoeFn : ((h : RandomL2 P) : W → ℝ) =ᵐ[P]
      fun w ↦ B b w - B a w := by
    rw [hhLp]
    filter_upwards [Lp.coeFn_sub (brownianLp hB b) (brownianLp hB a),
      coeFn_brownianLp hB b, coeFn_brownianLp hB a]
      with w hsub hbrow harow
    rw [hsub]
    simp only [Pi.sub_apply]
    rw [hbrow, harow]
  have hZCoeFn : ((Z : RandomL2 P) : W → ℝ) =ᵐ[P]
      fun w ↦ f (fun i ↦ B (t i) w) := by
    change ((hZ.toLp P : W → ℝ) =ᵐ[P]
      fun w ↦ f (fun i ↦ B (t i) w))
    exact MemLp.coeFn_toLp (hZ.memLp P 2)
  have hdiv : hZ.divergenceLp P h =
      elementaryBrownianValue hB hsm hnat hab Z := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (hZ.memLp_divergence P h),
      coeFn_elementaryBrownianValue hB hsm hnat hab Z,
      hZCoeFn, hhCoeFn]
      with w hleft hright hcoeff hinc
    change ((hZ.memLp_divergence P h).toLp
        (fun x ↦ f (fun i ↦ B (t i) x) * (h : RandomL2 P) x -
          inner ℝ (mderiv P (fun y ↦ f (fun i ↦ B (t i) y)) x) h)) w =
      (elementaryBrownianValue hB hsm hnat hab Z) w
    rw [hleft, hright, hcoeff, hinc, hcontract]
    ring
  have hcentered :
      ∫ w, elementaryBrownianValue hB hsm hnat hab Z w ∂P = 0 :=
    integral_elementaryBrownianValue hB hsm hnat hab Z
  have hconst (c : ℝ) :
      Lp.const 2 P c = c • Lp.const 2 P (1 : ℝ) := by
    change (Lp.constL 2 P ℝ) c = c • (Lp.constL 2 P ℝ) 1
    rw [← map_smul]
    simp only [smul_eq_mul, mul_one]
  have hone : inner ℝ (Lp.const 2 P (1 : ℝ))
      (elementaryBrownianValue hB hsm hnat hab Z) = 0 := by
    rw [real_inner_comm, ← integral_eq_inner_const, hcentered]
  have hexpect : inner ℝ (expectationL2 (hG.toLp P))
      (elementaryBrownianValue hB hsm hnat hab Z) = 0 := by
    rw [expectationL2, hconst, real_inner_smul_left, hone, mul_zero]
  have hmain : inner ℝ (hG.toLp P)
      (elementaryBrownianValue hB hsm hnat hab Z) =
        inner ℝ (hG.mderivLp P) (hZ.smulLp P h) := by
    rw [← hdiv]
    exact (inner_mderivLp_smulLp P hG hZ h).symm
  let D := Malliavin.timeDerivative hB coordinate coordinate_apply generated
    (hG.mderivLp P)
  let V := elementaryPredictable 𝓅 a b Z
  have hproj :
      inner ℝ ((predictableProjection 𝓅 D : PredictableProcessL2 𝓅 P) : TimeProcessL2 P)
          (V : TimeProcessL2 P) =
        inner ℝ D (V : TimeProcessL2 P) := by
    have hp := inner_predictableProjection_sub (𝓕 := 𝓅) D V
    rw [inner_sub_left] at hp
    exact sub_eq_zero.mp hp
  calc
    inner ℝ (hG.toLp P - expectationL2 (hG.toLp P))
        (elementaryBrownianValue hB hsm hnat hab Z) =
        inner ℝ (hG.toLp P)
          (elementaryBrownianValue hB hsm hnat hab Z) := by
      rw [inner_sub_left, hexpect, sub_zero]
    _ = inner ℝ (hG.mderivLp P) (hZ.smulLp P h) := hmain
    _ = inner ℝ D
        (Malliavin.timeDerivative hB coordinate coordinate_apply generated
          (hZ.smulLp P h)) :=
      by
        dsimp only [D]
        exact (LinearIsometry.inner_map_map (𝕜 := ℝ)
          (Malliavin.timeDerivative hB coordinate coordinate_apply generated)
          (hG.mderivLp P) (hZ.smulLp P h)).symm
    _ = inner ℝ D (V : TimeProcessL2 P) := by rw [htime]
    _ = inner ℝ
        ((predictableProjection 𝓅 D : PredictableProcessL2 𝓅 P) : TimeProcessL2 P)
        (V : TimeProcessL2 P) := hproj.symm
    _ = inner ℝ (predictableProjection 𝓅 D) V := rfl

/-- Fixing the time interval makes the elementary predictable construction a continuous linear
map of its adapted coefficient. -/
noncomputable def elementaryPredictableCoefficientCLM
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (a b : ℝ≥0) :
    lpMeas ℝ ℝ (𝓕 a) 2 P →L[ℝ] PredictableProcessL2 𝓕 P :=
  LinearMap.mkContinuous
    { toFun := elementaryPredictable 𝓕 a b
      map_add' := fun Z Y ↦ by
        apply Subtype.ext
        exact tensor_add (iocIndicator a b) (Z : RandomL2 P) (Y : RandomL2 P)
      map_smul' := fun c Z ↦ by
        apply Subtype.ext
        exact tensor_smul (iocIndicator a b) c (Z : RandomL2 P) }
    ‖iocIndicator a b‖ fun Z ↦ by
      change ‖tensor (iocIndicator a b) (Z : RandomL2 P)‖ ≤ ‖iocIndicator a b‖ * ‖Z‖
      rw [norm_tensor, Submodule.norm_coe]

omit [CompleteSpace W] [BorelSpace W] in
@[simp]
theorem elementaryPredictableCoefficientCLM_apply
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (a b : ℝ≥0)
    (Z : lpMeas ℝ ℝ (𝓕 a) 2 P) :
    elementaryPredictableCoefficientCLM (P := P) 𝓕 a b Z =
      elementaryPredictable 𝓕 a b Z := rfl

/-- Fixing an ordered time interval makes the elementary Brownian terminal value a continuous
linear map of its adapted coefficient. -/
noncomputable def elementaryBrownianCoefficientCLM
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm)
    {a b : ℝ≥0} (_hab : a ≤ b) :
    lpMeas ℝ ℝ (𝓕 a) 2 P →L[ℝ] RandomL2 P :=
  (naturalItoIntegral hB hsm hnat).comp
    (elementaryPredictableCoefficientCLM (P := P) 𝓕 a b)

omit [CompleteSpace W] [BorelSpace W] in
@[simp]
theorem elementaryBrownianCoefficientCLM_apply
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm)
    {a b : ℝ≥0} (hab : a ≤ b) (Z : lpMeas ℝ ℝ (𝓕 a) 2 P) :
    elementaryBrownianCoefficientCLM hB hsm hnat hab Z =
      elementaryBrownianValue hB hsm hnat hab Z := by
  rw [elementaryBrownianCoefficientCLM, ContinuousLinearMap.comp_apply,
    elementaryPredictableCoefficientCLM_apply,
    naturalItoIntegral_elementaryPredictable hB hsm hnat hab Z]

/-- Smooth bounded finite-coordinate Brownian cylinders available at filtration time `a`. -/
def pastCylinderSet
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm) (a : ℝ≥0) :
    Set (lpMeas ℝ ℝ (𝓕 a) 2 P) :=
  {Z | ∃ (n : ℕ) (f : (Fin n → ℝ) → ℝ)
      (hf : ContDiff ℝ 1 f)
      (hb : ∃ C, ∀ y, |f y| ≤ C)
      (hb' : ∃ C, ∀ y, ‖fderiv ℝ f y‖ ≤ C)
      (t : Fin n → ℝ≥0) (ht : ∀ i, t i ≤ a),
    Z = pastCylinderLpMeas hB coordinate coordinate_apply hsm hnat
      f hf hb hb' t a ht}

/-- The algebraic span of the smooth bounded past Brownian cylinders at time `a`. -/
def pastCylinderSpan
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm) (a : ℝ≥0) :
    Submodule ℝ (lpMeas ℝ ℝ (𝓕 a) 2 P) :=
  Submodule.span ℝ
    (pastCylinderSet hB coordinate coordinate_apply hsm hnat a)

/-- The only remaining coefficient-density input: smooth bounded finite-coordinate Brownian
cylinders are dense in every time section of the natural filtration. -/
def PastCylinderDense
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm) : Prop :=
  ∀ a, Dense (pastCylinderSpan hB coordinate coordinate_apply hsm hnat a :
    Set (lpMeas ℝ ℝ (𝓕 a) 2 P))

/-- Density of smooth bounded past cylinders promotes the cylinder calculation to every adapted
coefficient in the smooth elementary duality statement. -/
theorem smoothElementaryNaturalItoDuality_of_pastCylinderDense
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm)
    (hdense : PastCylinderDense hB coordinate coordinate_apply hsm hnat) :
    SmoothElementaryNaturalItoDuality
      hB coordinate coordinate_apply generated hsm hnat := by
  intro G hG a b hab Z
  let V := predictableProjection 𝓕
    (Malliavin.timeDerivative hB coordinate coordinate_apply generated
      (hG.mderivLp P))
  let L : lpMeas ℝ ℝ (𝓕 a) 2 P →L[ℝ] ℝ :=
    (innerSL ℝ (hG.toLp P - expectationL2 (hG.toLp P))).comp
      (elementaryBrownianCoefficientCLM hB hsm hnat hab)
  let R : lpMeas ℝ ℝ (𝓕 a) 2 P →L[ℝ] ℝ :=
    (innerSL ℝ V).comp
      (elementaryPredictableCoefficientCLM (P := P) 𝓕 a b)
  have hLR : L = R := by
    apply ContinuousLinearMap.ext_on
      (s := pastCylinderSet hB coordinate coordinate_apply hsm hnat a)
    · simpa only [pastCylinderSpan] using hdense a
    · rintro X ⟨n, f, hf, hb, hb', t, ht, rfl⟩
      simp only [L, R, V, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
        elementaryBrownianCoefficientCLM_apply,
        elementaryPredictableCoefficientCLM_apply]
      exact smoothElementaryNaturalItoDuality_pastCylinder
        hB coordinate coordinate_apply generated hsm hnat G hG
          f hf hb hb' t a b hab ht
  have happ := congrArg
    (fun T : lpMeas ℝ ℝ (𝓕 a) 2 P →L[ℝ] ℝ ↦ T Z) hLR
  simpa only [L, R, V, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
    elementaryBrownianCoefficientCLM_apply,
    elementaryPredictableCoefficientCLM_apply] using happ

/-- One-step duality extends to arbitrary predictable integrands by density of the elementary
predictable span. -/
theorem smoothNaturalItoDuality_of_elementary
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (hElementary : SmoothElementaryNaturalItoDuality
      hB coordinate coordinate_apply generated hsm hnat) :
    SmoothNaturalItoDuality
      hB coordinate coordinate_apply generated hsm hnat := by
  intro G hG U
  let V := predictableProjection 𝓅
    (Malliavin.timeDerivative hB coordinate coordinate_apply generated
      (hG.mderivLp P))
  let L : PredictableProcessL2 𝓅 P →L[ℝ] ℝ :=
    (innerSL ℝ (hG.toLp P - expectationL2 (hG.toLp P))).comp
      (naturalItoIntegral hB hsm hnat)
  let R : PredictableProcessL2 𝓅 P →L[ℝ] ℝ := innerSL ℝ V
  have hLR : L = R := by
    apply ContinuousLinearMap.ext_on
      (s := {X | ∃ a b : ℝ≥0, ∃ _hab : a ≤ b,
        ∃ Z : lpMeas ℝ ℝ (𝓅 a) 2 P, X = elementaryPredictable 𝓅 a b Z})
    · simpa only [elementaryPredictableSpan] using
        (dense_elementaryPredictableSpan (P := P) 𝓅)
    · rintro X ⟨a, b, hab, Z, rfl⟩
      change inner ℝ (hG.toLp P - expectationL2 (hG.toLp P))
          (naturalItoIntegral hB hsm hnat (elementaryPredictable 𝓅 a b Z)) =
        inner ℝ V (elementaryPredictable 𝓅 a b Z)
      rw [naturalItoIntegral_elementaryPredictable hB hsm hnat hab Z]
      exact hElementary G hG a b hab Z
  have happ := congrArg
    (fun T : PredictableProcessL2 𝓅 P →L[ℝ] ℝ ↦ T U) hLR
  exact happ

/-- Duality on the smooth core extends to every member of `D12` by graph closure. -/
theorem naturalItoDuality_of_smooth
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (hCore : SmoothNaturalItoDuality
      hB coordinate coordinate_apply generated hsm hnat)
    (F : D12 P) (U : PredictableProcessL2 𝓅 P) :
    inner ℝ (F.1 - expectationL2 F.1) (naturalItoIntegral hB hsm hnat U) =
      inner ℝ
        (predictableProjection 𝓅
          (Malliavin.timeDerivative hB coordinate coordinate_apply generated
            (mderivD12 P F))) U := by
  obtain ⟨G, hG, hDG⟩ := inGraphClosure_mderivClosure P F.2
  let R : Lp (CameronMartin.Space P) 2 P →L[ℝ] PredictableProcessL2 𝓅 P :=
    (predictableProjection 𝓅).comp
      (Malliavin.timeDerivative hB coordinate coordinate_apply generated
        ).toContinuousLinearMap
  have heq (n : ℕ) :
      inner ℝ (centeredPartCLM ((G n).2.toLp P))
          (naturalItoIntegral hB hsm hnat U) =
        inner ℝ (R ((G n).2.mderivLp P)) U := by
    rw [centeredPartCLM_apply]
    exact hCore (G n).1 (G n).2 U
  have hcenter :
      Tendsto (fun n ↦ centeredPartCLM ((G n).2.toLp P)) atTop
        (𝓝 (centeredPartCLM F.1)) :=
    ((centeredPartCLM (P := P)).continuous.tendsto F.1).comp hG
  have hleft :
      Tendsto
        (fun n ↦ inner ℝ (centeredPartCLM ((G n).2.toLp P))
          (naturalItoIntegral hB hsm hnat U)) atTop
        (𝓝 (inner ℝ (centeredPartCLM F.1)
          (naturalItoIntegral hB hsm hnat U))) :=
    hcenter.inner tendsto_const_nhds
  have hrightProcess :
      Tendsto (fun n ↦ R ((G n).2.mderivLp P)) atTop
        (𝓝 (R (mderivClosure P F.1))) :=
    (R.continuous.tendsto (mderivClosure P F.1)).comp hDG
  have hright :
      Tendsto (fun n ↦ inner ℝ (R ((G n).2.mderivLp P)) U) atTop
        (𝓝 (inner ℝ (R (mderivClosure P F.1)) U)) :=
    hrightProcess.inner tendsto_const_nhds
  rw [show (fun n ↦ inner ℝ (centeredPartCLM ((G n).2.toLp P))
      (naturalItoIntegral hB hsm hnat U)) =
      fun n ↦ inner ℝ (R ((G n).2.mderivLp P)) U by
        funext n
        exact heq n] at hleft
  have hlimit :
      inner ℝ (centeredPartCLM F.1) (naturalItoIntegral hB hsm hnat U) =
        inner ℝ (R (mderivClosure P F.1)) U :=
    tendsto_nhds_unique hleft hright
  rw [centeredPartCLM_apply] at hlimit
  change inner ℝ (F.1 - expectationL2 F.1)
      (naturalItoIntegral hB hsm hnat U) =
    inner ℝ
      (predictableProjection 𝓅
        (Malliavin.timeDerivative hB coordinate coordinate_apply generated
          (mderivD12 P F))) U at hlimit
  exact hlimit

/-- A Clark--Ocone identity on the smooth core extends to every member of `D12`, because
`mderivClosure` is its graph closure and every operator in the formula is continuous. -/
theorem naturalClarkOcone_of_smooth
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (hCore : SmoothNaturalClarkOcone hB coordinate coordinate_apply generated hsm hnat)
    (F : D12 P) :
    F.1 = expectationL2 F.1 +
      naturalItoIntegral hB hsm hnat
        (predictableProjection 𝓅
          (Malliavin.timeDerivative hB coordinate coordinate_apply generated
            (mderivD12 P F))) := by
  obtain ⟨G, hG, hDG⟩ := inGraphClosure_mderivClosure P F.2
  let R : Lp (CameronMartin.Space P) 2 P →L[ℝ] RandomL2 P :=
    (naturalItoIntegral hB hsm hnat).comp
      ((predictableProjection 𝓅).comp
        (Malliavin.timeDerivative hB coordinate coordinate_apply generated
          ).toContinuousLinearMap)
  have heq (n : ℕ) :
      centeredPartCLM ((G n).2.toLp P) = R ((G n).2.mderivLp P) := by
    rw [centeredPartCLM_apply]
    have hc := hCore (G n).1 (G n).2
    calc
      (G n).2.toLp P - expectationL2 ((G n).2.toLp P) =
          (expectationL2 ((G n).2.toLp P) +
            naturalItoIntegral hB hsm hnat
              (predictableProjection 𝓅
                (Malliavin.timeDerivative hB coordinate coordinate_apply generated
                  ((G n).2.mderivLp P)))) -
            expectationL2 ((G n).2.toLp P) :=
        congrArg (fun X : RandomL2 P ↦
          X - expectationL2 ((G n).2.toLp P)) hc
      _ = naturalItoIntegral hB hsm hnat
          (predictableProjection 𝓅
            (Malliavin.timeDerivative hB coordinate coordinate_apply generated
              ((G n).2.mderivLp P))) := by abel
  have hleft :
      Tendsto (fun n ↦ centeredPartCLM ((G n).2.toLp P)) atTop
        (𝓝 (centeredPartCLM F.1)) :=
    ((centeredPartCLM (P := P)).continuous.tendsto F.1).comp hG
  have hright :
      Tendsto (fun n ↦ R ((G n).2.mderivLp P)) atTop
        (𝓝 (R (mderivClosure P F.1))) :=
    (R.continuous.tendsto (mderivClosure P F.1)).comp hDG
  rw [show (fun n ↦ centeredPartCLM ((G n).2.toLp P)) =
      fun n ↦ R ((G n).2.mderivLp P) by
        funext n
        exact heq n] at hleft
  have hcenter : centeredPartCLM F.1 = R (mderivClosure P F.1) :=
    tendsto_nhds_unique hleft hright
  rw [centeredPartCLM_apply] at hcenter
  change F.1 - expectationL2 F.1 =
    naturalItoIntegral hB hsm hnat
      (predictableProjection 𝓅
        (Malliavin.timeDerivative hB coordinate coordinate_apply generated
          (mderivD12 P F))) at hcenter
  calc
    F.1 = expectationL2 F.1 + (F.1 - expectationL2 F.1) := by abel
    _ = expectationL2 F.1 +
        naturalItoIntegral hB hsm hnat
          (predictableProjection 𝓅
            (Malliavin.timeDerivative hB coordinate coordinate_apply generated
              (mderivD12 P F))) := by rw [hcenter]

/-- A Clark--Ocone identity on the smooth core already implies martingale representation.
Indeed, the centered part of every smooth-core element belongs to the natural Itô range; the
core is dense in ambient `L²`, while that range and the centered-part map are closed and
continuous, respectively. -/
theorem naturalMartingaleRepresentation_of_smoothClarkOcone
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (hCore : SmoothNaturalClarkOcone hB coordinate coordinate_apply generated hsm hnat) :
    NaturalMartingaleRepresentation hB hsm hnat := by
  intro F
  have hmem : centeredPartCLM F ∈ naturalItoRange hB hsm hnat := by
    refine (denseRange_toLp P).induction_on F ?_ ?_
    · exact (isClosed_naturalItoRange hB hsm hnat).preimage
        (centeredPartCLM (P := P)).continuous
    · rintro ⟨G, hG⟩
      rw [centeredPartCLM_apply]
      let V := predictableProjection 𝓅
        (Malliavin.timeDerivative hB coordinate coordinate_apply generated
          (hG.mderivLp P))
      refine ⟨V, ?_⟩
      have hc := hCore G hG
      have hcenter : hG.toLp P - expectationL2 (hG.toLp P) =
          naturalItoIntegral hB hsm hnat V := by
        calc
          hG.toLp P - expectationL2 (hG.toLp P) =
              (expectationL2 (hG.toLp P) + naturalItoIntegral hB hsm hnat V) -
                expectationL2 (hG.toLp P) :=
            congrArg (fun X : RandomL2 P ↦ X - expectationL2 (hG.toLp P)) hc
          _ = naturalItoIntegral hB hsm hnat V := by abel
      exact hcenter.symm
  obtain ⟨U, hU⟩ := hmem
  refine ⟨U, ?_⟩
  rw [centeredPartCLM_apply] at hU
  change naturalItoIntegral hB hsm hnat U = F - expectationL2 F at hU
  calc
    F = expectationL2 F + (F - expectationL2 F) := by abel
    _ = expectationL2 F + naturalItoIntegral hB hsm hnat U := by rw [← hU]

/-- The smooth-core Clark--Ocone identity also supplies the full Malliavin--Itô duality input:
first extend the representation to `D12`, then use the Itô inner-product isometry. -/
theorem naturalItoDuality_of_smoothClarkOcone
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (hCore : SmoothNaturalClarkOcone hB coordinate coordinate_apply generated hsm hnat)
    (F : D12 P) (U : PredictableProcessL2 𝓅 P) :
    inner ℝ (F.1 - expectationL2 F.1) (naturalItoIntegral hB hsm hnat U) =
      inner ℝ
        (predictableProjection 𝓅
          (Malliavin.timeDerivative hB coordinate coordinate_apply generated
            (mderivD12 P F))) U := by
  let V := predictableProjection 𝓅
    (Malliavin.timeDerivative hB coordinate coordinate_apply generated
      (mderivD12 P F))
  have hCO := naturalClarkOcone_of_smooth hB coordinate coordinate_apply generated
    hsm hnat hCore F
  have hcenter : F.1 - expectationL2 F.1 =
      naturalItoIntegral hB hsm hnat V := by
    calc
      F.1 - expectationL2 F.1 =
          (expectationL2 F.1 + naturalItoIntegral hB hsm hnat V) -
            expectationL2 F.1 :=
        congrArg (fun X : RandomL2 P ↦ X - expectationL2 F.1) hCO
      _ = naturalItoIntegral hB hsm hnat V := by abel
  calc
    inner ℝ (F.1 - expectationL2 F.1) (naturalItoIntegral hB hsm hnat U) =
        inner ℝ (naturalItoIntegral hB hsm hnat V)
          (naturalItoIntegral hB hsm hnat U) := by rw [hcenter]
    _ = inner ℝ V U := inner_naturalItoIntegral hB hsm hnat V U

/-- Build the concrete Brownian `ClarkOconeFamily` from a single Clark--Ocone identity on the
smooth core.  Graph closure supplies the identity on `D12`; density and closed range supply MRT;
the Itô isometry then supplies duality. -/
noncomputable def ClarkOconeFamily.ofNaturalItoSmoothClarkOcone
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (hCore : SmoothNaturalClarkOcone hB coordinate coordinate_apply generated hsm hnat) :
    ClarkOconeFamily B P 𝓅 :=
  ClarkOconeFamily.ofNaturalIto hB coordinate coordinate_apply generated hsm hnat
    (naturalMartingaleRepresentation_of_smoothClarkOcone
      hB coordinate coordinate_apply generated hsm hnat hCore)
    (naturalItoDuality_of_smoothClarkOcone
      hB coordinate coordinate_apply generated hsm hnat hCore)

/-- The smooth-core constructor uses the genuine Brownian integral on every elementary adapted
process. -/
theorem ClarkOconeFamily.ofNaturalItoSmoothClarkOcone_isBrownianOnElementary
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (hCore : SmoothNaturalClarkOcone hB coordinate coordinate_apply generated hsm hnat) :
    (ClarkOconeFamily.ofNaturalItoSmoothClarkOcone
      hB coordinate coordinate_apply generated hsm hnat hCore).IsBrownianOnElementary := by
  apply ClarkOconeFamily.isBrownianOnElementary_of_itoIntegral_eq_naturalItoIntegral
  rfl

/-- For the natural Brownian filtration, the raw timewise conditional-kernel formula required
by `ClarkOconeFamily.ofNaturalItoTimewiseCondExpKernel` is equivalent to the canonical
best-integrand equality required by `ClarkOconeFamily.ofNaturalItoBestIntegrand`.

Thus the global kernel identification supplies the jointly predictable representative of the
right-hand side, but does not by itself prove that the inverse-Itô integrand is that
representative. -/
theorem bestNaturalItoIntegrand_eq_predictableProjection_iff_ae_timewiseCondExpKernel
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm) (F : D12 P) :
    bestNaturalItoIntegrand hB hsm hnat (centeredPartL2 F.1) =
        predictableProjection 𝓅
          (Malliavin.timeDerivative hB coordinate coordinate_apply generated
            (mderivD12 P F)) ↔
      ∀ᵐ t ∂nonnegativeLebesgueMeasure,
        (fun w ↦
          (bestNaturalItoIntegrand hB hsm hnat (centeredPartL2 F.1) :
            ℝ≥0 × W → ℝ) (t, w)) =ᵐ[P]
          fun w ↦ ∫ w',
            (Malliavin.timeDerivative hB coordinate coordinate_apply generated
              (mderivD12 P F) : ℝ≥0 × W → ℝ) (t, w')
            ∂condExpKernel P (𝓅 t) w := by
  subst 𝓅
  constructor
  · intro hBest
    rw [hBest]
    have hsection :=
      timeSection_predictableProjection_ae_eq_integral_condExpKernel_natural
        hB hsm generated
          (Malliavin.timeDerivative hB coordinate coordinate_apply generated
            (mderivD12 P F))
    filter_upwards [hsection, nonnegativeLebesgueMeasure.ae_ne 0] with t ht ht0
    exact ht (pos_iff_ne_zero.mpr ht0)
  · intro hTimewise
    exact
      bestNaturalItoIntegrand_eq_predictableProjection_of_ae_timewiseCondExpKernel
        hB coordinate coordinate_apply generated hsm rfl F hTimewise

end Malliavin

end

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
