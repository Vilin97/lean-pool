/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.PositiveAxisExistence
public import LeanPool.NavierStokesAndEuler.NavierStokes.AxisSourceRegularity
public import LeanPool.NavierStokesAndEuler.NavierStokes.BoundaryAxisJets

@[expose] public section

/-!
# Local slow-order recursion from actual lower profiles

The source algebra consists of genuine smooth, even radial functions with
holomorphic parameter dependence. No preconstructed all-order jet family
is assumed.
-/

noncomputable section

namespace NavierStokes.SlowRecursion

open Set Filter
open scoped Topology ContDiff

abbrev Raw := ℝ × ℂ → ℂ

/-- The induction class for actual scalar radial profiles. -/
structure Regular (R : ℝ) (U : Set ℂ) (F : Raw) : Prop where
  smooth : ContDiffOn ℝ ∞ F (Ioo (-R) R ×ˢ U)
  holomorphic : ∀ r ∈ Ioo (-R) R, DifferentiableOn ℂ (fun z => F (r, z)) U
  even : ∀ z ∈ U, ∀ r ∈ Ioo (-R) R, F (-r, z) = F (r, z)
  real : ∀ r ∈ Ioo (-R) R, ∀ eta : ℝ, (eta : ℂ) ∈ U → (F (r, (eta : ℂ))).im = 0

theorem Regular.const (R : ℝ) (U : Set ℂ) (c : ℝ) :
    Regular R U (fun _ => (c : ℂ)) :=
  ⟨contDiffOn_const, fun _ _ => differentiableOn_const _, fun _ _ _ _ => rfl,
    fun _ _ _ _ => Complex.ofReal_im c⟩

theorem Regular.add {R : ℝ} {U : Set ℂ} {F G : Raw}
    (hF : Regular R U F) (hG : Regular R U G) : Regular R U (F + G) := by
  refine ⟨hF.smooth.add hG.smooth, fun r hr => (hF.holomorphic r hr).add (hG.holomorphic r hr), ?_,
    ?_⟩
  · intro z hz r hr
    change F (-r, z) + G (-r, z) = F (r, z) + G (r, z)
    rw [hF.even z hz r hr, hG.even z hz r hr]
  · intro r hr eta heta
    change (F (r, (eta : ℂ)) + G (r, (eta : ℂ))).im = 0
    simp only [Complex.add_im, hF.real r hr eta heta, hG.real r hr eta heta, add_zero]

theorem Regular.mul {R : ℝ} {U : Set ℂ} {F G : Raw}
    (hF : Regular R U F) (hG : Regular R U G) : Regular R U (F * G) := by
  refine ⟨hF.smooth.mul hG.smooth, fun r hr => (hF.holomorphic r hr).mul (hG.holomorphic r hr), ?_,
    ?_⟩
  · intro z hz r hr
    change F (-r, z) * G (-r, z) = F (r, z) * G (r, z)
    rw [hF.even z hz r hr, hG.even z hz r hr]
  · intro r hr eta heta
    change (F (r, (eta : ℂ)) * G (r, (eta : ℂ))).im = 0
    simp only [Complex.mul_im, hF.real r hr eta heta, hG.real r hr eta heta,
      mul_zero, zero_mul, add_zero]

/-- The class is an actual real algebra of functions. -/
noncomputable def regularAlgebra (R : ℝ) (U : Set ℂ) : Subalgebra ℝ Raw where
  carrier := {F | Regular R U F}
  zero_mem' := Regular.const R U 0
  one_mem' := Regular.const R U 1
  add_mem' := Regular.add
  mul_mem' := Regular.mul
  algebraMap_mem' := fun r => Regular.const R U r

abbrev AxisFunction (R : ℝ) (U : Set ℂ) : Type := ↥(regularAlgebra R U)

instance {R : ℝ} {U : Set ℂ} : CoeFun (AxisFunction R U) (fun _ => Raw) := ⟨fun F => F.1⟩

theorem AxisFunction.smooth {R : ℝ} {U : Set ℂ} (F : AxisFunction R U) :
    ContDiffOn ℝ ∞ F (Ioo (-R) R ×ˢ U) := F.2.smooth

theorem AxisFunction.holomorphic {R : ℝ} {U : Set ℂ} (F : AxisFunction R U)
    {r : ℝ} (hr : r ∈ Ioo (-R) R) : DifferentiableOn ℂ (fun z => F (r, z)) U :=
  F.2.holomorphic r hr

theorem AxisFunction.even {R : ℝ} {U : Set ℂ} (F : AxisFunction R U)
    {r : ℝ} (hr : r ∈ Ioo (-R) R) {z : ℂ} (hz : z ∈ U) : F (-r, z) = F (r, z) :=
  F.2.even z hz r hr

theorem AxisFunction.real {R : ℝ} {U : Set ℂ} (F : AxisFunction R U)
    {r : ℝ} (hr : r ∈ Ioo (-R) R) {eta : ℝ} (heta : (eta : ℂ) ∈ U) :
    (F (r, (eta : ℂ))).im = 0 := F.2.real r hr eta heta

noncomputable def realConstant (R : ℝ) (U : Set ℂ) (c : ℝ) : AxisFunction R U :=
  algebraMap ℝ (AxisFunction R U) c

@[simp] theorem realConstant_apply (R : ℝ) (U : Set ℂ) (c : ℝ) (p : ℝ × ℂ) :
    realConstant R U c p = (c : ℂ) := rfl

@[simp] theorem add_apply {R : ℝ} {U : Set ℂ} (F G : AxisFunction R U) (p : ℝ × ℂ) :
    (F + G) p = F p + G p := rfl
@[simp] theorem mul_apply {R : ℝ} {U : Set ℂ} (F G : AxisFunction R U) (p : ℝ × ℂ) :
    (F * G) p = F p * G p := rfl
@[simp] theorem sub_apply {R : ℝ} {U : Set ℂ} (F G : AxisFunction R U) (p : ℝ × ℂ) :
    (F - G) p = F p - G p := rfl
@[simp] theorem neg_apply {R : ℝ} {U : Set ℂ} (F : AxisFunction R U) (p : ℝ × ℂ) :
    (-F) p = -F p := rfl
@[simp] theorem zero_apply {R : ℝ} {U : Set ℂ} (p : ℝ × ℂ) :
    (0 : AxisFunction R U) p = 0 := rfl
@[simp] theorem one_apply {R : ℝ} {U : Set ℂ} (p : ℝ × ℂ) :
    (1 : AxisFunction R U) p = 1 := rfl

noncomputable def squaredRadius (R : ℝ) (U : Set ℂ) : AxisFunction R U :=
  ⟨fun p : ℝ × ℂ => ((p.1 ^ 2 : ℝ) : ℂ), {
    smooth := Complex.ofRealCLM.contDiff.comp_contDiffOn (contDiffOn_fst.pow 2)
    holomorphic := fun r _ => differentiableOn_const ((r ^ 2 : ℝ) : ℂ)
    even := fun _ _ _ _ => by simp only [neg_sq]
    real := fun _ _ _ _ => Complex.ofReal_im _ }⟩

noncomputable def parameter (R : ℝ) (U : Set ℂ) : AxisFunction R U :=
  ⟨Prod.snd, {
    smooth := contDiffOn_snd
    holomorphic := fun _ _ => differentiableOn_id
    even := fun _ _ _ _ => rfl
    real := fun _ _ _ _ => Complex.ofReal_im _ }⟩

theorem interval_mono {R S : ℝ} (hSR : S ≤ R) : Ioo (-S) S ⊆ Ioo (-R) R := by
  intro r hr
  exact ⟨lt_of_le_of_lt (neg_le_neg hSR) hr.1, lt_of_lt_of_le hr.2 hSR⟩

noncomputable def restrict {R S : ℝ} {U : Set ℂ} (hSR : S ≤ R)
    (F : AxisFunction R U) : AxisFunction S U :=
  ⟨F, {
    smooth := F.2.smooth.mono (Set.prod_mono (interval_mono hSR) Subset.rfl)
    holomorphic := fun r hr => F.2.holomorphic r (interval_mono hSR hr)
    even := fun z hz r hr => F.2.even z hz r (interval_mono hSR hr)
    real := fun r hr eta heta => F.2.real r (interval_mono hSR hr) eta heta }⟩

@[simp] theorem restrict_apply {R S : ℝ} {U : Set ℂ} (hSR : S ≤ R)
    (F : AxisFunction R U) (p : ℝ × ℂ) : restrict hSR F p = F p := rfl

noncomputable def inverse {R : ℝ} {U : Set ℂ} (F : AxisFunction R U)
    (hF : ∀ p ∈ Ioo (-R) R ×ˢ U, F p ≠ 0) : AxisFunction R U :=
  ⟨fun p => (F p)⁻¹, {
    smooth := F.2.smooth.inv hF
    holomorphic := fun r hr => (F.2.holomorphic r hr).inv (fun z hz => hF (r, z) ⟨hr, hz⟩)
    even := fun z hz r hr => congrArg Inv.inv (F.2.even z hz r hr)
    real := fun r hr eta heta => by simp [Complex.inv_im, F.2.real r hr eta heta] }⟩

theorem im_iteratedDeriv_zero {S : Set ℝ} (hS : IsOpen S) {f : ℝ → ℂ}
    (hf : ContDiffOn ℝ ∞ f S) (hreal : ∀ x ∈ S, (f x).im = 0)
    {x : ℝ} (hx : x ∈ S) (n : ℕ) : (iteratedDeriv n f x).im = 0 := by
  have hc := Complex.imCLM.iteratedFDerivWithin_comp_left (hf x hx) hS.uniqueDiffOn hx
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)
  have hv := congrArg (fun L : ℝ [×n]→L[ℝ] ℝ => L (fun _ => 1)) hc.symm
  have hm : (iteratedDeriv n f x).im = iteratedDeriv n (fun t => (f t).im) x := by
    simp only [iteratedFDerivWithin_of_isOpen n hS hx,
      ContinuousLinearMap.compContinuousMultilinearMap_coe, Complex.imCLM_apply, Function.comp_def]
        at hv
    exact hv
  have he : (fun t => (f t).im) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
    filter_upwards [hS.mem_nhds hx] with t ht
    exact hreal t ht
  rw [hm, he.iteratedDeriv_eq n]
  have hz (k : ℕ) : iteratedDeriv k (fun _ : ℝ => (0 : ℝ)) = fun _ => 0 := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [iteratedDeriv_succ, ih]
      funext t
      exact deriv_const t 0
  exact congrFun (hz n) x

theorem scaled_mem_open {R r t : ℝ} (hr : r ∈ Ioo (-R) R)
    (ht : t ∈ Icc (0 : ℝ) 1) : t * r ∈ Ioo (-R) R := by
  apply abs_lt.mp
  calc
    |t * r| = t * |r| := by rw [abs_mul, abs_of_nonneg ht.1]
    _ ≤ |r| := mul_le_of_le_one_left (abs_nonneg r) ht.2
    _ < R := abs_lt.mpr hr

theorem radialJet_one_real {R : ℝ} {U : Set ℂ} (F : AxisFunction R U)
    {r : ℝ} (hr : r ∈ Ioo (-R) R) {eta : ℝ} (heta : (eta : ℂ) ∈ U) :
    (BoundaryAxisJets.radialJet F 1 r (eta : ℂ)).im = 0 := by
  let f : ℝ → ℂ := fun s => F (s, (eta : ℂ))
  have hf : ContDiffOn ℝ ∞ f (Ioo (-R) R) :=
    F.2.smooth.comp (contDiff_id.prodMk contDiff_const).contDiffOn (fun s hs => ⟨hs, heta⟩)
  have hd := VolterraRegularity.real_iteratedDeriv_contDiffOn isOpen_Ioo hf 2
  have hi : IntervalIntegrable (fun t => iteratedDeriv 2 f (t * r))
      MeasureTheory.volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le zero_le_one]
    exact hd.continuousOn.comp (continuous_id.mul continuous_const).continuousOn
      (fun t ht => scaled_mem_open hr ht)
  change Complex.imCLM ((1 / 2 : ℝ) • ∫ t in (0 : ℝ)..1, iteratedDeriv 2 f (t * r)) = 0
  rw [map_smul, ← Complex.imCLM.intervalIntegral_comp_comm hi]
  have hz : (∫ t in (0 : ℝ)..1, Complex.imCLM (iteratedDeriv 2 f (t * r))) = 0 := by
    calc
      _ = ∫ _t in (0 : ℝ)..1, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using ht
        exact im_iteratedDeriv_zero isOpen_Ioo hf
          (fun s hs => F.2.real s hs eta heta) (scaled_mem_open hr ht') 2
      _ = 0 := by simp
  rw [hz, smul_zero]

noncomputable def radialDerivative {R : ℝ} (hR : 0 < R) {U : Set ℂ} (hU : IsOpen U)
    (F : AxisFunction R U) : AxisFunction R U :=
  ⟨fun p => BoundaryAxisJets.radialJet F 1 p.1 p.2, {
    smooth := BoundaryAxisJets.radialJet_joint_contDiffOn_full hR hU F.2.smooth 1
    holomorphic := fun _ hr => BoundaryAxisJets.radialJet_holomorphic_full hR hU
      F.2.smooth F.2.holomorphic 1 hr
    even := fun z hz _ hr => BoundaryAxisJets.radialJet_even_full hR (F.2.even z hz) 1 hr
    real := fun _ hr _ heta => radialJet_one_real F hr heta }⟩

theorem parameterDerivative_real {R : ℝ} {U : Set ℂ} (hU : IsOpen U)
    (F : AxisFunction R U) {r : ℝ} (hr : r ∈ Ioo (-R) R)
    {eta : ℝ} (heta : (eta : ℂ) ∈ U) :
    (BoundaryAxisJets.complexPartial F (r, (eta : ℂ))).im = 0 := by
  have hd := ((F.2.holomorphic r hr).differentiableAt (hU.mem_nhds heta)).hasDerivAt.comp_ofReal
  have hi := (Complex.imCLM.hasFDerivAt.comp_hasDerivAt eta hd).deriv
  have he : (fun t : ℝ => (F (r, (t : ℂ))).im) =ᶠ[𝓝 eta] fun _ => (0 : ℝ) := by
    filter_upwards [Complex.continuous_ofReal.continuousAt.preimage_mem_nhds (hU.mem_nhds heta)]
      with t ht
    exact F.2.real r hr t ht
  change deriv (fun t : ℝ => (F (r, (t : ℂ))).im) eta = _ at hi
  rw [he.deriv_eq, deriv_const] at hi
  exact hi.symm

noncomputable def parameterDerivative {R : ℝ} {U : Set ℂ} (hU : IsOpen U)
    (F : AxisFunction R U) : AxisFunction R U :=
  ⟨BoundaryAxisJets.complexPartial F, {
    smooth := BoundaryAxisJets.complexPartial_contDiffOn isOpen_Ioo hU F.2.smooth F.2.holomorphic
    holomorphic := fun r hr => (F.2.holomorphic r hr).deriv hU
    even := by
      intro z hz r hr
      apply Filter.EventuallyEq.deriv_eq
      filter_upwards [hU.mem_nhds hz] with w hw
      exact F.2.even w hw r hr
    real := fun _ hr _ heta => parameterDerivative_real hU F hr heta }⟩

theorem hasDerivAt_conjugate {f : ℂ → ℂ} {d z : ℂ}
    (hf : HasDerivAt f d (starRingEnd ℂ z)) :
    HasDerivAt (fun w => starRingEnd ℂ (f (starRingEnd ℂ w))) (starRingEnd ℂ d) z := by
  let J := Complex.conjCLE.toContinuousLinearMap
  have hh := J.hasFDerivAt.comp z ((hf.hasFDerivAt.restrictScalars ℝ).comp z J.hasFDerivAt)
  change HasFDerivAt _ ((1 : ℂ →L[ℂ] ℂ).smulRight (starRingEnd ℂ d)) z
  apply hasFDerivAt_of_restrictScalars ℝ hh
  ext v
  simp [J, map_mul]

/-- Reflection gives a holomorphic extension of the actual real trace. -/
noncomputable def realSymmetrization (F : Raw) (p : ℝ × ℂ) : ℂ :=
  (F p + starRingEnd ℂ (F (p.1, starRingEnd ℂ p.2))) / 2

theorem realSymmetrization_real (F : Raw) (r eta : ℝ) :
    realSymmetrization F (r, (eta : ℂ)) = ((F (r, (eta : ℂ))).re : ℂ) := by
  apply Complex.ext <;> simp [realSymmetrization]

noncomputable def symmetrize {R : ℝ} {U : Set ℂ} (hU : IsOpen U)
    (hconj : ∀ z ∈ U, starRingEnd ℂ z ∈ U) (F : Raw)
    (hs : ContDiffOn ℝ ∞ F (Ioo (-R) R ×ˢ U))
    (hh : ∀ r ∈ Ioo (-R) R, DifferentiableOn ℂ (fun z => F (r, z)) U)
    (he : ∀ z ∈ U, ∀ r ∈ Ioo (-R) R, F (-r, z) = F (r, z)) : AxisFunction R U :=
  ⟨realSymmetrization F, {
    smooth := by
      apply ContDiffOn.div_const
      apply hs.add
      apply Complex.conjCLE.toContinuousLinearMap.contDiff.comp_contDiffOn
      apply hs.comp
        (contDiff_fst.prodMk (Complex.conjCLE.toContinuousLinearMap.contDiff.comp
          contDiff_snd)).contDiffOn
      exact fun p hp => ⟨hp.1, hconj p.2 hp.2⟩
    holomorphic := by
      intro r hr
      apply DifferentiableOn.div_const
      apply (hh r hr).add
      intro z hz
      exact (hasDerivAt_conjugate ((hh r hr).differentiableAt
        (hU.mem_nhds (hconj z hz))).hasDerivAt).differentiableAt.differentiableWithinAt
    even := by
      intro z hz r hr
      dsimp [realSymmetrization]
      rw [he z hz r hr, he _ (hconj z hz) r hr]
    real := by
      intro r _ eta _
      rw [realSymmetrization_real]
      rfl }⟩

noncomputable def profile {R : ℝ} {U : Set ℂ} (F : AxisFunction R U)
    (p : ℝ × ℝ) : ℝ := (F (Real.sqrt p.1, (p.2 : ℂ))).re

noncomputable def complexProfile {R : ℝ} {U : Set ℂ} (F : AxisFunction R U)
    (p : ℝ × ℂ) : ℂ := F (Real.sqrt p.1, p.2)

theorem sqrt_mem {R X : ℝ} (hR : 0 < R) (hX : X ∈ Ico (0 : ℝ) (R ^ 2)) :
    Real.sqrt X ∈ Ioo (-R) R := by
  constructor
  · linarith [Real.sqrt_nonneg X]
  · nlinarith [Real.sq_sqrt hX.1, Real.sqrt_nonneg X, hX.2]

theorem complexProfile_real {R : ℝ} (hR : 0 < R) {U : Set ℂ} (F : AxisFunction R U)
    {X eta : ℝ} (hX : X ∈ Ico (0 : ℝ) (R ^ 2)) (heta : (eta : ℂ) ∈ U) :
    complexProfile F (X, (eta : ℂ)) = (profile F (X, eta) : ℂ) := by
  apply Complex.ext
  · rfl
  · exact F.2.real _ (sqrt_mem hR hX) eta heta

theorem complexProfile_square {R : ℝ} {U : Set ℂ} (F : AxisFunction R U)
    {r : ℝ} (hr : r ∈ Ioo (-R) R) {z : ℂ} (hz : z ∈ U) :
    complexProfile F (r ^ 2, z) = F (r, z) := by
  change F (Real.sqrt (r ^ 2), z) = _
  rw [Real.sqrt_sq_eq_abs]
  rcases le_or_gt 0 r with hs | hs
  · rw [abs_of_nonneg hs]
  · rw [abs_of_neg hs, F.2.even z hz r hr]

theorem profile_smooth {R : ℝ} (hR : 0 < R) {U : Set ℂ} (hU : IsOpen U)
    (F : AxisFunction R U) :
    ContDiffOn ℝ ∞ (profile F)
      (Ico (0 : ℝ) (R ^ 2) ×ˢ PositiveAxisExistence.realParameterDomain U) := by
  let G : ℝ × ℝ → ℝ := fun p => (F (p.2, (p.1 : ℂ))).re
  have hg : ContDiffOn ℝ ∞ G
      (PositiveAxisExistence.realParameterDomain U ×ˢ Ioo (-R) R) :=
    Complex.reCLM.contDiff.comp_contDiffOn (F.2.smooth.comp
      (contDiff_snd.prodMk (Complex.ofRealCLM.contDiff.comp contDiff_fst)).contDiffOn
      (fun p hp => ⟨hp.2, hp.1⟩))
  have he : ∀ eta ∈ PositiveAxisExistence.realParameterDomain U,
      ∀ r ∈ Ioo (-R) R, G (eta, -r) = G (eta, r) := by
    intro eta heta r hr
    exact congrArg Complex.re (F.2.even _ heta r hr)
  exact (ParametricEvenDescent.contDiffOn_descend_local
    (PositiveAxisExistence.realParameterDomain_isOpen hU) hR hg he).comp
      (contDiff_snd.prodMk contDiff_fst).contDiffOn (fun p hp => ⟨hp.2, hp.1⟩)

theorem profile_contDiffAt {R : ℝ} (hR : 0 < R) {U : Set ℂ} (hU : IsOpen U)
    (F : AxisFunction R U) {X eta : ℝ} (hX : X ∈ Ioo (0 : ℝ) (R ^ 2))
    (heta : (eta : ℂ) ∈ U) : ContDiffAt ℝ ∞ (profile F) (X, eta) :=
  ((profile_smooth hR hU F).mono (Set.prod_mono Ioo_subset_Ico_self (Subset.refl _))).contDiffAt
    ((isOpen_Ioo.prod (PositiveAxisExistence.realParameterDomain_isOpen hU)).mem_nhds ⟨hX, heta⟩)

theorem radialDerivative_value {R : ℝ} (hR : 0 < R) {U : Set ℂ} (hU : IsOpen U)
    (F : AxisFunction R U) {X eta : ℝ} (hX : X ∈ Ioo (0 : ℝ) (R ^ 2))
    (heta : (eta : ℂ) ∈ U) :
    complexProfile (radialDerivative hR hU F) (X, (eta : ℂ)) =
      (SimilarityProfile.partialX (profile F) (X, eta) : ℂ) := by
  have hb := BoundaryAxisJets.axisJet_eq_ordinary_full hR hU F.2.smooth F.2.even 1 hX heta
  have hd := ((profile_contDiffAt hR hU F hX heta).differentiableAt (by
    simp)).hasFDerivAt.comp_hasDerivAt X
    ((hasDerivAt_id X).prodMk (hasDerivAt_const X eta))
  change HasDerivAt (fun Y => profile F (Y, eta)) (SimilarityProfile.partialX (profile F) (X, eta))
    X at hd
  have he : (fun Y => F (Real.sqrt Y, (eta : ℂ))) =ᶠ[𝓝 X]
      (fun Y => (profile F (Y, eta) : ℂ)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hX] with Y hY
    exact complexProfile_real hR F ⟨hY.1.le, hY.2⟩ heta
  simp only [iteratedDeriv_one, he.deriv_eq, hd.ofReal_comp.deriv] at hb
  exact hb

theorem parameterDerivative_value {R : ℝ} (hR : 0 < R) {U : Set ℂ} (hU : IsOpen U)
    (F : AxisFunction R U) {X eta : ℝ} (hX : X ∈ Ioo (0 : ℝ) (R ^ 2))
    (heta : (eta : ℂ) ∈ U) :
    complexProfile (parameterDerivative hU F) (X, (eta : ℂ)) =
      (SimilarityProfile.partialEta (profile F) (X, eta) : ℂ) := by
  have hr := sqrt_mem hR ⟨hX.1.le, hX.2⟩
  have hdC := ((F.2.holomorphic _ hr).differentiableAt (hU.mem_nhds heta)).hasDerivAt
  have hdR := PositiveAxisSystem.hasDerivAt_parameterProfile
    ((profile_contDiffAt hR hU F hX heta).differentiableAt (by simp))
  apply Complex.ext
  · exact hdC.real_of_complex.deriv.symm.trans hdR.deriv
  · exact parameterDerivative_real hU F hr heta

theorem profile_radialDerivative {R : ℝ} (hR : 0 < R) {U : Set ℂ} (hU : IsOpen U)
    (F : AxisFunction R U) {X eta : ℝ} (hX : X ∈ Ioo (0 : ℝ) (R ^ 2))
    (heta : (eta : ℂ) ∈ U) :
    profile (radialDerivative hR hU F) (X, eta) =
      SimilarityProfile.partialX (profile F) (X, eta) :=
  congrArg Complex.re (radialDerivative_value hR hU F hX heta)

theorem profile_parameterDerivative {R : ℝ} (hR : 0 < R) {U : Set ℂ} (hU : IsOpen U)
    (F : AxisFunction R U) {X eta : ℝ} (hX : X ∈ Ioo (0 : ℝ) (R ^ 2))
    (heta : (eta : ℂ) ∈ U) :
    profile (parameterDerivative hU F) (X, eta) =
      SimilarityProfile.partialEta (profile F) (X, eta) :=
  congrArg Complex.re (parameterDerivative_value hR hU F hX heta)

theorem profile_radialDerivative_germ {R : ℝ} (hR : 0 < R) {U : Set ℂ} (hU : IsOpen U)
    (F : AxisFunction R U) {X eta : ℝ} (hX : X ∈ Ioo (0 : ℝ) (R ^ 2))
    (heta : (eta : ℂ) ∈ U) :
    profile (radialDerivative hR hU F) =ᶠ[𝓝 (X, eta)] SimilarityProfile.partialX (profile F) := by
  filter_upwards [(isOpen_Ioo.prod (PositiveAxisExistence.realParameterDomain_isOpen hU)).mem_nhds
    (show (X, eta) ∈ Ioo (0 : ℝ) (R ^ 2) ×ˢ PositiveAxisExistence.realParameterDomain U from ⟨hX,
      heta⟩)] with p hp
  exact profile_radialDerivative hR hU F hp.1 hp.2

theorem profile_parameterDerivative_germ {R : ℝ} (hR : 0 < R) {U : Set ℂ} (hU : IsOpen U)
    (F : AxisFunction R U) {X eta : ℝ} (hX : X ∈ Ioo (0 : ℝ) (R ^ 2))
    (heta : (eta : ℂ) ∈ U) :
    profile (parameterDerivative hU F) =ᶠ[𝓝 (X, eta)] SimilarityProfile.partialEta (profile F) := by
  filter_upwards [(isOpen_Ioo.prod (PositiveAxisExistence.realParameterDomain_isOpen hU)).mem_nhds
    (show (X, eta) ∈ Ioo (0 : ℝ) (R ^ 2) ×ˢ PositiveAxisExistence.realParameterDomain U from ⟨hX,
      heta⟩)] with p hp
  exact profile_parameterDerivative hR hU F hp.1 hp.2

theorem radialDerivative_twice_value {R : ℝ} (hR : 0 < R) {U : Set ℂ} (hU : IsOpen U)
    (F : AxisFunction R U) {X eta : ℝ} (hX : X ∈ Ioo (0 : ℝ) (R ^ 2))
    (heta : (eta : ℂ) ∈ U) :
    complexProfile (radialDerivative hR hU (radialDerivative hR hU F)) (X, (eta : ℂ)) =
      (SimilarityProfile.partialX (SimilarityProfile.partialX (profile F)) (X, eta) : ℂ) := by
  rw [radialDerivative_value hR hU _ hX heta]
  unfold SimilarityProfile.partialX
  rw [(profile_radialDerivative_germ hR hU F hX heta).fderiv_eq]
  rfl

/-- Fixed geometric data for one analytic parameter neighborhood. -/
structure Domain (R : ℝ) (U : Set ℂ) (h : ℝ) : Prop where
  positive : 0 < R
  open_set : IsOpen U
  conjugate : ∀ z ∈ U, starRingEnd ℂ z ∈ U
  denominator : ∀ z ∈ U, PositiveAxisSystem.ell (h : ℂ) z ≠ 0

theorem Domain.restrict {R S : ℝ} {U : Set ℂ} {h : ℝ} (c : Domain R U h)
    (hS : 0 < S) : Domain S U h := ⟨hS, c.open_set, c.conjugate, c.denominator⟩

noncomputable def denominatorFunction (R : ℝ) (U : Set ℂ) (h : ℝ) : AxisFunction R U :=
  1 - realConstant R U (2 * h) * parameter R U ^ 2

theorem denominatorFunction_apply (R : ℝ) (U : Set ℂ) (h : ℝ) (p : ℝ × ℂ) :
    denominatorFunction R U h p = PositiveAxisSystem.ell (h : ℂ) p.2 := by
  simp [denominatorFunction, parameter, realConstant, PositiveAxisSystem.ell]

noncomputable def inverseDenominator {R : ℝ} {U : Set ℂ} {h : ℝ} (c : Domain R U h) :
    AxisFunction R U :=
  inverse (denominatorFunction R U h) (fun p hp => by
    rw [denominatorFunction_apply]
    exact c.denominator p.2 hp.2)

noncomputable def timeOperator {R : ℝ} {U : Set ℂ} {h : ℝ} (c : Domain R U h)
    (b : ℝ) (F : AxisFunction R U) : AxisFunction R U :=
  (-realConstant R U b * F + realConstant R U (1 / 2 - h) * parameter R U *
    parameterDerivative c.open_set F + squaredRadius R U * radialDerivative c.positive c.open_set
      F) *
    inverseDenominator c

noncomputable def axialOperator {R : ℝ} {U : Set ℂ} {h : ℝ} (c : Domain R U h)
    (b : ℝ) (F : AxisFunction R U) : AxisFunction R U :=
  (realConstant R U 2 * parameter R U * realConstant R U b * F +
    (1 - parameter R U ^ 2) * parameterDerivative c.open_set F -
    realConstant R U 2 * parameter R U * squaredRadius R U *
      radialDerivative c.positive c.open_set F) * inverseDenominator c

@[simp] theorem complexProfile_add {R : ℝ} {U : Set ℂ} (F G : AxisFunction R U) (p : ℝ × ℂ) :
    complexProfile (F + G) p = complexProfile F p + complexProfile G p := rfl
@[simp] theorem complexProfile_sub {R : ℝ} {U : Set ℂ} (F G : AxisFunction R U) (p : ℝ × ℂ) :
    complexProfile (F - G) p = complexProfile F p - complexProfile G p := rfl
@[simp] theorem complexProfile_mul {R : ℝ} {U : Set ℂ} (F G : AxisFunction R U) (p : ℝ × ℂ) :
    complexProfile (F * G) p = complexProfile F p * complexProfile G p := rfl
@[simp] theorem complexProfile_neg {R : ℝ} {U : Set ℂ} (F : AxisFunction R U) (p : ℝ × ℂ) :
    complexProfile (-F) p = -complexProfile F p := rfl
@[simp] theorem complexProfile_pow {R : ℝ} {U : Set ℂ} (F : AxisFunction R U) (k : ℕ) (p : ℝ × ℂ) :
    complexProfile (F ^ k) p = complexProfile F p ^ k := rfl
@[simp] theorem complexProfile_zero {R : ℝ} {U : Set ℂ} (p : ℝ × ℂ) :
    complexProfile (0 : AxisFunction R U) p = 0 := rfl
@[simp] theorem complexProfile_one {R : ℝ} {U : Set ℂ} (p : ℝ × ℂ) :
    complexProfile (1 : AxisFunction R U) p = 1 := rfl
@[simp] theorem complexProfile_realConstant (R : ℝ) (U : Set ℂ) (b : ℝ) (p : ℝ × ℂ) :
    complexProfile (realConstant R U b) p = (b : ℂ) := rfl
@[simp] theorem complexProfile_parameter (R : ℝ) (U : Set ℂ) (p : ℝ × ℂ) :
    complexProfile (parameter R U) p = p.2 := rfl
@[simp] theorem complexProfile_squaredRadius (R : ℝ) (U : Set ℂ) {X : ℝ} (hX : 0 ≤ X) (z : ℂ) :
    complexProfile (squaredRadius R U) (X, z) = (X : ℂ) := by
  change ((Real.sqrt X ^ 2 : ℝ) : ℂ) = _
  rw [Real.sq_sqrt hX]
@[simp] theorem complexProfile_inverseDenominator {R : ℝ} {U : Set ℂ} {h : ℝ}
    (c : Domain R U h) (p : ℝ × ℂ) :
    complexProfile (inverseDenominator c) p = (PositiveAxisSystem.ell (h : ℂ) p.2)⁻¹ := by
  change (denominatorFunction R U h (Real.sqrt p.1, p.2))⁻¹ = _
  rw [denominatorFunction_apply]

theorem timeOperator_value {R : ℝ} {U : Set ℂ} {h : ℝ} (c : Domain R U h)
    (b : ℝ) (F : AxisFunction R U) {X eta : ℝ} (hX : X ∈ Ioo (0 : ℝ) (R ^ 2))
    (heta : (eta : ℂ) ∈ U) :
    complexProfile (timeOperator c b F) (X, (eta : ℂ)) =
      (SimilarityProfile.T h b (profile F) (X, eta) : ℂ) := by
  simp only [timeOperator, complexProfile_mul, complexProfile_add, complexProfile_neg,
    complexProfile_realConstant, complexProfile_parameter, complexProfile_squaredRadius R U hX.1.le,
    complexProfile_inverseDenominator, complexProfile_real c.positive F ⟨hX.1.le, hX.2⟩ heta,
    radialDerivative_value c.positive c.open_set F hX heta,
    parameterDerivative_value c.positive c.open_set F hX heta,
    SimilarityProfile.T, CoordinateAlgebra.timeCoeff, CoordinateAlgebra.L,
    PositiveAxisSystem.ell, Complex.ofReal_add, Complex.ofReal_sub,
    Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_one, div_eq_mul_inv]
  norm_num [CoordinateAlgebra.D]

theorem axialOperator_value {R : ℝ} {U : Set ℂ} {h : ℝ} (c : Domain R U h)
    (b : ℝ) (F : AxisFunction R U) {X eta : ℝ} (hX : X ∈ Ioo (0 : ℝ) (R ^ 2))
    (heta : (eta : ℂ) ∈ U) :
    complexProfile (axialOperator c b F) (X, (eta : ℂ)) =
      (SimilarityProfile.Z h b (profile F) (X, eta) : ℂ) := by
  simp only [axialOperator, complexProfile_mul, complexProfile_sub, complexProfile_add,
    complexProfile_pow, complexProfile_one, complexProfile_realConstant, complexProfile_parameter,
    complexProfile_squaredRadius R U hX.1.le, complexProfile_inverseDenominator,
    complexProfile_real c.positive F ⟨hX.1.le, hX.2⟩ heta,
    radialDerivative_value c.positive c.open_set F hX heta,
    parameterDerivative_value c.positive c.open_set F hX heta,
    SimilarityProfile.Z, CoordinateAlgebra.axialCoeff, CoordinateAlgebra.L,
    PositiveAxisSystem.ell, Complex.ofReal_add, Complex.ofReal_sub,
    Complex.ofReal_mul, Complex.ofReal_ofNat, div_eq_mul_inv]
  simp [CoordinateAlgebra.d]

theorem axialOperator_germ {R : ℝ} {U : Set ℂ} {h : ℝ} (c : Domain R U h)
    (b : ℝ) (F : AxisFunction R U) {X eta : ℝ} (hX : X ∈ Ioo (0 : ℝ) (R ^ 2))
    (heta : (eta : ℂ) ∈ U) :
    profile (axialOperator c b F) =ᶠ[𝓝 (X, eta)] SimilarityProfile.Z h b (profile F) := by
  filter_upwards [(isOpen_Ioo.prod (PositiveAxisExistence.realParameterDomain_isOpen
    c.open_set)).mem_nhds
    (show (X, eta) ∈ Ioo (0 : ℝ) (R ^ 2) ×ˢ PositiveAxisExistence.realParameterDomain U from ⟨hX,
      heta⟩)] with p hp
  exact congrArg Complex.re (axialOperator_value c b F hp.1 hp.2)

theorem axialOperator_twice_value {R : ℝ} {U : Set ℂ} {h : ℝ} (c : Domain R U h)
    (b₁ b₂ : ℝ) (F : AxisFunction R U) {X eta : ℝ} (hX : X ∈ Ioo (0 : ℝ) (R ^ 2))
    (heta : (eta : ℂ) ∈ U) :
    complexProfile (axialOperator c b₂ (axialOperator c b₁ F)) (X, (eta : ℂ)) =
      (SimilarityProfile.Z h b₂ (SimilarityProfile.Z h b₁ (profile F)) (X, eta) : ℂ) := by
  rw [axialOperator_value c b₂ _ hX heta,
    AxisSourceRegularity.Z_congr_germ h b₂ (axialOperator_germ c b₁ F hX heta)]

@[simp] theorem complexProfile_sum {ι : Type*} {R : ℝ} {U : Set ℂ}
    (s : Finset ι) (F : ι → AxisFunction R U) (p : ℝ × ℂ) :
    complexProfile (∑ i ∈ s, F i) p = ∑ i ∈ s, complexProfile (F i) p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp only [Finset.sum_insert ha, complexProfile_add, ih]

noncomputable def priorDiffusion {R : ℝ} {U : Set ℂ} {h : ℝ} (c : Domain R U h)
    (b : ℝ) (F : ℕ → AxisFunction R U) (n : ℕ) : AxisFunction R U :=
  if n = 0 then 0 else
    axialOperator c (b + PositiveAxisSystem.slowPower h (n - 1) - PositiveAxisSystem.dScale h)
      (axialOperator c (b + PositiveAxisSystem.slowPower h (n - 1)) (F (n - 1)))

theorem priorDiffusion_value {R : ℝ} {U : Set ℂ} {h : ℝ} (c : Domain R U h)
    (b : ℝ) (F : ℕ → AxisFunction R U) (n : ℕ) {X eta : ℝ}
    (hX : X ∈ Ioo (0 : ℝ) (R ^ 2)) (heta : (eta : ℂ) ∈ U) :
    complexProfile (priorDiffusion c b F n) (X, (eta : ℂ)) =
      (PositiveAxisSystem.precedingDiffusion h b (fun j => profile (F j)) n (X, eta) : ℂ) := by
  by_cases hn : n = 0
  · simp [priorDiffusion, PositiveAxisSystem.precedingDiffusion, hn]
  · simp only [priorDiffusion, PositiveAxisSystem.precedingDiffusion, ite_eq_right hn]
    exact axialOperator_twice_value c _ _ _ hX heta

noncomputable def shiftedBetaDiffusion {R : ℝ} {U : Set ℂ} {h : ℝ} (c : Domain R U h)
    (F : ℕ → AxisFunction R U) : ℕ → AxisFunction R U
  | 0 => 0
  | k + 1 => axialOperator c (AxisSourceRegularity.slowOrder h k - 1 - SimilarityProfile.D h)
      (axialOperator c (AxisSourceRegularity.slowOrder h k - 1) (F k))

theorem shiftedBetaDiffusion_value {R : ℝ} {U : Set ℂ} {h : ℝ} (c : Domain R U h)
    (F : ℕ → AxisFunction R U) (k : ℕ) {X eta : ℝ}
    (hX : X ∈ Ioo (0 : ℝ) (R ^ 2)) (heta : (eta : ℂ) ∈ U) :
    complexProfile (shiftedBetaDiffusion c F k) (X, (eta : ℂ)) =
      (AxisSourceRegularity.shiftedAxialFactor h (fun j => profile (F j)) k (X, eta) : ℂ) := by
  cases k with
  | zero => rfl
  | succ k => exact axialOperator_twice_value c _ _ _ hX heta

noncomputable def radialSource {R : ℝ} {U : Set ℂ} {h : ℝ} (c : Domain R U h)
    (u beta : ℕ → AxisFunction R U) (k : ℕ) : AxisFunction R U :=
  timeOperator c (AxisSourceRegularity.slowOrder h k - 1) (beta k) +
    (∑ ij ∈ Finset.antidiagonal k,
      (beta ij.1 * (realConstant R U (1 / 2) * beta ij.2 +
        squaredRadius R U * radialDerivative c.positive c.open_set (beta ij.2)) +
      u ij.1 * axialOperator c (AxisSourceRegularity.slowOrder h ij.2 - 1) (beta ij.2))) -
    (realConstant R U 4 * radialDerivative c.positive c.open_set (beta k) +
      realConstant R U 2 * squaredRadius R U *
        radialDerivative c.positive c.open_set (radialDerivative c.positive c.open_set (beta k))) -
    shiftedBetaDiffusion c beta k

theorem radialSource_value {R : ℝ} {U : Set ℂ} {h : ℝ} (c : Domain R U h)
    (u beta : ℕ → AxisFunction R U) (k : ℕ) {X eta : ℝ}
    (hX : X ∈ Ioo (0 : ℝ) (R ^ 2)) (heta : (eta : ℂ) ∈ U) :
    complexProfile (radialSource c u beta k) (X, (eta : ℂ)) =
      (AxisSourceRegularity.omegaDivX h (fun j => profile (u j)) (fun j => profile (beta j))
        k (X, eta) : ℂ) := by
  simp only [radialSource, AxisSourceRegularity.omegaDivX, complexProfile_sub, complexProfile_add,
    complexProfile_mul, complexProfile_realConstant, complexProfile_sum,
    complexProfile_squaredRadius R U hX.1.le, timeOperator_value c _ _ hX heta,
    axialOperator_value c _ _ hX heta, shiftedBetaDiffusion_value c _ _ hX heta,
    radialDerivative_value c.positive c.open_set _ hX heta,
    Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_sum,
    Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  simp only [complexProfile_real c.positive _ ⟨hX.1.le, hX.2⟩ heta]
  congr 3
  · apply Finset.sum_congr rfl
    intro ij _
    ring
  · unfold SimilarityProfile.partialX
    rw [(profile_radialDerivative_germ c.positive c.open_set (beta k) hX heta).fderiv_eq]
    rfl

noncomputable def previousRadialSource {R : ℝ} {U : Set ℂ} {h : ℝ} (c : Domain R U h)
    (u beta : ℕ → AxisFunction R U) : ℕ → AxisFunction R U
  | 0 => 0
  | k + 1 => radialSource c u beta k

theorem previousRadialSource_value {R : ℝ} {U : Set ℂ} {h : ℝ} (c : Domain R U h)
    (u beta : ℕ → AxisFunction R U) (n : ℕ) {X eta : ℝ}
    (hX : X ∈ Ioo (0 : ℝ) (R ^ 2)) (heta : (eta : ℂ) ∈ U) :
    complexProfile (previousRadialSource c u beta n) (X, (eta : ℂ)) =
      (AxisSourceRegularity.previousOmegaDivX h (fun j => profile (u j))
        (fun j => profile (beta j)) n (X, eta) : ℂ) := by
  cases n with
  | zero => rfl
  | succ k => exact radialSource_value c u beta k hX heta

noncomputable def angularSource {R : ℝ} {U : Set ℂ} {h : ℝ} (c : Domain R U h)
    (phi u beta : ℕ → AxisFunction R U) (n : ℕ) : AxisFunction R U :=
  (∑ i ∈ Finset.range (n - 1),
    (beta (i + 1) * (squaredRadius R U * radialDerivative c.positive c.open_set (phi (n - (i + 1)))
      +
      phi (n - (i + 1))) + u (i + 1) *
      axialOperator c (PositiveAxisSystem.angularPower h + PositiveAxisSystem.slowPower h (n - (i +
        1)))
        (phi (n - (i + 1))))) - priorDiffusion c (PositiveAxisSystem.angularPower h) phi n

noncomputable def axialSource {R : ℝ} {U : Set ℂ} {h : ℝ} (c : Domain R U h)
    (u beta : ℕ → AxisFunction R U) (n : ℕ) : AxisFunction R U :=
  (∑ i ∈ Finset.range (n - 1),
    (beta (i + 1) * squaredRadius R U * radialDerivative c.positive c.open_set (u (n - (i + 1))) +
      u (i + 1) * axialOperator c
        (PositiveAxisSystem.axialPower h + PositiveAxisSystem.slowPower h (n - (i + 1))) (u (n - (i
          + 1))))) -
    priorDiffusion c (PositiveAxisSystem.axialPower h) u n

noncomputable def pressureProduct {R : ℝ} {U : Set ℂ} (phi : ℕ → AxisFunction R U)
    (n : ℕ) : AxisFunction R U :=
  ∑ i ∈ Finset.range (n - 1), phi (i + 1) * phi (n - (i + 1))

/-- Each of the eleven inputs is an actual member of the smooth function
algebra; their regularity follows by construction from the lower profiles. -/
noncomputable def sourceFunctions {R : ℝ} {U : Set ℂ} {h : ℝ} (c : Domain R U h)
    (phi u beta : ℕ → AxisFunction R U) (n : ℕ) : Fin 11 → AxisFunction R U :=
  ![phi 0, radialDerivative c.positive c.open_set (phi 0), parameterDerivative c.open_set (phi 0),
    u 0, radialDerivative c.positive c.open_set (u 0), parameterDerivative c.open_set (u 0), beta 0,
    angularSource c phi u beta n, axialSource c u beta n, pressureProduct phi n,
    previousRadialSource c u beta n]

noncomputable def sourceData {R : ℝ} {U : Set ℂ} {h : ℝ} (c : Domain R U h)
    (phi u beta : ℕ → AxisFunction R U) (n : ℕ) : PositiveAxisSystem.CoefficientData :=
  fun i => complexProfile (sourceFunctions c phi u beta n i)

theorem sourceData_regular {R : ℝ} {U : Set ℂ} {h : ℝ} (c : Domain R U h)
    (phi u beta : ℕ → AxisFunction R U) (n : ℕ) :
    PositiveAxisExistence.LowerInputRegularity R U (h : ℂ) (sourceData c phi u beta n) := by
  refine ⟨?_, ?_, c.denominator⟩
  · intro i
    have hs := (sourceFunctions c phi u beta n i).2.smooth
    have hs' : ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => sourceData c phi u beta n i (p.1 ^ 2, p.2))
        (Ioo (-R) R ×ˢ U) := hs.congr (fun p hp => complexProfile_square _ hp.1 hp.2)
    simpa only [VolterraRegularity.radialDomain, Real.ball_eq_Ioo, sub_self, zero_sub, zero_add]
      using hs'
  · intro r hr i
    have hr' : r ∈ Ioo (-R) R := by simpa [VolterraRegularity.radialDomain, Real.ball_eq_Ioo] using
      hr
    exact ((sourceFunctions c phi u beta n i).2.holomorphic r hr').congr
      (fun z hz => complexProfile_square _ hr' hz)

theorem sourceData_real {R : ℝ} {U : Set ℂ} {h : ℝ} (c : Domain R U h)
    (phi u beta : ℕ → AxisFunction R U) (n : ℕ) :
    PositiveAxisExistence.RealCompatible R U (sourceData c phi u beta n)
      (PositiveAxisExistence.lowerHistoryData h n (fun j => profile (phi j)) (fun j => profile (u
        j))
        (fun j => profile (beta j)) (AxisSourceRegularity.previousOmegaDivX h
          (fun j => profile (u j)) (fun j => profile (beta j)) n)) := by
  intro X hX eta heta i
  have hv (F : AxisFunction R U) := complexProfile_real c.positive F ⟨hX.1.le, hX.2⟩ heta
  have hd (F : AxisFunction R U) := radialDerivative_value c.positive c.open_set F hX heta
  have he (F : AxisFunction R U) := parameterDerivative_value c.positive c.open_set F hX heta
  fin_cases i <;>
    simp only [sourceData, sourceFunctions, PositiveAxisExistence.lowerHistoryData]
  · exact hv _
  · exact hd _
  · exact he _
  · exact hv _
  · exact hd _
  · exact he _
  · exact hv _
  · change complexProfile (angularSource c phi u beta n) (X, (eta : ℂ)) =
      ((PositiveAxisSystem.actualLowerSource h n (fun j => profile (phi j)) (fun j => profile (u j))
        (fun j => profile (beta j)) (AxisSourceRegularity.previousOmegaDivX h
          (fun j => profile (u j)) (fun j => profile (beta j)) n) (X, eta)).angular : ℂ)
    simp only [angularSource, PositiveAxisSystem.actualLowerSource, PositiveAxisSystem.lowerSource,
      PositiveAxisSystem.lowerConvolution, PositiveAxisSystem.angularConvection,
      complexProfile_sub, complexProfile_sum, complexProfile_add, complexProfile_mul,
      complexProfile_squaredRadius R U hX.1.le, hd,
      axialOperator_value c _ _ hX heta, priorDiffusion_value c _ _ _ hX heta,
      Complex.ofReal_sub, Complex.ofReal_sum, Complex.ofReal_add, Complex.ofReal_mul,
        PositiveAxisSystem.actualJet]
    simp only [hv]
    rfl
  · change complexProfile (axialSource c u beta n) (X, (eta : ℂ)) =
      ((PositiveAxisSystem.actualLowerSource h n (fun j => profile (phi j)) (fun j => profile (u j))
        (fun j => profile (beta j)) (AxisSourceRegularity.previousOmegaDivX h
          (fun j => profile (u j)) (fun j => profile (beta j)) n) (X, eta)).axial : ℂ)
    simp only [axialSource, PositiveAxisSystem.actualLowerSource, PositiveAxisSystem.lowerSource,
      PositiveAxisSystem.lowerConvolution, PositiveAxisSystem.axialConvection,
      complexProfile_sub, complexProfile_sum, complexProfile_add, complexProfile_mul,
      complexProfile_squaredRadius R U hX.1.le, hd,
      axialOperator_value c _ _ hX heta, priorDiffusion_value c _ _ _ hX heta,
      Complex.ofReal_sub, Complex.ofReal_sum, Complex.ofReal_add, Complex.ofReal_mul,
        PositiveAxisSystem.actualJet]
    simp only [hv]
    rfl
  · change complexProfile (pressureProduct phi n) (X, (eta : ℂ)) =
      ((PositiveAxisSystem.actualLowerSource h n (fun j => profile (phi j)) (fun j => profile (u j))
        (fun j => profile (beta j)) (AxisSourceRegularity.previousOmegaDivX h
          (fun j => profile (u j)) (fun j => profile (beta j)) n) (X, eta)).pressureProduct : ℂ)
    simp only [pressureProduct, PositiveAxisSystem.actualLowerSource,
      PositiveAxisSystem.lowerSource,
      PositiveAxisSystem.lowerConvolution, complexProfile_sum, complexProfile_mul,
      Complex.ofReal_sum, Complex.ofReal_mul, PositiveAxisSystem.actualJet]
    simp only [hv]
  · exact previousRadialSource_value c u beta n hX heta

noncomputable def betaOperator {R : ℝ} {U : Set ℂ} {h : ℝ} (c : Domain R U h)
    (n : ℕ) (u k : AxisFunction R U) : AxisFunction R U :=
  (realConstant R U 2 * parameter R U *
      realConstant R U (PositiveAxisSystem.a h - PositiveAxisSystem.slowPower h n) * u -
    realConstant R U 2 * parameter R U *
      realConstant R U (PositiveAxisSystem.dScale h + PositiveAxisSystem.slowPower h n) * k -
    (1 - parameter R U ^ 2) * (parameterDerivative c.open_set u + parameterDerivative c.open_set
      k)) *
    inverseDenominator c

theorem betaOperator_value {R : ℝ} {U : Set ℂ} {h : ℝ} (c : Domain R U h)
    (n : ℕ) (u k : AxisFunction R U) {X eta : ℝ}
    (hX : X ∈ Ioo (0 : ℝ) (R ^ 2)) (heta : (eta : ℂ) ∈ U) :
    complexProfile (betaOperator c n u k) (X, (eta : ℂ)) =
      (PositiveAxisExistence.newBeta h n (profile u) (profile k) (X, eta) : ℂ) := by
  simp only [betaOperator, complexProfile_mul, complexProfile_sub, complexProfile_add,
    complexProfile_pow, complexProfile_one, complexProfile_realConstant, complexProfile_parameter,
    complexProfile_inverseDenominator, parameterDerivative_value c.positive c.open_set _ hX heta,
    PositiveAxisExistence.newBeta, PositiveAxisSystem.betaValue, PositiveAxisSystem.actualJet,
    PositiveAxisSystem.ell, PositiveAxisSystem.edge,
    Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_add,
    Complex.ofReal_pow, Complex.ofReal_one, Complex.ofReal_ofNat]
  simp only [complexProfile_real c.positive _ ⟨hX.1.le, hX.2⟩ heta]
  rw [div_eq_mul_inv]

abbrev Coefficient (R : ℝ) (U : Set ℂ) := Fin 5 → AxisFunction R U

noncomputable def stepRaw {R S : ℝ} {U : Set ℂ} {h : ℝ} (c : Domain R U h)
    (hS : 0 < S) (C : ℝ) (n : ℕ) (F : ℕ → Coefficient R U) : VolterraAnalyticBounds.Field :=
  PositiveAxisExistence.positiveSolution hS.le (h : ℂ)
    ((PositiveAxisSystem.slowPower h n : ℝ) : ℂ) (C : ℂ)
    (sourceData c (fun j => F j 0) (fun j => F j 1) (fun j => F j 4) n)

noncomputable def stepComponent {R S : ℝ} {U : Set ℂ} {h : ℝ} (c : Domain R U h)
    (hS : 0 < S) (hSR : S < R) (C : ℝ) (n : ℕ) (F : ℕ → Coefficient R U)
    (i : Fin 6) (hi : i.val < 4) : AxisFunction S U := by
  let W := stepRaw c hS C n F
  have hdata := sourceData_regular c (fun j => F j 0) (fun j => F j 1) (fun j => F j 4) n
  have hs : ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => W p.1 p.2 i) (Ioo (-S) S ×ˢ U) := by
    simpa only [W, stepRaw, VolterraRegularity.radialDomain, Real.ball_eq_Ioo,
      zero_sub, zero_add] using
      (contDiffOn_pi.mp (PositiveAxisExistence.positiveSolution_jointly_smooth hS.le hSR c.open_set
        ((PositiveAxisSystem.slowPower h n : ℝ) : ℂ) (C : ℂ) hdata) i)
  have hw := PositiveAxisExistence.positiveSolution_spec hS.le hSR c.open_set
    ((PositiveAxisSystem.slowPower h n : ℝ) : ℂ) (C : ℂ) hdata
  have hh : ∀ r ∈ Ioo (-S) S, DifferentiableOn ℂ (fun z => W r z i) U :=
    fun r hr => hw.parameter_holomorphic r ⟨hr.1.le, hr.2.le⟩ i
  have he : ∀ z ∈ U, ∀ r ∈ Ioo (-S) S, W (-r) z i = W r z i := by
    intro z hz r hr
    apply VolterraParity.first_components_even (i := i)
      (fun r hr z hz => PositiveAxisExistence.positiveSolution_parity hS.le hSR c.open_set
        ((PositiveAxisSystem.slowPower h n : ℝ) : ℂ) (C : ℂ) hdata hr hz) hi hz r hr
  exact symmetrize c.open_set c.conjugate (fun p => W p.1 p.2 i) hs hh he

theorem stepComponent_profile {R S : ℝ} {U : Set ℂ} {h : ℝ} (c : Domain R U h)
    (hS : 0 < S) (hSR : S < R) (C : ℝ) (n : ℕ) (F : ℕ → Coefficient R U)
    (i : Fin 6) (hi : i.val < 4) :
    profile (stepComponent c hS hSR C n F i hi) = PositiveAxisExistence.xProfile (stepRaw c hS C n
      F) i := by
  funext p
  change (realSymmetrization (fun q => stepRaw c hS C n F q.1 q.2 i)
    (Real.sqrt p.1, (p.2 : ℂ))).re = _
  rw [realSymmetrization_real]
  rfl

theorem stepComponent_axis_zero {R S : ℝ} {U : Set ℂ} {h : ℝ} (c : Domain R U h)
    (hS : 0 < S) (hSR : S < R) (C : ℝ) (n : ℕ) (F : ℕ → Coefficient R U)
    (i : Fin 6) (hi : i.val < 4) {z : ℂ} (hz : z ∈ U) :
    stepComponent c hS hSR C n F i hi (0, z) = 0 := by
  have hw := PositiveAxisExistence.positiveSolution_spec hS.le hSR c.open_set
    ((PositiveAxisSystem.slowPower h n : ℝ) : ℂ) (C : ℂ)
    (sourceData_regular c (fun j => F j 0) (fun j => F j 1) (fun j => F j 4) n)
  change (stepRaw c hS C n F 0 z i + starRingEnd ℂ (stepRaw c hS C n F 0 (starRingEnd ℂ z) i)) / 2
    = 0
  have hz₁ : stepRaw c hS C n F 0 z i = 0 := congrFun (hw.axis_zero z hz) i
  have hz₂ : stepRaw c hS C n F 0 (starRingEnd ℂ z) i = 0 :=
    congrFun (hw.axis_zero _ (c.conjugate z hz)) i
  rw [hz₁, hz₂, map_zero, add_zero, zero_div]

/-- One actual inductive step. The first four profiles come from the
convergent Volterra solution; the fifth is the genuine divergence formula. -/
noncomputable def step {R S : ℝ} {U : Set ℂ} {h : ℝ} (c : Domain R U h)
    (hS : 0 < S) (hSR : S < R) (C : ℝ) (n : ℕ) (F : ℕ → Coefficient R U) : Coefficient S U :=
  let a := stepComponent c hS hSR C n F 0 (by decide)
  let u := stepComponent c hS hSR C n F 1 (by decide)
  let k := stepComponent c hS hSR C n F 2 (by decide)
  let p := stepComponent c hS hSR C n F 3 (by decide)
  ![a, u, k, p, betaOperator (c.restrict hS) n u k]

theorem step_profile {R S : ℝ} {U : Set ℂ} {h : ℝ} (c : Domain R U h)
    (hS : 0 < S) (hSR : S < R) (C : ℝ) (n : ℕ) (F : ℕ → Coefficient R U)
    (i : Fin 4) :
    profile (step c hS hSR C n F ⟨i.val, by omega⟩) =
      PositiveAxisExistence.xProfile (stepRaw c hS C n F) ⟨i.val, by omega⟩ := by
  fin_cases i <;> exact stepComponent_profile c hS hSR C n F _ (by decide)

theorem sourceData_real_smaller {R S : ℝ} {U : Set ℂ} {h : ℝ} (c : Domain R U h)
    (hS : 0 < S) (hSR : S ≤ R) (phi u beta : ℕ → AxisFunction R U) (n : ℕ) :
    PositiveAxisExistence.RealCompatible S U (sourceData c phi u beta n)
      (PositiveAxisExistence.lowerHistoryData h n (fun j => profile (phi j)) (fun j => profile (u
        j))
        (fun j => profile (beta j)) (AxisSourceRegularity.previousOmegaDivX h
          (fun j => profile (u j)) (fun j => profile (beta j)) n)) := by
  intro X hX eta heta i
  apply sourceData_real c phi u beta n X _ eta heta i
  exact ⟨hX.1, lt_of_lt_of_le hX.2 (sq_le_sq₀ hS.le c.positive.le |>.2 hSR)⟩

theorem step_beta {R S : ℝ} {U : Set ℂ} {h : ℝ} (c : Domain R U h)
    (hS : 0 < S) (hSR : S < R) (C : ℝ) (n : ℕ) (F : ℕ → Coefficient R U)
    {X eta : ℝ} (hX : X ∈ Ioo (0 : ℝ) (S ^ 2)) (heta : (eta : ℂ) ∈ U) :
    profile (step c hS hSR C n F 4) (X, eta) = PositiveAxisExistence.newBeta h n
      (profile (step c hS hSR C n F 1)) (profile (step c hS hSR C n F 2)) (X, eta) :=
  congrArg Complex.re (betaOperator_value (c.restrict hS) n _ _ hX heta)

theorem step_expanded {R S : ℝ} {U : Set ℂ} {h : ℝ} (c : Domain R U h)
    (hS : 0 < S) (hSR : S < R) (C : ℝ) (n : ℕ) (F : ℕ → Coefficient R U)
    {X eta : ℝ} (hX : X ∈ Ioo (0 : ℝ) (S ^ 2)) (heta : (eta : ℂ) ∈ U) :
    PositiveAxisSystem.ExpandedEquations h (PositiveAxisSystem.slowPower h n) C eta X
      (PositiveAxisSystem.baseAtOrderZero
        (fun j => PositiveAxisSystem.actualJet (profile (F j 0)) (X, eta))
        (fun j => PositiveAxisSystem.actualJet (profile (F j 1)) (X, eta))
        (fun j => profile (F j 4) (X, eta)))
      (PositiveAxisSystem.actualLowerSource h n (fun j => profile (F j 0)) (fun j => profile (F j
        1))
        (fun j => profile (F j 4)) (AxisSourceRegularity.previousOmegaDivX h
          (fun j => profile (F j 1)) (fun j => profile (F j 4)) n) (X, eta))
      (PositiveAxisSystem.actualJet (profile (step c hS hSR C n F 0)) (X, eta))
      (PositiveAxisSystem.actualJet (profile (step c hS hSR C n F 1)) (X, eta))
      (PositiveAxisSystem.actualJet (profile (step c hS hSR C n F 2)) (X, eta))
      (PositiveAxisSystem.actualJet (profile (step c hS hSR C n F 3)) (X, eta)) := by
  let r := Real.sqrt X
  have hr : r ∈ Ioo (-S) S := sqrt_mem hS ⟨hX.1.le, hX.2⟩
  have hr0 : r ≠ 0 := (Real.sqrt_pos.mpr hX.1).ne'
  have hrX : r ^ 2 = X := Real.sq_sqrt hX.1.le
  have hd := sourceData_regular c (fun j => F j 0) (fun j => F j 1) (fun j => F j 4) n
  have hreal := sourceData_real_smaller c hS hSR.le (fun j => F j 0) (fun j => F j 1) (fun j => F j
    4) n
  have he := PositiveAxisExistence.positiveSolution_profiles_system hS hSR c.open_set
    h (PositiveAxisSystem.slowPower h n) C hd hreal hr hr0 heta
  have h0 : profile (step c hS hSR C n F 0) = PositiveAxisExistence.xProfile (stepRaw c hS C n F) 0
    :=
    step_profile c hS hSR C n F 0
  have h1 : profile (step c hS hSR C n F 1) = PositiveAxisExistence.xProfile (stepRaw c hS C n F) 1
    :=
    step_profile c hS hSR C n F 1
  have h2 : profile (step c hS hSR C n F 2) = PositiveAxisExistence.xProfile (stepRaw c hS C n F) 2
    :=
    step_profile c hS hSR C n F 2
  have h3 : profile (step c hS hSR C n F 3) = PositiveAxisExistence.xProfile (stepRaw c hS C n F) 3
    :=
    step_profile c hS hSR C n F 3
  have hsm (i : Fin 5) : ContDiffAt ℝ ∞ (profile (step c hS hSR C n F i)) (r ^ 2, eta) := by
    rw [hrX]
    exact profile_contDiffAt hS c.open_set _ hX heta
  let G := PositiveAxisExistence.lowerHistoryData h n (fun j => profile (F j 0))
    (fun j => profile (F j 1)) (fun j => profile (F j 4))
    (AxisSourceRegularity.previousOmegaDivX h (fun j => profile (F j 1)) (fun j => profile (F j 4))
      n)
  have he' : PositiveAxisSystem.ProfileSystem h (PositiveAxisSystem.slowPower h n) C r eta
      (PositiveAxisExistence.realBase G (r ^ 2, eta)) (PositiveAxisExistence.realSource G (r ^ 2,
        eta))
      (profile (step c hS hSR C n F 0)) (profile (step c hS hSR C n F 1))
      (profile (step c hS hSR C n F 2)) (profile (step c hS hSR C n F 3)) := by
    rw [h0, h1, h2, h3]
    exact he
  have hout := (PositiveAxisSystem.profileSystem_iff_expanded hr0 _ _
    ((hsm 0).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    ((hsm 1).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    ((hsm 2).differentiableAt (by simp)) ((hsm 3).differentiableAt (by simp))).mp he'
  simp only [hrX] at hout ⊢
  exact hout

theorem betaOperator_axis_zero {R : ℝ} {U : Set ℂ} {h : ℝ} (c : Domain R U h)
    (n : ℕ) (u k : AxisFunction R U)
    (hu : ∀ z ∈ U, u (0, z) = 0) (hk : ∀ z ∈ U, k (0, z) = 0)
    {z : ℂ} (hz : z ∈ U) : betaOperator c n u k (0, z) = 0 := by
  have hd (F : AxisFunction R U) (hF : ∀ z ∈ U, F (0, z) = 0) :
      parameterDerivative c.open_set F (0, z) = 0 := by
    have he : (fun w => F (0, w)) =ᶠ[𝓝 z] (fun _ => (0 : ℂ)) := by
      filter_upwards [c.open_set.mem_nhds hz] with w hw
      exact hF w hw
    exact he.deriv_eq.trans (deriv_const z 0)
  change (2 * z * _ * u (0, z) - 2 * z * _ * k (0, z) -
    (1 - z ^ 2) * (parameterDerivative c.open_set u (0, z) + parameterDerivative c.open_set k (0,
      z))) * _ = 0
  rw [hu z hz, hk z hz, hd u hu, hd k hk]
  ring

theorem step_axis_zero {R S : ℝ} {U : Set ℂ} {h : ℝ} (c : Domain R U h)
    (hS : 0 < S) (hSR : S < R) (C : ℝ) (n : ℕ) (F : ℕ → Coefficient R U)
    (i : Fin 5) {z : ℂ} (hz : z ∈ U) : step c hS hSR C n F i (0, z) = 0 := by
  fin_cases i
  · exact stepComponent_axis_zero c hS hSR C n F 0 (by decide) hz
  · exact stepComponent_axis_zero c hS hSR C n F 1 (by decide) hz
  · exact stepComponent_axis_zero c hS hSR C n F 2 (by decide) hz
  · exact stepComponent_axis_zero c hS hSR C n F 3 (by decide) hz
  · exact betaOperator_axis_zero (c.restrict hS) n _ _
      (fun _ hz => stepComponent_axis_zero c hS hSR C n F 1 (by decide) hz)
      (fun _ hz => stepComponent_axis_zero c hS hSR C n F 2 (by decide) hz) hz

/-- Buffer radii approach a fixed positive core without ever reaching it. -/
noncomputable def radius (core buffer : ℝ) (n : ℕ) : ℝ :=
  core + buffer / ((n : ℝ) + 1)

theorem core_lt_radius {core buffer : ℝ} (hbuffer : 0 < buffer) (n : ℕ) :
    core < radius core buffer n := by
  unfold radius
  have hd : 0 < buffer / ((n : ℝ) + 1) := div_pos hbuffer (by positivity)
  linarith

theorem radius_pos {core buffer : ℝ} (hcore : 0 < core) (hbuffer : 0 < buffer) (n : ℕ) :
    0 < radius core buffer n := lt_trans hcore (core_lt_radius hbuffer n)

theorem radius_antitone {core buffer : ℝ} (hbuffer : 0 ≤ buffer) : Antitone (radius core buffer) :=
  by
  intro m n hmn
  unfold radius
  apply add_le_add_right
  apply div_le_div_of_nonneg_left hbuffer (by positivity)
  exact_mod_cast Nat.add_le_add_right hmn 1

theorem radius_succ_lt {core buffer : ℝ} (hbuffer : 0 < buffer) (n : ℕ) :
    radius core buffer (n + 1) < radius core buffer n := by
  unfold radius
  apply add_lt_add_right
  apply div_lt_div_of_pos_left hbuffer (by positivity)
  norm_num

theorem radiusDomain {core buffer : ℝ} {U : Set ℂ} {h : ℝ}
    (c : Domain (radius core buffer 0) U h) (hcore : 0 < core) (hbuffer : 0 < buffer) (n : ℕ) :
    Domain (radius core buffer n) U h := c.restrict (radius_pos hcore hbuffer n)

/-- Only coefficients with index below `n` are accessed. The zero branch
is outside every finite source sum and is not an assumed future coefficient. -/
noncomputable def lowerHistory {core buffer : ℝ} {U : Set ℂ} (hbuffer : 0 < buffer) (n : ℕ)
    (previous : (j : ℕ) → j < n → Coefficient (radius core buffer j) U) :
    ℕ → Coefficient (radius core buffer (n - 1)) U :=
  fun j => if hj : j < n then
    fun i => restrict (radius_antitone hbuffer.le (by omega : j ≤ n - 1)) (previous j hj i)
  else 0

theorem lowerHistory_apply {core buffer : ℝ} {U : Set ℂ} (hbuffer : 0 < buffer) (n : ℕ)
    (previous : (j : ℕ) → j < n → Coefficient (radius core buffer j) U)
    {j : ℕ} (hj : j < n) (i : Fin 5) (p : ℝ × ℂ) :
    lowerHistory hbuffer n previous j i p = previous j hj i p := by
  simp only [lowerHistory, dite_eq_left hj, restrict_apply]

noncomputable def recursionStep {core buffer : ℝ} {U : Set ℂ} {h : ℝ}
    (c : Domain (radius core buffer 0) U h) (hcore : 0 < core) (hbuffer : 0 < buffer)
    (C : ℝ) (base : Coefficient (radius core buffer 0) U) :
    (n : ℕ) → ((j : ℕ) → j < n → Coefficient (radius core buffer j) U) → Coefficient (radius core
      buffer n) U
  | 0, _ => base
  | n + 1, previous => step (radiusDomain c hcore hbuffer n)
      (radius_pos hcore hbuffer (n + 1)) (radius_succ_lt hbuffer n) C (n + 1)
      (lowerHistory hbuffer (n + 1) previous)

/-- The actual sequence is built by well-founded recursion from one base
coefficient. Every recursive input has a strictly smaller slow index. -/
noncomputable def hierarchy {core buffer : ℝ} {U : Set ℂ} {h : ℝ}
    (c : Domain (radius core buffer 0) U h) (hcore : 0 < core) (hbuffer : 0 < buffer)
    (C : ℝ) (base : Coefficient (radius core buffer 0) U) (n : ℕ) :
    Coefficient (radius core buffer n) U :=
  Nat.lt_wfRel.wf.fix (recursionStep c hcore hbuffer C base) n

theorem hierarchy_zero {core buffer : ℝ} {U : Set ℂ} {h : ℝ}
    (c : Domain (radius core buffer 0) U h) (hcore : 0 < core) (hbuffer : 0 < buffer)
    (C : ℝ) (base : Coefficient (radius core buffer 0) U) :
    hierarchy c hcore hbuffer C base 0 = base := by
  unfold hierarchy
  rw [WellFounded.fix_eq]
  rfl

theorem hierarchy_succ {core buffer : ℝ} {U : Set ℂ} {h : ℝ}
    (c : Domain (radius core buffer 0) U h) (hcore : 0 < core) (hbuffer : 0 < buffer)
    (C : ℝ) (base : Coefficient (radius core buffer 0) U) (n : ℕ) :
    hierarchy c hcore hbuffer C base (n + 1) =
      step (radiusDomain c hcore hbuffer n)
        (radius_pos hcore hbuffer (n + 1)) (radius_succ_lt hbuffer n) C (n + 1)
        (lowerHistory hbuffer (n + 1) (fun j _ => hierarchy c hcore hbuffer C base j)) := by
  unfold hierarchy
  rw [WellFounded.fix_eq]
  rfl

/-- All orders on the same radial rectangle and the same complex
parameter neighborhood. Restriction changes no pointwise function value. -/
noncomputable def sequence {core buffer : ℝ} {U : Set ℂ} {h : ℝ}
    (c : Domain (radius core buffer 0) U h) (hcore : 0 < core) (hbuffer : 0 < buffer)
    (C : ℝ) (base : Coefficient (radius core buffer 0) U) (n : ℕ) : Coefficient core U :=
  fun i => restrict (core_lt_radius hbuffer n).le (hierarchy c hcore hbuffer C base n i)

theorem sequence_profile {core buffer : ℝ} {U : Set ℂ} {h : ℝ}
    (c : Domain (radius core buffer 0) U h) (hcore : 0 < core) (hbuffer : 0 < buffer)
    (C : ℝ) (base : Coefficient (radius core buffer 0) U) (n : ℕ) (i : Fin 5) :
    profile (sequence c hcore hbuffer C base n i) = profile (hierarchy c hcore hbuffer C base n i)
      := rfl

theorem sequence_zero {core buffer : ℝ} {U : Set ℂ} {h : ℝ}
    (c : Domain (radius core buffer 0) U h) (hcore : 0 < core) (hbuffer : 0 < buffer)
    (C : ℝ) (base : Coefficient (radius core buffer 0) U) (i : Fin 5) :
    profile (sequence c hcore hbuffer C base 0 i) = profile (base i) := by
  rw [sequence_profile, hierarchy_zero]

theorem lowerHistory_profile {core buffer : ℝ} {U : Set ℂ} {h : ℝ}
    (c : Domain (radius core buffer 0) U h) (hcore : 0 < core) (hbuffer : 0 < buffer)
    (C : ℝ) (base : Coefficient (radius core buffer 0) U) {n j : ℕ} (hj : j < n) (i : Fin 5) :
    profile (lowerHistory hbuffer n (fun j _ => hierarchy c hcore hbuffer C base j) j i) =
      profile (sequence c hcore hbuffer C base j i) := by
  funext p
  exact congrArg Complex.re (lowerHistory_apply hbuffer n _ hj i (Real.sqrt p.1, (p.2 : ℂ)))

theorem previousOmega_congr (h : ℝ) {n : ℕ}
    {u beta u' beta' : ℕ → SimilarityProfile.InnerProfile}
    (hu : ∀ j, j < n → u j = u' j) (hb : ∀ j, j < n → beta j = beta' j) :
    AxisSourceRegularity.previousOmegaDivX h u beta n =
      AxisSourceRegularity.previousOmegaDivX h u' beta' n := by
  cases n with
  | zero => rfl
  | succ k =>
    funext w
    have hs : (∑ ij ∈ Finset.antidiagonal k,
        (beta ij.1 w * (beta ij.2 w / 2 + w.1 * SimilarityProfile.partialX (beta ij.2) w) +
          u ij.1 w * SimilarityProfile.Z h (AxisSourceRegularity.slowOrder h ij.2 - 1) (beta ij.2)
            w)) =
        ∑ ij ∈ Finset.antidiagonal k,
        (beta' ij.1 w * (beta' ij.2 w / 2 + w.1 * SimilarityProfile.partialX (beta' ij.2) w) +
          u' ij.1 w * SimilarityProfile.Z h (AxisSourceRegularity.slowOrder h ij.2 - 1) (beta'
            ij.2) w) := by
      apply Finset.sum_congr rfl
      intro ij hij
      have hij' := Finset.mem_antidiagonal.mp hij
      rw [hb ij.1 (by omega), hb ij.2 (by omega), hu ij.1 (by omega)]
    have hp : AxisSourceRegularity.shiftedAxialFactor h beta k =
        AxisSourceRegularity.shiftedAxialFactor h beta' k := by
      cases k with
      | zero => rfl
      | succ k => simp only [AxisSourceRegularity.shiftedAxialFactor, hb k (by omega)]
    simp only [AxisSourceRegularity.previousOmegaDivX, AxisSourceRegularity.omegaDivX,
      hb k (Nat.lt_succ_self k), hs, hp]

theorem sequence_succ_profile {core buffer : ℝ} {U : Set ℂ} {h : ℝ}
    (c : Domain (radius core buffer 0) U h) (hcore : 0 < core) (hbuffer : 0 < buffer)
    (C : ℝ) (base : Coefficient (radius core buffer 0) U) (n : ℕ) (i : Fin 5) :
    profile (sequence c hcore hbuffer C base (n + 1) i) =
      profile (step (radiusDomain c hcore hbuffer n)
        (radius_pos hcore hbuffer (n + 1)) (radius_succ_lt hbuffer n) C (n + 1)
        (lowerHistory hbuffer (n + 1) (fun j _ => hierarchy c hcore hbuffer C base j)) i) := by
  rw [sequence_profile, hierarchy_succ]

theorem core_square_lt {core buffer X : ℝ} (hcore : 0 < core) (hbuffer : 0 < buffer)
    (hX : X < core ^ 2) (n : ℕ) : X < radius core buffer n ^ 2 := by
  have hr := core_lt_radius (core := core) hbuffer n
  nlinarith

theorem sequence_beta {core buffer : ℝ} {U : Set ℂ} {h : ℝ}
    (c : Domain (radius core buffer 0) U h) (hcore : 0 < core) (hbuffer : 0 < buffer)
    (C : ℝ) (base : Coefficient (radius core buffer 0) U) {n : ℕ} (hn : 0 < n)
    {X eta : ℝ} (hX : X ∈ Ioo (0 : ℝ) (core ^ 2)) (heta : (eta : ℂ) ∈ U) :
    profile (sequence c hcore hbuffer C base n 4) (X, eta) =
      PositiveAxisExistence.newBeta h n (profile (sequence c hcore hbuffer C base n 1))
        (profile (sequence c hcore hbuffer C base n 2)) (X, eta) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  simp only [sequence_succ_profile]
  exact step_beta (radiusDomain c hcore hbuffer m) (radius_pos hcore hbuffer (m + 1))
    (radius_succ_lt hbuffer m) C (m + 1) _
    ⟨hX.1, core_square_lt hcore hbuffer hX.2 (m + 1)⟩ heta

theorem sequence_expanded {core buffer : ℝ} {U : Set ℂ} {h : ℝ}
    (c : Domain (radius core buffer 0) U h) (hcore : 0 < core) (hbuffer : 0 < buffer)
    (C : ℝ) (base : Coefficient (radius core buffer 0) U) {n : ℕ} (hn : 0 < n)
    {X eta : ℝ} (hX : X ∈ Ioo (0 : ℝ) (core ^ 2)) (heta : (eta : ℂ) ∈ U) :
    let A := sequence c hcore hbuffer C base
    PositiveAxisSystem.ExpandedEquations h (PositiveAxisSystem.slowPower h n) C eta X
      (PositiveAxisSystem.baseAtOrderZero
        (fun j => PositiveAxisSystem.actualJet (profile (A j 0)) (X, eta))
        (fun j => PositiveAxisSystem.actualJet (profile (A j 1)) (X, eta))
        (fun j => profile (A j 4) (X, eta)))
      (PositiveAxisSystem.actualLowerSource h n (fun j => profile (A j 0)) (fun j => profile (A j
        1))
        (fun j => profile (A j 4)) (AxisSourceRegularity.previousOmegaDivX h
          (fun j => profile (A j 1)) (fun j => profile (A j 4)) n) (X, eta))
      (PositiveAxisSystem.actualJet (profile (A n 0)) (X, eta))
      (PositiveAxisSystem.actualJet (profile (A n 1)) (X, eta))
      (PositiveAxisSystem.actualJet (profile (A n 2)) (X, eta))
      (PositiveAxisSystem.actualJet (profile (A n 3)) (X, eta)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  let A := sequence c hcore hbuffer C base
  let H := lowerHistory hbuffer (m + 1) (fun j _ => hierarchy c hcore hbuffer C base j)
  have hH (j : ℕ) (hj : j < m + 1) (i : Fin 5) : profile (H j i) = profile (A j i) :=
    lowerHistory_profile c hcore hbuffer C base hj i
  have hO := previousOmega_congr h (fun j hj => hH j hj 1) (fun j hj => hH j hj 4)
  have hS := PositiveAxisSystem.actualLowerSource_congr h
    (AxisSourceRegularity.previousOmegaDivX h (fun j => profile (A j 1)) (fun j => profile (A j 4))
      (m + 1))
    (fun j hj => hH j hj 0) (fun j hj => hH j hj 1) (fun j hj => hH j hj 4) (X, eta)
  have hB : PositiveAxisSystem.baseAtOrderZero
      (fun j => PositiveAxisSystem.actualJet (profile (H j 0)) (X, eta))
      (fun j => PositiveAxisSystem.actualJet (profile (H j 1)) (X, eta))
      (fun j => profile (H j 4) (X, eta)) =
      PositiveAxisSystem.baseAtOrderZero
      (fun j => PositiveAxisSystem.actualJet (profile (A j 0)) (X, eta))
      (fun j => PositiveAxisSystem.actualJet (profile (A j 1)) (X, eta))
      (fun j => profile (A j 4) (X, eta)) := by
    simp only [PositiveAxisSystem.baseAtOrderZero, hH 0 (Nat.zero_lt_succ m)]
  have hout := step_expanded (radiusDomain c hcore hbuffer m)
    (radius_pos hcore hbuffer (m + 1)) (radius_succ_lt hbuffer m) C (m + 1) H
    ⟨hX.1, core_square_lt hcore hbuffer hX.2 (m + 1)⟩ heta
  rw [hO, hS, hB] at hout
  simpa only [A, H, ← sequence_succ_profile] using hout

/-- Every positive slow coefficient solves the actual finite convolution
equations, with the lower radial residual computed from the same hierarchy. -/
theorem sequence_positive_order {core buffer : ℝ} {U : Set ℂ} {h : ℝ}
    (c : Domain (radius core buffer 0) U h) (hcore : 0 < core) (hbuffer : 0 < buffer)
    (C : ℝ) (base : Coefficient (radius core buffer 0) U) {n : ℕ} (hn : 0 < n)
    {X eta : ℝ} (hX : X ∈ Ioo (0 : ℝ) (core ^ 2)) (heta : (eta : ℂ) ∈ U) :
    let A := sequence c hcore hbuffer C base
    PositiveAxisSystem.PositiveOrderEquations h C eta X n
      (fun j => PositiveAxisSystem.actualJet (profile (A j 0)) (X, eta))
      (fun j => PositiveAxisSystem.actualJet (profile (A j 1)) (X, eta))
      (fun j => profile (A j 4) (X, eta))
      (PositiveAxisSystem.actualJet (profile (A n 2)) (X, eta))
      (PositiveAxisSystem.actualJet (profile (A n 3)) (X, eta))
      (PositiveAxisSystem.precedingDiffusion h (PositiveAxisSystem.angularPower h) (fun j =>
        profile (A j 0)) n (X, eta))
      (PositiveAxisSystem.precedingDiffusion h (PositiveAxisSystem.axialPower h) (fun j => profile
        (A j 1)) n (X, eta))
      (AxisSourceRegularity.previousOmegaDivX h (fun j => profile (A j 1)) (fun j => profile (A j
        4)) n (X, eta)) := by
  apply (PositiveAxisSystem.expanded_iff_positiveOrder h C eta X hn _ _ _ _ _ _ _ _
    (sequence_beta c hcore hbuffer C base hn hX heta)).mp
  exact sequence_expanded c hcore hbuffer C base hn hX heta

theorem sequence_axis_zero {core buffer : ℝ} {U : Set ℂ} {h : ℝ}
    (c : Domain (radius core buffer 0) U h) (hcore : 0 < core) (hbuffer : 0 < buffer)
    (C : ℝ) (base : Coefficient (radius core buffer 0) U) {n : ℕ} (hn : 0 < n)
    (i : Fin 5) {z : ℂ} (hz : z ∈ U) : sequence c hcore hbuffer C base n i (0, z) = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  change hierarchy c hcore hbuffer C base (m + 1) i (0, z) = 0
  rw [hierarchy_succ]
  exact step_axis_zero _ _ _ _ _ _ _ hz

theorem domain_real_denominator {R : ℝ} {U : Set ℂ} {h : ℝ} (c : Domain R U h)
    {eta : ℝ} (heta : (eta : ℂ) ∈ U) : SimilarityProfile.L h eta ≠ 0 := by
  have he : ((SimilarityProfile.L h eta : ℝ) : ℂ) = PositiveAxisSystem.ell (h : ℂ) (eta : ℂ) := by
    simp [SimilarityProfile.L, CoordinateAlgebra.L, PositiveAxisSystem.ell]
  intro hh
  apply c.denominator (eta : ℂ) heta
  rw [← he, hh, Complex.ofReal_zero]

/-- The supplied regular representative really is the original radial
residual divided by X, for every previously constructed order. -/
theorem sequence_omega_quotient {core buffer : ℝ} {U : Set ℂ} {h : ℝ}
    (c : Domain (radius core buffer 0) U h) (hcore : 0 < core) (hbuffer : 0 < buffer)
    (C : ℝ) (base : Coefficient (radius core buffer 0) U) (k : ℕ)
    {X eta : ℝ} (hX : X ∈ Ioo (0 : ℝ) (core ^ 2)) (heta : (eta : ℂ) ∈ U) :
    let A := sequence c hcore hbuffer C base
    AxisSourceRegularity.omega h (fun j => profile (A j 1))
        (fun j => AxisSourceRegularity.axisFactor (profile (A j 4))) k (X, eta) / X =
      AxisSourceRegularity.previousOmegaDivX h (fun j => profile (A j 1))
        (fun j => profile (A j 4)) (k + 1) (X, eta) := by
  apply AxisSourceRegularity.omega_quotient_eq
  · intro j _
    exact (profile_contDiffAt hcore c.open_set _ hX heta).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  · exact domain_real_denominator c heta
  · exact hX.1.ne'

theorem average_from_equation {R : ℝ} (hR : 0 < R) {U : Set ℂ} (hU : IsOpen U)
    (u k : AxisFunction R U) {eta X : ℝ} (heta : (eta : ℂ) ∈ U)
    (hX : X ∈ Ioo (0 : ℝ) (R ^ 2))
    (heq : ∀ Y ∈ Ioo (0 : ℝ) (R ^ 2),
      Y * (SimilarityProfile.partialX (profile u) (Y, eta) +
        SimilarityProfile.partialX (profile k) (Y, eta)) + profile k (Y, eta) = 0) :
    ProfileHistories.average (profile u) (X, eta) = profile u (X, eta) + profile k (X, eta) := by
  have hc (F : AxisFunction R U) : ContinuousOn (fun Y => profile F (Y, eta)) (Icc (0 : ℝ) X) :=
    (profile_smooth hR hU F).continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun Y hY => ⟨⟨hY.1, lt_of_le_of_lt hY.2 hX.2⟩, heta⟩)
  have hd (F : AxisFunction R U) (Y : ℝ) (hY : Y ∈ Ioo (0 : ℝ) X) :
      HasDerivAt (fun Z => profile F (Z, eta)) (SimilarityProfile.partialX (profile F) (Y, eta)) Y
        := by
    exact ((profile_contDiffAt hR hU F ⟨hY.1, lt_trans hY.2 hX.2⟩ heta).differentiableAt
      (by simp)).hasFDerivAt.comp_hasDerivAt Y ((hasDerivAt_id Y).prodMk (hasDerivAt_const Y eta))
  have hi : IntervalIntegrable (fun Y => profile u (Y, eta)) MeasureTheory.volume 0 X := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le hX.1.le] using hc u
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hX.1.le
    (continuousOn_id.fun_mul ((hc u).fun_add (hc k)))
    (fun Y hY => show HasDerivAt (fun Z => Z * (profile u (Z, eta) + profile k (Z, eta)))
      (profile u (Y, eta)) Y from by
      convert! (hasDerivAt_id Y).fun_mul ((hd u Y hY).fun_add (hd k Y hY)) using 1
      have hh := heq Y ⟨hY.1, lt_trans hY.2 hX.2⟩
      simp only [id_eq, one_mul]
      linarith) hi
  have hmean : X * ProfileHistories.average (profile u) (X, eta) =
      ∫ Y in (0 : ℝ)..X, profile u (Y, eta) := by
    change X • (∫ t in (0 : ℝ)..1, profile u (t * X, eta)) = _
    rw [intervalIntegral.smul_integral_comp_mul_right (f := fun Y => profile u (Y, eta)), zero_mul,
      one_mul]
  rw [he] at hmean
  simp only [id_eq, zero_mul, sub_zero] at hmean
  exact (mul_left_cancel₀ hX.1.ne' hmean)

/-- The stored average defect is the literal integral average, including
the axis. No free integration constant survives the regular zero trace. -/
theorem sequence_average {core buffer : ℝ} {U : Set ℂ} {h : ℝ}
    (c : Domain (radius core buffer 0) U h) (hcore : 0 < core) (hbuffer : 0 < buffer)
    (C : ℝ) (base : Coefficient (radius core buffer 0) U) {n : ℕ} (hn : 0 < n)
    {X eta : ℝ} (hX : X ∈ Ico (0 : ℝ) (core ^ 2)) (heta : (eta : ℂ) ∈ U) :
    let A := sequence c hcore hbuffer C base
    ProfileHistories.average (profile (A n 1)) (X, eta) =
      profile (A n 1) (X, eta) + profile (A n 2) (X, eta) := by
  by_cases hz : X = 0
  · subst X
    have hk : profile (sequence c hcore hbuffer C base n 2) (0, eta) = 0 := by
      change (sequence c hcore hbuffer C base n 2 (Real.sqrt 0, (eta : ℂ))).re = 0
      rw [Real.sqrt_zero, sequence_axis_zero c hcore hbuffer C base hn 2 heta]
      rfl
    simp [ProfileHistories.average, hk]
  · exact average_from_equation hcore c.open_set _ _ heta ⟨lt_of_le_of_ne hX.1 (Ne.symm hz), hX.2⟩
      (fun Y hY => (sequence_positive_order c hcore hbuffer C base hn hY heta).1)

theorem profile_axis_jet {R : ℝ} (hR : 0 < R) {U : Set ℂ} (F : AxisFunction R U)
    {eta : ℝ} (heta : (eta : ℂ) ∈ U) (k : ℕ) :
    iteratedDerivWithin k (fun X => profile F (X, eta)) (Ici 0) 0 =
      ((k.factorial : ℝ) / ((2 * k).factorial : ℝ)) •
        iteratedDeriv (2 * k) (fun r => (F (r, (eta : ℂ))).re) 0 := by
  apply EvenSmoothDescent.iteratedDerivWithin_descent_zero_local
    (f := fun r => (F (r, (eta : ℂ))).re) hR
  · exact Complex.reCLM.contDiff.comp_contDiffOn
      (F.2.smooth.comp (contDiff_id.prodMk contDiff_const).contDiffOn (fun r hr => ⟨hr, heta⟩))
  · exact fun r hr => congrArg Complex.re (F.2.even _ heta r hr)

/-- A base made from four genuine profiles; its divergence coefficient is
computed by the same canonical derivative operator used in the recursion. -/
noncomputable def makeBase {R : ℝ} {U : Set ℂ} {h : ℝ} (c : Domain R U h)
    (phi u average pressure : AxisFunction R U) : Coefficient R U :=
  ![phi, u, average - u, pressure, betaOperator c 0 u (average - u)]

theorem sequence_smooth {core buffer : ℝ} {U : Set ℂ} {h : ℝ}
    (c : Domain (radius core buffer 0) U h) (hcore : 0 < core) (hbuffer : 0 < buffer)
    (C : ℝ) (base : Coefficient (radius core buffer 0) U) (n : ℕ) (i : Fin 5) :
    ContDiffOn ℝ ∞ (profile (sequence c hcore hbuffer C base n i))
      (Ico (0 : ℝ) (core ^ 2) ×ˢ PositiveAxisExistence.realParameterDomain U) :=
  profile_smooth hcore c.open_set _

theorem sequence_mixed_pullback_smooth {core buffer : ℝ} {U : Set ℂ} {h : ℝ}
    (c : Domain (radius core buffer 0) U h) (hcore : 0 < core) (hbuffer : 0 < buffer)
    (C : ℝ) (base : Coefficient (radius core buffer 0) U) (n : ℕ) (i : Fin 5) (k m : ℕ) :
    ContDiffOn ℝ ∞
      (fun p : ℝ × ℂ => BoundaryAxisJets.mixedAxisJet (sequence c hcore hbuffer C base n i) k m
        (p.1 ^ 2, p.2))
      (Ioo (-core) core ×ˢ U) :=
  BoundaryAxisJets.mixedAxisJet_pullback_contDiffOn_full hcore c.open_set
    (sequence c hcore hbuffer C base n i).2.smooth
    (sequence c hcore hbuffer C base n i).2.holomorphic
    (sequence c hcore hbuffer C base n i).2.even k m

theorem sequence_mixed_pullback_holomorphic {core buffer : ℝ} {U : Set ℂ} {h : ℝ}
    (c : Domain (radius core buffer 0) U h) (hcore : 0 < core) (hbuffer : 0 < buffer)
    (C : ℝ) (base : Coefficient (radius core buffer 0) U) (n : ℕ) (i : Fin 5) (k m : ℕ)
    {r : ℝ} (hr : r ∈ Ioo (-core) core) :
    DifferentiableOn ℂ
      (fun z => BoundaryAxisJets.mixedAxisJet (sequence c hcore hbuffer C base n i) k m (r ^ 2, z))
        U :=
  BoundaryAxisJets.mixedAxisJet_pullback_holomorphic_full hcore c.open_set
    (sequence c hcore hbuffer C base n i).2.smooth
    (sequence c hcore hbuffer C base n i).2.holomorphic
    (sequence c hcore hbuffer C base n i).2.even k m hr

/-- The concrete finite equations of an actual sequence of profile functions. -/
def OrderEquations {R : ℝ} {U : Set ℂ} (h C : ℝ) (A : ℕ → Coefficient R U)
    (n : ℕ) (w : SimilarityProfile.InnerPoint) : Prop :=
  PositiveAxisSystem.PositiveOrderEquations h C w.2 w.1 n
    (fun j => PositiveAxisSystem.actualJet (profile (A j 0)) w)
    (fun j => PositiveAxisSystem.actualJet (profile (A j 1)) w)
    (fun j => profile (A j 4) w)
    (PositiveAxisSystem.actualJet (profile (A n 2)) w)
    (PositiveAxisSystem.actualJet (profile (A n 3)) w)
    (PositiveAxisSystem.precedingDiffusion h (PositiveAxisSystem.angularPower h) (fun j => profile
      (A j 0)) n w)
    (PositiveAxisSystem.precedingDiffusion h (PositiveAxisSystem.axialPower h) (fun j => profile (A
      j 1)) n w)
    (AxisSourceRegularity.previousOmegaDivX h (fun j => profile (A j 1)) (fun j => profile (A j 4))
      n w)

/-- A local slow hierarchy is the output, not a hypothesis on the data.
Its underlying type supplies genuine compatible smooth coefficient functions. -/
structure LocalHierarchy (R : ℝ) (U : Set ℂ) (h C : ℝ)
    (base : Fin 5 → SimilarityProfile.InnerProfile) where
  coefficients : ℕ → Coefficient R U
  starts : ∀ i, profile (coefficients 0 i) = base i
  zero_axis : ∀ n, 0 < n → ∀ i : Fin 5, ∀ z ∈ U, coefficients n i (0, z) = 0
  beta : ∀ n, 0 < n → ∀ X ∈ Ioo (0 : ℝ) (R ^ 2), ∀ eta : ℝ, (eta : ℂ) ∈ U →
    profile (coefficients n 4) (X, eta) = PositiveAxisExistence.newBeta h n
      (profile (coefficients n 1)) (profile (coefficients n 2)) (X, eta)
  equations : ∀ n, 0 < n → ∀ X ∈ Ioo (0 : ℝ) (R ^ 2), ∀ eta : ℝ, (eta : ℂ) ∈ U →
    OrderEquations h C coefficients n (X, eta)
  average : ∀ n, 0 < n → ∀ X ∈ Ico (0 : ℝ) (R ^ 2), ∀ eta : ℝ, (eta : ℂ) ∈ U →
    ProfileHistories.average (profile (coefficients n 1)) (X, eta) =
      profile (coefficients n 1) (X, eta) + profile (coefficients n 2) (X, eta)

/-- Construct every positive slow order from a single finite base profile.
The entire sequence uses one fixed radial core and one fixed parameter domain. -/
noncomputable def buildLocalHierarchy {core buffer : ℝ} {U : Set ℂ} {h : ℝ}
    (c : Domain (radius core buffer 0) U h) (hcore : 0 < core) (hbuffer : 0 < buffer)
    (C : ℝ) (base : Coefficient (radius core buffer 0) U) :
    LocalHierarchy core U h C (fun i => profile (base i)) where
  coefficients := sequence c hcore hbuffer C base
  starts := sequence_zero c hcore hbuffer C base
  zero_axis := fun _ hn i _ hz => sequence_axis_zero c hcore hbuffer C base hn i hz
  beta := fun _ hn _ hX _ heta => sequence_beta c hcore hbuffer C base hn hX heta
  equations := fun _ hn _ hX _ heta => sequence_positive_order c hcore hbuffer C base hn hX heta
  average := fun _ hn _ hX _ heta => sequence_average c hcore hbuffer C base hn hX heta

theorem exists_local_slow_hierarchy {core buffer : ℝ} {U : Set ℂ} {h : ℝ}
    (c : Domain (radius core buffer 0) U h) (hcore : 0 < core) (hbuffer : 0 < buffer)
    (C : ℝ) (base : Coefficient (radius core buffer 0) U) :
    Nonempty (LocalHierarchy core U h C (fun i => profile (base i))) :=
  ⟨buildLocalHierarchy c hcore hbuffer C base⟩

theorem LocalHierarchy.profiles_smooth {R : ℝ} {U : Set ℂ} {h C : ℝ}
    {base : Fin 5 → SimilarityProfile.InnerProfile} (A : LocalHierarchy R U h C base)
    (hR : 0 < R) (hU : IsOpen U) (n : ℕ) (i : Fin 5) :
    ContDiffOn ℝ ∞ (profile (A.coefficients n i))
      (Ico (0 : ℝ) (R ^ 2) ×ˢ PositiveAxisExistence.realParameterDomain U) :=
  profile_smooth hR hU _

/-- Any fixed real parameter window contained in the input neighborhood is
retained at every slow order; the recursion consumes no further strip width. -/
theorem LocalHierarchy.equations_on_window {R : ℝ} {U : Set ℂ} {h C a b : ℝ}
    {base : Fin 5 → SimilarityProfile.InnerProfile} (A : LocalHierarchy R U h C base)
    (hwindow : ∀ eta ∈ Icc a b, (eta : ℂ) ∈ U)
    {n : ℕ} (hn : 0 < n) {X eta : ℝ} (hX : X ∈ Ioo (0 : ℝ) (R ^ 2))
    (heta : eta ∈ Icc a b) : OrderEquations h C A.coefficients n (X, eta) :=
  A.equations n hn X hX eta (hwindow eta heta)

end NavierStokes.SlowRecursion
