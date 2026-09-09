/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.MatchingDebtBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.HeatSwitchCone

@[expose] public section

/-!
# The actual restore and five-row repair interval

The interval has fixed logarithmic coordinates `[-8,-5]`.  Endpoint drift
and the actual repair coefficients are the only perturbation parameters.
All histories are recovered from the exact five-row match at the right end.
-/

noncomputable section

open Set Filter Function MeasureTheory
open scoped Topology ContDiff BigOperators
open NavierStokes.OutgoingProfile (Profile)

namespace NavierStokes.RepairConeBounds

abbrev Point := ℝ × ℝ
abbrev Coeff := FiveProfileMoments.Coeff
abbrev Parameter := ℝ × Coeff
abbrev Control := Parameter × Parameter
abbrev Raw := Parameter × Point

noncomputable def window : Set Point := Icc (-8) (-5) ×ˢ Icc (-1) 1

noncomputable def freeU (F : Profile) (z : Raw) : ℝ :=
  4 * z.2.2 + (1 - OutgoingSchedule.sigma (z.2.1 + 8)) * z.1.1 +
    NominalProfile.idealAmplitude F z.2.2 *
      FiveProfileMoments.u NominalProfile.resetPatch z.1.2 (Real.exp z.2.1)

noncomputable def freeE (F : Profile) (z : Raw) : ℝ :=
  NominalProfile.idealAmplitude F z.2.2 * (Real.exp (z.2.1 / 10) +
    FiveProfileMoments.e NominalProfile.resetPatch z.1.2 (Real.exp z.2.1))

theorem freeU_contDiff (F : Profile) : ContDiff ℝ ∞ (freeU F) := by
  have hb : ContDiff ℝ ∞ (fun z : Raw =>
      FiveProfileMoments.u NominalProfile.resetPatch z.1.2 (Real.exp z.2.1)) := by
    unfold FiveProfileMoments.u FiveProfileMoments.correction
    apply ContDiff.sum
    intro i _
    exact ((contDiff_apply ℝ ℝ i).comp contDiff_fst.snd.fst).mul
      ((FiveProfileMoments.bump_contDiff NominalProfile.resetPatch.leftHalf i).comp
        contDiff_snd.fst.exp)
  exact ((contDiff_const.mul contDiff_snd.snd).add
    ((contDiff_const.sub (OutgoingSchedule.sigma_contDiff.comp
      (contDiff_snd.fst.add contDiff_const))).mul contDiff_fst.fst)).add
    (((NominalProfile.idealAmplitude_smooth F).comp contDiff_snd.snd).mul hb)

theorem freeE_contDiff (F : Profile) : ContDiff ℝ ∞ (freeE F) := by
  have hb : ContDiff ℝ ∞ (fun z : Raw =>
      FiveProfileMoments.e NominalProfile.resetPatch z.1.2 (Real.exp z.2.1)) := by
    unfold FiveProfileMoments.e FiveProfileMoments.correction
    apply ContDiff.sum
    intro i _
    exact ((contDiff_apply ℝ ℝ i).comp contDiff_fst.snd.snd).mul
      ((FiveProfileMoments.bump_contDiff NominalProfile.resetPatch.rightHalf i).comp
        contDiff_snd.fst.exp)
  exact ((NominalProfile.idealAmplitude_smooth F).comp contDiff_snd.snd).mul
    ((contDiff_snd.fst.div_const 10).exp.add hb)

@[simp] theorem freeU_zero (F : Profile) (p : Point) : freeU F (0, p) = 4 * p.2 := by
  simp [freeU, FiveProfileMoments.u, FiveProfileMoments.correction]

@[simp] theorem freeE_zero (F : Profile) (p : Point) :
    freeE F (0, p) = NominalProfile.idealAmplitude F p.2 * Real.exp (p.1 / 10) := by
  simp [freeE, FiveProfileMoments.e, FiveProfileMoments.correction]

theorem freeU_zero_clean (F : Profile) {p : Point} (hp : p.1 ≤ 0) :
    freeU F (0, p) = F.logU p := by
  rw [freeU_zero]
  exact (OutgoingHistories.U_ideal F.data F.amp p.2 hp).symm

theorem freeE_zero_clean (F : Profile) {p : Point} (hp : p.1 ≤ 0) :
    freeE F (0, p) = F.logE p := by
  rw [freeE_zero]
  exact (OutgoingHistories.E_ideal F.reset p.2 hp).symm

noncomputable def rawPoint (z : Control × Point) : Raw := (z.1.1, z.2)
noncomputable def value (f : Raw → ℝ) (z : Control × Point) : ℝ := f (rawPoint z)
noncomputable def radialJet (f : Raw → ℝ) (z : Control × Point) : ℝ :=
  fderiv ℝ f (rawPoint z) (0, (1, 0))
noncomputable def parameterJet (f : Raw → ℝ) (z : Control × Point) : ℝ :=
  fderiv ℝ f (rawPoint z) (z.1.2, (0, 1))

theorem rawPoint_contDiff : ContDiff ℝ ∞ rawPoint := contDiff_fst.fst.prodMk contDiff_snd
theorem value_contDiff {f : Raw → ℝ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (value f) :=
  hf.comp rawPoint_contDiff
theorem radialJet_contDiff {f : Raw → ℝ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (radialJet f) :=
  ((hf.fderiv_right (m := ∞) (by simp)).comp rawPoint_contDiff).clm_apply contDiff_const
theorem parameterJet_contDiff {f : Raw → ℝ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (parameterJet f) :=
  ((hf.fderiv_right (m := ∞) (by simp)).comp rawPoint_contDiff).clm_apply
    (contDiff_fst.snd.prodMk contDiff_const)

noncomputable def finitePrefix (f : Raw → ℝ) (z : Raw) : ℝ :=
  ∫ t in (-5 : ℝ)..z.2.1, f (z.1, (t, z.2.2))

theorem finitePrefix_contDiff {f : Raw → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (finitePrefix f) := by
  have hm : ContDiff ℝ ∞ (fun z : (Parameter × ℝ) × ℝ => (z.1.1, (z.2, z.1.2)) :
      ((Parameter × ℝ) × ℝ) → Raw) :=
    contDiff_fst.fst.prodMk (contDiff_snd.prodMk contDiff_fst.snd)
  have hg := hf.comp hm
  have hi := HeatedOutgoing.anchoredPrimitive_contDiff
    (P := Parameter × ℝ) (fun z => f (z.1.1, (z.2, z.1.2))) hg (-5)
  have hp : ContDiff ℝ ∞ (fun z : Raw => ((z.1, z.2.2), z.2.1)) :=
    (contDiff_fst.prodMk contDiff_snd.snd).prodMk contDiff_snd.fst
  have hh := hi.comp hp
  exact hh

noncomputable def freeM (F : Profile) (z : Raw) : ℝ :=
  OutgoingHistories.M F.data F.amp z.2 + finitePrefix
    (fun q => Real.exp q.2.1 * (freeU F q - F.logU q.2)) z
noncomputable def freeI (F : Profile) (z : Raw) : ℝ :=
  OutgoingHistories.I F.reset z.2 + finitePrefix
    (fun q => Real.exp (3 * q.2.1 / 2) * (freeE F q - F.logE q.2)) z
noncomputable def freeJ (F : Profile) (z : Raw) : ℝ :=
  OutgoingHistories.J F.reset F.amp z.2 + finitePrefix
    (fun q => Real.exp (3 * q.2.1 / 2) *
      (freeE F q * freeU F q - F.logE q.2 * F.logU q.2)) z
noncomputable def freeS (F : Profile) (z : Raw) : ℝ :=
  OutgoingHistories.S F.reset F.amp z.2 + finitePrefix
    (fun q => Real.exp q.2.1 *
      ((freeU F q ^ 2 - freeE F q ^ 2 / 2) - (F.logU q.2 ^ 2 - F.logE q.2 ^ 2 / 2))) z
noncomputable def freePi (F : Profile) (z : Raw) : ℝ :=
  OutgoingHistories.Pi F.reset z.2 + (1 / 2 : ℝ) * finitePrefix
    (fun q => freeE F q ^ 2 - F.logE q.2 ^ 2) z

theorem freeM_contDiff (F : Profile) : ContDiff ℝ ∞ (freeM F) :=
  ((OutgoingHistories.M_smooth F.data F.amp_contDiff).comp contDiff_snd).add
    (finitePrefix_contDiff (contDiff_snd.fst.exp.mul
      ((freeU_contDiff F).sub (F.logU_contDiff.comp contDiff_snd))))
theorem freeI_contDiff (F : Profile) : ContDiff ℝ ∞ (freeI F) :=
  ((OutgoingHistories.I_smooth F.reset).comp contDiff_snd).add
    (finitePrefix_contDiff (((contDiff_const.mul contDiff_snd.fst).div_const 2).exp.mul
      ((freeE_contDiff F).sub (F.logE_contDiff.comp contDiff_snd))))
theorem freeJ_contDiff (F : Profile) : ContDiff ℝ ∞ (freeJ F) :=
  ((OutgoingHistories.J_smooth F.reset F.amp_contDiff).comp contDiff_snd).add
    (finitePrefix_contDiff (((contDiff_const.mul contDiff_snd.fst).div_const 2).exp.mul
      (((freeE_contDiff F).mul (freeU_contDiff F)).sub
        ((F.logE_contDiff.comp contDiff_snd).mul (F.logU_contDiff.comp contDiff_snd)))))
theorem freeS_contDiff (F : Profile) : ContDiff ℝ ∞ (freeS F) :=
  ((OutgoingHistories.S_smooth F.reset F.amp_contDiff).comp contDiff_snd).add
    (finitePrefix_contDiff (contDiff_snd.fst.exp.mul
      ((((freeU_contDiff F).pow 2).sub (((freeE_contDiff F).pow 2).div_const 2)).sub
        (((F.logU_contDiff.comp contDiff_snd).pow 2).sub
          (((F.logE_contDiff.comp contDiff_snd).pow 2).div_const 2)))))
theorem freePi_contDiff (F : Profile) : ContDiff ℝ ∞ (freePi F) :=
  ((OutgoingHistories.Pi_smooth F.reset).comp contDiff_snd).add
    (contDiff_const.mul (finitePrefix_contDiff
      (((freeE_contDiff F).pow 2).sub ((F.logE_contDiff.comp contDiff_snd).pow 2))))

theorem finitePrefix_zero {f : Raw → ℝ} {p : Point} (hp : p.1 ≤ 0)
    (hf : ∀ y ≤ 0, f (0, (y, p.2)) = 0) : finitePrefix f (0, p) = 0 := by
  change (∫ t in (-5 : ℝ)..p.1, f (0, (t, p.2))) = 0
  have he : (∫ t in (-5 : ℝ)..p.1, f (0, (t, p.2))) = ∫ t in (-5 : ℝ)..p.1, (0 : ℝ) := by
    apply intervalIntegral.integral_congr
    intro t ht
    exact hf t (ht.2.trans (max_le (by norm_num) hp))
  rw [he, intervalIntegral.integral_zero]

theorem freeM_zero (F : Profile) {p : Point} (hp : p.1 ≤ 0) :
    freeM F (0, p) = OutgoingHistories.M F.data F.amp p := by
  unfold freeM
  rw [finitePrefix_zero hp]
  · simp
  · intro y hy
    simp only [freeU_zero_clean F (p := (y, p.2)) hy, sub_self, mul_zero]

theorem freeI_zero (F : Profile) {p : Point} (hp : p.1 ≤ 0) :
    freeI F (0, p) = OutgoingHistories.I F.reset p := by
  unfold freeI
  rw [finitePrefix_zero hp]
  · simp
  · intro y hy
    simp only [freeE_zero_clean F (p := (y, p.2)) hy, sub_self, mul_zero]

theorem freeJ_zero (F : Profile) {p : Point} (hp : p.1 ≤ 0) :
    freeJ F (0, p) = OutgoingHistories.J F.reset F.amp p := by
  unfold freeJ
  rw [finitePrefix_zero hp]
  · simp
  · intro y hy
    simp only [freeE_zero_clean F (p := (y, p.2)) hy,
      freeU_zero_clean F (p := (y, p.2)) hy, sub_self, mul_zero]

theorem freeS_zero (F : Profile) {p : Point} (hp : p.1 ≤ 0) :
    freeS F (0, p) = OutgoingHistories.S F.reset F.amp p := by
  unfold freeS
  rw [finitePrefix_zero hp]
  · simp
  · intro y hy
    simp only [freeE_zero_clean F (p := (y, p.2)) hy,
      freeU_zero_clean F (p := (y, p.2)) hy, sub_self, mul_zero]

theorem freePi_zero (F : Profile) {p : Point} (hp : p.1 ≤ 0) :
    freePi F (0, p) = OutgoingHistories.Pi F.reset p := by
  unfold freePi
  rw [finitePrefix_zero hp]
  · simp
  · intro y hy
    simp only [freeE_zero_clean F (p := (y, p.2)) hy, sub_self]

theorem radialJet_hasDerivAt {f : Raw → ℝ} (hf : ContDiff ℝ ∞ f)
    (v : Control) (p : Point) :
    HasDerivAt (fun y => value f (v, (y, p.2))) (radialJet f (v, p)) p.1 := by
  have hg : HasDerivAt (fun y => (v.1, (y, p.2)) : ℝ → Raw) (0, (1, 0)) p.1 :=
    (hasDerivAt_const _ _).prodMk ((hasDerivAt_id _).prodMk (hasDerivAt_const _ _))
  exact (hf.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt _ hg

theorem parameterJet_hasDerivAt {f : Raw → ℝ} (hf : ContDiff ℝ ∞ f)
    {g : ℝ → Parameter} {g' : Parameter} {eta : ℝ} (hg : HasDerivAt g g' eta) (y : ℝ) :
    HasDerivAt (fun e => f (g e, (y, e))) (parameterJet f ((g eta, g'), (y, eta))) eta := by
  have hc : HasDerivAt (fun e => (g e, (y, e)) : ℝ → Raw) (g', (0, 1)) eta :=
    hg.prodMk ((hasDerivAt_const _ _).prodMk (hasDerivAt_id _))
  exact (hf.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt _ hc

theorem parameterJet_zero {f : Raw → ℝ} {g : Point → ℝ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) {p : Point} (he : ∀ eta, f (0, (p.1, eta)) = g (p.1, eta)) :
    parameterJet f (0, p) = OutgoingHistories.dEta g p := by
  have hd := parameterJet_hasDerivAt hf (hasDerivAt_const p.2 (0 : Parameter)) p.1
  have hfun : (fun eta => f (0, (p.1, eta))) = (fun eta => g (p.1, eta)) := funext he
  rw [hfun] at hd
  exact hd.unique (OutgoingHistories.dEta_hasDerivAt hg p)

theorem radialJet_freeU_zero (F : Profile) (p : Point) : radialJet (freeU F) (0, p) = 0 := by
  have hd := radialJet_hasDerivAt (freeU_contDiff F) (0 : Control) p
  have he : (fun y => value (freeU F) (0, (y, p.2))) = (fun _ => 4 * p.2) := by
    funext y
    exact freeU_zero F _
  rw [he] at hd
  exact hd.unique (hasDerivAt_const _ _)

theorem radialJet_freeE_zero (F : Profile) (p : Point) :
    radialJet (freeE F) (0, p) = value (freeE F) (0, p) / 10 := by
  have hd := radialJet_hasDerivAt (freeE_contDiff F) (0 : Control) p
  have he : (fun y => value (freeE F) (0, (y, p.2))) =
      (fun y => NominalProfile.idealAmplitude F p.2 * Real.exp (y / 10)) := by
    funext y
    exact freeE_zero F _
  rw [he] at hd
  have hh := hd.unique ((((hasDerivAt_id p.1).div_const 10).exp).const_mul
    (NominalProfile.idealAmplitude F p.2))
  change _ = freeE F (0, p) / 10
  rw [freeE_zero, hh]
  simp only [id_eq]
  ring

noncomputable def endpointError {F : Profile} {A : NominalProfile.AxisStage F}
    (c : NominalProfile.Controls A) (eta : ℝ) : ℝ := c.initialAxial eta - 4 * eta
noncomputable def dataParameter {F : Profile} {A : NominalProfile.AxisStage F}
    (c : NominalProfile.Controls A) (eta : ℝ) : Parameter :=
  (endpointError c eta, NominalProfile.resetCoefficients F c.debt eta)
noncomputable def controls {F : Profile} {A : NominalProfile.AxisStage F}
    (c : NominalProfile.Controls A) (eta : ℝ) : Control :=
  (dataParameter c eta,
    (deriv (endpointError c) eta, deriv (NominalProfile.resetCoefficients F c.debt) eta))

theorem dataParameter_hasDerivAt {F : Profile} {A : NominalProfile.AxisStage F}
    (c : NominalProfile.Controls A) {eta : ℝ} (heta : eta ∈ ReferencePath.parameterInterval)
    (hs : NominalProfile.SmallDebt F c.debt eta) :
    HasDerivAt (dataParameter c) (controls c eta).2 eta := by
  have he : ContDiffAt ℝ ∞ (endpointError c) eta :=
    (c.initialAxial_smooth.contDiffAt (ReferencePath.parameterInterval_open.mem_nhds heta)).sub
      (contDiff_const.mul contDiff_id).contDiffAt
  exact (he.differentiableAt (by simp)).hasDerivAt.prodMk
    ((c.coefficients_smoothAt heta hs).differentiableAt (by simp)).hasDerivAt

theorem controls_norm {F : Profile} {A : NominalProfile.AxisStage F}
    (c : NominalProfile.Controls A) {eps : ℝ}
    (hG : JetBounds.FiniteJetBound 1 (endpointError c) (Icc (-1) 1) eps)
    (hc : JetBounds.FiniteJetBound 1 (NominalProfile.resetCoefficients F c.debt) (Icc (-1) 1) eps)
    {eta : ℝ} (heta : eta ∈ Icc (-1) 1) : ‖controls c eta‖ ≤ eps := by
  have hdG := hG 1 le_rfl eta heta
  have hdc := hc 1 le_rfl eta heta
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_one] at hdG hdc
  simp only [controls, dataParameter, Prod.norm_mk]
  exact max_le (max_le (hG.norm_le heta) (hc.norm_le heta)) (max_le hdG hdc)

theorem actual_fields {F : Profile} {A : NominalProfile.AxisStage F}
    (c : NominalProfile.Controls A) (hsep : c.separation ≤ Real.exp (-8))
    {p : Point} (hy : p.1 ∈ Icc (-8) (-5)) (heta : p.2 ∈ ReferencePath.parameterInterval) :
    c.normalizedU (Real.exp p.1, p.2) = freeU F (dataParameter c p.2, p) ∧
    c.normalizedE (Real.exp p.1, p.2) = freeE F (dataParameter c p.2, p) := by
  have hx : c.separation ≤ Real.exp p.1 := hsep.trans (Real.exp_le_exp.mpr hy.1)
  have hxb : Real.exp p.1 ≤ NominalProfile.matchFraction := Real.exp_le_exp.mpr hy.2
  have hb := c.base_restore_segment hx hxb heta
  constructor
  · change NominalProfile.baseU F A.normalization c.seedU (Real.exp p.1, p.2) + _ = _
    rw [hb.1]
    simp only [ShapeTransition.restore, Real.log_exp, freeU, dataParameter, endpointError,
      NominalProfile.Controls.debt]
    ring
  · change NominalProfile.baseE F A.normalization c.shapeTime c.initialShape c.seedF (Real.exp p.1,
    p.2) + _ = _
    rw [hb.2]
    simp only [NominalProfile.idealE, Real.rpow_def_of_pos (Real.exp_pos p.1), Real.log_exp,
      freeE, dataParameter, NominalProfile.Controls.debt]
    rw [show p.1 * (1 / 10 : ℝ) = p.1 / 10 by ring]
    ring

theorem integral_exp_Iic (f : ℝ → ℝ) (y : ℝ) :
    (∫ x in Ioc 0 (Real.exp y), f x) = ∫ t in Iic y, Real.exp t * f (Real.exp t) := by
  rw [← ReleaseMoments.image_exp_Iic,
    integral_image_eq_integral_abs_deriv_smul measurableSet_Iic
      (fun t _ => (Real.hasDerivAt_exp t).hasDerivWithinAt) Real.exp_injective.injOn]
  simp only [abs_of_pos (Real.exp_pos _), smul_eq_mul]

theorem image_exp_Ioc (a b : ℝ) :
    Real.exp '' Ioc a b = Ioc (Real.exp a) (Real.exp b) := by
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨Real.exp_lt_exp.mpr ht.1, Real.exp_le_exp.mpr ht.2⟩
  · intro hx
    have hxpos : 0 < x := (Real.exp_pos a).trans hx.1
    refine ⟨Real.log x, ⟨?_, ?_⟩, Real.exp_log hxpos⟩
    · simpa only [Real.log_exp] using Real.log_lt_log (Real.exp_pos a) hx.1
    · simpa only [Real.log_exp] using Real.log_le_log hxpos hx.2

theorem integral_exp_Ioc (f : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b) :
    (∫ x in Ioc (Real.exp a) (Real.exp b), f x) =
      ∫ t in a..b, Real.exp t * f (Real.exp t) := by
  rw [← image_exp_Ioc,
    integral_image_eq_integral_abs_deriv_smul measurableSet_Ioc
      (fun t _ => (Real.hasDerivAt_exp t).hasDerivWithinAt) Real.exp_injective.injOn,
    intervalIntegral.integral_of_le hab]
  simp only [abs_of_pos (Real.exp_pos _), smul_eq_mul]

noncomputable def logRows (F : Profile) (p : Point) : Fin 5 → ℝ :=
  ![OutgoingHistories.M F.data F.amp p,
    Real.sqrt 2 * OutgoingHistories.I F.reset p,
    Real.sqrt 2 * OutgoingHistories.J F.reset F.amp p,
    OutgoingHistories.S F.reset F.amp p,
    OutgoingHistories.Pi F.reset p - F.axisDatum p.2]

noncomputable def freeRows (F : Profile) (z : Raw) : Fin 5 → ℝ :=
  ![freeM F z, Real.sqrt 2 * freeI F z, Real.sqrt 2 * freeJ F z, freeS F z,
    freePi F z - F.axisDatum z.2.2]

theorem outgoing_moments_log (F : Profile) (p : Point) :
    NominalProfile.moments F.U F.E (Real.exp p.1) p.2 = logRows F p := by
  have hs (t : ℝ) : Real.sqrt (2 * Real.exp t) = Real.sqrt 2 * Real.exp (t / 2) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.exp_half]
  have hw (t : ℝ) : Real.exp t * Real.exp (t / 2) = Real.exp (3 * t / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  ext i
  fin_cases i <;> simp only [NominalProfile.moments, logRows, NominalProfile.density]
  · rw [integral_exp_Iic, OutgoingHistories.M_eq_integral F.data F.amp_contDiff]
    simp only [OutgoingProfile.Profile.U, Real.log_exp]
    rfl
  · rw [integral_exp_Iic, OutgoingHistories.I_eq_integral]
    simp only [OutgoingProfile.Profile.E, Real.log_exp, hs]
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Iic
    intro t _
    change Real.exp t * (Real.sqrt 2 * Real.exp (t / 2) * F.logE (t, p.2)) = _
    rw [show Real.exp t * (Real.sqrt 2 * Real.exp (t / 2) * F.logE (t, p.2)) =
      Real.sqrt 2 * (Real.exp t * Real.exp (t / 2)) * F.logE (t, p.2) by ring, hw]
    change Real.sqrt 2 * Real.exp (3 * t / 2) * F.logE (t, p.2) =
      Real.sqrt 2 * (Real.exp (3 * t / 2) * F.logE (t, p.2))
    ring
  · rw [integral_exp_Iic, OutgoingHistories.J_eq_integral F.reset F.amp_contDiff]
    simp only [OutgoingProfile.Profile.U, OutgoingProfile.Profile.E, Real.log_exp, hs]
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Iic
    intro t _
    change Real.exp t * (F.logU (t, p.2) * (Real.sqrt 2 * Real.exp (t / 2)) * F.logE (t, p.2)) = _
    rw [show Real.exp t * (F.logU (t, p.2) * (Real.sqrt 2 * Real.exp (t / 2)) * F.logE (t, p.2)) =
      Real.sqrt 2 * (Real.exp t * Real.exp (t / 2)) * F.logE (t, p.2) * F.logU (t, p.2) by ring, hw]
    change Real.sqrt 2 * Real.exp (3 * t / 2) * F.logE (t, p.2) * F.logU (t, p.2) =
      Real.sqrt 2 * (Real.exp (3 * t / 2) * F.logE (t, p.2) * F.logU (t, p.2))
    ring
  · rw [integral_exp_Iic, OutgoingHistories.S_eq_integral F.reset F.amp_contDiff]
    simp only [OutgoingProfile.Profile.U, OutgoingProfile.Profile.E, Real.log_exp]
    rfl
  · rw [integral_exp_Iic, OutgoingHistories.Pi_eq_past_integral, F.axisDatum_eq]
    simp only [add_sub_cancel_left, OutgoingProfile.Profile.E, Real.log_exp]
    apply setIntegral_congr_fun measurableSet_Iic
    intro t _
    change Real.exp t * (F.logE (t, p.2) ^ 2 / (2 * Real.exp t)) = F.logE (t, p.2) ^ 2 / 2
    field_simp [Real.exp_ne_zero]

noncomputable def logDensity (U E : ℝ) (y : ℝ) : Fin 5 → ℝ :=
  ![Real.exp y * U, Real.sqrt 2 * Real.exp (3 * y / 2) * E,
    Real.sqrt 2 * Real.exp (3 * y / 2) * E * U,
    Real.exp y * (U ^ 2 - E ^ 2 / 2), E ^ 2 / 2]

theorem density_comp_exp (U E : NominalProfile.Field) (y eta : ℝ) (i : Fin 5) :
    Real.exp y * NominalProfile.density (fun x => U (x, eta)) (fun x => E (x, eta))
      (Real.exp y) i = logDensity (U (Real.exp y, eta)) (E (Real.exp y, eta)) y i := by
  have hs : Real.sqrt (2 * Real.exp y) = Real.sqrt 2 * Real.exp (y / 2) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.exp_half]
  have he : Real.exp y * Real.exp (y / 2) = Real.exp (3 * y / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  fin_cases i
  · rfl
  · change Real.exp y * (Real.sqrt (2 * Real.exp y) * E (Real.exp y, eta)) =
      Real.sqrt 2 * Real.exp (3 * y / 2) * E (Real.exp y, eta)
    rw [hs]
    calc
      _ = Real.sqrt 2 * (Real.exp y * Real.exp (y / 2)) * E (Real.exp y, eta) := by ring
      _ = _ := by rw [he]
  · change Real.exp y * (U (Real.exp y, eta) * Real.sqrt (2 * Real.exp y) * E (Real.exp y, eta)) =
      Real.sqrt 2 * Real.exp (3 * y / 2) * E (Real.exp y, eta) * U (Real.exp y, eta)
    rw [hs]
    calc
      _ = Real.sqrt 2 * (Real.exp y * Real.exp (y / 2)) * E (Real.exp y, eta) * U (Real.exp y, eta)
        := by ring
      _ = _ := by rw [he]
  · rfl
  · change Real.exp y * (E (Real.exp y, eta) ^ 2 / (2 * Real.exp y)) = E (Real.exp y, eta) ^ 2 / 2
    field_simp [Real.exp_ne_zero]

theorem freeRows_sub_logRows (F : Profile) (z : Raw) (i : Fin 5) :
    freeRows F z i - logRows F z.2 i = ∫ t in (-5 : ℝ)..z.2.1,
      logDensity (freeU F (z.1, (t, z.2.2))) (freeE F (z.1, (t, z.2.2))) t i -
        logDensity (F.logU (t, z.2.2)) (F.logE (t, z.2.2)) t i := by
  fin_cases i
  · change (_ + ∫ t in (-5 : ℝ)..z.2.1, Real.exp t *
      (freeU F (z.1, (t, z.2.2)) - F.logU (t, z.2.2))) - OutgoingHistories.M F.data F.amp z.2 = _
    rw [add_sub_cancel_left]
    apply intervalIntegral.integral_congr
    intro t _
    norm_num [logDensity]
    ring
  · change Real.sqrt 2 * (_ + ∫ t in (-5 : ℝ)..z.2.1, Real.exp (3 * t / 2) *
      (freeE F (z.1, (t, z.2.2)) - F.logE (t, z.2.2))) - Real.sqrt 2 * _ = _
    rw [mul_add, add_sub_cancel_left, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    norm_num [logDensity]
    ring
  · change Real.sqrt 2 * (_ + ∫ t in (-5 : ℝ)..z.2.1, Real.exp (3 * t / 2) *
      (freeE F (z.1, (t, z.2.2)) * freeU F (z.1, (t, z.2.2)) -
        F.logE (t, z.2.2) * F.logU (t, z.2.2))) - Real.sqrt 2 * _ = _
    rw [mul_add, add_sub_cancel_left, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    norm_num [logDensity]
    ring
  · change (_ + ∫ t in (-5 : ℝ)..z.2.1, Real.exp t *
      ((freeU F (z.1, (t, z.2.2)) ^ 2 - freeE F (z.1, (t, z.2.2)) ^ 2 / 2) -
        (F.logU (t, z.2.2) ^ 2 - F.logE (t, z.2.2) ^ 2 / 2))) - OutgoingHistories.S F.reset F.amp
          z.2 = _
    rw [add_sub_cancel_left]
    apply intervalIntegral.integral_congr
    intro t _
    norm_num [logDensity]
    ring
  · change (_ + (1 / 2 : ℝ) * ∫ t in (-5 : ℝ)..z.2.1,
      freeE F (z.1, (t, z.2.2)) ^ 2 - F.logE (t, z.2.2) ^ 2) - _ - (_ - _) = _
    rw [show (OutgoingHistories.Pi F.reset z.2 + (1 / 2 : ℝ) *
        ∫ t in (-5 : ℝ)..z.2.1, freeE F (z.1, (t, z.2.2)) ^ 2 - F.logE (t, z.2.2) ^ 2) -
        F.axisDatum z.2.2 - (OutgoingHistories.Pi F.reset z.2 - F.axisDatum z.2.2) =
        (1 / 2 : ℝ) * ∫ t in (-5 : ℝ)..z.2.1,
          freeE F (z.1, (t, z.2.2)) ^ 2 - F.logE (t, z.2.2) ^ 2 by ring]
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    norm_num [logDensity]
    ring

theorem prefix_difference {f g : ℝ → ℝ} {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hf : IntegrableOn f (Ioc 0 b)) (hg : IntegrableOn g (Ioc 0 b))
    (hmatch : (∫ x in Ioc 0 b, f x) = ∫ x in Ioc 0 b, g x) :
    (∫ x in Ioc 0 a, f x) - (∫ x in Ioc 0 a, g x) =
      -(∫ x in Ioc a b, f x - g x) := by
  have hfs := NominalProfile.prefix_integral_split ha hab hf
  have hgs := NominalProfile.prefix_integral_split ha hab hg
  have hi : Ioc a b ⊆ Ioc (0 : ℝ) b := fun _ hx => ⟨ha.trans_lt hx.1, hx.2⟩
  rw [integral_sub (hf.mono_set hi) (hg.mono_set hi)]
  linarith

theorem normalized_density_integrable {F : Profile} {A : NominalProfile.AxisStage F}
    (c : NominalProfile.Controls A) (hsep : c.separation ≤ Real.exp (-8))
    {eta : ℝ} (heta : eta ∈ ReferencePath.parameterInterval) (i : Fin 5) :
    IntegrableOn (fun x => NominalProfile.density (fun t => c.normalizedU (t, eta))
      (fun t => c.normalizedE (t, eta)) x i) (Ioc 0 NominalProfile.matchFraction) := by
  exact NominalProfile.corrected_density_integrable F
    (NominalProfile.baseU F A.normalization c.seedU)
    (NominalProfile.baseE F A.normalization c.shapeTime c.initialShape c.seedF) c.debt
    eta NominalProfile.matchFraction
    (fun x hx => NominalProfile.baseU_ideal F A.normalization_pos hx c.seedU eta)
    (NominalProfile.baseE_ideal F A.normalization_pos c.shapeTime_pos hsep c.initialShape
      c.seedF eta (c.held_on_patch hsep heta))
    (c.base_density_integrable hsep NominalProfile.matchFraction_pos.le heta) i

/-- Every stock is recovered backwards from the actual five-row match at
the right endpoint. No estimate for the stocks is an input. -/
theorem actual_moments {F : Profile} {A : NominalProfile.AxisStage F}
    (c : NominalProfile.Controls A) (hsep : c.separation ≤ Real.exp (-8))
    {p : Point} (hy : p.1 ∈ Icc (-8) (-5)) (heta : p.2 ∈ ReferencePath.parameterInterval)
    (hs : NominalProfile.SmallDebt F c.debt p.2) :
    NominalProfile.moments c.normalizedU c.normalizedE (Real.exp p.1) p.2 =
      freeRows F (dataParameter c p.2, p) := by
  have hmatch := c.moments_at_match hsep heta hs
  have hyb : Real.exp p.1 ≤ NominalProfile.matchFraction := Real.exp_le_exp.mpr hy.2
  ext i
  have hd := prefix_difference (Real.exp_pos p.1).le hyb
    (normalized_density_integrable c hsep heta i)
    (NominalProfile.outgoing_density_integrable F p.2 NominalProfile.matchFraction i)
    (congrFun hmatch i)
  change NominalProfile.moments c.normalizedU c.normalizedE (Real.exp p.1) p.2 i -
    NominalProfile.moments F.U F.E (Real.exp p.1) p.2 i = _ at hd
  rw [outgoing_moments_log] at hd
  change _ = -(∫ x in Ioc (Real.exp p.1) (Real.exp (-5)), _) at hd
  rw [integral_exp_Ioc _ hy.2] at hd
  have he : (∫ t in p.1..(-5 : ℝ), Real.exp t *
      (NominalProfile.density (fun u => c.normalizedU (u, p.2))
        (fun u => c.normalizedE (u, p.2)) (Real.exp t) i -
       NominalProfile.density (fun u => F.U (u, p.2)) (fun u => F.E (u, p.2)) (Real.exp t) i)) =
      ∫ t in p.1..(-5 : ℝ),
        logDensity (freeU F (dataParameter c p.2, (t, p.2)))
          (freeE F (dataParameter c p.2, (t, p.2))) t i -
          logDensity (F.logU (t, p.2)) (F.logE (t, p.2)) t i := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc p.1 (-5) := by simpa only [uIcc_of_le hy.2] using ht
    have htmem : t ∈ Icc (-8) (-5) := ⟨hy.1.trans ht'.1, ht'.2⟩
    have hf := actual_fields c hsep (p := (t, p.2)) htmem heta
    dsimp only
    rw [mul_sub, density_comp_exp, density_comp_exp, hf.1, hf.2]
    simp only [OutgoingProfile.Profile.U, OutgoingProfile.Profile.E, Real.log_exp]
  rw [he, ← intervalIntegral.integral_symm] at hd
  have hf := freeRows_sub_logRows F (dataParameter c p.2, p) i
  dsimp only at hf
  linarith

open StressAlgebra

noncomputable def familyW (F : Profile) (z : Control × Point) : ℝ :=
  (Real.exp z.2.1 - 2 * axialExponent F.data.h * z.2.2 * value (freeM F) z -
    coordinateFactor z.2.2 * parameterJet (freeM F) z) / Real.exp z.2.1
noncomputable def angularNumerator (F : Profile) (z : Control × Point) : ℝ :=
  -familyW F z * (Real.exp (3 * z.2.1 / 2) * value (freeE F) z) +
    ((1 - F.data.h) * value (freeI F) z - axialExponent F.data.h * z.2.2 * parameterJet (freeI F) z
      -
      coordinateFactor z.2.2 * parameterJet (freeJ F) z +
      2 * (F.data.h - axialExponent F.data.h) * z.2.2 * value (freeJ F) z)
noncomputable def familyQ (F : Profile) (z : Control × Point) : ℝ :=
  angularNumerator F z / (Real.exp (3 * z.2.1 / 2) * value (freeE F) z)
noncomputable def familyN (F : Profile) (z : Control × Point) : ℝ :=
  -familyW F z * value (freeU F) z +
    axialExponent F.data.h * (value (freeM F) z - z.2.2 * parameterJet (freeM F) z) / Real.exp
      z.2.1 +
    (4 * F.data.h * z.2.2 * value (freeS F) z - coordinateFactor z.2.2 * parameterJet (freeS F) z) /
      Real.exp z.2.1 + 4 * velocityExponent F.data.h * z.2.2 * value (freePi F) z -
      coordinateFactor z.2.2 * parameterJet (freePi F) z
noncomputable def radialNumerator (F : Profile) (z : Control × Point) : ℝ :=
  value (freeE F) z - 2 * radialJet (freeE F) z
noncomputable def familyA (F : Profile) (z : Control × Point) : ℝ :=
  radialNumerator F z / value (freeE F) z
noncomputable def familyB (F : Profile) (z : Control × Point) : ℝ :=
  -2 * radialJet (freeU F) z / value (freeE F) z
noncomputable def familyP1 (F : Profile) (z : Control × Point) : ℝ :=
  Real.exp z.2.1 * familyQ F z / NaturalAxisData.L F.data.h z.2.2
noncomputable def familyP2 (F : Profile) (z : Control × Point) : ℝ :=
  Real.exp z.2.1 * familyN F z / (NaturalAxisData.L F.data.h z.2.2 * value (freeE F) z)
noncomputable def familySpeed (F : Profile) (z : Control × Point) : ℝ :=
  ActivationContinuation.shearSize (familyA F z) (familyB F z)
noncomputable def familyProjection (F : Profile) (z : Control × Point) : ℝ :=
  ActivationContinuation.projection (familyP1 F z) (familyP2 F z) (familyA F z) (familyB F z)

theorem coordinateFactor_contDiff : ContDiff ℝ ∞ (fun z : Control × Point => coordinateFactor
  z.2.2) :=
  contDiff_const.sub (contDiff_snd.snd.pow 2)
theorem L_contDiff (F : Profile) : ContDiff ℝ ∞ (fun z : Control × Point => NaturalAxisData.L
  F.data.h z.2.2) :=
  contDiff_const.sub (contDiff_const.mul (contDiff_snd.snd.pow 2))

theorem familyW_contDiff (F : Profile) : ContDiff ℝ ∞ (familyW F) :=
  ((contDiff_snd.fst.exp.sub ((contDiff_const.mul contDiff_snd.snd).mul
    (value_contDiff (freeM_contDiff F)))).sub
      (coordinateFactor_contDiff.mul (parameterJet_contDiff (freeM_contDiff F)))).div
        contDiff_snd.fst.exp (fun _ => Real.exp_ne_zero _)

theorem angularNumerator_contDiff (F : Profile) : ContDiff ℝ ∞ (angularNumerator F) :=
  ((familyW_contDiff F).neg.mul (((contDiff_const.mul contDiff_snd.fst).div_const 2).exp.mul
    (value_contDiff (freeE_contDiff F)))).add
    ((((contDiff_const.mul (value_contDiff (freeI_contDiff F))).sub
      ((contDiff_const.mul contDiff_snd.snd).mul (parameterJet_contDiff (freeI_contDiff F)))).sub
      (coordinateFactor_contDiff.mul (parameterJet_contDiff (freeJ_contDiff F)))).add
      ((contDiff_const.mul contDiff_snd.snd).mul (value_contDiff (freeJ_contDiff F))))

theorem familyN_contDiff (F : Profile) : ContDiff ℝ ∞ (familyN F) := by
  have hm := value_contDiff (freeM_contDiff F)
  have hm' := parameterJet_contDiff (freeM_contDiff F)
  have hs := value_contDiff (freeS_contDiff F)
  have hs' := parameterJet_contDiff (freeS_contDiff F)
  have hp := value_contDiff (freePi_contDiff F)
  have hp' := parameterJet_contDiff (freePi_contDiff F)
  exact (((((familyW_contDiff F).neg.mul (value_contDiff (freeU_contDiff F))).add
    ((contDiff_const.mul (hm.sub (contDiff_snd.snd.mul hm'))).div contDiff_snd.fst.exp
      (fun _ => Real.exp_ne_zero _))).add
    ((((contDiff_const.mul contDiff_snd.snd).mul hs).sub (coordinateFactor_contDiff.mul hs')).div
      contDiff_snd.fst.exp (fun _ => Real.exp_ne_zero _))).add
    ((contDiff_const.mul contDiff_snd.snd).mul hp)).sub (coordinateFactor_contDiff.mul hp')

theorem radialNumerator_contDiff (F : Profile) : ContDiff ℝ ∞ (radialNumerator F) :=
  (value_contDiff (freeE_contDiff F)).sub (contDiff_const.mul (radialJet_contDiff (freeE_contDiff
    F)))

noncomputable def regular (F : Profile) : Set (Control × Point) :=
  {z | value (freeE F) z ≠ 0 ∧ radialNumerator F z ≠ 0 ∧ NaturalAxisData.L F.data.h z.2.2 ≠ 0}

theorem regular_isOpen (F : Profile) : IsOpen (regular F) :=
  (isOpen_ne_fun (value_contDiff (freeE_contDiff F)).continuous continuous_const).inter
    ((isOpen_ne_fun (radialNumerator_contDiff F).continuous continuous_const).inter
      (isOpen_ne_fun (L_contDiff F).continuous continuous_const))
theorem familyA_ne (F : Profile) {z : Control × Point} (hz : z ∈ regular F) : familyA F z ≠ 0 :=
  div_ne_zero hz.2.1 hz.1
theorem familyA_contDiffOn (F : Profile) : ContDiffOn ℝ ∞ (familyA F) (regular F) :=
  (radialNumerator_contDiff F).contDiffOn.div (value_contDiff (freeE_contDiff F)).contDiffOn
    (fun _ hz => hz.1)
theorem familyB_contDiffOn (F : Profile) : ContDiffOn ℝ ∞ (familyB F) (regular F) :=
  (contDiff_const.mul (radialJet_contDiff (freeU_contDiff F))).contDiffOn.div
    (value_contDiff (freeE_contDiff F)).contDiffOn (fun _ hz => hz.1)
theorem familyQ_contDiffOn (F : Profile) : ContDiffOn ℝ ∞ (familyQ F) (regular F) :=
  (angularNumerator_contDiff F).contDiffOn.div
    ((((contDiff_const.mul contDiff_snd.fst).div_const 2).exp).mul
      (value_contDiff (freeE_contDiff F))).contDiffOn
    (fun _ hz => mul_ne_zero (Real.exp_ne_zero _) hz.1)
theorem familyP1_contDiffOn (F : Profile) : ContDiffOn ℝ ∞ (familyP1 F) (regular F) :=
  (contDiffOn_snd.fst.exp.mul (familyQ_contDiffOn F)).div (L_contDiff F).contDiffOn
    (fun _ hz => hz.2.2)
theorem familyP2_contDiffOn (F : Profile) : ContDiffOn ℝ ∞ (familyP2 F) (regular F) :=
  (contDiffOn_snd.fst.exp.mul (familyN_contDiff F).contDiffOn).div
    (((L_contDiff F).mul (value_contDiff (freeE_contDiff F))).contDiffOn)
    (fun _ hz => mul_ne_zero hz.2.2 hz.1)
theorem familySpeed_contDiffOn (F : Profile) : ContDiffOn ℝ ∞ (familySpeed F) (regular F) :=
  (familyA_contDiffOn F).mul (contDiffOn_const.add
    (((familyB_contDiffOn F).div (familyA_contDiffOn F) (fun _ hz => familyA_ne F hz)).pow 2))
theorem familyProjection_contDiffOn (F : Profile) : ContDiffOn ℝ ∞ (familyProjection F) (regular F)
  :=
  (familyP1_contDiffOn F).add ((familyP2_contDiffOn F).mul
    ((familyB_contDiffOn F).div (familyA_contDiffOn F) (fun _ hz => familyA_ne F hz)))

theorem familyW_zero (F : Profile) {p : Point} (hp : p.1 ≤ 0) :
    familyW F (0, p) = OutgoingHistories.W F.data F.amp p := by
  have hM : value (freeM F) (0, p) = OutgoingHistories.M F.data F.amp p := freeM_zero F hp
  have hM' := parameterJet_zero (freeM_contDiff F) (OutgoingHistories.M_smooth F.data
    F.amp_contDiff)
    (p := p) (fun eta => freeM_zero F (p := (p.1, eta)) hp)
  rw [familyW, hM, hM']
  rfl

theorem familyQ_zero (F : Profile) {p : Point} (hp : p.1 ≤ 0) :
    familyQ F (0, p) = OutgoingHistories.Qs F.reset F.amp p := by
  have hE : value (freeE F) (0, p) = F.logE p := freeE_zero_clean F hp
  have hI : value (freeI F) (0, p) = OutgoingHistories.I F.reset p := freeI_zero F hp
  have hJ : value (freeJ F) (0, p) = OutgoingHistories.J F.reset F.amp p := freeJ_zero F hp
  have hI' := parameterJet_zero (freeI_contDiff F) (OutgoingHistories.I_smooth F.reset)
    (p := p) (fun eta => freeI_zero F (p := (p.1, eta)) hp)
  have hJ' := parameterJet_zero (freeJ_contDiff F) (OutgoingHistories.J_smooth F.reset
    F.amp_contDiff)
    (p := p) (fun eta => freeJ_zero F (p := (p.1, eta)) hp)
  rw [familyQ, angularNumerator, familyW_zero F hp, hE, hI, hJ, hI', hJ',
    OutgoingHistories.Qs_integrated]
  rw [show OutgoingHistories.X p * OutgoingHistories.H F.reset p =
    Real.exp (3 * p.1 / 2) * F.logE p from OutgoingHistories.angularWeight_eq F.reset p]
  have hne : F.logE p ≠ 0 := (OutgoingHistories.E_pos F.reset p).ne'
  field_simp [hne, Real.exp_ne_zero]

theorem familyA_zero (F : Profile) (p : Point) : familyA F (0, p) = 4 / 5 := by
  rw [familyA, radialNumerator, radialJet_freeE_zero]
  have he : 0 < value (freeE F) (0, p) := by
    change 0 < freeE F (0, p)
    rw [freeE_zero]
    exact mul_pos (NominalProfile.idealAmplitude_pos F p.2) (Real.exp_pos _)
  field_simp [he.ne'] ; ring

theorem familyB_zero (F : Profile) (p : Point) : familyB F (0, p) = 0 := by
  simp only [familyB, radialJet_freeU_zero, mul_zero, zero_div]

theorem familySpeed_zero (F : Profile) (p : Point) : familySpeed F (0, p) = 4 / 5 := by
  simp [familySpeed, ActivationContinuation.shearSize, familyA_zero, familyB_zero]

theorem familyProjection_zero (F : Profile) {p : Point} (hp : p.1 ≤ 0) :
    familyProjection F (0, p) =
      Real.exp p.1 * OutgoingHistories.Qs F.reset F.amp p / NaturalAxisData.L F.data.h p.2 := by
  simp only [familyProjection, ActivationContinuation.projection, familyB_zero, zero_div,
    mul_zero, add_zero, familyP1, familyQ_zero F hp]

theorem zero_regular (F : Profile) {p : Point} (hp : p ∈ window) : (0, p) ∈ regular F := by
  have he : 0 < value (freeE F) (0, p) := by
    change 0 < freeE F (0, p)
    rw [freeE_zero]
    exact mul_pos (NominalProfile.idealAmplitude_pos F p.2) (Real.exp_pos _)
  refine ⟨he.ne', ?_, ?_⟩
  · intro hz
    have ha := familyA_zero F p
    simp only [familyA, hz, zero_div] at ha
    norm_num at ha
  · exact (CoordinateAlgebra.L_pos F.data.h_pos.le F.data.h_lt_half
      ((sq_le_one_iff_abs_le_one p.2).mpr (abs_le.mpr hp.2))).ne'

theorem zero_projection_lower (F : Profile) (hh : F.data.h ≤ 1 / 100)
    {p : Point} (hp : p ∈ window) : Real.exp (-8) ≤ familyProjection F (0, p) := by
  have hy : p.1 ≤ 0 := hp.1.2.trans (by norm_num)
  have hq : 1 ≤ OutgoingHistories.Qs F.reset F.amp p := by
    rw [OutgoingEntranceCone.canonical_Qs_ideal F.reset F.amp_contDiff hy]
    exact OutgoingEntranceCone.idealAngularLag_lower F.data.h_pos.le hh (abs_le.mpr hp.2)
  have hL := OutgoingEntranceCone.natural_L_bounds F.data.h_pos.le hh (abs_le.mpr hp.2)
  rw [familyProjection_zero F hy]
  apply (le_div_iff₀ (by linarith : 0 < NaturalAxisData.L F.data.h p.2)).mpr
  calc
    Real.exp (-8) * NaturalAxisData.L F.data.h p.2 ≤ Real.exp (-8) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hL.2 (Real.exp_pos (-8)).le
    _ ≤ Real.exp p.1 := Real.exp_le_exp.mpr hp.1.1
    _ ≤ Real.exp p.1 * OutgoingHistories.Qs F.reset F.amp p :=
      le_mul_of_one_le_right (Real.exp_pos _).le hq

/-- All field jets and stock jets used in the actual integrated stresses. -/
noncomputable def observations (F : Profile) (z : Control × Point) : Fin 22 → ℝ :=
  ![value (freeE F) z, value (freeU F) z, radialJet (freeE F) z, radialJet (freeU F) z,
    parameterJet (freeE F) z, parameterJet (freeU F) z,
    value (freeM F) z, value (freeI F) z, value (freeJ F) z, value (freeS F) z, value (freePi F) z,
    parameterJet (freeM F) z, parameterJet (freeI F) z, parameterJet (freeJ F) z,
    parameterJet (freeS F) z, parameterJet (freePi F) z,
    familyQ F z, familyN F z, familyA F z, familyB F z, familySpeed F z, familyProjection F z]

theorem observations_contDiffOn (F : Profile) : ContDiffOn ℝ ∞ (observations F) (regular F) := by
  apply contDiffOn_pi.mpr
  intro i
  fin_cases i <;> dsimp only [observations, Matrix.cons_val_zero, Matrix.cons_val_succ]
  · exact (value_contDiff (freeE_contDiff F)).contDiffOn
  · exact (value_contDiff (freeU_contDiff F)).contDiffOn
  · exact (radialJet_contDiff (freeE_contDiff F)).contDiffOn
  · exact (radialJet_contDiff (freeU_contDiff F)).contDiffOn
  · exact (parameterJet_contDiff (freeE_contDiff F)).contDiffOn
  · exact (parameterJet_contDiff (freeU_contDiff F)).contDiffOn
  · exact (value_contDiff (freeM_contDiff F)).contDiffOn
  · exact (value_contDiff (freeI_contDiff F)).contDiffOn
  · exact (value_contDiff (freeJ_contDiff F)).contDiffOn
  · exact (value_contDiff (freeS_contDiff F)).contDiffOn
  · exact (value_contDiff (freePi_contDiff F)).contDiffOn
  · exact (parameterJet_contDiff (freeM_contDiff F)).contDiffOn
  · exact (parameterJet_contDiff (freeI_contDiff F)).contDiffOn
  · exact (parameterJet_contDiff (freeJ_contDiff F)).contDiffOn
  · exact (parameterJet_contDiff (freeS_contDiff F)).contDiffOn
  · exact (parameterJet_contDiff (freePi_contDiff F)).contDiffOn
  · exact familyQ_contDiffOn F
  · exact (familyN_contDiff F).contDiffOn
  · exact familyA_contDiffOn F
  · exact familyB_contDiffOn F
  · exact familySpeed_contDiffOn F
  · exact familyProjection_contDiffOn F

theorem model_estimate (F : Profile) :
    ∃ r L : ℝ, 0 < r ∧ 0 ≤ L ∧ ∀ v : Control, ‖v‖ ≤ r → ∀ p ∈ window,
      (v, p) ∈ regular F ∧ ‖observations F (v, p) - observations F (0, p)‖ ≤ L * ‖v‖ := by
  apply HeatSwitchCone.compact_control_estimate (isCompact_Icc.prod isCompact_Icc)
    ((convex_Icc _ _).prod (convex_Icc _ _)) (regular_isOpen F)
  · rintro ⟨v, p⟩ ⟨hv, hp⟩
    have hv' : v = 0 := hv
    subst v
    exact zero_regular F hp
  · exact observations_contDiffOn F

/-- The tolerance depends on the fixed outgoing data. Neither an incoming
axis stage nor its controls occur before this tolerance is chosen. -/
theorem model_margins (F : Profile) (hh : F.data.h ≤ 1 / 100) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ v : Control, ‖v‖ ≤ delta → ∀ p ∈ window,
      3 / 5 ≤ familyA F (v, p) ∧ familySpeed F (v, p) ≤ 1 ∧
        Real.exp (-8) / 2 ≤ familyProjection F (v, p) := by
  obtain ⟨r, L, hr, hL, hb⟩ := model_estimate F
  let m := min (1 / 5 : ℝ) (Real.exp (-8) / 2)
  have hm : 0 < m := lt_min (by norm_num) (by positivity)
  let delta := min r (m / (L + 1))
  have hdelta : 0 < delta := lt_min hr (div_pos hm (by linarith))
  refine ⟨delta, hdelta, ?_⟩
  intro v hv p hp
  have he := (hb v (hv.trans (min_le_left _ _)) p hp).2
  have hn : L * ‖v‖ ≤ m := by
    have hd := (le_div_iff₀ (by linarith : 0 < L + 1)).mp (hv.trans (min_le_right _ _))
    nlinarith [norm_nonneg v]
  have hcomp (i : Fin 22) : |observations F (v, p) i - observations F (0, p) i| ≤ m := by
    have hi := norm_le_pi_norm (observations F (v, p) - observations F (0, p)) i
    exact hi.trans (he.trans hn)
  have ha : |familyA F (v, p) - 4 / 5| ≤ m := by
    simpa [observations, familyA_zero] using hcomp 18
  have hs : |familySpeed F (v, p) - 4 / 5| ≤ m := by
    simpa [observations, familySpeed_zero] using hcomp 20
  have hproj : |familyProjection F (v, p) - familyProjection F (0, p)| ≤ m := by
    simpa [observations] using hcomp 21
  have hm1 : m ≤ 1 / 5 := min_le_left _ _
  have hm2 : m ≤ Real.exp (-8) / 2 := min_le_right _ _
  refine ⟨?_, ?_, ?_⟩
  · linarith [(abs_le.mp ha).1]
  · linarith [(abs_le.mp hs).2]
  · linarith [(abs_le.mp hproj).1, zero_projection_lower F hh hp]

noncomputable def chart (R : ℝ) (p : Point) : Point := (R * Real.exp p.1, p.2)
noncomputable def angularScale (R : ℝ) : ℝ := R * Real.sqrt R * Real.sqrt 2

theorem chart_mem {F : Profile} {A : NominalProfile.AxisStage F} (c : NominalProfile.Controls A)
    {p : Point} (heta : p.2 ∈ ReferencePath.parameterInterval)
    (hs : NominalProfile.SmallDebt F c.debt p.2) : chart c.radius p ∈ c.admissibleDomain.carrier :=
  c.admissible_nonnegative (mul_pos c.radius_pos (Real.exp_pos _)).le heta hs

theorem parameter_admissible_eventually {F : Profile} {A : NominalProfile.AxisStage F}
    (c : NominalProfile.Controls A) {eta : ℝ} (heta : eta ∈ ReferencePath.parameterInterval)
    (hs : NominalProfile.SmallDebt F c.debt eta) :
    ∀ᶠ e in 𝓝 eta, e ∈ ReferencePath.parameterInterval ∧ NominalProfile.SmallDebt F c.debt e := by
  have hm : (0, eta) ∈ c.admissibleDomain.carrier := c.admissible_nonnegative le_rfl heta hs
  have hn : ∀ᶠ e in 𝓝 eta, (0, e) ∈ c.admissibleDomain.carrier :=
    (continuous_const.prodMk continuous_id).continuousAt (c.admissibleDomain.isOpen.mem_nhds hm)
  filter_upwards [hn] with e he
  exact ⟨he.1.2, he.2⟩

theorem physical_rows {F : Profile} {A : NominalProfile.AxisStage F}
    (c : NominalProfile.Controls A) (hsep : c.separation ≤ Real.exp (-8))
    {p : Point} (hy : p.1 ∈ Icc (-8) (-5)) (heta : p.2 ∈ ReferencePath.parameterInterval)
    (hs : NominalProfile.SmallDebt F c.debt p.2) (i : Fin 5) :
    ProfileHistories.primitive (fun q => NominalProfile.regularDensity (c.profiles hsep) q i)
      (chart c.radius p) =
      NominalProfile.dilationFactor c.radius i * freeRows F (dataParameter c p.2, p) i := by
  have hX : 0 < (chart c.radius p).1 := mul_pos c.radius_pos (Real.exp_pos _)
  have hpr : ProfileHistories.primitive (fun q => NominalProfile.regularDensity (c.profiles hsep) q
    i)
      (chart c.radius p) = NominalProfile.moments c.U c.E (chart c.radius p).1 p.2 i := by
    rw [ProfileHistories.primitive, intervalIntegral.integral_of_le hX.le]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro x hx
    exact (congrArg (fun d : Fin 5 → ℝ => d i) (c.physical_density_eq hsep hx.1 p.2)).symm
  rw [hpr]
  change NominalProfile.moments (NominalProfile.dilateField c.radius c.normalizedU)
    (NominalProfile.dilateField c.radius c.normalizedE) (c.radius * Real.exp p.1) p.2 i = _
  rw [NominalProfile.moments_dilate c.radius c.radius_pos,
    mul_div_cancel_left₀ _ c.radius_pos.ne', actual_moments c hsep hy heta hs]

theorem physical_stock_values {F : Profile} {A : NominalProfile.AxisStage F}
    (c : NominalProfile.Controls A) (hsep : c.separation ≤ Real.exp (-8))
    {p : Point} (hy : p.1 ∈ Icc (-8) (-5)) (heta : p.2 ∈ ReferencePath.parameterInterval)
    (hs : NominalProfile.SmallDebt F c.debt p.2) :
    (c.profiles hsep).M (chart c.radius p) = c.radius * value (freeM F) (controls c p.2, p) ∧
    (c.profiles hsep).I (chart c.radius p) = angularScale c.radius * value (freeI F) (controls c
      p.2, p) ∧
    (c.profiles hsep).J (chart c.radius p) = angularScale c.radius * value (freeJ F) (controls c
      p.2, p) ∧
    (c.profiles hsep).S (chart c.radius p) = c.radius * value (freeS F) (controls c p.2, p) ∧
    (c.profiles hsep).pressure (chart c.radius p) = value (freePi F) (controls c p.2, p) := by
  have h0 := physical_rows c hsep hy heta hs 0
  have h1 := physical_rows c hsep hy heta hs 1
  have h2 := physical_rows c hsep hy heta hs 2
  have h3 := physical_rows c hsep hy heta hs 3
  have h4 := physical_rows c hsep hy heta hs 4
  change (c.profiles hsep).M (chart c.radius p) = c.radius * value (freeM F) (controls c p.2, p) at
    h0
  change (c.profiles hsep).I (chart c.radius p) =
    (c.radius * Real.sqrt c.radius) * (Real.sqrt 2 * value (freeI F) (controls c p.2, p)) at h1
  change (c.profiles hsep).J (chart c.radius p) =
    (c.radius * Real.sqrt c.radius) * (Real.sqrt 2 * value (freeJ F) (controls c p.2, p)) at h2
  change (c.profiles hsep).S (chart c.radius p) = c.radius * value (freeS F) (controls c p.2, p) at
    h3
  change ProfileHistories.primitive (fun q => c.f q ^ 2) (chart c.radius p) =
    1 * (value (freePi F) (controls c p.2, p) - F.axisDatum p.2) at h4
  refine ⟨h0, ?_, ?_, h3, ?_⟩
  · rw [h1, angularScale]
    ring
  · rw [h2, angularScale]
    ring
  · change F.axisDatum p.2 + ProfileHistories.primitive (fun q => c.f q ^ 2) (chart c.radius p) = _
    rw [h4]
    ring

theorem parameter_of_germ {D : ProfileHistories.RadialDomain} {H : Point → ℝ}
    (hH : ContDiffOn ℝ ∞ H D.carrier) {f : Raw → ℝ} (hf : ContDiff ℝ ∞ f)
    {F : Profile} {A : NominalProfile.AxisStage F} (c : NominalProfile.Controls A)
    {p : Point} (heta : p.2 ∈ ReferencePath.parameterInterval)
    (hs : NominalProfile.SmallDebt F c.debt p.2) (s X : ℝ) (hp : (X, p.2) ∈ D.carrier)
    (he : (fun eta => H (X, eta)) =ᶠ[𝓝 p.2]
      (fun eta => s * f (dataParameter c eta, (p.1, eta)))) :
    ProfileHistories.parameterPartial H (X, p.2) = s * parameterJet f (controls c p.2, p) := by
  have hd := (parameterJet_hasDerivAt hf (dataParameter_hasDerivAt c heta hs) p.1).const_mul s
  exact (ProfileHistories.parameterPartial_hasDerivAt D hH hp).unique
    (hd.congr_of_eventuallyEq he)

theorem physical_stock_parameters {F : Profile} {A : NominalProfile.AxisStage F}
    (c : NominalProfile.Controls A) (hsep : c.separation ≤ Real.exp (-8))
    {p : Point} (hy : p.1 ∈ Icc (-8) (-5)) (heta : p.2 ∈ ReferencePath.parameterInterval)
    (hs : NominalProfile.SmallDebt F c.debt p.2) :
    ProfileHistories.parameterPartial (c.profiles hsep).M (chart c.radius p) =
      c.radius * parameterJet (freeM F) (controls c p.2, p) ∧
    ProfileHistories.parameterPartial (c.profiles hsep).I (chart c.radius p) =
      angularScale c.radius * parameterJet (freeI F) (controls c p.2, p) ∧
    ProfileHistories.parameterPartial (c.profiles hsep).J (chart c.radius p) =
      angularScale c.radius * parameterJet (freeJ F) (controls c p.2, p) ∧
    ProfileHistories.parameterPartial (c.profiles hsep).S (chart c.radius p) =
      c.radius * parameterJet (freeS F) (controls c p.2, p) ∧
    ProfileHistories.parameterPartial (c.profiles hsep).pressure (chart c.radius p) =
      parameterJet (freePi F) (controls c p.2, p) := by
  have hp := chart_mem c heta hs
  have hn := parameter_admissible_eventually c heta hs
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply parameter_of_germ (c.profiles hsep).M_smooth (freeM_contDiff F) c heta hs c.radius _ hp
    filter_upwards [hn] with e he
    exact (physical_stock_values c hsep (p := (p.1, e)) hy he.1 he.2).1
  · apply parameter_of_germ (c.profiles hsep).I_smooth (freeI_contDiff F) c heta hs (angularScale
    c.radius) _ hp
    filter_upwards [hn] with e he
    exact (physical_stock_values c hsep (p := (p.1, e)) hy he.1 he.2).2.1
  · apply parameter_of_germ (c.profiles hsep).J_smooth (freeJ_contDiff F) c heta hs (angularScale
    c.radius) _ hp
    filter_upwards [hn] with e he
    exact (physical_stock_values c hsep (p := (p.1, e)) hy he.1 he.2).2.2.1
  · apply parameter_of_germ (c.profiles hsep).S_smooth (freeS_contDiff F) c heta hs c.radius _ hp
    filter_upwards [hn] with e he
    exact (physical_stock_values c hsep (p := (p.1, e)) hy he.1 he.2).2.2.2.1
  · have h := parameter_of_germ (c.profiles hsep).pressure_smooth (freePi_contDiff F) c heta hs 1
      (chart c.radius p).1 hp ?_
    · simp only [one_mul] at h
      exact h
    · filter_upwards [hn] with e he
      have hv := (physical_stock_values c hsep (p := (p.1, e)) hy he.1 he.2).2.2.2.2
      simp only [one_mul]
      exact hv

theorem physical_field_values {F : Profile} {A : NominalProfile.AxisStage F}
    (c : NominalProfile.Controls A) (hsep : c.separation ≤ Real.exp (-8))
    {p : Point} (hy : p.1 ∈ Icc (-8) (-5)) (heta : p.2 ∈ ReferencePath.parameterInterval) :
    (c.profiles hsep).U (chart c.radius p) = value (freeU F) (controls c p.2, p) ∧
      (c.profiles hsep).E (chart c.radius p) = value (freeE F) (controls c p.2, p) := by
  have hv := actual_fields c hsep hy heta
  constructor
  · change c.normalizedU ((c.radius * Real.exp p.1) / c.radius, p.2) = _
    simp only [mul_div_cancel_left₀ _ c.radius_pos.ne']
    exact hv.1
  · rw [c.profiles_E hsep (mul_pos c.radius_pos (Real.exp_pos _))]
    change c.normalizedE ((c.radius * Real.exp p.1) / c.radius, p.2) = _
    simp only [mul_div_cancel_left₀ _ c.radius_pos.ne']
    exact hv.2

theorem sqrt_chart {R : ℝ} (hR : 0 < R) (y : ℝ) :
    Real.sqrt (2 * (R * Real.exp y)) = Real.sqrt (2 * R) * Real.exp (y / 2) := by
  rw [← mul_assoc, Real.sqrt_mul (by positivity : 0 ≤ 2 * R)]
  congr 1
  exact (Real.exp_half y).symm

theorem angularScale_pos {R : ℝ} (hR : 0 < R) : 0 < angularScale R := by
  exact mul_pos (mul_pos hR (Real.sqrt_pos.mpr hR)) (Real.sqrt_pos.mpr (by norm_num))

theorem angular_weight_chart {D : ProfileHistories.RadialDomain}
    (P : ProfileHistories.Profiles D) {R : ℝ} (hR : 0 < R) (p : Point) :
    (chart R p).1 * P.H (chart R p) =
      angularScale R * (Real.exp (3 * p.1 / 2) * P.E (chart R p)) := by
  have hH : P.H (chart R p) = Real.sqrt (2 * (R * Real.exp p.1)) * P.E (chart R p) := by
    dsimp only [ProfileHistories.Profiles.H, ProfileHistories.Profiles.E, chart]
    rw [← mul_assoc (Real.sqrt (2 * (R * Real.exp p.1)))
      (Real.sqrt (2 * (R * Real.exp p.1))),
      Real.mul_self_sqrt (by positivity : 0 ≤ 2 * (R * Real.exp p.1))]
  have he : Real.exp (3 * p.1 / 2) = Real.exp p.1 * Real.exp (p.1 / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hH, sqrt_chart hR, he, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  dsimp only [chart, angularScale]
  ring

theorem physical_transport {F : Profile} {A : NominalProfile.AxisStage F}
    (c : NominalProfile.Controls A) (hsep : c.separation ≤ Real.exp (-8))
    {p : Point} (hy : p.1 ∈ Icc (-8) (-5)) (heta : p.2 ∈ ReferencePath.parameterInterval)
    (hs : NominalProfile.SmallDebt F c.debt p.2) :
    (c.profiles hsep).W F.data.h (chart c.radius p) = familyW F (controls c p.2, p) := by
  have hm := (physical_stock_values c hsep hy heta hs).1
  have hm' := (physical_stock_parameters c hsep hy heta hs).1
  have hw := ActivationStocks.profile_massFlux (c.profiles hsep) F.data.h (chart_mem c heta hs)
  rw [hm, hm'] at hw
  dsimp only [ActivationStocks.massFlux, chart, NaturalAxisData.D, NaturalAxisData.d] at hw
  dsimp only [familyW, axialExponent, coordinateFactor]
  apply (eq_div_iff (Real.exp_ne_zero p.1)).mpr
  apply (mul_left_cancel₀ c.radius_pos.ne')
  dsimp only [chart]
  nlinarith [hw]

theorem physical_lags {F : Profile} {A : NominalProfile.AxisStage F}
    (c : NominalProfile.Controls A) (hsep : c.separation ≤ Real.exp (-8))
    {p : Point} (hy : p.1 ∈ Icc (-8) (-5)) (heta : p.2 ∈ ReferencePath.parameterInterval)
    (hs : NominalProfile.SmallDebt F c.debt p.2) :
    (c.profiles hsep).angularLag F.data.h (chart c.radius p) = familyQ F (controls c p.2, p) ∧
      (c.profiles hsep).axialLag F.data.h (chart c.radius p) = familyN F (controls c p.2, p) := by
  have hp := chart_mem c heta hs
  have hX : 0 < (chart c.radius p).1 := mul_pos c.radius_pos (Real.exp_pos _)
  obtain ⟨hU, hE⟩ := physical_field_values c hsep hy heta
  obtain ⟨hM, hI, hJ, hS, hPi⟩ := physical_stock_values c hsep hy heta hs
  obtain ⟨hM', hI', hJ', hS', hPi'⟩ := physical_stock_parameters c hsep hy heta hs
  have hw := physical_transport c hsep hy heta hs
  have he : 0 < value (freeE F) (controls c p.2, p) := by
    rw [← hE, c.profiles_E hsep hX]
    exact c.E_positive hsep hX heta hs
  have hweight := angular_weight_chart (c.profiles hsep) c.radius_pos p
  rw [hE] at hweight
  have hH : (c.profiles hsep).H (chart c.radius p) ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hweight
    exact (ne_of_gt (mul_pos (angularScale_pos c.radius_pos) (mul_pos (Real.exp_pos _) he)))
      hweight.symm
  constructor
  · rw [(c.profiles hsep).angularLag_integrated F.data.h hp hX.ne' hH,
      hw, hI, hJ, hI', hJ', hweight]
    dsimp only [chart, familyQ, angularNumerator]
    field_simp [he.ne', (angularScale_pos c.radius_pos).ne', Real.exp_ne_zero]
  · rw [(c.profiles hsep).axialLag_integrated F.data.h hp hX,
      hw, hU, hM, hM', hS, hS', hPi, hPi']
    dsimp only [chart, familyN]
    field_simp [c.radius_pos.ne', Real.exp_ne_zero]

theorem physical_stocks {F : Profile} {A : NominalProfile.AxisStage F}
    (c : NominalProfile.Controls A) (hsep : c.separation ≤ Real.exp (-8))
    {p : Point} (hy : p.1 ∈ Icc (-8) (-5)) (heta : p.2 ∈ ReferencePath.parameterInterval)
    (hs : NominalProfile.SmallDebt F c.debt p.2) :
    ReferenceBounds.p1 (c.profiles hsep) F.data.h (chart c.radius p) =
        c.radius * familyP1 F (controls c p.2, p) ∧
      ReferenceBounds.p2 (c.profiles hsep) F.data.h (chart c.radius p) =
        c.radius * familyP2 F (controls c p.2, p) := by
  obtain ⟨hQ, hN⟩ := physical_lags c hsep hy heta hs
  have hE := (physical_field_values c hsep hy heta).2
  constructor
  · dsimp only [ReferenceBounds.p1]
    rw [hQ]
    dsimp only [chart, familyP1]
    ring
  · dsimp only [ReferenceBounds.p2, ReferenceBounds.ns]
    rw [hN, hE]
    dsimp only [chart, familyP2]
    ring

theorem physicalE_smoothAt {D : ProfileHistories.RadialDomain}
    (P : ProfileHistories.Profiles D) {p : Point} (hp : p ∈ D.carrier)
    (hX : 0 < p.1) : ContDiffAt ℝ ∞ P.E p :=
  ((contDiffAt_const.mul contDiffAt_fst).sqrt (by positivity)).mul
    (P.f_smooth.contDiffAt (D.isOpen.mem_nhds hp))

theorem derivative_eq_on_interval {f g : ℝ → ℝ} {dg a b y : ℝ} (hab : a < b)
    (hy : y ∈ Icc a b) (hf : DifferentiableAt ℝ f y) (hg : HasDerivAt g dg y)
    (he : EqOn f g (Icc a b)) : deriv f y = dg := by
  have hd : HasDerivWithinAt f dg (Icc a b) y :=
    hg.hasDerivWithinAt.congr he (he hy)
  exact (uniqueDiffOn_Icc hab y hy).eq_deriv _ hf.hasDerivAt.hasDerivWithinAt hd

theorem physical_field_radials {F : Profile} {A : NominalProfile.AxisStage F}
    (c : NominalProfile.Controls A) (hsep : c.separation ≤ Real.exp (-8))
    {p : Point} (hy : p.1 ∈ Icc (-8) (-5)) (heta : p.2 ∈ ReferencePath.parameterInterval)
    (hs : NominalProfile.SmallDebt F c.debt p.2) :
    deriv (fun y => (c.profiles hsep).U (c.radius * Real.exp y, p.2)) p.1 =
        radialJet (freeU F) (controls c p.2, p) ∧
      deriv (fun y => (c.profiles hsep).E (c.radius * Real.exp y, p.2)) p.1 =
        radialJet (freeE F) (controls c p.2, p) := by
  have hp := chart_mem c heta hs
  have hc : ContDiffAt ℝ ∞ (fun y => (c.radius * Real.exp y, p.2)) p.1 :=
    (contDiffAt_const.mul contDiffAt_id.exp).prodMk contDiffAt_const
  constructor
  · apply derivative_eq_on_interval (by norm_num : (-8 : ℝ) < -5) hy
      (((c.profiles hsep).U_smooth.contDiffAt (c.admissibleDomain.isOpen.mem_nhds hp)).comp p.1 hc
        |>.differentiableAt (by simp))
      (radialJet_hasDerivAt (freeU_contDiff F) (controls c p.2) p)
    intro y hy'
    exact (physical_field_values c hsep (p := (y, p.2)) hy' heta).1
  · apply derivative_eq_on_interval (by norm_num : (-8 : ℝ) < -5) hy
      (((physicalE_smoothAt (c.profiles hsep) hp (mul_pos c.radius_pos (Real.exp_pos _))).comp p.1
        hc).differentiableAt (by simp))
      (radialJet_hasDerivAt (freeE_contDiff F) (controls c p.2) p)
    intro y hy'
    exact (physical_field_values c hsep (p := (y, p.2)) hy' heta).2

theorem physical_field_parameters {F : Profile} {A : NominalProfile.AxisStage F}
    (c : NominalProfile.Controls A) (hsep : c.separation ≤ Real.exp (-8))
    {p : Point} (hy : p.1 ∈ Icc (-8) (-5)) (heta : p.2 ∈ ReferencePath.parameterInterval)
    (hs : NominalProfile.SmallDebt F c.debt p.2) :
    ProfileHistories.parameterPartial (c.profiles hsep).U (chart c.radius p) =
        parameterJet (freeU F) (controls c p.2, p) ∧
      ProfileHistories.parameterPartial (c.profiles hsep).E (chart c.radius p) =
        parameterJet (freeE F) (controls c p.2, p) := by
  have hp := chart_mem c heta hs
  have hn := parameter_admissible_eventually c heta hs
  constructor
  · have hd := parameter_of_germ (c.profiles hsep).U_smooth (freeU_contDiff F) c heta hs 1
      (chart c.radius p).1 hp ?_
    · simp only [one_mul] at hd
      exact hd
    · filter_upwards [hn] with e he
      have hv := (physical_field_values c hsep (p := (p.1, e)) hy he.1).1
      simp only [one_mul]
      exact hv
  · have hE := (physicalE_smoothAt (c.profiles hsep) hp
        (mul_pos c.radius_pos (Real.exp_pos _))).differentiableAt (by simp)
    have hd : HasDerivAt (fun e => (c.profiles hsep).E ((chart c.radius p).1, e))
        (ProfileHistories.parameterPartial (c.profiles hsep).E (chart c.radius p)) p.2 := by
      exact hE.hasFDerivAt.comp_hasDerivAt p.2
          ((hasDerivAt_const p.2 (chart c.radius p).1).prodMk (hasDerivAt_id p.2))
    apply hd.unique
    apply (parameterJet_hasDerivAt (freeE_contDiff F) (dataParameter_hasDerivAt c heta hs)
      p.1).congr_of_eventuallyEq
    filter_upwards [hn] with e he
    exact (physical_field_values c hsep (p := (p.1, e)) hy he.1).2

theorem shear_dilation_cancel {r z f : ℝ} (hr : r ≠ 0) (hz : z ≠ 0) (hf : f ≠ 0)
    (X df : ℝ) :
    -2 * X * df / f = 1 - 2 * (r * (z * (1 / 2)) * f + r * z * (df * X)) / (r * z * f) := by
  rw [show (2 : ℝ) * (r * (z * (1 / 2)) * f + r * z * (df * X)) =
    (r * z) * (f + 2 * df * X) by ring,
    mul_div_mul_left _ _ (mul_ne_zero hr hz)]
  field_simp [hf] ; ring

/-- This chart identity uses actual radial derivatives and the square-root
relation between the regular angular profile and the physical angular field. -/
theorem physical_log_shears {D : ProfileHistories.RadialDomain}
    (P : ProfileHistories.Profiles D) {R : ℝ} (hR : 0 < R) (p : Point)
    (hp : chart R p ∈ D.carrier) (hf : P.f (chart R p) ≠ 0) :
    ActivationContinuation.shearA P (chart R p) =
        1 - 2 * deriv (fun y => P.E (R * Real.exp y, p.2)) p.1 / P.E (chart R p) ∧
      ActivationContinuation.shearB P (chart R p) =
        -2 * deriv (fun y => P.U (R * Real.exp y, p.2)) p.1 / P.E (chart R p) := by
  have hc := (Real.hasDerivAt_exp p.1).const_mul R
  have hfd := (ProfileHistories.radialPartial_hasDerivAt D P.f_smooth hp).comp p.1 hc
  have hud := (ProfileHistories.radialPartial_hasDerivAt D P.U_smooth hp).comp p.1 hc
  have hr := (((hasDerivAt_id p.1).div_const 2).exp).const_mul (Real.sqrt (2 * R))
  dsimp only [chart, Function.comp_def, id_eq] at hfd hud hr
  have he : (fun y => P.E (R * Real.exp y, p.2)) =
      (fun y => (Real.sqrt (2 * R) * Real.exp (y / 2)) * P.f (R * Real.exp y, p.2)) := by
    funext y
    exact congrArg (fun t => t * P.f (R * Real.exp y, p.2)) (sqrt_chart hR y)
  constructor
  · rw [he, (hr.fun_mul hfd).deriv]
    change -2 * (R * Real.exp p.1) * ProfileHistories.radialPartial P.f (chart R p) /
      P.f (chart R p) = _
    rw [show P.E (chart R p) = (Real.sqrt (2 * R) * Real.exp (p.1 / 2)) * P.f (chart R p) from
      congrArg (fun t => t * P.f (chart R p)) (sqrt_chart hR p.1)]
    exact shear_dilation_cancel (Real.sqrt_pos.2 (by positivity)).ne'
      (Real.exp_ne_zero _) hf _ _
  · rw [hud.deriv]
    unfold ActivationContinuation.shearB
    dsimp only [chart]
    ring

theorem physical_shears {F : Profile} {A : NominalProfile.AxisStage F}
    (c : NominalProfile.Controls A) (hsep : c.separation ≤ Real.exp (-8))
    {p : Point} (hy : p.1 ∈ Icc (-8) (-5)) (heta : p.2 ∈ ReferencePath.parameterInterval)
    (hs : NominalProfile.SmallDebt F c.debt p.2) :
    ActivationContinuation.shearA (c.profiles hsep) (chart c.radius p) = familyA F (controls c p.2,
      p) ∧
      ActivationContinuation.shearB (c.profiles hsep) (chart c.radius p) = familyB F (controls c
        p.2, p) := by
  have hp := chart_mem c heta hs
  have hX : 0 < (chart c.radius p).1 := mul_pos c.radius_pos (Real.exp_pos _)
  have hpos : 0 < (c.profiles hsep).E (chart c.radius p) := by
    rw [c.profiles_E hsep hX]
    exact c.E_positive hsep hX heta hs
  have hf : (c.profiles hsep).f (chart c.radius p) ≠ 0 := by
    intro hz
    change 0 < Real.sqrt (2 * (chart c.radius p).1) * (c.profiles hsep).f (chart c.radius p) at hpos
    simp only [hz, mul_zero, lt_self_iff_false] at hpos
  have he := (physical_field_values c hsep hy heta).2
  have hd := physical_field_radials c hsep hy heta hs
  obtain ⟨ha, hb⟩ := physical_log_shears (c.profiles hsep) c.radius_pos p hp hf
  rw [hd.2, he] at ha
  rw [hd.1, he] at hb
  refine ⟨ha.trans ?_, hb⟩
  rw [he] at hpos
  dsimp only [familyA, radialNumerator]
  field_simp [hpos.ne']

theorem physical_projection {F : Profile} {A : NominalProfile.AxisStage F}
    (c : NominalProfile.Controls A) (hsep : c.separation ≤ Real.exp (-8))
    {p : Point} (hy : p.1 ∈ Icc (-8) (-5)) (heta : p.2 ∈ ReferencePath.parameterInterval)
    (hs : NominalProfile.SmallDebt F c.debt p.2) :
    ActivationContinuation.projection
        (ReferenceBounds.p1 (c.profiles hsep) F.data.h (chart c.radius p))
        (ReferenceBounds.p2 (c.profiles hsep) F.data.h (chart c.radius p))
        (ActivationContinuation.shearA (c.profiles hsep) (chart c.radius p))
        (ActivationContinuation.shearB (c.profiles hsep) (chart c.radius p)) =
      c.radius * familyProjection F (controls c p.2, p) := by
  obtain ⟨ha, hb⟩ := physical_shears c hsep hy heta hs
  obtain ⟨hp, hq⟩ := physical_stocks c hsep hy heta hs
  rw [ha, hb, hp, hq]
  dsimp only [familyProjection, ActivationContinuation.projection]
  ring

/-- These are actual field values, first radial and parameter jets, five
normalized histories and their parameter derivatives, and integrated cone
coordinates. The projection is divided by the physical matching radius. -/
noncomputable def actualObservations {F : Profile} {A : NominalProfile.AxisStage F}
    (c : NominalProfile.Controls A) (hsep : c.separation ≤ Real.exp (-8)) (p : Point) : Fin 22 → ℝ
      :=
  let P := c.profiles hsep
  let q := chart c.radius p
  ![P.E q, P.U q,
    deriv (fun y => P.E (c.radius * Real.exp y, p.2)) p.1,
    deriv (fun y => P.U (c.radius * Real.exp y, p.2)) p.1,
    ProfileHistories.parameterPartial P.E q, ProfileHistories.parameterPartial P.U q,
    P.M q / c.radius, P.I q / angularScale c.radius, P.J q / angularScale c.radius,
    P.S q / c.radius, P.pressure q,
    ProfileHistories.parameterPartial P.M q / c.radius,
    ProfileHistories.parameterPartial P.I q / angularScale c.radius,
    ProfileHistories.parameterPartial P.J q / angularScale c.radius,
    ProfileHistories.parameterPartial P.S q / c.radius, ProfileHistories.parameterPartial
      P.pressure q,
    P.angularLag F.data.h q, P.axialLag F.data.h q,
    ActivationContinuation.shearA P q, ActivationContinuation.shearB P q,
    ActivationContinuation.shearSize (ActivationContinuation.shearA P q)
      (ActivationContinuation.shearB P q),
    ActivationContinuation.projection (ReferenceBounds.p1 P F.data.h q) (ReferenceBounds.p2 P
      F.data.h q)
      (ActivationContinuation.shearA P q) (ActivationContinuation.shearB P q) / c.radius]

theorem actualObservations_eq {F : Profile} {A : NominalProfile.AxisStage F}
    (c : NominalProfile.Controls A) (hsep : c.separation ≤ Real.exp (-8))
    {p : Point} (hy : p.1 ∈ Icc (-8) (-5)) (heta : p.2 ∈ ReferencePath.parameterInterval)
    (hs : NominalProfile.SmallDebt F c.debt p.2) :
    actualObservations c hsep p = observations F (controls c p.2, p) := by
  obtain ⟨hU, hE⟩ := physical_field_values c hsep hy heta
  obtain ⟨hUy, hEy⟩ := physical_field_radials c hsep hy heta hs
  obtain ⟨hUeta, hEeta⟩ := physical_field_parameters c hsep hy heta hs
  obtain ⟨hM, hI, hJ, hS, hPi⟩ := physical_stock_values c hsep hy heta hs
  obtain ⟨hM', hI', hJ', hS', hPi'⟩ := physical_stock_parameters c hsep hy heta hs
  obtain ⟨hQ, hN⟩ := physical_lags c hsep hy heta hs
  obtain ⟨ha, hb⟩ := physical_shears c hsep hy heta hs
  have hp := physical_projection c hsep hy heta hs
  dsimp only [actualObservations]
  rw [hp, hU, hE, hUy, hEy, hUeta, hEeta, hM, hI, hJ, hS, hPi,
    hM', hI', hJ', hS', hPi', hQ, hN, ha, hb]
  simp only [mul_div_cancel_left₀ _ c.radius_pos.ne',
    mul_div_cancel_left₀ _ (angularScale_pos c.radius_pos).ne']
  rfl

/-- A genuine uniform bound for the actual jets and stocks. Its constants
are chosen before the incoming axis stage and before its controls. -/
theorem actual_observation_estimate (F : Profile) :
    ∃ r L : ℝ, 0 < r ∧ 0 ≤ L ∧
      ∀ (A : NominalProfile.AxisStage F) (c : NominalProfile.Controls A)
        (hsep : c.separation ≤ Real.exp (-8)) (eps : ℝ), eps ≤ r →
        JetBounds.FiniteJetBound 1 (endpointError c) (Icc (-1) 1) eps →
        JetBounds.FiniteJetBound 1 (NominalProfile.resetCoefficients F c.debt) (Icc (-1) 1) eps →
        ∀ p ∈ window, NominalProfile.SmallDebt F c.debt p.2 →
          ‖actualObservations c hsep p - observations F (0, p)‖ ≤ L * eps := by
  obtain ⟨r, L, hr, hL, hb⟩ := model_estimate F
  refine ⟨r, L, hr, hL, ?_⟩
  intro A c hsep eps heps hG hc p hp hs
  have hn := controls_norm c hG hc hp.2
  rw [actualObservations_eq c hsep hp.1 (NominalProfile.physical_band_in_parameterInterval hp.2) hs]
  exact (hb _ (hn.trans heps) p hp).2.trans (mul_le_mul_of_nonneg_left hn hL)

/-- The radius and first-jet tolerance are fixed before every incoming
axis stage and its matching controls. The input stocks are not hypotheses:
they have already been reconstructed from exact five-row matching. -/
theorem exists_repair_cone_log (F : Profile) :
    ∃ delta R0 : ℝ, 0 < delta ∧ 0 < R0 ∧
      ∀ (A : NominalProfile.AxisStage F) (c : NominalProfile.Controls A)
        (hsep : c.separation ≤ Real.exp (-8)),
        JetBounds.FiniteJetBound 1 (endpointError c) (Icc (-1) 1) delta →
        JetBounds.FiniteJetBound 1 (NominalProfile.resetCoefficients F c.debt) (Icc (-1) 1) delta →
        R0 ≤ c.radius → ∀ p ∈ window, NominalProfile.SmallDebt F c.debt p.2 →
          ActivationContinuation.IsRelaxed (c.profiles hsep) F.data.h (chart c.radius p) := by
  by_cases hh : F.data.h ≤ 1 / 100
  · obtain ⟨delta, hdelta, hm⟩ := model_margins F hh
    refine ⟨delta, 6 / Real.exp (-8), hdelta, by positivity, ?_⟩
    intro A c hsep hG hc hR p hp hs
    have heta := NominalProfile.physical_band_in_parameterInterval hp.2
    have hb := hm _ (controls_norm c hG hc hp.2) p hp
    obtain ⟨ha, hbb⟩ := physical_shears c hsep hp.1 heta hs
    have hspeed : ActivationContinuation.shearSize
        (ActivationContinuation.shearA (c.profiles hsep) (chart c.radius p))
        (ActivationContinuation.shearB (c.profiles hsep) (chart c.radius p)) ≤ 1 := by
      rw [ha, hbb]
      exact hb.2.1
    have hfloor : 6 ≤ c.radius * Real.exp (-8) :=
      (div_le_iff₀ (Real.exp_pos (-8))).mp hR
    have hproj : 2 < ActivationContinuation.projection
        (ReferenceBounds.p1 (c.profiles hsep) F.data.h (chart c.radius p))
        (ReferenceBounds.p2 (c.profiles hsep) F.data.h (chart c.radius p))
        (ActivationContinuation.shearA (c.profiles hsep) (chart c.radius p))
        (ActivationContinuation.shearB (c.profiles hsep) (chart c.radius p)) := by
      rw [physical_projection c hsep hp.1 heta hs]
      have hl := mul_le_mul_of_nonneg_left hb.2.2 c.radius_pos.le
      nlinarith
    refine ⟨?_, hproj, ConeAlgebra.relaxed_cone_of_le_two hproj (hspeed.trans (by norm_num))⟩
    rw [ha]
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 3 / 5) hb.1
  · refine ⟨1, 1, zero_lt_one, zero_lt_one, ?_⟩
    intro A
    exact False.elim (hh (by linarith [A.small.h_le]))

/-- Actual relaxed cone on the complete closed physical restore/repair
annulus, with a tolerance and radius floor depending only on `F`. -/
theorem exists_repair_cone (F : Profile) :
    ∃ delta R0 : ℝ, 0 < delta ∧ 0 < R0 ∧
      ∀ (A : NominalProfile.AxisStage F) (c : NominalProfile.Controls A)
        (hsep : c.separation ≤ Real.exp (-8)),
        JetBounds.FiniteJetBound 1 (endpointError c) (Icc (-1) 1) delta →
        JetBounds.FiniteJetBound 1 (NominalProfile.resetCoefficients F c.debt) (Icc (-1) 1) delta →
        R0 ≤ c.radius → ∀ p : Point,
          p.1 ∈ Icc (c.radius * Real.exp (-8)) (c.radius * Real.exp (-5)) →
          p.2 ∈ Icc (-1) 1 → NominalProfile.SmallDebt F c.debt p.2 →
            ActivationContinuation.IsRelaxed (c.profiles hsep) F.data.h p := by
  obtain ⟨delta, R0, hd, hR0, hb⟩ := exists_repair_cone_log F
  refine ⟨delta, R0, hd, hR0, ?_⟩
  intro A c hsep hG hc hR p hp heta hs
  have hx : 0 < p.1 := (mul_pos c.radius_pos (Real.exp_pos (-8))).trans_le hp.1
  have hxR : 0 < p.1 / c.radius := div_pos hx c.radius_pos
  have hlo : Real.exp (-8) ≤ p.1 / c.radius :=
    (le_div_iff₀ c.radius_pos).mpr (by nlinarith [hp.1])
  have hhi : p.1 / c.radius ≤ Real.exp (-5) :=
    (div_le_iff₀ c.radius_pos).mpr (by nlinarith [hp.2])
  have hy : Real.log (p.1 / c.radius) ∈ Icc (-8) (-5) := by
    constructor
    · simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos (-8)) hlo
    · simpa only [Real.log_exp] using Real.log_le_log hxR hhi
  have he : chart c.radius (Real.log (p.1 / c.radius), p.2) = p := by
    apply Prod.ext
    · dsimp only [chart]
      rw [Real.exp_log hxR]
      field_simp [c.radius_pos.ne']
    · rfl
  have hh := hb A c hsep hG hc hR (Real.log (p.1 / c.radius), p.2) ⟨hy, heta⟩ hs
  rwa [he] at hh

end NavierStokes.RepairConeBounds
