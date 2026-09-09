/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.HeatedOutgoing
public import LeanPool.NavierStokesAndEuler.NavierStokes.OutgoingCone
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Topology.MetricSpace.Thickening

@[expose] public section

/-!
# The compensated heat switch preserves the outgoing cone

The inverse entrance radius, the three compensation coefficients, and their
actual parameter derivatives are finite-dimensional perturbation parameters.
All estimates are on a fixed logarithmic interval, before the fully switched
terminal edge.  Constants are chosen after the outgoing profile and before
the entrance radius.
-/

noncomputable section

open Set Filter Function MeasureTheory
open scoped ContDiff Topology BigOperators
open NavierStokes.OutgoingProfile (Profile)

namespace NavierStokes.HeatSwitchCone


/-- A smooth finite-dimensional family has a uniform first-order estimate in
its control variable near a compact convex set of base points. -/
theorem compact_control_estimate
    {P B V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {s : Set B} (hs : IsCompact s) (hc : Convex ℝ s)
    {u : Set (P × B)} (hu : IsOpen u) (hsub : ({0} : Set P) ×ˢ s ⊆ u)
    {f : P × B → V} (hf : ContDiffOn ℝ ∞ f u) :
    ∃ r L : ℝ, 0 < r ∧ 0 ≤ L ∧ ∀ p : P, ‖p‖ ≤ r → ∀ b ∈ s,
      (p, b) ∈ u ∧ ‖f (p, b) - f (0, b)‖ ≤ L * ‖p‖ := by
  obtain ⟨r, hr, hru⟩ := (isCompact_singleton.prod hs).exists_cthickening_subset_open hu hsub
  let t : Set (P × B) := Metric.closedBall 0 r ×ˢ s
  have htu : t ⊆ u := by
    intro z hz
    apply hru
    apply Metric.mem_cthickening_of_dist_le z (0, z.2) r (({0} : Set P) ×ˢ s)
    · exact ⟨rfl, hz.2⟩
    · simpa [Prod.dist_eq, Metric.mem_closedBall, dist_zero_right] using hz.1
  have ht : IsCompact t := (isCompact_closedBall (0 : P) r).prod hs
  have hd : ContinuousOn (fderiv ℝ f) t := by
    intro z hz
    exact (((hf.contDiffAt (hu.mem_nhds (htu hz))).fderiv_right
      (m := 0) (by simp)).continuousAt).continuousWithinAt
  obtain ⟨L, hL⟩ := ht.exists_bound_of_continuousOn hd
  refine ⟨r, max 0 L, hr, le_max_left _ _, ?_⟩
  intro p hp b hb
  have hp' : (p, b) ∈ t := ⟨by simpa using hp, hb⟩
  have h0 : ((0 : P), b) ∈ t := ⟨by simpa using hr.le, hb⟩
  refine ⟨htu hp', ?_⟩
  have he := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z hz => (hf.contDiffAt (hu.mem_nhds (htu hz))).differentiableAt (by simp))
    (fun z hz => (hL z hz).trans (le_max_right 0 L))
    ((convex_closedBall (0 : P) r).prod hc) h0 hp'
  simpa only [Prod.mk_sub_mk, sub_zero, sub_self, Prod.norm_mk, norm_zero,
    max_eq_left (norm_nonneg p)] using he

abbrev Point := ℝ × ℝ
abbrev Coeff := TerminalCompensation.Coeff
abbrev Raw := (ℝ × Coeff) × Point
abbrev Control := ℝ × (Coeff × Coeff)

/-- The genuine heat multiplier, smoothly continued only in the auxiliary
inverse-radius variable and outside the physical parameter band. -/
noncomputable def freeE (F : Profile) (z : Raw) : ℝ :=
  F.logE z.2 * (1 + OutgoingSchedule.sigma
    ((z.2.1 - HeatTailEdit.switchStart F.data) / (3 / 10)) *
      (HeatProfileExtension.extension (1 + F.data.h)
        (2 * (1 - z.2.2 ^ 2) * z.1.1 * Real.exp (-z.2.1)) - 1)) +
  OutgoingDilation.shapedPatchAmplitude F z.2.2 * TerminalCompensation.correction
    OutgoingDilation.compensationPatch z.1.2
    (Real.exp (z.2.1 - OutgoingDilation.patchClock F))

theorem freeE_contDiff (F : Profile) : ContDiff ℝ ∞ (freeE F) := by
  have he := F.logE_contDiff.comp (contDiff_snd : ContDiff ℝ ∞ (fun z : Raw => z.2))
  have hs : ContDiff ℝ ∞ (fun z : Raw => OutgoingSchedule.sigma
      ((z.2.1 - HeatTailEdit.switchStart F.data) / (3 / 10))) :=
    OutgoingSchedule.sigma_contDiff.comp ((contDiff_snd.fst.sub contDiff_const).div_const _)
  have hz : ContDiff ℝ ∞ (fun z : Raw =>
      2 * (1 - z.2.2 ^ 2) * z.1.1 * Real.exp (-z.2.1)) :=
    ((contDiff_const.mul (contDiff_const.sub (contDiff_snd.snd.pow 2))).mul
      contDiff_fst.fst).mul contDiff_snd.fst.neg.exp
  have hh := (HeatProfileExtension.extension_contDiff
    (show 1 < 1 + F.data.h by linarith [F.data.h_pos])).comp hz
  have hb : ContDiff ℝ ∞ (fun z : Raw => TerminalCompensation.correction
    OutgoingDilation.compensationPatch z.1.2
      (Real.exp (z.2.1 - OutgoingDilation.patchClock F))) := by
    apply ContDiff.sum
    intro j _
    exact ((contDiff_apply ℝ ℝ j).comp contDiff_fst.snd).mul
      ((TerminalCompensation.bump_contDiff OutgoingDilation.compensationPatch j).comp
        (contDiff_snd.fst.sub contDiff_const).exp)
  exact (he.mul (contDiff_const.add (hs.mul (hh.sub contDiff_const)))).add
    (((OutgoingDilation.shapedPatchAmplitude_contDiff F).comp contDiff_snd.snd).mul hb)

@[simp] theorem freeE_zero (F : Profile) (p : Point) : freeE F ((0, 0), p) = F.logE p := by
  simp [freeE, HeatProfileExtension.extension_zero
    (show 1 < 1 + F.data.h by linarith [F.data.h_pos]), TerminalCompensation.correction]

/-- The normalized integral of a perturbation, starting at the reserved patch. -/
noncomputable def finitePrefix (F : Profile) (f : Raw → ℝ) (z : Raw) : ℝ :=
  ∫ t in OutgoingDilation.patchClock F..z.2.1, f (z.1, (t, z.2.2))

theorem finitePrefix_contDiff (F : Profile) {f : Raw → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (finitePrefix F f) := by
  have hmap : ContDiff ℝ ∞ (fun z : ((ℝ × Coeff) × ℝ) × ℝ =>
      (z.1.1, (z.2, z.1.2)) : (((ℝ × Coeff) × ℝ) × ℝ) → Raw) :=
    contDiff_fst.fst.prodMk (contDiff_snd.prodMk contDiff_fst.snd)
  have hg : ContDiff ℝ ∞ (fun z : ((ℝ × Coeff) × ℝ) × ℝ => f (z.1.1, (z.2, z.1.2))) :=
    hf.comp hmap
  have hi : ContDiff ℝ ∞ (fun z : ((ℝ × Coeff) × ℝ) × ℝ =>
      ∫ t in OutgoingDilation.patchClock F..z.2, f (z.1.1, (t, z.1.2))) :=
    HeatedOutgoing.anchoredPrimitive_contDiff (P := (ℝ × Coeff) × ℝ)
      (fun z => f (z.1.1, (z.2, z.1.2))) hg (OutgoingDilation.patchClock F)
  have hm : ContDiff ℝ ∞ (fun z : Raw => ((z.1, z.2.2), z.2.1)) :=
    (contDiff_fst.prodMk contDiff_snd.snd).prodMk contDiff_snd.fst
  have hh := hi.comp hm
  exact hh

noncomputable def freeI (F : Profile) (z : Raw) : ℝ :=
  OutgoingHistories.I F.reset z.2 + finitePrefix F
    (fun q => Real.exp (3 * q.2.1 / 2) * (freeE F q - F.logE q.2)) z

noncomputable def freeS (F : Profile) (z : Raw) : ℝ :=
  OutgoingHistories.S F.reset F.amp z.2 - (1 / 2 : ℝ) * finitePrefix F
    (fun q => Real.exp q.2.1 * (freeE F q ^ 2 - F.logE q.2 ^ 2)) z

noncomputable def freePi (F : Profile) (z : Raw) : ℝ :=
  OutgoingHistories.Pi F.reset z.2 + (1 / 2 : ℝ) * finitePrefix F
    (fun q => freeE F q ^ 2 - F.logE q.2 ^ 2) z

theorem freeI_contDiff (F : Profile) : ContDiff ℝ ∞ (freeI F) := by
  exact ((OutgoingHistories.I_smooth F.reset).comp contDiff_snd).add
    (finitePrefix_contDiff F (((contDiff_const.mul contDiff_snd.fst).div_const 2).exp.mul
      ((freeE_contDiff F).sub (F.logE_contDiff.comp contDiff_snd))))

theorem freeS_contDiff (F : Profile) : ContDiff ℝ ∞ (freeS F) := by
  exact ((OutgoingHistories.S_smooth F.reset F.amp_contDiff).comp contDiff_snd).sub
    (contDiff_const.mul (finitePrefix_contDiff F (contDiff_snd.fst.exp.mul
      (((freeE_contDiff F).pow 2).sub ((F.logE_contDiff.comp contDiff_snd).pow 2)))))

theorem freePi_contDiff (F : Profile) : ContDiff ℝ ∞ (freePi F) := by
  exact ((OutgoingHistories.Pi_smooth F.reset).comp contDiff_snd).add
    (contDiff_const.mul (finitePrefix_contDiff F
      (((freeE_contDiff F).pow 2).sub ((F.logE_contDiff.comp contDiff_snd).pow 2))))

@[simp] theorem freeI_zero (F : Profile) (p : Point) :
    freeI F ((0, 0), p) = OutgoingHistories.I F.reset p := by
  change OutgoingHistories.I F.reset p +
    (∫ t in OutgoingDilation.patchClock F..p.1,
      Real.exp (3 * t / 2) * (freeE F ((0, 0), (t, p.2)) - F.logE (t, p.2))) = _
  simp only [freeE_zero, sub_self, mul_zero, intervalIntegral.integral_zero, add_zero]

@[simp] theorem freeS_zero (F : Profile) (p : Point) :
    freeS F ((0, 0), p) = OutgoingHistories.S F.reset F.amp p := by
  change OutgoingHistories.S F.reset F.amp p - (1 / 2 : ℝ) *
    (∫ t in OutgoingDilation.patchClock F..p.1,
      Real.exp t * (freeE F ((0, 0), (t, p.2)) ^ 2 - F.logE (t, p.2) ^ 2)) = _
  simp only [freeE_zero, sub_self, mul_zero, intervalIntegral.integral_zero, sub_zero]

@[simp] theorem freePi_zero (F : Profile) (p : Point) :
    freePi F ((0, 0), p) = OutgoingHistories.Pi F.reset p := by
  change OutgoingHistories.Pi F.reset p + (1 / 2 : ℝ) *
    (∫ t in OutgoingDilation.patchClock F..p.1,
      freeE F ((0, 0), (t, p.2)) ^ 2 - F.logE (t, p.2) ^ 2) = _
  simp only [freeE_zero, sub_self, intervalIntegral.integral_zero, mul_zero, add_zero]

noncomputable def rawPoint (z : Control × Point) : Raw := ((z.1.1, z.1.2.1), z.2)

noncomputable def value (f : Raw → ℝ) (z : Control × Point) : ℝ := f (rawPoint z)
noncomputable def radialJet (f : Raw → ℝ) (z : Control × Point) : ℝ :=
  fderiv ℝ f (rawPoint z) ((0, 0), (1, 0))
noncomputable def parameterJet (f : Raw → ℝ) (z : Control × Point) : ℝ :=
  fderiv ℝ f (rawPoint z) ((0, z.1.2.2), (0, 1))

theorem rawPoint_contDiff : ContDiff ℝ ∞ rawPoint :=
  (contDiff_fst.fst.prodMk contDiff_fst.snd.fst).prodMk contDiff_snd

theorem value_contDiff {f : Raw → ℝ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (value f) :=
  hf.comp rawPoint_contDiff

theorem radialJet_contDiff {f : Raw → ℝ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (radialJet f) :=
  ((hf.fderiv_right (m := ∞) (by simp)).comp rawPoint_contDiff).clm_apply contDiff_const

theorem parameterJet_contDiff {f : Raw → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (parameterJet f) :=
  ((hf.fderiv_right (m := ∞) (by simp)).comp rawPoint_contDiff).clm_apply
    ((contDiff_const.prodMk contDiff_fst.snd.snd).prodMk contDiff_const)

theorem radialJet_hasDerivAt {f : Raw → ℝ} (hf : ContDiff ℝ ∞ f)
    (v : Control) (p : Point) :
    HasDerivAt (fun y => value f (v, (y, p.2))) (radialJet f (v, p)) p.1 := by
  have hg : HasDerivAt (fun y => ((v.1, v.2.1), (y, p.2)) : ℝ → Raw)
      ((0, 0), (1, 0)) p.1 :=
    (hasDerivAt_const _ _).prodMk ((hasDerivAt_id _).prodMk (hasDerivAt_const _ _))
  exact ((hf.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt _ hg)

theorem parameterJet_hasDerivWithinAt {f : Raw → ℝ} (hf : ContDiff ℝ ∞ f)
    {c : ℝ → Coeff} {dc : Coeff} {s : Set ℝ} {eta : ℝ}
    (hc : HasDerivWithinAt c dc s eta) (delta y : ℝ) :
    HasDerivWithinAt (fun t => f ((delta, c t), (y, t)))
      (parameterJet f ((delta, (c eta, dc)), (y, eta))) s eta := by
  have hg : HasDerivWithinAt (fun t => ((delta, c t), (y, t)) : ℝ → Raw)
      ((0, dc), (0, 1)) s eta :=
    ((hasDerivWithinAt_const _ _ _).prodMk hc).prodMk
      ((hasDerivWithinAt_const _ _ _).prodMk (hasDerivWithinAt_id _ _))
  exact ((hf.differentiable (by simp) _).hasFDerivAt.comp_hasDerivWithinAt _ hg)

theorem radialJet_zero {f : Raw → ℝ} {g : Point → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hzero : ∀ p, f ((0, 0), p) = g p) (p : Point) :
    radialJet f (0, p) = OutgoingHistories.dY g p := by
  have hd := radialJet_hasDerivAt hf (0 : Control) p
  have he : (fun y => value f (0, (y, p.2))) = (fun y => g (y, p.2)) := by
    funext y
    exact hzero _
  rw [he] at hd
  exact hd.unique (OutgoingHistories.dY_hasDerivAt hg p)

theorem parameterJet_zero {f : Raw → ℝ} {g : Point → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hzero : ∀ p, f ((0, 0), p) = g p) (p : Point) :
    parameterJet f (0, p) = OutgoingHistories.dEta g p := by
  have hd := parameterJet_hasDerivWithinAt hf
    (hasDerivWithinAt_const p.2 univ (0 : Coeff)) 0 p.1
  have he : (fun t => f ((0, 0), (p.1, t))) = (fun t => g (p.1, t)) := by
    funext t
    exact hzero _
  rw [he] at hd
  exact (hasDerivWithinAt_univ.mp hd).unique (OutgoingHistories.dEta_hasDerivAt hg p)

theorem radius_quotient (XR y a : ℝ) (hXR : 0 < XR) :
    XR * Real.exp y / (XR * Real.exp a) = Real.exp (y - a) := by
  rw [Real.exp_sub]
  field_simp

/-- Exact equality with the physical edit, including the actual diffusion
`1 - eta^2` and all three additive compensation bumps. -/
theorem freeE_eq_physical (F : Profile) (XR : ℝ) (c : ℝ → Coeff)
    (hXR : 0 < XR) (y eta : ℝ) (heta : eta ∈ HeatedOutgoing.parameterDomain) :
    freeE F ((1 / XR, c eta), (y, eta)) =
      HeatedOutgoing.E F XR c (XR * Real.exp y, eta) := by
  have hs : (XR * Real.exp y, eta) ∈ HeatedOutgoing.domain :=
    ⟨mul_pos hXR (Real.exp_pos _), heta⟩
  rw [HeatedOutgoing.E, HeatedOutgoing.heatE_eq_extended F XR hs]
  have hz : 2 * (1 - eta ^ 2) * (1 / XR) * Real.exp (-y) =
      2 * (1 - eta ^ 2) / (XR * Real.exp y) := by
    rw [Real.exp_neg]
    ring
  simp only [freeE, HeatedOutgoing.extendedHeatE, HeatedOutgoing.patchIncrement,
    OutgoingDilation.E, OutgoingProfile.Profile.E, OutgoingDilation.switchRadius,
    OutgoingDilation.patchRadius, OutgoingDilation.radius, HeatTailEdit.switch,
    HeatProfileExtension.physicalProfile, HeatProfileExtension.scaledProfile,
    mul_div_cancel_left₀ _ hXR.ne', radius_quotient XR y _ hXR, Real.log_exp, hz]

noncomputable def controls (F : Profile) {XR C : ℝ}
    (w : HeatedOutgoing.CompensationWitness F XR C) (eta : ℝ) : Control :=
  (1 / XR, (w.coefficients eta, derivWithin w.coefficients HeatedOutgoing.parameterDomain eta))

theorem controls_norm (F : Profile) {XR C : ℝ}
    (w : HeatedOutgoing.CompensationWitness F XR C) {eta : ℝ}
    (heta : eta ∈ HeatedOutgoing.parameterDomain) :
    ‖controls F w eta‖ ≤
      max (Real.exp (HeatTailEdit.switchStart F.data)) C / OutgoingDilation.switchRadius F XR := by
  have hK := OutgoingDilation.switchRadius_pos F XR w.radius_pos
  have hfirst : ‖(1 : ℝ) / XR‖ = Real.exp (HeatTailEdit.switchStart F.data) /
      OutgoingDilation.switchRadius F XR := by
    rw [Real.norm_eq_abs, abs_of_pos (div_pos zero_lt_one w.radius_pos)]
    unfold OutgoingDilation.switchRadius OutgoingDilation.radius
    rw [mul_comm XR]
    simpa only [mul_one] using
      (mul_div_mul_left (1 : ℝ) XR (Real.exp_ne_zero (HeatTailEdit.switchStart F.data))).symm
  rw [controls, Prod.norm_mk, Prod.norm_mk, hfirst]
  apply max_le
  · exact (div_le_div_iff_of_pos_right hK).mpr (le_max_left _ _)
  · exact (max_le (w.coefficient_bound eta heta) (w.derivative_bound eta heta)).trans
      ((div_le_div_iff_of_pos_right hK).mpr (le_max_right _ _))

open StressAlgebra

noncomputable def angularNumerator (F : Profile) (z : Control × Point) : ℝ :=
  -OutgoingHistories.W F.data F.amp z.2 *
      (Real.exp (3 * z.2.1 / 2) * value (freeE F) z) +
    ((1 - F.data.h) * value (freeI F) z - axialExponent F.data.h * z.2.2 *
      parameterJet (freeI F) z - coordinateFactor z.2.2 *
        OutgoingHistories.dEta (OutgoingHistories.J F.reset F.amp) z.2 +
      2 * (F.data.h - axialExponent F.data.h) * z.2.2 *
        OutgoingHistories.J F.reset F.amp z.2)

noncomputable def radialNumerator (F : Profile) (z : Control × Point) : ℝ :=
  value (freeE F) z - 2 * radialJet (freeE F) z

noncomputable def familyQ (F : Profile) (z : Control × Point) : ℝ :=
  angularNumerator F z / (Real.exp (3 * z.2.1 / 2) * value (freeE F) z)

noncomputable def familyN (F : Profile) (z : Control × Point) : ℝ :=
  -OutgoingHistories.W F.data F.amp z.2 * F.logU z.2 +
    axialExponent F.data.h * (OutgoingHistories.M F.data F.amp z.2 -
      z.2.2 * OutgoingHistories.dEta (OutgoingHistories.M F.data F.amp) z.2) / Real.exp z.2.1 +
    (4 * F.data.h * z.2.2 * value (freeS F) z -
      coordinateFactor z.2.2 * parameterJet (freeS F) z) / Real.exp z.2.1 +
    4 * velocityExponent F.data.h * z.2.2 * value (freePi F) z -
      coordinateFactor z.2.2 * parameterJet (freePi F) z

noncomputable def familyA (F : Profile) (z : Control × Point) : ℝ :=
  radialNumerator F z / value (freeE F) z
noncomputable def familyB (F : Profile) (z : Control × Point) : ℝ :=
  2 * OutgoingHistories.dY F.logU z.2 / value (freeE F) z
noncomputable def familyR (F : Profile) (z : Control × Point) : ℝ :=
  familyN F z / (value (freeE F) z * familyQ F z)
noncomputable def familyC (F : Profile) (z : Control × Point) : ℝ :=
  1 - familyB F z * familyR F z / familyA F z
noncomputable def familyJ (F : Profile) (z : Control × Point) : ℝ :=
  familyR F z + familyB F z / familyA F z
noncomputable def familyV (F : Profile) (z : Control × Point) : ℝ :=
  familyA F z * (1 + (familyB F z / familyA F z) ^ 2)
noncomputable def familyGap (F : Profile) (z : Control × Point) : ℝ :=
  2 * familyC F z ^ 2 - (familyV F z - 2) * familyJ F z ^ 2

theorem angularNumerator_contDiff (F : Profile) : ContDiff ℝ ∞ (angularNumerator F) := by
  have he := value_contDiff (freeE_contDiff F)
  have hi := value_contDiff (freeI_contDiff F)
  have hi' := parameterJet_contDiff (freeI_contDiff F)
  have hj := (OutgoingHistories.J_smooth F.reset F.amp_contDiff).comp
    (contDiff_snd : ContDiff ℝ ∞ (fun z : Control × Point => z.2))
  have hj' := (OutgoingHistories.dEta_smooth
    (OutgoingHistories.J_smooth F.reset F.amp_contDiff)).comp
    (contDiff_snd : ContDiff ℝ ∞ (fun z : Control × Point => z.2))
  have hw := (OutgoingHistories.W_smooth F.data F.amp_contDiff).comp
    (contDiff_snd : ContDiff ℝ ∞ (fun z : Control × Point => z.2))
  have hd : ContDiff ℝ ∞ (fun z : Control × Point => coordinateFactor z.2.2) :=
    contDiff_const.sub (contDiff_snd.snd.pow 2)
  exact (hw.neg.mul (((contDiff_const.mul contDiff_snd.fst).div_const 2).exp.mul he)).add
    ((((contDiff_const.mul hi).sub
      ((contDiff_const.mul contDiff_snd.snd).mul hi')).sub (hd.mul hj')).add
      ((contDiff_const.mul contDiff_snd.snd).mul hj))

theorem radialNumerator_contDiff (F : Profile) : ContDiff ℝ ∞ (radialNumerator F) :=
  (value_contDiff (freeE_contDiff F)).sub (contDiff_const.mul (radialJet_contDiff (freeE_contDiff
    F)))

theorem familyN_contDiff (F : Profile) : ContDiff ℝ ∞ (familyN F) := by
  have hw := (OutgoingHistories.W_smooth F.data F.amp_contDiff).comp
    (contDiff_snd : ContDiff ℝ ∞ (fun z : Control × Point => z.2))
  have hm := (OutgoingHistories.M_smooth F.data F.amp_contDiff).comp
    (contDiff_snd : ContDiff ℝ ∞ (fun z : Control × Point => z.2))
  have hm' := (OutgoingHistories.dEta_smooth
    (OutgoingHistories.M_smooth F.data F.amp_contDiff)).comp
    (contDiff_snd : ContDiff ℝ ∞ (fun z : Control × Point => z.2))
  have hd : ContDiff ℝ ∞ (fun z : Control × Point => coordinateFactor z.2.2) :=
    contDiff_const.sub (contDiff_snd.snd.pow 2)
  have hs := value_contDiff (freeS_contDiff F)
  have hs' := parameterJet_contDiff (freeS_contDiff F)
  have hp := value_contDiff (freePi_contDiff F)
  have hp' := parameterJet_contDiff (freePi_contDiff F)
  exact ((((hw.neg.mul (F.logU_contDiff.comp contDiff_snd)).add
    ((contDiff_const.mul (hm.sub (contDiff_snd.snd.mul hm'))).div
      contDiff_snd.fst.exp (fun z => (Real.exp_pos _).ne'))).add
      ((((contDiff_const.mul contDiff_snd.snd).mul hs).sub (hd.mul hs')).div
        contDiff_snd.fst.exp (fun z => (Real.exp_pos _).ne'))).add
          ((contDiff_const.mul contDiff_snd.snd).mul hp)).sub (hd.mul hp')

/-- This open set excludes only the denominators of the actual normalized
cone coordinates. Its zero-control slice contains the clean true cone. -/
noncomputable def regular (F : Profile) : Set (Control × Point) :=
  {z | value (freeE F) z ≠ 0 ∧ angularNumerator F z ≠ 0 ∧ radialNumerator F z ≠ 0}

theorem regular_isOpen (F : Profile) : IsOpen (regular F) :=
  (isOpen_ne_fun (value_contDiff (freeE_contDiff F)).continuous continuous_const).inter
    ((isOpen_ne_fun (angularNumerator_contDiff F).continuous continuous_const).inter
      (isOpen_ne_fun (radialNumerator_contDiff F).continuous continuous_const))

theorem familyQ_ne (F : Profile) {z : Control × Point} (hz : z ∈ regular F) : familyQ F z ≠ 0 :=
  div_ne_zero hz.2.1 (mul_ne_zero (Real.exp_ne_zero _) hz.1)
theorem familyA_ne (F : Profile) {z : Control × Point} (hz : z ∈ regular F) : familyA F z ≠ 0 :=
  div_ne_zero hz.2.2 hz.1

theorem familyQ_contDiffOn (F : Profile) : ContDiffOn ℝ ∞ (familyQ F) (regular F) :=
  (angularNumerator_contDiff F).contDiffOn.div
    ((((contDiff_const.mul contDiff_snd.fst).div_const 2).exp).mul
      (value_contDiff (freeE_contDiff F))).contDiffOn
    (fun _ hz => mul_ne_zero (Real.exp_ne_zero _) hz.1)
theorem familyA_contDiffOn (F : Profile) : ContDiffOn ℝ ∞ (familyA F) (regular F) :=
  (radialNumerator_contDiff F).contDiffOn.div (value_contDiff (freeE_contDiff F)).contDiffOn
    (fun _ hz => hz.1)
theorem familyB_contDiffOn (F : Profile) : ContDiffOn ℝ ∞ (familyB F) (regular F) :=
  (contDiff_const.mul ((OutgoingHistories.dY_smooth F.logU_contDiff).comp
    contDiff_snd)).contDiffOn.div (value_contDiff (freeE_contDiff F)).contDiffOn (fun _ hz => hz.1)
theorem familyR_contDiffOn (F : Profile) : ContDiffOn ℝ ∞ (familyR F) (regular F) :=
  (familyN_contDiff F).contDiffOn.div
    ((value_contDiff (freeE_contDiff F)).contDiffOn.mul (familyQ_contDiffOn F))
    (fun _ hz => mul_ne_zero hz.1 (familyQ_ne F hz))
theorem familyC_contDiffOn (F : Profile) : ContDiffOn ℝ ∞ (familyC F) (regular F) :=
  contDiffOn_const.sub (((familyB_contDiffOn F).mul (familyR_contDiffOn F)).div
    (familyA_contDiffOn F) (fun _ hz => familyA_ne F hz))
theorem familyJ_contDiffOn (F : Profile) : ContDiffOn ℝ ∞ (familyJ F) (regular F) :=
  (familyR_contDiffOn F).add ((familyB_contDiffOn F).div
    (familyA_contDiffOn F) (fun _ hz => familyA_ne F hz))
theorem familyV_contDiffOn (F : Profile) : ContDiffOn ℝ ∞ (familyV F) (regular F) :=
  (familyA_contDiffOn F).mul (contDiffOn_const.add
    (((familyB_contDiffOn F).div (familyA_contDiffOn F) (fun _ hz => familyA_ne F hz)).pow 2))
theorem familyGap_contDiffOn (F : Profile) : ContDiffOn ℝ ∞ (familyGap F) (regular F) :=
  (contDiffOn_const.mul ((familyC_contDiffOn F).pow 2)).sub
    (((familyV_contDiffOn F).sub contDiffOn_const).mul ((familyJ_contDiffOn F).pow 2))

@[simp] theorem familyQ_zero (F : Profile) (p : Point) :
    familyQ F (0, p) = OutgoingHistories.Qs F.reset F.amp p := by
  have hi := parameterJet_zero (freeI_contDiff F) (OutgoingHistories.I_smooth F.reset)
    (freeI_zero F) p
  rw [OutgoingHistories.Qs_integrated]
  simp only [familyQ, angularNumerator, value, rawPoint, Prod.fst_zero, Prod.snd_zero,
    freeE_zero, freeI_zero, hi]
  rw [show OutgoingHistories.X p * OutgoingHistories.H F.reset p =
    Real.exp (3 * p.1 / 2) * F.logE p from OutgoingHistories.angularWeight_eq F.reset p]
  change (-OutgoingHistories.W F.data F.amp p * (Real.exp (3 * p.1 / 2) * F.logE p) + _) /
    (Real.exp (3 * p.1 / 2) * F.logE p) = _
  have hp : F.logE p ≠ 0 := (OutgoingHistories.E_pos F.reset p).ne'
  field_simp [(Real.exp_pos (3 * p.1 / 2)).ne', hp]

@[simp] theorem familyN_zero (F : Profile) (p : Point) :
    familyN F (0, p) = OutgoingHistories.Ns F.reset F.amp p := by
  have hs := parameterJet_zero (freeS_contDiff F)
    (OutgoingHistories.S_smooth F.reset F.amp_contDiff) (freeS_zero F) p
  have hp := parameterJet_zero (freePi_contDiff F) (OutgoingHistories.Pi_smooth F.reset)
    (freePi_zero F) p
  rw [OutgoingHistories.Ns_integrated]
  simp only [familyN, value, rawPoint, Prod.fst_zero, Prod.snd_zero, freeS_zero, freePi_zero, hs,
    hp]
  rfl

@[simp] theorem familyA_zero (F : Profile) (p : Point) :
    familyA F (0, p) = OutgoingEntranceCone.coneA F.reset p := by
  have he := radialJet_zero (freeE_contDiff F) F.logE_contDiff (freeE_zero F) p
  rw [OutgoingEntranceCone.coneA_eq_E_derivative]
  simp only [familyA, radialNumerator, value, rawPoint, Prod.fst_zero, Prod.snd_zero,
    freeE_zero, he]
  change (F.logE p - 2 * OutgoingHistories.dY F.logE p) / F.logE p =
    1 - 2 * OutgoingHistories.dY F.logE p / F.logE p
  have hp : F.logE p ≠ 0 := (OutgoingHistories.E_pos F.reset p).ne'
  field_simp

@[simp] theorem familyB_zero (F : Profile) (p : Point) :
    familyB F (0, p) = OutgoingEntranceCone.coneB F.reset F.amp p := by
  simp only [familyB, value, rawPoint, Prod.fst_zero, Prod.snd_zero, freeE_zero]
  rfl
@[simp] theorem familyR_zero (F : Profile) (p : Point) :
    familyR F (0, p) = OutgoingEntranceCone.coneRatio F.reset F.amp p := by
  simp only [familyR, familyN_zero, familyQ_zero, value, rawPoint,
    Prod.fst_zero, Prod.snd_zero, freeE_zero]
  rfl
@[simp] theorem familyC_zero (F : Profile) (p : Point) :
    familyC F (0, p) = OutgoingCone.sourceC F.reset F.amp p := by
  simp only [familyC, familyB_zero, familyR_zero, familyA_zero]
  rfl
@[simp] theorem familyJ_zero (F : Profile) (p : Point) :
    familyJ F (0, p) = OutgoingCone.sourceJ F.reset F.amp p := by
  simp only [familyJ, familyB_zero, familyR_zero, familyA_zero]
  rfl
@[simp] theorem familyV_zero (F : Profile) (p : Point) :
    familyV F (0, p) = OutgoingCone.normalV F.reset F.amp p := by
  simp only [familyV, familyB_zero, familyA_zero]
  rfl
@[simp] theorem familyGap_zero (F : Profile) (p : Point) :
    familyGap F (0, p) = OutgoingCone.leadingGap F.reset F.amp p := by
  simp only [familyGap, familyC_zero, familyJ_zero, familyV_zero]
  rfl

/-- Evaluation at the actual compensation coefficients. -/
noncomputable def realize (f : Raw → ℝ) (delta : ℝ) (c : ℝ → Coeff) (p : Point) : ℝ :=
  f ((delta, c p.2), p)

theorem realize_radial_derivative {f : Raw → ℝ} (hf : ContDiff ℝ ∞ f)
    (delta : ℝ) (c : ℝ → Coeff) (p : Point) (dc : Coeff) :
    deriv (fun y => realize f delta c (y, p.2)) p.1 =
      radialJet f ((delta, (c p.2, dc)), p) :=
  (radialJet_hasDerivAt hf (delta, (c p.2, dc)) p).deriv

theorem realize_parameter_derivative {f : Raw → ℝ} (hf : ContDiff ℝ ∞ f)
    (delta : ℝ) {c : ℝ → Coeff}
    (hc : ContDiffOn ℝ ∞ c HeatedOutgoing.parameterDomain)
    {p : Point} (hp : p.2 ∈ HeatedOutgoing.parameterDomain) :
    derivWithin (fun eta => realize f delta c (p.1, eta)) HeatedOutgoing.parameterDomain p.2 =
      parameterJet f ((delta, (c p.2, derivWithin c HeatedOutgoing.parameterDomain p.2)), p) := by
  exact (parameterJet_hasDerivWithinAt hf
    ((hc.differentiableOn (by simp) p.2 hp).hasDerivWithinAt) delta p.1).derivWithin
      (uniqueDiffOn_Icc (by norm_num) p.2 hp)

/-- The actual angular velocity in the fixed logarithmic coordinate. -/
noncomputable def logE (F : Profile) (XR : ℝ) (c : ℝ → Coeff) (p : Point) : ℝ :=
  HeatedOutgoing.E F XR c (XR * Real.exp p.1, p.2)

/-- Incoming histories are retained. Only the integrals of the actual
changes beginning at the reserved patch are added. -/
noncomputable def logI (F : Profile) (XR : ℝ) (c : ℝ → Coeff) (p : Point) : ℝ :=
  OutgoingHistories.I F.reset p + ∫ t in OutgoingDilation.patchClock F..p.1,
    Real.exp (3 * t / 2) * (logE F XR c (t, p.2) - F.logE (t, p.2))

noncomputable def logS (F : Profile) (XR : ℝ) (c : ℝ → Coeff) (p : Point) : ℝ :=
  OutgoingHistories.S F.reset F.amp p - (1 / 2 : ℝ) *
    ∫ t in OutgoingDilation.patchClock F..p.1,
      Real.exp t * (logE F XR c (t, p.2) ^ 2 - F.logE (t, p.2) ^ 2)

noncomputable def logPi (F : Profile) (XR : ℝ) (c : ℝ → Coeff) (p : Point) : ℝ :=
  OutgoingHistories.Pi F.reset p + (1 / 2 : ℝ) *
    ∫ t in OutgoingDilation.patchClock F..p.1,
      logE F XR c (t, p.2) ^ 2 - F.logE (t, p.2) ^ 2

theorem logE_eq_realize (F : Profile) (XR : ℝ) (c : ℝ → Coeff) (hXR : 0 < XR)
    (p : Point) (hp : p.2 ∈ HeatedOutgoing.parameterDomain) :
    logE F XR c p = realize (freeE F) (1 / XR) c p :=
  (freeE_eq_physical F XR c hXR p.1 p.2 hp).symm

theorem logI_eq_realize (F : Profile) (XR : ℝ) (c : ℝ → Coeff) (hXR : 0 < XR)
    (p : Point) (hp : p.2 ∈ HeatedOutgoing.parameterDomain) :
    logI F XR c p = realize (freeI F) (1 / XR) c p := by
  unfold logI realize freeI finitePrefix
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [logE_eq_realize F XR c hXR (t, p.2) hp]
  rfl

theorem logS_eq_realize (F : Profile) (XR : ℝ) (c : ℝ → Coeff) (hXR : 0 < XR)
    (p : Point) (hp : p.2 ∈ HeatedOutgoing.parameterDomain) :
    logS F XR c p = realize (freeS F) (1 / XR) c p := by
  unfold logS realize freeS finitePrefix
  congr 2
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [logE_eq_realize F XR c hXR (t, p.2) hp]
  rfl

theorem logPi_eq_realize (F : Profile) (XR : ℝ) (c : ℝ → Coeff) (hXR : 0 < XR)
    (p : Point) (hp : p.2 ∈ HeatedOutgoing.parameterDomain) :
    logPi F XR c p = realize (freePi F) (1 / XR) c p := by
  unfold logPi realize freePi finitePrefix
  congr 2
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [logE_eq_realize F XR c hXR (t, p.2) hp]
  rfl

theorem logE_before_patch (F : Profile) {XR : ℝ} (hXR : 0 < XR) (c : ℝ → Coeff)
    {p : Point} (hp : p.1 ≤ OutgoingDilation.patchClock F) : logE F XR c p = F.logE p := by
  rw [logE, HeatedOutgoing.E_before_patch F XR c p.2 (XR * Real.exp p.1) hXR
    (mul_pos hXR (Real.exp_pos _))]
  · simp only [OutgoingDilation.E, OutgoingProfile.Profile.E,
      mul_div_cancel_left₀ _ hXR.ne', Real.log_exp, Prod.mk.eta]
  · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hp) hXR.le

theorem logE_parameter_derivative (F : Profile) {XR C : ℝ}
    (w : HeatedOutgoing.CompensationWitness F XR C) {p : Point}
    (hp : p.2 ∈ HeatedOutgoing.parameterDomain) :
    derivWithin (fun eta => logE F XR w.coefficients (p.1, eta))
      HeatedOutgoing.parameterDomain p.2 = parameterJet (freeE F) (controls F w p.2, p) := by
  rw [derivWithin_congr (fun eta heta => logE_eq_realize F XR w.coefficients w.radius_pos
    (p.1, eta) heta) (logE_eq_realize F XR w.coefficients w.radius_pos p hp)]
  exact realize_parameter_derivative (freeE_contDiff F) _ w.smooth hp

theorem logI_parameter_derivative (F : Profile) {XR C : ℝ}
    (w : HeatedOutgoing.CompensationWitness F XR C) {p : Point}
    (hp : p.2 ∈ HeatedOutgoing.parameterDomain) :
    derivWithin (fun eta => logI F XR w.coefficients (p.1, eta))
      HeatedOutgoing.parameterDomain p.2 = parameterJet (freeI F) (controls F w p.2, p) := by
  rw [derivWithin_congr (fun eta heta => logI_eq_realize F XR w.coefficients w.radius_pos
    (p.1, eta) heta) (logI_eq_realize F XR w.coefficients w.radius_pos p hp)]
  exact realize_parameter_derivative (freeI_contDiff F) _ w.smooth hp

theorem logS_parameter_derivative (F : Profile) {XR C : ℝ}
    (w : HeatedOutgoing.CompensationWitness F XR C) {p : Point}
    (hp : p.2 ∈ HeatedOutgoing.parameterDomain) :
    derivWithin (fun eta => logS F XR w.coefficients (p.1, eta))
      HeatedOutgoing.parameterDomain p.2 = parameterJet (freeS F) (controls F w p.2, p) := by
  rw [derivWithin_congr (fun eta heta => logS_eq_realize F XR w.coefficients w.radius_pos
    (p.1, eta) heta) (logS_eq_realize F XR w.coefficients w.radius_pos p hp)]
  exact realize_parameter_derivative (freeS_contDiff F) _ w.smooth hp

theorem logPi_parameter_derivative (F : Profile) {XR C : ℝ}
    (w : HeatedOutgoing.CompensationWitness F XR C) {p : Point}
    (hp : p.2 ∈ HeatedOutgoing.parameterDomain) :
    derivWithin (fun eta => logPi F XR w.coefficients (p.1, eta))
      HeatedOutgoing.parameterDomain p.2 = parameterJet (freePi F) (controls F w p.2, p) := by
  rw [derivWithin_congr (fun eta heta => logPi_eq_realize F XR w.coefficients w.radius_pos
    (p.1, eta) heta) (logPi_eq_realize F XR w.coefficients w.radius_pos p hp)]
  exact realize_parameter_derivative (freePi_contDiff F) _ w.smooth hp

theorem logE_radial_derivative (F : Profile) {XR C : ℝ}
    (w : HeatedOutgoing.CompensationWitness F XR C) {p : Point}
    (hp : p.2 ∈ HeatedOutgoing.parameterDomain) :
    deriv (fun y => logE F XR w.coefficients (y, p.2)) p.1 =
      radialJet (freeE F) (controls F w p.2, p) := by
  have he : (fun y => logE F XR w.coefficients (y, p.2)) =
      (fun y => realize (freeE F) (1 / XR) w.coefficients (y, p.2)) :=
    funext (fun y => logE_eq_realize F XR w.coefficients w.radius_pos (y, p.2) hp)
  rw [he]
  exact realize_radial_derivative (freeE_contDiff F) _ _ _ _

theorem zero_regular (F : Profile) {anchor left : ℝ}
    (h : OutgoingCone.CleanOutgoingCone F.reset anchor left) (ha : 0 < anchor)
    {p : Point} (hp : p ∈ OutgoingCone.trueWindow F.data) : (0, p) ∈ regular F := by
  have hm := OutgoingCone.clean_true_source_positive F.reset h ha hp
  have he : value (freeE F) (0, p) = F.logE p := freeE_zero F p
  refine ⟨by rw [he]; exact (OutgoingHistories.E_pos F.reset p).ne', ?_, ?_⟩
  · intro hn
    have hz : familyQ F (0, p) = 0 := by simp only [familyQ, hn, zero_div]
    rw [familyQ_zero] at hz
    exact hm.1.ne' hz
  · intro hn
    have hz : familyA F (0, p) = 0 := by simp only [familyA, hn, zero_div]
    rw [familyA_zero] at hz
    exact hm.2.1.ne' hz

/-- Values, all first jets needed in (9), both lags, and all normalized
stress coordinates. The last coordinate is the leading strict cone gap. -/
noncomputable def observations (F : Profile) (z : Control × Point) : Fin 18 → ℝ :=
  ![value (freeE F) z, radialJet (freeE F) z, parameterJet (freeE F) z,
    value (freeI F) z, parameterJet (freeI F) z,
    value (freeS F) z, parameterJet (freeS F) z,
    value (freePi F) z, parameterJet (freePi F) z,
    familyQ F z, familyN F z, familyA F z, familyB F z, familyR F z,
    familyC F z, familyJ F z, familyV F z, familyGap F z]

theorem observations_contDiffOn (F : Profile) :
    ContDiffOn ℝ ∞ (observations F) (regular F) := by
  apply contDiffOn_pi.mpr
  intro i
  fin_cases i <;> dsimp only [observations, Matrix.cons_val_zero, Matrix.cons_val_succ]
  · exact (value_contDiff (freeE_contDiff F)).contDiffOn
  · exact (radialJet_contDiff (freeE_contDiff F)).contDiffOn
  · exact (parameterJet_contDiff (freeE_contDiff F)).contDiffOn
  · exact (value_contDiff (freeI_contDiff F)).contDiffOn
  · exact (parameterJet_contDiff (freeI_contDiff F)).contDiffOn
  · exact (value_contDiff (freeS_contDiff F)).contDiffOn
  · exact (parameterJet_contDiff (freeS_contDiff F)).contDiffOn
  · exact (value_contDiff (freePi_contDiff F)).contDiffOn
  · exact (parameterJet_contDiff (freePi_contDiff F)).contDiffOn
  · exact familyQ_contDiffOn F
  · exact (familyN_contDiff F).contDiffOn
  · exact familyA_contDiffOn F
  · exact familyB_contDiffOn F
  · exact familyR_contDiffOn F
  · exact familyC_contDiffOn F
  · exact familyJ_contDiffOn F
  · exact familyV_contDiffOn F
  · exact familyGap_contDiffOn F

theorem observations_estimate (F : Profile) {anchor left : ℝ}
    (h : OutgoingCone.CleanOutgoingCone F.reset anchor left) (ha : 0 < anchor) :
    ∃ r L : ℝ, 0 < r ∧ 0 ≤ L ∧ ∀ v : Control, ‖v‖ ≤ r →
      ∀ p ∈ OutgoingCone.trueWindow F.data, (v, p) ∈ regular F ∧
        ‖observations F (v, p) - observations F (0, p)‖ ≤ L * ‖v‖ := by
  apply compact_control_estimate (isCompact_Icc.prod isCompact_Icc)
    ((convex_Icc _ _).prod (convex_Icc _ _)) (regular_isOpen F)
  · rintro ⟨v, p⟩ ⟨hv, hp⟩
    have hv' : v = 0 := hv
    subst v
    exact zero_regular F h ha hp
  · exact observations_contDiffOn F

/-- A single constant controls the actual value, radial and parameter jets,
histories, lags and normalized stresses. It is fixed before `XR` or the
particular compensation witness at that radius is chosen. -/
theorem compensated_observations_bound (F : Profile) {anchor left : ℝ}
    (h : OutgoingCone.CleanOutgoingCone F.reset anchor left) (ha : 0 < anchor) (C : ℝ) :
    ∃ XR₀ B : ℝ, 0 < XR₀ ∧ 0 < B ∧ ∀ XR : ℝ, XR₀ ≤ XR →
      ∀ w : HeatedOutgoing.CompensationWitness F XR C,
      ∀ p ∈ OutgoingCone.trueWindow F.data,
        (controls F w p.2, p) ∈ regular F ∧ ∀ i : Fin 18,
          |observations F (controls F w p.2, p) i - observations F (0, p) i| ≤
            B / OutgoingDilation.switchRadius F XR := by
  obtain ⟨r, L, hr, hL, he⟩ := observations_estimate F h ha
  let k := Real.exp (HeatTailEdit.switchStart F.data)
  let D := max k C
  have hk : 0 < k := Real.exp_pos _
  have hD : 0 < D := hk.trans_le (le_max_left _ _)
  let XR₀ := D / (r * k)
  let B := max 1 (L * D)
  refine ⟨XR₀, B, div_pos hD (mul_pos hr hk), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro XR hXR w p hp
  have hK := OutgoingDilation.switchRadius_pos F XR w.radius_pos
  have hsmall : D / OutgoingDilation.switchRadius F XR ≤ r := by
    apply (div_le_iff₀ hK).mpr
    have hh := (div_le_iff₀ (mul_pos hr hk)).mp hXR
    change D ≤ r * (XR * k)
    nlinarith only [hh]
  have hnorm := controls_norm F w hp.2
  have hob := he (controls F w p.2) (hnorm.trans hsmall) p hp
  refine ⟨hob.1, ?_⟩
  intro i
  calc
    |observations F (controls F w p.2, p) i - observations F (0, p) i| ≤
        ‖observations F (controls F w p.2, p) - observations F (0, p)‖ := by
      simpa only [Real.norm_eq_abs, Pi.sub_apply] using
        (norm_le_pi_norm (observations F (controls F w p.2, p) - observations F (0, p)) i)
    _ ≤ L * ‖controls F w p.2‖ := hob.2
    _ ≤ L * (D / OutgoingDilation.switchRadius F XR) := mul_le_mul_of_nonneg_left hnorm hL
    _ = (L * D) / OutgoingDilation.switchRadius F XR := by ring
    _ ≤ B / OutgoingDilation.switchRadius F XR :=
      (div_le_div_iff_of_pos_right hK).mpr (le_max_right _ _)

theorem cleanPi_eq (F : Profile) (p : Point) :
    F.logPi p = OutgoingHistories.Pi F.reset p := by
  rcases p with ⟨y, eta⟩
  rw [OutgoingHistories.Pi_eq_future_integral]
  rfl

theorem cleanPi_increment (F : Profile) (a y eta : ℝ) :
    (1 / 2 : ℝ) * ∫ t in a..y, F.logE (t, eta) ^ 2 =
      OutgoingHistories.Pi F.reset (y, eta) - OutgoingHistories.Pi F.reset (a, eta) := by
  have hc : Continuous (fun t => F.logE (t, eta) ^ 2 / 2) :=
    ((F.logE_contDiff.continuous.comp (continuous_id.prodMk continuous_const)).pow 2).div_const 2
  have hd (t : ℝ) : HasDerivAt (fun y => OutgoingHistories.Pi F.reset (y, eta))
      (F.logE (t, eta) ^ 2 / 2) t := OutgoingHistories.Pi_hasDerivAt F.reset (t, eta)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := a) (b := y)
    (fun t _ => hd t) (hc.intervalIntegrable a y)
  change (∫ t in a..y, F.logE (t, eta) ^ 2 / 2) = _ at hi
  rw [intervalIntegral.integral_div] at hi
  linarith

/-- The pressure in the normalized histories is the actual canonical future
integral. The proof uses exact three-row compensation through the existing
pressure primitive, not an independently chosen pressure constant. -/
theorem logPi_eq_canonical (F : Profile) {XR C : ℝ}
    (w : HeatedOutgoing.CompensationWitness F XR C) (p : Point)
    (hp : p.2 ∈ HeatedOutgoing.parameterDomain) :
    logPi F XR w.coefficients p =
      HeatedOutgoing.Pi F XR w.coefficients (XR * Real.exp p.1, p.2) := by
  let a := OutgoingDilation.patchClock F
  have hh := w.Pi_exp_primitive p.2 (Real.log XR + p.1) hp
  have hlog : Real.log (OutgoingDilation.patchRadius F XR) = Real.log XR + a := by
    rw [OutgoingDilation.patchRadius, OutgoingDilation.radius, Real.log_mul w.radius_pos.ne'
      (Real.exp_ne_zero _), Real.log_exp]
  have hbase : OutgoingDilation.Pi F XR (OutgoingDilation.patchRadius F XR, p.2) =
      OutgoingHistories.Pi F.reset (a, p.2) := by
    unfold OutgoingDilation.Pi OutgoingDilation.patchRadius OutgoingDilation.radius
    simp only [mul_div_cancel_left₀ _ w.radius_pos.ne', OutgoingProfile.Profile.Pi, Real.log_exp]
    exact cleanPi_eq F (a, p.2)
  rw [Real.exp_add, Real.exp_log w.radius_pos, hlog, hbase] at hh
  have hs : (∫ t in (Real.log XR + a)..(Real.log XR + p.1),
      HeatedOutgoing.freeLogE F XR ((w.coefficients p.2, p.2), t) ^ 2) =
      ∫ t in a..p.1, logE F XR w.coefficients (t, p.2) ^ 2 := by
    rw [← intervalIntegral.integral_comp_add_left
      (fun t => HeatedOutgoing.freeLogE F XR ((w.coefficients p.2, p.2), t) ^ 2) (Real.log XR)]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    rw [HeatedOutgoing.freeLogE_eq F XR w.coefficients p.2 _ hp,
      Real.exp_add, Real.exp_log w.radius_pos]
    rfl
  rw [hs] at hh
  have hclean := cleanPi_increment F a p.1 p.2
  have hheated : Continuous (fun t => logE F XR w.coefficients (t, p.2) ^ 2) := by
    have hg : Continuous (fun t => freeE F ((1 / XR, w.coefficients p.2), (t, p.2))) :=
      (freeE_contDiff F).continuous.comp (continuous_const.prodMk
        (continuous_id.prodMk continuous_const))
    have he : (fun t => logE F XR w.coefficients (t, p.2)) =
        (fun t => freeE F ((1 / XR, w.coefficients p.2), (t, p.2))) := by
      funext t
      exact logE_eq_realize F XR w.coefficients w.radius_pos (t, p.2) hp
    have h0 : Continuous (fun t => logE F XR w.coefficients (t, p.2)) := he.symm ▸ hg
    exact h0.pow 2
  have hcleanc : Continuous (fun t => F.logE (t, p.2) ^ 2) :=
    (F.logE_contDiff.continuous.comp (continuous_id.prodMk continuous_const)).pow 2
  unfold logPi
  rw [intervalIntegral.integral_sub (hheated.intervalIntegrable _ _) (hcleanc.intervalIntegrable _
    _)]
  dsimp only [a] at hh hclean
  linarith

noncomputable def Qs (F : Profile) (XR : ℝ) (c : ℝ → Coeff) (p : Point) : ℝ :=
  -OutgoingHistories.W F.data F.amp p +
    ((1 - F.data.h) * logI F XR c p - axialExponent F.data.h * p.2 *
      derivWithin (fun eta => logI F XR c (p.1, eta)) HeatedOutgoing.parameterDomain p.2 -
      coordinateFactor p.2 * OutgoingHistories.dEta (OutgoingHistories.J F.reset F.amp) p +
      2 * (F.data.h - axialExponent F.data.h) * p.2 * OutgoingHistories.J F.reset F.amp p) /
        (Real.exp (3 * p.1 / 2) * logE F XR c p)

noncomputable def Ns (F : Profile) (XR : ℝ) (c : ℝ → Coeff) (p : Point) : ℝ :=
  -OutgoingHistories.W F.data F.amp p * F.logU p +
    axialExponent F.data.h * (OutgoingHistories.M F.data F.amp p -
      p.2 * OutgoingHistories.dEta (OutgoingHistories.M F.data F.amp) p) / Real.exp p.1 +
    (4 * F.data.h * p.2 * logS F XR c p - coordinateFactor p.2 *
      derivWithin (fun eta => logS F XR c (p.1, eta)) HeatedOutgoing.parameterDomain p.2) /
        Real.exp p.1 + 4 * velocityExponent F.data.h * p.2 * logPi F XR c p -
      coordinateFactor p.2 * derivWithin (fun eta => logPi F XR c (p.1, eta))
        HeatedOutgoing.parameterDomain p.2

noncomputable def radialA (F : Profile) (XR : ℝ) (c : ℝ → Coeff) (p : Point) : ℝ :=
  1 - 2 * deriv (fun y => logE F XR c (y, p.2)) p.1 / logE F XR c p
noncomputable def radialB (F : Profile) (XR : ℝ) (c : ℝ → Coeff) (p : Point) : ℝ :=
  2 * OutgoingHistories.dY F.logU p / logE F XR c p
noncomputable def ratio (F : Profile) (XR : ℝ) (c : ℝ → Coeff) (p : Point) : ℝ :=
  Ns F XR c p / (logE F XR c p * Qs F XR c p)
noncomputable def sourceC (F : Profile) (XR : ℝ) (c : ℝ → Coeff) (p : Point) : ℝ :=
  1 - radialB F XR c p * ratio F XR c p / radialA F XR c p
noncomputable def sourceJ (F : Profile) (XR : ℝ) (c : ℝ → Coeff) (p : Point) : ℝ :=
  ratio F XR c p + radialB F XR c p / radialA F XR c p
noncomputable def normalV (F : Profile) (XR : ℝ) (c : ℝ → Coeff) (p : Point) : ℝ :=
  radialA F XR c p * (1 + (radialB F XR c p / radialA F XR c p) ^ 2)
noncomputable def leadingGap (F : Profile) (XR : ℝ) (c : ℝ → Coeff) (p : Point) : ℝ :=
  2 * sourceC F XR c p ^ 2 - (normalV F XR c p - 2) * sourceJ F XR c p ^ 2

theorem Qs_eq_family (F : Profile) {XR C : ℝ} (w : HeatedOutgoing.CompensationWitness F XR C)
    {p : Point} (hp : p.2 ∈ HeatedOutgoing.parameterDomain) :
    Qs F XR w.coefficients p = familyQ F (controls F w p.2, p) := by
  have hE := w.positive p.2 (XR * Real.exp p.1) hp (mul_pos w.radius_pos (Real.exp_pos _))
  change 0 < logE F XR w.coefficients p at hE
  rw [logE_eq_realize F XR w.coefficients w.radius_pos p hp] at hE
  rw [Qs, logI_parameter_derivative F w hp, logI_eq_realize F XR w.coefficients w.radius_pos p hp,
    logE_eq_realize F XR w.coefficients w.radius_pos p hp]
  unfold familyQ angularNumerator
  change -OutgoingHistories.W F.data F.amp p + _ / _ = _
  have hne : value (freeE F) (controls F w p.2, p) ≠ 0 := hE.ne'
  change 0 < value (freeE F) (controls F w p.2, p) at hE
  change -OutgoingHistories.W F.data F.amp p + _ /
    (Real.exp (3 * p.1 / 2) * value (freeE F) (controls F w p.2, p)) = _
  rw [show realize (freeI F) (1 / XR) w.coefficients p =
    value (freeI F) (controls F w p.2, p) from rfl]
  field_simp [hne, Real.exp_ne_zero]

theorem Ns_eq_family (F : Profile) {XR C : ℝ} (w : HeatedOutgoing.CompensationWitness F XR C)
    {p : Point} (hp : p.2 ∈ HeatedOutgoing.parameterDomain) :
    Ns F XR w.coefficients p = familyN F (controls F w p.2, p) := by
  rw [Ns, logS_parameter_derivative F w hp, logPi_parameter_derivative F w hp,
    logS_eq_realize F XR w.coefficients w.radius_pos p hp,
    logPi_eq_realize F XR w.coefficients w.radius_pos p hp]
  rfl

theorem radialA_eq_family (F : Profile) {XR C : ℝ} (w : HeatedOutgoing.CompensationWitness F XR C)
    {p : Point} (hp : p.2 ∈ HeatedOutgoing.parameterDomain) :
    radialA F XR w.coefficients p = familyA F (controls F w p.2, p) := by
  have hE := w.positive p.2 (XR * Real.exp p.1) hp (mul_pos w.radius_pos (Real.exp_pos _))
  change 0 < logE F XR w.coefficients p at hE
  rw [logE_eq_realize F XR w.coefficients w.radius_pos p hp] at hE
  rw [radialA, logE_radial_derivative F w hp,
    logE_eq_realize F XR w.coefficients w.radius_pos p hp]
  change 1 - 2 * radialJet (freeE F) (controls F w p.2, p) /
    value (freeE F) (controls F w p.2, p) = _
  unfold familyA radialNumerator
  have hne : value (freeE F) (controls F w p.2, p) ≠ 0 := hE.ne'
  field_simp [hne]

theorem normalized_eq_family (F : Profile) {XR C : ℝ}
    (w : HeatedOutgoing.CompensationWitness F XR C) {p : Point}
    (hp : p.2 ∈ HeatedOutgoing.parameterDomain) :
    radialB F XR w.coefficients p = familyB F (controls F w p.2, p) ∧
    ratio F XR w.coefficients p = familyR F (controls F w p.2, p) ∧
    sourceC F XR w.coefficients p = familyC F (controls F w p.2, p) ∧
    sourceJ F XR w.coefficients p = familyJ F (controls F w p.2, p) ∧
    normalV F XR w.coefficients p = familyV F (controls F w p.2, p) ∧
    leadingGap F XR w.coefficients p = familyGap F (controls F w p.2, p) := by
  have hb : radialB F XR w.coefficients p = familyB F (controls F w p.2, p) := by
    rw [radialB, logE_eq_realize F XR w.coefficients w.radius_pos p hp]
    rfl
  have hr : ratio F XR w.coefficients p = familyR F (controls F w p.2, p) := by
    rw [ratio, Ns_eq_family F w hp, Qs_eq_family F w hp,
      logE_eq_realize F XR w.coefficients w.radius_pos p hp]
    rfl
  have hc : sourceC F XR w.coefficients p = familyC F (controls F w p.2, p) := by
    rw [sourceC, hb, hr, radialA_eq_family F w hp]
    rfl
  have hj : sourceJ F XR w.coefficients p = familyJ F (controls F w p.2, p) := by
    rw [sourceJ, hb, hr, radialA_eq_family F w hp]
    rfl
  have hv : normalV F XR w.coefficients p = familyV F (controls F w p.2, p) := by
    rw [normalV, hb, radialA_eq_family F w hp]
    rfl
  refine ⟨hb, hr, hc, hj, hv, ?_⟩
  rw [leadingGap, hc, hj, hv]
  rfl

noncomputable def actualObservations (F : Profile) (XR : ℝ) (c : ℝ → Coeff)
    (p : Point) : Fin 18 → ℝ :=
  ![logE F XR c p, deriv (fun y => logE F XR c (y, p.2)) p.1,
    derivWithin (fun eta => logE F XR c (p.1, eta)) HeatedOutgoing.parameterDomain p.2,
    logI F XR c p,
    derivWithin (fun eta => logI F XR c (p.1, eta)) HeatedOutgoing.parameterDomain p.2,
    logS F XR c p,
    derivWithin (fun eta => logS F XR c (p.1, eta)) HeatedOutgoing.parameterDomain p.2,
    logPi F XR c p,
    derivWithin (fun eta => logPi F XR c (p.1, eta)) HeatedOutgoing.parameterDomain p.2,
    Qs F XR c p, Ns F XR c p, radialA F XR c p, radialB F XR c p, ratio F XR c p,
    sourceC F XR c p, sourceJ F XR c p, normalV F XR c p, leadingGap F XR c p]

theorem actualObservations_eq (F : Profile) {XR C : ℝ}
    (w : HeatedOutgoing.CompensationWitness F XR C) {p : Point}
    (hp : p.2 ∈ HeatedOutgoing.parameterDomain) :
    actualObservations F XR w.coefficients p = observations F (controls F w p.2, p) := by
  obtain ⟨hb, hr, hc, hj, hv, hg⟩ := normalized_eq_family F w hp
  unfold actualObservations observations
  rw [logE_radial_derivative F w hp, logE_parameter_derivative F w hp,
    logI_parameter_derivative F w hp, logS_parameter_derivative F w hp,
    logPi_parameter_derivative F w hp, Qs_eq_family F w hp, Ns_eq_family F w hp,
    radialA_eq_family F w hp, hb, hr, hc, hj, hv, hg,
    logE_eq_realize F XR w.coefficients w.radius_pos p hp,
    logI_eq_realize F XR w.coefficients w.radius_pos p hp,
    logS_eq_realize F XR w.coefficients w.radius_pos p hp,
    logPi_eq_realize F XR w.coefficients w.radius_pos p hp]
  rfl

theorem actual_observations_bound (F : Profile) {anchor left : ℝ}
    (h : OutgoingCone.CleanOutgoingCone F.reset anchor left) (ha : 0 < anchor) (C : ℝ) :
    ∃ XR₀ B : ℝ, 0 < XR₀ ∧ 0 < B ∧ ∀ XR : ℝ, XR₀ ≤ XR →
      ∀ w : HeatedOutgoing.CompensationWitness F XR C,
      ∀ p ∈ OutgoingCone.trueWindow F.data, ∀ i : Fin 18,
        |actualObservations F XR w.coefficients p i - observations F (0, p) i| ≤
          B / OutgoingDilation.switchRadius F XR := by
  obtain ⟨XR₀, B, hXR₀, hB, he⟩ := compensated_observations_bound F h ha C
  refine ⟨XR₀, B, hXR₀, hB, ?_⟩
  intro XR hXR w p hp i
  rw [actualObservations_eq F w hp.2]
  exact (he XR hXR w p hp).2 i

theorem div_switch_le (F : Profile) {B eps XR : ℝ} (heps : 0 < eps) (hXR : 0 < XR)
    (hlarge : B / (eps * Real.exp (HeatTailEdit.switchStart F.data)) ≤ XR) :
    B / OutgoingDilation.switchRadius F XR ≤ eps := by
  apply (div_le_iff₀ (OutgoingDilation.switchRadius_pos F XR hXR)).mpr
  have hh := (div_le_iff₀ (mul_pos heps (Real.exp_pos _))).mp hlarge
  change B ≤ eps * (XR * Real.exp (HeatTailEdit.switchStart F.data))
  nlinarith only [hh]

/-- Uniform strict source margins for every sufficiently large physical
radius, with a bound for the two coordinates entering the finite-radius
quadratic test. All constants precede the radius and witness quantifiers. -/
theorem compensated_source_margins (F : Profile) {anchor left : ℝ}
    (h : OutgoingCone.CleanOutgoingCone F.reset anchor left) (ha : 0 < anchor) (C : ℝ) :
    ∃ XR₀ m T : ℝ, 0 < XR₀ ∧ 0 < m ∧ 0 < T ∧ ∀ XR : ℝ, XR₀ ≤ XR →
      ∀ w : HeatedOutgoing.CompensationWitness F XR C,
      ∀ p ∈ OutgoingCone.trueWindow F.data,
        m ≤ Qs F XR w.coefficients p ∧ m ≤ radialA F XR w.coefficients p ∧
        m ≤ normalV F XR w.coefficients p - 2 ∧ m ≤ sourceC F XR w.coefficients p ∧
        m ≤ leadingGap F XR w.coefficients p ∧
        |sourceC F XR w.coefficients p| ≤ T ∧ |normalV F XR w.coefficients p| ≤ T := by
  obtain ⟨X₀, B, hX₀, hB, hb⟩ := actual_observations_bound F h ha C
  obtain ⟨eps, heps, hm⟩ := OutgoingCone.clean_true_source_margins F.reset h ha
  have hc : ContinuousOn (fun p : Point => observations F (0, p))
      (OutgoingCone.trueWindow F.data) :=
    (observations_contDiffOn F).continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn (fun p hp => zero_regular F h ha hp)
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hc
  let err := min (eps / 2) 1
  have herr : 0 < err := lt_min (by positivity) zero_lt_one
  let X₁ := B / (err * Real.exp (HeatTailEdit.switchStart F.data))
  let T := max 1 (M + 1)
  refine ⟨max X₀ X₁, eps / 2, T, hX₀.trans_le (le_max_left _ _), by positivity,
    lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro XR hXR w p hp
  have he := hb XR ((le_max_left _ _).trans hXR) w p hp
  have hsmall := div_switch_le F herr w.radius_pos ((le_max_right _ _).trans hXR)
  have herrs : ∀ i : Fin 18,
      |actualObservations F XR w.coefficients p i - observations F (0, p) i| ≤ err :=
    fun i => (he i).trans hsmall
  have hq : |Qs F XR w.coefficients p - OutgoingHistories.Qs F.reset F.amp p| ≤ err := by
    simpa [actualObservations, observations] using herrs 9
  have ha' : |radialA F XR w.coefficients p - OutgoingEntranceCone.coneA F.reset p| ≤ err := by
    simpa [actualObservations, observations] using herrs 11
  have hv : |normalV F XR w.coefficients p - OutgoingCone.normalV F.reset F.amp p| ≤ err := by
    simpa [actualObservations, observations] using herrs 16
  have hc' : |sourceC F XR w.coefficients p - OutgoingCone.sourceC F.reset F.amp p| ≤ err := by
    simpa [actualObservations, observations] using herrs 14
  have hg : |leadingGap F XR w.coefficients p - OutgoingCone.leadingGap F.reset F.amp p| ≤ err := by
    simpa [actualObservations, observations] using herrs 17
  have hm' := hm p hp
  have herreps : err ≤ eps / 2 := min_le_left _ _
  have herrone : err ≤ 1 := min_le_right _ _
  have habs (i : Fin 18) : |observations F (0, p) i| ≤ M := by
    have hi := norm_le_pi_norm (observations F (0, p)) i
    exact hi.trans (hM p hp)
  have hCM : |OutgoingCone.sourceC F.reset F.amp p| ≤ M := by
    simpa [observations] using habs 14
  have hVM : |OutgoingCone.normalV F.reset F.amp p| ≤ M := by
    simpa [observations] using habs 16
  dsimp only [OutgoingProfile.Profile.amp] at hq hv hc' hg
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linarith [(abs_le.mp hq).1, hm'.1]
  · linarith [(abs_le.mp ha').1, hm'.2.1]
  · linarith [(abs_le.mp hv).1, hm'.2.2.1]
  · linarith [(abs_le.mp hc').1, hm'.2.2.2.1]
  · linarith [(abs_le.mp hg).1, hm'.2.2.2.2]
  · calc
      |sourceC F XR w.coefficients p| ≤
          |sourceC F XR w.coefficients p - OutgoingCone.sourceC F.reset F.amp p| +
          |OutgoingCone.sourceC F.reset F.amp p| := by
            simpa only [sub_add_cancel] using abs_add_le
              (sourceC F XR w.coefficients p - OutgoingCone.sourceC F.reset F.amp p)
              (OutgoingCone.sourceC F.reset F.amp p)
      _ ≤ err + M := add_le_add hc' hCM
      _ ≤ T := by dsimp [T]; linarith [le_max_right (1 : ℝ) (M + 1)]
  · calc
      |normalV F XR w.coefficients p| ≤
          |normalV F XR w.coefficients p - OutgoingCone.normalV F.reset F.amp p| +
          |OutgoingCone.normalV F.reset F.amp p| := by
            simpa only [sub_add_cancel] using abs_add_le
              (normalV F XR w.coefficients p - OutgoingCone.normalV F.reset F.amp p)
              (OutgoingCone.normalV F.reset F.amp p)
      _ ≤ err + M := add_le_add hv hVM
      _ ≤ T := by dsimp [T]; linarith [le_max_right (1 : ℝ) (M + 1)]

noncomputable def stressScale (F : Profile) (XR : ℝ) (c : ℝ → Coeff) (p : Point) : ℝ :=
  XR * Real.exp p.1 * Qs F XR c p / CoordinateAlgebra.L F.data.h p.2
noncomputable def normalP (F : Profile) (XR : ℝ) (c : ℝ → Coeff) (p : Point) : ℝ :=
  stressScale F XR c p * sourceC F XR c p
noncomputable def normalJ (F : Profile) (XR : ℝ) (c : ℝ → Coeff) (p : Point) : ℝ :=
  stressScale F XR c p * sourceJ F XR c p

/-- The strict true cone, expressed in the same normalized stress coordinates
as the clean outgoing theorem. -/
def TrueAt (F : Profile) (XR : ℝ) (c : ℝ → Coeff) (p : Point) : Prop :=
  0 < Qs F XR c p ∧ 0 < radialA F XR c p ∧ 2 < normalV F XR c p ∧
  2 < normalP F XR c p ∧ normalV F XR c p < ConeAlgebra.coneBound (normalP F XR c p) (normalJ F XR
    c p)

/-- Compensation and the full switch-on interval preserve the strict true
cone. The outgoing profile, its reset and its axial amplitude remain fixed.
The final radius threshold is uniform over all compensation witnesses having
the previously fixed coefficient constant `C`. -/
theorem preserves_true_cone (F : Profile) {anchor left : ℝ}
    (h : OutgoingCone.CleanOutgoingCone F.reset anchor left) (ha : 0 < anchor) (C : ℝ) :
    ∃ XR₀ : ℝ, 0 < XR₀ ∧ ∀ XR : ℝ, XR₀ ≤ XR →
      ∀ w : HeatedOutgoing.CompensationWitness F XR C,
      ∀ p ∈ OutgoingCone.trueWindow F.data, TrueAt F XR w.coefficients p := by
  obtain ⟨X₀, m, T, hX₀, hm, hT, hs⟩ := compensated_source_margins F h ha C
  let k := Real.exp F.data.core.holdStart
  have hk : 0 < k := Real.exp_pos _
  let B := 3 + T + 4 * T ^ 2
  let X₁ := B / (k * m ^ 2)
  refine ⟨max X₀ X₁, hX₀.trans_le (le_max_left _ _), ?_⟩
  intro XR hXR w p hp
  obtain ⟨hq, har, hv, hc, hg, hcT, hvT⟩ := hs XR ((le_max_left _ _).trans hXR) w p hp
  have hqpos := hm.trans_le hq
  have harpos := hm.trans_le har
  have hvpos : 2 < normalV F XR w.coefficients p := by linarith
  have hcpos := hm.trans_le hc
  have hL : 0 < CoordinateAlgebra.L F.data.h p.2 := CoordinateAlgebra.L_pos
    F.data.h_pos.le F.data.h_lt_half
    (OutgoingEntranceCone.parameter_square_le_one (abs_le.mpr hp.2))
  have hL1 : CoordinateAlgebra.L F.data.h p.2 ≤ 1 := by
    unfold CoordinateAlgebra.L
    nlinarith [mul_nonneg F.data.h_pos.le (sq_nonneg p.2)]
  have hscale : 0 < stressScale F XR w.coefficients p :=
    div_pos (mul_pos (mul_pos w.radius_pos (Real.exp_pos _)) hqpos) hL
  have hlow : XR * k * m ≤ stressScale F XR w.coefficients p := by
    apply (le_div_iff₀ hL).mpr
    have hnonneg : 0 ≤ XR * k * m := (mul_pos (mul_pos w.radius_pos hk) hm).le
    calc
      XR * k * m * CoordinateAlgebra.L F.data.h p.2 ≤ XR * k * m := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hL1 hnonneg
      _ ≤ XR * Real.exp p.1 * Qs F XR w.coefficients p := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hp.1.1) w.radius_pos.le
        · exact hq
        · exact hm.le
        · exact (mul_pos w.radius_pos (Real.exp_pos _)).le
  have hB : B ≤ stressScale F XR w.coefficients p * m := by
    have hh := (div_le_iff₀ (mul_pos hk (sq_pos_of_pos hm))).mp ((le_max_right _ _).trans hXR)
    calc
      B ≤ XR * (k * m ^ 2) := hh
      _ = (XR * k * m) * m := by ring
      _ ≤ stressScale F XR w.coefficients p * m := mul_le_mul_of_nonneg_right hlow hm.le
  have hpc : B ≤ normalP F XR w.coefficients p :=
    hB.trans (mul_le_mul_of_nonneg_left hc hscale.le)
  have hP : 2 < normalP F XR w.coefficients p := by
    dsimp [B] at hpc
    nlinarith [sq_nonneg T]
  have hvc : normalV F XR w.coefficients p < normalP F XR w.coefficients p := by
    have hvT' := (le_abs_self _).trans hvT
    dsimp [B] at hpc
    nlinarith [sq_nonneg T]
  have hquad : 4 * sourceC F XR w.coefficients p * normalV F XR w.coefficients p <
      stressScale F XR w.coefficients p * leadingGap F XR w.coefficients p := by
    have hpT : sourceC F XR w.coefficients p * normalV F XR w.coefficients p ≤ T ^ 2 := by
      have hh := mul_le_mul ((le_abs_self _).trans hcT) ((le_abs_self _).trans hvT)
        (by linarith : 0 ≤ normalV F XR w.coefficients p) hT.le
      simpa only [pow_two] using hh
    have hgap := hB.trans (mul_le_mul_of_nonneg_left hg hscale.le)
    dsimp [B] at hgap
    nlinarith
  refine ⟨hqpos, harpos, hvpos, hP, ?_⟩
  exact ConeAlgebra.finite_amplitude_cone hscale hP hvc hquad

/-- Existence uses the already constructed compensation branch for the same
outgoing profile, after taking the maximum of its threshold and the cone
threshold. -/
theorem exists_compensated_true_cone (F : Profile) {anchor left : ℝ}
    (h : OutgoingCone.CleanOutgoingCone F.reset anchor left) (ha : 0 < anchor) :
    ∃ XR₀ C : ℝ, 0 < XR₀ ∧ 0 < C ∧ ∀ XR : ℝ, XR₀ ≤ XR →
      ∃ w : HeatedOutgoing.CompensationWitness F XR C,
        ∀ p ∈ OutgoingCone.trueWindow F.data, TrueAt F XR w.coefficients p := by
  obtain ⟨X₀, C, hX₀, hC, hw⟩ := HeatedOutgoing.exists_compensation F
  obtain ⟨X₁, _, hc⟩ := preserves_true_cone F h ha C
  refine ⟨max X₀ X₁, C, hX₀.trans_le (le_max_left _ _), hC, ?_⟩
  intro XR hXR
  obtain ⟨w⟩ := hw XR ((le_max_left _ _).trans hXR)
  exact ⟨w, hc XR ((le_max_right _ _).trans hXR) w⟩

theorem past_integrable_from {f : ℝ → ℝ} (hf : Continuous f) {a : ℝ}
    (ha : IntegrableOn f (Iic a)) (y : ℝ) : IntegrableOn f (Iic y) := by
  by_cases h : a ≤ y
  · rw [← Iic_union_Ioc_eq_Iic h]
    exact ha.union hf.integrableOn_Ioc
  · exact ha.mono_set (Iic_subset_Iic.mpr (le_of_not_ge h))

/-- Updating an actual past integral by the finite integral of the change.
The two functions agree throughout their entire incoming history. -/
theorem past_integral_update {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    {a : ℝ} (ha : IntegrableOn f (Iic a)) (he : ∀ t ≤ a, g t = f t) (y : ℝ) :
    IntegrableOn g (Iic y) ∧ (∫ t in Iic y, g t) =
      (∫ t in Iic y, f t) + ∫ t in a..y, g t - f t := by
  have hga : IntegrableOn g (Iic a) :=
    ha.congr_fun (fun t ht => (he t ht).symm) measurableSet_Iic
  have hgy := past_integrable_from hg hga y
  have hfy := past_integrable_from hf ha y
  have hbase : (∫ t in Iic a, g t) = ∫ t in Iic a, f t :=
    setIntegral_congr_fun measurableSet_Iic (fun t ht => he t ht)
  have hfg := intervalIntegral.integral_Iic_sub_Iic ha hfy
  have hgg := intervalIntegral.integral_Iic_sub_Iic hga hgy
  refine ⟨hgy, ?_⟩
  rw [intervalIntegral.integral_sub (hg.intervalIntegrable a y) (hf.intervalIntegrable a y)]
  linarith

theorem logE_continuous_radial (F : Profile) {XR : ℝ} (hXR : 0 < XR)
    (c : ℝ → Coeff) {eta : ℝ} (heta : eta ∈ HeatedOutgoing.parameterDomain) :
    Continuous (fun y => logE F XR c (y, eta)) := by
  have hc : Continuous (fun y => freeE F ((1 / XR, c eta), (y, eta))) :=
    (freeE_contDiff F).continuous.comp (continuous_const.prodMk
      (continuous_id.prodMk continuous_const))
  exact hc.congr (fun y => (logE_eq_realize F XR c hXR (y, eta) heta).symm)

theorem logI_eq_past_integral (F : Profile) {XR : ℝ} (hXR : 0 < XR) (c : ℝ → Coeff)
    {eta : ℝ} (heta : eta ∈ HeatedOutgoing.parameterDomain) (y : ℝ) :
    IntegrableOn (fun t => Real.exp (3 * t / 2) * logE F XR c (t, eta)) (Iic y) ∧
    logI F XR c (y, eta) = ∫ t in Iic y, Real.exp (3 * t / 2) * logE F XR c (t, eta) := by
  let f : ℝ → ℝ := fun t => Real.exp (3 * t / 2) * F.logE (t, eta)
  let g : ℝ → ℝ := fun t => Real.exp (3 * t / 2) * logE F XR c (t, eta)
  have hex : Continuous (fun t : ℝ => Real.exp (3 * t / 2)) :=
    Real.continuous_exp.comp ((continuous_const.mul continuous_id).div_const 2)
  have hf : Continuous f := hex.mul
    (F.logE_contDiff.continuous.comp (continuous_id.prodMk continuous_const))
  have hg : Continuous g := hex.mul
    (logE_continuous_radial F hXR c heta)
  have hzero : IntegrableOn f (Iic (0 : ℝ)) := by
    have hh := (OutgoingHistories.angular_past F.reset eta).1
    simp only [OutgoingHistories.angularWeight_eq] at hh
    exact hh
  have hbefore : ∀ t ≤ OutgoingDilation.patchClock F, g t = f t := by
    intro t ht
    dsimp [f, g]
    rw [logE_before_patch F hXR c ht]
  have hh := past_integral_update hf hg
    (past_integrable_from hf hzero (OutgoingDilation.patchClock F)) hbefore y
  refine ⟨hh.1, ?_⟩
  rw [hh.2]
  unfold logI
  rw [OutgoingHistories.I_eq_integral]
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  dsimp [f, g]
  ring

theorem logS_eq_past_integral (F : Profile) {XR : ℝ} (hXR : 0 < XR) (c : ℝ → Coeff)
    {eta : ℝ} (heta : eta ∈ HeatedOutgoing.parameterDomain) (y : ℝ) :
    IntegrableOn (fun t => Real.exp t * (F.logU (t, eta) ^ 2 - logE F XR c (t, eta) ^ 2 / 2))
      (Iic y) ∧ logS F XR c (y, eta) =
        ∫ t in Iic y, Real.exp t * (F.logU (t, eta) ^ 2 - logE F XR c (t, eta) ^ 2 / 2) := by
  let f : ℝ → ℝ := fun t => Real.exp t * (F.logU (t, eta) ^ 2 - F.logE (t, eta) ^ 2 / 2)
  let g : ℝ → ℝ := fun t => Real.exp t * (F.logU (t, eta) ^ 2 - logE F XR c (t, eta) ^ 2 / 2)
  have hu := F.logU_contDiff.continuous.comp (continuous_id.prodMk (continuous_const : Continuous
    (fun _ : ℝ => eta)))
  have hf : Continuous f := Real.continuous_exp.mul ((hu.pow 2).sub
    (((F.logE_contDiff.continuous.comp (continuous_id.prodMk continuous_const)).pow 2).div_const 2))
  have hg : Continuous g := Real.continuous_exp.mul ((hu.pow 2).sub
    (((logE_continuous_radial F hXR c heta).pow 2).div_const 2))
  have hzero : IntegrableOn f (Iic (0 : ℝ)) := (OutgoingHistories.energy_past F.reset F.amp eta).1
  have hbefore : ∀ t ≤ OutgoingDilation.patchClock F, g t = f t := by
    intro t ht
    dsimp [f, g]
    rw [logE_before_patch F hXR c ht]
  have hh := past_integral_update hf hg
    (past_integrable_from hf hzero (OutgoingDilation.patchClock F)) hbefore y
  refine ⟨hh.1, ?_⟩
  rw [hh.2]
  unfold logS
  rw [OutgoingHistories.S_eq_integral F.reset F.amp_contDiff]
  have hi : (∫ t in OutgoingDilation.patchClock F..y, g t - f t) =
      -(1 / 2 : ℝ) * ∫ t in OutgoingDilation.patchClock F..y,
        Real.exp t * (logE F XR c (t, eta) ^ 2 - F.logE (t, eta) ^ 2) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp [f, g]
    ring
  rw [hi]
  change (∫ t in Iic y, f t) - _ = (∫ t in Iic y, f t) + _
  ring

theorem logE_mul_logU (F : Profile) {XR : ℝ} (hXR : 0 < XR) (c : ℝ → Coeff) (p : Point) :
    logE F XR c p * F.logU p = F.logE p * F.logU p := by
  have hh := HeatedOutgoing.E_times_U F XR c p.2 (XR * Real.exp p.1) hXR
    (mul_pos hXR (Real.exp_pos _))
  simpa only [logE, HeatedOutgoing.U, OutgoingDilation.U, OutgoingDilation.E,
    OutgoingProfile.Profile.U, OutgoingProfile.Profile.E, mul_div_cancel_left₀ _ hXR.ne',
    Real.log_exp, Prod.mk.eta] using hh

theorem J_eq_heated_past_integral (F : Profile) {XR : ℝ} (hXR : 0 < XR) (c : ℝ → Coeff)
    (y eta : ℝ) : OutgoingHistories.J F.reset F.amp (y, eta) =
      ∫ t in Iic y, Real.exp (3 * t / 2) * logE F XR c (t, eta) * F.logU (t, eta) := by
  rw [OutgoingHistories.J_eq_integral F.reset F.amp_contDiff]
  apply setIntegral_congr_fun measurableSet_Iic
  intro t _
  change Real.exp (3 * t / 2) * F.logE (t, eta) * F.logU (t, eta) = _
  dsimp only
  rw [mul_assoc, mul_assoc, logE_mul_logU F hXR c (t, eta)]

theorem changeRow_after_switch (F : Profile) {XR : ℝ} (hXR : 0 < XR) (c : ℝ → Coeff)
    (eta : ℝ) (i : Fin 3) {X : ℝ} (hX : OutgoingDilation.switchRadius F XR ≤ X) :
    HeatedOutgoing.changeRow F XR c eta i X = HeatedOutgoing.heatRow F XR eta i X := by
  have hpos := (OutgoingDilation.switchRadius_pos F XR hXR).trans_le hX
  rw [HeatedOutgoing.changeRow_decomposition F XR c eta i X hXR hpos]
  have hc := OutgoingDilation.correction_zero_after_switch F XR X hXR (c eta) hX
  have hz : HeatedOutgoing.patchRow F XR c eta i X = 0 := by
    fin_cases i <;> simp [HeatedOutgoing.patchRow, TerminalCompensation.physicalProfile,
      TerminalCompensation.cleanProfile, hc]
  rw [hz, add_zero]

/-- Exact restored total moments identify a finite-point change with the
remaining future heat debt. In particular finite histories do not become
equal merely because compensation is completed. -/
theorem changeRow_prefix_eq_neg_future_heat (F : Profile) {XR C : ℝ}
    (w : HeatedOutgoing.CompensationWitness F XR C) {eta : ℝ}
    (heta : eta ∈ HeatedOutgoing.parameterDomain) (i : Fin 3) {X : ℝ}
    (hX : OutgoingDilation.switchRadius F XR ≤ X) :
    (∫ t in Ioc 0 X, HeatedOutgoing.changeRow F XR w.coefficients eta i t) =
      -(∫ t in Ioi X, HeatedOutgoing.heatRow F XR eta i t) := by
  have hpos := (OutgoingDilation.switchRadius_pos F XR w.radius_pos).trans_le hX
  have hi := w.changeRow_integrable eta i heta
  have hsum := setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
    (hi.mono_set Ioc_subset_Ioi_self) (hi.mono_set (Ioi_subset_Ioi hpos.le))
  rw [Ioc_union_Ioi_eq_Ioi hpos.le, w.changeRow_integral_zero eta i heta] at hsum
  have htail : (∫ t in Ioi X, HeatedOutgoing.changeRow F XR w.coefficients eta i t) =
      ∫ t in Ioi X, HeatedOutgoing.heatRow F XR eta i t := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    exact changeRow_after_switch F w.radius_pos w.coefficients eta i (hX.trans ht.le)
  rw [htail] at hsum
  linarith

end NavierStokes.HeatSwitchCone
