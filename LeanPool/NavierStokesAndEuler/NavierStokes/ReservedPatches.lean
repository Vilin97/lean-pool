/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.HeatedOutgoing
public import LeanPool.NavierStokesAndEuler.NavierStokes.FiveProfileMoments

@[expose] public section

/-!
# Four disjoint reservations on the actual outgoing shaped wait

The log intervals are the four examples in the manuscript: (-25,-20),
(-20,-15), (-14,-9), and (-8,-3), relative to the pulse entrance.
The first is the five-row repair after radial modulation. The second is the
existing heat-compensation patch. The last two remain pure powers after that
heat correction. All fields below use the same outgoing profile.
-/

noncomputable section

open Set Filter Function MeasureTheory
open scoped ContDiff Topology BigOperators
open NavierStokes.OutgoingProfile (Profile)

namespace NavierStokes.ReservedPatches

inductive Slot where
  | modulation
  | heat
  | positive
  | mean
  deriving DecidableEq

noncomputable def leftOffset : Slot → ℝ
  | .modulation => -25
  | .heat => -20
  | .positive => -14
  | .mean => -8

noncomputable def rightOffset : Slot → ℝ
  | .modulation => -20
  | .heat => -15
  | .positive => -9
  | .mean => -3

theorem offset_width (s : Slot) : rightOffset s = leftOffset s + 5 := by
  cases s <;> norm_num [leftOffset, rightOffset]

theorem offset_bounds (s : Slot) :
    -25 ≤ leftOffset s ∧ leftOffset s < rightOffset s ∧ rightOffset s ≤ -3 := by
  cases s <;> norm_num [leftOffset, rightOffset]

theorem offsets_separated {s t : Slot} (hst : s ≠ t) :
    rightOffset s ≤ leftOffset t ∨ rightOffset t ≤ leftOffset s := by
  cases s <;> cases t <;> simp_all [leftOffset, rightOffset] <;> norm_num

noncomputable def leftClock (F : Profile) (s : Slot) : ℝ :=
  F.data.core.pulseStart + leftOffset s

noncomputable def rightClock (F : Profile) (s : Slot) : ℝ :=
  F.data.core.pulseStart + rightOffset s

noncomputable def left (F : Profile) (XR : ℝ) (s : Slot) : ℝ :=
  OutgoingDilation.radius XR (leftClock F s)

noncomputable def right (F : Profile) (XR : ℝ) (s : Slot) : ℝ :=
  OutgoingDilation.radius XR (rightClock F s)

noncomputable def window (F : Profile) (XR : ℝ) (s : Slot) : Set ℝ :=
  Ioo (left F XR s) (right F XR s)

theorem radius_strictMono (XR : ℝ) (hXR : 0 < XR) :
    StrictMono (OutgoingDilation.radius XR) := by
  intro a b hab
  exact mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr hab) hXR

theorem left_pos (F : Profile) (XR : ℝ) (hXR : 0 < XR) (s : Slot) :
    0 < left F XR s := OutgoingDilation.radius_pos XR _ hXR

theorem left_lt_right (F : Profile) (XR : ℝ) (hXR : 0 < XR) (s : Slot) :
    left F XR s < right F XR s := by
  apply radius_strictMono XR hXR
  exact add_lt_add_right (offset_bounds s).2.1 _

theorem right_pos (F : Profile) (XR : ℝ) (hXR : 0 < XR) (s : Slot) :
    0 < right F XR s := (left_pos F XR hXR s).trans (left_lt_right F XR hXR s)

theorem mem_window_pos (F : Profile) (XR : ℝ) (hXR : 0 < XR)
    (s : Slot) {X : ℝ} (hX : X ∈ window F XR s) : 0 < X :=
  (left_pos F XR hXR s).trans hX.1

theorem window_nonempty (F : Profile) (XR : ℝ) (hXR : 0 < XR) (s : Slot) :
    (window F XR s).Nonempty := nonempty_Ioo.mpr (left_lt_right F XR hXR s)

theorem windows_disjoint (F : Profile) (XR : ℝ) (hXR : 0 < XR)
    {s t : Slot} (hst : s ≠ t) : Disjoint (window F XR s) (window F XR t) := by
  apply Set.disjoint_left.mpr
  intro X hXs hXt
  rcases offsets_separated hst with h | h
  · have hr : right F XR s ≤ left F XR t :=
      (radius_strictMono XR hXR).monotone (add_le_add_right h _)
    exact (not_lt_of_ge hr) (hXt.1.trans hXs.2)
  · have hr : right F XR t ≤ left F XR s :=
      (radius_strictMono XR hXR).monotone (add_le_add_right h _)
    exact (not_lt_of_ge hr) (hXs.1.trans hXt.2)

theorem clock_bounds (F : Profile) (XR : ℝ) (hXR : 0 < XR) (s : Slot)
    {X : ℝ} (hX : X ∈ window F XR s) :
    leftClock F s < OutgoingDilation.clock XR X ∧
      OutgoingDilation.clock XR X < rightClock F s := by
  have hp := mem_window_pos F XR hXR s hX
  constructor
  · exact (OutgoingDilation.radius_lt_iff XR X _ hXR hp).mp hX.1
  · by_contra hn
    have hr := (OutgoingDilation.radius_le_iff XR X (rightClock F s) hXR hp).mpr
      (le_of_not_gt hn)
    exact (not_le_of_gt hX.2) hr

theorem clock_inside_wait (F : Profile) (s : Slot) :
    F.data.core.holdStart < leftClock F s ∧ rightClock F s < F.data.core.pulseStart := by
  obtain ⟨hlo, _, hhi⟩ := offset_bounds s
  dsimp only [leftClock, rightClock, OutgoingSchedule.Parameters.pulseStart]
  constructor <;> linarith [F.data.core.wait_gt]

theorem window_inside_wait (F : Profile) (XR : ℝ) (hXR : 0 < XR)
    (s : Slot) {X : ℝ} (hX : X ∈ window F XR s) :
    F.data.core.holdStart < OutgoingDilation.clock XR X ∧
      OutgoingDilation.clock XR X < F.data.core.pulseStart := by
  obtain ⟨hl, hr⟩ := clock_bounds F XR hXR s hX
  obtain ⟨hwl, hwr⟩ := clock_inside_wait F s
  exact ⟨hwl.trans hl, hr.trans hwr⟩

/-- An explicit small-lambda threshold for the canonical sixty-log wait. -/
theorem canonical_wait_gt_54 {lam : ℝ} (hlam : 0 < lam) (hlam' : lam < 1 / 10) :
    54 < 60 * Real.log (1 / lam) := by
  have h := Real.one_sub_inv_le_log_of_pos (one_div_pos.mpr hlam)
  simp only [one_div, inv_inv] at h ⊢
  nlinarith

/-- The earliest reserved boundary has over twenty-nine log units of
entrance margin. The latest boundary has three log units before the pulse. -/
theorem canonical_margins (F : Profile)
    (hw : F.data.core.wait = 60 * Real.log (1 / F.data.core.lam)) (s : Slot) :
    F.data.core.holdStart + 29 < leftClock F s ∧
      rightClock F s ≤ F.data.core.pulseStart - 3 := by
  have hwait := canonical_wait_gt_54 F.data.core.lam_pos F.data.core.lam_lt
  rw [← hw] at hwait
  obtain ⟨hlo, _, hhi⟩ := offset_bounds s
  dsimp only [leftClock, rightClock, OutgoingSchedule.Parameters.pulseStart]
  constructor <;> linarith

theorem pulse_before_switch (F : Profile) :
    F.data.core.pulseStart < HeatTailEdit.switchStart F.data := by
  have hp := F.data.core.pulseLength_pos
  have hf := OutgoingTail.flattenEnd_gt_core F.data
  have hr := OutgoingTail.releaseStart_gt_flattenEnd F.data
  have ht := OutgoingTail.tailStart_gt_release F.data
  dsimp only [OutgoingSchedule.Parameters.endpoint] at hf
  dsimp only [HeatTailEdit.switchStart]
  linarith

theorem right_before_switch (F : Profile) (XR : ℝ) (hXR : 0 < XR) (s : Slot) :
    right F XR s < OutgoingDilation.switchRadius F XR := by
  apply radius_strictMono XR hXR
  exact (clock_inside_wait F s).2.trans (pulse_before_switch F)

theorem heat_left (F : Profile) (XR : ℝ) :
    left F XR .heat = OutgoingDilation.patchRadius F XR := by
  simp only [left, leftClock, leftOffset, OutgoingDilation.patchRadius,
    OutgoingDilation.patchClock, sub_eq_add_neg]

theorem right_eq_left_mul_exp (F : Profile) (XR : ℝ) (s : Slot) :
    right F XR s = left F XR s * Real.exp 5 := by
  unfold right left OutgoingDilation.radius rightClock leftClock
  rw [offset_width, ← add_assoc, Real.exp_add]
  ring

theorem heat_right (F : Profile) (XR : ℝ) :
    right F XR .heat = OutgoingDilation.patchRadius F XR *
      OutgoingDilation.compensationPatch.right := by
  rw [right_eq_left_mul_exp, heat_left]
  rfl

/-! ## Closed support regions with strict margins in the four windows -/

noncomputable def innerLower : Slot → ℝ
  | .heat => TerminalCompensation.lower OutgoingDilation.compensationPatch 0
  | _ => Real.exp 1

noncomputable def innerUpper : Slot → ℝ
  | .heat => TerminalCompensation.upper OutgoingDilation.compensationPatch 2
  | _ => Real.exp 4

theorem inner_bounds (s : Slot) :
    1 < innerLower s ∧ innerLower s < innerUpper s ∧ innerUpper s < Real.exp 5 := by
  cases s with
  | heat =>
    refine ⟨TerminalCompensation.lower_gt_left OutgoingDilation.compensationPatch 0, ?_,
      TerminalCompensation.upper_lt_right OutgoingDilation.compensationPatch 2⟩
    have h := OutgoingDilation.compensationPatch.ordered
    norm_num [innerLower, innerUpper, TerminalCompensation.lower, TerminalCompensation.upper] at *
    linarith
  | modulation | positive | mean =>
    simp only [innerLower, innerUpper]
    exact ⟨by simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr (show (0 : ℝ) < 1 by norm_num),
      Real.exp_lt_exp.mpr (by norm_num), Real.exp_lt_exp.mpr (by norm_num)⟩

noncomputable def supportLeft (F : Profile) (XR : ℝ) (s : Slot) : ℝ :=
  left F XR s * innerLower s

noncomputable def supportRight (F : Profile) (XR : ℝ) (s : Slot) : ℝ :=
  left F XR s * innerUpper s

noncomputable def closedPatch (F : Profile) (XR : ℝ) (s : Slot) : Set ℝ :=
  Icc (supportLeft F XR s) (supportRight F XR s)

theorem supportLeft_formula (F : Profile) (XR : ℝ) {s : Slot} (hs : s ≠ .heat) :
    supportLeft F XR s = OutgoingDilation.radius XR (leftClock F s + 1) := by
  cases s <;> simp_all [supportLeft, left, innerLower, OutgoingDilation.radius,
    Real.exp_add, mul_assoc]

theorem supportRight_formula (F : Profile) (XR : ℝ) {s : Slot} (hs : s ≠ .heat) :
    supportRight F XR s = OutgoingDilation.radius XR (rightClock F s - 1) := by
  have hu : innerUpper s = Real.exp 4 := by cases s <;> simp_all [innerUpper]
  have hc : rightClock F s - 1 = leftClock F s + 4 := by
    unfold rightClock leftClock
    rw [offset_width]
    ring
  rw [hc, supportRight, hu, left, OutgoingDilation.radius,
    OutgoingDilation.radius, Real.exp_add]
  ring

theorem support_margins (F : Profile) (XR : ℝ) (hXR : 0 < XR) (s : Slot) :
    left F XR s < supportLeft F XR s ∧
      supportLeft F XR s < supportRight F XR s ∧
      supportRight F XR s < right F XR s := by
  obtain ⟨hl, hm, hr⟩ := inner_bounds s
  have hp := left_pos F XR hXR s
  refine ⟨?_, mul_lt_mul_of_pos_left hm hp, ?_⟩
  · unfold supportLeft
    simpa only [mul_one] using mul_lt_mul_of_pos_left hl hp
  · rw [right_eq_left_mul_exp]
    exact mul_lt_mul_of_pos_left hr hp

theorem supportLeft_pos (F : Profile) (XR : ℝ) (hXR : 0 < XR) (s : Slot) :
    0 < supportLeft F XR s :=
  (left_pos F XR hXR s).trans (support_margins F XR hXR s).1

theorem closedPatch_subset (F : Profile) (XR : ℝ) (hXR : 0 < XR) (s : Slot) :
    closedPatch F XR s ⊆ window F XR s := by
  intro X hX
  obtain ⟨hl, _, hr⟩ := support_margins F XR hXR s
  exact ⟨hl.trans_le hX.1, hX.2.trans_lt hr⟩

theorem closedPatch_nonempty (F : Profile) (XR : ℝ) (hXR : 0 < XR) (s : Slot) :
    (closedPatch F XR s).Nonempty :=
  nonempty_Icc.mpr (support_margins F XR hXR s).2.1.le

theorem closedPatches_disjoint (F : Profile) (XR : ℝ) (hXR : 0 < XR)
    {s t : Slot} (hst : s ≠ t) :
    Disjoint (closedPatch F XR s) (closedPatch F XR t) :=
  (windows_disjoint F XR hXR hst).mono
    (closedPatch_subset F XR hXR s) (closedPatch_subset F XR hXR t)

noncomputable def momentPatch (F : Profile) (XR : ℝ) (hXR : 0 < XR)
    (s : Slot) : FiveProfileMoments.Patch where
  left := supportLeft F XR s
  right := supportRight F XR s
  left_pos := supportLeft_pos F XR hXR s
  ordered := (support_margins F XR hXR s).2.1

/-! ## Exact fields on the actual, common outgoing profile -/

noncomputable def xAmplitude (F : Profile) (XR eta : ℝ) : ℝ :=
  OutgoingSchedule.radialAmplitude F.data.core.P F.data.core.dropLength F.data.core.lam
    F.data.core.holdStart * OutgoingSchedule.shape eta *
      Real.exp ((1 / 2 + F.data.core.lam) * (Real.log XR + F.data.core.holdStart))

theorem xAmplitude_pos (F : Profile) (XR eta : ℝ) : 0 < xAmplitude F XR eta := by
  apply mul_pos
  · exact mul_pos (mul_pos F.data.core.P_pos (Real.exp_pos _)) (OutgoingSchedule.shape_pos eta)
  · exact Real.exp_pos _

theorem xAmplitude_contDiff (F : Profile) (XR : ℝ) : ContDiff ℝ ∞ (xAmplitude F XR) :=
  (contDiff_const.mul OutgoingSchedule.shape_contDiff).mul contDiff_const

theorem xAmplitude_shape (F : Profile) (XR eta : ℝ) :
    xAmplitude F XR eta = xAmplitude F XR 0 / (1 + eta ^ 2) := by
  simp only [xAmplitude, OutgoingSchedule.shape, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, add_zero, inv_one, mul_one, div_eq_mul_inv]
  ring

theorem clean_E_shaped (F : Profile) (XR eta X : ℝ) (hXR : 0 < XR) (hX : 0 < X)
    (hlo : F.data.core.holdStart ≤ OutgoingDilation.clock XR X)
    (hhi : OutgoingDilation.clock XR X ≤ F.data.core.pulseStart) :
    OutgoingDilation.E F XR (X, eta) =
      xAmplitude F XR eta * X ^ (-(1 / 2 + F.data.core.lam)) := by
  have he : OutgoingDilation.clock XR X ≤ F.data.core.endpoint := by
    dsimp only [OutgoingSchedule.Parameters.endpoint]
    linarith [F.data.core.pulseLength_pos]
  change F.logE (OutgoingDilation.clock XR X, eta) = _
  rw [F.logE_before eta he, OutgoingSchedule.angular_shaped_wait F.data.core eta hlo]
  unfold xAmplitude
  rw [Real.rpow_def_of_pos hX]
  have hex :
      -(1 / 2 + F.data.core.lam) * (OutgoingDilation.clock XR X - F.data.core.holdStart) =
      (1 / 2 + F.data.core.lam) * (Real.log XR + F.data.core.holdStart) +
        Real.log X * -(1 / 2 + F.data.core.lam) := by
    rw [OutgoingDilation.clock, Real.log_div hX.ne' hXR.ne']
    ring
  rw [hex, Real.exp_add]
  ring

theorem clean_fields (F : Profile) (XR : ℝ) (hXR : 0 < XR) (s : Slot)
    (eta : ℝ) {X : ℝ} (hX : X ∈ window F XR s) :
    OutgoingDilation.U F XR (X, eta) = 0 ∧
      OutgoingDilation.E F XR (X, eta) =
        xAmplitude F XR eta * X ^ (-(1 / 2 + F.data.core.lam)) := by
  obtain ⟨hlo, hhi⟩ := window_inside_wait F XR hXR s hX
  refine ⟨?_, clean_E_shaped F XR eta X hXR (mem_window_pos F XR hXR s hX) hlo.le hhi.le⟩
  exact OutgoingSchedule.axial_shaped_wait F.data.core F.amp eta hlo.le hhi.le

theorem heated_E_eq_clean (F : Profile) (XR : ℝ) (hXR : 0 < XR)
    (c : ℝ → HeatedOutgoing.Coeff) {s : Slot} (hs : s ≠ .heat)
    (eta : ℝ) {X : ℝ} (hX : X ∈ window F XR s) :
    HeatedOutgoing.E F XR c (X, eta) = OutgoingDilation.E F XR (X, eta) := by
  have hp := mem_window_pos F XR hXR s hX
  rcases offsets_separated hs with h | h
  · apply HeatedOutgoing.E_before_patch F XR c eta X hXR hp
    rw [← heat_left]
    exact hX.2.le.trans ((radius_strictMono XR hXR).monotone (add_le_add_right h _))
  · apply HeatedOutgoing.E_between_patch_and_switch F XR c eta X hXR hp
    · rw [← heat_right]
      exact ((radius_strictMono XR hXR).monotone (add_le_add_right h _)).trans hX.1.le
    · exact hX.2.le.trans (right_before_switch F XR hXR s).le

/-- The heat slot is deliberately excluded: its additive correction is real. -/
theorem heated_fields (F : Profile) (XR : ℝ) (hXR : 0 < XR)
    (c : ℝ → HeatedOutgoing.Coeff) {s : Slot} (hs : s ≠ .heat)
    (eta : ℝ) {X : ℝ} (hX : X ∈ window F XR s) :
    HeatedOutgoing.U F XR (X, eta) = 0 ∧
      HeatedOutgoing.E F XR c (X, eta) =
        xAmplitude F XR eta * X ^ (-(1 / 2 + F.data.core.lam)) := by
  rw [heated_E_eq_clean F XR hXR c hs eta hX]
  exact clean_fields F XR hXR s eta hX

theorem heated_fields_on_closedPatch (F : Profile) (XR : ℝ) (hXR : 0 < XR)
    (c : ℝ → HeatedOutgoing.Coeff) {s : Slot} (hs : s ≠ .heat)
    (eta : ℝ) {X : ℝ} (hX : X ∈ closedPatch F XR s) :
    HeatedOutgoing.U F XR (X, eta) = 0 ∧
      HeatedOutgoing.E F XR c (X, eta) =
        xAmplitude F XR eta * X ^ (-(1 / 2 + F.data.core.lam)) :=
  heated_fields F XR hXR c hs eta (closedPatch_subset F XR hXR s hX)

theorem heat_slot_actual_formula (F : Profile) (XR : ℝ) (hXR : 0 < XR)
    (c : ℝ → HeatedOutgoing.Coeff) (eta : ℝ) {X : ℝ} (hX : X ∈ window F XR .heat) :
    HeatedOutgoing.E F XR c (X, eta) =
      xAmplitude F XR eta * X ^ (-(1 / 2 + F.data.core.lam)) +
        HeatedOutgoing.patchIncrement F XR c (X, eta) := by
  rw [HeatedOutgoing.E, HeatedOutgoing.heatE_before F XR eta X hXR
    (mem_window_pos F XR hXR .heat hX) (hX.2.le.trans (right_before_switch F XR hXR .heat).le)]
  rw [(clean_fields F XR hXR .heat eta hX).2]

theorem witness_fields {F : Profile} {XR C : ℝ}
    (w : HeatedOutgoing.CompensationWitness F XR C) {s : Slot} (hs : s ≠ .heat)
    (eta : ℝ) {X : ℝ} (hX : X ∈ window F XR s) :
    HeatedOutgoing.U F XR (X, eta) = 0 ∧
      HeatedOutgoing.E F XR w.coefficients (X, eta) =
        xAmplitude F XR eta * X ^ (-(1 / 2 + F.data.core.lam)) :=
  heated_fields F XR w.radius_pos w.coefficients hs eta hX

/-! ## The heat correction lies in its own closed interior support region -/

theorem terminal_lower_min (P : TerminalCompensation.Patch) (j : Fin 3) :
    TerminalCompensation.lower P 0 ≤ TerminalCompensation.lower P j := by
  fin_cases j <;> norm_num [TerminalCompensation.lower] <;> linarith [P.ordered]

theorem terminal_upper_max (P : TerminalCompensation.Patch) (j : Fin 3) :
    TerminalCompensation.upper P j ≤ TerminalCompensation.upper P 2 := by
  fin_cases j <;> norm_num [TerminalCompensation.upper] <;> linarith [P.ordered]

theorem terminal_correction_inner_support (P : TerminalCompensation.Patch)
    (c : TerminalCompensation.Coeff) :
    support (TerminalCompensation.correction P c) ⊆
      Icc (TerminalCompensation.lower P 0) (TerminalCompensation.upper P 2) := by
  intro x hx
  by_contra hn
  apply hx
  apply Finset.sum_eq_zero
  intro j _
  have hb : TerminalCompensation.bump P j x = 0 := by
    by_contra hne
    have ht := TerminalCompensation.bump_tsupport P j (subset_tsupport _ hne)
    exact hn ⟨(terminal_lower_min P j).trans ht.1.le,
      ht.2.le.trans (terminal_upper_max P j)⟩
  rw [hb, mul_zero]

theorem heat_increment_support (F : Profile) (XR : ℝ) (hXR : 0 < XR)
    (c : ℝ → HeatedOutgoing.Coeff) (eta : ℝ) :
    support (fun X => HeatedOutgoing.patchIncrement F XR c (X, eta)) ⊆
      closedPatch F XR .heat := by
  intro X hX
  have hn : TerminalCompensation.correction OutgoingDilation.compensationPatch (c eta)
      (X / OutgoingDilation.patchRadius F XR) ≠ 0 := by
    intro hz
    exact hX (by simp only [HeatedOutgoing.patchIncrement, hz, mul_zero])
  have ht := terminal_correction_inner_support OutgoingDilation.compensationPatch (c eta) hn
  have hp := OutgoingDilation.patchRadius_pos F XR hXR
  constructor
  · change left F XR .heat * innerLower .heat ≤ X
    rw [heat_left]
    simpa only [innerLower, mul_comm] using (le_div_iff₀ hp).mp ht.1
  · change X ≤ left F XR .heat * innerUpper .heat
    rw [heat_left]
    simpa only [innerUpper, mul_comm] using (div_le_iff₀ hp).mp ht.2

theorem heat_increment_tsupport (F : Profile) (XR : ℝ) (hXR : 0 < XR)
    (c : ℝ → HeatedOutgoing.Coeff) (eta : ℝ) :
    tsupport (fun X => HeatedOutgoing.patchIncrement F XR c (X, eta)) ⊆
      closedPatch F XR .heat :=
  closure_minimal (heat_increment_support F XR hXR c eta) isClosed_Icc

/-! ## Conversion to the similarity radius R, where X = R squared / 2 -/

noncomputable def radialLeft (F : Profile) (XR : ℝ) (s : Slot) : ℝ :=
  Real.sqrt (2 * left F XR s)

noncomputable def radialRight (F : Profile) (XR : ℝ) (s : Slot) : ℝ :=
  Real.sqrt (2 * right F XR s)

noncomputable def radialSupportLeft (F : Profile) (XR : ℝ) (s : Slot) : ℝ :=
  Real.sqrt (2 * supportLeft F XR s)

noncomputable def radialSupportRight (F : Profile) (XR : ℝ) (s : Slot) : ℝ :=
  Real.sqrt (2 * supportRight F XR s)

noncomputable def radialWindow (F : Profile) (XR : ℝ) (s : Slot) : Set ℝ :=
  Ioo (radialLeft F XR s) (radialRight F XR s)

noncomputable def radialClosedPatch (F : Profile) (XR : ℝ) (s : Slot) : Set ℝ :=
  Icc (radialSupportLeft F XR s) (radialSupportRight F XR s)

theorem radialLeft_pos (F : Profile) (XR : ℝ) (hXR : 0 < XR) (s : Slot) :
    0 < radialLeft F XR s :=
  Real.sqrt_pos.mpr (mul_pos (by norm_num) (left_pos F XR hXR s))

theorem radial_left_lt_right (F : Profile) (XR : ℝ) (hXR : 0 < XR) (s : Slot) :
    radialLeft F XR s < radialRight F XR s :=
  Real.sqrt_lt_sqrt (mul_nonneg (by norm_num) (left_pos F XR hXR s).le)
    (mul_lt_mul_of_pos_left (left_lt_right F XR hXR s) (by norm_num))

theorem radial_support_margins (F : Profile) (XR : ℝ) (hXR : 0 < XR) (s : Slot) :
    radialLeft F XR s < radialSupportLeft F XR s ∧
      radialSupportLeft F XR s < radialSupportRight F XR s ∧
      radialSupportRight F XR s < radialRight F XR s := by
  obtain ⟨hl, hm, hr⟩ := support_margins F XR hXR s
  have ha := left_pos F XR hXR s
  have hb := ha.trans hl
  have hc := hb.trans hm
  exact ⟨Real.sqrt_lt_sqrt (by positivity) (by nlinarith),
    Real.sqrt_lt_sqrt (by positivity) (by nlinarith),
    Real.sqrt_lt_sqrt (by positivity) (by nlinarith)⟩

theorem radialSupportLeft_pos (F : Profile) (XR : ℝ) (hXR : 0 < XR) (s : Slot) :
    0 < radialSupportLeft F XR s :=
  (radialLeft_pos F XR hXR s).trans (radial_support_margins F XR hXR s).1

theorem square_half_mem_Ioo {a b R : ℝ} (ha : 0 < a)
    (hR : R ∈ Ioo (Real.sqrt (2 * a)) (Real.sqrt (2 * b))) :
    R ^ 2 / 2 ∈ Ioo a b := by
  have hRp : 0 < R := (Real.sqrt_pos.mpr (mul_pos (by norm_num) ha)).trans hR.1
  have hb : 0 < b := by
    have hsb : 0 < Real.sqrt (2 * b) := hRp.trans hR.2
    have h2b := Real.sqrt_pos.mp hsb
    linarith
  have hl := (sq_lt_sq₀ (Real.sqrt_nonneg (2 * a)) hRp.le).mpr hR.1
  have hr := (sq_lt_sq₀ hRp.le (Real.sqrt_nonneg (2 * b))).mpr hR.2
  rw [Real.sq_sqrt (by positivity)] at hl
  rw [Real.sq_sqrt (by positivity)] at hr
  constructor <;> nlinarith

theorem square_half_mem_Icc {a b R : ℝ} (ha : 0 < a)
    (hR : R ∈ Icc (Real.sqrt (2 * a)) (Real.sqrt (2 * b))) :
    R ^ 2 / 2 ∈ Icc a b := by
  have hRp : 0 < R := (Real.sqrt_pos.mpr (mul_pos (by norm_num) ha)).trans_le hR.1
  have hb : 0 < b := by
    have hsb : 0 < Real.sqrt (2 * b) := hRp.trans_le hR.2
    have h2b := Real.sqrt_pos.mp hsb
    linarith
  have hl := (sq_le_sq₀ (Real.sqrt_nonneg (2 * a)) hRp.le).mpr hR.1
  have hr := (sq_le_sq₀ hRp.le (Real.sqrt_nonneg (2 * b))).mpr hR.2
  rw [Real.sq_sqrt (by positivity)] at hl
  rw [Real.sq_sqrt (by positivity)] at hr
  constructor <;> nlinarith

theorem radial_mem_window (F : Profile) (XR : ℝ) (hXR : 0 < XR) (s : Slot)
    {R : ℝ} (hR : R ∈ radialWindow F XR s) : R ^ 2 / 2 ∈ window F XR s :=
  square_half_mem_Ioo (left_pos F XR hXR s) hR

theorem radial_mem_closedPatch (F : Profile) (XR : ℝ) (hXR : 0 < XR) (s : Slot)
    {R : ℝ} (hR : R ∈ radialClosedPatch F XR s) : R ^ 2 / 2 ∈ closedPatch F XR s :=
  square_half_mem_Icc (supportLeft_pos F XR hXR s) hR

theorem radial_closedPatch_subset (F : Profile) (XR : ℝ) (hXR : 0 < XR) (s : Slot) :
    radialClosedPatch F XR s ⊆ radialWindow F XR s := by
  intro R hR
  obtain ⟨hl, _, hr⟩ := radial_support_margins F XR hXR s
  exact ⟨hl.trans_le hR.1, hR.2.trans_lt hr⟩

theorem radial_windows_disjoint (F : Profile) (XR : ℝ) (hXR : 0 < XR)
    {s t : Slot} (hst : s ≠ t) : Disjoint (radialWindow F XR s) (radialWindow F XR t) := by
  apply Set.disjoint_left.mpr
  intro R hRs hRt
  exact Set.disjoint_left.mp (windows_disjoint F XR hXR hst)
    (radial_mem_window F XR hXR s hRs) (radial_mem_window F XR hXR t hRt)

theorem radial_closedPatches_disjoint (F : Profile) (XR : ℝ) (hXR : 0 < XR)
    {s t : Slot} (hst : s ≠ t) :
    Disjoint (radialClosedPatch F XR s) (radialClosedPatch F XR t) :=
  (radial_windows_disjoint F XR hXR hst).mono
    (radial_closedPatch_subset F XR hXR s) (radial_closedPatch_subset F XR hXR t)

noncomputable def radialAmplitude (F : Profile) (XR eta : ℝ) : ℝ :=
  xAmplitude F XR eta * (2 : ℝ) ^ (1 / 2 + F.data.core.lam)

theorem radialAmplitude_pos (F : Profile) (XR eta : ℝ) :
    0 < radialAmplitude F XR eta :=
  mul_pos (xAmplitude_pos F XR eta) (Real.rpow_pos_of_pos (by norm_num) _)

theorem radialAmplitude_contDiff (F : Profile) (XR : ℝ) :
    ContDiff ℝ ∞ (radialAmplitude F XR) :=
  (xAmplitude_contDiff F XR).mul contDiff_const

theorem radialAmplitude_shape (F : Profile) (XR eta : ℝ) :
    radialAmplitude F XR eta = radialAmplitude F XR 0 / (1 + eta ^ 2) := by
  simp only [radialAmplitude]
  rw [xAmplitude_shape F XR eta]
  ring

theorem square_half_power (lam R : ℝ) (hR : 0 < R) :
    (R ^ 2 / 2) ^ (-(1 / 2 + lam)) =
      (2 : ℝ) ^ (1 / 2 + lam) * R ^ (-1 - 2 * lam) := by
  have hX : 0 < R ^ 2 / 2 := by positivity
  rw [Real.rpow_def_of_pos hX, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
    Real.rpow_def_of_pos hR, ← Real.exp_add,
    Real.log_div (pow_ne_zero 2 hR.ne') (by norm_num), Real.log_pow]
  congr 1
  ring

/-- This is the precise R-power interface used by positive-order and mean repairs. -/
theorem radial_heated_fields (F : Profile) (XR : ℝ) (hXR : 0 < XR)
    (c : ℝ → HeatedOutgoing.Coeff) {s : Slot} (hs : s ≠ .heat)
    (eta : ℝ) {R : ℝ} (hR : R ∈ radialWindow F XR s) :
    HeatedOutgoing.U F XR (R ^ 2 / 2, eta) = 0 ∧
      HeatedOutgoing.E F XR c (R ^ 2 / 2, eta) =
        FiveRowRank.background F.data.core.lam (radialAmplitude F XR eta) R := by
  have hp : 0 < R := (radialLeft_pos F XR hXR s).trans hR.1
  obtain ⟨hu, he⟩ := heated_fields F XR hXR c hs eta (radial_mem_window F XR hXR s hR)
  refine ⟨hu, ?_⟩
  rw [he, square_half_power _ _ hp]
  simp only [FiveRowRank.background, radialAmplitude, mul_assoc]

theorem radial_witness_fields {F : Profile} {XR C : ℝ}
    (w : HeatedOutgoing.CompensationWitness F XR C) {s : Slot} (hs : s ≠ .heat)
    (eta : ℝ) {R : ℝ} (hR : R ∈ radialWindow F XR s) :
    HeatedOutgoing.U F XR (R ^ 2 / 2, eta) = 0 ∧
      HeatedOutgoing.E F XR w.coefficients (R ^ 2 / 2, eta) =
        FiveRowRank.background F.data.core.lam (radialAmplitude F XR eta) R :=
  radial_heated_fields F XR w.radius_pos w.coefficients hs eta hR

theorem radial_heated_fields_on_closedPatch (F : Profile) (XR : ℝ) (hXR : 0 < XR)
    (c : ℝ → HeatedOutgoing.Coeff) {s : Slot} (hs : s ≠ .heat)
    (eta : ℝ) {R : ℝ} (hR : R ∈ radialClosedPatch F XR s) :
    HeatedOutgoing.U F XR (R ^ 2 / 2, eta) = 0 ∧
      HeatedOutgoing.E F XR c (R ^ 2 / 2, eta) =
        FiveRowRank.background F.data.core.lam (radialAmplitude F XR eta) R :=
  radial_heated_fields F XR hXR c hs eta (radial_closedPatch_subset F XR hXR s hR)

/-! ## Supported perturbations preserve the other complete open windows -/

def Supported (F : Profile) (XR : ℝ) (s : Slot) (v : ℝ × ℝ → ℝ) : Prop :=
  ∀ eta, support (fun X => v (X, eta)) ⊆ closedPatch F XR s

theorem heat_increment_supported (F : Profile) (XR : ℝ) (hXR : 0 < XR)
    (c : ℝ → HeatedOutgoing.Coeff) :
    Supported F XR .heat (HeatedOutgoing.patchIncrement F XR c) :=
  heat_increment_support F XR hXR c

/-- The actual five-row bump formulas satisfy the support premise, for arbitrary
amplitude and coefficient functions. Smoothness is irrelevant to this identity. -/
theorem five_row_updates_supported (F : Profile) (XR : ℝ) (hXR : 0 < XR) (s : Slot)
    (A : ℝ → ℝ) (c : ℝ → FiveProfileMoments.Coeff) :
    Supported F XR s (fun p => A p.2 * FiveProfileMoments.u (momentPatch F XR hXR s) (c p.2) p.1) ∧
      Supported F XR s (fun p => A p.2 * FiveProfileMoments.e (momentPatch F XR hXR s) (c p.2) p.1)
        := by
  constructor
  · intro eta X hX
    have ht := (FiveProfileMoments.physical_edits_tsupport
      (momentPatch F XR hXR s) (A eta) (c eta)).1 (subset_tsupport _ hX)
    exact ⟨ht.1.le, ht.2.le⟩
  · intro eta X hX
    have ht := (FiveProfileMoments.physical_edits_tsupport
      (momentPatch F XR hXR s) (A eta) (c eta)).2 (subset_tsupport _ hX)
    exact ⟨ht.1.le, ht.2.le⟩

theorem supported_vanishes (F : Profile) (XR : ℝ) (hXR : 0 < XR)
    {s t : Slot} (hst : s ≠ t) {v : ℝ × ℝ → ℝ} (hv : Supported F XR s v)
    (eta : ℝ) {X : ℝ} (hX : X ∈ window F XR t) : v (X, eta) = 0 := by
  by_contra hn
  have hs := closedPatch_subset F XR hXR s (hv eta hn)
  exact Set.disjoint_left.mp (windows_disjoint F XR hXR hst) hs hX

theorem supported_update_eqOn (F : Profile) (XR : ℝ) (hXR : 0 < XR)
    {s t : Slot} (hst : s ≠ t) {v : ℝ × ℝ → ℝ} (hv : Supported F XR s v)
    (g : ℝ × ℝ → ℝ) :
    EqOn (fun p => g p + v p) g (window F XR t ×ˢ (univ : Set ℝ)) := by
  intro p hp
  change g p + v p = g p
  have hz : v p = 0 := supported_vanishes F XR hXR hst hv p.2 hp.1
  rw [hz, add_zero]

theorem supported_update_germ (F : Profile) (XR : ℝ) (hXR : 0 < XR)
    {s t : Slot} (hst : s ≠ t) {v : ℝ × ℝ → ℝ} (hv : Supported F XR s v)
    (g : ℝ × ℝ → ℝ) {p : ℝ × ℝ} (hp : p.1 ∈ window F XR t) :
    (fun q => g q + v q) =ᶠ[𝓝 p] g := by
  have ho : IsOpen (window F XR t ×ˢ (univ : Set ℝ)) := isOpen_Ioo.prod isOpen_univ
  filter_upwards [ho.mem_nhds (show p ∈ window F XR t ×ˢ (univ : Set ℝ) from
    ⟨hp, mem_univ _⟩)] with q hq
  exact supported_update_eqOn F XR hXR hst hv g hq

theorem supported_update_jets (F : Profile) (XR : ℝ) (hXR : 0 < XR)
    {s t : Slot} (hst : s ≠ t) {v : ℝ × ℝ → ℝ} (hv : Supported F XR s v)
    (g : ℝ × ℝ → ℝ) {p : ℝ × ℝ} (hp : p.1 ∈ window F XR t) (n : ℕ) :
    iteratedFDeriv ℝ n (fun q => g q + v q) p = iteratedFDeriv ℝ n g p := by
  have hg := supported_update_germ F XR hXR hst hv g hp
  have hg' : (fun q => g q + v q) =ᶠ[𝓝[univ] p] g := by simpa using hg
  simpa only [iteratedFDerivWithin_univ] using
    hg'.iteratedFDerivWithin_eq (𝕜 := ℝ) hg.self_of_nhds n

theorem supported_updates_preserve_fields (F : Profile) (XR : ℝ) (hXR : 0 < XR)
    (c : ℝ → HeatedOutgoing.Coeff) {s t : Slot} (hst : s ≠ t) (ht : t ≠ .heat)
    {vU vE : ℝ × ℝ → ℝ} (hu : Supported F XR s vU) (he : Supported F XR s vE)
    (eta : ℝ) {X : ℝ} (hX : X ∈ window F XR t) :
    HeatedOutgoing.U F XR (X, eta) + vU (X, eta) = 0 ∧
      HeatedOutgoing.E F XR c (X, eta) + vE (X, eta) =
        xAmplitude F XR eta * X ^ (-(1 / 2 + F.data.core.lam)) := by
  rw [supported_vanishes F XR hXR hst hu eta hX,
    supported_vanishes F XR hXR hst he eta hX, add_zero, add_zero]
  exact heated_fields F XR hXR c ht eta hX

theorem finite_updates_eqOn {ι : Type*} [Fintype ι]
    (F : Profile) (XR : ℝ) (hXR : 0 < XR) (t : Slot)
    (s : ι → Slot) (v : ι → ℝ × ℝ → ℝ)
    (hs : ∀ i, s i ≠ t) (hv : ∀ i, Supported F XR (s i) (v i))
    (g : ℝ × ℝ → ℝ) :
    EqOn (fun p => g p + ∑ i, v i p) g (window F XR t ×ˢ (univ : Set ℝ)) := by
  intro p hp
  have hz : ∑ i, v i p = 0 := Finset.sum_eq_zero
    (fun i _ => supported_vanishes F XR hXR (hs i) (hv i) p.2 hp.1)
  change g p + ∑ i, v i p = g p
  rw [hz, add_zero]

def RadialSupported (F : Profile) (XR : ℝ) (s : Slot) (v : ℝ × ℝ → ℝ) : Prop :=
  ∀ eta, support (fun R => v (R, eta)) ⊆ radialWindow F XR s

/-- This premise is exactly the open-support conclusion of the positive-order
and mean bump solvers. They may use the full window or any smaller subpatch. -/
theorem radial_supported_vanishes (F : Profile) (XR : ℝ) (hXR : 0 < XR)
    {s t : Slot} (hst : s ≠ t) {v : ℝ × ℝ → ℝ} (hv : RadialSupported F XR s v)
    (eta : ℝ) {R : ℝ} (hR : R ∈ radialWindow F XR t) : v (R, eta) = 0 := by
  by_contra hn
  exact Set.disjoint_left.mp (radial_windows_disjoint F XR hXR hst) (hv eta hn) hR

theorem radial_supported_update_germ (F : Profile) (XR : ℝ) (hXR : 0 < XR)
    {s t : Slot} (hst : s ≠ t) {v : ℝ × ℝ → ℝ} (hv : RadialSupported F XR s v)
    (g : ℝ × ℝ → ℝ) {p : ℝ × ℝ} (hp : p.1 ∈ radialWindow F XR t) :
    (fun q => g q + v q) =ᶠ[𝓝 p] g := by
  have ho : IsOpen (radialWindow F XR t ×ˢ (univ : Set ℝ)) := isOpen_Ioo.prod isOpen_univ
  filter_upwards [ho.mem_nhds (show p ∈ radialWindow F XR t ×ˢ (univ : Set ℝ) from
    ⟨hp, mem_univ _⟩)] with q hq
  have hz : v q = 0 := radial_supported_vanishes F XR hXR hst hv q.2 hq.1
  simp only [hz, add_zero]

theorem radial_supported_updates_preserve_fields (F : Profile) (XR : ℝ) (hXR : 0 < XR)
    (c : ℝ → HeatedOutgoing.Coeff) {s t : Slot} (hst : s ≠ t) (ht : t ≠ .heat)
    {vU vE : ℝ × ℝ → ℝ} (hu : RadialSupported F XR s vU) (he : RadialSupported F XR s vE)
    (eta : ℝ) {R : ℝ} (hR : R ∈ radialWindow F XR t) :
    HeatedOutgoing.U F XR (R ^ 2 / 2, eta) + vU (R, eta) = 0 ∧
      HeatedOutgoing.E F XR c (R ^ 2 / 2, eta) + vE (R, eta) =
        FiveRowRank.background F.data.core.lam (radialAmplitude F XR eta) R := by
  rw [radial_supported_vanishes F XR hXR hst hu eta hR,
    radial_supported_vanishes F XR hXR hst he eta hR, add_zero, add_zero]
  exact radial_heated_fields F XR hXR c ht eta hR

theorem radial_finite_updates_eqOn {ι : Type*} [Fintype ι]
    (F : Profile) (XR : ℝ) (hXR : 0 < XR) (t : Slot)
    (s : ι → Slot) (v : ι → ℝ × ℝ → ℝ)
    (hs : ∀ i, s i ≠ t) (hv : ∀ i, RadialSupported F XR (s i) (v i))
    (g : ℝ × ℝ → ℝ) :
    EqOn (fun p => g p + ∑ i, v i p) g (radialWindow F XR t ×ˢ (univ : Set ℝ)) := by
  intro p hp
  have hz : ∑ i, v i p = 0 := Finset.sum_eq_zero
    (fun i _ => radial_supported_vanishes F XR hXR (hs i) (hv i) p.2 hp.1)
  change g p + ∑ i, v i p = g p
  rw [hz, add_zero]

end NavierStokes.ReservedPatches
