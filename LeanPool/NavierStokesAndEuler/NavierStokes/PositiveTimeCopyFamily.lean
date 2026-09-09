/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.LocalPhysicalCopyBounds

@[expose] public section

/-!
# Positive lift-time localization of actual copy amplitudes

The gate changes only the amplitude outside positive lift time.  The physical
common lift has positive time exactly before terminal time, so all physical
copy fields and their ambient jets agree there with the original fields.
-/

noncomputable section

namespace NavierStokes.PositiveTimeCopyFamily

open Set Function Filter ProblemStatement PhysicalCopyBounds
open PhysicalWaveSum (WaveIndex commonLift preterminal)
open scoped Topology ContDiff BigOperators

abbrev LiftPoint := PhysicalGraphBounds.LiftPoint

def liftPast : Set LiftPoint := {x | 0 < x.1.1}

theorem liftPast_open : IsOpen liftPast :=
  isOpen_lt continuous_const continuous_fst.fst

/-- The carrier and gap are unchanged. Only the amplitude is extended by
zero outside positive native lift time. -/
noncomputable def gate {H : ℕ} {K : Type*} (f : CopyFamily H K) : CopyFamily H K := by
  classical
  exact {
    gap := f.gap
    carrier := f.carrier
    amplitude k I x := if x ∈ liftPast then f.amplitude k I x else 0 }

variable {H : ℕ} {K : Type*}

@[simp] theorem gate_gap (f : CopyFamily H K) : (gate f).gap = f.gap := rfl

@[simp] theorem gate_carrier (f : CopyFamily H K) : (gate f).carrier = f.carrier := rfl

theorem gate_amplitude_eq (f : CopyFamily H K) (k : K) (I : WaveIndex H)
    {x : LiftPoint} (hx : x ∈ liftPast) : (gate f).amplitude k I x = f.amplitude k I x := by
  simp only [gate, ite_eq_left hx]

theorem gate_amplitude_zero (f : CopyFamily H K) (k : K) (I : WaveIndex H)
    {x : LiftPoint} (hx : x ∉ liftPast) : (gate f).amplitude k I x = 0 := by
  simp only [gate, ite_eq_right hx]

theorem gate_amplitude_ne_zero_iff (f : CopyFamily H K) (k : K) (I : WaveIndex H)
    (x : LiftPoint) :
    (gate f).amplitude k I x ≠ 0 ↔ x ∈ liftPast ∧ f.amplitude k I x ≠ 0 := by
  classical
  by_cases hx : x ∈ liftPast <;> simp [gate, hx]

theorem gate_amplitude_germ (f : CopyFamily H K) (k : K) (I : WaveIndex H)
    {x : LiftPoint} (hx : x ∈ liftPast) :
    (gate f).amplitude k I =ᶠ[𝓝 x] f.amplitude k I := by
  filter_upwards [liftPast_open.mem_nhds hx] with y hy
  exact gate_amplitude_eq f k I hy

theorem gate_amplitude_jets (f : CopyFamily H K) (k : K) (I : WaveIndex H)
    {x : LiftPoint} (hx : x ∈ liftPast) (m : ℕ) :
    iteratedFDeriv ℝ m ((gate f).amplitude k I) x =
      iteratedFDeriv ℝ m (f.amplitude k I) x :=
  PhysicalWaveSum.iteratedFDeriv_eq_of_eventuallyEq (gate_amplitude_germ f k I hx) m

theorem gate_amplitude_support_subset (f : CopyFamily H K) (k : K) (I : WaveIndex H) :
    support ((gate f).amplitude k I) ⊆ support (f.amplitude k I) :=
  fun x hx => ((gate_amplitude_ne_zero_iff f k I x).mp hx).2

/-- The original closed copy cells still contain the gated amplitude. -/
noncomputable def gateCells {f : CopyFamily H K} (hc : SupportCells f) : SupportCells (gate f) where
  cells := hc.cells
  support I k := (gate_amplitude_support_subset f k I).trans (hc.support I k)

@[simp] theorem gateCells_cells {f : CopyFamily H K} (hc : SupportCells f) :
    (gateCells hc).cells = hc.cells := rfl

/-- Carrier bounds refer to the same carrier and the same cells. -/
noncomputable def gateCarrier {f : CopyFamily H K} (hc : SupportCells f) {a b h r0 : ℝ}
    (hb : CarrierBounds f hc a b h r0) : CarrierBounds (gate f) (gateCells hc) a b h r0 where
  region := hb.region
  open_region := hb.open_region
  jets := hb.jets
  contains := hb.contains

@[simp] theorem gateCarrier_region {f : CopyFamily H K} (hc : SupportCells f) {a b h r0 : ℝ}
    (hb : CarrierBounds f hc a b h r0) : (gateCarrier hc hb).region = hb.region := rfl

theorem commonLift_time (h : ℝ) (n d : ℕ) (w : SpaceTime) :
    (commonLift h n d w).1.1 = (1 - w.1) / ChartScales.Q n :=
  PhysicalGraphBounds.physicalChart_time h n w

/-- This identity also holds on the axis and for arbitrary cover gap. -/
theorem commonLift_mem_liftPast_iff (h : ℝ) (n d : ℕ) (w : SpaceTime) :
    commonLift h n d w ∈ liftPast ↔ w ∈ preterminal := by
  change 0 < (commonLift h n d w).1.1 ↔ w.1 < 1
  rw [commonLift_time, div_pos_iff_of_pos_right (ChartScales.Q_pos n), sub_pos]

theorem commonLift_mem_liftPast (h : ℝ) (n d : ℕ) {w : SpaceTime} (hw : w ∈ preterminal) :
    commonLift h n d w ∈ liftPast := (commonLift_mem_liftPast_iff h n d w).mpr hw

section PhysicalFields

variable (f : CopyFamily H K) (a h r0 : ℝ)

theorem term_eq (I : WaveIndex H) (k : K) {w : SpaceTime} (hw : w ∈ preterminal) :
    (gate f).term a h r0 I k w = f.term a h r0 I k w := by
  have hl := commonLift_mem_liftPast h I.1.val.1 (f.gap I.1) hw
  simp only [CopyFamily.term, CopyFamily.copy, PhysicalWaveSum.WaveFamily.term,
    PhysicalWaveSum.globalWave, PhysicalWaveSum.commonWave, gate, ite_eq_left hl]

theorem term_zero (I : WaveIndex H) (k : K) {w : SpaceTime} (hw : w ∉ preterminal) :
    (gate f).term a h r0 I k w = 0 := by
  apply PhysicalWaveSum.globalWave_eq_zero
  exact gate_amplitude_zero f k I (fun hl => hw ((commonLift_mem_liftPast_iff h
    I.1.val.1 (f.gap I.1) w).mp hl))

theorem term_germ (I : WaveIndex H) (k : K) {w : SpaceTime} (hw : w ∈ preterminal) :
    (gate f).term a h r0 I k =ᶠ[𝓝 w] f.term a h r0 I k := by
  filter_upwards [PhysicalWaveSum.preterminal_open.mem_nhds hw] with y hy
  exact term_eq f a h r0 I k hy

theorem term_jets (I : WaveIndex H) (k : K) {w : SpaceTime} (hw : w ∈ preterminal) (m : ℕ) :
    iteratedFDeriv ℝ m ((gate f).term a h r0 I k) w =
      iteratedFDeriv ℝ m (f.term a h r0 I k) w :=
  PhysicalWaveSum.iteratedFDeriv_eq_of_eventuallyEq (term_germ f a h r0 I k hw) m

theorem term_support_subset (I : WaveIndex H) (k : K) :
    support ((gate f).term a h r0 I k) ⊆ support (f.term a h r0 I k) := by
  intro w hw
  by_cases ht : w ∈ preterminal
  · simpa only [mem_support, term_eq f a h r0 I k ht] using hw
  · exact (hw (term_zero f a h r0 I k ht)).elim

theorem term_tsupport_subset (I : WaveIndex H) (k : K) :
    tsupport ((gate f).term a h r0 I k) ⊆ tsupport (f.term a h r0 I k) :=
  closure_mono (term_support_subset f a h r0 I k)

theorem periodized_eq (I : WaveIndex H) {w : SpaceTime} (hw : w ∈ preterminal) :
    (gate f).periodized a h r0 I w = f.periodized a h r0 I w := by
  apply tsum_congr
  intro k
  exact term_eq f a h r0 I k hw

theorem periodized_zero (I : WaveIndex H) {w : SpaceTime} (hw : w ∉ preterminal) :
    (gate f).periodized a h r0 I w = 0 := by
  simp only [CopyFamily.periodized, term_zero f a h r0 I _ hw, tsum_zero]

theorem periodized_germ (I : WaveIndex H) {w : SpaceTime} (hw : w ∈ preterminal) :
    (gate f).periodized a h r0 I =ᶠ[𝓝 w] f.periodized a h r0 I := by
  filter_upwards [PhysicalWaveSum.preterminal_open.mem_nhds hw] with y hy
  exact periodized_eq f a h r0 I hy

theorem periodized_jets (I : WaveIndex H) {w : SpaceTime} (hw : w ∈ preterminal) (m : ℕ) :
    iteratedFDeriv ℝ m ((gate f).periodized a h r0 I) w =
      iteratedFDeriv ℝ m (f.periodized a h r0 I) w :=
  PhysicalWaveSum.iteratedFDeriv_eq_of_eventuallyEq (periodized_germ f a h r0 I hw) m

theorem sum_eq {w : SpaceTime} (hw : w ∈ preterminal) :
    (gate f).sum a h r0 w = f.sum a h r0 w := by
  exact congrArg (fun g : WaveIndex H → ℂ => ∑ᶠ I, g I)
    (funext (fun I => periodized_eq f a h r0 I hw))

theorem sum_zero {w : SpaceTime} (hw : w ∉ preterminal) : (gate f).sum a h r0 w = 0 := by
  simp only [CopyFamily.sum, periodized_zero f a h r0 _ hw, finsum_zero]

theorem sum_germ {w : SpaceTime} (hw : w ∈ preterminal) :
    (gate f).sum a h r0 =ᶠ[𝓝 w] f.sum a h r0 := by
  filter_upwards [PhysicalWaveSum.preterminal_open.mem_nhds hw] with y hy
  exact sum_eq f a h r0 hy

theorem sum_jets {w : SpaceTime} (hw : w ∈ preterminal) (m : ℕ) :
    iteratedFDeriv ℝ m ((gate f).sum a h r0) w = iteratedFDeriv ℝ m (f.sum a h r0) w :=
  PhysicalWaveSum.iteratedFDeriv_eq_of_eventuallyEq (sum_germ f a h r0 hw) m

end PhysicalFields

section VectorFields

variable (f : Fin 3 → CopyFamily H K) (a h r0 : ℝ)

theorem vectorSum_eq {w : SpaceTime} (hw : w ∈ preterminal) :
    PhysicalCopyBounds.vectorSum (fun i => gate (f i)) a h r0 w =
      PhysicalCopyBounds.vectorSum f a h r0 w := by
  simp only [PhysicalCopyBounds.vectorSum, sum_eq (f _) a h r0 hw]

theorem vectorSum_zero {w : SpaceTime} (hw : w ∉ preterminal) :
    PhysicalCopyBounds.vectorSum (fun i => gate (f i)) a h r0 w = 0 := by
  simp only [PhysicalCopyBounds.vectorSum, sum_zero (f _) a h r0 hw, map_zero,
    Finset.sum_const_zero]

theorem vectorSum_germ {w : SpaceTime} (hw : w ∈ preterminal) :
    PhysicalCopyBounds.vectorSum (fun i => gate (f i)) a h r0 =ᶠ[𝓝 w]
      PhysicalCopyBounds.vectorSum f a h r0 := by
  filter_upwards [PhysicalWaveSum.preterminal_open.mem_nhds hw] with y hy
  exact vectorSum_eq f a h r0 hy

theorem vectorSum_jets {w : SpaceTime} (hw : w ∈ preterminal) (m : ℕ) :
    iteratedFDeriv ℝ m (PhysicalCopyBounds.vectorSum (fun i => gate (f i)) a h r0) w =
      iteratedFDeriv ℝ m (PhysicalCopyBounds.vectorSum f a h r0) w :=
  PhysicalWaveSum.iteratedFDeriv_eq_of_eventuallyEq (vectorSum_germ f a h r0 hw) m

end VectorFields

end NavierStokes.PositiveTimeCopyFamily
