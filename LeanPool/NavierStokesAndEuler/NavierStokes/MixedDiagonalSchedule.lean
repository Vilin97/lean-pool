/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.CutStageEstimates

/-!
# One physical diagonal schedule for potentials, direct fields, and pressure

The three input sequences are fixed actual fields. Separate raw losses and
logarithmic factors are combined before applying the proved cutoff estimates.
The initial stage is retained explicitly in every resulting full sum.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.MixedDiagonalSchedule

open Set Function Filter ProblemStatement
open scoped Topology ContDiff BigOperators


/-- Component: an abbreviation for `Fin 3`. -/
abbrev Component := Fin 3

namespace Component

/-- Potential, given by `0`. -/
noncomputable def potential : Component := 0
/-- Direct, given by `1`. -/
noncomputable def direct : Component := 1
/-- Pressure, given by `2`. -/
noncomputable def pressure : Component := 2

end Component

/-- Component space, with branches according to `c = 2`. -/
@[reducible] noncomputable def ComponentSpace (c : Component) : Type :=
  if c = 2 then ℝ else Space

noncomputable instance (c : Component) : NormedAddCommGroup (ComponentSpace c) :=
  Fin.cases (inferInstance : NormedAddCommGroup Space)
    (Fin.cases (inferInstance : NormedAddCommGroup Space)
      (Fin.cases (inferInstance : NormedAddCommGroup ℝ) (fun i => Fin.elim0 i))) c

noncomputable instance (c : Component) : NormedSpace ℝ (ComponentSpace c) :=
  Fin.cases (inferInstance : NormedSpace ℝ Space)
    (Fin.cases (inferInstance : NormedSpace ℝ Space)
      (Fin.cases (inferInstance : NormedSpace ℝ ℝ) (fun i => Fin.elim0 i))) c

/-- Literal component selection; no new physical fields are chosen. -/
noncomputable def family (A B : ℕ → VelocityField) (P : ℕ → PressureField) :
    (c : Component) → ℕ → SpaceTime → ComponentSpace c :=
  Fin.cases A (Fin.cases B (Fin.cases P (fun i => Fin.elim0 i)))

/-- Scalar family, given by `Fin.cases A (Fin.cases B (Fin.cases P (fun i => Fin.elim0 i)))`. -/
noncomputable def scalarFamily (A B P : ℕ → ℕ → ℝ) : Component → ℕ → ℕ → ℝ :=
  Fin.cases A (Fin.cases B (Fin.cases P (fun i => Fin.elim0 i)))

/-- Common raw loss, given by `max (LA m) (max (LB m) (LP m))`. -/
noncomputable def commonRawLoss (LA LB LP : ℕ → ℝ) (m : ℕ) : ℝ :=
  max (LA m) (max (LB m) (LP m))

/-- Common loss, given by `CutStageEstimates.cutLoss (commonRawLoss LA LB LP)`. -/
noncomputable def commonLoss (LA LB LP : ℕ → ℝ) : ℕ → ℝ :=
  CutStageEstimates.cutLoss (commonRawLoss LA LB LP)

theorem potential_loss_le (LA LB LP : ℕ → ℝ) (m : ℕ) :
    LA m ≤ commonRawLoss LA LB LP m := le_max_left _ _

theorem direct_loss_le (LA LB LP : ℕ → ℝ) (m : ℕ) :
    LB m ≤ commonRawLoss LA LB LP m := (le_max_left _ _).trans (le_max_right _ _)

theorem pressure_loss_le (LA LB LP : ℕ → ℝ) (m : ℕ) :
    LP m ≤ commonRawLoss LA LB LP m := (le_max_right _ _).trans (le_max_right _ _)

/-- The simultaneous estimates required by the mixed residual consumer.
All three refer to the supplied full sequences, including their initial terms. -/
structure ThreeCutBounds (a : ℕ → ℕ) (h : ℝ) (A B : ℕ → VelocityField)
    (P : ℕ → PressureField) (g L : ℕ → ℝ) (S : Set SpaceTime) : Prop where
  potential : DiagonalJetBounds.CutStageBounds (fun j => (a j : ℝ)) (PhysicalWaveSum.physicalQ h) A
      g L S
  direct : DiagonalJetBounds.CutStageBounds (fun j => (a j : ℝ)) (PhysicalWaveSum.physicalQ h) B g
      L S
  pressure : DiagonalJetBounds.CutStageBounds (fun j => (a j : ℝ)) (PhysicalWaveSum.physicalQ h) P
      g L S

/-- Three smooth sums data, collecting `potential`, `direct`, `pressure`. -/
structure ThreeSmoothSums (a : ℕ → ℕ) (h : ℝ) (A B : ℕ → VelocityField)
    (P : ℕ → PressureField) : Prop where
  potential : ContDiffOn ℝ ∞ (SolenoidalDiagonal.potentialSum (fun j => (a j : ℝ))
      (PhysicalWaveSum.physicalQ h) A)
    PhysicalWaveSum.preterminal
  direct : ContDiffOn ℝ ∞ (SolenoidalDiagonal.potentialSum (fun j => (a j : ℝ))
      (PhysicalWaveSum.physicalQ h) B)
    PhysicalWaveSum.preterminal
  pressure : ContDiffOn ℝ ∞ (SolenoidalDiagonal.potentialSum (fun j => (a j : ℝ))
      (PhysicalWaveSum.physicalQ h) P)
    PhysicalWaveSum.preterminal

section RawLoss

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Enlarge only the fixed derivative loss. Absolute values remove any
unnecessary sign assumption on the originally supplied raw constants. -/
theorem raw_bounds_mono_loss {q : E → ℝ} {A : ℕ → E → V}
    {g L L' : ℕ → ℝ} {C p : ℕ → ℕ → ℝ} {S : Set E}
    (hpos : ∀ x ∈ S, 0 < q x) (hL : ∀ m, L m ≤ L' m)
    (hb : CutStageEstimates.RawStageBounds q A g L C p S) :
    CutStageEstimates.RawStageBounds q A g L' (fun j m => |C j m|) p S := by
  intro j hj m x hx hq1
  have hqx := hpos x hx
  have hl : 0 ≤ (1 + |Real.log (q x)|) ^ p j m := Real.rpow_nonneg (by positivity) _
  calc
    _ ≤ C j m * (1 + |Real.log (q x)|) ^ p j m * q x ^ (g j - L m) := hb j hj m x hx hq1
    _ ≤ |C j m| * (1 + |Real.log (q x)|) ^ p j m * q x ^ (g j - L m) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hl)
        (Real.rpow_nonneg hqx.le _)
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge hqx hq1 (sub_le_sub_left (hL m) _))
      (mul_nonneg (abs_nonneg _) hl)

/-- Suppressing stage zero does not change any positive-stage estimate. -/
theorem cut_bounds_of_positiveStages {a : ℕ → ℝ} {q : E → ℝ}
    {A : ℕ → E → V} {g L : ℕ → ℝ} {S : Set E}
    (hb : DiagonalJetBounds.CutStageBounds a q (CutStageEstimates.positiveStages A) g L S) :
    DiagonalJetBounds.CutStageBounds a q A g L S := by
  intro j hj m hm x hx
  have he : SolenoidalDiagonal.cutStage a q (CutStageEstimates.positiveStages A) j =
      SolenoidalDiagonal.cutStage a q A j := by
    funext y
    simp only [SolenoidalDiagonal.cutStage, CutStageEstimates.positiveStages_of_pos hj]
  have hjb := hb j hj m hm x hx
  rwa [he] at hjb

end RawLoss

private theorem family_raw_bounds {h : ℝ} {S : Set SpaceTime}
    (hpos : ∀ x ∈ S, 0 < PhysicalWaveSum.physicalQ h x)
    {A B : ℕ → VelocityField} {P : ℕ → PressureField}
    {g LA LB LP : ℕ → ℝ} {CA CB CP pA pB pP : ℕ → ℕ → ℝ}
    (hA : CutStageEstimates.RawStageBounds (PhysicalWaveSum.physicalQ h) A g LA CA pA S)
    (hB : CutStageEstimates.RawStageBounds (PhysicalWaveSum.physicalQ h) B g LB CB pB S)
    (hP : CutStageEstimates.RawStageBounds (PhysicalWaveSum.physicalQ h) P g LP CP pP S) :
    ∀ c, CutStageEstimates.RawStageBounds (PhysicalWaveSum.physicalQ h) (family A B P c) g
      (commonRawLoss LA LB LP)
      (scalarFamily (fun j m => |CA j m|) (fun j m => |CB j m|) (fun j m => |CP j m|) c)
      (scalarFamily pA pB pP c) S := by
  intro c
  fin_cases c
  · exact raw_bounds_mono_loss hpos (potential_loss_le LA LB LP) hA
  · exact raw_bounds_mono_loss hpos (direct_loss_le LA LB LP) hB
  · exact raw_bounds_mono_loss hpos (pressure_loss_le LA LB LP) hP

/-- Simultaneous bounds for the fixed three input families and one actual
integer schedule. No cut-stage estimate is a hypothesis. -/
theorem exists_three_component_schedule {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {S : Set SpaceTime} (hS : S ⊆ PhysicalWaveSum.preterminal)
    {A B : ℕ → VelocityField} {P : ℕ → PressureField}
    (hA : ∀ j, 1 ≤ j → ContDiffOn ℝ ∞ (A j) PhysicalWaveSum.preterminal)
    (hB : ∀ j, 1 ≤ j → ContDiffOn ℝ ∞ (B j) PhysicalWaveSum.preterminal)
    (hP : ∀ j, 1 ≤ j → ContDiffOn ℝ ∞ (P j) PhysicalWaveSum.preterminal)
    (g LA LB LP : ℕ → ℝ) (CA CB CP pA pB pP : ℕ → ℕ → ℝ)
    (rawA : CutStageEstimates.RawStageBounds (PhysicalWaveSum.physicalQ h) A g LA CA pA S)
    (rawB : CutStageEstimates.RawStageBounds (PhysicalWaveSum.physicalQ h) B g LB CB pB S)
    (rawP : CutStageEstimates.RawStageBounds (PhysicalWaveSum.physicalQ h) P g LP CP pP S)
    (hg : ∀ j, 1 ≤ j → 0 < g j) (lower : ℕ) :
    ∃ a : ℕ → ℕ, lower ≤ a 0 ∧ (∀ j, 0 < a j) ∧
      (∀ j, 2 * a j ≤ a (j + 1)) ∧ StrictMono a ∧
      Tendsto (fun j => (a j : ℝ)) atTop atTop ∧
      ThreeCutBounds a h A B P (fun j => g j / 2) (commonLoss LA LB LP) S := by
  have hs : ∀ c j, 1 ≤ j → ContDiffOn ℝ ∞ (family A B P c j) PhysicalWaveSum.preterminal := by
    intro c
    fin_cases c
    · exact hA
    · exact hB
    · exact hP
  obtain ⟨a, hal, hap, had, ham, hat, hb⟩ :=
    CutStageEstimates.exists_physical_finite_diagonal_cut_bounds hh hh1 hS hs g (commonRawLoss LA
        LB LP)
      (scalarFamily (fun j m => |CA j m|) (fun j m => |CB j m|) (fun j m => |CP j m|))
      (scalarFamily pA pB pP)
      (family_raw_bounds (fun w hw => PhysicalWaveSum.physicalQ_pos hh hh1 (hS hw)) rawA rawB rawP)
          hg lower
  exact ⟨a, hal, hap, had, ham, hat,
    ⟨hb Component.potential, hb Component.direct, hb Component.pressure⟩⟩

section InitialStage

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

omit [NormedSpace ℝ E] in
/-- Exact initial-stage bookkeeping for the actual sum. The full sequence
is never replaced by its positive part without retaining this first term. -/
theorem full_sum_eq_initial_add_positive {a : ℕ → ℝ} (ha : Tendsto a atTop atTop)
    {q : E → ℝ} {x : E} (hq : ContinuousAt q x) (hpos : 0 < q x) (A : ℕ → E → V) :
    SolenoidalDiagonal.potentialSum a q A x = SolenoidalDiagonal.cutStage a q A 0 x +
      SolenoidalDiagonal.potentialSum a q (CutStageEstimates.positiveStages A) x := by
  have hs := SolenoidalDiagonal.summable_cutStage ha hq hpos A
  have hp := SolenoidalDiagonal.summable_cutStage ha hq hpos (CutStageEstimates.positiveStages A)
  have ht : ∀ n, SolenoidalDiagonal.cutStage a q (CutStageEstimates.positiveStages A) (n + 1) x =
      SolenoidalDiagonal.cutStage a q A (n + 1) x := by
    intro n
    simp only [SolenoidalDiagonal.cutStage, CutStageEstimates.positiveStages_of_pos (Nat.succ_pos
        n)]
  rw [SolenoidalDiagonal.potentialSum, hs.tsum_eq_zero_add]
  rw [SolenoidalDiagonal.potentialSum, hp.tsum_eq_zero_add]
  simp only [SolenoidalDiagonal.cutStage, CutStageEstimates.positiveStages_zero, Pi.zero_apply,
      smul_zero, zero_add] at *
  simp only [← ht]

end InitialStage

theorem physical_initial_split {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {a : ℕ → ℕ} (ha : StrictMono a) {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] (A : ℕ → SpaceTime → V) :
    EqOn (SolenoidalDiagonal.potentialSum (fun j => (a j : ℝ)) (PhysicalWaveSum.physicalQ h) A)
      (fun w => SolenoidalDiagonal.cutStage (fun j => (a j : ℝ)) (PhysicalWaveSum.physicalQ h) A 0
          w +
        SolenoidalDiagonal.potentialSum (fun j => (a j : ℝ)) (PhysicalWaveSum.physicalQ h)
            (CutStageEstimates.positiveStages A) w)
      PhysicalWaveSum.preterminal := by
  intro w hw
  exact full_sum_eq_initial_add_positive (SolenoidalDiagonal.realScales_tendsto ha)
    (PhysicalWaveSum.physicalQ_smoothAt hh hh1 hw).continuousAt (PhysicalWaveSum.physicalQ_pos hh
        hh1 hw) A

theorem physical_initial_split_germ {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {a : ℕ → ℕ} (ha : StrictMono a) {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] (A : ℕ → SpaceTime → V)
    {w : SpaceTime} (hw : w ∈ PhysicalWaveSum.preterminal) :
    SolenoidalDiagonal.potentialSum (fun j => (a j : ℝ)) (PhysicalWaveSum.physicalQ h) A =ᶠ[𝓝 w]
      (fun z => SolenoidalDiagonal.cutStage (fun j => (a j : ℝ)) (PhysicalWaveSum.physicalQ h) A 0
          z +
        SolenoidalDiagonal.potentialSum (fun j => (a j : ℝ)) (PhysicalWaveSum.physicalQ h)
          (CutStageEstimates.positiveStages A) z) := by
  filter_upwards [PhysicalWaveSum.preterminal_open.mem_nhds hw] with z hz
  exact physical_initial_split hh hh1 ha A hz

theorem physical_initial_split_jets {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {a : ℕ → ℕ} (ha : StrictMono a) {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] (A : ℕ → SpaceTime → V)
    {w : SpaceTime} (hw : w ∈ PhysicalWaveSum.preterminal) (m : ℕ) :
    iteratedFDeriv ℝ m
        (SolenoidalDiagonal.potentialSum (fun j => (a j : ℝ)) (PhysicalWaveSum.physicalQ h) A) w =
      iteratedFDeriv ℝ m
        (fun z => SolenoidalDiagonal.cutStage (fun j => (a j : ℝ)) (PhysicalWaveSum.physicalQ h) A
            0 z +
          SolenoidalDiagonal.potentialSum (fun j => (a j : ℝ)) (PhysicalWaveSum.physicalQ h)
            (CutStageEstimates.positiveStages A) z) w :=
  (SolenoidalDiagonal.iteratedFDeriv_eventuallyEq
    (physical_initial_split_germ hh hh1 ha A hw) m).self_of_nhds

/-- The same schedule also yields smooth full sums when stage zero is
smooth. The quantitative input still concerns only positive stages. -/
theorem exists_three_component_schedule_smooth {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {S : Set SpaceTime} (hS : S ⊆ PhysicalWaveSum.preterminal)
    {A B : ℕ → VelocityField} {P : ℕ → PressureField}
    (hA : ∀ j, ContDiffOn ℝ ∞ (A j) PhysicalWaveSum.preterminal)
    (hB : ∀ j, ContDiffOn ℝ ∞ (B j) PhysicalWaveSum.preterminal)
    (hP : ∀ j, ContDiffOn ℝ ∞ (P j) PhysicalWaveSum.preterminal)
    (g LA LB LP : ℕ → ℝ) (CA CB CP pA pB pP : ℕ → ℕ → ℝ)
    (rawA : CutStageEstimates.RawStageBounds (PhysicalWaveSum.physicalQ h) A g LA CA pA S)
    (rawB : CutStageEstimates.RawStageBounds (PhysicalWaveSum.physicalQ h) B g LB CB pB S)
    (rawP : CutStageEstimates.RawStageBounds (PhysicalWaveSum.physicalQ h) P g LP CP pP S)
    (hg : ∀ j, 1 ≤ j → 0 < g j) (lower : ℕ) :
    ∃ a : ℕ → ℕ, lower ≤ a 0 ∧ (∀ j, 0 < a j) ∧
      (∀ j, 2 * a j ≤ a (j + 1)) ∧ StrictMono a ∧
      Tendsto (fun j => (a j : ℝ)) atTop atTop ∧
      ThreeCutBounds a h A B P (fun j => g j / 2) (commonLoss LA LB LP) S ∧
      ThreeSmoothSums a h A B P := by
  obtain ⟨a, hal, hap, had, ham, hat, hb⟩ := exists_three_component_schedule hh hh1 hS
    (fun j _ => hA j) (fun j _ => hB j) (fun j _ => hP j)
    g LA LB LP CA CB CP pA pB pP rawA rawB rawP hg lower
  have hq : ContDiffOn ℝ ∞ (PhysicalWaveSum.physicalQ h) PhysicalWaveSum.preterminal :=
    fun w hw => (PhysicalWaveSum.physicalQ_smoothAt hh hh1 hw).contDiffWithinAt
  have hqpos := fun w hw => PhysicalWaveSum.physicalQ_pos hh hh1 (w := w) hw
  exact ⟨a, hal, hap, had, ham, hat, hb,
    ⟨SolenoidalDiagonal.potentialSum_contDiffOn hat PhysicalWaveSum.preterminal_open hqpos hq hA,
      SolenoidalDiagonal.potentialSum_contDiffOn hat PhysicalWaveSum.preterminal_open hqpos hq hB,
      SolenoidalDiagonal.potentialSum_contDiffOn hat PhysicalWaveSum.preterminal_open hqpos hq hP⟩⟩

section LocalStages

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Reattach the actual initial cutoff term to a smooth positive sum.
The initial field only needs smoothness on its original valid q-domain. -/
theorem full_sum_smooth_of_initial {h qbig : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {a : ℕ → ℕ} (ha : StrictMono a) (ha0 : 0 < a 0) (hrecip : 1 / (a 0 : ℝ) < qbig)
    {A : ℕ → SpaceTime → V}
    (hA0 : ContDiffOn ℝ ∞ (A 0) (CutStageEstimates.physicalSublevel h qbig))
    (hp : ContDiffOn ℝ ∞
      (SolenoidalDiagonal.potentialSum (fun j => (a j : ℝ)) (PhysicalWaveSum.physicalQ h)
        (CutStageEstimates.positiveStages A)) PhysicalWaveSum.preterminal) :
    ContDiffOn ℝ ∞
      (SolenoidalDiagonal.potentialSum (fun j => (a j : ℝ)) (PhysicalWaveSum.physicalQ h) A)
      PhysicalWaveSum.preterminal := by
  have hq : ContDiffOn ℝ ∞ (PhysicalWaveSum.physicalQ h) PhysicalWaveSum.preterminal :=
    fun w hw => (PhysicalWaveSum.physicalQ_smoothAt hh hh1 hw).contDiffWithinAt
  have ha0' : (0 : ℝ) < a 0 := by exact_mod_cast ha0
  have hgap : 1 < (a 0 : ℝ) * qbig := by
    simpa only [mul_comm] using (div_lt_iff₀ ha0').mp hrecip
  have hzero := CutStageEstimates.cut_product_smooth_of_sublevel
    PhysicalWaveSum.preterminal_open hq hA0 ha0' hgap
  exact (hzero.add hp).congr (fun w hw => physical_initial_split hh hh1 ha A hw)

/-- Every full sum, including stage zero, is genuinely zero beyond the
original validity range. No value of the uncut totalization is used there. -/
theorem full_sum_zero_of_sublevel_le {h qbig : ℝ} {a : ℕ → ℕ}
    (ha : ∀ j, 0 < a j) (hrecip : ∀ j, 1 / (a j : ℝ) < qbig)
    (A : ℕ → SpaceTime → V) {w : SpaceTime} (hw : qbig ≤ PhysicalWaveSum.physicalQ h w) :
    SolenoidalDiagonal.potentialSum (fun j => (a j : ℝ)) (PhysicalWaveSum.physicalQ h) A w = 0 := by
  have hz : ∀ j, SolenoidalDiagonal.cutStage (fun j => (a j : ℝ))
      (PhysicalWaveSum.physicalQ h) A j w = 0 := by
    intro j
    have hz := SmoothCutoffs.scaledCutoff_zero_of_inv_le
      (by exact_mod_cast ha j : (0 : ℝ) < a j) ((hrecip j).le.trans hw)
    simp only [SolenoidalDiagonal.cutStage, hz, zero_smul]
  simp only [SolenoidalDiagonal.potentialSum, hz, tsum_zero]

end LocalStages

/-- Local-q version for all three literal families. The initial scale
places every support inside the validity region; the full sums, with stage
zero retained, are smooth on all preterminal spacetime. -/
theorem exists_three_component_local_schedule {h qbig : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (hqbig : 0 < qbig)
    {S : Set SpaceTime} (hS : S ⊆ PhysicalWaveSum.preterminal)
    {A B : ℕ → VelocityField} {P : ℕ → PressureField}
    (hA : ∀ j, ContDiffOn ℝ ∞ (A j) (CutStageEstimates.physicalSublevel h qbig))
    (hB : ∀ j, ContDiffOn ℝ ∞ (B j) (CutStageEstimates.physicalSublevel h qbig))
    (hP : ∀ j, ContDiffOn ℝ ∞ (P j) (CutStageEstimates.physicalSublevel h qbig))
    (g LA LB LP : ℕ → ℝ) (CA CB CP pA pB pP : ℕ → ℕ → ℝ)
    (rawA : CutStageEstimates.RawStageBounds (PhysicalWaveSum.physicalQ h) A g LA CA pA
      (S ∩ CutStageEstimates.physicalSublevel h qbig))
    (rawB : CutStageEstimates.RawStageBounds (PhysicalWaveSum.physicalQ h) B g LB CB pB
      (S ∩ CutStageEstimates.physicalSublevel h qbig))
    (rawP : CutStageEstimates.RawStageBounds (PhysicalWaveSum.physicalQ h) P g LP CP pP
      (S ∩ CutStageEstimates.physicalSublevel h qbig))
    (hg : ∀ j, 1 ≤ j → 0 < g j) (lower : ℕ) :
    ∃ a : ℕ → ℕ, lower ≤ a 0 ∧ (∀ j, 0 < a j) ∧
      (∀ j, 2 * a j ≤ a (j + 1)) ∧ StrictMono a ∧
      Tendsto (fun j => (a j : ℝ)) atTop atTop ∧
      (∀ j, 1 / (a j : ℝ) < qbig) ∧
      ThreeCutBounds a h A B P (fun j => g j / 2) (commonLoss LA LB LP) S ∧
      ThreeSmoothSums a h A B P := by
  have hs : ∀ c j, 1 ≤ j → ContDiffOn ℝ ∞ (family A B P c j)
      (CutStageEstimates.physicalSublevel h qbig) := by
    intro c j _
    fin_cases c
    · exact hA j
    · exact hB j
    · exact hP j
  obtain ⟨a, hal, hap, had, ham, hat, hrecip, hb⟩ :=
    CutStageEstimates.exists_physical_local_diagonal_cut_bounds hh hh1 hqbig hS hs
      g (commonRawLoss LA LB LP)
      (scalarFamily (fun j m => |CA j m|) (fun j m => |CB j m|) (fun j m => |CP j m|))
      (scalarFamily pA pB pP)
      (family_raw_bounds (fun w hw => PhysicalWaveSum.physicalQ_pos hh hh1 hw.2.1)
        rawA rawB rawP) hg lower
  refine ⟨a, hal, hap, had, ham, hat, hrecip,
    ⟨cut_bounds_of_positiveStages (hb Component.potential).1,
      cut_bounds_of_positiveStages (hb Component.direct).1,
      cut_bounds_of_positiveStages (hb Component.pressure).1⟩, ?_⟩
  exact ⟨full_sum_smooth_of_initial hh hh1 ham (hap 0) (hrecip 0) (hA 0) (hb Component.potential).2,
    full_sum_smooth_of_initial hh hh1 ham (hap 0) (hrecip 0) (hB 0) (hb Component.direct).2,
    full_sum_smooth_of_initial hh hh1 ham (hap 0) (hrecip 0) (hP 0) (hb Component.pressure).2⟩

end NavierStokes.MixedDiagonalSchedule
