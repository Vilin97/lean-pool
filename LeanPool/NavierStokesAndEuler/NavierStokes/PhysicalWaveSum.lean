/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.PhysicalGraphBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.CommonCoverSolve
public import LeanPool.NavierStokesAndEuler.NavierStokes.SquaredPartition
public import LeanPool.NavierStokesAndEuler.NavierStokes.SimilarityProfile

/-!
# Physical waves on common covers and locally finite label sums

Cover changes are the actual powers of `J_g`. Bounds use actual Fréchet
derivatives and the constructed dyadic and spatial masks.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.PhysicalWaveSum

open Set Function Filter
open ProblemStatement
open scoped Topology ContDiff BigOperators


/-- Plane: an abbreviation for `PhysicalGraphBounds.Plane`. -/
abbrev Plane := PhysicalGraphBounds.Plane
/-- Lift point: an abbreviation for `PhysicalGraphBounds.LiftPoint`. -/
abbrev LiftPoint := PhysicalGraphBounds.LiftPoint
/-- Label: an abbreviation for `SlotColoring.Label`. -/
abbrev Label := SlotColoring.Label
/-- Position: an abbreviation for `SlotColoring.Position`. -/
abbrev Position := SlotColoring.Position

private theorem nat_le_infty (k : ℕ) : (k : WithTop ℕ∞) ≤ ∞ :=
  WithTop.coe_le_coe.mpr le_top

/-- Change only the auxiliary coordinate from native to common level. -/
noncomputable def downLift (d : ℕ) : LiftPoint →L[ℝ] LiftPoint :=
  (ContinuousLinearMap.id ℝ PhysicalGraphBounds.ChartPoint).prodMap
    ((CommonCoverSolve.coverPower d).symm : Plane →L[ℝ] Plane)

/-- Up lift, given by `(ContinuousLinearMap.id ℝ PhysicalGraphBounds.ChartPoint).prodMap
(CommonCoverSolve.coverPower d : Plane →L[ℝ] Plane)`. -/
noncomputable def upLift (d : ℕ) : LiftPoint →L[ℝ] LiftPoint :=
  (ContinuousLinearMap.id ℝ PhysicalGraphBounds.ChartPoint).prodMap
    (CommonCoverSolve.coverPower d : Plane →L[ℝ] Plane)

@[simp] theorem downLift_apply (d : ℕ) (y : LiftPoint) :
    downLift d y = (y.1, (CommonCoverSolve.coverPower d).symm y.2) := rfl

@[simp] theorem upLift_apply (d : ℕ) (y : LiftPoint) :
    upLift d y = (y.1, CommonCoverSolve.coverPower d y.2) := rfl

theorem up_down (d : ℕ) (y : LiftPoint) : upLift d (downLift d y) = y := by simp
theorem down_up (d : ℕ) (y : LiftPoint) : downLift d (upLift d y) = y := by simp

/-- Cover bound, given by `1 + CommonCoverSolve.coveringBound Δ`. -/
noncomputable def coverBound (Δ : ℕ) : ℝ := 1 + CommonCoverSolve.coveringBound Δ

theorem coverBound_ge_one (Δ : ℕ) : 1 ≤ coverBound Δ := by
  unfold coverBound
  linarith [CommonCoverSolve.coveringBound_pos Δ]

theorem norm_downLift_le {d Δ : ℕ} (hd : d ≤ Δ) : ‖downLift d‖ ≤ coverBound Δ := by
  have hK := coverBound_ge_one Δ
  have hc := CommonCoverSolve.inverseCoveringNorm_le_bound hd
  refine ContinuousLinearMap.opNorm_le_bound _ (by linarith) ?_
  intro y
  rw [downLift_apply, Prod.norm_def]
  apply max_le
  · exact (norm_fst_le y).trans (le_mul_of_one_le_left (norm_nonneg y) hK)
  · calc
      _ ≤ ‖((CommonCoverSolve.coverPower d).symm : Plane →L[ℝ] Plane)‖ * ‖y.2‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ CommonCoverSolve.coveringBound Δ * ‖y‖ :=
        mul_le_mul hc (norm_snd_le y) (norm_nonneg _) (CommonCoverSolve.coveringBound_pos Δ).le
      _ ≤ _ := by unfold coverBound; nlinarith [norm_nonneg y]

theorem norm_upLift_le {d Δ : ℕ} (hd : d ≤ Δ) : ‖upLift d‖ ≤ coverBound Δ := by
  have hK := coverBound_ge_one Δ
  have hc := CommonCoverSolve.coveringNorm_le_bound hd
  refine ContinuousLinearMap.opNorm_le_bound _ (by linarith) ?_
  intro y
  rw [upLift_apply, Prod.norm_def]
  apply max_le
  · exact (norm_fst_le y).trans (le_mul_of_one_le_left (norm_nonneg y) hK)
  · calc
      _ ≤ ‖(CommonCoverSolve.coverPower d : Plane →L[ℝ] Plane)‖ * ‖y.2‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ CommonCoverSolve.coveringBound Δ * ‖y‖ :=
        mul_le_mul hc (norm_snd_le y) (norm_nonneg _) (CommonCoverSolve.coveringBound_pos Δ).le
      _ ≤ _ := by unfold coverBound; nlinarith [norm_nonneg y]

/-- Common lift, given by `downLift d ∘ PhysicalGraphBounds.physicalLift h n`. -/
noncomputable def commonLift (h : ℝ) (n d : ℕ) : SpaceTime → LiftPoint :=
  downLift d ∘ PhysicalGraphBounds.physicalLift h n

/-- The changed coordinate is exactly `J_g^(i(n)-d) Y`, when the gap does
not exceed the native index. No periodicity of the source is assumed. -/
theorem commonLift_formula (h : ℝ) (n d : ℕ) (hd : d ≤ ChartScales.nativeIndex h n)
    (w : SpaceTime) :
    commonLift h n d w =
      (PhysicalGraphBounds.physicalChart h n w,
        (SlotGeometry.cover ^ (ChartScales.nativeIndex h n - d))
          (PhysicalGraphBounds.radialProfile (ChartScales.radialExponent h)
              (PhysicalGraphBounds.radialProjection w) +
            w.1 • PhysicalGraphBounds.timeDirection)) := by
  apply Prod.ext
  · rfl
  · apply (CommonCoverSolve.coverPower d).injective
    simp only [commonLift, comp_apply, downLift_apply, PhysicalGraphBounds.physicalLift,
      ContinuousLinearEquiv.apply_symm_apply, CommonCoverSolve.coverPower_apply]
    rw [← _root_.mul_apply_eq_comp, ← pow_add, Nat.add_sub_of_le hd]
    rfl

theorem commonLift_smoothAt (h : ℝ) (n d : ℕ) {w : SpaceTime}
    (hw : PhysicalGraphBounds.radialProjection w ≠ 0) : ContDiffAt ℝ ∞ (commonLift h n d) w :=
  (downLift d).contDiff.contDiffAt.comp w
    ((PhysicalGraphBounds.physicalChart_smooth h n).contDiffAt.prodMk
        (PhysicalGraphBounds.contDiffAt_nativeGraph h n hw))

theorem downLift_jet_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : LiftPoint → E} (hf : ContDiff ℝ ∞ f) {d Δ m : ℕ} (hd : d ≤ Δ)
    (y : LiftPoint) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ i ≤ m, ‖iteratedFDeriv ℝ i f (downLift d y)‖ ≤ B) :
    ∀ i ≤ m, ‖iteratedFDeriv ℝ i (f ∘ downLift d) y‖ ≤ B * coverBound Δ ^ m := by
  intro i hi
  have h := PhysicalGraphBounds.norm_jet_comp_linear (x := y) isOpen_univ hf.contDiffOn
    (downLift d) (mem_univ _) i
  apply h.trans
  exact mul_le_mul (hb i hi)
    ((pow_le_pow_left₀ (norm_nonneg _) (norm_downLift_le hd) i).trans
      (pow_le_pow_right₀ (coverBound_ge_one Δ) hi)) (by positivity) hB

/-- Common-cover descent changes the constant, preserving the native
graph loss and arbitrary input gain. The source may live only on the
coarsest covering torus. -/
theorem common_stripped_physical_bound {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h a b : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1 / 2) (ha : 0 < a)
    (Δ m : ℕ) (g e A : ℝ) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 4 ≤ n → ∀ d : ℕ, d ≤ Δ →
      ∀ w : SpaceTime, PhysicalGraphBounds.scaledRadial n w ∈ PhysicalGraphBounds.annulus a b →
          |w.1| ≤ 1 →
      ∀ q : ℝ, 0 < q → q / 2 ≤ ChartScales.Q n → ChartScales.Q n ≤ 2 * q →
      ∀ f : LiftPoint → E, ContDiff ℝ ∞ f →
      (∀ i ≤ m, ‖iteratedFDeriv ℝ i f (commonLift h n d w)‖ ≤
        A * ChartScales.Q n ^ g * ChartScales.S n ^ e) →
      ‖iteratedFDeriv ℝ m (f ∘ commonLift h n d) w‖ ≤
        C * q ^ (g - (PhysicalGraphBounds.graphLoss m + 1)) := by
  have hK : 0 ≤ coverBound Δ := zero_le_one.trans (coverBound_ge_one Δ)
  obtain ⟨C, hC, hb⟩ := PhysicalGraphBounds.stripped_class_physical_bound (E := E) (b := b) hh hh1
      ha m
    g e (A * coverBound Δ ^ m) (by positivity)
  refine ⟨C, hC, ?_⟩
  intro n hn d hd w hw ht q hq hlo hhi f hf hfb
  have hQ := ChartScales.Q_pos n
  have hS := ChartScales.S_pos (show 1 ≤ n by omega)
  apply hb n hn w hw ht q hq hlo hhi (f ∘ downLift d) (hf.comp (downLift d).contDiff)
  intro i hi
  have h := downLift_jet_bound hf hd (PhysicalGraphBounds.physicalLift h n w)
    (B := A * ChartScales.Q n ^ g * ChartScales.S n ^ e) (by positivity) hfb i hi
  exact h.trans_eq (by ring)

/-- Native phase data remain distinct from a source on a common cover. -/
structure CarrierData where
  /-- Chart of `CarrierData`, of type `PolarCharts.Index`. -/
  chart : PolarCharts.Index
  /-- Center of `CarrierData`, of type `Plane`. -/
  center : Plane
  /-- Angular of `CarrierData`, of type `ℝ`. -/
  angular : ℝ
  /-- Axial of `CarrierData`, of type `ℝ`. -/
  axial : ℝ
  /-- Radial of `CarrierData`, of type `ℝ`. -/
  radial : ℝ
  /-- F of `CarrierData`, of type `PhysicalGraphBounds.Slow → ℝ`. -/
  F : PhysicalGraphBounds.Slow → ℝ
  /-- Geometric data of `CarrierData`, of type `PhysicalGraphBounds.Slow → ℝ`. -/
  G : PhysicalGraphBounds.Slow → ℝ

/-- Phase, given by `PhysicalGraphBounds.liftedPhase (PolarCharts.chart a c.chart) h n c.center
r0 c.angular c.axial c.radial c.F c.G`. -/
noncomputable def CarrierData.phase (c : CarrierData) (a h : ℝ) (n : ℕ) (r0 : ℝ) :
    LiftPoint → ℝ :=
  PhysicalGraphBounds.liftedPhase (PolarCharts.chart a c.chart) h n c.center r0
    c.angular c.axial c.radial c.F c.G

/-- Common wave, constructed using `amp`. -/
noncomputable def commonWave (a h : ℝ) (n d : ℕ) (r0 : ℝ) (c : CarrierData)
    (amp : LiftPoint → ℂ) (j : ℤ) (w : SpaceTime) : ℂ :=
  amp (commonLift h n d w) *
    PhysicalGraphBounds.character ((ChartScales.carrier h n : ℝ) * (j : ℝ))
      (c.phase a h n r0 (PhysicalGraphBounds.physicalLift h n w))

theorem commonWave_smoothAt {a : ℝ} (ha : 0 < a) (h : ℝ) (n d : ℕ) (r0 : ℝ)
    (c : CarrierData) {amp : LiftPoint → ℂ} (hamp : ContDiff ℝ ∞ amp)
    (hF : ContDiff ℝ ∞ c.F) (hG : ContDiff ℝ ∞ c.G) (j : ℤ) {w : SpaceTime}
    (hw : PhysicalGraphBounds.radialProjection w ≠ 0) :
    ContDiffAt ℝ ∞ (commonWave a h n d r0 c amp j) w := by
  have hp := PhysicalGraphBounds.liftedPhase_smooth (PolarCharts.chart_contDiff ha c.chart)
    h n c.center r0 c.angular c.axial c.radial hF hG
  have hl := (PhysicalGraphBounds.physicalChart_smooth h n).contDiffAt.prodMk
    (PhysicalGraphBounds.contDiffAt_nativeGraph h n hw)
  exact (hamp.contDiffAt.comp w (commonLift_smoothAt h n d hw)).mul
    ((PhysicalGraphBounds.character_smooth _).contDiffAt.comp w (hp.contDiffAt.comp w hl))

/-- The literal native phase may multiply an arbitrary common-cover
amplitude. Bounded inverse-cover changes add only the factor `coverBound^m`
to the stripped constant. -/
theorem common_carrier_physical_bound {h a b Z r0 P B eBase : ℝ}
    (hh : 0 ≤ h) (hh1 : h ≤ 1 / 2) (ha : 0 < a)
    (hZ : 0 ≤ Z) (hr0 : 0 ≤ r0) (hP : 1 ≤ P) (hB : 1 ≤ B) (heBase : 0 ≤ eBase)
    (Δ m : ℕ) (g eAmp A H : ℝ) (hA : 0 ≤ A) (hH : 0 ≤ H) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 4 ≤ n → ∀ d : ℕ, d ≤ Δ →
      ∀ w : SpaceTime, PhysicalGraphBounds.scaledRadial n w ∈ PhysicalGraphBounds.annulus a b →
      |w.1| ≤ 1 → ‖PhysicalGraphBounds.liftZT (PhysicalGraphBounds.physicalLift h n w)‖ ≤ Z →
      ∀ q : ℝ, 0 < q → q / 2 ≤ ChartScales.Q n → ChartScales.Q n ≤ 2 * q →
      ∀ (c : CarrierData) (amp : LiftPoint → ℂ) (j : ℤ),
      |c.angular| ≤ P → |c.axial| ≤ P → |c.radial| ≤ P →
      |PhysicalGraphBounds.etaCoordinate (PhysicalGraphBounds.nativeGraph h n w - c.center)| ≤ r0 →
      ContDiff ℝ ∞ amp → ContDiff ℝ ∞ c.F → ContDiff ℝ ∞ c.G → |(j : ℝ)| ≤ H →
      (∀ i ≤ m, ‖iteratedFDeriv ℝ i amp (commonLift h n d w)‖ ≤
        A * ChartScales.Q n ^ g * ChartScales.S n ^ eAmp) →
      (∀ i ≤ m, ‖iteratedFDeriv ℝ i c.F
        (PhysicalGraphBounds.slotMap (PolarCharts.chart a c.chart)
          (ChartScales.timeCoefficient h n) c.center r0 (PhysicalGraphBounds.physicalLift h n
              w)).1‖ ≤
            B * ChartScales.S n ^ eBase) →
      (∀ i ≤ m, ‖iteratedFDeriv ℝ i c.G
        (PhysicalGraphBounds.slotMap (PolarCharts.chart a c.chart)
          (ChartScales.timeCoefficient h n) c.center r0 (PhysicalGraphBounds.physicalLift h n
              w)).1‖ ≤
            B * ChartScales.S n ^ eBase) →
      ‖iteratedFDeriv ℝ m (commonWave a h n d r0 c amp j) w‖ ≤
        C * q ^ (g - PhysicalGraphBounds.waveLoss h m) := by
  have hK : 0 ≤ coverBound Δ := zero_le_one.trans (coverBound_ge_one Δ)
  obtain ⟨C, hC, hb⟩ := PhysicalGraphBounds.native_carrier_physical_bound (b := b)
    hh hh1 ha hZ hr0 hP hB heBase m g eAmp (A * coverBound Δ ^ m) H (by positivity) hH
  refine ⟨C, hC, ?_⟩
  intro n hn d hd w hw ht hz q hq hlo hhi c amp j hp hpz hx0 hslot hamp hF hG hj hab hFb hGb
  have hQ := ChartScales.Q_pos n
  have hS := ChartScales.S_pos (show 1 ≤ n by omega)
  apply hb n hn w hw ht hz q hq hlo hhi c.chart c.center c.angular c.axial c.radial hp hpz hx0 hslot
    (amp ∘ downLift d) c.F c.G j (hamp.comp (downLift d).contDiff) hF hG hj
  · intro i hi
    have hh := downLift_jet_bound hamp hd (PhysicalGraphBounds.physicalLift h n w)
      (B := A * ChartScales.Q n ^ g * ChartScales.S n ^ eAmp) (by positivity) hab i hi
    exact hh.trans_eq (by ring)
  · exact hFb
  · exact hGb

/-- Closed supports of the actual dyadic and slow masks. -/
noncomputable def labelRegion (D : ℝ) (L : Label) : Set (ℝ × Position) :=
  tsupport (SquaredPartition.dyadicMask (L.1 : ℤ)) ×ˢ
    tsupport (SquaredPartition.physicalSlowMask D L.1 L.2.1)

theorem labelRegion_closed (D : ℝ) (L : Label) : IsClosed (labelRegion D L) :=
  isClosed_closure.prod isClosed_closure

/-- Physical mask, given by `SquaredPartition.dyadicMask (L.1 : ℤ) z.1 *
SquaredPartition.physicalSlowMask D L.1 L.2.1 z.2`. -/
noncomputable def physicalMask (D : ℝ) (L : Label) (z : ℝ × Position) : ℝ :=
  SquaredPartition.dyadicMask (L.1 : ℤ) z.1 *
    SquaredPartition.physicalSlowMask D L.1 L.2.1 z.2

theorem physicalMask_support_subset (D : ℝ) (L : Label) :
    support (physicalMask D L) ⊆ labelRegion D L := by
  intro z hz
  obtain ⟨hd, hs⟩ := mul_ne_zero_iff.mp hz
  exact ⟨subset_tsupport _ hd, subset_tsupport _ hs⟩

theorem physicalMask_tsupport_subset (D : ℝ) (L : Label) :
    tsupport (physicalMask D L) ⊆ labelRegion D L :=
  closure_minimal (physicalMask_support_subset D L) (labelRegion_closed D L)

theorem labelRegion_band {D : ℝ} {L : Label} {z : ℝ × Position}
    (hz : z ∈ labelRegion D L) :
    ChartScales.Q L.1 / 2 ≤ z.1 ∧ z.1 ≤ 2 * ChartScales.Q L.1 := by
  simpa only [SquaredPartition.dyadicMask_tsupport, SquaredPartition.integerQ_nat, mem_Icc]
    using hz.1

theorem labelRegion_active_relation {D : ℝ} {L : Label} {z : ℝ × Position}
    (hz : z ∈ labelRegion D L) : z.1 / 2 ≤ ChartScales.Q L.1 ∧ ChartScales.Q L.1 ≤ 2 * z.1 := by
  have hb := labelRegion_band hz
  constructor <;> linarith [hb.1, hb.2]

theorem logCoordinate_in_band {q : ℝ} (hq : 0 < q) {n : ℕ}
    (hlo : ChartScales.Q n / 2 ≤ q) (hhi : q ≤ 2 * ChartScales.Q n) :
    SquaredPartition.logCoordinate q ∈ Icc ((n : ℝ) - 1) ((n : ℝ) + 1) := by
  have hQ := ChartScales.Q_pos n
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogQ : Real.log (ChartScales.Q n) = -(n : ℝ) * Real.log 2 := by
    rw [← SquaredPartition.integerQ_nat, SquaredPartition.log_integerQ]
    simp only [Int.cast_natCast]
  have hl := Real.log_le_log (div_pos hQ (by norm_num : (0 : ℝ) < 2)) hlo
  have hu := Real.log_le_log hq hhi
  rw [Real.log_div hQ.ne' (by norm_num : (2 : ℝ) ≠ 0), hlogQ] at hl
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hQ.ne', hlogQ] at hu
  change (n : ℝ) - 1 ≤ -Real.log q / Real.log 2 ∧ -Real.log q / Real.log 2 ≤ (n : ℝ) + 1
  constructor
  · apply (le_div_iff₀ h2).mpr
    nlinarith
  · apply (div_le_iff₀ h2).mpr
    nlinarith

theorem labelRegion_adjacency {D : ℝ} {L M : Label} {z : ℝ × Position}
    (hq : 0 < z.1) (hL : 1 ≤ L.1) (hM : 1 ≤ M.1) (hne : L ≠ M)
    (hzL : z ∈ labelRegion D L) (hzM : z ∈ labelRegion D M) : SlotColoring.Adj D L M := by
  have hl := logCoordinate_in_band hq (labelRegion_band hzL).1 (labelRegion_band hzL).2
  have hm := logCoordinate_in_band hq (labelRegion_band hzM).1 (labelRegion_band hzM).2
  have hLM : L.1 ≤ M.1 + 4 := by
    have h : (L.1 : ℝ) ≤ (M.1 : ℝ) + 4 := by linarith [hl.1, hm.2]
    exact_mod_cast h
  have hML : M.1 ≤ L.1 + 4 := by
    have h : (M.1 : ℝ) ≤ (L.1 : ℝ) + 4 := by linarith [hm.1, hl.2]
    exact_mod_cast h
  exact ⟨hL, hM, hne, hLM, hML, z.2,
    SquaredPartition.physicalSlowMask_tsupport_subset_physicalBox D hL _ _ hzL.2,
    SquaredPartition.physicalSlowMask_tsupport_subset_physicalBox D hM _ _ hzM.2⟩

theorem labelRegion_color_injective {D : ℝ} {z : ℝ × Position} (hq : 0 < z.1) :
    Set.InjOn SlotColoring.colorData {L : Label | 1 ≤ L.1 ∧ z ∈ labelRegion D L} := by
  intro L hL M hM hc
  by_contra hne
  exact SlotColoring.colorData_proper D
    (labelRegion_adjacency hq hL.1 hM.1 hne hL.2 hM.2) hc

/-- The constructed coloring bounds overlap even on closed derivative
supports. In particular no generic bounded-overlap hypothesis is used. -/
theorem labelRegion_card_le {D : ℝ} {z : ℝ × Position} (hq : 0 < z.1)
    (s : Finset Label) (hs : ∀ L ∈ s, 1 ≤ L.1 ∧ z ∈ labelRegion D L) : s.card ≤ 2250 := by
  classical
  have hi : Set.InjOn SlotColoring.colorData (s : Set Label) :=
    (labelRegion_color_injective hq).mono hs
  have hc := Finset.card_le_card_of_injOn (t := Finset.univ) SlotColoring.colorData
    (fun L _ => Finset.mem_univ _) hi
  simpa only [Finset.card_univ, SlotColoring.palette_card] using hc

/-- Positive param: an abbreviation for `Ioi (0 : ℝ) × Position`. -/
abbrev PositiveParam := Ioi (0 : ℝ) × Position

theorem dyadic_closed_locallyFinite :
    LocallyFinite fun n : ℕ => {q : Ioi (0 : ℝ) |
      (q : ℝ) ∈ tsupport (SquaredPartition.dyadicMask (n : ℤ))} := by
  have hc : Continuous (fun q : Ioi (0 : ℝ) => SquaredPartition.logCoordinate q) :=
    ((continuous_subtype_val.log (fun q => q.property.ne')).neg).div_const (Real.log 2)
  have hl := (SquaredPartition.lineMask_locallyFinite.comp_injective
      Int.ofNat_injective).preimage_continuous hc
  apply hl.subset
  intro n q hq
  change SquaredPartition.logCoordinate q ∈ tsupport (SquaredPartition.lineMask (n : ℤ))
  rw [SquaredPartition.lineMask_tsupport]
  have hb : ChartScales.Q n / 2 ≤ (q : ℝ) ∧ (q : ℝ) ≤ 2 * ChartScales.Q n := by
    simp only [SquaredPartition.dyadicMask_tsupport, SquaredPartition.integerQ_nat, mem_Icc] at hq
    exact hq
  simpa only [Int.cast_natCast] using logCoordinate_in_band q.property hb.1 hb.2

theorem labelRegion_locallyFinite (D : ℝ) :
    LocallyFinite fun L : Label => {z : PositiveParam | ((z.1 : ℝ), z.2) ∈ labelRegion D L} := by
  have hb := dyadic_closed_locallyFinite.preimage_continuous
    (continuous_fst : Continuous (Prod.fst : PositiveParam → Ioi (0 : ℝ)))
  have hg (n : ℕ) : LocallyFinite fun k : SlotColoring.Grid =>
      {z : PositiveParam | z.2 ∈ tsupport (SquaredPartition.physicalSlowMask D n k)} :=
    (SquaredPartition.physicalSlowMask_locallyFinite D n).closure.preimage_continuous continuous_snd
  have hs (n : ℕ) : LocallyFinite fun k : SlotColoring.Grid × Bool =>
      {z : PositiveParam | z.2 ∈ tsupport (SquaredPartition.physicalSlowMask D n k.1)} := by
    simpa only [inter_univ] using SquaredPartition.locallyFinite_pair_inter (hg n)
      (fun _ => locallyFinite_of_finite (fun _ : Bool => (univ : Set PositiveParam)))
  exact SquaredPartition.locallyFinite_pair_inter hb hs

/-- Band label: an abbreviation for `{L : Label // 4 ≤ L.1}`. -/
abbrev BandLabel := {L : Label // 4 ≤ L.1}
/-- Harmonic: an abbreviation for `↥(Finset.Icc (-(H : ℤ)) (H : ℤ))`. -/
abbrev Harmonic (H : ℕ) := ↥(Finset.Icc (-(H : ℤ)) (H : ℤ))
/-- Wave index: an abbreviation for `BandLabel × Harmonic H`. -/
abbrev WaveIndex (H : ℕ) := BandLabel × Harmonic H

theorem harmonic_bound {H : ℕ} (j : Harmonic H) : |((j : ℤ) : ℝ)| ≤ (H : ℝ) := by
  have hj : |(j : ℤ)| ≤ (H : ℤ) := abs_le.mpr (Finset.mem_Icc.mp j.property)
  exact_mod_cast hj

theorem harmonic_card (H : ℕ) : Fintype.card (Harmonic H) = 2 * H + 1 := by
  simp only [Harmonic, Fintype.card_coe, Int.card_Icc]
  omega

/-- Wave color, given by `(SlotColoring.colorData I.1.val, I.2)`. -/
noncomputable def waveColor {H : ℕ} (I : WaveIndex H) : SlotColoring.Palette × Harmonic H :=
  (SlotColoring.colorData I.1.val, I.2)

theorem waveRegion_card_le {D : ℝ} {H : ℕ} {z : ℝ × Position} (hq : 0 < z.1)
    (s : Finset (WaveIndex H)) (hs : ∀ I ∈ s, z ∈ labelRegion D I.1.val) :
    s.card ≤ 2250 * (2 * H + 1) := by
  classical
  have hi : Set.InjOn waveColor (s : Set (WaveIndex H)) := by
    intro I hI J hJ hcol
    change (SlotColoring.colorData I.1.val, I.2) = (SlotColoring.colorData J.1.val, J.2) at hcol
    have hlabel : I.1.val = J.1.val := labelRegion_color_injective hq
      ⟨by have := I.1.property; omega, hs I hI⟩
      ⟨by have := J.1.property; omega, hs J hJ⟩ (congrArg Prod.fst hcol)
    exact Prod.ext (Subtype.ext hlabel)
      (congrArg (fun z : SlotColoring.Palette × Harmonic H => z.2) hcol)
  have hf : Function.Injective (fun I : s => waveColor (H := H) I.val) := by
    intro I J he
    exact Subtype.ext (hi I.property J.property he)
  have hc := Fintype.card_le_of_injective (fun I : s => waveColor (H := H) I.val) hf
  calc
    s.card ≤ Fintype.card (SlotColoring.Palette × Harmonic H) := by
      simpa only [Fintype.card_coe] using hc
    _ = _ := by rw [Fintype.card_prod, SlotColoring.palette_card, harmonic_card]

theorem waveRegion_locallyFinite (D : ℝ) (H : ℕ) :
    LocallyFinite fun I : WaveIndex H =>
      {z : PositiveParam | ((z.1 : ℝ), z.2) ∈ labelRegion D I.1.val} := by
  have hb := (labelRegion_locallyFinite D).comp_injective
    (Subtype.val_injective : Function.Injective (fun L : BandLabel => L.val))
  simpa only [inter_univ, Function.comp_def] using SquaredPartition.locallyFinite_pair_inter hb
    (fun _ => locallyFinite_of_finite (fun _ : Harmonic H => (univ : Set PositiveParam)))

/-- Preterminal, given by `{w | w.1 < 1}`. -/
noncomputable def preterminal : Set SpaceTime := {w | w.1 < 1}

theorem preterminal_open : IsOpen preterminal := isOpen_lt continuous_fst continuous_const

/-- The actual similarity coordinate at a Cartesian spacetime point. -/
noncomputable def physicalQ (h : ℝ) (w : SpaceTime) : ℝ :=
  SimilarityProfile.q h (AxisymmetricFields.profilePoint w.1 w.2)

theorem physicalQ_pos {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {w : SpaceTime} (hw : w ∈ preterminal) : 0 < physicalQ h w :=
  SimilarityProfile.q_pos hh hh1 hw

theorem physicalQ_smoothAt {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {w : SpaceTime} (hw : w ∈ preterminal) : ContDiffAt ℝ ∞ (physicalQ h) w :=
  (SimilarityProfile.q_smoothAt (p := AxisymmetricFields.profilePoint w.1 w.2) hh hh1 hw).comp w
    AxisymmetricFields.contDiff_profilePoint.contDiffAt

/-- The three physical variables whose rescalings enter the slow masks. -/
noncomputable def physicalPosition (w : SpaceTime) : Position :=
  ![PolarCharts.radius (PhysicalGraphBounds.radialProjection w), w.2 2, 1 - w.1]

theorem physicalPosition_continuous : Continuous physicalPosition := by
  apply continuous_pi
  intro j
  fin_cases j
  · exact PolarCharts.radius_continuous.comp PhysicalGraphBounds.radialProjection.continuous
  · exact ((AxisymmetricFields.projection 2).continuous.comp continuous_snd)
  · exact continuous_const.sub continuous_fst

/-- Physical params, given by `(physicalQ h w, physicalPosition w)`. -/
noncomputable def physicalParams (h : ℝ) (w : SpaceTime) : ℝ × Position :=
  (physicalQ h w, physicalPosition w)

theorem physicalParams_continuousAt {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {w : SpaceTime} (hw : w ∈ preterminal) : ContinuousAt (physicalParams h) w :=
  (physicalQ_smoothAt hh hh1 hw).continuousAt.prodMk physicalPosition_continuous.continuousAt

/-- Positive params, given by `(⟨physicalQ h w, physicalQ_pos hh hh1 w.property⟩,
physicalPosition w)`. -/
noncomputable def positiveParams {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (w : preterminal) : PositiveParam :=
  (⟨physicalQ h w, physicalQ_pos hh hh1 w.property⟩, physicalPosition w)

theorem positiveParams_continuous {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2) :
    Continuous (positiveParams hh hh1) := by
  have hq : Continuous (fun w : preterminal => physicalQ h w) := by
    apply continuous_iff_continuousAt.mpr
    intro w
    exact (physicalQ_smoothAt hh hh1 w.property).continuousAt.comp continuousAt_subtype_val
  exact (hq.subtype_mk _).prodMk (physicalPosition_continuous.comp continuous_subtype_val)

theorem waveRegion_closed (D : ℝ) {H : ℕ} (I : WaveIndex H) :
    IsClosed {z : PositiveParam | ((z.1 : ℝ), z.2) ∈ labelRegion D I.1.val} :=
  (labelRegion_closed D I.1.val).preimage ((continuous_subtype_val.comp continuous_fst).prodMk
      continuous_snd)

/-- A locally finite closed family has a neighborhood with no new
indices beyond the finite family active at the point. -/
theorem active_neighborhood {ι X : Type*} [TopologicalSpace X]
    {V : ι → Set X} (hV : LocallyFinite V) (hc : ∀ i, IsClosed (V i)) (x : X) :
    ∃ s : Finset ι, (∀ i, i ∈ s ↔ x ∈ V i) ∧
      ∀ᶠ y in 𝓝 x, ∀ i, y ∈ V i → i ∈ s := by
  classical
  let s := (hV.point_finite x).toFinset
  refine ⟨s, fun i => (hV.point_finite x).mem_toFinset, ?_⟩
  filter_upwards [hV.iInter_compl_mem_nhds hc x] with y hy
  intro i hi
  by_contra hn
  have hx : x ∉ V i := by simpa [s] using hn
  exact (mem_iInter₂.mp hy i hx) hi

/-- Local finiteness is used only on the actual positive-`q` domain. -/
theorem physical_active_neighborhood {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (H : ℕ) {w : SpaceTime} (hw : w ∈ preterminal) :
    ∃ s : Finset (WaveIndex H),
      (∀ I, I ∈ s ↔ physicalParams h w ∈ labelRegion (CoordinateAlgebra.D h) I.1.val) ∧
      ∀ᶠ y in 𝓝 w, y ∈ preterminal ∧
        ∀ I, physicalParams h y ∈ labelRegion (CoordinateAlgebra.D h) I.1.val → I ∈ s := by
  obtain ⟨s, hs, hnear⟩ := active_neighborhood (waveRegion_locallyFinite (CoordinateAlgebra.D h) H)
    (waveRegion_closed (CoordinateAlgebra.D h)) (positiveParams hh hh1 ⟨w, hw⟩)
  have hsub : ∀ᶠ y : preterminal in 𝓝 (⟨w, hw⟩ : preterminal),
      ∀ I, physicalParams h y ∈ labelRegion (CoordinateAlgebra.D h) I.1.val → I ∈ s :=
    (positiveParams_continuous hh hh1).continuousAt hnear
  obtain ⟨U, hU, hUs⟩ := (mem_nhds_subtype preterminal ⟨w, hw⟩ _).mp hsub
  refine ⟨s, hs, ?_⟩
  filter_upwards [hU, preterminal_open.mem_nhds hw] with y hy hyt
  exact ⟨hyt, hUs (show (⟨y, hyt⟩ : preterminal) ∈ Subtype.val ⁻¹' U from hy)⟩

theorem iteratedFDeriv_eq_of_eventuallyEq {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f g : E → F} {x : E} (he : f =ᶠ[𝓝 x] g) (m : ℕ) :
    iteratedFDeriv ℝ m f x = iteratedFDeriv ℝ m g x := by
  have he' : f =ᶠ[𝓝[univ] x] g := by simpa only [nhdsWithin_univ] using he
  simpa only [iteratedFDerivWithin_univ] using he'.iteratedFDerivWithin_eq he.self_of_nhds m

theorem iteratedFDeriv_finset_sum_at {ι E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (s : Finset ι) {f : ι → E → F} {x : E} {m : ℕ}
    (hf : ∀ i ∈ s, ContDiffAt ℝ m (f i) x) :
    iteratedFDeriv ℝ m (fun y => ∑ i ∈ s, f i y) x =
      ∑ i ∈ s, iteratedFDeriv ℝ m (f i) x := by
  simpa only [iteratedFDerivWithin_univ] using
    iteratedFDerivWithin_fun_sum_apply uniqueDiffOn_univ (mem_univ x)
      (fun i hi => (hf i hi).contDiffWithinAt)

/-- A mask support hypothesis produces an actual local finite-sum identity.
The summands need not have any native-torus periodicity. -/
theorem masked_finsum_eventually {E : Type*} [AddCommMonoid E] {h : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) {H : ℕ} (f : WaveIndex H → SpaceTime → E)
    (hsupp : ∀ I y, y ∈ preterminal → f I y ≠ 0 →
      physicalParams h y ∈ labelRegion (CoordinateAlgebra.D h) I.1.val)
    {w : SpaceTime} (hw : w ∈ preterminal) :
    ∃ s : Finset (WaveIndex H),
      (∀ I, I ∈ s ↔ physicalParams h w ∈ labelRegion (CoordinateAlgebra.D h) I.1.val) ∧
      (fun y => ∑ᶠ I, f I y) =ᶠ[𝓝 w] fun y => ∑ I ∈ s, f I y := by
  obtain ⟨s, hs, hn⟩ := physical_active_neighborhood hh hh1 H hw
  refine ⟨s, hs, ?_⟩
  filter_upwards [hn] with y hy
  apply finsum_eq_sum_of_support_subset
  intro I hI
  exact hy.2 I (hsupp I y hy.1 hI)

theorem masked_finsum_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2) {H : ℕ}
    (f : WaveIndex H → SpaceTime → E)
    (hf : ∀ I w, w ∈ preterminal → ContDiffAt ℝ ∞ (f I) w)
    (hsupp : ∀ I y, y ∈ preterminal → f I y ≠ 0 →
      physicalParams h y ∈ labelRegion (CoordinateAlgebra.D h) I.1.val) :
    ContDiffOn ℝ ∞ (fun y => ∑ᶠ I, f I y) preterminal := by
  intro w hw
  obtain ⟨s, _, he⟩ := masked_finsum_eventually hh hh1 f hsupp hw
  exact ((ContDiffAt.sum (fun I _ => hf I w hw)).congr_of_eventuallyEq he).contDiffWithinAt

theorem masked_finsum_jet_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2) {H : ℕ}
    (f : WaveIndex H → SpaceTime → E)
    (hf : ∀ I w, w ∈ preterminal → ContDiffAt ℝ ∞ (f I) w)
    (hsupp : ∀ I y, y ∈ preterminal → f I y ≠ 0 →
      physicalParams h y ∈ labelRegion (CoordinateAlgebra.D h) I.1.val)
    {w : SpaceTime} (hw : w ∈ preterminal) (m : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ I, physicalParams h w ∈ labelRegion (CoordinateAlgebra.D h) I.1.val →
      ‖iteratedFDeriv ℝ m (f I) w‖ ≤ B) :
    ‖iteratedFDeriv ℝ m (fun y => ∑ᶠ I, f I y) w‖ ≤ (2250 * (2 * H + 1) : ℕ) * B := by
  classical
  obtain ⟨s, hs, he⟩ := masked_finsum_eventually hh hh1 f hsupp hw
  rw [iteratedFDeriv_eq_of_eventuallyEq he m,
    iteratedFDeriv_finset_sum_at s (fun I _ => (hf I w hw).of_le (nat_le_infty m))]
  calc
    _ ≤ ∑ I ∈ s, ‖iteratedFDeriv ℝ m (f I) w‖ := norm_sum_le _ _
    _ ≤ ∑ _I ∈ s, B := Finset.sum_le_sum (fun I hI => hb I ((hs I).mp hI))
    _ = (s.card : ℝ) * B := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by
      exact_mod_cast waveRegion_card_le (physicalQ_pos hh hh1 hw) s (fun I hI => (hs I).mp hI)) hB

/-- A closed input support condition remains true on the topological
support of a physical field. Only continuity at the point is needed. -/
theorem closed_property_on_tsupport {E X Y : Type*} [Zero E]
    [TopologicalSpace X] [TopologicalSpace Y] {f : X → E} {g : X → Y}
    {U : Set X} (hU : IsOpen U) {x : X} (hx : x ∈ U)
    (hg : ContinuousAt g x) {S : Set Y} (hS : IsClosed S)
    (hs : ∀ y ∈ U, f y ≠ 0 → g y ∈ S) (ht : x ∈ tsupport f) : g x ∈ S := by
  by_contra ho
  have he : f =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [hU.mem_nhds hx, hg (hS.isOpen_compl.mem_nhds ho)] with y hy hys
    by_contra hfy
    exact hys (hs y hy hfy)
  exact (notMem_tsupport_iff_eventuallyEq.mpr he) ht

theorem jet_zero_off_tsupport {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (m : ℕ) {x : E}
    (hx : x ∉ tsupport f) : iteratedFDeriv ℝ m f x = 0 := by
  by_contra hn
  exact hx ((tsupport_iteratedFDeriv_subset m) (subset_tsupport _ hn))

/-- With chart, given by `{c with chart := i}`. -/
noncomputable def CarrierData.withChart (c : CarrierData) (i : PolarCharts.Index) : CarrierData :=
  {c with chart := i}

/-- Choose chart, choosing the witness provided by `hi`. -/
noncomputable def chooseChart (a : ℝ) (x : Plane) : PolarCharts.Index := by
  classical
  exact if hi : ∃ i : PolarCharts.Index, x ∈ PolarCharts.chartDomain a i then Classical.choose hi
      else 0

theorem chooseChart_valid {a b : ℝ} (ha : 0 < a) {x : Plane}
    (hx : x ∈ PhysicalGraphBounds.annulus a b) : x ∈ PolarCharts.chartDomain a (chooseChart a x) :=
        by
  obtain ⟨i, hi⟩ := PolarCharts.annulus_covered ha hx
  have he : ∃ j : PolarCharts.Index, x ∈ PolarCharts.chartDomain a j :=
    ⟨i, PolarCharts.sector_subset_chartDomain ha i hi⟩
  simp only [chooseChart, dite_eq_left he]
  exact Classical.choose_spec he

/-- Polar carrier, given by `PhaseCalculus.harmonic k j ε c.angular c.axial c.radial c.F c.G
((rθ.1, zt), (rθ.2, v))`. -/
noncomputable def polarCarrier (c : CarrierData) (k : ℝ) (j : ℤ) (ε : ℝ)
    (zt : ℝ × ℝ) (v : ℝ) (rθ : Plane) : ℂ :=
  PhaseCalculus.harmonic k j ε c.angular c.axial c.radial c.F c.G ((rθ.1, zt), (rθ.2, v))

@[simp] theorem withChart_chart (c : CarrierData) (i : PolarCharts.Index) :
    (c.withChart i).chart = i := rfl

@[simp] theorem withChart_center (c : CarrierData) (i : PolarCharts.Index) :
    (c.withChart i).center = c.center := rfl

@[simp] theorem polarCarrier_withChart (c : CarrierData) (i : PolarCharts.Index)
    (k : ℝ) (j : ℤ) (ε : ℝ) (zt : ℝ × ℝ) (v : ℝ) :
    polarCarrier (c.withChart i) k j ε zt v = polarCarrier c k j ε zt v := rfl

theorem polarCarrier_periodic (c : CarrierData) (k : ℝ) (j : ℤ) (ε : ℝ)
    (zt : ℝ × ℝ) (v : ℝ) (m : ℤ) (hkp : k * c.angular = (m : ℝ)) :
    ∀ r : ℝ, Periodic (fun θ => polarCarrier c k j ε zt v (r, θ)) (2 * Real.pi) := by
  intro r
  exact PhaseCalculus.harmonic_theta_periodic k j m ε c.angular c.axial c.radial c.F c.G
    (r, zt) v hkp

theorem commonWave_polar (a h : ℝ) (n d : ℕ) (r0 : ℝ) (c : CarrierData)
    (amp : LiftPoint → ℂ) (j : ℤ) (w : SpaceTime) :
    commonWave a h n d r0 c amp j w = amp (commonLift h n d w) *
      polarCarrier c (ChartScales.carrier h n) j (ChartScales.epsilon h n)
        (PhysicalGraphBounds.liftZT (PhysicalGraphBounds.physicalLift h n w))
        (PhysicalGraphBounds.slotTime h n c.center r0 w)
        (PolarCharts.chart a c.chart (PhysicalGraphBounds.scaledRadial n w)) := by
  unfold commonWave CarrierData.phase PhysicalGraphBounds.liftedPhase
  rw [Function.comp_apply, PhysicalGraphBounds.character_phase_eq_harmonic,
    PhysicalGraphBounds.slotMap_formula, PhysicalGraphBounds.liftXY_physicalLift]
  rfl

theorem commonWave_charts_agree {a : ℝ} (ha : 0 < a) (h : ℝ) (n d : ℕ) (r0 : ℝ)
    (c : CarrierData) (amp : LiftPoint → ℂ) (j : ℤ) (w : SpaceTime)
    (m : ℤ) (hkp : (ChartScales.carrier h n : ℝ) * c.angular = (m : ℝ))
    (i k : PolarCharts.Index)
    (hi : PhysicalGraphBounds.scaledRadial n w ∈ PolarCharts.chartDomain a i)
    (hk : PhysicalGraphBounds.scaledRadial n w ∈ PolarCharts.chartDomain a k) :
    commonWave a h n d r0 (c.withChart i) amp j w =
      commonWave a h n d r0 (c.withChart k) amp j w := by
  rw [commonWave_polar, commonWave_polar]
  simp only [withChart_center, withChart_chart, polarCarrier_withChart]
  have hp := polarCarrier_periodic c (ChartScales.carrier h n : ℝ) j (ChartScales.epsilon h n)
    (PhysicalGraphBounds.liftZT (PhysicalGraphBounds.physicalLift h n w))
    (PhysicalGraphBounds.slotTime h n c.center r0 w) m hkp
  have he := PolarCharts.chart_periodic_agree ha
    (polarCarrier c (ChartScales.carrier h n) j (ChartScales.epsilon h n)
      (PhysicalGraphBounds.liftZT (PhysicalGraphBounds.physicalLift h n w))
      (PhysicalGraphBounds.slotTime h n c.center r0 w)) hp i k hi hk
  exact congrArg (fun z : ℂ => amp (commonLift h n d w) * z) he

/-- A genuine angular carrier: valid polar charts are selected pointwise;
the integer angular mode will prove that the selection is smooth. -/
noncomputable def globalWave (a h : ℝ) (n d : ℕ) (r0 : ℝ) (c : CarrierData)
    (amp : LiftPoint → ℂ) (j : ℤ) (w : SpaceTime) : ℂ :=
  commonWave a h n d r0 (c.withChart (chooseChart a (PhysicalGraphBounds.scaledRadial n w))) amp j w

theorem globalWave_eq_zero {a h r0 : ℝ} {n d : ℕ} {c : CarrierData}
    {amp : LiftPoint → ℂ} {j : ℤ} {w : SpaceTime} (hz : amp (commonLift h n d w) = 0) :
    globalWave a h n d r0 c amp j w = 0 := by simp only [globalWave, commonWave, hz, zero_mul]

theorem globalWave_eventually_common {a b h r0 : ℝ} (ha : 0 < a) (n d : ℕ)
    (c : CarrierData) (amp : LiftPoint → ℂ) (j : ℤ) (m : ℤ)
    (hkp : (ChartScales.carrier h n : ℝ) * c.angular = (m : ℝ))
    (hs : ∀ y, amp (commonLift h n d y) ≠ 0 →
      PhysicalGraphBounds.scaledRadial n y ∈ PhysicalGraphBounds.annulus a b)
    {w : SpaceTime} (i : PolarCharts.Index)
    (hi : PhysicalGraphBounds.scaledRadial n w ∈ PolarCharts.chartDomain a i) :
    globalWave a h n d r0 c amp j =ᶠ[𝓝 w] commonWave a h n d r0 (c.withChart i) amp j := by
  filter_upwards [(PhysicalGraphBounds.scaledRadial n).continuous.continuousAt
    ((PolarCharts.chartDomain_open a i).mem_nhds hi)] with y hy
  by_cases hz : amp (commonLift h n d y) = 0
  · simp only [globalWave, commonWave, hz, zero_mul]
  · exact commonWave_charts_agree ha h n d r0 c amp j y m hkp _ i (chooseChart_valid ha (hs y hz))
      hy

theorem globalWave_eventually_zero_off_annulus {a b h r0 : ℝ} {n d : ℕ}
    (c : CarrierData) (amp : LiftPoint → ℂ) (j : ℤ)
    (hs : ∀ y, amp (commonLift h n d y) ≠ 0 →
      PhysicalGraphBounds.scaledRadial n y ∈ PhysicalGraphBounds.annulus a b)
    {w : SpaceTime} (hw : PhysicalGraphBounds.scaledRadial n w ∉ PhysicalGraphBounds.annulus a b) :
    globalWave a h n d r0 c amp j =ᶠ[𝓝 w] fun _ => 0 := by
  filter_upwards [(PhysicalGraphBounds.scaledRadial n).continuous.continuousAt
    ((PhysicalGraphBounds.isCompact_annulus a b).isClosed.isOpen_compl.mem_nhds hw)] with y hy
  apply globalWave_eq_zero
  by_contra hn
  exact hy (hs y hn)

theorem globalWave_smooth {a b h r0 : ℝ} (ha : 0 < a) (n d : ℕ)
    (c : CarrierData) (amp : LiftPoint → ℂ) (j : ℤ) (m : ℤ)
    (hkp : (ChartScales.carrier h n : ℝ) * c.angular = (m : ℝ))
    (hamp : ContDiff ℝ ∞ amp) (hF : ContDiff ℝ ∞ c.F) (hG : ContDiff ℝ ∞ c.G)
    (hs : ∀ y, amp (commonLift h n d y) ≠ 0 →
      PhysicalGraphBounds.scaledRadial n y ∈ PhysicalGraphBounds.annulus a b) :
    ContDiff ℝ ∞ (globalWave a h n d r0 c amp j) := by
  apply contDiff_iff_contDiffAt.mpr
  intro w
  by_cases hw : PhysicalGraphBounds.scaledRadial n w ∈ PhysicalGraphBounds.annulus a b
  · let i := chooseChart a (PhysicalGraphBounds.scaledRadial n w)
    have hi : PhysicalGraphBounds.scaledRadial n w ∈ PolarCharts.chartDomain a i :=
        chooseChart_valid ha hw
    have he : globalWave a h n d r0 c amp j =ᶠ[𝓝 w] commonWave a h n d r0 (c.withChart i) amp j :=
      globalWave_eventually_common (r0 := r0) ha n d c amp j m hkp hs i hi
    have hc : ContDiffAt ℝ ∞ (commonWave a h n d r0 (c.withChart i) amp j) w :=
      commonWave_smoothAt ha h n d r0 (c.withChart i) hamp hF hG j
        (PhysicalGraphBounds.scaledRadial_ne_zero (PhysicalGraphBounds.annulus_axisFree ha hw))
    exact hc.congr_of_eventuallyEq he
  · exact contDiffAt_const.congr_of_eventuallyEq (globalWave_eventually_zero_off_annulus c amp j hs
      hw)

theorem globalWave_ne_zero_amp {a h r0 : ℝ} {n d : ℕ} {c : CarrierData}
    {amp : LiftPoint → ℂ} {j : ℤ} {w : SpaceTime}
    (hw : globalWave a h n d r0 c amp j w ≠ 0) : amp (commonLift h n d w) ≠ 0 := by
  intro hz
  exact hw (globalWave_eq_zero hz)

theorem physicalSlowPair_eq (h : ℝ) (n : ℕ) (w : SpaceTime) :
    PhysicalGraphBounds.liftZT (PhysicalGraphBounds.physicalLift h n w) =
      (ChartScales.Q n ^ (-CoordinateAlgebra.D h) * w.2 2, (1 - w.1) / ChartScales.Q n) := by
  simp only [PhysicalGraphBounds.liftZT_apply, PhysicalGraphBounds.physicalLift,
    PhysicalGraphBounds.physicalChart, PhysicalGraphBounds.chartLinear_apply]
  ext <;> simp [Real.rpow_neg_one, div_eq_mul_inv]
  ring

theorem physicalSlowPair_continuous (h : ℝ) (n : ℕ) :
    Continuous (fun w => PhysicalGraphBounds.liftZT (PhysicalGraphBounds.physicalLift h n w)) := by
  simp_rw [physicalSlowPair_eq]
  exact (continuous_const.mul ((AxisymmetricFields.projection 2).continuous.comp
      continuous_snd)).prodMk
    ((continuous_const.sub continuous_fst).div_const _)

theorem nativeSlotCoordinate_eq (h : ℝ) (n : ℕ) (center : Plane) (w : SpaceTime) :
    PhysicalGraphBounds.etaCoordinate (PhysicalGraphBounds.nativeGraph h n w - center) =
      ChartScales.Tg ^ ChartScales.nativeIndex h n * w.1 - PhysicalGraphBounds.etaCoordinate center
          := by
  rw [map_sub, PhysicalGraphBounds.etaCoordinate_nativeGraph]

theorem nativeSlotCoordinate_continuous (h : ℝ) (n : ℕ) (center : Plane) :
    Continuous (fun w => PhysicalGraphBounds.etaCoordinate (PhysicalGraphBounds.nativeGraph h n w -
        center)) := by
  simp_rw [nativeSlotCoordinate_eq]
  exact (continuous_const.mul continuous_fst).sub continuous_const

theorem globalWave_tsupport_geometry {a b h r0 Z : ℝ} {n d : ℕ} (c : CarrierData)
    (amp : LiftPoint → ℂ) (j : ℤ)
    (hs : ∀ y, amp (commonLift h n d y) ≠ 0 →
      PhysicalGraphBounds.scaledRadial n y ∈ PhysicalGraphBounds.annulus a b ∧
      ‖PhysicalGraphBounds.liftZT (PhysicalGraphBounds.physicalLift h n y)‖ ≤ Z ∧
      |PhysicalGraphBounds.etaCoordinate (PhysicalGraphBounds.nativeGraph h n y - c.center)| ≤ r0)
    {w : SpaceTime} (hw : w ∈ tsupport (globalWave a h n d r0 c amp j)) :
    PhysicalGraphBounds.scaledRadial n w ∈ PhysicalGraphBounds.annulus a b ∧
      ‖PhysicalGraphBounds.liftZT (PhysicalGraphBounds.physicalLift h n w)‖ ≤ Z ∧
      |PhysicalGraphBounds.etaCoordinate (PhysicalGraphBounds.nativeGraph h n w - c.center)| ≤ r0
          := by
  refine ⟨?_, ?_, ?_⟩
  · exact closed_property_on_tsupport isOpen_univ (mem_univ w)
      (PhysicalGraphBounds.scaledRadial n).continuous.continuousAt
      (PhysicalGraphBounds.isCompact_annulus a b).isClosed
      (fun y _ hy => (hs y (globalWave_ne_zero_amp hy)).1) hw
  · exact closed_property_on_tsupport isOpen_univ (mem_univ w)
      (physicalSlowPair_continuous h n).norm.continuousAt isClosed_Iic
      (fun y _ hy => (hs y (globalWave_ne_zero_amp hy)).2.1) hw
  · exact closed_property_on_tsupport isOpen_univ (mem_univ w)
      (nativeSlotCoordinate_continuous h n c.center).abs.continuousAt isClosed_Iic
      (fun y _ hy => (hs y (globalWave_ne_zero_amp hy)).2.2) hw

/-- Wave family data, collecting `gap`, `carrier`, `amplitude`. -/
structure WaveFamily (H : ℕ) where
  /-- Gap of `WaveFamily`, of type `BandLabel → ℕ`. -/
  gap : BandLabel → ℕ
  /-- Carrier of `WaveFamily`, of type `BandLabel → CarrierData`. -/
  carrier : BandLabel → CarrierData
  /-- Amplitude of `WaveFamily`, of type `WaveIndex H → LiftPoint → ℂ`. -/
  amplitude : WaveIndex H → LiftPoint → ℂ

/-- Term, given by `globalWave a h I.1.val.1 (f.gap I.1) r0 (f.carrier I.1) (f.amplitude I)
I.2.val`. -/
noncomputable def WaveFamily.term {H : ℕ} (f : WaveFamily H) (a h r0 : ℝ)
    (I : WaveIndex H) : SpaceTime → ℂ :=
  globalWave a h I.1.val.1 (f.gap I.1) r0 (f.carrier I.1) (f.amplitude I) I.2.val

/-- Sum, given by `∑ᶠ I : WaveIndex H, f.term a h r0 I w`. -/
noncomputable def WaveFamily.sum {H : ℕ} (f : WaveFamily H) (a h r0 : ℝ) (w : SpaceTime) : ℂ :=
  ∑ᶠ I : WaveIndex H, f.term a h r0 I w

/-- Smooth coefficients, the genuine angular integrality condition, and
input amplitude supports. No output derivative estimate is assumed. -/
structure RegularFamily {H : ℕ} (f : WaveFamily H) (a b h r0 Z : ℝ) (Δ : ℕ) : Prop where
  gap_le : ∀ L, f.gap L ≤ Δ
  gap_native : ∀ L, f.gap L ≤ ChartScales.nativeIndex h L.val.1
  amplitude_smooth : ∀ I, ContDiff ℝ ∞ (f.amplitude I)
  F_smooth : ∀ L, ContDiff ℝ ∞ (f.carrier L).F
  G_smooth : ∀ L, ContDiff ℝ ∞ (f.carrier L).G
  angular_integer : ∀ L, ∃ m : ℤ,
    (ChartScales.carrier h L.val.1 : ℝ) * (f.carrier L).angular = (m : ℝ)
  geometry_support : ∀ I y,
    f.amplitude I (commonLift h I.1.val.1 (f.gap I.1) y) ≠ 0 →
      PhysicalGraphBounds.scaledRadial I.1.val.1 y ∈ PhysicalGraphBounds.annulus a b ∧
      ‖PhysicalGraphBounds.liftZT (PhysicalGraphBounds.physicalLift h I.1.val.1 y)‖ ≤ Z ∧
      |PhysicalGraphBounds.etaCoordinate
        (PhysicalGraphBounds.nativeGraph h I.1.val.1 y - (f.carrier I.1).center)| ≤ r0
  mask_support : ∀ I y, y ∈ preterminal →
    f.amplitude I (commonLift h I.1.val.1 (f.gap I.1) y) ≠ 0 →
      physicalMask (CoordinateAlgebra.D h) I.1.val (physicalParams h y) ≠ 0

theorem RegularFamily.commonLift_formula {H : ℕ} {f : WaveFamily H} {a b h r0 Z : ℝ} {Δ : ℕ}
    (hf : RegularFamily f a b h r0 Z Δ) (L : BandLabel) (w : SpaceTime) :
    commonLift h L.val.1 (f.gap L) w =
      (PhysicalGraphBounds.physicalChart h L.val.1 w,
        (SlotGeometry.cover ^ (ChartScales.nativeIndex h L.val.1 - f.gap L))
          (PhysicalGraphBounds.radialProfile (ChartScales.radialExponent h)
            (PhysicalGraphBounds.radialProjection w) + w.1 • PhysicalGraphBounds.timeDirection)) :=
  PhysicalWaveSum.commonLift_formula h L.val.1 (f.gap L) (hf.gap_native L) w

theorem RegularFamily.term_smooth {H : ℕ} {f : WaveFamily H} {a b h r0 Z : ℝ} {Δ : ℕ}
    (hf : RegularFamily f a b h r0 Z Δ) (ha : 0 < a) (I : WaveIndex H) :
    ContDiff ℝ ∞ (f.term a h r0 I) := by
  obtain ⟨m, hm⟩ := hf.angular_integer I.1
  exact globalWave_smooth ha I.1.val.1 (f.gap I.1) (f.carrier I.1) (f.amplitude I) I.2.val m hm
    (hf.amplitude_smooth I) (hf.F_smooth I.1) (hf.G_smooth I.1)
    (fun y hy => (hf.geometry_support I y hy).1)

theorem RegularFamily.term_support {H : ℕ} {f : WaveFamily H} {a b h r0 Z : ℝ} {Δ : ℕ}
    (hf : RegularFamily f a b h r0 Z Δ) (I : WaveIndex H) (w : SpaceTime)
    (hw : w ∈ preterminal) (hn : f.term a h r0 I w ≠ 0) :
    physicalParams h w ∈ labelRegion (CoordinateAlgebra.D h) I.1.val :=
  physicalMask_support_subset _ _ (hf.mask_support I w hw (globalWave_ne_zero_amp hn))

theorem RegularFamily.sum_smooth {H : ℕ} {f : WaveFamily H} {a b h r0 Z : ℝ} {Δ : ℕ}
    (hf : RegularFamily f a b h r0 Z Δ) (ha : 0 < a) (hh : 0 < h) (hh1 : h < 1 / 2) :
    ContDiffOn ℝ ∞ (f.sum a h r0) preterminal :=
  masked_finsum_smooth hh hh1 (f.term a h r0)
    (fun I _ _ => (hf.term_smooth ha I).contDiffAt) hf.term_support

/-- Bounds on genuine input coefficient jets in common coordinates, and
on the genuine base profiles entering the native phase. -/
structure StrippedClass {H : ℕ} (f : WaveFamily H)
    (a b h r0 P A B g eAmp eBase : ℝ) (m : ℕ) : Prop where
  parameters : ∀ L, |(f.carrier L).angular| ≤ P ∧
    |(f.carrier L).axial| ≤ P ∧ |(f.carrier L).radial| ≤ P
  amplitude : ∀ (I : WaveIndex H) (w : SpaceTime), w ∈ preterminal →
    physicalParams h w ∈ labelRegion (CoordinateAlgebra.D h) I.1.val →
    PhysicalGraphBounds.scaledRadial I.1.val.1 w ∈ PhysicalGraphBounds.annulus a b →
    ∀ i ≤ m, ‖iteratedFDeriv ℝ i (f.amplitude I) (commonLift h I.1.val.1 (f.gap I.1) w)‖ ≤
      A * ChartScales.Q I.1.val.1 ^ g * ChartScales.S I.1.val.1 ^ eAmp
  base_F : ∀ (I : WaveIndex H) (w : SpaceTime), w ∈ preterminal →
    physicalParams h w ∈ labelRegion (CoordinateAlgebra.D h) I.1.val →
    PhysicalGraphBounds.scaledRadial I.1.val.1 w ∈ PhysicalGraphBounds.annulus a b →
    ∀ chart : PolarCharts.Index,
    PhysicalGraphBounds.scaledRadial I.1.val.1 w ∈ PolarCharts.chartDomain a chart →
    ∀ i ≤ m, ‖iteratedFDeriv ℝ i (f.carrier I.1).F
      (PhysicalGraphBounds.slotMap (PolarCharts.chart a chart)
        (ChartScales.timeCoefficient h I.1.val.1) (f.carrier I.1).center r0
        (PhysicalGraphBounds.physicalLift h I.1.val.1 w)).1‖ ≤ B * ChartScales.S I.1.val.1 ^ eBase
  base_G : ∀ (I : WaveIndex H) (w : SpaceTime), w ∈ preterminal →
    physicalParams h w ∈ labelRegion (CoordinateAlgebra.D h) I.1.val →
    PhysicalGraphBounds.scaledRadial I.1.val.1 w ∈ PhysicalGraphBounds.annulus a b →
    ∀ chart : PolarCharts.Index,
    PhysicalGraphBounds.scaledRadial I.1.val.1 w ∈ PolarCharts.chartDomain a chart →
    ∀ i ≤ m, ‖iteratedFDeriv ℝ i (f.carrier I.1).G
      (PhysicalGraphBounds.slotMap (PolarCharts.chart a chart)
        (ChartScales.timeCoefficient h I.1.val.1) (f.carrier I.1).center r0
        (PhysicalGraphBounds.physicalLift h I.1.val.1 w)).1‖ ≤ B * ChartScales.S I.1.val.1 ^ eBase

/-- The full physical sum has exactly the same power loss as one native
carrier. The number of harmonics, bounded cover gap, overlap count, and
stripped-class degrees affect its constant only. -/
theorem physical_sum_jet_bound {h a b Z r0 P B eBase : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (ha : 0 < a)
    (hZ : 0 ≤ Z) (hr0 : 0 ≤ r0) (hP : 1 ≤ P) (hB : 1 ≤ B) (heBase : 0 ≤ eBase)
    (H Δ m : ℕ) (g eAmp A : ℝ) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : WaveFamily H,
      RegularFamily f a b h r0 Z Δ → StrippedClass f a b h r0 P A B g eAmp eBase m →
      ∀ w : SpaceTime, w ∈ preterminal → |w.1| ≤ 1 →
      ‖iteratedFDeriv ℝ m (f.sum a h r0) w‖ ≤
        C * physicalQ h w ^ (g - PhysicalGraphBounds.waveLoss h m) := by
  obtain ⟨C, hC, hpoint⟩ := common_carrier_physical_bound (b := b) hh.le hh1.le ha
    hZ hr0 hP hB heBase Δ m g eAmp A (H : ℝ) hA (Nat.cast_nonneg H)
  refine ⟨((2250 * (2 * H + 1) : ℕ) : ℝ) * C, mul_nonneg (Nat.cast_nonneg _) hC, ?_⟩
  intro f hregular hclass w hw ht
  have hq := physicalQ_pos hh hh1 hw
  have hsum := masked_finsum_jet_bound hh hh1 (f.term a h r0)
    (fun I _ _ => (hregular.term_smooth ha I).contDiffAt) hregular.term_support hw m
    (B := C * physicalQ h w ^ (g - PhysicalGraphBounds.waveLoss h m)) (by positivity)
  refine (hsum ?_).trans_eq (by ring)
  · intro I hregion
    by_cases hs : w ∈ tsupport (f.term a h r0 I)
    · have hgeo := globalWave_tsupport_geometry (f.carrier I.1) (f.amplitude I) I.2.val
        (hregular.geometry_support I) hs
      obtain ⟨mode, hmode⟩ := hregular.angular_integer I.1
      let chart := chooseChart a (PhysicalGraphBounds.scaledRadial I.1.val.1 w)
      have hchart : PhysicalGraphBounds.scaledRadial I.1.val.1 w ∈ PolarCharts.chartDomain a chart
          :=
        chooseChart_valid ha hgeo.1
      have he := globalWave_eventually_common (r0 := r0) ha I.1.val.1 (f.gap I.1)
        (f.carrier I.1) (f.amplitude I) I.2.val mode hmode
        (fun y hy => (hregular.geometry_support I y hy).1) chart hchart
      change ‖iteratedFDeriv ℝ m (globalWave a h I.1.val.1 (f.gap I.1) r0
        (f.carrier I.1) (f.amplitude I) I.2.val) w‖ ≤ _
      rw [iteratedFDeriv_eq_of_eventuallyEq he m]
      have hband := labelRegion_active_relation hregion
      exact hpoint I.1.val.1 I.1.property (f.gap I.1) (hregular.gap_le I.1)
        w hgeo.1 ht hgeo.2.1 (physicalQ h w) hq hband.1 hband.2
        ((f.carrier I.1).withChart chart) (f.amplitude I) I.2.val
        (hclass.parameters I.1).1 (hclass.parameters I.1).2.1 (hclass.parameters I.1).2.2 hgeo.2.2
        (hregular.amplitude_smooth I) (hregular.F_smooth I.1) (hregular.G_smooth I.1)
            (harmonic_bound I.2)
        (hclass.amplitude I w hw hregion hgeo.1)
        (hclass.base_F I w hw hregion hgeo.1 chart hchart)
        (hclass.base_G I w hw hregion hgeo.1 chart hchart)
    · rw [jet_zero_off_tsupport _ _ hs, norm_zero]
      positivity

/-- Cover change, given by `(downLift e).comp (upLift d)`. -/
noncomputable def coverChange (d e : ℕ) : LiftPoint →L[ℝ] LiftPoint :=
  (downLift e).comp (upLift d)

theorem coverChange_common (h : ℝ) (n d e : ℕ) (w : SpaceTime) :
    coverChange d e (commonLift h n d w) = commonLift h n e w := by
  simp only [coverChange, commonLift, ContinuousLinearMap.comp_apply, Function.comp_apply, up_down]

theorem norm_coverChange_le {d e Δ : ℕ} (hd : d ≤ Δ) (he : e ≤ Δ) :
    ‖coverChange d e‖ ≤ coverBound Δ ^ 2 := by
  unfold coverChange
  calc
    _ ≤ ‖downLift e‖ * ‖upLift d‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ coverBound Δ * coverBound Δ :=
      mul_le_mul (norm_downLift_le he) (norm_upLift_le hd) (norm_nonneg _) (by
        have := coverBound_ge_one Δ; linarith)
    _ = _ := (pow_two _).symm

/-- Re-expressing a source by the true linear cover change preserves its
physical wave exactly. This does not require finer native periodicity. -/
theorem commonWave_reexpress (a h : ℝ) (n d e : ℕ) (r0 : ℝ)
    (c : CarrierData) (amp : LiftPoint → ℂ) (j : ℤ) (w : SpaceTime) :
    commonWave a h n d r0 c (amp ∘ coverChange d e) j w =
      commonWave a h n e r0 c amp j w := by
  simp only [commonWave, Function.comp_apply, coverChange_common]

theorem globalWave_reexpress (a h : ℝ) (n d e : ℕ) (r0 : ℝ)
    (c : CarrierData) (amp : LiftPoint → ℂ) (j : ℤ) (w : SpaceTime) :
    globalWave a h n d r0 c (amp ∘ coverChange d e) j w =
      globalWave a h n e r0 c amp j w :=
  commonWave_reexpress a h n d e r0 _ amp j w

theorem RegularFamily.sum_locally_finite {H : ℕ} {f : WaveFamily H} {a b h r0 Z : ℝ} {Δ : ℕ}
    (hf : RegularFamily f a b h r0 Z Δ) (hh : 0 < h) (hh1 : h < 1 / 2)
    {w : SpaceTime} (hw : w ∈ preterminal) :
    ∃ s : Finset (WaveIndex H), s.card ≤ 2250 * (2 * H + 1) ∧
      f.sum a h r0 =ᶠ[𝓝 w] fun y => ∑ I ∈ s, f.term a h r0 I y := by
  obtain ⟨s, hs, he⟩ := masked_finsum_eventually hh hh1 (f.term a h r0) hf.term_support hw
  exact ⟨s, waveRegion_card_le (physicalQ_pos hh hh1 hw) s (fun I hI => (hs I).mp hI), he⟩

/-- Factoring in the actual constructed mask proves the support input used
by `RegularFamily`; no separate support assertion about the sum is needed. -/
theorem mask_support_of_factorization {D h : ℝ} {L : Label} {n d : ℕ}
    {amp : LiftPoint → ℂ} {rest : SpaceTime → ℂ}
    (he : ∀ w, amp (commonLift h n d w) = (physicalMask D L (physicalParams h w) : ℂ) * rest w)
    (w : SpaceTime) (hw : amp (commonLift h n d w) ≠ 0) :
    physicalMask D L (physicalParams h w) ≠ 0 := by
  intro hz
  apply hw
  rw [he, hz, Complex.ofReal_zero, zero_mul]

/-- Real coordinate, given by `Complex.reCLM.smulRight (coordinateVector i)`. -/
noncomputable def realCoordinate (i : Fin 3) : ℂ →L[ℝ] Space :=
  Complex.reCLM.smulRight (coordinateVector i)

@[simp] theorem realCoordinate_apply (i : Fin 3) (z : ℂ) :
    realCoordinate i z = z.re • coordinateVector i := rfl

theorem norm_realCoordinate_le (i : Fin 3) : ‖realCoordinate i‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
  intro z
  rw [realCoordinate_apply, norm_smul, coordinateVector, PiLp.norm_single, norm_one,
    mul_one, one_mul]
  exact Complex.abs_re_le_norm z

/-- Real Euclidean vector assembled from the three scalar carrier sums. -/
noncomputable def vectorSum {H : ℕ} (f : Fin 3 → WaveFamily H) (a h r0 : ℝ)
    (w : SpaceTime) : Space := ∑ i : Fin 3, realCoordinate i ((f i).sum a h r0 w)

theorem vectorSum_smooth {H : ℕ} {f : Fin 3 → WaveFamily H} {a b h r0 Z : ℝ} {Δ : ℕ}
    (hf : ∀ i, RegularFamily (f i) a b h r0 Z Δ) (ha : 0 < a) (hh : 0 < h) (hh1 : h < 1 / 2) :
    ContDiffOn ℝ ∞ (vectorSum f a h r0) preterminal := by
  intro w hw
  apply ContDiffAt.contDiffWithinAt
  apply ContDiffAt.sum
  intro i _
  exact (realCoordinate i).contDiff.contDiffAt.comp w
    (((hf i).sum_smooth ha hh hh1).contDiffAt (preterminal_open.mem_nhds hw))

theorem norm_jet_linear_comp_at {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : E → F} {w : E} {m : ℕ} (hf : ContDiffAt ℝ m f w) (L : F →L[ℝ] G) :
    ‖iteratedFDeriv ℝ m (L ∘ f) w‖ ≤ ‖L‖ * ‖iteratedFDeriv ℝ m f w‖ := by
  rw [L.iteratedFDeriv_comp_left hf le_rfl]
  exact L.norm_compContinuousMultilinearMap_le _

theorem vectorSum_jet_bound {H : ℕ} {f : Fin 3 → WaveFamily H} {a b h r0 Z : ℝ} {Δ : ℕ}
    (hf : ∀ i, RegularFamily (f i) a b h r0 Z Δ) (ha : 0 < a) (hh : 0 < h) (hh1 : h < 1 / 2)
    {w : SpaceTime} (hw : w ∈ preterminal) (m : ℕ) {B : ℝ}
    (hb : ∀ i, ‖iteratedFDeriv ℝ m ((f i).sum a h r0) w‖ ≤ B) :
    ‖iteratedFDeriv ℝ m (vectorSum f a h r0) w‖ ≤ 3 * B := by
  have hlocal (i : Fin 3) : ContDiffAt ℝ m ((f i).sum a h r0) w :=
    (((hf i).sum_smooth ha hh hh1).contDiffAt (preterminal_open.mem_nhds hw)).of_le (nat_le_infty m)
  unfold vectorSum
  rw [iteratedFDeriv_finset_sum_at (f := fun i y => realCoordinate i ((f i).sum a h r0 y))
      Finset.univ
    (fun i _ => (realCoordinate i).contDiff.contDiffAt.comp w (hlocal i))]
  calc
    _ ≤ ∑ i : Fin 3, ‖iteratedFDeriv ℝ m (fun y => realCoordinate i ((f i).sum a h r0 y)) w‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _i : Fin 3, B := by
      apply Finset.sum_le_sum
      intro i _
      exact (norm_jet_linear_comp_at (hlocal i) (realCoordinate i)).trans
        ((mul_le_of_le_one_left (norm_nonneg _) (norm_realCoordinate_le i)).trans (hb i))
    _ = _ := by simp

/-- The same stage-independent loss for an actual real Cartesian vector
field. Passing from scalar components costs only a factor of three. -/
theorem physical_vector_sum_jet_bound {h a b Z r0 P B eBase : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (ha : 0 < a)
    (hZ : 0 ≤ Z) (hr0 : 0 ≤ r0) (hP : 1 ≤ P) (hB : 1 ≤ B) (heBase : 0 ≤ eBase)
    (H Δ m : ℕ) (g eAmp A : ℝ) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Fin 3 → WaveFamily H,
      (∀ i, RegularFamily (f i) a b h r0 Z Δ) →
      (∀ i, StrippedClass (f i) a b h r0 P A B g eAmp eBase m) →
      ∀ w : SpaceTime, w ∈ preterminal → |w.1| ≤ 1 →
      ‖iteratedFDeriv ℝ m (vectorSum f a h r0) w‖ ≤
        C * physicalQ h w ^ (g - PhysicalGraphBounds.waveLoss h m) := by
  obtain ⟨C, hC, hb⟩ := physical_sum_jet_bound (b := b) hh hh1 ha hZ hr0 hP hB heBase H Δ m g eAmp
      A hA
  refine ⟨3 * C, by positivity, ?_⟩
  intro f hreg hclass w hw ht
  exact (vectorSum_jet_bound hreg ha hh hh1 hw m (fun i => hb (f i) (hreg i) (hclass i) w hw
      ht)).trans_eq
    (by ring)

end NavierStokes.PhysicalWaveSum
