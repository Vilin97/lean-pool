/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualPrimaryBounds
import LeanPool.NavierStokesAndEuler.NavierStokes.ActualPrimaryCoherence
import LeanPool.NavierStokesAndEuler.NavierStokes.PhysicalClassBounds

/-!
# Ordinary jets of the selected primary phase

The angle and axial coordinate are affine in the actual phase.  Their
values need not be bounded, but their positive derivatives have a uniform
bound.  The remaining expression has polynomial slow jets on the same
native phase cells used to construct the primary waves.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.ActualPhaseJetBounds

open Set Function Filter PhaseJetBounds
open CorrectionInitialization
open scoped Topology ContDiff



private theorem nat_le_infty (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ :=
  ENat.natCast_le_of_coe_top_le_withTop le_rfl n

/-- Affine values may be unbounded; every positive jet is bounded by the
linear part alone. -/
theorem norm_positive_jet_affine {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (c : F) (x : E) {j : ℕ} (hj : 1 ≤ j) :
    ‖iteratedFDeriv ℝ j (fun y => L y + c) x‖ ≤ ‖L‖ := by
  have hd : fderiv ℝ (fun y => L y + c) = fun _ => L := by
    funext y
    exact (L.hasFDerivAt.add_const c).fderiv
  cases j with
  | zero => omega
  | succ j =>
    rw [← norm_iteratedFDeriv_fderiv, hd]
    cases j with
    | zero => simp only [norm_iteratedFDeriv_zero, le_refl]
    | succ j =>
      rw [iteratedFDeriv_succ_const]
      simpa only [Pi.zero_apply, norm_zero] using norm_nonneg L

variable {B N0 : ℕ}

/-- Signed label: an abbreviation for `ActualPrimaryBounds.SignedLabel B N0`. -/
abbrev SignedLabel (B N0 : ℕ) := ActualPrimaryBounds.SignedLabel B N0

/-- Both signs share the actual, unmodified analytic phase cells. -/
noncomputable def slowDomain : Domain (SignedLabel B N0) PhaseCalculus.Slow where
  scale l := ChartScales.S (BaseChartJets.cellBand l.2)
  carrier l := (PrimaryGeometryAssembly.domain ActualPrimary.nominal (ActualPrimary.choice B
      N0).prepared.N).carrier l.2
  isOpen l := (PrimaryGeometryAssembly.domain ActualPrimary.nominal (ActualPrimary.choice B
      N0).prepared.N).isOpen l.2
  one_le_scale l := (PrimaryGeometryAssembly.domain ActualPrimary.nominal (ActualPrimary.choice B
      N0).prepared.N).one_le_scale l.2

/-- Jet domain, given by `slowDomain.slot (fun l => (ActualPrimary.phases B N0 l.1).V l.2) (fun
l => (ActualPrimary.phases B N0 l.1).openV l.2)`. -/
noncomputable def jetDomain : Domain (SignedLabel B N0) (PhaseCalculus.Slow × ℝ) :=
  slowDomain.slot (fun l => (ActualPrimary.phases B N0 l.1).V l.2)
    (fun l => (ActualPrimary.phases B N0 l.1).openV l.2)

/-- Phase size, given by `(ActualPrimary.phases B N0 0).M + (ActualPrimary.phases B N0 1).M`. -/
noncomputable def phaseSize (B N0 : ℕ) : ℝ :=
  (ActualPrimary.phases B N0 0).M + (ActualPrimary.phases B N0 1).M

theorem one_le_phaseSize : 1 ≤ phaseSize B N0 := by
  have h0 := (ActualPrimary.phases B N0 0).one_le_M
  have h1 := (ActualPrimary.phases B N0 1).one_le_M
  dsimp [phaseSize]
  linarith

theorem signSize_le (j : Fin 2) : (ActualPrimary.phases B N0 j).M ≤ phaseSize B N0 := by
  have h0 := (ActualPrimary.phases B N0 0).one_le_M
  have h1 := (ActualPrimary.phases B N0 1).one_le_M
  fin_cases j <;> dsimp [phaseSize] <;> linarith

theorem phase_constants_bound (l : SignedLabel B N0) :
    |(ActualPrimary.phases B N0 l.1).phase.p l.2| ≤ phaseSize B N0 ∧
    |(ActualPrimary.phases B N0 l.1).phase.pz l.2| ≤ phaseSize B N0 ∧
    |(ActualPrimary.phases B N0 l.1).phase.x0 l.2| ≤ phaseSize B N0 :=
  ⟨((ActualPrimary.phases B N0 l.1).constants l.2).2.1.trans (signSize_le l.1),
   ((ActualPrimary.phases B N0 l.1).constants l.2).2.2.1.trans (signSize_le l.1),
   ((ActualPrimary.phases B N0 l.1).constants l.2).2.2.2.trans (signSize_le l.1)⟩

/-- The nonaffine part of the literal native phase. -/
noncomputable def nativeRemainder (l : SignedLabel B N0) (z : PhaseCalculus.Slow × ℝ) : ℝ :=
  (ActualPrimary.phases B N0 l.1).phase.x0 l.2 * z.1.1 -
    z.2 * ((ActualPrimary.phases B N0 l.1).phase.p l.2 * (ActualPrimary.phases B N0 l.1).phase.F
        l.2 z.1 +
      (ActualPrimary.phases B N0 l.1).phase.pz l.2 * (ActualPrimary.phases B N0 l.1).phase.G l.2
          z.1)

/-- All orders follow from the actual constructed F/G jets and bounded
native constants; this contains no phase-jet hypothesis. -/
theorem nativeRemainder_polynomial :
    PolynomialJets (jetDomain (B := B) (N0 := N0)) nativeRemainder := by
  let D := slowDomain (B := B) (N0 := N0)
  let V : SignedLabel B N0 → Set ℝ := fun l => (ActualPrimary.phases B N0 l.1).V l.2
  have hV : ∀ l, IsOpen (V l) := fun l => (ActualPrimary.phases B N0 l.1).openV l.2
  have hF : PolynomialJets D (fun l => (ActualPrimary.phases B N0 l.1).phase.F l.2) :=
    PrimaryGeometryAssembly.polynomial_restrict_reindex (ActualPrimary.phases B N0 0).baseF Prod.snd
      (fun _ => rfl) (fun _ _ hp => hp)
  have hG : PolynomialJets D (fun l => (ActualPrimary.phases B N0 l.1).phase.G l.2) :=
    PrimaryGeometryAssembly.polynomial_restrict_reindex (ActualPrimary.phases B N0 0).baseG Prod.snd
      (fun _ => rfl) (fun _ _ hp => hp)
  have hp : PolynomialJets (D.slot V hV) (fun l _ => (ActualPrimary.phases B N0 l.1).phase.p l.2) :=
    PolynomialJets.const_uniform _ one_le_phaseSize
      (fun l => by simpa only [Real.norm_eq_abs] using (phase_constants_bound l).1)
  have hpz : PolynomialJets (D.slot V hV) (fun l _ => (ActualPrimary.phases B N0 l.1).phase.pz l.2)
      :=
    PolynomialJets.const_uniform _ one_le_phaseSize
      (fun l => by simpa only [Real.norm_eq_abs] using (phase_constants_bound l).2.1)
  have hx0 : PolynomialJets (D.slot V hV) (fun l _ => (ActualPrimary.phases B N0 l.1).phase.x0 l.2)
      :=
    PolynomialJets.const_uniform _ one_le_phaseSize
      (fun l => by simpa only [Real.norm_eq_abs] using (phase_constants_bound l).2.2)
  have hR : PolynomialJets D (fun _ (p : PhaseCalculus.Slow) => p.1) := by
    simpa only [ContinuousLinearMap.coe_fst', add_zero] using
      (PolynomialJets.affine (D := D) (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ))
        (fun _ => 0) (m := 0) (one_le_phaseSize (B := B) (N0 := N0))
        (fun l p hp => by
          simpa only [ContinuousLinearMap.coe_fst', add_zero, pow_zero, mul_one, Real.norm_eq_abs]
              using
            ((ActualPrimary.phases B N0 l.1).radius l.2 p hp).2.trans (signSize_le l.1)))
  have ht : PolynomialJets (D.slot V hV) (fun _ (z : PhaseCalculus.Slow × ℝ) => z.2) := by
    simpa only [ContinuousLinearMap.coe_snd', add_zero] using
      (PolynomialJets.affine (D := D.slot V hV) (ContinuousLinearMap.snd ℝ PhaseCalculus.Slow ℝ)
        (fun _ => 0) (m := 1) (one_le_phaseSize (B := B) (N0 := N0))
        (fun l z hz => by
          simp only [ContinuousLinearMap.coe_snd', add_zero, Real.norm_eq_abs, pow_one]
          exact
            ((ActualPrimary.phases B N0 l.1).slot l.2 z.2 hz.2).trans
              (mul_le_mul_of_nonneg_right (signSize_le l.1)
                (zero_le_one.trans (D.one_le_scale l)))))
  exact (hx0.mul (hR.lift_slot V hV)).sub
    (ht.mul ((hp.mul (hF.lift_slot V hV)).add (hpz.mul (hG.lift_slot V hV))))

/-! ## Ordinary pullback jets on the actual native copy -/

/-- Copy index: an abbreviation for `SignedLabel B N0 × TorusInverse.Frequency`. -/
abbrev CopyIndex (B N0 : ℕ) := SignedLabel B N0 × TorusInverse.Frequency

/-- Only the genuine analytic cell and clock core are required.  In
particular, this also allows the larger geometric source window. -/
noncomputable def phaseCell (n : ℕ) (i : CopyIndex B N0) : Set ActualPrimary.FullPoint :=
  {x | ActualPrimaryBounds.near i.1 n ∧
    (ActualPrimaryBounds.fullCopy i.1 n i.2 x).1 ∈
      (PrimaryGeometryAssembly.domain ActualPrimary.nominal
        (ActualPrimary.choice B N0).prepared.N).carrier i.1.2 ∧
    (ActualPrimaryBounds.fullCopy i.1 n i.2 x).2 ∈ (ActualPrimary.clockWindow i.1.2).core}

theorem controlCell_subset_phaseCell (n : ℕ) (i : CopyIndex B N0) :
    ActualPrimaryBounds.controlCell n i ⊆ phaseCell n i :=
  fun _ hx => ⟨hx.1, hx.2.1, hx.2.2.1⟩

theorem phaseCell_maps {n : ℕ} {i : CopyIndex B N0} {x : ActualPrimary.FullPoint}
    (hx : x ∈ phaseCell n i) :
    ((ActualPrimaryBounds.fullCopy i.1 n i.2 x).1,
      (ActualPrimaryBounds.fullCopy i.1 n i.2 x).2.2) ∈ jetDomain.carrier i.1 := by
  refine ⟨hx.2.1, (ActualPrimary.phases B N0 i.1.1).interval i.1.2 ?_⟩
  simp only [ActualPrimary.length_sign i.1.1 i.1.2]
  exact hx.2.2.2

theorem slow_eq_S {n : ℕ} (hn : 1 ≤ n) :
    ActualPrimaryBounds.fullStrip.slow n = ChartScales.S n := by
  change max 1 (ChartScales.S n) = ChartScales.S n
  exact max_eq_right (PhysicalGraphBounds.S_ge_one hn)

theorem polynomial_copy_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : SignedLabel B N0 → PhaseCalculus.Slow × ℝ → E}
    (hf : PolynomialJets jetDomain f) {n : ℕ} {i : CopyIndex B N0}
    {x : ActualPrimary.FullPoint} (hx : x ∈ phaseCell n i) :
    ContDiffAt ℝ ∞ (fun y => f i.1 ((ActualPrimaryBounds.fullCopy i.1 n i.2 y).1,
      (ActualPrimaryBounds.fullCopy i.1 n i.2 y).2.2)) x := by
  have hm := phaseCell_maps hx
  rw [ActualPrimaryBounds.slotCopy_affine] at hm
  have hh := ((hf.smooth i.1).contDiffAt (jetDomain.isOpen i.1 |>.mem_nhds hm)).comp x
    (((ActualPrimaryBounds.slotLinear i.1 n).contDiff.add
      (contDiff_const (c := ActualPrimaryBounds.slotOfNative
        (ActualPrimaryBounds.copyPoint i.1 n i.2 0)))).contDiffAt)
  simpa only [← ActualPrimaryBounds.slotCopy_affine, Function.comp_def] using hh

/-- The estimate uses only the slow scale S, with no inverse distance to
the boundary hidden in the bound. -/
theorem polynomial_copy_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : SignedLabel B N0 → PhaseCalculus.Slow × ℝ → E}
    (hf : PolynomialJets jetDomain f) (m : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ p : ℕ, ∀ n (i : CopyIndex B N0) x,
      x ∈ phaseCell n i → ∀ j ≤ m,
      ‖iteratedFDeriv ℝ j (fun y => f i.1
        ((ActualPrimaryBounds.fullCopy i.1 n i.2 y).1,
          (ActualPrimaryBounds.fullCopy i.1 n i.2 y).2.2)) x‖ ≤ C * ChartScales.S n ^ p := by
  obtain ⟨C, hC, p, hb⟩ := hf.bound m
  have hcost := ActualPrimaryBounds.copyCost_one
  refine ⟨C * 25 ^ p * ActualPrimaryBounds.copyCost ^ m, ?_, p + m, ?_⟩
  · exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le hC (one_le_pow₀ (by norm_num))) (one_le_pow₀ hcost)
  intro n i x hx j hj
  have hS := PhysicalGraphBounds.S_ge_one hx.1.1
  have hm := phaseCell_maps hx
  have hscale : jetDomain.scale i.1 ≤ 25 * ChartScales.S n :=
    ActualSignedGeometry.S_window_le hx.1.1 (ActualPrimaryBounds.near_distance hx.1).2
  have hlin0 : ‖ActualPrimaryBounds.slotLinear i.1 n‖ ≤ ActualPrimaryBounds.copyCost *
      ChartScales.S n := by
    simpa only [slow_eq_S hx.1.1] using ActualPrimaryBounds.slotLinear_bound hx.1
  have hlin : ‖ActualPrimaryBounds.slotLinear i.1 n‖ ^ j ≤
      ActualPrimaryBounds.copyCost ^ m * ChartScales.S n ^ m := by
    calc
      _ ≤ (ActualPrimaryBounds.copyCost * ChartScales.S n) ^ m :=
        (pow_le_pow_left₀ (norm_nonneg _) hlin0 j).trans
          (pow_le_pow_right₀ (one_le_mul_of_one_le_of_one_le hcost hS) hj)
      _ = _ := mul_pow _ _ _
  have hu := norm_jet_comp_affine (jetDomain.isOpen i.1) (hf.smooth i.1)
    (ActualPrimaryBounds.slotLinear i.1 n)
    (ActualPrimaryBounds.slotOfNative (ActualPrimaryBounds.copyPoint i.1 n i.2 0))
    (by simpa only [← ActualPrimaryBounds.slotCopy_affine] using hm) j
  simp only [← ActualPrimaryBounds.slotCopy_affine] at hu
  calc
    _ ≤ ‖iteratedFDeriv ℝ j (f i.1)
        ((ActualPrimaryBounds.fullCopy i.1 n i.2 x).1,
          (ActualPrimaryBounds.fullCopy i.1 n i.2 x).2.2)‖ *
        ‖ActualPrimaryBounds.slotLinear i.1 n‖ ^ j := hu
    _ ≤ (C * (25 * ChartScales.S n) ^ p) *
        (ActualPrimaryBounds.copyCost ^ m * ChartScales.S n ^ m) := by
      have hfb := (hb i.1 j hj _ hm).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (zero_le_one.trans (jetDomain.one_le_scale i.1)) hscale p)
        (zero_le_one.trans hC))
      exact mul_le_mul hfb hlin (pow_nonneg (norm_nonneg _) _) ((norm_nonneg _).trans hfb)
    _ = _ := by rw [mul_pow, pow_add]; ring

/-- The axial coordinate on the native slow/clock product. -/
noncomputable def nativeZ : (PhaseCalculus.Slow × ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).comp
    ((ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)).comp
      (ContinuousLinearMap.fst ℝ PhaseCalculus.Slow ℝ))

theorem nativeZ_norm : ‖nativeZ‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖x.1.2.1‖ ≤ 1 * ‖x‖
  rw [one_mul]
  exact (norm_fst_le x.1.2).trans ((norm_snd_le x.1).trans (norm_fst_le x))

/-- Phase linear as an element of `ActualPrimary.FullPoint →L[ℝ] ℝ`. -/
noncomputable def phaseLinear (l : SignedLabel B N0) (n : ℕ) :
    ActualPrimary.FullPoint →L[ℝ] ℝ :=
  (ActualPrimary.phases B N0 l.1).phase.p l.2 •
      (ContinuousLinearMap.snd ℝ ActualPrimaryBounds.Point ℝ) +
    ((ActualPrimary.phases B N0 l.1).phase.pz l.2 /
      ChartScales.epsilon ActualPrimary.h (BaseChartJets.cellBand l.2)) •
      (nativeZ.comp (ActualPrimaryBounds.slotLinear l n))

/-- Phase offset as an element of `ℝ`. -/
noncomputable def phaseOffset (n : ℕ) (i : CopyIndex B N0) : ℝ :=
  ((ActualPrimary.phases B N0 i.1.1).phase.pz i.1.2 /
      ChartScales.epsilon ActualPrimary.h (BaseChartJets.cellBand i.1.2)) *
    nativeZ (ActualPrimaryBounds.slotOfNative (ActualPrimaryBounds.copyPoint i.1 n i.2 0))

/-- Local phase, constructed using `PhaseCalculus.phase`. -/
noncomputable def localPhase (n : ℕ) (i : CopyIndex B N0) (x : ActualPrimary.FullPoint) : ℝ :=
  PhaseCalculus.phase (ChartScales.epsilon ActualPrimary.h (BaseChartJets.cellBand i.1.2))
    ((ActualPrimary.phases B N0 i.1.1).phase.p i.1.2)
    ((ActualPrimary.phases B N0 i.1.1).phase.pz i.1.2)
    ((ActualPrimary.phases B N0 i.1.1).phase.x0 i.1.2)
    ((ActualPrimary.phases B N0 i.1.1).phase.F i.1.2)
    ((ActualPrimary.phases B N0 i.1.1).phase.G i.1.2)
    ((ActualPrimaryBounds.fullCopy i.1 n i.2 x).1,
      (x.2, (ActualPrimaryBounds.fullCopy i.1 n i.2 x).2.2))

theorem localPhase_decomposition (n : ℕ) (i : CopyIndex B N0) (x : ActualPrimary.FullPoint) :
    localPhase n i x = phaseLinear i.1 n x + phaseOffset n i +
      nativeRemainder i.1 ((ActualPrimaryBounds.fullCopy i.1 n i.2 x).1,
        (ActualPrimaryBounds.fullCopy i.1 n i.2 x).2.2) := by
  have hz := congrArg nativeZ (ActualPrimaryBounds.slotCopy_affine i.1 n i.2 x)
  rw [map_add] at hz
  change (ActualPrimaryBounds.fullCopy i.1 n i.2 x).1.2.1 =
    nativeZ (ActualPrimaryBounds.slotLinear i.1 n x) +
      nativeZ (ActualPrimaryBounds.slotOfNative (ActualPrimaryBounds.copyPoint i.1 n i.2 0)) at hz
  simp only [localPhase, PhaseCalculus.phase, nativeRemainder, phaseLinear, phaseOffset,
    _root_.add_apply, _root_.smul_apply,
    ContinuousLinearMap.coe_snd', ContinuousLinearMap.comp_apply, smul_eq_mul]
  rw [hz]
  ring

theorem localPhase_smooth {n : ℕ} {i : CopyIndex B N0} {x : ActualPrimary.FullPoint}
    (hx : x ∈ phaseCell n i) : ContDiffAt ℝ ∞ (localPhase n i) x := by
  have he : localPhase n i = fun y => phaseLinear i.1 n y + phaseOffset n i +
      nativeRemainder i.1 ((ActualPrimaryBounds.fullCopy i.1 n i.2 y).1,
        (ActualPrimaryBounds.fullCopy i.1 n i.2 y).2.2) := funext (localPhase_decomposition n i)
  rw [he]
  exact (((phaseLinear i.1 n).contDiff.contDiffAt).add contDiffAt_const).add
    (polynomial_copy_smooth nativeRemainder_polynomial hx)

theorem one_le_inverse_epsilon (n : ℕ) :
    1 ≤ (ChartScales.epsilon ActualPrimary.h n)⁻¹ := by
  have he := ChartScales.epsilon_pos ActualPrimary.h n
  have hle := ChartScales.epsilon_le_one ActualPrimary.h ActualPrimary.outgoing.data.h_pos.le n
  simpa only [one_div] using (one_le_div he).mpr hle

theorem carrier_le_inverse_epsilon (n : ℕ) :
    (ChartScales.carrier ActualPrimary.h n : ℝ) ≤
      2 * (ChartScales.epsilon ActualPrimary.h n)⁻¹ := by
  have he := ChartScales.epsilon_pos ActualPrimary.h n
  have hs := Real.sqrt_nonneg (ChartScales.epsilon ActualPrimary.h n)
  have hs1 := Real.sqrt_le_one.mpr
    (ChartScales.epsilon_le_one ActualPrimary.h ActualPrimary.outgoing.data.h_pos.le n)
  have hsq := Real.sq_sqrt he.le
  have hel : ChartScales.epsilon ActualPrimary.h n ≤
      Real.sqrt (ChartScales.epsilon ActualPrimary.h n) := by nlinarith
  have hupper := (Scaling.carrier_frequency_sqrt_bounds he).2
  change (ChartScales.carrier ActualPrimary.h n : ℝ) *
    Real.sqrt (ChartScales.epsilon ActualPrimary.h n) ≤
      1 + Real.sqrt (ChartScales.epsilon ActualPrimary.h n) at hupper
  have hk : 0 ≤ (ChartScales.carrier ActualPrimary.h n : ℝ) := Nat.cast_nonneg _
  have hmul : (ChartScales.carrier ActualPrimary.h n : ℝ) *
      ChartScales.epsilon ActualPrimary.h n ≤ 2 :=
    (mul_le_mul_of_nonneg_left hel hk).trans (by linarith)
  simpa only [div_eq_mul_inv] using (le_div_iff₀ he).mpr hmul

theorem phaseLinear_bound {l : SignedLabel B N0} {n : ℕ}
    (hn : ActualPrimaryBounds.near l n) :
    ‖phaseLinear l n‖ ≤
      (2 * phaseSize B N0 * ActualPrimaryBounds.copyCost) * ChartScales.S n *
        (ChartScales.epsilon ActualPrimary.h (BaseChartJets.cellBand l.2))⁻¹ := by
  have hM := one_le_phaseSize (B := B) (N0 := N0)
  have hM0 := zero_le_one.trans hM
  have hK := ActualPrimaryBounds.copyCost_one
  have hS := PhysicalGraphBounds.S_ge_one hn.1
  have he := ChartScales.epsilon_pos ActualPrimary.h (BaseChartJets.cellBand l.2)
  have hei := one_le_inverse_epsilon (BaseChartJets.cellBand l.2)
  have hangle : ‖ContinuousLinearMap.snd ℝ ActualPrimaryBounds.Point ℝ‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simpa only [ContinuousLinearMap.coe_snd', one_mul] using norm_snd_le x
  have hz : ‖nativeZ.comp (ActualPrimaryBounds.slotLinear l n)‖ ≤
      ActualPrimaryBounds.copyCost * ChartScales.S n := by
    calc
      _ ≤ ‖nativeZ‖ * ‖ActualPrimaryBounds.slotLinear l n‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * (ActualPrimaryBounds.copyCost * ChartScales.S n) := by
        gcongr
        · exact nativeZ_norm
        · simpa only [slow_eq_S hn.1] using ActualPrimaryBounds.slotLinear_bound hn
      _ = _ := one_mul _
  have hd : |(ActualPrimary.phases B N0 l.1).phase.pz l.2 /
      ChartScales.epsilon ActualPrimary.h (BaseChartJets.cellBand l.2)| ≤
      phaseSize B N0 * (ChartScales.epsilon ActualPrimary.h (BaseChartJets.cellBand l.2))⁻¹ := by
    rw [abs_div, abs_of_pos he, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (phase_constants_bound l).2.1 (inv_nonneg.mpr he.le)
  have hprod : 1 ≤ ActualPrimaryBounds.copyCost * ChartScales.S n *
      (ChartScales.epsilon ActualPrimary.h (BaseChartJets.cellBand l.2))⁻¹ :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hK hS) hei
  calc
    _ ≤ ‖(ActualPrimary.phases B N0 l.1).phase.p l.2 •
        ContinuousLinearMap.snd ℝ ActualPrimaryBounds.Point ℝ‖ +
      ‖((ActualPrimary.phases B N0 l.1).phase.pz l.2 /
        ChartScales.epsilon ActualPrimary.h (BaseChartJets.cellBand l.2)) •
        (nativeZ.comp (ActualPrimaryBounds.slotLinear l n))‖ := norm_add_le _ _
    _ ≤ phaseSize B N0 * 1 +
        (phaseSize B N0 * (ChartScales.epsilon ActualPrimary.h (BaseChartJets.cellBand l.2))⁻¹) *
          (ActualPrimaryBounds.copyCost * ChartScales.S n) := by
      apply add_le_add
      · exact (norm_smul_le _ _).trans
          (mul_le_mul (by simpa only [Real.norm_eq_abs] using (phase_constants_bound l).1)
            hangle (norm_nonneg _) hM0)
      · exact (norm_smul_le _ _).trans
          (mul_le_mul (by simpa only [Real.norm_eq_abs] using hd) hz
            (norm_nonneg _) (mul_nonneg hM0 (inv_nonneg.mpr he.le)))
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hprod hM0]

theorem localPhase_positive_jets (m : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ p : ℕ, ∀ n (i : CopyIndex B N0) x,
      x ∈ phaseCell n i → ∀ j, 1 ≤ j → j ≤ m →
      ‖iteratedFDeriv ℝ j (localPhase n i) x‖ ≤ C * ChartScales.S n ^ p *
        (ChartScales.epsilon ActualPrimary.h (BaseChartJets.cellBand i.1.2))⁻¹ := by
  obtain ⟨C, hC, p, hb⟩ := polynomial_copy_bound
    (nativeRemainder_polynomial (B := B) (N0 := N0)) m
  let A := 2 * phaseSize B N0 * ActualPrimaryBounds.copyCost
  have hM := one_le_phaseSize (B := B) (N0 := N0)
  have hK := ActualPrimaryBounds.copyCost_one
  have hA : 1 ≤ A :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (by norm_num) hM) hK
  refine ⟨A + C, by linarith, p + 1, ?_⟩
  intro n i x hx j hj hjm
  have hS := PhysicalGraphBounds.S_ge_one hx.1.1
  have hei := one_le_inverse_epsilon (BaseChartJets.cellBand i.1.2)
  have hs0 : ChartScales.S n ^ p ≤ ChartScales.S n ^ (p + 1) :=
    pow_le_pow_right₀ hS (Nat.le_add_right _ _)
  have hs1 : ChartScales.S n ≤ ChartScales.S n ^ (p + 1) := by
    simpa only [pow_one] using pow_le_pow_right₀ hS (by omega : 1 ≤ p + 1)
  have ha := norm_positive_jet_affine (phaseLinear i.1 n) (phaseOffset n i) x hj
  have hr := polynomial_copy_smooth nativeRemainder_polynomial hx
  have he : localPhase n i = fun y => phaseLinear i.1 n y + phaseOffset n i +
      nativeRemainder i.1 ((ActualPrimaryBounds.fullCopy i.1 n i.2 y).1,
        (ActualPrimaryBounds.fullCopy i.1 n i.2 y).2.2) := funext (localPhase_decomposition n i)
  rw [he, fun_iteratedFDeriv_add_apply
    ((((phaseLinear i.1 n).contDiff.contDiffAt).add contDiffAt_const).of_le (nat_le_infty j))
    (hr.of_le (nat_le_infty j))]
  calc
    _ ≤ ‖iteratedFDeriv ℝ j (fun y => phaseLinear i.1 n y + phaseOffset n i) x‖ +
        ‖iteratedFDeriv ℝ j (fun y => nativeRemainder i.1
          ((ActualPrimaryBounds.fullCopy i.1 n i.2 y).1,
            (ActualPrimaryBounds.fullCopy i.1 n i.2 y).2.2)) x‖ := norm_add_le _ _
    _ ≤ A * ChartScales.S n * (ChartScales.epsilon ActualPrimary.h (BaseChartJets.cellBand
        i.1.2))⁻¹ +
        C * ChartScales.S n ^ p := add_le_add (ha.trans (phaseLinear_bound hx.1)) (hb n i x hx j
            hjm)
    _ ≤ A * ChartScales.S n ^ (p + 1) *
          (ChartScales.epsilon ActualPrimary.h (BaseChartJets.cellBand i.1.2))⁻¹ +
        C * ChartScales.S n ^ (p + 1) *
          (ChartScales.epsilon ActualPrimary.h (BaseChartJets.cellBand i.1.2))⁻¹ := by
      apply add_le_add
      · gcongr
      · exact (mul_le_mul_of_nonneg_left hs0 (zero_le_one.trans hC)).trans
          (le_mul_of_one_le_right (by positivity) hei)
    _ = _ := by ring

/-- The full frequency-weighted phase, with the literal chosen carrier. -/
noncomputable def weightedPhase (l : SignedLabel B N0) (n : ℕ)
    (x : ActualPrimary.FullPoint) : ℝ :=
  (ActualPrimary.chartCoefficients l.1 l.2).frequency n *
    (ActualPrimary.chartCoefficients l.1 l.2).phase n x

theorem weightedPhase_germ {n : ℕ} {i : CopyIndex B N0} {x : ActualPrimary.FullPoint}
    (hx : x ∈ phaseCell n i) :
    weightedPhase i.1 n =ᶠ[𝓝 x] fun y =>
      (ChartScales.carrier ActualPrimary.h (BaseChartJets.cellBand i.1.2) : ℝ) *
        localPhase n i y := by
  have hcore : (ActualPhaseDefect.nativeCopy i.1.1 i.1.2 n i.2 x).2 ∈
      (ActualSignedGeometry.clockWindow ActualPrimary.slots (BaseChartJets.cellBand i.1.2)).core :=
          by
    simp only [← ActualPrimaryBounds.clock_eq i.1]
    exact hx.2.2
  have he := ActualPhaseDefect.chart_phase_germ i.1.1 i.1.2 n
    (CommonWindow.index_le hx.1.2) i.2 hcore
  have hk := (ActualPrimary.chartCoefficients_frequency_pos i.1.1 i.1.2 n).ne'
  filter_upwards [he] with y hy
  unfold weightedPhase
  rw [hy]
  change (ChartScales.carrier ActualPrimary.h n : ℝ) *
    ((ChartScales.carrier ActualPrimary.h (BaseChartJets.cellBand i.1.2) : ℝ) /
      (ChartScales.carrier ActualPrimary.h n : ℝ) * localPhase n i y) = _
  change (ChartScales.carrier ActualPrimary.h n : ℝ) ≠ 0 at hk
  field_simp [hk]

theorem weightedPhase_smooth {n : ℕ} {i : CopyIndex B N0} {x : ActualPrimary.FullPoint}
    (hx : x ∈ phaseCell n i) : ContDiffAt ℝ ∞ (weightedPhase i.1 n) x :=
  (contDiffAt_const.mul (localPhase_smooth hx)).congr_of_eventuallyEq (weightedPhase_germ hx)

theorem inverse_sq_eq_rpow (n : ℕ) :
    (ChartScales.epsilon ActualPrimary.h n)⁻¹ ^ 2 =
      ChartScales.epsilon ActualPrimary.h n ^ (-2 : ℝ) := by
  rw [Real.rpow_neg (ChartScales.epsilon_pos _ _).le, Real.rpow_two, inv_pow]

theorem inverse_epsilon_sq (n : ℕ) :
    (ChartScales.epsilon ActualPrimary.h n)⁻¹ ^ 2 =
      ChartScales.Q n ^ (-(2 * ActualPrimary.h)) := by
  rw [inverse_sq_eq_rpow, ChartScales.epsilon, ← Real.rpow_mul (ChartScales.Q_pos n).le]
  congr 1
  ring

theorem inverse_epsilon_sq_window {l : SignedLabel B N0} {n : ℕ}
    (hn : ActualPrimaryBounds.near l n) :
    (ChartScales.epsilon ActualPrimary.h (BaseChartJets.cellBand l.2))⁻¹ ^ 2 ≤
      ActualSignedGeometry.powerBound (2 * ActualPrimary.h) *
        (ChartScales.epsilon ActualPrimary.h n)⁻¹ ^ 2 := by
  rw [inverse_sq_eq_rpow, inverse_sq_eq_rpow]
  convert! ActualPrimaryBounds.epsilon_power_window
    (ActualPrimaryBounds.near_distance hn).1 (ActualPrimaryBounds.near_distance hn).2 (-2) using 2
  ring_nf

/-- One fixed loss `Q^(-2h)` controls every positive ordinary phase
derivative. Only the constant and the slow power depend on its order. -/
theorem weightedPhase_positive_jets (m : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ p : ℕ, ∀ n (i : CopyIndex B N0) x,
      x ∈ phaseCell n i → ∀ j, 1 ≤ j → j ≤ m →
      ‖iteratedFDeriv ℝ j (weightedPhase i.1 n) x‖ ≤
        C * ChartScales.S n ^ p * ChartScales.Q n ^ (-(2 * ActualPrimary.h)) := by
  obtain ⟨C, hC, p, hb⟩ := localPhase_positive_jets (B := B) (N0 := N0) m
  let W := ActualSignedGeometry.powerBound (2 * ActualPrimary.h)
  have hW : 1 ≤ W := ActualSignedGeometry.powerBound_one _
  refine ⟨2 * C * W, one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (by norm_num) hC) hW, p, ?_⟩
  intro n i x hx j hj hjm
  rw [PhysicalWaveSum.iteratedFDeriv_eq_of_eventuallyEq (weightedPhase_germ hx) j]
  have hd :
      ‖iteratedFDeriv ℝ j (fun y =>
        (ChartScales.carrier ActualPrimary.h (BaseChartJets.cellBand i.1.2) : ℝ) * localPhase n i
            y) x‖ ≤
      (ChartScales.carrier ActualPrimary.h (BaseChartJets.cellBand i.1.2) : ℝ) *
        ‖iteratedFDeriv ℝ j (localPhase n i) x‖ := by
    change ‖iteratedFDeriv ℝ j
      ((ChartScales.carrier ActualPrimary.h (BaseChartJets.cellBand i.1.2) : ℝ) • localPhase n i)
          x‖ ≤ _
    rw [iteratedFDeriv_const_smul_apply ((localPhase_smooth hx).of_le (nat_le_infty j))]
    have hk0 : 0 ≤ (ChartScales.carrier ActualPrimary.h (BaseChartJets.cellBand i.1.2) : ℝ) :=
      Nat.cast_nonneg _
    simpa only [Real.norm_eq_abs, abs_of_nonneg hk0] using
      norm_smul_le (ChartScales.carrier ActualPrimary.h (BaseChartJets.cellBand i.1.2) : ℝ)
        (iteratedFDeriv ℝ j (localPhase n i) x)
  have hS := PhysicalGraphBounds.S_ge_one hx.1.1
  calc
    _ ≤ (ChartScales.carrier ActualPrimary.h (BaseChartJets.cellBand i.1.2) : ℝ) *
        ‖iteratedFDeriv ℝ j (localPhase n i) x‖ := hd
    _ ≤ (2 * (ChartScales.epsilon ActualPrimary.h (BaseChartJets.cellBand i.1.2))⁻¹) *
        (C * ChartScales.S n ^ p *
          (ChartScales.epsilon ActualPrimary.h (BaseChartJets.cellBand i.1.2))⁻¹) := by
      exact mul_le_mul (carrier_le_inverse_epsilon _) (hb n i x hx j hj hjm)
        (norm_nonneg _) (mul_nonneg (by norm_num)
          (inv_nonneg.mpr (ChartScales.epsilon_pos _ _).le))
    _ = (2 * C * ChartScales.S n ^ p) *
        (ChartScales.epsilon ActualPrimary.h (BaseChartJets.cellBand i.1.2))⁻¹ ^ 2 := by ring
    _ ≤ (2 * C * ChartScales.S n ^ p) *
        (W * (ChartScales.epsilon ActualPrimary.h n)⁻¹ ^ 2) :=
      mul_le_mul_of_nonneg_left (inverse_epsilon_sq_window hx.1) (by positivity)
    _ = _ := by rw [inverse_epsilon_sq]; ring

theorem weightedPhase_contDiffOn (l : SignedLabel B N0) (n : ℕ) :
    ContDiffOn ℝ ∞ (weightedPhase l n) ActualPrimaryBounds.fullStrip.domain :=
  contDiffOn_const.mul
    (ActualPrimaryCoherence.piece_phase_smooth ActualPrimaryBounds.region l.1 l.2 n)

/-- The full phase is exactly the zero-angle section plus the fixed
integer angular frequency. -/
theorem weightedPhase_eq_section (l : SignedLabel B N0) (n : ℕ) (x : ActualPrimary.FullPoint) :
    weightedPhase l n x =
      (ActualPrimary.chartCoefficients l.1 l.2).frequency n *
        ActualPrimaryBounds.phase l n x.1 +
          (ActualPrimaryBounds.angularFrequency l n : ℝ) * x.2 := by
  unfold weightedPhase ActualPrimaryBounds.phase
  rw [ActualPrimary.chartCoefficients_phase, ActualPrimary.chartCoefficients_phase]
  simp only [ActualPrimary.absolutePhase, mul_zero, zero_add,
    ActualPrimaryBounds.angularFrequency]
  ring

theorem phaseCell_of_cut_tsupport (l : SignedLabel B N0) (n : ℕ)
    {x : ActualPrimary.FullPoint} (hx : x ∈ ActualPrimaryBounds.fullStrip.domain)
    (hs : x ∈ tsupport ((ActualPrimaryBounds.cutCoefficients l).amplitude n)) :
    ∃ k : TorusInverse.Frequency, x ∈ phaseCell n (l,k) := by
  rcases ActualPrimaryBounds.actual_input_cover l n hx with hc | hz
  · obtain ⟨k,hk⟩ := hc
    exact ⟨k, controlCell_subset_phaseCell n (l,k) hk⟩
  · exact False.elim ((notMem_tsupport_iff_eventuallyEq.mpr hz.1) hs)

theorem weightedPhase_positive_jets_cut (m : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ p : ℕ, ∀ (l : SignedLabel B N0) n x,
      x ∈ ActualPrimaryBounds.fullStrip.domain →
      x ∈ tsupport ((ActualPrimaryBounds.cutCoefficients l).amplitude n) →
      ∀ j, 1 ≤ j → j ≤ m →
      ‖iteratedFDeriv ℝ j (weightedPhase l n) x‖ ≤
        C * ChartScales.S n ^ p * ChartScales.Q n ^ (-(2 * ActualPrimary.h)) := by
  obtain ⟨C,hC,p,hb⟩ := weightedPhase_positive_jets (B := B) (N0 := N0) m
  refine ⟨C,hC,p,?_⟩
  intro l n x hx hs j hj hjm
  obtain ⟨k,hk⟩ := phaseCell_of_cut_tsupport l n hx hs
  exact hb n (l,k) x hk j hj hjm

theorem carrier_eq_character (l : SignedLabel B N0) (n : ℕ) :
    HarmonicCalculus.carrier ((ActualPrimary.chartCoefficients l.1 l.2).frequency n)
      ((ActualPrimary.chartCoefficients l.1 l.2).phase n) =
      PhysicalGraphBounds.character 1 ∘ weightedPhase l n := by
  funext x
  simp only [HarmonicCalculus.carrier, HarmonicCalculus.phaseFactor,
    PhysicalGraphBounds.character, PhysicalGraphBounds.phaseFactor, Function.comp_apply,
    weightedPhase, Complex.ofReal_mul, Complex.ofReal_one, one_mul]
  congr 1
  ring

theorem inverse_power_eq_rpow (n m : ℕ) :
    (ChartScales.epsilon ActualPrimary.h n)⁻¹ ^ (2*m) =
      ChartScales.epsilon ActualPrimary.h n ^ (-(2*(m : ℝ))) := by
  rw [← Real.rpow_natCast, Real.inv_rpow (ChartScales.epsilon_pos _ _).le,
    ← Real.rpow_neg (ChartScales.epsilon_pos _ _).le]
  norm_num

/-- Restoring the unit-modulus exponential uses only positive inner
phase jets.  Its finite-prefix loss is explicit, including order zero. -/
theorem carrier_jets_phaseCell (m : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ p : ℕ, ∀ n (i : CopyIndex B N0) x,
      x ∈ ActualPrimaryBounds.fullStrip.domain → x ∈ phaseCell n i → ∀ j ≤ m,
      ‖iteratedFDeriv ℝ j (HarmonicCalculus.carrier
        ((ActualPrimary.chartCoefficients i.1.1 i.1.2).frequency n)
        ((ActualPrimary.chartCoefficients i.1.1 i.1.2).phase n)) x‖ ≤
      WeightedClasses.majorant ActualPrimaryBounds.fullStrip (fun _ _ => 1)
        (-(2*(m : ℝ))) C p n x := by
  obtain ⟨C,hC,p,hb⟩ := weightedPhase_positive_jets (B := B) (N0 := N0) m
  refine ⟨(m.factorial : ℝ) * C^m, ?_, p*m, ?_⟩
  · exact one_le_mul_of_one_le_of_one_le
      (by exact_mod_cast (Nat.succ_le_of_lt (Nat.factorial_pos m))) (one_le_pow₀ hC)
  intro n i x hx hc j hj
  have hS := PhysicalGraphBounds.S_ge_one hc.1.1
  have hQ : 1 ≤ ChartScales.Q n ^ (-(2*ActualPrimary.h)) := by
    rw [← inverse_epsilon_sq]
    exact one_le_pow₀ (one_le_inverse_epsilon n)
  have hD : 1 ≤ C * ChartScales.S n^p * ChartScales.Q n ^ (-(2*ActualPrimary.h)) :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hC (one_le_pow₀ hS)) hQ
  have hcomp := PhysicalClassBounds.composition_jet_bound
    (PhysicalGraphBounds.character_smooth 1) ActualPrimaryBounds.fullStrip.isOpen_domain
    (weightedPhase_contDiffOn i.1 n) hx m zero_le_one hD
    (fun q _ => by rw [PhysicalGraphBounds.norm_character_jet]; simp)
    (fun q hq hqm => hb n i x hc q hq hqm) j hj
  rw [carrier_eq_character]
  apply hcomp.trans
  have hSG : ChartScales.S n ≤ ActualPrimaryBounds.fullStrip.growth n x := by
    rw [← slow_eq_S hc.1.1]
    exact ActualPrimaryBounds.fullStrip.slow_le_growth n x
  calc
    _ = ((m.factorial : ℝ) * C^m) *
        ChartScales.S n ^ (p*m) * (ChartScales.epsilon ActualPrimary.h n)⁻¹ ^ (2*m) := by
      rw [← inverse_epsilon_sq, mul_one, mul_pow, mul_pow, ← pow_mul, ← pow_mul]
      ring
    _ ≤ ((m.factorial : ℝ) * C^m) *
        ActualPrimaryBounds.fullStrip.growth n x ^ (p*m) *
          (ChartScales.epsilon ActualPrimary.h n)⁻¹ ^ (2*m) := by
      gcongr
      exact pow_nonneg (inv_nonneg.mpr (ChartScales.epsilon_pos _ _).le) _
    _ = _ := by
      rw [inverse_power_eq_rpow, WeightedClasses.majorant, mul_one]
      change _ = ((m.factorial : ℝ) * C^m) *
        ChartScales.epsilon ActualPrimary.h n ^ (-(2*(m : ℝ))) *
          ActualPrimaryBounds.fullStrip.growth n x ^ (p*m)
      ring

/-- The actual cut amplitude's support supplies the needed native copy;
no independent carrier-jet estimate is assumed. -/
theorem carrier_jets_cut (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ p : ℕ, ∃ r : ℝ, ∀ (l : SignedLabel B N0) n x,
      x ∈ ActualPrimaryBounds.fullStrip.domain →
      x ∈ tsupport ((ActualPrimaryBounds.cutCoefficients l).amplitude n) → ∀ j ≤ m,
      ‖iteratedFDeriv ℝ j (HarmonicCalculus.carrier
        ((ActualPrimary.chartCoefficients l.1 l.2).frequency n)
        ((ActualPrimary.chartCoefficients l.1 l.2).phase n)) x‖ ≤
      WeightedClasses.majorant ActualPrimaryBounds.fullStrip (fun _ _ => 1) r C p n x := by
  obtain ⟨C,hC,p,hb⟩ := carrier_jets_phaseCell (B := B) (N0 := N0) m
  refine ⟨C,zero_le_one.trans hC,p,-(2*(m : ℝ)),?_⟩
  intro l n x hx hs j hj
  obtain ⟨k,hk⟩ := phaseCell_of_cut_tsupport l n hx hs
  exact hb n (l,k) x hx hk j hj

theorem phase_jet_le_weighted {n : ℕ} {i : CopyIndex B N0} {x : ActualPrimary.FullPoint}
    (hx : x ∈ phaseCell n i) (j : ℕ) :
    ‖iteratedFDeriv ℝ j ((ActualPrimary.chartCoefficients i.1.1 i.1.2).phase n) x‖ ≤
      ‖iteratedFDeriv ℝ j (weightedPhase i.1 n) x‖ := by
  have hk : 0 < (ActualPrimary.chartCoefficients i.1.1 i.1.2).frequency n :=
    ActualPrimary.chartCoefficients_frequency_pos _ _ _
  have hk' : 0 < (ChartScales.carrier ActualPrimary.h n : ℝ) := hk
  have hkN : 0 < ChartScales.carrier ActualPrimary.h n := by exact_mod_cast hk'
  have hk1 : 1 ≤ (ActualPrimary.chartCoefficients i.1.1 i.1.2).frequency n := by
    change 1 ≤ (ChartScales.carrier ActualPrimary.h n : ℝ)
    exact_mod_cast (Nat.succ_le_of_lt hkN)
  have he : (ActualPrimary.chartCoefficients i.1.1 i.1.2).phase n =
      (fun y => ((ActualPrimary.chartCoefficients i.1.1 i.1.2).frequency n)⁻¹ •
        weightedPhase i.1 n y) := by
    funext y
    simp only [weightedPhase, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hk.ne', one_mul]
  rw [he, iteratedFDeriv_const_smul_apply'
    ((weightedPhase_smooth hx).of_le (nat_le_infty j))]
  have hnorm : ‖((ActualPrimary.chartCoefficients i.1.1 i.1.2).frequency n)⁻¹‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hk)]
    exact (inv_le_one₀ hk).mpr hk1
  exact (norm_smul_le _ _).trans
    (by
      simpa only [one_mul] using (mul_le_mul_of_nonneg_right hnorm
        (norm_nonneg (iteratedFDeriv ℝ j (weightedPhase i.1 n) x))))

/-- The literal normalized phase satisfies the same fixed-loss bound. -/
theorem phase_positive_jets (m : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ p : ℕ, ∀ n (i : CopyIndex B N0) x,
      x ∈ phaseCell n i → ∀ j, 1 ≤ j → j ≤ m →
      ‖iteratedFDeriv ℝ j ((ActualPrimary.chartCoefficients i.1.1 i.1.2).phase n) x‖ ≤
        C * ChartScales.S n ^ p * ChartScales.Q n ^ (-(2 * ActualPrimary.h)) := by
  obtain ⟨C,hC,p,hb⟩ := weightedPhase_positive_jets (B := B) (N0 := N0) m
  exact ⟨C,hC,p,fun n i x hx j hj hjm =>
    (phase_jet_le_weighted hx j).trans (hb n i x hx j hj hjm)⟩

/-- A bounded set of harmonic multiples changes only the constant.
The power of Q is independent of both harmonic and derivative order. -/
theorem harmonicPhase_positive_jets (H : ℝ) (hH : 1 ≤ H) (m : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ p : ℕ, ∀ a : ℝ, |a| ≤ H →
      ∀ n (i : CopyIndex B N0) x, x ∈ phaseCell n i → ∀ j, 1 ≤ j → j ≤ m →
      ‖iteratedFDeriv ℝ j (fun y => a * weightedPhase i.1 n y) x‖ ≤
        C * ChartScales.S n ^ p * ChartScales.Q n ^ (-(2 * ActualPrimary.h)) := by
  obtain ⟨C,hC,p,hb⟩ := weightedPhase_positive_jets (B := B) (N0 := N0) m
  refine ⟨H*C,one_le_mul_of_one_le_of_one_le hH hC,p,?_⟩
  intro a ha n i x hx j hj hjm
  have hn : ‖a‖ ≤ H := by simpa only [Real.norm_eq_abs] using ha
  change ‖iteratedFDeriv ℝ j (fun y => a • weightedPhase i.1 n y) x‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply' ((weightedPhase_smooth hx).of_le (nat_le_infty j))]
  calc
    _ ≤ ‖a‖ * ‖iteratedFDeriv ℝ j (weightedPhase i.1 n) x‖ := norm_smul_le _ _
    _ ≤ H * (C * ChartScales.S n ^ p * ChartScales.Q n ^ (-(2 * ActualPrimary.h))) :=
      mul_le_mul hn (hb n i x hx j hj hjm) (norm_nonneg _) (zero_le_one.trans hH)
    _ = _ := by ring

end NavierStokes.ActualPhaseJetBounds
