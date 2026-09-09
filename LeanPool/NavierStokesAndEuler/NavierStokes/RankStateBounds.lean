/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.LocalRankDefect
import LeanPool.NavierStokesAndEuler.NavierStokes.UniformCone

/-!
# Actual moving-strip bounds for the rank increment

The input is the measured slow debt.  The rank coefficients are the explicit
normalized coordinate formulas, and the output is the literal variable-gauge
State increment.  A fixed containing shell is used only to estimate the
integral; the final class retains the original moving profile weight.
-/

@[expose] public section


namespace NavierStokes.RankStateBounds

noncomputable section

open Set Function Filter MeasureTheory
open scoped ContDiff Topology Interval BigOperators
open WeightedClasses MeanIncrementBounds

/-- Plane: an abbreviation for `PressureStream.Plane`. -/
abbrev Plane := PressureStream.Plane
/-- Point: an abbreviation for `MeanRankUpdate.ChartPoint /-! ## Lifting the actual slow debt
-/`. -/
abbrev Point := MeanRankUpdate.ChartPoint

/-! ## Lifting the actual slow debt -/

/-- Slow projection, given by `(ContinuousLinearMap.fst ℝ Plane Plane).comp
(ContinuousLinearMap.snd ℝ ℝ (Plane × Plane))`. -/
noncomputable def slowProjection : Point →L[ℝ] Plane :=
  (ContinuousLinearMap.fst ℝ Plane Plane).comp
    (ContinuousLinearMap.snd ℝ ℝ (Plane × Plane))

theorem norm_slowProjection_le : ‖slowProjection‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖x.2.1‖ ≤ 1 * ‖x‖
  simp only [one_mul, Prod.norm_def]
  exact (le_max_left _ _).trans (le_max_right _ _)

theorem slowClass_lift {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (s : StripData Point) {U : Set Plane} (hU : IsOpen U)
    (hSU : ∀ x ∈ s.domain, x.2.1 ∈ U) {α : ℝ} {f : ℕ → Plane → F}
    (hf : UnweightedClass (PhysicalMeanDomain.localSlowStripData U hU s.epsilon s.slow
      s.epsilon_pos s.epsilon_le_one s.one_le_slow) α f) :
    UnweightedClass s α (fun n x => f n x.2.1) := by
  refine ⟨fun _ _ _ => zero_le_one, ?_, ?_⟩
  · intro n
    exact ((hf.smooth n).comp_continuousLinearMap slowProjection).mono (fun x hx => hSU x hx)
  · intro m
    obtain ⟨C, hC, k, hb⟩ := hf.bounds m
    refine ⟨C, hC, k, ?_⟩
    intro n x hx j hj
    have hxu : slowProjection x ∈ U := hSU x hx
    have hpre : IsOpen (slowProjection ⁻¹' U) := hU.preimage slowProjection.continuous
    have he := slowProjection.iteratedFDerivWithin_comp_right (hf.smooth n) hU.uniqueDiffOn
      hpre.uniqueDiffOn hxu (ENat.natCast_le_of_coe_top_le_withTop le_rfl j)
    change iteratedFDerivWithin ℝ j (f n ∘ slowProjection) (slowProjection ⁻¹' U) x =
      (iteratedFDerivWithin ℝ j (f n) U (slowProjection x)).compContinuousLinearMap
        (fun _ => slowProjection) at he
    rw [iteratedFDerivWithin_of_isOpen j hpre hxu,
      iteratedFDerivWithin_of_isOpen (f := f n) j hU hxu] at he
    have hn : ‖iteratedFDeriv ℝ j (fun y : Point => f n y.2.1) x‖ ≤
        ‖iteratedFDeriv ℝ j (f n) x.2.1‖ := by
      change ‖iteratedFDeriv ℝ j (f n ∘ slowProjection) x‖ ≤ _
      rw [he]
      apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      exact mul_le_of_le_one_right (norm_nonneg _)
        (pow_le_one₀ (norm_nonneg _) norm_slowProjection_le)
    have hs : ‖iteratedFDeriv ℝ j (f n) x.2.1‖ ≤ C * s.epsilon n ^ α * s.slow n ^ k := by
      simpa only [majorant, StripData.growth, PhysicalMeanDomain.localSlowStripData,
        MeanMomentBounds.slowStripData, inv_one, max_self, mul_one] using hb n x.2.1 hxu j hj
    apply hn.trans (hs.trans _)
    simpa only [majorant, mul_one] using
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (zero_le_one.trans (s.one_le_slow n)) (s.slow_le_growth n x) k)
        (mul_nonneg hC (Real.rpow_pos_of_pos (s.epsilon_pos n) α).le)

theorem debtClass_of_components (s : StripData Plane) {α : ℝ} {d : ℕ → Plane → Fin 3 → ℝ}
    (hd : ∀ i, UnweightedClass s α (fun n x => d n x i)) : UnweightedClass s α d := by
  have ht := MemClass.sum Finset.univ
    (fun i n x => (ContinuousLinearMap.single ℝ (fun _ : Fin 3 => ℝ) i) (d n x i))
    (fun _ _ _ => zero_le_one)
    (fun i _ => (hd i).map (ContinuousLinearMap.single ℝ (fun _ : Fin 3 => ℝ) i))
  have he : (fun n x => ∑ i : Fin 3,
      (ContinuousLinearMap.single ℝ (fun _ : Fin 3 => ℝ) i) (d n x i)) = d := by
    funext n x i
    simp
  rwa [he] at ht

/-! ## Explicit normalized primitive data -/

/-- These are identities of input coefficients, not bounds on a constructed output. -/
structure NormalizedParameters (coord A B : ℝ) (r : CorrectionState.RankData Plane)
    (U : Set Plane) : Prop where
  length : ∀ n x, x ∈ U → r.length n x = VariableGaugeMean.qLength coord x
  velocity : ∀ n x, x ∈ U →
    r.velocity n x = MeanRankUpdate.chartQ coord (0, x, 0) ^ (-A)
  coefficient : ∀ n x, x ∈ U →
    r.coefficient n x = MeanRankUpdate.shapedAmplitude B (MeanRankUpdate.chartEta coord (0, x, 0))

/-- Normalized data, bundling `lambda`, `inner`, `outer`, `length` and the required
compatibility proofs. -/
noncomputable def normalizedData (coord A B lam a b : ℝ) : CorrectionState.RankData Plane where
  lambda := lam
  inner := a
  outer := b
  length := fun _ x => Real.sqrt (MeanRankUpdate.chartQ coord (0, x, 0))
  velocity := fun _ x => MeanRankUpdate.chartQ coord (0, x, 0) ^ (-A)
  coefficient := fun _ x => MeanRankUpdate.shapedAmplitude B (MeanRankUpdate.chartEta coord (0, x,
      0))

theorem normalizedData_parameters (coord A B lam a b : ℝ) (U : Set Plane) :
    NormalizedParameters coord A B (normalizedData coord A B lam a b) U :=
  ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩

namespace NormalizedParameters

variable {coord A B : ℝ} {r : CorrectionState.RankData Plane} {U : Set Plane}
  (h : NormalizedParameters coord A B r U)

include h

theorem angular_eq (c : CorrectionState.Context Point) (u : CorrectionState.State Point)
    (n : ℕ) {z : Point} (hz : z.2.1 ∈ U) :
    MeanRankUpdate.slowLift (CorrectionState.rankAngular r c u n) z =
      MeanRankUpdate.chartAngular coord A B r.lambda r.inner r.outer
        (fun x => CorrectionState.debt c u n x.2.1) z := by
  change MeanRankUpdate.angularIncrement r.lambda (r.coefficient n z.2.1) r.inner r.outer
    (r.length n z.2.1) (r.velocity n z.2.1) (CorrectionState.debt c u n z.2.1) z.1 = _
  rw [h.length n _ hz, h.velocity n _ hz, h.coefficient n _ hz]
  rfl

theorem desired_eq (c : CorrectionState.Context Point) (u : CorrectionState.State Point)
    (n : ℕ) {z : Point} (hz : z.2.1 ∈ U) :
    MeanRankUpdate.slowLift (CorrectionState.rankDesiredAxial r c u n) z =
      MeanRankUpdate.chartAxial coord A B r.lambda r.inner r.outer
        (fun x => CorrectionState.debt c u n x.2.1) z := by
  change MeanRankUpdate.desiredAxialIncrement r.lambda (r.coefficient n z.2.1) r.inner r.outer
    (r.length n z.2.1) (r.velocity n z.2.1) (CorrectionState.debt c u n z.2.1) z.1 = _
  rw [h.length n _ hz, h.velocity n _ hz, h.coefficient n _ hz]
  rfl

end NormalizedParameters

/-! ## A fixed shell used for intermediate estimates -/

open LocalSignedRequest WeightedRadialPrimitive

theorem containingShell {coord a b : ℝ} (U : SlowRegion coord) (ha : 0 < a) (hab : a < b) :
    ∃ lo hi : ℝ, 0 < lo ∧ lo < hi ∧ lo < Real.sqrt U.qlo * a ∧ Real.sqrt U.qhi * b < hi ∧
      (∀ x ∈ U.carrier, lo ≤ VariableGaugeMean.qLength coord x * a) ∧
      (∀ x ∈ U.carrier, VariableGaugeMean.qLength coord x * b ≤ hi) := by
  let lo := Real.sqrt U.qlo * a / 2
  let hi := lo + Real.sqrt U.qhi * b + 1
  have hbase : 0 < Real.sqrt U.qlo * a := mul_pos (Real.sqrt_pos.mpr U.qlo_pos) ha
  have hlo : 0 < lo := div_pos hbase (by norm_num)
  have hlo' : lo < Real.sqrt U.qlo * a := by dsimp [lo]; linarith
  have hb : 0 < b := ha.trans hab
  have htop : 0 ≤ Real.sqrt U.qhi * b := mul_nonneg (Real.sqrt_nonneg _) hb.le
  have horder : lo < hi := by dsimp [hi]; linarith
  have hhi : Real.sqrt U.qhi * b < hi := by dsimp [hi]; linarith
  refine ⟨lo, hi, hlo, horder, hlo', hhi, ?_, ?_⟩
  · intro x hx
    exact hlo'.le.trans (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (U.q_mem x hx).1) ha.le)
  · intro x hx
    exact (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (U.q_mem x hx).2) hb.le).trans hhi.le

theorem fixed_weight_margin {lo hi a b qlo qhi cL cR : ℝ}
    (hlo : 0 < lo) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    (U : Set Plane) (hU : IsOpen U)
    (hleft : lo < Real.sqrt qlo * a) (hright : Real.sqrt qhi * b < hi) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p ∈ (PhysicalMeanDomain.localStripData lo hi cL cR hlo hcL hcR
      ε L hε hεone hL U hU).domain,
      p ∈ MeanRankUpdate.supportBand a b qlo qhi →
        δ ≤ (PhysicalMeanDomain.localStripData lo hi cL cR hlo hcL hcR ε L hε hεone hL U hU).zeta p
            := by
  let base : StripData Point := logStripData lo hi cL cR hlo hcL hcR ε L hε hεone hL
  have hmem : ∀ R ∈ Icc (Real.sqrt qlo * a) (Real.sqrt qhi * b), R ∈ Ioo lo hi :=
    fun R hR => ⟨hleft.trans_le hR.1, hR.2.trans_lt hright⟩
  have hcont : ContinuousOn (fun R : ℝ => base.zeta (R, 0))
      (Icc (Real.sqrt qlo * a) (Real.sqrt qhi * b)) :=
    base.zeta_smooth.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun R hR => hmem R hR)
  obtain ⟨δ, hδ, hbound⟩ := UniformCone.positive_uniform_margin isCompact_Icc hcont
    (fun R hR => zeta_pos cL cR (logPosition_mem hlo (hmem R hR)))
  exact ⟨δ, hδ, fun p _ hp => hbound p.1 hp⟩

section ActualSources

variable {coord A B cL cR : ℝ} (U : SlowRegion coord)
    {g : VariableGaugeMean.GaugeData Plane} {r : CorrectionState.RankData Plane}
    {c : CorrectionState.Context Point} {u : CorrectionState.State Point}
    (hg : LocalRankDefect.RankGeometry g r U.carrier c u)
    (hparam : NormalizedParameters coord A B r U.carrier) (hB : B ≠ 0)
    {lo hi : ℝ} (hlo : 0 < lo) (hcL : 0 < cL) (hcR : 0 < cR)
    (hleft : lo < Real.sqrt U.qlo * r.inner) (hright : Real.sqrt U.qhi * r.outer < hi)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)

include hg hparam hB hleft hright in
/-- The source classes follow from the measured debt and the actual
normalized rank inverse. Neither source class is a premise. -/
theorem rankSources_fixedClass {H : ℝ}
    (hdebt : UnweightedClass (PhysicalMeanDomain.localSlowStripData U.carrier U.isOpen
      ε L hε hεone hL) H (CorrectionState.debt c u)) :
    MeanClass (PhysicalMeanDomain.localStripData lo hi cL cR hlo hcL hcR ε L hε hεone hL U.carrier
        U.isOpen) H
      (fun n => MeanRankUpdate.slowLift (CorrectionState.rankAngular r c u n)) ∧
    MeanClass (PhysicalMeanDomain.localStripData lo hi cL cR hlo hcL hcR ε L hε hεone hL U.carrier
        U.isOpen) H
      (fun n => MeanRankUpdate.slowLift (CorrectionState.rankDesiredAxial r c u n)) := by
  let st := PhysicalMeanDomain.localStripData lo hi cL cR hlo hcL hcR ε L hε hεone hL U.carrier
      U.isOpen
  have hd := slowClass_lift st U.isOpen (fun _ hx => hx.2) hdebt
  have hz := fixed_weight_margin hlo hcL hcR ε L hε hεone hL U.carrier U.isOpen hleft hright
  have hr := MeanRankUpdate.rank_update_meanClass (A := A) (B := B) (lam := r.lambda)
    st U.coord_pos U.coord_lt_one hg.inner_pos hg.inner_lt_outer hB U.qlo_pos
    (fun x hx => U.time_pos x.2.1 hx.2) (fun x hx => U.q_mem x.2.1 hx.2)
    (fun x hx => ⟨hx.1.1.le, hx.1.2.le⟩) hz hd
  exact ⟨MeanRankUpdate.meanClass_congr_on hr.1 (fun n x hx => hparam.angular_eq c u n hx.2),
    MeanRankUpdate.meanClass_congr_on hr.2 (fun n x hx => hparam.desired_eq c u n hx.2)⟩

end ActualSources

section MovingTransfer

variable {coord a b inner outer lo hi cL cR : ℝ} (U : SlowRegion coord)
    (ha : 0 < a) (hlo : 0 < lo) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    (hleft : a < inner) (hright : outer < b)

include hlo hleft hright in
/-- The intermediate fixed shell is removed using actual reserved moving
support and full local band jets. -/
theorem fixedClass_to_moving {H : ℝ} {f : ℕ → Point → ℝ}
    (hf : LocalRankDefect.LocalShell lo hi U.carrier f)
    (hs : ∀ n, VariableGaugeMean.SupportedGauge inner outer (VariableGaugeMean.qLength coord)
        U.carrier (f n))
    (hclass : MeanClass (PhysicalMeanDomain.localStripData lo hi cL cR hlo hcL hcR
      ε L hε hεone hL U.carrier U.isOpen) H f) :
    MeanClass (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) H f :=
  VariableGaugeMean.localBandJets_meanClass_of_gaugeInteriorSupport U ha hcL hcR ε L hε hεone hL
    hleft hright hf.smooth hs
    (PhysicalMeanDomain.meanClass_localBandJets hlo hcL hcR ε L hε hεone hL U.carrier U.isOpen
      hf.smooth hf.supported hclass)

end MovingTransfer

section ActualIncrement

variable {coord A B cL cR : ℝ} (U : SlowRegion coord)
    (g : VariableGaugeMean.GaugeData Plane) (r : CorrectionState.RankData Plane)
    (ha : 0 < g.radial.inner) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    (c : CorrectionState.Context Point) (u : CorrectionState.State Point)
    (hg : LocalRankDefect.RankGeometry g r U.carrier c u)
    (hparam : NormalizedParameters coord A B r U.carrier) (hB : B ≠ 0)
    (hleft : g.radial.inner < r.inner) (hright : r.outer < g.radial.outer)
    (axial : Plane × Plane)

include hg hparam hB hleft hright

/-- The literal variable-gauge rank State update is bounded directly from
the measured slow debt. The radial field gains its actual epsilon factor. -/
theorem rankIncrementState_bounds {H : ℝ}
    (heps : BandBound (movingStripData U g.radial.inner g.radial.outer cL cR ha hcL hcR
      ε L hε hεone hL) 1 c.operators.epsilon)
    (hdebt : UnweightedClass (PhysicalMeanDomain.localSlowStripData U.carrier U.isOpen
      ε L hε hεone hL) H (CorrectionState.debt c u)) :
    IncrementBounds (movingStripData U g.radial.inner g.radial.outer cL cR ha hcL hcR
      ε L hε hεone hL) H (VariableGaugeMean.rankIncrementState g r axial c u) := by
  obtain ⟨lo, hi, hlo, horder, hlo', hhi', hlow, hupp⟩ := containingShell U hg.inner_pos
      hg.inner_lt_outer
  have hlow' (n : ℕ) (x : Plane) (hx : x ∈ U.carrier) : lo ≤ r.length n x * r.inner := by
    rw [hparam.length n x hx]
    exact hlow x hx
  have hupp' (n : ℕ) (x : Plane) (hx : x ∈ U.carrier) : r.length n x * r.outer ≤ hi := by
    rw [hparam.length n x hx]
    exact hupp x hx
  have hsource := rankSources_fixedClass U hg hparam hB hlo hcL hcR hlo' hhi' ε L hε hεone hL hdebt
  have heps' : BandBound (PhysicalMeanDomain.localStripData lo hi cL cR hlo hcL hcR
      ε L hε hεone hL U.carrier U.isOpen) 1 c.operators.epsilon := heps
  have hfixed := LocalRankDefect.RankGeometry.increment_bounds hlo horder hcL hcR ε L hε hεone hL
    U.carrier U.isOpen hg hlow' hupp' axial hsource.1 hsource.2 heps'
  have hlocal := hg.increment_localTriple hlo horder U.isOpen hlow' hupp' axial
  have hsup (n : ℕ) := hg.increment_supportedGauge hlo horder U.isOpen hlow' hupp' axial n
  have hsR (n : ℕ) : VariableGaugeMean.SupportedGauge r.inner r.outer
      (VariableGaugeMean.qLength coord) U.carrier
      ((VariableGaugeMean.rankIncrementState g r axial c u).radial n) := by
    intro z hz hn
    have hh := (hsup n).1 z hz hn
    rwa [hparam.length n _ hz] at hh
  have hsT (n : ℕ) : VariableGaugeMean.SupportedGauge r.inner r.outer
      (VariableGaugeMean.qLength coord) U.carrier
      ((VariableGaugeMean.rankIncrementState g r axial c u).angular n) := by
    intro z hz hn
    have hh := (hsup n).2.1 z hz hn
    rwa [hparam.length n _ hz] at hh
  have hsZ (n : ℕ) : VariableGaugeMean.SupportedGauge r.inner r.outer
      (VariableGaugeMean.qLength coord) U.carrier
      ((VariableGaugeMean.rankIncrementState g r axial c u).axial n) := by
    intro z hz hn
    have hh := (hsup n).2.2 z hz hn
    rwa [hparam.length n _ hz] at hh
  exact ⟨fixedClass_to_moving U ha hlo hcL hcR ε L hε hεone hL hleft hright hlocal.radial hsR
      hfixed.radial,
    fixedClass_to_moving U ha hlo hcL hcR ε L hε hεone hL hleft hright hlocal.angular hsT
        hfixed.angular,
    fixedClass_to_moving U ha hlo hcL hcR ε L hε hεone hL hleft hright hlocal.axial hsZ
        hfixed.axial⟩

theorem rankIncrementState_bounds_of_components {H : ℝ}
    (heps : BandBound (movingStripData U g.radial.inner g.radial.outer cL cR ha hcL hcR
      ε L hε hεone hL) 1 c.operators.epsilon)
    (hdebt : ∀ i : Fin 3, UnweightedClass (PhysicalMeanDomain.localSlowStripData U.carrier U.isOpen
      ε L hε hεone hL) H (fun n x => CorrectionState.debt c u n x i)) :
    IncrementBounds (movingStripData U g.radial.inner g.radial.outer cL cR ha hcL hcR
      ε L hε hεone hL) H (VariableGaugeMean.rankIncrementState g r axial c u) :=
  rankIncrementState_bounds U g r ha hcL hcR ε L hε hεone hL c u hg hparam hB hleft hright axial
      heps
    (debtClass_of_components _ hdebt)

theorem rankIncrementState_bounds_of_defectBounds {σ H : ℝ} (hH : H ≤ 1 + σ)
    (heps : BandBound (movingStripData U g.radial.inner g.radial.outer cL cR ha hcL hcR
      ε L hε hεone hL) 1 c.operators.epsilon)
    (hdebt : CorrectionState.DefectBounds (PhysicalMeanDomain.localSlowStripData U.carrier U.isOpen
      ε L hε hεone hL) σ c u) :
    IncrementBounds (movingStripData U g.radial.inner g.radial.outer cL cR ha hcL hcR
      ε L hε hεone hL) H (VariableGaugeMean.rankIncrementState g r axial c u) :=
  rankIncrementState_bounds_of_components U g r ha hcL hcR ε L hε hεone hL c u hg hparam hB hleft
      hright axial heps
    (fun i => (hdebt i).mono_exponent hH)

omit hB in
/-- One positive profile margin controls every nonzero component of the
actual rank increment, uniformly over bands and slow points. -/
theorem rankIncrementState_support_margin :
    ∃ δ : ℝ, 0 < δ ∧ ∀ n z, z.2.1 ∈ U.carrier →
      ((VariableGaugeMean.rankIncrementState g r axial c u).radial n z ≠ 0 ∨
        (VariableGaugeMean.rankIncrementState g r axial c u).angular n z ≠ 0 ∨
        (VariableGaugeMean.rankIncrementState g r axial c u).axial n z ≠ 0) →
      δ ≤ z.1 / VariableGaugeMean.qLength coord z.2.1 - g.radial.inner ∧
        δ ≤ g.radial.outer - z.1 / VariableGaugeMean.qLength coord z.2.1 := by
  obtain ⟨lo, hi, hlo, horder, _, _, hlow, hupp⟩ := containingShell U hg.inner_pos hg.inner_lt_outer
  have hlow' (n : ℕ) (x : Plane) (hx : x ∈ U.carrier) : lo ≤ r.length n x * r.inner := by
    rw [hparam.length n x hx]
    exact hlow x hx
  have hupp' (n : ℕ) (x : Plane) (hx : x ∈ U.carrier) : r.length n x * r.outer ≤ hi := by
    rw [hparam.length n x hx]
    exact hupp x hx
  let I := VariableGaugeMean.rankIncrementState g r axial c u
  let f : ℕ → Point → ℝ := fun n z => ‖I.radial n z‖ + ‖I.angular n z‖ + ‖I.axial n z‖
  have hs : ∀ n, VariableGaugeMean.SupportedGauge r.inner r.outer (r.length n) U.carrier (f n) := by
    intro n z hz hn
    have hsup := hg.increment_supportedGauge hlo horder U.isOpen hlow' hupp' axial n
    by_cases hR : I.radial n z = 0
    · by_cases hT : I.angular n z = 0
      · apply hsup.2.2 z hz
        intro hZ
        exact hn (by simp only [f, hR, hT, show I.axial n z = 0 from hZ, norm_zero, add_zero])
      · exact hsup.2.1 z hz hT
    · exact hsup.1 z hz hR
  obtain ⟨δ, hδ, hb⟩ := LocalRankDefect.normalized_support_margin hleft hright r.length U.carrier f
      hg.length_pos hs
  refine ⟨δ, hδ, ?_⟩
  intro n z hz hn
  have hpos : 0 < f n z := by
    rcases hn with hR | hT | hZ
    · have hr : 0 < ‖I.radial n z‖ := norm_pos_iff.mpr hR
      dsimp only [f]
      linarith [norm_nonneg (I.angular n z), norm_nonneg (I.axial n z)]
    · have ht : 0 < ‖I.angular n z‖ := norm_pos_iff.mpr hT
      dsimp only [f]
      linarith [norm_nonneg (I.radial n z), norm_nonneg (I.axial n z)]
    · have hz' : 0 < ‖I.axial n z‖ := norm_pos_iff.mpr hZ
      dsimp only [f]
      linarith [norm_nonneg (I.radial n z), norm_nonneg (I.angular n z)]
  have hm := hb n z hz hpos.ne'
  rwa [hparam.length n _ hz] at hm

end ActualIncrement

end

end NavierStokes.RankStateBounds
