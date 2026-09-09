/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.AnnularEndpoint
public import LeanPool.NavierStokesAndEuler.NavierStokes.VariableGaugeMean
public import LeanPool.NavierStokesAndEuler.NavierStokes.PeriodicPhaseAssembly

/-!
# Primitive correction formulas at a nonzero axial endpoint

The positive stable branch of the similarity coordinate continues across
`T = 0` when `Z ≠ 0`.  This file uses that branch in the actual moving-radius
mean operations.  Agreement of primitive data is on whole slow fibers,
because radial and torus integrals are nonlocal on each such fiber.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.OffplaneCorrectionExtensions

open Set Filter Function
open scoped Topology ContDiff BigOperators

/-- Slow: an abbreviation for `PressureStream.Plane`. -/
abbrev Slow := PressureStream.Plane
/-- Lift: an abbreviation for `PressureStream.Lift Slow`. -/
abbrev Lift := PressureStream.Lift Slow
/-- Model: an abbreviation for `MeanRankUpdate.ModelPoint × PressureStream.Plane`. -/
abbrev Model := MeanRankUpdate.ModelPoint × PressureStream.Plane

/-- Stable Q, given by `(PositiveRepresentatives.stableInverse coord s).1`. -/
noncomputable def stableQ (coord : ℝ) (s : Slow) : ℝ :=
  (PositiveRepresentatives.stableInverse coord s).1

/-- Stable length, given by `Real.sqrt (stableQ coord s)`. -/
noncomputable def stableLength (coord : ℝ) (s : Slow) : ℝ := Real.sqrt (stableQ coord s)

theorem stableQ_pos {coord : ℝ} {s : Slow}
    (hs : s ∈ PositiveRepresentatives.stableTarget coord) : 0 < stableQ coord s :=
  (PositiveRepresentatives.stableInverse_spec hs).1.1

theorem stableQ_contDiffAt {coord : ℝ} (hc : 0 < coord) (hc1 : coord < 1) {s : Slow}
    (hs : s ∈ PositiveRepresentatives.stableTarget coord) : ContDiffAt ℝ ∞ (stableQ coord) s :=
  (PositiveRepresentatives.stableInverse_smoothAt hc.le hc1.le hs).fst

theorem stableLength_pos {coord : ℝ} {s : Slow}
    (hs : s ∈ PositiveRepresentatives.stableTarget coord) : 0 < stableLength coord s :=
  Real.sqrt_pos.mpr (stableQ_pos hs)

theorem stableLength_contDiffAt {coord : ℝ} (hc : 0 < coord) (hc1 : coord < 1) {s : Slow}
    (hs : s ∈ PositiveRepresentatives.stableTarget coord) :
    ContDiffAt ℝ ∞ (stableLength coord) s :=
  (stableQ_contDiffAt hc hc1 hs).sqrt (stableQ_pos hs).ne'

theorem stableLength_contDiffOn {coord : ℝ} (hc : 0 < coord) (hc1 : coord < 1) :
    ContDiffOn ℝ ∞ (stableLength coord) (PositiveRepresentatives.stableTarget coord) :=
  fun _ hs => (stableLength_contDiffAt hc hc1 hs).contDiffWithinAt

theorem stableQ_eq_coordinateQ {coord : ℝ} (hc : 0 < coord) (hc1 : coord < 1)
    {s : Slow} (hs : 0 < s.1) : stableQ coord s = SimilarityCoordinates.coordinateQ coord s := by
  exact congrArg Prod.fst (PositiveRepresentatives.stableInverse_eq_inverseMap hc hc1 hs)

theorem stableLength_eq_qLength {coord : ℝ} (hc : 0 < coord) (hc1 : coord < 1)
    {s : Slow} (hs : 0 < s.1) : stableLength coord s = VariableGaugeMean.qLength coord s := by
  exact congrArg Real.sqrt (stableQ_eq_coordinateQ hc hc1 hs)

/-- A neighborhood on which the moving radial interval has fixed positive
inner and finite outer bounds.  These bounds are constructed from the
actual stable branch below. -/
structure Window (coord a b : ℝ) where
  /-- Carrier of `Window`, of type `Set Slow`. -/
  carrier : Set Slow
  isOpen : IsOpen carrier
  stable : carrier ⊆ PositiveRepresentatives.stableTarget coord
  /-- Lower of `Window`, of type `ℝ`. -/
  lower : ℝ
  /-- Upper of `Window`, of type `ℝ`. -/
  upper : ℝ
  lower_pos : 0 < lower
  lower_lt_upper : lower < upper
  left : ∀ s ∈ carrier, lower ≤ stableLength coord s * a
  right : ∀ s ∈ carrier, stableLength coord s * b ≤ upper

theorem exists_window_at {coord a b : ℝ} (hc : 0 < coord) (hc1 : coord < 1)
    (ha : 0 < a) (hab : a < b) {s₀ : Slow}
    (hs : s₀ ∈ PositiveRepresentatives.stableTarget coord) :
    ∃ W : Window coord a b, s₀ ∈ W.carrier := by
  let L := stableLength coord s₀
  have hL : 0 < L := stableLength_pos hs
  have hl := (stableLength_contDiffAt hc hc1 hs).continuousAt
  have hnear : ∀ᶠ s in 𝓝 s₀,
      s ∈ PositiveRepresentatives.stableTarget coord ∧
      L / 2 < stableLength coord s ∧ stableLength coord s < 2 * L := by
    filter_upwards [(PositiveRepresentatives.stableTarget_open coord).mem_nhds hs,
      hl (lt_mem_nhds (half_lt_self hL)), hl (gt_mem_nhds (show L < 2 * L by linarith))]
      with s hst hlo hhi
    exact ⟨hst, hlo, hhi⟩
  obtain ⟨U, hUsub, hU, hzU⟩ := mem_nhds_iff.mp hnear
  refine ⟨⟨U, hU, fun s hs => (hUsub hs).1, L / 2 * a, 2 * L * b,
    mul_pos (half_pos hL) ha, ?_, ?_, ?_⟩, hzU⟩
  · have hprod := mul_lt_mul_of_pos_left hab hL
    have hprodpos := mul_pos hL ha
    nlinarith
  · intro s hsU
    exact mul_le_mul_of_nonneg_right (hUsub hsU).2.1.le ha.le
  · intro s hsU
    exact mul_le_mul_of_nonneg_right (hUsub hsU).2.2.le (ha.trans hab).le

theorem exists_endpoint_window {coord a b Z : ℝ} (hc : 0 < coord) (hc1 : coord < 1)
    (ha : 0 < a) (hab : a < b) (hZ : Z ≠ 0) :
    ∃ W : Window coord a b, (0, Z) ∈ W.carrier :=
  exists_window_at hc hc1 ha hab (EndpointCoordinates.zeroTime_mem_stableTarget hc hc1 hZ)

namespace Window

variable {coord a b : ℝ} (W : Window coord a b)

theorem length_pos {s : Slow} (hs : s ∈ W.carrier) : 0 < stableLength coord s :=
  stableLength_pos (W.stable hs)

theorem length_smooth (hc : 0 < coord) (hc1 : coord < 1) :
    ContDiffOn ℝ ∞ (stableLength coord) W.carrier :=
  (stableLength_contDiffOn hc hc1).mono W.stable

theorem fixed_support {f : Lift → ℝ}
    (hf : VariableGaugeMean.SupportedGauge a b (stableLength coord) W.carrier f) :
    PhysicalMeanDomain.SupportedOn W.lower W.upper W.carrier f := by
  intro p hp hn
  exact ⟨(W.left _ hp).trans (hf p hp hn).1, (hf p hp hn).2.trans (W.right _ hp)⟩

end Window

/-- Positive time is restricted only in the agreement assertion.  The
continued formulas themselves are defined on the full stable neighborhood. -/
noncomputable def positiveSlow : Set Slow := {s | 0 < s.1}

theorem positiveSlow_open : IsOpen positiveSlow := isOpen_lt continuous_const continuous_fst

/-- Fiber agreement, given by `EqOn F f (PhysicalMeanDomain.slowDomain (U ∩ positiveSlow))`. -/
def FiberAgreement {V : Type*} (U : Set Slow) (F f : Lift → V) : Prop :=
  EqOn F f (PhysicalMeanDomain.slowDomain (U ∩ positiveSlow))

theorem FiberAgreement.fiber {V : Type*} {U : Set Slow} {F f : Lift → V}
    (h : FiberAgreement U F f) {s : Slow} (hs : s ∈ U) (ht : 0 < s.1) :
    ∀ r Y, F (r, (s, Y)) = f (r, (s, Y)) :=
  fun _ _ => h ⟨hs, ht⟩

theorem FiberAgreement.eventuallyEq {V : Type*} {U : Set Slow} (hU : IsOpen U) {F f : Lift → V}
    (h : FiberAgreement U F f) {p : Lift} (hp : p.2.1 ∈ U) (ht : 0 < p.2.1.1) :
    F =ᶠ[𝓝 p] f := by
  filter_upwards [(PhysicalMeanDomain.slowDomain_open (hU.inter positiveSlow_open)).mem_nhds
    (show p ∈ PhysicalMeanDomain.slowDomain (U ∩ positiveSlow) from ⟨hp, ht⟩)] with z hz
  exact h hz

/-- A primitive model retains the fast torus coordinate and the physical
radial variable; only the time coordinate is replaced by `q`. -/
noncomputable def stableModel (coord : ℝ) (p : Lift) : Model :=
  ((stableQ coord p.2.1, (p.1, p.2.1.2)), p.2.2)

/-- Physical model, given by `((SimilarityCoordinates.coordinateQ coord p.2.1, (p.1, p.2.1.2)),
p.2.2)`. -/
noncomputable def physicalModel (coord : ℝ) (p : Lift) : Model :=
  ((SimilarityCoordinates.coordinateQ coord p.2.1, (p.1, p.2.1.2)), p.2.2)

/-- Model domain, given by `{y | 0 < y.1.1}`. -/
noncomputable def modelDomain : Set Model := {y | 0 < y.1.1}

theorem modelDomain_open : IsOpen modelDomain :=
  isOpen_lt continuous_const (continuous_fst.comp continuous_fst)

theorem stableModel_contDiffOn {coord : ℝ} (hc : 0 < coord) (hc1 : coord < 1) :
    ContDiffOn ℝ ∞ (stableModel coord)
      (PhysicalMeanDomain.slowDomain (PositiveRepresentatives.stableTarget coord)) := by
  intro p hp
  have hq := (stableQ_contDiffAt hc hc1 hp).comp p contDiffAt_snd.fst
  exact ((hq.prodMk (contDiffAt_fst.prodMk contDiffAt_snd.fst.snd)).prodMk
    contDiffAt_snd.snd).contDiffWithinAt

theorem stableModel_mem {coord : ℝ} {p : Lift}
    (hp : p.2.1 ∈ PositiveRepresentatives.stableTarget coord) :
    stableModel coord p ∈ modelDomain := stableQ_pos hp

/-- Continued source, given by `F ∘ stableModel coord`. -/
noncomputable def continuedSource (coord : ℝ) (F : Model → ℝ) : Lift → ℝ :=
  F ∘ stableModel coord

/-- Physical source, given by `F ∘ physicalModel coord`. -/
noncomputable def physicalSource (coord : ℝ) (F : Model → ℝ) : Lift → ℝ :=
  F ∘ physicalModel coord

theorem continuedSource_smooth {coord : ℝ} (hc : 0 < coord) (hc1 : coord < 1)
    {F : Model → ℝ} (hF : ContDiffOn ℝ ∞ F modelDomain) :
    ContDiffOn ℝ ∞ (continuedSource coord F)
      (PhysicalMeanDomain.slowDomain (PositiveRepresentatives.stableTarget coord)) :=
  hF.comp (stableModel_contDiffOn hc hc1) (fun _ hp => stableModel_mem hp)

theorem continuedSource_agreement {coord : ℝ} (hc : 0 < coord) (hc1 : coord < 1)
    (F : Model → ℝ) (U : Set Slow) :
    FiberAgreement U (continuedSource coord F) (physicalSource coord F) := by
  intro p hp
  simp only [continuedSource, physicalSource, comp_apply, stableModel, physicalModel,
    stableQ_eq_coordinateQ hc hc1 hp.2]

/-- A support condition on the explicit primitive model, before any mean
operation is performed. -/
def ModelSupported {V : Type*} [Zero V] (a b : ℝ) (F : Model → V) : Prop :=
  ∀ y ∈ modelDomain, F y ≠ 0 →
    y.1.2.1 ∈ Icc (Real.sqrt y.1.1 * a) (Real.sqrt y.1.1 * b)

/-- Model periodic, given by `∀ y : MeanRankUpdate.ModelPoint, 0 < y.1 →
FourierAlias.TorusPeriodic (fun Y => F (y, Y))`. -/
def ModelPeriodic (F : Model → ℝ) : Prop :=
  ∀ y : MeanRankUpdate.ModelPoint, 0 < y.1 →
    FourierAlias.TorusPeriodic (fun Y => F (y, Y))

theorem continuedSource_periodic {coord : ℝ} {F : Model → ℝ} (hF : ModelPeriodic F)
    {U : Set Slow} (hU : U ⊆ PositiveRepresentatives.stableTarget coord) :
    PhysicalMeanDomain.PeriodicOn U (continuedSource coord F) := by
  intro r s hs
  exact hF (stableQ coord s, (r, s.2)) (stableQ_pos (hU hs))

theorem continuedSource_supported {coord a b : ℝ} {F : Model → ℝ}
    (hF : ModelSupported a b F) {U : Set Slow}
    (hU : U ⊆ PositiveRepresentatives.stableTarget coord) :
    VariableGaugeMean.SupportedGauge a b (stableLength coord) U (continuedSource coord F) := by
  intro p hp hn
  exact hF (stableModel coord p) (stableModel_mem (hU hp)) hn

namespace Window

variable {coord a b : ℝ} (W : Window coord a b)
    (hc : 0 < coord) (hc1 : coord < 1)

include hc hc1

theorem compactPrimitive_smooth (ha : 0 < a) (hab : a < b) {d : ℝ} (hd : 0 < d)
    (M : ℝ) (v : Slow) {f : Lift → ℝ}
    (hf : ContDiffOn ℝ ∞ f (PhysicalMeanDomain.slowDomain W.carrier))
    (hs : VariableGaugeMean.SupportedGauge a b (stableLength coord) W.carrier f) :
    ContDiffOn ℝ ∞ (VariableGaugeMean.compactPrimitive d a b M (stableLength coord) v f)
      (PhysicalMeanDomain.slowDomain W.carrier) :=
  VariableGaugeMean.compactPrimitive_contDiffOn W.lower_pos W.lower_lt_upper ha hab hd v
    W.isOpen (W.length_smooth hc hc1) (fun _ hs => W.length_pos hs) W.left W.right hf hs

theorem pressureSource_smooth (hab : a < b) {f : Lift → ℝ}
    (hf : ContDiffOn ℝ ∞ f (PhysicalMeanDomain.slowDomain W.carrier))
    (hs : VariableGaugeMean.SupportedGauge a b (stableLength coord) W.carrier f) :
    ContDiffOn ℝ ∞ (VariableGaugeMean.pressureSource a b hab (stableLength coord) f)
      (PhysicalMeanDomain.slowDomain W.carrier) :=
  hf.sub ((VariableGaugeMean.density_contDiffOn hab (W.length_smooth hc hc1)
    (fun _ hs => W.length_pos hs)).mul
      (PhysicalMeanDomain.liftedPressureMass_contDiffOn W.isOpen hf (W.fixed_support hs)))

theorem meanPressure_smooth (ha : 0 < a) (hab : a < b) {d : ℝ} (hd : 0 < d)
    (M : ℝ) (v : Slow) {f : Lift → ℝ}
    (hf : ContDiffOn ℝ ∞ f (PhysicalMeanDomain.slowDomain W.carrier))
    (hs : VariableGaugeMean.SupportedGauge a b (stableLength coord) W.carrier f) :
    ContDiffOn ℝ ∞ (VariableGaugeMean.meanPressure d a b M hab (stableLength coord) v f)
      (PhysicalMeanDomain.slowDomain W.carrier) :=
  W.compactPrimitive_smooth hc hc1 ha hab hd M v
    (W.pressureSource_smooth hc hc1 hab hf hs)
    (VariableGaugeMean.pressureSource_supported hab (fun _ hs => W.length_pos hs) hs)

theorem streamPotential_smooth (ha : 0 < a) (hab : a < b) {d : ℝ} (hd : 0 < d)
    (M : ℝ) (v : Slow) {f : Lift → ℝ}
    (hf : ContDiffOn ℝ ∞ f (PhysicalMeanDomain.slowDomain W.carrier))
    (hs : VariableGaugeMean.SupportedGauge a b (stableLength coord) W.carrier f) :
    ContDiffOn ℝ ∞ (VariableGaugeMean.streamPotential d a b M (stableLength coord) v f)
      (PhysicalMeanDomain.slowDomain W.carrier) := by
  have hws : VariableGaugeMean.SupportedGauge a b (stableLength coord) W.carrier
      (PressureStream.weightedSource f) := fun p hp hn => hs p hp (right_ne_zero_of_mul hn)
  have hwf : ContDiffOn ℝ ∞ (PressureStream.weightedSource f)
      (PhysicalMeanDomain.slowDomain W.carrier) := contDiffOn_fst.mul hf
  have hI := W.compactPrimitive_smooth hc hc1 ha hab hd M v hwf hws
  have hIs := VariableGaugeMean.compactPrimitive_supportedGauge (M := M) ha hab hd
    (stableLength coord) v W.isOpen (fun _ hs => W.length_pos hs) hwf hws
  exact VariableGaugeMean.divideRadius_contDiffOn W.lower_pos W.isOpen hI (W.fixed_support hIs)

theorem compactAlias_smooth (ha : 0 < a) (hab : a < b) {d : ℝ} (hd : 0 < d)
    (M : ℝ) (v : Slow) {f : Lift → ℝ}
    (hf : ContDiffOn ℝ ∞ f (PhysicalMeanDomain.slowDomain W.carrier))
    (hs : VariableGaugeMean.SupportedGauge a b (stableLength coord) W.carrier f) :
    ContDiffOn ℝ ∞ (VariableGaugeMean.compactAlias d a b M (stableLength coord) v f)
      (PhysicalMeanDomain.slowDomain W.carrier) := by
  have hC := VariableGaugeMean.cutoffRadialDerivative_contDiffOn ha d b
    (W.length_smooth hc hc1) (fun _ hs => W.length_pos hs)
  have hJ := VariableGaugeMean.physicalTotal_contDiffOn (M := M)
    W.lower_pos W.lower_lt_upper hd v W.isOpen hf (W.fixed_support hs)
  apply (hC.mul hJ).congr
  intro p hp
  exact VariableGaugeMean.compactAlias_reference W.lower_pos ha hab hd (stableLength coord) v
    (fun _ hs => W.length_pos hs) W.left hs p hp

end Window

section ExactAgreement

variable {coord : ℝ} (hc : 0 < coord) (hc1 : coord < 1)
    {U : Set Slow} {F f : Lift → ℝ} (he : FiberAgreement U F f)

include hc hc1 he

theorem compactPrimitive_agreement (d a b M : ℝ) (v : Slow) :
    FiberAgreement U (VariableGaugeMean.compactPrimitive d a b M (stableLength coord) v F)
      (VariableGaugeMean.compactPrimitive d a b M (VariableGaugeMean.qLength coord) v f) := by
  intro p hp
  dsimp only [VariableGaugeMean.compactPrimitive]
  rw [stableLength_eq_qLength hc hc1 hp.2]
  exact PhysicalMeanDomain.physicalCompact_fiberLocal d _ _ M v F f p.2.1
    (he.fiber hp.1 hp.2) p.1 p.2.2

theorem pressureSource_agreement (a b : ℝ) (hab : a < b) :
    FiberAgreement U (VariableGaugeMean.pressureSource a b hab (stableLength coord) F)
      (VariableGaugeMean.pressureSource a b hab (VariableGaugeMean.qLength coord) f) := by
  intro p hp
  have hm : PressureStream.pressureMass F p.2.1 = PressureStream.pressureMass f p.2.1 :=
    PhysicalMeanDomain.liftedPressureMass_fiberLocal F f p.2.1 (he.fiber hp.1 hp.2) p.1 p.2.2
  dsimp only [VariableGaugeMean.pressureSource, VariableGaugeMean.density,
    VariableGaugeMean.radialRatio]
  rw [he hp, hm, stableLength_eq_qLength hc hc1 hp.2]

theorem meanPressure_agreement (d a b M : ℝ) (hab : a < b) (v : Slow) :
    FiberAgreement U (VariableGaugeMean.meanPressure d a b M hab (stableLength coord) v F)
      (VariableGaugeMean.meanPressure d a b M hab (VariableGaugeMean.qLength coord) v f) :=
  compactPrimitive_agreement hc hc1 (pressureSource_agreement hc hc1 he a b hab) d a b M v

theorem streamPotential_agreement (d a b M : ℝ) (v : Slow) :
    FiberAgreement U (VariableGaugeMean.streamPotential d a b M (stableLength coord) v F)
      (VariableGaugeMean.streamPotential d a b M (VariableGaugeMean.qLength coord) v f) := by
  have hw : FiberAgreement U (PressureStream.weightedSource F) (PressureStream.weightedSource f) :=
      by
    intro p hp
    exact congrArg (fun t => p.1 * t) (he hp)
  intro p hp
  exact congrArg (fun t => t / p.1) (compactPrimitive_agreement hc hc1 hw d a b M v hp)

theorem compactAlias_agreement (d a b M : ℝ) (v : Slow) :
    FiberAgreement U (VariableGaugeMean.compactAlias d a b M (stableLength coord) v F)
      (VariableGaugeMean.compactAlias d a b M (VariableGaugeMean.qLength coord) v f) := by
  intro p hp
  dsimp only [VariableGaugeMean.compactAlias]
  rw [stableLength_eq_qLength hc hc1 hp.2]
  exact PhysicalMeanDomain.physicalAlias_fiberLocal d _ _ M v F f p.2.1
    (he.fiber hp.1 hp.2) p.1 p.2.2

omit hc hc1 in
theorem temporalAtIndex_agreement (h : ℝ) (n i : ℕ) :
    FiberAgreement U (MeanChartCompatibility.temporalAtIndex h n i F)
      (MeanChartCompatibility.temporalAtIndex h n i f) := by
  intro p hp
  exact VariableGaugeMean.temporalAtIndex_fiberLocal h n i F f p.2.1
    (he.fiber hp.1 hp.2) p.1 p.2.2

end ExactAgreement

/-- A full-fiber primitive continuation.  Constructors below obtain such
data from explicit positive-q models, then preserve it through the actual
nonlocal mean operations. -/
structure SupportedContinuation {coord a b : ℝ} (W : Window coord a b) (f : Lift → ℝ) where
  /-- Value of `SupportedContinuation`, of type `Lift → ℝ`. -/
  value : Lift → ℝ
  smooth : ContDiffOn ℝ ∞ value (PhysicalMeanDomain.slowDomain W.carrier)
  supported : VariableGaugeMean.SupportedGauge a b (stableLength coord) W.carrier value
  agrees : FiberAgreement W.carrier value f

namespace SupportedContinuation

variable {coord a b : ℝ} {W : Window coord a b} (hc : 0 < coord) (hc1 : coord < 1)

/-- Of model, bundling `value`, `smooth`, `supported`, `agrees`. -/
noncomputable def ofModel (F : Model → ℝ) (hF : ContDiffOn ℝ ∞ F modelDomain)
    (hs : ModelSupported a b F) : SupportedContinuation W (physicalSource coord F) where
  value := continuedSource coord F
  smooth := (continuedSource_smooth hc hc1 hF).mono (fun _ hp => W.stable hp)
  supported := continuedSource_supported hs W.stable
  agrees := continuedSource_agreement hc hc1 F W.carrier

/-- Primitive, bundling `value`, `smooth`, `supported`, `W` and the required compatibility
proofs. -/
noncomputable def primitive {f : Lift → ℝ} (e : SupportedContinuation W f)
    (ha : 0 < a) (hab : a < b) {d : ℝ} (hd : 0 < d) (M : ℝ) (v : Slow) :
    SupportedContinuation W
      (VariableGaugeMean.compactPrimitive d a b M (VariableGaugeMean.qLength coord) v f) where
  value := VariableGaugeMean.compactPrimitive d a b M (stableLength coord) v e.value
  smooth := W.compactPrimitive_smooth hc hc1 ha hab hd M v e.smooth e.supported
  supported := VariableGaugeMean.compactPrimitive_supportedGauge ha hab hd (stableLength coord) v
    W.isOpen (fun _ hs => W.length_pos hs) e.smooth e.supported
  agrees := compactPrimitive_agreement hc hc1 e.agrees d a b M v

/-- Pressure, bundling `value`, `smooth`, `supported`, `W` and the required compatibility
proofs. -/
noncomputable def pressure {f : Lift → ℝ} (e : SupportedContinuation W f)
    (ha : 0 < a) (hab : a < b) {d : ℝ} (hd : 0 < d) (M : ℝ) (v : Slow) :
    SupportedContinuation W
      (VariableGaugeMean.meanPressure d a b M hab (VariableGaugeMean.qLength coord) v f) where
  value := VariableGaugeMean.meanPressure d a b M hab (stableLength coord) v e.value
  smooth := W.meanPressure_smooth hc hc1 ha hab hd M v e.smooth e.supported
  supported := VariableGaugeMean.compactPrimitive_supportedGauge ha hab hd (stableLength coord) v
    W.isOpen (fun _ hs => W.length_pos hs) (W.pressureSource_smooth hc hc1 hab e.smooth e.supported)
    (VariableGaugeMean.pressureSource_supported hab (fun _ hs => W.length_pos hs) e.supported)
  agrees := meanPressure_agreement hc hc1 e.agrees d a b M hab v

/-- Stream, bundling `value`, `smooth`, `supported`, `W` and the required compatibility proofs. -/
noncomputable def stream {f : Lift → ℝ} (e : SupportedContinuation W f)
    (ha : 0 < a) (hab : a < b) {d : ℝ} (hd : 0 < d) (M : ℝ) (v : Slow) :
    SupportedContinuation W
      (VariableGaugeMean.streamPotential d a b M (VariableGaugeMean.qLength coord) v f) where
  value := VariableGaugeMean.streamPotential d a b M (stableLength coord) v e.value
  smooth := W.streamPotential_smooth hc hc1 ha hab hd M v e.smooth e.supported
  supported := VariableGaugeMean.streamPotential_supportedGauge ha hab hd (stableLength coord) v
    W.isOpen (fun _ hs => W.length_pos hs) e.smooth e.supported
  agrees := streamPotential_agreement hc hc1 e.agrees d a b M v

/-- Alias field, bundling `value`, `smooth`, `supported`, `agrees`. -/
noncomputable def aliasField {f : Lift → ℝ} (e : SupportedContinuation W f)
    (ha : 0 < a) (hab : a < b) {d : ℝ} (hd : 0 < d) (M : ℝ) (v : Slow) :
    SupportedContinuation W
      (VariableGaugeMean.compactAlias d a b M (VariableGaugeMean.qLength coord) v f) where
  value := VariableGaugeMean.compactAlias d a b M (stableLength coord) v e.value
  smooth := W.compactAlias_smooth hc hc1 ha hab hd M v e.smooth e.supported
  supported := by
    intro p hp hn
    exact RadialPullback.physicalAlias_supported (mul_pos (W.length_pos hp) ha)
      (mul_lt_mul_of_pos_left hab (W.length_pos hp)) hd M ((0 : Slow), v) e.value hn
  agrees := compactAlias_agreement hc hc1 e.agrees d a b M v

omit hc hc1 in
/-- Temporal, bundling `value`, `smooth`, `supported`, `agrees`. -/
noncomputable def temporal {f : Lift → ℝ} (e : SupportedContinuation W f)
    (h : ℝ) (n i : ℕ) (hp : PhysicalMeanDomain.PeriodicOn W.carrier e.value) :
    SupportedContinuation W (MeanChartCompatibility.temporalAtIndex h n i f) where
  value := MeanChartCompatibility.temporalAtIndex h n i e.value
  smooth := VariableGaugeMean.temporalAtIndex_contDiffOn h n i W.isOpen e.smooth hp
  supported := VariableGaugeMean.temporalAtIndex_supportedGauge h n i e.supported
  agrees := temporalAtIndex_agreement e.agrees h n i

end SupportedContinuation

namespace SupportedContinuation

variable {coord a b : ℝ} {W : Window coord a b}

/-- Scale slow, bundling `value`, `smooth`, `supported`, `agrees`. -/
noncomputable def scaleSlow {f : Lift → ℝ} (e : SupportedContinuation W f)
    {c : Slow → ℝ} (C : Slow → ℝ) (hC : ContDiffOn ℝ ∞ C W.carrier)
    (he : EqOn C c (W.carrier ∩ positiveSlow)) :
    SupportedContinuation W (fun p => c p.2.1 * f p) where
  value := fun p => C p.2.1 * e.value p
  smooth := (hC.comp contDiffOn_snd.fst (fun _ hp => hp)).mul e.smooth
  supported := fun p hp hn => e.supported p hp (right_ne_zero_of_mul hn)
  agrees := fun _ hp => congrArg₂ (fun x y : ℝ => x * y) (he hp) (e.agrees hp)

/-- Finite sum, bundling `value`, `smooth`, `supported`, `agrees` and the required compatibility
proofs. -/
noncomputable def finiteSum {ι : Type*} (s : Finset ι) (f : ι → Lift → ℝ)
    (e : ∀ i, SupportedContinuation W (f i)) :
    SupportedContinuation W (fun p => ∑ i ∈ s, f i p) where
  value := fun p => ∑ i ∈ s, (e i).value p
  smooth := ContDiffOn.sum (fun i _ => (e i).smooth)
  supported := by
    intro p hp hn
    by_contra hr
    apply hn
    apply Finset.sum_eq_zero
    intro i _
    by_contra hi
    exact hr ((e i).supported p hp hi)
  agrees := by
    intro p hp
    exact Finset.sum_congr rfl (fun i _ => (e i).agrees hp)

/-- Actual radial/torus integration produces smooth slow debt coefficients
on the continued neighborhood. -/
theorem pressureMass_smooth {f : Lift → ℝ} (e : SupportedContinuation W f) :
    ContDiffOn ℝ ∞ (PressureStream.pressureMass e.value) W.carrier := by
  have hm := PhysicalMeanDomain.liftedPressureMass_contDiffOn W.isOpen e.smooth (W.fixed_support
      e.supported)
  have hmap : ContDiffOn ℝ ∞ (fun s : Slow => ((0 : ℝ), (s, (0 : Slow)))) W.carrier :=
    contDiffOn_const.prodMk (contDiffOn_id.prodMk contDiffOn_const)
  exact hm.comp hmap (fun _ hp => hp)

theorem pressureMass_agreement {f : Lift → ℝ} (e : SupportedContinuation W f) :
    EqOn (PressureStream.pressureMass e.value) (PressureStream.pressureMass f)
      (W.carrier ∩ positiveSlow) := by
  intro s hs
  exact PhysicalMeanDomain.liftedPressureMass_fiberLocal e.value f s (e.agrees.fiber hs.1 hs.2) 0 0

theorem support_on_past {f : Lift → ℝ} (e : SupportedContinuation W f)
    (hc : 0 < coord) (hc1 : coord < 1) {p : Lift}
    (hp : p.2.1 ∈ W.carrier) (ht : 0 < p.2.1.1) (hn : f p ≠ 0) :
    p.1 ∈ Icc (VariableGaugeMean.qLength coord p.2.1 * a)
      (VariableGaugeMean.qLength coord p.2.1 * b) := by
  have he := e.agrees ⟨hp, ht⟩
  have hs := e.supported p hp (fun hzero => hn (he.symm.trans hzero))
  simpa only [stableLength_eq_qLength hc hc1 ht] using hs

end SupportedContinuation

section ReferenceODE

variable {P Q V E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Reparameterize primitive ODE coefficients and forcing, while keeping
the native-copy path and its entry point unchanged. -/
noncomputable def pullLinearData (φ : P → Q) (d : CommonCoverSolve.LinearData Q V E) :
    CommonCoverSolve.LinearData P V E where
  coefficient := fun p => d.coefficient (φ p.1, p.2)
  forcingMap := fun p => d.forcingMap (φ p.1, p.2)
  source := fun p => d.source (φ p.1, p.2)

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [CompleteSpace E] in
theorem coefficientPath_pull (φ : P → Q) (d : CommonCoverSolve.LinearData Q V E)
    (g : CommonCoverSolve.Geometry) (k : TorusInverse.Frequency) (p : P × Slow) (a b : ℝ) :
    (pullLinearData φ d).coefficientPath (a := a) (b := b) g k p =
      d.coefficientPath g k (φ p.1, p.2) := rfl

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [CompleteSpace E] in
theorem forcingPath_pull (φ : P → Q) (d : CommonCoverSolve.LinearData Q V E)
    (g : CommonCoverSolve.Geometry) (k : TorusInverse.Frequency) (p : P × Slow) (a b : ℝ) :
    (pullLinearData φ d).forcingPath (a := a) (b := b) g k p =
      d.forcingPath g k (φ p.1, p.2) := rfl

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Q] [NormedSpace ℝ Q] in
/-- This is the actual Volterra solution operator, including its anchored
path.  Reparameterization is an equality of definitions. -/
theorem copySolve_pull (φ : P → Q) (d : CommonCoverSolve.LinearData Q V E)
    (g : CommonCoverSolve.Geometry) {a b : ℝ} (hab : a ≤ b)
    (k : TorusInverse.Frequency) (p : P × Slow) :
    (pullLinearData φ d).copySolve g hab k p = d.copySolve g hab k (φ p.1, p.2) := rfl

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Q] [NormedSpace ℝ Q] in
theorem commonSolve_pull (φ : P → Q) (d : CommonCoverSolve.LinearData Q V E)
    (g : CommonCoverSolve.Geometry) {a b : ℝ} (hab : a ≤ b)
    (κ : Slow → ℝ) (p : P × Slow) :
    (pullLinearData φ d).commonSolve g hab κ p = d.commonSolve g hab κ (φ p.1, p.2) := rfl

end ReferenceODE

section ContinuedReferenceODE

variable {V E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Stable parameter, given by `(stableQ coord p.2, (p.1, p.2.2))`. -/
noncomputable def stableParameter (coord : ℝ) (p : ℝ × Slow) : MeanRankUpdate.ModelPoint :=
  (stableQ coord p.2, (p.1, p.2.2))

/-- Physical parameter, given by `(SimilarityCoordinates.coordinateQ coord p.2, (p.1, p.2.2))`. -/
noncomputable def physicalParameter (coord : ℝ) (p : ℝ × Slow) : MeanRankUpdate.ModelPoint :=
  (SimilarityCoordinates.coordinateQ coord p.2, (p.1, p.2.2))

/-- Continued reference solve, defined pointwise by `(pullLinearData (stableParameter coord)
d).commonSolve g hab κ ((p.1, p.2.1), p.2.2)`. -/
noncomputable def continuedReferenceSolve (coord : ℝ)
    (d : CommonCoverSolve.LinearData MeanRankUpdate.ModelPoint V E)
    (g : CommonCoverSolve.Geometry) {a b : ℝ} (hab : a ≤ b) (κ : Slow → ℝ) : Lift → E :=
  fun p => (pullLinearData (stableParameter coord) d).commonSolve g hab κ ((p.1, p.2.1), p.2.2)

/-- Physical reference solve, defined pointwise by `(pullLinearData (physicalParameter coord)
d).commonSolve g hab κ ((p.1, p.2.1), p.2.2)`. -/
noncomputable def physicalReferenceSolve (coord : ℝ)
    (d : CommonCoverSolve.LinearData MeanRankUpdate.ModelPoint V E)
    (g : CommonCoverSolve.Geometry) {a b : ℝ} (hab : a ≤ b) (κ : Slow → ℝ) : Lift → E :=
  fun p => (pullLinearData (physicalParameter coord) d).commonSolve g hab κ ((p.1, p.2.1), p.2.2)

theorem continuedReferenceSolve_eq (coord : ℝ)
    (d : CommonCoverSolve.LinearData MeanRankUpdate.ModelPoint V E)
    (g : CommonCoverSolve.Geometry) {a b : ℝ} (hab : a ≤ b) (κ : Slow → ℝ) :
    continuedReferenceSolve coord d g hab κ = d.commonSolve g hab κ ∘ stableModel coord := rfl

theorem physicalReferenceSolve_eq (coord : ℝ)
    (d : CommonCoverSolve.LinearData MeanRankUpdate.ModelPoint V E)
    (g : CommonCoverSolve.Geometry) {a b : ℝ} (hab : a ≤ b) (κ : Slow → ℝ) :
    physicalReferenceSolve coord d g hab κ = d.commonSolve g hab κ ∘ physicalModel coord := rfl

/-- The actual sum of localized native Volterra solves continues smoothly
from smooth primitive matrix, conversion map, and source models.  No
regularity assumption is made on a solved amplitude. -/
theorem continuedReferenceSolve_smooth {coord : ℝ} (hc : 0 < coord) (hc1 : coord < 1)
    (d : CommonCoverSolve.LinearData MeanRankUpdate.ModelPoint V E)
    (g : CommonCoverSolve.Geometry) {a b : ℝ} (hab : a ≤ b)
    (hA : ContDiffOn ℝ ∞ d.coefficient (PhysicalCoordinateBounds.positiveTime ×ˢ univ))
    (hB : ContDiffOn ℝ ∞ d.forcingMap (PhysicalCoordinateBounds.positiveTime ×ˢ univ))
    (hf : ContDiffOn ℝ ∞ d.source (PhysicalCoordinateBounds.positiveTime ×ˢ univ))
    {κ : Slow → ℝ} (hκ : ContDiff ℝ ∞ κ) (hcκ : HasCompactSupport κ)
    (hsκ : tsupport κ ⊆ univ ×ˢ Ioo a b) :
    ContDiffOn ℝ ∞ (continuedReferenceSolve coord d g hab κ)
      (PhysicalMeanDomain.slowDomain (PositiveRepresentatives.stableTarget coord)) := by
  have hsolve := d.commonSolve_contDiffOn g hab PhysicalCoordinateBounds.positiveTime_isOpen
    hA hB hf hκ hcκ hsκ
  exact hsolve.comp (stableModel_contDiffOn hc hc1)
    (fun _ hp => ⟨stableQ_pos hp, mem_univ _⟩)

theorem referenceSolve_agreement {coord : ℝ} (hc : 0 < coord) (hc1 : coord < 1)
    (d : CommonCoverSolve.LinearData MeanRankUpdate.ModelPoint V E)
    (g : CommonCoverSolve.Geometry) {a b : ℝ} (hab : a ≤ b) (κ : Slow → ℝ) (U : Set Slow) :
    FiberAgreement U (continuedReferenceSolve coord d g hab κ)
      (physicalReferenceSolve coord d g hab κ) := by
  intro p hp
  rw [continuedReferenceSolve_eq, physicalReferenceSolve_eq]
  simp only [comp_apply, stableModel, physicalModel, stableQ_eq_coordinateQ hc hc1 hp.2]

/-- Radial support of the primitive forcing propagates through the
zero-entry Volterra solve and the actual sum of its native copies. -/
theorem referenceSolve_model_supported
    (d : CommonCoverSolve.LinearData MeanRankUpdate.ModelPoint V E)
    (g : CommonCoverSolve.Geometry) {s t : ℝ} (hst : s ≤ t) (κ : Slow → ℝ)
    {a b : ℝ} (hs : ModelSupported a b d.source) :
    ModelSupported a b (d.commonSolve g hst κ) := by
  intro y hy hn
  by_contra hr
  have hsource : ∀ Y : Slow, d.source (y.1, Y) = 0 := by
    intro Y
    by_contra hne
    exact hr (hs (y.1, Y) hy hne)
  have hcopy (k : TorusInverse.Frequency) : d.copySolve g hst k y = 0 :=
    d.copySolve_zero_of_source_zero g hst k y.1 y.2 (fun _ _ => hsource _)
  apply hn
  simp only [CommonCoverSolve.LinearData.commonSolve, CommonCoverSolve.LinearData.localizedCopy,
    hcopy, smul_zero, tsum_zero]

/-- A real component of an actual reference solve supplies a primitive
continuation for the mean calculus.  Its smoothness and support are derived
from the ODE inputs, not assumed for the solved component. -/
noncomputable def referenceContinuation {coord a b : ℝ} {W : Window coord a b}
    (hc : 0 < coord) (hc1 : coord < 1)
    (d : CommonCoverSolve.LinearData MeanRankUpdate.ModelPoint V E)
    (g : CommonCoverSolve.Geometry) {s t : ℝ} (hst : s ≤ t)
    (hA : ContDiffOn ℝ ∞ d.coefficient (PhysicalCoordinateBounds.positiveTime ×ˢ univ))
    (hB : ContDiffOn ℝ ∞ d.forcingMap (PhysicalCoordinateBounds.positiveTime ×ˢ univ))
    (hf : ContDiffOn ℝ ∞ d.source (PhysicalCoordinateBounds.positiveTime ×ˢ univ))
    (hs : ModelSupported a b d.source)
    {κ : Slow → ℝ} (hκ : ContDiff ℝ ∞ κ) (hcκ : HasCompactSupport κ)
    (hsκ : tsupport κ ⊆ univ ×ˢ Ioo s t) (L : E →L[ℝ] ℝ) :
    SupportedContinuation W (fun p => L (physicalReferenceSolve coord d g hst κ p)) := by
  have hmodel := d.commonSolve_contDiffOn g hst PhysicalCoordinateBounds.positiveTime_isOpen
    hA hB hf hκ hcκ hsκ
  have hsmodel := referenceSolve_model_supported d g hst κ hs
  refine SupportedContinuation.ofModel hc hc1 (fun y => L (d.commonSolve g hst κ y)) ?_ ?_
  · exact (L.contDiff.comp_contDiffOn hmodel).mono (fun y hy => ⟨hy, mem_univ _⟩)
  · intro y hy hn
    apply hsmodel y hy
    intro hz
    exact hn (by simp only [hz, map_zero])

end ContinuedReferenceODE

section ContinuedPhase

/-- The actual periodic-clock phase is continued by the same stable
parameter substitution, keeping every clock and native-copy datum fixed. -/
theorem continued_periodic_phase_smooth {coord : ℝ} (hc : 0 < coord) (hc1 : coord < 1)
    (g : CommonCoverSolve.Geometry) (w : PeriodicPhaseAssembly.ClockWindow)
    {A B : MeanRankUpdate.ModelPoint → ℝ}
    (hA : ContDiffOn ℝ ∞ A PhysicalCoordinateBounds.positiveTime)
    (hB : ContDiffOn ℝ ∞ B PhysicalCoordinateBounds.positiveTime) :
    ContDiffOn ℝ ∞ (continuedSource coord (PeriodicPhaseAssembly.phase g w.cutoff A B))
      (PhysicalMeanDomain.slowDomain (PositiveRepresentatives.stableTarget coord)) := by
  apply continuedSource_smooth hc hc1
  exact (PeriodicPhaseAssembly.phase_contDiffOn g w hA hB).mono (fun y hy => ⟨hy, mem_univ _⟩)

end ContinuedPhase

section FullReferenceCarrier

variable {V E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Reference carrier model, given by `(HarmonicCalculus.mode frequency
(PeriodicPhaseAssembly.phase g w.cutoff A B) (fun z => L (d.commonSolve g hst κ z)) y).re`. -/
noncomputable def referenceCarrierModel
    (d : CommonCoverSolve.LinearData MeanRankUpdate.ModelPoint V E)
    (g : CommonCoverSolve.Geometry) {s t : ℝ} (hst : s ≤ t) (κ : Slow → ℝ)
    (w : PeriodicPhaseAssembly.ClockWindow) (A B : MeanRankUpdate.ModelPoint → ℝ)
    (frequency : ℝ) (L : E →L[ℝ] ℂ) (y : Model) : ℝ :=
  (HarmonicCalculus.mode frequency (PeriodicPhaseAssembly.phase g w.cutoff A B)
    (fun z => L (d.commonSolve g hst κ z)) y).re

/-- The complete carrier keeps the genuine periodic clock and multiplies
the actual reference solve.  The phase is not replaced by an unwrapped
single-copy expression. -/
theorem referenceCarrier_physical_formula (coord : ℝ)
    (d : CommonCoverSolve.LinearData MeanRankUpdate.ModelPoint V E)
    (g : CommonCoverSolve.Geometry) {s t : ℝ} (hst : s ≤ t) (κ : Slow → ℝ)
    (w : PeriodicPhaseAssembly.ClockWindow) (A B : MeanRankUpdate.ModelPoint → ℝ)
    (frequency : ℝ) (L : E →L[ℝ] ℂ) (p : Lift) :
    physicalSource coord (referenceCarrierModel d g hst κ w A B frequency L) p =
      (L (physicalReferenceSolve coord d g hst κ p) *
        HarmonicCalculus.carrier frequency
          (physicalSource coord (PeriodicPhaseAssembly.phase g w.cutoff A B)) p).re := rfl

/-- Reference carrier continuation as an element of `SupportedContinuation W (physicalSource
coord (referenceCarrierModel d g hst κ w A B frequency L))`. -/
noncomputable def referenceCarrierContinuation {coord a b : ℝ} {W : Window coord a b}
    (hc : 0 < coord) (hc1 : coord < 1)
    (d : CommonCoverSolve.LinearData MeanRankUpdate.ModelPoint V E)
    (g : CommonCoverSolve.Geometry) {s t : ℝ} (hst : s ≤ t)
    (hM : ContDiffOn ℝ ∞ d.coefficient (PhysicalCoordinateBounds.positiveTime ×ˢ univ))
    (hL : ContDiffOn ℝ ∞ d.forcingMap (PhysicalCoordinateBounds.positiveTime ×ˢ univ))
    (hf : ContDiffOn ℝ ∞ d.source (PhysicalCoordinateBounds.positiveTime ×ˢ univ))
    (hs : ModelSupported a b d.source)
    {κ : Slow → ℝ} (hκ : ContDiff ℝ ∞ κ) (hcκ : HasCompactSupport κ)
    (hsκ : tsupport κ ⊆ univ ×ˢ Ioo s t)
    (w : PeriodicPhaseAssembly.ClockWindow) (A B : MeanRankUpdate.ModelPoint → ℝ)
    (hA : ContDiffOn ℝ ∞ A PhysicalCoordinateBounds.positiveTime)
    (hB : ContDiffOn ℝ ∞ B PhysicalCoordinateBounds.positiveTime)
    (frequency : ℝ) (L : E →L[ℝ] ℂ) :
    SupportedContinuation W
      (physicalSource coord (referenceCarrierModel d g hst κ w A B frequency L)) := by
  have hsol := d.commonSolve_contDiffOn g hst PhysicalCoordinateBounds.positiveTime_isOpen
    hM hL hf hκ hcκ hsκ
  have hphase := PeriodicPhaseAssembly.phase_contDiffOn g w hA hB
  have hmode := HarmonicCalculus.contDiffOn_mode frequency hphase (L.contDiff.comp_contDiffOn hsol)
  have hsmodel := referenceSolve_model_supported d g hst κ hs
  refine SupportedContinuation.ofModel hc hc1
    (referenceCarrierModel d g hst κ w A B frequency L) ?_ ?_
  · exact (Complex.reCLM.contDiff.comp_contDiffOn hmode).mono (fun y hy => ⟨hy, mem_univ _⟩)
  · intro y hy hn
    apply hsmodel y hy
    intro hz
    exact hn (by simp only [referenceCarrierModel, HarmonicCalculus.mode, hz, map_zero,
      zero_mul, Complex.zero_re])

end FullReferenceCarrier

section RankModels

theorem rankAngular_model_supported (coord A B lam a b : ℝ) (hab : a < b)
    (d : MeanRankUpdate.Debt) :
    ModelSupported a b (fun y => MeanRankUpdate.angularModel coord A B lam a b d y.1) := by
  intro y hy hn
  have hr := MeanRankUpdate.angularIncrement_tsupport lam (MeanRankUpdate.modelAmplitude coord B
      y.1)
    a b (MeanRankUpdate.modelVelocity A y.1) (Real.sqrt_pos.mpr hy) hab d (subset_tsupport _ hn)
  exact ⟨hr.1.le, hr.2.le⟩

theorem rankAxial_model_supported (coord A B lam a b : ℝ) (hab : a < b)
    (d : MeanRankUpdate.Debt) :
    ModelSupported a b (fun y => MeanRankUpdate.axialModel coord A B lam a b d y.1) := by
  intro y hy hn
  have hr := MeanRankUpdate.desiredAxialIncrement_tsupport lam (MeanRankUpdate.modelAmplitude coord
      B y.1)
    a b (MeanRankUpdate.modelVelocity A y.1) (Real.sqrt_pos.mpr hy) hab d (subset_tsupport _ hn)
  exact ⟨hr.1.le, hr.2.le⟩

/-- The explicit five-row angular kernel supplies its own primitive
continuation; its smoothness is not an additional source assumption. -/
noncomputable def rankAngularContinuation {coord a b : ℝ} {W : Window coord a b}
    (hc : 0 < coord) (hc1 : coord < 1) (A B lam : ℝ) (hB : B ≠ 0) (hab : a < b)
    (d : MeanRankUpdate.Debt) :
    SupportedContinuation W (MeanRankUpdate.chartKernel coord (MeanRankUpdate.angularModel coord A
        B lam a b d)) := by
  apply SupportedContinuation.ofModel hc hc1 (fun y => MeanRankUpdate.angularModel coord A B lam a
      b d y.1)
  · exact (MeanRankUpdate.angularModel_contDiffOn coord A B lam a b hB d).comp
      contDiffOn_fst (fun _ hy => hy)
  · exact rankAngular_model_supported coord A B lam a b hab d

/-- Rank axial continuation as an element of `SupportedContinuation W
(MeanRankUpdate.chartKernel coord (MeanRankUpdate.axialModel coord A B lam a b d))`. -/
noncomputable def rankAxialContinuation {coord a b : ℝ} {W : Window coord a b}
    (hc : 0 < coord) (hc1 : coord < 1) (A B lam : ℝ) (hB : B ≠ 0) (hab : a < b)
    (d : MeanRankUpdate.Debt) :
    SupportedContinuation W (MeanRankUpdate.chartKernel coord (MeanRankUpdate.axialModel coord A B
        lam a b d)) := by
  apply SupportedContinuation.ofModel hc hc1 (fun y => MeanRankUpdate.axialModel coord A B lam a b
      d y.1)
  · exact (MeanRankUpdate.axialModel_contDiffOn coord A B lam a b hB d).comp
      contDiffOn_fst (fun _ hy => hy)
  · exact rankAxial_model_supported coord A B lam a b hab d

end RankModels

section PhysicalFields

/-- Space: an abbreviation for `ProblemStatement.Space`. -/
abbrev Space := ProblemStatement.Space
/-- Space time: an abbreviation for `ProblemStatement.SpaceTime`. -/
abbrev SpaceTime := ProblemStatement.SpaceTime

/-- Physical slow, given by `(1 - w.1, w.2 2)`. -/
noncomputable def physicalSlow (w : SpaceTime) : Slow := (1 - w.1, w.2 2)

theorem physicalSlow_contDiff : ContDiff ℝ ∞ physicalSlow :=
  (contDiff_const.sub contDiff_fst).prodMk
    ((AxisymmetricFields.projection 2).contDiff.comp contDiff_snd)

/-- The actual radial/slow/native-graph restriction of a full-fiber mean
field.  The common covering level remains the supplied `n`. -/
noncomputable def physicalLift (h : ℝ) (n : ℕ) (w : SpaceTime) : Lift :=
  (AnnularEndpoint.radius w, (physicalSlow w, PhysicalGraphBounds.nativeGraph h n w))

/-- Physical domain, given by `physicalSlow ⁻¹' U`. -/
noncomputable def physicalDomain (U : Set Slow) : Set SpaceTime := physicalSlow ⁻¹' U

theorem physicalDomain_open {U : Set Slow} (hU : IsOpen U) : IsOpen (physicalDomain U) :=
  hU.preimage physicalSlow_contDiff.continuous

theorem radius_pos_of_projection {w : SpaceTime}
    (hw : PhysicalGraphBounds.radialProjection w ≠ 0) : 0 < AnnularEndpoint.radius w :=
  (norm_pos_iff.mpr hw).trans_le (PolarCharts.norm_le_radius _)

theorem radius_contDiffAt {w : SpaceTime} (hw : PhysicalGraphBounds.radialProjection w ≠ 0) :
    ContDiffAt ℝ ∞ AnnularEndpoint.radius w := by
  have hs : w.2 0 ^ 2 + w.2 1 ^ 2 ≠ 0 := by
    intro hz
    apply hw
    apply Prod.ext
    · change w.2 0 = 0
      nlinarith [sq_nonneg (w.2 1), sq_nonneg (w.2 0)]
    · change w.2 1 = 0
      nlinarith [sq_nonneg (w.2 1), sq_nonneg (w.2 0)]
  change ContDiffAt ℝ ∞ (fun z : SpaceTime => Real.sqrt (z.2 0 ^ 2 + z.2 1 ^ 2)) w
  exact ((((AxisymmetricFields.projection 0).contDiff.comp contDiff_snd).contDiffAt.pow 2).add
    (((AxisymmetricFields.projection 1).contDiff.comp contDiff_snd).contDiffAt.pow 2)).sqrt hs

theorem physicalLift_contDiffAt (h : ℝ) (n : ℕ) {w : SpaceTime}
    (hw : PhysicalGraphBounds.radialProjection w ≠ 0) : ContDiffAt ℝ ∞ (physicalLift h n) w :=
  (radius_contDiffAt hw).prodMk (physicalSlow_contDiff.contDiffAt.prodMk
    (PhysicalGraphBounds.contDiffAt_nativeGraph h n hw))

/-- Physical scalar, given by `f ∘ physicalLift h n`. -/
noncomputable def physicalScalar (h : ℝ) (n : ℕ) (f : Lift → ℝ) : SpaceTime → ℝ :=
  f ∘ physicalLift h n

theorem physicalScalar_zero_germ (h : ℝ) (n : ℕ) {U : Set Slow} (hU : IsOpen U)
    {c e : ℝ} {f : Lift → ℝ} (hs : PhysicalMeanDomain.SupportedOn c e U f)
    {w : SpaceTime} (hw : w ∈ physicalDomain U) (hr : AnnularEndpoint.radius w < c) :
    physicalScalar h n f =ᶠ[𝓝 w] fun _ => 0 := by
  filter_upwards [(physicalDomain_open hU).mem_nhds hw,
    AnnularEndpoint.radius_continuous.continuousAt (gt_mem_nhds hr)] with z hz hzr
  by_contra hn
  exact (not_lt_of_ge (hs (physicalLift h n z) hz hn).1) hzr

/-- A positive lower radial support bound removes the coordinate singularity
on the symmetry axis.  No smoothness of the graph at the axis is assumed. -/
theorem physicalScalar_smooth (h : ℝ) (n : ℕ) {U : Set Slow} (hU : IsOpen U)
    {c e : ℝ} (hc : 0 < c) {f : Lift → ℝ}
    (hf : ContDiffOn ℝ ∞ f (PhysicalMeanDomain.slowDomain U))
    (hs : PhysicalMeanDomain.SupportedOn c e U f) :
    ContDiffOn ℝ ∞ (physicalScalar h n f) (physicalDomain U) := by
  intro w hw
  by_cases ha : PhysicalGraphBounds.radialProjection w = 0
  · have hr : AnnularEndpoint.radius w = 0 := by
      simp only [AnnularEndpoint.radius, ha, PolarCharts.radius, Prod.fst_zero, Prod.snd_zero,
        zero_pow (by decide : 2 ≠ 0), zero_add, Real.sqrt_zero]
    exact (contDiffAt_const.congr_of_eventuallyEq
      (physicalScalar_zero_germ h n hU hs hw (hr ▸ hc))).contDiffWithinAt
  · exact ((hf.contDiffAt ((PhysicalMeanDomain.slowDomain_open hU).mem_nhds hw)).comp w
      (physicalLift_contDiffAt h n ha)).contDiffWithinAt

/-- `streamPotential` is already the azimuthal component of the vector
potential, including its division by the radial variable. -/
noncomputable def azimuthalPotential (h : ℝ) (n : ℕ) (f : Lift → ℝ) (w : SpaceTime) : Space :=
  (-w.2 1 / AnnularEndpoint.radius w * physicalScalar h n f w) • ProblemStatement.coordinateVector
      0 +
    (w.2 0 / AnnularEndpoint.radius w * physicalScalar h n f w) • ProblemStatement.coordinateVector
        1

/-- A direct angular velocity uses the same Cartesian multiplication by
`e_theta`.  This definition does not apply a curl or a radial primitive. -/
noncomputable def angularField (h : ℝ) (n : ℕ) (f : Lift → ℝ) : SpaceTime → Space :=
  azimuthalPotential h n f

theorem azimuthalPotential_smooth (h : ℝ) (n : ℕ) {U : Set Slow} (hU : IsOpen U)
    {c e : ℝ} (hc : 0 < c) {f : Lift → ℝ}
    (hf : ContDiffOn ℝ ∞ f (PhysicalMeanDomain.slowDomain U))
    (hs : PhysicalMeanDomain.SupportedOn c e U f) :
    ContDiffOn ℝ ∞ (azimuthalPotential h n f) (physicalDomain U) := by
  intro w hw
  by_cases ha : PhysicalGraphBounds.radialProjection w = 0
  · have hr : AnnularEndpoint.radius w = 0 := by
      simp [AnnularEndpoint.radius, ha, PolarCharts.radius]
    have he : azimuthalPotential h n f =ᶠ[𝓝 w] fun _ => 0 := by
      filter_upwards [physicalScalar_zero_germ h n hU hs hw (hr ▸ hc)] with z hz
      simp only [azimuthalPotential, hz, mul_zero, zero_smul, add_zero]
    exact (contDiffAt_const.congr_of_eventuallyEq he).contDiffWithinAt
  · have hR := radius_contDiffAt ha
    have hRn := (radius_pos_of_projection ha).ne'
    have hψ := (physicalScalar_smooth h n hU hc hf hs).contDiffAt
      ((physicalDomain_open hU).mem_nhds hw)
    have h0 : ContDiffAt ℝ ∞ (fun z : SpaceTime => z.2 0) w :=
      ((AxisymmetricFields.projection 0).contDiff.comp contDiff_snd).contDiffAt
    have h1 : ContDiffAt ℝ ∞ (fun z : SpaceTime => z.2 1) w :=
      ((AxisymmetricFields.projection 1).contDiff.comp contDiff_snd).contDiffAt
    exact ((((h1.neg.div hR hRn).mul hψ).smul contDiffAt_const).add
      (((h0.div hR hRn).mul hψ).smul contDiffAt_const)).contDiffWithinAt

namespace SupportedContinuation

variable {coord a b : ℝ} {W : Window coord a b} {f : Lift → ℝ}

/-- Physical extension, bundling `value`, `domain`, `isOpen`, `mem` and the required
compatibility proofs. -/
noncomputable def physicalExtension (e : SupportedContinuation W f) (h : ℝ) (n : ℕ)
    {x : Space} (hx : (0, x 2) ∈ W.carrier) :
    JointResidualLimits.OneSidedExtension (physicalScalar h n f) x where
  value := physicalScalar h n e.value
  domain := physicalDomain W.carrier
  isOpen := physicalDomain_open W.isOpen
  mem := by simpa only [physicalDomain, mem_preimage, physicalSlow, sub_self] using hx
  smooth := physicalScalar_smooth h n W.isOpen W.lower_pos e.smooth (W.fixed_support e.supported)
  agrees := by
    intro w hw
    exact e.agrees ⟨hw.1, show 0 < 1 - w.1 from sub_pos.mpr hw.2.1⟩

/-- Azimuthal extension, bundling `value`, `domain`, `isOpen`, `mem` and the required
compatibility proofs. -/
noncomputable def azimuthalExtension (e : SupportedContinuation W f) (h : ℝ) (n : ℕ)
    {x : Space} (hx : (0, x 2) ∈ W.carrier) :
    JointResidualLimits.OneSidedExtension (azimuthalPotential h n f) x where
  value := azimuthalPotential h n e.value
  domain := physicalDomain W.carrier
  isOpen := physicalDomain_open W.isOpen
  mem := by simpa only [physicalDomain, mem_preimage, physicalSlow, sub_self] using hx
  smooth := azimuthalPotential_smooth h n W.isOpen W.lower_pos e.smooth (W.fixed_support
      e.supported)
  agrees := by
    intro w hw
    have he := (e.physicalExtension h n hx).agrees hw
    change physicalScalar h n e.value w = physicalScalar h n f w at he
    dsimp only [azimuthalPotential]
    rw [he]

/-- Angular extension, given by `e.azimuthalExtension h n hx`. -/
noncomputable def angularExtension (e : SupportedContinuation W f) (h : ℝ) (n : ℕ)
    {x : Space} (hx : (0, x 2) ∈ W.carrier) :
    JointResidualLimits.OneSidedExtension (angularField h n f) x :=
  e.azimuthalExtension h n hx

end SupportedContinuation

/-- The scalar pressure and the actual azimuthal mean potential (and hence
its Cartesian curl) have ambient endpoint extensions from primitive model
smoothness and support.  No extension of a solved field is an input. -/
theorem mean_model_extensions {h a b d : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (ha : 0 < a) (hab : a < b) (hd : 0 < d) (M : ℝ) (v : Slow) (n : ℕ)
    (F : Model → ℝ) (hF : ContDiffOn ℝ ∞ F modelDomain) (hs : ModelSupported a b F)
    {x : Space} (hx : x 2 ≠ 0) :
    Nonempty (JointResidualLimits.OneSidedExtension
      (physicalScalar h n (VariableGaugeMean.meanPressure d a b M hab
        (VariableGaugeMean.qLength (2 * h)) v (physicalSource (2 * h) F))) x) ∧
    Nonempty (JointResidualLimits.OneSidedExtension
      (azimuthalPotential h n (VariableGaugeMean.streamPotential d a b M
        (VariableGaugeMean.qLength (2 * h)) v (physicalSource (2 * h) F))) x) ∧
    Nonempty (JointResidualLimits.OneSidedExtension
      (SpatialCurl.spatialCurl (azimuthalPotential h n (VariableGaugeMean.streamPotential d a b M
        (VariableGaugeMean.qLength (2 * h)) v (physicalSource (2 * h) F)))) x) := by
  have hc : 0 < 2 * h := by linarith
  have hc1 : 2 * h < 1 := by linarith
  obtain ⟨W, hw⟩ := exists_endpoint_window hc hc1 ha hab hx
  let e : SupportedContinuation W (physicalSource (2 * h) F) :=
    SupportedContinuation.ofModel hc hc1 F hF hs
  let ep := (e.pressure hc hc1 ha hab hd M v).physicalExtension h n hw
  let eA := (e.stream hc hc1 ha hab hd M v).azimuthalExtension h n hw
  exact ⟨⟨ep⟩, ⟨eA⟩, ⟨AnnularEndpoint.curlExtension eA⟩⟩

/-- The actual temporal inverse is taken before reconstructing its mean
stream potential.  Its full-fiber continuation comes from the input torus
periodicity and the proved inverse construction. -/
theorem temporal_mean_model_extension {h a b d : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (ha : 0 < a) (hab : a < b) (hd : 0 < d) (M : ℝ) (v : Slow) (n i : ℕ)
    (F : Model → ℝ) (hF : ContDiffOn ℝ ∞ F modelDomain) (hs : ModelSupported a b F)
    (hp : ModelPeriodic F) {x : Space} (hx : x 2 ≠ 0) :
    Nonempty (JointResidualLimits.OneSidedExtension
      (azimuthalPotential h n (VariableGaugeMean.streamPotential d a b M
        (VariableGaugeMean.qLength (2 * h)) v
        (MeanChartCompatibility.temporalAtIndex h n i (physicalSource (2 * h) F)))) x) := by
  have hc : 0 < 2 * h := by linarith
  have hc1 : 2 * h < 1 := by linarith
  obtain ⟨W, hw⟩ := exists_endpoint_window hc hc1 ha hab hx
  let e : SupportedContinuation W (physicalSource (2 * h) F) :=
    SupportedContinuation.ofModel hc hc1 F hF hs
  have heper : PhysicalMeanDomain.PeriodicOn W.carrier e.value := continuedSource_periodic hp
      W.stable
  exact ⟨((e.temporal h n i heper).stream hc hc1 ha hab hd M v).azimuthalExtension h n hw⟩

theorem mean_models_supported {coord a b d : ℝ} (hc : 0 < coord) (hc1 : coord < 1)
    (ha : 0 < a) (hab : a < b) (hd : 0 < d) (M : ℝ) (v : Slow)
    (F : Model → ℝ) (hF : ContDiffOn ℝ ∞ F modelDomain) (hs : ModelSupported a b F) :
    VariableGaugeMean.SupportedGauge a b (VariableGaugeMean.qLength coord) positiveSlow
      (VariableGaugeMean.meanPressure d a b M hab (VariableGaugeMean.qLength coord) v
          (physicalSource coord F)) ∧
    VariableGaugeMean.SupportedGauge a b (VariableGaugeMean.qLength coord) positiveSlow
      (VariableGaugeMean.streamPotential d a b M (VariableGaugeMean.qLength coord) v
          (physicalSource coord F)) := by
  constructor
  · intro p hp hn
    obtain ⟨W, hw⟩ := exists_window_at hc hc1 ha hab
      (PositiveRepresentatives.positiveTime_mem_stableTarget hc hc1 hp)
    let e : SupportedContinuation W (physicalSource coord F) := SupportedContinuation.ofModel hc
        hc1 F hF hs
    exact (e.pressure hc hc1 ha hab hd M v).support_on_past hc hc1 hw hp hn
  · intro p hp hn
    obtain ⟨W, hw⟩ := exists_window_at hc hc1 ha hab
      (PositiveRepresentatives.positiveTime_mem_stableTarget hc hc1 hp)
    let e : SupportedContinuation W (physicalSource coord F) := SupportedContinuation.ofModel hc
        hc1 F hF hs
    exact (e.stream hc hc1 ha hab hd M v).support_on_past hc hc1 hw hp hn

theorem physicalScalar_shrinkingSupport (h : ℝ) (n : ℕ) {a b : ℝ} {f : Lift → ℝ}
    (hf : VariableGaugeMean.SupportedGauge a b (VariableGaugeMean.qLength (2 * h)) positiveSlow f) :
    AnnularEndpoint.ShrinkingSupport h b (physicalScalar h n f) := by
  intro w ht hn
  have hs := (hf (physicalLift h n w) (show 0 < 1 - w.1 from sub_pos.mpr ht) hn).2
  change AnnularEndpoint.radius w ≤
    Real.sqrt (SimilarityCoordinates.coordinateQ (2 * h) (1 - w.1, w.2 2)) * b at hs
  change AnnularEndpoint.radius w ≤
    b * Real.sqrt (SimilarityCoordinates.coordinateQ (2 * h) (1 - w.1, w.2 2))
  simpa only [mul_comm] using hs

theorem azimuthalPotential_shrinkingSupport (h : ℝ) (n : ℕ) {a b : ℝ} {f : Lift → ℝ}
    (hf : VariableGaugeMean.SupportedGauge a b (VariableGaugeMean.qLength (2 * h)) positiveSlow f) :
    AnnularEndpoint.ShrinkingSupport h b (azimuthalPotential h n f) := by
  intro w ht hn
  apply physicalScalar_shrinkingSupport h n hf w ht
  intro hz
  exact hn (by simp only [azimuthalPotential, hz, mul_zero, zero_smul, add_zero])

end PhysicalFields

section DiagonalCutoffs

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Physical Q extension, given by `(EndpointCoordinates.cartesianExtension h w).1`. -/
noncomputable def physicalQExtension (h : ℝ) (w : SpaceTime) : ℝ :=
  (EndpointCoordinates.cartesianExtension h w).1

theorem physicalQExtension_eq {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {w : SpaceTime} (ht : w.1 < 1) : physicalQExtension h w = PhysicalWaveSum.physicalQ h w :=
  congrArg Prod.fst (EndpointCoordinates.cartesianExtension_eq_physical hh hh1 ht)

/-- Only finitely many stages survive near a positive-q endpoint.  Their
extensions are combined with the same scalar cutoffs and the same schedule.
The preceding model/mean constructors supply the finite-stage extensions. -/
theorem diagonal_extension {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {a : ℕ → ℝ} (ha : Tendsto a atTop atTop) {F : ℕ → SpaceTime → V}
    {x : Space} (hx : x 2 ≠ 0)
    (he : ∀ j, Nonempty (JointResidualLimits.OneSidedExtension (F j) x)) :
    Nonempty (JointResidualLimits.OneSidedExtension
      (SolenoidalDiagonal.potentialSum a (PhysicalWaveSum.physicalQ h) F) x) := by
  classical
  obtain ⟨U, hU, hxU, hUD, _, _, hqU⟩ := EndpointCoordinates.cartesian_endpoint_neighborhood hh hh1
      hx
  obtain ⟨N, hN⟩ := SmoothCutoffs.scaledCutoffs_zero_on_common_neighborhood a ha
    (EndpointCoordinates.endpointRoot_pos (2 * h) hx)
  let e : ∀ j, JointResidualLimits.OneSidedExtension (F j) x := fun j => Classical.choice (he j)
  let D : Set SpaceTime := U ∩ ⋂ j ∈ Finset.range N, (e j).domain
  have hD : IsOpen D := hU.inter (isOpen_biInter_finset fun j _ => (e j).isOpen)
  have hxD : (1, x) ∈ D := ⟨hxU, mem_iInter.mpr fun j => mem_iInter.mpr fun _ => (e j).mem⟩
  have hsub (j : ℕ) (hj : j ∈ Finset.range N) : D ⊆ (e j).domain :=
    fun w hw => mem_iInter.mp (mem_iInter.mp hw.2 j) hj
  have hq : ContDiffOn ℝ ∞ (physicalQExtension h) D :=
    (EndpointCoordinates.cartesianExtension_smoothOn hh hh1).fst.mono (fun _ hw => hUD hw.1)
  refine ⟨{
    value := fun w => ∑ j ∈ Finset.range N,
      SmoothCutoffs.scaledCutoff (a j) (physicalQExtension h w) • (e j).value w
    domain := D
    isOpen := hD
    mem := hxD
    smooth := ?_
    agrees := ?_ }⟩
  · apply ContDiffOn.sum
    intro j hj
    exact ((SmoothCutoffs.scaledCutoff_contDiff (a j)).comp_contDiffOn hq).smul
      ((e j).smooth.mono (hsub j hj))
  · intro w hw
    have hqt := physicalQExtension_eq hh hh1 hw.2.1
    have hlow : EndpointCoordinates.endpointRoot (2 * h) (x 2) / 2 < PhysicalWaveSum.physicalQ h w
        := by
      rw [← hqt]
      exact (hqU w hw.1.1).1
    have hsum : SolenoidalDiagonal.potentialSum a (PhysicalWaveSum.physicalQ h) F w =
        ∑ j ∈ Finset.range N, SolenoidalDiagonal.cutStage a (PhysicalWaveSum.physicalQ h) F j w :=
            by
      apply tsum_eq_sum
      intro j hj
      simp only [SolenoidalDiagonal.cutStage, hN j
        (Nat.le_of_not_gt (by simpa only [Finset.mem_range] using hj)) _ hlow, zero_smul]
    rw [hsum]
    apply Finset.sum_congr rfl
    intro j hj
    change SmoothCutoffs.scaledCutoff (a j) (physicalQExtension h w) • (e j).value w =
      SmoothCutoffs.scaledCutoff (a j) (PhysicalWaveSum.physicalQ h w) • F j w
    rw [hqt, (e j).agrees ⟨hsub j hj hw.1, hw.2⟩]

end DiagonalCutoffs

/-- All stages of actual moving mean reconstruction can be summed with the
chosen cutoff schedule at a nonzero-axial endpoint.  The model assumptions
are on the primitive source of each stage. -/
theorem mean_diagonal_extensions {h a b d : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (ha : 0 < a) (hab : a < b) (hd : 0 < d)
    (M : ℕ → ℝ) (v : ℕ → Slow) (n : ℕ → ℕ)
    (F : ℕ → Model → ℝ) (hF : ∀ j, ContDiffOn ℝ ∞ (F j) modelDomain)
    (hs : ∀ j, ModelSupported a b (F j)) {scale : ℕ → ℝ} (hscale : Tendsto scale atTop atTop)
    {x : Space} (hx : x 2 ≠ 0) :
    let p := fun j => physicalScalar h (n j) (VariableGaugeMean.meanPressure d a b (M j) hab
      (VariableGaugeMean.qLength (2 * h)) (v j) (physicalSource (2 * h) (F j)))
    let A := fun j => azimuthalPotential h (n j) (VariableGaugeMean.streamPotential d a b (M j)
      (VariableGaugeMean.qLength (2 * h)) (v j) (physicalSource (2 * h) (F j)))
    Nonempty (JointResidualLimits.OneSidedExtension
      (SolenoidalDiagonal.potentialSum scale (PhysicalWaveSum.physicalQ h) p) x) ∧
    Nonempty (JointResidualLimits.OneSidedExtension
      (SolenoidalDiagonal.potentialSum scale (PhysicalWaveSum.physicalQ h) A) x) ∧
    Nonempty (JointResidualLimits.OneSidedExtension
      (SolenoidalDiagonal.velocitySum scale (PhysicalWaveSum.physicalQ h) A) x) := by
  have he := fun j => mean_model_extensions hh hh1 ha hab hd (M j) (v j) (n j) (F j) (hF j) (hs j)
      hx
  obtain ⟨eA⟩ := diagonal_extension hh hh1 hscale hx (fun j => (he j).2.1)
  exact ⟨diagonal_extension hh hh1 hscale hx (fun j => (he j).1), ⟨eA⟩,
    ⟨AnnularEndpoint.curlExtension eA⟩⟩

/-- Combining the new positive-q continuation with the shrinking-support
argument gives full away-extensions for these actually reconstructed mean
families.  The common outer support bound is a conclusion of the primitive
model support, rather than an additional output assumption. -/
theorem mean_diagonal_awayExtensions {h a b d : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (ha : 0 < a) (hab : a < b) (hd : 0 < d)
    (M : ℕ → ℝ) (v : ℕ → Slow) (n : ℕ → ℕ)
    (F : ℕ → Model → ℝ) (hF : ∀ j, ContDiffOn ℝ ∞ (F j) modelDomain)
    (hs : ∀ j, ModelSupported a b (F j)) {scale : ℕ → ℝ} (hscale : Tendsto scale atTop atTop) :
    let p := fun j => physicalScalar h (n j) (VariableGaugeMean.meanPressure d a b (M j) hab
      (VariableGaugeMean.qLength (2 * h)) (v j) (physicalSource (2 * h) (F j)))
    let A := fun j => azimuthalPotential h (n j) (VariableGaugeMean.streamPotential d a b (M j)
      (VariableGaugeMean.qLength (2 * h)) (v j) (physicalSource (2 * h) (F j)))
    JointResidualLimits.AwayExtensions (SolenoidalDiagonal.potentialSum scale
        (PhysicalWaveSum.physicalQ h) p) ∧
    JointResidualLimits.AwayExtensions (SolenoidalDiagonal.potentialSum scale
        (PhysicalWaveSum.physicalQ h) A) ∧
    JointResidualLimits.AwayExtensions (SolenoidalDiagonal.velocitySum scale
        (PhysicalWaveSum.physicalQ h) A) := by
  have hsup j := mean_models_supported (by linarith : 0 < 2 * h) (by linarith : 2 * h < 1)
    ha hab hd (M j) (v j) (F j) (hF j) (hs j)
  have hps := AnnularEndpoint.ShrinkingSupport.potentialSum
    (fun j => physicalScalar_shrinkingSupport h (n j) (hsup j).1) scale (PhysicalWaveSum.physicalQ
        h)
  have hAs := AnnularEndpoint.ShrinkingSupport.potentialSum
    (fun j => azimuthalPotential_shrinkingSupport h (n j) (hsup j).2) scale
        (PhysicalWaveSum.physicalQ h)
  have hvs := hAs.spatialCurl hh hh1
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    by_cases hz : x 2 = 0
    · exact hps.oneSidedExtension hh hh1 hx hz
    · exact (mean_diagonal_extensions hh hh1 ha hab hd M v n F hF hs hscale hz).1
  · intro x hx
    by_cases hz : x 2 = 0
    · exact hAs.oneSidedExtension hh hh1 hx hz
    · exact (mean_diagonal_extensions hh hh1 ha hab hd M v n F hF hs hscale hz).2.1
  · intro x hx
    by_cases hz : x 2 = 0
    · exact hvs.oneSidedExtension hh hh1 hx hz
    · exact (mean_diagonal_extensions hh hh1 ha hab hd M v n F hF hs hscale hz).2.2

end NavierStokes.OffplaneCorrectionExtensions
