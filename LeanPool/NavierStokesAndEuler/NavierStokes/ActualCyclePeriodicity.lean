/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualWaveCoefficientPeriodicity
import LeanPool.NavierStokesAndEuler.NavierStokes.ActualSeedPeriodicity

/-!
# Auxiliary periodicity of the actual correction coefficients

The total velocity does not determine the periods of each stored harmonic
coefficient.  This module tracks the individual velocity, pressure and
Gaussian coefficients on precisely the bands whose common cover is ordered.
The differential residual preserves these periods on its open slow domain.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.ActualCyclePeriodicity

open Set Function Filter CorrectionState CorrectionStep CorrectionInitialization
open HarmonicFields HarmonicResidual
open ActualWaveRegularity
open scoped Topology ContDiff BigOperators ComplexConjugate


/-- Point: an abbreviation for `ActualInitialization.Point`. -/
abbrev Point := ActualInitialization.Point
/-- Index: an abbreviation for `ActualInitialization.Index /-! Translation calculus for finite
harmonic coefficients. -/`. -/
abbrev Index := ActualInitialization.Index

/-! Translation calculus for finite harmonic coefficients. -/

section TranslationCalculus

variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]

/-- Coefficients translation, given by `∀ j, TranslationOn U v (a j)`. -/
def CoefficientsTranslation (U : Set D) (v : D) (a : HarmonicFields.Coefficients D) : Prop :=
  ∀ j, TranslationOn U v (a j)

namespace CoefficientsTranslation

variable {U : Set D} {v : D} {a b : HarmonicFields.Coefficients D}

omit [NormedSpace ℝ D] in
theorem zero : CoefficientsTranslation U v (0 : HarmonicFields.Coefficients D) :=
  fun _ => TranslationOn.const 0

omit [NormedSpace ℝ D] in
theorem add (ha : CoefficientsTranslation U v a) (hb : CoefficientsTranslation U v b) :
    CoefficientsTranslation U v (a + b) :=
  fun j => (ha j).map₂ (hb j) (· + ·)

omit [NormedSpace ℝ D] in
theorem neg (ha : CoefficientsTranslation U v a) :
    CoefficientsTranslation U v (-a) := fun j => (ha j).map Neg.neg

omit [NormedSpace ℝ D] in
theorem sub (ha : CoefficientsTranslation U v a) (hb : CoefficientsTranslation U v b) :
    CoefficientsTranslation U v (a - b) :=
  fun j => (ha j).map₂ (hb j) (· - ·)

omit [NormedSpace ℝ D] in
theorem mul (ha : CoefficientsTranslation U v a) (hb : CoefficientsTranslation U v b) :
    CoefficientsTranslation U v (a * b) := by
  intro j x hx
  simp only [HarmonicFields.convolution_apply]
  apply Finset.sum_congr rfl
  intro m _
  rw [ha m x hx, hb (j - m) x hx]

omit [NormedSpace ℝ D] in
theorem boundConstant {f : D → ℂ} (hf : TranslationOn U v f) :
    CoefficientsTranslation U v (constantCoefficient f) := by
  classical
  intro j x hx
  simp only [constantCoefficient, AddMonoidAlgebra.coeff_single, Finsupp.single_apply, ite_apply]
  split_ifs <;> simp only [hf x hx, Pi.zero_apply]

theorem differentiate (ha : CoefficientsTranslation U v a) (hU : IsOpen U)
    {V : D → D} {Φ : D → ℝ} (hV : TranslationOn U v V)
    (hΦ : TranslationOn U v Φ) (k : ℝ) :
    CoefficientsTranslation U v (HarmonicFields.differentiate V k Φ a) := by
  intro j x hx
  simp only [HarmonicFields.differentiate_apply, derivativeCoefficient,
    (ha j).along hV hU x hx, hΦ.along hV hU x hx, ha j x hx]

omit [NormedSpace ℝ D] in
theorem angular (ha : CoefficientsTranslation U v a) (k : ℤ) :
    CoefficientsTranslation U v (angularDifferentiate k a) := by
  intro j x hx
  simp only [angularDifferentiate_apply, ha j x hx]

omit [NormedSpace ℝ D] in
theorem realProjection (ha : CoefficientsTranslation U v a) :
    CoefficientsTranslation U v (realCoefficients a) := by
  intro j x hx
  simp only [realCoefficients_apply, ha j x hx, ha (-j) x hx]

omit [NormedSpace ℝ D] in
theorem nonconstant (ha : CoefficientsTranslation U v a) :
    CoefficientsTranslation U v (HarmonicResidual.nonconstant a) := by
  rw [nonconstant_eq_sub]
  exact ha.sub (boundConstant (ha 0))

omit [NormedSpace ℝ D] in
theorem sum {ι : Type} (s : Finset ι) (f : ι → HarmonicFields.Coefficients D)
    (hf : ∀ i ∈ s, CoefficientsTranslation U v (f i)) :
    CoefficientsTranslation U v (∑ i ∈ s, f i) := by
  classical
  revert hf
  induction s using Finset.induction_on with
  | empty =>
      intro _
      simpa only [Finset.sum_empty] using
        (zero : CoefficientsTranslation U v (0 : HarmonicFields.Coefficients D))
  | @insert i s hi ih =>
      intro hf
      rw [Finset.sum_insert hi]
      exact (hf i (Finset.mem_insert_self _ _)).add
        (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

omit [NormedSpace ℝ D] in
theorem field (ha : CoefficientsTranslation U v a) {Φ : D → ℝ}
    (hΦ : TranslationOn U v Φ) (k : ℝ) (kp : ℤ) (θ : ℝ) :
    TranslationOn U v (fun x => HarmonicFields.field a k Φ kp (x, θ)) := by
  intro x hx
  simp only [HarmonicFields.field_expansion]
  apply Finset.sum_congr rfl
  intro j _
  rw [ha j x hx, hΦ x hx]

end CoefficientsTranslation

/-- Frame translation data, collecting `radius`, `radial`, `axial`, `time`. -/
structure FrameTranslation (U : Set D) (v : D) (g : Frame D) : Prop where
  radius : TranslationOn U v g.radius
  radial : TranslationOn U v g.radial
  axial : TranslationOn U v g.axial
  time : TranslationOn U v g.time

namespace FrameTranslation

variable {U : Set D} {v : D} {g : Frame D}
  (hg : FrameTranslation U v g) (hU : IsOpen U)
  {Φ : D → ℝ} (hΦ : TranslationOn U v Φ) (k : ℝ) (kp : ℤ)

include hg hU hΦ in
theorem scalarLaplacian {a : HarmonicFields.Coefficients D}
    (ha : CoefficientsTranslation U v a) :
    CoefficientsTranslation U v (HarmonicResidual.scalarLaplacian g k Φ kp a) := by
  have hr := ha.differentiate hU hg.radial hΦ k
  exact ((hr.differentiate hU hg.radial hΦ k).add
    ((CoefficientsTranslation.boundConstant (hg.radius.map (fun R => ((R⁻¹ : ℝ) : ℂ)))).mul hr)).add
    ((CoefficientsTranslation.boundConstant (hg.radius.map (fun R => (((R ^ 2)⁻¹ : ℝ) : ℂ)))).mul
      ((ha.angular kp).angular kp)) |>.add
    ((ha.differentiate hU hg.axial hΦ k).differentiate hU hg.axial hΦ k)

omit [NormedSpace ℝ D] in
theorem rotate {a : VectorCoefficients D}
    (ha : ∀ i, CoefficientsTranslation U v (a i)) :
    ∀ i, CoefficientsTranslation U v (HarmonicResidual.rotate a i) := by
  intro i
  fin_cases i
  · exact (ha 1).neg
  · exact ha 0
  · exact CoefficientsTranslation.zero

include hg hU hΦ in
theorem vectorLaplacian {a : VectorCoefficients D}
    (ha : ∀ i, CoefficientsTranslation U v (a i)) :
    ∀ i, CoefficientsTranslation U v (HarmonicResidual.vectorLaplacian g k Φ kp a i) := by
  intro i
  exact (hg.scalarLaplacian hU hΦ k kp (ha i)).add
    ((CoefficientsTranslation.boundConstant (hg.radius.map (fun R => (((R ^ 2)⁻¹ : ℝ) : ℂ)))).mul
      (((CoefficientsTranslation.boundConstant (TranslationOn.const (2 : ℂ))).mul
        (rotate (fun i => (ha i).angular kp) i)).add (rotate (rotate ha) i)))

include hg hU hΦ in
theorem transport {a b : VectorCoefficients D}
    (ha : ∀ i, CoefficientsTranslation U v (a i))
    (hb : ∀ i, CoefficientsTranslation U v (b i)) :
    ∀ i, CoefficientsTranslation U v (HarmonicResidual.transport g k Φ kp a b i) := by
  intro i
  exact (((ha 0).mul ((hb i).differentiate hU hg.radial hΦ k)).add
    (((ha 1).mul (CoefficientsTranslation.boundConstant (hg.radius.map (fun R => (R : ℂ)⁻¹)))).mul
      (((hb i).angular kp).add (rotate hb i)))).add
    ((ha 2).mul ((hb i).differentiate hU hg.axial hΦ k))

include hg hU hΦ in
theorem gradient {p : HarmonicFields.Coefficients D}
    (hp : CoefficientsTranslation U v p) :
    ∀ i, CoefficientsTranslation U v (HarmonicResidual.gradient g k Φ kp p i) := by
  intro i
  fin_cases i
  · exact hp.differentiate hU hg.radial hΦ k
  · exact (CoefficientsTranslation.boundConstant (hg.radius.map (fun R => ((R⁻¹ : ℝ) : ℂ)))).mul
      (hp.angular kp)
  · exact hp.differentiate hU hg.axial hΦ k

include hg hU hΦ in
theorem linearResidual {B a : VectorCoefficients D} {p : HarmonicFields.Coefficients D}
    (hB : ∀ i, CoefficientsTranslation U v (B i))
    (ha : ∀ i, CoefficientsTranslation U v (a i)) (hp : CoefficientsTranslation U v p) :
    ∀ i, CoefficientsTranslation U v (HarmonicResidual.linearResidual g k Φ kp B a p i) := by
  intro i
  exact ((((ha i).differentiate hU hg.time hΦ k).add (hg.transport hU hΦ k kp hB ha i)).add
    (hg.transport hU hΦ k kp ha hB i) |>.add (hg.gradient hU hΦ k kp hp i)).sub
    ((CoefficientsTranslation.boundConstant (TranslationOn.const (g.viscosity : ℂ))).mul
      (hg.vectorLaplacian hU hΦ k kp ha i))

include hg hU hΦ in
theorem nonlinearResidual {B a : VectorCoefficients D} {p : HarmonicFields.Coefficients D}
    (hB : ∀ i, CoefficientsTranslation U v (B i))
    (ha : ∀ i, CoefficientsTranslation U v (a i)) (hp : CoefficientsTranslation U v p) :
    ∀ i, CoefficientsTranslation U v (HarmonicResidual.nonlinearResidual g k Φ kp B a p i) :=
  fun i => (hg.linearResidual hU hΦ k kp hB ha hp i).add (hg.transport hU hΦ k kp ha ha i)

end FrameTranslation

/-- The actual finite residual, including both excluded-error inputs,
commutes with a translation when its primitive data do. -/
theorem residualSource_translation {U : Set D} {v : D} (hU : IsOpen U)
    (c : Context D) (u : State D) (b : HarmonicBlock D)
    (G A : HarmonicResidual.BlockCoefficients D) (n : ℕ)
    (hg : FrameTranslation U v (contextFrame c n))
    (hB : TranslationOn U v (contextBase c n))
    (hM : TranslationOn U v (stateMean u n))
    (hΦ : TranslationOn U v (b.phase n))
    (hv : ∀ i, CoefficientsTranslation U v (b.velocity n i))
    (hp : CoefficientsTranslation U v (b.pressure n))
    (hG : ∀ i, CoefficientsTranslation U v (G n i))
    (hA : ∀ i, CoefficientsTranslation U v (A n i)) (j : ℤ) :
    TranslationOn U v (ParticularWaveAssembly.residualSource c u b G A j n) := by
  have hBM : ∀ i, CoefficientsTranslation U v (constantVector (contextBase c n + stateMean u n) i)
      :=
    fun i => CoefficientsTranslation.boundConstant ((hB.component i).map₂ (hM.component i) (· + ·))
  have hr := hg.nonlinearResidual hU hΦ (b.frequency n) (b.angularFrequency n)
    hBM (fun i => (hv i).realProjection) hp.realProjection
  intro z hz
  funext i
  exact (((hr i).sub (hG i)).sub (hA i)).realProjection.nonconstant j z hz

end TranslationCalculus

/-! The separately carried periodicity invariant. -/

/-- Point deck, given by `(0, (0, TorusAverages.latticePoint k))`. -/
noncomputable def pointDeck (k : TorusInverse.Frequency) : Point :=
  (0, (0, TorusAverages.latticePoint k))

theorem add_pointDeck (z : Point) (k : TorusInverse.Frequency) :
    z + pointDeck k = (z.1, (z.2.1, z.2.2 + TorusAverages.latticePoint k)) := by
  simp only [pointDeck, Prod.add_def, add_zero]

/-- Periodic data, collecting `velocity`, `pressure`, `gaussian`. -/
structure Periodic {B N0 : ℕ} (x : CycleState (Index B N0)) : Prop where
  velocity : ∀ l n, ActualWaveRegularityData.Ordered l n → ∀ k i,
    CoefficientsTranslation ActualInitialization.geometry.domain (pointDeck k)
      ((x.coefficients.blocks l).velocity n i)
  pressure : ∀ l n, ActualWaveRegularityData.Ordered l n → ∀ k,
    CoefficientsTranslation ActualInitialization.geometry.domain (pointDeck k)
      ((x.coefficients.blocks l).pressure n)
  gaussian : ∀ l n, ActualWaveRegularityData.Ordered l n → ∀ k i,
    CoefficientsTranslation ActualInitialization.geometry.domain (pointDeck k)
      (x.coefficients.gaussian l n i)

/-- The literal initialized state has every auxiliary period required below. -/
theorem initial (B N0 : ℕ) : Periodic (ActualInitialization.initialCycleState B N0) where
  velocity l n hn k i j z _ :=
    ActualSeedPeriodicity.primary_velocity_periodic l n hn i j k z
  pressure l n hn k j z _ :=
    ActualSeedPeriodicity.primary_pressure_periodic l n hn j k z
  gaussian l n hn k i j z _ :=
    ActualSeedPeriodicity.gaussian_velocity_periodic l n hn i j k z

/-- Addition of the two actual wave increments preserves the coefficient
periods. The mean and axisymmetric updates do not alter these coefficients. -/
theorem Periodic.step_of_waves {B N0 : ℕ} {x : CycleState (Index B N0)}
    (h : Periodic x) (p : CycleParameters (Index B N0)) (c : Context Point)
    (hp : ∀ l n, ActualWaveRegularityData.Ordered l n → ∀ k,
      (∀ i, CoefficientsTranslation ActualInitialization.geometry.domain (pointDeck k)
        ((p.particularBlock x.coefficients c x.state l).velocity n i)) ∧
      CoefficientsTranslation ActualInitialization.geometry.domain (pointDeck k)
        ((p.particularBlock x.coefficients c x.state l).pressure n) ∧
      (∀ i, CoefficientsTranslation ActualInitialization.geometry.domain (pointDeck k)
        ((p.particularGaussianBlock x.coefficients c x.state l).velocity n i)))
    (hs : ∀ l n, ActualWaveRegularityData.Ordered l n → ∀ k,
      (∀ i, CoefficientsTranslation ActualInitialization.geometry.domain (pointDeck k)
        ((p.signedBlock x.coefficients c x.state l).velocity n i)) ∧
      CoefficientsTranslation ActualInitialization.geometry.domain (pointDeck k)
        ((p.signedBlock x.coefficients c x.state l).pressure n) ∧
      (∀ i, CoefficientsTranslation ActualInitialization.geometry.domain (pointDeck k)
        ((p.signedGaussianBlock x.coefficients c x.state l).velocity n i))) :
    Periodic (x.step p c) where
  velocity l n hn k i := ((h.velocity l n hn k i).add ((hp l n hn k).1 i)).add
    ((hs l n hn k).1 i)
  pressure l n hn k := ((h.pressure l n hn k).add (hp l n hn k).2.1).add
    (hs l n hn k).2.1
  gaussian l n hn k i := ((h.gaussian l n hn k i).add ((hp l n hn k).2.2 i)).add
    ((hs l n hn k).2.2 i)

theorem domain_deck (k : TorusInverse.Frequency) {z : Point}
    (hz : z ∈ ActualInitialization.geometry.domain) :
    z + pointDeck k ∈ ActualInitialization.geometry.domain := by
  change (z + pointDeck k).2.1 ∈ ActualPrimary.standardRegion.carrier
  simp only [pointDeck, Prod.add_def, add_zero]
  exact hz

theorem context_frame_translation (B n : ℕ) (k : TorusInverse.Frequency) :
    FrameTranslation ActualInitialization.geometry.domain (pointDeck k)
      (contextFrame (ActualPrimary.commonContext B) n) := by
  constructor
  · intro z _
    change (z + pointDeck k).1 = z.1
    simp only [pointDeck, Prod.add_def, add_zero]
  · intro z _
    change _ + (_ * RadialPullback.radialJacobian _ (z + pointDeck k).1) • _ = _
    simp only [pointDeck, Prod.add_def, add_zero]
    rfl
  · exact TranslationOn.const _
  · exact TranslationOn.const _

theorem context_base_translation (B n : ℕ) (k : TorusInverse.Frequency) :
    TranslationOn ActualInitialization.geometry.domain (pointDeck k)
      (contextBase (ActualPrimary.commonContext B) n) := by
  intro z _
  simp only [contextBase, ActualPrimary.commonContext, CommonBaseContext.context,
    BaseContextAssembly.nativeContext, BaseContextAssembly.context, BaseContextAssembly.base,
    BaseContextAssembly.radialBase, BaseContextAssembly.frequencyBase,
        BaseContextAssembly.axialBase,
    BaseContextAssembly.physicalPoint, BaseContextAssembly.slowCoordinates_apply,
    pointDeck, Prod.add_def, add_zero]

section CurrentSource

variable {B N0 : ℕ} {σ : ℝ} {x : CycleState (Index B N0)}
  {P : Index B N0 → ℕ → Point → ℝ} {S : Index B N0 → ℕ → Set Point}
  (H : CycleAnalyticInvariant ActualInitialization.geometry (ActualPrimary.commonContext B)
    ActualInitialization.tangentBlock P S σ x)

include H in
theorem state_mean_translation (n : ℕ) (k : TorusInverse.Frequency) :
    TranslationOn ActualInitialization.geometry.domain (pointDeck k) (stateMean x.state n) := by
  intro z hz
  have hr := H.primitives.mean.radial.periodic n z.1 z.2.1 hz z.2.2 k
  have ha := H.primitives.mean.angular.periodic n z.1 z.2.1 hz z.2.2 k
  have hz' := H.primitives.mean.axial.periodic n z.1 z.2.1 hz z.2.2 k
  dsimp only at hr ha hz'
  simp only [stateMean, add_pointDeck, TorusAverages.latticePoint]
  rw [hr, ha, hz']

include H in
theorem state_phase_translation (l : Index B N0) (n : ℕ)
    (hn : ActualWaveRegularityData.Ordered l n) (k : TorusInverse.Frequency) :
    TranslationOn ActualInitialization.geometry.domain (pointDeck k)
      ((x.coefficients.blocks l).phase n) := by
  rw [← (H.carrier l).phase]
  intro z _
  change (ActualPrimary.chartCoefficients l.2 l.1).phase n (z + pointDeck k, 0) =
    (ActualPrimary.chartCoefficients l.2 l.1).phase n (z, 0)
  simpa only [ActualPrimaryCoherence.chartDeck, pointDeck, Prod.add_def, add_zero] using
    ActualPrimaryCoherence.chart_phase_periodic l.2 l.1 n hn k (z, 0)

include H in
/-- The per-label real velocity, pressure, and retained Gaussian field
have the same periods as their literal coefficients. -/
theorem fields_ordered (h : Periodic x) (l : Index B N0) (n : ℕ)
    (hn : ActualWaveRegularityData.Ordered l n) (k : TorusInverse.Frequency) (θ : ℝ) :
    TranslationOn ActualInitialization.geometry.domain (pointDeck k)
      (fun z => (x.coefficients.blocks l).oscillation n (z, θ)) ∧
    TranslationOn ActualInitialization.geometry.domain (pointDeck k)
      (fun z => (x.coefficients.blocks l).oscillatoryPressure n (z, θ)) ∧
    TranslationOn ActualInitialization.geometry.domain (pointDeck k)
      (fun z => coefficientField (x.coefficients.blocks l) (x.coefficients.gaussian l) n (z, θ)) :=
          by
  have hΦ := state_phase_translation H l n hn k
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    funext i
    exact congrArg Complex.re ((h.velocity l n hn k i).field hΦ _ _ θ z hz)
  · intro z hz
    exact congrArg Complex.re ((h.pressure l n hn k).field hΦ _ _ θ z hz)
  · intro z hz
    funext i
    exact congrArg Complex.re ((h.gaussian l n hn k i).field hΦ _ _ θ z hz)

include H in
/-- Every actual residual coefficient has the common periods on an ordered band.
This uses the separate per-label hypotheses, not merely the total velocity. -/
theorem source_ordered (h : Periodic x) (l : Index B N0) (n : ℕ)
    (hn : ActualWaveRegularityData.Ordered l n) (j : ℤ) (k : TorusInverse.Frequency) :
    TranslationOn ActualInitialization.geometry.domain (pointDeck k)
      (ParticularWaveAssembly.residualSource (ActualPrimary.commonContext B) x.state
        (x.coefficients.blocks l) (x.coefficients.gaussian l)
        (x.coefficients.aliasCoefficients l) j n) := by
  apply residualSource_translation ActualInitialization.geometry.domain_open
    (ActualPrimary.commonContext B) x.state (x.coefficients.blocks l)
    (x.coefficients.gaussian l) (x.coefficients.aliasCoefficients l) n
    (context_frame_translation B n k) (context_base_translation B n k)
    (state_mean_translation H n k) (state_phase_translation H l n hn k)
    (h.velocity l n hn k) (h.pressure l n hn k) (h.gaussian l n hn k)
  intro i
  rw [H.aliasCoefficients l]
  exact CoefficientsTranslation.zero

include H in
theorem source_all (h : Periodic x)
    (hzero : ∀ l n, ¬ActualWaveRegularityData.Ordered l n → ∀ j z,
      z ∈ ActualInitialization.geometry.domain →
      ParticularWaveAssembly.residualSource (ActualPrimary.commonContext B) x.state
        (x.coefficients.blocks l) (x.coefficients.gaussian l)
        (x.coefficients.aliasCoefficients l) j n z = 0)
    (l : Index B N0) (n : ℕ) (j : ℤ) (k : TorusInverse.Frequency) :
    TranslationOn ActualInitialization.geometry.domain (pointDeck k)
      (ParticularWaveAssembly.residualSource (ActualPrimary.commonContext B) x.state
        (x.coefficients.blocks l) (x.coefficients.gaussian l)
        (x.coefficients.aliasCoefficients l) j n) := by
  by_cases hn : ActualWaveRegularityData.Ordered l n
  · exact source_ordered H h l n hn j k
  · intro z hz
    rw [hzero l n hn j (z + pointDeck k) (domain_deck k hz), hzero l n hn j z hz]

end CurrentSource

/-! The literal source, with the associator used by the particular solver. -/

/-- Copies, constructed using `ActualWaveRegularityData.particularCopies`. -/
noncomputable def copies {B N0 : ℕ} (x : CycleState (Index B N0))
    (l : Index B N0) (j : ℤ) :=
  ActualWaveRegularityData.particularCopies (l.2, l.1)
    (StateReindex.context cycleAssoc.symm (ActualPrimary.commonContext B))
    (StateReindex.state cycleAssoc.symm x.state)
    (StateReindex.block cycleAssoc.symm (x.coefficients.blocks l))
    (StateReindex.blockCoefficients cycleAssoc.symm (x.coefficients.gaussian l))
    (StateReindex.blockCoefficients cycleAssoc.symm (x.coefficients.aliasCoefficients l)) j

theorem copies_source {B N0 : ℕ} (x : CycleState (Index B N0))
    (l : Index B N0) (j : ℤ) (n : ℕ) (z : ActualWaveRegularity.ParticularSpace) :
    (copies x l j).source n z =
      ParticularWaveAssembly.residualSource (ActualPrimary.commonContext B) x.state
        (x.coefficients.blocks l) (x.coefficients.gaussian l)
        (x.coefficients.aliasCoefficients l) j n
        (ActualWaveRegularity.particularChart.symm z).1 := by
  change ParticularWaveAssembly.residualSource
    (StateReindex.context cycleAssoc.symm (ActualPrimary.commonContext B))
    (StateReindex.state cycleAssoc.symm x.state)
    (StateReindex.block cycleAssoc.symm (x.coefficients.blocks l))
    (StateReindex.blockCoefficients cycleAssoc.symm (x.coefficients.gaussian l))
    (StateReindex.blockCoefficients cycleAssoc.symm (x.coefficients.aliasCoefficients l))
      j n (z.1.1, z.2) = _
  unfold ParticularWaveAssembly.residualSource
  rw [StateReindex.residualBlock_pull]
  rfl

section NativeSource

variable {B N0 : ℕ} {σ : ℝ} {x : CycleState (Index B N0)}
  {P : Index B N0 → ℕ → Point → ℝ} {S : Index B N0 → ℕ → Set Point}
  (H : CycleAnalyticInvariant ActualInitialization.geometry (ActualPrimary.commonContext B)
    ActualInitialization.tangentBlock P S σ x)

include H in
theorem copies_source_ordered (h : Periodic x) (l : Index B N0) (n : ℕ)
    (hn : ActualWaveRegularityData.Ordered l n) (j : ℤ)
    (z : ActualWaveRegularity.ParticularSpace)
    (hz : z ∈ ActualWaveRegularity.nativeDomain ActualWaveRegularity.particularChart
      ActualPrimary.standardRegion) :
    CommonCoverSolve.PeriodicAt ((copies x l j).source n) z.1 := by
  intro Y k
  rw [copies_source, copies_source]
  have hy : (z.1.1.1, (z.1.1.2, Y)) ∈ ActualInitialization.geometry.domain := hz.1
  have hh := source_ordered H h l n hn j k (z.1.1.1, (z.1.1.2, Y)) hy
  simp only [pointDeck, Prod.add_def, add_zero] at hh
  exact hh

include H in
/-- The complete source callback required by the actual particular-copy solver.
Unordered bands are supplied by the independent support/zero-germ argument. -/
theorem copies_source_periodic (h : Periodic x)
    (hzero : ∀ l n, ¬ActualWaveRegularityData.Ordered l n → ∀ j z,
      z ∈ ActualInitialization.geometry.domain →
      ParticularWaveAssembly.residualSource (ActualPrimary.commonContext B) x.state
        (x.coefficients.blocks l) (x.coefficients.gaussian l)
        (x.coefficients.aliasCoefficients l) j n z = 0)
    (l : Index B N0) (j : ℤ) (n : ℕ) (z : ActualWaveRegularity.ParticularSpace)
    (hz : z ∈ ActualWaveRegularity.nativeDomain ActualWaveRegularity.particularChart
      ActualPrimary.standardRegion) :
    CommonCoverSolve.PeriodicAt ((copies x l j).source n) z.1 := by
  intro Y k
  rw [copies_source, copies_source]
  have hy : (z.1.1.1, (z.1.1.2, Y)) ∈ ActualInitialization.geometry.domain := hz.1
  have hh := source_all H h hzero l n j k (z.1.1.1, (z.1.1.2, Y)) hy
  simp only [pointDeck, Prod.add_def, add_zero] at hh
  exact hh

end NativeSource

section Propagation

variable {B N0 : ℕ} {σ : ℝ} {x : CycleState (Index B N0)}
  {P : Index B N0 → ℕ → Point → ℝ} {S : Index B N0 → ℕ → Set Point}
  (H : CycleAnalyticInvariant ActualInitialization.geometry (ActualPrimary.commonContext B)
    ActualInitialization.tangentBlock P S σ x)

include H in
theorem native_sources_periodic (h : Periodic x) (l : Index B N0) (n : ℕ)
    (hn : ActualWaveRegularityData.Ordered l n) :
    ActualWaveCoefficientPeriodicity.NativeSourcesPeriodic x.coefficients
      (ActualPrimary.commonContext B) x.state l n := by
  intro j _ z hz
  exact copies_source_ordered H h l n hn j z hz

include H in
/-- The literal four-stage cycle preserves the auxiliary periodicity
invariant. Both increments are the actual constructed waves, and their
source-periodicity premises are proved from the incoming coefficients. -/
theorem step (h : Periodic x) :
    Periodic (x.step (ActualCycleParameters.fixedParameters B N0)
      (ActualPrimary.commonContext B)) := by
  apply h.step_of_waves (ActualCycleParameters.fixedParameters B N0)
    (ActualPrimary.commonContext B)
  · intro l n hn k
    exact ActualWaveCoefficientPeriodicity.particular_coefficients x.coefficients
      (ActualPrimary.commonContext B) x.state l n hn k (H.carrier l)
      (native_sources_periodic H h l n hn)
  · intro l n hn k
    exact ActualWaveCoefficientPeriodicity.signed_coefficients x.coefficients
      (ActualPrimary.commonContext B) x.state l n hn k

end Propagation

end NavierStokes.ActualCyclePeriodicity
