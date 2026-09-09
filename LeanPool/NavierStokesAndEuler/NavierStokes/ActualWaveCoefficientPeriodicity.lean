/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualWaveRegularityData
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualCycleParameters

/-!
# Deck translations of the actual wave-block coefficients

Native coefficient translations pass through the literal angular section,
finite harmonic sum, conjugate pairing, and coordinate reindexing.  The
particular source assumption is made on full native parameter fibers.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.ActualWaveCoefficientPeriodicity

open Set Function Filter CorrectionState CorrectionStep
open ActualWaveRegularity
open scoped BigOperators Topology ContDiff


/-- Point: an abbreviation for `LocalSignedRequest.Point`. -/
abbrev Point := LocalSignedRequest.Point
/-- Full point: an abbreviation for `Point × ℝ`. -/
abbrev FullPoint := Point × ℝ
/-- Index: an abbreviation for `ActualInitialization.Index B N0`. -/
abbrev Index (B N0 : ℕ) := ActualInitialization.Index B N0
/-- Frequency: an abbreviation for `TorusInverse.Frequency`. -/
abbrev Frequency := TorusInverse.Frequency

/-- Point deck, given by `(0, (0, TorusAverages.latticePoint k))`. -/
noncomputable def pointDeck (k : Frequency) : Point :=
  (0, (0, TorusAverages.latticePoint k))

/-- Native section, given by `ActualWaveRegularity.particularChart (x, 0)`. -/
noncomputable def nativeSection (x : Point) : ActualWaveRegularity.ParticularSpace :=
  ActualWaveRegularity.particularChart (x, 0)

theorem fullSection_deck (x : Point) (k : Frequency) :
    (x + pointDeck k, (0 : ℝ)) = (x, 0) + ActualWaveRegularity.deckShift k := by
  change (x + pointDeck k, (0 : ℝ)) = (x + pointDeck k, 0 + 0)
  rw [add_zero]

theorem nativeSection_deck (x : Point) (k : Frequency) :
    nativeSection (x + pointDeck k) = nativeSection x +
      ActualWaveRegularity.particularChart (ActualWaveRegularity.deckShift k) := by
  unfold nativeSection
  rw [fullSection_deck, map_add]

theorem fullSection_mem {x : Point} (hx : x ∈ ActualInitialization.geometry.domain) :
    (x, (0 : ℝ)) ∈ ActualWaveRegularity.fullDomain
      CorrectionInitialization.ActualPrimary.standardRegion :=
  ⟨hx, mem_univ _⟩

theorem nativeSection_mem {x : Point} (hx : x ∈ ActualInitialization.geometry.domain) :
    nativeSection x ∈ ActualWaveRegularity.nativeDomain ActualWaveRegularity.particularChart
      CorrectionInitialization.ActualPrimary.standardRegion := by
  change ActualWaveRegularity.particularChart.symm
    (ActualWaveRegularity.particularChart (x,0)) ∈ ActualWaveRegularity.fullDomain
      CorrectionInitialization.ActualPrimary.standardRegion
  rw [LinearIsometryEquiv.symm_apply_apply]
  exact fullSection_mem hx

theorem fullSection_translation {E : Type} {k : Frequency} {f : FullPoint → E}
    (hf : TranslationOn (ActualWaveRegularity.fullDomain
      CorrectionInitialization.ActualPrimary.standardRegion) (ActualWaveRegularity.deckShift k) f) :
    TranslationOn ActualInitialization.geometry.domain (pointDeck k) (fun x => f (x,0)) := by
  intro x hx
  change f (x + pointDeck k, 0) = f (x, 0)
  rw [fullSection_deck]
  exact hf (x,0) (fullSection_mem hx)

theorem nativeSection_translation {E : Type} {k : Frequency}
    {f : ActualWaveRegularity.ParticularSpace → E}
    (hf : TranslationOn (ActualWaveRegularity.nativeDomain ActualWaveRegularity.particularChart
      CorrectionInitialization.ActualPrimary.standardRegion)
      (ActualWaveRegularity.particularChart (ActualWaveRegularity.deckShift k)) f) :
    TranslationOn ActualInitialization.geometry.domain (pointDeck k) (fun x => f (nativeSection x))
        := by
  intro x hx
  change f (nativeSection (x + pointDeck k)) = f (nativeSection x)
  rw [nativeSection_deck]
  exact hf (nativeSection x) (nativeSection_mem hx)

section FiniteAssembly

variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
  {Ω : Set D} {shift : D}

omit [NormedSpace ℝ D] in
theorem conjugatePair_translation {f : D → ℂ}
    (hf : TranslationOn Ω shift f) (j m : ℤ) :
    TranslationOn Ω shift (ErrorHarmonics.conjugatePair j f m) := by
  intro x hx
  simp only [ParticularWaveAssembly.pair_apply, hf x hx]

omit [NormedSpace ℝ D] in
theorem assembled_velocity_translation {E : Type} (e : D → E) (N : ℕ) (frequency : ℕ → ℝ)
    (phase : ℕ → E → ℝ) (angular : ℕ → ℤ)
    (v : ℤ → ℕ → E → HarmonicCalculus.ComplexVector) (p : ℤ → ℕ → E → ℂ)
    (n : ℕ) (hv : ∀ j ∈ ParticularWaveAssembly.modes N,
      TranslationOn Ω shift (fun x => v j n (e x)))
    (i : Fin 3) (m : ℤ) :
    TranslationOn Ω shift
      (fun x => (ParticularWaveAssembly.assembledBlock N frequency phase angular v p).velocity n i
          m (e x)) := by
  intro x hx
  simp only [ParticularWaveAssembly.assembledBlock, ErrorHarmonics.sumBlock,
    ParticularWaveAssembly.modeBlock]
  rw [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j hj
  have he := congrFun (hv j hj x hx) i
  simp only [ParticularWaveAssembly.pair_apply, he]

omit [NormedSpace ℝ D] in
theorem assembled_pressure_translation {E : Type} (e : D → E) (N : ℕ) (frequency : ℕ → ℝ)
    (phase : ℕ → E → ℝ) (angular : ℕ → ℤ)
    (v : ℤ → ℕ → E → HarmonicCalculus.ComplexVector) (p : ℤ → ℕ → E → ℂ)
    (n : ℕ) (hp : ∀ j ∈ ParticularWaveAssembly.modes N,
      TranslationOn Ω shift (fun x => p j n (e x)))
    (m : ℤ) :
    TranslationOn Ω shift
      (fun x => (ParticularWaveAssembly.assembledBlock N frequency phase angular v p).pressure n m
          (e x)) := by
  intro x hx
  simp only [ParticularWaveAssembly.assembledBlock, ErrorHarmonics.sumBlock,
    ParticularWaveAssembly.modeBlock]
  rw [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [ParticularWaveAssembly.pair_apply, hp j hj x hx]

end FiniteAssembly

variable {B N0 : ℕ}

/-- Particular data, given by `ActualWaveRegularity.particularCopyData
(ActualCycleParameters.fixedParameters B N0) v c u l j`. -/
noncomputable def particularData (v : CycleCoefficients (Index B N0))
    (c : Context Point) (u : State Point) (l : Index B N0) (j : ℤ) :=
  ActualWaveRegularity.particularCopyData (ActualCycleParameters.fixedParameters B N0) v c u l j

/-- The incoming carrier is identified before applying the native
translation theorem; no carrier of a solved wave is assumed. -/
theorem particular_phase (v : CycleCoefficients (Index B N0))
    (c : Context Point) (u : State Point) (l : Index B N0)
    (hc : SameCarrier (v.blocks l) (ActualInitialization.tangentBlock l)) (j : ℤ) :
    (particularData v c u l j).background.phase =
      (ActualParticularStageControls.background (l.2,l.1)).phase := by
  funext n z
  change (v.blocks l).phase n (cycleAssoc.symm (z.1.1,z.2)) +
    ((v.blocks l).angularFrequency n : ℝ) / (v.blocks l).frequency n * z.1.2 = _
  rw [← hc.phase, ← hc.angular, ← hc.frequency]
  change (CorrectionInitialization.ActualPrimary.chartCoefficients l.2 l.1).phase n
      ((z.1.1.1,(z.1.1.2,z.2)),0) +
    (PrimaryGeometryAssembly.angularMode CorrectionInitialization.ActualPrimary.certificate
      CorrectionInitialization.ActualPrimary.modulation
      (CorrectionInitialization.ActualPrimary.choice B N0).prepared l.2 l.1 : ℝ) /
      (ChartScales.carrier CorrectionInitialization.ActualPrimary.h n : ℝ) * z.1.2 =
    (CorrectionInitialization.ActualPrimary.chartCoefficients l.2 l.1).phase n
      ((z.1.1.1,(z.1.1.2,z.2)),z.1.2)
  simp only [CorrectionInitialization.ActualPrimary.chartCoefficients,
    CorrectionInitialization.ActualPrimary.absolutePhase, mul_zero, zero_add]
  ring

/-- The finite list of actual particular sources has its asserted periods
on the complete native parameter fibers. -/
noncomputable def NativeSourcesPeriodic (v : CycleCoefficients (Index B N0))
    (c : Context Point) (u : State Point) (l : Index B N0) (n : ℕ) : Prop :=
  ∀ j ∈ ParticularWaveAssembly.modes v.residualBand,
    ∀ z, z ∈ ActualWaveRegularity.nativeDomain ActualWaveRegularity.particularChart
      CorrectionInitialization.ActualPrimary.standardRegion →
      CommonCoverSolve.PeriodicAt ((particularData v c u l j).source n) z.1

/-- Ordered-band periods of the literal particular block and its Gaussian
block, including every Fourier coefficient rather than only real fields. -/
theorem particular_coefficients (v : CycleCoefficients (Index B N0))
    (c : Context Point) (u : State Point) (l : Index B N0) (n : ℕ)
    (hn : ActualWaveRegularityData.Ordered l n) (k : Frequency)
    (hc : SameCarrier (v.blocks l) (ActualInitialization.tangentBlock l))
    (hsource : NativeSourcesPeriodic v c u l n) :
    (∀ i m, TranslationOn ActualInitialization.geometry.domain (pointDeck k)
      (((ActualCycleParameters.fixedParameters B N0).particularBlock v c u l).velocity n i m)) ∧
    (∀ m, TranslationOn ActualInitialization.geometry.domain (pointDeck k)
      (((ActualCycleParameters.fixedParameters B N0).particularBlock v c u l).pressure n m)) ∧
    (∀ i m, TranslationOn ActualInitialization.geometry.domain (pointDeck k)
      (((ActualCycleParameters.fixedParameters B N0).particularGaussianBlock v c u l).velocity n i
          m)) := by
  have ht (j : ℤ) (hj : j ∈ ParticularWaveAssembly.modes v.residualBand) :=
    ActualWaveRegularityData.particular_coefficient_translations (l.2,l.1)
      (StateReindex.context cycleAssoc.symm c) (StateReindex.state cycleAssoc.symm u)
      (StateReindex.block cycleAssoc.symm (v.blocks l))
      (StateReindex.blockCoefficients cycleAssoc.symm (v.gaussian l))
      (StateReindex.blockCoefficients cycleAssoc.symm (v.aliasCoefficients l)) j
      (particular_phase v c u l hc j) n hn k (hsource j hj)
  refine ⟨?_, ?_, ?_⟩
  · intro i m
    apply assembled_velocity_translation (fun x => cycleAssoc x)
    intro j hj
    exact nativeSection_translation (ht j hj).2.1
  · intro m
    apply assembled_pressure_translation (fun x => cycleAssoc x)
    intro j hj
    exact nativeSection_translation (ht j hj).2.2.1
  · intro i m
    apply assembled_velocity_translation (fun x => cycleAssoc x)
    intro j hj
    exact nativeSection_translation (ht j hj).2.2.2

/-- The actual signed request gives the native periods directly; no
periodicity assumption on an output block or on a freely supplied request
is needed. -/
theorem signed_coefficients (v : CycleCoefficients (Index B N0))
    (c : Context Point) (u : State Point) (l : Index B N0) (n : ℕ)
    (hn : ActualWaveRegularityData.Ordered l n) (k : Frequency) :
    (∀ i m, TranslationOn ActualInitialization.geometry.domain (pointDeck k)
      (((ActualCycleParameters.fixedParameters B N0).signedBlock v c u l).velocity n i m)) ∧
    (∀ m, TranslationOn ActualInitialization.geometry.domain (pointDeck k)
      (((ActualCycleParameters.fixedParameters B N0).signedBlock v c u l).pressure n m)) ∧
    (∀ i m, TranslationOn ActualInitialization.geometry.domain (pointDeck k)
      (((ActualCycleParameters.fixedParameters B N0).signedGaussianBlock v c u l).velocity n i m))
          := by
  have ht := ActualWaveRegularityData.signed_coefficient_translations l
    ActualInitialization.geometry.patch ActualInitialization.geometry.coord c
    ((ActualCycleParameters.fixedParameters B N0).afterParticular v c u) n hn k
  refine ⟨?_, ?_, ?_⟩
  · intro i m
    exact conjugatePair_translation ((fullSection_translation ht.2.1).component i) 1 m
  · intro m
    exact conjugatePair_translation (fullSection_translation ht.2.2.1) 1 m
  · intro i m
    exact conjugatePair_translation ((fullSection_translation ht.2.2.2).component i) 1 m

end NavierStokes.ActualWaveCoefficientPeriodicity
