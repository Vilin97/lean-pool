/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.SignedMeanGain

/-!
# Signed mean gain with fixed physical labels

The physical wave family keeps its original label type.  At each band an
injection on the active finite set identifies its coefficient data with the
relative native labels used by `SignedMeanGain.NativeData`.  Finite-sum
reindexing then gives the actual native cross identity.  The mean-gain theorem
is applied to the original family, with its original uniform constants.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.BandReindexedSignedMeanGain

open Set Function
open scoped BigOperators
open WeightedClasses MeanIncrementBounds CorrectionState SignedMeanGain

/-! ## Coefficient and carrier identities at one band -/

/-- The carrier metadata needed to compare the actual fields at one band.
No relationship at another band is required. -/
structure SameCarrierAt {D : Type} (a b : HarmonicBlock D) (n : ℕ) : Prop where
  frequency : b.frequency n = a.frequency n
  phase : b.phase n = a.phase n
  angular : b.angularFrequency n = a.angularFrequency n

theorem sameCarrierAt_of_sameCarrier {D : Type} {a b : HarmonicBlock D}
    (h : LabelSumBounds.SameCarrier a b) (n : ℕ) : SameCarrierAt a b n :=
  ⟨congrFun h.frequency n, congrFun h.phase n, congrFun h.angular n⟩

/-- Equality of the stored coefficients and carrier metadata identifies the
actual harmonic field at this band.  Pressure data are not used in covariance. -/
theorem oscillation_eq_at_band_of_coefficients {D : Type}
    (a b : HarmonicBlock D) (n : ℕ)
    (hv : a.velocity n = b.velocity n) (hc : SameCarrierAt a b n) :
    a.oscillation n = b.oscillation n := by
  funext p i
  simp only [HarmonicBlock.oscillation, hv, hc.frequency, hc.phase, hc.angular]

/-! ## Finite reindexing of actual fields -/

/-- Reindex a finite sum using only the coefficient and carrier identities
on its active labels.  Inactive labels need not have distinct images. -/
theorem fieldSum_reindex_of_coefficients {D ι κ : Type} [DecidableEq κ]
    (labels : ℕ → Finset ι) (nativeLabels : ℕ → Finset κ)
    (a : ι → HarmonicBlock D) (b : κ → HarmonicBlock D)
    (e : ℕ → ι → κ)
    (he : ∀ n, Set.InjOn (e n) (labels n : Set ι))
    (hlabels : ∀ n, (labels n).image (e n) = nativeLabels n)
    (hv : ∀ n l, l ∈ labels n → (a l).velocity n = (b (e n l)).velocity n)
    (hc : ∀ n l, l ∈ labels n → SameCarrierAt (a l) (b (e n l)) n) :
    LabelSumBounds.fieldSum labels (fun l => (a l).oscillation) =
      LabelSumBounds.fieldSum nativeLabels (fun l => (b l).oscillation) := by
  funext n p i
  simp only [LabelSumBounds.fieldSum]
  rw [← hlabels n, Finset.sum_image (he n)]
  apply Finset.sum_congr rfl
  intro l hl
  exact congrFun (congrFun
    (oscillation_eq_at_band_of_coefficients (a l) (b (e n l)) n
      (hv n l hl) (hc n l hl)) p) i

/-! ## The native requested cross for arbitrary physical labels -/

/-- The actual primary and tangent sums agree with the native sums after
bandwise finite reindexing.  This theorem does not reindex `SignedFamily`,
so none of its uniform coefficient bounds acquire a label-dependent constant. -/
theorem native_fields
    (G : Geometry) (B : NativeData G) (c : Context Point) (u : State Point)
    {ι : Type} {P : ι → ℕ → Point → ℝ} {α δ β η : ℝ}
    (f : LabelSumBounds.SignedFamily G.strip P α δ β η) (a : Assembly f)
    (e : ℕ → ι → NativeIndex)
    (he : ∀ n, Set.InjOn (e n) (a.labels n : Set ι))
    (hlabels : ∀ n, (a.labels n).image (e n) = B.labels n)
    (hp : ∀ n l, l ∈ a.labels n →
      (f.primary l).velocity n = (B.primaryBlocks (e n l)).velocity n)
    (hcp : ∀ n l, l ∈ a.labels n →
      SameCarrierAt (f.primary l) (B.primaryBlocks (e n l)) n)
    (ht : ∀ n l, l ∈ a.labels n →
      (f.tangent l).velocity n = (B.signedBlocks c u (e n l)).velocity n)
    (hct : ∀ n l, l ∈ a.labels n →
      SameCarrierAt (f.tangent l) (B.signedBlocks c u (e n l)) n) :
    primaryField f a = LabelSumBounds.fieldSum B.labels
      (fun l => (B.primaryBlocks l).oscillation) ∧
    tangentField f a = LabelSumBounds.fieldSum B.labels
      (fun l => (B.signedBlocks c u l).oscillation) := by
  exact ⟨fieldSum_reindex_of_coefficients a.labels B.labels f.primary B.primaryBlocks
      e he hlabels hp hcp,
    fieldSum_reindex_of_coefficients a.labels B.labels f.tangent (B.signedBlocks c u)
      e he hlabels ht hct⟩

/-- The same primary matrix, masks, fundamental, and signed inverse supply
the requested physical stress.  Both cross identities are conclusions. -/
theorem native_family_cross
    (G : Geometry) (B : NativeData G) (c : Context Point) (u : State Point)
    {ι : Type} {P : ι → ℕ → Point → ℝ} {α δ β η : ℝ}
    (f : LabelSumBounds.SignedFamily G.strip P α δ β η) (a : Assembly f)
    (e : ℕ → ι → NativeIndex)
    (he : ∀ n, Set.InjOn (e n) (a.labels n : Set ι))
    (hlabels : ∀ n, (a.labels n).image (e n) = B.labels n)
    (hp : ∀ n l, l ∈ a.labels n →
      (f.primary l).velocity n = (B.primaryBlocks (e n l)).velocity n)
    (hcp : ∀ n l, l ∈ a.labels n →
      SameCarrierAt (f.primary l) (B.primaryBlocks (e n l)) n)
    (ht : ∀ n l, l ∈ a.labels n →
      (f.tangent l).velocity n = (B.signedBlocks c u (e n l)).velocity n)
    (hct : ∀ n l, l ∈ a.labels n →
      SameCarrierAt (f.tangent l) (B.signedBlocks c u (e n l)) n) :
    Agree G.strip.domain (StateMomentBalances.meanBar (crossTensor f a 0 1))
      (physicalSigma G 2 (u.thetaResidual c)) ∧
    Agree G.strip.domain (StateMomentBalances.meanBar (crossTensor f a 0 2))
      (physicalSigma G 1 (u.axialResidual c)) := by
  obtain ⟨hprimary, htangent⟩ := native_fields G B c u f a e he hlabels hp hcp ht hct
  constructor
  · have ht := B.requested_cross c u 0
    simp only [crossTensor, hprimary, htangent, LocalSignedRequest.requestedStress,
      Matrix.cons_val_zero] at ht ⊢
    exact ht
  · have ht := B.requested_cross c u 1
    simp only [crossTensor, hprimary, htangent, LocalSignedRequest.requestedStress,
      Matrix.cons_val_one] at ht ⊢
    exact ht

/-! ## The gain for the original family and literal reconstructed state -/

/-- Signed-wave mean gain for fixed physical labels and a band-dependent
native reindexing.  The input uniform bounds remain those of `f` on the
original label type.  The output is the actual moving-gauge reconstructed
state, including the supplied Gaussian error and all covariance terms. -/
theorem native_signed_mean_gain
    (G : Geometry) (B : NativeData G) (c : Context Point) (u : State Point)
    {ι : Type} {P : ι → ℕ → Point → ℝ} {σ κ : ℝ}
    (hσ : 1 / 5 ≤ σ) (hκ : 0 ≤ κ) (hκsmall : κ ≤ 1 / 100000)
    (f : LabelSumBounds.SignedFamily G.strip P (1 / 2) (17 / 25)
      (1 / 2 + σ - κ) (1 + σ - 2 * κ)) (a : Assembly f)
    (e : ℕ → ι → NativeIndex)
    (he : ∀ n, Set.InjOn (e n) (a.labels n : Set ι))
    (hlabels : ∀ n, (a.labels n).image (e n) = B.labels n)
    (hp : ∀ n l, l ∈ a.labels n →
      (f.primary l).velocity n = (B.primaryBlocks (e n l)).velocity n)
    (hcp : ∀ n l, l ∈ a.labels n →
      SameCarrierAt (f.primary l) (B.primaryBlocks (e n l)) n)
    (ht : ∀ n l, l ∈ a.labels n →
      (f.tangent l).velocity n = (B.signedBlocks c u (e n l)).velocity n)
    (hct : ∀ n l, l ∈ a.labels n →
      SameCarrierAt (f.tangent l) (B.signedBlocks c u (e n l)) n)
    (q : OscillatoryScalar Point) (gaussian : Oscillation Point)
    (hold : u.oscillation = oldField f a)
    (H : LocalData G c u (tangentField f a + curlField f a) q gaussian)
    (ho : OperatorBounds G.strip G.operators κ)
    (hX : ∀ i j, MovingField G (incrementTensor f a i j))
    (hS : ∀ i j, MovingField G (crossTensor f a i j))
    (hθ : MeanClass G.strip (1 + σ - κ) (u.thetaResidual c))
    (hz : MeanClass G.strip (1 + σ - κ) (u.axialResidual c))
    (hd : DefectBounds G.slowStrip (σ - κ) c u) :
    let v := waveStage G.gauge c u (tangentField f a + curlField f a) q gaussian
    MeanClass G.strip (1 + σ - 2 * κ) (v.thetaResidual c) ∧
    MeanClass G.strip (1 + σ - 2 * κ) (v.axialResidual c) ∧
    MeanClass G.strip (1 + σ + 17 / 100) (StateMomentBalances.meanBar (v.thetaResidual c)) ∧
    MeanClass G.strip (1 + σ + 17 / 100) (StateMomentBalances.meanBar (v.axialResidual c)) := by
  obtain ⟨hcθ, hcz⟩ := native_family_cross G B c u f a e he hlabels hp hcp ht hct
  exact SignedMeanGain.signed_mean_gain_of_cross G c u hσ hκ hκsmall f a q gaussian
    hold H ho hX hS hθ hz hd hcθ hcz

end NavierStokes.BandReindexedSignedMeanGain
