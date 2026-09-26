/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.ProbeEnvelope

/-! # Bad Event Summability -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

open MeasureTheory
open IndependentSums
open scoped BigOperators ENNReal

/-!
# Bad-pair tail estimates

This file contains the one-pair tail estimates used by the quantitative
minimal-scale proof.
-/

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A Γ-tail controls any event contained in the corresponding upper-tail
event. -/
theorem measureReal_le_exp_of_subset_upperTail_gammaSigma
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : Ω → ℝ} {E : Set Ω} {A σ s : ℝ}
    (hX : IsBigOWith μ (gammaSigma σ) X A)
    (hs : 1 ≤ s)
    (hE : E ⊆ upperTailEvent X (A * s)) :
    μ.real E ≤ Real.exp (-(s ^ σ)) := by
  calc
    μ.real E ≤ μ.real (upperTailEvent X (A * s)) := by
      exact measureReal_mono hE
    _ ≤ Real.exp (-(s ^ σ)) := by
      simpa [gammaSigma, Real.exp_neg] using hX hs

omit [MeasurableSpace Ω] in
/-- If the deterministic center and stochastic Γ-scale each fit into half of
the target threshold, then the threshold exceedance is a centered upper-tail
event. -/
theorem thresholdEvent_subset_centered_upperTail
    {H : Ω → ℝ} {A c T s : ℝ}
    (hcenter : c ≤ T / 2)
    (hscale : A * s ≤ T / 2) :
    {ω | T < H ω} ⊆ upperTailEvent (fun ω => H ω - c) (A * s) := by
  intro ω hω
  have hsum : A * s + c ≤ T := by linarith
  have hT_lt : T < H ω := hω
  change A * s < H ω - c
  linarith

/-- One-pair bad-event estimate for a discounted observable.  The hypothesis
`discount * T ≤ R` says that `T` is a post-discount threshold below the bad
event threshold `R`. -/
theorem measureReal_discounted_badPair_le_exp_of_isBigOWith_gammaSigma
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {H : Ω → ℝ} {A c T s σ discount R : ℝ}
    (hX : IsBigOWith μ (gammaSigma σ) (fun ω => H ω - c) A)
    (hs : 1 ≤ s)
    (hdiscount_pos : 0 < discount)
    (hthreshold : discount * T ≤ R)
    (hcenter : c ≤ T / 2)
    (hscale : A * s ≤ T / 2) :
    μ.real {ω | R < discount * H ω} ≤ Real.exp (-(s ^ σ)) := by
  refine measureReal_le_exp_of_subset_upperTail_gammaSigma
    (μ := μ) (X := fun ω => H ω - c)
    (E := {ω | R < discount * H ω}) hX hs ?_
  intro ω hω
  have hdisc_lt : discount * T < discount * H ω :=
    lt_of_le_of_lt hthreshold hω
  have hT_lt : T < H ω := by
    nlinarith
  exact thresholdEvent_subset_centered_upperTail
    (H := H) (A := A) (c := c) (T := T) (s := s)
    hcenter hscale hT_lt

/-- One-pair bad-event estimate from a symmetric Γ-bound, used for the crude
bottom-scale contribution. -/
theorem measureReal_discounted_badPair_le_exp_of_isBigO_gammaSigma
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {H : Ω → ℝ} {A T s σ discount R : ℝ}
    (hX : IsBigO μ (gammaSigma σ) H A)
    (hs : 1 ≤ s)
    (hdiscount_pos : 0 < discount)
    (hthreshold : discount * T ≤ R)
    (hscale : A * s ≤ T) :
    μ.real {ω | R < discount * H ω} ≤ Real.exp (-(s ^ σ)) := by
  refine measureReal_le_exp_of_subset_upperTail_gammaSigma
    (μ := μ) (X := fun ω => |H ω|)
    (E := {ω | R < discount * H ω}) hX hs ?_
  intro ω hω
  have hdisc_lt : discount * T < discount * H ω :=
    lt_of_le_of_lt hthreshold hω
  have hT_lt : T < H ω := by
    nlinarith
  change A * s < |H ω|
  exact lt_of_le_of_lt hscale (lt_of_lt_of_le hT_lt (le_abs_self (H ω)))

/-- The fixed-pair component of `badScaleEvent`. -/
def badPairEvent {Ω : Type*}
    (H : ℕ → ℕ → Ω → ℝ) (t α : ℝ) (N m n : ℕ) : Set Ω :=
  {ω | n < m ∧ N ≤ m ∧
    (3 : ℝ) ^ (-t * ((m - n : ℕ) : ℝ)) * H m n ω >
      (3 : ℝ) ^ (-α * ((m - N : ℕ) : ℝ))}

/-- The bad event used in the quantitative minimal-scale theorem: at scale
`N`, some larger pair `(m,n)` violates the discounted algebraic estimate. -/
def badScaleEvent {Ω : Type*}
    (H : ℕ → ℕ → Ω → ℝ) (t α : ℝ) (N : ℕ) : Set Ω :=
  {ω | ∃ m n : ℕ, n < m ∧ N ≤ m ∧
    (3 : ℝ) ^ (-t * ((m - n : ℕ) : ℝ)) * H m n ω >
      (3 : ℝ) ^ (-α * ((m - N : ℕ) : ℝ))}

omit [MeasurableSpace Ω] in
theorem badScaleEvent_eq_iUnion_badPairEvent
    {H : ℕ → ℕ → Ω → ℝ} {t α : ℝ} {N : ℕ} :
    badScaleEvent H t α N =
      ⋃ p : ℕ × ℕ, badPairEvent H t α N p.1 p.2 := by
  ext ω
  simp [badScaleEvent, badPairEvent, Prod.exists]

/-- Localized first-quenched estimate for the concrete finite-probe envelope.

The only change from `localizedFirstQuenchedEstimate_normalizedProbeJMax` is
the deterministic multiplication by the dimension-only envelope constant. -/
theorem localizedFirstQuenchedEstimate_quenchedProbeEnvelope
    {d : ℕ} [NeZero d] {σ : ℝ}
    (hσ_pos : 0 < σ)
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ Cfluct Centry α : ℝ, 0 < Cfluct ∧ 0 < Centry ∧ 0 < α ∧
      ∀ {P : Ch04.RestrictionCoeffLaw d}
        (hP : Ch04.RestrictionLawCarrier P)
        (hStruct : Ch04.RestrictionStructuralLaw P)
        (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct),
        hΓ.sigma = σ → hΓ.params = params →
      ∀ {ℓ n m : ℕ}, ℓ < n → n < m →
        let N0 : ℕ :=
          annealedAlgebraicEntryScale P
            hΓ.toQuantitativeCoarseGrainedEllipticity Centry
        let D : Finset (TriadicCube d) :=
          descendantsAtScale
            (originCube d (((N0 + m : ℕ) : ℤ)))
            (((N0 + n : ℕ) : ℤ))
        let S : Finset (NormalizedProbeIndex d) := Finset.univ
        IsBigOWith P (gammaSigma (min σ 2))
          (fun a =>
            quenchedProbeEnvelope hP hStruct (N0 + m) (N0 + n) a -
              quenchedProbeEnvelopeConst d *
                Real.rpow (3 : ℝ) (-α * (ℓ : ℝ)))
          (quenchedProbeEnvelopeConst d *
            (((3 * Real.log (S.card : ℝ)) ^ (min σ 2)⁻¹) *
              (((3 * Real.log (D.card : ℝ)) ^ (min σ 2)⁻¹) *
                (Cfluct *
                  (3 : ℝ) ^
                    (-(d : ℝ) / 2 *
                      (Int.toNat
                        ((((N0 + n : ℕ) : ℤ) -
                          ((N0 + ℓ : ℕ) : ℤ))) : ℝ)) *
                  hΓ.thetaHat ^ (2 : ℕ))))) := by
  obtain ⟨Cfluct, Centry, α, hCfluct, hCentry, hα, hprobe⟩ :=
    localizedFirstQuenchedEstimate_normalizedProbeJMax
      (d := d) hσ_pos params
  refine ⟨Cfluct, Centry, α, hCfluct, hCentry, hα, ?_⟩
  intro P hP hStruct hΓ hσ_eq hparams ℓ n m hℓn hnm
  let K : ℝ := quenchedProbeEnvelopeConst d
  let N0 : ℕ :=
    annealedAlgebraicEntryScale P
      hΓ.toQuantitativeCoarseGrainedEllipticity Centry
  let D : Finset (TriadicCube d) :=
    descendantsAtScale
      (originCube d (((N0 + m : ℕ) : ℤ)))
      (((N0 + n : ℕ) : ℤ))
  let S : Finset (NormalizedProbeIndex d) := Finset.univ
  let r : ℝ := Real.rpow (3 : ℝ) (-α * (ℓ : ℝ))
  let A : ℝ :=
    ((3 * Real.log (S.card : ℝ)) ^ (min σ 2)⁻¹) *
      (((3 * Real.log (D.card : ℝ)) ^ (min σ 2)⁻¹) *
        (Cfluct *
          (3 : ℝ) ^
            (-(d : ℝ) / 2 *
              (Int.toNat
                ((((N0 + n : ℕ) : ℤ) -
                  ((N0 + ℓ : ℕ) : ℤ))) : ℝ)) *
          hΓ.thetaHat ^ (2 : ℕ)))
  have htail :
      IsBigOWith P (gammaSigma (min σ 2))
        (fun a =>
          localizedNormalizedProbeJMax hP hStruct (N0 + m) (N0 + n) a - r)
        A := by
    simpa [N0, D, S, r, A] using
      hprobe hP hStruct hΓ hσ_eq hparams hℓn hnm
  have hmul :=
    IsBigOWith.const_mul
      (μ := P) (Ψ := gammaSigma (min σ 2))
      (X := fun a =>
        localizedNormalizedProbeJMax hP hStruct (N0 + m) (N0 + n) a - r)
      (A := A) (c := K)
      (by simpa [K] using quenchedProbeEnvelopeConst_nonneg d) htail
  simpa [quenchedProbeEnvelope, K, N0, D, S, r, A, mul_sub] using hmul

/-- Crude Γσ estimate for the concrete finite-probe envelope. -/
theorem isBigO_quenchedProbeEnvelope
    {d : ℕ} [NeZero d] {σ : ℝ}
    (hσ_pos : 0 < σ)
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {P : Ch04.RestrictionCoeffLaw d}
        (hP : Ch04.RestrictionLawCarrier P)
        (hStruct : Ch04.RestrictionStructuralLaw P)
        (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct),
        hΓ.sigma = σ → hΓ.params = params →
      ∀ {m n : ℕ}, n < m →
        let D : Finset (TriadicCube d) :=
          descendantsAtScale (originCube d ((m : ℕ) : ℤ)) ((n : ℕ) : ℤ)
        let S : Finset (NormalizedProbeIndex d) := Finset.univ
        IsBigO P (gammaSigma σ)
          (quenchedProbeEnvelope hP hStruct m n)
          (quenchedProbeEnvelopeConst d *
            (((3 * Real.log (S.card : ℝ)) ^ σ⁻¹) *
              (((3 * Real.log (D.card : ℝ)) ^ σ⁻¹) *
                (C * hΓ.thetaHat ^ (2 : ℕ))))) := by
  obtain ⟨C, hC, hprobe⟩ :=
    isBigO_localizedNormalizedProbeJMax (d := d) hσ_pos params
  refine ⟨C, hC, ?_⟩
  intro P hP hStruct hΓ hσ_eq hparams m n hnm
  let K : ℝ := quenchedProbeEnvelopeConst d
  let D : Finset (TriadicCube d) :=
    descendantsAtScale (originCube d ((m : ℕ) : ℤ)) ((n : ℕ) : ℤ)
  let S : Finset (NormalizedProbeIndex d) := Finset.univ
  let A : ℝ :=
    ((3 * Real.log (S.card : ℝ)) ^ σ⁻¹) *
      (((3 * Real.log (D.card : ℝ)) ^ σ⁻¹) *
        (C * hΓ.thetaHat ^ (2 : ℕ)))
  have htail :
      IsBigO P (gammaSigma σ)
        (localizedNormalizedProbeJMax hP hStruct m n) A := by
    simpa [D, S, A] using
      hprobe hP hStruct hΓ hσ_eq hparams hnm
  have hmul :=
    IsBigO.const_mul
      (μ := P) (Ψ := gammaSigma σ)
      (X := localizedNormalizedProbeJMax hP hStruct m n)
      (A := A) (c := K)
      (by simpa [K] using quenchedProbeEnvelopeConst_nonneg d) htail
  simpa [quenchedProbeEnvelope, K, D, S, A] using! hmul

/-- Fixed-pair high-scale bad-event estimate, after shifting the deterministic
entry scale to zero.  The three threshold hypotheses are deterministic and are
where the later interpolation choice of `ℓ` is used. -/
theorem measureReal_shiftedHigh_badPairEvent_quenchedProbeEnvelope_le_exp
    {d : ℕ} [NeZero d] {σ : ℝ}
    (hσ_pos : 0 < σ)
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ Cfluct Centry a : ℝ, 0 < Cfluct ∧ 0 < Centry ∧ 0 < a ∧
      ∀ {t αbad : ℝ},
      ∀ {P : Ch04.RestrictionCoeffLaw d}
        (hP : Ch04.RestrictionLawCarrier P)
        (hStruct : Ch04.RestrictionStructuralLaw P)
        (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct),
        hΓ.sigma = σ → hΓ.params = params →
      ∀ {q m n ℓ : ℕ} {s T : ℝ}, ℓ < n → n < m → q ≤ m → 1 ≤ s →
        let N0 : ℕ :=
          annealedAlgebraicEntryScale P
            hΓ.toQuantitativeCoarseGrainedEllipticity Centry
        let D : Finset (TriadicCube d) :=
          descendantsAtScale
            (originCube d (((N0 + m : ℕ) : ℤ)))
            (((N0 + n : ℕ) : ℤ))
        let S : Finset (NormalizedProbeIndex d) := Finset.univ
        let A : ℝ :=
          quenchedProbeEnvelopeConst d *
            (((3 * Real.log (S.card : ℝ)) ^ (min σ 2)⁻¹) *
              (((3 * Real.log (D.card : ℝ)) ^ (min σ 2)⁻¹) *
                (Cfluct *
                  (3 : ℝ) ^
                    (-(d : ℝ) / 2 *
                      (Int.toNat
                        ((((N0 + n : ℕ) : ℤ) -
                          ((N0 + ℓ : ℕ) : ℤ))) : ℝ)) *
                  hΓ.thetaHat ^ (2 : ℕ))))
        let c : ℝ :=
          quenchedProbeEnvelopeConst d *
            Real.rpow (3 : ℝ) (-a * (ℓ : ℝ))
        let discount : ℝ := (3 : ℝ) ^ (-t * ((m - n : ℕ) : ℝ))
        let R : ℝ := (3 : ℝ) ^ (-αbad * ((m - q : ℕ) : ℝ))
        discount * T ≤ R →
        c ≤ T / 2 →
        A * s ≤ T / 2 →
        P.real
          (badPairEvent
            (fun M N aω =>
              quenchedProbeEnvelope hP hStruct (N0 + M) (N0 + N) aω)
            t αbad q m n) ≤
          Real.exp (-(s ^ (min σ 2))) := by
  obtain ⟨Cfluct, Centry, a, hCfluct, hCentry, ha, hfirst⟩ :=
    localizedFirstQuenchedEstimate_quenchedProbeEnvelope
      (d := d) hσ_pos params
  refine ⟨Cfluct, Centry, a, hCfluct, hCentry, ha, ?_⟩
  intro t αbad P hP hStruct hΓ hσ_eq hparams q m n ℓ s T hℓn hnm hqm hs
  dsimp only
  intro hthreshold hcenter hscale
  let : IsProbabilityMeasure P := hP.isProbability
  let N0 : ℕ :=
    annealedAlgebraicEntryScale P
      hΓ.toQuantitativeCoarseGrainedEllipticity Centry
  let D : Finset (TriadicCube d) :=
    descendantsAtScale
      (originCube d (((N0 + m : ℕ) : ℤ)))
      (((N0 + n : ℕ) : ℤ))
  let S : Finset (NormalizedProbeIndex d) := Finset.univ
  let A : ℝ :=
    quenchedProbeEnvelopeConst d *
      (((3 * Real.log (S.card : ℝ)) ^ (min σ 2)⁻¹) *
        (((3 * Real.log (D.card : ℝ)) ^ (min σ 2)⁻¹) *
          (Cfluct *
            (3 : ℝ) ^
              (-(d : ℝ) / 2 *
                (Int.toNat
                  ((((N0 + n : ℕ) : ℤ) -
                    ((N0 + ℓ : ℕ) : ℤ))) : ℝ)) *
            hΓ.thetaHat ^ (2 : ℕ))))
  let c : ℝ :=
    quenchedProbeEnvelopeConst d *
      Real.rpow (3 : ℝ) (-a * (ℓ : ℝ))
  let discount : ℝ := (3 : ℝ) ^ (-t * ((m - n : ℕ) : ℝ))
  let R : ℝ := (3 : ℝ) ^ (-αbad * ((m - q : ℕ) : ℝ))
  let Hshift : ℕ → ℕ → RegCoeffField d → ℝ :=
    fun M N aω => quenchedProbeEnvelope hP hStruct (N0 + M) (N0 + N) aω
  have htail :
      IsBigOWith P (gammaSigma (min σ 2))
        (fun aω => Hshift m n aω - c) A := by
    simpa [Hshift, N0, D, S, A, c] using
      hfirst hP hStruct hΓ hσ_eq hparams hℓn hnm
  have hdisc_pos : 0 < discount := by
    dsimp [discount]
    positivity
  have hbad :
      P.real {aω | R < discount * Hshift m n aω} ≤
        Real.exp (-(s ^ (min σ 2))) := by
    exact
      measureReal_discounted_badPair_le_exp_of_isBigOWith_gammaSigma
        (μ := P) (H := Hshift m n) (A := A) (c := c) (T := T)
        (s := s) (σ := min σ 2) (discount := discount) (R := R)
        htail hs hdisc_pos hthreshold hcenter hscale
  have hsubset :
      badPairEvent Hshift t αbad q m n ⊆
        {aω | R < discount * Hshift m n aω} := by
    intro aω haω
    exact haω.2.2
  exact (measureReal_mono (μ := P) hsubset).trans hbad

/-- Fixed-pair crude bad-event estimate for the concrete envelope. -/
theorem measureReal_crude_badPairEvent_quenchedProbeEnvelope_le_exp
    {d : ℕ} [NeZero d] {σ t αbad : ℝ}
    (hσ_pos : 0 < σ)
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {P : Ch04.RestrictionCoeffLaw d}
        (hP : Ch04.RestrictionLawCarrier P)
        (hStruct : Ch04.RestrictionStructuralLaw P)
        (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct),
        hΓ.sigma = σ → hΓ.params = params →
      ∀ {N m n : ℕ} {s T : ℝ}, n < m → N ≤ m → 1 ≤ s →
        let D : Finset (TriadicCube d) :=
          descendantsAtScale (originCube d ((m : ℕ) : ℤ)) ((n : ℕ) : ℤ)
        let S : Finset (NormalizedProbeIndex d) := Finset.univ
        let A : ℝ :=
          quenchedProbeEnvelopeConst d *
            (((3 * Real.log (S.card : ℝ)) ^ σ⁻¹) *
              (((3 * Real.log (D.card : ℝ)) ^ σ⁻¹) *
                (C * hΓ.thetaHat ^ (2 : ℕ))))
        let discount : ℝ := (3 : ℝ) ^ (-t * ((m - n : ℕ) : ℝ))
        let R : ℝ := (3 : ℝ) ^ (-αbad * ((m - N : ℕ) : ℝ))
        discount * T ≤ R →
        A * s ≤ T →
        P.real
          (badPairEvent (quenchedProbeEnvelope hP hStruct) t αbad N m n) ≤
          Real.exp (-(s ^ σ)) := by
  obtain ⟨C, hC, hcrude⟩ :=
    isBigO_quenchedProbeEnvelope (d := d) hσ_pos params
  refine ⟨C, hC, ?_⟩
  intro P hP hStruct hΓ hσ_eq hparams N m n s T hnm hNm hs
  dsimp only
  intro hthreshold hscale
  let : IsProbabilityMeasure P := hP.isProbability
  let D : Finset (TriadicCube d) :=
    descendantsAtScale (originCube d ((m : ℕ) : ℤ)) ((n : ℕ) : ℤ)
  let S : Finset (NormalizedProbeIndex d) := Finset.univ
  let A : ℝ :=
    quenchedProbeEnvelopeConst d *
      (((3 * Real.log (S.card : ℝ)) ^ σ⁻¹) *
        (((3 * Real.log (D.card : ℝ)) ^ σ⁻¹) *
          (C * hΓ.thetaHat ^ (2 : ℕ))))
  let discount : ℝ := (3 : ℝ) ^ (-t * ((m - n : ℕ) : ℝ))
  let R : ℝ := (3 : ℝ) ^ (-αbad * ((m - N : ℕ) : ℝ))
  have htail :
      IsBigO P (gammaSigma σ)
        (quenchedProbeEnvelope hP hStruct m n) A := by
    simpa [D, S, A] using
      hcrude hP hStruct hΓ hσ_eq hparams hnm
  have hdisc_pos : 0 < discount := by
    dsimp [discount]
    positivity
  have hbad :
      P.real {aω | R < discount * quenchedProbeEnvelope hP hStruct m n aω} ≤
        Real.exp (-(s ^ σ)) := by
    exact
      measureReal_discounted_badPair_le_exp_of_isBigO_gammaSigma
        (μ := P) (H := quenchedProbeEnvelope hP hStruct m n)
        (A := A) (T := T) (s := s) (σ := σ)
        (discount := discount) (R := R)
        htail hs hdisc_pos hthreshold hscale
  have hsubset :
      badPairEvent (quenchedProbeEnvelope hP hStruct) t αbad N m n ⊆
        {aω | R < discount * quenchedProbeEnvelope hP hStruct m n aω} := by
    intro aω haω
    exact haω.2.2
  exact (measureReal_mono (μ := P) hsubset).trans hbad

end

end Section57
end Ch05
end Book
end Homogenization
