/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.FiniteSupTail
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.LocalizedMax
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.ProbeMax

/-! # Localized Max Tail -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

open MeasureTheory
open IndependentSums
open scoped ENNReal

/-!
# Probability-level localized maximum tails

These lemmas are the no-loss replacements for the logarithmically inflated
`O_{\Gamma}` maximum packaging.  The cardinality of the finite family remains
as an explicit probability prefactor.
-/

noncomputable section

/-- Direct finite-union tail for the localized descendant maximum, for one
fixed probe vector. -/
theorem measureReal_localizedLimitNormalizedJMax_sub_const_tail_le_card_mul_exp
    {d : ℕ} [NeZero d] {Pμ : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier Pμ) (hStruct : Ch04.RestrictionStructuralLaw Pμ)
    (hstat : Ch04.RestrictionStationaryLaw Pμ)
    {σ A c lam : ℝ} (hlam : 1 ≤ lam)
    {m n : ℕ} (hnm : n < m) (e : FullBlockVec d)
    (hOrigin :
      IsBigOWith Pμ (gammaSigma σ)
        (fun a =>
          limitNormalizedBlockJObservable hP hStruct
            (originCube d ((n : ℕ) : ℤ)) e a - c) A) :
    let D : Finset (TriadicCube d) :=
      descendantsAtScale (originCube d ((m : ℕ) : ℤ)) ((n : ℕ) : ℤ)
    Pμ.real
        {a | c + A * lam <
          localizedLimitNormalizedJMax hP hStruct m n e a} ≤
      (D.card : ℝ) * Real.exp (-(lam ^ σ)) := by
  intro D
  classical
  let : IsProbabilityMeasure Pμ := hP.isProbability
  have hD : D.Nonempty :=
    descendantsAtScale_originCube_nat_nonempty
      (d := d) (m := m) (n := n) (le_of_lt hnm)
  have hn_nonneg : 0 ≤ ((n : ℕ) : ℤ) := by
    exact_mod_cast Nat.zero_le n
  have hnm_int : ((n : ℕ) : ℤ) ≤ ((m : ℕ) : ℤ) := by
    exact_mod_cast le_of_lt hnm
  have htailR :
      ∀ R ∈ D,
        IsBigOWith Pμ (gammaSigma σ)
          (fun a => limitNormalizedBlockJObservable hP hStruct R e a - c) A := by
    intro R hR
    exact
      isBigOWith_limitNormalizedBlockJObservable_sub_const_of_mem_descendantsAtScale
        hP hStruct hstat hn_nonneg hnm_int
        (R := R) (by simpa [D] using hR) e hOrigin
  have htail :=
    measureReal_finiteSup_sub_const_tail_le_card_mul_exp
      (μ := Pμ) (s := D) (X := fun R a =>
        limitNormalizedBlockJObservable hP hStruct R e a)
      (c := c) (A := A) (lam := lam) (σ := σ) hD hlam htailR
  simpa [localizedLimitNormalizedJMax, D, hD] using htail

/-- Direct finite-union tail for the normalized finite-probe maximum. -/
theorem measureReal_localizedNormalizedProbeJMax_sub_const_tail_le_card_mul_card_mul_exp
    {d : ℕ} [NeZero d] {Pμ : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier Pμ) (hStruct : Ch04.RestrictionStructuralLaw Pμ)
    (hstat : Ch04.RestrictionStationaryLaw Pμ)
    {σ A c lam : ℝ} (hlam : 1 ≤ lam)
    {m n : ℕ} (hnm : n < m)
    (hOrigin :
      ∀ i : NormalizedProbeIndex d,
        IsBigOWith Pμ (gammaSigma σ)
          (fun a =>
            limitNormalizedBlockJObservable hP hStruct
              (originCube d ((n : ℕ) : ℤ)) (normalizedProbeVec i) a - c) A) :
    let D : Finset (TriadicCube d) :=
      descendantsAtScale (originCube d ((m : ℕ) : ℤ)) ((n : ℕ) : ℤ)
    let S : Finset (NormalizedProbeIndex d) := Finset.univ
    Pμ.real
        {a | c + A * lam <
          localizedNormalizedProbeJMax hP hStruct m n a} ≤
      (S.card : ℝ) * ((D.card : ℝ) * Real.exp (-(lam ^ σ))) := by
  intro D S
  classical
  let : IsProbabilityMeasure Pμ := hP.isProbability
  have hS : S.Nonempty := by
    let α : BlockCoord d := Classical.choice inferInstance
    exact ⟨(α, α, NormalizedProbeKind.coord), by simp [S]⟩
  have htailS :
      ∀ i ∈ S,
        Pμ.real
            {a | c + A * lam <
              localizedLimitNormalizedJMax hP hStruct m n
                (normalizedProbeVec i) a} ≤
          (D.card : ℝ) * Real.exp (-(lam ^ σ)) := by
    intro i _hi
    simpa [D] using
      measureReal_localizedLimitNormalizedJMax_sub_const_tail_le_card_mul_exp
        hP hStruct hstat (σ := σ) (A := A) (c := c) (lam := lam)
        hlam hnm (normalizedProbeVec i) (hOrigin i)
  have htail :=
    measureReal_finiteSupTail_le_card_mul
      (μ := Pμ) (s := S)
      (X := fun i a =>
        localizedLimitNormalizedJMax hP hStruct m n (normalizedProbeVec i) a)
      (T := c + A * lam)
      (R := (D.card : ℝ) * Real.exp (-(lam ^ σ))) hS htailS
  simpa only [localizedNormalizedProbeJMax, S, hS, Finset.sup'_apply, Finset.sup'_eq_sup,
    Finset.sup_apply, Pi.sup_apply] using! htail

/-- Direct finite-union tail for the localized descendant maximum, using
symmetric `Γσ` tails. -/
theorem measureReal_localizedLimitNormalizedJMax_tail_le_card_mul_exp_of_isBigO
    {d : ℕ} [NeZero d] {Pμ : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier Pμ) (hStruct : Ch04.RestrictionStructuralLaw Pμ)
    (hstat : Ch04.RestrictionStationaryLaw Pμ)
    {σ A lam : ℝ} (hlam : 1 ≤ lam)
    {m n : ℕ} (hnm : n < m) (e : FullBlockVec d)
    (hOrigin :
      IsBigO Pμ (gammaSigma σ)
        (limitNormalizedBlockJObservable hP hStruct
          (originCube d ((n : ℕ) : ℤ)) e) A) :
    let D : Finset (TriadicCube d) :=
      descendantsAtScale (originCube d ((m : ℕ) : ℤ)) ((n : ℕ) : ℤ)
    Pμ.real
        {a | A * lam <
          localizedLimitNormalizedJMax hP hStruct m n e a} ≤
      (D.card : ℝ) * Real.exp (-(lam ^ σ)) := by
  intro D
  classical
  let : IsProbabilityMeasure Pμ := hP.isProbability
  have hD : D.Nonempty :=
    descendantsAtScale_originCube_nat_nonempty
      (d := d) (m := m) (n := n) (le_of_lt hnm)
  have hn_nonneg : 0 ≤ ((n : ℕ) : ℤ) := by
    exact_mod_cast Nat.zero_le n
  have hnm_int : ((n : ℕ) : ℤ) ≤ ((m : ℕ) : ℤ) := by
    exact_mod_cast le_of_lt hnm
  have htailR :
      ∀ R ∈ D,
        IsBigO Pμ (gammaSigma σ)
          (limitNormalizedBlockJObservable hP hStruct R e) A := by
    intro R hR
    exact
      isBigO_limitNormalizedBlockJObservable_of_mem_descendantsAtScale
        hP hStruct hstat hn_nonneg hnm_int
        (R := R) (by simpa [D] using hR) e hOrigin
  have htail :=
    measureReal_finiteSup_tail_le_card_mul_exp_of_isBigO
      (μ := Pμ) (s := D) (X := fun R a =>
        limitNormalizedBlockJObservable hP hStruct R e a)
      (A := A) (lam := lam) (σ := σ) hD hlam htailR
  simpa [localizedLimitNormalizedJMax, D, hD] using htail

/-- Direct finite-union tail for the normalized finite-probe maximum, using
symmetric `Γσ` tails and no logarithmic maximum packaging. -/
theorem measureReal_localizedNormalizedProbeJMax_tail_le_card_mul_card_mul_exp_of_isBigO
    {d : ℕ} [NeZero d] {Pμ : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier Pμ) (hStruct : Ch04.RestrictionStructuralLaw Pμ)
    (hstat : Ch04.RestrictionStationaryLaw Pμ)
    {σ A lam : ℝ} (hlam : 1 ≤ lam)
    {m n : ℕ} (hnm : n < m)
    (hOrigin :
      ∀ i : NormalizedProbeIndex d,
        IsBigO Pμ (gammaSigma σ)
          (limitNormalizedBlockJObservable hP hStruct
            (originCube d ((n : ℕ) : ℤ)) (normalizedProbeVec i)) A) :
    let D : Finset (TriadicCube d) :=
      descendantsAtScale (originCube d ((m : ℕ) : ℤ)) ((n : ℕ) : ℤ)
    let S : Finset (NormalizedProbeIndex d) := Finset.univ
    Pμ.real
        {a | A * lam <
          localizedNormalizedProbeJMax hP hStruct m n a} ≤
      (S.card : ℝ) * ((D.card : ℝ) * Real.exp (-(lam ^ σ))) := by
  intro D S
  classical
  let : IsProbabilityMeasure Pμ := hP.isProbability
  have hS : S.Nonempty := by
    let α : BlockCoord d := Classical.choice inferInstance
    exact ⟨(α, α, NormalizedProbeKind.coord), by simp [S]⟩
  have htailS :
      ∀ i ∈ S,
        Pμ.real
            {a | A * lam <
              localizedLimitNormalizedJMax hP hStruct m n
                (normalizedProbeVec i) a} ≤
          (D.card : ℝ) * Real.exp (-(lam ^ σ)) := by
    intro i _hi
    simpa [D] using
      measureReal_localizedLimitNormalizedJMax_tail_le_card_mul_exp_of_isBigO
        hP hStruct hstat (σ := σ) (A := A) (lam := lam)
        hlam hnm (normalizedProbeVec i) (hOrigin i)
  have htail :=
    measureReal_finiteSupTail_le_card_mul
      (μ := Pμ) (s := S)
      (X := fun i a =>
        localizedLimitNormalizedJMax hP hStruct m n (normalizedProbeVec i) a)
      (T := A * lam)
      (R := (D.card : ℝ) * Real.exp (-(lam ^ σ))) hS htailS
  simpa only [localizedNormalizedProbeJMax, S, hS, Finset.sup'_apply, Finset.sup'_eq_sup,
    Finset.sup_apply, Pi.sup_apply] using! htail

/-- Localized first-quenched estimate for the finite-probe maximum, kept as a
probability-level finite union bound rather than a logarithmically inflated
`O_{\Gamma}` estimate. -/
theorem measureReal_localizedFirstQuenchedEstimate_normalizedProbeJMax_tail_noLog
    {d : ℕ} [NeZero d] {σ : ℝ}
    (hσ_pos : 0 < σ)
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ Cfluct Centry alpha : ℝ,
      0 < Cfluct ∧ 0 < Centry ∧ 0 < alpha ∧
      ∀ {P : Ch04.RestrictionCoeffLaw d}
        (hP : Ch04.RestrictionLawCarrier P)
        (hStruct : Ch04.RestrictionStructuralLaw P)
        (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct),
        hΓ.sigma = σ → hΓ.params = params →
      ∀ {ell n m : ℕ} {lam : ℝ}, 1 ≤ lam → ell < n → n < m →
        let N0 : ℕ :=
          annealedAlgebraicEntryScale P
            hΓ.toQuantitativeCoarseGrainedEllipticity Centry
        let D : Finset (TriadicCube d) :=
          descendantsAtScale
            (originCube d (((N0 + m : ℕ) : ℤ)))
            (((N0 + n : ℕ) : ℤ))
        let S : Finset (NormalizedProbeIndex d) := Finset.univ
        let tau : ℝ := min σ 2
        let center : ℝ := Real.rpow (3 : ℝ) (-alpha * (ell : ℝ))
        let scale : ℝ :=
          Cfluct *
            (3 : ℝ) ^
              (-(d : ℝ) / 2 *
                (Int.toNat
                  ((((N0 + n : ℕ) : ℤ) -
                    ((N0 + ell : ℕ) : ℤ))) : ℝ)) *
            hΓ.thetaHat ^ (2 : ℕ)
        P.real
            {aω | center + scale * lam <
              localizedNormalizedProbeJMax hP hStruct (N0 + m) (N0 + n) aω} ≤
          (S.card : ℝ) * ((D.card : ℝ) * Real.exp (-(lam ^ tau))) := by
  obtain ⟨Cfluct, Centry, alpha, hCfluct, hCentry, halpha, hfirst⟩ :=
    firstQuenchedEstimate_limitNormalized (d := d) hσ_pos params
  refine ⟨Cfluct, Centry, alpha, hCfluct, hCentry, halpha, ?_⟩
  intro P hP hStruct hΓ hσ_eq hparams ell n m lam hlam helln hnm
  classical
  let : IsProbabilityMeasure P := hP.isProbability
  let N0 : ℕ :=
    annealedAlgebraicEntryScale P
      hΓ.toQuantitativeCoarseGrainedEllipticity Centry
  let D : Finset (TriadicCube d) :=
    descendantsAtScale
      (originCube d (((N0 + m : ℕ) : ℤ)))
      (((N0 + n : ℕ) : ℤ))
  let S : Finset (NormalizedProbeIndex d) := Finset.univ
  let tau : ℝ := min σ 2
  let center : ℝ := Real.rpow (3 : ℝ) (-alpha * (ell : ℝ))
  let scale : ℝ :=
    Cfluct *
      (3 : ℝ) ^
        (-(d : ℝ) / 2 *
          (Int.toNat
            ((((N0 + n : ℕ) : ℤ) -
              ((N0 + ell : ℕ) : ℤ))) : ℝ)) *
      hΓ.thetaHat ^ (2 : ℕ)
  have hOrigin :
      ∀ i : NormalizedProbeIndex d,
        IsBigOWith P (gammaSigma tau)
          (fun aω =>
            limitNormalizedBlockJObservable hP hStruct
              (originCube d (((N0 + n : ℕ) : ℤ)))
              (normalizedProbeVec i) aω - center)
          scale := by
    intro i
    have hi_norm : dotProduct (normalizedProbeVec i) (normalizedProbeVec i) ≤ 1 :=
      normalizedProbeVec_dotProduct_self_le_one i
    simpa [N0, tau, center, scale] using
      hfirst hP hStruct hΓ hσ_eq hparams
        (normalizedProbeVec i) hi_norm (n := ell) (m := n) helln
  simpa [N0, D, S, tau, center, scale] using
    measureReal_localizedNormalizedProbeJMax_sub_const_tail_le_card_mul_card_mul_exp
      hP hStruct hStruct.stationary
      (σ := tau) (A := scale) (c := center) (lam := lam)
      hlam (m := N0 + m) (n := N0 + n)
      (Nat.add_lt_add_left hnm N0) hOrigin

/-- Uniform-in-`σ` version of
`measureReal_localizedFirstQuenchedEstimate_normalizedProbeJMax_tail_noLog`. -/
theorem measureReal_localizedFirstQuenchedEstimate_normalizedProbeJMax_tail_noLog_uniformAnnealedExponent
    {d : ℕ} [NeZero d]
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ Centry a : ℝ, 0 < Centry ∧ 0 < a ∧
      ∀ {σ : ℝ}, 0 < σ →
        ∃ Cfluct : ℝ, 0 < Cfluct ∧
          ∀ {P : Ch04.RestrictionCoeffLaw d}
            (hP : Ch04.RestrictionLawCarrier P)
            (hStruct : Ch04.RestrictionStructuralLaw P)
            (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct),
            hΓ.sigma = σ → hΓ.params = params →
          ∀ {ell n m : ℕ} {lam : ℝ}, 1 ≤ lam → ell < n → n < m →
            let N0 : ℕ :=
              annealedAlgebraicEntryScale P
                hΓ.toQuantitativeCoarseGrainedEllipticity Centry
            let D : Finset (TriadicCube d) :=
              descendantsAtScale
                (originCube d (((N0 + m : ℕ) : ℤ)))
                (((N0 + n : ℕ) : ℤ))
            let S : Finset (NormalizedProbeIndex d) := Finset.univ
            let tau : ℝ := min σ 2
            let center : ℝ := Real.rpow (3 : ℝ) (-a * (ell : ℝ))
            let scale : ℝ :=
              Cfluct *
                (3 : ℝ) ^
                  (-(d : ℝ) / 2 *
                    (Int.toNat
                      ((((N0 + n : ℕ) : ℤ) -
                        ((N0 + ell : ℕ) : ℤ))) : ℝ)) *
                hΓ.thetaHat ^ (2 : ℕ)
            P.real
                {aω | center + scale * lam <
                  localizedNormalizedProbeJMax hP hStruct
                    (N0 + m) (N0 + n) aω} ≤
              (S.card : ℝ) * ((D.card : ℝ) * Real.exp (-(lam ^ tau))) := by
  obtain ⟨Centry, a, hCentry, ha, hfirstBase⟩ :=
    firstQuenchedEstimate_limitNormalized_uniformAnnealedExponent
      (d := d) params
  refine ⟨Centry, a, hCentry, ha, ?_⟩
  intro σ hσ_pos
  obtain ⟨Cfluct, hCfluct, hfirst⟩ := hfirstBase hσ_pos
  refine ⟨Cfluct, hCfluct, ?_⟩
  intro P hP hStruct hΓ hσ_eq hparams ell n m lam hlam helln hnm
  classical
  let : IsProbabilityMeasure P := hP.isProbability
  let N0 : ℕ :=
    annealedAlgebraicEntryScale P
      hΓ.toQuantitativeCoarseGrainedEllipticity Centry
  let D : Finset (TriadicCube d) :=
    descendantsAtScale
      (originCube d (((N0 + m : ℕ) : ℤ)))
      (((N0 + n : ℕ) : ℤ))
  let S : Finset (NormalizedProbeIndex d) := Finset.univ
  let tau : ℝ := min σ 2
  let center : ℝ := Real.rpow (3 : ℝ) (-a * (ell : ℝ))
  let scale : ℝ :=
    Cfluct *
      (3 : ℝ) ^
        (-(d : ℝ) / 2 *
          (Int.toNat
            ((((N0 + n : ℕ) : ℤ) -
              ((N0 + ell : ℕ) : ℤ))) : ℝ)) *
      hΓ.thetaHat ^ (2 : ℕ)
  have hOrigin :
      ∀ i : NormalizedProbeIndex d,
        IsBigOWith P (gammaSigma tau)
          (fun aω =>
            limitNormalizedBlockJObservable hP hStruct
              (originCube d (((N0 + n : ℕ) : ℤ)))
              (normalizedProbeVec i) aω - center)
          scale := by
    intro i
    have hi_norm : dotProduct (normalizedProbeVec i) (normalizedProbeVec i) ≤ 1 :=
      normalizedProbeVec_dotProduct_self_le_one i
    simpa [N0, tau, center, scale] using
      hfirst hP hStruct hΓ hσ_eq hparams
        (normalizedProbeVec i) hi_norm (n := ell) (m := n) helln
  simpa [N0, D, S, tau, center, scale] using
    measureReal_localizedNormalizedProbeJMax_sub_const_tail_le_card_mul_card_mul_exp
      hP hStruct hStruct.stationary
      (σ := tau) (A := scale) (c := center) (lam := lam)
      hlam (m := N0 + m) (n := N0 + n)
      (Nat.add_lt_add_left hnm N0) hOrigin

end

end Section57
end Ch05
end Book
end Homogenization
