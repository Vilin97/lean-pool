/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.EntryScaleCompression
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.UniformEllipticityEndpoint

/-! # First Quenched Estimate Compressed -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

open MeasureTheory
open IndependentSums

/-!
# Note-facing compressed entry scale for the first quenched estimate

The core first quenched estimate is proved with the annealed algebraic entry
scale associated to the Chapter 5 iteration.  This file repackages that theorem
with the manuscript-scale entry
`ceil(C log^2(2 + thetaHat))`, using the deterministic compression lemma from
`EntryScaleCompression`.
-/

noncomputable section

/-- Note-facing version of Corollary `c.first.quenched.estimate` with no
exposed internal `xi` and with the entry scale compressed to one manuscript
ceiling `ceil(C log^2(2 + thetaHat))`.

The algebraic exponent is selected before the finite moment exponent `sigma`.
For each `sigma`, the entry-scale constant and fluctuation constant are then
selected before the law. -/
theorem firstQuenchedEstimate_limitNormalized_logSqEntry_noXi
    {d : ℕ} [NeZero d]
    (params : GammaCoarseGrainedEllipticityParams d) :
    ∃ a : ℝ, 0 < a ∧
      ∀ {σ : ℝ}, 0 < σ →
        ∃ CentryScale Cfluct : ℝ, 0 < CentryScale ∧ 0 < Cfluct ∧
          ∀ {Pμ : Ch04.RestrictionCoeffLaw d}
            (hPμ : Ch04.RestrictionLawCarrier Pμ)
            (hStruct : Ch04.RestrictionStructuralLaw Pμ)
            (hΓ : GammaSigmaCoarseGrainedEllipticityNoXi Pμ hPμ hStruct),
            hΓ.sigma = σ → hΓ.params = params →
          ∀ (e : FullBlockVec d), dotProduct e e ≤ 1 →
          ∀ {n m : ℕ}, n < m →
            let N0 : ℕ :=
              Nat.ceil (CentryScale *
                (Real.log (2 + hΓ.thetaHat)) ^ (2 : ℕ))
            IsBigOWith Pμ (gammaSigma (min σ 2))
              (fun aω =>
                limitNormalizedBlockJObservable hPμ hStruct
                    (originCube d ((N0 + m : ℕ) : ℤ)) e aω -
                  Real.rpow (3 : ℝ) (-a * (n : ℝ)))
              (Cfluct *
                (3 : ℝ) ^
                  (-(d : ℝ) / 2 *
                    (Int.toNat
                      (((N0 + m : ℕ) : ℤ) -
                        ((N0 + n : ℕ) : ℤ)) : ℝ)) *
                hΓ.thetaHat ^ (2 : ℕ)) := by
  obtain ⟨Centry, a, hCentry_pos, ha_pos, hfinite⟩ :=
    firstQuenchedEstimate_limitNormalized_uniformAnnealedExponent_noXi
      (d := d) params
  refine ⟨a, ha_pos, ?_⟩
  intro σ hσ
  obtain ⟨CentryScale, hCentryScale_pos, hscale⟩ :=
    exists_entryScale_le_natCeil_logSq
      (d := d) hσ hCentry_pos params.toQuantitativeParams
  obtain ⟨Cfluct, hCfluct_pos, hfluct⟩ := hfinite hσ
  refine ⟨CentryScale, Cfluct, hCentryScale_pos, hCfluct_pos, ?_⟩
  intro Pμ hPμ hStruct hΓ hσ_eq hparams e he_norm n m hnm
  let : IsProbabilityMeasure Pμ := hPμ.isProbability
  let hΓold : GammaSigmaCoarseGrainedEllipticity Pμ hPμ hStruct :=
    hΓ.withInternalXi
  let Nold : ℕ :=
    annealedAlgebraicEntryScale Pμ
      hΓold.toQuantitativeCoarseGrainedEllipticity Centry
  let Nnew : ℕ :=
    Nat.ceil (CentryScale *
      (Real.log (2 + hΓ.thetaHat)) ^ (2 : ℕ))
  let Δ : ℕ := Nnew - Nold
  have hσ_old : hΓold.sigma = σ := by
    simpa [hΓold] using hσ_eq
  have hparams_old :
      hΓold.params = params.toQuantitativeParams := by
    dsimp [hΓold, GammaSigmaCoarseGrainedEllipticityNoXi.withInternalXi]
    rw [hparams]
  have hNold_le_new : Nold ≤ Nnew := by
    simpa [Nold, Nnew, hΓold] using
      hscale hPμ hStruct hΓold hσ_old hparams_old
  have hNold_add_delta : Nold + Δ = Nnew :=
    Nat.add_sub_of_le hNold_le_new
  have hNm : Nold + (Δ + m) = Nnew + m := by
    omega
  have hNn : Nold + (Δ + n) = Nnew + n := by
    omega
  have hNm_comm : m + (Nold + Δ) = m + Nnew := by
    omega
  have hNn_comm : n + (Nold + Δ) = n + Nnew := by
    omega
  have hmn_shift : Δ + n < Δ + m :=
    Nat.add_lt_add_left hnm Δ
  have hold :=
    hfluct hPμ hStruct hΓ hσ_eq hparams e he_norm
      (n := Δ + n) (m := Δ + m) hmn_shift
  have hold' :
      IsBigOWith Pμ (gammaSigma (min σ 2))
        (fun aω =>
          limitNormalizedBlockJObservable hPμ hStruct
              (originCube d ((m + Nnew : ℕ) : ℤ)) e aω -
            Real.rpow (3 : ℝ) (-a * ((Δ + n : ℕ) : ℝ)))
        (Cfluct *
          (3 : ℝ) ^
            (-(d : ℝ) / 2 *
              (Int.toNat
                (((m + Nnew : ℕ) : ℤ) -
                  ((n + Nnew : ℕ) : ℤ)) : ℝ)) *
          hΓ.thetaHat ^ (2 : ℕ)) := by
    simpa [hΓold, Nold, Nnew, Δ, hNold_add_delta, hNm, hNn, hNm_comm,
      hNn_comm, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hold
  have hn_le_shift : (n : ℝ) ≤ ((Δ + n : ℕ) : ℝ) := by
    have hn_nat : n ≤ Δ + n := by omega
    exact_mod_cast hn_nat
  have hcenter_le :
      Real.rpow (3 : ℝ) (-a * ((Δ + n : ℕ) : ℝ)) ≤
        Real.rpow (3 : ℝ) (-a * (n : ℝ)) := by
    refine Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 3) ?_
    have hmul :
        a * (n : ℝ) ≤ a * ((Δ + n : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left hn_le_shift ha_pos.le
    nlinarith
  have htarget :
      IsBigOWith Pμ (gammaSigma (min σ 2))
        (fun aω =>
          limitNormalizedBlockJObservable hPμ hStruct
              (originCube d ((m + Nnew : ℕ) : ℤ)) e aω -
            Real.rpow (3 : ℝ) (-a * (n : ℝ)))
        (Cfluct *
          (3 : ℝ) ^
            (-(d : ℝ) / 2 *
              (Int.toNat
                (((m + Nnew : ℕ) : ℤ) -
                  ((n + Nnew : ℕ) : ℤ)) : ℝ)) *
          hΓ.thetaHat ^ (2 : ℕ)) := by
    refine hold'.of_le ?_
    intro aω
    dsimp
    exact sub_le_sub_left hcenter_le _
  simpa [Nnew, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htarget

/-- Endpoint (`sigma = infinity`) version of
`firstQuenchedEstimate_limitNormalized_logSqEntry_noXi`.

The endpoint assumption is converted internally to the finite statement at
`sigma = 2`, so the displayed tail class is `Gamma_2`. -/
theorem firstQuenchedEstimate_limitNormalized_logSqEntry_noXi_infinity
    {d : ℕ} [NeZero d]
    (params : GammaCoarseGrainedEllipticityParams d) :
    ∃ a : ℝ, 0 < a ∧
      ∃ CentryScale Cfluct : ℝ, 0 < CentryScale ∧ 0 < Cfluct ∧
        ∀ {Pμ : Ch04.RestrictionCoeffLaw d}
          (hPμ : Ch04.RestrictionLawCarrier Pμ)
          (hStruct : Ch04.RestrictionStructuralLaw Pμ)
          (hInf : GammaInfinityCoarseGrainedEllipticityNoXi Pμ hPμ hStruct),
          hInf.params = params →
        ∀ (e : FullBlockVec d), dotProduct e e ≤ 1 →
        ∀ {n m : ℕ}, n < m →
          let N0 : ℕ :=
            Nat.ceil (CentryScale *
              (Real.log (2 + hInf.thetaHat)) ^ (2 : ℕ))
          IsBigOWith Pμ (gammaSigma 2)
            (fun aω =>
              limitNormalizedBlockJObservable hPμ hStruct
                  (originCube d ((N0 + m : ℕ) : ℤ)) e aω -
                Real.rpow (3 : ℝ) (-a * (n : ℝ)))
            (Cfluct *
              (3 : ℝ) ^
                (-(d : ℝ) / 2 *
                  (Int.toNat
                    (((N0 + m : ℕ) : ℤ) -
                      ((N0 + n : ℕ) : ℤ)) : ℝ)) *
              hInf.thetaHat ^ (2 : ℕ)) := by
  obtain ⟨a, ha, hfinite⟩ :=
    firstQuenchedEstimate_limitNormalized_logSqEntry_noXi
      (d := d) params
  obtain ⟨CentryScale, Cfluct, hCentryScale, hCfluct, hfluct⟩ :=
    hfinite (σ := (2 : ℝ)) (by norm_num : (0 : ℝ) < 2)
  refine ⟨a, ha, CentryScale, Cfluct, hCentryScale, hCfluct, ?_⟩
  intro Pμ hPμ hStruct hInf hparams e he_norm n m hnm
  let hΓ2 : GammaSigmaCoarseGrainedEllipticityNoXi Pμ hPμ hStruct :=
    hInf.toGammaSigmaNoXi 2 (by norm_num : (0 : ℝ) < 2)
  have hσ2 : hΓ2.sigma = (2 : ℝ) := rfl
  have hparams2 : hΓ2.params = params := by
    simpa [hΓ2, GammaInfinityCoarseGrainedEllipticityNoXi.toGammaSigmaNoXi]
      using hparams
  have h :=
    hfluct hPμ hStruct hΓ2 hσ2 hparams2 e he_norm hnm
  simpa [hΓ2, GammaInfinityCoarseGrainedEllipticityNoXi.toGammaSigmaNoXi]
    using h

end

end Section57
end Ch05
end Book
end Homogenization
