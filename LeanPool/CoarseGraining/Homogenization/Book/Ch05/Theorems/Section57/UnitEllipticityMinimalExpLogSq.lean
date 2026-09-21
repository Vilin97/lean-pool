/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.LocalizedUnitEllipticityMinimal
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.AbsoluteScaleCompression

/-! # Unit Ellipticity Minimal Exp Log Sq -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

open MeasureTheory
open IndependentSums
open scoped ENNReal

/-!
# Compressed unit-ellipticity minimal scale

This file gives the localized unit-ellipticity stopping scale the same
manuscript-scale stochastic envelope as the quenched `J` stopping scale:
`exp(C log^2(2 + thetaHat))`.
-/

noncomputable section

/-- The localized unit-ellipticity minimal scale with the note-facing
`exp(C log^2(2 + thetaHat))` stochastic size. -/
theorem exists_unitEllipticityMinimalScale_interpolated_expLogSq
    {d : ℕ} [NeZero d] {σ : ℝ} (hσ_pos : 0 < σ)
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∀ {t α : ℝ},
      let η : ℝ := finiteQuenchedTailExponent d σ t
      0 < t →
      0 ≤ α →
      α < t →
      ∃ Cscale : ℝ, 0 < Cscale ∧
        ∀ {P : Ch04.RestrictionCoeffLaw d}
          (hP : Ch04.RestrictionLawCarrier P)
          (hStruct : Ch04.RestrictionStructuralLaw P)
          (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct),
          hΓ.sigma = σ → hΓ.params = params →
          ∃ X : RegCoeffField d → ℝ,
            IsBigO P (gammaSigma η) X
              (Real.exp
                (Cscale * (Real.log (2 + hΓ.thetaHat)) ^ (2 : ℕ))) ∧
            (∀ aω, 1 ≤ X aω) ∧
              ∀ᵐ aω ∂P,
                ∀ {m : ℕ},
                  X aω ≤ (3 : ℝ) ^ m →
                  localizedLimitWeightedUnitEllipticitySup
                      hP hStruct hΓ.params m aω ≤
                    (Real.rpow (3 : ℝ) (t * (m : ℝ)) *
                      Real.sqrt (((3 : ℝ) ^ m / X aω) ^ (-α))) ^ (2 : ℕ) := by
  intro t α η ht hα_nonneg hαt
  classical
  let w : ℝ := ((3 ^ d : ℕ) : ℝ)
  let W : ℝ := max 1 w
  let ρunit : ℝ := (3 : ℝ) ^ (2 * t - α)
  let Kunit : ℝ := weightedGeometricExpKernelConst w (ρunit ^ σ)
  let M : ℝ := max 1 (max 0 Kunit)
  let ρgap : ℝ := (3 : ℝ) ^ η
  let C₀ : ℝ := 2 + Real.log W
  let G : ℝ :=
    Ch04.gammaMomentConst σ * (params.xi : ℝ) ^ σ⁻¹
  let A : ℝ := (max 1 G) ^ (σ / η)
  let p : ℝ := 2 * (σ / η)
  have hη_pos : 0 < η := by
    simpa [η] using finiteQuenchedTailExponent_pos
      (d := d) (σ := σ) (t := t) hσ_pos ht
  obtain ⟨R, _hR, htail_abs⟩ :=
    exists_quantitative_threshold_unitEllipticityBadTail_le_interpolated_tail
      (d := d) (σ := σ) hσ_pos
      (t := t) (α := α) ht hα_nonneg hαt
  have hA_pos : 0 < A := by
    dsimp [A]
    exact Real.rpow_pos_of_pos
      (lt_of_lt_of_le zero_lt_one (le_max_left 1 G)) _
  have hp_nonneg : 0 ≤ p := by
    dsimp [p]
    positivity
  obtain ⟨Cscale, hCscale_pos, hcompress⟩ :=
    explicit_threshold_prefactor_le_exp_logSq_of_Blead_le_poly
      (η := η) (A := A) (p := p) (M := M) (R := R) (Qcut := 0)
      hη_pos hA_pos hp_nonneg
  refine ⟨Cscale, hCscale_pos, ?_⟩
  intro P hP hStruct hΓ hσ_eq hparams
  let : IsProbabilityMeasure P := hP.isProbability
  let scale : ℝ := thetaAtScale hP hStruct (0 : ℤ) * hΓ.thetaHat
  let Blead : ℝ := smallBottomTailDenominator scale η σ
  let Btail : ℝ := 2 * Blead
  let B : ℝ := max 1 Btail
  let cgap : ℝ := Blead ^ (-η) - Btail ^ (-η)
  let Qpref : ℕ :=
    max (Nat.ceil (max 0 (Real.log M)))
      (max R (Nat.ceil ((2 * max 0 (-(Real.log cgap))) /
        Real.log ρgap)))
  let Qlead : ℕ := Nat.ceil (Real.log Blead / Real.log 3)
  let Q : ℕ := max Qpref Qlead
  let Bad : ℕ → Set (RegCoeffField d) :=
    unitEllipticityBadScaleEvent hP hStruct hΓ.params t α
  let X : RegCoeffField d → ℝ := quenchedMinimalScale Q Bad
  let C : ℝ := 3 * ((3 : ℝ) ^ Q) * B
  have hθ_one : 1 ≤ thetaAtScale hP hStruct (0 : ℤ) := by
    simpa using
      Section54.GoodScale.one_le_thetaAtScale_of_P4
        hP hStruct hΓ.toQuantitativeCoarseGrainedEllipticity 0
  have hscale_pos : 0 < scale := by
    dsimp [scale]
    exact mul_pos (lt_of_lt_of_le zero_lt_one hθ_one) hΓ.thetaHat_pos
  have hBlead_pos : 0 < Blead := by
    simpa [Blead] using
      smallBottomTailDenominator_pos
        (scale := scale) (η := η) (σ := σ)
  have hBtail_pos : 0 < Btail := by
    dsimp [Btail]
    positivity
  have hB : 1 ≤ B := by
    dsimp [B]
    exact le_max_left 1 Btail
  have hB_pos : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hC_pos : 0 < C := by
    dsimp [C]
    positivity
  have htail :
      ∀ N : ℕ, Q ≤ N →
        P.real (badTailEvent Bad N) ≤
          Real.exp
            (-(((Real.rpow (3 : ℝ) ((N - Q : ℕ) : ℝ)) / B) ^ η)) := by
    intro N hQN
    have hN_abs :
        P.real
            (badTailEvent
              (unitEllipticityBadScaleEvent hP hStruct hΓ.params t α)
              N) ≤
          Real.exp (-(((3 : ℝ) ^ (N : ℝ) / Btail) ^ η)) := by
      simpa [η, w, W, ρunit, Kunit, M, ρgap, C₀,
        scale, Blead, Btail, cgap, Qpref, Qlead, Q] using
        htail_abs hP hStruct hΓ hσ_eq N hQN
    have hcompare :
        Real.exp (-(((3 : ℝ) ^ (N : ℝ) / Btail) ^ η)) ≤
          Real.exp
            (-(((Real.rpow (3 : ℝ) ((N - Q : ℕ) : ℝ)) / B) ^ η)) := by
      simpa [B] using
        exp_neg_rpow_three_nat_div_le_exp_neg_shifted_max_one
          (Q := Q) (N := N) (B := Btail) (η := η)
          hBtail_pos hη_pos
    exact hN_abs.trans hcompare
  have hsmall :
      ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, Q ≤ N ∧ P.real (badTailEvent Bad N) ≤ ε := by
    intro ε hε
    obtain ⟨j, hj⟩ :=
      exists_exp_neg_rpow_three_div_le
        (B := B) (η := η) (ε := ε) hB_pos hη_pos hε
    refine ⟨Q + j, Nat.le_add_right Q j, ?_⟩
    have htail_j := htail (Q + j) (Nat.le_add_right Q j)
    exact htail_j.trans (by simpa [Nat.add_sub_cancel_left] using hj)
  have hgoodAE : ∀ᵐ aω ∂P, hasGoodTailFrom Q Bad aω := by
    exact ae_hasGoodTailFrom
      (μ := P) (N0 := Q) (Bad := Bad) hsmall
  have hO_raw :
      IsBigO P (gammaSigma η) X C := by
    simpa [X, C] using
      isBigO_quenchedMinimalScale_of_badTailEvent_bound
        (μ := P) (N0 := Q) (Bad := Bad) (B := B) (η := η)
        hη_pos hB htail
  have hG_pos : 0 < G := by
    dsimp [G]
    exact mul_pos
      (IndependentSums.gammaMomentConst_pos hσ_pos)
      (Real.rpow_pos_of_pos (by exact_mod_cast params.xi_pos) _)
  have htheta0_le :
      thetaAtScale hP hStruct (0 : ℤ) ≤ G * hΓ.thetaHat := by
    have h := hΓ.thetaAtScale_zero_le_gammaMomentScale
    simpa [G, hσ_eq, hparams] using h
  have hscale_le :
      scale ≤ G * hΓ.thetaHat ^ (2 : ℕ) := by
    dsimp [scale]
    calc
      thetaAtScale hP hStruct (0 : ℤ) * hΓ.thetaHat
          ≤ (G * hΓ.thetaHat) * hΓ.thetaHat :=
            mul_le_mul_of_nonneg_right htheta0_le hΓ.thetaHat_pos.le
      _ = G * hΓ.thetaHat ^ (2 : ℕ) := by ring
  have hBlead_one : 1 ≤ Blead := by
    simpa [Blead] using
      one_le_smallBottomTailDenominator
        (scale := scale) (η := η) (σ := σ) hη_pos hσ_pos.le
  have hBlead_poly :
      Blead ≤ A * (max 1 hΓ.thetaHat) ^ p := by
    have hmax_scale :
        max 1 scale ≤ max 1 (G * hΓ.thetaHat ^ (2 : ℕ)) := by
      refine max_le ?_ ?_
      · exact le_max_left 1 (G * hΓ.thetaHat ^ (2 : ℕ))
      · exact hscale_le.trans
          (le_max_right 1 (G * hΓ.thetaHat ^ (2 : ℕ)))
    have hraw :
        (max 1 scale) ^ (σ / η) ≤
          (max 1 (G * hΓ.thetaHat ^ (2 : ℕ))) ^ (σ / η) := by
      exact Real.rpow_le_rpow
        (le_trans zero_le_one (le_max_left 1 scale)) hmax_scale
        (by positivity)
    have hpoly :
        (max 1 (G * hΓ.thetaHat ^ (2 : ℕ))) ^ (σ / η) ≤
          A * (max 1 hΓ.thetaHat) ^ p := by
      simpa [A, p] using
        rpow_max_one_mul_sq_le_const_mul_rpow
          (A := G) (θ := hΓ.thetaHat) (r := σ / η)
          hΓ.thetaHat_pos.le (by positivity)
    simpa [Blead, smallBottomTailDenominator] using hraw.trans hpoly
  have hscaleC :
      C ≤
        Real.exp
          (Cscale * (Real.log (2 + hΓ.thetaHat)) ^ (2 : ℕ)) := by
    have h :=
      hcompress hΓ.thetaHat hΓ.thetaHat_pos.le Blead hBlead_one
        hBlead_poly
    simpa [C, B, Btail, cgap, ρgap, Qpref, Qlead, Q] using h
  have hO :
      IsBigO P (gammaSigma η) X
        (Real.exp
          (Cscale * (Real.log (2 + hΓ.thetaHat)) ^ (2 : ℕ))) :=
    IsBigO.mono_scale (μ := P) (Ψ := gammaSigma η) hO_raw hscaleC
  have hXone : ∀ aω, 1 ≤ X aω := by
    intro aω
    simpa [X] using one_le_quenchedMinimalScale Q Bad aω
  have hpoint :
      ∀ᵐ aω ∂P,
        ∀ {m : ℕ},
          X aω ≤ (3 : ℝ) ^ m →
          localizedLimitWeightedUnitEllipticitySup
              hP hStruct hΓ.params m aω ≤
            (Real.rpow (3 : ℝ) (t * (m : ℝ)) *
              Real.sqrt (((3 : ℝ) ^ m / X aω) ^ (-α))) ^ (2 : ℕ) := by
    filter_upwards [hgoodAE] with aω hgood
    intro m hm
    simpa [Bad, X] using
      localizedLimitWeightedUnitEllipticitySup_le_above_quenchedMinimalScale
        hP hStruct hΓ.params (N0 := Q) (m := m) (t := t) (α := α)
        (a := aω) hgood (by simpa [Bad, X] using hm)
  exact ⟨X, hO, hXone, hpoint⟩

end

end Section57
end Ch05
end Book
end Homogenization
