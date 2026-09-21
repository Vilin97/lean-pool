/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.ScaleGeometry
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleEntrySplit
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadPairNoLog
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleComponentSummation

/-! # Small Bottom Band -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

open MeasureTheory

/-!
# The small-bottom band below the annealed entry scale

This file starts the quantitative treatment of the finite band `n < N0` in
the final quenched theorem.  The first lemma is the concrete crude fixed-pair
row estimate in absolute variables.
-/

noncomputable section

private theorem pow_le_pow_add_of_one_le {a : ℝ} (ha : 1 ≤ a) (m n : ℕ) :
    a ^ m ≤ a ^ (m + n) := by
  exact pow_le_pow_right₀ ha (Nat.le_add_right m n)

/-- Reindex the small-bottom event into rows above the bad scale and the
finite set of bottom levels below `Nentry`. -/
theorem smallBottomBadScaleEvent_subset_rows
    {Ω : Type*} {H : ℕ → ℕ → Ω → ℝ} {Nentry q : ℕ} {t α : ℝ} :
    smallBottomBadScaleEvent H Nentry t α (Nentry + q) ⊆
      ⋃ r : ℕ, ⋃ j : Fin Nentry,
        badPairEvent H t α (Nentry + q) (Nentry + q + r) j.val := by
  intro ω hω
  rcases hω with ⟨m, n, hn_entry, hnm, hNm, hbad⟩
  let r : ℕ := m - (Nentry + q)
  let j : Fin Nentry := ⟨n, hn_entry⟩
  refine Set.mem_iUnion.2 ⟨r, Set.mem_iUnion.2 ⟨j, ?_⟩⟩
  have hm : Nentry + q + r = m := by
    dsimp [r]
    exact Nat.add_sub_of_le hNm
  simpa [badPairEvent, hm, j] using
    (⟨hnm, hNm, hbad⟩ :
      ω ∈ badPairEvent H t α (Nentry + q) m n)

/-- Concrete crude fixed-pair row estimate for pairs whose bottom scale is
below the entry scale.  Here `q` is the distance from the entry scale to the
bad scale and `r` is the distance above the bad scale. -/
theorem measureReal_smallBottomPairEvent_quenchedProbeEnvelope_le_weighted_row
    {d : ℕ} [NeZero d] {σ : ℝ}
    (hσ_pos : 0 < σ)
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ Ccrude : ℝ, 0 < Ccrude ∧
      ∀ {t α : ℝ},
      ∀ {P : Ch04.RestrictionCoeffLaw d}
        (hP : Ch04.RestrictionLawCarrier P)
        (hStruct : Ch04.RestrictionStructuralLaw P)
        (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct),
        hΓ.sigma = σ → hΓ.params = params →
      ∀ {Nentry q r n : ℕ},
        let K : ℝ := quenchedProbeEnvelopeConst d
        let H : ℕ → ℕ → RegCoeffField d → ℝ :=
          quenchedProbeEnvelope hP hStruct
        let S : Finset (NormalizedProbeIndex d) := Finset.univ
        let w : ℝ := ((3 ^ d : ℕ) : ℝ)
        let scale : ℝ := K * (Ccrude * hΓ.thetaHat ^ (2 : ℕ))
        let A : ℝ := (3 : ℝ) ^ (t * (q : ℝ)) / scale
        let ρ : ℝ := (3 : ℝ) ^ (t - α)
        let N : ℕ := Nentry + q
        let m : ℕ := N + r
        0 < t →
        α < t →
        n < Nentry →
        1 ≤ A →
        P.real (badPairEvent H t α N m n) ≤
          ((S.card : ℝ) * w ^ Nentry * w ^ q) *
            (w ^ r * Real.exp (-((A * ρ ^ r) ^ σ))) := by
  obtain ⟨Ccrude, hCcrude, hpair⟩ :=
    measureReal_shiftedCrude_badPairEvent_quenchedProbeEnvelope_le_card_mul_card_mul_exp_noLog
      (d := d) (σ := σ) hσ_pos params
  refine ⟨Ccrude, hCcrude, ?_⟩
  intro t α P hP hStruct hΓ hσ_eq hparams Nentry q r n
  dsimp only
  intro ht hαt hn_entry hA_one
  classical
  let : IsProbabilityMeasure P := hP.isProbability
  let K : ℝ := quenchedProbeEnvelopeConst d
  let H : ℕ → ℕ → RegCoeffField d → ℝ := quenchedProbeEnvelope hP hStruct
  let S : Finset (NormalizedProbeIndex d) := Finset.univ
  let w : ℝ := ((3 ^ d : ℕ) : ℝ)
  let scale : ℝ := K * (Ccrude * hΓ.thetaHat ^ (2 : ℕ))
  let A : ℝ := (3 : ℝ) ^ (t * (q : ℝ)) / scale
  let ρ : ℝ := (3 : ℝ) ^ (t - α)
  let N : ℕ := Nentry + q
  let m : ℕ := N + r
  let x : ℝ := α * ((m - N : ℕ) : ℝ) - t * ((m - n : ℕ) : ℝ)
  let D : Finset (TriadicCube d) :=
    descendantsAtScale (originCube d ((m : ℕ) : ℤ)) ((n : ℕ) : ℤ)
  let T : ℝ := Real.rpow (3 : ℝ) (-x)
  let lam : ℝ := T / scale
  have hK_pos : 0 < K := by
    simpa [K] using quenchedProbeEnvelopeConst_pos (d := d)
  have hscale_pos : 0 < scale := by
    dsimp [scale]
    exact mul_pos hK_pos (mul_pos hCcrude (pow_pos hΓ.thetaHat_pos 2))
  have hρ_gt : 1 < ρ := by
    have hgap : 0 < t - α := sub_pos.mpr hαt
    dsimp [ρ]
    calc
      (1 : ℝ) = (3 : ℝ) ^ (0 : ℝ) := by simp
      _ < (3 : ℝ) ^ (t - α) :=
        Real.rpow_lt_rpow_of_exponent_lt
          (by norm_num : (1 : ℝ) < 3) hgap
  have hρ_pos : 0 < ρ := lt_trans zero_lt_one hρ_gt
  have hA_pos : 0 < A := lt_of_lt_of_le zero_lt_one hA_one
  have hAρ_nonneg : 0 ≤ A * ρ ^ r := by positivity
  have hN_le_m : N ≤ m := by
    dsimp [m]
    exact Nat.le_add_right N r
  have hn_m : n < m := by
    have hNentry_le_m : Nentry ≤ m := by
      dsimp [m, N]
      omega
    exact lt_of_lt_of_le hn_entry hNentry_le_m
  have hcard_eq : D.card = (3 ^ d) ^ (m - n) := by
    simpa [D] using
      descendantsAtScale_originCube_nat_card
        (d := d) (m := m) (n := n) (le_of_lt hn_m)
  have hmn_le : m - n ≤ Nentry + q + r := by
    dsimp [m, N]
    omega
  have hw_ge_one : 1 ≤ w := by
    dsimp [w]
    have hpow : 0 < 3 ^ d := pow_pos (by norm_num : (0 : ℕ) < 3) d
    exact_mod_cast (Nat.succ_le_of_lt hpow)
  have hD_weight : (D.card : ℝ) ≤ w ^ Nentry * w ^ q * w ^ r := by
    have hpow_le : w ^ (m - n) ≤ w ^ (Nentry + q + r) :=
      pow_le_pow_right₀ hw_ge_one hmn_le
    have hsplit : w ^ (Nentry + q + r) = w ^ Nentry * w ^ q * w ^ r := by
      rw [pow_add, pow_add]
    calc
      (D.card : ℝ) = w ^ (m - n) := by
        rw [hcard_eq]
        norm_num [w]
      _ ≤ w ^ (Nentry + q + r) := hpow_le
      _ = w ^ Nentry * w ^ q * w ^ r := hsplit
  have hlam_lower : A * ρ ^ r ≤ lam := by
    have hmN : (m - N : ℕ) = r := by
      dsimp [m]
      rw [Nat.add_sub_cancel_left]
    have hmn_decomp :
        (m - n : ℕ) = q + r + (Nentry - n) := by
      dsimp [m, N]
      omega
    have hentry_gap_nonneg : 0 ≤ t * ((Nentry - n : ℕ) : ℝ) := by
      positivity
    have hpow_le :
        (3 : ℝ) ^ (t * (q : ℝ) + (t - α) * (r : ℝ)) ≤ T := by
      dsimp [T, x]
      rw [hmN, hmn_decomp]
      refine Real.rpow_le_rpow_of_exponent_le
        (by norm_num : (1 : ℝ) ≤ 3) ?_
      have hexp :
          -(α * (r : ℝ) -
              t * ((q + r + (Nentry - n) : ℕ) : ℝ)) =
            t * (q : ℝ) + (t - α) * (r : ℝ) +
              t * ((Nentry - n : ℕ) : ℝ) := by
        norm_num [Nat.cast_add]
        ring
      rw [hexp]
      linarith
    have hAρ_eq :
        A * ρ ^ r =
          (3 : ℝ) ^ (t * (q : ℝ) + (t - α) * (r : ℝ)) / scale := by
      have hρpow :
          ρ ^ r = (3 : ℝ) ^ ((t - α) * (r : ℝ)) := by
        dsimp [ρ]
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
      dsimp [A]
      rw [hρpow]
      calc
        (3 : ℝ) ^ (t * (q : ℝ)) / scale *
            (3 : ℝ) ^ ((t - α) * (r : ℝ))
            =
          ((3 : ℝ) ^ (t * (q : ℝ)) *
              (3 : ℝ) ^ ((t - α) * (r : ℝ))) / scale := by
            ring
        _ = (3 : ℝ) ^ (t * (q : ℝ) + (t - α) * (r : ℝ)) / scale := by
            rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    dsimp [lam]
    rw [hAρ_eq]
    exact div_le_div_of_nonneg_right hpow_le hscale_pos.le
  have hlam_one : 1 ≤ lam :=
    hA_one.trans (by
      have hρ_pow_one : 1 ≤ ρ ^ r := one_le_pow₀ hρ_gt.le
      have hA_le_Aρ : A ≤ A * ρ ^ r := by
        calc
          A = A * 1 := by ring
          _ ≤ A * ρ ^ r :=
            mul_le_mul_of_nonneg_left hρ_pow_one hA_pos.le
      exact hA_le_Aρ.trans hlam_lower)
  have hbad :
      P.real (badPairEvent H t α N m n) ≤
        (S.card : ℝ) * ((D.card : ℝ) * Real.exp (-(lam ^ σ))) := by
    simpa [H, K, S, scale, T, lam, x, D, N, m] using
      hpair (t := t) (αbad := α) hP hStruct hΓ hσ_eq hparams
        (N0 := 0) (q := N) (m := m) (n := n)
        hn_m hN_le_m hlam_one
  have hexp :
      Real.exp (-(lam ^ σ)) ≤ Real.exp (-((A * ρ ^ r) ^ σ)) := by
    have hpow : (A * ρ ^ r) ^ σ ≤ lam ^ σ :=
      Real.rpow_le_rpow hAρ_nonneg hlam_lower hσ_pos.le
    exact Real.exp_le_exp.mpr (by linarith)
  have hS_nonneg : 0 ≤ (S.card : ℝ) := by positivity
  have htail :
      (S.card : ℝ) * ((D.card : ℝ) * Real.exp (-(lam ^ σ))) ≤
        ((S.card : ℝ) * w ^ Nentry * w ^ q) *
          (w ^ r * Real.exp (-((A * ρ ^ r) ^ σ))) := by
    have hDexp :
        (D.card : ℝ) * Real.exp (-(lam ^ σ)) ≤
          (w ^ Nentry * w ^ q * w ^ r) *
            Real.exp (-((A * ρ ^ r) ^ σ)) :=
      mul_le_mul hD_weight hexp (by positivity) (by positivity)
    calc
      (S.card : ℝ) * ((D.card : ℝ) * Real.exp (-(lam ^ σ)))
          ≤ (S.card : ℝ) *
              ((w ^ Nentry * w ^ q * w ^ r) *
                Real.exp (-((A * ρ ^ r) ^ σ))) :=
            mul_le_mul_of_nonneg_left hDexp hS_nonneg
      _ =
        ((S.card : ℝ) * w ^ Nentry * w ^ q) *
          (w ^ r * Real.exp (-((A * ρ ^ r) ^ σ))) := by ring
  exact hbad.trans htail

/-- Sum the small-bottom fixed-pair row estimate over the rows and the finite
bottom band. -/
theorem measureReal_smallBottomBadScaleEvent_quenchedProbeEnvelope_le_weighted_kernel
    {d : ℕ} [NeZero d] {σ : ℝ}
    (hσ_pos : 0 < σ)
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ Ccrude : ℝ, 0 < Ccrude ∧
      ∀ {t α : ℝ},
      ∀ {P : Ch04.RestrictionCoeffLaw d}
        (hP : Ch04.RestrictionLawCarrier P)
        (hStruct : Ch04.RestrictionStructuralLaw P)
        (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct),
        hΓ.sigma = σ → hΓ.params = params →
      ∀ {Nentry q : ℕ},
        let K : ℝ := quenchedProbeEnvelopeConst d
        let H : ℕ → ℕ → RegCoeffField d → ℝ :=
          quenchedProbeEnvelope hP hStruct
        let S : Finset (NormalizedProbeIndex d) := Finset.univ
        let w : ℝ := ((3 ^ d : ℕ) : ℝ)
        let scale : ℝ := K * (Ccrude * hΓ.thetaHat ^ (2 : ℕ))
        let A : ℝ := (3 : ℝ) ^ (t * (q : ℝ)) / scale
        let ρ : ℝ := (3 : ℝ) ^ (t - α)
        let N : ℕ := Nentry + q
        0 < t →
        α < t →
        1 ≤ A →
        P.real (smallBottomBadScaleEvent H Nentry t α N) ≤
          ((Nentry : ℝ) * ((S.card : ℝ) * w ^ Nentry * w ^ q)) *
            (Real.exp (-(A ^ σ)) *
              weightedGeometricExpKernelConst w (ρ ^ σ)) := by
  obtain ⟨Ccrude, hCcrude, hrow⟩ :=
    measureReal_smallBottomPairEvent_quenchedProbeEnvelope_le_weighted_row
      (d := d) (σ := σ) hσ_pos params
  refine ⟨Ccrude, hCcrude, ?_⟩
  intro t α P hP hStruct hΓ hσ_eq hparams Nentry q
  dsimp only
  intro ht hαt hA_one
  classical
  let : IsProbabilityMeasure P := hP.isProbability
  let K : ℝ := quenchedProbeEnvelopeConst d
  let H : ℕ → ℕ → RegCoeffField d → ℝ := quenchedProbeEnvelope hP hStruct
  let S : Finset (NormalizedProbeIndex d) := Finset.univ
  let w : ℝ := ((3 ^ d : ℕ) : ℝ)
  let scale : ℝ := K * (Ccrude * hΓ.thetaHat ^ (2 : ℕ))
  let A : ℝ := (3 : ℝ) ^ (t * (q : ℝ)) / scale
  let ρ : ℝ := (3 : ℝ) ^ (t - α)
  let N : ℕ := Nentry + q
  let C : ℝ := (S.card : ℝ) * w ^ Nentry * w ^ q
  let E : ℕ → Fin Nentry → Set (RegCoeffField d) :=
    fun r j => badPairEvent H t α N (N + r) j.val
  have hC_nonneg : 0 ≤ C := by dsimp [C]; positivity
  have hw_pos : 0 < w := by
    dsimp [w]
    exact_mod_cast pow_pos (by norm_num : (0 : ℕ) < 3) d
  have hρ_gt : 1 < ρ := by
    have hgap : 0 < t - α := sub_pos.mpr hαt
    dsimp [ρ]
    calc
      (1 : ℝ) = (3 : ℝ) ^ (0 : ℝ) := by simp
      _ < (3 : ℝ) ^ (t - α) :=
        Real.rpow_lt_rpow_of_exponent_lt
          (by norm_num : (1 : ℝ) < 3) hgap
  have hsubset :
      smallBottomBadScaleEvent H Nentry t α N ⊆
        ⋃ r : ℕ, ⋃ j : Fin Nentry, E r j := by
    simpa [E, N] using
      smallBottomBadScaleEvent_subset_rows
        (H := H) (Nentry := Nentry) (q := q) (t := t) (α := α)
  calc
    P.real (smallBottomBadScaleEvent H Nentry t α N)
        ≤ P.real (⋃ r : ℕ, ⋃ j : Fin Nentry, E r j) :=
          measureReal_mono (μ := P) hsubset
    _ ≤ ((Nentry : ℝ) * C) *
        (Real.exp (-(A ^ σ)) *
          weightedGeometricExpKernelConst w (ρ ^ σ)) :=
          measureReal_iUnion_constRows_le_weighted_exp_kernel
            (μ := P) (Q := Nentry) (E := E)
            hC_nonneg hw_pos hA_one hρ_gt hσ_pos
            (by
              intro r j
              simpa [E, H, K, S, w, scale, A, ρ, N, C] using
                hrow (t := t) (α := α) hP hStruct hΓ hσ_eq hparams
                  (Nentry := Nentry) (q := q) (r := r) (n := j.val)
                  ht hαt j.isLt hA_one)
    _ =
      ((Nentry : ℝ) * ((S.card : ℝ) * w ^ Nentry * w ^ q)) *
        (Real.exp (-(A ^ σ)) *
          weightedGeometricExpKernelConst w (ρ ^ σ)) := by
        dsimp [C]

end

end Section57
end Ch05
end Book
end Homogenization
