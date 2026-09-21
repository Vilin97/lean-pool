/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.MultiscaleEllipticity.Localization

/-! # Public -/

namespace Homogenization
namespace Book
namespace Ch02

noncomputable section

/-!
# Public Chapter 2.5 Multiscale Ellipticity Theorems

This file assembles the public theorem packages and records that the
multiscale ellipticity quantities depend only on a.e. coefficient data.
-/

open MeasureTheory
open scoped Matrix.Norms.Frobenius


/-- Public theorem package for the Sec. 2.5 basic order and localization
facts. -/
theorem multiscaleEllipticityBasicTheory {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : TriadicCoeffFamily d) :
    MultiscaleEllipticityBasicTheory Q a where
  LambdaSq_nonneg := by
    intro s q hs hq
    exact LambdaSq_nonneg Q a hs hq
  lambdaSq_nonneg := by
    intro s q hs hq
    exact lambdaSq_nonneg Q a hs hq
  LambdaSq_pos := by
    intro s q hs hq
    exact LambdaSq_pos Q a hs hq
  lambdaSq_pos := by
    intro s q hs hq
    exact lambdaSq_pos Q a hs hq
  oneCube_sigmaStarInv_le_b := oneCube_sigmaStarInv_le_b Q a
  lambdaSq_mono := by
    intro t s q ht hts hq
    exact lambdaSq_mono Q a ht hts hq
  LambdaSq_antitone := by
    intro t s q ht hts hq
    exact LambdaSq_antitone Q a ht hts hq
  lambdaSq_le_oneCube := by
    intro s q hs hq
    exact lambdaSq_le_oneCube Q a hs hq
  oneCube_b_le_LambdaSq := by
    intro s q hs hq
    exact oneCube_b_le_LambdaSq Q a hs hq
  maxDescendant_b_le_maxDescendant_LambdaSq := by
    intro k s q hk hs hq
    exact maxDescendant_b_le_maxDescendant_LambdaSq Q a hk hs hq
  maxDescendant_sigmaStarInv_le_maxDescendant_lambdaSq_inv := by
    intro k s q hk hs hq
    exact maxDescendant_sigmaStarInv_le_maxDescendant_lambdaSq_inv Q a hk hs hq
  maxDescendant_LambdaSq_le := by
    intro k s q hk hs hq
    exact maxDescendant_LambdaSq_le Q a hk hs hq
  maxDescendant_lambdaSq_inv_le := by
    intro k s q hk hs hq
    exact maxDescendant_lambdaSq_inv_le Q a hk hs hq
  descendant_LambdaSq_le := by
    intro R k s q hR hs hq
    exact descendant_LambdaSq_le (Q := Q) (R := R) (k := k) a hR hs hq
  descendant_lambdaSq_inv_le := by
    intro R k s q hR hs hq
    exact descendant_lambdaSq_inv_le (Q := Q) (R := R) (k := k) a hR hs hq
  ThetaRatio_nonneg := by
    intro s t hs ht
    exact ThetaRatio_nonneg Q a hs ht
  one_le_ThetaRatio_of_pos := by
    intro s t hs ht
    exact one_le_ThetaRatio_of_pos Q a hs ht
  one_le_ThetaRatio := by
    intro s t ht hts
    exact one_le_ThetaRatio Q a ht hts
  descendant_ThetaRatio_le := by
    intro R k s t hR ht hts
    exact descendant_ThetaRatio_le (Q := Q) (R := R) (k := k) a hR
      (lt_trans ht hts) ht
  descendant_ThetaRatio_rpow_half_le := by
    intro R k s t hR ht hts
    exact descendant_ThetaRatio_rpow_half_le (Q := Q) (R := R) (k := k) a hR
      (lt_trans ht hts) ht

theorem coarseBMatrixNorm_eq_ofAEEq {d : ℕ} {a b : TriadicCoeffFamily d}
    (h : TriadicCoeffFamily.AEEq a b) (Q : TriadicCube d) :
    coarseBMatrixNorm Q a = coarseBMatrixNorm Q b := by
  unfold coarseBMatrixNorm
  rw [bCoarse_eq_ofAEEq (h Q)]

theorem coarseSigmaStarInvMatrixNorm_eq_ofAEEq {d : ℕ}
    {a b : TriadicCoeffFamily d} (h : TriadicCoeffFamily.AEEq a b)
    (Q : TriadicCube d) :
    coarseSigmaStarInvMatrixNorm Q a = coarseSigmaStarInvMatrixNorm Q b := by
  unfold coarseSigmaStarInvMatrixNorm
  rw [sigmaStarInvCoarse_eq_ofAEEq (h Q)]

theorem maxDescendantBMatrixNormAtScale_eq_ofAEEq {d : ℕ}
    {a b : TriadicCoeffFamily d} (h : TriadicCoeffFamily.AEEq a b)
    (Q : TriadicCube d) (k : ℤ) :
    maxDescendantBMatrixNormAtScale Q k a =
      maxDescendantBMatrixNormAtScale Q k b := by
  unfold maxDescendantBMatrixNormAtScale
  exact finsetSupReal_congr _ fun R _ => coarseBMatrixNorm_eq_ofAEEq h R

theorem maxDescendantSigmaStarInvMatrixNormAtScale_eq_ofAEEq {d : ℕ}
    {a b : TriadicCoeffFamily d} (h : TriadicCoeffFamily.AEEq a b)
    (Q : TriadicCube d) (k : ℤ) :
    maxDescendantSigmaStarInvMatrixNormAtScale Q k a =
      maxDescendantSigmaStarInvMatrixNormAtScale Q k b := by
  unfold maxDescendantSigmaStarInvMatrixNormAtScale
  exact finsetSupReal_congr _ fun R _ =>
    coarseSigmaStarInvMatrixNorm_eq_ofAEEq h R

theorem maxDescendantBMatrixNormAtScale_translateCube_of_coarseBMatrixNorm
    {d : ℕ} (a b : TriadicCoeffFamily d) (z : Fin d → ℤ)
    (Q : TriadicCube d) {k : ℤ} (hk : k ≤ Q.scale)
    (hB : ∀ R ∈ descendantsAtScale Q k,
      coarseBMatrixNorm
          (translateCube (descendantTranslationShift (Int.toNat (Q.scale - k)) z) R) a =
        coarseBMatrixNorm R b) :
    maxDescendantBMatrixNormAtScale (translateCube z Q) k a =
      maxDescendantBMatrixNormAtScale Q k b := by
  unfold maxDescendantBMatrixNormAtScale
  rw [descendantsAtScale_translateCube z Q hk]
  exact finsetSupReal_image _ _ _ _ hB

theorem maxDescendantSigmaStarInvMatrixNormAtScale_translateCube_of_coarseSigmaStarInvMatrixNorm
    {d : ℕ} (a b : TriadicCoeffFamily d) (z : Fin d → ℤ)
    (Q : TriadicCube d) {k : ℤ} (hk : k ≤ Q.scale)
    (hSigma : ∀ R ∈ descendantsAtScale Q k,
      coarseSigmaStarInvMatrixNorm
          (translateCube (descendantTranslationShift (Int.toNat (Q.scale - k)) z) R) a =
        coarseSigmaStarInvMatrixNorm R b) :
    maxDescendantSigmaStarInvMatrixNormAtScale (translateCube z Q) k a =
      maxDescendantSigmaStarInvMatrixNormAtScale Q k b := by
  unfold maxDescendantSigmaStarInvMatrixNormAtScale
  rw [descendantsAtScale_translateCube z Q hk]
  exact finsetSupReal_image _ _ _ _ hSigma

theorem LambdaSqFinite_translateCube_of_coarseBMatrixNorm
    {d : ℕ} (a b : TriadicCoeffFamily d) (z : Fin d → ℤ)
    (Q : TriadicCube d) (s q : ℝ)
    (hB : ∀ (n : ℕ) (R : TriadicCube d),
      R ∈ descendantsAtScale Q (Q.scale - (n : ℤ)) →
        coarseBMatrixNorm (translateCube (descendantTranslationShift n z) R) a =
          coarseBMatrixNorm R b) :
    LambdaSqFinite (translateCube z Q) s q a = LambdaSqFinite Q s q b := by
  unfold LambdaSqFinite
  apply congrArg (fun S : ℝ => Real.rpow S (2 / q))
  apply tsum_congr
  intro n
  have hk : Q.scale - (n : ℤ) ≤ Q.scale := by
    exact sub_le_self Q.scale (by exact_mod_cast Nat.zero_le n)
  have hmax :=
    maxDescendantBMatrixNormAtScale_translateCube_of_coarseBMatrixNorm
      (a := a) (b := b) z Q (k := Q.scale - (n : ℤ)) hk
      (by
        intro R hR
        simpa using hB n R hR)
  simpa [translateCube] using
    congrArg (fun x => geometricWeight s q n * Real.rpow x (q / 2)) hmax

theorem lambdaSqFinite_translateCube_of_coarseSigmaStarInvMatrixNorm
    {d : ℕ} (a b : TriadicCoeffFamily d) (z : Fin d → ℤ)
    (Q : TriadicCube d) (s q : ℝ)
    (hSigma : ∀ (n : ℕ) (R : TriadicCube d),
      R ∈ descendantsAtScale Q (Q.scale - (n : ℤ)) →
        coarseSigmaStarInvMatrixNorm (translateCube (descendantTranslationShift n z) R) a =
          coarseSigmaStarInvMatrixNorm R b) :
    lambdaSqFinite (translateCube z Q) s q a = lambdaSqFinite Q s q b := by
  unfold lambdaSqFinite
  apply congrArg (fun S : ℝ => Real.rpow S (-(2 / q)))
  apply tsum_congr
  intro n
  have hk : Q.scale - (n : ℤ) ≤ Q.scale := by
    exact sub_le_self Q.scale (by exact_mod_cast Nat.zero_le n)
  have hmax :=
    maxDescendantSigmaStarInvMatrixNormAtScale_translateCube_of_coarseSigmaStarInvMatrixNorm
      (a := a) (b := b) z Q (k := Q.scale - (n : ℤ)) hk
      (by
        intro R hR
        simpa using hSigma n R hR)
  simpa [translateCube] using
    congrArg (fun x => geometricWeight s q n * Real.rpow x (q / 2)) hmax

theorem LambdaSqInfinity_translateCube_of_coarseBMatrixNorm
    {d : ℕ} (a b : TriadicCoeffFamily d) (z : Fin d → ℤ)
    (Q : TriadicCube d) (s : ℝ)
    (hB : ∀ (n : ℕ) (R : TriadicCube d),
      R ∈ descendantsAtScale Q (Q.scale - (n : ℤ)) →
        coarseBMatrixNorm (translateCube (descendantTranslationShift n z) R) a =
          coarseBMatrixNorm R b) :
    LambdaSqInfinity (translateCube z Q) s a = LambdaSqInfinity Q s b := by
  unfold LambdaSqInfinity
  refine congrArg sSup ?_
  ext M
  constructor
  · rintro ⟨n, rfl⟩
    refine ⟨n, ?_⟩
    have hk : Q.scale - (n : ℤ) ≤ Q.scale := by
      exact sub_le_self Q.scale (by exact_mod_cast Nat.zero_le n)
    have hmax :=
      maxDescendantBMatrixNormAtScale_translateCube_of_coarseBMatrixNorm
        (a := a) (b := b) z Q (k := Q.scale - (n : ℤ)) hk
        (by
          intro R hR
          simpa using hB n R hR)
    simpa [translateCube] using
      congrArg (fun x => Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)) * x) hmax
  · rintro ⟨n, rfl⟩
    refine ⟨n, ?_⟩
    have hk : Q.scale - (n : ℤ) ≤ Q.scale := by
      exact sub_le_self Q.scale (by exact_mod_cast Nat.zero_le n)
    have hmax :=
      maxDescendantBMatrixNormAtScale_translateCube_of_coarseBMatrixNorm
        (a := a) (b := b) z Q (k := Q.scale - (n : ℤ)) hk
        (by
          intro R hR
          simpa using hB n R hR)
    simpa [translateCube] using
      congrArg (fun x => Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)) * x) hmax.symm

theorem lambdaSqInfinity_translateCube_of_coarseSigmaStarInvMatrixNorm
    {d : ℕ} (a b : TriadicCoeffFamily d) (z : Fin d → ℤ)
    (Q : TriadicCube d) (s : ℝ)
    (hSigma : ∀ (n : ℕ) (R : TriadicCube d),
      R ∈ descendantsAtScale Q (Q.scale - (n : ℤ)) →
        coarseSigmaStarInvMatrixNorm (translateCube (descendantTranslationShift n z) R) a =
          coarseSigmaStarInvMatrixNorm R b) :
    lambdaSqInfinity (translateCube z Q) s a = lambdaSqInfinity Q s b := by
  unfold lambdaSqInfinity
  congr 1
  refine congrArg sSup ?_
  ext M
  constructor
  · rintro ⟨n, rfl⟩
    refine ⟨n, ?_⟩
    have hk : Q.scale - (n : ℤ) ≤ Q.scale := by
      exact sub_le_self Q.scale (by exact_mod_cast Nat.zero_le n)
    have hmax :=
      maxDescendantSigmaStarInvMatrixNormAtScale_translateCube_of_coarseSigmaStarInvMatrixNorm
        (a := a) (b := b) z Q (k := Q.scale - (n : ℤ)) hk
        (by
          intro R hR
          simpa using hSigma n R hR)
    simpa [translateCube] using
      congrArg (fun x => Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)) * x) hmax
  · rintro ⟨n, rfl⟩
    refine ⟨n, ?_⟩
    have hk : Q.scale - (n : ℤ) ≤ Q.scale := by
      exact sub_le_self Q.scale (by exact_mod_cast Nat.zero_le n)
    have hmax :=
      maxDescendantSigmaStarInvMatrixNormAtScale_translateCube_of_coarseSigmaStarInvMatrixNorm
        (a := a) (b := b) z Q (k := Q.scale - (n : ℤ)) hk
        (by
          intro R hR
          simpa using hSigma n R hR)
    simpa [translateCube] using
      congrArg (fun x => Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)) * x) hmax.symm

theorem LambdaSq_translateCube_of_coarseBMatrixNorm
    {d : ℕ} (a b : TriadicCoeffFamily d) (z : Fin d → ℤ)
    (Q : TriadicCube d) (s : ℝ) (q : MultiscaleExponent)
    (hB : ∀ (n : ℕ) (R : TriadicCube d),
      R ∈ descendantsAtScale Q (Q.scale - (n : ℤ)) →
        coarseBMatrixNorm (translateCube (descendantTranslationShift n z) R) a =
          coarseBMatrixNorm R b) :
    LambdaSq (translateCube z Q) s q a = LambdaSq Q s q b := by
  cases q with
  | finite q =>
      exact LambdaSqFinite_translateCube_of_coarseBMatrixNorm a b z Q s q hB
  | infinity =>
      exact LambdaSqInfinity_translateCube_of_coarseBMatrixNorm a b z Q s hB

theorem lambdaSq_translateCube_of_coarseSigmaStarInvMatrixNorm
    {d : ℕ} (a b : TriadicCoeffFamily d) (z : Fin d → ℤ)
    (Q : TriadicCube d) (s : ℝ) (q : MultiscaleExponent)
    (hSigma : ∀ (n : ℕ) (R : TriadicCube d),
      R ∈ descendantsAtScale Q (Q.scale - (n : ℤ)) →
        coarseSigmaStarInvMatrixNorm (translateCube (descendantTranslationShift n z) R) a =
          coarseSigmaStarInvMatrixNorm R b) :
    lambdaSq (translateCube z Q) s q a = lambdaSq Q s q b := by
  cases q with
  | finite q =>
      exact lambdaSqFinite_translateCube_of_coarseSigmaStarInvMatrixNorm a b z Q s q hSigma
  | infinity =>
      exact lambdaSqInfinity_translateCube_of_coarseSigmaStarInvMatrixNorm a b z Q s hSigma

theorem LambdaSqFinite_eq_ofAEEq {d : ℕ} {a b : TriadicCoeffFamily d}
    (h : TriadicCoeffFamily.AEEq a b) (Q : TriadicCube d) (s q : ℝ) :
    LambdaSqFinite Q s q a = LambdaSqFinite Q s q b := by
  unfold LambdaSqFinite
  apply congrArg (fun S : ℝ => Real.rpow S (2 / q))
  apply tsum_congr
  intro n
  rw [maxDescendantBMatrixNormAtScale_eq_ofAEEq h]

theorem lambdaSqFinite_eq_ofAEEq {d : ℕ} {a b : TriadicCoeffFamily d}
    (h : TriadicCoeffFamily.AEEq a b) (Q : TriadicCube d) (s q : ℝ) :
    lambdaSqFinite Q s q a = lambdaSqFinite Q s q b := by
  unfold lambdaSqFinite
  apply congrArg (fun S : ℝ => Real.rpow S (-(2 / q)))
  apply tsum_congr
  intro n
  rw [maxDescendantSigmaStarInvMatrixNormAtScale_eq_ofAEEq h]

theorem LambdaSqInfinity_eq_ofAEEq {d : ℕ} {a b : TriadicCoeffFamily d}
    (h : TriadicCoeffFamily.AEEq a b) (Q : TriadicCube d) (s : ℝ) :
    LambdaSqInfinity Q s a = LambdaSqInfinity Q s b := by
  unfold LambdaSqInfinity
  refine congrArg sSup ?_
  ext M
  constructor
  · rintro ⟨n, rfl⟩
    refine ⟨n, ?_⟩
    rw [maxDescendantBMatrixNormAtScale_eq_ofAEEq h]
  · rintro ⟨n, rfl⟩
    refine ⟨n, ?_⟩
    rw [maxDescendantBMatrixNormAtScale_eq_ofAEEq h]

theorem lambdaSqInfinity_eq_ofAEEq {d : ℕ} {a b : TriadicCoeffFamily d}
    (h : TriadicCoeffFamily.AEEq a b) (Q : TriadicCube d) (s : ℝ) :
    lambdaSqInfinity Q s a = lambdaSqInfinity Q s b := by
  unfold lambdaSqInfinity
  apply congrArg (fun S : ℝ => S⁻¹)
  refine congrArg sSup ?_
  ext M
  constructor
  · rintro ⟨n, rfl⟩
    refine ⟨n, ?_⟩
    rw [maxDescendantSigmaStarInvMatrixNormAtScale_eq_ofAEEq h]
  · rintro ⟨n, rfl⟩
    refine ⟨n, ?_⟩
    rw [maxDescendantSigmaStarInvMatrixNormAtScale_eq_ofAEEq h]

theorem LambdaSq_eq_ofAEEq {d : ℕ} {a b : TriadicCoeffFamily d}
    (h : TriadicCoeffFamily.AEEq a b) (Q : TriadicCube d) (s : ℝ)
    (q : MultiscaleExponent) :
    LambdaSq Q s q a = LambdaSq Q s q b := by
  cases q with
  | finite q =>
      exact LambdaSqFinite_eq_ofAEEq h Q s q
  | infinity =>
      exact LambdaSqInfinity_eq_ofAEEq h Q s

theorem lambdaSq_eq_ofAEEq {d : ℕ} {a b : TriadicCoeffFamily d}
    (h : TriadicCoeffFamily.AEEq a b) (Q : TriadicCube d) (s : ℝ)
    (q : MultiscaleExponent) :
    lambdaSq Q s q a = lambdaSq Q s q b := by
  cases q with
  | finite q =>
      exact lambdaSqFinite_eq_ofAEEq h Q s q
  | infinity =>
      exact lambdaSqInfinity_eq_ofAEEq h Q s

theorem LambdaS_eq_ofAEEq {d : ℕ} {a b : TriadicCoeffFamily d}
    (h : TriadicCoeffFamily.AEEq a b) (Q : TriadicCube d) (s : ℝ) :
    LambdaS Q s a = LambdaS Q s b :=
  LambdaSq_eq_ofAEEq h Q s (.finite 1)

theorem lambdaS_eq_ofAEEq {d : ℕ} {a b : TriadicCoeffFamily d}
    (h : TriadicCoeffFamily.AEEq a b) (Q : TriadicCube d) (s : ℝ) :
    lambdaS Q s a = lambdaS Q s b :=
  lambdaSq_eq_ofAEEq h Q s (.finite 1)

theorem ThetaRatio_eq_ofAEEq {d : ℕ} {a b : TriadicCoeffFamily d}
    (h : TriadicCoeffFamily.AEEq a b) (Q : TriadicCube d) (s t : ℝ) :
    ThetaRatio Q s t a = ThetaRatio Q s t b := by
  unfold ThetaRatio
  rw [LambdaS_eq_ofAEEq h Q s, lambdaS_eq_ofAEEq h Q t]

/-- Public theorem package asserting that Sec. 2.5 quantities depend only on
the coefficient family modulo a.e. equality on each triadic cube. -/
theorem multiscaleEllipticityAEEqTheory (d : ℕ) :
    MultiscaleEllipticityAEEqTheory d where
  coarseBMatrixNorm_eq_ofAEEq := by
    intro a b h Q
    exact coarseBMatrixNorm_eq_ofAEEq h Q
  coarseSigmaStarInvMatrixNorm_eq_ofAEEq := by
    intro a b h Q
    exact coarseSigmaStarInvMatrixNorm_eq_ofAEEq h Q
  LambdaSq_eq_ofAEEq := by
    intro a b h Q s q
    exact LambdaSq_eq_ofAEEq h Q s q
  lambdaSq_eq_ofAEEq := by
    intro a b h Q s q
    exact lambdaSq_eq_ofAEEq h Q s q
  ThetaRatio_eq_ofAEEq := by
    intro a b h Q s t
    exact ThetaRatio_eq_ofAEEq h Q s t

theorem multiscaleEllipticityChangeExponentTheory (d : ℕ) [NeZero d] :
    MultiscaleEllipticityChangeExponentTheory d where
  exists_change_exponent_constant := by
    refine ⟨25 * Real.exp 4, by positivity, ?_⟩
    intro Q a s p q hs hs_le hp hpq
    constructor
    · exact LambdaSqFinite_le_change_exponent Q a hs hs_le hp hpq
    · exact lambdaSqFinite_inv_le_change_exponent Q a hs hs_le hp hpq

theorem multiscaleEllipticityTheory (d : ℕ) [NeZero d] :
    MultiscaleEllipticityTheory d where
  basic := by
    intro Q a
    exact multiscaleEllipticityBasicTheory Q a
  change_exponent := multiscaleEllipticityChangeExponentTheory d
  aeeq := multiscaleEllipticityAEEqTheory d

end

end Ch02
end Book
end Homogenization
