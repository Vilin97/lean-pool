/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch02.MultiscaleEllipticity

/-! # Multiscale Ellipticity Definitions -/

namespace Homogenization
namespace Book
namespace Ch02

noncomputable section

/-!
# Public Chapter 2.5 Multiscale Ellipticity Theorem Surface

These are proposition-valued theorem packages for the basic Sec. 2.5 facts.
They are statements only: proving the packages belongs in the companion theorem
files and internal bridge layer.
-/

/-- Public theorem package for the order and localization facts in
`l.multiscale.ellipticity.basic.definitions`.

The package is phrased in the downstream form needed by Chapter 3: besides the
displayed one-cube maxima, it includes individual descendant localization
lemmas for `\Lambda`, `\lambda^{-1}`, and `\Theta`. -/
structure MultiscaleEllipticityBasicTheory {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : TriadicCoeffFamily d) : Prop where
  LambdaSq_nonneg :
    ∀ {s : ℝ} {q : MultiscaleExponent},
      0 < s → q.IsAdmissible → 0 ≤ LambdaSq Q s q a
  lambdaSq_nonneg :
    ∀ {s : ℝ} {q : MultiscaleExponent},
      0 < s → q.IsAdmissible → 0 ≤ lambdaSq Q s q a
  LambdaSq_pos :
    ∀ {s : ℝ} {q : MultiscaleExponent},
      0 < s → q.IsAdmissible → 0 < LambdaSq Q s q a
  lambdaSq_pos :
    ∀ {s : ℝ} {q : MultiscaleExponent},
      0 < s → q.IsAdmissible → 0 < lambdaSq Q s q a
  oneCube_sigmaStarInv_le_b :
    (coarseSigmaStarInvMatrixNorm Q a)⁻¹ ≤ coarseBMatrixNorm Q a
  lambdaSq_mono :
    ∀ {t s : ℝ} {q : MultiscaleExponent},
      0 < t → t < s → q.IsAdmissible →
        lambdaSq Q t q a ≤ lambdaSq Q s q a
  LambdaSq_antitone :
    ∀ {t s : ℝ} {q : MultiscaleExponent},
      0 < t → t < s → q.IsAdmissible →
        LambdaSq Q s q a ≤ LambdaSq Q t q a
  lambdaSq_le_oneCube :
    ∀ {s : ℝ} {q : MultiscaleExponent},
      0 < s → q.IsAdmissible →
        lambdaSq Q s q a ≤ (coarseSigmaStarInvMatrixNorm Q a)⁻¹
  oneCube_b_le_LambdaSq :
    ∀ {s : ℝ} {q : MultiscaleExponent},
      0 < s → q.IsAdmissible →
        coarseBMatrixNorm Q a ≤ LambdaSq Q s q a
  maxDescendant_b_le_maxDescendant_LambdaSq :
    ∀ {k : ℤ} {s : ℝ} {q : MultiscaleExponent},
      k ≤ Q.scale → 0 < s → q.IsAdmissible →
        maxDescendantBMatrixNormAtScale Q k a ≤
          maxDescendantUpperEllipticityAtScale Q k s q a
  maxDescendant_sigmaStarInv_le_maxDescendant_lambdaSq_inv :
    ∀ {k : ℤ} {s : ℝ} {q : MultiscaleExponent},
      k ≤ Q.scale → 0 < s → q.IsAdmissible →
        maxDescendantSigmaStarInvMatrixNormAtScale Q k a ≤
          maxDescendantLowerEllipticityInvAtScale Q k s q a
  maxDescendant_LambdaSq_le :
    ∀ {k : ℤ} {s : ℝ} {q : MultiscaleExponent},
      k ≤ Q.scale → 0 < s → q.IsAdmissible →
        maxDescendantUpperEllipticityAtScale Q k s q a ≤
          multiscaleDescendantWeight Q k s * LambdaSq Q s q a
  maxDescendant_lambdaSq_inv_le :
    ∀ {k : ℤ} {s : ℝ} {q : MultiscaleExponent},
      k ≤ Q.scale → 0 < s → q.IsAdmissible →
        maxDescendantLowerEllipticityInvAtScale Q k s q a ≤
          multiscaleDescendantWeight Q k s * (lambdaSq Q s q a)⁻¹
  descendant_LambdaSq_le :
    ∀ {R : TriadicCube d} {k : ℤ} {s : ℝ} {q : MultiscaleExponent},
      R ∈ descendantsAtScale Q k → 0 < s → q.IsAdmissible →
        LambdaSq R s q a ≤
          multiscaleDescendantWeight Q k s * LambdaSq Q s q a
  descendant_lambdaSq_inv_le :
    ∀ {R : TriadicCube d} {k : ℤ} {s : ℝ} {q : MultiscaleExponent},
      R ∈ descendantsAtScale Q k → 0 < s → q.IsAdmissible →
        (lambdaSq R s q a)⁻¹ ≤
          multiscaleDescendantWeight Q k s * (lambdaSq Q s q a)⁻¹
  ThetaRatio_nonneg :
    ∀ {s t : ℝ}, 0 < s → 0 < t → 0 ≤ ThetaRatio Q s t a
  one_le_ThetaRatio_of_pos :
    ∀ {s t : ℝ}, 0 < s → 0 < t → 1 ≤ ThetaRatio Q s t a
  one_le_ThetaRatio :
    ∀ {s t : ℝ}, 0 < t → t < s → 1 ≤ ThetaRatio Q s t a
  descendant_ThetaRatio_le :
    ∀ {R : TriadicCube d} {k : ℤ} {s t : ℝ},
      R ∈ descendantsAtScale Q k → 0 < t → t < s →
        ThetaRatio R s t a ≤
          (multiscaleDescendantWeight Q k s *
              multiscaleDescendantWeight Q k t) *
            ThetaRatio Q s t a
  descendant_ThetaRatio_rpow_half_le :
    ∀ {R : TriadicCube d} {k : ℤ} {s t : ℝ},
      R ∈ descendantsAtScale Q k → 0 < t → t < s →
        Real.rpow (ThetaRatio R s t a) (1 / 2 : ℝ) ≤
          Real.rpow
            ((multiscaleDescendantWeight Q k s *
                multiscaleDescendantWeight Q k t) *
              ThetaRatio Q s t a)
            (1 / 2 : ℝ)

/-- Public theorem package for
`e.ellipticities.change.q.basic.definitions`.

The constant is stated once per dimension and is then uniform in cube,
coefficient family, and finite exponents. -/
structure MultiscaleEllipticityChangeExponentTheory (d : ℕ) : Prop where
  exists_change_exponent_constant :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Q : TriadicCube d) (a : TriadicCoeffFamily d)
        {s p q : ℝ},
        0 < s → s ≤ 1 → 1 ≤ p → p ≤ q →
          LambdaSq Q s (.finite q) a ≤
              C * Real.rpow s (2 / q - 2 / p) *
                LambdaSq Q s (.finite p) a ∧
            (lambdaSq Q s (.finite q) a)⁻¹ ≤
              C * Real.rpow s (2 / q - 2 / p) *
                (lambdaSq Q s (.finite p) a)⁻¹

/-- Public theorem package asserting that the Sec. 2.5 quantities depend only
on the a.e. coefficient family. -/
structure MultiscaleEllipticityAEEqTheory (d : ℕ) : Prop where
  coarseBMatrixNorm_eq_ofAEEq :
    ∀ {a b : TriadicCoeffFamily d}, TriadicCoeffFamily.AEEq a b →
      ∀ Q : TriadicCube d,
        coarseBMatrixNorm Q a = coarseBMatrixNorm Q b
  coarseSigmaStarInvMatrixNorm_eq_ofAEEq :
    ∀ {a b : TriadicCoeffFamily d}, TriadicCoeffFamily.AEEq a b →
      ∀ Q : TriadicCube d,
        coarseSigmaStarInvMatrixNorm Q a =
          coarseSigmaStarInvMatrixNorm Q b
  LambdaSq_eq_ofAEEq :
    ∀ {a b : TriadicCoeffFamily d}, TriadicCoeffFamily.AEEq a b →
      ∀ (Q : TriadicCube d) (s : ℝ) (q : MultiscaleExponent),
        LambdaSq Q s q a = LambdaSq Q s q b
  lambdaSq_eq_ofAEEq :
    ∀ {a b : TriadicCoeffFamily d}, TriadicCoeffFamily.AEEq a b →
      ∀ (Q : TriadicCube d) (s : ℝ) (q : MultiscaleExponent),
        lambdaSq Q s q a = lambdaSq Q s q b
  ThetaRatio_eq_ofAEEq :
    ∀ {a b : TriadicCoeffFamily d}, TriadicCoeffFamily.AEEq a b →
      ∀ (Q : TriadicCube d) (s t : ℝ),
        ThetaRatio Q s t a = ThetaRatio Q s t b

/-- Aggregate public theorem package for Sec. 2.5. -/
structure MultiscaleEllipticityTheory (d : ℕ) [NeZero d] : Prop where
  basic :
    ∀ (Q : TriadicCube d) (a : TriadicCoeffFamily d),
      MultiscaleEllipticityBasicTheory Q a
  change_exponent :
    MultiscaleEllipticityChangeExponentTheory d
  aeeq :
    MultiscaleEllipticityAEEqTheory d

end

end Ch02
end Book
end Homogenization
