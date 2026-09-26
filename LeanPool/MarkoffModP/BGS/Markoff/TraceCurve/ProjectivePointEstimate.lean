/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.Markoff.TraceCurve.BiprojectiveClosure
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The exact projective-to-torus point-count bridge

Mathlib currently has no general smooth-projective curve, genus, normalization,
and Hasse--Weil package from which the endgame estimate can be derived.  This
module therefore starts at the first honest arithmetic interface:

* an explicit equivalence between affine cover zeros and projective rational
  points away from an explicit boundary finset;
* the Hasse inequality for that projective model, passed as a proposition;
* independent numerical genus and boundary bounds.

The conclusion is the desired `O(sqrt (#K) * d * e)` estimate for the actual
Laurent trace-solution finset.  No target estimate is hidden in a typeclass.
-/

@[expose] public section

namespace BGS.Markoff

noncomputable section

variable (K : Type*) [Field K] [Fintype K] [DecidableEq K]

/-- An explicit projective comparison, Hasse inequality, genus bound, and
boundary bound imply the split trace-cover estimate on the original torus.

`projectivePoints` is intended to be the rational-point finset of the smooth
projective normalization, and `projectiveBoundary` its complement of the
affine chart.  Requiring an actual equivalence of finite types prevents the
model comparison from being replaced by a cardinality assertion about the
desired torus count. -/
theorem splitTraceCurveSolutions_count_error_le_of_projectiveComparison_and_hasse
    {P : Type*} [DecidableEq P]
    (alpha beta : K) (d e : ℕ) (hd : 0 < d) (he : 0 < e) (hbeta : beta ≠ 0)
    (projectivePoints projectiveBoundary : Finset P)
    (hboundarySubset : projectiveBoundary ⊆ projectivePoints)
    (modelComparison :
      ↥(affineSplitTraceCoverZeros K alpha beta d e) ≃
        ↥(projectivePoints \ projectiveBoundary))
    (genus genusCoefficient boundaryCoefficient : ℕ)
    (hprojectiveHasse :
      |(projectivePoints.card : ℝ) - ((Fintype.card K : ℝ) + 1)| ≤
        2 * (genus : ℝ) * Real.sqrt (Fintype.card K : ℝ))
    (hgenus : genus ≤ genusCoefficient * d * e)
    (hboundary : projectiveBoundary.card ≤ boundaryCoefficient * d * e) :
    |((splitTraceCurveSolutions K alpha beta d e).card : ℝ) -
        (Fintype.card K : ℝ)| ≤
      ((2 * (genusCoefficient : ℝ) * Real.sqrt (Fintype.card K : ℝ)) +
          (boundaryCoefficient : ℝ)) * (d : ℝ) * (e : ℝ) := by
  have hmodelCard :
      (affineSplitTraceCoverZeros K alpha beta d e).card =
        (projectivePoints \ projectiveBoundary).card := by
    calc
      (affineSplitTraceCoverZeros K alpha beta d e).card =
          Fintype.card ↥(affineSplitTraceCoverZeros K alpha beta d e) :=
        (Fintype.card_coe _).symm
      _ = Fintype.card ↥(projectivePoints \ projectiveBoundary) :=
        Fintype.card_congr modelComparison
      _ = (projectivePoints \ projectiveBoundary).card := Fintype.card_coe _
  have hprojectivePartition :
      (projectivePoints \ projectiveBoundary).card + projectiveBoundary.card =
        projectivePoints.card :=
    Finset.card_sdiff_add_card_eq_card hboundarySubset
  have haffineBoundary :=
    affineSplitTraceCoverZeros_card_eq_torus_card_add_one
      K alpha beta d e hd he hbeta
  have htorusSolutions :=
    torusSplitTraceCoverZeros_card_eq_splitTraceCurveSolutions_card
      K alpha beta d e
  have hcardIdentity :
      projectivePoints.card =
        (splitTraceCurveSolutions K alpha beta d e).card + 1 +
          projectiveBoundary.card := by
    omega
  have herrorIdentity :
      ((splitTraceCurveSolutions K alpha beta d e).card : ℝ) -
          (Fintype.card K : ℝ) =
        ((projectivePoints.card : ℝ) - ((Fintype.card K : ℝ) + 1)) -
          (projectiveBoundary.card : ℝ) := by
    have hcardReal :
        (projectivePoints.card : ℝ) =
          (splitTraceCurveSolutions K alpha beta d e).card + 1 +
            projectiveBoundary.card := by
      exact_mod_cast hcardIdentity
    rw [hcardReal]
    ring
  have hboundaryReal :
      (projectiveBoundary.card : ℝ) ≤
        (boundaryCoefficient : ℝ) * d * e := by
    exact_mod_cast hboundary
  have hgenusReal :
      (genus : ℝ) ≤ (genusCoefficient : ℝ) * d * e := by
    exact_mod_cast hgenus
  have hsqrtNonnegative :
      0 ≤ Real.sqrt (Fintype.card K : ℝ) := Real.sqrt_nonneg _
  rw [herrorIdentity]
  calc
    |((projectivePoints.card : ℝ) - ((Fintype.card K : ℝ) + 1)) -
          (projectiveBoundary.card : ℝ)| ≤
        |(projectivePoints.card : ℝ) - ((Fintype.card K : ℝ) + 1)| +
          |(projectiveBoundary.card : ℝ)| := abs_sub _ _
    _ = |(projectivePoints.card : ℝ) - ((Fintype.card K : ℝ) + 1)| +
          (projectiveBoundary.card : ℝ) := by simp
    _ ≤ 2 * (genus : ℝ) * Real.sqrt (Fintype.card K : ℝ) +
          (projectiveBoundary.card : ℝ) :=
      add_le_add hprojectiveHasse le_rfl
    _ ≤ 2 * ((genusCoefficient : ℝ) * d * e) *
          Real.sqrt (Fintype.card K : ℝ) +
          ((boundaryCoefficient : ℝ) * d * e) := by
      gcongr
    _ = ((2 * (genusCoefficient : ℝ) * Real.sqrt (Fintype.card K : ℝ)) +
          (boundaryCoefficient : ℝ)) * (d : ℝ) * (e : ℝ) := by ring

/-- Since a finite field is nonempty, its square-root cardinality is at least
one.  Thus the separate projective-boundary contribution can be absorbed into
the same `sqrt (#K) * d * e` error term used in the paper. -/
theorem splitTraceCurveSolutions_count_error_le_sqrt_mul_de_of_projectiveComparison_and_hasse
    {P : Type*} [DecidableEq P]
    (alpha beta : K) (d e : ℕ) (hd : 0 < d) (he : 0 < e) (hbeta : beta ≠ 0)
    (projectivePoints projectiveBoundary : Finset P)
    (hboundarySubset : projectiveBoundary ⊆ projectivePoints)
    (modelComparison :
      ↥(affineSplitTraceCoverZeros K alpha beta d e) ≃
        ↥(projectivePoints \ projectiveBoundary))
    (genus genusCoefficient boundaryCoefficient : ℕ)
    (hprojectiveHasse :
      |(projectivePoints.card : ℝ) - ((Fintype.card K : ℝ) + 1)| ≤
        2 * (genus : ℝ) * Real.sqrt (Fintype.card K : ℝ))
    (hgenus : genus ≤ genusCoefficient * d * e)
    (hboundary : projectiveBoundary.card ≤ boundaryCoefficient * d * e) :
    |((splitTraceCurveSolutions K alpha beta d e).card : ℝ) -
        (Fintype.card K : ℝ)| ≤
      (2 * (genusCoefficient : ℝ) + (boundaryCoefficient : ℝ)) *
        Real.sqrt (Fintype.card K : ℝ) * (d : ℝ) * (e : ℝ) := by
  have hbridge :=
    splitTraceCurveSolutions_count_error_le_of_projectiveComparison_and_hasse
      K alpha beta d e hd he hbeta projectivePoints projectiveBoundary
        hboundarySubset modelComparison genus genusCoefficient boundaryCoefficient
        hprojectiveHasse hgenus hboundary
  have hcardOneNat : 1 ≤ Fintype.card K := Fintype.card_pos
  have hcardOneReal : (1 : ℝ) ≤ Fintype.card K := by exact_mod_cast hcardOneNat
  have hsqrtOne : (1 : ℝ) ≤ Real.sqrt (Fintype.card K : ℝ) :=
    Real.one_le_sqrt.mpr hcardOneReal
  have hboundaryAbsorb :
      (boundaryCoefficient : ℝ) ≤
        (boundaryCoefficient : ℝ) * Real.sqrt (Fintype.card K : ℝ) := by
    simpa using mul_le_mul_of_nonneg_left hsqrtOne
      (Nat.cast_nonneg boundaryCoefficient)
  calc
    |((splitTraceCurveSolutions K alpha beta d e).card : ℝ) -
        (Fintype.card K : ℝ)| ≤
      ((2 * (genusCoefficient : ℝ) * Real.sqrt (Fintype.card K : ℝ)) +
          (boundaryCoefficient : ℝ)) * (d : ℝ) * (e : ℝ) := hbridge
    _ ≤ (2 * (genusCoefficient : ℝ) * Real.sqrt (Fintype.card K : ℝ) +
          (boundaryCoefficient : ℝ) * Real.sqrt (Fintype.card K : ℝ)) *
          (d : ℝ) * (e : ℝ) := by gcongr
    _ = (2 * (genusCoefficient : ℝ) + (boundaryCoefficient : ℝ)) *
        Real.sqrt (Fintype.card K : ℝ) * (d : ℝ) * (e : ℝ) := by ring

/-- Square-form Hasse interface, matching the form used by the explicit
Legendre development and the standard Hasse--Weil statement. -/
theorem splitTraceCurveSolutions_count_error_le_sqrt_mul_de_of_projectiveComparison_and_hasseSquare
    {P : Type*} [DecidableEq P]
    (alpha beta : K) (d e : ℕ) (hd : 0 < d) (he : 0 < e) (hbeta : beta ≠ 0)
    (projectivePoints projectiveBoundary : Finset P)
    (hboundarySubset : projectiveBoundary ⊆ projectivePoints)
    (modelComparison :
      ↥(affineSplitTraceCoverZeros K alpha beta d e) ≃
        ↥(projectivePoints \ projectiveBoundary))
    (genus genusCoefficient boundaryCoefficient : ℕ)
    (hprojectiveHasseSquare :
      ((projectivePoints.card : ℝ) - ((Fintype.card K : ℝ) + 1)) ^ 2 ≤
        4 * (genus : ℝ) ^ 2 * (Fintype.card K : ℝ))
    (hgenus : genus ≤ genusCoefficient * d * e)
    (hboundary : projectiveBoundary.card ≤ boundaryCoefficient * d * e) :
    |((splitTraceCurveSolutions K alpha beta d e).card : ℝ) -
        (Fintype.card K : ℝ)| ≤
      (2 * (genusCoefficient : ℝ) + (boundaryCoefficient : ℝ)) *
        Real.sqrt (Fintype.card K : ℝ) * (d : ℝ) * (e : ℝ) := by
  let projectiveError : ℝ :=
    (projectivePoints.card : ℝ) - ((Fintype.card K : ℝ) + 1)
  have hcardNonnegative : (0 : ℝ) ≤ Fintype.card K := Nat.cast_nonneg _
  have htargetNonnegative :
      0 ≤ 2 * (genus : ℝ) * Real.sqrt (Fintype.card K : ℝ) := by positivity
  have hprojectiveHasse :
      |projectiveError| ≤
        2 * (genus : ℝ) * Real.sqrt (Fintype.card K : ℝ) := by
    apply (sq_le_sq₀ (abs_nonneg _) htargetNonnegative).mp
    calc
      |projectiveError| ^ 2 = projectiveError ^ 2 := sq_abs projectiveError
      _ ≤ 4 * (genus : ℝ) ^ 2 * (Fintype.card K : ℝ) := by
        simpa [projectiveError] using hprojectiveHasseSquare
      _ = (2 * (genus : ℝ) * Real.sqrt (Fintype.card K : ℝ)) ^ 2 := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hcardNonnegative]
        ring
  exact splitTraceCurveSolutions_count_error_le_sqrt_mul_de_of_projectiveComparison_and_hasse
    K alpha beta d e hd he hbeta projectivePoints projectiveBoundary
      hboundarySubset modelComparison genus genusCoefficient boundaryCoefficient
      (by simpa [projectiveError] using hprojectiveHasse) hgenus hboundary

/-! ### Boundary labels supplied by the corner initial forms -/

/-- Four raw projective corners, with one label for each factor of the corresponding weighted
initial form.  A normalization proof should inject its boundary points into this finite type. -/
abbrev splitTraceNormalizationBoundaryLabels (d e : ℕ) :=
  Fin 4 × Fin (Nat.gcd d e)

/-- An injective labeling of normalization-boundary points by a corner and an initial factor gives
the explicit `4de` boundary bound required by the point-count bridge.  This premise is structural:
it does not assume the desired cardinal inequality. -/
theorem projectiveBoundary_card_le_four_mul_de_of_injective_normalizationLabels
    {P : Type*} [DecidableEq P] (boundary : Finset P)
    (d e : ℕ) (hd : 0 < d) (he : 0 < e)
    (labels : ↥boundary → splitTraceNormalizationBoundaryLabels d e)
    (hlabels : Function.Injective labels) :
    boundary.card ≤ 4 * d * e := by
  have hgcd : Nat.gcd d e ≤ d := Nat.gcd_le_left e hd
  have hdde : d ≤ d * e := Nat.le_mul_of_pos_right d he
  calc
    boundary.card = Fintype.card ↥boundary := (Fintype.card_coe boundary).symm
    _ ≤ Fintype.card (splitTraceNormalizationBoundaryLabels d e) :=
      Fintype.card_le_of_injective labels hlabels
    _ = 4 * Nat.gcd d e := by simp
    _ ≤ 4 * d := Nat.mul_le_mul_left 4 hgcd
    _ ≤ 4 * d * e := by simpa [Nat.mul_assoc] using Nat.mul_le_mul_left 4 hdde

/-- The projective point estimate with boundary control supplied by actual normalization labels.
The remaining inputs are the affine-chart comparison, the genus bound, and Hasse--Weil for the
smooth projective normalization. -/
theorem splitTraceCurveSolutions_count_error_le_of_normalizationLabels_and_hasse
    {P : Type*} [DecidableEq P]
    (alpha beta : K) (d e : ℕ) (hd : 0 < d) (he : 0 < e) (hbeta : beta ≠ 0)
    (projectivePoints projectiveBoundary : Finset P)
    (hboundarySubset : projectiveBoundary ⊆ projectivePoints)
    (modelComparison :
      ↥(affineSplitTraceCoverZeros K alpha beta d e) ≃
        ↥(projectivePoints \ projectiveBoundary))
    (boundaryLabels :
      ↥projectiveBoundary → splitTraceNormalizationBoundaryLabels d e)
    (hboundaryLabels : Function.Injective boundaryLabels)
    (genus genusCoefficient : ℕ)
    (hprojectiveHasse :
      |(projectivePoints.card : ℝ) - ((Fintype.card K : ℝ) + 1)| ≤
        2 * (genus : ℝ) * Real.sqrt (Fintype.card K : ℝ))
    (hgenus : genus ≤ genusCoefficient * d * e) :
    |((splitTraceCurveSolutions K alpha beta d e).card : ℝ) -
        (Fintype.card K : ℝ)| ≤
      (2 * (genusCoefficient : ℝ) + 4) *
        Real.sqrt (Fintype.card K : ℝ) * (d : ℝ) * (e : ℝ) := by
  exact splitTraceCurveSolutions_count_error_le_sqrt_mul_de_of_projectiveComparison_and_hasse
    K alpha beta d e hd he hbeta projectivePoints projectiveBoundary
      hboundarySubset modelComparison genus genusCoefficient 4 hprojectiveHasse hgenus
      (projectiveBoundary_card_le_four_mul_de_of_injective_normalizationLabels
        projectiveBoundary d e hd he boundaryLabels hboundaryLabels)

end


end BGS.Markoff
