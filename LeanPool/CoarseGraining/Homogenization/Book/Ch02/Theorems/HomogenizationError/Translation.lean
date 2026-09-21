/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.HomogenizationError.Basic

/-! # Translation -/

open scoped BigOperators MatrixOrder Matrix.Norms.Frobenius

namespace Homogenization
namespace Book
namespace Ch02

noncomputable section


/-!
# Translation Covariance for Chapter 2.5 Homogenization Error

This file proves the public basic properties of the homogenization error
`\mathcal E_{s,\infty,1}` from Sec. 2.5.
-/

/-- Translation covariance of descendant normalized-response maxima, reduced
to one-cube normalized-response covariance. -/
theorem maxDescendantNormalizedBlockResponseAtScale_translateCube_of_normalizedBlockResponseMax
    {d : ℕ} [NeZero d] (a b : TriadicCoeffFamily d) (z : Fin d → ℤ)
    (Q : TriadicCube d) (a0 : Mat d) {k : ℤ} (hk : k ≤ Q.scale)
    (hJ : ∀ R ∈ descendantsAtScale Q k,
      normalizedBlockResponseMax
          (translateCube (descendantTranslationShift (Int.toNat (Q.scale - k)) z) R)
          a a0 =
        normalizedBlockResponseMax R b a0) :
    maxDescendantNormalizedBlockResponseAtScale (translateCube z Q) k a a0 =
      maxDescendantNormalizedBlockResponseAtScale Q k b a0 := by
  unfold maxDescendantNormalizedBlockResponseAtScale
  rw [descendantsAtScale_translateCube z Q hk]
  exact finsetSupReal_image _ _ _ _ hJ

/-- Translation covariance of the scale-level response aggregation, reduced to
one-cube normalized-response covariance. -/
theorem scaleResponseAtScale_translateCube_of_normalizedBlockResponseMax
    {d : ℕ} [NeZero d] (a b : TriadicCoeffFamily d) (z : Fin d → ℤ)
    (Q : TriadicCube d) (a0 : Mat d) {k : ℤ} (hk : k ≤ Q.scale)
    (p : MultiscaleExponent)
    (hJ : ∀ R ∈ descendantsAtScale Q k,
      normalizedBlockResponseMax
          (translateCube (descendantTranslationShift (Int.toNat (Q.scale - k)) z) R)
          a a0 =
        normalizedBlockResponseMax R b a0) :
    scaleResponseAtScale (translateCube z Q) k p a a0 =
      scaleResponseAtScale Q k p b a0 := by
  cases p with
  | finite p =>
      unfold scaleResponseAtScale
      rw [descendantsAtScale_translateCube z Q hk]
      refine congrArg (fun x : ℝ => Real.rpow x (1 / p)) ?_
      refine finsetAverageReal_image _ _ ?_ _ _ ?_
      · exact (translateCube_injective
          (descendantTranslationShift (Int.toNat (Q.scale - k)) z)).injOn
      · intro R hR
        exact congrArg (fun x : ℝ => Real.rpow x (p / 2)) (hJ R hR)
  | infinity =>
      unfold scaleResponseAtScale
      exact congrArg (fun x : ℝ => Real.rpow x (1 / 2))
        (maxDescendantNormalizedBlockResponseAtScale_translateCube_of_normalizedBlockResponseMax
          a b z Q a0 hk hJ)

/-- Translation covariance of finite-`q` homogenization error, reduced to
one-cube normalized-response covariance on all descendant scales used by the
series. -/
theorem HomogenizationErrorFinite_translateCube_of_normalizedBlockResponseMax
    {d : ℕ} [NeZero d] (a b : TriadicCoeffFamily d) (z : Fin d → ℤ)
    (Q : TriadicCube d) {n : ℤ} (hn : n ≤ Q.scale) (s : ℝ)
    (p : MultiscaleExponent) (q : ℝ) (a0 : Mat d)
    (hJ : ∀ (l : ℕ) (R : TriadicCube d),
      R ∈ descendantsAtScale Q (n - (l : ℤ)) →
        normalizedBlockResponseMax
            (translateCube
              (descendantTranslationShift
                (Int.toNat (Q.scale - (n - (l : ℤ)))) z) R)
            a a0 =
          normalizedBlockResponseMax R b a0) :
    HomogenizationErrorFinite (translateCube z Q) n s p q a a0 =
      HomogenizationErrorFinite Q n s p q b a0 := by
  unfold HomogenizationErrorFinite
  refine congrArg (fun x : ℝ => Real.rpow x (1 / q)) ?_
  apply tsum_congr
  intro l
  have hk : n - (l : ℤ) ≤ Q.scale := by
    exact le_trans (sub_le_self n (by exact_mod_cast Nat.zero_le l)) hn
  have hscale :=
    scaleResponseAtScale_translateCube_of_normalizedBlockResponseMax
      (a := a) (b := b) z Q a0 (k := n - (l : ℤ)) hk p
      (by
        intro R hR
        simpa using hJ l R hR)
  simpa [translateCube] using
    congrArg (fun x => geometricWeight s q l * Real.rpow x q) hscale

/-- Translation covariance of endpoint homogenization error, reduced to
one-cube normalized-response covariance on all descendant scales used by the
supremum. -/
theorem HomogenizationErrorInfinity_translateCube_of_normalizedBlockResponseMax
    {d : ℕ} [NeZero d] (a b : TriadicCoeffFamily d) (z : Fin d → ℤ)
    (Q : TriadicCube d) {n : ℤ} (hn : n ≤ Q.scale) (s : ℝ)
    (p : MultiscaleExponent) (a0 : Mat d)
    (hJ : ∀ (l : ℕ) (R : TriadicCube d),
      R ∈ descendantsAtScale Q (n - (l : ℤ)) →
        normalizedBlockResponseMax
            (translateCube
              (descendantTranslationShift
                (Int.toNat (Q.scale - (n - (l : ℤ)))) z) R)
            a a0 =
          normalizedBlockResponseMax R b a0) :
    HomogenizationErrorInfinity (translateCube z Q) n s p a a0 =
      HomogenizationErrorInfinity Q n s p b a0 := by
  unfold HomogenizationErrorInfinity
  refine congrArg sSup ?_
  ext M
  constructor
  · rintro ⟨l, rfl⟩
    refine ⟨l, ?_⟩
    have hk : n - (l : ℤ) ≤ Q.scale := by
      exact le_trans (sub_le_self n (by exact_mod_cast Nat.zero_le l)) hn
    have hscale :=
      scaleResponseAtScale_translateCube_of_normalizedBlockResponseMax
        (a := a) (b := b) z Q a0 (k := n - (l : ℤ)) hk p
        (by
          intro R hR
          simpa using hJ l R hR)
    simpa [translateCube] using
      congrArg (fun x => Real.rpow (3 : ℝ) (-s * (l : ℝ)) * x) hscale
  · rintro ⟨l, rfl⟩
    refine ⟨l, ?_⟩
    have hk : n - (l : ℤ) ≤ Q.scale := by
      exact le_trans (sub_le_self n (by exact_mod_cast Nat.zero_le l)) hn
    have hscale :=
      scaleResponseAtScale_translateCube_of_normalizedBlockResponseMax
        (a := a) (b := b) z Q a0 (k := n - (l : ℤ)) hk p
        (by
          intro R hR
          simpa using hJ l R hR)
    simpa [translateCube] using
      congrArg (fun x => Real.rpow (3 : ℝ) (-s * (l : ℝ)) * x) hscale.symm

/-- Translation covariance of homogenization error, reduced to one-cube
normalized-response covariance. -/
theorem HomogenizationError_translateCube_of_normalizedBlockResponseMax
    {d : ℕ} [NeZero d] (a b : TriadicCoeffFamily d) (z : Fin d → ℤ)
    (Q : TriadicCube d) {n : ℤ} (hn : n ≤ Q.scale) (s : ℝ)
    (p q : MultiscaleExponent) (a0 : Mat d)
    (hJ : ∀ (l : ℕ) (R : TriadicCube d),
      R ∈ descendantsAtScale Q (n - (l : ℤ)) →
        normalizedBlockResponseMax
            (translateCube
              (descendantTranslationShift
                (Int.toNat (Q.scale - (n - (l : ℤ)))) z) R)
            a a0 =
          normalizedBlockResponseMax R b a0) :
    HomogenizationError (translateCube z Q) n s p q a a0 =
      HomogenizationError Q n s p q b a0 := by
  cases q with
  | finite q =>
      exact HomogenizationErrorFinite_translateCube_of_normalizedBlockResponseMax
        a b z Q hn s p q a0 hJ
  | infinity =>
      exact HomogenizationErrorInfinity_translateCube_of_normalizedBlockResponseMax
        a b z Q hn s p a0 hJ

/-- Translation covariance of the on-cube homogenization error, reduced to
one-cube normalized-response covariance. -/
theorem HomogenizationErrorOnCube_translateCube_of_normalizedBlockResponseMax
    {d : ℕ} [NeZero d] (a b : TriadicCoeffFamily d) (z : Fin d → ℤ)
    (Q : TriadicCube d) (s : ℝ) (p q : MultiscaleExponent) (a0 : Mat d)
    (hJ : ∀ (l : ℕ) (R : TriadicCube d),
      R ∈ descendantsAtScale Q (Q.scale - (l : ℤ)) →
        normalizedBlockResponseMax (translateCube (descendantTranslationShift l z) R)
            a a0 =
          normalizedBlockResponseMax R b a0) :
    HomogenizationErrorOnCube (translateCube z Q) s p q a a0 =
      HomogenizationErrorOnCube Q s p q b a0 := by
  unfold HomogenizationErrorOnCube
  refine HomogenizationError_translateCube_of_normalizedBlockResponseMax
    a b z Q le_rfl s p q a0 ?_
  intro l R hR
  have hnat :
      Int.toNat (Q.scale - (Q.scale - (l : ℤ))) = l := by
    simp
  simpa [hnat] using hJ l R hR

end

end Ch02
end Book
end Homogenization
