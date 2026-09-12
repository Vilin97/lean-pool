/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

import LeanPool.MetricCodes.SpectralDecomposition

/-!
# Binary and spherical code bounds

The unconditional characteristic-minor argument and the final headline theorems.
-/

noncomputable section MetricCodesNoncomputable

namespace MetricCodes

namespace Spherical

section


open scoped BigOperators InnerProductSpace

namespace HigherYoungAllRankActualProjectedAxisCompletion

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCanonicalBoxActualForward
open HigherHarmonicYoung.AllRankCanonicalBoxFischerRecurrenceOfCharacteristicMinor
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCanonicalBoxProjectedAxisWitness
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCartanCharacteristicProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAxisCompressedCharacteristicMinor
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCanonicalPhysicalSignedSpan
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCartanHodgeSelector
open MetricCodes.Spherical.HigherHierarchy
open MetricCodes.Spherical.HigherHierarchyActualBoxSufficiency
open MetricCodes.Spherical.HigherProjectionInstantiation
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungActualGraphAssembly
open MetricCodes.Spherical.HigherYoungAllRankActualBoxInstantiation
open MetricCodes.Spherical.HigherYoungAllRankActualProjectedAxisAssembly
open MetricCodes.Spherical.HigherYoungAllRankCanonicalBoxReverseRange
open MetricCodes.Spherical.HigherYoungAllRankStrongStableActualBoxSufficiency

theorem fixedLevelHierarchyCodeBound_of_extraStrongCanonicalFischerRecurrence
    (hrecurrence : ∀ {r m n : ℕ}
      (a : Fin (r + 2) → ℝ) (b : Fin (r + 1) → ℝ),
      Interlacing a b → 0 < a (Fin.last (r + 1)) →
      2 * (r + 2) + 5 ≤ n + 1 →
      (hstable : ∀ v : RectangularVertices.Vertex (r + 1) m,
        FiniteInterlacing (n + 1)
          (RectangularVertices.signature a (n + 1) v)
          (flooredCoordinates b (n + 1))) →
      ∀ (low high : BoxIndex (r + 1) m)
        (row : Fin (r + 2))
        (_ : boxSignature (m := m) a (n + 1) high =
          raiseWeight (boxSignature (m := m) a (n + 1) low) row),
        CanonicalBoxAdjacentFischerRecurrence a b hstable
          (fun i => canonicalBoxPositiveFischerGram a b hstable i)
          low high row) :
    FixedLevelHierarchyCodeBound := by
  classical
  apply fixedLevelHierarchyCodeBound_of_extraStrongStableProjectedAxis
  intro r m n a b hinterlacing hlast hnextra hstable
  cases n with
  | zero => omega
  | succ n =>
      have hnstrong : 2 * (r + 1) + 5 ≤ n + 1 := by omega
      let hgram := fun i => canonicalBoxPositiveFischerGram a b hstable i
      let fibre := canonicalBoxGelfandTsetlinFibre a b hstable hgram
      let o := boxAxis (n + 1) (by omega)
      refine ⟨o, fibre, ?_⟩
      intro target source h
      refine ⟨canonicalBoxProjectedAxisWitness a b hstable hgram o ?_
        target source h⟩
      intro low high row hrow
      exact canonicalBoxEdgeAxisDataOfPolynomialData a b hstable hgram
        low high row hrow
        (canonicalBoxForwardPolynomialData_of_recurrence
          a b hstable hgram low high row hrow
          (hrecurrence a b hinterlacing hlast hnextra hstable
            low high row hrow))
        (canonicalBoxReverseAxisRange_of_strongStable a b hstable hgram
          hnstrong low high row hrow)

private def ActualBoxAxisCharacteristicMinor
    {r m n : ℕ}
    (a : Fin (r + 2) → ℝ) (b : Fin (r + 1) → ℝ)
    (hstable : ∀ v : RectangularVertices.Vertex (r + 1) m,
      FiniteInterlacing (n + 1)
        (RectangularVertices.signature a (n + 1) v)
        (flooredCoordinates b (n + 1)))
    (hgram : ∀ i : BoxIndex (r + 1) m,
      PositiveGelfandTsetlinFischerGram (n := n)
        (boxSignature (m := m) a (n + 1) i)
        (Weyl.flooredWeight b (n + 1))
        (boxSignature_interlaces a b hstable i))
    (low : BoxIndex (r + 1) m) : Prop :=
  ∀ p q : HarmonicYoungSpace (n := n)
      (Weyl.flooredWeight b (n + 1)),
    gtAxisCompressedCharacteristicMinor
        (boxSignature (m := m) a (n + 1) low)
        (Weyl.flooredWeight b (n + 1))
        (boxSignature_interlaces a b hstable low)
        (hgram low) p q =
      Polynomial.C ⟪p, q⟫_ℝ *
        channelNumeratorPolynomial (wallShift (n + 1) (r + 1))
          (HigherChannel.stabilizerShift (n + 1)
            (Weyl.flooredWeight b (n + 1)))

private def ActualBoxSelectedAxisProjectorAgreement
    {r m n : ℕ}
    (a : Fin (r + 2) → ℝ) (b : Fin (r + 1) → ℝ)
    (hstable : ∀ v : RectangularVertices.Vertex (r + 1) m,
      FiniteInterlacing (n + 1)
        (RectangularVertices.signature a (n + 1) v)
        (flooredCoordinates b (n + 1)))
    (hgram : ∀ i : BoxIndex (r + 1) m,
      PositiveGelfandTsetlinFischerGram (n := n)
        (boxSignature (m := m) a (n + 1) i)
        (Weyl.flooredWeight b (n + 1))
        (boxSignature_interlaces a b hstable i))
    (low : BoxIndex (r + 1) m) (row : Fin (r + 2)) : Prop :=
  ∀ p : HarmonicYoungSpace (n := n)
      (Weyl.flooredWeight b (n + 1)),
    allRankCartanCharacteristicProjector
        (boxSignature (m := m) a (n + 1) low) (row, true)
        (canonicalGelfandTsetlinAxisTensor
          (boxSignature (m := m) a (n + 1) low)
          (Weyl.flooredWeight b (n + 1))
          (boxSignature_interlaces a b hstable low) (hgram low) p) =
      gtSelectedRowClebschRangeProjector
        (boxSignature (m := m) a (n + 1) low) row
        (canonicalGelfandTsetlinAxisTensor
          (boxSignature (m := m) a (n + 1) low)
          (Weyl.flooredWeight b (n + 1))
          (boxSignature_interlaces a b hstable low) (hgram low) p)

theorem fixedLevelHierarchyCodeBound_of_actualCharacteristicMinorAndProjector
    (hedges : ∀ {r m n : ℕ}
      (a : Fin (r + 2) → ℝ) (b : Fin (r + 1) → ℝ),
      Interlacing a b → 0 < a (Fin.last (r + 1)) →
      2 * (r + 2) + 5 ≤ n + 1 →
      (hstable : ∀ v : RectangularVertices.Vertex (r + 1) m,
        FiniteInterlacing (n + 1)
          (RectangularVertices.signature a (n + 1) v)
          (flooredCoordinates b (n + 1))) →
      ∀ (low high : BoxIndex (r + 1) m)
        (row : Fin (r + 2))
        (_ : boxSignature (m := m) a (n + 1) high =
          raiseWeight (boxSignature (m := m) a (n + 1) low) row),
        ActualBoxAxisCharacteristicMinor a b hstable
          (fun i => canonicalBoxPositiveFischerGram a b hstable i) low ∧
        ActualBoxSelectedAxisProjectorAgreement a b hstable
          (fun i => canonicalBoxPositiveFischerGram a b hstable i)
          low row) :
    FixedLevelHierarchyCodeBound := by
  apply fixedLevelHierarchyCodeBound_of_extraStrongCanonicalFischerRecurrence
  intro r m n a b hinterlacing hlast hnextra hstable low high row hrow
  let hgram := fun i => canonicalBoxPositiveFischerGram a b hstable i
  obtain ⟨hminor, hselected⟩ :=
    hedges a b hinterlacing hlast hnextra hstable low high row hrow
  have hnstrong : 2 * (r + 1) + 5 ≤ n + 1 := by omega
  exact canonicalBoxAdjacentFischerRecurrence_of_minor_of_strongStable
    a b hstable hgram low high row hrow hnstrong hminor hselected

theorem fixedLevelHierarchyCodeBound_of_actualCharacteristicMinor
    (hminor : ∀ {r m n : ℕ}
      (a : Fin (r + 2) → ℝ) (b : Fin (r + 1) → ℝ),
      Interlacing a b → 0 < a (Fin.last (r + 1)) →
      2 * (r + 2) + 5 ≤ n + 1 →
      (hstable : ∀ v : RectangularVertices.Vertex (r + 1) m,
        FiniteInterlacing (n + 1)
          (RectangularVertices.signature a (n + 1) v)
          (flooredCoordinates b (n + 1))) →
      ∀ low : BoxIndex (r + 1) m,
        ActualBoxAxisCharacteristicMinor a b hstable
          (fun i => canonicalBoxPositiveFischerGram a b hstable i) low) :
    FixedLevelHierarchyCodeBound := by
  apply fixedLevelHierarchyCodeBound_of_actualCharacteristicMinorAndProjector
  intro r m n a b hinterlacing hlast hn hstable low high row hrow
  refine ⟨hminor a b hinterlacing hlast hn hstable low, ?_⟩
  let lam := boxSignature (m := m) a (n + 1) low
  let mu := Weyl.flooredWeight b (n + 1)
  let h := boxSignature_interlaces a b hstable low
  let hgram := canonicalBoxPositiveFischerGram a b hstable low
  have hfinite : FiniteInterlacing (n + 1) lam mu := by
    constructor
    · exact (hstable
        ((Fintype.equivFin (RectangularVertices.Vertex (r + 1) m)).symm low)).1
    · exact h
  have hdom : Antitone lam := h.antitone_ambient
  have hhigh : Antitone (raiseWeight lam row) := by
    rw [← hrow]
    exact (boxSignature_interlaces a b hstable high).antitone_ambient
  intro p
  exact allRankCartanCharacteristicProjector_canonicalAxis_eq_physicalClebsch
    lam mu h hgram hfinite hdom row hhigh hn p

end HigherYoungAllRankActualProjectedAxisCompletion

end

namespace HigherHarmonicYoung

section


open scoped BigOperators InnerProductSpace TensorProduct

namespace AllRankGTTerminalNegativeProjectorVanishing

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCartanCharacteristicProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAxisCompressedCharacteristicMinor
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriActualChannels
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriSourceSignatureInjectivity

theorem allRankCartanCharacteristicProjector_last_false_eq_zero
    {r n : ℕ} (hn : 2 * r + 4 ≤ n)
    (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam)
    (hzero : lam (Fin.last r) = 0)
    (mu : Fin r → ℕ) (hfinite : FiniteInterlacing n lam mu) :
    allRankCartanCharacteristicProjector (n := n)
        lam (Fin.last r, false) = 0 := by
  let P := allRankCartanCharacteristicProjector (n := n)
    lam (Fin.last r, false)
  let A := paddedOrthogonalTensorPieriChannel hn lam hdom
  have hle : (⨆ i : PaddedPieriChannel lam,
      LinearMap.range (A i).toLinearMap) ≤ LinearMap.ker P := by
    apply iSup_le
    intro i
    rintro _ ⟨q, rfl⟩
    change P (A i q) = 0
    cases i with
    | inl row =>
        change allRankCartanCharacteristicProjector lam
          (Fin.last r, false)
            ((paddedOrthogonalTensorPieriChannel hn lam hdom
              (Sum.inl row)).toLinearMap q) = 0
        have hraise := allRankCartanCharacteristicProjector_raise_channel
          lam mu hfinite (Fin.last r, false) row.val
          (paddedOrthogonalTensorPieriChannel hn lam hdom
            (Sum.inl row)).toLinearMap
          (paddedOrthogonalTensorPieriChannel_rotation_intertwine
            hn lam hdom (Sum.inl row)) q
        rw [ite_eq_right (by simp only [Prod.mk.injEq, Bool.false_eq_true, and_false,
          not_false_eq_true])] at hraise
        exact hraise
    | inr row =>
        have hsource : lam =
            raiseWeight (paddedPieriSource lam (Sum.inr row)) row.val :=
          (raiseWeight_loweredInternalYoungWeight
            lam row.val row.property.1).symm
        change allRankCartanCharacteristicProjector lam
          (Fin.last r, false)
            ((paddedOrthogonalTensorPieriChannel hn lam hdom
              (Sum.inr row)).toLinearMap q) = 0
        rw [allRankCartanCharacteristicProjector_lower_channel
          lam mu hfinite (Fin.last r, false) row.val
          (paddedPieriSource lam (Sum.inr row)) hsource
          (paddedOrthogonalTensorPieriChannel hn lam hdom
            (Sum.inr row)).toLinearMap
          (paddedOrthogonalTensorPieriChannel_rotation_intertwine
            hn lam hdom (Sum.inr row))]
        have hne : (Fin.last r, false) ≠ (row.val, false) := by
          intro heq
          have hrow := congrArg Prod.fst heq
          change Fin.last r = row.val at hrow
          have hpos := row.property.1
          rw [← hrow, hzero] at hpos
          omega
        simp only [hne, ↓reduceIte]
  rw [paddedOrthogonalTensorPieri_iSup_range_eq_top hn lam hdom hzero] at hle
  apply LinearMap.ext
  intro x
  have hx := hle (show x ∈ (⊤ : Submodule ℝ
    (SpherePacking.Euclidean n ⊗[ℝ]
      HarmonicYoungSpace (n := n) lam)) from trivial)
  exact hx

theorem signedCharacteristicProjector_last_false_eq_zero
    {r n : ℕ} (hn : 2 * r + 4 ≤ n)
    (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam)
    (hzero : lam (Fin.last r) = 0)
    (mu : Fin r → ℕ) (hfinite : FiniteInterlacing n lam mu) :
    signedCharacteristicProjector
      (HigherChannel.ambientShift n lam)
      (gtRelativeCasimir (n := n) lam) (Fin.last r, false) = 0 :=
  allRankCartanCharacteristicProjector_last_false_eq_zero
    hn lam hdom hzero mu hfinite

theorem gtAxisCompressedSignedProjectorCoefficient_last_false_eq_zero
    {r n : ℕ} (hn : 2 * (r + 1) + 4 ≤ n + 1)
    (lam : Fin (r + 2) → ℕ) (mu : Fin (r + 1) → ℕ)
    (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (hdom : Antitone lam) (hzero : lam (Fin.last (r + 1)) = 0)
    (hfinite : FiniteInterlacing (n + 1) lam mu)
    (p q : HarmonicYoungSpace (n := n) mu) :
    gtAxisCompressedSignedProjectorCoefficient
      lam mu h hgram p q (Fin.last (r + 1), false) = 0 := by
  unfold gtAxisCompressedSignedProjectorCoefficient
  rw [signedCharacteristicProjector_last_false_eq_zero
    hn lam hdom hzero mu hfinite]
  simp only [canonicalGelfandTsetlinAxisTensor_apply, EuclideanSpace.basisFun_apply,
    canonicalGelfandTsetlinFibre_apply, TensorProduct.tmul_smul, map_smul, LinearMap.zero_apply,
    smul_zero, inner_zero_right]

end AllRankGTTerminalNegativeProjectorVanishing

end

section


open scoped InnerProductSpace

namespace AllRankGTAbsentWallCharacteristicFactor

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAxisCompressedCharacteristicMinor
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTerminalNegativeProjectorVanishing
open MetricCodes.Spherical.HigherRepresentationGraph (Interlaces)
open MetricCodes.Spherical.HigherYoungAllRankGTCharacteristicResidue

theorem ambientShift_last_eq_wallShift_of_last_eq_zero
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (hlast : lam (Fin.last (r + 1)) = 0) :
    ambientShift (n + 1) lam (Fin.last (r + 1)) =
      wallShift (n + 1) (r + 1) := by
  rw [ambientShift_last, hlast]
  norm_num

theorem signedNode_last_false_eq_neg_wallShift
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (hlast : lam (Fin.last (r + 1)) = 0) :
    signedNode (ambientShift (n + 1) lam)
        (Fin.last (r + 1), false) =
      -(wallShift (n + 1) (r + 1)) := by
  simp only [signedNode, Bool.false_eq_true, ↓reduceIte]
  rw [ambientShift_last_eq_wallShift_of_last_eq_zero lam hlast]

theorem gtAxisCompressedCharacteristicMinor_eval_neg_wallShift
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (hfinite : FiniteInterlacing (n + 1) lam mu)
    (hlast : lam (Fin.last (r + 1)) = 0)
    (p q : HarmonicYoungSpace (n := n) mu) :
    (gtAxisCompressedCharacteristicMinor lam mu h hgram p q).eval
        (-(wallShift (n + 1) (r + 1))) =
      (gtChannelCharacteristicPolynomial (n + 1) lam).derivative.eval
          (-(wallShift (n + 1) (r + 1))) *
        gtAxisCompressedSignedProjectorCoefficient
          lam mu h hgram p q (Fin.last (r + 1), false) := by
  simpa only [signedNode_last_false_eq_neg_wallShift lam hlast] using
    gtAxisCompressedCharacteristicMinor_eval_signedNode lam mu h hgram hfinite p q (Fin.last (r
      + 1), false)

theorem gtAxisCompressedCharacteristicMinor_eval_neg_wallShift_eq_zero_iff
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (hfinite : FiniteInterlacing (n + 1) lam mu)
    (hlast : lam (Fin.last (r + 1)) = 0)
    (p q : HarmonicYoungSpace (n := n) mu) :
    (gtAxisCompressedCharacteristicMinor lam mu h hgram p q).eval
        (-(wallShift (n + 1) (r + 1))) = 0 ↔
      gtAxisCompressedSignedProjectorCoefficient
        lam mu h hgram p q (Fin.last (r + 1), false) = 0 := by
  rw [gtAxisCompressedCharacteristicMinor_eval_neg_wallShift
    lam mu h hgram hfinite hlast p q, mul_eq_zero]
  have hderivative :
      (gtChannelCharacteristicPolynomial (n + 1) lam).derivative.eval
          (-(wallShift (n + 1) (r + 1))) ≠ 0 := by
    simpa only [ne_eq, signedNode_last_false_eq_neg_wallShift lam hlast] using
      (FiniteInterlacing.gtChannelCharacteristic_derivative_eval_ne_zero hfinite (Fin.last (r +
        1)) false)
  simp only [hderivative, false_or]

theorem gtAxisCompressedCharacteristicMinor_eval_neg_wallShift_eq_zero
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (hfinite : FiniteInterlacing (n + 1) lam mu)
    (hlast : lam (Fin.last (r + 1)) = 0)
    (p q : HarmonicYoungSpace (n := n) mu)
    (hforbidden : gtAxisCompressedSignedProjectorCoefficient
      lam mu h hgram p q (Fin.last (r + 1), false) = 0) :
    (gtAxisCompressedCharacteristicMinor lam mu h hgram p q).eval
      (-(wallShift (n + 1) (r + 1))) = 0 :=
  (gtAxisCompressedCharacteristicMinor_eval_neg_wallShift_eq_zero_iff
    lam mu h hgram hfinite hlast p q).2 hforbidden

theorem gtAxisCompressedCharacteristicMinor_eval_neg_wallShift_eq_zero_of_last_eq_zero
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (hfinite : FiniteInterlacing (n + 1) lam mu)
    (hlast : lam (Fin.last (r + 1)) = 0)
    (p q : HarmonicYoungSpace (n := n) mu) :
    (gtAxisCompressedCharacteristicMinor lam mu h hgram p q).eval
      (-(wallShift (n + 1) (r + 1))) = 0 := by
  apply gtAxisCompressedCharacteristicMinor_eval_neg_wallShift_eq_zero
    lam mu h hgram hfinite hlast p q
  exact gtAxisCompressedSignedProjectorCoefficient_last_false_eq_zero
    hfinite.1 lam mu h hgram h.antitone_ambient hlast hfinite p q

end AllRankGTAbsentWallCharacteristicFactor

end

section


open scoped BigOperators InnerProductSpace TensorProduct

namespace AllRankGTPhysicalInvalidRowProjectorVanishing

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCartanCharacteristicInterpolation
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAbsentSignedProjectorOnRetainedSpan
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAppendedPieriPhysicalAxisOrthogonality
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAxisCompressedCharacteristicMinor
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTIllegalStabilizerIntertwiner
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTInvalidNonterminalProjectorVanishing
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTInvalidRowCharacteristicMinorVanishing
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTNoninterlacingTensorChannelAxisOrthogonality
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirZeroRowTransport
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransportedPieriOrthogonality
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankPaddedLowerClebschIntertwining
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankZeroRowTensorCasimirConjugacy
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching
open MetricCodes.Spherical.HigherHarmonicYoung.ClebschRotation
open MetricCodes.Spherical.HigherHarmonicYoung.CrossGram
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungAllRankGTAppendedRowLegality
open MetricCodes.Spherical.HigherYoungAllRankGTArrowheadSchurComplement
open MetricCodes.Spherical.HigherYoungAllRankGTAxisTensorRotationIntertwining
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriActualChannels
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriSourceSignatureInjectivity
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankTensorClebschCompleteness
open MetricCodes.Spherical.HigherYoungPenultimateRowProjectedLower
open MetricCodes.Spherical.ThreeRowYoungBranching

theorem interlaces_of_appendZeroWeight
    {r : ℕ} (lam : Fin (r + 2) → ℕ) (mu : Fin (r + 1) → ℕ)
    (h : Interlaces (appendZeroWeight lam) (appendZeroWeight mu)) :
    Interlaces lam mu := by
  intro row
  constructor
  · simpa only [appendZeroWeight_castSucc] using (h row.castSucc).1
  · have hcast : row.castSucc.succ = row.succ.castSucc := by
      apply Fin.ext
      rfl
    have hrow := (h row.castSucc).2
    rw [hcast] at hrow
    simpa only [appendZeroWeight_castSucc] using hrow

theorem pieri_crossGram_intertwines_of_skew
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ)
    (i : PaddedPieriChannel (appendZeroWeight lam))
    (A : HarmonicYoungSpace (n := n + 1)
        (paddedPieriSource (appendZeroWeight lam) i) →ₗ[ℝ]
      (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
        HarmonicYoungSpace (n := n + 1) (appendZeroWeight lam)))
    (B : HarmonicYoungSpace (n := n)
        (appendZeroWeight (appendZeroWeight mu)) →ₗ[ℝ]
      (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
        HarmonicYoungSpace (n := n + 1) (appendZeroWeight lam)))
    (R : HarmonicYoungSpace (n := n + 1)
        (paddedPieriSource (appendZeroWeight lam) i) →ₗ[ℝ]
      HarmonicYoungSpace (n := n + 1)
        (paddedPieriSource (appendZeroWeight lam) i))
    (T : HarmonicYoungSpace (n := n)
        (appendZeroWeight (appendZeroWeight mu)) →ₗ[ℝ]
      HarmonicYoungSpace (n := n)
        (appendZeroWeight (appendZeroWeight mu)))
    (S : (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
        HarmonicYoungSpace (n := n + 1) (appendZeroWeight lam)) →ₗ[ℝ]
      (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
        HarmonicYoungSpace (n := n + 1) (appendZeroWeight lam)))
    (hR : R.adjoint = -R)
    (hS : S.adjoint = -S)
    (hA : A.comp R = S.comp A)
    (hB : B.comp T = S.comp B) :
    (A.adjoint.comp B).comp T = R.comp (A.adjoint.comp B) :=
  crossGram_intertwines_of_skew A B R T S hR hS hA hB

theorem physicalPaddedPieriChannel_adjoint_canonicalAxis_eq_zero_of_not_interlaces
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (hdom : Antitone lam)
    (hn : 2 * (r + 2) + 5 ≤ n + 1)
    (i : PaddedPieriChannel (appendZeroWeight lam))
    (hbad : ¬ Interlaces (paddedPieriSource (appendZeroWeight lam) i)
      (appendZeroWeight mu))
    (p : HarmonicYoungSpace (n := n) mu) :
    (physicalPaddedPieriChannel (n := n + 1) (by omega) lam
      (appendZeroWeight_antitone lam hdom) i).toLinearMap.adjoint
        (canonicalGelfandTsetlinAxisTensor lam mu h hgram p) = 0 := by
  let hpadded := appendZeroWeight_antitone lam hdom
  let C := (paddedOrthogonalTensorPieriChannel
    (by omega : 2 * (r + 2) + 4 ≤ n + 1)
    (appendZeroWeight lam) hpadded i).toLinearMap
  let A := originalPaddedSelectedAxisTensor lam mu h hgram
  let Z := appendZeroRowIsometryEquiv (n := n) mu
  let W := appendZeroRowIsometryEquiv (n := n) (appendZeroWeight mu)
  let T := zeroRowTensorIsometryEquiv (n := n + 1) lam
  have hcross : C.adjoint.comp A = 0 := by
    apply illegalYoungStabilizerIntertwiner_eq_zero
      (paddedPieriSource (appendZeroWeight lam) i)
      (appendZeroWeight mu) (by omega)
      (paddedPieriSource_antitone (appendZeroWeight lam) i)
      (appendZeroWeight_antitone mu
        (interlaces_antitone_stabilizer h)) hbad
    intro a b
    apply pieri_crossGram_intertwines_of_skew lam mu i C A
      (youngAmbientRotation
        (paddedPieriSource (appendZeroWeight lam) i)
          a.castSucc b.castSucc)
      (youngAmbientRotation (appendZeroWeight (appendZeroWeight mu)) a b)
      (tensorAmbientRotation (appendZeroWeight lam)
        a.castSucc b.castSucc)
      (youngAmbientRotation_adjoint
        (paddedPieriSource (appendZeroWeight lam) i)
          a.castSucc b.castSucc)
      (tensorAmbientRotation_adjoint (appendZeroWeight lam)
        a.castSucc b.castSucc)
    · exact paddedOrthogonalTensorPieriChannel_rotation_intertwine
        (by omega) (appendZeroWeight lam) hpadded i
          a.castSucc b.castSucc
    · exact originalPaddedSelectedAxisTensor_rotation_intertwine
        lam mu h hgram a b
  have hz := LinearMap.congr_fun hcross (W (Z p))
  have hC : C.adjoint (T
      (canonicalGelfandTsetlinAxisTensor lam mu h hgram p)) = 0 := by
    change C.adjoint
      (T (canonicalGelfandTsetlinAxisTensor lam mu h hgram
        (Z.symm (W.symm (W (Z p)))))) = 0 at hz
    simpa only [canonicalGelfandTsetlinAxisTensor_apply, EuclideanSpace.basisFun_apply,
      canonicalGelfandTsetlinFibre_apply, TensorProduct.tmul_smul, map_smul, smul_eq_zero,
      inv_eq_zero, LinearIsometryEquiv.symm_apply_apply] using hz
  apply ext_inner_left ℝ
  intro q
  rw [inner_zero_right, LinearMap.adjoint_inner_right]
  change ⟪T.symm (C q),
    canonicalGelfandTsetlinAxisTensor lam mu h hgram p⟫_ℝ = 0
  calc
    ⟪T.symm (C q),
      canonicalGelfandTsetlinAxisTensor lam mu h hgram p⟫_ℝ =
        ⟪canonicalGelfandTsetlinAxisTensor lam mu h hgram p,
          T.symm (C q)⟫_ℝ :=
            real_inner_comm
              (canonicalGelfandTsetlinAxisTensor lam mu h hgram p)
              (T.symm (C q))
    _ = ⟪T (canonicalGelfandTsetlinAxisTensor lam mu h hgram p), C q⟫_ℝ := by
          rw [← T.inner_map_map,
            LinearIsometryEquiv.apply_symm_apply]
    _ = ⟪C.adjoint
        (T (canonicalGelfandTsetlinAxisTensor lam mu h hgram p)), q⟫_ℝ :=
          (LinearMap.adjoint_inner_left C q _).symm
    _ = 0 := by
      rw [hC, young_inner_eq_polynomialInner,
        SpherePacking.Fischer.polynomialInner_comm]
      exact SpherePacking.fischer_polynomialInner_zero_right _ _

theorem canonicalAxis_mem_retainedPhysicalPieriSpan
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (hdom : Antitone lam)
    (hn : 2 * (r + 2) + 5 ≤ n + 1)
    (p : HarmonicYoungSpace (n := n) mu) :
    canonicalGelfandTsetlinAxisTensor lam mu h hgram p ∈
      ⨆ i : {j : PaddedPieriChannel (appendZeroWeight lam) //
        retainedPaddedPieriChannel lam j},
        LinearMap.range
          (physicalPaddedPieriChannel (n := n + 1) (by omega) lam
            (appendZeroWeight_antitone lam hdom) i.val).toLinearMap := by
  classical
  let hfamily : 2 * (r + 2) + 4 ≤ n + 1 := by omega
  let hpadded := appendZeroWeight_antitone lam hdom
  let A := physicalPaddedPieriChannel hfamily lam hpadded
  apply orthogonalCompleteBranch_mem_selected_iSup A
    (physicalPaddedPieriChannel_inner_eq_zero hfamily lam hpadded)
    (physicalPaddedPieriChannel_finrank hfamily lam hpadded)
    (retainedPaddedPieriChannel lam)
    (canonicalGelfandTsetlinAxisTensor lam mu h hgram p)
  intro i hnot q
  cases i with
  | inl row =>
      change ¬ row.val ≠ Fin.last (r + 2) at hnot
      have hlast : row.val = Fin.last (r + 2) := Classical.byContradiction hnot
      rcases row with ⟨row, hsource⟩
      dsimp at hlast
      subst row
      exact paddedOrthogonalTensorPieriChannel_appended_originalCanonicalAxis_orthogonal
        lam mu h hgram hpadded hsource hn p q
  | inr row =>
      exact (hnot trivial).elim

theorem signedCharacteristicProjector_canonicalAxis_eq_zero_of_matching_noninterlacing
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (hfinite : FiniteInterlacing (n + 1) lam mu)
    (hn : 2 * (r + 2) + 5 ≤ n + 1)
    (selected : Fin (r + 2) × Bool)
    (hbad : ∀ i : {j : PaddedPieriChannel (appendZeroWeight lam) //
        retainedPaddedPieriChannel lam j},
      retainedPaddedPieriSignedNode lam i = selected →
        ¬ Interlaces (retainedPaddedPieriPhysicalSource lam i) mu)
    (p : HarmonicYoungSpace (n := n) mu) :
    signedCharacteristicProjector (HigherChannel.ambientShift (n + 1) lam)
      (gtRelativeCasimir lam) selected
      (canonicalGelfandTsetlinAxisTensor lam mu h hgram p) = 0 := by
  classical
  let hfamily : 2 * (r + 2) + 4 ≤ n + 1 := by omega
  let hpadded := appendZeroWeight_antitone lam hfinite.antitone_ambient
  let A := physicalPaddedPieriChannel hfamily lam hpadded
  change gtCharacteristicProjector lam selected
    (canonicalGelfandTsetlinAxisTensor lam mu h hgram p) = 0
  apply gtCharacteristicProjector_apply_eq_zero_of_matching_adjoint_zero
    lam mu hfinite (retainedPaddedPieriSignedNode lam)
    (retainedPaddedPieriSignedNode_injective lam)
    (fun i => A i.val)
  · intro i j hij u v
    exact physicalPaddedPieriChannel_inner_eq_zero hfamily lam hpadded
      i.val j.val (fun heq => hij (Subtype.ext heq)) u v
  · intro i q
    exact transportedPaddedPieriChannel_eigen_of_retained
      hfamily lam hpadded i q
  · exact canonicalAxis_mem_retainedPhysicalPieriSpan
      lam mu h hgram hfinite.antitone_ambient hn p
  · intro i hi
    apply physicalPaddedPieriChannel_adjoint_canonicalAxis_eq_zero_of_not_interlaces
      lam mu h hgram hfinite.antitone_ambient hn i.val
    intro hsource
    apply hbad i hi
    apply interlaces_of_appendZeroWeight
      (retainedPaddedPieriPhysicalSource lam i) mu
    rw [← paddedPieriSource_retained_eq_appendZero lam i]
    exact hsource

theorem retainedPhysicalSource_not_interlaces_of_invalid_negative
    {r : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (row : Fin (r + 1))
    (hbad : ¬ Interlaces lam (raiseWeight mu row))
    (i : {j : PaddedPieriChannel (appendZeroWeight lam) //
      retainedPaddedPieriChannel lam j})
    (hi : retainedPaddedPieriSignedNode lam i = (row.castSucc, false)) :
    ¬ Interlaces (retainedPaddedPieriPhysicalSource lam i) mu := by
  have hwall : lam row.castSucc = mu row :=
    (not_interlaces_raiseWeight_iff_upperWall lam mu h row).mp hbad
  rcases i with ⟨(actual | actual), hretained⟩
  · have hsign := congrArg Prod.snd hi
    simp only [retainedPaddedPieriSignedNode, Bool.true_eq_false] at hsign
  · have hrow :
        actual.val.castPred (paddedPieriLowerRow_ne_last lam actual) =
          row.castSucc := congrArg Prod.fst hi
    change ¬ Interlaces
      (loweredInternalYoungWeight lam
        (actual.val.castPred (paddedPieriLowerRow_ne_last lam actual))) mu
    rw [hrow]
    apply not_interlaces_lowerAmbient_of_upperWall lam mu row hwall
    have hcast : actual.val = row.castSucc.castSucc := by
      calc
        actual.val =
            (actual.val.castPred
              (paddedPieriLowerRow_ne_last lam actual)).castSucc :=
                (Fin.castSucc_castPred _ _).symm
        _ = row.castSucc.castSucc := congrArg Fin.castSucc hrow
    simpa only [gt_iff_lt, hcast, appendZeroWeight_castSucc] using actual.property.1

theorem retainedPhysicalSource_not_interlaces_of_invalid_positive
    {r : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (row : Fin (r + 1))
    (hbad : mu row = 0 ∨
      ¬ Interlaces lam (loweredInternalYoungWeight mu row))
    (i : {j : PaddedPieriChannel (appendZeroWeight lam) //
      retainedPaddedPieriChannel lam j})
    (hi : retainedPaddedPieriSignedNode lam i = (row.succ, true)) :
    ¬ Interlaces (retainedPaddedPieriPhysicalSource lam i) mu := by
  have hwall : lam row.succ = mu row :=
    lowerWall_of_invalid_lower_stabilizer lam mu h row hbad
  rcases i with ⟨(actual | actual), hretained⟩
  · have hrow : actual.val.castPred hretained = row.succ :=
      congrArg Prod.fst hi
    change ¬ Interlaces
      (raiseWeight lam (actual.val.castPred hretained)) mu
    rw [hrow]
    exact not_interlaces_raiseAmbient_of_lowerWall lam mu row hwall
  · have hsign := congrArg Prod.snd hi
    simp only [retainedPaddedPieriSignedNode, Bool.false_eq_true] at hsign

theorem signedCharacteristicProjector_canonicalAxis_invalid_negative_eq_zero
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (hfinite : FiniteInterlacing (n + 1) lam mu)
    (hn : 2 * (r + 2) + 5 ≤ n + 1)
    (row : Fin (r + 1))
    (hbad : ¬ Interlaces lam (raiseWeight mu row))
    (p : HarmonicYoungSpace (n := n) mu) :
    signedCharacteristicProjector (HigherChannel.ambientShift (n + 1) lam)
      (gtRelativeCasimir lam) (row.castSucc, false)
      (canonicalGelfandTsetlinAxisTensor lam mu h hgram p) = 0 := by
  apply signedCharacteristicProjector_canonicalAxis_eq_zero_of_matching_noninterlacing
    lam mu h hgram hfinite hn (row.castSucc, false) _ p
  intro i hi
  exact retainedPhysicalSource_not_interlaces_of_invalid_negative
    lam mu h row hbad i hi

theorem signedCharacteristicProjector_canonicalAxis_invalid_positive_eq_zero
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (hfinite : FiniteInterlacing (n + 1) lam mu)
    (hn : 2 * (r + 2) + 5 ≤ n + 1)
    (row : Fin (r + 1))
    (hbad : mu row = 0 ∨
      ¬ Interlaces lam (loweredInternalYoungWeight mu row))
    (p : HarmonicYoungSpace (n := n) mu) :
    signedCharacteristicProjector (HigherChannel.ambientShift (n + 1) lam)
      (gtRelativeCasimir lam) (row.succ, true)
      (canonicalGelfandTsetlinAxisTensor lam mu h hgram p) = 0 := by
  apply signedCharacteristicProjector_canonicalAxis_eq_zero_of_matching_noninterlacing
    lam mu h hgram hfinite hn (row.succ, true) _ p
  intro i hi
  exact retainedPhysicalSource_not_interlaces_of_invalid_positive
    lam mu h row hbad i hi

theorem gtAxisCompressedSignedProjectorCoefficient_invalid_negative_eq_zero
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (hfinite : FiniteInterlacing (n + 1) lam mu)
    (hn : 2 * (r + 2) + 5 ≤ n + 1)
    (row : Fin (r + 1))
    (hbad : ¬ Interlaces lam (raiseWeight mu row))
    (p q : HarmonicYoungSpace (n := n) mu) :
    gtAxisCompressedSignedProjectorCoefficient lam mu h hgram p q
      (row.castSucc, false) = 0 := by
  unfold gtAxisCompressedSignedProjectorCoefficient
  rw [signedCharacteristicProjector_canonicalAxis_invalid_negative_eq_zero
    lam mu h hgram hfinite hn row hbad q, inner_zero_right]

theorem gtAxisCompressedSignedProjectorCoefficient_invalid_positive_eq_zero
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (hfinite : FiniteInterlacing (n + 1) lam mu)
    (hn : 2 * (r + 2) + 5 ≤ n + 1)
    (row : Fin (r + 1))
    (hbad : mu row = 0 ∨
      ¬ Interlaces lam (loweredInternalYoungWeight mu row))
    (p q : HarmonicYoungSpace (n := n) mu) :
    gtAxisCompressedSignedProjectorCoefficient lam mu h hgram p q
      (row.succ, true) = 0 := by
  unfold gtAxisCompressedSignedProjectorCoefficient
  rw [signedCharacteristicProjector_canonicalAxis_invalid_positive_eq_zero
    lam mu h hgram hfinite hn row hbad q, inner_zero_right]

theorem gtAxisCompressedCharacteristicMinor_eval_negativeStabilizerNode_eq_zero_of_invalid
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (hfinite : FiniteInterlacing (n + 1) lam mu)
    (hn : 2 * (r + 2) + 5 ≤ n + 1)
    (row : Fin (r + 1))
    (hbad : ¬ Interlaces lam (raiseWeight mu row))
    (p q : HarmonicYoungSpace (n := n) mu) :
    (gtAxisCompressedCharacteristicMinor lam mu h hgram p q).eval
        (gtStabilizerArrowheadNode
          (wallShift (n + 1) (r + 1))
          (HigherChannel.stabilizerShift (n + 1) mu) (.inr (row, false))) = 0 :=
  gtAxisCompressedCharacteristicMinor_eval_negativeStabilizerNode_eq_zero
    lam mu h hgram hfinite row hbad p q
    (gtAxisCompressedSignedProjectorCoefficient_invalid_negative_eq_zero
      lam mu h hgram hfinite hn row hbad p q)

theorem gtAxisCompressedCharacteristicMinor_eval_positiveStabilizerNode_eq_zero_of_invalid
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (hfinite : FiniteInterlacing (n + 1) lam mu)
    (hn : 2 * (r + 2) + 5 ≤ n + 1)
    (row : Fin (r + 1))
    (hbad : mu row = 0 ∨
      ¬ Interlaces lam (loweredInternalYoungWeight mu row))
    (p q : HarmonicYoungSpace (n := n) mu) :
    (gtAxisCompressedCharacteristicMinor lam mu h hgram p q).eval
        (gtStabilizerArrowheadNode
          (wallShift (n + 1) (r + 1))
          (HigherChannel.stabilizerShift (n + 1) mu) (.inr (row, true))) = 0 :=
  gtAxisCompressedCharacteristicMinor_eval_positiveStabilizerNode_eq_zero
    lam mu h hgram hfinite row hbad p q
    (gtAxisCompressedSignedProjectorCoefficient_invalid_positive_eq_zero
      lam mu h hgram hfinite hn row hbad p q)

end AllRankGTPhysicalInvalidRowProjectorVanishing

end

section


open scoped BigOperators InnerProductSpace

namespace AllRankGTTransverseCharacteristicDeterminant

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAxisCompressedCharacteristicMinor
open MetricCodes.Spherical.HigherRepresentationGraph (Interlaces)
open MetricCodes.Spherical.HigherYoungAllRankGTArrowheadSchurComplement

theorem nodal_erase_coeff_card_pred
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (nodes : ι → ℝ) (i : ι) :
    (Lagrange.nodal (Finset.univ.erase i) nodes).coeff
      (Fintype.card ι - 1) = 1 := by
  have h := (Lagrange.nodal_monic
    (s := Finset.univ.erase i) (v := nodes)).leadingCoeff
  rw [Polynomial.leadingCoeff, Lagrange.natDegree_nodal] at h
  simpa only [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ] using h

theorem gtAxisCompressedCharacteristicMinor_coeff_card_pred
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (hfinite : FiniteInterlacing (n + 1) lam mu)
    (p q : HarmonicYoungSpace (n := n) mu) :
    (gtAxisCompressedCharacteristicMinor lam mu h hgram p q).coeff
      (Fintype.card (Fin (r + 2) × Bool) - 1) =
      ⟪p, q⟫_ℝ := by
  rw [gtAxisCompressedCharacteristicMinor_eq_sum_nodal_erase
    lam mu h hgram hfinite p q, Polynomial.finsetSum_coeff]
  simp_rw [Polynomial.coeff_C_mul,
    nodal_erase_coeff_card_pred
      (signedNode (ambientShift (n + 1) lam)), mul_one]
  exact sum_gtAxisCompressedSignedProjectorCoefficient
    lam mu h hgram hfinite p q

theorem polynomial_eq_C_mul_nodal_of_roots_and_topCoeff
    {ι : Type*} [Fintype ι]
    (nodes : ι → ℝ) (hinj : Function.Injective nodes)
    (P : Polynomial ℝ) (c : ℝ)
    (hdeg : P.degree < Fintype.card ι + 1)
    (hcoeff : P.coeff (Fintype.card ι) = c)
    (hroot : ∀ i : ι, P.eval (nodes i) = 0) :
    P = Polynomial.C c * Lagrange.nodal Finset.univ nodes := by
  classical
  let Q : Polynomial ℝ :=
    P - Polynomial.C c * Lagrange.nodal Finset.univ nodes
  have hqdeg : Q.degree < Fintype.card ι := by
    rw [Polynomial.degree_lt_iff_coeff_zero]
    intro k hk
    unfold Q
    rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul]
    by_cases heq : k = Fintype.card ι
    · subst k
      rw [hcoeff]
      have hmonic := (Lagrange.nodal_monic
        (s := Finset.univ) (v := nodes)).leadingCoeff
      rw [Polynomial.leadingCoeff, Lagrange.natDegree_nodal] at hmonic
      simp only [Finset.card_univ] at hmonic
      rw [hmonic]
      ring
    · have hstrict : Fintype.card ι < k := lt_of_le_of_ne hk (Ne.symm heq)
      have hpzero : P.coeff k = 0 := by
        apply Polynomial.coeff_eq_zero_of_degree_lt
        exact hdeg.trans_le (by exact_mod_cast hstrict)
      have hnzero :
          (Lagrange.nodal (Finset.univ : Finset ι) nodes).coeff k = 0 := by
        apply Polynomial.coeff_eq_zero_of_degree_lt
        rw [Lagrange.degree_nodal]
        exact_mod_cast hstrict
      rw [hpzero, hnzero, mul_zero, sub_zero]
  have hqzero : Q = 0 :=
    Polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero
      (Finset.univ : Finset ι) hinj.injOn hqdeg (by
        intro i _
        simp only [Polynomial.eval_sub, hroot i, Polynomial.eval_mul, Polynomial.eval_C,
          Lagrange.eval_nodal_at_node (Finset.mem_univ i), mul_zero, sub_self, Q])
  exact sub_eq_zero.mp hqzero

theorem gtStabilizerArrowheadNode_injective_of_gap
    {r : ℕ} (rho : ℝ) (M : Fin r → ℝ)
    (hrho : 0 < rho)
    (hgap : ∀ i : Fin r, rho + 1 / 2 ≤ M i)
    (hinj : Function.Injective M) :
    Function.Injective (gtStabilizerArrowheadNode rho M) := by
  intro x y hxy
  cases x with
  | inl x =>
      cases y with
      | inl y => cases x; cases y; rfl
      | inr y =>
          rcases y with ⟨j, b⟩
          cases b <;>
            simp only [gtStabilizerArrowheadNode] at hxy <;>
            linarith [hgap j]
  | inr x =>
      rcases x with ⟨i, a⟩
      cases y with
      | inl y =>
          cases a <;>
            simp only [gtStabilizerArrowheadNode] at hxy <;>
            linarith [hgap i]
      | inr y =>
          rcases y with ⟨j, b⟩
          cases a <;> cases b
          · have heq : M i = M j := by
              simp only [gtStabilizerArrowheadNode] at hxy
              linarith
            have hij := hinj heq
            subst j
            rfl
          · simp only [gtStabilizerArrowheadNode] at hxy
            linarith [hgap i, hgap j]
          · simp only [gtStabilizerArrowheadNode] at hxy
            linarith [hgap i, hgap j]
          · have heq : M i = M j := by
              simp only [gtStabilizerArrowheadNode] at hxy
              linarith
            have hij := hinj heq
            subst j
            rfl

theorem gtStabilizerArrowheadNode_injective_of_interlacing
    {r n : ℕ} {lam : Fin (r + 2) → ℕ}
    {mu : Fin (r + 1) → ℕ}
    (h : FiniteInterlacing (n + 1) lam mu) :
    Function.Injective
      (gtStabilizerArrowheadNode
        (wallShift (n + 1) (r + 1))
        (stabilizerShift (n + 1) mu)) := by
  apply gtStabilizerArrowheadNode_injective_of_gap
    (wallShift (n + 1) (r + 1))
    (stabilizerShift (n + 1) mu) h.wallShift_pos
  · intro i
    unfold stabilizerShift wallShift
    have hi : i.val ≤ r := by have := i.isLt; omega
    have hireal : (i.val : ℝ) ≤ r := by exact_mod_cast hi
    have hmu : (0 : ℝ) ≤ mu i := Nat.cast_nonneg _
    push_cast
    linarith
  · have hanti : Antitone mu := by
      apply Fin.antitone_iff_succ_le.mpr
      intro i
      exact (h.2 i.succ).1.trans (by
        simpa only [Fin.castSucc_succ] using (h.2 i.castSucc).2)
    have hstrict : StrictAnti (stabilizerShift (n + 1) mu) := by
      apply Fin.strictAnti_iff_succ_lt.mpr
      intro i
      have hm := hanti (Fin.castSucc_le_succ i)
      unfold stabilizerShift
      simp only [Fin.val_castSucc, Fin.val_succ]
      have hmreal : (mu i.succ : ℝ) ≤ (mu i.castSucc : ℝ) := by
        exact_mod_cast hm
      push_cast
      linarith
    exact hstrict.injective

theorem gtAxisCompressedCharacteristicMinor_eq_stabilizerArrowheadMinor_of_roots
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (hfinite : FiniteInterlacing (n + 1) lam mu)
    (p q : HarmonicYoungSpace (n := n) mu)
    (hroot : ∀ j : Unit ⊕ (Fin (r + 1) × Bool),
      (gtAxisCompressedCharacteristicMinor lam mu h hgram p q).eval
        (gtStabilizerArrowheadNode
          (wallShift (n + 1) (r + 1))
          (stabilizerShift (n + 1) mu) j) = 0) :
    gtAxisCompressedCharacteristicMinor lam mu h hgram p q =
      Polynomial.C ⟪p, q⟫_ℝ *
        gtStabilizerArrowheadMinor
          (wallShift (n + 1) (r + 1))
          (stabilizerShift (n + 1) mu) := by
  unfold gtStabilizerArrowheadMinor
  apply polynomial_eq_C_mul_nodal_of_roots_and_topCoeff
    (gtStabilizerArrowheadNode
      (wallShift (n + 1) (r + 1))
      (stabilizerShift (n + 1) mu))
    (gtStabilizerArrowheadNode_injective_of_interlacing hfinite)
  · have hdegree := gtAxisCompressedCharacteristicMinor_degree_lt
      lam mu h hgram hfinite p q
    convert hdegree using 1;
      simp [Fintype.card_sum, Fintype.card_prod,
        Fintype.card_fin, Fintype.card_bool]; ring
  · convert gtAxisCompressedCharacteristicMinor_coeff_card_pred
      lam mu h hgram hfinite p q using 2;
      simp [Fintype.card_sum, Fintype.card_prod,
        Fintype.card_fin, Fintype.card_bool]; omega
  · exact hroot

theorem gtAxisCompressedCharacteristicMinor_eq_channelNumerator_of_roots
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (hfinite : FiniteInterlacing (n + 1) lam mu)
    (p q : HarmonicYoungSpace (n := n) mu)
    (hroot : ∀ j : Unit ⊕ (Fin (r + 1) × Bool),
      (gtAxisCompressedCharacteristicMinor lam mu h hgram p q).eval
        (gtStabilizerArrowheadNode
          (wallShift (n + 1) (r + 1))
          (stabilizerShift (n + 1) mu) j) = 0) :
    gtAxisCompressedCharacteristicMinor lam mu h hgram p q =
      Polynomial.C ⟪p, q⟫_ℝ *
        channelNumeratorPolynomial
          (wallShift (n + 1) (r + 1))
          (stabilizerShift (n + 1) mu) := by
  rw [← gtStabilizerArrowheadMinor_eq_channelNumerator]
  exact gtAxisCompressedCharacteristicMinor_eq_stabilizerArrowheadMinor_of_roots
    lam mu h hgram hfinite p q hroot

end AllRankGTTransverseCharacteristicDeterminant

end

section


open scoped InnerProductSpace

namespace AllRankGTCharacteristicMinorOfValidRoots

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAxisCompressedCharacteristicMinor
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTPhysicalInvalidRowProjectorVanishing
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCharacteristicDeterminant
open MetricCodes.Spherical.HigherRepresentationGraph (Interlaces)
open MetricCodes.Spherical.HigherYoungAllRankGTArrowheadSchurComplement
open MetricCodes.Spherical.HigherYoungPenultimateRowProjectedLower

theorem gtAxisCompressedCharacteristicMinor_eq_channelNumerator_of_validRoots
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (hfinite : FiniteInterlacing (n + 1) lam mu)
    (hn : 2 * (r + 2) + 5 ≤ n + 1)
    (p q : HarmonicYoungSpace (n := n) mu)
    (hwall : (gtAxisCompressedCharacteristicMinor lam mu h hgram p q).eval
      (-(wallShift (n + 1) (r + 1))) = 0)
    (hnegative : ∀ row : Fin (r + 1),
      Interlaces lam (raiseWeight mu row) →
        (gtAxisCompressedCharacteristicMinor lam mu h hgram p q).eval
          (gtStabilizerArrowheadNode (wallShift (n + 1) (r + 1))
            (HigherChannel.stabilizerShift (n + 1) mu)
              (.inr (row, false))) = 0)
    (hpositive : ∀ row : Fin (r + 1), 0 < mu row →
      Interlaces lam (loweredInternalYoungWeight mu row) →
        (gtAxisCompressedCharacteristicMinor lam mu h hgram p q).eval
          (gtStabilizerArrowheadNode (wallShift (n + 1) (r + 1))
            (HigherChannel.stabilizerShift (n + 1) mu)
              (.inr (row, true))) = 0) :
    gtAxisCompressedCharacteristicMinor lam mu h hgram p q =
      Polynomial.C ⟪p, q⟫_ℝ *
        channelNumeratorPolynomial (wallShift (n + 1) (r + 1))
          (HigherChannel.stabilizerShift (n + 1) mu) := by
  apply gtAxisCompressedCharacteristicMinor_eq_channelNumerator_of_roots
    lam mu h hgram hfinite p q
  intro node
  cases node with
  | inl wall =>
      cases wall
      exact hwall
  | inr signed =>
      rcases signed with ⟨row, sign⟩
      cases sign with
      | false =>
          by_cases hvalid : Interlaces lam (raiseWeight mu row)
          · exact hnegative row hvalid
          · exact
              gtAxisCompressedCharacteristicMinor_eval_negativeStabilizerNode_eq_zero_of_invalid
                lam mu h hgram hfinite hn row hvalid p q
      | true =>
          by_cases hzero : mu row = 0
          · exact
              gtAxisCompressedCharacteristicMinor_eval_positiveStabilizerNode_eq_zero_of_invalid
                lam mu h hgram hfinite hn row (.inl hzero) p q
          · by_cases hvalid :
              Interlaces lam (loweredInternalYoungWeight mu row)
            · exact hpositive row (Nat.pos_of_ne_zero hzero) hvalid
            · exact
                gtAxisCompressedCharacteristicMinor_eval_positiveStabilizerNode_eq_zero_of_invalid
                  lam mu h hgram hfinite hn row (.inr hvalid) p q

end AllRankGTCharacteristicMinorOfValidRoots

end

section


open scoped BigOperators TensorProduct

namespace AllRankGTStabilizerCasimirShift

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherYoungAllRankGTArrowheadSchurComplement

theorem stabilizerShift_succ_eq_ambientShift {r n : ℕ}
    (mu : Fin (r + 1) → ℕ) (row : Fin (r + 1)) :
    stabilizerShift (n + 1) mu row = ambientShift n mu row := by
  simp only [stabilizerShift, ambientShift, Nat.cast_add, Nat.cast_one]
  ring

theorem gtStabilizerCasimir_raiseBranch_eigenvalue {r n : ℕ}
    (mu : Fin (r + 1) → ℕ) (row : Fin (r + 1)) :
    (allRankCasimirEigenvalue n mu -
      allRankCasimirEigenvalue n (raiseWeight mu row)) / 2 =
      -stabilizerShift (n + 1) mu row - 1 / 2 := by
  have h := gtRelativeCasimir_raise_eigenvalue (n := n) mu row
  rw [← stabilizerShift_succ_eq_ambientShift] at h
  linarith

theorem gtStabilizerCasimir_lowerBranch_eigenvalue {r n : ℕ}
    (mu nu : Fin (r + 1) → ℕ) (row : Fin (r + 1))
    (hnu : mu = raiseWeight nu row) :
    (allRankCasimirEigenvalue n mu -
      allRankCasimirEigenvalue n nu) / 2 =
      stabilizerShift (n + 1) mu row - 1 / 2 := by
  have h := gtRelativeCasimir_lower_eigenvalue
    (n := n) mu nu row hnu
  rw [← stabilizerShift_succ_eq_ambientShift] at h
  linarith

theorem gtStabilizerRelativeCasimir_raiseTarget_eigenvalue {r n : ℕ}
    (mu : Fin (r + 1) → ℕ) (row : Fin (r + 1)) :
    (allRankCasimirEigenvalue n mu -
      allRankCasimirEigenvalue n (raiseWeight mu row) - 1) / 2 =
      -stabilizerShift (n + 1) mu row - 1 := by
  have h := gtStabilizerCasimir_raiseBranch_eigenvalue (n := n) mu row
  linarith

theorem gtStabilizerRelativeCasimir_lowerTarget_eigenvalue {r n : ℕ}
    (mu nu : Fin (r + 1) → ℕ) (row : Fin (r + 1))
    (hnu : mu = raiseWeight nu row) :
    (allRankCasimirEigenvalue n mu -
      allRankCasimirEigenvalue n nu - 1) / 2 =
      stabilizerShift (n + 1) mu row - 1 := by
  have h := gtStabilizerCasimir_lowerBranch_eigenvalue
    (n := n) mu nu row hnu
  linarith

private def gtStabilizerShiftedRelativeCasimir {r n : ℕ}
    (nu : Fin (r + 1) → ℕ) :
    Module.End ℝ (SpherePacking.Euclidean n ⊗[ℝ]
      HarmonicYoungSpace (n := n) nu) :=
  gtRelativeCasimir nu + (1 / 2 : ℝ) • LinearMap.id

theorem gtStabilizerShiftedRelativeCasimir_raiseTarget_channel
    {r n : ℕ} (mu : Fin (r + 1) → ℕ) (row : Fin (r + 1))
    (A : HarmonicYoungSpace (n := n) mu →ₗ[ℝ]
      (SpherePacking.Euclidean n ⊗[ℝ]
        HarmonicYoungSpace (n := n) (raiseWeight mu row)))
    (hA : ∀ a b : Fin n,
      A.comp (youngAmbientRotation mu a b) =
        (ClebschRotation.tensorAmbientRotation
          (raiseWeight mu row) a b).comp A)
    (p : HarmonicYoungSpace (n := n) mu) :
    gtStabilizerShiftedRelativeCasimir (raiseWeight mu row) (A p) =
      gtStabilizerArrowheadNode (wallShift (n + 1) (r + 1))
        (stabilizerShift (n + 1) mu) (.inr (row, false)) • A p := by
  simp only [gtStabilizerShiftedRelativeCasimir, LinearMap.add_apply,
    LinearMap.smul_apply, LinearMap.id_apply,
    gtStabilizerArrowheadNode_neg]
  rw [gtRelativeCasimir_channel mu (raiseWeight mu row) A hA,
    gtStabilizerRelativeCasimir_raiseTarget_eigenvalue]
  rw [← add_smul]
  congr 1
  ring

theorem gtStabilizerShiftedRelativeCasimir_lowerTarget_channel
    {r n : ℕ} (mu nu : Fin (r + 1) → ℕ)
    (row : Fin (r + 1)) (hnu : mu = raiseWeight nu row)
    (A : HarmonicYoungSpace (n := n) mu →ₗ[ℝ]
      (SpherePacking.Euclidean n ⊗[ℝ]
        HarmonicYoungSpace (n := n) nu))
    (hA : ∀ a b : Fin n,
      A.comp (youngAmbientRotation mu a b) =
        (ClebschRotation.tensorAmbientRotation nu a b).comp A)
    (p : HarmonicYoungSpace (n := n) mu) :
    gtStabilizerShiftedRelativeCasimir nu (A p) =
      gtStabilizerArrowheadNode (wallShift (n + 1) (r + 1))
        (stabilizerShift (n + 1) mu) (.inr (row, true)) • A p := by
  simp only [gtStabilizerShiftedRelativeCasimir, LinearMap.add_apply,
    LinearMap.smul_apply, LinearMap.id_apply,
    gtStabilizerArrowheadNode_pos]
  rw [gtRelativeCasimir_channel mu nu A hA,
    gtStabilizerRelativeCasimir_lowerTarget_eigenvalue
      mu nu row hnu]
  rw [← add_smul]
  congr 1
  ring

end AllRankGTStabilizerCasimirShift

end

section


open scoped BigOperators InnerProductSpace TensorProduct

namespace AllRankGTTransverseCasimirEmbedding

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTStabilizerCasimirShift
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity
open MetricCodes.Spherical.HigherHarmonicYoung.ClebschRotation
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungAllRankGTArrowheadSchurComplement

private def gtTransverseEuclidean (n : ℕ) :
    SpherePacking.Euclidean n →ₗ[ℝ] SpherePacking.Euclidean (n + 1) where
  toFun x := WithLp.toLp 2 (Fin.snoc (WithLp.ofLp x) 0)
  map_add' x y := by
    ext i
    induction i using Fin.lastCases with
    | last => simp only [WithLp.ofLp_add, Fin.snoc_last, PiLp.add_apply, add_zero]
    | cast j => simp only [WithLp.ofLp_add, Fin.snoc_castSucc, Pi.add_apply, PiLp.add_apply]
  map_smul' c x := by
    ext i
    induction i using Fin.lastCases with
    | last => simp only [WithLp.ofLp_smul, Fin.snoc_last, Real.ringHom_apply, PiLp.smul_apply,
                smul_eq_mul, mul_zero]
    | cast j => simp only [WithLp.ofLp_smul, Fin.snoc_castSucc, Pi.smul_apply, smul_eq_mul,
                  Real.ringHom_apply, PiLp.smul_apply]

@[simp] theorem gtTransverseEuclidean_castSucc
    (n : ℕ) (x : SpherePacking.Euclidean n) (i : Fin n) :
    gtTransverseEuclidean n x i.castSucc = x i := by
  simp only [gtTransverseEuclidean, LinearMap.coe_mk, AddHom.coe_mk, Fin.snoc_castSucc]

@[simp] theorem gtTransverseEuclidean_last
    (n : ℕ) (x : SpherePacking.Euclidean n) :
    gtTransverseEuclidean n x (Fin.last n) = 0 := by
  simp only [gtTransverseEuclidean, LinearMap.coe_mk, AddHom.coe_mk, Fin.snoc_last]

theorem gtTransverseEuclidean_inner
    (n : ℕ) (x y : SpherePacking.Euclidean n) :
    ⟪gtTransverseEuclidean n x, gtTransverseEuclidean n y⟫_ℝ =
      ⟪x, y⟫_ℝ := by
  rw [PiLp.inner_apply, Fin.sum_univ_castSucc]
  simp [PiLp.inner_apply]

private def gtTransverseEuclideanIsometry (n : ℕ) :
    SpherePacking.Euclidean n →ₗᵢ[ℝ] SpherePacking.Euclidean (n + 1) :=
  (gtTransverseEuclidean n).isometryOfInner (gtTransverseEuclidean_inner n)

@[simp] theorem gtTransverseEuclideanIsometry_castSucc
    (n : ℕ) (x : SpherePacking.Euclidean n) (i : Fin n) :
    gtTransverseEuclideanIsometry n x i.castSucc = x i := by
  simp only [gtTransverseEuclideanIsometry, gtTransverseEuclidean, LinearMap.coe_isometryOfInner,
    LinearMap.coe_mk, AddHom.coe_mk, Fin.snoc_castSucc]

@[simp] theorem gtTransverseEuclideanIsometry_last
    (n : ℕ) (x : SpherePacking.Euclidean n) :
    gtTransverseEuclideanIsometry n x (Fin.last n) = 0 := by
  simp only [gtTransverseEuclideanIsometry, gtTransverseEuclidean, LinearMap.coe_isometryOfInner,
    LinearMap.coe_mk, AddHom.coe_mk, Fin.snoc_last]

theorem gtTransverseEuclideanIsometry_orthogonal_last
    (n : ℕ) (x : SpherePacking.Euclidean n) :
    ⟪gtTransverseEuclideanIsometry n x,
      EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n)⟫_ℝ = 0 := by
  rw [EuclideanSpace.inner_basisFun_real,
    gtTransverseEuclideanIsometry_last]

private def gtTransverseTensorEmbedding
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (nu : Fin (r + 1) → ℕ)
    (h : Interlaces lam nu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam nu h) :
    (SpherePacking.Euclidean n ⊗[ℝ] HarmonicYoungSpace (n := n) nu) →ₗᵢ[ℝ]
      (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
        HarmonicYoungSpace (n := n + 1) lam) :=
  TensorProduct.mapIsometry (gtTransverseEuclideanIsometry n)
    (canonicalGelfandTsetlinFibre lam nu h hgram)

@[simp] theorem gtTransverseTensorEmbedding_tmul
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (nu : Fin (r + 1) → ℕ)
    (h : Interlaces lam nu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam nu h)
    (v : SpherePacking.Euclidean n)
    (p : HarmonicYoungSpace (n := n) nu) :
    gtTransverseTensorEmbedding lam nu h hgram (v ⊗ₜ[ℝ] p) =
      gtTransverseEuclideanIsometry n v ⊗ₜ[ℝ]
        canonicalGelfandTsetlinFibre lam nu h hgram p := rfl

theorem gtTransverseTensorEmbedding_axis_inner_eq_zero
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (nu mu : Fin (r + 1) → ℕ)
    (hnu : Interlaces lam nu)
    (hnuGram : PositiveGelfandTsetlinFischerGram (n := n) lam nu hnu)
    (hmu : Interlaces lam mu)
    (hmuGram : PositiveGelfandTsetlinFischerGram (n := n) lam mu hmu)
    (x : SpherePacking.Euclidean n ⊗[ℝ]
      HarmonicYoungSpace (n := n) nu)
    (q : HarmonicYoungSpace (n := n) mu) :
    ⟪gtTransverseTensorEmbedding lam nu hnu hnuGram x,
      canonicalGelfandTsetlinAxisTensor lam mu hmu hmuGram q⟫_ℝ = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, canonicalGelfandTsetlinAxisTensor_apply,
              EuclideanSpace.basisFun_apply, canonicalGelfandTsetlinFibre_apply,
              TensorProduct.tmul_smul, inner_zero_left]
  | tmul v p =>
      rw [gtTransverseTensorEmbedding_tmul,
        canonicalGelfandTsetlinAxisTensor_apply,
        TensorProduct.inner_tmul,
        gtTransverseEuclideanIsometry_orthogonal_last]
      simp only [canonicalGelfandTsetlinFibre_apply, zero_mul]
  | add x y hx hy =>
      rw [map_add, inner_add_left, hx, hy, zero_add]

private def gtTransverseNegativeSector
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (row : Fin (r + 1))
    (hnu : Interlaces lam (raiseWeight mu row))
    (hgram : PositiveGelfandTsetlinFischerGram (n := n)
      lam (raiseWeight mu row) hnu) :
    HarmonicYoungSpace (n := n) mu →ₗ[ℝ]
      (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
        HarmonicYoungSpace (n := n + 1) lam) :=
  (gtTransverseTensorEmbedding lam (raiseWeight mu row)
    hnu hgram).toLinearMap.comp
      (youngClebschRaise (raiseWeight mu row) mu
        (sum_raiseWeight mu row) row)

private def gtTransversePositiveSector
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu nu : Fin (r + 1) → ℕ) (row : Fin (r + 1))
    (hmu : mu = raiseWeight nu row)
    (hnu : Interlaces lam nu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n)
      lam nu hnu) :
    HarmonicYoungSpace (n := n) mu →ₗ[ℝ]
      (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
        HarmonicYoungSpace (n := n + 1) lam) :=
  (gtTransverseTensorEmbedding lam nu hnu hgram).toLinearMap.comp
    (youngClebschLower nu mu
      (by rw [hmu]; exact sum_raiseWeight nu row) row)

theorem gtTransverseNegativeSector_axis_inner_eq_zero
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (row : Fin (r + 1))
    (hnu : Interlaces lam (raiseWeight mu row))
    (hnuGram : PositiveGelfandTsetlinFischerGram (n := n)
      lam (raiseWeight mu row) hnu)
    (hmu : Interlaces lam mu)
    (hmuGram : PositiveGelfandTsetlinFischerGram (n := n) lam mu hmu)
    (p q : HarmonicYoungSpace (n := n) mu) :
    ⟪gtTransverseNegativeSector lam mu row hnu hnuGram p,
      canonicalGelfandTsetlinAxisTensor lam mu hmu hmuGram q⟫_ℝ = 0 := by
  exact gtTransverseTensorEmbedding_axis_inner_eq_zero
    lam (raiseWeight mu row) mu hnu hnuGram hmu hmuGram
    (youngClebschRaise (raiseWeight mu row) mu
      (sum_raiseWeight mu row) row p) q

theorem gtTransversePositiveSector_axis_inner_eq_zero
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu nu : Fin (r + 1) → ℕ) (row : Fin (r + 1))
    (hmunu : mu = raiseWeight nu row)
    (hnu : Interlaces lam nu)
    (hnuGram : PositiveGelfandTsetlinFischerGram (n := n) lam nu hnu)
    (hmu : Interlaces lam mu)
    (hmuGram : PositiveGelfandTsetlinFischerGram (n := n) lam mu hmu)
    (p q : HarmonicYoungSpace (n := n) mu) :
    ⟪gtTransversePositiveSector lam mu nu row hmunu hnu hnuGram p,
      canonicalGelfandTsetlinAxisTensor lam mu hmu hmuGram q⟫_ℝ = 0 := by
  exact gtTransverseTensorEmbedding_axis_inner_eq_zero
    lam nu mu hnu hnuGram hmu hmuGram
    (youngClebschLower nu mu
      (by rw [hmunu]; exact sum_raiseWeight nu row) row p) q

end AllRankGTTransverseCasimirEmbedding

end

section


open scoped BigOperators InnerProductSpace TensorProduct

namespace AllRankGTTransverseTangentialCompression

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirPureAxis
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCasimirEmbedding
open MetricCodes.Spherical.HigherHarmonicYoung.ClebschRotation
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherRepresentationGraph

theorem canonicalGelfandTsetlinFibre_rotation_adjoint_compression
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (nu : Fin (r + 1) → ℕ) (h : Interlaces lam nu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam nu h)
    (a b : Fin n) :
    (canonicalGelfandTsetlinFibre lam nu h hgram).toLinearMap.adjoint.comp
        ((youngAmbientRotation lam a.castSucc b.castSucc).comp
          (canonicalGelfandTsetlinFibre lam nu h hgram).toLinearMap) =
      youngAmbientRotation nu a b := by
  rw [← canonicalGelfandTsetlinFibre_rotation_intertwine
    lam nu h hgram a b]
  rw [← LinearMap.comp_assoc,
    (canonicalGelfandTsetlinFibre lam nu h hgram).adjoint_comp_self',
    LinearMap.id_comp]

theorem gtTransverseEuclideanIsometry_rotation_intertwine
    (n : ℕ) (a b : Fin n) :
    (gtTransverseEuclideanIsometry n).toLinearMap.comp
        (euclideanAmbientRotation a b) =
      (euclideanAmbientRotation a.castSucc b.castSucc).comp
        (gtTransverseEuclideanIsometry n).toLinearMap := by
  apply LinearMap.ext
  intro v
  ext i
  induction i using Fin.lastCases with
  | last =>
      simp only [LinearMap.coe_comp, LinearIsometry.coe_toLinearMap, Function.comp_apply,
        euclideanAmbientRotation_apply, EuclideanSpace.basisFun_apply, map_sub, map_smul,
        PiLp.sub_apply, PiLp.smul_apply, gtTransverseEuclideanIsometry_last, smul_eq_mul, mul_zero,
        sub_self, gtTransverseEuclideanIsometry_castSucc, ne_eq, Fin.castSucc_ne_last,
        not_false_eq_true, PiLp.single_eq_of_ne']
  | cast i =>
      simp only [LinearMap.coe_comp, LinearIsometry.coe_toLinearMap, Function.comp_apply,
        euclideanAmbientRotation_apply, EuclideanSpace.basisFun_apply, map_sub, map_smul,
        PiLp.sub_apply, PiLp.smul_apply, gtTransverseEuclideanIsometry_castSucc, PiLp.single_apply,
        smul_eq_mul, mul_ite, mul_one, mul_zero, Fin.castSucc_inj]

theorem gtTransverseEuclideanIsometry_rotation_adjoint_compression
    (n : ℕ) (a b : Fin n) :
    (gtTransverseEuclideanIsometry n).toLinearMap.adjoint.comp
        ((euclideanAmbientRotation a.castSucc b.castSucc).comp
          (gtTransverseEuclideanIsometry n).toLinearMap) =
      euclideanAmbientRotation a b := by
  rw [← gtTransverseEuclideanIsometry_rotation_intertwine n a b]
  rw [← LinearMap.comp_assoc,
    (gtTransverseEuclideanIsometry n).adjoint_comp_self',
    LinearMap.id_comp]

theorem gtTransverseEuclideanIsometry_adjoint_basisFun_last
    (n : ℕ) :
    (gtTransverseEuclideanIsometry n).toLinearMap.adjoint
        (EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n)) = 0 := by
  apply ext_inner_right ℝ
  intro v
  rw [LinearMap.adjoint_inner_left, inner_zero_left]
  rw [real_inner_comm]
  exact gtTransverseEuclideanIsometry_orthogonal_last n v

theorem gtTransverseEuclideanIsometry_cross_rotation_compression
    (n : ℕ) (a : Fin n) :
    (gtTransverseEuclideanIsometry n).toLinearMap.adjoint.comp
        ((euclideanAmbientRotation a.castSucc (Fin.last n)).comp
          (gtTransverseEuclideanIsometry n).toLinearMap) = 0 := by
  apply LinearMap.ext
  intro v
  change
    (gtTransverseEuclideanIsometry n).toLinearMap.adjoint
      (euclideanAmbientRotation a.castSucc (Fin.last n)
        (gtTransverseEuclideanIsometry n v)) = 0
  rw [euclideanAmbientRotation_apply,
    gtTransverseEuclideanIsometry_last, zero_smul, zero_sub,
    map_neg, map_smul,
    gtTransverseEuclideanIsometry_adjoint_basisFun_last,
    smul_zero, neg_zero]

theorem gtTransverseEuclideanIsometry_cross_rotation_compression_swap
    (n : ℕ) (a : Fin n) :
    (gtTransverseEuclideanIsometry n).toLinearMap.adjoint.comp
        ((euclideanAmbientRotation (Fin.last n) a.castSucc).comp
          (gtTransverseEuclideanIsometry n).toLinearMap) = 0 := by
  apply LinearMap.ext
  intro v
  change
    (gtTransverseEuclideanIsometry n).toLinearMap.adjoint
      (euclideanAmbientRotation (Fin.last n) a.castSucc
        (gtTransverseEuclideanIsometry n v)) = 0
  rw [euclideanAmbientRotation_apply,
    gtTransverseEuclideanIsometry_last, zero_smul, sub_zero,
    map_smul,
    gtTransverseEuclideanIsometry_adjoint_basisFun_last,
    smul_zero]

theorem gtTransverseTensorEmbedding_rotationTerm_adjoint_compression
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (nu : Fin (r + 1) → ℕ) (h : Interlaces lam nu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam nu h)
    (a b : Fin (n + 1)) :
    (gtTransverseTensorEmbedding lam nu h hgram).toLinearMap.adjoint.comp
        ((TensorProduct.map (euclideanAmbientRotation a b)
          (youngAmbientRotation lam a b)).comp
          (gtTransverseTensorEmbedding lam nu h hgram).toLinearMap) =
      TensorProduct.map
        ((gtTransverseEuclideanIsometry n).toLinearMap.adjoint.comp
          ((euclideanAmbientRotation a b).comp
            (gtTransverseEuclideanIsometry n).toLinearMap))
        ((canonicalGelfandTsetlinFibre lam nu h hgram).toLinearMap.adjoint.comp
          ((youngAmbientRotation lam a b).comp
            (canonicalGelfandTsetlinFibre lam nu h hgram).toLinearMap)) := by
  change
    (TensorProduct.map
      (gtTransverseEuclideanIsometry n).toLinearMap
      (canonicalGelfandTsetlinFibre lam nu h hgram).toLinearMap).adjoint.comp
        ((TensorProduct.map (euclideanAmbientRotation a b)
          (youngAmbientRotation lam a b)).comp
          (TensorProduct.map
            (gtTransverseEuclideanIsometry n).toLinearMap
            (canonicalGelfandTsetlinFibre lam nu h hgram).toLinearMap)) = _
  rw [TensorProduct.adjoint_map]
  apply TensorProduct.ext
  ext v p
  rfl

theorem gtTransverseTensorEmbedding_tangentialTerm_adjoint_compression
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (nu : Fin (r + 1) → ℕ) (h : Interlaces lam nu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam nu h)
    (a b : Fin n) :
    (gtTransverseTensorEmbedding lam nu h hgram).toLinearMap.adjoint.comp
        ((TensorProduct.map
          (euclideanAmbientRotation a.castSucc b.castSucc)
          (youngAmbientRotation lam a.castSucc b.castSucc)).comp
          (gtTransverseTensorEmbedding lam nu h hgram).toLinearMap) =
      TensorProduct.map (euclideanAmbientRotation a b)
        (youngAmbientRotation nu a b) := by
  rw [gtTransverseTensorEmbedding_rotationTerm_adjoint_compression,
    gtTransverseEuclideanIsometry_rotation_adjoint_compression,
    canonicalGelfandTsetlinFibre_rotation_adjoint_compression]

theorem gtTransverseTensorEmbedding_crossTerm_adjoint_compression
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (nu : Fin (r + 1) → ℕ) (h : Interlaces lam nu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam nu h)
    (a : Fin n) :
    (gtTransverseTensorEmbedding lam nu h hgram).toLinearMap.adjoint.comp
        ((TensorProduct.map
          (euclideanAmbientRotation a.castSucc (Fin.last n))
          (youngAmbientRotation lam a.castSucc (Fin.last n))).comp
          (gtTransverseTensorEmbedding lam nu h hgram).toLinearMap) = 0 := by
  rw [gtTransverseTensorEmbedding_rotationTerm_adjoint_compression,
    gtTransverseEuclideanIsometry_cross_rotation_compression]
  apply TensorProduct.ext
  ext v p
  simp only [TensorProduct.map_zero_left, LinearMap.compr₂ₛₗ_apply, TensorProduct.mk_apply,
    LinearMap.zero_apply]

theorem gtTransverseTensorEmbedding_crossTerm_adjoint_compression_swap
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (nu : Fin (r + 1) → ℕ) (h : Interlaces lam nu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam nu h)
    (a : Fin n) :
    (gtTransverseTensorEmbedding lam nu h hgram).toLinearMap.adjoint.comp
        ((TensorProduct.map
          (euclideanAmbientRotation (Fin.last n) a.castSucc)
          (youngAmbientRotation lam (Fin.last n) a.castSucc)).comp
          (gtTransverseTensorEmbedding lam nu h hgram).toLinearMap) = 0 := by
  rw [gtTransverseTensorEmbedding_rotationTerm_adjoint_compression,
    gtTransverseEuclideanIsometry_cross_rotation_compression_swap]
  apply TensorProduct.ext
  ext v p
  simp only [TensorProduct.map_zero_left, LinearMap.compr₂ₛₗ_apply, TensorProduct.mk_apply,
    LinearMap.zero_apply]

theorem gtTransverseTensorEmbedding_lastTerm_adjoint_compression
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (nu : Fin (r + 1) → ℕ) (h : Interlaces lam nu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam nu h) :
    (gtTransverseTensorEmbedding lam nu h hgram).toLinearMap.adjoint.comp
        ((TensorProduct.map
          (euclideanAmbientRotation (Fin.last n) (Fin.last n))
          (youngAmbientRotation lam (Fin.last n) (Fin.last n))).comp
          (gtTransverseTensorEmbedding lam nu h hgram).toLinearMap) = 0 := by
  rw [gtTransverseTensorEmbedding_rotationTerm_adjoint_compression]
  have hzero : euclideanAmbientRotation (Fin.last n) (Fin.last n) = 0 := by
    apply LinearMap.ext
    intro v
    simp only [euclideanAmbientRotation_apply, EuclideanSpace.basisFun_apply, sub_self,
      LinearMap.zero_apply]
  rw [hzero]
  simp only [LinearMap.zero_comp, LinearMap.comp_zero, TensorProduct.map_zero_left]

theorem gtTransverseTensorEmbedding_mixedRotation_adjoint_compression
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (nu : Fin (r + 1) → ℕ) (h : Interlaces lam nu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam nu h) :
    (gtTransverseTensorEmbedding lam nu h hgram).toLinearMap.adjoint.comp
        ((gtMixedRotationOperator (n := n + 1) lam).comp
          (gtTransverseTensorEmbedding lam nu h hgram).toLinearMap) =
      gtMixedRotationOperator (n := n) nu := by
  unfold gtMixedRotationOperator
  apply TensorProduct.ext'
  intro v p
  simp only [LinearMap.comp_apply, LinearMap.sum_apply, map_sum]
  rw [Fin.sum_univ_castSucc]
  simp_rw [Fin.sum_univ_castSucc]
  have htangential (a b : Fin n) := LinearMap.congr_fun
    (gtTransverseTensorEmbedding_tangentialTerm_adjoint_compression
      lam nu h hgram a b) (v ⊗ₜ[ℝ] p)
  have hcross (a : Fin n) := LinearMap.congr_fun
    (gtTransverseTensorEmbedding_crossTerm_adjoint_compression
      lam nu h hgram a) (v ⊗ₜ[ℝ] p)
  have hcrossSwap (a : Fin n) := LinearMap.congr_fun
    (gtTransverseTensorEmbedding_crossTerm_adjoint_compression_swap
      lam nu h hgram a) (v ⊗ₜ[ℝ] p)
  have hlast := LinearMap.congr_fun
    (gtTransverseTensorEmbedding_lastTerm_adjoint_compression
      lam nu h hgram) (v ⊗ₜ[ℝ] p)
  simp only [LinearMap.comp_apply, LinearMap.zero_apply] at htangential hcross hcrossSwap hlast
  simp only [htangential, hcross, hcrossSwap, hlast,
    Finset.sum_const_zero, add_zero]

end AllRankGTTransverseTangentialCompression

end

section


open scoped BigOperators InnerProductSpace TensorProduct

namespace AllRankGTTransverseTensorRelativeCompression

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirPureAxis
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTStabilizerCasimirShift
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCasimirEmbedding
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseTangentialCompression
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity
open MetricCodes.Spherical.HigherHarmonicYoung.ClebschRotation
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungAllRankGTArrowheadSchurComplement

theorem gtRelativeCasimir_eq_scalar_sub_mixed
    {r n : ℕ} (lam : Fin (r + 1) → ℕ) :
    gtRelativeCasimir (n := n) lam =
      (((n : ℝ) - 2) / 2) • LinearMap.id -
        (2 : ℝ)⁻¹ • gtMixedRotationOperator lam := by
  apply TensorProduct.ext
  ext x y
  exact gtRelativeCasimir_tmul_eq_scalar_sub_mixed lam x y

theorem gtRelativeCasimir_transverse_compression_of_mixed
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (nu : Fin (r + 1) → ℕ)
    (I : (SpherePacking.Euclidean n ⊗[ℝ]
      HarmonicYoungSpace (n := n) nu) →ₗ[ℝ]
      (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
        HarmonicYoungSpace (n := n + 1) lam))
    (hisom : I.adjoint.comp I = LinearMap.id)
    (hmixed : I.adjoint.comp
        ((gtMixedRotationOperator (n := n + 1) lam).comp I) =
      gtMixedRotationOperator (n := n) nu) :
    I.adjoint.comp ((gtRelativeCasimir (n := n + 1) lam).comp I) =
      gtStabilizerShiftedRelativeCasimir nu := by
  rw [gtRelativeCasimir_eq_scalar_sub_mixed (n := n + 1) lam,
    gtStabilizerShiftedRelativeCasimir,
    gtRelativeCasimir_eq_scalar_sub_mixed (n := n) nu]
  simp only [LinearMap.sub_comp, LinearMap.smul_comp,
    LinearMap.id_comp, LinearMap.comp_sub, LinearMap.comp_smul]
  rw [hisom, hmixed]
  norm_num
  module

theorem gtRelativeCasimir_gtTransverseTensorEmbedding_adjoint_compression_of_mixed
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (nu : Fin (r + 1) → ℕ) (h : Interlaces lam nu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam nu h)
    (hmixed :
      (gtTransverseTensorEmbedding lam nu h hgram).toLinearMap.adjoint.comp
        ((gtMixedRotationOperator (n := n + 1) lam).comp
          (gtTransverseTensorEmbedding lam nu h hgram).toLinearMap) =
        gtMixedRotationOperator (n := n) nu) :
    (gtTransverseTensorEmbedding lam nu h hgram).toLinearMap.adjoint.comp
      ((gtRelativeCasimir (n := n + 1) lam).comp
        (gtTransverseTensorEmbedding lam nu h hgram).toLinearMap) =
      gtStabilizerShiftedRelativeCasimir nu := by
  exact gtRelativeCasimir_transverse_compression_of_mixed lam nu
    (gtTransverseTensorEmbedding lam nu h hgram).toLinearMap
    (gtTransverseTensorEmbedding lam nu h hgram).adjoint_comp_self'
    hmixed

theorem gtTransverseNegativeSector_relativeCasimir_adjoint_compression_of_mixed
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (row : Fin (r + 1))
    (hnu : Interlaces lam (raiseWeight mu row))
    (hgram : PositiveGelfandTsetlinFischerGram (n := n)
      lam (raiseWeight mu row) hnu)
    (hmixed :
      (gtTransverseTensorEmbedding lam (raiseWeight mu row) hnu hgram).toLinearMap.adjoint.comp
          ((gtMixedRotationOperator (n := n + 1) lam).comp
            (gtTransverseTensorEmbedding lam (raiseWeight mu row)
              hnu hgram).toLinearMap) =
        gtMixedRotationOperator (n := n) (raiseWeight mu row))
    (p : HarmonicYoungSpace (n := n) mu) :
    (gtTransverseTensorEmbedding lam (raiseWeight mu row) hnu hgram).toLinearMap.adjoint
        (gtRelativeCasimir (n := n + 1) lam
          (gtTransverseNegativeSector lam mu row hnu hgram p)) =
      gtStabilizerArrowheadNode (wallShift (n + 1) (r + 1))
        (MetricCodes.Spherical.HigherChannel.stabilizerShift (n + 1) mu)
          (.inr (row, false)) •
          youngClebschRaise (raiseWeight mu row) mu
            (sum_raiseWeight mu row) row p := by
  exact (LinearMap.congr_fun
    (gtRelativeCasimir_gtTransverseTensorEmbedding_adjoint_compression_of_mixed
      lam (raiseWeight mu row) hnu hgram hmixed)
    (youngClebschRaise (raiseWeight mu row) mu
      (sum_raiseWeight mu row) row p)).trans
    (gtStabilizerShiftedRelativeCasimir_raiseTarget_channel mu row
      (youngClebschRaise (raiseWeight mu row) mu
        (sum_raiseWeight mu row) row)
      (fun a b => youngClebschRaise_rotation_intertwine
        (raiseWeight mu row) mu (sum_raiseWeight mu row) row a b)
      p)

theorem gtTransversePositiveSector_relativeCasimir_adjoint_compression_of_mixed
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu nu : Fin (r + 1) → ℕ) (row : Fin (r + 1))
    (hmu : mu = raiseWeight nu row)
    (hnu : Interlaces lam nu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam nu hnu)
    (hmixed :
      (gtTransverseTensorEmbedding lam nu hnu hgram).toLinearMap.adjoint.comp
        ((gtMixedRotationOperator (n := n + 1) lam).comp
          (gtTransverseTensorEmbedding lam nu hnu hgram).toLinearMap) =
        gtMixedRotationOperator (n := n) nu)
    (p : HarmonicYoungSpace (n := n) mu) :
    (gtTransverseTensorEmbedding lam nu hnu hgram).toLinearMap.adjoint
        (gtRelativeCasimir (n := n + 1) lam
          (gtTransversePositiveSector lam mu nu row hmu hnu hgram p)) =
      gtStabilizerArrowheadNode (wallShift (n + 1) (r + 1))
        (MetricCodes.Spherical.HigherChannel.stabilizerShift (n + 1) mu)
          (.inr (row, true)) •
          youngClebschLower nu mu
            (by rw [hmu]; exact sum_raiseWeight nu row) row p := by
  exact (LinearMap.congr_fun
    (gtRelativeCasimir_gtTransverseTensorEmbedding_adjoint_compression_of_mixed
      lam nu hnu hgram hmixed)
    (youngClebschLower nu mu
      (by rw [hmu]; exact sum_raiseWeight nu row) row p)).trans
    (gtStabilizerShiftedRelativeCasimir_lowerTarget_channel mu nu row hmu
      (youngClebschLower nu mu
        (by rw [hmu]; exact sum_raiseWeight nu row) row)
      (fun a b => youngClebschLower_rotation_intertwine
        nu mu (by rw [hmu]; exact sum_raiseWeight nu row) row a b)
      p)

theorem gtTransverseNegativeSector_relativeCasimir_adjoint_compression
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (row : Fin (r + 1))
    (hnu : Interlaces lam (raiseWeight mu row))
    (hgram : PositiveGelfandTsetlinFischerGram (n := n)
      lam (raiseWeight mu row) hnu)
    (p : HarmonicYoungSpace (n := n) mu) :
    (gtTransverseTensorEmbedding lam (raiseWeight mu row) hnu hgram).toLinearMap.adjoint
        (gtRelativeCasimir (n := n + 1) lam
          (gtTransverseNegativeSector lam mu row hnu hgram p)) =
      gtStabilizerArrowheadNode (wallShift (n + 1) (r + 1))
        (MetricCodes.Spherical.HigherChannel.stabilizerShift (n + 1) mu)
          (.inr (row, false)) •
          youngClebschRaise (raiseWeight mu row) mu
            (sum_raiseWeight mu row) row p :=
  gtTransverseNegativeSector_relativeCasimir_adjoint_compression_of_mixed
    lam mu row hnu hgram
    (gtTransverseTensorEmbedding_mixedRotation_adjoint_compression
      lam (raiseWeight mu row) hnu hgram) p

theorem gtTransversePositiveSector_relativeCasimir_adjoint_compression
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu nu : Fin (r + 1) → ℕ) (row : Fin (r + 1))
    (hmu : mu = raiseWeight nu row)
    (hnu : Interlaces lam nu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam nu hnu)
    (p : HarmonicYoungSpace (n := n) mu) :
    (gtTransverseTensorEmbedding lam nu hnu hgram).toLinearMap.adjoint
        (gtRelativeCasimir (n := n + 1) lam
          (gtTransversePositiveSector lam mu nu row hmu hnu hgram p)) =
      gtStabilizerArrowheadNode (wallShift (n + 1) (r + 1))
        (MetricCodes.Spherical.HigherChannel.stabilizerShift (n + 1) mu)
          (.inr (row, true)) •
          youngClebschLower nu mu
            (by rw [hmu]; exact sum_raiseWeight nu row) row p :=
  gtTransversePositiveSector_relativeCasimir_adjoint_compression_of_mixed
    lam mu nu row hmu hnu hgram
    (gtTransverseTensorEmbedding_mixedRotation_adjoint_compression
      lam nu hnu hgram) p

end AllRankGTTransverseTensorRelativeCompression

namespace AllRankGTTransverseWignerEckartPhase

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCanonicalEdgeRaisingGram
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCasimirEmbedding
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInternalRowLowerGram
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowDownstreamActualChannels
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungPenultimateRowProjectedLower

theorem gtTransverseNegativeSector_inner
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (kappa : Fin r → ℕ)
    (row : Fin (r + 1))
    (hnu : Interlaces lam (raiseWeight mu row))
    (hnuGram : PositiveGelfandTsetlinFischerGram
      (n := n) lam (raiseWeight mu row) hnu)
    (hfinite : FiniteInterlacing n mu kappa)
    (hraise : FiniteInterlacing n (raiseWeight mu row) kappa)
    (p q : HarmonicYoungSpace (n := n) mu) :
    ⟪gtTransverseNegativeSector lam mu row hnu hnuGram p,
      gtTransverseNegativeSector lam mu row hnu hnuGram q⟫_ℝ =
      (internalRowLowerGramScalar (raiseWeight mu row) row *
        weylEdgeRatio n mu row) * ⟪p, q⟫_ℝ := by
  obtain ⟨c, _hc, hinner, hc⟩ :=
    canonicalEdgeRaisingGram mu kappa row hfinite hraise
  change
    ⟪gtTransverseTensorEmbedding lam (raiseWeight mu row) hnu hnuGram
        (youngClebschRaise (raiseWeight mu row) mu
          (sum_raiseWeight mu row) row p),
      gtTransverseTensorEmbedding lam (raiseWeight mu row) hnu hnuGram
        (youngClebschRaise (raiseWeight mu row) mu
          (sum_raiseWeight mu row) row q)⟫_ℝ = _
  rw [(gtTransverseTensorEmbedding lam (raiseWeight mu row)
    hnu hnuGram).inner_map_map, hinner p q, hc]

theorem gtTransverseNegativeSector_gram_pos
    {r n : ℕ} (mu : Fin (r + 1) → ℕ)
    (kappa : Fin r → ℕ) (row : Fin (r + 1))
    (hfinite : FiniteInterlacing n mu kappa)
    (hraise : FiniteInterlacing n (raiseWeight mu row) kappa) :
    0 < internalRowLowerGramScalar (raiseWeight mu row) row *
      weylEdgeRatio n mu row := by
  obtain ⟨c, hc, _hinner, heq⟩ :=
    canonicalEdgeRaisingGram mu kappa row hfinite hraise
  simpa only [heq] using hc

private def normalizedGTTransverseNegativeSector
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (kappa : Fin r → ℕ)
    (row : Fin (r + 1))
    (hnu : Interlaces lam (raiseWeight mu row))
    (hnuGram : PositiveGelfandTsetlinFischerGram
      (n := n) lam (raiseWeight mu row) hnu)
    (hfinite : FiniteInterlacing n mu kappa)
    (hraise : FiniteInterlacing n (raiseWeight mu row) kappa) :
    HarmonicYoungSpace (n := n) mu →ₗᵢ[ℝ]
      (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
        HarmonicYoungSpace (n := n + 1) lam) :=
  SpherePacking.HarmonicCoordinateOperators.normalizedChannelIsometry
    (gtTransverseNegativeSector lam mu row hnu hnuGram)
    (internalRowLowerGramScalar (raiseWeight mu row) row *
      weylEdgeRatio n mu row)
    (gtTransverseNegativeSector_gram_pos mu kappa row hfinite hraise)
    (gtTransverseNegativeSector_inner lam mu kappa row
      hnu hnuGram hfinite hraise)

@[simp] theorem normalizedGTTransverseNegativeSector_toLinearMap
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (kappa : Fin r → ℕ)
    (row : Fin (r + 1))
    (hnu : Interlaces lam (raiseWeight mu row))
    (hnuGram : PositiveGelfandTsetlinFischerGram
      (n := n) lam (raiseWeight mu row) hnu)
    (hfinite : FiniteInterlacing n mu kappa)
    (hraise : FiniteInterlacing n (raiseWeight mu row) kappa) :
    (normalizedGTTransverseNegativeSector lam mu kappa row
      hnu hnuGram hfinite hraise).toLinearMap =
      (Real.sqrt (internalRowLowerGramScalar (raiseWeight mu row) row *
        weylEdgeRatio n mu row))⁻¹ •
        gtTransverseNegativeSector lam mu row hnu hnuGram := rfl

private theorem youngClebschLower_inner_of_loweredSignature_metriccodes2_32e91722
    {r n : ℕ} (high low : Fin (r + 1) → ℕ)
    (row : Fin (r + 1))
    (hlowered : low = loweredInternalYoungWeight high row)
    (hpositive : 0 < high row)
    (hdominant : Antitone high)
    (hdegree : (∑ j, high j) = (∑ j, low j) + 1)
    (p q : HarmonicYoungSpace (n := n) high) :
    ⟪youngClebschLower low high hdegree row p,
      youngClebschLower low high hdegree row q⟫_ℝ =
      internalRowLowerGramScalar high row * ⟪p, q⟫_ℝ := by
  subst low
  exact youngClebschLower_arbitrary_inner high row hpositive hdominant p q

theorem gtTransversePositiveSector_inner
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu nu : Fin (r + 1) → ℕ) (row : Fin (r + 1))
    (hmunu : mu = raiseWeight nu row)
    (hmu : Interlaces lam mu)
    (hnu : Interlaces lam nu)
    (hnuGram : PositiveGelfandTsetlinFischerGram
      (n := n) lam nu hnu)
    (p q : HarmonicYoungSpace (n := n) mu) :
    ⟪gtTransversePositiveSector lam mu nu row hmunu hnu hnuGram p,
      gtTransversePositiveSector lam mu nu row hmunu hnu hnuGram q⟫_ℝ =
      internalRowLowerGramScalar mu row * ⟪p, q⟫_ℝ := by
  subst mu
  have hpositive : 0 < raiseWeight nu row row := by
    simp only [raiseWeight, Function.update_self, lt_add_iff_pos_left, Order.lt_add_one_iff,
      zero_le]
  have hdominant : Antitone (raiseWeight nu row) :=
    interlaces_antitone_stabilizer hmu
  change
    ⟪gtTransverseTensorEmbedding lam nu hnu hnuGram
        (youngClebschLower nu (raiseWeight nu row)
          (sum_raiseWeight nu row) row p),
      gtTransverseTensorEmbedding lam nu hnu hnuGram
        (youngClebschLower nu (raiseWeight nu row)
          (sum_raiseWeight nu row) row q)⟫_ℝ = _
  rw [(gtTransverseTensorEmbedding lam nu hnu hnuGram).inner_map_map]
  exact youngClebschLower_inner_of_loweredSignature_metriccodes2_32e91722
    (raiseWeight nu row) nu row
    (canonicalEdge_loweredInternalYoungWeight_raiseWeight nu row).symm
    hpositive hdominant (sum_raiseWeight nu row) p q

theorem gtTransversePositiveSector_gram_pos
    {r : ℕ} (nu : Fin (r + 1) → ℕ)
    (row : Fin (r + 1)) (hdominant : Antitone nu) :
    0 < internalRowLowerGramScalar (raiseWeight nu row) row := by
  apply internalRowLowerGramScalar_pos
  · simp only [raiseWeight, Function.update_self, lt_add_iff_pos_left, Order.lt_add_one_iff,
      zero_le]
  · intro j hj
    exact canonicalEdge_raiseWeight_strictly_removable
      nu hdominant row j hj

private def normalizedGTTransversePositiveSector
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu nu : Fin (r + 1) → ℕ) (row : Fin (r + 1))
    (hmunu : mu = raiseWeight nu row)
    (hmu : Interlaces lam mu)
    (hnu : Interlaces lam nu)
    (hnuGram : PositiveGelfandTsetlinFischerGram
      (n := n) lam nu hnu) :
    HarmonicYoungSpace (n := n) mu →ₗᵢ[ℝ]
      (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
        HarmonicYoungSpace (n := n + 1) lam) :=
  SpherePacking.HarmonicCoordinateOperators.normalizedChannelIsometry
    (gtTransversePositiveSector lam mu nu row hmunu hnu hnuGram)
    (internalRowLowerGramScalar mu row)
    (by
      subst mu
      exact gtTransversePositiveSector_gram_pos nu row
        (interlaces_antitone_stabilizer hnu))
    (gtTransversePositiveSector_inner lam mu nu row
      hmunu hmu hnu hnuGram)

@[simp] theorem normalizedGTTransversePositiveSector_toLinearMap
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu nu : Fin (r + 1) → ℕ) (row : Fin (r + 1))
    (hmunu : mu = raiseWeight nu row)
    (hmu : Interlaces lam mu)
    (hnu : Interlaces lam nu)
    (hnuGram : PositiveGelfandTsetlinFischerGram
      (n := n) lam nu hnu) :
    (normalizedGTTransversePositiveSector lam mu nu row
      hmunu hmu hnu hnuGram).toLinearMap =
      (Real.sqrt (internalRowLowerGramScalar mu row))⁻¹ •
        gtTransversePositiveSector lam mu nu row hmunu hnu hnuGram := rfl

end AllRankGTTransverseWignerEckartPhase

namespace AllRankGTNormalizedTransverseSector

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCasimirEmbedding
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseTensorRelativeCompression
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseWignerEckartPhase
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInternalRowLowerGram
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungAllRankGTArrowheadSchurComplement

theorem isometric_scaled_sector_adjoint_compression
    {X Y Z : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
    [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y]
    [FiniteDimensional ℝ Z]
    (I : X →ₗᵢ[ℝ] Y) (C : Z →ₗ[ℝ] X)
    (B : Z →ₗᵢ[ℝ] Y) (T : Module.End ℝ Y)
    (phase node : ℝ)
    (hphase : B.toLinearMap = phase • I.toLinearMap.comp C)
    (hnode : ∀ p : Z,
      I.toLinearMap.adjoint (T (I (C p))) = node • C p) :
    B.toLinearMap.adjoint.comp (T.comp B.toLinearMap) =
      node • LinearMap.id := by
  apply LinearMap.ext
  intro p
  apply ext_inner_left ℝ
  intro q
  simp only [LinearMap.comp_apply, LinearMap.smul_apply,
    LinearMap.id_coe, id_eq]
  rw [LinearMap.adjoint_inner_right, real_inner_smul_right]
  have hinner := B.inner_map_map q p
  change ⟪B.toLinearMap q, B.toLinearMap p⟫_ℝ = ⟪q, p⟫_ℝ at hinner
  rw [hphase] at hinner ⊢
  change
    ⟪phase • I (C q), T (phase • I (C p))⟫_ℝ =
      node * ⟪q, p⟫_ℝ
  change
    ⟪phase • I (C q), phase • I (C p)⟫_ℝ =
      ⟪q, p⟫_ℝ at hinner
  rw [real_inner_smul_left, real_inner_smul_right,
    I.inner_map_map] at hinner
  have hpair :
      ⟪I (C q), T (I (C p))⟫_ℝ =
        node * ⟪C q, C p⟫_ℝ := by
    change
      ⟪I.toLinearMap (C q), T (I (C p))⟫_ℝ =
        node * ⟪C q, C p⟫_ℝ
    rw [← LinearMap.adjoint_inner_right I.toLinearMap (C q)
      (T (I (C p))), hnode p, real_inner_smul_right]
  rw [map_smul, real_inner_smul_left, real_inner_smul_right,
    hpair, ← hinner]
  ring

theorem normalizedGTTransverseNegativeSector_relativeCasimir_adjoint_compression
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (kappa : Fin r → ℕ)
    (row : Fin (r + 1))
    (hnu : Interlaces lam (raiseWeight mu row))
    (hnuGram : PositiveGelfandTsetlinFischerGram
      (n := n) lam (raiseWeight mu row) hnu)
    (hfinite : FiniteInterlacing n mu kappa)
    (hraise : FiniteInterlacing n (raiseWeight mu row) kappa) :
    (normalizedGTTransverseNegativeSector lam mu kappa row
      hnu hnuGram hfinite hraise).toLinearMap.adjoint.comp
        ((gtRelativeCasimir (n := n + 1) lam).comp
          (normalizedGTTransverseNegativeSector lam mu kappa row
            hnu hnuGram hfinite hraise).toLinearMap) =
      gtStabilizerArrowheadNode (wallShift (n + 1) (r + 1))
        (MetricCodes.Spherical.HigherChannel.stabilizerShift
          (n + 1) mu) (.inr (row, false)) •
          LinearMap.id := by
  apply isometric_scaled_sector_adjoint_compression
    (gtTransverseTensorEmbedding lam (raiseWeight mu row) hnu hnuGram)
    (youngClebschRaise (raiseWeight mu row) mu
      (sum_raiseWeight mu row) row)
    (normalizedGTTransverseNegativeSector lam mu kappa row
      hnu hnuGram hfinite hraise)
    (gtRelativeCasimir lam)
    (Real.sqrt (internalRowLowerGramScalar (raiseWeight mu row) row *
      weylEdgeRatio n mu row))⁻¹
    (gtStabilizerArrowheadNode (wallShift (n + 1) (r + 1))
      (MetricCodes.Spherical.HigherChannel.stabilizerShift
        (n + 1) mu) (.inr (row, false)))
  · exact normalizedGTTransverseNegativeSector_toLinearMap
      lam mu kappa row hnu hnuGram hfinite hraise
  · intro p
    exact gtTransverseNegativeSector_relativeCasimir_adjoint_compression
      lam mu row hnu hnuGram p

theorem normalizedGTTransversePositiveSector_relativeCasimir_adjoint_compression
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu nu : Fin (r + 1) → ℕ) (row : Fin (r + 1))
    (hmunu : mu = raiseWeight nu row)
    (hmu : Interlaces lam mu)
    (hnu : Interlaces lam nu)
    (hnuGram : PositiveGelfandTsetlinFischerGram
      (n := n) lam nu hnu) :
    (normalizedGTTransversePositiveSector lam mu nu row
      hmunu hmu hnu hnuGram).toLinearMap.adjoint.comp
        ((gtRelativeCasimir (n := n + 1) lam).comp
          (normalizedGTTransversePositiveSector lam mu nu row
            hmunu hmu hnu hnuGram).toLinearMap) =
      gtStabilizerArrowheadNode (wallShift (n + 1) (r + 1))
        (MetricCodes.Spherical.HigherChannel.stabilizerShift
          (n + 1) mu) (.inr (row, true)) •
          LinearMap.id := by
  apply isometric_scaled_sector_adjoint_compression
    (gtTransverseTensorEmbedding lam nu hnu hnuGram)
    (youngClebschLower nu mu
      (by rw [hmunu]; exact sum_raiseWeight nu row) row)
    (normalizedGTTransversePositiveSector lam mu nu row
      hmunu hmu hnu hnuGram)
    (gtRelativeCasimir lam)
    (Real.sqrt (internalRowLowerGramScalar mu row))⁻¹
    (gtStabilizerArrowheadNode (wallShift (n + 1) (r + 1))
      (MetricCodes.Spherical.HigherChannel.stabilizerShift
        (n + 1) mu) (.inr (row, true)))
  · exact normalizedGTTransversePositiveSector_toLinearMap
      lam mu nu row hmunu hmu hnu hnuGram
  · intro p
    exact gtTransversePositiveSector_relativeCasimir_adjoint_compression
      lam mu nu row hmunu hnu hnuGram p

end AllRankGTNormalizedTransverseSector

namespace AllRankGTNormalizedTransverseRotationIntertwining

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCasimirEmbedding
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseTangentialCompression
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseWignerEckartPhase
open MetricCodes.Spherical.HigherHarmonicYoung.ClebschRotation
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherRepresentationGraph

theorem gtTransverseTensorEmbedding_rotation_intertwine
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (nu : Fin (r + 1) → ℕ) (h : Interlaces lam nu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam nu h)
    (a b : Fin n) :
    (gtTransverseTensorEmbedding lam nu h hgram).toLinearMap.comp
        (tensorAmbientRotation nu a b) =
      (tensorAmbientRotation lam a.castSucc b.castSucc).comp
        (gtTransverseTensorEmbedding lam nu h hgram).toLinearMap := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy =>
      simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | tmul v p =>
      have hE := LinearMap.congr_fun
        (gtTransverseEuclideanIsometry_rotation_intertwine n a b) v
      have hF := LinearMap.congr_fun
        (canonicalGelfandTsetlinFibre_rotation_intertwine
          lam nu h hgram a b) p
      change
        gtTransverseEuclideanIsometry n (euclideanAmbientRotation a b v) =
          euclideanAmbientRotation a.castSucc b.castSucc
            (gtTransverseEuclideanIsometry n v) at hE
      change
        canonicalGelfandTsetlinFibre lam nu h hgram
            (youngAmbientRotation nu a b p) =
          youngAmbientRotation lam a.castSucc b.castSucc
            (canonicalGelfandTsetlinFibre lam nu h hgram p) at hF
      change
        gtTransverseEuclideanIsometry n
            (euclideanAmbientRotation a b v) ⊗ₜ[ℝ]
          canonicalGelfandTsetlinFibre lam nu h hgram p +
        gtTransverseEuclideanIsometry n v ⊗ₜ[ℝ]
          canonicalGelfandTsetlinFibre lam nu h hgram
            (youngAmbientRotation nu a b p) =
        euclideanAmbientRotation a.castSucc b.castSucc
            (gtTransverseEuclideanIsometry n v) ⊗ₜ[ℝ]
          canonicalGelfandTsetlinFibre lam nu h hgram p +
        gtTransverseEuclideanIsometry n v ⊗ₜ[ℝ]
          youngAmbientRotation lam a.castSucc b.castSucc
            (canonicalGelfandTsetlinFibre lam nu h hgram p)
      rw [hE, hF]

theorem gtTransverseNegativeSector_rotation_intertwine
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (row : Fin (r + 1))
    (hnu : Interlaces lam (raiseWeight mu row))
    (hnuGram : PositiveGelfandTsetlinFischerGram
      (n := n) lam (raiseWeight mu row) hnu)
    (a b : Fin n) :
    (gtTransverseNegativeSector lam mu row hnu hnuGram).comp
        (youngAmbientRotation mu a b) =
      (tensorAmbientRotation lam a.castSucc b.castSucc).comp
        (gtTransverseNegativeSector lam mu row hnu hnuGram) := by
  unfold gtTransverseNegativeSector
  rw [LinearMap.comp_assoc,
    youngClebschRaise_rotation_intertwine,
    ← LinearMap.comp_assoc,
    gtTransverseTensorEmbedding_rotation_intertwine,
    LinearMap.comp_assoc]

theorem gtTransversePositiveSector_rotation_intertwine
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu nu : Fin (r + 1) → ℕ) (row : Fin (r + 1))
    (hmu : mu = raiseWeight nu row)
    (hnu : Interlaces lam nu)
    (hnuGram : PositiveGelfandTsetlinFischerGram
      (n := n) lam nu hnu)
    (a b : Fin n) :
    (gtTransversePositiveSector lam mu nu row hmu hnu hnuGram).comp
        (youngAmbientRotation mu a b) =
      (tensorAmbientRotation lam a.castSucc b.castSucc).comp
        (gtTransversePositiveSector lam mu nu row hmu hnu hnuGram) := by
  unfold gtTransversePositiveSector
  rw [LinearMap.comp_assoc,
    youngClebschLower_rotation_intertwine,
    ← LinearMap.comp_assoc,
    gtTransverseTensorEmbedding_rotation_intertwine,
    LinearMap.comp_assoc]

theorem normalizedGTTransverseNegativeSector_rotation_intertwine
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (kappa : Fin r → ℕ)
    (row : Fin (r + 1))
    (hnu : Interlaces lam (raiseWeight mu row))
    (hnuGram : PositiveGelfandTsetlinFischerGram
      (n := n) lam (raiseWeight mu row) hnu)
    (hfinite : FiniteInterlacing n mu kappa)
    (hraise : FiniteInterlacing n (raiseWeight mu row) kappa)
    (a b : Fin n) :
    (normalizedGTTransverseNegativeSector
      lam mu kappa row hnu hnuGram hfinite hraise).toLinearMap.comp
        (youngAmbientRotation mu a b) =
      (tensorAmbientRotation lam a.castSucc b.castSucc).comp
        (normalizedGTTransverseNegativeSector
          lam mu kappa row hnu hnuGram hfinite hraise).toLinearMap := by
  rw [normalizedGTTransverseNegativeSector_toLinearMap,
    LinearMap.smul_comp, LinearMap.comp_smul,
    gtTransverseNegativeSector_rotation_intertwine]

theorem normalizedGTTransversePositiveSector_rotation_intertwine
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu nu : Fin (r + 1) → ℕ) (row : Fin (r + 1))
    (hmunu : mu = raiseWeight nu row)
    (hmu : Interlaces lam mu)
    (hnu : Interlaces lam nu)
    (hnuGram : PositiveGelfandTsetlinFischerGram
      (n := n) lam nu hnu)
    (a b : Fin n) :
    (normalizedGTTransversePositiveSector
      lam mu nu row hmunu hmu hnu hnuGram).toLinearMap.comp
        (youngAmbientRotation mu a b) =
      (tensorAmbientRotation lam a.castSucc b.castSucc).comp
        (normalizedGTTransversePositiveSector
          lam mu nu row hmunu hmu hnu hnuGram).toLinearMap := by
  rw [normalizedGTTransversePositiveSector_toLinearMap,
    LinearMap.smul_comp, LinearMap.comp_smul,
    gtTransversePositiveSector_rotation_intertwine]

end AllRankGTNormalizedTransverseRotationIntertwining

end

section


open scoped BigOperators InnerProductSpace TensorProduct

namespace AllRankGTTransverseAppendedChannelOrthogonality

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAppendedClebschOrthogonality
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAppendedRowExclusion
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirZeroRowTransport
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTNormalizedTransverseRotationIntertwining
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseWignerEckartPhase
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankPaddedLowerClebschIntertwining
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankZeroRowTensorCasimirConjugacy
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension
open MetricCodes.Spherical.HigherHarmonicYoung.ClebschRotation
open MetricCodes.Spherical.HigherHarmonicYoung.CrossGram
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness
open MetricCodes.Spherical.HigherYoungAllRankDistinctSignatureStabilizerIntertwiner
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriActualChannels
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriSourceSignatureInjectivity
open MetricCodes.Spherical.HigherYoungAllRankZeroRowRotationEquivariance
open MetricCodes.Spherical.ThreeRowYoungBranching

private theorem appendZeroWeight_antitone_metriccodes2_021c7d5c {r : ℕ}
    (mu : Fin (r + 1) → ℕ) (hmu : Antitone mu) :
    Antitone (appendZeroWeight mu) := by
  intro i j hij
  induction i using Fin.lastCases with
  | last =>
      have hj : j = Fin.last (r + 1) := by
        apply Fin.ext
        have hbound := j.isLt
        change r + 1 ≤ j.val at hij
        change j.val = r + 1
        omega
      subst j
      exact le_rfl
  | cast i =>
      induction j using Fin.lastCases with
      | last => simp only [appendZeroWeight_last, appendZeroWeight_castSucc, zero_le]
      | cast j =>
          have hle : i ≤ j := by simpa only [Fin.castSucc_le_castSucc_iff] using hij
          simpa only [appendZeroWeight_castSucc, ge_iff_le] using hmu hle

private def paddedPhysicalStabilizerTensor
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ)
    (B : HarmonicYoungSpace (n := n) mu →ₗ[ℝ]
      (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
        HarmonicYoungSpace (n := n + 1) lam)) :
    HarmonicYoungSpace (n := n)
        (appendZeroWeight (appendZeroWeight mu)) →ₗ[ℝ]
      (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
        HarmonicYoungSpace (n := n + 1) (appendZeroWeight lam)) :=
  (zeroRowTensorIsometryEquiv (n := n + 1) lam).toLinearMap.comp
    (B.comp
      ((appendZeroRowIsometryEquiv (n := n) mu).symm.toLinearMap.comp
        (appendZeroRowIsometryEquiv
          (n := n) (appendZeroWeight mu)).symm.toLinearMap))

theorem paddedPhysicalStabilizerTensor_rotation_intertwine
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ)
    (B : HarmonicYoungSpace (n := n) mu →ₗ[ℝ]
      (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
        HarmonicYoungSpace (n := n + 1) lam))
    (hB : ∀ a b : Fin n,
      B.comp (youngAmbientRotation mu a b) =
        (tensorAmbientRotation lam a.castSucc b.castSucc).comp B)
    (a b : Fin n) :
    (paddedPhysicalStabilizerTensor lam mu B).comp
        (youngAmbientRotation
          (appendZeroWeight (appendZeroWeight mu)) a b) =
      (tensorAmbientRotation (appendZeroWeight lam)
        a.castSucc b.castSucc).comp
          (paddedPhysicalStabilizerTensor lam mu B) := by
  let T := (zeroRowTensorIsometryEquiv (n := n + 1) lam).toLinearMap
  let Z := (appendZeroRowIsometryEquiv (n := n) mu).symm.toLinearMap
  let W := (appendZeroRowIsometryEquiv
    (n := n) (appendZeroWeight mu)).symm.toLinearMap
  apply LinearMap.ext
  intro p
  change T (B (Z (W (youngAmbientRotation
    (appendZeroWeight (appendZeroWeight mu)) a b p)))) =
    tensorAmbientRotation (appendZeroWeight lam)
      a.castSucc b.castSucc (T (B (Z (W p))))
  have hW := LinearMap.congr_fun
    (appendZeroRowIsometryEquiv_symm_rotation_intertwine
      (appendZeroWeight mu) a b) p
  have hZ := LinearMap.congr_fun
    (appendZeroRowIsometryEquiv_symm_rotation_intertwine
      mu a b) (W p)
  have hsector := LinearMap.congr_fun (hB a b) (Z (W p))
  have hT := LinearMap.congr_fun
    (zeroRowTensorIsometryEquiv_rotation_intertwine
      lam a.castSucc b.castSucc) (B (Z (W p)))
  exact (congrArg (fun q => T (B (Z q))) hW).trans
    ((congrArg (fun q => T (B q)) hZ).trans
      ((congrArg T hsector).trans hT))

theorem appendedFullBranchPieriLower_adjoint_paddedPhysicalStabilizerTensor_eq_zero
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (hmu : Antitone mu)
    (B : HarmonicYoungSpace (n := n) mu →ₗ[ℝ]
      (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
        HarmonicYoungSpace (n := n + 1) lam))
    (hB : ∀ a b : Fin n,
      B.comp (youngAmbientRotation mu a b) =
        (tensorAmbientRotation lam a.castSucc b.castSucc).comp B)
    (hdominant : Antitone (appendZeroWeight lam))
    (hsource : Antitone
      (raiseWeight (appendZeroWeight lam) (Fin.last (r + 2))))
    (hn : 2 * (r + 2) + 5 ≤ n + 1)
    (nu : FullBranchWeight
      (raiseWeight (appendZeroWeight lam) (Fin.last (r + 2)))) :
    (appendedFullBranchPieriLower
      lam hdominant hsource hn nu).adjoint.comp
        (paddedPhysicalStabilizerTensor lam mu B) = 0 := by
  have hpadded : Antitone (appendZeroWeight (appendZeroWeight mu)) :=
    appendZeroWeight_antitone_metriccodes2_021c7d5c (appendZeroWeight mu)
      (appendZeroWeight_antitone_metriccodes2_021c7d5c mu hmu)
  apply youngRotationIntertwiner_eq_zero_of_signature_ne
    (by omega)
    (appendZeroWeight (appendZeroWeight mu)) (fullBranchSignature nu)
    hpadded (Ne.symm (appendedRowFullBranchSignature_ne_appendZero lam mu nu))
  intro a b
  exact crossGram_intertwines_of_skew
    (appendedFullBranchPieriLower lam hdominant hsource hn nu)
    (paddedPhysicalStabilizerTensor lam mu B)
    (youngAmbientRotation (fullBranchSignature nu) a b)
    (youngAmbientRotation (appendZeroWeight (appendZeroWeight mu)) a b)
    (tensorAmbientRotation (appendZeroWeight lam) a.castSucc b.castSucc)
    (youngAmbientRotation_adjoint (fullBranchSignature nu) a b)
    (tensorAmbientRotation_adjoint (appendZeroWeight lam)
      a.castSucc b.castSucc)
    (appendedFullBranchPieriLower_rotation_intertwine
      lam hdominant hsource hn nu a b)
    (paddedPhysicalStabilizerTensor_rotation_intertwine
      lam mu B hB a b)

theorem appendedFullBranchPieriLower_paddedPhysicalStabilizerTensor_inner_eq_zero
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (hmu : Antitone mu)
    (B : HarmonicYoungSpace (n := n) mu →ₗ[ℝ]
      (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
        HarmonicYoungSpace (n := n + 1) lam))
    (hB : ∀ a b : Fin n,
      B.comp (youngAmbientRotation mu a b) =
        (tensorAmbientRotation lam a.castSucc b.castSucc).comp B)
    (hdominant : Antitone (appendZeroWeight lam))
    (hsource : Antitone
      (raiseWeight (appendZeroWeight lam) (Fin.last (r + 2))))
    (hn : 2 * (r + 2) + 5 ≤ n + 1)
    (nu : FullBranchWeight
      (raiseWeight (appendZeroWeight lam) (Fin.last (r + 2))))
    (p : HarmonicYoungSpace (n := n)
      (appendZeroWeight (appendZeroWeight mu)))
    (q : HarmonicYoungSpace (n := n) (fullBranchSignature nu)) :
    ⟪paddedPhysicalStabilizerTensor lam mu B p,
      appendedFullBranchPieriLower lam hdominant hsource hn nu q⟫_ℝ = 0 := by
  let A := paddedPhysicalStabilizerTensor lam mu B
  let C := appendedFullBranchPieriLower lam hdominant hsource hn nu
  have hzero := LinearMap.congr_fun
    (appendedFullBranchPieriLower_adjoint_paddedPhysicalStabilizerTensor_eq_zero
      lam mu hmu B hB hdominant hsource hn nu) p
  have hz : C.adjoint (A p) = 0 := by
    simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using hzero
  change ⟪A p, C q⟫_ℝ = 0
  calc
    ⟪A p, C q⟫_ℝ = ⟪C.adjoint (A p), q⟫_ℝ :=
      (LinearMap.adjoint_inner_left C q (A p)).symm
    _ = 0 := by
      rw [hz, young_inner_eq_polynomialInner,
        SpherePacking.Fischer.polynomialInner_comm]
      exact SpherePacking.fischer_polynomialInner_zero_right _ _

theorem appendedPaddedPieriLower_adjoint_paddedPhysicalStabilizerTensor_eq_zero
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (hmu : Antitone mu)
    (B : HarmonicYoungSpace (n := n) mu →ₗ[ℝ]
      (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
        HarmonicYoungSpace (n := n + 1) lam))
    (hB : ∀ a b : Fin n,
      B.comp (youngAmbientRotation mu a b) =
        (tensorAmbientRotation lam a.castSucc b.castSucc).comp B)
    (hdominant : Antitone (appendZeroWeight lam))
    (hsource : Antitone
      (raiseWeight (appendZeroWeight lam) (Fin.last (r + 2))))
    (hn : 2 * (r + 2) + 5 ≤ n + 1) :
    (normalizedPaddedPieriLower (n := n + 1)
      (appendZeroWeight lam) hdominant (Fin.last (r + 2)) hsource).adjoint.comp
        (paddedPhysicalStabilizerTensor lam mu B) = 0 := by
  classical
  let source := raiseWeight (appendZeroWeight lam) (Fin.last (r + 2))
  let C := (normalizedPaddedPieriLower (n := n + 1)
    (appendZeroWeight lam) hdominant (Fin.last (r + 2)) hsource).toLinearMap
  let A := paddedPhysicalStabilizerTensor lam mu B
  apply LinearMap.ext
  intro p
  change C.adjoint (A p) = 0
  apply ext_inner_left ℝ
  intro q
  rw [inner_zero_right]
  have hsum := canonicalFullBranch_sum_projection source hn hsource q
  rw [← hsum, sum_inner]
  apply Finset.sum_eq_zero
  intro nu _
  let F := (canonicalFullBranchFibre source hn nu).toLinearMap
  obtain ⟨z, hz⟩ := Submodule.starProjection_apply_mem
    (LinearMap.range F) q
  change F z = (LinearMap.range F).starProjection q at hz
  rw [← hz]
  calc
    ⟪F z, C.adjoint (A p)⟫_ℝ = ⟪C (F z), A p⟫_ℝ :=
      LinearMap.adjoint_inner_right C (F z) (A p)
    _ = ⟪A p, C (F z)⟫_ℝ := real_inner_comm (A p) (C (F z))
    _ = 0 :=
      appendedFullBranchPieriLower_paddedPhysicalStabilizerTensor_inner_eq_zero
        lam mu hmu B hB hdominant hsource hn nu p z

theorem paddedOrthogonalTensorPieriChannel_appended_stabilizerIntertwiner_orthogonal
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (hmu : Antitone mu)
    (B : HarmonicYoungSpace (n := n) mu →ₗ[ℝ]
      (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
        HarmonicYoungSpace (n := n + 1) lam))
    (hB : ∀ a b : Fin n,
      B.comp (youngAmbientRotation mu a b) =
        (tensorAmbientRotation lam a.castSucc b.castSucc).comp B)
    (hdominant : Antitone (appendZeroWeight lam))
    (hsource : Antitone
      (raiseWeight (appendZeroWeight lam) (Fin.last (r + 2))))
    (hn : 2 * (r + 2) + 5 ≤ n + 1)
    (p : HarmonicYoungSpace (n := n) mu)
    (q : HarmonicYoungSpace (n := n + 1)
      (raiseWeight (appendZeroWeight lam) (Fin.last (r + 2)))) :
    ⟪B p,
      zeroRowTransportPaddedPieriChannel lam
        (paddedOrthogonalTensorPieriChannel (by omega)
          (appendZeroWeight lam) hdominant
          (Sum.inl ⟨Fin.last (r + 2), hsource⟩)) q⟫_ℝ = 0 := by
  let C := (normalizedPaddedPieriLower (n := n + 1)
    (appendZeroWeight lam) hdominant (Fin.last (r + 2)) hsource).toLinearMap
  let A := paddedPhysicalStabilizerTensor lam mu B
  let Z := appendZeroRowIsometryEquiv (n := n) mu
  let W := appendZeroRowIsometryEquiv (n := n) (appendZeroWeight mu)
  let T := zeroRowTensorIsometryEquiv (n := n + 1) lam
  have hzero := LinearMap.congr_fun
    (appendedPaddedPieriLower_adjoint_paddedPhysicalStabilizerTensor_eq_zero
      lam mu hmu B hB hdominant hsource hn) (W (Z p))
  have hz : C.adjoint (T (B p)) = 0 := by
    change C.adjoint (A (W (Z p))) = 0 at hzero
    change C.adjoint (T (B (Z.symm (W.symm (W (Z p)))))) = 0 at hzero
    rw [W.symm_apply_apply, Z.symm_apply_apply] at hzero
    exact hzero
  change ⟪B p, T.symm (C q)⟫_ℝ = 0
  calc
    ⟪B p, T.symm (C q)⟫_ℝ =
      ⟪T (B p), T (T.symm (C q))⟫_ℝ :=
        (T.inner_map_map (B p) (T.symm (C q))).symm
    _ = ⟪T (B p), C q⟫_ℝ := by
      rw [LinearIsometryEquiv.apply_symm_apply]
    _ = ⟪C.adjoint (T (B p)), q⟫_ℝ :=
      (LinearMap.adjoint_inner_left C q (T (B p))).symm
    _ = 0 := by
      rw [hz, young_inner_eq_polynomialInner,
        SpherePacking.Fischer.polynomialInner_comm]
      exact SpherePacking.fischer_polynomialInner_zero_right _ _

theorem paddedOrthogonalTensorPieriChannel_appended_normalizedGTTransverseNegativeSector_orthogonal
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (kappa : Fin r → ℕ)
    (row : Fin (r + 1))
    (hnu : Interlaces lam (raiseWeight mu row))
    (hnuGram : PositiveGelfandTsetlinFischerGram
      (n := n) lam (raiseWeight mu row) hnu)
    (hfinite : FiniteInterlacing n mu kappa)
    (hraise : FiniteInterlacing n (raiseWeight mu row) kappa)
    (hdominant : Antitone (appendZeroWeight lam))
    (hsource : Antitone
      (raiseWeight (appendZeroWeight lam) (Fin.last (r + 2))))
    (hn : 2 * (r + 2) + 5 ≤ n + 1)
    (p : HarmonicYoungSpace (n := n) mu)
    (q : HarmonicYoungSpace (n := n + 1)
      (raiseWeight (appendZeroWeight lam) (Fin.last (r + 2)))) :
    ⟪normalizedGTTransverseNegativeSector
        lam mu kappa row hnu hnuGram hfinite hraise p,
      zeroRowTransportPaddedPieriChannel lam
        (paddedOrthogonalTensorPieriChannel (by omega)
          (appendZeroWeight lam) hdominant
          (Sum.inl ⟨Fin.last (r + 2), hsource⟩)) q⟫_ℝ = 0 := by
  apply paddedOrthogonalTensorPieriChannel_appended_stabilizerIntertwiner_orthogonal
    lam mu hfinite.antitone_ambient
    (normalizedGTTransverseNegativeSector
      lam mu kappa row hnu hnuGram hfinite hraise).toLinearMap
    (normalizedGTTransverseNegativeSector_rotation_intertwine
      lam mu kappa row hnu hnuGram hfinite hraise)
    hdominant hsource hn p q

theorem paddedOrthogonalTensorPieriChannel_appended_normalizedGTTransversePositiveSector_orthogonal
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu nu : Fin (r + 1) → ℕ) (row : Fin (r + 1))
    (hmunu : mu = raiseWeight nu row)
    (hmu : Interlaces lam mu)
    (hnu : Interlaces lam nu)
    (hnuGram : PositiveGelfandTsetlinFischerGram
      (n := n) lam nu hnu)
    (hdominant : Antitone (appendZeroWeight lam))
    (hsource : Antitone
      (raiseWeight (appendZeroWeight lam) (Fin.last (r + 2))))
    (hn : 2 * (r + 2) + 5 ≤ n + 1)
    (p : HarmonicYoungSpace (n := n) mu)
    (q : HarmonicYoungSpace (n := n + 1)
      (raiseWeight (appendZeroWeight lam) (Fin.last (r + 2)))) :
    ⟪normalizedGTTransversePositiveSector
        lam mu nu row hmunu hmu hnu hnuGram p,
      zeroRowTransportPaddedPieriChannel lam
        (paddedOrthogonalTensorPieriChannel (by omega)
          (appendZeroWeight lam) hdominant
          (Sum.inl ⟨Fin.last (r + 2), hsource⟩)) q⟫_ℝ = 0 := by
  apply paddedOrthogonalTensorPieriChannel_appended_stabilizerIntertwiner_orthogonal
    lam mu (interlaces_antitone_stabilizer hmu)
    (normalizedGTTransversePositiveSector
      lam mu nu row hmunu hmu hnu hnuGram).toLinearMap
    (normalizedGTTransversePositiveSector_rotation_intertwine
      lam mu nu row hmunu hmu hnu hnuGram)
    hdominant hsource hn p q

end AllRankGTTransverseAppendedChannelOrthogonality

end

section


open scoped BigOperators InnerProductSpace TensorProduct

namespace AllRankGTTransverseSectorSignedSpan

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolventSpectral
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTPhysicalPaddedPieriSignedSpan
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTNormalizedTransverseRotationIntertwining
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirZeroRowTransport
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransportedPieriOrthogonality
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseAppendedChannelOrthogonality
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCasimirEmbedding
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching
open MetricCodes.Spherical.HigherHarmonicYoung.ClebschRotation
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriActualChannels
open MetricCodes.Spherical.HigherYoungAllRankGTCharacteristicResidue
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriSourceSignatureInjectivity
open MetricCodes.Spherical.ThreeRowYoungBranching

theorem gtSignedEigenvectorSpan_mem_of_appendedPhysicalPaddedPieriChannel_orthogonal
    {r n : ℕ} (hn : 2 * (r + 1) + 4 ≤ n)
    (lam : Fin (r + 1) → ℕ)
    (hdom : Antitone (appendZeroWeight lam))
    (v : SpherePacking.Euclidean n ⊗[ℝ]
      HarmonicYoungSpace (n := n) lam)
    (happended :
      ∀ (hsource : Antitone
          (raiseWeight (appendZeroWeight lam) (Fin.last (r + 1))))
        (q : HarmonicYoungSpace (n := n)
          (raiseWeight (appendZeroWeight lam) (Fin.last (r + 1)))),
        ⟪v, physicalPaddedPieriChannel hn lam hdom
          (Sum.inl ⟨Fin.last (r + 1), hsource⟩) q⟫_ℝ = 0) :
    v ∈ gtSignedEigenvectorSpan (n := n) lam := by
  apply gtSignedEigenvectorSpan_mem_of_physicalPaddedPieriChannel_excluded
    hn lam hdom v
  intro i hnot q
  cases i with
  | inl row =>
      rcases row with ⟨row, hsource⟩
      change ¬ row ≠ Fin.last (r + 1) at hnot
      have hrow : row = Fin.last (r + 1) := Classical.byContradiction hnot
      subst row
      exact happended hsource q
  | inr row =>
      exact False.elim (hnot trivial)

theorem gtPhysicalStabilizerIntertwiner_mem_gtSignedEigenvectorSpan
    {r n : ℕ} (hn : 2 * (r + 2) + 5 ≤ n + 1)
    (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (hmu : Antitone mu)
    (B : HarmonicYoungSpace (n := n) mu →ₗ[ℝ]
      (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
        HarmonicYoungSpace (n := n + 1) lam))
    (hB : ∀ a b : Fin n,
      B.comp (youngAmbientRotation mu a b) =
        (tensorAmbientRotation lam a.castSucc b.castSucc).comp B)
    (hdom : Antitone (appendZeroWeight lam))
    (p : HarmonicYoungSpace (n := n) mu) :
    B p ∈ gtSignedEigenvectorSpan (n := n + 1) lam := by
  apply gtSignedEigenvectorSpan_mem_of_appendedPhysicalPaddedPieriChannel_orthogonal
    (by omega) lam hdom (B p)
  intro hsource q
  change
    ⟪B p,
      zeroRowTransportPaddedPieriChannel lam
        (paddedOrthogonalTensorPieriChannel (by omega)
          (appendZeroWeight lam) hdom
          (Sum.inl ⟨Fin.last (r + 2), hsource⟩)) q⟫_ℝ = 0
  exact
    paddedOrthogonalTensorPieriChannel_appended_stabilizerIntertwiner_orthogonal
      lam mu hmu B hB hdom hsource hn p q

end AllRankGTTransverseSectorSignedSpan

end

section


open scoped BigOperators InnerProductSpace TensorProduct

namespace AllRankGTNormalizedTransverseCharacteristicAnnihilation

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolventSpectral
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirZeroRowTransport
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseAppendedChannelOrthogonality
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCasimirEmbedding
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseSectorSignedSpan
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseWignerEckartPhase
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungAllRankGTAppendedRowLegality
open MetricCodes.Spherical.HigherYoungAllRankGTCharacteristicResidue
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriActualChannels
open MetricCodes.Spherical.ThreeRowYoungBranching

theorem normalizedGTTransverseNegativeSector_mem_gtSignedEigenvectorSpan
    {r n : ℕ} (hn : 2 * (r + 2) + 5 ≤ n + 1)
    (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (kappa : Fin r → ℕ)
    (row : Fin (r + 1))
    (hnu : Interlaces lam (raiseWeight mu row))
    (hnuGram : PositiveGelfandTsetlinFischerGram
      (n := n) lam (raiseWeight mu row) hnu)
    (hfinite : FiniteInterlacing n mu kappa)
    (hraise : FiniteInterlacing n (raiseWeight mu row) kappa)
    (p : HarmonicYoungSpace (n := n) mu) :
    normalizedGTTransverseNegativeSector lam mu kappa row
      hnu hnuGram hfinite hraise p ∈
        gtSignedEigenvectorSpan (n := n + 1) lam := by
  let hdom : Antitone (appendZeroWeight lam) :=
    appendZeroWeight_antitone lam hnu.antitone_ambient
  apply gtSignedEigenvectorSpan_mem_of_appendedPhysicalPaddedPieriChannel_orthogonal
    (by omega) lam hdom
    (normalizedGTTransverseNegativeSector
      lam mu kappa row hnu hnuGram hfinite hraise p)
  intro hsource q
  change
    ⟪normalizedGTTransverseNegativeSector
        lam mu kappa row hnu hnuGram hfinite hraise p,
      zeroRowTransportPaddedPieriChannel lam
        (paddedOrthogonalTensorPieriChannel (by omega)
          (appendZeroWeight lam) hdom
          (Sum.inl ⟨Fin.last (r + 2), hsource⟩)) q⟫_ℝ = 0
  exact
    paddedOrthogonalTensorPieriChannel_appended_normalizedGTTransverseNegativeSector_orthogonal
      lam mu kappa row hnu hnuGram hfinite hraise hdom hsource hn p q

theorem normalizedGTTransversePositiveSector_mem_gtSignedEigenvectorSpan
    {r n : ℕ} (hn : 2 * (r + 2) + 5 ≤ n + 1)
    (lam : Fin (r + 2) → ℕ)
    (mu nu : Fin (r + 1) → ℕ) (row : Fin (r + 1))
    (hmunu : mu = raiseWeight nu row)
    (hmu : Interlaces lam mu)
    (hnu : Interlaces lam nu)
    (hnuGram : PositiveGelfandTsetlinFischerGram
      (n := n) lam nu hnu)
    (p : HarmonicYoungSpace (n := n) mu) :
    normalizedGTTransversePositiveSector lam mu nu row
      hmunu hmu hnu hnuGram p ∈
        gtSignedEigenvectorSpan (n := n + 1) lam := by
  let hdom : Antitone (appendZeroWeight lam) :=
    appendZeroWeight_antitone lam hmu.antitone_ambient
  apply gtSignedEigenvectorSpan_mem_of_appendedPhysicalPaddedPieriChannel_orthogonal
    (by omega) lam hdom
    (normalizedGTTransversePositiveSector
      lam mu nu row hmunu hmu hnu hnuGram p)
  intro hsource q
  change
    ⟪normalizedGTTransversePositiveSector
        lam mu nu row hmunu hmu hnu hnuGram p,
      zeroRowTransportPaddedPieriChannel lam
        (paddedOrthogonalTensorPieriChannel (by omega)
          (appendZeroWeight lam) hdom
          (Sum.inl ⟨Fin.last (r + 2), hsource⟩)) q⟫_ℝ = 0
  exact
    paddedOrthogonalTensorPieriChannel_appended_normalizedGTTransversePositiveSector_orthogonal
      lam mu nu row hmunu hmu hnu hnuGram hdom hsource hn p q

theorem normalizedGTTransverseNegativeSector_characteristic_aeval_eq_zero
    {r n : ℕ} (hn : 2 * (r + 2) + 5 ≤ n + 1)
    (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (kappa : Fin r → ℕ)
    (row : Fin (r + 1))
    (hnu : Interlaces lam (raiseWeight mu row))
    (hnuGram : PositiveGelfandTsetlinFischerGram
      (n := n) lam (raiseWeight mu row) hnu)
    (hfinite : FiniteInterlacing n mu kappa)
    (hraise : FiniteInterlacing n (raiseWeight mu row) kappa)
    (p : HarmonicYoungSpace (n := n) mu) :
    Polynomial.aeval (gtRelativeCasimir (n := n + 1) lam)
        (gtChannelCharacteristicPolynomial (n + 1) lam)
        (normalizedGTTransverseNegativeSector lam mu kappa row
          hnu hnuGram hfinite hraise p) = 0 :=
  gtSignedEigenvectorSpan_le_characteristic_ker lam
    (normalizedGTTransverseNegativeSector_mem_gtSignedEigenvectorSpan
      hn lam mu kappa row hnu hnuGram hfinite hraise p)

theorem normalizedGTTransversePositiveSector_characteristic_aeval_eq_zero
    {r n : ℕ} (hn : 2 * (r + 2) + 5 ≤ n + 1)
    (lam : Fin (r + 2) → ℕ)
    (mu nu : Fin (r + 1) → ℕ) (row : Fin (r + 1))
    (hmunu : mu = raiseWeight nu row)
    (hmu : Interlaces lam mu)
    (hnu : Interlaces lam nu)
    (hnuGram : PositiveGelfandTsetlinFischerGram
      (n := n) lam nu hnu)
    (p : HarmonicYoungSpace (n := n) mu) :
    Polynomial.aeval (gtRelativeCasimir (n := n + 1) lam)
        (gtChannelCharacteristicPolynomial (n + 1) lam)
        (normalizedGTTransversePositiveSector lam mu nu row
          hmunu hmu hnu hnuGram p) = 0 :=
  gtSignedEigenvectorSpan_le_characteristic_ker lam
    (normalizedGTTransversePositiveSector_mem_gtSignedEigenvectorSpan
      hn lam mu nu row hmunu hmu hnu hnuGram p)

end AllRankGTNormalizedTransverseCharacteristicAnnihilation

end

section


open scoped BigOperators InnerProductSpace TensorProduct

namespace AllRankGTWallTransverseCompression

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCasimirEmbedding
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension
open MetricCodes.Spherical.HigherHarmonicYoung.ClebschRotation
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherRepresentationGraph (Interlaces)
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness
open MetricCodes.Spherical.ThreeRowYoungBranching

private def gtWallFullBranchOfSignature {r : ℕ}
    (lam signature : Fin (r + 1) → ℕ)
    (hupper : ∀ i, signature i ≤ lam i)
    (hlower : ∀ i : Fin r, lam i.succ ≤ signature i.castSucc) :
    FullBranchWeight lam :=
  ⟨fun i => ⟨signature i, Nat.lt_succ_of_le (hupper i)⟩,
    fun i => hlower i⟩

theorem exists_fullBranchSignature_wall_of_last_pos {r : ℕ}
    (lam : Fin (r + 2) → ℕ) (mu : Fin (r + 1) → ℕ)
    (h : Interlaces lam mu)
    (hlast : 0 < lam (Fin.last (r + 1))) :
    ∃ nu : FullBranchWeight lam,
      fullBranchSignature nu =
        raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)) := by
  let signature : Fin (r + 2) → ℕ :=
    raiseWeight (appendZeroWeight mu) (Fin.last (r + 1))
  have hupper : ∀ i, signature i ≤ lam i := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [signature, raiseWeight] using
        (show 1 ≤ lam (Fin.last (r + 1)) by omega)
    · simpa [signature, raiseWeight, Fin.castSucc_ne_last] using (h j).1
  have hlower : ∀ i : Fin (r + 1),
      lam i.succ ≤ signature i.castSucc := by
    intro i
    simpa [signature, raiseWeight, Fin.castSucc_ne_last] using (h i).2
  exact ⟨gtWallFullBranchOfSignature lam signature hupper hlower, rfl⟩

private def gtWallFullBranch
    {r : ℕ} (lam : Fin (r + 2) → ℕ) (mu : Fin (r + 1) → ℕ)
    (h : Interlaces lam mu)
    (hlast : 0 < lam (Fin.last (r + 1))) : FullBranchWeight lam :=
  Classical.choose (exists_fullBranchSignature_wall_of_last_pos
    lam mu h hlast)

@[simp] theorem gtWallFullBranch_signature
    {r : ℕ} (lam : Fin (r + 2) → ℕ) (mu : Fin (r + 1) → ℕ)
    (h : Interlaces lam mu)
    (hlast : 0 < lam (Fin.last (r + 1))) :
    fullBranchSignature (gtWallFullBranch lam mu h hlast) =
      raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)) :=
  Classical.choose_spec
    (exists_fullBranchSignature_wall_of_last_pos lam mu h hlast)

private def gtWallCanonicalFullBranchFibre
    {r n : ℕ} (lam : Fin (r + 2) → ℕ) (mu : Fin (r + 1) → ℕ)
    (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hlast : 0 < lam (Fin.last (r + 1))) :
    HarmonicYoungSpace (n := n)
        (raiseWeight (appendZeroWeight mu) (Fin.last (r + 1))) →ₗᵢ[ℝ]
      HarmonicYoungSpace (n := n + 1) lam :=
  (gtWallFullBranch_signature lam mu h hlast) ▸
    canonicalFullBranchFibre lam hn (gtWallFullBranch lam mu h hlast)

private def gtTransverseWallTensorEmbedding
    {r n : ℕ} (lam : Fin (r + 2) → ℕ) (mu : Fin (r + 1) → ℕ)
    (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hlast : 0 < lam (Fin.last (r + 1))) :
    (SpherePacking.Euclidean n ⊗[ℝ]
      HarmonicYoungSpace (n := n)
        (raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))) →ₗᵢ[ℝ]
      (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
        HarmonicYoungSpace (n := n + 1) lam) :=
  TensorProduct.mapIsometry (gtTransverseEuclideanIsometry n)
    (gtWallCanonicalFullBranchFibre lam mu h hn hlast)

private def gtTransverseWallSector
    {r n : ℕ} (lam : Fin (r + 2) → ℕ) (mu : Fin (r + 1) → ℕ)
    (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hlast : 0 < lam (Fin.last (r + 1))) :
    HarmonicYoungSpace (n := n) mu →ₗ[ℝ]
      (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
        HarmonicYoungSpace (n := n + 1) lam) :=
  (gtTransverseWallTensorEmbedding
    lam mu h hn hlast).toLinearMap.comp
      ((youngClebschRaise
        (raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
        (appendZeroWeight mu)
        (sum_raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
        (Fin.last (r + 1))).comp
          (appendZeroRowIsometryEquiv mu).toLinearMap)

end AllRankGTWallTransverseCompression

end

section


open scoped BigOperators InnerProductSpace TensorProduct

namespace AllRankGTWallSectorGram

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCanonicalEdgeRaisingGram
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallTransverseCompression
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInternalRowLowerGram
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity
open MetricCodes.Spherical.HigherRepresentationGraph (Interlaces)
open MetricCodes.Spherical.ThreeRowYoungBranching

/-- The gt wall sector gram used in the spherical-code argument. -/
def gtWallSectorGram {r : ℕ} (n : ℕ) (mu : Fin (r + 1) → ℕ) : ℝ :=
  internalRowLowerGramScalar
      (raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
      (Fin.last (r + 1)) *
    weylEdgeRatio n (appendZeroWeight mu) (Fin.last (r + 1))

theorem gtWallZeroRow_finiteInterlacing
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1) :
    FiniteInterlacing n (appendZeroWeight mu) mu := by
  refine ⟨by omega, ?_⟩
  intro row
  constructor
  · simp only [appendZeroWeight_castSucc, Std.le_refl]
  · refine Fin.lastCases ?_ (fun row => ?_) row
    · simp only [Fin.succ_last, Nat.succ_eq_add_one, appendZeroWeight_last, zero_le]
    · simpa only [← Fin.castSucc_succ, appendZeroWeight_castSucc] using
        (interlaces_antitone_stabilizer h)
          (Fin.castSucc_le_succ row)

theorem gtWallRaisedZeroRow_finiteInterlacing
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hlast : 0 < lam (Fin.last (r + 1))) :
    FiniteInterlacing n
      (raiseWeight (appendZeroWeight mu) (Fin.last (r + 1))) mu := by
  have hmuLast : 0 < mu (Fin.last r) := by
    have hbound := (h (Fin.last r)).2
    have hbound' : lam (Fin.last (r + 1)) ≤ mu (Fin.last r) := by
      simpa only [Fin.succ_last, Nat.succ_eq_add_one] using hbound
    omega
  refine ⟨by omega, ?_⟩
  intro row
  constructor
  · simp only [raiseWeight, appendZeroWeight_last, zero_add, ne_eq, Fin.castSucc_ne_last,
      not_false_eq_true, Function.update_of_ne, appendZeroWeight_castSucc, Std.le_refl]
  · refine Fin.lastCases ?_ (fun row => ?_) row
    · simpa only [raiseWeight, appendZeroWeight_last, zero_add, Fin.succ_last, Nat.succ_eq_add_one,
        Function.update_self] using (show 1 ≤ mu (Fin.last r) by omega)
    · simpa only [raiseWeight, appendZeroWeight_last, zero_add, ← Fin.castSucc_succ, ne_eq,
      Fin.castSucc_ne_last,
        not_false_eq_true, Function.update_of_ne, appendZeroWeight_castSucc] using
        (interlaces_antitone_stabilizer h) (Fin.castSucc_le_succ row)

theorem gtWallSectorGram_pos
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hlast : 0 < lam (Fin.last (r + 1))) :
    0 < gtWallSectorGram n mu := by
  obtain ⟨raisingGram, hpositive, _, heq⟩ :=
    canonicalEdgeRaisingGram (appendZeroWeight mu) mu
      (Fin.last (r + 1))
      (gtWallZeroRow_finiteInterlacing lam mu h hn)
      (gtWallRaisedZeroRow_finiteInterlacing lam mu h hn hlast)
  change 0 <
    internalRowLowerGramScalar
        (raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
        (Fin.last (r + 1)) *
      weylEdgeRatio n (appendZeroWeight mu) (Fin.last (r + 1))
  rw [← heq]
  exact hpositive

theorem gtTransverseWallSector_inner
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hlast : 0 < lam (Fin.last (r + 1)))
    (p q : HarmonicYoungSpace (n := n) mu) :
    ⟪gtTransverseWallSector lam mu h hn hlast p,
      gtTransverseWallSector lam mu h hn hlast q⟫_ℝ =
      gtWallSectorGram n mu * ⟪p, q⟫_ℝ := by
  obtain ⟨raisingGram, _, hinner, heq⟩ :=
    canonicalEdgeRaisingGram (appendZeroWeight mu) mu
      (Fin.last (r + 1))
      (gtWallZeroRow_finiteInterlacing lam mu h hn)
      (gtWallRaisedZeroRow_finiteInterlacing lam mu h hn hlast)
  change
    ⟪gtTransverseWallTensorEmbedding lam mu h hn hlast
        (youngClebschRaise
          (raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
          (appendZeroWeight mu)
          (sum_raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
          (Fin.last (r + 1)) (appendZeroRowIsometryEquiv mu p)),
      gtTransverseWallTensorEmbedding lam mu h hn hlast
        (youngClebschRaise
          (raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
          (appendZeroWeight mu)
          (sum_raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
          (Fin.last (r + 1)) (appendZeroRowIsometryEquiv mu q))⟫_ℝ = _
  calc
    _ = ⟪youngClebschRaise
          (raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
          (appendZeroWeight mu)
          (sum_raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
          (Fin.last (r + 1)) (appendZeroRowIsometryEquiv mu p),
        youngClebschRaise
          (raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
          (appendZeroWeight mu)
          (sum_raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
          (Fin.last (r + 1)) (appendZeroRowIsometryEquiv mu q)⟫_ℝ :=
      (gtTransverseWallTensorEmbedding lam mu h hn hlast).inner_map_map _ _
    _ = raisingGram *
          ⟪appendZeroRowIsometryEquiv mu p,
            appendZeroRowIsometryEquiv mu q⟫_ℝ := hinner _ _
    _ = raisingGram * ⟪p, q⟫_ℝ :=
      congrArg (fun x : ℝ => raisingGram * x)
        ((appendZeroRowIsometryEquiv mu).inner_map_map p q)
    _ = gtWallSectorGram n mu * ⟪p, q⟫_ℝ := by
      rw [heq]
      rfl

end AllRankGTWallSectorGram

end

section


open scoped BigOperators InnerProductSpace TensorProduct

namespace AllRankGTWallTransverseCompression

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirPureAxis
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTStabilizerCasimirShift
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCasimirEmbedding
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseTangentialCompression
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseTensorRelativeCompression
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension
open MetricCodes.Spherical.HigherHarmonicYoung.ClebschRotation
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherRepresentationGraph (Interlaces)
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness
open MetricCodes.Spherical.ThreeRowYoungBranching

theorem stabilizerIsometry_rotation_adjoint_compression
    {s r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (nu : Fin (s + 1) → ℕ)
    (F : HarmonicYoungSpace (n := n) nu →ₗᵢ[ℝ]
      HarmonicYoungSpace (n := n + 1) lam)
    (hF : ∀ a b : Fin n,
      F.toLinearMap.comp (youngAmbientRotation nu a b) =
        (youngAmbientRotation lam a.castSucc b.castSucc).comp F.toLinearMap)
    (a b : Fin n) :
    F.toLinearMap.adjoint.comp
      ((youngAmbientRotation lam a.castSucc b.castSucc).comp F.toLinearMap) =
      youngAmbientRotation nu a b := by
  rw [← hF a b, ← LinearMap.comp_assoc,
    F.adjoint_comp_self', LinearMap.id_comp]

private def transverseTensorEmbeddingOfStabilizerIsometry
    {s r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (nu : Fin (s + 1) → ℕ)
    (F : HarmonicYoungSpace (n := n) nu →ₗᵢ[ℝ]
      HarmonicYoungSpace (n := n + 1) lam) :
    (SpherePacking.Euclidean n ⊗[ℝ]
      HarmonicYoungSpace (n := n) nu) →ₗᵢ[ℝ]
      (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
        HarmonicYoungSpace (n := n + 1) lam) :=
  TensorProduct.mapIsometry (gtTransverseEuclideanIsometry n) F

theorem transverseTensorEmbeddingOfStabilizerIsometry_rotationTerm
    {s r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (nu : Fin (s + 1) → ℕ)
    (F : HarmonicYoungSpace (n := n) nu →ₗᵢ[ℝ]
      HarmonicYoungSpace (n := n + 1) lam)
    (a b : Fin (n + 1)) :
    (transverseTensorEmbeddingOfStabilizerIsometry lam nu F).toLinearMap.adjoint.comp
        ((TensorProduct.map (euclideanAmbientRotation a b)
          (youngAmbientRotation lam a b)).comp
          (transverseTensorEmbeddingOfStabilizerIsometry lam nu F).toLinearMap) =
      TensorProduct.map
        ((gtTransverseEuclideanIsometry n).toLinearMap.adjoint.comp
          ((euclideanAmbientRotation a b).comp
            (gtTransverseEuclideanIsometry n).toLinearMap))
        (F.toLinearMap.adjoint.comp
          ((youngAmbientRotation lam a b).comp F.toLinearMap)) := by
  change
    (TensorProduct.map
      (gtTransverseEuclideanIsometry n).toLinearMap F.toLinearMap).adjoint.comp
        ((TensorProduct.map (euclideanAmbientRotation a b)
          (youngAmbientRotation lam a b)).comp
          (TensorProduct.map
            (gtTransverseEuclideanIsometry n).toLinearMap F.toLinearMap)) = _
  rw [TensorProduct.adjoint_map]
  apply TensorProduct.ext
  ext v p
  rfl

theorem transverseTensorEmbeddingOfStabilizerIsometry_mixedRotation
    {s r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (nu : Fin (s + 1) → ℕ)
    (F : HarmonicYoungSpace (n := n) nu →ₗᵢ[ℝ]
      HarmonicYoungSpace (n := n + 1) lam)
    (hF : ∀ a b : Fin n,
      F.toLinearMap.comp (youngAmbientRotation nu a b) =
        (youngAmbientRotation lam a.castSucc b.castSucc).comp F.toLinearMap) :
    (transverseTensorEmbeddingOfStabilizerIsometry lam nu F).toLinearMap.adjoint.comp
        ((gtMixedRotationOperator (n := n + 1) lam).comp
          (transverseTensorEmbeddingOfStabilizerIsometry lam nu F).toLinearMap) =
      gtMixedRotationOperator (n := n) nu := by
  let I := (transverseTensorEmbeddingOfStabilizerIsometry lam nu F).toLinearMap
  have htangential (a b : Fin n) :
      I.adjoint.comp
          ((TensorProduct.map
            (euclideanAmbientRotation a.castSucc b.castSucc)
            (youngAmbientRotation lam a.castSucc b.castSucc)).comp I) =
        TensorProduct.map (euclideanAmbientRotation a b)
          (youngAmbientRotation nu a b) := by
    change
      (transverseTensorEmbeddingOfStabilizerIsometry lam nu F).toLinearMap.adjoint.comp
          ((TensorProduct.map
            (euclideanAmbientRotation a.castSucc b.castSucc)
            (youngAmbientRotation lam a.castSucc b.castSucc)).comp
            (transverseTensorEmbeddingOfStabilizerIsometry lam nu F).toLinearMap) = _
    rw [transverseTensorEmbeddingOfStabilizerIsometry_rotationTerm,
      gtTransverseEuclideanIsometry_rotation_adjoint_compression,
      stabilizerIsometry_rotation_adjoint_compression lam nu F hF]
  have hcross (a : Fin n) :
      I.adjoint.comp
          ((TensorProduct.map
            (euclideanAmbientRotation a.castSucc (Fin.last n))
            (youngAmbientRotation lam a.castSucc (Fin.last n))).comp I) = 0 := by
    change
      (transverseTensorEmbeddingOfStabilizerIsometry lam nu F).toLinearMap.adjoint.comp
          ((TensorProduct.map
            (euclideanAmbientRotation a.castSucc (Fin.last n))
            (youngAmbientRotation lam a.castSucc (Fin.last n))).comp
            (transverseTensorEmbeddingOfStabilizerIsometry lam nu F).toLinearMap) = 0
    rw [transverseTensorEmbeddingOfStabilizerIsometry_rotationTerm,
      gtTransverseEuclideanIsometry_cross_rotation_compression]
    apply TensorProduct.ext
    ext v p
    simp only [TensorProduct.map_zero_left, LinearMap.compr₂ₛₗ_apply, TensorProduct.mk_apply,
      LinearMap.zero_apply]
  have hcrossSwap (a : Fin n) :
      I.adjoint.comp
          ((TensorProduct.map
            (euclideanAmbientRotation (Fin.last n) a.castSucc)
            (youngAmbientRotation lam (Fin.last n) a.castSucc)).comp I) = 0 := by
    change
      (transverseTensorEmbeddingOfStabilizerIsometry lam nu F).toLinearMap.adjoint.comp
          ((TensorProduct.map
            (euclideanAmbientRotation (Fin.last n) a.castSucc)
            (youngAmbientRotation lam (Fin.last n) a.castSucc)).comp
            (transverseTensorEmbeddingOfStabilizerIsometry lam nu F).toLinearMap) = 0
    rw [transverseTensorEmbeddingOfStabilizerIsometry_rotationTerm,
      gtTransverseEuclideanIsometry_cross_rotation_compression_swap]
    apply TensorProduct.ext
    ext v p
    simp only [TensorProduct.map_zero_left, LinearMap.compr₂ₛₗ_apply, TensorProduct.mk_apply,
      LinearMap.zero_apply]
  have hlast :
      I.adjoint.comp
          ((TensorProduct.map
            (euclideanAmbientRotation (Fin.last n) (Fin.last n))
            (youngAmbientRotation lam (Fin.last n) (Fin.last n))).comp I) = 0 := by
    change
      (transverseTensorEmbeddingOfStabilizerIsometry lam nu F).toLinearMap.adjoint.comp
          ((TensorProduct.map
            (euclideanAmbientRotation (Fin.last n) (Fin.last n))
            (youngAmbientRotation lam (Fin.last n) (Fin.last n))).comp
            (transverseTensorEmbeddingOfStabilizerIsometry lam nu F).toLinearMap) = 0
    rw [transverseTensorEmbeddingOfStabilizerIsometry_rotationTerm]
    have hzero : euclideanAmbientRotation (Fin.last n) (Fin.last n) = 0 := by
      apply LinearMap.ext
      intro v
      simp only [euclideanAmbientRotation_apply, EuclideanSpace.basisFun_apply, sub_self,
        LinearMap.zero_apply]
    rw [hzero]
    simp only [LinearMap.zero_comp, LinearMap.comp_zero, TensorProduct.map_zero_left]
  unfold gtMixedRotationOperator
  change I.adjoint.comp ((∑ a : Fin (n + 1), ∑ b : Fin (n + 1),
    TensorProduct.map (euclideanAmbientRotation a b)
      (youngAmbientRotation lam a b)).comp I) = _
  apply TensorProduct.ext'
  intro v p
  simp only [LinearMap.comp_apply, LinearMap.sum_apply, map_sum]
  rw [Fin.sum_univ_castSucc]
  simp_rw [Fin.sum_univ_castSucc]
  have htangential' (a b : Fin n) :=
    LinearMap.congr_fun (htangential a b) (v ⊗ₜ[ℝ] p)
  have hcross' (a : Fin n) :=
    LinearMap.congr_fun (hcross a) (v ⊗ₜ[ℝ] p)
  have hcrossSwap' (a : Fin n) :=
    LinearMap.congr_fun (hcrossSwap a) (v ⊗ₜ[ℝ] p)
  have hlast' := LinearMap.congr_fun hlast (v ⊗ₜ[ℝ] p)
  simp only [LinearMap.comp_apply, LinearMap.zero_apply] at htangential' hcross' hcrossSwap' hlast'
  simp only [htangential', hcross', hcrossSwap', hlast',
    Finset.sum_const_zero, add_zero]

theorem transverseTensorEmbeddingOfStabilizerIsometry_relativeCasimir
    {s r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (nu : Fin (s + 1) → ℕ)
    (F : HarmonicYoungSpace (n := n) nu →ₗᵢ[ℝ]
      HarmonicYoungSpace (n := n + 1) lam)
    (hF : ∀ a b : Fin n,
      F.toLinearMap.comp (youngAmbientRotation nu a b) =
        (youngAmbientRotation lam a.castSucc b.castSucc).comp F.toLinearMap) :
    (transverseTensorEmbeddingOfStabilizerIsometry lam nu F).toLinearMap.adjoint.comp
        ((gtRelativeCasimir (n := n + 1) lam).comp
          (transverseTensorEmbeddingOfStabilizerIsometry lam nu F).toLinearMap) =
      gtStabilizerShiftedRelativeCasimir nu := by
  rw [gtRelativeCasimir_eq_scalar_sub_mixed (n := n + 1) lam,
    gtStabilizerShiftedRelativeCasimir,
    gtRelativeCasimir_eq_scalar_sub_mixed (n := n) nu]
  simp only [LinearMap.sub_comp, LinearMap.smul_comp,
    LinearMap.id_comp, LinearMap.comp_sub, LinearMap.comp_smul]
  rw [(transverseTensorEmbeddingOfStabilizerIsometry
    lam nu F).adjoint_comp_self',
    transverseTensorEmbeddingOfStabilizerIsometry_mixedRotation
      lam nu F hF]
  norm_num
  module

theorem stabilizerShift_appendZeroWeight_last_add_half_eq_wall
    {r n : ℕ} (mu : Fin (r + 1) → ℕ) :
    stabilizerShift (n + 1) (appendZeroWeight mu) (Fin.last (r + 1)) +
        (1 / 2 : ℝ) = wallShift (n + 1) (r + 1) := by
  simp only [stabilizerShift, wallShift, appendZeroWeight_last,
    Nat.cast_zero, Nat.cast_add, Nat.cast_one, Fin.val_last]
  ring

theorem gtStabilizerShiftedRelativeCasimir_terminal_youngClebschRaise
    {r n : ℕ} (mu : Fin (r + 1) → ℕ)
    (p : HarmonicYoungSpace (n := n) (appendZeroWeight mu)) :
    gtStabilizerShiftedRelativeCasimir
      (raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
      (youngClebschRaise
        (raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
        (appendZeroWeight mu)
        (sum_raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
        (Fin.last (r + 1)) p) =
      (-wallShift (n + 1) (r + 1)) •
        youngClebschRaise
          (raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
          (appendZeroWeight mu)
          (sum_raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
          (Fin.last (r + 1)) p := by
  rw [gtStabilizerShiftedRelativeCasimir_raiseTarget_channel
    (appendZeroWeight mu) (Fin.last (r + 1))
    (youngClebschRaise
      (raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
      (appendZeroWeight mu)
      (sum_raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
      (Fin.last (r + 1)))
    (fun a b => youngClebschRaise_rotation_intertwine
      (raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
      (appendZeroWeight mu)
      (sum_raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
      (Fin.last (r + 1)) a b) p]
  simp only
    [HigherYoungAllRankGTArrowheadSchurComplement.gtStabilizerArrowheadNode_neg]
  congr 1
  linarith [stabilizerShift_appendZeroWeight_last_add_half_eq_wall
    (n := n) mu]

@[simp] theorem gtTransverseWallTensorEmbedding_tmul
    {r n : ℕ} (lam : Fin (r + 2) → ℕ) (mu : Fin (r + 1) → ℕ)
    (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hlast : 0 < lam (Fin.last (r + 1)))
    (v : SpherePacking.Euclidean n)
    (p : HarmonicYoungSpace (n := n)
      (raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))) :
    gtTransverseWallTensorEmbedding lam mu h hn hlast (v ⊗ₜ[ℝ] p) =
      gtTransverseEuclideanIsometry n v ⊗ₜ[ℝ]
        gtWallCanonicalFullBranchFibre lam mu h hn hlast p := by
  change
    TensorProduct.map
      (gtTransverseEuclideanIsometry n).toLinearMap
      (gtWallCanonicalFullBranchFibre lam mu h hn hlast).toLinearMap
      (v ⊗ₜ[ℝ] p) = _
  exact TensorProduct.map_tmul
    (gtTransverseEuclideanIsometry n).toLinearMap
    (gtWallCanonicalFullBranchFibre lam mu h hn hlast).toLinearMap v p

theorem gtTransverseWallTensorEmbedding_axis_inner_eq_zero
    {r n : ℕ} (lam : Fin (r + 2) → ℕ) (mu : Fin (r + 1) → ℕ)
    (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hlast : 0 < lam (Fin.last (r + 1)))
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (x : SpherePacking.Euclidean n ⊗[ℝ]
      HarmonicYoungSpace (n := n)
        (raiseWeight (appendZeroWeight mu) (Fin.last (r + 1))))
    (q : HarmonicYoungSpace (n := n) mu) :
    ⟪gtTransverseWallTensorEmbedding lam mu h hn hlast x,
      canonicalGelfandTsetlinAxisTensor lam mu h hgram q⟫_ℝ = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, canonicalGelfandTsetlinAxisTensor_apply,
              EuclideanSpace.basisFun_apply, canonicalGelfandTsetlinFibre_apply,
              TensorProduct.tmul_smul, inner_zero_left]
  | tmul v p =>
      rw [gtTransverseWallTensorEmbedding_tmul,
        canonicalGelfandTsetlinAxisTensor_apply,
        TensorProduct.inner_tmul,
        gtTransverseEuclideanIsometry_orthogonal_last]
      simp only [canonicalGelfandTsetlinFibre_apply, zero_mul]
  | add x y hx hy =>
      rw [map_add, inner_add_left, hx, hy, zero_add]

theorem gtTransverseWallSector_axis_inner_eq_zero
    {r n : ℕ} (lam : Fin (r + 2) → ℕ) (mu : Fin (r + 1) → ℕ)
    (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hlast : 0 < lam (Fin.last (r + 1)))
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (p q : HarmonicYoungSpace (n := n) mu) :
    ⟪gtTransverseWallSector lam mu h hn hlast p,
      canonicalGelfandTsetlinAxisTensor lam mu h hgram q⟫_ℝ = 0 := by
  exact gtTransverseWallTensorEmbedding_axis_inner_eq_zero
    lam mu h hn hlast hgram
    (youngClebschRaise
      (raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
      (appendZeroWeight mu)
      (sum_raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
      (Fin.last (r + 1)) (appendZeroRowIsometryEquiv mu p)) q

private theorem transportedFullBranchFibre_rotation_intertwine_metriccodes2_5c2d5a44
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (nu : FullBranchWeight lam)
    (sigma : Fin (r + 2) → ℕ)
    (hsigma : fullBranchSignature nu = sigma)
    (a b : Fin n) :
    let F : HarmonicYoungSpace (n := n) sigma →ₗᵢ[ℝ]
      HarmonicYoungSpace (n := n + 1) lam :=
        hsigma ▸ canonicalFullBranchFibre lam hn nu
    F.toLinearMap.comp (youngAmbientRotation sigma a b) =
      (youngAmbientRotation lam a.castSucc b.castSucc).comp F.toLinearMap := by
  subst sigma
  exact canonicalFullBranchFibre_rotation_intertwine lam hn nu a b

theorem gtWallCanonicalFullBranchFibre_rotation_intertwine
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hlast : 0 < lam (Fin.last (r + 1)))
    (a b : Fin n) :
    (gtWallCanonicalFullBranchFibre lam mu h hn hlast).toLinearMap.comp
      (youngAmbientRotation
        (raiseWeight (appendZeroWeight mu) (Fin.last (r + 1))) a b) =
      (youngAmbientRotation lam a.castSucc b.castSucc).comp
        (gtWallCanonicalFullBranchFibre lam mu h hn hlast).toLinearMap :=
  transportedFullBranchFibre_rotation_intertwine_metriccodes2_5c2d5a44 lam hn
    (gtWallFullBranch lam mu h hlast)
    (raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
    (gtWallFullBranch_signature lam mu h hlast) a b

theorem gtTransverseWallTensorEmbedding_relativeCasimir_compression
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hlast : 0 < lam (Fin.last (r + 1))) :
    (gtTransverseWallTensorEmbedding lam mu h hn hlast).toLinearMap.adjoint.comp
        ((gtRelativeCasimir (n := n + 1) lam).comp
          (gtTransverseWallTensorEmbedding lam mu h hn hlast).toLinearMap) =
      gtStabilizerShiftedRelativeCasimir
        (raiseWeight (appendZeroWeight mu) (Fin.last (r + 1))) := by
  exact transverseTensorEmbeddingOfStabilizerIsometry_relativeCasimir
    lam (raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
    (gtWallCanonicalFullBranchFibre lam mu h hn hlast)
    (gtWallCanonicalFullBranchFibre_rotation_intertwine
      lam mu h hn hlast)

theorem gtTransverseWallSector_relativeCasimir_compression
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hlast : 0 < lam (Fin.last (r + 1)))
    (p : HarmonicYoungSpace (n := n) mu) :
    (gtTransverseWallTensorEmbedding lam mu h hn hlast).toLinearMap.adjoint
        (gtRelativeCasimir (n := n + 1) lam
          (gtTransverseWallSector lam mu h hn hlast p)) =
      (-wallShift (n + 1) (r + 1)) •
        youngClebschRaise
          (raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
          (appendZeroWeight mu)
          (sum_raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
          (Fin.last (r + 1))
          (appendZeroRowIsometryEquiv mu p) := by
  unfold gtTransverseWallSector
  change
    ((gtTransverseWallTensorEmbedding lam mu h hn hlast).toLinearMap.adjoint.comp
      ((gtRelativeCasimir (n := n + 1) lam).comp
        (gtTransverseWallTensorEmbedding lam mu h hn hlast).toLinearMap))
        (youngClebschRaise
          (raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
          (appendZeroWeight mu)
          (sum_raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
          (Fin.last (r + 1))
          (appendZeroRowIsometryEquiv mu p)) = _
  rw [gtTransverseWallTensorEmbedding_relativeCasimir_compression]
  exact gtStabilizerShiftedRelativeCasimir_terminal_youngClebschRaise
    mu (appendZeroRowIsometryEquiv mu p)

end AllRankGTWallTransverseCompression

end

section


open scoped BigOperators InnerProductSpace TensorProduct

namespace AllRankGTWallSectorIsometry

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallSectorGram
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallTransverseCompression
open MetricCodes.Spherical.HigherRepresentationGraph (Interlaces)
open MetricCodes.Spherical.HigherYoungMixedGapAxisProbability

private def normalizedGTTransverseWallSector
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hlast : 0 < lam (Fin.last (r + 1))) :
    HarmonicYoungSpace (n := n) mu →ₗᵢ[ℝ]
      (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
        HarmonicYoungSpace (n := n + 1) lam) :=
  SpherePacking.HarmonicCoordinateOperators.normalizedChannelIsometry
    (gtTransverseWallSector lam mu h hn hlast)
    (gtWallSectorGram n mu)
    (gtWallSectorGram_pos lam mu h hn hlast)
    (gtTransverseWallSector_inner lam mu h hn hlast)

@[simp] theorem normalizedGTTransverseWallSector_toLinearMap
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hlast : 0 < lam (Fin.last (r + 1))) :
    (normalizedGTTransverseWallSector lam mu h hn hlast).toLinearMap =
      (Real.sqrt (gtWallSectorGram n mu))⁻¹ •
        gtTransverseWallSector lam mu h hn hlast := rfl

@[simp] theorem normalizedGTTransverseWallSector_apply
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hlast : 0 < lam (Fin.last (r + 1)))
    (p : HarmonicYoungSpace (n := n) mu) :
    normalizedGTTransverseWallSector lam mu h hn hlast p =
      (Real.sqrt (gtWallSectorGram n mu))⁻¹ •
        gtTransverseWallSector lam mu h hn hlast p := rfl

theorem normalizedGTTransverseWallSector_axis_inner_eq_zero
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hlast : 0 < lam (Fin.last (r + 1)))
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (p q : HarmonicYoungSpace (n := n) mu) :
    ⟪normalizedGTTransverseWallSector lam mu h hn hlast p,
      canonicalGelfandTsetlinAxisTensor lam mu h hgram q⟫_ℝ = 0 := by
  change
    ⟪(Real.sqrt (gtWallSectorGram n mu))⁻¹ •
        gtTransverseWallSector lam mu h hn hlast p,
      canonicalGelfandTsetlinAxisTensor lam mu h hgram q⟫_ℝ = 0
  rw [real_inner_smul_left,
    gtTransverseWallSector_axis_inner_eq_zero
      lam mu h hn hlast hgram p q, mul_zero]

theorem canonicalAxis_inner_normalizedGTTransverseWallSector_eq_zero
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hlast : 0 < lam (Fin.last (r + 1)))
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (p q : HarmonicYoungSpace (n := n) mu) :
    ⟪canonicalGelfandTsetlinAxisTensor lam mu h hgram p,
      normalizedGTTransverseWallSector lam mu h hn hlast q⟫_ℝ = 0 := by
  exact (real_inner_comm
    (canonicalGelfandTsetlinAxisTensor lam mu h hgram p)
    (normalizedGTTransverseWallSector lam mu h hn hlast q)).symm.trans
      (normalizedGTTransverseWallSector_axis_inner_eq_zero
        lam mu h hn hlast hgram q p)

end AllRankGTWallSectorIsometry

end

section


open scoped BigOperators InnerProductSpace TensorProduct

namespace AllRankGTNormalizedWallCharacteristicAnnihilation

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolventSpectral
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCasimirEmbedding
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseSectorSignedSpan
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseTangentialCompression
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallSectorIsometry
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallTransverseCompression
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension
open MetricCodes.Spherical.HigherHarmonicYoung.ClebschRotation
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness
open MetricCodes.Spherical.HigherYoungAllRankGTCharacteristicResidue
open MetricCodes.Spherical.HigherYoungAllRankZeroRowRotationEquivariance
open MetricCodes.Spherical.ThreeRowYoungBranching

private theorem wallFullBranchFibre_rotation_intertwine_metriccodes2_3a89272e
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hlast : 0 < lam (Fin.last (r + 1)))
    (a b : Fin n) :
    (gtWallCanonicalFullBranchFibre lam mu h hn hlast).toLinearMap.comp
      (youngAmbientRotation
        (raiseWeight (appendZeroWeight mu) (Fin.last (r + 1))) a b) =
      (youngAmbientRotation lam a.castSucc b.castSucc).comp
        (gtWallCanonicalFullBranchFibre lam mu h hn hlast).toLinearMap :=
  gtWallCanonicalFullBranchFibre_rotation_intertwine
    lam mu h hn hlast a b

private theorem wallTensorEmbedding_rotation_intertwine_metriccodes2_3a89272e
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hlast : 0 < lam (Fin.last (r + 1)))
    (a b : Fin n) :
    (gtTransverseWallTensorEmbedding lam mu h hn hlast).toLinearMap.comp
        (tensorAmbientRotation
          (raiseWeight (appendZeroWeight mu) (Fin.last (r + 1))) a b) =
      (tensorAmbientRotation lam a.castSucc b.castSucc).comp
        (gtTransverseWallTensorEmbedding lam mu h hn hlast).toLinearMap := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy =>
      simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | tmul v p =>
      have hE := LinearMap.congr_fun
        (gtTransverseEuclideanIsometry_rotation_intertwine n a b) v
      have hF := LinearMap.congr_fun
        (wallFullBranchFibre_rotation_intertwine_metriccodes2_3a89272e
          lam mu h hn hlast a b) p
      simp only [LinearMap.comp_apply] at hE hF
      change
        gtTransverseEuclideanIsometry n
            (euclideanAmbientRotation a b v) ⊗ₜ[ℝ]
          gtWallCanonicalFullBranchFibre lam mu h hn hlast p +
        gtTransverseEuclideanIsometry n v ⊗ₜ[ℝ]
          gtWallCanonicalFullBranchFibre lam mu h hn hlast
            (youngAmbientRotation
              (raiseWeight (appendZeroWeight mu) (Fin.last (r + 1))) a b p) =
        euclideanAmbientRotation a.castSucc b.castSucc
            (gtTransverseEuclideanIsometry n v) ⊗ₜ[ℝ]
          gtWallCanonicalFullBranchFibre lam mu h hn hlast p +
        gtTransverseEuclideanIsometry n v ⊗ₜ[ℝ]
          youngAmbientRotation lam a.castSucc b.castSucc
            (gtWallCanonicalFullBranchFibre lam mu h hn hlast p)
      exact congrArg₂ (· + ·)
        (congrArg (fun w => w ⊗ₜ[ℝ]
          gtWallCanonicalFullBranchFibre lam mu h hn hlast p) hE)
        (congrArg (fun w => gtTransverseEuclideanIsometry n v ⊗ₜ[ℝ] w) hF)

private theorem wallSector_rotation_intertwine_metriccodes2_3a89272e
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hlast : 0 < lam (Fin.last (r + 1)))
    (a b : Fin n) :
    (gtTransverseWallSector lam mu h hn hlast).comp
        (youngAmbientRotation mu a b) =
      (tensorAmbientRotation lam a.castSucc b.castSucc).comp
        (gtTransverseWallSector lam mu h hn hlast) := by
  apply LinearMap.ext
  intro p
  have hzero := LinearMap.congr_fun
    (appendZeroRowIsometryEquiv_rotation_intertwine mu a b) p
  have hraise := LinearMap.congr_fun
    (youngClebschRaise_rotation_intertwine
      (raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
      (appendZeroWeight mu)
      (sum_raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
      (Fin.last (r + 1)) a b)
    (appendZeroRowIsometryEquiv mu p)
  have htensor := LinearMap.congr_fun
    (wallTensorEmbedding_rotation_intertwine_metriccodes2_3a89272e
      lam mu h hn hlast a b)
    (youngClebschRaise
      (raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
      (appendZeroWeight mu)
      (sum_raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
      (Fin.last (r + 1)) (appendZeroRowIsometryEquiv mu p))
  simp only [LinearMap.comp_apply] at hzero hraise htensor ⊢
  change
    gtTransverseWallTensorEmbedding lam mu h hn hlast
        (youngClebschRaise
          (raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
          (appendZeroWeight mu)
          (sum_raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
          (Fin.last (r + 1))
          (appendZeroRowIsometryEquiv mu (youngAmbientRotation mu a b p))) = _
  exact (congrArg (fun q =>
    gtTransverseWallTensorEmbedding lam mu h hn hlast
      (youngClebschRaise
        (raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
        (appendZeroWeight mu)
        (sum_raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
        (Fin.last (r + 1)) q)) hzero).trans
    ((congrArg
      (gtTransverseWallTensorEmbedding lam mu h hn hlast) hraise).trans
      htensor)

theorem normalizedGTTransverseWallSector_rotation_intertwine
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hlast : 0 < lam (Fin.last (r + 1)))
    (a b : Fin n) :
    (normalizedGTTransverseWallSector lam mu h hn hlast).toLinearMap.comp
        (youngAmbientRotation mu a b) =
      (tensorAmbientRotation lam a.castSucc b.castSucc).comp
        (normalizedGTTransverseWallSector lam mu h hn hlast).toLinearMap := by
  rw [normalizedGTTransverseWallSector_toLinearMap,
    LinearMap.smul_comp, LinearMap.comp_smul,
    wallSector_rotation_intertwine_metriccodes2_3a89272e lam mu h hn hlast a b]

theorem normalizedGTTransverseWallSector_mem_gtSignedEigenvectorSpan
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hstable : 2 * (r + 2) + 5 ≤ n + 1)
    (hlast : 0 < lam (Fin.last (r + 1)))
    (p : HarmonicYoungSpace (n := n) mu) :
    normalizedGTTransverseWallSector lam mu h hn hlast p ∈
      gtSignedEigenvectorSpan (n := n + 1) lam := by
  have hdominant : Antitone (appendZeroWeight lam) :=
    (fullBranchSignature_interlaces_appendZeroWeight lam
      (fullBranchOfInterlaces mu h)).antitone_ambient
  exact gtPhysicalStabilizerIntertwiner_mem_gtSignedEigenvectorSpan
    hstable lam mu (interlaces_antitone_stabilizer h)
    (normalizedGTTransverseWallSector lam mu h hn hlast).toLinearMap
    (normalizedGTTransverseWallSector_rotation_intertwine
      lam mu h hn hlast)
    hdominant p

theorem normalizedGTTransverseWallSector_characteristic_aeval_eq_zero
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hstable : 2 * (r + 2) + 5 ≤ n + 1)
    (hlast : 0 < lam (Fin.last (r + 1)))
    (p : HarmonicYoungSpace (n := n) mu) :
    Polynomial.aeval (gtRelativeCasimir (n := n + 1) lam)
      (gtChannelCharacteristicPolynomial (n + 1) lam)
      (normalizedGTTransverseWallSector lam mu h hn hlast p) = 0 :=
  gtSignedEigenvectorSpan_le_characteristic_ker lam
    (normalizedGTTransverseWallSector_mem_gtSignedEigenvectorSpan
      lam mu h hn hstable hlast p)

end AllRankGTNormalizedWallCharacteristicAnnihilation

end

section


namespace AllRankGTPresentWallSignedNodeSeparation

open MetricCodes.Spherical.HigherChannel

theorem wallShift_lt_ambientShift_of_last_pos
    {r n : ℕ} {lam : Fin (r + 2) → ℕ}
    {mu : Fin (r + 1) → ℕ}
    (hfinite : FiniteInterlacing (n + 1) lam mu)
    (hlast : 0 < lam (Fin.last (r + 1)))
    (row : Fin (r + 2)) :
    wallShift (n + 1) (r + 1) < ambientShift (n + 1) lam row := by
  have hpositive : (0 : ℝ) < (lam (Fin.last (r + 1)) : ℝ) := by
    exact_mod_cast hlast
  have horder := hfinite.ambientShift_strictAnti.antitone row.le_last
  rw [ambientShift_last] at horder
  linarith

theorem presentWall_ne_signedAmbientNode
    {r n : ℕ} {lam : Fin (r + 2) → ℕ}
    {mu : Fin (r + 1) → ℕ}
    (hfinite : FiniteInterlacing (n + 1) lam mu)
    (hlast : 0 < lam (Fin.last (r + 1)))
    (z : Fin (r + 2) × Bool) :
    -(wallShift (n + 1) (r + 1)) ≠
      signedNode (ambientShift (n + 1) lam) z := by
  rcases z with ⟨row, sign⟩
  cases sign with
  | false =>
      simp only [signedNode, Bool.false_eq_true, ↓reduceIte]
      intro heq
      linarith [wallShift_lt_ambientShift_of_last_pos hfinite hlast row]
  | true =>
      simp only [signedNode, ↓reduceIte]
      intro heq
      linarith [hfinite.wallShift_pos, hfinite.ambientShift_pos row]

end AllRankGTPresentWallSignedNodeSeparation

end

section


open scoped BigOperators InnerProductSpace TensorProduct

namespace AllRankGTTransverseFullBranchDecomposition

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCasimirEmbedding
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankOrthogonalBranchCompleteness
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness

private def gtFullTransverseInternalEmbedding {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) (hn : 2 * r + 5 ≤ n + 1)
    (mu : FullBranchWeight lam) :
    (SpherePacking.Euclidean n ⊗[ℝ]
      HarmonicYoungSpace (n := n) (fullBranchSignature mu)) →ₗᵢ[ℝ]
        (SpherePacking.Euclidean n ⊗[ℝ]
          HarmonicYoungSpace (n := n + 1) lam) :=
  TensorProduct.mapIsometry
    (LinearIsometry.id :
      SpherePacking.Euclidean n →ₗᵢ[ℝ] SpherePacking.Euclidean n)
    (canonicalFullBranchFibre lam hn mu)

@[simp] theorem gtFullTransverseInternalEmbedding_tmul {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) (hn : 2 * r + 5 ≤ n + 1)
    (mu : FullBranchWeight lam)
    (v : SpherePacking.Euclidean n)
    (p : HarmonicYoungSpace (n := n) (fullBranchSignature mu)) :
    gtFullTransverseInternalEmbedding lam hn mu (v ⊗ₜ[ℝ] p) =
      v ⊗ₜ[ℝ] canonicalFullBranchFibre lam hn mu p := rfl

theorem gtFullTransverseInternalEmbedding_orthogonal {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) (hn : 2 * r + 5 ≤ n + 1)
    (mu nu : FullBranchWeight lam) (hne : mu ≠ nu)
    (x : SpherePacking.Euclidean n ⊗[ℝ]
      HarmonicYoungSpace (n := n) (fullBranchSignature mu))
    (y : SpherePacking.Euclidean n ⊗[ℝ]
      HarmonicYoungSpace (n := n) (fullBranchSignature nu)) :
    ⟪gtFullTransverseInternalEmbedding lam hn mu x,
      gtFullTransverseInternalEmbedding lam hn nu y⟫_ℝ = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, inner_zero_left]
  | tmul v p =>
      induction y using TensorProduct.induction_on with
      | zero => simp only [gtFullTransverseInternalEmbedding_tmul, Nat.add_one_sub_one, map_zero,
                  inner_zero_right]
      | tmul w q =>
          rw [gtFullTransverseInternalEmbedding_tmul,
            gtFullTransverseInternalEmbedding_tmul,
            TensorProduct.inner_tmul]
          calc
            ⟪v, w⟫_ℝ *
                ⟪canonicalFullBranchFibre lam hn mu p,
                  canonicalFullBranchFibre lam hn nu q⟫_ℝ =
              ⟪v, w⟫_ℝ * 0 :=
                congrArg (fun z : ℝ => ⟪v, w⟫_ℝ * z)
                  (canonicalFullBranchFibre_orthogonal
                    lam hn mu nu hne p q)
            _ = 0 := mul_zero _
      | add y z hy hz =>
          rw [map_add, inner_add_right, hy, hz, add_zero]
  | add x z hx hz =>
      rw [map_add, inner_add_left, hx, hz, add_zero]

theorem gtFullTransverseInternalEmbedding_finrank_sum {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) (hn : 2 * r + 5 ≤ n + 1)
    (hdom : Antitone lam) :
    Module.finrank ℝ
        (SpherePacking.Euclidean n ⊗[ℝ]
          HarmonicYoungSpace (n := n + 1) lam) =
      ∑ mu : FullBranchWeight lam,
        Module.finrank ℝ
          (SpherePacking.Euclidean n ⊗[ℝ]
            HarmonicYoungSpace (n := n) (fullBranchSignature mu)) := by
  rw [Module.finrank_tensorProduct]
  calc
    Module.finrank ℝ (SpherePacking.Euclidean n) *
        Module.finrank ℝ (HarmonicYoungSpace (n := n + 1) lam) =
      Module.finrank ℝ (SpherePacking.Euclidean n) *
        ∑ mu : FullBranchWeight lam,
          Module.finrank ℝ
            (HarmonicYoungSpace (n := n)
              (fullBranchSignature mu)) := by
          congr 1
          convert canonicalFullBranch_finrank_sum_allRank lam hn hdom using 1
          · apply Finset.sum_congr rfl
            intro mu _
            congr 1
    _ = ∑ mu : FullBranchWeight lam,
          Module.finrank ℝ
            (SpherePacking.Euclidean n ⊗[ℝ]
              HarmonicYoungSpace (n := n)
                (fullBranchSignature mu)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro mu _
          symm
          exact Module.finrank_tensorProduct

theorem gtFullTransverseInternalEmbedding_iSup_range_eq_top
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (hn : 2 * r + 5 ≤ n + 1) (hdom : Antitone lam) :
    (⨆ mu : FullBranchWeight lam,
      LinearMap.range
        (gtFullTransverseInternalEmbedding lam hn mu).toLinearMap) =
      (⊤ : Submodule ℝ
        (SpherePacking.Euclidean n ⊗[ℝ]
          HarmonicYoungSpace (n := n + 1) lam)) :=
  orthogonalBranch_iSup_range_eq_top
    (gtFullTransverseInternalEmbedding lam hn)
    (gtFullTransverseInternalEmbedding_orthogonal lam hn)
    (gtFullTransverseInternalEmbedding_finrank_sum lam hn hdom)

private def gtFullTransverseAmbientInclusion {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) :
    (SpherePacking.Euclidean n ⊗[ℝ]
      HarmonicYoungSpace (n := n + 1) lam) →ₗᵢ[ℝ]
        (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
          HarmonicYoungSpace (n := n + 1) lam) :=
  TensorProduct.mapIsometry (gtTransverseEuclideanIsometry n)
    (LinearIsometry.id :
      HarmonicYoungSpace (n := n + 1) lam →ₗᵢ[ℝ]
        HarmonicYoungSpace (n := n + 1) lam)

private def gtFullTransverseEmbedding {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) (hn : 2 * r + 5 ≤ n + 1)
    (mu : FullBranchWeight lam) :
    (SpherePacking.Euclidean n ⊗[ℝ]
      HarmonicYoungSpace (n := n) (fullBranchSignature mu)) →ₗᵢ[ℝ]
        (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
          HarmonicYoungSpace (n := n + 1) lam) :=
  TensorProduct.mapIsometry (gtTransverseEuclideanIsometry n)
    (canonicalFullBranchFibre lam hn mu)

theorem gtFullTransverseEmbedding_eq_comp {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) (hn : 2 * r + 5 ≤ n + 1)
    (mu : FullBranchWeight lam) :
    (gtFullTransverseEmbedding lam hn mu).toLinearMap =
      (gtFullTransverseAmbientInclusion (n := n) lam).toLinearMap.comp
        (gtFullTransverseInternalEmbedding lam hn mu).toLinearMap := by
  apply TensorProduct.ext
  ext v p
  rfl

theorem gtFullTransverseEmbedding_orthogonal {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) (hn : 2 * r + 5 ≤ n + 1)
    (mu nu : FullBranchWeight lam) (hne : mu ≠ nu)
    (x : SpherePacking.Euclidean n ⊗[ℝ]
      HarmonicYoungSpace (n := n) (fullBranchSignature mu))
    (y : SpherePacking.Euclidean n ⊗[ℝ]
      HarmonicYoungSpace (n := n) (fullBranchSignature nu)) :
    ⟪gtFullTransverseEmbedding lam hn mu x,
      gtFullTransverseEmbedding lam hn nu y⟫_ℝ = 0 := by
  have hmu := LinearMap.congr_fun
    (gtFullTransverseEmbedding_eq_comp lam hn mu) x
  have hnu := LinearMap.congr_fun
    (gtFullTransverseEmbedding_eq_comp lam hn nu) y
  change
    ⟪(gtFullTransverseEmbedding lam hn mu).toLinearMap x,
      (gtFullTransverseEmbedding lam hn nu).toLinearMap y⟫_ℝ = 0
  rw [hmu, hnu]
  calc
    _ = ⟪gtFullTransverseInternalEmbedding lam hn mu x,
          gtFullTransverseInternalEmbedding lam hn nu y⟫_ℝ :=
      (gtFullTransverseAmbientInclusion (n := n) lam).inner_map_map _ _
    _ = 0 :=
      gtFullTransverseInternalEmbedding_orthogonal lam hn mu nu hne x y

theorem gtFullTransverseEmbedding_iSup_range {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) (hn : 2 * r + 5 ≤ n + 1)
    (hdom : Antitone lam) :
    (⨆ mu : FullBranchWeight lam,
      LinearMap.range (gtFullTransverseEmbedding lam hn mu).toLinearMap) =
      LinearMap.range
        (gtFullTransverseAmbientInclusion (n := n) lam).toLinearMap := by
  calc
    (⨆ mu : FullBranchWeight lam,
      LinearMap.range (gtFullTransverseEmbedding lam hn mu).toLinearMap) =
        ⨆ mu : FullBranchWeight lam,
          (LinearMap.range
            (gtFullTransverseInternalEmbedding lam hn mu).toLinearMap).map
              (gtFullTransverseAmbientInclusion (n := n) lam).toLinearMap := by
          congr 1
          funext mu
          rw [gtFullTransverseEmbedding_eq_comp, LinearMap.range_comp]
    _ = (⨆ mu : FullBranchWeight lam,
          LinearMap.range
            (gtFullTransverseInternalEmbedding lam hn mu).toLinearMap).map
              (gtFullTransverseAmbientInclusion (n := n) lam).toLinearMap :=
          (Submodule.map_iSup _ _).symm
    _ = (⊤ : Submodule ℝ
          (SpherePacking.Euclidean n ⊗[ℝ]
            HarmonicYoungSpace (n := n + 1) lam)).map
              (gtFullTransverseAmbientInclusion (n := n) lam).toLinearMap := by
          rw [gtFullTransverseInternalEmbedding_iSup_range_eq_top
            lam hn hdom]
    _ = LinearMap.range
          (gtFullTransverseAmbientInclusion (n := n) lam).toLinearMap :=
          Submodule.map_top _

end AllRankGTTransverseFullBranchDecomposition

namespace AllRankGTActualAxisTransverseDecomposition

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCasimirEmbedding
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseFullBranchDecomposition
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness

theorem euclidean_eq_gtTransverse_add_last_axis {n : ℕ}
    (v : SpherePacking.Euclidean (n + 1)) :
    v = gtTransverseEuclideanIsometry n
        (WithLp.toLp 2 (fun i : Fin n => v i.castSucc)) +
      v (Fin.last n) •
        (EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n)) := by
  ext i
  induction i using Fin.lastCases with
  | last => simp only [EuclideanSpace.basisFun_apply, PiLp.add_apply,
              gtTransverseEuclideanIsometry_last, PiLp.smul_apply, PiLp.single_eq_same, smul_eq_mul,
              mul_one, zero_add]
  | cast j => simp only [EuclideanSpace.basisFun_apply, PiLp.add_apply,
                gtTransverseEuclideanIsometry_castSucc, PiLp.smul_apply, ne_eq,
                Fin.castSucc_ne_last, not_false_eq_true, PiLp.single_eq_of_ne, smul_eq_mul,
                mul_zero, add_zero]

private def gtFullAxisAmbientInclusion {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) :
    HarmonicYoungSpace (n := n + 1) lam →ₗᵢ[ℝ]
      (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
        HarmonicYoungSpace (n := n + 1) lam) :=
  (TensorProduct.mk ℝ (SpherePacking.Euclidean (n + 1))
    (HarmonicYoungSpace (n := n + 1) lam)
    (EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n))).isometryOfInner
      (by
        intro p q
        change
          ⟪(EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n)) ⊗ₜ[ℝ] p,
            (EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n)) ⊗ₜ[ℝ] q⟫_ℝ =
            ⟪p, q⟫_ℝ
        rw [TensorProduct.inner_tmul,
          (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).inner_eq_one,
          one_mul]
        rfl)

theorem gtFullAxisAmbientInclusion_sup_transverse_range_eq_top
    {r n : ℕ} (lam : Fin (r + 1) → ℕ) :
    LinearMap.range (gtFullAxisAmbientInclusion (n := n) lam).toLinearMap ⊔
        LinearMap.range
          (gtFullTransverseAmbientInclusion (n := n) lam).toLinearMap =
      (⊤ : Submodule ℝ
        (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
          HarmonicYoungSpace (n := n + 1) lam)) := by
  apply top_unique
  intro x _
  induction x using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | tmul v p =>
      let w : SpherePacking.Euclidean n :=
        WithLp.toLp 2 (fun i : Fin n => v i.castSucc)
      have hv := euclidean_eq_gtTransverse_add_last_axis v
      change v ⊗ₜ[ℝ] p ∈ _
      rw [hv, TensorProduct.add_tmul]
      apply Submodule.add_mem
      · apply Submodule.mem_sup_right
        exact ⟨w ⊗ₜ[ℝ] p, rfl⟩
      · apply Submodule.mem_sup_left
        refine ⟨v (Fin.last n) • p, ?_⟩
        change
          (EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n)) ⊗ₜ[ℝ]
              (v (Fin.last n) • p) =
            (v (Fin.last n) •
              (EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n))) ⊗ₜ[ℝ] p
        simp only [TensorProduct.tmul_smul, TensorProduct.smul_tmul]
  | add x y hx hy => exact Submodule.add_mem _ (hx trivial) (hy trivial)

private def gtFullAxisEmbedding {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) (hn : 2 * r + 5 ≤ n + 1)
    (mu : FullBranchWeight lam) :
    HarmonicYoungSpace (n := n) (fullBranchSignature mu) →ₗᵢ[ℝ]
      (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
        HarmonicYoungSpace (n := n + 1) lam) :=
  (gtFullAxisAmbientInclusion (n := n) lam).comp
    (canonicalFullBranchFibre lam hn mu)

@[simp] theorem gtFullAxisEmbedding_apply {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) (hn : 2 * r + 5 ≤ n + 1)
    (mu : FullBranchWeight lam)
    (p : HarmonicYoungSpace (n := n) (fullBranchSignature mu)) :
    gtFullAxisEmbedding lam hn mu p =
      (EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n)) ⊗ₜ[ℝ]
        canonicalFullBranchFibre lam hn mu p := rfl

theorem gtFullAxisEmbedding_orthogonal {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) (hn : 2 * r + 5 ≤ n + 1)
    (mu nu : FullBranchWeight lam) (hne : mu ≠ nu)
    (p : HarmonicYoungSpace (n := n) (fullBranchSignature mu))
    (q : HarmonicYoungSpace (n := n) (fullBranchSignature nu)) :
    ⟪gtFullAxisEmbedding lam hn mu p,
      gtFullAxisEmbedding lam hn nu q⟫_ℝ = 0 := by
  calc
    ⟪gtFullAxisEmbedding lam hn mu p,
        gtFullAxisEmbedding lam hn nu q⟫_ℝ =
      ⟪canonicalFullBranchFibre lam hn mu p,
        canonicalFullBranchFibre lam hn nu q⟫_ℝ :=
          (gtFullAxisAmbientInclusion (n := n) lam).inner_map_map _ _
    _ = 0 := canonicalFullBranchFibre_orthogonal lam hn mu nu hne p q

theorem gtFullAxisEmbedding_inner_transverse_eq_zero {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) (hn : 2 * r + 5 ≤ n + 1)
    (mu nu : FullBranchWeight lam)
    (p : HarmonicYoungSpace (n := n) (fullBranchSignature mu))
    (x : SpherePacking.Euclidean n ⊗[ℝ]
      HarmonicYoungSpace (n := n) (fullBranchSignature nu)) :
    ⟪gtFullAxisEmbedding lam hn mu p,
      gtFullTransverseEmbedding lam hn nu x⟫_ℝ = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [gtFullAxisEmbedding_apply, EuclideanSpace.basisFun_apply,
              Nat.add_one_sub_one, map_zero, inner_zero_right]
  | tmul v q =>
      rw [gtFullAxisEmbedding_apply]
      change
        ⟪(EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n)) ⊗ₜ[ℝ]
            canonicalFullBranchFibre lam hn mu p,
          gtTransverseEuclideanIsometry n v ⊗ₜ[ℝ]
            canonicalFullBranchFibre lam hn nu q⟫_ℝ = 0
      rw [TensorProduct.inner_tmul]
      have hzero :
          ⟪EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n),
            gtTransverseEuclideanIsometry n v⟫_ℝ = 0 := by
        rw [real_inner_comm]
        exact gtTransverseEuclideanIsometry_orthogonal_last n v
      rw [hzero, zero_mul]
  | add x y hx hy => rw [map_add, inner_add_right, hx, hy, add_zero]

theorem gtFullAxisEmbedding_iSup_range
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (hn : 2 * r + 5 ≤ n + 1) (hdom : Antitone lam) :
    (⨆ mu : FullBranchWeight lam,
      LinearMap.range (gtFullAxisEmbedding lam hn mu).toLinearMap) =
        LinearMap.range
          (gtFullAxisAmbientInclusion (n := n) lam).toLinearMap := by
  calc
    (⨆ mu : FullBranchWeight lam,
      LinearMap.range (gtFullAxisEmbedding lam hn mu).toLinearMap) =
        ⨆ mu : FullBranchWeight lam,
          (LinearMap.range
            (canonicalFullBranchFibre lam hn mu).toLinearMap).map
              (gtFullAxisAmbientInclusion (n := n) lam).toLinearMap := by
          congr 1
          funext mu
          change
            LinearMap.range
                ((gtFullAxisAmbientInclusion (n := n) lam).toLinearMap.comp
                  (canonicalFullBranchFibre lam hn mu).toLinearMap) = _
          rw [LinearMap.range_comp]
    _ = (⨆ mu : FullBranchWeight lam,
          LinearMap.range (canonicalFullBranchFibre lam hn mu).toLinearMap).map
            (gtFullAxisAmbientInclusion (n := n) lam).toLinearMap :=
          (Submodule.map_iSup _ _).symm
    _ = (⊤ : Submodule ℝ
          (HarmonicYoungSpace (n := n + 1) lam)).map
            (gtFullAxisAmbientInclusion (n := n) lam).toLinearMap := by
          rw [canonicalFullBranch_iSup_range_eq_top_unconditional
            lam hn hdom]
    _ = LinearMap.range
          (gtFullAxisAmbientInclusion (n := n) lam).toLinearMap :=
          Submodule.map_top _

theorem gtFullAxisTransverse_iSup_range_eq_top
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (hn : 2 * r + 5 ≤ n + 1) (hdom : Antitone lam) :
    (⨆ mu : FullBranchWeight lam,
      LinearMap.range (gtFullAxisEmbedding lam hn mu).toLinearMap) ⊔
        (⨆ mu : FullBranchWeight lam,
          LinearMap.range (gtFullTransverseEmbedding lam hn mu).toLinearMap) =
      (⊤ : Submodule ℝ
        (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
          HarmonicYoungSpace (n := n + 1) lam)) := by
  rw [gtFullAxisEmbedding_iSup_range lam hn hdom,
    gtFullTransverseEmbedding_iSup_range lam hn hdom]
  exact gtFullAxisAmbientInclusion_sup_transverse_range_eq_top lam

end AllRankGTActualAxisTransverseDecomposition

end

section


open scoped BigOperators InnerProductSpace TensorProduct

namespace AllRankGTPhysicalCompleteBlockReconstruction

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTActualAxisTransverseDecomposition
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseFullBranchDecomposition
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness

theorem inner_eq_zero_of_mem_iSup_range_of_adjoint_eq_zero
    {ι : Type*} {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V]
    (E : ι → Type*)
    [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace ℝ (E i)]
    [∀ i, FiniteDimensional ℝ (E i)]
    (A : (i : ι) → E i →ₗ[ℝ] V)
    (y : V) (hzero : ∀ i : ι, (A i).adjoint y = 0)
    (x : V) (hx : x ∈ ⨆ i : ι, LinearMap.range (A i)) :
    ⟪x, y⟫_ℝ = 0 := by
  refine Submodule.iSup_induction
    (motive := fun z : V => ⟪z, y⟫_ℝ = 0) _ hx ?_ ?_ ?_
  · intro i z hz
    obtain ⟨p, rfl⟩ := hz
    rw [← LinearMap.adjoint_inner_right, hzero i, inner_zero_right]
  · simp only [inner_zero_left]
  · intro u v hu hv
    rw [inner_add_left, hu, hv, add_zero]

theorem eq_zero_of_iSup_range_sup_eq_top_of_adjoint_eq_zero
    {ι κ : Type*} {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V]
    (E : ι → Type*) (F : κ → Type*)
    [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace ℝ (E i)]
    [∀ i, FiniteDimensional ℝ (E i)]
    [∀ j, NormedAddCommGroup (F j)]
    [∀ j, InnerProductSpace ℝ (F j)]
    [∀ j, FiniteDimensional ℝ (F j)]
    (A : (i : ι) → E i →ₗ[ℝ] V)
    (B : (j : κ) → F j →ₗ[ℝ] V)
    (hcomplete :
      (⨆ i : ι, LinearMap.range (A i)) ⊔
        (⨆ j : κ, LinearMap.range (B j)) = ⊤)
    (y : V)
    (haxis : ∀ i : ι, (A i).adjoint y = 0)
    (htransverse : ∀ j : κ, (B j).adjoint y = 0) :
    y = 0 := by
  apply ext_inner_left ℝ
  intro x
  rw [inner_zero_right]
  have hx : x ∈
      (⨆ i : ι, LinearMap.range (A i)) ⊔
        (⨆ j : κ, LinearMap.range (B j)) := by
    rw [hcomplete]
    trivial
  obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hx
  rw [inner_add_left,
    inner_eq_zero_of_mem_iSup_range_of_adjoint_eq_zero E A y haxis u hu,
    inner_eq_zero_of_mem_iSup_range_of_adjoint_eq_zero F B y htransverse v hv,
    add_zero]

theorem eq_of_iSup_range_sup_eq_top_of_adjoint_eq
    {ι κ : Type*} {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V]
    (E : ι → Type*) (F : κ → Type*)
    [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace ℝ (E i)]
    [∀ i, FiniteDimensional ℝ (E i)]
    [∀ j, NormedAddCommGroup (F j)]
    [∀ j, InnerProductSpace ℝ (F j)]
    [∀ j, FiniteDimensional ℝ (F j)]
    (A : (i : ι) → E i →ₗ[ℝ] V)
    (B : (j : κ) → F j →ₗ[ℝ] V)
    (hcomplete :
      (⨆ i : ι, LinearMap.range (A i)) ⊔
        (⨆ j : κ, LinearMap.range (B j)) = ⊤)
    (x y : V)
    (haxis : ∀ i : ι, (A i).adjoint x = (A i).adjoint y)
    (htransverse : ∀ j : κ, (B j).adjoint x = (B j).adjoint y) :
    x = y := by
  apply sub_eq_zero.mp
  apply eq_zero_of_iSup_range_sup_eq_top_of_adjoint_eq_zero
    E F A B hcomplete (x - y)
  · intro i
    rw [map_sub, haxis i, sub_self]
  · intro j
    rw [map_sub, htransverse j, sub_self]

end AllRankGTPhysicalCompleteBlockReconstruction

end

section


open scoped BigOperators InnerProductSpace TensorProduct

namespace AllRankGTValidTransverseArrowheadRow

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherRepresentationGraph (Interlaces)

private def canonicalGelfandTsetlinAxisIsometry
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h) :
    HarmonicYoungSpace (n := n) mu →ₗᵢ[ℝ]
      (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
        HarmonicYoungSpace (n := n + 1) lam) :=
  (canonicalGelfandTsetlinAxisTensor lam mu h hgram).isometryOfInner
    (canonicalGelfandTsetlinAxisTensor_inner lam mu h hgram)

end AllRankGTValidTransverseArrowheadRow

end

section


open scoped BigOperators InnerProductSpace TensorProduct

namespace AllRankGTPhysicalRetainedAdditiveColumn

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTActualAxisTransverseDecomposition
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTPhysicalCompleteBlockReconstruction
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseFullBranchDecomposition
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTValidTransverseArrowheadRow
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness

theorem linearMap_comp_eq_smul_add_of_complete_adjoint_block_rows
    {ι κ E F V : Type*}
    [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V]
    (X : ι → Type*) (Y : κ → Type*)
    [∀ i, NormedAddCommGroup (X i)]
    [∀ i, InnerProductSpace ℝ (X i)]
    [∀ i, FiniteDimensional ℝ (X i)]
    [∀ j, NormedAddCommGroup (Y j)]
    [∀ j, InnerProductSpace ℝ (Y j)]
    [∀ j, FiniteDimensional ℝ (Y j)]
    (C : (i : ι) → X i →ₗ[ℝ] V)
    (D : (j : κ) → Y j →ₗ[ℝ] V)
    (hcomplete :
      (⨆ i : ι, LinearMap.range (C i)) ⊔
        (⨆ j : κ, LinearMap.range (D j)) = ⊤)
    (T : Module.End ℝ V)
    (B : E →ₗ[ℝ] V) (A : F →ₗ[ℝ] V)
    (K : E →ₗ[ℝ] F) (d : ℝ)
    (haxis : ∀ i : ι,
      (C i).adjoint.comp (T.comp B) =
        d • ((C i).adjoint.comp B) +
          ((C i).adjoint.comp A).comp K)
    (htransverse : ∀ j : κ,
      (D j).adjoint.comp (T.comp B) =
        d • ((D j).adjoint.comp B) +
          ((D j).adjoint.comp A).comp K) :
    T.comp B = d • B + A.comp K := by
  apply LinearMap.ext
  intro p
  apply eq_of_iSup_range_sup_eq_top_of_adjoint_eq
    X Y C D hcomplete (T (B p)) (d • B p + A (K p))
  · intro i
    have hi := LinearMap.congr_fun (haxis i) p
    simpa only [LinearMap.comp_apply, LinearMap.add_apply,
      LinearMap.smul_apply, map_add, map_smul] using hi
  · intro j
    have hj := LinearMap.congr_fun (htransverse j) p
    simpa only [LinearMap.comp_apply, LinearMap.add_apply,
      LinearMap.smul_apply, map_add, map_smul] using hj

theorem gtRelativeCasimir_comp_eq_smul_add_of_full_axis_transverse_rows
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (hn : 2 * r + 5 ≤ n + 1) (hdom : Antitone lam)
    {E F : Type*}
    [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F]
    (B : E →ₗ[ℝ]
      (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
        HarmonicYoungSpace (n := n + 1) lam))
    (A : F →ₗ[ℝ]
      (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
        HarmonicYoungSpace (n := n + 1) lam))
    (K : E →ₗ[ℝ] F) (d : ℝ)
    (haxis : ∀ mu : FullBranchWeight lam,
      (gtFullAxisEmbedding lam hn mu).toLinearMap.adjoint.comp
          ((gtRelativeCasimir (n := n + 1) lam).comp B) =
        d • ((gtFullAxisEmbedding lam hn mu).toLinearMap.adjoint.comp B) +
          ((gtFullAxisEmbedding lam hn mu).toLinearMap.adjoint.comp A).comp K)
    (htransverse : ∀ mu : FullBranchWeight lam,
      (gtFullTransverseEmbedding lam hn mu).toLinearMap.adjoint.comp
          ((gtRelativeCasimir (n := n + 1) lam).comp B) =
        d • ((gtFullTransverseEmbedding lam hn mu).toLinearMap.adjoint.comp B) +
          ((gtFullTransverseEmbedding lam hn mu).toLinearMap.adjoint.comp A).comp K) :
    (gtRelativeCasimir (n := n + 1) lam).comp B =
      d • B + A.comp K := by
  exact linearMap_comp_eq_smul_add_of_complete_adjoint_block_rows
    (fun mu : FullBranchWeight lam =>
      HarmonicYoungSpace (n := n) (fullBranchSignature mu))
    (fun mu : FullBranchWeight lam =>
      SpherePacking.Euclidean n ⊗[ℝ]
        HarmonicYoungSpace (n := n) (fullBranchSignature mu))
    (fun mu => (gtFullAxisEmbedding lam hn mu).toLinearMap)
    (fun mu => (gtFullTransverseEmbedding lam hn mu).toLinearMap)
    (gtFullAxisTransverse_iSup_range_eq_top lam hn hdom)
    (gtRelativeCasimir (n := n + 1) lam) B A K d haxis htransverse

theorem gtRelativeCasimir_comp_eq_smul_add_of_orthogonal_full_block_rows
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (hn : 2 * r + 5 ≤ n + 1) (hdom : Antitone lam)
    {E F : Type*}
    [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F]
    (B : E →ₗ[ℝ]
      (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
        HarmonicYoungSpace (n := n + 1) lam))
    (A : F →ₗ[ℝ]
      (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
        HarmonicYoungSpace (n := n + 1) lam))
    (K : E →ₗ[ℝ] F) (d : ℝ)
    (haxisOrth : ∀ mu : FullBranchWeight lam,
      (gtFullAxisEmbedding lam hn mu).toLinearMap.adjoint.comp B = 0)
    (htransverseOrth : ∀ mu : FullBranchWeight lam,
      (gtFullTransverseEmbedding lam hn mu).toLinearMap.adjoint.comp A = 0)
    (haxis : ∀ mu : FullBranchWeight lam,
      (gtFullAxisEmbedding lam hn mu).toLinearMap.adjoint.comp
          ((gtRelativeCasimir (n := n + 1) lam).comp B) =
        ((gtFullAxisEmbedding lam hn mu).toLinearMap.adjoint.comp A).comp K)
    (htransverse : ∀ mu : FullBranchWeight lam,
      (gtFullTransverseEmbedding lam hn mu).toLinearMap.adjoint.comp
          ((gtRelativeCasimir (n := n + 1) lam).comp B) =
        d • ((gtFullTransverseEmbedding lam hn mu).toLinearMap.adjoint.comp B)) :
    (gtRelativeCasimir (n := n + 1) lam).comp B =
      d • B + A.comp K := by
  apply gtRelativeCasimir_comp_eq_smul_add_of_full_axis_transverse_rows
    lam hn hdom B A K d
  · intro mu
    rw [haxisOrth mu, smul_zero, zero_add, haxis mu]
  · intro mu
    rw [htransverseOrth mu, LinearMap.zero_comp, add_zero,
      htransverse mu]

end AllRankGTPhysicalRetainedAdditiveColumn

end

section


open scoped BigOperators InnerProductSpace TensorProduct

namespace AllRankGTRelativeCasimirCrossBlock

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirCompressedResolvent
open MetricCodes.Spherical.HigherRepresentationGraph (Interlaces)

private def gtTransverseAxisCrossBlock
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (B : HarmonicYoungSpace (n := n) mu →ₗ[ℝ]
      (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
        HarmonicYoungSpace (n := n + 1) lam)) :
    Module.End ℝ (HarmonicYoungSpace (n := n) mu) :=
  (canonicalGelfandTsetlinAxisTensor lam mu h hgram).adjoint.comp
    ((gtRelativeCasimir lam).comp B)

end AllRankGTRelativeCasimirCrossBlock

end

section


open scoped TensorProduct

namespace AllRankGTPhysicalPaddedPieriFullEigen

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTInvalidNonterminalProjectorVanishing
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirZeroRowTransport
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransportedPieriOrthogonality
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankZeroRowTensorCasimirConjugacy
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriActualChannels
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriSourceSignatureInjectivity
open MetricCodes.Spherical.ThreeRowYoungBranching

theorem physicalPaddedPieriChannel_relativeCasimir
    {r n : ℕ} (hn : 2 * (r + 1) + 4 ≤ n)
    (lam : Fin (r + 1) → ℕ)
    (hdom : Antitone (appendZeroWeight lam))
    (i : PaddedPieriChannel (appendZeroWeight lam))
    (p : HarmonicYoungSpace (n := n)
      (paddedPieriSource (appendZeroWeight lam) i)) :
    gtRelativeCasimir (n := n) lam
        (physicalPaddedPieriChannel hn lam hdom i p) =
      HigherChannel.signedNode
        (HigherChannel.ambientShift n (appendZeroWeight lam))
        (paddedPieriSignedChannel (appendZeroWeight lam) i) •
        physicalPaddedPieriChannel hn lam hdom i p := by
  exact zeroRowTransportPaddedPieriChannel_eigen_of_intertwine
    lam
    (paddedOrthogonalTensorPieriChannel hn
      (appendZeroWeight lam) hdom i)
    (zeroRowTensorIsometryEquiv_symm_relativeCasimir_intertwine lam).symm
    (HigherChannel.signedNode
      (HigherChannel.ambientShift n (appendZeroWeight lam))
      (paddedPieriSignedChannel (appendZeroWeight lam) i))
    p
    (paddedOrthogonalTensorPieriChannel_relativeCasimir hn
      (appendZeroWeight lam) hdom i p)

end AllRankGTPhysicalPaddedPieriFullEigen

end

section


open scoped BigOperators InnerProductSpace TensorProduct

namespace AllRankGTSelectedMuAxisProjectionVanishing

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCanonicalSelectedBranchRange
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTActualAxisTransverseDecomposition
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTInvalidNonterminalProjectorVanishing
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTPhysicalPaddedPieriFullEigen
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransportedPieriOrthogonality
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTValidTransverseArrowheadRow
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankOrthogonalBranchCompleteness
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankZeroRowTensorCasimirConjugacy
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension
open MetricCodes.Spherical.HigherHarmonicYoung.ClebschRotation
open MetricCodes.Spherical.HigherHarmonicYoung.CrossGram
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness
open MetricCodes.Spherical.HigherYoungAllRankDistinctSignatureStabilizerIntertwiner
open MetricCodes.Spherical.HigherYoungAllRankGTAxisTensorRotationIntertwining
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriActualChannels
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriSourceSignatureInjectivity
open MetricCodes.Spherical.HigherYoungAllRankZeroRowRotationEquivariance
open MetricCodes.Spherical.ThreeRowYoungBranching

theorem physicalPaddedPieriChannel_rotation_intertwine
    {r n : ℕ} (hn : 2 * (r + 1) + 4 ≤ n)
    (lam : Fin (r + 1) → ℕ)
    (hdom : Antitone (appendZeroWeight lam))
    (i : PaddedPieriChannel (appendZeroWeight lam))
    (a b : Fin n) :
    (physicalPaddedPieriChannel hn lam hdom i).toLinearMap.comp
        (youngAmbientRotation
          (paddedPieriSource (appendZeroWeight lam) i) a b) =
      (tensorAmbientRotation lam a b).comp
        (physicalPaddedPieriChannel hn lam hdom i).toLinearMap := by
  apply LinearMap.ext
  intro p
  let Z := (zeroRowTensorIsometryEquiv (n := n) lam).symm.toLinearMap
  let A := (paddedOrthogonalTensorPieriChannel
    hn (appendZeroWeight lam) hdom i).toLinearMap
  change Z (A (youngAmbientRotation
    (paddedPieriSource (appendZeroWeight lam) i) a b p)) =
      tensorAmbientRotation lam a b (Z (A p))
  have hA := LinearMap.congr_fun
    (paddedOrthogonalTensorPieriChannel_rotation_intertwine
      hn (appendZeroWeight lam) hdom i a b) p
  have hZ := LinearMap.congr_fun
    (zeroRowTensorIsometryEquiv_symm_rotation_intertwine lam a b) (A p)
  exact (congrArg Z hA).trans hZ

theorem gtRelativeCasimir_tensorAmbientRotation_commute
    {r n : ℕ} (hn : 2 * (r + 1) + 4 ≤ n)
    (lam : Fin (r + 1) → ℕ)
    (hdom : Antitone (appendZeroWeight lam))
    (a b : Fin n) :
    (gtRelativeCasimir (n := n) lam).comp
        (tensorAmbientRotation lam a b) =
      (tensorAmbientRotation lam a b).comp
        (gtRelativeCasimir (n := n) lam) := by
  classical
  let A := physicalPaddedPieriChannel hn lam hdom
  have hcomplete :
      (⨆ i : PaddedPieriChannel (appendZeroWeight lam),
        LinearMap.range (A i).toLinearMap) =
      (⊤ : Submodule ℝ
        (SpherePacking.Euclidean n ⊗[ℝ]
          HarmonicYoungSpace (n := n) lam)) :=
    orthogonalBranch_iSup_range_eq_top A
      (physicalPaddedPieriChannel_inner_eq_zero hn lam hdom)
      (physicalPaddedPieriChannel_finrank hn lam hdom)
  apply LinearMap.ext
  intro x
  have hx : x ∈ ⨆ i : PaddedPieriChannel (appendZeroWeight lam),
      LinearMap.range (A i).toLinearMap := by
    rw [hcomplete]
    trivial
  change
    gtRelativeCasimir lam (tensorAmbientRotation lam a b x) =
      tensorAmbientRotation lam a b (gtRelativeCasimir lam x)
  refine Submodule.iSup_induction
    (motive := fun x =>
      gtRelativeCasimir lam (tensorAmbientRotation lam a b x) =
        tensorAmbientRotation lam a b (gtRelativeCasimir lam x))
    _ hx ?_ ?_ ?_
  · intro i x hxi
    obtain ⟨p, rfl⟩ := hxi
    let d := signedNode
      (HigherChannel.ambientShift n (appendZeroWeight lam))
      (paddedPieriSignedChannel (appendZeroWeight lam) i)
    have hrot := LinearMap.congr_fun
      (physicalPaddedPieriChannel_rotation_intertwine hn lam hdom i a b) p
    change
      A i (youngAmbientRotation
        (paddedPieriSource (appendZeroWeight lam) i) a b p) =
        tensorAmbientRotation lam a b (A i p) at hrot
    have heigen (q : HarmonicYoungSpace (n := n)
        (paddedPieriSource (appendZeroWeight lam) i)) :
        gtRelativeCasimir lam (A i q) = d • A i q := by
      simpa only [A, d] using
        physicalPaddedPieriChannel_relativeCasimir hn lam hdom i q
    calc
      gtRelativeCasimir lam
          (tensorAmbientRotation lam a b (A i p)) =
        gtRelativeCasimir lam
          (A i (youngAmbientRotation
            (paddedPieriSource (appendZeroWeight lam) i) a b p)) :=
          congrArg (gtRelativeCasimir lam) hrot.symm
      _ = d • A i (youngAmbientRotation
          (paddedPieriSource (appendZeroWeight lam) i) a b p) :=
          heigen _
      _ = d • tensorAmbientRotation lam a b (A i p) :=
          congrArg (d • ·) hrot
      _ = tensorAmbientRotation lam a b (d • A i p) :=
          (map_smul (tensorAmbientRotation lam a b) d (A i p)).symm
      _ = tensorAmbientRotation lam a b
            (gtRelativeCasimir lam (A i p)) :=
          congrArg (tensorAmbientRotation lam a b) (heigen p).symm
  · simp only [map_zero]
  · intro x y hx hy
    simpa only [map_add] using congrArg₂ (· + ·) hx hy

theorem gtFullAxisEmbedding_rotation_intertwine
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (hn : 2 * r + 5 ≤ n + 1)
    (nu : FullBranchWeight lam) (a b : Fin n) :
    (gtFullAxisEmbedding lam hn nu).toLinearMap.comp
        (youngAmbientRotation (fullBranchSignature nu) a b) =
      (tensorAmbientRotation lam a.castSucc b.castSucc).comp
        (gtFullAxisEmbedding lam hn nu).toLinearMap := by
  apply LinearMap.ext
  intro p
  change
    (EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n)) ⊗ₜ[ℝ]
        canonicalFullBranchFibre lam hn nu
          (youngAmbientRotation (fullBranchSignature nu) a b p) =
      tensorAmbientRotation lam a.castSucc b.castSucc
        ((EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n)) ⊗ₜ[ℝ]
          canonicalFullBranchFibre lam hn nu p)
  rw [tensorAmbientRotation_tmul,
    euclideanAmbientRotation_castSucc_last,
    TensorProduct.zero_tmul, zero_add]
  exact congrArg
    (fun q => (EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n))
      ⊗ₜ[ℝ] q)
    (LinearMap.congr_fun
      (canonicalFullBranchFibre_rotation_intertwine lam hn nu a b) p)

theorem gtFullAxisEmbedding_selected_range_eq_canonicalAxis
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ)
    (hmu : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu hmu) :
    LinearMap.range
        (gtFullAxisEmbedding (n := n) lam hn
          (fullBranchOfInterlaces mu hmu)).toLinearMap =
      LinearMap.range
        (canonicalGelfandTsetlinAxisIsometry
          lam mu hmu hgram).toLinearMap := by
  change
    LinearMap.range
        ((gtFullAxisAmbientInclusion (n := n) lam).toLinearMap.comp
          (canonicalFullBranchFibre lam hn
            (fullBranchOfInterlaces mu hmu)).toLinearMap) =
      LinearMap.range
        ((gtFullAxisAmbientInclusion (n := n) lam).toLinearMap.comp
          (canonicalGelfandTsetlinFibre lam mu hmu hgram).toLinearMap)
  rw [LinearMap.range_comp, LinearMap.range_comp,
    canonicalGelfandTsetlinFibre_range_eq_selectedFullBranch
      lam mu hmu hn hmu.antitone_ambient hgram]

theorem gtFullAxisEmbedding_adjoint_relativeCasimir_stabilizerSector_eq_zero
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ)
    (hmu : Interlaces lam mu)
    (hstable : 2 * (r + 2) + 5 ≤ n + 1)
    (nu : FullBranchWeight lam)
    (hne : fullBranchSignature nu ≠ appendZeroWeight mu)
    (B : HarmonicYoungSpace (n := n) mu →ₗ[ℝ]
      (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
        HarmonicYoungSpace (n := n + 1) lam))
    (hB : ∀ a b : Fin n,
      B.comp (youngAmbientRotation mu a b) =
        (tensorAmbientRotation lam a.castSucc b.castSucc).comp B)
    (p : HarmonicYoungSpace (n := n) mu) :
    (gtFullAxisEmbedding (n := n) lam (by omega) nu).toLinearMap.adjoint
      (gtRelativeCasimir (n := n + 1) lam (B p)) = 0 := by
  let Z := appendZeroRowIsometryEquiv (n := n) mu
  let F := (gtFullAxisEmbedding (n := n) lam (by omega) nu).toLinearMap
  let Bpad := B.comp Z.symm.toLinearMap
  let C := (gtRelativeCasimir (n := n + 1) lam).comp Bpad
  have hdom : Antitone (appendZeroWeight lam) :=
    (fullBranchSignature_interlaces_appendZeroWeight lam
      (fullBranchOfInterlaces mu hmu)).antitone_ambient
  have hdommu : Antitone (appendZeroWeight mu) := by
    rw [← fullBranchOfInterlaces_signature_eq_appendZeroWeight mu hmu]
    exact fullBranchSignature_antitone (fullBranchOfInterlaces mu hmu)
  have hBpad (a b : Fin n) :
      Bpad.comp (youngAmbientRotation (appendZeroWeight mu) a b) =
        (tensorAmbientRotation lam a.castSucc b.castSucc).comp Bpad := by
    apply LinearMap.ext
    intro q
    have hZ := LinearMap.congr_fun
      (appendZeroRowIsometryEquiv_symm_rotation_intertwine mu a b) q
    have hactual := LinearMap.congr_fun (hB a b) (Z.symm q)
    change B (Z.symm (youngAmbientRotation
      (appendZeroWeight mu) a b q)) =
        tensorAmbientRotation lam a.castSucc b.castSucc
          (B (Z.symm q))
    exact (congrArg B hZ).trans hactual
  have hC (a b : Fin n) :
      C.comp (youngAmbientRotation (appendZeroWeight mu) a b) =
        (tensorAmbientRotation lam a.castSucc b.castSucc).comp C := by
    calc
      C.comp (youngAmbientRotation (appendZeroWeight mu) a b) =
        (gtRelativeCasimir (n := n + 1) lam).comp
          (Bpad.comp (youngAmbientRotation (appendZeroWeight mu) a b)) := by
            ext q
            rfl
      _ = (gtRelativeCasimir (n := n + 1) lam).comp
          ((tensorAmbientRotation lam a.castSucc b.castSucc).comp Bpad) := by
            rw [hBpad a b]
      _ = ((gtRelativeCasimir (n := n + 1) lam).comp
          (tensorAmbientRotation lam a.castSucc b.castSucc)).comp Bpad := by
            ext q
            rfl
      _ = ((tensorAmbientRotation lam a.castSucc b.castSucc).comp
          (gtRelativeCasimir (n := n + 1) lam)).comp Bpad := by
            rw [gtRelativeCasimir_tensorAmbientRotation_commute
              (by omega) lam hdom a.castSucc b.castSucc]
      _ = (tensorAmbientRotation lam a.castSucc b.castSucc).comp C := by
            ext q
            rfl
  have hzero : F.adjoint.comp C = 0 := by
    apply youngRotationIntertwiner_eq_zero_of_signature_ne
      (by omega : 2 * ((r + 1) + 1) + 2 ≤ n)
      (appendZeroWeight mu) (fullBranchSignature nu)
      hdommu (Ne.symm hne)
    intro a b
    exact crossGram_intertwines_of_skew F C
      (youngAmbientRotation (fullBranchSignature nu) a b)
      (youngAmbientRotation (appendZeroWeight mu) a b)
      (tensorAmbientRotation lam a.castSucc b.castSucc)
      (youngAmbientRotation_adjoint (fullBranchSignature nu) a b)
      (tensorAmbientRotation_adjoint lam a.castSucc b.castSucc)
      (gtFullAxisEmbedding_rotation_intertwine lam (by omega) nu a b)
      (hC a b)
  have hp := LinearMap.congr_fun hzero (Z p)
  change F.adjoint
    (gtRelativeCasimir lam (B (Z.symm (Z p)))) = 0 at hp
  simpa only [LinearIsometryEquiv.symm_apply_apply] using hp

end AllRankGTSelectedMuAxisProjectionVanishing

end

end HigherHarmonicYoung

end Spherical

end MetricCodes


namespace MetricCodes

namespace Spherical

namespace HigherHarmonicYoung

section

open scoped BigOperators InnerProductSpace TensorProduct

namespace AllRankGTFullTransverseSameSignatureRow

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCanonicalSelectedBranchRange
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTNormalizedTransverseSector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCasimirEmbedding
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseFullBranchDecomposition
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseTensorRelativeCompression
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseWignerEckartPhase
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInternalRowLowerGram
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness
open MetricCodes.Spherical.HigherYoungAllRankGTArrowheadSchurComplement
open MetricCodes.Spherical.HigherYoungAllRankSelectedBranchSignature
open MetricCodes.Spherical.ThreeRowYoungBranching

theorem tensor_mapIsometry_range_eq_of_second_range_eq
    {E F X Y Z : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
    (e : E →ₗᵢ[ℝ] F) (g : X →ₗᵢ[ℝ] Z) (h : Y →ₗᵢ[ℝ] Z)
    (heq : LinearMap.range g.toLinearMap = LinearMap.range h.toLinearMap) :
    LinearMap.range (TensorProduct.mapIsometry e g).toLinearMap =
      LinearMap.range (TensorProduct.mapIsometry e h).toLinearMap := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    induction x using TensorProduct.induction_on with
    | zero => exact Submodule.zero_mem _
    | add x y hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
    | tmul v p =>
        have hmem : g p ∈ LinearMap.range h.toLinearMap := by
          rw [← heq]
          exact ⟨p, rfl⟩
        obtain ⟨q, hq⟩ := hmem
        change h q = g p at hq
        refine ⟨v ⊗ₜ[ℝ] q, ?_⟩
        change e v ⊗ₜ[ℝ] h q = e v ⊗ₜ[ℝ] g p
        rw [hq]
  · rintro _ ⟨x, rfl⟩
    induction x using TensorProduct.induction_on with
    | zero => exact Submodule.zero_mem _
    | add x y hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
    | tmul v p =>
        have hmem : h p ∈ LinearMap.range g.toLinearMap := by
          rw [heq]
          exact ⟨p, rfl⟩
        obtain ⟨q, hq⟩ := hmem
        change g q = h p at hq
        refine ⟨v ⊗ₜ[ℝ] q, ?_⟩
        change e v ⊗ₜ[ℝ] g q = e v ⊗ₜ[ℝ] h p
        rw [hq]

theorem adjoint_eigen_of_range_le
    {X Y H : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    (I : X →ₗ[ℝ] H) (J : Y →ₗ[ℝ] H)
    (hrange : LinearMap.range J ≤ LinearMap.range I)
    (T : Module.End ℝ H) (x : H) (d : ℝ)
    (hI : I.adjoint (T x) = d • I.adjoint x) :
    J.adjoint (T x) = d • J.adjoint x := by
  apply ext_inner_left ℝ
  intro q
  obtain ⟨z, hz⟩ := hrange (show J q ∈ LinearMap.range J from ⟨q, rfl⟩)
  calc
    ⟪q, J.adjoint (T x)⟫_ℝ = ⟪J q, T x⟫_ℝ :=
      LinearMap.adjoint_inner_right J q (T x)
    _ = ⟪I z, T x⟫_ℝ := by rw [hz]
    _ = ⟪z, I.adjoint (T x)⟫_ℝ :=
      (LinearMap.adjoint_inner_right I z (T x)).symm
    _ = ⟪z, d • I.adjoint x⟫_ℝ := by rw [hI]
    _ = d * ⟪z, I.adjoint x⟫_ℝ := real_inner_smul_right z (I.adjoint x) d
    _ = d * ⟪I z, x⟫_ℝ := by rw [LinearMap.adjoint_inner_right]
    _ = d * ⟪J q, x⟫_ℝ := by rw [hz]
    _ = ⟪q, d • J.adjoint x⟫_ℝ := by
      rw [real_inner_smul_right, LinearMap.adjoint_inner_right]

theorem gtTransverseTensorEmbedding_range_eq_selectedFull
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hdom : Antitone lam)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h) :
    LinearMap.range (gtTransverseTensorEmbedding lam mu h hgram).toLinearMap =
      LinearMap.range
        (gtFullTransverseEmbedding lam hn (fullBranchOfInterlaces mu h)).toLinearMap := by
  exact tensor_mapIsometry_range_eq_of_second_range_eq
    (gtTransverseEuclideanIsometry n)
    (canonicalGelfandTsetlinFibre lam mu h hgram)
    (canonicalFullBranchFibre lam hn (fullBranchOfInterlaces mu h))
    (canonicalGelfandTsetlinFibre_range_eq_selectedFullBranch
      lam mu h hn hdom hgram)

theorem negativeSector_shortTensor_adjoint_eigen
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (kappa : Fin r → ℕ)
    (row : Fin (r + 1))
    (hnu : Interlaces lam (raiseWeight mu row))
    (hnuGram : PositiveGelfandTsetlinFischerGram
      (n := n) lam (raiseWeight mu row) hnu)
    (hfinite : FiniteInterlacing n mu kappa)
    (hraise : FiniteInterlacing n (raiseWeight mu row) kappa)
    (p : HarmonicYoungSpace (n := n) mu) :
    let I := gtTransverseTensorEmbedding lam (raiseWeight mu row) hnu hnuGram
    let B := normalizedGTTransverseNegativeSector lam mu kappa row
      hnu hnuGram hfinite hraise
    let d := gtStabilizerArrowheadNode (wallShift (n + 1) (r + 1))
      (MetricCodes.Spherical.HigherChannel.stabilizerShift (n + 1) mu)
        (.inr (row, false))
    I.toLinearMap.adjoint
      (gtRelativeCasimir (n := n + 1) lam (B p)) =
        d • I.toLinearMap.adjoint (B p) := by
  dsimp
  let c : ℝ := (Real.sqrt
    (internalRowLowerGramScalar (raiseWeight mu row) row *
      weylEdgeRatio n mu row))⁻¹
  let C := youngClebschRaise (n := n) (raiseWeight mu row) mu
    (sum_raiseWeight mu row) row
  have hphase :
      normalizedGTTransverseNegativeSector lam mu kappa row
          hnu hnuGram hfinite hraise p =
        c • gtTransverseNegativeSector lam mu row hnu hnuGram p := by
    change (normalizedGTTransverseNegativeSector lam mu kappa row
      hnu hnuGram hfinite hraise).toLinearMap p = _
    rw [normalizedGTTransverseNegativeSector_toLinearMap]
    rfl
  have hself :
      (gtTransverseTensorEmbedding lam (raiseWeight mu row)
          hnu hnuGram).toLinearMap.adjoint
        (gtTransverseNegativeSector lam mu row hnu hnuGram p) = C p := by
    exact LinearMap.congr_fun
      (gtTransverseTensorEmbedding lam (raiseWeight mu row)
        hnu hnuGram).adjoint_comp_self' (C p)
  rw [hphase, map_smul, map_smul, map_smul,
    gtTransverseNegativeSector_relativeCasimir_adjoint_compression,
    hself]
  exact smul_comm _ _ _

theorem negativeSector_selectedFullTensor_adjoint_eigen
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (kappa : Fin r → ℕ)
    (row : Fin (r + 1))
    (hnu : Interlaces lam (raiseWeight mu row))
    (hnuGram : PositiveGelfandTsetlinFischerGram
      (n := n) lam (raiseWeight mu row) hnu)
    (hfinite : FiniteInterlacing n mu kappa)
    (hraise : FiniteInterlacing n (raiseWeight mu row) kappa)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (p : HarmonicYoungSpace (n := n) mu) :
    let J := gtFullTransverseEmbedding lam hn
      (fullBranchOfInterlaces (raiseWeight mu row) hnu)
    let B := normalizedGTTransverseNegativeSector lam mu kappa row
      hnu hnuGram hfinite hraise
    let d := gtStabilizerArrowheadNode (wallShift (n + 1) (r + 1))
      (MetricCodes.Spherical.HigherChannel.stabilizerShift (n + 1) mu)
        (.inr (row, false))
    J.toLinearMap.adjoint
      (gtRelativeCasimir (n := n + 1) lam (B p)) =
        d • J.toLinearMap.adjoint (B p) := by
  dsimp
  apply adjoint_eigen_of_range_le
    (gtTransverseTensorEmbedding lam (raiseWeight mu row) hnu hnuGram).toLinearMap
    (gtFullTransverseEmbedding lam hn
      (fullBranchOfInterlaces (raiseWeight mu row) hnu)).toLinearMap
    (le_of_eq
      (gtTransverseTensorEmbedding_range_eq_selectedFull
        lam (raiseWeight mu row) hnu hn hnu.antitone_ambient hnuGram).symm)
    (gtRelativeCasimir (n := n + 1) lam)
    (normalizedGTTransverseNegativeSector lam mu kappa row
      hnu hnuGram hfinite hraise p)
    (gtStabilizerArrowheadNode (wallShift (n + 1) (r + 1))
      (MetricCodes.Spherical.HigherChannel.stabilizerShift (n + 1) mu)
        (.inr (row, false)))
  exact negativeSector_shortTensor_adjoint_eigen
    lam mu kappa row hnu hnuGram hfinite hraise p

theorem positiveSector_shortTensor_adjoint_eigen
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu nu : Fin (r + 1) → ℕ) (row : Fin (r + 1))
    (hmunu : mu = raiseWeight nu row)
    (hmu : Interlaces lam mu)
    (hnu : Interlaces lam nu)
    (hnuGram : PositiveGelfandTsetlinFischerGram
      (n := n) lam nu hnu)
    (p : HarmonicYoungSpace (n := n) mu) :
    let I := gtTransverseTensorEmbedding lam nu hnu hnuGram
    let B := normalizedGTTransversePositiveSector
      lam mu nu row hmunu hmu hnu hnuGram
    let d := gtStabilizerArrowheadNode (wallShift (n + 1) (r + 1))
      (MetricCodes.Spherical.HigherChannel.stabilizerShift (n + 1) mu)
        (.inr (row, true))
    I.toLinearMap.adjoint
      (gtRelativeCasimir (n := n + 1) lam (B p)) =
        d • I.toLinearMap.adjoint (B p) := by
  dsimp
  let c : ℝ := (Real.sqrt (internalRowLowerGramScalar mu row))⁻¹
  let C := youngClebschLower (n := n) nu mu
    (by rw [hmunu]; exact sum_raiseWeight nu row) row
  have hphase :
      normalizedGTTransversePositiveSector
          lam mu nu row hmunu hmu hnu hnuGram p =
        c • gtTransversePositiveSector lam mu nu row hmunu hnu hnuGram p := by
    change (normalizedGTTransversePositiveSector
      lam mu nu row hmunu hmu hnu hnuGram).toLinearMap p = _
    rw [normalizedGTTransversePositiveSector_toLinearMap]
    rfl
  have hself :
      (gtTransverseTensorEmbedding lam nu hnu hnuGram).toLinearMap.adjoint
        (gtTransversePositiveSector lam mu nu row hmunu hnu hnuGram p) =
          C p := by
    exact LinearMap.congr_fun
      (gtTransverseTensorEmbedding lam nu hnu hnuGram).adjoint_comp_self'
      (C p)
  rw [hphase, map_smul, map_smul, map_smul,
    gtTransversePositiveSector_relativeCasimir_adjoint_compression,
    hself]
  exact smul_comm _ _ _

theorem positiveSector_selectedFullTensor_adjoint_eigen
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu nu : Fin (r + 1) → ℕ) (row : Fin (r + 1))
    (hmunu : mu = raiseWeight nu row)
    (hmu : Interlaces lam mu)
    (hnu : Interlaces lam nu)
    (hnuGram : PositiveGelfandTsetlinFischerGram
      (n := n) lam nu hnu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (p : HarmonicYoungSpace (n := n) mu) :
    let J := gtFullTransverseEmbedding lam hn (fullBranchOfInterlaces nu hnu)
    let B := normalizedGTTransversePositiveSector
      lam mu nu row hmunu hmu hnu hnuGram
    let d := gtStabilizerArrowheadNode (wallShift (n + 1) (r + 1))
      (MetricCodes.Spherical.HigherChannel.stabilizerShift (n + 1) mu)
        (.inr (row, true))
    J.toLinearMap.adjoint
      (gtRelativeCasimir (n := n + 1) lam (B p)) =
        d • J.toLinearMap.adjoint (B p) := by
  dsimp
  apply adjoint_eigen_of_range_le
    (gtTransverseTensorEmbedding lam nu hnu hnuGram).toLinearMap
    (gtFullTransverseEmbedding lam hn
      (fullBranchOfInterlaces nu hnu)).toLinearMap
    (le_of_eq
      (gtTransverseTensorEmbedding_range_eq_selectedFull
        lam nu hnu hn hnu.antitone_ambient hnuGram).symm)
    (gtRelativeCasimir (n := n + 1) lam)
    (normalizedGTTransversePositiveSector
      lam mu nu row hmunu hmu hnu hnuGram p)
    (gtStabilizerArrowheadNode (wallShift (n + 1) (r + 1))
      (MetricCodes.Spherical.HigherChannel.stabilizerShift (n + 1) mu)
        (.inr (row, true)))
  exact positiveSector_shortTensor_adjoint_eigen
    lam mu nu row hmunu hmu hnu hnuGram p

end AllRankGTFullTransverseSameSignatureRow

end

section


open scoped InnerProductSpace TensorProduct

namespace AllRankGTWallFullTransverseFactorization

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCasimirEmbedding
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseFullBranchDecomposition
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallSectorIsometry
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallTransverseCompression
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension
open MetricCodes.Spherical.HigherRepresentationGraph (Interlaces)
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness
open MetricCodes.Spherical.ThreeRowYoungBranching

theorem gtWallCanonicalFullBranchFibre_range_eq_fullBranch
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hlast : 0 < lam (Fin.last (r + 1))) :
    LinearMap.range (gtWallCanonicalFullBranchFibre lam mu h hn hlast).toLinearMap =
      LinearMap.range (canonicalFullBranchFibre lam hn
        (gtWallFullBranch lam mu h hlast)).toLinearMap := by
  unfold gtWallCanonicalFullBranchFibre
  have transport_range_eq {signature : Fin (r + 2) → ℕ}
      (hsignature :
        fullBranchSignature (gtWallFullBranch lam mu h hlast) = signature) :
      LinearMap.range
          (hsignature ▸
            (canonicalFullBranchFibre lam hn
              (gtWallFullBranch lam mu h hlast))).toLinearMap =
        LinearMap.range
          (canonicalFullBranchFibre lam hn
            (gtWallFullBranch lam mu h hlast)).toLinearMap := by
    subst signature
    rfl
  exact transport_range_eq (gtWallFullBranch_signature lam mu h hlast)

theorem gtTransverseWallTensorEmbedding_range_eq_fullTransverse
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hlast : 0 < lam (Fin.last (r + 1))) :
    LinearMap.range
        (gtTransverseWallTensorEmbedding lam mu h hn hlast).toLinearMap =
      LinearMap.range
        (gtFullTransverseEmbedding lam hn
          (gtWallFullBranch lam mu h hlast)).toLinearMap := by
  change
    LinearMap.range
      (TensorProduct.map (gtTransverseEuclideanIsometry n).toLinearMap
        (gtWallCanonicalFullBranchFibre lam mu h hn hlast).toLinearMap) =
      LinearMap.range
        (TensorProduct.map (gtTransverseEuclideanIsometry n).toLinearMap
          (canonicalFullBranchFibre lam hn
            (gtWallFullBranch lam mu h hlast)).toLinearMap)
  rw [TensorProduct.range_map, TensorProduct.range_map,
    gtWallCanonicalFullBranchFibre_range_eq_fullBranch
      lam mu h hn hlast]

theorem normalizedGTTransverseWallSector_range_le_fullTransverse
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hlast : 0 < lam (Fin.last (r + 1))) :
    LinearMap.range
        (normalizedGTTransverseWallSector
          lam mu h hn hlast).toLinearMap ≤
      LinearMap.range
        (gtFullTransverseEmbedding lam hn
          (gtWallFullBranch lam mu h hlast)).toLinearMap := by
  rw [← gtTransverseWallTensorEmbedding_range_eq_fullTransverse
    lam mu h hn hlast]
  rintro _ ⟨p, rfl⟩
  change normalizedGTTransverseWallSector lam mu h hn hlast p ∈ _
  rw [normalizedGTTransverseWallSector_apply]
  change
    (Real.sqrt
      (MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallSectorGram.gtWallSectorGram n mu))⁻¹ •
      (gtTransverseWallTensorEmbedding lam mu h hn hlast)
        ((youngClebschRaise
          (raiseWeight
            (appendZeroWeight mu)
            (Fin.last (r + 1)))
          (appendZeroWeight mu)
          (sum_raiseWeight
            (appendZeroWeight mu)
            (Fin.last (r + 1)))
          (Fin.last (r + 1)))
            ((appendZeroRowIsometryEquiv mu) p)) ∈ _
  exact Submodule.smul_mem _ _ ⟨_, rfl⟩

end AllRankGTWallFullTransverseFactorization

end

section


open scoped BigOperators InnerProductSpace TensorProduct

namespace AllRankGTTransversePhysicalDiagonalColumn

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTFullTransverseSameSignatureRow
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseFullBranchDecomposition
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallFullTransverseFactorization
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallSectorGram
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallSectorIsometry
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallTransverseCompression
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherRepresentationGraph (Interlaces)
open MetricCodes.Spherical.ThreeRowYoungBranching

theorem normalizedWallSector_shortTensor_adjoint_eigen
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hlast : 0 < lam (Fin.last (r + 1)))
    (p : HarmonicYoungSpace (n := n) mu) :
    let I := gtTransverseWallTensorEmbedding lam mu h hn hlast
    let B := normalizedGTTransverseWallSector lam mu h hn hlast
    let d := -(wallShift (n + 1) (r + 1))
    I.toLinearMap.adjoint
      (gtRelativeCasimir (n := n + 1) lam (B p)) =
        d • I.toLinearMap.adjoint (B p) := by
  dsimp
  let c : ℝ := (Real.sqrt (gtWallSectorGram n mu))⁻¹
  let C :=
    (youngClebschRaise (n := n)
      (raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
      (appendZeroWeight mu)
      (sum_raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
      (Fin.last (r + 1))).comp
        (appendZeroRowIsometryEquiv (n := n) mu).toLinearMap
  have hphase :
      normalizedGTTransverseWallSector lam mu h hn hlast p =
        c • gtTransverseWallSector lam mu h hn hlast p := by
    change (normalizedGTTransverseWallSector lam mu h hn hlast).toLinearMap p = _
    rw [normalizedGTTransverseWallSector_toLinearMap]
    rfl
  have hself :
      (gtTransverseWallTensorEmbedding lam mu h hn hlast).toLinearMap.adjoint
        (gtTransverseWallSector lam mu h hn hlast p) = C p := by
    exact LinearMap.congr_fun
      (gtTransverseWallTensorEmbedding lam mu h hn hlast).adjoint_comp_self'
      (C p)
  rw [map_smul, map_smul, map_smul,
    gtTransverseWallSector_relativeCasimir_compression,
    hself]
  exact smul_comm _ _ _

theorem normalizedWallSector_selectedFullTensor_adjoint_eigen
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hlast : 0 < lam (Fin.last (r + 1)))
    (p : HarmonicYoungSpace (n := n) mu) :
    let J := gtFullTransverseEmbedding lam hn
      (gtWallFullBranch lam mu h hlast)
    let B := normalizedGTTransverseWallSector lam mu h hn hlast
    let d := -(wallShift (n + 1) (r + 1))
    J.toLinearMap.adjoint
      (gtRelativeCasimir (n := n + 1) lam (B p)) =
        d • J.toLinearMap.adjoint (B p) := by
  dsimp
  apply adjoint_eigen_of_range_le
    (gtTransverseWallTensorEmbedding lam mu h hn hlast).toLinearMap
    (gtFullTransverseEmbedding lam hn
      (gtWallFullBranch lam mu h hlast)).toLinearMap
    (le_of_eq
      (gtTransverseWallTensorEmbedding_range_eq_fullTransverse
        lam mu h hn hlast).symm)
    (gtRelativeCasimir (n := n + 1) lam)
    (normalizedGTTransverseWallSector lam mu h hn hlast p)
    (-(wallShift (n + 1) (r + 1)))
  exact normalizedWallSector_shortTensor_adjoint_eigen
    lam mu h hn hlast p

end AllRankGTTransversePhysicalDiagonalColumn

end

section


open scoped BigOperators InnerProductSpace TensorProduct

namespace AllRankGTTransverseWrongBranchCompression

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirPureAxis
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCasimirEmbedding
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseFullBranchDecomposition
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseTangentialCompression
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseTensorRelativeCompression
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseWignerEckartPhase
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallTransverseCompression
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInternalRowLowerGram
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension
open MetricCodes.Spherical.HigherHarmonicYoung.ClebschRotation
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGTFullCrossOrthogonality
open MetricCodes.Spherical.ThreeRowYoungBranching

theorem transverseStabilizerIsometry_adjoint_comp_of_orthogonal
    {s t r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (source : Fin (s + 1) → ℕ) (target : Fin (t + 1) → ℕ)
    (F : HarmonicYoungSpace (n := n) source →ₗᵢ[ℝ]
      HarmonicYoungSpace (n := n + 1) lam)
    (G : HarmonicYoungSpace (n := n) target →ₗᵢ[ℝ]
      HarmonicYoungSpace (n := n + 1) lam)
    (horth : F.toLinearMap.adjoint.comp G.toLinearMap = 0) :
    (transverseTensorEmbeddingOfStabilizerIsometry
      lam source F).toLinearMap.adjoint.comp
        (transverseTensorEmbeddingOfStabilizerIsometry
          lam target G).toLinearMap = 0 := by
  change
    (TensorProduct.map (gtTransverseEuclideanIsometry n).toLinearMap
      F.toLinearMap).adjoint.comp
      (TensorProduct.map (gtTransverseEuclideanIsometry n).toLinearMap
        G.toLinearMap) = 0
  rw [TensorProduct.adjoint_map]
  apply TensorProduct.ext
  ext v p
  have hz := LinearMap.congr_fun horth p
  change F.toLinearMap.adjoint (G p) = 0 at hz
  change
    (gtTransverseEuclideanIsometry n).toLinearMap.adjoint
        (gtTransverseEuclideanIsometry n v) ⊗ₜ[ℝ]
      F.toLinearMap.adjoint (G p) = 0
  rw [hz, TensorProduct.tmul_zero]

theorem transverseStabilizerIsometry_rotationTerm_cross
    {s t r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (source : Fin (s + 1) → ℕ) (target : Fin (t + 1) → ℕ)
    (F : HarmonicYoungSpace (n := n) source →ₗᵢ[ℝ]
      HarmonicYoungSpace (n := n + 1) lam)
    (G : HarmonicYoungSpace (n := n) target →ₗᵢ[ℝ]
      HarmonicYoungSpace (n := n + 1) lam)
    (a b : Fin (n + 1)) :
    (transverseTensorEmbeddingOfStabilizerIsometry
      lam source F).toLinearMap.adjoint.comp
        ((TensorProduct.map (euclideanAmbientRotation a b)
          (youngAmbientRotation lam a b)).comp
          (transverseTensorEmbeddingOfStabilizerIsometry
            lam target G).toLinearMap) =
      TensorProduct.map
        ((gtTransverseEuclideanIsometry n).toLinearMap.adjoint.comp
          ((euclideanAmbientRotation a b).comp
            (gtTransverseEuclideanIsometry n).toLinearMap))
        (F.toLinearMap.adjoint.comp
          ((youngAmbientRotation lam a b).comp G.toLinearMap)) := by
  change
    (TensorProduct.map (gtTransverseEuclideanIsometry n).toLinearMap
      F.toLinearMap).adjoint.comp
      ((TensorProduct.map (euclideanAmbientRotation a b)
        (youngAmbientRotation lam a b)).comp
        (TensorProduct.map (gtTransverseEuclideanIsometry n).toLinearMap
          G.toLinearMap)) = _
  rw [TensorProduct.adjoint_map]
  apply TensorProduct.ext
  ext v p
  rfl

theorem transverseStabilizerIsometry_mixedRotation_cross_eq_zero
    {s t r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (source : Fin (s + 1) → ℕ) (target : Fin (t + 1) → ℕ)
    (F : HarmonicYoungSpace (n := n) source →ₗᵢ[ℝ]
      HarmonicYoungSpace (n := n + 1) lam)
    (G : HarmonicYoungSpace (n := n) target →ₗᵢ[ℝ]
      HarmonicYoungSpace (n := n + 1) lam)
    (horth : F.toLinearMap.adjoint.comp G.toLinearMap = 0)
    (hG : ∀ a b : Fin n,
      G.toLinearMap.comp (youngAmbientRotation target a b) =
        (youngAmbientRotation lam a.castSucc b.castSucc).comp G.toLinearMap) :
    (transverseTensorEmbeddingOfStabilizerIsometry
      lam source F).toLinearMap.adjoint.comp
        ((gtMixedRotationOperator (n := n + 1) lam).comp
          (transverseTensorEmbeddingOfStabilizerIsometry
            lam target G).toLinearMap) = 0 := by
  let I := (transverseTensorEmbeddingOfStabilizerIsometry
    lam source F).toLinearMap
  let J := (transverseTensorEmbeddingOfStabilizerIsometry
    lam target G).toLinearMap
  have htangential (a b : Fin n) :
      I.adjoint.comp
        ((TensorProduct.map
          (euclideanAmbientRotation a.castSucc b.castSucc)
          (youngAmbientRotation lam a.castSucc b.castSucc)).comp J) = 0 := by
    change
      (transverseTensorEmbeddingOfStabilizerIsometry
        lam source F).toLinearMap.adjoint.comp
        ((TensorProduct.map
          (euclideanAmbientRotation a.castSucc b.castSucc)
          (youngAmbientRotation lam a.castSucc b.castSucc)).comp
          (transverseTensorEmbeddingOfStabilizerIsometry
            lam target G).toLinearMap) = 0
    rw [transverseStabilizerIsometry_rotationTerm_cross]
    have hz : F.toLinearMap.adjoint.comp
        ((youngAmbientRotation lam a.castSucc b.castSucc).comp G.toLinearMap) = 0 := by
      rw [← hG a b, ← LinearMap.comp_assoc, horth, LinearMap.zero_comp]
    rw [hz]
    apply TensorProduct.ext
    ext v p
    simp only [TensorProduct.map_zero_right, LinearMap.compr₂ₛₗ_apply, TensorProduct.mk_apply,
      LinearMap.zero_apply]
  have hcross (a : Fin n) :
      I.adjoint.comp
        ((TensorProduct.map
          (euclideanAmbientRotation a.castSucc (Fin.last n))
          (youngAmbientRotation lam a.castSucc (Fin.last n))).comp J) = 0 := by
    change
      (transverseTensorEmbeddingOfStabilizerIsometry
        lam source F).toLinearMap.adjoint.comp
        ((TensorProduct.map
          (euclideanAmbientRotation a.castSucc (Fin.last n))
          (youngAmbientRotation lam a.castSucc (Fin.last n))).comp
          (transverseTensorEmbeddingOfStabilizerIsometry
            lam target G).toLinearMap) = 0
    rw [transverseStabilizerIsometry_rotationTerm_cross,
      gtTransverseEuclideanIsometry_cross_rotation_compression]
    apply TensorProduct.ext
    ext v p
    simp only [TensorProduct.map_zero_left, LinearMap.compr₂ₛₗ_apply, TensorProduct.mk_apply,
      LinearMap.zero_apply]
  have hcrossSwap (a : Fin n) :
      I.adjoint.comp
        ((TensorProduct.map
          (euclideanAmbientRotation (Fin.last n) a.castSucc)
          (youngAmbientRotation lam (Fin.last n) a.castSucc)).comp J) = 0 := by
    change
      (transverseTensorEmbeddingOfStabilizerIsometry
        lam source F).toLinearMap.adjoint.comp
        ((TensorProduct.map
          (euclideanAmbientRotation (Fin.last n) a.castSucc)
          (youngAmbientRotation lam (Fin.last n) a.castSucc)).comp
          (transverseTensorEmbeddingOfStabilizerIsometry
            lam target G).toLinearMap) = 0
    rw [transverseStabilizerIsometry_rotationTerm_cross,
      gtTransverseEuclideanIsometry_cross_rotation_compression_swap]
    apply TensorProduct.ext
    ext v p
    simp only [TensorProduct.map_zero_left, LinearMap.compr₂ₛₗ_apply, TensorProduct.mk_apply,
      LinearMap.zero_apply]
  have hlast :
      I.adjoint.comp
        ((TensorProduct.map
          (euclideanAmbientRotation (Fin.last n) (Fin.last n))
          (youngAmbientRotation lam (Fin.last n) (Fin.last n))).comp J) = 0 := by
    have hzero : euclideanAmbientRotation (Fin.last n) (Fin.last n) = 0 := by
      apply LinearMap.ext
      intro v
      simp only [euclideanAmbientRotation_apply, EuclideanSpace.basisFun_apply, sub_self,
        LinearMap.zero_apply]
    change
      (transverseTensorEmbeddingOfStabilizerIsometry
        lam source F).toLinearMap.adjoint.comp
        ((TensorProduct.map
          (euclideanAmbientRotation (Fin.last n) (Fin.last n))
          (youngAmbientRotation lam (Fin.last n) (Fin.last n))).comp
          (transverseTensorEmbeddingOfStabilizerIsometry
            lam target G).toLinearMap) = 0
    rw [transverseStabilizerIsometry_rotationTerm_cross, hzero]
    simp only [LinearMap.zero_comp, LinearMap.comp_zero, TensorProduct.map_zero_left]
  unfold gtMixedRotationOperator
  change I.adjoint.comp ((∑ a : Fin (n + 1), ∑ b : Fin (n + 1),
    TensorProduct.map (euclideanAmbientRotation a b)
      (youngAmbientRotation lam a b)).comp J) = 0
  apply TensorProduct.ext'
  intro v p
  simp only [LinearMap.comp_apply, LinearMap.sum_apply, map_sum,
    LinearMap.zero_apply]
  rw [Fin.sum_univ_castSucc]
  simp_rw [Fin.sum_univ_castSucc]
  have htangential' (a b : Fin n) :=
    LinearMap.congr_fun (htangential a b) (v ⊗ₜ[ℝ] p)
  have hcross' (a : Fin n) :=
    LinearMap.congr_fun (hcross a) (v ⊗ₜ[ℝ] p)
  have hcrossSwap' (a : Fin n) :=
    LinearMap.congr_fun (hcrossSwap a) (v ⊗ₜ[ℝ] p)
  have hlast' := LinearMap.congr_fun hlast (v ⊗ₜ[ℝ] p)
  simp only [LinearMap.comp_apply, LinearMap.zero_apply]
    at htangential' hcross' hcrossSwap' hlast'
  simp only [htangential', hcross', hcrossSwap', hlast',
    Finset.sum_const_zero, add_zero]

theorem transverseStabilizerIsometry_relativeCasimir_cross_eq_zero
    {s t r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (source : Fin (s + 1) → ℕ) (target : Fin (t + 1) → ℕ)
    (F : HarmonicYoungSpace (n := n) source →ₗᵢ[ℝ]
      HarmonicYoungSpace (n := n + 1) lam)
    (G : HarmonicYoungSpace (n := n) target →ₗᵢ[ℝ]
      HarmonicYoungSpace (n := n + 1) lam)
    (horth : F.toLinearMap.adjoint.comp G.toLinearMap = 0)
    (hG : ∀ a b : Fin n,
      G.toLinearMap.comp (youngAmbientRotation target a b) =
        (youngAmbientRotation lam a.castSucc b.castSucc).comp G.toLinearMap) :
    (transverseTensorEmbeddingOfStabilizerIsometry
      lam source F).toLinearMap.adjoint.comp
        ((gtRelativeCasimir (n := n + 1) lam).comp
          (transverseTensorEmbeddingOfStabilizerIsometry
            lam target G).toLinearMap) = 0 := by
  rw [gtRelativeCasimir_eq_scalar_sub_mixed]
  simp only [LinearMap.sub_comp, LinearMap.smul_comp,
    LinearMap.id_comp, LinearMap.comp_sub, LinearMap.comp_smul]
  rw [transverseStabilizerIsometry_adjoint_comp_of_orthogonal
    lam source target F G horth,
    transverseStabilizerIsometry_mixedRotation_cross_eq_zero
      lam source target F G horth hG]
  simp only [Nat.cast_add, Nat.cast_one, smul_zero, sub_self]

theorem canonicalFullBranchFibre_adjoint_comp_of_ne
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (hn : 2 * r + 5 ≤ n + 1)
    (branch selected : FullBranchWeight lam)
    (hne : branch ≠ selected) :
    (canonicalFullBranchFibre lam hn branch).toLinearMap.adjoint.comp
      (canonicalFullBranchFibre lam hn selected).toLinearMap = 0 := by
  apply LinearMap.ext
  intro p
  apply ext_inner_left ℝ
  intro q
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, inner_zero_right]
  rw [LinearMap.adjoint_inner_right]
  exact canonicalFullBranchFibre_orthogonal lam hn branch selected hne q p

theorem canonicalFullBranchFibre_adjoint_canonicalGelfandTsetlinFibre_eq_zero
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (branch : FullBranchWeight lam)
    (hwrong : branch ≠ fullBranchOfInterlaces mu h) :
    (canonicalFullBranchFibre lam hn branch).toLinearMap.adjoint.comp
      (canonicalGelfandTsetlinFibre lam mu h hgram).toLinearMap = 0 := by
  apply LinearMap.ext
  intro p
  apply ext_inner_left ℝ
  intro q
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, inner_zero_right]
  rw [LinearMap.adjoint_inner_right]
  exact (real_inner_comm
    (canonicalGelfandTsetlinFibre lam mu h hgram p)
    (canonicalFullBranchFibre lam hn branch q)).trans
      (canonicalGelfandTsetlinFibre_fullBranch_orthogonal_of_ne_selected
        lam mu h hn hgram branch hwrong p q)

theorem gtFullTransverseEmbedding_relativeCasimir_cross_physical_eq_zero
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (branch : FullBranchWeight lam)
    (hwrong : branch ≠ fullBranchOfInterlaces mu h) :
    (gtFullTransverseEmbedding lam hn branch).toLinearMap.adjoint.comp
      ((gtRelativeCasimir (n := n + 1) lam).comp
        (gtTransverseTensorEmbedding lam mu h hgram).toLinearMap) = 0 := by
  exact transverseStabilizerIsometry_relativeCasimir_cross_eq_zero
    (s := r + 1) (t := r) (r := r + 1) (n := n)
    lam (fullBranchSignature branch) mu
    (canonicalFullBranchFibre lam hn branch)
    (canonicalGelfandTsetlinFibre lam mu h hgram)
    (canonicalFullBranchFibre_adjoint_canonicalGelfandTsetlinFibre_eq_zero
      lam mu h hn hgram branch hwrong)
    (canonicalGelfandTsetlinFibre_rotation_intertwine lam mu h hgram)

theorem gtFullTransverseEmbedding_negativeRelativeCasimir_eq_zero_of_wrong_branch
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (row : Fin (r + 1))
    (hnu : Interlaces lam (raiseWeight mu row))
    (hnuGram : PositiveGelfandTsetlinFischerGram
      (n := n) lam (raiseWeight mu row) hnu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (branch : FullBranchWeight lam)
    (hwrong : branch ≠ fullBranchOfInterlaces (raiseWeight mu row) hnu)
    (p : HarmonicYoungSpace (n := n) mu) :
    (gtFullTransverseEmbedding lam hn branch).toLinearMap.adjoint
      (gtRelativeCasimir (n := n + 1) lam
        (gtTransverseNegativeSector lam mu row hnu hnuGram p)) = 0 := by
  have hz := LinearMap.congr_fun
    (gtFullTransverseEmbedding_relativeCasimir_cross_physical_eq_zero
      lam (raiseWeight mu row) hnu hn hnuGram branch hwrong)
    (youngClebschRaise (raiseWeight mu row) mu
      (sum_raiseWeight mu row) row p)
  exact hz

theorem gtFullTransverseEmbedding_positiveRelativeCasimir_eq_zero_of_wrong_branch
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu nu : Fin (r + 1) → ℕ) (row : Fin (r + 1))
    (hmunu : mu = raiseWeight nu row)
    (hnu : Interlaces lam nu)
    (hnuGram : PositiveGelfandTsetlinFischerGram
      (n := n) lam nu hnu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (branch : FullBranchWeight lam)
    (hwrong : branch ≠ fullBranchOfInterlaces nu hnu)
    (p : HarmonicYoungSpace (n := n) mu) :
    (gtFullTransverseEmbedding lam hn branch).toLinearMap.adjoint
      (gtRelativeCasimir (n := n + 1) lam
        (gtTransversePositiveSector lam mu nu row hmunu hnu hnuGram p)) = 0 := by
  have hz := LinearMap.congr_fun
    (gtFullTransverseEmbedding_relativeCasimir_cross_physical_eq_zero
      lam nu hnu hn hnuGram branch hwrong)
    (youngClebschLower nu mu
      (by rw [hmunu]; exact sum_raiseWeight nu row) row p)
  exact hz

theorem gtFullTransverseEmbedding_normalizedNegativeRelativeCasimir_eq_zero_of_wrong_branch
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (kappa : Fin r → ℕ)
    (row : Fin (r + 1))
    (hnu : Interlaces lam (raiseWeight mu row))
    (hnuGram : PositiveGelfandTsetlinFischerGram
      (n := n) lam (raiseWeight mu row) hnu)
    (hfinite : FiniteInterlacing n mu kappa)
    (hraise : FiniteInterlacing n (raiseWeight mu row) kappa)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (branch : FullBranchWeight lam)
    (hwrong : branch ≠ fullBranchOfInterlaces (raiseWeight mu row) hnu)
    (p : HarmonicYoungSpace (n := n) mu) :
    (gtFullTransverseEmbedding lam hn branch).toLinearMap.adjoint
      (gtRelativeCasimir (n := n + 1) lam
        (normalizedGTTransverseNegativeSector lam mu kappa row
          hnu hnuGram hfinite hraise p)) = 0 := by
  change
    (gtFullTransverseEmbedding lam hn branch).toLinearMap.adjoint
      (gtRelativeCasimir (n := n + 1) lam
        ((normalizedGTTransverseNegativeSector lam mu kappa row
          hnu hnuGram hfinite hraise).toLinearMap p)) = 0
  rw [normalizedGTTransverseNegativeSector_toLinearMap,
    LinearMap.smul_apply, map_smul, map_smul,
    gtFullTransverseEmbedding_negativeRelativeCasimir_eq_zero_of_wrong_branch
      lam mu row hnu hnuGram hn branch hwrong p, smul_zero]

theorem gtFullTransverseEmbedding_normalizedPositiveRelativeCasimir_eq_zero_of_wrong_branch
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu nu : Fin (r + 1) → ℕ) (row : Fin (r + 1))
    (hmunu : mu = raiseWeight nu row)
    (hmu : Interlaces lam mu)
    (hnu : Interlaces lam nu)
    (hnuGram : PositiveGelfandTsetlinFischerGram
      (n := n) lam nu hnu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (branch : FullBranchWeight lam)
    (hwrong : branch ≠ fullBranchOfInterlaces nu hnu)
    (p : HarmonicYoungSpace (n := n) mu) :
    (gtFullTransverseEmbedding lam hn branch).toLinearMap.adjoint
      (gtRelativeCasimir (n := n + 1) lam
        (normalizedGTTransversePositiveSector lam mu nu row
          hmunu hmu hnu hnuGram p)) = 0 := by
  change
    (gtFullTransverseEmbedding lam hn branch).toLinearMap.adjoint
      (gtRelativeCasimir (n := n + 1) lam
        ((normalizedGTTransversePositiveSector lam mu nu row
          hmunu hmu hnu hnuGram).toLinearMap p)) = 0
  rw [normalizedGTTransversePositiveSector_toLinearMap,
    LinearMap.smul_apply, map_smul, map_smul,
    gtFullTransverseEmbedding_positiveRelativeCasimir_eq_zero_of_wrong_branch
      lam mu nu row hmunu hnu hnuGram hn branch hwrong p, smul_zero]

end AllRankGTTransverseWrongBranchCompression

end

section


open scoped BigOperators InnerProductSpace TensorProduct

namespace AllRankGTWallTransverseCrossOrthogonality

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseFullBranchDecomposition
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseWrongBranchCompression
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallSectorIsometry
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallTransverseCompression
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension
open MetricCodes.Spherical.HigherHarmonicYoung.ClebschRotation
open MetricCodes.Spherical.HigherRepresentationGraph (Interlaces)
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness
open MetricCodes.Spherical.ThreeRowYoungBranching

private theorem canonicalFullBranchFibre_adjoint_transport_of_ne_metriccodes2_f07c51ce
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (branch selected : FullBranchWeight lam)
    (signature : Fin (r + 2) → ℕ)
    (hsignature : fullBranchSignature selected = signature)
    (hwrong : branch ≠ selected) :
    (canonicalFullBranchFibre lam hn branch).toLinearMap.adjoint.comp
      (hsignature ▸ (canonicalFullBranchFibre lam hn selected)).toLinearMap = 0 := by
  subst signature
  exact canonicalFullBranchFibre_adjoint_comp_of_ne
    lam hn branch selected hwrong

theorem canonicalFullBranchFibre_adjoint_wallCanonicalFullBranchFibre_eq_zero
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hlast : 0 < lam (Fin.last (r + 1)))
    (branch : FullBranchWeight lam)
    (hwrong : branch ≠ gtWallFullBranch lam mu h hlast) :
    (canonicalFullBranchFibre lam hn branch).toLinearMap.adjoint.comp
      (gtWallCanonicalFullBranchFibre lam mu h hn hlast).toLinearMap = 0 := by
  exact canonicalFullBranchFibre_adjoint_transport_of_ne_metriccodes2_f07c51ce
    lam hn branch (gtWallFullBranch lam mu h hlast)
    (raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
    (gtWallFullBranch_signature lam mu h hlast) hwrong

theorem gtFullTransverseEmbedding_adjoint_wallTensorEmbedding_eq_zero
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hlast : 0 < lam (Fin.last (r + 1)))
    (branch : FullBranchWeight lam)
    (hwrong : branch ≠ gtWallFullBranch lam mu h hlast) :
    (gtFullTransverseEmbedding lam hn branch).toLinearMap.adjoint.comp
      (gtTransverseWallTensorEmbedding lam mu h hn hlast).toLinearMap = 0 := by
  exact transverseStabilizerIsometry_adjoint_comp_of_orthogonal
    (s := r + 1) (t := r + 1) (r := r + 1) (n := n)
    lam (fullBranchSignature branch)
    (raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
    (canonicalFullBranchFibre lam hn branch)
    (gtWallCanonicalFullBranchFibre lam mu h hn hlast)
    (canonicalFullBranchFibre_adjoint_wallCanonicalFullBranchFibre_eq_zero
      lam mu h hn hlast branch hwrong)

theorem gtFullTransverseEmbedding_relativeCasimir_cross_wallTensorEmbedding_eq_zero
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hlast : 0 < lam (Fin.last (r + 1)))
    (branch : FullBranchWeight lam)
    (hwrong : branch ≠ gtWallFullBranch lam mu h hlast) :
    (gtFullTransverseEmbedding lam hn branch).toLinearMap.adjoint.comp
      ((gtRelativeCasimir (n := n + 1) lam).comp
        (gtTransverseWallTensorEmbedding lam mu h hn hlast).toLinearMap) = 0 := by
  exact transverseStabilizerIsometry_relativeCasimir_cross_eq_zero
    (s := r + 1) (t := r + 1) (r := r + 1) (n := n)
    lam (fullBranchSignature branch)
    (raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
    (canonicalFullBranchFibre lam hn branch)
    (gtWallCanonicalFullBranchFibre lam mu h hn hlast)
    (canonicalFullBranchFibre_adjoint_wallCanonicalFullBranchFibre_eq_zero
      lam mu h hn hlast branch hwrong)
    (gtWallCanonicalFullBranchFibre_rotation_intertwine
      lam mu h hn hlast)

theorem gtFullTransverseEmbedding_adjoint_wallSector_eq_zero
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hlast : 0 < lam (Fin.last (r + 1)))
    (branch : FullBranchWeight lam)
    (hwrong : branch ≠ gtWallFullBranch lam mu h hlast) :
    (gtFullTransverseEmbedding lam hn branch).toLinearMap.adjoint.comp
      (gtTransverseWallSector lam mu h hn hlast) = 0 := by
  unfold gtTransverseWallSector
  rw [← LinearMap.comp_assoc,
    gtFullTransverseEmbedding_adjoint_wallTensorEmbedding_eq_zero
      lam mu h hn hlast branch hwrong, LinearMap.zero_comp]

theorem gtFullTransverseEmbedding_relativeCasimir_cross_wallSector_eq_zero
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hlast : 0 < lam (Fin.last (r + 1)))
    (branch : FullBranchWeight lam)
    (hwrong : branch ≠ gtWallFullBranch lam mu h hlast) :
    (gtFullTransverseEmbedding lam hn branch).toLinearMap.adjoint.comp
      ((gtRelativeCasimir (n := n + 1) lam).comp
        (gtTransverseWallSector lam mu h hn hlast)) = 0 := by
  unfold gtTransverseWallSector
  calc
    _ = ((gtFullTransverseEmbedding lam hn branch).toLinearMap.adjoint.comp
      ((gtRelativeCasimir (n := n + 1) lam).comp
        (gtTransverseWallTensorEmbedding lam mu h hn hlast).toLinearMap)).comp
        ((youngClebschRaise
          (raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
          (appendZeroWeight mu)
          (sum_raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
          (Fin.last (r + 1))).comp
            (appendZeroRowIsometryEquiv mu).toLinearMap) := by
              ext p
              rfl
    _ = 0 := by
      rw [gtFullTransverseEmbedding_relativeCasimir_cross_wallTensorEmbedding_eq_zero
        lam mu h hn hlast branch hwrong, LinearMap.zero_comp]

theorem gtFullTransverseEmbedding_adjoint_normalizedWallSector_eq_zero
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hlast : 0 < lam (Fin.last (r + 1)))
    (branch : FullBranchWeight lam)
    (hwrong : branch ≠ gtWallFullBranch lam mu h hlast) :
    (gtFullTransverseEmbedding lam hn branch).toLinearMap.adjoint.comp
      (normalizedGTTransverseWallSector lam mu h hn hlast).toLinearMap = 0 := by
  rw [normalizedGTTransverseWallSector_toLinearMap, LinearMap.comp_smul,
    gtFullTransverseEmbedding_adjoint_wallSector_eq_zero
      lam mu h hn hlast branch hwrong, smul_zero]

theorem gtFullTransverseEmbedding_relativeCasimir_cross_normalizedWallSector_eq_zero
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hlast : 0 < lam (Fin.last (r + 1)))
    (branch : FullBranchWeight lam)
    (hwrong : branch ≠ gtWallFullBranch lam mu h hlast) :
    (gtFullTransverseEmbedding lam hn branch).toLinearMap.adjoint.comp
      ((gtRelativeCasimir (n := n + 1) lam).comp
        (normalizedGTTransverseWallSector lam mu h hn hlast).toLinearMap) = 0 := by
  rw [normalizedGTTransverseWallSector_toLinearMap, LinearMap.comp_smul,
    LinearMap.comp_smul,
    gtFullTransverseEmbedding_relativeCasimir_cross_wallSector_eq_zero
      lam mu h hn hlast branch hwrong, smul_zero]

end AllRankGTWallTransverseCrossOrthogonality

end

section


open scoped BigOperators InnerProductSpace TensorProduct

namespace AllRankGTPhysicalWallAdditiveColumn

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTActualAxisTransverseDecomposition
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTNormalizedWallCharacteristicAnnihilation
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTPhysicalRetainedAdditiveColumn
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirCrossBlock
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTSelectedMuAxisProjectionVanishing
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseFullBranchDecomposition
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransversePhysicalDiagonalColumn
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTValidTransverseArrowheadRow
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallFullTransverseFactorization
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallSectorIsometry
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallTransverseCompression
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallTransverseCrossOrthogonality
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness
open MetricCodes.Spherical.ThreeRowYoungBranching

private theorem adjoint_eq_adjoint_isometric_range_projection_metriccodes2_c0c59de2
    {E F G : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
    (A : E →ₗᵢ[ℝ] F) (C : G →ₗ[ℝ] F)
    (hCA : LinearMap.range C ≤ LinearMap.range A.toLinearMap)
    (x : F) :
    C.adjoint x = C.adjoint (A (A.toLinearMap.adjoint x)) := by
  apply ext_inner_left ℝ
  intro p
  obtain ⟨q, hq⟩ := hCA ⟨p, rfl⟩
  change A q = C p at hq
  calc
    ⟪p, C.adjoint x⟫_ℝ = ⟪C p, x⟫_ℝ :=
      LinearMap.adjoint_inner_right C p x
    _ = ⟪A q, x⟫_ℝ := by rw [hq]
    _ = ⟪q, A.toLinearMap.adjoint x⟫_ℝ :=
      (LinearMap.adjoint_inner_right A.toLinearMap q x).symm
    _ = ⟪A q, A (A.toLinearMap.adjoint x)⟫_ℝ :=
      (A.inner_map_map q (A.toLinearMap.adjoint x)).symm
    _ = ⟪C p, A (A.toLinearMap.adjoint x)⟫_ℝ := by rw [hq]
    _ = ⟪p, C.adjoint (A (A.toLinearMap.adjoint x))⟫_ℝ :=
      (LinearMap.adjoint_inner_right C p _).symm

theorem gtRelativeCasimir_normalizedWallSector_additiveColumn
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ)
    (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (hn : 2 * (r + 2) + 5 ≤ n + 1)
    (hlast : 0 < lam (Fin.last (r + 1))) :
    let hw : 2 * (r + 1) + 5 ≤ n + 1 := by omega
    let B := normalizedGTTransverseWallSector lam mu h hw hlast
    (gtRelativeCasimir (n := n + 1) lam).comp B.toLinearMap =
      (-(wallShift (n + 1) (r + 1))) • B.toLinearMap +
        (canonicalGelfandTsetlinAxisTensor lam mu h hgram).comp
          (gtTransverseAxisCrossBlock lam mu h hgram B.toLinearMap) := by
  dsimp
  let hw : 2 * (r + 1) + 5 ≤ n + 1 := by omega
  let B := normalizedGTTransverseWallSector lam mu h hw hlast
  let A := canonicalGelfandTsetlinAxisTensor lam mu h hgram
  let K := gtTransverseAxisCrossBlock lam mu h hgram B.toLinearMap
  let selected := fullBranchOfInterlaces mu h
  let wall := gtWallFullBranch lam mu h hlast
  change
    (gtRelativeCasimir (n := n + 1) lam).comp B.toLinearMap =
      (-(wallShift (n + 1) (r + 1))) • B.toLinearMap + A.comp K
  apply gtRelativeCasimir_comp_eq_smul_add_of_orthogonal_full_block_rows
    lam hw h.antitone_ambient B.toLinearMap A K
      (-(wallShift (n + 1) (r + 1)))
  · intro branch
    apply LinearMap.ext
    intro p
    apply ext_inner_left ℝ
    intro q
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, inner_zero_right]
    rw [LinearMap.adjoint_inner_right]
    obtain ⟨z, hz⟩ :=
      normalizedGTTransverseWallSector_range_le_fullTransverse
        lam mu h hw hlast (show B p ∈ LinearMap.range B.toLinearMap from ⟨p, rfl⟩)
    change gtFullTransverseEmbedding lam hw wall z = B p at hz
    change ⟪gtFullAxisEmbedding lam hw branch q, B p⟫_ℝ = 0
    rw [← hz]
    exact gtFullAxisEmbedding_inner_transverse_eq_zero
      lam hw branch wall q z
  · intro branch
    apply LinearMap.ext
    intro p
    apply ext_inner_left ℝ
    intro q
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, inner_zero_right]
    rw [LinearMap.adjoint_inner_right]
    have hp : A p ∈ LinearMap.range
        (gtFullAxisEmbedding lam hw selected).toLinearMap := by
      rw [gtFullAxisEmbedding_selected_range_eq_canonicalAxis
        lam mu h hw hgram]
      exact ⟨p, rfl⟩
    obtain ⟨z, hz⟩ := hp
    change gtFullAxisEmbedding lam hw selected z = A p at hz
    rw [← hz, real_inner_comm]
    exact gtFullAxisEmbedding_inner_transverse_eq_zero
      lam hw selected branch z q
  · intro branch
    by_cases hbranch : branch = selected
    · subst branch
      apply LinearMap.ext
      intro p
      change
        (gtFullAxisEmbedding lam hw selected).toLinearMap.adjoint
            (gtRelativeCasimir (n := n + 1) lam (B p)) =
          (gtFullAxisEmbedding lam hw selected).toLinearMap.adjoint
            (A (K p))
      have hrange :
          LinearMap.range
            (gtFullAxisEmbedding lam hw selected).toLinearMap ≤
              LinearMap.range
                (canonicalGelfandTsetlinAxisIsometry lam mu h hgram).toLinearMap := by
        rw [gtFullAxisEmbedding_selected_range_eq_canonicalAxis
          lam mu h hw hgram]
      have hproj := adjoint_eq_adjoint_isometric_range_projection_metriccodes2_c0c59de2
        (canonicalGelfandTsetlinAxisIsometry lam mu h hgram)
        (gtFullAxisEmbedding lam hw selected).toLinearMap hrange
        (gtRelativeCasimir (n := n + 1) lam (B p))
      change
        (gtFullAxisEmbedding lam hw selected).toLinearMap.adjoint
            (gtRelativeCasimir (n := n + 1) lam (B p)) =
          (gtFullAxisEmbedding lam hw selected).toLinearMap.adjoint
            (A (A.adjoint
              (gtRelativeCasimir (n := n + 1) lam (B p)))) at hproj
      exact hproj
    · have hsignature : fullBranchSignature branch ≠ appendZeroWeight mu := by
        intro heq
        apply hbranch
        apply fullBranchSignature_injective lam
        simpa [selected,
          fullBranchOfInterlaces_signature_eq_appendZeroWeight] using heq
      have hleft :
          (gtFullAxisEmbedding lam hw branch).toLinearMap.adjoint.comp
            ((gtRelativeCasimir (n := n + 1) lam).comp B.toLinearMap) = 0 := by
        apply LinearMap.ext
        intro p
        exact gtFullAxisEmbedding_adjoint_relativeCasimir_stabilizerSector_eq_zero
          lam mu h hn branch hsignature B.toLinearMap
          (normalizedGTTransverseWallSector_rotation_intertwine
            lam mu h hw hlast) p
      rw [hleft]
      apply Eq.symm
      apply LinearMap.ext
      intro p
      apply ext_inner_left ℝ
      intro q
      simp only [LinearMap.comp_apply, LinearMap.zero_apply, inner_zero_right]
      rw [LinearMap.adjoint_inner_right]
      have hp : A (K p) ∈ LinearMap.range
          (gtFullAxisEmbedding lam hw selected).toLinearMap := by
        rw [gtFullAxisEmbedding_selected_range_eq_canonicalAxis
          lam mu h hw hgram]
        exact ⟨K p, rfl⟩
      obtain ⟨z, hz⟩ := hp
      change gtFullAxisEmbedding lam hw selected z = A (K p) at hz
      rw [← hz]
      exact gtFullAxisEmbedding_orthogonal
        lam hw branch selected hbranch q z
  · intro branch
    by_cases hbranch : branch = wall
    · subst branch
      apply LinearMap.ext
      intro p
      exact normalizedWallSector_selectedFullTensor_adjoint_eigen
        lam mu h hw hlast p
    · rw [gtFullTransverseEmbedding_relativeCasimir_cross_normalizedWallSector_eq_zero
        lam mu h hw hlast branch hbranch,
        gtFullTransverseEmbedding_adjoint_normalizedWallSector_eq_zero
          lam mu h hw hlast branch hbranch,
        smul_zero]

end AllRankGTPhysicalWallAdditiveColumn

end

section


open scoped BigOperators

namespace AllRankGTTransverseEigenNodeSeparation

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherRepresentationGraph (Interlaces)
open MetricCodes.Spherical.HigherYoungAllRankGTArrowheadSchurComplement

theorem negativeStabilizerNode_ne_signedAmbientNode_of_valid_raise
    {r n : ℕ} (lam : Fin (r + 2) → ℕ) (mu : Fin (r + 1) → ℕ)
    (hfinite : FiniteInterlacing (n + 1) lam mu)
    (row : Fin (r + 1))
    (hraise : Interlaces lam (raiseWeight mu row))
    (channel : Fin (r + 2) × Bool) :
    gtStabilizerArrowheadNode
        (wallShift (n + 1) (r + 1))
        (stabilizerShift (n + 1) mu) (.inr (row, false)) ≠
      signedNode (ambientShift (n + 1) lam) channel := by
  have hweight : mu row < lam row.castSucc := by
    have hh := (hraise row).1
    simpa only [gt_iff_lt, raiseWeight, Function.update_self, Order.add_one_le_iff] using hh
  have hweightR : (mu row : ℝ) < (lam row.castSucc : ℝ) := by
    exact_mod_cast hweight
  have hupper :
      stabilizerShift (n + 1) mu row + 1 / 2 <
        ambientShift (n + 1) lam row.castSucc := by
    simp only [stabilizerShift, ambientShift, Fin.val_castSucc,
      Nat.cast_add, Nat.cast_one]
    linarith
  have hlower :
      ambientShift (n + 1) lam row.succ <
        stabilizerShift (n + 1) mu row + 1 / 2 := by
    linarith [hfinite.stabilizerShift_ge_succ row]
  rcases channel with ⟨j, sign⟩
  cases sign
  · simp only [gtStabilizerArrowheadNode_neg, one_div, signedNode, Bool.false_eq_true, ↓reduceIte,
      ne_eq]
    intro heq
    have hcoord :
        stabilizerShift (n + 1) mu row + 1 / 2 =
          ambientShift (n + 1) lam j := by linarith
    by_cases hji : j ≤ row.castSucc
    · have hmono := hfinite.ambientShift_strictAnti.antitone hji
      linarith
    · have hij : row.succ ≤ j := by
        have hlt : row.castSucc < j := lt_of_not_ge hji
        apply Fin.le_iff_val_le_val.mpr
        have hv : row.val < j.val := hlt
        exact Nat.succ_le_of_lt hv
      have hmono := hfinite.ambientShift_strictAnti.antitone hij
      linarith
  · simp only [gtStabilizerArrowheadNode_neg, one_div, signedNode, ↓reduceIte, ne_eq]
    have hM := hfinite.stabilizerShift_pos row
    have hL := hfinite.ambientShift_pos j
    linarith

theorem positiveStabilizerNode_ne_signedAmbientNode_of_valid_lower
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu nu : Fin (r + 1) → ℕ)
    (hfinite : FiniteInterlacing (n + 1) lam mu)
    (row : Fin (r + 1))
    (hlower : mu = raiseWeight nu row)
    (hnu : Interlaces lam nu)
    (channel : Fin (r + 2) × Bool) :
    gtStabilizerArrowheadNode
        (wallShift (n + 1) (r + 1))
        (stabilizerShift (n + 1) mu) (.inr (row, true)) ≠
      signedNode (ambientShift (n + 1) lam) channel := by
  have hweight : lam row.succ < mu row := by
    have hh := (hnu row).2
    rw [hlower]
    simpa only [raiseWeight, Function.update_self, Order.lt_add_one_iff, ge_iff_le,
      Nat.succ_eq_add_one] using
      Nat.lt_succ_of_le hh
  have hweightR : (lam row.succ : ℝ) < (mu row : ℝ) := by
    exact_mod_cast hweight
  have hlower' :
      ambientShift (n + 1) lam row.succ <
        stabilizerShift (n + 1) mu row - 1 / 2 := by
    simp only [stabilizerShift, ambientShift, Fin.val_succ,
      Nat.cast_add, Nat.cast_one]
    linarith
  have hupper :
      stabilizerShift (n + 1) mu row - 1 / 2 <
        ambientShift (n + 1) lam row.castSucc := by
    linarith [hfinite.ambientShift_castSucc_ge row]
  rcases channel with ⟨j, sign⟩
  cases sign
  · simp only [gtStabilizerArrowheadNode_pos, one_div, signedNode, Bool.false_eq_true, ↓reduceIte,
      ne_eq]
    have hL := hfinite.ambientShift_pos j
    have hlowpos := hfinite.ambientShift_pos row.succ
    linarith
  · simp only [gtStabilizerArrowheadNode_pos, one_div, signedNode, ↓reduceIte, ne_eq]
    intro heq
    by_cases hji : j ≤ row.castSucc
    · have hmono := hfinite.ambientShift_strictAnti.antitone hji
      linarith
    · have hij : row.succ ≤ j := by
        have hlt : row.castSucc < j := lt_of_not_ge hji
        apply Fin.le_iff_val_le_val.mpr
        have hv : row.val < j.val := hlt
        exact Nat.succ_le_of_lt hv
      have hmono := hfinite.ambientShift_strictAnti.antitone hij
      linarith

end AllRankGTTransverseEigenNodeSeparation

end

section


open scoped BigOperators InnerProductSpace TensorProduct

namespace AllRankGTFullySelectedTransverseBranchProjection

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCanonicalSelectedBranchRange
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCasimirEmbedding
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseFullBranchDecomposition
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension
open MetricCodes.Spherical.HigherRepresentationGraph (Interlaces)
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness
open MetricCodes.Spherical.HigherYoungAllRankSelectedBranchSignature
open MetricCodes.Spherical.ThreeRowYoungBranching

theorem gtFullTransverseEmbedding_range_eq_selectedTransverseTensorEmbedding
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (tau : Fin (r + 1) → ℕ) (h : Interlaces lam tau)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hdom : Antitone lam)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam tau h) :
    LinearMap.range
        (gtFullTransverseEmbedding lam hn
          (fullBranchOfInterlaces tau h)).toLinearMap =
      LinearMap.range
        (gtTransverseTensorEmbedding lam tau h hgram).toLinearMap := by
  change
    LinearMap.range
        (TensorProduct.map (gtTransverseEuclideanIsometry n).toLinearMap
          (canonicalFullBranchFibre lam hn
            (fullBranchOfInterlaces tau h)).toLinearMap) =
      LinearMap.range
        (TensorProduct.map (gtTransverseEuclideanIsometry n).toLinearMap
          (canonicalGelfandTsetlinFibre lam tau h hgram).toLinearMap)
  rw [TensorProduct.range_map, TensorProduct.range_map,
    canonicalGelfandTsetlinFibre_range_eq_selectedFullBranch
      lam tau h hn hdom hgram]

end AllRankGTFullySelectedTransverseBranchProjection

end

section


open scoped BigOperators InnerProductSpace TensorProduct

namespace AllRankGTPhysicalSelectedTwoBlockClosure

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTActualAxisTransverseDecomposition
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTPhysicalCompleteBlockReconstruction
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseFullBranchDecomposition
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness

theorem linearIsometry_range_starProjection
    {E H : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ H]
    (F : E →ₗᵢ[ℝ] H) (x : H) :
    (LinearMap.range F.toLinearMap).starProjection x =
      F (F.toLinearMap.adjoint x) := by
  apply (LinearMap.range F.toLinearMap).eq_starProjection_of_mem_of_inner_eq_zero
  · exact ⟨F.toLinearMap.adjoint x, rfl⟩
  · rintro _ ⟨p, rfl⟩
    change ⟪x - F (F.toLinearMap.adjoint x), F p⟫_ℝ = 0
    rw [inner_sub_left]
    change
      ⟪x, F.toLinearMap p⟫_ℝ -
        ⟪F (F.toLinearMap.adjoint x), F p⟫_ℝ = 0
    rw [← LinearMap.adjoint_inner_left F.toLinearMap p x,
      F.inner_map_map, sub_self]

theorem mem_submodule_of_complete_orthogonal_two_family_projections
    {ι κ H : Type*} [Finite ι] [Finite κ]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]
    (U : ι → Submodule ℝ H) (V : κ → Submodule ℝ H)
    (hU : ∀ i j : ι, i ≠ j → U i ⟂ U j)
    (hV : ∀ i j : κ, i ≠ j → V i ⟂ V j)
    (hUV : ∀ i : ι, ∀ j : κ, U i ⟂ V j)
    (hcomplete : (⨆ i, U i) ⊔ (⨆ j, V j) = ⊤)
    (S : Submodule ℝ H) (x : H)
    (haxis : ∀ i : ι, (U i).starProjection x ∈ S)
    (htransverse : ∀ j : κ, (V j).starProjection x ∈ S) :
    x ∈ S := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  let _ : Fintype κ := Fintype.ofFinite κ
  let W : ι ⊕ κ → Submodule ℝ H := Sum.elim U V
  have hpair : ∀ a b : ι ⊕ κ, a ≠ b → W a ⟂ W b := by
    intro a b hab
    cases a with
    | inl i =>
      cases b with
      | inl j => exact hU i j (fun hij => hab (congrArg Sum.inl hij))
      | inr j => exact hUV i j
    | inr i =>
      cases b with
      | inl j => exact (hUV j i).symm
      | inr j => exact hV i j (fun hij => hab (congrArg Sum.inr hij))
  have horth : OrthogonalFamily ℝ
      (fun i : ι ⊕ κ => ↥(W i)) (fun i => (W i).subtypeₗᵢ) :=
    OrthogonalFamily.of_pairwise hpair
  have hspan : (⨆ i : ι ⊕ κ, W i) = ⊤ := by
    rw [iSup_sum]
    change (⨆ i, U i) ⊔ (⨆ j, V j) = ⊤
    exact hcomplete
  have hx : x ∈ ⨆ i : ι ⊕ κ, W i := by
    rw [hspan]
    trivial
  rw [← horth.sum_projection_of_mem_iSup x hx]
  apply S.sum_mem
  intro i _
  cases i with
  | inl j => exact haxis j
  | inr j => exact htransverse j

theorem gtPhysicalTensor_mem_submodule_of_full_axis_transverse_projection
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (hn : 2 * r + 5 ≤ n + 1) (hdom : Antitone lam)
    (S : Submodule ℝ
      (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
        HarmonicYoungSpace (n := n + 1) lam))
    (x : SpherePacking.Euclidean (n + 1) ⊗[ℝ]
      HarmonicYoungSpace (n := n + 1) lam)
    (haxis : ∀ mu : FullBranchWeight lam,
      gtFullAxisEmbedding lam hn mu
        ((gtFullAxisEmbedding lam hn mu).toLinearMap.adjoint x) ∈ S)
    (htransverse : ∀ mu : FullBranchWeight lam,
      gtFullTransverseEmbedding lam hn mu
        ((gtFullTransverseEmbedding lam hn mu).toLinearMap.adjoint x) ∈ S) :
    x ∈ S := by
  apply mem_submodule_of_complete_orthogonal_two_family_projections
    (fun mu : FullBranchWeight lam =>
      LinearMap.range (gtFullAxisEmbedding lam hn mu).toLinearMap)
    (fun mu : FullBranchWeight lam =>
      LinearMap.range (gtFullTransverseEmbedding lam hn mu).toLinearMap)
    (S := S) (x := x)
  · intro i j hij
    apply Submodule.isOrtho_iff_inner_eq.mpr
    rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩
    exact gtFullAxisEmbedding_orthogonal lam hn i j hij p q
  · intro i j hij
    apply Submodule.isOrtho_iff_inner_eq.mpr
    rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩
    exact gtFullTransverseEmbedding_orthogonal lam hn i j hij p q
  · intro i j
    apply Submodule.isOrtho_iff_inner_eq.mpr
    rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩
    exact gtFullAxisEmbedding_inner_transverse_eq_zero lam hn i j p q
  · exact gtFullAxisTransverse_iSup_range_eq_top lam hn hdom
  · intro i
    rw [linearIsometry_range_starProjection]
    exact haxis i
  · intro i
    rw [linearIsometry_range_starProjection]
    exact htransverse i

end AllRankGTPhysicalSelectedTwoBlockClosure

end

section


open scoped InnerProductSpace TensorProduct

namespace AllRankGTTransverseSelectedClebschRange

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseWignerEckartHighest
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankZeroRowTensorCasimirConjugacy
open MetricCodes.Spherical.HigherHarmonicYoung.ClebschRotation
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherYoungAllRankGTAppendedRowLegality
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriActualChannels
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriSourceSignatureInjectivity
open MetricCodes.Spherical.ThreeRowYoungBranching

theorem linearIsometry_projection_mem_range_of_adjoint_coordinate_mem
    {X Y Z : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
    [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y]
    (F : X →ₗᵢ[ℝ] Y) (B : Z →ₗ[ℝ] Y)
    (hBF : LinearMap.range B ≤ LinearMap.range F.toLinearMap)
    (v : Y)
    (hcoordinate : F.toLinearMap.adjoint v ∈
      LinearMap.range (F.toLinearMap.adjoint.comp B)) :
    F (F.toLinearMap.adjoint v) ∈ LinearMap.range B := by
  obtain ⟨p, hp⟩ := hcoordinate
  obtain ⟨x, hx⟩ := hBF ⟨p, rfl⟩
  have hself := LinearMap.congr_fun F.adjoint_comp_self' x
  have hself' : F.toLinearMap.adjoint (F.toLinearMap x) = x := by
    simpa only [LinearMap.comp_apply, LinearMap.id_apply] using hself
  have hcoord : F.toLinearMap.adjoint (B p) =
      F.toLinearMap.adjoint v := by
    simpa only [LinearMap.comp_apply] using hp
  change F.toLinearMap (F.toLinearMap.adjoint v) ∈ LinearMap.range B
  refine ⟨p, ?_⟩
  calc
    B p = F.toLinearMap x := hx.symm
    _ = F.toLinearMap
      (F.toLinearMap.adjoint (F.toLinearMap x)) :=
        congrArg F.toLinearMap hself'.symm
    _ = F.toLinearMap (F.toLinearMap.adjoint (B p)) :=
      congrArg (fun y : Y => F.toLinearMap (F.toLinearMap.adjoint y)) hx
    _ = F.toLinearMap (F.toLinearMap.adjoint v) :=
      congrArg F.toLinearMap hcoord

theorem linearIsometry_projection_mem_range_of_adjoint_scalar
    {X Y Z : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
    [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y]
    (F : X →ₗᵢ[ℝ] Y) (B : Z →ₗ[ℝ] Y)
    (hBF : LinearMap.range B ≤ LinearMap.range F.toLinearMap)
    (v : Y) (p : Z) (d : ℝ)
    (hcoordinate : F.toLinearMap.adjoint v =
      d • F.toLinearMap.adjoint (B p)) :
    F (F.toLinearMap.adjoint v) ∈ LinearMap.range B := by
  apply linearIsometry_projection_mem_range_of_adjoint_coordinate_mem
    F B hBF v
  refine ⟨d • p, ?_⟩
  simpa only [LinearMap.comp_apply, map_smul] using hcoordinate.symm

theorem linearMap_range_le_isometry_of_scaled_factor_of_range_eq
    {W X Y Z : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
    (F : X →ₗᵢ[ℝ] Y) (E : W →ₗᵢ[ℝ] Y)
    (B : Z →ₗ[ℝ] Y) (C : Z →ₗ[ℝ] W) (phase : ℝ)
    (hrange : LinearMap.range F.toLinearMap =
      LinearMap.range E.toLinearMap)
    (hfactor : B = phase • E.toLinearMap.comp C) :
    LinearMap.range B ≤ LinearMap.range F.toLinearMap := by
  intro y hy
  obtain ⟨p, rfl⟩ := hy
  rw [hrange]
  refine ⟨phase • C p, ?_⟩
  rw [map_smul, hfactor]
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]

end AllRankGTTransverseSelectedClebschRange

end

section


open scoped BigOperators InnerProductSpace TensorProduct

namespace AllRankGTTransverseRetainedTwoBlockClosure

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTActualAxisTransverseDecomposition
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTFullySelectedTransverseBranchProjection
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTFullTransverseSameSignatureRow
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTNormalizedTransverseRotationIntertwining
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTPhysicalSelectedTwoBlockClosure
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTSelectedMuAxisProjectionVanishing
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCasimirEmbedding
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseFullBranchDecomposition
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseSelectedClebschRange
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseWignerEckartPhase
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseWrongBranchCompression
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTValidTransverseArrowheadRow
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInternalRowLowerGram
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherRepresentationGraph (Interlaces)
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness
open MetricCodes.Spherical.HigherYoungAllRankGTArrowheadSchurComplement
open MetricCodes.Spherical.HigherYoungAllRankSelectedBranchSignature
open MetricCodes.Spherical.ThreeRowYoungBranching

theorem normalizedGTTransverseNegativeSector_range_le_selectedFullTransverse
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (kappa : Fin r → ℕ)
    (row : Fin (r + 1))
    (hnu : Interlaces lam (raiseWeight mu row))
    (hnuGram : PositiveGelfandTsetlinFischerGram
      (n := n) lam (raiseWeight mu row) hnu)
    (hfinite : FiniteInterlacing n mu kappa)
    (hraise : FiniteInterlacing n (raiseWeight mu row) kappa)
    (hn : 2 * (r + 1) + 5 ≤ n + 1) :
    LinearMap.range
        (normalizedGTTransverseNegativeSector lam mu kappa row
          hnu hnuGram hfinite hraise).toLinearMap ≤
      LinearMap.range
        (gtFullTransverseEmbedding lam hn
          (fullBranchOfInterlaces (raiseWeight mu row) hnu)).toLinearMap := by
  apply linearMap_range_le_isometry_of_scaled_factor_of_range_eq
    (gtFullTransverseEmbedding lam hn
      (fullBranchOfInterlaces (raiseWeight mu row) hnu))
    (gtTransverseTensorEmbedding lam (raiseWeight mu row) hnu hnuGram)
    (normalizedGTTransverseNegativeSector lam mu kappa row
      hnu hnuGram hfinite hraise).toLinearMap
    (youngClebschRaise (raiseWeight mu row) mu
      (sum_raiseWeight mu row) row)
    (Real.sqrt (internalRowLowerGramScalar (raiseWeight mu row) row *
      weylEdgeRatio n mu row))⁻¹
  · exact gtFullTransverseEmbedding_range_eq_selectedTransverseTensorEmbedding
      lam (raiseWeight mu row) hnu hn hnu.antitone_ambient hnuGram
  · exact normalizedGTTransverseNegativeSector_toLinearMap
      lam mu kappa row hnu hnuGram hfinite hraise

theorem normalizedGTTransversePositiveSector_range_le_selectedFullTransverse
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu nu : Fin (r + 1) → ℕ) (row : Fin (r + 1))
    (hmunu : mu = raiseWeight nu row)
    (hmu : Interlaces lam mu)
    (hnu : Interlaces lam nu)
    (hnuGram : PositiveGelfandTsetlinFischerGram
      (n := n) lam nu hnu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1) :
    LinearMap.range
        (normalizedGTTransversePositiveSector
          lam mu nu row hmunu hmu hnu hnuGram).toLinearMap ≤
      LinearMap.range
        (gtFullTransverseEmbedding lam hn
          (fullBranchOfInterlaces nu hnu)).toLinearMap := by
  apply linearMap_range_le_isometry_of_scaled_factor_of_range_eq
    (gtFullTransverseEmbedding lam hn (fullBranchOfInterlaces nu hnu))
    (gtTransverseTensorEmbedding lam nu hnu hnuGram)
    (normalizedGTTransversePositiveSector
      lam mu nu row hmunu hmu hnu hnuGram).toLinearMap
    (youngClebschLower nu mu
      (by rw [hmunu]; exact sum_raiseWeight nu row) row)
    (Real.sqrt (internalRowLowerGramScalar mu row))⁻¹
  · exact gtFullTransverseEmbedding_range_eq_selectedTransverseTensorEmbedding
      lam nu hnu hn hnu.antitone_ambient hnuGram
  · exact normalizedGTTransversePositiveSector_toLinearMap
      lam mu nu row hmunu hmu hnu hnuGram

theorem gtTransverseNegativeSector_relativeCasimir_mem_axis_sup_sector
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (kappa : Fin r → ℕ)
    (row : Fin (r + 1))
    (hmu : Interlaces lam mu)
    (hmuGram : PositiveGelfandTsetlinFischerGram (n := n) lam mu hmu)
    (hnu : Interlaces lam (raiseWeight mu row))
    (hnuGram : PositiveGelfandTsetlinFischerGram
      (n := n) lam (raiseWeight mu row) hnu)
    (hfinite : FiniteInterlacing n mu kappa)
    (hraise : FiniteInterlacing n (raiseWeight mu row) kappa)
    (hstable : 2 * (r + 2) + 5 ≤ n + 1)
    (p : HarmonicYoungSpace (n := n) mu) :
    gtRelativeCasimir lam
      (normalizedGTTransverseNegativeSector lam mu kappa row
        hnu hnuGram hfinite hraise p) ∈
      LinearMap.range
        (canonicalGelfandTsetlinAxisIsometry
          lam mu hmu hmuGram).toLinearMap ⊔
      LinearMap.range
        (normalizedGTTransverseNegativeSector lam mu kappa row
          hnu hnuGram hfinite hraise).toLinearMap := by
  let hn : 2 * (r + 1) + 5 ≤ n + 1 := by omega
  let A := canonicalGelfandTsetlinAxisIsometry lam mu hmu hmuGram
  let B := normalizedGTTransverseNegativeSector lam mu kappa row
    hnu hnuGram hfinite hraise
  let S := LinearMap.range A.toLinearMap ⊔ LinearMap.range B.toLinearMap
  change gtRelativeCasimir lam (B p) ∈ S
  apply gtPhysicalTensor_mem_submodule_of_full_axis_transverse_projection
    lam hn hmu.antitone_ambient S (gtRelativeCasimir lam (B p))
  · intro branch
    by_cases hs : fullBranchSignature branch = appendZeroWeight mu
    · have hb :=
        (fullBranch_eq_selected_iff_signature_eq_appendZeroWeight
          mu hmu branch).mpr hs
      subst branch
      apply Submodule.mem_sup_left
      rw [← gtFullAxisEmbedding_selected_range_eq_canonicalAxis
        lam mu hmu hn hmuGram]
      exact ⟨_, rfl⟩
    · have hz :=
        gtFullAxisEmbedding_adjoint_relativeCasimir_stabilizerSector_eq_zero
          lam mu hmu hstable branch hs B.toLinearMap
          (normalizedGTTransverseNegativeSector_rotation_intertwine
            lam mu kappa row hnu hnuGram hfinite hraise) p
      change gtFullAxisEmbedding lam hn branch
        ((gtFullAxisEmbedding lam hn branch).toLinearMap.adjoint
          (gtRelativeCasimir lam (B p))) ∈ S
      change (gtFullAxisEmbedding lam hn branch).toLinearMap.adjoint
        (gtRelativeCasimir lam (B p)) = 0 at hz
      rw [hz, map_zero]
      exact S.zero_mem
  · intro branch
    by_cases hb : branch =
        fullBranchOfInterlaces (raiseWeight mu row) hnu
    · subst branch
      apply Submodule.mem_sup_right
      apply linearIsometry_projection_mem_range_of_adjoint_scalar
        (gtFullTransverseEmbedding lam hn
          (fullBranchOfInterlaces (raiseWeight mu row) hnu))
        B.toLinearMap
        (normalizedGTTransverseNegativeSector_range_le_selectedFullTransverse
          lam mu kappa row hnu hnuGram hfinite hraise hn)
        (gtRelativeCasimir lam (B p)) p
        (gtStabilizerArrowheadNode (wallShift (n + 1) (r + 1))
          (stabilizerShift (n + 1) mu) (.inr (row, false)))
      exact negativeSector_selectedFullTensor_adjoint_eigen
        lam mu kappa row hnu hnuGram hfinite hraise hn p
    · have hz :=
        gtFullTransverseEmbedding_normalizedNegativeRelativeCasimir_eq_zero_of_wrong_branch
          lam mu kappa row hnu hnuGram hfinite hraise hn branch hb p
      change gtFullTransverseEmbedding lam hn branch
        ((gtFullTransverseEmbedding lam hn branch).toLinearMap.adjoint
          (gtRelativeCasimir lam (B p))) ∈ S
      rw [hz, map_zero]
      exact S.zero_mem

theorem gtTransversePositiveSector_relativeCasimir_mem_axis_sup_sector
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu nu : Fin (r + 1) → ℕ) (row : Fin (r + 1))
    (hmunu : mu = raiseWeight nu row)
    (hmu : Interlaces lam mu)
    (hmuGram : PositiveGelfandTsetlinFischerGram (n := n) lam mu hmu)
    (hnu : Interlaces lam nu)
    (hnuGram : PositiveGelfandTsetlinFischerGram
      (n := n) lam nu hnu)
    (hstable : 2 * (r + 2) + 5 ≤ n + 1)
    (p : HarmonicYoungSpace (n := n) mu) :
    gtRelativeCasimir lam
      (normalizedGTTransversePositiveSector
        lam mu nu row hmunu hmu hnu hnuGram p) ∈
      LinearMap.range
        (canonicalGelfandTsetlinAxisIsometry
          lam mu hmu hmuGram).toLinearMap ⊔
      LinearMap.range
        (normalizedGTTransversePositiveSector
          lam mu nu row hmunu hmu hnu hnuGram).toLinearMap := by
  let hn : 2 * (r + 1) + 5 ≤ n + 1 := by omega
  let A := canonicalGelfandTsetlinAxisIsometry lam mu hmu hmuGram
  let B := normalizedGTTransversePositiveSector
    lam mu nu row hmunu hmu hnu hnuGram
  let S := LinearMap.range A.toLinearMap ⊔ LinearMap.range B.toLinearMap
  change gtRelativeCasimir lam (B p) ∈ S
  apply gtPhysicalTensor_mem_submodule_of_full_axis_transverse_projection
    lam hn hmu.antitone_ambient S (gtRelativeCasimir lam (B p))
  · intro branch
    by_cases hs : fullBranchSignature branch = appendZeroWeight mu
    · have hb :=
        (fullBranch_eq_selected_iff_signature_eq_appendZeroWeight
          mu hmu branch).mpr hs
      subst branch
      apply Submodule.mem_sup_left
      rw [← gtFullAxisEmbedding_selected_range_eq_canonicalAxis
        lam mu hmu hn hmuGram]
      exact ⟨_, rfl⟩
    · have hz :=
        gtFullAxisEmbedding_adjoint_relativeCasimir_stabilizerSector_eq_zero
          lam mu hmu hstable branch hs B.toLinearMap
          (normalizedGTTransversePositiveSector_rotation_intertwine
            lam mu nu row hmunu hmu hnu hnuGram) p
      change gtFullAxisEmbedding lam hn branch
        ((gtFullAxisEmbedding lam hn branch).toLinearMap.adjoint
          (gtRelativeCasimir lam (B p))) ∈ S
      change (gtFullAxisEmbedding lam hn branch).toLinearMap.adjoint
        (gtRelativeCasimir lam (B p)) = 0 at hz
      rw [hz, map_zero]
      exact S.zero_mem
  · intro branch
    by_cases hb : branch = fullBranchOfInterlaces nu hnu
    · subst branch
      apply Submodule.mem_sup_right
      apply linearIsometry_projection_mem_range_of_adjoint_scalar
        (gtFullTransverseEmbedding lam hn (fullBranchOfInterlaces nu hnu))
        B.toLinearMap
        (normalizedGTTransversePositiveSector_range_le_selectedFullTransverse
          lam mu nu row hmunu hmu hnu hnuGram hn)
        (gtRelativeCasimir lam (B p)) p
        (gtStabilizerArrowheadNode (wallShift (n + 1) (r + 1))
          (stabilizerShift (n + 1) mu) (.inr (row, true)))
      exact positiveSector_selectedFullTensor_adjoint_eigen
        lam mu nu row hmunu hmu hnu hnuGram hn p
    · have hz :=
        gtFullTransverseEmbedding_normalizedPositiveRelativeCasimir_eq_zero_of_wrong_branch
          lam mu nu row hmunu hmu hnu hnuGram hn branch hb p
      change gtFullTransverseEmbedding lam hn branch
        ((gtFullTransverseEmbedding lam hn branch).toLinearMap.adjoint
          (gtRelativeCasimir lam (B p))) ∈ S
      rw [hz, map_zero]
      exact S.zero_mem

end AllRankGTTransverseRetainedTwoBlockClosure

end

section


open scoped BigOperators InnerProductSpace TensorProduct

namespace AllRankGTAxisCompressedValidNodeRoot

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAxisCompressedCharacteristicMinor
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherRepresentationGraph (Interlaces)
open MetricCodes.Spherical.HigherYoungAllRankGTCharacteristicResidue

private def signedCharacteristicAdjugate {r : ℕ} {V : Type*}
    [AddCommGroup V] [Module ℝ V]
    (L : Fin (r + 1) → ℝ) (T : Module.End ℝ V)
    (z : ℝ) : Module.End ℝ V :=
  ∑ channel : Fin (r + 1) × Bool,
    (Lagrange.nodal
      ((Finset.univ : Finset (Fin (r + 1) × Bool)).erase channel)
      (signedNode L)).eval z •
        signedCharacteristicProjector L T channel

theorem signedCharacteristicAdjugate_resolvent_apply
    {r : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V]
    (L : Fin (r + 1) → ℝ)
    (hL : Function.Injective (signedNode L))
    (T : Module.End ℝ V) (z : ℝ) (v : V)
    (hchar : Polynomial.aeval T (signedAmbientCharacteristic L) v = 0) :
    (z • (LinearMap.id : Module.End ℝ V) - T)
        (signedCharacteristicAdjugate L T z v) =
      (signedAmbientCharacteristic L).eval z • v := by
  classical
  unfold signedCharacteristicAdjugate
  simp only [LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, LinearMap.sum_apply]
  rw [Finset.smul_sum, map_sum, ← Finset.sum_sub_distrib]
  have hterm (channel : Fin (r + 1) × Bool) :
      z • ((Lagrange.nodal
          ((Finset.univ : Finset (Fin (r + 1) × Bool)).erase channel)
          (signedNode L)).eval z •
            signedCharacteristicProjector L T channel v) -
        T ((Lagrange.nodal
          ((Finset.univ : Finset (Fin (r + 1) × Bool)).erase channel)
          (signedNode L)).eval z •
            signedCharacteristicProjector L T channel v) =
        (signedAmbientCharacteristic L).eval z •
          signedCharacteristicProjector L T channel v := by
    rw [map_smul,
      signedCharacteristicProjector_eigen_of_aeval_apply
        L T channel v hchar,
      smul_smul, smul_smul, ← sub_smul]
    congr 1
    have hnodal := congrArg (Polynomial.eval z)
      (Lagrange.nodal_eq_mul_nodal_erase
        (s := (Finset.univ : Finset (Fin (r + 1) × Bool)))
        (v := signedNode L) (Finset.mem_univ channel))
    simp only [Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C] at hnodal
    change
      z * _ - _ * signedNode L channel =
        (signedAmbientCharacteristic L).eval z
    change
      z * _ - _ * signedNode L channel =
        (Lagrange.nodal Finset.univ (signedNode L)).eval z
    nlinarith
  simp_rw [hterm]
  rw [← Finset.smul_sum]
  congr 1
  simpa only [LinearMap.sum_apply, LinearMap.id_apply] using
    LinearMap.congr_fun (sum_signedCharacteristicProjector L hL T) v

theorem gtAxisCompressedCharacteristicMinor_eval_eq_adjugate_inner
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (hfinite : FiniteInterlacing (n + 1) lam mu)
    (p q : HarmonicYoungSpace (n := n) mu) (z : ℝ) :
    (gtAxisCompressedCharacteristicMinor lam mu h hgram p q).eval z =
      ⟪canonicalGelfandTsetlinAxisTensor lam mu h hgram p,
        signedCharacteristicAdjugate
          (ambientShift (n + 1) lam)
          (gtRelativeCasimir (n := n + 1) lam) z
            (canonicalGelfandTsetlinAxisTensor lam mu h hgram q)⟫_ℝ := by
  classical
  rw [gtAxisCompressedCharacteristicMinor_eq_sum_nodal_erase
    lam mu h hgram hfinite p q]
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, signedCharacteristicAdjugate,
    LinearMap.sum_apply, inner_sum, LinearMap.smul_apply,
    real_inner_smul_right,
    gtAxisCompressedSignedProjectorCoefficient]
  apply Finset.sum_congr rfl
  intro channel _
  ring

theorem gtAxisCompressedCharacteristicMinor_eval_eq_zero_of_arrowhead_operator_row
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (hfinite : FiniteInterlacing (n + 1) lam mu)
    (p q : HarmonicYoungSpace (n := n) mu)
    (B : HarmonicYoungSpace (n := n) mu →ₗ[ℝ]
      (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
        HarmonicYoungSpace (n := n + 1) lam))
    (node : ℝ)
    (coupling : Module.End ℝ (HarmonicYoungSpace (n := n) mu))
    (hcoupling : Function.Injective coupling)
    (horth : B.adjoint
      (canonicalGelfandTsetlinAxisTensor lam mu h hgram q) = 0)
    (hchar :
      Polynomial.aeval (gtRelativeCasimir (n := n + 1) lam)
        (gtChannelCharacteristicPolynomial (n + 1) lam)
        (canonicalGelfandTsetlinAxisTensor lam mu h hgram q) = 0)
    (hrow : ∀ x : SpherePacking.Euclidean (n + 1) ⊗[ℝ]
        HarmonicYoungSpace (n := n + 1) lam,
      B.adjoint (gtRelativeCasimir (n := n + 1) lam x) =
        node • B.adjoint x +
          coupling ((canonicalGelfandTsetlinAxisTensor
            lam mu h hgram).adjoint x)) :
    (gtAxisCompressedCharacteristicMinor lam mu h hgram p q).eval node = 0 := by
  let A := canonicalGelfandTsetlinAxisTensor lam mu h hgram
  let T := gtRelativeCasimir (n := n + 1) lam
  let v := signedCharacteristicAdjugate
    (ambientShift (n + 1) lam) T node (A q)
  have hresolvent := signedCharacteristicAdjugate_resolvent_apply
    (ambientShift (n + 1) lam)
    (signedNode_injective hfinite.ambientShift_pos
      hfinite.ambientShift_strictAnti.injective)
    T node (A q) hchar
  change node • v - T v =
    (gtChannelCharacteristicPolynomial (n + 1) lam).eval node • A q at hresolvent
  have hprojected := congrArg B.adjoint hresolvent
  rw [map_sub, map_smul, map_smul, horth, smul_zero,
    hrow v] at hprojected
  have haxis : A.adjoint v = 0 := by
    apply hcoupling
    simpa only [map_zero, sub_add_cancel_left, neg_eq_zero] using hprojected
  rw [gtAxisCompressedCharacteristicMinor_eval_eq_adjugate_inner
    lam mu h hgram hfinite p q node]
  change ⟪A p, v⟫_ℝ = 0
  rw [← LinearMap.adjoint_inner_right A p v, haxis, inner_zero_right]

end AllRankGTAxisCompressedValidNodeRoot

end

end HigherHarmonicYoung

section


open scoped BigOperators InnerProductSpace TensorProduct

namespace HigherYoungAllRankGTCanonicalAxisSignedCharacteristic

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolventSpectral
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseOrthogonalCompleteness
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungAllRankGTCharacteristicResidue

theorem gtChannelCharacteristic_aeval_canonicalAxis_eq_zero
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hn : 2 * (r + 2) + 5 ≤ n + 1)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (p : HarmonicYoungSpace (n := n) mu) :
    Polynomial.aeval (gtRelativeCasimir (n := n + 1) lam)
        (gtChannelCharacteristicPolynomial (n + 1) lam)
        (canonicalGelfandTsetlinAxisTensor lam mu h hgram p) = 0 := by
  simpa only [canonicalGelfandTsetlinAxisTensor_apply, EuclideanSpace.basisFun_apply,
    canonicalGelfandTsetlinFibre_apply, TensorProduct.tmul_smul, map_smul, smul_eq_zero,
      inv_eq_zero, pow_zero,
    Module.End.one_apply] using
    gtChannelCharacteristic_aeval_apply_canonicalAxis_iterate_eq_zero lam mu h hgram p
      (canonicalGelfandTsetlinAxisTensor_mem_gtSignedEigenvectorSpan lam mu h hn hgram p) 0

end HigherYoungAllRankGTCanonicalAxisSignedCharacteristic

end

namespace HigherHarmonicYoung

section


open scoped BigOperators

namespace AllRankGTAmbientCharacteristicAtTransverseNode

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherYoungAllRankGTArrowheadSchurComplement
open MetricCodes.Spherical.HigherYoungAllRankGTCharacteristicResidue

theorem signedAmbientCharacteristic_eval_ne_zero_of_forall_ne
    {r : ℕ} (L : Fin (r + 1) → ℝ) (d : ℝ)
    (hnode : ∀ i : Fin (r + 1) × Bool, d ≠ signedNode L i) :
    (signedAmbientCharacteristic L).eval d ≠ 0 := by
  unfold signedAmbientCharacteristic
  apply Lagrange.eval_nodal_not_at_node
  intro i _
  exact hnode i

theorem gtChannelCharacteristicPolynomial_eval_ne_zero_of_forall_ne
    {r n : ℕ} (lam : Fin (r + 1) → ℕ) (d : ℝ)
    (hnode : ∀ i : Fin (r + 1) × Bool,
      d ≠ signedNode (ambientShift n lam) i) :
    (gtChannelCharacteristicPolynomial n lam).eval d ≠ 0 :=
  signedAmbientCharacteristic_eval_ne_zero_of_forall_ne
    (ambientShift n lam) d hnode

end AllRankGTAmbientCharacteristicAtTransverseNode

end

section


open scoped InnerProductSpace

namespace AllRankGTTransverseCouplingNonzero

theorem polynomial_eigenvector_eq_zero_of_annihilating_eval_ne_zero
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (T : Module.End ℝ V) (P : Polynomial ℝ)
    (d : ℝ) (v : V)
    (heigen : T v = d • v)
    (hchar : Polynomial.aeval T P v = 0)
    (heval : P.eval d ≠ 0) : v = 0 := by
  rw [Module.End.aeval_apply_of_mem_apply_eq_smul heigen] at hchar
  exact (smul_eq_zero.mp hchar).resolve_left heval

end AllRankGTTransverseCouplingNonzero

end

section


open scoped InnerProductSpace TensorProduct

namespace AllRankGTCartanSpectralCouplingNonvanishing

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAmbientCharacteristicAtTransverseNode
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCouplingNonzero
open MetricCodes.Spherical.HigherYoungAllRankGTCharacteristicResidue

theorem arrowhead_eigen_of_coupling_kernel
    {E F V : Type*}
    [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F]
    [AddCommGroup V] [Module ℝ V]
    (T : Module.End ℝ V)
    (B : E →ₗ[ℝ] V) (A : F →ₗ[ℝ] V) (K : E →ₗ[ℝ] F)
    (d : ℝ)
    (hrow : T.comp B = d • B + A.comp K)
    (p : E) (hp : K p = 0) :
    T (B p) = d • B p := by
  have h := LinearMap.congr_fun hrow p
  simpa only [LinearMap.comp_apply, LinearMap.add_apply,
    LinearMap.smul_apply, hp, map_zero, add_zero] using h

theorem arrowhead_coupling_eq_zero_of_apply_eq_zero
    {E F V : Type*}
    [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F]
    [AddCommGroup V] [Module ℝ V]
    (T : Module.End ℝ V)
    (B : E →ₗ[ℝ] V) (hB : Function.Injective B)
    (A : F →ₗ[ℝ] V) (K : E →ₗ[ℝ] F)
    (P : Polynomial ℝ) (d : ℝ)
    (hrow : T.comp B = d • B + A.comp K)
    (hchar : ∀ p : E, Polynomial.aeval T P (B p) = 0)
    (heval : P.eval d ≠ 0)
    (p : E) (hp : K p = 0) : p = 0 := by
  have heigen := arrowhead_eigen_of_coupling_kernel
    T B A K d hrow p hp
  have hzero := polynomial_eigenvector_eq_zero_of_annihilating_eval_ne_zero
    T P d (B p) heigen (hchar p) heval
  exact hB (by simpa only [map_zero] using hzero)

theorem arrowhead_coupling_injective_of_characteristic
    {E F V : Type*}
    [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F]
    [AddCommGroup V] [Module ℝ V]
    (T : Module.End ℝ V)
    (B : E →ₗ[ℝ] V) (hB : Function.Injective B)
    (A : F →ₗ[ℝ] V) (K : E →ₗ[ℝ] F)
    (P : Polynomial ℝ) (d : ℝ)
    (hrow : T.comp B = d • B + A.comp K)
    (hchar : ∀ p : E, Polynomial.aeval T P (B p) = 0)
    (heval : P.eval d ≠ 0) :
    Function.Injective K := by
  intro p q hpq
  apply sub_eq_zero.mp
  apply arrowhead_coupling_eq_zero_of_apply_eq_zero
    T B hB A K P d hrow hchar heval (p - q)
  rw [map_sub, hpq, sub_self]

theorem arrowhead_isometric_coupling_injective_of_characteristic
    {E F V : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [AddCommGroup F] [Module ℝ F]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (T : Module.End ℝ V)
    (B : E →ₗᵢ[ℝ] V)
    (A : F →ₗ[ℝ] V) (K : E →ₗ[ℝ] F)
    (P : Polynomial ℝ) (d : ℝ)
    (hrow : T.comp B.toLinearMap = d • B.toLinearMap + A.comp K)
    (hchar : ∀ p : E, Polynomial.aeval T P (B p) = 0)
    (heval : P.eval d ≠ 0) :
    Function.Injective K :=
  arrowhead_coupling_injective_of_characteristic
    T B.toLinearMap B.injective A K P d hrow hchar heval

theorem gtSignedArrowheadCoupling_injective
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [AddCommGroup F] [Module ℝ F]
    (B : E →ₗᵢ[ℝ]
      (SpherePacking.Euclidean n ⊗[ℝ]
        HarmonicYoungSpace (n := n) lam))
    (A : F →ₗ[ℝ]
      (SpherePacking.Euclidean n ⊗[ℝ]
        HarmonicYoungSpace (n := n) lam))
    (K : E →ₗ[ℝ] F) (d : ℝ)
    (hrow :
      (gtRelativeCasimir (n := n) lam).comp B.toLinearMap =
        d • B.toLinearMap + A.comp K)
    (hchar : ∀ p : E,
      Polynomial.aeval (gtRelativeCasimir (n := n) lam)
        (gtChannelCharacteristicPolynomial n lam) (B p) = 0)
    (hnode : ∀ i : Fin (r + 1) × Bool,
      d ≠ signedNode (HigherChannel.ambientShift n lam) i) :
    Function.Injective K := by
  apply arrowhead_isometric_coupling_injective_of_characteristic
    (gtRelativeCasimir (n := n) lam) B A K
    (gtChannelCharacteristicPolynomial n lam) d hrow hchar
  exact gtChannelCharacteristicPolynomial_eval_ne_zero_of_forall_ne
    lam d hnode

end AllRankGTCartanSpectralCouplingNonvanishing

end

section


open scoped BigOperators InnerProductSpace TensorProduct

namespace AllRankGTValidTransverseMinorRoots

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAxisCompressedCharacteristicMinor
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAxisCompressedValidNodeRoot
open MetricCodes.Spherical.HigherYoungAllRankGTCanonicalAxisSignedCharacteristic
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCartanSpectralCouplingNonvanishing
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCasimirEmbedding
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTValidTransverseArrowheadRow
open MetricCodes.Spherical.HigherRepresentationGraph (Interlaces)
open MetricCodes.Spherical.HigherYoungAllRankGTArrowheadSchurComplement
open MetricCodes.Spherical.HigherYoungAllRankGTCharacteristicResidue





private theorem end_adjoint_injective_of_injective_metriccodes2_f07ed3eb
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (K : Module.End ℝ V)
    (hK : Function.Injective K) : Function.Injective K.adjoint := by
  have hsurjective : Function.Surjective K :=
    LinearMap.injective_iff_surjective.mp hK
  have hrange : K.range = ⊤ := LinearMap.range_eq_top.mpr hsurjective
  have horthogonal := LinearMap.orthogonal_range K
  have hkernel : K.adjoint.ker = ⊥ := by
    simpa only [hrange, Submodule.top_orthogonal_eq_bot] using horthogonal.symm
  exact LinearMap.ker_eq_bot.mp hkernel

private theorem gtActualPhysicalColumn_adjoint_row_metriccodes2_f07ed3eb
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ)
    (A B : HarmonicYoungSpace (n := n) mu →ₗ[ℝ]
      (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
        HarmonicYoungSpace (n := n + 1) lam))
    (node : ℝ) (K : Module.End ℝ (HarmonicYoungSpace (n := n) mu))
    (hcolumn : (gtRelativeCasimir (n := n + 1) lam).comp B =
      node • B + A.comp K) :
    B.adjoint.comp (gtRelativeCasimir (n := n + 1) lam) =
      node • B.adjoint + K.adjoint.comp A.adjoint := by
  have hadjoint := congrArg LinearMap.adjoint hcolumn
  simpa only [LinearMap.adjoint_comp, LinearMap.adjoint_adjoint,
    gtRelativeCasimir_adjoint, map_add, map_smul] using hadjoint

theorem gtAxisCompressedCharacteristicMinor_eval_actualPhysicalNode_eq_zero
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ)
    (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram
      (n := n) lam mu h)
    (hfinite : FiniteInterlacing (n + 1) lam mu)
    (hn : 2 * (r + 2) + 5 ≤ n + 1)
    (B : HarmonicYoungSpace (n := n) mu →ₗᵢ[ℝ]
      (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
        HarmonicYoungSpace (n := n + 1) lam))
    (node : ℝ)
    (K : Module.End ℝ (HarmonicYoungSpace (n := n) mu))
    (horthogonal : ∀ p q : HarmonicYoungSpace (n := n) mu,
      ⟪canonicalGelfandTsetlinAxisTensor lam mu h hgram p,
        B q⟫_ℝ = 0)
    (hcolumn :
      (gtRelativeCasimir (n := n + 1) lam).comp B.toLinearMap =
        node • B.toLinearMap +
          (canonicalGelfandTsetlinAxisTensor lam mu h hgram).comp K)
    (hsector : ∀ p : HarmonicYoungSpace (n := n) mu,
      Polynomial.aeval (gtRelativeCasimir (n := n + 1) lam)
        (gtChannelCharacteristicPolynomial (n + 1) lam) (B p) = 0)
    (hnode : ∀ i : Fin (r + 2) × Bool,
      node ≠ signedNode (ambientShift (n + 1) lam) i)
    (p q : HarmonicYoungSpace (n := n) mu) :
    (gtAxisCompressedCharacteristicMinor lam mu h hgram p q).eval node = 0 := by
  have hK : Function.Injective K :=
    gtSignedArrowheadCoupling_injective lam B
      (canonicalGelfandTsetlinAxisTensor lam mu h hgram)
      K node hcolumn hsector hnode
  have hKadjoint : Function.Injective K.adjoint :=
    end_adjoint_injective_of_injective_metriccodes2_f07ed3eb K hK
  apply gtAxisCompressedCharacteristicMinor_eval_eq_zero_of_arrowhead_operator_row
    lam mu h hgram hfinite p q B.toLinearMap node K.adjoint hKadjoint
  · apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    rw [LinearMap.adjoint_inner_right, real_inner_comm]
    exact horthogonal q _
  · exact gtChannelCharacteristic_aeval_canonicalAxis_eq_zero
      lam mu h hn hgram q
  · intro x
    have hrow := LinearMap.congr_fun
      (gtActualPhysicalColumn_adjoint_row_metriccodes2_f07ed3eb lam mu
        (canonicalGelfandTsetlinAxisTensor lam mu h hgram)
        B.toLinearMap node K hcolumn) x
    simpa only [LinearMap.comp_apply, LinearMap.add_apply,
      LinearMap.smul_apply] using hrow

end AllRankGTValidTransverseMinorRoots

end

section


namespace AllRankGTAdjacentCommonInterlacing

open MetricCodes.Spherical.HigherChannel

private def gtSelectedPrefixWeight {r : ℕ}
    (mu : Fin (r + 1) → ℕ) : Fin r → ℕ :=
  fun j => mu j.castSucc

theorem gtSelectedPrefixWeight_finiteInterlacing
    {r n : ℕ} (mu : Fin (r + 1) → ℕ)
    (hn : 2 * r + 4 ≤ n) (hdom : Antitone mu) :
    FiniteInterlacing n mu (gtSelectedPrefixWeight mu) := by
  refine ⟨hn, ?_⟩
  intro j
  constructor
  · exact le_rfl
  · exact hdom (Fin.castSucc_le_succ j)

theorem gtSelectedPrefixWeight_finiteInterlacing_raise
    {r n : ℕ} (mu : Fin (r + 1) → ℕ)
    (row : Fin (r + 1)) (hn : 2 * r + 4 ≤ n)
    (hdom : Antitone mu)
    (hraiseDom : Antitone (raiseWeight mu row)) :
    FiniteInterlacing n (raiseWeight mu row)
      (gtSelectedPrefixWeight mu) := by
  refine ⟨hn, ?_⟩
  intro j
  constructor
  · change mu j.castSucc ≤ raiseWeight mu row j.castSucc
    by_cases hrow : j.castSucc = row
    · subst row
      simp only [raiseWeight, Function.update_self, le_add_iff_nonneg_right, zero_le]
    · simp only [raiseWeight, ne_eq, hrow, not_false_eq_true, Function.update_of_ne, Std.le_refl]
  · by_cases hrow : j.succ = row
    · have hne : j.castSucc ≠ row := by
        intro heq
        have hlt : j.castSucc < j.succ :=
          Fin.castSucc_lt_succ_iff.mpr le_rfl
        rw [heq, hrow] at hlt
        exact (lt_irrefl _ hlt)
      have hle := hraiseDom (Fin.castSucc_le_succ j)
      simpa only [raiseWeight, hrow, Function.update_self, gtSelectedPrefixWeight,
        Order.add_one_le_iff, gt_iff_lt, ne_eq, hne, not_false_eq_true,
        Function.update_of_ne] using hle
    · change raiseWeight mu row j.succ ≤ mu j.castSucc
      simpa only [raiseWeight, ne_eq, hrow, not_false_eq_true, Function.update_of_ne] using
        hdom (Fin.castSucc_le_succ j)

end AllRankGTAdjacentCommonInterlacing

end

section


namespace AllRankGTValidTransverseSignedIndex

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherRepresentationGraph (Interlaces)
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriSourceSignatureInjectivity
open MetricCodes.Spherical.HigherYoungPenultimateRowProjectedLower

end AllRankGTValidTransverseSignedIndex

end

section


open scoped BigOperators InnerProductSpace TensorProduct

namespace AllRankGTValidTransverseSectorFamily

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAdjacentCommonInterlacing
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTNormalizedTransverseSector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCasimirEmbedding
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseWignerEckartPhase
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTValidTransverseArrowheadRow
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTValidTransverseMinorRoots
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTValidTransverseSignedIndex
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInternalRowLowerGram
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherRepresentationGraph (Interlaces)
open MetricCodes.Spherical.HigherYoungAllRankGTArrowheadSchurComplement
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriSourceSignatureInjectivity
open MetricCodes.Spherical.HigherYoungMixedGapAxisProbability
open MetricCodes.Spherical.HigherYoungPenultimateRowProjectedLower

theorem normalizedNegativeSector_canonicalAxis_inner_eq_zero
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (kappa : Fin r → ℕ)
    (hmu : Interlaces lam mu)
    (hmuGram : PositiveGelfandTsetlinFischerGram (n := n) lam mu hmu)
    (row : Fin (r + 1))
    (hnu : Interlaces lam (raiseWeight mu row))
    (hnuGram : PositiveGelfandTsetlinFischerGram (n := n)
      lam (raiseWeight mu row) hnu)
    (hfinite : FiniteInterlacing n mu kappa)
    (hraise : FiniteInterlacing n (raiseWeight mu row) kappa)
    (p q : HarmonicYoungSpace (n := n) mu) :
    ⟪canonicalGelfandTsetlinAxisTensor lam mu hmu hmuGram p,
      normalizedGTTransverseNegativeSector
        lam mu kappa row hnu hnuGram hfinite hraise q⟫_ℝ = 0 := by
  change
    ⟪canonicalGelfandTsetlinAxisTensor lam mu hmu hmuGram p,
      (Real.sqrt (internalRowLowerGramScalar (raiseWeight mu row) row *
        weylEdgeRatio n mu row))⁻¹ •
        gtTransverseNegativeSector lam mu row hnu hnuGram q⟫_ℝ = 0
  rw [real_inner_smul_right, real_inner_comm,
    gtTransverseNegativeSector_axis_inner_eq_zero
      lam mu row hnu hnuGram hmu hmuGram q p, mul_zero]

theorem normalizedPositiveSector_canonicalAxis_inner_eq_zero
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu nu : Fin (r + 1) → ℕ) (row : Fin (r + 1))
    (hmunu : mu = raiseWeight nu row)
    (hmu : Interlaces lam mu)
    (hmuGram : PositiveGelfandTsetlinFischerGram (n := n) lam mu hmu)
    (hnu : Interlaces lam nu)
    (hnuGram : PositiveGelfandTsetlinFischerGram (n := n) lam nu hnu)
    (p q : HarmonicYoungSpace (n := n) mu) :
    ⟪canonicalGelfandTsetlinAxisTensor lam mu hmu hmuGram p,
      normalizedGTTransversePositiveSector
        lam mu nu row hmunu hmu hnu hnuGram q⟫_ℝ = 0 := by
  change
    ⟪canonicalGelfandTsetlinAxisTensor lam mu hmu hmuGram p,
      (Real.sqrt (internalRowLowerGramScalar mu row))⁻¹ •
        gtTransversePositiveSector lam mu nu row hmunu hnu hnuGram q⟫_ℝ = 0
  rw [real_inner_smul_right, real_inner_comm,
    gtTransversePositiveSector_axis_inner_eq_zero
      lam mu nu row hmunu hnu hnuGram hmu hmuGram q p, mul_zero]

end AllRankGTValidTransverseSectorFamily

end

section


open scoped BigOperators InnerProductSpace TensorProduct

namespace AllRankGTUnconditionalCharacteristicMinor

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAxisCompressedCharacteristicMinor
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAbsentWallCharacteristicFactor
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAdjacentCommonInterlacing
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCharacteristicMinorOfValidRoots
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent
open
  MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTNormalizedTransverseCharacteristicAnnihilation
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTNormalizedTransverseSector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTNormalizedWallCharacteristicAnnihilation
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTPresentWallSignedNodeSeparation
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTPhysicalWallAdditiveColumn
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirCrossBlock
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseEigenNodeSeparation
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseRetainedTwoBlockClosure
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseWignerEckartPhase
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTValidTransverseArrowheadRow
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTValidTransverseMinorRoots
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTValidTransverseSectorFamily
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallSectorIsometry
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherHierarchy
open MetricCodes.Spherical.HigherProjectionInstantiation
open MetricCodes.Spherical.HigherRepresentationGraph (Interlaces)
open MetricCodes.Spherical.HigherYoungActualGraphAssembly
open MetricCodes.Spherical.HigherYoungAllRankActualBoxInstantiation
open MetricCodes.Spherical.HigherYoungAllRankActualProjectedAxisCompletion
open MetricCodes.Spherical.HigherYoungAllRankGTArrowheadSchurComplement
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriSourceSignatureInjectivity
open MetricCodes.Spherical.HigherYoungPenultimateRowProjectedLower

theorem isometricSector_operator_column_of_mem_axis_sector
    {V H : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ V] [FiniteDimensional ℝ H]
    (A B : V →ₗᵢ[ℝ] H) (T : Module.End ℝ H) (d : ℝ)
    (horth : A.toLinearMap.adjoint.comp B.toLinearMap = 0)
    (hdiag : B.toLinearMap.adjoint.comp
      (T.comp B.toLinearMap) = d • LinearMap.id)
    (hclosed : ∀ p : V,
      T (B p) ∈ LinearMap.range A.toLinearMap ⊔
        LinearMap.range B.toLinearMap) :
    T.comp B.toLinearMap = d • B.toLinearMap +
      A.toLinearMap.comp
        (A.toLinearMap.adjoint.comp (T.comp B.toLinearMap)) := by
  have hAB (p : V) : A.toLinearMap.adjoint (B p) = 0 :=
    LinearMap.congr_fun horth p
  have hBA (p : V) : B.toLinearMap.adjoint (A p) = 0 := by
    have hreverse := congrArg LinearMap.adjoint horth
    simp only [LinearMap.adjoint_comp, LinearMap.adjoint_adjoint,
      map_zero] at hreverse
    exact LinearMap.congr_fun hreverse p
  apply LinearMap.ext
  intro p
  obtain ⟨u, ⟨x, rfl⟩, v, ⟨y, rfl⟩, heq⟩ :=
    Submodule.mem_sup.mp (hclosed p)
  have hx : x = A.toLinearMap.adjoint (T (B p)) := by
    have h := congrArg A.toLinearMap.adjoint heq
    change A.toLinearMap.adjoint (A x + B y) =
      A.toLinearMap.adjoint (T (B p)) at h
    rw [map_add, hAB, add_zero] at h
    have hself := LinearMap.congr_fun A.adjoint_comp_self' x
    change A.toLinearMap.adjoint (A x) = x at hself
    exact hself.symm.trans h
  have hy : y = d • p := by
    have h := congrArg B.toLinearMap.adjoint heq
    change B.toLinearMap.adjoint (A x + B y) =
      B.toLinearMap.adjoint (T (B p)) at h
    rw [map_add, hBA, zero_add] at h
    have hself := LinearMap.congr_fun B.adjoint_comp_self' y
    change B.toLinearMap.adjoint (B y) = y at hself
    rw [hself] at h
    have hdiagonal := LinearMap.congr_fun hdiag p
    change B.toLinearMap.adjoint (T (B p)) = d • p at hdiagonal
    exact h.trans hdiagonal
  change T (B p) = d • B p +
    A (A.toLinearMap.adjoint (T (B p)))
  calc
    T (B p) = A x + B y := heq.symm
    _ = A (A.toLinearMap.adjoint (T (B p))) + B (d • p) := by
      rw [hx, hy]
    _ = d • B p + A (A.toLinearMap.adjoint (T (B p))) := by
      rw [map_smul]
      module

theorem gtAxisCompressedCharacteristicMinor_eval_negativeValidNode_eq_zero
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (hfinite : FiniteInterlacing (n + 1) lam mu)
    (hn : 2 * (r + 2) + 5 ≤ n + 1)
    (row : Fin (r + 1))
    (hnu : Interlaces lam (raiseWeight mu row))
    (p q : HarmonicYoungSpace (n := n) mu) :
    (gtAxisCompressedCharacteristicMinor lam mu h hgram p q).eval
      (gtStabilizerArrowheadNode (wallShift (n + 1) (r + 1))
        (stabilizerShift (n + 1) mu) (.inr (row, false))) = 0 := by
  let kappa := gtSelectedPrefixWeight mu
  let hnuGram : PositiveGelfandTsetlinFischerGram
      (n := n) lam (raiseWeight mu row) hnu :=
    positiveGelfandTsetlinFischerGram (by omega) lam (raiseWeight mu row) hnu
  let hkappa : FiniteInterlacing n mu kappa :=
    gtSelectedPrefixWeight_finiteInterlacing mu (by omega)
      (interlaces_antitone_stabilizer h)
  let hraise : FiniteInterlacing n (raiseWeight mu row) kappa :=
    gtSelectedPrefixWeight_finiteInterlacing_raise
      mu row (by omega) (interlaces_antitone_stabilizer h)
        (interlaces_antitone_stabilizer hnu)
  let A := canonicalGelfandTsetlinAxisIsometry lam mu h hgram
  let B := normalizedGTTransverseNegativeSector
    lam mu kappa row hnu hnuGram hkappa hraise
  let T := gtRelativeCasimir (n := n + 1) lam
  let node := gtStabilizerArrowheadNode (wallShift (n + 1) (r + 1))
    (stabilizerShift (n + 1) mu) (.inr (row, false))
  have horth : A.toLinearMap.adjoint.comp B.toLinearMap = 0 := by
    apply LinearMap.ext
    intro x
    apply ext_inner_left ℝ
    intro y
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, inner_zero_right]
    rw [LinearMap.adjoint_inner_right]
    exact normalizedNegativeSector_canonicalAxis_inner_eq_zero
      lam mu kappa h hgram row hnu hnuGram hkappa hraise y x
  have hdiag : B.toLinearMap.adjoint.comp (T.comp B.toLinearMap) =
      node • LinearMap.id :=
    normalizedGTTransverseNegativeSector_relativeCasimir_adjoint_compression
      lam mu kappa row hnu hnuGram hkappa hraise
  have hclosed (x : HarmonicYoungSpace (n := n) mu) :
      T (B x) ∈ LinearMap.range A.toLinearMap ⊔
        LinearMap.range B.toLinearMap :=
    gtTransverseNegativeSector_relativeCasimir_mem_axis_sup_sector
      lam mu kappa row h hgram hnu hnuGram hkappa hraise hn x
  let K := A.toLinearMap.adjoint.comp (T.comp B.toLinearMap)
  have hcolumn : T.comp B.toLinearMap = node • B.toLinearMap +
      (canonicalGelfandTsetlinAxisTensor lam mu h hgram).comp K :=
    isometricSector_operator_column_of_mem_axis_sector
      A B T node horth hdiag hclosed
  exact gtAxisCompressedCharacteristicMinor_eval_actualPhysicalNode_eq_zero
    lam mu h hgram hfinite hn B node K
    (fun x y => normalizedNegativeSector_canonicalAxis_inner_eq_zero
      lam mu kappa h hgram row hnu hnuGram hkappa hraise x y)
    hcolumn
    (fun x => normalizedGTTransverseNegativeSector_characteristic_aeval_eq_zero
      hn lam mu kappa row hnu hnuGram hkappa hraise x)
    (negativeStabilizerNode_ne_signedAmbientNode_of_valid_raise
      lam mu hfinite row hnu)
    p q

theorem gtAxisCompressedCharacteristicMinor_eval_positiveValidNode_eq_zero
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu nu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (hfinite : FiniteInterlacing (n + 1) lam mu)
    (hn : 2 * (r + 2) + 5 ≤ n + 1)
    (row : Fin (r + 1))
    (hmunu : mu = raiseWeight nu row)
    (hnu : Interlaces lam nu)
    (p q : HarmonicYoungSpace (n := n) mu) :
    (gtAxisCompressedCharacteristicMinor lam mu h hgram p q).eval
      (gtStabilizerArrowheadNode (wallShift (n + 1) (r + 1))
        (stabilizerShift (n + 1) mu) (.inr (row, true))) = 0 := by
  let hnuGram : PositiveGelfandTsetlinFischerGram (n := n) lam nu hnu :=
    positiveGelfandTsetlinFischerGram (by omega) lam nu hnu
  let A := canonicalGelfandTsetlinAxisIsometry lam mu h hgram
  let B := normalizedGTTransversePositiveSector
    lam mu nu row hmunu h hnu hnuGram
  let T := gtRelativeCasimir (n := n + 1) lam
  let node := gtStabilizerArrowheadNode (wallShift (n + 1) (r + 1))
    (stabilizerShift (n + 1) mu) (.inr (row, true))
  have horth : A.toLinearMap.adjoint.comp B.toLinearMap = 0 := by
    apply LinearMap.ext
    intro x
    apply ext_inner_left ℝ
    intro y
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, inner_zero_right]
    rw [LinearMap.adjoint_inner_right]
    exact normalizedPositiveSector_canonicalAxis_inner_eq_zero
      lam mu nu row hmunu h hgram hnu hnuGram y x
  have hdiag : B.toLinearMap.adjoint.comp (T.comp B.toLinearMap) =
      node • LinearMap.id :=
    normalizedGTTransversePositiveSector_relativeCasimir_adjoint_compression
      lam mu nu row hmunu h hnu hnuGram
  have hclosed (x : HarmonicYoungSpace (n := n) mu) :
      T (B x) ∈ LinearMap.range A.toLinearMap ⊔
        LinearMap.range B.toLinearMap :=
    gtTransversePositiveSector_relativeCasimir_mem_axis_sup_sector
      lam mu nu row hmunu h hgram hnu hnuGram hn x
  let K := A.toLinearMap.adjoint.comp (T.comp B.toLinearMap)
  have hcolumn : T.comp B.toLinearMap = node • B.toLinearMap +
      (canonicalGelfandTsetlinAxisTensor lam mu h hgram).comp K :=
    isometricSector_operator_column_of_mem_axis_sector
      A B T node horth hdiag hclosed
  exact gtAxisCompressedCharacteristicMinor_eval_actualPhysicalNode_eq_zero
    lam mu h hgram hfinite hn B node K
    (fun x y => normalizedPositiveSector_canonicalAxis_inner_eq_zero
      lam mu nu row hmunu h hgram hnu hnuGram x y)
    hcolumn
    (fun x => normalizedGTTransversePositiveSector_characteristic_aeval_eq_zero
      hn lam mu nu row hmunu h hnu hnuGram x)
    (positiveStabilizerNode_ne_signedAmbientNode_of_valid_lower
      lam mu nu hfinite row hmunu hnu)
    p q

theorem gtAxisCompressedCharacteristicMinor_eval_wallNode_eq_zero
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (hfinite : FiniteInterlacing (n + 1) lam mu)
    (hn : 2 * (r + 2) + 5 ≤ n + 1)
    (p q : HarmonicYoungSpace (n := n) mu) :
    (gtAxisCompressedCharacteristicMinor lam mu h hgram p q).eval
      (-(wallShift (n + 1) (r + 1))) = 0 := by
  by_cases hlast : lam (Fin.last (r + 1)) = 0
  · exact gtAxisCompressedCharacteristicMinor_eval_neg_wallShift_eq_zero_of_last_eq_zero
      lam mu h hgram hfinite hlast p q
  · have hpos : 0 < lam (Fin.last (r + 1)) := Nat.pos_of_ne_zero hlast
    let hw : 2 * (r + 1) + 5 ≤ n + 1 := by omega
    let B := normalizedGTTransverseWallSector lam mu h hw hpos
    let K := gtTransverseAxisCrossBlock lam mu h hgram B.toLinearMap
    exact gtAxisCompressedCharacteristicMinor_eval_actualPhysicalNode_eq_zero
      lam mu h hgram hfinite hn B (-(wallShift (n + 1) (r + 1))) K
      (fun x y => canonicalAxis_inner_normalizedGTTransverseWallSector_eq_zero
        lam mu h hw hpos hgram x y)
      (gtRelativeCasimir_normalizedWallSector_additiveColumn
        lam mu h hgram hn hpos)
      (fun x => normalizedGTTransverseWallSector_characteristic_aeval_eq_zero
        lam mu h hw hn hpos x)
      (presentWall_ne_signedAmbientNode hfinite hpos)
      p q

theorem gtAxisCompressedCharacteristicMinor_eq_channelNumerator
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (hfinite : FiniteInterlacing (n + 1) lam mu)
    (hn : 2 * (r + 2) + 5 ≤ n + 1)
    (p q : HarmonicYoungSpace (n := n) mu) :
    gtAxisCompressedCharacteristicMinor lam mu h hgram p q =
      Polynomial.C ⟪p, q⟫_ℝ *
        channelNumeratorPolynomial (wallShift (n + 1) (r + 1))
          (stabilizerShift (n + 1) mu) := by
  apply gtAxisCompressedCharacteristicMinor_eq_channelNumerator_of_validRoots
    lam mu h hgram hfinite hn p q
  · exact gtAxisCompressedCharacteristicMinor_eval_wallNode_eq_zero
      lam mu h hgram hfinite hn p q
  · intro row hnu
    exact gtAxisCompressedCharacteristicMinor_eval_negativeValidNode_eq_zero
      lam mu h hgram hfinite hn row hnu p q
  · intro row hpos hnu
    exact gtAxisCompressedCharacteristicMinor_eval_positiveValidNode_eq_zero
      lam mu (loweredInternalYoungWeight mu row) h hgram hfinite hn row
      (raiseWeight_loweredInternalYoungWeight mu row hpos).symm hnu p q

theorem fixedLevelHierarchyCodeBound : FixedLevelHierarchyCodeBound := by
  apply fixedLevelHierarchyCodeBound_of_actualCharacteristicMinor
  intro r m n a b _ _ hn hstable low p q
  exact gtAxisCompressedCharacteristicMinor_eq_channelNumerator
    (boxSignature (m := m) a (n + 1) low)
    (Weyl.flooredWeight b (n + 1))
    (boxSignature_interlaces a b hstable low)
    (canonicalBoxPositiveFischerGram a b hstable low)
    (hstable
      ((Fintype.equivFin (RectangularVertices.Vertex (r + 1) m)).symm low))
    hn p q

end AllRankGTUnconditionalCharacteristicMinor

end

end HigherHarmonicYoung

section

open Filter Topology
open scoped Topology

namespace HigherHierarchy

open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTUnconditionalCharacteristicMinor

theorem main_general {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    (∀ {r : ℕ} {R : ℝ}
      (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ),
      Interlacing a b → s < 2 * Gamma a b → Phi a b < R →
        ∀ᶠ n : ℕ in atTop, ∀ C : SpherePacking.SphericalCode n s,
          (C.points.card : ℝ) < (2 : ℝ) ^ (R * (n : ℝ))) ∧
      sphericalCodeRate s ≤ closedHierarchyVariationalRate s :=
  main_general_of_actualCodeBound fixedLevelHierarchyCodeBound hs hs'

theorem strict_hierarchy {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    (∀ r : ℕ,
      levelRate (r + 1) s < levelRate r s ∧
        localizedLevelRate (r + 1) s < localizedLevelRate r s) ∧
      sphericalCodeRate s ≤ localizedHierarchyRate s ∧
      localizedHierarchyRate s < localizedLevelRate 1 s ∧
      localizedLevelRate 1 s < localizedRowRate s ∧
      localizedRowRate s < localizedLevelRate 0 s ∧
      localizedLevelRate 0 s = classicalLocalizedRate s :=
  strict_hierarchy_of_actualCodeBound fixedLevelHierarchyCodeBound hs hs'

end HigherHierarchy

end

end Spherical

end MetricCodes

section

open Filter Topology
open scoped Topology

namespace SpherePacking

/-- The kissing number used in the spherical-code argument. -/
def kissingNumber (n : ℕ) : ℕ∞ :=
  sphericalCodeNumber n ((1 : ℝ) / 2)

end SpherePacking

namespace MetricCodes.Johnson

theorem main_binary_theorem {δ : ℝ}
    (hδ : 0 < δ) (hhalf : δ < (1 : ℝ) / 2) :
    MetricCodes.Hamming.binaryRate δ ≤ combinedVariationalRate δ ∧
      combinedVariationalRate δ < mrrwRate δ :=
  ⟨binaryRate_le_combinedVariationalRate hδ hhalf,
    MetricCodes.MRRW.strict_mrrw2 hδ hhalf⟩

end MetricCodes.Johnson

namespace MetricCodes.Spherical.HigherHierarchy.NumericalMaximum

theorem eventually_kissingNumber_lt_published :
    ∀ᶠ n : ℕ in atTop,
      ((SpherePacking.kissingNumber n).toNat : ℝ) ≤
        (2 : ℝ) ^ ((0.39661 : ℝ) * (n : ℝ)) := by
  have hcode :=
    (MetricCodes.Spherical.HigherHierarchy.main_general
      (s := (1 : ℝ) / 2) (by norm_num) (by norm_num)).1
      (R := (0.39661 : ℝ))
      MetricCodes.Spherical.HigherHierarchy.Numerics.kissingAmbient
      MetricCodes.Spherical.HigherHierarchy.Numerics.kissingStabilizer
      MetricCodes.Spherical.HigherHierarchy.Numerics.kissing_interlacing
      (by linarith [MetricCodes.Spherical.HigherHierarchy.Numerics.kissing_spectral_certificate])
      (by linarith [MetricCodes.Spherical.HigherHierarchy.Numerics.kissing_entropy_certificate])
  filter_upwards [hcode] with n hn
  obtain ⟨C, hC⟩ :=
    SpherePacking.exists_maximal_sphericalCode (n := n) (s := (1 : ℝ) / 2)
      (by norm_num)
  have hcard : (SpherePacking.kissingNumber n).toNat = C.points.card := by
    change (SpherePacking.sphericalCodeNumber n ((1 : ℝ) / 2)).toNat = _
    rw [← hC]
    exact ENat.toNat_natCast _
  rw [hcard]
  exact (hn C).le

end MetricCodes.Spherical.HigherHierarchy.NumericalMaximum

end

end MetricCodesNoncomputable
