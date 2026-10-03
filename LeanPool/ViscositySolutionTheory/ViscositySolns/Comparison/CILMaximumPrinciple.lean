/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module


public import LeanPool.ViscositySolutionTheory.ViscositySolns.Comparison.IshiiLemma
public import LeanPool.ViscositySolutionTheory.ViscositySolns.Comparison.Neighborhoods
public import LeanPool.ViscositySolutionTheory.ViscositySolns.Comparison.SeparatedJets

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# The CIL maximum principle for quadratic test functions

This file assembles the compact localization, regularized doubled convolution,
and semiconvex matrix theorem into the CIL maximum-principle conclusion for
test functions which are represented globally by their quadratic expansion at
each base point. The coordinate quadratic penalty is the main intended
instance.
-/

@[expose] public noncomputable section

open scoped MatrixOrder

namespace ViscositySolns

variable {n : Nat}

/--
The CIL two-function maximum principle for a test function which is globally
equal to its quadratic expansion at every base point.

In quantified mathematical form, assume:

* `u` is upper semicontinuous on `C`;
* `v` is lower semicontinuous on `D`;
* the relative topologies on `C` and `D` are locally compact;
* for every base point `z = (x, y)`, the function `φ` satisfies
  `φ(w) = doubledQuadraticExpansionAt x y (φ z) (P z) (A z) w` for every
  `w`;
* each matrix `A z` is symmetric;
* `A z ≤ μ(z) [I 0; 0 I]` and `0 ≤ μ(z)`.

Then the CIL maximum-principle conclusion holds with first-order components
`blockPointLeft (P z)` and `-blockPointRight (P z)`, Hessian `A z`, and
matrix norm bound `μ(z)`.
-/
theorem CILDoubledMaximumPrincipleOn.of_global_doubledQuadraticExpansion
    (hJensen : JensenContactSetPositiveMeasureOnClosedBallTheorem (n + n))
    (hAleksandrov : AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem (n + n))
    {C D : Set (Point n)} [LocallyCompactSpace C] [LocallyCompactSpace D]
    {u v : Point n -> Real} {φ : DoubledPoint n -> Real}
    {P : DoubledPoint n -> BlockPoint n} {A : DoubledPoint n -> BlockHessian n}
    {μ : DoubledPoint n -> Real}
    (hu : UpperSemicontinuousOn u C) (hv : LowerSemicontinuousOn v D)
    (hφ :
      ∀ z : DoubledPoint n, ∀ w : DoubledPoint n,
        φ w = doubledQuadraticExpansionAt (n := n) z.1 z.2 (φ z) (P z) (A z) w)
    (hHerm : ∀ z : DoubledPoint n, (A z).IsHermitian)
    (hA : ∀ z : DoubledPoint n, A z <= μ z • blockDiagonalIdentity n)
    (hμ : ∀ z : DoubledPoint n, 0 <= μ z) :
    CILDoubledMaximumPrincipleOn C D u v φ
      (fun z : DoubledPoint n => blockPointLeft (P z))
      (fun z : DoubledPoint n => -blockPointRight (P z))
      A μ := by
  intro epsilon hepsilon x0 y0 hlocal
  rcases exists_compact_translated_product_isMaxOn_of_hasDoubledLocalMaximumOn
      (n := n) hlocal with
    ⟨K, L, hKne, hLne, hKcompact, hLcompact, h0K, h0L,
      hKnhds, hLnhds, hKsubsetC, hLsubsetD, hmax⟩
  let z0 : DoubledPoint n := (x0, y0)
  have hmaxExpansion :
      IsMaxOn
        (fun q : DoubledPoint n =>
          u q.1 - v q.2 -
            doubledQuadraticExpansionAt (n := n) x0 y0 (φ z0) (P z0) (A z0) q)
        {q : DoubledPoint n | q.1 - x0 ∈ K ∧ q.2 - y0 ∈ L}
        (x0, y0) := by
    convert hmax using 1
    ext q
    rw [hφ z0 q]
  have huK : UpperSemicontinuousOn u ((fun x : Point n => x0 + x) '' K) :=
    hu.mono hKsubsetC
  have hvL : LowerSemicontinuousOn v ((fun y : Point n => y0 + y) '' L) :=
    hv.mono hLsubsetD
  have hinv_pos : 0 < epsilon⁻¹ := inv_pos.mpr hepsilon
  have hlambda_nonneg : 0 <= epsilon⁻¹ + μ z0 := by
    linarith [hμ z0]
  have hlambda_ne : epsilon⁻¹ + μ z0 ≠ 0 := by
    have hpos : 0 < epsilon⁻¹ + μ z0 := by
      linarith [hμ z0]
    exact ne_of_gt hpos
  rcases closedSemijets_and_cilBounds_ambient_of_regularizedDoubledConvolution
      (n := n) hJensen hAleksandrov hlambda_nonneg hlambda_ne
      (C := C) (D := D) (K := K) (L := L) (u := u) (v := v)
      (x0 := x0) (y0 := y0) (φ0 := φ z0) (P := P z0) (A := A z0)
      (hHerm z0) hepsilon (hA z0) hKne hLne hKcompact hLcompact
      huK hvL h0K h0L hKsubsetC hLsubsetD hKnhds hLnhds hmaxExpansion with
    ⟨X, Y, hX, hY, hlower, hupper⟩
  exact ⟨{
    X := X
    Y := Y
    superjet_mem := hX
    subjet_mem := hY
    matrix_relation := ⟨hlower, hupper⟩
  }⟩

/--
The CIL two-function maximum principle for globally quadratic test functions
follows from the localized Aleksandrov second-differentiability theorem in
dimension `n + n`, because the localized Jensen contact-set theorem has
already been proved.
-/
theorem CILDoubledMaximumPrincipleOn.of_aleksandrov_global_doubledQuadraticExpansion
    (hAleksandrov : AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem (n + n))
    {C D : Set (Point n)} [LocallyCompactSpace C] [LocallyCompactSpace D]
    {u v : Point n -> Real} {φ : DoubledPoint n -> Real}
    {P : DoubledPoint n -> BlockPoint n} {A : DoubledPoint n -> BlockHessian n}
    {μ : DoubledPoint n -> Real}
    (hu : UpperSemicontinuousOn u C) (hv : LowerSemicontinuousOn v D)
    (hφ :
      ∀ z : DoubledPoint n, ∀ w : DoubledPoint n,
        φ w = doubledQuadraticExpansionAt (n := n) z.1 z.2 (φ z) (P z) (A z) w)
    (hHerm : ∀ z : DoubledPoint n, (A z).IsHermitian)
    (hA : ∀ z : DoubledPoint n, A z <= μ z • blockDiagonalIdentity n)
    (hμ : ∀ z : DoubledPoint n, 0 <= μ z) :
    CILDoubledMaximumPrincipleOn C D u v φ
      (fun z : DoubledPoint n => blockPointLeft (P z))
      (fun z : DoubledPoint n => -blockPointRight (P z))
      A μ :=
  CILDoubledMaximumPrincipleOn.of_global_doubledQuadraticExpansion
    (n := n)
    (JensenContactSetPositiveMeasureOnClosedBallTheorem.proof (n := n + n))
    hAleksandrov hu hv hφ hHerm hA hμ

/--
The CIL two-function maximum principle from the selected two-sided-jet theorem.

In quantified mathematical form, this is
`CILDoubledMaximumPrincipleOn.of_global_doubledQuadraticExpansion` with the
analytic input replaced by the selected two-sided-jet theorem for the compact
regularized doubled convolution.
-/
theorem CILDoubledMaximumPrincipleOn.of_selectedTwoSidedJets_global_doubledQuadraticExpansion
    (hselected : SelectedTwoSidedJetsForRegularizedDoubledConvolutionTheorem n)
    {C D : Set (Point n)} [LocallyCompactSpace C] [LocallyCompactSpace D]
    {u v : Point n -> Real} {φ : DoubledPoint n -> Real}
    {P : DoubledPoint n -> BlockPoint n} {A : DoubledPoint n -> BlockHessian n}
    {μ : DoubledPoint n -> Real}
    (hu : UpperSemicontinuousOn u C) (hv : LowerSemicontinuousOn v D)
    (hφ :
      ∀ z : DoubledPoint n, ∀ w : DoubledPoint n,
        φ w = doubledQuadraticExpansionAt (n := n) z.1 z.2 (φ z) (P z) (A z) w)
    (hHerm : ∀ z : DoubledPoint n, (A z).IsHermitian)
    (hA : ∀ z : DoubledPoint n, A z <= μ z • blockDiagonalIdentity n)
    (hμ : ∀ z : DoubledPoint n, 0 <= μ z) :
    CILDoubledMaximumPrincipleOn C D u v φ
      (fun z : DoubledPoint n => blockPointLeft (P z))
      (fun z : DoubledPoint n => -blockPointRight (P z))
      A μ := by
  intro epsilon hepsilon x0 y0 hlocal
  rcases exists_compact_translated_product_isMaxOn_of_hasDoubledLocalMaximumOn
      (n := n) hlocal with
    ⟨K, L, hKne, hLne, hKcompact, hLcompact, h0K, h0L,
      hKnhds, hLnhds, hKsubsetC, hLsubsetD, hmax⟩
  let z0 : DoubledPoint n := (x0, y0)
  have hmaxExpansion :
      IsMaxOn
        (fun q : DoubledPoint n =>
          u q.1 - v q.2 -
            doubledQuadraticExpansionAt (n := n) x0 y0 (φ z0) (P z0) (A z0) q)
        {q : DoubledPoint n | q.1 - x0 ∈ K ∧ q.2 - y0 ∈ L}
        (x0, y0) := by
    convert hmax using 1
    ext q
    rw [hφ z0 q]
  have huK : UpperSemicontinuousOn u ((fun x : Point n => x0 + x) '' K) :=
    hu.mono hKsubsetC
  have hvL : LowerSemicontinuousOn v ((fun y : Point n => y0 + y) '' L) :=
    hv.mono hLsubsetD
  have hinv_pos : 0 < epsilon⁻¹ := inv_pos.mpr hepsilon
  have hlambda_nonneg : 0 <= epsilon⁻¹ + μ z0 := by
    linarith [hμ z0]
  have hlambda_ne : epsilon⁻¹ + μ z0 ≠ 0 := by
    have hpos : 0 < epsilon⁻¹ + μ z0 := by
      linarith [hμ z0]
    exact ne_of_gt hpos
  rcases closedSemijets_and_cilBounds_ambient_of_selectedTwoSidedJets
      (n := n) hselected hlambda_nonneg hlambda_ne
      (C := C) (D := D) (K := K) (L := L) (u := u) (v := v)
      (x0 := x0) (y0 := y0) (φ0 := φ z0) (P := P z0) (A := A z0)
      (hHerm z0) hepsilon (hA z0) hKne hLne hKcompact hLcompact
      huK hvL h0K h0L hKsubsetC hLsubsetD hKnhds hLnhds hmaxExpansion with
    ⟨X, Y, hX, hY, hlower, hupper⟩
  exact ⟨{
    X := X
    Y := Y
    superjet_mem := hX
    subjet_mem := hY
    matrix_relation := ⟨hlower, hupper⟩
  }⟩

/--
The coordinate quadratic penalty is equal to its quadratic expansion at every
base point.

In quantified mathematical form, for every `α`, every base point `z`, and
every point `w`,

`quadraticPenalty α w.1 w.2`

is equal to the quadratic polynomial at `w` with value
`quadraticPenalty α z.1 z.2`, first derivative
`[αI -αI; -αI αI] (z.1, z.2)`, and Hessian
`[αI -αI; -αI αI]`.
-/
theorem quadraticPenalty_eq_doubledQuadraticExpansionAt
    (α : Real) (z w : DoubledPoint n) :
    quadraticPenalty α w.1 w.2 =
      doubledQuadraticExpansionAt (n := n) z.1 z.2
        (quadraticPenalty α z.1 z.2)
        (Matrix.mulVec (comparisonPenaltyBlock (n := n) α) (doubledPointToBlockPoint z))
        (comparisonPenaltyBlock (n := n) α) w := by
  let A : BlockHessian n := comparisonPenaltyBlock (n := n) α
  let zBlock : BlockPoint n := doubledPointToBlockPoint z
  let hBlock : BlockPoint n := doubledPointToBlockPoint (w.1 - z.1, w.2 - z.2)
  have hHerm : A.IsHermitian := by
    have hαI : (α • (1 : Hessian n)).IsHermitian :=
      Matrix.isHermitian_one.smul (IsSelfAdjoint.all α)
    have hnegαI : ((-α) • (1 : Hessian n)).IsHermitian :=
      Matrix.isHermitian_one.smul (IsSelfAdjoint.all (-α))
    exact Matrix.IsHermitian.fromBlocks hαI hnegαI hαI
  have hsum : zBlock + hBlock = doubledPointToBlockPoint w := by
    ext i
    cases i <;> simp [zBlock, hBlock, doubledPointToBlockPoint]
  calc
    quadraticPenalty α w.1 w.2 =
        blockQuadraticModel A (doubledPointToBlockPoint w) := by
          rw [blockQuadraticModel_comparisonPenaltyBlock_doubledPoint]
    _ = blockQuadraticModel A (zBlock + hBlock) := by rw [hsum]
    _ = blockQuadraticModel A zBlock + dotProduct (Matrix.mulVec A zBlock) hBlock +
          blockQuadraticModel A hBlock := by
          exact blockQuadraticModel_add hHerm zBlock hBlock
    _ =
        doubledQuadraticExpansionAt (n := n) z.1 z.2
          (quadraticPenalty α z.1 z.2)
          (Matrix.mulVec (comparisonPenaltyBlock (n := n) α) (doubledPointToBlockPoint z))
          (comparisonPenaltyBlock (n := n) α) w := by
          rw [blockQuadraticModel_comparisonPenaltyBlock_doubledPoint (n := n) α z]
          simp [doubledQuadraticExpansionAt, A, zBlock, hBlock]

/--
The quadratic-penalty Ishii lemma follows from the localized Jensen and
Aleksandrov analytic inputs.

In quantified mathematical form, assume `u` is upper semicontinuous on `C`,
`v` is lower semicontinuous on `D`, and the relative topologies on `C` and
`D` are locally compact. If the localized Jensen contact-set theorem and the
localized Aleksandrov second-differentiability theorem are available in
dimension `n + n`, then for every `α > 0` and every local maximum point of

`(x, y) ↦ u(x) - v(y) - (α / 2) * ∑ i, (x i - y i)^2`

relative to `C × D`, the usual quadratic-penalty Ishii conclusion holds.
-/
theorem QuadraticPenaltyIshiiLemmaOn.of_localized_jensen_aleksandrov
    (hJensen : JensenContactSetPositiveMeasureOnClosedBallTheorem (n + n))
    (hAleksandrov : AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem (n + n))
    {C D : Set (Point n)} [LocallyCompactSpace C] [LocallyCompactSpace D]
    {u v : Point n -> Real}
    (hu : UpperSemicontinuousOn u C) (hv : LowerSemicontinuousOn v D) :
    QuadraticPenaltyIshiiLemmaOn C D u v := by
  apply QuadraticPenaltyIshiiLemmaOn.of_quadraticPenaltyCILDoubledMaximumPrinciple
  intro α hα
  have hα_nonneg : 0 <= α := le_of_lt hα
  have hCIL :
      CILDoubledMaximumPrincipleOn C D u v
        (fun q : DoubledPoint n => quadraticPenalty α q.1 q.2)
        (fun z : DoubledPoint n =>
          blockPointLeft
            (Matrix.mulVec (comparisonPenaltyBlock (n := n) α) (doubledPointToBlockPoint z)))
        (fun z : DoubledPoint n =>
          -blockPointRight
            (Matrix.mulVec (comparisonPenaltyBlock (n := n) α) (doubledPointToBlockPoint z)))
        (fun _z : DoubledPoint n => comparisonPenaltyBlock (n := n) α)
        (fun _z : DoubledPoint n => 2 * α) :=
    CILDoubledMaximumPrincipleOn.of_global_doubledQuadraticExpansion
      (n := n) hJensen hAleksandrov hu hv
      (P := fun z : DoubledPoint n =>
        Matrix.mulVec (comparisonPenaltyBlock (n := n) α) (doubledPointToBlockPoint z))
      (A := fun _z : DoubledPoint n => comparisonPenaltyBlock (n := n) α)
      (μ := fun _z : DoubledPoint n => 2 * α)
      (fun z w => quadraticPenalty_eq_doubledQuadraticExpansionAt (n := n) α z w)
      (fun _z => by
        have hαI : (α • (1 : Hessian n)).IsHermitian :=
          Matrix.isHermitian_one.smul (IsSelfAdjoint.all α)
        have hnegαI : ((-α) • (1 : Hessian n)).IsHermitian :=
          Matrix.isHermitian_one.smul (IsSelfAdjoint.all (-α))
        exact Matrix.IsHermitian.fromBlocks hαI hnegαI hαI)
      (fun _z => comparisonPenaltyBlock_le_two_smul_blockDiagonalIdentity
        (n := n) hα_nonneg)
      (fun _z => by linarith)
  simpa [blockPointLeft_comparisonPenaltyBlock_mulVec_doubledPoint,
    blockPointRight_comparisonPenaltyBlock_mulVec_doubledPoint] using hCIL

/--
The quadratic-penalty Ishii lemma follows from the localized Aleksandrov
second-differentiability theorem in dimension `n + n`, because the localized
Jensen contact-set theorem has already been proved.
-/
theorem QuadraticPenaltyIshiiLemmaOn.of_aleksandrov
    (hAleksandrov : AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem (n + n))
    {C D : Set (Point n)} [LocallyCompactSpace C] [LocallyCompactSpace D]
    {u v : Point n -> Real}
    (hu : UpperSemicontinuousOn u C) (hv : LowerSemicontinuousOn v D) :
    QuadraticPenaltyIshiiLemmaOn C D u v :=
  QuadraticPenaltyIshiiLemmaOn.of_localized_jensen_aleksandrov
    (n := n)
    (JensenContactSetPositiveMeasureOnClosedBallTheorem.proof (n := n + n))
    hAleksandrov hu hv

/-- The quadratic-penalty Ishii lemma with the analytic inputs discharged. -/
theorem QuadraticPenaltyIshiiLemmaOn.proof
    {C D : Set (Point n)} [LocallyCompactSpace C] [LocallyCompactSpace D]
    {u v : Point n → ℝ}
    (hu : UpperSemicontinuousOn u C) (hv : LowerSemicontinuousOn v D) :
    QuadraticPenaltyIshiiLemmaOn C D u v :=
  QuadraticPenaltyIshiiLemmaOn.of_aleksandrov
    (AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem.proof_external (n + n)) hu hv

/--
The quadratic-penalty Ishii lemma follows from the selected two-sided-jet
theorem for compact regularized doubled convolutions.

In quantified mathematical form, assume `u` is upper semicontinuous on `C`,
`v` is lower semicontinuous on `D`, and the relative topologies on `C` and
`D` are locally compact. If
`SelectedTwoSidedJetsForRegularizedDoubledConvolutionTheorem n` holds, then
for every `α > 0` and every local maximum point of

`(x, y) ↦ u(x) - v(y) - (α / 2) * ∑ i, (x i - y i)^2`

relative to `C × D`, the usual quadratic-penalty Ishii conclusion holds.
-/
theorem QuadraticPenaltyIshiiLemmaOn.of_selectedTwoSidedJets
    (hselected : SelectedTwoSidedJetsForRegularizedDoubledConvolutionTheorem n)
    {C D : Set (Point n)} [LocallyCompactSpace C] [LocallyCompactSpace D]
    {u v : Point n -> Real}
    (hu : UpperSemicontinuousOn u C) (hv : LowerSemicontinuousOn v D) :
    QuadraticPenaltyIshiiLemmaOn C D u v := by
  apply QuadraticPenaltyIshiiLemmaOn.of_quadraticPenaltyCILDoubledMaximumPrinciple
  intro α hα
  have hα_nonneg : 0 <= α := le_of_lt hα
  have hCIL :
      CILDoubledMaximumPrincipleOn C D u v
        (fun q : DoubledPoint n => quadraticPenalty α q.1 q.2)
        (fun z : DoubledPoint n =>
          blockPointLeft
            (Matrix.mulVec (comparisonPenaltyBlock (n := n) α) (doubledPointToBlockPoint z)))
        (fun z : DoubledPoint n =>
          -blockPointRight
            (Matrix.mulVec (comparisonPenaltyBlock (n := n) α) (doubledPointToBlockPoint z)))
        (fun _z : DoubledPoint n => comparisonPenaltyBlock (n := n) α)
        (fun _z : DoubledPoint n => 2 * α) :=
    CILDoubledMaximumPrincipleOn.of_selectedTwoSidedJets_global_doubledQuadraticExpansion
      (n := n) hselected hu hv
      (P := fun z : DoubledPoint n =>
        Matrix.mulVec (comparisonPenaltyBlock (n := n) α) (doubledPointToBlockPoint z))
      (A := fun _z : DoubledPoint n => comparisonPenaltyBlock (n := n) α)
      (μ := fun _z : DoubledPoint n => 2 * α)
      (fun z w => quadraticPenalty_eq_doubledQuadraticExpansionAt (n := n) α z w)
      (fun _z => by
        have hαI : (α • (1 : Hessian n)).IsHermitian :=
          Matrix.isHermitian_one.smul (IsSelfAdjoint.all α)
        have hnegαI : ((-α) • (1 : Hessian n)).IsHermitian :=
          Matrix.isHermitian_one.smul (IsSelfAdjoint.all (-α))
        exact Matrix.IsHermitian.fromBlocks hαI hnegαI hαI)
      (fun _z => comparisonPenaltyBlock_le_two_smul_blockDiagonalIdentity
        (n := n) hα_nonneg)
      (fun _z => by linarith)
  simpa [blockPointLeft_comparisonPenaltyBlock_mulVec_doubledPoint,
    blockPointRight_comparisonPenaltyBlock_mulVec_doubledPoint] using hCIL

end ViscositySolns
