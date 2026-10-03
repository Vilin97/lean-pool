/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Comparison.SeparatedJets.BlockBounds

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Second-order jets of separated functions (CilBounds)

Part of the development recording the ordinary two-sided jet consequences of
writing a function on `R^n × R^n` as a separated difference. Split from
`SeparatedJets.lean`; see the umbrella module docstring.
-/

@[expose] public noncomputable section

open scoped MatrixOrder

namespace ViscositySolns

variable {n : Nat}

/--
Closed semijets for the translated affine-normalized functions with the CIL
matrix bounds.

In quantified mathematical form, suppose that `A` is symmetric, `ε > 0`,
`A ≤ μ [I 0; 0 I]`, `0 ≤ ε⁻¹ + μ`, and `ε⁻¹ + μ ≠ 0`. If `(x0, y0)` is a
maximum point on the translated compact product of

`u(x) - v(y) - doubledQuadraticExpansionAt(x0, y0, φ0, P, A)(x, y)`,

then there exist matrices `X` and `Y` such that

`(0, X) ∈ \overline J^{2,+}_K u_norm(0)`,

`(0, Y) ∈ \overline J^{2,-}_L v_norm(0)`,

and

`-(ε⁻¹ + μ)[I 0; 0 I] ≤ [X 0; 0 -Y] ≤ A + εA²`.
-/
theorem closedSemijets_and_cilBounds_original_of_regularizedDoubledConvolution_normalized
    (hJensen : JensenContactSetPositiveMeasureOnClosedBallTheorem (n + n))
    (hAleksandrov : AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem (n + n))
    {epsilon mu : Real}
    (hlambda_nonneg : 0 <= epsilon⁻¹ + mu)
    (hlambda_ne : epsilon⁻¹ + mu ≠ 0)
    {K L : Set (Point n)} {u v : Point n -> Real}
    {x0 y0 : Point n} {φ0 : Real} {P : BlockPoint n} {A : BlockHessian n}
    (hHerm : A.IsHermitian) (hepsilon : 0 < epsilon)
    (hA : A <= mu • blockDiagonalIdentity n)
    (hKne : K.Nonempty) (hLne : L.Nonempty)
    (hKcompact : IsCompact K) (hLcompact : IsCompact L)
    (hu : UpperSemicontinuousOn u ((fun x : Point n => x0 + x) '' K))
    (hv : LowerSemicontinuousOn v ((fun y : Point n => y0 + y) '' L))
    (h0K : (0 : Point n) ∈ K) (h0L : (0 : Point n) ∈ L)
    (hmax : IsMaxOn
      (fun q : DoubledPoint n =>
        u q.1 - v q.2 - doubledQuadraticExpansionAt (n := n) x0 y0 φ0 P A q)
      {q : DoubledPoint n | q.1 - x0 ∈ K ∧ q.2 - y0 ∈ L}
      (x0, y0)) :
    ∃ X Y : Hessian n,
      ({ gradient := 0, hessian := X } : Jet n) ∈
        ClosedSuperjet K (normalizedLeftOfBlockGradient (n := n) u x0 P) 0 ∧
      ({ gradient := 0, hessian := Y } : Jet n) ∈
        ClosedSubjet L (normalizedRightOfBlockGradient (n := n) v y0 P) 0 ∧
      (-(epsilon⁻¹ + mu)) • blockDiagonalIdentity n <=
        comparisonBlockDiagonal X Y ∧
      comparisonBlockDiagonal X Y <= A + epsilon • (A * A) := by
  let uNorm : Point n -> Real := normalizedLeftOfBlockGradient (n := n) u x0 P
  let vNorm : Point n -> Real := normalizedRightOfBlockGradient (n := n) v y0 P
  let lambda : Real := epsilon⁻¹ + mu
  let B : BlockHessian n := A + epsilon • (A * A)
  have huNorm : UpperSemicontinuousOn uNorm K :=
    upperSemicontinuousOn_normalizedLeftOfBlockGradient (n := n) hu
  have hvNorm : LowerSemicontinuousOn vNorm L :=
    lowerSemicontinuousOn_normalizedRightOfBlockGradient (n := n) hv
  have hAAHerm : (A * A).IsHermitian := by
    have htranspose : A.transpose = A := by
      ext i j
      simpa using hHerm.apply i j
    have h := Matrix.isHermitian_mul_conjTranspose_self A
    simpa [htranspose] using h
  have hBHerm : B.IsHermitian :=
    hHerm.add (hAAHerm.smul (IsSelfAdjoint.all epsilon))
  have hmaxReg :
      IsMaxOn
        (fun ξ : BlockPoint n =>
          regularizedDoubledConvolution (n := n) lambda K L uNorm vNorm ξ -
            blockQuadraticModel B ξ)
        Set.univ 0 := by
    simpa [uNorm, vNorm, lambda, B] using
      isMaxOn_regularizedDoubledConvolution_normalized_sub_cilQuadratic_of_translated_mem_zero
        (n := n) (epsilon := epsilon) (mu := mu) (K := K) (L := L)
        (u := u) (v := v) (x0 := x0) (y0 := y0) (φ0 := φ0) (P := P) (A := A)
        hHerm hepsilon hA hKne hLne hKcompact hLcompact hu hv h0K h0L hmax
  simpa [uNorm, vNorm, lambda, B] using
    closedSemijets_and_blockBounds_original_of_regularizedDoubledConvolution_max
      (n := n) hJensen hAleksandrov hlambda_nonneg hlambda_ne
      hKne hLne hKcompact hLcompact huNorm hvNorm hBHerm hmaxReg

/--
Closed semijets for the translated affine-normalized functions with the CIL
matrix bounds, from the selected two-sided-jet theorem.
-/
theorem closedSemijets_and_cilBounds_original_of_selectedTwoSidedJets_normalized
    (hselected : SelectedTwoSidedJetsForRegularizedDoubledConvolutionTheorem n)
    {epsilon mu : Real}
    (hlambda_nonneg : 0 <= epsilon⁻¹ + mu)
    (hlambda_ne : epsilon⁻¹ + mu ≠ 0)
    {K L : Set (Point n)} {u v : Point n -> Real}
    {x0 y0 : Point n} {φ0 : Real} {P : BlockPoint n} {A : BlockHessian n}
    (hHerm : A.IsHermitian) (hepsilon : 0 < epsilon)
    (hA : A <= mu • blockDiagonalIdentity n)
    (hKne : K.Nonempty) (hLne : L.Nonempty)
    (hKcompact : IsCompact K) (hLcompact : IsCompact L)
    (hu : UpperSemicontinuousOn u ((fun x : Point n => x0 + x) '' K))
    (hv : LowerSemicontinuousOn v ((fun y : Point n => y0 + y) '' L))
    (h0K : (0 : Point n) ∈ K) (h0L : (0 : Point n) ∈ L)
    (hmax : IsMaxOn
      (fun q : DoubledPoint n =>
        u q.1 - v q.2 - doubledQuadraticExpansionAt (n := n) x0 y0 φ0 P A q)
      {q : DoubledPoint n | q.1 - x0 ∈ K ∧ q.2 - y0 ∈ L}
      (x0, y0)) :
    ∃ X Y : Hessian n,
      ({ gradient := 0, hessian := X } : Jet n) ∈
        ClosedSuperjet K (normalizedLeftOfBlockGradient (n := n) u x0 P) 0 ∧
      ({ gradient := 0, hessian := Y } : Jet n) ∈
        ClosedSubjet L (normalizedRightOfBlockGradient (n := n) v y0 P) 0 ∧
      (-(epsilon⁻¹ + mu)) • blockDiagonalIdentity n <=
        comparisonBlockDiagonal X Y ∧
      comparisonBlockDiagonal X Y <= A + epsilon • (A * A) := by
  let uNorm : Point n -> Real := normalizedLeftOfBlockGradient (n := n) u x0 P
  let vNorm : Point n -> Real := normalizedRightOfBlockGradient (n := n) v y0 P
  let lambda : Real := epsilon⁻¹ + mu
  let B : BlockHessian n := A + epsilon • (A * A)
  have huNorm : UpperSemicontinuousOn uNorm K :=
    upperSemicontinuousOn_normalizedLeftOfBlockGradient (n := n) hu
  have hvNorm : LowerSemicontinuousOn vNorm L :=
    lowerSemicontinuousOn_normalizedRightOfBlockGradient (n := n) hv
  have hAAHerm : (A * A).IsHermitian := by
    have htranspose : A.transpose = A := by
      ext i j
      simpa using hHerm.apply i j
    have h := Matrix.isHermitian_mul_conjTranspose_self A
    simpa [htranspose] using h
  have hBHerm : B.IsHermitian :=
    hHerm.add (hAAHerm.smul (IsSelfAdjoint.all epsilon))
  have hmaxReg :
      IsMaxOn
        (fun ξ : BlockPoint n =>
          regularizedDoubledConvolution (n := n) lambda K L uNorm vNorm ξ -
            blockQuadraticModel B ξ)
        Set.univ 0 := by
    simpa [uNorm, vNorm, lambda, B] using
      isMaxOn_regularizedDoubledConvolution_normalized_sub_cilQuadratic_of_translated_mem_zero
        (n := n) (epsilon := epsilon) (mu := mu) (K := K) (L := L)
        (u := u) (v := v) (x0 := x0) (y0 := y0) (φ0 := φ0) (P := P) (A := A)
        hHerm hepsilon hA hKne hLne hKcompact hLcompact hu hv h0K h0L hmax
  simpa [uNorm, vNorm, lambda, B] using
    closedSemijets_and_blockBounds_original_of_selectedTwoSidedJets
      (n := n) hselected hlambda_nonneg hlambda_ne
      hKne hLne hKcompact hLcompact huNorm hvNorm hBHerm hmaxReg

/--
Closed semijets for the original functions on translated compact domains with
the CIL matrix bounds.

In quantified mathematical form, under the hypotheses of
`closedSemijets_and_cilBounds_original_of_regularizedDoubledConvolution_normalized`,
there exist matrices `X` and `Y` such that

`(P_x, X) ∈ \overline J^{2,+}_{x0+K} u(x0)`,

`(-P_y, Y) ∈ \overline J^{2,-}_{y0+L} v(y0)`,

and

`-(ε⁻¹ + μ)[I 0; 0 I] ≤ [X 0; 0 -Y] ≤ A + εA²`.
-/
theorem closedSemijets_and_cilBounds_translated_of_regularizedDoubledConvolution
    (hJensen : JensenContactSetPositiveMeasureOnClosedBallTheorem (n + n))
    (hAleksandrov : AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem (n + n))
    {epsilon mu : Real}
    (hlambda_nonneg : 0 <= epsilon⁻¹ + mu)
    (hlambda_ne : epsilon⁻¹ + mu ≠ 0)
    {K L : Set (Point n)} {u v : Point n -> Real}
    {x0 y0 : Point n} {φ0 : Real} {P : BlockPoint n} {A : BlockHessian n}
    (hHerm : A.IsHermitian) (hepsilon : 0 < epsilon)
    (hA : A <= mu • blockDiagonalIdentity n)
    (hKne : K.Nonempty) (hLne : L.Nonempty)
    (hKcompact : IsCompact K) (hLcompact : IsCompact L)
    (hu : UpperSemicontinuousOn u ((fun x : Point n => x0 + x) '' K))
    (hv : LowerSemicontinuousOn v ((fun y : Point n => y0 + y) '' L))
    (h0K : (0 : Point n) ∈ K) (h0L : (0 : Point n) ∈ L)
    (hmax : IsMaxOn
      (fun q : DoubledPoint n =>
        u q.1 - v q.2 - doubledQuadraticExpansionAt (n := n) x0 y0 φ0 P A q)
      {q : DoubledPoint n | q.1 - x0 ∈ K ∧ q.2 - y0 ∈ L}
      (x0, y0)) :
    ∃ X Y : Hessian n,
      ({ gradient := blockPointLeft P, hessian := X } : Jet n) ∈
        ClosedSuperjet ((fun x : Point n => x0 + x) '' K) u x0 ∧
      ({ gradient := -blockPointRight P, hessian := Y } : Jet n) ∈
        ClosedSubjet ((fun y : Point n => y0 + y) '' L) v y0 ∧
      (-(epsilon⁻¹ + mu)) • blockDiagonalIdentity n <=
        comparisonBlockDiagonal X Y ∧
      comparisonBlockDiagonal X Y <= A + epsilon • (A * A) := by
  rcases closedSemijets_and_cilBounds_original_of_regularizedDoubledConvolution_normalized
      (n := n) hJensen hAleksandrov hlambda_nonneg hlambda_ne
      hHerm hepsilon hA hKne hLne hKcompact hLcompact hu hv h0K h0L hmax with
    ⟨X, Y, hX, hY, hlower, hupper⟩
  exact ⟨X, Y,
    closedSuperjet_of_closedSuperjet_normalizedLeftOfBlockGradient (n := n) hX,
    closedSubjet_of_closedSubjet_normalizedRightOfBlockGradient (n := n) hY,
    hlower, hupper⟩

/--
Closed semijets for the original functions on translated compact domains with
the CIL matrix bounds, from the selected two-sided-jet theorem.
-/
theorem closedSemijets_and_cilBounds_translated_of_selectedTwoSidedJets
    (hselected : SelectedTwoSidedJetsForRegularizedDoubledConvolutionTheorem n)
    {epsilon mu : Real}
    (hlambda_nonneg : 0 <= epsilon⁻¹ + mu)
    (hlambda_ne : epsilon⁻¹ + mu ≠ 0)
    {K L : Set (Point n)} {u v : Point n -> Real}
    {x0 y0 : Point n} {φ0 : Real} {P : BlockPoint n} {A : BlockHessian n}
    (hHerm : A.IsHermitian) (hepsilon : 0 < epsilon)
    (hA : A <= mu • blockDiagonalIdentity n)
    (hKne : K.Nonempty) (hLne : L.Nonempty)
    (hKcompact : IsCompact K) (hLcompact : IsCompact L)
    (hu : UpperSemicontinuousOn u ((fun x : Point n => x0 + x) '' K))
    (hv : LowerSemicontinuousOn v ((fun y : Point n => y0 + y) '' L))
    (h0K : (0 : Point n) ∈ K) (h0L : (0 : Point n) ∈ L)
    (hmax : IsMaxOn
      (fun q : DoubledPoint n =>
        u q.1 - v q.2 - doubledQuadraticExpansionAt (n := n) x0 y0 φ0 P A q)
      {q : DoubledPoint n | q.1 - x0 ∈ K ∧ q.2 - y0 ∈ L}
      (x0, y0)) :
    ∃ X Y : Hessian n,
      ({ gradient := blockPointLeft P, hessian := X } : Jet n) ∈
        ClosedSuperjet ((fun x : Point n => x0 + x) '' K) u x0 ∧
      ({ gradient := -blockPointRight P, hessian := Y } : Jet n) ∈
        ClosedSubjet ((fun y : Point n => y0 + y) '' L) v y0 ∧
      (-(epsilon⁻¹ + mu)) • blockDiagonalIdentity n <=
        comparisonBlockDiagonal X Y ∧
      comparisonBlockDiagonal X Y <= A + epsilon • (A * A) := by
  rcases closedSemijets_and_cilBounds_original_of_selectedTwoSidedJets_normalized
      (n := n) hselected hlambda_nonneg hlambda_ne
      hHerm hepsilon hA hKne hLne hKcompact hLcompact hu hv h0K h0L hmax with
    ⟨X, Y, hX, hY, hlower, hupper⟩
  exact ⟨X, Y,
    closedSuperjet_of_closedSuperjet_normalizedLeftOfBlockGradient (n := n) hX,
    closedSubjet_of_closedSubjet_normalizedRightOfBlockGradient (n := n) hY,
    hlower, hupper⟩

/--
Closed semijets for the original functions on the ambient domains with the CIL
matrix bounds.

In quantified mathematical form, assume the hypotheses of
`closedSemijets_and_cilBounds_translated_of_regularizedDoubledConvolution`.
Assume additionally that `{x0 + x | x ∈ K}` is a subset of `C` and is a
relative neighborhood of `x0` in `C`, and that `{y0 + y | y ∈ L}` is a subset
of `D` and is a relative neighborhood of `y0` in `D`. Then there exist
matrices `X` and `Y` such that

`(P_x, X) ∈ \overline J^{2,+}_C u(x0)`,

`(-P_y, Y) ∈ \overline J^{2,-}_D v(y0)`,

and

`-(ε⁻¹ + μ)[I 0; 0 I] ≤ [X 0; 0 -Y] ≤ A + εA²`.
-/
theorem closedSemijets_and_cilBounds_ambient_of_regularizedDoubledConvolution
    (hJensen : JensenContactSetPositiveMeasureOnClosedBallTheorem (n + n))
    (hAleksandrov : AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem (n + n))
    {epsilon mu : Real}
    (hlambda_nonneg : 0 <= epsilon⁻¹ + mu)
    (hlambda_ne : epsilon⁻¹ + mu ≠ 0)
    {C D K L : Set (Point n)} {u v : Point n -> Real}
    {x0 y0 : Point n} {φ0 : Real} {P : BlockPoint n} {A : BlockHessian n}
    (hHerm : A.IsHermitian) (hepsilon : 0 < epsilon)
    (hA : A <= mu • blockDiagonalIdentity n)
    (hKne : K.Nonempty) (hLne : L.Nonempty)
    (hKcompact : IsCompact K) (hLcompact : IsCompact L)
    (hu : UpperSemicontinuousOn u ((fun x : Point n => x0 + x) '' K))
    (hv : LowerSemicontinuousOn v ((fun y : Point n => y0 + y) '' L))
    (h0K : (0 : Point n) ∈ K) (h0L : (0 : Point n) ∈ L)
    (hKsubsetC : ((fun x : Point n => x0 + x) '' K) ⊆ C)
    (hLsubsetD : ((fun y : Point n => y0 + y) '' L) ⊆ D)
    (hKnhds : ((fun x : Point n => x0 + x) '' K) ∈ nhdsWithin x0 C)
    (hLnhds : ((fun y : Point n => y0 + y) '' L) ∈ nhdsWithin y0 D)
    (hmax : IsMaxOn
      (fun q : DoubledPoint n =>
        u q.1 - v q.2 - doubledQuadraticExpansionAt (n := n) x0 y0 φ0 P A q)
      {q : DoubledPoint n | q.1 - x0 ∈ K ∧ q.2 - y0 ∈ L}
      (x0, y0)) :
    ∃ X Y : Hessian n,
      ({ gradient := blockPointLeft P, hessian := X } : Jet n) ∈
        ClosedSuperjet C u x0 ∧
      ({ gradient := -blockPointRight P, hessian := Y } : Jet n) ∈
        ClosedSubjet D v y0 ∧
      (-(epsilon⁻¹ + mu)) • blockDiagonalIdentity n <=
        comparisonBlockDiagonal X Y ∧
      comparisonBlockDiagonal X Y <= A + epsilon • (A * A) := by
  rcases closedSemijets_and_cilBounds_translated_of_regularizedDoubledConvolution
      (n := n) hJensen hAleksandrov hlambda_nonneg hlambda_ne hHerm hepsilon hA
      hKne hLne hKcompact hLcompact hu hv h0K h0L hmax with
    ⟨X, Y, hX, hY, hlower, hupper⟩
  exact ⟨X, Y,
    closedSuperjet_of_closedSuperjet_of_mem_nhdsWithin hKsubsetC hKnhds hX,
    closedSubjet_of_closedSubjet_of_mem_nhdsWithin hLsubsetD hLnhds hY,
    hlower, hupper⟩

/--
Closed semijets for the original functions on the ambient domains with the CIL
matrix bounds, from the selected two-sided-jet theorem.
-/
theorem closedSemijets_and_cilBounds_ambient_of_selectedTwoSidedJets
    (hselected : SelectedTwoSidedJetsForRegularizedDoubledConvolutionTheorem n)
    {epsilon mu : Real}
    (hlambda_nonneg : 0 <= epsilon⁻¹ + mu)
    (hlambda_ne : epsilon⁻¹ + mu ≠ 0)
    {C D K L : Set (Point n)} {u v : Point n -> Real}
    {x0 y0 : Point n} {φ0 : Real} {P : BlockPoint n} {A : BlockHessian n}
    (hHerm : A.IsHermitian) (hepsilon : 0 < epsilon)
    (hA : A <= mu • blockDiagonalIdentity n)
    (hKne : K.Nonempty) (hLne : L.Nonempty)
    (hKcompact : IsCompact K) (hLcompact : IsCompact L)
    (hu : UpperSemicontinuousOn u ((fun x : Point n => x0 + x) '' K))
    (hv : LowerSemicontinuousOn v ((fun y : Point n => y0 + y) '' L))
    (h0K : (0 : Point n) ∈ K) (h0L : (0 : Point n) ∈ L)
    (hKsubsetC : ((fun x : Point n => x0 + x) '' K) ⊆ C)
    (hLsubsetD : ((fun y : Point n => y0 + y) '' L) ⊆ D)
    (hKnhds : ((fun x : Point n => x0 + x) '' K) ∈ nhdsWithin x0 C)
    (hLnhds : ((fun y : Point n => y0 + y) '' L) ∈ nhdsWithin y0 D)
    (hmax : IsMaxOn
      (fun q : DoubledPoint n =>
        u q.1 - v q.2 - doubledQuadraticExpansionAt (n := n) x0 y0 φ0 P A q)
      {q : DoubledPoint n | q.1 - x0 ∈ K ∧ q.2 - y0 ∈ L}
      (x0, y0)) :
    ∃ X Y : Hessian n,
      ({ gradient := blockPointLeft P, hessian := X } : Jet n) ∈
        ClosedSuperjet C u x0 ∧
      ({ gradient := -blockPointRight P, hessian := Y } : Jet n) ∈
        ClosedSubjet D v y0 ∧
      (-(epsilon⁻¹ + mu)) • blockDiagonalIdentity n <=
        comparisonBlockDiagonal X Y ∧
      comparisonBlockDiagonal X Y <= A + epsilon • (A * A) := by
  rcases closedSemijets_and_cilBounds_translated_of_selectedTwoSidedJets
      (n := n) hselected hlambda_nonneg hlambda_ne hHerm hepsilon hA
      hKne hLne hKcompact hLcompact hu hv h0K h0L hmax with
    ⟨X, Y, hX, hY, hlower, hupper⟩
  exact ⟨X, Y,
    closedSuperjet_of_closedSuperjet_of_mem_nhdsWithin hKsubsetC hKnhds hX,
    closedSubjet_of_closedSubjet_of_mem_nhdsWithin hLsubsetD hLnhds hY,
    hlower, hupper⟩

/--
The zero-base specialization of
`HasSecondOrderJet.left_of_blockFunctionToPointFunction_sub_at`.
-/
theorem HasSecondOrderJet.left_of_blockFunctionToPointFunction_sub
    {G H : Point n -> Real} {p : Point (n + n)} {Z : Hessian (n + n)}
    (hJ : HasSecondOrderJet
      (blockFunctionToPointFunction (n := n)
        (fun q : BlockPoint n => G (blockPointLeft q) - H (blockPointRight q)))
      0 p Z) :
    HasSecondOrderJet G 0
      (leftPointGradient (n := n) p) (leftPointHessian (n := n) Z) := by
  simpa using
    HasSecondOrderJet.left_of_blockFunctionToPointFunction_sub_at
      (n := n) (G := G) (H := H) (z := 0) hJ

/--
The zero-base specialization of
`HasSecondOrderJet.right_of_blockFunctionToPointFunction_sub_at`.
-/
theorem HasSecondOrderJet.right_of_blockFunctionToPointFunction_sub
    {G H : Point n -> Real} {p : Point (n + n)} {Z : Hessian (n + n)}
    (hJ : HasSecondOrderJet
      (blockFunctionToPointFunction (n := n)
        (fun q : BlockPoint n => G (blockPointLeft q) - H (blockPointRight q)))
      0 p Z) :
    HasSecondOrderJet H 0
      (-rightPointGradient (n := n) p) (-rightPointHessian (n := n) Z) := by
  simpa using
    HasSecondOrderJet.right_of_blockFunctionToPointFunction_sub_at
      (n := n) (G := G) (H := H) (z := 0) hJ

/--
Apply separated-function two-sided jet splitting to every term in a sequence.

In quantified mathematical form, let `G, H : R^n -> R` and let
`F(ξ, η) = G(ξ) - H(η)`. If for every natural number `k`, the pair
`((J_k).gradient, (J_k).hessian)` is an ordinary two-sided second-order jet
of `F` at `z_k`, then for every natural number `k` the left component is an
ordinary two-sided second-order jet of `G` at the left component of `z_k`,
and the negative right component is an ordinary two-sided second-order jet of
`H` at the right component of `z_k`.
-/
theorem hasSecondOrderJet_left_right_sequence_of_blockFunctionToPointFunction_sub
    {G H : Point n -> Real} {zSeq : Nat -> Point (n + n)}
    {JSeq : Nat -> Jet (n + n)}
    (hJ : ∀ k : Nat,
      HasSecondOrderJet
        (blockFunctionToPointFunction (n := n)
          (fun q : BlockPoint n => G (blockPointLeft q) - H (blockPointRight q)))
        (zSeq k) (JSeq k).gradient (JSeq k).hessian) :
    (∀ k : Nat,
      HasSecondOrderJet G (pointLeft (n := n) (zSeq k))
        (leftPointGradient (n := n) (JSeq k).gradient)
        (leftPointHessian (n := n) (JSeq k).hessian)) ∧
    (∀ k : Nat,
      HasSecondOrderJet H (pointRight (n := n) (zSeq k))
        (-rightPointGradient (n := n) (JSeq k).gradient)
        (-rightPointHessian (n := n) (JSeq k).hessian)) := by
  constructor
  · intro k
    exact (hJ k).left_of_blockFunctionToPointFunction_sub_at
  · intro k
    exact (hJ k).right_of_blockFunctionToPointFunction_sub_at

/--
A convergent sequence of two-sided jets of a separated difference gives
closed semijets of the two component functions.

In quantified mathematical form, let `G, H : R^n -> R`, let
`F(ξ, η) = G(ξ) - H(η)`, and let `z_k -> 0` in `R^n × R^n`. Suppose that
`J_k -> J`, and suppose that for every natural number `k`,
`((J_k).gradient, (J_k).hessian)` is an ordinary two-sided second-order jet
of `F` at `z_k`. If `G` and `H` are continuous, then the left component of
`J` belongs to the closed superjet of `G` at `0`, and the negative right
component of `J` belongs to the closed subjet of `H` at `0`.
-/
theorem closedSemijets_of_tendsto_twoSidedJet_blockFunctionToPointFunction_sub
    {G H : Point n -> Real} (hG : Continuous G) (hH : Continuous H)
    {zSeq : Nat -> Point (n + n)} {JSeq : Nat -> Jet (n + n)}
    {J : Jet (n + n)}
    (hz : Filter.Tendsto zSeq Filter.atTop (nhds (0 : Point (n + n))))
    (hJtendsto : Filter.Tendsto JSeq Filter.atTop (nhds J))
    (hJ : ∀ k : Nat,
      HasSecondOrderJet
        (blockFunctionToPointFunction (n := n)
          (fun q : BlockPoint n => G (blockPointLeft q) - H (blockPointRight q)))
        (zSeq k) (JSeq k).gradient (JSeq k).hessian) :
    leftPointJet (n := n) J ∈ ClosedSuperjet Set.univ G 0 ∧
      (rightPointJet (n := n) J).neg ∈ ClosedSubjet Set.univ H 0 := by
  have hsplit :=
    hasSecondOrderJet_left_right_sequence_of_blockFunctionToPointFunction_sub
      (n := n) (G := G) (H := H) (zSeq := zSeq) (JSeq := JSeq) hJ
  have hzLeft :
      Filter.Tendsto (fun k : Nat => pointLeft (n := n) (zSeq k))
        Filter.atTop (nhds (0 : Point n)) := by
    have hraw :=
      (continuous_pointLeft (n := n)).tendsto (0 : Point (n + n)) |>.comp hz
    rw [pointLeft_zero] at hraw
    exact hraw
  have hzRight :
      Filter.Tendsto (fun k : Nat => pointRight (n := n) (zSeq k))
        Filter.atTop (nhds (0 : Point n)) := by
    have hraw :=
      (continuous_pointRight (n := n)).tendsto (0 : Point (n + n)) |>.comp hz
    rw [pointRight_zero] at hraw
    exact hraw
  have hGvalue :
      Filter.Tendsto (fun k : Nat => G (pointLeft (n := n) (zSeq k)))
        Filter.atTop (nhds (G 0)) :=
    hG.continuousAt.tendsto.comp hzLeft
  have hHvalue :
      Filter.Tendsto (fun k : Nat => H (pointRight (n := n) (zSeq k)))
        Filter.atTop (nhds (H 0)) :=
    hH.continuousAt.tendsto.comp hzRight
  have hleftJet :
      Filter.Tendsto (fun k : Nat => leftPointJet (n := n) (JSeq k))
        Filter.atTop (nhds (leftPointJet (n := n) J)) :=
    tendsto_leftPointJet_of_tendsto (n := n) hJtendsto
  have hrightJet :
      Filter.Tendsto (fun k : Nat => (rightPointJet (n := n) (JSeq k)).neg)
        Filter.atTop (nhds ((rightPointJet (n := n) J).neg)) :=
    tendsto_rightPointJet_neg_of_tendsto (n := n) hJtendsto
  have hleftMem :
      ∀ᶠ k : Nat in Filter.atTop,
        leftPointJet (n := n) (JSeq k) ∈
          ClosedSuperjet Set.univ G (pointLeft (n := n) (zSeq k)) :=
    Filter.Eventually.of_forall fun k => by
      have hclosed :=
        superjet_subset_closedSuperjet
          (C := Set.univ) (u := G) (x := pointLeft (n := n) (zSeq k))
          (Set.mem_univ _) (hsplit.1 k).1
      simpa [leftPointJet] using hclosed
  have hrightMem :
      ∀ᶠ k : Nat in Filter.atTop,
        (rightPointJet (n := n) (JSeq k)).neg ∈
          ClosedSubjet Set.univ H (pointRight (n := n) (zSeq k)) :=
    Filter.Eventually.of_forall fun k => by
      have hclosed :=
        subjet_subset_closedSubjet
          (C := Set.univ) (u := H) (x := pointRight (n := n) (zSeq k))
          (Set.mem_univ _) (hsplit.2 k).2
      simpa [rightPointJet, Jet.neg] using hclosed
  constructor
  · exact
      closedSuperjet_of_tendsto_closedSuperjet
        (C := Set.univ) (u := G) (x := 0) (J := leftPointJet (n := n) J)
        (xᵢ := fun k : Nat => pointLeft (n := n) (zSeq k))
        (Jᵢ := fun k : Nat => leftPointJet (n := n) (JSeq k))
        hzLeft hGvalue hleftJet hleftMem
  · exact
      closedSubjet_of_tendsto_closedSubjet
        (C := Set.univ) (u := H) (x := 0) (J := (rightPointJet (n := n) J).neg)
        (xᵢ := fun k : Nat => pointRight (n := n) (zSeq k))
        (Jᵢ := fun k : Nat => (rightPointJet (n := n) (JSeq k)).neg)
        hzRight hHvalue hrightJet hrightMem


end ViscositySolns
