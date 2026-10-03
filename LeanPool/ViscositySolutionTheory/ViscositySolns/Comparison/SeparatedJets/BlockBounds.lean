/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Analysis.SemiconvexJensen
public import LeanPool.ViscositySolutionTheory.ViscositySolns.Comparison.ProductCoordinates

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Second-order jets of separated functions (BlockBounds)

Part of the development recording the ordinary two-sided jet consequences of
writing a function on `R^n × R^n` as a separated difference. Split from
`SeparatedJets.lean`; see the umbrella module docstring.
-/

@[expose] public noncomputable section

open scoped MatrixOrder

namespace ViscositySolns

variable {n : Nat}

/--
The left component of a two-sided jet of a separated difference is a
two-sided jet of the left function.

In quantified mathematical form, let `G, H : R^n -> R`, let
`F(ξ, η) = G(ξ) - H(η)`, and suppose `(p, Z)` belongs both to the ordinary
superjet and to the ordinary subjet of `F` at `(x0, y0)`. Then the left
component of `p` and the left-left block of `Z` belong both to the ordinary
superjet and to the ordinary subjet of `G` at `x0`.
-/
theorem HasSecondOrderJet.left_of_blockFunctionToPointFunction_sub_at
    {G H : Point n -> Real} {z : Point (n + n)} {p : Point (n + n)}
    {Z : Hessian (n + n)}
    (hJ : HasSecondOrderJet
      (blockFunctionToPointFunction (n := n)
        (fun q : BlockPoint n => G (blockPointLeft q) - H (blockPointRight q)))
      z p Z) :
    HasSecondOrderJet G (pointLeft (n := n) z)
      (leftPointGradient (n := n) p) (leftPointHessian (n := n) Z) := by
  constructor
  · exact
      superjet_left_of_superjet_blockFunctionToPointFunction_sub_at
        (n := n) (G := G) (H := H) (z := z)
        (J := ({ gradient := p, hessian := Z } : Jet (n + n))) hJ.1
  · exact
      subjet_left_of_subjet_blockFunctionToPointFunction_sub_at
        (n := n) (G := G) (H := H) (z := z)
        (J := ({ gradient := p, hessian := Z } : Jet (n + n))) hJ.2

/--
The right component of a two-sided jet of a separated difference is a
two-sided jet of the right function with the signs dictated by subtraction.

In quantified mathematical form, let `G, H : R^n -> R`, let
`F(ξ, η) = G(ξ) - H(η)`, and suppose `(p, Z)` belongs both to the ordinary
superjet and to the ordinary subjet of `F` at `(x0, y0)`. Then the negative
right component of `p` and the negative right-right block of `Z` belong both
to the ordinary superjet and to the ordinary subjet of `H` at `y0`.
-/
theorem HasSecondOrderJet.right_of_blockFunctionToPointFunction_sub_at
    {G H : Point n -> Real} {z : Point (n + n)} {p : Point (n + n)}
    {Z : Hessian (n + n)}
    (hJ : HasSecondOrderJet
      (blockFunctionToPointFunction (n := n)
        (fun q : BlockPoint n => G (blockPointLeft q) - H (blockPointRight q)))
      z p Z) :
    HasSecondOrderJet H (pointRight (n := n) z)
      (-rightPointGradient (n := n) p) (-rightPointHessian (n := n) Z) := by
  constructor
  · exact
      superjet_right_of_subjet_blockFunctionToPointFunction_sub_at
        (n := n) (G := G) (H := H) (z := z)
        (J := ({ gradient := p, hessian := Z } : Jet (n + n))) hJ.2
  · exact
      subjet_right_of_superjet_blockFunctionToPointFunction_sub_at
        (n := n) (G := G) (H := H) (z := z)
        (J := ({ gradient := p, hessian := Z } : Jet (n + n))) hJ.1

/--
A two-sided jet of a separated difference gives the two corresponding
one-function two-sided jets.

In quantified mathematical form, let `G, H : R^n -> R`, let
`F(ξ, η) = G(ξ) - H(η)`, and suppose `(p, Z)` belongs both to the ordinary
superjet and to the ordinary subjet of `F` at `(x0, y0)`. Then the left
component of `(p, Z)` is an ordinary two-sided second-order jet of `G` at
`x0`, and the negative right component of `(p, Z)` is an ordinary two-sided
second-order jet of `H` at `y0`.
-/
theorem HasSecondOrderJet.left_right_of_blockFunctionToPointFunction_sub_at
    {G H : Point n -> Real} {z : Point (n + n)} {p : Point (n + n)}
    {Z : Hessian (n + n)}
    (hJ : HasSecondOrderJet
      (blockFunctionToPointFunction (n := n)
        (fun q : BlockPoint n => G (blockPointLeft q) - H (blockPointRight q)))
      z p Z) :
    HasSecondOrderJet G (pointLeft (n := n) z)
        (leftPointGradient (n := n) p) (leftPointHessian (n := n) Z) ∧
      HasSecondOrderJet H (pointRight (n := n) z)
        (-rightPointGradient (n := n) p) (-rightPointHessian (n := n) Z) :=
  ⟨hJ.left_of_blockFunctionToPointFunction_sub_at,
    hJ.right_of_blockFunctionToPointFunction_sub_at⟩

/--
A two-sided jet of a separated difference has zero mixed Hessian bilinear
expression.

In quantified mathematical form, let `G, H : R^n -> R`, let
`F(ξ, η) = G(ξ) - H(η)`, and suppose that `F` has an ordinary two-sided
second-order jet `(p, Z)` at `(x0, y0)`. Then for every `x, y ∈ R^n`,

`⟪Z(x, 0), (0, y)⟫ + ⟪Z(0, y), (x, 0)⟫ = 0`.
-/
theorem HasSecondOrderJet.mixed_dot_zero_of_blockFunctionToPointFunction_sub_at
    {G H : Point n -> Real} {z : Point (n + n)} {p : Point (n + n)}
    {Z : Hessian (n + n)}
    (hJ : HasSecondOrderJet
      (blockFunctionToPointFunction (n := n)
        (fun q : BlockPoint n => G (blockPointLeft q) - H (blockPointRight q)))
      z p Z) :
    ∀ x y : Point n,
      dotProduct (Matrix.mulVec Z (leftPointEmbedding (n := n) x))
          (rightPointEmbedding (n := n) y) +
        dotProduct (Matrix.mulVec Z (rightPointEmbedding (n := n) y))
          (leftPointEmbedding (n := n) x) = 0 :=
  mixed_dot_zero_of_hasSecondOrderExpansionWithin_blockFunctionToPointFunction_sub
    (n := n) (G := G) (H := H) (z := z) (p := p) (Z := Z)
    hJ.hasSecondOrderExpansionWithin

/--
A Hermitian two-sided jet Hessian of a separated difference is block diagonal.

In quantified mathematical form, let `G, H : R^n -> R`, let
`F(ξ, η) = G(ξ) - H(η)`, and suppose that `F` has an ordinary two-sided
second-order jet `(p, Z)` at `(x0, y0)`. If `Z` is Hermitian, then the
block-coordinate form of `Z` is

`[X 0; 0 -Y]`,

where `X` is the left-left block of `Z` and `Y` is the negative of the
right-right block of `Z`.
-/
theorem HasSecondOrderJet.blockDiagonal_of_blockFunctionToPointFunction_sub_at
    {G H : Point n -> Real} {z : Point (n + n)} {p : Point (n + n)}
    {Z : Hessian (n + n)} (hZ : Z.IsHermitian)
    (hJ : HasSecondOrderJet
      (blockFunctionToPointFunction (n := n)
        (fun q : BlockPoint n => G (blockPointLeft q) - H (blockPointRight q)))
      z p Z) :
    pointHessianToBlockHessian (n := n) Z =
      comparisonBlockDiagonal (leftPointHessian (n := n) Z)
        (-rightPointHessian (n := n) Z) :=
  pointHessianToBlockHessian_eq_comparisonBlockDiagonal_of_mixed_dot_zero
    (n := n) (Z := Z) hZ
    hJ.mixed_dot_zero_of_blockFunctionToPointFunction_sub_at

/--
A convergent sequence of separated two-sided jet Hessians has a block diagonal
limit.

In quantified mathematical form, let `G, H : R^n -> R`, let
`F(ξ, η) = G(ξ) - H(η)`, and suppose that for every natural number `k`,
`(J_k.gradient, J_k.hessian)` is an ordinary two-sided second-order jet of
`F` at `z_k`. Suppose also that every `J_k.hessian` is Hermitian and that a
subsequence of the Hessians converges to `Z`. Then the block-coordinate form
of `Z` is

`[X 0; 0 -Y]`,

where `X` is the left-left block of `Z` and `Y` is the negative of the
right-right block of `Z`.
-/
theorem blockDiagonal_of_tendsto_twoSidedJet_blockFunctionToPointFunction_sub
    {G H : Point n -> Real} {zSeq : Nat -> Point (n + n)}
    {JSeq : Nat -> Jet (n + n)} {Z : Hessian (n + n)} {φ : Nat -> Nat}
    (hZ : Filter.Tendsto (fun k : Nat => (JSeq (φ k)).hessian) Filter.atTop (nhds Z))
    (hHerm : ∀ k : Nat, ((JSeq k).hessian).IsHermitian)
    (hJ : ∀ k : Nat,
      HasSecondOrderJet
        (blockFunctionToPointFunction (n := n)
          (fun q : BlockPoint n => G (blockPointLeft q) - H (blockPointRight q)))
        (zSeq k) (JSeq k).gradient (JSeq k).hessian) :
    pointHessianToBlockHessian (n := n) Z =
      comparisonBlockDiagonal (leftPointHessian (n := n) Z)
        (-rightPointHessian (n := n) Z) := by
  have hcontBlock :
      Continuous fun X : Hessian (n + n) => pointHessianToBlockHessian (n := n) X := by
    refine continuous_pi ?_
    intro i
    refine continuous_pi ?_
    intro j
    exact
      (continuous_apply (finSumFinEquiv j)).comp
        (continuous_apply (finSumFinEquiv i) :
          Continuous fun X : Hessian (n + n) => X (finSumFinEquiv i))
  have hcontDiag :
      Continuous fun X : Hessian (n + n) =>
        comparisonBlockDiagonal (leftPointHessian (n := n) X)
          (-rightPointHessian (n := n) X) := by
    refine continuous_pi ?_
    intro i
    refine continuous_pi ?_
    intro j
    cases i with
    | inl i =>
        cases j with
        | inl j =>
            exact
              (continuous_apply (Fin.castAdd n j)).comp
                (continuous_apply (Fin.castAdd n i) :
                  Continuous fun X : Hessian (n + n) => X (Fin.castAdd n i))
        | inr j =>
            simpa [comparisonBlockDiagonal] using
              (continuous_const : Continuous fun _X : Hessian (n + n) => (0 : Real))
    | inr i =>
        cases j with
        | inl j =>
            simpa [comparisonBlockDiagonal] using
              (continuous_const : Continuous fun _X : Hessian (n + n) => (0 : Real))
        | inr j =>
            refine ((continuous_apply (Fin.natAdd n j)).comp
                (continuous_apply (Fin.natAdd n i) :
                  Continuous fun X : Hessian (n + n) => X (Fin.natAdd n i))).congr fun X => ?_
            exact (neg_neg (X (Fin.natAdd n i) (Fin.natAdd n j))).symm
  have hblockLim :
      Filter.Tendsto
        (fun k : Nat => pointHessianToBlockHessian (n := n) (JSeq (φ k)).hessian)
        Filter.atTop (nhds (pointHessianToBlockHessian (n := n) Z)) :=
    (hcontBlock.tendsto Z).comp hZ
  have hdiagLim :
      Filter.Tendsto
        (fun k : Nat =>
          comparisonBlockDiagonal (leftPointHessian (n := n) (JSeq (φ k)).hessian)
            (-rightPointHessian (n := n) (JSeq (φ k)).hessian))
        Filter.atTop
        (nhds
          (comparisonBlockDiagonal (leftPointHessian (n := n) Z)
            (-rightPointHessian (n := n) Z))) :=
    (hcontDiag.tendsto Z).comp hZ
  have hseq :
      (fun k : Nat => pointHessianToBlockHessian (n := n) (JSeq (φ k)).hessian) =ᶠ[Filter.atTop]
        fun k : Nat =>
          comparisonBlockDiagonal (leftPointHessian (n := n) (JSeq (φ k)).hessian)
            (-rightPointHessian (n := n) (JSeq (φ k)).hessian) := by
    exact Filter.Eventually.of_forall fun k =>
      (hJ (φ k)).blockDiagonal_of_blockFunctionToPointFunction_sub_at (hHerm (φ k))
  have hblockLim' :
      Filter.Tendsto
        (fun k : Nat => pointHessianToBlockHessian (n := n) (JSeq (φ k)).hessian)
        Filter.atTop
        (nhds
          (comparisonBlockDiagonal (leftPointHessian (n := n) Z)
            (-rightPointHessian (n := n) Z))) :=
    hdiagLim.congr' hseq.symm
  exact tendsto_nhds_unique hblockLim hblockLim'

/--
Closed semijets and matrix bounds for the compact regularized doubled
convolution, using the block diagonal limit supplied by selected two-sided
jets.

In quantified mathematical form, let `K` and `L` be nonempty compact subsets
of `R^n`, let `u` be upper semicontinuous on `K`, and let `v` be lower
semicontinuous on `L`. Let

`F(ξ, η) =
compactSupConvolution lambda K u ξ - compactInfConvolution lambda L v η`.

Suppose that a sequence of ordinary two-sided second-order jets of `F` has
Hermitian Hessians whose subsequence converges to `Z`, and suppose that
`(0, Z)` belongs to the closed superjet of `F` at `(0, 0)`. If the
block-coordinate matrix of `Z` lies between `lower` and `upper`, then
`(0, X)` belongs to the closed superjet at `0` of the compact
sup-convolution, `(0, Y)` belongs to the closed subjet at `0` of the compact
inf-convolution, and

`lower ≤ [X 0; 0 -Y] ≤ upper`,

where `X` is the left-left block of `Z` and `Y` is the negative of the
right-right block of `Z`.
-/
theorem closedSemijets_and_blockBounds_of_tendsto_twoSidedJet_regularizedDoubledConvolution
    {lambda : Real} {K L : Set (Point n)} {u v : Point n -> Real}
    (hKne : K.Nonempty) (hLne : L.Nonempty)
    (hKcompact : IsCompact K) (hLcompact : IsCompact L)
    (hu : UpperSemicontinuousOn u K) (hv : LowerSemicontinuousOn v L)
    {zSeq : Nat -> Point (n + n)} {JSeq : Nat -> Jet (n + n)}
    {Z : Hessian (n + n)} {φ : Nat -> Nat} {lower upper : BlockHessian n}
    (hZ : Filter.Tendsto (fun k : Nat => (JSeq (φ k)).hessian) Filter.atTop (nhds Z))
    (hHerm : ∀ k : Nat, ((JSeq k).hessian).IsHermitian)
    (hJ : ∀ k : Nat,
      HasSecondOrderJet
        (blockFunctionToPointFunction (n := n)
          (regularizedDoubledConvolution (n := n) lambda K L u v))
        (zSeq k) (JSeq k).gradient (JSeq k).hessian)
    (hlower : lower <= pointHessianToBlockHessian (n := n) Z)
    (hupper : pointHessianToBlockHessian (n := n) Z <= upper)
    (hclosed : ({ gradient := 0, hessian := Z } : Jet (n + n)) ∈
      ClosedSuperjet Set.univ
        (blockFunctionToPointFunction (n := n)
          (regularizedDoubledConvolution (n := n) lambda K L u v)) 0) :
    ({ gradient := 0, hessian := leftPointHessian (n := n) Z } : Jet n) ∈
        ClosedSuperjet Set.univ (fun ξ : Point n => compactSupConvolution lambda K u ξ) 0 ∧
      ({ gradient := 0, hessian := -rightPointHessian (n := n) Z } : Jet n) ∈
        ClosedSubjet Set.univ (fun η : Point n => compactInfConvolution lambda L v η) 0 ∧
        lower <=
          comparisonBlockDiagonal (leftPointHessian (n := n) Z)
            (-rightPointHessian (n := n) Z) ∧
        comparisonBlockDiagonal (leftPointHessian (n := n) Z)
            (-rightPointHessian (n := n) Z) <= upper := by
  let G : Point n -> Real := fun ξ => compactSupConvolution lambda K u ξ
  let H : Point n -> Real := fun η => compactInfConvolution lambda L v η
  have hJsep : ∀ k : Nat,
      HasSecondOrderJet
        (blockFunctionToPointFunction (n := n)
          (fun q : BlockPoint n => G (blockPointLeft q) - H (blockPointRight q)))
        (zSeq k) (JSeq k).gradient (JSeq k).hessian := by
    intro k
    exact hJ k
  have hdiag :
      pointHessianToBlockHessian (n := n) Z =
        comparisonBlockDiagonal (leftPointHessian (n := n) Z)
          (-rightPointHessian (n := n) Z) :=
    blockDiagonal_of_tendsto_twoSidedJet_blockFunctionToPointFunction_sub
      (n := n) (G := G) (H := H) (zSeq := zSeq) (JSeq := JSeq) (Z := Z) (φ := φ)
      hZ hHerm hJsep
  exact
    closedSemijets_and_blockBounds_of_regularizedDoubledConvolution
      (n := n) hKne hLne hKcompact hLcompact hu hv hdiag hlower hupper hclosed

/--
Transfer the closed semijets produced for compact sup- and inf-convolutions
back to the original functions at the origin.

In quantified mathematical form, assume the hypotheses of
`closedSemijets_and_blockBounds_of_tendsto_twoSidedJet_regularizedDoubledConvolution`
and assume `lambda ≠ 0`. Since the closed semijets produced at the origin
have first-order part zero, the compact sup-convolution transfer point is
`0 + lambda^{-1} 0 = 0`, and the compact inf-convolution transfer point is
`0 - lambda^{-1} 0 = 0`. Hence the same matrices give a closed superjet of
`u` at `0` relative to `K` and a closed subjet of `v` at `0` relative to `L`,
with the same Loewner bounds.
-/
theorem closedSemijets_and_blockBounds_original_of_tendsto_twoSidedJet_regularizedDoubledConvolution
    {lambda : Real} (hlambda : lambda ≠ 0)
    {K L : Set (Point n)} {u v : Point n -> Real}
    (hKne : K.Nonempty) (hLne : L.Nonempty)
    (hKcompact : IsCompact K) (hLcompact : IsCompact L)
    (hu : UpperSemicontinuousOn u K) (hv : LowerSemicontinuousOn v L)
    {zSeq : Nat -> Point (n + n)} {JSeq : Nat -> Jet (n + n)}
    {Z : Hessian (n + n)} {φ : Nat -> Nat} {lower upper : BlockHessian n}
    (hZ : Filter.Tendsto (fun k : Nat => (JSeq (φ k)).hessian) Filter.atTop (nhds Z))
    (hHerm : ∀ k : Nat, ((JSeq k).hessian).IsHermitian)
    (hJ : ∀ k : Nat,
      HasSecondOrderJet
        (blockFunctionToPointFunction (n := n)
          (regularizedDoubledConvolution (n := n) lambda K L u v))
        (zSeq k) (JSeq k).gradient (JSeq k).hessian)
    (hlower : lower <= pointHessianToBlockHessian (n := n) Z)
    (hupper : pointHessianToBlockHessian (n := n) Z <= upper)
    (hclosed : ({ gradient := 0, hessian := Z } : Jet (n + n)) ∈
      ClosedSuperjet Set.univ
        (blockFunctionToPointFunction (n := n)
          (regularizedDoubledConvolution (n := n) lambda K L u v)) 0) :
    ({ gradient := 0, hessian := leftPointHessian (n := n) Z } : Jet n) ∈
        ClosedSuperjet K u 0 ∧
      ({ gradient := 0, hessian := -rightPointHessian (n := n) Z } : Jet n) ∈
        ClosedSubjet L v 0 ∧
        lower <=
          comparisonBlockDiagonal (leftPointHessian (n := n) Z)
            (-rightPointHessian (n := n) Z) ∧
        comparisonBlockDiagonal (leftPointHessian (n := n) Z)
            (-rightPointHessian (n := n) Z) <= upper := by
  let X : Hessian n := leftPointHessian (n := n) Z
  let Y : Hessian n := -rightPointHessian (n := n) Z
  let Jx : Jet n := { gradient := 0, hessian := X }
  let Jy : Jet n := { gradient := 0, hessian := Y }
  rcases closedSemijets_and_blockBounds_of_tendsto_twoSidedJet_regularizedDoubledConvolution
      (n := n) hKne hLne hKcompact hLcompact hu hv
      (zSeq := zSeq) (JSeq := JSeq) (Z := Z) (φ := φ)
      (lower := lower) (upper := upper) hZ hHerm hJ hlower hupper hclosed with
    ⟨hJx, hJy, hlower', hupper'⟩
  have hxTransfer :
      Jx ∈ ClosedSuperjet K u (supConvolutionTransferPoint lambda (0 : Point n) Jx) :=
    closedSuperjet_of_closedSuperjet_compactSupConvolution_transfer_of_isCompact_of_ne_zero
      (K := K) (v := u) (lambda := lambda) (η := 0) (J := Jx)
      hlambda hKne hKcompact hu (by simpa [Jx, X] using hJx)
  have hyTransfer :
      Jy ∈ ClosedSubjet L v (infConvolutionTransferPoint lambda (0 : Point n) Jy) :=
    closedSubjet_of_closedSubjet_compactInfConvolution_transfer_of_isCompact_of_ne_zero
      (K := L) (v := v) (lambda := lambda) (η := 0) (J := Jy)
      hlambda hLne hLcompact hv (by simpa [Jy, Y] using hJy)
  have hxPoint : supConvolutionTransferPoint lambda (0 : Point n) Jx = 0 := by
    simp [supConvolutionTransferPoint, Jx]
  have hyPoint : infConvolutionTransferPoint lambda (0 : Point n) Jy = 0 := by
    simp [infConvolutionTransferPoint, Jy]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [Jx, X, hxPoint] using hxTransfer
  · simpa [Jy, Y, hyPoint] using hyTransfer
  · simpa [X, Y] using hlower'
  · simpa [X, Y] using hupper'

/--
Selected ordinary two-sided jets for the compact regularized doubled
convolution, with Hessian bounds in block coordinates.

In quantified mathematical form, let `K` and `L` be nonempty compact subsets
of `R^n`, let `u` be upper semicontinuous on `K`, and let `v` be lower
semicontinuous on `L`. Let

`F(ξ, η) =
compactSupConvolution lambda K u ξ - compactInfConvolution lambda L v η`.

Assume `0 ≤ lambda`, let `B` be a symmetric block Hessian, and suppose that

`(ξ, η) ↦ F(ξ, η) - (1 / 2)⟪B(ξ, η), (ξ, η)⟫`

has a maximum at `(0, 0)` on all of `R^n × R^n`. Then there are points
`z_k ∈ R^(n+n)`, ordinary two-sided jets `J_k` of `z ↦ F(z_1, z_2)` at
`z_k`, a matrix `Z`, and a strictly increasing map `φ : Nat -> Nat` such
that `(J_{φ(k)}).hessian -> Z`,
`(0, Z) ∈ \overline J^{2,+}_{R^(n+n)}(z ↦ F(z_1,z_2))(0)`, and

`-lambda [I 0; 0 I] ≤ pointHessianToBlockHessian Z ≤ B`.
-/
theorem exists_twoSidedJet_sequence_subsequence_graph_tendsto_regularizedDoubledConvolution
    (hJensen : JensenContactSetPositiveMeasureOnClosedBallTheorem (n + n))
    (hAleksandrov : AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem (n + n))
    {lambda : Real} (hlambda : 0 <= lambda)
    {K L : Set (Point n)} {u v : Point n -> Real}
    (hKne : K.Nonempty) (hLne : L.Nonempty)
    (hKcompact : IsCompact K) (hLcompact : IsCompact L)
    (hu : UpperSemicontinuousOn u K) (hv : LowerSemicontinuousOn v L)
    {B : BlockHessian n} (hB : B.IsHermitian)
    (hmax : IsMaxOn
      (fun q : BlockPoint n =>
        regularizedDoubledConvolution (n := n) lambda K L u v q -
          blockQuadraticModel B q)
      Set.univ 0) :
    ∃ zSeq : Nat -> Point (n + n), ∃ JSeq : Nat -> Jet (n + n),
    ∃ Z : Hessian (n + n), ∃ φ : Nat -> Nat,
      (∀ k : Nat, (JSeq k).hessian.IsHermitian) ∧
      (∀ k : Nat,
        HasSecondOrderJet
          (blockFunctionToPointFunction (n := n)
            (regularizedDoubledConvolution (n := n) lambda K L u v))
          (zSeq k) (JSeq k).gradient (JSeq k).hessian) ∧
      StrictMono φ ∧
      Filter.Tendsto (fun k : Nat => (JSeq (φ k)).hessian)
        Filter.atTop (nhds Z) ∧
      Z.IsHermitian ∧
      (-lambda) • blockDiagonalIdentity n <= pointHessianToBlockHessian (n := n) Z ∧
      pointHessianToBlockHessian (n := n) Z <= B ∧
      ({ gradient := 0, hessian := Z } : Jet (n + n)) ∈
        ClosedSuperjet Set.univ
          (blockFunctionToPointFunction (n := n)
            (regularizedDoubledConvolution (n := n) lambda K L u v)) 0 := by
  let F : BlockPoint n -> Real :=
    regularizedDoubledConvolution (n := n) lambda K L u v
  let f : Point (n + n) -> Real := blockFunctionToPointFunction (n := n) F
  have hFcont : Continuous F :=
    continuous_regularizedDoubledConvolution_of_isCompact
      (n := n) hKne hLne hKcompact hLcompact hu hv
  have hf : Continuous f :=
    Continuous.blockFunctionToPointFunction (n := n) hFcont
  have hFsemi : BlockCoordinateSemiconvexOn lambda Set.univ F :=
    blockCoordinateSemiconvexOn_regularizedDoubledConvolution_of_isCompact
      (n := n) hKne hLne hKcompact hLcompact hu hv
  have hfsemi : CoordinateSemiconvexOn lambda Set.univ f :=
    hFsemi.coordinateSemiconvexOn_blockFunctionToPointFunction
  have hBpoint : (blockHessianToPointHessian (n := n) B).IsHermitian :=
    Matrix.IsHermitian.blockHessianToPointHessian (n := n) hB
  have hmaxPoint :
      IsMaxOn
        (semiconvexQuadraticObjective f (blockHessianToPointHessian (n := n) B))
        Set.univ 0 := by
    simpa [F, f] using
      isMaxOn_semiconvexQuadraticObjective_blockFunctionToPointFunction
        (n := n) (F := F) (B := B) hmax
  rcases exists_semiconvex_twoSidedJet_sequence_subsequence_graph_tendsto
      (n := n + n) hJensen hAleksandrov hlambda hf hBpoint hfsemi hmaxPoint with
    ⟨zSeq, JSeq, Z, φ, hHerm, hJ, hφ, hZ, hZHerm, hlowerPoint, hupperPoint,
      hclosed⟩
  rcases pointHessianToBlockHessian_bounds_of_scalar_identity_bounds
      (n := n) hlowerPoint hupperPoint with
    ⟨hlower, hupper⟩
  refine ⟨zSeq, JSeq, Z, φ, hHerm, ?_, hφ, hZ, hZHerm, hlower, ?_, ?_⟩
  · simpa [F, f] using hJ
  · simpa [pointHessianToBlockHessian_blockHessianToPointHessian] using hupper
  · simpa [F, f] using hclosed

/--
The theorem-shaped proposition for the selected two-sided-jet input used by
the compact regularized doubled convolution argument.

In quantified mathematical form, this says that for every `lambda ≥ 0`, every
pair of nonempty compact sets `K, L ⊆ R^n`, every function `u` upper
semicontinuous on `K`, every function `v` lower semicontinuous on `L`, every
Hermitian block matrix `B`, and every maximum at `0` of

`q ↦ regularizedDoubledConvolution lambda K L u v q
  - (1 / 2)⟪Bq, q⟫`,

there exist points `z_k ∈ R^(n+n)`, ordinary two-sided jets `J_k` at `z_k`,
a matrix `Z`, and a strictly increasing map `φ : Nat -> Nat` such that
`(J_{φ(k)}).hessian` converges to `Z`, the jet `(0, Z)` belongs to the closed
superjet at `0` of the regularized doubled convolution, and the block form of
`Z` lies between `-lambda [I 0; 0 I]` and `B` in the Loewner order.
-/
def SelectedTwoSidedJetsForRegularizedDoubledConvolutionTheorem (n : Nat) : Prop :=
  ∀ lambda : Real, 0 <= lambda ->
  ∀ K L : Set (Point n), ∀ u v : Point n -> Real,
    K.Nonempty -> L.Nonempty ->
    IsCompact K -> IsCompact L ->
    UpperSemicontinuousOn u K -> LowerSemicontinuousOn v L ->
  ∀ B : BlockHessian n, B.IsHermitian ->
    IsMaxOn
      (fun q : BlockPoint n =>
        regularizedDoubledConvolution (n := n) lambda K L u v q -
          blockQuadraticModel B q)
      Set.univ 0 ->
    ∃ zSeq : Nat -> Point (n + n), ∃ JSeq : Nat -> Jet (n + n),
    ∃ Z : Hessian (n + n), ∃ φ : Nat -> Nat,
      (∀ k : Nat, (JSeq k).hessian.IsHermitian) ∧
      (∀ k : Nat,
        HasSecondOrderJet
          (blockFunctionToPointFunction (n := n)
            (regularizedDoubledConvolution (n := n) lambda K L u v))
          (zSeq k) (JSeq k).gradient (JSeq k).hessian) ∧
      StrictMono φ ∧
      Filter.Tendsto (fun k : Nat => (JSeq (φ k)).hessian)
        Filter.atTop (nhds Z) ∧
      Z.IsHermitian ∧
      (-lambda) • blockDiagonalIdentity n <= pointHessianToBlockHessian (n := n) Z ∧
      pointHessianToBlockHessian (n := n) Z <= B ∧
      ({ gradient := 0, hessian := Z } : Jet (n + n)) ∈
        ClosedSuperjet Set.univ
          (blockFunctionToPointFunction (n := n)
            (regularizedDoubledConvolution (n := n) lambda K L u v)) 0

/--
The localized Jensen contact-set theorem and localized Aleksandrov
second-differentiability theorem imply the selected two-sided-jet theorem for
the compact regularized doubled convolution.
-/
theorem SelectedTwoSidedJetsForRegularizedDoubledConvolutionTheorem.of_localized_jensen_aleksandrov
    (hJensen : JensenContactSetPositiveMeasureOnClosedBallTheorem (n + n))
    (hAleksandrov : AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem (n + n)) :
    SelectedTwoSidedJetsForRegularizedDoubledConvolutionTheorem n := by
  intro lambda hlambda K L u v hKne hLne hKcompact hLcompact hu hv B hB hmax
  exact exists_twoSidedJet_sequence_subsequence_graph_tendsto_regularizedDoubledConvolution
    (n := n) hJensen hAleksandrov hlambda
    hKne hLne hKcompact hLcompact hu hv hB hmax

/--
The selected two-sided-jet theorem for the compact regularized doubled
convolution follows from the localized Aleksandrov second-differentiability
theorem in dimension `n + n`, because the localized Jensen contact-set theorem
has already been proved.
-/
theorem SelectedTwoSidedJetsForRegularizedDoubledConvolutionTheorem.of_aleksandrov
    (hAleksandrov : AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem (n + n)) :
    SelectedTwoSidedJetsForRegularizedDoubledConvolutionTheorem n :=
  SelectedTwoSidedJetsForRegularizedDoubledConvolutionTheorem.of_localized_jensen_aleksandrov
    (n := n)
    (JensenContactSetPositiveMeasureOnClosedBallTheorem.proof (n := n + n))
    hAleksandrov

/--
Closed semijets of the original compact functions obtained from the
Aleksandrov--Jensen selected ordinary two-sided jets.

In quantified mathematical form, assume the hypotheses of
`exists_twoSidedJet_sequence_subsequence_graph_tendsto_regularizedDoubledConvolution`
and assume `lambda ≠ 0`. Then there exist matrices `X` and `Y` such that

`(0, X) ∈ \overline J^{2,+}_K u(0)`,

`(0, Y) ∈ \overline J^{2,-}_L v(0)`,

and

`-lambda [I 0; 0 I] ≤ [X 0; 0 -Y] ≤ B`.
-/
theorem closedSemijets_and_blockBounds_original_of_regularizedDoubledConvolution_max
    (hJensen : JensenContactSetPositiveMeasureOnClosedBallTheorem (n + n))
    (hAleksandrov : AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem (n + n))
    {lambda : Real} (hlambda_nonneg : 0 <= lambda) (hlambda_ne : lambda ≠ 0)
    {K L : Set (Point n)} {u v : Point n -> Real}
    (hKne : K.Nonempty) (hLne : L.Nonempty)
    (hKcompact : IsCompact K) (hLcompact : IsCompact L)
    (hu : UpperSemicontinuousOn u K) (hv : LowerSemicontinuousOn v L)
    {B : BlockHessian n} (hB : B.IsHermitian)
    (hmax : IsMaxOn
      (fun q : BlockPoint n =>
        regularizedDoubledConvolution (n := n) lambda K L u v q -
          blockQuadraticModel B q)
      Set.univ 0) :
    ∃ X Y : Hessian n,
      ({ gradient := 0, hessian := X } : Jet n) ∈ ClosedSuperjet K u 0 ∧
      ({ gradient := 0, hessian := Y } : Jet n) ∈ ClosedSubjet L v 0 ∧
      (-lambda) • blockDiagonalIdentity n <= comparisonBlockDiagonal X Y ∧
      comparisonBlockDiagonal X Y <= B := by
  rcases exists_twoSidedJet_sequence_subsequence_graph_tendsto_regularizedDoubledConvolution
      (n := n) hJensen hAleksandrov hlambda_nonneg
      hKne hLne hKcompact hLcompact hu hv hB hmax with
    ⟨zSeq, JSeq, Z, φ, hHerm, hJ, _hφ, hZ, _hZHerm, hlower, hupper, hclosed⟩
  rcases
    closedSemijets_and_blockBounds_original_of_tendsto_twoSidedJet_regularizedDoubledConvolution
      (n := n) (lambda := lambda) hlambda_ne
      hKne hLne hKcompact hLcompact hu hv
      (zSeq := zSeq) (JSeq := JSeq) (Z := Z) (φ := φ)
      (lower := (-lambda) • blockDiagonalIdentity n) (upper := B)
      hZ hHerm hJ hlower hupper hclosed with
    ⟨hX, hY, hlower', hupper'⟩
  exact ⟨leftPointHessian (n := n) Z, -rightPointHessian (n := n) Z,
    hX, hY, hlower', hupper'⟩

/--
Closed semijets of the original compact functions from the selected
two-sided-jet theorem.

In quantified mathematical form, this is
`closedSemijets_and_blockBounds_original_of_regularizedDoubledConvolution_max`
with the selected two-sided-jet theorem supplied directly, rather than
through the localized Jensen and Aleksandrov inputs.
-/
theorem closedSemijets_and_blockBounds_original_of_selectedTwoSidedJets
    (hselected : SelectedTwoSidedJetsForRegularizedDoubledConvolutionTheorem n)
    {lambda : Real} (hlambda_nonneg : 0 <= lambda) (hlambda_ne : lambda ≠ 0)
    {K L : Set (Point n)} {u v : Point n -> Real}
    (hKne : K.Nonempty) (hLne : L.Nonempty)
    (hKcompact : IsCompact K) (hLcompact : IsCompact L)
    (hu : UpperSemicontinuousOn u K) (hv : LowerSemicontinuousOn v L)
    {B : BlockHessian n} (hB : B.IsHermitian)
    (hmax : IsMaxOn
      (fun q : BlockPoint n =>
        regularizedDoubledConvolution (n := n) lambda K L u v q -
          blockQuadraticModel B q)
      Set.univ 0) :
    ∃ X Y : Hessian n,
      ({ gradient := 0, hessian := X } : Jet n) ∈ ClosedSuperjet K u 0 ∧
      ({ gradient := 0, hessian := Y } : Jet n) ∈ ClosedSubjet L v 0 ∧
      (-lambda) • blockDiagonalIdentity n <= comparisonBlockDiagonal X Y ∧
      comparisonBlockDiagonal X Y <= B := by
  rcases hselected lambda hlambda_nonneg K L u v
      hKne hLne hKcompact hLcompact hu hv B hB hmax with
    ⟨zSeq, JSeq, Z, φ, hHerm, hJ, _hφ, hZ, _hZHerm, hlower, hupper, hclosed⟩
  rcases
    closedSemijets_and_blockBounds_original_of_tendsto_twoSidedJet_regularizedDoubledConvolution
      (n := n) (lambda := lambda) hlambda_ne
      hKne hLne hKcompact hLcompact hu hv
      (zSeq := zSeq) (JSeq := JSeq) (Z := Z) (φ := φ)
      (lower := (-lambda) • blockDiagonalIdentity n) (upper := B)
      hZ hHerm hJ hlower hupper hclosed with
    ⟨hX, hY, hlower', hupper'⟩
  exact ⟨leftPointHessian (n := n) Z, -rightPointHessian (n := n) Z,
    hX, hY, hlower', hupper'⟩

end ViscositySolns
