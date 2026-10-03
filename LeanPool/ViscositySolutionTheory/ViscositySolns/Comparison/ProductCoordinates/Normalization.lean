/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Comparison.ProductCoordinates.JetTransfer

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Product-coordinate consequences of the semiconvex matrix lemma (Normalization)

Part of the product-coordinate development connecting the semiconvex matrix
conclusion on the coordinate space `R^(n+n)` to the block-matrix notation on
`R^n × R^n`. Split from `ProductCoordinates.lean`; see the umbrella module
docstring.
-/

@[expose] public noncomputable section

open scoped MatrixOrder
open Filter

namespace ViscositySolns

variable {n : Nat}

/--
Restrict a superjet of a separated difference to the left coordinate slice.

In standard mathematical terms, if `(p, Z)` is a superjet at `(0, 0)` of
`(ξ, η) ↦ G(ξ) - H(η)`, then the left component of `p` and the left-left
block of `Z` form a superjet at `0` of `G`.
-/
theorem superjet_left_of_superjet_blockFunctionToPointFunction_sub
    {G H : Point n -> Real} {J : Jet (n + n)}
    (hJ : J ∈ Superjet Set.univ
      (blockFunctionToPointFunction (n := n)
        (fun q : BlockPoint n => G (blockPointLeft q) - H (blockPointRight q))) 0) :
    ({ gradient := leftPointGradient (n := n) J.gradient,
       hessian := leftPointHessian (n := n) J.hessian } : Jet n) ∈
      Superjet Set.univ G 0 := by
  rw [superjet_iff_superjetExcess_secondOrderNonposWithin]
  have hblock :=
    (superjet_iff_superjetExcess_secondOrderNonposWithin (C := Set.univ)
      (u := blockFunctionToPointFunction (n := n)
        (fun q : BlockPoint n => G (blockPointLeft q) - H (blockPointRight q)))
      (x := 0) (J := J)).1 hJ
  intro ε hε
  have hleftTendsto :
      Tendsto (leftPointEmbedding (n := n))
        (nhdsWithin (0 : Point n) Set.univ)
        (nhdsWithin (0 : Point (n + n)) Set.univ) := by
    rw [nhdsWithin_univ, nhdsWithin_univ]
    have hcont : ContinuousAt (leftPointEmbedding (n := n)) (0 : Point n) := by
      exact continuous_leftPointEmbedding.continuousAt
    simpa using hcont.tendsto
  have hb := hleftTendsto.eventually (hblock ε hε)
  filter_upwards [hb] with x hx
  have hexcess :
      SuperjetExcess G 0
          ({ gradient := leftPointGradient (n := n) J.gradient,
             hessian := leftPointHessian (n := n) J.hessian } : Jet n) x =
        SuperjetExcess
          (blockFunctionToPointFunction (n := n)
            (fun q : BlockPoint n => G (blockPointLeft q) - H (blockPointRight q)))
          0 J (leftPointEmbedding (n := n) x) := by
    simp only [SuperjetExcess, blockFunctionToPointFunction,
      pointSumEquivBlockPoint_leftPointEmbedding, blockPointLeft_leftBlockPoint,
      blockPointRight_leftBlockPoint, quadraticModel_leftPointEmbedding]
    simp [quadraticModel, blockPointLeft, blockPointRight]
    ring
  have hnorm : ‖leftPointEmbedding (n := n) x - 0‖ <= ‖x - 0‖ := by
    simpa using norm_leftPointEmbedding_le (n := n) x
  have hsq : ‖leftPointEmbedding (n := n) x - 0‖ ^ 2 <= ‖x - 0‖ ^ 2 := by
    have hmul := mul_le_mul hnorm hnorm (norm_nonneg _) (norm_nonneg _)
    simpa [pow_two] using hmul
  have hmul : ε * ‖leftPointEmbedding (n := n) x - 0‖ ^ 2 <= ε * ‖x - 0‖ ^ 2 :=
    mul_le_mul_of_nonneg_left hsq hε.le
  linarith

/--
Restrict a superjet of a separated difference to the right coordinate slice.

In standard mathematical terms, if `(p, Z)` is a superjet at `(0, 0)` of
`(ξ, η) ↦ G(ξ) - H(η)`, then the negative right component of `p` and the
negative right-right block of `Z` form a subjet at `0` of `H`.
-/
theorem subjet_right_of_superjet_blockFunctionToPointFunction_sub
    {G H : Point n -> Real} {J : Jet (n + n)}
    (hJ : J ∈ Superjet Set.univ
      (blockFunctionToPointFunction (n := n)
        (fun q : BlockPoint n => G (blockPointLeft q) - H (blockPointRight q))) 0) :
    ({ gradient := -rightPointGradient (n := n) J.gradient,
       hessian := -rightPointHessian (n := n) J.hessian } : Jet n) ∈
      Subjet Set.univ H 0 := by
  let Jr : Jet n :=
    { gradient := rightPointGradient (n := n) J.gradient,
      hessian := rightPointHessian (n := n) J.hessian }
  have hsuperNeg :
      Jr ∈ Superjet Set.univ (fun y => -H y) 0 := by
    rw [superjet_iff_superjetExcess_secondOrderNonposWithin]
    have hblock :=
      (superjet_iff_superjetExcess_secondOrderNonposWithin (C := Set.univ)
        (u := blockFunctionToPointFunction (n := n)
          (fun q : BlockPoint n => G (blockPointLeft q) - H (blockPointRight q)))
        (x := 0) (J := J)).1 hJ
    intro ε hε
    have hrightTendsto :
        Tendsto (rightPointEmbedding (n := n))
          (nhdsWithin (0 : Point n) Set.univ)
          (nhdsWithin (0 : Point (n + n)) Set.univ) := by
      rw [nhdsWithin_univ, nhdsWithin_univ]
      have hcont : ContinuousAt (rightPointEmbedding (n := n)) (0 : Point n) := by
        exact continuous_rightPointEmbedding.continuousAt
      simpa using hcont.tendsto
    have hb := hrightTendsto.eventually (hblock ε hε)
    filter_upwards [hb] with y hy
    have hexcess :
        SuperjetExcess (fun y : Point n => -H y) 0
            Jr y =
          SuperjetExcess
            (blockFunctionToPointFunction (n := n)
              (fun q : BlockPoint n => G (blockPointLeft q) - H (blockPointRight q)))
            0 J (rightPointEmbedding (n := n) y) := by
      simp only [SuperjetExcess, blockFunctionToPointFunction,
        pointSumEquivBlockPoint_rightPointEmbedding, blockPointLeft_rightBlockPoint,
        blockPointRight_rightBlockPoint, quadraticModel_rightPointEmbedding]
      simp [quadraticModel, blockPointLeft, blockPointRight, Jr]
      ring
    have hnorm : ‖rightPointEmbedding (n := n) y - 0‖ <= ‖y - 0‖ := by
      simpa using norm_rightPointEmbedding_le (n := n) y
    have hsq : ‖rightPointEmbedding (n := n) y - 0‖ ^ 2 <= ‖y - 0‖ ^ 2 := by
      have hmul := mul_le_mul hnorm hnorm (norm_nonneg _) (norm_nonneg _)
      simpa [pow_two] using hmul
    have hmul : ε * ‖rightPointEmbedding (n := n) y - 0‖ ^ 2 <= ε * ‖y - 0‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hsq hε.le
    linarith
  change Jr.neg ∈ Subjet Set.univ H 0
  simpa using
    (superjet_neg_iff_subjet (C := Set.univ) (u := fun y : Point n => -H y)
      (x := 0) (J := Jr)).1 hsuperNeg

/--
Restrict a subjet of a separated difference to the left coordinate slice.

In standard mathematical terms, if `(p, Z)` is a subjet at `(0, 0)` of
`(ξ, η) ↦ G(ξ) - H(η)`, then the left component of `p` and the left-left
block of `Z` form a subjet at `0` of `G`.
-/
theorem subjet_left_of_subjet_blockFunctionToPointFunction_sub
    {G H : Point n -> Real} {J : Jet (n + n)}
    (hJ : J ∈ Subjet Set.univ
      (blockFunctionToPointFunction (n := n)
        (fun q : BlockPoint n => G (blockPointLeft q) - H (blockPointRight q))) 0) :
    ({ gradient := leftPointGradient (n := n) J.gradient,
       hessian := leftPointHessian (n := n) J.hessian } : Jet n) ∈
      Subjet Set.univ G 0 := by
  rw [subjet_iff_subjetExcess_secondOrderNonposWithin]
  have hblock :=
    (subjet_iff_subjetExcess_secondOrderNonposWithin (C := Set.univ)
      (u := blockFunctionToPointFunction (n := n)
        (fun q : BlockPoint n => G (blockPointLeft q) - H (blockPointRight q)))
      (x := 0) (J := J)).1 hJ
  intro ε hε
  have hleftTendsto :
      Tendsto (leftPointEmbedding (n := n))
        (nhdsWithin (0 : Point n) Set.univ)
        (nhdsWithin (0 : Point (n + n)) Set.univ) := by
    rw [nhdsWithin_univ, nhdsWithin_univ]
    have hcont : ContinuousAt (leftPointEmbedding (n := n)) (0 : Point n) := by
      exact continuous_leftPointEmbedding.continuousAt
    simpa using hcont.tendsto
  have hb := hleftTendsto.eventually (hblock ε hε)
  filter_upwards [hb] with x hx
  have hexcess :
      SubjetExcess G 0
          ({ gradient := leftPointGradient (n := n) J.gradient,
             hessian := leftPointHessian (n := n) J.hessian } : Jet n) x =
        SubjetExcess
          (blockFunctionToPointFunction (n := n)
            (fun q : BlockPoint n => G (blockPointLeft q) - H (blockPointRight q)))
          0 J (leftPointEmbedding (n := n) x) := by
    simp only [SubjetExcess, blockFunctionToPointFunction,
      pointSumEquivBlockPoint_leftPointEmbedding, blockPointLeft_leftBlockPoint,
      blockPointRight_leftBlockPoint, quadraticModel_leftPointEmbedding]
    simp [quadraticModel, blockPointLeft, blockPointRight]
    ring
  have hnorm : ‖leftPointEmbedding (n := n) x - 0‖ <= ‖x - 0‖ := by
    simpa using norm_leftPointEmbedding_le (n := n) x
  have hsq : ‖leftPointEmbedding (n := n) x - 0‖ ^ 2 <= ‖x - 0‖ ^ 2 := by
    have hmul := mul_le_mul hnorm hnorm (norm_nonneg _) (norm_nonneg _)
    simpa [pow_two] using hmul
  have hmul : ε * ‖leftPointEmbedding (n := n) x - 0‖ ^ 2 <= ε * ‖x - 0‖ ^ 2 :=
    mul_le_mul_of_nonneg_left hsq hε.le
  linarith

/--
Restrict a subjet of a separated difference to the right coordinate slice.

In standard mathematical terms, if `(p, Z)` is a subjet at `(0, 0)` of
`(ξ, η) ↦ G(ξ) - H(η)`, then the negative right component of `p` and the
negative right-right block of `Z` form a superjet at `0` of `H`.
-/
theorem superjet_right_of_subjet_blockFunctionToPointFunction_sub
    {G H : Point n -> Real} {J : Jet (n + n)}
    (hJ : J ∈ Subjet Set.univ
      (blockFunctionToPointFunction (n := n)
        (fun q : BlockPoint n => G (blockPointLeft q) - H (blockPointRight q))) 0) :
    ({ gradient := -rightPointGradient (n := n) J.gradient,
       hessian := -rightPointHessian (n := n) J.hessian } : Jet n) ∈
      Superjet Set.univ H 0 := by
  let Jr : Jet n :=
    { gradient := -rightPointGradient (n := n) J.gradient,
      hessian := -rightPointHessian (n := n) J.hessian }
  rw [superjet_iff_superjetExcess_secondOrderNonposWithin]
  have hblock :=
    (subjet_iff_subjetExcess_secondOrderNonposWithin (C := Set.univ)
      (u := blockFunctionToPointFunction (n := n)
        (fun q : BlockPoint n => G (blockPointLeft q) - H (blockPointRight q)))
      (x := 0) (J := J)).1 hJ
  intro ε hε
  have hrightTendsto :
      Tendsto (rightPointEmbedding (n := n))
        (nhdsWithin (0 : Point n) Set.univ)
        (nhdsWithin (0 : Point (n + n)) Set.univ) := by
    rw [nhdsWithin_univ, nhdsWithin_univ]
    have hcont : ContinuousAt (rightPointEmbedding (n := n)) (0 : Point n) := by
      exact continuous_rightPointEmbedding.continuousAt
    simpa using hcont.tendsto
  have hb := hrightTendsto.eventually (hblock ε hε)
  filter_upwards [hb] with y hy
  have hexcess :
      SuperjetExcess H 0 Jr y =
        SubjetExcess
          (blockFunctionToPointFunction (n := n)
            (fun q : BlockPoint n => G (blockPointLeft q) - H (blockPointRight q)))
          0 J (rightPointEmbedding (n := n) y) := by
    simp only [SuperjetExcess, SubjetExcess, blockFunctionToPointFunction,
      pointSumEquivBlockPoint_rightPointEmbedding, blockPointLeft_rightBlockPoint,
      blockPointRight_rightBlockPoint, quadraticModel_rightPointEmbedding]
    simp [quadraticModel, blockPointLeft, blockPointRight, Jr, Matrix.neg_mulVec,
      neg_dotProduct]
    ring
  have hnorm : ‖rightPointEmbedding (n := n) y - 0‖ <= ‖y - 0‖ := by
    simpa using norm_rightPointEmbedding_le (n := n) y
  have hsq : ‖rightPointEmbedding (n := n) y - 0‖ ^ 2 <= ‖y - 0‖ ^ 2 := by
    have hmul := mul_le_mul hnorm hnorm (norm_nonneg _) (norm_nonneg _)
    simpa [pow_two] using hmul
  have hmul : ε * ‖rightPointEmbedding (n := n) y - 0‖ ^ 2 <= ε * ‖y - 0‖ ^ 2 :=
    mul_le_mul_of_nonneg_left hsq hε.le
  linarith

/--
Pulling a continuous function on `R^n × R^n` back to `R^(n+n)` gives a
continuous function.
-/
theorem Continuous.blockFunctionToPointFunction
    {F : BlockPoint n -> Real} (hF : Continuous F) :
    Continuous (blockFunctionToPointFunction (n := n) F) :=
  hF.comp continuous_pointSumEquivBlockPoint

/--
The quadratic expansion of a test function at a doubled point, written in
translated block coordinates.

In standard mathematical terms, at the base point `(x0, y0)` this is

`φ0 + ⟪P, (x - x0, y - y0)⟫
  + (1 / 2) * ⟪A (x - x0, y - y0), (x - x0, y - y0)⟫`.
-/
def doubledQuadraticExpansionAt
    (x0 y0 : Point n) (φ0 : Real) (P : BlockPoint n) (A : BlockHessian n)
    (q : DoubledPoint n) : Real :=
  let z : BlockPoint n := doubledPointToBlockPoint (q.1 - x0, q.2 - y0)
  φ0 + dotProduct P z + blockQuadraticModel A z

/--
The left normalized function used after translating the doubled maximum point
to the origin and subtracting the affine part of the test function.

In standard mathematical terms this is
`x ↦ u(x0 + x) - u(x0) - ⟪P_x, x⟫`.
-/
def normalizedLeftOfBlockGradient
    (u : Point n -> Real) (x0 : Point n) (P : BlockPoint n) (x : Point n) :
    Real :=
  u (x0 + x) - u x0 - dotProduct (blockPointLeft P) x

@[simp]
theorem normalizedLeftOfBlockGradient_zero
    (u : Point n -> Real) (x0 : Point n) (P : BlockPoint n) :
    normalizedLeftOfBlockGradient (n := n) u x0 P 0 = 0 := by
  simp [normalizedLeftOfBlockGradient, dotProduct]

/--
The right normalized function used after translating the doubled maximum
point to the origin and subtracting the affine part of the test function.

If `P_y` is the derivative of the test function with respect to the second
variable, this is
`y ↦ v(y0 + y) - v(y0) + ⟪P_y, y⟫`. Equivalently, it subtracts the subjet
gradient `-P_y`.
-/
def normalizedRightOfBlockGradient
    (v : Point n -> Real) (y0 : Point n) (P : BlockPoint n) (y : Point n) :
    Real :=
  v (y0 + y) - v y0 + dotProduct (blockPointRight P) y

@[simp]
theorem normalizedRightOfBlockGradient_zero
    (v : Point n -> Real) (y0 : Point n) (P : BlockPoint n) :
    normalizedRightOfBlockGradient (n := n) v y0 P 0 = 0 := by
  simp [normalizedRightOfBlockGradient, dotProduct]

/--
Closed superjets of the left normalized function transfer back to closed
superjets of the original function with the affine gradient restored.

In quantified mathematical form, if

`u_norm(x) = u(x0+x) - u(x0) - ⟪P_x, x⟫`

and `(0, X) ∈ \overline J^{2,+}_K u_norm(0)`, then
`(P_x, X) ∈ \overline J^{2,+}_{x0+K} u(x0)`.
-/
theorem closedSuperjet_of_closedSuperjet_normalizedLeftOfBlockGradient
    {K : Set (Point n)} {u : Point n -> Real} {x0 : Point n} {P : BlockPoint n}
    {X : Hessian n}
    (hJ : ({ gradient := 0, hessian := X } : Jet n) ∈
      ClosedSuperjet K (normalizedLeftOfBlockGradient (n := n) u x0 P) 0) :
    ({ gradient := blockPointLeft P, hessian := X } : Jet n) ∈
      ClosedSuperjet ((fun x : Point n => x0 + x) '' K) u x0 := by
  let p : Point n := blockPointLeft P
  let uComp : Point n -> Real := fun x => u (x0 + x)
  let φ : Point n -> Real := fun x => -u x0 - dotProduct p x
  let A : Point n -> Jet n := fun _x => ({ gradient := -p, hessian := 0 } : Jet n)
  have hfun :
      normalizedLeftOfBlockGradient (n := n) u x0 P = fun x => uComp x + φ x := by
    funext x
    simp [normalizedLeftOfBlockGradient, uComp, φ, p]
    ring
  have hφ :
      ∀ y : Point n, y ∈ K -> HasSecondOrderExpansionWithin K φ y (A y) := by
    intro y _hy
    have hquad :=
      hasSecondOrderExpansionWithin_quadraticModel_recenter
        (C := K) (x0 := 0) (r := -u x0) (p := -p) (X := (0 : Hessian n)) y
    have hφ_eq :
        φ =
          fun z : Point n => quadraticModel 0 (-u x0) (-p) (0 : Hessian n) z := by
      funext z
      simp [φ, quadraticModel]
      ring
    have hA_eq :
        A y = quadraticModelJetAt 0 (-p) (0 : Hessian n) y := by
      apply (Jet.equivProd n).injective
      simp [A, Jet.equivProd, quadraticModelJetAt]
    simpa [hφ_eq, hA_eq] using hquad
  have hφ_cont : Continuous φ :=
    continuous_const.sub (continuous_const.dotProduct continuous_id)
  have hA_cont : Continuous A := continuous_const
  have hK :
      ({ gradient := blockPointLeft P, hessian := X } : Jet n) ∈ ClosedSuperjet K uComp 0 := by
    have hshift :
        ({ gradient := 0, hessian := X } : Jet n) - A 0 ∈ ClosedSuperjet K uComp 0 :=
      closedSuperjet_sub_of_add_hasSecondOrderExpansionWithin
        (C := K) (u := uComp) (φ := φ) (x := 0)
        (J := ({ gradient := 0, hessian := X } : Jet n))
        (A := A) hφ hφ_cont hA_cont (by simpa [hfun] using hJ)
    have hjet :
        ({ gradient := 0, hessian := X } : Jet n) - A 0 =
          ({ gradient := blockPointLeft P, hessian := X } : Jet n) := by
      apply (Jet.equivProd n).injective
      simp [A, p, Jet.equivProd]
    simpa [hjet, uComp] using hshift
  simpa [uComp] using closedSuperjet_translate_add_left (x0 := x0) (x := 0) hK

/--
Closed subjets of the right normalized function transfer back to closed
subjets of the original function with the affine gradient restored.

In quantified mathematical form, if

`v_norm(y) = v(y0+y) - v(y0) + ⟪P_y, y⟫`

and `(0, Y) ∈ \overline J^{2,-}_L v_norm(0)`, then
`(-P_y, Y) ∈ \overline J^{2,-}_{y0+L} v(y0)`.
-/
theorem closedSubjet_of_closedSubjet_normalizedRightOfBlockGradient
    {L : Set (Point n)} {v : Point n -> Real} {y0 : Point n} {P : BlockPoint n}
    {Y : Hessian n}
    (hJ : ({ gradient := 0, hessian := Y } : Jet n) ∈
      ClosedSubjet L (normalizedRightOfBlockGradient (n := n) v y0 P) 0) :
    ({ gradient := -blockPointRight P, hessian := Y } : Jet n) ∈
      ClosedSubjet ((fun y : Point n => y0 + y) '' L) v y0 := by
  let p : Point n := blockPointRight P
  let vComp : Point n -> Real := fun y => v (y0 + y)
  let φ : Point n -> Real := fun y => -v y0 + dotProduct p y
  let A : Point n -> Jet n := fun _y => ({ gradient := p, hessian := 0 } : Jet n)
  have hfun :
      normalizedRightOfBlockGradient (n := n) v y0 P = fun y => vComp y + φ y := by
    funext y
    simp [normalizedRightOfBlockGradient, vComp, φ, p]
    ring
  have hφ :
      ∀ y : Point n, y ∈ L -> HasSecondOrderExpansionWithin L φ y (A y) := by
    intro y _hy
    have hquad :=
      hasSecondOrderExpansionWithin_quadraticModel_recenter
        (C := L) (x0 := 0) (r := -v y0) (p := p) (X := (0 : Hessian n)) y
    have hφ_eq :
        φ =
          fun z : Point n => quadraticModel 0 (-v y0) p (0 : Hessian n) z := by
      funext z
      simp [φ, quadraticModel]
    have hA_eq :
        A y = quadraticModelJetAt 0 p (0 : Hessian n) y := by
      apply (Jet.equivProd n).injective
      simp [A, Jet.equivProd, quadraticModelJetAt]
    simpa [hφ_eq, hA_eq] using hquad
  have hφ_cont : Continuous φ :=
    continuous_const.add (continuous_const.dotProduct continuous_id)
  have hA_cont : Continuous A := continuous_const
  have hL :
      ({ gradient := -blockPointRight P, hessian := Y } : Jet n) ∈ ClosedSubjet L vComp 0 := by
    have hshift :
        ({ gradient := 0, hessian := Y } : Jet n) - A 0 ∈ ClosedSubjet L vComp 0 :=
      closedSubjet_sub_of_add_hasSecondOrderExpansionWithin
        (C := L) (u := vComp) (φ := φ) (x := 0)
        (J := ({ gradient := 0, hessian := Y } : Jet n))
        (A := A) hφ hφ_cont hA_cont (by simpa [hfun] using hJ)
    have hjet :
        ({ gradient := 0, hessian := Y } : Jet n) - A 0 =
          ({ gradient := -blockPointRight P, hessian := Y } : Jet n) := by
      apply (Jet.equivProd n).injective
      simp [A, p, Jet.equivProd]
    simpa [hjet, vComp] using hshift
  simpa [vComp] using closedSubjet_translate_add_left (x0 := y0) (x := 0) hL

/--
Upper semicontinuity is preserved by translating the argument and subtracting
the affine part used in the normalized maximum-principle reduction.
-/
theorem upperSemicontinuousOn_normalizedLeftOfBlockGradient
    {K : Set (Point n)} {u : Point n -> Real} {x0 : Point n} {P : BlockPoint n}
    (hu : UpperSemicontinuousOn u ((fun x : Point n => x0 + x) '' K)) :
    UpperSemicontinuousOn (normalizedLeftOfBlockGradient (n := n) u x0 P) K := by
  let T : Point n -> Point n := fun x => x0 + x
  have hTcont : ContinuousOn T K := (continuous_const.add continuous_id).continuousOn
  have hTmap : Set.MapsTo T K ((fun x : Point n => x0 + x) '' K) := by
    intro x hx
    exact ⟨x, hx, rfl⟩
  have hucomp :
      UpperSemicontinuousOn (fun x : Point n => u (x0 + x)) K := by
    simpa [T, Function.comp_def] using hu.comp hTcont hTmap
  have haffCont :
      ContinuousOn (fun x : Point n => -u x0 - dotProduct (blockPointLeft P) x) K := by
    exact (continuous_const.sub (continuous_const.dotProduct continuous_id)).continuousOn
  have haffUpper :
      UpperSemicontinuousOn
        (fun x : Point n => -u x0 - dotProduct (blockPointLeft P) x) K :=
    (continuousOn_iff_lower_upperSemicontinuousOn.mp haffCont).2
  have hsum := hucomp.add haffUpper
  convert hsum using 1
  ext x
  simp [normalizedLeftOfBlockGradient]
  ring

/--
Lower semicontinuity is preserved by translating the argument and adding the
affine part used in the normalized maximum-principle reduction.
-/
theorem lowerSemicontinuousOn_normalizedRightOfBlockGradient
    {L : Set (Point n)} {v : Point n -> Real} {y0 : Point n} {P : BlockPoint n}
    (hv : LowerSemicontinuousOn v ((fun y : Point n => y0 + y) '' L)) :
    LowerSemicontinuousOn (normalizedRightOfBlockGradient (n := n) v y0 P) L := by
  let T : Point n -> Point n := fun y => y0 + y
  have hTcont : ContinuousOn T L := (continuous_const.add continuous_id).continuousOn
  have hTmap : Set.MapsTo T L ((fun y : Point n => y0 + y) '' L) := by
    intro y hy
    exact ⟨y, hy, rfl⟩
  have hvcomp :
      LowerSemicontinuousOn (fun y : Point n => v (y0 + y)) L := by
    simpa [T, Function.comp_def] using hv.comp hTcont hTmap
  have haffCont :
      ContinuousOn (fun y : Point n => -v y0 + dotProduct (blockPointRight P) y) L := by
    exact (continuous_const.add (continuous_const.dotProduct continuous_id)).continuousOn
  have haffLower :
      LowerSemicontinuousOn
        (fun y : Point n => -v y0 + dotProduct (blockPointRight P) y) L :=
    (continuousOn_iff_lower_upperSemicontinuousOn.mp haffCont).1
  have hsum := hvcomp.add haffLower
  convert hsum using 1
  ext y
  simp [normalizedRightOfBlockGradient]
  ring

/--
The difference of the two normalized functions is the original doubled
difference with the base value and affine test part subtracted.
-/
theorem normalizedLeft_sub_normalizedRight_eq
    {u v : Point n -> Real} {x0 y0 : Point n} {P : BlockPoint n}
    (x y : Point n) :
    normalizedLeftOfBlockGradient (n := n) u x0 P x -
        normalizedRightOfBlockGradient (n := n) v y0 P y =
      (u (x0 + x) - v (y0 + y)) - (u x0 - v y0) -
        dotProduct P (doubledPointToBlockPoint (x, y)) := by
  simp [normalizedLeftOfBlockGradient, normalizedRightOfBlockGradient,
    doubledPointToBlockPoint, blockPointLeft, blockPointRight, dotProduct,
    Fintype.sum_sum_type]
  ring

/--
A maximum of the doubled difference minus a quadratic expansion gives the
normalized pointwise quadratic bound.

In standard mathematical terms, suppose `(x0, y0)` is a maximum, relative to
the translated set
`{(x0 + x, y0 + y) | x ∈ K, y ∈ L}`, of

`(x, y) ↦ u(x) - v(y)
  - [φ0 + ⟪P, (x - x0, y - y0)⟫
      + (1 / 2) * ⟪A(x - x0, y - y0), (x - x0, y - y0)⟫]`.

Then for every `x ∈ K` and `y ∈ L`,

`u(x0 + x) - u(x0) - ⟪P_x, x⟫
 - [v(y0 + y) - v(y0) + ⟪P_y, y⟫]
 ≤ (1 / 2) * ⟪A(x, y), (x, y)⟫`.
-/
theorem normalized_pointwise_bound_of_isMaxOn_doubledQuadraticExpansionAt
    {K L : Set (Point n)} {u v : Point n -> Real}
    {x0 y0 : Point n} {φ0 : Real} {P : BlockPoint n} {A : BlockHessian n}
    (hmax : IsMaxOn
      (fun q : DoubledPoint n =>
        u q.1 - v q.2 - doubledQuadraticExpansionAt (n := n) x0 y0 φ0 P A q)
      {q : DoubledPoint n | q.1 - x0 ∈ K ∧ q.2 - y0 ∈ L}
      (x0, y0)) :
    ∀ x : Point n, x ∈ K -> ∀ y : Point n, y ∈ L ->
      normalizedLeftOfBlockGradient (n := n) u x0 P x -
          normalizedRightOfBlockGradient (n := n) v y0 P y <=
        blockQuadraticModel A (doubledPointToBlockPoint (x, y)) := by
  intro x hx y hy
  have hmem :
      (x0 + x, y0 + y) ∈
        {q : DoubledPoint n | q.1 - x0 ∈ K ∧ q.2 - y0 ∈ L} := by
    constructor <;>
      simpa [add_sub_cancel_left] using (by assumption)
  have hineq := hmax hmem
  change
    u (x0 + x) - v (y0 + y) -
        doubledQuadraticExpansionAt (n := n) x0 y0 φ0 P A (x0 + x, y0 + y) <=
      u x0 - v y0 - doubledQuadraticExpansionAt (n := n) x0 y0 φ0 P A (x0, y0)
    at hineq
  have hnorm :=
    normalizedLeft_sub_normalizedRight_eq (n := n)
      (u := u) (v := v) (x0 := x0) (y0 := y0) (P := P) x y
  have hbase :
      doubledQuadraticExpansionAt (n := n) x0 y0 φ0 P A (x0, y0) = φ0 := by
    simp [doubledQuadraticExpansionAt, blockQuadraticModel, doubledPointToBlockPoint, dotProduct]
  have hpoint :
      doubledQuadraticExpansionAt (n := n) x0 y0 φ0 P A (x0 + x, y0 + y) =
        φ0 + dotProduct P (doubledPointToBlockPoint (x, y)) +
          blockQuadraticModel A (doubledPointToBlockPoint (x, y)) := by
    simp [doubledQuadraticExpansionAt, add_sub_cancel_left]
  rw [hbase, hpoint] at hineq
  rw [hnorm]
  linarith

/--
Restrict a doubled maximum to a translated product set.

In standard mathematical terms, if `(x0, y0)` is a maximum point of `f` on a
set `P`, and every pair `(x, y)` satisfying `x - x0 ∈ K` and `y - y0 ∈ L`
belongs to `P`, then `(x0, y0)` is a maximum point of `f` on that translated
product set.
-/
theorem isMaxOn_translated_product_of_isMaxOn_superset
    {K L : Set (Point n)} {P : Set (DoubledPoint n)}
    {f : DoubledPoint n -> Real} {x0 y0 : Point n}
    (hmax : IsMaxOn f P (x0, y0))
    (hsubset :
      {q : DoubledPoint n | q.1 - x0 ∈ K ∧ q.2 - y0 ∈ L} ⊆ P) :
    IsMaxOn f {q : DoubledPoint n | q.1 - x0 ∈ K ∧ q.2 - y0 ∈ L} (x0, y0) := by
  intro q hq
  exact hmax (hsubset hq)

/--
The semiconvexity inequality on `R^n × R^n`, written in block coordinates.

In quantified mathematical form, a function `F : R^n × R^n -> R` satisfies
`BlockCoordinateSemiconvexOn lambda C F` if for every `x, y ∈ C` and every
real numbers `a, b` with `0 ≤ a`, `0 ≤ b`, and `a + b = 1`, whenever
`a x + b y ∈ C`, one has

`F (a x + b y) ≤
 a F x + b F y + (lambda / 2) a b |x - y|^2`.
-/
def BlockCoordinateSemiconvexOn (lambda : Real) (C : Set (BlockPoint n))
    (F : BlockPoint n -> Real) : Prop :=
  ∀ x : BlockPoint n, x ∈ C ->
  ∀ y : BlockPoint n, y ∈ C ->
  ∀ a b : Real, 0 <= a -> 0 <= b -> a + b = 1 ->
    a • x + b • y ∈ C ->
      F (a • x + b • y) <=
        a * F x + b * F y +
          (lambda / 2) * a * b * dotProduct (x - y) (x - y)

/--
Writing a block-coordinate semiconvex function in `R^(n+n)` coordinates
preserves the semiconvexity inequality.

In quantified mathematical form, if `F : R^n × R^n -> R` satisfies the
semiconvexity inequality with constant `lambda` on all of `R^n × R^n`, then
`z ↦ F(z_1, z_2)`, regarded as a function on `R^(n+n)`, satisfies the same
semiconvexity inequality with constant `lambda` on all of `R^(n+n)`.
-/
theorem BlockCoordinateSemiconvexOn.coordinateSemiconvexOn_blockFunctionToPointFunction
    {lambda : Real} {F : BlockPoint n -> Real}
    (hsemi : BlockCoordinateSemiconvexOn lambda Set.univ F) :
    CoordinateSemiconvexOn lambda Set.univ
      (blockFunctionToPointFunction (n := n) F) := by
  intro x _hx y _hy a b ha hb hab _hcombo
  have hblock := hsemi
    (pointSumEquivBlockPoint n x) trivial
    (pointSumEquivBlockPoint n y) trivial
    a b ha hb hab trivial
  have hdot :
      dotProduct
          (pointSumEquivBlockPoint n x - pointSumEquivBlockPoint n y)
          (pointSumEquivBlockPoint n x - pointSumEquivBlockPoint n y) =
        dotProduct (x - y) (x - y) := by
    simpa using
      dotProduct_pointSumEquivBlockPoint (n := n) (x - y) (x - y)
  simpa [blockFunctionToPointFunction, ← pointSumEquivBlockPoint_add,
    ← pointSumEquivBlockPoint_smul, hdot] using hblock

/--
Block-coordinate semiconvexity on all of `R^n × R^n` implies continuity.

In standard mathematical terms, this is the continuity of a semiconvex
function on the finite-dimensional product space.
-/
theorem BlockCoordinateSemiconvexOn.continuous_univ
    {lambda : Real} {F : BlockPoint n -> Real}
    (hsemi : BlockCoordinateSemiconvexOn lambda Set.univ F) :
    Continuous F := by
  have hcoord : Continuous (blockFunctionToPointFunction (n := n) F) :=
    hsemi.coordinateSemiconvexOn_blockFunctionToPointFunction.continuous_univ
  have hsymm : Continuous ((pointSumEquivBlockPoint n).symm : BlockPoint n -> Point (n + n)) := by
    continuity
  have hF : F = (blockFunctionToPointFunction (n := n) F) ∘ (pointSumEquivBlockPoint n).symm := by
    funext q
    simp [blockFunctionToPointFunction]
  rw [hF]
  exact hcoord.comp hsymm

/--
If two functions on `R^n` are semiconvex with the same constant, then their
sum as a function on `R^n × R^n` is semiconvex with that same constant.

In standard mathematical terms, if `f` and `g` satisfy the semiconvexity
inequality with constant `lambda`, then
`(x, y) ↦ f(x) + g(y)` satisfies the semiconvexity inequality with constant
`lambda` on the product space, because
`|(x_1, y_1) - (x_2, y_2)|^2 = |x_1 - x_2|^2 + |y_1 - y_2|^2`.
-/
theorem BlockCoordinateSemiconvexOn.left_right_add
    {lambda : Real} {f g : Point n -> Real}
    (hf : CoordinateSemiconvexOn lambda Set.univ f)
    (hg : CoordinateSemiconvexOn lambda Set.univ g) :
    BlockCoordinateSemiconvexOn lambda Set.univ
      (fun q : BlockPoint n => f (blockPointLeft q) + g (blockPointRight q)) := by
  intro x _hx y _hy a b ha hb hab _hcombo
  have hleft := hf (blockPointLeft x) trivial (blockPointLeft y) trivial a b ha hb hab trivial
  have hright := hg (blockPointRight x) trivial (blockPointRight y) trivial a b ha hb hab trivial
  have hleft_combo : blockPointLeft (a • x + b • y) =
      a • blockPointLeft x + b • blockPointLeft y := by
    rfl
  have hright_combo : blockPointRight (a • x + b • y) =
      a • blockPointRight x + b • blockPointRight y := by
    rfl
  have hdot :
      dotProduct (x - y) (x - y) =
        dotProduct (blockPointLeft x - blockPointLeft y) (blockPointLeft x - blockPointLeft y) +
          dotProduct (blockPointRight x - blockPointRight y)
            (blockPointRight x - blockPointRight y) := by
    rw [Matrix.dotProduct_block]
    rfl
  change f (blockPointLeft (a • x + b • y)) + g (blockPointRight (a • x + b • y)) <=
    a * (f (blockPointLeft x) + g (blockPointRight x)) +
      b * (f (blockPointLeft y) + g (blockPointRight y)) +
        lambda / 2 * a * b * dotProduct (x - y) (x - y)
  rw [hleft_combo, hright_combo, hdot]
  nlinarith

end ViscositySolns
