/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Analysis.SemiconvexJensen.Aleksandrov.Basic.Core

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Strictification and jet bridges for the Aleksandrov--Jensen argument (CoordinateQuartic)

Part of the quartic strictification, compact Hessian, and jet transport
development used before the contact-set and approximation arguments in
`SemiconvexJensen`. Split from `Strictification.lean`; see the umbrella
module docstring.
-/

@[expose] public noncomputable section

open scoped ContDiff MatrixOrder Topology
open scoped ENNReal

open ContinuousLinearMap MeasureTheory

namespace ViscositySolns

variable {n : Nat}

/--
If `K` has positive Lebesgue measure and the set where `P` fails has measure
zero, then some point of `K` satisfies `P`.
-/
theorem exists_mem_of_measure_pos_of_measure_compl_property_zero
    {K : Set (Point n)} {P : Point n -> Prop}
    (hKpos : 0 < volume K)
    (hnull : volume {x : Point n | ¬ P x} = 0) :
    ∃ x : Point n, x ∈ K ∧ P x := by
  by_contra hnone
  have hsubset : K ⊆ {x : Point n | ¬ P x} := by
    intro x hxK hPx
    exact hnone ⟨x, hxK, hPx⟩
  have hmeasure_le : volume K <= volume {x : Point n | ¬ P x} :=
    measure_mono hsubset
  rw [hnull] at hmeasure_le
  exact (not_le_of_gt hKpos) hmeasure_le

/--
If `K` has positive Lebesgue measure and the subset of `K` where `P` fails has
measure zero, then some point of `K` satisfies `P`.
-/
theorem exists_mem_of_measure_pos_of_measure_inter_compl_property_zero
    {K : Set (Point n)} {P : Point n -> Prop}
    (hKpos : 0 < volume K)
    (hnull : volume (K ∩ {x : Point n | ¬ P x}) = 0) :
    ∃ x : Point n, x ∈ K ∧ P x := by
  by_contra hnone
  have hsubset : K ⊆ K ∩ {x : Point n | ¬ P x} := by
    intro x hxK
    refine ⟨hxK, ?_⟩
    intro hPx
    exact hnone ⟨x, hxK, hPx⟩
  have hmeasure_le : volume K <= volume (K ∩ {x : Point n | ¬ P x}) :=
    measure_mono hsubset
  rw [hnull] at hmeasure_le
  exact (not_le_of_gt hKpos) hmeasure_le

/--
The coordinate quartic used in the source proof to make the maximum strict.

In quantified mathematical form, this is
`x ↦ (∑ i, x_i^2)^2`.
-/
def coordinateQuartic (x : Point n) : Real :=
  (dotProduct x x) ^ 2

@[simp]
theorem coordinateQuartic_zero : coordinateQuartic (0 : Point n) = 0 := by
  simp [coordinateQuartic]

/--
The coordinate quartic is continuous.
-/
theorem continuous_coordinateQuartic :
    Continuous (coordinateQuartic (n := n)) := by
  exact
    ((continuous_id : Continuous fun x : Point n => x).dotProduct continuous_id).pow 2

/--
The coordinate quadratic identity underlying the quartic estimate.

In quantified mathematical form, if `a + b = 1`, then

`∑ i (a x_i + b y_i)^2 + a b ∑ i (x_i - y_i)^2
 = a ∑ i x_i^2 + b ∑ i y_i^2`.
-/
theorem dotProduct_self_convex_combination
    (x y : Point n) {a b : Real} (hab : a + b = 1) :
    dotProduct (a • x + b • y) (a • x + b • y) +
        a * b * dotProduct (x - y) (x - y) =
      a * dotProduct x x + b * dotProduct y y := by
  have h :=
    quadraticModel_scalar_identity_convex_combination
      (n := n) (lambda := 2) x y (a := a) (b := b) hab
  simp [quadraticModel, Matrix.smul_mulVec, Matrix.one_mulVec, smul_dotProduct] at h ⊢
  nlinarith

/--
The defect in the coordinate quartic is bounded on a closed ball.

In quantified mathematical form, suppose `0 ≤ r`, `x ∈ closedBall 0 r`,
`y ∈ closedBall 0 r`, `a ≥ 0`, `b ≥ 0`, and `a + b = 1`. Then

`a (∑ i x_i^2)^2 + b (∑ i y_i^2)^2
 - (∑ i (a x_i + b y_i)^2)^2`

is at most

`(4 n^2 r^2 + 2 n r^2) a b ∑ i (x_i - y_i)^2`.
-/
theorem coordinateQuartic_convex_combination_defect_le_closedBall
    {r : Real} (hr : 0 <= r) {x y : Point n}
    (hx : x ∈ Metric.closedBall (0 : Point n) r)
    (hy : y ∈ Metric.closedBall (0 : Point n) r)
    {a b : Real} (ha : 0 <= a) (hb : 0 <= b) (hab : a + b = 1) :
    a * coordinateQuartic x + b * coordinateQuartic y -
        coordinateQuartic (a • x + b • y) <=
      (4 * (n : Real) ^ 2 * r ^ 2 + 2 * (n : Real) * r ^ 2) *
        a * b * dotProduct (x - y) (x - y) := by
  let A : Real := dotProduct x x
  let C : Real := dotProduct y y
  let D : Real := dotProduct (x - y) (x - y)
  let S : Real := a * A + b * C
  let Z : Real := dotProduct (a • x + b • y) (a • x + b • y)
  have hD_nonneg : 0 <= D := by
    dsimp [D, dotProduct]
    exact Finset.sum_nonneg fun i _hi => by
      simpa [sq] using sq_nonneg ((x - y) i)
  have hab_nonneg : 0 <= a * b := mul_nonneg ha hb
  have hxnorm : ‖x‖ <= r := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hx
  have hynorm : ‖y‖ <= r := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hy
  have hA_nonneg : 0 <= A := by
    dsimp [A, dotProduct]
    exact Finset.sum_nonneg fun i _hi => by
      simpa [sq] using sq_nonneg (x i)
  have hC_nonneg : 0 <= C := by
    dsimp [C, dotProduct]
    exact Finset.sum_nonneg fun i _hi => by
      simpa [sq] using sq_nonneg (y i)
  have hA_le : A <= (n : Real) * r ^ 2 := by
    have hnorm_sq : ‖x‖ ^ 2 <= r ^ 2 := by
      exact sq_le_sq.mpr (by simpa [abs_of_nonneg (norm_nonneg x), abs_of_nonneg hr] using hxnorm)
    calc
      A = dotProduct x x := rfl
      _ <= (n : Real) * ‖x‖ ^ 2 := dotProduct_self_le_card_mul_norm_sq x
      _ <= (n : Real) * r ^ 2 := by
        gcongr
  have hC_le : C <= (n : Real) * r ^ 2 := by
    have hnorm_sq : ‖y‖ ^ 2 <= r ^ 2 := by
      exact sq_le_sq.mpr (by simpa [abs_of_nonneg (norm_nonneg y), abs_of_nonneg hr] using hynorm)
    calc
      C = dotProduct y y := rfl
      _ <= (n : Real) * ‖y‖ ^ 2 := dotProduct_self_le_card_mul_norm_sq y
      _ <= (n : Real) * r ^ 2 := by
        gcongr
  have hS_le : S <= (n : Real) * r ^ 2 := by
    dsimp [S]
    nlinarith
  have hZ_relation : Z + a * b * D = S := by
    dsimp [Z, D, S, A, C]
    exact dotProduct_self_convex_combination (n := n) x y (a := a) (b := b) hab
  have hZ_eq : Z = S - a * b * D := by linarith
  have hAC :
      A - C = dotProduct (x + y) (x - y) := by
    dsimp [A, C]
    simp only [dotProduct_sub, add_dotProduct]
    rw [dotProduct_comm y x]
    ring
  have hsum_norm : ‖x + y‖ <= 2 * r := by
    calc
      ‖x + y‖ <= ‖x‖ + ‖y‖ := norm_add_le x y
      _ <= r + r := by gcongr
      _ = 2 * r := by ring
  have hAC_abs :
      |A - C| <= (n : Real) * (2 * r) * ‖x - y‖ := by
    calc
      |A - C| = |dotProduct (x + y) (x - y)| := by rw [hAC]
      _ <= (n : Real) * ‖x + y‖ * ‖x - y‖ :=
        abs_dotProduct_le_card_mul_norm_mul_norm (n := n) (x + y) (x - y)
      _ <= (n : Real) * (2 * r) * ‖x - y‖ := by
        gcongr
  have hAC_sq_norm :
      (A - C) ^ 2 <= ((n : Real) * (2 * r) * ‖x - y‖) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg (A - C)) hAC_abs 2
  have hAC_sq :
      (A - C) ^ 2 <=
        (4 * (n : Real) ^ 2 * r ^ 2) * D := by
    calc
      (A - C) ^ 2 <= ((n : Real) * (2 * r) * ‖x - y‖) ^ 2 := hAC_sq_norm
      _ = (4 * (n : Real) ^ 2 * r ^ 2) * ‖x - y‖ ^ 2 := by ring
      _ <= (4 * (n : Real) ^ 2 * r ^ 2) * D := by
        have hnormD : ‖x - y‖ ^ 2 <= D := by
          simpa [D] using norm_sq_le_dotProduct_self (x - y)
        gcongr
  have hvariance :
      a * A ^ 2 + b * C ^ 2 - S ^ 2 = a * b * (A - C) ^ 2 := by
    have hb_eq : b = 1 - a := by linarith
    dsimp [S]
    subst b
    ring
  have hdefect_eq :
      a * A ^ 2 + b * C ^ 2 - Z ^ 2 =
        a * b * (A - C) ^ 2 + 2 * a * b * D * S - (a * b * D) ^ 2 := by
    calc
      a * A ^ 2 + b * C ^ 2 - Z ^ 2 =
          a * A ^ 2 + b * C ^ 2 - (S - a * b * D) ^ 2 := by
        rw [hZ_eq]
      _ = (a * A ^ 2 + b * C ^ 2 - S ^ 2) +
            2 * a * b * D * S - (a * b * D) ^ 2 := by
        ring
      _ = a * b * (A - C) ^ 2 + 2 * a * b * D * S - (a * b * D) ^ 2 := by
        rw [hvariance]
  have hterm1 :
      a * b * (A - C) ^ 2 <=
        a * b * ((4 * (n : Real) ^ 2 * r ^ 2) * D) := by
    exact mul_le_mul_of_nonneg_left hAC_sq hab_nonneg
  have hterm2 :
      2 * a * b * D * S <=
        2 * a * b * D * ((n : Real) * r ^ 2) := by
    have hcoeff : 0 <= 2 * a * b * D := by positivity
    exact mul_le_mul_of_nonneg_left hS_le hcoeff
  have hneg : - (a * b * D) ^ 2 <= 0 := by
    exact neg_nonpos.mpr (sq_nonneg (a * b * D))
  dsimp [coordinateQuartic, A, C, Z] at hdefect_eq ⊢
  nlinarith only [hdefect_eq, hterm1, hterm2, hneg]

/--
The negative coordinate quartic is coordinate semiconvex on a closed ball.

In quantified mathematical form, if `0 ≤ r`, then the function

`x ↦ - (∑ i x_i^2)^2`

satisfies the coordinate semiconvexity inequality on `closedBall 0 r` with
constant

`2 * (4 n^2 r^2 + 2 n r^2)`.
-/
theorem coordinateSemiconvexOn_neg_coordinateQuartic_closedBall
    {r : Real} (hr : 0 <= r) :
    CoordinateSemiconvexOn
      (2 * (4 * (n : Real) ^ 2 * r ^ 2 + 2 * (n : Real) * r ^ 2))
      (Metric.closedBall (0 : Point n) r)
      (fun x : Point n => -coordinateQuartic x) := by
  intro x hx y hy a b ha hb hab hcombo
  have hdefect :=
    coordinateQuartic_convex_combination_defect_le_closedBall
      (n := n) hr hx hy ha hb hab
  nlinarith

/--
The coordinate quartic is smooth.
-/
theorem contDiff_coordinateQuartic :
    ContDiff Real ⊤ (coordinateQuartic (n := n)) := by
  change ContDiff Real ⊤ fun x : Point n => (∑ i : Fin n, x i * x i) ^ 2
  fun_prop

/--
The coordinate square-sum `x ↦ ∑ i, x_i^2`.
-/
def coordinateSquareSum (x : Point n) : Real :=
  ∑ i : Fin n, x i * x i

/--
The first Fréchet derivative of the coordinate square-sum, written as a
continuous linear map.
-/
def coordinateSquareSumFDeriv (x : Point n) : Point n →L[Real] Real :=
  ∑ i : Fin n, ((x i) • (ContinuousLinearMap.proj i : Point n →L[Real] Real) +
    (x i) • (ContinuousLinearMap.proj i : Point n →L[Real] Real))

/--
At the origin, the coordinate square-sum has zero first Fréchet derivative.
-/
theorem hasFDerivWithinAt_coordinateSquareSum_zero :
    HasFDerivWithinAt (coordinateSquareSum (n := n))
      (0 : Point n →L[Real] Real) Set.univ 0 := by
  change HasFDerivWithinAt (fun x : Point n => ∑ i : Fin n, x i * x i)
    (0 : Point n →L[Real] Real) Set.univ 0
  simpa using
    (HasFDerivWithinAt.fun_sum (u := (Finset.univ : Finset (Fin n)))
      (A := fun i x => x i * x i)
      (A' := fun _ => (0 : Point n →L[Real] Real))
      (s := Set.univ) (x := (0 : Point n)) (fun i _hi => by
        have hcoord : HasFDerivWithinAt (fun x : Point n => x i)
            (ContinuousLinearMap.proj i : Point n →L[Real] Real) Set.univ 0 := by
          exact (ContinuousLinearMap.proj i : Point n →L[Real] Real).hasFDerivWithinAt
        (convert hcoord.mul hcoord using 1; simp)))

/--
The coordinate formula for the first derivative of the coordinate square-sum
vanishes at the origin.
-/
@[simp]
theorem coordinateSquareSumFDeriv_zero :
    coordinateSquareSumFDeriv (n := n) 0 = 0 := by
  ext v
  simp [coordinateSquareSumFDeriv]

/--
The coordinate formula for the first derivative of the coordinate square-sum is
differentiable at the origin.
-/
theorem differentiableWithinAt_coordinateSquareSumFDeriv_zero :
    DifferentiableWithinAt Real (coordinateSquareSumFDeriv (n := n)) Set.univ 0 := by
  unfold coordinateSquareSumFDeriv
  fun_prop

/--
The derivative of the coordinate quartic, written in terms of the square-sum
and its derivative.
-/
def coordinateQuarticFDeriv (x : Point n) : Point n →L[Real] Real :=
  coordinateSquareSum x • coordinateSquareSumFDeriv x +
    coordinateSquareSum x • coordinateSquareSumFDeriv x

/--
At the origin, the derivative of the coordinate-quartic derivative formula is
zero.
-/
theorem hasFDerivWithinAt_coordinateQuarticFDeriv_zero :
    HasFDerivWithinAt (coordinateQuarticFDeriv (n := n))
      (0 : Point n →L[Real] (Point n →L[Real] Real)) Set.univ 0 := by
  have hs := hasFDerivWithinAt_coordinateSquareSum_zero (n := n)
  have hD := differentiableWithinAt_coordinateSquareSumFDeriv_zero (n := n)
  have hterm : HasFDerivWithinAt
      (fun x : Point n => coordinateSquareSum x • coordinateSquareSumFDeriv x)
      (0 : Point n →L[Real] (Point n →L[Real] Real)) Set.univ 0 := by
    convert hs.smul hD.hasFDerivWithinAt using 1
    simp [coordinateSquareSum]
  convert hterm.add hterm using 1
  all_goals first | rfl | simp

/--
At every point, the coordinate quartic has the first Fréchet derivative given
by `coordinateQuarticFDeriv`.
-/
theorem hasFDerivWithinAt_coordinateQuartic (x : Point n) :
    HasFDerivWithinAt (coordinateQuartic (n := n)) (coordinateQuarticFDeriv x)
      Set.univ x := by
  have hsum : HasFDerivWithinAt (coordinateSquareSum (n := n))
      (coordinateSquareSumFDeriv x) Set.univ x := by
    change HasFDerivWithinAt (fun y : Point n => ∑ i : Fin n, y i * y i)
      (coordinateSquareSumFDeriv x) Set.univ x
    simpa [coordinateSquareSumFDeriv] using
      (HasFDerivWithinAt.fun_sum (u := (Finset.univ : Finset (Fin n)))
        (A := fun i y => y i * y i)
        (A' := fun i =>
          ((x i) • (ContinuousLinearMap.proj i : Point n →L[Real] Real) +
            (x i) • (ContinuousLinearMap.proj i : Point n →L[Real] Real)))
        (s := Set.univ) (x := x) (fun i _hi => by
          have hcoord : HasFDerivWithinAt (fun y : Point n => y i)
              (ContinuousLinearMap.proj i : Point n →L[Real] Real) Set.univ x := by
            exact (ContinuousLinearMap.proj i : Point n →L[Real] Real).hasFDerivWithinAt
          exact hcoord.mul hcoord))
  have hquartic := hsum.mul hsum
  convert hquartic using 1
  all_goals first
    | rfl
    | (funext y; simp [coordinateQuartic, coordinateSquareSum, dotProduct, pow_two])

/--
At the origin, the coordinate quartic has zero first Fréchet derivative.
-/
theorem fderivWithin_coordinateQuartic_univ_zero :
    fderivWithin Real (coordinateQuartic (n := n)) Set.univ (0 : Point n) = 0 := by
  have h := hasFDerivWithinAt_coordinateQuartic (n := n) (0 : Point n)
  have hzero : coordinateQuarticFDeriv (n := n) 0 = 0 := by
    ext v
    simp [coordinateQuarticFDeriv, coordinateSquareSum]
  simpa [hzero] using h.fderivWithin (uniqueDiffOn_univ (0 : Point n) trivial)

/--
At the origin, the first-derivative map of the coordinate quartic has zero
Fréchet derivative.
-/
theorem hasFDerivWithinAt_fderivWithin_coordinateQuartic_univ_zero :
    HasFDerivWithinAt
      (fderivWithin Real (coordinateQuartic (n := n)) Set.univ)
      (0 : Point n →L[Real] (Point n →L[Real] Real)) Set.univ 0 := by
  have hformula :
      fderivWithin Real (coordinateQuartic (n := n)) Set.univ =
        coordinateQuarticFDeriv (n := n) := by
    funext x
    exact (hasFDerivWithinAt_coordinateQuartic (n := n) x).fderivWithin
      (uniqueDiffOn_univ x trivial)
  simpa [hformula] using hasFDerivWithinAt_coordinateQuarticFDeriv_zero (n := n)

/--
At the origin, the second Fréchet derivative of the coordinate quartic is zero.
-/
theorem fderivWithin_fderivWithin_coordinateQuartic_univ_zero :
    fderivWithin Real
      (fderivWithin Real (coordinateQuartic (n := n)) Set.univ)
      Set.univ (0 : Point n) = 0 := by
  exact (hasFDerivWithinAt_fderivWithin_coordinateQuartic_univ_zero (n := n)).fderivWithin
    (uniqueDiffOn_univ (0 : Point n) trivial)

/--
The coordinate quartic is strictly positive away from the origin.
-/
theorem coordinateQuartic_pos_of_ne_zero {x : Point n} (hx : x ≠ 0) :
    0 < coordinateQuartic x := by
  have hnorm_pos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hnorm_sq_pos : 0 < ‖x‖ ^ 2 := sq_pos_of_pos hnorm_pos
  have hdot_ge : ‖x‖ ^ 2 <= dotProduct x x := norm_sq_le_dotProduct_self x
  have hdot_pos : 0 < dotProduct x x := lt_of_lt_of_le hnorm_sq_pos hdot_ge
  exact sq_pos_of_pos hdot_pos

/--
The coordinate quartic is fourth order at the origin.

In quantified mathematical form,

`(∑ i, x_i^2)^2 = o(|x|^2)` as `x -> 0`.
-/
theorem coordinateQuartic_isLittleO_norm_sq :
    (fun x : Point n => coordinateQuartic x) =o[𝓝 (0 : Point n)]
      (fun x : Point n => ‖x‖ ^ 2) := by
  have hbig :
      (fun x : Point n => coordinateQuartic x) =O[𝓝 (0 : Point n)]
        (fun x : Point n => ‖x‖ ^ 4) := by
    refine Asymptotics.IsBigO.of_bound ((n : Real) ^ 2) ?_
    filter_upwards with x
    have hdot : dotProduct x x <= (n : Real) * ‖x‖ ^ 2 :=
      dotProduct_self_le_card_mul_norm_sq x
    have hdot_nonneg : 0 <= dotProduct x x := by
      rw [dotProduct]
      exact Finset.sum_nonneg fun i _hi => by
        simpa [sq] using sq_nonneg (x i)
    have hsq :
        (dotProduct x x) ^ 2 <= ((n : Real) * ‖x‖ ^ 2) ^ 2 :=
      pow_le_pow_left₀ hdot_nonneg hdot 2
    have hquartic_nonneg : 0 <= coordinateQuartic x := by
      exact sq_nonneg (dotProduct x x)
    calc
      ‖coordinateQuartic x‖ = coordinateQuartic x := by
        rw [Real.norm_eq_abs, abs_of_nonneg hquartic_nonneg]
      _ = (dotProduct x x) ^ 2 := rfl
      _ <= ((n : Real) * ‖x‖ ^ 2) ^ 2 := hsq
      _ = (n : Real) ^ 2 * ‖x‖ ^ 4 := by ring
      _ = (n : Real) ^ 2 * ‖‖x‖ ^ 4‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg x) 4)]
  have hsmall :
      (fun x : Point n => ‖x‖ ^ 4) =o[𝓝 (0 : Point n)]
        (fun x : Point n => ‖x‖ ^ 2) :=
    Asymptotics.isLittleO_norm_pow_norm_pow (E' := Point n)
      (by norm_num : 2 < 4)
  exact hbig.trans_isLittleO hsmall

/--
At the origin, the coordinate quartic has zero value, zero gradient, and zero
Hessian in the second-order expansion sense used by semijets.
-/
theorem hasSecondOrderExpansionWithin_coordinateQuartic_zero
    {C : Set (Point n)} :
    HasSecondOrderExpansionWithin C (coordinateQuartic (n := n)) 0
      ({ gradient := 0, hessian := 0 } : Jet n) := by
  refine ⟨coordinateQuartic, ?_, ?_⟩
  · have h := coordinateQuartic_isLittleO_norm_sq (n := n)
    simpa [SemijetRemainder] using h.mono (nhdsWithin_le_nhds (s := C))
  · filter_upwards with x
    simp [coordinateQuartic, quadraticModel]

/--
The canonical second-order jet of the coordinate quartic at a point.

In quantified mathematical form, this is the pair whose first component is
the Fréchet derivative of `x ↦ (∑ i, x_i^2)^2` at `x`, and whose second
component is the Fréchet derivative at `x` of the first-derivative map. Both
derivatives are converted from mathlib's continuous-linear-map form to the
coordinate gradient and Hessian used by semijets.
-/
def coordinateQuarticJetAt (x : Point n) : Jet n :=
  Jet.ofDerivatives
    (fderivWithin Real (coordinateQuartic (n := n)) Set.univ x)
    (fderivWithin Real
      (fderivWithin Real (coordinateQuartic (n := n)) Set.univ) Set.univ x)

/--
The canonical coordinate-quartic jet at the origin is the zero jet.
-/
@[simp]
theorem coordinateQuarticJetAt_zero :
    coordinateQuarticJetAt (n := n) (0 : Point n) = 0 := by
  rw [coordinateQuarticJetAt, fderivWithin_coordinateQuartic_univ_zero,
    fderivWithin_fderivWithin_coordinateQuartic_univ_zero]
  change
    ({ gradient := linearMapGradient (0 : Point n →L[Real] Real),
        hessian := bilinearMapHessian
          (0 : Point n →L[Real] Point n →L[Real] Real) } : Jet n) =
      ({ gradient := 0, hessian := 0 } : Jet n)
  congr

/--
The Hessian component of the canonical coordinate-quartic jet is Hermitian at
every point.
-/
theorem coordinateQuarticJetAt_hessian_isHermitian (x : Point n) :
    (coordinateQuarticJetAt x).hessian.IsHermitian := by
  have hφ : ContDiffOn Real (2 : ℕ∞ω) (coordinateQuartic (n := n)) Set.univ :=
    ((contDiff_coordinateQuartic (n := n)).of_le le_top).contDiffOn
  have hsymWithin :
      IsSymmSndFDerivWithinAt Real (coordinateQuartic (n := n)) Set.univ x :=
    (hφ x trivial).isSymmSndFDerivWithinAt (by norm_num) uniqueDiffOn_univ (by simp) trivial
  have hsym :
      IsSymmetricBilinear
        (fderivWithin Real
          (fderivWithin Real (coordinateQuartic (n := n)) Set.univ) Set.univ x) :=
    isSymmetricBilinear_fderivWithin_fderivWithin hsymWithin
  apply Matrix.IsHermitian.ext
  intro i j
  change
    (fderivWithin Real
      (fderivWithin Real (coordinateQuartic (n := n)) Set.univ) Set.univ x)
        (coordinateVector j) (coordinateVector i) =
      (fderivWithin Real
        (fderivWithin Real (coordinateQuartic (n := n)) Set.univ) Set.univ x)
          (coordinateVector i) (coordinateVector j)
  exact hsym (coordinateVector j) (coordinateVector i)

/--
At every point, the coordinate quartic has the second-order expansion given by
its canonical first and second Fréchet derivatives.
-/
theorem hasSecondOrderExpansionWithin_coordinateQuartic_univ (x : Point n) :
    HasSecondOrderExpansionWithin Set.univ (coordinateQuartic (n := n)) x
      (coordinateQuarticJetAt x) := by
  apply hasSecondOrderExpansionWithin_of_contDiffOn_two
    (C := Set.univ) (φ := coordinateQuartic (n := n)) (x0 := x)
  · exact convex_univ
  · exact uniqueDiffOn_univ
  · exact Set.mem_univ x
  · simp
  · exact ((contDiff_coordinateQuartic (n := n)).of_le le_top).contDiffOn
  · simp [coordinateQuarticJetAt]
  · simp [coordinateQuarticJetAt]

/--
The canonical coordinate-quartic jet depends continuously on the base point.
-/
theorem continuous_coordinateQuarticJetAt :
    Continuous (coordinateQuarticJetAt (n := n)) := by
  have hφ : ContDiffOn Real (2 : ℕ∞ω) (coordinateQuartic (n := n)) Set.univ :=
    ((contDiff_coordinateQuartic (n := n)).of_le le_top).contDiffOn
  have hDφ_cont :
      ContinuousOn (fderivWithin Real (coordinateQuartic (n := n)) Set.univ) Set.univ :=
    hφ.continuousOn_fderivWithin uniqueDiffOn_univ (by norm_num)
  have hDφ_cd :
      ContDiffOn Real (1 : ℕ∞ω)
        (fderivWithin Real (coordinateQuartic (n := n)) Set.univ) Set.univ :=
    hφ.fderivWithin (m := (1 : ℕ∞ω)) uniqueDiffOn_univ (by norm_num)
  have hD2φ_cont :
      ContinuousOn
        (fderivWithin Real
          (fderivWithin Real (coordinateQuartic (n := n)) Set.univ) Set.univ)
        Set.univ :=
    hDφ_cd.continuousOn_fderivWithin uniqueDiffOn_univ (by norm_num)
  have hDφ_cont' :
      Continuous (fderivWithin Real (coordinateQuartic (n := n)) Set.univ) :=
    continuousOn_univ.mp hDφ_cont
  have hD2φ_cont' :
      Continuous
        (fderivWithin Real
          (fderivWithin Real (coordinateQuartic (n := n)) Set.univ) Set.univ) :=
    continuousOn_univ.mp hD2φ_cont
  refine continuous_induced_rng.mpr ?_
  have hgrad :
      Continuous fun x : Point n =>
        (coordinateQuarticJetAt x).gradient := by
    exact continuous_pi fun i =>
      hDφ_cont'.clm_apply continuous_const
  have hhess :
      Continuous fun x : Point n =>
        (coordinateQuarticJetAt x).hessian := by
    exact continuous_pi fun i =>
      continuous_pi fun j =>
        ((hD2φ_cont'.clm_apply continuous_const).clm_apply continuous_const)
  exact hgrad.prodMk hhess

/--
As `x -> 0`, the Hessian component of the canonical coordinate-quartic jet
tends to zero.
-/
theorem tendsto_coordinateQuarticJetAt_hessian_zero :
    Filter.Tendsto (fun x : Point n => (coordinateQuarticJetAt x).hessian)
      (𝓝 (0 : Point n)) (𝓝 (0 : Hessian n)) := by
  have hcont :
      Continuous fun x : Point n => (coordinateQuarticJetAt x).hessian :=
    Jet.continuous_hessian.comp (continuous_coordinateQuarticJetAt (n := n))
  have h0 :
      ContinuousAt (fun x : Point n => (coordinateQuarticJetAt x).hessian) 0 :=
    hcont.continuousAt
  have hz : (coordinateQuarticJetAt (n := n) (0 : Point n)).hessian = 0 := by
    rw [coordinateQuarticJetAt_zero]
    rfl
  rw [← hz]
  exact h0

/--
As `x -> 0`, the gradient component of the canonical coordinate-quartic jet
tends to zero.
-/
theorem tendsto_coordinateQuarticJetAt_gradient_zero :
    Filter.Tendsto (fun x : Point n => (coordinateQuarticJetAt x).gradient)
      (𝓝 (0 : Point n)) (𝓝 (0 : Point n)) := by
  have hcont :
      Continuous fun x : Point n => (coordinateQuarticJetAt x).gradient :=
    Jet.continuous_gradient.comp (continuous_coordinateQuarticJetAt (n := n))
  have h0 :
      ContinuousAt (fun x : Point n => (coordinateQuarticJetAt x).gradient) 0 :=
    hcont.continuousAt
  have hz : (coordinateQuarticJetAt (n := n) (0 : Point n)).gradient = 0 := by
    rw [coordinateQuarticJetAt_zero]
    rfl
  simpa [hz] using h0.tendsto
end ViscositySolns
