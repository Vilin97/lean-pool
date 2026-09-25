/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.RowStability
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! # Source Anari Rezaei -/

@[expose] public section

open scoped BigOperators

namespace BeyondBethe

/-!
# Anari--Rezaei's sharp one-row inequality

This file formalizes the source proof of the one-row inequality used in the
upper Bethe bound.  The first step pairs every ordering with its reversal and
reduces the averaged row score to the deterministic prefix--suffix functional
called `phi` in the source.
-/

/-- The sum of the two row scores for an ordering and its reversal, minus
twice the complement-entropy term.  After reindexing the coordinates into the
given order, this is Anari--Rezaei's function `phi`. -/
noncomputable def pairedRowScore {m : ℕ}
    (p : Fin m → ℝ) (π : Equiv.Perm (Fin m)) : ℝ :=
  (∑ j, p j * Real.log (suffixMass p π j)) +
    (∑ j, p j * Real.log (suffixMass p (reverseOrdering π) j)) -
      2 * ∑ j, (1 - p j) * Real.log (1 - p j)

/-- Averaging the paired score gives exactly twice the one-row correction. -/
theorem uniformAverage_pairedRowScore {m : ℕ} (p : Fin m → ℝ) :
    uniformAverage (pairedRowScore p) = 2 * rowCorrection p := by
  let f : Equiv.Perm (Fin m) → ℝ := fun π ↦
    ∑ j, p j * Real.log (suffixMass p π j)
  let C : ℝ := ∑ j, (1 - p j) * Real.log (1 - p j)
  have hrev : uniformAverage (fun π : Equiv.Perm (Fin m) ↦
      f (reverseOrdering π)) = uniformAverage f := by
    exact uniformAverage_perm_preTrans f Fin.revPerm
  have hconst : uniformAverage
      (fun _π : Equiv.Perm (Fin m) ↦ 2 * C) = 2 * C :=
    uniformAverage_const (2 * C)
  rw [show pairedRowScore p = fun π ↦
      f π + f (reverseOrdering π) - 2 * C by
    funext π
    rfl]
  rw [uniformAverage_sub, uniformAverage_add, hrev, hconst]
  have hf : uniformAverage f = rowT p := rfl
  rw [hf]
  change rowT p + rowT p - 2 * C = 2 * rowCorrection p
  rw [rowCorrection]
  ring

/-- Pointwise control of the reversal-paired functional implies the sharp
one-row deficit inequality. -/
theorem rowDeficit_nonneg_of_pairedRowScore_le
    {m : ℕ} (p : Fin m → ℝ)
    (hphi : ∀ π : Equiv.Perm (Fin m), pairedRowScore p π ≤ Real.log 2) :
    0 ≤ rowDeficit p := by
  have havg : uniformAverage (pairedRowScore p) ≤
      uniformAverage (fun _π : Equiv.Perm (Fin m) ↦ Real.log 2) := by
    unfold uniformAverage
    exact div_le_div_of_nonneg_right
      (Finset.sum_le_sum fun π _ ↦ hphi π) (Nat.cast_nonneg _)
  rw [uniformAverage_pairedRowScore,
    uniformAverage_const (α := Equiv.Perm (Fin m))] at havg
  rw [rowDeficit]
  linarith

/-- The canonical `phi`, with the coordinates already arranged in their
natural order. -/
noncomputable def anariRezaeiPhi {m : ℕ} (p : Fin m → ℝ) : ℝ :=
  pairedRowScore p (Equiv.refl (Fin m))

/-- Reindex a probability vector by an ordering. -/
def orderCoordinates {m : ℕ}
    (p : Fin m → ℝ) (π : Equiv.Perm (Fin m)) : Fin m → ℝ :=
  fun i ↦ p (π i)

theorem orderCoordinates_probability {m : ℕ}
    {p : Fin m → ℝ} (hp : IsProbabilityVector p)
    (π : Equiv.Perm (Fin m)) :
    IsProbabilityVector (orderCoordinates p π) := by
  refine ⟨fun i ↦ hp.nonnegative (π i), ?_⟩
  exact (Equiv.sum_comp π p).trans hp.sum_eq_one

theorem suffixMass_orderCoordinates {m : ℕ}
    (p : Fin m → ℝ) (π : Equiv.Perm (Fin m)) (i : Fin m) :
    suffixMass (orderCoordinates p π) (Equiv.refl (Fin m)) i =
      suffixMass p π (π i) := by
  classical
  rw [suffixMass, suffixMass]
  change (∑ k, if i ≤ k then p (π k) else 0) =
    ∑ k, if π.symm (π i) ≤ π.symm k then p k else 0
  let f : Fin m → ℝ := fun k ↦
    if π.symm (π i) ≤ π.symm k then p k else 0
  calc
    (∑ k, if i ≤ k then p (π k) else 0) =
        ∑ k, f (π k) := by simp [f]
    _ = ∑ k, f k := Equiv.sum_comp π f
    _ = ∑ k, if π.symm (π i) ≤ π.symm k then p k else 0 := rfl

theorem suffixMass_reverse_orderCoordinates {m : ℕ}
    (p : Fin m → ℝ) (π : Equiv.Perm (Fin m)) (i : Fin m) :
    suffixMass (orderCoordinates p π)
        (reverseOrdering (Equiv.refl (Fin m))) i =
      suffixMass p (reverseOrdering π) (π i) := by
  classical
  rw [suffixMass, suffixMass]
  change (∑ k, if
      (reverseOrdering (Equiv.refl (Fin m))).symm i ≤
        (reverseOrdering (Equiv.refl (Fin m))).symm k
      then p (π k) else 0) =
    ∑ k, if (reverseOrdering π).symm (π i) ≤
      (reverseOrdering π).symm k then p k else 0
  let f : Fin m → ℝ := fun k ↦
    if (reverseOrdering π).symm (π i) ≤
      (reverseOrdering π).symm k then p k else 0
  calc
    (∑ k, if
        (reverseOrdering (Equiv.refl (Fin m))).symm i ≤
          (reverseOrdering (Equiv.refl (Fin m))).symm k
        then p (π k) else 0) =
      ∑ k, f (π k) := by
        apply Finset.sum_congr rfl
        intro k _
        simp [f, reverseOrdering, Equiv.trans_apply]
    _ = ∑ k, f k := Equiv.sum_comp π f
    _ = ∑ k, if (reverseOrdering π).symm (π i) ≤
        (reverseOrdering π).symm k then p k else 0 := rfl

/-- Every paired row score is the canonical `phi` of the reordered vector. -/
theorem anariRezaeiPhi_orderCoordinates {m : ℕ}
    (p : Fin m → ℝ) (π : Equiv.Perm (Fin m)) :
    anariRezaeiPhi (orderCoordinates p π) = pairedRowScore p π := by
  classical
  rw [anariRezaeiPhi, pairedRowScore, pairedRowScore]
  have hsuffix :
      (∑ j, orderCoordinates p π j *
          Real.log (suffixMass (orderCoordinates p π)
            (Equiv.refl (Fin m)) j)) =
        ∑ j, p j * Real.log (suffixMass p π j) := by
    let f : Fin m → ℝ := fun j ↦
      p j * Real.log (suffixMass p π j)
    calc
      (∑ j, orderCoordinates p π j *
          Real.log (suffixMass (orderCoordinates p π)
            (Equiv.refl (Fin m)) j)) =
        ∑ i, f (π i) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [suffixMass_orderCoordinates]
          rfl
      _ = ∑ j, f j := Equiv.sum_comp π f
      _ = ∑ j, p j * Real.log (suffixMass p π j) := rfl
  have hreverse :
      (∑ j, orderCoordinates p π j *
          Real.log (suffixMass (orderCoordinates p π)
            (reverseOrdering (Equiv.refl (Fin m))) j)) =
        ∑ j, p j * Real.log (suffixMass p (reverseOrdering π) j) := by
    let f : Fin m → ℝ := fun j ↦
      p j * Real.log (suffixMass p (reverseOrdering π) j)
    calc
      (∑ j, orderCoordinates p π j *
          Real.log (suffixMass (orderCoordinates p π)
            (reverseOrdering (Equiv.refl (Fin m))) j)) =
        ∑ i, f (π i) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [suffixMass_reverse_orderCoordinates]
          rfl
      _ = ∑ j, f j := Equiv.sum_comp π f
      _ = ∑ j, p j *
          Real.log (suffixMass p (reverseOrdering π) j) := rfl
  have hcomplement :
      (∑ j, (1 - orderCoordinates p π j) *
          Real.log (1 - orderCoordinates p π j)) =
        ∑ j, (1 - p j) * Real.log (1 - p j) := by
    exact Equiv.sum_comp π
      (fun j ↦ (1 - p j) * Real.log (1 - p j))
  rw [hsuffix, hreverse, hcomplement]

/-- The canonical `phi` inequality implies the full Anari--Rezaei one-row
interface. -/
theorem anariRezaeiRowInequality_of_phi
    (hphi : ∀ {m : ℕ}, 2 ≤ m → ∀ p : Fin m → ℝ,
      IsProbabilityVector p → anariRezaeiPhi p ≤ Real.log 2) :
    AnariRezaeiRowInequality := by
  intro m hm p hp
  apply rowDeficit_nonneg_of_pairedRowScore_le
  intro π
  rw [← anariRezaeiPhi_orderCoordinates]
  exact hphi hm (orderCoordinates p π)
    (orderCoordinates_probability hp π)

/-! ## An analytic replacement for the source's three-variable grid check -/

/-- A hyperbolic upper bound for the logarithm. -/
theorem two_mul_log_le_sub_inv {z : ℝ} (hz : 1 ≤ z) :
    2 * Real.log z ≤ z - 1 / z := by
  let h : ℝ → ℝ := fun x ↦ x - 1 / x - 2 * Real.log x
  have hcont : ContinuousOn h (Set.Ici (1 : ℝ)) := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hx)
    dsimp [h]
    fun_prop
  have hdiff : DifferentiableOn ℝ h (interior (Set.Ici (1 : ℝ))) := by
    intro x hx
    have hx' : 1 < x := by simpa using hx
    have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans hx')
    have hd : HasDerivAt h (1 + 1 / x ^ 2 - 2 / x) x := by
      dsimp [h]
      convert! ((hasDerivAt_id x).sub
        ((hasDerivAt_const x 1).div (hasDerivAt_id x) hx0)).sub
          ((Real.hasDerivAt_log hx0).const_mul 2) using 1 <;>
        simp only [id_eq] <;> ring
    exact hd.differentiableAt.differentiableWithinAt
  have hderiv : ∀ x ∈ interior (Set.Ici (1 : ℝ)),
      deriv h x = (x - 1) ^ 2 / x ^ 2 := by
    intro x hx
    have hx' : 1 < x := by simpa using hx
    have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans hx')
    have hd : HasDerivAt h (1 + 1 / x ^ 2 - 2 / x) x := by
      dsimp [h]
      convert! ((hasDerivAt_id x).sub
        ((hasDerivAt_const x 1).div (hasDerivAt_id x) hx0)).sub
          ((Real.hasDerivAt_log hx0).const_mul 2) using 1 <;>
        simp only [id_eq] <;> ring
    rw [hd.deriv]
    field_simp
    ring
  have hmono : MonotoneOn h (Set.Ici (1 : ℝ)) :=
    monotoneOn_of_deriv_nonneg (convex_Ici (1 : ℝ)) hcont hdiff fun x hx ↦ by
      rw [hderiv x hx]
      positivity
  have hle := hmono (by simp : (1 : ℝ) ∈ Set.Ici 1) hz hz
  dsimp [h] at hle
  norm_num at hle ⊢
  linarith

/-- Positive Bernstein coefficients for the rational polynomial certificate
used below.  The two indices are the Bernstein degrees in `u` and `v`. -/
private noncomputable def anariRezaeiDirectionCoeff
    (k : Fin 7) (l : Fin 5) : ℝ :=
  match k.1, l.1 with
  | 0, 0 => 1 | 0, 1 => 78/25 | 0, 2 => 84/25 | 0, 3 => 34/25 | 0, 4 => 3/25
  | 1, 0 => 6 | 1, 1 => 468/25 | 1, 2 => 12358/625 | 1, 3 => 118062/15625 | 1, 4 => 7862/15625
  | 2, 0 => 15 | 2, 1 => 234/5 | 2, 2 => 30048/625 | 2, 3 => 267446/15625 | 2, 4 => 313384/390625
  | 3, 0 => 20 | 3, 1 => 312/5 | 3, 2 => 7674/125 | 3, 3 => 312712/15625 | 3, 4 => 281922/390625
  | 4, 0 => 15 | 4, 1 => 234/5 | 4, 2 => 26781/625 | 4, 3 => 197266/15625 | 4, 4 => 264016/390625
  | 5, 0 => 6 | 5, 1 => 468/25 | 5, 2 => 9454/625 | 5, 3 => 66032/15625 | 5, 4 => 242288/390625
  | 6, 0 => 1 | 6, 1 => 78/25 | 6, 2 => 1253/625 | 6, 3 => 10844/15625 | 6, 4 => 81844/390625
  | _, _ => 0

private noncomputable def anariRezaeiDirectionCertificate
    (u v : ℝ) : ℝ :=
  ∑ k : Fin 7, ∑ l : Fin 5,
    anariRezaeiDirectionCoeff k l *
      u ^ k.1 * (1 - u) ^ (6 - k.1) *
      v ^ l.1 * (1 - v) ^ (4 - l.1)

private theorem anariRezaeiDirectionCoeff_nonneg
    (k : Fin 7) (l : Fin 5) :
    0 ≤ anariRezaeiDirectionCoeff k l := by
  fin_cases k <;> fin_cases l <;>
    norm_num [anariRezaeiDirectionCoeff]

private theorem anariRezaeiDirectionCertificate_nonneg
    {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    0 ≤ anariRezaeiDirectionCertificate u v := by
  apply Finset.sum_nonneg
  intro k _
  apply Finset.sum_nonneg
  intro l _
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
    (anariRezaeiDirectionCoeff_nonneg k l) (pow_nonneg hu0 _))
      (pow_nonneg (sub_nonneg.mpr hu1) _))
        (pow_nonneg hv0 _)) (pow_nonneg (sub_nonneg.mpr hv1) _)

private theorem anariRezaeiDirectionCertificate_eq (u v : ℝ) :
    anariRezaeiDirectionCertificate u v =
      1 - (22/25)*v
        - (242/625)*u*v^2 + (2662/15625)*u*v^3
        - (242/625)*u^2*v^2 + (7986/15625)*u^2*v^3 - (14641/390625)*u^2*v^4
        - (242/625)*u^3*v^2 + (10648/15625)*u^3*v^3 - (58564/390625)*u^3*v^4
        - (121/625)*u^4*v^2 + (7986/15625)*u^4*v^3 - (87846/390625)*u^4*v^4
        + (2662/15625)*u^5*v^3 - (58564/390625)*u^5*v^4
        - (14641/390625)*u^6*v^4 := by
  norm_num [anariRezaeiDirectionCertificate,
    anariRezaeiDirectionCoeff, Fin.sum_univ_succ]
  ring

/-- Polynomial obtained after removing denominators from the directional
derivative estimate for the three-variable `phi`. -/
noncomputable def anariRezaeiLargeCoordinatePolynomial
    (q s : ℝ) : ℝ :=
  2*q*(1-q)*s*(q+s)^2 + s^2*(1-s)^2 - (1-q)^2*(q+s)^4

/-- The polynomial is nonnegative on the triangle
`0 ≤ q ≤ s ≤ 11/25`.  This is the 35-term exact rational certificate that
replaces the source's `881^2` grid computation. -/
theorem anariRezaeiLargeCoordinatePolynomial_nonneg
    {q s : ℝ} (hq0 : 0 ≤ q) (hqs : q ≤ s)
    (hs : s ≤ 11/25) :
    0 ≤ anariRezaeiLargeCoordinatePolynomial q s := by
  have hs0 : 0 ≤ s := hq0.trans hqs
  by_cases hs_zero : s = 0
  · have hq_zero : q = 0 := le_antisymm (hqs.trans_eq hs_zero) hq0
    simp [anariRezaeiLargeCoordinatePolynomial, hs_zero, hq_zero]
  · have hspos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs_zero)
    let u := q / s
    let v := s / (11/25 : ℝ)
    have hu0 : 0 ≤ u := div_nonneg hq0 hs0
    have hu1 : u ≤ 1 := (div_le_one hspos).mpr hqs
    have hv0 : 0 ≤ v := div_nonneg hs0 (by norm_num)
    have hv1 : v ≤ 1 :=
      (div_le_one (by norm_num : (0 : ℝ) < 11/25)).mpr hs
    have hc := anariRezaeiDirectionCertificate_nonneg hu0 hu1 hv0 hv1
    have hid : anariRezaeiLargeCoordinatePolynomial q s =
        s^2 * anariRezaeiDirectionCertificate u v := by
      rw [anariRezaeiDirectionCertificate_eq]
      dsimp [anariRezaeiLargeCoordinatePolynomial, u, v]
      field_simp [hs_zero]
      ring
    rw [hid]
    exact mul_nonneg (sq_nonneg s) hc

/-- The derivative of the three-variable `phi` in its larger endpoint
coordinate, after eliminating the middle coordinate by `r = 1-q-s`. -/
noncomputable def anariRezaeiLargeCoordinateDerivative
    (q s : ℝ) : ℝ :=
  Real.log (s*(1-s)/((1-q)*(q+s)^2)) + q/(1-s)

/-- On `0 ≤ q ≤ s ≤ 11/25`, increasing the larger endpoint coordinate does
not decrease the three-variable `phi`. -/
theorem anariRezaeiLargeCoordinateDerivative_nonneg
    {q s : ℝ} (hq0 : 0 ≤ q) (hqs : q ≤ s)
    (hs : s ≤ 11/25) (hspos : 0 < s) :
    0 ≤ anariRezaeiLargeCoordinateDerivative q s := by
  have hs1 : s < 1 := hs.trans_lt (by norm_num)
  have hq1 : q < 1 := hqs.trans_lt hs1
  have honeq : 0 < 1-q := sub_pos.mpr hq1
  have hones : 0 < 1-s := sub_pos.mpr hs1
  have hsum : 0 < q+s := add_pos_of_nonneg_of_pos hq0 hspos
  let z : ℝ := (1-q)*(q+s)^2/(s*(1-s))
  have hzpos : 0 < z := div_pos (mul_pos honeq (sq_pos_of_pos hsum))
    (mul_pos hspos hones)
  have hrewrite : anariRezaeiLargeCoordinateDerivative q s =
      -Real.log z + q/(1-s) := by
    rw [anariRezaeiLargeCoordinateDerivative]
    have hinv : s * (1-s) / ((1-q)*(q+s)^2) = z⁻¹ := by
      dsimp [z]
      field_simp
    rw [hinv, Real.log_inv]
  rw [hrewrite]
  by_cases hz : z ≤ 1
  · have hlog : Real.log z ≤ 0 := Real.log_nonpos hzpos.le hz
    exact add_nonneg (neg_nonneg.mpr hlog) (div_nonneg hq0 hones.le)
  · have hz1 : 1 ≤ z := le_of_not_ge hz
    have hlog := two_mul_log_le_sub_inv hz1
    have hpoly := anariRezaeiLargeCoordinatePolynomial_nonneg hq0 hqs hs
    have hrat : z - 1/z ≤ 2*q/(1-s) := by
      dsimp [z]
      have hden1 : s * (1-s) ≠ 0 := (mul_pos hspos hones).ne'
      have hden2 : (1-q)*(q+s)^2 ≠ 0 :=
        (mul_pos honeq (sq_pos_of_pos hsum)).ne'
      field_simp [hden1, hden2, hones.ne']
      rw [anariRezaeiLargeCoordinatePolynomial] at hpoly
      nlinarith
    have htwo : 2*q/(1-s) = 2*(q/(1-s)) := by ring
    rw [htwo] at hrat
    have hlog' : Real.log z ≤ q/(1-s) := by linarith
    linarith

/-- The source's three-variable `phi(q,1-q-s,s)`, written with the continuous
`negMulLog` convention at `q=0` or `s=0`. -/
noncomputable def anariRezaeiPhiThree (q s : ℝ) : ℝ :=
  -Real.negMulLog q - Real.negMulLog s
    - (1-q+s)*Real.log (1-q)
    - (1+q-s)*Real.log (1-s)
    + 2*Real.negMulLog (q+s)

theorem hasDerivAt_anariRezaeiPhiThree_right
    {q s : ℝ} (hq1 : q < 1) (hs0 : 0 < s) (hs1 : s < 1)
    (hq0 : 0 ≤ q) :
    HasDerivAt (anariRezaeiPhiThree q)
      (anariRezaeiLargeCoordinateDerivative q s) s := by
  have hqsum : 0 < q+s := add_pos_of_nonneg_of_pos hq0 hs0
  have h1q : 1-q ≠ 0 := (sub_pos.mpr hq1).ne'
  have h1s : 1-s ≠ 0 := (sub_pos.mpr hs1).ne'
  have hsum : q+s ≠ 0 := hqsum.ne'
  have hnegS := (Real.hasDerivAt_negMulLog hs0.ne').neg
  have hlin1 : HasDerivAt (fun x : ℝ => 1-q+x) 1 s := by
    convert! (hasDerivAt_const s (1-q)).add (hasDerivAt_id s) using 1 <;> ring
  have hterm1 := (hlin1.mul_const (Real.log (1-q))).neg
  have hlin2 : HasDerivAt (fun x : ℝ => 1+q-x) (-1) s := by
    convert! (hasDerivAt_const s (1+q)).sub (hasDerivAt_id s) using 1 <;> ring
  have hcomp2 : HasDerivAt (fun x : ℝ => Real.log (1-x))
      (-1/(1-s)) s := by
    convert! (Real.hasDerivAt_log h1s).comp s
      ((hasDerivAt_const s 1).sub (hasDerivAt_id s)) using 1 <;> ring
  have hterm2 := (hlin2.mul hcomp2).neg
  have hsumlin : HasDerivAt (fun x : ℝ => q+x) 1 s := by
    convert! (hasDerivAt_const s q).add (hasDerivAt_id s) using 1 <;> ring
  have hterm3 := ((Real.hasDerivAt_negMulLog hsum).comp s hsumlin).const_mul 2
  have hd := ((((hasDerivAt_const s (-Real.negMulLog q)).add hnegS).add
    hterm1).add hterm2).add hterm3
  convert! hd using 1
  rw [anariRezaeiLargeCoordinateDerivative]
  rw [Real.log_div (mul_ne_zero hs0.ne' h1s)
        (mul_ne_zero h1q (pow_ne_zero 2 hsum)),
    Real.log_mul hs0.ne' h1s,
    Real.log_mul h1q (pow_ne_zero 2 hsum), Real.log_pow]
  field_simp [h1s]
  ring

/-- On the central triangle, `phi(q,1-q-s,s)` is no larger than its value
after increasing the larger endpoint coordinate to `11/25`. -/
theorem anariRezaeiPhiThree_le_boundary
    {q s : ℝ} (hq0 : 0 ≤ q) (hqs : q ≤ s)
    (hs : s ≤ 11/25) :
    anariRezaeiPhiThree q s ≤ anariRezaeiPhiThree q (11/25) := by
  have hq1 : q < 1 := (hqs.trans hs).trans_lt (by norm_num)
  have hcont : ContinuousOn (anariRezaeiPhiThree q)
      (Set.Icc s (11/25)) := by
    intro x hx
    have hx1 : x < 1 := hx.2.trans_lt (by norm_num)
    have h1q : 1-q ≠ 0 := (sub_pos.mpr hq1).ne'
    have h1x : 1-x ≠ 0 := (sub_pos.mpr hx1).ne'
    have hnml : ContinuousAt (fun y : ℝ ↦ Real.negMulLog y) x :=
      Real.continuous_negMulLog.continuousAt
    have hlinearQ : ContinuousAt (fun y : ℝ ↦ 1 - q + y) x :=
      (continuousAt_const.sub continuousAt_const).add continuousAt_id
    have hlinearX : ContinuousAt (fun y : ℝ ↦ 1 + q - y) x :=
      (continuousAt_const.add continuousAt_const).sub continuousAt_id
    have hlogQ : ContinuousAt (fun _y : ℝ ↦ Real.log (1 - q)) x :=
      continuousAt_const
    have hlogX : ContinuousAt (fun y : ℝ ↦ Real.log (1 - y)) x :=
      (continuousAt_const.sub continuousAt_id).log h1x
    have hnmlSum : ContinuousAt (fun y : ℝ ↦ Real.negMulLog (q + y)) x :=
      Real.continuous_negMulLog.continuousAt.comp'
        (continuousAt_const.add continuousAt_id)
    have hzero : ContinuousAt (fun _y : ℝ ↦ -Real.negMulLog q) x :=
      continuousAt_const
    have htwo : ContinuousAt (fun _y : ℝ ↦ (2 : ℝ)) x :=
      continuousAt_const
    have htotal :=
      ((((hzero.sub hnml).sub (hlinearQ.mul hlogQ)).sub
        (hlinearX.mul hlogX)).add (htwo.mul hnmlSum))
    change ContinuousWithinAt (fun y : ℝ ↦
      -Real.negMulLog q - Real.negMulLog y
        - (1-q+y)*Real.log (1-q)
        - (1+q-y)*Real.log (1-y)
        + 2*Real.negMulLog (q+y)) (Set.Icc s (11/25)) x
    exact htotal.continuousWithinAt
  have hdiff : DifferentiableOn ℝ (anariRezaeiPhiThree q)
      (interior (Set.Icc s (11/25))) := by
    intro x hx
    have hx' : s < x ∧ x < 11/25 := by simpa using hx
    have hx0 : 0 < x := lt_of_le_of_lt (hq0.trans hqs) hx'.1
    have hx1 : x < 1 := hx'.2.trans (by norm_num)
    exact (hasDerivAt_anariRezaeiPhiThree_right hq1 hx0 hx1 hq0).differentiableAt.differentiableWithinAt
  have hmono : MonotoneOn (anariRezaeiPhiThree q)
      (Set.Icc s (11/25)) :=
    monotoneOn_of_deriv_nonneg (convex_Icc s (11/25)) hcont hdiff fun x hx => by
      have hx' : s < x ∧ x < 11/25 := by simpa using hx
      have hx0 : 0 < x := lt_of_le_of_lt (hq0.trans hqs) hx'.1
      have hx1 : x < 1 := hx'.2.trans (by norm_num)
      rw [(hasDerivAt_anariRezaeiPhiThree_right hq1 hx0 hx1 hq0).deriv]
      exact anariRezaeiLargeCoordinateDerivative_nonneg hq0
        (hqs.trans hx'.1.le) hx'.2.le hx0
  exact hmono ⟨le_rfl, hs⟩ ⟨hs, le_rfl⟩ hs

theorem anariRezaeiPhiThree_comm (q s : ℝ) :
    anariRezaeiPhiThree q s = anariRezaeiPhiThree s q := by
  rw [anariRezaeiPhiThree, anariRezaeiPhiThree]
  ring

/-! On the boundary `s = 11/25`, the derivative is nonnegative after
`q = 1/5`.  The following five positive Bernstein coefficients certify the
only polynomial inequality needed for that assertion. -/

private noncomputable def anariRezaeiEdgeCoeff (k : Fin 5) : ℝ :=
  match k.1 with
  | 0 => 3260944 / 244140625
  | 1 => 24245392 / 244140625
  | 2 => 53151396 / 244140625
  | 3 => 41514088 / 244140625
  | 4 => 9903124 / 244140625
  | _ => 0

private noncomputable def anariRezaeiEdgeCertificate (v : ℝ) : ℝ :=
  ∑ k : Fin 5, anariRezaeiEdgeCoeff k *
    v ^ k.1 * (1 - v) ^ (4 - k.1)

private theorem anariRezaeiEdgeCoeff_nonneg (k : Fin 5) :
    0 ≤ anariRezaeiEdgeCoeff k := by
  fin_cases k <;> norm_num [anariRezaeiEdgeCoeff]

private theorem anariRezaeiEdgeCertificate_nonneg
    {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    0 ≤ anariRezaeiEdgeCertificate v := by
  apply Finset.sum_nonneg
  intro k _
  exact mul_nonneg (mul_nonneg (anariRezaeiEdgeCoeff_nonneg k)
    (pow_nonneg hv0 _)) (pow_nonneg (sub_nonneg.mpr hv1) _)

private theorem anariRezaeiEdgeCertificate_eq (v : ℝ) :
    anariRezaeiEdgeCertificate v =
      (3260944 + 11201616*v - 19116*v^2 - 5096304*v^3 +
        555984*v^4) / 244140625 := by
  norm_num [anariRezaeiEdgeCertificate, anariRezaeiEdgeCoeff,
    Fin.sum_univ_succ]
  ring

/-- The explicit quartic edge polynomial with constants `11/25` and `14/25` used in the
Anari-Rezaei edge estimate. -/
noncomputable def anariRezaeiEdgePolynomial (q : ℝ) : ℝ :=
  2*(11/25)*(14/25)*q*(q+11/25)^2 + q^2*(1-q)^2 -
    (14/25)^2*(q+11/25)^4

theorem anariRezaeiEdgePolynomial_nonneg
    {q : ℝ} (hq0 : 1/5 ≤ q) (hq1 : q ≤ 11/25) :
    0 ≤ anariRezaeiEdgePolynomial q := by
  let v : ℝ := (q - 1/5) / (6/25)
  have hv0 : 0 ≤ v := div_nonneg (sub_nonneg.mpr hq0) (by norm_num)
  have hv1 : v ≤ 1 := by
    dsimp [v]
    apply (div_le_one (by norm_num : (0 : ℝ) < 6/25)).mpr
    linarith
  have hc := anariRezaeiEdgeCertificate_nonneg hv0 hv1
  have hid : anariRezaeiEdgePolynomial q =
      anariRezaeiEdgeCertificate v := by
    rw [anariRezaeiEdgeCertificate_eq]
    dsimp [anariRezaeiEdgePolynomial, v]
    ring
  rw [hid]
  exact hc

/-- The boundary-edge derivative is nonnegative on `[1/5, 11/25]`. -/
theorem anariRezaeiEdgeDerivative_nonneg
    {q : ℝ} (hq0 : 1/5 ≤ q) (hq1 : q ≤ 11/25) :
    0 ≤ anariRezaeiLargeCoordinateDerivative (11/25) q := by
  have hqpos : 0 < q := (by norm_num : (0 : ℝ) < 1/5).trans_le hq0
  have hq_lt_one : q < 1 := hq1.trans_lt (by norm_num)
  have h1q : 0 < 1-q := sub_pos.mpr hq_lt_one
  have ha0 : 0 < (11/25 : ℝ) := by norm_num
  have ha1 : 0 < (14/25 : ℝ) := by norm_num
  have hsum : 0 < q+11/25 := add_pos hqpos ha0
  let z : ℝ := (14/25)*(q+11/25)^2/(q*(1-q))
  have hzpos : 0 < z := div_pos (mul_pos ha1 (sq_pos_of_pos hsum))
    (mul_pos hqpos h1q)
  have hrewrite : anariRezaeiLargeCoordinateDerivative (11/25) q =
      -Real.log z + (11/25)/(1-q) := by
    rw [anariRezaeiLargeCoordinateDerivative]
    have hinv : q*(1-q)/((1-11/25)*(11/25+q)^2) = z⁻¹ := by
      dsimp [z]
      norm_num
      field_simp
      ring
    rw [hinv, Real.log_inv]
  rw [hrewrite]
  by_cases hz : z ≤ 1
  · have hlog : Real.log z ≤ 0 := Real.log_nonpos hzpos.le hz
    exact add_nonneg (neg_nonneg.mpr hlog) (div_nonneg (by norm_num) h1q.le)
  · have hz1 : 1 ≤ z := le_of_not_ge hz
    have hlog := two_mul_log_le_sub_inv hz1
    have hpoly := anariRezaeiEdgePolynomial_nonneg hq0 hq1
    have hrat : z - 1/z ≤ 2*(11/25)/(1-q) := by
      dsimp [z]
      have hden1 : q*(1-q) ≠ 0 := (mul_pos hqpos h1q).ne'
      have hden2 : (14/25)*(q+11/25)^2 ≠ 0 :=
        (mul_pos ha1 (sq_pos_of_pos hsum)).ne'
      field_simp [hden1, hden2, h1q.ne']
      rw [anariRezaeiEdgePolynomial] at hpoly
      nlinarith
    have htwo : 2*(11/25)/(1-q) = 2*((11/25)/(1-q)) := by ring
    rw [htwo] at hrat
    linarith

theorem hasDerivAt_anariRezaeiPhiThree_edge
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    HasDerivAt (fun x ↦ anariRezaeiPhiThree x (11/25))
      (anariRezaeiLargeCoordinateDerivative (11/25) q) q := by
  have hd := hasDerivAt_anariRezaeiPhiThree_right
    (q := (11/25 : ℝ)) (s := q) (by norm_num) hq0 hq1 (by norm_num)
  have heq : (fun x ↦ anariRezaeiPhiThree x (11/25)) =ᶠ[nhds q]
      anariRezaeiPhiThree (11/25) :=
    Filter.Eventually.of_forall fun x ↦
      (anariRezaeiPhiThree_comm (11/25) x).symm
  exact hd.congr_of_eventuallyEq heq

/-- The edge second-derivative expression `1/q - 2/(q + 11/25) - (1 - q - 11/25)/(1 - q)^2`. -/
noncomputable def anariRezaeiEdgeSecondDerivative (q : ℝ) : ℝ :=
  1/q - 2/(q+11/25) - (1-q-11/25)/(1-q)^2

theorem hasDerivAt_anariRezaeiEdgeDerivative
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    HasDerivAt (anariRezaeiLargeCoordinateDerivative (11/25))
      (anariRezaeiEdgeSecondDerivative q) q := by
  have h1q : 1-q ≠ 0 := (sub_pos.mpr hq1).ne'
  have hsum : q+11/25 ≠ 0 := (add_pos hq0 (by norm_num)).ne'
  have hnum : q*(1-q) ≠ 0 := mul_ne_zero hq0.ne' h1q
  have hden : (1-11/25)*(11/25+q)^2 ≠ 0 := by
    norm_num
    simpa [add_comm] using hsum
  have hnum' := (hasDerivAt_id q).mul
    ((hasDerivAt_const q 1).sub (hasDerivAt_id q))
  have hsum' : HasDerivAt (fun x : ℝ ↦ 11/25+x) 1 q := by
    convert! (hasDerivAt_const q (11/25)).add (hasDerivAt_id q) using 1 <;> ring
  have hden' : HasDerivAt
      (fun x : ℝ ↦ (1-11/25)*(11/25+x)^2)
      (2*(1-11/25)*(11/25+q)) q := by
    convert! (hsum'.pow 2).const_mul (1-11/25) using 1 <;> ring
  have hquot := hnum'.div hden' hden
  have hlog := (Real.hasDerivAt_log (div_ne_zero hnum hden)).comp q hquot
  have hlin : HasDerivAt (fun x : ℝ ↦ 1-x) (-1) q := by
    convert! (hasDerivAt_const q 1).sub (hasDerivAt_id q) using 1 <;> ring
  have hfrac := (hasDerivAt_const q (11/25 : ℝ)).div hlin h1q
  have hd := hlog.add hfrac
  convert! hd using 1 <;>
    dsimp [anariRezaeiLargeCoordinateDerivative,
      anariRezaeiEdgeSecondDerivative] <;>
    field_simp [hq0.ne', h1q, hsum] <;> ring

private theorem anariRezaeiEdgeSecondNumerator_nonneg
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1/5) :
    0 ≤ 11/25 - (1329/625)*q + (58/25)*q^2 := by
  have hfactor1 : 0 ≤ 1/5-q := sub_nonneg.mpr hq1
  have hfactor2 : 0 ≤ 1329/625-(58/25)*(q+1/5) := by
    linarith
  have hprod := mul_nonneg hfactor1 hfactor2
  nlinarith

theorem anariRezaeiEdgeSecondDerivative_nonneg
    {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1/5) :
    0 ≤ anariRezaeiEdgeSecondDerivative q := by
  have hq_lt_one : q < 1 := hq1.trans_lt (by norm_num)
  have h1q : 0 < 1-q := sub_pos.mpr hq_lt_one
  have hsum : 0 < q+11/25 := add_pos hq0 (by norm_num)
  have hnum := anariRezaeiEdgeSecondNumerator_nonneg hq0.le hq1
  have hden : 0 < q*(q+11/25)*(1-q)^2 :=
    mul_pos (mul_pos hq0 hsum) (sq_pos_of_pos h1q)
  have hid : anariRezaeiEdgeSecondDerivative q =
      (11/25 - (1329/625)*q + (58/25)*q^2) /
        (q*(q+11/25)*(1-q)^2) := by
    rw [anariRezaeiEdgeSecondDerivative]
    field_simp [hq0.ne', hsum.ne', h1q.ne']
    ring
  rw [hid]
  exact div_nonneg hnum hden.le

private theorem continuousWithinAt_anariRezaeiPhiThree_edge
    {D : Set ℝ} {q : ℝ} (hq1 : q < 1) :
    ContinuousWithinAt (fun x ↦ anariRezaeiPhiThree x (11/25)) D q := by
  have h1q : 1-q ≠ 0 := (sub_pos.mpr hq1).ne'
  have hid : ContinuousWithinAt (fun x : ℝ ↦ x) D q :=
    continuousAt_id.continuousWithinAt
  have hc : ContinuousWithinAt (fun _x : ℝ ↦ (11/25 : ℝ)) D q :=
    continuousWithinAt_const
  have hnq : ContinuousWithinAt (fun x : ℝ ↦ Real.negMulLog x) D q :=
    Real.continuous_negMulLog.continuousAt.continuousWithinAt
  have hna : ContinuousWithinAt (fun _x : ℝ ↦ Real.negMulLog (11/25)) D q :=
    continuousWithinAt_const
  have hlogq : ContinuousWithinAt (fun x : ℝ ↦ Real.log (1-x)) D q :=
    (continuousWithinAt_const.sub hid).log h1q
  have hloga : ContinuousWithinAt
      (fun _x : ℝ ↦ Real.log (1-11/25)) D q := continuousWithinAt_const
  have hnsum : ContinuousWithinAt
      (fun x : ℝ ↦ Real.negMulLog (x+11/25)) D q := by
    simpa [Function.comp_def] using
      (Real.continuous_negMulLog.continuousAt.comp
        (continuousAt_id.add continuousAt_const)).continuousWithinAt
  unfold anariRezaeiPhiThree
  exact (((hnq.neg.sub hna).sub
    (((continuousWithinAt_const.sub hid).add hc).mul hlogq)).sub
      (((continuousWithinAt_const.add hid).sub hc).mul hloga)).add
        (hnsum.const_mul 2)

/-- The boundary-edge function is convex between `0` and `1/5`. -/
theorem anariRezaeiPhiThree_edge_convex :
    ConvexOn ℝ (Set.Icc (0 : ℝ) (1/5))
      (fun q ↦ anariRezaeiPhiThree q (11/25)) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc 0 (1/5))
  · intro q hq
    have hq1 : q < 1 := hq.2.trans_lt (by norm_num)
    exact continuousWithinAt_anariRezaeiPhiThree_edge hq1
  · intro q hq
    have hq' : 0 < q ∧ q < 1/5 := by simpa using hq
    exact (hasDerivAt_anariRezaeiPhiThree_edge hq'.1
      (hq'.2.trans (by norm_num))).hasDerivWithinAt
  · intro q hq
    have hq' : 0 < q ∧ q < 1/5 := by simpa using hq
    exact (hasDerivAt_anariRezaeiEdgeDerivative hq'.1
      (hq'.2.trans (by norm_num))).hasDerivWithinAt
  · intro q hq
    have hq' : 0 < q ∧ q < 1/5 := by simpa using hq
    exact anariRezaeiEdgeSecondDerivative_nonneg hq'.1 hq'.2.le

theorem binaryEntropy_le_log_two
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    binaryEntropy t ≤ Real.log 2 := by
  let p : Fin 2 → ℝ := fun i ↦ if i = 0 then t else 1-t
  have hp : IsProbabilityVector p := by
    constructor
    · intro i
      fin_cases i <;> simp [p, ht0, sub_nonneg.mpr ht1]
    · norm_num [p, Fin.sum_univ_succ]
  have h := shannonEntropy_le_log_card hp
  simpa [shannonEntropy, binaryEntropy, p, Fin.sum_univ_succ] using h

theorem anariRezaeiPhiThree_zero_edge :
    anariRezaeiPhiThree 0 (11/25) = binaryEntropy (11/25) := by
  rw [anariRezaeiPhiThree, binaryEntropy]
  simp only [Real.negMulLog_zero, neg_zero, zero_add,
    Real.log_one, mul_zero, sub_zero]
  rw [Real.negMulLog_def]
  ring

theorem anariRezaeiPhiThree_zero_edge_le :
    anariRezaeiPhiThree 0 (11/25) ≤ Real.log 2 := by
  rw [anariRezaeiPhiThree_zero_edge]
  exact binaryEntropy_le_log_two (by norm_num) (by norm_num)

/-- At the other endpoint of the boundary edge, the desired estimate reduces
to a single exact integer inequality. -/
theorem anariRezaeiPhiThree_diagonal_le_binaryEntropy :
    anariRezaeiPhiThree (11/25) (11/25) ≤ binaryEntropy (11/25) := by
  have h11 : (11/25 : ℝ) ≠ 0 := by norm_num
  have h14 : (14/25 : ℝ) ≠ 0 := by norm_num
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  have hA : (11/25 : ℝ)^11 ≠ 0 := pow_ne_zero 11 h11
  have hB : (2 : ℝ)^44 ≠ 0 := pow_ne_zero 44 h2
  have hC : (14/25 : ℝ)^36 ≠ 0 := pow_ne_zero 36 h14
  have hprod : (1 : ℝ) ≤
      (11/25 : ℝ)^11 * 2^44 * (14/25)^36 := by
    norm_num
  have hlogprod := Real.log_nonneg hprod
  rw [Real.log_mul (mul_ne_zero hA hB) hC,
    Real.log_mul hA hB, Real.log_pow, Real.log_pow, Real.log_pow] at hlogprod
  have h22 : (22/25 : ℝ) = 2*(11/25) := by norm_num
  rw [anariRezaeiPhiThree, binaryEntropy, Real.negMulLog_def]
  norm_num only [sub_self, add_zero, Real.log_one,
    mul_zero, sub_zero]
  rw [h22, Real.log_mul h2 h11]
  nlinarith

theorem anariRezaeiPhiThree_diagonal_le :
    anariRezaeiPhiThree (11/25) (11/25) ≤ Real.log 2 :=
  anariRezaeiPhiThree_diagonal_le_binaryEntropy.trans
    (binaryEntropy_le_log_two (by norm_num) (by norm_num))

theorem anariRezaeiPhiThree_edge_le_diagonal
    {q : ℝ} (hq0 : 1/5 ≤ q) (hq1 : q ≤ 11/25) :
    anariRezaeiPhiThree q (11/25) ≤
      anariRezaeiPhiThree (11/25) (11/25) := by
  have hcont : ContinuousOn (fun x ↦ anariRezaeiPhiThree x (11/25))
      (Set.Icc q (11/25)) := by
    intro x hx
    exact continuousWithinAt_anariRezaeiPhiThree_edge
      (hx.2.trans_lt (by norm_num))
  have hdiff : DifferentiableOn ℝ
      (fun x ↦ anariRezaeiPhiThree x (11/25))
      (interior (Set.Icc q (11/25))) := by
    intro x hx
    have hx' : q < x ∧ x < 11/25 := by simpa using hx
    exact (hasDerivAt_anariRezaeiPhiThree_edge
      ((by norm_num : (0 : ℝ) < 1/5).trans_le (hq0.trans hx'.1.le))
      (hx'.2.trans (by norm_num))).differentiableAt.differentiableWithinAt
  have hmono : MonotoneOn (fun x ↦ anariRezaeiPhiThree x (11/25))
      (Set.Icc q (11/25)) :=
    monotoneOn_of_deriv_nonneg (convex_Icc q (11/25)) hcont hdiff
      fun x hx ↦ by
        have hx' : q < x ∧ x < 11/25 := by simpa using hx
        rw [(hasDerivAt_anariRezaeiPhiThree_edge
          ((by norm_num : (0 : ℝ) < 1/5).trans_le (hq0.trans hx'.1.le))
          (hx'.2.trans (by norm_num))).deriv]
        exact anariRezaeiEdgeDerivative_nonneg (hq0.trans hx'.1.le) hx'.2.le
  exact hmono ⟨le_rfl, hq1⟩ ⟨hq1, le_rfl⟩ hq1

/-- Every point of the boundary edge satisfies the sharp `log 2` bound. -/
theorem anariRezaeiPhiThree_edge_le
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 11/25) :
    anariRezaeiPhiThree q (11/25) ≤ Real.log 2 := by
  by_cases hq : q ≤ 1/5
  · have hmax := anariRezaeiPhiThree_edge_convex.le_max_of_mem_Icc
      (x := (0 : ℝ)) (y := (1/5 : ℝ)) (z := q)
      (by norm_num) (by norm_num) ⟨hq0, hq⟩
    have hright : anariRezaeiPhiThree (1/5) (11/25) ≤ Real.log 2 :=
      (anariRezaeiPhiThree_edge_le_diagonal (by norm_num) (by norm_num)).trans
        anariRezaeiPhiThree_diagonal_le
    exact hmax.trans (max_le anariRezaeiPhiThree_zero_edge_le hright)
  · exact (anariRezaeiPhiThree_edge_le_diagonal (le_of_not_ge hq) hq1).trans
      anariRezaeiPhiThree_diagonal_le

/-- Exact replacement for the source's computer-assisted three-variable
base case. -/
theorem anariRezaeiPhiThree_le_log_two
    {q s : ℝ} (hq0 : 0 ≤ q) (hs0 : 0 ≤ s)
    (hq : q ≤ 11/25) (hs : s ≤ 11/25) :
    anariRezaeiPhiThree q s ≤ Real.log 2 := by
  rcases le_total q s with hqs | hsq
  · exact (anariRezaeiPhiThree_le_boundary hq0 hqs hs).trans
      (anariRezaeiPhiThree_edge_le hq0 hq)
  · rw [anariRezaeiPhiThree_comm]
    exact (anariRezaeiPhiThree_le_boundary hs0 hsq hq).trans
      (anariRezaeiPhiThree_edge_le hs0 hs)

/-- The three-coordinate vector with entries `q`, `1 - q - s`, and `s`. -/
def anariRezaeiThreeVector (q s : ℝ) : Fin 3 → ℝ :=
  ![q, 1-q-s, s]

theorem anariRezaeiThreeVector_probability
    {q s : ℝ} (hq : 0 ≤ q) (hs : 0 ≤ s) (hqs : q+s ≤ 1) :
    IsProbabilityVector (anariRezaeiThreeVector q s) := by
  constructor
  · intro i
    fin_cases i <;> simp [anariRezaeiThreeVector] <;> linarith
  · norm_num [anariRezaeiThreeVector, Fin.sum_univ_succ]

theorem anariRezaeiPhi_threeVector (q s : ℝ) :
    anariRezaeiPhi (anariRezaeiThreeVector q s) =
      anariRezaeiPhiThree q s := by
  classical
  rw [anariRezaeiPhi, pairedRowScore]
  simp [suffixMass, reverseOrdering, anariRezaeiThreeVector,
    Fin.sum_univ_succ, anariRezaeiPhiThree]
  simp only [Real.negMulLog_def]
  ring_nf

end BeyondBethe
