/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.CorvajaZannier.GlobalWronskianPlaceSum
public import Mathlib.Tactic

/-!
# Degree-weighted Corvaja--Zannier Wronskian summation

The published proof sums local orders with the residue degree of each place.
This module derives the weighted version of the four-case global inequality by
replacing a place of weight `e` by `e` identical copies and applying
`globalWronskianInequality_of_placewiseBounds`.

This is the finite combinatorial form of the weighted divisor summation in
Corvaja--Zannier, Proposition 2 (published reconstruction, pp. 15--16).
-/

@[expose] public section

namespace BGS.CorvajaZannier

noncomputable section

private abbrev ReplicatedPlace {ι : Type*} (weight : ι → ℕ) :=
  Σ i, Fin (weight i)

private def replicatedFinset {ι : Type*} [Fintype ι] [DecidableEq ι]
    (weight : ι → ℕ) (S : Finset ι) :
    Finset (ReplicatedPlace weight) := by
  classical
  exact Finset.univ.filter (fun x ↦ x.1 ∈ S)

private theorem sum_replicatedFinset
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (weight : ι → ℕ) (S : Finset ι) (F : ι → ℤ) :
    ∑ x ∈ replicatedFinset weight S, F x.1 =
      ∑ i ∈ S, (weight i : ℤ) * F i := by
  classical
  rw [replicatedFinset, Finset.sum_filter, Fintype.sum_sigma]
  calc
    ∑ i, ∑ _j : Fin (weight i), (if i ∈ S then F i else 0) =
        ∑ i, if i ∈ S then (weight i : ℤ) * F i else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i ∈ S
      · simp [hi, Finset.sum_const]
      · simp [hi]
    _ = ∑ i ∈ S, (weight i : ℤ) * F i := by
      rw [← Finset.sum_filter]
      congr 1
      ext i
      simp

private theorem card_replicatedFinset
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (weight : ι → ℕ) (S : Finset ι) :
    (replicatedFinset weight S).card = ∑ i ∈ S, weight i := by
  classical
  have h := sum_replicatedFinset weight S (fun _ ↦ (1 : ℤ))
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h
  exact_mod_cast h

/-- Residue-degree-weighted finite-support form of the global summation step in
the proof of Corvaja--Zannier Proposition 2. -/
theorem globalWronskianInequality_of_weightedPlacewiseBounds
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (weight : ι → ℕ) (S : Finset ι)
    (ordU ordV ordRho ordGrid ordW : ι → ℤ)
    (h k n sigma degreeU degreeV chi heightOutside : ℕ)
    (canonicalDegree : ℤ)
    (hUOutside : ∀ i, i ∉ S → ordU i = 0)
    (hGridOutside : ∀ i, i ∉ S → ordGrid i = 0)
    (hUSum : ∑ i, ordU i * (weight i : ℤ) = 0)
    (hGridSum : ∑ i, ordGrid i * (weight i : ℤ) = 0)
    (hDegreeV : ∑ i ∈ S.filter (fun i ↦ 0 < ordV i),
      ordV i * (weight i : ℤ) = degreeV)
    (hOutsideHeight :
      ∑ i ∈ Finset.univ.filter (fun i ↦ i ∉ S ∧ ordRho i < 0),
        ordRho i * (weight i : ℤ) = -(heightOutside : ℤ))
    (hCanonical : ∑ i, ordW i * (weight i : ℤ) =
      (sigma : ℤ) * canonicalDegree)
    (hEuler : canonicalDegree + (∑ i ∈ S, weight i : ℕ) ≤ (chi : ℤ))
    (hRhoSupport :
      -((degreeU : ℤ) + (degreeV : ℤ)) ≤
        ∑ i ∈ S, ordRho i * (weight i : ℤ))
    (hCaseI : ∀ i, i ∉ S → ordRho i < 0 →
      (n : ℤ) * ordRho i ≤ ordW i)
    (hCaseII : ∀ i, i ∉ S → 0 ≤ ordRho i → 0 ≤ ordW i)
    (hCaseIII : ∀ i, i ∈ S → 0 < ordV i →
      ((k * (k - 1) / 2 : ℕ) : ℤ) * ordU i +
        ((h * k : ℕ) : ℤ) * ordV i + (k : ℤ) * ordRho i +
        ordGrid i - (sigma : ℤ) ≤ ordW i)
    (hCaseIV : ∀ i, i ∈ S → ordV i ≤ 0 →
      ((k * (k - 1) / 2 : ℕ) : ℤ) * ordU i +
        (k : ℤ) * ordRho i + ordGrid i - (sigma : ℤ) ≤ ordW i) :
    ((h * k : ℕ) : ℤ) * (degreeV : ℤ) -
        (k : ℤ) * ((degreeU : ℤ) + (degreeV : ℤ)) -
        (sigma : ℤ) * (chi : ℤ) ≤
      (n : ℤ) * (heightOutside : ℤ) := by
  classical
  let ι' := ReplicatedPlace weight
  let S' : Finset ι' := replicatedFinset weight S
  let lift (F : ι → ℤ) : ι' → ℤ := fun x ↦ F x.1
  apply globalWronskianInequality_of_placewiseBounds
    S' (lift ordU) (lift ordV) (lift ordRho) (lift ordGrid) (lift ordW)
    h k n sigma degreeU degreeV chi heightOutside canonicalDegree
  · intro x hx
    apply hUOutside x.1
    simpa [S', replicatedFinset] using hx
  · intro x hx
    apply hGridOutside x.1
    simpa [S', replicatedFinset] using hx
  · simpa [lift, replicatedFinset, mul_comm] using
      (sum_replicatedFinset weight Finset.univ ordU).trans
        (by simpa [mul_comm] using hUSum)
  · simpa [lift, replicatedFinset, mul_comm] using
      (sum_replicatedFinset weight Finset.univ ordGrid).trans
        (by simpa [mul_comm] using hGridSum)
  · rw [show S'.filter (fun x ↦ 0 < lift ordV x) =
        replicatedFinset weight (S.filter fun i ↦ 0 < ordV i) by
      ext x
      simp [S', replicatedFinset, lift]]
    rw [sum_replicatedFinset]
    simpa [mul_comm] using hDegreeV
  · rw [show Finset.univ.filter (fun x : ι' ↦ x ∉ S' ∧ lift ordRho x < 0) =
        replicatedFinset weight
          (Finset.univ.filter fun i ↦ i ∉ S ∧ ordRho i < 0) by
      ext x
      simp [S', replicatedFinset, lift]]
    rw [sum_replicatedFinset]
    simpa [mul_comm] using hOutsideHeight
  · simpa [lift, replicatedFinset, mul_comm] using
      (sum_replicatedFinset weight Finset.univ ordW).trans
        (by simpa [mul_comm] using hCanonical)
  · rw [show S'.card = ∑ i ∈ S, weight i by
      exact card_replicatedFinset weight S]
    exact hEuler
  · rw [show ∑ x ∈ S', lift ordRho x =
        ∑ i ∈ S, (weight i : ℤ) * ordRho i by
      exact sum_replicatedFinset weight S ordRho]
    simpa [mul_comm] using hRhoSupport
  · intro x hxS hxRho
    exact hCaseI x.1 (by simpa [S', replicatedFinset] using hxS) hxRho
  · intro x hxS hxRho
    exact hCaseII x.1 (by simpa [S', replicatedFinset] using hxS) hxRho
  · intro x hxS hxV
    exact hCaseIII x.1 (by simpa [S', replicatedFinset] using hxS) hxV
  · intro x hxS hxV
    exact hCaseIV x.1 (by simpa [S', replicatedFinset] using hxS) hxV

end

end BGS.CorvajaZannier
