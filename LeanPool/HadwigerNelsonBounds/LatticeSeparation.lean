/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.HadwigerNelsonBounds.Voronoi

/-!
# Separation of equally colored lattice points

This module proves the modular quadratic-form estimate that separates distinct
lattice points carrying the same residue color.
-/

namespace HadwigerNelsonBounds

open SimpleGraph

/-- **Number-theoretic core of (G2).** If `(Δi, Δj) ∈ ℤ²` is nonzero and
    `Δi + 3·Δj ≡ 0 (mod 7)`, then `Δi² + Δi·Δj + Δj² ≥ 7`.

    Proof outline: Let `Q := Δi² + Δi·Δj + Δj²`. Then
        4·Q = (2·Δi + Δj)² + 3·Δj².
    From `Δi + 3·Δj ≡ 0 (mod 7)`:
        `2·Δi + Δj = 2·(Δi + 3·Δj) − 5·Δj ≡ −5·Δj ≡ 2·Δj (mod 7)`,
    so `(2·Δi + Δj)² ≡ 4·Δj² (mod 7)`, hence
        `4·Q ≡ 4·Δj² + 3·Δj² = 7·Δj² ≡ 0 (mod 7)`.
    Since `gcd(4, 7) = 1`, `7 ∣ Q`.
    Also `Q ≥ 0` (sum of squares after `4·Q = (2·Δi+Δj)² + 3·Δj²`), and
    `Q = 0` would force `Δj = 0` and `2·Δi + Δj = 0`, hence
    `Δi = Δj = 0`, contradicting non-zeroness. So `Q > 0` and `7 ∣ Q`,
    giving `Q ≥ 7`. -/
private lemma sublattice_quadratic_form_ge_seven
    {di dj : ℤ} (hne : (di, dj) ≠ (0, 0))
    (hmod : (7 : ℤ) ∣ (di + 3 * dj)) :
    di ^ 2 + di * dj + dj ^ 2 ≥ 7 := by
  -- 7 divides di + 3·dj, so 2·di + dj = 2·(di + 3·dj) - 5·dj,
  -- and (2·di + dj)² ≡ 25·dj² ≡ 4·dj² (mod 7).
  -- Hence 4·Q = (2·di + dj)² + 3·dj² ≡ 7·dj² ≡ 0 (mod 7), so 7 | Q.
  have hQ_nonneg : 0 ≤ di ^ 2 + di * dj + dj ^ 2 := by
    have h4Q_form : 4 * (di ^ 2 + di * dj + dj ^ 2)
        = (2 * di + dj) ^ 2 + 3 * dj ^ 2 := by ring
    have : 0 ≤ (2 * di + dj) ^ 2 + 3 * dj ^ 2 := by positivity
    linarith [this, h4Q_form]
  -- 4·Q = (di + 3·dj)·(4·di − 8·dj) + 7·(4·dj²), so 7 | 4·Q.
  have hdvd_4Q : (7 : ℤ) ∣ (4 * (di ^ 2 + di * dj + dj ^ 2)) := by
    have hid : 4 * (di ^ 2 + di * dj + dj ^ 2)
        = (di + 3 * dj) * (4 * di - 8 * dj) + 7 * (4 * dj ^ 2) := by ring
    rw [hid]
    exact Dvd.dvd.add (Dvd.dvd.mul_right hmod _) (dvd_mul_right _ _)
  -- 7 coprime with 4, so 7 | Q.
  have hdvd_Q : (7 : ℤ) ∣ (di ^ 2 + di * dj + dj ^ 2) := by
    have h74 : IsCoprime (7 : ℤ) 4 := by decide
    exact h74.dvd_of_dvd_mul_left hdvd_4Q
  -- Q > 0 or Q = 0. If Q = 0, then (di, dj) = (0, 0).
  rcases hQ_nonneg.lt_or_eq with hpos | hzero
  · -- Q > 0 and 7 | Q, so Q ≥ 7.
    have : (7 : ℤ) ≤ di ^ 2 + di * dj + dj ^ 2 :=
      Int.le_of_dvd hpos hdvd_Q
    linarith
  · -- Q = 0. We show this contradicts hne.
    exfalso
    have hQ_eq : (di ^ 2 + di * dj + dj ^ 2) = 0 := hzero.symm
    have h4Q : 4 * (di ^ 2 + di * dj + dj ^ 2) = 0 := by linarith
    have h4Q_form : 4 * (di ^ 2 + di * dj + dj ^ 2)
        = (2 * di + dj) ^ 2 + 3 * dj ^ 2 := by ring
    rw [h4Q_form] at h4Q
    have h1 : (2 * di + dj) ^ 2 = 0 ∧ (3 : ℤ) * dj ^ 2 = 0 := by
      have hsq_nn : 0 ≤ (2 * di + dj) ^ 2 := sq_nonneg _
      have hd_nn : 0 ≤ (3 : ℤ) * dj ^ 2 := by positivity
      omega
    have hdj_zero : dj = 0 := by
      have : dj ^ 2 = 0 := by linarith [h1.2]
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    have hdi_zero : di = 0 := by
      have h0 : 2 * di + dj = 0 := by
        have hsq : (2 * di + dj) ^ 2 = 0 := h1.1
        exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
      omega
    apply hne
    simp [hdi_zero, hdj_zero]

/-- **(G2) Same-color lattice separation.** Two distinct lattice points
    with the same `(i + 3·j) mod 7` color are at Euclidean distance at
    least `a·√7`.

    Proof: if `(i, j) ≠ (i', j')` and `(i + 3·j) ≡ (i' + 3·j') (mod 7)`,
    then `(Δi, Δj) := (i − i', j − j')` is a nonzero integer vector
    with `Δi + 3·Δj ≡ 0 (mod 7)`. The Euclidean length squared of
    `Δi·v₁ + Δj·v₂` is
        a²·(Δi² + Δi·Δj + Δj²).
    By `sublattice_quadratic_form_ge_seven`, the integer quadratic form
    `Δi² + Δi·Δj + Δj² ≥ 7`, so squared distance ≥ 7·a², giving distance
    ≥ a·√7. -/
lemma dist_between_same_color_lattice_points
    {i j i' j' : ℤ} (hne : (i, j) ≠ (i', j'))
    (hsame : ((i + 3 * j) : ZMod 7) = ((i' + 3 * j') : ZMod 7)) :
    dist (isbellLatticePoint i j) (isbellLatticePoint i' j')
      ≥ isbellLatticeStep * Real.sqrt 7 := by
  -- Translate ZMod-7 equality to integer divisibility 7 ∣ ((i - i') + 3·(j - j')).
  have hmod : (7 : ℤ) ∣ ((i - i') + 3 * (j - j')) := by
    have hdiff_zero : (((i - i') + 3 * (j - j') : ℤ) : ZMod 7) = 0 := by
      push_cast
      -- Goal: (i : ZMod 7) - i' + 3 * (j - j') = 0
      -- From hsame : (i + 3*j) = (i' + 3*j') in ZMod 7, subtract.
      have hs : ((i : ZMod 7) + 3 * (j : ZMod 7)) - ((i' : ZMod 7) + 3 * (j' : ZMod 7)) = 0 := by
        rw [sub_eq_zero]; exact hsame
      linear_combination hs
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hdiff_zero
  -- Translate (i, j) ≠ (i', j') to ((i - i'), (j - j')) ≠ (0, 0).
  have hne' : (i - i', j - j') ≠ (0, 0) := by
    intro h
    apply hne
    have h1 : i - i' = 0 := (Prod.mk.injEq _ _ _ _).mp h |>.1
    have h2 : j - j' = 0 := (Prod.mk.injEq _ _ _ _).mp h |>.2
    have : i = i' := by omega
    have : j = j' := by omega
    simp_all
  -- Apply the number-theoretic core.
  have hQ_ge_7 : (7 : ℤ) ≤ (i - i') ^ 2 + (i - i') * (j - j') + (j - j') ^ 2 :=
    sublattice_quadratic_form_ge_seven hne' hmod
  have hQ_ge_7_real :
      (7 : ℝ) ≤
        ((i : ℝ) - i') ^ 2 +
          ((i : ℝ) - i') * ((j : ℝ) - j') +
          ((j : ℝ) - j') ^ 2 := by
    have h1 :
        ((7 : ℤ) : ℝ) ≤
          (((i - i') ^ 2 + (i - i') * (j - j') +
            (j - j') ^ 2 : ℤ) : ℝ) := by
      exact_mod_cast hQ_ge_7
    have hcast : (((i - i') ^ 2 + (i - i') * (j - j') + (j - j') ^ 2 : ℤ) : ℝ)
        = ((i : ℝ) - i') ^ 2 + ((i : ℝ) - i') * ((j : ℝ) - j') + ((j : ℝ) - j') ^ 2 := by
      push_cast; ring
    rw [hcast] at h1
    exact_mod_cast h1
  -- Squared distance equals a²·Q.
  have hdist_sq := isbellLatticePoint_dist_sq i j i' j'
  -- Distance is nonneg.
  have hdist_nn : (0 : ℝ) ≤ dist (isbellLatticePoint i j) (isbellLatticePoint i' j') :=
    dist_nonneg
  -- isbellLatticeStep ≥ 0.
  have ha_nn : (0 : ℝ) ≤ isbellLatticeStep := by unfold isbellLatticeStep; norm_num
  -- √7 ≥ 0.
  have hsqrt7_nn : (0 : ℝ) ≤ Real.sqrt 7 := Real.sqrt_nonneg _
  -- The squared bound.
  have hsq_bound :
      (isbellLatticeStep * Real.sqrt 7) ^ 2
        ≤ dist (isbellLatticePoint i j) (isbellLatticePoint i' j') ^ 2 := by
    rw [hdist_sq]
    have hsq7 : Real.sqrt 7 * Real.sqrt 7 = 7 := Real.mul_self_sqrt (by norm_num)
    have hsq7_eq : (isbellLatticeStep * Real.sqrt 7) ^ 2 = isbellLatticeStep ^ 2 * 7 := by
      have : (isbellLatticeStep * Real.sqrt 7) ^ 2
          = isbellLatticeStep ^ 2 * (Real.sqrt 7 * Real.sqrt 7) := by ring
      rw [this, hsq7]
    rw [hsq7_eq]
    have hstep_sq_nn : (0 : ℝ) ≤ isbellLatticeStep ^ 2 := sq_nonneg _
    nlinarith [hQ_ge_7_real, hstep_sq_nn]
  -- Square root of the squared bound: since both sides are nonneg, squared inequality
  -- transfers to the inequality on the original values.
  have h_step7_nn : 0 ≤ isbellLatticeStep * Real.sqrt 7 := by positivity
  have hkey : isbellLatticeStep * Real.sqrt 7
      ≤ dist (isbellLatticePoint i j) (isbellLatticePoint i' j') := by
    -- Want: a·√7 ≤ dist. Have: (a·√7)² ≤ dist², and both ≥ 0.
    -- Use abs_le_of_sq_le_sq.
    nlinarith [hsq_bound, hdist_nn, h_step7_nn,
      sq_nonneg (dist (isbellLatticePoint i j) (isbellLatticePoint i' j')
        - isbellLatticeStep * Real.sqrt 7),
      sq_nonneg (dist (isbellLatticePoint i j) (isbellLatticePoint i' j')
        + isbellLatticeStep * Real.sqrt 7)]
  linarith [hkey]

end HadwigerNelsonBounds
