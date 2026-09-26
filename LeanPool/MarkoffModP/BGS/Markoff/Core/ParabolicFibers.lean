/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.Markoff.Core.Normalization
public import LeanPool.MarkoffModP.BGS.Markoff.Core.Rotation
public import Mathlib.NumberTheory.LegendreSymbol.Basic

/-!
# Parabolic fibers of the normalized Markoff surface

This module exposes the elementary algebra suppressed in Lemma 3 of
Bourgain--Gamburd--Sarnak.  The parameter fixed in the first coordinate is a normalized trace,
so the exceptional values are `2` and `-2`, not the original-coordinate values `2 / 3` and
`-2 / 3`.
-/

@[expose] public section

namespace BGS.Markoff

universe u

open scoped Matrix

/-- One of the two affine lines above the normalized parabolic trace `2`.  Replacing `i` by
`-i` gives the other line. -/
def parabolicLineAtTwo {R : Type u} [CommRing R] (i t : R) : NormalizedPoint R :=
  ⟨2, t, t + 2 * i⟩

/-- One of the two affine lines above the normalized parabolic trace `-2`.  Replacing `i` by
`-i` gives the other line. -/
def parabolicLineAtNegTwo {R : Type u} [CommRing R] (i t : R) : NormalizedPoint R :=
  ⟨-2, t, -t + 2 * i⟩

/-- At normalized trace `2`, the Markoff equation is the factorized equation
`(u₃ - u₂)² = -4`. -/
theorem normalizedPolynomial_at_two {R : Type u} [CommRing R] (t s : R) :
    normalizedPolynomial (⟨(2 : R), t, s⟩ : NormalizedPoint R) = (s - t) ^ 2 + 4 := by
  simp [normalizedPolynomial]
  ring

/-- At normalized trace `-2`, the Markoff equation is the factorized equation
`(u₃ + u₂)² = -4`. -/
theorem normalizedPolynomial_at_neg_two {R : Type u} [CommRing R] (t s : R) :
    normalizedPolynomial (⟨(-2 : R), t, s⟩ : NormalizedPoint R) = (s + t) ^ 2 + 4 := by
  simp [normalizedPolynomial]
  ring

theorem isNormalizedMarkoff_at_two_iff {R : Type u} [CommRing R] (t s : R) :
    IsNormalizedMarkoff (⟨(2 : R), t, s⟩ : NormalizedPoint R) ↔
      (s - t) ^ 2 = -(2 : R) ^ 2 := by
  rw [IsNormalizedMarkoff, normalizedPolynomial_at_two]
  constructor <;> intro h
  · linear_combination h
  · linear_combination h

theorem isNormalizedMarkoff_at_neg_two_iff {R : Type u} [CommRing R] (t s : R) :
    IsNormalizedMarkoff (⟨(-2 : R), t, s⟩ : NormalizedPoint R) ↔
      (s + t) ^ 2 = -(2 : R) ^ 2 := by
  rw [IsNormalizedMarkoff, normalizedPolynomial_at_neg_two]
  constructor <;> intro h
  · linear_combination h
  · linear_combination h

/-- Once a square root `i` of `-1` is fixed, the trace-`2` equation has exactly the two
displayed line solutions. -/
theorem isNormalizedMarkoff_at_two_iff_on_parabolic_lines
    {R : Type u} [CommRing R] [NoZeroDivisors R] {i t s : R} (hi : i ^ 2 = -1) :
    IsNormalizedMarkoff (⟨2, t, s⟩ : NormalizedPoint R) ↔
      s = t + 2 * i ∨ s = t + 2 * (-i) := by
  rw [isNormalizedMarkoff_at_two_iff]
  have hroot : (2 * i) ^ 2 = -(2 : R) ^ 2 := by
    rw [mul_pow, hi]
    ring
  rw [← hroot, sq_eq_sq_iff_eq_or_eq_neg]
  constructor
  · rintro (h | h)
    · left
      linear_combination h
    · right
      linear_combination h
  · rintro (h | h)
    · left
      linear_combination h
    · right
      linear_combination h

/-- Once a square root `i` of `-1` is fixed, the trace-`-2` equation has exactly the two
displayed line solutions. -/
theorem isNormalizedMarkoff_at_neg_two_iff_on_parabolic_lines
    {R : Type u} [CommRing R] [NoZeroDivisors R] {i t s : R} (hi : i ^ 2 = -1) :
    IsNormalizedMarkoff (⟨-2, t, s⟩ : NormalizedPoint R) ↔
      s = -t + 2 * i ∨ s = -t + 2 * (-i) := by
  rw [isNormalizedMarkoff_at_neg_two_iff]
  have hroot : (2 * i) ^ 2 = -(2 : R) ^ 2 := by
    rw [mul_pow, hi]
    ring
  rw [← hroot, sq_eq_sq_iff_eq_or_eq_neg]
  constructor
  · rintro (h | h)
    · left
      linear_combination h
    · right
      linear_combination h
  · rintro (h | h)
    · left
      linear_combination h
    · right
      linear_combination h

/-- Set-theoretic classification of the normalized trace-`2` fiber as two affine lines. -/
theorem normalizedFiber1_two_eq_parabolic_lines
    {R : Type u} [CommRing R] [NoZeroDivisors R] (i : R) (hi : i ^ 2 = -1) :
    normalizedFiber1 (2 : R) =
      Set.range (parabolicLineAtTwo i) ∪ Set.range (parabolicLineAtTwo (-i)) := by
  ext x
  rcases x with ⟨u1, u2, u3⟩
  constructor
  · rintro ⟨hx, hx1⟩
    change u1 = 2 at hx1
    subst u1
    rw [isNormalizedMarkoff_at_two_iff_on_parabolic_lines hi] at hx
    rcases hx with hline | hline
    · left
      refine ⟨u2, ?_⟩
      ext <;> simp [parabolicLineAtTwo, hline]
    · right
      refine ⟨u2, ?_⟩
      ext <;> simp [parabolicLineAtTwo, hline]
  · rintro (⟨t, ht⟩ | ⟨t, ht⟩)
    · rw [← ht]
      constructor
      · change IsNormalizedMarkoff (⟨2, t, t + 2 * i⟩ : NormalizedPoint R)
        rw [isNormalizedMarkoff_at_two_iff_on_parabolic_lines hi]
        exact Or.inl rfl
      · rfl
    · rw [← ht]
      constructor
      · change IsNormalizedMarkoff (⟨2, t, t + 2 * (-i)⟩ : NormalizedPoint R)
        rw [isNormalizedMarkoff_at_two_iff_on_parabolic_lines hi]
        exact Or.inr rfl
      · rfl

/-- Set-theoretic classification of the normalized trace-`-2` fiber as two affine lines. -/
theorem normalizedFiber1_neg_two_eq_parabolic_lines
    {R : Type u} [CommRing R] [NoZeroDivisors R] (i : R) (hi : i ^ 2 = -1) :
    normalizedFiber1 (-2 : R) =
      Set.range (parabolicLineAtNegTwo i) ∪ Set.range (parabolicLineAtNegTwo (-i)) := by
  ext x
  rcases x with ⟨u1, u2, u3⟩
  constructor
  · rintro ⟨hx, hx1⟩
    change u1 = -2 at hx1
    subst u1
    rw [isNormalizedMarkoff_at_neg_two_iff_on_parabolic_lines hi] at hx
    rcases hx with hline | hline
    · left
      refine ⟨u2, ?_⟩
      ext <;> simp [parabolicLineAtNegTwo, hline]
    · right
      refine ⟨u2, ?_⟩
      ext <;> simp [parabolicLineAtNegTwo, hline]
  · rintro (⟨t, ht⟩ | ⟨t, ht⟩)
    · rw [← ht]
      constructor
      · change IsNormalizedMarkoff (⟨-2, t, -t + 2 * i⟩ : NormalizedPoint R)
        rw [isNormalizedMarkoff_at_neg_two_iff_on_parabolic_lines hi]
        exact Or.inl rfl
      · rfl
    · rw [← ht]
      constructor
      · change IsNormalizedMarkoff (⟨-2, t, -t + 2 * (-i)⟩ : NormalizedPoint R)
        rw [isNormalizedMarkoff_at_neg_two_iff_on_parabolic_lines hi]
        exact Or.inr rfl
      · rfl

/-- Each parabolic-line parametrization is injective because its second coordinate is the
parameter. -/
theorem parabolicLineAtTwo_injective
    {R : Type u} [CommRing R] (i : R) : Function.Injective (parabolicLineAtTwo i) := by
  intro t s h
  exact congrArg NormalizedPoint.u2 h

/-- Each trace-`-2` parabolic-line parametrization is injective. -/
theorem parabolicLineAtNegTwo_injective
    {R : Type u} [CommRing R] (i : R) : Function.Injective (parabolicLineAtNegTwo i) := by
  intro t s h
  exact congrArg NormalizedPoint.u2 h

/-- The two trace-`2` lines are disjoint whenever `4i` is nonzero. -/
theorem parabolicLineAtTwo_disjoint
    {R : Type u} [CommRing R] (i : R) (hfourI : (4 : R) * i ≠ 0) :
    Disjoint (Set.range (parabolicLineAtTwo i)) (Set.range (parabolicLineAtTwo (-i))) := by
  rw [Set.disjoint_left]
  rintro x ⟨t, rfl⟩ ⟨s, hs⟩
  have hparameter := congrArg NormalizedPoint.u2 hs
  have hst : s = t := by simpa [parabolicLineAtTwo] using hparameter
  subst s
  have hthird := congrArg NormalizedPoint.u3 hs
  change t + 2 * (-i) = t + 2 * i at hthird
  apply hfourI
  linear_combination -hthird

/-- The two trace-`-2` lines are disjoint whenever `4i` is nonzero. -/
theorem parabolicLineAtNegTwo_disjoint
    {R : Type u} [CommRing R] (i : R) (hfourI : (4 : R) * i ≠ 0) :
    Disjoint (Set.range (parabolicLineAtNegTwo i))
      (Set.range (parabolicLineAtNegTwo (-i))) := by
  rw [Set.disjoint_left]
  rintro x ⟨t, rfl⟩ ⟨s, hs⟩
  have hparameter := congrArg NormalizedPoint.u2 hs
  have hst : s = t := by simpa [parabolicLineAtNegTwo] using hparameter
  subst s
  have hthird := congrArg NormalizedPoint.u3 hs
  change -t + 2 * (-i) = -t + 2 * i at hthird
  apply hfourI
  linear_combination -hthird

/-- The normalized rotation at trace `2` acts by translation on either parabolic line. -/
@[simp]
theorem normalizedRotate1_parabolicLineAtTwo
    {R : Type u} [CommRing R] (i t : R) :
    normalizedRotate1 (parabolicLineAtTwo i t) = parabolicLineAtTwo i (t + 2 * i) := by
  ext <;> simp [normalizedRotate1, parabolicLineAtTwo]
  ring

/-- The normalized rotation at trace `-2` exchanges the two parabolic lines. -/
@[simp]
theorem normalizedRotate1_parabolicLineAtNegTwo
    {R : Type u} [CommRing R] (i t : R) :
    normalizedRotate1 (parabolicLineAtNegTwo i t) =
      parabolicLineAtNegTwo (-i) (-t + 2 * i) := by
  ext <;> simp [normalizedRotate1, parabolicLineAtNegTwo]
  ring

/-- Two steps of the trace-`-2` rotation return to the same line and translate its parameter. -/
theorem normalizedRotate1_twice_parabolicLineAtNegTwo
    {R : Type u} [CommRing R] (i t : R) :
    normalizedRotate1 (normalizedRotate1 (parabolicLineAtNegTwo i t)) =
      parabolicLineAtNegTwo i (t - 4 * i) := by
  ext <;> simp [normalizedRotate1, parabolicLineAtNegTwo] <;> ring

/-- A natural number strictly between zero and the modulus remains nonzero in `ZMod p`. -/
private theorem natCast_ne_zero_zmod_of_pos_of_lt
    {n p : ℕ} (hn : 0 < n) (hnp : n < p) : (n : ZMod p) ≠ 0 := by
  intro hzero
  have hdvd : p ∣ n := (ZMod.natCast_eq_zero_iff n p).mp hzero
  exact (Nat.not_le_of_gt hnp) (Nat.le_of_dvd hn hdvd)

/-- If `p ≡ 3 (mod 4)`, the normalized trace-`2` fiber is empty. -/
theorem normalizedFiber1_two_eq_empty_of_mod_four_eq_three
    (p : ℕ) [Fact p.Prime] (hmod : p % 4 = 3) :
    normalizedFiber1 (2 : ZMod p) = ∅ := by
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  rcases x with ⟨u1, u2, u3⟩
  rintro ⟨hsurface, hu1⟩
  change u1 = 2 at hu1
  subst u1
  have hpGreaterThanTwo : 2 < p := by
    by_contra hp
    have hpLe : p ≤ 2 := Nat.le_of_not_gt hp
    interval_cases p <;> norm_num at hmod
  have htwo : (2 : ZMod p) ≠ 0 :=
    natCast_ne_zero_zmod_of_pos_of_lt (by norm_num) hpGreaterThanTwo
  have hsquare : (u3 - u2) ^ 2 = -(2 : ZMod p) ^ 2 :=
    (isNormalizedMarkoff_at_two_iff u2 u3).mp hsurface
  exact (ZMod.mod_four_ne_three_of_sq_eq_neg_sq' htwo hsquare) hmod

/-- If `p ≡ 3 (mod 4)`, the normalized trace-`-2` fiber is empty. -/
theorem normalizedFiber1_neg_two_eq_empty_of_mod_four_eq_three
    (p : ℕ) [Fact p.Prime] (hmod : p % 4 = 3) :
    normalizedFiber1 (-2 : ZMod p) = ∅ := by
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  rcases x with ⟨u1, u2, u3⟩
  rintro ⟨hsurface, hu1⟩
  change u1 = -2 at hu1
  subst u1
  have hpGreaterThanTwo : 2 < p := by
    by_contra hp
    have hpLe : p ≤ 2 := Nat.le_of_not_gt hp
    interval_cases p <;> norm_num at hmod
  have htwo : (2 : ZMod p) ≠ 0 :=
    natCast_ne_zero_zmod_of_pos_of_lt (by norm_num) hpGreaterThanTwo
  have hsquare : (u3 + u2) ^ 2 = -(2 : ZMod p) ^ 2 :=
    (isNormalizedMarkoff_at_neg_two_iff u2 u3).mp hsurface
  exact (ZMod.mod_four_ne_three_of_sq_eq_neg_sq' htwo hsquare) hmod

/-- If `p ≡ 1 (mod 4)`, a square root of `-1` exists and simultaneously supplies the two-line
descriptions of both normalized parabolic fibers. -/
theorem exists_parabolic_line_decomposition_of_mod_four_eq_one
    (p : ℕ) [Fact p.Prime] (hmod : p % 4 = 1) :
    ∃ i : ZMod p,
      i ^ 2 = -1 ∧
      normalizedFiber1 (2 : ZMod p) =
        Set.range (parabolicLineAtTwo i) ∪ Set.range (parabolicLineAtTwo (-i)) ∧
      normalizedFiber1 (-2 : ZMod p) =
        Set.range (parabolicLineAtNegTwo i) ∪ Set.range (parabolicLineAtNegTwo (-i)) := by
  rcases (ZMod.exists_sq_eq_neg_one_iff (p := p)).2 (by omega) with ⟨i, hi⟩
  have hi' : i ^ 2 = -1 := by simpa [pow_two] using hi.symm
  exact ⟨i, hi', normalizedFiber1_two_eq_parabolic_lines i hi',
    normalizedFiber1_neg_two_eq_parabolic_lines i hi'⟩

/-- Iterating the trace-`2` rotation translates the line parameter by `2ni`. -/
theorem iterate_normalizedRotate1_parabolicLineAtTwo
    {R : Type u} [CommRing R] (n : ℕ) (i t : R) :
    (normalizedRotate1^[n]) (parabolicLineAtTwo i t) =
      parabolicLineAtTwo i (t + (n : R) * (2 * i)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih,
        normalizedRotate1_parabolicLineAtTwo]
      congr 1
      push_cast
      ring

/-- On either trace-`2` parabolic line over `ZMod p`, a rotation iterate returns to its starting
point exactly when the exponent is divisible by `p`. -/
theorem iterate_normalizedRotate1_parabolicLineAtTwo_eq_self_iff
    (p : ℕ) [Fact p.Prime] (hpTwo : p ≠ 2) (n : ℕ) (i t : ZMod p)
    (hi : i ^ 2 = -1) :
    (normalizedRotate1^[n]) (parabolicLineAtTwo i t) = parabolicLineAtTwo i t ↔ p ∣ n := by
  rw [iterate_normalizedRotate1_parabolicLineAtTwo]
  constructor
  · intro hreturn
    have hparameter := congrArg NormalizedPoint.u2 hreturn
    change t + (n : ZMod p) * (2 * i) = t at hparameter
    have hi0 : i ≠ 0 := by
      intro hi0
      subst i
      norm_num at hi
    have htwo : (2 : ZMod p) ≠ 0 :=
      natCast_ne_zero_zmod_of_pos_of_lt (by norm_num) (by
        have hpLower : 2 ≤ p := (Fact.out : p.Prime).two_le
        exact lt_of_le_of_ne hpLower (Ne.symm hpTwo))
    have hnzero : (n : ZMod p) = 0 := by
      apply (mul_eq_zero.mp ?_).resolve_right (mul_ne_zero htwo hi0)
      linear_combination hparameter
    exact (ZMod.natCast_eq_zero_iff n p).mp hnzero
  · intro hn
    have hnzero : (n : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff n p).2 hn
    simp [hnzero]

/-- Closed formula for powers of the unipotent normalized rotation with trace `2`. -/
theorem rho_two_pow {R : Type u} [CommRing R] (n : ℕ) :
    rho (2 : R) ^ n =
      !![(1 : R) - n, n; -(n : R), 1 + n] := by
  induction n with
  | zero =>
      ext a b
      fin_cases a <;> fin_cases b <;> simp
  | succ n ih =>
      rw [pow_succ, ih]
      ext a b
      fin_cases a <;> fin_cases b <;>
        simp [rho, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- A power of the trace-`2` rotation over `ZMod p` is the identity exactly at multiples of the
characteristic. -/
theorem rhoSL_two_pow_eq_one_iff
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    rhoSL (2 : ZMod p) ^ n = 1 ↔ p ∣ n := by
  constructor
  · intro hpower
    have hmatrix := congrArg
      (fun g : Matrix.SpecialLinearGroup (Fin 2) (ZMod p) =>
        (g : Matrix (Fin 2) (Fin 2) (ZMod p))) hpower
    change rho (2 : ZMod p) ^ n = 1 at hmatrix
    have hentry := congrArg (fun m : Matrix (Fin 2) (Fin 2) (ZMod p) => m 0 1) hmatrix
    simp [rho_two_pow] at hentry
    exact (ZMod.natCast_eq_zero_iff n p).mp hentry
  · intro hn
    have hnzero : (n : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff n p).2 hn
    apply Matrix.SpecialLinearGroup.ext
    intro a b
    change (rho (2 : ZMod p) ^ n) a b = (1 : Matrix (Fin 2) (Fin 2) (ZMod p)) a b
    fin_cases a <;> fin_cases b <;> simp [rho_two_pow, hnzero]

/-- The normalized trace-`2` rotation has exact group-theoretic order `p`. -/
theorem rotationOrder_two (p : ℕ) [Fact p.Prime] :
    rotationOrder (2 : ZMod p) = p := by
  rw [rotationOrder, orderOf_eq_iff (Fact.out : p.Prime).pos]
  constructor
  · exact (rhoSL_two_pow_eq_one_iff p p).2 dvd_rfl
  · intro m hmLower hmPositive hpower
    exact (Nat.not_dvd_of_pos_of_lt hmPositive hmLower)
      ((rhoSL_two_pow_eq_one_iff p m).mp hpower)

/-- Closed formula for powers of the nontrivial parabolic normalized rotation with trace `-2`.
The scalar factor records its eigenvalue `-1`; the remaining matrix is unipotent. -/
theorem rho_neg_two_pow {R : Type u} [CommRing R] (n : ℕ) :
    rho (-2 : R) ^ n =
      !![(-1 : R) ^ n * (1 - n), (-1 : R) ^ n * (-(n : R));
        (-1 : R) ^ n * n, (-1 : R) ^ n * (1 + n)] := by
  induction n with
  | zero =>
      ext a b
      fin_cases a <;> fin_cases b <;> simp
  | succ n ih =>
      rw [pow_succ, ih]
      ext a b
      fin_cases a <;> fin_cases b <;>
        simp [rho, Matrix.mul_apply, Fin.sum_univ_two, pow_succ] <;> ring

/-- A power of the trace-`-2` rotation over an odd prime field is the identity exactly at
multiples of `2p`. -/
theorem rhoSL_neg_two_pow_eq_one_iff
    (p : ℕ) [Fact p.Prime] (hpTwo : p ≠ 2) (n : ℕ) :
    rhoSL (-2 : ZMod p) ^ n = 1 ↔ 2 * p ∣ n := by
  have hnegOne : (-1 : ZMod p) ≠ 1 := by
    intro h
    have htwo : (2 : ZMod p) = 0 := by linear_combination -h
    have hpLe : p ≤ 2 := Nat.le_of_dvd (by norm_num)
      ((ZMod.natCast_eq_zero_iff 2 p).mp htwo)
    exact hpTwo (Nat.le_antisymm hpLe (Fact.out : p.Prime).two_le)
  constructor
  · intro hpower
    have hmatrix := congrArg
      (fun g : Matrix.SpecialLinearGroup (Fin 2) (ZMod p) =>
        (g : Matrix (Fin 2) (Fin 2) (ZMod p))) hpower
    change rho (-2 : ZMod p) ^ n = 1 at hmatrix
    have hoffDiagonal := congrArg
      (fun m : Matrix (Fin 2) (Fin 2) (ZMod p) => m 0 1) hmatrix
    have hnzero : (n : ZMod p) = 0 := by
      simpa [rho_neg_two_pow] using hoffDiagonal
    have hpdvd : p ∣ n := (ZMod.natCast_eq_zero_iff n p).mp hnzero
    have hdiagonal := congrArg
      (fun m : Matrix (Fin 2) (Fin 2) (ZMod p) => m 0 0) hmatrix
    have hsign : (-1 : ZMod p) ^ n = 1 := by
      simpa [rho_neg_two_pow, hnzero] using hdiagonal
    have heven : Even n := (neg_one_pow_eq_one_iff_even hnegOne).mp hsign
    exact (Fact.out : p.Prime).odd_of_ne_two hpTwo |>.coprime_two_left
      |>.mul_dvd_of_dvd_of_dvd heven.two_dvd hpdvd
  · intro hn
    have hpdvd : p ∣ n := (dvd_mul_left p 2).trans hn
    have htwoDvd : 2 ∣ n := (dvd_mul_right 2 p).trans hn
    have heven : Even n := even_iff_two_dvd.mpr htwoDvd
    have hnzero : (n : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff n p).2 hpdvd
    have hsign : (-1 : ZMod p) ^ n = 1 := heven.neg_one_pow
    apply Matrix.SpecialLinearGroup.ext
    intro a b
    change (rho (-2 : ZMod p) ^ n) a b = (1 : Matrix (Fin 2) (Fin 2) (ZMod p)) a b
    fin_cases a <;> fin_cases b <;>
      simp [rho_neg_two_pow, hnzero, hsign]

/-- The normalized trace-`-2` rotation has exact group-theoretic order `2p` for odd `p`. -/
theorem rotationOrder_neg_two
    (p : ℕ) [Fact p.Prime] (hpTwo : p ≠ 2) :
    rotationOrder (-2 : ZMod p) = 2 * p := by
  rw [rotationOrder, orderOf_eq_iff (Nat.mul_pos (by norm_num) (Fact.out : p.Prime).pos)]
  constructor
  · exact (rhoSL_neg_two_pow_eq_one_iff p hpTwo (2 * p)).2 dvd_rfl
  · intro m hmLower hmPositive hpower
    exact (Nat.not_dvd_of_pos_of_lt hmPositive hmLower)
      ((rhoSL_neg_two_pow_eq_one_iff p hpTwo m).mp hpower)

end BGS.Markoff
