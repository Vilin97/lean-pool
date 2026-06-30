/-
Copyright (c) 2026 Lazar Milikic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lazar Milikic
-/

import LeanPool.PythagoreanPolynomialParametrization.Basic

/-! # Source-level handoff lemmas

These declarations mirror the intermediate claims used in the paper's proofs. They are
kept separate from the explicit polynomial witnesses so each proof obligation has a
small, source-located target.
-/

namespace LeanPool.PythagoreanPolynomialParametrization



/-- The rational map
T(a,b,c) = (c(a²-b²)/2, cab, c(a²+b²)/2)
used in the proof of the main parametrization theorem. -/
def TMap (a b c : ℤ) : ℚ × ℚ × ℚ :=
  ((c : ℚ) * ((a : ℚ) ^ 2 - (b : ℚ) ^ 2) / 2,
    (c : ℚ) * (a : ℚ) * (b : ℚ),
    (c : ℚ) * ((a : ℚ) ^ 2 + (b : ℚ) ^ 2) / 2)

/-- A value of `TMap` is integral when all three rational coordinates are integers. -/
def IsIntegralTValue (a b c : ℤ) : Prop :=
  ∃ x y z : ℤ, TMap a b c = ((x : ℚ), (y : ℚ), (z : ℚ))

/-- The paper's parity condition for `T(a,b,c)` to have integer coordinates:
`c` is even or `a` and `b` have the same parity. -/
def PaperParityCondition (a b c : ℤ) : Prop :=
  Even c ∨ Even (a - b)

/-- Positive parameters for the paper's positive-triple variant of `T(a,b,c)`. -/
def PositiveTParameters (a b c : ℤ) : Prop :=
  0 < a ∧ 0 < b ∧ 0 < c ∧ b < a ∧ PaperParityCondition a b c

/-- The introductory source claim: every Pythagorean triple is covered by one of two
integer-coefficient polynomial families, and every value of those families is a
Pythagorean triple. -/
theorem pythagoreanTriple_two_integer_polynomial_families (x y z : ℤ) :
    IsPythagoreanTriple x y z ↔
      ∃ a b c : ℤ,
        (x = c * (a ^ 2 - b ^ 2) ∧
          y = (2 : ℤ) * c * a * b ∧
          z = c * (a ^ 2 + b ^ 2)) ∨
        (x = (2 : ℤ) * c * a * b ∧
          y = c * (a ^ 2 - b ^ 2) ∧
          z = c * (a ^ 2 + b ^ 2)) := by
  constructor
  · intro h
    have hp : PythagoreanTriple x y z := by
      simpa [IsPythagoreanTriple, PythagoreanTriple, pow_two] using h
    rcases (PythagoreanTriple.classification (x := x) (y := y) (z := z)).mp hp with
      ⟨k, m, n, hxy, hz⟩
    rcases hxy with hxy | hxy
    · rcases hxy with ⟨hx, hy⟩
      rcases hz with hz | hz
      · refine ⟨m, n, k, Or.inl ⟨?_, ?_, ?_⟩⟩
        · simpa using hx
        · rw [hy]
          ring
        · simpa using hz
      · refine ⟨-n, m, -k, Or.inl ⟨?_, ?_, ?_⟩⟩
        · rw [hx]
          ring
        · rw [hy]
          ring
        · rw [hz]
          ring
    · rcases hxy with ⟨hx, hy⟩
      rcases hz with hz | hz
      · refine ⟨m, n, k, Or.inr ⟨?_, ?_, ?_⟩⟩
        · rw [hx]
          ring
        · simpa using hy
        · simpa using hz
      · refine ⟨-n, m, -k, Or.inr ⟨?_, ?_, ?_⟩⟩
        · rw [hx]
          ring
        · rw [hy]
          ring
        · rw [hz]
          ring
  · rintro ⟨a, b, c, (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩)⟩
    · simp [IsPythagoreanTriple]
      ring
    · simp [IsPythagoreanTriple]
      ring

/-- Source proof handoff lemma: the set of Pythagorean triples is exactly the set of
integer triples in the range of `TMap`. -/
theorem pythagorean_iff_mem_TMap_range (x y z : ℤ) :
    IsPythagoreanTriple x y z ↔
      ∃ a b c : ℤ, TMap a b c = ((x : ℚ), (y : ℚ), (z : ℚ)) := by
  constructor
  · intro h
    rcases (pythagoreanTriple_two_integer_polynomial_families x y z).mp h with
      ⟨a, b, c, hfam⟩
    rcases hfam with hfam | hfam
    · rcases hfam with ⟨hx, hy, hz⟩
      refine ⟨a, b, (2 : ℤ) * c, ?_⟩
      ext <;> simp [TMap, hx, hy, hz] <;> ring
    · rcases hfam with ⟨hx, hy, hz⟩
      refine ⟨a + b, a - b, c, ?_⟩
      ext <;> simp [TMap, hx, hy, hz] <;> ring
  · rintro ⟨a, b, c, hT⟩
    dsimp [IsPythagoreanTriple]
    have hq : ((x : ℚ) ^ 2 + (y : ℚ) ^ 2 = (z : ℚ) ^ 2) := by
      have hpy : (TMap a b c).1 ^ 2 + (TMap a b c).2.1 ^ 2 = (TMap a b c).2.2 ^ 2 := by
        simp [TMap]
        ring
      simpa [hT] using hpy
    exact_mod_cast hq

private lemma rat_half_int_iff_even (n : ℤ) :
    (∃ k : ℤ, ((n : ℚ) / 2 = (k : ℚ))) ↔ Even n := by
  constructor
  · rintro ⟨k, hk⟩
    have hmul : (n : ℚ) = (2 : ℚ) * k := by
      nlinarith
    have hInt : n = 2 * k := by
      exact_mod_cast hmul
    simp [hInt]
  · intro hn
    rcases hn with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [hk]
    norm_num

private lemma even_sq_iff_even_int (n : ℤ) : Even (n ^ 2) ↔ Even n := by
  simpa [pow_two] using (Int.even_mul (m := n) (n := n))

private lemma even_sq_sub_sq_iff_even_sub (a b : ℤ) :
    Even (a ^ 2 - b ^ 2) ↔ Even (a - b) := by
  simp [Int.even_sub, even_sq_iff_even_int]

private lemma even_sq_add_sq_of_even_sub {a b : ℤ} (h : Even (a - b)) :
    Even (a ^ 2 + b ^ 2) := by
  have hab : Even a ↔ Even b := (Int.even_sub.mp h)
  exact Int.even_add.mpr (by simpa [even_sq_iff_even_int] using hab)

/-- Source proof handoff lemma: `T(a,b,c)` has integer coordinates iff the paper's
parity condition holds. -/
theorem TMap_integral_iff_parity (a b c : ℤ) :
    IsIntegralTValue a b c ↔ PaperParityCondition a b c := by
  constructor
  · rintro ⟨x, y, z, hT⟩
    have hxq : (c : ℚ) * ((a : ℚ) ^ 2 - (b : ℚ) ^ 2) / 2 = (x : ℚ) := by
      simpa [TMap] using congrArg Prod.fst hT
    have hprod : Even (c * (a ^ 2 - b ^ 2)) := by
      exact (rat_half_int_iff_even (c * (a ^ 2 - b ^ 2))).mp ⟨x, by
        simpa [pow_two] using hxq⟩
    rcases (Int.even_mul.mp hprod) with hc | hsq
    · exact Or.inl hc
    · exact Or.inr ((even_sq_sub_sq_iff_even_sub a b).mp hsq)
  · intro hpar
    have hdiff : Even (c * (a ^ 2 - b ^ 2)) := by
      rcases hpar with hc | hab
      · exact Int.even_mul.mpr (Or.inl hc)
      · exact Int.even_mul.mpr (Or.inr ((even_sq_sub_sq_iff_even_sub a b).mpr hab))
    have hsum : Even (c * (a ^ 2 + b ^ 2)) := by
      rcases hpar with hc | hab
      · exact Int.even_mul.mpr (Or.inl hc)
      · exact Int.even_mul.mpr (Or.inr (even_sq_add_sq_of_even_sub hab))
    rcases (rat_half_int_iff_even (c * (a ^ 2 - b ^ 2))).mpr hdiff with ⟨x, hx⟩
    rcases (rat_half_int_iff_even (c * (a ^ 2 + b ^ 2))).mpr hsum with ⟨z, hz⟩
    refine ⟨x, c * a * b, z, ?_⟩
    ext
    · simpa [TMap, pow_two] using hx
    · simp [TMap]
    · simpa [TMap, pow_two] using hz

/-- Source proof handoff lemma: the parity condition is parametrized by
`(y + zw, z - yw, 2x - xw)`. -/
theorem parity_condition_parametrized (a b c : ℤ) :
    PaperParityCondition a b c ↔
      ∃ x y z w : ℤ,
        a = y + z * w ∧
        b = z - y * w ∧
        c = (2 : ℤ) * x - x * w := by
  constructor
  · intro h
    rcases h with hc | hab
    · rcases hc with ⟨x, hx⟩
      refine ⟨x, a, b, 0, ?_, ?_, ?_⟩
      · ring
      · ring
      · rw [hx]
        ring
    · rcases hab with ⟨t, ht⟩
      refine ⟨c, t, b + t, 1, ?_, ?_, ?_⟩
      · nlinarith
      · ring
      · ring
  · rintro ⟨x, y, z, w, ha, hb, hc⟩
    rcases Int.even_or_odd w with hw | hw
    · left
      rw [hc]
      have h2mw : Even ((2 : ℤ) - w) := by
        exact Int.even_sub.mpr (by simp [hw])
      have hmul : Even (x * ((2 : ℤ) - w)) := Int.even_mul.mpr (Or.inr h2mw)
      convert hmul using 1
      ring
    · right
      rcases hw with ⟨k, hk⟩
      rw [ha, hb, hk]
      use (k + 1) * y + k * z
      ring

/-- Source proof handoff lemma for the positive remark: the restricted positive
parameters are parametrized by `(y + (1+w)z, y, x + (1-w)^2 x)`. -/
theorem positive_T_parameters_parametrized (a b c : ℤ) :
    PositiveTParameters a b c ↔
      ∃ x y z w : ℤ,
        0 < x ∧ 0 < y ∧ 0 < z ∧ 0 ≤ w ∧
        a = y + ((1 : ℤ) + w) * z ∧
        b = y ∧
        c = x + ((1 : ℤ) - w) ^ 2 * x := by
  constructor
  · intro h
    rcases h with ⟨ha, hb, hcpos, hba, hpar⟩
    rcases hpar with hcEven | habEven
    · rcases hcEven with ⟨x, hx⟩
      have hxpos : 0 < x := by
        rw [hx] at hcpos
        nlinarith
      refine ⟨x, b, a - b, 0, hxpos, hb, ?_, by norm_num, ?_, rfl, ?_⟩
      · nlinarith
      · ring
      · rw [hx]
        ring
    · rcases habEven with ⟨z, hz⟩
      have hzpos : 0 < z := by
        have hdiffpos : 0 < a - b := by nlinarith
        rw [hz] at hdiffpos
        nlinarith
      refine ⟨c, b, z, 1, hcpos, hb, hzpos, by norm_num, ?_, rfl, ?_⟩
      · nlinarith [hz]
      · ring
  · rintro ⟨x, y, z, w, hxpos, hypos, hzpos, hw_nonneg, haeq, hbeq, hceq⟩
    have hw1pos : 0 < (1 : ℤ) + w := by nlinarith
    have hprodpos : 0 < ((1 : ℤ) + w) * z := mul_pos hw1pos hzpos
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [haeq]
      nlinarith
    · rw [hbeq]
      exact hypos
    · rw [hceq]
      have hsq_nonneg : 0 ≤ ((1 : ℤ) - w) ^ 2 := sq_nonneg ((1 : ℤ) - w)
      have hmul_nonneg : 0 ≤ ((1 : ℤ) - w) ^ 2 * x :=
        mul_nonneg hsq_nonneg (le_of_lt hxpos)
      nlinarith
    · rw [haeq, hbeq]
      nlinarith
    · dsimp [PaperParityCondition]
      rcases Int.even_or_odd w with hw | hw
      · left
        rcases hw with ⟨k, hk⟩
        rw [hceq, hk]
        use x * (1 - 2 * k + 2 * k ^ 2)
        ring
      · right
        rcases hw with ⟨k, hk⟩
        rw [haeq, hbeq, hk]
        use (k + 1) * z
        ring

/-- Lagrange four-square handoff: every nonnegative integer is a sum of four squares. -/
theorem int_nonneg_iff_four_squares (n : ℤ) :
    0 ≤ n ↔ ∃ a b c d : ℤ, n = a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 := by
  constructor
  · intro hn
    rcases Nat.sum_four_squares n.toNat with ⟨a, b, c, d, hsum⟩
    refine ⟨a, b, c, d, ?_⟩
    have hn' : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn
    rw [← hn']
    exact_mod_cast hsum.symm
  · rintro ⟨a, b, c, d, rfl⟩
    nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg d]

/-- Four-square corollary used by the 16-parameter substitution: every positive integer
is one plus a sum of four squares. -/
theorem int_positive_iff_four_squares_add_one (n : ℤ) :
    0 < n ↔ ∃ a b c d : ℤ, n = a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + 1 := by
  constructor
  · intro hn
    have hn' : 0 ≤ n - 1 := by nlinarith
    rcases (int_nonneg_iff_four_squares (n - 1)).mp hn' with ⟨a, b, c, d, hsum⟩
    refine ⟨a, b, c, d, ?_⟩
    nlinarith
  · rintro ⟨a, b, c, d, rfl⟩
    nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg d]

end LeanPool.PythagoreanPolynomialParametrization
