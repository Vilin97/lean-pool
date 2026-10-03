/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JD Jones
-/
module

public import LeanPool.NaslundCounterexample.Families
public import LeanPool.NaslundCounterexample.Asymptotics

/-!
# Counterexamples to Naslund's Conjecture 13

The conjecture is from Eric Naslund, *Paley graphs and Sárközy's theorem in function
fields*, Quarterly Journal of Mathematics 74 (2023), 627–637, Conjecture 13
(https://arxiv.org/abs/2203.01293v3). This project refutes its square-difference case
over F_3; it does not assert a counterexample over other finite fields.

The upstream source was written by Claude under JD Jones's direction, with Claude,
GPT-6 and Grok consulted for the construction and proofs. Lean Pool adaptations
rename declarations, narrow imports and optimize proofs; the statements are unchanged.

The two polynomial families give the existence statements once their internal degree
bound is converted to the public one. The two refutations compare their sizes with the
conjectured bound `3^{3n/4}`: for `n = 8e` this is `3^{6e} = 729^e < 810^e`, and for `n = 8e + 4`
it is `3^{6e+3} = 27 · 729^e < 27 · 810^e`. The growth rate is the theorem of
`NaslundCounterexample.Asymptotics`.

The statements below are proved from the explicit polynomial families.
-/

public section

namespace NaslundCounterexample

open Polynomial

/-- **A square-difference-free subset of `P_{3,8}` with `810` elements**, the first lift of the
one-element base. -/
theorem exists_card_810 :
    ∃ A : Finset (Polynomial (ZMod 3)),
      DegreeBelow 8 A ∧ A.card = 810 ∧ SquareDifferenceFree A := by
  refine ⟨familyFromZero 1, ?_, ?_, familyFromZero_sdf 1⟩
  · have h : AllBelow 8 (familyFromZero 1) := by simpa using familyFromZero_allBelow 1
    exact (allBelow_iff_degreeBelow 8 (familyFromZero 1) (by norm_num)).mp h
  · simpa using familyFromZero_card 1

/-- **The conjectured bound fails at `q = 3`, `k = 2`, `n = 8`:** not every square-difference-free
subset of `P_{3,8}` has at most `3^6 = 729` elements, since `810 > 729`. -/
theorem conjecture_fails_at_eight :
    ¬ ∀ A : Finset (Polynomial (ZMod 3)),
      DegreeBelow 8 A → SquareDifferenceFree A → A.card ≤ 3 ^ 6 := by
  intro h
  obtain ⟨A, hA, hcard, hS⟩ := exists_card_810
  have hle := h A hA hS
  rw [hcard] at hle
  norm_num at hle

/-- **The first family.** For every `e ≥ 1`, a square-difference-free subset of `P_{3,8e}` with
`810^e` elements. -/
theorem exists_card_pow (e : ℕ) (he : 1 ≤ e) :
    ∃ A : Finset (Polynomial (ZMod 3)), DegreeBelow (8 * e) A ∧ A.card = 810 ^ e ∧
        SquareDifferenceFree A :=
  ⟨familyFromZero e, (allBelow_iff_degreeBelow (8 * e) (familyFromZero e) (by omega)).mp
      (familyFromZero_allBelow e),
    familyFromZero_card e, familyFromZero_sdf e⟩

/-- **The second family.** For every `e`, a square-difference-free subset of `P_{3,8e+4}` with
`27 · 810^e` elements. -/
theorem exists_card_twenty_seven_mul_pow (e : ℕ) :
    ∃ A : Finset (Polynomial (ZMod 3)), DegreeBelow (8 * e + 4) A ∧ A.card = 27 * 810 ^ e ∧
        SquareDifferenceFree A :=
  ⟨familyFromFour e, (allBelow_iff_degreeBelow (8 * e + 4) (familyFromFour e) (by omega)).mp
      (familyFromFour_allBelow e),
    familyFromFour_card e, familyFromFour_sdf e⟩

/-- **The conjectured bound fails for every admissible `n ≥ 8`:** for `4 ∣ n` and `n ≥ 8`, not
every square-difference-free subset of `P_{3,n}` has at most `3^{3n/4}` elements. Such an `n` is
`8e` or `8e + 4` with `e ≥ 1`, and the corresponding family exceeds the bound by `(10/9)^e`. -/
theorem conjecture_fails (n : ℕ) (h4 : 4 ∣ n) (h8 : 8 ≤ n) :
    ¬ ∀ A : Finset (Polynomial (ZMod 3)),
      DegreeBelow n A → SquareDifferenceFree A → A.card ≤ 3 ^ (3 * n / 4) := by
  intro h
  obtain ⟨k, rfl⟩ := h4
  rcases Nat.even_or_odd k with hk | hk
  · -- `n = 8e` with `e ≥ 1`: the first family has `810^e` elements against the bound `729^e`.
    obtain ⟨e, he⟩ := hk
    have he1 : 1 ≤ e := by omega
    obtain ⟨A, hA, hcard, hS⟩ := exists_card_pow e he1
    have hn : 4 * k = 8 * e := by omega
    rw [hn] at h
    have hb : 3 * (8 * e) / 4 = 6 * e := by omega
    rw [hb] at h
    have hle := h A hA hS
    have key : (3 : ℕ) ^ (6 * e) = 729 ^ e := by rw [pow_mul]; norm_num
    rw [hcard, key] at hle
    have hlt : (729 : ℕ) ^ e < 810 ^ e := Nat.pow_lt_pow_left (by norm_num) (by omega)
    omega
  · -- `n = 8e + 4` with `e ≥ 1`: the second family has `27 · 810^e` against `27 · 729^e`.
    obtain ⟨e, he⟩ := hk
    have he1 : 1 ≤ e := by omega
    obtain ⟨A, hA, hcard, hS⟩ := exists_card_twenty_seven_mul_pow e
    have hn : 4 * k = 8 * e + 4 := by omega
    rw [hn] at h
    have hb : 3 * (8 * e + 4) / 4 = 6 * e + 3 := by omega
    rw [hb] at h
    have hle := h A hA hS
    have key : (3 : ℕ) ^ (6 * e + 3) = 729 ^ e * 27 := by rw [pow_add, pow_mul]; norm_num
    rw [hcard, key] at hle
    have hlt : (729 : ℕ) ^ e < 810 ^ e := Nat.pow_lt_pow_left (by norm_num) (by omega)
    omega

end NaslundCounterexample
