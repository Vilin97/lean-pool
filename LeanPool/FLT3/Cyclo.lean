/-
Copyright (c) 2026 Riccardo Brasca, Sanyam Gupta, Omar Haddad, David Lowry-Duda, Lorenzo Luccioli, Pietro Monticone, Alexis Saurin, Florent Schaffhauser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, Sanyam Gupta, Omar Haddad, David Lowry-Duda, Lorenzo Luccioli, Pietro Monticone, Alexis Saurin, Florent Schaffhauser
-/

import Mathlib.NumberTheory.Cyclotomic.Embeddings
import Mathlib.NumberTheory.Cyclotomic.Rat
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem

open NumberField Units InfinitePlace nonZeroDivisors Polynomial

namespace IsCyclotomicExtension.Rat.Three

/- Let `K` be a number field such that `IsCyclotomicExtension {3} ℚ K`. -/
variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {3} ℚ K]

/- Let `ζ` be any primitive `3`-rd root of unity in `K` and `u` be a unit in `(𝓞 K)ˣ`. -/
variable {ζ : K} (hζ : IsPrimitiveRoot ζ ↑(3 : ℕ+)) (u : (𝓞 K)ˣ)

/- Let `η` be the element in the units of the ring of integers corresponding to `ζ`. -/
local notation3 "η" => (IsPrimitiveRoot.isUnit (hζ.toInteger_isPrimitiveRoot) (by decide)).unit

/- Let `λ` be the element in the ring of integers corresponding to `ζ - 1`. -/
local notation3 "λ" => hζ.toInteger - 1

/-- We have that `2` in `𝓞 K ⧸ Ideal.span {λ}` is not `0`. -/
lemma two_ne_zero : (2 : 𝓞 K ⧸ Ideal.span {λ}) ≠ 0 := by
  suffices 2 ∉ Ideal.span {hζ.toInteger - 1} by
    intro h
    refine this (Ideal.Quotient.eq_zero_iff_mem.1 <| by simp [h])
  intro h
  rw [Ideal.mem_span_singleton] at h
  replace h : hζ.toInteger - 1 ∣ ↑(2 : ℤ) := by simp [h]
  rw [← Ideal.norm_dvd_iff, hζ.norm_toInteger_sub_one_of_prime_ne_two' (by decide)] at h
  · norm_num at h
  · rw [hζ.norm_toInteger_sub_one_of_prime_ne_two' (by decide)]
    exact Int.prime_three

/-- We have that `λ` does not divide `2`. -/
lemma lambda_not_dvd_two : ¬ λ ∣ 2 :=
  fun h ↦ two_ne_zero hζ <| Ideal.Quotient.eq_zero_iff_mem.2 <| Ideal.mem_span_singleton.2 h

instance : Nontrivial (𝓞 K ⧸ Ideal.span {λ}) := nontrivial_of_ne 2 0 <| two_ne_zero hζ

open Classical Finset in

/-- We have that `η ^ 3 = 1`. -/
lemma _root_.IsPrimitiveRoot.toInteger_cube_eq_one : η ^ 3 = 1 := by
  ext
  exact hζ.pow_eq_one

/-- We have that `η ^ 2 + η + 1 = 0`. -/
lemma _root_.IsPrimitiveRoot.toInteger_eval_cyclo : (η : 𝓞 K) ^ 2 + η + 1 = 0 := by
  ext; simpa using hζ.isRoot_cyclotomic (by decide)

/-- We have that `x ^ 3 - 1 = (x - 1) * (x - η) * (x - η ^ 2)`. -/
lemma cube_sub_one (x : 𝓞 K) : x ^ 3 - 1 = (x - 1) * (x - η) * (x - η ^ 2) := by
  symm
  calc _ = x ^ 3 - x ^ 2 * (η ^ 2 + η + 1) + x * (η ^ 2 + η + η ^ 3) - η ^ 3 := by ring
  _ = x ^ 3 - x ^ 2 * (η ^ 2 + η + 1) + x * (η ^ 2 + η + 1) - 1 := by
    norm_cast
    simp [hζ.toInteger_cube_eq_one]
  _ = x ^ 3 - 1 := by rw [hζ.toInteger_eval_cyclo]; ring

end IsCyclotomicExtension.Rat.Three
