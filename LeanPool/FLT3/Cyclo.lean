/-
Copyright (c) 2026 Riccardo Brasca and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, Sanyam Gupta, Omar Haddad, David Lowry-Duda, Lorenzo Luccioli
-/

import Mathlib.NumberTheory.NumberField.Cyclotomic.Embeddings
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Three
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem

/-!
# Cyclotomic preliminaries for Fermat's Last Theorem, exponent `3`

This file develops the basic arithmetic of the sixth root of unity `η` and the
prime `λ = ζ - 1` in the ring of integers of a number field `K` with
`IsCyclotomicExtension {3} ℚ K`, as needed for the descent proof of Fermat's
Last Theorem for exponent `3`. All declarations live under the `FLT3` namespace
to avoid clashing with the now-upstreamed Mathlib development in
`Mathlib.NumberTheory.NumberField.Cyclotomic.Three`, from which the proofs are
derived.
-/

open NumberField Units InfinitePlace nonZeroDivisors Polynomial

namespace FLT3

namespace IsCyclotomicExtension.Rat.Three

/- Let `K` be a number field such that `IsCyclotomicExtension {3} ℚ K`. -/
variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {3} ℚ K]

/- Let `ζ` be any primitive `3`-rd root of unity in `K` and `u` be a unit in `(𝓞 K)ˣ`. -/
variable {ζ : K} (hζ : IsPrimitiveRoot ζ 3) (u : (𝓞 K)ˣ)

/- Let `η` be the element in the units of the ring of integers corresponding to `ζ`. -/
local notation3 "η" => (IsPrimitiveRoot.isUnit (hζ.toInteger_isPrimitiveRoot) (by decide)).unit

/- Let `λ` be the element in the ring of integers corresponding to `ζ - 1`. -/
local notation3 "λ" => hζ.toInteger - 1

/-- We have that `λ` does not divide `2`. -/
lemma lambda_not_dvd_two : ¬ λ ∣ 2 := by
  have hζ' : IsPrimitiveRoot ζ (3 ^ 1) := by rwa [pow_one]
  exact hζ'.toInteger_sub_one_not_dvd_two (by decide)

/-- We have that `2` in `𝓞 K ⧸ Ideal.span {λ}` is not `0`. -/
lemma two_ne_zero : (2 : 𝓞 K ⧸ Ideal.span {λ}) ≠ 0 := by
  intro h
  refine lambda_not_dvd_two hζ <| Ideal.mem_span_singleton.1 <| Ideal.Quotient.eq_zero_iff_mem.1 ?_
  rw [map_ofNat]
  exact h

instance : Nontrivial (𝓞 K ⧸ Ideal.span {λ}) := nontrivial_of_ne 2 0 <| two_ne_zero hζ

omit [NumberField K] [IsCyclotomicExtension {3} ℚ K] in
/-- We have that `η ^ 3 = 1`. -/
lemma toInteger_cube_eq_one : η ^ 3 = 1 := by
  ext
  exact hζ.pow_eq_one

omit [NumberField K] [IsCyclotomicExtension {3} ℚ K] in
/-- We have that `η ^ 2 + η + 1 = 0`. -/
lemma toInteger_eval_cyclo : (η : 𝓞 K) ^ 2 + η + 1 = 0 :=
  _root_.IsCyclotomicExtension.Rat.Three.eta_sq_add_eta_add_one hζ

omit [NumberField K] [IsCyclotomicExtension {3} ℚ K] in
/-- We have that `x ^ 3 - 1 = (x - 1) * (x - η) * (x - η ^ 2)`. -/
lemma cube_sub_one (x : 𝓞 K) : x ^ 3 - 1 = (x - 1) * (x - η) * (x - η ^ 2) :=
  _root_.IsCyclotomicExtension.Rat.Three.cube_sub_one_eq_mul hζ x

end IsCyclotomicExtension.Rat.Three

end FLT3
