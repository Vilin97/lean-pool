/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JD Jones
-/
module

public import LeanPool.NaslundCounterexample.Below
public import LeanPool.NaslundCounterexample.Code

/-!
# The two bases

The recursion needs a starting set at each residue of `n` modulo `8` that the construction
reaches. `B_0 = {0}` is the trivial square-difference-free subset of `P_{3,0}`, and

`B_4 = { a T^3 + b T + c (1 - T^2) : a, b, c ∈ F_3 }`

is a square-difference-free subset of `P_{3,4}` with `27` elements. Square-difference-freeness of
`B_4` is the only place where the shape `1 - T^2` matters: a difference of two of its elements
has constant term `c` and `T^2`-coefficient `-c`, while a nonzero square of degree below `4` is
the square of a linear polynomial `v + u T`, with constant term `v^2` and `T^2`-coefficient
`u^2`; so `v^2 + u^2 = 0`, which in `F_3` forces `u = v = 0`.
-/

public section

namespace NaslundCounterexample

open Polynomial

/-- The base `B_0 = {0} ⊆ P_{3,0}`. -/
noncomputable def base0 : Finset (ZMod 3)[X] := {0}

/-- `B_0` has one element. -/
theorem base0_card : base0.card = 1 := Finset.card_singleton 0

/-- `B_0` lies in `P_{3,0}`. -/
theorem base0_allBelow : AllBelow 0 base0 := by
  intro f hf
  rw [base0, Finset.mem_singleton] at hf
  subst hf
  exact below_zero 0

/-- `B_0` is square-difference-free. -/
theorem base0_sdf : SquareDifferenceFree base0 := by
  intro f hf g hg z hz
  rw [base0, Finset.mem_singleton] at hf hg
  subst hf; subst hg
  simpa using hz.symm

/-- One element of `B_4`, the polynomial `a T^3 + b T + c (1 - T^2)`. -/
noncomputable def base4Map (t : ZMod 3 × ZMod 3 × ZMod 3) : (ZMod 3)[X] :=
  C t.1 * X ^ 3 + C t.2.1 * X + C t.2.2 * (1 - X ^ 2)

/-- The base `B_4 = { a T^3 + b T + c (1 - T^2) : a, b, c ∈ F_3 } ⊆ P_{3,4}`. -/
noncomputable def base4 : Finset (ZMod 3)[X] :=
  open scoped Classical in Finset.univ.image base4Map

/-- Distinct triples give distinct elements of `B_4`: the coefficients at `T^3`, `T` and `1` read
`a`, `b` and `c` back. -/
theorem base4Map_injective : Function.Injective base4Map := by
  intro t t' h
  have h3 := congrArg (fun f => Polynomial.coeff f 3) h
  have h1 := congrArg (fun f => Polynomial.coeff f 1) h
  have h0 := congrArg (fun f => Polynomial.coeff f 0) h
  simp only [base4Map, mul_sub, mul_one, coeff_add, coeff_sub, coeff_C_mul, coeff_X_pow,
    coeff_C, coeff_X] at h3 h1 h0
  norm_num at h3 h1 h0
  exact Prod.ext h3 (Prod.ext h1 h0)

/-- `B_4` has `27` elements. -/
theorem base4_card : base4.card = 27 := by
  classical
  rw [base4, Finset.card_image_of_injective _ base4Map_injective, Finset.card_univ]
  simp [ZMod.card]

/-- `B_4` lies in `P_{3,4}`. -/
theorem base4_allBelow : AllBelow 4 base4 := by
  classical
  intro f hf
  rw [base4, Finset.mem_image] at hf
  obtain ⟨t, -, rfl⟩ := hf
  refine below_of_degree_le (m := 3) ?_
  unfold base4Map
  compute_degree
  norm_num

/-- **`B_4` is square-difference-free.** A difference of two of its elements has constant term `c`
and `T^2`-coefficient `-c`; a nonzero square of degree below `4` is the square of a linear
polynomial `v + u T`, whose constant term is `v^2` and whose `T^2`-coefficient is `u^2`; so
`v^2 + u^2 = 0`, and in `F_3` that forces `u = v = 0`. -/
theorem base4_sdf : SquareDifferenceFree base4 := by
  classical
  intro f hf g hg z hz
  -- A difference of two elements of `B_4` has degree below `4`, so the square `z^2` does too,
  -- and `natDegree (z^2) = 2 · natDegree z` makes `z` linear.
  have hd : Below 4 (g - f) := (base4_allBelow g hg).sub (base4_allBelow f hf)
  have hz1 : z.natDegree ≤ 1 := by
    have h3 : (g - f).natDegree ≤ 3 := Below.natDegree_le (m := 3) hd
    rw [hz, Polynomial.natDegree_pow] at h3
    omega
  -- The two coefficients of a square of a linear polynomial: `v^2` at `1` and `u^2` at `T^2`.
  have e0 : (z ^ 2).coeff 0 = z.coeff 0 ^ 2 := by
    rw [sq, Polynomial.mul_coeff_zero, ← sq]
  have e2 : (z ^ 2).coeff 2 = z.coeff 1 ^ 2 := by
    simpa using Polynomial.coeff_pow_of_natDegree_le (p := z) (n := 1) (m := 2) hz1
  -- The same two coefficients of the difference: `c` and `-c`.
  rw [base4, Finset.mem_image] at hf hg
  obtain ⟨t, -, rfl⟩ := hf
  obtain ⟨t', -, rfl⟩ := hg
  have d0 : (base4Map t' - base4Map t).coeff 0 = t'.2.2 - t.2.2 := by
    simp [base4Map, Polynomial.coeff_X_pow, mul_sub]
  have d2 : (base4Map t' - base4Map t).coeff 2 = -(t'.2.2 - t.2.2) := by
    simp only [base4Map, mul_sub, mul_one, Polynomial.coeff_sub, Polynomial.coeff_add,
      Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C]
    norm_num
    ring
  -- Hence `v^2 + u^2 = c + (-c) = 0`, which in `F_3` forces `u = v = 0`.
  have h0 : z.coeff 0 ^ 2 = t'.2.2 - t.2.2 := by rw [← e0, ← hz, d0]
  have h2 : z.coeff 1 ^ 2 = -(t'.2.2 - t.2.2) := by rw [← e2, ← hz, d2]
  obtain ⟨hu, hv⟩ := eq_zero_of_sq_add_sq (z.coeff 1) (z.coeff 0) (by rw [h0, h2]; ring)
  rw [Polynomial.eq_X_add_C_of_natDegree_le_one hz1, hu, hv]
  simp

end NaslundCounterexample
