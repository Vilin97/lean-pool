/-
Copyright (c) 2026 Jue Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jue Xu
-/

module

public import LeanPool.LowWeightPauliDynamics.Pauli.Matrix
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Traces of Pauli operators, and orthogonality of the Pauli family

This file computes the trace of every Pauli operator `toMatrix u` and, from it, the trace
pairing `Tr((toMatrix s)ᴴ * toMatrix t)` of any two. The result is the orthogonality relation
`Tr(s s') = δ_{s,s'}` that `def:pauli_basis` attaches to the normalized `n`-qubit Pauli basis.
The paper uses that relation in two places: for the normalization of the Pauli 2-norm (the norm
entering `apd:eq:def_high_weight_norm`), and in the proof of `apd:thm:local_flow_k_local`, where
the traces `Tr(P O^{(g)})` are the coordinates of an orthonormal expansion — which is what makes
conjugation act as an *orthogonal* matrix on coefficient vectors.

## Main results

* `char_sum`: `∑_b (-1)^{u ⬝ᵥ b} = 2^n` if `u = 0` and `0` otherwise.
* `trace_toMatrix_of_x_ne_zero`, `trace_toMatrix_of_x_eq_zero`: the trace of a Pauli operator.
* `trace_star_toMatrix_mul`: the trace pairing of two Pauli operators, with its two special
  cases `trace_star_toMatrix_mul_eq_zero` (orthogonality) and `trace_star_toMatrix_mul_self`
  (squared Hilbert–Schmidt norm `2^n`).
* `trace_star_toMatrix_mul_phaseMul`: phase variants of one string are *not* orthogonal.

## The shape of the statement, and the trap in it

`Pauli/Matrix.lean` represents the whole phase-extended group, `4·4^n` elements. That family is
**not** orthogonal and cannot be: `toMatrix (phaseMul 1 s) = i · toMatrix s`, so a string and its
phase multiples are collinear. What is true, and what this file proves, is that the trace pairing
sees exactly the `(x, z)` data:

  `Tr((toMatrix s)ᴴ * toMatrix t) = 0`   unless `s.x = t.x` and `s.z = t.z`,

with the value `2^n · i^{phase}` when they do agree. So the orthogonal family is the `4^n` *signless
classes*, and a statement of orthogonality over `PauliString n` itself would be false. Anything
downstream that wants an orthonormal basis has to choose a phase normalization first:
`Pauli/Coeff.lean` chooses the self-adjoint representative `herm`, and `Pauli/Tensor.lean` the
positive tensor-product representative `tensorRepresentative`.

## How it is proved

Everything reduces to one character sum. The diagonal of `toMatrix u` is empty unless `u.x = 0`,
because the entry at `(a, a)` is non-zero only where `a = a + u.x`; so

  `Tr (toMatrix u) = 0`                                        if `u.x ≠ 0`,
  `Tr (toMatrix u) = i^{u.phase} · ∑_b (-1)^{u.z ⬝ᵥ b}`        if `u.x = 0`,

and the sum is `2^n` at `u.z = 0` and `0` otherwise. The pairing statement then follows from
`toMatrix_star` and `toMatrix_mul`, since `(star s * t).x = s.x + t.x` in characteristic two.
-/

@[expose] public section

namespace Lean4LPD

namespace PauliString

variable {n : ℕ} {s t u : PauliString n}

/-! ### The character sum

`∑_{b ∈ {0,1}^n} (-1)^{u ⬝ᵥ b}` is the orthogonality relation for the additive characters of
`(ZMod 2)^n`, and the engine of everything below.

There are two natural proofs. The one used here factorizes the sign over sites and swaps the sum
with the product; the alternative pairs `b` with `b + eᵢ` at a site where `u` is on and cancels
signs, via `Finset.sum_ninvolution`. The factorized proof is preferred because it is shorter,
because it proves both branches from one identity rather than arguing `u = 0` separately, and
because `negOnePow_sum` and `negOnePow_dotProduct` are reusable on their own. -/

/-- Sum over the two elements of `ZMod 2`. `Fin.sum_univ_two` does not apply directly: the
`Fintype (ZMod 2)` instance is `ZMod.fintype 2`, defeq but not syntactically equal to
`Fin.fintype 2`, so `rw` reports "not type-correct under `implicit` transparency". -/
private lemma sum_zmod_two (f : ZMod 2 → ℂ) : ∑ c : ZMod 2, f c = f 0 + f 1 := by
  rw [show (Finset.univ : Finset (ZMod 2)) = {0, 1} from by decide,
    Finset.sum_insert (by decide), Finset.sum_singleton]

private lemma zmod_two_cases' (a : ZMod 2) : a = 0 ∨ a = 1 := by revert a; decide

/-- **`negOnePow` is multiplicative over finite sums**: `(-1)^{∑ f i} = ∏ (-1)^{f i}`. -/
lemma negOnePow_sum {ι : Type*} (s : Finset ι) (f : ι → ZMod 2) :
    negOnePow (∑ i ∈ s, f i) = ∏ i ∈ s, negOnePow (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, negOnePow_add, ih]

/-- The sign of a dot product **factorizes over sites**. -/
lemma negOnePow_dotProduct (u b : Bits n) :
    negOnePow (u ⬝ᵥ b) = ∏ i, negOnePow (u i * b i) := by
  simp only [dotProduct]
  exact negOnePow_sum _ _

/-- One site's contribution: `2` at `a = 0` and `0` at `a = 1`. This vanishing is the whole
content of the character sum. -/
lemma sum_negOnePow_mul (a : ZMod 2) :
    (∑ c : ZMod 2, negOnePow (a * c)) = if a = 0 then (2 : ℂ) else 0 := by
  rw [sum_zmod_two]
  rcases zmod_two_cases' a with ha | ha <;> rw [ha] <;> norm_num

/-- **The Pauli character sum**: `2^n` at the trivial character, `0` otherwise. -/
theorem char_sum (n : ℕ) (u : Bits n) :
    (∑ b : Bits n, negOnePow (u ⬝ᵥ b)) = if u = 0 then (2 : ℂ) ^ n else 0 := by
  rw [Finset.sum_congr rfl fun b _ => negOnePow_dotProduct u b,
    ← Fintype.prod_sum fun (i : Fin n) (c : ZMod 2) => negOnePow (u i * c),
    Finset.prod_congr rfl fun i _ => sum_negOnePow_mul (u i)]
  by_cases hu : u = 0
  · subst hu; simp
  · rw [ite_eq_right hu]
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hu
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

/-- A guard against a vacuous reading: both branches fire. -/
example : (∑ b : Bits 2, negOnePow ((0 : Bits 2) ⬝ᵥ b)) = 4 := by
  rw [char_sum, ite_eq_left (rfl : (0 : Bits 2) = 0)]; norm_num

example : (∑ b : Bits 1, negOnePow ((1 : Bits 1) ⬝ᵥ b)) = 0 := by
  rw [char_sum, ite_eq_right (by decide : ¬ ((1 : Bits 1) = 0))]

/-! ### The diagonal -/

/-- In characteristic two a shift fixes a basis label only when it is trivial, so `toMatrix u` has
a non-empty diagonal exactly when its `X`-part vanishes. -/
lemma diag_ne_zero_iff (u : PauliString n) (a : Bits n) :
    a = a + u.x ↔ u.x = 0 := by
  constructor
  · intro h
    have h' : a + 0 = a + u.x := by rwa [add_zero]
    exact (add_left_cancel h').symm
  · intro h; rw [h, add_zero]

lemma toMatrix_diag_of_x_ne_zero (hu : u.x ≠ 0) (a : Bits n) : toMatrix u a a = 0 := by
  rw [toMatrix_apply, ite_eq_right]
  intro h
  exact hu ((diag_ne_zero_iff u a).1 h)

lemma toMatrix_diag_of_x_eq_zero (hu : u.x = 0) (a : Bits n) :
    toMatrix u a a = iPow u.phase * negOnePow (u.z ⬝ᵥ a) := by
  rw [toMatrix_apply, ite_eq_left ((diag_ne_zero_iff u a).2 hu)]

/-! ### The trace -/

/-- A Pauli operator with a non-trivial `X`-part is traceless: it is a permutation matrix pattern
with no fixed points. -/
theorem trace_toMatrix_of_x_ne_zero (hu : u.x ≠ 0) : (toMatrix u).trace = 0 := by
  rw [Matrix.trace]
  exact Finset.sum_eq_zero fun a _ => toMatrix_diag_of_x_ne_zero hu a

/-- With a trivial `X`-part the trace is the phase times a character sum over the `Z`-part. -/
theorem trace_toMatrix_of_x_eq_zero (hu : u.x = 0) :
    (toMatrix u).trace = iPow u.phase * ∑ b : Bits n, negOnePow (u.z ⬝ᵥ b) := by
  rw [Matrix.trace, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by
    rw [Matrix.diag_apply, toMatrix_diag_of_x_eq_zero hu a]

/-! ### Orthogonality

The trace pairing sees the `(x, z)` data and nothing else. This is the relation
`Tr(s s') = δ_{s,s'}` of `def:pauli_basis`, stated for the phase-extended group rather than for a
normalized basis — which is the form that holds for `PauliString n`, since the group itself is
not an orthogonal family. -/

lemma star_mul_x (s t : PauliString n) : (star s * t).x = s.x + t.x := rfl

lemma star_mul_z (s t : PauliString n) : (star s * t).z = s.z + t.z := rfl

/-- **The trace pairing of two Pauli operators.** Zero unless the two strings carry the same
`X`- and `Z`-parts; `2^n` times a fourth root of unity when they do. -/
theorem trace_star_toMatrix_mul (s t : PauliString n) :
    (star (toMatrix s) * toMatrix t).trace
      = if s.x = t.x ∧ s.z = t.z then (2 : ℂ) ^ n * iPow (star s * t).phase else 0 := by
  rw [toMatrix_star, toMatrix_mul]
  by_cases hx : s.x = t.x
  · have hx0 : (star s * t).x = 0 := by
      rw [star_mul_x]; exact bits_add_eq_zero_iff.2 hx
    rw [trace_toMatrix_of_x_eq_zero hx0, char_sum, star_mul_z]
    by_cases hz : s.z = t.z
    · rw [ite_eq_left (bits_add_eq_zero_iff.2 hz), ite_eq_left ⟨hx, hz⟩]
      ring
    · rw [ite_eq_right (fun h => hz (bits_add_eq_zero_iff.1 h)),
        ite_eq_right (fun h => hz h.2)]
      ring
  · have hx0 : (star s * t).x ≠ 0 := fun h => hx (bits_add_eq_zero_iff.1 (by rwa [star_mul_x] at h))
    rw [trace_toMatrix_of_x_ne_zero hx0, ite_eq_right (fun h => hx h.1)]

/-- Two Pauli strings differing in their `X`- or `Z`-part are **orthogonal** operators. -/
theorem trace_star_toMatrix_mul_eq_zero (h : ¬(s.x = t.x ∧ s.z = t.z)) :
    (star (toMatrix s) * toMatrix t).trace = 0 := by
  rw [trace_star_toMatrix_mul, ite_eq_right h]

/-- Every Pauli operator has squared Hilbert–Schmidt norm `2^n`. With the `2^{-n/2}` normalization
of `def:pauli_basis` this is the diagonal case `Tr(s s) = 1` of its orthonormality relation. -/
theorem trace_star_toMatrix_mul_self (s : PauliString n) :
    (star (toMatrix s) * toMatrix s).trace = (2 : ℂ) ^ n := by
  rw [toMatrix_star, toMatrix_mul, star_eq_inv, inv_mul_cancel, toMatrix_one, Matrix.trace_one,
    card_bits]
  push_cast
  ring

/-- **Phase variants are not orthogonal**, and this records why the orthogonal family is the `4^n`
signless classes rather than the `4·4^n` group elements: `i·s` pairs with `s` to give `2^n · i`,
not `0`. Anything that wants an orthonormal basis must normalize the phase first. -/
theorem trace_star_toMatrix_mul_phaseMul (k : ZMod 4) (s : PauliString n) :
    (star (toMatrix s) * toMatrix (phaseMul k s)).trace = (2 : ℂ) ^ n * iPow k := by
  have hp : (star s * phaseMul k s).phase = k := by
    have h : (star s * phaseMul k s).phase
        = (-s.phase + signPhase (s.z ⬝ᵥ s.x)) + (s.phase + k)
          + signPhase (s.z ⬝ᵥ s.x) := rfl
    rw [h, show (-s.phase + signPhase (s.z ⬝ᵥ s.x)) + (s.phase + k) + signPhase (s.z ⬝ᵥ s.x)
        = k + (signPhase (s.z ⬝ᵥ s.x) + signPhase (s.z ⬝ᵥ s.x)) by ring,
      signPhase_add_self, add_zero]
  rw [trace_star_toMatrix_mul, ite_eq_left ⟨rfl, rfl⟩, hp]

end PauliString

end Lean4LPD
