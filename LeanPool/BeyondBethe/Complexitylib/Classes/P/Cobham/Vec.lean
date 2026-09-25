/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Classes.P.Cobham.Defs
public import LeanPool.BeyondBethe.Complexitylib.Classes.P.Defs
public import LeanPool.BeyondBethe.Complexitylib.Encoding.Pairing
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Fixed-arity inputs for Cobham's characterization

`FP` is defined for unary string functions, while Cobham's algebra is inherently
multi-arity. This module gives the public, auditable bridge: `encodeVec` packs a
fixed-arity argument vector into one string, `vectorLength` measures its unencoded
size, and `FPn` asks a unary `FP` function to agree on the encoded vectors.

The nested pairing has an arity-dependent constant overhead. It is injective, and
for every fixed arity its encoded length is linear in `vectorLength`.

## Main definitions and results

- `Cobham.encodeVec` — nested-pairing tuple encoding, head component last
- `Cobham.vectorLength` — sum of the component lengths
- `Cobham.encodeVec_injective` — tuple encoding loses no information
- `Cobham.encodeVec_length_le` — fixed-arity linear length bound
- `Cobham.FPn` — polynomial time on encoded argument vectors
-/


@[expose] public section

namespace Complexity

namespace Cobham

/-- Encode an argument vector as a single bitstring by nested pairing, with the
head component placed in the verbatim suffix:
`encodeVec ![] = []` and `encodeVec (x ::ᵥ v) = pair (encodeVec v) x`. -/
def encodeVec : {n : ℕ} → (Fin n → List Bool) → List Bool
  | 0, _ => []
  | _ + 1, v => pair (encodeVec (Fin.tail v)) (v 0)

@[simp] theorem encodeVec_zero (v : Fin 0 → List Bool) : encodeVec v = [] := rfl

@[simp] theorem encodeVec_succ {n : ℕ} (v : Fin (n + 1) → List Bool) :
    encodeVec v = pair (encodeVec (Fin.tail v)) (v 0) := rfl

/-- The arity-one encoding is the single component placed in the verbatim suffix
of an empty block: `encodeVec ![x] = pair [] x`. -/
theorem encodeVec_one (v : Fin 1 → List Bool) : encodeVec v = pair [] (v 0) := by
  simp [encodeVec]

/-- The sum of the component lengths of a fixed-arity input vector. -/
def vectorLength {n : ℕ} (v : Fin n → List Bool) : ℕ :=
  ∑ i, (v i).length

@[simp] theorem vectorLength_zero (v : Fin 0 → List Bool) : vectorLength v = 0 := by
  simp [vectorLength]

@[simp] theorem vectorLength_succ {n : ℕ} (v : Fin (n + 1) → List Bool) :
    vectorLength v = (v 0).length + vectorLength (Fin.tail v) := by
  rw [vectorLength, Fin.sum_univ_succ, vectorLength]
  rfl

/-- Exact recursive length law for the nested tuple encoding. -/
theorem encodeVec_length_succ {n : ℕ} (v : Fin (n + 1) → List Bool) :
    (encodeVec v).length =
      2 * (encodeVec (Fin.tail v)).length + 2 + (v 0).length := by
  simp [encodeVec_succ]

/-- `encodeVec` is injective at every arity. -/
theorem encodeVec_injective {n : ℕ} : Function.Injective (@encodeVec n) := by
  induction n with
  | zero =>
      intro v w _
      funext i
      exact Fin.elim0 i
  | succ n ih =>
      intro v w h
      rw [encodeVec_succ, encodeVec_succ] at h
      obtain ⟨htail, hhead⟩ := pair_inj h
      have htail' : Fin.tail v = Fin.tail w := ih htail
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact hhead
      · exact congrFun htail' j

/-- For fixed arity `n`, the nested encoding has length linear in the sum of the
component lengths. The explicit coefficient also records that this is not a
uniform-in-arity linear bound. -/
theorem encodeVec_length_le {n : ℕ} (v : Fin n → List Bool) :
    (encodeVec v).length ≤ 2 ^ n * (vectorLength v + 2 * n) := by
  induction n with
  | zero =>
      simp [encodeVec, vectorLength]
  | succ n ih =>
      rw [encodeVec_length_succ, vectorLength_succ]
      have hp : 1 ≤ 2 ^ n := one_le_pow₀ (by omega)
      have h2 := Nat.mul_le_mul_left 2 (ih (Fin.tail v))
      calc
        2 * (encodeVec (Fin.tail v)).length + 2 + (v 0).length
            ≤ 2 * (2 ^ n * (vectorLength (Fin.tail v) + 2 * n)) +
                2 + (v 0).length := by omega
        _ ≤ 2 ^ (n + 1) *
              ((v 0).length + vectorLength (Fin.tail v) + 2 * (n + 1)) := by
            rw [pow_succ]
            nlinarith

/-- **Multi-arity polynomial time.** A function of an argument vector is `FPn`
when some genuine unary `FP` function computes it on encoded vectors. -/
def FPn {n : ℕ} (f : (Fin n → List Bool) → List Bool) : Prop :=
  ∃ g, g ∈ FP ∧ ∀ v, g (encodeVec v) = f v

end Cobham

end Complexity
