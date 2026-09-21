/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Order.Lattice.Nat
import LeanPool.ErdosGinzburgZiv.EGZ.MainTheorem

/-!
# Checked proofs of the independent Palomar statements

This module deliberately does not import `Challenge`. The definitions below
are the same independent definitions, and the bridge lemmas identify their
constants with the ones used by the full EGZ proof.
-/

open scoped BigOperators

namespace PalomarEGZ

/-- Every length-`n` sequence in `(ZMod p)^d` has `p` distinct positions
whose vectors sum to zero. Repeated vector values are allowed. -/
def zeroSumProperty (p d n : ℕ) : Prop :=
  ∀ a : Fin n → (Fin d → ZMod p),
    ∃ I : Finset (Fin n), I.card = p ∧ ∑ i ∈ I, a i = 0

/-- A family is `p`-hollow if a nonnegative integer combination of total
weight `p` sums to zero exactly when one member receives all the weight.
At primes this condition forces the family to have no repeated vectors. -/
def isHollow (p : ℕ) {d s : ℕ} (v : Fin s → (Fin d → ZMod p)) : Prop :=
  ∀ α : Fin s → ℕ, (∑ i, α i) = p →
    ((∑ i, α i • v i) = 0 ↔ ∃ i, α i = p)

/-- The Erdős–Ginzburg–Ziv constant: the least length at which every
sequence has a `p`-term zero sum. For prime `p` this defining set is nonempty,
by pigeonhole with the bound `(p-1) * p^d + 1`. -/
noncomputable def egzConstant (p d : ℕ) : ℕ :=
  sInf {n : ℕ | zeroSumProperty p d n}

/-- The maximum size of a `p`-hollow family. For prime `p`, admitted lengths
are nonempty and bounded by `p^d`, so this natural supremum is attained.
Only prime values are used below; Mathlib's total natural supremum also
assigns a value at degenerate moduli where these lengths may be unbounded. -/
noncomputable def hollowConstant (p d : ℕ) : ℕ :=
  sSup {s : ℕ | ∃ v : Fin s → (Fin d → ZMod p), isHollow p v}

/-- Tending to infinity through prime natural numbers. -/
def atTopAlongPrimes : Filter ℕ :=
  Filter.atTop ⊓ Filter.principal {p : ℕ | p.Prime}

theorem egzConstant_eq (p d : ℕ) : egzConstant p d = EGZ.egzConstant p d := by
  apply le_antisymm
  · exact csInf_le ⟨0, fun _ _ ↦ Nat.zero_le _⟩ (EGZ.egzConstant_spec p d)
  · exact le_csInf (EGZ.exists_egzProperty p d) (fun _ h ↦ EGZ.egzConstant_min h)

theorem hollowConstant_eq {p d : ℕ} (hp : p.Prime) :
    hollowConstant p d = EGZ.hollowConstant p d := by
  apply le_antisymm
  · exact csSup_le ⟨0, EGZ.admitsPHollowLength_zero hp.pos⟩
      (fun _ h ↦ EGZ.hollowConstant_max hp h)
  · exact le_csSup ⟨p ^ d, fun _ h ↦ EGZ.AdmitsPHollowLength.le_pow hp h⟩
      (EGZ.hollowConstant_spec hp)

/-- Theorem 1.2: for each fixed positive dimension,
`s((F_p)^d) = p * w((F_p)^d) + o(p)` as `p` tends to infinity through primes. -/
theorem theorem_1_2 (d : ℕ) (hd : 0 < d) :
    (fun p : ℕ ↦ (egzConstant p d : ℝ) - (p : ℝ) * (hollowConstant p d : ℝ))
      =o[atTopAlongPrimes] (fun p : ℕ ↦ (p : ℝ)) := by
  have heq : (fun p : ℕ ↦ (egzConstant p d : ℝ) - (p : ℝ) * (hollowConstant p d : ℝ))
      =ᶠ[atTopAlongPrimes]
        (fun p : ℕ ↦ (EGZ.egzConstant p d : ℝ) - (p : ℝ) * (EGZ.hollowConstant p d : ℝ)) := by
    change ∀ᶠ p in atTopAlongPrimes,
      (egzConstant p d : ℝ) - (p : ℝ) * (hollowConstant p d : ℝ) =
        (EGZ.egzConstant p d : ℝ) - (p : ℝ) * (EGZ.hollowConstant p d : ℝ)
    rw [atTopAlongPrimes, Filter.eventually_inf_principal]
    exact Filter.Eventually.of_forall fun p hp ↦ by rw [egzConstant_eq, hollowConstant_eq hp]
  exact (EGZ.theorem_1_2 d hd).congr' heq.symm Filter.EventuallyEq.rfl

/-- The corresponding upper estimate: for each positive error `ε`, every
sufficiently large prime satisfies `s((F_p)^d) ≤ (w((F_p)^d) + ε) p`. -/
theorem main_upper_bound (d : ℕ) (hd : 0 < d) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ p in atTopAlongPrimes,
      (egzConstant p d : ℝ) ≤ ((hollowConstant p d : ℝ) + ε) * (p : ℝ) := by
  intro ε hε
  have hh := EGZ.main_upper_bound d hd ε hε
  rw [EGZ.atTopAlongPrimes, Filter.eventually_inf_principal] at hh
  rw [atTopAlongPrimes, Filter.eventually_inf_principal]
  filter_upwards [hh] with p hp hprime
  simpa only [egzConstant_eq, hollowConstant_eq hprime] using hp hprime

end PalomarEGZ
