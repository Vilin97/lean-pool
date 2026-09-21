/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import Mathlib.Combinatorics.Additive.ErdosGinzburgZiv
import Lean.Elab.Tactic.Omega

open scoped BigOperators

namespace PrimeEGZ

/-!
This completed file is a regression example, not the paper's Theorem 1.2.
It proves the classical one-dimensional Erdős--Ginzburg--Ziv theorem already
supported by Mathlib.
-/

/-- A sequence `a` contains `p` terms, at distinct positions, whose sum is
zero in `ZMod p`. -/
def HasZeroSumSubsequence {ι : Type} (p : ℕ) (a : ι → ZMod p) : Prop :=
  ∃ t : Finset ι, t.card = p ∧ ∑ i ∈ t, a i = 0

/-- Every sequence of length at least `N` in `ZMod p` contains a zero-sum
subsequence of length `p`.

The index type is allowed to be an arbitrary finite type; this avoids making
the definition depend on a particular enumeration of the sequence. -/
def ForcesZeroSum (p N : ℕ) : Prop :=
  ∀ {ι : Type} [Fintype ι] (a : ι → ZMod p),
    N ≤ Fintype.card ι → HasZeroSumSubsequence p a

theorem ForcesZeroSum.mono {p N M : ℕ} (h : ForcesZeroSum p N) (hNM : N ≤ M) :
    ForcesZeroSum p M := by
  intro ι _ a hM
  exact h a (hNM.trans hM)

/-- The upper bound in the Erdős--Ginzburg--Ziv theorem.

Mathlib contains the stronger theorem `ZMod.erdos_ginzburg_ziv`, valid for
every modulus, not only a prime modulus. -/
theorem forcesZeroSum_two_mul_sub_one (p : ℕ) :
    ForcesZeroSum p (2 * p - 1) := by
  classical
  intro ι _ a hcard
  obtain ⟨t, _htuniv, htcard, htsum⟩ :=
    ZMod.erdos_ginzburg_ziv (s := (Finset.univ : Finset ι)) a
      (by simpa using hcard)
  exact ⟨t, htcard, htsum⟩

theorem exists_forcing_length (p : ℕ) : ∃ N, ForcesZeroSum p N :=
  ⟨2 * p - 1, forcesZeroSum_two_mul_sub_one p⟩

/-- The Erdős--Ginzburg--Ziv constant of `ZMod p`: the least length which
forces a zero-sum subsequence of length `p`. -/
noncomputable def sFp (p : ℕ) : ℕ := by
  classical
  exact Nat.find (exists_forcing_length p)

theorem sFp_spec (p : ℕ) : ForcesZeroSum p (sFp p) := by
  classical
  exact Nat.find_spec (exists_forcing_length p)

theorem sFp_min {p N : ℕ} (hN : ForcesZeroSum p N) : sFp p ≤ N := by
  classical
  exact Nat.find_min' (exists_forcing_length p) hN

/-- The usual sharpness example: `p - 1` zeroes and `p - 1` ones do not
contain a zero-sum subsequence of length `p`.

The positions are represented by `Fin (p - 1) × Bool`; the Boolean coordinate
records whether the term is zero or one. -/
theorem not_forcesZeroSum_two_mul_sub_two {p : ℕ} (hp : 2 ≤ p) :
    ¬ForcesZeroSum p (2 * p - 2) := by
  classical
  intro h

  let ι := Fin (p - 1) × Bool
  let a : ι → ZMod p := fun x => if x.2 = true then 1 else 0

  have hcard : 2 * p - 2 ≤ Fintype.card ι := by
    simp [ι]
    omega

  obtain ⟨t, htcard, htsum⟩ := h a hcard

  let rightTerms : Finset ι := t.filter fun x => x.2 = true
  have hrightCast : (rightTerms.card : ZMod p) = 0 := by
    simpa [a, rightTerms, Finset.sum_ite] using htsum
  have hp_dvd_right : p ∣ rightTerms.card :=
    (ZMod.natCast_eq_zero_iff rightTerms.card p).mp hrightCast

  let rightSide : Finset ι :=
    (Finset.univ : Finset (Fin (p - 1))).product {true}
  have hright_sub : rightTerms ⊆ rightSide := by
    intro x hx
    have hx' : x ∈ t ∧ x.2 = true := by
      simpa [rightTerms] using hx
    rcases x with ⟨x, b⟩
    have hb : b = true := by simpa using hx'.2
    cases hb
    exact Finset.mem_product.mpr ⟨Finset.mem_univ x, Finset.mem_singleton_self true⟩
  have hright_le : rightTerms.card ≤ p - 1 := by
    calc
      rightTerms.card ≤ rightSide.card := Finset.card_le_card hright_sub
      _ = p - 1 := by simp [rightSide]
  have hright_lt : rightTerms.card < p := by omega
  have hright_zero : rightTerms.card = 0 := by
    have hmod : rightTerms.card % p = 0 :=
      Nat.mod_eq_zero_of_dvd hp_dvd_right
    rw [Nat.mod_eq_of_lt hright_lt] at hmod
    exact hmod
  have hright_empty : rightTerms = ∅ :=
    Finset.card_eq_zero.mp hright_zero

  let leftSide : Finset ι :=
    (Finset.univ : Finset (Fin (p - 1))).product {false}
  have ht_sub_left : t ⊆ leftSide := by
    intro x hx
    rcases x with ⟨x, b⟩
    cases b with
    | false =>
        exact Finset.mem_product.mpr ⟨Finset.mem_univ x, Finset.mem_singleton_self false⟩
    | true =>
        exfalso
        have hxr : (x, true) ∈ rightTerms := by
          simp [rightTerms, hx]
        rw [hright_empty] at hxr
        simp at hxr

  have ht_le : t.card ≤ p - 1 := by
    calc
      t.card ≤ leftSide.card := Finset.card_le_card ht_sub_left
      _ = p - 1 := by simp [leftSide]
  omega

/-- Sharp Erdős--Ginzburg--Ziv theorem.  The proof actually works for every
modulus `p ≥ 2`; the prime case is stated separately below. -/
theorem sFp_eq_two_mul_sub_one {p : ℕ} (hp : 2 ≤ p) :
    sFp p = 2 * p - 1 := by
  apply le_antisymm
  · exact sFp_min (forcesZeroSum_two_mul_sub_one p)
  · by_contra hle
    have hs_le : sFp p ≤ 2 * p - 2 := by omega
    exact not_forcesZeroSum_two_mul_sub_two hp
      (ForcesZeroSum.mono (sFp_spec p) hs_le)

/-- The Erdős--Ginzburg--Ziv theorem for the prime field `𝔽_p = ZMod p`:
`s(𝔽_p) = 2p - 1`. -/
theorem erdos_ginzburg_ziv_prime {p : ℕ} (hp : p.Prime) :
    sFp p = 2 * p - 1 :=
  sFp_eq_two_mul_sub_one hp.two_le

end PrimeEGZ
