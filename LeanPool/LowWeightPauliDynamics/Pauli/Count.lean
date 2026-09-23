/-
Copyright (c) 2026 Jue Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jue Xu
-/
import LeanPool.LowWeightPauliDynamics.Pauli.Coeff

/-!
# How many Paulis LPD stores: `O(n^{w*})`

The number of Pauli classes on `n` qubits of weight at most `w` is at most `C(n,w) · 4^w`, hence
at most `4^w · n^w`. This is the counting step of `apd:thm:lightcone` and `apd:thm:runtime`: an
observable truncated at weight `w*` contains `O(n^{w*})` Pauli operators, and the time
`O((r+1) · n^{w*})` and memory `O(n^{w*})` of `apd:thm:runtime` are built on that count.

**Scope.** `apd:thm:runtime` itself is not formalized in this library; only this count is. The
rest of that theorem combines the truncation-error analysis (the entanglement hypothesis of
`apd:thm:triangle`, the short-time condition `t < t₀`, and the formula for `w*`, of which this
library proves the existence form `exists_uniform_weight_cutoff`) with a *computational cost
model*: a data structure indexed by supports, with `O(1)` access to a coefficient. A cost model is
not something this library formalizes; it could only enter as a declared assumption. The counting
step is the opposite: pure combinatorics, independent of all of those, and it is what makes
`n^{w*}` polynomial rather than exponential in `n` at fixed `w*`.

**The bound is `C(n,w) · 4^w`, and it is loose in two stated ways.** It double-counts classes of
weight `< w`, which lie in several `w`-element supersets, and it allows a site inside the chosen
support to be the identity, giving `4` where an exact count gives `3`. Both are the price of
avoiding a fiberwise exact count, and neither affects the `O(n^w)` conclusion. `card_lowSet_le`
is an explicit inequality where the paper writes `O(·)`, and an upper bound is the direction that
matters: an upper bound on the number of stored Paulis is what bounds the runtime.

## Main definitions

* `lowSet n w`: the Pauli classes of weight at most `w`, the complement of `highSet n w`. These
  are the classes a weight-`w` truncation retains.
* `psupp p`: the sites at which the class `p` is not the identity.
* `vanishOff S`: the classes that are the identity outside the set of sites `S`.

## Main results

* `card_vanishOff`: exactly `4 ^ S.card` classes are the identity outside `S`.
* `card_lowSet_le`: `(lowSet n w).card ≤ n.choose w * 4 ^ w` for `w ≤ n`.
* `card_lowSet_le_pow`: `(lowSet n w).card ≤ 4 ^ w * n ^ w` for `w ≤ n`.
-/

namespace Lean4LPD.PauliString
open Finset

variable {n : ℕ}

/-- The low-weight region: the Pauli classes of weight at most `w`, defined as the complement of
`highSet n w`. These are the classes a weight-`w` truncation retains. -/
def lowSet (n w : ℕ) : Finset (PauliIndex n) := (highSet n w)ᶜ

@[simp] lemma mem_lowSet {w : ℕ} {p : PauliIndex n} : p ∈ lowSet n w ↔ wt p ≤ w := by
  simp [lowSet]

/-- A Pauli class read site by site: the pair of `x` and `z` bits at each qubit. The pair is `0`
exactly when the class is the identity at that site. -/
def siteFun (p : PauliIndex n) : Fin n → ZMod 2 × ZMod 2 := fun i => (p.1 i, p.2 i)

/-- `siteFun` as an equivalence between Pauli classes and functions from sites to bit pairs. -/
def siteEquiv : PauliIndex n ≃ (Fin n → ZMod 2 × ZMod 2) where
  toFun := siteFun
  invFun f := (fun i => (f i).1, fun i => (f i).2)
  left_inv _ := rfl
  right_inv _ := funext fun _ => rfl

/-- The sites at which the class is not the identity. `wt` counts exactly these. -/
def psupp (p : PauliIndex n) : Finset (Fin n) := univ.filter fun i => siteFun p i ≠ 0

lemma wt_eq_card_psupp (p : PauliIndex n) : wt p = (psupp p).card := rfl

@[simp] lemma mem_psupp {p : PauliIndex n} {i : Fin n} : i ∈ psupp p ↔ siteFun p i ≠ 0 := by
  simp [psupp]

/-- Classes whose site function vanishes outside `S`. -/
def vanishOff (S : Finset (Fin n)) : Finset (PauliIndex n) :=
  univ.filter fun p => ∀ i ∉ S, siteFun p i = 0

/-- Exactly `4 ^ S.card` classes are the identity outside `S`: each site of `S` carries one of
the four bit pairs, and every other site carries `0`. -/
lemma card_vanishOff (S : Finset (Fin n)) : (vanishOff S).card = 4 ^ S.card := by
  classical
  have himg : vanishOff S
      = (Fintype.piFinset fun i => if i ∈ S then (univ : Finset (ZMod 2 × ZMod 2)) else {0}).image
          siteEquiv.symm := by
    ext p
    simp only [vanishOff, mem_filter, mem_univ, true_and, mem_image, Fintype.mem_piFinset]
    constructor
    · intro h
      refine ⟨siteFun p, fun i => ?_, siteEquiv.left_inv p⟩
      by_cases hi : i ∈ S
      · simp [hi]
      · simp [hi, h i hi]
    · rintro ⟨f, hf, rfl⟩ i hi
      have hfi := hf i
      simp only [hi, ite_false, mem_singleton] at hfi
      have : siteFun (siteEquiv.symm f) i = f i := rfl
      rw [this, hfi]
  rw [himg, card_image_of_injective _ siteEquiv.symm.injective, Fintype.card_piFinset]
  have hcard : ∀ i : Fin n,
      (if i ∈ S then (univ : Finset (ZMod 2 × ZMod 2)) else {0}).card = if i ∈ S then 4 else 1 := by
    intro i; by_cases hi : i ∈ S <;> simp [hi]
  rw [Finset.prod_congr rfl fun i _ => hcard i, Finset.prod_ite_mem]
  simp

/-- **The stored set is polynomial in `n` for fixed `w`.**

`apd:thm:runtime` uses that an observable truncated at weight `w*` contains `O(n^{w*})` Pauli
operators. This is that count, with the constant explicit rather than inside an `O(·)`.

Every class of weight `≤ w` has its support inside some `w`-element set, and the classes supported
in a fixed `S` number exactly `4^{|S|}` (`card_vanishOff`) — so the union over all `C(n,w)` choices
of `S` bounds the whole stored set. The bound is not tight: it double-counts classes of weight
`< w`, which lie in several `S`. `4` rather than `3` for the same reason — a site inside `S` is
allowed to be the identity. Both are the price of avoiding a fiberwise exact count, and neither
affects the `O(n^w)` conclusion this is here to supply. -/
theorem card_lowSet_le (n w : ℕ) (hw : w ≤ n) :
    (lowSet n w).card ≤ n.choose w * 4 ^ w := by
  classical
  have hsub : lowSet n w ⊆ (univ.powersetCard w).biUnion vanishOff := by
    intro p hp
    have hcard : (psupp p).card ≤ w := by
      rw [← wt_eq_card_psupp]; exact mem_lowSet.1 hp
    obtain ⟨S, hPS, -, hScard⟩ :=
      Finset.exists_subsuperset_card_eq (Finset.subset_univ (psupp p)) hcard (by simpa using hw)
    refine mem_biUnion.2 ⟨S, mem_powersetCard.2 ⟨Finset.subset_univ S, hScard⟩, ?_⟩
    simp only [vanishOff, mem_filter, mem_univ, true_and]
    intro i hi
    by_contra hne
    exact hi (hPS (mem_psupp.2 hne))
  calc (lowSet n w).card
      ≤ ((univ.powersetCard w).biUnion vanishOff).card := card_le_card hsub
    _ ≤ ∑ S ∈ univ.powersetCard w, (vanishOff S).card := card_biUnion_le
    _ = n.choose w * 4 ^ w := by
        rw [Finset.sum_congr rfl fun S hS => by
              rw [card_vanishOff, (mem_powersetCard.1 hS).2]]
        rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
          smul_eq_mul]

/-- The same bound as a polynomial in `n`: `C(n,w) ≤ n^w`. This is the form
`apd:thm:runtime`'s `O(n^{w*})` names. -/
theorem card_lowSet_le_pow (n w : ℕ) (hw : w ≤ n) :
    (lowSet n w).card ≤ 4 ^ w * n ^ w :=
  (card_lowSet_le n w hw).trans <| by
    rw [Nat.mul_comm]
    exact Nat.mul_le_mul_left _ (Nat.choose_le_pow n w)

/-! ### Sanity checks: the bound holds and is not vacuous -/

/-- Two qubits, weight ≤ 1: the identity plus `3` single-site Paulis on each of `2` sites = `7`.
Proved by `decide`. -/
example : (lowSet 2 1).card = 7 := by decide

/-- The bound holds there and is loose by exactly the double-count it admits: `8` against `7`. -/
example : (lowSet 2 1).card ≤ Nat.choose 2 1 * 4 ^ 1 := card_lowSet_le 2 1 (by norm_num)

/-- Non-vacuous: the stored set is not everything. All `16` classes on two qubits, `7` of weight
`≤ 1`, so the truncation genuinely discards. -/
example : (lowSet 2 1).card < Fintype.card (PauliIndex 2) := by decide

/-- And it grows polynomially, not exponentially: weight `≤ 1` on three qubits is `10`,
not `2^6`. -/
example : (lowSet 3 1).card = 10 := by decide

end Lean4LPD.PauliString
