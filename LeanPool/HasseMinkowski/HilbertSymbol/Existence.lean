/-
Copyright (c) 2026 Nirvana Coppola, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nirvana Coppola, María Inés de Frutos-Fernández, jayyswan
-/
module

public import LeanPool.HasseMinkowski.HilbertSymbol.Defs
public import LeanPool.HasseMinkowski.HilbertSymbol.Padic
public import LeanPool.HasseMinkowski.HilbertSymbol.Real
public import LeanPool.HasseMinkowski.HilbertSymbol.Reciprocity
public import LeanPool.HasseMinkowski.HilbertSymbol.Local
public import LeanPool.HasseMinkowski.Legendre
public import LeanPool.HasseMinkowski.RatApproximation
public import LeanPool.HasseMinkowski.Padics.Squares
public import LeanPool.HasseMinkowski.RatSquares
public import Mathlib.NumberTheory.LSeries.PrimesInAP
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic

/-!
# Hilbert-symbol existence theorem

Given prescribed local Hilbert-symbol values `(x, aᵢ)_v = e_{i,v}` at all places `v` of `ℚ`,
one asks whether there is a single rational `x` realising all of them.  The answer is given
by the classical necessary-and-sufficient conditions (Serre, *Cours d'arithmétique*, Ch. III):

1. for each `i`, almost all the `e_{i,v}` are `1`;
2. for each `i`, the product of the `e_{i,v}` is `1` (the product formula);
3. the prescription is locally realisable at every place.

This file ports the **constructive core** of the HassePrinciple proof.  Writing `S` for the
finite set of
prime numbers dividing some `aᵢ` (together with `2`) and `T` for the finite set of primes at
which some `e_{i,p}` equals `-1`, the construction produces
`x = A · q` with `A = ∏_{t ∈ T} t` and `q` a prime chosen by Dirichlet's theorem so that
`q ≡ A (mod 4·∏_{s ∈ S} s)`.  This `x` is a square at every prime of `S`, has `p`-adic
valuation `1` at every prime of `T` and valuation `0` at the remaining primes — exactly the
three facts on which the place-by-place verification rests.

## Status

This file provides the Dirichlet/CRT construction of `S`, `T`, `A`, `M`, the
squareness/valuation lemmas at each place, the disjoint case of the existence theorem
(`exists_disjoint`, WP3.1 of `Plan-v3.md`), and the general existence theorem
(`exists_rat_hilbertSym`, WP3.2, Serre III Thm 4), which reduces to the disjoint case.  No
`sorry` is introduced.

## Provenance

This file is a derived work.  It is based on `HilbertSymbol/ExistenceTheorem.lean` of the
HassePrinciple project (<https://github.com/mariainesdff/HassePrinciple>,
Apache-2.0, Copyright (c) 2026 Nirvana Coppola,
María Inés de Frutos-Fernández), a Women in Numbers 7 collaboration.
It has been modified: the statements and proofs were rewritten for Lean 4.33 /
Mathlib without upstream's module system, and the development is extended beyond
what upstream proves.  Upstream declaration names are kept so that the two
developments can be compared side by side.  See the repository NOTICE file.
-/

@[expose] public section

namespace HasseMinkowski

open scoped BigOperators
open Filter Finset Nat
attribute [local instance] Classical.propDecidable

namespace Existence

variable {I : Type*} {a : I → ℤ} {ep : I → Primes → ℤ} {ereal : I → ℤ}

/-- From `ep i p = 1` or `-1`, we deduce `ep i p = -1` iff not `ep i p = 1`. -/
private lemma ep_eq_neg_one_iff_not_one
    (hep : ∀ i : I, ∀ p : Primes, ep i p = 1 ∨ ep i p = -1) {i : I} {p : Primes} :
    ep i p = -1 ↔ ¬ ep i p = 1 :=
  ⟨fun h => by simp [h], fun h => (hep i p).resolve_left h⟩

variable [Finite I]

/-- `S` is the finite set of primes dividing the numerator or the denominator of some `a i`,
together with `2`.  (In Serre, `S` also contains `∞`.) -/
noncomputable def S (a : I → ℤ) : Finset Primes :=
  have : Fintype I := Fintype.ofFinite I
  (Finset.univ.biUnion (fun i => (a i).natAbs.primeFactors) ∪ {2}).preimage Subtype.val
    Subtype.val_injective.injOn

-- Theorem: the prime `2` lies in `S`.
theorem two_in_S (a : I → ℤ) : (⟨2, Nat.prime_two⟩ : Primes) ∈ S a := by
  simp only [S]
  exact Finset.mem_preimage.mpr (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))

-- Theorem: the set of primes where some `ep i p` equals `-1` is finite, by hypothesis `h1`.
theorem Tfin (hep : ∀ i : I, ∀ p : Primes, ep i p = 1 ∨ ep i p = -1)
    (h1 : ∀ i : I, ∀ᶠ p : Primes in cofinite, ep i p = 1) :
    (⋃ i : I, {p : Primes | ep i p = -1}).Finite := by
  refine Set.finite_iUnion fun i => ?_
  simp only [eventually_cofinite, ← ep_eq_neg_one_iff_not_one hep, Int.reduceNeg] at h1
  exact h1 i

/-- `T` is the finite set of primes such that at least one of the `e_{i,v}` is `-1`. -/
noncomputable def T (hep : ∀ i : I, ∀ p : Primes, ep i p = 1 ∨ ep i p = -1)
    (h1 : ∀ i : I, ∀ᶠ p : Primes in cofinite, ep i p = 1) : Finset Primes :=
  (Tfin hep h1).toFinset

-- Theorem: a prime outside `T` has all its prescribed symbols equal to `1`.
theorem ep_eq_one_of_not_mem_T (hep : ∀ i : I, ∀ p : Primes, ep i p = 1 ∨ ep i p = -1)
    (h1 : ∀ i : I, ∀ᶠ p : Primes in cofinite, ep i p = 1)
    {p : Primes} (hpT : p ∉ T hep h1) (i : I) : ep i p = 1 := by
  simp only [T, Set.Finite.mem_toFinset, Set.mem_iUnion, Set.mem_ofPred_eq, not_exists,
    ep_eq_neg_one_iff_not_one hep] at hpT
  exact of_not_not (hpT i)

-- Theorem: membership in `T` characterisation.
theorem ep_eq_one_iff_not_mem_T (hep : ∀ i : I, ∀ p : Primes, ep i p = 1 ∨ ep i p = -1)
    (h1 : ∀ i : I, ∀ᶠ p : Primes in cofinite, ep i p = 1) (p : Primes) :
    p ∉ T hep h1 ↔ ∀ i : I, ep i p = 1 := by
  constructor
  · intro h i
    exact ep_eq_one_of_not_mem_T hep h1 h i
  · intro h
    simp only [T, Set.Finite.mem_toFinset, Set.mem_iUnion, Set.mem_ofPred_eq, not_exists]
    intro i
    rw [ep_eq_neg_one_iff_not_one hep]
    exact fun hc => hc (h i)

-- Theorem: if `S` and `T` are disjoint, every prime of `S` has all its symbols equal to `1`.
theorem ep_eq_one_of_mem_S_disjoint (a : I → ℤ)
    (hep : ∀ i : I, ∀ p : Primes, ep i p = 1 ∨ ep i p = -1)
    (h1 : ∀ i : I, ∀ᶠ p : Primes in cofinite, ep i p = 1)
    (disjoint_ST : Disjoint (S a) (T hep h1)) {p : Primes} (hpS : p ∈ S a) (i : I) :
    ep i p = 1 :=
  ep_eq_one_of_not_mem_T hep h1 (disjoint_left.mp disjoint_ST hpS) i

-- Theorem: if `p ∉ S` then every `a i` is a `p`-adic unit.
theorem is_unit_ai_of_p_notMem_S (a : I → ℤ) (ha : ∀ i, a i ≠ 0) {p : Primes}
    (hpS : p ∉ S a) (i : I) : padicValInt p (a i) = 0 := by
  have : Fintype I := Fintype.ofFinite I
  have hmem : p.1 ∉ Finset.univ.biUnion (fun i => (a i).natAbs.primeFactors) := by
    intro h
    apply hpS
    simp only [S]
    exact Finset.mem_preimage.mpr (Finset.mem_union.mpr (Or.inl (by simpa using h)))
  simp only [Finset.mem_biUnion, Finset.mem_univ, Nat.mem_primeFactors, p.2,
    ← Int.natCast_dvd, ne_eq, Int.natAbs_eq_zero, ha, not_false_eq_true, and_true, true_and,
    not_exists] at hmem
  exact padicValInt.eq_zero_of_not_dvd (hmem i)

/-- `A` is the product of all primes of `T`. -/
noncomputable def A (hep : ∀ i : I, ∀ p : Primes, ep i p = 1 ∨ ep i p = -1)
    (h1 : ∀ i : I, ∀ᶠ p : Primes in cofinite, ep i p = 1) : ℕ :=
  ∏ t ∈ T hep h1, (t : ℕ)

-- Theorem: `A` is nonzero.
theorem A_ne_zero (hep : ∀ i : I, ∀ p : Primes, ep i p = 1 ∨ ep i p = -1)
    (h1 : ∀ i : I, ∀ᶠ p : Primes in cofinite, ep i p = 1) : A hep h1 ≠ 0 := by
  rw [A, Finset.prod_ne_zero_iff]
  intro t _
  exact t.2.ne_zero

-- Theorem: `A` is positive.
theorem A_pos (hep : ∀ i : I, ∀ p : Primes, ep i p = 1 ∨ ep i p = -1)
    (h1 : ∀ i : I, ∀ᶠ p : Primes in cofinite, ep i p = 1) : 0 < A hep h1 :=
  Nat.pos_of_ne_zero (A_ne_zero hep h1)

/-- `M = 4 · ∏_{s ∈ S} s`, the modulus used in the congruence defining `q`. -/
noncomputable def M (a : I → ℤ) : ℕ := 4 * ∏ s ∈ S a, (s : ℕ)

-- Theorem: `M` is nonzero.
theorem M_ne_zero (a : I → ℤ) : M a ≠ 0 := by
  rw [M]
  refine mul_ne_zero (by norm_num) ?_
  rw [Finset.prod_ne_zero_iff]
  intro s _
  exact s.2.ne_zero

/-! ### WP3.1 sub-lemmas: the auxiliary prime `ℓ`

The construction `x = A · ℓ` needs `ℓ` to be a prime larger than every prime of `S ∪ T`
and congruent to `A` modulo `M`.  These lemmas record the elementary consequences of those
two hypotheses: `ℓ ∉ T` (hence `ε_{i,ℓ} = 1`), the congruence `M ∣ ℓ - A`, and the
divisibility of `A` by exactly the primes of `T`. -/

-- Theorem: a prime `ℓ` that exceeds every prime of `S ∪ T` is not in `T`.
theorem prime_notMem_T_of_lt (hε : ∀ i : I, ∀ p : Primes, ep i p = 1 ∨ ep i p = -1)
    (h1 : ∀ i : I, ∀ᶠ p : Primes in cofinite, ep i p = 1) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hℓgt : ∀ s ∈ S a ∪ T hε h1, (s : ℕ) < ℓ) : (⟨ℓ, hℓ⟩ : Primes) ∉ T hε h1 := by
  intro hmem
  exact absurd (hℓgt _ (Finset.mem_union.mpr (Or.inr hmem))) (lt_irrefl ℓ)

-- Theorem: a prime `ℓ` that exceeds every prime of `S ∪ T` satisfies `ε_{i,ℓ} = 1` for
-- every `i`.
theorem ep_eq_one_prime_of_lt (hε : ∀ i : I, ∀ p : Primes, ep i p = 1 ∨ ep i p = -1)
    (h1 : ∀ i : I, ∀ᶠ p : Primes in cofinite, ep i p = 1) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hℓgt : ∀ s ∈ S a ∪ T hε h1, (s : ℕ) < ℓ) (i : I) : ep i ⟨ℓ, hℓ⟩ = 1 :=
  ep_eq_one_of_not_mem_T hε h1 (prime_notMem_T_of_lt hε h1 hℓ hℓgt) i

-- Theorem: `M a` divides `ℓ - A` as integers; equivalently `(ℓ : ℤ) ≡ A [ZMOD M]`.
theorem M_dvd_int (hε : ∀ i : I, ∀ p : Primes, ep i p = 1 ∨ ep i p = -1)
    (h1 : ∀ i : I, ∀ᶠ p : Primes in cofinite, ep i p = 1) {ℓ : ℕ}
    (hℓA : ℓ ≡ A hε h1 [MOD M a]) :
    (M a : ℤ) ∣ (ℓ : ℤ) - (A hε h1 : ℤ) := by
  have h : (M a : ℤ) ∣ (A hε h1 : ℤ) - (ℓ : ℤ) := hℓA.dvd
  have h2 : (M a : ℤ) ∣ -((A hε h1 : ℤ) - (ℓ : ℤ)) := h.neg_right
  rwa [neg_sub] at h2

-- Theorem: every prime of `T` divides `A`.
theorem dvd_A_of_mem_T (hε : ∀ i : I, ∀ p : Primes, ep i p = 1 ∨ ep i p = -1)
    (h1 : ∀ i : I, ∀ᶠ p : Primes in cofinite, ep i p = 1) {p : Primes}
    (hp : p ∈ T hε h1) : (p : ℕ) ∣ A hε h1 := by
  rw [A]
  exact Finset.dvd_prod_of_mem (fun t : Primes => (t : ℕ)) hp

-- Theorem: a prime outside `T` does not divide `A`.
theorem not_dvd_A_of_notMem_T (hε : ∀ i : I, ∀ p : Primes, ep i p = 1 ∨ ep i p = -1)
    (h1 : ∀ i : I, ∀ᶠ p : Primes in cofinite, ep i p = 1) {p : Primes}
    (hp : p ∉ T hε h1) : ¬ (p : ℕ) ∣ A hε h1 := by
  rw [A]
  intro hdvd
  obtain ⟨t, ht, hpt⟩ :=
    (p.2.prime.dvd_finsetProd_iff (fun t : Primes => (t : ℕ))).mp hdvd
  have hpt_eq : p = t := Subtype.ext ((Nat.prime_dvd_prime_iff_eq p.2 t.2).mp hpt)
  exact hp (by simpa [hpt_eq] using ht)

-- Theorem: disjointness of `S` and `T` puts `2` outside `T`.
theorem two_notMem_T_of_disjoint (hε : ∀ i : I, ∀ p : Primes, ep i p = 1 ∨ ep i p = -1)
    (h1 : ∀ i : I, ∀ᶠ p : Primes in cofinite, ep i p = 1)
    (hdisj : Disjoint (S a) (T hε h1)) : (⟨2, Nat.prime_two⟩ : Primes) ∉ T hε h1 :=
  disjoint_left.mp hdisj (two_in_S a)

-- Theorem: disjointness of `S` and `T` makes `A` odd.
theorem not_two_dvd_A (hε : ∀ i : I, ∀ p : Primes, ep i p = 1 ∨ ep i p = -1)
    (h1 : ∀ i : I, ∀ᶠ p : Primes in cofinite, ep i p = 1)
    (hdisj : Disjoint (S a) (T hε h1)) : ¬ 2 ∣ A hε h1 :=
  not_dvd_A_of_notMem_T hε h1 (two_notMem_T_of_disjoint hε h1 hdisj)

-- Theorem: every prime of `T` occurs to the first power in `A`: `padicValNat p A = 1`.
theorem padicValNat_A_of_mem_T (hε : ∀ i : I, ∀ p : Primes, ep i p = 1 ∨ ep i p = -1)
    (h1 : ∀ i : I, ∀ᶠ p : Primes in cofinite, ep i p = 1) {p : Primes}
    (hp : p ∈ T hε h1) : padicValNat (p : ℕ) (A hε h1) = 1 := by
  rw [← Nat.factorization_def (A hε h1) p.2, A]
  rw [Nat.factorization_prod_apply (g := fun t : Primes => (t : ℕ)) (S := T hε h1)
    (fun t _ => t.2.ne_zero)]
  have hterm : ∀ t ∈ T hε h1,
      ((t : ℕ)).factorization (p : ℕ) = if t = p then 1 else 0 := by
    intro t _
    by_cases htp : t = p
    · rw [ite_eq_left htp, htp, Nat.factorization_def _ p.2]
      exact padicValNat_self
    · rw [ite_eq_right htp, Nat.factorization_eq_zero_of_not_dvd]
      intro hdvd
      exact htp (Subtype.ext ((Nat.prime_dvd_prime_iff_eq p.2 t.2).mp hdvd)).symm
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' (T hε h1) p (fun _ => (1 : ℕ)),
    ite_eq_left hp]

-- Theorem: `M = 4 · ∏_{s ∈ S} s` is divisible by `8`, because `2 ∈ S`.
theorem eight_dvd_M (a : I → ℤ) : 8 ∣ M a := by
  rw [M]
  have hdvd : 2 ∣ ∏ s ∈ S a, (s : ℕ) :=
    Finset.dvd_prod_of_mem (fun s : Primes => (s : ℕ)) (two_in_S a)
  obtain ⟨c, hc⟩ := hdvd
  exact ⟨c, by rw [hc]; ring⟩

-- Theorem: a prime of `S` divides the modulus `M`.
theorem dvd_M_of_mem_S (a : I → ℤ) {p : Primes} (hpS : p ∈ S a) : (p : ℕ) ∣ M a := by
  rw [M]
  by_cases hp2 : (p : ℕ) = 2
  · rw [hp2]
    exact dvd_mul_of_dvd_left (by norm_num : 2 ∣ 4) _
  · exact dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem (fun s : Primes => (s : ℕ)) hpS) 4

-- Theorem: a prime strictly below a prime `ℓ` does not divide `ℓ`.
theorem prime_not_dvd_of_lt {p : Primes} {ℓ : ℕ} (hℓ : ℓ.Prime) (hlt : (p : ℕ) < ℓ) :
    ¬ (p : ℕ) ∣ ℓ := by
  have hp2 : 1 < (p : ℕ) := p.2.one_lt
  rintro h
  rcases (Nat.dvd_prime hℓ).mp h with h1 | h2
  · omega
  · omega

-- Theorem: a prime different from `ℓ` does not divide the prime `ℓ`.
theorem prime_not_dvd_of_ne {p : Primes} {ℓ : ℕ} (hℓ : ℓ.Prime) (hne : (p : ℕ) ≠ ℓ) :
    ¬ (p : ℕ) ∣ ℓ := by
  have hp2 : 1 < (p : ℕ) := p.2.one_lt
  rintro h
  rcases (Nat.dvd_prime hℓ).mp h with h1 | h2
  · omega
  · exact hne h2

/-- Coercion of an integral square to a rational square. -/
private lemma isSquare_ratCast_of_isSquare_intCast {p : ℕ} [Fact (Nat.Prime p)] {n : ℕ}
    (h : IsSquare ((n : ℤ_[p]))) : IsSquare ((n : ℚ_[p])) := by
  obtain ⟨z, hz⟩ := h
  refine ⟨(z : ℚ_[p]), ?_⟩
  have hc := congrArg (fun t : ℤ_[p] => (t : ℚ_[p])) hz
  push_cast at hc
  simpa using hc

/-- An odd-`p` natural whose reduction mod `p` is a square is a square in `ℚ_[p]`. -/
private lemma isSquare_odd_natCast_of_mod {p : ℕ} [Fact (Nat.Prime p)] (hp : p ≠ 2)
    {n : ℕ} (hm : ¬ (p : ℤ_[p]) ∣ (n : ℤ_[p])) (hmod : IsSquare ((n : ZMod p))) :
    IsSquare ((n : ℚ_[p])) :=
  isSquare_ratCast_of_isSquare_intCast (PadicInt.isSquare_of_zmod hp hm (by simpa using hmod))

/-- A natural congruent to `1` mod `8` is a square in `ℚ_[2]`. -/
private lemma isSquare_two_natCast_of_mod8 {n : ℕ} (hm8 : (n : ZMod 8) = 1) :
    IsSquare ((n : ℚ_[2])) := by
  have h2 : (n : ZMod 2) = 1 := by
    have hc := congrArg (ZMod.castHom (by norm_num : 2 ∣ 8) (ZMod 2)) hm8
    simpa using hc
  have hndvd : ¬ (2 : ℤ_[2]) ∣ (n : ℤ_[2]) := by
    intro hd
    have hd' : (n : ℤ_[2]).toZMod = 0 :=
      (PadicInt.p_dvd_iff_toZMod_eq_zero (p := 2)).mp hd
    rw [map_natCast, h2] at hd'
    exact one_ne_zero hd'
  obtain ⟨z, hz⟩ := PadicInt.isSquare_of_zmodPow hndvd (by
    rw [map_natCast, hm8]
    exact IsSquare.one)
  refine ⟨(z : ℚ_[2]), ?_⟩
  have hc := congrArg (fun t : ℤ_[2] => (t : ℚ_[2])) hz
  push_cast at hc
  simpa using hc

-- Theorem: for `p ∈ S a`, the number `A · ℓ` is a square in `ℚ_[p]`.
theorem isSquare_A_mul_ell_of_mem_S
    (hε : ∀ i : I, ∀ p : Primes, ep i p = 1 ∨ ep i p = -1)
    (h1 : ∀ i : I, ∀ᶠ p : Primes in cofinite, ep i p = 1)
    (hdisj : Disjoint (S a) (T hε h1)) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hℓA : ℓ ≡ A hε h1 [MOD M a]) (hℓgt : ∀ s ∈ S a ∪ T hε h1, (s : ℕ) < ℓ)
    {p : Primes} (hpS : p ∈ S a) :
    IsSquare ((((A hε h1) * ℓ : ℕ) : ℚ_[p])) := by
  set A' : ℕ := A hε h1 with hA'
  set n : ℕ := A' * ℓ with hn
  have hpMdvd : (p : ℕ) ∣ M a := dvd_M_of_mem_S a hpS
  have hpT : p ∉ T hε h1 := disjoint_left.mp hdisj hpS
  have hAnot2 : ¬ 2 ∣ A' := by rw [hA']; exact not_two_dvd_A hε h1 hdisj
  have hpAd : ¬ (p : ℕ) ∣ A' := by rw [hA']; exact not_dvd_A_of_notMem_T hε h1 hpT
  have hplt : (p : ℕ) < ℓ := hℓgt p (Finset.mem_union.mpr (Or.inl hpS))
  have hpℓ : ¬ (p : ℕ) ∣ ℓ := prime_not_dvd_of_lt hℓ hplt
  have hpn : ¬ (p : ℕ) ∣ n := by
    rw [hn]
    exact p.2.not_dvd_mul hpAd hpℓ
  have hmodp : ℓ ≡ A' [MOD (p : ℕ)] := by rw [hA']; exact hℓA.of_dvd hpMdvd
  have hzeq : ((ℓ : ZMod (p : ℕ))) = ((A' : ZMod (p : ℕ))) :=
    (ZMod.natCast_eq_natCast_iff ℓ A' (p : ℕ)).mpr hmodp
  have hnz : ((n : ZMod (p : ℕ))) = (A' : ZMod (p : ℕ)) ^ 2 := by
    rw [hn, Nat.cast_mul, hzeq, sq]
  by_cases hp2 : (p : ℕ) = 2
  · have hmod8 : ℓ ≡ A' [MOD 8] := by rw [hA']; exact hℓA.of_dvd (eight_dvd_M a)
    have hℓ8 : ((ℓ : ZMod 8)) = ((A' : ZMod 8)) :=
      (ZMod.natCast_eq_natCast_iff ℓ A' 8).mpr hmod8
    have hn8 : ((n : ZMod 8)) = (A' : ZMod 8) ^ 2 := by
      rw [hn, Nat.cast_mul, hℓ8, sq]
    have hAodd : Odd A' :=
      Nat.not_even_iff_odd.mp (fun he => hAnot2 (even_iff_two_dvd.mp he))
    have hAsq : ((A' : ZMod 8)) ^ 2 = 1 := by
      set r : ℕ := A' % 8 with hr
      have hrval : ((r : ℕ) : ZMod 8) = (A' : ZMod 8) := by
        rw [hr]
        exact (ZMod.natCast_eq_natCast_iff (A' % 8) A' 8).mpr (Nat.mod_modEq A' 8)
      have hlt : r < 8 := by rw [hr]; exact Nat.mod_lt _ (by norm_num)
      have hodd : r % 2 = 1 := by
        rw [hr, Nat.mod_mod_of_dvd A' (by norm_num : 2 ∣ 8)]
        exact Nat.odd_iff.mp hAodd
      rw [← hrval]
      interval_cases r <;> (norm_num at hodd) <;> decide
    have hn1 : ((n : ZMod 8)) = 1 := by rw [hn8, hAsq]
    obtain rfl : p = ⟨2, Nat.prime_two⟩ := Subtype.ext hp2
    exact isSquare_two_natCast_of_mod8 hn1
  · have hm : ¬ (p : ℤ_[p]) ∣ (n : ℤ_[p]) := by
      intro hd
      have hd' : (n : ℤ_[p]).toZMod = 0 := (PadicInt.p_dvd_iff_toZMod_eq_zero).mp hd
      rw [map_natCast, ← Nat.cast_zero] at hd'
      exact hpn (Nat.modEq_zero_iff_dvd.mp ((ZMod.natCast_eq_natCast_iff n 0 (p : ℕ)).mp hd'))
    exact isSquare_odd_natCast_of_mod hp2 hm ⟨(A' : ZMod (p : ℕ)), by rw [hnz]; ring⟩

-- Theorem: for `p ∈ S a` and any `i`, the symbol `(a i, A·ℓ)_p` is `1`.
theorem hilbertSym_A_mul_ell_eq_one_of_mem_S (ha : ∀ i, a i ≠ 0)
    (hε : ∀ i : I, ∀ p : Primes, ep i p = 1 ∨ ep i p = -1)
    (h1 : ∀ i : I, ∀ᶠ p : Primes in cofinite, ep i p = 1)
    (hdisj : Disjoint (S a) (T hε h1)) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hℓA : ℓ ≡ A hε h1 [MOD M a]) (hℓgt : ∀ s ∈ S a ∪ T hε h1, (s : ℕ) < ℓ)
    {p : Primes} (hpS : p ∈ S a) (i : I) :
    hilbertSym (a i : ℚ_[p]) (((A hε h1) * ℓ : ℕ) : ℚ_[p]) = 1 := by
  obtain ⟨y, hy⟩ := isSquare_A_mul_ell_of_mem_S hε h1 hdisj hℓ hℓA hℓgt hpS
  have hn0 : (((A hε h1) * ℓ : ℕ) : ℚ_[p]) ≠ 0 := by
    push_cast
    exact mul_ne_zero (by exact_mod_cast A_ne_zero hε h1) (by exact_mod_cast hℓ.ne_zero)
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hy
    exact hn0 hy
  have hai : (a i : ℚ_[p]) ≠ 0 := by exact_mod_cast ha i
  rw [hy, ← pow_two]
  exact hilbertSym_sq_right hai hy0

/-! ### The symbol at a `p`-adic unit against an arbitrary element

For odd `p`, if the first argument is a unit then only the parity of the valuation of the
second argument matters: `(u,b)_p = χ(u)` for odd valuation and `= 1` for even valuation. -/

-- Theorem: the valuation of a `p`-adic unit is `0`.
private lemma valuation_unit_eq_zero {p : ℕ} [Fact (Nat.Prime p)] (u : ℤ_[p]ˣ) :
    Padic.valuation ((u : ℤ_[p]) : ℚ_[p]) = 0 := by
  have hne : ((u : ℤ_[p]) : ℚ_[p]) ≠ 0 := by
    rw [PadicInt.coe_ne_zero]
    exact u.ne_zero
  have hnorm : ‖((u : ℤ_[p]) : ℚ_[p])‖ = 1 := by
    rw [← PadicInt.norm_def, PadicInt.norm_units]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast Nat.Prime.pos Fact.out
  have hp1 : (p : ℝ) ≠ 1 := by exact_mod_cast (ne_of_gt (Nat.Prime.one_lt Fact.out))
  have h : (p : ℝ) ^ (-(Padic.valuation ((u : ℤ_[p]) : ℚ_[p]))) = (p : ℝ) ^ (0 : ℤ) := by
    rw [zpow_zero, ← Padic.norm_eq_zpow_neg_valuation hne, hnorm]
  have := (zpow_right_inj₀ hp0 hp1).mp h
  simpa using this

-- Theorem: the unit part of a `p`-adic unit is that unit.
private lemma padicUnit_unit {p : ℕ} [Fact (Nat.Prime p)] (u : ℤ_[p]ˣ)
    (hu : ((u : ℤ_[p]) : ℚ_[p]) ≠ 0) :
    padicUnit ((u : ℤ_[p]) : ℚ_[p]) hu = u := by
  apply Units.ext
  apply Subtype.ext
  rw [coe_padicUnit, valuation_unit_eq_zero, neg_zero, zpow_zero, mul_one]

-- Theorem: for odd `p`, `(u,b)_p` for a unit `u` depends only on the parity of `b`'s
-- valuation: it is `χ(u)` for odd valuation and `1` for even valuation.
private lemma hilbertSym_unit_eq_parity {p : ℕ} [Fact (Nat.Prime p)] (hp : p ≠ 2)
    (u : ℤ_[p]ˣ) {b : ℚ_[p]} (hb : b ≠ 0) :
    hilbertSym ((u : ℤ_[p]) : ℚ_[p]) b =
      if Even b.valuation then 1
        else (quadraticChar (ZMod p)) (PadicInt.toZMod (u : ℤ_[p])) := by
  have hu : ((u : ℤ_[p]) : ℚ_[p]) ≠ 0 := by
    rw [PadicInt.coe_ne_zero]
    exact u.ne_zero
  rw [hilbertSym_padic_odd_eq hp hu hb, valuation_unit_eq_zero u, padicUnit_unit u hu]
  simp [parityPow]

-- Theorem: for odd `p`, if the first argument has valuation `0` then `(a,b)_p` depends only
-- on the parity of `b`'s valuation.
private lemma hilbertSym_val_zero_eq_parity {p : ℕ} [Fact (Nat.Prime p)] (hp : p ≠ 2)
    {a b : ℚ_[p]} (ha : a ≠ 0) (hva : Padic.valuation a = 0) (hb : b ≠ 0) :
    hilbertSym a b = if Even (Padic.valuation b) then 1
      else (quadraticChar (ZMod p)) (PadicInt.toZMod (padicUnit a ha : ℤ_[p])) := by
  have hpu : (padicUnit a ha : ℚ_[p]) = a := by
    rw [coe_padicUnit, hva, neg_zero, zpow_zero, mul_one]
  have h1 := hilbertSym_unit_eq_parity hp (padicUnit a ha) hb
  rw [hpu] at h1
  exact h1

-- Theorem: the `T`-place of the construction: for `p ∈ T`, `(a i, A·ℓ)_p = ep i p`.
theorem hilbertSym_A_mul_ell_eq_of_mem_T (ha : ∀ i, a i ≠ 0)
    (hε : ∀ i : I, ∀ p : Primes, ep i p = 1 ∨ ep i p = -1)
    (h1 : ∀ i : I, ∀ᶠ p : Primes in cofinite, ep i p = 1)
    (hdisj : Disjoint (S a) (T hε h1)) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hℓgt : ∀ s ∈ S a ∪ T hε h1, (s : ℕ) < ℓ)
    (h3 : ∀ p : Primes, ∃ x : ℚ_[p], x ≠ 0 ∧ ∀ i, hilbertSym (a i : ℚ_[p]) x = ep i p)
    {p : Primes} (hpT : p ∈ T hε h1) (i : I) :
    hilbertSym (a i : ℚ_[p]) ((A hε h1 * ℓ : ℕ) : ℚ_[p]) = ep i p := by
  have hpS : p ∉ S a := disjoint_right.mp hdisj hpT
  have hp2 : (p : ℕ) ≠ 2 := by
    intro h
    exact hpS (by rw [show p = ⟨2, Nat.prime_two⟩ from Subtype.ext h]; exact two_in_S a)
  have hpℓ : ¬ (p : ℕ) ∣ ℓ :=
    prime_not_dvd_of_lt hℓ (hℓgt p (Finset.mem_union.mpr (Or.inr hpT)))
  have hai : (a i : ℚ_[p]) ≠ 0 := by exact_mod_cast ha i
  have hva : Padic.valuation (a i : ℚ_[p]) = 0 := by
    rw [Padic.valuation_intCast, is_unit_ai_of_p_notMem_S a ha hpS i]
    norm_num
  have hx0 : ((A hε h1 * ℓ : ℕ) : ℚ_[p]) ≠ 0 := by
    push_cast
    exact mul_ne_zero (by exact_mod_cast A_ne_zero hε h1) (by exact_mod_cast hℓ.ne_zero)
  have hvx : Padic.valuation ((A hε h1 * ℓ : ℕ) : ℚ_[p]) = 1 := by
    rw [Padic.valuation_natCast,
      padicValNat.mul (A_ne_zero hε h1) hℓ.ne_zero, padicValNat_A_of_mem_T hε h1 hpT,
      padicValNat.eq_zero_of_not_dvd hpℓ, add_zero]
    norm_num
  have hxpar : hilbertSym (a i : ℚ_[p]) ((A hε h1 * ℓ : ℕ) : ℚ_[p])
      = (quadraticChar (ZMod (p : ℕ)))
        (PadicInt.toZMod (padicUnit (a i : ℚ_[p]) hai : ℤ_[p])) := by
    rw [hilbertSym_val_zero_eq_parity hp2 hai hva hx0, hvx,
      ite_eq_right (by decide : ¬ Even (1 : ℤ))]
  obtain ⟨j, hj⟩ : ∃ j, ep j p = -1 := by
    by_contra hcon
    push Not at hcon
    exact (ep_eq_one_iff_not_mem_T hε h1 p).mpr
      (fun k => (hε k p).resolve_right (hcon k)) hpT
  obtain ⟨xp, hxp0, hxp⟩ := h3 p
  have hxpj : hilbertSym (a j : ℚ_[p]) xp = -1 := by rw [hxp j, hj]
  have haj : (a j : ℚ_[p]) ≠ 0 := by exact_mod_cast ha j
  have hvaj : Padic.valuation (a j : ℚ_[p]) = 0 := by
    rw [Padic.valuation_intCast, is_unit_ai_of_p_notMem_S a ha hpS j]
    norm_num
  have hodd : ¬ Even (Padic.valuation xp) := by
    intro heven
    rw [hilbertSym_val_zero_eq_parity hp2 haj hvaj hxp0, ite_eq_left heven] at hxpj
    norm_num at hxpj
  have hchi : ep i p = (quadraticChar (ZMod (p : ℕ)))
      (PadicInt.toZMod (padicUnit (a i : ℚ_[p]) hai : ℤ_[p])) := by
    rw [← hxp i, hilbertSym_val_zero_eq_parity hp2 hai hva hxp0, ite_eq_right hodd]
  rw [hxpar, ← hchi]

-- Theorem: the unit place of the construction: for `p` in neither `S`, `T` nor `{ℓ}`, the
-- symbol `(a i, A·ℓ)_p` is `1`.
theorem hilbertSym_A_mul_ell_eq_one_of_notMem (ha : ∀ i, a i ≠ 0)
    (hε : ∀ i : I, ∀ p : Primes, ep i p = 1 ∨ ep i p = -1)
    (h1 : ∀ i : I, ∀ᶠ p : Primes in cofinite, ep i p = 1) {ℓ : ℕ} (hℓ : ℓ.Prime)
    {p : Primes} (hpS : p ∉ S a) (hpT : p ∉ T hε h1) (hpℓ : (p : ℕ) ≠ ℓ) (i : I) :
    hilbertSym (a i : ℚ_[p]) ((A hε h1 * ℓ : ℕ) : ℚ_[p]) = 1 := by
  have hp2 : (p : ℕ) ≠ 2 := by
    intro h
    exact hpS (by rw [show p = ⟨2, Nat.prime_two⟩ from Subtype.ext h]; exact two_in_S a)
  have hai : (a i : ℚ_[p]) ≠ 0 := by exact_mod_cast ha i
  have hva : Padic.valuation (a i : ℚ_[p]) = 0 := by
    rw [Padic.valuation_intCast, is_unit_ai_of_p_notMem_S a ha hpS i]
    norm_num
  have hx0 : ((A hε h1 * ℓ : ℕ) : ℚ_[p]) ≠ 0 := by
    push_cast
    exact mul_ne_zero (by exact_mod_cast A_ne_zero hε h1) (by exact_mod_cast hℓ.ne_zero)
  have hvx : Padic.valuation ((A hε h1 * ℓ : ℕ) : ℚ_[p]) = 0 := by
    rw [Padic.valuation_natCast, padicValNat.mul (A_ne_zero hε h1) hℓ.ne_zero,
      padicValNat.eq_zero_of_not_dvd (not_dvd_A_of_notMem_T hε h1 hpT),
      padicValNat.eq_zero_of_not_dvd (prime_not_dvd_of_ne hℓ hpℓ), add_zero]
    norm_num
  rw [hilbertSym_val_zero_eq_parity hp2 hai hva hx0, hvx,
    ite_eq_left (show Even (0 : ℤ) from ⟨0, by norm_num⟩)]

/-! ### The product-formula obstruction

The hypotheses of `exists_disjoint` force the construction `x = A · ℓ`, but they do not
constrain the *product* of the prescribed values `ep i p`.  The lemma below shows this is a
genuine obstruction: if `a > 0` and a nonzero rational `x` realises the sign pattern that is
`-1` at a single prime `p₀` and `1` at every other finite place, then Hilbert reciprocity
(whose archimedean factor is `1` because `a > 0`) is violated.  Thus no version of
`exists_disjoint` without a hypothesis `∏ᶠ p, ep i p = 1` can be true. -/

-- Theorem: for `a > 0` there is no `x ≠ 0` whose Hilbert symbols against `a` are `-1` at a
-- single prime and `1` at every other prime.
--
-- Concretely, taking `I = Unit`, `a = 3`, `ep p = if p = 5 then -1 else 1` satisfies
-- `hε`, `h1`, `h3` and the disjointness of `S a = {2,3}` and `T = {5}`, and `ℓ = 29` is a
-- prime `> max(S ∪ T)` with `29 ≡ 5 [MOD 24]` — but the product `∏ᶠ p, ep p` is `-1`, so the
-- product-formula hypothesis `h2` of `exists_disjoint` fails.  Hence `h2` is genuinely
-- necessary, not a convenience.
theorem not_realizable_of_single_neg {a : ℚ} (ha : 0 < a) {p₀ : Primes} {x : ℚ}
    (hx : x ≠ 0)
    (hother : ∀ p : Primes, p ≠ p₀ → hilbertSym (a : ℚ_[p]) (x : ℚ_[p]) = 1)
    (hp₀ : hilbertSym (a : ℚ_[p₀]) (x : ℚ_[p₀]) = -1) : False := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hxR : (x : ℝ) ≠ 0 := Rat.cast_ne_zero.mpr hx
  have haR : (a : ℝ) ≠ 0 := Rat.cast_ne_zero.mpr ha0
  have hreal : hilbertSym (a : ℝ) (x : ℝ) = 1 := by
    rw [hilbertSym_real_eq haR hxR]
    exact ite_eq_left (Or.inl (by exact_mod_cast ha))
  have hprod : hilbertProd a x = 1 := hilbertReciprocity a x ha0 hx
  have hfp : (∏ᶠ p : Primes, hilbertSym (a : ℚ_[p]) (x : ℚ_[p])) = -1 := by
    rw [finprod_eq_single _ p₀ hother, hp₀]
  unfold hilbertProd at hprod
  rw [hfp, hreal] at hprod
  norm_num at hprod

/-! ### The `ℓ`-place and the assembly

At the new prime `ℓ` we use Hilbert reciprocity.  Since `x = A·ℓ > 0`, the archimedean factor
is `1`, so the product of all finite symbols is `1`; all finite places other than `ℓ` have
symbol `ep i p` (cases `S`, `T`, and the unit place), and the product of the `ep i p` is `1`
by `h2`.  Hence the symbol at `ℓ` is `1`, matching `ep i ℓ = 1`. -/

-- Theorem: if two integer-valued functions on the primes agree off a single point `ℓ'`, the
-- second is `1` at `ℓ'`, and both have product `1`, then the first is `1` at `ℓ'` as well.
private lemma finprod_eq_one_of_eq_off {F E : Primes → ℤ} {ℓ' : Primes}
    (hEsupp : Function.HasFiniteMulSupport E)
    (hFE : ∀ q, q ≠ ℓ' → F q = E q) (hE : E ℓ' = 1)
    (hprodE : (∏ᶠ q, E q) = 1) (hprodF : (∏ᶠ q, F q) = 1) : F ℓ' = 1 := by
  let G : Primes → ℤ := fun q => if q = ℓ' then F ℓ' else 1
  have hGsupp : Function.HasFiniteMulSupport G :=
    (Set.finite_singleton ℓ').subset (fun q hq => by
      by_contra hne
      exact hq (by dsimp only [G]; rw [ite_eq_right (by simpa using hne)]))
  have hFG : ∀ q, F q = E q * G q := by
    intro q
    by_cases hq : q = ℓ'
    · rw [hq, hE]
      dsimp only [G]
      rw [ite_eq_left rfl, one_mul]
    · dsimp only [G]
      rw [ite_eq_right hq, mul_one, hFE q hq]
  have hstep : (∏ᶠ q, F q) = (∏ᶠ q, E q) * (∏ᶠ q, G q) := by
    rw [finprod_congr hFG]
    exact finprod_mul_distrib hEsupp hGsupp
  have hGprod : (∏ᶠ q, G q) = F ℓ' := by
    rw [finprod_eq_single G ℓ' (fun q hq => by dsimp only [G]; rw [ite_eq_right hq])]
    dsimp only [G]
    rw [ite_eq_left rfl]
  rw [hprodE, one_mul, hGprod, hprodF] at hstep
  exact hstep.symm

-- Theorem: Serre's existence theorem, disjoint case (Serre III Thm 4).  If the prescribed
-- local symbols `ep i p` are almost all `1` (`h1`), have product `1` (`h2`), are locally
-- realisable (`h3`), and the sets `S` and `T` are disjoint, then `x = A·ℓ` realises them.
theorem exists_disjoint {I : Type*} [Finite I] (a : I → ℤ) (ha : ∀ i, a i ≠ 0)
    (εp : I → Primes → ℤ) (hε : ∀ i p, εp i p = 1 ∨ εp i p = -1)
    (h1 : ∀ i, ∀ᶠ p : Primes in cofinite, εp i p = 1)
    (h2 : ∀ i, (∏ᶠ p : Primes, εp i p) = 1)
    (h3 : ∀ p : Primes, ∃ x : ℚ_[p], x ≠ 0 ∧ ∀ i, hilbertSym (a i : ℚ_[p]) x = εp i p)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓA : ℓ ≡ A hε h1 [MOD M a])
    (hℓgt : ∀ s ∈ S a ∪ T hε h1, (s : ℕ) < ℓ) :
    ∃ x : ℚ, x ≠ 0 ∧ ∀ i (p : Primes), hilbertSym (a i : ℚ_[p]) x = εp i p := by
  -- `S` and `T` are automatically disjoint: a common prime would divide both `M` and `A`,
  -- hence would divide `ℓ`, forcing it to equal the prime `ℓ`, contrary to `hℓgt`.
  have hdisj : Disjoint (S a) (T hε h1) := by
    rw [Finset.disjoint_iff_ne]
    intro q hqS q' hqT hqq
    rw [← hqq] at hqT
    have hq1 : 1 < (q : ℕ) := q.2.one_lt
    have hlt : (q : ℕ) < ℓ := hℓgt q (Finset.mem_union.mpr (Or.inl hqS))
    have hqℓ : (q : ℕ) ∣ ℓ := by
      have hpdvd : (q : ℤ) ∣ (ℓ : ℤ) - (A hε h1 : ℤ) :=
        dvd_trans (Int.ofNat_dvd.mpr (dvd_M_of_mem_S a hqS)) (M_dvd_int hε h1 hℓA)
      have hqA : (q : ℤ) ∣ (A hε h1 : ℤ) :=
        Int.ofNat_dvd.mpr (dvd_A_of_mem_T hε h1 hqT)
      have hsum : (q : ℤ) ∣ (ℓ : ℤ) := by
        have h := dvd_add hpdvd hqA
        rwa [sub_add_cancel] at h
      exact Int.ofNat_dvd.mp hsum
    rcases (Nat.dvd_prime hℓ).mp hqℓ with h1 | h1
    · omega
    · omega
  refine ⟨(A hε h1 : ℚ) * (ℓ : ℚ), ?_, ?_⟩
  · exact mul_ne_zero (by exact_mod_cast A_ne_zero hε h1) (by exact_mod_cast hℓ.ne_zero)
  · intro i p
    have hcast : (((A hε h1 : ℚ) * (ℓ : ℚ) : ℚ) : ℚ_[p])
        = ((A hε h1 * ℓ : ℕ) : ℚ_[p]) := by
      push_cast
      ring
    rw [hcast]
    by_cases hpS : p ∈ S a
    · rw [hilbertSym_A_mul_ell_eq_one_of_mem_S ha hε h1 hdisj hℓ hℓA hℓgt hpS i,
        ep_eq_one_of_mem_S_disjoint a hε h1 hdisj hpS i]
    · by_cases hpT : p ∈ T hε h1
      · exact hilbertSym_A_mul_ell_eq_of_mem_T ha hε h1 hdisj hℓ hℓgt h3 hpT i
      · by_cases hpe : (p : ℕ) = ℓ
        · have hpeq : p = ⟨ℓ, hℓ⟩ := Subtype.ext hpe
          rw [hpeq]
          let F : Primes → ℤ := fun q =>
            hilbertSym (a i : ℚ_[q]) ((A hε h1 * ℓ : ℕ) : ℚ_[q])
          have hxq : (A hε h1 : ℚ) * (ℓ : ℚ) ≠ 0 :=
            mul_ne_zero (by exact_mod_cast A_ne_zero hε h1)
              (by exact_mod_cast hℓ.ne_zero)
          have hrealX : hilbertSym (((a i : ℚ) : ℝ))
              ((((A hε h1 : ℚ) * (ℓ : ℚ) : ℚ) : ℝ)) = 1 := by
            have hxR : ((((A hε h1 : ℚ) * (ℓ : ℚ) : ℚ) : ℝ)) ≠ 0 := by
              exact_mod_cast hxq
            have haR : (((a i : ℚ) : ℝ)) ≠ 0 := by exact_mod_cast ha i
            rw [hilbertSym_real_eq haR hxR]
            exact ite_eq_left (Or.inr (by
              push_cast
              exact mul_pos (by exact_mod_cast A_pos hε h1)
                (by exact_mod_cast hℓ.pos)))
          have hEℓ : εp i ⟨ℓ, hℓ⟩ = 1 := ep_eq_one_prime_of_lt hε h1 hℓ hℓgt i
          have hEsupp : Function.HasFiniteMulSupport (εp i) :=
            Filter.eventually_cofinite.mp (h1 i)
          have hFeq : ∀ q, q ≠ ⟨ℓ, hℓ⟩ → F q = εp i q := by
            intro q hq
            have hne : (q : ℕ) ≠ ℓ := fun h => hq (Subtype.ext h)
            by_cases hqS : q ∈ S a
            · rw [show F q = 1 from
                  hilbertSym_A_mul_ell_eq_one_of_mem_S ha hε h1 hdisj hℓ hℓA hℓgt hqS i,
                show εp i q = 1 from ep_eq_one_of_mem_S_disjoint a hε h1 hdisj hqS i]
            · by_cases hqT : q ∈ T hε h1
              · exact hilbertSym_A_mul_ell_eq_of_mem_T ha hε h1 hdisj hℓ hℓgt h3 hqT i
              · rw [show F q = 1 from
                    hilbertSym_A_mul_ell_eq_one_of_notMem ha hε h1 hℓ hqS hqT hne i,
                  show εp i q = 1 from ep_eq_one_of_not_mem_T hε h1 hqT i]
          have hfpF : (∏ᶠ q, F q) = 1 := by
            have hrecip := hilbertReciprocity (a i : ℚ) ((A hε h1 : ℚ) * (ℓ : ℚ))
              (by exact_mod_cast ha i) hxq
            rw [hrealX, mul_one] at hrecip
            have hcongr : (∏ᶠ q : Primes, hilbertSym (((a i : ℚ) : ℚ_[q]))
                ((((A hε h1 : ℚ) * (ℓ : ℚ) : ℚ) : ℚ_[q]))) = ∏ᶠ q, F q := by
              refine finprod_congr (fun q => ?_)
              dsimp only [F]
              (congr 2; push_cast; ring)
            rw [hcongr] at hrecip
            exact hrecip
          rw [hEℓ]
          exact finprod_eq_one_of_eq_off hEsupp hFeq hEℓ (h2 i) hfpF
        · rw [hilbertSym_A_mul_ell_eq_one_of_notMem ha hε h1 hℓ hpS hpT hpe i,
            ep_eq_one_of_not_mem_T hε h1 hpT i]

/-! ### WP3.2: the general existence theorem

We now drop the disjointness assumption.  The proof reduces `a` to squarefree integers,
approximates the local realisations by a rational `x'` whose quotients are local squares,
shifts the prescription by `(α i, x')`, and applies the disjoint-case
`exists_disjoint` to the shifted prescription. -/

-- Theorem: a nonzero Hilbert symbol is `1` or `-1`.
theorem hilbertSym_eq_one_or_neg_one {k : Type*} [Field k] {a b : k} (ha : a ≠ 0)
    (hb : b ≠ 0) : hilbertSym a b = 1 ∨ hilbertSym a b = -1 := by
  rcases hilbertSym_eq_one_or a b with h | h | h
  · exact Or.inl h
  · exact absurd ((hilbertSym_eq_zero_iff a b).mp h) (by rw [not_or]; exact ⟨ha, hb⟩)
  · exact Or.inr h

-- Theorem: multiplying the first argument of the Hilbert symbol by a nonzero square does not
-- change it.
theorem hilbertSym_mul_sq_left {k : Type*} [Field k] {a s b : k} (hs : s ≠ 0) :
    hilbertSym (a * s ^ 2) b = hilbertSym a b := by
  have h := hilbertSym_mul_square_eq (a := a) (a' := s) (b := b) (b' := 1) hs one_ne_zero
  simpa using h

-- Theorem: simultaneous weak approximation at the places of `S`, realising the local square
-- classes.  Given nonzero `p`-adic targets `x p` and a nonzero real `r`, there is `x' : ℚ`
-- with the sign of `r` and with `x' / x p` a square in `ℚ_[p]` for every `p ∈ S`.
theorem exists_rat_local_squares (S : Finset Primes) (hS : S.Nonempty)
    (x : (p : S) → ℚ_[p]) (hx : ∀ p, x p ≠ 0) {r : ℝ} (hr : r ≠ 0) :
    ∃ x' : ℚ, x' ≠ 0 ∧ (0 < r ↔ 0 < (x' : ℝ)) ∧
      ∀ p (hp : p ∈ S), IsSquare ((x' : ℚ_[p]) / x ⟨p, hp⟩) := by
  let δ : S → ℝ := fun p => ‖x p‖ / 4
  have hδpos : ∀ p, 0 < δ p := fun p => by
    dsimp only [δ]
    exact div_pos (norm_pos_iff.mpr (hx p)) (by norm_num)
  let T : Finset ℝ := (S.attach.image δ) ∪ {1, |r| / 2}
  have hTne : T.Nonempty := ⟨1, Finset.mem_union_right _ (Finset.mem_insert_self 1 _)⟩
  set ε : ℝ := T.min' hTne with hεdef
  have hεpos : 0 < ε := by
    rw [hεdef]
    have hmem := Finset.min'_mem T hTne
    rcases Finset.mem_union.mp hmem with h | h
    · obtain ⟨p, _, hp⟩ := Finset.mem_image.mp h
      rw [← hp]
      exact hδpos p
    · rcases Finset.mem_insert.mp h with h1 | h1
      · rw [h1]; norm_num
      · rw [Finset.mem_singleton.mp h1]
        exact div_pos (abs_pos.mpr hr) (by norm_num)
  have hεδ : ∀ p (hp : p ∈ S), ε ≤ δ ⟨p, hp⟩ := fun p hp =>
    Finset.min'_le T (δ ⟨p, hp⟩) (Finset.mem_union_left _
      (Finset.mem_image.mpr ⟨⟨p, hp⟩, Finset.mem_attach S ⟨p, hp⟩, rfl⟩))
  have hεr : ε ≤ |r| / 2 :=
    Finset.min'_le T (|r| / 2)
      (Finset.mem_union_right _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
  obtain ⟨x', hsum⟩ := Rat.approximation' hεpos (r, x)
  have hclose : ∀ p (hp : p ∈ S), ‖x ⟨p, hp⟩ - (x' : ℚ_[p])‖ < δ ⟨p, hp⟩ := by
    intro p hp
    have hmem : (⟨p, hp⟩ : S) ∈ Finset.attach S := Finset.mem_attach S ⟨p, hp⟩
    have h1 : ‖x ⟨p, hp⟩ - (x' : ℚ_[p])‖ ≤
        Finset.sum (Finset.attach S) (fun n => ‖x n - (x' : ℚ_[n.1.1])‖) :=
      Finset.single_le_sum (f := fun n : S => ‖x n - (x' : ℚ_[n.1.1])‖)
        (fun i _ => norm_nonneg _) hmem
    have h2 : Finset.sum (Finset.attach S) (fun n => ‖x n - (x' : ℚ_[n.1.1])‖) ≤
        ‖r - (x' : ℝ)‖ + Finset.sum (Finset.attach S)
          (fun n => ‖x n - (x' : ℚ_[n.1.1])‖) :=
      le_add_of_nonneg_left (norm_nonneg _)
    exact lt_of_lt_of_le (lt_of_le_of_lt (le_trans h1 h2) hsum) (hεδ p hp)
  have hx'0 : x' ≠ 0 := by
    intro h0
    rcases hS with ⟨p, hp⟩
    have hcl := hclose p hp
    rw [h0] at hcl
    dsimp only [δ] at hcl
    simp only [Rat.cast_zero, sub_zero] at hcl
    have := norm_pos_iff.mpr (hx ⟨p, hp⟩)
    linarith
  have hreal : ‖r - (x' : ℝ)‖ < |r| / 2 := by
    have h1 : ‖r - (x' : ℝ)‖ ≤ ‖r - (x' : ℝ)‖ + Finset.sum (Finset.attach S)
        (fun n => ‖x n - (x' : ℚ_[n.1.1])‖) :=
      le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    rw [Real.norm_eq_abs]
    exact lt_of_lt_of_le (lt_of_le_of_lt h1 hsum) hεr
  have hsign1 : 0 < r → 0 < (x' : ℝ) := by
    intro hr0
    have hlt := hreal
    rw [Real.norm_eq_abs, abs_lt] at hlt
    rw [abs_of_pos hr0] at hlt
    linarith [hlt.1]
  have hsign2 : r < 0 → (x' : ℝ) < 0 := by
    intro hr0
    have hlt := hreal
    rw [Real.norm_eq_abs, abs_lt] at hlt
    rw [abs_of_neg hr0] at hlt
    linarith [hlt.2]
  have hsign : 0 < r ↔ 0 < (x' : ℝ) := by
    refine ⟨hsign1, fun hx0 => ?_⟩
    rcases lt_trichotomy r 0 with h | h | h
    · exact absurd (hsign2 h) (not_lt.mpr hx0.le)
    · exact absurd h hr
    · exact h
  refine ⟨x', hx'0, hsign, ?_⟩
  intro p hp
  have hd : dist ((x' : ℚ_[p]) / x ⟨p, hp⟩) 1 < 1 / 4 := by
    have heq : (x' : ℚ_[p]) / x ⟨p, hp⟩ - 1
        = ((x' : ℚ_[p]) - x ⟨p, hp⟩) / x ⟨p, hp⟩ := by
      rw [div_sub_one]
      exact hx ⟨p, hp⟩
    calc dist ((x' : ℚ_[p]) / x ⟨p, hp⟩) 1
        = ‖((x' : ℚ_[p]) - x ⟨p, hp⟩) / x ⟨p, hp⟩‖ := by rw [dist_eq_norm, heq]
      _ = ‖(x' : ℚ_[p]) - x ⟨p, hp⟩‖ / ‖x ⟨p, hp⟩‖ := norm_div _ _
      _ < (‖x ⟨p, hp⟩‖ / 4) / ‖x ⟨p, hp⟩‖ := by
            refine div_lt_div_of_pos_right ?_ (norm_pos_iff.mpr (hx ⟨p, hp⟩))
            rw [norm_sub_rev]
            exact hclose p hp
      _ = 1 / 4 := by
            rw [div_div,
              div_eq_iff (mul_ne_zero (by norm_num) (norm_ne_zero_iff.mpr (hx ⟨p, hp⟩)))]
            ring
  by_cases hp2 : (p : ℕ) = 2
  · obtain rfl : p = ⟨2, Nat.prime_two⟩ := Subtype.ext hp2
    have hd2 : dist ((x' : ℚ_[2]) / x ⟨⟨2, Nat.prime_two⟩, hp⟩) 1
        < (2 : ℝ) ^ (-(2 : ℤ)) := by
      have hpow : (2 : ℝ) ^ (-(2 : ℤ)) = 1 / 4 := by norm_num
      rw [hpow]
      exact hd
    exact Padic.isSquare_of_dist_one_lt_pow hd2
  · exact Padic.isSquare_of_dist_one_lt_one hp2 (by linarith [hd])

-- Theorem: the integer cast and the rational cast of an integer give the same Hilbert symbol.
theorem hilbertSym_cast_eq {k : Type*} [Field k] (n : ℤ) (q : ℚ) :
    hilbertSym (((n : ℚ) : k)) (((q : ℚ) : k)) = hilbertSym (n : k) (q : k) := by
  have h1 : ((n : ℚ) : k) = (n : k) := by simp
  have h2 : ((q : ℚ) : k) = (q : k) := by simp
  rw [h1, h2]

-- Lemma: given a disjoint-case solution `y` for the shifted prescription `η`, the product
-- `x' * y` realises the original prescription at every place (Serre III Thm 4, Step 5).
private lemma combine_disjoint_solution {I : Type*} [Finite I]
    (a : I → ℚ) (α : I → ℤ) (hαne : ∀ i, α i ≠ 0)
    (ε : I → Primes → ℤ) (εR : I → ℤ) (η : I → Primes → ℤ) (x' : ℚ) (hx'0 : x' ≠ 0)
    (hηdef : ∀ i p, η i p = ε i p * hilbertSym (α i : ℚ_[p]) (x' : ℚ_[p]))
    (hηε : ∀ i p, η i p = 1 ∨ η i p = -1)
    (hη1 : ∀ i, ∀ᶠ p : Primes in cofinite, η i p = 1)
    (hη2 : ∀ i, (∏ᶠ p : Primes, η i p) = 1)
    (hη3 : ∀ p : Primes, ∃ x : ℚ_[p], x ≠ 0 ∧ ∀ i, hilbertSym (α i : ℚ_[p]) x = η i p)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓA : ℓ ≡ A hηε hη1 [MOD M α])
    (hℓgt : ∀ s ∈ S α ∪ T hηε hη1, (s : ℕ) < ℓ)
    (hreal_eq : ∀ i, hilbertSym (α i : ℝ) (x' : ℝ) = εR i)
    (hredp : ∀ i (p : Primes) (y : ℚ_[p]),
      hilbertSym (a i : ℚ_[p]) y = hilbertSym (α i : ℚ_[p]) y)
    (hredR : ∀ i (y : ℝ), hilbertSym (a i : ℝ) y = hilbertSym (α i : ℝ) y) :
    ∃ x : ℚ, x ≠ 0 ∧ (∀ i (p : Primes), hilbertSym (a i : ℚ_[p]) x = ε i p) ∧
      ∀ i, hilbertSym (a i : ℝ) x = εR i := by
  obtain ⟨y, hy0, hy⟩ := exists_disjoint α hαne η hηε hη1 hη2 hη3 hℓ hℓA hℓgt
  refine ⟨x' * y, mul_ne_zero hx'0 hy0, ?_, ?_⟩
  · intro i p
    have hsym_sq : hilbertSym (α i : ℚ_[p]) (x' : ℚ_[p])
        * hilbertSym (α i : ℚ_[p]) (x' : ℚ_[p]) = 1 := by
      rcases hilbertSym_eq_one_or_neg_one
        (show (α i : ℚ_[p]) ≠ 0 from by exact_mod_cast hαne i)
        (show (x' : ℚ_[p]) ≠ 0 from by exact_mod_cast hx'0) with h | h <;>
        rw [h] <;> norm_num
    have hα_i : hilbertSym (α i : ℚ_[p]) ((x' * y : ℚ) : ℚ_[p]) = ε i p := by
      rw [show ((x' * y : ℚ) : ℚ_[p]) = (x' : ℚ_[p]) * (y : ℚ_[p]) by push_cast; ring,
        HasBilinHilbertSym.mul_right_eq, hy i p, hηdef]
      rw [show hilbertSym (α i : ℚ_[p]) (x' : ℚ_[p])
            * (ε i p * hilbertSym (α i : ℚ_[p]) (x' : ℚ_[p]))
          = ε i p * (hilbertSym (α i : ℚ_[p]) (x' : ℚ_[p])
            * hilbertSym (α i : ℚ_[p]) (x' : ℚ_[p])) by ring,
        hsym_sq, mul_one]
    rw [hredp i p (((x' * y : ℚ) : ℚ_[p]))]
    exact hα_i
  · intro i
    have hfin : (∏ᶠ p : Primes, hilbertSym (((α i : ℚ) : ℚ_[p])) (((y : ℚ) : ℚ_[p]))) = 1 := by
      rw [finprod_congr (fun p : Primes => hilbertSym_cast_eq (α i) y),
        finprod_congr (fun p : Primes => hy i p)]
      exact hη2 i
    have hyR : hilbertSym (α i : ℝ) (y : ℝ) = 1 := by
      have hrec := hilbertReciprocity (α i : ℚ) y (by exact_mod_cast hαne i) hy0
      rw [hfin, one_mul] at hrec
      rw [hilbertSym_cast_eq (α i) y] at hrec
      exact hrec
    have hα_R : hilbertSym (α i : ℝ) (((x' * y : ℚ) : ℝ)) = εR i := by
      rw [show ((x' * y : ℚ) : ℝ) = (x' : ℝ) * (y : ℝ) by push_cast; ring,
        HasBilinHilbertSym.mul_right_eq, hyR, mul_one]
      exact hreal_eq i
    rw [hredR i (((x' * y : ℚ) : ℝ))]
    exact hα_R

-- Theorem: Serre's existence theorem (Serre III Thm 4), general case.  Given prescribed
-- local symbols `ε i p` (almost all `1`, product `εR i⁻¹`) and `εR i` at the real place,
-- all locally realisable, there is a rational `x` realising all of them.
theorem exists_rat_hilbertSym {I : Type*} [Finite I] (a : I → ℚ) (ha : ∀ i, a i ≠ 0)
    (ε : I → Primes → ℤ) (εR : I → ℤ)
    (h1 : ∀ i, {p | ε i p ≠ 1}.Finite)
    (h2 : ∀ i, (∏ᶠ p : Primes, ε i p) * εR i = 1)
    (h3 : ∀ p : Primes, ∃ x : ℚ_[p], x ≠ 0 ∧ ∀ i, hilbertSym (a i : ℚ_[p]) x = ε i p)
    (h3R : ∃ x : ℝ, x ≠ 0 ∧ ∀ i, hilbertSym (a i : ℝ) x = εR i) :
    ∃ x : ℚ, x ≠ 0 ∧ (∀ i (p : Primes), hilbertSym (a i : ℚ_[p]) x = ε i p) ∧
      ∀ i, hilbertSym (a i : ℝ) x = εR i := by
  classical
  -- Step 1: reduce `a` to squarefree integers `α`.
  have hred : ∀ i, ∃ (b : ℤ) (t : ℚ), Squarefree b ∧ t ≠ 0 ∧ a i = (b : ℚ) * t ^ 2 := by
    intro i
    obtain ⟨b, hb, t, ht, heq⟩ := exists_squarefree_mul_sq (a i) (ha i)
    exact ⟨b, t, hb, ht, heq⟩
  choose α s hp using hred
  have hsne : ∀ i, s i ≠ 0 := fun i => (hp i).2.1
  have hαeq : ∀ i, a i = (α i : ℚ) * (s i) ^ 2 := fun i => (hp i).2.2
  have hαne : ∀ i, α i ≠ 0 := by
    intro i h
    exact ha i (by rw [hαeq i, h]; simp)
  have hredp : ∀ i (p : Primes) (y : ℚ_[p]),
      hilbertSym (a i : ℚ_[p]) y = hilbertSym (α i : ℚ_[p]) y := by
    intro i p y
    have hs : (s i : ℚ_[p]) ≠ 0 := by exact_mod_cast hsne i
    have hcast : (a i : ℚ_[p]) = (α i : ℚ_[p]) * (s i : ℚ_[p]) ^ 2 := by
      rw [hαeq i]; push_cast; ring
    rw [hcast, hilbertSym_mul_sq_left hs]
  have hredR : ∀ i (y : ℝ),
      hilbertSym (a i : ℝ) y = hilbertSym (α i : ℝ) y := by
    intro i y
    have hs : (s i : ℝ) ≠ 0 := by exact_mod_cast hsne i
    have hcast : (a i : ℝ) = (α i : ℝ) * (s i : ℝ) ^ 2 := by
      rw [hαeq i]; push_cast; ring
    rw [hcast, hilbertSym_mul_sq_left hs]
  -- Step 2: local points and the real point.
  choose z hzall using h3
  have hz0 : ∀ p, z p ≠ 0 := fun p => (hzall p).1
  have hz : ∀ (p : Primes) (i : I), hilbertSym (a i : ℚ_[p]) (z p) = ε i p :=
    fun p i => (hzall p).2 i
  have hzα : ∀ (p : Primes) (i : I), hilbertSym (α i : ℚ_[p]) (z p) = ε i p :=
    fun p i => by rw [← hredp i p (z p)]; exact hz p i
  have hε : ∀ i p, ε i p = 1 ∨ ε i p = -1 := by
    intro i p
    rw [← hz p i]
    exact hilbertSym_eq_one_or_neg_one (show (a i : ℚ_[p]) ≠ 0 from by exact_mod_cast ha i)
      (hz0 p)
  obtain ⟨xR, hxR0, hxR⟩ := h3R
  have hxRα : ∀ i, hilbertSym (α i : ℝ) xR = εR i :=
    fun i => by rw [← hredR i xR]; exact hxR i
  have hεR : ∀ i, εR i = 1 ∨ εR i = -1 := by
    intro i
    rw [← hxRα i, hilbertSym_real_eq (by exact_mod_cast hαne i) hxR0]
    by_cases h : 0 < (α i : ℝ) ∨ 0 < xR
    · rw [ite_eq_left h]; exact Or.inl rfl
    · rw [ite_eq_right h]; exact Or.inr rfl
  have hsqR : ∀ i, εR i * εR i = 1 := by
    intro i
    rcases hεR i with h | h <;> rw [h] <;> norm_num
  -- The real sign to be matched by the rational approximation.
  let r : ℝ := if 0 < xR then 1 else -1
  have hr : r ≠ 0 := by
    dsimp only [r]
    by_cases h : 0 < xR <;> simp [h]
  -- Step 3: approximate at `S α` with local square classes.
  obtain ⟨x', hx'0, hsign, hsq⟩ :=
    exists_rat_local_squares (S α) ⟨⟨2, Nat.prime_two⟩, two_in_S α⟩
      (fun p : S α => z p.1) (fun p => hz0 p.1) hr
  have hreal_eq : ∀ i, hilbertSym (α i : ℝ) (x' : ℝ) = εR i := by
    intro i
    have hαR : (α i : ℝ) ≠ 0 := by exact_mod_cast hαne i
    have hx'R : (x' : ℝ) ≠ 0 := by exact_mod_cast hx'0
    have hsame : (0 < (x' : ℝ)) ↔ 0 < xR := by
      rw [← hsign]
      dsimp only [r]
      by_cases h : 0 < xR <;> simp [h]
    rw [← hxRα i, hilbertSym_real_eq hαR hx'R, hilbertSym_real_eq hαR hxR0]
    rcases lt_or_gt_of_ne hαR with hαneg | hαpos
    · by_cases hx : 0 < (x' : ℝ)
      · rw [ite_eq_left (Or.inr hx), ite_eq_left (Or.inr (hsame.mp hx))]
      · have h1 : ¬ (0 < (α i : ℝ) ∨ 0 < (x' : ℝ)) := by
          rintro (h | h)
          · exact absurd h (not_lt.mpr hαneg.le)
          · exact hx h
        have h2 : ¬ (0 < (α i : ℝ) ∨ 0 < xR) := by
          rintro (h | h)
          · exact absurd h (not_lt.mpr hαneg.le)
          · exact hx (hsame.mpr h)
        rw [ite_eq_right h1, ite_eq_right h2]
    · rw [ite_eq_left (Or.inl hαpos), ite_eq_left (Or.inl hαpos)]
  -- Step 4: the shifted prescription `η`.
  set η : I → Primes → ℤ :=
    fun i p => ε i p * hilbertSym (α i : ℚ_[p]) (x' : ℚ_[p]) with hηdef
  have hsym_fin : ∀ i, {p : Primes | hilbertSym (α i : ℚ_[p]) (x' : ℚ_[p]) ≠ 1}.Finite := by
    intro i
    refine (finite_nontrivial_hilbertSym (a := (α i : ℚ)) (b := x')
      (by exact_mod_cast hαne i) hx'0).subset ?_
    intro p hp
    rw [Set.mem_ofPred_eq] at hp
    rw [Set.mem_ofPred_eq, hilbertSym_cast_eq (α i) x']
    exact hp
  have hηε : ∀ i p, η i p = 1 ∨ η i p = -1 := by
    intro i p
    dsimp only [η]
    rcases hε i p with h | h <;>
      rcases hilbertSym_eq_one_or_neg_one
        (show (α i : ℚ_[p]) ≠ 0 from by exact_mod_cast hαne i)
        (show (x' : ℚ_[p]) ≠ 0 from by exact_mod_cast hx'0) with h' | h' <;>
      simp [h, h']
  have hη1 : ∀ i, ∀ᶠ p : Primes in cofinite, η i p = 1 := by
    intro i
    rw [Filter.eventually_cofinite]
    refine (Set.Finite.union (h1 i) (hsym_fin i)).subset ?_
    intro p hp
    simp only [Set.mem_ofPred_eq] at hp ⊢
    by_cases he : ε i p = 1
    · by_cases hx : hilbertSym (α i : ℚ_[p]) (x' : ℚ_[p]) = 1
      · exact absurd (by dsimp only [η]; simp [he, hx]) hp
      · exact Or.inr hx
    · exact Or.inl he
  have hprodε : ∀ i, (∏ᶠ p : Primes, ε i p) = εR i := by
    intro i
    have h := h2 i
    calc (∏ᶠ p : Primes, ε i p) = (∏ᶠ p : Primes, ε i p) * 1 := (mul_one _).symm
      _ = (∏ᶠ p : Primes, ε i p) * (εR i * εR i) := by rw [hsqR i]
      _ = ((∏ᶠ p : Primes, ε i p) * εR i) * εR i := by ring
      _ = εR i := by rw [h, one_mul]
  have hprodα : ∀ i, (∏ᶠ p : Primes, hilbertSym (α i : ℚ_[p]) (x' : ℚ_[p])) = εR i := by
    intro i
    have hrec := hilbertReciprocity (α i : ℚ) x' (by exact_mod_cast hαne i) hx'0
    have hfin : (∏ᶠ p : Primes, hilbertSym (((α i : ℚ) : ℚ_[p])) (((x' : ℚ) : ℚ_[p])))
        = ∏ᶠ p : Primes, hilbertSym (α i : ℚ_[p]) (x' : ℚ_[p]) :=
      finprod_congr (fun p => hilbertSym_cast_eq (α i) x')
    rw [hfin] at hrec
    have hrealR : hilbertSym (((α i : ℚ) : ℝ)) (((x' : ℚ) : ℝ)) = εR i :=
      (hilbertSym_cast_eq (α i) x').trans (hreal_eq i)
    rw [hrealR] at hrec
    calc (∏ᶠ p : Primes, hilbertSym (α i : ℚ_[p]) (x' : ℚ_[p]))
        = (∏ᶠ p : Primes, hilbertSym (α i : ℚ_[p]) (x' : ℚ_[p])) * 1 := (mul_one _).symm
      _ = (∏ᶠ p : Primes, hilbertSym (α i : ℚ_[p]) (x' : ℚ_[p])) * (εR i * εR i) := by
            rw [hsqR i]
      _ = ((∏ᶠ p : Primes, hilbertSym (α i : ℚ_[p]) (x' : ℚ_[p])) * εR i) * εR i := by ring
      _ = εR i := by rw [hrec, one_mul]
  have hη2 : ∀ i, (∏ᶠ p : Primes, η i p) = 1 := by
    intro i
    have hsplit : (∏ᶠ p : Primes, η i p)
        = (∏ᶠ p : Primes, ε i p)
          * (∏ᶠ p : Primes, hilbertSym (α i : ℚ_[p]) (x' : ℚ_[p])) := by
      rw [show (∏ᶠ p : Primes, η i p)
          = ∏ᶠ p : Primes, ε i p * hilbertSym (α i : ℚ_[p]) (x' : ℚ_[p]) from
        finprod_congr (fun p => by dsimp only [η])]
      exact finprod_mul_distrib (h1 i) (hsym_fin i)
    rw [hsplit, hprodε i, hprodα i, hsqR i]
  have hη3 : ∀ p : Primes, ∃ x : ℚ_[p], x ≠ 0 ∧ ∀ i, hilbertSym (α i : ℚ_[p]) x = η i p := by
    intro p
    refine ⟨z p * (x' : ℚ_[p]), mul_ne_zero (hz0 p) (by exact_mod_cast hx'0), fun i => ?_⟩
    rw [HasBilinHilbertSym.mul_right_eq, hzα p i]
  -- `η` is trivial on `S α`.
  have hη_S_one : ∀ i {p : Primes}, p ∈ S α → η i p = 1 := by
    intro i p hpS
    obtain ⟨c, hc⟩ := hsq p hpS
    have hc0 : c ≠ 0 := by
      rintro rfl
      have h : (x' : ℚ_[p]) = 0 := by
        have hh := hc
        rw [mul_zero] at hh
        exact (div_eq_zero_iff.mp hh).resolve_right (hz0 p)
      exact hx'0 (by exact_mod_cast h)
    have hx'eq : (x' : ℚ_[p]) = c * c * z p := by
      have hh := congrArg (fun t : ℚ_[p] => t * z p) hc
      rwa [div_mul_cancel₀ _ (hz0 p)] at hh
    have hsym : hilbertSym (α i : ℚ_[p]) (x' : ℚ_[p]) = ε i p := by
      rw [hx'eq, ← pow_two, HasBilinHilbertSym.mul_right_eq,
        hilbertSym_sq_right (by exact_mod_cast hαne i) hc0, one_mul, hzα p i]
    dsimp only [η]
    rw [hsym]
    rcases hε i p with h | h <;> rw [h] <;> norm_num
  -- `A` is coprime to `M`, so Dirichlet supplies the auxiliary prime `ℓ`.
  have hcop : Nat.Coprime (A hηε hη1) (M α) := by
    have hAnot : ∀ {p : Primes}, p ∈ S α → ¬ (p : ℕ) ∣ A hηε hη1 := by
      intro p hpS
      exact not_dvd_A_of_notMem_T hηε hη1
        ((ep_eq_one_iff_not_mem_T hηε hη1 p).mpr (fun i => hη_S_one i hpS))
    have hc4 : Nat.Coprime (A hηε hη1) 4 := by
      have h2' : ¬ 2 ∣ A hηε hη1 := by
        have := hAnot (two_in_S α)
        simpa using this
      have hc2 : Nat.Coprime (A hηε hη1) 2 :=
        ((Nat.prime_two.coprime_iff_not_dvd).mpr h2').symm
      simpa using hc2.pow_right 2
    have hcS : Nat.Coprime (A hηε hη1) (∏ q ∈ S α, (q : ℕ)) :=
      Nat.Coprime.prod_right fun q hq =>
        ((q.2.coprime_iff_not_dvd).mpr (hAnot hq)).symm
    rw [M]
    exact hc4.mul_right hcS
  obtain ⟨ℓ, hℓn, hℓ, hℓA⟩ :=
    Nat.forall_exists_prime_gt_and_modEq
      ((S α ∪ T hηε hη1).sup (fun q => (q : ℕ))) (M_ne_zero α) hcop
  have hℓgt : ∀ q ∈ S α ∪ T hηε hη1, (q : ℕ) < ℓ := fun q hq =>
    lt_of_le_of_lt (Finset.le_sup (f := fun q : Primes => (q : ℕ)) hq) hℓn
  -- Step 5: apply the disjoint case.
  exact combine_disjoint_solution a α hαne ε εR η x' hx'0
    (fun i p => by dsimp only [η]) hηε hη1 hη2 hη3 hℓ hℓA hℓgt hreal_eq hredp hredR

end Existence

end HasseMinkowski
