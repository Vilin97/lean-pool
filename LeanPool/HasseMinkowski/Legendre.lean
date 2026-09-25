/-
Copyright (c) 2026 jayyswan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: jayyswan
-/
module

public import LeanPool.HasseMinkowski.HilbertSymbol.Norm
public import LeanPool.HasseMinkowski.HilbertSymbol.Padic
public import LeanPool.HasseMinkowski.HilbertSymbol.Real
public import LeanPool.HasseMinkowski.RankThree
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.Data.Nat.ChineseRemainder
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Tactic

/-!
# WP1 1.1 — norm transfer for the Hilbert symbol

The Hilbert symbol `(a, b)_k` depends on `b` only through its class in `kˣ / kˣ²`, but in the
form used later (the descent in the proof of quadratic reciprocity) the input is not a square
multiple of `b` but a *norm* from `k(√a)`: we are handed `t` with `t ^ 2 - a = b * b'`.

Geometrically, `t + √a` has norm `t ^ 2 - a = b * b'` in `k(√a)`, so if `b` is a norm then so is
`b'` (divide the norm identity by `b`), and conversely. Since a nonzero nonsquare `a` satisfies
`(b, a)_k = 1` exactly when `b` is a norm from `k(√a)`, the two symbols agree.
-/

@[expose] public section

namespace HasseMinkowski

attribute [local instance] Classical.propDecidable
open Module

/-- If `t ^ 2 - a = b * b'` with `b` and `b'` nonzero, then `(a, b)_k = (a, b')_k`: the two
second arguments differ by the norm of `t + √a` in `k(√a)`, and being a norm from `k(√a)` is
invariant under multiplication by a square class, in particular under `b ↦ (t² - a) / b`. -/
-- Theorem: if `t ^ 2 - a = b * b'` with `b`, `b'` nonzero, then `(a,b)_k = (a,b')_k`.
theorem hilbertSym_eq_of_sq_sub_eq_mul {k : Type*} [Field k]
    {a b b' t : k} (hb : b ≠ 0) (hb' : b' ≠ 0) (h : t ^ 2 - a = b * b') :
    hilbertSym a b = hilbertSym a b' := by
  -- If `b` is a norm from `k(√a)` then so is `b'`, and vice versa.
  have aux : ∀ c c' : k, c ≠ 0 → c' ≠ 0 → t ^ 2 - a = c * c' →
      (∃ u : QuadraticAlgebra k a 0, c = u.norm) →
      ∃ u : QuadraticAlgebra k a 0, c' = u.norm := by
    intro c c' hc hc' hcc' ⟨u, hu⟩
    refine ⟨algebraMap k (QuadraticAlgebra k a 0) c⁻¹ * (⟨t, 1⟩ * star u), ?_⟩
    have hw : (⟨t, 1⟩ : QuadraticAlgebra k a 0).norm = c * c' := by
      simp [QuadraticAlgebra.norm_def]
      linear_combination hcc'
    simp only [map_mul, QuadraticAlgebra.norm_algebraMap, QuadraticAlgebra.norm_star, hw, ← hu]
    field_simp
  by_cases ha : a = 0
  · rw [ha]
    simp [hilbertSym_zero_left]
  · by_cases hsq : IsSquare a
    · -- `a` is a nonzero square, so both symbols are `1`.
      rcases hsq with ⟨s, hs⟩
      have h1 : hilbertSym a b = 1 := by
        refine hilbertSym_eq_one_of_sol ha hb ⟨s, 1, 0, by simp, ?_⟩
        rw [hs]
        ring
      have h2 : hilbertSym a b' = 1 := by
        refine hilbertSym_eq_one_of_sol ha hb' ⟨s, 1, 0, by simp, ?_⟩
        rw [hs]
        ring
      rw [h1, h2]
    · -- Main case: `a` is a nonzero nonsquare; use the norm characterization.
      rw [hilbertSym_comm a b, hilbertSym_comm a b']
      have hiff1 := hilbertSym_eq_one_iff_isNorm (a := b) (b := a) hb ha hsq
      have hiff2 := hilbertSym_eq_one_iff_isNorm (a := b') (b := a) hb' ha hsq
      have key : (∃ u : QuadraticAlgebra k a 0, b = u.norm) ↔
          (∃ u : QuadraticAlgebra k a 0, b' = u.norm) :=
        ⟨aux b b' hb hb' h, aux b' b hb' hb (h.trans (mul_comm b b'))⟩
      have hiff : (hilbertSym b a = 1) ↔ (hilbertSym b' a = 1) := by
        rw [hiff1, hiff2]
        exact key
      have hb0 : hilbertSym b a ≠ 0 := by
        intro hc
        rw [hilbertSym_eq_zero_iff] at hc
        exact hc.elim hb ha
      have hb'0 : hilbertSym b' a ≠ 0 := by
        intro hc
        rw [hilbertSym_eq_zero_iff] at hc
        exact hc.elim hb' ha
      rcases hilbertSym_eq_one_or b a with h1 | h0 | hm1
      · rcases hilbertSym_eq_one_or b' a with h2 | h02 | hm2
        · rw [h1, h2]
        · exact absurd h02 hb'0
        · exact absurd (hiff.mp h1) (by rw [hm2]; norm_num)
      · exact absurd h0 hb0
      · rcases hilbertSym_eq_one_or b' a with h2 | h02 | hm2
        · exact absurd (hiff.mpr h2) (by rw [hm1]; norm_num)
        · exact absurd h02 hb'0
        · rw [hm1, hm2]

/-! ### WP1 1.4 — the squarefree normal form

Every nonzero integer is a squarefree integer times a nonzero square, and the same holds for
every nonzero rational after clearing denominators. -/

/-- Every nonzero integer is a squarefree integer times a nonzero square. -/
-- Theorem: nonzero integer normal form `n = m * u ^ 2` with `m` squarefree and `u ≠ 0`.
theorem exists_squarefree_mul_sq_int (n : ℤ) (hn : n ≠ 0) :
    ∃ m u : ℤ, Squarefree m ∧ u ≠ 0 ∧ n = m * u ^ 2 := by
  obtain ⟨b, a, hba, hsf⟩ := exists_sq_mul_squarefree n.natAbs
  have hb : b ≠ 0 := by
    rintro rfl
    simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul] at hba
    exact Int.natAbs_ne_zero.mpr hn hba.symm
  have hbZ : (b : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hb
  have hbaZ : (b : ℤ) ^ 2 * (a : ℤ) = (n.natAbs : ℤ) := by exact_mod_cast hba
  rcases lt_trichotomy n 0 with hneg | hzero | hpos
  · have hsfZneg : Squarefree (-(a : ℤ)) := by
      rw [← Int.squarefree_natAbs]
      simpa using hsf
    refine ⟨-(a : ℤ), (b : ℤ), hsfZneg, hbZ, ?_⟩
    have hthis : n = -(n.natAbs : ℤ) := by
      rw [Int.natCast_natAbs, abs_of_neg hneg]
      ring
    rw [hthis, ← hbaZ]
    ring
  · exact absurd hzero hn
  · have hsfZ : Squarefree (a : ℤ) := by simpa using hsf
    refine ⟨(a : ℤ), (b : ℤ), hsfZ, hbZ, ?_⟩
    have hthis : n = (n.natAbs : ℤ) := by
      rw [Int.natCast_natAbs, abs_of_nonneg (le_of_lt hpos)]
    rw [hthis, ← hbaZ]
    ring

/-- Every nonzero rational is a squarefree integer times a nonzero square. -/
-- Theorem: nonzero rational normal form `A = a * s ^ 2` with `a : ℤ` squarefree and `s ≠ 0`.
theorem exists_squarefree_mul_sq (A : ℚ) (hA : A ≠ 0) :
    ∃ a : ℤ, Squarefree a ∧ ∃ s : ℚ, s ≠ 0 ∧ A = a * s ^ 2 := by
  set u : ℕ := A.num.natAbs with hu_def
  set v : ℕ := A.den with hv_def
  have hu : 0 < u := by
    rw [hu_def]
    exact Int.natAbs_pos.mpr (Rat.num_ne_zero.mpr hA)
  have hv : 0 < v := by
    rw [hv_def]
    exact Nat.pos_of_ne_zero A.den_ne_zero
  obtain ⟨a, b, -, hb, hba, hsf⟩ := Nat.sq_mul_squarefree_of_pos (Nat.mul_pos hu hv)
  have hbne : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hb.ne'
  have hvne : (v : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hv.ne'
  have hs : (b : ℚ) / (v : ℚ) ≠ 0 := div_ne_zero hbne hvne
  have habs : |A| = (u : ℚ) / (v : ℚ) := by
    rw [Rat.abs_def, ← hu_def, ← hv_def, Rat.divInt_eq_div]
    norm_num
  have h1 : (b : ℚ) ^ 2 * (a : ℚ) = (u : ℚ) * (v : ℚ) := by exact_mod_cast hba
  have hfrac : (u : ℚ) / (v : ℚ) = (a : ℚ) * ((b : ℚ) / (v : ℚ)) ^ 2 := by
    field_simp
    nlinarith [h1]
  by_cases hneg : A < 0
  · refine ⟨-(a : ℤ), ?_, (b : ℚ) / (v : ℚ), hs, ?_⟩
    · rw [← Int.squarefree_natAbs]
      simpa using hsf
    · have hA' : A = -((u : ℚ) / (v : ℚ)) := by
        rw [abs_of_neg hneg] at habs
        rw [← habs]
        ring
      rw [hA', hfrac]
      push_cast
      ring
  · have hnonneg : 0 ≤ A := le_of_not_gt hneg
    refine ⟨(a : ℤ), by simpa using hsf, (b : ℚ) / (v : ℚ), hs, ?_⟩
    · rw [abs_of_nonneg hnonneg] at habs
      rw [habs, hfrac]
      push_cast
      ring

/-! ### WP1 1.3 — combining the local congruences by CRT

If `t ^ 2 ≡ a (mod p)` is solvable for every prime `p ∣ b` with `b` squarefree, then it is
solvable modulo `b`, and the solution can be chosen in the balanced range `2 |t| ≤ |b|`.
The balanced representative is `Int.bmod`, which preserves the congruence and satisfies the
bound. -/

/-- **CRT plus a size bound.** For squarefree `b`, if `t ^ 2 - a` is divisible by every prime
factor of `b`, then some residue class `t` satisfies `b ∣ t ^ 2 - a` and `2 * |t| ≤ |b|`. -/
-- Theorem: local square-mod-`p` data for all `p ∣ b` combine to `b ∣ t ^ 2 - a` with
-- `2 * |t| ≤ |b|`.
theorem exists_sq_mod_squarefree (a b : ℤ) (hb : Squarefree b)
    (h : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ b → ∃ t : ℤ, (p : ℤ) ∣ t ^ 2 - a) :
    ∃ t : ℤ, b ∣ t ^ 2 - a ∧ 2 * |t| ≤ |b| := by
  classical
  have hb0 : b ≠ 0 := hb.ne_zero
  set m : ℕ := b.natAbs with hm_def
  have hmpos : 0 < m := by rw [hm_def]; exact Int.natAbs_pos.mpr hb0
  have hsfm : Squarefree m := by rw [hm_def]; exact Int.squarefree_natAbs.mpr hb
  -- a chosen witness for every prime dividing `b`
  let w : ℕ → ℤ :=
    fun p => if hp : p.Prime ∧ (p : ℤ) ∣ b then (h p hp.1 hp.2).choose else 0
  have hw : ∀ (p : ℕ) (hp : p.Prime) (hpb : (p : ℤ) ∣ b), (p : ℤ) ∣ (w p) ^ 2 - a := by
    intro p hp hpb
    have hcond : p.Prime ∧ (p : ℤ) ∣ b := ⟨hp, hpb⟩
    simp only [w, dite_eq_left hcond]
    exact (h p hp hpb).choose_spec
  -- the nonnegative residues used by the Chinese remainder theorem
  let A : ℕ → ℕ := fun p => ((w p) % (p : ℤ)).toNat
  have hAeq : ∀ {p : ℕ} (hp : p ≠ 0), (A p : ℤ) = w p % (p : ℤ) := by
    intro p hp
    exact Int.toNat_of_nonneg (Int.emod_nonneg (w p) (by exact_mod_cast hp))
  have hAdvd : ∀ {p : ℕ} (hp : p ≠ 0), (p : ℤ) ∣ (A p : ℤ) - w p := by
    intro p hp
    rw [hAeq hp]
    exact Int.dvd_emod_sub_self
  have hcop : (m.primeFactors : Set ℕ).Pairwise (fun p q => Nat.Coprime p q) := by
    intro p hp q hq hpq
    exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
      (Nat.prime_of_mem_primeFactors hq)).mpr hpq
  obtain ⟨k, hk⟩ := Nat.chineseRemainderOfFinset A (fun p => p) m.primeFactors
    (fun p hp => (Nat.prime_of_mem_primeFactors hp).ne_zero) hcop
  -- each prime factor of `m` divides `k ^ 2 - a`
  have hprime : ∀ p ∈ m.primeFactors, (p : ℤ) ∣ (k : ℤ) ^ 2 - a := by
    intro p hpS
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hpS
    have hpb : (p : ℤ) ∣ b := by
      rw [← Int.natAbs_dvd_natAbs, Int.natAbs_natCast]
      simpa [← hm_def] using Nat.dvd_of_mem_primeFactors hpS
    have hkp : (p : ℤ) ∣ (k : ℤ) - (A p : ℤ) := by
      have h' : (p : ℤ) ∣ (A p : ℤ) - (k : ℤ) := Nat.modEq_iff_dvd.mp (hk p hpS)
      have he : (k : ℤ) - (A p : ℤ) = -((A p : ℤ) - (k : ℤ)) := by ring
      rw [he]
      exact dvd_neg.mpr h'
    have hsq1 : (p : ℤ) ∣ (k : ℤ) ^ 2 - (A p : ℤ) ^ 2 := by
      have he : (k : ℤ) ^ 2 - (A p : ℤ) ^ 2
          = ((k : ℤ) - (A p : ℤ)) * ((k : ℤ) + (A p : ℤ)) := by ring
      rw [he]
      exact hkp.mul_right _
    have hsq2 : (p : ℤ) ∣ (A p : ℤ) ^ 2 - (w p) ^ 2 := by
      have h' : (p : ℤ) ∣ (A p : ℤ) - w p := hAdvd hpp.ne_zero
      have he : (A p : ℤ) ^ 2 - (w p) ^ 2
          = ((A p : ℤ) - w p) * ((A p : ℤ) + w p) := by ring
      rw [he]
      exact h'.mul_right _
    have hsq3 : (p : ℤ) ∣ (w p) ^ 2 - a := hw p hpp hpb
    have hsum : (p : ℤ) ∣ ((k : ℤ) ^ 2 - (A p : ℤ) ^ 2)
        + ((A p : ℤ) ^ 2 - (w p) ^ 2) + ((w p) ^ 2 - a) :=
      dvd_add (dvd_add hsq1 hsq2) hsq3
    have he : ((k : ℤ) ^ 2 - (A p : ℤ) ^ 2) + ((A p : ℤ) ^ 2 - (w p) ^ 2)
        + ((w p) ^ 2 - a) = (k : ℤ) ^ 2 - a := by ring
    rwa [he] at hsum
  -- the product of the prime factors of `m` is `m`, and divides `k ^ 2 - a`
  have hprod : (∏ p ∈ m.primeFactors, (p : ℤ)) ∣ (k : ℤ) ^ 2 - a := by
    refine Finset.prod_dvd_of_coprime ?_ ?_
    · intro p hp q hq hpq
      exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
        (Nat.prime_of_mem_primeFactors hq)).mpr hpq |>.cast
    · exact hprime
  have hprod_eq : (∏ p ∈ m.primeFactors, (p : ℤ)) = (m : ℤ) := by
    have hcast : (∏ p ∈ m.primeFactors, (p : ℤ))
        = ((∏ p ∈ m.primeFactors, p : ℕ) : ℤ) := by
      push_cast
      rfl
    rw [hcast, Nat.prod_primeFactors_of_squarefree hsfm]
  have hmdvd : (m : ℤ) ∣ (k : ℤ) ^ 2 - a := by
    rwa [hprod_eq] at hprod
  -- balance `k` with `Int.bmod`
  refine ⟨Int.bmod (k : ℤ) m, ?_, ?_⟩
  · have ht : (m : ℤ) ∣ (Int.bmod (k : ℤ) m) ^ 2 - (k : ℤ) ^ 2 := by
      have h1 : (m : ℤ) ∣ Int.bmod (k : ℤ) m - (k : ℤ) := Int.dvd_bmod_sub_self
      have he : (Int.bmod (k : ℤ) m) ^ 2 - (k : ℤ) ^ 2
          = (Int.bmod (k : ℤ) m - (k : ℤ)) * (Int.bmod (k : ℤ) m + (k : ℤ)) := by ring
      rw [he]
      exact h1.mul_right _
    have hsum : (m : ℤ) ∣ (Int.bmod (k : ℤ) m) ^ 2 - a := by
      have hs := dvd_add ht hmdvd
      have he : ((Int.bmod (k : ℤ) m) ^ 2 - (k : ℤ) ^ 2) + ((k : ℤ) ^ 2 - a)
          = (Int.bmod (k : ℤ) m) ^ 2 - a := by ring
      rwa [he] at hs
    have hmb : (m : ℤ) = |b| := by
      rw [hm_def]
      exact Int.natCast_natAbs b
    rw [hmb] at hsum
    exact (abs_dvd b _).mp hsum
  · have h1 : Int.bmod (k : ℤ) m ≤ ((m : ℤ) - 1) / 2 := Int.bmod_le hmpos
    have h2 : -((m : ℤ) / 2) ≤ Int.bmod (k : ℤ) m := Int.le_bmod hmpos
    have habs : |Int.bmod (k : ℤ) m| ≤ (m : ℤ) / 2 := by
      rw [abs_le]
      refine ⟨h2, ?_⟩
      have hle : ((m : ℤ) - 1) / 2 ≤ (m : ℤ) / 2 := by omega
      exact le_trans h1 hle
    have h2m : 2 * ((m : ℤ) / 2) ≤ (m : ℤ) := by omega
    have hfin : 2 * |Int.bmod (k : ℤ) m| ≤ (m : ℤ) := by linarith
    rw [show |b| = (m : ℤ) by rw [hm_def]; exact (Int.natCast_natAbs b).symm]
    exact hfin

/-! ### WP1 1.2 — the local symbol being `1` forces a square residue

If `(a, b)_p = 1`, `b` is squarefree and `p ∣ b`, then `a` is a square modulo `p`. The case
`p ∣ a` is trivial (`t = 0`), and `p = 2` follows from `a ^ 2 ≡ a (mod 2)` (`t = a`). For odd
`p` with `p ∤ a`, the integer `b` has `p`-adic valuation `1` (squarefree plus `p ∣ b`), so
its norm is `p⁻¹`, while `p ∤ a` makes `a` a unit of `ℤ_[p]`. Serre's case `10` formula then
reads
`(a, b)_p = (a / p)`, the quadratic character of `a`; being `1` it says `a` is a square mod `p`,
and that square lifts back to an integer `t` with `p ∣ t ^ 2 - a`. -/

/-- **Local square residue.** If the local Hilbert symbol `(a, b)_p` equals `1` for a squarefree
`b` divisible by `p`, then `a ≡ t ^ 2 (mod p)` for some integer `t`. -/
-- Theorem: `(a,b)_p = 1` for `p ∣ b` squarefree implies `∃ t : ℤ, p ∣ t ^ 2 - a`.
theorem exists_sq_mod_of_hilbertSym (a b : ℤ) (hb : Squarefree b) (p : ℕ) [Fact p.Prime]
    (hpb : (p : ℤ) ∣ b) (h : hilbertSym (a : ℚ_[p]) (b : ℚ_[p]) = 1) :
    ∃ t : ℤ, (p : ℤ) ∣ t ^ 2 - a := by
  have hp : p.Prime := Fact.out
  by_cases hpa : (p : ℤ) ∣ a
  · exact ⟨0, by simpa using (dvd_neg.mpr hpa)⟩
  by_cases hp2 : p = 2
  · refine ⟨a, ?_⟩
    rw [hp2]
    have hz : (((a ^ 2 - a : ℤ)) : ZMod 2) = 0 := by
      push_cast
      exact (show ∀ x : ZMod 2, x ^ 2 - x = 0 by decide) _
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (a := a ^ 2 - a) (b := 2)).mp hz
  · have hb0 : b ≠ 0 := hb.ne_zero
    have ha0 : a ≠ 0 := fun h0 => hpa (by rw [h0]; exact dvd_zero _)
    have hbQ : (b : ℚ_[p]) ≠ 0 := by exact_mod_cast hb0
    -- `b` has `p`-adic valuation `1`, hence norm `p⁻¹`
    have hsfnat : Squarefree b.natAbs := Int.squarefree_natAbs.mpr hb
    have hnotsq : ¬ (p : ℤ) ^ 2 ∣ b := by
      intro hd
      have hd' : p ^ 2 ∣ b.natAbs := by
        have h'' := (Int.natAbs_dvd_natAbs (a := (p : ℤ) ^ 2) (b := b)).mpr hd
        simpa using h''
      exact (Nat.squarefree_iff_prime_squarefree.mp hsfnat p hp) (by simpa [pow_two] using hd')
    have hv1 : 1 ≤ padicValInt p b := by
      rcases (padicValInt_dvd_iff (p := p) 1 b).mp (by simpa using hpb) with h' | h'
      · exact absurd h' hb0
      · exact h'
    have hv2 : padicValInt p b < 2 := by
      by_contra hcon
      push Not at hcon
      exact hnotsq ((padicValInt_dvd_iff (p := p) 2 b).mpr (Or.inr hcon))
    have hnorm : ‖((b : ℤ) : ℚ_[p])‖ = (p : ℝ)⁻¹ := by
      have h1 := Padic.norm_eq_zpow_neg_valuation (p := p) hbQ
      rw [Padic.valuation_intCast] at h1
      have hv : padicValInt p b = 1 := by omega
      rw [hv] at h1
      simpa using h1
    -- `a` is a unit of `ℤ_[p]`
    have hunit : IsUnit ((a : ℤ_[p])) := by
      rw [PadicInt.isUnit_iff]
      refine le_antisymm (PadicInt.norm_le_one _) ?_
      rw [← not_lt]
      intro hlt
      exact hpa ((PadicInt.norm_intCast_lt_one_iff).mp hlt)
    let u : ℤ_[p]ˣ := hunit.unit
    have hu : (u : ℚ_[p]) = (a : ℚ_[p]) :=
      congrArg (fun z : ℤ_[p] => (z : ℚ_[p])) (IsUnit.unit_spec hunit)
    -- Serre's case `10`
    have hcase : hilbertSym (a : ℚ_[p]) (b : ℚ_[p])
        = (quadraticChar (ZMod p)) (PadicInt.toZMod (u : ℤ_[p])) := by
      have hc := hilbertSym_padic_odd_case10 (p := p) hp2 u hnorm
      rwa [hu] at hc
    have hchi : (quadraticChar (ZMod p)) (PadicInt.toZMod (u : ℤ_[p])) = 1 := by
      rw [← hcase]
      exact h
    have hu0 : PadicInt.toZMod (u : ℤ_[p]) ≠ 0 :=
      (IsUnit.map (PadicInt.toZMod (p := p)) u.isUnit).ne_zero
    obtain ⟨s, hs⟩ := (quadraticChar_one_iff_isSquare hu0).mp hchi
    -- identify `toZMod u` with the residue of `a`
    have huZ : (u : ℤ_[p]) = (a : ℤ_[p]) :=
      Subtype.coe_injective (by simpa using hu)
    rw [huZ] at hs
    have hsa : ((a : ℤ) : ZMod p) = s * s := by simpa using hs
    obtain ⟨t, ht⟩ := ZMod.intCast_surjective s
    refine ⟨t, ?_⟩
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ht]
    have hs2 : s ^ 2 = ((a : ℤ) : ZMod p) := by rw [sq, hsa]
    rw [hs2]
    ring

/-! ### WP1 1.5 — the integral descent (Legendre's theorem)

The local–global principle for the Hilbert symbol at the integral place (Serre, Cours
d'arithmétique, IV §3.2, Theorem 8): for squarefree integers `a`, `b`, if `(a, b)_v = 1` at
every place `v` — every prime and the real place — then `(a, b)_ℚ = 1`. The argument is an
elementary descent on
`|a| + |b|`: by symmetry assume `|a| ≤ |b|`; for `|b| ≤ 1` all cases are immediate, while for
`|b| ≥ 2` CRT (`exists_sq_mod_squarefree`) produces `t` with `t ^ 2 ≡ a (mod b)`, the size bound
`2|t| ≤ |b|` makes `b' = (t ^ 2 - a) / b` strictly smaller than `b`, the norm-transfer lemma
`hilbertSym_eq_of_sq_sub_eq_mul` moves every local hypothesis from `b` to `b'`, and stripping the
square class of `b'` (`exists_squarefree_mul_sq_int`) lets the induction hypothesis finish. -/

-- Lemma: the base case `b.natAbs ≤ 1` of the integral descent, where `a, b ∈ {±1}`.
private lemma legendre_int_base (a b : ℤ) (ha : Squarefree a) (hb : Squarefree b)
    (hr : hilbertSym (a : ℝ) (b : ℝ) = 1) (hle : a.natAbs ≤ b.natAbs)
    (hbase : b.natAbs ≤ 1) :
    hilbertSym (a : ℚ) (b : ℚ) = 1 := by
  have ha_cases : a = 1 ∨ a = -1 := by
    have h1 : a.natAbs = 1 := by
      have := Int.natAbs_pos.mpr ha.ne_zero
      omega
    rcases Int.natAbs_eq a with h | h
    · left; rw [h, h1]; norm_num
    · right; rw [h, h1]; norm_num
  have hb_cases : b = 1 ∨ b = -1 := by
    have h1 : b.natAbs = 1 := by
      have := Int.natAbs_pos.mpr hb.ne_zero
      omega
    rcases Int.natAbs_eq b with h | h
    · left; rw [h, h1]; norm_num
    · right; rw [h, h1]; norm_num
  rcases ha_cases with rfl | rfl <;> rcases hb_cases with rfl | rfl
  · simpa using hilbertSym_sq_left (k := ℚ) (a := (1 : ℚ)) (b := (1 : ℚ))
      (by norm_num) (by norm_num)
  · simpa using hilbertSym_sq_left (k := ℚ) (a := (1 : ℚ)) (b := (-1 : ℚ))
      (by norm_num) (by norm_num)
  · simpa using hilbertSym_sq_right (k := ℚ) (a := (-1 : ℚ)) (b := (1 : ℚ))
      (by norm_num) (by norm_num)
  · exfalso
    have hreal := hilbertSym_real_eq (a := ((-1 : ℤ) : ℝ)) (b := ((-1 : ℤ) : ℝ))
      (by norm_num) (by norm_num)
    rw [ite_eq_right (by norm_num :
      ¬ (0 < ((-1 : ℤ) : ℝ) ∨ 0 < ((-1 : ℤ) : ℝ)))] at hreal
    rw [hreal] at hr
    norm_num at hr

/-- **Integral descent.** If the Hilbert symbol `(a, b)_v` equals `1` at every finite place and
at the real place, for squarefree integers `a`, `b`, then `(a, b)_ℚ = 1`. -/
-- Theorem: squarefree `a`, `b` with `(a,b)_v = 1` for all `v` have
-- `hilbertSym (a:ℚ) (b:ℚ) = 1`.
theorem legendre_int (a b : ℤ) (ha : Squarefree a) (hb : Squarefree b)
    (hp : ∀ (p : ℕ) [Fact (Nat.Prime p)], hilbertSym (a : ℚ_[p]) (b : ℚ_[p]) = 1)
    (hr : hilbertSym (a : ℝ) (b : ℝ) = 1) : hilbertSym (a : ℚ) (b : ℚ) = 1 := by
  have H : ∀ n : ℕ, (∀ a b : ℤ, a.natAbs + b.natAbs = n →
      Squarefree a → Squarefree b →
      (∀ (p : ℕ) [Fact (Nat.Prime p)], hilbertSym (a : ℚ_[p]) (b : ℚ_[p]) = 1) →
      hilbertSym (a : ℝ) (b : ℝ) = 1 → hilbertSym (a : ℚ) (b : ℚ) = 1) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro a b hab ha hb hp hr
      -- the descent for a pair normalized by `a.natAbs ≤ b.natAbs`
      have main : ∀ a b : ℤ, a.natAbs + b.natAbs = n → a.natAbs ≤ b.natAbs →
          Squarefree a → Squarefree b →
          (∀ (p : ℕ) [Fact (Nat.Prime p)], hilbertSym (a : ℚ_[p]) (b : ℚ_[p]) = 1) →
          hilbertSym (a : ℝ) (b : ℝ) = 1 → hilbertSym (a : ℚ) (b : ℚ) = 1 := by
        intro a b hab hle ha hb hp hr
        by_cases hbase : b.natAbs ≤ 1
        · exact legendre_int_base a b ha hb hr hle hbase
        · -- step: `2 ≤ b.natAbs`
          have hb2 : 2 ≤ b.natAbs := by omega
          have hbne : b ≠ 0 := hb.ne_zero
          have ha0 : a ≠ 0 := ha.ne_zero
          have hloc : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ b →
              ∃ t : ℤ, (p : ℤ) ∣ t ^ 2 - a := by
            intro p hpp hpb
            have : Fact (Nat.Prime p) := ⟨hpp⟩
            exact exists_sq_mod_of_hilbertSym a b hb p hpb (hp p)
          obtain ⟨t, hb_dvd, htsize⟩ := exists_sq_mod_squarefree a b hb hloc
          by_cases htsq : t ^ 2 = a
          · -- `a` is a square
            have haQ : (a : ℚ) ≠ 0 := by exact_mod_cast ha0
            have hbQ : (b : ℚ) ≠ 0 := by exact_mod_cast hbne
            refine hilbertSym_eq_one_of_sol haQ hbQ ⟨(t : ℚ), 1, 0, by simp, ?_⟩
            have ht : ((t : ℚ)) ^ 2 = (a : ℚ) := by exact_mod_cast htsq
            rw [ht]
            ring
          · -- descent
            let b' : ℤ := (t ^ 2 - a) / b
            have hb'mul : b' * b = t ^ 2 - a := Int.ediv_mul_cancel hb_dvd
            have hb'ne : b' ≠ 0 := by
              intro h
              apply htsq
              have h' := hb'mul
              rw [h, zero_mul] at h'
              exact sub_eq_zero.mp h'.symm
            -- the strict size bound `|b'| < |b|`
            have hBpos : 0 < b.natAbs := by omega
            have hnum : (t ^ 2 - a).natAbs ≤ t.natAbs ^ 2 + a.natAbs := by
              have h1 : |t ^ 2 - a| ≤ |t| ^ 2 + |a| := by
                calc |t ^ 2 - a| = |t ^ 2 + -a| := by ring_nf
                  _ ≤ |t ^ 2| + |-a| := abs_add_le _ _
                  _ = |t| ^ 2 + |a| := by rw [abs_neg, abs_pow]
              have h1Z : (((t ^ 2 - a).natAbs : ℤ)) ≤
                  ((t.natAbs : ℤ)) ^ 2 + (a.natAbs : ℤ) := by
                calc ((t ^ 2 - a).natAbs : ℤ) = |t ^ 2 - a| := Int.natCast_natAbs _
                  _ ≤ |t| ^ 2 + |a| := h1
                  _ = ((t.natAbs : ℤ)) ^ 2 + (a.natAbs : ℤ) := by
                      rw [Int.natCast_natAbs, Int.natCast_natAbs]
              exact_mod_cast h1Z
            have htbZ : (2 : ℤ) * (t.natAbs : ℤ) ≤ (b.natAbs : ℤ) := by
              simpa only [Int.natCast_natAbs] using htsize
            have hleZ : ((a.natAbs : ℤ)) ≤ ((b.natAbs : ℤ)) := by exact_mod_cast hle
            have hb2Z : (2 : ℤ) ≤ ((b.natAbs : ℤ)) := by exact_mod_cast hb2
            have hstrictZ :
                ((t.natAbs : ℤ)) ^ 2 + (a.natAbs : ℤ) < ((b.natAbs : ℤ)) ^ 2 := by
              have h4T : 4 * ((t.natAbs : ℤ)) ^ 2 ≤ ((b.natAbs : ℤ)) ^ 2 := by
                have h := pow_le_pow_left₀ (show (0 : ℤ) ≤ 2 * (t.natAbs : ℤ) by positivity)
                  htbZ 2
                nlinarith [h]
              have hkey : 4 * (((t.natAbs : ℤ)) ^ 2 + (a.natAbs : ℤ))
                  < 4 * ((b.natAbs : ℤ)) ^ 2 := by nlinarith [h4T, hleZ, hb2Z]
              nlinarith [hkey]
            have hstrict : t.natAbs ^ 2 + a.natAbs < b.natAbs ^ 2 := by
              exact_mod_cast hstrictZ
            have hsmallnum : (t ^ 2 - a).natAbs < b.natAbs ^ 2 := lt_of_le_of_lt hnum hstrict
            have hnat : b'.natAbs * b.natAbs = (t ^ 2 - a).natAbs := by
              rw [← Int.natAbs_mul, hb'mul]
            have hb'lt : b'.natAbs < b.natAbs := by
              have hltmul : b.natAbs * b'.natAbs < b.natAbs * b.natAbs := by
                rw [mul_comm b.natAbs b'.natAbs, hnat]
                exact lt_of_lt_of_eq hsmallnum (by ring)
              exact (Nat.mul_lt_mul_left hBpos).mp hltmul
            obtain ⟨b'', u, hb''sf, hu_ne, hb'eq⟩ := exists_squarefree_mul_sq_int b' hb'ne
            have hsmall : a.natAbs + b''.natAbs < n := by
              have heq : b'.natAbs = b''.natAbs * u.natAbs ^ 2 := by
                rw [hb'eq, Int.natAbs_mul, Int.natAbs_pow]
              have hu2 : 0 < u.natAbs ^ 2 := by
                have : 0 < u.natAbs := Int.natAbs_pos.mpr hu_ne
                positivity
              have hle'' : b''.natAbs ≤ b'.natAbs := by
                rw [heq]
                calc b''.natAbs = b''.natAbs * 1 := (mul_one _).symm
                  _ ≤ b''.natAbs * u.natAbs ^ 2 := Nat.mul_le_mul_left _ hu2
              omega
            -- transfer the local hypotheses to `(a, b'')`
            have hp'' : ∀ (p : ℕ) [Fact (Nat.Prime p)],
                hilbertSym (a : ℚ_[p]) (b'' : ℚ_[p]) = 1 := by
              intro p hpinst
              have : Fact (Nat.Prime p) := hpinst
              have h2p : Invertible (2 : ℚ_[p]) :=
                invertibleOfNonzero (by exact_mod_cast (show (2 : ℤ) ≠ 0 by norm_num))
              have hbQp : (b : ℚ_[p]) ≠ 0 := by exact_mod_cast hbne
              have hb'Qp : (b' : ℚ_[p]) ≠ 0 := by exact_mod_cast hb'ne
              have hcast : ((t : ℚ_[p])) ^ 2 - (a : ℚ_[p])
                  = (b : ℚ_[p]) * (b' : ℚ_[p]) := by
                have h := congrArg (fun z : ℤ => (z : ℚ_[p])) hb'mul.symm
                push_cast at h
                rwa [mul_comm] at h
              have heqp : hilbertSym (a : ℚ_[p]) (b : ℚ_[p])
                  = hilbertSym (a : ℚ_[p]) (b' : ℚ_[p]) :=
                hilbertSym_eq_of_sq_sub_eq_mul hbQp hb'Qp hcast
              have huQp : (u : ℚ_[p]) ≠ 0 := by exact_mod_cast hu_ne
              have hb'fac : (b' : ℚ_[p]) = (b'' : ℚ_[p]) * (u : ℚ_[p]) ^ 2 := by
                have h := congrArg (fun z : ℤ => (z : ℚ_[p])) hb'eq
                push_cast at h
                exact h
              have heq2 : hilbertSym (a : ℚ_[p]) (b' : ℚ_[p])
                  = hilbertSym (a : ℚ_[p]) (b'' : ℚ_[p]) := by
                rw [hb'fac]
                have := hilbertSym_mul_square_eq (k := ℚ_[p]) (a := (a : ℚ_[p])) (a' := 1)
                  (b := (b'' : ℚ_[p])) (b' := (u : ℚ_[p])) (by norm_num) huQp
                simpa using this
              rw [← heq2, ← heqp]
              exact hp p
            have hr'' : hilbertSym (a : ℝ) (b'' : ℝ) = 1 := by
              have h2r : Invertible (2 : ℝ) :=
                invertibleOfNonzero (by exact_mod_cast (show (2 : ℤ) ≠ 0 by norm_num))
              have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hbne
              have hb'R : (b' : ℝ) ≠ 0 := by exact_mod_cast hb'ne
              have hcast : ((t : ℝ)) ^ 2 - (a : ℝ) = (b : ℝ) * (b' : ℝ) := by
                have h := congrArg (fun z : ℤ => (z : ℝ)) hb'mul.symm
                push_cast at h
                rwa [mul_comm] at h
              have heqp : hilbertSym (a : ℝ) (b : ℝ) = hilbertSym (a : ℝ) (b' : ℝ) :=
                hilbertSym_eq_of_sq_sub_eq_mul hbR hb'R hcast
              have huR : (u : ℝ) ≠ 0 := by exact_mod_cast hu_ne
              have hb'fac : (b' : ℝ) = (b'' : ℝ) * (u : ℝ) ^ 2 := by
                have h := congrArg (fun z : ℤ => (z : ℝ)) hb'eq
                push_cast at h
                exact h
              have heq2 : hilbertSym (a : ℝ) (b' : ℝ) = hilbertSym (a : ℝ) (b'' : ℝ) := by
                rw [hb'fac]
                have := hilbertSym_mul_square_eq (k := ℝ) (a := (a : ℝ)) (a' := 1)
                  (b := (b'' : ℝ)) (b' := (u : ℝ)) (by norm_num) huR
                simpa using this
              rw [← heq2, ← heqp]
              exact hr
            have hIH := ih (a.natAbs + b''.natAbs) hsmall a b'' rfl ha hb''sf hp'' hr''
            -- transfer back over `ℚ`
            have h2q : Invertible (2 : ℚ) :=
              invertibleOfNonzero (by exact_mod_cast (show (2 : ℤ) ≠ 0 by norm_num))
            have hbQ : (b : ℚ) ≠ 0 := by exact_mod_cast hbne
            have hb'Q : (b' : ℚ) ≠ 0 := by exact_mod_cast hb'ne
            have hcast : ((t : ℚ)) ^ 2 - (a : ℚ) = (b : ℚ) * (b' : ℚ) := by
              have h := congrArg (fun z : ℤ => (z : ℚ)) hb'mul.symm
              push_cast at h
              rwa [mul_comm] at h
            have heqp : hilbertSym (a : ℚ) (b : ℚ) = hilbertSym (a : ℚ) (b' : ℚ) :=
              hilbertSym_eq_of_sq_sub_eq_mul hbQ hb'Q hcast
            have huQ : (u : ℚ) ≠ 0 := by exact_mod_cast hu_ne
            have hb'fac : (b' : ℚ) = (b'' : ℚ) * (u : ℚ) ^ 2 := by
              have h := congrArg (fun z : ℤ => (z : ℚ)) hb'eq
              push_cast at h
              exact h
            have heq2 : hilbertSym (a : ℚ) (b' : ℚ) = hilbertSym (a : ℚ) (b'' : ℚ) := by
              rw [hb'fac]
              have := hilbertSym_mul_square_eq (k := ℚ) (a := (a : ℚ)) (a' := 1)
                (b := (b'' : ℚ)) (b' := (u : ℚ)) (by norm_num) huQ
              simpa using this
            rw [heqp, heq2]
            exact hIH
      rcases le_total a.natAbs b.natAbs with hle | hle
      · exact main a b hab hle ha hb hp hr
      · have hmain : hilbertSym (b : ℚ) (a : ℚ) = 1 :=
          main b a (by omega) hle hb ha
            (fun p hpinst => by
              have : Fact (Nat.Prime p) := hpinst
              rw [hilbertSym_comm]
              exact hp p)
            (by rw [hilbertSym_comm]; exact hr)
        rwa [hilbertSym_comm] at hmain
  exact H (a.natAbs + b.natAbs) a b rfl ha hb hp hr

/-! ### WP1 1.6 — the rank-three local–global principle

With `legendre_int` in hand we can discharge the hypothesis that `RankThree.lean` isolated:
a global Hilbert symbol `(A, B)_ℚ` is `1` as soon as all its localizations are.  The reduction
from arbitrary nonzero `A`, `B` to squarefree integers is the square-class normal form 1.4, and
the local hypotheses are moved along the same square factors by `hilbertSym_mul_square_eq`. -/

/-- **Legendre's theorem / Hasse norm theorem for `ℚ(√B)`.** If `(A, B)_v = 1` at every place
`v` of `ℚ` (every prime `p` and `v = ∞`), then `(A, B)_ℚ = 1`. -/
-- Theorem: the local–global principle for the Hilbert symbol over `ℚ`.
theorem hilbertSymLocalGlobal : HilbertSymLocalGlobal := by
  intro A B hA hB hlocp hlocR
  obtain ⟨a, ha, s, hs, hAeq⟩ := exists_squarefree_mul_sq A hA
  obtain ⟨b, hb, t, ht, hBeq⟩ := exists_squarefree_mul_sq B hB
  have hmain : hilbertSym (a : ℚ) (b : ℚ) = 1 := by
    refine legendre_int a b ha hb ?_ ?_
    · intro p hpinst
      have : Fact (Nat.Prime p) := hpinst
      have hp' : hilbertSym (A : ℚ_[p]) (B : ℚ_[p]) = 1 := hlocp p
      have hArep : (A : ℚ_[p]) = (a : ℚ_[p]) * (s : ℚ_[p]) ^ 2 := by
        have h := congrArg (fun z : ℚ => (z : ℚ_[p])) hAeq
        push_cast at h
        exact h
      have hBrep : (B : ℚ_[p]) = (b : ℚ_[p]) * (t : ℚ_[p]) ^ 2 := by
        have h := congrArg (fun z : ℚ => (z : ℚ_[p])) hBeq
        push_cast at h
        exact h
      rw [hArep, hBrep] at hp'
      rw [hilbertSym_mul_square_eq (a := (a : ℚ_[p])) (a' := (s : ℚ_[p]))
        (b := (b : ℚ_[p])) (b' := (t : ℚ_[p]))
        (by exact_mod_cast hs) (by exact_mod_cast ht)] at hp'
      exact hp'
    · have hArep : (A : ℝ) = (a : ℝ) * (s : ℝ) ^ 2 := by
        have h := congrArg (fun z : ℚ => (z : ℝ)) hAeq
        push_cast at h
        exact h
      have hBrep : (B : ℝ) = (b : ℝ) * (t : ℝ) ^ 2 := by
        have h := congrArg (fun z : ℚ => (z : ℝ)) hBeq
        push_cast at h
        exact h
      rw [hArep, hBrep] at hlocR
      rw [hilbertSym_mul_square_eq (a := (a : ℝ)) (a' := (s : ℝ))
        (b := (b : ℝ)) (b' := (t : ℝ))
        (by exact_mod_cast hs) (by exact_mod_cast ht)] at hlocR
      exact hlocR
  calc hilbertSym A B
      = hilbertSym ((a : ℚ) * s ^ 2) ((b : ℚ) * t ^ 2) := by rw [hAeq, hBeq]
    _ = hilbertSym (a : ℚ) (b : ℚ) :=
        hilbertSym_mul_square_eq (a := (a : ℚ)) (a' := s) (b := (b : ℚ)) (b' := t) hs ht
    _ = 1 := hmain

/-- **Rank-three local–global principle (unconditional).** A nondegenerate quadratic form of
rank three over `ℚ` that is isotropic over every completion is isotropic over `ℚ`. -/
-- Theorem: unconditional rank-three Hasse–Minkowski over `ℚ`.
theorem isotropic_of_rank_three' {V : Type*} [AddCommGroup V] [Module ℚ V]
    [FiniteDimensional ℚ V] (Q : QuadraticForm ℚ V) (hr : finrank ℚ V = 3)
    (hQ : Q.Nondegenerate) (hQ' : EverywhereLocallyIsotropic Q) : Isotropic Q :=
  isotropic_of_rank_three hilbertSymLocalGlobal Q hr hQ hQ'

end HasseMinkowski
