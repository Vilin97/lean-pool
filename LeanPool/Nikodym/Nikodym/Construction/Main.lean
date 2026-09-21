/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/

import LeanPool.Nikodym.Nikodym.Construction.Count
import LeanPool.Nikodym.Nikodym.Construction.Arith
import LeanPool.Nikodym.Nikodym.MultiQuadratic.Scaffold
import LeanPool.Nikodym.Nikodym.MultiQuadratic.Legendre

/-!
# The upper bound: assembly

This file implements blueprint node M02 of `docs/nikodym_construction_lean_blueprint.md`: the
final assembly of the construction, discharging `Nikodym.exists_isNikodym_card_le`.

* `two_rpow_one_sub`: `2 ^ (1 - (k + 1)) = 2⁻¹ ^ k` in `ℝ`.
* `exists_sq_eq_of_primes`: the Legendre step (L01) packaged as the choice of a squarefree
  `r ∈ {ℓ, ℓ', ℓ ℓ'}`, `r > 1`, with a square root in `F`.
* `exists_isNikodym_card_le_aux`: for `d ≥ 2` and `ε > 0`, every field of sufficiently large
  prime cardinality `q` contains a Nikodym set `N ⊆ F^d` with
  `|N| ≤ q ^ d - q ^ (d - 2 ^ (1 - d) - ε)`.

The route is that of the blueprint: with `d = k + 1`, choose `m` with `3 (k+1) / 2^m ≤ ε/2`
(M01(a)) and `n = 2^m`; choose `2m` distinct odd primes `ℓⱼ, ℓ'ⱼ` (M01(d)); put
`K₀ = ∏ⱼ ℓⱼ ℓ'ⱼ` and `c = E01const n k K₀`; choose `q₁` with `q^(-ε/2) ≤ c` for `q ≥ q₁`
(M01(b)). For a field `F` of prime cardinality `q ≥ q₀`, L01 provides `rⱼ ∣ ℓⱼ ℓ'ⱼ` with square
roots `sⱼ` in `F`; K06 gives a scaffold of rank `n` with constant `K₀`; E02 gives the Nikodym set;
M01(c) converts the exponent.
-/

namespace Nikodym

open Real

/-- Blueprint M02: `2 ^ (1 - (k + 1)) = 2⁻¹ ^ k` as real numbers. -/
theorem two_rpow_one_sub (k : ℕ) : (2 : ℝ) ^ (1 - ((k + 1 : ℕ) : ℝ)) = (2 : ℝ)⁻¹ ^ k := by
  rw [show (1 : ℝ) - ((k + 1 : ℕ) : ℝ) = -(k : ℝ) by push_cast; ring, rpow_neg zero_le_two,
    rpow_natCast, inv_pow]

/-- Blueprint M02 (Legendre step, from L01): for `F` of odd prime cardinality and distinct primes
`ℓ, ℓ' < |F|`, there is a squarefree `r > 1` dividing `ℓ ℓ'` which is a square in `F`. -/
theorem exists_sq_eq_of_primes {F : Type*} [Field F] [Fintype F] (hp : (Fintype.card F).Prime)
    (hodd : Odd (Fintype.card F)) {ℓ ℓ' : ℕ} (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime) (hne : ℓ ≠ ℓ')
    (h1 : ℓ < Fintype.card F) (h2 : ℓ' < Fintype.card F) :
    ∃ (r : ℕ) (s : F), s ^ 2 = (r : F) ∧ 1 < r ∧ Squarefree r ∧ r ∣ ℓ * ℓ' := by
  rcases MultiQuad.exists_isSquare_of_primes hp hodd hℓ hℓ' h1 h2 with ⟨s, hs⟩ | ⟨s, hs⟩ | ⟨s, hs⟩
  · exact ⟨ℓ, s, by rw [sq, hs], hℓ.one_lt, hℓ.prime.squarefree, dvd_mul_right _ _⟩
  · exact ⟨ℓ', s, by rw [sq, hs], hℓ'.one_lt, hℓ'.prime.squarefree, dvd_mul_left _ _⟩
  · refine ⟨ℓ * ℓ', s, by rw [sq, hs], ?_, ?_, dvd_rfl⟩
    · exact lt_of_lt_of_le hℓ.one_lt (Nat.le_mul_of_pos_right _ hℓ'.pos)
    · exact (Nat.squarefree_mul ((Nat.coprime_primes hℓ hℓ').2 hne)).2
        ⟨hℓ.prime.squarefree, hℓ'.prime.squarefree⟩

/-- Blueprint M02 (the final theorem, construction side). For `d ≥ 2` and `ε > 0`, every finite
field `F` of sufficiently large prime cardinality `q` contains a Nikodym set `N ⊆ F^d` with
`|N| ≤ q ^ d - q ^ (d - 2 ^ (1 - d) - ε)`. -/
theorem exists_isNikodym_card_le_aux {d : ℕ} (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    ∃ q₀ : ℕ, ∀ (F : Type) [Field F] [Fintype F],
      (Fintype.card F).Prime → q₀ ≤ Fintype.card F →
        ∃ N : Finset (Fin d → F), IsNikodym N ∧
          (N.card : ℝ) ≤ (Fintype.card F : ℝ) ^ d -
            (Fintype.card F : ℝ) ^ ((d : ℝ) - 2 ^ (1 - (d : ℝ)) - ε) := by
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
  have hk : 1 ≤ k := by omega
  -- M01(a): `m` with `3 (k+1) / 2^m ≤ ε/2`, and `n = 2^m`
  obtain ⟨m, hm⟩ := exists_pow_two_ge (k + 1) hε
  set n : ℕ := 2 ^ m with hn_def
  have hn : 1 ≤ n := Nat.one_le_two_pow
  have hsε : 3 * ((k : ℝ) + 1) / n ≤ ε / 2 := by
    have hn' : (n : ℝ) = 2 ^ m := by rw [hn_def]; push_cast; ring
    rw [hn']
    push_cast at hm
    exact hm
  -- M01(d): `2m` distinct odd primes
  obtain ⟨ℓ, ℓ', hℓ, hℓ', hne, hdist⟩ := exists_distinct_odd_primes m
  have hℓpos : ∀ j, 0 < ℓ j * ℓ' j := fun j ↦ Nat.mul_pos (hℓ j).1.pos (hℓ' j).1.pos
  -- the uniform scaffold constant `K₀ = ∏ⱼ ℓⱼ ℓ'ⱼ` (and its integer version `P`)
  have hK₀ : 0 < ∏ j, ((ℓ j * ℓ' j : ℕ) : ℝ) :=
    Finset.prod_pos fun j _ ↦ by exact_mod_cast hℓpos j
  set P : ℕ := ∏ j, (ℓ j * ℓ' j) with hP_def
  have hPpos : 0 < P := Finset.prod_pos fun j _ ↦ hℓpos j
  have hℓP : ∀ j, ℓ j ≤ P := fun j ↦ Nat.le_of_dvd hPpos
    ((dvd_mul_right _ _).trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ j)))
  have hℓ'P : ∀ j, ℓ' j ≤ P := fun j ↦ Nat.le_of_dvd hPpos
    ((dvd_mul_left _ _).trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ j)))
  -- M01(b): `q₁` with `q^(-ε/2) ≤ c` for `q ≥ q₁`
  obtain ⟨q₁, hq₁⟩ := exists_rpow_neg_le (Scaffold.E01const_pos (n := n) (k := k) hK₀ hn) hε
  refine ⟨max (max (2 ^ (n * 2 ^ k)) (10 ^ n)) (max (P + 1) q₁), ?_⟩
  intro F _ _ hp hq₀
  have hq : 2 ^ (n * 2 ^ k) ≤ Fintype.card F :=
    ((le_max_left _ _).trans (le_max_left _ _)).trans hq₀
  have h10 : 10 ^ n ≤ Fintype.card F := ((le_max_right _ _).trans (le_max_left _ _)).trans hq₀
  have hPq : P + 1 ≤ Fintype.card F := ((le_max_left _ _).trans (le_max_right _ _)).trans hq₀
  have hq₁' : q₁ ≤ Fintype.card F := ((le_max_right _ _).trans (le_max_right _ _)).trans hq₀
  have hM : 10 ≤ Params.M n (Fintype.card F) := Params.le_M_of_pow_le hn h10
  have hodd : Odd (Fintype.card F) := by
    refine hp.eq_two_or_odd'.resolve_left fun h2 ↦ ?_
    have : 10 ≤ Fintype.card F := (Nat.le_self_pow (by omega) 10).trans h10
    omega
  -- L01: square roots of `rⱼ ∈ {ℓⱼ, ℓ'ⱼ, ℓⱼ ℓ'ⱼ}` in `F`
  have hsq : ∀ j, ∃ (r : ℕ) (s : F), s ^ 2 = (r : F) ∧ 1 < r ∧ Squarefree r ∧ r ∣ ℓ j * ℓ' j :=
    fun j ↦ exists_sq_eq_of_primes hp hodd (hℓ j).1 (hℓ' j).1 (hne j)
      (by have := hℓP j; omega) (by have := hℓ'P j; omega)
  choose r s hs hr1 hrsq hrdvd using hsq
  have hcop : ∀ j j', j ≠ j' → Nat.Coprime (r j) (r j') := by
    intro j j' hjj'
    obtain ⟨h1, h2, h3⟩ := hdist j j' hjj'
    have h4 : ℓ' j ≠ ℓ j' := fun h ↦ (hdist j' j hjj'.symm).2.1 h.symm
    have hprod : Nat.Coprime (ℓ j * ℓ' j) (ℓ j' * ℓ' j') := by
      refine Nat.Coprime.mul_left ?_ ?_
      · exact Nat.Coprime.mul_right ((Nat.coprime_primes (hℓ j).1 (hℓ j').1).2 h1)
          ((Nat.coprime_primes (hℓ j).1 (hℓ' j').1).2 h2)
      · exact Nat.Coprime.mul_right ((Nat.coprime_primes (hℓ' j).1 (hℓ j').1).2 h4)
          ((Nat.coprime_primes (hℓ' j).1 (hℓ' j').1).2 h3)
    exact (hprod.coprime_dvd_left (hrdvd j)).coprime_dvd_right (hrdvd j')
  -- K06: the scaffold of rank `n = 2^m` with constant `K₀`
  have S := MultiQuad.scaffold_of_dvd hr1 hrsq hcop hp s hs ℓ ℓ' hrdvd hℓpos
  have hcard : Fintype.card (Fin m → ℤˣ) = n := MultiQuad.rank_eq
  -- E02
  obtain ⟨N, hN, hcount⟩ := S.exists_isNikodym_of_scaffold hK₀ hcard hn hk rfl hq hM
  refine ⟨N, hN, ?_⟩
  -- M01(c): convert the exponent
  have hq1 : (1 : ℝ) ≤ Fintype.card F := by
    exact_mod_cast Params.one_le_q_of_threshold (h := k + 1) hq
  have hc : (Fintype.card F : ℝ) ^ (-(ε / 2)) ≤
      Scaffold.E01const n k (∏ j, ((ℓ j * ℓ' j : ℕ) : ℝ)) :=
    hq₁ _ (by exact_mod_cast hq₁')
  have hgap := rpow_gap (a := (k + 1 : ℝ) - (2 : ℝ)⁻¹ ^ k) hq1 hsε hc
  have hexp : ((k + 1 : ℕ) : ℝ) - 2 ^ (1 - ((k + 1 : ℕ) : ℝ)) - ε =
      (k + 1 : ℝ) - (2 : ℝ)⁻¹ ^ k - ε := by
    rw [two_rpow_one_sub]
    push_cast
    ring
  rw [hexp]
  linarith

end Nikodym

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
