/-
Copyright (c) 2026 jayyswan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: jayyswan
-/
module

public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.Data.Nat.Cast.Field
public import Mathlib.Data.Nat.ChineseRemainder
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Pi
public import Mathlib.Topology.MetricSpace.Pseudo.Constructions

/-!
# Weak approximation for ℚ

The weak approximation theorem for the rational numbers: a rational number can be found
arbitrarily close (simultaneously) to any prescribed real number and any finite collection of
`p`-adic numbers.  This is the arithmetic input for the high-rank Hasse–Minkowski induction.

The proof is elementary.  Fix tolerances, approximate each `p`-adic coordinate `y_p` by a
rational `c_p`, clear denominators with `D = ∏ p, (c p).den` and use the Chinese remainder
theorem to solve `r ≡ D·c_p (mod p^{m})` for a single integer `r`.  Then `x = r/D` already
matches every `p`-adic coordinate; adding an integer multiple of `N = ∏ p^{m}` (divided by `D`)
preserves the `p`-adic congruences as long as the multiplier is `p`-adically integral, and a
multiplier of the form `s / L^j` with `L` a prime outside the finite set is `p`-adically
integral for every `p` in the set while being dense in `ℝ`.  This gives the real approximation.
-/

@[expose] public section

namespace Rat

open scoped BigOperators
open scoped Function

/-- The `n`-th prime is prime, as an instance. -/
local instance fact_prime_of_primes (p : Nat.Primes) : Fact (Nat.Prime (p : ℕ)) := ⟨p.2⟩

/-- The finite embedding of `ℚ` into the product of the completions of `ℚ` at a finite set of
places (which includes `ℝ`). -/
noncomputable abbrev finiteEmbedding (S : Finset Nat.Primes) (x : ℚ) : ℝ × (Π p : S, ℚ_[p]) :=
  ⟨algebraMap ℚ ℝ x, fun p ↦ (algebraMap ℚ ℚ_[p]) x⟩

/-! ### Elementary lemmas -/

-- Theorem: the norm of `p ^ k` in `ℚ_[p]` is `p ^ (-k)` (as a real number).
lemma norm_pow_eq (p : ℕ) [Fact p.Prime] (k : ℕ) :
    ‖(p : ℚ_[p]) ^ k‖ = (p : ℝ) ^ (-(k : ℤ)) := by
  rw [norm_pow, Padic.norm_p, inv_pow, ← zpow_natCast, zpow_neg]

-- Theorem: the norm of a nonzero natural number `D` in `ℚ_[p]` is `p ^ (-v_p(D))`.
lemma norm_natCast_eq (p : ℕ) [Fact p.Prime] {D : ℕ} (hD : D ≠ 0) :
    ‖(D : ℚ_[p])‖ = (p : ℝ) ^ (-(padicValNat p D : ℤ)) := by
  have hD' : (D : ℚ_[p]) ≠ 0 := by
    exact_mod_cast hD
  rw [Padic.norm_eq_zpow_neg_valuation hD', Padic.valuation_natCast]

-- Theorem (per-place estimate): if `D * x - n = p ^ (m + v) * w` with `(n : ℚ) = D * c`,
-- `‖D‖ = p ^ (-v)` and `‖w‖ ≤ 1`, then `‖x - c‖ ≤ p ^ (-m)`.
lemma norm_sub_le (p : ℕ) [Fact p.Prime] {D : ℕ} (hD : D ≠ 0)
    {c x : ℚ} {n : ℤ} (hn : (n : ℚ) = D * c)
    {m v : ℕ} (hv : ‖(D : ℚ_[p])‖ = (p : ℝ) ^ (-(v : ℤ)))
    {w : ℚ} (hval : D * x - n = (p : ℚ) ^ (m + v) * w)
    (hw : ‖(w : ℚ_[p])‖ ≤ 1) :
    ‖((x - c : ℚ) : ℚ_[p])‖ ≤ (p : ℝ) ^ (-(m : ℤ)) := by
  have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hD
  have hxc : x - c = ((D : ℚ) * x - n) / D := by
    rw [hn]
    field_simp
  have hcast : ((x - c : ℚ) : ℚ_[p]) =
      (p : ℚ_[p]) ^ (m + v) * (w : ℚ_[p]) * (D : ℚ_[p])⁻¹ := by
    rw [hxc, hval]
    push_cast
    ring
  rw [hcast, norm_mul, norm_mul, norm_pow_eq, norm_inv, hv]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : Nat.Prime p).pos
  have hcomb : (p : ℝ) ^ (-((m + v : ℕ) : ℤ)) * (p : ℝ) ^ ((v : ℕ) : ℤ) =
      (p : ℝ) ^ (-(m : ℤ)) := by
    rw [← zpow_add₀ hp0.ne']
    congr 1
    push_cast
    ring
  calc (p : ℝ) ^ (-((m + v : ℕ) : ℤ)) * ‖(w : ℚ_[p])‖ *
        ((p : ℝ) ^ (-((v : ℕ) : ℤ)))⁻¹
      = ((p : ℝ) ^ (-((m + v : ℕ) : ℤ)) * (p : ℝ) ^ ((v : ℕ) : ℤ)) *
        ‖(w : ℚ_[p])‖ := by
        rw [show ((p : ℝ) ^ (-((v : ℕ) : ℤ)))⁻¹ = (p : ℝ) ^ ((v : ℕ) : ℤ) by
          rw [zpow_neg, inv_inv]]
        ring
    _ = (p : ℝ) ^ (-(m : ℤ)) * ‖(w : ℚ_[p])‖ := by rw [hcomb]
    _ ≤ (p : ℝ) ^ (-(m : ℤ)) * 1 := by
        exact mul_le_mul_of_nonneg_left hw (zpow_nonneg hp0.le _)
    _ = (p : ℝ) ^ (-(m : ℤ)) := mul_one _

-- Theorem (CRT): for pairwise coprime prime powers `(π i) ^ k i` and integer residues `a i`
-- there is an integer `r` congruent to `a i` modulo `(π i) ^ k i` for every `i`.
lemma exists_int_modEq {ι : Type*} (π : ι → Nat.Primes)
    (hπ : Function.Injective π) (t : Finset ι) (k : ι → ℕ) (a : ι → ℤ) :
    ∃ r : ℤ, ∀ i ∈ t, r ≡ a i [ZMOD ((π i : ℕ) : ℤ) ^ (k i)] := by
  classical
  set s : ι → ℕ := fun i ↦ (π i : ℕ) ^ k i with hs
  have hs0 : ∀ i ∈ t, s i ≠ 0 := fun i _ ↦ pow_ne_zero _ (π i).2.ne_zero
  have hpp : Set.Pairwise (↑t : Set ι) (Nat.Coprime on s) := by
    intro i _ j _ hij
    have hne : (π i : ℕ) ≠ (π j : ℕ) := fun h ↦ hij (hπ (Subtype.ext h))
    have hcop : Nat.Coprime (π i : ℕ) (π j : ℕ) :=
      (Nat.Prime.coprime_iff_not_dvd (π i).2).mpr fun hd ↦ by
        rcases (Nat.dvd_prime (π j).2).mp hd with h1 | h2
        · exact (π i).2.ne_one h1
        · exact hne h2
    exact hcop.pow (k i) (k j)
  let a' : ι → ℕ := fun i ↦ (a i % ((s i : ℕ) : ℤ)).toNat
  obtain ⟨r, hr⟩ := Nat.chineseRemainderOfFinset a' s t hs0 hpp
  refine ⟨r, fun i hi ↦ ?_⟩
  have hmod : (s i : ℤ) = ((π i : ℕ) : ℤ) ^ (k i) := by
    rw [hs]; push_cast; ring
  rw [← hmod]
  have hr' : r ≡ a' i [MOD s i] := hr i hi
  have h1 : (r : ℤ) ≡ (a' i : ℤ) [ZMOD (s i : ℤ)] := by
    simpa using (Int.natCast_modEq_iff.mpr hr')
  have hsi : (s i : ℤ) ≠ 0 := by exact_mod_cast hs0 i hi
  have h2 : (a' i : ℤ) = a i % ((s i : ℕ) : ℤ) := by
    simp only [a']
    exact Int.toNat_of_nonneg (Int.emod_nonneg _ hsi)
  have h3 : a i % ((s i : ℕ) : ℤ) ≡ a i [ZMOD (s i : ℤ)] := Int.mod_modEq _ _
  rw [h2] at h1
  exact h1.trans h3

-- Theorem: a grid of spacing `1 / L ^ j` with `L > 1` hits every real to within one step.
lemma exists_int_grid (L : ℝ) (hL : 1 < L) (u : ℝ) (j : ℕ) :
    ∃ s : ℤ, |u - (s : ℝ) / L ^ j| < 1 / L ^ j := by
  refine ⟨⌊u * L ^ j⌋, ?_⟩
  have hLj : (0 : ℝ) < L ^ j := pow_pos (by linarith) j
  have h1 : ((⌊u * L ^ j⌋ : ℤ) : ℝ) ≤ u * L ^ j := Int.floor_le _
  have h2 : u * L ^ j < ((⌊u * L ^ j⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
  have h3 : |u * L ^ j - (⌊u * L ^ j⌋ : ℝ)| < 1 := by
    rw [abs_lt]
    constructor <;> linarith
  have heq : u - (⌊u * L ^ j⌋ : ℝ) / L ^ j =
      (u * L ^ j - (⌊u * L ^ j⌋ : ℝ)) / L ^ j := by
    field_simp
  rw [heq, abs_div, abs_of_pos hLj]
  exact div_lt_div_of_pos_right h3 hLj

-- Theorem: if `L` is a prime different from `p`, then `a + b * (c / L ^ j)` is `p`-adically
-- integral for all integers `a`, `b`, `c` and every `j`.
lemma norm_add_mul_div_le_one (p : ℕ) [Fact p.Prime] {L : ℕ} (hL : Nat.Prime L) (hpL : p ≠ L)
    (a : ℤ) (b : ℕ) (c : ℤ) (j : ℕ) :
    ‖(((a : ℚ) + (b : ℚ) * ((c : ℚ) / (L : ℚ) ^ j) : ℚ) : ℚ_[p])‖ ≤ 1 := by
  have hnot : ¬ p ∣ L := by
    intro hd
    rcases (Nat.dvd_prime hL).mp hd with h1 | h2
    · exact (Fact.out : Nat.Prime p).ne_one h1
    · exact hpL h2
  have hLn : ‖(L : ℚ_[p])‖ = 1 := by
    rw [show (L : ℚ_[p]) = ((L : ℚ) : ℚ_[p]) by norm_cast, Padic.eq_padicNorm]
    exact_mod_cast (padicNorm.nat_eq_one_iff L).mpr hnot
  have ha : ‖(a : ℚ_[p])‖ ≤ 1 := by
    rw [show (a : ℚ_[p]) = ((a : ℚ) : ℚ_[p]) by norm_cast, Padic.eq_padicNorm]
    exact_mod_cast (padicNorm.of_int a)
  have hb : ‖(b : ℚ_[p])‖ ≤ 1 := by
    rw [show (b : ℚ_[p]) = ((b : ℚ) : ℚ_[p]) by norm_cast, Padic.eq_padicNorm]
    exact_mod_cast (padicNorm.of_nat b)
  have hc : ‖(c : ℚ_[p])‖ ≤ 1 := by
    rw [show (c : ℚ_[p]) = ((c : ℚ) : ℚ_[p]) by norm_cast, Padic.eq_padicNorm]
    exact_mod_cast (padicNorm.of_int c)
  have hcl : ‖(c : ℚ_[p]) / (L : ℚ_[p]) ^ j‖ ≤ 1 := by
    rw [norm_div, norm_pow, hLn, one_pow, div_one]
    exact hc
  rw [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast]
  refine (Padic.nonarchimedean _ _).trans (max_le ha ?_)
  rw [norm_mul]
  calc ‖(b : ℚ_[p])‖ * ‖(c : ℚ_[p]) / (L : ℚ_[p]) ^ j‖ ≤ 1 * 1 :=
        mul_le_mul hb hcl (norm_nonneg _) zero_le_one
    _ = 1 := by norm_num

/-! ### Weak approximation -/

/-- Given a finite set of places and a point in the product of the completions of ℚ at those
places, there exists a rational number that is arbitrarily close to the given point at all those
places. -/
theorem approximation' {S : Finset Nat.Primes} {ε : ℝ} (hε : ε > 0)
    (y : ℝ × (Π p : S, ℚ_[p])) :
    ∃ x : ℚ, ‖y.1 - x‖ + Finset.sum (Finset.attach S) (fun n ↦ ‖y.2 n - x‖) < ε := by
  classical
  set δ : ℝ := ε / (2 * ((S.card : ℝ) + 1)) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]; positivity
  have hδ2 : 0 < δ / 2 := half_pos hδpos
  -- Rational approximations at the `p`-adic places.
  have hc_exists : ∀ p : S, ∃ c : ℚ, ‖y.2 p - (c : ℚ_[p])‖ < δ / 2 :=
    fun p ↦ Padic.rat_dense p.1.1 (y.2 p) hδ2
  choose c hc using hc_exists
  -- A common denominator for those approximations.
  set D : ℕ := ∏ p : S, (c p).den with hDdef
  have hDpos : 0 < D := by
    rw [hDdef]
    exact Finset.prod_pos fun p _ ↦ Rat.pos (c p)
  have hDne : D ≠ 0 := hDpos.ne'
  set n : S → ℤ := fun p ↦ (c p).num * ((D / (c p).den : ℕ) : ℤ) with hndef
  have hden : ∀ p : S, (c p).den ∣ D := fun p ↦ by
    rw [hDdef]; exact Finset.dvd_prod_of_mem _ (Finset.mem_univ p)
  have hn_eq : ∀ p : S, (n p : ℚ) = (D : ℚ) * c p := by
    intro p
    have hDq : (D : ℚ) = ((c p).den : ℚ) * ((D / (c p).den : ℕ) : ℚ) := by
      norm_cast
      exact (Nat.mul_div_cancel' (hden p)).symm
    have hcp : c p = ((c p).num : ℚ) / ((c p).den : ℚ) :=
      (Rat.num_div_den (c p)).symm
    have hn1 : (n p : ℚ) = ((c p).num : ℚ) * ((D / (c p).den : ℕ) : ℚ) := by
      simp only [hndef, Int.cast_mul, Int.cast_natCast]
    have hdivq : ((D / (c p).den : ℕ) : ℚ) = (D : ℚ) / ((c p).den : ℚ) :=
      Nat.cast_div_charZero (hden p)
    calc (n p : ℚ) = ((c p).num : ℚ) * ((D / (c p).den : ℕ) : ℚ) := hn1
      _ = ((c p).num : ℚ) * ((D : ℚ) / ((c p).den : ℚ)) := by rw [hdivq]
      _ = (D : ℚ) * c p := by
          conv_rhs => rw [hcp]
          ring
  -- The `p`-adic precision.
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (2 : ℝ) ^ (-(m : ℤ)) < δ / 2 := by
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (y := (2 : ℝ)⁻¹) hδ2 (by norm_num)
    exact ⟨m, by
      rw [show ((2 : ℝ)⁻¹) ^ m = (2 : ℝ) ^ (-(m : ℤ)) by
        rw [inv_pow, ← zpow_natCast, ← zpow_neg]] at hm
      exact hm⟩
  set K : S → ℕ := fun p ↦ m + padicValNat p.1.1 D with hKdef
  set N : ℕ := ∏ p : S, p.1.1 ^ K p with hNdef
  have hNpos : 0 < N := by
    rw [hNdef]
    exact Finset.prod_pos fun p _ ↦ pow_pos p.1.2.pos _
  have hNne : N ≠ 0 := hNpos.ne'
  -- Chinese remainder.
  obtain ⟨r, hr⟩ := exists_int_modEq (fun p : S ↦ p.1) Subtype.val_injective
    (Finset.univ : Finset S) K n
  -- A prime `L` outside the finite set.
  set Q : ℕ := ∏ p : S, p.1.1 with hQdef
  obtain ⟨L, hLge, hLprime⟩ := Nat.exists_infinite_primes (1 + Q)
  have hpQ : ∀ p : S, p.1.1 ≤ Q := fun p ↦ by
    rw [hQdef]
    exact Finset.single_le_prod (fun q _ ↦ (q.1.2.one_lt).le) (Finset.mem_univ p)
  have hLne : ∀ p : S, p.1.1 ≠ L := by
    intro p hp
    have := hpQ p
    omega
  have hL1 : (1 : ℝ) < L := by exact_mod_cast hLprime.one_lt
  -- A multiplier `s / L ^ j` which is integral at every place in `S`.
  obtain ⟨j, hj⟩ : ∃ j : ℕ, ((L : ℝ)⁻¹) ^ j < δ * D / (2 * N) :=
    exists_pow_lt_of_lt_one (y := (L : ℝ)⁻¹) (by positivity)
      (inv_lt_one_of_one_lt₀ hL1)
  -- Real approximation on the grid `s / L ^ j`.
  set u : ℝ := ((D : ℝ) * y.1 - (r : ℝ)) / (N : ℝ) with hudef
  obtain ⟨s, hs⟩ := exists_int_grid (L : ℝ) hL1 u j
  set x : ℚ := ((r : ℚ) + (N : ℚ) * ((s : ℚ) / (L : ℚ) ^ j)) / (D : ℚ) with hxdef
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hNne
  have hDr : (D : ℝ) ≠ 0 := by exact_mod_cast hDne
  have hLr : (L : ℝ) ≠ 0 := by positivity
  -- The real coordinate is close.
  have hreal : ‖y.1 - x‖ < δ := by
    rw [Real.norm_eq_abs]
    have hdiff : y.1 - x = ((N : ℝ) / (D : ℝ)) * (u - (s : ℝ) / (L : ℝ) ^ j) := by
      rw [hxdef, hudef]
      push_cast
      field_simp
      ring
    rw [hdiff]
    have hND : 0 < (N : ℝ) / (D : ℝ) := by positivity
    rw [abs_mul, abs_of_pos hND]
    have hLp : 1 / (L : ℝ) ^ j = ((L : ℝ)⁻¹) ^ j := by rw [one_div, inv_pow]
    rw [hLp] at hs
    calc (N : ℝ) / (D : ℝ) * |u - (s : ℝ) / (L : ℝ) ^ j|
        < (N : ℝ) / (D : ℝ) * ((L : ℝ)⁻¹) ^ j := mul_lt_mul_of_pos_left hs hND
      _ < (N : ℝ) / (D : ℝ) * (δ * D / (2 * N)) := mul_lt_mul_of_pos_left hj hND
      _ = δ / 2 := by field_simp
      _ < δ := by linarith
  -- Each `p`-adic coordinate is close.
  have hper : ∀ p : S, ‖y.2 p - x‖ < δ := by
    intro p
    obtain ⟨q₀, hq₀⟩ := (Int.modEq_iff_add_fac).mp (hr p (Finset.mem_univ p))
    have hdivN : p.1.1 ^ K p ∣ N := by
      rw [hNdef]; exact Finset.dvd_prod_of_mem _ (Finset.mem_univ p)
    let w : ℚ := (-(q₀) : ℚ) +
      ((N / p.1.1 ^ K p : ℕ) : ℚ) * ((s : ℚ) / (L : ℚ) ^ j)
    have hxval : (D : ℚ) * x = (r : ℚ) + (N : ℚ) * ((s : ℚ) / (L : ℚ) ^ j) := by
      rw [hxdef]; field_simp
    have hnq : (n p : ℚ) = (r : ℚ) + ((p.1.1 : ℚ) ^ K p) * (q₀ : ℚ) := by
      rw [hq₀]; push_cast; ring
    have hNs : (N : ℚ) = ((p.1.1 : ℚ) ^ K p) * ((N / p.1.1 ^ K p : ℕ) : ℚ) := by
      rw [← Nat.cast_pow, ← Nat.cast_mul, Nat.mul_div_cancel' hdivN]
    have hval : (D : ℚ) * x - (n p : ℚ) =
        ((p.1.1 : ℚ) ^ (m + padicValNat p.1.1 D)) * w := by
      rw [hxval, hnq, hNs, hKdef]
      ring
    have hw : ‖(w : ℚ_[p.1.1])‖ ≤ 1 := by
      have := norm_add_mul_div_le_one p.1.1 hLprime (hLne p) (-q₀)
        (N / p.1.1 ^ K p : ℕ) s j
      simpa [w] using this
    have hxc' : ‖(c p : ℚ_[p.1.1]) - (x : ℚ_[p.1.1])‖ < δ / 2 := by
      have hcast : (c p : ℚ_[p.1.1]) - (x : ℚ_[p.1.1]) =
          -(((x - c p : ℚ) : ℚ_[p.1.1])) := by push_cast; ring
      rw [hcast, norm_neg]
      have hle := norm_sub_le p.1.1 hDne (hn_eq p) (norm_natCast_eq p.1.1 hDne) hval hw
      have hp2 : (2 : ℝ) ≤ (p.1.1 : ℝ) := by exact_mod_cast p.1.2.two_le
      have hmono : (p.1.1 : ℝ) ^ (-(m : ℤ)) ≤ (2 : ℝ) ^ (-(m : ℤ)) := by
        simp only [zpow_neg, zpow_natCast]
        exact (inv_le_inv₀ (pow_pos (by positivity) m) (pow_pos (by norm_num) m)).mpr
          (pow_le_pow_left₀ (by norm_num) hp2 m)
      exact lt_of_le_of_lt (hle.trans hmono) hm
    have htri := dist_triangle (y.2 p) (c p : ℚ_[p.1.1]) (x : ℚ_[p.1.1])
    rw [dist_eq_norm, dist_eq_norm, dist_eq_norm] at htri
    exact lt_of_le_of_lt htri (by linarith [hc p, hxc'])
  refine ⟨x, ?_⟩
  have hsumle : Finset.sum (Finset.attach S) (fun n ↦ ‖y.2 n - (x : ℚ_[n.1.1])‖) ≤
      (S.card : ℝ) * δ := by
    have := Finset.sum_le_card_nsmul (Finset.attach S)
      (fun n ↦ ‖y.2 n - (x : ℚ_[n.1.1])‖) δ fun n _ ↦ le_of_lt (hper n)
    rwa [nsmul_eq_mul, Finset.card_attach] at this
  have htwo : ((S.card : ℝ) + 1) * δ = ε / 2 := by
    rw [hδdef]; field_simp
  have hfin : ‖y.1 - x‖ + Finset.sum (Finset.attach S) (fun n ↦ ‖y.2 n - x‖) <
      ((S.card : ℝ) + 1) * δ := by
    calc ‖y.1 - x‖ + Finset.sum (Finset.attach S) (fun n ↦ ‖y.2 n - x‖)
        < δ + (S.card : ℝ) * δ := add_lt_add_of_lt_of_le hreal hsumle
      _ = ((S.card : ℝ) + 1) * δ := by ring
  exact lt_of_lt_of_le hfin (by rw [htwo]; linarith)

/-- The approximation theorem can be restated as saying that the finite embedding is dense. -/
theorem approximation (S : Finset Nat.Primes) :
    Dense (Set.range (finiteEmbedding S)) := by
  rw [Metric.dense_iff]
  intro y r hr
  obtain ⟨x, hx⟩ := approximation' hr y
  have h2 : dist y.2 (fun p : S => (x : ℚ_[p.1.1])) ≤
      Finset.sum (Finset.attach S) (fun n => ‖y.2 n - (x : ℚ_[n.1.1])‖) := by
    rw [dist_pi_le_iff (Finset.sum_nonneg fun i _ => norm_nonneg _)]
    intro p
    rw [dist_eq_norm]
    exact Finset.single_le_sum (f := fun n => ‖y.2 n - (x : ℚ_[n.1.1])‖)
      (fun i _ => norm_nonneg _) (Finset.mem_attach S p)
  have hmain : dist y (finiteEmbedding S x) ≤
      ‖y.1 - (x : ℝ)‖ +
        Finset.sum (Finset.attach S) (fun n => ‖y.2 n - (x : ℚ_[n.1.1])‖) := by
    rw [Prod.dist_eq]
    refine max_le ?_ ?_
    · rw [dist_eq_norm]
      exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => norm_nonneg _)
    · exact h2.trans (le_add_of_nonneg_left (norm_nonneg _))
  exact ⟨finiteEmbedding S x,
    Metric.mem_ball.mpr (lt_of_le_of_lt (by simpa [dist_comm] using hmain) hx), ⟨x, rfl⟩⟩

end Rat
