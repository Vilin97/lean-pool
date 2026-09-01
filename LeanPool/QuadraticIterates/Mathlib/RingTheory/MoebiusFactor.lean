/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.UniqueFactorizationDomain.Finsupp
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Push

import LeanPool.QuadraticIterates.Mathlib.Algebra.BigOperators
import LeanPool.QuadraticIterates.Mathlib.NumberTheory.Moebius

/-!
# Integrality of Möbius factors of strong divisibility sequences

For a strong divisibility sequence `c` in a UFD `R` (nowhere zero on `n ≥ 1`), the Möbius factor
`∏_{d ∣ n} c_d ^ μ(n/d)`, a priori an element of the fraction field, lies in the image of `R`.
`moebiusFactorR c n` is its unique `R`-preimage, characterised by `algebraMap_moebiusFactorR`:
its image in any fraction field is the Möbius formula.

Auxiliary material for the formalization of M. Stoll, *Galois groups over ℚ of some iterated
polynomials*, Arch. Math. 59 (1992), 239-244; upstreaming candidates for Mathlib.
-/

open scoped ArithmeticFunction.Moebius
open UniqueFactorizationMonoid ArithmeticFunction

variable {R : Type*} [CommRing R] [IsDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- The Möbius factor of `c` in the fraction field. -/
noncomputable def moebiusFactorK (c : ℕ → R) (n : ℕ) : K :=
  ∏ x ∈ n.divisorsAntidiagonal, (algebraMap R K (c x.2)) ^ (μ x.1)

/-- numerator product (μ = 1 part) and denominator product (μ = -1 part), in `R`. -/
noncomputable def numProd (c : ℕ → R) (n : ℕ) : R :=
  ∏ x ∈ n.divisorsAntidiagonal with μ x.1 = 1, c x.2

/-- The product of sequence values whose Möbius coefficient is negative. -/
noncomputable def denProd (c : ℕ → R) (n : ℕ) : R :=
  ∏ x ∈ n.divisorsAntidiagonal with μ x.1 = -1, c x.2

omit [IsDomain R] in
theorem moebiusFactorK_eq_div {c : ℕ → R} (hc : ∀ d ≥ 1, c d ≠ 0) (n : ℕ) :
    moebiusFactorK (K := K) c n
      = algebraMap R K (numProd c n) / algebraMap R K (denProd c n) := by
  have hne (x : ℕ × ℕ) (hx : x ∈ n.divisorsAntidiagonal) : algebraMap R K (c x.2) ≠ 0 := by
    rw [ne_eq, FaithfulSMul.algebraMap_eq_zero_iff]
    exact hc x.2 (Nat.pos_of_ne_zero (Nat.right_ne_zero_of_mem_divisorsAntidiagonal hx))
  rw [moebiusFactorK, Finset.prod_congr rfl (fun x hx ↦ show (algebraMap R K (c x.2)) ^ (μ x.1)
      = (if μ x.1 = 1 then algebraMap R K (c x.2) else 1)
        * (if μ x.1 = -1 then (algebraMap R K (c x.2))⁻¹ else 1) by
    rcases moebius_eq_or x.1 with h | h | h <;> simp [h]),
    Finset.prod_mul_distrib, ← Finset.prod_filter, ← Finset.prod_filter, numProd, denProd,
    map_prod, map_prod, div_eq_mul_inv, ← Finset.prod_inv_distrib]

omit [IsDomain R] in
/-- A Möbius factor of a nowhere-zero sequence is nonzero in the fraction field. -/
lemma moebiusFactorK_ne_zero {c : ℕ → R} (hc : ∀ d ≥ 1, c d ≠ 0) (n : ℕ) :
    moebiusFactorK (K := K) c n ≠ 0 := by
  rw [moebiusFactorK, Finset.prod_ne_zero_iff]
  intro x hx
  refine zpow_ne_zero _ ?_
  rw [ne_eq, FaithfulSMul.algebraMap_eq_zero_iff]
  exact hc x.2 (Nat.pos_of_ne_zero (Nat.right_ne_zero_of_mem_divisorsAntidiagonal hx))

omit [IsDomain R] [IsFractionRing R K] in
@[simp] lemma moebiusFactorK_one (c : ℕ → R) :
    moebiusFactorK (K := K) c 1 = algebraMap R K (c 1) := by
  simp [moebiusFactorK]

omit [IsDomain R] in
/-- Möbius inversion in the fraction field: `c n = ∏_{d ∣ n} moebiusFactorK c d`. -/
lemma prod_moebiusFactorK {c : ℕ → R} (hc : ∀ d ≥ 1, c d ≠ 0) (n : ℕ) (hn : 1 ≤ n) :
    algebraMap R K (c n) = ∏ d ∈ n.divisors, moebiusFactorK (K := K) c d :=
  ((ArithmeticFunction.prod_eq_iff_prod_pow_moebius_eq_of_nonzero
      (f := moebiusFactorK (K := K) c) (g := fun k ↦ algebraMap R K (c k))
      (fun n _ ↦ moebiusFactorK_ne_zero hc n)
      (fun k hk ↦ by rw [ne_eq, FaithfulSMul.algebraMap_eq_zero_iff]; exact hc k hk)).mpr
    (fun n _ ↦ by simp [moebiusFactorK]) n hn).symm

/-- `algebraMap a / algebraMap b` is integral iff `b ∣ a` (for `b ≠ 0`). -/
theorem isInteger_div_iff_dvd (a b : R) (hb : b ≠ 0) :
    IsLocalization.IsInteger R (algebraMap R K a / algebraMap R K b) ↔ b ∣ a := by
  have hbK : algebraMap R K b ≠ 0 := by
    simpa using (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective R K)).mpr hb
  constructor
  · rintro ⟨r, hr⟩
    rw [eq_div_iff hbK, ← map_mul] at hr
    exact ⟨r, ((FaithfulSMul.algebraMap_injective R K hr).symm.trans (mul_comm r b))⟩
  · rintro ⟨q, rfl⟩
    exact ⟨q, by rw [map_mul]; field_simp⟩

/-- The R-valued Möbius factor: the (unique, by injectivity) preimage of the fraction-field factor.
Junk value if the factor is not integral. -/
noncomputable def moebiusFactorR (c : ℕ → R) (n : ℕ) : R :=
  Function.invFun (algebraMap R (FractionRing R)) (moebiusFactorK c n)

@[simp] lemma moebiusFactorR_one (c : ℕ → R) : moebiusFactorR c 1 = c 1 := by
  rw [moebiusFactorR, moebiusFactorK_one,
    Function.leftInverse_invFun (FaithfulSMul.algebraMap_injective R (FractionRing R))]

variable [UniqueFactorizationMonoid R] [NormalizedGCDMonoid R]

section Factorization
variable [DecidableEq R]

lemma factorization_prod {ι : Type*} {s : Finset ι} {f : ι → R} (hf : ∀ i ∈ s, f i ≠ 0) (p : R) :
    (factorization (∏ i ∈ s, f i)) p = ∑ i ∈ s, (factorization (f i)) p := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, factorization_mul (hf a (by simp))
        (Finset.prod_ne_zero_iff.mpr fun i hi ↦ hf i (by simp [hi])), Finsupp.add_apply,
      Finset.sum_insert ha, ih fun i hi ↦ hf i (by simp [hi])]

/-- The valuation gap `v_p(numProd) - v_p(denProd)` is the Möbius transform of `v_p ∘ c`. -/
lemma factorization_numProd_sub_denProd {c : ℕ → R} (hc : ∀ d ≥ 1, c d ≠ 0) (n : ℕ) (p : R) :
    (factorization (numProd c n) p : ℤ) - (factorization (denProd c n) p : ℤ)
      = ∑ x ∈ n.divisorsAntidiagonal, (μ x.1) * (factorization (c x.2) p : ℤ) := by
  have hcx (x : ℕ × ℕ) (hx : x ∈ n.divisorsAntidiagonal) : c x.2 ≠ 0 :=
    hc x.2 (Nat.pos_of_ne_zero (Nat.right_ne_zero_of_mem_divisorsAntidiagonal hx))
  rw [numProd, denProd, factorization_prod (fun x hx ↦ hcx x (Finset.mem_of_mem_filter x hx)),
    factorization_prod (fun x hx ↦ hcx x (Finset.mem_of_mem_filter x hx))]
  rw [Finset.sum_filter, Finset.sum_filter]
  push_cast
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rcases moebius_eq_or x.1 with h | h | h <;> simp [h]

omit [IsDomain R] in
/-- The `p`-multiplicity of a gcd is the minimum of the multiplicities. -/
theorem factorization_gcd_min (a b : R) (ha : a ≠ 0) (hb : b ≠ 0) (p : R) :
    (factorization (gcd a b)) p = min ((factorization a) p) ((factorization b) p) := by
  have hg : gcd a b ≠ 0 := gcd_ne_zero_of_left ha
  simp only [factorization_eq_count]
  refine le_antisymm (le_min
    (Multiset.count_le_of_le p ((dvd_iff_normalizedFactors_le_normalizedFactors hg ha).mp
      (gcd_dvd_left a b)))
    (Multiset.count_le_of_le p ((dvd_iff_normalizedFactors_le_normalizedFactors hg hb).mp
      (gcd_dvd_right a b)))) ?_
  by_cases hp : Irreducible p ∧ normalize p = p
  · obtain ⟨hpi, hpn⟩ := hp
    set k := min ((normalizedFactors a).count p) ((normalizedFactors b).count p)
    have hcount (x : R) (hx : x ≠ 0) :
        emultiplicity p x = ((normalizedFactors x).count p : ℕ∞) := by
      rw [emultiplicity_eq_count_normalizedFactors hpi hx, hpn]
    have hda : p ^ k ∣ a := pow_dvd_iff_le_emultiplicity.mpr (by
      rw [hcount a ha]; exact_mod_cast min_le_left _ _)
    have hdb : p ^ k ∣ b := pow_dvd_iff_le_emultiplicity.mpr (by
      rw [hcount b hb]; exact_mod_cast min_le_right _ _)
    have hgd := pow_dvd_iff_le_emultiplicity.mp (dvd_gcd hda hdb)
    rw [hcount _ hg] at hgd
    exact_mod_cast hgd
  · rw [Multiset.count_eq_zero.mpr fun hmem ↦ hp
      ⟨irreducible_of_normalized_factor p hmem, normalize_normalized_factor p hmem⟩,
      Multiset.count_eq_zero.mpr fun hmem ↦ hp
      ⟨irreducible_of_normalized_factor p hmem, normalize_normalized_factor p hmem⟩]
    simp

omit [IsDomain R] in
/-- `v_p ∘ c` is a `gcd`-`min` function when `c` is a strong divisibility sequence. -/
lemma factorization_c_gcd_min {c : ℕ → R} (hc : ∀ d ≥ 1, c d ≠ 0)
    (hsd : ∀ m n, Associated (gcd (c m) (c n)) (c (m.gcd n))) (p : R) :
    ∀ x ≥ 1, ∀ y ≥ 1, (factorization (c (x.gcd y)) p)
      = min (factorization (c x) p) (factorization (c y) p) := by
  intro x hx y hy
  rw [factorization_eq_count, ← (hsd x y).normalizedFactors_eq, ← factorization_eq_count,
    factorization_gcd_min (c x) (c y) (hc x hx) (hc y hy)]


omit [DecidableEq R] in
theorem denProd_dvd_numProd {c : ℕ → R} (hc : ∀ d ≥ 1, c d ≠ 0)
    (hsd : ∀ m n, Associated (gcd (c m) (c n)) (c (m.gcd n))) (n : ℕ) (hn : 1 ≤ n) :
    denProd c n ∣ numProd c n := by
  classical
  have hcx (x : ℕ × ℕ) (hx : x ∈ n.divisorsAntidiagonal) : c x.2 ≠ 0 :=
    hc x.2 (Nat.pos_of_ne_zero (Nat.right_ne_zero_of_mem_divisorsAntidiagonal hx))
  have hnum : numProd c n ≠ 0 := Finset.prod_ne_zero_iff.mpr fun x hx ↦
    hcx x (Finset.mem_of_mem_filter x hx)
  have hden : denProd c n ≠ 0 := Finset.prod_ne_zero_iff.mpr fun x hx ↦
    hcx x (Finset.mem_of_mem_filter x hx)
  rw [dvd_iff_normalizedFactors_le_normalizedFactors hden hnum, Multiset.le_iff_count]
  intro p
  rw [← factorization_eq_count, ← factorization_eq_count]
  have hge : (0 : ℤ) ≤ ∑ x ∈ n.divisorsAntidiagonal, (μ x.1) * (factorization (c x.2) p : ℤ) :=
    moebius_transform_nonneg (fun d ↦ factorization (c d) p)
      (factorization_c_gcd_min hc hsd p) n hn
  have heq := factorization_numProd_sub_denProd hc n p
  omega

end Factorization

/-- **Integrality (approach a).** For a nowhere-zero strong divisibility sequence `c` in a UFD `R`,
the fraction-field Möbius factor `moebiusFactorK c n` lies in the image of `R`. -/
theorem moebiusFactorK_isInteger {c : ℕ → R} (hc : ∀ d ≥ 1, c d ≠ 0)
    (hsd : ∀ m n, Associated (gcd (c m) (c n)) (c (m.gcd n))) (n : ℕ) (hn : 1 ≤ n) :
    IsLocalization.IsInteger R (moebiusFactorK (K := K) c n) := by
  classical
  have hden : denProd c n ≠ 0 := Finset.prod_ne_zero_iff.mpr fun x hx ↦
    hc x.2 (Nat.pos_of_ne_zero (Nat.right_ne_zero_of_mem_divisorsAntidiagonal
      (Finset.mem_of_mem_filter x hx)))
  rw [moebiusFactorK_eq_div hc]
  exact (isInteger_div_iff_dvd (numProd c n) (denProd c n) hden).mpr
    (denProd_dvd_numProd hc hsd n hn)

/-- **API lemma.** In any fraction field `K` of `R`, the image of `moebiusFactorR c n` is the
Möbius formula (for a nowhere-zero strong divisibility sequence). -/
theorem algebraMap_moebiusFactorR {c : ℕ → R} (hc : ∀ d ≥ 1, c d ≠ 0)
    (hsd : ∀ m n, Associated (gcd (c m) (c n)) (c (m.gcd n))) (n : ℕ) (hn : 1 ≤ n) :
    algebraMap R K (moebiusFactorR c n) = moebiusFactorK (K := K) c n := by
  classical
  -- first over the canonical fraction ring FractionRing R
  obtain ⟨r, hr⟩ := moebiusFactorK_isInteger (K := FractionRing R) hc hsd n hn
  have hcanon : moebiusFactorR c n = r := by
    rw [moebiusFactorR, ← hr,
      Function.leftInverse_invFun (FaithfulSMul.algebraMap_injective R (FractionRing R)) r]
  rw [hcanon]
  -- transfer to arbitrary K via the unique R-algebra hom FractionRing R →+* K
  let ψ : FractionRing R →+* K := IsFractionRing.lift (FaithfulSMul.algebraMap_injective R K)
  have hψc (x : R) : ψ (algebraMap R (FractionRing R) x) = algebraMap R K x :=
    IsFractionRing.lift_algebraMap _ x
  have hnat : ψ (moebiusFactorK (K := FractionRing R) c n) = moebiusFactorK (K := K) c n := by
    rw [moebiusFactorK, moebiusFactorK, map_prod]
    exact Finset.prod_congr rfl fun x _ ↦ by rw [map_zpow₀, hψc]
  rw [← hnat, ← hr, hψc r]

/-- Möbius inversion in `R`: `c n = ∏_{d ∣ n} moebiusFactorR c d` for a nowhere-zero strong
divisibility sequence. -/
theorem prod_moebiusFactorR {c : ℕ → R} (hc : ∀ d ≥ 1, c d ≠ 0)
    (hsd : ∀ m n, Associated (gcd (c m) (c n)) (c (m.gcd n))) (n : ℕ) (hn : 1 ≤ n) :
    c n = ∏ d ∈ n.divisors, moebiusFactorR c d := by
  classical
  apply FaithfulSMul.algebraMap_injective R (FractionRing R)
  rw [map_prod, Finset.prod_congr rfl fun d hd ↦
      algebraMap_moebiusFactorR hc hsd d (Nat.pos_of_mem_divisors hd),
    prod_moebiusFactorK hc n hn]

section Coprimality

variable [DecidableEq R]

omit [DecidableEq R] in
/-- The defining identity of the `R`-valued factor: `β_n · denProd = numProd`. -/
theorem moebiusFactorR_mul_denProd {c : ℕ → R} (hc : ∀ d ≥ 1, c d ≠ 0)
    (hsd : ∀ m n, Associated (gcd (c m) (c n)) (c (m.gcd n))) (n : ℕ) (hn : 1 ≤ n) :
    moebiusFactorR c n * denProd c n = numProd c n := by
  classical
  apply FaithfulSMul.algebraMap_injective R (FractionRing R)
  have hden : algebraMap R (FractionRing R) (denProd c n) ≠ 0 := by
    rw [ne_eq, FaithfulSMul.algebraMap_eq_zero_iff, denProd, Finset.prod_eq_zero_iff]
    push Not
    exact fun x hx ↦ hc x.2 (Nat.pos_of_ne_zero
      (Nat.right_ne_zero_of_mem_divisorsAntidiagonal (Finset.mem_of_mem_filter x hx)))
  rw [map_mul, algebraMap_moebiusFactorR hc hsd n hn, moebiusFactorK_eq_div hc,
    div_mul_cancel₀ _ hden]

omit [DecidableEq R] in
theorem moebiusFactorR_ne_zero {c : ℕ → R} (hc : ∀ d ≥ 1, c d ≠ 0)
    (hsd : ∀ m n, Associated (gcd (c m) (c n)) (c (m.gcd n))) (n : ℕ) (hn : 1 ≤ n) :
    moebiusFactorR c n ≠ 0 := by
  classical
  intro h0
  have := moebiusFactorR_mul_denProd hc hsd n hn
  rw [h0, zero_mul] at this
  refine absurd this.symm ?_
  rw [numProd, Finset.prod_eq_zero_iff]
  push Not
  exact fun x hx ↦ hc x.2 (Nat.pos_of_ne_zero
    (Nat.right_ne_zero_of_mem_divisorsAntidiagonal (Finset.mem_of_mem_filter x hx)))

/-- `v_p(β_n)` is the Möbius transform of `v_p ∘ c`. -/
theorem factorization_moebiusFactorR {c : ℕ → R} (hc : ∀ d ≥ 1, c d ≠ 0)
    (hsd : ∀ m n, Associated (gcd (c m) (c n)) (c (m.gcd n))) (n : ℕ) (hn : 1 ≤ n) (p : R) :
    (factorization (moebiusFactorR c n) p : ℤ)
      = ∑ x ∈ n.divisorsAntidiagonal, (μ x.1) * (factorization (c x.2) p : ℤ) := by
  have hβden := moebiusFactorR_mul_denProd hc hsd n hn
  have hden : denProd c n ≠ 0 := by
    rw [denProd, ne_eq, Finset.prod_eq_zero_iff]
    push Not
    exact fun x hx ↦ hc x.2 (Nat.pos_of_ne_zero
      (Nat.right_ne_zero_of_mem_divisorsAntidiagonal (Finset.mem_of_mem_filter x hx)))
  have hkey : factorization (moebiusFactorR c n) p + factorization (denProd c n) p
      = factorization (numProd c n) p := by
    rw [← Finsupp.add_apply, ← factorization_mul (moebiusFactorR_ne_zero hc hsd n hn) hden,
      hβden]
  have := factorization_numProd_sub_denProd hc n p
  omega

/-- If `v_p ∘ c` has the constant-valuation shape (value `E` exactly on the multiples of `m`),
then `v_p(β_n)` is supported at the single index `n = m`. -/
theorem factorization_moebiusFactorR_shape {c : ℕ → R} (hc : ∀ d ≥ 1, c d ≠ 0)
    (hsd : ∀ m n, Associated (gcd (c m) (c n)) (c (m.gcd n))) (p : R) {m E : ℕ} (hm : 1 ≤ m)
    (hshape : ∀ k ≥ 1, factorization (c k) p = if m ∣ k then E else 0) (n : ℕ) (hn : 1 ≤ n) :
    factorization (moebiusFactorR c n) p = if n = m then E else 0 := by
  have hpos : ∀ x ∈ n.divisorsAntidiagonal, 1 ≤ x.2 := fun x hx ↦
    Nat.pos_of_ne_zero (Nat.right_ne_zero_of_mem_divisorsAntidiagonal hx)
  have hmain : (factorization (moebiusFactorR c n) p : ℤ) = if n = m then (E : ℤ) else 0 := by
    rw [factorization_moebiusFactorR hc hsd n hn p,
      Finset.sum_congr rfl fun x hx ↦ congrArg ((μ x.1 : ℤ) * ·) (by
        rw [hshape x.2 (hpos x hx), Nat.cast_ite, Nat.cast_zero]),
      Finset.sum_mul_ite_const n.divisorsAntidiagonal]
    by_cases hMn : m ∣ n
    · grind [moebius_restricted_sum m n hm hn hMn]
    · have hempty : (n.divisorsAntidiagonal.filter (fun x ↦ m ∣ x.2)) = ∅ := by
        refine Finset.filter_eq_empty_iff.mpr fun x hx ↦ ?_
        rw [Nat.mem_divisorsAntidiagonal] at hx
        exact fun hMx ↦ hMn (dvd_trans hMx ⟨x.1, by rw [← hx.1]; ring⟩)
      have hnM : n ≠ m := fun h ↦ hMn (h ▸ dvd_refl m)
      simp [hempty, hnM]
  split_ifs at hmain ⊢ <;> exact_mod_cast hmain

/-- **Pairwise relative primality of the Möbius factors** of a strong divisibility sequence with
the constant-valuation property: distinct factors share no prime. -/
theorem moebiusFactorR_isRelPrime {c : ℕ → R} (hc : ∀ d ≥ 1, c d ≠ 0)
    (hsd : ∀ m n, Associated (gcd (c m) (c n)) (c (m.gcd n)))
    (hshape : ∀ p : R, Prime p → normalize p = p →
      ∃ m ≥ 1, ∃ E : ℕ, ∀ k ≥ 1, factorization (c k) p = if m ∣ k then E else 0)
    (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (hmn : m ≠ n) :
    IsRelPrime (moebiusFactorR c m) (moebiusFactorR c n) := by
  intro d hdm hdn
  by_contra hdu
  have hd0 : d ≠ 0 := fun h ↦
    moebiusFactorR_ne_zero hc hsd m hm (zero_dvd_iff.mp (h ▸ hdm))
  obtain ⟨q, hq, hqd⟩ := WfDvdMonoid.exists_irreducible_factor hdu hd0
  replace hq : Prime q := hq.prime
  set p := normalize q with hp
  have hpq : Prime p := (associated_normalize q).prime hq
  have hcount (k : ℕ) (hk : 1 ≤ k) (hdvd : q ∣ moebiusFactorR c k) :
      1 ≤ factorization (moebiusFactorR c k) p := by
    have h1 : (1 : ℕ∞) ≤ emultiplicity q (moebiusFactorR c k) := by
      rw [← pow_one q] at hdvd
      exact pow_dvd_iff_le_emultiplicity.mp (by rwa [pow_one] at hdvd ⊢) |>.trans_eq rfl
    rw [emultiplicity_eq_count_normalizedFactors hq.irreducible
      (moebiusFactorR_ne_zero hc hsd k hk)] at h1
    rw [factorization_eq_count]
    exact_mod_cast h1
  obtain ⟨M, hM1, E, hE⟩ := hshape p hpq (normalize_idem q)
  have h1 := factorization_moebiusFactorR_shape hc hsd p hM1 hE m hm
  have h2 := factorization_moebiusFactorR_shape hc hsd p hM1 hE n hn
  have hm' := hcount m hm (hqd.trans hdm)
  have hn' := hcount n hn (hqd.trans hdn)
  rw [h1] at hm'
  rw [h2] at hn'
  split_ifs at hm' hn' with e1 e2
  · exact hmn (e1.trans e2.symm)
  all_goals lia

end Coprimality
