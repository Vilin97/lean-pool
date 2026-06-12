/-
Copyright (c) 2026 James Huang, Samuël Borza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Huang, Samuël Borza
-/
import LeanPool.IsTranscendentalPi.NivenPolynomials
import LeanPool.IsTranscendentalPi.SymmetricPolynomials
import Mathlib.Algebra.Polynomial.OfFn

/-!
# Subset-sum polynomial

The polynomial `∏ x ∈ s, (X - C x)` attached to a multiset `s` and its factorization
according to the vanishing subset sums, used to track integer divisibility in
Niven's argument.
-/

open Polynomial
open Multiset

open scoped Polynomial
open scoped BigOperators

noncomputable section

/-- The polynomial `∏ x ∈ s, (X - C x)` associated to a multiset `s`. -/
def polyOfMultiset {S : Type*} [CommRing S] (s : Multiset S) : Polynomial S :=
  (Multiset.map (fun a : S => X - C a) s).prod

/-- `∏_{a ∈ s} (X - a) = X^{#{a ∈ s, a = 0}} ∏_{a ∈ s, a ≠ 0} (X - a)`. -/
lemma polyOfMultiset_split_zero {S : Type*} [CommRing S] [DecidableEq S] (s : Multiset S) :
    polyOfMultiset s = X ^ (s.count 0) * polyOfMultiset (s.filter (fun x => x ≠ 0)) := by
  rw [polyOfMultiset, ← Multiset.filter_add_not (s := s) (p := fun x => x = 0),
    Multiset.map_add, Multiset.prod_add]
  nth_rewrite 1 [Multiset.filter_eq' s 0]
  simp [polyOfMultiset]

/-- The multiset `{X₀, …, Xₙ₋₁}` inside `ℤ[X₀, …, Xₙ₋₁]`. -/
def varsFin (n : ℕ) : Multiset (MvPolynomial (Fin n) ℤ) := Finset.univ.val.map MvPolynomial.X

/-- The polynomial whose roots are `{ ∑_{x ∈ t} x | t ⊆ s }` for a given multiset `s`. -/
def polyOfSubsetSums {S : Type*} [CommRing S] (s : Multiset S) : Polynomial S :=
  polyOfMultiset (subsetSums s)

/-- The polynomial whose roots are `{ ∑_{x ∈ t} x ≠ 0 | t ⊆ s }` for a given multiset `s`. -/
def polyOfNonzeroSubsetSums {S : Type*} [CommRing S] [DecidableEq S] (s : Multiset S) :
    Polynomial S := polyOfMultiset (nonzeroSubsetSums s)

/-- The polynomial whose roots are `{ ∑_{x ∈ t} x ≠ 0 | t ⊆ s }` for a given multiset `s`
is monic. -/
lemma polyOfNonzeroSubsetSums_monic {S : Type*} [CommRing S] [DecidableEq S] (s : Multiset S) :
    (polyOfNonzeroSubsetSums s).Monic := by
  exact Polynomial.monic_multisetProd_X_sub_C (nonzeroSubsetSums s)

/-- If `{ ∑_{x ∈ t} x ≠ 0 | t ⊆ s }` is indexed by `a : Fin n → S`, then every `a i` is nonzero. -/
lemma ne_zero_of_nonzeroSubsetSums_eq_valuesFin
    {S : Type*} [AddCommMonoid S] [DecidableEq S] {s : Multiset S} {n : ℕ} {a : Fin n → S}
    (ha : nonzeroSubsetSums s = valuesFin a) (i : Fin n) : a i ≠ 0 := by
  exact ne_zero_of_mem_nonzeroSubsetSums (s := s) <| by
    simpa [ha] using (show a i ∈ valuesFin a by simp [valuesFin])

/-- The `r`-th elementary symmetric polynomial in `{ ∑_{i ∈ I} Xᵢ | I ⊆ {0, …, n-1} }`. -/
def esymmVarsFinSubsetSums (n r : ℕ) : MvPolynomial (Fin n) ℤ := (subsetSums (varsFin n)).esymm r

/-- Taking powersets commutes with mapping a function over a multiset. -/
lemma powerset_map_eq {α β : Type*} (f : α → β) (s : Multiset α) :
    Multiset.map (Multiset.map f) s.powerset = (Multiset.map f s).powerset := by
  rw [← Multiset.bind_powerset_len s, Multiset.map_bind]
  simp_rw [← Multiset.powersetCard_map]
  rw [← Multiset.bind_powerset_len (Multiset.map f s), Multiset.card_map]

/-- The multiset `{X₀, …, Xₙ₋₁}` is invariant under permutation of the variables. -/
lemma varsFin_IsSymmetric (n : ℕ) (e : Equiv.Perm (Fin n)) :
    Multiset.map (MvPolynomial.rename e) (varsFin n) = varsFin n := by
  rw [varsFin, Multiset.map_map]
  simpa [Function.comp_def] using
    e.ofFn_comp_perm (fun i : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) ℤ))

/-- The multiset of subset sums of `X₀, …, Xₙ₋₁` is invariant under permutation of the
variables. -/
lemma varsFinSubsetSums_IsSymmetric (n : ℕ) (e : Equiv.Perm (Fin n)) :
    Multiset.map (MvPolynomial.rename e) (subsetSums (varsFin n)) = subsetSums (varsFin n) := by
  rw [subsetSums, Multiset.map_map]
  simpa [Function.comp, map_multiset_sum, subsetSums, Multiset.map_map] using
    congrArg (Multiset.map Multiset.sum)
      ((powerset_map_eq (MvPolynomial.rename e) (varsFin n)).trans (by rw [varsFin_IsSymmetric]))

/-- Renaming variables commutes with the elementary symmetric polynomial of a multiset. -/
lemma multisetEsymm_IsSymmetric {n r : ℕ} (e : Equiv.Perm (Fin n))
    (s : Multiset (MvPolynomial (Fin n) ℤ)) :
    (MvPolynomial.rename e) (s.esymm r) = (Multiset.map (MvPolynomial.rename e) s).esymm r := by
  simp [Multiset.esymm, map_multiset_sum, map_multiset_prod, Multiset.powersetCard_map]

/-- The r-th elementary symmetric polynomial in `{ ∑_{i ∈ I} Xᵢ | I ⊆ {0, …, n-1} }`
 is symmetric. -/
lemma esymmVarsFinSubsetSums_isSymmetric (n r : ℕ) :
    MvPolynomial.IsSymmetric (esymmVarsFinSubsetSums n r) := by
  intro e
  simp [esymmVarsFinSubsetSums, multisetEsymm_IsSymmetric, varsFinSubsetSums_IsSymmetric]

/-- Evaluating `{X₀, …, Xₙ₋₁}` at `b` gives the multiset `{b₀, …, bₙ₋₁}`. -/
lemma aeval_varsFin {S : Type*} [CommRing S] (n : ℕ) (b : Fin n → S) :
    Multiset.map (MvPolynomial.aeval (σ := Fin n) (R := ℤ) (S₁ := S) b) (varsFin n) =
      valuesFin b := by
  rw [varsFin, valuesFin, Multiset.map_map]
  simp

/-- Evaluating the subset sums of `{X₀, …, Xₙ₋₁}` at `b` is the subset sums of `{b₀, …, bₙ₋₁}`. -/
lemma aeval_subsetSums {S : Type*} [CommRing S] (n : ℕ) (b : Fin n → S) :
    Multiset.map
        (MvPolynomial.aeval (σ := Fin n) (R := ℤ) (S₁ := S) b)
        (subsetSums (varsFin n)) =
      subsetSums (valuesFin b) := by
  simp_rw [← aeval_varsFin n b]
  rw [subsetSums, subsetSums, Multiset.map_map]
  simpa [Multiset.map_map, Function.comp, map_multiset_sum] using
    congrArg (Multiset.map Multiset.sum)
      (powerset_map_eq
        ((MvPolynomial.aeval (σ := Fin n) (R := ℤ) (S₁ := S) b).toAddMonoidHom) (varsFin n))

/-- Evaluating the `r`-th elementary symmetric polynomial in `{ ∑_{i ∈ I} Xᵢ | I ⊆ {0, …, n-1} }`
at `b` gives the `r`-th elementary symmetric polynomial in the subset sums of `{b₀, …, bₙ₋₁}`. -/
lemma aeval_esymmVarsFinSubsetSums
    {S : Type*} [CommRing S] (n r : ℕ) (b : Fin n → S) :
    MvPolynomial.aeval (σ := Fin n) (R := ℤ) (S₁ := S) b (esymmVarsFinSubsetSums n r) =
      (subsetSums (valuesFin b)).esymm r := by
  rw [esymmVarsFinSubsetSums]
  simpa [Multiset.esymm, map_multiset_sum, map_multiset_prod, Multiset.powersetCard_map,
    Multiset.map_map, Function.comp] using
    congrArg (fun t : Multiset S => t.esymm r) (aeval_subsetSums n b)

/-- The `k`-th coefficient of the polynomial whose roots are `{ ∑_{x ∈ t} x | t ⊆ b }`
is given by an elementary symmetric polynomial in `{ ∑_{i ∈ I} Xᵢ | I ⊆ {0, …, n-1} }` at `b`. -/
lemma coeff_polyOfSubsetSums
    {S : Type*} [CommRing S] (n : ℕ) (b : Fin n → S) (k : ℕ)
    (hk : k ≤ (subsetSums (valuesFin b)).card) :
    (polyOfSubsetSums (valuesFin b)).coeff k =
      MvPolynomial.aeval (σ := Fin n) (R := ℤ) (S₁ := S) b
        (((-1) ^ ((subsetSums (valuesFin b)).card - k))
          * esymmVarsFinSubsetSums n ((subsetSums (valuesFin b)).card - k)) := by
  rw [polyOfSubsetSums, polyOfMultiset,
    Multiset.prod_X_sub_C_coeff (s := subsetSums (valuesFin b)) (k := k) hk, map_mul,
    aeval_esymmVarsFinSubsetSums (n := n) (r := (subsetSums (valuesFin b)).card - k) (b := b)]
  simp

/-- If `B` is monic with roots `b₀, …, bₙ₋₁`, then the coefficients of the polynomial
whose roots are `{ ∑_{x ∈ t} x | t ⊆ b }` are polynomials in the coefficients of `B`. -/
lemma coeff_polyOfSubsetSums_as_coeff_poly
    {R S : Type*} [CommRing R] [Field S] [Algebra R S] [IsAlgClosed S]
    {n : ℕ} (B : R[X]) (b : Fin n → S) (hmonic : B.Monic) (hroots : B.aroots S = valuesFin b)
    {k : ℕ} (hk : k ≤ (subsetSums (valuesFin b)).card) :
    ∃ Q : MvPolynomial (Fin n) ℤ,
      ((polyOfSubsetSums (valuesFin b)).coeff k)
        = algebraMap R S (MvPolynomial.aeval (σ := Fin n) (R := ℤ) (S₁ := R)
          (fun i : Fin n => (-1) ^ (i.1 + 1) * B.coeff (n - (i.1 + 1))) Q) := by
  obtain ⟨Q, hQ⟩ := symmetric_poly_at_roots_eq_poly_of_esymm
    (B := B) (a := b) hmonic hroots
    (((-1 : ℤ) ^ ((subsetSums (valuesFin b)).card - k)) •
      esymmVarsFinSubsetSums n ((subsetSums (valuesFin b)).card - k))
    ((esymmVarsFinSubsetSums_isSymmetric n ((subsetSums (valuesFin b)).card - k)).smul
      (((-1 : ℤ) ^ ((subsetSums (valuesFin b)).card - k))))
  refine ⟨Q, ?_⟩
  rw [coeff_polyOfSubsetSums n b k hk]
  simpa [smul_eq_mul] using hQ

/-- If `B` is monic with roots `b₀, …, bₙ₋₁`, then the coefficients of the polynomial
whose roots are `{ ∑_{x ∈ t} x ≠ 0 | t ⊆ b }` are polynomials in the coefficients of `B`. -/
lemma coeff_polyOfNonzeroSubsetSums_as_coeff_poly
    {R S : Type*} [CommRing R] [Field S] [Algebra R S] [IsAlgClosed S] [DecidableEq S]
    {n k : ℕ} (B : R[X]) (b : Fin n → S)
    (hmonic : B.Monic) (hroots : B.aroots S = valuesFin b)
    (hk : k + (subsetSums (valuesFin b)).count 0 ≤ (subsetSums (valuesFin b)).card) :
    ∃ Q : MvPolynomial (Fin n) ℤ,
      ((polyOfNonzeroSubsetSums (valuesFin b)).coeff k)
        = algebraMap R S (MvPolynomial.aeval (σ := Fin n) (R := ℤ) (S₁ := R)
          (fun i : Fin n => (-1) ^ (i.1 + 1) * B.coeff (n - (i.1 + 1))) Q) := by
  obtain ⟨Q, hQ⟩ := coeff_polyOfSubsetSums_as_coeff_poly (B := B) (b := b) hmonic hroots
    (k := k + (subsetSums (valuesFin b)).count 0) hk
  refine ⟨Q, ?_⟩
  rw [← coeff_X_pow_mul (p := polyOfNonzeroSubsetSums (valuesFin b))
      (n := (subsetSums (valuesFin b)).count 0) (d := k), polyOfNonzeroSubsetSums,
      nonzeroSubsetSums, ← polyOfMultiset_split_zero (s := subsetSums (valuesFin b))]
  exact hQ

/-- From a monic polynomial `B` with roots `a₀, …, aₙ₋₁`, one obtains a polynomial over the
base ring whose image has roots the nonzero subset sums of the `a_i`. -/
lemma polyOfNonzeroSubsetSums_as_poly
    {R S : Type*} [CommRing R] [Field S] [Algebra R S] [IsAlgClosed S] [DecidableEq S]
    {n : ℕ} (B : R[X]) (a : Fin n → S) (hmonic : B.Monic) (hroots : B.aroots S = valuesFin a) :
      ∃ P : R[X], P.map (algebraMap R S) = polyOfNonzeroSubsetSums (valuesFin a) := by
  obtain ⟨P, hP⟩ : ∃ P : R[X],
      P.map (algebraMap R S) = polyOfNonzeroSubsetSums (valuesFin a) := by
    rw [← Polynomial.mem_lifts, Polynomial.lifts_iff_coeff_lifts]
    intro k
    by_cases hk : k + (subsetSums (valuesFin a)).count 0 ≤ (subsetSums (valuesFin a)).card
    · obtain ⟨Q, hQ⟩ := coeff_polyOfNonzeroSubsetSums_as_coeff_poly B a hmonic hroots hk
      refine ⟨MvPolynomial.aeval (σ := Fin n) (R := ℤ) (S₁ := R)
        (fun i : Fin n => (-1) ^ (i.1 + 1) * B.coeff (n - (i.1 + 1))) Q, ?_⟩
      simpa [eq_comm] using hQ
    · refine ⟨0, ?_⟩
      simp only [_root_.map_zero]
      symm
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      rw [polyOfNonzeroSubsetSums, polyOfMultiset, natDegree_multiset_prod_X_sub_C_eq_card,
        nonzeroSubsetSums]
      nth_rw 2 [← Multiset.filter_add_not (p := fun x : S => x = 0)
        (subsetSums (valuesFin a))] at hk
      rw [Multiset.count_eq_card_filter_eq, Multiset.card_add] at hk
      simp [eq_comm] at hk ⊢
      omega
  exact ⟨P, hP⟩

/-- Clearing denominators for a polynomial over `ℚ`: every rational polynomial
is a nonzero integer multiple of the image of some polynomial over `ℤ`. -/
lemma ClearDenominatorOf (T' : ℚ[X]) :
    ∃ (T : ℤ[X]) (c : ℤ), c ≠ 0 ∧ Polynomial.map (algebraMap ℤ ℚ) T = c • T' := by
  obtain ⟨c, hc, hT'⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) T'
  refine ⟨IsLocalization.integerNormalization (nonZeroDivisors ℤ) T', c,
    mem_nonZeroDivisors_iff_ne_zero.mp hc, hT'⟩

/-- The rescaled coefficient used to build the monic degree `d` polynomial attached to `T`.
Precisely, they are `cᵈ⁻¹⁻ᵏ Tₖ` for `k < d`, `= 1` for `k = d`, and `= 0` for `k > d` -/
def monicRescaleCoeff (T : ℤ[X]) (d : ℕ) (c : ℤ) (k : ℕ) : ℤ :=
  if k < d then c ^ (d - 1 - k) * T.coeff k else if k = d then 1 else 0

/-- The monic degree `d` polynomial obtained by rescaling the lower coefficients of `T`.
Precisely, it is the polynomial `Xᵈ + ∑ₖ₌₀ᵈ⁻¹ cᵈ⁻¹⁻ᵏ Tₖ Xᵏ` -/
def monicRescaleOf (T : ℤ[X]) (d : ℕ) (c : ℤ) : ℤ[X] :=
  Polynomial.ofFn (d + 1) fun i : Fin (d + 1) =>
    if (i : ℕ) = d then 1 else c ^ (d - 1 - i) * T.coeff i

/-- The coefficients of `Xᵈ + ∑ₖ₌₀ᵈ⁻¹ cᵈ⁻¹⁻ᵏ Tₖ Xᵏ`. -/
lemma coeff_monicRescaleOf (T : ℤ[X]) (d : ℕ) (c : ℤ) (k : ℕ) :
    (monicRescaleOf T d c).coeff k = monicRescaleCoeff T d c k := by
  by_cases hk : k < d + 1
  · rw [monicRescaleOf, Polynomial.ofFn_coeff_eq_val_of_lt _ hk]
    by_cases hkd : k = d
    · subst k
      simp [monicRescaleCoeff]
    · have hklt : k < d := by omega
      simp [hkd, hklt, monicRescaleCoeff]
  · rw [monicRescaleOf, Polynomial.ofFn_coeff_eq_zero_of_ge]
    · have hkd : d < k := by omega
      simp [monicRescaleCoeff, Nat.not_lt_of_ge (Nat.le_of_lt hkd), Nat.ne_of_gt hkd]
    · exact Nat.le_of_not_lt hk

/-- `Xᵈ + ∑ₖ₌₀ᵈ⁻¹ cᵈ⁻¹⁻ᵏ Tₖ Xᵏ` has degree `d`. -/
lemma natDegree_monicRescaleOf (T : ℤ[X]) (d : ℕ) (c : ℤ) :
    (monicRescaleOf T d c).natDegree = d := by
  refine Polynomial.natDegree_eq_of_le_of_coeff_ne_zero ?_ ?_
  · simpa [Nat.lt_succ_iff, monicRescaleOf] using
      (Polynomial.ofFn_natDegree_lt (show 1 ≤ d + 1 by omega)
        (fun i : Fin (d + 1) => if (i : ℕ) = d then 1 else c ^ (d - 1 - i) * T.coeff i))
  · simp [coeff_monicRescaleOf, monicRescaleCoeff]

/-- `Xᵈ + ∑ₖ₌₀ᵈ⁻¹ cᵈ⁻¹⁻ᵏ Tₖ Xᵏ` is monic. -/
lemma monic_monicRescaleOf (T : ℤ[X]) (d : ℕ) (c : ℤ) :
    (monicRescaleOf T d c).Monic := by
  apply Polynomial.monic_of_natDegree_le_of_coeff_eq_one d
  · rw [natDegree_monicRescaleOf]
  · simp [coeff_monicRescaleOf, monicRescaleCoeff]

/-- Coefficients of `Xᵈ + ∑ₖ₌₀ᵈ⁻¹ cᵈ⁻¹⁻ᵏ Tₖ Xᵏ` correspond to the coefficients of scaleRoots. -/
lemma coeff_monicRescaleOf_scaleRoots
    (T : ℤ[X]) (T' : ℚ[X]) (d : ℕ) (c : ℤ)
    (hmonic : T'.Monic) (hd : T'.natDegree = d)
    (hT : T.map (algebraMap ℤ ℚ) = C (c : ℚ) * T')
    (k : ℕ) :
    ((monicRescaleOf T d c).map (algebraMap ℤ ℚ)).coeff k =
      (T'.scaleRoots (c : ℚ)).coeff k := by
  have hcoeffT : ((T.coeff k : ℤ) : ℚ) = (c : ℚ) * T'.coeff k := by
    simpa [Polynomial.coeff_map, Polynomial.coeff_C_mul] using
      congrArg (fun P : ℚ[X] => P.coeff k) hT
  rw [Polynomial.coeff_map, coeff_monicRescaleOf, Polynomial.coeff_scaleRoots, hd]
  rcases lt_trichotomy k d with hk | hk | hk
  · rw [monicRescaleCoeff, if_pos hk]
    calc
      _ = (c : ℚ) ^ (d - 1 - k) * ((T.coeff k : ℤ) : ℚ) := by simp
      _ = (c : ℚ) ^ (d - 1 - k) * ((c : ℚ) * T'.coeff k) := by rw [hcoeffT]
      _ = T'.coeff k * (c : ℚ) ^ ((d - 1 - k) + 1) := by
            rw [pow_succ']
            ring
      _ = _ := by
            congr 2
            omega
  · have hlead : T'.coeff d = 1 := by
      simpa [hd] using hmonic.coeff_natDegree
    simp [monicRescaleCoeff, hk, hlead]
  · have hzero : T'.coeff k = 0 := by
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      simpa [hd] using hk
    have hne : k ≠ d := by omega
    simp [monicRescaleCoeff, Nat.not_lt_of_ge hk.le, hne, hzero]

/-- After mapping to `ℚ`, the monic rescaling is the `scaleRoots` of the monic rational
polynomial `T'`. -/
lemma monicRescaleOf_scaleRoots
    (T : ℤ[X]) (T' : ℚ[X]) (d : ℕ) (c : ℤ)
    (hmonic : T'.Monic) (hd : T'.natDegree = d)
    (hT : T.map (algebraMap ℤ ℚ) = C (c : ℚ) * T') :
    (monicRescaleOf T d c).map (algebraMap ℤ ℚ) = T'.scaleRoots (c : ℚ) := by
  exact Polynomial.ext fun k => coeff_monicRescaleOf_scaleRoots T T' d c hmonic hd hT k

/-- If `T = c T'` with `T'` monic of degree `d` and roots `a₀, …, a_{d-1}`,
then `Xᵈ + ∑ₖ₌₀ᵈ⁻¹ cᵈ⁻¹⁻ᵏ Tₖ Xᵏ` is the monic polynomial whose roots are `c a₀, …, c a_{d-1}`. -/
lemma aroots_monicRescaleOf
    (T : ℤ[X]) (T' : ℚ[X]) (d : ℕ) (c : ℤ) (a : Fin d → ℂ)
    (hc : c ≠ 0) (hmonic : T'.Monic) (hd : T'.natDegree = d)
    (hT : T.map (Int.castRingHom ℚ) = C (c : ℚ) * T')
    (hroots' : T'.aroots ℂ = valuesFin a) :
    (monicRescaleOf T d c).aroots ℂ = valuesFin (fun j : Fin d => (c : ℂ) * a j) := by
  rw [Polynomial.aroots_def] at hroots'
  rw [← Polynomial.aroots_map (S := ℚ) (R := ℂ) (p := monicRescaleOf T d c)]
  rw [monicRescaleOf_scaleRoots T T' d c hmonic hd hT, Polynomial.aroots_def]
  rw [Polynomial.map_scaleRoots T' (c : ℚ) (algebraMap ℚ ℂ) (by simp [hmonic.leadingCoeff])]
  rw [Polynomial.roots_scaleRoots
    (p := T'.map (algebraMap ℚ ℂ))
    (r := algebraMap ℚ ℂ (c : ℚ))
    (isUnit_iff_ne_zero.mpr (by simpa using (show (c : ℂ) ≠ 0 by exact_mod_cast hc)))]
  rw [hroots', valuesFin, valuesFin, Multiset.map_map]
  simp [Function.comp]

/-- If `T'` is the polynomial whose roots are `{ ∑_{x ∈ t} x ≠ 0 | t ⊆ s }`,
then `T'` is monic. -/
lemma monic_of_T' (T' : ℚ[X]) (d : ℕ) (r : Fin d → ℂ)
    (hT' : T'.map (algebraMap ℚ ℂ) = polyOfNonzeroSubsetSums (valuesFin r)) : T'.Monic := by
  apply Polynomial.monic_of_injective (algebraMap ℚ ℂ).injective
  simpa [hT'] using polyOfNonzeroSubsetSums_monic (valuesFin r)

/-- If `T'` is the polynomial whose roots are `{ ∑_{x ∈ t} x ≠ 0 | t ⊆ s }`,
then `deg(T')` is the number of those roots. -/
lemma natDegree_of_T'
    (T' : ℚ[X]) (d n : ℕ) (r : Fin d → ℂ) (a : Fin n → ℂ)
    (hT' : T'.map (algebraMap ℚ ℂ) = polyOfNonzeroSubsetSums (valuesFin r))
    (ha : nonzeroSubsetSums (valuesFin r) = valuesFin a) : T'.natDegree = n := by
  calc
    T'.natDegree = (nonzeroSubsetSums (valuesFin r)).card := by
      rw [← Polynomial.Monic.natDegree_map (monic_of_T' T' d r hT') (algebraMap ℚ ℂ), hT',
        polyOfNonzeroSubsetSums, polyOfMultiset, natDegree_multiset_prod_X_sub_C_eq_card]
    _ = n := by
      simpa [valuesFin] using congrArg Multiset.card ha

/-- If `T'` is the polynomial whose roots are `{ ∑_{x ∈ t} x ≠ 0 | t ⊆ s }`,
then its roots are exactly that multiset. -/
lemma aroots_of_T'
    (T' : ℚ[X]) (d n : ℕ) (r : Fin d → ℂ) (a : Fin n → ℂ)
    (hT' : T'.map (algebraMap ℚ ℂ) = polyOfNonzeroSubsetSums (valuesFin r))
    (ha : nonzeroSubsetSums (valuesFin r) = valuesFin a) : T'.aroots ℂ = valuesFin a := by
  rw [Polynomial.aroots_def]
  calc
    _ = (polyOfNonzeroSubsetSums (valuesFin r)).roots := by rw [hT']
    _ = nonzeroSubsetSums (valuesFin r) := by
      simp [polyOfNonzeroSubsetSums, polyOfMultiset]
    _ = _ := ha

/-- If `T'` is the polynomial whose roots are `{ ∑_{x ∈ t} x ≠ 0 | t ⊆ s }`, then `T'(0) ≠ 0`. -/
lemma aeval_zero_ne_zero_of_T'
    (T' : ℚ[X]) (d n : ℕ) (r : Fin d → ℂ) (a : Fin n → ℂ)
    (hT' : T'.map (algebraMap ℚ ℂ) = polyOfNonzeroSubsetSums (valuesFin r))
    (ha : nonzeroSubsetSums (valuesFin r) = valuesFin a) :
    aeval (0 : ℂ) T' ≠ 0 := by
  intro h0
  exact ne_zero_of_mem_nonzeroSubsetSums
    (by simpa [ha.symm, aroots_of_T' T' d n r a hT' ha] using
      ((Polynomial.mem_aroots (p := T') (a := (0 : ℂ))).2 ⟨(monic_of_T' T' d r hT').ne_zero, h0⟩))
    rfl

/-- If `T = c • T'`, and `T'` is the polynomial whose roots are `{ ∑_{x ∈ t} x ≠ 0 | t ⊆ s }`,
then the roots of `T` are also `{ ∑_{x ∈ t} x ≠ 0 | t ⊆ s }`. -/
lemma aroots_of_T
    (T : ℤ[X]) (T' : ℚ[X]) (c : ℤ) (d n : ℕ) (r : Fin d → ℂ) (a : Fin n → ℂ) (hc : c ≠ 0)
    (hT : T.map (Int.castRingHom ℚ) = c • T')
    (hT' : T'.map (algebraMap ℚ ℂ) = polyOfNonzeroSubsetSums (valuesFin r))
    (ha : nonzeroSubsetSums (valuesFin r) = valuesFin a) : T.aroots ℂ = valuesFin a := by
  have hmapC : T.map (algebraMap ℤ ℂ) = (c : ℂ) • (T'.map (algebraMap ℚ ℂ)) := by
    have hcomp : (algebraMap ℚ ℂ).comp (Int.castRingHom ℚ) = algebraMap ℤ ℂ :=
      RingHom.ext_int _ _
    simpa [Polynomial.map_map, hcomp, smul_eq_C_mul, map_mul] using
      congrArg (Polynomial.map (algebraMap ℚ ℂ)) hT
  calc
    _ = (T'.map (algebraMap ℚ ℂ)).aroots ℂ := by
      have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc
      rw [Polynomial.aroots_def, Polynomial.aroots_def, hmapC, Algebra.algebraMap_self,
        Polynomial.map_id]
      exact Polynomial.roots_smul_nonzero (Polynomial.map (algebraMap ℚ ℂ) T') hcC
    _ = T'.aroots ℂ := by simp [Polynomial.aroots_def]
    _ = _ := aroots_of_T' T' d n r a hT' ha

/-- If `c ≠ 0`, `T' ≠ 0`, and `c * T' = T ∈ ℤ[X]`, then `T ≠ 0`. -/
lemma RescaledOf_nonZero
    (T : ℤ[X]) (T' : ℚ[X]) (c : ℤ) (hc : c ≠ 0) (hT' : T' ≠ 0)
    (hT : T.map (algebraMap ℤ ℚ) = C (c : ℚ) * T') : T ≠ 0 := by
  intro h0
  exact
    mul_ne_zero (C_ne_zero.mpr (by simpa using hc : (c : ℚ) ≠ 0)) hT' (by simpa [h0] using hT.symm)

/-- If `c ≠ 0` and `c * T' = T ∈ ℤ[X]`, then `deg(T) = deg(T')`. -/
lemma RescaledOf_natDegree
    (T : ℤ[X]) (T' : ℚ[X]) (c : ℤ) (hc : c ≠ 0)
    (hT : T.map (Int.castRingHom ℚ) = C (c : ℚ) * T') : T.natDegree = T'.natDegree := by
  rw [← Polynomial.natDegree_map_eq_of_injective (f := Int.castRingHom ℚ) Int.cast_injective T,
    hT, Polynomial.natDegree_C_mul (by exact_mod_cast hc)]

/-- If `T'(0) ≠ 0` and `c * T' = T ∈ ℤ[X]`, then `T(0) ≠ 0`. -/
lemma RescaledOf_nonZero_at_Zero
    (T : ℤ[X]) (T' : ℚ[X]) (c : ℤ) (hc : c ≠ 0) (hT : T.map (Int.castRingHom ℚ) = C (c : ℚ) * T')
    (hT'0 : aeval (0 : ℂ) T' ≠ 0) : aeval (0 : ℂ) T ≠ 0 := by
  intro h0
  apply hT'0
  simp only [aeval_def, eval₂_at_zero, eq_ratCast, Rat.cast_eq_zero]
  exact_mod_cast
    (mul_eq_zero.mp (by
      rw [← Polynomial.coeff_C_mul, ← hT]
      simpa [Polynomial.coeff_map, Polynomial.aeval_def] using h0)).resolve_left
      (by norm_num [hc])

/-- If `T = c • T'`, and `T'` is the polynomial whose roots are
`{ ∑_{x ∈ t} x ≠ 0 | t ⊆ s }`, then `T(0) ≠ 0`. -/
lemma aeval_zero_ne_zero_of_T
    (T : ℤ[X]) (T' : ℚ[X]) (c : ℤ) (d n : ℕ) (r : Fin d → ℂ) (a : Fin n → ℂ)
    (hc : c ≠ 0) (hT : T.map (Int.castRingHom ℚ) = c • T')
    (hT' : T'.map (algebraMap ℚ ℂ) = polyOfNonzeroSubsetSums (valuesFin r))
    (ha : nonzeroSubsetSums (valuesFin r) = valuesFin a) :
    aeval (0 : ℂ) T ≠ 0 := by
  exact RescaledOf_nonZero_at_Zero T T' c hc
    (by
      rw [← smul_eq_C_mul]
      exact hT)
    (aeval_zero_ne_zero_of_T' T' d n r a hT' ha)
