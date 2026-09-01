/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathlib.Data.ENat.Lattice
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.UniqueFactorizationDomain.Finsupp
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity

/-!
# Unique factorization lemmas

Auxiliary material for the formalization of M. Stoll, *Galois groups over ℚ of some iterated
polynomials*, Arch. Math. 59 (1992), 239-244; upstreaming candidates for Mathlib.
-/

open UniqueFactorizationMonoid in
/-- If `σ` is a multiplicative automorphism of a normalization UFD and `σ p` is associated to
`p`, then `normalize ∘ σ` permutes the multiset of normalized factors of `p`. -/
lemma normalizedFactors_map_mulEquiv_eq {α : Type*} [CommMonoidWithZero α]
    [NormalizationMonoid α] [UniqueFactorizationMonoid α] (σ : α ≃* α) {p : α} (hp0 : p ≠ 0)
    (hassoc : Associated (σ p) p) :
    (normalizedFactors p).map (fun q ↦ normalize (σ q)) = normalizedFactors p := by
  have hIrr2 : ∀ q ∈ (normalizedFactors p).map σ, Irreducible q := by
    intro q hq
    obtain ⟨q', hq', rfl⟩ := Multiset.mem_map.mp hq
    exact (MulEquiv.irreducible_iff σ).mpr (irreducible_of_normalized_factor q' hq')
  have hprod : Associated ((normalizedFactors p).map σ).prod p := by
    rw [← map_multiset_prod]
    exact ((prod_normalizedFactors hp0).map σ.toMonoidHom).trans hassoc
  calc (normalizedFactors p).map (fun q ↦ normalize (σ q))
      = ((normalizedFactors p).map σ).map normalize := by rw [Multiset.map_map]; rfl
    _ = normalizedFactors ((normalizedFactors p).map σ).prod :=
        (normalizedFactors_prod_eq _ hIrr2).symm
    _ = normalizedFactors p := hprod.normalizedFactors_eq

section Factorization

open UniqueFactorizationMonoid

variable {R : Type*} [CommMonoidWithZero R] [UniqueFactorizationMonoid R]
    [NormalizationMonoid R] [DecidableEq R]

/-- `p ^ k ∣ x` iff `k` is at most the multiplicity of a normalized prime `p` in `x ≠ 0`. -/
lemma pow_dvd_iff_le_factorization {p x : R} (hp : Prime p) (hpn : normalize p = p) (hx : x ≠ 0)
    {k : ℕ} : p ^ k ∣ x ↔ k ≤ factorization x p := by
  rw [factorization_eq_count, pow_dvd_iff_le_emultiplicity,
    emultiplicity_eq_count_normalizedFactors hp.irreducible hx, hpn, Nat.cast_le]

/-- A normalized prime `p` divides `x ≠ 0` iff its multiplicity in `x` is positive. -/
lemma one_le_factorization_iff_dvd {p x : R} (hp : Prime p) (hpn : normalize p = p) (hx : x ≠ 0) :
    1 ≤ factorization x p ↔ p ∣ x := by
  simpa using (pow_dvd_iff_le_factorization hp hpn hx (k := 1)).symm

/-- The multiplicity of a normalized prime `p` in `x ≠ 0` vanishes iff `p ∤ x`. -/
lemma factorization_eq_zero_iff_not_dvd {p x : R} (hp : Prime p) (hpn : normalize p = p)
    (hx : x ≠ 0) : factorization x p = 0 ↔ ¬p ∣ x := by
  rw [← one_le_factorization_iff_dvd hp hpn hx]
  lia

end Factorization

section PeriodicShape

open UniqueFactorizationMonoid

variable {S : Type*} [CommRing S] [UniqueFactorizationMonoid S]
    [NormalizationMonoid S] [DecidableEq S]

/-- The multiplicity at `p` is determined by the residue mod `p ^ (E+1)`: if `v_p y = E` and
`p ^ (E+1) ∣ x - y`, then `v_p x = E`. -/
theorem factorization_eq_of_dvd_sub {p : S} (hp : Prime p) (hpn : normalize p = p)
    {x y : S} (hx : x ≠ 0) (hy : y ≠ 0) {E : ℕ} (hyE : factorization y p = E)
    (hcong : p ^ (E + 1) ∣ x - y) : factorization x p = E := by
  have hpEy : p ^ E ∣ y := (pow_dvd_iff_le_factorization hp hpn hy).mpr (by lia)
  have hpEx : p ^ E ∣ x := by
    have h1 : p ^ E ∣ x - y := (pow_dvd_pow p (by lia : E ≤ E + 1)).trans hcong
    simpa using dvd_add h1 hpEy
  have hnotEx : ¬ p ^ (E + 1) ∣ x := fun hcon ↦ by
    have hyd : p ^ (E + 1) ∣ y := by
      have hyeq : y = x - (x - y) := by ring
      rw [hyeq]; exact dvd_sub hcon hcong
    have := (pow_dvd_iff_le_factorization hp hpn hy).mp hyd
    lia
  have h1 := (pow_dvd_iff_le_factorization hp hpn hx).mp hpEx
  have h2 : ¬ (E + 1 ≤ factorization x p) := fun hle ↦
    hnotEx ((pow_dvd_iff_le_factorization hp hpn hx).mpr hle)
  lia

/-- If a sequence `x` in a UFD is nonzero on `[1,∞)`, first `p`-divisible at index `m ≥ 2` with
`p ∤ x (m+1)`, and periodic modulo `p ^ (E+1)` with period `m` from index `2` on (where
`E = v_p (x m)`), then `v_p (x n) = E` when `m ∣ n` and `0` otherwise. -/
theorem factorization_periodic_shape {p : S} (hp : Prime p) (hpn : normalize p = p)
    (x : ℕ → S) (m E : ℕ) (hm : 2 ≤ m) (hne : ∀ n ≥ 1, x n ≠ 0)
    (hE : factorization (x m) p = E)
    (hmin : ∀ k < m, ¬ (1 ≤ k ∧ p ∣ x k)) (hpm1 : ¬ p ∣ x (m + 1))
    (hper : ∀ n ≥ 2, p ^ (E + 1) ∣ x (n + m) - x n) :
    ∀ n ≥ 1, factorization (x n) p = if m ∣ n then E else 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases Nat.lt_or_ge n (m + 2) with hsmall | hbig
    · rcases Nat.lt_or_ge n m with hlt | hge2
      · rw [ite_eq_right (fun hdvd ↦ by have := Nat.le_of_dvd (by lia) hdvd; lia),
          factorization_eq_zero_iff_not_dvd hp hpn (hne n hn)]
        exact fun hd ↦ hmin n hlt ⟨hn, hd⟩
      · rcases Nat.lt_or_ge n (m + 1) with hnm | hnm1
        · rw [show n = m from by lia, ite_eq_left (dvd_refl m), hE]
        · rw [show n = m + 1 from by lia, ite_eq_right (by
            rw [Nat.dvd_add_self_left]; intro hm1; have := Nat.le_of_dvd (by lia) hm1; lia),
            factorization_eq_zero_iff_not_dvd hp hpn (hne (m + 1) (by lia))]
          exact hpm1
    · have hge1 : 1 ≤ n - m := by lia
      have ihval := ih (n - m) (by lia) hge1
      have hcong : p ^ (E + 1) ∣ x n - x (n - m) := by
        have := hper (n - m) (by lia); rwa [show (n - m) + m = n from by lia] at this
      have hmdvd_iff : m ∣ n ↔ m ∣ n - m :=
        ⟨fun h ↦ Nat.dvd_sub h (dvd_refl m),
          fun h ↦ by rw [show n = (n - m) + m from by lia]; exact Nat.dvd_add h (dvd_refl m)⟩
      by_cases hmn : m ∣ n
      · rw [ite_eq_left hmn]; rw [ite_eq_left (hmdvd_iff.mp hmn)] at ihval
        exact factorization_eq_of_dvd_sub hp hpn (hne n hn) (hne (n - m) hge1) ihval hcong
      · rw [ite_eq_right hmn]; rw [ite_eq_right (fun h ↦ hmn (hmdvd_iff.mpr h))] at ihval
        have hnpnm : ¬ p ∣ x (n - m) :=
          (factorization_eq_zero_iff_not_dvd hp hpn (hne (n - m) hge1)).mp ihval
        rw [factorization_eq_zero_iff_not_dvd hp hpn (hne n hn)]
        refine fun hd ↦ hnpnm ?_
        have hxnm : x (n - m) = x n - (x n - x (n - m)) := by ring
        rw [hxnm]
        exact dvd_sub hd (dvd_trans (dvd_pow_self p (by lia : E + 1 ≠ 0)) hcong)

end PeriodicShape
