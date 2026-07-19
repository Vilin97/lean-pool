/-
Copyright (c) 2026 Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Caleb L. Geiger
-/

import LeanPool.SingularModuli.QuadraticOrder.Prime.QuotientIso

/-!
# Prime classification, part 4: the ramified case

**Thesis.** §3.2, Proposition 3.2.1 — the *ramified* branch: a rational prime
`p` ramifies in `O_d` exactly when `p ∣ d`. Algebraically, `(p)` fails to be a
radical ideal: `O/(p)` acquires a nonzero nilpotent (the dual-numbers picture).

**This file proves:**

* `tau_sq_mem_span_p_of_p_dvd_d` — `τ² ∈ (p)` when `p ∣ d`
* `tau_not_mem_span_p`           — `τ ∉ (p)` (always; `τ` is a basis element)
* `span_p_not_isRadical_of_p_dvd_d` — together: `(p)` is not radical
* `prime_ramified_iff`           — `(p)` not radical ↔ `p ∣ d`

The reverse direction of `prime_ramified_iff` (`p ∤ d ⇒ (p)` radical) uses the
private helper `polyMod_squarefree_of_not_p_dvd_d`, transported across the ring
iso of `QuotientIso.lean`.

**Divergence from thesis.** "Ramified" is phrased here as the precise statement
`¬ (p).IsRadical`, with `τ` as an explicit order-2 nilpotent witness. The
reverse direction reduces to *squarefreeness of `polyMod d p`* and transports
`IsReduced` across `quadraticOrderModPEquivPolyModQuot`, in place of the
thesis's hand computation. Mathematically the same as Prop 3.2.1.
-/

open Polynomial

namespace QuadraticOrder

variable {d : ℤ} {p : ℕ}

/-- **Ramification witness**: when `p ∣ d` (with `p ≠ 2`, `d ≡ 0 ∨ 1 (mod 4)`),
`τ²` lies in `(p) ⊆ QuadraticOrder d`. Combined with `τ ∉ (p)` (which holds
generally because `τ` is a Z-basis element), this exhibits `τ + (p)` as a
nonzero nilpotent of order 2 in `QuadraticOrder d / (p)` — the algebraic
fingerprint of ramification of `p` in `QuadraticOrder d`. -/
theorem tau_sq_mem_span_p_of_p_dvd_d
    [Fact p.Prime] (hp2 : p ≠ 2) (hd : d % 4 = 0 ∨ d % 4 = 1)
    (hpd : (p : ℤ) ∣ d) :
    (tau (d := d)) ^ 2 ∈ Ideal.span {(p : QuadraticOrder d)} := by
  -- Extract `p ∣ (d²-d)/4` from the already-proved `polyMod_eq_X_sq_of_p_dvd_d`:
  -- the constant coefficient of `polyMod d p = X^2` is zero in `ZMod p`, and
  -- the constant coefficient is `((d²-d)/4 : ℤ) : ZMod p`.
  have hp_dvd_q : (p : ℤ) ∣ (d ^ 2 - d) / 4 := by
    have hpoly := polyMod_eq_X_sq_of_p_dvd_d hp2 hd hpd
    have h0 := congr_arg (Polynomial.coeff · 0) hpoly
    simp only [polyMod_coeff_zero, Polynomial.coeff_X_pow] at h0
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h0
  -- From `tau_minimal_poly`: `τ² = d • τ - ((d²-d)/4) • 1`.
  have htau : (tau (d := d)) ^ 2 =
      d • tau - ((d ^ 2 - d) / 4 : ℤ) • (1 : QuadraticOrder d) := by
    have h := tau_minimal_poly (d := d)
    linear_combination h
  rw [htau]
  -- Show each summand is in the ideal.
  apply Ideal.sub_mem
  · -- `d • τ ∈ (p)`: rewrite `d = p * k`, then `d • τ = (p : QO d) * (k • τ)`.
    obtain ⟨k, hk⟩ := hpd
    have hstep : (d : ℤ) • (tau (d := d)) =
        (p : QuadraticOrder d) * (k • tau) := by
      rw [hk, zsmul_eq_mul, zsmul_eq_mul]
      push_cast
      ring
    rw [hstep]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton _))
  · -- `((d²-d)/4) • 1 ∈ (p)`: same idea with the divisibility `p ∣ (d²-d)/4`.
    obtain ⟨m, hm⟩ := hp_dvd_q
    have hstep : ((d ^ 2 - d) / 4 : ℤ) • (1 : QuadraticOrder d) =
        (p : QuadraticOrder d) * (m • (1 : QuadraticOrder d)) := by
      simp_all
    rw [hstep]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton _))

/-- `τ` is not in the ideal `(p)` of `QuadraticOrder d` for any prime `p`.
This holds because `τ` is the second `ℤ`-basis element of `QuadraticOrder d`
(the first being `1`), so its `τ`-coordinate is `1`, which is not a multiple
of `p ≥ 2`.

Together with `tau_sq_mem_span_p_of_p_dvd_d`, this shows that when `p ∣ d`,
the image of `τ` in `QuadraticOrder d / (p)` is a nonzero element with
`τ² = 0` — a genuine order-2 nilpotent witnessing ramification. -/
theorem tau_not_mem_span_p [Fact p.Prime] :
    tau (d := d) ∉ Ideal.span {(p : QuadraticOrder d)} := by
  intro hmem
  -- Unfold span membership: get `α` with `α * (p : QO d) = τ`, i.e. `(p : ℕ) • α = τ`.
  obtain ⟨α, hα⟩ := Ideal.mem_span_singleton'.mp hmem
  have hsmul : (p : ℕ) • α = tau (d := d) := by
    rw [nsmul_eq_mul, ← mul_comm α, hα]
  -- Project `(p : ℕ) • α = τ` onto the τ-coordinate (index `1`). The τ-coordinate
  -- of `τ` is `1` (`basis_repr_tau_one`), so `(p : ℤ) ∣ 1` — impossible.
  let i1 : Fin (basis (d := d)).dim := ⟨1, by simp⟩
  have hlhs : ((basis (d := d)).basis.repr ((p : ℕ) • α)) i1 = 1 := by
    rw [hsmul]; exact basis_repr_tau_one
  rw [map_nsmul, Finsupp.coe_smul, Pi.smul_apply, nsmul_eq_mul] at hlhs
  exact (Nat.prime_iff_prime_int.mp Fact.out).not_dvd_one ⟨_, hlhs.symm⟩

/-- **Ramified-direction radical-witness**: when `p ∣ d` (with `p ≠ 2`,
`d ≡ 0 ∨ 1 (mod 4)`), the ideal `(p)` in `QuadraticOrder d` is NOT a
radical ideal. The witness is `τ`: `τ² ∈ (p)` (by
`tau_sq_mem_span_p_of_p_dvd_d`) but `τ ∉ (p)` (by `tau_not_mem_span_p`).
This is the algebraic fingerprint of ramification — the quotient
`QuadraticOrder d / (p)` has a nonzero nilpotent. -/
theorem span_p_not_isRadical_of_p_dvd_d
    [Fact p.Prime] (hp2 : p ≠ 2) (hd : d % 4 = 0 ∨ d % 4 = 1)
    (hpd : (p : ℤ) ∣ d) :
    ¬ (Ideal.span {(p : QuadraticOrder d)}).IsRadical := by
  intro hrad
  -- `IsRadical I ↔ I.radical ≤ I`. Apply `hrad` to `tau` with witness `n = 2`.
  apply tau_not_mem_span_p (d := d) (p := p)
  -- `tau ∈ (p).radical` because `tau^2 ∈ (p)`.
  exact hrad ⟨2, tau_sq_mem_span_p_of_p_dvd_d hp2 hd hpd⟩

/-- When `p ∤ d` (with `p ≠ 2`, `d ≡ 0 ∨ 1 (mod 4)`), the polynomial
`polyMod d p` is squarefree in `(ZMod p)[X]`. In the inert case
(`legendreSym p d = -1`) it is irreducible. In the split case
(`legendreSym p d = 1`) it factors as `(X - C r) * (X - C s)` with `r ≠ s`,
a product of two coprime irreducible (and thus squarefree) factors. -/
private theorem polyMod_squarefree_of_not_p_dvd_d [Fact p.Prime] (hp2 : p ≠ 2)
    (hd : d % 4 = 0 ∨ d % 4 = 1) (hpd : ¬ (p : ℤ) ∣ d) :
    Squarefree (polyMod d p) := by
  -- `d ≢ 0 (mod p)` since `p ∤ d`.
  have hd_ne : (d : ZMod p) ≠ 0 := by
    rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  -- The Legendre symbol is ±1.
  have htri : legendreSym p d = 1 ∨ legendreSym p d = -1 :=
    legendreSym.eq_one_or_neg_one (p := p) hd_ne
  rcases htri with hsplit | hinert
  · -- Split: factor `polyMod = (X - C r) * (X - C s)` with `r ≠ s`.
    obtain ⟨r, s, hrs, hr, hs⟩ :=
      polyMod_exists_two_distinct_roots_of_legendreSym_eq_one hp2 hd hsplit
    -- Each linear factor divides `polyMod`.
    have hr_dvd : (X - C r) ∣ polyMod d p := Polynomial.dvd_iff_isRoot.mpr hr
    have hs_dvd : (X - C s) ∣ polyMod d p := Polynomial.dvd_iff_isRoot.mpr hs
    -- The two linear factors are coprime (since `r - s ≠ 0` is a unit in the field).
    have hcop : IsCoprime (X - C r) (X - C s) :=
      Polynomial.isCoprime_X_sub_C_of_isUnit_sub
        ((sub_ne_zero_of_ne hrs).isUnit)
    -- Product divides `polyMod`.
    have hmul_dvd : (X - C r) * (X - C s) ∣ polyMod d p := hcop.mul_dvd hr_dvd hs_dvd
    -- Both sides monic of degree 2, so equal.
    have hmul_monic : ((X - C r) * (X - C s)).Monic :=
      (Polynomial.monic_X_sub_C r).mul (Polynomial.monic_X_sub_C s)
    have hmul_natDeg : ((X - C r) * (X - C s)).natDegree = 2 := by
      compute_degree!
    have heq : polyMod d p = (X - C r) * (X - C s) :=
      Polynomial.eq_of_monic_of_dvd_of_natDegree_le hmul_monic (polyMod_monic d p)
        hmul_dvd (by rw [polyMod_natDegree, hmul_natDeg])
    -- Squarefreeness of the product.
    rw [heq, squarefree_mul_iff]
    refine ⟨hcop.isRelPrime, ?_, ?_⟩
    · exact (Polynomial.irreducible_X_sub_C r).squarefree
    · exact (Polynomial.irreducible_X_sub_C s).squarefree
  · -- Inert: irreducible → squarefree.
    exact ((polyMod_irreducible_iff_legendreSym_eq_neg_one hp2 hd).mpr hinert).squarefree

/-- **Issue #7's ramified iff at the ideal level**: the ideal `(p)` fails to
be radical in `QuadraticOrder d` exactly when `p ∣ d`. The forward direction
(`p ∣ d → ¬ IsRadical`) is `span_p_not_isRadical_of_p_dvd_d`. The reverse
(`p ∤ d → IsRadical`) is proved by transporting squarefreeness of
`polyMod d p` (from `polyMod_squarefree_of_not_p_dvd_d`) along the ring
isomorphism `quadraticOrderModPEquivPolyModQuot`. -/
theorem prime_ramified_iff [Fact p.Prime] (hp2 : p ≠ 2)
    (hd : d % 4 = 0 ∨ d % 4 = 1) :
    ¬ (Ideal.span {(p : QuadraticOrder d)}).IsRadical ↔ (p : ℤ) ∣ d := by
  refine ⟨?_, span_p_not_isRadical_of_p_dvd_d hp2 hd⟩
  -- Reverse: `¬ IsRadical → p ∣ d`. Contrapositive: `p ∤ d → IsRadical`.
  contrapose!
  intro hpd
  -- Step 1: `polyMod d p` is squarefree, hence the ideal `(polyMod d p)`
  -- in `(ZMod p)[X]` is radical.
  have hsqf : Squarefree (polyMod d p) := polyMod_squarefree_of_not_p_dvd_d hp2 hd hpd
  have hrad_poly : (Ideal.span {polyMod d p}).IsRadical :=
    isRadical_iff_span_singleton.mp hsqf.isRadical
  -- Step 2: the quotient `(ZMod p)[X] ⧸ (polyMod d p)` is reduced.
  have hred_poly : IsReduced ((ZMod p)[X] ⧸ Ideal.span {polyMod d p}) :=
    (Ideal.isRadical_iff_quotient_reduced _).mp hrad_poly
  -- Step 3: transport reducedness through the ring iso
  -- `QO d ⧸ (p) ≃+* (ZMod p)[X] ⧸ (polyMod d p)`.
  have hred_QO : IsReduced (QuadraticOrder d ⧸ Ideal.span {(p : QuadraticOrder d)}) :=
    isReduced_of_injective
      (quadraticOrderModPEquivPolyModQuot d p).toRingHom
      (quadraticOrderModPEquivPolyModQuot d p).injective
  -- Step 4: reduced quotient ↔ radical ideal.
  exact (Ideal.isRadical_iff_quotient_reduced _).mpr hred_QO

end QuadraticOrder
