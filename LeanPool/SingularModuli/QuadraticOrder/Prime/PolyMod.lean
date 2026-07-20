/-
Copyright (c) 2026 Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Caleb L. Geiger
-/

import LeanPool.SingularModuli.QuadraticOrder.Basic
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-!
# Prime classification, part 1: the reduced polynomial `polyMod d p`

**Thesis.** §3.2, Proposition 3.2.1 and Remark 3.2.3 — the splitting behaviour
of a rational prime `p` in `O_d` is governed by the factorisation of the
defining polynomial mod `p`, i.e. by the Kronecker/Legendre symbol `(d/p)`.

**This file is the polynomial-level scaffolding** for that classification:
reduction of `poly d` mod `p`, its degree/coefficients, the discriminant
identity `disc = d (mod p)`, and the bridge from *roots of `polyMod`* to the
*Legendre symbol*:

* `polyMod`, `polyMod_eq`, `polyMod_monic`, `polyMod_natDegree`, `polyMod_coeff_*`
* `polyMod_discrim_eq` — `disc(polyMod) = d` in `ZMod p` (needs `d ≡ 0,1 mod 4`)
* `polyMod_exists_root_iff_isSquare_d` / `…_legendreSym_ne_neg_one`
* `polyMod_no_root_iff_legendreSym_eq_neg_one`  (inert criterion)
* `legendreSym_eq_zero_iff_dvd`                  (ramified criterion)
* `polyMod_splits_iff_legendreSym_ne_neg_one`
* `polyMod_eq_X_sq_of_p_dvd_d`                   (ramified: `polyMod = X²`)
* `polyMod_exists_two_distinct_roots_of_legendreSym_eq_one` (split)
* `polyMod_irreducible_iff_legendreSym_eq_neg_one`         (inert)

The *ideal-level* consequences are split across `QuotientIso.lean` (the ring
iso), `Inert.lean`, `Split.lean`, and `Ramified.lean`.

**Note.** This file also carries the shared Mathlib import block for the whole
`Prime/` directory; the other `Prime/*` files import this one and inherit it.
-/

open Polynomial

namespace QuadraticOrder

variable (d : ℤ) (p : ℕ)

/-- Reduction of the defining polynomial `poly d` modulo `p`, as a
polynomial in `(ZMod p)[X]`. -/
noncomputable def polyMod : (ZMod p)[X] :=
  (poly d).map (Int.castRingHom (ZMod p))

/-- Explicit form: `polyMod d p = X² - d·X + ((d² - d)/4)` over `ZMod p`. -/
lemma polyMod_eq :
    polyMod d p = X ^ 2 - C ((d : ZMod p)) * X
      + C (((d ^ 2 - d) / 4 : ℤ) : ZMod p) := by
  unfold polyMod poly
  simp [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul,
        Polynomial.map_pow, Polynomial.map_X]

/-- The mod-`p` reduction is monic. -/
lemma polyMod_monic : (polyMod d p).Monic :=
  (poly_monic d).map _

variable {d p}

/-- The mod-`p` reduction has degree 2 (requires `p` prime so `ZMod p` is
nontrivial). -/
lemma polyMod_natDegree [Fact p.Prime] : (polyMod d p).natDegree = 2 := by
  unfold polyMod
  rw [(poly_monic d).natDegree_map]
  unfold poly
  compute_degree!

/-- Coefficient of `X²` in `polyMod d p` is `1`. -/
@[simp] lemma polyMod_coeff_two : (polyMod d p).coeff 2 = 1 := by
  unfold polyMod
  rw [Polynomial.coeff_map]
  unfold poly
  simp [Polynomial.coeff_X_pow,
        Mathlib.Tactic.ComputeDegree.coeff_intCast_ite]

/-- Coefficient of `X` in `polyMod d p` is `-d (mod p)`. -/
@[simp] lemma polyMod_coeff_one :
    (polyMod d p).coeff 1 = -(d : ZMod p) := by
  unfold polyMod
  rw [Polynomial.coeff_map]
  unfold poly
  simp [Polynomial.coeff_X_pow,
        Mathlib.Tactic.ComputeDegree.coeff_intCast_ite]

/-- Constant coefficient of `polyMod d p` is `(d² - d)/4 (mod p)`. -/
@[simp] lemma polyMod_coeff_zero :
    (polyMod d p).coeff 0 = (((d ^ 2 - d) / 4 : ℤ) : ZMod p) := by
  unfold polyMod
  rw [Polynomial.coeff_map]
  unfold poly
  simp_all

/-- Discriminant identity: when `d ≡ 0 ∨ 1 (mod 4)`, the (coefficient-level)
discriminant of the monic-quadratic form of `polyMod d p` equals `d` in
`ZMod p`. This is the key bridge connecting `poly d`'s splitting behaviour
to the Kronecker symbol `(d / p)`. -/
lemma polyMod_discrim_eq (hd : d % 4 = 0 ∨ d % 4 = 1) :
    discrim (1 : ZMod p) (-(d : ZMod p)) (((d ^ 2 - d) / 4 : ℤ) : ZMod p)
      = (d : ZMod p) := by
  unfold discrim
  have h4dvd := dvd_four_of_valid_disc hd
  have hcancel : (4 : ℤ) * ((d ^ 2 - d) / 4) = d ^ 2 - d :=
    Int.mul_ediv_cancel' h4dvd
  have key : (-d) ^ 2 - 4 * ((d ^ 2 - d) / 4) = d := by
    nlinarith [hcancel]
  have hcast := congrArg (fun z : ℤ => (z : ZMod p)) key
  push_cast at hcast
  simp_all

/-- Evaluation of `polyMod d p` at `x ∈ ZMod p`: a closed-form expansion.

This reduces evaluation to a quadratic expression in `x` over `ZMod p`. -/
lemma polyMod_eval (x : ZMod p) :
    (polyMod d p).eval x = x ^ 2 - (d : ZMod p) * x + (((d ^ 2 - d) / 4 : ℤ) : ZMod p) := by
  rw [polyMod_eq]
  simp [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_X]

/-- For `p` an odd prime and `d ≡ 0 ∨ 1 (mod 4)`, `polyMod d p` has a root
in `ZMod p` iff `d` is a quadratic residue mod `p` (i.e. `IsSquare (d : ZMod p)`).

This is the polynomial-level bridge connecting `poly d`'s splitting behaviour
to the Kronecker / Legendre symbol `(d / p)`. -/
theorem polyMod_exists_root_iff_isSquare_d
    [Fact p.Prime] (hp2 : p ≠ 2) (hd : d % 4 = 0 ∨ d % 4 = 1) :
    (∃ x : ZMod p, (polyMod d p).eval x = 0) ↔ IsSquare (d : ZMod p) := by
  -- Establish `NeZero (2 : ZMod p)` from `p` prime and `p ≠ 2`.
  have hp_two_ne : (2 : ZMod p) ≠ 0 := by
    intro h
    have hp_dvd : p ∣ 2 := by rwa [← Nat.cast_two, CharP.cast_eq_zero_iff (ZMod p) p] at h
    have hle : p ≤ 2 := Nat.le_of_dvd (by decide) hp_dvd
    have hge : 2 ≤ p := (Fact.out : p.Prime).two_le
    exact hp2 (by omega)
  have hne2 : NeZero (2 : ZMod p) := ⟨hp_two_ne⟩
  -- Bridge `polyMod` evaluation to standard quadratic form `a*(x*x) + b*x + c = 0`.
  have hquad_iff : ∀ x : ZMod p,
      (polyMod d p).eval x = 0 ↔
        (1 : ZMod p) * (x * x) + (-(d : ZMod p)) * x +
          (((d ^ 2 - d) / 4 : ℤ) : ZMod p) = 0 := by
    intro x
    rw [polyMod_eval]
    constructor <;> (intro h; linear_combination h)
  -- Restate the existential using the quadratic form.
  simp_rw [hquad_iff]
  -- Now apply the discriminant characterisation.
  have h1ne : (1 : ZMod p) ≠ 0 := one_ne_zero
  constructor
  · -- Forward: a root gives a square root of the discriminant, which is `d`.
    rintro ⟨x, hx⟩
    have hdsq := discrim_eq_sq_of_quadratic_eq_zero hx
    -- `discrim 1 (-d) ((d^2-d)/4) = (2*1*x + (-d))^2`
    rw [polyMod_discrim_eq hd] at hdsq
    refine ⟨2 * 1 * x + (-(d : ZMod p)), ?_⟩
    linear_combination hdsq
  · -- Reverse: a square `d = s*s` gives a discriminant-square, then `exists_quadratic_eq_zero`.
    rintro ⟨s, hs⟩
    have hdisc_sq : ∃ t : ZMod p,
        discrim (1 : ZMod p) (-(d : ZMod p)) (((d ^ 2 - d) / 4 : ℤ) : ZMod p) = t * t := by
      refine ⟨s, ?_⟩
      rw [polyMod_discrim_eq hd, hs]
    exact exists_quadratic_eq_zero h1ne hdisc_sq

/-- `polyMod d p` has a root in `ZMod p` iff the Legendre symbol `(d/p)` is
not `-1`. Equivalently, `d` is either zero (ramified case) or a quadratic
residue (split case) mod `p`. -/
theorem polyMod_exists_root_iff_legendreSym_ne_neg_one
    [Fact p.Prime] (hp2 : p ≠ 2) (hd : d % 4 = 0 ∨ d % 4 = 1) :
    (∃ x : ZMod p, (polyMod d p).eval x = 0) ↔ legendreSym p d ≠ -1 := by
  rw [polyMod_exists_root_iff_isSquare_d hp2 hd, Ne, legendreSym.eq_neg_one_iff,
      not_not]

/-- `polyMod d p` has no root in `ZMod p` iff `(d/p) = -1` — the inert case. -/
theorem polyMod_no_root_iff_legendreSym_eq_neg_one
    [Fact p.Prime] (hp2 : p ≠ 2) (hd : d % 4 = 0 ∨ d % 4 = 1) :
    (¬ ∃ x : ZMod p, (polyMod d p).eval x = 0) ↔ legendreSym p d = -1 := by
  rw [polyMod_exists_root_iff_legendreSym_ne_neg_one hp2 hd, not_not]

/-- The ramified case: `(d/p) = 0 ↔ p ∣ d`. -/
theorem legendreSym_eq_zero_iff_dvd [Fact p.Prime] :
    legendreSym p d = 0 ↔ (p : ℤ) ∣ d := by
  rw [legendreSym.eq_zero_iff, ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- A monic-quadratic polynomial in `(ZMod p)[X]` splits iff it has a root.
For `polyMod d p` this is the bridge from `polyMod_exists_root_iff_isSquare_d`
to the `Polynomial.Splits` predicate. -/
theorem polyMod_splits_iff_exists_root [Fact p.Prime] :
    (polyMod d p).Splits ↔ ∃ x : ZMod p, (polyMod d p).eval x = 0 := by
  constructor
  · intro hs
    refine hs.exists_eval_eq_zero ?_
    rw [Polynomial.degree_eq_natDegree (polyMod_monic d p).ne_zero, polyMod_natDegree]
    decide
  · rintro ⟨x, hx⟩
    exact Polynomial.Splits.of_natDegree_eq_two polyMod_natDegree hx

/-- `polyMod d p` splits in `(ZMod p)[X]` iff the Legendre symbol `(d/p)` is
not `-1`. This combines `polyMod_splits_iff_exists_root` with the previously
proved `polyMod_exists_root_iff_legendreSym_ne_neg_one`. -/
theorem polyMod_splits_iff_legendreSym_ne_neg_one
    [Fact p.Prime] (hp2 : p ≠ 2) (hd : d % 4 = 0 ∨ d % 4 = 1) :
    (polyMod d p).Splits ↔ legendreSym p d ≠ -1 := by
  rw [polyMod_splits_iff_exists_root,
      polyMod_exists_root_iff_legendreSym_ne_neg_one hp2 hd]

/-- The ramified case at the polynomial level: when `p` is an odd prime
dividing `d` (with `d ≡ 0 ∨ 1 (mod 4)`), the reduction `polyMod d p` is
identically `X²` in `(ZMod p)[X]`. In particular it has the unique root 0
with multiplicity 2, witnessing the ramified behaviour of `(p)` in
`QuadraticOrder d`. -/
theorem polyMod_eq_X_sq_of_p_dvd_d
    [Fact p.Prime] (hp2 : p ≠ 2) (hd : d % 4 = 0 ∨ d % 4 = 1)
    (hpd : (p : ℤ) ∣ d) :
    polyMod d p = X ^ 2 := by
  rw [polyMod_eq]
  -- Show both the linear and constant coefficients are 0 in ZMod p.
  have hd_zmod : (d : ZMod p) = 0 := by
    rwa [ZMod.intCast_zmod_eq_zero_iff_dvd]
  have h4dvd := dvd_four_of_valid_disc hd
  have hp_dvd_q : (p : ℤ) ∣ (d ^ 2 - d) / 4 := by
    -- 4 * ((d²-d)/4) = d² - d (by hcancel), and p ∣ d² - d = d*(d-1).
    -- Then p prime, p ∤ 4, so p ∣ (d²-d)/4.
    have hp_dvd_sub : (p : ℤ) ∣ 4 * ((d ^ 2 - d) / 4) := by
      rw [Int.mul_ediv_cancel' h4dvd]
      exact dvd_sub (dvd_pow hpd (by norm_num)) hpd
    have hp_prime_int : Prime (p : ℤ) :=
      Nat.prime_iff_prime_int.mp (Fact.out (p := p.Prime))
    have hp_not_dvd_4 : ¬ (p : ℤ) ∣ 4 := by
      intro hdvd4
      have hp_prime : p.Prime := Fact.out
      have hp_le : (p : ℤ) ≤ 4 := Int.le_of_dvd (by norm_num) hdvd4
      have hpnat_le : p ≤ 4 := by exact_mod_cast hp_le
      have hpnat_ge : 2 ≤ p := hp_prime.two_le
      interval_cases p
      · exact hp2 rfl
      · norm_num at hdvd4
      · exact absurd hp_prime (by decide)
    exact (hp_prime_int.dvd_mul.mp hp_dvd_sub).resolve_left hp_not_dvd_4
  have hq_zmod : (((d ^ 2 - d) / 4 : ℤ) : ZMod p) = 0 := by
    rwa [ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp_all

/-- The split case at the polynomial level: when `p` is an odd prime, `d ≡ 0 ∨ 1
(mod 4)`, and the Legendre symbol `(d/p) = 1` (so `d` is a non-zero quadratic
residue mod `p`), `polyMod d p` has two distinct roots in `ZMod p`. These two
roots witness the splitting `(p) = P₁ · P₂` in `QuadraticOrder d`. -/
theorem polyMod_exists_two_distinct_roots_of_legendreSym_eq_one
    [Fact p.Prime] (hp2 : p ≠ 2) (hd : d % 4 = 0 ∨ d % 4 = 1)
    (h_split : legendreSym p d = 1) :
    ∃ r s : ZMod p, r ≠ s ∧
      (polyMod d p).eval r = 0 ∧ (polyMod d p).eval s = 0 := by
  -- Establish `(2 : ZMod p) ≠ 0` from `p` prime and `p ≠ 2` (same pattern as
  -- `polyMod_exists_root_iff_isSquare_d`).
  have hp_two_ne : (2 : ZMod p) ≠ 0 := by
    intro h
    have hp_dvd : p ∣ 2 := by rwa [← Nat.cast_two, CharP.cast_eq_zero_iff (ZMod p) p] at h
    have hle : p ≤ 2 := Nat.le_of_dvd (by decide) hp_dvd
    have hge : 2 ≤ p := (Fact.out : p.Prime).two_le
    exact hp2 (by omega)
  have hne2 : NeZero (2 : ZMod p) := ⟨hp_two_ne⟩
  -- From `(d/p) = 1`: `d ≠ 0 mod p` and `d` is a square mod p.
  have hd_ne_zero : (d : ZMod p) ≠ 0 := by
    intro hd0
    have : legendreSym p d = 0 := (legendreSym.eq_zero_iff p d).mpr hd0
    simp_all
  have hsq : IsSquare (d : ZMod p) := (legendreSym.eq_one_iff p hd_ne_zero).mp h_split
  obtain ⟨t, ht⟩ := hsq
  -- `ht : (d : ZMod p) = t * t`
  -- Therefore `t ≠ 0` (else `d = 0 mod p`).
  have ht_ne_zero : t ≠ 0 := by
    simp_all
  -- The discriminant equals `t * t`.
  have hdiscr : discrim (1 : ZMod p) (-(d : ZMod p)) (((d ^ 2 - d) / 4 : ℤ) : ZMod p)
      = t * t := by
    rw [polyMod_discrim_eq hd]; exact ht
  -- Bridge `polyMod` evaluation to the standard quadratic form used by
  -- `quadratic_eq_zero_iff`.
  have hquad_iff : ∀ x : ZMod p,
      (polyMod d p).eval x = 0 ↔
        (1 : ZMod p) * (x * x) + (-(d : ZMod p)) * x +
          (((d ^ 2 - d) / 4 : ℤ) : ZMod p) = 0 := by
    intro x
    rw [polyMod_eval]
    constructor <;> (intro h; linear_combination h)
  -- The two roots from `quadratic_eq_zero_iff` are `(d + t)/2` and `(d - t)/2`.
  refine ⟨((d : ZMod p) + t) / 2, ((d : ZMod p) - t) / 2, ?_, ?_, ?_⟩
  · -- Distinctness: if `r = s` then `t = 0`.
    intro hrs
    apply ht_ne_zero
    -- From `(d+t)/2 = (d-t)/2`, multiply by `2`: `d + t = d - t`, so `2t = 0`.
    have h2t : (2 : ZMod p) * t = 0 := by
      have hmul : 2 * (((d : ZMod p) + t) / 2) = 2 * (((d : ZMod p) - t) / 2) :=
        congrArg (fun x => 2 * x) hrs
      rw [mul_div_cancel₀ _ hp_two_ne, mul_div_cancel₀ _ hp_two_ne] at hmul
      linear_combination hmul
    simp_all
  · -- `((d+t)/2)` is a root.
    rw [hquad_iff]
    rw [quadratic_eq_zero_iff one_ne_zero hdiscr]
    simp_all
  · -- `((d-t)/2)` is a root.
    rw [hquad_iff]
    rw [quadratic_eq_zero_iff one_ne_zero hdiscr]
    simp_all

/-- `polyMod d p` is irreducible in `(ZMod p)[X]` iff the Legendre symbol
`(d/p) = -1`. Combines the monic-degree-two irreducibility characterisation
with the polynomial-level Legendre bridge already established. -/
theorem polyMod_irreducible_iff_legendreSym_eq_neg_one
    [Fact p.Prime] (hp2 : p ≠ 2) (hd : d % 4 = 0 ∨ d % 4 = 1) :
    Irreducible (polyMod d p) ↔ legendreSym p d = -1 := by
  have hne : (polyMod d p) ≠ 0 := (polyMod_monic d p).ne_zero
  rw [Polynomial.Monic.irreducible_iff_roots_eq_zero_of_degree_le_three
        (polyMod_monic d p)
        (by rw [polyMod_natDegree]) (by rw [polyMod_natDegree]; decide),
      Multiset.eq_zero_iff_forall_notMem]
  simp_rw [Polynomial.mem_roots hne, Polynomial.IsRoot.def]
  rw [← not_exists, polyMod_no_root_iff_legendreSym_eq_neg_one hp2 hd]

end QuadraticOrder
