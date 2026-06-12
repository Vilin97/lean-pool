/-
Copyright (c) 2026 Barinder S. Banwait. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Barinder S. Banwait
-/

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.QuadraticAlgebra.NormDeterminant
import Mathlib.Algebra.Order.Round
import Mathlib.Data.Rat.Floor
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.UniqueFactorizationDomain.Defs
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.Multiplicity
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Polyrith

/-!
# Algebraic infrastructure for `R = QuadraticAlgebra ℤ (-2) 1 = ℤ[(1+√-7)/2]`

Following Michael Stoll's suggestion to work directly in `QuadraticAlgebra ℤ (-2) 1`
rather than through `𝓞 K` where `K = QuadraticAlgebra ℚ (-2) 1`. The payoff:

* `θ ^ 2 = θ - 2`, `θ * θ' = 2`, `θ + θ' = 1`, `norm θ = 2`, `norm θ' = 2`
  are all literal `rfl`s (no `Subtype.ext` ceremony, no
  `omega_mul_omega_eq_mk`).
* `units_pm_one` reduces to a one-page completing-the-square argument over ℤ.
* `EuclideanDomain R → IsPrincipalIdealRing R → UniqueFactorizationMonoid R`
  replaces the discriminant / class-number-1 detour through Dirichlet.
-/

namespace RamanujanNagell

open QuadraticAlgebra

/-- The integer ring `ℤ[(1 + √-7)/2]`, packaged as `QuadraticAlgebra ℤ (-2) 1`. -/
abbrev R : Type := QuadraticAlgebra ℤ (-2) 1

/-- `θ = (1 + √-7)/2`, the generator of `R`. -/
def θ : R := ⟨0, 1⟩

/-- `θ' = (1 - √-7)/2 = 1 - θ`, the Galois conjugate of `θ`. -/
def θ' : R := ⟨1, -1⟩

/-! ## Stoll's `rfl` claims -/

lemma theta_sq : θ ^ 2 = θ - 2 := rfl

lemma theta_mul_theta' : θ * θ' = 2 := rfl

lemma theta_add_theta' : θ + θ' = 1 := rfl

lemma theta'_eq_one_sub_theta : θ' = 1 - θ := rfl

/-- For backward compatibility with the old Helpers API. -/
lemma two_factorisation_R : θ * (1 - θ) = 2 := rfl

/-! ## Norm form and positivity

`norm ⟨x, y⟩ = x² + xy + 2y²`; the key identity is `4·N = (2x + y)² + 7y²`. -/

lemma norm_eq (x y : ℤ) : QuadraticAlgebra.norm (⟨x, y⟩ : R) = x ^ 2 + x * y + 2 * y ^ 2 := by
  rw [QuadraticAlgebra.norm_def]; ring

/-- The completing-the-square identity. -/
lemma four_norm_eq (z : R) :
    4 * QuadraticAlgebra.norm z = (2 * z.re + z.im) ^ 2 + 7 * z.im ^ 2 := by
  rw [QuadraticAlgebra.norm_def]; ring

lemma norm_nonneg (z : R) : 0 ≤ QuadraticAlgebra.norm z := by
  have h := four_norm_eq z
  have h1 : 0 ≤ (2 * z.re + z.im) ^ 2 := sq_nonneg _
  have h2 : 0 ≤ 7 * z.im ^ 2 := by positivity
  linarith

lemma norm_eq_zero_iff (z : R) : QuadraticAlgebra.norm z = 0 ↔ z = 0 := by
  refine ⟨fun h => ?_, fun h => h ▸ QuadraticAlgebra.norm_zero⟩
  have h4 := four_norm_eq z
  rw [h] at h4
  have hv : z.im = 0 := by nlinarith [sq_nonneg (2 * z.re + z.im), sq_nonneg z.im]
  have hu : z.re = 0 := by nlinarith [h4, hv, sq_nonneg z.re]
  exact QuadraticAlgebra.ext hu hv

lemma norm_pos {z : R} (hz : z ≠ 0) : 0 < QuadraticAlgebra.norm z := by
  rcases lt_or_eq_of_le (norm_nonneg z) with h | h
  · exact h
  · exact absurd ((norm_eq_zero_iff z).mp h.symm) hz

/-! ## Units are ±1 -/

lemma units_pm_one (u : Rˣ) : u = 1 ∨ u = -1 := by
  have hunit : IsUnit (QuadraticAlgebra.norm (u : R)) :=
    QuadraticAlgebra.isUnit_iff_norm_isUnit.mp u.isUnit
  rcases Int.isUnit_iff.mp hunit with hn | hn
  · set x := (u : R).re
    set y := (u : R).im
    have hcoord : (u : R) = ⟨x, y⟩ := by apply QuadraticAlgebra.ext <;> rfl
    have hn' : x ^ 2 + x * y + 2 * y ^ 2 = 1 := by
      rw [show x = (⟨x, y⟩ : R).re from rfl, show y = (⟨x, y⟩ : R).im from rfl,
          ← norm_eq]
      rw [← hcoord]; exact hn
    have h_csq : (2 * x + y) ^ 2 + 7 * y ^ 2 = 4 := by linarith
    have hy : y = 0 := by nlinarith [sq_nonneg y, sq_nonneg (2 * x + y)]
    have hx2 : x ^ 2 = 1 := by nlinarith
    have hx : x = 1 ∨ x = -1 := by
      have hfact : (x - 1) * (x + 1) = 0 := by linarith [hx2]
      rcases mul_eq_zero.mp hfact with h | h
      · left; omega
      · right; omega
    rcases hx with hx1 | hx1
    · left
      apply Units.ext
      rw [hcoord, hx1, hy]; rfl
    · right
      apply Units.ext
      rw [hcoord, hx1, hy]; rfl
  · exfalso
    have := norm_nonneg (u : R)
    omega

/-! ## θ and θ' are irreducible -/

private lemma norm_factor_dichotomy {m n : ℤ} (hm : 0 ≤ m) (hn : 0 ≤ n) (hmn : m * n = 2) :
    m = 1 ∨ n = 1 := by
  have hm_pos : 0 < m := by
    rcases lt_or_eq_of_le hm with h | h
    · exact h
    · exfalso; rw [← h, zero_mul] at hmn; exact absurd hmn (by decide)
  have hn_pos : 0 < n := by
    rcases lt_or_eq_of_le hn with h | h
    · exact h
    · exfalso; rw [← h, mul_zero] at hmn; exact absurd hmn (by decide)
  have hm_le : m ≤ 2 := by nlinarith
  interval_cases m
  · left; rfl
  · right; linarith

private lemma isUnit_of_norm_one {a : R} (h : QuadraticAlgebra.norm a = 1) : IsUnit a := by
  apply QuadraticAlgebra.isUnit_iff_norm_isUnit.mpr
  rw [h]; exact isUnit_one

lemma theta_irreducible : Irreducible θ := by
  refine ⟨?_, ?_⟩
  · intro hu
    have h1 : IsUnit (QuadraticAlgebra.norm θ) := QuadraticAlgebra.isUnit_iff_norm_isUnit.mp hu
    have h2 : IsUnit (2 : ℤ) := h1
    exact absurd (Int.isUnit_iff.mp h2) (by decide)
  · intro a b hab
    have hnab : QuadraticAlgebra.norm a * QuadraticAlgebra.norm b = 2 := by
      rw [← map_mul, ← hab]; rfl
    rcases norm_factor_dichotomy (norm_nonneg a) (norm_nonneg b) hnab with h | h
    · exact Or.inl (isUnit_of_norm_one h)
    · exact Or.inr (isUnit_of_norm_one h)

lemma theta'_irreducible : Irreducible θ' := by
  refine ⟨?_, ?_⟩
  · intro hu
    have h1 : IsUnit (QuadraticAlgebra.norm θ') := QuadraticAlgebra.isUnit_iff_norm_isUnit.mp hu
    have h2 : IsUnit (2 : ℤ) := h1
    exact absurd (Int.isUnit_iff.mp h2) (by decide)
  · intro a b hab
    have hnab : QuadraticAlgebra.norm a * QuadraticAlgebra.norm b = 2 := by
      rw [← map_mul, ← hab]; rfl
    rcases norm_factor_dichotomy (norm_nonneg a) (norm_nonneg b) hnab with h | h
    · exact Or.inl (isUnit_of_norm_one h)
    · exact Or.inr (isUnit_of_norm_one h)

/-! ## EuclideanDomain instance via smart rounding

`R = ℤ[(1+√-7)/2]` with norm `N(x, y) = x² + xy + 2y²`. To divide `a` by `b ≠ 0`,
we want `q` such that `N(a - b·q) < N(b)`. Naive independent rounding of `(a/b)`
in the `(re, im)` basis can leave `N = 1` exactly at the fundamental-domain
corner; the fix is to round `im` first, then re-round `re` shifted by half the
`im` residual. With that choice `16·N(rem) ≤ 11·N(b)`. -/

private lemma b_mul_star_eq_norm (b : R) :
    b * star b = ((QuadraticAlgebra.norm b : ℤ) : R) := by
  apply QuadraticAlgebra.ext
  · simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star,
      QuadraticAlgebra.re_intCast, QuadraticAlgebra.norm_def, Int.cast_id]
    ring
  · simp only [QuadraticAlgebra.im_mul, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star,
      QuadraticAlgebra.im_intCast]
    ring

private lemma N_mul_rem_eq (a b q : R) :
    ((QuadraticAlgebra.norm b : ℤ) : R) * (a - b * q) =
      b * (a * star b - ((QuadraticAlgebra.norm b : ℤ) : R) * q) := by
  have hbs := b_mul_star_eq_norm b
  calc ((QuadraticAlgebra.norm b : ℤ) : R) * (a - b * q)
      = (b * star b) * (a - b * q) := by rw [← hbs]
    _ = b * (a * star b - (b * star b) * q) := by ring
    _ = b * (a * star b - ((QuadraticAlgebra.norm b : ℤ) : R) * q) := by rw [hbs]

private lemma N_mul_norm_rem_eq (a b q : R) (hb : b ≠ 0) :
    QuadraticAlgebra.norm b * QuadraticAlgebra.norm (a - b * q) =
      QuadraticAlgebra.norm (a * star b - ((QuadraticAlgebra.norm b : ℤ) : R) * q) := by
  have hN_pos : 0 < QuadraticAlgebra.norm b := norm_pos hb
  have hN_ne : QuadraticAlgebra.norm b ≠ 0 := hN_pos.ne'
  have h_key := N_mul_rem_eq a b q
  have h_norm : QuadraticAlgebra.norm
      (((QuadraticAlgebra.norm b : ℤ) : R) * (a - b * q)) =
      QuadraticAlgebra.norm
      (b * (a * star b - ((QuadraticAlgebra.norm b : ℤ) : R) * q)) := by
    rw [h_key]
  rw [map_mul, map_mul, QuadraticAlgebra.norm_intCast] at h_norm
  have h_sq : (QuadraticAlgebra.norm b) ^ 2 =
              QuadraticAlgebra.norm b * QuadraticAlgebra.norm b := sq _
  have : QuadraticAlgebra.norm b *
         (QuadraticAlgebra.norm b * QuadraticAlgebra.norm (a - b * q)) =
         QuadraticAlgebra.norm b *
         QuadraticAlgebra.norm (a * star b - ((QuadraticAlgebra.norm b : ℤ) : R) * q) := by
    rw [← mul_assoc, ← h_sq]
    exact h_norm
  exact mul_left_cancel₀ hN_ne this

/-- Smart-rounded quotient. -/
noncomputable def quot (a b : R) : R :=
  let N : ℤ := QuadraticAlgebra.norm b
  if N = 0 then 0
  else
    let s : R := a * star b
    let n : ℤ := round ((s.im : ℚ) / N)
    let m : ℤ := round ((2 * (s.re : ℚ) + s.im - N * n) / (2 * N))
    ⟨m, n⟩

/-- Smart-rounded remainder: `rem a b = a - b * quot a b`. -/
noncomputable def rem (a b : R) : R := a - b * quot a b

@[simp] lemma quot_zero (a : R) : quot a 0 = 0 := by unfold quot; simp

lemma quot_mul_add_rem_eq (a b : R) : b * quot a b + rem a b = a := by
  unfold rem; ring

private lemma sixteen_norm_rem_le (a b : R) (hb : b ≠ 0) :
    16 * QuadraticAlgebra.norm (rem a b) ≤ 11 * QuadraticAlgebra.norm b := by
  set N := QuadraticAlgebra.norm b with hN_def
  have hN_pos : 0 < N := norm_pos hb
  have hN_ne : N ≠ 0 := hN_pos.ne'
  set s : R := a * star b with hs_def
  set n : ℤ := round ((s.im : ℚ) / N) with hn_def
  set m : ℤ := round ((2 * (s.re : ℚ) + s.im - N * n) / (2 * N)) with hm_def
  have hquot : quot a b = (⟨m, n⟩ : R) := by
    change (if QuadraticAlgebra.norm b = 0 then (0 : R) else _) = _
    rw [if_neg hN_ne]
  set u : ℤ := s.re - N * m with hu_def
  set v : ℤ := s.im - N * n with hv_def
  have hNq_pos : (0 : ℚ) < N := by exact_mod_cast hN_pos
  have hNq : (N : ℚ) ≠ 0 := hNq_pos.ne'
  have h2Nq_pos : (0 : ℚ) < 2 * N := by linarith
  have hv_bd : (2 * v) ^ 2 ≤ N ^ 2 := by
    have habs : |(s.im : ℚ) / N - n| ≤ 1 / 2 := abs_sub_round _
    have heq : ((s.im : ℚ) / N - n) * (2 * N) = ((2 * v : ℤ) : ℚ) := by
      push_cast [hv_def]; field_simp
    have h_abs_2v : |((2 * v : ℤ) : ℚ)| ≤ N := by
      rw [← heq, abs_mul, abs_of_pos h2Nq_pos]
      have := mul_le_mul_of_nonneg_right habs h2Nq_pos.le
      linarith
    have h_sq : ((2 * v : ℤ) : ℚ) ^ 2 ≤ (N : ℚ) ^ 2 := by
      have hsa : ((2 * v : ℤ) : ℚ) ^ 2 = |((2 * v : ℤ) : ℚ)| ^ 2 := (sq_abs _).symm
      rw [hsa]
      exact sq_le_sq' (by linarith [abs_nonneg ((2 * v : ℤ) : ℚ)]) h_abs_2v
    exact_mod_cast h_sq
  have huv_bd : (2 * u + v) ^ 2 ≤ N ^ 2 := by
    have habs : |(2 * (s.re : ℚ) + s.im - N * n) / (2 * N) - m| ≤ 1 / 2 := abs_sub_round _
    have heq : ((2 * (s.re : ℚ) + s.im - N * n) / (2 * N) - m) * (2 * N) =
               ((2 * u + v : ℤ) : ℚ) := by
      push_cast [hu_def, hv_def]; field_simp; ring
    have h_abs : |((2 * u + v : ℤ) : ℚ)| ≤ N := by
      rw [← heq, abs_mul, abs_of_pos h2Nq_pos]
      have := mul_le_mul_of_nonneg_right habs h2Nq_pos.le
      linarith
    have h_sq : ((2 * u + v : ℤ) : ℚ) ^ 2 ≤ (N : ℚ) ^ 2 := by
      have hsa : ((2 * u + v : ℤ) : ℚ) ^ 2 = |((2 * u + v : ℤ) : ℚ)| ^ 2 := (sq_abs _).symm
      rw [hsa]
      exact sq_le_sq' (by linarith [abs_nonneg ((2 * u + v : ℤ) : ℚ)]) h_abs
    exact_mod_cast h_sq
  have h_chain : N * QuadraticAlgebra.norm (rem a b) = u ^ 2 + u * v + 2 * v ^ 2 := by
    unfold rem
    rw [hquot]
    have h := N_mul_norm_rem_eq a b (⟨m, n⟩ : R) hb
    rw [h]
    have hre : (a * star b - ((N : ℤ) : R) * (⟨m, n⟩ : R)).re = u := by
      change s.re - (((N : ℤ) : R) * (⟨m, n⟩ : R)).re = u
      push_cast [hu_def]
      change s.re - (N * m + (-2) * 0 * n) = s.re - N * m
      ring
    have him : (a * star b - ((N : ℤ) : R) * (⟨m, n⟩ : R)).im = v := by
      change s.im - (((N : ℤ) : R) * (⟨m, n⟩ : R)).im = v
      push_cast [hv_def]
      change s.im - (N * n + 0 * m + 1 * 0 * n) = s.im - N * n
      ring
    rw [QuadraticAlgebra.norm_def, hre, him]; ring
  have h_alg : 16 * (u ^ 2 + u * v + 2 * v ^ 2) = 4 * (2 * u + v) ^ 2 + 7 * (2 * v) ^ 2 := by
    ring
  have h_bd : 16 * (u ^ 2 + u * v + 2 * v ^ 2) ≤ 11 * N ^ 2 := by
    rw [h_alg]; nlinarith [hv_bd, huv_bd]
  have hN_sq : N ^ 2 = N * N := sq N
  nlinarith [h_chain, h_bd, hN_pos]

private noncomputable def normMeasure (a : R) : ℕ := Int.natAbs (QuadraticAlgebra.norm a)

private lemma natAbs_norm_rem_lt (a : R) {b : R} (hb : b ≠ 0) :
    normMeasure (rem a b) < normMeasure b := by
  unfold normMeasure
  have hN_pos : 0 < QuadraticAlgebra.norm b := norm_pos hb
  have hr_nn : 0 ≤ QuadraticAlgebra.norm (rem a b) := norm_nonneg _
  have h_bd := sixteen_norm_rem_le a b hb
  have hr_lt : QuadraticAlgebra.norm (rem a b) < QuadraticAlgebra.norm b := by linarith
  zify
  rw [abs_of_nonneg hr_nn, abs_of_nonneg hN_pos.le]
  exact hr_lt

private lemma norm_mul_left_not_lt (a : R) {b : R} (hb : b ≠ 0) :
    ¬ normMeasure (a * b) < normMeasure a := by
  unfold normMeasure
  have hN_pos : 0 < QuadraticAlgebra.norm b := norm_pos hb
  have ha_nn : 0 ≤ QuadraticAlgebra.norm a := norm_nonneg a
  have hab : QuadraticAlgebra.norm (a * b) =
             QuadraticAlgebra.norm a * QuadraticAlgebra.norm b := map_mul _ _ _
  have hab_nn : 0 ≤ QuadraticAlgebra.norm (a * b) := hab ▸ mul_nonneg ha_nn hN_pos.le
  intro h
  zify at h
  rw [abs_of_nonneg hab_nn, abs_of_nonneg ha_nn, hab] at h
  nlinarith [ha_nn, hN_pos]

/-- `R` is a Euclidean domain. Division of `a` by `b ≠ 0` uses smart rounding of
`a · star b / N(b)` (round the `im` coordinate first, then shift-round `re`),
which guarantees `16 · N(rem) ≤ 11 · N(b)`, hence a strictly smaller norm. -/
noncomputable instance instEuclideanDomain : EuclideanDomain R where
  quotient := quot
  quotient_zero := quot_zero
  remainder := rem
  quotient_mul_add_remainder_eq := quot_mul_add_rem_eq
  r := fun a b => normMeasure a < normMeasure b
  r_wellFounded := (measure normMeasure).wf
  remainder_lt := natAbs_norm_rem_lt
  mul_left_not_lt := norm_mul_left_not_lt

/-- `R` is a principal ideal ring, since every Euclidean domain is one. -/
instance instPrincipalIdealRing : IsPrincipalIdealRing R :=
  EuclideanDomain.to_principal_ideal_domain

/-- `R` is a unique factorization domain, since every principal ideal ring is one. -/
instance instUniqueFactorizationMonoid : UniqueFactorizationMonoid R := inferInstance

/-! ## θ, θ' are prime -/

lemma theta_prime : Prime θ :=
  UniqueFactorizationMonoid.irreducible_iff_prime.mp theta_irreducible

lemma theta'_prime : Prime θ' :=
  UniqueFactorizationMonoid.irreducible_iff_prime.mp theta'_irreducible

/-! ## UFD scaffolding for the Ramanujan-Nagell argument

These lemmas combine `units_pm_one` with `UniqueFactorizationMonoid R` to give
the key dichotomy `α * β = θ^m · θ'^m ∧ IsCoprime α β → α = ±θ^m ∨ α = ±θ'^m`. -/

lemma theta_theta'_not_associated : ¬ Associated θ θ' := by
  rintro ⟨u, hu⟩
  rcases units_pm_one u with rfl | rfl
  · -- θ = θ' · 1 = θ', compare re-components: 0 ≠ 1
    have h := congrArg QuadraticAlgebra.re hu
    simp [θ, θ'] at h
  · -- θ = θ' · (-1) = -θ', compare re-components: 0 ≠ -1
    have h := congrArg QuadraticAlgebra.re hu
    simp [θ, θ'] at h

lemma theta_not_dvd_theta' : ¬ (θ ∣ θ') := by
  intro h
  exact theta_theta'_not_associated (theta_irreducible.associated_of_dvd theta'_irreducible h)

lemma theta'_not_dvd_theta : ¬ (θ' ∣ θ) := by
  intro h
  exact theta_theta'_not_associated
    (theta'_irreducible.associated_of_dvd theta_irreducible h).symm

lemma theta_pow_dvd_of_coprime_prod (α β : R) (m : ℕ)
    (h_prod : α * β = θ ^ m * θ' ^ m)
    (h_coprime : IsCoprime α β) :
    θ ^ m ∣ α ∨ θ ^ m ∣ β := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact Or.inl (one_dvd α)
  have hθ_prime : _root_.Prime θ := theta_prime
  have h_dvd_prod : θ ^ m ∣ α * β := h_prod ▸ dvd_mul_right (θ ^ m) (θ' ^ m)
  have h_dvd_or : θ ∣ α ∨ θ ∣ β :=
    hθ_prime.dvd_or_dvd (dvd_trans (dvd_pow_self θ (by omega)) h_dvd_prod)
  rcases h_dvd_or with h_dvd_α | h_dvd_β
  · have h_not_dvd_β : ¬ (θ ∣ β) := fun h_dvd_β =>
      hθ_prime.not_unit (h_coprime.isUnit_of_dvd' h_dvd_α h_dvd_β)
    exact Or.inl (hθ_prime.pow_dvd_of_dvd_mul_right m h_not_dvd_β h_dvd_prod)
  · have h_not_dvd_α : ¬ (θ ∣ α) := fun h_dvd_α =>
      hθ_prime.not_unit (h_coprime.isUnit_of_dvd' h_dvd_α h_dvd_β)
    exact Or.inr (hθ_prime.pow_dvd_of_dvd_mul_left m h_not_dvd_α h_dvd_prod)

lemma associated_of_theta_pow_dvd (α β : R) (m : ℕ)
    (h_prod : α * β = θ ^ m * θ' ^ m)
    (h_coprime : IsCoprime α β)
    (_hα : ¬IsUnit α) (hβ : ¬IsUnit β)
    (h_dvd : θ ^ m ∣ α) :
    Associated α (θ ^ m) := by
  obtain ⟨γ, hγ⟩ := h_dvd
  have hθm_ne : θ ^ m ≠ 0 := pow_ne_zero m (Irreducible.ne_zero theta_irreducible)
  have hθ'm_ne : θ' ^ m ≠ 0 := pow_ne_zero m (Irreducible.ne_zero theta'_irreducible)
  have h_cancel : γ * β = θ' ^ m := by
    have h1 := h_prod
    rw [hγ, mul_assoc] at h1
    exact mul_left_cancel₀ hθm_ne h1
  have hθ'_prime : _root_.Prime θ' := theta'_prime
  have h_not_dvd_γ : ¬ (θ' ∣ γ) := by
    intro h_dvd_γ
    have h_dvd_α : θ' ∣ α := hγ ▸ dvd_mul_of_dvd_right h_dvd_γ (θ ^ m)
    have h_not_dvd_β : ¬ (θ' ∣ β) := fun h_dvd_β =>
      hθ'_prime.not_unit (h_coprime.isUnit_of_dvd' h_dvd_α h_dvd_β)
    have h_dvd_prod : θ' ^ m ∣ γ * β := h_cancel ▸ dvd_refl (θ' ^ m)
    have h_θ'_pow_dvd_γ : θ' ^ m ∣ γ :=
      hθ'_prime.pow_dvd_of_dvd_mul_right m h_not_dvd_β h_dvd_prod
    obtain ⟨δ, hδ⟩ := h_θ'_pow_dvd_γ
    have h_eq := h_cancel
    rw [hδ, mul_assoc] at h_eq
    have h_δβ : δ * β = 1 := by
      conv at h_eq => rhs; rw [← mul_one (θ' ^ m)]
      exact mul_left_cancel₀ hθ'm_ne h_eq
    exact hβ (IsUnit.of_mul_eq_one δ (by rw [mul_comm]; exact h_δβ))
  have h_dvd_prod : θ' ^ m ∣ γ * β := h_cancel ▸ dvd_refl (θ' ^ m)
  have h_θ'_dvd_β : θ' ^ m ∣ β :=
    hθ'_prime.pow_dvd_of_dvd_mul_left m h_not_dvd_γ h_dvd_prod
  obtain ⟨ε, hε⟩ := h_θ'_dvd_β
  have h_eq := h_cancel
  rw [hε, ← mul_assoc, mul_comm γ (θ' ^ m), mul_assoc] at h_eq
  have h_γε : γ * ε = 1 := by
    conv at h_eq => rhs; rw [← mul_one (θ' ^ m)]
    exact mul_left_cancel₀ hθ'm_ne h_eq
  have hγ_unit : IsUnit γ := IsUnit.of_mul_eq_one ε h_γε
  rw [hγ]
  exact associated_mul_unit_left (θ ^ m) γ hγ_unit

lemma associated_of_theta_pow_dvd_right (α β : R) (m : ℕ)
    (h_prod : α * β = θ ^ m * θ' ^ m)
    (h_coprime : IsCoprime α β)
    (hα : ¬IsUnit α) (_hβ : ¬IsUnit β)
    (h_dvd : θ ^ m ∣ β) :
    Associated α (θ' ^ m) := by
  obtain ⟨γ, hγ⟩ := h_dvd
  have hθm_ne : θ ^ m ≠ 0 := pow_ne_zero m (Irreducible.ne_zero theta_irreducible)
  have hθ'm_ne : θ' ^ m ≠ 0 := pow_ne_zero m (Irreducible.ne_zero theta'_irreducible)
  have h_cancel : α * γ = θ' ^ m := by
    have h1 := h_prod
    rw [hγ, ← mul_assoc, mul_comm α (θ ^ m), mul_assoc] at h1
    exact mul_left_cancel₀ hθm_ne h1
  have hθ'_prime : _root_.Prime θ' := theta'_prime
  have h_not_dvd_γ : ¬ (θ' ∣ γ) := by
    intro h_dvd_γ
    have h_dvd_β : θ' ∣ β := hγ ▸ dvd_mul_of_dvd_right h_dvd_γ (θ ^ m)
    have h_not_dvd_α : ¬ (θ' ∣ α) := fun h_dvd_α =>
      hθ'_prime.not_unit (h_coprime.isUnit_of_dvd' h_dvd_α h_dvd_β)
    have h_dvd_prod : θ' ^ m ∣ α * γ := h_cancel ▸ dvd_refl (θ' ^ m)
    have h_θ'_pow_dvd_γ : θ' ^ m ∣ γ :=
      hθ'_prime.pow_dvd_of_dvd_mul_left m h_not_dvd_α h_dvd_prod
    obtain ⟨δ, hδ⟩ := h_θ'_pow_dvd_γ
    have h_eq := h_cancel
    rw [hδ, ← mul_assoc, mul_comm α (θ' ^ m), mul_assoc] at h_eq
    have h_αδ : α * δ = 1 := by
      conv at h_eq => rhs; rw [← mul_one (θ' ^ m)]
      exact mul_left_cancel₀ hθ'm_ne h_eq
    exact hα (IsUnit.of_mul_eq_one δ h_αδ)
  have h_dvd_prod : θ' ^ m ∣ α * γ := h_cancel ▸ dvd_refl (θ' ^ m)
  have h_θ'_dvd_α : θ' ^ m ∣ α :=
    hθ'_prime.pow_dvd_of_dvd_mul_right m h_not_dvd_γ h_dvd_prod
  obtain ⟨ε, hε⟩ := h_θ'_dvd_α
  have h_eq := h_cancel
  rw [hε, mul_assoc] at h_eq
  have h_εγ : ε * γ = 1 := by
    conv at h_eq => rhs; rw [← mul_one (θ' ^ m)]
    exact mul_left_cancel₀ hθ'm_ne h_eq
  have hε_unit : IsUnit ε := IsUnit.of_mul_eq_one γ h_εγ
  rw [hε]
  exact associated_mul_unit_left (θ' ^ m) ε hε_unit

lemma ufd_associated_dichotomy (α β : R) (m : ℕ)
    (h_prod : α * β = θ ^ m * θ' ^ m)
    (h_coprime : IsCoprime α β)
    (hα : ¬IsUnit α) (hβ : ¬IsUnit β) :
    Associated α (θ ^ m) ∨ Associated α (θ' ^ m) := by
  rcases theta_pow_dvd_of_coprime_prod α β m h_prod h_coprime with h | h
  · exact Or.inl (associated_of_theta_pow_dvd α β m h_prod h_coprime hα hβ h)
  · exact Or.inr (associated_of_theta_pow_dvd_right α β m h_prod h_coprime hα hβ h)

lemma associated_eq_or_neg (α γ : R) (h : Associated α γ) :
    α = γ ∨ α = -γ := by
  rcases h with ⟨u, rfl⟩
  rcases units_pm_one u with rfl | rfl
  · left; simp
  · right; simp

lemma ufd_power_association (α β : R) (m : ℕ)
    (h_prod : α * β = θ ^ m * θ' ^ m)
    (h_coprime : IsCoprime α β)
    (hα : ¬IsUnit α) (hβ : ¬IsUnit β) :
    (α = θ ^ m ∨ α = -(θ ^ m)) ∨ (α = θ' ^ m ∨ α = -(θ' ^ m)) := by
  have h_assoc := ufd_associated_dichotomy α β m h_prod h_coprime hα hβ
  rcases h_assoc with h_left | h_right
  · left; exact associated_eq_or_neg α (θ ^ m) h_left
  · right; exact associated_eq_or_neg α (θ' ^ m) h_right

end RamanujanNagell
