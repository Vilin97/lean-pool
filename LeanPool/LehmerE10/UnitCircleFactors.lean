/-
Copyright (c) 2026 Dillon Ryan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dillon Ryan
-/

import LeanPool.LehmerE10.CyclotomicKill
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# no factor of Lehmer's polynomial lives on the unit circle.
Contents:
  • `no_unit_circle_factor` — a monic ℤ-factor of `L` of positive degree cannot
    have all its complex roots on the unit circle: such a factor would carry a root
    of unity (`kronecker_roots`), whose cyclotomic minimal polynomial would descend
    to a cyclotomic ℤ-divisor of `L` (Gauss's lemma), refuted by
    `no_cyclotomic_divisor`.  So every proper factor must touch the off-circle
    Salem pair.
  • `norm_eq_one_of_trace_in_ball` — the on-circle half of the root dichotomy:
    `z + 1/z` real in `(−2, 2)` forces `‖z‖ = 1` (real `z` is excluded by AM–GM;
    the conjugate is then the reciprocal).
  • `two_le_self_add_inv` — the AM–GM inequality used above.
Axiom footprint: `propext`, `Classical.choice`, `Quot.sound` only.
-/

namespace LehmerE10

open Polynomial

/-! ### AM–GM face: a positive real plus its inverse is at least 2. -/

theorem two_le_self_add_inv {t : ℝ} (ht : 0 < t) : 2 ≤ t + 1 / t := by
  have hsq : 0 ≤ (t - 1) ^ 2 := sq_nonneg _
  have hmul : t * (t + 1 / t) = t ^ 2 + 1 := by
    field_simp
  nlinarith

/-! ### The on-circle half of the root dichotomy. -/

/-- If z + 1/z is a real number strictly inside (−2, 2), then ‖z‖ = 1: z cannot be
    real (AM–GM), and the conjugate — a root of the same real quadratic — must then
    be the reciprocal, giving ‖z‖² = z·conj z = 1. -/
theorem norm_eq_one_of_trace_in_ball {z : ℂ} {y : ℝ} (hz : z ≠ 0)
    (htr : z + 1 / z = (y : ℂ)) (hy : -2 < y) (hy' : y < 2) : ‖z‖ = 1 := by
  -- conj z satisfies the same relation
  have hconj : (starRingEnd ℂ) z + 1 / (starRingEnd ℂ) z = (y : ℂ) := by
    have := congrArg (starRingEnd ℂ) htr
    simpa [map_add, map_div₀, Complex.conj_ofReal] using this
  -- z and conj z are both roots of X² − yX + 1, whose roots are {z, 1/z}
  -- (from z + 1/z = y: the quadratic factors as (X − z)(X − 1/z))
  have hquad : ∀ w : ℂ, w ^ 2 - (y : ℂ) * w + 1 = (w - z) * (w - 1 / z) := by
    intro w
    have h1 : z * (1 / z) = 1 := by field_simp
    calc w ^ 2 - (y : ℂ) * w + 1
        = w ^ 2 - (z + 1 / z) * w + z * (1 / z) := by rw [htr, h1]
      _ = (w - z) * (w - 1 / z) := by ring
  -- conj z is a root of the quadratic
  have hcz0 : (starRingEnd ℂ) z ≠ 0 := by simpa using hz
  have hinvc : (starRingEnd ℂ) z * (1 / (starRingEnd ℂ) z) = 1 := by field_simp
  have hzero : ((starRingEnd ℂ) z) ^ 2 - (y : ℂ) * ((starRingEnd ℂ) z) + 1 = 0 := by
    linear_combination ((starRingEnd ℂ) z) * hconj - hinvc
  have hcz : ((starRingEnd ℂ) z - z) * ((starRingEnd ℂ) z - 1 / z) = 0 := by
    rw [← hquad ((starRingEnd ℂ) z)]
    exact hzero
  rcases mul_eq_zero.mp hcz with h | h
  · -- conj z = z : z is real, contradiction with |y| < 2 via AM–GM
    exfalso
    have hreal : ∃ t : ℝ, (t : ℂ) = z := by
      have := sub_eq_zero.mp h
      exact ⟨z.re, by
        have := Complex.conj_eq_iff_re.mp this
        exact this⟩
    obtain ⟨t, rfl⟩ := hreal
    have ht0 : t ≠ 0 := by simpa using hz
    have htr' : t + 1 / t = y := by
      have : ((t + 1 / t : ℝ) : ℂ) = (y : ℂ) := by push_cast; simpa using htr
      exact_mod_cast this
    rcases lt_or_gt_of_ne ht0 with hneg | hpos
    · have h2 := two_le_self_add_inv (t := -t) (by linarith)
      have hneg' : -t + 1 / -t = -(t + 1 / t) := by ring
      rw [hneg', htr'] at h2
      linarith
    · have h2 := two_le_self_add_inv hpos
      rw [htr'] at h2
      linarith
  · -- conj z = 1/z : ‖z‖² = 1
    have hczz : (starRingEnd ℂ) z = 1 / z := sub_eq_zero.mp h
    have hprod : z * (starRingEnd ℂ) z = 1 := by rw [hczz]; field_simp
    have h1 : ‖z * (starRingEnd ℂ) z‖ = 1 := by rw [hprod]; simp
    rw [norm_mul, RCLike.norm_conj] at h1
    rcases mul_self_eq_one_iff.mp h1 with h' | h'
    · exact h'
    · exfalso; have := norm_nonneg z; linarith

/-! ### THE CIRCLE IS CLOSED: no all-on-circle factor. -/

/-- **NO UNIT-CIRCLE FACTOR (proven)**: a monic factor of Lehmer with positive degree
    and all complex roots on the unit circle is impossible — its root of unity would
    give a cyclotomic ℤ-divisor of Lehmer, refuted by `no_cyclotomic_divisor`. -/
theorem no_unit_circle_factor {F : Polynomial ℤ} (hFm : F.Monic)
    (hdeg : 0 < F.natDegree) (hFdvd : F ∣ lehmerPolynomial)
    (hcirc : ∀ z ∈ (F.map (Int.castRingHom ℂ)).roots, ‖z‖ = 1) : False := by
  -- a complex root exists
  have hFCm : (F.map (Int.castRingHom ℂ)).Monic := hFm.map _
  have hFCdeg : 0 < (F.map (Int.castRingHom ℂ)).degree := by
    rw [hFm.degree_map]
    exact Polynomial.natDegree_pos_iff_degree_pos.mp hdeg
  obtain ⟨z, hzroot⟩ := Complex.exists_root hFCdeg
  have hz : z ∈ (F.map (Int.castRingHom ℂ)).roots :=
    (mem_roots hFCm.ne_zero).mpr hzroot
  -- z is a root of unity (Kronecker)
  obtain ⟨n, hn, hzn⟩ := kronecker_roots hFm hcirc hz
  have hfin : IsOfFinOrder z := isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, hzn⟩
  have hk : 0 < orderOf z := hfin.orderOf_pos
  have hprim : IsPrimitiveRoot z (orderOf z) := IsPrimitiveRoot.orderOf z
  -- z is a root of Lehmer over ℚ (through F ∣ L and the cast tower ℤ → ℚ → ℂ)
  have hLC : z ∈ (lehmerPolynomial.map (Int.castRingHom ℂ)).roots := by
    have hLne : lehmerPolynomial.map (Int.castRingHom ℂ) ≠ 0 :=
      (lehmerPolynomial_monic.map _).ne_zero
    exact Multiset.mem_of_le
      (roots.le_of_dvd hLne (Polynomial.map_dvd _ hFdvd)) hz
  have hzL : (Polynomial.aeval z) (lehmerPolynomial.map (Int.castRingHom ℚ)) = 0 := by
    have hLne : lehmerPolynomial.map (Int.castRingHom ℂ) ≠ 0 :=
      (lehmerPolynomial_monic.map _).ne_zero
    have h := (mem_roots hLne).mp hLC
    rw [IsRoot.def, eval_map] at h
    rw [aeval_def, Polynomial.eval₂_map]
    have hcomp : ((algebraMap ℚ ℂ).comp (Int.castRingHom ℚ)) = Int.castRingHom ℂ :=
      RingHom.ext_int _ _
    rwa [hcomp]
  -- minpoly = cyclotomic (orderOf z) over ℚ divides L over ℚ, then descends to ℤ
  have hdvdQ : cyclotomic (orderOf z) ℚ ∣ lehmerPolynomial.map (Int.castRingHom ℚ) :=
    (cyclotomic_eq_minpoly_rat hprim hk) ▸ minpoly.dvd ℚ z hzL
  have hdvdZ : cyclotomic (orderOf z) ℤ ∣ lehmerPolynomial := by
    rw [IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast _ _
      (cyclotomic.monic _ ℤ).isPrimitive lehmerPolynomial_monic.isPrimitive]
    rwa [Polynomial.map_cyclotomic_int]
  exact no_cyclotomic_divisor hk hdvdZ


end LehmerE10
