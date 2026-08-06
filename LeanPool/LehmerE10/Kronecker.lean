/-
Copyright (c) 2026 Dillon Ryan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dillon Ryan
-/

import LeanPool.LehmerE10.Defs
import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.NormNum.Prime

/-!
# basic facts about Lehmer's polynomial `L`, and Kronecker's theorem.
Contents:
  • degree/monicity of `L` and the evaluation witnesses `L(1) = −1`, `L(−1) = 1`,
    `L(2) = 1291` (prime);
  • `kronecker_roots` — Kronecker's theorem (1857) in root form: every complex root
    of a monic integer polynomial, all of whose complex roots lie on the unit
    circle, is a root of unity.  Proved from Mathlib's
    `NumberField.Embeddings.pow_eq_one_of_norm_eq_one` applied inside the number
    field ℚ⟮z⟯.
  • `totient_le_of_lehmer_root` — a primitive k-th root of unity that is a root of
    `L` has φ(k) ≤ 10 (cyclotomic = minimal polynomial + degree bound).
Axiom footprint: `propext`, `Classical.choice`, `Quot.sound` only.
-/

namespace LehmerE10

open Polynomial

theorem lehmerPolynomial_natDegree : lehmerPolynomial.natDegree = 10 := by
  unfold lehmerPolynomial; compute_degree!

theorem lehmerPolynomial_monic : lehmerPolynomial.Monic := by
  unfold lehmerPolynomial; monicity!

theorem lehmerPolynomial_ne_zero : lehmerPolynomial ≠ 0 := lehmerPolynomial_monic.ne_zero

/-! ### The eval-witness integers (the kill table's three points). -/

theorem lehmer_eval_one : lehmerPolynomial.eval 1 = -1 := by
  unfold lehmerPolynomial; simp

theorem lehmer_eval_neg_one : lehmerPolynomial.eval (-1) = 1 := by
  unfold lehmerPolynomial; norm_num

theorem lehmer_eval_two : lehmerPolynomial.eval 2 = 1291 := by
  unfold lehmerPolynomial; norm_num

/-- 1291 is prime: the x = 2 witness kills every remaining non-prime-power modulus
    (Φ₁₂(2)=13, Φ₁₅(2)=151, Φ₂₀(2)=205, Φ₂₄(2)=241, Φ₃₀(2)=331 — none divide 1291). -/
theorem witness_1291_prime : Nat.Prime 1291 := by norm_num

/-! ### Kronecker's theorem: roots of unit-circle monic ℤ-polynomials are roots of unity. -/

/-- **Kronecker's theorem, root form**: every complex root of a monic integer
    polynomial, all of whose complex roots lie on the unit circle, is a root of unity.
    (The conclusion is stated root-wise: the `p ∣ xⁿ − 1` form fails for
    non-squarefree `p`.) -/
theorem kronecker_roots {p : Polynomial ℤ} (hm : p.Monic)
    (h1 : ∀ w ∈ (p.map (Int.castRingHom ℂ)).roots, ‖w‖ = 1)
    {z : ℂ} (hz : z ∈ (p.map (Int.castRingHom ℂ)).roots) :
    ∃ n : ℕ, 0 < n ∧ z ^ n = 1 := by
  have hmapne : p.map (Int.castRingHom ℂ) ≠ 0 := (hm.map _).ne_zero
  have hroot : (Polynomial.aeval z) p = 0 := by
    have h := (mem_roots hmapne).mp hz
    rw [IsRoot.def, eval_map] at h
    rwa [aeval_def, algebraMap_int_eq]
  -- z is an algebraic integer
  have hint : IsIntegral ℤ z := ⟨p, hm, by rw [← aeval_def]; exact hroot⟩
  -- the number field K = ℚ⟮z⟯
  have halg : IsAlgebraic ℚ z := (hint.tower_top (A := ℚ)).isAlgebraic
  let K := IntermediateField.adjoin ℚ ({z} : Set ℂ)
  have : FiniteDimensional ℚ K :=
    IntermediateField.adjoin.finiteDimensional halg.isIntegral
  have : NumberField K := ⟨⟩
  -- the generator, its integrality, and its image
  set x : K := IntermediateField.AdjoinSimple.gen ℚ z with hxdef
  have hgen : (algebraMap K ℂ) x = z := IntermediateField.AdjoinSimple.algebraMap_gen ℚ z
  have hinj : Function.Injective (algebraMap K ℂ) := (algebraMap K ℂ).injective
  have hxi : IsIntegral ℤ x := by
    exact (isIntegral_algebraMap_iff hinj).mp (hgen ▸ hint)
  -- the generator is itself a root of p inside K
  have hpx : (Polynomial.aeval x) p = 0 := by
    apply hinj
    rw [map_zero, ← Polynomial.aeval_algebraMap_apply, hgen]
    exact hroot
  -- every embedding sends x to a root of p, hence to the unit circle
  have hφ : ∀ φ : K →+* ℂ, ‖φ x‖ = 1 := by
    intro φ
    apply h1
    have hcomp : φ.comp (algebraMap ℤ K) = algebraMap ℤ ℂ := RingHom.ext_int _ _
    have hφx : (Polynomial.aeval (φ x)) p = 0 := by
      have h := congrArg φ hpx
      rw [map_zero] at h
      rw [aeval_def, ← hcomp, ← Polynomial.hom_eval₂, ← aeval_def, h]
    refine (mem_roots hmapne).mpr ?_
    rw [IsRoot.def, eval_map]
    rw [aeval_def, algebraMap_int_eq] at hφx
    exact hφx
  obtain ⟨n, hn, hxn⟩ := NumberField.Embeddings.pow_eq_one_of_norm_eq_one K ℂ hxi hφ
  refine ⟨n, hn, ?_⟩
  have h := congrArg (algebraMap K ℂ) hxn
  rwa [map_pow, map_one, hgen] at h

/-! ### The order bound: root-of-unity roots of L live in the eligible census. -/

/-- A primitive k-th root of unity that is a root of `lehmerPolynomial` (over ℚ) has
    φ(k) ≤ 10: cyclotomic k = minpoly, and the minpoly divides the degree-10 image. -/
theorem totient_le_of_lehmer_root {z : ℂ} {k : ℕ} (hk : 0 < k)
    (hprim : IsPrimitiveRoot z k)
    (hroot : (Polynomial.aeval z) (lehmerPolynomial.map (Int.castRingHom ℚ)) = 0) :
    k.totient ≤ 10 := by
  have hmin : cyclotomic k ℚ = minpoly ℚ z := cyclotomic_eq_minpoly_rat hprim hk
  have hmapne : lehmerPolynomial.map (Int.castRingHom ℚ) ≠ 0 :=
    (lehmerPolynomial_monic.map (Int.castRingHom ℚ)).ne_zero
  have hdvd : minpoly ℚ z ∣ lehmerPolynomial.map (Int.castRingHom ℚ) := minpoly.dvd ℚ z hroot
  have hdeg10 : (lehmerPolynomial.map (Int.castRingHom ℚ)).natDegree = 10 := by
    rw [lehmerPolynomial_monic.natDegree_map]; exact lehmerPolynomial_natDegree
  have hdeg := Polynomial.natDegree_le_of_dvd hdvd hmapne
  rwa [← hmin, natDegree_cyclotomic, hdeg10] at hdeg

/-- The moduli `k ≤ 66` with `φ(k) ≤ 10` — the only possible orders of
    root-of-unity roots of a degree-10 polynomial. -/
theorem eligible_totient_census :
    ((List.range 66).filter fun n => (n + 1).totient ≤ 10).map (· + 1) =
      [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16, 18, 20, 22, 24, 30] := by
  decide


end LehmerE10
