/-
Copyright (c) 2026 James Huang, Samuël Borza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Huang, Samuël Borza
-/
import Mathlib.Analysis.Complex.IsIntegral
import LeanPool.IsTranscendentalPi.AnalyticEstimates
import LeanPool.IsTranscendentalPi.ScaledAuxiliaryPolynomial
import LeanPool.IsTranscendentalPi.SymmetricPolynomials

/-!
# Transcendence of `π`

The main theorem: the complex number `π` (and hence the real number `π`) is
transcendental over `ℚ`, assembling the analytic and algebraic estimates of the
preceding modules into Niven's contradiction argument.
-/

open Polynomial

open Complex

open scoped Polynomial
open scoped BigOperators

noncomputable section

/-- If `π` is not transcendental over `ℚ`, then `π` is algebraic over `ℚ`. -/
lemma isAlgebraic_pi_of_not_transcendental_pi
    (hpi : ¬ Transcendental ℚ (Real.pi : ℂ)) : IsAlgebraic ℚ (Real.pi : ℂ) := by
  simpa [Transcendental] using hpi

/-- If `π` is algebraic over `ℚ`, then so is `π i`. -/
lemma isAlgebraic_I_mul_pi_of_isAlgebraic_pi
    (hpi : IsAlgebraic ℚ (Real.pi : ℂ)) : IsAlgebraic ℚ (Real.pi * I : ℂ) := by
  simpa [mul_comm] using (isAlgebraic_iff_isIntegral.2 Complex.isIntegral_rat_I).mul hpi

/-- If `π i` is algebraic over `ℚ`, there is a monic rational polynomial vanishing at `π i`. -/
lemma exists_monic_rat_poly_aeval_Ipi_eq_zero
    (hpi : IsAlgebraic ℚ (Real.pi * I : ℂ)) :
    ∃ B : ℚ[X], B.Monic ∧ aeval (Real.pi * I) B = 0 := by
  exact ⟨minpoly ℚ (Real.pi * I : ℂ), minpoly.monic hpi.isIntegral,
    minpoly.aeval ℚ (Real.pi * I : ℂ)⟩

/-- The complex number `π` is transcendental over `ℚ`. -/
theorem IsTranscendentalPi : Transcendental ℚ (Real.pi : ℂ) := by
  by_contra hpi
  obtain ⟨B, hBmonic, hBroot⟩ := exists_monic_rat_poly_aeval_Ipi_eq_zero
    <| isAlgebraic_I_mul_pi_of_isAlgebraic_pi <| isAlgebraic_pi_of_not_transcendental_pi hpi
  have hB : B ≠ 0 := hBmonic.ne_zero
  obtain ⟨n, a, ha⟩ := exists_valuesFin_eq_multiset (nonzeroSubsetSums (B.aroots ℂ))
  have hcard : (nonzeroSubsetSums (B.aroots ℂ)).card = n := by
    simpa [valuesFin] using congrArg Multiset.card ha
  let b : Fin n → ℂ := fun _ => 1
  obtain ⟨d, r, hr⟩ := exists_valuesFin_eq_aroots B
  obtain ⟨T', hT'⟩ := polyOfNonzeroSubsetSums_as_poly B r hBmonic hr
  have hT'aroots := aroots_of_T' T' d n r a hT' (by simpa [hr] using ha)
  have hT'monic : T'.Monic := monic_of_T' T' d r hT'
  have hT'deg : T'.natDegree = n := natDegree_of_T' T' d n r a hT' (by simpa [hr] using ha)
  have hT'zero : aeval (0 : ℂ) T' ≠ 0 :=
    aeval_zero_ne_zero_of_T' T' d n r a hT' (by simpa [hr] using ha)
  obtain ⟨T, c, hc, hT⟩ := ClearDenominatorOf T'
  have hTaroots : T.aroots ℂ = valuesFin a :=
    aroots_of_T T T' c d n r a hc hT hT' (by simpa [hr] using ha)
  have hroot : ∀ i : Fin n, a i ∈ T.aroots ℂ := by simp [hTaroots, valuesFin]
  have hTzero : aeval (0 : ℂ) T ≠ 0 :=
    aeval_zero_ne_zero_of_T T T' c d n r a hc hT hT' (by simpa [hr] using ha)
  have hn : 0 < n := by
    rw [← hcard]
    exact Multiset.card_pos_iff_exists_mem.2 ⟨Real.pi * I, mem_nonzeroSubsetSums_of_mem_of_ne_zero
            ((Polynomial.mem_aroots (p := B) (a := Real.pi * I)).2 ⟨hB, hBroot⟩)
            (by simp [Complex.I_ne_zero])⟩
  let k : ℕ := (subsetSums (B.aroots ℂ)).count 0
  have hk : k ≠ 0 := ne_of_gt <| by simpa [k, subsetSums] using
    (Multiset.count_pos.mpr <| Multiset.mem_map.2 ⟨0, by simp, by simp⟩)
  have hsum := sum_weighted_cexp_nonzeroSubsetSums_eq_neg_count_zero_subsetSums
                B hB hBroot a ha b (fun _ => rfl) k rfl
  let f : ℕ → ℤ := fun m =>
    if hm : Nat.Prime m then
      intSumAevalGp T T' c n a hc hT'monic hT'deg (by simpa [smul_eq_C_mul] using hT) hT'aroots m
    else 0
  have hf : ∀ᶠ p : {p : ℕ // Nat.Prime p} in Filter.atTop,
    c ^ (p * n - 1) * (∑ i : Fin n, b i * aeval (a i) (Gp T (p : ℕ))) = (f (p : ℕ) : ℂ) := by
    refine Filter.Eventually.of_forall fun p => ?_
    simpa [f, b, p.property] using
      SumAevalGp_as_intSumAevalGp T T' c (p : ℕ) n a hc p.property.pos hT'monic hT'deg
      (by
        rw [← smul_eq_C_mul]
        exact hT)
      hT'aroots
  have hUpper := sum_intExpNegPoly_asym_ubound n T hn a b (c ^ n : ℂ)
  have hLower := sum_Gp_asym_lbound n T a b (c ^ n) (k : ℤ) (fun m => c * f m) (pow_ne_zero _ hc)
    (by simp [hk]) hTzero <| by
      filter_upwards [hf] with p hp
      simp only [Int.cast_mul, Int.cast_pow]
      rw [← hp, ← pow_mul, Nat.mul_comm]
      nth_rw 1 [← Nat.sub_add_cancel (Nat.succ_le_of_lt (Nat.mul_pos p.property.pos hn))]
      rw [pow_succ']
      ac_rfl
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hUpper
  letI : Nonempty {p : ℕ // Nat.Prime p} := ⟨⟨2, by decide⟩⟩
  obtain ⟨q, hq⟩ := Filter.eventually_atTop.1 hLower
  obtain ⟨p, hp, hpprime⟩ := Nat.exists_infinite_primes (max N (q : ℕ))
  exact
    (not_le_of_gt (hN p (le_trans (le_max_left N (q : ℕ)) hp))) <| by
      rw [intExpNegPoly_eq n p T a b hn hpprime.pos
        (ne_zero_of_nonzeroSubsetSums_eq_valuesFin ha) hroot, hsum]
      simpa using hq ⟨p, hpprime⟩ (by
        change (q : ℕ) ≤ p
        exact le_trans (le_max_right N (q : ℕ)) hp)

/-- The real number `π` is transcendental over `ℚ`. -/
theorem IsTranscendentalPiReal : Transcendental ℚ (Real.pi : ℝ) :=
  (transcendental_algebraMap_iff
    (R := ℚ) (S := ℝ) (A := ℂ) Complex.ofReal_injective).1 IsTranscendentalPi
