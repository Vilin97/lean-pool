/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.Tactic.Ring

/-!
# Normalized height-one valuations under ring equivalences

Identity-on-fraction-field ring equivalences identify corresponding valuation
rings. Surjectivity then identifies their integer-valued normalizations.
-/

@[expose] public section

namespace BGS.HasseWeil

open IsDedekindDomain Multiplicative WithZero
open scoped nonZeroDivisors

noncomputable section

/-- Transport the condition of belonging to a height-one valuation ring
across an identity-on-fraction-field ring equivalence. -/
theorem heightOneValuation_le_one_of_ringEquiv
    {R S F : Type*} [CommRing R] [CommRing S] [Field F]
    [Algebra R F] [Algebra S F] [IsFractionRing R F]
    [IsFractionRing S F] [IsDedekindDomain R] [IsDedekindDomain S]
    (e : R ≃+* S)
    (halg : ∀ r : R, algebraMap S F (e r) = algebraMap R F r)
    (q : HeightOneSpectrum R) (q' : HeightOneSpectrum S)
    (hideal : q'.asIdeal = q.asIdeal.comap e.symm)
    {x : F} (hx : q.valuation F x ≤ 1) : q'.valuation F x ≤ 1 := by
  obtain ⟨n, d, hnd⟩ := q.exists_primeCompl_mul_eq_of_integer x hx
  have hd' : e d.1 ∉ q'.asIdeal := by
    intro hmem
    have hd : (d.1 : R) ∉ q.asIdeal := d.2
    apply hd
    rw [hideal] at hmem
    change e.symm (e d.1) ∈ q.asIdeal at hmem
    simpa using hmem
  have hnd' :
      x * algebraMap S F (e d.1) = algebraMap S F (e n) := by
    simpa only [halg] using hnd
  have hval := congrArg (q'.valuation F) hnd'
  rw [map_mul, q'.valuation_eq_one_iff_notMem (K := F).2 hd'] at hval
  simp only [mul_one] at hval
  rw [hval]
  exact q'.valuation_le_one (K := F) (e n)

/-- Identity-on-fraction-field equivalences identify the valuation rings of
corresponding height-one primes. -/
theorem heightOneValuation_isEquiv_of_ringEquiv
    {R S F : Type*} [CommRing R] [CommRing S] [Field F]
    [Algebra R F] [Algebra S F] [IsFractionRing R F]
    [IsFractionRing S F] [IsDedekindDomain R] [IsDedekindDomain S]
    (e : R ≃+* S)
    (halg : ∀ r : R, algebraMap S F (e r) = algebraMap R F r)
    (q : HeightOneSpectrum R) (q' : HeightOneSpectrum S)
    (hideal : q'.asIdeal = q.asIdeal.comap e.symm) :
    (q.valuation F).IsEquiv (q'.valuation F) := by
  apply Valuation.isEquiv_of_val_le_one
  intro x
  constructor
  · exact heightOneValuation_le_one_of_ringEquiv
      e halg q q' hideal
  · intro hx
    have halg' : ∀ s : S,
        algebraMap R F (e.symm s) = algebraMap S F s := by
      intro s
      rw [← halg (e.symm s), e.apply_symm_apply]
    have hideal' : q.asIdeal = q'.asIdeal.comap e := by
      ext r
      rw [Ideal.mem_comap, hideal, Ideal.mem_comap]
      simp
    exact heightOneValuation_le_one_of_ringEquiv
      e.symm halg' q' q hideal' hx

/-- Equivalent surjective valuations with value group `ℤᵐ⁰` have the same
normalization. -/
theorem normalizedIntValuation_eq_of_isEquiv_of_surjective
    {F : Type*} [Field F] (v w : Valuation F ℤᵐ⁰)
    (hvw : v.IsEquiv w) (hv : Function.Surjective v)
    (hw : Function.Surjective w) : v = w := by
  obtain ⟨π, hvπ⟩ := hv (WithZero.exp (-1 : ℤ))
  have hπ : π ≠ 0 := by
    apply (Valuation.ne_zero_iff v).mp
    rw [hvπ]
    exact WithZero.exp_ne_zero
  have hwπ0 : w π ≠ 0 :=
    (hvw.eq_zero.ne).mp ((Valuation.ne_zero_iff v).2 hπ)
  let m : ℤ := -WithZero.log (w π)
  have hmpos : 0 < m := by
    have hvπlt : v π < 1 := by
      rw [hvπ, ← WithZero.exp_zero, WithZero.exp_lt_exp]
      omega
    have hwπlt : w π < 1 := hvw.lt_one_iff_lt_one.mp hvπlt
    have hlog : WithZero.log (w π) < 0 := by
      rw [← WithZero.log_one]
      exact (WithZero.log_lt_log hwπ0 one_ne_zero).2 hwπlt
    dsimp only [m]
    omega
  have hformula (x : F) (hx : x ≠ 0) :
      w x = WithZero.exp (m * WithZero.log (v x)) := by
    have hvx0 : v x ≠ 0 := (Valuation.ne_zero_iff v).2 hx
    let n : ℤ := WithZero.log (v x)
    have hvpow : v (π ^ (-n)) = v x := by
      rw [map_zpow₀, hvπ, ← WithZero.exp_zsmul]
      rw [← WithZero.exp_log hvx0]
      congr 1
      dsimp only [n]
      simp
    have hwpow : w (π ^ (-n)) = w x := hvw.eq_iff.mp hvpow
    calc
      w x = w (π ^ (-n)) := hwpow.symm
      _ = (w π) ^ (-n) := by rw [map_zpow₀]
      _ = WithZero.exp ((-n) • WithZero.log (w π)) := by
        rw [WithZero.exp_zsmul, WithZero.exp_log hwπ0]
      _ = WithZero.exp (m * WithZero.log (v x)) := by
        congr 1
        dsimp only [m, n]
        ring
  obtain ⟨y, hwy⟩ := hw (WithZero.exp (1 : ℤ))
  have hy : y ≠ 0 := by
    apply (Valuation.ne_zero_iff w).mp
    rw [hwy]
    exact WithZero.exp_ne_zero
  have hm : m * WithZero.log (v y) = 1 := by
    apply WithZero.exp_injective
    rw [← hformula y hy, hwy]
  have hm1 : m = 1 := by
    rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hm with h | h
    · exact h.1
    · omega
  ext x
  by_cases hx : x = 0
  · subst x
    simp
  · rw [hformula x hx, hm1, one_mul,
      WithZero.exp_log ((Valuation.ne_zero_iff v).2 hx)]

/-- Corresponding height-one primes have exactly the same normalized
`ℤᵐ⁰`-valued valuation under an identity-on-fraction-field equivalence. -/
theorem heightOneValuation_eq_of_ringEquiv
    {R S F : Type*} [CommRing R] [CommRing S] [Field F]
    [Algebra R F] [Algebra S F] [IsFractionRing R F]
    [IsFractionRing S F] [IsDedekindDomain R] [IsDedekindDomain S]
    (e : R ≃+* S)
    (halg : ∀ r : R, algebraMap S F (e r) = algebraMap R F r)
    (q : HeightOneSpectrum R) (q' : HeightOneSpectrum S)
    (hideal : q'.asIdeal = q.asIdeal.comap e.symm) :
    q.valuation F = q'.valuation F := by
  apply normalizedIntValuation_eq_of_isEquiv_of_surjective
  · exact heightOneValuation_isEquiv_of_ringEquiv e halg q q' hideal
  · exact HeightOneSpectrum.valuation_surjective (K := F) q
  · exact HeightOneSpectrum.valuation_surjective (K := F) q'

end

end BGS.HasseWeil
