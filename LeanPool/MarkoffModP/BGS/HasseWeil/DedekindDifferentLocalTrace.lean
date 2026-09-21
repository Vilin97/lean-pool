/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.AdicValuation

open scoped nonZeroDivisors

open Set Function UniqueFactorizationMonoid IsDedekindDomain
  IsDedekindDomain.HeightOneSpectrum

noncomputable section

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

namespace FractionalIdeal

theorem le_iff_count_ge {I J : FractionalIdeal R⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0) :
    I ≤ J ↔ ∀ v : HeightOneSpectrum R, count K v J ≤ count K v I := by
  constructor
  · intro h v
    exact count_mono K v hI h
  · intro h
    rw [← finprod_heightOneSpectrum_factorization' (K := K) hI,
      ← finprod_heightOneSpectrum_factorization' (K := K) hJ]
    have hfinite (A : FractionalIdeal R⁰ K) :
        (fun v : HeightOneSpectrum R ↦
          (v.asIdeal : FractionalIdeal R⁰ K) ^ count K v A).HasFiniteMulSupport := by
      have hcount : Set.Finite {v : HeightOneSpectrum R | count K v A ≠ 0} := by
        simpa only [Filter.eventually_cofinite] using finite_factors (K := K) A
      exact hcount.subset fun v hv hzero ↦ by
        apply hv
        simpa [hzero]
    apply finprod_le_finprod
    · exact hfinite I
    · exact fun _ ↦ zero_le _
    · exact hfinite J
    · intro v
      exact zpow_le_zpow_right_of_le_one₀
        (show 0 < (v.asIdeal : FractionalIdeal R⁰ K) from bot_lt_iff_ne_bot.mpr
          (coeIdeal_ne_zero.mpr v.ne_bot))
        coeIdeal_le_one (h v)

theorem count_coeIdeal_eq_multiplicity (I : Ideal R) (hI : I ≠ ⊥)
    (v : HeightOneSpectrum R) :
    count K v (I : FractionalIdeal R⁰ K) = (multiplicity v.asIdeal I : ℤ) := by
  rw [count_coe K v hI,
    Ideal.count_associates_factors_eq hI v.isPrime v.ne_bot,
    HeightOneSpectrum.count_normalizedFactors_eq_multiplicity hI]

theorem mem_iff_count_ge {I : FractionalIdeal R⁰ K} (hI : I ≠ 0)
    {x : K} (hx : x ≠ 0) :
    x ∈ I ↔ ∀ v : HeightOneSpectrum R,
      count K v I ≤ count K v (spanSingleton R⁰ x) := by
  rw [← spanSingleton_le_iff_mem,
    le_iff_count_ge (spanSingleton_ne_zero_iff.mpr hx) hI]

end FractionalIdeal

universe u

variable (A K₀ : Type*) {L : Type u} {B : Type*}
variable [CommRing A] [Field K₀] [CommRing B] [Field L]
variable [Algebra A K₀] [Algebra B L] [Algebra A B] [Algebra K₀ L] [Algebra A L]
variable [IsScalarTower A K₀ L] [IsScalarTower A B L]
variable [IsDomain A] [IsFractionRing A K₀]
variable [FiniteDimensional K₀ L] [Algebra.IsSeparable K₀ L]
variable [IsIntegralClosure B A L] [IsFractionRing B L] [IsIntegrallyClosed A]
variable [IsDedekindDomain B]
variable [Module.IsTorsionFree A B]
variable [Algebra.IsIntegral A B]

namespace HeightOneSpectrum

theorem algebraMap_mem_pow_of_mem_under_pow
    (q : HeightOneSpectrum B) (c : A) (n : ℕ)
    (hc : c ∈ (q.under A).asIdeal ^ n) :
    algebraMap A B c ∈ q.asIdeal ^ n := by
  have hmap :
      algebraMap A B c ∈
        Ideal.map (algebraMap A B) ((q.under A).asIdeal ^ n) :=
    Ideal.mem_map_of_mem (algebraMap A B) hc
  rw [Ideal.map_pow] at hmap
  exact (pow_le_pow_left'
    (Ideal.map_le_iff_le_comap.mpr (show
      (q.under A).asIdeal ≤ q.asIdeal.comap (algebraMap A B) from le_rfl)) n) hmap

theorem natCast_le_count_spanSingleton_algebraMap_of_mem_under_pow
    (q : HeightOneSpectrum B) (c : A) (n : ℕ) (hc0 : c ≠ 0)
    (hc : c ∈ (q.under A).asIdeal ^ n) :
    (n : ℤ) ≤ FractionalIdeal.count L q
      (FractionalIdeal.spanSingleton B⁰ (algebraMap A L c)) := by
  have hcB : algebraMap A B c ∈ q.asIdeal ^ n :=
    algebraMap_mem_pow_of_mem_under_pow A q c n hc
  have hcL : algebraMap A L c ∈
      ((q.asIdeal ^ n : Ideal B) : FractionalIdeal B⁰ L) := by
    rw [FractionalIdeal.mem_coeIdeal]
    refine ⟨algebraMap A B c, hcB, ?_⟩
    exact (IsScalarTower.algebraMap_apply A B L c).symm
  have hle :
      FractionalIdeal.spanSingleton B⁰ (algebraMap A L c) ≤
        ((q.asIdeal ^ n : Ideal B) : FractionalIdeal B⁰ L) :=
    FractionalIdeal.spanSingleton_le_iff_mem.mpr hcL
  have hcount := FractionalIdeal.count_mono L q
    (FractionalIdeal.spanSingleton_ne_zero_iff.mpr
      (by
        rw [IsScalarTower.algebraMap_apply A B L]
        simpa using (IsFractionRing.injective B L).ne
          ((FaithfulSMul.algebraMap_injective A B).ne hc0))) hle
  simpa [FractionalIdeal.coeIdeal_pow, FractionalIdeal.count_pow,
    FractionalIdeal.count_self] using hcount

end HeightOneSpectrum

namespace BGS.HasseWeil

theorem count_dual_one_eq_neg_different_multiplicity
    (q : HeightOneSpectrum B) :
    FractionalIdeal.count L q
      (FractionalIdeal.dual A K₀ (1 : FractionalIdeal B⁰ L)) =
      -(multiplicity q.asIdeal (differentIdeal A B) : ℤ) := by
  have hdiff : differentIdeal A B ≠ ⊥ := by
    apply (FractionalIdeal.coeIdeal_ne_zero (K := L)).mp
    rw [coeIdeal_differentIdeal A K₀ L B]
    exact inv_ne_zero (FractionalIdeal.dual_ne_zero A K₀
      (by exact one_ne_zero : (1 : FractionalIdeal B⁰ L) ≠ 0))
  have hdual :
      FractionalIdeal.dual A K₀ (1 : FractionalIdeal B⁰ L) =
        ((differentIdeal A B : Ideal B) : FractionalIdeal B⁰ L)⁻¹ := by
    apply inv_injective
    rw [inv_inv, ← coeIdeal_differentIdeal A K₀ L B]
  rw [hdual, FractionalIdeal.count_inv,
    FractionalIdeal.count_coeIdeal_eq_multiplicity (K := L) _ hdiff]

theorem mem_dual_one_iff_different_multiplicity_le_count
    {x : L} (hx : x ≠ 0) :
    x ∈ FractionalIdeal.dual A K₀ (1 : FractionalIdeal B⁰ L) ↔
      ∀ q : HeightOneSpectrum B,
        -(multiplicity q.asIdeal (differentIdeal A B) : ℤ) ≤
          FractionalIdeal.count L q (FractionalIdeal.spanSingleton B⁰ x) := by
  rw [FractionalIdeal.mem_iff_count_ge
    (FractionalIdeal.dual_ne_zero A K₀
      (by exact one_ne_zero : (1 : FractionalIdeal B⁰ L) ≠ 0)) hx]
  exact forall_congr' fun q ↦ by
    rw [count_dual_one_eq_neg_different_multiplicity A K₀ q]

theorem trace_mem_algebraMap_range_of_different_multiplicity_le_count
    {z : L} (hz : z ≠ 0)
    (hcount : ∀ q : HeightOneSpectrum B,
      -(multiplicity q.asIdeal (differentIdeal A B) : ℤ) ≤
        FractionalIdeal.count L q (FractionalIdeal.spanSingleton B⁰ z)) :
    Algebra.trace K₀ L z ∈ (algebraMap A K₀).range := by
  have hzdual : z ∈
      FractionalIdeal.dual A K₀ (1 : FractionalIdeal B⁰ L) :=
    (mem_dual_one_iff_different_multiplicity_le_count A K₀ hz).mpr hcount
  have htrace := (FractionalIdeal.mem_dual
    (A := A) (K := K₀) (I := (1 : FractionalIdeal B⁰ L))
    (by exact one_ne_zero)).mp hzdual (1 : L) (by simp)
  simpa [Algebra.traceForm_apply] using htrace

theorem finite_badDifferentCount_set (hdiff : differentIdeal A B ≠ ⊥) (y : L) :
    Set.Finite {q : HeightOneSpectrum B |
      ¬ (-(multiplicity q.asIdeal (differentIdeal A B) : ℤ) ≤
        FractionalIdeal.count L q (FractionalIdeal.spanSingleton B⁰ y))} := by
  have hdiffFinite : Set.Finite {q : HeightOneSpectrum B |
      FractionalIdeal.count L q
        ((differentIdeal A B : Ideal B) : FractionalIdeal B⁰ L) ≠ 0} := by
    simpa only [Filter.eventually_cofinite] using
      FractionalIdeal.finite_factors
        (K := L) ((differentIdeal A B : Ideal B) : FractionalIdeal B⁰ L)
  have hyFinite : Set.Finite {q : HeightOneSpectrum B |
      FractionalIdeal.count L q (FractionalIdeal.spanSingleton B⁰ y) ≠ 0} := by
    simpa only [Filter.eventually_cofinite] using
      FractionalIdeal.finite_factors
        (K := L) (FractionalIdeal.spanSingleton B⁰ y)
  refine (hdiffFinite.union hyFinite).subset ?_
  intro q hbad
  by_contra hq
  have hqdiff : FractionalIdeal.count L q
      ((differentIdeal A B : Ideal B) : FractionalIdeal B⁰ L) = 0 := by
    by_contra hne
    exact hq (by
      rw [Set.mem_union, Set.mem_setOf_eq, Set.mem_setOf_eq]
      exact Or.inl hne)
  have hqy : FractionalIdeal.count L q
      (FractionalIdeal.spanSingleton B⁰ y) = 0 := by
    by_contra hne
    exact hq (by
      rw [Set.mem_union, Set.mem_setOf_eq, Set.mem_setOf_eq]
      exact Or.inr hne)
  apply hbad
  rw [← FractionalIdeal.count_coeIdeal_eq_multiplicity
    (K := L) (differentIdeal A B) hdiff, hqdiff, hqy]
  simp

theorem exists_base_multiplier_clearing_different_counts
    [IsDedekindDomain A]
    (hdiff : differentIdeal A B ≠ ⊥)
    (p : HeightOneSpectrum A) {y : L} (hy : y ≠ 0)
    (hlocal : ∀ q : HeightOneSpectrum B,
      q.under A = p →
        -(multiplicity q.asIdeal (differentIdeal A B) : ℤ) ≤
          FractionalIdeal.count L q (FractionalIdeal.spanSingleton B⁰ y)) :
    ∃ c : A, c ∉ p.asIdeal ∧
      ∀ q : HeightOneSpectrum B,
        -(multiplicity q.asIdeal (differentIdeal A B) : ℤ) ≤
          FractionalIdeal.count L q
            (FractionalIdeal.spanSingleton B⁰ (algebraMap A L c * y)) := by
  classical
  let bad : Finset (HeightOneSpectrum B) :=
    (finite_badDifferentCount_set (A := A) (B := B) (L := L) hdiff y).toFinset
  have hbad_iff (q : HeightOneSpectrum B) : q ∈ bad ↔
      ¬ (-(multiplicity q.asIdeal (differentIdeal A B) : ℤ) ≤
        FractionalIdeal.count L q (FractionalIdeal.spanSingleton B⁰ y)) := by
    simp [bad]
  let need : HeightOneSpectrum B → ℕ := fun q =>
    Int.toNat (-(multiplicity q.asIdeal (differentIdeal A B) : ℤ) -
      FractionalIdeal.count L q (FractionalIdeal.spanSingleton B⁰ y))
  let N : ℕ := ∑ q ∈ bad, need q
  have hbelow_ne (q : HeightOneSpectrum B) (hq : q ∈ bad) :
      (q.under A).asIdeal ≠ p.asIdeal := by
    intro heq
    have heq' : q.under A = p :=
      HeightOneSpectrum.ext heq
    exact (hbad_iff q).mp hq (hlocal q heq')
  let selected : Finset (Ideal A) :=
    insert p.asIdeal
      (bad.image fun q => (q.under A).asIdeal)
  have hselectedPrime : ∀ P ∈ selected, Prime P := by
    intro P hP
    rw [Finset.mem_insert] at hP
    rcases hP with rfl | hP
    · exact p.prime
    · rcases Finset.mem_image.mp hP with ⟨q, hq, rfl⟩
      exact (q.under A).prime
  let exponent : Ideal A → ℕ := fun P => if P = p.asIdeal then 1 else N
  let target : selected → A := fun P => if (P : Ideal A) = p.asIdeal then 1 else 0
  obtain ⟨c, hc⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal
    (s := selected) (fun P : Ideal A => P) exponent hselectedPrime
    (by
      intro P hP Q hQ hPQ
      simpa using hPQ)
    target
  have hpSelected : p.asIdeal ∈ selected := Finset.mem_insert_self _ _
  have hcpow := hc p.asIdeal hpSelected
  have hcp : c - 1 ∈ p.asIdeal := by
    simpa [target, exponent] using hcpow
  have hcnot : c ∉ p.asIdeal := by
    intro hcP
    have hone : (1 : A) ∈ p.asIdeal := by
      have hsub := p.asIdeal.sub_mem hcP hcp
      convert hsub using 1 <;> ring
    exact p.isPrime.ne_top ((Ideal.eq_top_iff_one p.asIdeal).mpr hone)
  have hc0 : c ≠ 0 := fun hcZero => hcnot (hcZero.symm ▸ p.asIdeal.zero_mem)
  refine ⟨c, hcnot, ?_⟩
  intro q
  have hcL0 : algebraMap A L c ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply A B L]
    simpa using (IsFractionRing.injective B L).ne
      ((FaithfulSMul.algebraMap_injective A B).ne hc0)
  have hspanCount :
      FractionalIdeal.count L q
          (FractionalIdeal.spanSingleton B⁰ (algebraMap A L c * y)) =
        FractionalIdeal.count L q
            (FractionalIdeal.spanSingleton B⁰ (algebraMap A L c)) +
          FractionalIdeal.count L q (FractionalIdeal.spanSingleton B⁰ y) := by
    rw [← FractionalIdeal.spanSingleton_mul_spanSingleton,
      FractionalIdeal.count_mul]
    · exact FractionalIdeal.spanSingleton_ne_zero_iff.mpr hcL0
    · exact FractionalIdeal.spanSingleton_ne_zero_iff.mpr hy
  rw [hspanCount]
  by_cases hq : q ∈ bad
  · have hqSelected : (q.under A).asIdeal ∈ selected := by
      change (q.under A).asIdeal ∈
        insert p.asIdeal
          (bad.image fun r => (r.under A).asIdeal)
      exact Finset.mem_insert.mpr <| Or.inr <|
        Finset.mem_image.mpr ⟨q, hq, rfl⟩
    have hcqpow := hc (q.under A).asIdeal hqSelected
    have hrne : q.asIdeal.comap (algebraMap A B) ≠ p.asIdeal := by
      simpa using hbelow_ne q hq
    have hcq : c ∈ (q.under A).asIdeal ^ N := by
      simpa [target, exponent, hrne] using hcqpow
    have hNcount : (N : ℤ) ≤
        FractionalIdeal.count L q
          (FractionalIdeal.spanSingleton B⁰ (algebraMap A L c)) :=
      HeightOneSpectrum.natCast_le_count_spanSingleton_algebraMap_of_mem_under_pow
        (A := A) (B := B) (L := L) q c N hc0 hcq
    have hneedNonneg : 0 ≤
        -(multiplicity q.asIdeal (differentIdeal A B) : ℤ) -
          FractionalIdeal.count L q (FractionalIdeal.spanSingleton B⁰ y) := by
      have := (hbad_iff q).mp hq
      omega
    have hneedCast : (need q : ℤ) =
        -(multiplicity q.asIdeal (differentIdeal A B) : ℤ) -
          FractionalIdeal.count L q (FractionalIdeal.spanSingleton B⁰ y) := by
      exact Int.toNat_of_nonneg hneedNonneg
    have hneedN : need q ≤ N := by
      dsimp [N]
      exact Finset.single_le_sum (fun i _ => Nat.zero_le (need i)) hq
    omega
  · have hgood :
        -(multiplicity q.asIdeal (differentIdeal A B) : ℤ) ≤
          FractionalIdeal.count L q (FractionalIdeal.spanSingleton B⁰ y) := by
      by_contra hnot
      exact hq ((hbad_iff q).mpr hnot)
    have hzeroCount : (0 : ℤ) ≤
        FractionalIdeal.count L q
          (FractionalIdeal.spanSingleton B⁰ (algebraMap A L c)) :=
      HeightOneSpectrum.natCast_le_count_spanSingleton_algebraMap_of_mem_under_pow
        (A := A) (B := B) (L := L) q c 0 hc0 (by simp)
    omega

theorem valuation_trace_le_one_of_different_count_bounds_over
    [IsDedekindDomain A]
    (p : HeightOneSpectrum A) {y : L} (hy : y ≠ 0)
    (hlocal : ∀ q : HeightOneSpectrum B,
      q.under A = p →
        -(multiplicity q.asIdeal (differentIdeal A B) : ℤ) ≤
          FractionalIdeal.count L q (FractionalIdeal.spanSingleton B⁰ y)) :
    p.valuation K₀ (Algebra.trace K₀ L y) ≤ 1 := by
  have hdiff : differentIdeal A B ≠ ⊥ := by
    apply (FractionalIdeal.coeIdeal_ne_zero (K := L)).mp
    rw [coeIdeal_differentIdeal A K₀ L B]
    exact inv_ne_zero (FractionalIdeal.dual_ne_zero A K₀
      (by exact one_ne_zero : (1 : FractionalIdeal B⁰ L) ≠ 0))
  obtain ⟨c, hcnot, hcount⟩ :=
    exists_base_multiplier_clearing_different_counts
      (A := A) (B := B) (L := L) hdiff p hy hlocal
  have hc0 : c ≠ 0 := fun hcZero => hcnot (hcZero.symm ▸ p.asIdeal.zero_mem)
  have hcL0 : algebraMap A L c ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply A B L]
    simpa using (IsFractionRing.injective B L).ne
      ((FaithfulSMul.algebraMap_injective A B).ne hc0)
  have hcy0 : algebraMap A L c * y ≠ 0 := mul_ne_zero hcL0 hy
  have htraceRange :
      Algebra.trace K₀ L (algebraMap A L c * y) ∈ (algebraMap A K₀).range :=
    trace_mem_algebraMap_range_of_different_multiplicity_le_count
      (A := A) (K₀ := K₀) (B := B) (L := L) hcy0 hcount
  obtain ⟨a, ha⟩ := htraceRange
  have htraceSmul :
      Algebra.trace K₀ L (algebraMap A L c * y) =
        algebraMap A K₀ c * Algebra.trace K₀ L y := by
    rw [IsScalarTower.algebraMap_apply A K₀ L]
    simpa [Algebra.smul_def] using
      (Algebra.trace K₀ L).map_smul (algebraMap A K₀ c) y
  have hcVal : p.valuation K₀ (algebraMap A K₀ c) = 1 :=
    (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := K₀) p).mpr hcnot
  calc
    p.valuation K₀ (Algebra.trace K₀ L y) =
        p.valuation K₀ (algebraMap A K₀ c) *
          p.valuation K₀ (Algebra.trace K₀ L y) := by rw [hcVal, one_mul]
    _ = p.valuation K₀
          (algebraMap A K₀ c * Algebra.trace K₀ L y) := by
      rw [map_mul]
    _ = p.valuation K₀
          (Algebra.trace K₀ L (algebraMap A L c * y)) := by rw [htraceSmul]
    _ = p.valuation K₀ (algebraMap A K₀ a) := by rw [← ha]
    _ ≤ 1 := p.valuation_le_one a

end BGS.HasseWeil
