/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.JMNPeriodicity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.LocalFinite
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! Local finiteness and continuity of the explicit `j_{m,n}` coefficient. -/

@[expose] public section

noncomputable section

open Filter
open scoped Topology

namespace AVenhance.Infra.Section3

open AVenhance

/-- One odd-index matrix term used to establish regularity of the moment sum. -/
def JMNRegularity.jMNSummand' {β : ℝ} (I : Ingredients β) (m n : ℕ)
    (k : {k : ℤ // Odd k}) (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (I.zetaMK m k.1 t * iteratedDeriv n (I.zetaMK m k.1) t) •
    ((if k.1 % 4 = 1 then !![0, 0; 0, 1] else 0) +
      (if k.1 % 4 = 3 then !![1, 0; 0, 0] else 0) :
        Matrix (Fin 2) (Fin 2) ℝ)

theorem JMNRegularity.zetaMK_index_abs_bound {β : ℝ} (I : Ingredients β)
    {m : ℕ} (t₀ t : ℝ) (k : ℤ)
    (ht : t ∈ Set.Icc (t₀ - 1) (t₀ + 1))
    (hne : I.zetaMK m k t ≠ 0) :
    |(k : ℝ)| ≤ (|t₀| + 1) / tau β I.Λ m + 2 / 3 := by
  have hτ : 0 < tau β I.Λ m :=
    Infra.Ingredients.tau_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  let u := (t - (k : ℝ) * tau β I.Λ m) / tau β I.Λ m
  have hu : u ∈ Set.Icc (-(2 / 3 : ℝ)) (2 / 3) := by
    by_contra hnot
    have hzero : indIcc (-(2 / 3)) (2 / 3) u = 0 := by
      unfold indIcc
      rw [Set.indicator_of_notMem hnot]
    have hle := I.zeta_le_ind u
    rw [hzero] at hle
    have hpos : 0 < I.zeta u := lt_of_le_of_ne (I.zeta_nonneg u) (Ne.symm hne)
    change I.zeta u ≤ 0 at hle
    linarith
  have hlo := (le_div_iff₀ hτ).mp hu.1
  have hhi := (div_le_iff₀ hτ).mp hu.2
  have hklower : t / tau β I.Λ m - 2 / 3 ≤ (k : ℝ) := by
    have htdiv : t / tau β I.Λ m ≤ (k : ℝ) + 2 / 3 := by
      apply (div_le_iff₀ hτ).2
      nlinarith [hhi]
    linarith
  have hkupper : (k : ℝ) ≤ t / tau β I.Λ m + 2 / 3 := by
    have htdiv : (k : ℝ) - 2 / 3 ≤ t / tau β I.Λ m := by
      apply (le_div_iff₀ hτ).2
      nlinarith [hlo]
    linarith
  have htabs : |t| ≤ |t₀| + 1 := by
    rw [abs_le]
    constructor
    · have h := neg_le_abs t₀
      linarith [ht.1]
    · have h := le_abs_self t₀
      linarith [ht.2]
  have hratio : |t / tau β I.Λ m| ≤ (|t₀| + 1) / tau β I.Λ m := by
    rw [abs_div, abs_of_pos hτ]
    exact div_le_div_of_nonneg_right htabs (le_of_lt hτ)
  rw [abs_le]
  constructor <;> linarith [neg_le_abs (t / tau β I.Λ m), le_abs_self (t / tau β I.Λ m),
    hklower, hkupper, hratio]

/-- Finite set of odd integer indices in a symmetric interval. -/
noncomputable def JMNRegularity.oddIndicesIcc (N : ℕ) : Finset {k : ℤ // Odd k} :=
  ((Set.finite_Icc (-(N : ℤ)) (N : ℤ)).preimage
    (fun _ _ _ _ h => Subtype.ext h)).toFinset

theorem JMNRegularity.jMNSummand_eq_finite_sum {β : ℝ} (I : Ingredients β)
    {m n : ℕ} (t₀ t : ℝ) (N : ℕ)
    (hN : (|t₀| + 1) / tau β I.Λ m + 2 < (N : ℝ))
    (ht : t ∈ Set.Icc (t₀ - 1) (t₀ + 1)) :
    (∑' k : {k : ℤ // Odd k}, JMNRegularity.jMNSummand' I m n k t) =
      ∑ k ∈ JMNRegularity.oddIndicesIcc N, JMNRegularity.jMNSummand' I m n k t := by
  classical
  apply tsum_eq_sum
  intro k hk
  have hnot : k ∉ JMNRegularity.oddIndicesIcc N := hk
  have hnotval : (k.1 : ℤ) ∉ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
    intro hmem
    apply hnot
    apply (Set.Finite.mem_toFinset _).2
    exact Set.mem_Icc.mpr (Finset.mem_Icc.mp hmem)
  have hzero : I.zetaMK m k.1 t = 0 := by
    by_contra hne
    have hb := JMNRegularity.zetaMK_index_abs_bound I t₀ t k.1 ht hne
    have hb' : |(k.1 : ℝ)| < (N : ℝ) := by linarith
    have hcast' : -(N : ℤ) < k.1 ∧ k.1 < N := by
      exact_mod_cast (abs_lt.mp hb')
    have hcast : -(N : ℤ) ≤ k.1 ∧ k.1 ≤ N := by omega
    exact hnotval (Finset.mem_Icc.mpr hcast)
  simp [JMNRegularity.jMNSummand', hzero]

theorem JMNRegularity.jMNSummand_continuous {β : ℝ} (I : Ingredients β)
    (m n : ℕ) (k : {k : ℤ // Odd k}) :
    Continuous (fun t => JMNRegularity.jMNSummand' I m n k t) := by
  have hzeta : ContDiff ℝ (⊤ : ℕ∞) (I.zetaMK m k.1) := by
    unfold Ingredients.zetaMK scaledCutoff
    exact I.zeta_smooth.comp (by fun_prop)
  have hzetaC : Continuous (I.zetaMK m k.1) := hzeta.continuous
  have hderivC : Continuous (iteratedDeriv n (I.zetaMK m k.1)) :=
    hzeta.continuous_iteratedDeriv n (by simp)
  exact ((hzetaC.mul hderivC).smul continuous_const)

/-- The locally finite odd-mode series defining `j_{m,n}` is continuous in time. -/
theorem jMN_continuous {β : ℝ} (I : Ingredients β) (m n : ℕ) (κ : ℝ) :
    Continuous (I.jMN κ m n) := by
  rw [continuous_iff_continuousAt]
  intro t₀
  have hτ : 0 < tau β I.Λ m :=
    Infra.Ingredients.tau_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  obtain ⟨N, hN⟩ := exists_nat_gt ((|t₀| + 1) / tau β I.Λ m + 2)
  let S := JMNRegularity.oddIndicesIcc N
  have hlocal : ∀ᶠ t in 𝓝 t₀,
      I.jMN κ m n t =
        (2 * Real.pi ^ 2 * a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 2 /
            (n.factorial : ℝ) *
          (epsilon β I.Λ m ^ 2 / (4 * Real.pi ^ 2 * κ)) ^ n) •
          (∑ k ∈ S, JMNRegularity.jMNSummand' I m n k t) := by
    filter_upwards [Ioo_mem_nhds (by norm_num : t₀ - 1 < t₀)
      (by norm_num : t₀ < t₀ + 1)] with t ht
    have htIcc : t ∈ Set.Icc (t₀ - 1) (t₀ + 1) :=
      ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    unfold Ingredients.jMN
    change
      (2 * Real.pi ^ 2 * a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 2 /
          (n.factorial : ℝ) *
        (epsilon β I.Λ m ^ 2 / (4 * Real.pi ^ 2 * κ)) ^ n) •
          (∑' k : {k : ℤ // Odd k}, JMNRegularity.jMNSummand' I m n k t) = _
    rw [JMNRegularity.jMNSummand_eq_finite_sum I t₀ t N hN htIcc]
  have hsum : Continuous (fun t =>
      (2 * Real.pi ^ 2 * a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 2 /
          (n.factorial : ℝ) *
        (epsilon β I.Λ m ^ 2 / (4 * Real.pi ^ 2 * κ)) ^ n) •
        (∑ k ∈ S, JMNRegularity.jMNSummand' I m n k t)) := by
    have hcoeff : Continuous (fun _ : ℝ =>
        2 * Real.pi ^ 2 * a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 2 /
          (n.factorial : ℝ) *
        (epsilon β I.Λ m ^ 2 / (4 * Real.pi ^ 2 * κ)) ^ n) := continuous_const
    exact hcoeff.smul
      (continuous_finsetSum S fun k _ => JMNRegularity.jMNSummand_continuous I m n k)
  have hevent : (fun t =>
      (2 * Real.pi ^ 2 * a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 2 /
          (n.factorial : ℝ) *
        (epsilon β I.Λ m ^ 2 / (4 * Real.pi ^ 2 * κ)) ^ n) •
        (∑ k ∈ S, JMNRegularity.jMNSummand' I m n k t)) =ᶠ[𝓝 t₀]
      fun t => I.jMN κ m n t := by
    filter_upwards [hlocal] with t ht
    exact ht.symm
  exact hsum.continuousAt.congr hevent

end AVenhance.Infra.Section3

end
