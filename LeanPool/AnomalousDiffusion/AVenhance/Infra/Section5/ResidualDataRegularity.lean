/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.QMNRRecursion
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.LocalFinite
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.HmAdapter
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.ResidualCompletion
public import Mathlib.Analysis.Matrix.Normed

/-! Regularity adapters used to construct the pointwise residual calculus data. -/

@[expose] public section

noncomputable section

open Filter Homogenization
open scoped ContDiff
open scoped Topology
open scoped Matrix.Norms.Elementwise

namespace AVenhance.Infra.Section5

open AVenhance

/-- One shear-mode matrix term in the residual cutoff moment. -/
def ResidualDataRegularity.residualJMNMode {β : ℝ} (I : Ingredients β) (m n : ℕ)
    (k : {k : ℤ // Odd k}) (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (I.zetaMK m k.1 t * iteratedDeriv n (I.zetaMK m k.1) t) •
    ((if k.1 % 4 = 1 then !![0, 0; 0, 1] else 0) +
      (if k.1 % 4 = 3 then !![1, 0; 0, 0] else 0) : Matrix (Fin 2) (Fin 2) ℝ)

/-- Finite set of odd indices in a symmetric interval for the residual moment sum. -/
noncomputable def ResidualDataRegularity.residualOddIndicesIcc (N : ℕ) : Finset {k : ℤ // Odd k} :=
  ((Set.finite_Icc (-(N : ℤ)) (N : ℤ)).preimage
    (fun _ _ _ _ h => Subtype.ext h)).toFinset

theorem ResidualDataRegularity.residual_zeta_index_abs_bound {β : ℝ} (I : Ingredients β)
    {m : ℕ} (t₀ t : ℝ) (k : ℤ)
    (ht : t ∈ Set.Icc (t₀ - 1) (t₀ + 1))
    (hne : I.zetaMK m k t ≠ 0) :
    |(k : ℝ)| ≤ (|t₀| + 1) / tau β I.Λ m + 2 / 3 := by
  have hτ : 0 < tau β I.Λ m := I.tau_pos' m
  let u := (t - (k : ℝ) * tau β I.Λ m) / tau β I.Λ m
  have hu : u ∈ Set.Icc (-(2 / 3 : ℝ)) (2 / 3) := by
    by_contra hnot
    apply hne
    have hle := I.zeta_le_ind u
    rw [indIcc_eq_zero_of_not_mem hnot] at hle
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

theorem ResidualDataRegularity.residualJMNMode_eq_sum {β : ℝ} (I : Ingredients β)
    {m n : ℕ} (t₀ t : ℝ) (N : ℕ)
    (hN : (|t₀| + 1) / tau β I.Λ m + 2 < (N : ℝ))
    (ht : t ∈ Set.Icc (t₀ - 1) (t₀ + 1)) :
    (∑' k : {k : ℤ // Odd k}, ResidualDataRegularity.residualJMNMode I m n k t) =
      ∑ k ∈ ResidualDataRegularity.residualOddIndicesIcc N, ResidualDataRegularity.residualJMNMode
          I m n k t := by
  classical
  apply tsum_eq_sum
  intro k hk
  have hnot : k ∉ ResidualDataRegularity.residualOddIndicesIcc N := hk
  have hnotval : (k.1 : ℤ) ∉ Finset.Icc (-(N : ℤ)) N := by
    intro hmem
    apply hnot
    apply (Set.Finite.mem_toFinset _).2
    exact Set.mem_Icc.mpr (Finset.mem_Icc.mp hmem)
  have hzero : I.zetaMK m k.1 t = 0 := by
    by_contra hne
    have hb := ResidualDataRegularity.residual_zeta_index_abs_bound I t₀ t k.1 ht hne
    have hb' : |(k.1 : ℝ)| < (N : ℝ) := by linarith
    have hcast' : -(N : ℤ) < k.1 ∧ k.1 < N := by exact_mod_cast (abs_lt.mp hb')
    have hcast : -(N : ℤ) ≤ k.1 ∧ k.1 ≤ N := by omega
    exact hnotval (Finset.mem_Icc.mpr hcast)
  simp [ResidualDataRegularity.residualJMNMode, hzero]

/-- The explicit `j_{m,n}` coefficient is smooth: near each time its odd-mode
series reduces to a finite sum of smooth cutoff derivatives. -/
theorem residual_jMN_contDiff {β : ℝ} (I : Ingredients β)
    (m n : ℕ) (κ : ℝ) : ContDiff ℝ ∞ (I.jMN κ m n) := by
  rw [contDiff_iff_contDiffAt]
  intro t₀
  have hτ := I.tau_pos' m
  obtain ⟨N, hN⟩ := exists_nat_gt ((|t₀| + 1) / tau β I.Λ m + 2)
  let S := ResidualDataRegularity.residualOddIndicesIcc N
  let c := 2 * Real.pi ^ 2 * a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 2 /
    (n.factorial : ℝ) * (epsilon β I.Λ m ^ 2 / (4 * Real.pi ^ 2 * κ)) ^ n
  have hlocal : ∀ᶠ t in 𝓝 t₀,
      I.jMN κ m n t = c • ∑ k ∈ S, ResidualDataRegularity.residualJMNMode I m n k t := by
    filter_upwards [Ioo_mem_nhds (by norm_num : t₀ - 1 < t₀)
      (by norm_num : t₀ < t₀ + 1)] with t ht
    have htIcc : t ∈ Set.Icc (t₀ - 1) (t₀ + 1) :=
      ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    have hsum := ResidualDataRegularity.residualJMNMode_eq_sum I (m := m) (n := n)
      t₀ t N hN htIcc
    have hmul := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => c • M) hsum
    simpa [Ingredients.jMN, ResidualDataRegularity.residualJMNMode, c, S] using hmul
  have hmode (k : {k : ℤ // Odd k}) :
      ContDiff ℝ ∞ (ResidualDataRegularity.residualJMNMode I m n k) := by
    have hz : ContDiff ℝ ∞ (I.zetaMK m k.1) := by
      unfold Ingredients.zetaMK scaledCutoff
      exact I.zeta_smooth.comp (by fun_prop)
    have hd : ContDiff ℝ ∞ (iteratedDeriv n (I.zetaMK m k.1)) := by
      rw [iteratedDeriv_eq_iterate]
      exact hz.iterate_deriv n
    change ContDiff ℝ ∞ (fun t =>
      (I.zetaMK m k.1 t * iteratedDeriv n (I.zetaMK m k.1) t) • _)
    exact (hz.mul hd).smul contDiff_const
  have hsum : ContDiff ℝ ∞ (fun t => c • ∑ k ∈ S, ResidualDataRegularity.residualJMNMode I m n k
      t) := by
    exact (ContDiff.sum fun k hk => hmode k).const_smul c
  have hevent : (fun t => c • ∑ k ∈ S, ResidualDataRegularity.residualJMNMode I m n k t) =ᶠ[𝓝 t₀]
      fun t => I.jMN κ m n t := by
    filter_upwards [hlocal] with t ht
    exact ht.symm
  exact hsum.contDiffAt.congr_of_eventuallyEq hevent.symm

theorem ResidualDataRegularity.residual_qMNR_entry_contDiff {β : ℝ} (I : Ingredients β)
    (κ : ℝ) (m n r : ℕ) (i j : Fin 2) :
    ContDiff ℝ ∞ (fun t => I.qMNR κ m n r t i j) := by
  induction r with
  | zero =>
      have hj : ContDiff ℝ ∞ (fun t => I.jMN κ m n t i j) :=
        (contDiff_pi.mp (contDiff_pi.mp (residual_jMN_contDiff I m n κ) i) j)
      simpa [Ingredients.qMNR] using hj.sub contDiff_const
  | succ r ih =>
      apply contDiff_infty_iff_deriv.mpr
      constructor
      · intro t
        exact (Infra.Section3.qMNR_hasDerivAt I κ m n r t i j).differentiableAt
      · have hderiv : deriv (fun t => I.qMNR κ m n (r + 1) t i j) =
            fun t => -I.qMNR κ m n r t i j := by
          funext t
          exact (Infra.Section3.qMNR_hasDerivAt I κ m n r t i j).deriv
        rw [hderiv]
        exact ih.neg

/-- Every recursive `q_{m,n,r}` coefficient is smooth in time. -/
theorem residual_qMNR_contDiff {β : ℝ} (I : Ingredients β)
    (κ : ℝ) (m n r : ℕ) : ContDiff ℝ ∞ (I.qMNR κ m n r) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  exact ResidualDataRegularity.residual_qMNR_entry_contDiff I κ m n r i j

end AVenhance.Infra.Section5

end
