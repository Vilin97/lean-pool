/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.Matrix
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.FrozenFlowRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.CorrTimeRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.LocalFinite
public import Mathlib.Topology.Instances.Matrix

/-! # Joint continuity of the leading matrix `F`

Source: `enhance.tex` 8298–8302.  Near each time only finitely many modes `ξ_{m,k}` are active
(their supports have length `(5/2)τ_m`), so `F` is locally a finite sum of jointly continuous
matrix fields `ξ_{m,k}(t) (I + ∇Χ_{m,k}(t,·)) ∘ X⁻¹_{m-1,l_k}(t,x)`. -/

@[expose] public section

noncomputable section

open Homogenization Filter Topology

namespace AVenhance.Infra.Section5.LeftToShow

open AVenhance AVenhance.Infra.Section3

variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

theorem epsilon_ne_zero (m : ℕ) : epsilon β I.Λ m ≠ 0 :=
  (Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt (by exact_mod_cast I.two_pow_seven_le)).ne'

/-- A single mode's corrector gradient is jointly continuous in time and position. -/
theorem continuous_gradMatrix_chiMK (κ : ℝ) (m : ℕ) {k : ℤ} (hk : Odd k) :
    Continuous (fun q : ℝ × Vec 2 => gradMatrix (I.chiMK κ m k q.1) q.2) := by
  have hε := epsilon_ne_zero I m
  have hcorr : Continuous (fun q : ℝ × Vec 2 => I.corrTime κ m k q.1) :=
    (corrTime_continuous I κ k).comp continuous_fst
  have hk4 : k % 4 = 1 ∨ k % 4 = 3 := by
    rcases hk with ⟨n, hn⟩
    omega
  refine continuous_matrix fun i j => ?_
  have hentry : (fun q : ℝ × Vec 2 => gradMatrix (I.chiMK κ m k q.1) q.2 i j) =
      fun q => spaceGrad (fun y => I.chiMK κ m k q.1 y j) q.2 i := by
    funext q
    simp [gradMatrix]
  rw [hentry]
  have hzero : ∀ (q : ℝ × Vec 2) (c : Fin 2),
      (∀ y : Vec 2, I.chiMK κ m k q.1 y c = 0) →
        spaceGrad (fun y => I.chiMK κ m k q.1 y c) q.2 i = 0 := by
    intro q c h
    have : (fun y : Vec 2 => I.chiMK κ m k q.1 y c) = fun _ => 0 := funext h
    rw [this]
    simp [spaceGrad]
  obtain rfl | rfl : j = 0 ∨ j = 1 := by fin_cases j <;> simp
  · rcases hk4 with h1 | h3
    · refine continuous_const.congr fun q => (hzero q 0 fun y => ?_).symm
      simp [Ingredients.chiMK, uShear, h1]
    · refine Continuous.congr (f := fun q : ℝ × Vec 2 =>
        if i = 1 then -(4 * Real.pi ^ 2 * a β I.Λ m * I.corrTime κ m k q.1) *
          Real.sin (2 * Real.pi * q.2 1 / epsilon β I.Λ m) else 0) ?_ fun q => ?_
      · by_cases hi : i = 1
        · simp only [hi, ite_true]
          fun_prop
        · simp only [hi, ite_false]
          fun_prop
      · rw [chiMK_spaceGrad_three_all I κ k _ _ i h3 hε]
  · rcases hk4 with h1 | h3
    · refine Continuous.congr (f := fun q : ℝ × Vec 2 =>
        if i = 0 then 4 * Real.pi ^ 2 * a β I.Λ m * I.corrTime κ m k q.1 *
          Real.sin (2 * Real.pi * q.2 0 / epsilon β I.Λ m) else 0) ?_ fun q => ?_
      · by_cases hi : i = 0
        · simp only [hi, ite_true]
          fun_prop
        · simp only [hi, ite_false]
          fun_prop
      · rw [chiMK_spaceGrad_one_all I κ k _ _ i h1 hε]
    · refine continuous_const.congr fun q => (hzero q 1 fun y => ?_).symm
      simp [Ingredients.chiMK, uShear, h3]

/-- Nonvanishing of `ξ_{m,k}(t)` forces `t` to lie within `(5/4) τ_m` of `k τ_m`. -/
theorem xiMK_ne_zero_abs_le (m : ℕ) {k : ℤ} {t : ℝ} (hne : I.xiMK m k t ≠ 0) :
    |t - (k : ℝ) * tau β I.Λ m| ≤ 5 / 4 * tau β I.Λ m := by
  have hτ := I.tau_pos' m
  set u := (t - k * tau β I.Λ m) / tau β I.Λ m with hu
  have hmem : u ∈ Set.Icc (-(5 / 4) : ℝ) (5 / 4) := by
    by_contra hnot
    apply hne
    have h1 := I.xi_le_ind u
    have h2 := I.ind_le_xi u
    rw [indIcc_eq_zero_of_not_mem hnot] at h1
    have h3 := indIcc_nonneg' (-(3 / 4)) (3 / 4) u
    exact le_antisymm h1 (h3.trans h2)
  have : |u| ≤ 5 / 4 := abs_le.mpr ⟨hmem.1, hmem.2⟩
  rw [hu, abs_div, abs_of_pos hτ, div_le_iff₀ hτ] at this
  linarith

theorem continuous_xiMK (m : ℕ) (k : ℤ) : Continuous (I.xiMK m k) := by
  unfold Ingredients.xiMK scaledCutoff
  exact I.xi_smooth.continuous.comp ((continuous_id.sub continuous_const).div_const _)

/-- The `k`-th summand of `F`, as a function of the spacetime point. -/
def leadingSummand (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ) (k : ℤ) (q : ℝ × Vec 2) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  I.xiMK m k q.1 •
    (1 + gradMatrix (I.chiMK κm m k q.1) (I.xFlowInv hΦ m (lIdx β I.Λ m k) q.1 q.2))

theorem continuous_leadingSummand (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ) {k : ℤ}
    (hk : Odd k) : Continuous (leadingSummand I hΦ m κm k) := by
  unfold leadingSummand
  have hflow : Continuous (fun q : ℝ × Vec 2 => I.xFlowInv hΦ m (lIdx β I.Λ m k) q.1 q.2) :=
    (Infra.Section5.xFlowInv_joint_contDiff_one I hΦ m (lIdx β I.Λ m k)).continuous
  have hgrad : Continuous (fun q : ℝ × Vec 2 =>
      gradMatrix (I.chiMK κm m k q.1) (I.xFlowInv hΦ m (lIdx β I.Λ m k) q.1 q.2)) :=
    (continuous_gradMatrix_chiMK I κm m hk).comp (continuous_fst.prodMk hflow)
  exact ((continuous_xiMK I m k).comp continuous_fst).smul (continuous_const.add hgrad)

/-- Joint continuity of `F` (finitely many active modes near each time). -/
theorem leadingMatrix_continuous (hΦ : IsStreamSeq I Φ) {m : ℕ} (_hm : 1 ≤ m) {κm : ℝ}
    (_hκm : 0 < κm) :
    Continuous (fun p : ℝ × Vec 2 => leadingMatrix I hΦ m κm p.1 p.2) := by
  classical
  rw [continuous_iff_continuousAt]
  rintro ⟨t₀, x₀⟩
  have hτ := I.tau_pos' m
  -- the finitely many modes active near `t₀`
  have hfin : {k : {k : ℤ // Odd k} |
      |t₀ - (k.1 : ℝ) * tau β I.Λ m| ≤ 5 / 4 * tau β I.Λ m + 1}.Finite :=
    (finite_lattice_near hτ t₀ (5 / 4 * tau β I.Λ m + 1)).preimage
      (fun a _ b _ h => Subtype.ext h)
  set S := hfin.toFinset with hS
  have hnear : ∀ᶠ q : ℝ × Vec 2 in 𝓝 (t₀, x₀), q.1 ∈ Set.Ioo (t₀ - 1) (t₀ + 1) :=
    (continuous_fst.continuousAt (x := (t₀, x₀))).eventually_mem
      (Ioo_mem_nhds (by linarith) (by linarith))
  have hsum : ContinuousAt (fun q : ℝ × Vec 2 => ∑ k ∈ S, leadingSummand I hΦ m κm k.1 q)
      (t₀, x₀) :=
    (continuous_finsetSum _ fun k _ => continuous_leadingSummand I hΦ m κm k.2).continuousAt
  refine hsum.congr ?_
  filter_upwards [hnear] with q hq
  have hzero : ∀ k ∉ S, leadingSummand I hΦ m κm k.1 q = 0 := by
    intro k hk
    have hξ : I.xiMK m k.1 q.1 = 0 := by
      by_contra hne
      apply hk
      rw [hS, Set.Finite.mem_toFinset]
      have h1 := xiMK_ne_zero_abs_le I m hne
      have h2 : |t₀ - q.1| ≤ 1 := by
        rw [abs_le]
        constructor <;> linarith [hq.1, hq.2]
      have h3 : |t₀ - (k.1 : ℝ) * tau β I.Λ m| ≤
          |t₀ - q.1| + |q.1 - (k.1 : ℝ) * tau β I.Λ m| := by
        have := abs_add_le (t₀ - q.1) (q.1 - (k.1 : ℝ) * tau β I.Λ m)
        simpa using this
      change |t₀ - (k.1 : ℝ) * tau β I.Λ m| ≤ 5 / 4 * tau β I.Λ m + 1
      linarith
    simp [leadingSummand, hξ]
  unfold leadingMatrix
  exact (tsum_eq_sum (L := SummationFilter.unconditional {k : ℤ // Odd k}) (s := S) hzero).symm

end AVenhance.Infra.Section5.LeftToShow

end
