/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.ExplicitFormula.GammaSeqLogDerivLimit
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.PSeries

/-!
# Gauss Digamma Uniform Series

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Complex Filter Real Set
open scoped Topology

namespace NumberField.Odlyzko

/-- A gauss digamma series term used in the Odlyzko-bound argument. -/
noncomputable def gaussDigammaSeriesTerm (k : ℕ) (s : ℂ) : ℂ :=
  (((k + 1 : ℕ) : ℂ)⁻¹ - (s + k)⁻¹)

private theorem gaussDigammaPartialSum_eq_sum_seriesTerm (s : ℂ) (n : ℕ) :
    gaussDigammaPartialSum s n =
      ∑ k ∈ Finset.range n, gaussDigammaSeriesTerm k s :=
  rfl

theorem gaussDigammaSeriesTerm_eq_div
    {s : ℂ} (hs : 0 < s.re) (k : ℕ) :
    gaussDigammaSeriesTerm k s =
      (s - 1) / (((k + 1 : ℕ) : ℂ) * (s + k)) := by
  have hk1 : ((k + 1 : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero k
  have hsk : s + k ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [add_re, natCast_re, zero_re] at hre
    grind
  unfold gaussDigammaSeriesTerm
  grind

theorem norm_gaussDigammaSeriesTerm_le
    {M : ℝ} {s : ℂ} (hs : 0 < s.re) (hsM : ‖s - 1‖ ≤ M)
    {k : ℕ} (hk : 1 ≤ k) :
    ‖gaussDigammaSeriesTerm k s‖ ≤ M / (k : ℝ) ^ 2 := by
  have hkR : 0 < (k : ℝ) := Nat.cast_pos.mpr (Nat.zero_lt_of_lt hk)
  have hM : 0 ≤ M := (norm_nonneg _).trans hsM
  have hsk :
      (k : ℝ) ≤ ‖s + k‖ := by
    calc
      (k : ℝ) ≤ s.re + k := by linarith
      _ = (s + k).re := by simp
      _ ≤ ‖s + k‖ := Complex.re_le_norm _
  have hk1norm :
      ‖(((k + 1 : ℕ) : ℂ))‖ = (k + 1 : ℕ) := by
    change ‖(((k + 1 : ℕ) : ℝ) : ℂ)‖ = ((k + 1 : ℕ) : ℝ)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    grind
  rw [gaussDigammaSeriesTerm_eq_div hs, norm_div, norm_mul,
    hk1norm]
  have hden :
      (k : ℝ) ^ 2 ≤
        (k + 1 : ℕ) * ‖s + k‖ := by
    rw [pow_two]
    calc
      (k : ℝ) * k ≤ (k + 1 : ℕ) * k := by simp_all
      _ ≤ (k + 1 : ℕ) * ‖s + k‖ := by
        gcongr
  exact div_le_div₀ hM hsM (sq_pos_of_pos hkR) hden

theorem tendstoUniformlyOn_gaussDigammaPartialSum
    (M : ℝ) :
    TendstoUniformlyOn
      (fun n s ↦ gaussDigammaPartialSum s n)
      (fun s ↦ ∑' k, gaussDigammaSeriesTerm k s)
      atTop {s : ℂ | 0 < s.re ∧ ‖s - 1‖ ≤ M} := by
  have hu :
      Summable (fun k : ℕ ↦ M / (k : ℝ) ^ 2) := by
    have h :=
      (Real.summable_one_div_nat_pow.mpr
        (show 1 < (2 : ℕ) by norm_num)).mul_left M
    grind
  rw [show (fun n s ↦ gaussDigammaPartialSum s n) =
      (fun n s ↦ ∑ k ∈ Finset.range n,
        gaussDigammaSeriesTerm k s) by
    funext n s
    exact gaussDigammaPartialSum_eq_sum_seriesTerm s n]
  apply tendstoUniformlyOn_tsum_nat_eventually hu
  filter_upwards [eventually_ge_atTop 1] with k hk s hs
  exact norm_gaussDigammaSeriesTerm_le hs.1 hs.2 hk

theorem tsum_gaussDigammaSeriesTerm_eq_integral
    {s : ℂ} (hs : 0 < s.re) :
    (∑' k, gaussDigammaSeriesTerm k s) =
      ∫ x : ℝ in Ioi 0, gaussDigammaIntegrand s x := by
  exact tendsto_nhds_unique
    ((tendstoUniformlyOn_gaussDigammaPartialSum ‖s - 1‖).tendsto_at
      ⟨hs, le_rfl⟩)
    (tendsto_gaussDigammaPartialSum hs)

theorem tendstoLocallyUniformlyOn_gaussDigammaPartialSum :
    TendstoLocallyUniformlyOn
      (fun n s ↦ gaussDigammaPartialSum s n)
      (fun s ↦ ∫ x : ℝ in Ioi 0, gaussDigammaIntegrand s x)
      atTop {s : ℂ | 0 < s.re} := by
  have hopen : IsOpen {s : ℂ | 0 < s.re} :=
    continuous_re.isOpen_preimage _ isOpen_Ioi
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hopen]
  intro K hKsub hK
  obtain ⟨C, hC⟩ :=
    isBounded_iff_forall_norm_le.mp hK.isBounded
  have hsubset :
      K ⊆ {s : ℂ | 0 < s.re ∧ ‖s - 1‖ ≤ C + 1} := by
    intro s hsK
    refine ⟨hKsub hsK, ?_⟩
    exact (norm_sub_le s 1).trans
      (by simpa using add_le_add_right (hC s hsK) 1)
  have huniform :=
    (tendstoUniformlyOn_gaussDigammaPartialSum (C + 1)).mono hsubset
  apply huniform.congr_right
  intro s hsK
  exact tsum_gaussDigammaSeriesTerm_eq_integral (hKsub hsK)

end NumberField.Odlyzko
