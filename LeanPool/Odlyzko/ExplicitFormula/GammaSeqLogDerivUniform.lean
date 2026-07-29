/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.ExplicitFormula.GaussDigammaUniformSeries

/-!
# Gamma Seq Log Deriv Uniform

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Complex Filter Real Set
open scoped Topology

namespace NumberField.Odlyzko

theorem norm_inv_add_natCast_le
    {s : ℂ} (hs : 0 < s.re) {n : ℕ} (hn : 1 ≤ n) :
    ‖(s + (n : ℂ))⁻¹‖ ≤ 1 / (n : ℝ) := by
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.zero_lt_of_lt hn)
  have hnorm :
      (n : ℝ) ≤ ‖s + (n : ℂ)‖ := by
    calc
      (n : ℝ) ≤ s.re + n := by linarith
      _ = (s + (n : ℂ)).re := by simp
      _ ≤ ‖s + (n : ℂ)‖ := Complex.re_le_norm _
  rw [norm_inv, one_div]
  exact inv_anti₀ hnR hnorm

theorem tendstoUniformlyOn_inv_add_natCast_succ :
    TendstoUniformlyOn
      (fun n (s : ℂ) ↦ (s + (n + 1 : ℕ))⁻¹)
      (fun _ ↦ 0)
      atTop {s : ℂ | 0 < s.re} := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hscalar :
      Tendsto (fun n : ℕ ↦ 1 / ((n + 1 : ℕ) : ℝ))
        atTop (𝓝 0) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hscalar ε hε
  filter_upwards [eventually_ge_atTop N] with n hn s hs
  simp only [dist_zero_left]
  exact
    (norm_inv_add_natCast_le hs
      (Nat.succ_le_succ (Nat.zero_le n))).trans_lt
        (by
          have hnonneg : 0 ≤ (n : ℝ) + 1 := by positivity
          have hinvnonneg : 0 ≤ ((n : ℝ) + 1)⁻¹ :=
            inv_nonneg.mpr hnonneg
          simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg,
            abs_of_nonneg hinvnonneg, one_div, Nat.cast_add,
            Nat.cast_succ, Nat.cast_one] using hN n hn)

theorem tendstoLocallyUniformlyOn_logDeriv_GammaSeq_succ :
    TendstoLocallyUniformlyOn
      (fun n s ↦ logDeriv (fun z : ℂ ↦ Complex.GammaSeq z (n + 1)) s)
      gaussDigamma
      atTop {s : ℂ | 0 < s.re} := by
  have hopen : IsOpen {s : ℂ | 0 < s.re} :=
    continuous_re.isOpen_preimage _ isOpen_Ioi
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hopen]
  intro K hKsub hK
  have hpartialBase :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hopen).mp
      tendstoLocallyUniformlyOn_gaussDigammaPartialSum K hKsub hK
  have hpartial :=
    show TendstoUniformlyOn
      (fun n s ↦ gaussDigammaPartialSum s (n + 1))
      (fun s ↦ ∫ x : ℝ in Ioi 0, gaussDigammaIntegrand s x)
      atTop K by
      rw [Metric.tendstoUniformlyOn_iff] at hpartialBase ⊢
      intro ε hε
      exact (Filter.tendsto_add_atTop_nat 1).eventually
        (hpartialBase ε hε)
  have heulerReal :=
    Real.tendsto_eulerMascheroniSeq'.comp
      (Filter.tendsto_add_atTop_nat 1)
  have heuler :
      Tendsto
        (fun n : ℕ ↦
          (Real.eulerMascheroniSeq' (n + 1) : ℂ))
        atTop
        (𝓝 (Real.eulerMascheroniConstant : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp heulerReal
  have heulerUniform :=
    heuler.tendstoUniformlyOn_const K
  have htail :=
    tendstoUniformlyOn_inv_add_natCast_succ.mono hKsub
  have hcombined :=
    (hpartial.sub heulerUniform).sub htail
  have hlimit :
      (fun s : ℂ ↦
          (∫ x : ℝ in Ioi 0, gaussDigammaIntegrand s x) -
            (Real.eulerMascheroniConstant : ℂ) - 0) =
        gaussDigamma := by
    funext s
    unfold gaussDigamma
    ring
  rw [← hlimit]
  apply hcombined.congr
  filter_upwards [] with n s hs
  exact (logDeriv_GammaSeq_succ_eq (hKsub hs) n).symm

end NumberField.Odlyzko
