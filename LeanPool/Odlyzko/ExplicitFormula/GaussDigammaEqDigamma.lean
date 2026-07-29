/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.ExplicitFormula.GammaSeqIntegralConvergence
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma

/-!
# Gauss Digamma Eq Digamma

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Complex Filter Set
open scoped Topology

namespace NumberField.Odlyzko

theorem tendstoLocallyUniformlyOn_GammaSeq_succ :
    TendstoLocallyUniformlyOn
      (fun n s ↦ Complex.GammaSeq s (n + 1))
      Complex.Gamma
      atTop {s : ℂ | 0 < s.re} := by
  intro u hu s hs
  obtain ⟨t, ht, hEventually⟩ :=
    tendstoLocallyUniformlyOn_GammaSeq u hu s hs
  exact
    ⟨t, ht,
      (Filter.tendsto_add_atTop_nat 1).eventually hEventually⟩

theorem differentiableOn_GammaSeq_succ (n : ℕ) :
    DifferentiableOn ℂ
      (fun s : ℂ ↦ Complex.GammaSeq s (n + 1))
      {s : ℂ | 0 < s.re} := by
  intro s hs
  change 0 < s.re at hs
  unfold Complex.GammaSeq
  apply DifferentiableAt.differentiableWithinAt
  have hnC : (((n + 1 : ℕ) : ℂ)) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  have hnum :
      DifferentiableAt ℂ
        (fun z : ℂ ↦
          ((n + 1 : ℕ) : ℂ) ^ z *
            ((n + 1).factorial : ℂ)) s :=
    ((hasDerivAt_id s).const_cpow
      (c := ((n + 1 : ℕ) : ℂ)) (Or.inl hnC))
      |>.differentiableAt.mul (differentiableAt_const _)
  have hden :
      DifferentiableAt ℂ
        (fun z : ℂ ↦
          ∏ j ∈ Finset.range (n + 1 + 1), (z + j)) s := by
    fun_prop
  apply hnum.div hden
  exact Finset.prod_ne_zero_iff.mpr fun j hj hzero ↦ by
    have hre := congrArg Complex.re hzero
    simp only [add_re, natCast_re, zero_re] at hre
    grind

theorem gaussDigamma_eq_digamma
    {s : ℂ} (hs : 0 < s.re) :
    gaussDigamma s = Complex.digamma s := by
  have hGauss :=
    tendstoLocallyUniformlyOn_logDeriv_GammaSeq_succ.tendsto_at hs
  have hMathlib :=
    Complex.logDeriv_tendsto
      (continuous_re.isOpen_preimage _ isOpen_Ioi)
      hs
      tendstoLocallyUniformlyOn_GammaSeq_succ
      (Eventually.of_forall differentiableOn_GammaSeq_succ)
      (Complex.Gamma_ne_zero_of_re_pos hs)
  exact tendsto_nhds_unique hGauss hMathlib

end NumberField.Odlyzko
