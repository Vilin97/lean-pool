/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.Normed.SymmetricGauge

/-! # The supremum symmetric gauge

The scalar-free infinity endpoint of the Schatten scale, on the canonical
`SymmetricGauge` structure. The extension is the coordinate supremum even when it is infinite.
The finite-gauge proofs originate in `Analysis.OperatorIdeal.SymmetricGauge`.
-/

public section

open scoped NNReal ENNReal

namespace TauCeti

/-- The sup norm of a finitely supported nonnegative sequence. -/
noncomputable def supGaugeFinsupp (a : ℕ →₀ ℝ≥0) : ℝ≥0 := a.support.sup a

/-- Every term is bounded by the sup. -/
theorem le_supGaugeFinsupp (a : ℕ →₀ ℝ≥0) (n : ℕ) : a n ≤ supGaugeFinsupp a := by
  by_cases hn : n ∈ a.support
  · exact Finset.le_sup hn
  · simp only [Finsupp.notMem_support_iff] at hn
    simp [hn]

/-- The sup is the least such bound. -/
theorem supGaugeFinsupp_le {a : ℕ →₀ ℝ≥0} {c : ℝ≥0} (h : ∀ n, a n ≤ c) :
    supGaugeFinsupp a ≤ c :=
  Finset.sup_le fun n _ => h n

/-- `Φ_∞`, the symmetric gauge at the top of the Schatten scale. -/
noncomputable def supGauge : SymmetricGauge where
  toFun := supGaugeFinsupp
  add_le a b := supGaugeFinsupp_le fun n => by
    simpa using add_le_add (le_supGaugeFinsupp a n) (le_supGaugeFinsupp b n)
  smul c a := by
    classical
    rcases eq_or_ne c 0 with rfl | hc
    · simp [supGaugeFinsupp]
    · have hsupp : (c • a).support = a.support := by
        ext n
        simp [Finsupp.mem_support_iff, hc]
      simp only [supGaugeFinsupp, hsupp, NNReal.mul_finset_sup]
      exact Finset.sup_congr rfl fun n _ => by simp
  symm σ a := by
    refine le_antisymm (supGaugeFinsupp_le fun n => ?_) (supGaugeFinsupp_le fun n => ?_)
    · simpa [Finsupp.equivMapDomain_apply] using le_supGaugeFinsupp a (σ.symm n)
    · simpa [Finsupp.equivMapDomain_apply] using
        le_supGaugeFinsupp (Finsupp.equivMapDomain σ a) (σ n)
  mono {a b} h := supGaugeFinsupp_le fun n =>
    le_trans (h n) (le_supGaugeFinsupp b n)
  normalized := by
    refine le_antisymm (supGaugeFinsupp_le fun n => ?_) ?_
    · by_cases hn : n = 0 <;> simp [hn]
    · simpa using le_supGaugeFinsupp (Finsupp.single (0 : ℕ) (1 : ℝ≥0)) 0

/-- The extension of the sup gauge is the supremum, including infinite coordinates. -/
theorem supGauge_extend (a : ℕ → ENNReal) :
    supGauge.extend a = ⨆ n, a n := by
  refine le_antisymm (supGauge.extend_le fun b hb => ?_) (supGauge.iSup_le_extend a)
  by_cases ht : (⨆ n, a n) = ⊤
  · simp [ht]
  · have hbound : supGaugeFinsupp b ≤ (⨆ n, a n).toNNReal := by
      apply supGaugeFinsupp_le
      intro n
      apply ENNReal.coe_le_coe.mp
      rw [ENNReal.coe_toNNReal ht]
      exact (hb n).trans (le_iSup a n)
    calc (supGauge b : ENNReal)
        ≤ ((⨆ n, a n).toNNReal : ENNReal) := by exact_mod_cast hbound
      _ = ⨆ n, a n := ENNReal.coe_toNNReal ht

/-- On an antitone sequence the sup gauge is its leading coordinate. -/
theorem supGauge_extend_of_antitone {a : ℕ → ENNReal} (ha : Antitone a) :
    supGauge.extend a = a 0 := by
  rw [supGauge_extend]
  exact le_antisymm (iSup_le fun n => ha (Nat.zero_le n)) (le_iSup a 0)

end TauCeti
