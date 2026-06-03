/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import LeanPool.LeanModularForms.Modularforms.IccIcoLems

/-! # LimunderLems -/


@[expose] public section

open TopologicalSpace Set
  Metric Filter Function Complex

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat


lemma limUnder_add {α : Type*} [Preorder α] [(atTop : Filter α).NeBot] (f g : α → ℂ)
    (hf : CauchySeq f) (hg : CauchySeq g) :
    (limUnder atTop f) + (limUnder atTop g) = limUnder atTop (f + g) := by
  nth_rw 3 [Filter.Tendsto.limUnder_eq]
  rw [@Pi.add_def]
  apply Filter.Tendsto.add
  · refine CauchySeq.tendsto_limUnder hf
  refine CauchySeq.tendsto_limUnder hg


lemma limUnder_mul_const {α : Type*} [Preorder α] [(atTop : Filter α).NeBot] (f : α → ℂ)
    (hf : CauchySeq f) (c : ℂ) :
    c * (limUnder atTop f)= limUnder atTop (c • f) := by
  nth_rw 2 [Filter.Tendsto.limUnder_eq]
  apply Filter.Tendsto.const_mul
  refine CauchySeq.tendsto_limUnder hf


lemma limUnder_sub {α : Type*} [Preorder α] [(atTop : Filter α).NeBot] (f g : α → ℂ)
    (hf : CauchySeq f) (hg : CauchySeq g) :
    (limUnder atTop f) - (limUnder atTop g) = limUnder atTop (f - g) := by
  nth_rw 3 [Filter.Tendsto.limUnder_eq]
  rw [@Pi.sub_def]
  apply Filter.Tendsto.sub
  · refine CauchySeq.tendsto_limUnder hf
  refine CauchySeq.tendsto_limUnder hg


lemma limUnder_congr_eventually (f g : ℕ → ℂ) (h : ∀ᶠ n in atTop, f n = g n)
  (hf : CauchySeq f) (hg : CauchySeq g) :
  limUnder atTop f = limUnder atTop g := by
  have h0 := CauchySeq.tendsto_limUnder hf
  have h1 := CauchySeq.tendsto_limUnder hg
  rw [Filter.Tendsto.limUnder_eq (x := (limUnder atTop f)) ]
  · rw [Filter.Tendsto.limUnder_eq ]
    apply Filter.Tendsto.congr' _ h1
    symm
    apply h
  exact h0


lemma tsum_limUnder_atTop (f : ℤ → ℂ) (hf : Summable f) : ∑' n, f n =
    limUnder atTop (fun N : ℕ => ∑ n ∈ Finset.Ico (-N : ℤ) N, f n) := by
  rw [Filter.Tendsto.limUnder_eq]
  have := hf.hasSum
  have V := this.comp verga
  apply V
