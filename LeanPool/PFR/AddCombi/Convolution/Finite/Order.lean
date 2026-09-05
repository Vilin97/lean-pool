/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/

module
public import LeanPool.PFR.AddCombi.Convolution.Finite.Defs

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Conjneg
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Data.Rat.Star

/-!
# Ordered finite convolution estimates
-/

open Finset Function Real
open scoped ComplexConjugate NNReal Pointwise

variable {G K : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
variable [Semifield K] [CharZero K] [LinearOrder K] [IsStrictOrderedRing K] {f g : G → K}

public
lemma conv_nonneg (hf : 0 ≤ f) (hg : 0 ≤ g) : 0 ≤ f ∗ g :=
  fun _a ↦ expect_nonneg fun _x _ ↦ mul_nonneg (hf _) (hg _)





public
lemma conv_pos (hf : 0 < f) (hg : 0 < g) : 0 < f ∗ g := by
  rw [Pi.lt_def] at hf hg ⊢
  obtain ⟨hf, a, ha⟩ := hf
  obtain ⟨hg, b, hb⟩ := hg
  refine ⟨conv_nonneg hf hg, a + b, ?_⟩
  rw [conv_apply_add]
  exact expect_pos' (fun c _ ↦ mul_nonneg (hf _) <| hg _) ⟨0, by simpa using mul_pos ha hb⟩

variable [StarRing K] [StarOrderedRing K]

omit [IsStrictOrderedRing K] in
public
lemma dconv_nonneg (hf : 0 ≤ f) (hg : 0 ≤ g) : 0 ≤ f ○ g :=
  fun _a ↦ expect_nonneg fun _x _ ↦ mul_nonneg (hf _) <| star_nonneg_iff.2 <| hg _

omit [IsStrictOrderedRing K] in
public
lemma dconv_apply_nonneg (hf : 0 ≤ f) (hg : 0 ≤ g) (a : G) : 0 ≤ (f ○ g) a := dconv_nonneg hf hg _



public
lemma dconv_pos (hf : 0 < f) (hg : 0 < g) : 0 < f ○ g := by
  rw [← conv_conjneg]; exact conv_pos hf (conjneg_pos.2 hg)
