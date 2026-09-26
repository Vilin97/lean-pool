/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.BKARForestFormula.BKAR.OrderedBranch

/-! # One-edge growths and their branch integrals

A base case of the ordered recursion: the one-edge ordered growth
`singletonGrowth` determined by a chosen active extension, and the
identification of its branch integral with a single interval integral of
the partial derivative along the interpolation family, when the extended
forest has no active edges left.
-/

@[expose] public section

noncomputable section

namespace BKAR

namespace Forest

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace ActiveExtension

variable {F : Forest V} {e : Edge V}

/--
The one-edge ordered growth determined by a chosen active extension.
-/
def singletonGrowth (h : ActiveExtension F e) :
    OrderedGrowth F [e] h.forest :=
  OrderedGrowth.cons h.extension (OrderedGrowth.nil h.forest)

theorem singletonGrowth_firstStep (h : ActiveExtension F e) :
    h.singletonGrowth.firstStep = h.extension :=
  rfl

theorem singletonGrowth_tailGrowth (h : ActiveExtension F e) :
    h.singletonGrowth.tailGrowth = OrderedGrowth.nil h.forest :=
  rfl

theorem singleton_branchIntegralAux_eq_integral_partialDeriv_of_emptyActiveEdges
    (h : ActiveExtension F e) (top : ℝ) (u : F.EdgeParam → ℝ)
    (ρ : (Edge V → ℝ) → ℝ) (hterm : h.forest.activeEdges = ∅) :
    h.singletonGrowth.branchIntegralAux top u ρ =
      ∫ t in 0..top, partialDeriv e ρ
        (h.forest.interpWithFill (h.extension.extendParam u t) t) := by
  rw [singletonGrowth,
    OrderedGrowth.branchIntegralAux_cons_nil_eq_integral_partialDeriv_standardInterp]
  apply intervalIntegral.integral_congr
  intro t _
  change partialDeriv e ρ
      (h.forest.standardInterp (h.extension.extendParam u t)) =
    partialDeriv e ρ
      (h.forest.interpWithFill (h.extension.extendParam u t) t)
  rw [← h.forest.interpWithFill_eq_standardInterp_of_activeEdges_eq_empty
    (h.extension.extendParam u t) t hterm]

theorem integral_partialDeriv_eq_singleton_branchIntegralAux_of_emptyActiveEdges
    (h : ActiveExtension F e) (top : ℝ) (u : F.EdgeParam → ℝ)
    (ρ : (Edge V → ℝ) → ℝ) (hterm : h.forest.activeEdges = ∅) :
    (∫ t in 0..top, partialDeriv e ρ
        (h.forest.interpWithFill (h.extension.extendParam u t) t)) =
      h.singletonGrowth.branchIntegralAux top u ρ :=
  (h.singleton_branchIntegralAux_eq_integral_partialDeriv_of_emptyActiveEdges
    top u ρ hterm).symm

theorem singleton_branchIntegral_eq_integral_partialDeriv_of_emptyActiveEdges
    (h : ActiveExtension F e) (u : F.EdgeParam → ℝ)
    (ρ : (Edge V → ℝ) → ℝ) (hterm : h.forest.activeEdges = ∅) :
    h.singletonGrowth.branchIntegral u ρ =
      ∫ t in 0..(1 : ℝ), partialDeriv e ρ
        (h.forest.interpWithFill (h.extension.extendParam u t) t) :=
  h.singleton_branchIntegralAux_eq_integral_partialDeriv_of_emptyActiveEdges
    1 u ρ hterm

theorem integral_partialDeriv_eq_singleton_branchIntegral_of_emptyActiveEdges
    (h : ActiveExtension F e) (u : F.EdgeParam → ℝ)
    (ρ : (Edge V → ℝ) → ℝ) (hterm : h.forest.activeEdges = ∅) :
    (∫ t in 0..(1 : ℝ), partialDeriv e ρ
        (h.forest.interpWithFill (h.extension.extendParam u t) t)) =
      h.singletonGrowth.branchIntegral u ρ :=
  (h.singleton_branchIntegral_eq_integral_partialDeriv_of_emptyActiveEdges
    u ρ hterm).symm

end ActiveExtension

end Forest

end BKAR

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
