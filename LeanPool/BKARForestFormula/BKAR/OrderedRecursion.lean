/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.BKARForestFormula.BKAR.OrderedTerminal

/-! # Prepending an active extension to an ordered growth

The recursion step on growth certificates: `consGrowth` prepends a chosen
active extension to an ordered growth of the extended forest, and the
accompanying lemmas identify the first step, tail data, and branch
integrals of the resulting growth.  This is the combinatorial engine of the
inductive proof of the BKAR forest interpolation formula (see
`BKAR.Formula`).
-/

@[expose] public section

noncomputable section

namespace BKAR

namespace Forest

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace ActiveExtension

variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}

/--
Prepend a chosen active extension to an ordered growth from the extended forest.
-/
def consGrowth (h : ActiveExtension F e)
    (tail : OrderedGrowth h.forest order G) :
    OrderedGrowth F (e :: order) G :=
  OrderedGrowth.cons h.extension tail

theorem consGrowth_firstStep (h : ActiveExtension F e)
    (tail : OrderedGrowth h.forest order G) :
    (h.consGrowth tail).firstStep = h.extension :=
  rfl

theorem consGrowth_tailGrowth (h : ActiveExtension F e)
    (tail : OrderedGrowth h.forest order G) :
    (h.consGrowth tail).tailGrowth = tail :=
  rfl

theorem consGrowth_firstActiveExtension (h : ActiveExtension F e)
    (tail : OrderedGrowth h.forest order G) :
    (h.consGrowth tail).firstActiveExtension = h :=
  rfl

theorem consGrowth_tailForest (h : ActiveExtension F e)
    (tail : OrderedGrowth h.forest order G) :
    (h.consGrowth tail).tailForest = h.forest :=
  rfl

theorem singletonGrowth_eq_consGrowth_nil (h : ActiveExtension F e) :
    h.singletonGrowth = h.consGrowth (OrderedGrowth.nil h.forest) :=
  rfl

theorem consGrowth_params_first (h : ActiveExtension F e)
    (tail : OrderedGrowth h.forest order G)
    (u : F.EdgeParam → ℝ) (t : ℝ) (ts : List ℝ) :
    (h.consGrowth tail).params u (t :: ts)
        ⟨e, (h.consGrowth tail).mem_edges_of_mem_order
          (by rw [List.mem_cons]; exact Or.inl rfl)⟩ = t :=
  (h.consGrowth tail).params_first u t ts

theorem consGrowth_branchPoint_first (h : ActiveExtension F e)
    (tail : OrderedGrowth h.forest order G)
    (u : F.EdgeParam → ℝ) (t : ℝ) (ts : List ℝ) :
    (h.consGrowth tail).branchPoint u (t :: ts) e = t :=
  (h.consGrowth tail).branchPoint_first u t ts

theorem consGrowth_branchPoint_of_initial_mem (h : ActiveExtension F e)
    (tail : OrderedGrowth h.forest order G)
    (u : F.EdgeParam → ℝ) (ts : List ℝ) {e' : Edge V}
    (he' : e' ∈ F.edges) :
    (h.consGrowth tail).branchPoint u ts e' = u ⟨e', he'⟩ :=
  (h.consGrowth tail).branchPoint_of_initial_mem u ts he'

theorem consGrowth_branchIntegralAux_eq_integral_tail_partialDeriv
    (h : ActiveExtension F e) (tail : OrderedGrowth h.forest order G)
    (top : ℝ) (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    (h.consGrowth tail).branchIntegralAux top u ρ =
      ∫ t in 0..top,
        tail.branchIntegralAux t (h.extension.extendParam u t)
          (partialDeriv e ρ) :=
  OrderedGrowth.branchIntegralAux_cons_eq_integral_tail_partialDeriv
    h.extension tail top u ρ

theorem consGrowth_branchIntegral_eq_integral_tail_partialDeriv
    (h : ActiveExtension F e) (tail : OrderedGrowth h.forest order G)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    (h.consGrowth tail).branchIntegral u ρ =
      ∫ t in 0..(1 : ℝ),
        tail.branchIntegralAux t (h.extension.extendParam u t)
          (partialDeriv e ρ) :=
  h.consGrowth_branchIntegralAux_eq_integral_tail_partialDeriv tail 1 u ρ

end ActiveExtension

end Forest

end BKAR

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
