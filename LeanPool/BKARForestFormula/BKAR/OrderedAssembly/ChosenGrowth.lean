/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.CanonicalForestBridge

/-! # Chosen growths as ordered growths

Converts a chosen growth — one following the active-extension choice
system — into an ordinary ordered growth certificate, and identifies the
branch integrals, interpolation points, and integrands of the grown and
canonical forests with the intrinsic ordered-contribution data of those
forests.
-/

noncomputable section

namespace BKAR

namespace Forest

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace ChosenGrowth

variable {choices : ActiveExtensionChoice V}
variable {F G : Forest V} {order : List (Edge V)}

/--
A chosen growth path is, in particular, an ordered growth certificate with the
same edge order and terminal forest.
-/
theorem exists_orderedGrowth (path : ChosenGrowth choices F order G) :
    Nonempty (OrderedGrowth F order G) := by
  induction path with
  | nil F =>
      exact ⟨OrderedGrowth.nil F⟩
  | cons he _tail ih =>
      rcases ih with ⟨growth⟩
      exact ⟨OrderedGrowth.cons (choices _ ⟨_, he⟩).extension growth⟩

/--
A definite ordered-growth certificate obtained from a chosen growth path.
This is only a certificate extractor; mathematical identities below do not
depend on the particular proof object chosen.
-/
def toOrderedGrowth (path : ChosenGrowth choices F order G) :
    OrderedGrowth F order G :=
  Classical.choice path.exists_orderedGrowth

end ChosenGrowth

namespace OrderedGrowth

variable {G : Forest V} {order : List (Edge V)}

/--
An ordered growth from the empty forest computes the same integral as the
ordered contribution of its terminal `Forest` representative in that growth order.
-/
theorem branchIntegral_emptyStart_eq_orderedContribution
    (growth : OrderedGrowth (Forest.empty V) order G)
    (ρ : (Edge V → ℝ) → ℝ) :
    growth.branchIntegral emptyParam ρ =
      G.orderedContribution order ρ := by
  rw [branchIntegral, branchIntegralAux, orderedContribution]
  apply orderedSimplexIntegral_congr_of_length
  intro ts hlen
  rw [branchIntegrand_def_standardInterp]
  rw [growth.params_emptyStart_eq_paramsOfOrder_of_length hlen]

end OrderedGrowth

namespace ChosenGrowth

variable {choices : ActiveExtensionChoice V}
variable {G : Forest V} {order : List (Edge V)}

/--
Chosen-growth version of
`OrderedGrowth.branchIntegral_emptyStart_eq_orderedContribution`.
-/
theorem branchIntegral_emptyStart_eq_orderedContribution
    (path : ChosenGrowth choices (Forest.empty V) order G)
    (ρ : (Edge V → ℝ) → ℝ) :
    path.toOrderedGrowth.branchIntegral emptyParam ρ =
      G.orderedContribution order ρ :=
  path.toOrderedGrowth.branchIntegral_emptyStart_eq_orderedContribution ρ

end ChosenGrowth

/-- The ordered-growth certificate carried by a grown support/order forest. -/
def grownForestForSupportOrderGrowth
    (choices : ActiveExtensionChoice V)
    (I : ForestIndex V)
    (order : {order : List (Edge V) // order ∈ edgeSetOrders I.edges}) :
    OrderedGrowth (Forest.empty V) order.val
      (grownForestForSupportOrder choices I order) :=
  (chosenGrowth_of_followOrderOption_eq_some choices
    (followOrderOption_grownForestForSupportOrder choices I order)).toOrderedGrowth

/--
The grown support/order forest's ordered contribution can be read as the
branch integral of its concrete ordered-growth certificate.
-/
theorem grownForestForSupportOrder_branchIntegral_eq_orderedContribution
    (choices : ActiveExtensionChoice V)
    (I : ForestIndex V)
    (order : {order : List (Edge V) // order ∈ edgeSetOrders I.edges})
    (ρ : (Edge V → ℝ) → ℝ) :
  (grownForestForSupportOrderGrowth choices I order).branchIntegral
        emptyParam ρ =
      (grownForestForSupportOrder choices I order).orderedContribution
        order.val ρ :=
  OrderedGrowth.branchIntegral_emptyStart_eq_orderedContribution
    (grownForestForSupportOrderGrowth choices I order) ρ

/--
The branch point attached to a grown support/order forest is exactly its
standard interpolation in the same ordered-sector coordinates.
-/
theorem grownForestForSupportOrder_branchPoint_eq_standardInterp_paramsOfOrder
    (choices : ActiveExtensionChoice V)
    (I : ForestIndex V)
    (order : {order : List (Edge V) // order ∈ edgeSetOrders I.edges})
    (ts : List ℝ) (hlen : ts.length = order.val.length) :
    (grownForestForSupportOrderGrowth choices I order).branchPoint
        emptyParam ts =
      (grownForestForSupportOrder choices I order).standardInterp
        ((grownForestForSupportOrder choices I order).paramsOfOrder
          order.val ts) := by
  rw [OrderedGrowth.branchPoint_def]
  rw [OrderedGrowth.params_emptyStart_eq_paramsOfOrder_of_length
    (grownForestForSupportOrderGrowth choices I order) hlen]

/--
The grown support/order branch integrand is the usual ordered-sector
integrand of the grown `Forest` representative, in list simplex coordinates.
-/
theorem grownForestForSupportOrder_branchIntegrand_eq_orderedSectorIntegrand
    (choices : ActiveExtensionChoice V)
    (I : ForestIndex V)
    (order : {order : List (Edge V) // order ∈ edgeSetOrders I.edges})
    (ρ : (Edge V → ℝ) → ℝ)
    (ts : List ℝ) (hlen : ts.length = order.val.length) :
    (grownForestForSupportOrderGrowth choices I order).branchIntegrand
        emptyParam ρ ts =
      mixedPartialList order.val.reverse ρ
        ((grownForestForSupportOrder choices I order).standardInterp
          ((grownForestForSupportOrder choices I order).paramsOfOrder
            order.val ts)) := by
  rw [OrderedGrowth.branchIntegrand_def_standardInterp]
  rw [OrderedGrowth.params_emptyStart_eq_paramsOfOrder_of_length
    (grownForestForSupportOrderGrowth choices I order) hlen]

/-- The ordered-growth certificate carried by the canonical support representative. -/
def canonicalGrownForestForSupportGrowth
    (choices : ActiveExtensionChoice V) (I : ForestIndex V) :
    OrderedGrowth (Forest.empty V) I.canonicalOrder.val
      (canonicalGrownForestForSupport choices I) :=
  grownForestForSupportOrderGrowth choices I I.canonicalOrder

/--
The canonical support representative's canonical-order contribution is the
branch integral of its concrete ordered-growth certificate.
-/
theorem canonicalGrownForestForSupport_branchIntegral_eq_orderedContribution
    (choices : ActiveExtensionChoice V) (I : ForestIndex V)
    (ρ : (Edge V → ℝ) → ℝ) :
  (canonicalGrownForestForSupportGrowth choices I).branchIntegral
        emptyParam ρ =
      (canonicalGrownForestForSupport choices I).orderedContribution
        I.canonicalOrder.val ρ :=
  OrderedGrowth.branchIntegral_emptyStart_eq_orderedContribution
    (canonicalGrownForestForSupportGrowth choices I) ρ

/--
The branch point attached to the canonical support representative is exactly
its standard interpolation in canonical-order coordinates.
-/
theorem canonicalGrownForestForSupport_branchPoint_eq_standardInterp_paramsOfOrder
    (choices : ActiveExtensionChoice V) (I : ForestIndex V)
    (ts : List ℝ) (hlen : ts.length = I.canonicalOrder.val.length) :
    (canonicalGrownForestForSupportGrowth choices I).branchPoint
        emptyParam ts =
      (canonicalGrownForestForSupport choices I).standardInterp
        ((canonicalGrownForestForSupport choices I).paramsOfOrder
          I.canonicalOrder.val ts) := by
  rw [OrderedGrowth.branchPoint_def]
  rw [OrderedGrowth.params_emptyStart_eq_paramsOfOrder_of_length
    (canonicalGrownForestForSupportGrowth choices I) hlen]

/--
The canonical support representative's canonical branch integrand is the
usual ordered-sector integrand of that representative, in list simplex
coordinates.
-/
theorem canonicalGrownForestForSupport_branchIntegrand_eq_orderedSectorIntegrand
    (choices : ActiveExtensionChoice V) (I : ForestIndex V)
    (ρ : (Edge V → ℝ) → ℝ)
    (ts : List ℝ) (hlen : ts.length = I.canonicalOrder.val.length) :
    (canonicalGrownForestForSupportGrowth choices I).branchIntegrand
        emptyParam ρ ts =
      mixedPartialList I.canonicalOrder.val.reverse ρ
        ((canonicalGrownForestForSupport choices I).standardInterp
          ((canonicalGrownForestForSupport choices I).paramsOfOrder
            I.canonicalOrder.val ts)) := by
  rw [OrderedGrowth.branchIntegrand_def_standardInterp]
  rw [OrderedGrowth.params_emptyStart_eq_paramsOfOrder_of_length
    (canonicalGrownForestForSupportGrowth choices I) hlen]

end Forest

end BKAR

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
