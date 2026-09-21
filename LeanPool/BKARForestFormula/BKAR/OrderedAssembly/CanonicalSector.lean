/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.ChosenGrowth
import LeanPool.BKARForestFormula.BKAR.CubePartition.SimplexSector.Finite

/-! # Canonicalizing the sector integrands

Rewrites each root support/order fiber as the closed ordered cube-sector
integral of the forest grown by that order, and shows that the sector
integrand depends only on the canonical data of the support: the
grown-forest sector contributions agree with those of the canonical
representative.
-/

noncomputable section

namespace BKAR

namespace Forest

open MeasureTheory

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace OrderedGrowth

variable {G : Forest V} {order : List (Edge V)}

/--
An empty-start ordered-growth sector can be read directly as a finite ordered
simplex integral of the branch integrand carried by the growth certificate.
-/
theorem orderedCubeSectorContribution_eq_integral_branchIntegrand_emptyStart
    (growth : OrderedGrowth (Forest.empty V) order G)
    (ρ : (Edge V → ℝ) → ℝ) :
    G.orderedCubeSectorContribution order ρ =
      ∫ ts in orderedFinSimplex order.length,
        growth.branchIntegrand emptyParam ρ (List.ofFn ts) := by
  have horder : order ∈ G.edgeOrders :=
    growth.order_mem_edgeOrders_emptyStart
  rw [G.orderedCubeSectorContribution_eq_orderedFinSimplexIntegral horder ρ]
  apply setIntegral_congr_fun (measurableSet_orderedFinSimplex order.length)
  intro ts _hts
  change
    mixedPartialList order.reverse ρ
        (G.standardInterp ((G.orderMeasurableEquivOfOrder horder).symm ts)) =
      growth.branchIntegrand emptyParam ρ (List.ofFn ts)
  rw [growth.branchIntegrand_def_standardInterp]
  rw [growth.params_emptyStart_eq_paramsOfOrder_of_length (by simp)]
  rw [G.paramsOfOrder_ofFn_eq_orderMeasurableEquiv_symm horder ts]

end OrderedGrowth

/--
Finite-sector normal form for the grown support/order forest, expressed via
its concrete chosen-growth branch integrand.
-/
theorem grownForestForSupportOrder_orderedCubeSectorContribution_eq_integral_branchIntegrand
    (choices : ActiveExtensionChoice V)
    (I : ForestIndex V)
    (order : {order : List (Edge V) // order ∈ edgeSetOrders I.edges})
    (ρ : (Edge V → ℝ) → ℝ) :
    (grownForestForSupportOrder choices I order).orderedCubeSectorContribution
        order.val ρ =
      ∫ ts in orderedFinSimplex order.val.length,
        (grownForestForSupportOrder_orderedGrowth choices I order).branchIntegrand
          emptyParam ρ (List.ofFn ts) :=
  OrderedGrowth.orderedCubeSectorContribution_eq_integral_branchIntegrand_emptyStart
    (grownForestForSupportOrder_orderedGrowth choices I order) ρ

/--
Finite-coordinate form of the grown support/order cube sector, written
directly with the grown forest's ordered-sector integrand.
-/
theorem grownForestForSupportOrder_orderedCubeSectorContribution_eq_orderedFinSimplexIntegral
    (choices : ActiveExtensionChoice V)
    (I : ForestIndex V)
    (order : {order : List (Edge V) // order ∈ edgeSetOrders I.edges})
    (ρ : (Edge V → ℝ) → ℝ) :
    (grownForestForSupportOrder choices I order).orderedCubeSectorContribution
        order.val ρ =
      ∫ ts in orderedFinSimplex order.val.length,
        mixedPartialList order.val.reverse ρ
          ((grownForestForSupportOrder choices I order).standardInterp
            ((Forest.orderMeasurableEquivOfOrder
                (grownForestForSupportOrder choices I order)
                (grownForestForSupportOrder_order_mem_edgeOrders
                  choices I order)).symm ts)) :=
  (grownForestForSupportOrder choices I order)
    |>.orderedCubeSectorContribution_eq_orderedFinSimplexIntegral
      (grownForestForSupportOrder_order_mem_edgeOrders choices I order) ρ

/--
Per-sector simplex-to-cube-sector bridge for the root support/order fiber:
the recursive ordered
simplex contribution is the corresponding closed cube-sector integral of the
`Forest` representative grown by following that same support order.
-/
theorem rootBoundarySupportOrderContribution_eq_grownForestForSupportOrder_orderedCubeSectorContribution
    (choices : ActiveExtensionChoice V)
    (I : ForestIndex V)
    (order : {order : List (Edge V) // order ∈ edgeSetOrders I.edges})
    (ρ : (Edge V → ℝ) → ℝ) (hρ : BKARContDiff ρ) :
    rootBoundarySupportOrderContribution choices ρ I order.val =
      (grownForestForSupportOrder choices I order).orderedCubeSectorContribution
        order.val ρ := by
  rw [rootBoundarySupportOrderContribution_eq_grownForestForSupportOrder
    choices I order ρ]
  exact
    (grownForestForSupportOrder choices I order)
      |>.orderedContribution_eq_orderedCubeSectorContribution_of_contDiff
        (grownForestForSupportOrder_order_mem_edgeOrders choices I order)
        ρ hρ

/--
Finite-sector normal form for the canonical grown representative in its
canonical order.
-/
theorem canonicalGrownForestForSupport_orderedCubeSectorContribution_eq_integral_branchIntegrand
    (choices : ActiveExtensionChoice V) (I : ForestIndex V)
    (ρ : (Edge V → ℝ) → ℝ) :
    (canonicalGrownForestForSupport choices I).orderedCubeSectorContribution
        I.canonicalOrder.val ρ =
      ∫ ts in orderedFinSimplex I.canonicalOrder.val.length,
        (canonicalGrownForestForSupport_orderedGrowth choices I).branchIntegrand
          emptyParam ρ (List.ofFn ts) :=
  OrderedGrowth.orderedCubeSectorContribution_eq_integral_branchIntegrand_emptyStart
    (canonicalGrownForestForSupport_orderedGrowth choices I) ρ

/--
Finite-coordinate form of the canonical grown representative's sector for
an arbitrary order of the same support.
-/
theorem canonicalGrownForestForSupport_orderedCubeSectorContribution_eq_orderedFinSimplexIntegral
    (choices : ActiveExtensionChoice V) (I : ForestIndex V)
    (order : {order : List (Edge V) // order ∈ edgeSetOrders I.edges})
    (ρ : (Edge V → ℝ) → ℝ) :
    (canonicalGrownForestForSupport choices I).orderedCubeSectorContribution
        order.val ρ =
      ∫ ts in orderedFinSimplex order.val.length,
        mixedPartialList order.val.reverse ρ
          ((canonicalGrownForestForSupport choices I).standardInterp
            ((Forest.orderMeasurableEquivOfOrder
                (canonicalGrownForestForSupport choices I)
                (canonicalGrownForestForSupport_order_mem_edgeOrders
                  choices I order.property)).symm ts)) :=
  (canonicalGrownForestForSupport choices I)
    |>.orderedCubeSectorContribution_eq_orderedFinSimplexIntegral
      (canonicalGrownForestForSupport_order_mem_edgeOrders
        choices I order.property) ρ

/--
The grown forest for a support/order and the canonical grown
representative have the same finite-coordinate interpolation point on that
support/order sector.
-/
theorem grownForestForSupportOrder_standardInterp_orderMeasurableEquiv_symm_eq_canonical
    (choices : ActiveExtensionChoice V)
    (I : ForestIndex V)
    (order : {order : List (Edge V) // order ∈ edgeSetOrders I.edges})
    (ts : Fin order.val.length → ℝ) :
    (grownForestForSupportOrder choices I order).standardInterp
        ((Forest.orderMeasurableEquivOfOrder
            (grownForestForSupportOrder choices I order)
            (grownForestForSupportOrder_order_mem_edgeOrders
              choices I order)).symm ts) =
      (canonicalGrownForestForSupport choices I).standardInterp
        ((Forest.orderMeasurableEquivOfOrder
            (canonicalGrownForestForSupport choices I)
            (canonicalGrownForestForSupport_order_mem_edgeOrders
              choices I order.property)).symm ts) := by
  let F : Forest V := grownForestForSupportOrder choices I order
  let G : Forest V := canonicalGrownForestForSupport choices I
  have hForder : order.val ∈ F.edgeOrders := by
    simpa [F] using grownForestForSupportOrder_order_mem_edgeOrders choices I order
  have hGorder : order.val ∈ G.edgeOrders := by
    simpa [G] using
      canonicalGrownForestForSupport_order_mem_edgeOrders
        choices I order.property
  have hedges : F.edges = G.edges := by
    simp [F, G, grownForestForSupportOrder_edges,
      canonicalGrownForestForSupport_edges]
  change
    F.standardInterp
        ((F.orderMeasurableEquivOfOrder hForder).symm ts) =
      G.standardInterp
        ((G.orderMeasurableEquivOfOrder hGorder).symm ts)
  rw [← F.paramsOfOrder_ofFn_eq_orderMeasurableEquiv_symm hForder ts]
  rw [← G.paramsOfOrder_ofFn_eq_orderMeasurableEquiv_symm hGorder ts]
  exact F.standardInterp_paramsOfOrder_eq_of_edges_eq G hedges
    order.val (List.ofFn ts)

/--
Pointwise finite-sector integrands agree after replacing the support/order
grown forest by the canonical grown representative.
-/
theorem grownForestForSupportOrder_orderedFinSectorIntegrand_eq_canonical
    (choices : ActiveExtensionChoice V)
    (I : ForestIndex V)
    (order : {order : List (Edge V) // order ∈ edgeSetOrders I.edges})
    (ρ : (Edge V → ℝ) → ℝ)
    (ts : Fin order.val.length → ℝ) :
    mixedPartialList order.val.reverse ρ
        ((grownForestForSupportOrder choices I order).standardInterp
          ((Forest.orderMeasurableEquivOfOrder
              (grownForestForSupportOrder choices I order)
              (grownForestForSupportOrder_order_mem_edgeOrders
                choices I order)).symm ts)) =
      mixedPartialList order.val.reverse ρ
        ((canonicalGrownForestForSupport choices I).standardInterp
          ((Forest.orderMeasurableEquivOfOrder
              (canonicalGrownForestForSupport choices I)
              (canonicalGrownForestForSupport_order_mem_edgeOrders
                choices I order.property)).symm ts)) :=
  congrArg (mixedPartialList order.val.reverse ρ)
    (grownForestForSupportOrder_standardInterp_orderMeasurableEquiv_symm_eq_canonical
      choices I order ts)

/--
Sectorwise canonicalization: the closed cube-sector contribution of the
`Forest` representative grown by a support/order equals the same ordered sector of the
canonical grown representative for that support.
-/
theorem grownForestForSupportOrder_orderedCubeSectorContribution_eq_canonical
    (choices : ActiveExtensionChoice V)
    (I : ForestIndex V)
    (order : {order : List (Edge V) // order ∈ edgeSetOrders I.edges})
    (ρ : (Edge V → ℝ) → ℝ) :
    (grownForestForSupportOrder choices I order).orderedCubeSectorContribution
        order.val ρ =
      (canonicalGrownForestForSupport choices I).orderedCubeSectorContribution
        order.val ρ := by
  rw [grownForestForSupportOrder_orderedCubeSectorContribution_eq_orderedFinSimplexIntegral
    choices I order ρ]
  rw [canonicalGrownForestForSupport_orderedCubeSectorContribution_eq_orderedFinSimplexIntegral
    choices I order ρ]
  apply setIntegral_congr_fun (measurableSet_orderedFinSimplex order.val.length)
  intro ts _hts
  exact
    grownForestForSupportOrder_orderedFinSectorIntegrand_eq_canonical
      choices I order ρ ts

end Forest

end BKAR

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
