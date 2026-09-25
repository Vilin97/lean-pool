/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.BKARForestFormula.BKAR.CubePartition.MeasureSmoothness
public import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.CanonicalSector

/-! # Folding sectors into cube contributions

Sums the closed ordered cube-sector contributions over all enumerations of
a support and identifies the result with the ordinary cube contribution of
the canonical grown forest, which depends only on the underlying edge set
and not on the choice system.  This is the final fold from per-order
sectors to the one-cube-integral-per-forest form of the BKAR forest
interpolation formula (see `BKAR.Formula`).
-/

@[expose] public section

noncomputable section

namespace BKAR

namespace Forest

open MeasureTheory

variable {V : Type*} [Fintype V] [DecidableEq V]

/--
Closed ordered cube-sector contributions are invariant under replacing a `Forest` representative
by another `Forest` representative with the same underlying edge set.
-/
theorem orderedCubeSectorContribution_eq_of_edges_eq
    (F G : Forest V) (hedges : F.edges = G.edges)
    {order : List (Edge V)}
    (hForder : order ∈ F.edgeOrders) (hGorder : order ∈ G.edgeOrders)
    (ρ : (Edge V → ℝ) → ℝ) :
    F.orderedCubeSectorContribution order ρ =
      G.orderedCubeSectorContribution order ρ := by
  rw [F.orderedCubeSectorContribution_eq_orderedFinSimplexIntegral hForder ρ]
  rw [G.orderedCubeSectorContribution_eq_orderedFinSimplexIntegral hGorder ρ]
  apply setIntegral_congr_fun (measurableSet_orderedFinSimplex order.length)
  intro ts _hts
  apply congrArg (mixedPartialList order.reverse ρ)
  rw [← F.paramsOfOrder_ofFn_eq_orderMeasurableEquiv_symm hForder ts]
  rw [← G.paramsOfOrder_ofFn_eq_orderMeasurableEquiv_symm hGorder ts]
  exact F.standardInterp_paramsOfOrder_eq_of_edges_eq G hedges
    order (List.ofFn ts)

/--
The existing cube-partition theorem, folded in the direction needed by
support-indexed ordered assembly.
-/
theorem sum_edgeOrders_orderedCubeSectorContribution_eq_cubeContribution
    (F : Forest V) (ρ : (Edge V → ℝ) → ℝ)
    (hρ : BKARContDiff ρ) :
    Finset.sum F.edgeOrders
      (fun order => F.orderedCubeSectorContribution order ρ) =
      F.cubeContribution ρ :=
  (F.cubeContribution_eq_sum_orderedCubeSectorContribution ρ hρ).symm

/--
The unordered cube contribution depends only on the edge set, not on the
path data stored in the `Forest` representative.
-/
theorem cubeContribution_eq_of_edges_eq
    (F G : Forest V) (hedges : F.edges = G.edges)
    (ρ : (Edge V → ℝ) → ℝ) (hρ : BKARContDiff ρ) :
    F.cubeContribution ρ = G.cubeContribution ρ := by
  calc
    F.cubeContribution ρ =
      Finset.sum F.edgeOrders
        (fun order => F.orderedCubeSectorContribution order ρ) := by
        exact (F.sum_edgeOrders_orderedCubeSectorContribution_eq_cubeContribution
          ρ hρ).symm
    _ =
      Finset.sum F.edgeOrders
        (fun order => G.orderedCubeSectorContribution order ρ) := by
        apply Finset.sum_congr rfl
        intro order horder
        have hGorder : order ∈ G.edgeOrders := by
          simpa [edgeOrders, hedges] using horder
        exact F.orderedCubeSectorContribution_eq_of_edges_eq G hedges
          horder hGorder ρ
    _ =
      Finset.sum G.edgeOrders
        (fun order => G.orderedCubeSectorContribution order ρ) := by
        have horders : F.edgeOrders = G.edgeOrders := by
          simp [edgeOrders, hedges]
        rw [horders]
    _ = G.cubeContribution ρ :=
        G.sum_edgeOrders_orderedCubeSectorContribution_eq_cubeContribution ρ hρ

/--
Transport the ordered-sector fold from a forest's own `edgeOrders` to the
canonical order set of any support index with the same edge set.
-/
theorem sum_edgeSetOrders_orderedCubeSectorContribution_eq_cubeContribution_of_edges_eq
    (F : Forest V) (I : ForestIndex V)
    (ρ : (Edge V → ℝ) → ℝ) (hρ : BKARContDiff ρ)
    (hedges : F.edges = I.edges) :
    Finset.sum (edgeSetOrders I.edges)
      (fun order => F.orderedCubeSectorContribution order ρ) =
      F.cubeContribution ρ := by
  simpa [edgeOrders, hedges] using
    F.sum_edgeOrders_orderedCubeSectorContribution_eq_cubeContribution ρ hρ

/--
The canonical grown forest over a support folds its support-indexed ordered
cube sectors back to its unordered cube contribution.
-/
theorem sectorContributionSum_eq_canonicalContribution
    (choices : ActiveExtensionChoice V) (I : ForestIndex V)
    (ρ : (Edge V → ℝ) → ℝ) (hρ : BKARContDiff ρ) :
    Finset.sum (edgeSetOrders I.edges)
      (fun order =>
        (canonicalGrownForestForSupport choices I).orderedCubeSectorContribution
          order ρ) =
      (canonicalGrownForestForSupport choices I).cubeContribution ρ :=
  (canonicalGrownForestForSupport choices I)
    |>.sum_edgeSetOrders_orderedCubeSectorContribution_eq_cubeContribution_of_edges_eq
      I ρ hρ (canonicalGrownForestForSupport_edges choices I)

/--
After sectorwise canonicalization, the whole support/order sum over grown
`Forest` representatives folds to the ordinary cube contribution of the canonical grown
representative.
-/
theorem sum_orderedSectorContribution_eq_canonicalContribution
    (choices : ActiveExtensionChoice V) (I : ForestIndex V)
    (ρ : (Edge V → ℝ) → ℝ) (hρ : BKARContDiff ρ) :
    Finset.sum (edgeSetOrders I.edges).attach
      (fun order =>
        (grownForestForSupportOrder choices I order).orderedCubeSectorContribution
          order.val ρ) =
      (canonicalGrownForestForSupport choices I).cubeContribution ρ := by
  calc
    Finset.sum (edgeSetOrders I.edges).attach
        (fun order =>
          (grownForestForSupportOrder choices I order).orderedCubeSectorContribution
            order.val ρ)
        =
      Finset.sum (edgeSetOrders I.edges).attach
        (fun order =>
          (canonicalGrownForestForSupport choices I).orderedCubeSectorContribution
            order.val ρ) := by
        apply Finset.sum_congr rfl
        intro order _horder
        exact
          grownForestForSupportOrder_orderedCubeSectorContribution_eq_canonical
            choices I order ρ
    _ =
      Finset.sum (edgeSetOrders I.edges)
        (fun order =>
          (canonicalGrownForestForSupport choices I).orderedCubeSectorContribution
            order ρ) := by
        exact
          Finset.sum_attach (edgeSetOrders I.edges)
            (fun order =>
              (canonicalGrownForestForSupport choices I).orderedCubeSectorContribution
                order ρ)
    _ = (canonicalGrownForestForSupport choices I).cubeContribution ρ :=
        sectorContributionSum_eq_canonicalContribution
          choices I ρ hρ

/--
For a fixed support, the canonical grown cube contribution is independent
of the auxiliary active-extension choice system.
-/
theorem canonicalGrownForestForSupport_cubeContribution_eq_of_choices
    (choices₁ choices₂ : ActiveExtensionChoice V) (I : ForestIndex V)
    (ρ : (Edge V → ℝ) → ℝ) (hρ : BKARContDiff ρ) :
    (canonicalGrownForestForSupport choices₁ I).cubeContribution ρ =
      (canonicalGrownForestForSupport choices₂ I).cubeContribution ρ := by
  apply cubeContribution_eq_of_edges_eq
  · simp [canonicalGrownForestForSupport_edges]
  · exact hρ

end Forest

end BKAR

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
