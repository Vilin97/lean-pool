/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.ForestIndexCube
public import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.AllBranchesSmoothness

/-! # The BKAR forest interpolation formula

Main results.  For a finite vertex set `V` and `ρ : (Edge V → ℝ) → ℝ`
smooth on the edge-coupling space (`BKARContDiff`), the flagship theorem
`bkar_formula_forestIndex_cube_contributions` states

  `ρ oneConfig = ∑ I : ForestIndex V, I.cubeContribution ρ`,

that is: the value of `ρ` at the all-ones coupling is the sum, over all
acyclic edge sets `F` on `V`, of `∫_{[0,1]^{E(F)}} ∂_{E(F)} ρ (x^F(u)) du`,
where `∂_{E(F)}` is the mixed partial derivative in the edge variables of
`F` and the interpolation point `x^F(u)` assigns to each edge the minimum
of `u` along the unique forest path between its endpoints (`0` across
components); the empty forest contributes `ρ zeroConfig`.  Variants:
support/order sector forms, grown-forest sector forms with proved
choice-independence, and the form with the empty sector split off
(`bkar_formula_nonempty`).

The formalization assumes `C^∞` smoothness where the classical statement
needs only `C^{|V|-1}` — a deliberate strengthening of the hypothesis.

## References

* D. Brydges, T. Kennedy, *Mayer expansions and the Hamilton–Jacobi
  equation*, J. Statist. Phys. 48 (1987) 19–49.
* A. Abdesselam, V. Rivasseau, *Trees, forests and jungles: a botanical
  garden for cluster expansions*, in Constructive Physics (Palaiseau 1994),
  Lecture Notes in Physics 446, Springer, 1995.  arXiv:hep-th/9409094.
-/

@[expose] public section

noncomputable section

namespace BKAR

variable {V : Type*} [Fintype V] [DecidableEq V]

/--
The scalar BKAR identity in the support/order form produced by the ordered
assembly. The empty forest sector is included in
`Forest.rootBoundarySupportOrderContribution` and contributes `ρ zeroConfig`.
-/
private theorem bkar_formula_with_choices
    (choices : Forest.ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ)
    (hρ : BKARContDiff ρ) :
    ρ oneConfig =
      Finset.sum (Finset.univ : Finset (ForestIndex V))
        (fun I => Finset.sum (Forest.edgeSetOrders I.edges)
          (fun order =>
            Forest.rootBoundarySupportOrderContribution choices ρ I order)) :=
  BKARContDiff.rho_oneConfig_eq_sum_rootBoundarySupportOrderContribution_of_contDiff
    hρ choices

/--
Canonical-representative sector form of BKAR: for each support/order sector, use
the `Forest` representative grown by following that order through the chosen active
extension data.
-/
private theorem bkar_formula_grown_forests_with_choices
    (choices : Forest.ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ)
    (hρ : BKARContDiff ρ) :
    ρ oneConfig =
      Finset.sum (Finset.univ : Finset (ForestIndex V))
        (fun I => Finset.sum (Forest.edgeSetOrders I.edges).attach
          (fun order =>
            (Forest.grownForestForSupportOrder choices I order).orderedContribution
              order.val ρ)) := by
  rw [bkar_formula_with_choices choices ρ hρ]
  apply Finset.sum_congr rfl
  intro I _
  exact
    Forest.sum_rootBoundarySupportOrderContribution_eq_sum_grownForestForSupportOrder
      choices I ρ

/--
Canonical-representative closed-sector form of BKAR: via the simplex-sector conversion,
every recursive ordered simplex contribution of
`bkar_formula_grown_forests_with_choices` has been converted to the
corresponding ordered cube-sector set integral for the `Forest` representative grown by
that support/order.
-/
private theorem bkar_formula_grown_forest_cube_sectors_with_choices
    (choices : Forest.ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ)
    (hρ : BKARContDiff ρ) :
    ρ oneConfig =
      Finset.sum (Finset.univ : Finset (ForestIndex V))
        (fun I => Finset.sum (Forest.edgeSetOrders I.edges).attach
          (fun order =>
            (Forest.grownForestForSupportOrder choices I order).orderedCubeSectorContribution
              order.val ρ)) := by
  rw [bkar_formula_grown_forests_with_choices choices ρ hρ]
  apply Finset.sum_congr rfl
  intro I _
  apply Finset.sum_congr rfl
  intro order _
  exact
    Forest.orderedContribution_eq_orderedCubeSectorContribution_of_contDiff
      (Forest.grownForestForSupportOrder choices I order)
      (Forest.grownForestForSupportOrder_order_mem_edgeOrders choices I order)
      ρ hρ

/--
The final closed-sector right-hand side, still written using the `Forest` representative
grown by the chosen active-extension system in each support/order sector.
-/
def grownForestCubeSectorSum
    (choices : Forest.ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ) : ℝ :=
  Finset.sum (Finset.univ : Finset (ForestIndex V))
    (fun I => Finset.sum (Forest.edgeSetOrders I.edges).attach
      (fun order =>
        (Forest.grownForestForSupportOrder choices I order).orderedCubeSectorContribution
          order.val ρ))

private theorem grownForestCubeSectorSum_eq
    (choices : Forest.ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ)
    (hρ : BKARContDiff ρ) :
    grownForestCubeSectorSum choices ρ = ρ oneConfig :=
  (bkar_formula_grown_forest_cube_sectors_with_choices choices ρ hρ).symm

/-- Compact public form of the closed-sector grown-representative BKAR identity. -/
private theorem bkar_formula_grown_forest_cube_sector_sum_with_choices
    (choices : Forest.ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ)
    (hρ : BKARContDiff ρ) :
    ρ oneConfig = grownForestCubeSectorSum choices ρ :=
  bkar_formula_grown_forest_cube_sectors_with_choices choices ρ hρ

/--
Canonical grown-representative cube contribution sum: one ordinary cube integral for
the canonical `Forest` representative over each support.
-/
def canonicalGrownForestCubeContributionSum
    (choices : Forest.ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ) : ℝ :=
  Finset.sum (Finset.univ : Finset (ForestIndex V))
    (fun I =>
      (Forest.canonicalGrownForestForSupport choices I).cubeContribution ρ)

/--
Folded BKAR formula: by the unit-cube partition step, the grown
support/order cube sectors have been sectorwise canonicalized and folded into
one ordinary cube contribution for each support.
-/
private theorem bkar_formula_canonical_grown_cube_contributions_with_choices
    (choices : Forest.ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ)
    (hρ : BKARContDiff ρ) :
    ρ oneConfig = canonicalGrownForestCubeContributionSum choices ρ := by
  rw [bkar_formula_grown_forest_cube_sectors_with_choices choices ρ hρ]
  rw [canonicalGrownForestCubeContributionSum]
  apply Finset.sum_congr rfl
  intro I _hI
  exact
    Forest.sum_orderedSectorContribution_eq_canonicalContribution
      choices I ρ hρ

private theorem canonicalGrownForestCubeContributionSum_eq
    (choices : Forest.ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ)
    (hρ : BKARContDiff ρ) :
    canonicalGrownForestCubeContributionSum choices ρ = ρ oneConfig :=
  (bkar_formula_canonical_grown_cube_contributions_with_choices
    choices ρ hρ).symm

/--
Support-sum form, with the right-hand side expressed directly
through the forest index rather than through a grown `Forest` representative.
-/
private theorem bkar_formula_forestIndex_cube_contributions_with_choices
    (choices : Forest.ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ)
    (hρ : BKARContDiff ρ) :
    ρ oneConfig =
      Finset.sum (Finset.univ : Finset (ForestIndex V))
        (fun I => I.cubeContribution ρ) := by
  rw [bkar_formula_canonical_grown_cube_contributions_with_choices
    choices ρ hρ]
  rw [canonicalGrownForestCubeContributionSum]
  apply Finset.sum_congr rfl
  intro I _hI
  exact (I.cubeContribution_eq_canonicalGrownForestForSupport
    choices ρ hρ).symm

/--
The total grown-representative closed-sector sum is independent of the auxiliary
active-extension choices. This is the honest global choice-independence fact
available from the proved BKAR identity without assuming path-data
proof-irrelevance for individual same-edge `Forest` representatives.
-/
theorem grownForestCubeSectorSum_choice_independent
    (choices₁ choices₂ : Forest.ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ)
    (hρ : BKARContDiff ρ) :
    grownForestCubeSectorSum choices₁ ρ =
      grownForestCubeSectorSum choices₂ ρ := by
  rw [grownForestCubeSectorSum_eq choices₁ ρ hρ,
    grownForestCubeSectorSum_eq choices₂ ρ hρ]

/--
The folded canonical grown-representative cube contribution sum is also independent
of the auxiliary active-extension choices.
-/
theorem canonicalGrownForestCubeContributionSum_choice_independent
    (choices₁ choices₂ : Forest.ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ)
    (hρ : BKARContDiff ρ) :
    canonicalGrownForestCubeContributionSum choices₁ ρ =
      canonicalGrownForestCubeContributionSum choices₂ ρ := by
  rw [canonicalGrownForestCubeContributionSum_eq choices₁ ρ hρ,
    canonicalGrownForestCubeContributionSum_eq choices₂ ρ hρ]

/--
For a fixed choice system and support, the canonical grown representative's
usual cube contribution is exactly the sum over all ordered sectors of that
same representative.
-/
theorem canonicalGrownForestForSupport_cubeContribution_eq_sum_edgeSetOrders
    (choices : Forest.ActiveExtensionChoice V)
    (I : ForestIndex V) (ρ : (Edge V → ℝ) → ℝ)
    (hρ : BKARContDiff ρ) :
    (Forest.canonicalGrownForestForSupport choices I).cubeContribution ρ =
      Finset.sum (Forest.edgeSetOrders I.edges)
        (fun order =>
          (Forest.canonicalGrownForestForSupport choices I).orderedCubeSectorContribution
            order ρ) := by
  exact
    (Forest.sectorContributionSum_eq_canonicalContribution
      choices I ρ hρ).symm

/--
The same scalar BKAR identity with the empty support/order sector split off as
`ρ zeroConfig`.
-/
private theorem bkar_formula_nonempty_with_choices
    (choices : Forest.ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ)
    (hρ : BKARContDiff ρ) :
    ρ oneConfig =
      ρ zeroConfig +
        Finset.sum
          ((Finset.univ : Finset (ForestIndex V)).filter
            (fun I => I.edges ≠ ∅))
          (fun I => Finset.sum (Forest.edgeSetOrders I.edges)
            (fun order =>
              Forest.boundarySupportOrderTreeFiber choices (Forest.empty V)
                [] [] 1 I order ρ)) :=
  BKARContDiff.oneConfig_eq_zeroConfig_add_nonemptyTreeSum_of_contDiff
    hρ choices

/--
Public scalar BKAR theorem. The statement is uniform in the auxiliary
forest-extension choices made by the ordered assembly.
-/
theorem bkar_formula
    (ρ : (Edge V → ℝ) → ℝ)
    (hρ : BKARContDiff ρ) :
    ∀ choices : Forest.ActiveExtensionChoice V,
      ρ oneConfig =
        Finset.sum (Finset.univ : Finset (ForestIndex V))
          (fun I => Finset.sum (Forest.edgeSetOrders I.edges)
            (fun order =>
              Forest.rootBoundarySupportOrderContribution choices ρ I order)) :=
  fun choices => bkar_formula_with_choices choices ρ hρ

/--
Public canonical-representative sector form. This removes the existential
`Forest`-representative bridge from each sector by choosing the forest grown by the canonical
order follower.
-/
theorem bkar_formula_grown_forests
    (ρ : (Edge V → ℝ) → ℝ)
    (hρ : BKARContDiff ρ) :
    ∀ choices : Forest.ActiveExtensionChoice V,
      ρ oneConfig =
        Finset.sum (Finset.univ : Finset (ForestIndex V))
          (fun I => Finset.sum (Forest.edgeSetOrders I.edges).attach
            (fun order =>
              (Forest.grownForestForSupportOrder choices I order).orderedContribution
                order.val ρ)) :=
  fun choices => bkar_formula_grown_forests_with_choices choices ρ hρ

/--
Public canonical-representative closed-sector form. The `Forest` representative choice remaining in
the sector integrand is removed by the canonicalized forms below (see
`bkar_formula_forestIndex_cube_contributions`).
-/
theorem bkar_formula_grown_forest_cube_sectors
    (ρ : (Edge V → ℝ) → ℝ)
    (hρ : BKARContDiff ρ) :
    ∀ choices : Forest.ActiveExtensionChoice V,
      ρ oneConfig =
        Finset.sum (Finset.univ : Finset (ForestIndex V))
          (fun I => Finset.sum (Forest.edgeSetOrders I.edges).attach
            (fun order =>
              (Forest.grownForestForSupportOrder choices I order).orderedCubeSectorContribution
                order.val ρ)) :=
  fun choices => bkar_formula_grown_forest_cube_sectors_with_choices choices ρ hρ

/--
Public compact grown-representative closed-sector form. The accompanying theorem
`grownForestCubeSectorSum_choice_independent` proves that the right-hand
side is independent of the auxiliary active-extension choices.
-/
theorem bkar_formula_grown_forest_cube_sector_sum
    (ρ : (Edge V → ℝ) → ℝ)
    (hρ : BKARContDiff ρ) :
    ∀ choices : Forest.ActiveExtensionChoice V,
      ρ oneConfig = grownForestCubeSectorSum choices ρ :=
  fun choices => bkar_formula_grown_forest_cube_sector_sum_with_choices choices ρ hρ

/--
Public folded canonical-representative cube-contribution BKAR form. This is the
support-indexed sum, modulo the still-explicit choice of `Forest`
representatives used to realize each abstract forest support.
-/
theorem bkar_formula_canonical_grown_cube_contributions
    (ρ : (Edge V → ℝ) → ℝ)
    (hρ : BKARContDiff ρ) :
    ∀ choices : Forest.ActiveExtensionChoice V,
      ρ oneConfig = canonicalGrownForestCubeContributionSum choices ρ :=
  fun choices =>
    bkar_formula_canonical_grown_cube_contributions_with_choices
      choices ρ hρ

/--
Forest-index cube-contribution BKAR form under the sole remaining structural
existence witness: a global active-extension choice system. The conclusion has
the final support-indexed right-hand side; the public theorem below
constructs this witness from the forest API.
-/
private theorem bkar_formula_forestIndex_cube_contributions_of_nonempty_choices
    (hchoices : Nonempty (Forest.ActiveExtensionChoice V))
    (ρ : (Edge V → ℝ) → ℝ)
    (hρ : BKARContDiff ρ) :
    ρ oneConfig =
      Finset.sum (Finset.univ : Finset (ForestIndex V))
        (fun I => I.cubeContribution ρ) :=
  bkar_formula_forestIndex_cube_contributions_with_choices
    (Classical.choice hchoices) ρ hρ

/--
Main scalar BKAR theorem — the forest interpolation formula: the value at the
all-ones configuration is the support-indexed sum of ordinary cube
contributions over abstract forest edge sets.
-/
theorem bkar_formula_forestIndex_cube_contributions
    (ρ : (Edge V → ℝ) → ℝ)
    (hρ : BKARContDiff ρ) :
    ρ oneConfig =
      Finset.sum (Finset.univ : Finset (ForestIndex V))
        (fun I => I.cubeContribution ρ) :=
  bkar_formula_forestIndex_cube_contributions_of_nonempty_choices
    (Forest.nonempty_activeExtensionChoice V) ρ hρ

/--
Public scalar BKAR theorem with the empty forest sector split off explicitly
as `ρ zeroConfig`.
-/
theorem bkar_formula_nonempty
    (ρ : (Edge V → ℝ) → ℝ)
    (hρ : BKARContDiff ρ) :
    ∀ choices : Forest.ActiveExtensionChoice V,
      ρ oneConfig =
        ρ zeroConfig +
          Finset.sum
            ((Finset.univ : Finset (ForestIndex V)).filter
              (fun I => I.edges ≠ ∅))
            (fun I => Finset.sum (Forest.edgeSetOrders I.edges)
              (fun order =>
                Forest.boundarySupportOrderTreeFiber choices (Forest.empty V)
                  [] [] 1 I order ρ)) :=
  fun choices => bkar_formula_nonempty_with_choices choices ρ hρ

end BKAR

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
