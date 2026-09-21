/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Grassmannian.GrassmannianExistence
import LeanPool.BrillNoetherGraphs.Utilities.Transmission.TransmissionDuality
import LeanPool.BrillNoetherGraphs.Utilities.Transmission.TransmissionIso

/-!
# Finite-length transmission existence

The transmission existence problem ranges over affine sign-preserving
permutations with at most `genus G` inversions.  Finiteness is a separate
hypothesis: in Mathlib, `Set.ncard` is zero on an infinite set, so the bare
inequality

`(inv_set tau).ncard <= genus G`

does not express finite Coxeter length by itself.

The predicate in this file is the general two-marked existence condition.  Its
restriction to shifted Grassmannian permutations is exactly the once-marked
Brill--Noether existence predicate.
-/

namespace Utilities

universe uTransmission

/-- The inversion set of `tau` is finite.  Keeping this named avoids the
incorrect convention that `Set.ncard` alone detects finite ASP length. -/
def FiniteTransmissionPerm (tau : AspPerm) : Prop :=
  (inv_set tau).Finite

/-- Every finite-length ASP transmission problem allowed by the genus has a
witness on the twice-marked graph `(G,u,v)`. -/
def TransmissionExistence (G : CFGraph) (u v : G.V) : Prop :=
  forall tau : AspPerm,
    FiniteTransmissionPerm tau ->
    ((inv_set tau).ncard : Int) <= genus G ->
    TransmissionExists G u v tau

/-- The general transmission-existence conjecture for finite connected
twice-marked graphs. -/
def TransmissionExistenceConjecture : Prop :=
  forall (G : CFGraph.{uTransmission}), graph_connected G ->
    forall u v : G.V, TransmissionExistence G u v

/-- Every shifted Grassmannian permutation has finite transmission length. -/
theorem finiteTransmissionPerm_shiftedGrassmannianPerm
    (lambda : YoungDiagram) (chi : Int) :
    FiniteTransmissionPerm (shiftedGrassmannianPerm lambda chi) := by
  unfold FiniteTransmissionPerm
  rw [inv_set_shiftedGrassmannianPerm]
  exact grassmannianInvSet_finite lambda

/-- General finite-length transmission existence contains the complete
Grassmannian transmission family. -/
theorem grassmannianTransmissionExistence_of_transmissionExistence
    {G : CFGraph} {u v : G.V}
    (h : TransmissionExistence G u v) :
    GrassmannianTransmissionExistence G u v := by
  intro lambda hCard chi
  apply h (shiftedGrassmannianPerm lambda chi)
  · exact finiteTransmissionPerm_shiftedGrassmannianPerm lambda chi
  · rw [ncard_inv_set_shiftedGrassmannianPerm]
    exact hCard

/-- On a connected graph, the general twice-marked conjecture implies the
once-marked Brill--Noether existence statement at its first mark. -/
theorem onceMarkedBNExistence_of_transmissionExistence
    {G : CFGraph} (hG : graph_connected G) (u v : G.V)
    (h : TransmissionExistence G u v) :
    OnceMarkedBNExistence G u := by
  apply (grassmannianTransmissionExistence_iff_onceMarkedBNExistence
    hG u v).mp
  exact grassmannianTransmissionExistence_of_transmissionExistence h

/-! ## Inversion and mark symmetry -/

/-- Reversing an inversion and applying `tau` to both entries identifies the
inversion set of `tau` with that of its inverse. -/
theorem inv_set_inverse_eq_revMap_image (tau : AspPerm) :
    inv_set (tau⁻¹).func = tau.rev_map '' inv_set tau := by
  ext pair
  rcases pair with ⟨a, b⟩
  constructor
  · intro h
    have hPre : ⟨tau⁻¹ b, tau⁻¹ a⟩ ∈ inv_set tau := by
      simpa only [inv_inv] using ((tau⁻¹).inv_set_inverse a b).mp h
    refine ⟨⟨tau⁻¹ b, tau⁻¹ a⟩, hPre, ?_⟩
    simp [AspPerm.rev_map]
  · rintro ⟨⟨i, j⟩, hij, hImage⟩
    rw [← hImage]
    exact (tau.inv_set_inverse i j).mp hij

/-- The inversion-reversal map is injective. -/
theorem revMap_injective (tau : AspPerm) :
    Function.Injective tau.rev_map := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ h
  simp only [AspPerm.rev_map, Prod.mk.injEq] at h
  apply Prod.ext
  · exact tau.injective h.2
  · exact tau.injective h.1

/-- ASP inversion preserves the inversion number, including the infinite case
under Mathlib's `Set.ncard` convention. -/
theorem ncard_inv_set_inverse (tau : AspPerm) :
    (inv_set (tau⁻¹).func).ncard = (inv_set tau).ncard := by
  rw [inv_set_inverse_eq_revMap_image]
  exact Set.ncard_image_of_injective (inv_set tau) (revMap_injective tau)

/-- Finite transmission length is invariant under ASP inversion. -/
theorem finiteTransmissionPerm_inverse_iff (tau : AspPerm) :
    FiniteTransmissionPerm tau⁻¹ ↔ FiniteTransmissionPerm tau := by
  unfold FiniteTransmissionPerm
  rw [inv_set_inverse_eq_revMap_image]
  exact Set.finite_image_iff (revMap_injective tau).injOn

/-- Riemann--Roch duality makes the fully quantified transmission-existence
predicate symmetric in its two marked vertices. -/
theorem transmissionExistence_swap_iff
    {G : CFGraph} (hG : graph_connected G) (u v : G.V) :
    TransmissionExistence G v u ↔ TransmissionExistence G u v := by
  constructor
  · intro h tau hFinite hLength
    have hInverse : TransmissionExists G v u tau⁻¹ := by
      apply h tau⁻¹
      · exact (finiteTransmissionPerm_inverse_iff tau).2 hFinite
      · rw [ncard_inv_set_inverse]
        exact hLength
    simpa only [inv_inv] using transmissionExists_dual hG v u tau⁻¹ hInverse
  · intro h tau hFinite hLength
    have hInverse : TransmissionExists G u v tau⁻¹ := by
      apply h tau⁻¹
      · exact (finiteTransmissionPerm_inverse_iff tau).2 hFinite
      · rw [ncard_inv_set_inverse]
        exact hLength
    simpa only [inv_inv] using transmissionExists_dual hG u v tau⁻¹ hInverse

/-! ## Graph relabeling -/

namespace CFGraphIso

universe u v

/-- Full finite-length transmission existence is invariant under relabeling
the graph and both marked vertices. -/
theorem transmissionExistence_map_iff
    {G : CFGraph.{u}} {H : CFGraph.{v}} (equivalence : CFGraphIso G H)
    (x y : G.V) :
    TransmissionExistence H (equivalence.vertexEquiv x)
        (equivalence.vertexEquiv y) ↔
      TransmissionExistence G x y := by
  constructor
  · intro h tau hFinite hLength
    apply (equivalence.transmissionExists_map_iff x y tau).mp
    apply h tau hFinite
    rw [equivalence.genus_eq]
    exact hLength
  · intro h tau hFinite hLength
    apply (equivalence.transmissionExists_map_iff x y tau).mpr
    apply h tau hFinite
    rw [← equivalence.genus_eq]
    exact hLength

end CFGraphIso

end Utilities
