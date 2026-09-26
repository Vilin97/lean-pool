/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Bananas.Classification.GenusOneKGeneral
public import LeanPool.BrillNoetherGraphs.Bananas.Transmission.ChainTwoLoopsSameLeft
public import LeanPool.BrillNoetherGraphs.Bananas.Transmission.EqualTorsionKGeneral

/-!
# General transmission on pointed rigid genus-one factors

`PointedGenusOneRigid` supplies exactly the degree-one rigidity needed to
derive all-divisor submodularity for a distinct marking.  Combined with the
genus-one transmission theorem, this turns an exact torsion calculation on a
cycle factor directly into `KGeneralTransmission`.
-/

@[expose] public section

namespace Bananas

open Utilities

/-- Reversing the marked difference preserves nonprincipality. -/
private theorem nonprincipal_mark_difference_of_pointedRigid
    {G : CFGraph} {x u : G.V} (hRigid : PointedGenusOneRigid G x)
    (hu : u ≠ x) :
    ¬ linearEquiv G (oneChip u - oneChip x) 0 := by
  intro h
  apply hRigid.nontrivial u hu
  unfold linearEquiv at h ⊢
  have hNeg := (principalDivisors G).neg_mem h
  convert hNeg using 1
  abel

/-- A distinct marking on a pointed rigid genus-one graph is `k`-general at
its exact torsion order.  This is the factor-level input needed in the
opposite-side vertex-wedge branch of Theorem 4.13. -/
theorem pointedGenusOneRigid_kGeneral_of_isTorsionOrder
    {G : CFGraph} (x u : G.V) (hRigid : PointedGenusOneRigid G x)
    (hu : u ≠ x) {k : ℕ}
    (hOrder : IsTorsionOrder (mark G u x) k) :
    KGeneralTransmission (mark G u x) k := by
  apply kGeneralTransmission_genusOne_of_torsionOrder_and_allSubmodular
    hRigid.connected hRigid.genus_one hOrder
  exact allSubmodular_of_connected_genus_one_distinct_classes
    hRigid.connected hRigid.genus_one u x
    (nonprincipal_mark_difference_of_pointedRigid hRigid hu)

/-- The opposite-side wedge of two pointed rigid genus-one factors is
`k`-general as soon as the two factor markings have the same exact torsion
order.  This is the forward wedge clause in Theorem 4.13 with all
factor-level submodularity and transmission hypotheses discharged. -/
theorem pointedGenusOneRigid_vertexWedge_opposite_kGeneral_of_isTorsionOrder
    {G H : CFGraph} (x : G.V) (y : H.V) (u : G.V) (v : H.V) (k : ℕ)
    (hG : PointedGenusOneRigid G x) (hH : PointedGenusOneRigid H y)
    (hu : u ≠ x) (hv : v ≠ y)
    (hGOrder : IsTorsionOrder (mark G u x) k)
    (hHOrder : IsTorsionOrder (mark H y v) k) :
    KGeneralTransmission
      (mark (vertexWedge G H x y) (Sum.inl u)
        (wedgeRightVertex G H x y v)) k := by
  apply kGeneralTransmission_vertexWedge_opposite G H x y u v k
    hG.connected hH.connected
  · exact pointedGenusOneRigid_kGeneral_of_isTorsionOrder
      x u hG hu hGOrder
  · apply KGeneralTransmission.swap_marks v y
    have hHOrderSwap : IsTorsionOrder (mark H v y) k := by
      refine ⟨torsionWitness_swap y v hHOrder.1, ?_⟩
      intro m hm
      exact hHOrder.2 m (torsionWitness_swap v y hm)
    exact pointedGenusOneRigid_kGeneral_of_isTorsionOrder
      y v hH hv hHOrderSwap

end Bananas
