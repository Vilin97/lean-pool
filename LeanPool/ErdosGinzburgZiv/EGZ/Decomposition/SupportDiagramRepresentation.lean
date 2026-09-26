/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/
module


public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.SupportDiagram
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.SupportRepresentation
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.SupportRechartMass

/-!
# Representing a charted support diagram

The old affine maps need only realize the support residues and commute on
supported atoms. Injective modular lattice charts then give a surjective
representation of the charted flag on its minimal ambient affine spaces.
-/

@[expose] public section

namespace EGZ.LatticeSupportDiagram

variable {p d : ℕ} [NeZero p] [Fact p.Prime]
    (D : LatticeSupportDiagram) (C : ∀ x, IntegerLatticeChart (D.support x))
    (w : D.Node → FpCoord p d → ℕ)
    (φ : (x : D.Node) → FpCoord p d →ᵃ[ZMod p] FpCoord p (D.rank x))

/-- Express the old coordinate map through the modular chart's left inverse. -/
noncomputable def coordinateMap (x : D.Node) :
    FpCoord p d →ᵃ[ZMod p] FpCoord p (C x).rank := (C x).rechartMap (φ x)

variable (hinj : ∀ x, Function.Injective ((D.chart C x).modp p))

include hinj

omit [NeZero p] in
theorem coordinateMap_eq_mod (x : D.Node) (v : FpCoord p d) (q : IntCoord (C x).rank)
    (hv : φ x v = ((C x).map q).mod p) : coordinateMap D C φ x v = q.mod p := by
  change affineLeftInverse ((D.chart C x).modp p) (φ x v) = _
  rw [hv]
  change affineLeftInverse ((D.chart C x).modp p) (((D.chart C x).integer q).mod p) = _
  rw [← (D.chart C x).mod_integer]
  exact affineLeftInverse_apply _ (hinj x) _

variable (himage : ∀ x,
    φ x '' {v | FlagDecompositionRaw.cumulativeWeight (F := D.toConvexFlag) w x v ≠ 0} =
      IntCoord.mod p '' (D.support x : Set (IntCoord (D.rank x))))

include himage

omit [NeZero p] in
theorem coordinateMap_image_support (x : D.Node) :
    coordinateMap D C φ x ''
        {v | FlagDecompositionRaw.cumulativeWeight (F := D.toConvexFlag) w x v ≠ 0} =
      IntCoord.mod p '' ((C x).coordinateSupport : Set (IntCoord (C x).rank)) := by
  ext a
  constructor
  · rintro ⟨v, hv, rfl⟩
    have hold : φ x v ∈ φ x ''
        {v | FlagDecompositionRaw.cumulativeWeight (F := D.toConvexFlag) w x v ≠ 0} :=
      ⟨v, hv, rfl⟩
    rw [himage x] at hold
    obtain ⟨z, hz, hmod⟩ := hold
    refine ⟨(C x).coordinates z, (C x).coordinates_mem_coordinateSupport hz, ?_⟩
    symm
    apply D.coordinateMap_eq_mod C φ hinj x v
    rw [(C x).map_coordinates_of_mem hz]
    exact hmod.symm
  · rintro ⟨q, hq, rfl⟩
    have hold : ((C x).map q).mod p ∈ φ x ''
        {v | FlagDecompositionRaw.cumulativeWeight (F := D.toConvexFlag) w x v ≠ 0} := by
      rw [himage x]
      exact ⟨(C x).map q, (C x).mem_coordinateSupport.mp hq, rfl⟩
    obtain ⟨v, hv, hmod⟩ := hold
    exact ⟨v, hv, D.coordinateMap_eq_mod C φ hinj x v q hmod⟩

omit [NeZero p] in
theorem chart_coordinateMap (x : D.Node) (v : FpCoord p d)
    (hv : FlagDecompositionRaw.cumulativeWeight (F := D.toConvexFlag) w x v ≠ 0) :
    (D.chart C x).modp p (coordinateMap D C φ x v) = φ x v := by
  have hold : φ x v ∈ φ x ''
      {v | FlagDecompositionRaw.cumulativeWeight (F := D.toConvexFlag) w x v ≠ 0} :=
    ⟨v, hv, rfl⟩
  rw [himage x] at hold
  obtain ⟨z, hz, hmod⟩ := hold
  apply affineLeftInverse_retract _ (hinj x)
  refine ⟨((C x).coordinates z).mod p, ?_⟩
  rw [(D.chart C x).mod_integer]
  change ((C x).map ((C x).coordinates z)).mod p = φ x v
  rw [(C x).map_coordinates_of_mem hz]
  exact hmod

variable (hcompat : ∀ {x y : D.Node} (h : x ≤ y) {v : FpCoord p d},
    FlagDecompositionRaw.cumulativeWeight (F := D.toConvexFlag) w x v ≠ 0 →
      φ y v = (D.transition h).modp p (φ x v))

include hcompat

omit [NeZero p] in
theorem coordinateMap_compatible {x y : D.Node} (h : x ≤ y) {v : FpCoord p d}
    (hv : FlagDecompositionRaw.cumulativeWeight (F := D.toConvexFlag) w x v ≠ 0) :
    coordinateMap D C φ y v = (D.chartedTransition C h).modp p (coordinateMap D C φ x v) := by
  apply hinj y
  have hvy : FlagDecompositionRaw.cumulativeWeight (F := D.toConvexFlag) w y v ≠ 0 :=
    ne_of_gt ((Nat.pos_of_ne_zero hv).trans_le
      (FlagDecompositionRaw.cumulativeWeight_node_mono (F := D.toConvexFlag) w h v))
  rw [D.chart_coordinateMap C w φ hinj himage y v hvy,
    D.chart_transition_modp C h p,
    D.chart_coordinateMap C w φ hinj himage x v hv]
  exact hcompat h hv

/-- The actual representation of the charted support diagram. -/
noncomputable def chartedRepresentation : FpRepresentation p d (D.chartedFlag C) :=
  FpRepresentation.ofCumulativeSupport w (coordinateMap D C φ)
    (fun x ↦ (C x).coordinateSupport)
    (fun x ↦ (C x).coordinateSupport_affineIntSpans)
    (D.coordinateMap_image_support C w φ hinj himage)
    (D.coordinateMap_compatible C w φ hinj himage hcompat)
    (fun _ _ ↦ Iff.rfl)

end EGZ.LatticeSupportDiagram
