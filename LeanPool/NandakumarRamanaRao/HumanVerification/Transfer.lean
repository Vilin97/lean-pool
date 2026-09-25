/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.HumanVerification.CauchyCroftonStatement
public import LeanPool.NandakumarRamanaRao.NRR.AAK.MainTheoremAffinePullback

/-! # Transfer -/

@[expose] public section

open Set MeasureTheory

noncomputable section

namespace NRR.HumanExport

private theorem interiors_disjoint_of_nullOverlap
    {K : NRR.Geometry.ConvexBody Plane} {n : ℕ}
    (Q : NRR.ConvexPartition K n) {i j : Fin n} (hij : i ≠ j) :
    Disjoint (interior (Q.piece i : Set Plane))
      (interior (Q.piece j : Set Plane)) := by
  by_contra hdisjoint
  obtain ⟨x, hx⟩ := Set.not_disjoint_iff.mp hdisjoint
  have hopen : IsOpen
      (interior (Q.piece i : Set Plane) ∩
        interior (Q.piece j : Set Plane)) :=
    isOpen_interior.inter isOpen_interior
  have hzero : volume
      (interior (Q.piece i : Set Plane) ∩
        interior (Q.piece j : Set Plane)) = 0 := by
    exact MeasureTheory.measure_mono_null
      (Set.inter_subset_inter interior_subset interior_subset)
      (Q.nullOverlap i j hij)
  have hpos : 0 < volume
      (interior (Q.piece i : Set Plane) ∩
        interior (Q.piece j : Set Plane)) :=
    hopen.measure_pos MeasureTheory.MeasureSpace.volume ⟨x, hx⟩
  exact hpos.ne' hzero

private theorem volume_eq_of_aak_area_eq
    (K L : NRR.Geometry.ConvexBody Plane)
    (harea : K.area = L.area) :
    volume (K : Set Plane) = volume (L : Set Plane) := by
  apply (ENNReal.toReal_eq_toReal_iff'
    (ne_of_lt K.area_lt_top) (ne_of_lt L.area_lt_top)).mp
  simpa [NRR.Geometry.ConvexBody.area] using harea

/--
The AAK theorem transferred to an arbitrary human-facing model once the
planar Cauchy--Crofton identity has been established.
-/
theorem equalAreaEqualPerimeterPartition_of_cauchyCrofton
    {α : Type} [ConvexFigureModel α]
    (hcrofton : HumanVerification.CauchyCroftonStatement)
    (F : α) (n : ℕ) (hn : 0 < n) :
    ∃ pieces : Fin n → α,
      IsConvexPartition F pieces ∧
      (∀ i j, area (pieces i) = area (pieces j)) ∧
      (∀ i j, perimeter (pieces i) = perimeter (pieces j)) := by
  obtain ⟨Q, hfair⟩ :=
    NRR.avvakumov_akopyan_karasev
      (ConvexFigureModel.toBody F) n hn
  let pieces : Fin n → α := fun i => ConvexFigureModel.ofBody (Q.piece i)
  refine ⟨pieces, ?_, ?_, ?_⟩
  · constructor
    · change ConvexFigureModel.carrier F =
        ⋃ i, ConvexFigureModel.carrier
          (ConvexFigureModel.ofBody (Q.piece i))
      simp only [ConvexFigureModel.carrier_ofBody_apply]
      simpa only [ConvexFigureModel.toBody_carrier] using Q.iUnion_piece_eq.symm
    · intro i j hij
      simp only [pieces, ConvexFigureModel.carrier_ofBody_apply]
      exact interiors_disjoint_of_nullOverlap Q hij
  · intro i j
    simp only [area, pieces, ConvexFigureModel.carrier_ofBody_apply]
    exact volume_eq_of_aak_area_eq (Q.piece i) (Q.piece j)
      (hfair.1 i j)
  · intro i j
    simp only [perimeter, pieces, ConvexFigureModel.carrier_ofBody_apply]
    rw [hcrofton (Q.piece i), hcrofton (Q.piece j), hfair.2 i j]

end NRR.HumanExport
