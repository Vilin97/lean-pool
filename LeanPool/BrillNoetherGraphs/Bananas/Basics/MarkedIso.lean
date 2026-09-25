/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Bananas.Transmission.TorsionIso
public import LeanPool.BrillNoetherGraphs.Utilities.Iso.GraphIso

/-!
# Second rank differences under marked graph isomorphism
-/

@[expose] public section

namespace Bananas

open Utilities

/-- `rankDelta` is invariant under an isomorphism that carries the ordered
marked pair to the ordered marked pair.  Explicit marked structures avoid any
dependently typed coercion through `mark`. -/
theorem rankDelta_mapDiv_of_marks
    {M N : TwiceMarked} (φ : CFGraphIso M.graph N.graph)
    (hu : φ.vertexEquiv M.u = N.u) (hv : φ.vertexEquiv M.v = N.v)
    (D : CFDiv M.graph) :
    rankDelta N (φ.mapDiv D) = rankDelta M D := by
  unfold rankDelta
  have hU : φ.mapDiv (D - oneChip M.u) = φ.mapDiv D - oneChip N.u := by
    rw [map_sub, φ.mapDiv_one_chip, hu]
  have hV : φ.mapDiv (D - oneChip M.v) = φ.mapDiv D - oneChip N.v := by
    rw [map_sub, φ.mapDiv_one_chip, hv]
  have hUV : φ.mapDiv (D - oneChip M.u - oneChip M.v) =
      φ.mapDiv D - oneChip N.u - oneChip N.v := by
    rw [map_sub, map_sub, φ.mapDiv_one_chip, φ.mapDiv_one_chip, hu, hv]
  rw [← hUV, ← hU, ← hV, φ.rank_mapDiv, φ.rank_mapDiv,
    φ.rank_mapDiv, φ.rank_mapDiv]

theorem torsionWitness_mapDiv_of_marks_iff
    {M N : TwiceMarked} (φ : CFGraphIso M.graph N.graph)
    (hu : φ.vertexEquiv M.u = N.u) (hv : φ.vertexEquiv M.v = N.v)
    (k : ℕ) :
    TorsionWitness N k ↔ TorsionWitness M k := by
  constructor
  · rintro ⟨hk, h⟩
    refine ⟨hk, ?_⟩
    have hDiv : φ.mapDiv ((k : ℤ) • (oneChip M.u - oneChip M.v)) =
        (k : ℤ) • (oneChip N.u - oneChip N.v) := by
      rw [map_zsmul, map_sub, φ.mapDiv_one_chip, φ.mapDiv_one_chip, hu, hv]
    have hMapped : linearEquiv N.graph
        (φ.mapDiv ((k : ℤ) • (oneChip M.u - oneChip M.v))) 0 := by
      rw [hDiv]
      exact h
    exact (φ.linear_equiv_mapDiv_iff _ 0).mp hMapped
  · rintro ⟨hk, h⟩
    refine ⟨hk, ?_⟩
    have hDiv : φ.mapDiv ((k : ℤ) • (oneChip M.u - oneChip M.v)) =
        (k : ℤ) • (oneChip N.u - oneChip N.v) := by
      rw [map_zsmul, map_sub, φ.mapDiv_one_chip, φ.mapDiv_one_chip, hu, hv]
    have hMapped := (φ.linear_equiv_mapDiv_iff _ 0).mpr h
    rw [hDiv] at hMapped
    exact hMapped

theorem isTorsionOrder_map_of_marks_iff
    {M N : TwiceMarked} (φ : CFGraphIso M.graph N.graph)
    (hu : φ.vertexEquiv M.u = N.u) (hv : φ.vertexEquiv M.v = N.v)
    (k : ℕ) :
    IsTorsionOrder N k ↔ IsTorsionOrder M k := by
  constructor
  · rintro ⟨hWitness, hMin⟩
    refine ⟨(torsionWitness_mapDiv_of_marks_iff φ hu hv k).mp hWitness, ?_⟩
    intro m hm
    exact hMin m ((torsionWitness_mapDiv_of_marks_iff φ hu hv m).mpr hm)
  · rintro ⟨hWitness, hMin⟩
    refine ⟨(torsionWitness_mapDiv_of_marks_iff φ hu hv k).mpr hWitness, ?_⟩
    intro m hm
    exact hMin m ((torsionWitness_mapDiv_of_marks_iff φ hu hv m).mp hm)

theorem submodular_mapDiv_of_marks_iff
    {M N : TwiceMarked} (φ : CFGraphIso M.graph N.graph)
    (hu : φ.vertexEquiv M.u = N.u) (hv : φ.vertexEquiv M.v = N.v)
    (D : CFDiv M.graph) :
    Submodular N (φ.mapDiv D) ↔ Submodular M D := by
  have hTwist (a b : ℤ) : φ.mapDiv (twist M D a b) =
      twist N (φ.mapDiv D) a b := by
    unfold twist
    rw [map_add, map_add, map_zsmul, map_zsmul,
      φ.mapDiv_one_chip, φ.mapDiv_one_chip, hu, hv]
  constructor
  · intro h a b
    have h' := h a b
    rw [← hTwist, rankDelta_mapDiv_of_marks φ hu hv] at h'
    exact h'
  · intro h a b
    have h' := h a b
    rw [← hTwist, rankDelta_mapDiv_of_marks φ hu hv]
    exact h'

/-- The same integer transmission permutation witnesses the mapped divisor.
This is the raw `IsTransmissionPermutation` counterpart of rank transport. -/
theorem isTransmissionPermutation_mapDiv_of_marks_iff
    {M N : TwiceMarked} (φ : CFGraphIso M.graph N.graph)
    (hu : φ.vertexEquiv M.u = N.u) (hv : φ.vertexEquiv M.v = N.v)
    (D : CFDiv M.graph) (τ : ℤ → ℤ) :
    IsTransmissionPermutation N (φ.mapDiv D) τ ↔
      IsTransmissionPermutation M D τ := by
  have hTwist (a b : ℤ) : φ.mapDiv (twist M D a (-b)) =
      twist N (φ.mapDiv D) a (-b) := by
    unfold twist
    rw [map_add, map_add, map_zsmul, map_zsmul,
      φ.mapDiv_one_chip, φ.mapDiv_one_chip, hu, hv]
  constructor
  · rintro ⟨hBij, hRows⟩
    refine ⟨hBij, ?_⟩
    intro a b
    have h := hRows a b
    have hTwist' : φ.mapDiv (D + a • oneChip M.u - b • oneChip M.v) =
        φ.mapDiv D + a • oneChip N.u - b • oneChip N.v := by
      simpa [twist, sub_eq_add_neg] using hTwist a b
    rw [← hTwist', rankDelta_mapDiv_of_marks φ hu hv] at h
    exact h
  · rintro ⟨hBij, hRows⟩
    refine ⟨hBij, ?_⟩
    intro a b
    have h := hRows a b
    have hTwist' : φ.mapDiv (D + a • oneChip M.u - b • oneChip M.v) =
        φ.mapDiv D + a • oneChip N.u - b • oneChip N.v := by
      simpa [twist, sub_eq_add_neg] using hTwist a b
    rw [← hTwist', rankDelta_mapDiv_of_marks φ hu hv]
    exact h

/-- All-divisor submodularity is a marked graph-isomorphism invariant. -/
theorem allSubmodular_map_of_marks_iff
    {M N : TwiceMarked} (φ : CFGraphIso M.graph N.graph)
    (hu : φ.vertexEquiv M.u = N.u) (hv : φ.vertexEquiv M.v = N.v) :
    AllSubmodular N ↔ AllSubmodular M := by
  constructor
  · intro h D
    exact (submodular_mapDiv_of_marks_iff φ hu hv D).mp (h (φ.mapDiv D))
  · intro h E
    let D : CFDiv M.graph := φ.symm.mapDiv E
    have hD := h D
    have hMapped := (submodular_mapDiv_of_marks_iff φ hu hv D).mpr hD
    simpa [D] using hMapped

/-- General transmission is invariant under a certified isomorphism of
ordered marked graphs. -/
theorem kGeneralTransmission_map_of_marks_iff
    {M N : TwiceMarked} (φ : CFGraphIso M.graph N.graph)
    (hu : φ.vertexEquiv M.u = N.u) (hv : φ.vertexEquiv M.v = N.v)
    (k : ℕ) :
    KGeneralTransmission N k ↔ KGeneralTransmission M k := by
  constructor
  · rintro ⟨hTor, hSub, hData⟩
    refine ⟨(torsionWitness_mapDiv_of_marks_iff φ hu hv k).mp hTor,
      (allSubmodular_map_of_marks_iff φ hu hv).mp hSub, ?_⟩
    intro D
    obtain ⟨τ, hτ, hAffine, hFinite, hCount⟩ := hData (φ.mapDiv D)
    rw [φ.genus_eq] at hCount
    exact ⟨τ, (isTransmissionPermutation_mapDiv_of_marks_iff φ hu hv D τ).mp hτ,
      hAffine, hFinite, hCount⟩
  · rintro ⟨hTor, hSub, hData⟩
    refine ⟨(torsionWitness_mapDiv_of_marks_iff φ hu hv k).mpr hTor,
      (allSubmodular_map_of_marks_iff φ hu hv).mpr hSub, ?_⟩
    intro E
    let D : CFDiv M.graph := φ.symm.mapDiv E
    obtain ⟨τ, hτ, hAffine, hFinite, hCount⟩ := hData D
    rw [φ.genus_eq]
    have hMapped := (isTransmissionPermutation_mapDiv_of_marks_iff φ hu hv D τ).mpr hτ
    exact ⟨τ, by simpa [D] using hMapped, hAffine, hFinite, hCount⟩

end Bananas
