/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.Basics.Definitions
import LeanPool.BrillNoetherGraphs.Utilities.Iso.GraphIso

/-!
# Torsion order under graph isomorphism

The paper's torsion order is intrinsic to a marked graph.  This file supplies
the raw-divisor transport needed to use certified subdivision relabelings.
-/

namespace Bananas

open Utilities

theorem torsionWitness_map
    {G H : CFGraph} (φ : CFGraphIso G H) (u v : G.V) (k : ℕ)
    (h : TorsionWitness (mark G u v) k) :
    TorsionWitness (mark H (φ.vertexEquiv u) (φ.vertexEquiv v)) k := by
  refine ⟨h.1, ?_⟩
  have hMap := (φ.linear_equiv_mapDiv_iff
    ((k : ℤ) • (one_chip u - one_chip v)) 0).mpr h.2
  have hDiv : φ.mapDiv ((k : ℤ) • (one_chip u - one_chip v)) =
      (k : ℤ) • (one_chip (φ.vertexEquiv u) - one_chip (φ.vertexEquiv v)) := by
    rw [map_zsmul, map_sub, φ.mapDiv_one_chip, φ.mapDiv_one_chip]
  rw [hDiv] at hMap
  exact hMap

theorem torsionWitness_map_iff
    {G H : CFGraph} (φ : CFGraphIso G H) (u v : G.V) (k : ℕ) :
    TorsionWitness (mark H (φ.vertexEquiv u) (φ.vertexEquiv v)) k ↔
      TorsionWitness (mark G u v) k := by
  constructor
  · intro h
    simpa [CFGraphIso.symm] using
      torsionWitness_map φ.symm (φ.vertexEquiv u) (φ.vertexEquiv v) k h
  · exact torsionWitness_map φ u v k

theorem isTorsionOrder_map_iff
    {G H : CFGraph} (φ : CFGraphIso G H) (u v : G.V) (k : ℕ) :
    IsTorsionOrder (mark H (φ.vertexEquiv u) (φ.vertexEquiv v)) k ↔
      IsTorsionOrder (mark G u v) k := by
  constructor
  · rintro ⟨hWitness, hMin⟩
    refine ⟨(torsionWitness_map_iff φ u v k).mp hWitness, ?_⟩
    intro m hm
    exact hMin m ((torsionWitness_map_iff φ u v m).mpr hm)
  · rintro ⟨hWitness, hMin⟩
    refine ⟨(torsionWitness_map_iff φ u v k).mpr hWitness, ?_⟩
    intro m hm
    exact hMin m ((torsionWitness_map_iff φ u v m).mp hm)

end Bananas
