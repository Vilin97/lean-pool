/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Iso.GraphIso
import LeanPool.BrillNoetherGraphs.Utilities.Grassmannian.OnceMarked
import LeanPool.BrillNoetherGraphs.Utilities.Transmission.Transmission

/-!
# Transmission and chip-firing graph isomorphisms

The transmission condition is equivariant for relabelings of a chip-firing
graph.  In particular, the affine permutation is *not* changed: an
isomorphism only transports the two marked vertices and the witness divisor.
-/

namespace Utilities

universe u v

namespace CFGraphIso

variable {G : CFGraph.{u}} {H : CFGraph.{v}}

/-- Relabeling commutes with every twice-marked divisor twist. -/
@[simp] theorem mapDiv_add_marked_twist
    (φ : CFGraphIso G H) (D : CFDiv G) (u v : G.V) (a b : ℤ) :
    φ.mapDiv (D + a • oneChip u - b • oneChip v) =
      φ.mapDiv D + a • oneChip (φ.vertexEquiv u) -
        b • oneChip (φ.vertexEquiv v) := by
  simp only [map_sub, map_add, map_zsmul, mapDiv_one_chip]

/-- A single transmission rank inequality is invariant under relabeling the
graph, the two marks, and the divisor. -/
@[simp] theorem transmissionInequality_mapDiv_iff
    (φ : CFGraphIso G H) (u v : G.V) (τ : AspPerm) (D : CFDiv G)
    (a b : ℤ) :
    TransmissionInequality H (φ.vertexEquiv u) (φ.vertexEquiv v) τ
        (φ.mapDiv D) a b ↔
      TransmissionInequality G u v τ D a b := by
  unfold TransmissionInequality
  rw [← φ.mapDiv_add_marked_twist, φ.rank_mapDiv]

/-- Restricted transmission tests are invariant under graph relabeling. -/
@[simp] theorem satisfiesTransmissionOn_mapDiv_iff
    (φ : CFGraphIso G H) (u v : G.V) (τ : AspPerm) (D : CFDiv G)
    (S : Set (ℤ × ℤ)) :
    SatisfiesTransmissionOn H (φ.vertexEquiv u) (φ.vertexEquiv v) τ
        (φ.mapDiv D) S ↔
      SatisfiesTransmissionOn G u v τ D S := by
  constructor <;> intro h p hp
  · exact (φ.transmissionInequality_mapDiv_iff u v τ D p.1 p.2).mp (h p hp)
  · exact (φ.transmissionInequality_mapDiv_iff u v τ D p.1 p.2).mpr (h p hp)

/-- The complete transmission condition is invariant under graph relabeling. -/
@[simp] theorem satisfiesTransmission_mapDiv_iff
    (φ : CFGraphIso G H) (u v : G.V) (τ : AspPerm) (D : CFDiv G) :
    SatisfiesTransmission H (φ.vertexEquiv u) (φ.vertexEquiv v) τ
        (φ.mapDiv D) ↔
      SatisfiesTransmission G u v τ D := by
  constructor
  · rintro ⟨hDegree, hRows⟩
    refine ⟨?_, ?_⟩
    · rw [φ.deg_mapDiv, φ.genus_eq] at hDegree
      exact hDegree
    · intro a b
      exact (φ.transmissionInequality_mapDiv_iff u v τ D a b).mp (hRows a b)
  · rintro ⟨hDegree, hRows⟩
    refine ⟨?_, ?_⟩
    · rw [φ.deg_mapDiv, φ.genus_eq]
      exact hDegree
    · intro a b
      exact (φ.transmissionInequality_mapDiv_iff u v τ D a b).mpr (hRows a b)

/-- A transmission witness transports forward along a chip-firing graph
isomorphism. -/
theorem satisfiesTransmission_mapDiv
    (φ : CFGraphIso G H) (u v : G.V) (τ : AspPerm) (D : CFDiv G)
    (h : SatisfiesTransmission G u v τ D) :
    SatisfiesTransmission H (φ.vertexEquiv u) (φ.vertexEquiv v) τ
      (φ.mapDiv D) :=
  (φ.satisfiesTransmission_mapDiv_iff u v τ D).mpr h

/-- Transmission existence is invariant under graph relabeling. -/
@[simp] theorem transmissionExists_map_iff
    (φ : CFGraphIso G H) (u v : G.V) (τ : AspPerm) :
    TransmissionExists H (φ.vertexEquiv u) (φ.vertexEquiv v) τ ↔
      TransmissionExists G u v τ := by
  constructor
  · rintro ⟨D, hD⟩
    refine ⟨φ.symm.mapDiv D, ?_⟩
    simpa [CFGraphIso.symm] using
      (φ.symm.satisfiesTransmission_mapDiv_iff
        (φ.vertexEquiv u) (φ.vertexEquiv v) τ D).mpr hD
  · rintro ⟨D, hD⟩
    exact ⟨φ.mapDiv D, φ.satisfiesTransmission_mapDiv u v τ D hD⟩

/-- Forward form of `transmissionExists_map_iff`. -/
theorem transmissionExists_map
    (φ : CFGraphIso G H) (u v : G.V) (τ : AspPerm)
    (h : TransmissionExists G u v τ) :
    TransmissionExists H (φ.vertexEquiv u) (φ.vertexEquiv v) τ :=
  (φ.transmissionExists_map_iff u v τ).mpr h

/-! ## Once-marked consequences -/

/-- A normalized once-marked partition witness transports forward under a
graph relabeling. -/
theorem onceMarkedBNExists_map
    (φ : CFGraphIso G H) (u : G.V) (lambda : YoungDiagram)
    (h : OnceMarkedBNExists G u lambda) :
    OnceMarkedBNExists H (φ.vertexEquiv u) lambda := by
  obtain ⟨D, hDegree, hRows⟩ := h
  refine ⟨φ.mapDiv D, ?_, ?_⟩
  · rw [φ.deg_mapDiv, φ.genus_eq]
    exact hDegree
  · intro c hc
    calc
      rank H (φ.mapDiv D + c.1 • oneChip (φ.vertexEquiv u)) =
          rank H (φ.mapDiv (D + c.1 • oneChip u)) := by
            rw [map_add, map_zsmul, φ.mapDiv_one_chip]
      _ = rank G (D + c.1 • oneChip u) := φ.rank_mapDiv _
      _ ≥ c.2.2 := hRows c hc

/-- Once-marked partition occurrence is invariant under relabeling the graph
and its marked vertex. -/
@[simp] theorem onceMarkedBNExists_map_iff
    (φ : CFGraphIso G H) (u : G.V) (lambda : YoungDiagram) :
    OnceMarkedBNExists H (φ.vertexEquiv u) lambda ↔
      OnceMarkedBNExists G u lambda := by
  constructor
  · intro h
    simpa [CFGraphIso.symm] using
      φ.symm.onceMarkedBNExists_map (φ.vertexEquiv u) lambda h
  · exact φ.onceMarkedBNExists_map u lambda

/-- The full once-marked existence predicate is invariant under graph
relabeling. -/
@[simp] theorem onceMarkedBNExistence_map_iff
    (φ : CFGraphIso G H) (u : G.V) :
    OnceMarkedBNExistence H (φ.vertexEquiv u) ↔
      OnceMarkedBNExistence G u := by
  unfold OnceMarkedBNExistence
  constructor
  · intro h lambda hCard
    apply (φ.onceMarkedBNExists_map_iff u lambda).mp
    apply h lambda
    rw [φ.genus_eq]
    exact hCard
  · intro h lambda hCard
    apply (φ.onceMarkedBNExists_map_iff u lambda).mpr
    apply h lambda
    rw [← φ.genus_eq]
    exact hCard

end CFGraphIso

end Utilities
