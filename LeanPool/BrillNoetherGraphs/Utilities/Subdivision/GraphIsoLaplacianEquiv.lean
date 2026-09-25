/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Iso.GraphIso
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.LaplacianEquiv
public import LeanPool.BrillNoetherGraphs.Utilities.Transmission.TransmissionExistence

/-!
# Compatibility between graph and Laplacian equivalences

The graph-isomorphism and certificate layers use the same vertex-equivalence
and edge-multiplicity data.  This module gives the two presentations explicit
conversions, so results from either layer can be used without rebuilding that
data by hand.
-/

@[expose] public section

namespace Utilities

universe u v

namespace CFGraphIso

variable {G : CFGraph.{u}} {H : CFGraph.{v}}

/-- Regard a chip-firing graph isomorphism as a Laplacian-preserving vertex
equivalence. -/
def toLaplacianEquiv (φ : CFGraphIso G H) : Certificate.LaplacianEquiv G H where
  toEquiv := φ.vertexEquiv
  num_edges_eq := φ.map_num_edges

@[simp] theorem toLaplacianEquiv_mapDiv (φ : CFGraphIso G H) (D : CFDiv G) :
    φ.toLaplacianEquiv.mapDiv D = φ.mapDiv D := rfl

@[simp] theorem toLaplacianEquiv_mapScript
    (φ : CFGraphIso G H) (script : firingScript G) :
    φ.toLaplacianEquiv.mapScript script = φ.mapScript script := rfl

end CFGraphIso

namespace Certificate.LaplacianEquiv

variable {G : CFGraph.{u}} {H : CFGraph.{v}}

/-- Regard a Laplacian-preserving vertex equivalence as a chip-firing graph
isomorphism. -/
def toGraphIso (equivalence : LaplacianEquiv G H) : CFGraphIso G H where
  vertexEquiv := equivalence.toEquiv
  map_num_edges := equivalence.num_edges_eq

@[simp] theorem toGraphIso_mapDiv (equivalence : LaplacianEquiv G H)
    (D : CFDiv G) :
    equivalence.toGraphIso.mapDiv D = equivalence.mapDiv D := rfl

@[simp] theorem toGraphIso_mapScript (equivalence : LaplacianEquiv G H)
    (script : firingScript G) :
    equivalence.toGraphIso.mapScript script = equivalence.mapScript script := rfl

@[simp] theorem toGraphIso_toLaplacianEquiv
    (equivalence : LaplacianEquiv G H) :
    equivalence.toGraphIso.toLaplacianEquiv = equivalence := by
  cases equivalence
  rfl

/-- Full finite-length transmission existence is invariant under Laplacian
equivalences.  This exposes the graph-isomorphism theorem directly at the
certificate API, so relabelings need not reconstruct a second transport
object. -/
theorem transmissionExistence_map_iff
    (equivalence : LaplacianEquiv G H) (x y : G.V) :
    TransmissionExistence H (equivalence x) (equivalence y) ↔
      TransmissionExistence G x y :=
  equivalence.toGraphIso.transmissionExistence_map_iff x y

end Certificate.LaplacianEquiv

namespace CFGraphIso

variable {G : CFGraph.{u}} {H : CFGraph.{v}}

@[simp] theorem toLaplacianEquiv_toGraphIso (φ : CFGraphIso G H) :
    φ.toLaplacianEquiv.toGraphIso = φ := by
  cases φ
  rfl

end CFGraphIso

end Utilities
