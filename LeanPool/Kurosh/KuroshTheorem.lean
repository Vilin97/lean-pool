/-
Copyright (c) 2026 Arthur Freitas Ramos et al. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/
import LeanPool.Kurosh.KuroshActive

/-!
# The Kurosh subgroup theorem in Bass--Serre form

The subgroup acts on the Bass--Serre tree of the free product.  The quotient
graph supplies one vertex group for each quotient vertex and a free group for
the quotient graph.  The universal graph-of-groups cover constructed in the
supporting development identifies the resulting free product with the
subgroup itself.

Adapted for Lean Pool from Arthur742Ramos/KuroshSubgroupTheorem,
commit `911707126c8b9bb0c764bf853008fe1053c0aad9`: imports, API compatibility,
and proof organization were revised.
-/

open Set Function
open CategoryTheory
open scoped Pointwise
noncomputable section

universe u v

namespace GraphCoveringTheory.Kurosh

/-- The Bass--Serre graph-of-groups form of Kurosh's theorem. -/
noncomputable def kuroshBassSerreEquiv {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :
    @TreeKuroshProduct.{u, v, 0} ι G _ H ≃* H :=
  treeKuroshProductMulEquivH G H

/-- Every subgroup of a free product is the free product of its Bass--Serre
vertex stabilizers and the free group of the quotient graph. -/
theorem kurosh_bass_serre_decomposition {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :
    Nonempty (@TreeKuroshProduct.{u, v, 0} ι G _ H ≃* H) :=
  ⟨kuroshBassSerreEquiv G H⟩

/-- Every subgroup of a free product is a free product of the nontrivial
vertex stabilizers in the quotient Bass--Serre graph and the quotient graph's
free group. -/
theorem kurosh_decomposition {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :
    Nonempty (@KuroshActiveProduct.{u, v, 0} ι G _ H ≃* H) :=
  ⟨kuroshActiveEquivH G H⟩

/-- The vertex groups in the Bass--Serre decomposition are either trivial
central-vertex stabilizers or intersections with conjugates of the original
free factors. -/
theorem kurosh_vertex_stabilizer_classification {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (a : RawBassSerreOrbitVertex G H) :
    (∃ g : FreeProduct G,
      rawTreeRepresentative G H a = RawBassSerreVertex.central g ∧
      treeVertexStabilizer G H a = ⊥) ∨
    (∃ (i : ι) (g : FreeProduct G),
      rawTreeRepresentative G H a =
        RawBassSerreVertex.factor i (factorCosetMk G i g) ∧
      treeVertexStabilizer G H a = intersectionFactorInH H i g) :=
  test_treeVertexStabilizer_central_or_factor G H a

/-- Each nontrivial factor in the factor-only form is an intersection with a
conjugate of one of the original free factors. -/
theorem kurosh_factor_is_conjugate_intersection {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (j : KuroshActiveVertexIndex G H) :
    ∃ (i : ι) (g : FreeProduct G),
      treeVertexStabilizer G H j.1 = intersectionFactorInH H i g :=
  kurosh_active_vertex_intersection G H j

end GraphCoveringTheory.Kurosh
