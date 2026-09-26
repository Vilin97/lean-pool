/-
Copyright (c) 2026 Arthur Freitas Ramos et al. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/
module

public import LeanPool.Kurosh.KuroshCoverLift

/-!
# Kurosh Path Relation

Adapted for Lean Pool from Arthur742Ramos/KuroshSubgroupTheorem,
commit `911707126c8b9bb0c764bf853008fe1053c0aad9`: imports, API compatibility,
and proof organization were revised.
-/

public section

open Set Function
open CategoryTheory
open scoped Pointwise
noncomputable section
/-- Classical equality used locally in this part of the Kurosh construction. -/
local instance GraphCoveringTheory.Kurosh.kuroshPathRelationDecidableEq
    (α : Type*) : DecidableEq α := Classical.decEq α
universe u v
namespace GraphCoveringTheory.Kurosh

/-- Recover the raw symmetrified Bass-Serre path from a path-category morphism. -/
def catPathToRaw {ι : Type v} (G : ι → Type u) [∀ i, Group (G i)]
    {a b : Quiver.Symmetrify (RawBassSerreVertex G)}
    (p : (CategoryTheory.Paths.of
      (Quiver.Symmetrify (RawBassSerreVertex G))).obj a ⟶
        (CategoryTheory.Paths.of
          (Quiver.Symmetrify (RawBassSerreVertex G))).obj b) :
    @Quiver.Path (Quiver.Symmetrify (RawBassSerreVertex G))
      (@Quiver.symmetrifyQuiver (RawBassSerreVertex G)
        (rawBassSerreQuiver G)) a b := p

end GraphCoveringTheory.Kurosh
