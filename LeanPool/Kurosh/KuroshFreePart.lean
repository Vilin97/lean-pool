/-
Copyright (c) 2026 Arthur Freitas Ramos et al. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/
import LeanPool.Kurosh.KuroshKernel

/-!
# Kurosh Free Part

Adapted for Lean Pool from Arthur742Ramos/KuroshSubgroupTheorem,
commit `911707126c8b9bb0c764bf853008fe1053c0aad9`: imports, API compatibility,
and proof organization were revised.
-/

open CategoryTheory

noncomputable section

universe u v

namespace GraphCoveringTheory.Kurosh

/-- The quotient-graph free factor embeds in the subgroup. -/
theorem kuroshFreePartHom_injective {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :
    Function.Injective (kuroshFreePartHom G H) := by
  intro x y h
  have hfree : @treeKuroshFreeInclusion.{u, v, 0} ι G _ H x =
      treeKuroshFreeInclusion G H y := by
    apply Internal.treeKuroshProductToH_injective G H
    simpa only [treeKuroshProductToH_free] using h
  have hup : (ULift.up x : ULift.{max (u + 1) (v + 1)} (KuroshFreePart G H)) =
      ULift.up y := Monoid.CoprodI.of_injective (Sum.inr PUnit.unit) hfree
  exact ULift.up_injective hup

end GraphCoveringTheory.Kurosh
