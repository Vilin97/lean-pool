/-
Copyright (c) 2026 Arthur Freitas Ramos et al. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/
import LeanPool.Kurosh.KuroshFreePart

/-!
# Kurosh Free Corollary

Adapted for Lean Pool from Arthur742Ramos/KuroshSubgroupTheorem,
commit `911707126c8b9bb0c764bf853008fe1053c0aad9`: imports, API compatibility,
and proof organization were revised.
-/

open Set Function
open CategoryTheory
open scoped Pointwise
noncomputable section

/-- Classical equality used locally in this part of the Kurosh construction. -/
local instance GraphCoveringTheory.Kurosh.kuroshFreeCorollaryDecidableEq
    (α : Type*) : DecidableEq α := Classical.decEq α

universe u v w

namespace GraphCoveringTheory.Kurosh

open Monoid.CoprodI

/-- Kill every stabilizer component and retain the free component. -/
noncomputable def treeKuroshComponentToFreePart {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (q : TreeKuroshComponentIndex G H) :
    TreeKuroshComponent G H q →* KuroshFreePart G H := by
  cases q using Sum.casesOn with
  | inl a =>
      change ULift.{max (u + 1) (v + 1)}
          (treeVertexStabilizer G H a) →* KuroshFreePart G H
      exact
        { toFun := fun _ => 1
          map_one' := by rfl
          map_mul' := by intro x y; simp }
  | inr q =>
      change ULift.{max (u + 1) (v + 1)}
          (KuroshFreePart G H) →* KuroshFreePart G H
      exact
        { toFun := fun x => x.down
          map_one' := by rfl
          map_mul' := by intro x y; rfl }

/-- The projection of the tree Kurosh product onto its free component. -/
noncomputable def treeKuroshProductToFreePart {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :
    TreeKuroshProduct G H →* KuroshFreePart G H := by
  change FreeProduct (TreeKuroshComponent G H) →* KuroshFreePart G H
  exact Monoid.CoprodI.lift (treeKuroshComponentToFreePart G H)

theorem treeKuroshProductToFreePart_vertex {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (a : RawBassSerreOrbitVertex G H)
    (x : treeVertexStabilizer G H a) :
    treeKuroshProductToFreePart G H
      (treeKuroshVertexInclusion G H a x) = 1 := by
  change treeKuroshProductToFreePart G H
      (Monoid.CoprodI.of
        (show TreeKuroshComponent G H (Sum.inl a) from ULift.up x)) = 1
  change (Monoid.CoprodI.lift (treeKuroshComponentToFreePart G H))
      (Monoid.CoprodI.of
        (show TreeKuroshComponent G H (Sum.inl a) from ULift.up x)) = 1
  rw [Monoid.CoprodI.lift_of]
  rfl

@[simp] theorem treeKuroshProductToFreePart_free {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (x : KuroshFreePart G H) :
    treeKuroshProductToFreePart G H
      (treeKuroshFreeInclusion G H x) = x := by
  change treeKuroshProductToFreePart G H
      (Monoid.CoprodI.of
        (show TreeKuroshComponent G H (Sum.inr PUnit.unit) from ULift.up x)) = x
  change (Monoid.CoprodI.lift (treeKuroshComponentToFreePart G H))
      (Monoid.CoprodI.of
        (show TreeKuroshComponent G H (Sum.inr PUnit.unit) from ULift.up x)) = x
  rw [Monoid.CoprodI.lift_of]
  rfl

theorem treeKuroshProductToH_factor_through_freePart {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (htriv : ∀ a : RawBassSerreOrbitVertex G H,
      Subsingleton (treeVertexStabilizer G H a)) :
    treeKuroshProductToH G H =
      (kuroshFreePartHom G H).comp (treeKuroshProductToFreePart G H) := by
  apply Monoid.CoprodI.ext_hom
  intro q
  cases q using Sum.casesOn with
  | inl a =>
      apply MonoidHom.ext
      intro x
      have hx : x.down = (1 : treeVertexStabilizer G H a) := by
        let := htriv a
        exact Subsingleton.elim _ _
      change treeKuroshComponentHom G H (Sum.inl a) x =
        kuroshFreePartHom G H
          (treeKuroshProductToFreePart G H
            (Monoid.CoprodI.of
              (show TreeKuroshComponent G H (Sum.inl a) from x)))
      change x.down.1 =
        kuroshFreePartHom G H
          ((Monoid.CoprodI.lift (treeKuroshComponentToFreePart G H))
            (Monoid.CoprodI.of
              (show TreeKuroshComponent G H (Sum.inl a) from x)))
      rw [Monoid.CoprodI.lift_of]
      change x.down.1 = 1
      exact congrArg Subtype.val hx
  | inr q =>
      apply MonoidHom.ext
      intro x
      change treeKuroshComponentHom G H (Sum.inr q) x =
        kuroshFreePartHom G H
          (treeKuroshProductToFreePart G H
            (Monoid.CoprodI.of
              (show TreeKuroshComponent G H (Sum.inr q) from x)))
      change kuroshFreePartHom G H x.down =
        kuroshFreePartHom G H
          ((Monoid.CoprodI.lift (treeKuroshComponentToFreePart G H))
            (Monoid.CoprodI.of
              (show TreeKuroshComponent G H (Sum.inr q) from x)))
      rw [Monoid.CoprodI.lift_of]
      rfl

theorem kuroshFreePartHom_surjective_of_trivial_stabilizers {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (htriv : ∀ a : RawBassSerreOrbitVertex G H,
      Subsingleton (treeVertexStabilizer G H a)) :
    Function.Surjective (kuroshFreePartHom G H) := by
  intro h
  obtain ⟨p, hp⟩ :=
    test_treeKuroshProductToH_surjective_for_kernel G H h
  refine ⟨treeKuroshProductToFreePart G H p, ?_⟩
  have hfactor := congrArg
    (fun f : @TreeKuroshProduct.{u, v, 0} ι G _ H →* H => f p)
    (@treeKuroshProductToH_factor_through_freePart.{u, v, 0}
      ι G _ H htriv)
  simpa using hfactor.symm.trans hp

/-- When all vertex stabilizers are trivial, free-part evaluation is an isomorphism onto `H`. -/
noncomputable def kuroshFreePartEquivOfTrivialStabilizers {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (htriv : ∀ a : RawBassSerreOrbitVertex G H,
      Subsingleton (treeVertexStabilizer G H a)) :
    KuroshFreePart G H ≃* H :=
  MulEquiv.ofBijective (kuroshFreePartHom G H)
    ⟨testKuroshFreePartHom_injective G H,
      kuroshFreePartHom_surjective_of_trivial_stabilizers G H htriv⟩

theorem kurosh_subgroup_is_free_of_trivial_stabilizers {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (htriv : ∀ a : RawBassSerreOrbitVertex G H,
      Subsingleton (treeVertexStabilizer G H a)) :
    IsFreeGroup H := by
  exact IsFreeGroup.ofMulEquiv
    (kuroshFreePartEquivOfTrivialStabilizers G H htriv)

end GraphCoveringTheory.Kurosh
