/-
Copyright (c) 2026 Arthur Freitas Ramos et al. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/
module

public import Mathlib.CategoryTheory.Action.Concrete
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.GroupTheory.Index

/-!
# Deck transformations of a regular finite Schreier action

The finite coset action used in the index-formula proof has a second useful
interpretation.  Its automorphisms as a `G`-set are the deck transformations
of the corresponding regular Schreier cover.  This file proves the regular
case directly: for a finite-index normal subgroup, right translation gives
all deck transformations, so the deck group is the quotient group.

Adapted for Lean Pool from Arthur742Ramos/KuroshSubgroupTheorem,
commit `911707126c8b9bb0c764bf853008fe1053c0aad9`: imports, API compatibility,
and proof organization were revised.
-/

@[expose] public section

open Set Function
open CategoryTheory

noncomputable section

universe u

namespace GraphCoveringTheory

/-- The finite `G`-set underlying the Schreier cover of a subgroup `H`. -/
abbrev SchreierAction (G : Type u) [Group G] (H : Subgroup G)
    [Fintype (G ⧸ H)] : Action FintypeCat G :=
  Action.FintypeCat.ofMulAction G (FintypeCat.of (G ⧸ H))

/-- Automorphisms of the finite Schreier action, i.e. its deck transformations. -/
abbrev SchreierDeckGroup (G : Type u) [Group G] (H : Subgroup G)
    [Fintype (G ⧸ H)] : Type _ := CategoryTheory.Aut (SchreierAction G H)

/-- The quotient acts on its coset space by the right translations induced from `G`. -/
noncomputable def quotientDeckEndHom (G : Type u) [Group G] (H : Subgroup G)
    [H.Normal] [Fintype (G ⧸ H)] : G ⧸ H →* End (SchreierAction G H) :=
  QuotientGroup.lift H (Action.FintypeCat.toEndHom H) (by
    intro n hn
    change Action.FintypeCat.toEndHom H n = 𝟙 _
    exact Action.FintypeCat.toEndHom_trivial_of_mem (N := H) hn)

@[simp]
lemma quotientDeckEndHom_mk (G : Type u) [Group G] (H : Subgroup G)
    [H.Normal] [Fintype (G ⧸ H)] (g h : G) :
    (quotientDeckEndHom G H (g : G ⧸ H)).hom ⟦h⟧ = ⟦h * g⁻¹⟧ := rfl

@[simp]
lemma quotientDeckEndHom_apply_one (G : Type u) [Group G] (H : Subgroup G)
    [H.Normal] [Fintype (G ⧸ H)] (q : G ⧸ H) :
    (quotientDeckEndHom G H q).hom (1 : G ⧸ H) = q⁻¹ := by
  refine QuotientGroup.induction_on q ?_
  intro g
  change (quotientDeckEndHom G H (g : G ⧸ H)).hom ⟦(1 : G)⟧ = _
  rw [quotientDeckEndHom_mk]
  change QuotientGroup.mk' H (1 * g⁻¹) = (QuotientGroup.mk' H g)⁻¹
  simp

/-- Right translations by inverse quotient elements, viewed as invertible equivariant
endomorphisms. -/
noncomputable def quotientDeckUnitsHom (G : Type u) [Group G] (H : Subgroup G)
    [H.Normal] [Fintype (G ⧸ H)] : (G ⧸ H) →* (End (SchreierAction G H))ˣ where
  toFun q :=
    { val := quotientDeckEndHom G H q
      inv := quotientDeckEndHom G H q⁻¹
      val_inv := by
        rw [← (quotientDeckEndHom G H).map_mul]
        simp
      inv_val := by
        rw [← (quotientDeckEndHom G H).map_mul]
        simp }
  map_one' := by
    apply Units.ext
    simp
  map_mul' q r := by
    apply Units.ext
    simp

/-!
The `Aut`/`Units` conversion is only packaging: the underlying action map is
still the explicit right-translation endomorphism above.
-/
/-- The homomorphism from the quotient group to automorphisms of its Schreier action. -/
noncomputable def quotientDeckHom (G : Type u) [Group G] (H : Subgroup G)
    [H.Normal] [Fintype (G ⧸ H)] : (G ⧸ H) →* SchreierDeckGroup G H :=
  (Aut.unitsEndEquivAut (SchreierAction G H)).toMonoidHom.comp
    (quotientDeckUnitsHom G H)

lemma quotientDeckHom_hom (G : Type u) [Group G] (H : Subgroup G)
    [H.Normal] [Fintype (G ⧸ H)] (q : G ⧸ H) :
    (quotientDeckHom G H q).hom.hom = (quotientDeckEndHom G H q).hom := rfl

@[simp]
lemma quotientDeckHom_apply_one (G : Type u) [Group G] (H : Subgroup G)
    [H.Normal] [Fintype (G ⧸ H)] (q : G ⧸ H) :
    (quotientDeckHom G H q).hom.hom (1 : G ⧸ H) = q⁻¹ := by
  rw [quotientDeckHom_hom]
  exact quotientDeckEndHom_apply_one G H q

private lemma schreierActionHom_ext_of_one (G : Type u) [Group G] (H : Subgroup G)
    [H.Normal] [Fintype (G ⧸ H)]
    (f g : SchreierAction G H ⟶ SchreierAction G H)
    (h : f.hom (1 : G ⧸ H) = g.hom (1 : G ⧸ H)) : f = g := by
  apply Action.hom_ext
  apply FintypeCat.hom_ext
  intro x
  induction x using Quotient.inductionOn with | _ a =>
    change (ConcreteCategory.hom f.hom) (a : G ⧸ H) =
      (ConcreteCategory.hom g.hom) (a : G ⧸ H)
    have ha : (a : G ⧸ H) = (a : G) • (1 : G ⧸ H) := by
      change QuotientGroup.mk' H a = (QuotientGroup.mk' H a) * 1
      simp
    have hf := ConcreteCategory.congr_hom (f.comm a) (1 : G ⧸ H)
    have hg := ConcreteCategory.congr_hom (g.comm a) (1 : G ⧸ H)
    change f.hom (a • (1 : G ⧸ H)) = a • f.hom (1 : G ⧸ H) at hf
    change g.hom (a • (1 : G ⧸ H)) = a • g.hom (1 : G ⧸ H) at hg
    rw [ha]
    exact hf.trans ((congrArg (fun z : G ⧸ H => a • z) h).trans hg.symm)

lemma quotientDeckHom_injective (G : Type u) [Group G] (H : Subgroup G)
    [H.Normal] [Fintype (G ⧸ H)] :
    Function.Injective (quotientDeckHom G H) := by
  intro q r h
  have h' := congrArg (fun d : SchreierDeckGroup G H => d.hom.hom (1 : G ⧸ H)) h
  dsimp [SchreierAction] at h'
  rw [quotientDeckHom_apply_one, quotientDeckHom_apply_one] at h'
  have h'' := congrArg
    (fun x : (SchreierAction G H).V.obj => (x : G ⧸ H)) h'
  have h''' : q⁻¹ = r⁻¹ := h''
  exact inv_inj.mp h'''

lemma quotientDeckHom_surjective (G : Type u) [Group G] (H : Subgroup G)
    [H.Normal] [Fintype (G ⧸ H)] :
    Function.Surjective (quotientDeckHom G H) := by
  intro d
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective H (d.hom.hom (1 : G ⧸ H))
  refine ⟨(g⁻¹ : G ⧸ H), ?_⟩
  apply Aut.ext
  apply schreierActionHom_ext_of_one G H
  change (quotientDeckEndHom G H (g⁻¹ : G ⧸ H)).hom (1 : G ⧸ H) =
    d.hom.hom (1 : G ⧸ H)
  have hg' : ((g : G ⧸ H) : (SchreierAction G H).V.obj) =
      d.hom.hom (1 : G ⧸ H) := by
    exact congrArg (fun x : G ⧸ H => (x : (SchreierAction G H).V.obj)) hg
  have hg'' : (((g⁻¹ : G ⧸ H)⁻¹ : G ⧸ H) : (SchreierAction G H).V.obj) =
      d.hom.hom (1 : G ⧸ H) := by
    simpa only [inv_inv] using hg'
  simpa only [inv_inv] using
    (quotientDeckEndHom_apply_one G H (g⁻¹ : G ⧸ H)).trans hg''

/-- The deck group of a finite regular Schreier cover is its quotient group. -/
noncomputable def quotientDeckGroupEquiv (G : Type u) [Group G] (H : Subgroup G)
    [H.Normal] [Fintype (G ⧸ H)] :
    G ⧸ H ≃* SchreierDeckGroup G H :=
  MulEquiv.ofBijective (quotientDeckHom G H)
    ⟨quotientDeckHom_injective G H, quotientDeckHom_surjective G H⟩

/-- The same deck-group identification stated with Mathlib's finite-index class. -/
noncomputable def finiteIndexQuotientDeckGroupEquiv (G : Type u) [Group G]
    (H : Subgroup G) [H.Normal] [H.FiniteIndex] :
    letI : Fintype (G ⧸ H) := H.fintypeQuotientOfFiniteIndex
    G ⧸ H ≃* SchreierDeckGroup G H := by
  letI : Fintype (G ⧸ H) := H.fintypeQuotientOfFiniteIndex
  exact quotientDeckGroupEquiv G H

end GraphCoveringTheory
