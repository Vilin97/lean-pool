/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.IndSchur
public import LeanPool.RegtsSevenster.RS.Classical.Deligne.ScalarLinear

/-!
# The ind-embedding preserves simplicity

For a small abelian category `C` the embedding `RS.indOf : C ⥤ Ind C`
carries simple objects to simple objects, and hence the unit of
`Ind C` is simple as soon as the unit of `C` is.

The proof is short because the pin already supplies every input.

* the embedded objects form a separating family in `Ind C`
  (`CategoryTheory.Ind.isSeparating_range_yoneda`), the consequence
  of "every ind-object is a filtered colimit of embedded objects"
  that the argument actually needs;
* `RS.indOf` is fully faithful, and it preserves and reflects
  vanishing of morphisms (`RS.indOf_map_eq_zero_iff`);
* `RS.indOf` preserves finite colimits, hence epimorphisms;
* `Ind C` is abelian (`CategoryTheory.Ind` is abelian for `C`
  abelian and small), hence balanced.

Given a nonzero monomorphism `m : U ⟶ indOf.obj X`, separation
produces an object `W` of `C` and a map `g : indOf.obj W ⟶ U` with
`g ≫ m ≠ 0`.  Full faithfulness writes `g ≫ m = indOf.map f` for a
unique nonzero `f : W ⟶ X`, simplicity of `X` makes `f` an
epimorphism, and preservation of epimorphisms makes `g ≫ m` — and
therefore `m` — an epimorphism.  A monomorphism that is also an
epimorphism in an abelian category is an isomorphism.

## Main results

* `RS.simple_indOf` — the embedding preserves simplicity;
* `RS.simple_unit_ind` — the unit of `Ind C` is simple when the unit
  of `C` is;
* `RS.mono_unit_ind` — a nonzero algebra unit in `Ind C` is a
  monomorphism.
-/

@[expose] public section

namespace RS

open CategoryTheory Limits MonoidalCategory
open scoped MonObj

universe v

section Embedding

variable {C : Type v}

/-- **The ind-embedding preserves simplicity.**  If `X` is a simple
object of a small abelian category `C`, then `indOf.obj X` is a
simple object of `Ind C`. -/
theorem simple_indOf [SmallCategory C] [Abelian C]
    (X : C) [Simple X] : Simple (indOf.obj X) := by
  have := indOf_additive (C := C)
  constructor
  intro U m hm
  have := hm
  constructor
  · -- An isomorphism onto an embedded simple object is nonzero:
    -- otherwise the identity of `X` would be killed by a faithful
    -- functor.
    intro hiso hzero
    have := hiso
    have hid : 𝟙 (indOf.obj X) = 0 :=
      calc 𝟙 (indOf.obj X) = inv m ≫ m := (IsIso.inv_hom_id m).symm
        _ = inv m ≫ 0 := congrArg (fun t => inv m ≫ t) hzero
        _ = 0 := comp_zero
    refine id_nonzero X ?_
    refine (indOf (C := C)).map_injective ?_
    rw [CategoryTheory.Functor.map_id,
      CategoryTheory.Functor.map_zero, hid]
  · -- A nonzero monomorphism onto an embedded simple object is an
    -- isomorphism.
    intro hne
    have hex : ∃ (W : C) (g : indOf.obj W ⟶ U), g ≫ m ≠ 0 := by
      by_contra hcon
      refine hne (Ind.isSeparating_range_yoneda m 0 ?_)
      rintro _ ⟨W⟩ g
      have hg : g ≫ m = 0 := not_not.mp fun h => hcon ⟨W, g, h⟩
      simp [hg]
    obtain ⟨W, g, hgm⟩ := hex
    have hmap : indOf.map
        (Ind.yoneda.fullyFaithful.preimage (g ≫ m)) = g ≫ m :=
      Ind.yoneda.fullyFaithful.map_preimage (g ≫ m)
    have hfne : Ind.yoneda.fullyFaithful.preimage (g ≫ m) ≠ 0 := by
      intro h0
      exact hgm (((indOf_map_eq_zero_iff _).mpr h0).symm.trans hmap).symm
    have : Epi (Ind.yoneda.fullyFaithful.preimage (g ≫ m)) :=
      epi_of_nonzero_to_simple hfne
    have : Epi (g ≫ m) := by
      rw [← hmap]
      infer_instance
    have : Epi m := epi_of_epi g m
    exact isIso_of_mono_of_epi m

end Embedding

section Unit

variable {C : Type v}

/-- **The unit of `Ind C` is simple** whenever the unit of `C` is:
the unit of `Ind C` is the embedded unit (`RS.indOfUnitIso`), and
the embedding preserves simplicity. -/
theorem simple_unit_ind [SmallCategory C] [MonoidalCategory C] [Abelian C]
    (hsimple : Simple (𝟙_ C)) :
    Simple (𝟙_ (Ind C)) :=
  haveI := hsimple
  haveI := simple_indOf (𝟙_ C)
  Simple.of_iso (indOfUnitIso (C := C))

/-- **A nonzero algebra unit in `Ind C` is a monomorphism.**  This
is the faithful-flatness input to faithfulness of Deligne's fibre
functor: the unit of `Ind C` is simple, so any nonzero morphism out
of it is a monomorphism. -/
theorem mono_unit_ind [SmallCategory C] [MonoidalCategory C] [Abelian C]
    (hsimple : Simple (𝟙_ C)) (A : Ind C)
    [MonObj A] (hne : η[A] ≠ 0) : Mono η[A] :=
  haveI := simple_unit_ind hsimple
  mono_of_nonzero_from_simple hne

end Unit

end RS
