/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.GammaCountable
public import LeanPool.RegtsSevenster.RS.Classical.Deligne.IndSchurKilled

/-!
# ℂ-linearity of the embedding `C ⥤ Ind C`

For an *arbitrary* pair of ℂ-linear structures on `C` and on `Ind C`
the embedding `RS.indOf` need not be ℂ-linear: two ring maps
`ℂ → End (𝟙_ (Ind C))` can differ by a field automorphism of ℂ, and
nothing ties the structure upstairs to the one downstairs.  That is
why `RS.IndOfLinear` is carried as a hypothesis in
`RS.Classical.Deligne.GammaCountable`.

The structures this development actually installs are not arbitrary.
Both come from a single scalar unit `ψ : ℂ ≃+* End (𝟙_ C)`, by
`RS.linearOfScalarUnit ψ` downstairs and
`RS.linearOfScalarUnit (indScalarUnit ψ)` upstairs, and
`RS.indScalarUnit ψ` is by construction the transport of `ψ` along
the embedding and the unit comparison `RS.indOfUnitIso`
(`RS.indScalarUnit_apply`, which is a `rfl`).  For that pair the
scalar action on either side is conjugation of a unit endomorphism
through the left unitor, and the embedding is strong monoidal
(`RS.indOfMonoidal`), so it carries the one conjugate to the other:
this is `RS.indOf_map_scalarSmul`.

This file reads that transport in the language of the installed
module structures:

* `RS.indOf_linear` — `indOf.map (c • f) = c • indOf.map f` under the
  two `letI`-installed structures;
* `RS.indOfFunctorLinear` — the same, packaged as Mathlib's
  `CategoryTheory.Functor.Linear ℂ indOf`;
* `RS.indOfLinear_of_scalarUnit` — the same, in the shape
  `RS.IndOfLinear C` in which `RS.Classical.Deligne.GammaCountable`
  consumes it, so that the hypothesis is discharged for the scalar-unit
  structures.

The additive law is `RS.indOf_additive`; this module proves scalar
compatibility. No compatibility between `ψ`
and an ambient linear structure is asked, and no braiding is needed:
both actions are defined from the same `ψ`, and the proof uses only
the unitality of the strong monoidal structure of the embedding.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits

universe v

noncomputable section

/-! ## The scalar half, for the installed structures -/

section Installed

variable {C : Type v}

/-- **The embedding `C ⥤ Ind C` is ℂ-linear** for the two ℂ-linear
structures induced by a single scalar unit `ψ`: `RS.scalarSmul` is
what `•` means on both sides, and `RS.indOf_map_scalarSmul` transports
the one to the other. -/
theorem indOf_linear [SmallCategory C] [MonoidalCategory C] [Preadditive C]
    [HasFiniteColimits C] [MonoidalPreadditive C]
    (ψ : ℂ ≃+* End (𝟙_ C)) :
    letI := linearOfScalarUnit ψ
    letI := linearOfScalarUnit (indScalarUnit ψ)
    ∀ {X Y : C} (c : ℂ) (f : X ⟶ Y),
      (indOf : C ⥤ Ind C).map (c • f) =
        c • (indOf : C ⥤ Ind C).map f := by
  let := linearOfScalarUnit ψ
  let := linearOfScalarUnit (indScalarUnit ψ)
  intro X Y c f
  exact indOf_map_scalarSmul ψ c f

/-- `RS.indOf_linear`, packaged as Mathlib's linearity class for a
functor. -/
theorem indOfFunctorLinear
    [SmallCategory C] [MonoidalCategory C] [Preadditive C]
    [HasFiniteColimits C] [MonoidalPreadditive C]
    (ψ : ℂ ≃+* End (𝟙_ C)) :
    letI := linearOfScalarUnit ψ
    letI := linearOfScalarUnit (indScalarUnit ψ)
    Functor.Linear ℂ (indOf : C ⥤ Ind C) := by
  let := linearOfScalarUnit ψ
  let := linearOfScalarUnit (indScalarUnit ψ)
  exact ⟨fun f c => indOf_map_scalarSmul ψ c f⟩

end Installed

/-! ## Discharging the hypothesis of the countability lane -/

section Hypothesis

variable {C : Type v}

/-- **The ℂ-linearity hypothesis of
`RS.Classical.Deligne.GammaCountable` holds for the scalar-unit
structures**: `RS.IndOfLinear C` is exactly `RS.indOf_linear`, read at
the two structures induced by `ψ`. -/
theorem indOfLinear_of_scalarUnit
    [SmallCategory C] [MonoidalCategory C] [Abelian C]
    [MonoidalPreadditive C]
    (ψ : ℂ ≃+* End (𝟙_ C)) :
    letI := linearOfScalarUnit ψ
    letI := linearOfScalarUnit (indScalarUnit ψ)
    IndOfLinear C := by
  let := linearOfScalarUnit ψ
  let := linearOfScalarUnit (indScalarUnit ψ)
  exact fun _ _ c f => indOf_map_scalarSmul ψ c f

end Hypothesis

/-! ## Acceptance -/

section Acceptance

variable {C : Type v}

/- The ℂ-linear full faithfulness of the embedding, which
`RS.Classical.Deligne.GammaCountable` builds from the hypothesis, is
therefore available outright for the scalar-unit structures. -/
example
    [SmallCategory C] [MonoidalCategory C] [Abelian C]
    [MonoidalPreadditive C]
    (ψ : ℂ ≃+* End (𝟙_ C)) (X Y : C) :
    letI := linearOfScalarUnit ψ
    letI := linearOfScalarUnit (indScalarUnit ψ)
    (X ⟶ Y) ≃ₗ[ℂ] ((indOf : C ⥤ Ind C).obj X ⟶ indOf.obj Y) :=
  letI := linearOfScalarUnit ψ
  letI := linearOfScalarUnit (indScalarUnit ψ)
  indOfHomEquiv (indOfLinear_of_scalarUnit ψ) X Y

end Acceptance

end

end RS
