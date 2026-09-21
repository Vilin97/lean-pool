/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.SimpleQuotient
import LeanPool.RegtsSevenster.RS.Classical.Deligne.FreeSummand
import LeanPool.RegtsSevenster.RS.Classical.Deligne.FreeModBiprod
import LeanPool.RegtsSevenster.RS.Classical.Deligne.MixShuffleLine
import LeanPool.RegtsSevenster.RS.Classical.Deligne.ModAbelian

/-!
# Free mixed modules over a simple algebra

Over a commutative algebra object of the ind-completion whose only
ideals are the zero subobject and the whole algebra, the free
modules on mixed sums of the unit and of an odd line are
semisimple of finite length.  Consequently subobjects, quotients
and subquotients of objects whose free module is a mixed sum again
have free modules that are mixed sums, and every epimorphism out of
a free mixed module has a section.

The development runs in three steps.

* The regular module is simple.  Submodules of the regular module
  are exactly the ideals of the algebra: the intertwining law of a
  module map `g` into the regular module says precisely that
  multiplication by the algebra against the image of `g` lands in
  that image, which is `RS.isIdeal_mk_hom`; simplicity of the
  algebra then leaves only the zero and the whole subobject, and
  `RS.mono_iff_hom`/`RS.epi_iff_hom` carry the conclusion back to
  the category of modules (`RS.simple_regularMod`).
* The free module on the odd line is simple.  Whiskering on the
  right by the line is invertible up to the rotation
  `RS.OddLine.rot` coming from the square of the line, so a
  submodule of the free module on the line becomes, after
  twisting, a submodule of the regular module
  (`RS.lineToRegular`); whiskering by the line reflects both
  vanishing and invertibility, so simplicity transfers
  (`RS.simple_freeMod_oddLine`).  The route taken is the direct
  one: no auto-equivalence of the category of modules is built,
  only the single twisting functor's action on objects and
  morphisms, and the coherence identity `RS.rot_act` saying that
  the rotation intertwines an action with its double twist.
* The free module on a mixed sum is a `RS.mixSum` of copies of the
  regular module and of the free module on the line
  (`RS.freeModMixIso`), by peeling summands with
  `RS.OddLine.mixSuccIso` and `RS.OddLine.mixLineSuccIso` and
  carrying them across with `RS.freeModBiprodIso`.

The payoff combines these with the engine of
`RS/Classical/Deligne/ModAbelian.lean`: `RS.exists_mixSum_iso_of_mono`
and `RS.exists_mixSum_iso_of_epi` give
`RS.exists_mix_of_mono_of_simple`, `RS.exists_mix_of_epi_of_simple`
and `RS.exists_mix_of_isSubquotient`, since tensoring in `Ind C` is
exact and so the free-module functor preserves monomorphisms and
epimorphisms.

A last section splits epimorphisms.  In any abelian category an
epimorphism out of a finite direct sum of simple objects has a
section (`RS.exists_section_idxSum`, from the binary step
`RS.exists_section_biprod`), so over a simple algebra every
epimorphism out of a free mixed module splits
(`RS.exists_section_freeMod_mix`), which supplies the section datum
of the local splitting statement without constructing it by hand.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v uE vE jE

/-! ## Splitting epimorphisms out of a sum of simple objects -/

section SplitEpi

variable {E : Type uE}

/-- **The inductive step for splitting an epimorphism**: an
epimorphism out of `X ⊞ T` with `X` simple splits as soon as every
epimorphism out of `T` splits.  Either the second summand already
covers the target — the cokernel of its restriction vanishes — and
the section comes from the hypothesis on `T`; or the simple summand
maps isomorphically onto that cokernel, which exhibits the target as
the cokernel together with the image of the second summand, and the
two halves of the section are assembled by addition. -/
theorem exists_section_biprod [Category.{vE} E] [Abelian E]
    {X T N : E} [Simple X]
    (f : (X ⊞ T) ⟶ N) (hf : Epi f)
    (hT : ∀ {N' : E} (g : T ⟶ N'), Epi g →
      ∃ s : N' ⟶ T, s ≫ g = 𝟙 N') :
    ∃ s : N ⟶ (X ⊞ T), s ≫ f = 𝟙 N := by
  haveI := hf
  have hg : biprod.inr ≫ f ≫ cokernel.π (biprod.inr ≫ f) = 0 := by
    rw [← Category.assoc]
    exact cokernel.condition _
  have hfac : f ≫ cokernel.π (biprod.inr ≫ f) =
      biprod.fst ≫
        (biprod.inl ≫ f ≫ cokernel.π (biprod.inr ≫ f)) := by
    refine biprod.hom_ext' _ _ ?_ ?_ <;> simp [hg]
  haveI : Epi (biprod.inl ≫ f ≫ cokernel.π (biprod.inr ≫ f)) := by
    have h1 : Epi (f ≫ cokernel.π (biprod.inr ≫ f)) := epi_comp _ _
    rw [hfac] at h1
    exact epi_of_epi (biprod.fst : (X ⊞ T) ⟶ X)
      (biprod.inl ≫ f ≫ cokernel.π (biprod.inr ≫ f))
  by_cases hu : biprod.inl ≫ f ≫ cokernel.π (biprod.inr ≫ f) = 0
  · have hc0 : cokernel.π (biprod.inr ≫ f) = 0 := by
      refine zero_of_epi_comp f ?_
      rw [hfac, hu, Limits.comp_zero]
    haveI : Epi (biprod.inr ≫ f) := by
      rw [Preadditive.epi_iff_cancel_zero]
      intro R w hw
      rw [← cokernel.π_desc (biprod.inr ≫ f) w hw, hc0,
        Limits.zero_comp]
    obtain ⟨s₀, hs₀⟩ := hT (biprod.inr ≫ f) inferInstance
    refine ⟨s₀ ≫ biprod.inr, ?_⟩
    rw [Category.assoc]
    exact hs₀
  · haveI : IsIso (biprod.inl ≫ f ≫ cokernel.π (biprod.inr ≫ f)) :=
      isIso_of_epi_of_nonzero hu
    have hs : (inv (biprod.inl ≫ f ≫ cokernel.π (biprod.inr ≫ f))
          ≫ (biprod.inl ≫ f)) ≫ cokernel.π (biprod.inr ≫ f) =
        𝟙 (cokernel (biprod.inr ≫ f)) := by
      rw [Category.assoc, Category.assoc]
      exact IsIso.inv_hom_id _
    obtain ⟨t, ht⟩ :=
      hT (Abelian.factorThruImage (biprod.inr ≫ f)) inferInstance
    have hti : t ≫ (biprod.inr ≫ f) =
        kernel.ι (cokernel.π (biprod.inr ≫ f)) :=
      (whisker_eq t
          (Abelian.image.fac (biprod.inr ≫ f)).symm).trans
        ((Category.assoc _ _ _).symm.trans
          ((eq_whisker ht _).trans (Category.id_comp _)))
    refine ⟨sectionRetraction _ _ hs ≫ t ≫ biprod.inr +
      cokernel.π (biprod.inr ≫ f) ≫
        inv (biprod.inl ≫ f ≫ cokernel.π (biprod.inr ≫ f)) ≫
          biprod.inl, ?_⟩
    rw [Preadditive.add_comp]
    simp only [Category.assoc]
    rw [hti, sectionRetraction_ι]
    abel

/-- **An epimorphism out of a finite direct sum of simple objects
splits.** -/
theorem exists_section_idxSum [Category.{vE} E] [Abelian E]
    {J : Type jE} (S : J → E) :
    ∀ (L : List J), (∀ j ∈ L, Simple (S j)) →
      ∀ {N : E} (f : idxSum S L ⟶ N), Epi f →
        ∃ s : N ⟶ idxSum S L, s ≫ f = 𝟙 N := by
  intro L
  induction L with
  | nil =>
      intro _ N f hf
      haveI := hf
      have h0 : f = 0 := (isZero_zero E).eq_zero_of_src f
      have h1 : (𝟙 N : N ⟶ N) = 0 := by
        refine (cancel_epi f).1 ?_
        rw [Category.comp_id, h0, Limits.zero_comp]
      exact ⟨0, by rw [Limits.zero_comp, h1]⟩
  | cons i L₀ ih =>
      intro hS N f hf
      haveI : Simple (S i) := hS i (List.mem_cons_self ..)
      exact exists_section_biprod
        (X := S i) (T := idxSum S L₀) (N := N) f hf
        (fun g hg =>
          ih (fun j hj => hS j (List.mem_cons_of_mem i hj)) g hg)

/-- **An epimorphism out of a sum of copies of two simple objects
splits.** -/
theorem exists_section_mixSum [Category.{vE} E] [Abelian E]
    (X Y : E) [Simple X] [Simple Y]
    (p q : ℕ) {N : E} (f : mixSum X Y p q ⟶ N) (hf : Epi f) :
    ∃ s : N ⟶ mixSum X Y p q, s ≫ f = 𝟙 N :=
  exists_section_idxSum (id : E → E)
    (List.replicate p X ++ List.replicate q Y)
    (simple_of_mem_mix X Y p q) f hf

end SplitEpi

variable {C : Type v}

section Regular

/-- **A module map is an isomorphism exactly when its underlying
morphism is.** -/
theorem isIso_iff_hom
    [SmallCategory C] [MonoidalCategory C] [Abelian C] [RigidCategory C]
    [MonoidalPreadditive C] (𝔹 : Ind C) [MonObj 𝔹]
    {M N : Mod (Ind C) 𝔹} (f : M ⟶ N) :
    IsIso f ↔ IsIso f.hom := by
  constructor
  · intro h
    haveI := h
    exact inferInstanceAs (IsIso ((Mod.forget (D := Ind C) 𝔹).map f))
  · intro h
    haveI := h
    haveI : Mono f := (mono_iff_hom 𝔹 f).2 inferInstance
    haveI : Epi f := (epi_iff_hom 𝔹 f).2 inferInstance
    exact isIso_of_mono_of_epi f

/-- **A submodule of the regular module is an ideal.**  The
intertwining law of a module map into the regular module says
exactly that multiplication by the algebra lands in the
subobject. -/
theorem isIdeal_mk_hom
    [SmallCategory C] [MonoidalCategory C] (𝔹 : Ind C) [MonObj 𝔹]
    {M : Mod (Ind C) 𝔹} (g : M ⟶ regularMod 𝔹)
    [Mono g.hom] : IsIdeal 𝔹 (Subobject.mk g.hom) := by
  have hlaw : actLeft 𝔹 M.X ≫ g.hom = (𝔹 ◁ g.hom) ≫ μ[𝔹] :=
    g.isModHom.smul_hom
  have harrow : (Subobject.mk g.hom).arrow =
      (Subobject.underlyingIso g.hom).hom ≫ g.hom :=
    (Iso.inv_comp_eq _).1 (Subobject.underlyingIso_arrow _)
  show (Subobject.mk g.hom).Factors
    ((𝔹 ◁ (Subobject.mk g.hom).arrow) ≫ μ[𝔹])
  refine factors_of_comm
    ((𝔹 ◁ (Subobject.underlyingIso g.hom).hom) ≫
      actLeft 𝔹 M.X ≫ (Subobject.underlyingIso g.hom).inv) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (whisker_eq _ (Category.assoc _ _ _)) ?_
  refine Eq.trans (whisker_eq _ (whisker_eq _
    (Subobject.underlyingIso_arrow g.hom))) ?_
  refine Eq.trans (whisker_eq _ hlaw) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker
    (MonoidalCategory.whiskerLeft_comp 𝔹 _ _).symm _) ?_
  exact congrArg (fun t => (𝔹 ◁ t) ≫ μ[𝔹]) harrow.symm

/-- **The regular module over a simple algebra is simple**: its
submodules are exactly the ideals of the algebra. -/
theorem simple_regularMod
    [SmallCategory C] [MonoidalCategory C] [Abelian C] [RigidCategory C]
    [MonoidalPreadditive C] (𝔹 : Ind C) [MonObj 𝔹]
    (hsimple : ∀ I : Subobject 𝔹, IsIdeal 𝔹 I → I = ⊥ ∨ I = ⊤)
    (hne : η[𝔹] ≠ 0) : Simple (regularMod 𝔹) := by
  constructor
  intro M g hg
  haveI := hg
  haveI hmono : Mono g.hom := (mono_iff_hom 𝔹 g).1 hg
  constructor
  · intro hiso h0
    haveI := hiso
    refine hne ?_
    have h1 : (𝟙 (regularMod 𝔹) : regularMod 𝔹 ⟶ regularMod 𝔹) = 0 :=
      (IsIso.inv_hom_id g).symm.trans
        ((congrArg (fun t => inv g ≫ t) h0).trans Limits.comp_zero)
    have h2 : (𝟙 𝔹 : 𝔹 ⟶ 𝔹) = 0 := congrArg Mod.Hom.hom h1
    exact (Category.comp_id η[𝔹]).symm.trans
      ((congrArg (fun t => η[𝔹] ≫ t) h2).trans Limits.comp_zero)
  · intro hg0
    have hghom : g.hom ≠ 0 := fun h => hg0 (Mod.hom_ext _ _ h)
    rcases hsimple _ (isIdeal_mk_hom 𝔹 g) with h | h
    · exact absurd (Subobject.mk_eq_bot_iff_zero.1 h) hghom
    · haveI : IsIso g.hom := (Subobject.isIso_iff_mk_eq_top g.hom).2 h
      exact (isIso_iff_hom 𝔹 g).2 inferInstance

end Regular

/-! ## Rotating by the odd line -/

section Rotation

/-- **The rotation is compatible with whiskering on the left**: a
purely structural identity, once the square of the line is moved to
a common position on both sides. -/
@[reassoc]
theorem whiskerLeft_rot
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C] [Abelian C]
    (L : OddLine (Ind C))
    (A X : Ind C) :
    (α_ A (X ⊗ L.obj) L.obj).inv ≫ ((α_ A X L.obj).inv ▷ L.obj) ≫
        (L.rot (A ⊗ X)).hom = A ◁ (L.rot X).hom := by
  have hu : (α_ A (X ⊗ L.obj) L.obj).inv ≫
        ((α_ A X L.obj).inv ▷ L.obj) ≫
        (α_ (A ⊗ X) L.obj L.obj).hom ≫
        (α_ A X (L.obj ⊗ L.obj)).hom =
      A ◁ (α_ X L.obj L.obj).hom := by
    monoidal
  have hv : (α_ A X (𝟙_ (Ind C))).hom ≫ (A ◁ (ρ_ X).hom) =
      (ρ_ (A ⊗ X)).hom := by
    monoidal
  rw [OddLine.rot_hom, OddLine.rot_hom]
  simp only [MonoidalCategory.whiskerLeft_comp]
  rw [← hv, associator_naturality_right_assoc, reassoc_of% hu]

/-- **The rotation intertwines an action with its double twist by
the line.** -/
theorem rot_act
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C] [Abelian C]
    (L : OddLine (Ind C))
    {A X : Ind C} (act : A ⊗ X ⟶ X) :
    ((α_ A (X ⊗ L.obj) L.obj).inv ≫
        (((α_ A X L.obj).inv ≫ act ▷ L.obj) ▷ L.obj)) ≫
      (L.rot X).hom = (A ◁ (L.rot X).hom) ≫ act := by
  rw [MonoidalCategory.comp_whiskerRight]
  simp only [Category.assoc]
  rw [L.whiskerRight_rot act, whiskerLeft_rot_assoc]

/-- **Whiskering by the line carries an intertwiner to an
intertwiner** for the twisted actions. -/
theorem whiskerRight_act
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C] [Abelian C]
    (L : OddLine (Ind C))
    {A X Y : Ind C} (actX : A ⊗ X ⟶ X)
    (actY : A ⊗ Y ⟶ Y) (f : X ⟶ Y)
    (hf : actX ≫ f = (A ◁ f) ≫ actY) :
    ((α_ A X L.obj).inv ≫ actX ▷ L.obj) ≫ (f ▷ L.obj) =
      (A ◁ (f ▷ L.obj)) ≫
        ((α_ A Y L.obj).inv ≫ actY ▷ L.obj) := by
  rw [Category.assoc, ← MonoidalCategory.comp_whiskerRight, hf,
    MonoidalCategory.comp_whiskerRight,
    associator_inv_naturality_middle_assoc]

/-- **Whiskering by the line reflects isomorphisms.** -/
theorem isIso_of_whiskerRight
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C] [Abelian C]
    (L : OddLine (Ind C))
    {X Y : Ind C} (f : X ⟶ Y)
    (h : IsIso (f ▷ L.obj)) : IsIso f := by
  haveI := h
  haveI : IsIso ((f ▷ L.obj) ▷ L.obj) :=
    inferInstanceAs (IsIso ((tensorRight L.obj).map (f ▷ L.obj)))
  have hf : f = (L.rot X).inv ≫ ((f ▷ L.obj) ▷ L.obj) ≫
      (L.rot Y).hom := (L.rot_whiskerRight f).symm
  rw [hf]
  infer_instance

end Rotation

/-! ## The free module on the odd line -/

section OddLineFree

/-- A module twisted on the right by the odd line. -/
noncomputable def modLine
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C] [Abelian C]
    (𝔹 : Ind C) [MonObj 𝔹] (L : OddLine (Ind C))
    (M : Mod (Ind C) 𝔹) : Mod (Ind C) 𝔹 :=
  letI := tensorRightModObj 𝔹 M.X L.obj
  ⟨M.X ⊗ L.obj⟩

@[simp] theorem modLine_X
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C] [Abelian C]
    (𝔹 : Ind C) [MonObj 𝔹] (L : OddLine (Ind C))
    (M : Mod (Ind C) 𝔹) :
    (modLine 𝔹 L M).X = M.X ⊗ L.obj := rfl

/-- **A submodule of the free module on the line becomes a
submodule of the regular module** after twisting by the line: the
twist of the free module on the line is the regular module, by the
rotation. -/
noncomputable def lineToRegular
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C] [Abelian C]
    (𝔹 : Ind C) [MonObj 𝔹] (L : OddLine (Ind C))
    {M : Mod (Ind C) 𝔹}
    (g : M ⟶ freeMod 𝔹 L.obj) : modLine 𝔹 L M ⟶ regularMod 𝔹 :=
  Mod.Hom.mk' ((g.hom ▷ L.obj) ≫ (L.rot 𝔹).hom) (by
    have hf : actLeft 𝔹 M.X ≫ g.hom =
        (𝔹 ◁ g.hom) ≫ ((α_ 𝔹 𝔹 L.obj).inv ≫ μ[𝔹] ▷ L.obj) :=
      g.isModHom.smul_hom
    have h1 := whiskerRight_act L (actLeft 𝔹 M.X)
      ((α_ 𝔹 𝔹 L.obj).inv ≫ μ[𝔹] ▷ L.obj) g.hom hf
    have h2 := rot_act L (A := 𝔹) (X := 𝔹) μ[𝔹]
    show ((α_ 𝔹 M.X L.obj).inv ≫ actLeft 𝔹 M.X ▷ L.obj) ≫
        ((g.hom ▷ L.obj) ≫ (L.rot 𝔹).hom) =
      (𝔹 ◁ ((g.hom ▷ L.obj) ≫ (L.rot 𝔹).hom)) ≫ μ[𝔹]
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker h1 _) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (whisker_eq _ h2) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    exact eq_whisker
      (MonoidalCategory.whiskerLeft_comp 𝔹 _ _).symm _)

/-- The twisted map vanishes exactly when the original does. -/
theorem lineToRegular_eq_zero_iff
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C] [Abelian C]
    [MonoidalPreadditive C] (𝔹 : Ind C) [MonObj 𝔹] (L : OddLine (Ind C))
    {M : Mod (Ind C) 𝔹}
    (g : M ⟶ freeMod 𝔹 L.obj) :
    lineToRegular 𝔹 L g = 0 ↔ g = 0 := by
  constructor
  · intro h
    have h1 : (g.hom ▷ L.obj) ≫ (L.rot 𝔹).hom = 0 :=
      congrArg Mod.Hom.hom h
    have h2 : g.hom ▷ L.obj = 0 :=
      (Iso.cancel_iso_hom_right _ _ (L.rot 𝔹)).mp
        (h1.trans Limits.zero_comp.symm)
    exact Mod.hom_ext _ _ (L.eq_zero_of_whiskerRight g.hom h2)
  · intro h
    refine Mod.hom_ext _ _ ?_
    show (g.hom ▷ L.obj) ≫ (L.rot 𝔹).hom = 0
    rw [show g.hom = 0 from congrArg Mod.Hom.hom h,
      MonoidalPreadditive.zero_whiskerRight, Limits.zero_comp]

/-- **The free module on the odd line is nonzero** as soon as the
unit of the algebra is: the rotation identifies its double twist
with the algebra. -/
theorem id_freeMod_oddLine_ne_zero
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C] [Abelian C]
    [MonoidalPreadditive C] (𝔹 : Ind C) [MonObj 𝔹] (L : OddLine (Ind C))
    (hne : η[𝔹] ≠ 0) :
    (𝟙 (freeMod 𝔹 L.obj) : freeMod 𝔹 L.obj ⟶ freeMod 𝔹 L.obj)
      ≠ 0 := by
  intro h
  have h1 : (𝟙 (𝔹 ⊗ L.obj) : 𝔹 ⊗ L.obj ⟶ 𝔹 ⊗ L.obj) = 0 :=
    congrArg Mod.Hom.hom h
  have h2 : (𝟙 ((𝔹 ⊗ L.obj) ⊗ L.obj) :
      (𝔹 ⊗ L.obj) ⊗ L.obj ⟶ (𝔹 ⊗ L.obj) ⊗ L.obj) = 0 := by
    rw [← MonoidalCategory.id_whiskerRight (𝔹 ⊗ L.obj) L.obj, h1,
      MonoidalPreadditive.zero_whiskerRight]
  have hz : IsZero 𝔹 :=
    IsZero.of_iso ((IsZero.iff_id_eq_zero _).2 h2) (L.rot 𝔹).symm
  exact hne (hz.eq_zero_of_tgt _)

/-- **The free module on the odd line over a simple algebra is
simple.**  Twisting by the line carries its submodules to
submodules of the regular module, and whiskering by the line
reflects both vanishing and invertibility. -/
theorem simple_freeMod_oddLine
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C] [Abelian C]
    [RigidCategory C] [MonoidalPreadditive C] (𝔹 : Ind C) [MonObj 𝔹]
    (L : OddLine (Ind C))
    (hsimple : ∀ I : Subobject 𝔹, IsIdeal 𝔹 I → I = ⊥ ∨ I = ⊤)
    (hne : η[𝔹] ≠ 0) : Simple (freeMod 𝔹 L.obj) := by
  haveI := simple_regularMod 𝔹 hsimple hne
  constructor
  intro M g hg
  haveI := hg
  haveI hgm : Mono g.hom := (mono_iff_hom 𝔹 g).1 hg
  haveI hwm : Mono (g.hom ▷ L.obj) :=
    inferInstanceAs (Mono ((tensorRight L.obj).map g.hom))
  haveI hhm : Mono (lineToRegular 𝔹 L g) := by
    refine mono_of_mono_hom _ ?_
    show Mono ((g.hom ▷ L.obj) ≫ (L.rot 𝔹).hom)
    infer_instance
  constructor
  · intro hiso h0
    haveI := hiso
    refine id_freeMod_oddLine_ne_zero 𝔹 L hne ?_
    exact (IsIso.inv_hom_id g).symm.trans
      ((congrArg (fun t => inv g ≫ t) h0).trans Limits.comp_zero)
  · intro h0
    haveI : IsIso (lineToRegular 𝔹 L g) :=
      isIso_of_mono_of_nonzero
        (fun h => h0 ((lineToRegular_eq_zero_iff 𝔹 L g).1 h))
    haveI : IsIso ((g.hom ▷ L.obj) ≫ (L.rot 𝔹).hom) :=
      (isIso_iff_hom 𝔹 (lineToRegular 𝔹 L g)).1 inferInstance
    haveI : IsIso (g.hom ▷ L.obj) :=
      IsIso.of_isIso_comp_right _ (L.rot 𝔹).hom
    exact (isIso_iff_hom 𝔹 g).2
      (isIso_of_whiskerRight L g.hom inferInstance)

end OddLineFree

/-! ## The free module on a mixed sum -/

section MixedFree

/-- A module whose carrier vanishes vanishes. -/
theorem isZero_of_isZero_X [SmallCategory C] [MonoidalCategory C] [Abelian C]
    [MonoidalPreadditive C] (𝔹 : Ind C) [MonObj 𝔹]
    {M : Mod (Ind C) 𝔹} (h : IsZero M.X) :
    IsZero M := by
  rw [IsZero.iff_id_eq_zero]
  exact Mod.hom_ext _ _ ((IsZero.iff_id_eq_zero M.X).1 h)

/-- **The free module on a mixed sum is a mixed sum of copies of
the regular module and of the free module on the odd line.**  The
free-module functor carries the peeling isomorphisms of the mixed
sum to biproduct decompositions of the module. -/
noncomputable def freeModMixIso
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C] [Abelian C]
    [RigidCategory C] [MonoidalPreadditive C] (𝔹 : Ind C) [MonObj 𝔹]
    (L : OddLine (Ind C)) : ∀ p q : ℕ,
    freeMod 𝔹 (L.mix p q) ≅
      mixSum (regularMod 𝔹) (freeMod 𝔹 L.obj) p q
  | 0, 0 =>
      IsZero.iso
        (isZero_of_isZero_X 𝔹 (freeModZeroIso 𝔹 L.isZero_mix_zero))
        (isZero_zero (Mod (Ind C) 𝔹))
  | 0, q + 1 =>
      freeModMapIso 𝔹 (L.mixLineSuccIso 0 q) ≪≫
        freeModBiprodIso 𝔹 L.obj (L.mix 0 q) ≪≫
        modBiprodMapIso 𝔹 _ _ (Iso.refl (freeMod 𝔹 L.obj))
          (freeModMixIso 𝔹 L 0 q) ≪≫
        biprod.uniqueUpToIso _ _ (modBinaryBiconeIsBilimit 𝔹 _ _)
  | p + 1, q =>
      freeModMapIso 𝔹 (L.mixSuccIso p q) ≪≫
        freeModBiprodIso 𝔹 (𝟙_ (Ind C)) (L.mix p q) ≪≫
        modBiprodMapIso 𝔹 _ _ (freeModUnitIso 𝔹)
          (freeModMixIso 𝔹 L p q) ≪≫
        biprod.uniqueUpToIso _ _ (modBinaryBiconeIsBilimit 𝔹 _ _)

end MixedFree

/-! ## Subquotients of a free mixed module -/

section Payoff

/-- **The free-module functor preserves monomorphisms**: tensoring
in the ind-completion is exact. -/
theorem mono_freeModMap
    [SmallCategory C] [MonoidalCategory C] [Abelian C] [RigidCategory C]
    [MonoidalPreadditive C] (𝔹 : Ind C) [MonObj 𝔹]
    {V W : Ind C} (f : V ⟶ W) (hf : Mono f) :
    Mono (freeModMap 𝔹 f) := by
  haveI := hf
  refine mono_of_mono_hom _ ?_
  show Mono (𝔹 ◁ f)
  exact inferInstanceAs (Mono ((tensorLeft 𝔹).map f))

/-- **The free-module functor preserves epimorphisms.** -/
theorem epi_freeModMap
    [SmallCategory C] [MonoidalCategory C] [Abelian C] [RigidCategory C]
    [MonoidalPreadditive C] (𝔹 : Ind C) [MonObj 𝔹]
    {V W : Ind C} (f : V ⟶ W) (hf : Epi f) :
    Epi (freeModMap 𝔹 f) := by
  haveI := hf
  refine epi_of_epi_hom _ ?_
  show Epi (𝔹 ◁ f)
  exact inferInstanceAs (Epi ((tensorLeft 𝔹).map f))

/-- **A subobject of an object with free mixed module has a free
mixed module.** -/
theorem exists_mix_of_mono_of_simple
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C] [Abelian C]
    [RigidCategory C] [MonoidalPreadditive C] (𝔹 : Ind C) [MonObj 𝔹]
    (L : OddLine (Ind C))
    (hsimple : ∀ I : Subobject 𝔹, IsIdeal 𝔹 I → I = ⊥ ∨ I = ⊤)
    (hne : η[𝔹] ≠ 0) {Y W : Ind C} (f : Y ⟶ W) (hf : Mono f)
    {p q : ℕ} (e : freeMod 𝔹 W ≅ freeMod 𝔹 (L.mix p q)) :
    ∃ p' q' : ℕ,
      Nonempty (freeMod 𝔹 Y ≅ freeMod 𝔹 (L.mix p' q')) := by
  haveI := simple_regularMod 𝔹 hsimple hne
  haveI := simple_freeMod_oddLine 𝔹 L hsimple hne
  haveI := mono_freeModMap 𝔹 f hf
  obtain ⟨p', q', -, -, ⟨w⟩⟩ :=
    exists_mixSum_iso_of_mono (regularMod 𝔹) (freeMod 𝔹 L.obj) p q
      (freeModMap 𝔹 f ≫ e.hom ≫ (freeModMixIso 𝔹 L p q).hom)
      (mono_comp _ _)
  exact ⟨p', q', ⟨w ≪≫ (freeModMixIso 𝔹 L p' q').symm⟩⟩

/-- **A quotient of an object with free mixed module has a free
mixed module.** -/
theorem exists_mix_of_epi_of_simple
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C] [Abelian C]
    [RigidCategory C] [MonoidalPreadditive C] (𝔹 : Ind C) [MonObj 𝔹]
    (L : OddLine (Ind C))
    (hsimple : ∀ I : Subobject 𝔹, IsIdeal 𝔹 I → I = ⊥ ∨ I = ⊤)
    (hne : η[𝔹] ≠ 0) {Y W : Ind C} (f : W ⟶ Y) (hf : Epi f)
    {p q : ℕ} (e : freeMod 𝔹 W ≅ freeMod 𝔹 (L.mix p q)) :
    ∃ p' q' : ℕ,
      Nonempty (freeMod 𝔹 Y ≅ freeMod 𝔹 (L.mix p' q')) := by
  haveI := simple_regularMod 𝔹 hsimple hne
  haveI := simple_freeMod_oddLine 𝔹 L hsimple hne
  haveI := epi_freeModMap 𝔹 f hf
  obtain ⟨p', q', -, -, ⟨w⟩⟩ :=
    exists_mixSum_iso_of_epi (regularMod 𝔹) (freeMod 𝔹 L.obj) p q
      ((freeModMixIso 𝔹 L p q).inv ≫ e.inv ≫ freeModMap 𝔹 f)
      (epi_comp _ _)
  exact ⟨p', q', ⟨w ≪≫ (freeModMixIso 𝔹 L p' q').symm⟩⟩

/-- **A subquotient of an object with free mixed module has a free
mixed module.** -/
theorem exists_mix_of_isSubquotient
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C] [Abelian C]
    [RigidCategory C] [MonoidalPreadditive C] (𝔹 : Ind C) [MonObj 𝔹]
    (L : OddLine (Ind C))
    (hsimple : ∀ I : Subobject 𝔹, IsIdeal 𝔹 I → I = ⊥ ∨ I = ⊤)
    (hne : η[𝔹] ≠ 0) {Y W : Ind C} (h : IsSubquotientOf Y W)
    {p q : ℕ} (e : freeMod 𝔹 W ≅ freeMod 𝔹 (L.mix p q)) :
    ∃ p' q' : ℕ,
      Nonempty (freeMod 𝔹 Y ≅ freeMod 𝔹 (L.mix p' q')) := by
  obtain ⟨S, i, r, hi, hr⟩ := h
  obtain ⟨p₁, q₁, ⟨e₁⟩⟩ :=
    exists_mix_of_mono_of_simple 𝔹 L hsimple hne i hi e
  exact exists_mix_of_epi_of_simple 𝔹 L hsimple hne r hr e₁

/-- **Every epimorphism out of a free mixed module splits.**  Over
a simple algebra a free mixed module is a finite direct sum of
copies of two simple modules, and an epimorphism out of such a sum
has a section. -/
theorem exists_section_freeMod_mix
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C] [Abelian C]
    [RigidCategory C] [MonoidalPreadditive C] (𝔹 : Ind C) [MonObj 𝔹]
    (L : OddLine (Ind C))
    (hsimple : ∀ I : Subobject 𝔹, IsIdeal 𝔹 I → I = ⊥ ∨ I = ⊤)
    (hne : η[𝔹] ≠ 0) (p q : ℕ) {N : Mod (Ind C) 𝔹}
    (f : freeMod 𝔹 (L.mix p q) ⟶ N) (hf : Epi f) :
    ∃ s : N ⟶ freeMod 𝔹 (L.mix p q), s ≫ f = 𝟙 N := by
  haveI := simple_regularMod 𝔹 hsimple hne
  haveI := simple_freeMod_oddLine 𝔹 L hsimple hne
  haveI := hf
  obtain ⟨s₀, hs₀⟩ :=
    exists_section_mixSum (regularMod 𝔹) (freeMod 𝔹 L.obj) p q
      ((freeModMixIso 𝔹 L p q).inv ≫ f) (epi_comp _ _)
  refine ⟨s₀ ≫ (freeModMixIso 𝔹 L p q).inv, ?_⟩
  rw [Category.assoc]
  exact hs₀

/-- **A morphism whose source has a free mixed module has a
module-level section as soon as its free module is an
epimorphism.**  This is the section datum of the local splitting
statement, supplied by semisimplicity rather than by hand. -/
theorem exists_section_of_simple
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C] [Abelian C]
    [RigidCategory C] [MonoidalPreadditive C] (𝔹 : Ind C) [MonObj 𝔹]
    (L : OddLine (Ind C))
    (hsimple : ∀ I : Subobject 𝔹, IsIdeal 𝔹 I → I = ⊥ ∨ I = ⊤)
    (hne : η[𝔹] ≠ 0) {V W : Ind C} (g : V ⟶ W)
    (hV : ∃ p q : ℕ,
      Nonempty (freeMod 𝔹 V ≅ freeMod 𝔹 (L.mix p q)))
    (hepi : Epi (freeModMap 𝔹 g)) :
    ∃ s : freeMod 𝔹 W ⟶ freeMod 𝔹 V,
      s ≫ freeModMap 𝔹 g = 𝟙 (freeMod 𝔹 W) := by
  haveI := hepi
  obtain ⟨p, q, ⟨e⟩⟩ := hV
  obtain ⟨s₀, hs₀⟩ :=
    exists_section_freeMod_mix 𝔹 L hsimple hne p q
      (e.inv ≫ freeModMap 𝔹 g) (epi_comp _ _)
  refine ⟨s₀ ≫ e.inv, ?_⟩
  rw [Category.assoc]
  exact hs₀

end Payoff

end RS
