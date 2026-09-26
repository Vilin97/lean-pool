/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.GammaCountable

/-!
# Countable descent for the witnessing algebras

The dimension count of `RS.Classical.Deligne.GammaCountable` asks
each constituent algebra of the universal algebra of Deligne 2.11 to
be countably presented (`RS.CountablyPresented`): a countable
filtered colimit of embedded objects.  An algebra witnessing local
mixedness or a splitting is to be replaced by a countably presented
one, and this file assembles the two devices such a replacement
runs on: the countable tower generated inside an algebra by one
stage of its presentation, and the compactness of the objects that
carry the finite data to be pushed down that tower.

The tower.  Every ind-object is a filtered colimit of embedded
objects (`Ind.presentation`), the stage maps being `RS.presStage`,
and compactness of the embedded objects factors any map out of one
of them through a stage (`RS.exists_presStage_factor`).  Starting
from a stage of the presentation of an algebra, rung `n + 1` of the
tower is chosen above rung `n` and above a stage absorbing the
square of rung `n`.  The colimit `RS.stageSubalgebra` of the tower
is then countably presented
(`RS.countablyPresented_stageSubalgebra`), maps to the algebra
(`RS.stageSubalgebraHom`), contains the unit
(`RS.exists_unit_stageSubalgebra`) and is closed under
multiplication one rung at a time (`RS.stageRungMul_comp_hom`).

The tower inside the algebra.  The ind-completion of a small abelian
category is abelian, so each rung may be replaced by its image in the
algebra (`RS.stageImage`).  The rung maps are then monomorphisms, and
so is the map `RS.imageSubalgebraHom` of the resulting colimit
`RS.imageSubalgebra` into the algebra
(`RS.mono_imageSubalgebraHom`): a map out of an embedded object into
the colimit factors through a rung, and monomorphisms of ind-objects
are detected on the embedded objects
(`RS.mono_of_hom_indOf_injective`).  Countable presentation of the
image tower is `RS.countablyPresented_imageSubalgebra`, over the
hypothesis `RS.IndImageEmbedded` that images of embedded objects are
embedded.

The compactness.  The data to be pushed down is carried by mixed
sums of the unit and the odd line.  The unit is compact because it
is embedded; the odd line is compact because its square is the unit,
which makes tensoring with it an equivalence and so turns a map out
of it into a point of a translate — this is `RS.oddUntwist`, and it
gives both halves of the compactness formula,
`RS.exists_factor_of_sq_unit_hom_colimit` and
`RS.factor_eq_of_sq_unit_hom_colimit`.  Mixed sums are finite
biproducts of the two, and a finite family of stages of a filtered
diagram is dominated by a single stage, whence
`RS.exists_factor_of_mix_hom_colimit`.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

/-! ## Towers of embedded objects

An ℕ-shaped diagram is filtered and countable, so the colimit of a
tower of embedded objects is countably presented.  The index
category has to live in the ambient universe, whence the `AsSmall`
wrapper. -/

section Tower

/-- The index category of a tower: the natural numbers, transported
into the ambient universe. -/
abbrev Tower : Type v := AsSmall.{v} ℕ

instance countable_tower : Countable Tower.{v} :=
  inferInstanceAs (Countable (ULift ℕ))

variable {C : Type v}

/-- The diagram of a tower of objects of `C`. -/
noncomputable def towerDiagram [SmallCategory C]
    {Y : ℕ → C} (u : ∀ n, Y n ⟶ Y (n + 1)) :
    Tower.{v} ⥤ C :=
  AsSmall.down ⋙ Functor.ofSequence u

/-- **The colimit of a tower of embedded objects is countably
presented.**  This is the shape in which countable presentation is
produced below: no bookkeeping beyond the tower itself. -/
theorem countablyPresented_colimit_tower [SmallCategory C]
    {Y : ℕ → C}
    (u : ∀ n, Y n ⟶ Y (n + 1)) :
    CountablyPresented (colimit (towerDiagram u ⋙ indOf)) :=
  ⟨Tower.{v}, inferInstance, inferInstance, inferInstance,
    towerDiagram u, ⟨Iso.refl _⟩⟩

end Tower

/-! ## The stages of a presentation

Mathlib's `Ind.presentation` exhibits every ind-object as a filtered
colimit of embedded objects.  The maps of the stages into the
ind-object are `RS.presStage`, and compactness of the embedded
objects (`RS.exists_factor_of_hom_colimit`) factors any map out of an
embedded object through one of them. -/

section Presentation

variable {C : Type v}

/-- The diagram of embedded objects presenting an ind-object. -/
noncomputable abbrev presDiagram [SmallCategory C]
    (A : Ind C) : A.presentation.I ⥤ Ind C :=
  A.presentation.F ⋙ indOf

/-- The structural map of a stage of the chosen presentation into the
ind-object it presents. -/
noncomputable def presStage [SmallCategory C]
    (A : Ind C) (i : A.presentation.I) :
    indOf.obj (A.presentation.F.obj i) ⟶ A :=
  colimit.ι (presDiagram A) i ≫ (Ind.colimitPresentationCompYoneda A).hom

/-- The structural maps are compatible with the transition maps of
the presentation. -/
theorem presStage_naturality [SmallCategory C]
    (A : Ind C) {i j : A.presentation.I}
    (α : i ⟶ j) :
    indOf.map (A.presentation.F.map α) ≫ presStage A j = presStage A i := by
  rw [presStage, presStage, ← Category.assoc]
  exact eq_whisker (colimit.w (presDiagram A) α) _

/-- **A map out of an embedded object factors through a stage of the
presentation**: this is compactness of the embedded objects. -/
theorem exists_presStage_factor [SmallCategory C]
    (A : Ind C) {Y : C}
    (f : indOf.obj Y ⟶ A) :
    ∃ (i : A.presentation.I) (g : Y ⟶ A.presentation.F.obj i),
      indOf.map g ≫ presStage A i = f := by
  obtain ⟨i, g, hg⟩ := exists_factor_of_hom_colimit (presDiagram A) Y
    (f ≫ (Ind.colimitPresentationCompYoneda A).inv)
  refine ⟨i, Ind.yoneda.fullyFaithful.preimage g, ?_⟩
  have hp : indOf.map (Ind.yoneda.fullyFaithful.preimage g) = g :=
    Ind.yoneda.fullyFaithful.map_preimage g
  rw [hp, presStage, ← Category.assoc]
  refine (eq_whisker hg _).trans ?_
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- **A point of an ind-object factors through a stage.** -/
theorem exists_presStage_point [SmallCategory C]
    [MonoidalCategory C] (A : Ind C)
    (f : 𝟙_ (Ind C) ⟶ A) :
    ∃ (i : A.presentation.I) (e : 𝟙_ (Ind C) ⟶
      indOf.obj (A.presentation.F.obj i)), e ≫ presStage A i = f := by
  obtain ⟨i, g, hg⟩ := exists_factor_of_unit_hom_colimit (presDiagram A)
    (f ≫ (Ind.colimitPresentationCompYoneda A).inv)
  refine ⟨i, g, ?_⟩
  rw [presStage, ← Category.assoc]
  refine (eq_whisker hg _).trans ?_
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

end Presentation

/-! ## The subalgebra generated by a stage

Rung `n + 1` of the tower is chosen above rung `n` and above a stage
of the presentation absorbing the square of rung `n`.  The colimit of
the tower is therefore countably presented, maps to the algebra, and
is closed under multiplication one rung at a time. -/

section Generate

variable {C : Type v}

/-- The square of a stage of the presentation, multiplied into the
algebra. -/
noncomputable def stageMulToAlg
    [SmallCategory C] [MonoidalCategory C] (A : Ind C) [MonObj A]
    (i : A.presentation.I) :
    indOf.obj (A.presentation.F.obj i ⊗ A.presentation.F.obj i) ⟶ A :=
  (indOfTensorIso _ _).inv ≫ (presStage A i ⊗ₘ presStage A i) ≫ μ[A]

/-- A stage of the presentation absorbing the square of the given
stage. -/
noncomputable def mulStage
    [SmallCategory C] [MonoidalCategory C] (A : Ind C) [MonObj A]
    (i : A.presentation.I) : A.presentation.I :=
  (exists_presStage_factor A (stageMulToAlg A i)).choose

/-- The multiplication of a stage with itself, landing in the
absorbing stage. -/
noncomputable def mulStageMap
    [SmallCategory C] [MonoidalCategory C] (A : Ind C) [MonObj A]
    (i : A.presentation.I) :
    A.presentation.F.obj i ⊗ A.presentation.F.obj i ⟶
      A.presentation.F.obj (mulStage A i) :=
  (exists_presStage_factor A (stageMulToAlg A i)).choose_spec.choose

/-- The comparison of the embedding with the tensor product turns the
square of a stage into the product of its two structural maps. -/
theorem indOfTensorIso_stageMulToAlg
    [SmallCategory C] [MonoidalCategory C] (A : Ind C) [MonObj A]
    (i : A.presentation.I) :
    (indOfTensorIso (A.presentation.F.obj i)
        (A.presentation.F.obj i)).hom ≫ stageMulToAlg A i =
      (presStage A i ⊗ₘ presStage A i) ≫ μ[A] := by
  rw [stageMulToAlg, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

theorem mulStageMap_spec
    [SmallCategory C] [MonoidalCategory C] (A : Ind C) [MonObj A]
    (i : A.presentation.I) :
    indOf.map (mulStageMap A i) ≫ presStage A (mulStage A i) =
      stageMulToAlg A i :=
  (exists_presStage_factor A (stageMulToAlg A i)).choose_spec.choose_spec

/-- The next rung: a stage above the given one and above the stage
absorbing its square. -/
noncomputable def nextStage
    [SmallCategory C] [MonoidalCategory C] (A : Ind C) [MonObj A]
    (i : A.presentation.I) : A.presentation.I :=
  IsFiltered.max i (mulStage A i)

/-- The transition map of the tower, at the level of the index
category of the presentation. -/
noncomputable def stageStep
    [SmallCategory C] [MonoidalCategory C] (A : Ind C) [MonObj A]
    (i : A.presentation.I) : i ⟶ nextStage A i :=
  IsFiltered.leftToMax _ _

/-- The multiplication of a stage with itself, landing in the next
rung. -/
noncomputable def stageMul
    [SmallCategory C] [MonoidalCategory C] (A : Ind C) [MonObj A]
    (i : A.presentation.I) :
    A.presentation.F.obj i ⊗ A.presentation.F.obj i ⟶
      A.presentation.F.obj (nextStage A i) :=
  mulStageMap A i ≫
    A.presentation.F.map (IsFiltered.rightToMax i (mulStage A i))

theorem stageMul_spec
    [SmallCategory C] [MonoidalCategory C] (A : Ind C) [MonObj A]
    (i : A.presentation.I) :
    indOf.map (stageMul A i) ≫ presStage A (nextStage A i) =
      stageMulToAlg A i := by
  erw [stageMul, CategoryTheory.Functor.map_comp, Category.assoc,
    presStage_naturality, mulStageMap_spec]

/-- The stages of the generated tower. -/
noncomputable def towerIdx
    [SmallCategory C] [MonoidalCategory C] (A : Ind C) [MonObj A]
    (i₀ : A.presentation.I) : ℕ → A.presentation.I
  | 0 => i₀
  | n + 1 => nextStage A (towerIdx A i₀ n)

/-- The rungs of the generated tower, as objects of `C`. -/
@[reducible] noncomputable def towerObj
    [SmallCategory C] [MonoidalCategory C] (A : Ind C) [MonObj A]
    (i₀ : A.presentation.I)
    (n : ℕ) : C :=
  A.presentation.F.obj (towerIdx A i₀ n)

/-- The transition maps of the generated tower. -/
noncomputable def towerStep
    [SmallCategory C] [MonoidalCategory C] (A : Ind C) [MonObj A]
    (i₀ : A.presentation.I)
    (n : ℕ) :
    towerObj A i₀ n ⟶ towerObj A i₀ (n + 1) :=
  A.presentation.F.map (stageStep A (towerIdx A i₀ n))

/-- The tower as a diagram of ind-objects. -/
noncomputable def towerSeq
    [SmallCategory C] [MonoidalCategory C] (A : Ind C) [MonObj A]
    (i₀ : A.presentation.I) : ℕ ⥤ Ind C :=
  Functor.ofSequence (towerStep A i₀) ⋙ indOf

/-- The cocone of the tower under the algebra. -/
noncomputable def towerNatTrans
    [SmallCategory C] [MonoidalCategory C] (A : Ind C) [MonObj A]
    (i₀ : A.presentation.I) :
    towerSeq A i₀ ⟶ (Functor.const ℕ).obj A :=
  NatTrans.ofSequence (fun n => presStage A (towerIdx A i₀ n)) (by
    intro n
    have h1 : (towerSeq A i₀).map (homOfLE (n.le_add_right 1)) =
        indOf.map (towerStep A i₀ n) :=
      congrArg (fun m => indOf.map m)
        (Functor.ofSequence_map_homOfLE_succ (towerStep A i₀) n)
    have h2 : indOf.map (towerStep A i₀ n) ≫
        presStage A (towerIdx A i₀ (n + 1)) =
        presStage A (towerIdx A i₀ n) :=
      presStage_naturality A (stageStep A (towerIdx A i₀ n))
    exact (eq_whisker h1 _).trans (h2.trans (Category.comp_id _).symm))

/-- **The subalgebra generated by a stage**: the colimit of the
tower.  It is not known to be a subobject of the algebra — see
the module documentation — but it is countably presented, it maps to
the algebra, it contains the unit and it is closed under
multiplication rung by rung. -/
noncomputable def stageSubalgebra
    [SmallCategory C] [MonoidalCategory C] (A : Ind C) [MonObj A]
    (i₀ : A.presentation.I) : Ind C :=
  colimit (towerDiagram (towerStep A i₀) ⋙ indOf)

/-- **The generated tower is countably presented.** -/
theorem countablyPresented_stageSubalgebra
    [SmallCategory C] [MonoidalCategory C] (A : Ind C) [MonObj A]
    (i₀ : A.presentation.I) :
    CountablyPresented (stageSubalgebra A i₀) :=
  countablyPresented_colimit_tower _

/-- The map of the generated tower into the algebra. -/
noncomputable def stageSubalgebraHom
    [SmallCategory C] [MonoidalCategory C] (A : Ind C) [MonObj A]
    (i₀ : A.presentation.I) : stageSubalgebra A i₀ ⟶ A :=
  colimit.desc _ (Cocone.whisker AsSmall.down
    (Cocone.mk A (towerNatTrans A i₀)))

/-- The rungs of the generated tower map into it. -/
noncomputable def stageRung
    [SmallCategory C] [MonoidalCategory C] (A : Ind C) [MonObj A]
    (i₀ : A.presentation.I)
    (n : ℕ) :
    indOf.obj (towerObj A i₀ n) ⟶ stageSubalgebra A i₀ :=
  colimit.ι (towerDiagram (towerStep A i₀) ⋙ indOf) ⟨n⟩

@[simp] theorem stageRung_comp_hom
    [SmallCategory C] [MonoidalCategory C] (A : Ind C) [MonObj A]
    (i₀ : A.presentation.I)
    (n : ℕ) :
    stageRung A i₀ n ≫ stageSubalgebraHom A i₀ =
      presStage A (towerIdx A i₀ n) :=
  colimit.ι_desc _ _

/-- The multiplication of a rung of the generated tower with itself,
landing in the next rung. -/
noncomputable def stageRungMul
    [SmallCategory C] [MonoidalCategory C] (A : Ind C) [MonObj A]
    (i₀ : A.presentation.I)
    (n : ℕ) :
    indOf.obj (towerObj A i₀ n) ⊗ indOf.obj (towerObj A i₀ n) ⟶
      stageSubalgebra A i₀ :=
  (indOfTensorIso (towerObj A i₀ n) (towerObj A i₀ n)).hom ≫
    indOf.map (stageMul A (towerIdx A i₀ n)) ≫ stageRung A i₀ (n + 1)

/-- **The generated tower is closed under multiplication, rung by
rung**: the product of a rung with itself, taken in the algebra,
factors through the tower. -/
theorem stageRungMul_comp_hom
    [SmallCategory C] [MonoidalCategory C] (A : Ind C) [MonObj A]
    (i₀ : A.presentation.I)
    (n : ℕ) :
    stageRungMul A i₀ n ≫ stageSubalgebraHom A i₀ =
      (presStage A (towerIdx A i₀ n) ⊗ₘ
        presStage A (towerIdx A i₀ n)) ≫ μ[A] :=
  have h4 : stageRung A i₀ (n + 1) ≫ stageSubalgebraHom A i₀ =
      presStage A (nextStage A (towerIdx A i₀ n)) :=
    stageRung_comp_hom A i₀ (n + 1)
  have h3 : indOf.map (stageMul A (towerIdx A i₀ n)) ≫
      presStage A (nextStage A (towerIdx A i₀ n)) =
      stageMulToAlg A (towerIdx A i₀ n) :=
    stageMul_spec A (towerIdx A i₀ n)
  (Category.assoc _ _ _).trans
    ((whisker_eq _ ((Category.assoc _ _ _).trans
      ((whisker_eq _ h4).trans h3))).trans
      (indOfTensorIso_stageMulToAlg A (towerIdx A i₀ n)))

/-! ### The unit rung

Generating the tower at a stage through which the unit of the algebra
factors puts the unit into the tower. -/

/-- A stage of the presentation through which the unit factors. -/
noncomputable def unitStage
    [SmallCategory C] [MonoidalCategory C] (A : Ind C) [MonObj A] :
    A.presentation.I :=
  (exists_presStage_point A η[A]).choose

/-- The unit, read at the stage that absorbs it. -/
noncomputable def unitStagePoint
    [SmallCategory C] [MonoidalCategory C] (A : Ind C) [MonObj A] :
    𝟙_ (Ind C) ⟶ indOf.obj (A.presentation.F.obj (unitStage A)) :=
  (exists_presStage_point A η[A]).choose_spec.choose

theorem unitStagePoint_spec
    [SmallCategory C] [MonoidalCategory C] (A : Ind C) [MonObj A] :
    unitStagePoint A ≫ presStage A (unitStage A) = η[A] :=
  (exists_presStage_point A η[A]).choose_spec.choose_spec

/-- **The tower generated at the unit stage contains the unit.** -/
theorem exists_unit_stageSubalgebra
    [SmallCategory C] [MonoidalCategory C] (A : Ind C) [MonObj A] :
    ∃ e : 𝟙_ (Ind C) ⟶ stageSubalgebra A (unitStage A),
      e ≫ stageSubalgebraHom A (unitStage A) = η[A] := by
  refine ⟨unitStagePoint A ≫ stageRung A (unitStage A) 0, ?_⟩
  have h0 : stageRung A (unitStage A) 0 ≫
      stageSubalgebraHom A (unitStage A) = presStage A (unitStage A) :=
    stageRung_comp_hom A (unitStage A) 0
  exact (Category.assoc _ _ _).trans
    ((whisker_eq _ h0).trans (unitStagePoint_spec A))

end Generate

/-! ## The image tower

The ind-completion of a small abelian category is abelian, so a map
into an ind-object has an image, and the rungs of the generated tower
can be replaced by their images in the algebra.  The rung maps then
become monomorphisms, and so does the map of the resulting colimit
into the algebra: a map out of an embedded object into the colimit
factors through a rung, and monomorphisms of ind-objects are detected
on the embedded objects. -/

section Detect

variable {C : Type v}

/-- **Monomorphisms are detected on the embedded objects**: a map of
ind-objects along which maps out of embedded objects cancel is a
monomorphism.  Every ind-object is a filtered colimit of embedded
objects, so a pair of maps into the source is determined by its
restrictions to embedded objects. -/
theorem mono_of_hom_indOf_injective [SmallCategory C]
    {Y Z : Ind C} (f : Y ⟶ Z)
    (h : ∀ (W : C) (u v : indOf.obj W ⟶ Y), u ≫ f = v ≫ f → u = v) :
    Mono f := by
  refine ⟨fun {T} u v huv => ?_⟩
  refine (cancel_epi (Ind.colimitPresentationCompYoneda T).hom).mp ?_
  refine colimit.hom_ext (fun a => ?_)
  refine h (T.presentation.F.obj a) _ _ ?_
  calc (colimit.ι (T.presentation.F ⋙ indOf) a ≫
        (Ind.colimitPresentationCompYoneda T).hom ≫ u) ≫ f
      = colimit.ι (T.presentation.F ⋙ indOf) a ≫
        (Ind.colimitPresentationCompYoneda T).hom ≫ u ≫ f := by
        simp only [Category.assoc]
    _ = colimit.ι (T.presentation.F ⋙ indOf) a ≫
        (Ind.colimitPresentationCompYoneda T).hom ≫ v ≫ f := by
        rw [huv]
    _ = (colimit.ι (T.presentation.F ⋙ indOf) a ≫
        (Ind.colimitPresentationCompYoneda T).hom ≫ v) ≫ f := by
        simp only [Category.assoc]

end Detect

section StageImage

variable {C : Type v}

/-- The image in the ind-object of a stage of its presentation. -/
noncomputable def stageImage [SmallCategory C] [Abelian C] (A : Ind C)
    (i : A.presentation.I) : Ind C :=
  Limits.image (presStage A i)

/-- The image of a stage, as a subobject of the ind-object. -/
noncomputable def stageImageι [SmallCategory C] [Abelian C] (A : Ind C)
    (i : A.presentation.I) :
    stageImage A i ⟶ A :=
  Limits.image.ι (presStage A i)

instance mono_stageImageι [SmallCategory C] [Abelian C] (A : Ind C)
    (i : A.presentation.I) :
    Mono (stageImageι A i) :=
  inferInstanceAs (Mono (Limits.image.ι (presStage A i)))

/-- The stage maps through its image. -/
noncomputable def stageToImage [SmallCategory C] [Abelian C] (A : Ind C)
    (i : A.presentation.I) :
    indOf.obj (A.presentation.F.obj i) ⟶ stageImage A i :=
  Limits.factorThruImage (presStage A i)

instance epi_stageToImage [SmallCategory C] [Abelian C] (A : Ind C)
    (i : A.presentation.I) :
    Epi (stageToImage A i) :=
  inferInstanceAs (Epi (Limits.factorThruImage (presStage A i)))

@[simp] theorem stageToImage_comp_ι [SmallCategory C] [Abelian C] (A : Ind C)
    (i : A.presentation.I) :
    stageToImage A i ≫ stageImageι A i = presStage A i :=
  Limits.image.fac (presStage A i)

/-- A transition map of the presentation includes one image into the
next. -/
noncomputable def stageImageMap [SmallCategory C] [Abelian C] (A : Ind C)
    {i j : A.presentation.I} (α : i ⟶ j) :
    stageImage A i ⟶ stageImage A j :=
  Limits.image.lift
    { I := stageImage A j
      m := stageImageι A j
      e := indOf.map (A.presentation.F.map α) ≫ stageToImage A j
      fac := by
        rw [Category.assoc, stageToImage_comp_ι]
        exact presStage_naturality A α }

@[simp] theorem stageImageMap_comp_ι [SmallCategory C] [Abelian C] (A : Ind C)
    {i j : A.presentation.I}
    (α : i ⟶ j) :
    stageImageMap A α ≫ stageImageι A j = stageImageι A i :=
  Limits.image.lift_fac _

end StageImage

section ImageTower

variable {C : Type v}

/-- The rungs of the image tower. -/
noncomputable def imageRung
    [SmallCategory C] [MonoidalCategory C] [Abelian C] (A : Ind C)
    [MonObj A] (i₀ : A.presentation.I)
    (n : ℕ) : Ind C :=
  stageImage A (towerIdx A i₀ n)

/-- The transition maps of the image tower. -/
noncomputable def imageRungStep
    [SmallCategory C] [MonoidalCategory C] [Abelian C] (A : Ind C)
    [MonObj A] (i₀ : A.presentation.I)
    (n : ℕ) :
    imageRung A i₀ n ⟶ imageRung A i₀ (n + 1) :=
  stageImageMap A (stageStep A (towerIdx A i₀ n))

/-- The image tower as a diagram of ind-objects. -/
noncomputable def imageSeq
    [SmallCategory C] [MonoidalCategory C] [Abelian C] (A : Ind C)
    [MonObj A] (i₀ : A.presentation.I) : ℕ ⥤ Ind C :=
  Functor.ofSequence (imageRungStep A i₀)

/-- **The subalgebra generated by a stage, realised inside the
algebra**: the colimit of the tower of images. -/
noncomputable def imageSubalgebra
    [SmallCategory C] [MonoidalCategory C] [Abelian C] (A : Ind C)
    [MonObj A] (i₀ : A.presentation.I) : Ind C :=
  colimit (AsSmall.down ⋙ imageSeq A i₀)

/-- The cocone of the image tower under the algebra. -/
noncomputable def imageNatTrans
    [SmallCategory C] [MonoidalCategory C] [Abelian C] (A : Ind C)
    [MonObj A] (i₀ : A.presentation.I) :
    imageSeq A i₀ ⟶ (Functor.const ℕ).obj A :=
  NatTrans.ofSequence (fun n => stageImageι A (towerIdx A i₀ n)) (by
    intro n
    have h1 : (imageSeq A i₀).map (homOfLE (n.le_add_right 1)) =
        imageRungStep A i₀ n :=
      Functor.ofSequence_map_homOfLE_succ (imageRungStep A i₀) n
    have h2 : imageRungStep A i₀ n ≫
        stageImageι A (towerIdx A i₀ (n + 1)) =
        stageImageι A (towerIdx A i₀ n) :=
      stageImageMap_comp_ι A (stageStep A (towerIdx A i₀ n))
    exact (eq_whisker h1 _).trans (h2.trans (Category.comp_id _).symm))

/-- The map of the image tower into the algebra. -/
noncomputable def imageSubalgebraHom
    [SmallCategory C] [MonoidalCategory C] [Abelian C] (A : Ind C)
    [MonObj A] (i₀ : A.presentation.I) : imageSubalgebra A i₀ ⟶ A :=
  colimit.desc _ (Cocone.whisker AsSmall.down
    (Cocone.mk A (imageNatTrans A i₀)))

/-- The rungs of the image tower map into it. -/
noncomputable def imageRungι
    [SmallCategory C] [MonoidalCategory C] [Abelian C] (A : Ind C)
    [MonObj A] (i₀ : A.presentation.I)
    (n : ℕ) :
    imageRung A i₀ n ⟶ imageSubalgebra A i₀ :=
  colimit.ι (AsSmall.down ⋙ imageSeq A i₀) ⟨n⟩

@[simp] theorem imageRungι_comp_hom
    [SmallCategory C] [MonoidalCategory C] [Abelian C] (A : Ind C)
    [MonObj A] (i₀ : A.presentation.I)
    (n : ℕ) :
    imageRungι A i₀ n ≫ imageSubalgebraHom A i₀ =
      stageImageι A (towerIdx A i₀ n) :=
  colimit.ι_desc _ _

/-- **The image tower is a subobject of the algebra.**  A map out of
an embedded object into the colimit factors through a rung, two such
factorisations are merged at a later rung, and the rung maps into the
algebra are monomorphisms. -/
theorem mono_imageSubalgebraHom
    [SmallCategory C] [MonoidalCategory C] [Abelian C] (A : Ind C)
    [MonObj A] (i₀ : A.presentation.I) : Mono (imageSubalgebraHom A i₀) := by
  refine mono_of_hom_indOf_injective _ (fun W u v huv => ?_)
  obtain ⟨s, u', hu'⟩ := exists_factor_of_hom_colimit
    (AsSmall.down ⋙ imageSeq A i₀) W u
  obtain ⟨t, v', hv'⟩ := exists_factor_of_hom_colimit
    (AsSmall.down ⋙ imageSeq A i₀) W v
  obtain ⟨k, ⟨hsk⟩, ⟨htk⟩⟩ : ∃ k : ℕ,
      Nonempty (s ⟶ (⟨k⟩ : Tower.{v})) ∧
      Nonempty (t ⟶ (⟨k⟩ : Tower.{v})) :=
    ⟨max (ULift.down s) (ULift.down t),
      ⟨⟨homOfLE (le_max_left _ _)⟩⟩, ⟨⟨homOfLE (le_max_right _ _)⟩⟩⟩
  have hu2 : (u' ≫ (AsSmall.down ⋙ imageSeq A i₀).map hsk) ≫
      colimit.ι (AsSmall.down ⋙ imageSeq A i₀) ⟨k⟩ = u := by
    erw [Category.assoc, colimit.w, hu']
  have hv2 : (v' ≫ (AsSmall.down ⋙ imageSeq A i₀).map htk) ≫
      colimit.ι (AsSmall.down ⋙ imageSeq A i₀) ⟨k⟩ = v := by
    erw [Category.assoc, colimit.w, hv']
  have hrung : colimit.ι (AsSmall.down ⋙ imageSeq A i₀) ⟨k⟩ ≫
      imageSubalgebraHom A i₀ = stageImageι A (towerIdx A i₀ k) :=
    imageRungι_comp_hom A i₀ k
  have hcancel : (u' ≫ (AsSmall.down ⋙ imageSeq A i₀).map hsk) ≫
      stageImageι A (towerIdx A i₀ k) =
      (v' ≫ (AsSmall.down ⋙ imageSeq A i₀).map htk) ≫
      stageImageι A (towerIdx A i₀ k) :=
    calc (u' ≫ (AsSmall.down ⋙ imageSeq A i₀).map hsk) ≫
          stageImageι A (towerIdx A i₀ k)
        = ((u' ≫ (AsSmall.down ⋙ imageSeq A i₀).map hsk) ≫
            colimit.ι (AsSmall.down ⋙ imageSeq A i₀) ⟨k⟩) ≫
            imageSubalgebraHom A i₀ :=
          ((Category.assoc _ _ _).trans (whisker_eq _ hrung)).symm
      _ = u ≫ imageSubalgebraHom A i₀ := eq_whisker hu2 _
      _ = v ≫ imageSubalgebraHom A i₀ := huv
      _ = ((v' ≫ (AsSmall.down ⋙ imageSeq A i₀).map htk) ≫
            colimit.ι (AsSmall.down ⋙ imageSeq A i₀) ⟨k⟩) ≫
            imageSubalgebraHom A i₀ := eq_whisker hv2.symm _
      _ = (v' ≫ (AsSmall.down ⋙ imageSeq A i₀).map htk) ≫
            stageImageι A (towerIdx A i₀ k) :=
          (Category.assoc _ _ _).trans (whisker_eq _ hrung)
  exact hu2.symm.trans ((eq_whisker
    ((cancel_mono (stageImageι A (towerIdx A i₀ k))).mp hcancel) _).trans
    hv2)

end ImageTower

/-! ## Countable presentation of the image tower

The rungs of the image tower are images of embedded objects, and the
tower is countable, so the tower is countably presented as soon as
those images are again embedded.  That is a condition on `C` alone —
`RS.IndImageEmbedded` — and it is not a consequence of abelianness:
for `C` the finitely presented modules over a coherent ring, the
image of `R ⟶ R ⧸ I` is `R ⧸ I`, which is embedded only when `I` is
finitely generated.  It does hold as soon as the subobject orders of
`C` satisfy the ascending chain condition, which the finite length
hypothesis of `RS.Classical.Deligne.GammaCountable` supplies. -/

section PresentedTower

variable {C : Type v}

variable (C) in
/-- **Embedded images**: the image in the ind-completion of a map out
of an embedded object is again embedded. -/
def IndImageEmbedded [SmallCategory C] [Abelian C] : Prop :=
  ∀ (Y : C) (Z : Ind C) (f : indOf.obj Y ⟶ Z),
    ∃ W : C, Nonempty (Limits.image f ≅ indOf.obj W)

/-- **The image tower is countably presented** when the images of
embedded objects are embedded: the tower is an ℕ-tower, and each rung
is by hypothesis an embedded object. -/
theorem countablyPresented_imageSubalgebra
    [SmallCategory C] [Abelian C] [MonoidalCategory C] (A : Ind C)
    [MonObj A] (i₀ : A.presentation.I)
    (h : IndImageEmbedded C) :
    CountablyPresented (imageSubalgebra A i₀) := by
  classical
  choose Z hZ using fun n : ℕ =>
    h (A.presentation.F.obj (towerIdx A i₀ n)) A
      (presStage A (towerIdx A i₀ n))
  set e : ∀ n : ℕ, imageRung A i₀ n ≅ indOf.obj (Z n) :=
    fun n => (hZ n).some with he
  set w : ∀ n : ℕ, Z n ⟶ Z (n + 1) := fun n =>
    Ind.yoneda.fullyFaithful.preimage
      ((e n).inv ≫ imageRungStep A i₀ n ≫ (e (n + 1)).hom) with hw
  have hwmap : ∀ n : ℕ, indOf.map (w n) =
      (e n).inv ≫ imageRungStep A i₀ n ≫ (e (n + 1)).hom := fun n =>
    Ind.yoneda.fullyFaithful.map_preimage _
  set τ : Functor.ofSequence w ⋙ indOf ⟶ imageSeq A i₀ :=
    NatTrans.ofSequence (fun n => (e n).inv) (by
      intro n
      have h1 : (Functor.ofSequence w ⋙ indOf).map
          (homOfLE (n.le_add_right 1)) = indOf.map (w n) :=
        congrArg (fun m => indOf.map m)
          (Functor.ofSequence_map_homOfLE_succ w n)
      have h2 : (imageSeq A i₀).map (homOfLE (n.le_add_right 1)) =
          imageRungStep A i₀ n :=
        Functor.ofSequence_map_homOfLE_succ (imageRungStep A i₀) n
      rw [h1, h2, hwmap n]
      exact (Category.assoc _ _ _).trans (whisker_eq _
        (((Category.assoc _ _ _).trans
          (whisker_eq _ (Iso.hom_inv_id _))).trans
          (Category.comp_id _)))) with hτ
  have hiso : ∀ n : ℕ, IsIso (τ.app n) := by
    intro n
    rw [hτ]
    exact inferInstanceAs (IsIso (e n).inv)
  have : IsIso τ := NatIso.isIso_of_isIso_app τ
  refine CountablyPresented.of_iso
    (HasColimit.isoOfNatIso
      (CategoryTheory.Functor.isoWhiskerLeft (AsSmall.down (C := ℕ))
        (asIso τ))) (countablyPresented_colimit_tower w)

end PresentedTower

/-! ## Compactness of the odd line and of the mixed sums

The isomorphism witnessing local mixedness is a map out of a mixed
sum of the unit and the odd line, so pushing it down to a stage needs
those objects to be compact.  The unit is compact because it is
embedded (`RS.exists_factor_of_unit_hom_colimit`); the odd line is
compact because its square is the unit, which makes tensoring with it
an equivalence and so turns a map out of it into a point of a
translate.  The mixed sums are finite biproducts of the two, and a
finite family of stages of a filtered diagram is dominated by a
single stage. -/

section Untwist

variable {D : Type u}

/-- **Untwisting**: along a trivialisation of the square of `L`, a
point of `L ⊗ W` becomes a map `L ⟶ W`. -/
def oddUntwist [Category.{v} D] [MonoidalCategory D] {L : D} (e : L ⊗ L ≅ 𝟙_ D)
    {W : D} (h : 𝟙_ D ⟶ L ⊗ W) : L ⟶ W :=
  (ρ_ L).inv ≫ L ◁ h ≫ (α_ L L W).inv ≫ e.hom ▷ W ≫ (λ_ W).hom

/-- Untwisting is natural in the target. -/
theorem oddUntwist_comp
    [Category.{v} D] [MonoidalCategory D] {L : D} (e : L ⊗ L ≅ 𝟙_ D)
    {W W' : D} (h : 𝟙_ D ⟶ L ⊗ W) (k : W ⟶ W') :
    oddUntwist e (h ≫ L ◁ k) = oddUntwist e h ≫ k := by
  simp only [oddUntwist, MonoidalCategory.whiskerLeft_comp,
    Category.assoc, associator_inv_naturality_right_assoc,
    whisker_exchange_assoc, leftUnitor_naturality]

/-- The zigzag automorphism of `L` attached to a trivialisation of
its square: untwisting the twist of the identity. -/
def oddZigzag
    [Category.{v} D] [MonoidalCategory D] {L : D} (e : L ⊗ L ≅ 𝟙_ D) : L ≅ L :=
  (ρ_ L).symm ≪≫ whiskerLeftIso L e.symm ≪≫ (α_ L L L).symm ≪≫
    whiskerRightIso e L ≪≫ λ_ L

/-- Untwisting undoes twisting, up to the zigzag automorphism. -/
theorem oddUntwist_twist
    [Category.{v} D] [MonoidalCategory D] {L : D} (e : L ⊗ L ≅ 𝟙_ D)
    {W : D} (g : L ⟶ W) :
    oddUntwist e (e.inv ≫ L ◁ g) = (oddZigzag e).hom ≫ g :=
  oddUntwist_comp e e.inv g

end Untwist

section OddCompact

variable {C : Type v}

/-- **An object whose square is the unit is compact**: a map from it
into a filtered colimit factors through a stage.  Tensoring with the
object preserves the colimit, and the unit is compact, so the
translated point factors; untwisting brings the factorisation
back. -/
theorem exists_factor_of_sq_unit_hom_colimit
    [SmallCategory C] [MonoidalCategory C]
    {L : Ind C}
    (e : L ⊗ L ≅ 𝟙_ (Ind C)) {I : Type v} [SmallCategory I]
    [IsFiltered I] (D : I ⥤ Ind C) (f : L ⟶ colimit D) :
    ∃ (i : I) (g : L ⟶ D.obj i), g ≫ colimit.ι D i = f := by
  obtain ⟨i, h, hh⟩ := exists_factor_of_unit_hom_colimit
    (D ⋙ tensorLeft L)
    ((e.inv ≫ L ◁ f) ≫ (preservesColimitIso (tensorLeft L) D).hom)
  have hι : (tensorLeft L).map (colimit.ι D i) ≫
      (preservesColimitIso (tensorLeft L) D).hom =
      colimit.ι (D ⋙ tensorLeft L) i :=
    ι_preservesColimitIso_hom (tensorLeft L) D i
  have key : h ≫ L ◁ colimit.ι D i = e.inv ≫ L ◁ f := by
    refine (cancel_mono (preservesColimitIso (tensorLeft L) D).hom).mp ?_
    exact (Category.assoc _ _ _).trans
      ((whisker_eq h hι).trans hh)
  refine ⟨i, (oddZigzag e).inv ≫ oddUntwist e h, ?_⟩
  have h1 : oddUntwist e h ≫ colimit.ι D i =
      (oddZigzag e).hom ≫ f :=
    calc oddUntwist e h ≫ colimit.ι D i
        = oddUntwist e (h ≫ L ◁ colimit.ι D i) :=
          (oddUntwist_comp e h (colimit.ι D i)).symm
      _ = oddUntwist e (e.inv ≫ L ◁ f) :=
          congrArg
            (fun t : 𝟙_ (Ind C) ⟶ L ⊗ colimit D => oddUntwist e t) key
      _ = (oddZigzag e).hom ≫ f := oddUntwist_twist e f
  rw [Category.assoc, h1, ← Category.assoc, Iso.inv_hom_id,
    Category.id_comp]

/-- Twisting a map out of an object with unit square into a point of
a translate turns composition into whiskering. -/
theorem oddTwist_comp [SmallCategory C] [MonoidalCategory C]
    {L : Ind C} (e : L ⊗ L ≅ 𝟙_ (Ind C))
    {Z Z' : Ind C} (x : L ⟶ Z) (y : Z ⟶ Z') :
    e.inv ≫ L ◁ (x ≫ y) = (e.inv ≫ L ◁ x) ≫ L ◁ y := by
  rw [MonoidalCategory.whiskerLeft_comp, Category.assoc]

/-- **Merging of stage factorisations out of an object with unit
square**: two factorisations that agree after passing to a filtered
colimit are merged by transition maps of the diagram.  With the
previous theorem this is the whole compactness formula for the odd
line. -/
theorem factor_eq_of_sq_unit_hom_colimit [SmallCategory C] [MonoidalCategory C]
    {L : Ind C}
    (e : L ⊗ L ≅ 𝟙_ (Ind C)) {I : Type v} [SmallCategory I]
    [IsFiltered I] (D : I ⥤ Ind C) {i j : I} (g₁ : L ⟶ D.obj i)
    (g₂ : L ⟶ D.obj j)
    (h : g₁ ≫ colimit.ι D i = g₂ ≫ colimit.ι D j) :
    ∃ (k : I) (α : i ⟶ k) (β : j ⟶ k),
      g₁ ≫ D.map α = g₂ ≫ D.map β := by
  have hι : ∀ m : I, (L ◁ colimit.ι D m) ≫
      (preservesColimitIso (tensorLeft L) D).hom =
      colimit.ι (D ⋙ tensorLeft L) m := fun m =>
    ι_preservesColimitIso_hom (tensorLeft L) D m
  have key : (e.inv ≫ L ◁ g₁) ≫ colimit.ι (D ⋙ tensorLeft L) i =
      (e.inv ≫ L ◁ g₂) ≫ colimit.ι (D ⋙ tensorLeft L) j :=
    calc (e.inv ≫ L ◁ g₁) ≫ colimit.ι (D ⋙ tensorLeft L) i
        = (e.inv ≫ L ◁ g₁) ≫ (L ◁ colimit.ι D i) ≫
            (preservesColimitIso (tensorLeft L) D).hom :=
          whisker_eq _ (hι i).symm
      _ = (e.inv ≫ L ◁ (g₁ ≫ colimit.ι D i)) ≫
            (preservesColimitIso (tensorLeft L) D).hom :=
          ((Category.assoc _ _ _).symm.trans
            (eq_whisker (oddTwist_comp e g₁ (colimit.ι D i)).symm _))
      _ = (e.inv ≫ L ◁ (g₂ ≫ colimit.ι D j)) ≫
            (preservesColimitIso (tensorLeft L) D).hom := by rw [h]
      _ = (e.inv ≫ L ◁ g₂) ≫ (L ◁ colimit.ι D j) ≫
            (preservesColimitIso (tensorLeft L) D).hom :=
          (eq_whisker (oddTwist_comp e g₂ (colimit.ι D j)) _).trans
            (Category.assoc _ _ _)
      _ = (e.inv ≫ L ◁ g₂) ≫ colimit.ι (D ⋙ tensorLeft L) j :=
          whisker_eq _ (hι j)
  obtain ⟨k, α, β, hk⟩ := unit_factor_eq_of_hom_colimit
    (D ⋙ tensorLeft L) (e.inv ≫ L ◁ g₁) (e.inv ≫ L ◁ g₂) key
  refine ⟨k, α, β, ?_⟩
  have hk' : e.inv ≫ L ◁ (g₁ ≫ D.map α) = e.inv ≫ L ◁ (g₂ ≫ D.map β) :=
    (oddTwist_comp e g₁ (D.map α)).trans
      (hk.trans (oddTwist_comp e g₂ (D.map β)).symm)
  refine (cancel_epi (oddZigzag e).hom).mp ?_
  exact ((oddUntwist_twist e (g₁ ≫ D.map α)).symm.trans
    (congrArg (fun t : 𝟙_ (Ind C) ⟶ L ⊗ D.obj k => oddUntwist e t)
      hk')).trans (oddUntwist_twist e (g₂ ≫ D.map β))

/-- The summands of a mixed sum. -/
noncomputable def mixFamily [SmallCategory C] [MonoidalCategory C] [Abelian C]
    [SymmetricCategory (Ind C)]
    (L : OddLine (Ind C)) (p q : ℕ) :
    Fin p ⊕ Fin q → Ind C :=
  fun i => Sum.elim (fun _ => 𝟙_ (Ind C)) (fun _ => L.obj) i

/-- **The mixed sums are compact**: a map from a mixed sum of the
unit and the odd line into a filtered colimit factors through a
stage.  Each summand factors, and a finite family of stages of a
filtered diagram is dominated by a single one. -/
theorem exists_factor_of_mix_hom_colimit
    [SmallCategory C] [MonoidalCategory C] [Abelian C]
    [SymmetricCategory (Ind C)] [HasFiniteBiproducts (Ind C)]
    (L : OddLine (Ind C))
    (p q : ℕ) {I : Type v} [SmallCategory I] [IsFiltered I]
    (D : I ⥤ Ind C) (f : L.mix p q ⟶ colimit D) :
    ∃ (i : I) (g : L.mix p q ⟶ D.obj i), g ≫ colimit.ι D i = f := by
  classical
  have hcomp : ∀ k : Fin p ⊕ Fin q, ∃ (i : I)
      (g : mixFamily L p q k ⟶ D.obj i),
      g ≫ colimit.ι D i = biproduct.ι (mixFamily L p q) k ≫ f := by
    rintro (a | b)
    · exact exists_factor_of_unit_hom_colimit D _
    · exact exists_factor_of_sq_unit_hom_colimit L.sq D _
  choose idx gg hgg using hcomp
  obtain ⟨S, hS⟩ := IsFiltered.sup_objs_exists
    (Finset.image idx Finset.univ)
  have hmap : ∀ k, Nonempty (idx k ⟶ S) := fun k =>
    hS (Finset.mem_image_of_mem idx (Finset.mem_univ k))
  refine ⟨S, biproduct.desc (fun k => gg k ≫ D.map (hmap k).some), ?_⟩
  refine biproduct.hom_ext' _ _ (fun k => ?_)
  have e1 : biproduct.ι (mixFamily L p q) k ≫
      biproduct.desc (fun k => gg k ≫ D.map (hmap k).some) =
      gg k ≫ D.map (hmap k).some := biproduct.ι_desc _ _
  calc biproduct.ι (mixFamily L p q) k ≫
        (biproduct.desc (fun k => gg k ≫ D.map (hmap k).some) ≫
          colimit.ι D S)
      = (biproduct.ι (mixFamily L p q) k ≫
          biproduct.desc (fun k => gg k ≫ D.map (hmap k).some)) ≫
          colimit.ι D S := (Category.assoc _ _ _).symm
    _ = (gg k ≫ D.map (hmap k).some) ≫ colimit.ι D S :=
        eq_whisker e1 _
    _ = gg k ≫ D.map (hmap k).some ≫ colimit.ι D S :=
        Category.assoc _ _ _
    _ = gg k ≫ colimit.ι D (idx k) := whisker_eq _ (colimit.w D _)
    _ = biproduct.ι (mixFamily L p q) k ≫ f := hgg k

end OddCompact

end RS
