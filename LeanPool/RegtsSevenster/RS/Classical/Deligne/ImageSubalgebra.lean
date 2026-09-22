/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.CountableDescent

/-!
# The algebra structure on the image tower

`RS.Classical.Deligne.CountableDescent` builds, inside a commutative
algebra `A` of `Ind C` and above a stage `i₀` of its presentation, the
tower of images `RS.imageRung`, its colimit `RS.imageSubalgebra`, and
the monomorphism `RS.imageSubalgebraHom` of that colimit into the
algebra.  This file makes the colimit an algebra in its own right, so
that the countably presented replacement produced there is a
replacement of algebras.

The multiplication.  Tensoring in `Ind C` preserves filtered colimits
(`RS.Classical.Deligne.IndTensorExact`), so the square of the colimit
is the colimit of the squares, and the multiplication is a descent in
each variable: `RS.imageMul` is `RS.imageLeftMul` descended along the
right-hand variable, and `RS.imageLeftMul` is `RS.imagePairMul`
descended along the left-hand one.  The naturality conditions of the
two descents cost nothing, because `RS.imageSubalgebraHom` is a
monomorphism and both sides of each condition have the same composite
with it.

The product of a pair of rungs.  Rungs `n` and `m` are pushed up to
their common upper bound, where the tower is closed under
multiplication one rung at a time.  Closure is an
epimorphism--monomorphism lifting: the square of the stage of the
presentation surjects onto the square of its image, because the
tensor of `Ind C` is right exact in each variable
(`RS.Classical.Deligne.IndCoeq`) and hence carries epimorphisms to
epimorphisms; the next rung is a subobject of the algebra; and
`RS.stageMul_spec` says the square commutes.  Every epimorphism of an
abelian category is strong, so the lifting exists.

The unit and the laws.  A stage carrying the unit of the algebra
(`RS.UnitAtStage`, satisfied by `RS.unitStage` and by every stage
above it) puts the unit into rung zero.  The laws are then free: each
is an equation between maps into the colimit, and a monomorphism
cancels, so each reduces to the corresponding law in `A`.  This is
`RS.monObjOfMono`, and it gives `MonObj (RS.imageSubalgebra A i₀)`
and, over a symmetric `C`, `IsCommMonObj` of the same.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe w u v

/-! ## Subobjects closed under the operations

A monomorphism into an algebra whose source carries a multiplication
and a unit lying over those of the algebra is itself an algebra: each
law is an equation between maps into the source, and a monomorphism
cancels. -/

section SubObject

variable {D : Type u}

/-- **The unit law of a subobject closed under the operations**,
left-hand version. -/
theorem one_mul_of_mono
    [Category.{w} D] [MonoidalCategory D] {S : D} {A : D} [MonObj A]
    (k : S ⟶ A) [Mono k] (m : S ⊗ S ⟶ S) (e : 𝟙_ D ⟶ S)
    (hm : m ≫ k = (k ⊗ₘ k) ≫ μ[A])
    (he : e ≫ k = η[A]) : e ▷ S ≫ m = (λ_ S).hom := by
  rw [← cancel_mono k, Category.assoc, hm, ← Category.assoc,
    ← tensorHom_id, tensorHom_comp_tensorHom, Category.id_comp, he,
    tensorHom_def', Category.assoc, MonObj.one_mul,
    leftUnitor_naturality]

/-- **The unit law of a subobject closed under the operations**,
right-hand version. -/
theorem mul_one_of_mono
    [Category.{w} D] [MonoidalCategory D] {S : D} {A : D} [MonObj A]
    (k : S ⟶ A) [Mono k] (m : S ⊗ S ⟶ S) (e : 𝟙_ D ⟶ S)
    (hm : m ≫ k = (k ⊗ₘ k) ≫ μ[A])
    (he : e ≫ k = η[A]) : S ◁ e ≫ m = (ρ_ S).hom := by
  rw [← cancel_mono k, Category.assoc, hm, ← Category.assoc,
    ← id_tensorHom, tensorHom_comp_tensorHom, Category.id_comp, he,
    tensorHom_def, Category.assoc, MonObj.mul_one,
    rightUnitor_naturality]

/-- **The associativity law of a subobject closed under the
operations.** -/
theorem mul_assoc_of_mono
    [Category.{w} D] [MonoidalCategory D] {S : D} {A : D} [MonObj A]
    (k : S ⟶ A) [Mono k] (m : S ⊗ S ⟶ S)
    (hm : m ≫ k = (k ⊗ₘ k) ≫ μ[A]) :
    m ▷ S ≫ m = (α_ S S S).hom ≫ S ◁ m ≫ m := by
  have h1 : m ▷ S ≫ (k ⊗ₘ k) = ((k ⊗ₘ k) ≫ μ[A]) ⊗ₘ k := by
    rw [← tensorHom_id, tensorHom_comp_tensorHom, Category.id_comp, hm]
  have h2 : S ◁ m ≫ (k ⊗ₘ k) = k ⊗ₘ ((k ⊗ₘ k) ≫ μ[A]) := by
    rw [← id_tensorHom, tensorHom_comp_tensorHom, Category.id_comp, hm]
  have h3 : ((k ⊗ₘ k) ≫ μ[A]) ⊗ₘ k
      = ((k ⊗ₘ k) ⊗ₘ k) ≫ μ[A] ▷ A := by
    rw [← tensorHom_id, tensorHom_comp_tensorHom, Category.comp_id]
  have h4 : k ⊗ₘ ((k ⊗ₘ k) ≫ μ[A])
      = (k ⊗ₘ (k ⊗ₘ k)) ≫ A ◁ μ[A] := by
    rw [← id_tensorHom, tensorHom_comp_tensorHom, Category.comp_id]
  rw [← cancel_mono k]
  simp only [Category.assoc, hm]
  rw [← Category.assoc, h1, h3, ← Category.assoc (S ◁ m), h2, h4,
    Category.assoc, Category.assoc, MonObj.mul_assoc,
    ← Category.assoc ((k ⊗ₘ k) ⊗ₘ k), associator_naturality,
    Category.assoc]

/-- **The commutativity law of a subobject closed under the
operations.** -/
theorem mul_comm_of_mono
    [Category.{w} D] [MonoidalCategory D] {S : D} {A : D} [MonObj A]
    (k : S ⟶ A) [Mono k] (m : S ⊗ S ⟶ S)
    [BraidedCategory D] [IsCommMonObj A]
    (hm : m ≫ k = (k ⊗ₘ k) ≫ μ[A]) : (β_ S S).hom ≫ m = m := by
  rw [← cancel_mono k, Category.assoc, hm, ← Category.assoc,
    ← BraidedCategory.braiding_naturality, Category.assoc,
    IsCommMonObj.mul_comm]

/-- **A subobject closed under the operations is an algebra.** -/
@[reducible] def monObjOfMono
    [Category.{w} D] [MonoidalCategory D] {S : D} {A : D} [MonObj A]
    (k : S ⟶ A) [Mono k] (m : S ⊗ S ⟶ S) (e : 𝟙_ D ⟶ S)
    (hm : m ≫ k = (k ⊗ₘ k) ≫ μ[A])
    (he : e ≫ k = η[A]) : MonObj S where
  one := e
  mul := m
  one_mul := one_mul_of_mono k m e hm he
  mul_one := mul_one_of_mono k m e hm he
  mul_assoc := mul_assoc_of_mono k m hm

end SubObject

/-! ## Epimorphisms and the tensor of ind-objects

The tensor product of `Ind C` is right exact in each variable, so it
carries epimorphisms to epimorphisms; and every epimorphism of an
abelian category is strong. -/

section IndEpi

variable {C : Type v}

/-- **The tensor of two epimorphisms of ind-objects is an
epimorphism**: both whiskerings are right exact. -/
instance epi_tensorHom_ind
    [SmallCategory C] [MonoidalCategory C] [Abelian C] [RigidCategory C]
    [MonoidalPreadditive C]
    {X Y X' Y' : Ind C} (f : X ⟶ Y)
    (g : X' ⟶ Y') [Epi f] [Epi g] : Epi (f ⊗ₘ g) := by
  haveI : Epi (f ▷ X') := inferInstanceAs (Epi ((tensorRight X').map f))
  haveI : Epi (Y ◁ g) := inferInstanceAs (Epi ((tensorLeft Y).map g))
  rw [tensorHom_def]
  exact epi_comp _ _

/-- The tensor of two epimorphisms of ind-objects is a strong
epimorphism: `Ind C` is abelian. -/
instance strongEpi_tensorHom_ind
    [SmallCategory C] [MonoidalCategory C] [Abelian C] [RigidCategory C]
    [MonoidalPreadditive C]
    {X Y X' Y' : Ind C} (f : X ⟶ Y)
    (g : X' ⟶ Y') [Epi f] [Epi g] : StrongEpi (f ⊗ₘ g) :=
  strongEpi_of_epi _

end IndEpi

/-! ## The stage carrying the unit

The tower generated at a stage contains the unit of the algebra as
soon as the unit factors through that stage.  The chosen stage
`RS.unitStage` does, and so does every stage above it. -/

section UnitStage

variable {C : Type v}

/-- **The unit is carried by a stage**: the unit of the algebra
factors through the given stage of the chosen presentation. -/
class UnitAtStage
    [SmallCategory C] [MonoidalCategory C]
    (A : Ind C) [MonObj A] (i : A.presentation.I) :
    Prop where
  /-- The unit of the algebra factors through the stage. -/
  exists_point : ∃ e : 𝟙_ (Ind C) ⟶
    indOf.obj (A.presentation.F.obj i), e ≫ presStage A i = η[A]

/-- The factorisation of the unit through a stage that carries it. -/
theorem exists_unitAtStage_point [SmallCategory C] [MonoidalCategory C]
    (A : Ind C) [MonObj A]
    (i : A.presentation.I) [UnitAtStage A i] :
    ∃ e : 𝟙_ (Ind C) ⟶ indOf.obj (A.presentation.F.obj i),
      e ≫ presStage A i = η[A] :=
  UnitAtStage.exists_point

/-- **The chosen unit stage carries the unit.** -/
instance unitAtStage_unitStage [SmallCategory C] [MonoidalCategory C]
    (A : Ind C) [MonObj A] :
    UnitAtStage A (unitStage A) :=
  ⟨⟨unitStagePoint A, unitStagePoint_spec A⟩⟩

/-- **Every stage above a stage carrying the unit carries it too.** -/
theorem UnitAtStage.map [SmallCategory C] [MonoidalCategory C]
    {A : Ind C} [MonObj A]
    {i j : A.presentation.I} (α : i ⟶ j) [UnitAtStage A i] :
    UnitAtStage A j := by
  obtain ⟨e, he⟩ := exists_unitAtStage_point A i
  refine ⟨⟨e ≫ indOf.map (A.presentation.F.map α), ?_⟩⟩
  exact (Category.assoc _ _ _).trans
    ((whisker_eq _ (presStage_naturality A α)).trans he)

end UnitStage

/-! ## The tower, its rungs, and its unit

Everything in this section is available over an abelian `C`: the
comparison maps of the rungs, the lifting square for the rung-wise
multiplication, and the unit. -/

section ImageTowerBasic

variable {C : Type v}

/-- The image tower, read as a diagram over the ambient-universe copy
of the natural numbers. -/
@[reducible] noncomputable def imageDiagram
    [SmallCategory C] [MonoidalCategory C] [Abelian C] (A : Ind C)
    [MonObj A] (i₀ : A.presentation.I) : Tower.{v} ⥤ Ind C :=
  AsSmall.down ⋙ imageSeq A i₀

/-- **Maps into the image tower are determined by their composites
with the inclusion into the algebra**, that inclusion being a
monomorphism. -/
theorem imageSubalgebra_hom_ext
    [SmallCategory C] [MonoidalCategory C] [Abelian C] (A : Ind C)
    [MonObj A] (i₀ : A.presentation.I)
    {X : Ind C}
    {f g : X ⟶ imageSubalgebra A i₀}
    (h : f ≫ imageSubalgebraHom A i₀ = g ≫ imageSubalgebraHom A i₀) :
    f = g :=
  haveI := mono_imageSubalgebraHom A i₀
  (cancel_mono (imageSubalgebraHom A i₀)).mp h

/-- The structural maps of the colimit of the image tower, composed
with the inclusion into the algebra. -/
theorem imageColimitι_comp_hom
    [SmallCategory C] [MonoidalCategory C] [Abelian C] (A : Ind C)
    [MonObj A] (i₀ : A.presentation.I)
    (m : Tower.{v}) :
    colimit.ι (imageDiagram A i₀) m ≫ imageSubalgebraHom A i₀ =
      stageImageι A (towerIdx A i₀ (ULift.down m)) :=
  imageRungι_comp_hom A i₀ (ULift.down m)

/-- The transition maps of the image tower are compatible with the
inclusions of the rungs into the algebra. -/
theorem imageDiagram_map_comp_ι
    [SmallCategory C] [MonoidalCategory C] [Abelian C] (A : Ind C)
    [MonObj A] (i₀ : A.presentation.I)
    {m m' : Tower.{v}} (u : m ⟶ m') :
    (imageDiagram A i₀).map u ≫
        stageImageι A (towerIdx A i₀ (ULift.down m')) =
      stageImageι A (towerIdx A i₀ (ULift.down m)) :=
  (whisker_eq _ (imageColimitι_comp_hom A i₀ m').symm).trans
    ((Category.assoc _ _ _).symm.trans
      ((eq_whisker (colimit.w (imageDiagram A i₀) u) _).trans
        (imageColimitι_comp_hom A i₀ m)))

/-- The comparison map of two rungs of the image tower. -/
noncomputable def imageRungLe
    [SmallCategory C] [MonoidalCategory C] [Abelian C] (A : Ind C)
    [MonObj A] (i₀ : A.presentation.I)
    {n k : ℕ} (h : n ≤ k) :
    stageImage A (towerIdx A i₀ n) ⟶ stageImage A (towerIdx A i₀ k) :=
  (imageDiagram A i₀).map (X := (⟨n⟩ : Tower.{v})) (Y := ⟨k⟩)
    ⟨homOfLE h⟩

theorem imageRungLe_comp_ι
    [SmallCategory C] [MonoidalCategory C] [Abelian C] (A : Ind C)
    [MonObj A] (i₀ : A.presentation.I)
    {n k : ℕ} (h : n ≤ k) :
    imageRungLe A i₀ h ≫ stageImageι A (towerIdx A i₀ k) =
      stageImageι A (towerIdx A i₀ n) :=
  imageDiagram_map_comp_ι A i₀ _

/-- The square of a rung of the generated tower, multiplied into the
next rung of the image tower. -/
noncomputable def imageRungTop
    [SmallCategory C] [MonoidalCategory C] [Abelian C] (A : Ind C)
    [MonObj A] (i₀ : A.presentation.I)
    (n : ℕ) :
    indOf.obj (towerObj A i₀ n) ⊗ indOf.obj (towerObj A i₀ n) ⟶
      stageImage A (towerIdx A i₀ (n + 1)) :=
  (indOfTensorIso (towerObj A i₀ n) (towerObj A i₀ n)).hom ≫
    indOf.map (stageMul A (towerIdx A i₀ n)) ≫
      stageToImage A (towerIdx A i₀ (n + 1))

theorem imageRungTop_comp_ι
    [SmallCategory C] [MonoidalCategory C] [Abelian C] (A : Ind C)
    [MonObj A] (i₀ : A.presentation.I)
    (n : ℕ) :
    imageRungTop A i₀ n ≫ stageImageι A (towerIdx A i₀ (n + 1)) =
      (presStage A (towerIdx A i₀ n) ⊗ₘ
        presStage A (towerIdx A i₀ n)) ≫ μ[A] :=
  have h4 : stageToImage A (towerIdx A i₀ (n + 1)) ≫
      stageImageι A (towerIdx A i₀ (n + 1)) =
      presStage A (nextStage A (towerIdx A i₀ n)) :=
    stageToImage_comp_ι A (towerIdx A i₀ (n + 1))
  have h3 : indOf.map (stageMul A (towerIdx A i₀ n)) ≫
      presStage A (nextStage A (towerIdx A i₀ n)) =
      stageMulToAlg A (towerIdx A i₀ n) :=
    stageMul_spec A (towerIdx A i₀ n)
  (Category.assoc _ _ _).trans
    ((whisker_eq _ ((Category.assoc _ _ _).trans
      ((whisker_eq _ h4).trans h3))).trans
      (indOfTensorIso_stageMulToAlg A (towerIdx A i₀ n)))

theorem imageRungBot_comp
    [SmallCategory C] [MonoidalCategory C] [Abelian C] (A : Ind C)
    [MonObj A] (i₀ : A.presentation.I)
    (n : ℕ) :
    (stageToImage A (towerIdx A i₀ n) ⊗ₘ
        stageToImage A (towerIdx A i₀ n)) ≫
      ((stageImageι A (towerIdx A i₀ n) ⊗ₘ
        stageImageι A (towerIdx A i₀ n)) ≫ μ[A]) =
    (presStage A (towerIdx A i₀ n) ⊗ₘ
      presStage A (towerIdx A i₀ n)) ≫ μ[A] :=
  have h : (stageToImage A (towerIdx A i₀ n) ⊗ₘ
        stageToImage A (towerIdx A i₀ n)) ≫
      (stageImageι A (towerIdx A i₀ n) ⊗ₘ
        stageImageι A (towerIdx A i₀ n)) =
      presStage A (towerIdx A i₀ n) ⊗ₘ
        presStage A (towerIdx A i₀ n) := by
    rw [tensorHom_comp_tensorHom, stageToImage_comp_ι]
  (Category.assoc _ _ _).symm.trans (eq_whisker h μ[A])

/-- The lifting square for the multiplication of a rung of the image
tower with itself: the square of the stage surjects onto the square of
its image, the next rung is a subobject of the algebra, and the
generated tower is closed under multiplication. -/
theorem imageRungMul_sq
    [SmallCategory C] [MonoidalCategory C] [Abelian C] (A : Ind C)
    [MonObj A] (i₀ : A.presentation.I)
    (n : ℕ) :
    CommSq (imageRungTop A i₀ n)
      (stageToImage A (towerIdx A i₀ n) ⊗ₘ
        stageToImage A (towerIdx A i₀ n))
      (stageImageι A (towerIdx A i₀ (n + 1)))
      ((stageImageι A (towerIdx A i₀ n) ⊗ₘ
        stageImageι A (towerIdx A i₀ n)) ≫ μ[A]) :=
  ⟨(imageRungTop_comp_ι A i₀ n).trans (imageRungBot_comp A i₀ n).symm⟩

/-- **The unit of the image tower**, present as soon as the generating
stage carries the unit of the algebra. -/
noncomputable def imageOne
    [SmallCategory C] [MonoidalCategory C] [Abelian C] (A : Ind C)
    [MonObj A] (i₀ : A.presentation.I)
    [UnitAtStage A i₀] :
    𝟙_ (Ind C) ⟶ imageSubalgebra A i₀ :=
  (exists_unitAtStage_point A i₀).choose ≫
    stageToImage A i₀ ≫ imageRungι A i₀ 0

/-- **The unit of the image tower lies over the unit of the
algebra.** -/
theorem imageOne_comp_hom
    [SmallCategory C] [MonoidalCategory C] [Abelian C] (A : Ind C)
    [MonObj A] (i₀ : A.presentation.I)
    [UnitAtStage A i₀] :
    imageOne A i₀ ≫ imageSubalgebraHom A i₀ = η[A] :=
  have h0 : imageRungι A i₀ 0 ≫ imageSubalgebraHom A i₀ =
      stageImageι A i₀ := imageRungι_comp_hom A i₀ 0
  have h1 : stageToImage A i₀ ≫ (imageRungι A i₀ 0 ≫
      imageSubalgebraHom A i₀) = presStage A i₀ :=
    (whisker_eq _ h0).trans (stageToImage_comp_ι A i₀)
  (Category.assoc _ _ _).trans
    ((whisker_eq _ ((Category.assoc _ _ _).trans h1)).trans
      (exists_unitAtStage_point A i₀).choose_spec)

/-- **The unit of the image tower does not vanish** when the unit of
the algebra does not: it composes to the unit of the algebra. -/
theorem imageOne_ne_zero
    [SmallCategory C] [MonoidalCategory C] [Abelian C] (A : Ind C)
    [MonObj A] (i₀ : A.presentation.I)
    [UnitAtStage A i₀] (h : η[A] ≠ 0) :
    imageOne A i₀ ≠ 0 := fun hz =>
  h ((imageOne_comp_hom A i₀).symm.trans
    ((eq_whisker hz _).trans (Limits.zero_comp)))

end ImageTowerBasic

/-! ## The multiplication of the image tower

The rungs are closed under multiplication one rung at a time, by an
epimorphism--monomorphism lifting; the products of pairs of rungs
assemble into the multiplication of the colimit by two filtered
descents. -/

section ImageMul

variable {C : Type v}

/-- **The image tower is closed under multiplication, rung by
rung.** -/
noncomputable def imageRungMul
    [SmallCategory C] [MonoidalCategory C] [Abelian C] [RigidCategory C]
    [MonoidalPreadditive C] (A : Ind C) [MonObj A] (i₀ : A.presentation.I)
    (n : ℕ) :
    stageImage A (towerIdx A i₀ n) ⊗ stageImage A (towerIdx A i₀ n) ⟶
      stageImage A (towerIdx A i₀ (n + 1)) :=
  (imageRungMul_sq A i₀ n).lift

theorem imageRungMul_comp_ι
    [SmallCategory C] [MonoidalCategory C] [Abelian C] [RigidCategory C]
    [MonoidalPreadditive C] (A : Ind C) [MonObj A] (i₀ : A.presentation.I)
    (n : ℕ) :
    imageRungMul A i₀ n ≫ stageImageι A (towerIdx A i₀ (n + 1)) =
      (stageImageι A (towerIdx A i₀ n) ⊗ₘ
        stageImageι A (towerIdx A i₀ n)) ≫ μ[A] :=
  (imageRungMul_sq A i₀ n).fac_right

/-- **The product of two rungs of the image tower**: both are pushed
up to their common upper bound, where the tower multiplies. -/
noncomputable def imagePairMul
    [SmallCategory C] [MonoidalCategory C] [Abelian C] [RigidCategory C]
    [MonoidalPreadditive C] (A : Ind C) [MonObj A] (i₀ : A.presentation.I)
    (n m : ℕ) :
    stageImage A (towerIdx A i₀ n) ⊗ stageImage A (towerIdx A i₀ m) ⟶
      imageSubalgebra A i₀ :=
  (imageRungLe A i₀ (le_max_left n m) ⊗ₘ
      imageRungLe A i₀ (le_max_right n m)) ≫
    imageRungMul A i₀ (max n m) ≫ imageRungι A i₀ (max n m + 1)

theorem imagePairMul_comp_hom
    [SmallCategory C] [MonoidalCategory C] [Abelian C] [RigidCategory C]
    [MonoidalPreadditive C] (A : Ind C) [MonObj A] (i₀ : A.presentation.I)
    (n m : ℕ) :
    imagePairMul A i₀ n m ≫ imageSubalgebraHom A i₀ =
      (stageImageι A (towerIdx A i₀ n) ⊗ₘ
        stageImageι A (towerIdx A i₀ m)) ≫ μ[A] :=
  have h1 : imageRungMul A i₀ (max n m) ≫
      (imageRungι A i₀ (max n m + 1) ≫ imageSubalgebraHom A i₀) =
      (stageImageι A (towerIdx A i₀ (max n m)) ⊗ₘ
        stageImageι A (towerIdx A i₀ (max n m))) ≫ μ[A] :=
    (whisker_eq _ (imageRungι_comp_hom A i₀ (max n m + 1))).trans
      (imageRungMul_comp_ι A i₀ (max n m))
  have h2 : (imageRungLe A i₀ (le_max_left n m) ⊗ₘ
        imageRungLe A i₀ (le_max_right n m)) ≫
      (stageImageι A (towerIdx A i₀ (max n m)) ⊗ₘ
        stageImageι A (towerIdx A i₀ (max n m))) =
      stageImageι A (towerIdx A i₀ n) ⊗ₘ
        stageImageι A (towerIdx A i₀ m) := by
    rw [tensorHom_comp_tensorHom,
      imageRungLe_comp_ι A i₀ (le_max_left n m),
      imageRungLe_comp_ι A i₀ (le_max_right n m)]
  (Category.assoc _ _ _).trans
    ((whisker_eq _ ((Category.assoc _ _ _).trans h1)).trans
      ((Category.assoc _ _ _).symm.trans (eq_whisker h2 μ[A])))

/-- The cocone over the image tower whose leg at a rung is the product
with a fixed rung. -/
noncomputable def imageLeftMulCocone
    [SmallCategory C] [MonoidalCategory C] [Abelian C] [RigidCategory C]
    [MonoidalPreadditive C] (A : Ind C) [MonObj A] (i₀ : A.presentation.I)
    (n : ℕ) :
    Cocone (imageDiagram A i₀ ⋙
      tensorLeft (stageImage A (towerIdx A i₀ n))) :=
  Cocone.mk (imageSubalgebra A i₀)
    { app := fun m => imagePairMul A i₀ n (ULift.down m)
      naturality := fun m m' u => by
        have hh : (stageImage A (towerIdx A i₀ n) ◁
              (imageDiagram A i₀).map u) ≫
            (stageImageι A (towerIdx A i₀ n) ⊗ₘ
              stageImageι A (towerIdx A i₀ (ULift.down m'))) =
            stageImageι A (towerIdx A i₀ n) ⊗ₘ
              stageImageι A (towerIdx A i₀ (ULift.down m)) := by
          erw [whiskerLeft_comp_tensorHom, imageDiagram_map_comp_ι]
          rfl
        refine Eq.trans ?_ (Category.comp_id _).symm
        refine imageSubalgebra_hom_ext A i₀ ?_
        exact ((Category.assoc _ _ _).trans
          ((whisker_eq _ (imagePairMul_comp_hom A i₀ n
              (ULift.down m'))).trans
            ((Category.assoc _ _ _).symm.trans
              (eq_whisker hh μ[A])))).trans
          (imagePairMul_comp_hom A i₀ n (ULift.down m)).symm }

/-- The product of a rung of the image tower with the whole tower. -/
noncomputable def imageLeftMul
    [SmallCategory C] [MonoidalCategory C] [Abelian C] [RigidCategory C]
    [MonoidalPreadditive C] (A : Ind C) [MonObj A] (i₀ : A.presentation.I)
    (n : ℕ) :
    stageImage A (towerIdx A i₀ n) ⊗ imageSubalgebra A i₀ ⟶
      imageSubalgebra A i₀ :=
  (isColimitOfPreserves (tensorLeft (stageImage A (towerIdx A i₀ n)))
    (colimit.isColimit (imageDiagram A i₀))).desc
      (imageLeftMulCocone A i₀ n)

theorem imageLeftMul_fac
    [SmallCategory C] [MonoidalCategory C] [Abelian C] [RigidCategory C]
    [MonoidalPreadditive C] (A : Ind C) [MonObj A] (i₀ : A.presentation.I)
    (n : ℕ) (m : Tower.{v}) :
    (stageImage A (towerIdx A i₀ n) ◁
        colimit.ι (imageDiagram A i₀) m) ≫ imageLeftMul A i₀ n =
      imagePairMul A i₀ n (ULift.down m) :=
  (isColimitOfPreserves (tensorLeft (stageImage A (towerIdx A i₀ n)))
    (colimit.isColimit (imageDiagram A i₀))).fac
      (imageLeftMulCocone A i₀ n) m

theorem imageLeftMul_comp_hom
    [SmallCategory C] [MonoidalCategory C] [Abelian C] [RigidCategory C]
    [MonoidalPreadditive C] (A : Ind C) [MonObj A] (i₀ : A.presentation.I)
    (n : ℕ) :
    imageLeftMul A i₀ n ≫ imageSubalgebraHom A i₀ =
      (stageImageι A (towerIdx A i₀ n) ⊗ₘ
        imageSubalgebraHom A i₀) ≫ μ[A] :=
  (isColimitOfPreserves (tensorLeft (stageImage A (towerIdx A i₀ n)))
    (colimit.isColimit (imageDiagram A i₀))).hom_ext (fun m =>
      have hh : (stageImage A (towerIdx A i₀ n) ◁
            colimit.ι (imageDiagram A i₀) m) ≫
          (stageImageι A (towerIdx A i₀ n) ⊗ₘ
            imageSubalgebraHom A i₀) =
          stageImageι A (towerIdx A i₀ n) ⊗ₘ
            stageImageι A (towerIdx A i₀ (ULift.down m)) := by
        erw [whiskerLeft_comp_tensorHom, imageColimitι_comp_hom]
        rfl
      ((Category.assoc _ _ _).symm.trans
        ((eq_whisker (imageLeftMul_fac A i₀ n m) _).trans
          (imagePairMul_comp_hom A i₀ n (ULift.down m)))).trans
        ((Category.assoc _ _ _).symm.trans
          (eq_whisker hh μ[A])).symm)

/-- The cocone over the image tower whose leg at a rung is the product
of that rung with the whole tower. -/
noncomputable def imageMulCocone
    [SmallCategory C] [MonoidalCategory C] [Abelian C] [RigidCategory C]
    [MonoidalPreadditive C] (A : Ind C) [MonObj A] (i₀ : A.presentation.I) :
    Cocone (imageDiagram A i₀ ⋙
      tensorRight (imageSubalgebra A i₀)) :=
  Cocone.mk (imageSubalgebra A i₀)
    { app := fun n => imageLeftMul A i₀ (ULift.down n)
      naturality := fun n n' u => by
        have hh : ((imageDiagram A i₀).map u ▷
              imageSubalgebra A i₀) ≫
            (stageImageι A (towerIdx A i₀ (ULift.down n')) ⊗ₘ
              imageSubalgebraHom A i₀) =
            stageImageι A (towerIdx A i₀ (ULift.down n)) ⊗ₘ
              imageSubalgebraHom A i₀ := by
          erw [whiskerRight_comp_tensorHom, imageDiagram_map_comp_ι]
          rfl
        refine Eq.trans ?_ (Category.comp_id _).symm
        refine imageSubalgebra_hom_ext A i₀ ?_
        exact ((Category.assoc _ _ _).trans
          ((whisker_eq _ (imageLeftMul_comp_hom A i₀
              (ULift.down n'))).trans
            ((Category.assoc _ _ _).symm.trans
              (eq_whisker hh μ[A])))).trans
          (imageLeftMul_comp_hom A i₀ (ULift.down n)).symm }

/-- **The multiplication of the image tower.** -/
noncomputable def imageMul
    [SmallCategory C] [MonoidalCategory C] [Abelian C] [RigidCategory C]
    [MonoidalPreadditive C] (A : Ind C) [MonObj A] (i₀ : A.presentation.I) :
    imageSubalgebra A i₀ ⊗ imageSubalgebra A i₀ ⟶
      imageSubalgebra A i₀ :=
  (isColimitOfPreserves (tensorRight (imageSubalgebra A i₀))
    (colimit.isColimit (imageDiagram A i₀))).desc (imageMulCocone A i₀)

theorem imageMul_fac
    [SmallCategory C] [MonoidalCategory C] [Abelian C] [RigidCategory C]
    [MonoidalPreadditive C] (A : Ind C) [MonObj A] (i₀ : A.presentation.I)
    (n : Tower.{v}) :
    (colimit.ι (imageDiagram A i₀) n ▷ imageSubalgebra A i₀) ≫
        imageMul A i₀ =
      imageLeftMul A i₀ (ULift.down n) :=
  (isColimitOfPreserves (tensorRight (imageSubalgebra A i₀))
    (colimit.isColimit (imageDiagram A i₀))).fac
      (imageMulCocone A i₀) n

/-- **The multiplication of the image tower lies over the
multiplication of the algebra.** -/
theorem imageMul_comp_hom
    [SmallCategory C] [MonoidalCategory C] [Abelian C] [RigidCategory C]
    [MonoidalPreadditive C] (A : Ind C) [MonObj A] (i₀ : A.presentation.I) :
    imageMul A i₀ ≫ imageSubalgebraHom A i₀ =
      (imageSubalgebraHom A i₀ ⊗ₘ imageSubalgebraHom A i₀) ≫ μ[A] :=
  (isColimitOfPreserves (tensorRight (imageSubalgebra A i₀))
    (colimit.isColimit (imageDiagram A i₀))).hom_ext (fun n =>
      have hh : (colimit.ι (imageDiagram A i₀) n ▷
            imageSubalgebra A i₀) ≫
          (imageSubalgebraHom A i₀ ⊗ₘ imageSubalgebraHom A i₀) =
          stageImageι A (towerIdx A i₀ (ULift.down n)) ⊗ₘ
            imageSubalgebraHom A i₀ := by
        erw [whiskerRight_comp_tensorHom, imageColimitι_comp_hom]
        rfl
      ((Category.assoc _ _ _).symm.trans
        ((eq_whisker (imageMul_fac A i₀ n) _).trans
          (imageLeftMul_comp_hom A i₀ (ULift.down n)))).trans
        ((Category.assoc _ _ _).symm.trans
          (eq_whisker hh μ[A])).symm)

/-- **The image tower is an algebra.**  The laws are inherited from
the algebra: each is an equation between maps into the tower, and the
inclusion into the algebra is a monomorphism. -/
noncomputable instance monObjImageSubalgebra
    [SmallCategory C] [MonoidalCategory C] [Abelian C] [RigidCategory C]
    [MonoidalPreadditive C] (A : Ind C) [MonObj A] (i₀ : A.presentation.I)
    [UnitAtStage A i₀] :
    MonObj (imageSubalgebra A i₀) :=
  haveI := mono_imageSubalgebraHom A i₀
  monObjOfMono (imageSubalgebraHom A i₀) (imageMul A i₀)
    (imageOne A i₀) (imageMul_comp_hom A i₀) (imageOne_comp_hom A i₀)

/-- The unit of the image tower, read through its algebra structure,
does not vanish when the unit of the algebra does not. -/
theorem one_imageSubalgebra_ne_zero
    [SmallCategory C] [MonoidalCategory C] [Abelian C] [RigidCategory C]
    [MonoidalPreadditive C] (A : Ind C) [MonObj A] (i₀ : A.presentation.I)
    [UnitAtStage A i₀] (h : η[A] ≠ 0) :
    η[imageSubalgebra A i₀] ≠ 0 :=
  imageOne_ne_zero A i₀ h

end ImageMul

/-! ## Commutativity

Over a symmetric `C` the image tower is a commutative algebra, again
because the inclusion into the algebra is a monomorphism. -/

section ImageComm

variable {C : Type v}

/-- **The image tower is a commutative algebra.** -/
noncomputable instance isCommMonObj_imageSubalgebra
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C] [Abelian C]
    [RigidCategory C] [MonoidalPreadditive C] (A : Ind C) [MonObj A]
    [IsCommMonObj A] (i₀ : A.presentation.I) [UnitAtStage A i₀] :
    IsCommMonObj (imageSubalgebra A i₀) where
  mul_comm :=
    haveI := mono_imageSubalgebraHom A i₀
    mul_comm_of_mono (imageSubalgebraHom A i₀) (imageMul A i₀)
      (imageMul_comp_hom A i₀)

end ImageComm

/-! ## Acceptance tests

The algebra structure synthesises at the chosen unit stage, and the
replacement it produces is a monomorphism of commutative algebras
with countably presented source and non-vanishing unit. -/

section AcceptanceTests

variable {C : Type v}

noncomputable example
    [SmallCategory C] [MonoidalCategory C] [Abelian C] [RigidCategory C]
    [MonoidalPreadditive C] (A : Ind C) [MonObj A] :
    MonObj (imageSubalgebra A (unitStage A)) :=
  inferInstance

noncomputable example
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C] [Abelian C]
    [RigidCategory C] [MonoidalPreadditive C] (A : Ind C) [MonObj A]
    [IsCommMonObj A] :
    IsCommMonObj (imageSubalgebra A (unitStage A)) :=
  inferInstance

example
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C] [Abelian C]
    [RigidCategory C] [MonoidalPreadditive C] (A : Ind C) [MonObj A]
    [IsCommMonObj A]
    (hemb : IndImageEmbedded C) (h : η[A] ≠ 0) :
    ∃ (B : Ind C) (_ : MonObj B) (_ : IsCommMonObj B) (f : B ⟶ A),
      Mono f ∧ CountablyPresented B ∧ η[B] ≠ 0 :=
  ⟨imageSubalgebra A (unitStage A), inferInstance, inferInstance,
    imageSubalgebraHom A (unitStage A), mono_imageSubalgebraHom _ _,
    countablyPresented_imageSubalgebra _ _ hemb,
    one_imageSubalgebra_ne_zero A (unitStage A) h⟩

end AcceptanceTests

end RS
