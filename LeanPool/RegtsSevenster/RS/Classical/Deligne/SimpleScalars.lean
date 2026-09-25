/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.SimpleQuotient
import LeanPool.RegtsSevenster.RS.Classical.Deligne.MulBy

/-!
# The scalars of a simple algebra

For a commutative algebra object `R` whose only ideals are `⊥` and
`⊤`, multiplication by a nonzero even scalar is an isomorphism, so
the even part of the Γ-algebra of `R` is a field; and the odd part
of that Γ-algebra vanishes.

The mechanism is `RS.mulBy`: multiplication by an even scalar is a
module endomorphism of `R` (`RS.mul_comp_mulBy`), so its kernel and
its image are ideals (`RS.isIdeal_kernelSubobject_mulBy`,
`RS.isIdeal_imageSubobject_mulBy`).  Simplicity forces the kernel to
be `⊥` and the image to be `⊤`, whence the endomorphism is an
isomorphism (`RS.isIso_mulBy_of_simple`) and the preimage of the
unit inverts the scalar (`RS.exists_inverse_of_simple`).

The odd part goes the same way.  An odd element `f` acts on `R` by
`RS.gmul f (𝟙 R)`, whose image is an ideal for the same reason; an
odd element squares to zero, so that action kills its own image, and
under either alternative of simplicity the action vanishes
(`RS.hom_oddLine_eq_zero_of_simple`).
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

/-! ## Convolution against the identity -/

section Ungraded

variable {D : Type u}

/-- Whiskering a morphism into the algebra and multiplying is the
convolution with the identity. -/
theorem whiskerLeft_comp_mul
    [Category.{v} D] [MonoidalCategory D] (R : D) [MonObj R]
    {X : D} (k : X ⟶ R) :
    (R ◁ k) ≫ μ[R] = gmul (𝟙 R) k := by
  rw [gmul_def, id_tensorHom]

/-- The convolution of the identity with itself is the
multiplication. -/
theorem gmul_id_id [Category.{v} D] [MonoidalCategory D] (R : D) [MonObj R] :
    gmul (𝟙 R) (𝟙 R) = μ[R] := by
  rw [gmul_def, id_tensorHom, MonoidalCategory.whiskerLeft_id,
    Category.id_comp]

end Ungraded

section UngradedAdditive

variable {D : Type u}

/-- Convolution with a zero morphism vanishes. -/
theorem zero_gmul [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] (R : D) [MonObj R]
    {X Y : D} (b : Y ⟶ R) :
    gmul (0 : X ⟶ R) b = 0 := by
  rw [gmul_def, tensorHom_def, MonoidalPreadditive.zero_whiskerRight,
    zero_comp, zero_comp]

end UngradedAdditive

/-! ## Multiplication by a scalar is a module endomorphism -/

section Commutative

variable {D : Type u}

/-- Convolution with an even scalar reads the same on either side,
once the source is identified with its tensor with the unit. -/
theorem leftUnitor_inv_gmul_comm
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (R : D)
    [MonObj R] [IsCommMonObj R]
    {X : D} (a : X ⟶ R)
    (g : 𝟙_ D ⟶ R) :
    (λ_ X).inv ≫ gmul g a = (ρ_ X).inv ≫ gmul a g := by
  have hb : (ρ_ X).inv ≫ (β_ X (𝟙_ D)).hom = (λ_ X).inv := by
    rw [← cancel_mono (λ_ X).hom, Category.assoc,
      braiding_leftUnitor, Iso.inv_hom_id, Iso.inv_hom_id]
  rw [gmul_comm a g, ← Category.assoc, hb]

/-- Multiplication by an even scalar, written on the other side. -/
theorem mulBy_eq_gmul_id
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (R : D)
    [MonObj R] [IsCommMonObj R]
    (g : 𝟙_ D ⟶ R) :
    mulBy R g = (ρ_ R).inv ≫ gmul (𝟙 R) g :=
  leftUnitor_inv_gmul_comm R (𝟙 R) g

/-- **Multiplication by an even scalar is a module
endomorphism**: it commutes with the multiplication of the algebra
in the second variable.  Both sides say `g·(a·b) = a·(g·b)`. -/
theorem mul_comp_mulBy
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (R : D)
    [MonObj R] [IsCommMonObj R]
    (g : 𝟙_ D ⟶ R) :
    μ[R] ≫ mulBy R g = (R ◁ mulBy R g) ≫ μ[R] := by
  have h5 : gmul (𝟙 R) (gmul (𝟙 R) g) =
      (α_ R R (𝟙_ D)).inv ≫ gmul μ[R] g := by
    rw [← gmul_id_id R, gmul_assoc, ← Category.assoc, Iso.inv_hom_id,
      Category.id_comp]
  have h6 : R ◁ (ρ_ R).inv ≫ (α_ R R (𝟙_ D)).inv =
      (ρ_ (R ⊗ R)).inv := by monoidal
  have hR : gmul (𝟙 R) (mulBy R g) =
      (ρ_ (R ⊗ R)).inv ≫ gmul μ[R] g := by
    rw [mulBy_eq_gmul_id, gmul_comp, h5, ← Category.assoc, h6]
  rw [whiskerLeft_comp_mul, hR, comp_mulBy,
    leftUnitor_inv_gmul_comm]

/-- **The action of a fixed element is a module map.**  For any
`f : X ⟶ R` the convolution `gmul f (𝟙 R)` absorbs multiplication
by the algebra: `a·(f·b) = f·(a·b)`. -/
theorem act_comp_gmul_id
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (R : D)
    [MonObj R] [IsCommMonObj R]
    {X : D} (f : X ⟶ R) :
    ((β_ R (X ⊗ R)).hom ≫ (α_ X R R).hom ≫ (X ◁ μ[R])) ≫
        gmul f (𝟙 R) =
      (R ◁ gmul f (𝟙 R)) ≫ μ[R] := by
  have hf : gmul f μ[R] = (X ◁ μ[R]) ≫ gmul f (𝟙 R) := by
    rw [← gmul_comp, Category.comp_id]
  rw [whiskerLeft_comp_mul, gmul_comm (𝟙 R) (gmul f (𝟙 R)),
    gmul_assoc, gmul_id_id, hf]
  simp only [Category.assoc]

end Commutative

/-! ## Images as subobjects -/

section Ind

variable {C : Type v}

/-- The factorisation of a morphism through its image, read as a
morphism into the image subobject. -/
noncomputable def imageFactor [SmallCategory C] [Abelian C]
    {X Y : Ind C} (k : X ⟶ Y) :
    X ⟶ ((Subobject.mk (image.ι k) : Subobject Y) : Ind C) :=
  factorThruImage k ≫ (Subobject.underlyingIso (image.ι k)).inv

/-- The factorisation through the image subobject recovers the
morphism. -/
theorem imageFactor_arrow [SmallCategory C] [Abelian C]
    {X Y : Ind C} (k : X ⟶ Y) :
    imageFactor k ≫ (Subobject.mk (image.ι k)).arrow = k := by
  rw [imageFactor, Category.assoc, Subobject.underlyingIso_arrow,
    image.fac]

/-- The factorisation through the image subobject is an
epimorphism. -/
instance epi_imageFactor [SmallCategory C] [Abelian C]
    {X Y : Ind C} (k : X ⟶ Y) :
    Epi (imageFactor k) := by
  change Epi (factorThruImage k ≫ _)
  exact epi_comp _ _

/-! ## Kernel and image are ideals -/

/-- **The kernel of multiplication by a scalar is an ideal**:
multiplication by a scalar is a module endomorphism, so anything it
kills stays killed after multiplying by the algebra. -/
theorem isIdeal_kernelSubobject_mulBy
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C] [Abelian C]
    [MonoidalPreadditive C] (R : Ind C) [MonObj R] [IsCommMonObj R]
    (g : 𝟙_ (Ind C) ⟶ R) :
    IsIdeal R (kernelSubobject (mulBy R g)) := by
  refine (kernelSubobject_factors_iff _ _).2 ?_
  rw [Category.assoc, mul_comp_mulBy, ← Category.assoc,
    ← MonoidalCategory.whiskerLeft_comp, kernelSubobject_arrow_comp,
    MonoidalPreadditive.whiskerLeft_zero, zero_comp]

/-- **The image of a module map is an ideal.**  If a morphism into
the algebra absorbs multiplication by the algebra, its image does
too: tensoring preserves the covering epimorphism onto the image. -/
theorem isIdeal_imageSubobject_of
    [SmallCategory C] [MonoidalCategory C] [Abelian C] [RigidCategory C]
    [MonoidalPreadditive C] (R : Ind C) [MonObj R]
    {X : Ind C} (k : X ⟶ R)
    (θ : R ⊗ X ⟶ X) (hθ : θ ≫ k = (R ◁ k) ≫ μ[R]) :
    IsIdeal R (Subobject.mk (image.ι k)) := by
  have : Epi (R ◁ imageFactor k) :=
    inferInstanceAs (Epi ((tensorLeft R).map _))
  refine factors_of_epi_comp _ (R ◁ imageFactor k) _ ?_
  refine factors_of_comm (θ ≫ imageFactor k) ?_
  rw [Category.assoc, imageFactor_arrow, hθ, ← Category.assoc,
    ← MonoidalCategory.whiskerLeft_comp, imageFactor_arrow]

/-- **The image of multiplication by a scalar is an ideal.** -/
theorem isIdeal_imageSubobject_mulBy
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C] [Abelian C]
    [RigidCategory C] [MonoidalPreadditive C] (R : Ind C) [MonObj R]
    [IsCommMonObj R]
    (g : 𝟙_ (Ind C) ⟶ R) :
    IsIdeal R (Subobject.mk (image.ι (mulBy R g))) :=
  isIdeal_imageSubobject_of R (mulBy R g) μ[R] (mul_comp_mulBy R g)

/-! ## Simplicity makes multiplication invertible -/

/-- A subobject equal to `⊥` has a zero arrow, so a morphism whose
image it is vanishes. -/
theorem eq_zero_of_imageSubobject_eq_bot [SmallCategory C] [Abelian C]
    {X Y : Ind C} {k : X ⟶ Y}
    (h : Subobject.mk (image.ι k) = ⊥) : k = 0 := by
  rw [← image.fac k, Subobject.mk_eq_bot_iff_zero.1 h, comp_zero]

/-- A morphism whose image subobject is `⊤` is an epimorphism. -/
theorem epi_of_imageSubobject_eq_top [SmallCategory C] [Abelian C]
    {X Y : Ind C} {k : X ⟶ Y}
    (h : Subobject.mk (image.ι k) = ⊤) : Epi k := by
  have : IsIso (Subobject.mk (image.ι k)).arrow :=
    (Subobject.isIso_arrow_iff_eq_top _).2 h
  have : IsIso (image.ι k) := by
    rw [← Subobject.underlyingIso_arrow (image.ι k)]
    infer_instance
  have he : Epi (factorThruImage k ≫ image.ι k) := epi_comp _ _
  rwa [image.fac] at he

/-- **Simplicity makes multiplication by a nonzero scalar
invertible.**  The kernel is an ideal different from `⊤`, because a
scalar whose multiplication vanishes is itself zero; the image is an
ideal different from `⊥`, for the same reason.  So the kernel is `⊥`
and the image is `⊤`, and a monomorphism which is an epimorphism of
an abelian category is an isomorphism.  No hypothesis on the unit is
needed: a nonzero scalar already rules out both bad alternatives. -/
theorem isIso_mulBy_of_simple
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C] [Abelian C]
    [RigidCategory C] [MonoidalPreadditive C] (R : Ind C) [MonObj R]
    [IsCommMonObj R]
    (hsimple : ∀ I : Subobject R, IsIdeal R I → I = ⊥ ∨ I = ⊤)
    {g : 𝟙_ (Ind C) ⟶ R} (hg : g ≠ 0) :
    IsIso (mulBy R g) := by
  have hz : mulBy R g ≠ 0 := fun h =>
    hg (eq_zero_of_mulBy_eq_zero R h)
  have : Mono (mulBy R g) := by
    rcases hsimple _ (isIdeal_kernelSubobject_mulBy R g) with h | h
    · refine Preadditive.mono_of_kernel_zero ?_
      have ha : (kernelSubobject (mulBy R g)).arrow = 0 := by
        rw [h, Subobject.bot_arrow]
      have hk := kernelSubobject_arrow' (mulBy R g)
      rw [ha, comp_zero] at hk
      exact hk.symm
    · have : IsIso (kernelSubobject (mulBy R g)).arrow :=
        (Subobject.isIso_arrow_iff_eq_top _).2 h
      exact absurd (zero_of_epi_comp _
        (kernelSubobject_arrow_comp (mulBy R g))) hz
  have : Epi (mulBy R g) := by
    rcases hsimple _ (isIdeal_imageSubobject_mulBy R g) with h | h
    · exact absurd (eq_zero_of_imageSubobject_eq_bot h) hz
    · exact epi_of_imageSubobject_eq_top h
  exact isIso_of_mono_of_epi _

/-! ## The even part is a field -/

/-- **Every nonzero even scalar of a simple algebra is
invertible**: the preimage of the unit under multiplication by the
scalar is its inverse. -/
theorem exists_inverse_of_simple
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C] [Abelian C]
    [RigidCategory C] [MonoidalPreadditive C] (R : Ind C) [MonObj R]
    [IsCommMonObj R]
    (hsimple : ∀ I : Subobject R, IsIdeal R I → I = ⊥ ∨ I = ⊤)
    {g : 𝟙_ (Ind C) ⟶ R} (hg : g ≠ 0) :
    ∃ g' : 𝟙_ (Ind C) ⟶ R,
      (λ_ (𝟙_ (Ind C))).inv ≫ gmul g g' = η[R] := by
  have := isIso_mulBy_of_simple R hsimple hg
  refine ⟨η[R] ≫ inv (mulBy R g), ?_⟩
  rw [← comp_mulBy, Category.assoc, IsIso.inv_hom_id,
    Category.comp_id]

/-- **The even part of the Γ-algebra of a simple algebra is a
field.** -/
theorem isField_gammaEven
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C] [Abelian C]
    [RigidCategory C] [MonoidalPreadditive C] (R : Ind C) [MonObj R]
    [IsCommMonObj R] [CategoryTheory.Linear ℂ (Ind C)]
    [MonoidalLinear ℂ (Ind C)]
    (L : OddLine (Ind C))
    (hsimple : ∀ I : Subobject R, IsIdeal R I → I = ⊥ ∨ I = ⊤)
    (hne : η[R] ≠ 0) :
    IsField ((gammaAlgebra (Ind C) L R).even) := by
  refine ⟨⟨1, 0, ?_⟩, mul_comm, ?_⟩
  · intro h
    exact hne h
  · intro a ha
    obtain ⟨b, hb⟩ := exists_inverse_of_simple R hsimple (g := a) ha
    exact ⟨b, hb⟩

/-- The even part of the Γ-algebra of a simple algebra, as a
field. -/
@[reducible] noncomputable def gammaEvenField
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C] [Abelian C]
    [RigidCategory C] [MonoidalPreadditive C] (R : Ind C) [MonObj R]
    [IsCommMonObj R] [CategoryTheory.Linear ℂ (Ind C)]
    [MonoidalLinear ℂ (Ind C)]
    (L : OddLine (Ind C))
    (hsimple : ∀ I : Subobject R, IsIdeal R I → I = ⊥ ∨ I = ⊤)
    (hne : η[R] ≠ 0) : Field ((gammaAlgebra (Ind C) L R).even) :=
  (isField_gammaEven R L hsimple hne).toField

/-! ## The odd part vanishes -/

/-- **The odd part of the Γ-algebra of a simple algebra
vanishes.**  An odd element `f` acts on the algebra by
`gmul f (𝟙 R)`, whose image is an ideal, so simplicity leaves two
alternatives and the action vanishes under both: if the image is
`⊥` the action is zero outright, and if the image is `⊤` the action
is an epimorphism, which the square-zero law of an odd element
makes annihilate itself.  Evaluating the zero action at the unit
returns `f`. -/
theorem hom_oddLine_eq_zero_of_simple
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C] [Abelian C]
    [RigidCategory C] [MonoidalPreadditive C] (R : Ind C) [MonObj R]
    [IsCommMonObj R] [CategoryTheory.Linear ℂ (Ind C)]
    (L : OddLine (Ind C))
    (hsimple : ∀ I : Subobject R, IsIdeal R I → I = ⊥ ∨ I = ⊤)
    (f : L.obj ⟶ R) : f = 0 := by
  have hid : IsIdeal R (Subobject.mk (image.ι (gmul f (𝟙 R)))) :=
    isIdeal_imageSubobject_of R (gmul f (𝟙 R)) _
      (act_comp_gmul_id R f)
  have hsq : gmul f (gmul f (𝟙 R)) = 0 := by
    have h := gmul_assoc f f (𝟙 R)
    rw [gmul_self_eq_zero_of_oddLine R L f, zero_gmul] at h
    have h2 := congrArg (fun t => (α_ L.obj L.obj R).inv ≫ t) h
    simpa using h2.symm
  have hzero : gmul f (𝟙 R) = 0 := by
    rcases hsimple _ hid with h | h
    · exact eq_zero_of_imageSubobject_eq_bot h
    · have := epi_of_imageSubobject_eq_top h
      have : Epi (L.obj ◁ gmul f (𝟙 R)) :=
        inferInstanceAs (Epi ((tensorLeft L.obj).map _))
      refine zero_of_epi_comp (L.obj ◁ gmul f (𝟙 R)) ?_
      rw [← gmul_comp, Category.comp_id]
      exact hsq
  have hfac : (L.obj ◁ η[R]) ≫ gmul f (𝟙 R) =
      (ρ_ L.obj).hom ≫ f := by
    rw [← gmul_comp, Category.comp_id, gmul_one_right]
  rw [hzero, comp_zero] at hfac
  exact (cancel_epi (ρ_ L.obj).hom).1
    (hfac.symm.trans (comp_zero).symm)

end Ind

end RS
