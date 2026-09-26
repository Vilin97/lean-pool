/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.IndTensorExact
public import LeanPool.RegtsSevenster.RS.Novel.Envelope.SymPerm

/-!
# ℂ-linearity from the scalar unit

A preadditive monoidal category whose unit endomorphisms are
identified with ℂ carries a ℂ-linear structure on every hom-set:
the scalar `c` acts by conjugating the unit endomorphism `φ c`
through the left unitor and composing.  The file proves the module
laws and assembles `CategoryTheory.Linear ℂ D` from a single ring
isomorphism `φ : ℂ ≃+* End (𝟙_ D)`, then instantiates the input at
`Ind C`: the unit of the transported monoidal structure is the
embedded unit (`RS.indOfUnitIso`), so a scalar unit for `C` induces
one for `Ind C` (`RS.indScalarUnit`).

Two points of care.

* `End`-multiplication is reversed composition, and ℂ is
  commutative; `RS.scalarUnit_map_mul` records the translation
  `φ (a * b) = φ a ≫ φ b` on which `mul_smul` rests.
* The monoidal-linear laws need more than the module laws: left
  whiskering moves the scalar to the *right* leg of the tensor, so
  `whiskerLeft_smul` needs the left-unitor conjugate of `φ c ▷ X`
  to agree with the right-unitor conjugate of `X ◁ φ c`.  This is
  not a theorem of general monoidal categories (in bimodules over a
  commutative ring `R` with an automorphism, the two conjugates
  differ on twisted bimodules even when `End (𝟙) = ℂ`), but it
  holds in braided ones.  The agreement is therefore isolated as
  the hypothesis `RS.ScalarBalanced`, discharged for braided
  categories by `RS.scalarBalanced_of_braided`.

Everything here is a `def` or a `theorem`, never an instance: a
global `Linear ℂ` instance built from an arbitrary `φ` would clash
with existing linear structures (and with itself, for two different
`φ`), so callers install the structure with `letI` at use sites.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits

universe v u v' u'

noncomputable section

/-! ## The scalar action of the unit's endomorphisms -/

section General

variable {D : Type u}

/-- The unit endomorphism `φ c`, typed as a morphism rather than as
an element of the endomorphism ring, so that sums and composites of
these values elaborate at the hom-set instances. -/
def scalarHom [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    (φ : ℂ ≃+* End (𝟙_ D)) (c : ℂ) : 𝟙_ D ⟶ 𝟙_ D :=
  φ c

/-- `End`-multiplication is reversed composition, and ℂ is
commutative, so a ring isomorphism out of ℂ turns products into
composites in either order; this is the composition-order reading
used throughout. -/
theorem scalarUnit_map_mul [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    (φ : ℂ ≃+* End (𝟙_ D)) (a b : ℂ) :
    scalarHom φ (a * b) = scalarHom φ a ≫ scalarHom φ b := by
  simp only [scalarHom]
  rw [mul_comm a b, map_mul, End.mul_def]

/-- **The scalar `c` as an endomorphism of `X`**: whisker the unit
endomorphism `φ c` onto `X` and cancel the unit through the left
unitor. -/
def scalarEnd [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    (φ : ℂ ≃+* End (𝟙_ D)) (c : ℂ) (X : D) : X ⟶ X :=
  (λ_ X).inv ≫ (scalarHom φ c ▷ X) ≫ (λ_ X).hom

/-- The scalar `1` acts as the identity. -/
theorem scalarEnd_one [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    (φ : ℂ ≃+* End (𝟙_ D)) (X : D) :
    scalarEnd φ 1 X = 𝟙 X := by
  have h : scalarHom φ 1 = 𝟙 (𝟙_ D) := map_one φ
  simp [scalarEnd, h]

/-- The action turns multiplication into composition. -/
theorem scalarEnd_mul [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    (φ : ℂ ≃+* End (𝟙_ D)) (a b : ℂ) (X : D) :
    scalarEnd φ (a * b) X = scalarEnd φ a X ≫ scalarEnd φ b X := by
  simp [scalarEnd, scalarUnit_map_mul φ a b]

/-- **The scalar action is central**: it exchanges with every
morphism.  Left-unitor naturality moves the unitors across `f`, and
the whisker exchange moves `φ c ▷ −` across `𝟙 ◁ f`. -/
theorem scalarEnd_naturality
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    (φ : ℂ ≃+* End (𝟙_ D)) (c : ℂ)
    {X Y : D} (f : X ⟶ Y) :
    scalarEnd φ c X ≫ f = f ≫ scalarEnd φ c Y := by
  simp only [scalarEnd, Category.assoc]
  rw [← leftUnitor_naturality, ← whisker_exchange_assoc,
    ← leftUnitor_inv_naturality_assoc]

/-- The scalar action whiskers on the right: the left-unitor
conjugate at `X ⊗ Y` restricts to the one at `X`. -/
theorem scalarEnd_whiskerRight
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    (φ : ℂ ≃+* End (𝟙_ D)) (c : ℂ)
    (X Y : D) :
    scalarEnd φ c X ▷ Y = scalarEnd φ c (X ⊗ Y) := by
  simp [scalarEnd]

/-- **The two-sided agreement of the unit action**: the left-unitor
conjugate of `φ c ▷ X` is the right-unitor conjugate of `X ◁ φ c`.
This is *not* automatic in a monoidal category — bimodule categories
with `End (𝟙) = ℂ` can act by different ring embeddings on the two
sides of an object — and it is exactly what the monoidal-linear law
for left whiskering needs, so it is a named hypothesis, discharged
in the braided case by `RS.scalarBalanced_of_braided`. -/
def ScalarBalanced [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    (φ : ℂ ≃+* End (𝟙_ D)) : Prop :=
  ∀ (c : ℂ) (X : D),
    (λ_ X).inv ≫ (scalarHom φ c ▷ X) ≫ (λ_ X).hom =
      (ρ_ X).inv ≫ (X ◁ scalarHom φ c) ≫ (ρ_ X).hom

/-- In a braided category the unit action is balanced: the braiding
with the unit carries `φ c ▷ X` to `X ◁ φ c` and exchanges the two
unitors. -/
theorem scalarBalanced_of_braided
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [BraidedCategory D]
    (φ : ℂ ≃+* End (𝟙_ D)) : ScalarBalanced φ := by
  intro c X
  have h : (scalarHom φ c ▷ X) ≫ (β_ (𝟙_ D) X).hom =
      (β_ (𝟙_ D) X).hom ≫ (X ◁ scalarHom φ c) :=
    BraidedCategory.braiding_naturality_left _ X
  have h' : scalarHom φ c ▷ X =
      (β_ (𝟙_ D) X).hom ≫ (X ◁ scalarHom φ c) ≫
        (β_ (𝟙_ D) X).inv := by
    rw [← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  rw [h', braiding_tensorUnit_left, braiding_inv_tensorUnit_left]
  simp

/-- Left whiskering carries the left-unitor conjugate of a unit
endomorphism into the right-unitor conjugate, whiskered on the
right: the triangle identity trades `X ◁ (λ_ Y)` for
`(ρ_ X) ▷ Y` around the middle associator. -/
theorem whiskerLeft_unitConj [Category.{v} D] [MonoidalCategory D]
    (u : 𝟙_ D ⟶ 𝟙_ D) (X Y : D) :
    X ◁ ((λ_ Y).inv ≫ (u ▷ Y) ≫ (λ_ Y).hom) =
      ((ρ_ X).inv ≫ (X ◁ u) ≫ (ρ_ X).hom) ▷ Y := by
  have hmid : X ◁ (u ▷ Y) =
      (α_ X (𝟙_ D) Y).inv ≫
        ((X ◁ u) ▷ Y) ≫ (α_ X (𝟙_ D) Y).hom := by
    rw [whisker_assoc]
    simp
  simp only [MonoidalCategory.whiskerLeft_comp, hmid,
    comp_whiskerRight, Category.assoc]
  rw [← triangle_assoc_comp_left_inv_assoc, ← MonoidalCategory.triangle]

/-- The scalar action whiskers on the left, given the two-sided
agreement, which converts the right-unitor data produced by
`RS.whiskerLeft_unitConj` back to left-unitor data at `X`. -/
theorem whiskerLeft_scalarEnd
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    (φ : ℂ ≃+* End (𝟙_ D))
    (h : ScalarBalanced φ) (c : ℂ) (X Y : D) :
    X ◁ scalarEnd φ c Y = scalarEnd φ c (X ⊗ Y) := by
  calc X ◁ scalarEnd φ c Y
      = ((ρ_ X).inv ≫ (X ◁ scalarHom φ c) ≫ (ρ_ X).hom) ▷ Y :=
        whiskerLeft_unitConj (scalarHom φ c) X Y
    _ = ((λ_ X).inv ≫ (scalarHom φ c ▷ X) ≫ (λ_ X).hom) ▷ Y :=
        by rw [← h c X]
    _ = scalarEnd φ c X ▷ Y := rfl
    _ = scalarEnd φ c (X ⊗ Y) := scalarEnd_whiskerRight φ c X Y

/-! ## The hom-set modules and the linear structure -/

/-- The action is additive in the scalar. -/
theorem scalarEnd_add [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D]
    (φ : ℂ ≃+* End (𝟙_ D)) (a b : ℂ) (X : D) :
    scalarEnd φ (a + b) X = scalarEnd φ a X + scalarEnd φ b X := by
  have h : scalarHom φ (a + b) = scalarHom φ a + scalarHom φ b :=
    map_add φ a b
  simp only [scalarEnd, h, MonoidalPreadditive.add_whiskerRight,
    Preadditive.add_comp, Preadditive.comp_add]

/-- The scalar `0` acts as zero. -/
theorem scalarEnd_zero [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D]
    (φ : ℂ ≃+* End (𝟙_ D)) (X : D) :
    scalarEnd φ 0 X = 0 := by
  have h : scalarHom φ 0 = (0 : 𝟙_ D ⟶ 𝟙_ D) := map_zero φ
  simp [scalarEnd, h]

/-- **The scalar action on a hom-set**: whisker the unit
endomorphism through the left unitor of the source and compose. -/
def scalarSmul [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    (φ : ℂ ≃+* End (𝟙_ D)) {X Y : D} (c : ℂ)
    (f : X ⟶ Y) : X ⟶ Y :=
  (λ_ X).inv ≫ (scalarHom φ c ▷ X) ≫ (λ_ X).hom ≫ f

/-- The action on morphisms is composition with the endomorphism
form of the scalar. -/
theorem scalarSmul_eq [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    (φ : ℂ ≃+* End (𝟙_ D)) {X Y : D} (c : ℂ)
    (f : X ⟶ Y) : scalarSmul φ c f = scalarEnd φ c X ≫ f := by
  simp [scalarSmul, scalarEnd]

/-- The ℂ-module structure on a hom-set induced by the scalar
unit. -/
@[reducible] def scalarModule
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D]
    (φ : ℂ ≃+* End (𝟙_ D)) (X Y : D) :
    Module ℂ (X ⟶ Y) where
  smul c f := scalarSmul φ c f
  one_smul f := by
    change scalarSmul φ 1 f = f
    rw [scalarSmul_eq, scalarEnd_one, Category.id_comp]
  mul_smul a b f := by
    change scalarSmul φ (a * b) f = scalarSmul φ a (scalarSmul φ b f)
    rw [scalarSmul_eq, scalarSmul_eq, scalarSmul_eq, scalarEnd_mul,
      Category.assoc]
  smul_zero c := by
    change scalarSmul φ c 0 = 0
    rw [scalarSmul_eq, Limits.comp_zero]
  smul_add c f g := by
    change scalarSmul φ c (f + g) = scalarSmul φ c f + scalarSmul φ c g
    rw [scalarSmul_eq, scalarSmul_eq, scalarSmul_eq,
      Preadditive.comp_add]
  add_smul a b f := by
    change scalarSmul φ (a + b) f = scalarSmul φ a f + scalarSmul φ b f
    rw [scalarSmul_eq, scalarSmul_eq, scalarSmul_eq, scalarEnd_add,
      Preadditive.add_comp]
  zero_smul f := by
    change scalarSmul φ 0 f = 0
    rw [scalarSmul_eq, scalarEnd_zero, Limits.zero_comp]

/-- **ℂ-linearity from the scalar unit**: a ring isomorphism
`ℂ ≃+* End (𝟙_ D)` makes a preadditive monoidal category ℂ-linear.
A `def`, not an instance: an unconditional instance would clash with
every existing linear structure, so callers install it by `letI`. -/
@[reducible] def linearOfScalarUnit
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D]
    (φ : ℂ ≃+* End (𝟙_ D)) :
    CategoryTheory.Linear ℂ D where
  homModule X Y := scalarModule φ X Y
  smul_comp X Y Z r f g := by
    change scalarSmul φ r f ≫ g = scalarSmul φ r (f ≫ g)
    rw [scalarSmul_eq, scalarSmul_eq, Category.assoc]
  comp_smul X Y Z f r g := by
    change f ≫ scalarSmul φ r g = scalarSmul φ r (f ≫ g)
    rw [scalarSmul_eq, scalarSmul_eq, ← Category.assoc,
      ← scalarEnd_naturality, Category.assoc]

/-- **Monoidal ℂ-linearity from the scalar unit**, given the
two-sided agreement of the unit action: whiskering is ℂ-linear in
each variable.  Stated under `letI := linearOfScalarUnit φ`; use it
the same way. -/
theorem monoidalLinearOfScalarUnit
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D]
    (φ : ℂ ≃+* End (𝟙_ D))
    (h : ScalarBalanced φ) :
    letI := linearOfScalarUnit φ
    MonoidalLinear ℂ D := by
  let := linearOfScalarUnit φ
  refine ⟨fun X {Y Z} r f => ?_, fun r {Y Z} f X => ?_⟩
  · change X ◁ scalarSmul φ r f = scalarSmul φ r (X ◁ f)
    rw [scalarSmul_eq, scalarSmul_eq,
      MonoidalCategory.whiskerLeft_comp, whiskerLeft_scalarEnd φ h]
  · change scalarSmul φ r f ▷ X = scalarSmul φ r (f ▷ X)
    rw [scalarSmul_eq, scalarSmul_eq, comp_whiskerRight,
      scalarEnd_whiskerRight]

/-- Monoidal ℂ-linearity from the scalar unit in a braided category,
where the two-sided agreement is automatic. -/
theorem monoidalLinearOfScalarUnitBraided
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D]
    [BraidedCategory D]
    (φ : ℂ ≃+* End (𝟙_ D)) :
    letI := linearOfScalarUnit φ
    MonoidalLinear ℂ D :=
  monoidalLinearOfScalarUnit φ (scalarBalanced_of_braided φ)

end General

/-! ## Endomorphism rings under isomorphism and embedding -/

section EndTransport

variable {E : Type u'}

/-- Conjugation by an isomorphism as a ring equivalence of
endomorphism rings; conjugation preserves the reversed products
because the connecting isomorphisms cancel in the middle. -/
def endCongrRingEquiv [Category.{v'} E] [Preadditive E]
    {X Y : E} (α : X ≅ Y) : End X ≃+* End Y :=
  { α.conj with
    map_add' := fun f g => by
      have h : ∀ p q : X ⟶ X, α.inv ≫ (p + q) ≫ α.hom =
          (α.inv ≫ p ≫ α.hom) + (α.inv ≫ q ≫ α.hom) := fun p q => by
        rw [Preadditive.add_comp, Preadditive.comp_add]
      exact h f g }

end EndTransport

/-! ## The scalar unit of `Ind C` -/

section Ind

variable {C : Type v}

/-- The embedding `C ⥤ Ind C` is additive: it preserves finite
colimits, hence binary biproducts, between preadditive
categories. -/
theorem indOf_additive [SmallCategory C] [Preadditive C] [HasFiniteColimits C] :
    (indOf (C := C)).Additive := by
  have : Limits.HasFiniteBiproducts C :=
    Limits.HasFiniteBiproducts.of_hasFiniteCoproducts
  have : Limits.HasBinaryBiproducts C :=
    Limits.hasBinaryBiproducts_of_finite_biproducts C
  have : Limits.HasBinaryBiproducts (Ind C) :=
    Limits.hasBinaryBiproducts_of_finite_biproducts (Ind C)
  have : (indOf (C := C)).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_map_zero_object
      (isZero_indOf (Limits.isZero_zero C)).isoZero
  have := Limits.preservesBinaryBiproducts_of_preservesBinaryCoproducts
    (indOf (C := C))
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- Full faithfulness of the embedding on endomorphisms, as a ring
equivalence; `End`-multiplication is reversed composition on both
sides, so functoriality preserves it verbatim. -/
def indOfEndRingEquiv [SmallCategory C] [Preadditive C] [HasFiniteColimits C]
    (x : C) : End x ≃+* End (indOf.obj x) where
  toFun f := indOf.map f
  invFun g := Ind.yoneda.fullyFaithful.preimage g
  left_inv f := Ind.yoneda.fullyFaithful.preimage_map f
  right_inv g := Ind.yoneda.fullyFaithful.map_preimage g
  map_mul' f g := by
    rw [End.mul_def, End.mul_def, Functor.map_comp]
  map_add' f g := by
    have := indOf_additive (C := C)
    exact Functor.map_add (F := indOf (C := C))

/-- **The scalar unit of `Ind C`**: a ring isomorphism
`ℂ ≃+* End (𝟙_ C)` transports along the embedding and the unit
identification to one for `Ind C`. -/
def indScalarUnit [SmallCategory C] [MonoidalCategory C] [Preadditive C]
    [HasFiniteColimits C]
    (ψ : ℂ ≃+* End (𝟙_ C)) :
    ℂ ≃+* End (𝟙_ (Ind C)) :=
  (ψ.trans (indOfEndRingEquiv (𝟙_ C))).trans
    (endCongrRingEquiv (indOfUnitIso (C := C)).symm)

end Ind

/-! ## Acceptance -/

section Acceptance

variable {C : Type v}

example
    [SmallCategory C] [MonoidalCategory C] [Preadditive C]
    [HasFiniteColimits C] [MonoidalPreadditive C]
    (ψ : ℂ ≃+* End (𝟙_ C)) : CategoryTheory.Linear ℂ (Ind C) :=
  linearOfScalarUnit (indScalarUnit ψ)

example
    [SmallCategory C] [MonoidalCategory C] [Preadditive C]
    [HasFiniteColimits C] [MonoidalPreadditive C]
    [BraidedCategory C] (ψ : ℂ ≃+* End (𝟙_ C)) :
    letI := linearOfScalarUnit (indScalarUnit ψ)
    MonoidalLinear ℂ (Ind C) :=
  monoidalLinearOfScalarUnitBraided (indScalarUnit ψ)

example
    [SmallCategory C] [MonoidalCategory C] [Preadditive C]
    [HasFiniteColimits C] [MonoidalPreadditive C]
    [SymmetricCategory C] (ψ : ℂ ≃+* End (𝟙_ C)) (X : Ind C)
    (n : ℕ) :
    letI := linearOfScalarUnit (indScalarUnit ψ)
    SymGroupAlgebra n →ₐ[ℂ] End (tensorPow (Ind C) X n) :=
  letI := linearOfScalarUnit (indScalarUnit ψ)
  permAlg X n

end Acceptance

end

end RS
