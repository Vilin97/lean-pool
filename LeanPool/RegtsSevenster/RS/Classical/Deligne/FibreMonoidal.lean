/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.FibreMuNat
import LeanPool.RegtsSevenster.RS.Classical.Deligne.FibreEps
import LeanPool.RegtsSevenster.RS.Classical.Deligne.FreeModShuffleCoh
import LeanPool.RegtsSevenster.RS.Classical.Deligne.FreeModFunctor

/-!
# The fibre functor is symmetric monoidal

Deligne's `ω` is base change to the algebra followed by
realization, and its monoidal comparison `RS.fibreMu` is, on the
generators of the tensor product of super modules, nothing but the
free-module shuffle evaluated at a pair of morphisms.  The three
coherence laws of a lax monoidal functor therefore reduce, family
by family, to the three coherence laws of the shuffle recorded in
`RS.FreeModShuffleCoh`.

The reduction is uniform.  Each generator family names a morphism
`s` out of the intended source into a tensor product of the two
sources involved, and the comparison sends a pair `(m, n)` to
`s ≫ (m ⊗ₘ n) ≫ freeModShuffle`.  Associativity at a family is
then the associativity of the shuffle conjugated by the coherence
identity relating the four `s`'s of that family — exactly the
identity that already appears in the corresponding associativity
axiom of `RS.gammaModule`.  Unitality and the braiding law are the
same computation one factor shorter.

Two signs appear, and both are forced by the target rather than by
the fibre functor:

* the Koszul sign of `rightUnitorHom_evenMap_tmulOO` in the
  odd-odd family of the right unitor;
* the Koszul sign of `braidingHom_evenMap_tmulOO` in the odd-odd
  family of the braiding.

In both places the sign is supplied by `RS.OddLine.braid_neg`: the
self-braiding of the odd line is `−1`, so the source identification
`L.sq.inv` picks up exactly that sign when the two odd generators
are exchanged.  No sign is left over.

The functor is packaged as `CategoryTheory.Functor.LaxMonoidal` and
`CategoryTheory.Functor.LaxBraided`.  Invertibility of `fibreMu` is
a separate matter and is not assumed here, so the strong notions
`Functor.Monoidal` and `Functor.Braided` are not instantiated.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

/-! ## Splitting a tensor of composites -/

section Split

variable {D : Type u}

/-- A composite in the first factor, split off on the left. -/
theorem tensorHom_comp_fst [Category.{v} D] [MonoidalCategory D]
    {A B C X Y : D} (f : A ⟶ B) (g : B ⟶ X)
    (p : C ⟶ Y) : (f ≫ g) ⊗ₘ p = f ▷ C ≫ (g ⊗ₘ p) := by
  rw [← tensorHom_id, tensorHom_comp_tensorHom, Category.id_comp]

/-- A composite in the second factor, split off on the left. -/
theorem tensorHom_comp_snd [Category.{v} D] [MonoidalCategory D]
    {A B C X Y : D} (m : A ⟶ X) (f : B ⟶ C)
    (g : C ⟶ Y) : m ⊗ₘ (f ≫ g) = A ◁ f ≫ (m ⊗ₘ g) := by
  rw [← id_tensorHom, tensorHom_comp_tensorHom, Category.id_comp]

/-- A composite in the first factor, split off on the right. -/
theorem tensorHom_comp_fst' [Category.{v} D] [MonoidalCategory D]
    {A B C X Y : D} (f : A ⟶ B)
    (g : B ⟶ X) (p : C ⟶ Y) : (f ≫ g) ⊗ₘ p = (f ⊗ₘ p) ≫ g ▷ Y := by
  rw [← tensorHom_id, tensorHom_comp_tensorHom, Category.comp_id]

/-- A composite in the second factor, split off on the right. -/
theorem tensorHom_comp_snd' [Category.{v} D] [MonoidalCategory D]
    {A B C X Y : D} (m : A ⟶ X)
    (f : B ⟶ C) (g : C ⟶ Y) : m ⊗ₘ (f ≫ g) = (m ⊗ₘ f) ≫ X ◁ g := by
  rw [← id_tensorHom, tensorHom_comp_tensorHom, Category.comp_id]

end Split

/-! ## The coherence of the shuffle at arbitrary sources -/

section AtSources

variable {D : Type u}

/-- **Associativity of the shuffle at arbitrary sources.**  Given
a coherence identity between the two ways of reassociating the
chosen sources, the two ways of shuffling three morphisms agree. -/
theorem freeModShuffle_assoc_at
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (R : D)
    [MonObj R]
    {A B C T T' T'' : D}
    (s₁ : T ⟶ T' ⊗ C) (s₂ : T' ⟶ A ⊗ B) (s₃ : T ⟶ A ⊗ T'')
    (s₄ : T'' ⟶ B ⊗ C)
    (h : s₁ ≫ s₂ ▷ C ≫ (α_ A B C).hom = s₃ ≫ A ◁ s₄)
    {V W Z : D} (m : A ⟶ R ⊗ V) (n : B ⟶ R ⊗ W)
    (p : C ⟶ R ⊗ Z) :
    s₁ ≫ ((s₂ ≫ (m ⊗ₘ n) ≫ freeModShuffle R V W) ⊗ₘ p) ≫
        freeModShuffle R (V ⊗ W) Z ≫ R ◁ (α_ V W Z).hom =
      s₃ ≫ (m ⊗ₘ (s₄ ≫ (n ⊗ₘ p) ≫ freeModShuffle R W Z)) ≫
        freeModShuffle R V (W ⊗ Z) := by
  rw [tensorHom_comp_fst, tensorHom_comp_fst', tensorHom_comp_snd,
    tensorHom_comp_snd']
  simp only [Category.assoc]
  rw [freeModShuffle_assoc R V W Z,
    associator_naturality_assoc m n p, reassoc_of% h]

/-- `RS.freeModShuffle_assoc_at`, bracketed as realization of the
reassociation of the generators produces it. -/
theorem freeModShuffle_assoc_at'
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (R : D)
    [MonObj R]
    {A B C T T' T'' : D}
    (s₁ : T ⟶ T' ⊗ C) (s₂ : T' ⟶ A ⊗ B) (s₃ : T ⟶ A ⊗ T'')
    (s₄ : T'' ⟶ B ⊗ C)
    (h : s₁ ≫ s₂ ▷ C ≫ (α_ A B C).hom = s₃ ≫ A ◁ s₄)
    {V W Z : D} (m : A ⟶ R ⊗ V) (n : B ⟶ R ⊗ W)
    (p : C ⟶ R ⊗ Z) :
    (s₁ ≫ ((s₂ ≫ (m ⊗ₘ n) ≫ freeModShuffle R V W) ⊗ₘ p) ≫
        freeModShuffle R (V ⊗ W) Z) ≫ R ◁ (α_ V W Z).hom =
      s₃ ≫ (m ⊗ₘ (s₄ ≫ (n ⊗ₘ p) ≫ freeModShuffle R W Z)) ≫
        freeModShuffle R V (W ⊗ Z) :=
  Eq.trans (Category.assoc _ _ _)
    (Eq.trans (whisker_eq _ (Category.assoc _ _ _))
      (freeModShuffle_assoc_at R s₁ s₂ s₃ s₄ h m n p))

/-- **Left unitality of the shuffle**, with the trailing
reassociation of the generators cancelled. -/
theorem freeModShuffle_unit_left'
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (R : D)
    [MonObj R]
    (V : D) :
    ((ρ_ R).inv ▷ (R ⊗ V)) ≫ freeModShuffle R (𝟙_ D) V ≫
        R ◁ (λ_ V).hom = (α_ R R V).inv ≫ μ[R] ▷ V := by
  rw [← Category.assoc, freeModShuffle_unit_left, Category.assoc,
    ← MonoidalCategory.whiskerLeft_comp, Iso.inv_hom_id,
    MonoidalCategory.whiskerLeft_id, Category.comp_id]

/-- **Left unitality of the shuffle at arbitrary sources**:
filling the first slot with the unit comparison leaves the action
of the free module. -/
theorem freeModShuffle_unit_left_at
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (R : D)
    [MonObj R]
    {X Y T : D} (s : T ⟶ X ⊗ Y)
    {V : D} (x : X ⟶ R) (m : Y ⟶ R ⊗ V) :
    s ≫ ((x ≫ (ρ_ R).inv) ⊗ₘ m) ≫ freeModShuffle R (𝟙_ D) V ≫
        R ◁ (λ_ V).hom
      = s ≫ (x ⊗ₘ m) ≫ (α_ R R V).inv ≫ μ[R] ▷ V := by
  rw [tensorHom_comp_fst']
  simp only [Category.assoc]
  rw [freeModShuffle_unit_left' R V]

/-- `RS.freeModShuffle_unit_left_at`, bracketed as realization of
the left unitor of the generators produces it. -/
theorem freeModShuffle_unit_left_at'
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (R : D)
    [MonObj R]
    {X Y T : D} (s : T ⟶ X ⊗ Y)
    {V : D} (x : X ⟶ R) (m : Y ⟶ R ⊗ V) :
    (s ≫ ((x ≫ (ρ_ R).inv) ⊗ₘ m) ≫
        freeModShuffle R (𝟙_ D) V) ≫ R ◁ (λ_ V).hom
      = s ≫ (x ⊗ₘ m) ≫ (α_ R R V).inv ≫ μ[R] ▷ V :=
  Eq.trans (Category.assoc _ _ _)
    (Eq.trans (whisker_eq _ (Category.assoc _ _ _))
      (freeModShuffle_unit_left_at R s x m))

end AtSources

section AtSourcesComm

variable {D : Type u}

/-- **Right unitality of the shuffle**, with the trailing
reassociation of the generators cancelled. -/
theorem freeModShuffle_unit_right'
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (R : D)
    [MonObj R] [IsCommMonObj R]
    (V : D) :
    ((R ⊗ V) ◁ (ρ_ R).inv) ≫ freeModShuffle R V (𝟙_ D) ≫
        R ◁ (ρ_ V).hom
      = (β_ (R ⊗ V) R).hom ≫ (α_ R R V).inv ≫ μ[R] ▷ V := by
  rw [← Category.assoc, freeModShuffle_unit_right, Category.assoc,
    ← MonoidalCategory.whiskerLeft_comp, Iso.inv_hom_id,
    MonoidalCategory.whiskerLeft_id, Category.comp_id]

/-- **Right unitality of the shuffle at arbitrary sources**:
filling the second slot with the unit comparison leaves the action
of the free module, the two sources having been exchanged. -/
theorem freeModShuffle_unit_right_at
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (R : D)
    [MonObj R] [IsCommMonObj R]
    {X Y T : D} (s : T ⟶ X ⊗ Y)
    {V : D} (m : X ⟶ R ⊗ V) (x : Y ⟶ R) :
    s ≫ (m ⊗ₘ (x ≫ (ρ_ R).inv)) ≫ freeModShuffle R V (𝟙_ D) ≫
        R ◁ (ρ_ V).hom
      = s ≫ (β_ X Y).hom ≫ (x ⊗ₘ m) ≫ (α_ R R V).inv ≫
          μ[R] ▷ V := by
  rw [tensorHom_comp_snd']
  simp only [Category.assoc]
  rw [freeModShuffle_unit_right' R V,
    BraidedCategory.braiding_naturality_assoc m x]

/-- `RS.freeModShuffle_unit_right_at`, bracketed as realization of
the right unitor of the generators produces it. -/
theorem freeModShuffle_unit_right_at'
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (R : D)
    [MonObj R] [IsCommMonObj R]
    {X Y T : D} (s : T ⟶ X ⊗ Y)
    {V : D} (m : X ⟶ R ⊗ V) (x : Y ⟶ R) :
    (s ≫ (m ⊗ₘ (x ≫ (ρ_ R).inv)) ≫
        freeModShuffle R V (𝟙_ D)) ≫ R ◁ (ρ_ V).hom
      = s ≫ (β_ X Y).hom ≫ (x ⊗ₘ m) ≫ (α_ R R V).inv ≫
          μ[R] ▷ V :=
  Eq.trans (Category.assoc _ _ _)
    (Eq.trans (whisker_eq _ (Category.assoc _ _ _))
      (freeModShuffle_unit_right_at R s m x))

end AtSourcesComm

section AtSourcesSym

variable {D : Type u}

/-- **The shuffle commutes with the braiding, at arbitrary
sources.** -/
theorem freeModShuffle_braiding_at
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (R : D)
    [MonObj R] [IsCommMonObj R]
    {X Y T : D} (s : T ⟶ X ⊗ Y)
    {V W : D} (m : X ⟶ R ⊗ V) (n : Y ⟶ R ⊗ W) :
    s ≫ (m ⊗ₘ n) ≫ freeModShuffle R V W ≫ R ◁ (β_ V W).hom
      = s ≫ (β_ X Y).hom ≫ (n ⊗ₘ m) ≫ freeModShuffle R W V := by
  rw [← freeModShuffle_braiding R V W,
    BraidedCategory.braiding_naturality_assoc m n]

/-- `RS.freeModShuffle_braiding_at`, bracketed as realization of
the braiding of the generators produces it. -/
theorem freeModShuffle_braiding_at'
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (R : D)
    [MonObj R] [IsCommMonObj R]
    {X Y T : D} (s : T ⟶ X ⊗ Y)
    {V W : D} (m : X ⟶ R ⊗ V) (n : Y ⟶ R ⊗ W) :
    (s ≫ (m ⊗ₘ n) ≫ freeModShuffle R V W) ≫ R ◁ (β_ V W).hom
      = s ≫ (β_ X Y).hom ≫ (n ⊗ₘ m) ≫ freeModShuffle R W V :=
  Eq.trans (Category.assoc _ _ _)
    (Eq.trans (whisker_eq _ (Category.assoc _ _ _))
      (freeModShuffle_braiding_at R s m n))

end AtSourcesSym

/-! ## The braiding on the four sources -/

section OddSources

variable {D : Type u}

/-- The even-even source is fixed by the braiding. -/
theorem leftUnitorInv_braiding_ee
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] :
    (λ_ (𝟙_ D)).inv ≫ (β_ (𝟙_ D) (𝟙_ D)).hom
      = (λ_ (𝟙_ D)).inv := by
  rw [← cancel_mono (ρ_ (𝟙_ D)).hom, Category.assoc,
    braiding_rightUnitor, ← unitors_equal]

/-- The braiding exchanges the even-odd and odd-even sources. -/
theorem leftUnitorInv_braiding_eo
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] (L : OddLine D) :
    (λ_ L.obj).inv ≫ (β_ (𝟙_ D) L.obj).hom = (ρ_ L.obj).inv := by
  rw [← cancel_mono (ρ_ L.obj).hom, Category.assoc,
    braiding_rightUnitor, Iso.inv_hom_id, Iso.inv_hom_id]

/-- The braiding exchanges the odd-even and even-odd sources. -/
theorem rightUnitorInv_braiding_oe
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] (L : OddLine D) :
    (ρ_ L.obj).inv ≫ (β_ L.obj (𝟙_ D)).hom = (λ_ L.obj).inv := by
  rw [braiding_tensorUnit_right, Iso.inv_hom_id_assoc]

end OddSources

/-! ## The four families of the unitor and the braiding -/

section Families

variable {D : Type u}

/-- Right unitality at the even-even family. -/
theorem freeModShuffle_unit_right_ee
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (R : D)
    [MonObj R] [IsCommMonObj R]
    (V : D) (m : 𝟙_ D ⟶ R ⊗ V)
    (x : 𝟙_ D ⟶ R) :
    ((λ_ (𝟙_ D)).inv ≫ (m ⊗ₘ (x ≫ (ρ_ R).inv)) ≫
        freeModShuffle R V (𝟙_ D)) ≫ R ◁ (ρ_ V).hom
      = (λ_ (𝟙_ D)).inv ≫ (x ⊗ₘ m) ≫ (α_ R R V).inv ≫
          μ[R] ▷ V := by
  rw [freeModShuffle_unit_right_at',
    reassoc_of% (leftUnitorInv_braiding_ee (D := D))]

/-- Right unitality at the odd-odd family; the Koszul sign of the
right unitor appears here, and nowhere else. -/
theorem freeModShuffle_unit_right_oo
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R]
    (V : D) (m : L.obj ⟶ R ⊗ V)
    (u : L.obj ⟶ R) :
    (L.sq.inv ≫ (m ⊗ₘ (u ≫ (ρ_ R).inv)) ≫
        freeModShuffle R V (𝟙_ D)) ≫ R ◁ (ρ_ V).hom
      = -(L.sq.inv ≫ (u ⊗ₘ m) ≫ (α_ R R V).inv ≫
          μ[R] ▷ V) := by
  rw [freeModShuffle_unit_right_at',
    reassoc_of% (oddLine_sq_inv_braiding L), Preadditive.neg_comp]

/-- Right unitality at the even-odd family. -/
theorem freeModShuffle_unit_right_eo
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R]
    (V : D) (m : 𝟙_ D ⟶ R ⊗ V)
    (u : L.obj ⟶ R) :
    ((λ_ L.obj).inv ≫ (m ⊗ₘ (u ≫ (ρ_ R).inv)) ≫
        freeModShuffle R V (𝟙_ D)) ≫ R ◁ (ρ_ V).hom
      = (ρ_ L.obj).inv ≫ (u ⊗ₘ m) ≫ (α_ R R V).inv ≫
          μ[R] ▷ V := by
  rw [freeModShuffle_unit_right_at',
    reassoc_of% (leftUnitorInv_braiding_eo L)]

/-- Right unitality at the odd-even family. -/
theorem freeModShuffle_unit_right_oe
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R]
    (V : D) (m : L.obj ⟶ R ⊗ V)
    (x : 𝟙_ D ⟶ R) :
    ((ρ_ L.obj).inv ≫ (m ⊗ₘ (x ≫ (ρ_ R).inv)) ≫
        freeModShuffle R V (𝟙_ D)) ≫ R ◁ (ρ_ V).hom
      = (λ_ L.obj).inv ≫ (x ⊗ₘ m) ≫ (α_ R R V).inv ≫
          μ[R] ▷ V := by
  rw [freeModShuffle_unit_right_at',
    reassoc_of% (rightUnitorInv_braiding_oe L)]

/-- The braiding at the even-even family. -/
theorem freeModShuffle_braiding_ee
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (R : D)
    [MonObj R] [IsCommMonObj R]
    (V W : D) (m : 𝟙_ D ⟶ R ⊗ V)
    (n : 𝟙_ D ⟶ R ⊗ W) :
    ((λ_ (𝟙_ D)).inv ≫ (m ⊗ₘ n) ≫ freeModShuffle R V W) ≫
        R ◁ (β_ V W).hom
      = (λ_ (𝟙_ D)).inv ≫ (n ⊗ₘ m) ≫ freeModShuffle R W V := by
  rw [freeModShuffle_braiding_at',
    reassoc_of% (leftUnitorInv_braiding_ee (D := D))]

/-- The braiding at the odd-odd family; the Koszul sign of the
Koszul swap appears here, and nowhere else. -/
theorem freeModShuffle_braiding_oo
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R]
    (V W : D) (m : L.obj ⟶ R ⊗ V)
    (n : L.obj ⟶ R ⊗ W) :
    (L.sq.inv ≫ (m ⊗ₘ n) ≫ freeModShuffle R V W) ≫
        R ◁ (β_ V W).hom
      = -(L.sq.inv ≫ (n ⊗ₘ m) ≫ freeModShuffle R W V) := by
  rw [freeModShuffle_braiding_at',
    reassoc_of% (oddLine_sq_inv_braiding L), Preadditive.neg_comp]

/-- The braiding at the even-odd family. -/
theorem freeModShuffle_braiding_eo
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R]
    (V W : D) (m : 𝟙_ D ⟶ R ⊗ V)
    (n : L.obj ⟶ R ⊗ W) :
    ((λ_ L.obj).inv ≫ (m ⊗ₘ n) ≫ freeModShuffle R V W) ≫
        R ◁ (β_ V W).hom
      = (ρ_ L.obj).inv ≫ (n ⊗ₘ m) ≫ freeModShuffle R W V := by
  rw [freeModShuffle_braiding_at',
    reassoc_of% (leftUnitorInv_braiding_eo L)]

/-- The braiding at the odd-even family. -/
theorem freeModShuffle_braiding_oe
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R]
    (V W : D) (m : L.obj ⟶ R ⊗ V)
    (n : 𝟙_ D ⟶ R ⊗ W) :
    ((ρ_ L.obj).inv ≫ (m ⊗ₘ n) ≫ freeModShuffle R V W) ≫
        R ◁ (β_ V W).hom
      = (λ_ L.obj).inv ≫ (n ⊗ₘ m) ≫ freeModShuffle R W V := by
  rw [freeModShuffle_braiding_at',
    reassoc_of% (rightUnitorInv_braiding_oe L)]

end Families

/-! ## The fibre functor and its comparison data -/

section Fibre

variable {D : Type u}

open SuperCommAlgebra.Mod

/-- **The fibre functor over an algebra**: base change to the
algebra followed by realization. -/
noncomputable def fibreOver
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R] :
    D ⥤ (gammaAlgebra D L R).Mod :=
  freeModFunctor R ⋙ gammaModuleFunctor L R

/-- Realization of a base-changed morphism, in even degree. -/
theorem gammaFunMap_freeModMap_evenMap
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R]
    {V W : D} (f : V ⟶ W)
    (m : 𝟙_ D ⟶ (freeMod R V).X) :
    (gammaFunMap L R (freeModMap R f)).evenMap m = m ≫ R ◁ f :=
  rfl

/-- Realization of a base-changed morphism, in odd degree. -/
theorem gammaFunMap_freeModMap_oddMap
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R]
    {V W : D} (f : V ⟶ W)
    (m : L.obj ⟶ (freeMod R V).X) :
    (gammaFunMap L R (freeModMap R f)).oddMap m = m ≫ R ◁ f :=
  rfl

/-! ## Associativity -/

private theorem fibreTensorComp_EE
    {S : SuperCommAlgebra.{v, v}} {M M' N P Q : S.Mod.{v, v, v, v}}
    (f : M ⟶ M') (g : M'.tensor N ⟶ P) (h : P ⟶ Q)
    (m : M.even) (n : N.even) :
    (SuperCommAlgebra.Mod.tensorHom f (𝟙 N) ≫ g ≫ h).evenMap (tmulEE M N m n) =
      h.evenMap (g.evenMap (tmulEE M' N (f.evenMap m) n)) := by
  simp only [comp_evenMap, LinearMap.comp_apply, tensorHom_evenMap_tmulEE, id_evenMap,
    LinearMap.id_coe, id_eq]

private theorem fibreTensorComp_EO
    {S : SuperCommAlgebra.{v, v}} {M M' N P Q : S.Mod.{v, v, v, v}}
    (f : M ⟶ M') (g : M'.tensor N ⟶ P) (h : P ⟶ Q)
    (m : M.even) (n : N.odd) :
    (SuperCommAlgebra.Mod.tensorHom f (𝟙 N) ≫ g ≫ h).oddMap (tmulEO M N m n) =
      h.oddMap (g.oddMap (tmulEO M' N (f.evenMap m) n)) := by
  simp only [comp_oddMap, LinearMap.comp_apply, tensorHom_oddMap_tmulEO, id_oddMap,
    LinearMap.id_coe, id_eq]

private theorem fibreTensorComp_OE
    {S : SuperCommAlgebra.{v, v}} {M M' N P Q : S.Mod.{v, v, v, v}}
    (f : M ⟶ M') (g : M'.tensor N ⟶ P) (h : P ⟶ Q)
    (m : M.odd) (n : N.even) :
    (SuperCommAlgebra.Mod.tensorHom f (𝟙 N) ≫ g ≫ h).oddMap (tmulOE M N m n) =
      h.oddMap (g.oddMap (tmulOE M' N (f.oddMap m) n)) := by
  simp only [comp_oddMap, LinearMap.comp_apply, tensorHom_oddMap_tmulOE, id_evenMap,
    LinearMap.id_coe, id_eq]

private theorem fibreTensorComp_OO
    {S : SuperCommAlgebra.{v, v}} {M M' N P Q : S.Mod.{v, v, v, v}}
    (f : M ⟶ M') (g : M'.tensor N ⟶ P) (h : P ⟶ Q)
    (m : M.odd) (n : N.odd) :
    (SuperCommAlgebra.Mod.tensorHom f (𝟙 N) ≫ g ≫ h).evenMap (tmulOO M N m n) =
      h.evenMap (g.evenMap (tmulOO M' N (f.oddMap m) n)) := by
  simp only [comp_evenMap, LinearMap.comp_apply, tensorHom_evenMap_tmulOO, id_oddMap,
    LinearMap.id_coe, id_eq]

private theorem fibreAssocTensorComp_EEE
    {S : SuperCommAlgebra.{v, v}} {M N P Q T : S.Mod.{v, v, v, v}}
    (f : N.tensor P ⟶ Q) (g : M.tensor Q ⟶ T)
    (m : M.even) (n : N.even)
    (p : P.even) :
    (assocHom M N P ≫ SuperCommAlgebra.Mod.tensorHom (𝟙 M) f ≫ g).evenMap
        (tmulEE (M.tensor N) P (tmulEE M N m n) p) =
      g.evenMap (tmulEE M Q m (f.evenMap (tmulEE N P n p))) := by
  simp only [comp_evenMap, LinearMap.comp_apply, tensorHom_evenMap_tmulEE,
    assocHom_evenMap_tmulEE, assocFee_tmulEE, id_evenMap, LinearMap.id_coe, id_eq]

private theorem fibreAssocTensorComp_EEO
    {S : SuperCommAlgebra.{v, v}} {M N P Q T : S.Mod.{v, v, v, v}}
    (f : N.tensor P ⟶ Q) (g : M.tensor Q ⟶ T)
    (m : M.even) (n : N.even)
    (p : P.odd) :
    (assocHom M N P ≫ SuperCommAlgebra.Mod.tensorHom (𝟙 M) f ≫ g).oddMap
        (tmulEO (M.tensor N) P (tmulEE M N m n) p) =
      g.oddMap (tmulEO M Q m (f.oddMap (tmulEO N P n p))) := by
  simp only [comp_oddMap, LinearMap.comp_apply, tensorHom_oddMap_tmulEO, assocHom_oddMap_tmulEO,
    assocFeo_tmulEE, id_evenMap, LinearMap.id_coe, id_eq]

private theorem fibreAssocTensorComp_EOE
    {S : SuperCommAlgebra.{v, v}} {M N P Q T : S.Mod.{v, v, v, v}}
    (f : N.tensor P ⟶ Q) (g : M.tensor Q ⟶ T)
    (m : M.even) (n : N.odd)
    (p : P.even) :
    (assocHom M N P ≫ SuperCommAlgebra.Mod.tensorHom (𝟙 M) f ≫ g).oddMap
        (tmulOE (M.tensor N) P (tmulEO M N m n) p) =
      g.oddMap (tmulEO M Q m (f.oddMap (tmulOE N P n p))) := by
  simp only [comp_oddMap, LinearMap.comp_apply, tensorHom_oddMap_tmulEO, assocHom_oddMap_tmulOE,
    assocFoe_tmulEO, id_evenMap, LinearMap.id_coe, id_eq]

private theorem fibreAssocTensorComp_EOO
    {S : SuperCommAlgebra.{v, v}} {M N P Q T : S.Mod.{v, v, v, v}}
    (f : N.tensor P ⟶ Q) (g : M.tensor Q ⟶ T)
    (m : M.even) (n : N.odd)
    (p : P.odd) :
    (assocHom M N P ≫ SuperCommAlgebra.Mod.tensorHom (𝟙 M) f ≫ g).evenMap
        (tmulOO (M.tensor N) P (tmulEO M N m n) p) =
      g.evenMap (tmulEE M Q m (f.evenMap (tmulOO N P n p))) := by
  simp only [comp_evenMap, LinearMap.comp_apply, tensorHom_evenMap_tmulEE,
    assocHom_evenMap_tmulOO, assocFoo_tmulEO, id_evenMap, LinearMap.id_coe, id_eq]

private theorem fibreAssocTensorComp_OEE
    {S : SuperCommAlgebra.{v, v}} {M N P Q T : S.Mod.{v, v, v, v}}
    (f : N.tensor P ⟶ Q) (g : M.tensor Q ⟶ T)
    (m : M.odd) (n : N.even)
    (p : P.even) :
    (assocHom M N P ≫ SuperCommAlgebra.Mod.tensorHom (𝟙 M) f ≫ g).oddMap
        (tmulOE (M.tensor N) P (tmulOE M N m n) p) =
      g.oddMap (tmulOE M Q m (f.evenMap (tmulEE N P n p))) := by
  simp only [comp_oddMap, LinearMap.comp_apply, tensorHom_oddMap_tmulOE, assocHom_oddMap_tmulOE,
    assocFoe_tmulOE, id_oddMap, LinearMap.id_coe, id_eq]

private theorem fibreAssocTensorComp_OEO
    {S : SuperCommAlgebra.{v, v}} {M N P Q T : S.Mod.{v, v, v, v}}
    (f : N.tensor P ⟶ Q) (g : M.tensor Q ⟶ T)
    (m : M.odd) (n : N.even)
    (p : P.odd) :
    (assocHom M N P ≫ SuperCommAlgebra.Mod.tensorHom (𝟙 M) f ≫ g).evenMap
        (tmulOO (M.tensor N) P (tmulOE M N m n) p) =
      g.evenMap (tmulOO M Q m (f.oddMap (tmulEO N P n p))) := by
  simp only [comp_evenMap, LinearMap.comp_apply, tensorHom_evenMap_tmulOO,
    assocHom_evenMap_tmulOO, assocFoo_tmulOE, id_oddMap, LinearMap.id_coe, id_eq]

private theorem fibreAssocTensorComp_OOE
    {S : SuperCommAlgebra.{v, v}} {M N P Q T : S.Mod.{v, v, v, v}}
    (f : N.tensor P ⟶ Q) (g : M.tensor Q ⟶ T)
    (m : M.odd) (n : N.odd)
    (p : P.even) :
    (assocHom M N P ≫ SuperCommAlgebra.Mod.tensorHom (𝟙 M) f ≫ g).evenMap
        (tmulEE (M.tensor N) P (tmulOO M N m n) p) =
      g.evenMap (tmulOO M Q m (f.oddMap (tmulOE N P n p))) := by
  simp only [comp_evenMap, LinearMap.comp_apply, tensorHom_evenMap_tmulOO,
    assocHom_evenMap_tmulEE, assocFee_tmulOO, id_oddMap, LinearMap.id_coe, id_eq]

private theorem fibreAssocTensorComp_OOO
    {S : SuperCommAlgebra.{v, v}} {M N P Q T : S.Mod.{v, v, v, v}}
    (f : N.tensor P ⟶ Q) (g : M.tensor Q ⟶ T)
    (m : M.odd) (n : N.odd)
    (p : P.odd) :
    (assocHom M N P ≫ SuperCommAlgebra.Mod.tensorHom (𝟙 M) f ≫ g).oddMap
        (tmulEO (M.tensor N) P (tmulOO M N m n) p) =
      g.oddMap (tmulOE M Q m (f.evenMap (tmulOO N P n p))) := by
  simp only [comp_oddMap, LinearMap.comp_apply, tensorHom_oddMap_tmulOE, assocHom_oddMap_tmulEO,
    assocFeo_tmulOO, id_oddMap, LinearMap.id_coe, id_eq]

/- Keep intermediate computations in bundled module types, so rewriting does not repeatedly
unfold the module instance dictionaries. The final coherence step unfolds the products once. -/
private noncomputable def fibreProductEE
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D]
    (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R] (V W : D)
    (m : (gammaModule D L R (freeMod R V).X).even)
    (n : (gammaModule D L R (freeMod R W).X).even) :
    (gammaModule D L R (freeMod R (V ⊗ W)).X).even :=
  (λ_ (𝟙_ D)).inv ≫ (m ⊗ₘ n) ≫ freeModShuffle R V W

private noncomputable def fibreProductOO
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D]
    (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R] (V W : D)
    (m : (gammaModule D L R (freeMod R V).X).odd)
    (n : (gammaModule D L R (freeMod R W).X).odd) :
    (gammaModule D L R (freeMod R (V ⊗ W)).X).even :=
  L.sq.inv ≫ (m ⊗ₘ n) ≫ freeModShuffle R V W

private noncomputable def fibreProductEO
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D]
    (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R] (V W : D)
    (m : (gammaModule D L R (freeMod R V).X).even)
    (n : (gammaModule D L R (freeMod R W).X).odd) :
    (gammaModule D L R (freeMod R (V ⊗ W)).X).odd :=
  (λ_ L.obj).inv ≫ (m ⊗ₘ n) ≫ freeModShuffle R V W

private noncomputable def fibreProductOE
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D]
    (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R] (V W : D)
    (m : (gammaModule D L R (freeMod R V).X).odd)
    (n : (gammaModule D L R (freeMod R W).X).even) :
    (gammaModule D L R (freeMod R (V ⊗ W)).X).odd :=
  (ρ_ L.obj).inv ≫ (m ⊗ₘ n) ≫ freeModShuffle R V W

private noncomputable def fibreMapEven
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D]
    (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R] {V W : D}
    (f : V ⟶ W) (m : (gammaModule D L R (freeMod R V).X).even) :
    (gammaModule D L R (freeMod R W).X).even := m ≫ R ◁ f

private noncomputable def fibreMapOdd
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D]
    (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R] {V W : D}
    (f : V ⟶ W) (m : (gammaModule D L R (freeMod R V).X).odd) :
    (gammaModule D L R (freeMod R W).X).odd := m ≫ R ◁ f

private theorem typedFibreMuEE
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R] (V W : D)
    (m : (gammaModule D L R (freeMod R V).X).even)
    (n : (gammaModule D L R (freeMod R W).X).even) :
    (fibreMu L R V W).evenMap
      (tmulEE (gammaModule D L R (freeMod R V).X)
        (gammaModule D L R (freeMod R W).X) m n) = fibreProductEE L R V W m n :=
  fibreMu_evenMap_tmulEE L R V W m n

private theorem typedFibreMuOO
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R] (V W : D)
    (m : (gammaModule D L R (freeMod R V).X).odd)
    (n : (gammaModule D L R (freeMod R W).X).odd) :
    (fibreMu L R V W).evenMap
      (tmulOO (gammaModule D L R (freeMod R V).X)
        (gammaModule D L R (freeMod R W).X) m n) = fibreProductOO L R V W m n :=
  fibreMu_evenMap_tmulOO L R V W m n

private theorem typedFibreMuEO
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R] (V W : D)
    (m : (gammaModule D L R (freeMod R V).X).even)
    (n : (gammaModule D L R (freeMod R W).X).odd) :
    (fibreMu L R V W).oddMap
      (tmulEO (gammaModule D L R (freeMod R V).X)
        (gammaModule D L R (freeMod R W).X) m n) = fibreProductEO L R V W m n :=
  fibreMu_oddMap_tmulEO L R V W m n

private theorem typedFibreMuOE
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R] (V W : D)
    (m : (gammaModule D L R (freeMod R V).X).odd)
    (n : (gammaModule D L R (freeMod R W).X).even) :
    (fibreMu L R V W).oddMap
      (tmulOE (gammaModule D L R (freeMod R V).X)
        (gammaModule D L R (freeMod R W).X) m n) = fibreProductOE L R V W m n :=
  fibreMu_oddMap_tmulOE L R V W m n

private theorem typedFibreMapEven
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D]
    (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R] {V W : D}
    (f : V ⟶ W) (m : (gammaModule D L R (freeMod R V).X).even) :
    (gammaFunMap L R (freeModMap R f)).evenMap m = fibreMapEven L R f m := rfl

private theorem typedFibreMapOdd
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D]
    (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R] {V W : D}
    (f : V ⟶ W) (m : (gammaModule D L R (freeMod R V).X).odd) :
    (gammaFunMap L R (freeModMap R f)).oddMap m = fibreMapOdd L R f m := rfl

private theorem fibreMu_associativity_eee
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R]
    (V W Z : D) :
    ∀ m n p,
      (SuperCommAlgebra.Mod.tensorHom (fibreMu L R V W)
          (𝟙 (gammaModule D L R (freeMod R Z).X)) ≫
        fibreMu L R (V ⊗ W) Z ≫
          gammaFunMap L R (freeModMap R (α_ V W Z).hom)).evenMap (tmulEE ((gammaModule D L R
            (freeMod R V).X).tensor (gammaModule D L R (freeMod R W).X)) (gammaModule D L R
            (freeMod R Z).X)
          (tmulEE (gammaModule D L R (freeMod R V).X) (gammaModule D L R (freeMod R W).X) m n) p) =
      (assocHom (gammaModule D L R (freeMod R V).X)
            (gammaModule D L R (freeMod R W).X)
            (gammaModule D L R (freeMod R Z).X) ≫
          SuperCommAlgebra.Mod.tensorHom
              (𝟙 (gammaModule D L R (freeMod R V).X))
              (fibreMu L R W Z) ≫
            fibreMu L R V (W ⊗ Z)).evenMap (tmulEE ((gammaModule D L R (freeMod R V).X).tensor
              (gammaModule D L R (freeMod R W).X)) (gammaModule D L R (freeMod R Z).X)
          (tmulEE (gammaModule D L R (freeMod R V).X) (gammaModule D L R (freeMod R W).X) m n)
            p) := by
  intro m n p
  rw [fibreTensorComp_EE, fibreAssocTensorComp_EEE]
  rw [typedFibreMuEE, typedFibreMuEE, typedFibreMuEE, typedFibreMuEE,
    typedFibreMapEven]
  refine freeModShuffle_assoc_at' R _ _ _ _ ?_ m n p
  monoidal

private theorem fibreMu_associativity_ooe
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R]
    (V W Z : D) :
    ∀ m n p,
      (SuperCommAlgebra.Mod.tensorHom (fibreMu L R V W)
          (𝟙 (gammaModule D L R (freeMod R Z).X)) ≫
        fibreMu L R (V ⊗ W) Z ≫
          gammaFunMap L R (freeModMap R (α_ V W Z).hom)).evenMap (tmulEE ((gammaModule D L R
            (freeMod R V).X).tensor (gammaModule D L R (freeMod R W).X)) (gammaModule D L R
            (freeMod R Z).X)
          (tmulOO (gammaModule D L R (freeMod R V).X) (gammaModule D L R (freeMod R W).X) m n) p) =
      (assocHom (gammaModule D L R (freeMod R V).X)
            (gammaModule D L R (freeMod R W).X)
            (gammaModule D L R (freeMod R Z).X) ≫
          SuperCommAlgebra.Mod.tensorHom
              (𝟙 (gammaModule D L R (freeMod R V).X))
              (fibreMu L R W Z) ≫
            fibreMu L R V (W ⊗ Z)).evenMap (tmulEE ((gammaModule D L R (freeMod R V).X).tensor
              (gammaModule D L R (freeMod R W).X)) (gammaModule D L R (freeMod R Z).X)
          (tmulOO (gammaModule D L R (freeMod R V).X) (gammaModule D L R (freeMod R W).X) m n)
            p) := by
  intro m n p
  rw [fibreTensorComp_EE, fibreAssocTensorComp_OOE]
  rw [typedFibreMuOO, typedFibreMuEE, typedFibreMuOE, typedFibreMuOO,
    typedFibreMapEven]
  refine freeModShuffle_assoc_at' R _ _ _ _ ?_ m n p
  have hc : (ρ_ (L.obj ⊗ L.obj)).inv ≫
      (α_ L.obj L.obj (𝟙_ D)).hom =
      L.obj ◁ (ρ_ L.obj).inv := by monoidal
  rw [unitors_inv_equal, ← Category.assoc,
    ← rightUnitor_inv_naturality, Category.assoc, hc]

private theorem fibreMu_associativity_eoo
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R]
    (V W Z : D) :
    ∀ m n p,
      (SuperCommAlgebra.Mod.tensorHom (fibreMu L R V W)
          (𝟙 (gammaModule D L R (freeMod R Z).X)) ≫
        fibreMu L R (V ⊗ W) Z ≫
          gammaFunMap L R (freeModMap R (α_ V W Z).hom)).evenMap (tmulOO ((gammaModule D L R
            (freeMod R V).X).tensor (gammaModule D L R (freeMod R W).X)) (gammaModule D L R
            (freeMod R Z).X)
          (tmulEO (gammaModule D L R (freeMod R V).X) (gammaModule D L R (freeMod R W).X) m n) p) =
      (assocHom (gammaModule D L R (freeMod R V).X)
            (gammaModule D L R (freeMod R W).X)
            (gammaModule D L R (freeMod R Z).X) ≫
          SuperCommAlgebra.Mod.tensorHom
              (𝟙 (gammaModule D L R (freeMod R V).X))
              (fibreMu L R W Z) ≫
            fibreMu L R V (W ⊗ Z)).evenMap (tmulOO ((gammaModule D L R (freeMod R V).X).tensor
              (gammaModule D L R (freeMod R W).X)) (gammaModule D L R (freeMod R Z).X)
          (tmulEO (gammaModule D L R (freeMod R V).X) (gammaModule D L R (freeMod R W).X) m n)
            p) := by
  intro m n p
  rw [fibreTensorComp_OO, fibreAssocTensorComp_EOO]
  rw [typedFibreMuEO, typedFibreMuOO, typedFibreMuOO, typedFibreMuEE,
    typedFibreMapEven]
  refine freeModShuffle_assoc_at' R _ _ _ _ ?_ m n p
  have hc : (λ_ L.obj).inv ▷ L.obj ≫
      (α_ (𝟙_ D) L.obj L.obj).hom =
      (λ_ (L.obj ⊗ L.obj)).inv := by monoidal
  rw [hc]
  exact leftUnitor_inv_naturality L.sq.inv

private theorem fibreMu_associativity_oeo
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R]
    (V W Z : D) :
    ∀ m n p,
      (SuperCommAlgebra.Mod.tensorHom (fibreMu L R V W)
          (𝟙 (gammaModule D L R (freeMod R Z).X)) ≫
        fibreMu L R (V ⊗ W) Z ≫
          gammaFunMap L R (freeModMap R (α_ V W Z).hom)).evenMap (tmulOO ((gammaModule D L R
            (freeMod R V).X).tensor (gammaModule D L R (freeMod R W).X)) (gammaModule D L R
            (freeMod R Z).X)
          (tmulOE (gammaModule D L R (freeMod R V).X) (gammaModule D L R (freeMod R W).X) m n) p) =
      (assocHom (gammaModule D L R (freeMod R V).X)
            (gammaModule D L R (freeMod R W).X)
            (gammaModule D L R (freeMod R Z).X) ≫
          SuperCommAlgebra.Mod.tensorHom
              (𝟙 (gammaModule D L R (freeMod R V).X))
              (fibreMu L R W Z) ≫
            fibreMu L R V (W ⊗ Z)).evenMap (tmulOO ((gammaModule D L R (freeMod R V).X).tensor
              (gammaModule D L R (freeMod R W).X)) (gammaModule D L R (freeMod R Z).X)
          (tmulOE (gammaModule D L R (freeMod R V).X) (gammaModule D L R (freeMod R W).X) m n)
            p) := by
  intro m n p
  rw [fibreTensorComp_OO, fibreAssocTensorComp_OEO]
  rw [typedFibreMuOE, typedFibreMuOO, typedFibreMuEO, typedFibreMuOO,
    typedFibreMapEven]
  refine freeModShuffle_assoc_at' R _ _ _ _ ?_ m n p
  have hc : (ρ_ L.obj).inv ▷ L.obj ≫
      (α_ L.obj (𝟙_ D) L.obj).hom =
      L.obj ◁ (λ_ L.obj).inv := by monoidal
  rw [hc]

private theorem fibreMu_associativity_eeo
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R]
    (V W Z : D) :
    ∀ m n p,
      (SuperCommAlgebra.Mod.tensorHom (fibreMu L R V W)
          (𝟙 (gammaModule D L R (freeMod R Z).X)) ≫
        fibreMu L R (V ⊗ W) Z ≫
          gammaFunMap L R (freeModMap R (α_ V W Z).hom)).oddMap (tmulEO ((gammaModule D L R
            (freeMod R V).X).tensor (gammaModule D L R (freeMod R W).X)) (gammaModule D L R
            (freeMod R Z).X)
          (tmulEE (gammaModule D L R (freeMod R V).X) (gammaModule D L R (freeMod R W).X) m n) p) =
      (assocHom (gammaModule D L R (freeMod R V).X)
            (gammaModule D L R (freeMod R W).X)
            (gammaModule D L R (freeMod R Z).X) ≫
          SuperCommAlgebra.Mod.tensorHom
              (𝟙 (gammaModule D L R (freeMod R V).X))
              (fibreMu L R W Z) ≫
            fibreMu L R V (W ⊗ Z)).oddMap (tmulEO ((gammaModule D L R (freeMod R V).X).tensor
              (gammaModule D L R (freeMod R W).X)) (gammaModule D L R (freeMod R Z).X)
          (tmulEE (gammaModule D L R (freeMod R V).X) (gammaModule D L R (freeMod R W).X) m n)
            p) := by
  intro m n p
  rw [fibreTensorComp_EO, fibreAssocTensorComp_EEO]
  rw [typedFibreMuEE, typedFibreMuEO, typedFibreMuEO, typedFibreMuEO,
    typedFibreMapOdd]
  refine freeModShuffle_assoc_at' R _ _ _ _ ?_ m n p
  monoidal

private theorem fibreMu_associativity_ooo
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R]
    (V W Z : D) :
    ∀ m n p,
      (SuperCommAlgebra.Mod.tensorHom (fibreMu L R V W)
          (𝟙 (gammaModule D L R (freeMod R Z).X)) ≫
        fibreMu L R (V ⊗ W) Z ≫
          gammaFunMap L R (freeModMap R (α_ V W Z).hom)).oddMap (tmulEO ((gammaModule D L R
            (freeMod R V).X).tensor (gammaModule D L R (freeMod R W).X)) (gammaModule D L R
            (freeMod R Z).X)
          (tmulOO (gammaModule D L R (freeMod R V).X) (gammaModule D L R (freeMod R W).X) m n) p) =
      (assocHom (gammaModule D L R (freeMod R V).X)
            (gammaModule D L R (freeMod R W).X)
            (gammaModule D L R (freeMod R Z).X) ≫
          SuperCommAlgebra.Mod.tensorHom
              (𝟙 (gammaModule D L R (freeMod R V).X))
              (fibreMu L R W Z) ≫
            fibreMu L R V (W ⊗ Z)).oddMap (tmulEO ((gammaModule D L R (freeMod R V).X).tensor
              (gammaModule D L R (freeMod R W).X)) (gammaModule D L R (freeMod R Z).X)
          (tmulOO (gammaModule D L R (freeMod R V).X) (gammaModule D L R (freeMod R W).X) m n)
            p) := by
  intro m n p
  rw [fibreTensorComp_EO, fibreAssocTensorComp_OOO]
  rw [typedFibreMuOO, typedFibreMuEO, typedFibreMuOO, typedFibreMuOE,
    typedFibreMapOdd]
  refine freeModShuffle_assoc_at' R _ _ _ _ ?_ m n p
  have h2 : L.sq.inv ▷ L.obj ≫ (α_ L.obj L.obj L.obj).hom =
      (λ_ L.obj).hom ≫ (ρ_ L.obj).inv ≫
        L.obj ◁ L.sq.inv := by
    rw [← reassoc_of% L.evaluation_coevaluation,
      ← MonoidalCategory.whiskerLeft_comp, Iso.hom_inv_id,
      MonoidalCategory.whiskerLeft_id, Category.comp_id]
  rw [h2, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

private theorem fibreMu_associativity_eoe
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R]
    (V W Z : D) :
    ∀ m n p,
      (SuperCommAlgebra.Mod.tensorHom (fibreMu L R V W)
          (𝟙 (gammaModule D L R (freeMod R Z).X)) ≫
        fibreMu L R (V ⊗ W) Z ≫
          gammaFunMap L R (freeModMap R (α_ V W Z).hom)).oddMap (tmulOE ((gammaModule D L R
            (freeMod R V).X).tensor (gammaModule D L R (freeMod R W).X)) (gammaModule D L R
            (freeMod R Z).X)
          (tmulEO (gammaModule D L R (freeMod R V).X) (gammaModule D L R (freeMod R W).X) m n) p) =
      (assocHom (gammaModule D L R (freeMod R V).X)
            (gammaModule D L R (freeMod R W).X)
            (gammaModule D L R (freeMod R Z).X) ≫
          SuperCommAlgebra.Mod.tensorHom
              (𝟙 (gammaModule D L R (freeMod R V).X))
              (fibreMu L R W Z) ≫
            fibreMu L R V (W ⊗ Z)).oddMap (tmulOE ((gammaModule D L R (freeMod R V).X).tensor
              (gammaModule D L R (freeMod R W).X)) (gammaModule D L R (freeMod R Z).X)
          (tmulEO (gammaModule D L R (freeMod R V).X) (gammaModule D L R (freeMod R W).X) m n)
            p) := by
  intro m n p
  rw [fibreTensorComp_OE, fibreAssocTensorComp_EOE]
  rw [typedFibreMuEO, typedFibreMuOE, typedFibreMuOE, typedFibreMuEO,
    typedFibreMapOdd]
  refine freeModShuffle_assoc_at' R _ _ _ _ ?_ m n p
  monoidal

private theorem fibreMu_associativity_oee
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R]
    (V W Z : D) :
    ∀ m n p,
      (SuperCommAlgebra.Mod.tensorHom (fibreMu L R V W)
          (𝟙 (gammaModule D L R (freeMod R Z).X)) ≫
        fibreMu L R (V ⊗ W) Z ≫
          gammaFunMap L R (freeModMap R (α_ V W Z).hom)).oddMap (tmulOE ((gammaModule D L R
            (freeMod R V).X).tensor (gammaModule D L R (freeMod R W).X)) (gammaModule D L R
            (freeMod R Z).X)
          (tmulOE (gammaModule D L R (freeMod R V).X) (gammaModule D L R (freeMod R W).X) m n) p) =
      (assocHom (gammaModule D L R (freeMod R V).X)
            (gammaModule D L R (freeMod R W).X)
            (gammaModule D L R (freeMod R Z).X) ≫
          SuperCommAlgebra.Mod.tensorHom
              (𝟙 (gammaModule D L R (freeMod R V).X))
              (fibreMu L R W Z) ≫
            fibreMu L R V (W ⊗ Z)).oddMap (tmulOE ((gammaModule D L R (freeMod R V).X).tensor
              (gammaModule D L R (freeMod R W).X)) (gammaModule D L R (freeMod R Z).X)
          (tmulOE (gammaModule D L R (freeMod R V).X) (gammaModule D L R (freeMod R W).X) m n)
            p) := by
  intro m n p
  rw [fibreTensorComp_OE, fibreAssocTensorComp_OEE]
  rw [typedFibreMuOE, typedFibreMuOE, typedFibreMuEE, typedFibreMuOE,
    typedFibreMapOdd]
  refine freeModShuffle_assoc_at' R _ _ _ _ ?_ m n p
  monoidal

/-- **Associativity of the monoidal comparison of the fibre
functor**: the two ways of comparing a threefold tensor product
agree, up to the associator of the super modules and the
reassociation of the three objects. -/
theorem fibreMu_associativity
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R]
    (V W Z : D) :
    SuperCommAlgebra.Mod.tensorHom (fibreMu L R V W)
          (𝟙 (gammaModule D L R (freeMod R Z).X)) ≫
        fibreMu L R (V ⊗ W) Z ≫
          gammaFunMap L R (freeModMap R (α_ V W Z).hom)
      = assocHom (gammaModule D L R (freeMod R V).X)
            (gammaModule D L R (freeMod R W).X)
            (gammaModule D L R (freeMod R Z).X) ≫
          SuperCommAlgebra.Mod.tensorHom
              (𝟙 (gammaModule D L R (freeMod R V).X))
              (fibreMu L R W Z) ≫
            fibreMu L R V (W ⊗ Z) := by
  exact hom_ext₃
    (fibreMu_associativity_eee L R V W Z)
    (fibreMu_associativity_ooe L R V W Z)
    (fibreMu_associativity_eoo L R V W Z)
    (fibreMu_associativity_oeo L R V W Z)
    (fibreMu_associativity_eeo L R V W Z)
    (fibreMu_associativity_ooo L R V W Z)
    (fibreMu_associativity_eoe L R V W Z)
    (fibreMu_associativity_oee L R V W Z)

/-! ## Unitality -/

/-- **Left unitality of the monoidal comparison of the fibre
functor**: the unit comparison in the first slot is the left
unitor of the super modules.  No sign appears. -/
theorem fibreMu_left_unitality
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R]
    (V : D) :
    leftUnitorHom (gammaModule D L R (freeMod R V).X)
      = SuperCommAlgebra.Mod.tensorHom (fibreEps L R)
            (𝟙 (gammaModule D L R (freeMod R V).X)) ≫
          fibreMu L R (𝟙_ D) V ≫
            gammaFunMap L R (freeModMap R (λ_ V).hom) := by
  refine hom_ext (fun x m => ?_) (fun u m => ?_) (fun x m => ?_)
    (fun u m => ?_)
  · erw [leftUnitorHom_evenMap_tmulEE, comp_evenMap_apply,
      comp_evenMap_apply, tensorHom_evenMap_tmulEE,
      typedFibreMuEE, typedFibreMapEven]
    exact (freeModShuffle_unit_left_at' R (λ_ (𝟙_ D)).inv x m).symm
  · erw [leftUnitorHom_evenMap_tmulOO, comp_evenMap_apply,
      comp_evenMap_apply, tensorHom_evenMap_tmulOO,
      typedFibreMuOO, typedFibreMapEven]
    exact (freeModShuffle_unit_left_at' R L.sq.inv u m).symm
  · erw [leftUnitorHom_oddMap_tmulEO, comp_oddMap_apply,
      comp_oddMap_apply, tensorHom_oddMap_tmulEO,
      typedFibreMuEO, typedFibreMapOdd]
    exact (freeModShuffle_unit_left_at' R (λ_ L.obj).inv x m).symm
  · erw [leftUnitorHom_oddMap_tmulOE, comp_oddMap_apply,
      comp_oddMap_apply, tensorHom_oddMap_tmulOE,
      typedFibreMuOE, typedFibreMapOdd]
    exact (freeModShuffle_unit_left_at' R (ρ_ L.obj).inv u m).symm

/-- **Right unitality of the monoidal comparison of the fibre
functor**: the unit comparison in the second slot is the right
unitor of the super modules.  The Koszul sign of the odd-odd block
of the right unitor is `RS.freeModShuffle_unit_right_oo`, and it is
supplied by `RS.oddLine_sq_inv_braiding`. -/
theorem fibreMu_right_unitality
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R]
    (V : D) :
    rightUnitorHom (gammaModule D L R (freeMod R V).X)
      = SuperCommAlgebra.Mod.tensorHom
            (𝟙 (gammaModule D L R (freeMod R V).X))
            (fibreEps L R) ≫
          fibreMu L R V (𝟙_ D) ≫
            gammaFunMap L R (freeModMap R (ρ_ V).hom) := by
  refine hom_ext (fun m x => ?_) (fun m u => ?_) (fun m u => ?_)
    (fun m x => ?_)
  · erw [rightUnitorHom_evenMap_tmulEE, comp_evenMap_apply,
      comp_evenMap_apply, tensorHom_evenMap_tmulEE,
      typedFibreMuEE, typedFibreMapEven]
    exact (freeModShuffle_unit_right_ee R V m x).symm
  · erw [rightUnitorHom_evenMap_tmulOO, comp_evenMap_apply,
      comp_evenMap_apply, tensorHom_evenMap_tmulOO,
      typedFibreMuOO, typedFibreMapEven]
    exact (freeModShuffle_unit_right_oo L R V m u).symm
  · erw [rightUnitorHom_oddMap_tmulEO, comp_oddMap_apply,
      comp_oddMap_apply, tensorHom_oddMap_tmulEO,
      typedFibreMuEO, typedFibreMapOdd]
    exact (freeModShuffle_unit_right_eo L R V m u).symm
  · erw [rightUnitorHom_oddMap_tmulOE, comp_oddMap_apply,
      comp_oddMap_apply, tensorHom_oddMap_tmulOE,
      typedFibreMuOE, typedFibreMapOdd]
    exact (freeModShuffle_unit_right_oe L R V m x).symm

/-! ## Compatibility with the braiding -/

/-- **The monoidal comparison of the fibre functor commutes with
the braiding**: swapping the two factors of the super-module
tensor product and comparing agrees with comparing and swapping
the two objects.  The Koszul sign of the odd-odd block of the
Koszul swap is `RS.freeModShuffle_braiding_oo`, and it is again
supplied by `RS.oddLine_sq_inv_braiding`. -/
theorem fibreMu_braided
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R]
    (V W : D) :
    braidingHom (gammaModule D L R (freeMod R V).X)
          (gammaModule D L R (freeMod R W).X) ≫ fibreMu L R W V
      = fibreMu L R V W ≫
          gammaFunMap L R (freeModMap R (β_ V W).hom) := by
  refine hom_ext (fun m n => ?_) (fun m n => ?_) (fun m n => ?_)
    (fun m n => ?_)
  · erw [comp_evenMap_apply, braidingHom_evenMap_tmulEE,
      typedFibreMuEE, comp_evenMap_apply,
      typedFibreMuEE, typedFibreMapEven]
    exact (freeModShuffle_braiding_ee R V W m n).symm
  · erw [comp_evenMap_apply, braidingHom_evenMap_tmulOO, map_neg,
      typedFibreMuOO, comp_evenMap_apply,
      typedFibreMuOO, typedFibreMapEven]
    exact (freeModShuffle_braiding_oo L R V W m n).symm
  · erw [comp_oddMap_apply, braidingHom_oddMap_tmulEO,
      typedFibreMuOE, comp_oddMap_apply,
      typedFibreMuEO, typedFibreMapOdd]
    exact (freeModShuffle_braiding_eo L R V W m n).symm
  · erw [comp_oddMap_apply, braidingHom_oddMap_tmulOE,
      typedFibreMuEO, comp_oddMap_apply,
      typedFibreMuOE, typedFibreMapOdd]
    exact (freeModShuffle_braiding_oe L R V W m n).symm

/-! ## The lax monoidal and lax braided structures -/

/-- **The fibre functor is lax monoidal**, with unit `RS.fibreEps`
and tensorator `RS.fibreMu`. -/
noncomputable instance fibreOverLaxMonoidal
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R] :
    (fibreOver L R).LaxMonoidal :=
  CategoryTheory.Functor.LaxMonoidal.ofTensorHom
    (F := fibreOver L R) (fibreEps L R) (fibreMu L R)
    (fun f g => fibreMu_naturality L R f g)
    (fun V W Z => fibreMu_associativity L R V W Z)
    (fun V => fibreMu_left_unitality L R V)
    (fun V => fibreMu_right_unitality L R V)

/-- The unit of the lax monoidal structure. -/
theorem fibreOver_ε [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R] :
    CategoryTheory.Functor.LaxMonoidal.ε (fibreOver L R)
      = fibreEps L R :=
  rfl

/-- The tensorator of the lax monoidal structure. -/
theorem fibreOver_μ [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R]
    (V W : D) :
    CategoryTheory.Functor.LaxMonoidal.μ (fibreOver L R) V W
      = fibreMu L R V W :=
  rfl

/-- **The fibre functor is lax braided**: its tensorator commutes
with the two symmetries. -/
noncomputable instance fibreOverLaxBraided
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R] :
    (fibreOver L R).LaxBraided where
  toLaxMonoidal := fibreOverLaxMonoidal L R
  braided V W := (fibreMu_braided L R V W).symm

end Fibre

end RS
