/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.CatTheory.TensorPow
public import LeanPool.RegtsSevenster.RS.Classical.Deligne.DoubledAbelian

/-!
# Deligne's growth and generation hypotheses in the doubling

`RS/Classical/Deligne/Doubling.lean` builds the ℤ/2-graded
doubling `Doubled A`, the faithful summing functor
`total : Doubled A ⥤ A`, `X ↦ X.even ⊞ X.odd` along which the
monoidal structure is induced, and the even embedding
`evenEmbed : A ⥤ Doubled A`.  This module transports two of
Deligne's hypotheses across that construction: moderate growth of
the lengths of tensor powers, and finite ⊗-generation.

Growth travels along the summing functor.  It is monoidal, so its
comparison isomorphisms assemble by induction into
`total.obj (Y ^ ⊗ N) ≅ (total.obj Y) ^ ⊗ N`; and it reflects the
subobject order — the graded components of a monomorphism are
monomorphisms, a biproduct of monomorphisms is a monomorphism, and
a factorisation of the summed subobjects splits back into its
matrix entries.  So a strictly increasing chain of subobjects
upstairs gives one of the same length downstairs, and the constants
that bound the growth of `total.obj Y` in `A` bound the growth of
`Y` in the doubling verbatim.

Generation travels along the diagonal embedding `dbl`,
`M ↦ (M, M)`, which is additive and preserves monomorphisms and
epimorphisms.  A super-object `Y` is a retract of
`dbl (Y.even ⊞ Y.odd)`, so a subquotient presentation of
`Y.even ⊞ Y.odd` downstairs presents both graded components at
once.  The generator taken upstairs is
`gen X = (X ⊞ Xᘁ ⊞ 𝟙_ A, 𝟙_ A)`: the ambient generator, its dual
and the unit in even degree, the unit in odd degree.  Its pure
tensor powers already contain the diagonal double of every mixed
power of `X` as a retract — read the word `X, …, X, (𝟙, 𝟙),
Xᘁ, …, Xᘁ` off the letters of `gen X`, the diagonal letter
spreading an even word over both degrees.  No dual is ever formed
in the doubling: the presentations produced here use mixed powers
with no dual factors at all.
-/

@[expose] public section

namespace RS

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe v u

noncomputable section

namespace Doubled

section Components

variable {A : Type u}

/-- The even component of a monomorphism of super-objects is a
monomorphism: a morphism killed by it is the even component of a
morphism killed by it. -/
theorem mono_evenHom [Category.{v} A] [Preadditive A]
    {S Z : Doubled A} (m : S ⟶ Z) [Mono m] :
    Mono (evenHom m) := by
  refine (Preadditive.mono_iff_cancel_zero _).2 fun T g hg => ?_
  have hzero : (homMk g 0 : (⟨T, S.odd⟩ : Doubled A) ⟶ S) ≫ m = 0 := by
    apply hom_ext
    · simpa using hg
    · simp
  have hg' := (Preadditive.mono_iff_cancel_zero m).1 ‹Mono m› _ _ hzero
  simpa using congrArg evenHom hg'

/-- The odd component of a monomorphism of super-objects is a
monomorphism. -/
theorem mono_oddHom [Category.{v} A] [Preadditive A]
    {S Z : Doubled A} (m : S ⟶ Z) [Mono m] :
    Mono (oddHom m) := by
  refine (Preadditive.mono_iff_cancel_zero _).2 fun T g hg => ?_
  have hzero : (homMk 0 g : (⟨S.even, T⟩ : Doubled A) ⟶ S) ≫ m = 0 := by
    apply hom_ext
    · simp
    · simpa using hg
  have hg' := (Preadditive.mono_iff_cancel_zero m).1 ‹Mono m› _ _ hzero
  simpa using congrArg oddHom hg'

/-- A morphism of super-objects with monomorphic components is a
monomorphism: morphisms are compared componentwise. -/
theorem mono_of_components [Category.{v} A] [Preadditive A]
    {S Z : Doubled A} (m : S ⟶ Z)
    (he : Mono (evenHom m)) (ho : Mono (oddHom m)) : Mono m := by
  refine (Preadditive.mono_of_cancel_zero _) fun g hg => ?_
  have he' : evenHom g = 0 :=
    (Preadditive.mono_iff_cancel_zero _).1 he _ _
      (by simpa using congrArg evenHom hg)
  have ho' : oddHom g = 0 :=
    (Preadditive.mono_iff_cancel_zero _).1 ho _ _
      (by simpa using congrArg oddHom hg)
  exact hom_ext (by simpa using he') (by simpa using ho')

/-- A morphism of super-objects with epimorphic components is an
epimorphism. -/
theorem epi_of_components [Category.{v} A] [Preadditive A]
    {S Z : Doubled A} (m : S ⟶ Z)
    (he : Epi (evenHom m)) (ho : Epi (oddHom m)) : Epi m := by
  refine (Preadditive.epi_of_cancel_zero _) fun g hg => ?_
  have he' : evenHom g = 0 :=
    (Preadditive.epi_iff_cancel_zero _).1 he _ _
      (by simpa using congrArg evenHom hg)
  have ho' : oddHom g = 0 :=
    (Preadditive.epi_iff_cancel_zero _).1 ho _ _
      (by simpa using congrArg oddHom hg)
  exact hom_ext (by simpa using he') (by simpa using ho')

end Components

section TotalMono

variable {A : Type u}

/-- A biproduct of two monomorphisms is a monomorphism: a morphism
killed by it is killed in each matrix entry. -/
theorem eq_zero_of_comp_biprod_map
    [Category.{v} A] [Preadditive A] [HasBinaryBiproducts A]
    {P M N M' N' : A}
    (g : P ⟶ M ⊞ N) {f₁ : M ⟶ M'} {f₂ : N ⟶ N'} (h₁ : Mono f₁)
    (h₂ : Mono f₂) (hg : g ≫ biprod.map f₁ f₂ = 0) : g = 0 := by
  have e₁ : g ≫ biprod.fst = 0 := by
    refine (Preadditive.mono_iff_cancel_zero _).1 h₁ _ _ ?_
    have h : g ≫ biprod.map f₁ f₂ ≫ biprod.fst = 0 := by
      rw [← Category.assoc, hg, Limits.zero_comp]
    simpa using h
  have e₂ : g ≫ biprod.snd = 0 := by
    refine (Preadditive.mono_iff_cancel_zero _).1 h₂ _ _ ?_
    have h : g ≫ biprod.map f₁ f₂ ≫ biprod.snd = 0 := by
      rw [← Category.assoc, hg, Limits.zero_comp]
    simpa using h
  exact biprod.hom_ext _ _ (by simpa using e₁) (by simpa using e₂)

/-- The summing functor preserves monomorphisms: on components a
monomorphism of super-objects is a pair of monomorphisms, and the
biproduct of two monomorphisms is one. -/
instance total_map_mono [Category.{v} A] [Preadditive A] [HasBinaryBiproducts A]
    {S Z : Doubled A} (m : S ⟶ Z) [Mono m] :
    Mono (total.map m) := by
  refine Preadditive.mono_of_cancel_zero _ ?_
  intro P g hg
  have hg' : g ≫ biprod.map (evenHom m) (oddHom m) = 0 := hg
  exact eq_zero_of_comp_biprod_map g (mono_evenHom m) (mono_oddHom m)
    hg'

/-- The diagonal matrix entries of a factorisation of one
biproduct of morphisms through another factor the two given
morphisms. -/
theorem diag_of_comp_biprod_map
    [Category.{v} A] [Preadditive A] [HasBinaryBiproducts A]
    {M N M' N' P Q : A}
    (u : M ⊞ N ⟶ M' ⊞ N') {t₁ : M' ⟶ P} {t₂ : N' ⟶ Q}
    {s₁ : M ⟶ P} {s₂ : N ⟶ Q}
    (hu : u ≫ biprod.map t₁ t₂ = biprod.map s₁ s₂) :
    (biprod.inl ≫ u ≫ biprod.fst) ≫ t₁ = s₁ ∧
      (biprod.inr ≫ u ≫ biprod.snd) ≫ t₂ = s₂ := by
  constructor
  · simpa using congrArg (fun w => biprod.inl ≫ w ≫ biprod.fst) hu
  · simpa using congrArg (fun w => biprod.inr ≫ w ≫ biprod.snd) hu

/-- A factorisation of the summed subobjects splits back into its
diagonal matrix entries, which assemble into a factorisation of the
subobjects themselves. -/
theorem le_of_total_comm
    [Category.{v} A] [Preadditive A] [HasBinaryBiproducts A]
    {Z : Doubled A} {S T : Subobject Z}
    (u : total.obj (S : Doubled A) ⟶ total.obj (T : Doubled A))
    (hu : u ≫ total.map T.arrow = total.map S.arrow) : S ≤ T := by
  have hu' : u ≫ biprod.map (evenHom T.arrow) (oddHom T.arrow) =
      biprod.map (evenHom S.arrow) (oddHom S.arrow) := hu
  obtain ⟨he, ho⟩ := diag_of_comp_biprod_map u hu'
  refine Subobject.le_of_comm (homMk (biprod.inl ≫ u ≫ biprod.fst)
    (biprod.inr ≫ u ≫ biprod.snd)) ?_
  exact hom_ext he ho

/-- The summing functor reflects the subobject order. -/
theorem le_of_total_le [Category.{v} A] [Preadditive A] [HasBinaryBiproducts A]
    {Z : Doubled A} {S T : Subobject Z}
    (h : Subobject.mk (total.map S.arrow) ≤
      Subobject.mk (total.map T.arrow)) : S ≤ T :=
  le_of_total_comm
    (Subobject.ofMkLEMk (total.map S.arrow) (total.map T.arrow) h)
    (Subobject.ofMkLEMk_comp h)

/-- Length in the doubling is length of the total object: a
strictly increasing chain of subobjects of `Z` maps to a strictly
increasing chain of subobjects of `total.obj Z`. -/
theorem lengthLE_of_total
    [Category.{v} A] [Preadditive A] [HasBinaryBiproducts A]
    {Z : Doubled A} {k : ℕ}
    (h : LengthLE (total.obj Z) k) : LengthLE Z k := by
  intro f hf
  refine h (fun i => Subobject.mk (total.map (f i).arrow)) ?_
  intro i j hij
  have hlt : f i < f j := hf hij
  have hle : Subobject.mk (total.map (f i).arrow) ≤
      Subobject.mk (total.map (f j).arrow) :=
    Subobject.mk_le_mk_of_comm
      (total.map (Subobject.ofLE _ _ hlt.le))
      (by rw [← CategoryTheory.Functor.map_comp,
        Subobject.ofLE_arrow])
  refine lt_of_le_of_ne hle fun heq => ?_
  exact hlt.ne
    (le_antisymm hlt.le (le_of_total_le (le_of_eq heq.symm)))

end TotalMono

section GrowthTransport

variable {A : Type u}

/-- The summing functor carries the graded tensor powers of `Y` to
the ambient tensor powers of `total.obj Y`: the comparison
isomorphisms of the monoidal functor `total`, assembled by
induction on the exponent. -/
def totalTensorPowIso [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A] [HasBinaryBiproducts A] [HasZeroObject A]
    (Y : Doubled A) : ∀ N : ℕ,
    total.obj (tensorPow (Doubled A) Y N) ≅
      tensorPow A (total.obj Y) N
  | 0 => epsIso.symm
  | N + 1 => (muIso (tensorPow (Doubled A) Y N) Y).symm ≪≫
      tensorIso (totalTensorPowIso Y N) (Iso.refl (total.obj Y))

end GrowthTransport

end Doubled

section Retracts

variable {C : Type u}

/-- **`Y` is a retract of `Z`**: a section split by a retraction.
A retract is in particular a subquotient, and — unlike the
subquotient relation — the property is visibly stable under tensor
products, tensor powers and biproducts. -/
def IsRetractOf [Category.{v} C]
    (Y Z : C) : Prop :=
  ∃ (s : Y ⟶ Z) (r : Z ⟶ Y), s ≫ r = 𝟙 Y

/-- An isomorphism is a retraction. -/
theorem isRetractOf_of_iso [Category.{v} C]
    {Y Z : C} (e : Y ≅ Z) : IsRetractOf Y Z :=
  ⟨e.hom, e.inv, e.hom_inv_id⟩

/-- Every object is a retract of itself. -/
theorem isRetractOf_rfl [Category.{v} C]
    (Y : C) : IsRetractOf Y Y :=
  isRetractOf_of_iso (Iso.refl Y)

/-- Retractions compose. -/
theorem IsRetractOf.trans [Category.{v} C]
    {Y Z W : C} (h : IsRetractOf Y Z)
    (h' : IsRetractOf Z W) : IsRetractOf Y W := by
  obtain ⟨s, r, hsr⟩ := h
  obtain ⟨s', r', hsr'⟩ := h'
  refine ⟨s ≫ s', r' ≫ r, ?_⟩
  rw [Category.assoc, ← Category.assoc s', hsr', Category.id_comp,
    hsr]

/-- A subquotient sandwiched between two retractions is a
subquotient: a split monomorphism extends the inclusion and a split
epimorphism extends the quotient map. -/
theorem IsSubquotientOf.sandwich [Category.{v} C]
    {Y Y' Z' Z : C}
    (hY : IsRetractOf Y Y') (h : IsSubquotientOf Y' Z')
    (hZ : IsRetractOf Z' Z) : IsSubquotientOf Y Z := by
  obtain ⟨s, r, hsr⟩ := hY
  obtain ⟨S, i, p, hi, hp⟩ := h
  obtain ⟨s', r', hsr'⟩ := hZ
  have := hi
  have := hp
  have : IsSplitMono s' := IsSplitMono.mk' ⟨r', hsr'⟩
  have : IsSplitEpi r := IsSplitEpi.mk' ⟨s, hsr⟩
  exact ⟨S, i ≫ s', p ≫ r, inferInstance, inferInstance⟩

end Retracts

section RetractsMonoidal

variable {C : Type u}

/-- Retractions multiply. -/
theorem IsRetractOf.tensor [Category.{v} C] [MonoidalCategory C]
    {Y Z Y' Z' : C} (h : IsRetractOf Y Z)
    (h' : IsRetractOf Y' Z') : IsRetractOf (Y ⊗ Y') (Z ⊗ Z') := by
  obtain ⟨s, r, hsr⟩ := h
  obtain ⟨s', r', hsr'⟩ := h'
  exact ⟨s ⊗ₘ s', r ⊗ₘ r', by
    rw [MonoidalCategory.tensorHom_comp_tensorHom, hsr, hsr',
      MonoidalCategory.id_tensorHom_id]⟩

/-- Retractions raise to tensor powers. -/
theorem IsRetractOf.tensorPow [Category.{v} C] [MonoidalCategory C]
    {Y Z : C} (h : IsRetractOf Y Z) :
    ∀ n : ℕ, IsRetractOf (tensorPow C Y n) (tensorPow C Z n)
  | 0 => isRetractOf_rfl _
  | n + 1 => (h.tensorPow n).tensor h

end RetractsMonoidal

section RetractsBiproduct

variable {C : Type u}

/-- Retractions assemble over a finite biproduct. -/
theorem IsRetractOf.biproduct [Category.{v} C] [Preadditive C]
    {J : Type} {f g : J → C}
    [HasBiproduct f] [HasBiproduct g]
    (h : ∀ t, IsRetractOf (f t) (g t)) :
    IsRetractOf (⨁ f) (⨁ g) := by
  choose s r hsr using h
  refine ⟨Limits.biproduct.map s, Limits.biproduct.map r, ?_⟩
  ext t
  simp [hsr t]

end RetractsBiproduct

namespace Doubled

section Diagonal

variable {A : Type u}

/-- The diagonal embedding `M ↦ (M, M)`: the ambient object placed
in both degrees at once. -/
def dbl [Category.{v} A] : A ⥤ Doubled A where
  obj M := ⟨M, M⟩
  map f := homMk f f
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp]
theorem dbl_obj_even [Category.{v} A]
    (M : A) : (dbl.obj M).even = M :=
  rfl

@[simp]
theorem dbl_obj_odd [Category.{v} A]
    (M : A) : (dbl.obj M).odd = M :=
  rfl

/-- The diagonal embedding is additive. -/
instance [Category.{v} A] [Preadditive A] : (dbl (A := A)).Additive where
  map_add := rfl

/-- The diagonal embedding preserves subquotients: its components
are the given morphisms, so monomorphisms and epimorphisms are
preserved. -/
theorem isSubquotientOf_dbl [Category.{v} A] [Preadditive A]
    {P Q : A} (h : IsSubquotientOf P Q) :
    IsSubquotientOf (dbl.obj P) (dbl.obj Q) := by
  obtain ⟨S, i, p, hi, hp⟩ := h
  exact ⟨dbl.obj S, dbl.map i, dbl.map p,
    mono_of_components _ hi hi, epi_of_components _ hp hp⟩

/-- A retraction of super-objects from a pair of component
retractions. -/
theorem isRetractOf_of_components [Category.{v} A]
    {V W : Doubled A}
    (se : V.even ⟶ W.even) (re : W.even ⟶ V.even)
    (he : se ≫ re = 𝟙 V.even) (so : V.odd ⟶ W.odd)
    (ro : W.odd ⟶ V.odd) (ho : so ≫ ro = 𝟙 V.odd) :
    IsRetractOf V W :=
  ⟨homMk se so, homMk re ro,
    hom_ext (by simpa using he) (by simpa using ho)⟩

end Diagonal

section DiagonalBiprod

variable {A : Type u}

/-- Every super-object is a retract of the diagonal double of the
sum of its two components. -/
theorem isRetractOf_dbl_self
    [Category.{v} A] [Preadditive A] [HasBinaryBiproducts A]
    (Y : Doubled A) :
    IsRetractOf Y (dbl.obj (Y.even ⊞ Y.odd)) :=
  isRetractOf_of_components biprod.inl biprod.fst (by simp)
    biprod.inr biprod.snd (by simp)

end DiagonalBiprod

section EvenTensor

variable {A : Type u}

open ZeroObject

/-- Tensoring an even object on the left multiplies both graded
components: the mixed blocks vanish. -/
def evenTensorIso [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A] [HasBinaryBiproducts A] [HasZeroObject A]
    (Z : A) (V : Doubled A) :
    evenEmbed.obj Z ⊗ V ≅ ⟨Z ⊗ V.even, Z ⊗ V.odd⟩ :=
  isoMk (isoBiprodZero (isZero_zeroTensor _)).symm
    (isoBiprodZero (isZero_zeroTensor _)).symm

/-- Tensoring an even object on the right multiplies both graded
components. -/
def tensorEvenIso [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A] [HasBinaryBiproducts A] [HasZeroObject A]
    (V : Doubled A) (Z : A) :
    V ⊗ evenEmbed.obj Z ≅ ⟨V.even ⊗ Z, V.odd ⊗ Z⟩ :=
  isoMk (isoBiprodZero (isZero_tensorZero _)).symm
    (isoZeroBiprod (isZero_tensorZero _)).symm

/-- Tensor powers of an even object are even. -/
def evenTensorPowIso [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A] [HasBinaryBiproducts A] [HasZeroObject A]
    (Z : A) : ∀ n : ℕ,
    tensorPow (Doubled A) (evenEmbed.obj Z) n ≅
      evenEmbed.obj (tensorPow A Z n)
  | 0 => Iso.refl _
  | n + 1 => tensorIso (evenTensorPowIso Z n) (Iso.refl _) ≪≫
      evenEmbedTensorIso _ _

end EvenTensor

section Generator

variable {A : Type u}

open ZeroObject

/-- The generator of the doubling attached to a generator `X` of
`A`: the ambient generator, its dual and the unit in even degree,
the unit in odd degree.  The odd component is what makes the odd
half of a super-object reachable; the dual and the unit in the even
component are what let the words of a mixed power be read off
without ever forming a dual in the doubling.  It is reducible, so
that the component computations below see its two blocks. -/
@[reducible]
def gen [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [HasBinaryBiproducts A] [RigidCategory A]
    (X : A) : Doubled A :=
  ⟨X ⊞ Xᘁ ⊞ 𝟙_ A, 𝟙_ A⟩

/-- The even copy of `X` is a retract of the generator. -/
theorem isRetractOf_evenEmbed_gen
    [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [HasBinaryBiproducts A] [HasZeroObject A] [RigidCategory A]
    (X : A) :
    IsRetractOf (evenEmbed.obj X) (gen X) :=
  isRetractOf_of_components biprod.inl biprod.fst (by simp) 0 0
    ((isZero_zero A).eq_of_src _ _)

/-- The even copy of the dual of `X` is a retract of the
generator. -/
theorem isRetractOf_evenEmbedDual_gen
    [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [HasBinaryBiproducts A] [HasZeroObject A] [RigidCategory A]
    (X : A) :
    IsRetractOf (evenEmbed.obj (Xᘁ)) (gen X) :=
  isRetractOf_of_components (biprod.inl ≫ biprod.inr)
    (biprod.snd ≫ biprod.fst) (by simp) 0 0
    ((isZero_zero A).eq_of_src _ _)

/-- The diagonal double of the unit is a retract of the
generator. -/
theorem isRetractOf_dblUnit_gen
    [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [HasBinaryBiproducts A] [RigidCategory A]
    (X : A) :
    IsRetractOf (dbl.obj (𝟙_ A)) (gen X) :=
  isRetractOf_of_components (biprod.inr ≫ biprod.inr)
    (biprod.snd ≫ biprod.snd) (by simp) (𝟙 _) (𝟙 _) (by simp)

/-- The word in the generator that reads off a mixed power: `a`
even copies of `X`, then the diagonal double of the unit, then `b`
even copies of the dual of `X`. -/
def genWord [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A] [HasBinaryBiproducts A] [HasZeroObject A]
    [RigidCategory A]
    (X : A) (a : ℕ) : ℕ → Doubled A
  | 0 => tensorPow (Doubled A) (evenEmbed.obj X) a ⊗ dbl.obj (𝟙_ A)
  | b + 1 => genWord X a b ⊗ evenEmbed.obj (Xᘁ)

/-- The word is the diagonal double of the mixed power: the
diagonal factor spreads the even word over both degrees, and the
remaining brackets are reassociated. -/
def genWordIso [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A] [HasBinaryBiproducts A] [HasZeroObject A]
    [RigidCategory A]
    (X : A) (a : ℕ) : ∀ b : ℕ,
    genWord X a b ≅ dbl.obj (mixedPow A X a b)
  | 0 => tensorIso (evenTensorPowIso X a) (Iso.refl _) ≪≫
      evenTensorIso _ _
  | b + 1 => tensorIso (genWordIso X a b) (Iso.refl _) ≪≫
      tensorEvenIso _ _ ≪≫ dbl.mapIso (α_ _ _ _)

/-- The word is a retract of a tensor power of the generator:
letter by letter. -/
theorem isRetractOf_genWord
    [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A] [HasBinaryBiproducts A] [HasZeroObject A]
    [RigidCategory A]
    (X : A) (a : ℕ) : ∀ b : ℕ,
    IsRetractOf (genWord X a b)
      (tensorPow (Doubled A) (gen X) (a + 1 + b))
  | 0 => ((isRetractOf_evenEmbed_gen X).tensorPow a).tensor
      (isRetractOf_dblUnit_gen X)
  | b + 1 => (isRetractOf_genWord X a b).tensor
      (isRetractOf_evenEmbedDual_gen X)

/-- The diagonal double of a mixed power of `X` is a retract of a
pure power of the generator — a mixed power of the generator with
no dual factors. -/
theorem isRetractOf_dbl_mixedPow
    [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A] [HasBinaryBiproducts A] [HasZeroObject A]
    [RigidCategory A]
    (X : A) (a b : ℕ) :
    IsRetractOf (dbl.obj (mixedPow A X a b))
      (mixedPow (Doubled A) (gen X) (a + 1 + b) 0) :=
  (isRetractOf_of_iso (genWordIso X a b).symm).trans
    ((isRetractOf_genWord X a b).trans
      (isRetractOf_of_iso (tensorPowIsoMixed (Doubled A) (gen X) _)))

end Generator

end Doubled

section Hypotheses

variable {A : Type u}

/-- **Moderate length growth passes to the doubling.**  The
constants bounding the growth of `total.obj Y` in `A` bound the
growth of `Y` in the doubling verbatim. -/
theorem moderateLengthGrowth_doubled
    [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A] [HasBinaryBiproducts A] [HasZeroObject A]
    (h : ModerateLengthGrowth A) :
    ModerateLengthGrowth (Doubled A) := by
  intro Y
  obtain ⟨C, c, hC⟩ := h (Doubled.total.obj Y)
  refine ⟨C, c, fun N => Doubled.lengthLE_of_total ?_⟩
  exact (hC N).of_iso (Doubled.totalTensorPowIso Y N).symm

end Hypotheses

section Generation

variable {A : Type u}

attribute [local instance] Doubled.hasFiniteBiproducts

/-- **Tensor generation passes to the doubling.**  A super-object
is a retract of the diagonal double of the sum of its components,
that sum is a subquotient of a biproduct of mixed powers of `X`,
and the diagonal double of a mixed power of `X` is a retract of a
pure power of `Doubled.gen X`. -/
theorem tensorGeneratedBy_doubled
    [Category.{v} A] [Abelian A] [MonoidalCategory A]
    [MonoidalPreadditive A] [HasFiniteBiproducts A] [RigidCategory A]
    {X : A}
    (h : TensorGeneratedBy A X) :
    TensorGeneratedBy (Doubled A) (Doubled.gen X) := by
  intro Y
  obtain ⟨k, ab, hsub⟩ := h (Y.even ⊞ Y.odd)
  refine ⟨k, fun t => ((ab t).1 + 1 + (ab t).2, 0), ?_⟩
  refine IsSubquotientOf.sandwich (Doubled.isRetractOf_dbl_self Y)
    (Doubled.isSubquotientOf_dbl hsub) ?_
  refine IsRetractOf.trans
    (isRetractOf_of_iso (Functor.mapBiproduct Doubled.dbl _)) ?_
  exact IsRetractOf.biproduct fun t =>
    Doubled.isRetractOf_dbl_mixedPow X (ab t).1 (ab t).2

end Generation

end

end RS
