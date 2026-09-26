/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.CountableDescentClose
public import LeanPool.RegtsSevenster.RS.Classical.Deligne.FibreMix
public import LeanPool.RegtsSevenster.RS.Classical.Deligne.IndOfLinear
public import LeanPool.RegtsSevenster.RS.Classical.Deligne.PointBaseChange
public import LeanPool.RegtsSevenster.RS.Classical.Deligne.ScalarUnitInd

/-!
# From a countable family to a complex point of the splitting algebra

The descent of the argument of Deligne §2.11 to the complex numbers
is a chain of five steps, and this file runs it end to end for a countable
family of objects and of morphisms of the small category.

This is a route to the complex numbers, not the route
`RS.deligne_theorem` takes: that one splits a single object and
passes to a simple quotient
(`RS/Classical/Deligne/SplitEverything.lean`), which reaches ℂ
without a countability restriction on the family.  What the
assembly consumes from this module is `RS.fibreFreeIso`, the fibre
of a mixed object as a free super module.

1. *The splitting algebra.*  The tensor-product device of Deligne 2.11
   produces, out of local mixedness for each object of the family and a
   splitting for each morphism, one nonzero commutative algebra of the
   ind-completion realising all of them at once.
2. *Countable presentation.*  The witnessing algebras of the input are
   arbitrary; `RS.locallyMixed_countablyPresented` and
   `RS.section_countablyPresented` replace each of them by a countably
   presented one.  The compactness they ask for is available because
   the family is indexed by objects of the *small* category
   (`RS.indCompactObj_indOf`).
3. *The dimension count.*  Over countable index families the algebra
   assembled from countably presented constituents has even component
   of at most countable dimension:
   `RS.exists_universal_algebra_rank_le_aleph0`.  This is the same
   assembly as step 1, carrying the count, so the two steps are run
   together rather than one after the other; the ℂ-linearity of the
   embedding that the count consumes is discharged for the structures
   installed from a scalar unit by `RS.indOfLinear_of_scalarUnit`.
4. *The point.*  The countable Nullstellensatz turns that count into a
   ℂ-point of the Γ-algebra: `RS.nonempty_superPoint_gammaAlgebra`.
5. *The fibre.*  At such a point the fibre of an object of the family
   is a finite-dimensional super vector space, of dimension exactly the
   pair `(p | q)` of the mixed sum it becomes over the algebra; this is
   `RS.Classical.Deligne.PointBaseChange` applied through
   `RS.fibreMixIso`.

## Contents

* `RS.exists_superPoint_of_countable_family` — the chain, steps 1 to 4:
  the splitting algebra together with a complex point of its
  Γ-algebra.
* `RS.fibreFreeIso` — the fibre of a mixed object, as a free super
  module.
* `RS.finrank_fibre_tensor_point_even` and
  `RS.finrank_fibre_tensor_point_odd` — the two dimensions of the fibre
  at a point, with their finite-dimensionality.
* `RS.exists_superVect_fibre` — the fibre, packaged as an
  `RS.SuperVect` of dimension `(p | q)`.
* `RS.exists_superPoint_fibre_of_countable_family` — the whole chain,
  steps 1 to 5.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits
open SuperCommAlgebra (pointMod)
open scoped MonObj

universe v

variable {C : Type v}

/-! ## The chain to a complex point -/

/-- **From a countable family of objects to split to a complex point.**
Given a countable family of objects of the small category, each locally
mixed after the embedding, and a countable family of morphisms of
embedded objects, each split after base change to some nonzero
commutative algebra, there is a single nonzero commutative algebra of
the ind-completion over which every object of the family becomes a
mixed sum and every morphism of the family acquires a section, and
whose Γ-algebra has a ℂ-point.

The finite-length hypothesis is what makes the constituents of the
assembled algebra countably presented; the countability of the two
index families is what keeps the assembled algebra of countable
dimension; and the linear structures are the ones installed from the
scalar unit `ψ`, for which the ℂ-linearity of the embedding is
automatic. -/
theorem exists_superPoint_of_countable_family
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C] [Abelian C]
    [RigidCategory C] [MonoidalPreadditive C]
    (ψ : ℂ ≃+* End (𝟙_ C))
    (L : OddLine (Ind C)) {J K : Type v} [Countable J] [Countable K]
    (Xf : J → C) (V W : K → C)
    (g : ∀ k, (indOf : C ⥤ Ind C).obj (V k) ⟶
      (indOf : C ⥤ Ind C).obj (W k))
    (hlen : ∀ Z : C, ∃ N : ℕ, LengthLE Z N)
    (hmix : ∀ j, L.LocallyMixed ((indOf : C ⥤ Ind C).obj (Xf j)))
    (hsplit : ∀ k, ∃ (A : Ind C) (_ : MonObj A) (_ : IsCommMonObj A),
      η[A] ≠ 0 ∧
      ∃ s : freeMod A ((indOf : C ⥤ Ind C).obj (W k)) ⟶
          freeMod A ((indOf : C ⥤ Ind C).obj (V k)),
        s ≫ freeModMap A (g k) =
          𝟙 (freeMod A ((indOf : C ⥤ Ind C).obj (W k)))) :
    letI := linearOfScalarUnit ψ
    letI := monoidalLinearOfScalarUnitBraided ψ
    letI := linearOfScalarUnit (indScalarUnit ψ)
    letI := monoidalLinearOfScalarUnitBraided (indScalarUnit ψ)
    ∃ (𝔸 : Ind C) (_ : MonObj 𝔸) (_ : IsCommMonObj 𝔸),
      η[𝔸] ≠ 0 ∧
      (∀ j, ∃ p q : ℕ,
        Nonempty (freeMod 𝔸 ((indOf : C ⥤ Ind C).obj (Xf j)) ≅
          freeMod 𝔸 (L.mix p q))) ∧
      (∀ k, ∃ s : freeMod 𝔸 ((indOf : C ⥤ Ind C).obj (W k)) ⟶
          freeMod 𝔸 ((indOf : C ⥤ Ind C).obj (V k)),
        s ≫ freeModMap 𝔸 (g k) =
          𝟙 (freeMod 𝔸 ((indOf : C ⥤ Ind C).obj (W k)))) ∧
      Nonempty (SuperPoint (gammaAlgebra (Ind C) L 𝔸)) := by
  let := linearOfScalarUnit ψ
  let := monoidalLinearOfScalarUnitBraided ψ
  let := linearOfScalarUnit (indScalarUnit ψ)
  let := monoidalLinearOfScalarUnitBraided (indScalarUnit ψ)
  have hu : HasScalarUnit C := hasScalarUnit_of_scalarUnit ψ
  obtain ⟨𝔸, hmon, hcomm, hne, hmixed, hsec, hrk⟩ :=
    exists_universal_algebra_rank_le_aleph0 (C := C) hu
      (indOfLinear_of_scalarUnit ψ) hlen L
      (fun j => (indOf : C ⥤ Ind C).obj (Xf j))
      (fun k => (indOf : C ⥤ Ind C).obj (V k))
      (fun k => (indOf : C ⥤ Ind C).obj (W k)) g
      (fun j => locallyMixed_countablyPresented L _
        (indCompactObj_indOf (Xf j)) hlen (hmix j))
      (fun k => section_countablyPresented (g k)
        (indCompactObj_indOf (V k)) (indCompactObj_indOf (W k)) hlen
        (hsplit k))
  let := hmon
  let := hcomm
  exact ⟨𝔸, hmon, hcomm, hne, hmixed, hsec,
    nonempty_superPoint_gammaAlgebra L 𝔸 hne hrk⟩

/-! ## The fibre at a complex point -/

section Fibre

/-- **The fibre of a mixed object is a free super module.**  An object
that becomes the mixed sum `L.mix p q` after base change to the algebra
has for its fibre the free super module of rank `(p | q)`: apply the
realization functor to the isomorphism of free modules, then
`RS.fibreMixIso`. -/
noncomputable def fibreFreeIso
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C] [Abelian C]
    [MonoidalPreadditive C] [CategoryTheory.Linear ℂ (Ind C)]
    [MonoidalLinear ℂ (Ind C)] (L : OddLine (Ind C)) (𝔸 : Ind C) [MonObj 𝔸]
    [IsCommMonObj 𝔸]
    {X : Ind C} {p q : ℕ}
    (e : freeMod 𝔸 X ≅ freeMod 𝔸 (L.mix p q)) :
    (fibreFun L 𝔸).obj X ≅
      ⨁ fun i : Fin p ⊕ Fin q =>
        Sum.elim (fun _ => (gammaAlgebra (Ind C) L 𝔸).unitMod)
          (fun _ => SuperCommAlgebra.Mod.shift
            (gammaAlgebra (Ind C) L 𝔸).unitMod) i :=
  (gammaModuleFunctor L 𝔸).mapIso e ≪≫ fibreMixIso L 𝔸 p q

/-- **The even part of the fibre at a point is finite
dimensional.** -/
theorem finiteDimensional_fibre_tensor_point_even
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C] [Abelian C]
    [MonoidalPreadditive C] [CategoryTheory.Linear ℂ (Ind C)]
    [MonoidalLinear ℂ (Ind C)] (L : OddLine (Ind C)) (𝔸 : Ind C) [MonObj 𝔸]
    [IsCommMonObj 𝔸]
    (P : SuperPoint (gammaAlgebra (Ind C) L 𝔸)) {X : Ind C}
    {p q : ℕ} (e : freeMod 𝔸 X ≅ freeMod 𝔸 (L.mix p q)) :
    FiniteDimensional ℂ
      (((fibreFun L 𝔸).obj X).tensor (pointMod P)).even :=
  finiteDimensional_even_of_free P p q _ (fibreFreeIso L 𝔸 e)

/-- **The odd part of the fibre at a point is finite
dimensional.** -/
theorem finiteDimensional_fibre_tensor_point_odd
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C] [Abelian C]
    [MonoidalPreadditive C] [CategoryTheory.Linear ℂ (Ind C)]
    [MonoidalLinear ℂ (Ind C)] (L : OddLine (Ind C)) (𝔸 : Ind C) [MonObj 𝔸]
    [IsCommMonObj 𝔸]
    (P : SuperPoint (gammaAlgebra (Ind C) L 𝔸)) {X : Ind C}
    {p q : ℕ} (e : freeMod 𝔸 X ≅ freeMod 𝔸 (L.mix p q)) :
    FiniteDimensional ℂ
      (((fibreFun L 𝔸).obj X).tensor (pointMod P)).odd :=
  finiteDimensional_odd_of_free P p q _ (fibreFreeIso L 𝔸 e)

/-- **The even dimension of the fibre at a point is `p`.** -/
theorem finrank_fibre_tensor_point_even
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C] [Abelian C]
    [MonoidalPreadditive C] [CategoryTheory.Linear ℂ (Ind C)]
    [MonoidalLinear ℂ (Ind C)] (L : OddLine (Ind C)) (𝔸 : Ind C) [MonObj 𝔸]
    [IsCommMonObj 𝔸]
    (P : SuperPoint (gammaAlgebra (Ind C) L 𝔸)) {X : Ind C}
    {p q : ℕ} (e : freeMod 𝔸 X ≅ freeMod 𝔸 (L.mix p q)) :
    Module.finrank ℂ
      (((fibreFun L 𝔸).obj X).tensor (pointMod P)).even = p :=
  finrank_even_of_free P p q _ (fibreFreeIso L 𝔸 e)

/-- **The odd dimension of the fibre at a point is `q`.** -/
theorem finrank_fibre_tensor_point_odd
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C] [Abelian C]
    [MonoidalPreadditive C] [CategoryTheory.Linear ℂ (Ind C)]
    [MonoidalLinear ℂ (Ind C)] (L : OddLine (Ind C)) (𝔸 : Ind C) [MonObj 𝔸]
    [IsCommMonObj 𝔸]
    (P : SuperPoint (gammaAlgebra (Ind C) L 𝔸)) {X : Ind C}
    {p q : ℕ} (e : freeMod 𝔸 X ≅ freeMod 𝔸 (L.mix p q)) :
    Module.finrank ℂ
      (((fibreFun L 𝔸).obj X).tensor (pointMod P)).odd = q :=
  finrank_odd_of_free P p q _ (fibreFreeIso L 𝔸 e)

/-- **The fibre at a point, as a super vector space of dimension
`(p | q)`.**  The packaging is `RS.toSuperVect`, whose components are
coordinate spaces of the two dimensions just computed. -/
theorem exists_superVect_fibre
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C] [Abelian C]
    [MonoidalPreadditive C] [CategoryTheory.Linear ℂ (Ind C)]
    [MonoidalLinear ℂ (Ind C)] (L : OddLine (Ind C)) (𝔸 : Ind C) [MonObj 𝔸]
    [IsCommMonObj 𝔸]
    (P : SuperPoint (gammaAlgebra (Ind C) L 𝔸)) {X : Ind C}
    {p q : ℕ} (e : freeMod 𝔸 X ≅ freeMod 𝔸 (L.mix p q)) :
    ∃ E : SuperVect, Module.finrank ℂ E.even = p ∧
      Module.finrank ℂ E.odd = q := by
  have := finiteDimensional_fibre_tensor_point_even L 𝔸 P e
  have := finiteDimensional_fibre_tensor_point_odd L 𝔸 P e
  refine ⟨toSuperVect P ((fibreFun L 𝔸).obj X), ?_, ?_⟩
  · exact finrank_toSuperVect_even_of_free P p q _ (fibreFreeIso L 𝔸 e)
  · exact finrank_toSuperVect_odd_of_free P p q _ (fibreFreeIso L 𝔸 e)

end Fibre

/-! ## The whole chain -/

/-- **From a countable family of objects to split to a fibre functor
valued in finite-dimensional super vector spaces.**  The algebra and
the point of `RS.exists_superPoint_of_countable_family`, with the fibre
of each object of the family recorded as a super vector space of the
dimension pair its mixed sum prescribes. -/
theorem exists_superPoint_fibre_of_countable_family
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C] [Abelian C]
    [RigidCategory C] [MonoidalPreadditive C]
    (ψ : ℂ ≃+* End (𝟙_ C)) (L : OddLine (Ind C)) {J K : Type v}
    [Countable J] [Countable K] (Xf : J → C) (V W : K → C)
    (g : ∀ k, (indOf : C ⥤ Ind C).obj (V k) ⟶
      (indOf : C ⥤ Ind C).obj (W k))
    (hlen : ∀ Z : C, ∃ N : ℕ, LengthLE Z N)
    (hmix : ∀ j, L.LocallyMixed ((indOf : C ⥤ Ind C).obj (Xf j)))
    (hsplit : ∀ k, ∃ (A : Ind C) (_ : MonObj A) (_ : IsCommMonObj A),
      η[A] ≠ 0 ∧
      ∃ s : freeMod A ((indOf : C ⥤ Ind C).obj (W k)) ⟶
          freeMod A ((indOf : C ⥤ Ind C).obj (V k)),
        s ≫ freeModMap A (g k) =
          𝟙 (freeMod A ((indOf : C ⥤ Ind C).obj (W k)))) :
    letI := linearOfScalarUnit ψ
    letI := monoidalLinearOfScalarUnitBraided ψ
    letI := linearOfScalarUnit (indScalarUnit ψ)
    letI := monoidalLinearOfScalarUnitBraided (indScalarUnit ψ)
    ∃ (𝔸 : Ind C) (_ : MonObj 𝔸) (_ : IsCommMonObj 𝔸),
      η[𝔸] ≠ 0 ∧
      (∀ k, ∃ s : freeMod 𝔸 ((indOf : C ⥤ Ind C).obj (W k)) ⟶
          freeMod 𝔸 ((indOf : C ⥤ Ind C).obj (V k)),
        s ≫ freeModMap 𝔸 (g k) =
          𝟙 (freeMod 𝔸 ((indOf : C ⥤ Ind C).obj (W k)))) ∧
      ∃ P : SuperPoint (gammaAlgebra (Ind C) L 𝔸),
        ∀ j, ∃ p q : ℕ,
          Nonempty (freeMod 𝔸 ((indOf : C ⥤ Ind C).obj (Xf j)) ≅
            freeMod 𝔸 (L.mix p q)) ∧
          Module.finrank ℂ
            (((fibreFun L 𝔸).obj ((indOf : C ⥤ Ind C).obj (Xf j))).tensor
              (pointMod P)).even = p ∧
          Module.finrank ℂ
            (((fibreFun L 𝔸).obj ((indOf : C ⥤ Ind C).obj (Xf j))).tensor
              (pointMod P)).odd = q ∧
          ∃ E : SuperVect, Module.finrank ℂ E.even = p ∧
            Module.finrank ℂ E.odd = q := by
  let := linearOfScalarUnit ψ
  let := monoidalLinearOfScalarUnitBraided ψ
  let := linearOfScalarUnit (indScalarUnit ψ)
  let := monoidalLinearOfScalarUnitBraided (indScalarUnit ψ)
  obtain ⟨𝔸, hmon, hcomm, hne, hmixed, hsec, ⟨P⟩⟩ :=
    exists_superPoint_of_countable_family ψ L Xf V W g hlen hmix hsplit
  let := hmon
  let := hcomm
  refine ⟨𝔸, hmon, hcomm, hne, hsec, P, fun j => ?_⟩
  obtain ⟨p, q, ⟨e⟩⟩ := hmixed j
  exact ⟨p, q, ⟨e⟩, finrank_fibre_tensor_point_even L 𝔸 P e,
    finrank_fibre_tensor_point_odd L 𝔸 P e,
    exists_superVect_fibre L 𝔸 P e⟩

/-! ## Acceptance

The intended instantiation takes for `J` the pairs of natural numbers,
indexing the mixed powers of a ⊗-generator.  The index families are
asked to live in the same universe as the objects of the small
category, so the concrete family is `ULift.{v} (ℕ × ℕ)`, which is
countable; there are no morphisms to split. -/

section Acceptance

example
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C] [Abelian C]
    [RigidCategory C] [MonoidalPreadditive C]
    (ψ : ℂ ≃+* End (𝟙_ C)) (L : OddLine (Ind C))
    (Xf : ULift.{v} (ℕ × ℕ) → C)
    (hlen : ∀ Z : C, ∃ N : ℕ, LengthLE Z N)
    (hmix : ∀ j, L.LocallyMixed ((indOf : C ⥤ Ind C).obj (Xf j))) :
    letI := linearOfScalarUnit ψ
    letI := monoidalLinearOfScalarUnitBraided ψ
    letI := linearOfScalarUnit (indScalarUnit ψ)
    letI := monoidalLinearOfScalarUnitBraided (indScalarUnit ψ)
    ∃ (𝔸 : Ind C) (_ : MonObj 𝔸) (_ : IsCommMonObj 𝔸),
      η[𝔸] ≠ 0 ∧
      (∀ j, ∃ p q : ℕ,
        Nonempty (freeMod 𝔸 ((indOf : C ⥤ Ind C).obj (Xf j)) ≅
          freeMod 𝔸 (L.mix p q))) ∧
      Nonempty (SuperPoint (gammaAlgebra (Ind C) L 𝔸)) := by
  let := linearOfScalarUnit ψ
  let := monoidalLinearOfScalarUnitBraided ψ
  let := linearOfScalarUnit (indScalarUnit ψ)
  let := monoidalLinearOfScalarUnitBraided (indScalarUnit ψ)
  obtain ⟨𝔸, hmon, hcomm, hne, hmixed, _, hP⟩ :=
    exists_superPoint_of_countable_family ψ L Xf
      (K := PEmpty.{v + 1}) PEmpty.elim PEmpty.elim
      (fun k => PEmpty.elim k) hlen hmix (fun k => PEmpty.elim k)
  exact ⟨𝔸, hmon, hcomm, hne, hmixed, hP⟩

end Acceptance

end RS
