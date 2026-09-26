/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.CountableNullstellensatz
public import LeanPool.RegtsSevenster.RS.Classical.Deligne.GammaAlgebra
public import LeanPool.RegtsSevenster.RS.Classical.Deligne.HomFinite
public import LeanPool.RegtsSevenster.RS.Classical.Deligne.SuperEvenRing
public import LeanPool.RegtsSevenster.RS.Classical.Deligne.UniversalAlgebra

/-!
# Countable dimension of the Γ-algebra

The descent to the complex numbers of Deligne's Proposition 4.5
consumes a ℂ-point of the Γ-algebra of the universal algebra, and the
countable Nullstellensatz
(`RS.exists_algHom_of_countable_dimension`) supplies one as soon as
the even component has at most countable dimension.  This file
establishes that dimension count for the algebras built by the
tensor-product device of Deligne 2.11 over a countable index family.

The route is the compactness of the unit in the ind-completion.  The
big tensor product of a family of algebras is, by construction, the
filtered colimit of the finite sub-tensor-products
(`RS.bigTensor`), and a morphism out of the unit into a filtered
colimit factors through a stage
(`RS.exists_factor_of_unit_hom_colimit`).  So the even component
`𝟙 ⟶ bigTensor B` is the union of the images of the even components
of the stages; over a countable index family there are only countably
many stages, and a countable union of subspaces of at most countable
dimension has at most countable dimension.

The finite stages are the tensor words of the family, and they are
handled by the same one-variable colimit lemma.  Call an object of
the ind-completion *countably presented* (`RS.CountablyPresented`)
when it is a countable filtered colimit of embedded objects — the
precise sense of "built from countably much data".  Tensoring
preserves the colimits of the ind-completion, and the embedding is
monoidal, so a countably presented factor of a tensor word can be
absorbed one stage at a time
(`RS.rank_hom_unit_tensor_presented`), leaving tensor words against
an embedded object; those are finite dimensional by finite length
(`RS.finiteDimensional_hom_unit`).  Induction along the word
(`RS.rank_hom_unit_listTensor_le_aleph0`) needs no product of index
categories.

Two hypotheses are carried explicitly, because the ambient linear
structure on the ind-completion is itself a hypothesis of this
development and neither follows from it: ℂ-linearity of the
embedding `C ⥤ Ind C` (`RS.IndOfLinear`), and finite length of every
object of `C`.

The conclusion is packaged three ways: as a dimension count for the
common extension of a countable family
(`RS.exists_common_algebra_rank_le_aleph0_of_presented`), as the same
count for the universal algebra of Deligne 2.11 over countable index
families (`RS.exists_universal_algebra_rank_le_aleph0`), and, through
the countable Nullstellensatz, as a ℂ-point of the Γ-algebra
(`RS.nonempty_superPoint_gammaAlgebra`).
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits

universe v u

/-! ## A countable union of small subspaces is small

Pure linear algebra: a module covered by countably many subspaces of
at most countable dimension has at most countable dimension.  Choose
a basis of each piece; the union of the bases is a countable spanning
set. -/

section CountableRank

variable {K : Type*}

/-- **A countable union of subspaces of countable dimension has
countable dimension**: the union of chosen bases of the pieces is a
countable spanning set. -/
theorem rank_le_aleph0_of_countable_cover
    [DivisionRing K] {M : Type*} [AddCommGroup M] [Module K M]
    {I : Type*} [Countable I]
    (p : I → Submodule K M)
    (hp : ∀ i, Module.rank K (p i) ≤ Cardinal.aleph0)
    (hcover : ∀ x : M, ∃ i, x ∈ p i) :
    Module.rank K M ≤ Cardinal.aleph0 := by
  classical
  set b : ∀ i, Module.Basis (Module.Free.ChooseBasisIndex K (p i))
      K (p i) := fun i => Module.Free.chooseBasis K (p i)
  have hcnt : ∀ i, Countable (Module.Free.ChooseBasisIndex K (p i)) :=
    fun i => Cardinal.mk_le_aleph0_iff.mp (by
      rw [← Module.Free.rank_eq_card_chooseBasisIndex]
      exact hp i)
  set s : I → Set M :=
    fun i => Set.range (fun t => ((b i t : p i) : M)) with hs
  have hspan : ∀ i, p i = Submodule.span K (s i) := by
    intro i
    have h1 : Submodule.map (p i).subtype
        (Submodule.span K (Set.range (b i))) =
        Submodule.span K (s i) := by
      rw [Submodule.map_span, hs]
      exact congrArg (Submodule.span K) (Set.range_comp _ _).symm
    rwa [(b i).span_eq, Submodule.map_top, Submodule.range_subtype]
      at h1
  have hcS : (⋃ i, s i).Countable := by
    have := hcnt
    exact Set.countable_iUnion fun i => Set.countable_range _
  have htopS : Submodule.span K (⋃ i, s i) = ⊤ := by
    rw [Submodule.span_iUnion]
    refine eq_top_iff.mpr fun x _ => ?_
    obtain ⟨i, hi⟩ := hcover x
    exact Submodule.mem_iSup_of_mem i (by rw [← hspan i]; exact hi)
  have hrk := rank_span_le (R := K) (⋃ i, s i)
  rw [htopS, rank_top] at hrk
  exact hrk.trans (Cardinal.le_aleph0_iff_set_countable.mpr hcS)

end CountableRank

/-! ## Countable filtered colimits in the ind-completion

The unit of the ind-completion is compact: a morphism out of it into
a filtered colimit factors through a stage.  So the even component of
a filtered colimit is the union of the images of the even components
of the stages, and over a countable diagram the previous section
applies. -/

section IndColimit

variable {C : Type v}

/-- **A countable filtered colimit of objects with countable even
component again has countable even component.**  Compactness of the
unit (`RS.exists_factor_of_unit_hom_colimit`) covers `𝟙 ⟶ colimit D`
by the countably many images of the `𝟙 ⟶ D.obj i`. -/
theorem rank_hom_unit_colimit_le_aleph0
    [SmallCategory C] [MonoidalCategory C] [Abelian C]
    [CategoryTheory.Linear ℂ (Ind C)]
    {I : Type v} [SmallCategory I]
    [IsFiltered I] [Countable I] (D : I ⥤ Ind C)
    (h : ∀ i : I,
      Module.rank ℂ (𝟙_ (Ind C) ⟶ D.obj i) ≤ Cardinal.aleph0) :
    Module.rank ℂ (𝟙_ (Ind C) ⟶ colimit D) ≤ Cardinal.aleph0 := by
  refine rank_le_aleph0_of_countable_cover
    (fun i => LinearMap.range
      (Linear.rightComp ℂ (𝟙_ (Ind C)) (colimit.ι D i)))
    (fun i => ?_) (fun f => ?_)
  · exact le_trans (LinearMap.rank_le_of_surjective _
      (Linear.rightComp ℂ (𝟙_ (Ind C))
        (colimit.ι D i)).surjective_rangeRestrict) (h i)
  · obtain ⟨i, g, hg⟩ := exists_factor_of_unit_hom_colimit D f
    exact ⟨i, LinearMap.mem_range.mpr ⟨g, hg⟩⟩

end IndColimit

/-! ## The big tensor product over a countable index family

The big tensor product is the filtered colimit of its finite
sub-tensor-products, indexed by the finite subsets of the index
family.  Over a countable family there are only countably many of
those, so the even component is of at most countable dimension as
soon as each finite stage is. -/

section BigTensorRank

variable {C : Type v}

/-- **The big tensor product of a countable family has countable
even component**, provided each finite sub-tensor-product does: the
stages are indexed by `Finset J`, which is countable. -/
theorem rank_hom_unit_bigTensor_le_aleph0
    [SmallCategory C] [MonoidalCategory C] [Abelian C]
    [CategoryTheory.Linear ℂ (Ind C)] {J : Type v} [LinearOrder J]
    (B : J → Ind C) [∀ j, MonObj (B j)]
    [Countable J]
    (h : ∀ s : Finset J,
      Module.rank ℂ (𝟙_ (Ind C) ⟶ finTensor B s) ≤ Cardinal.aleph0) :
    Module.rank ℂ (𝟙_ (Ind C) ⟶ bigTensor B) ≤ Cardinal.aleph0 :=
  rank_hom_unit_colimit_le_aleph0 (finTensorDiagram B) h

/-- The finite stages are the tensor words of the family: a bound on
every word bounds every stage. -/
theorem rank_hom_unit_finTensor_le_aleph0
    [SmallCategory C] [MonoidalCategory C] [Abelian C]
    [CategoryTheory.Linear ℂ (Ind C)] {J : Type v} [LinearOrder J]
    (B : J → Ind C)
    (h : ∀ l : List J,
      Module.rank ℂ (𝟙_ (Ind C) ⟶ listTensor B l) ≤ Cardinal.aleph0)
    (s : Finset J) :
    Module.rank ℂ (𝟙_ (Ind C) ⟶ finTensor B s) ≤ Cardinal.aleph0 :=
  h (s.sort (· ≤ ·))

end BigTensorRank

/-! ## Transport along isomorphisms -/

section Transport

variable {C : Type v}

/-- Isomorphic objects have isomorphic even components. -/
theorem rank_hom_unit_congr [SmallCategory C] [MonoidalCategory C] [Abelian C]
    [CategoryTheory.Linear ℂ (Ind C)]
    {Y Z : Ind C} (e : Y ≅ Z) :
    Module.rank ℂ (𝟙_ (Ind C) ⟶ Y) =
      Module.rank ℂ (𝟙_ (Ind C) ⟶ Z) :=
  (Linear.homCongr ℂ (Iso.refl (𝟙_ (Ind C))) e).rank_eq

/-- Countability of the even component is an isomorphism
invariant. -/
theorem rank_hom_unit_le_aleph0_of_iso
    [SmallCategory C] [MonoidalCategory C] [Abelian C]
    [CategoryTheory.Linear ℂ (Ind C)]
    {Y Z : Ind C} (e : Y ≅ Z)
    (h : Module.rank ℂ (𝟙_ (Ind C) ⟶ Z) ≤ Cardinal.aleph0) :
    Module.rank ℂ (𝟙_ (Ind C) ⟶ Y) ≤ Cardinal.aleph0 :=
  (rank_hom_unit_congr e).trans_le h

end Transport

/-! ## The embedded objects

For an embedded object the even component is the even component
downstairs, which finite length makes finite dimensional
(`RS.finiteDimensional_hom_unit`).  The identification is ℂ-linear
only if the embedding is, which the hypothesised linear structure on
the ind-completion does not by itself provide; ℂ-linearity of the
embedding is therefore carried as an explicit hypothesis, in the
shape in which the induced structure of `RS.linearOfScalarUnit`
supplies it. -/

section Embedded

variable {C : Type v}

variable (C) in
/-- ℂ-linearity of the embedding `C ⥤ Ind C`, as a hypothesis on the
ambient linear structure of the ind-completion. -/
def IndOfLinear [SmallCategory C] [Abelian C] [CategoryTheory.Linear ℂ C]
    [CategoryTheory.Linear ℂ (Ind C)] : Prop :=
  ∀ (X Y : C) (c : ℂ) (f : X ⟶ Y),
    (indOf (C := C)).map (c • f) = c • (indOf (C := C)).map f

/-- **Full faithfulness of the embedding, ℂ-linearly**: for a
ℂ-linear embedding the hom-modules downstairs and upstairs are the
same ℂ-module. -/
noncomputable def indOfHomEquiv
    [SmallCategory C] [Abelian C] [CategoryTheory.Linear ℂ C]
    [CategoryTheory.Linear ℂ (Ind C)]
    (hsmul : IndOfLinear C) (X Y : C) :
    (X ⟶ Y) ≃ₗ[ℂ] (indOf.obj X ⟶ indOf.obj Y) :=
  letI := indOf_additive (C := C)
  { toFun := fun f => indOf.map f
    map_add' := fun _ _ => (indOf (C := C)).map_add
    map_smul' := fun c f => hsmul X Y c f
    invFun := fun g => Ind.yoneda.fullyFaithful.preimage g
    left_inv := fun f => Ind.yoneda.fullyFaithful.preimage_map f
    right_inv := fun g => Ind.yoneda.fullyFaithful.map_preimage g }

/-- **An embedded object of finite length has finite dimensional even
component**, hence countable dimension: the even component is
`𝟙_ C ⟶ W`, which `RS.finiteDimensional_hom_unit` makes finite
dimensional. -/
theorem rank_hom_unit_indOf_le_aleph0
    [SmallCategory C] [MonoidalCategory C] [Abelian C]
    [CategoryTheory.Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
    [RigidCategory C] [CategoryTheory.Linear ℂ (Ind C)]
    (hu : HasScalarUnit C)
    (hsmul : IndOfLinear C) {W : C} (hW : ∃ N : ℕ, LengthLE W N) :
    Module.rank ℂ (𝟙_ (Ind C) ⟶ indOf.obj W) ≤ Cardinal.aleph0 := by
  have : FiniteDimensional ℂ (𝟙_ C ⟶ W) :=
    finiteDimensional_hom_unit hu hW
  have h1 : Module.rank ℂ (𝟙_ (Ind C) ⟶ indOf.obj W) =
      Module.rank ℂ (indOf.obj (𝟙_ C) ⟶ indOf.obj W) :=
    (Linear.homCongr ℂ (indOfUnitIso (C := C))
      (Iso.refl (indOf.obj W))).rank_eq
  have h2 : Module.rank ℂ (𝟙_ C ⟶ W) =
      Module.rank ℂ (indOf.obj (𝟙_ C) ⟶ indOf.obj W) :=
    (indOfHomEquiv hsmul (𝟙_ C) W).rank_eq
  rw [h1, ← h2]
  exact le_of_lt (Module.rank_lt_aleph0 ℂ (𝟙_ C ⟶ W))

end Embedded

/-! ## Countably presented ind-objects

An object of the ind-completion built from countably much data is a
countable filtered colimit of embedded objects.  Such objects are
absorbed one at a time into a tensor word: tensoring preserves
filtered colimits of the ind-completion
(`RS.tensorLeft_ind_preservesColimitsOfShape` and its right-hand
version), so a tensor word against a countably
presented factor is again a countable filtered colimit, whose stages
are tensor words against an *embedded* factor — and the embedding is
monoidal (`RS.indOfTensorIso`), so those stages absorb the factor
into the base category.  Iterating along the word never leaves the
one-variable colimit lemma, and no product of index categories is
needed. -/

section Presented

variable {C : Type v}

/-- An object of the ind-completion is *countably presented* when it
is the colimit of a countable filtered diagram of embedded objects.
This is the shape in which "built from countably much data" enters
the dimension count of the Γ-algebra. -/
def CountablyPresented [SmallCategory C]
    (Z : Ind C) : Prop :=
  ∃ (I : Type v) (_ : SmallCategory I) (_ : IsFiltered I)
    (_ : Countable I) (G : I ⥤ C),
    Nonempty (Z ≅ colimit (G ⋙ indOf))

/-- Being countably presented is an isomorphism invariant. -/
theorem CountablyPresented.of_iso [SmallCategory C]
    {Y Z : Ind C} (e : Y ≅ Z)
    (h : CountablyPresented Y) : CountablyPresented Z := by
  obtain ⟨I, hcat, hfil, hcnt, G, ⟨eY⟩⟩ := h
  exact ⟨I, hcat, hfil, hcnt, G, ⟨e.symm ≪≫ eY⟩⟩

/-- The single object of the one-morphism index category is
terminal. -/
private def punitIsTerminal :
    IsTerminal (Discrete.mk PUnit.unit : Discrete PUnit.{v + 1}) :=
  IsTerminal.ofUniqueHom (fun X => Discrete.eqToHom (by cases X; rfl))
    (fun _ _ => Subsingleton.elim _ _)

/-- **Absorbing a countably presented factor.**  A tensor word `Y`
whose even component stays countable against every embedded factor
keeps that property after `Y` is enlarged by a countably presented
factor: the enlarged word against an embedded factor is a countable
filtered colimit of copies of the original word against an embedded
factor. -/
theorem rank_hom_unit_tensor_presented
    [SmallCategory C] [MonoidalCategory C] [Abelian C]
    [CategoryTheory.Linear ℂ (Ind C)]
    {Y Z : Ind C}
    (hZ : CountablyPresented Z)
    (hY : ∀ W : C, Module.rank ℂ (𝟙_ (Ind C) ⟶ Y ⊗ indOf.obj W) ≤
      Cardinal.aleph0) (W : C) :
    Module.rank ℂ (𝟙_ (Ind C) ⟶ (Y ⊗ Z) ⊗ indOf.obj W) ≤
      Cardinal.aleph0 := by
  obtain ⟨I, hcat, hfil, hcnt, G, ⟨eZ⟩⟩ := hZ
  let := hcat
  let := hfil
  let := hcnt
  refine rank_hom_unit_le_aleph0_of_iso
    (Z := colimit (((G ⋙ indOf) ⋙ tensorRight (indOf.obj W)) ⋙
      tensorLeft Y)) ?_ ?_
  · exact (α_ Y Z (indOf.obj W)) ≪≫
      whiskerLeftIso Y ((tensorRight (indOf.obj W)).mapIso eZ ≪≫
        preservesColimitIso (tensorRight (indOf.obj W))
          (G ⋙ indOf)) ≪≫
      preservesColimitIso (tensorLeft Y) _
  · refine rank_hom_unit_colimit_le_aleph0 _ (fun i => ?_)
    exact rank_hom_unit_le_aleph0_of_iso
      (whiskerLeftIso Y (indOfTensorIso (G.obj i) W))
      (hY (G.obj i ⊗ W))

/-- The induction along a tensor word: each factor is absorbed by
`RS.rank_hom_unit_tensor_presented`, the accumulated word being
carried as the parameter `Y`. -/
private theorem rank_tensor_listTensor_aux
    [SmallCategory C] [MonoidalCategory C] [Abelian C]
    [CategoryTheory.Linear ℂ (Ind C)]
    {J : Type v}
    (B : J → Ind C) (hB : ∀ j, CountablyPresented (B j)) :
    ∀ (l : List J) (Y : Ind C),
      (∀ W : C, Module.rank ℂ (𝟙_ (Ind C) ⟶ Y ⊗ indOf.obj W) ≤
        Cardinal.aleph0) →
      ∀ W : C, Module.rank ℂ
        (𝟙_ (Ind C) ⟶ (Y ⊗ listTensor B l) ⊗ indOf.obj W) ≤
        Cardinal.aleph0
  | [], Y, hY, W =>
    rank_hom_unit_le_aleph0_of_iso
      (whiskerRightIso (ρ_ Y) (indOf.obj W)) (hY W)
  | j :: l, Y, hY, W =>
    rank_hom_unit_le_aleph0_of_iso
      (whiskerRightIso (α_ Y (B j) (listTensor B l)).symm
        (indOf.obj W))
      (rank_tensor_listTensor_aux B hB l (Y ⊗ B j)
        (rank_hom_unit_tensor_presented (hB j) hY) W)

/-- **The tensor words of countably presented algebras have countable
even component.**  This is the finite-stage input of
`RS.rank_hom_unit_bigTensor_le_aleph0`, discharged. -/
theorem rank_hom_unit_listTensor_le_aleph0
    [SmallCategory C] [MonoidalCategory C] [Abelian C] [RigidCategory C]
    [MonoidalPreadditive C] [CategoryTheory.Linear ℂ (Ind C)]
    [CategoryTheory.Linear ℂ C] [MonoidalLinear ℂ C]
    (hu : HasScalarUnit C)
    (hsmul : IndOfLinear C) (hlen : ∀ X : C, ∃ N : ℕ, LengthLE X N)
    {J : Type v} (B : J → Ind C)
    (hB : ∀ j, CountablyPresented (B j)) (l : List J) :
    Module.rank ℂ (𝟙_ (Ind C) ⟶ listTensor B l) ≤ Cardinal.aleph0 := by
  have hbase : ∀ W : C,
      Module.rank ℂ (𝟙_ (Ind C) ⟶ 𝟙_ (Ind C) ⊗ indOf.obj W) ≤
        Cardinal.aleph0 := fun W =>
    rank_hom_unit_le_aleph0_of_iso (λ_ (indOf.obj W))
      (rank_hom_unit_indOf_le_aleph0 hu hsmul (hlen W))
  refine rank_hom_unit_le_aleph0_of_iso ?_
    (rank_tensor_listTensor_aux B hB l (𝟙_ (Ind C)) hbase (𝟙_ C))
  exact (ρ_ (listTensor B l)).symm ≪≫
    whiskerLeftIso (listTensor B l) (indOfUnitIso (C := C)) ≪≫
    whiskerRightIso (λ_ (listTensor B l)).symm (indOf.obj (𝟙_ C))

end Presented

/-! ## The common extension of a countable family

The tensor-product device of Deligne 2.11, with the dimension count
carried along: a countable family of algebras whose tensor words have
countable even component has a common extension with countable even
component. -/

section CommonAlgebraRank

variable {C : Type v}

/-- **A countable family of nonzero algebras has a common nonzero
extension of countable even dimension**: the tensor product of the
family, as in `RS.exists_common_algebra`, with the dimension count of
`RS.rank_hom_unit_bigTensor_le_aleph0` added.  The hypothesis is the
countability of the even component of every tensor word of the
family, which is the finite-stage input the colimit argument
consumes. -/
theorem exists_common_algebra_rank_le_aleph0
    [SmallCategory C] [MonoidalCategory C] [Abelian C]
    [CategoryTheory.Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
    [RigidCategory C] [CategoryTheory.Linear ℂ (Ind C)]
    [SymmetricCategory (Ind C)]
    (hu : HasScalarUnit C)
    {J : Type v} [Countable J] (B : J → Ind C) [∀ j, MonObj (B j)]
    [∀ j, IsCommMonObj (B j)] (hB : ∀ j, MonObj.one (X := B j) ≠ 0)
    (hrk : ∀ l : List J,
      Module.rank ℂ (𝟙_ (Ind C) ⟶ listTensor B l) ≤ Cardinal.aleph0) :
    ∃ (𝔸 : Ind C) (_ : MonObj 𝔸) (_ : IsCommMonObj 𝔸),
      MonObj.one (X := 𝔸) ≠ 0 ∧
      (∀ j, ∃ φ : B j ⟶ 𝔸, IsMonHom φ) ∧
      Module.rank ℂ (𝟙_ (Ind C) ⟶ 𝔸) ≤ Cardinal.aleph0 := by
  let : DecidableRel (WellOrderingRel (α := J)) :=
    Classical.decRel _
  let : LinearOrder J := linearOrderOfSTO WellOrderingRel
  exact ⟨bigTensor B, bigTensorMon B, bigTensorCommMon B,
    bigTensorUnit_ne_zero_ind B hu hB,
    fun j => ⟨bigTensorOf B j, isMonHom_bigTensorOf B j⟩,
    rank_hom_unit_bigTensor_le_aleph0 B
      (rank_hom_unit_finTensor_le_aleph0 B hrk)⟩

/-- **The common extension of a countable family of countably
presented algebras has countable even component.**  The hypothesis is
structural: each member of the family is a countable filtered
colimit of embedded objects, which is what "built from countably much
data" means for the algebras of Deligne 2.11. -/
theorem exists_common_algebra_rank_le_aleph0_of_presented
    [SmallCategory C] [MonoidalCategory C] [Abelian C]
    [CategoryTheory.Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
    [RigidCategory C] [CategoryTheory.Linear ℂ (Ind C)]
    [SymmetricCategory (Ind C)]
    (hu : HasScalarUnit C) (hsmul : IndOfLinear C)
    (hlen : ∀ X : C, ∃ N : ℕ, LengthLE X N) {J : Type v} [Countable J]
    (B : J → Ind C) [∀ j, MonObj (B j)] [∀ j, IsCommMonObj (B j)]
    (hB : ∀ j, MonObj.one (X := B j) ≠ 0)
    (hpres : ∀ j, CountablyPresented (B j)) :
    ∃ (𝔸 : Ind C) (_ : MonObj 𝔸) (_ : IsCommMonObj 𝔸),
      MonObj.one (X := 𝔸) ≠ 0 ∧
      (∀ j, ∃ φ : B j ⟶ 𝔸, IsMonHom φ) ∧
      Module.rank ℂ (𝟙_ (Ind C) ⟶ 𝔸) ≤ Cardinal.aleph0 :=
  exists_common_algebra_rank_le_aleph0 hu B hB
    (rank_hom_unit_listTensor_le_aleph0 hu hsmul hlen B hpres)

end CommonAlgebraRank

/-! ## The universal algebra over a countable family

Deligne 2.11 with the dimension count carried along.  The two
hypotheses are those of `RS.exists_universal_algebra` strengthened by
the requirement that the algebra chosen at each index be countably
presented; the index families are countable, so the universal algebra
— the tensor product of all the chosen algebras — has countable even
component. -/

section UniversalAlgebraRank

variable {C : Type v}

/-- **The universal algebra over countable families has countable
even component**: one nonzero algebra over which every object of the
family becomes a mixed sum and every chosen morphism acquires a
section, whose Γ-algebra is of at most countable dimension over ℂ.
The hypotheses are those of `RS.exists_universal_algebra` with the
chosen algebras required to be countably presented. -/
theorem exists_universal_algebra_rank_le_aleph0
    [SmallCategory C] [MonoidalCategory C] [Abelian C]
    [CategoryTheory.Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
    [RigidCategory C] [CategoryTheory.Linear ℂ (Ind C)]
    [SymmetricCategory (Ind C)] [HasCoequalizers (Ind C)]
    [∀ Z : Ind C, PreservesColimitsOfShape WalkingParallelPair (tensorLeft
      Z)] [HasFiniteBiproducts (Ind C)]
    (hu : HasScalarUnit C)
    (hsmul : IndOfLinear C) (hlen : ∀ Z : C, ∃ N : ℕ, LengthLE Z N)
    (L : OddLine (Ind C)) {J K : Type v} [Countable J] [Countable K]
    (X : J → Ind C) (V W : K → Ind C) (g : ∀ k, V k ⟶ W k)
    (hmix : ∀ j, ∃ (p q : ℕ) (A : Ind C) (_ : MonObj A)
      (_ : IsCommMonObj A), MonObj.one (X := A) ≠ 0 ∧
      CountablyPresented A ∧
      Nonempty (freeMod A (X j) ≅ freeMod A (L.mix p q)))
    (hsplit : ∀ k, ∃ (A : Ind C) (_ : MonObj A) (_ : IsCommMonObj A),
      MonObj.one (X := A) ≠ 0 ∧ CountablyPresented A ∧
      ∃ s : freeMod A (W k) ⟶ freeMod A (V k),
        s ≫ freeModMap A (g k) = 𝟙 (freeMod A (W k))) :
    ∃ (𝔸 : Ind C) (_ : MonObj 𝔸) (_ : IsCommMonObj 𝔸),
      MonObj.one (X := 𝔸) ≠ 0 ∧
      (∀ j, ∃ p q : ℕ,
        Nonempty (freeMod 𝔸 (X j) ≅ freeMod 𝔸 (L.mix p q))) ∧
      (∀ k, ∃ s : freeMod 𝔸 (W k) ⟶ freeMod 𝔸 (V k),
        s ≫ freeModMap 𝔸 (g k) = 𝟙 (freeMod 𝔸 (W k))) ∧
      Module.rank ℂ (𝟙_ (Ind C) ⟶ 𝔸) ≤ Cardinal.aleph0 := by
  classical
  choose pm qm Am Amon Acomm Ane Apres Aiso using hmix
  choose Bs Bmon Bcomm Bne Bpres Bsec using hsplit
  let : ∀ i : J ⊕ K, MonObj (Sum.elim Am Bs i) := fun i =>
    match i with
    | Sum.inl j => Amon j
    | Sum.inr k => Bmon k
  let : ∀ i : J ⊕ K, IsCommMonObj (Sum.elim Am Bs i) := fun i =>
    match i with
    | Sum.inl j => Acomm j
    | Sum.inr k => Bcomm k
  obtain ⟨𝔸, hmon, hcomm, hne, hmap, hrk⟩ :=
    exists_common_algebra_rank_le_aleph0_of_presented hu hsmul hlen
      (Sum.elim Am Bs)
      (fun i => match i with
        | Sum.inl j => Ane j
        | Sum.inr k => Bne k)
      (fun i => match i with
        | Sum.inl j => Apres j
        | Sum.inr k => Bpres k)
  refine ⟨𝔸, hmon, hcomm, hne, ?_, ?_, hrk⟩
  · intro j
    obtain ⟨φ, hφ⟩ := hmap (Sum.inl j)
    have : IsMonHom (show Am j ⟶ 𝔸 from φ) := hφ
    exact ⟨pm j, qm j,
      ⟨freeModIsoBaseChange (Am j) 𝔸 (show Am j ⟶ 𝔸 from φ)
        (Aiso j).some⟩⟩
  · intro k
    obtain ⟨φ, hφ⟩ := hmap (Sum.inr k)
    have : IsMonHom (show Bs k ⟶ 𝔸 from φ) := hφ
    obtain ⟨s, hs⟩ := Bsec k
    exact exists_section_baseChange (Bs k) 𝔸
      (show Bs k ⟶ 𝔸 from φ) (g k) s hs

end UniversalAlgebraRank

/-! ## The Γ-algebra and its ℂ-point

The even component of the Γ-algebra of a commutative monoid object is
its even component as computed above, so the dimension count is a
count of `𝟙 ⟶ R`; and the countable Nullstellensatz turns it into a
ℂ-point of the Γ-algebra. -/

section SuperPointCountable

universe u'

/-- **A super-commutative ℂ-algebra of at most countable dimension
has a ℂ-point.**  The odd-nil quotient is a nonzero commutative
ℂ-algebra of at most countable dimension, so
`RS.exists_algHom_of_countable_dimension` gives it a ℂ-algebra map to
ℂ, which pulls back to a point.  This is the countable-dimension
replacement for the finite-type hypothesis of
`RS.nonempty_superPoint`. -/
theorem nonempty_superPoint_of_rank_le_aleph0
    (S : SuperCommAlgebra.{u, u'}) [Nontrivial S.even]
    (h : Module.rank ℂ S.even ≤ Cardinal.aleph0) :
    Nonempty (SuperPoint S) := by
  have := S.nontrivial_quotient_oddIdeal
  refine (exists_algHom_of_countable_dimension (S.even ⧸ S.oddIdeal)
    ?_).map (SuperPoint.ofQuotient S)
  exact le_trans (LinearMap.rank_le_of_surjective
    (Ideal.Quotient.mkₐ ℂ S.oddIdeal).toLinearMap
    (Ideal.Quotient.mkₐ_surjective ℂ _)) h

end SuperPointCountable

section GammaRank

variable {C : Type v}

/-- **The even component of the Γ-algebra has countable dimension**
whenever the even hom-module of the algebra does: the two are the
same ℂ-module. -/
theorem rank_gammaEven_le_aleph0
    [SmallCategory C] [MonoidalCategory C] [Abelian C]
    [CategoryTheory.Linear ℂ (Ind C)] [MonoidalPreadditive (Ind C)]
    [MonoidalLinear ℂ (Ind C)] [SymmetricCategory (Ind C)]
    (L : OddLine (Ind C)) (R : Ind C)
    [MonObj R] [IsCommMonObj R]
    (h : Module.rank ℂ (𝟙_ (Ind C) ⟶ R) ≤ Cardinal.aleph0) :
    Module.rank ℂ (gammaAlgebra (Ind C) L R).even ≤
      Cardinal.aleph0 := h

/-- **A ℂ-point of the Γ-algebra of an algebra with countable even
component**: the last step of the descent to the complex numbers, run
over the countable-dimension Nullstellensatz.  Nontriviality of the
even ring is exactly the nonvanishing of the unit of the algebra. -/
theorem nonempty_superPoint_gammaAlgebra
    [SmallCategory C] [MonoidalCategory C] [Abelian C]
    [CategoryTheory.Linear ℂ (Ind C)] [MonoidalPreadditive (Ind C)]
    [MonoidalLinear ℂ (Ind C)] [SymmetricCategory (Ind C)]
    (L : OddLine (Ind C))
    (R : Ind C) [MonObj R] [IsCommMonObj R]
    (hR : MonObj.one (X := R) ≠ 0)
    (h : Module.rank ℂ (𝟙_ (Ind C) ⟶ R) ≤ Cardinal.aleph0) :
    Nonempty (SuperPoint (gammaAlgebra (Ind C) L R)) := by
  have : Nontrivial (gammaAlgebra (Ind C) L R).even :=
    nontrivial_of_ne 1 0 hR
  exact nonempty_superPoint_of_rank_le_aleph0 _
    (rank_gammaEven_le_aleph0 L R h)

end GammaRank

end RS
