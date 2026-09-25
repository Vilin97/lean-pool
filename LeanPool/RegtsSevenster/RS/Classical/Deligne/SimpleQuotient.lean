/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.CountableDescentClose
public import LeanPool.RegtsSevenster.RS.Classical.Deligne.KernelPow

/-!
# Simple quotients of commutative algebras in the ind-completion

Every nonzero commutative algebra object of `Ind C` has a quotient
algebra which is simple as an algebra: its only ideals are `⊥` and
`⊤`.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v

variable {C : Type v}

/-! ## Well-poweredness of the ind-completion -/

/-- **The ind-completion is well powered.**  The embedded objects
form a separating family, hence a detecting one, and a category with
a small detecting family is well powered. -/
noncomputable instance wellPoweredInd
    [SmallCategory C] [Abelian C] : WellPowered.{v} (Ind C) :=
  CategoryTheory.wellPowered_of_isDetecting
    (Ind.isSeparating_range_yoneda (C := C)).isDetecting

/-! ## Factoring through a subobject -/

/-- A commuting triangle exhibits a factorisation through a
subobject. -/
theorem factors_of_comm [SmallCategory C]
    {X Y : Ind C} {P : Subobject Y} {f : X ⟶ Y}
    (g : X ⟶ (P : Ind C)) (h : g ≫ P.arrow = f) : P.Factors f :=
  h ▸ Subobject.factors_comp_arrow g

/-- The factorisation named by `Subobject.Factors`, read back as an
explicit commuting triangle. -/
theorem exists_factor [SmallCategory C]
    {X Y : Ind C} {P : Subobject Y} {f : X ⟶ Y}
    (h : P.Factors f) : ∃ g : X ⟶ (P : Ind C), g ≫ P.arrow = f :=
  ⟨P.factorThru f h, P.factorThru_arrow f h⟩

/-- **Factoring through a subobject is being killed by its
cokernel.**  A monomorphism of an abelian category is the kernel of
its own cokernel, so a morphism factors through a subobject exactly
when it dies against the cokernel of the subobject's arrow. -/
theorem factors_iff_comp_cokernel [SmallCategory C] [Abelian C]
    {X Y : Ind C} (P : Subobject Y)
    (f : X ⟶ Y) : P.Factors f ↔ f ≫ cokernel.π P.arrow = 0 := by
  constructor
  · intro hf
    rw [← P.factorThru_arrow f hf, Category.assoc,
      cokernel.condition, comp_zero]
  · intro h
    obtain ⟨l, hl⟩ := KernelFork.IsLimit.lift'
      (Abelian.monoIsKernelOfCokernel _
        (cokernelIsCokernel P.arrow)) f h
    exact factors_of_comm l hl

/-- **Factoring is detected on a colimit cocone**: a morphism out of
a colimit factors through a subobject as soon as each of its
restrictions to the stages does. -/
theorem factors_of_isColimit [SmallCategory C] [Abelian C]
    {J : Type v} [SmallCategory J]
    {F : J ⥤ Ind C} (c : Cocone F) (hc : IsColimit c) {W : Ind C}
    (P : Subobject W) (f : c.pt ⟶ W)
    (h : ∀ j, P.Factors (c.ι.app j ≫ f)) : P.Factors f := by
  rw [factors_iff_comp_cokernel]
  refine hc.hom_ext (fun j => ?_)
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  exact ((factors_iff_comp_cokernel P _).1 (h j)).trans
    (comp_zero).symm

/-! ## Ideals -/

/-- **An ideal of an algebra object**: a subobject that absorbs
multiplication by the algebra. -/
def IsIdeal [SmallCategory C] [MonoidalCategory C]
    (𝔸 : Ind C) [MonObj 𝔸] (I : Subobject 𝔸) : Prop :=
  I.Factors ((𝔸 ◁ I.arrow) ≫ μ[𝔸])

/-- **The zero subobject is an ideal.** -/
theorem isIdeal_bot [SmallCategory C] [MonoidalCategory C] [Abelian C]
    [MonoidalPreadditive C]
    (𝔸 : Ind C) [MonObj 𝔸] : IsIdeal 𝔸 ⊥ := by
  have hz : IsZero (Subobject.underlying.obj (⊥ : Subobject 𝔸)) :=
    IsZero.of_iso (isZero_zero (Ind C)) Subobject.botCoeIsoZero
  have h : (⊥ : Subobject 𝔸).arrow = 0 := hz.eq_zero_of_src _
  change (⊥ : Subobject 𝔸).Factors _
  rw [Subobject.bot_factors_iff_zero, h,
    MonoidalPreadditive.whiskerLeft_zero, zero_comp]

/-! ## Proper ideals -/

/-- **A proper subobject**: one through which the unit of the
algebra does not factor. -/
def IsProper [SmallCategory C] [MonoidalCategory C]
    (𝔸 : Ind C) [MonObj 𝔸] (I : Subobject 𝔸) : Prop :=
  ¬ I.Factors η[𝔸]

/-- **For an ideal, properness is exactly being different from the
whole algebra.**  If the unit factors through an ideal then the
arrow of the ideal is a split epimorphism, hence an isomorphism. -/
theorem isProper_iff_ne_top [SmallCategory C] [MonoidalCategory C]
    (𝔸 : Ind C) [MonObj 𝔸]
    {I : Subobject 𝔸} (hI : IsIdeal 𝔸 I) :
    IsProper 𝔸 I ↔ I ≠ ⊤ := by
  constructor
  · intro hp htop
    exact hp (htop ▸ Subobject.top_factors η[𝔸])
  · intro hne hfac
    obtain ⟨a, ha⟩ := exists_factor hfac
    obtain ⟨b, hb⟩ := exists_factor hI
    have key : (𝔸 ◁ a) ≫ (𝔸 ◁ I.arrow) ≫ μ[𝔸] = (ρ_ 𝔸).hom := by
      rw [← Category.assoc, ← MonoidalCategory.whiskerLeft_comp, ha,
        MonObj.mul_one]
    have hs : ((ρ_ 𝔸).inv ≫ (𝔸 ◁ a) ≫ b) ≫ I.arrow = 𝟙 𝔸 := by
      rw [Category.assoc, Category.assoc, hb, key, Iso.inv_hom_id]
    have : IsSplitEpi I.arrow := IsSplitEpi.mk' ⟨_, hs⟩
    have : IsIso I.arrow := isIso_of_mono_of_isSplitEpi _
    exact hne (Subobject.eq_top_of_isIso_arrow I)

/-- **The zero ideal is proper as soon as the unit is nonzero.** -/
theorem isProper_bot [SmallCategory C] [MonoidalCategory C] [Abelian C]
    (𝔸 : Ind C) [MonObj 𝔸] (hne : η[𝔸] ≠ 0) :
    IsProper 𝔸 ⊥ := fun h =>
  hne ((Subobject.bot_factors_iff_zero η[𝔸]).1 h)

/-! ## Suprema of ideals -/

/-- Arbitrary suprema of subobjects of an ind-object, from
well-poweredness, images and coproducts. -/
noncomputable instance completeSemilatticeSupSubobject
    [SmallCategory C] [Abelian C]
    (A : Ind C) :
    CompleteSemilatticeSup (Subobject A) :=
  Subobject.completeSemilatticeSup.{v}

/-! ## Compactness of the unit -/

/-- **Compactness transports along an isomorphism.** -/
theorem IndCompactObj.of_iso [SmallCategory C]
    {X Y : Ind C} (e : X ≅ Y)
    (h : IndCompactObj X) : IndCompactObj Y := fun D f => by
  obtain ⟨i, g, hg⟩ := h D (e.hom ≫ f)
  refine ⟨i, e.inv ≫ g, ?_⟩
  rw [Category.assoc, hg, ← Category.assoc, e.inv_hom_id,
    Category.id_comp]

/-- **The unit object of the ind-completion is compact**: it is the
embedded unit of the small category. -/
theorem indCompactObj_tensorUnit [SmallCategory C] [MonoidalCategory C] :
    IndCompactObj (𝟙_ (Ind C)) :=
  IndCompactObj.of_iso (indOfUnitIso (C := C)).symm
    (indCompactObj_indOf (𝟙_ C))

/-! ## The union of a directed family of subobjects -/

/-- A family of subobjects of an ind-object is `v`-small. -/
instance small_subobject_subset [SmallCategory C] [Abelian C]
    {A : Ind C} (s : Set (Subobject A)) :
    Small.{v} ↥s :=
  small_of_injective (f := (Subtype.val : ↥s → Subobject A))
    Subtype.val_injective

/-- A `v`-small copy of a family of subobjects of an ind-object,
serving as the index of the diagram of its members. -/
def SubIndex [SmallCategory C] [Abelian C]
    {A : Ind C} (s : Set (Subobject A)) : Type v :=
  Shrink.{v} ↥s

/-- The subobject named by an index. -/
noncomputable def SubIndex.val [SmallCategory C] [Abelian C]
    {A : Ind C} {s : Set (Subobject A)}
    (j : SubIndex s) : Subobject A :=
  ((equivShrink ↥s).symm j).1

/-- The subobject named by an index belongs to the family. -/
theorem SubIndex.val_mem [SmallCategory C] [Abelian C]
    {A : Ind C} {s : Set (Subobject A)}
    (j : SubIndex s) : SubIndex.val j ∈ s :=
  ((equivShrink ↥s).symm j).2

/-- Every member of the family is named by an index. -/
theorem SubIndex.val_index [SmallCategory C] [Abelian C]
    {A : Ind C} {s : Set (Subobject A)}
    {I : Subobject A} (hI : I ∈ s) :
    SubIndex.val (equivShrink ↥s ⟨I, hI⟩) = I :=
  congrArg Subtype.val (Equiv.symm_apply_apply _ _)

/-- The index of a family of subobjects, ordered by inclusion of the
subobjects it names. -/
noncomputable instance subIndexPreorder [SmallCategory C] [Abelian C]
    {A : Ind C}
    (s : Set (Subobject A)) : Preorder (SubIndex s) :=
  Preorder.lift SubIndex.val

/-- A morphism of the index category is an inclusion of the
subobjects it names. -/
theorem SubIndex.le_of_hom [SmallCategory C] [Abelian C]
    {A : Ind C} {s : Set (Subobject A)}
    {j k : SubIndex s} (h : j ⟶ k) :
    SubIndex.val j ≤ SubIndex.val k := (leOfHom h : j ≤ k)

/-- **The index of a nonempty directed family is filtered.** -/
theorem isFiltered_subIndex [SmallCategory C] [Abelian C]
    {A : Ind C} {s : Set (Subobject A)}
    (hne : s.Nonempty) (hdir : DirectedOn (· ≤ ·) s) :
    IsFiltered (SubIndex s) := by
  obtain ⟨x, hx⟩ := hne
  have : Nonempty (SubIndex s) := ⟨equivShrink ↥s ⟨x, hx⟩⟩
  have : IsDirectedOrder (SubIndex s) := by
    refine ⟨fun j k => ?_⟩
    obtain ⟨z, hz, h₁, h₂⟩ := hdir _ (SubIndex.val_mem j) _
      (SubIndex.val_mem k)
    refine ⟨equivShrink ↥s ⟨z, hz⟩, ?_, ?_⟩
    · change SubIndex.val j ≤ SubIndex.val _
      rw [SubIndex.val_index hz]; exact h₁
    · change SubIndex.val k ≤ SubIndex.val _
      rw [SubIndex.val_index hz]; exact h₂
  exact isFiltered_of_directed_le_nonempty _

/-- The diagram of the members of a family of subobjects. -/
noncomputable def subDiagram [SmallCategory C] [Abelian C]
    {A : Ind C} (s : Set (Subobject A)) :
    SubIndex s ⥤ Ind C where
  obj j := (SubIndex.val j : Ind C)
  map {j k} h := Subobject.ofLE _ _ (SubIndex.le_of_hom h)
  map_id j := by
    refine (cancel_mono (SubIndex.val j).arrow).1 ?_
    rw [Subobject.ofLE_arrow, Category.id_comp]
  map_comp {j k l} f g := by
    refine (cancel_mono (SubIndex.val l).arrow).1 ?_
    rw [Category.assoc, Subobject.ofLE_arrow, Subobject.ofLE_arrow,
      Subobject.ofLE_arrow]

/-- The tautological cocone of `RS.subDiagram` on the ambient
ind-object, given by the arrows of the members. -/
noncomputable def subCocone [SmallCategory C] [Abelian C]
    {A : Ind C} (s : Set (Subobject A)) :
    Cocone (subDiagram s) :=
  Cocone.mk A
    { app := fun j => (SubIndex.val j).arrow
      naturality := fun _ _ h =>
        (Subobject.ofLE_arrow (SubIndex.le_of_hom h)).trans
          (Category.comp_id _).symm }

/-- The comparison morphism from the colimit of a family of
subobjects to the ambient ind-object. -/
noncomputable def subUnionHom [SmallCategory C] [Abelian C]
    {A : Ind C} (s : Set (Subobject A)) :
    colimit (subDiagram s) ⟶ A :=
  colimit.desc _ (subCocone s)

/-- The colimit injections composed with the comparison morphism are
the arrows of the members. -/
theorem ι_subUnionHom [SmallCategory C] [Abelian C]
    {A : Ind C} (s : Set (Subobject A))
    (j : SubIndex s) :
    colimit.ι (subDiagram s) j ≫ subUnionHom s =
      (SubIndex.val j).arrow :=
  colimit.ι_desc _ _

/-- **The colimit of a constant diagram over a filtered index is the
constant value.** -/
noncomputable def constColimitIso [SmallCategory C]
    {J : Type v} [SmallCategory J]
    [IsFiltered J] (A : Ind C) :
    colimit ((Functor.const J).obj A) ≅ A :=
  haveI : IsConnected J := IsFiltered.isConnected J
  (colimit.isColimit ((Functor.const J).obj A)).coconePointUniqueUpToIso
    (isColimitConstCocone J A)

/-- Each injection of the constant colimit is undone by
`RS.constColimitIso`. -/
theorem ι_constColimitIso [SmallCategory C]
    {J : Type v} [SmallCategory J]
    [IsFiltered J] (A : Ind C) (j : J) :
    colimit.ι ((Functor.const J).obj A) j ≫ (constColimitIso A).hom
      = 𝟙 A := by
  have : IsConnected J := IsFiltered.isConnected J
  exact Eq.trans (IsColimit.comp_coconePointUniqueUpToIso_hom _ _ _)
    rfl

/-- **The union of a filtered family of subobjects is a
subobject**: filtered colimits are exact in the ind-completion, so
the comparison morphism of `RS.subUnionHom` is a monomorphism. -/
instance mono_subUnionHom [SmallCategory C] [Abelian C]
    {A : Ind C} (s : Set (Subobject A))
    [IsFiltered (SubIndex s)] : Mono (subUnionHom s) := by
  have : ∀ j, Mono ((subCocone s).ι.app j) := fun j =>
    inferInstanceAs (Mono (SubIndex.val j).arrow)
  have : Mono ((subCocone s).ι) := NatTrans.mono_of_mono_app _
  have : Mono (colimMap ((subCocone s).ι)) := by
    rw [colimMap_eq]
    exact (colim (J := SubIndex s) (C := Ind C)).map_mono _
  have hd : subUnionHom s =
      colimMap ((subCocone s).ι) ≫ (constColimitIso A).hom := by
    refine colimit.hom_ext (fun j => ?_)
    have h₁ : colimit.ι (subDiagram s) j ≫ subUnionHom s =
        (subCocone s).ι.app j := colimit.ι_desc _ _
    have h₂ : colimit.ι (subDiagram s) j ≫
        (colimMap ((subCocone s).ι) ≫ (constColimitIso A).hom) =
        (subCocone s).ι.app j := by
      erw [← Category.assoc, ι_colimMap, Category.assoc,
        show colimit.ι ((Functor.const (SubIndex s)).obj
            (subCocone s).pt) j ≫ (constColimitIso A).hom = 𝟙 A from
          ι_constColimitIso A j]
      exact Category.comp_id _
    exact h₁.trans h₂.symm
  rw [hd]
  refine ⟨fun {Z} f g h => ?_⟩
  apply (cancel_mono (colimMap ((subCocone s).ι))).mp
  apply (Iso.cancel_iso_hom_right _ _ (constColimitIso (J := SubIndex s) A)).mp
  erw [Category.assoc, Category.assoc]
  exact h

/-! ## The chain condition -/

/-- **A nonempty directed family of proper ideals is bounded above by
a proper ideal.**  The bound is the union of the family: it is an
ideal because tensoring preserves the colimit of the members, and it
is proper because the unit is compact, so a factorisation of the unit
through the union already factors through a member. -/
theorem exists_ub_of_directed
    [SmallCategory C] [MonoidalCategory C] [Abelian C] [RigidCategory C]
    [MonoidalPreadditive C]
    (𝔸 : Ind C) [MonObj 𝔸]
    {c : Set (Subobject 𝔸)} (hne : c.Nonempty)
    (hdir : DirectedOn (· ≤ ·) c) (hid : ∀ I ∈ c, IsIdeal 𝔸 I)
    (hpr : ∀ I ∈ c, IsProper 𝔸 I) :
    ∃ ub : Subobject 𝔸, IsIdeal 𝔸 ub ∧ IsProper 𝔸 ub ∧
      ∀ I ∈ c, I ≤ ub := by
  have := isFiltered_subIndex hne hdir
  have harrow : (Subobject.mk (subUnionHom c)).arrow =
      (Subobject.underlyingIso (subUnionHom c)).hom ≫ subUnionHom c :=
    (Iso.inv_comp_eq _).1 (Subobject.underlyingIso_arrow _)
  have hlej : ∀ j : SubIndex c,
      SubIndex.val j ≤ Subobject.mk (subUnionHom c) := fun j =>
    le_trans (le_of_eq (Subobject.mk_arrow (SubIndex.val j)).symm)
      (Subobject.mk_le_mk_of_comm (colimit.ι (subDiagram c) j)
        (ι_subUnionHom c j))
  refine ⟨Subobject.mk (subUnionHom c), ?_, ?_, ?_⟩
  · have hstep : (Subobject.mk (subUnionHom c)).Factors
        ((𝔸 ◁ subUnionHom c) ≫ μ[𝔸]) := by
      refine factors_of_isColimit
        ((tensorLeft 𝔸).mapCocone (colimit.cocone (subDiagram c)))
        (isColimitOfPreserves _ (colimit.isColimit _)) _ _ (fun j => ?_)
      have hj : (𝔸 ◁ colimit.ι (subDiagram c) j) ≫
          ((𝔸 ◁ subUnionHom c) ≫ μ[𝔸]) =
          (𝔸 ◁ (SubIndex.val j).arrow) ≫ μ[𝔸] := by
        rw [← Category.assoc, ← MonoidalCategory.whiskerLeft_comp,
          ι_subUnionHom]
        rfl
      refine Eq.mpr (congrArg
        (fun t => (Subobject.mk (subUnionHom c)).Factors t) hj) ?_
      exact Subobject.factors_of_le _ (hlej j)
        (hid _ (SubIndex.val_mem j))
    have : Epi
        (𝔸 ◁ (Subobject.underlyingIso (subUnionHom c)).inv) :=
      inferInstanceAs (Epi ((tensorLeft 𝔸).map _))
    have hgoal : (𝔸 ◁ (Subobject.underlyingIso (subUnionHom c)).inv)
        ≫ (𝔸 ◁ (Subobject.mk (subUnionHom c)).arrow) ≫ μ[𝔸] =
        (𝔸 ◁ subUnionHom c) ≫ μ[𝔸] :=
      (Category.assoc _ _ _).symm.trans
        (congrArg (fun t => t ≫ μ[𝔸])
          ((MonoidalCategory.whiskerLeft_comp 𝔸 _ _).symm.trans
            (congrArg (fun t => 𝔸 ◁ t)
              (Subobject.underlyingIso_arrow (subUnionHom c)))))
    refine factors_of_epi_comp _
      (𝔸 ◁ (Subobject.underlyingIso (subUnionHom c)).inv) _ ?_
    exact Eq.mpr (congrArg
      (fun t => (Subobject.mk (subUnionHom c)).Factors t) hgoal) hstep
  · intro hfac
    obtain ⟨g, hg⟩ := exists_factor hfac
    obtain ⟨j, g₀, hg₀⟩ := indCompactObj_tensorUnit (C := C)
      (subDiagram c)
      (g ≫ (Subobject.underlyingIso (subUnionHom c)).hom)
    refine hpr _ (SubIndex.val_mem j) (factors_of_comm g₀ ?_)
    refine Eq.trans (congrArg (fun t => g₀ ≫ t)
      (ι_subUnionHom c j)).symm ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (congrArg (fun t => t ≫ subUnionHom c) hg₀) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    exact Eq.trans (congrArg (fun t => g ≫ t) harrow.symm) hg
  · intro I hI
    have h := hlej (equivShrink ↥c ⟨I, hI⟩)
    rwa [SubIndex.val_index hI] at h

/-! ## Maximal proper ideals -/

/-- **Every algebra with a nonzero unit has a maximal proper
ideal.** -/
theorem exists_maximal_ideal
    [SmallCategory C] [MonoidalCategory C] [Abelian C] [RigidCategory C]
    [MonoidalPreadditive C]
    (𝔸 : Ind C) [MonObj 𝔸]
    (hne : η[𝔸] ≠ 0) :
    ∃ 𝔪 : Subobject 𝔸, IsIdeal 𝔸 𝔪 ∧ IsProper 𝔸 𝔪 ∧
      ∀ J : Subobject 𝔸, IsIdeal 𝔸 J → IsProper 𝔸 J → 𝔪 ≤ J →
        J ≤ 𝔪 := by
  have hbdd : ∀ cc ⊆ {I : Subobject 𝔸 | IsIdeal 𝔸 I ∧ IsProper 𝔸 I},
      IsChain (· ≤ ·) cc → ∀ y ∈ cc,
      ∃ ub ∈ {I : Subobject 𝔸 | IsIdeal 𝔸 I ∧ IsProper 𝔸 I},
        ∀ z ∈ cc, z ≤ ub := by
    intro cc hcc hchain y hy
    obtain ⟨ub, h₁, h₂, h₃⟩ := exists_ub_of_directed 𝔸 ⟨y, hy⟩
      hchain.directedOn (fun I hI => (hcc hI).1)
      (fun I hI => (hcc hI).2)
    exact ⟨ub, ⟨h₁, h₂⟩, h₃⟩
  obtain ⟨m, -, hm⟩ := zorn_le_nonempty₀ _ hbdd ⊥
    ⟨isIdeal_bot 𝔸, isProper_bot 𝔸 hne⟩
  exact ⟨m, hm.1.1, hm.1.2,
    fun J hJ hJp hle => hm.2 ⟨hJ, hJp⟩ hle⟩

/-! ## Transport of an algebra structure along an epimorphism -/

/-- **An epimorphism transports an algebra structure.**  If a unit
and a multiplication on the target are compatible with those of the
source along an epimorphism, they satisfy the algebra laws. -/
@[reducible] noncomputable def monObjOfEpi
    [SmallCategory C] [MonoidalCategory C] [Abelian C] [RigidCategory C]
    [MonoidalPreadditive C]
    {A B : Ind C} [MonObj A]
    (p : A ⟶ B)
    [Epi p] (o : 𝟙_ (Ind C) ⟶ B) (m : B ⊗ B ⟶ B)
    (ho : η[A] ≫ p = o) (hm : (p ⊗ₘ p) ≫ m = μ[A] ≫ p) :
    MonObj B where
  one := o
  mul := m
  one_mul := by
    have : Epi (𝟙_ (Ind C) ◁ p) :=
      inferInstanceAs (Epi ((tensorLeft _).map p))
    have h₁ : (𝟙_ (Ind C) ◁ p) ≫ (o ▷ B) = (η[A] ▷ A) ≫ (p ⊗ₘ p) := by
      refine Eq.trans (tensorHom_def' o p).symm ?_
      rw [← tensorHom_id, tensorHom_comp_tensorHom, ho,
        Category.id_comp]
    refine (cancel_epi (𝟙_ (Ind C) ◁ p)).1 ?_
    rw [← Category.assoc, h₁, Category.assoc, hm, ← Category.assoc,
      MonObj.one_mul, leftUnitor_naturality]
  mul_one := by
    have : Epi (p ▷ 𝟙_ (Ind C)) :=
      inferInstanceAs (Epi ((tensorRight _).map p))
    have h₁ : (p ▷ 𝟙_ (Ind C)) ≫ (B ◁ o) = (A ◁ η[A]) ≫ (p ⊗ₘ p) := by
      refine Eq.trans (tensorHom_def p o).symm ?_
      rw [← id_tensorHom, tensorHom_comp_tensorHom, ho,
        Category.id_comp]
    refine (cancel_epi (p ▷ 𝟙_ (Ind C))).1 ?_
    rw [← Category.assoc, h₁, Category.assoc, hm, ← Category.assoc,
      MonObj.mul_one, rightUnitor_naturality]
  mul_assoc := by
    have h₁ : ((p ⊗ₘ p) ⊗ₘ p) ≫ (m ▷ B) = (μ[A] ▷ A) ≫ (p ⊗ₘ p) := by
      rw [← tensorHom_id, tensorHom_comp_tensorHom, hm,
        Category.comp_id, ← tensorHom_id, tensorHom_comp_tensorHom,
        Category.id_comp]
    have h₂ : (p ⊗ₘ (p ⊗ₘ p)) ≫ (B ◁ m) =
        (A ◁ μ[A]) ≫ (p ⊗ₘ p) := by
      rw [← id_tensorHom, tensorHom_comp_tensorHom, hm,
        Category.comp_id, ← id_tensorHom, tensorHom_comp_tensorHom,
        Category.id_comp]
    have hL : ((p ⊗ₘ p) ⊗ₘ p) ≫ (m ▷ B) ≫ m =
        ((μ[A] ▷ A) ≫ μ[A]) ≫ p := by
      rw [← Category.assoc, h₁, Category.assoc, hm, ← Category.assoc]
    have hR : ((p ⊗ₘ p) ⊗ₘ p) ≫ (α_ B B B).hom ≫ (B ◁ m) ≫ m =
        ((α_ A A A).hom ≫ (A ◁ μ[A]) ≫ μ[A]) ≫ p := by
      rw [← Category.assoc, associator_naturality, Category.assoc,
        ← Category.assoc (p ⊗ₘ (p ⊗ₘ p)), h₂, Category.assoc, hm]
      simp only [Category.assoc]
    refine (cancel_epi ((p ⊗ₘ p) ⊗ₘ p)).1 ?_
    rw [hL, hR, MonObj.mul_assoc]

/-- **An epimorphism transports commutativity.** -/
theorem isCommMonObj_of_epi
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C] [Abelian C]
    [RigidCategory C] [MonoidalPreadditive C]
    {A B : Ind C} [MonObj A] [IsCommMonObj A]
    [MonObj B] (p : A ⟶ B) [Epi p]
    (hm : (p ⊗ₘ p) ≫ μ[B] = μ[A] ≫ p) : IsCommMonObj B where
  mul_comm := by
    refine (cancel_epi (p ⊗ₘ p)).1 ?_
    rw [← Category.assoc, BraidedCategory.braiding_naturality,
      Category.assoc, hm, ← Category.assoc,
      IsCommMonObj.mul_comm A]

/-! ## The quotient of an algebra by an ideal -/

/-- The multiplication of the algebra against an ideal dies in the
quotient by that ideal. -/
theorem whiskerLeft_arrow_mul_π
    [SmallCategory C] [MonoidalCategory C] [Abelian C]
    (𝔸 : Ind C) [MonObj 𝔸]
    (𝔪 : Subobject 𝔸) (h𝔪 : IsIdeal 𝔸 𝔪) :
    (𝔸 ◁ 𝔪.arrow) ≫ μ[𝔸] ≫ cokernel.π 𝔪.arrow = 0 := by
  obtain ⟨b, hb⟩ := exists_factor h𝔪
  rw [← Category.assoc, ← hb, Category.assoc, cokernel.condition,
    comp_zero]

/-- The same on the other side, by commutativity. -/
theorem whiskerRight_arrow_mul_π
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C] [Abelian C]
    (𝔸 : Ind C) [MonObj 𝔸]
    [IsCommMonObj 𝔸] (𝔪 : Subobject 𝔸) (h𝔪 : IsIdeal 𝔸 𝔪) :
    (𝔪.arrow ▷ 𝔸) ≫ μ[𝔸] ≫ cokernel.π 𝔪.arrow = 0 := by
  have h : (𝔪.arrow ▷ 𝔸) ≫ μ[𝔸] =
      (β_ (𝔪 : Ind C) 𝔸).hom ≫ (𝔸 ◁ 𝔪.arrow) ≫ μ[𝔸] := by
    rw [← Category.assoc, ← BraidedCategory.braiding_naturality_left,
      Category.assoc, IsCommMonObj.mul_comm 𝔸]
  rw [← Category.assoc, h]
  simp only [Category.assoc]
  rw [whiskerLeft_arrow_mul_π 𝔸 𝔪 h𝔪, comp_zero]

/-- The multiplication of the algebra, descended in its second
variable to the quotient by an ideal. -/
noncomputable def quotMulAux
    [SmallCategory C] [MonoidalCategory C] [Abelian C] [RigidCategory C]
    [MonoidalPreadditive C]
    (𝔸 : Ind C) [MonObj 𝔸]
    (𝔪 : Subobject 𝔸) (h𝔪 : IsIdeal 𝔸 𝔪) :
    𝔸 ⊗ cokernel 𝔪.arrow ⟶ cokernel 𝔪.arrow :=
  (CokernelCofork.IsColimit.desc'
    (isColimitOfHasCokernelOfPreservesColimit (tensorLeft 𝔸) 𝔪.arrow)
    (μ[𝔸] ≫ cokernel.π 𝔪.arrow)
    (whiskerLeft_arrow_mul_π 𝔸 𝔪 h𝔪)).1

/-- The defining property of `RS.quotMulAux`. -/
theorem whiskerLeft_π_quotMulAux
    [SmallCategory C] [MonoidalCategory C] [Abelian C] [RigidCategory C]
    [MonoidalPreadditive C]
    (𝔸 : Ind C) [MonObj 𝔸]
    (𝔪 : Subobject 𝔸) (h𝔪 : IsIdeal 𝔸 𝔪) :
    (𝔸 ◁ cokernel.π 𝔪.arrow) ≫ quotMulAux 𝔸 𝔪 h𝔪 =
      μ[𝔸] ≫ cokernel.π 𝔪.arrow :=
  (CokernelCofork.IsColimit.desc'
    (isColimitOfHasCokernelOfPreservesColimit (tensorLeft 𝔸) 𝔪.arrow)
    (μ[𝔸] ≫ cokernel.π 𝔪.arrow)
    (whiskerLeft_arrow_mul_π 𝔸 𝔪 h𝔪)).2

/-- The half-descended multiplication kills the ideal in its first
variable as well. -/
theorem whiskerRight_quotMulAux
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C] [Abelian C]
    [RigidCategory C] [MonoidalPreadditive C]
    (𝔸 : Ind C) [MonObj 𝔸]
    [IsCommMonObj 𝔸] (𝔪 : Subobject 𝔸) (h𝔪 : IsIdeal 𝔸 𝔪) :
    (𝔪.arrow ▷ cokernel 𝔪.arrow) ≫ quotMulAux 𝔸 𝔪 h𝔪 = 0 := by
  have : Epi ((𝔪 : Ind C) ◁ cokernel.π 𝔪.arrow) :=
    inferInstanceAs (Epi ((tensorLeft _).map _))
  refine zero_of_epi_comp ((𝔪 : Ind C) ◁ cokernel.π 𝔪.arrow) ?_
  rw [← Category.assoc, whisker_exchange, Category.assoc,
    whiskerLeft_π_quotMulAux, whiskerRight_arrow_mul_π 𝔸 𝔪 h𝔪]

/-- **The multiplication of the quotient algebra.** -/
noncomputable def quotMul
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C] [Abelian C]
    [RigidCategory C] [MonoidalPreadditive C]
    (𝔸 : Ind C) [MonObj 𝔸] [IsCommMonObj 𝔸]
    (𝔪 : Subobject 𝔸) (h𝔪 : IsIdeal 𝔸 𝔪) :
    cokernel 𝔪.arrow ⊗ cokernel 𝔪.arrow ⟶ cokernel 𝔪.arrow :=
  (CokernelCofork.IsColimit.desc'
    (isColimitOfHasCokernelOfPreservesColimit
      (tensorRight (cokernel 𝔪.arrow)) 𝔪.arrow)
    (quotMulAux 𝔸 𝔪 h𝔪) (whiskerRight_quotMulAux 𝔸 𝔪 h𝔪)).1

/-- The defining property of `RS.quotMul`. -/
theorem whiskerRight_π_quotMul
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C] [Abelian C]
    [RigidCategory C] [MonoidalPreadditive C]
    (𝔸 : Ind C) [MonObj 𝔸]
    [IsCommMonObj 𝔸] (𝔪 : Subobject 𝔸) (h𝔪 : IsIdeal 𝔸 𝔪) :
    (cokernel.π 𝔪.arrow ▷ cokernel 𝔪.arrow) ≫ quotMul 𝔸 𝔪 h𝔪 =
      quotMulAux 𝔸 𝔪 h𝔪 :=
  (CokernelCofork.IsColimit.desc'
    (isColimitOfHasCokernelOfPreservesColimit
      (tensorRight (cokernel 𝔪.arrow)) 𝔪.arrow)
    (quotMulAux 𝔸 𝔪 h𝔪) (whiskerRight_quotMulAux 𝔸 𝔪 h𝔪)).2

/-- **The projection is multiplicative.** -/
theorem tensorHom_π_quotMul
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C] [Abelian C]
    [RigidCategory C] [MonoidalPreadditive C]
    (𝔸 : Ind C) [MonObj 𝔸] [IsCommMonObj 𝔸]
    (𝔪 : Subobject 𝔸) (h𝔪 : IsIdeal 𝔸 𝔪) :
    (cokernel.π 𝔪.arrow ⊗ₘ cokernel.π 𝔪.arrow) ≫ quotMul 𝔸 𝔪 h𝔪 =
      μ[𝔸] ≫ cokernel.π 𝔪.arrow := by
  rw [tensorHom_def', Category.assoc, whiskerRight_π_quotMul,
    whiskerLeft_π_quotMulAux]

/-- **The quotient of an algebra by an ideal is an algebra.** -/
@[reducible] noncomputable def quotMonObj
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C] [Abelian C]
    [RigidCategory C] [MonoidalPreadditive C]
    (𝔸 : Ind C) [MonObj 𝔸]
    [IsCommMonObj 𝔸] (𝔪 : Subobject 𝔸) (h𝔪 : IsIdeal 𝔸 𝔪) :
    MonObj (cokernel 𝔪.arrow) :=
  monObjOfEpi (cokernel.π 𝔪.arrow) (η[𝔸] ≫ cokernel.π 𝔪.arrow)
    (quotMul 𝔸 𝔪 h𝔪) rfl (tensorHom_π_quotMul 𝔸 𝔪 h𝔪)

/-! ## Pulling ideals back along the projection -/

/-- **Pulling a subobject back**: a morphism factors through the
pullback of a subobject exactly when its composite factors through
the subobject. -/
theorem factors_pullback_iff [SmallCategory C] [Abelian C]
    {A B W : Ind C} (I : Subobject B)
    (p : A ⟶ B) (h : W ⟶ A) :
    (Subobject.mk (pullback.snd I.arrow p)).Factors h ↔
      I.Factors (h ≫ p) := by
  have harrow : (Subobject.underlyingIso (pullback.snd I.arrow p)).inv
      ≫ (Subobject.mk (pullback.snd I.arrow p)).arrow =
      pullback.snd I.arrow p := Subobject.underlyingIso_arrow _
  have harrow' : (Subobject.mk (pullback.snd I.arrow p)).arrow =
      (Subobject.underlyingIso (pullback.snd I.arrow p)).hom ≫
        pullback.snd I.arrow p := (Iso.inv_comp_eq _).1 harrow
  constructor
  · intro hf
    obtain ⟨l, hl⟩ := exists_factor hf
    refine factors_of_comm ((l ≫
      (Subobject.underlyingIso (pullback.snd I.arrow p)).hom) ≫
        pullback.fst I.arrow p) ?_
    rw [Category.assoc, pullback.condition, ← Category.assoc,
      Category.assoc l, ← harrow', hl]
  · intro hf
    obtain ⟨k, hk⟩ := exists_factor hf
    refine factors_of_comm (pullback.lift k h hk ≫
      (Subobject.underlyingIso (pullback.snd I.arrow p)).inv) ?_
    rw [Category.assoc, harrow, pullback.lift_snd]

/-! ## The simple quotient -/

/-- **Every commutative algebra object of the ind-completion with a
nonzero unit has a simple quotient**: a quotient algebra whose only
ideals are the zero subobject and the whole object.  The quotient is
by a maximal proper ideal, and ideals of the quotient correspond to
ideals of the algebra containing that maximal ideal. -/
theorem exists_simple_quotient
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C] [Abelian C]
    [RigidCategory C] [MonoidalPreadditive C]
    (𝔸 : Ind C) [MonObj 𝔸]
    [IsCommMonObj 𝔸] (hne : η[𝔸] ≠ 0) :
    ∃ (𝔹 : Ind C) (_ : MonObj 𝔹) (_ : IsCommMonObj 𝔹) (π : 𝔸 ⟶ 𝔹),
      η[𝔹] ≠ 0 ∧ Epi π ∧ IsMonHom π ∧
      (∀ I : Subobject 𝔹, IsIdeal 𝔹 I → I = ⊥ ∨ I = ⊤) := by
  obtain ⟨𝔪, hid, hpr, hmax⟩ := exists_maximal_ideal 𝔸 hne
  let : MonObj (cokernel 𝔪.arrow) := quotMonObj 𝔸 𝔪 hid
  have hmul : (cokernel.π 𝔪.arrow ⊗ₘ cokernel.π 𝔪.arrow) ≫
      μ[cokernel 𝔪.arrow] = μ[𝔸] ≫ cokernel.π 𝔪.arrow :=
    tensorHom_π_quotMul 𝔸 𝔪 hid
  let : IsCommMonObj (cokernel 𝔪.arrow) :=
    isCommMonObj_of_epi (cokernel.π 𝔪.arrow) hmul
  have : IsMonHom (cokernel.π 𝔪.arrow) := ⟨rfl, hmul.symm⟩
  refine ⟨cokernel 𝔪.arrow, inferInstance, inferInstance,
    cokernel.π 𝔪.arrow, ?_, inferInstance, inferInstance, ?_⟩
  · intro h0
    exact hpr ((factors_iff_comp_cokernel 𝔪 η[𝔸]).2 h0)
  · intro I hI
    by_cases hIp : IsProper (cokernel 𝔪.arrow) I
    · left
      obtain ⟨t, ht⟩ := exists_factor
        ((factors_pullback_iff I (cokernel.π 𝔪.arrow)
          (Subobject.mk
            (pullback.snd I.arrow (cokernel.π 𝔪.arrow))).arrow).1
          (Subobject.factors_self _))
      have hPid : IsIdeal 𝔸
          (Subobject.mk (pullback.snd I.arrow
            (cokernel.π 𝔪.arrow))) := by
        refine (factors_pullback_iff I (cokernel.π 𝔪.arrow) _).2 ?_
        have h1 : (𝔸 ◁ (Subobject.mk (pullback.snd I.arrow
              (cokernel.π 𝔪.arrow))).arrow) ≫
            (𝔸 ◁ cokernel.π 𝔪.arrow) =
            (𝔸 ◁ t) ≫ (𝔸 ◁ I.arrow) := by
          rw [← MonoidalCategory.whiskerLeft_comp,
            ← MonoidalCategory.whiskerLeft_comp, ht]
        have hcomp : ((𝔸 ◁ (Subobject.mk (pullback.snd I.arrow
              (cokernel.π 𝔪.arrow))).arrow) ≫ μ[𝔸]) ≫
              cokernel.π 𝔪.arrow =
            (𝔸 ◁ t) ≫ (cokernel.π 𝔪.arrow ▷ (I : Ind C)) ≫
              (cokernel 𝔪.arrow ◁ I.arrow) ≫
                μ[cokernel 𝔪.arrow] := by
          rw [Category.assoc, ← hmul, tensorHom_def']
          simp only [Category.assoc]
          rw [← Category.assoc (𝔸 ◁ (Subobject.mk (pullback.snd
            I.arrow (cokernel.π 𝔪.arrow))).arrow), h1]
          simp only [Category.assoc]
          rw [← Category.assoc (𝔸 ◁ I.arrow), whisker_exchange]
          simp only [Category.assoc]
        rw [hcomp]
        exact Subobject.factors_of_factors_right _
          (Subobject.factors_of_factors_right _ hI)
      have hPpr : IsProper 𝔸
          (Subobject.mk (pullback.snd I.arrow
            (cokernel.π 𝔪.arrow))) := fun hf =>
        hIp ((factors_pullback_iff I (cokernel.π 𝔪.arrow) η[𝔸]).1 hf)
      have hmP : 𝔪 ≤ Subobject.mk (pullback.snd I.arrow
          (cokernel.π 𝔪.arrow)) :=
        Subobject.le_of_factors
          ((factors_pullback_iff I (cokernel.π 𝔪.arrow) 𝔪.arrow).2
            (by rw [cokernel.condition]; exact Subobject.factors_zero))
      have hPm := hmax _ hPid hPpr hmP
      have hsnd : pullback.snd I.arrow (cokernel.π 𝔪.arrow) =
          (Subobject.underlyingIso (pullback.snd I.arrow
            (cokernel.π 𝔪.arrow))).inv ≫
            Subobject.ofLE _ _ hPm ≫ 𝔪.arrow := by
        rw [Subobject.ofLE_arrow, Subobject.underlyingIso_arrow]
      have hzero : pullback.snd I.arrow (cokernel.π 𝔪.arrow) ≫
          cokernel.π 𝔪.arrow = 0 := by
        rw [hsnd, Category.assoc, Category.assoc,
          cokernel.condition, comp_zero, comp_zero]
      have : Epi (pullback.fst I.arrow (cokernel.π 𝔪.arrow)) :=
        Abelian.epi_pullback_of_epi_g _ _
      have hIarrow : I.arrow = 0 := by
        refine zero_of_epi_comp
          (pullback.fst I.arrow (cokernel.π 𝔪.arrow)) ?_
        rw [pullback.condition, hzero]
      exact (Subobject.mk_arrow I).symm.trans
        (Subobject.mk_eq_bot_iff_zero.2 hIarrow)
    · right
      exact not_not.1
        (fun hne' => hIp ((isProper_iff_ne_top _ hI).2 hne'))

end RS
