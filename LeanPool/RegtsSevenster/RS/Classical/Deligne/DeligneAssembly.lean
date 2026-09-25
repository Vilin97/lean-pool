/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.DoubledSplit
public import LeanPool.RegtsSevenster.RS.Classical.Deligne.FibreLinear
public import LeanPool.RegtsSevenster.RS.Classical.Deligne.PointMonoidal

/-!
# Deligne's theorem assembled

`RS.deligne_theorem` proves `RS.DeligneTheoremStatement`
(*Catégories tensorielles*, Théorème 0.6).  It is
`RS.deligne_theorem_of_braided`, which assembles the statement from
`RS.BraidedFibreHypothesis` — that the fibre functor
`RS.deligneFibre` of a splitting algebra at a complex point is
symmetric monoidal — applied to `RS.braidedFibreHypothesis`, which
discharges it from `RS.nonempty_braided_deligneFibre`.

The route is not Deligne's.  His §4 obtains the passage from an
arbitrary nonzero algebra of scalars to ℂ by descent along a
faithfully flat `Isom⊗` torsor.  Here the tensor generator alone is
split and one passes to a quotient by a maximal ideal: over a simple
algebra the regular module and its twist by the odd line are simple
objects of the module category, so a free mixed module is semisimple
of finite length, the objects the algebra splits are closed under
subquotients, and the scalars are a field of countable dimension over
ℂ, hence ℂ.  This is the pattern of Coulembier, *Tannakian categories
in positive characteristic*, Duke Math. J. **169** (2020), Lemma
3.3.2(ii), with Lemmas 1.2.10 and 1.5.2.

* `RS.deligneTheoremStatement_of_small`
  ([SmallReduction.lean](SmallReduction.lean)) reduces the statement,
  which quantifies over essentially small categories, to the case of
  a genuinely small one.
* A tensor category need not contain an odd line, so the small
  category is replaced by its ℤ/2-graded doubling, whose
  ind-completion carries the odd line `RS.doubledIndOddLine`
  ([Prop21General.lean](Prop21General.lean)).
* `RS.exists_splitting_simple_algebra_doubled`
  ([DoubledSplit.lean](DoubledSplit.lean)) produces the simple
  commutative algebra of the ind-completion of the doubling that
  splits every embedded object into a mixed sum of copies of the unit
  and of the odd line, together with a complex point of its
  Γ-algebra.
* Simplicity supplies the sections that exactness of the fibre
  functor consumes.  An embedded short exact sequence has an
  epimorphic right-hand map, so the free-module functor sends it to
  an epimorphism (`RS.epi_freeModMap`), and over a simple algebra
  every epimorphism out of a free mixed module splits
  (`RS.exists_section_of_simple`,
  [SimpleSplit.lean](SimpleSplit.lean)).
* `RS.deligneFibreFunctorOfPoint` collects `RS.deligneFibre` and its
  properties into a `RS.DeligneFibreFunctor`; the ℂ-linear clause is
  `RS.superVectFunctor_linear` fed by `RS.fibreFun_linear` and
  `RS.indOfFunctorLinear`.
* `RS.DeligneFibreFunctor.precompose` restricts the fibre functor of
  the doubling along the even embedding, which is strong braided
  monoidal, exact, faithful and ℂ-linear.

One compatibility is needed for the last step.  The even embedding is
ℂ-linear for the structure the doubling inherits componentwise from
its base, whereas the fibre construction runs at the structure induced
by the scalar unit, `RS.linearOfScalarUnit`.  The two agree:
`RS.scalarSmul_scalarUnitEquiv` identifies the scalar action of a
scalar unit with the ambient action in a monoidally ℂ-linear category,
and `RS.evenEmbedLinear_scalarUnit` reads that off for the even
embedding.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

noncomputable section

/-! ## The scalar action of a scalar unit is the ambient action -/

section ScalarBridge

variable {D : Type u}

/-- **The endomorphism attached to a scalar is the rescaled
identity**, when the scalar unit is the ambient action of ℂ on the
endomorphisms of the tensor unit: whiskering `c • 𝟙` onto `X` gives
`c • 𝟙` again because the tensor product is ℂ-bilinear, and the two
unitors then cancel. -/
theorem scalarEnd_scalarUnitEquiv
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [CategoryTheory.Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
    (h : HasScalarUnit D) (c : ℂ)
    (X : D) : scalarEnd (scalarUnitEquiv h) c X = c • 𝟙 X := by
  have hs : scalarHom (scalarUnitEquiv h) c = c • 𝟙 (𝟙_ D) := rfl
  change (λ_ X).inv ≫ (scalarHom (scalarUnitEquiv h) c ▷ X) ≫
    (λ_ X).hom = c • 𝟙 X
  rw [hs, MonoidalLinear.smul_whiskerRight, id_whiskerRight,
    CategoryTheory.Linear.smul_comp, CategoryTheory.Linear.comp_smul,
    Category.id_comp, Iso.inv_hom_id]

/-- **The ℂ-linear structure induced by the ambient scalar unit is the
ambient one.**  In a monoidally ℂ-linear category the action of
`RS.linearOfScalarUnit (scalarUnitEquiv h)` on a hom-set is the given
action, so the two structures may be used interchangeably. -/
theorem scalarSmul_scalarUnitEquiv
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [CategoryTheory.Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
    (h : HasScalarUnit D) {X Y : D}
    (c : ℂ) (f : X ⟶ Y) :
    scalarSmul (scalarUnitEquiv h) c f = c • f := by
  rw [scalarSmul_eq, scalarEnd_scalarUnitEquiv,
    CategoryTheory.Linear.smul_comp, Category.id_comp]

end ScalarBridge

/-! ## The even embedding at the scalar-unit structure -/

section EvenEmbedLinear

variable {B : Type v}

/-- The scalar action of `RS.doubledScalarUnit` on the doubling is the
action the doubling inherits componentwise from its base. -/
theorem scalarSmul_doubledScalarUnit
    [SmallCategory B] [Abelian B] [CategoryTheory.Linear ℂ B]
    [MonoidalCategory B] [MonoidalPreadditive B] [MonoidalLinear ℂ B]
    (hu : HasScalarUnit B)
    {V W : Doubled B} (c : ℂ) (f : V ⟶ W) :
    scalarSmul (doubledScalarUnit hu) c f = c • f :=
  scalarSmul_scalarUnitEquiv (hasScalarUnit_doubled hu) c f

/-- The even embedding carries a rescaled morphism to the scalar-unit
rescaling of its image. -/
theorem evenEmbed_map_smul_doubled
    [SmallCategory B] [Abelian B] [CategoryTheory.Linear ℂ B]
    [MonoidalCategory B] [MonoidalPreadditive B] [MonoidalLinear ℂ B]
    (hu : HasScalarUnit B) (c : ℂ)
    {V W : B} (f : V ⟶ W) :
    (Doubled.evenEmbed : B ⥤ Doubled B).map (c • f) =
      scalarSmul (doubledScalarUnit hu) c
        ((Doubled.evenEmbed : B ⥤ Doubled B).map f) := by
  rw [scalarSmul_doubledScalarUnit]
  exact Functor.Linear.map_smul (R := ℂ) f c

/-- **The even embedding is ℂ-linear for the scalar-unit structure**
of the doubling, the structure at which the fibre construction runs.
-/
theorem evenEmbedLinear_scalarUnit
    [SmallCategory B] [Abelian B] [CategoryTheory.Linear ℂ B]
    [MonoidalCategory B] [MonoidalPreadditive B] [MonoidalLinear ℂ B]
    (hu : HasScalarUnit B) :
    letI := linearOfScalarUnit (doubledScalarUnit hu)
    Functor.Linear ℂ (Doubled.evenEmbed : B ⥤ Doubled B) :=
  letI := linearOfScalarUnit (doubledScalarUnit hu)
  ⟨fun f c => evenEmbed_map_smul_doubled hu c f⟩

end EvenEmbedLinear

/-! ## The symmetry of the fibre functor -/

/-- **The fibre functor of a splitting algebra at a complex point is
symmetric monoidal.**  The assembly below takes this clause of
Deligne's conclusion as a hypothesis, which
`RS.braidedFibreHypothesis` discharges from
`RS.nonempty_braided_deligneFibre`; the strong monoidal structure of
the composite is `RS.fibreRestrictMonoidal`, and the Koszul sign of
`RS.SuperVect` is the braiding it transports. -/
def BraidedFibreHypothesis : Prop :=
  ∀ (C : Type v) [SmallCategory C] [MonoidalCategory C]
    [SymmetricCategory C] [Abelian C] [RigidCategory C]
    [MonoidalPreadditive C]
    [CategoryTheory.Linear ℂ (Ind C)] [MonoidalLinear ℂ (Ind C)]
    (L : OddLine (Ind C)) (𝔸 : Ind C) [MonObj 𝔸] [IsCommMonObj 𝔸]
    (hsp : SplitsOn L 𝔸 (indOf : C ⥤ Ind C))
    (pt : SuperPoint (gammaAlgebra (Ind C) L 𝔸)),
    Nonempty (deligneFibre L 𝔸 hsp pt).Braided

/-! ## The fibre functor of a splitting algebra, packaged -/

section GeneralFibre

variable {C : Type v}

/-- **The conclusion of Deligne's theorem for a category split by an
algebra with a complex point.**  Every clause of
`RS.DeligneFibreFunctor` is available for `RS.deligneFibre`: it is
additive and ℂ-linear because the embedding, the fibre functor over
the algebra and base change all are; it is exact because the sections
make each embedded short exact sequence split after base change; and
it is faithful because the unit of the algebra is a monomorphism.
Symmetry is the hypothesis `hbraid`. -/
def deligneFibreFunctorOfPoint
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C] [Abelian C]
    [RigidCategory C] [MonoidalPreadditive C] [CategoryTheory.Linear ℂ C]
    [CategoryTheory.Linear ℂ (Ind C)] [MonoidalLinear ℂ (Ind C)]
    [∀ Z : Ind C, (tensorRight Z).PreservesMonomorphisms]
    [(indOf : C ⥤ Ind C).Additive] [Functor.Linear ℂ (indOf : C ⥤ Ind C)]
    (L : OddLine (Ind C)) (𝔸 : Ind C) [MonObj 𝔸] [IsCommMonObj 𝔸]
    (hmono : Mono η[𝔸])
    (hsp : SplitsOn L 𝔸 (indOf : C ⥤ Ind C))
    (hsec : ∀ T : CategoryTheory.ShortComplex C, T.ShortExact →
      ∃ s : freeMod 𝔸 ((T.map (indOf : C ⥤ Ind C)).X₃) ⟶
          freeMod 𝔸 ((T.map (indOf : C ⥤ Ind C)).X₂),
        s ≫ freeModMap 𝔸 ((T.map (indOf : C ⥤ Ind C)).g) =
          𝟙 (freeMod 𝔸 ((T.map (indOf : C ⥤ Ind C)).X₃)))
    (pt : SuperPoint (gammaAlgebra (Ind C) L 𝔸))
    (hbraid : (deligneFibre L 𝔸 hsp pt).Braided) :
    DeligneFibreFunctor C where
  ω := deligneFibre L 𝔸 hsp pt
  braided := hbraid
  additive := deligneFibre_additive L 𝔸 hsp pt
  linear := superVectFunctor_linear pt _ _ _
  faithful := deligneFibre_faithful L 𝔸 hmono hsp hsec pt
  preservesFiniteLimits :=
    deligneFibre_preservesFiniteLimits L 𝔸 hsp hsec pt
  preservesFiniteColimits :=
    deligneFibre_preservesFiniteColimits L 𝔸 hsp hsec pt

end GeneralFibre

/-! ## Deligne's theorem -/

section Assembly

variable {B : Type v}

attribute [local instance] Doubled.hasFiniteBiproducts

/-- **Deligne's theorem for a small category.**  The doubling of `B`
carries every hypothesis, and its ind-completion carries an odd line,
so the simple algebra `𝔹` that splits the embedding is available
together with a complex point of its Γ-algebra.  Simplicity of `𝔹`
supplies the sections, the nonvanishing of its unit makes that unit a
monomorphism, and the resulting fibre functor of `Doubled B` restricts
along the even embedding to one of `B`. -/
theorem exists_deligneFibreFunctor_small
    [SmallCategory B] [Abelian B] [CategoryTheory.Linear ℂ B]
    [MonoidalCategory B] [SymmetricCategory B] [MonoidalPreadditive B]
    [MonoidalLinear ℂ B] [HasFiniteBiproducts B] [RigidCategory B]
    (P : SchurPackage.{v})
    (P₀ : SchurPackage.{0}) (hbr : BraidedFibreHypothesis.{v})
    (hu : HasScalarUnit B) (X : B) (hgen : TensorGeneratedBy B X)
    (hgrow : ModerateLengthGrowth B) :
    Nonempty (DeligneFibreFunctor B) := by
  let := linearOfScalarUnit (doubledScalarUnit hu)
  let := monoidalLinearOfScalarUnitBraided (doubledScalarUnit hu)
  let := linearOfScalarUnit (indScalarUnit (doubledScalarUnit hu))
  let := monoidalLinearOfScalarUnitBraided
    (indScalarUnit (doubledScalarUnit hu))
  obtain ⟨𝔹, hmon, hcomm, hne, hsimple, hsp, ⟨pt⟩⟩ :=
    exists_splitting_simple_algebra_doubled P P₀ hu X hgen hgrow
  let := hmon
  let := hcomm
  have hpm : ∀ Z : Ind (Doubled B),
      (tensorRight Z).PreservesMonomorphisms := fun _ => inferInstance
  have hmono : Mono η[𝔹] :=
    mono_unit_ind (simple_unit_of_hasScalarUnit
      (hasScalarUnit_of_scalarUnit (doubledScalarUnit hu))) 𝔹 hne
  have hsec : ∀ T : CategoryTheory.ShortComplex (Doubled B),
      T.ShortExact →
      ∃ s : freeMod 𝔹 ((T.map
            (indOf : Doubled B ⥤ Ind (Doubled B))).X₃) ⟶
          freeMod 𝔹 ((T.map
            (indOf : Doubled B ⥤ Ind (Doubled B))).X₂),
        s ≫ freeModMap 𝔹 ((T.map
            (indOf : Doubled B ⥤ Ind (Doubled B))).g) =
          𝟙 (freeMod 𝔹 ((T.map
            (indOf : Doubled B ⥤ Ind (Doubled B))).X₃)) := by
    intro T hT
    have := (indOf_shortExact hT).epi_g
    exact exists_section_of_simple 𝔹 doubledIndOddLine hsimple hne
      ((T.map (indOf : Doubled B ⥤ Ind (Doubled B))).g) (hsp T.X₂)
      (epi_freeModMap 𝔹 _ inferInstance)
  let := indOf_additive (C := Doubled B)
  let := indOfFunctorLinear (doubledScalarUnit hu)
  let := evenEmbedLinear_scalarUnit hu
  have hb := (hbr (Doubled B) doubledIndOddLine 𝔹 hsp pt).some
  have hF : DeligneFibreFunctor (Doubled B) :=
    deligneFibreFunctorOfPoint doubledIndOddLine 𝔹 hmono hsp hsec pt hb
  exact ⟨hF.precompose (Doubled.evenEmbed : B ⥤ Doubled B)⟩

/-- **Deligne's theorem** (*Catégories tensorielles*, Théorème 0.6),
conditional on the symmetry of the fibre functor: every essentially
small abelian ℂ-linear rigid symmetric monoidal category with
ℂ-bilinear tensor product, scalar unit endomorphisms, a finite tensor
generator and moderate growth of the lengths of its tensor powers
admits an exact faithful ℂ-linear symmetric monoidal fibre functor to
finite-dimensional super vector spaces. -/
theorem deligne_theorem_of_braided (P : SchurPackage.{v})
    (P₀ : SchurPackage.{0}) (hbr : BraidedFibreHypothesis.{v}) :
    DeligneTheoremStatement.{u, v} := by
  refine deligneTheoremStatement_of_small ?_
  intro A _ _ _ _ _ _ _ _ _ hu hgen hgrow
  obtain ⟨X, hX⟩ := hgen
  exact exists_deligneFibreFunctor_small P P₀ hbr hu X hX hgrow

end Assembly

end

/-- **The braided hypothesis is discharged**: the fibre functor of a
splitting algebra at a complex point is symmetric monoidal, because
the fibre functor over the algebra is and the base change at the
point is. -/
theorem braidedFibreHypothesis : BraidedFibreHypothesis.{v} :=
  fun _ _ _ _ _ _ _ _ _ L 𝔸 _ _ hsp pt =>
    nonempty_braided_deligneFibre L 𝔸 hsp pt

/-- **Deligne's theorem** (*Catégories tensorielles*, Théorème 0.6):
every essentially small abelian ℂ-linear rigid symmetric monoidal
category with ℂ-bilinear tensor product, scalar unit endomorphisms, a
finite tensor generator and moderate growth of the lengths of its
tensor powers admits an exact faithful ℂ-linear symmetric monoidal
fibre functor to finite-dimensional super vector spaces. -/
theorem deligne_theorem : DeligneTheoremStatement.{u, v} :=
  deligne_theorem_of_braided schurPackage schurPackage
    braidedFibreHypothesis

end RS
