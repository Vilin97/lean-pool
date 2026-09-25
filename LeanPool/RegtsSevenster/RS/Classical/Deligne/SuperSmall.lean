/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.SuperRealize

/-!
# A small model of `SuperVect`

`RS.SuperVect` is a large category: its objects are pairs of
finite-dimensional complex vector spaces drawn from `Type`, so the
type of objects lives in `Type 1`, while every hom-space is a pair
of linear maps in `Type 0`.  The whole Ind-layer —
`RS.indOf`, the `Ind C` instances, and the realization functor
`RS.superRealize` — runs over a *small* preadditive category with
finite colimits and a biproduct-generating pair.  This file
supplies the missing bridge.

* Classification: every super vector space is isomorphic to the
  standard object `stdObj (p, q)` — `Fin p → ℂ` in even degree,
  `Fin q → ℂ` in odd degree — of its dimension pair (`isoStdObj`).

* Colimit structure: `SuperVect` has a zero object, all finite
  biproducts (componentwise products, `piBicone`), and cokernels
  (componentwise quotients, `cokerIsColimit`), hence coequalizers
  and all finite colimits.

* The small model `SmallSuperVect`: the category induced on the
  dimension pairs `ℕ × ℕ` by `stdObj`.  It is a small category
  with `Preadditive`, `Linear ℂ`, and `HasFiniteColimits`
  instances, and the inclusion `smallSuperInclusion` is an
  equivalence (`smallSuperEquiv`); in particular `SuperVect` is
  essentially small relative to `Type 0`.

* Generators: the images `sEven = (1, 0)` and `sOdd = (0, 1)` of
  the unit and the odd line biproduct-generate the small model
  (`biproductGenerates_smallSuper`): a `(p, q)`-dimensional object
  is the biproduct of `p` copies of the unit and `q` copies of the
  odd line.  This discharges the hypothesis of
  `RS.isZero_of_isZero_superRealize` at `C := SmallSuperVect`.

The small model is built as an `InducedCategory` on `ℕ × ℕ`
rather than through Mathlib's `SmallModel`: the induced
category's hom-spaces are the hom-spaces of `SuperVect` between
standard objects, wrapped in the one-field structure
`InducedCategory.Hom`, so smallness, `Preadditive`, `Linear ℂ`,
and full faithfulness of the inclusion are existing Mathlib
instances, whereas `SmallModel` (a skeleton quotient) would need
every instance conjugated across `equivSmallModel`.  Mathlib's
`EssentiallySmall`/`SmallModel`/`equivSmallModel` API, the
biproduct machinery (`Bicone`, `isBilimitOfTotal`,
`biproduct.uniqueUpToIso`, `biproduct.reindex`), and the colimit
constructions (`Preadditive.hasCoequalizers_of_hasCokernels`,
`hasFiniteColimits_of_hasCoequalizers_and_finite_coproducts`) are
all reachable through the funnel; `isBilimitOfTotal` lives in the
root `CategoryTheory.Limits` namespace, not on `Bicone`.
-/

namespace RS

noncomputable section

open CategoryTheory Limits

namespace SuperVect

/-! ### Standard objects and the classification by dimension -/

/-- The standard super vector space of a dimension pair:
`Fin p → ℂ` in even degree and `Fin q → ℂ` in odd degree.  Every
super vector space is isomorphic to exactly one standard object,
which is the entire content of the small model below. -/
def stdObj (pq : ℕ × ℕ) : SuperVect where
  even := Fin pq.1 → ℂ
  odd := Fin pq.2 → ℂ

/-- The even component of a standard object. -/
@[simp]
theorem stdObj_even (pq : ℕ × ℕ) :
    (stdObj pq).even = (Fin pq.1 → ℂ) := rfl

/-- The odd component of a standard object. -/
@[simp]
theorem stdObj_odd (pq : ℕ × ℕ) :
    (stdObj pq).odd = (Fin pq.2 → ℂ) := rfl

/-- Componentwise linear equivalences assemble to an isomorphism
of super vector spaces. -/
def isoOfEquivs {V W : SuperVect} (e : V.even ≃ₗ[ℂ] W.even)
    (o : V.odd ≃ₗ[ℂ] W.odd) : V ≅ W where
  hom := ⟨e.toLinearMap, o.toLinearMap⟩
  inv := ⟨e.symm.toLinearMap, o.symm.toLinearMap⟩
  hom_inv_id := hom_ext
    (LinearMap.ext fun x => e.symm_apply_apply x)
    (LinearMap.ext fun x => o.symm_apply_apply x)
  inv_hom_id := hom_ext
    (LinearMap.ext fun x => e.apply_symm_apply x)
    (LinearMap.ext fun x => o.apply_symm_apply x)

/-- **Classification of super vector spaces**: every object of
`SuperVect` is isomorphic to the standard object of its dimension
pair, componentwise by `LinearEquiv.ofFinrankEq`. -/
def isoStdObj (V : SuperVect) :
    V ≅ stdObj (Module.finrank ℂ V.even, Module.finrank ℂ V.odd) :=
  isoOfEquivs
    (LinearEquiv.ofFinrankEq _ _ (Module.finrank_fin_fun ℂ).symm)
    (LinearEquiv.ofFinrankEq _ _ (Module.finrank_fin_fun ℂ).symm)

/-! ### Subsingleton hom-spaces -/

/-- The even component of a purely odd standard object is
trivial. -/
instance (q : ℕ) : Subsingleton (stdObj (0, q)).even :=
  inferInstanceAs (Subsingleton (Fin 0 → ℂ))

/-- The odd component of a purely even standard object is
trivial. -/
instance (p : ℕ) : Subsingleton (stdObj (p, 0)).odd :=
  inferInstanceAs (Subsingleton (Fin 0 → ℂ))

/-- Hom-spaces whose component spaces of linear maps are
subsingletons are themselves subsingletons: this recognises the
zero object and kills the mixed-parity morphisms between the two
generator lines. -/
theorem hom_eq_of_subsingleton {V W : SuperVect}
    (he : Subsingleton (V.even →ₗ[ℂ] W.even))
    (ho : Subsingleton (V.odd →ₗ[ℂ] W.odd)) (f g : V ⟶ W) :
    f = g :=
  hom_ext (he.elim _ _) (ho.elim _ _)

/-- A subsingleton instance form of `hom_eq_of_subsingleton`. -/
instance homSubsingleton {V W : SuperVect}
    [Subsingleton (V.even →ₗ[ℂ] W.even)]
    [Subsingleton (V.odd →ₗ[ℂ] W.odd)] : Subsingleton (V ⟶ W) :=
  ⟨fun f g => hom_eq_of_subsingleton ‹_› ‹_› f g⟩

/-! ### The zero object -/

/-- The standard object of dimensions `(0, 0)` is a zero
object. -/
theorem isZero_stdObj_zero : IsZero (stdObj (0, 0)) := by
  constructor
  · exact fun Y => ⟨⟨⟨0⟩, fun f => Subsingleton.elim f 0⟩⟩
  · exact fun Y => ⟨⟨⟨0⟩, fun f => Subsingleton.elim f 0⟩⟩

/-- `SuperVect` has a zero object. -/
instance : HasZeroObject SuperVect :=
  ⟨stdObj (0, 0), isZero_stdObj_zero⟩

/-! ### Finite biproducts -/

/-- The sum of the coordinate inclusion-projection round trips on
a finite product of modules is the identity. -/
theorem sum_single_comp_proj {ι : Type} [Fintype ι] [DecidableEq ι]
    (φ : ι → Type) [∀ i, AddCommGroup (φ i)] [∀ i, Module ℂ (φ i)] :
    ∑ j, (LinearMap.single ℂ φ j ∘ₗ LinearMap.proj j) =
      (LinearMap.id : (∀ i, φ i) →ₗ[ℂ] ∀ i, φ i) := by
  refine LinearMap.ext fun x => ?_
  simp [LinearMap.sum_apply, Finset.univ_sum_single]

/-- The componentwise product of a finite family of super vector
spaces: the biproduct candidate. -/
def piObj {n : ℕ} (f : Fin n → SuperVect) : SuperVect where
  even := ∀ j, (f j).even
  odd := ∀ j, (f j).odd

/-- The componentwise bicone over a finite family: coordinate
projections and inclusions in each degree. -/
def piBicone {n : ℕ} (f : Fin n → SuperVect) : Bicone f where
  pt := piObj f
  π j := ⟨LinearMap.proj (φ := fun i => (f i).even) j,
    LinearMap.proj (φ := fun i => (f i).odd) j⟩
  ι j := ⟨LinearMap.single ℂ (fun i => (f i).even) j,
    LinearMap.single ℂ (fun i => (f i).odd) j⟩
  ι_π j j' := by
    rcases eq_or_ne j j' with rfl | hne
    · rw [dite_eq_left rfl, eqToHom_refl]
      refine hom_ext (LinearMap.ext fun x => ?_)
        (LinearMap.ext fun x => ?_)
      · change Pi.single (M := fun i => (f i).even) j x j = x
        exact Pi.single_eq_same (M := fun i => (f i).even) j x
      · change Pi.single (M := fun i => (f i).odd) j x j = x
        exact Pi.single_eq_same (M := fun i => (f i).odd) j x
    · rw [dite_eq_right hne]
      refine hom_ext (LinearMap.ext fun x => ?_)
        (LinearMap.ext fun x => ?_)
      · change Pi.single (M := fun i => (f i).even) j x j' = 0
        exact Pi.single_eq_of_ne (M := fun i => (f i).even) hne.symm x
      · change Pi.single (M := fun i => (f i).odd) j x j' = 0
        exact Pi.single_eq_of_ne (M := fun i => (f i).odd) hne.symm x

/-- Taking the even component of a morphism is additive. -/
def evenMapAddHom (V W : SuperVect) :
    (V ⟶ W) →+ (V.even →ₗ[ℂ] W.even) where
  toFun f := f.evenMap
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Taking the odd component of a morphism is additive. -/
def oddMapAddHom (V W : SuperVect) :
    (V ⟶ W) →+ (V.odd →ₗ[ℂ] W.odd) where
  toFun f := f.oddMap
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The even component of a finite sum of morphisms is the sum of
the even components. -/
theorem sum_evenMap {α : Type*} (s : Finset α) {V W : SuperVect}
    (f : α → (V ⟶ W)) :
    (∑ i ∈ s, f i).evenMap = ∑ i ∈ s, (f i).evenMap :=
  map_sum (evenMapAddHom V W) f s

/-- The odd component of a finite sum of morphisms is the sum of
the odd components. -/
theorem sum_oddMap {α : Type*} (s : Finset α) {V W : SuperVect}
    (f : α → (V ⟶ W)) :
    (∑ i ∈ s, f i).oddMap = ∑ i ∈ s, (f i).oddMap :=
  map_sum (oddMapAddHom V W) f s

/-- The componentwise bicone is a bilimit: the coordinate round
trips sum to the identity in each degree. -/
def piBiconeIsBilimit {n : ℕ} (f : Fin n → SuperVect) :
    (piBicone f).IsBilimit := by
  refine isBilimitOfTotal _ (hom_ext ?_ ?_)
  · rw [sum_evenMap]
    exact sum_single_comp_proj fun i => (f i).even
  · rw [sum_oddMap]
    exact sum_single_comp_proj fun i => (f i).odd

/-- `SuperVect` has all finite biproducts, componentwise. -/
instance : HasFiniteBiproducts SuperVect where
  out _ :=
    { has_biproduct := fun f =>
        HasBiproduct.mk ⟨piBicone f, piBiconeIsBilimit f⟩ }

/-! ### Cokernels and finite colimits -/

/-- The componentwise cokernel object of a morphism: the quotient
by the range in each degree. -/
def cokerObj {V W : SuperVect} (f : V ⟶ W) : SuperVect where
  even := W.even ⧸ LinearMap.range f.evenMap
  odd := W.odd ⧸ LinearMap.range f.oddMap

/-- The projection onto the componentwise cokernel. -/
def cokerπ {V W : SuperVect} (f : V ⟶ W) : W ⟶ cokerObj f where
  evenMap := (LinearMap.range f.evenMap).mkQ
  oddMap := (LinearMap.range f.oddMap).mkQ

/-- The cokernel projection annihilates the morphism. -/
theorem comp_cokerπ {V W : SuperVect} (f : V ⟶ W) :
    f ≫ cokerπ f = 0 :=
  hom_ext
    (LinearMap.ext fun x =>
      (Submodule.Quotient.mk_eq_zero _).mpr
        (LinearMap.mem_range_self f.evenMap x))
    (LinearMap.ext fun x =>
      (Submodule.Quotient.mk_eq_zero _).mpr
        (LinearMap.mem_range_self f.oddMap x))

/-- Descent through the componentwise cokernel: a morphism
annihilating `f` factors through the quotient in each degree. -/
def cokerDesc {V W Z : SuperVect} (f : V ⟶ W) (g : W ⟶ Z)
    (hg : f ≫ g = 0) : cokerObj f ⟶ Z where
  evenMap := (LinearMap.range f.evenMap).liftQ g.evenMap
    (LinearMap.range_le_ker_iff.mpr (congrArg Hom.evenMap hg))
  oddMap := (LinearMap.range f.oddMap).liftQ g.oddMap
    (LinearMap.range_le_ker_iff.mpr (congrArg Hom.oddMap hg))

/-- The componentwise cokernel is a categorical cokernel. -/
def cokerIsColimit {V W : SuperVect} (f : V ⟶ W) :
    IsColimit (CokernelCofork.ofπ (cokerπ f) (comp_cokerπ f)) :=
  CokernelCofork.IsColimit.ofπ _ _
    (fun g hg => cokerDesc f g hg)
    (fun _ _ => hom_ext
      (Submodule.liftQ_mkQ _ _ _)
      (Submodule.liftQ_mkQ _ _ _))
    (fun _ _ _ hm => hom_ext
      ((LinearMap.range f.evenMap).linearMap_qext
        ((congrArg Hom.evenMap hm).trans
          (Submodule.liftQ_mkQ _ _ _).symm))
      ((LinearMap.range f.oddMap).linearMap_qext
        ((congrArg Hom.oddMap hm).trans
          (Submodule.liftQ_mkQ _ _ _).symm)))

/-- `SuperVect` has all cokernels, componentwise. -/
instance : HasCokernels SuperVect where
  has_colimit f := HasColimit.mk ⟨_, cokerIsColimit f⟩

/-- `SuperVect` has coequalizers: in a preadditive category they
are cokernels of differences. -/
instance : HasCoequalizers SuperVect :=
  Preadditive.hasCoequalizers_of_hasCokernels

/-- **`SuperVect` has all finite colimits**: finite coproducts
come from the componentwise biproducts and coequalizers from the
componentwise cokernels. -/
instance : HasFiniteColimits SuperVect :=
  hasFiniteColimits_of_hasCoequalizers_and_finite_coproducts

/-! ### The generator lines -/

/-- The inclusion of the even line at coordinate `i`: the even
component places the scalar at coordinate `i`, the odd component
is zero. -/
def evenLineIn (p q : ℕ) (i : Fin p) :
    stdObj (1, 0) ⟶ stdObj (p, q) where
  evenMap := LinearMap.single ℂ (fun _ : Fin p => ℂ) i ∘ₗ
    LinearMap.proj (φ := fun _ : Fin 1 => ℂ) 0
  oddMap := 0

/-- The projection onto the even line at coordinate `i`. -/
def evenLinePrj (p q : ℕ) (i : Fin p) :
    stdObj (p, q) ⟶ stdObj (1, 0) where
  evenMap := LinearMap.single ℂ (fun _ : Fin 1 => ℂ) 0 ∘ₗ
    LinearMap.proj (φ := fun _ : Fin p => ℂ) i
  oddMap := 0

/-- The inclusion of the odd line at coordinate `j`. -/
def oddLineIn (p q : ℕ) (j : Fin q) :
    stdObj (0, 1) ⟶ stdObj (p, q) where
  evenMap := 0
  oddMap := LinearMap.single ℂ (fun _ : Fin q => ℂ) j ∘ₗ
    LinearMap.proj (φ := fun _ : Fin 1 => ℂ) 0

/-- The projection onto the odd line at coordinate `j`. -/
def oddLinePrj (p q : ℕ) (j : Fin q) :
    stdObj (p, q) ⟶ stdObj (0, 1) where
  evenMap := 0
  oddMap := LinearMap.single ℂ (fun _ : Fin 1 => ℂ) 0 ∘ₗ
    LinearMap.proj (φ := fun _ : Fin q => ℂ) j

/-- The even-line round trip through `stdObj (p, q)` at equal
coordinates is the identity. -/
theorem evenLineIn_comp_prj_same (p q : ℕ) (i : Fin p) :
    evenLineIn p q i ≫ evenLinePrj p q i = 𝟙 (stdObj (1, 0)) := by
  refine hom_ext (LinearMap.ext fun x => funext fun k => ?_)
    (Subsingleton.elim _ _)
  obtain rfl : k = 0 := Subsingleton.elim k 0
  change Pi.single (M := fun _ : Fin 1 => ℂ) 0
      (Pi.single (M := fun _ : Fin p => ℂ) i (x 0) i) 0 = x 0
  simp [Pi.single_eq_same]

/-- The even-line round trip at distinct coordinates vanishes. -/
theorem evenLineIn_comp_prj_ne (p q : ℕ) {i i' : Fin p}
    (h : i ≠ i') : evenLineIn p q i ≫ evenLinePrj p q i' = 0 := by
  refine hom_ext (LinearMap.ext fun x => funext fun k => ?_)
    (Subsingleton.elim _ _)
  change Pi.single (M := fun _ : Fin 1 => ℂ) 0
      (Pi.single (M := fun _ : Fin p => ℂ) i (x 0) i') k = 0
  rw [Pi.single_eq_of_ne (Ne.symm h), Pi.single_zero]
  rfl

/-- The odd-line round trip at equal coordinates is the
identity. -/
theorem oddLineIn_comp_prj_same (p q : ℕ) (j : Fin q) :
    oddLineIn p q j ≫ oddLinePrj p q j = 𝟙 (stdObj (0, 1)) := by
  refine hom_ext (Subsingleton.elim _ _)
    (LinearMap.ext fun x => funext fun k => ?_)
  obtain rfl : k = 0 := Subsingleton.elim k 0
  change Pi.single (M := fun _ : Fin 1 => ℂ) 0
      (Pi.single (M := fun _ : Fin q => ℂ) j (x 0) j) 0 = x 0
  simp [Pi.single_eq_same]

/-- The odd-line round trip at distinct coordinates vanishes. -/
theorem oddLineIn_comp_prj_ne (p q : ℕ) {j j' : Fin q}
    (h : j ≠ j') : oddLineIn p q j ≫ oddLinePrj p q j' = 0 := by
  refine hom_ext (Subsingleton.elim _ _)
    (LinearMap.ext fun x => funext fun k => ?_)
  change Pi.single (M := fun _ : Fin 1 => ℂ) 0
      (Pi.single (M := fun _ : Fin q => ℂ) j (x 0) j') k = 0
  rw [Pi.single_eq_of_ne (Ne.symm h), Pi.single_zero]
  rfl

/-- Mixed-parity composites vanish: even line into odd line. -/
theorem evenLineIn_comp_oddPrj (p q : ℕ) (i : Fin p) (j : Fin q) :
    evenLineIn p q i ≫ oddLinePrj p q j = 0 :=
  hom_eq_of_subsingleton inferInstance inferInstance _ _

/-- Mixed-parity composites vanish: odd line into even line. -/
theorem oddLineIn_comp_evenPrj (p q : ℕ) (i : Fin p) (j : Fin q) :
    oddLineIn p q j ≫ evenLinePrj p q i = 0 :=
  hom_eq_of_subsingleton inferInstance inferInstance _ _

/-- The even component of the even-line
projection-then-inclusion round trip through the point is the
coordinate round trip. -/
theorem evenLinePrj_comp_in_evenMap (p q : ℕ) (i : Fin p) :
    (evenLinePrj p q i ≫ evenLineIn p q i).evenMap =
      LinearMap.single ℂ (fun _ : Fin p => ℂ) i ∘ₗ
        LinearMap.proj (φ := fun _ : Fin p => ℂ) i := by
  refine LinearMap.ext fun x => funext fun k => ?_
  change Pi.single (M := fun _ : Fin p => ℂ) i
      (Pi.single (M := fun _ : Fin 1 => ℂ) 0 (x i) 0) k =
    Pi.single (M := fun _ : Fin p => ℂ) i (x i) k
  rw [Pi.single_eq_same]

/-- The odd component of the even-line round trip through the
point vanishes. -/
theorem evenLinePrj_comp_in_oddMap (p q : ℕ) (i : Fin p) :
    (evenLinePrj p q i ≫ evenLineIn p q i).oddMap = 0 :=
  LinearMap.zero_comp 0

/-- The odd component of the odd-line
projection-then-inclusion round trip through the point is the
coordinate round trip. -/
theorem oddLinePrj_comp_in_oddMap (p q : ℕ) (j : Fin q) :
    (oddLinePrj p q j ≫ oddLineIn p q j).oddMap =
      LinearMap.single ℂ (fun _ : Fin q => ℂ) j ∘ₗ
        LinearMap.proj (φ := fun _ : Fin q => ℂ) j := by
  refine LinearMap.ext fun x => funext fun k => ?_
  change Pi.single (M := fun _ : Fin q => ℂ) j
      (Pi.single (M := fun _ : Fin 1 => ℂ) 0 (x j) 0) k =
    Pi.single (M := fun _ : Fin q => ℂ) j (x j) k
  rw [Pi.single_eq_same]

/-- The even component of the odd-line round trip through the
point vanishes. -/
theorem oddLinePrj_comp_in_evenMap (p q : ℕ) (j : Fin q) :
    (oddLinePrj p q j ≫ oddLineIn p q j).evenMap = 0 :=
  LinearMap.zero_comp 0

/-- **The line decomposition of a standard object**: the sum of
all line round trips through `stdObj (p, q)` is the identity. -/
theorem lines_total (p q : ℕ) :
    (∑ i : Fin p, evenLinePrj p q i ≫ evenLineIn p q i) +
      (∑ j : Fin q, oddLinePrj p q j ≫ oddLineIn p q j) =
      𝟙 (stdObj (p, q)) := by
  refine hom_ext ?_ ?_
  · rw [add_evenMap, sum_evenMap, sum_evenMap,
      Finset.sum_congr rfl fun i _ => evenLinePrj_comp_in_evenMap p q i,
      Finset.sum_congr rfl fun j _ => oddLinePrj_comp_in_evenMap p q j,
      Finset.sum_const_zero, add_zero]
    exact sum_single_comp_proj fun _ => ℂ
  · rw [add_oddMap, sum_oddMap, sum_oddMap,
      Finset.sum_congr rfl fun i _ => evenLinePrj_comp_in_oddMap p q i,
      Finset.sum_congr rfl fun j _ => oddLinePrj_comp_in_oddMap p q j,
      Finset.sum_const_zero, zero_add]
    exact sum_single_comp_proj fun _ => ℂ

end SuperVect

/-! ## The small model -/

/-- **The small model of `SuperVect`**: the category induced on
the type `ℕ × ℕ` of dimension pairs by the standard objects.  Its
hom-spaces are the hom-spaces of `SuperVect` between standard
objects (wrapped in `InducedCategory.homMk`), so smallness,
`Preadditive`, `Linear ℂ`, and full faithfulness of the inclusion
are all Mathlib instances on `InducedCategory` — the choice of an
induced category over Mathlib's `SmallModel` (a skeleton
quotient, which would need every instance conjugated across
`equivSmallModel`) is what makes them free. -/
abbrev SmallSuperVect : Type :=
  InducedCategory SuperVect SuperVect.stdObj

/-- The inclusion of the small model into `SuperVect`, sending a
dimension pair to its standard object.  An abbreviation so that
the `InducedCategory` instances (full, faithful, additive) apply
to it directly. -/
abbrev smallSuperInclusion : SmallSuperVect ⥤ SuperVect :=
  inducedFunctor SuperVect.stdObj

/-- The inclusion of the small model is essentially surjective:
every super vector space is standard up to isomorphism. -/
instance : smallSuperInclusion.EssSurj where
  mem_essImage V :=
    ⟨(Module.finrank ℂ V.even, Module.finrank ℂ V.odd),
      ⟨(SuperVect.isoStdObj V).symm⟩⟩

/-- The inclusion of the small model is an equivalence: fully
faithful and essentially surjective. -/
instance : smallSuperInclusion.IsEquivalence := {}

/-- **The small-model equivalence**: the small model is equivalent
to `SuperVect`. -/
def smallSuperEquiv : SmallSuperVect ≌ SuperVect :=
  smallSuperInclusion.asEquivalence

/-- **`SuperVect` is essentially small** relative to `Type 0`: the
small model is a witness. -/
instance : EssentiallySmall.{0} SuperVect :=
  ⟨⟨SmallSuperVect, inferInstance, ⟨smallSuperEquiv.symm⟩⟩⟩

/-- The small model has all finite colimits, transported across
the inclusion equivalence from the componentwise colimits of
`SuperVect`. -/
instance : HasFiniteColimits SmallSuperVect :=
  ⟨fun _ _ _ =>
    Adjunction.hasColimitsOfShape_of_equivalence smallSuperInclusion⟩

/-! ## The generator pair -/

/-- The even generator of the small model: the unit line
`(1, 0)`, whose standard object is the monoidal unit of
`SuperVect` up to isomorphism (`sEvenIso`). -/
def sEven : SmallSuperVect := (1, 0)

/-- The odd generator of the small model: the odd line
`(0, 1)`. -/
def sOdd : SmallSuperVect := (0, 1)

/-- Any two subsingleton ℂ-modules are linearly equivalent by the
zero map. -/
def zeroLinearEquiv (M N : Type) [AddCommGroup M] [Module ℂ M]
    [AddCommGroup N] [Module ℂ N] [Subsingleton M]
    [Subsingleton N] : M ≃ₗ[ℂ] N where
  toFun _ := 0
  map_add' _ _ := (add_zero 0).symm
  map_smul' c _ := (smul_zero c).symm
  invFun _ := 0
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

open MonoidalCategory in
/-- The standard object of the even generator is the monoidal
unit of `SuperVect`: `Fin 1 → ℂ` is the scalar line and the odd
component is trivial. -/
def sEvenIso : smallSuperInclusion.obj sEven ≅ 𝟙_ SuperVect :=
  haveI : Subsingleton (𝟙_ SuperVect).odd :=
    inferInstanceAs (Subsingleton PUnit)
  haveI : Subsingleton (smallSuperInclusion.obj sEven).odd :=
    inferInstanceAs (Subsingleton (Fin 0 → ℂ))
  SuperVect.isoOfEquivs (LinearEquiv.funUnique (Fin 1) ℂ ℂ)
    (zeroLinearEquiv _ _)

/-! ## Biproduct generation -/

/-- The parity word of the generating decomposition of `(p, q)`:
the first `p` letters select the even generator, the last `q` the
odd one. -/
def genWord (p q : ℕ) (s : Fin p ⊕ Fin q) : Bool :=
  Sum.elim (fun _ => false) (fun _ => true) s

/-- The sum-indexed generator family underlying the generating
biproduct decomposition of `(p, q)`. -/
def genFamily (p q : ℕ) (s : Fin p ⊕ Fin q) : SmallSuperVect :=
  generatorPair sEven sOdd (genWord p q s)

/-- The underlying morphism of the zero morphism of the small
model is zero. -/
theorem smallZero_hom {X Y : SmallSuperVect} :
    (0 : X ⟶ Y).hom = 0 := by
  have h := map_zero (InducedCategory.homAddEquiv
    (C := SuperVect) (F := SuperVect.stdObj) (X := X) (Y := Y))
  simpa using h

/-- The generating bicone: `(p, q)` carries the line inclusions
and projections over the sum-indexed generator family. -/
def genBicone (p q : ℕ) : Bicone (genFamily p q) where
  pt := ((p, q) : SmallSuperVect)
  π s := match s with
    | .inl i => InducedCategory.homMk (SuperVect.evenLinePrj p q i)
    | .inr j => InducedCategory.homMk (SuperVect.oddLinePrj p q j)
  ι s := match s with
    | .inl i => InducedCategory.homMk (SuperVect.evenLineIn p q i)
    | .inr j => InducedCategory.homMk (SuperVect.oddLineIn p q j)
  ι_π s t := by
    rcases s with i | j <;> rcases t with i' | j'
    · rcases eq_or_ne i i' with rfl | hne
      · rw [dite_eq_left rfl, eqToHom_refl]
        exact InducedCategory.hom_ext
          (SuperVect.evenLineIn_comp_prj_same p q i)
      · rw [dite_eq_right fun h => hne (Sum.inl.inj h)]
        refine InducedCategory.hom_ext ?_
        rw [smallZero_hom]
        exact SuperVect.evenLineIn_comp_prj_ne p q hne
    · rw [dite_eq_right (Sum.inl_ne_inr)]
      refine InducedCategory.hom_ext ?_
      rw [smallZero_hom]
      exact SuperVect.evenLineIn_comp_oddPrj p q i j'
    · rw [dite_eq_right (Sum.inr_ne_inl)]
      refine InducedCategory.hom_ext ?_
      rw [smallZero_hom]
      exact SuperVect.oddLineIn_comp_evenPrj p q i' j
    · rcases eq_or_ne j j' with rfl | hne
      · rw [dite_eq_left rfl, eqToHom_refl]
        exact InducedCategory.hom_ext
          (SuperVect.oddLineIn_comp_prj_same p q j)
      · rw [dite_eq_right fun h => hne (Sum.inr.inj h)]
        refine InducedCategory.hom_ext ?_
        rw [smallZero_hom]
        exact SuperVect.oddLineIn_comp_prj_ne p q hne

/-- The generating bicone is a bilimit: the line round trips sum
to the identity. -/
def genBiconeIsBilimit (p q : ℕ) : (genBicone p q).IsBilimit := by
  refine isBilimitOfTotal _ (InducedCategory.hom_ext ?_)
  have hsum : (∑ s : Fin p ⊕ Fin q,
      (genBicone p q).π s ≫ (genBicone p q).ι s).hom =
      ∑ s : Fin p ⊕ Fin q,
        ((genBicone p q).π s ≫ (genBicone p q).ι s).hom :=
    map_sum (InducedCategory.homAddEquiv
      (C := SuperVect) (F := SuperVect.stdObj)) _ Finset.univ
  rw [hsum, Fintype.sum_sum_type]
  exact SuperVect.lines_total p q

attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts

/-- **Biproduct generation for the small model**: every dimension
pair is a finite biproduct of copies of the unit line and the odd
line — `(p, q)` decomposes as `p` copies of `sEven` followed by
`q` copies of `sOdd`.  This discharges the generation hypothesis
of `RS.isZero_of_isZero_superRealize` at `C := SmallSuperVect`. -/
theorem biproductGenerates_smallSuper :
    BiproductGenerates (generatorPair sEven sOdd) := by
  intro X
  obtain ⟨p, q⟩ := X
  refine ⟨p + q, fun j => genWord p q (finSumFinEquiv.symm j), ?_⟩
  have : HasBiproduct (genFamily p q) :=
    HasBiproduct.mk ⟨genBicone p q, genBiconeIsBilimit p q⟩
  exact ⟨biproduct.uniqueUpToIso (genFamily p q)
      (genBiconeIsBilimit p q) ≪≫
    (biproduct.reindex finSumFinEquiv.symm (genFamily p q)).symm⟩

end

end RS
