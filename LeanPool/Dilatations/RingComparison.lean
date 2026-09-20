/-
Copyright (c) 2026 Arnaud Mayeux, Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arnaud Mayeux, Jujian Zhang
-/
module

public import LeanPool.Dilatations.Centers
public import LeanPool.Dilatations.Rings
public import Mathlib.CategoryTheory.SingleObj
public import Mathlib.RingTheory.Localization.Basic

/-!
# Exponent-profile centers recover ring dilatations

From Arnaud Mayeux, *Dilatations of categories, via their Lean formalization*,
https://arxiv.org/abs/2608.09305, and `rndmx/DilCat` at commit
`604559654c948566675da3f7709b8ad3126bd487` (Apache-2.0).
The ring construction includes work by Arnaud Mayeux and Jujian Zhang from
`ProjConstruction/Proj` (Apache-2.0).
-/

@[expose] public section

noncomputable section

open CategoryTheory Finset
open CategoryTheory.Localization.Construction

universe v u v' pu pv u₁ v₁ u₂ v₂ u₃ v₃

namespace CategoryTheory.Dilatations

variable {C : Type u} [Category.{v} C]
variable (Z : Center C)
variable {D : Type u} [Category.{v'} D]
variable (F : C ⥤ D)

open Family

/-! #### Proposition 5.1 : identifying the categorical and ring-theoretic dilatations

`C := SingleObj A'` is "the category attached to `A'`" from §5.0.2 : a single object `•`, with
`Hom(•,•) = A'` and composition = multiplication (`CategoryTheory.SingleObj`, already used above
for Fact 5.2). A `Multicenter A'` (`{[Mᵢ,aᵢ]}ᵢ∈I`) corresponds exactly to a `Center (SingleObj A')`:
`aᵢ` becomes the morphism `M.elem i : star ⟶ star`, and `Mᵢ` — an ideal, hence automatically
closed under multiplication by *arbitrary* ring elements — becomes a sieve (`Sieve.ofIdeal`
below), matching the paper's own identification `ObC = {•}` (§5.0.2). -/
namespace Prop51

open CategoryTheory Multicenter Multicenter.Dilatation

variable {A' : Type u} [CommRing A']

/-- An ideal of `A'`, regarded as a sieve over the unique object of `SingleObj A'`: ideals absorb
multiplication by arbitrary ring elements, which is exactly a sieve's stability under
precomposition, since composition in `SingleObj A'` *is* ring multiplication. -/
def Sieve.ofIdeal (I : Ideal A') : Sieve (CategoryTheory.SingleObj.star A') where
  arrows {_} f := (f : A') ∈ I
  downward_closed {_ _ f} hf g := by
    change (f * g : A') ∈ I
    exact I.mul_mem_right g hf

/-- A `Multicenter A'` as a `Center (SingleObj A')`, indexed by exponent profiles `ν : M^ℕ`: the
generator at `ν` divides by `aᵢ ^ ν := M.elem ^ ν` with numerator ranging over `M.LargeIdeal ^ ν`,
matching `Dilatation.frac` exactly (needed for `Phi51` to be surjective — a single-index
generator only reaches products, not sums, of `LargeIdeal` elements). -/
def centerOfMulticenter (M : Multicenter A') :
    Center (CategoryTheory.SingleObj A') where
  I := M^ℕ
  nonempty := ⟨0⟩
  dom _ := CategoryTheory.SingleObj.star A'
  cod _ := CategoryTheory.SingleObj.star A'
  mor ν := M.elem ^ ν
  N ν := Sieve.ofIdeal (M.LargeIdeal ^ ν)

variable (M : Multicenter A')

/-- The functor `SingleObj A' ⥤ SingleObj A'[M]` induced by the canonical ring map `A' → A'[M]`
(`CategoryTheory.SingleObj.mapHom` turns any monoid hom into a functor between the attached
one-object categories). This plays the role of `Θ` on the "attached-to-a-ring" side. -/
def toDilatationFunctor : CategoryTheory.SingleObj A' ⥤ CategoryTheory.SingleObj A'[M] :=
  CategoryTheory.SingleObj.mapHom A' A'[M] (algebraMap A' A'[M]).toMonoidHom

/-- **General fact**: in the one-object category `SingleObj R` attached to a monoid `R`, a
morphism is an isomorphism iff it is a unit of `R` — composition unwinds to multiplication
(`SingleObj.comp_as_mul`), so a two-sided categorical inverse is exactly a two-sided
multiplicative inverse. -/
lemma isIso_iff_isUnit {R : Type*} [Monoid R]
    (x : CategoryTheory.SingleObj.star R ⟶ CategoryTheory.SingleObj.star R) :
    CategoryTheory.IsIso x ↔ IsUnit x := by
  constructor
  · intro h
    have := h
    refine ⟨⟨x, CategoryTheory.inv x, ?_, ?_⟩, rfl⟩
    · change x * CategoryTheory.inv x = (1 : R)
      have := CategoryTheory.IsIso.inv_hom_id x
      rwa [CategoryTheory.SingleObj.comp_as_mul, CategoryTheory.SingleObj.id_as_one] at this
    · change CategoryTheory.inv x * x = (1 : R)
      have := CategoryTheory.IsIso.hom_inv_id x
      rwa [CategoryTheory.SingleObj.comp_as_mul, CategoryTheory.SingleObj.id_as_one] at this
  · rintro ⟨u, rfl⟩
    refine ⟨⟨(↑u⁻¹ : R), ?_, ?_⟩⟩
    · change (↑u⁻¹ : R) * (↑u : R) = (1 : R)
      exact u.inv_mul
    · change (↑u : R) * (↑u⁻¹ : R) = (1 : R)
      exact u.mul_inv

/-- **General fact**: if `W.IsInvertedBy e` for some *faithful* `e`, then `W.Q` is faithful —
`e` factors as `W.Q ⋙ (lift of e)` (universal property of the localization), and a functor whose
composite with something else is faithful is itself faithful (`faithful_of_comp_faithful_gen`,
applied to the *lift*, not `e` itself : here we need the reverse composition order, so we go via
`e`'s own factorization instead). -/
lemma faithful_Q_of_isInvertedBy_of_faithful {E : Type u} [Category.{v'} E] (W : MorphismProperty E)
    {E' : Type u} [Category.{v'} E'] (e : E ⥤ E') (he : W.IsInvertedBy e) (hefaith : e.Faithful) :
    W.Q.Faithful := by
  apply faithful_of_comp_faithful_gen W.Q (Localization.Construction.lift e he)
  rw [Localization.Construction.fac]
  exact hefaith

/-- The images of `M`'s generators in `A'[M]` are non-zero-divisors — an unconditional structural
fact about dilatations (`Multicenter.Dilatation.nonzerodiv_image`, specialized to a single
generator). -/
lemma nonzerodiv_image_single (i : M.index) :
    algebraMap A' A'[M] (M.elem i) ∈ nonZeroDivisors A'[M] := by
  have h := Multicenter.Dilatation.nonzerodiv_image (M := M) (Finsupp.single i 1)
  simpa [familyPow_def] using h

/-- **Proposition 5.1, universal-property half.** `Dila (centerOfMulticenter M)` is the unique
factorization of `toDilatationFunctor M` through `CatToDila (centerOfMulticenter M)`. -/
theorem prop_5_1 :
    ∃! (Φ : Dila (centerOfMulticenter M) ⥤ CategoryTheory.SingleObj A'[M]),
      CatToDila (centerOfMulticenter M) ⋙ Φ = toDilatationFunctor M := by
  apply Dila_universal_property
  · change (ImageCenterMorphismProperty (centerOfMulticenter M) (toDilatationFunctor M)).Q.Faithful
    set Sgen : Submonoid A'[M] :=
      Submonoid.closure (Set.range (fun i => algebraMap A' A'[M] (M.elem i))) with hSgendef
    have hSgennzd : Sgen ≤ nonZeroDivisors A'[M] := by
      rw [hSgendef, Submonoid.closure_le]
      rintro x ⟨i, rfl⟩
      exact nonzerodiv_image_single M i
    let e0 : CategoryTheory.SingleObj A'[M] ⥤ CategoryTheory.SingleObj (Localization Sgen) :=
      CategoryTheory.SingleObj.mapHom _ _ (algebraMap A'[M] (Localization Sgen)).toMonoidHom
    have he0faith : e0.Faithful := by
      constructor
      intro _ _ f g h
      exact IsLocalization.injective (M := Sgen) (Localization Sgen) hSgennzd h
    have he0inv :
        (ImageCenterMorphismProperty (centerOfMulticenter M)
          (toDilatationFunctor M)).IsInvertedBy e0 := by
      rintro X Y f ⟨ν0, hi⟩
      set ν : M^ℕ := ν0 with hνdef
      have hX : X = (toDilatationFunctor M).obj ((centerOfMulticenter M).dom ν) :=
        congrArg Sigma.fst hi
      have hY : Y = (toDilatationFunctor M).obj ((centerOfMulticenter M).cod ν) :=
        congrArg (fun s => s.2.1) hi
      subst hX
      subst hY
      have hf : f = (toDilatationFunctor M).map ((centerOfMulticenter M).mor ν) := by
        cases hi; rfl
      have hmem : algebraMap A' A'[M] (M.elem ^ ν) ∈ Sgen := by
        rw [familyPow_def, Finsupp.prod, map_prod]
        refine Submonoid.prod_mem Sgen (fun i _ => ?_)
        rw [map_pow]
        refine Submonoid.pow_mem Sgen ?_ _
        rw [hSgendef]
        exact Submonoid.subset_closure ⟨i, rfl⟩
      rw [hf, isIso_iff_isUnit]
      exact IsLocalization.map_units (Localization Sgen)
        (⟨algebraMap A' A'[M] (M.elem ^ ν), hmem⟩ : Sgen)
    exact faithful_Q_of_isInvertedBy_of_faithful _ e0 he0inv he0faith
  · intro ν0
    set ν : M^ℕ := ν0 with hνdef
    rintro Y f ⟨Z, g, h, hg, rfl⟩
    obtain rfl : Y = CategoryTheory.SingleObj.star A'[M] := Subsingleton.elim _ _
    obtain rfl : Z = CategoryTheory.SingleObj.star A' := Subsingleton.elim _ _
    let h' : A'[M] := h
    let d : A'[M] :=
      @CategoryTheory.Functor.map (CategoryTheory.SingleObj A') _ (CategoryTheory.SingleObj A'[M]) _
        (toDilatationFunctor M) (CategoryTheory.SingleObj.star A')
          (CategoryTheory.SingleObj.star A')
        (M.elem ^ ν)
    have hd : d = algebraMap A' A'[M] (M.elem ^ ν) := by
      change (@CategoryTheory.Functor.map (CategoryTheory.SingleObj A') _
        (CategoryTheory.SingleObj A'[M]) _ (toDilatationFunctor M)
        (CategoryTheory.SingleObj.star A') (CategoryTheory.SingleObj.star A') (M.elem ^ ν)) = _
      simp [toDilatationFunctor, CategoryTheory.SingleObj.mapHom]
    have hgeq : @CategoryTheory.Functor.map (CategoryTheory.SingleObj A') _
        (CategoryTheory.SingleObj A'[M]) _ (toDilatationFunctor M)
        (CategoryTheory.SingleObj.star A') (CategoryTheory.SingleObj.star A') g
        = algebraMap A' A'[M] g := by
      simp [toDilatationFunctor, CategoryTheory.SingleObj.mapHom]
    have hmem : algebraMap A' A'[M] g ∈ Ideal.span {algebraMap A' A'[M] (M.elem ^ ν)} := by
      rw [Multicenter.Dilatation.image_elem_LargeIdeal_equal (M := M) ν]
      exact Ideal.mem_map_of_mem _ hg
    rw [Ideal.mem_span_singleton'] at hmem
    obtain ⟨c, hc⟩ := hmem
    refine ⟨CategoryTheory.SingleObj.star A'[M], c * h', d, Presieve.singleton_self _, ?_⟩
    rw [CategoryTheory.SingleObj.comp_as_mul, CategoryTheory.SingleObj.comp_as_mul, hd, hgeq, ← hc]
    change algebraMap A' A'[M] (M.elem ^ ν) * (c * h') = c * algebraMap A' A'[M] (M.elem ^ ν) * h'
    ring

/-- The functor `Φ` from Proposition 5.1 (the functor produced by `prop_5_1`'s existence claim),
matching the paper's own naming (cf. `Alpha315` for the analogous functor in Proposition 3.15). -/
noncomputable def Phi51 : Dila (centerOfMulticenter M) ⥤ CategoryTheory.SingleObj A'[M] :=
  (prop_5_1 M).choose

theorem Phi51_spec :
    CatToDila (centerOfMulticenter M) ⋙ Phi51 M = toDilatationFunctor M :=
  (prop_5_1 M).choose_spec.1

theorem Phi51_unique (G : Dila (centerOfMulticenter M) ⥤ CategoryTheory.SingleObj A'[M])
    (hG : CatToDila (centerOfMulticenter M) ⋙ G = toDilatationFunctor M) :
    G = Phi51 M :=
  (prop_5_1 M).choose_spec.2 G hG

/-! ##### Injectivity of `Φ`

Compare both `Φ` and the (unconditionally faithful) raw-localization comparison `DilaToLoc`
against a common target : the categorical localization `(CenterMorphismProperty
(centerOfMulticenter M)).Localization`, reached from `SingleObj A'[M]` via the *ring-theoretic*
localization of `A'` at `M`'s generators (using the monoid-level universal property of
`Localization`, since the target's endomorphism monoid need not be a ring). -/
/-- `M`'s generators, viewed as a submonoid of `A'` itself (not of `A'[M]`). -/
def genSubmonoid : Submonoid A' :=
  Submonoid.closure (Set.range M.elem)

lemma genSubmonoid_nonZeroDivisors (i : M.index) :
    algebraMap A' (Localization (genSubmonoid M)) (M.elem i) ∈
      nonZeroDivisors (Localization (genSubmonoid M)) :=
  (IsLocalization.map_units (Localization (genSubmonoid M))
    (⟨M.elem i, Submonoid.subset_closure ⟨i, rfl⟩⟩ : genSubmonoid M)).mem_nonZeroDivisors

lemma genSubmonoid_gen (i : M.index) :
    Ideal.span {algebraMap A' (Localization (genSubmonoid M)) (M.elem i)} =
      Ideal.map (algebraMap A' (Localization (genSubmonoid M))) (M.LargeIdeal i) := by
  have hunit : IsUnit (algebraMap A' (Localization (genSubmonoid M)) (M.elem i)) :=
    IsLocalization.map_units (Localization (genSubmonoid M))
      (⟨M.elem i, Submonoid.subset_closure ⟨i, rfl⟩⟩ : genSubmonoid M)
  have hspan_top : Ideal.span {algebraMap A' (Localization (genSubmonoid M)) (M.elem i)} = ⊤ :=
    Ideal.span_singleton_eq_top.mpr hunit
  have hmap_top :
      Ideal.map (algebraMap A' (Localization (genSubmonoid M))) (M.LargeIdeal i) = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ (M.elem_mem_LargeIdeal i)) hunit
  rw [hspan_top, hmap_top]

/-- The canonical map from `A'[M]` into the *full* localization of `A'` at the generators —
trivial to build via `desc`, since generators become units there. -/
noncomputable def descToLoc : A'[M] →ₐ[A'] Localization (genSubmonoid M) :=
  Multicenter.desc M (genSubmonoid_nonZeroDivisors M) (genSubmonoid_gen M)

/-- `A'`, as a monoid hom into the endomorphism monoid of the raw localization
`(CenterMorphismProperty (centerOfMulticenter M)).Localization`, matching
`LocalizationFunctor (centerOfMulticenter M)`. -/
def toLocEnd : A' →* CategoryTheory.End
    ((LocalizationFunctor (centerOfMulticenter M)).obj (CategoryTheory.SingleObj.star A')) where
  toFun a := (LocalizationFunctor (centerOfMulticenter M)).map
    (a : CategoryTheory.SingleObj.star A' ⟶ CategoryTheory.SingleObj.star A')
  map_one' := by
    change (LocalizationFunctor (centerOfMulticenter M)).map
        (𝟙 (CategoryTheory.SingleObj.star A')) =
      𝟙 ((LocalizationFunctor (centerOfMulticenter M)).obj (CategoryTheory.SingleObj.star A'))
    rw [CategoryTheory.Functor.map_id]
  map_mul' a b := by
    change (LocalizationFunctor (centerOfMulticenter M)).map
        ((a * b : A') : CategoryTheory.SingleObj.star A' ⟶ CategoryTheory.SingleObj.star A') =
      (LocalizationFunctor (centerOfMulticenter M)).map
          (b : CategoryTheory.SingleObj.star A' ⟶ CategoryTheory.SingleObj.star A') ≫
        (LocalizationFunctor (centerOfMulticenter M)).map
          (a : CategoryTheory.SingleObj.star A' ⟶ CategoryTheory.SingleObj.star A')
    rw [← CategoryTheory.SingleObj.comp_as_mul, CategoryTheory.Functor.map_comp]

lemma toLocEnd_inverts_gen : ∀ y : genSubmonoid M, IsUnit (toLocEnd M (y : A')) := by
  rintro ⟨y, hy⟩
  induction hy using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    rw [CategoryTheory.isUnit_iff_isIso]
    change CategoryTheory.IsIso (toLocEnd M (M.elem i))
    exact CategoryTheory.MorphismProperty.Q_inverts (CenterMorphismProperty (centerOfMulticenter M))
      (M.elem i : CategoryTheory.SingleObj.star A' ⟶ CategoryTheory.SingleObj.star A')
      ⟨Finsupp.single i 1, by
        have heq : M.elem i = M.elem ^ (Finsupp.single i 1) := by simp [familyPow_def]
        exact congrArg
          (fun x => (⟨CategoryTheory.SingleObj.star A', CategoryTheory.SingleObj.star A', x⟩ :
            Σ X Y : CategoryTheory.SingleObj A', X ⟶ Y)) heq⟩
  | one =>
    rw [CategoryTheory.isUnit_iff_isIso]
    change CategoryTheory.IsIso (toLocEnd M (1 : A'))
    rw [map_one, CategoryTheory.End.one_def]
    infer_instance
  | mul x y _ _ hx hy => rw [map_mul]; exact hx.mul hy

/-- General fact : if `u` commutes with `v₁` and with `v₂`, it commutes with `v₁ ≫ v₂`. -/
private lemma commutesComp {E : Type*} [CategoryTheory.Category E] {X : E} {u v₁ v₂ : X ⟶ X}
    (h₁ : u ≫ v₁ = v₁ ≫ u) (h₂ : u ≫ v₂ = v₂ ≫ u) : u ≫ (v₁ ≫ v₂) = (v₁ ≫ v₂) ≫ u := by
  rw [← CategoryTheory.Category.assoc, h₁, CategoryTheory.Category.assoc, h₂,
    ← CategoryTheory.Category.assoc]

/-- General fact : if `u` commutes with the `hom` of an iso `α : X ≅ X`, it commutes with
`α.inv` too. Stated for an explicit `Iso` (rather than `[IsIso _]`) so that it applies directly
to `Localization.Construction.wIso`, without worrying about which `IsIso` witness is in scope. -/
private lemma commutesInv {E : Type*} [CategoryTheory.Category E] {X : E} {u : X ⟶ X}
    (α : X ≅ X) (h : u ≫ α.hom = α.hom ≫ u) : u ≫ α.inv = α.inv ≫ u := by
  rw [CategoryTheory.Iso.comp_inv_eq, CategoryTheory.Category.assoc, h,
    ← CategoryTheory.Category.assoc, α.inv_hom_id, CategoryTheory.Category.id_comp]

/-- **Key structural fact**: since `A'` is commutative, every image `toLocEnd M a` is *central*
in the raw localization's endomorphism monoid — it commutes with everything. Proved via
`Localization.Construction.morphismProperty_eq_top`: a `MorphismProperty` stable under
composition, containing every generator-image and every formal inverse, is everything. -/
lemma genImage_central (a : A') :
    ∀ ⦃X Y : (CenterMorphismProperty (centerOfMulticenter M)).Localization⦄ (v : X ⟶ Y),
      (toLocEnd M a) ≫ v = v ≫ (toLocEnd M a) := by
  let P : CategoryTheory.MorphismProperty
      (CenterMorphismProperty (centerOfMulticenter M)).Localization :=
    fun _ _ v => (toLocEnd M a) ≫ v = v ≫ (toLocEnd M a)
  have : P.IsStableUnderComposition := ⟨fun _ _ hf hg => commutesComp hf hg⟩
  have hP : P = ⊤ := by
    apply Localization.Construction.morphismProperty_eq_top P
    · intro X Y f
      change toLocEnd M a ≫ toLocEnd M (f : A') = toLocEnd M (f : A') ≫ toLocEnd M a
      rw [← CategoryTheory.End.mul_def, ← CategoryTheory.End.mul_def, ← map_mul, ← map_mul,
        mul_comm]
    · intro X Y w hw
      change toLocEnd M a ≫ (Localization.Construction.wIso w hw).inv =
        (Localization.Construction.wIso w hw).inv ≫ toLocEnd M a
      apply commutesInv (Localization.Construction.wIso w hw)
      change toLocEnd M a ≫ toLocEnd M (w : A') = toLocEnd M (w : A') ≫ toLocEnd M a
      rw [← CategoryTheory.End.mul_def, ← CategoryTheory.End.mul_def, ← map_mul, ← map_mul,
        mul_comm]
  intro X Y v
  simpa only [← hP] using CategoryTheory.MorphismProperty.top_apply v

/-- The single object of the raw localization, viewed as an object of
`(CenterMorphismProperty (centerOfMulticenter M)).Localization`. -/
noncomputable abbrev localizationPoint : (CenterMorphismProperty (centerOfMulticenter
    M)).Localization :=
  (LocalizationFunctor (centerOfMulticenter M)).obj (CategoryTheory.SingleObj.star A')

/-- Every object of the raw localization is (canonically, but non-computably) equal to
    `localizationPoint`,
since the localization of a single-object category is again single-object. -/
lemma isoObj_eq_localizationPoint :
    ∀ X : (CenterMorphismProperty (centerOfMulticenter M)).Localization, X = localizationPoint
      M := by
  have : Subsingleton (CenterMorphismProperty (centerOfMulticenter M)).Localization :=
    Equiv.subsingleton.symm (CategoryTheory.Localization.Construction.objEquiv
      (CenterMorphismProperty (centerOfMulticenter M)))
  intro X
  exact Subsingleton.elim _ _

/-- Cast a morphism between arbitrary objects of the raw localization into an endomorphism of
`localizationPoint`, using that the localization has (up to equality) a single object. -/
noncomputable def castEndomorphism ⦃X Y : (CenterMorphismProperty (centerOfMulticenter
    M)).Localization⦄
    (u : X ⟶ Y) : CategoryTheory.End (localizationPoint M) :=
  CategoryTheory.eqToHom (isoObj_eq_localizationPoint M X).symm ≫ u ≫
    CategoryTheory.eqToHom (isoObj_eq_localizationPoint M Y)

private lemma castE_comp ⦃X Y Z : (CenterMorphismProperty (centerOfMulticenter M)).Localization⦄
    (f : X ⟶ Y) (g : Y ⟶ Z) : castEndomorphism M (f ≫ g) = castEndomorphism M f ≫
      castEndomorphism M g := by
  change CategoryTheory.eqToHom _ ≫ (f ≫ g) ≫ CategoryTheory.eqToHom _ =
    (CategoryTheory.eqToHom _ ≫ f ≫ CategoryTheory.eqToHom _) ≫
      (CategoryTheory.eqToHom _ ≫ g ≫ CategoryTheory.eqToHom _)
  simp only [CategoryTheory.Category.assoc, eqToHom_trans_assoc, CategoryTheory.eqToHom_refl,
    CategoryTheory.Category.id_comp]

private lemma castE_eq_self (u : CategoryTheory.End (localizationPoint M)) : castEndomorphism
    M u = u := by
  change CategoryTheory.eqToHom _ ≫ u ≫ CategoryTheory.eqToHom _ = u
  simp only [CategoryTheory.eqToHom_refl, CategoryTheory.Category.id_comp,
    CategoryTheory.Category.comp_id]

/-- **Key structural fact, part 2**: *every* endomorphism of the raw localization is central
(commutes with everything) — same argument as `genImage_central`, one level up : generator-images
are central by `genImage_central`, and formal inverses of central elements are central too. -/
lemma allCentral (v : CategoryTheory.End (localizationPoint M)) :
    ∀ ⦃X Y : (CenterMorphismProperty (centerOfMulticenter M)).Localization⦄ (u : X ⟶ Y),
      castEndomorphism M u ≫ v = v ≫ castEndomorphism M u := by
  let P : CategoryTheory.MorphismProperty
      (CenterMorphismProperty (centerOfMulticenter M)).Localization :=
    fun _ _ u => castEndomorphism M u ≫ v = v ≫ castEndomorphism M u
  have hcomp : ∀ {X Y Z} (f : X ⟶ Y) (g : Y ⟶ Z), P f → P g → P (f ≫ g) := by
    intro X Y Z f g hf hg
    change castEndomorphism M (f ≫ g) ≫ v = v ≫ castEndomorphism M (f ≫ g)
    rw [castE_comp, CategoryTheory.Category.assoc, hg, ← CategoryTheory.Category.assoc, hf,
      CategoryTheory.Category.assoc]
  have : P.IsStableUnderComposition := ⟨hcomp⟩
  have hP : P = ⊤ := by
    apply Localization.Construction.morphismProperty_eq_top P
    · intro X Y f
      change castEndomorphism M ((LocalizationFunctor (centerOfMulticenter M)).map f) ≫ v =
        v ≫ castEndomorphism M ((LocalizationFunctor (centerOfMulticenter M)).map f)
      obtain rfl : X = CategoryTheory.SingleObj.star A' := Subsingleton.elim _ _
      obtain rfl : Y = CategoryTheory.SingleObj.star A' := Subsingleton.elim _ _
      rw [castE_eq_self]
      exact genImage_central M (f : A') v
    · intro X Y w hw
      obtain rfl : X = CategoryTheory.SingleObj.star A' := Subsingleton.elim _ _
      obtain rfl : Y = CategoryTheory.SingleObj.star A' := Subsingleton.elim _ _
      change castEndomorphism M (Localization.Construction.wIso w hw).inv ≫ v =
        v ≫ castEndomorphism M (Localization.Construction.wIso w hw).inv
      erw [castE_eq_self]
      apply Eq.symm
      apply commutesInv (Localization.Construction.wIso w hw)
      change v ≫ (LocalizationFunctor (centerOfMulticenter M)).map w =
        (LocalizationFunctor (centerOfMulticenter M)).map w ≫ v
      exact (genImage_central M (w : A') v).symm
  intro X Y u
  simpa only [← hP] using CategoryTheory.MorphismProperty.top_apply u

/-- The endomorphism monoid of the raw localization's single object is commutative : this is
what makes `LocEndLift` (a monoid-localization universal-property construction) type-check. -/
noncomputable instance commEnd : CommMonoid (CategoryTheory.End (localizationPoint M)) where
  __ := CategoryTheory.End.monoid
  mul_comm u v := by
    change v ≫ u = u ≫ v
    have h := allCentral M v u
    rw [castE_eq_self] at h
    exact h.symm

/-- The universal monoid-level extension of `toLocEnd` along `A' → Localization (genSubmonoid M)`
(the generators already become units under `toLocEnd`, so the monoid-localization universal
property applies unconditionally). -/
noncomputable def LocEndLift :
    Localization (genSubmonoid M) →* CategoryTheory.End
      ((LocalizationFunctor (centerOfMulticenter M)).obj (CategoryTheory.SingleObj.star A')) :=
  (IsLocalization.toLocalizationMap (genSubmonoid M) (Localization (genSubmonoid M))).lift
    (g := toLocEnd M) (toLocEnd_inverts_gen M)

/-- The comparison map `A'[M] → (CenterMorphismProperty (centerOfMulticenter M)).Localization`,
as a monoid hom on the (single) Hom-set. -/
noncomputable def kappaHom : A'[M] →* CategoryTheory.End
    ((LocalizationFunctor (centerOfMulticenter M)).obj (CategoryTheory.SingleObj.star A')) :=
  (LocEndLift M).comp (descToLoc M).toRingHom.toMonoidHom

/-- `kappaHom` as a functor `SingleObj A'[M] ⥤ (CenterMorphismProperty
(centerOfMulticenter M)).Localization`. -/
noncomputable def kappaFunctor :
    CategoryTheory.SingleObj A'[M] ⥤
      (CenterMorphismProperty (centerOfMulticenter M)).Localization :=
  CategoryTheory.SingleObj.functor (kappaHom M)

theorem toDilatationFunctor_comp_kappaFunctor :
    toDilatationFunctor M ⋙ kappaFunctor M = LocalizationFunctor (centerOfMulticenter M) := by
  refine CategoryTheory.Functor.hext (fun _ => rfl) ?_
  intro X Y a
  refine heq_of_eq ?_
  change kappaHom M ((toDilatationFunctor M).map a) =
      (LocalizationFunctor (centerOfMulticenter M)).map a
  change kappaHom M (algebraMap A' A'[M] a) = toLocEnd M a
  change (LocEndLift M) ((descToLoc M) (algebraMap A' A'[M] a)) = toLocEnd M a
  rw [AlgHom.commutes]
  exact (IsLocalization.toLocalizationMap (genSubmonoid M)
    (Localization (genSubmonoid M))).lift_eq (toLocEnd_inverts_gen M) a

theorem Phi51_comp_kappaFunctor :
    Phi51 M ⋙ kappaFunctor M = DilaToLoc (centerOfMulticenter M) := by
  apply Dila_factor_unique (centerOfMulticenter M)
    (LocalizationFunctor (centerOfMulticenter M))
  · show CatToDila (centerOfMulticenter M) ⋙ Phi51 M ⋙ kappaFunctor M =
      LocalizationFunctor (centerOfMulticenter M)
    rw [← CategoryTheory.Functor.assoc, Phi51_spec, toDilatationFunctor_comp_kappaFunctor]
  · exact CatToDila_comp_DilaToLoc (centerOfMulticenter M)
  · exact LocalizationFunctor_isSigmaRegular (centerOfMulticenter M)

theorem Phi51_faithful : (Phi51 M).Faithful := by
  apply faithful_of_comp_faithful (Phi51 M) (kappaFunctor M)
  rw [Phi51_comp_kappaFunctor]
  exact DilaToLoc_faithful (centerOfMulticenter M)

/-! ##### Surjectivity of `Φ`

With the `ν`-indexed sieve, a *single* fraction-generator edge at profile `ν` already reaches an
*arbitrary* element of `LargeIdeal ^ ν` (the whole ideal, not just a product of simpler pieces), so
every `Dilatation.frac` fraction — hence every element of `A'[M]`, by `induction_on` — is directly
the `Φ`-image of one such generator. No path/product induction is needed at all. -/
/-- The defining fraction identity `aᵢ ^ ν · (num/aᵢ ^ ν) = num` inside `A'[M]` itself (as
    opposed to
`Multicenter.Dilatation.image_elem_LargeIdeal_equal`'s span/map statement) — the same computation,
extracted as a reusable equation. -/
lemma algebraMap_elem_pow_mul_frac (ν : M^ℕ) (num : A') (hnum : num ∈ M.LargeIdeal ^ ν) :
    algebraMap A' A'[M] (M.elem ^ ν) * frac ν ⟨num, hnum⟩ = algebraMap A' A'[M] num :=
  algebraMap_mul_fraction ν num hnum

theorem Phi51_full : (Phi51 M).Full := by
  refine ⟨fun {X Y} g => ?_⟩
  obtain ⟨X0, hX0⟩ := CatToDila_obj_surjective (centerOfMulticenter M) X
  obtain ⟨Y0, hY0⟩ := CatToDila_obj_surjective (centerOfMulticenter M) Y
  obtain rfl : X0 = CategoryTheory.SingleObj.star A' := Subsingleton.elim _ _
  obtain rfl : Y0 = CategoryTheory.SingleObj.star A' := Subsingleton.elim _ _
  subst hX0
  subst hY0
  set a : A'[M] := g with hadef
  induction a using Multicenter.Dilatation.induction_on with
  | h x =>
    obtain ⟨ν, num, hnum⟩ := x
    refine ⟨fractionInDilatation (centerOfMulticenter M)
      ⟨ν, CategoryTheory.SingleObj.star A', num, hnum⟩, ?_⟩
    have hcomp := fraction_in_dila_comp_mor (centerOfMulticenter M) ν
      (CategoryTheory.SingleObj.star A') num hnum
    have hmap := congrArg (Phi51 M).map hcomp
    rw [CategoryTheory.Functor.map_comp] at hmap
    have hspec1 : (Phi51 M).map
        ((CatToDila (centerOfMulticenter M)).map ((centerOfMulticenter M).mor ν)) =
        algebraMap A' A'[M] (M.elem ^ ν) := by
      have h := CategoryTheory.Functor.congr_hom (Phi51_spec M) ((centerOfMulticenter M).mor ν)
      simpa [toDilatationFunctor, CategoryTheory.SingleObj.mapHom,
        CategoryTheory.Functor.comp_map, centerOfMulticenter] using! h
    set numMor : CategoryTheory.SingleObj.star A' ⟶ CategoryTheory.SingleObj.star A' :=
      num with hnumMor
    have hspec2 : (Phi51 M).map ((CatToDila (centerOfMulticenter M)).map numMor) =
        algebraMap A' A'[M] num := by
      have h := CategoryTheory.Functor.congr_hom (Phi51_spec M) numMor
      simpa [toDilatationFunctor, CategoryTheory.SingleObj.mapHom,
        CategoryTheory.Functor.comp_map, centerOfMulticenter] using! h
    rw [hspec1, hspec2] at hmap
    rw [← CategoryTheory.End.mul_def] at hmap
    have hnzd : algebraMap A' A'[M] (M.elem ^ ν) ∈ nonZeroDivisors A'[M] :=
      Multicenter.Dilatation.nonzerodiv_image (M := M) ν
    exact (mul_cancel_left_mem_nonZeroDivisors hnzd).mp
      (hmap.trans (algebraMap_elem_pow_mul_frac M ν num hnum).symm)

/-! ##### Packaging `Φ` into an isomorphism of categories

`Phi51` is full and faithful, and both `Dila (centerOfMulticenter M)` and `SingleObj A'[M]` have a
single object, so `Φ` restricts to a bijection on the (unique) Hom-set — a `MonoidHom` inverse to
`Phi51.map` builds the inverse functor `Psi51` directly, mirroring `Iso315` in Proposition 3.15. -/
/-- `Φ`, restricted to the single Hom-set, as a bijection (using that `Phi51` is full and
faithful). -/
noncomputable def Phi51Equiv :
    CategoryTheory.End
      ((CatToDila (centerOfMulticenter M)).obj (CategoryTheory.SingleObj.star A')) ≃ A'[M] := by
  haveI := Phi51_faithful M
  haveI := Phi51_full M
  exact Equiv.ofBijective (Phi51 M).map
    ⟨fun _ _ h => (Phi51 M).map_injective h, fun a => (Phi51 M).map_surjective a⟩

lemma Phi51Equiv_apply (x : CategoryTheory.End
    ((CatToDila (centerOfMulticenter M)).obj (CategoryTheory.SingleObj.star A'))) :
    Phi51Equiv M x = (Phi51 M).map x := rfl

lemma Phi51Equiv_one : Phi51Equiv M 1 = 1 := by
  change (Phi51 M).map (1 : CategoryTheory.End _) = (1 : A'[M])
  rw [CategoryTheory.End.one_def, CategoryTheory.Functor.map_id,
    CategoryTheory.SingleObj.id_as_one]

lemma Phi51Equiv_mul (x y : CategoryTheory.End
    ((CatToDila (centerOfMulticenter M)).obj (CategoryTheory.SingleObj.star A'))) :
    Phi51Equiv M (x * y) = Phi51Equiv M x * Phi51Equiv M y := by
  simp only [Phi51Equiv_apply]
  rw [CategoryTheory.End.mul_def, CategoryTheory.Functor.map_comp, CategoryTheory.End.mul_def]

/-- The inverse of `Phi51Equiv`, as a `MonoidHom` — the data needed to build `Psi51`. -/
noncomputable def psi51Hom : A'[M] →* CategoryTheory.End
    ((CatToDila (centerOfMulticenter M)).obj (CategoryTheory.SingleObj.star A')) where
  toFun := (Phi51Equiv M).symm
  map_one' := by rw [← Phi51Equiv_one, Equiv.symm_apply_apply]
  map_mul' x y := by
    apply (Phi51Equiv M).injective
    rw [Phi51Equiv_mul, Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- The inverse functor to `Phi51`. -/
noncomputable def Psi51 : CategoryTheory.SingleObj A'[M] ⥤ Dila (centerOfMulticenter M) :=
  CategoryTheory.SingleObj.functor (psi51Hom M)

/-- `Dila (centerOfMulticenter M)` has a single object, since `C = SingleObj A'` does
(`CatToDila_obj_surjective` and `Subsingleton.elim` on `C`). -/
instance dila51_subsingleton : Subsingleton (Dila (centerOfMulticenter M)) := by
  constructor
  intro X Y
  obtain ⟨X0, hX0⟩ := CatToDila_obj_surjective (centerOfMulticenter M) X
  obtain ⟨Y0, hY0⟩ := CatToDila_obj_surjective (centerOfMulticenter M) Y
  obtain rfl : X0 = CategoryTheory.SingleObj.star A' := Subsingleton.elim _ _
  obtain rfl : Y0 = CategoryTheory.SingleObj.star A' := Subsingleton.elim _ _
  rw [← hX0, ← hY0]

theorem Phi51_comp_Psi51 : Phi51 M ⋙ Psi51 M = 𝟭 (Dila (centerOfMulticenter M)) := by
  refine CategoryTheory.Functor.hext (fun _ => Subsingleton.elim _ _) ?_
  intro X Y f
  refine heq_of_eq ?_
  obtain ⟨X0, hX0⟩ := CatToDila_obj_surjective (centerOfMulticenter M) X
  obtain ⟨Y0, hY0⟩ := CatToDila_obj_surjective (centerOfMulticenter M) Y
  obtain rfl : X0 = CategoryTheory.SingleObj.star A' := Subsingleton.elim _ _
  obtain rfl : Y0 = CategoryTheory.SingleObj.star A' := Subsingleton.elim _ _
  subst hX0
  subst hY0
  change (Psi51 M).map ((Phi51 M).map f) = f
  change psi51Hom M (Phi51Equiv M f) = f
  change (Phi51Equiv M).symm (Phi51Equiv M f) = f
  rw [Equiv.symm_apply_apply]

theorem Psi51_comp_Phi51 : Psi51 M ⋙ Phi51 M = 𝟭 (CategoryTheory.SingleObj A'[M]) := by
  refine CategoryTheory.Functor.hext (fun _ => Subsingleton.elim _ _) ?_
  intro X Y g
  refine heq_of_eq ?_
  obtain rfl : X = CategoryTheory.SingleObj.star A'[M] := Subsingleton.elim _ _
  obtain rfl : Y = CategoryTheory.SingleObj.star A'[M] := Subsingleton.elim _ _
  change (Phi51 M).map ((Psi51 M).map g) = g
  change Phi51Equiv M (psi51Hom M g) = g
  change Phi51Equiv M ((Phi51Equiv M).symm g) = g
  rw [Equiv.apply_symm_apply]

/-- **Proposition 5.1, full statement.** `Φ` assembles `Phi51`/`Psi51` into an isomorphism of
categories `Dila (centerOfMulticenter M) ≅ SingleObj A'[M]`, matching the paper's "provides the
desired identification." -/
noncomputable def Iso51 :
    Cat.of (Dila (centerOfMulticenter M)) ≅ Cat.of (CategoryTheory.SingleObj A'[M]) where
  hom := (Phi51 M).toCatHom
  inv := (Psi51 M).toCatHom
  hom_inv_id := Cat.ext (Phi51_comp_Psi51 M)
  inv_hom_id := Cat.ext (Psi51_comp_Phi51 M)

end Prop51

end CategoryTheory.Dilatations
