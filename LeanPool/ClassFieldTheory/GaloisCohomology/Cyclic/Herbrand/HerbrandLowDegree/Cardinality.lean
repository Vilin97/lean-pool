/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.TateComparison
import Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic

/-! # Cardinality -/
namespace CyclicCohomology

/-!
# Cardinality identity from the standard Tate exact sequence

For a short exact sequence of finite cyclic modules, this module applies
mathlib's homology long exact sequence to the standard two-periodic cyclic
complex.  The resulting cardinality identity is transported to the
arithmetic `H⁰` and `H⁻¹` presentations.
-/

noncomputable section

namespace ProfiniteCohomology
namespace Herbrand

open CategoryTheory

variable {G A B C : Type}

section

variable [CommGroup G] [Fintype G]
variable [CommGroup A] [CommGroup B] [CommGroup C]
variable [MulDistribMulAction G A] [MulDistribMulAction G B]
  [MulDistribMulAction G C]

private noncomputable def subCompNormMap
    (σ : G) (f : A →* B)
    (hf : ∀ (g : G) (a : A), f (g • a) = g • f a) :
    Rep.FiniteCyclicGroup.subCompNormHom
        (Rep.ofMulDistribMulAction G A) σ ⟶
      Rep.FiniteCyclicGroup.subCompNormHom
        (Rep.ofMulDistribMulAction G B) σ where
  τ₁ := (equivariantRepHom f hf).toModuleCatHom
  τ₂ := (equivariantRepHom f hf).toModuleCatHom
  τ₃ := (equivariantRepHom f hf).toModuleCatHom
  comm₁₂ := by
    ext a
    change Additive A at a
    change
      Additive.ofMul ((σ • f a.toMul) / f a.toMul) =
        Additive.ofMul (f ((σ • a.toMul) / a.toMul))
    exact congrArg Additive.ofMul (by rw [map_div, hf])
  comm₂₃ := by
    ext a
    apply Additive.ofMul.injective
    simp [Rep.FiniteCyclicGroup.subCompNormHom, Rep.norm,
      Representation.norm, Rep.hom_comm_apply]

private noncomputable def periodicChainMap
    (σ : G) (f : A →* B)
    (hf : ∀ (g : G) (a : A), f (g • a) = g • f a) :
    Rep.FiniteCyclicGroup.moduleCatChainComplex
        (Rep.ofMulDistribMulAction G A) σ ⟶
      Rep.FiniteCyclicGroup.moduleCatChainComplex
        (Rep.ofMulDistribMulAction G B) σ where
  f _ := (equivariantRepHom f hf).toModuleCatHom
  comm' := by
    rintro i j ⟨rfl⟩
    by_cases hj : Even (j + 1)
    · simp [Rep.FiniteCyclicGroup.moduleCatChainComplex,
        HomologicalComplex.alternatingConst, hj]
      exact (subCompNormMap σ f hf).comm₂₃
    · simp [Rep.FiniteCyclicGroup.moduleCatChainComplex,
        HomologicalComplex.alternatingConst, hj]
      exact (subCompNormMap σ f hf).comm₁₂

private noncomputable def periodicShortComplex
    (σ : G)
    (i : A →* B) (j : B →* C)
    (hi : ∀ (g : G) (a : A), i (g • a) = g • i a)
    (hj : ∀ (g : G) (b : B), j (g • b) = g • j b)
    (hker : ∀ b : B, j b = 1 ↔ ∃ a : A, i a = b) :
    ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
  ShortComplex.mk (periodicChainMap σ i hi) (periodicChainMap σ j hj) <| by
    apply HomologicalComplex.hom_ext
    intro n
    ext a
    change Additive.ofMul (j (i a.toMul)) = 0
    apply Additive.ofMul.injective
    exact (hker (i a.toMul)).2 ⟨a.toMul, rfl⟩

private theorem periodicShortComplex_shortExact
    (σ : G)
    (i : A →* B) (j : B →* C)
    (hi : ∀ (g : G) (a : A), i (g • a) = g • i a)
    (hj : ∀ (g : G) (b : B), j (g • b) = g • j b)
    (hker : ∀ b : B, j b = 1 ↔ ∃ a : A, i a = b)
    (hinj : Function.Injective i) (hsurj : Function.Surjective j) :
    (periodicShortComplex σ i j hi hj hker).ShortExact := by
  rw [HomologicalComplex.shortExact_iff_degreewise_shortExact]
  intro n
  refine
    { exact := ?_
      mono_f := (ModuleCat.mono_iff_injective _).2 ?_
      epi_g := (ModuleCat.epi_iff_surjective _).2 ?_ }
  · apply (ShortComplex.moduleCat_exact_iff _).2
    intro b hb
    change Additive.ofMul (j b.toMul) = 0 at hb
    have hb' : j b.toMul = 1 := Additive.ofMul.injective hb
    rcases (hker b.toMul).1 hb' with ⟨a, ha⟩
    refine ⟨Additive.ofMul a, ?_⟩
    apply Additive.toMul.injective
    exact ha
  · intro a a' ha
    apply Additive.toMul.injective
    apply hinj
    exact Additive.ofMul.injective ha
  · intro c
    rcases hsurj c.toMul with ⟨b, hb⟩
    refine ⟨Additive.ofMul b, ?_⟩
    apply Additive.toMul.injective
    exact hb

private noncomputable def periodicScIsoEven
    {R H : Type} [CommRing R] [CommGroup H] [Fintype H]
    (M : Rep R H) (τ : H)
    {n : ℕ} [h₀ : NeZero n] (hn : Even n) :
    (Rep.FiniteCyclicGroup.moduleCatChainComplex M τ).sc n ≅
      Rep.FiniteCyclicGroup.subCompNormHom M τ :=
  HomologicalComplex.alternatingConstScIsoEven
    (ModuleCat.of R M.V)
    (by ext; simp [Rep.sub_hom, Rep.applyAsHom, Rep.norm])
    (by ext; simp [Rep.sub_hom, Rep.applyAsHom, Rep.norm])
    (fun _ _ => ComplexShape.down_nat_odd_add)
    (by simp)
    (by
      induction n generalizing h₀ with
      | zero => exact (NeZero.ne 0 rfl).elim
      | succ n _ => simp)
    hn

private noncomputable def periodicScIsoOdd
    {R H : Type} [CommRing R] [CommGroup H] [Fintype H]
    (M : Rep R H) (τ : H) {n : ℕ} (hn : Odd n) :
    (Rep.FiniteCyclicGroup.moduleCatChainComplex M τ).sc n ≅
      Rep.FiniteCyclicGroup.normHomCompSub M τ :=
  HomologicalComplex.alternatingConstScIsoOdd
    (ModuleCat.of R M.V)
    (by ext; simp [Rep.sub_hom, Rep.applyAsHom, Rep.norm])
    (by ext; simp [Rep.sub_hom, Rep.applyAsHom, Rep.norm])
    (fun _ _ => ComplexShape.down_nat_odd_add)
    (by simp)
    (by rcases hn with ⟨m, rfl⟩; simp)
    hn

private noncomputable def periodicHomologyIsoEven
    {R H : Type} [CommRing R] [CommGroup H] [Fintype H]
    (M : Rep R H) (τ : H)
    {n : ℕ} [NeZero n] (hn : Even n) :
    (Rep.FiniteCyclicGroup.moduleCatChainComplex M τ).homology n ≅
      (Rep.FiniteCyclicGroup.subCompNormHom M τ).homology :=
  ShortComplex.homologyMapIso (periodicScIsoEven M τ hn)

private noncomputable def periodicHomologyIsoOdd
    {R H : Type} [CommRing R] [CommGroup H] [Fintype H]
    (M : Rep R H) (τ : H) {n : ℕ} (hn : Odd n) :
    (Rep.FiniteCyclicGroup.moduleCatChainComplex M τ).homology n ≅
      (Rep.FiniteCyclicGroup.normHomCompSub M τ).homology :=
  ShortComplex.homologyMapIso (periodicScIsoOdd M τ hn)

private noncomputable def periodicEvenHerbrandHMinusOneIso
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ)
    {n : ℕ} [NeZero n] (hn : Even n) :
    (Rep.FiniteCyclicGroup.moduleCatChainComplex
        (Rep.ofMulDistribMulAction G A) σ).homology n ≅
      ModuleCat.of ℤ (Additive (HerbrandHMinusOne G A σ)) :=
  periodicHomologyIsoEven (Rep.ofMulDistribMulAction G A) σ hn ≪≫
    (TateCohomology.isoFiniteCyclicNegOne
      (Rep.ofMulDistribMulAction G A) σ hgen).symm ≪≫
    tateHMinusOneIsoHerbrandHMinusOne σ hgen

private noncomputable def periodicOddHerbrandHZeroIso
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ)
    {n : ℕ} (hn : Odd n) :
    (Rep.FiniteCyclicGroup.moduleCatChainComplex
        (Rep.ofMulDistribMulAction G A) σ).homology n ≅
      ModuleCat.of ℤ (Additive (HerbrandH0 G A)) :=
  periodicHomologyIsoOdd (Rep.ofMulDistribMulAction G A) σ hn ≪≫
    (TateCohomology.isoFiniteCyclicZero
      (Rep.ofMulDistribMulAction G A) σ hgen).symm ≪≫
    tateH0IsoHerbrandH0

private theorem periodicScIsoEven_naturality
    (σ : G) {n : ℕ} [NeZero n] (hn : Even n)
    (f : A →* B)
    (hf : ∀ (g : G) (a : A), f (g • a) = g • f a) :
    ShortComplex.homologyMap
          (periodicScIsoEven
            (Rep.ofMulDistribMulAction G A) σ hn).inv ≫
        ShortComplex.homologyMap
          ((HomologicalComplex.shortComplexFunctor
            (ModuleCat ℤ) (ComplexShape.down ℕ) n).map
              (periodicChainMap σ f hf)) ≫
        ShortComplex.homologyMap
          (periodicScIsoEven
            (Rep.ofMulDistribMulAction G B) σ hn).hom =
      ShortComplex.homologyMap (subCompNormMap σ f hf) := by
  rw [← ShortComplex.homologyMap_comp, ← ShortComplex.homologyMap_comp]
  congr 1

private theorem periodicHomologyIsoEven_naturality
    (σ : G) {n : ℕ} [NeZero n] (hn : Even n)
    (f : A →* B)
    (hf : ∀ (g : G) (a : A), f (g • a) = g • f a) :
    (periodicHomologyIsoEven
      (Rep.ofMulDistribMulAction G A) σ hn).inv ≫
        HomologicalComplex.homologyMap (periodicChainMap σ f hf) n ≫
        (periodicHomologyIsoEven
          (Rep.ofMulDistribMulAction G B) σ hn).hom =
      ShortComplex.homologyMap (subCompNormMap σ f hf) :=
  periodicScIsoEven_naturality σ hn f hf

/-- Conjugating a `ModuleCat ℤ` morphism by isomorphisms identifies the
ranges of the associated multiplicatively tagged homomorphisms. -/
noncomputable def moduleCatRangeEquivOfConjugate
    {X Y X' Y' : ModuleCat.{0} ℤ}
    (f : X ⟶ Y) (g : X' ⟶ Y')
    (eX : X ≅ X') (eY : Y ≅ Y')
    (h : eX.inv ≫ f ≫ eY.hom = g) :
    MonoidHom.range f.hom.toAddMonoidHom.toMultiplicative ≃
      MonoidHom.range g.hom.toAddMonoidHom.toMultiplicative := by
  have hnat : f ≫ eY.hom = eX.hom ≫ g := by
    rw [← cancel_epi eX.inv]
    simpa only [Category.assoc, eX.inv_hom_id_assoc] using h
  have hinv : eX.inv ≫ f = g ≫ eY.inv := by
    rw [← cancel_mono eY.hom]
    simpa only [Category.assoc, eY.inv_hom_id, Category.comp_id] using h
  refine
    { toFun := fun y => ⟨Multiplicative.ofAdd (eY.hom y.1.toAdd), ?_⟩
      invFun := fun y => ⟨Multiplicative.ofAdd (eY.inv y.1.toAdd), ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · rcases y.2 with ⟨x, hx⟩
    refine ⟨Multiplicative.ofAdd (eX.hom x.toAdd), ?_⟩
    apply Multiplicative.toAdd.injective
    change g (eX.hom x.toAdd) = eY.hom y.1.toAdd
    have hx' : f x.toAdd = y.1.toAdd :=
      congrArg Multiplicative.toAdd hx
    rw [← hx']
    exact (congrArg (fun k : X ⟶ Y' => k x.toAdd) hnat).symm
  · rcases y.2 with ⟨x, hx⟩
    refine ⟨Multiplicative.ofAdd (eX.inv x.toAdd), ?_⟩
    apply Multiplicative.toAdd.injective
    change f (eX.inv x.toAdd) = eY.inv y.1.toAdd
    have hx' : g x.toAdd = y.1.toAdd :=
      congrArg Multiplicative.toAdd hx
    rw [← hx']
    exact congrArg (fun k : X' ⟶ Y => k x.toAdd) hinv
  · intro y
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    exact eY.hom_inv_id_apply y.1.toAdd
  · intro y
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    exact eY.inv_hom_id_apply y.1.toAdd

/-- Conjugate `ModuleCat ℤ` morphisms have ranges of the same cardinality
after multiplicatively tagging their underlying additive groups. -/
theorem moduleCatRangeCard_eq_of_conjugate
    {X Y X' Y' : ModuleCat.{0} ℤ}
    (f : X ⟶ Y) (g : X' ⟶ Y')
    (eX : X ≅ X') (eY : Y ≅ Y')
    (h : eX.inv ≫ f ≫ eY.hom = g) :
    Nat.card (MonoidHom.range
        f.hom.toAddMonoidHom.toMultiplicative) =
      Nat.card (MonoidHom.range
        g.hom.toAddMonoidHom.toMultiplicative) :=
  Nat.card_congr (moduleCatRangeEquivOfConjugate f g eX eY h)

/-- Function exactness of morphisms in `ModuleCat ℤ` gives multiplicative
exactness after tagging the underlying additive groups as multiplicative. -/
theorem mulExact_of_moduleCat_exact
    {X Y Z : ModuleCat.{0} ℤ} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hexact : Function.Exact f g) :
    Function.MulExact
      f.hom.toAddMonoidHom.toMultiplicative
      g.hom.toAddMonoidHom.toMultiplicative := by
  intro y
  constructor
  · intro hy
    change g y.toAdd = 0 at hy
    rcases (hexact y.toAdd).1 hy with ⟨x, hx⟩
    refine ⟨Multiplicative.ofAdd x, ?_⟩
    apply Multiplicative.toAdd.injective
    exact hx
  · rintro ⟨x, rfl⟩
    change g (f x.toAdd) = 0
    exact (hexact (f x.toAdd)).2 ⟨x.toAdd, rfl⟩

/-- Exactness of a short complex in `ModuleCat ℤ` gives multiplicative
exactness of its two underlying homomorphisms. -/
theorem mulExact_of_moduleCat_shortComplex_exact
    {X Y Z : ModuleCat.{0} ℤ} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hzero : f ≫ g = 0)
    (hexact : (ShortComplex.mk f g hzero).Exact) :
    Function.MulExact
      f.hom.toAddMonoidHom.toMultiplicative
      g.hom.toAddMonoidHom.toMultiplicative :=
  mulExact_of_moduleCat_exact f g
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 hexact)

/-- For an exact pair of `ModuleCat ℤ` morphisms with finite middle term,
the cardinality of the middle term is the product of the two range
cardinalities. -/
theorem moduleCat_card_eq_card_range_mul_card_range_of_exact
    {X Y Z : ModuleCat.{0} ℤ} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hexact : Function.Exact f g) [Finite Y] :
    Nat.card Y =
      Nat.card (MonoidHom.range
        f.hom.toAddMonoidHom.toMultiplicative) *
      Nat.card (MonoidHom.range
        g.hom.toAddMonoidHom.toMultiplicative) := by
  exact
    monoidHom_card_eq_card_range_mul_card_range_of_exact
      f.hom.toAddMonoidHom.toMultiplicative
      g.hom.toAddMonoidHom.toMultiplicative
      (mulExact_of_moduleCat_exact f g hexact).monoidHom_ker_eq.symm

/-- Finiteness transports from the target to the source of a
`ModuleCat ℤ` isomorphism. -/
theorem finite_source_of_moduleIso
    {X Y : ModuleCat.{0} ℤ} (e : X ≅ Y) [Finite Y] :
    Finite X := by
  let e' : X ≃ Y := ((forget (ModuleCat ℤ)).mapIso e).toEquiv
  exact Finite.of_injective e' e'.injective

/-- Finiteness transports from the source to the target of a
`ModuleCat ℤ` isomorphism. -/
theorem finite_target_of_moduleIso
    {X Y : ModuleCat.{0} ℤ} (e : X ≅ Y) [Finite X] :
    Finite Y := by
  let e' : Y ≃ X := ((forget (ModuleCat ℤ)).mapIso e.symm).toEquiv
  exact Finite.of_injective e' e'.injective

/-- A `ModuleCat ℤ` isomorphism with the additive form of a commutative
group identifies their cardinalities. -/
theorem moduleCat_card_eq_of_iso
    {X : ModuleCat.{0} ℤ} {T : Type} [CommGroup T]
    (e : X ≅ ModuleCat.of ℤ (Additive T)) :
    Nat.card X = Nat.card T :=
  Nat.card_congr ((forget (ModuleCat ℤ)).mapIso e).toEquiv

end

/-- The finite-cardinality identity supplied directly by mathlib's standard
two-periodic Tate exact sequence for a finite cyclic group. -/
theorem herbrand_exact_cardinality_identity
    [Group G] [Fintype G]
    [CommGroup A] [CommGroup B] [CommGroup C]
    [MulDistribMulAction G A] [MulDistribMulAction G B]
    [MulDistribMulAction G C]
    (i : A →* B) (j : B →* C)
    (hi : ∀ (g : G) (a : A), i (g • a) = g • i a)
    (hj : ∀ (g : G) (b : B), j (g • b) = g • j b)
    (hker : ∀ b : B, j b = 1 ↔ ∃ a : A, i a = b)
    (hinj : Function.Injective i)
    (hsurj : ∀ c : C, ∃ b : B, j b = c)
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ)
    [Finite (HerbrandH0 G A)] [Finite (HerbrandHMinusOne G A σ)]
    [Finite (HerbrandH0 G B)] [Finite (HerbrandHMinusOne G B σ)]
    [Finite (HerbrandH0 G C)] [Finite (HerbrandHMinusOne G C σ)] :
    Nat.card (HerbrandH0 G B) *
        Nat.card (HerbrandHMinusOne G A σ) *
        Nat.card (HerbrandHMinusOne G C σ) =
      Nat.card (HerbrandH0 G A) *
        Nat.card (HerbrandH0 G C) *
        Nat.card (HerbrandHMinusOne G B σ) := by
  let : IsCyclic G := ⟨⟨σ, hgen⟩⟩
  let : CommGroup G := IsCyclic.commGroup
  let S := periodicShortComplex σ i j hi hj hker
  have hS : S.ShortExact :=
    periodicShortComplex_shortExact σ i j hi hj hker hinj hsurj
  let eA4 : S.X₁.homology 4 ≅
      ModuleCat.of ℤ (Additive (HerbrandHMinusOne G A σ)) := by
    exact periodicEvenHerbrandHMinusOneIso
      (G := G) (A := A) (n := 4) σ hgen (⟨2, rfl⟩ : Even 4)
  let eB4 : S.X₂.homology 4 ≅
      ModuleCat.of ℤ (Additive (HerbrandHMinusOne G B σ)) := by
    exact periodicEvenHerbrandHMinusOneIso
      (G := G) (A := B) (n := 4) σ hgen (⟨2, rfl⟩ : Even 4)
  let eC4 : S.X₃.homology 4 ≅
      ModuleCat.of ℤ (Additive (HerbrandHMinusOne G C σ)) := by
    exact periodicEvenHerbrandHMinusOneIso
      (G := G) (A := C) (n := 4) σ hgen (⟨2, rfl⟩ : Even 4)
  let eA3 : S.X₁.homology 3 ≅
      ModuleCat.of ℤ (Additive (HerbrandH0 G A)) := by
    exact periodicOddHerbrandHZeroIso
      (G := G) (A := A) (n := 3) σ hgen (⟨1, rfl⟩ : Odd 3)
  let eB3 : S.X₂.homology 3 ≅
      ModuleCat.of ℤ (Additive (HerbrandH0 G B)) := by
    exact periodicOddHerbrandHZeroIso
      (G := G) (A := B) (n := 3) σ hgen (⟨1, rfl⟩ : Odd 3)
  let eC3 : S.X₃.homology 3 ≅
      ModuleCat.of ℤ (Additive (HerbrandH0 G C)) := by
    exact periodicOddHerbrandHZeroIso
      (G := G) (A := C) (n := 3) σ hgen (⟨1, rfl⟩ : Odd 3)
  let eA2 : S.X₁.homology 2 ≅
      ModuleCat.of ℤ (Additive (HerbrandHMinusOne G A σ)) := by
    exact periodicEvenHerbrandHMinusOneIso
      (G := G) (A := A) (n := 2) σ hgen (by simp : Even 2)
  let eB2 : S.X₂.homology 2 ≅
      ModuleCat.of ℤ (Additive (HerbrandHMinusOne G B σ)) := by
    exact periodicEvenHerbrandHMinusOneIso
      (G := G) (A := B) (n := 2) σ hgen (by simp : Even 2)
  let pA4 : S.X₁.homology 4 ≅
      (Rep.FiniteCyclicGroup.subCompNormHom
        (Rep.ofMulDistribMulAction G A) σ).homology := by
    exact periodicHomologyIsoEven
      (Rep.ofMulDistribMulAction G A) σ (⟨2, rfl⟩ : Even 4)
  let pB4 : S.X₂.homology 4 ≅
      (Rep.FiniteCyclicGroup.subCompNormHom
        (Rep.ofMulDistribMulAction G B) σ).homology := by
    exact periodicHomologyIsoEven
      (Rep.ofMulDistribMulAction G B) σ (⟨2, rfl⟩ : Even 4)
  let pA2 : S.X₁.homology 2 ≅
      (Rep.FiniteCyclicGroup.subCompNormHom
        (Rep.ofMulDistribMulAction G A) σ).homology := by
    exact periodicHomologyIsoEven
      (Rep.ofMulDistribMulAction G A) σ (by simp : Even 2)
  let pB2 : S.X₂.homology 2 ≅
      (Rep.FiniteCyclicGroup.subCompNormHom
        (Rep.ofMulDistribMulAction G B) σ).homology := by
    exact periodicHomologyIsoEven
      (Rep.ofMulDistribMulAction G B) σ (by simp : Even 2)
  let : Finite (S.X₁.homology 4) := finite_source_of_moduleIso eA4
  let : Finite (S.X₂.homology 4) := finite_source_of_moduleIso eB4
  let : Finite (S.X₃.homology 4) := finite_source_of_moduleIso eC4
  let : Finite (S.X₁.homology 3) := finite_source_of_moduleIso eA3
  let : Finite (S.X₂.homology 3) := finite_source_of_moduleIso eB3
  let : Finite (S.X₃.homology 3) := finite_source_of_moduleIso eC3
  let : Finite (S.X₁.homology 2) := finite_source_of_moduleIso eA2
  let f4 := HomologicalComplex.homologyMap S.f 4
  let g4 := HomologicalComplex.homologyMap S.g 4
  let δ43 := hS.δ 4 3 (by simp)
  let f3 := HomologicalComplex.homologyMap S.f 3
  let g3 := HomologicalComplex.homologyMap S.g 3
  let δ32 := hS.δ 3 2 (by simp)
  let f2 := HomologicalComplex.homologyMap S.f 2
  have hexactB4 : Function.Exact f4 g4 :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (hS.homology_exact₂ 4)
  have hexactC4 : Function.Exact g4 δ43 :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (hS.homology_exact₃ 4 3 (by simp))
  have hexactA3 : Function.Exact δ43 f3 :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (hS.homology_exact₁ 4 3 (by simp))
  have hexactB3 : Function.Exact f3 g3 :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (hS.homology_exact₂ 3)
  have hexactC3 : Function.Exact g3 δ32 :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (hS.homology_exact₃ 3 2 (by simp))
  have hexactA2 : Function.Exact δ32 f2 :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (hS.homology_exact₁ 3 2 (by simp))
  have hB4 :=
    moduleCat_card_eq_card_range_mul_card_range_of_exact f4 g4 hexactB4
  have hC4 :=
    moduleCat_card_eq_card_range_mul_card_range_of_exact g4 δ43 hexactC4
  have hA3 :=
    moduleCat_card_eq_card_range_mul_card_range_of_exact δ43 f3 hexactA3
  have hB3 :=
    moduleCat_card_eq_card_range_mul_card_range_of_exact f3 g3 hexactB3
  have hC3 :=
    moduleCat_card_eq_card_range_mul_card_range_of_exact g3 δ32 hexactC3
  have hA2 :=
    moduleCat_card_eq_card_range_mul_card_range_of_exact δ32 f2 hexactA2
  let q := ShortComplex.homologyMap (subCompNormMap σ i hi)
  have hf4q :
      Nat.card (MonoidHom.range
          f4.hom.toAddMonoidHom.toMultiplicative) =
        Nat.card (MonoidHom.range
          q.hom.toAddMonoidHom.toMultiplicative) := by
    apply moduleCatRangeCard_eq_of_conjugate f4 q pA4 pB4
    exact periodicHomologyIsoEven_naturality
      σ (⟨2, rfl⟩ : Even 4) i hi
  have hf2q :
      Nat.card (MonoidHom.range
          f2.hom.toAddMonoidHom.toMultiplicative) =
        Nat.card (MonoidHom.range
          q.hom.toAddMonoidHom.toMultiplicative) := by
    apply moduleCatRangeCard_eq_of_conjugate f2 q pA2 pB2
    exact periodicHomologyIsoEven_naturality σ (by simp : Even 2) i hi
  have hrange :
      Nat.card (MonoidHom.range
          f4.hom.toAddMonoidHom.toMultiplicative) =
        Nat.card (MonoidHom.range
          f2.hom.toAddMonoidHom.toMultiplicative) :=
    hf4q.trans hf2q.symm
  have hperiodic :
      Nat.card (S.X₂.homology 3) *
          Nat.card (S.X₁.homology 2) *
          Nat.card (S.X₃.homology 4) =
        Nat.card (S.X₁.homology 3) *
          Nat.card (S.X₃.homology 3) *
          Nat.card (S.X₂.homology 4) := by
    rw [hB3, hA2, hC4, hA3, hC3, hB4, ← hrange]
    ac_rfl
  have hcB4 := moduleCat_card_eq_of_iso eB4
  have hcC4 := moduleCat_card_eq_of_iso eC4
  have hcA3 := moduleCat_card_eq_of_iso eA3
  have hcB3 := moduleCat_card_eq_of_iso eB3
  have hcC3 := moduleCat_card_eq_of_iso eC3
  have hcA2 := moduleCat_card_eq_of_iso eA2
  calc
    _ = Nat.card (S.X₂.homology 3) *
          Nat.card (S.X₁.homology 2) *
          Nat.card (S.X₃.homology 4) := by
      rw [hcB3, hcA2, hcC4]
    _ = Nat.card (S.X₁.homology 3) *
          Nat.card (S.X₃.homology 3) *
          Nat.card (S.X₂.homology 4) :=
      hperiodic
    _ = _ := by
      rw [hcA3, hcC3, hcB4]

end Herbrand
end ProfiniteCohomology

end
end CyclicCohomology
