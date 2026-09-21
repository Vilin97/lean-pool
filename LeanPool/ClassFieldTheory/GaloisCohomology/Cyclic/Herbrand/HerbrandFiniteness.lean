/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Core
import LeanPool.ClassFieldTheory.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.TateComparison
import Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic
import Mathlib.RepresentationTheory.Homological.GroupHomology.FiniteCyclic

/-! # Herbrand Finiteness -/
namespace CyclicCohomology

/-!
# Finiteness in the Herbrand exact hexagon

This file supplies the finiteness clause in Herbrand-quotient multiplicativity:
for a short exact sequence of modules over a finite cyclic group, if the Herbrand
quotients of any two terms are defined, then the quotient of the third term is
defined as well.
-/

noncomputable section

namespace ProfiniteCohomology
namespace Herbrand

open CategoryTheory

universe uG uA

variable {G A B C : Type}
variable [Group G] [Fintype G] [CommGroup A] [CommGroup B] [CommGroup C]
variable [MulDistribMulAction G A] [MulDistribMulAction G B]
  [MulDistribMulAction G C]

/-- The condition that the Herbrand quotient of `A` is defined. -/
def HerbrandQuotientDefined (G : Type uG) (A : Type uA)
    [Group G] [Fintype G] [CommGroup A] [MulDistribMulAction G A]
    (σ : G) : Prop :=
  Finite (HerbrandH0 G A) ∧ Finite (HerbrandHMinusOne G A σ)

/-- In an exact pair `X → Y → Z`, finiteness of `X` and `Z` forces
finiteness of `Y`. -/
private theorem finite_middle_of_exact
    {X Y Z : Type}
    [Group X] [Group Y] [Group Z]
    (f : X →* Y) (g : Y →* Z) (hexact : MonoidHom.range f = MonoidHom.ker g)
    [Finite X] [Finite Z] :
    Finite Y := by
  apply g.finite_iff_finite_ker_range.mpr
  constructor
  · let : Finite (MonoidHom.range f) :=
      Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
    rw [← hexact]
    infer_instance
  · infer_instance

private theorem finite_middle_of_moduleCat_exact
    {X Y Z : ModuleCat.{0} ℤ} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hexact : Function.Exact f g)
    [Finite X] [Finite Z] :
    Finite Y := by
  let fm : Multiplicative X →* Multiplicative Y :=
    f.hom.toAddMonoidHom.toMultiplicative
  let gm : Multiplicative Y →* Multiplicative Z :=
    g.hom.toAddMonoidHom.toMultiplicative
  exact finite_middle_of_exact
    (X := Multiplicative X) (Y := Multiplicative Y)
    (Z := Multiplicative Z) fm gm
    (mulExact_of_moduleCat_exact f g hexact).monoidHom_ker_eq.symm

private noncomputable def tateHOneIsoHerbrandHMinusOne
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) :
    tateCohomology (Rep.ofMulDistribMulAction G A) 1 ≅
      ModuleCat.of ℤ (Additive (HerbrandHMinusOne G A σ)) := by
  letI : IsCyclic G := ⟨⟨σ, hgen⟩⟩
  letI : CommGroup G := IsCyclic.commGroup
  let M := Rep.ofMulDistribMulAction G A
  exact
    (TateCohomology.isoGroupCohomology 1).app M ≪≫
      Rep.FiniteCyclicGroup.groupCohomologyIsoOdd
        M σ hgen 1 (by simp) ≪≫
      (TateCohomology.isoFiniteCyclicNegOne M σ hgen).symm ≪≫
      tateHMinusOneIsoHerbrandHMinusOne σ hgen

private noncomputable def tateHMinusTwoIsoHerbrandH0
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) :
    tateCohomology (Rep.ofMulDistribMulAction G A) (-2) ≅
      ModuleCat.of ℤ (Additive (HerbrandH0 G A)) := by
  classical
  letI : IsCyclic G := ⟨⟨σ, hgen⟩⟩
  letI : CommGroup G := IsCyclic.commGroup
  let M := Rep.ofMulDistribMulAction G A
  exact
    (TateCohomology.isoGroupHomology (-2) 1 (by norm_num)).app M ≪≫
      Rep.FiniteCyclicGroup.groupHomologyIsoOdd
        M σ hgen 1 (by simp) ≪≫
      (TateCohomology.isoFiniteCyclicZero M σ hgen).symm ≪≫
      tateH0IsoHerbrandH0

/-- Herbrand-quotient multiplicativity, finiteness transfer from the first and third terms to
the middle term. -/
theorem herbrandQuotientDefined_middle_of_left_right
    (i : A →* B) (j : B →* C)
    (hi : ∀ (g : G) (a : A), i (g • a) = g • i a)
    (hj : ∀ (g : G) (b : B), j (g • b) = g • j b)
    (hker : ∀ b : B, j b = 1 ↔ ∃ a : A, i a = b)
    (hinj : Function.Injective i)
    (hsurj : ∀ c : C, ∃ b : B, j b = c)
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ)
    (hA : HerbrandQuotientDefined G A σ)
    (hC : HerbrandQuotientDefined G C σ) :
    HerbrandQuotientDefined G B σ := by
  let : Finite (HerbrandH0 G A) := hA.1
  let : Finite (HerbrandHMinusOne G A σ) := hA.2
  let : Finite (HerbrandH0 G C) := hC.1
  let : Finite (HerbrandHMinusOne G C σ) := hC.2
  let S := equivariantShortComplex i j hi hj hker
  have hS : S.ShortExact :=
    equivariantShortComplex_shortExact
      i j hi hj hker hinj hsurj
  let : Finite (tateCohomology S.X₁ (-1)) :=
    finite_source_of_moduleIso
      (tateHMinusOneIsoHerbrandHMinusOne
        (G := G) (A := A) σ hgen)
  let : Finite (tateCohomology S.X₃ (-1)) :=
    finite_source_of_moduleIso
      (tateHMinusOneIsoHerbrandHMinusOne
        (G := G) (A := C) σ hgen)
  have hminusTate : Finite (tateCohomology S.X₂ (-1)) :=
    finite_middle_of_moduleCat_exact
      ((tateCohomologyFunctor (-1)).map S.f)
      ((tateCohomologyFunctor (-1)).map S.g)
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
        ((TateCohomology.map_tateComplexFunctor_shortExact hS)
          |>.homology_exact₂ (-1)))
  have hminus : Finite (HerbrandHMinusOne G B σ) := by
    let :
        Finite
          (tateCohomology
            (Rep.ofMulDistribMulAction G B) (-1)) := by
      change Finite (tateCohomology S.X₂ (-1))
      exact hminusTate
    exact finite_target_of_moduleIso
      (tateHMinusOneIsoHerbrandHMinusOne
        (G := G) (A := B) σ hgen)
  let : Finite (tateCohomology S.X₁ 0) :=
    finite_source_of_moduleIso
      (tateH0IsoHerbrandH0 (G := G) (A := A))
  let : Finite (tateCohomology S.X₃ 0) :=
    finite_source_of_moduleIso
      (tateH0IsoHerbrandH0 (G := G) (A := C))
  have hzeroTate : Finite (tateCohomology S.X₂ 0) :=
    finite_middle_of_moduleCat_exact
      ((tateCohomologyFunctor 0).map S.f)
      ((tateCohomologyFunctor 0).map S.g)
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
        ((TateCohomology.map_tateComplexFunctor_shortExact hS)
          |>.homology_exact₂ 0))
  have hzero : Finite (HerbrandH0 G B) := by
    let :
        Finite
          (tateCohomology
            (Rep.ofMulDistribMulAction G B) 0) := by
      change Finite (tateCohomology S.X₂ 0)
      exact hzeroTate
    exact finite_target_of_moduleIso
      (tateH0IsoHerbrandH0 (G := G) (A := B))
  exact ⟨hzero, hminus⟩

/-- Herbrand-quotient multiplicativity, finiteness transfer from the first and middle terms to
the third term. -/
theorem herbrandQuotientDefined_right_of_left_middle
    (i : A →* B) (j : B →* C)
    (hi : ∀ (g : G) (a : A), i (g • a) = g • i a)
    (hj : ∀ (g : G) (b : B), j (g • b) = g • j b)
    (hker : ∀ b : B, j b = 1 ↔ ∃ a : A, i a = b)
    (hinj : Function.Injective i)
    (hsurj : ∀ c : C, ∃ b : B, j b = c)
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ)
    (hA : HerbrandQuotientDefined G A σ)
    (hB : HerbrandQuotientDefined G B σ) :
    HerbrandQuotientDefined G C σ := by
  let : Finite (HerbrandH0 G A) := hA.1
  let : Finite (HerbrandHMinusOne G A σ) := hA.2
  let : Finite (HerbrandH0 G B) := hB.1
  let : Finite (HerbrandHMinusOne G B σ) := hB.2
  let S := equivariantShortComplex i j hi hj hker
  have hS : S.ShortExact :=
    equivariantShortComplex_shortExact
      i j hi hj hker hinj hsurj
  let : Finite (tateCohomology S.X₂ (-1)) :=
    finite_source_of_moduleIso
      (tateHMinusOneIsoHerbrandHMinusOne
        (G := G) (A := B) σ hgen)
  have hA0 : Finite (tateCohomology S.X₁ 0) :=
    finite_source_of_moduleIso
      (tateH0IsoHerbrandH0 (G := G) (A := A))
  let : Finite (tateCohomology S.X₁ ((-1) + 1)) := by
    norm_num
    exact hA0
  have hminusTate : Finite (tateCohomology S.X₃ (-1)) :=
    finite_middle_of_moduleCat_exact
      ((tateCohomologyFunctor (-1)).map S.g)
      (TateCohomology.δ hS (-1))
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
        (TateCohomology.exact₃ hS (-1)))
  have hminus : Finite (HerbrandHMinusOne G C σ) := by
    let :
        Finite
          (tateCohomology
            (Rep.ofMulDistribMulAction G C) (-1)) := by
      change Finite (tateCohomology S.X₃ (-1))
      exact hminusTate
    exact finite_target_of_moduleIso
      (tateHMinusOneIsoHerbrandHMinusOne
        (G := G) (A := C) σ hgen)
  let : Finite (tateCohomology S.X₂ 0) :=
    finite_source_of_moduleIso
      (tateH0IsoHerbrandH0 (G := G) (A := B))
  have hA1 : Finite (tateCohomology S.X₁ 1) :=
    finite_source_of_moduleIso
      (tateHOneIsoHerbrandHMinusOne
        (G := G) (A := A) σ hgen)
  let : Finite (tateCohomology S.X₁ (0 + 1)) := by
    norm_num
    exact hA1
  have hzeroTate : Finite (tateCohomology S.X₃ 0) :=
    finite_middle_of_moduleCat_exact
      ((tateCohomologyFunctor 0).map S.g)
      (TateCohomology.δ hS 0)
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
        (TateCohomology.exact₃ hS 0))
  have hzero : Finite (HerbrandH0 G C) := by
    let :
        Finite
          (tateCohomology
            (Rep.ofMulDistribMulAction G C) 0) := by
      change Finite (tateCohomology S.X₃ 0)
      exact hzeroTate
    exact finite_target_of_moduleIso
      (tateH0IsoHerbrandH0 (G := G) (A := C))
  exact ⟨hzero, hminus⟩

/-- Herbrand-quotient multiplicativity, finiteness transfer from the middle and third terms to
the first term. -/
theorem herbrandQuotientDefined_left_of_middle_right
    (i : A →* B) (j : B →* C)
    (hi : ∀ (g : G) (a : A), i (g • a) = g • i a)
    (hj : ∀ (g : G) (b : B), j (g • b) = g • j b)
    (hker : ∀ b : B, j b = 1 ↔ ∃ a : A, i a = b)
    (hinj : Function.Injective i)
    (hsurj : ∀ c : C, ∃ b : B, j b = c)
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ)
    (hB : HerbrandQuotientDefined G B σ)
    (hC : HerbrandQuotientDefined G C σ) :
    HerbrandQuotientDefined G A σ := by
  let : Finite (HerbrandH0 G B) := hB.1
  let : Finite (HerbrandHMinusOne G B σ) := hB.2
  let : Finite (HerbrandH0 G C) := hC.1
  let : Finite (HerbrandHMinusOne G C σ) := hC.2
  let S := equivariantShortComplex i j hi hj hker
  have hS : S.ShortExact :=
    equivariantShortComplex_shortExact
      i j hi hj hker hinj hsurj
  let : Finite (tateCohomology S.X₃ (-2)) :=
    finite_source_of_moduleIso
      (tateHMinusTwoIsoHerbrandH0
        (G := G) (A := C) σ hgen)
  have hBminus : Finite (tateCohomology S.X₂ (-1)) :=
    finite_source_of_moduleIso
      (tateHMinusOneIsoHerbrandHMinusOne
        (G := G) (A := B) σ hgen)
  let : Finite ((tateCohomologyFunctor ((-2) + 1)).obj S.X₂) := by
    norm_num
    exact hBminus
  have hminusTate :
      Finite (tateCohomology S.X₁ ((-2) + 1)) :=
    finite_middle_of_moduleCat_exact
      (TateCohomology.δ hS (-2))
      ((tateCohomologyFunctor ((-2) + 1)).map S.f)
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
        (TateCohomology.exact₁ hS (-2)))
  have hminus : Finite (HerbrandHMinusOne G A σ) := by
    let :
        Finite
          (tateCohomology
            (Rep.ofMulDistribMulAction G A) (-1)) := by
      norm_num at hminusTate ⊢
      exact hminusTate
    exact finite_target_of_moduleIso
      (tateHMinusOneIsoHerbrandHMinusOne
        (G := G) (A := A) σ hgen)
  let : Finite (tateCohomology S.X₃ (-1)) :=
    finite_source_of_moduleIso
      (tateHMinusOneIsoHerbrandHMinusOne
        (G := G) (A := C) σ hgen)
  let : Finite (tateCohomology S.X₂ 0) :=
    finite_source_of_moduleIso
      (tateH0IsoHerbrandH0 (G := G) (A := B))
  have hzeroTate : Finite (tateCohomology S.X₁ 0) :=
    finite_middle_of_moduleCat_exact
      (TateCohomology.δ hS (-1))
      ((tateCohomologyFunctor 0).map S.f)
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
        (TateCohomology.exact₁ hS (-1)))
  have hzero : Finite (HerbrandH0 G A) := by
    let :
        Finite
          (tateCohomology
            (Rep.ofMulDistribMulAction G A) 0) := by
      change Finite (tateCohomology S.X₁ 0)
      exact hzeroTate
    exact finite_target_of_moduleIso
      (tateH0IsoHerbrandH0 (G := G) (A := A))
  exact ⟨hzero, hminus⟩

/-- Herbrand-quotient multiplicativity, the complete "any two imply the third" finiteness
statement for a short exact sequence. -/
theorem herbrandQuotientDefined_anyTwo
    (i : A →* B) (j : B →* C)
    (hi : ∀ (g : G) (a : A), i (g • a) = g • i a)
    (hj : ∀ (g : G) (b : B), j (g • b) = g • j b)
    (hker : ∀ b : B, j b = 1 ↔ ∃ a : A, i a = b)
    (hinj : Function.Injective i)
    (hsurj : ∀ c : C, ∃ b : B, j b = c)
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) :
    (HerbrandQuotientDefined G A σ ∧ HerbrandQuotientDefined G B σ →
        HerbrandQuotientDefined G C σ) ∧
      (HerbrandQuotientDefined G A σ ∧ HerbrandQuotientDefined G C σ →
        HerbrandQuotientDefined G B σ) ∧
      (HerbrandQuotientDefined G B σ ∧ HerbrandQuotientDefined G C σ →
        HerbrandQuotientDefined G A σ) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨hA, hB⟩
    exact herbrandQuotientDefined_right_of_left_middle
      i j hi hj hker hinj hsurj σ hgen hA hB
  · rintro ⟨hA, hC⟩
    exact herbrandQuotientDefined_middle_of_left_right
      i j hi hj hker hinj hsurj σ hgen hA hC
  · rintro ⟨hB, hC⟩
    exact herbrandQuotientDefined_left_of_middle_right
      i j hi hj hker hinj hsurj σ hgen hB hC

/-- Herbrand-quotient multiplicativity, Herbrand-quotient multiplicativity once the three
quotients are defined. -/
theorem herbrandQuotient_multiplicative_of_shortExact
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
    herbrandQuotient (G := G) (A := B) σ =
      herbrandQuotient (G := G) (A := A) σ *
        herbrandQuotient (G := G) (A := C) σ :=
  herbrandQuotient_exact_multiplicative
    i j hi hj hker hinj hsurj σ hgen

/-- Herbrand-quotient multiplicativity in its first two-defined form: if the quotients of `A`
and `C` are defined, the quotient of `B` is defined and multiplicativity
holds for that induced finiteness witness. -/
theorem herbrandQuotient_multiplicative_of_left_right_defined
    (i : A →* B) (j : B →* C)
    (hi : ∀ (g : G) (a : A), i (g • a) = g • i a)
    (hj : ∀ (g : G) (b : B), j (g • b) = g • j b)
    (hker : ∀ b : B, j b = 1 ↔ ∃ a : A, i a = b)
    (hinj : Function.Injective i)
    (hsurj : ∀ c : C, ∃ b : B, j b = c)
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ)
    [Finite (HerbrandH0 G A)] [Finite (HerbrandHMinusOne G A σ)]
    [Finite (HerbrandH0 G C)] [Finite (HerbrandHMinusOne G C σ)] :
    ∃ hB : HerbrandQuotientDefined G B σ,
      @herbrandQuotient G B _ _ _ _ σ hB.1 hB.2 =
        herbrandQuotient (G := G) (A := A) σ *
          herbrandQuotient (G := G) (A := C) σ := by
  let hA : HerbrandQuotientDefined G A σ := ⟨inferInstance, inferInstance⟩
  let hC : HerbrandQuotientDefined G C σ := ⟨inferInstance, inferInstance⟩
  let hB := herbrandQuotientDefined_middle_of_left_right
    i j hi hj hker hinj hsurj σ hgen hA hC
  refine ⟨hB, ?_⟩
  let : Finite (HerbrandH0 G B) := hB.1
  let : Finite (HerbrandHMinusOne G B σ) := hB.2
  exact herbrandQuotient_multiplicative_of_shortExact
    i j hi hj hker hinj hsurj σ hgen

/-- Herbrand-quotient multiplicativity in its second two-defined form: if the quotients of `A`
and `B` are defined, the quotient of `C` is defined and multiplicativity
holds for that induced finiteness witness. -/
theorem herbrandQuotient_multiplicative_of_left_middle_defined
    (i : A →* B) (j : B →* C)
    (hi : ∀ (g : G) (a : A), i (g • a) = g • i a)
    (hj : ∀ (g : G) (b : B), j (g • b) = g • j b)
    (hker : ∀ b : B, j b = 1 ↔ ∃ a : A, i a = b)
    (hinj : Function.Injective i)
    (hsurj : ∀ c : C, ∃ b : B, j b = c)
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ)
    [Finite (HerbrandH0 G A)] [Finite (HerbrandHMinusOne G A σ)]
    [Finite (HerbrandH0 G B)] [Finite (HerbrandHMinusOne G B σ)] :
    ∃ hC : HerbrandQuotientDefined G C σ,
      herbrandQuotient (G := G) (A := B) σ =
        herbrandQuotient (G := G) (A := A) σ *
          @herbrandQuotient G C _ _ _ _ σ hC.1 hC.2 := by
  let hA : HerbrandQuotientDefined G A σ := ⟨inferInstance, inferInstance⟩
  let hB : HerbrandQuotientDefined G B σ := ⟨inferInstance, inferInstance⟩
  let hC := herbrandQuotientDefined_right_of_left_middle
    i j hi hj hker hinj hsurj σ hgen hA hB
  refine ⟨hC, ?_⟩
  let : Finite (HerbrandH0 G C) := hC.1
  let : Finite (HerbrandHMinusOne G C σ) := hC.2
  exact herbrandQuotient_multiplicative_of_shortExact
    i j hi hj hker hinj hsurj σ hgen

/-- Herbrand-quotient multiplicativity in its third two-defined form: if the quotients of `B`
and `C` are defined, the quotient of `A` is defined and multiplicativity
holds for that induced finiteness witness. -/
theorem herbrandQuotient_multiplicative_of_middle_right_defined
    (i : A →* B) (j : B →* C)
    (hi : ∀ (g : G) (a : A), i (g • a) = g • i a)
    (hj : ∀ (g : G) (b : B), j (g • b) = g • j b)
    (hker : ∀ b : B, j b = 1 ↔ ∃ a : A, i a = b)
    (hinj : Function.Injective i)
    (hsurj : ∀ c : C, ∃ b : B, j b = c)
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ)
    [Finite (HerbrandH0 G B)] [Finite (HerbrandHMinusOne G B σ)]
    [Finite (HerbrandH0 G C)] [Finite (HerbrandHMinusOne G C σ)] :
    ∃ hA : HerbrandQuotientDefined G A σ,
      herbrandQuotient (G := G) (A := B) σ =
        @herbrandQuotient G A _ _ _ _ σ hA.1 hA.2 *
          herbrandQuotient (G := G) (A := C) σ := by
  let hB : HerbrandQuotientDefined G B σ := ⟨inferInstance, inferInstance⟩
  let hC : HerbrandQuotientDefined G C σ := ⟨inferInstance, inferInstance⟩
  let hA := herbrandQuotientDefined_left_of_middle_right
    i j hi hj hker hinj hsurj σ hgen hB hC
  refine ⟨hA, ?_⟩
  let : Finite (HerbrandH0 G A) := hA.1
  let : Finite (HerbrandHMinusOne G A σ) := hA.2
  exact herbrandQuotient_multiplicative_of_shortExact
    i j hi hj hker hinj hsurj σ hgen

/-- Herbrand-quotient multiplicativity, the finite-module case. -/
theorem herbrandQuotient_eq_one_of_finite_module
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) [Finite A] :
    herbrandQuotient (G := G) (A := A) σ = 1 :=
  herbrandQuotient_finite_module_eq_one σ hgen

end Herbrand
end ProfiniteCohomology

end
end CyclicCohomology
