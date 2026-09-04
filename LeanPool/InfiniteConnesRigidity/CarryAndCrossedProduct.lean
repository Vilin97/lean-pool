/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

module

public import Mathlib.Algebra.Group.MinimalAxioms
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.Data.Finsupp.Encodable
public import Mathlib.Data.Finsupp.Pointwise
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.LinearAlgebra.Countable
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.Localization.Algebra
public import Mathlib.Topology.Algebra.PontryaginDual
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import Mathlib.Topology.Instances.ZMod
public import Mathlib.Topology.Metrizable.Urysohn
public import LeanPool.InfiniteConnesRigidity.UniversalLattice

/-!
# Carry groups, duality, and crossed products
-/

noncomputable section

namespace ConnesRigidity
section

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem integerElementaryGeneration : IntegerElementaryGeneration := by
  change IntegerElementaryProof.elementary = ⊤
  exact IntegerElementaryProof.elementary_eq_top

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem suslinElementaryGeneration_iff_relative :
    SuslinElementaryGeneration ↔ SuslinRelativeElementaryGeneration := by
  rw [suslinElementaryGeneration_iff_base_and_relative]
  exact and_iff_right integerElementaryGeneration

end

section

open Polynomial
open scoped BigOperators

universe u

variable {A : Type u} [CommRing A]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def suslinAwayToLocalization (M : Submonoid A) (d : M) :
    Localization.Away (d : A) →+* Localization M :=
  IsLocalization.Away.lift (d : A)
    (IsLocalization.map_units (Localization M) d)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem suslinAwayToLocalization_algebraMap
    (M : Submonoid A) (d : M) (a : A) :
    suslinAwayToLocalization M d
        (algebraMap A (Localization.Away (d : A)) a) =
      algebraMap A (Localization M) a :=
  IsLocalization.Away.lift_eq (d : A) _ a

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def suslinAwayToProduct (M : Submonoid A) (d e : M) :
    Localization.Away (d : A) →+*
      Localization.Away ((d * e : M) : A) :=
  IsLocalization.Away.awayToAwayRight
    (S := Localization.Away (d : A))
    (P := Localization.Away ((d * e : M) : A))
    (d : A) (e : A)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem suslinAwayToProduct_algebraMap
    (M : Submonoid A) (d e : M) (a : A) :
    suslinAwayToProduct M d e
        (algebraMap A (Localization.Away (d : A)) a) =
      algebraMap A (Localization.Away ((d * e : M) : A)) a :=
  IsLocalization.Away.awayToAwayRight_eq (d : A) (e : A) a

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem suslin_exists_away_eq_of_localization_eq
    (M : Submonoid A) (d : M)
    (x y : Localization.Away (d : A))
    (hxy : suslinAwayToLocalization M d x =
      suslinAwayToLocalization M d y) :
    ∃ e : M, suslinAwayToProduct M d e x =
      suslinAwayToProduct M d e y := by
  obtain ⟨a, s, hs⟩ :=
    IsLocalization.exists_mk'_eq (Submonoid.powers (d : A)) (x - y)
  have hzero : suslinAwayToLocalization M d (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hspec := IsLocalization.mk'_spec
    (Localization.Away (d : A)) a s
  rw [hs] at hspec
  have hspecmap := congrArg (suslinAwayToLocalization M d) hspec
  simp only [map_mul, suslinAwayToLocalization_algebraMap] at hspecmap
  have ha : algebraMap A (Localization M) a = 0 := by
    rw [← hspecmap, hzero, zero_mul]
  obtain ⟨e, he⟩ :=
    (IsLocalization.map_eq_zero_iff M (Localization M) a).mp ha
  refine ⟨e, ?_⟩
  let T := Localization.Away ((d * e : M) : A)
  let f := suslinAwayToProduct M d e
  have heunit : IsUnit (algebraMap A T (e : A)) := by
    apply IsLocalization.Away.isUnit_of_dvd ((d * e : M) : A)
    refine ⟨(d : A), ?_⟩
    exact mul_comm _ _
  have ha' : algebraMap A T a = 0 := by
    apply heunit.mul_left_cancel
    rw [mul_zero, ← map_mul, he, map_zero]
  have hmap_s : f (algebraMap A (Localization.Away (d : A))
      (s : A)) = algebraMap A T (s : A) :=
    suslinAwayToProduct_algebraMap M d e (s : A)
  have hmap_a : f (algebraMap A (Localization.Away (d : A)) a) =
      algebraMap A T a :=
    suslinAwayToProduct_algebraMap M d e a
  have hsunit : IsUnit (algebraMap A T (s : A)) := by
    rw [← hmap_s]
    exact (IsLocalization.map_units (Localization.Away (d : A)) s).map f
  have hspec' := congrArg f hspec
  simp only [map_mul] at hspec'
  rw [hmap_s, hmap_a, ha'] at hspec'
  have hz : f (x - y) = 0 := by
    apply hsunit.mul_right_cancel
    simpa only [Submonoid.coe_mul, map_sub, zero_mul] using hspec'
  exact sub_eq_zero.mp (by simpa only [map_sub] using hz)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def suslinAwayMapOfDvd {r s : A} (hrs : r ∣ s) :
    Localization.Away r →+* Localization.Away s :=
  IsLocalization.Away.lift r
    (IsLocalization.Away.isUnit_of_dvd s hrs)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem suslinAwayMapOfDvd_algebraMap
    {r s : A} (hrs : r ∣ s) (a : A) :
    suslinAwayMapOfDvd hrs
        (algebraMap A (Localization.Away r) a) =
      algebraMap A (Localization.Away s) a :=
  IsLocalization.Away.lift_eq r _ a

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem suslinAwayMapOfDvd_comp_product
    (M : Submonoid A) (d e E : M)
    (hden : ((d * e : M) : A) ∣ ((d * E : M) : A)) :
    (suslinAwayMapOfDvd hden).comp
        (suslinAwayToProduct M d e) =
      suslinAwayToProduct M d E := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (d : A))
  ext a
  simp only [RingHom.comp_apply]
  rw [suslinAwayToProduct_algebraMap,
    suslinAwayMapOfDvd_algebraMap,
    suslinAwayToProduct_algebraMap]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem suslin_exists_away_finite_eq_of_localization_eq
    (M : Submonoid A) (d : M)
    {ι : Type*} [Finite ι]
    (x y : ι → Localization.Away (d : A))
    (hxy : ∀ i, suslinAwayToLocalization M d (x i) =
      suslinAwayToLocalization M d (y i)) :
    ∃ e : M, ∀ i, suslinAwayToProduct M d e (x i) =
      suslinAwayToProduct M d e (y i) := by
  classical
  let := Fintype.ofFinite ι
  choose e he using fun i =>
    suslin_exists_away_eq_of_localization_eq M d (x i) (y i) (hxy i)
  let E : M := ∏ i, e i
  refine ⟨E, ?_⟩
  intro i
  have hei : e i ∣ E := by
    dsimp [E]
    exact Finset.dvd_prod_of_mem e (Finset.mem_univ i)
  obtain ⟨c, hc⟩ := hei
  have hdiv : ((d * e i : M) : A) ∣ ((d * E : M) : A) := by
    refine ⟨(c : A), ?_⟩
    change ((d * E : M) : A) = (((d * e i) * c : M) : A)
    congr 1
    rw [hc, mul_assoc]
  have hcomp := suslinAwayMapOfDvd_comp_product M d (e i) E hdiv
  have hi := congrArg (suslinAwayMapOfDvd hdiv) (he i)
  change ((suslinAwayMapOfDvd hdiv).comp
      (suslinAwayToProduct M d (e i))) (x i) =
    ((suslinAwayMapOfDvd hdiv).comp
      (suslinAwayToProduct M d (e i))) (y i) at hi
  rw [hcomp] at hi
  exact hi

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem suslin_exists_away_specialLinear_eq_of_localization_eq
    (M : Submonoid A) (d : M)
    (x y : Matrix.SpecialLinearGroup Index
      (Polynomial (Localization.Away (d : A))))
    (hxy : Matrix.SpecialLinearGroup.map
        (Polynomial.mapRingHom (suslinAwayToLocalization M d)) x =
      Matrix.SpecialLinearGroup.map
        (Polynomial.mapRingHom (suslinAwayToLocalization M d)) y) :
    ∃ e : M,
      Matrix.SpecialLinearGroup.map
          (Polynomial.mapRingHom (suslinAwayToProduct M d e)) x =
        Matrix.SpecialLinearGroup.map
          (Polynomial.mapRingHom (suslinAwayToProduct M d e)) y := by
  classical
  let ι : Type := Σ ij : Index × Index,
    {n : ℕ // n ∈ (x.1 ij.1 ij.2).support ∪
      (y.1 ij.1 ij.2).support}
  let a : ι → Localization.Away (d : A) :=
    fun k => (x.1 k.1.1 k.1.2).coeff (k.2 : ℕ)
  let b : ι → Localization.Away (d : A) :=
    fun k => (y.1 k.1.1 k.1.2).coeff (k.2 : ℕ)
  have hab : ∀ k : ι,
      suslinAwayToLocalization M d (a k) =
        suslinAwayToLocalization M d (b k) := by
    intro k
    have hk := congrArg
      (fun z : Matrix.SpecialLinearGroup Index (Polynomial (Localization M)) =>
        (z.1 k.1.1 k.1.2).coeff (k.2 : ℕ)) hxy
    change
      (Polynomial.map (suslinAwayToLocalization M d)
          (x.1 k.1.1 k.1.2)).coeff (k.2 : ℕ) =
        (Polynomial.map (suslinAwayToLocalization M d)
          (y.1 k.1.1 k.1.2)).coeff (k.2 : ℕ) at hk
    simpa only [Polynomial.coeff_map, a, b] using hk
  obtain ⟨e, he⟩ :=
    suslin_exists_away_finite_eq_of_localization_eq M d a b hab
  refine ⟨e, ?_⟩
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  apply Polynomial.ext
  intro n
  change
    (Polynomial.map (suslinAwayToProduct M d e) (x.1 i j)).coeff n =
      (Polynomial.map (suslinAwayToProduct M d e) (y.1 i j)).coeff n
  simp only [Polynomial.coeff_map]
  by_cases hn : n ∈ (x.1 i j).support ∪ (y.1 i j).support
  · simpa only [a, b] using
      (he (⟨(i, j), ⟨n, hn⟩⟩ : ι))
  · have hnx : n ∉ (x.1 i j).support :=
      fun hx => hn (Finset.mem_union_left _ hx)
    have hny : n ∉ (y.1 i j).support :=
      fun hy => hn (Finset.mem_union_right _ hy)
    simp only [Submonoid.coe_mul, Polynomial.notMem_support_iff.mp hnx, map_zero,
      Polynomial.notMem_support_iff.mp hny]

end

section

open Polynomial
open scoped BigOperators

universe u

variable {A : Type u} [CommRing A]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem suslin_exists_away_elementary_of_atPrime
    (m : Ideal A) [m.IsPrime]
    (g : Matrix.SpecialLinearGroup Index (Polynomial A))
    (hg : Matrix.SpecialLinearGroup.map
      (Polynomial.mapRingHom (algebraMap A (Localization.AtPrime m))) g ∈
      localGlobalElementarySubgroup (Polynomial (Localization.AtPrime m))) :
    ∃ d : m.primeCompl, suslinAwayElementary g (d : A) := by
  let gp : Matrix.SpecialLinearGroup Index
      (Polynomial (Localization.AtPrime m)) :=
    Matrix.SpecialLinearGroup.map
      (Polynomial.mapRingHom (algebraMap A (Localization.AtPrime m))) g
  obtain ⟨d, q, hq, hqmap⟩ :=
    suslin_exists_away_elementary_word_lift_atPrime m gp hg
  let gd : Matrix.SpecialLinearGroup Index
      (Polynomial (Localization.Away (d : A))) :=
    Matrix.SpecialLinearGroup.map
      (Polynomial.mapRingHom
        (algebraMap A (Localization.Away (d : A)))) g
  have heq :
      Matrix.SpecialLinearGroup.map
          (Polynomial.mapRingHom
            (suslinAwayToLocalization m.primeCompl d)) q =
        Matrix.SpecialLinearGroup.map
          (Polynomial.mapRingHom
            (suslinAwayToLocalization m.primeCompl d)) gd := by
    change
      Matrix.SpecialLinearGroup.map
          (Polynomial.mapRingHom (suslinAwayToAtPrime m d)) q =
        Matrix.SpecialLinearGroup.map
          (Polynomial.mapRingHom (suslinAwayToAtPrime m d)) gd
    rw [hqmap]
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    change Polynomial.map (algebraMap A (Localization.AtPrime m)) (g.1 i j) =
      Polynomial.map (suslinAwayToAtPrime m d)
        (Polynomial.map
          (algebraMap A (Localization.Away (d : A))) (g.1 i j))
    apply Polynomial.ext
    intro n
    simp only [coeff_map, suslinAwayToAtPrime_algebraMap]
  obtain ⟨e, heq'⟩ :=
    suslin_exists_away_specialLinear_eq_of_localization_eq
      m.primeCompl d q gd heq
  refine ⟨d * e, ?_⟩
  change
    Matrix.SpecialLinearGroup.map
        (Polynomial.mapRingHom
          (algebraMap A
            (Localization.Away ((d * e : m.primeCompl) : A)))) g ∈
      localGlobalElementarySubgroup
        (Polynomial (Localization.Away ((d * e : m.primeCompl) : A)))
  have hgd :
      Matrix.SpecialLinearGroup.map
          (Polynomial.mapRingHom
            (suslinAwayToProduct m.primeCompl d e)) gd =
        Matrix.SpecialLinearGroup.map
          (Polynomial.mapRingHom
            (algebraMap A
              (Localization.Away ((d * e : m.primeCompl) : A)))) g := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    change
      Polynomial.map (suslinAwayToProduct m.primeCompl d e)
          (Polynomial.map
            (algebraMap A (Localization.Away (d : A))) (g.1 i j)) =
        Polynomial.map
          (algebraMap A
            (Localization.Away ((d * e : m.primeCompl) : A))) (g.1 i j)
    apply Polynomial.ext
    intro n
    simp only [Polynomial.coeff_map]
    exact suslinAwayToProduct_algebraMap
      m.primeCompl d e ((g.1 i j).coeff n)
  rw [← hgd, ← heq']
  exact map_localGlobalElementarySubgroup_le
    (Polynomial.mapRingHom (suslinAwayToProduct m.primeCompl d e))
    ⟨q, hq, rfl⟩

end

section

open scoped BigOperators

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem exists_powered_partition_of_unity
    {A : Type*} [CommRing A]
    {ι : Type*} [Fintype ι] (s : ι → A)
    (hcover : Ideal.span (Set.range s) = ⊤) (N : ℕ) :
    ∃ c : ι → A, ∑ i, c i * s i ^ N = 1 := by
  have hpow : Ideal.span (Set.range fun i => s i ^ N) = ⊤ := by
    have hrange : ((fun x : A => x ^ N) '' Set.range s) =
        Set.range (fun i => s i ^ N) := by
      ext y
      constructor
      · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨s i, ⟨i, rfl⟩, rfl⟩
    rw [← hrange]
    exact Ideal.span_pow_eq_top (Set.range s) hcover N
  exact (Ideal.mem_span_range_iff_exists_fun).mp
    ((Ideal.eq_top_iff_one _).mp hpow)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def suslinPoweredPrefix
    {A : Type*} [CommRing A]
    (s c : ℕ → A) (N j : ℕ) : A :=
  ∑ i ∈ Finset.range j, c i * s i ^ N

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem suslinPoweredPrefix_zero
    {A : Type*} [CommRing A] (s c : ℕ → A) (N : ℕ) :
    suslinPoweredPrefix s c N 0 = 0 := by
  simp only [suslinPoweredPrefix, Finset.range_zero, Finset.sum_empty]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem suslinPoweredPrefix_succ
    {A : Type*} [CommRing A] (s c : ℕ → A) (N j : ℕ) :
    suslinPoweredPrefix s c N (j + 1) =
      suslinPoweredPrefix s c N j + c j * s j ^ N := by
  simp only [suslinPoweredPrefix, Finset.sum_range_succ]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem suslin_reverse_telescope
    {G : Type*} [Group G] (f : ℕ → G) (n : ℕ) :
    (((List.range n).map fun j => f (j + 1) * (f j)⁻¹).reverse).prod =
      f n * (f 0)⁻¹ := by
  induction n with
  | zero => simp only [List.range_zero, List.map_nil, List.reverse_nil, List.prod_nil,
              mul_inv_cancel]
  | succ n ih =>
      simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil, List.reverse_append,
        List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.prod_cons, ih,
        mul_assoc, inv_mul_cancel_left]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem subgroup_mem_of_powered_partition_patches
    {A : Type*} [CommRing A]
    {G : Type*} [Group G] (H : Subgroup G)
    (α : A → G) (hzero : α 0 = 1)
    (s c : ℕ → A) (n N : ℕ)
    (hpartition : ∑ i ∈ Finset.range n, c i * s i ^ N = 1)
    (hpatch : ∀ j < n,
      α (suslinPoweredPrefix s c N j + c j * s j ^ N) *
        (α (suslinPoweredPrefix s c N j))⁻¹ ∈ H) :
    α 1 ∈ H := by
  let f : ℕ → G := fun j => α (suslinPoweredPrefix s c N j)
  have htel := suslin_reverse_telescope f n
  have hend : suslinPoweredPrefix s c N n = 1 := hpartition
  have hprod :
      (((List.range n).map fun j => f (j + 1) * (f j)⁻¹).reverse).prod ∈ H := by
    apply H.list_prod_mem
    intro x hx
    rw [List.mem_reverse, List.mem_map] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    have hjn : j < n := List.mem_range.mp hj
    simpa [f, suslinPoweredPrefix_succ] using hpatch j hjn
  dsimp [f] at htel
  rw [hend, suslinPoweredPrefix_zero, hzero, inv_one, mul_one] at htel
  rw [← htel]
  exact hprod

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def suslinPolynomialDilationRingHom (a : ℤ) :
    IntegralPolynomial →+* IntegralPolynomial :=
  Polynomial.eval₂RingHom (Polynomial.C : ℤ →+* IntegralPolynomial)
    (Polynomial.C a * Polynomial.X)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def suslinPolynomialDilate (a : ℤ) :
    IntegralSpecialLinearGroup →* IntegralSpecialLinearGroup :=
  Matrix.SpecialLinearGroup.map (suslinPolynomialDilationRingHom a)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem suslinPolynomialDilate_entry
    (a : ℤ) (g : IntegralSpecialLinearGroup) (i j : Index) :
    suslinPolynomialDilate a g i j =
      (g i j).eval₂ Polynomial.C (Polynomial.C a * Polynomial.X) := rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem suslinPolynomialDilate_one
    (g : IntegralSpecialLinearGroup) :
    suslinPolynomialDilate 1 g = g := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  simp only [suslinPolynomialDilate_entry, eq_intCast, Int.cast_one, one_mul, Polynomial.eval₂_C_X]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem suslinPolynomialDilate_zero
    (g : IntegralSpecialLinearGroup) :
    suslinPolynomialDilate 0 g =
      suslinConstantSection (suslinEvaluation g) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  simp only [suslinPolynomialDilate_entry, eq_intCast, Int.cast_zero, zero_mul,
    Polynomial.eval₂_at_zero, Polynomial.coeff_zero_eq_eval_zero, suslinConstantSection,
    suslinEvaluation, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
    Polynomial.coe_evalRingHom, Matrix.map_apply]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem suslinPolynomialDilate_zero_of_mem_augmentation
    {g : IntegralSpecialLinearGroup} (hg : g ∈ suslinAugmentationKernel) :
    suslinPolynomialDilate 0 g = 1 := by
  rw [suslinPolynomialDilate_zero]
  rw [show suslinEvaluation g = 1 from hg]
  exact map_one _

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem suslin_augmentation_mem_elementary_of_powered_patches
    (g : IntegralSpecialLinearGroup)
    (hg : g ∈ suslinAugmentationKernel)
    (s c : ℕ → ℤ) (n N : ℕ)
    (hpartition : ∑ i ∈ Finset.range n, c i * s i ^ N = 1)
    (hpatch : ∀ j < n,
      suslinPolynomialDilate
          (suslinPoweredPrefix s c N j + c j * s j ^ N) g *
        (suslinPolynomialDilate (suslinPoweredPrefix s c N j) g)⁻¹ ∈
          integralElementarySubgroup) :
    g ∈ integralElementarySubgroup := by
  have h := subgroup_mem_of_powered_partition_patches
    integralElementarySubgroup
    (fun a : ℤ => suslinPolynomialDilate a g)
    (suslinPolynomialDilate_zero_of_mem_augmentation hg)
    s c n N hpartition hpatch
  simpa only [suslinPolynomialDilate_one] using h

end

section

open scoped commutatorElement

variable {R : Type*} [CommRing R]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private abbrev SL (R : Type*) [CommRing R] :=
  Matrix.SpecialLinearGroup (Fin 4) R

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def relativeRootSubgroup (I : Ideal R) : Subgroup (SL R) :=
  Subgroup.closure
    {g | ∃ (i j : Fin 4) (h : i ≠ j) (b : R),
      b ∈ I ∧ g = Matrix.SpecialLinearGroup.transvection h b}

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def relativeZSubgroup (I : Ideal R) : Subgroup (SL R) :=
  Subgroup.closure
    {g | ∃ (i j : Fin 4) (h : i ≠ j) (a b : R), b ∈ I ∧
      g = Matrix.SpecialLinearGroup.transvection h.symm a *
        Matrix.SpecialLinearGroup.transvection h b *
        (Matrix.SpecialLinearGroup.transvection h.symm a)⁻¹}

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem relativeZ_mem (I : Ideal R) (i j : Fin 4) (h : i ≠ j)
    (a b : R) (hb : b ∈ I) :
    Matrix.SpecialLinearGroup.transvection h.symm a *
        Matrix.SpecialLinearGroup.transvection h b *
        (Matrix.SpecialLinearGroup.transvection h.symm a)⁻¹ ∈
      relativeZSubgroup I :=
  Subgroup.subset_closure ⟨i, j, h, a, b, hb, rfl⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem relativeRoot_mem_Z (I : Ideal R) (i j : Fin 4) (h : i ≠ j)
    (b : R) (hb : b ∈ I) :
    Matrix.SpecialLinearGroup.transvection h b ∈ relativeZSubgroup I := by
  simpa only [Matrix.SpecialLinearGroup.transvection_coeff_zero, one_mul, inv_one,
    mul_one] using relativeZ_mem I i j h 0 b hb

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem relativeRoot_mem_F (I : Ideal R) (i j : Fin 4) (h : i ≠ j)
    (b : R) (hb : b ∈ I) :
    Matrix.SpecialLinearGroup.transvection h b ∈ relativeRootSubgroup I :=
  Subgroup.subset_closure ⟨i, j, h, b, hb, rfl⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem conjugate_relative_root_mem_Z
    (I : Ideal R) (k l i j : Fin 4)
    (hkl : k ≠ l) (hij : i ≠ j)
    (a b : R) (hb : b ∈ I) :
    Matrix.SpecialLinearGroup.transvection hkl a *
        Matrix.SpecialLinearGroup.transvection hij b *
        (Matrix.SpecialLinearGroup.transvection hkl a)⁻¹ ∈
      relativeZSubgroup I := by
  by_cases hli : l = i
  · subst l
    by_cases hkj : k = j
    · subst k
      exact relativeZ_mem I i j hij a b hb
    · rw [suslin_transvection_conj_adjacent k i j hkl hij hkj a b]
      exact (relativeZSubgroup I).mul_mem
        (relativeRoot_mem_Z I k j hkj (a * b) (I.mul_mem_left a hb))
        (relativeRoot_mem_Z I i j hij b hb)
  · by_cases hjk : j = k
    · subst k
      rw [suslin_transvection_conj_reverse_adjacent j l i hkl hli hij.symm a b]
      exact (relativeZSubgroup I).mul_mem
        (relativeRoot_mem_Z I i l (Ne.symm hli) (-(b * a))
          (I.neg_mem (I.mul_mem_right a hb)))
        (relativeRoot_mem_Z I i j hij b hb)
    · rw [suslin_transvection_conj_noncomposable hkl hij hli hjk a b]
      exact relativeRoot_mem_Z I i j hij b hb

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem conjugate_relative_root_mem_F_of_not_opposite
    (I : Ideal R) (k l i j : Fin 4)
    (hkl : k ≠ l) (hij : i ≠ j)
    (a b : R) (hb : b ∈ I)
    (hnot : ¬ (k = j ∧ l = i)) :
    Matrix.SpecialLinearGroup.transvection hkl a *
        Matrix.SpecialLinearGroup.transvection hij b *
        (Matrix.SpecialLinearGroup.transvection hkl a)⁻¹ ∈
      relativeRootSubgroup I := by
  by_cases hli : l = i
  · subst l
    have hkj : k ≠ j := fun h => hnot ⟨h, rfl⟩
    rw [suslin_transvection_conj_adjacent k i j hkl hij hkj a b]
    exact (relativeRootSubgroup I).mul_mem
      (relativeRoot_mem_F I k j hkj (a * b) (I.mul_mem_left a hb))
      (relativeRoot_mem_F I i j hij b hb)
  · by_cases hjk : j = k
    · subst k
      rw [suslin_transvection_conj_reverse_adjacent j l i hkl hli hij.symm a b]
      exact (relativeRootSubgroup I).mul_mem
        (relativeRoot_mem_F I i l (Ne.symm hli) (-(b * a))
          (I.neg_mem (I.mul_mem_right a hb)))
        (relativeRoot_mem_F I i j hij b hb)
    · rw [suslin_transvection_conj_noncomposable hkl hij hli hjk a b]
      exact relativeRoot_mem_F I i j hij b hb

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem conjugate_relative_F_mem_Z
    (I : Ideal R) (k l : Fin 4) (hkl : k ≠ l) (a : R)
    {g : SL R} (hg : g ∈ relativeRootSubgroup I) :
    Matrix.SpecialLinearGroup.transvection hkl a * g *
        (Matrix.SpecialLinearGroup.transvection hkl a)⁻¹ ∈
      relativeZSubgroup I := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨i, j, hij, b, hb, rfl⟩ := hx
      exact conjugate_relative_root_mem_Z I k l i j hkl hij a b hb
  | one =>
      simp only [mul_one, mul_inv_cancel, one_mem]
  | mul x y hx hy ihx ihy =>
      have h := (relativeZSubgroup I).mul_mem ihx ihy
      simpa only [mul_assoc, inv_mul_cancel_left] using h
  | inv x hx ih =>
      have h := (relativeZSubgroup I).inv_mem ih
      simpa only [mul_assoc, mul_inv_rev, inv_inv] using h

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem conjugate_Z_generator_of_commute_outer
    (I : Ideal R) (k l i j : Fin 4)
    (hkl : k ≠ l) (hij : i ≠ j)
    (c a b : R) (hb : b ∈ I)
    (hlj : l ≠ j) (hik : i ≠ k)
    (hnot : ¬ (k = j ∧ l = i)) :
    Matrix.SpecialLinearGroup.transvection hkl c *
      (Matrix.SpecialLinearGroup.transvection hij.symm a *
        Matrix.SpecialLinearGroup.transvection hij b *
        (Matrix.SpecialLinearGroup.transvection hij.symm a)⁻¹) *
      (Matrix.SpecialLinearGroup.transvection hkl c)⁻¹ ∈
      relativeZSubgroup I := by
  let x : SL R := Matrix.SpecialLinearGroup.transvection hkl c
  let y : SL R := Matrix.SpecialLinearGroup.transvection hij.symm a
  let z : SL R := Matrix.SpecialLinearGroup.transvection hij b
  have hxyconj : x * y * x⁻¹ = y :=
    suslin_transvection_conj_noncomposable hkl hij.symm hlj hik c a
  have hxy : x * y = y * x := by
    calc
      x * y = (x * y * x⁻¹) * x := by simp only [mul_assoc, inv_mul_cancel, mul_one]
      _ = y * x := by rw [hxyconj]
  have hxyinv : y⁻¹ * x⁻¹ = x⁻¹ * y⁻¹ := by
    simpa only [mul_inv_rev] using congrArg Inv.inv hxy
  have hroot : x * z * x⁻¹ ∈ relativeRootSubgroup I :=
    conjugate_relative_root_mem_F_of_not_opposite
      I k l i j hkl hij c b hb hnot
  have hy : y * (x * z * x⁻¹) * y⁻¹ ∈ relativeZSubgroup I :=
    conjugate_relative_F_mem_Z I j i hij.symm a hroot
  change x * (y * z * y⁻¹) * x⁻¹ ∈ relativeZSubgroup I
  rw [show x * (y * z * y⁻¹) * x⁻¹ =
      y * (x * z * x⁻¹) * y⁻¹ by
    calc
      x * (y * z * y⁻¹) * x⁻¹ =
          (x * y) * z * (y⁻¹ * x⁻¹) := by simp only [mul_assoc]
      _ = (y * x) * z * (x⁻¹ * y⁻¹) := by rw [hxy, hxyinv]
      _ = y * (x * z * x⁻¹) * y⁻¹ := by simp only [mul_assoc]]
  exact hy

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem conjugate_mul_relative_root_mem_Z
    (I : Ideal R) (k l m n i j : Fin 4)
    (hkl : k ≠ l) (hmn : m ≠ n) (hij : i ≠ j)
    (a c b : R) (hb : b ∈ I)
    (hnot : ¬ (m = j ∧ n = i)) :
    (Matrix.SpecialLinearGroup.transvection hkl a *
      Matrix.SpecialLinearGroup.transvection hmn c) *
      Matrix.SpecialLinearGroup.transvection hij b *
      (Matrix.SpecialLinearGroup.transvection hkl a *
        Matrix.SpecialLinearGroup.transvection hmn c)⁻¹ ∈
      relativeZSubgroup I := by
  have hinner :
      Matrix.SpecialLinearGroup.transvection hmn c *
        Matrix.SpecialLinearGroup.transvection hij b *
        (Matrix.SpecialLinearGroup.transvection hmn c)⁻¹ ∈
        relativeRootSubgroup I :=
    conjugate_relative_root_mem_F_of_not_opposite
      I m n i j hmn hij c b hb hnot
  have houter := conjugate_relative_F_mem_Z I k l hkl a hinner
  simpa only [mul_assoc, mul_inv_rev] using houter

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem hard_commutator_mem_relativeZ
    (I : Ideal R) (i j k : Fin 4)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (a b c : R) (hb : b ∈ I) :
    let U : SL R :=
      Matrix.SpecialLinearGroup.transvection hik (b * (1 + a * c)) *
        Matrix.SpecialLinearGroup.transvection hjk (a * b)
    let V : SL R :=
      Matrix.SpecialLinearGroup.transvection hik.symm (-a) *
        Matrix.SpecialLinearGroup.transvection hjk.symm (1 + a * c)
    U * V * U⁻¹ * V⁻¹ ∈ relativeZSubgroup I := by
  let u : SL R :=
    Matrix.SpecialLinearGroup.transvection hik (b * (1 + a * c))
  let v : SL R :=
    Matrix.SpecialLinearGroup.transvection hjk (a * b)
  let x : SL R := Matrix.SpecialLinearGroup.transvection hik.symm (-a)
  let y : SL R :=
    Matrix.SpecialLinearGroup.transvection hjk.symm (1 + a * c)
  have hbu : b * (1 + a * c) ∈ I := I.mul_mem_right (1 + a * c) hb
  have hbv : a * b ∈ I := I.mul_mem_left a hb
  have hu : u ∈ relativeZSubgroup I :=
    relativeRoot_mem_Z I i k hik (b * (1 + a * c)) hbu
  have hv : v ∈ relativeZSubgroup I :=
    relativeRoot_mem_Z I j k hjk (a * b) hbv
  have hxconj : x * y * x⁻¹ = y :=
    suslin_transvection_conj_noncomposable
      hik.symm hjk.symm hik hjk (-a) (1 + a * c)
  have hxy : x * y = y * x := by
    calc
      x * y = (x * y * x⁻¹) * x := by simp only [mul_assoc, inv_mul_cancel, mul_one]
      _ = y * x := by rw [hxconj]
  have hfirst : (x * y) * u * (x * y)⁻¹ ∈ relativeZSubgroup I := by
    exact conjugate_mul_relative_root_mem_Z
      I k i k j i k hik.symm hjk.symm hik
      (-a) (1 + a * c) (b * (1 + a * c)) hbu
      (fun h => hij h.2.symm)
  have hsecond : (x * y) * v * (x * y)⁻¹ ∈ relativeZSubgroup I := by
    rw [hxy]
    exact conjugate_mul_relative_root_mem_Z
      I k j k i j k hjk.symm hik.symm hjk
      (1 + a * c) (-a) (a * b) hbv
      (fun h => hij h.2)
  have hconjInv :
      (x * y) * (u * v)⁻¹ * (x * y)⁻¹ ∈ relativeZSubgroup I := by
    have h := (relativeZSubgroup I).mul_mem
      ((relativeZSubgroup I).inv_mem hsecond)
      ((relativeZSubgroup I).inv_mem hfirst)
    simpa only [mul_inv_rev, mul_assoc, inv_inv, inv_mul_cancel_left] using h
  change (u * v) * (x * y) * (u * v)⁻¹ * (x * y)⁻¹ ∈
    relativeZSubgroup I
  have huv := (relativeZSubgroup I).mul_mem hu hv
  have h := (relativeZSubgroup I).mul_mem huv hconjInv
  simpa only [mul_assoc, mul_inv_rev] using h

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem conjugate_Z_generator_of_not_same_inner
    (I : Ideal R) (k l i j : Fin 4)
    (hkl : k ≠ l) (hij : i ≠ j)
    (c a b : R) (hb : b ∈ I)
    (hnot : ¬ (k = i ∧ l = j)) :
    Matrix.SpecialLinearGroup.transvection hkl c *
      (Matrix.SpecialLinearGroup.transvection hij.symm a *
        Matrix.SpecialLinearGroup.transvection hij b *
        (Matrix.SpecialLinearGroup.transvection hij.symm a)⁻¹) *
      (Matrix.SpecialLinearGroup.transvection hkl c)⁻¹ ∈
      relativeZSubgroup I := by
  let x : SL R := Matrix.SpecialLinearGroup.transvection hkl c
  let y : SL R := Matrix.SpecialLinearGroup.transvection hij.symm a
  let z : SL R := Matrix.SpecialLinearGroup.transvection hij b
  by_cases hkj : k = j
  · subst k
    by_cases hli : l = i
    · subst l
      have hxy : x * y =
          Matrix.SpecialLinearGroup.transvection hij.symm (c + a) :=
        (Matrix.SpecialLinearGroup.transvection_add hij.symm c a).symm
      change x * (y * z * y⁻¹) * x⁻¹ ∈ relativeZSubgroup I
      rw [show x * (y * z * y⁻¹) * x⁻¹ =
          (x * y) * z * (x * y)⁻¹ by simp only [mul_assoc, mul_inv_rev], hxy]
      exact relativeZ_mem I i j hij (c + a) b hb
    · exact conjugate_Z_generator_of_commute_outer I j l i j
        hkl hij c a b hb (Ne.symm hkl) hij
        (fun h => hli h.2)
  · by_cases hli : l = i
    · subst l
      exact conjugate_Z_generator_of_commute_outer I k i i j
        hkl hij c a b hb hij (Ne.symm hkl)
        (fun h => hkj h.1)
    · by_cases hlj : l = j
      · subst l
        have hki : k ≠ i := fun h => hnot ⟨h, rfl⟩
        let u : SL R :=
          Matrix.SpecialLinearGroup.transvection hki (c * a)
        have hxy : x * y * x⁻¹ = u * y :=
          suslin_transvection_conj_adjacent k j i hkl hij.symm hki c a
        have hxz : x * z * x⁻¹ = z :=
          suslin_transvection_conj_noncomposable hkl hij hij.symm
            (Ne.symm hkl) c b
        change x * (y * z * y⁻¹) * x⁻¹ ∈ relativeZSubgroup I
        rw [show x * (y * z * y⁻¹) * x⁻¹ =
            u * (y * z * y⁻¹) * u⁻¹ by
          calc
            x * (y * z * y⁻¹) * x⁻¹ =
                (x * y * x⁻¹) * (x * z * x⁻¹) *
                  (x * y * x⁻¹)⁻¹ := by simp only [mul_assoc, inv_mul_cancel_left, mul_inv_rev,
                                          inv_inv]
            _ = (u * y) * z * (u * y)⁻¹ := by rw [hxy, hxz]
            _ = u * (y * z * y⁻¹) * u⁻¹ := by simp only [mul_assoc, mul_inv_rev]]
        exact conjugate_Z_generator_of_commute_outer I k i i j
          hki hij (c * a) a b hb hij (Ne.symm hki)
          (fun h => hkj h.1)
      · by_cases hki : k = i
        · subst k
          let u : SL R :=
            Matrix.SpecialLinearGroup.transvection (Ne.symm hlj) (-(a * c))
          have hxy : x * y * x⁻¹ = u * y :=
            suslin_transvection_conj_reverse_adjacent i l j
              hkl hlj hij c a
          have hxz : x * z * x⁻¹ = z :=
            suslin_transvection_conj_noncomposable hkl hij
              (Ne.symm hkl) hij.symm c b
          change x * (y * z * y⁻¹) * x⁻¹ ∈ relativeZSubgroup I
          rw [show x * (y * z * y⁻¹) * x⁻¹ =
              u * (y * z * y⁻¹) * u⁻¹ by
            calc
              x * (y * z * y⁻¹) * x⁻¹ =
                  (x * y * x⁻¹) * (x * z * x⁻¹) *
                    (x * y * x⁻¹)⁻¹ := by simp only [mul_assoc, inv_mul_cancel_left, mul_inv_rev,
                                            inv_inv]
              _ = (u * y) * z * (u * y)⁻¹ := by rw [hxy, hxz]
              _ = u * (y * z * y⁻¹) * u⁻¹ := by simp only [mul_assoc, mul_inv_rev]]
          exact conjugate_Z_generator_of_commute_outer I j l i j
            (Ne.symm hlj) hij (-(a * c)) a b hb hlj hij
            (fun h => hkl h.2.symm)
        · exact conjugate_Z_generator_of_commute_outer I k l i j
            hkl hij c a b hb hlj (Ne.symm hki)
            (fun h => hkj h.1)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem suslin_bak_vavilov_opposite_conjugate_factor
    {ι : Type u} {A : Type v}
    [Fintype ι] [DecidableEq ι] [CommRing A]
    (i j k : ι) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (c a b : A) :
    Matrix.SpecialLinearGroup.transvection hij c *
      (Matrix.SpecialLinearGroup.transvection hij.symm a *
        Matrix.SpecialLinearGroup.transvection hij b *
        (Matrix.SpecialLinearGroup.transvection hij.symm a)⁻¹) *
      (Matrix.SpecialLinearGroup.transvection hij c)⁻¹ =
      (Matrix.SpecialLinearGroup.transvection hik
          (b * (1 + a * c)) *
        Matrix.SpecialLinearGroup.transvection hjk (a * b)) *
      (Matrix.SpecialLinearGroup.transvection hik.symm (-a) *
        Matrix.SpecialLinearGroup.transvection hjk.symm (1 + a * c)) *
      (Matrix.SpecialLinearGroup.transvection hik
          (b * (1 + a * c)) *
        Matrix.SpecialLinearGroup.transvection hjk (a * b))⁻¹ *
      (Matrix.SpecialLinearGroup.transvection hik.symm (-a) *
        Matrix.SpecialLinearGroup.transvection hjk.symm (1 + a * c))⁻¹ := by
  let x := Matrix.SpecialLinearGroup.transvection hij c
  let y := Matrix.SpecialLinearGroup.transvection hij.symm a
  let u := Matrix.SpecialLinearGroup.transvection hik b
  let v := Matrix.SpecialLinearGroup.transvection hjk.symm (1 : A)
  let U := Matrix.SpecialLinearGroup.transvection hik (b * (1 + a * c)) *
    Matrix.SpecialLinearGroup.transvection hjk (a * b)
  let V := Matrix.SpecialLinearGroup.transvection hik.symm (-a) *
    Matrix.SpecialLinearGroup.transvection hjk.symm (1 + a * c)
  have hxyu :
      (x * y) * u * (x * y)⁻¹ = U := by
    have hyu : y * u * y⁻¹ =
        Matrix.SpecialLinearGroup.transvection hjk (a * b) *
          Matrix.SpecialLinearGroup.transvection hik b :=
      suslin_transvection_conj_adjacent j i k hij.symm hik hjk a b
    have hxleft :
        x * Matrix.SpecialLinearGroup.transvection hjk (a * b) * x⁻¹ =
          Matrix.SpecialLinearGroup.transvection hik (c * (a * b)) *
            Matrix.SpecialLinearGroup.transvection hjk (a * b) :=
      suslin_transvection_conj_adjacent i j k hij hjk hik c (a * b)
    have hxright :
        x * Matrix.SpecialLinearGroup.transvection hik b * x⁻¹ =
          Matrix.SpecialLinearGroup.transvection hik b :=
      suslin_transvection_conj_noncomposable hij hik hij.symm hik.symm c b
    have hcomm :
        Matrix.SpecialLinearGroup.transvection hjk (a * b) *
          Matrix.SpecialLinearGroup.transvection hik b =
        Matrix.SpecialLinearGroup.transvection hik b *
          Matrix.SpecialLinearGroup.transvection hjk (a * b) := by
      have h := suslin_transvection_conj_noncomposable
        hjk hik hik.symm hjk.symm (a * b) b
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using congrArg
        (fun z => z * Matrix.SpecialLinearGroup.transvection hjk (a * b)) h
    calc
      (x * y) * u * (x * y)⁻¹ =
          x * (y * u * y⁻¹) * x⁻¹ := by simp only [mul_assoc, mul_inv_rev]
      _ = x *
          (Matrix.SpecialLinearGroup.transvection hjk (a * b) *
            Matrix.SpecialLinearGroup.transvection hik b) * x⁻¹ := by rw [hyu]
      _ =
          (x * Matrix.SpecialLinearGroup.transvection hjk (a * b) * x⁻¹) *
            (x * Matrix.SpecialLinearGroup.transvection hik b * x⁻¹) := by
              simp only [mul_assoc, inv_mul_cancel_left]
      _ =
          (Matrix.SpecialLinearGroup.transvection hik (c * (a * b)) *
            Matrix.SpecialLinearGroup.transvection hjk (a * b)) *
            Matrix.SpecialLinearGroup.transvection hik b := by
              rw [hxleft, hxright]
      _ =
          (Matrix.SpecialLinearGroup.transvection hik (c * (a * b)) *
            Matrix.SpecialLinearGroup.transvection hik b) *
            Matrix.SpecialLinearGroup.transvection hjk (a * b) := by
              simp only [mul_assoc]
              rw [hcomm]
      _ = U := by
        rw [← Matrix.SpecialLinearGroup.transvection_add]
        dsimp [U]
        congr 2
        ring
  have hxyv :
      (x * y) * v * (x * y)⁻¹ = V := by
    have hyv : y * v * y⁻¹ =
        Matrix.SpecialLinearGroup.transvection hik.symm (-a) *
          Matrix.SpecialLinearGroup.transvection hjk.symm 1 := by
      simpa only [one_mul] using suslin_transvection_conj_reverse_adjacent
        j i k hij.symm hik hjk a (1 : A)
    have hxleft :
        x * Matrix.SpecialLinearGroup.transvection hik.symm (-a) * x⁻¹ =
          Matrix.SpecialLinearGroup.transvection hjk.symm (a * c) *
            Matrix.SpecialLinearGroup.transvection hik.symm (-a) := by
      simpa only [neg_mul, neg_neg] using suslin_transvection_conj_reverse_adjacent
        i j k hij hjk hik c (-a)
    have hxright :
        x * Matrix.SpecialLinearGroup.transvection hjk.symm 1 * x⁻¹ =
          Matrix.SpecialLinearGroup.transvection hjk.symm 1 :=
      suslin_transvection_conj_noncomposable
        hij hjk.symm hjk hij.symm c 1
    have hcomm :
        Matrix.SpecialLinearGroup.transvection hjk.symm (a * c) *
          Matrix.SpecialLinearGroup.transvection hik.symm (-a) =
        Matrix.SpecialLinearGroup.transvection hik.symm (-a) *
          Matrix.SpecialLinearGroup.transvection hjk.symm (a * c) := by
      have h := suslin_transvection_conj_noncomposable
        hjk.symm hik.symm hjk hik (a * c) (-a)
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using congrArg
        (fun z => z * Matrix.SpecialLinearGroup.transvection hjk.symm (a * c)) h
    calc
      (x * y) * v * (x * y)⁻¹ =
          x * (y * v * y⁻¹) * x⁻¹ := by simp only [mul_assoc, mul_inv_rev]
      _ = x *
          (Matrix.SpecialLinearGroup.transvection hik.symm (-a) *
            Matrix.SpecialLinearGroup.transvection hjk.symm 1) * x⁻¹ := by
              rw [hyv]
      _ =
          (x * Matrix.SpecialLinearGroup.transvection hik.symm (-a) * x⁻¹) *
            (x * Matrix.SpecialLinearGroup.transvection hjk.symm 1 * x⁻¹) := by
              simp only [mul_assoc, inv_mul_cancel_left]
      _ =
          (Matrix.SpecialLinearGroup.transvection hjk.symm (a * c) *
            Matrix.SpecialLinearGroup.transvection hik.symm (-a)) *
            Matrix.SpecialLinearGroup.transvection hjk.symm 1 := by
              rw [hxleft, hxright]
      _ =
          Matrix.SpecialLinearGroup.transvection hik.symm (-a) *
            (Matrix.SpecialLinearGroup.transvection hjk.symm (a * c) *
              Matrix.SpecialLinearGroup.transvection hjk.symm 1) := by
              rw [hcomm, mul_assoc]
      _ = V := by
        rw [← Matrix.SpecialLinearGroup.transvection_add]
        dsimp [V]
        congr 2
        ring
  have hcomm := specialLinear_transvection_commutator
    i k j hik hjk.symm hij b (1 : A)
  have hcomm' :
      u * v * u⁻¹ * v⁻¹ =
        Matrix.SpecialLinearGroup.transvection hij b := by
    dsimp [u, v]
    simpa only [mul_one] using hcomm
  change
    x * (y * Matrix.SpecialLinearGroup.transvection hij b * y⁻¹) * x⁻¹ =
      U * V * U⁻¹ * V⁻¹
  rw [← hcomm']
  calc
    x * (y * (u * v * u⁻¹ * v⁻¹) * y⁻¹) * x⁻¹ =
        ((x * y) * u * (x * y)⁻¹) *
          ((x * y) * v * (x * y)⁻¹) *
          ((x * y) * u * (x * y)⁻¹)⁻¹ *
          ((x * y) * v * (x * y)⁻¹)⁻¹ := by
            simp only [mul_assoc, mul_inv_rev, inv_mul_cancel_left, inv_inv]
    _ = U * V * U⁻¹ * V⁻¹ := by rw [hxyu, hxyv]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem conjugate_Z_generator
    (I : Ideal R) (k l i j : Fin 4)
    (hkl : k ≠ l) (hij : i ≠ j)
    (c a b : R) (hb : b ∈ I) :
    Matrix.SpecialLinearGroup.transvection hkl c *
      (Matrix.SpecialLinearGroup.transvection hij.symm a *
        Matrix.SpecialLinearGroup.transvection hij b *
        (Matrix.SpecialLinearGroup.transvection hij.symm a)⁻¹) *
      (Matrix.SpecialLinearGroup.transvection hkl c)⁻¹ ∈
      relativeZSubgroup I := by
  by_cases hsame : k = i ∧ l = j
  · obtain ⟨hki, hlj⟩ := hsame
    subst k
    subst l
    obtain ⟨m, hmi, hmj⟩ :=
      Fin.exists_ne_and_ne_of_two_lt i j (by decide : 2 < 4)
    rw [suslin_bak_vavilov_opposite_conjugate_factor
      i j m hij hmj.symm hmi.symm c a b]
    exact hard_commutator_mem_relativeZ I i j m hij hmi.symm hmj.symm
      a b c hb
  · exact conjugate_Z_generator_of_not_same_inner
      I k l i j hkl hij c a b hb hsame

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem relativeZ_conjugate_by_root
    (I : Ideal R) (k l : Fin 4) (hkl : k ≠ l) (c : R)
    {z : SL R} (hz : z ∈ relativeZSubgroup I) :
    Matrix.SpecialLinearGroup.transvection hkl c * z *
        (Matrix.SpecialLinearGroup.transvection hkl c)⁻¹ ∈
      relativeZSubgroup I := by
  induction hz using Subgroup.closure_induction with
  | mem z hz =>
      obtain ⟨i, j, hij, a, b, hb, rfl⟩ := hz
      exact conjugate_Z_generator I k l i j hkl hij c a b hb
  | one =>
      simp only [mul_one, mul_inv_cancel, one_mem]
  | mul x y hx hy ihx ihy =>
      have h := (relativeZSubgroup I).mul_mem ihx ihy
      simpa only [mul_assoc, inv_mul_cancel_left] using h
  | inv x hx ih =>
      have h := (relativeZSubgroup I).inv_mem ih
      simpa only [mul_assoc, mul_inv_rev, inv_inv] using h

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem elementary_le_normalizer_relativeZ (I : Ideal R) :
    suslinElementarySubgroup (Fin 4) R ≤
      Subgroup.normalizer (relativeZSubgroup I : Set (SL R)) := by
  change Subgroup.closure _ ≤ _
  rw [Subgroup.closure_le]
  rintro _ ⟨i, j, hij, a, rfl⟩
  change Matrix.SpecialLinearGroup.transvection hij a ∈
    Subgroup.normalizer (relativeZSubgroup I : Set (SL R))
  apply (Subgroup.mem_normalizer_iff).2
  intro z
  constructor
  · intro hz
    exact relativeZ_conjugate_by_root I i j hij a hz
  · intro hz
    have h := relativeZ_conjugate_by_root I i j hij (-a) hz
    rw [← Matrix.SpecialLinearGroup.transvection_inv hij a] at h
    simpa only [mul_assoc, inv_mul_cancel_left, inv_inv, inv_mul_cancel, mul_one] using h

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem relativeZ_normalized_by_elementary
    (I : Ideal R) {g : SL R}
    (hg : g ∈ suslinElementarySubgroup (Fin 4) R)
    {z : SL R} (hz : z ∈ relativeZSubgroup I) :
    g * z * g⁻¹ ∈ relativeZSubgroup I :=
  (Subgroup.mem_normalizer_iff.mp
    (elementary_le_normalizer_relativeZ I hg) z).mp hz

end

section

open Polynomial

universe u v

variable {A : Type u} [CommRing A]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def suslinPolynomialConstantRetraction (A : Type*) [CommRing A] :
    Matrix.SpecialLinearGroup Index (Polynomial A) →*
      Matrix.SpecialLinearGroup Index (Polynomial A) :=
  (Matrix.SpecialLinearGroup.map (Polynomial.C : A →+* Polynomial A)).comp
    (Matrix.SpecialLinearGroup.map (Polynomial.evalRingHom (0 : A)))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem suslinPolynomialConstantRetraction_transvection
    (i j : Index) (hij : i ≠ j) (p : Polynomial A) :
    suslinPolynomialConstantRetraction A
        (Matrix.SpecialLinearGroup.transvection hij p) =
      Matrix.SpecialLinearGroup.transvection hij
        (Polynomial.C (p.eval 0)) := by
  unfold suslinPolynomialConstantRetraction
  change
    Matrix.SpecialLinearGroup.map (Polynomial.C : A →+* Polynomial A)
        (Matrix.SpecialLinearGroup.map (Polynomial.evalRingHom (0 : A))
          (Matrix.SpecialLinearGroup.transvection hij p)) = _
  rw [specialLinear_map_transvection_baseChange,
    specialLinear_map_transvection_baseChange]
  rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem suslinPolynomial_sub_C_eval_coeff_zero
    (p : Polynomial A) :
    (p - Polynomial.C (p.eval 0)).coeff 0 = 0 := by
  simp only [coeff_zero_eq_eval_zero, eval_sub, eval_C, sub_self]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem suslinPolynomialRoot_deviation
    (i j : Index) (hij : i ≠ j) (p : Polynomial A) :
    Matrix.SpecialLinearGroup.transvection hij p *
        (suslinPolynomialConstantRetraction A
          (Matrix.SpecialLinearGroup.transvection hij p))⁻¹ =
      Matrix.SpecialLinearGroup.transvection hij
        (p - Polynomial.C (p.eval 0)) := by
  rw [suslinPolynomialConstantRetraction_transvection,
    Matrix.SpecialLinearGroup.transvection_inv,
    ← Matrix.SpecialLinearGroup.transvection_add, sub_eq_add_neg]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem suslinElementary_deviation_mem_of_normalized
    (H : Subgroup (Matrix.SpecialLinearGroup Index (Polynomial A)))
    (hroot : ∀ (i j : Index) (hij : i ≠ j) (p : Polynomial A),
      p.coeff 0 = 0 → Matrix.SpecialLinearGroup.transvection hij p ∈ H)
    (hnormal : ∀ (x : Matrix.SpecialLinearGroup Index (Polynomial A)),
      x ∈ localGlobalElementarySubgroup (Polynomial A) →
      ∀ (z : Matrix.SpecialLinearGroup Index (Polynomial A)),
        z ∈ H → x * z * x⁻¹ ∈ H)
    {g : Matrix.SpecialLinearGroup Index (Polynomial A)}
    (hg : g ∈ localGlobalElementarySubgroup (Polynomial A)) :
    g * (suslinPolynomialConstantRetraction A g)⁻¹ ∈ H := by
  change g ∈ Subgroup.closure _ at hg
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
      obtain ⟨i, j, hij, p, rfl⟩ := hg
      rw [suslinPolynomialRoot_deviation]
      exact hroot i j hij (p - Polynomial.C (p.eval 0))
        (suslinPolynomial_sub_C_eval_coeff_zero p)
  | one =>
      simp only [map_one, inv_one, mul_one, one_mem]
  | mul x y hx hy ihx ihy =>
      have hxelem : x ∈ localGlobalElementarySubgroup (Polynomial A) := hx
      have hc :
          x * (y * (suslinPolynomialConstantRetraction A y)⁻¹) * x⁻¹ ∈ H :=
        hnormal x hxelem _ ihy
      have hp := H.mul_mem hc ihx
      simpa only [map_mul, mul_inv_rev, mul_assoc, inv_mul_cancel_left] using hp
  | inv x hx ih =>
      have hxelem : x ∈ localGlobalElementarySubgroup (Polynomial A) := hx
      have hxe : x⁻¹ ∈ localGlobalElementarySubgroup (Polynomial A) :=
        (localGlobalElementarySubgroup (Polynomial A)).inv_mem hxelem
      have hc :
          x⁻¹ * (x * (suslinPolynomialConstantRetraction A x)⁻¹)⁻¹ *
              (x⁻¹)⁻¹ ∈ H :=
        hnormal x⁻¹ hxe _ (H.inv_mem ih)
      simpa only [map_inv, inv_inv, mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one] using hc

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem suslinRelativePolynomialKernel_le_of_normalized
    (H : Subgroup (Matrix.SpecialLinearGroup Index (Polynomial A)))
    (hroot : ∀ (i j : Index) (hij : i ≠ j) (p : Polynomial A),
      p.coeff 0 = 0 → Matrix.SpecialLinearGroup.transvection hij p ∈ H)
    (hnormal : ∀ (x : Matrix.SpecialLinearGroup Index (Polynomial A)),
      x ∈ localGlobalElementarySubgroup (Polynomial A) →
      ∀ (z : Matrix.SpecialLinearGroup Index (Polynomial A)),
        z ∈ H → x * z * x⁻¹ ∈ H)
    {g : Matrix.SpecialLinearGroup Index (Polynomial A)}
    (hg : g ∈ localGlobalElementarySubgroup (Polynomial A))
    (hzero : Matrix.SpecialLinearGroup.map
      (Polynomial.evalRingHom (0 : A)) g = 1) :
    g ∈ H := by
  have hdev := suslinElementary_deviation_mem_of_normalized H hroot hnormal hg
  have hretract : suslinPolynomialConstantRetraction A g = 1 := by
    change
      Matrix.SpecialLinearGroup.map (Polynomial.C : A →+* Polynomial A)
        (Matrix.SpecialLinearGroup.map
          (Polynomial.evalRingHom (0 : A)) g) = 1
    rw [hzero, map_one]
  simpa only [hretract, inv_one, mul_one] using hdev

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem suslin_relative_elementary_mem_eventual
    {B : Type v} [CommRing B] [Algebra A B]
    (M : Submonoid A) [IsLocalization M B]
    {g : Matrix.SpecialLinearGroup Index (Polynomial B)}
    (hg : g ∈ localGlobalElementarySubgroup (Polynomial B))
    (hzero : Matrix.SpecialLinearGroup.map
      (Polynomial.evalRingHom (0 : B)) g = 1) :
    g ∈ suslinEventuallyElementarySubgroup (A := A) (B := B) M := by
  let I : Ideal (Polynomial B) :=
    RingHom.ker (Polynomial.evalRingHom (0 : B))
  have hroot : ∀ (i j : Index) (hij : i ≠ j) (p : Polynomial B),
      p.coeff 0 = 0 →
        Matrix.SpecialLinearGroup.transvection hij p ∈ relativeZSubgroup I := by
    intro i j hij p hp
    apply relativeRoot_mem_Z I i j hij p
    change p.eval 0 = 0
    simpa only [coeff_zero_eq_eval_zero] using hp
  have hnormal :
      ∀ (x : Matrix.SpecialLinearGroup Index (Polynomial B)),
        x ∈ localGlobalElementarySubgroup (Polynomial B) →
          ∀ (z : Matrix.SpecialLinearGroup Index (Polynomial B)),
            z ∈ relativeZSubgroup I → x * z * x⁻¹ ∈ relativeZSubgroup I := by
    intro x hx z hz
    apply relativeZ_normalized_by_elementary I
    · exact hx
    · exact hz
  have hZ : g ∈ relativeZSubgroup I :=
    suslinRelativePolynomialKernel_le_of_normalized
      (relativeZSubgroup I) hroot hnormal hg hzero
  have hle : relativeZSubgroup I ≤
      suslinEventuallyElementarySubgroup (A := A) (B := B) M := by
    change Subgroup.closure _ ≤ _
    rw [Subgroup.closure_le]
    rintro _ ⟨i, j, hij, a, p, hp, rfl⟩
    have hpzero : p.coeff 0 = 0 := by
      change p.eval 0 = 0 at hp
      simpa only [coeff_zero_eq_eval_zero] using hp
    exact suslin_polynomial_relative_z_mem_eventual M i j hij a p hpzero
  exact hle hZ

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem exists_localization_dilated_relative_elementary_word_lift
    {B : Type v} [CommRing B] [Algebra A B]
    (M : Submonoid A) [IsLocalization M B]
    (g : Matrix.SpecialLinearGroup Index (Polynomial B))
    (hg : g ∈ localGlobalElementarySubgroup (Polynomial B))
    (hzero : Matrix.SpecialLinearGroup.map
      (Polynomial.evalRingHom (0 : B)) g = 1) :
    ∃ (d : M) (q : Matrix.SpecialLinearGroup Index (Polynomial A)),
      q ∈ localGlobalElementarySubgroup (Polynomial A) ∧
        Matrix.SpecialLinearGroup.map
          (Polynomial.mapRingHom (algebraMap A B)) q =
          suslinDilation B (algebraMap A B (d : A)) g :=
  suslin_relative_elementary_mem_eventual M hg hzero

end

section

open Polynomial

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def suslinSymbolicLift (g : IntegralSpecialLinearGroup) :
    Matrix.SpecialLinearGroup Index (Polynomial (Polynomial ℤ)) :=
  Matrix.SpecialLinearGroup.map
    (Polynomial.mapRingHom (Polynomial.C : ℤ →+* Polynomial ℤ)) g

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem suslinSymbolicLift_eval
    (a : ℤ) (g : IntegralSpecialLinearGroup) :
    Matrix.SpecialLinearGroup.map
        (Polynomial.mapRingHom (Polynomial.evalRingHom a))
        (suslinSymbolicLift g) = g := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  change
    Polynomial.map (Polynomial.evalRingHom a)
      (Polynomial.map (Polynomial.C : ℤ →+* Polynomial ℤ) (g i j)) = g i j
  rw [Polynomial.map_map]
  have h : (Polynomial.evalRingHom a).comp
      (Polynomial.C : ℤ →+* Polynomial ℤ) = RingHom.id ℤ := by
    ext z
    simp only [eq_intCast, Int.cast_eq]
  rw [h, Polynomial.map_id]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem suslinSymbolicDifference_eval
    (a : ℤ) (g : IntegralSpecialLinearGroup) :
    Matrix.SpecialLinearGroup.map
        (Polynomial.mapRingHom
          (Polynomial.mapRingHom (Polynomial.evalRingHom a)))
        (suslinDifferencePath (Polynomial.X : Polynomial ℤ)
          (suslinSymbolicLift g)) =
      suslinDifferencePath a g := by
  rw [suslinDifferencePath_baseChange]
  simp only [coe_evalRingHom, eval_X, suslinSymbolicLift_eval]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem suslinSymbolicDifferenceDilation_integer
    (a : ℤ) (g : IntegralSpecialLinearGroup) :
    suslinDifferenceDilation a g = suslinPolynomialDilate a g := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem suslinSymbolic_outer_dilation_eval_mul_X
    (c d : ℤ) :
    (Polynomial.evalRingHom
        (Polynomial.C c * (Polynomial.X : Polynomial ℤ))).comp
        (suslinDifferenceDilationRingHom
          (Polynomial.C d : Polynomial ℤ)) =
      Polynomial.evalRingHom
        (Polynomial.C (c * d) * (Polynomial.X : Polynomial ℤ)) := by
  apply Polynomial.ringHom_ext
  · intro p
    simp only [eq_intCast, suslinDifferenceDilationRingHom, map_intCast, RingHom.coe_comp,
      coe_evalRingHom, coe_compRingHom, Function.comp_apply, C_comp, eval_C, Int.cast_mul]
  · simp only [eq_intCast, suslinDifferenceDilationRingHom, map_intCast, RingHom.coe_comp,
      coe_evalRingHom, coe_compRingHom, Function.comp_apply, X_comp, eval_mul, eval_intCast, eval_X,
      mul_left_comm, Int.cast_mul, mul_assoc]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem suslinSymbolicPoweredIncrement_of_elementary_dilation
    (g : IntegralSpecialLinearGroup) (d : ℤ) (N : ℕ)
    (hpath :
      suslinDilation (Polynomial (Polynomial ℤ))
          (Polynomial.C (Polynomial.C (d ^ N)))
          (suslinDifferencePath (Polynomial.X : Polynomial ℤ)
            (suslinSymbolicLift g)) ∈
        localGlobalElementarySubgroup
          (Polynomial (Polynomial (Polynomial ℤ)))) :
    ∀ a c : ℤ,
      suslinPolynomialDilate (a + c * d ^ N) g *
          (suslinPolynomialDilate a g)⁻¹ ∈
        integralElementarySubgroup := by
  intro a c
  let f : Polynomial (Polynomial ℤ) →+* Polynomial ℤ :=
    Polynomial.mapRingHom (Polynomial.evalRingHom a)
  let r : Polynomial (Polynomial (Polynomial ℤ)) →+* Polynomial ℤ :=
    (Polynomial.evalRingHom
      (Polynomial.C c * (Polynomial.X : Polynomial ℤ))).comp
      (Polynomial.mapRingHom f)
  have hmem := map_localGlobalElementarySubgroup_le r
    ⟨suslinDilation (Polynomial (Polynomial ℤ))
      (Polynomial.C (Polynomial.C (d ^ N)))
      (suslinDifferencePath (Polynomial.X : Polynomial ℤ)
        (suslinSymbolicLift g)), hpath, rfl⟩
  have hbase :
      Matrix.SpecialLinearGroup.map (Polynomial.mapRingHom f)
          (suslinDilation (Polynomial (Polynomial ℤ))
            (Polynomial.C (Polynomial.C (d ^ N)))
            (suslinDifferencePath (Polynomial.X : Polynomial ℤ)
              (suslinSymbolicLift g))) =
        suslinDifferenceDilation (Polynomial.C (d ^ N))
          (suslinDifferencePath a g) := by
    have h := suslinDifferenceDilation_baseChange f
      (Polynomial.C (Polynomial.C (d ^ N)))
      (suslinDifferencePath (Polynomial.X : Polynomial ℤ)
        (suslinSymbolicLift g))
    change
      Matrix.SpecialLinearGroup.map (Polynomial.mapRingHom f)
          (suslinDilation (Polynomial (Polynomial ℤ))
            (Polynomial.C (Polynomial.C (d ^ N)))
            (suslinDifferencePath (Polynomial.X : Polynomial ℤ)
              (suslinSymbolicLift g))) =
        suslinDifferenceDilation
          (f (Polynomial.C (Polynomial.C (d ^ N))))
          (Matrix.SpecialLinearGroup.map (Polynomial.mapRingHom f)
            (suslinDifferencePath (Polynomial.X : Polynomial ℤ)
              (suslinSymbolicLift g))) at h
    simpa [f, suslinSymbolicDifference_eval] using h
  have heval :
      Matrix.SpecialLinearGroup.map r
          (suslinDilation (Polynomial (Polynomial ℤ))
            (Polynomial.C (Polynomial.C (d ^ N)))
            (suslinDifferencePath (Polynomial.X : Polynomial ℤ)
              (suslinSymbolicLift g))) =
        Matrix.SpecialLinearGroup.map
          (Polynomial.evalRingHom
            (Polynomial.C (c * d ^ N) *
              (Polynomial.X : Polynomial ℤ)))
          (suslinDifferencePath a g) := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    change
      (Polynomial.evalRingHom
        (Polynomial.C c * (Polynomial.X : Polynomial ℤ)))
          ((Polynomial.mapRingHom f)
            ((suslinDilation (Polynomial (Polynomial ℤ))
              (Polynomial.C (Polynomial.C (d ^ N)))
              (suslinDifferencePath (Polynomial.X : Polynomial ℤ)
                (suslinSymbolicLift g))) i j)) = _
    rw [show (Polynomial.mapRingHom f)
          ((suslinDilation (Polynomial (Polynomial ℤ))
            (Polynomial.C (Polynomial.C (d ^ N)))
            (suslinDifferencePath (Polynomial.X : Polynomial ℤ)
              (suslinSymbolicLift g))) i j) =
          (suslinDifferenceDilation (Polynomial.C (d ^ N))
            (suslinDifferencePath a g)) i j from
      congrFun (congrFun (congrArg Subtype.val hbase) i) j]
    exact RingHom.congr_fun
      (suslinSymbolic_outer_dilation_eval_mul_X c (d ^ N))
      (suslinDifferencePath a g i j)
  change (Matrix.SpecialLinearGroup.map r
        (suslinDilation (Polynomial (Polynomial ℤ))
          (Polynomial.C (Polynomial.C (d ^ N)))
          (suslinDifferencePath (Polynomial.X : Polynomial ℤ)
            (suslinSymbolicLift g))) :
          Matrix.SpecialLinearGroup Index IntegralPolynomial) ∈
      localGlobalElementarySubgroup IntegralPolynomial at hmem
  rw [heval, suslinDifferencePath_eval_mul_X,
    suslinSymbolicDifferenceDilation_integer,
    suslinSymbolicDifferenceDilation_integer] at hmem
  exact hmem

end

section

open Polynomial

universe u v

attribute [local instance] Polynomial.algebra

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem suslin_symbolic_double_denominator
    (d : ℤ)
    (s : ((Submonoid.powers d).map
      (Polynomial.C : ℤ →+* Polynomial ℤ)).map
      (Polynomial.C : Polynomial ℤ →+*
        Polynomial (Polynomial ℤ))) :
    ∃ N : ℕ,
      (s : Polynomial (Polynomial ℤ)) =
        Polynomial.C (Polynomial.C (d ^ N)) := by
  obtain ⟨t, ht, hst⟩ := s.property
  obtain ⟨r, hr, htr⟩ := ht
  obtain ⟨N, hNr⟩ := hr
  change d ^ N = r at hNr
  refine ⟨N, hst.symm.trans ?_⟩
  rw [← htr, ← hNr]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem suslin_uniform_symbolic_differencePath_elementary
    (g : IntegralSpecialLinearGroup) (d : ℤ) (hd : d ≠ 0)
    (hg : suslinAwayElementary g d) :
    ∃ N : ℕ,
      suslinDilation (Polynomial (Polynomial ℤ))
          (Polynomial.C (Polynomial.C (d ^ N)))
          (suslinDifferencePath (Polynomial.X : Polynomial ℤ)
            (Matrix.SpecialLinearGroup.map
              (Polynomial.mapRingHom
                (Polynomial.C : ℤ →+* Polynomial ℤ)) g)) ∈
        localGlobalElementarySubgroup
          (Polynomial (Polynomial (Polynomial ℤ))) := by
  let L := Localization.Away d
  let : CommRing L := inferInstance
  let f : ℤ →+* L := algebraMap ℤ L
  let A₁ := Polynomial ℤ
  let : CommRing A₁ := inferInstance
  let B₁ := Polynomial L
  let : CommRing B₁ := inferInstance
  let f₁ : A₁ →+* B₁ := Polynomial.mapRingHom f
  let A₂ := Polynomial A₁
  let : CommRing A₂ := inferInstance
  let B₂ := Polynomial B₁
  let : CommRing B₂ := inferInstance
  let f₂ : A₂ →+* B₂ := Polynomial.mapRingHom f₁
  let M₀ : Submonoid ℤ := Submonoid.powers d
  let M₁ : Submonoid A₁ := M₀.map (Polynomial.C : ℤ →+* A₁)
  let M₂ : Submonoid A₂ :=
    M₁.map (Polynomial.C : A₁ →+* A₂)
  let : IsLocalization M₁ B₁ :=
    Polynomial.isLocalization M₀ L
  let : IsLocalization M₂ B₂ :=
    Polynomial.isLocalization M₁ B₁
  let gT : Matrix.SpecialLinearGroup Index (Polynomial A₁) :=
    Matrix.SpecialLinearGroup.map
      (Polynomial.mapRingHom (Polynomial.C : ℤ →+* A₁)) g
  have hcomm :
      Matrix.SpecialLinearGroup.map (Polynomial.mapRingHom f₁) gT =
        Matrix.SpecialLinearGroup.map
          (Polynomial.mapRingHom (Polynomial.C : L →+* B₁))
          (Matrix.SpecialLinearGroup.map
            (Polynomial.mapRingHom f) g) := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    change
      Polynomial.map f₁
          (Polynomial.map (Polynomial.C : ℤ →+* A₁) (g i j)) =
        Polynomial.map (Polynomial.C : L →+* B₁)
          (Polynomial.map f (g i j))
    ext n
    simp only [coeff_map, eq_intCast, map_intCast, f₁]
  have hgT :
      Matrix.SpecialLinearGroup.map (Polynomial.mapRingHom f₁) gT ∈
        localGlobalElementarySubgroup (Polynomial B₁) := by
    rw [hcomm]
    apply map_localGlobalElementarySubgroup_le
      (Polynomial.mapRingHom (Polynomial.C : L →+* B₁))
    exact ⟨_, hg, rfl⟩
  let hpath : Matrix.SpecialLinearGroup Index (Polynomial A₂) :=
    suslinDifferencePath (Polynomial.X : A₁) gT
  let hpathB : Matrix.SpecialLinearGroup Index (Polynomial B₂) :=
    Matrix.SpecialLinearGroup.map (Polynomial.mapRingHom f₂) hpath
  have hrel :
      hpathB ∈ localGlobalElementarySubgroup (Polynomial B₂) ∧
        Matrix.SpecialLinearGroup.map
          (Polynomial.evalRingHom (0 : B₂)) hpathB = 1 := by
    exact suslinDifferencePath_relative_elementary_of_baseChange
      f₁ (Polynomial.X : A₁) gT hgT
  obtain ⟨δ, q, hq, heq⟩ :=
    exists_localization_dilated_relative_elementary_word_lift
      M₂ hpathB hrel.1 hrel.2
  obtain ⟨N, hδ⟩ := suslin_symbolic_double_denominator d δ
  have hf : Function.Injective f := by
    apply IsLocalization.injective (M := M₀) L
    intro z hz
    obtain ⟨n, rfl⟩ := hz
    exact mem_nonZeroDivisors_of_ne_zero (pow_ne_zero n hd)
  have hf₁ : Function.Injective f₁ :=
    Polynomial.map_injective f hf
  have hf₂ : Function.Injective f₂ :=
    Polynomial.map_injective f₁ hf₁
  have hf₃ : Function.Injective (Polynomial.mapRingHom f₂) :=
    Polynomial.map_injective f₂ hf₂
  have hSLinj : Function.Injective
      (Matrix.SpecialLinearGroup.map (n := Index)
        (Polynomial.mapRingHom f₂)) := by
    intro x y hxy
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    apply hf₃
    exact congrArg
      (fun z : Matrix.SpecialLinearGroup Index (Polynomial B₂) => z i j)
      hxy
  have hbase :
      Matrix.SpecialLinearGroup.map (Polynomial.mapRingHom f₂)
          (suslinDilation A₂ (δ : A₂) hpath) =
        suslinDilation B₂ (f₂ (δ : A₂)) hpathB := by
    exact suslinPolynomialBaseChange_dilation (δ : A₂) hpath
  have hqeq : q = suslinDilation A₂ (δ : A₂) hpath := by
    apply hSLinj
    exact heq.trans hbase.symm
  refine ⟨N, ?_⟩
  change suslinDilation A₂ (Polynomial.C (Polynomial.C (d ^ N))) hpath ∈
    localGlobalElementarySubgroup (Polynomial A₂)
  rw [← hδ, ← hqeq]
  exact hq

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem suslin_away_elementary_implies_powered_local_increment
    (g : IntegralSpecialLinearGroup) (d : ℤ)
    (hg : suslinAwayElementary g d) :
    ∃ N : ℕ, ∀ a c : ℤ,
      suslinPolynomialDilate (a + c * d ^ N) g *
          (suslinPolynomialDilate a g)⁻¹ ∈
        integralElementarySubgroup := by
  by_cases hd : d = 0
  · subst d
    refine ⟨1, ?_⟩
    intro a c
    simp only [pow_one, mul_zero, add_zero, mul_inv_cancel, one_mem]
  · obtain ⟨N, hpath⟩ :=
      suslin_uniform_symbolic_differencePath_elementary g d hd hg
    refine ⟨N, ?_⟩
    apply suslinSymbolicPoweredIncrement_of_elementary_dilation g d N
    exact hpath

end

section

open scoped BigOperators

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem suslin_augmentation_mem_elementary_of_finite_away_powered_increments
    (g : IntegralSpecialLinearGroup)
    (hg : g ∈ suslinAugmentationKernel)
    (s : Finset ℤ)
    (hspan : Ideal.span (s : Set ℤ) = ⊤)
    (hincrement : ∀ d ∈ s, ∃ N : ℕ, ∀ a c : ℤ,
      suslinPolynomialDilate (a + c * d ^ N) g *
        (suslinPolynomialDilate a g)⁻¹ ∈
          integralElementarySubgroup) :
    g ∈ integralElementarySubgroup := by
  classical
  have hlocal : ∀ d : s, ∃ N : ℕ, ∀ a c : ℤ,
      suslinPolynomialDilate (a + c * (d : ℤ) ^ N) g *
        (suslinPolynomialDilate a g)⁻¹ ∈
          integralElementarySubgroup :=
    fun d => hincrement d d.property
  choose exponent hexponent using hlocal
  let N : ℕ := ∑ d : s, exponent d
  have hle (d : s) : exponent d ≤ N := by
    exact Finset.single_le_sum
      (fun i _ => Nat.zero_le (exponent i)) (Finset.mem_univ d)
  have hrange : Set.range (fun d : s => (d : ℤ)) = (s : Set ℤ) := by
    ext d
    simp
  have hcover : Ideal.span (Set.range (fun d : s => (d : ℤ))) = ⊤ := by
    rw [hrange]
    exact hspan
  obtain ⟨coefficient, hpartition⟩ :=
    exists_powered_partition_of_unity
      (fun d : s => (d : ℤ)) hcover N
  let e : s ≃ Fin (Fintype.card s) := Fintype.equivFin s
  let denominator : Fin (Fintype.card s) → ℤ :=
    fun i => (e.symm i : ℤ)
  let c : Fin (Fintype.card s) → ℤ :=
    fun i => coefficient (e.symm i)
  have hpartitionFin :
      ∑ i : Fin (Fintype.card s), c i * denominator i ^ N = 1 := by
    simpa [c, denominator] using
      (show ∑ i : Fin (Fintype.card s),
        coefficient (e.symm i) * (e.symm i : ℤ) ^ N = 1 from
          (e.symm.sum_comp
            (fun d : s => coefficient d * (d : ℤ) ^ N)).trans hpartition)
  have hlocalFin : ∀ (i : Fin (Fintype.card s)) (a : ℤ),
      suslinPolynomialDilate (a + c i * denominator i ^ N) g *
        (suslinPolynomialDilate a g)⁻¹ ∈
          integralElementarySubgroup := by
    intro i a
    let d : s := e.symm i
    have hpow :
        (d : ℤ) ^ N =
          (d : ℤ) ^ (N - exponent d) * (d : ℤ) ^ exponent d := by
      rw [← pow_add, Nat.sub_add_cancel (hle d)]
    have h := hexponent d a
      (coefficient d * (d : ℤ) ^ (N - exponent d))
    simpa [c, denominator, d, hpow, mul_assoc] using h
  let sn : ℕ → ℤ := fun j =>
    if h : j < Fintype.card s then denominator ⟨j, h⟩ else 0
  let cn : ℕ → ℤ := fun j =>
    if h : j < Fintype.card s then c ⟨j, h⟩ else 0
  have hsn (j : ℕ) (hj : j < Fintype.card s) :
      sn j = denominator ⟨j, hj⟩ := by
    change
      (if h : j < Fintype.card s then denominator ⟨j, h⟩ else 0) =
        denominator ⟨j, hj⟩
    rw [dite_eq_left hj]
  have hcn (j : ℕ) (hj : j < Fintype.card s) :
      cn j = c ⟨j, hj⟩ := by
    change
      (if h : j < Fintype.card s then c ⟨j, h⟩ else 0) =
        c ⟨j, hj⟩
    rw [dite_eq_left hj]
  have hpartitionFin' :
      ∑ i : Fin (Fintype.card s), cn i * sn i ^ N = 1 := by
    calc
      _ = ∑ i : Fin (Fintype.card s),
            c i * denominator i ^ N := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hcn i i.isLt, hsn i i.isLt]
      _ = 1 := hpartitionFin
  have hpartitionNat :
      ∑ j ∈ Finset.range (Fintype.card s), cn j * sn j ^ N = 1 := by
    rw [← Fin.sum_univ_eq_sum_range]
    exact hpartitionFin'
  apply suslin_augmentation_mem_elementary_of_powered_patches
    g hg sn cn (Fintype.card s) N hpartitionNat
  intro j hj
  rw [hsn j hj, hcn j hj]
  exact hlocalFin ⟨j, hj⟩ (suslinPoweredPrefix sn cn N j)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem suslinRelativeElementaryGeneration_of_maximal_away_powered_increments
    (hlocal : ∀ (g : IntegralSpecialLinearGroup),
      g ∈ suslinAugmentationKernel →
        ∀ (m : Ideal ℤ) [m.IsMaximal],
          ∃ d : m.primeCompl, suslinAwayElementary g (d : ℤ))
    (hincrement : ∀ (g : IntegralSpecialLinearGroup),
      g ∈ suslinAugmentationKernel →
        ∀ d : ℤ, suslinAwayElementary g d →
          ∃ N : ℕ, ∀ a c : ℤ,
            suslinPolynomialDilate (a + c * d ^ N) g *
              (suslinPolynomialDilate a g)⁻¹ ∈
                integralElementarySubgroup) :
    SuslinRelativeElementaryGeneration := by
  intro g hg
  obtain ⟨s, hs, hspan⟩ :=
    suslin_exists_finset_denominators_of_primeCompl
      (suslinAwayElementary g) (hlocal g hg)
  apply suslin_augmentation_mem_elementary_of_finite_away_powered_increments
    g hg s hspan
  exact fun d hd => hincrement g hg d (hs d hd)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem suslinRelativeElementaryGeneration_of_maximal_local_powered_increments
    (hlocal : ∀ (g : IntegralSpecialLinearGroup),
      g ∈ suslinAugmentationKernel →
        ∀ (m : Ideal ℤ) [m.IsMaximal],
          Matrix.SpecialLinearGroup.map
            (Polynomial.mapRingHom
              (algebraMap ℤ (Localization.AtPrime m))) g ∈
            localGlobalElementarySubgroup
              (Polynomial (Localization.AtPrime m)))
    (hincrement : ∀ (g : IntegralSpecialLinearGroup),
      g ∈ suslinAugmentationKernel →
        ∀ d : ℤ, suslinAwayElementary g d →
          ∃ N : ℕ, ∀ a c : ℤ,
            suslinPolynomialDilate (a + c * d ^ N) g *
              (suslinPolynomialDilate a g)⁻¹ ∈
                integralElementarySubgroup) :
    SuslinRelativeElementaryGeneration := by
  apply suslinRelativeElementaryGeneration_of_maximal_away_powered_increments
    (hincrement := hincrement)
  intro g hg m inst
  exact suslin_exists_away_elementary_of_atPrime m g (hlocal g hg m)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem suslinRelativeElementaryGeneration_of_maximal_local_elementary
    (hlocal : ∀ (g : IntegralSpecialLinearGroup),
      g ∈ suslinAugmentationKernel →
        ∀ (m : Ideal ℤ) [m.IsMaximal],
          Matrix.SpecialLinearGroup.map
            (Polynomial.mapRingHom
              (algebraMap ℤ (Localization.AtPrime m))) g ∈
            localGlobalElementarySubgroup
              (Polynomial (Localization.AtPrime m))) :
    SuslinRelativeElementaryGeneration :=
  suslinRelativeElementaryGeneration_of_maximal_local_powered_increments
    hlocal
    (fun g _ d hd =>
      suslin_away_elementary_implies_powered_local_increment g d hd)

end

section

open Matrix

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
abbrev cornulierLast : Index := 3

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def cornulierRoot (i j : Index) (h : i ≠ j)
    (a : IntegralPolynomial) : integralElementaryGroup :=
  ⟨Matrix.SpecialLinearGroup.transvection h a,
    Subgroup.subset_closure ⟨i, j, h, a, rfl⟩⟩



/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def cornulierK₁ : Subgroup integralElementaryGroup :=
  Subgroup.closure
    {g | ∃ (i : Index) (h : i ≠ cornulierLast)
      (a : IntegralPolynomial), g = cornulierRoot i cornulierLast h a}

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def cornulierK₂ : Subgroup integralElementaryGroup :=
  Subgroup.closure
    {g | ∃ (j : Index) (h : cornulierLast ≠ j)
      (a : IntegralPolynomial), g = cornulierRoot cornulierLast j h a}

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem cornulierRoot_mem_K₁ (i : Index) (h : i ≠ cornulierLast)
    (a : IntegralPolynomial) :
    cornulierRoot i cornulierLast h a ∈ cornulierK₁ :=
  Subgroup.subset_closure ⟨i, h, a, rfl⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem cornulierRoot_mem_K₂ (j : Index) (h : cornulierLast ≠ j)
    (a : IntegralPolynomial) :
    cornulierRoot cornulierLast j h a ∈ cornulierK₂ :=
  Subgroup.subset_closure ⟨j, h, a, rfl⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem cornulierRoot_mem_K₁_sup_K₂
    (i j : Index) (hij : i ≠ j) (a : IntegralPolynomial) :
    cornulierRoot i j hij a ∈ cornulierK₁ ⊔ cornulierK₂ := by
  by_cases hi : i = cornulierLast
  · subst i
    exact Subgroup.mem_sup_right (cornulierRoot_mem_K₂ j hij a)
  by_cases hj : j = cornulierLast
  · subst j
    exact Subgroup.mem_sup_left (cornulierRoot_mem_K₁ i hij a)
  have hlastj : cornulierLast ≠ j := Ne.symm hj
  let x : integralElementaryGroup := cornulierRoot i cornulierLast hi a
  let y : integralElementaryGroup :=
    cornulierRoot cornulierLast j hlastj (1 : IntegralPolynomial)
  have hx : x ∈ cornulierK₁ ⊔ cornulierK₂ :=
    Subgroup.mem_sup_left (cornulierRoot_mem_K₁ i hi a)
  have hy : y ∈ cornulierK₁ ⊔ cornulierK₂ :=
    Subgroup.mem_sup_right (cornulierRoot_mem_K₂ j hlastj 1)
  have hcomm : x * y * x⁻¹ * y⁻¹ ∈ cornulierK₁ ⊔ cornulierK₂ :=
    (cornulierK₁ ⊔ cornulierK₂).mul_mem
      ((cornulierK₁ ⊔ cornulierK₂).mul_mem
        ((cornulierK₁ ⊔ cornulierK₂).mul_mem hx hy)
        ((cornulierK₁ ⊔ cornulierK₂).inv_mem hx))
      ((cornulierK₁ ⊔ cornulierK₂).inv_mem hy)
  have hroot : x * y * x⁻¹ * y⁻¹ = cornulierRoot i j hij a := by
    apply Subtype.ext
    change
      Matrix.SpecialLinearGroup.transvection hi a *
        Matrix.SpecialLinearGroup.transvection hlastj 1 *
        (Matrix.SpecialLinearGroup.transvection hi a)⁻¹ *
        (Matrix.SpecialLinearGroup.transvection hlastj 1)⁻¹ =
        Matrix.SpecialLinearGroup.transvection hij a
    simpa only [mul_one] using specialLinear_transvection_commutator
      i cornulierLast j hi hlastj hij a 1
  rw [← hroot]
  exact hcomm

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem cornulierK₁_sup_cornulierK₂_eq_top :
    cornulierK₁ ⊔ cornulierK₂ = ⊤ := by
  let S : Subgroup integralElementaryGroup := cornulierK₁ ⊔ cornulierK₂
  have hcover : integralElementarySubgroup ≤
      S.map integralElementarySubgroup.subtype := by
    change Subgroup.closure _ ≤ _
    rw [Subgroup.closure_le]
    rintro _ ⟨i, j, hij, a, rfl⟩
    exact ⟨cornulierRoot i j hij a,
      cornulierRoot_mem_K₁_sup_K₂ i j hij a, rfl⟩
  apply top_unique
  intro g _
  obtain ⟨z, hz, hzg⟩ := hcover g.property
  have heq : z = g := Subtype.ext hzg
  change g ∈ S
  subst z
  exact hz

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def cornulierBlockSubgroup : Subgroup IntegralSpecialLinearGroup where
  carrier :=
    {g | (∀ i : Index,
      g i cornulierLast = if i = cornulierLast then 1 else 0) ∧
      (∀ j : Index,
        g cornulierLast j = if cornulierLast = j then 1 else 0)}
  one_mem' := by
    constructor <;> intro i <;> simp [Matrix.one_apply]
  mul_mem' := by
    rintro g h ⟨hgcol, hgrow⟩ ⟨hhcol, hhrow⟩
    constructor
    · intro i
      change (g.val * h.val) i cornulierLast = _
      simp only [Matrix.mul_apply, hhcol, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, ↓reduceIte, hgcol]
    · intro j
      change (g.val * h.val) cornulierLast j = _
      simp only [Matrix.mul_apply, hgrow, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
        Finset.mem_univ, ↓reduceIte, hhrow]
  inv_mem' := by
    rintro g ⟨hgcol, hgrow⟩
    constructor
    · intro i
      have he := congrArg
        (fun z : IntegralSpecialLinearGroup => z i cornulierLast)
        (inv_mul_cancel g)
      change (g⁻¹).val * g.val |> fun M => M i cornulierLast = _ at he
      simpa only [Matrix.SpecialLinearGroup.coe_inv, Matrix.mul_apply, hgcol, mul_ite, mul_one,
        mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
        Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply] using he
    · intro j
      have he := congrArg
        (fun z : IntegralSpecialLinearGroup => z cornulierLast j)
        (mul_inv_cancel g)
      change (g.val * (g⁻¹).val) cornulierLast j = _ at he
      simpa only [Matrix.SpecialLinearGroup.coe_inv, Matrix.mul_apply, hgrow, ite_mul, one_mul,
        zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, Matrix.SpecialLinearGroup.coe_one,
        Matrix.one_apply] using he

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def cornulierH : Subgroup integralElementaryGroup :=
  cornulierBlockSubgroup.comap integralElementarySubgroup.subtype

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def CornulierBoundedFactorization : Prop :=
  ∀ g : integralElementaryGroup,
    ∃ (x₁ : integralElementaryGroup), x₁ ∈ cornulierK₁ ∧
    ∃ (x₂ : integralElementaryGroup), x₂ ∈ cornulierK₂ ∧
    ∃ (y₁ : integralElementaryGroup), y₁ ∈ cornulierK₁ ∧
    ∃ (b : integralElementaryGroup), b ∈ cornulierH ∧
    ∃ (y₂ : integralElementaryGroup), y₂ ∈ cornulierK₂ ∧
      g = x₁ * x₂ * y₁ * b * y₂

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem cornulier_conjugate_single_apply
    (g : IntegralSpecialLinearGroup)
    (i j p q : Index) (a : IntegralPolynomial) :
    (g.val * Matrix.single i j a * (g⁻¹).val) p q =
      g p i * a * (g⁻¹) j q := by
  simp only [Matrix.SpecialLinearGroup.coe_inv, Matrix.mul_apply, single_apply, ite_and, mul_ite,
    mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, ite_mul, mul_assoc, zero_mul]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem cornulier_conjugate_root_apply
    (g : IntegralSpecialLinearGroup)
    (i j : Index) (hij : i ≠ j) (a : IntegralPolynomial)
    (p q : Index) :
    (g * Matrix.SpecialLinearGroup.transvection hij a * g⁻¹) p q =
      (if p = q then 1 else 0) + g p i * a * (g⁻¹) j q := by
  change
    (g.val * (1 + Matrix.single i j a) * (g⁻¹).val) p q = _
  rw [mul_add, add_mul, Matrix.mul_one]
  have hunit : g.val * (g⁻¹).val = 1 := by
    change ((g * g⁻¹ : IntegralSpecialLinearGroup).val) = _
    simp only [mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  rw [hunit, Matrix.add_apply, Matrix.one_apply,
    cornulier_conjugate_single_apply]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def cornulierColumnRootProduct (v : Index → IntegralPolynomial) :
    integralElementaryGroup :=
  cornulierRoot 0 cornulierLast (by decide) (v 0) *
    cornulierRoot 1 cornulierLast (by decide) (v 1) *
    cornulierRoot 2 cornulierLast (by decide) (v 2)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem cornulierColumnRootProduct_mem (v : Index → IntegralPolynomial) :
    cornulierColumnRootProduct v ∈ cornulierK₁ := by
  exact cornulierK₁.mul_mem
    (cornulierK₁.mul_mem
      (cornulierRoot_mem_K₁ 0 (by decide) (v 0))
      (cornulierRoot_mem_K₁ 1 (by decide) (v 1)))
    (cornulierRoot_mem_K₁ 2 (by decide) (v 2))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem cornulierColumnRootProduct_apply (v : Index → IntegralPolynomial)
    (p q : Index) :
    (cornulierColumnRootProduct v).val p q =
      (if p = q then 1 else 0) +
      if q = cornulierLast then
        if p = cornulierLast then 0 else v p
      else 0 := by
  change
    (Matrix.SpecialLinearGroup.transvection
          (show (0 : Index) ≠ cornulierLast by decide) (v 0) *
        Matrix.SpecialLinearGroup.transvection
          (show (1 : Index) ≠ cornulierLast by decide) (v 1) *
        Matrix.SpecialLinearGroup.transvection
          (show (2 : Index) ≠ cornulierLast by decide) (v 2) :
      IntegralSpecialLinearGroup) p q = _
  fin_cases p <;> fin_cases q <;>
    simp only [cornulierLast, Fin.isValue, Nat.reduceAdd, Fin.zero_eta,
      Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.transvection_coe, Matrix.mul_apply,
      Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, true_and,
      Fin.sum_univ_four, ↓reduceIte, Fin.reduceEq, add_zero, one_ne_zero,
      false_and, mul_ite, mul_one, mul_zero, zero_ne_one, zero_mul, ite_self,
      zero_add, and_false,
      Finset.sum_ite_eq', Finset.mem_univ, Fin.mk_one, Fin.reduceFinMk,
      and_true, ite_mul, one_mul, Finset.sum_ite_eq]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def cornulierRowRootProduct (v : Index → IntegralPolynomial) :
    integralElementaryGroup :=
  cornulierRoot cornulierLast 0 (by decide) (v 0) *
    cornulierRoot cornulierLast 1 (by decide) (v 1) *
    cornulierRoot cornulierLast 2 (by decide) (v 2)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem cornulierRowRootProduct_mem (v : Index → IntegralPolynomial) :
    cornulierRowRootProduct v ∈ cornulierK₂ := by
  exact cornulierK₂.mul_mem
    (cornulierK₂.mul_mem
      (cornulierRoot_mem_K₂ 0 (by decide) (v 0))
      (cornulierRoot_mem_K₂ 1 (by decide) (v 1)))
    (cornulierRoot_mem_K₂ 2 (by decide) (v 2))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem cornulierRowRootProduct_apply (v : Index → IntegralPolynomial)
    (p q : Index) :
    (cornulierRowRootProduct v).val p q =
      (if p = q then 1 else 0) +
      if p = cornulierLast then
        if q = cornulierLast then 0 else v q
      else 0 := by
  change
    (Matrix.SpecialLinearGroup.transvection
          (show cornulierLast ≠ (0 : Index) by decide) (v 0) *
        Matrix.SpecialLinearGroup.transvection
          (show cornulierLast ≠ (1 : Index) by decide) (v 1) *
        Matrix.SpecialLinearGroup.transvection
          (show cornulierLast ≠ (2 : Index) by decide) (v 2) :
      IntegralSpecialLinearGroup) p q = _
  fin_cases p <;> fin_cases q <;>
    simp only [cornulierLast, Fin.isValue, Nat.reduceAdd, Fin.zero_eta,
      Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.transvection_coe, Matrix.mul_apply,
      Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, true_and,
      Fin.sum_univ_four, ↓reduceIte, Fin.reduceEq, add_zero, one_ne_zero,
      false_and, mul_ite, mul_one, mul_zero, zero_ne_one, zero_mul, ite_self,
      zero_add, and_false,
      Finset.sum_ite_eq', Finset.mem_univ, Fin.mk_one, Fin.reduceFinMk,
      and_true, ite_mul, one_mul, Finset.sum_ite_eq]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem cornulier_conjugate_K₁_root_mem
    (h : integralElementaryGroup) (hh : h ∈ cornulierH)
    (i : Index) (hi : i ≠ cornulierLast) (a : IntegralPolynomial) :
    h * cornulierRoot i cornulierLast hi a * h⁻¹ ∈ cornulierK₁ := by
  change h.val ∈ cornulierBlockSubgroup at hh
  have hhinv : h.val⁻¹ ∈ cornulierBlockSubgroup :=
    cornulierBlockSubgroup.inv_mem hh
  let v : Index → IntegralPolynomial := fun p => h.val p i * a
  have heq : h * cornulierRoot i cornulierLast hi a * h⁻¹ =
      cornulierColumnRootProduct v := by
    apply Subtype.ext
    apply Matrix.SpecialLinearGroup.ext
    intro p q
    change
      (h.val * Matrix.SpecialLinearGroup.transvection hi a * h.val⁻¹) p q =
        (cornulierColumnRootProduct v).val p q
    rw [cornulier_conjugate_root_apply h.val i cornulierLast hi a p q,
      cornulierColumnRootProduct_apply]
    by_cases hq : q = cornulierLast
    · subst q
      by_cases hp : p = cornulierLast
      · subst p
        have hzero : h.val cornulierLast i = 0 := by
          simpa only [hi.symm, ↓reduceIte] using hh.2 i
        simp only [↓reduceIte, hzero, zero_mul, hhinv.2 cornulierLast, mul_one, add_zero, v]
      · simp only [hp, ↓reduceIte, hhinv.2 cornulierLast, mul_one, zero_add, v]
    · have hzero : (h.val⁻¹) cornulierLast q = 0 := by
        simpa only [Matrix.SpecialLinearGroup.coe_inv, Ne.symm hq, ↓reduceIte] using hhinv.2 q
      simp only [hzero, mul_zero, add_zero, hq, ↓reduceIte]
  rw [heq]
  exact cornulierColumnRootProduct_mem v

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem cornulier_conjugate_K₂_root_mem
    (h : integralElementaryGroup) (hh : h ∈ cornulierH)
    (j : Index) (hj : cornulierLast ≠ j) (a : IntegralPolynomial) :
    h * cornulierRoot cornulierLast j hj a * h⁻¹ ∈ cornulierK₂ := by
  change h.val ∈ cornulierBlockSubgroup at hh
  have hhinv : h.val⁻¹ ∈ cornulierBlockSubgroup :=
    cornulierBlockSubgroup.inv_mem hh
  let v : Index → IntegralPolynomial := fun q => a * (h.val⁻¹) j q
  have heq : h * cornulierRoot cornulierLast j hj a * h⁻¹ =
      cornulierRowRootProduct v := by
    apply Subtype.ext
    apply Matrix.SpecialLinearGroup.ext
    intro p q
    change
      (h.val * Matrix.SpecialLinearGroup.transvection hj a * h.val⁻¹) p q =
        (cornulierRowRootProduct v).val p q
    rw [cornulier_conjugate_root_apply h.val cornulierLast j hj a p q,
      cornulierRowRootProduct_apply]
    by_cases hp : p = cornulierLast
    · subst p
      by_cases hq : q = cornulierLast
      · subst q
        have hzero : (h.val⁻¹) j cornulierLast = 0 := by
          simpa only [Matrix.SpecialLinearGroup.coe_inv, Ne.symm hj, ↓reduceIte] using hhinv.1 j
        simp only [↓reduceIte, hh.1 cornulierLast, one_mul, hzero, mul_zero, add_zero, v]
      · simp only [hh.1 cornulierLast, ↓reduceIte, one_mul, Matrix.SpecialLinearGroup.coe_inv, hq,
          v]
    · have hzero : h.val p cornulierLast = 0 := by
        simpa only [hp, ↓reduceIte] using hh.1 p
      simp only [hzero, zero_mul, Matrix.SpecialLinearGroup.coe_inv, add_zero, hp, ↓reduceIte]
  rw [heq]
  exact cornulierRowRootProduct_mem v

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem cornulier_conjugate_K₁_mem
    (h : integralElementaryGroup) (hh : h ∈ cornulierH)
    (k : integralElementaryGroup) (hk : k ∈ cornulierK₁) :
    h * k * h⁻¹ ∈ cornulierK₁ := by
  let φ : integralElementaryGroup →* integralElementaryGroup :=
    (MulAut.conj h).toMonoidHom
  have hle : cornulierK₁ ≤ cornulierK₁.comap φ := by
    change Subgroup.closure _ ≤ _
    rw [Subgroup.closure_le]
    rintro _ ⟨i, hi, a, rfl⟩
    change h * cornulierRoot i cornulierLast hi a * h⁻¹ ∈ cornulierK₁
    exact cornulier_conjugate_K₁_root_mem h hh i hi a
  exact hle hk

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem cornulier_conjugate_K₂_mem
    (h : integralElementaryGroup) (hh : h ∈ cornulierH)
    (k : integralElementaryGroup) (hk : k ∈ cornulierK₂) :
    h * k * h⁻¹ ∈ cornulierK₂ := by
  let φ : integralElementaryGroup →* integralElementaryGroup :=
    (MulAut.conj h).toMonoidHom
  have hle : cornulierK₂ ≤ cornulierK₂.comap φ := by
    change Subgroup.closure _ ≤ _
    rw [Subgroup.closure_le]
    rintro _ ⟨j, hj, a, rfl⟩
    change h * cornulierRoot cornulierLast j hj a * h⁻¹ ∈ cornulierK₂
    exact cornulier_conjugate_K₂_root_mem h hh j hj a
  exact hle hk

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem cornulierH_le_normalizer_K₁ :
    cornulierH ≤ Subgroup.normalizer (cornulierK₁ : Set integralElementaryGroup) := by
  intro h hh
  apply Subgroup.mem_normalizer_iff.mpr
  intro k
  constructor
  · exact cornulier_conjugate_K₁_mem h hh k
  · intro hk
    have hback := cornulier_conjugate_K₁_mem h⁻¹
      (cornulierH.inv_mem hh) (h * k * h⁻¹) hk
    simpa only [mul_assoc, inv_mul_cancel_left, inv_inv, inv_mul_cancel, mul_one] using hback

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem cornulierH_le_normalizer_K₂ :
    cornulierH ≤ Subgroup.normalizer (cornulierK₂ : Set integralElementaryGroup) := by
  intro h hh
  apply Subgroup.mem_normalizer_iff.mpr
  intro k
  constructor
  · exact cornulier_conjugate_K₂_mem h hh k
  · intro hk
    have hback := cornulier_conjugate_K₂_mem h⁻¹
      (cornulierH.inv_mem hh) (h * k * h⁻¹) hk
    simpa only [mul_assoc, inv_mul_cancel_left, inv_inv, inv_mul_cancel, mul_one] using hback

end

section

open MonicMatrixElimination
open StabilizedBlockReduction

universe u

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem suslin_stabilizedThreeElementaryGeneration_of_elementaryThreeGeneration
    {R : Type u} [CommRing R]
    (hthree : ∀ b : Matrix.SpecialLinearGroup (Fin 3) R,
      b ∈ elementaryThreeSubgroup R) :
    StabilizedThreeElementaryGeneration R := by
  intro b
  exact lowerBlock_mem_of_elementaryThree b (hthree b)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem
    suslin_stabilizedThreeElementaryGeneration_of_lastColumnTransitivity_and_stabilizedTwo
    {R : Type u} [CommRing R]
    (htrans : ∀ v : Fin 3 → R, UnimodularRow v →
      ∃ e : Matrix.SpecialLinearGroup (Fin 3) R,
        e ∈ elementaryThreeSubgroup R ∧
          e • v = Pi.single (2 : Fin 3) 1)
    (hblock : ∀ b : Matrix.SpecialLinearGroup (Fin 2) R,
      stabilizedTwoHom b ∈ elementaryThreeSubgroup R) :
    StabilizedThreeElementaryGeneration R :=
  suslin_stabilizedThreeElementaryGeneration_of_elementaryThreeGeneration
    (HorrocksValuationInduction.specialLinearThree_mem_of_lastColumnTransitivity_and_stabilizedTwo
      htrans hblock)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem suslin_integer_atPrime_isDiscreteValuationRing
    (p : Ideal ℤ) [p.IsMaximal] :
    IsDiscreteValuationRing (Localization.AtPrime p) := by
  have hp : p ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField
      (inferInstance : p.IsMaximal) Int.not_isField
  exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
    ℤ hp _

end

section

universe u

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem suslin_dvr_polynomial_ringKrullDim
    {A : Type u} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] :
    ringKrullDim (Polynomial A) = 2 := by
  rw [Polynomial.ringKrullDim_of_isNoetherianRing,
    IsPrincipalIdealRing.ringKrullDim_eq_one A
      (IsDiscreteValuationRing.not_isField A)]
  norm_num

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem suslin_dvr_polynomial_stableRangeThree
    {A : Type u} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] :
    BassStableRangeAtMost (Polynomial A) 3 :=
  bassStableRangeThree_of_noetherian_domain_dimension_two
    suslin_dvr_polynomial_ringKrullDim

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem suslin_dvr_stabilizedThreeElementaryGeneration_of_stabilizedTwo
    {A : Type u} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A]
    (hblock : ∀ b : Matrix.SpecialLinearGroup (Fin 2) (Polynomial A),
      StabilizedBlockReduction.stabilizedTwoHom b ∈
        StabilizedBlockReduction.elementaryThreeSubgroup (Polynomial A)) :
    StabilizedBlockReduction.StabilizedThreeElementaryGeneration
      (Polynomial A) :=
  suslin_stabilizedThreeElementaryGeneration_of_lastColumnTransitivity_and_stabilizedTwo
    suslin_valuation_unimodular_three_elementary_reduce hblock

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem suslin_dvr_polynomial_elementary
    {A : Type u} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A]
    (g : Matrix.SpecialLinearGroup (Fin 4) (Polynomial A)) :
    g ∈ localGlobalElementarySubgroup (Polynomial A) := by
  exact suslin_specialLinear_elementary_of_stableRangeThree_of_stabilizedThree
    suslin_dvr_polynomial_stableRangeThree
    (suslin_dvr_stabilizedThreeElementaryGeneration_of_stabilizedTwo
      suslin_dvr_stabilized_two_mem)
    g

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem suslin_atPrime_polynomial_elementary
    (p : Ideal ℤ) [p.IsMaximal]
    (g : Matrix.SpecialLinearGroup (Fin 4)
      (Polynomial (Localization.AtPrime p))) :
    g ∈ localGlobalElementarySubgroup
      (Polynomial (Localization.AtPrime p)) := by
  let : IsDiscreteValuationRing (Localization.AtPrime p) :=
    suslin_integer_atPrime_isDiscreteValuationRing p
  exact suslin_dvr_polynomial_elementary g

end

section

open scoped BigOperators

section MatrixLemmas

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem minkowski_matrix_mul_eq_zero_of_det_ne_zero
    {A B : Matrix ι ι ℤ} (h : A * B = 0) (hdet : B.det ≠ 0) : A = 0 := by
  have hzero : A * (B * B.adjugate) = 0 := by
    rw [← Matrix.mul_assoc, h, Matrix.zero_mul]
  rw [Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one] at hzero
  ext i j
  have hij := congrArg (fun C : Matrix ι ι ℤ => C i j) hzero
  exact (mul_eq_zero.mp hij).resolve_left hdet

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def minkowskiModThree : Matrix ι ι ℤ →+* Matrix ι ι (ZMod 3) :=
  (Int.castRingHom (ZMod 3)).mapMatrix

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem minkowski_det_ne_zero_of_modThree_eq_smul_one
    (A : Matrix ι ι ℤ) (c : ZMod 3) (hc : c ≠ 0)
    (hA : minkowskiModThree A = c • (1 : Matrix ι ι (ZMod 3))) :
    A.det ≠ 0 := by
  intro hzero
  have hmap := (Int.castRingHom (ZMod 3)).map_det A
  rw [hzero, map_zero] at hmap
  change (0 : ZMod 3) = (minkowskiModThree A).det at hmap
  rw [hA, Matrix.det_smul, Matrix.det_one, mul_one] at hmap
  exact pow_ne_zero _ hc hmap.symm

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem minkowski_geom_sum_modThree
    (A : Matrix ι ι ℤ) (hA : minkowskiModThree A = 1) (m : ℕ) :
    minkowskiModThree (∑ i ∈ Finset.range m, A ^ i) =
      (m : ZMod 3) • (1 : Matrix ι ι (ZMod 3)) := by
  simp only [map_sum, map_pow, hA, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    mul_one, Nat.cast_smul_eq_nsmul]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem minkowski_prime_ne_three_modThree
    {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) :
    (p : ZMod 3) ≠ 0 := by
  intro hzero
  have hdvd : 3 ∣ p := (CharP.cast_eq_zero_iff (ZMod 3) 3 p).mp hzero
  exact hp3 ((hp.dvd_iff_eq (by decide : 3 ≠ 1)).mp hdvd)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem minkowski_prime_ne_three_matrix
    (A : Matrix ι ι ℤ) (hA : minkowskiModThree A = 1)
    {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) (hpow : A ^ p = 1) :
    A = 1 := by
  let S : Matrix ι ι ℤ := ∑ i ∈ Finset.range p, A ^ i
  have hzero : (A - 1) * S = 0 := by
    dsimp [S]
    rw [mul_geom_sum, hpow, sub_self]
  have hdet : S.det ≠ 0 :=
    minkowski_det_ne_zero_of_modThree_eq_smul_one S (p : ZMod 3)
      (minkowski_prime_ne_three_modThree hp hp3)
      (minkowski_geom_sum_modThree A hA p)
  exact sub_eq_zero.mp
    (minkowski_matrix_mul_eq_zero_of_det_ne_zero hzero hdet)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem minkowski_exists_sub_one_eq_three_smul
    (A : Matrix ι ι ℤ) (hA : minkowskiModThree A = 1) :
    ∃ B : Matrix ι ι ℤ, A - 1 = (3 : ℤ) • B := by
  have hzero : minkowskiModThree (A - 1) = 0 := by
    simp only [map_sub, hA, map_one, sub_self]
  have hdiv : ∀ i j, (3 : ℤ) ∣ (A - 1) i j := by
    intro i j
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd ((A - 1) i j) 3).mp
    simpa only [Matrix.sub_apply, Int.cast_sub, minkowskiModThree, RingHom.mapMatrix_apply,
      Int.coe_castRingHom, Matrix.map_apply, Matrix.zero_apply] using
      congrArg (fun M : Matrix ι ι (ZMod 3) => M i j) hzero
  choose B hB using hdiv
  refine ⟨B, ?_⟩
  ext i j
  change (A - 1) i j = 3 * B i j
  exact hB i j

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem minkowski_prime_three_matrix
    (A : Matrix ι ι ℤ) (hA : minkowskiModThree A = 1)
    (hpow : A ^ 3 = 1) :
    A = 1 := by
  obtain ⟨B, hB⟩ := minkowski_exists_sub_one_eq_three_smul A hA
  have hAform : A = 1 + (3 : ℤ) • B := by
    rw [← hB]
    simp only [add_sub_cancel]
  let T : Matrix ι ι ℤ := 1 + (3 : ℤ) • B + (3 : ℤ) • (B * B)
  have hgeom : (∑ i ∈ Finset.range 3, A ^ i) = (3 : ℤ) • T := by
    simp only [hAform, zsmul_eq_mul, Int.cast_ofNat, Finset.sum_range_succ, Finset.range_one,
      Finset.sum_singleton, pow_zero, pow_succ, one_mul, smul_add, mul_one, T]
    noncomm_ring
    simp only [zsmul_eq_mul, Int.cast_ofNat, mul_one]
    abel
  have hzero : (A - 1) * T = 0 := by
    have hzero' : (A - 1) * ((3 : ℤ) • T) = 0 := by
      rw [← hgeom, mul_geom_sum, hpow, sub_self]
    rw [Matrix.mul_smul] at hzero'
    ext i j
    have hij := congrArg (fun M : Matrix ι ι ℤ => M i j) hzero'
    exact (mul_eq_zero.mp hij).resolve_left (by norm_num)
  have hT : minkowskiModThree T = 1 := by
    have hthree : (3 : Matrix ι ι (ZMod 3)) = 0 := by
      have hthreeScalar : (3 : ZMod 3) = 0 := ZMod.natCast_self 3
      ext i j
      by_cases hij : i = j <;>
        simp [Matrix.ofNat_apply, hij, hthreeScalar]
    dsimp [T]
    rw [zsmul_eq_mul, zsmul_eq_mul]
    simp only [map_add, map_mul, map_intCast, map_one]
    simp only [Int.cast_ofNat, hthree, zero_mul, add_zero]
  have hdet : T.det ≠ 0 :=
    minkowski_det_ne_zero_of_modThree_eq_smul_one T 1 one_ne_zero
      (by simpa only [one_smul] using hT)
  exact sub_eq_zero.mp
    (minkowski_matrix_mul_eq_zero_of_det_ne_zero hzero hdet)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem minkowski_prime_order_matrix
    (A : Matrix ι ι ℤ)
    (hA : (Int.castRingHom (ZMod 3)).mapMatrix A = 1)
    {p : ℕ} (hp : p.Prime) (hpow : A ^ p = 1) :
    A = 1 := by
  change minkowskiModThree A = 1 at hA
  by_cases hp3 : p = 3
  · subst p
    exact minkowski_prime_three_matrix A hA hpow
  · exact minkowski_prime_ne_three_matrix A hA hp hp3 hpow

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem specialLinear_eq_one_of_modThree_eq_one_of_isOfFinOrder
    (g : Matrix.SpecialLinearGroup ι ℤ)
    (hmod : Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod 3)) g = 1)
    (hfinite : IsOfFinOrder g) : g = 1 := by
  by_contra hg
  have horder_ne_one : orderOf g ≠ 1 := fun h =>
    hg (orderOf_eq_one_iff.mp h)
  let p := (orderOf g).minFac
  have hp : Nat.Prime p := Nat.minFac_prime horder_ne_one
  have hpdiv : p ∣ orderOf g := Nat.minFac_dvd (orderOf g)
  let a : Matrix.SpecialLinearGroup ι ℤ := g ^ (orderOf g / p)
  have haorder : orderOf a = p :=
    orderOf_pow_orderOf_div hfinite.orderOf_pos.ne' hpdiv
  have hane : a ≠ 1 := by
    intro ha
    have hpone : p = 1 := by
      simpa only [ha, orderOf_one] using haorder.symm
    exact hp.ne_one hpone
  have hapow : a ^ p = 1 := by
    rw [← haorder]
    exact pow_orderOf_eq_one a
  have hamod :
      Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod 3)) a = 1 := by
    dsimp [a]
    rw [map_pow, hmod, one_pow]
  have hamatrixmod :
      (Int.castRingHom (ZMod 3)).mapMatrix (a : Matrix ι ι ℤ) = 1 :=
    congrArg
      (fun z : Matrix.SpecialLinearGroup ι (ZMod 3) =>
        (z : Matrix ι ι (ZMod 3))) hamod
  have hamatrixpow : (a : Matrix ι ι ℤ) ^ p = 1 := by
    simpa only [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one] using congrArg
      (fun z : Matrix.SpecialLinearGroup ι ℤ => (z : Matrix ι ι ℤ)) hapow
  have hamatrixone : (a : Matrix ι ι ℤ) = 1 :=
    minkowski_prime_order_matrix (a : Matrix ι ι ℤ)
      hamatrixmod hp hamatrixpow
  apply hane
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  exact congrArg (fun A : Matrix ι ι ℤ => A i j) hamatrixone

end MatrixLemmas

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem levelThreeInteger_torsionFree : LevelThreeIntegerTorsionFree := by
  intro g hg
  apply Subtype.ext
  exact specialLinear_eq_one_of_modThree_eq_one_of_isOfFinOrder
    (g : IntegerSpecialLinearGroup) g.property
    (levelThreeIntegerSubgroup.subtype.isOfFinOrder hg)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem K_no_nontrivial_torsion :
    ∀ g : K, IsOfFinOrder g → g = 1 :=
  K_no_nontrivial_torsion_of_levelThree_torsionFree
    levelThreeInteger_torsionFree

end

section GeneralTransvections

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [CommRing A]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem conjugates_eq_iff_quotient_commutes
    {G : Type*} [Group G] (u v g : G) :
    u * g * u⁻¹ = v * g * v⁻¹ ↔ Commute (v⁻¹ * u) g := by
  constructor
  · intro h
    change (v⁻¹ * u) * g = g * (v⁻¹ * u)
    calc
      (v⁻¹ * u) * g = v⁻¹ * (u * g * u⁻¹) * u := by group
      _ = v⁻¹ * (v * g * v⁻¹) * u := by rw [h]
      _ = g * (v⁻¹ * u) := by group
  · intro h
    change (v⁻¹ * u) * g = g * (v⁻¹ * u) at h
    calc
      u * g * u⁻¹ = v * ((v⁻¹ * u) * g) * u⁻¹ := by group
      _ = v * (g * (v⁻¹ * u)) * u⁻¹ := by rw [h]
      _ = v * g * v⁻¹ := by group

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem transvection_conjugates_eq_iff_commutes
    {i j : ι} (hij : i ≠ j) (a b : A)
    (g : Matrix.SpecialLinearGroup ι A) :
    Matrix.SpecialLinearGroup.transvection hij a * g *
        (Matrix.SpecialLinearGroup.transvection hij a)⁻¹ =
      Matrix.SpecialLinearGroup.transvection hij b * g *
        (Matrix.SpecialLinearGroup.transvection hij b)⁻¹ ↔
      Commute (Matrix.SpecialLinearGroup.transvection hij (a - b)) g := by
  rw [conjugates_eq_iff_quotient_commutes,
    Matrix.SpecialLinearGroup.transvection_inv,
    ← Matrix.SpecialLinearGroup.transvection_add]
  simp only [add_comm, sub_eq_add_neg]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem commute_matrixUnit_of_commute_nonzero_transvection
    [IsDomain A] {i j : ι} (hij : i ≠ j) (a : A) (ha : a ≠ 0)
    (g : Matrix.SpecialLinearGroup ι A)
    (h : Commute (Matrix.SpecialLinearGroup.transvection hij a) g) :
    Commute (Matrix.single i j (1 : A)) (g : Matrix ι ι A) := by
  have hmatrix := congrArg
    (fun u : Matrix.SpecialLinearGroup ι A => (u : Matrix ι ι A)) h.eq
  change ((1 : Matrix ι ι A) + Matrix.single i j a) *
    (g : Matrix ι ι A) = (g : Matrix ι ι A) *
      ((1 : Matrix ι ι A) + Matrix.single i j a) at hmatrix
  have hsingle : Matrix.single i j a * (g : Matrix ι ι A) =
      (g : Matrix ι ι A) * Matrix.single i j a := by
    simpa only [Matrix.add_mul, one_mul, Matrix.mul_add, mul_one, add_right_inj] using hmatrix
  have hrepr : Matrix.single i j a = a • Matrix.single i j (1 : A) := by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [hrepr, Matrix.smul_mul, Matrix.mul_smul] at hsingle
  change Matrix.single i j (1 : A) * (g : Matrix ι ι A) =
    (g : Matrix ι ι A) * Matrix.single i j (1 : A)
  ext k l
  have hentry := congrArg (fun M : Matrix ι ι A => M k l) hsingle
  simpa only [Matrix.smul_apply, smul_eq_mul] using
    (mul_left_cancel₀ ha hentry)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem transvection_conjugates_injective_of_not_commute_matrixUnit
    [IsDomain A] {i j : ι} (hij : i ≠ j)
    (g : Matrix.SpecialLinearGroup ι A)
    (hnot : ¬Commute (Matrix.single i j (1 : A)) (g : Matrix ι ι A)) :
    Function.Injective (fun a : A =>
      Matrix.SpecialLinearGroup.transvection hij a * g *
        (Matrix.SpecialLinearGroup.transvection hij a)⁻¹) := by
  intro a b hab
  by_contra hne
  apply hnot
  apply commute_matrixUnit_of_commute_nonzero_transvection hij (a - b)
    (sub_ne_zero.mpr hne) g
  exact (transvection_conjugates_eq_iff_commutes hij a b g).mp hab

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem scaled_transvection_conjugates_injective
    [IsDomain A] {i j : ι} (hij : i ≠ j)
    (g : Matrix.SpecialLinearGroup ι A)
    (hnot : ¬Commute (Matrix.single i j (1 : A)) (g : Matrix ι ι A))
    (c : A) (hc : c ≠ 0) :
    Function.Injective (fun a : A =>
      Matrix.SpecialLinearGroup.transvection hij (c * a) * g *
        (Matrix.SpecialLinearGroup.transvection hij (c * a))⁻¹) := by
  intro a b hab
  apply mul_left_cancel₀ hc
  exact transvection_conjugates_injective_of_not_commute_matrixUnit
    hij g hnot hab

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem specialLinear_scalar_pow_card_eq_one
    (g : Matrix.SpecialLinearGroup ι A)
    (hscalar : (g : Matrix ι ι A) ∈ Set.range (Matrix.scalar ι)) :
    g ^ Fintype.card ι = 1 := by
  obtain ⟨a, ha⟩ := hscalar
  have hroot : a ^ Fintype.card ι = 1 := by
    simpa only [← ha, Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const,
      Finset.card_univ] using g.property
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  change ((g : Matrix ι ι A) ^ Fintype.card ι) i j =
    (1 : Matrix ι ι A) i j
  rw [← ha, ← map_pow (Matrix.scalar ι), hroot, map_one]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem specialLinear_transvection_injective
    {i j : ι} (hij : i ≠ j) :
    Function.Injective (Matrix.SpecialLinearGroup.transvection hij :
      A → Matrix.SpecialLinearGroup ι A) := by
  intro a b hab
  have hentry := congrArg (fun u : Matrix.SpecialLinearGroup ι A => u i j) hab
  simpa only [Matrix.SpecialLinearGroup.transvection_coe, Matrix.add_apply, ne_eq, hij,
    not_false_eq_true, Matrix.one_apply_ne, Matrix.single_apply_same, zero_add] using hentry

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem specialLinear_subgroup_conjugacy_infinite
    [IsDomain A] [Infinite A] [Nonempty ι]
    (H : Subgroup (Matrix.SpecialLinearGroup ι A))
    (c : A) (hc : c ≠ 0)
    (hmem : ∀ {i j : ι} (hij : i ≠ j) (a : A),
      Matrix.SpecialLinearGroup.transvection hij (c * a) ∈ H)
    (htf : ∀ h : H, IsOfFinOrder h → h = 1)
    (g : H) (hg : g ≠ 1) :
    (Set.range fun h : H => h * g * h⁻¹).Infinite := by
  have hnot_scalar : ¬(g.val : Matrix ι ι A) ∈ Set.range (Matrix.scalar ι) := by
    intro hscalar
    have hpow : g.val ^ Fintype.card ι = 1 :=
      specialLinear_scalar_pow_card_eq_one g.val hscalar
    have hpow' : g ^ Fintype.card ι = 1 := by
      apply Subtype.ext
      exact hpow
    have hcard : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr inferInstance
    exact hg (htf g (isOfFinOrder_iff_pow_eq_one.mpr
      ⟨Fintype.card ι, hcard, hpow'⟩))
  have hnot_all : ¬∀ (i j : ι), i ≠ j →
      Commute (Matrix.single i j (1 : A)) (g.val : Matrix ι ι A) := by
    intro hcomm
    exact hnot_scalar (Matrix.mem_range_scalar_of_commute_single hcomm)
  push Not at hnot_all
  obtain ⟨i, j, hij, hnot⟩ := hnot_all
  let lift (a : A) : H :=
    ⟨Matrix.SpecialLinearGroup.transvection hij (c * a), hmem hij a⟩
  have hinj : Function.Injective (fun a : A => lift a * g * (lift a)⁻¹) := by
    intro a b hab
    apply scaled_transvection_conjugates_injective
      hij g.val hnot c hc
    simpa only [Subgroup.coe_mul, InvMemClass.coe_inv] using congrArg (fun h : H => h.val) hab
  apply (Set.infinite_range_of_injective hinj).mono
  rintro _ ⟨a, rfl⟩
  exact ⟨lift a, rfl⟩

end GeneralTransvections

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem liftedIntegralTransvection_injective
    {i j : Index} (hij : i ≠ j) :
    Function.Injective (liftedIntegralTransvection hij) := by
  intro a b hab
  apply mul_left_cancel₀ (show (3 : IntegralPolynomial) ≠ 0 by norm_num)
  apply specialLinear_transvection_injective hij
  exact congrArg (fun g : K => (g : IntegralSpecialLinearGroup)) hab

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem actingGroup_infinite : Infinite K :=
  Infinite.of_injective
    (liftedIntegralTransvection (show (0 : Index) ≠ 1 by decide))
    (liftedIntegralTransvection_injective (show (0 : Index) ≠ 1 by decide))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem actingGroup_conjugacyClass_infinite (g : K) (hg : g ≠ 1) :
    (ConnesRigidity.conjugacyClass actingGroup g).Infinite := by
  have hclass := specialLinear_subgroup_conjugacy_infinite
    (ι := Index) (A := IntegralPolynomial)
    modThreeGroupHom.ker (3 : IntegralPolynomial) (by norm_num)
    (fun hij a => integralTransvection_mem_KSubgroup hij a)
    K_no_nontrivial_torsion g hg
  apply hclass.mono
  rintro _ ⟨h, rfl⟩
  exact ⟨h, rfl⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem actingGroup_isICC : ConnesRigidity.IsICC actingGroup :=
  ⟨actingGroup_infinite, actingGroup_conjugacyClass_infinite⟩

section

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
abbrev X := V →ₗ[F] F

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
abbrev Y := B →ₗ[F] F

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def tensorFunctional (ℓ ℓ' : X) : T →ₗ[F] F :=
  TensorProduct.lift ((LinearMap.mul F F).compl₁₂ ℓ ℓ')

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem tensorFunctional_tmul (ℓ ℓ' : X) (v w : V) :
    tensorFunctional ℓ ℓ' (v ⊗ₜ[F] w) = ℓ v * ℓ' w := rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def carry (ℓ ℓ' : X) : Y :=
  (tensorFunctional ℓ ℓ').comp B.subtype



/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem carry_apply_diagonal (ℓ ℓ' : X) (v : V) :
    carry ℓ ℓ' (diagonal v) = ℓ v * ℓ' v := rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem tensorFunctional_add_left (ℓ₁ ℓ₂ ℓ' : X) :
    tensorFunctional (ℓ₁ + ℓ₂) ℓ' =
      tensorFunctional ℓ₁ ℓ' + tensorFunctional ℓ₂ ℓ' := by
  apply TensorProduct.ext'
  intro v w
  simp only [tensorFunctional_tmul, LinearMap.add_apply, add_mul]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem tensorFunctional_add_right (ℓ ℓ₁ ℓ₂ : X) :
    tensorFunctional ℓ (ℓ₁ + ℓ₂) =
      tensorFunctional ℓ ℓ₁ + tensorFunctional ℓ ℓ₂ := by
  apply TensorProduct.ext'
  intro v w
  simp only [tensorFunctional_tmul, LinearMap.add_apply, mul_add]





/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem carry_zero_left (ℓ : X) : carry 0 ℓ = 0 := by
  apply LinearMap.ext
  intro w
  change tensorFunctional 0 ℓ (w : T) = 0
  have h : tensorFunctional 0 ℓ = 0 := by
    apply TensorProduct.ext'
    intro v u
    simp only [tensorFunctional_tmul, LinearMap.zero_apply, zero_mul]
  rw [h]
  rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem carry_zero_right (ℓ : X) : carry ℓ 0 = 0 := by
  apply LinearMap.ext
  intro w
  change tensorFunctional ℓ 0 (w : T) = 0
  have h : tensorFunctional ℓ 0 = 0 := by
    apply TensorProduct.ext'
    intro v u
    simp only [tensorFunctional_tmul, LinearMap.zero_apply, mul_zero]
  rw [h]
  rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem carry_add_left (ℓ₁ ℓ₂ ℓ' : X) :
    carry (ℓ₁ + ℓ₂) ℓ' = carry ℓ₁ ℓ' + carry ℓ₂ ℓ' := by
  apply LinearMap.ext
  intro w
  change tensorFunctional (ℓ₁ + ℓ₂) ℓ' (w : T) =
    tensorFunctional ℓ₁ ℓ' (w : T) + tensorFunctional ℓ₂ ℓ' (w : T)
  rw [tensorFunctional_add_left]
  rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem carry_add_right (ℓ ℓ₁ ℓ₂ : X) :
    carry ℓ (ℓ₁ + ℓ₂) = carry ℓ ℓ₁ + carry ℓ ℓ₂ := by
  apply LinearMap.ext
  intro w
  change tensorFunctional ℓ (ℓ₁ + ℓ₂) (w : T) =
    tensorFunctional ℓ ℓ₁ (w : T) + tensorFunctional ℓ ℓ₂ (w : T)
  rw [tensorFunctional_add_right]
  rfl









/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem carry_comm (ℓ ℓ' : X) : carry ℓ ℓ' = carry ℓ' ℓ := by
  apply LinearMap.ext
  rintro ⟨w, hw⟩
  change tensorFunctional ℓ ℓ' w = tensorFunctional ℓ' ℓ w
  change w ∈ Submodule.span F (Set.range square) at hw
  refine Submodule.span_induction
    (p := fun z _ => tensorFunctional ℓ ℓ' z = tensorFunctional ℓ' ℓ z)
    ?_ ?_ ?_ ?_ hw
  · rintro _ ⟨v, rfl⟩
    simp only [square, tensorFunctional_tmul, mul_comm]
  · simp only [map_zero]
  · intro u v _ _ hu hv
    simp only [map_add, hu, hv]
  · intro a v _ hv
    simp only [map_smul, hv]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def shiftVector (n : ℕ) : V →ₗ[F] V :=
  (LinearMap.lsmul R V (Polynomial.X ^ n)).restrictScalars F

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem shiftVector_apply (n : ℕ) (v : V) (i : Fin 4) :
    shiftVector n v i = Polynomial.X ^ n * v i := rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def shift (n : ℕ) : X →ₗ[F] X where
  toFun ℓ := ℓ.comp (shiftVector n)
  map_add' ℓ₁ ℓ₂ := by
    apply LinearMap.ext
    intro v
    rfl
  map_smul' a ℓ := by
    apply LinearMap.ext
    intro v
    rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem shift_apply (n : ℕ) (ℓ : X) (v : V) :
    shift n ℓ v = ℓ (shiftVector n v) := rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem shift_zero (n : ℕ) : shift n 0 = 0 := by
  exact (shift n).map_zero

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem shift_add (n : ℕ) (ℓ ℓ' : X) :
    shift n (ℓ + ℓ') = shift n ℓ + shift n ℓ' := by
  exact (shift n).map_add ℓ ℓ'

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def shiftedCarry (n : ℕ) (ℓ ℓ' : X) : Y :=
  carry (shift n ℓ) (shift n ℓ')

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem shiftedCarry_zero_left (n : ℕ) (ℓ : X) :
    shiftedCarry n 0 ℓ = 0 := by
  simp only [shiftedCarry, shift_zero, carry_zero_left]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem shiftedCarry_zero_right (n : ℕ) (ℓ : X) :
    shiftedCarry n ℓ 0 = 0 := by
  simp only [shiftedCarry, shift_zero, carry_zero_right]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem shiftedCarry_comm (n : ℕ) (ℓ ℓ' : X) :
    shiftedCarry n ℓ ℓ' = shiftedCarry n ℓ' ℓ :=
  carry_comm _ _

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem shiftedCarry_add_left (n : ℕ) (ℓ₁ ℓ₂ ℓ' : X) :
    shiftedCarry n (ℓ₁ + ℓ₂) ℓ' =
      shiftedCarry n ℓ₁ ℓ' + shiftedCarry n ℓ₂ ℓ' := by
  simp only [shiftedCarry, shift_add, carry_add_left]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem shiftedCarry_add_right (n : ℕ) (ℓ ℓ₁ ℓ₂ : X) :
    shiftedCarry n ℓ (ℓ₁ + ℓ₂) =
      shiftedCarry n ℓ ℓ₁ + shiftedCarry n ℓ ℓ₂ := by
  simp only [shiftedCarry, shift_add, carry_add_right]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
structure CarryGroup (_n : ℕ) where
  /-- The linear coordinate. -/
  linear : X
  /-- The quadratic coordinate. -/
  quadratic : Y

namespace CarryGroup

variable {n : ℕ}

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[ext]
public
theorem ext {x y : CarryGroup n}
    (hlinear : x.linear = y.linear)
    (hquadratic : x.quadratic = y.quadratic) : x = y := by
  cases x
  cases y
  simp_all

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
instance : Zero (CarryGroup n) := ⟨⟨0, 0⟩⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
instance : Add (CarryGroup n) where
  add x y :=
    ⟨x.linear + y.linear,
      x.quadratic + y.quadratic + shiftedCarry n x.linear y.linear⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
instance : Neg (CarryGroup n) where
  neg x := ⟨x.linear, x.quadratic + shiftedCarry n x.linear x.linear⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem zero_linear : (0 : CarryGroup n).linear = 0 := rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem zero_quadratic : (0 : CarryGroup n).quadratic = 0 := rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem add_linear (x y : CarryGroup n) :
    (x + y).linear = x.linear + y.linear := rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem add_quadratic (x y : CarryGroup n) :
    (x + y).quadratic =
      x.quadratic + y.quadratic + shiftedCarry n x.linear y.linear := rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem neg_linear (x : CarryGroup n) :
    (-x).linear = x.linear := rfl



/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem add_assoc' (x y z : CarryGroup n) :
    (x + y) + z = x + (y + z) := by
  apply ext
  · exact add_assoc _ _ _
  · simp only [add_quadratic, add_linear]
    rw [shiftedCarry_add_left, shiftedCarry_add_right]
    abel

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem zero_add' (x : CarryGroup n) : 0 + x = x := by
  apply ext
  · simp only [add_linear, zero_linear, zero_add]
  · simp only [add_quadratic, zero_quadratic, zero_add, zero_linear, shiftedCarry_zero_left,
      add_zero]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem neg_add_cancel' (x : CarryGroup n) : -x + x = 0 := by
  apply ext
  · simp only [add_linear, neg_linear, add_self_eq_zero, zero_linear]
  · change (x.quadratic + shiftedCarry n x.linear x.linear) +
        x.quadratic + shiftedCarry n x.linear x.linear = 0
    calc
      _ = (x.quadratic + x.quadratic) +
            (shiftedCarry n x.linear x.linear +
              shiftedCarry n x.linear x.linear) := by abel
      _ = 0 := by rw [add_self_eq_zero, add_self_eq_zero, zero_add]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
instance : AddGroup (CarryGroup n) :=
  AddGroup.ofLeftAxioms add_assoc' zero_add' neg_add_cancel'

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
instance : AddCommGroup (CarryGroup n) :=
  AddCommGroup.mk fun x y ↦ by
    apply ext
    · exact add_comm _ _
    · simp only [add_quadratic]
      rw [shiftedCarry_comm n x.linear y.linear]
      abel

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem two_nsmul_linear (x : CarryGroup n) :
    ((2 : ℕ) • x).linear = 0 := by
  rw [two_nsmul, add_linear, add_self_eq_zero]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem two_nsmul_quadratic (x : CarryGroup n) :
    ((2 : ℕ) • x).quadratic = shiftedCarry n x.linear x.linear := by
  rw [two_nsmul, add_quadratic, add_self_eq_zero, zero_add]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem four_nsmul_eq_zero (x : CarryGroup n) : (4 : ℕ) • x = 0 := by
  change (2 * 2 : ℕ) • x = 0
  rw [mul_nsmul]
  apply ext
  · simp only [two_nsmul_linear, zero_linear]
  · simp only [two_nsmul_quadratic, two_nsmul_linear, shiftedCarry_zero_right, zero_quadratic]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def coefficientFunctional (n : ℕ) : X :=
  (Polynomial.lcoeff F n).comp (LinearMap.proj (R := F) (0 : Fin 4))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem coefficientFunctional_apply (n : ℕ) (v : V) :
    coefficientFunctional n v = (v 0).coeff n := rfl



/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def orderFourElement (n : ℕ) : CarryGroup n :=
  ⟨coefficientFunctional n, 0⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem orderFourElement_linear (n : ℕ) :
    (orderFourElement n).linear = coefficientFunctional n := rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem orderFourElement_quadratic (n : ℕ) :
    (orderFourElement n).quadratic = 0 := rfl

end CarryGroup

end

section


/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[reducible, expose]
public
def pointwiseDualTopology (M : Type*) [AddCommGroup M] [Module F M] :
    TopologicalSpace (M →ₗ[F] F) :=
  TopologicalSpace.induced (fun ℓ : M →ₗ[F] F => (fun m => ℓ m)) inferInstance

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
instance instXTopologicalSpace : TopologicalSpace X := pointwiseDualTopology V

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
instance instYTopologicalSpace : TopologicalSpace Y := pointwiseDualTopology B

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem xClosedEmbedding :
    Topology.IsClosedEmbedding ((↑) : X → V → F) :=
  ⟨Function.Injective.isEmbedding_induced DFunLike.coe_injective,
    LinearMap.isClosed_range_coe V F (RingHom.id F)⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem yClosedEmbedding :
    Topology.IsClosedEmbedding ((↑) : Y → B → F) :=
  ⟨Function.Injective.isEmbedding_induced DFunLike.coe_injective,
    LinearMap.isClosed_range_coe B F (RingHom.id F)⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
instance instXCompactSpace : CompactSpace X := xClosedEmbedding.compactSpace

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
instance instYCompactSpace : CompactSpace Y := yClosedEmbedding.compactSpace

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
instance instXT2Space : T2Space X := xClosedEmbedding.toIsEmbedding.t2Space

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
instance instYT2Space : T2Space Y := yClosedEmbedding.toIsEmbedding.t2Space

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
instance instXSecondCountableTopology : SecondCountableTopology X := by
  let : Countable R :=
    (AddMonoidAlgebra.coeff_injective.comp Polynomial.toFinsupp_injective).countable
  exact xClosedEmbedding.toIsEmbedding.secondCountableTopology

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
instance instYSecondCountableTopology : SecondCountableTopology Y := by
  let : Countable R :=
    (AddMonoidAlgebra.coeff_injective.comp Polynomial.toFinsupp_injective).countable
  let : Countable B := by
    change Countable (Submodule.span F (Set.range square))
    infer_instance
  exact yClosedEmbedding.toIsEmbedding.secondCountableTopology

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem continuous_X_eval (v : V) : Continuous (fun ℓ : X => ℓ v) :=
  (continuous_apply v).comp continuous_induced_dom

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem continuous_Y_eval (w : B) : Continuous (fun q : Y => q w) :=
  (continuous_apply w).comp continuous_induced_dom

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem continuous_X_iff {A : Type*} [TopologicalSpace A] {f : A → X} :
    Continuous f ↔ ∀ v : V, Continuous (fun a => f a v) := by
  rw [continuous_induced_rng, continuous_pi_iff]
  rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem continuous_Y_iff {A : Type*} [TopologicalSpace A] {f : A → Y} :
    Continuous f ↔ ∀ w : B, Continuous (fun a => f a w) := by
  rw [continuous_induced_rng, continuous_pi_iff]
  rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem continuous_X_precomp (f : V →ₗ[F] V) :
    Continuous (fun ℓ : X => ℓ.comp f) :=
  continuous_X_iff.mpr fun v => continuous_X_eval (f v)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem continuous_Y_precomp (f : B →ₗ[F] B) :
    Continuous (fun q : Y => q.comp f) :=
  continuous_Y_iff.mpr fun w => continuous_Y_eval (f w)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
instance instXTopologicalAddGroup : IsTopologicalAddGroup X where
  continuous_add := by
    apply continuous_X_iff.mpr
    intro v
    exact ((continuous_X_eval v).comp continuous_fst).add
      ((continuous_X_eval v).comp continuous_snd)
  continuous_neg := by
    apply continuous_X_iff.mpr
    intro v
    exact (continuous_X_eval v).neg

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
instance instYTopologicalAddGroup : IsTopologicalAddGroup Y where
  continuous_add := by
    apply continuous_Y_iff.mpr
    intro w
    exact ((continuous_Y_eval w).comp continuous_fst).add
      ((continuous_Y_eval w).comp continuous_snd)
  continuous_neg := by
    apply continuous_Y_iff.mpr
    intro w
    exact (continuous_Y_eval w).neg

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem continuous_shift (n : ℕ) : Continuous (shift n : X → X) :=
  continuous_X_precomp (shiftVector n)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def carryCoordinates (n : ℕ) (z : CarryGroup n) : X × Y :=
  (z.linear, z.quadratic)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
instance instCarryGroupTopologicalSpace (n : ℕ) : TopologicalSpace (CarryGroup n) :=
  TopologicalSpace.induced (carryCoordinates n) inferInstance

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def carryHomeomorph (n : ℕ) : CarryGroup n ≃ₜ X × Y where
  toFun := carryCoordinates n
  invFun z := ⟨z.1, z.2⟩
  left_inv z := by cases z; rfl
  right_inv z := by cases z; rfl
  continuous_toFun := continuous_induced_dom
  continuous_invFun := continuous_induced_rng.mpr continuous_id

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem continuous_carryCoordinates (n : ℕ) :
    Continuous (carryCoordinates n) := (carryHomeomorph n).continuous

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem continuous_linear (n : ℕ) :
    Continuous (CarryGroup.linear : CarryGroup n → X) :=
  continuous_fst.comp (continuous_carryCoordinates n)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem continuous_quadratic (n : ℕ) :
    Continuous (CarryGroup.quadratic : CarryGroup n → Y) :=
  continuous_snd.comp (continuous_carryCoordinates n)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem continuous_linear_eval (n : ℕ) (v : V) :
    Continuous (fun z : CarryGroup n => z.linear v) :=
  (continuous_X_eval v).comp (continuous_linear n)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem continuous_quadratic_eval (n : ℕ) (w : B) :
    Continuous (fun z : CarryGroup n => z.quadratic w) :=
  (continuous_Y_eval w).comp (continuous_quadratic n)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem continuous_CarryGroup_iff {A : Type*} [TopologicalSpace A]
    {n : ℕ} {f : A → CarryGroup n} :
    Continuous f ↔
      (∀ v : V, Continuous (fun a => (f a).linear v)) ∧
        (∀ w : B, Continuous (fun a => (f a).quadratic w)) := by
  rw [continuous_induced_rng]
  change Continuous (fun a => ((f a).linear, (f a).quadratic)) ↔ _
  rw [continuous_prodMk]
  exact and_congr continuous_X_iff continuous_Y_iff

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
instance instCarryGroupCompactSpace (n : ℕ) : CompactSpace (CarryGroup n) :=
  (carryHomeomorph n).symm.compactSpace

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
instance instCarryGroupT2Space (n : ℕ) : T2Space (CarryGroup n) :=
  (carryHomeomorph n).isEmbedding.t2Space

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
instance instCarryGroupSecondCountableTopology (n : ℕ) :
    SecondCountableTopology (CarryGroup n) :=
  (carryHomeomorph n).isInducing.secondCountableTopology

end

section

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def binaryRootsEquiv : Multiplicative F ≃* rootsOfUnity 2 Circle :=
  MulEquiv.ofBijective
    (AddChar.toMonoidHomEquiv (ZMod.rootsOfUnityAddChar 2))
    (by simpa only [AddChar.coe_toMonoidHomEquiv,
          EquivLike.bijective_comp] using (bijective_rootsOfUnityAddChar (n := 2)))



/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem binaryRootsEquiv_val (a : Multiplicative F) :
    ((binaryRootsEquiv a).val : Circle) =
      ZMod.toCircle (Multiplicative.toAdd a) := rfl

variable (M : Type*) [AddCommGroup M] [Module F M]
  [TopologicalSpace M]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem character_sq (χ : PontryaginDual (Multiplicative M))
    (x : Multiplicative M) : χ x ^ (2 : ℕ) = 1 := by
  have hx : x ^ (2 : ℕ) = (1 : Multiplicative M) := by
    apply Multiplicative.toAdd.injective
    change (2 : ℕ) • Multiplicative.toAdd x = 0
    simpa only [two_nsmul] using
      (ConnesRigidity.add_self_eq_zero (Multiplicative.toAdd x))
  rw [← map_pow, hx, map_one]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def characterIntoRoots
    (χ : PontryaginDual (Multiplicative M)) :
    Multiplicative M →* rootsOfUnity 2 Circle where
  toFun x := ⟨toUnits (χ x), by
    rw [mem_rootsOfUnity']
    change χ x ^ (2 : ℕ) = 1
    exact character_sq M χ x⟩
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    exact map_one χ
  map_mul' x y := by
    apply Subtype.ext
    apply Units.ext
    exact map_mul χ x y

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def characterAdd
    (χ : PontryaginDual (Multiplicative M)) : M →+ F :=
  { toFun x := Multiplicative.toAdd
      (binaryRootsEquiv.symm
        (characterIntoRoots M χ (Multiplicative.ofAdd x)))
    map_zero' := by
      change Multiplicative.toAdd
        (binaryRootsEquiv.symm (characterIntoRoots M χ 1)) = 0
      rw [map_one, map_one]
      rfl
    map_add' x y := by
      change Multiplicative.toAdd
          (binaryRootsEquiv.symm
            (characterIntoRoots M χ
              (Multiplicative.ofAdd x * Multiplicative.ofAdd y))) = _
      rw [map_mul, map_mul]
      rfl }

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def characterLinear
    (χ : PontryaginDual (Multiplicative M)) : M →ₗ[F] F :=
  (characterAdd M χ).toZModLinearMap 2

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
public
theorem characterLinear_circle
    (χ : PontryaginDual (Multiplicative M)) (x : M) :
    ZMod.toCircle (characterLinear M χ x) =
      χ (Multiplicative.ofAdd x) := by
  have h := binaryRootsEquiv.apply_symm_apply
    (characterIntoRoots M χ (Multiplicative.ofAdd x))
  change ZMod.toCircle (Multiplicative.toAdd
    (binaryRootsEquiv.symm
      (characterIntoRoots M χ (Multiplicative.ofAdd x)))) =
      χ (Multiplicative.ofAdd x)
  calc
    _ = ((characterIntoRoots M χ
      (Multiplicative.ofAdd x)).val : Circle) := by
      simpa only [binaryRootsEquiv_val] using
        congrArg (fun z : rootsOfUnity 2 Circle => (z.val : Circle)) h
    _ = _ := rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem continuous_characterLinear
    (χ : PontryaginDual (Multiplicative M)) :
    Continuous (characterLinear M χ) := by
  rw [continuous_def]
  intro s _
  classical
  have hopen (a : F) :
      IsOpen {x : M | characterLinear M χ x = a} := by
    have hcircle : Continuous (fun x : M =>
        χ (Multiplicative.ofAdd x)) := χ.continuous
    have hpre : IsOpen {x : M |
        χ (Multiplicative.ofAdd x) ≠ ZMod.toCircle (a + 1)} :=
      isOpen_ne.preimage hcircle
    convert hpre using 1
    ext x
    simp only [Set.mem_ofPred_eq]
    rw [← characterLinear_circle M χ x]
    rw [ZMod.injective_toCircle.ne_iff]
    exact (show ∀ a b : F, b = a ↔ b ≠ a + 1 from by decide)
      a (characterLinear M χ x)
  have hs : (characterLinear M χ : M → F) ⁻¹' s =
      ⋃ a ∈ s, {x : M | characterLinear M χ x = a} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop, exists_eq_right']
  rw [hs]
  apply isOpen_iUnion
  intro a
  exact isOpen_iUnion fun _ => by
    simpa only using hopen a

end

section


/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem continuous_binaryDual_eq_evaluation
    (M : Type*) [AddCommGroup M] [Module F M]
    (φ : (M →ₗ[F] F) →ₗ[F] F)
    (hφ : @Continuous (M →ₗ[F] F) F
      (pointwiseDualTopology M) inferInstance φ) :
    ∃ m : M, ∀ ℓ : M →ₗ[F] F, φ ℓ = ℓ m := by
  let : TopologicalSpace (M →ₗ[F] F) := pointwiseDualTopology M
  have hzeroOpen : IsOpen ({0} : Set F) := isOpen_discrete _
  have hkerOpen : IsOpen {ℓ : M →ₗ[F] F | φ ℓ = 0} :=
    hzeroOpen.preimage hφ
  have hkerOpen' :
      @IsOpen (M →ₗ[F] F) (pointwiseDualTopology M)
        {ℓ : M →ₗ[F] F | φ ℓ = 0} := hkerOpen
  obtain ⟨U, hU, hpre⟩ := isOpen_induced_iff.mp hkerOpen'
  have hzeroU : (0 : M → F) ∈ U := by
    have h : (0 : M →ₗ[F] F) ∈ {ℓ : M →ₗ[F] F | φ ℓ = 0} := by
      simp only [Set.mem_ofPred_eq, map_zero]
    rw [← hpre] at h
    exact h
  obtain ⟨I, u, hu, hsubset⟩ := (isOpen_pi_iff.mp hU) 0 hzeroU
  have hzeroCoord : ∀ i ∈ I, (0 : F) ∈ u i := by
    intro i hi
    simpa only [Pi.zero_apply] using (hu i hi).2
  have hkernels :
      (⨅ i : {i // i ∈ I}, (Module.Dual.eval F M i.1).ker) ≤ φ.ker := by
    intro ℓ hℓ
    have hv : ∀ i ∈ I, ℓ i = 0 := by
      intro i hi
      have hi' :=
        (Submodule.mem_iInf
          (fun i : {i // i ∈ I} => (Module.Dual.eval F M i.1).ker)).mp hℓ
          (⟨i, hi⟩ : {i // i ∈ I})
      exact LinearMap.mem_ker.mp hi'
    have hcylinder : (fun m => ℓ m) ∈ (I : Set M).pi u := by
      intro i hi
      have hi' : i ∈ I := Finset.mem_coe.mp hi
      change ℓ i ∈ u i
      rw [hv i hi']
      exact hzeroCoord i hi'
    apply LinearMap.mem_ker.mpr
    have hmem : ℓ ∈ {f : M →ₗ[F] F | φ f = 0} := by
      rw [← hpre]
      exact hsubset hcylinder
    exact hmem
  have hspan :
      φ ∈ Submodule.span F (Set.range fun i : {i // i ∈ I} =>
        Module.Dual.eval F M i.1) :=
    mem_span_of_iInf_ker_le_ker hkernels
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp hspan
  refine ⟨∑ i, c i • i.1, ?_⟩
  intro ℓ
  rw [← hc]
  simp only [Finset.univ_eq_attach, LinearMap.coe_sum, LinearMap.coe_smul, Finset.sum_apply,
    Pi.smul_apply, Module.Dual.eval_apply, smul_eq_mul, map_sum, map_smul]











section EvaluationCharacters

variable (M : Type*) [AddCommGroup M] [Module F M]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
local instance instPointwiseBinaryDualTopology : TopologicalSpace (M →ₗ[F] F) :=
  pointwiseDualTopology M

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def pointwiseEvaluationCharacter (m : M) :
    PontryaginDual (Multiplicative (M →ₗ[F] F)) where
  toMonoidHom :=
    (AddChar.toMonoidHomEquiv (ZMod.toCircle : AddChar F Circle)).comp
      (Module.Dual.eval F M m).toAddMonoidHom.toMultiplicative
  continuous_toFun := by
    change Continuous
      (fun ℓ : M →ₗ[F] F ↦ ZMod.toCircle (ℓ m))
    exact continuous_of_discreteTopology.comp
      ((continuous_apply m).comp continuous_induced_dom)



/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def pointwiseEvaluationHom :
    M →+ Additive (PontryaginDual (Multiplicative (M →ₗ[F] F))) where
  toFun m := Additive.ofMul (pointwiseEvaluationCharacter M m)
  map_zero' := by
    apply Additive.toMul.injective
    apply PontryaginDual.ext
    intro ℓ
    change ZMod.toCircle ((Multiplicative.toAdd ℓ) 0) = 1
    simp only [map_zero, AddChar.map_zero_eq_one]
  map_add' m n := by
    apply Additive.toMul.injective
    apply PontryaginDual.ext
    intro ℓ
    change ZMod.toCircle ((Multiplicative.toAdd ℓ) (m + n)) =
      ZMod.toCircle ((Multiplicative.toAdd ℓ) m) *
        ZMod.toCircle ((Multiplicative.toAdd ℓ) n)
    rw [map_add, AddChar.map_add_eq_mul]



/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def pointwisePontryaginDualEquiv :
    Additive (PontryaginDual (Multiplicative (M →ₗ[F] F))) ≃+ M := by
  refine (AddEquiv.ofBijective (pointwiseEvaluationHom M) ⟨?_, ?_⟩).symm
  · intro m n h
    apply Module.eval_apply_injective F
    apply LinearMap.ext
    intro ℓ
    change ℓ m = ℓ n
    apply ZMod.injective_toCircle
    exact DFunLike.congr_fun (congrArg Additive.toMul h)
      (Multiplicative.ofAdd ℓ)
  · intro χ
    obtain ⟨m, hm⟩ := continuous_binaryDual_eq_evaluation M
      (characterLinear (M →ₗ[F] F) (Additive.toMul χ))
      (continuous_characterLinear (M →ₗ[F] F) (Additive.toMul χ))
    refine ⟨m, ?_⟩
    apply Additive.toMul.injective
    apply PontryaginDual.ext
    intro ℓ
    change ZMod.toCircle ((Multiplicative.toAdd ℓ) m) =
      Additive.toMul χ ℓ
    rw [← hm (Multiplicative.toAdd ℓ)]
    exact characterLinear_circle (M →ₗ[F] F)
      (Additive.toMul χ) (Multiplicative.toAdd ℓ)



/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem pointwisePontryaginDualEquiv_apply_character
    (χ : Additive (PontryaginDual (Multiplicative (M →ₗ[F] F))))
    (ℓ : M →ₗ[F] F) :
    ZMod.toCircle (ℓ (pointwisePontryaginDualEquiv M χ)) =
      Additive.toMul χ (Multiplicative.ofAdd ℓ) := by
  have h := (pointwisePontryaginDualEquiv M).symm_apply_apply χ
  have hpoint := DFunLike.congr_fun (congrArg Additive.toMul h)
    (Multiplicative.ofAdd ℓ)
  exact hpoint

end EvaluationCharacters

end

section

namespace FiniteCarry

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
abbrev Bit := ZMod 2



/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def carry (x x' : Bit) : Bit := x * x'

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem carry_zero_left (x : Bit) : carry 0 x = 0 := by
  simp only [carry, zero_mul]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem carry_zero_right (x : Bit) : carry x 0 = 0 := by
  simp only [carry, mul_zero]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem carry_comm (x y : Bit) : carry x y = carry y x := by
  simp only [carry, mul_comm]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem carry_add_left (x y z : Bit) :
    carry (x + y) z = carry x z + carry y z := by
  simp only [carry, add_mul]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem carry_add_right (x y z : Bit) :
    carry x (y + z) = carry x y + carry x z := by
  simp only [carry, mul_add]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def liftBit (x : Bit) : ZMod 4 := (x.val : ZMod 4)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem liftBit_zero : liftBit 0 = 0 := by decide

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem liftBit_one : liftBit 1 = 1 := by decide

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[ext]
public
structure Carry where
  /-- The low carry bit. -/
  low : Bit
  /-- The high carry bit. -/
  high : Bit
deriving DecidableEq, Fintype

namespace Carry

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
instance : Add Carry where
  add p q := ⟨p.low + q.low, p.high + q.high + carry p.low q.low⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
instance : Zero Carry := ⟨⟨0, 0⟩⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
instance : Neg Carry where
  neg p := ⟨p.low, p.high + p.low⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
instance : AddCommGroup Carry where
  add_assoc := by decide
  zero_add := by decide
  add_zero := by decide
  neg_add_cancel := by decide
  add_comm := by decide
  nsmul := nsmulRec
  zsmul := zsmulRec





/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem add_low (p q : Carry) :
    (p + q).low = p.low + q.low := rfl











/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def code (p : Carry) : ZMod 4 :=
  liftBit p.low + 2 * liftBit p.high

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def decode (z : ZMod 4) : Carry :=
  ⟨(z.val % 2 : ℕ), (z.val / 2 : ℕ)⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def codeEquiv : Carry ≃+ ZMod 4 where
  toFun := code
  invFun := decode
  left_inv := by decide
  right_inv := by decide
  map_add' := by decide





/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem exponent_four : ∀ p : Carry, 4 • p = 0 := by decide

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
public
theorem card : Fintype.card Carry = 4 := by decide

end Carry

end FiniteCarry

end

section

namespace CarryGroup

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def pointEvaluation (n : ℕ) (v : V) : CarryGroup n →+ FiniteCarry.Carry where
  toFun x := ⟨shift n x.linear v, x.quadratic (diagonal v)⟩
  map_zero' := by
    apply FiniteCarry.Carry.ext <;> rfl
  map_add' x y := by
    apply FiniteCarry.Carry.ext
    · simp only [add_linear, shift_add, LinearMap.add_apply, shift_apply, FiniteCarry.Carry.add_low]
    · change (x.quadratic + y.quadratic +
          shiftedCarry n x.linear y.linear) (diagonal v) =
        x.quadratic (diagonal v) + y.quadratic (diagonal v) +
          FiniteCarry.carry (shift n x.linear v) (shift n y.linear v)
      change x.quadratic (diagonal v) + y.quadratic (diagonal v) +
          shiftedCarry n x.linear y.linear (diagonal v) =
        x.quadratic (diagonal v) + y.quadratic (diagonal v) +
          (shift n x.linear v * shift n y.linear v)
      congr 1





/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def evalFour (n : ℕ) (v : V) : CarryGroup n →+ ZMod 4 :=
  FiniteCarry.Carry.codeEquiv.toAddMonoidHom.comp (pointEvaluation n v)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
public
theorem evalFour_apply (n : ℕ) (v : V) (x : CarryGroup n) :
    evalFour n v x =
      FiniteCarry.liftBit (shift n x.linear v) +
        2 * FiniteCarry.liftBit (x.quadratic (diagonal v)) := rfl



end CarryGroup

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem continuous_shiftedCarry_linear_pair_apply (n : ℕ) (b : B) :
    Continuous (fun z : CarryGroup n × CarryGroup n =>
      shiftedCarry n z.1.linear z.2.linear b) := by
  rcases b with ⟨w, hw⟩
  change Continuous
    (fun z : CarryGroup n × CarryGroup n =>
      tensorFunctional (shift n z.1.linear) (shift n z.2.linear) w)
  change w ∈ Submodule.span F (Set.range square) at hw
  refine Submodule.span_induction
    (p := fun u _ => Continuous
      (fun z : CarryGroup n × CarryGroup n =>
        tensorFunctional (shift n z.1.linear) (shift n z.2.linear) u))
    ?_ ?_ ?_ ?_ hw
  · rintro _ ⟨v, rfl⟩
    change Continuous (fun z : CarryGroup n × CarryGroup n =>
      z.1.linear (shiftVector n v) * z.2.linear (shiftVector n v))
    exact ((continuous_linear_eval n (shiftVector n v)).comp continuous_fst).mul
      ((continuous_linear_eval n (shiftVector n v)).comp continuous_snd)
  · simpa only [map_zero] using
      (continuous_const : Continuous (fun _ : CarryGroup n × CarryGroup n => (0 : F)))
  · intro u v _ _ hu hv
    simp_rw [map_add]
    convert hu.add hv using 1
    all_goals rfl
  · intro a v _ hv
    simp_rw [map_smul, smul_eq_mul]
    convert (continuous_const : Continuous
      (fun _ : CarryGroup n × CarryGroup n => a)).mul hv using 1
    all_goals rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem continuous_shiftedCarry_linear_self_apply (n : ℕ) (b : B) :
    Continuous (fun z : CarryGroup n => shiftedCarry n z.linear z.linear b) := by
  rcases b with ⟨w, hw⟩
  change Continuous
    (fun z : CarryGroup n => tensorFunctional (shift n z.linear) (shift n z.linear) w)
  change w ∈ Submodule.span F (Set.range square) at hw
  refine Submodule.span_induction
    (p := fun u _ => Continuous
      (fun z : CarryGroup n => tensorFunctional (shift n z.linear) (shift n z.linear) u))
    ?_ ?_ ?_ ?_ hw
  · rintro _ ⟨v, rfl⟩
    change Continuous (fun z : CarryGroup n =>
      z.linear (shiftVector n v) * z.linear (shiftVector n v))
    exact (continuous_linear_eval n (shiftVector n v)).mul
      (continuous_linear_eval n (shiftVector n v))
  · simpa only [map_zero] using
      (continuous_const : Continuous (fun _ : CarryGroup n => (0 : F)))
  · intro u v _ _ hu hv
    simp_rw [map_add]
    convert hu.add hv using 1
    all_goals rfl
  · intro a v _ hv
    simp_rw [map_smul, smul_eq_mul]
    convert (continuous_const : Continuous (fun _ : CarryGroup n => a)).mul hv using 1
    all_goals rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
instance instCarryGroupContinuousAdd (n : ℕ) :
    ContinuousAdd (CarryGroup n) where
  continuous_add := by
    apply continuous_CarryGroup_iff.mpr
    constructor
    · intro v
      change Continuous (fun z : CarryGroup n × CarryGroup n =>
        z.1.linear v + z.2.linear v)
      exact ((continuous_linear_eval n v).comp continuous_fst).add
        ((continuous_linear_eval n v).comp continuous_snd)
    · intro b
      change Continuous (fun z : CarryGroup n × CarryGroup n =>
        z.1.quadratic b + z.2.quadratic b +
          shiftedCarry n z.1.linear z.2.linear b)
      exact (((continuous_quadratic_eval n b).comp continuous_fst).add
        ((continuous_quadratic_eval n b).comp continuous_snd)).add
          (continuous_shiftedCarry_linear_pair_apply n b)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
instance instCarryGroupContinuousNeg (n : ℕ) :
    ContinuousNeg (CarryGroup n) where
  continuous_neg := by
    apply continuous_CarryGroup_iff.mpr
    constructor
    · intro v
      change Continuous (fun z : CarryGroup n => z.linear v)
      exact continuous_linear_eval n v
    · intro b
      change Continuous (fun z : CarryGroup n =>
        z.quadratic b + shiftedCarry n z.linear z.linear b)
      exact (continuous_quadratic_eval n b).add
        (continuous_shiftedCarry_linear_self_apply n b)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
instance instCarryGroupTopologicalAddGroup (n : ℕ) :
    IsTopologicalAddGroup (CarryGroup n) where
  continuous_add := continuous_add
  continuous_neg := continuous_neg

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
abbrev E (n : ℕ) :=
  Additive (PontryaginDual (Multiplicative (CarryGroup n)))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def fourthRootAddCharacter : AddChar (ZMod 4) Circle :=
  ZMod.toCircle

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def fourthRootMonoidCharacter : Multiplicative (ZMod 4) →* Circle :=
  AddChar.toMonoidHomEquiv fourthRootAddCharacter

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def fourthRootCharacter : PontryaginDual (Multiplicative (ZMod 4)) where
  toMonoidHom := fourthRootMonoidCharacter
  continuous_toFun := continuous_of_discreteTopology





/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem fourthRootCharacter_injective :
    Function.Injective fourthRootCharacter := by
  intro a b hab
  apply Multiplicative.toAdd.injective
  apply ZMod.injective_toCircle
  exact hab

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem pontryaginDual_mul_apply {A : Type*} [Monoid A]
    [TopologicalSpace A] (φ ψ : PontryaginDual A) (a : A) :
    (φ * ψ) a = φ a * ψ a := by
  rfl



/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem pontryaginDual_pow_apply {A : Type*} [Monoid A]
    [TopologicalSpace A] (φ : PontryaginDual A) (m : ℕ) (a : A) :
    (φ ^ m) a = (φ a) ^ m := by
  induction m with
  | zero => simp only [pow_zero, PontryaginDual.one_apply]
  | succ m ih => simp only [pow_succ, pontryaginDual_mul_apply, ih]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem E_four_nsmul (n : ℕ) (η : E n) : 4 • η = 0 := by
  change (Additive.toMul η) ^ 4 = 1
  apply PontryaginDual.ext
  intro z
  have hz : z ^ 4 = (1 : Multiplicative (CarryGroup n)) := by
    apply Multiplicative.toAdd.injective
    change 4 • Multiplicative.toAdd z = 0
    exact CarryGroup.four_nsmul_eq_zero (Multiplicative.toAdd z)
  simpa only [pontryaginDual_pow_apply, PontryaginDual.one_apply, map_pow, map_one] using congrArg
    (fun w : Multiplicative (CarryGroup n) => (Additive.toMul η) w) hz

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem continuous_evalFour (n : ℕ) (v : V) :
    Continuous (CarryGroup.evalFour n v : CarryGroup n → ZMod 4) := by
  have hlift : Continuous (FiniteCarry.liftBit : F → ZMod 4) :=
    continuous_of_discreteTopology
  have hlinear :
      Continuous (fun z : CarryGroup n =>
        FiniteCarry.liftBit (shift n z.linear v)) := by
    exact hlift.comp (continuous_linear_eval n (shiftVector n v))
  have hquadratic :
      Continuous (fun z : CarryGroup n =>
        FiniteCarry.liftBit (z.quadratic (diagonal v))) :=
    hlift.comp (continuous_quadratic_eval n (diagonal v))
  exact (hlinear.add (continuous_const.mul hquadratic)).congr
    (fun z => (CarryGroup.evalFour_apply n v z).symm)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def evalFourContinuous (n : ℕ) (v : V) :
    Multiplicative (CarryGroup n) →ₜ* Multiplicative (ZMod 4) where
  toMonoidHom := (CarryGroup.evalFour n v).toMultiplicative
  continuous_toFun := continuous_evalFour n v



/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def fourthRootCharacter.comp {A : Type*} [AddMonoid A] [TopologicalSpace A]
    (f : Multiplicative A →ₜ* Multiplicative (ZMod 4)) :
    PontryaginDual (Multiplicative A) :=
  PontryaginDual.map f fourthRootCharacter

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
public
theorem fourthRootCharacter.comp_apply
    {A : Type*} [AddMonoid A] [TopologicalSpace A]
    (f : Multiplicative A →ₜ* Multiplicative (ZMod 4))
    (a : Multiplicative A) :
    fourthRootCharacter.comp f a = fourthRootCharacter (f a) := rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem fourthRootCharacter_comp_sq_ne_one_of_apply
    {A : Type*} [AddMonoid A] [TopologicalSpace A]
    (f : Multiplicative A →ₜ* Multiplicative (ZMod 4))
    (a : Multiplicative A)
    (ha : Multiplicative.toAdd (f a) + Multiplicative.toAdd (f a) ≠
      (0 : ZMod 4)) :
    (fourthRootCharacter.comp f) ^ 2 ≠ 1 := by
  intro h
  have hpoint := DFunLike.congr_fun h a
  have hpoint' :
      fourthRootCharacter (f a) * fourthRootCharacter (f a) = 1 := by
    simpa only [pow_two, pontryaginDual_mul_apply, fourthRootCharacter.comp_apply,
      PontryaginDual.one_apply] using hpoint
  have hroot :
      fourthRootCharacter (f a * f a) =
        fourthRootCharacter (1 : Multiplicative (ZMod 4)) := by
    simpa only [map_mul, map_one] using hpoint'
  have heq := fourthRootCharacter_injective hroot
  exact ha (congrArg Multiplicative.toAdd heq)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def epsilon (n : ℕ) (v : V) : E n :=
  Additive.ofMul (fourthRootCharacter.comp (evalFourContinuous n v))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
public
theorem epsilon_apply (n : ℕ) (v : V) (z : CarryGroup n) :
    Additive.toMul (epsilon n v) (Multiplicative.ofAdd z) =
      ZMod.toCircle (CarryGroup.evalFour n v z) := rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem epsilon_two_nsmul_ne_zero (n : ℕ) :
    2 • epsilon n e ≠ 0 := by
  change (fourthRootCharacter.comp (evalFourContinuous n e)) ^ 2 ≠ 1
  apply fourthRootCharacter_comp_sq_ne_one_of_apply
    (evalFourContinuous n e)
    (Multiplicative.ofAdd (CarryGroup.orderFourElement n))
  change
    CarryGroup.evalFour n e (CarryGroup.orderFourElement n) +
      CarryGroup.evalFour n e (CarryGroup.orderFourElement n) ≠
      (0 : ZMod 4)
  simpa only [CarryGroup.evalFour_apply, CarryGroup.orderFourElement_linear, shift_apply,
    CarryGroup.coefficientFunctional_apply, Fin.isValue, shiftVector_apply, e_apply, ↓reduceIte,
    mul_one, Polynomial.coeff_X_pow, FiniteCarry.liftBit_one, CarryGroup.orderFourElement_quadratic,
    LinearMap.zero_apply, FiniteCarry.liftBit_zero, mul_zero, add_zero, ne_eq] using
    (by decide : (1 : ZMod 4) + (1 : ZMod 4) ≠ 0)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem epsilon_addOrderOf (n : ℕ) :
    addOrderOf (epsilon n e) = 4 := by
  exact addOrderOf_eq_prime_pow (p := 2) (n := 1)
    (by simpa only [pow_one, ne_eq] using epsilon_two_nsmul_ne_zero n)
    (by simpa only [Nat.reduceAdd, Nat.reducePow] using E_four_nsmul n (epsilon n e))

section GeneralPontryaginDual

variable (A : Type*) [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem pontryaginDual_countable [CompactSpace A]
    [SecondCountableTopology A] : Countable (PontryaginDual A) := by
  let : SecondCountableTopology C(A, Circle) := inferInstance
  let : SecondCountableTopology (PontryaginDual A) :=
    (ContinuousMonoidHom.isEmbedding_toContinuousMap A Circle).secondCountableTopology
  exact (TopologicalSpace.separableSpace_iff_countable).mp inferInstance

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def dualAut (e : A ≃ₜ* A) : MulAut (PontryaginDual A) where
  toFun χ := PontryaginDual.map (e.symm : A →ₜ* A) χ
  invFun χ := PontryaginDual.map (e : A →ₜ* A) χ
  left_inv χ := by
    ext a
    simp only [PontryaginDual.map_apply, ContinuousMonoidHom.coe_coe,
      ContinuousMulEquiv.symm_apply_apply]
  right_inv χ := by
    ext a
    simp only [PontryaginDual.map_apply, ContinuousMonoidHom.coe_coe,
      ContinuousMulEquiv.apply_symm_apply]
  map_mul' χ ψ := by
    ext a
    rfl

variable (K : Type*) [Group K]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def continuousAutOfAction (ρ : K →* MulAut A)
    (hcont : ∀ k : K, Continuous (ρ k : A → A)) (k : K) : A ≃ₜ* A where
  __ := ρ k
  continuous_toFun := hcont k
  continuous_invFun := by
    exact (hcont k⁻¹).congr (fun a => by
      change ρ k⁻¹ a = (ρ k).symm a
      rw [map_inv, MulAut.inv_apply])

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def dualAction (ρ : K →* MulAut A)
    (hcont : ∀ k : K, Continuous (ρ k : A → A)) :
    K →* MulAut (PontryaginDual A) where
  toFun k := dualAut A (continuousAutOfAction A K ρ hcont k)
  map_one' := by
    apply MulEquiv.ext
    intro χ
    apply PontryaginDual.ext
    intro a
    change χ ((ρ 1)⁻¹ a) = χ a
    simp only [map_one, inv_one, MulAut.one_apply]
  map_mul' k h := by
    apply MulEquiv.ext
    intro χ
    apply PontryaginDual.ext
    intro a
    change χ ((ρ (k * h))⁻¹ a) = χ ((ρ h)⁻¹ ((ρ k)⁻¹ a))
    simp only [map_mul, mul_inv_rev, MulAut.mul_apply, MulAut.inv_apply]



end GeneralPontryaginDual

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
noncomputable instance instECountable (n : ℕ) : Countable (E n) := by
  let : SecondCountableTopology (Multiplicative (CarryGroup n)) :=
    (show Topology.IsEmbedding
      (Multiplicative.toAdd : Multiplicative (CarryGroup n) → CarryGroup n) from
      { toIsInducing := ⟨induced_id.symm⟩
        injective := fun _ _ h => h }).secondCountableTopology
  change Countable (PontryaginDual (Multiplicative (CarryGroup n)))
  exact pontryaginDual_countable (Multiplicative (CarryGroup n))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem shiftVector_injective (n : ℕ) :
    Function.Injective (shiftVector n) := by
  intro v w h
  funext i
  exact mul_left_cancel₀
    (pow_ne_zero n Polynomial.X_ne_zero) (congrFun h i)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem shiftVector_range (n : ℕ) :
    LinearMap.range (shiftVector n) = shiftedSubmodule n := by
  ext v
  rw [LinearMap.mem_range, mem_shiftedSubmodule_iff]
  constructor
  · rintro ⟨u, rfl⟩ i
    exact ⟨u i, rfl⟩
  · intro hv
    choose u hu using hv
    refine ⟨u, ?_⟩
    funext i
    exact (hu i).symm

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def shiftKernel (n : ℕ) : Submodule F X :=
  LinearMap.ker (shift n)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem shiftKernel_eq_dualAnnihilator (n : ℕ) :
    shiftKernel n = (shiftedSubmodule n).dualAnnihilator := by
  change LinearMap.ker (shiftVector n).dualMap = _
  rw [LinearMap.ker_dualMap_eq_dualAnnihilator_range, shiftVector_range]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
noncomputable def shiftKernelEquivDualQuotient (n : ℕ) :
    shiftKernel n ≃ₗ[F] Module.Dual F (ShiftedQuotient n) :=
  (LinearEquiv.ofEq _ _ (shiftKernel_eq_dualAnnihilator n)).trans
    (Submodule.dualQuotEquivDualAnnihilator (shiftedSubmodule n)).symm

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
noncomputable def shiftedQuotientBasis (n : ℕ) :
    Module.Basis (Fin 4 × Fin n) F (ShiftedQuotient n) :=
  (Pi.basisFun F (Fin 4 × Fin n)).map
    ((LinearEquiv.curry F F (Fin 4) (Fin n)).trans
      (shiftedQuotientCoeffEquiv n).symm)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
noncomputable def shiftKernelEquivQuotient (n : ℕ) :
    shiftKernel n ≃ₗ[F] ShiftedQuotient n :=
  (shiftKernelEquivDualQuotient n).trans
    (shiftedQuotientBasis n).toDualEquiv.symm

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem shiftKernel_card (n : ℕ) :
    Nat.card (shiftKernel n) = 2 ^ (4 * n) := by
  rw [Nat.card_congr (shiftKernelEquivQuotient n).toEquiv]
  exact shiftedQuotient_card n





/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def carryKernelInclusion (n : ℕ) : Y →+ CarryGroup n where
  toFun q := ⟨0, q⟩
  map_zero' := rfl
  map_add' q q' := by
    apply CarryGroup.ext
    · simp only [CarryGroup.add_linear, add_zero]
    · simp only [CarryGroup.add_quadratic, shiftedCarry_zero_right, add_zero]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem carryKernelInclusion_linear (n : ℕ) (q : Y) :
    (carryKernelInclusion n q).linear = 0 := rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem carryKernelInclusion_quadratic (n : ℕ) (q : Y) :
    (carryKernelInclusion n q).quadratic = q := rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem shift_zero_apply (ℓ : X) : shift 0 ℓ = ℓ := by
  apply LinearMap.ext
  intro v
  simp only [shift, shiftVector, pow_zero, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.coe_comp,
    LinearMap.coe_restrictScalars, Function.comp_apply, LinearMap.lsmul_apply, one_smul]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def carryPullback (n : ℕ) : CarryGroup n →+ CarryGroup 0 where
  toFun z := ⟨shift n z.linear, z.quadratic⟩
  map_zero' := by
    apply CarryGroup.ext <;> simp
  map_add' z w := by
    apply CarryGroup.ext
    · simp only [CarryGroup.add_linear, shift_add]
    · change z.quadratic + w.quadratic + shiftedCarry n z.linear w.linear =
        z.quadratic + w.quadratic +
          shiftedCarry 0 (shift n z.linear) (shift n w.linear)
      simp only [shiftedCarry, shift_zero_apply]





/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem continuous_carryPullback (n : ℕ) :
    Continuous (carryPullback n : CarryGroup n → CarryGroup 0) := by
  apply continuous_induced_rng.mpr
  exact ((continuous_shift n).comp (continuous_linear n)).prodMk
    (continuous_quadratic n)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def shiftKernelInclusion (n : ℕ) : shiftKernel n →+ CarryGroup n where
  toFun ℓ := ⟨ℓ.1, 0⟩
  map_zero' := rfl
  map_add' ℓ ℓ' := by
    apply CarryGroup.ext
    · rfl
    · change 0 = 0 + 0 + shiftedCarry n ℓ.1 ℓ'.1
      have hℓ : shift n ℓ.1 = 0 := ℓ.property
      simp only [add_zero, shiftedCarry, hℓ, carry_zero_left]





/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem continuous_shiftKernelInclusion (n : ℕ) :
    Continuous (shiftKernelInclusion n : shiftKernel n → CarryGroup n) := by
  apply continuous_CarryGroup_iff.mpr
  exact ⟨fun v => (continuous_X_eval v).comp continuous_subtype_val,
    fun _ => continuous_const⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def shiftVectorLeftInverse (n : ℕ) : V →ₗ[F] V :=
  (shiftVector n).leftInverse

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem shiftVectorLeftInverse_shiftVector (n : ℕ) (v : V) :
    shiftVectorLeftInverse n (shiftVector n v) = v := by
  exact LinearMap.leftInverse_apply_of_inj
    (LinearMap.ker_eq_bot.mpr (shiftVector_injective n)) v

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def shiftSection (n : ℕ) : X →ₗ[F] X where
  toFun ℓ := ℓ.comp (shiftVectorLeftInverse n)
  map_add' _ _ := by
    apply LinearMap.ext
    intro v
    rfl
  map_smul' _ _ := by
    apply LinearMap.ext
    intro v
    rfl



/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem continuous_shiftSection (n : ℕ) :
    Continuous (shiftSection n : X → X) :=
  continuous_X_precomp (shiftVectorLeftInverse n)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem shift_shiftSection (n : ℕ) (ℓ : X) :
    shift n (shiftSection n ℓ) = ℓ := by
  apply LinearMap.ext
  intro v
  change ℓ (shiftVectorLeftInverse n (shiftVector n v)) = ℓ v
  rw [shiftVectorLeftInverse_shiftVector]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def carryPullbackSection (n : ℕ) : CarryGroup 0 →+ CarryGroup n where
  toFun z := ⟨shiftSection n z.linear, z.quadratic⟩
  map_zero' := by
    apply CarryGroup.ext <;> simp
  map_add' z w := by
    apply CarryGroup.ext
    · exact (shiftSection n).map_add z.linear w.linear
    · change z.quadratic + w.quadratic + shiftedCarry 0 z.linear w.linear =
        z.quadratic + w.quadratic +
          shiftedCarry n (shiftSection n z.linear) (shiftSection n w.linear)
      simp only [shiftedCarry, shift_zero_apply, shift_shiftSection]





/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem continuous_carryPullbackSection (n : ℕ) :
    Continuous (carryPullbackSection n : CarryGroup 0 → CarryGroup n) := by
  apply continuous_induced_rng.mpr
  exact ((continuous_shiftSection n).comp (continuous_linear 0)).prodMk
    (continuous_quadratic 0)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
public
theorem carryPullback_carryPullbackSection
    (n : ℕ) (z : CarryGroup 0) :
    carryPullback n (carryPullbackSection n z) = z := by
  apply CarryGroup.ext
  · exact shift_shiftSection n z.linear
  · rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def carryPullbackContinuous (n : ℕ) :
    Multiplicative (CarryGroup n) →ₜ* Multiplicative (CarryGroup 0) :=
  ContinuousMonoidHom.mk
    (AddMonoidHom.toMultiplicative (carryPullback n))
    (continuous_carryPullback n)



/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def carryPullbackSectionContinuous (n : ℕ) :
    Multiplicative (CarryGroup 0) →ₜ* Multiplicative (CarryGroup n) :=
  ContinuousMonoidHom.mk
    (AddMonoidHom.toMultiplicative (carryPullbackSection n))
    (continuous_carryPullbackSection n)





/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def kernelProjection (n : ℕ) : CarryGroup n →+ shiftKernel n where
  toFun z :=
    ⟨z.linear - shiftSection n (shift n z.linear), by
      change shift n (z.linear - shiftSection n (shift n z.linear)) = 0
      rw [map_sub, shift_shiftSection, sub_self]⟩
  map_zero' := by
    apply Subtype.ext
    simp only [CarryGroup.zero_linear, map_zero, sub_self, ZeroMemClass.coe_zero]
  map_add' z w := by
    apply Subtype.ext
    change z.linear + w.linear -
        shiftSection n (shift n (z.linear + w.linear)) =
      (z.linear - shiftSection n (shift n z.linear)) +
        (w.linear - shiftSection n (shift n w.linear))
    rw [(shift n).map_add, (shiftSection n).map_add]
    abel



/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem continuous_kernelProjection (n : ℕ) :
    Continuous (kernelProjection n : CarryGroup n → shiftKernel n) := by
  exact ((continuous_linear n).sub
    ((continuous_shiftSection n).comp
      ((continuous_shift n).comp (continuous_linear n)))).subtype_mk _

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def kernelProjectionContinuous (n : ℕ) :
    Multiplicative (CarryGroup n) →ₜ* Multiplicative (shiftKernel n) :=
  ContinuousMonoidHom.mk
    (AddMonoidHom.toMultiplicative (kernelProjection n))
    (continuous_kernelProjection n)



/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def shiftKernelInclusionContinuous (n : ℕ) :
    Multiplicative (shiftKernel n) →ₜ* Multiplicative (CarryGroup n) :=
  ContinuousMonoidHom.mk
    (AddMonoidHom.toMultiplicative (shiftKernelInclusion n))
    (continuous_shiftKernelInclusion n)



/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
public
theorem kernelProjection_shiftKernelInclusion
    (n : ℕ) (ℓ : shiftKernel n) :
    kernelProjection n (shiftKernelInclusion n ℓ) = ℓ := by
  apply Subtype.ext
  change ℓ.1 - shiftSection n (shift n ℓ.1) = ℓ.1
  have hℓ : shift n ℓ.1 = 0 := ℓ.property
  rw [hℓ, map_zero, sub_zero]



/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem kernelProjection_carryPullbackSection
    (n : ℕ) (z : CarryGroup 0) :
    kernelProjection n (carryPullbackSection n z) = 0 := by
  apply Subtype.ext
  change shiftSection n z.linear -
    shiftSection n (shift n (shiftSection n z.linear)) = 0
  rw [shift_shiftSection, sub_self]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def carryGroupSplitEquiv (n : ℕ) :
    CarryGroup n ≃+ CarryGroup 0 × shiftKernel n where
  toFun z := (carryPullback n z, kernelProjection n z)
  invFun z := carryPullbackSection n z.1 + shiftKernelInclusion n z.2
  left_inv z := by
    apply CarryGroup.ext
    · change shiftSection n (shift n z.linear) +
        (z.linear - shiftSection n (shift n z.linear)) = z.linear
      abel
    · change z.quadratic + 0 + shiftedCarry n
        (shiftSection n (shift n z.linear))
        (z.linear - shiftSection n (shift n z.linear)) = z.quadratic
      have hzero : shift n
          (z.linear - shiftSection n (shift n z.linear)) = 0 := by
        rw [map_sub, shift_shiftSection, sub_self]
      simp only [add_zero, shiftedCarry, shift_shiftSection, hzero, carry_zero_right]
  right_inv z := by
    apply Prod.ext
    · change carryPullback n (carryPullbackSection n z.1 +
        shiftKernelInclusion n z.2) = z.1
      rw [map_add, carryPullback_carryPullbackSection]
      have hzero : carryPullback n (shiftKernelInclusion n z.2) = 0 := by
        apply CarryGroup.ext
        · exact z.2.property
        · rfl
      rw [hzero, add_zero]
    · change kernelProjection n (carryPullbackSection n z.1 +
        shiftKernelInclusion n z.2) = z.2
      rw [map_add, kernelProjection_carryPullbackSection,
        kernelProjection_shiftKernelInclusion, zero_add]
  map_add' z w := by
    exact Prod.ext ((carryPullback n).map_add z w)
      ((kernelProjection n).map_add z w)

end

section

open Module

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def auxiliaryBasis : Basis (Basis.ofVectorSpaceIndex F V) F V :=
  Basis.ofVectorSpace F V

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def coordinateProduct : V →ₗ[F] V →ₗ[F] V where
  toFun x :=
    { toFun := fun y ↦ auxiliaryBasis.repr.symm
        (auxiliaryBasis.repr x * auxiliaryBasis.repr y)
      map_add' y z := by
        apply auxiliaryBasis.repr.injective
        ext i
        simp only [map_add, mul_add, Basis.repr_symm_apply, Basis.repr_linearCombination,
          Finsupp.coe_add, Pi.add_apply, Finsupp.mul_apply]
      map_smul' c y := by
        apply auxiliaryBasis.repr.injective
        ext i
        simp only [map_smul, Basis.repr_symm_apply, Basis.repr_linearCombination, Finsupp.mul_apply,
          Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, mul_left_comm, RingHom.id_apply] }
  map_add' x y := by
    apply LinearMap.ext
    intro z
    apply auxiliaryBasis.repr.injective
    ext i
    simp only [map_add, add_mul, Basis.repr_symm_apply, LinearMap.coe_mk, AddHom.coe_mk,
      Basis.repr_linearCombination, Finsupp.coe_add, Pi.add_apply, Finsupp.mul_apply,
      LinearMap.add_apply]
  map_smul' c x := by
    apply LinearMap.ext
    intro y
    apply auxiliaryBasis.repr.injective
    ext i
    simp only [map_smul, Basis.repr_symm_apply, LinearMap.coe_mk, AddHom.coe_mk,
      Basis.repr_linearCombination, Finsupp.mul_apply, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul,
      mul_assoc, RingHom.id_apply, LinearMap.smul_apply]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def tensorDiagonal : T →ₗ[F] V := TensorProduct.lift coordinateProduct

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem scalar_mul_self (c : F) : c * c = c := by
  by_cases hc : c = 0
  · simp only [hc, mul_zero]
  · rw [FeedbackBooleanPolynomial.eq_one_of_ne_zero_zmod_two c hc, mul_one]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem tensorDiagonal_square (v : V) : tensorDiagonal (square v) = v := by
  apply auxiliaryBasis.repr.injective
  ext i
  simp only [tensorDiagonal, coordinateProduct, Basis.repr_symm_apply, square,
    TensorProduct.lift.tmul, LinearMap.coe_mk, AddHom.coe_mk, Basis.repr_linearCombination,
    Finsupp.mul_apply, scalar_mul_self]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def d : B →ₗ[F] V := tensorDiagonal.comp B.subtype

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem d_diagonal (v : V) : d (diagonal v) = v :=
  tensorDiagonal_square v



/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem d_surjective : Function.Surjective d := by
  intro v
  exact ⟨diagonal v, d_diagonal v⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem linearMap_ext_on_diagonal {W : Type*}
    [AddCommGroup W] [Module F W] {f g : B →ₗ[F] W}
    (h : ∀ v : V, f (diagonal v) = g (diagonal v)) : f = g := by
  apply LinearMap.ext
  intro w
  rcases w with ⟨w, hw⟩
  change f ⟨w, hw⟩ = g ⟨w, hw⟩
  change w ∈ Submodule.span F (Set.range square) at hw
  induction hw using Submodule.span_induction with
  | mem w hw =>
      rcases hw with ⟨v, rfl⟩
      exact h v
  | zero =>
      change f 0 = g 0
      simp only [map_zero]
  | add x y hx hy ihx ihy =>
      change f (⟨x, hx⟩ + ⟨y, hy⟩) = g (⟨x, hx⟩ + ⟨y, hy⟩)
      simpa only [map_add] using congrArg₂ (· + ·) ihx ihy
  | smul c x hx ih =>
      change f (c • (⟨x, hx⟩ : B)) = g (c • (⟨x, hx⟩ : B))
      simpa only [map_smul] using congrArg (c • ·) ih

end

section

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def binaryRootCharacter : PontryaginDual (Multiplicative F) where
  toMonoidHom := AddChar.toMonoidHomEquiv (ZMod.toCircle (N := 2))
  continuous_toFun := continuous_of_discreteTopology



/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def carryLinearEvaluation (n : ℕ) (v : V) : CarryGroup n →+ F where
  toFun z := z.linear v
  map_zero' := rfl
  map_add' _ _ := rfl



/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def carryLinearEvaluationContinuous (n : ℕ) (v : V) :
    Multiplicative (CarryGroup n) →ₜ* Multiplicative F where
  toMonoidHom := (carryLinearEvaluation n v).toMultiplicative
  continuous_toFun := continuous_linear_eval n v



/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def iotaCharacter (n : ℕ) (v : V) : E n :=
  Additive.ofMul
    (PontryaginDual.map (carryLinearEvaluationContinuous n v)
      binaryRootCharacter)



/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def iota (n : ℕ) : V →+ E n where
  toFun := iotaCharacter n
  map_zero' := by
    apply Additive.toMul.injective
    apply PontryaginDual.ext
    intro z
    change ZMod.toCircle ((Multiplicative.toAdd z).linear 0) = 1
    simp only [map_zero, AddChar.map_zero_eq_one]
  map_add' v w := by
    apply Additive.toMul.injective
    apply PontryaginDual.ext
    intro z
    change ZMod.toCircle ((Multiplicative.toAdd z).linear (v + w)) =
      ZMod.toCircle ((Multiplicative.toAdd z).linear v) *
        ZMod.toCircle ((Multiplicative.toAdd z).linear w)
    rw [map_add, AddChar.map_add_eq_mul]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
public
theorem iota_apply (n : ℕ) (v : V) (z : CarryGroup n) :
    Additive.toMul (iota n v) (Multiplicative.ofAdd z) =
      ZMod.toCircle (z.linear v) := rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem iota_injective (n : ℕ) : Function.Injective (iota n) := by
  intro v w h
  apply Module.eval_apply_injective F
  apply LinearMap.ext
  intro ℓ
  have hcharacters := congrArg Additive.toMul h
  have hpoint := DFunLike.congr_fun hcharacters
    (Multiplicative.ofAdd (⟨ℓ, 0⟩ : CarryGroup n))
  exact ZMod.injective_toCircle hpoint

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem circle_four_square_liftBit (a : F) :
    (ZMod.toCircle (FiniteCarry.liftBit a) : Circle) ^ 2 =
      ZMod.toCircle a := by
  fin_cases a
  · change ZMod.toCircle (0 : ZMod 4) ^ 2 = ZMod.toCircle (0 : ZMod 2)
    simp only [AddChar.map_zero_eq_one, one_pow]
  · rw [← AddChar.map_nsmul_eq_pow]
    change ZMod.toCircle (2 : ZMod 4) = ZMod.toCircle (1 : ZMod 2)
    apply Circle.ext
    calc
      _ = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (2 : ℕ) / (4 : ℕ)) :=
        ZMod.toCircle_natCast (N := 4) 2
      _ = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (1 : ℕ) / (2 : ℕ)) := by
        congr 1
        ring
      _ = _ := (ZMod.toCircle_natCast (N := 2) 1).symm

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def quadraticInclusionContinuous (n : ℕ) :
    Multiplicative Y →ₜ* Multiplicative (CarryGroup n) where
  toMonoidHom := (carryKernelInclusion n).toMultiplicative
  continuous_toFun := by
    apply continuous_CarryGroup_iff.mpr
    constructor
    · intro v
      exact continuous_const
    · intro w
      exact continuous_Y_eval w



/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def quadraticRestriction (n : ℕ) :
    E n →+ Additive (PontryaginDual (Multiplicative Y)) :=
  (PontryaginDual.map (quadraticInclusionContinuous n)).toMonoidHom.toAdditive



/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem iota_range_le_ker_quadraticRestriction (n : ℕ) :
    (iota n).range ≤ (quadraticRestriction n).ker := by
  rintro _ ⟨v, rfl⟩
  change quadraticRestriction n (iota n v) = 0
  apply Additive.toMul.injective
  apply PontryaginDual.ext
  intro q
  change ZMod.toCircle ((0 : X) v) = 1
  simp only [LinearMap.zero_apply, AddChar.map_zero_eq_one]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def quadraticEvaluation (b : B) : Y →+ F where
  toFun q := q b
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def quadraticEvaluationContinuous (b : B) :
    Multiplicative Y →ₜ* Multiplicative F where
  toMonoidHom := (quadraticEvaluation b).toMultiplicative
  continuous_toFun := continuous_Y_eval b

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def quadraticCharacter (b : B) :
    Additive (PontryaginDual (Multiplicative Y)) :=
  Additive.ofMul (PontryaginDual.map (quadraticEvaluationContinuous b)
    binaryRootCharacter)



/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def quadraticPairing : B →+ Additive (PontryaginDual (Multiplicative Y)) where
  toFun := quadraticCharacter
  map_zero' := by
    apply Additive.toMul.injective
    apply PontryaginDual.ext
    intro q
    change ZMod.toCircle ((Multiplicative.toAdd q) 0) = 1
    simp only [map_zero, AddChar.map_zero_eq_one]
  map_add' b c := by
    apply Additive.toMul.injective
    apply PontryaginDual.ext
    intro q
    change ZMod.toCircle ((Multiplicative.toAdd q) (b + c)) =
      ZMod.toCircle ((Multiplicative.toAdd q) b) *
        ZMod.toCircle ((Multiplicative.toAdd q) c)
    rw [map_add, AddChar.map_add_eq_mul]



/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem circle_four_twice_liftBit (a : F) :
    ZMod.toCircle (2 * FiniteCarry.liftBit a : ZMod 4) =
      ZMod.toCircle a := by
  calc
    _ = (ZMod.toCircle (FiniteCarry.liftBit a) : Circle) ^ 2 := by
      rw [← AddChar.map_nsmul_eq_pow]
      congr 1
      simp only [two_mul, nsmul_eq_mul, Nat.cast_ofNat]
    _ = ZMod.toCircle a := circle_four_square_liftBit a

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem quadraticRestriction_epsilon (n : ℕ) (v : V) :
    quadraticRestriction n (epsilon n v) = quadraticPairing (diagonal v) := by
  apply Additive.toMul.injective
  apply PontryaginDual.ext
  intro q
  change ZMod.toCircle
    (CarryGroup.evalFour n v (⟨0, Multiplicative.toAdd q⟩ : CarryGroup n)) =
      ZMod.toCircle ((Multiplicative.toAdd q) (diagonal v))
  rw [CarryGroup.evalFour_apply]
  simpa only [shift, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.zero_comp, LinearMap.zero_apply,
    FiniteCarry.liftBit_zero, zero_add] using
    circle_four_twice_liftBit ((Multiplicative.toAdd q) (diagonal v))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem quadraticPairing_range_le_quadraticRestriction_range (n : ℕ) :
    quadraticPairing.range ≤ (quadraticRestriction n).range := by
  rintro _ ⟨b, rfl⟩
  rcases b with ⟨b, hb⟩
  change b ∈ Submodule.span F (Set.range square) at hb
  induction hb using Submodule.span_induction with
  | mem b hb =>
      rcases hb with ⟨v, rfl⟩
      exact ⟨epsilon n v, quadraticRestriction_epsilon n v⟩
  | zero =>
      change quadraticPairing (0 : B) ∈ (quadraticRestriction n).range
      rw [map_zero]
      exact (quadraticRestriction n).range.zero_mem
  | add b c hb hc ihb ihc =>
      change quadraticPairing ((⟨b, hb⟩ : B) + (⟨c, hc⟩ : B)) ∈
        (quadraticRestriction n).range
      rw [map_add]
      exact (quadraticRestriction n).range.add_mem ihb ihc
  | smul a b hb ih =>
      have ha : a = 0 ∨ a = 1 := by
        fin_cases a
        · exact Or.inl rfl
        · exact Or.inr rfl
      rcases ha with rfl | rfl
      · have hzero :
            (⟨(0 : F) • b, by simp only [zero_smul, zero_mem]⟩ : B) = 0 := by
          apply Subtype.ext
          simp only [zero_smul, ZeroMemClass.coe_zero]
        change quadraticPairing
          (⟨(0 : F) • b, _⟩ : B) ∈ (quadraticRestriction n).range
        rw [hzero, map_zero]
        exact (quadraticRestriction n).range.zero_mem
      · have hone :
            (⟨(1 : F) • b, by simpa only [one_smul] using
              (show b ∈ B from hb)⟩ : B) =
              (⟨b, (show b ∈ B from hb)⟩ : B) := by
          apply Subtype.ext
          simp only [one_smul]
        change quadraticPairing
          (⟨(1 : F) • b, _⟩ : B) ∈ (quadraticRestriction n).range
        rw [hone]
        exact ih

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem binary_sq_eq_self (a : F) : a * a = a := by
  by_cases ha : a = 0
  · simp only [ha, mul_zero]
  · rw [FeedbackBooleanPolynomial.eq_one_of_ne_zero_zmod_two a ha, mul_one]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem carry_self_eq_evaluate_d (ℓ : X) (b : B) :
    carry ℓ ℓ b = ℓ (d b) := by
  let lhs : B →ₗ[F] F := carry ℓ ℓ
  let rhs : B →ₗ[F] F := ℓ.comp d
  have h : lhs = rhs := by
    apply linearMap_ext_on_diagonal
    intro v
    change carry ℓ ℓ (diagonal v) = (ℓ.comp d) (diagonal v)
    rw [carry_apply_diagonal, LinearMap.comp_apply, d_diagonal]
    exact binary_sq_eq_self (ℓ v)
  exact DFunLike.congr_fun h b

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem shiftedCarry_self_eq_evaluate_d (n : ℕ) (ℓ : X) (b : B) :
    shiftedCarry n ℓ ℓ b = ℓ (shiftVector n (d b)) := by
  exact carry_self_eq_evaluate_d (shift n ℓ) b

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def linearSection (n : ℕ) (ℓ : X) : CarryGroup n := ⟨ℓ, 0⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem linearSection_linear (n : ℕ) (ℓ : X) :
    (linearSection n ℓ).linear = ℓ := rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem linearSection_quadratic (n : ℕ) (ℓ : X) :
    (linearSection n ℓ).quadratic = 0 := rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem linearSection_zero (n : ℕ) : linearSection n 0 = 0 := rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem continuous_linearSection (n : ℕ) :
    Continuous (linearSection n) := by
  apply continuous_CarryGroup_iff.mpr
  exact ⟨fun v => continuous_X_eval v, fun _ => continuous_const⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem linearSection_add (n : ℕ) (ℓ ℓ' : X) :
    linearSection n ℓ + linearSection n ℓ' =
      linearSection n (ℓ + ℓ') +
        carryKernelInclusion n (shiftedCarry n ℓ ℓ') := by
  apply CarryGroup.ext
  · simp only [CarryGroup.add_linear, linearSection_linear, carryKernelInclusion_linear, add_zero]
  · simp only [CarryGroup.add_quadratic, linearSection_quadratic, add_zero, linearSection_linear,
      zero_add, carryKernelInclusion_quadratic, carryKernelInclusion_linear,
      shiftedCarry_zero_right]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def evalEta {n : ℕ} (η : E n) (z : CarryGroup n) : Circle :=
  Additive.toMul η (Multiplicative.ofAdd z)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem evalEta_zero {n : ℕ} (η : E n) : evalEta η 0 = 1 :=
  map_one (Additive.toMul η)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem evalEta_add {n : ℕ} (η : E n) (z w : CarryGroup n) :
    evalEta η (z + w) = evalEta η z * evalEta η w := by
  change (Additive.toMul η)
      (Multiplicative.ofAdd z * Multiplicative.ofAdd w) =
    Additive.toMul η (Multiplicative.ofAdd z) *
      Additive.toMul η (Multiplicative.ofAdd w)
  exact map_mul (Additive.toMul η)
    (Multiplicative.ofAdd z) (Multiplicative.ofAdd w)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem evalEta_kernel {n : ℕ} (η : E n)
    (h : quadraticRestriction n η = 0) (q : Y) :
    evalEta η (carryKernelInclusion n q) = 1 := by
  have hpoint := DFunLike.congr_fun (congrArg Additive.toMul h)
    (Multiplicative.ofAdd q)
  exact hpoint

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem evalEta_linearSection_add {n : ℕ} (η : E n)
    (h : quadraticRestriction n η = 0) (ℓ ℓ' : X) :
    evalEta η (linearSection n (ℓ + ℓ')) =
      evalEta η (linearSection n ℓ) *
        evalEta η (linearSection n ℓ') := by
  have hdecomp := congrArg (evalEta η) (linearSection_add n ℓ ℓ')
  rw [evalEta_add, evalEta_add,
    evalEta_kernel η h, mul_one] at hdecomp
  exact hdecomp.symm

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def kernelCharacter (n : ℕ) (η : E n)
    (h : quadraticRestriction n η = 0) :
    PontryaginDual (Multiplicative X) where
  toMonoidHom :=
    { toFun := fun ℓ => evalEta η
        (linearSection n (Multiplicative.toAdd ℓ))
      map_one' := by simp only [toAdd_one, linearSection_zero, evalEta_zero]
      map_mul' ℓ ℓ' :=
        evalEta_linearSection_add η h
          (Multiplicative.toAdd ℓ) (Multiplicative.toAdd ℓ') }
  continuous_toFun :=
    (Additive.toMul η).continuous.comp (continuous_linearSection n)



/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem evalEta_eq_kernelCharacter_linear {n : ℕ} (η : E n)
    (h : quadraticRestriction n η = 0) (z : CarryGroup n) :
    evalEta η z =
      kernelCharacter n η h (Multiplicative.ofAdd z.linear) := by
  have hdecomp :
      z = linearSection n z.linear + carryKernelInclusion n z.quadratic := by
    apply CarryGroup.ext <;> simp
  conv_lhs => rw [hdecomp]
  rw [evalEta_add, evalEta_kernel η h, mul_one]
  rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def sigma (n : ℕ) : E n →+ B :=
  (pointwisePontryaginDualEquiv B).toAddMonoidHom.comp
    (quadraticRestriction n)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem sigma_characterization (n : ℕ) (η : E n) (q : Y) :
    ZMod.toCircle (q (sigma n η)) =
      Additive.toMul η
        (Multiplicative.ofAdd (⟨0, q⟩ : CarryGroup n)) := by
  exact pointwisePontryaginDualEquiv_apply_character B
    (quadraticRestriction n η) q



/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem sigma_surjective (n : ℕ) : Function.Surjective (sigma n) := by
  intro b
  have hb : quadraticPairing b ∈ quadraticPairing.range := ⟨b, rfl⟩
  obtain ⟨η, hη⟩ :=
    quadraticPairing_range_le_quadraticRestriction_range n hb
  refine ⟨η, ?_⟩
  change pointwisePontryaginDualEquiv B
    (quadraticRestriction n η) = b
  rw [hη]
  change pointwisePontryaginDualEquiv B
    (pointwiseEvaluationHom B b) = b
  exact (pointwisePontryaginDualEquiv B).apply_symm_apply b

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem sigma_eq_zero_iff (n : ℕ) (η : E n) :
    sigma n η = 0 ↔ quadraticRestriction n η = 0 := by
  change pointwisePontryaginDualEquiv B (quadraticRestriction n η) = 0 ↔ _
  exact (pointwisePontryaginDualEquiv B).map_eq_zero_iff

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem sigma_ker (n : ℕ) : (sigma n).ker = (iota n).range := by
  ext η
  constructor
  · intro hη
    have hrestriction : quadraticRestriction n η = 0 :=
      (sigma_eq_zero_iff n η).mp hη
    let χ : Additive (PontryaginDual (Multiplicative X)) :=
      Additive.ofMul (kernelCharacter n η hrestriction)
    let v : V := pointwisePontryaginDualEquiv V χ
    refine ⟨v, ?_⟩
    apply Additive.toMul.injective
    apply PontryaginDual.ext
    intro z
    change ZMod.toCircle ((Multiplicative.toAdd z).linear v) =
      evalEta η (Multiplicative.toAdd z)
    rw [evalEta_eq_kernelCharacter_linear η hrestriction]
    exact pointwisePontryaginDualEquiv_apply_character V
      χ (Multiplicative.toAdd z).linear
  · rintro ⟨v, rfl⟩
    exact (sigma_eq_zero_iff n (iota n v)).mpr
      (iota_range_le_ker_quadraticRestriction n ⟨v, rfl⟩)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem two_nsmul_eta (n : ℕ) (η : E n) :
    (2 : ℕ) • η = iota n (shiftVector n (d (sigma n η))) := by
  apply Additive.toMul.injective
  apply PontryaginDual.ext
  intro z
  change (Additive.toMul η z) ^ (2 : ℕ) =
    ZMod.toCircle
      ((Multiplicative.toAdd z).linear
        (shiftVector n (d (sigma n η))))
  have hdouble :
      z ^ (2 : ℕ) = Multiplicative.ofAdd
        (⟨0, shiftedCarry n
          (Multiplicative.toAdd z).linear
          (Multiplicative.toAdd z).linear⟩ : CarryGroup n) := by
    apply Multiplicative.toAdd.injective
    apply CarryGroup.ext
    · change ((2 : ℕ) • Multiplicative.toAdd z).linear = 0
      simp only [CarryGroup.two_nsmul_linear]
    · change ((2 : ℕ) • Multiplicative.toAdd z).quadratic =
        shiftedCarry n (Multiplicative.toAdd z).linear
          (Multiplicative.toAdd z).linear
      simp only [CarryGroup.two_nsmul_quadratic]
  calc
    (Additive.toMul η z) ^ (2 : ℕ) =
        Additive.toMul η (z ^ (2 : ℕ)) :=
      (map_pow (Additive.toMul η).toMonoidHom z 2).symm
    _ = Additive.toMul η
      (Multiplicative.ofAdd
        (⟨0, shiftedCarry n
          (Multiplicative.toAdd z).linear
          (Multiplicative.toAdd z).linear⟩ : CarryGroup n)) :=
      congrArg (fun w => (Additive.toMul η) w) hdouble
    _ = ZMod.toCircle
      (shiftedCarry n
        (Multiplicative.toAdd z).linear
        (Multiplicative.toAdd z).linear (sigma n η)) :=
      (sigma_characterization n η _).symm
    _ = ZMod.toCircle
      ((Multiplicative.toAdd z).linear
        (shiftVector n (d (sigma n η)))) :=
      congrArg ZMod.toCircle
        (shiftedCarry_self_eq_evaluate_d n
          (Multiplicative.toAdd z).linear (sigma n η))

end

section

open MeasureTheory TopologicalSpace

universe u

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
instance instXMeasurableSpace : MeasurableSpace X := borel X

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
instance instXBorelSpace : BorelSpace X := ⟨rfl⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
instance instYMeasurableSpace : MeasurableSpace Y := borel Y

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
instance instYBorelSpace : BorelSpace Y := ⟨rfl⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
instance instCarryGroupMeasurableSpace (n : ℕ) :
    MeasurableSpace (CarryGroup n) := borel (CarryGroup n)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
instance instCarryGroupBorelSpace (n : ℕ) :
    BorelSpace (CarryGroup n) := ⟨rfl⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def normalizedAddHaar
    (A : Type u) [AddGroup A] [TopologicalSpace A] [CompactSpace A]
    [IsTopologicalAddGroup A] [MeasurableSpace A] [BorelSpace A] : Measure A :=
  Measure.addHaarMeasure
    (⟨⟨Set.univ, isCompact_univ⟩, by simp only [interior_univ,
                                       Set.univ_nonempty]⟩ : PositiveCompacts A)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
instance normalizedAddHaar_isProbabilityMeasure
    (A : Type u) [AddGroup A] [TopologicalSpace A] [CompactSpace A]
    [IsTopologicalAddGroup A] [MeasurableSpace A] [BorelSpace A] :
    IsProbabilityMeasure (normalizedAddHaar A) where
  measure_univ := by
    simpa only [normalizedAddHaar, interior_univ, Set.univ_nonempty, PositiveCompacts.coe_mk,
      Compacts.coe_mk] using
      (Measure.addHaarMeasure_self
        (K₀ := (⟨⟨Set.univ, isCompact_univ⟩, by simp only [interior_univ,
                                                  Set.univ_nonempty]⟩ : PositiveCompacts A)))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
instance normalizedAddHaar_isAddHaarMeasure
    (A : Type u) [AddGroup A] [TopologicalSpace A] [CompactSpace A]
    [IsTopologicalAddGroup A] [MeasurableSpace A] [BorelSpace A] :
    Measure.IsAddHaarMeasure (normalizedAddHaar A) := by
  unfold normalizedAddHaar
  infer_instance

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem normalizedAddHaar_unique
    (A : Type u) [AddGroup A] [TopologicalSpace A] [CompactSpace A]
    [IsTopologicalAddGroup A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ]
    [Measure.IsAddLeftInvariant μ] :
    μ = normalizedAddHaar A := by
  let U : PositiveCompacts A :=
    ⟨⟨Set.univ, isCompact_univ⟩, by simp only [interior_univ, Set.univ_nonempty]⟩
  have h := Measure.addHaarMeasure_unique μ U
  change μ = μ Set.univ • normalizedAddHaar A at h
  simpa only [measure_univ, one_smul] using h

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem normalizedAddHaar_preserving_addEquiv
    (A : Type u) [AddCommGroup A] [TopologicalSpace A] [CompactSpace A]
    [IsTopologicalAddGroup A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A]
    (e : A ≃+ A) (he : Continuous e) (heinv : Continuous e.symm) :
    MeasurePreserving e (normalizedAddHaar A) (normalizedAddHaar A) := by
  let μ := normalizedAddHaar A
  have : Measure.IsAddHaarMeasure (μ.map e) :=
    e.isAddHaarMeasure_map μ he heinv
  have : IsProbabilityMeasure (μ.map e) :=
    μ.isProbabilityMeasure_map he.measurable.aemeasurable
  refine ⟨he.measurable, ?_⟩
  exact normalizedAddHaar_unique A (μ.map e)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem skew_add_translation_measurePreserving
    {P Q : Type*} [AddCommGroup P] [AddCommGroup Q]
    [TopologicalSpace P] [TopologicalSpace Q]
    [IsTopologicalAddGroup P] [IsTopologicalAddGroup Q]
    [SecondCountableTopology Q]
    [MeasurableSpace P] [BorelSpace P]
    [MeasurableSpace Q] [BorelSpace Q]
    (μ : Measure P) (ν : Measure Q) [SFinite μ] [SFinite ν]
    [Measure.IsAddLeftInvariant μ] [Measure.IsAddLeftInvariant ν]
    (a : P) (b : Q) (c : P → Q) (hc : Continuous c) :
    MeasurePreserving
      (fun z : P × Q ↦ (a + z.1, b + z.2 + c z.1))
      (μ.prod ν) (μ.prod ν) := by
  refine MeasurePreserving.skew_product (μc := ν) (μd := ν)
    (g := fun x : P ↦ fun y : Q ↦ b + y + c x)
    (measurePreserving_add_left μ a) ?_ ?_
  · exact (measurable_const.add measurable_snd).add
      (hc.measurable.comp measurable_fst)
  · refine Filter.Eventually.of_forall fun x ↦ ?_
    convert map_add_left_eq_self ν (b + c x) using 1
    congr 1
    funext y
    abel

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def productHaar : Measure (X × Y) :=
  (normalizedAddHaar X).prod (normalizedAddHaar Y)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
instance productHaar_isProbabilityMeasure :
    IsProbabilityMeasure productHaar := by
  unfold productHaar
  infer_instance

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
instance productHaar_isAddLeftInvariant :
    Measure.IsAddLeftInvariant productHaar where
  map_add_left_eq_self z := by
    have hx := measurePreserving_add_left (normalizedAddHaar X) z.1
    have hy := measurePreserving_add_left (normalizedAddHaar Y) z.2
    change
      Measure.map
          (fun p : X × Y ↦ (z.1 + p.1, z.2 + p.2))
          ((normalizedAddHaar X).prod (normalizedAddHaar Y)) =
        (normalizedAddHaar X).prod (normalizedAddHaar Y)
    exact (hx.prod hy).map_eq

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem productHaar_eq_normalizedAddHaar :
    productHaar = normalizedAddHaar (X × Y) :=
  normalizedAddHaar_unique (X × Y) productHaar

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
instance productHaar_isAddHaarMeasure :
    Measure.IsAddHaarMeasure productHaar := by
  rw [productHaar_eq_normalizedAddHaar]
  infer_instance

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem productHaar_preserving_addEquiv
    (e : (X × Y) ≃+ (X × Y))
    (he : Continuous e) (heinv : Continuous e.symm) :
    MeasurePreserving e productHaar productHaar := by
  rw [productHaar_eq_normalizedAddHaar]
  exact normalizedAddHaar_preserving_addEquiv (X × Y) e he heinv

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem continuous_shiftedCarry_right (n : ℕ) (ℓ : X) :
    Continuous (fun x : X ↦ shiftedCarry n ℓ x) := by
  apply continuous_Y_iff.mpr
  rintro ⟨w, hw⟩
  change Continuous
    (fun x : X => tensorFunctional (shift n ℓ) (shift n x) w)
  change w ∈ Submodule.span F (Set.range square) at hw
  refine Submodule.span_induction
    (p := fun u _ => Continuous
      (fun x : X => tensorFunctional (shift n ℓ) (shift n x) u))
    ?_ ?_ ?_ ?_ hw
  · rintro _ ⟨v, rfl⟩
    change Continuous
      (fun x : X => ℓ (shiftVector n v) * x (shiftVector n v))
    exact (continuous_const : Continuous
      (fun _ : X => ℓ (shiftVector n v))).mul
        (continuous_X_eval (shiftVector n v))
  · simpa only [map_zero] using (continuous_const : Continuous (fun _ : X => (0 : F)))
  · intro u v _ _ hu hv
    simp_rw [map_add]
    convert hu.add hv using 1
    rfl
  · intro r v _ hv
    simp_rw [map_smul, smul_eq_mul]
    convert (continuous_const : Continuous (fun _ : X => r)).mul hv using 1
    rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem carryTranslation_measurePreserving (n : ℕ) (a : CarryGroup n) :
    MeasurePreserving
      (fun z : X × Y ↦
        (a.linear + z.1,
          a.quadratic + z.2 + shiftedCarry n a.linear z.1))
      productHaar productHaar := by
  change
    MeasurePreserving
      (fun z : X × Y ↦
        (a.linear + z.1,
          a.quadratic + z.2 + shiftedCarry n a.linear z.1))
      ((normalizedAddHaar X).prod (normalizedAddHaar Y))
      ((normalizedAddHaar X).prod (normalizedAddHaar Y))
  apply skew_add_translation_measurePreserving
    (normalizedAddHaar X) (normalizedAddHaar Y)
    a.linear a.quadratic (fun x ↦ shiftedCarry n a.linear x)
  exact continuous_shiftedCarry_right n a.linear

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def carryHaar (n : ℕ) : Measure (CarryGroup n) :=
  productHaar.map (carryHomeomorph n).symm

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
instance carryHaar_isProbabilityMeasure (n : ℕ) :
    IsProbabilityMeasure (carryHaar n) := by
  unfold carryHaar
  exact Measure.isProbabilityMeasure_map
    (carryHomeomorph n).symm.continuous.measurable.aemeasurable

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
instance carryHaar_isAddLeftInvariant (n : ℕ) :
    Measure.IsAddLeftInvariant (carryHaar n) := by
  constructor
  intro a
  have hpres := (carryTranslation_measurePreserving n a).map_eq
  have he : Measurable (carryHomeomorph n).symm :=
    (carryHomeomorph n).symm.continuous.measurable
  have ht : Measurable
      (fun z : X × Y ↦
        (a.linear + z.1,
          a.quadratic + z.2 + shiftedCarry n a.linear z.1)) :=
    (carryTranslation_measurePreserving n a).measurable
  change
    Measure.map (a + ·) (productHaar.map (carryHomeomorph n).symm) =
      productHaar.map (carryHomeomorph n).symm
  rw [Measure.map_map (continuous_const_add a).measurable he]
  calc
    Measure.map ((a + ·) ∘ (carryHomeomorph n).symm) productHaar =
        Measure.map ((carryHomeomorph n).symm ∘
          (fun z : X × Y ↦
            (a.linear + z.1,
              a.quadratic + z.2 + shiftedCarry n a.linear z.1)))
          productHaar := by rfl
    _ = Measure.map (carryHomeomorph n).symm
          (Measure.map
            (fun z : X × Y ↦
              (a.linear + z.1,
                a.quadratic + z.2 + shiftedCarry n a.linear z.1))
            productHaar) :=
          (Measure.map_map he ht).symm
    _ = productHaar.map (carryHomeomorph n).symm := by rw [hpres]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem carryHaar_eq_normalizedAddHaar (n : ℕ) :
    carryHaar n = normalizedAddHaar (CarryGroup n) :=
  normalizedAddHaar_unique (CarryGroup n) (carryHaar n)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
instance carryHaar_isAddHaarMeasure (n : ℕ) :
    Measure.IsAddHaarMeasure (carryHaar n) := by
  rw [carryHaar_eq_normalizedAddHaar n]
  infer_instance

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem carryHaar_preserving_addEquiv (n : ℕ)
    (e : CarryGroup n ≃+ CarryGroup n)
    (he : Continuous e) (heinv : Continuous e.symm) :
    MeasurePreserving e (carryHaar n) (carryHaar n) := by
  rw [carryHaar_eq_normalizedAddHaar n]
  exact normalizedAddHaar_preserving_addEquiv (CarryGroup n) e he heinv

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def carryCoordinatesMeasurableEquiv (n : ℕ) :
    CarryGroup n ≃ᵐ X × Y :=
  (carryHomeomorph n).toMeasurableEquiv



/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem carryCoordinates_measurePreserving (n : ℕ) :
    MeasurePreserving (carryCoordinatesMeasurableEquiv n)
      (carryHaar n) productHaar := by
  refine ⟨(carryHomeomorph n).continuous.measurable, ?_⟩
  change
    (productHaar.map (carryHomeomorph n).symm).map
      (carryHomeomorph n) = productHaar
  exact MeasurableEquiv.map_map_symm (carryCoordinatesMeasurableEquiv n)

end

section

open Set Submodule MeasureTheory
open scoped ENNReal Topology

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def linearEvaluationCharacter (n : ℕ) (v : V) : E n :=
  Additive.ofMul
    { toFun := fun z => ZMod.toCircle ((Multiplicative.toAdd z).linear v)
      map_one' := by simp only [toAdd_one, CarryGroup.zero_linear, LinearMap.zero_apply,
                       AddChar.map_zero_eq_one]
      map_mul' z w := by
        change ZMod.toCircle
          ((Multiplicative.toAdd z).linear v +
            (Multiplicative.toAdd w).linear v) = _
        exact AddChar.map_add_eq_mul _ _ _
      continuous_toFun :=
        (continuous_of_discreteTopology :
          Continuous (fun x : F => (ZMod.toCircle x : Circle))).comp
          (continuous_linear_eval n v) }

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem linearEvaluationCharacter_apply
    (n : ℕ) (v : V) (z : CarryGroup n) :
    Additive.toMul (linearEvaluationCharacter n v) (Multiplicative.ofAdd z) =
      ZMod.toCircle (z.linear v) := rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem carry_pontryagin_characters_separate
    (n : ℕ) (x y : CarryGroup n) (hxy : x ≠ y) :
    ∃ χ : E n,
      Additive.toMul χ (Multiplicative.ofAdd x) ≠
        Additive.toMul χ (Multiplicative.ofAdd y) := by
  let _ := @linearEvaluationCharacter_apply
  by_contra h
  push Not at h
  apply hxy
  apply CarryGroup.ext
  · apply LinearMap.ext
    intro v
    apply ZMod.injective_toCircle
    simpa only [linearEvaluationCharacter_apply] using h (linearEvaluationCharacter n v)
  · apply linearMap_ext_on_diagonal
    intro v
    have hfour : CarryGroup.evalFour n v x = CarryGroup.evalFour n v y := by
      apply ZMod.injective_toCircle
      simpa only [epsilon_apply] using h (epsilon n v)
    have hpoint : CarryGroup.pointEvaluation n v x =
        CarryGroup.pointEvaluation n v y := by
      apply FiniteCarry.Carry.codeEquiv.injective
      exact hfour
    exact congrArg FiniteCarry.Carry.high hpoint

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def carryComplexCharacter (n : ℕ) (η : E n) : C(CarryGroup n, ℂ) where
  toFun z := (Additive.toMul η (Multiplicative.ofAdd z) : ℂ)
  continuous_toFun := continuous_subtype_val.comp (Additive.toMul η).continuous



/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem carryComplexCharacter_zero (n : ℕ) :
    carryComplexCharacter n 0 = 1 := by
  ext z
  rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem carryComplexCharacter_add
    (n : ℕ) (η θ : E n) :
    carryComplexCharacter n (η + θ) =
      carryComplexCharacter n η * carryComplexCharacter n θ := by
  ext z
  rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem carryComplexCharacter_star (n : ℕ) (η : E n) :
    star (carryComplexCharacter n η) = carryComplexCharacter n (-η) := by
  ext z
  exact (Circle.coe_inv_eq_conj
    (Additive.toMul η (Multiplicative.ofAdd z))).symm

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def carryCharacterSubalgebra (n : ℕ) :
    StarSubalgebra ℂ C(CarryGroup n, ℂ) where
  toSubalgebra := Algebra.adjoin ℂ (range (carryComplexCharacter n))
  star_mem' := by
    change Algebra.adjoin ℂ (range (carryComplexCharacter n)) ≤
      star (Algebra.adjoin ℂ (range (carryComplexCharacter n)))
    refine Algebra.adjoin_le ?_
    rintro _ ⟨η, rfl⟩
    exact Algebra.subset_adjoin ⟨-η, (carryComplexCharacter_star n η).symm⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem carryCharacterSubalgebra_toSubmodule (n : ℕ) :
    (carryCharacterSubalgebra n).toSubalgebra.toSubmodule =
      span ℂ (range (carryComplexCharacter n)) := by
  apply Algebra.adjoin_eq_span_of_subset
  refine Set.Subset.trans ?_ Submodule.subset_span
  intro z hz
  refine Submonoid.closure_induction (fun _ => id) ?_ ?_ hz
  · exact ⟨0, carryComplexCharacter_zero n⟩
  · rintro _ _ _ _ ⟨η, rfl⟩ ⟨θ, rfl⟩
    exact ⟨η + θ, carryComplexCharacter_add n η θ⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem carryComplexCharacter_span_closure_eq_top (n : ℕ) :
    (span ℂ (range (carryComplexCharacter n))).topologicalClosure = ⊤ := by
  have hsep : (carryCharacterSubalgebra n).SeparatesPoints := by
    intro x y hxy
    obtain ⟨η, hη⟩ := carry_pontryagin_characters_separate n x y hxy
    refine ⟨_, ⟨carryComplexCharacter n η,
      Algebra.subset_adjoin ⟨η, rfl⟩, rfl⟩, ?_⟩
    intro heq
    exact hη (Subtype.ext heq)
  rw [← carryCharacterSubalgebra_toSubmodule]
  exact congrArg (Subalgebra.toSubmodule ∘ StarSubalgebra.toSubalgebra)
    (ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
      (carryCharacterSubalgebra n) hsep)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def carryCharacterL2 (n : ℕ) (η : E n) : Lp ℂ 2 (carryHaar n) :=
  ContinuousMap.toLp 2 (carryHaar n) ℂ (carryComplexCharacter n η)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem carryCharacterL2_span_closure_eq_top (n : ℕ) :
    (span ℂ (range (carryCharacterL2 n))).topologicalClosure = ⊤ := by
  convert!
    (ContinuousMap.toLp_denseRange (p := (2 : ℝ≥0∞))
      ℂ (carryHaar n) ℂ (by simp only [ne_eq, ENNReal.ofNat_ne_top,
                              not_false_eq_true])).topologicalClosure_map_submodule
      (carryComplexCharacter_span_closure_eq_top n)
  rw [map_span]
  unfold carryCharacterL2
  rw [range_comp']
  simp only [ContinuousLinearMap.coe_coe]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem integral_add_character_eq_zero
    {G : Type*} [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsAddLeftInvariant]
    (χ : PontryaginDual (Multiplicative G)) (hχ : χ ≠ 1) :
    (∫ x : G, (χ (Multiplicative.ofAdd x) : ℂ) ∂μ) = 0 := by
  obtain ⟨g, hg⟩ : ∃ g : G, χ (Multiplicative.ofAdd g) ≠ 1 := by
    by_contra h
    push Not at h
    apply hχ
    apply PontryaginDual.ext
    intro g
    simpa only [PontryaginDual.one_apply, ofAdd_toAdd] using h (Multiplicative.toAdd g)
  have htrans :
      (χ (Multiplicative.ofAdd g) : ℂ) *
        (∫ x : G, (χ (Multiplicative.ofAdd x) : ℂ) ∂μ) =
        ∫ x : G, (χ (Multiplicative.ofAdd x) : ℂ) ∂μ := by
    calc
      (χ (Multiplicative.ofAdd g) : ℂ) *
          (∫ x : G, (χ (Multiplicative.ofAdd x) : ℂ) ∂μ) =
          ∫ x : G,
            (χ (Multiplicative.ofAdd g) : ℂ) *
              (χ (Multiplicative.ofAdd x) : ℂ) ∂μ :=
        (integral_const_mul (χ (Multiplicative.ofAdd g) : ℂ)
          (fun x : G => (χ (Multiplicative.ofAdd x) : ℂ))).symm
      _ = ∫ x : G, (χ (Multiplicative.ofAdd (g + x)) : ℂ) ∂μ := by
        congr 1
        funext x
        simp only [ofAdd_add, map_mul, Circle.coe_mul]
      _ = ∫ x : G, (χ (Multiplicative.ofAdd x) : ℂ) ∂μ :=
        integral_add_left_eq_self
          (fun x : G => (χ (Multiplicative.ofAdd x) : ℂ)) g
  have hzero :
      ((χ (Multiplicative.ofAdd g) : ℂ) - 1) *
        (∫ x : G, (χ (Multiplicative.ofAdd x) : ℂ) ∂μ) = 0 := by
    linear_combination htrans
  rcases mul_eq_zero.mp hzero with h | h
  · exfalso
    apply hg
    exact Circle.coe_eq_one.mp (sub_eq_zero.mp h)
  · exact h

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem carryCharacterL2_orthonormal (n : ℕ) :
    Orthonormal ℂ (carryCharacterL2 n) := by
  classical
  rw [orthonormal_iff_ite]
  intro η θ
  change inner ℂ
      (ContinuousMap.toLp 2 (carryHaar n) ℂ (carryComplexCharacter n η))
      (ContinuousMap.toLp 2 (carryHaar n) ℂ (carryComplexCharacter n θ)) =
    if η = θ then 1 else 0
  rw [ContinuousMap.inner_toLp (carryHaar n)
    (carryComplexCharacter n η) (carryComplexCharacter n θ)]
  split_ifs with h
  · subst θ
    have hpoint : ∀ x : CarryGroup n,
        (Additive.toMul η (Multiplicative.ofAdd x) : ℂ) *
          starRingEnd ℂ
            (Additive.toMul η (Multiplicative.ofAdd x) : ℂ) = 1 := by
      intro x
      rw [← Circle.coe_inv_eq_conj, ← Circle.coe_mul, mul_inv_cancel]
      rfl
    change
      (∫ x : CarryGroup n,
        (Additive.toMul η (Multiplicative.ofAdd x) : ℂ) *
          starRingEnd ℂ
            (Additive.toMul η (Multiplicative.ofAdd x) : ℂ)
          ∂carryHaar n) = 1
    simp_rw [hpoint]
    simp only [integral_const, probReal_univ, one_smul]
  · have hne :
        Additive.toMul θ * (Additive.toMul η)⁻¹ ≠ 1 := by
      intro he
      apply h
      apply Eq.symm
      apply Additive.toMul.injective
      exact mul_inv_eq_one.mp he
    have hz := integral_add_character_eq_zero
      (carryHaar n) (Additive.toMul θ * (Additive.toMul η)⁻¹) hne
    convert hz using 1
    congr 1
    funext x
    change
      (Additive.toMul θ (Multiplicative.ofAdd x) : ℂ) *
          starRingEnd ℂ
            (Additive.toMul η (Multiplicative.ofAdd x) : ℂ) =
        ((Additive.toMul θ (Multiplicative.ofAdd x) *
          (Additive.toMul η (Multiplicative.ofAdd x))⁻¹ : Circle) : ℂ)
    rw [Circle.coe_mul, Circle.coe_inv_eq_conj]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def carryFourierBasis (n : ℕ) :
    HilbertBasis (E n) ℂ (Lp ℂ 2 (carryHaar n)) :=
  HilbertBasis.mk (carryCharacterL2_orthonormal n)
    (carryCharacterL2_span_closure_eq_top n).ge



/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def carryFourierTransform (n : ℕ) :
    (lp (fun _ : E n => ℂ) 2) ≃ₗᵢ[ℂ] Lp ℂ 2 (carryHaar n) :=
  (carryFourierBasis n).repr.symm

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
abbrev carryFourierEquiv (n : ℕ) :
    (lp (fun _ : E n => ℂ) 2) ≃ₗᵢ[ℂ] Lp ℂ 2 (carryHaar n) :=
  carryFourierTransform n

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem carryFourierTransform_single (n : ℕ) [DecidableEq (E n)] (η : E n) :
    carryFourierTransform n (lp.single 2 η 1) = carryCharacterL2 n η := by
  exact Orthonormal.linearIsometryEquiv_symm_apply_single_one
    (carryCharacterL2_orthonormal n)
    (carryCharacterL2_span_closure_eq_top n).ge η

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem carryFourierEquiv_single (n : ℕ) [DecidableEq (E n)] (η : E n) :
    carryFourierEquiv n (lp.single 2 η 1) = carryCharacterL2 n η :=
  carryFourierTransform_single n η

end

section

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def carryBidualEvaluation (n : ℕ) (z : CarryGroup n) :
    PontryaginDual (Multiplicative (E n)) where
  toMonoidHom :=
    { toFun := fun η =>
        (η : PontryaginDual (Multiplicative (CarryGroup n)))
          (Multiplicative.ofAdd z)
      map_one' := rfl
      map_mul' _ _ := rfl }
  continuous_toFun := continuous_of_discreteTopology



/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem continuous_carryBidualEvaluation (n : ℕ) :
    Continuous (carryBidualEvaluation n) := by
  change Continuous
    (fun z : CarryGroup n =>
      (carryBidualEvaluation n z :
        (Multiplicative (E n)) →ₜ* Circle))
  apply ContinuousMonoidHom.continuous_of_continuous_uncurry
  apply continuous_prod_of_discrete_right.mpr
  intro η
  exact (η : PontryaginDual (Multiplicative (CarryGroup n))).continuous

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem carryBidualEvaluation_injective (n : ℕ) :
    Function.Injective (carryBidualEvaluation n) := by
  intro x y hxy
  by_contra hne
  obtain ⟨η, hη⟩ := carry_pontryagin_characters_separate n x y hne
  exact hη (DFunLike.congr_fun hxy (Multiplicative.ofAdd η))

namespace CarryBidualInternal

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
local instance vectorDiscreteTopology : TopologicalSpace V := ⊥
/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
local instance vectorDiscrete : DiscreteTopology V := ⟨rfl⟩
/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
local instance dividedSquareDiscreteTopology : TopologicalSpace B := ⊥
/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
local instance dividedSquareDiscrete : DiscreteTopology B := ⟨rfl⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def restrictIota (n : ℕ)
    (φ : PontryaginDual (Multiplicative (E n))) :
    PontryaginDual (Multiplicative V) where
  toMonoidHom := φ.toMonoidHom.comp (iota n).toMultiplicative
  continuous_toFun := continuous_of_discreteTopology

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def linearCoord (n : ℕ)
    (φ : PontryaginDual (Multiplicative (E n))) : X :=
  characterLinear V (restrictIota n φ)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem linearCoord_spec (n : ℕ)
    (φ : PontryaginDual (Multiplicative (E n))) (v : V) :
    ZMod.toCircle (linearCoord n φ v) =
      φ (Multiplicative.ofAdd (iota n v)) :=
  characterLinear_circle V (restrictIota n φ) v

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def linearCandidate (n : ℕ)
    (φ : PontryaginDual (Multiplicative (E n))) : CarryGroup n :=
  ⟨linearCoord n φ, 0⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def residualCharacter (n : ℕ)
    (φ : PontryaginDual (Multiplicative (E n))) :
    PontryaginDual (Multiplicative (E n)) :=
  φ * (carryBidualEvaluation n (linearCandidate n φ))⁻¹

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem residual_iota (n : ℕ)
    (φ : PontryaginDual (Multiplicative (E n))) (v : V) :
    residualCharacter n φ (Multiplicative.ofAdd (iota n v)) = 1 := by
  change φ (Multiplicative.ofAdd (iota n v)) *
    (ZMod.toCircle (linearCoord n φ v))⁻¹ = 1
  rw [linearCoord_spec]
  exact mul_inv_cancel _

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def sigmaMultiplicative (n : ℕ) :
    Multiplicative (E n) →* Multiplicative B :=
  (sigma n).toMultiplicative

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem sigmaMultiplicative_surjective (n : ℕ) :
    Function.Surjective (sigmaMultiplicative n) := by
  intro b
  obtain ⟨η, hη⟩ := sigma_surjective n (Multiplicative.toAdd b)
  exact ⟨Multiplicative.ofAdd η,
    Multiplicative.toAdd.injective hη⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem residual_ker (n : ℕ)
    (φ : PontryaginDual (Multiplicative (E n))) :
    (sigmaMultiplicative n).ker ≤ (residualCharacter n φ).toMonoidHom.ker := by
  intro η hη
  change sigma n (Multiplicative.toAdd η) = 0 at hη
  have hmem : Multiplicative.toAdd η ∈ (sigma n).ker := hη
  rw [sigma_ker] at hmem
  obtain ⟨v, hv⟩ := hmem
  have hηv : η = Multiplicative.ofAdd (iota n v) := by
    apply Multiplicative.toAdd.injective
    exact hv.symm
  change residualCharacter n φ η = 1
  rw [hηv]
  exact residual_iota n φ v

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def residualOnB (n : ℕ)
    (φ : PontryaginDual (Multiplicative (E n))) :
    Multiplicative B →* Circle :=
  (sigmaMultiplicative n).liftOfRightInverseAux
    (Function.surjInv (sigmaMultiplicative_surjective n))
    (Function.rightInverse_surjInv (sigmaMultiplicative_surjective n))
    (residualCharacter n φ).toMonoidHom
    (residual_ker n φ)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem residualOnB_sigma (n : ℕ)
    (φ : PontryaginDual (Multiplicative (E n))) (η : E n) :
    residualOnB n φ (Multiplicative.ofAdd (sigma n η)) =
      residualCharacter n φ (Multiplicative.ofAdd η) := by
  change residualOnB n φ
      (sigmaMultiplicative n (Multiplicative.ofAdd η)) =
    (residualCharacter n φ).toMonoidHom (Multiplicative.ofAdd η)
  unfold residualOnB
  exact MonoidHom.liftOfRightInverseAux_comp_apply _ _ _ _ _ _

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def residualBCharacter (n : ℕ)
    (φ : PontryaginDual (Multiplicative (E n))) :
    PontryaginDual (Multiplicative B) where
  toMonoidHom := residualOnB n φ
  continuous_toFun := continuous_of_discreteTopology

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def quadraticCoord (n : ℕ)
    (φ : PontryaginDual (Multiplicative (E n))) : Y :=
  characterLinear B (residualBCharacter n φ)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem quadraticCoord_spec (n : ℕ)
    (φ : PontryaginDual (Multiplicative (E n))) (η : E n) :
    ZMod.toCircle (quadraticCoord n φ (sigma n η)) =
      residualCharacter n φ (Multiplicative.ofAdd η) := by
  change ZMod.toCircle
    (characterLinear B (residualBCharacter n φ) (sigma n η)) = _
  rw [characterLinear_circle]
  exact residualOnB_sigma n φ η

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem evaluation_surjective (n : ℕ) :
    Function.Surjective (carryBidualEvaluation n) := by
  intro φ
  let l : X := linearCoord n φ
  let q : Y := quadraticCoord n φ
  let z : CarryGroup n := ⟨l, q⟩
  refine ⟨z, ?_⟩
  apply PontryaginDual.ext
  intro η
  let η' : E n := Multiplicative.toAdd η
  have hdecomp : z = linearCandidate n φ + carryKernelInclusion n q := by
    apply CarryGroup.ext <;> simp [z, l, q, linearCandidate]
  change evalEta η' z = φ η
  rw [hdecomp, evalEta_add]
  have hquad : evalEta η' (carryKernelInclusion n q) =
      residualCharacter n φ (Multiplicative.ofAdd η') := by
    calc
      _ = ZMod.toCircle (q (sigma n η')) :=
        (sigma_characterization n η' q).symm
      _ = residualCharacter n φ (Multiplicative.ofAdd η') :=
        quadraticCoord_spec n φ η'
  rw [hquad]
  change carryBidualEvaluation n (linearCandidate n φ)
      (Multiplicative.ofAdd η') *
      (φ (Multiplicative.ofAdd η') *
        (carryBidualEvaluation n (linearCandidate n φ)
          (Multiplicative.ofAdd η'))⁻¹) = φ η
  change carryBidualEvaluation n (linearCandidate n φ) η *
      (φ η * (carryBidualEvaluation n (linearCandidate n φ) η)⁻¹) = φ η
  simp only [mul_left_comm, mul_inv_cancel, mul_comm, one_mul]

end CarryBidualInternal

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem carryBidualEvaluation_surjective (n : ℕ) :
    Function.Surjective (carryBidualEvaluation n) :=
  CarryBidualInternal.evaluation_surjective n

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
noncomputable def carryBidualEquiv (n : ℕ) :
    CarryGroup n ≃ PontryaginDual (Multiplicative (E n)) :=
  Equiv.ofBijective (carryBidualEvaluation n)
    ⟨carryBidualEvaluation_injective n, carryBidualEvaluation_surjective n⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
noncomputable def carryBidualHomeomorph (n : ℕ) :
    CarryGroup n ≃ₜ PontryaginDual (Multiplicative (E n)) :=
  (continuous_carryBidualEvaluation n).homeoOfEquivCompactToT2
    (f := carryBidualEquiv n)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
public
theorem carryBidualHomeomorph_apply
    (n : ℕ) (z : CarryGroup n) (η : E n) :
    carryBidualHomeomorph n z (Multiplicative.ofAdd η) =
      Additive.toMul η (Multiplicative.ofAdd z) := rfl

end

section

open Set Submodule MeasureTheory
open scoped ENNReal Topology

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def splitBinaryEvaluation (d : D) : (X × Y) →+ F where
  toFun z := z.1 d.1 + z.2 d.2
  map_zero' := by simp only [Prod.fst_zero, LinearMap.zero_apply, Prod.snd_zero, add_zero]
  map_add' z w := by
    change (z.1 d.1 + w.1 d.1) + (z.2 d.2 + w.2 d.2) =
      (z.1 d.1 + z.2 d.2) + (w.1 d.1 + w.2 d.2)
    ac_rfl



/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem continuous_splitBinaryEvaluation (d : D) :
    Continuous (splitBinaryEvaluation d : X × Y → F) :=
  ((continuous_X_eval d.1).comp continuous_fst).add
    ((continuous_Y_eval d.2).comp continuous_snd)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def splitPontryaginCharacter (d : D) :
    PontryaginDual (Multiplicative (X × Y)) where
  toMonoidHom :=
    (AddChar.toMonoidHomEquiv (ZMod.toCircle (N := 2))).comp
      (splitBinaryEvaluation d).toMultiplicative
  continuous_toFun :=
    (continuous_of_discreteTopology :
      Continuous (fun a : F => (ZMod.toCircle a : Circle))).comp
        (continuous_splitBinaryEvaluation d)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem splitPontryaginCharacter_apply (d : D) (z : X × Y) :
    splitPontryaginCharacter d (Multiplicative.ofAdd z) =
      ZMod.toCircle (z.1 d.1 + z.2 d.2) := rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem splitPontryaginCharacter_injective :
    Function.Injective splitPontryaginCharacter := by
  intro d d' h
  apply Prod.ext
  · apply Module.eval_apply_injective F
    apply LinearMap.ext
    intro ℓ
    apply ZMod.injective_toCircle
    have hpoint := DFunLike.congr_fun h
      (Multiplicative.ofAdd (ℓ, (0 : Y)))
    simpa only [Module.Dual.eval_apply, splitPontryaginCharacter_apply, LinearMap.zero_apply,
      add_zero] using hpoint
  · apply Module.eval_apply_injective F
    apply LinearMap.ext
    intro q
    apply ZMod.injective_toCircle
    have hpoint := DFunLike.congr_fun h
      (Multiplicative.ofAdd ((0 : X), q))
    simpa only [Module.Dual.eval_apply, splitPontryaginCharacter_apply, LinearMap.zero_apply,
      zero_add] using hpoint

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem splitPontryaginCharacter_separates
    (z w : X × Y) (hzw : z ≠ w) :
    ∃ d : D,
      splitPontryaginCharacter d (Multiplicative.ofAdd z) ≠
        splitPontryaginCharacter d (Multiplicative.ofAdd w) := by
  by_contra h
  push Not at h
  apply hzw
  apply Prod.ext
  · apply LinearMap.ext
    intro v
    apply ZMod.injective_toCircle
    simpa only [splitPontryaginCharacter_apply, map_zero, add_zero] using h (v, (0 : B))
  · apply LinearMap.ext
    intro b
    apply ZMod.injective_toCircle
    simpa only [splitPontryaginCharacter_apply, map_zero, zero_add] using h ((0 : V), b)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def splitComplexCharacter (d : D) : C(X × Y, ℂ) where
  toFun z := (splitPontryaginCharacter d (Multiplicative.ofAdd z) : ℂ)
  continuous_toFun := continuous_subtype_val.comp
    (splitPontryaginCharacter d).continuous



/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
public
theorem splitComplexCharacter_zero : splitComplexCharacter 0 = 1 := by
  ext z
  simp only [splitComplexCharacter, splitPontryaginCharacter_apply, Prod.fst_zero, map_zero,
    Prod.snd_zero, add_zero, AddChar.map_zero_eq_one, Circle.coe_one, ContinuousMap.coe_mk,
    ContinuousMap.one_apply]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem splitComplexCharacter_add (d e : D) :
    splitComplexCharacter (d + e) =
      splitComplexCharacter d * splitComplexCharacter e := by
  ext z
  change (ZMod.toCircle
    (z.1 (d.1 + e.1) + z.2 (d.2 + e.2)) : ℂ) = _
  rw [z.1.map_add d.1 e.1, z.2.map_add d.2 e.2]
  rw [show z.1 d.1 + z.1 e.1 + (z.2 d.2 + z.2 e.2) =
    (z.1 d.1 + z.2 d.2) + (z.1 e.1 + z.2 e.2) by ac_rfl]
  rw [AddChar.map_add_eq_mul]
  rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem splitComplexCharacter_star (d : D) :
    star (splitComplexCharacter d) = splitComplexCharacter (-d) := by
  ext z
  change star (ZMod.toCircle (z.1 d.1 + z.2 d.2) : ℂ) =
    (ZMod.toCircle (z.1 (-d.1) + z.2 (-d.2)) : ℂ)
  rw [z.1.map_neg d.1, z.2.map_neg d.2, ← neg_add]
  rw [AddChar.map_neg_eq_inv]
  exact (Circle.coe_inv_eq_conj
    (ZMod.toCircle (z.1 d.1 + z.2 d.2))).symm

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def splitCharacterSubalgebra : StarSubalgebra ℂ C(X × Y, ℂ) where
  toSubalgebra := Algebra.adjoin ℂ (range splitComplexCharacter)
  star_mem' := by
    change Algebra.adjoin ℂ (range splitComplexCharacter) ≤
      star (Algebra.adjoin ℂ (range splitComplexCharacter))
    refine Algebra.adjoin_le ?_
    rintro _ ⟨d, rfl⟩
    exact Algebra.subset_adjoin ⟨-d, (splitComplexCharacter_star d).symm⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem splitCharacterSubalgebra_toSubmodule :
    splitCharacterSubalgebra.toSubalgebra.toSubmodule =
      span ℂ (range splitComplexCharacter) := by
  apply Algebra.adjoin_eq_span_of_subset
  refine Set.Subset.trans ?_ Submodule.subset_span
  intro z hz
  refine Submonoid.closure_induction (fun _ => id) ?_ ?_ hz
  · exact ⟨0, splitComplexCharacter_zero⟩
  · rintro _ _ _ _ ⟨d, rfl⟩ ⟨e, rfl⟩
    exact ⟨d + e, splitComplexCharacter_add d e⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem splitComplexCharacter_span_closure_eq_top :
    (span ℂ (range splitComplexCharacter)).topologicalClosure = ⊤ := by
  have hsep : splitCharacterSubalgebra.SeparatesPoints := by
    intro z w hzw
    obtain ⟨d, hd⟩ := splitPontryaginCharacter_separates z w hzw
    refine ⟨_, ⟨splitComplexCharacter d,
      Algebra.subset_adjoin ⟨d, rfl⟩, rfl⟩, ?_⟩
    intro heq
    exact hd (Subtype.ext heq)
  rw [← splitCharacterSubalgebra_toSubmodule]
  exact congrArg (Subalgebra.toSubmodule ∘ StarSubalgebra.toSubalgebra)
    (ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
      splitCharacterSubalgebra hsep)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def splitCharacterL2 (d : D) : Lp ℂ 2 productHaar :=
  ContinuousMap.toLp 2 productHaar ℂ (splitComplexCharacter d)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem splitCharacterL2_span_closure_eq_top :
    (span ℂ (range splitCharacterL2)).topologicalClosure = ⊤ := by
  convert!
    (ContinuousMap.toLp_denseRange (p := (2 : ℝ≥0∞))
      ℂ productHaar ℂ (by simp only [ne_eq, ENNReal.ofNat_ne_top,
                            not_false_eq_true])).topologicalClosure_map_submodule
      splitComplexCharacter_span_closure_eq_top
  rw [map_span]
  unfold splitCharacterL2
  rw [range_comp']
  simp only [ContinuousLinearMap.coe_coe]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem split_integral_character_eq_zero
    {G : Type*} [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsAddLeftInvariant]
    (χ : PontryaginDual (Multiplicative G)) (hχ : χ ≠ 1) :
    (∫ z : G, (χ (Multiplicative.ofAdd z) : ℂ) ∂μ) = 0 := by
  obtain ⟨g, hg⟩ : ∃ g : G, χ (Multiplicative.ofAdd g) ≠ 1 := by
    by_contra h
    push Not at h
    apply hχ
    apply PontryaginDual.ext
    intro g
    simpa only [PontryaginDual.one_apply, ofAdd_toAdd] using h (Multiplicative.toAdd g)
  have htrans :
      (χ (Multiplicative.ofAdd g) : ℂ) *
        (∫ z : G, (χ (Multiplicative.ofAdd z) : ℂ) ∂μ) =
        ∫ z : G, (χ (Multiplicative.ofAdd z) : ℂ) ∂μ := by
    calc
      _ = ∫ z : G,
          (χ (Multiplicative.ofAdd g) : ℂ) *
            (χ (Multiplicative.ofAdd z) : ℂ) ∂μ :=
        (integral_const_mul (χ (Multiplicative.ofAdd g) : ℂ)
          (fun z : G => (χ (Multiplicative.ofAdd z) : ℂ))).symm
      _ = ∫ z : G, (χ (Multiplicative.ofAdd (g + z)) : ℂ) ∂μ := by
        congr 1
        funext z
        simp only [ofAdd_add, map_mul, Circle.coe_mul]
      _ = ∫ z : G, (χ (Multiplicative.ofAdd z) : ℂ) ∂μ :=
        integral_add_left_eq_self
          (fun z : G => (χ (Multiplicative.ofAdd z) : ℂ)) g
  have hzero :
      ((χ (Multiplicative.ofAdd g) : ℂ) - 1) *
        (∫ z : G, (χ (Multiplicative.ofAdd z) : ℂ) ∂μ) = 0 := by
    linear_combination htrans
  rcases mul_eq_zero.mp hzero with h | h
  · exfalso
    apply hg
    exact Circle.coe_eq_one.mp (sub_eq_zero.mp h)
  · exact h

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem splitCharacterL2_orthonormal : Orthonormal ℂ splitCharacterL2 := by
  classical
  rw [orthonormal_iff_ite]
  intro d e
  change inner ℂ
      (ContinuousMap.toLp 2 productHaar ℂ (splitComplexCharacter d))
      (ContinuousMap.toLp 2 productHaar ℂ (splitComplexCharacter e)) =
    if d = e then 1 else 0
  rw [ContinuousMap.inner_toLp productHaar
    (splitComplexCharacter d) (splitComplexCharacter e)]
  split_ifs with h
  · subst e
    have hpoint : ∀ z : X × Y,
        (splitPontryaginCharacter d (Multiplicative.ofAdd z) : ℂ) *
          starRingEnd ℂ
            (splitPontryaginCharacter d (Multiplicative.ofAdd z) : ℂ) = 1 := by
      intro z
      rw [← Circle.coe_inv_eq_conj, ← Circle.coe_mul, mul_inv_cancel]
      rfl
    change
      (∫ z : X × Y,
        (splitPontryaginCharacter d (Multiplicative.ofAdd z) : ℂ) *
          starRingEnd ℂ
            (splitPontryaginCharacter d (Multiplicative.ofAdd z) : ℂ)
          ∂productHaar) = 1
    simp_rw [hpoint]
    simp only [integral_const, probReal_univ, one_smul]
  · have hne :
        splitPontryaginCharacter e * (splitPontryaginCharacter d)⁻¹ ≠ 1 := by
      intro he
      apply h
      apply Eq.symm
      apply splitPontryaginCharacter_injective
      exact mul_inv_eq_one.mp he
    have hz := split_integral_character_eq_zero
      productHaar
      (splitPontryaginCharacter e * (splitPontryaginCharacter d)⁻¹) hne
    convert hz using 1
    congr 1
    funext z
    change
      (splitPontryaginCharacter e (Multiplicative.ofAdd z) : ℂ) *
          starRingEnd ℂ
            (splitPontryaginCharacter d (Multiplicative.ofAdd z) : ℂ) =
        ((splitPontryaginCharacter e (Multiplicative.ofAdd z) *
          (splitPontryaginCharacter d (Multiplicative.ofAdd z))⁻¹ : Circle) : ℂ)
    rw [Circle.coe_mul, Circle.coe_inv_eq_conj]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def splitFourierBasis : HilbertBasis D ℂ (Lp ℂ 2 productHaar) :=
  HilbertBasis.mk splitCharacterL2_orthonormal
    splitCharacterL2_span_closure_eq_top.ge



/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def splitFourierTransform :
    (lp (fun _ : D => ℂ) 2) ≃ₗᵢ[ℂ] Lp ℂ 2 productHaar :=
  splitFourierBasis.repr.symm

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
abbrev splitFourierEquiv :
    (lp (fun _ : D => ℂ) 2) ≃ₗᵢ[ℂ] Lp ℂ 2 productHaar :=
  splitFourierTransform

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem splitFourierEquiv_single [DecidableEq D] (d : D) :
    splitFourierEquiv (lp.single 2 d 1) = splitCharacterL2 d := by
  exact Orthonormal.linearIsometryEquiv_symm_apply_single_one
    splitCharacterL2_orthonormal splitCharacterL2_span_closure_eq_top.ge d

end

section

open ConnesRigidity

universe u v w

section

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def groupFactorEquivSymm
    {G : CountableDiscreteGroup.{u}}
    {H : CountableDiscreteGroup.{v}}
    (e : TracialGroupFactorEquiv G H) :
    TracialGroupFactorEquiv H G where
  toStarAlgEquiv := e.toStarAlgEquiv.symm
  normal := by
    exact ⟨e.normal.2, e.normal.1⟩
  trace_preserving := by
    intro y
    have h := e.trace_preserving (e.toStarAlgEquiv.symm y)
    simpa only [StarAlgEquiv.apply_symm_apply] using h.symm

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def groupFactorEquivTrans
    {G : CountableDiscreteGroup.{u}}
    {H : CountableDiscreteGroup.{v}}
    {J : CountableDiscreteGroup.{w}}
    (e : TracialGroupFactorEquiv G H)
    (f : TracialGroupFactorEquiv H J) :
    TracialGroupFactorEquiv G J where
  toStarAlgEquiv := e.toStarAlgEquiv.trans f.toStarAlgEquiv
  normal := by
    constructor
    · intro S p hp
      have he := e.normal.1 S p hp
      have hf := f.normal.1 (e.toStarAlgEquiv '' S) (e.toStarAlgEquiv p) he
      change
        IsProjectionSupremum
          ((fun x ↦ f.toStarAlgEquiv (e.toStarAlgEquiv x)) '' S)
          (f.toStarAlgEquiv (e.toStarAlgEquiv p))
      simpa only [Set.image_image] using hf
    · intro S p hp
      have hf := f.normal.2 S p hp
      have he :=
        e.normal.2 (f.toStarAlgEquiv.symm '' S) (f.toStarAlgEquiv.symm p) hf
      change
        IsProjectionSupremum
          ((fun x ↦ e.toStarAlgEquiv.symm (f.toStarAlgEquiv.symm x)) '' S)
          (e.toStarAlgEquiv.symm (f.toStarAlgEquiv.symm p))
      simpa only [Set.image_image] using he
  trace_preserving := by
    intro x
    change
      canonicalTrace J (f.toStarAlgEquiv (e.toStarAlgEquiv x)) =
        canonicalTrace G x
    rw [f.trace_preserving, e.trace_preserving]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem groupFactorsIsomorphic_symm
    {G : CountableDiscreteGroup.{u}}
    {H : CountableDiscreteGroup.{v}}
    (h : TracialGroupFactorsIsomorphic G H) :
    TracialGroupFactorsIsomorphic H G := by
  obtain ⟨e⟩ := h
  exact ⟨groupFactorEquivSymm e⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem groupFactorsIsomorphic_trans
    {G : CountableDiscreteGroup.{u}}
    {H : CountableDiscreteGroup.{v}}
    {J : CountableDiscreteGroup.{w}}
    (hGH : TracialGroupFactorsIsomorphic G H)
    (hHJ : TracialGroupFactorsIsomorphic H J) :
    TracialGroupFactorsIsomorphic G J := by
  obtain ⟨e⟩ := hGH
  obtain ⟨f⟩ := hHJ
  exact ⟨groupFactorEquivTrans e f⟩

end

end

section

open ConnesRigidity MeasureTheory

universe u v w x y

section

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
structure HaarProbabilityAction
    (K : Type u) (Ω : Type v)
    [Group K] [AddCommGroup Ω] [TopologicalSpace Ω] [MeasurableSpace Ω] where
  /-- The invariant probability measure. -/
  measure : Measure Ω
  haar : Measure.IsAddHaarMeasure measure
  probability : IsProbabilityMeasure measure
  /-- The group action on the measured group. -/
  action : K →* Equiv.Perm Ω
  action_add :
    ∀ (k : K) (z z' : Ω), action k (z + z') = action k z + action k z'
  action_preserves_measure :
    ∀ k : K, MeasurePreserving (action k : Ω → Ω) measure measure

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
structure EquivariantHaarEquiv
    {K : Type u} {Ω : Type v} {Ξ : Type w}
    [Group K]
    [AddCommGroup Ω] [TopologicalSpace Ω] [MeasurableSpace Ω]
    [AddCommGroup Ξ] [TopologicalSpace Ξ] [MeasurableSpace Ξ]
    (X : HaarProbabilityAction K Ω)
    (Y : HaarProbabilityAction K Ξ) where
  /-- The underlying measurable equivalence. -/
  toMeasurableEquiv : Ω ≃ᵐ Ξ
  measure_preserving :
    MeasurePreserving toMeasurableEquiv X.measure Y.measure
  equivariant :
    ∀ (k : K) (z : Ω),
      toMeasurableEquiv (X.action k z) =
        Y.action k (toMeasurableEquiv z)

namespace EquivariantHaarEquiv

variable {K : Type u} {Ω : Type v} {Ξ : Type w} {Ζ : Type x}
variable [Group K]
variable [AddCommGroup Ω] [TopologicalSpace Ω] [MeasurableSpace Ω]
variable [AddCommGroup Ξ] [TopologicalSpace Ξ] [MeasurableSpace Ξ]
variable [AddCommGroup Ζ] [TopologicalSpace Ζ] [MeasurableSpace Ζ]

/-- The identity equivariant equivalence. -/
@[expose]
public
def refl (X : HaarProbabilityAction K Ω) : EquivariantHaarEquiv X X where
  toMeasurableEquiv := MeasurableEquiv.refl Ω
  measure_preserving := MeasurePreserving.id X.measure
  equivariant := by
    intro k z
    rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def symm
    {X : HaarProbabilityAction K Ω}
    {Y : HaarProbabilityAction K Ξ}
    (e : EquivariantHaarEquiv X Y) :
    EquivariantHaarEquiv Y X where
  toMeasurableEquiv := e.toMeasurableEquiv.symm
  measure_preserving :=
    MeasurePreserving.symm e.toMeasurableEquiv e.measure_preserving
  equivariant := by
    intro k z
    apply e.toMeasurableEquiv.injective
    simpa only [MeasurableEquiv.apply_symm_apply] using
      (e.equivariant k (e.toMeasurableEquiv.symm z)).symm

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def trans
    {X : HaarProbabilityAction K Ω}
    {Y : HaarProbabilityAction K Ξ}
    {Z : HaarProbabilityAction K Ζ}
    (e : EquivariantHaarEquiv X Y)
    (f : EquivariantHaarEquiv Y Z) :
    EquivariantHaarEquiv X Z where
  toMeasurableEquiv := e.toMeasurableEquiv.trans f.toMeasurableEquiv
  measure_preserving := e.measure_preserving.trans f.measure_preserving
  equivariant := by
    intro k z
    change
      f.toMeasurableEquiv (e.toMeasurableEquiv (X.action k z)) =
        Z.action k (f.toMeasurableEquiv (e.toMeasurableEquiv z))
    rw [e.equivariant k z,
      f.equivariant k (e.toMeasurableEquiv z)]

end EquivariantHaarEquiv

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
structure CrossedProductModel
    (ℋ : Type v)
    [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] where
  /-- The modeled von Neumann algebra. -/
  algebra : VonNeumannAlgebra ℋ
  /-- The trace on the modeled algebra. -/
  trace : algebra.toStarSubalgebra → ℂ

end

end

section

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
instance : Countable B := by
  change Countable (Submodule.span F (Set.range square))
  infer_instance

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
instance : Countable D := inferInstance

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
instance : Countable (Multiplicative D) :=
  (Multiplicative.toAdd (α := D)).injective.countable

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def kLinear : K →* (V ≃ₗ[F] V) where
  toFun k := (Matrix.SpecialLinearGroup.toLin' (pi₂ k)).restrictScalars F
  map_one' := by
    apply LinearEquiv.ext
    intro v
    change Matrix.SpecialLinearGroup.toLin' (pi₂ 1) v = v
    simp only [map_one, LinearEquiv.coe_one, id_eq]
  map_mul' k l := by
    apply LinearEquiv.ext
    intro v
    change Matrix.SpecialLinearGroup.toLin' (pi₂ (k * l)) v =
      Matrix.SpecialLinearGroup.toLin' (pi₂ k)
        (Matrix.SpecialLinearGroup.toLin' (pi₂ l) v)
    rw [map_mul, map_mul]
    rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem kLinear_apply (k : K) (v : V) :
    kLinear k v = Matrix.SpecialLinearGroup.toLin' (pi₂ k) v := rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def kTensorLinear : K →* (T ≃ₗ[F] T) where
  toFun k := TensorProduct.congr (kLinear k) (kLinear k)
  map_one' := by
    change TensorProduct.congr (kLinear (1 : K)) (kLinear (1 : K)) =
      LinearEquiv.refl F T
    rw [map_one]
    exact TensorProduct.congr_refl_refl
  map_mul' k l := by
    rw [map_mul, TensorProduct.congr_mul]



/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem kTensorLinear_square (k : K) (v : V) :
    kTensorLinear k (square v) = square (kLinear k v) := rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem kTensorLinear_map_B (k : K) :
    B.map (kTensorLinear k).toLinearMap = B := by
  rw [B, Submodule.map_span]
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
    exact square_mem (kLinear k v)
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨v, rfl⟩
    apply Submodule.subset_span
    refine ⟨square ((kLinear k).symm v), ⟨_, rfl⟩, ?_⟩
    simp only [LinearEquiv.coe_coe, kTensorLinear_square, LinearEquiv.apply_symm_apply]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def kDividedSquareLinear : K →* (B ≃ₗ[F] B) where
  toFun k := (kTensorLinear k).ofSubmodules B B (kTensorLinear_map_B k)
  map_one' := by
    ext b
    change kTensorLinear 1 (b : T) = (b : T)
    simp only [map_one, LinearEquiv.coe_one, id_eq]
  map_mul' k l := by
    ext b
    change kTensorLinear (k * l) (b : T) =
      kTensorLinear k (kTensorLinear l (b : T))
    rw [map_mul]
    rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
public
theorem kDividedSquareLinear_val (k : K) (b : B) :
    (kDividedSquareLinear k b : T) = kTensorLinear k (b : T) := rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
public
theorem kDividedSquareLinear_diagonal (k : K) (v : V) :
    kDividedSquareLinear k (diagonal v) = diagonal (kLinear k v) := by
  apply Subtype.ext
  exact kTensorLinear_square k v



/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def kDLinear : K →* (D ≃ₗ[F] D) where
  toFun k := (kLinear k).prodCongr (kDividedSquareLinear k)
  map_one' := by
    ext d <;> simp
  map_mul' k l := by
    ext d <;> simp



/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def kDAction : K →* MulAut (Multiplicative D) where
  toFun k := AddEquiv.toMultiplicative (kDLinear k).toAddEquiv
  map_one' := by
    apply MulEquiv.ext
    intro d
    change kDLinear 1 (Multiplicative.toAdd d) = Multiplicative.toAdd d
    simp only [map_one, LinearEquiv.coe_one, id_eq]
  map_mul' k l := by
    apply MulEquiv.ext
    intro d
    change kDLinear (k * l) (Multiplicative.toAdd d) =
      kDLinear k (kDLinear l (Multiplicative.toAdd d))
    rw [map_mul]
    rfl



/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
abbrev Lambda := SemidirectProduct (Multiplicative D) K kDAction

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
instance : Countable Lambda := SemidirectProduct.equivProd.injective.countable

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def lambdaGroup : ConnesRigidity.CountableDiscreteGroup where
  Carrier := Lambda
  group := inferInstance
  countable := inferInstance



/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
abbrev lambdaInl : Multiplicative D →* Lambda := SemidirectProduct.inl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
abbrev lambdaInr : K →* Lambda := SemidirectProduct.inr

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
abbrev lambdaProjection : Lambda →* K := SemidirectProduct.rightHom





/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem lambda_conjugation (k : K) (d : Multiplicative D) :
    lambdaInl (kDAction k d) = lambdaInr k * lambdaInl d * (lambdaInr k)⁻¹ := by
  simpa only [map_inv] using (SemidirectProduct.inl_aut (φ := kDAction) k d)

end

section

open ConnesRigidity

universe u

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
structure GroupCardinalInvariant where
  /-- The type assigned to each group. -/
  carrier : CountableDiscreteGroup.{u} → Type u
  /-- Transport of the invariant along a group equivalence. -/
  mapMulEquiv : ∀ {G H : CountableDiscreteGroup.{u}},
    (G ≃* H) → carrier G ≃ carrier H

namespace GroupCardinalInvariant

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
noncomputable def value (I : GroupCardinalInvariant.{u})
    (G : CountableDiscreteGroup.{u}) : ℕ :=
  Nat.card (I.carrier G)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem value_mulEquiv (I : GroupCardinalInvariant.{u})
    {G H : CountableDiscreteGroup.{u}} (e : G ≃* H) :
    I.value G = I.value H :=
  Nat.card_congr (I.mapMulEquiv e)

end GroupCardinalInvariant

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem paperInvariantCard_injective {m n : ℕ}
    (h : 2 ^ (4 * m) = 2 ^ (4 * n)) : m = n := by
  have hmul : 4 * m = 4 * n :=
    Nat.pow_right_injective (by decide : 2 ≤ (2 : ℕ)) h
  exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < (4 : ℕ)) hmul

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
structure ExactIndexEmbedding
    (G H : CountableDiscreteGroup.{u}) (index : ℕ) where
  /-- The underlying group homomorphism. -/
  hom : G →* H
  injective : Function.Injective hom
  index_eq : hom.range.index = index

namespace ExactIndexEmbedding

variable {G H : CountableDiscreteGroup.{u}} {index : ℕ}

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private noncomputable def rangeEquiv (f : ExactIndexEmbedding G H index) :
    G ≃* f.hom.range :=
  MonoidHom.ofInjective f.injective

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem range_finiteIndex (f : ExactIndexEmbedding G H index)
    (hindex : index ≠ 0) : f.hom.range.FiniteIndex :=
  Subgroup.finiteIndex_iff.mpr (by simpa only [f.index_eq, ne_eq] using hindex)

end ExactIndexEmbedding

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def AbstractlyCommensurable
    (G H : CountableDiscreteGroup.{u}) : Prop :=
  ∃ (S : Subgroup G) (T : Subgroup H),
    S.FiniteIndex ∧ T.FiniteIndex ∧ Nonempty (S ≃* T)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem abstractlyCommensurable_of_common_embedding
    {A G H : CountableDiscreteGroup.{u}} {i j : ℕ}
    (f : ExactIndexEmbedding A G i) (g : ExactIndexEmbedding A H j)
    (hi : i ≠ 0) (hj : j ≠ 0) :
    AbstractlyCommensurable G H := by
  refine ⟨f.hom.range, g.hom.range,
    f.range_finiteIndex hi, g.range_finiteIndex hj, ?_⟩
  exact ⟨f.rangeEquiv.symm.trans g.rangeEquiv⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem not_groupsIsomorphic_of_orderFour
    {G H : CountableDiscreteGroup.{u}}
    (hG : ∃ g : G, orderOf g = 4)
    (hH : ∀ h : H, orderOf h ≠ 4) :
    ¬GroupsIsomorphic G H := by
  rintro ⟨e⟩
  obtain ⟨g, hg⟩ := hG
  exact hH (e g) (by simpa only [MulEquiv.orderOf_eq] using (e.orderOf_eq g).trans hg)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
structure PaperFamilyInput where
  /-- The distinguished group in the family. -/
  Lambda : CountableDiscreteGroup.{u}
  /-- The indexed groups in the family. -/
  Gamma : ℕ → CountableDiscreteGroup.{u}
  /-- The cardinal invariant separating the indexed groups. -/
  invariant : GroupCardinalInvariant.{u}
  invariant_card : ∀ n, invariant.value (Gamma n) = 2 ^ (4 * n)
  lambda_no_order_four : ∀ g : Lambda, orderOf g ≠ 4
  gamma_order_four : ∀ n, ∃ g : Gamma n, orderOf g = 4
  lambda_fg : Group.FG Lambda
  gamma_fg : ∀ n, Group.FG (Gamma n)
  lambda_icc : IsICC Lambda
  gamma_icc : ∀ n, IsICC (Gamma n)
  lambda_propertyT : HasKazhdanPropertyT Lambda
  gamma_propertyT : ∀ n, HasKazhdanPropertyT (Gamma n)
  factors_isomorphic : ∀ n, TracialGroupFactorsIsomorphic (Gamma n) Lambda
  /-- Exact-index embeddings from the first group into every indexed group. -/
  embeddings : ∀ n, ExactIndexEmbedding (Gamma 0) (Gamma n) (2 ^ (4 * n))

namespace PaperFamilyInput

variable (F : PaperFamilyInput.{u})

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem parameter_eq_of_mulEquiv {m n : ℕ}
    (e : F.Gamma m ≃* F.Gamma n) : m = n := by
  apply paperInvariantCard_injective
  calc
    2 ^ (4 * m) = F.invariant.value (F.Gamma m) :=
      (F.invariant_card m).symm
    _ = F.invariant.value (F.Gamma n) := F.invariant.value_mulEquiv e
    _ = 2 ^ (4 * n) := F.invariant_card n

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem gamma_not_isomorphic {m n : ℕ} (hmn : m ≠ n) :
    ¬GroupsIsomorphic (F.Gamma m) (F.Gamma n) := by
  rintro ⟨e⟩
  exact hmn (F.parameter_eq_of_mulEquiv e)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem gamma_not_isomorphic_lambda (n : ℕ) :
    ¬GroupsIsomorphic (F.Gamma n) F.Lambda :=
  not_groupsIsomorphic_of_orderFour (F.gamma_order_four n)
    F.lambda_no_order_four

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem lambda_not_isomorphic_gamma (n : ℕ) :
    ¬GroupsIsomorphic F.Lambda (F.Gamma n) := by
  rintro ⟨e⟩
  exact F.gamma_not_isomorphic_lambda n ⟨e.symm⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem gamma_commensurable (m n : ℕ) :
    AbstractlyCommensurable (F.Gamma m) (F.Gamma n) := by
  apply abstractlyCommensurable_of_common_embedding
    (F.embeddings m) (F.embeddings n)
  · exact pow_ne_zero _ (by decide : (2 : ℕ) ≠ 0)
  · exact pow_ne_zero _ (by decide : (2 : ℕ) ≠ 0)

end PaperFamilyInput

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
structure InfinitePropertyTFiber where
  /-- The distinguished group in the fiber. -/
  Lambda : CountableDiscreteGroup.{u}
  /-- The infinite sequence of groups in the fiber. -/
  Gamma : ℕ → CountableDiscreteGroup.{u}
  lambda_fg : Group.FG Lambda
  gamma_fg : ∀ n, Group.FG (Gamma n)
  lambda_icc : IsICC Lambda
  gamma_icc : ∀ n, IsICC (Gamma n)
  lambda_propertyT : HasKazhdanPropertyT Lambda
  gamma_propertyT : ∀ n, HasKazhdanPropertyT (Gamma n)
  factors_isomorphic : ∀ n, TracialGroupFactorsIsomorphic (Gamma n) Lambda
  gamma_pairwise_nonisomorphic : ∀ {m n}, m ≠ n →
    ¬GroupsIsomorphic (Gamma m) (Gamma n)
  lambda_not_isomorphic : ∀ n, ¬GroupsIsomorphic Lambda (Gamma n)
  /-- Exact-index embeddings from the first group into every indexed group. -/
  exactIndexEmbeddings :
    ∀ n, ExactIndexEmbedding (Gamma 0) (Gamma n) (2 ^ (4 * n))
  commensurable : ∀ m n, AbstractlyCommensurable (Gamma m) (Gamma n)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def PaperFamilyInput.toInfinitePropertyTFiber (F : PaperFamilyInput.{u}) :
    InfinitePropertyTFiber.{u} where
  Lambda := F.Lambda
  Gamma := F.Gamma
  lambda_fg := F.lambda_fg
  gamma_fg := F.gamma_fg
  lambda_icc := F.lambda_icc
  gamma_icc := F.gamma_icc
  lambda_propertyT := F.lambda_propertyT
  gamma_propertyT := F.gamma_propertyT
  factors_isomorphic := F.factors_isomorphic
  gamma_pairwise_nonisomorphic := fun hmn => F.gamma_not_isomorphic hmn
  lambda_not_isomorphic := F.lambda_not_isomorphic_gamma
  exactIndexEmbeddings := F.embeddings
  commensurable := F.gamma_commensurable

end

section

open ConnesRigidity

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def kXLinear : K →* (X ≃ₗ[F] X) where
  toFun k := LinearEquiv.dualMap (kLinear k⁻¹)
  map_one' := by
    apply LinearEquiv.ext
    intro ℓ
    apply LinearMap.ext
    intro v
    simp only [inv_one, map_one, LinearEquiv.dualMap_apply, LinearEquiv.coe_one, id_eq]
  map_mul' k h := by
    apply LinearEquiv.ext
    intro ℓ
    apply LinearMap.ext
    intro v
    simp only [mul_inv_rev, map_mul, map_inv, LinearEquiv.dualMap_apply, LinearEquiv.mul_apply,
      LinearEquiv.coe_inv]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
public
theorem kXLinear_apply (k : K) (ℓ : X) (v : V) :
    kXLinear k ℓ v = ℓ (kLinear k⁻¹ v) := rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def kYLinear : K →* (Y ≃ₗ[F] Y) where
  toFun k := LinearEquiv.dualMap (kDividedSquareLinear k⁻¹)
  map_one' := by
    apply LinearEquiv.ext
    intro q
    apply LinearMap.ext
    intro b
    simp only [inv_one, map_one, LinearEquiv.dualMap_apply, LinearEquiv.coe_one, id_eq]
  map_mul' k h := by
    apply LinearEquiv.ext
    intro q
    apply LinearMap.ext
    intro b
    simp only [mul_inv_rev, map_mul, map_inv, LinearEquiv.dualMap_apply, LinearEquiv.mul_apply,
      LinearEquiv.coe_inv]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
public
theorem kYLinear_apply (k : K) (q : Y) (b : B) :
    kYLinear k q b = q (kDividedSquareLinear k⁻¹ b) := rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem continuous_kXLinear (k : K) :
    Continuous (kXLinear k : X → X) := by
  change Continuous
    (fun ℓ : X => ℓ.comp (kLinear k⁻¹).toLinearMap)
  exact continuous_X_precomp (kLinear k⁻¹).toLinearMap

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem continuous_kYLinear (k : K) :
    Continuous (kYLinear k : Y → Y) := by
  change Continuous
    (fun q : Y => q.comp (kDividedSquareLinear k⁻¹).toLinearMap)
  exact continuous_Y_precomp (kDividedSquareLinear k⁻¹).toLinearMap

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem kLinear_shiftVector (k : K) (n : ℕ) (v : V) :
    kLinear k (shiftVector n v) = shiftVector n (kLinear k v) := by
  simp only [kLinear_apply, shiftVector, LinearMap.restrictScalars_apply,
    LinearMap.lsmul_apply]
  exact (Matrix.SpecialLinearGroup.toLin' (pi₂ k)).map_smul _ _

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem kXLinear_shift (k : K) (n : ℕ) (ℓ : X) :
    shift n (kXLinear k ℓ) = kXLinear k (shift n ℓ) := by
  apply LinearMap.ext
  intro v
  change ℓ (kLinear k⁻¹ (shiftVector n v)) =
    ℓ (shiftVector n (kLinear k⁻¹ v))
  rw [kLinear_shiftVector]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem kYLinear_carry (k : K) (ℓ ℓ' : X) :
    kYLinear k (carry ℓ ℓ') =
      carry (kXLinear k ℓ) (kXLinear k ℓ') := by
  apply linearMap_ext_on_diagonal
  intro v
  change carry ℓ ℓ' (kDividedSquareLinear k⁻¹ (diagonal v)) =
    carry (kXLinear k ℓ) (kXLinear k ℓ') (diagonal v)
  rw [kDividedSquareLinear_diagonal]
  simp only [carry_apply_diagonal, kXLinear_apply]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem kYLinear_shiftedCarry (k : K) (n : ℕ) (ℓ ℓ' : X) :
    kYLinear k (shiftedCarry n ℓ ℓ') =
      shiftedCarry n (kXLinear k ℓ) (kXLinear k ℓ') := by
  unfold shiftedCarry
  rw [kYLinear_carry, ← kXLinear_shift, ← kXLinear_shift]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def kCarryAddAut (n : ℕ) (k : K) : AddAut (CarryGroup n) where
  toFun z := ⟨kXLinear k z.linear, kYLinear k z.quadratic⟩
  invFun z := ⟨kXLinear k⁻¹ z.linear, kYLinear k⁻¹ z.quadratic⟩
  left_inv z := by
    apply CarryGroup.ext <;> simp
  right_inv z := by
    apply CarryGroup.ext <;> simp
  map_add' z w := by
    apply CarryGroup.ext
    · simp only [CarryGroup.add_linear, map_add]
    · change kYLinear k
        (z.quadratic + w.quadratic + shiftedCarry n z.linear w.linear) =
          kYLinear k z.quadratic + kYLinear k w.quadratic +
            shiftedCarry n (kXLinear k z.linear) (kXLinear k w.linear)
      rw [map_add, map_add, kYLinear_shiftedCarry]





/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def kCarryAction (n : ℕ) : K →* MulAut (Multiplicative (CarryGroup n)) where
  toFun k := AddEquiv.toMultiplicative (kCarryAddAut n k)
  map_one' := by
    apply MulEquiv.ext
    intro z
    apply Multiplicative.toAdd.injective
    apply CarryGroup.ext
    · change kXLinear 1 (Multiplicative.toAdd z).linear =
        (Multiplicative.toAdd z).linear
      simp only [map_one, LinearEquiv.coe_one, id_eq]
    · change kYLinear 1 (Multiplicative.toAdd z).quadratic =
        (Multiplicative.toAdd z).quadratic
      simp only [map_one, LinearEquiv.coe_one, id_eq]
  map_mul' k h := by
    apply MulEquiv.ext
    intro z
    apply Multiplicative.toAdd.injective
    apply CarryGroup.ext
    · change kXLinear (k * h) (Multiplicative.toAdd z).linear =
        kXLinear k (kXLinear h (Multiplicative.toAdd z).linear)
      rw [map_mul]
      rfl
    · change kYLinear (k * h) (Multiplicative.toAdd z).quadratic =
        kYLinear k (kYLinear h (Multiplicative.toAdd z).quadratic)
      rw [map_mul]
      rfl





/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem continuous_kCarryAddAut (n : ℕ) (k : K) :
    Continuous (kCarryAddAut n k : CarryGroup n → CarryGroup n) := by
  apply continuous_CarryGroup_iff.mpr
  constructor
  · intro v
    exact continuous_linear_eval n (kLinear k⁻¹ v)
  · intro b
    exact continuous_quadratic_eval n (kDividedSquareLinear k⁻¹ b)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem continuous_kCarryAction (n : ℕ) (k : K) :
    Continuous (kCarryAction n k :
      Multiplicative (CarryGroup n) → Multiplicative (CarryGroup n)) := by
  change Continuous
    (fun z : CarryGroup n => kCarryAddAut n k z)
  exact continuous_kCarryAddAut n k

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def kEAction (n : ℕ) : K →* MulAut (Multiplicative (E n)) := by
  change K →* MulAut (PontryaginDual (Multiplicative (CarryGroup n)))
  exact dualAction (Multiplicative (CarryGroup n)) K (kCarryAction n)
    (continuous_kCarryAction n)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
public
theorem kEAction_apply (n : ℕ) (k : K)
    (η : Multiplicative (E n)) (z : Multiplicative (CarryGroup n)) :
    (kEAction n k η : PontryaginDual (Multiplicative (CarryGroup n))) z =
      (η : PontryaginDual (Multiplicative (CarryGroup n)))
        ((kCarryAction n k)⁻¹ z) := rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
noncomputable instance instMultiplicativeECountable (n : ℕ) :
    Countable (Multiplicative (E n)) :=
  (Multiplicative.toAdd : Multiplicative (E n) ≃ E n).injective.countable

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
abbrev Gamma (n : ℕ) :=
  SemidirectProduct (Multiplicative (E n)) K (kEAction n)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
noncomputable instance instGammaCountable (n : ℕ) : Countable (Gamma n) :=
  SemidirectProduct.equivProd.injective.countable

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def gammaGroup (n : ℕ) : CountableDiscreteGroup where
  Carrier := Gamma n
  group := inferInstance
  countable := inferInstance

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def gammaOrderFourElement (n : ℕ) : Gamma n :=
  SemidirectProduct.inl (Multiplicative.ofAdd (epsilon n e))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem gammaOrderFourElement_orderOf (n : ℕ) :
    orderOf (gammaOrderFourElement n) = 4 := by
  rw [gammaOrderFourElement,
    orderOf_injective (SemidirectProduct.inl :
      Multiplicative (E n) →* Gamma n) SemidirectProduct.inl_injective]
  exact epsilon_addOrderOf n

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem gamma_has_order_four (n : ℕ) :
    ∃ g : gammaGroup n, orderOf g = 4 :=
  ⟨gammaOrderFourElement n, gammaOrderFourElement_orderOf n⟩

end

section

open ConnesRigidity MeasureTheory

section

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def paperSplitAddAut (k : K) : (X × Y) ≃+ (X × Y) :=
  (kXLinear k).toAddEquiv.prodCongr (kYLinear k).toAddEquiv



/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def paperSplitPerm : K →* Equiv.Perm (X × Y) where
  toFun k := (paperSplitAddAut k).toEquiv
  map_one' := by
    apply Equiv.ext
    intro z
    change (kXLinear 1 z.1, kYLinear 1 z.2) = z
    simp only [map_one, LinearEquiv.coe_one, id_eq, Prod.mk.eta]
  map_mul' k h := by
    apply Equiv.ext
    intro z
    change
      (kXLinear (k * h) z.1, kYLinear (k * h) z.2) =
        (kXLinear k (kXLinear h z.1),
          kYLinear k (kYLinear h z.2))
    simp only [map_mul, LinearEquiv.mul_apply]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem continuous_paperSplitAddAut (k : K) :
    Continuous (paperSplitAddAut k : X × Y → X × Y) :=
  (continuous_kXLinear k).prodMap (continuous_kYLinear k)



/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem paper_kXLinear_symm (k : K) :
    (kXLinear k).symm = kXLinear k⁻¹ := by
  rw [map_inv]
  rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem paper_kYLinear_symm (k : K) :
    (kYLinear k).symm = kYLinear k⁻¹ := by
  rw [map_inv]
  rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem continuous_paperSplitAddAut_symm (k : K) :
    Continuous ((paperSplitAddAut k).symm : X × Y → X × Y) := by
  change Continuous
    (fun z : X × Y ↦ ((kXLinear k).symm z.1, (kYLinear k).symm z.2))
  rw [paper_kXLinear_symm, paper_kYLinear_symm]
  exact (continuous_kXLinear k⁻¹).prodMap
    (continuous_kYLinear k⁻¹)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def paperSplitHaarAction : HaarProbabilityAction K (X × Y) where
  measure := productHaar
  haar := inferInstance
  probability := inferInstance
  action := paperSplitPerm
  action_add := by
    intro k z z'
    exact (paperSplitAddAut k).map_add z z'
  action_preserves_measure := by
    intro k
    exact productHaar_preserving_addEquiv
      (paperSplitAddAut k)
      (continuous_paperSplitAddAut k)
      (continuous_paperSplitAddAut_symm k)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def paperCarryPerm (n : ℕ) : K →* Equiv.Perm (CarryGroup n) where
  toFun k := (kCarryAddAut n k).toEquiv
  map_one' := by
    apply Equiv.ext
    intro z
    apply CarryGroup.ext
    · change kXLinear 1 z.linear = z.linear
      simp only [map_one, LinearEquiv.coe_one, id_eq]
    · change kYLinear 1 z.quadratic = z.quadratic
      simp only [map_one, LinearEquiv.coe_one, id_eq]
  map_mul' k h := by
    apply Equiv.ext
    intro z
    apply CarryGroup.ext
    · change kXLinear (k * h) z.linear =
        kXLinear k (kXLinear h z.linear)
      rw [map_mul]
      rfl
    · change kYLinear (k * h) z.quadratic =
        kYLinear k (kYLinear h z.quadratic)
      rw [map_mul]
      rfl



/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem kCarryAddAut_symm_eq (n : ℕ) (k : K) :
    (kCarryAddAut n k).symm = kCarryAddAut n k⁻¹ := by
  apply AddEquiv.ext
  intro z
  rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem continuous_kCarryAddAut_symm (n : ℕ) (k : K) :
    Continuous ((kCarryAddAut n k).symm : CarryGroup n → CarryGroup n) := by
  rw [kCarryAddAut_symm_eq]
  exact continuous_kCarryAddAut n k⁻¹

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem paperCarryPerm_add (n : ℕ) (k : K)
    (z z' : CarryGroup n) :
    paperCarryPerm n k (z + z') =
      paperCarryPerm n k z + paperCarryPerm n k z' :=
  (kCarryAddAut n k).map_add z z'

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem paperCarryAddAut_preserves_measure (n : ℕ) (k : K) :
    MeasurePreserving (kCarryAddAut n k : CarryGroup n → CarryGroup n)
      (carryHaar n) (carryHaar n) :=
  carryHaar_preserving_addEquiv n (kCarryAddAut n k)
    (continuous_kCarryAddAut n k) (continuous_kCarryAddAut_symm n k)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def paperCarryHaarAction (n : ℕ) :
    HaarProbabilityAction K (CarryGroup n) where
  measure := carryHaar n
  haar := inferInstance
  probability := inferInstance
  action := paperCarryPerm n
  action_add := paperCarryPerm_add n
  action_preserves_measure := by
    intro k
    change MeasurePreserving
      (kCarryAddAut n k : CarryGroup n → CarryGroup n)
      (carryHaar n) (carryHaar n)
    exact paperCarryAddAut_preserves_measure n k

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def paperCommonHaarEquiv (n : ℕ) :
    EquivariantHaarEquiv (paperCarryHaarAction n) paperSplitHaarAction where
  toMeasurableEquiv := carryCoordinatesMeasurableEquiv n
  measure_preserving := carryCoordinates_measurePreserving n
  equivariant := by
    intro k z
    apply Prod.ext <;> rfl

end

end

section

open ConnesRigidity MeasureTheory
open scoped NNReal ENNReal

universe u v w

section

variable {K : Type u} [Group K]
variable {Ω : Type v} [AddCommGroup Ω] [TopologicalSpace Ω] [MeasurableSpace Ω]
variable {Ξ : Type w} [AddCommGroup Ξ] [TopologicalSpace Ξ] [MeasurableSpace Ξ]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
abbrev crossedBaseHilbert (X : HaarProbabilityAction K Ω) :=
  MeasureTheory.Lp ℂ 2 X.measure

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
abbrev crossedHilbert (X : HaarProbabilityAction K Ω) :=
  lp (fun _ : K ↦ crossedBaseHilbert X) 2

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
abbrev crossedCoefficient (X : HaarProbabilityAction K Ω) :=
  MeasureTheory.Lp ℂ ⊤ X.measure

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def crossedBaseMultiplier (X : HaarProbabilityAction K Ω)
    (f : crossedCoefficient X) :
    crossedBaseHilbert X →L[ℂ] crossedBaseHilbert X :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL X.measure ⊤ 2 2 f

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem crossedBaseMultiplier_apply_ae (X : HaarProbabilityAction K Ω)
    (f : crossedCoefficient X) (ξ : crossedBaseHilbert X) :
    crossedBaseMultiplier X f ξ =ᵐ[X.measure]
      fun z ↦ f z * ξ z :=
  ContinuousLinearMap.coeFn_holder (ContinuousLinearMap.mul ℂ ℂ) f ξ

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def crossedFiberwiseOperator
    {H : Type v} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (T : H →L[ℂ] H) :
    lp (fun _ : K ↦ H) 2 →L[ℂ] lp (fun _ : K ↦ H) 2 := by
  let F : lp (fun _ : K ↦ H) 2 →ₗ[ℂ] lp (fun _ : K ↦ H) 2 :=
    { toFun := fun ξ ↦
        ⟨fun k ↦ T (ξ k), by
          apply ((lp.memℓp ξ).const_smul (‖T‖ : ℂ)).mono'
          intro k
          change ‖T (ξ k)‖ ≤ ‖(‖T‖ : ℂ) • ξ k‖
          simpa only [Complex.coe_smul, norm_smul, norm_norm] using T.le_opNorm (ξ k)⟩
      map_add' := by
        intro ξ η
        ext k
        exact map_add T (ξ k) (η k)
      map_smul' := by
        intro c ξ
        ext k
        exact map_smul T c (ξ k) }
  exact F.mkContinuous ‖T‖ (by
    intro ξ
    calc
      ‖F ξ‖ ≤ ‖(‖T‖ : ℂ) • ξ‖ := lp.norm_mono (by norm_num) (by
        intro k
        change ‖T (ξ k)‖ ≤ ‖(‖T‖ : ℂ) • ξ k‖
        simpa only [Complex.coe_smul, norm_smul, norm_norm] using T.le_opNorm (ξ k))
      _ = ‖T‖ * ‖ξ‖ := by
        rw [lp.norm_const_smul (by norm_num : (2 : ℝ≥0∞) ≠ 0)]
        simp only [Complex.norm_real, norm_norm])

omit [Group K] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
public
theorem crossedFiberwiseOperator_apply
    {H : Type v} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (T : H →L[ℂ] H) (ξ : lp (fun _ : K ↦ H) 2) (k : K) :
    crossedFiberwiseOperator (K := K) T ξ k = T (ξ k) := rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def crossedMultiplier (X : HaarProbabilityAction K Ω)
    (f : crossedCoefficient X) : crossedHilbert X →L[ℂ] crossedHilbert X :=
  crossedFiberwiseOperator (K := K) (crossedBaseMultiplier X f)



/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def crossedFiberwiseEquiv
    {H : Type v} {J : Type w}
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup J] [NormedSpace ℂ J]
    (e : H ≃ₗᵢ[ℂ] J) :
    lp (fun _ : K ↦ H) 2 ≃ₗᵢ[ℂ] lp (fun _ : K ↦ J) 2 where
  toLinearEquiv :=
    { toFun := fun ξ ↦
        ⟨fun k ↦ e (ξ k), by
          change Memℓp (fun k ↦ e (ξ k)) 2
          rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
          simpa only [norm_map, ENNReal.toReal_ofNat, Real.rpow_ofNat] using
            (lp.memℓp ξ).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)⟩
      invFun := fun ξ ↦
        ⟨fun k ↦ e.symm (ξ k), by
          change Memℓp (fun k ↦ e.symm (ξ k)) 2
          rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
          simpa only [norm_map, ENNReal.toReal_ofNat, Real.rpow_ofNat] using
            (lp.memℓp ξ).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)⟩
      left_inv := by
        intro ξ
        ext k
        exact e.symm_apply_apply (ξ k)
      right_inv := by
        intro ξ
        ext k
        exact e.apply_symm_apply (ξ k)
      map_add' := by
        intro ξ η
        ext k
        exact map_add e (ξ k) (η k)
      map_smul' := by
        intro c ξ
        ext k
        exact map_smul e c (ξ k) }
  norm_map' := by
    intro ξ
    rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    change
      (∑' k : K, ‖e (ξ k)‖ ^ (2 : ℝ≥0∞).toReal) ^
        (1 / (2 : ℝ≥0∞).toReal) =
        (∑' k : K, ‖ξ k‖ ^ (2 : ℝ≥0∞).toReal) ^
          (1 / (2 : ℝ≥0∞).toReal)
    simp only [LinearIsometryEquiv.norm_map]



/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def crossedIndexEquiv
    {H : Type v} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (e : K ≃ K) :
    lp (fun _ : K ↦ H) 2 ≃ₗᵢ[ℂ] lp (fun _ : K ↦ H) 2 where
  toLinearEquiv :=
    { toFun := fun ξ ↦
        ⟨fun k ↦ ξ (e.symm k), by
          change Memℓp (fun k ↦ ξ (e.symm k)) 2
          rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
          exact (e.symm.summable_iff).2
            ((lp.memℓp ξ).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal))⟩
      invFun := fun ξ ↦
        ⟨fun k ↦ ξ (e k), by
          change Memℓp (fun k ↦ ξ (e k)) 2
          rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
          exact (e.summable_iff).2
            ((lp.memℓp ξ).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal))⟩
      left_inv := by
        intro ξ
        ext k
        exact congrArg ξ (e.symm_apply_apply k)
      right_inv := by
        intro ξ
        ext k
        exact congrArg ξ (e.apply_symm_apply k)
      map_add' := by
        intro ξ η
        ext k
        rfl
      map_smul' := by
        intro c ξ
        ext k
        rfl }
  norm_map' := by
    intro ξ
    rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    congr 1
    exact e.symm.tsum_eq (fun k ↦ ‖ξ k‖ ^ (2 : ℝ≥0∞).toReal)



/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def crossedBaseHaarEquiv
    {X : HaarProbabilityAction K Ω}
    {Y : HaarProbabilityAction K Ξ}
    (e : EquivariantHaarEquiv X Y) :
    crossedBaseHilbert X ≃ₗᵢ[ℂ] crossedBaseHilbert Y where
  toLinearEquiv :=
    { toFun := Lp.compMeasurePreserving e.toMeasurableEquiv.symm
        (EquivariantHaarEquiv.symm e).measure_preserving
      invFun := Lp.compMeasurePreserving e.toMeasurableEquiv
        e.measure_preserving
      left_inv := by
        intro f
        have h := Lp.compMeasurePreserving_comp_apply f
          (EquivariantHaarEquiv.symm e).measure_preserving
          e.measure_preserving
        simpa only [EquivariantHaarEquiv.symm, Function.comp_def, MeasurableEquiv.symm_apply_apply,
          show (fun z : Ω ↦ z) = id from rfl, Lp.compMeasurePreserving_id,
          AddMonoidHom.id_apply] using h.symm
      right_inv := by
        intro f
        have h := Lp.compMeasurePreserving_comp_apply f
          e.measure_preserving
          (EquivariantHaarEquiv.symm e).measure_preserving
        simpa only [EquivariantHaarEquiv.symm, Function.comp_def, MeasurableEquiv.apply_symm_apply,
          show (fun z : Ξ ↦ z) = id from rfl, Lp.compMeasurePreserving_id,
          AddMonoidHom.id_apply] using h.symm
      map_add' := by
        intro f g
        exact map_add
          (Lp.compMeasurePreserving e.toMeasurableEquiv.symm
            (EquivariantHaarEquiv.symm e).measure_preserving) f g
      map_smul' := by
        intro c f
        exact map_smul
          (Lp.compMeasurePreservingₗ ℂ e.toMeasurableEquiv.symm
            (EquivariantHaarEquiv.symm e).measure_preserving) c f }
  norm_map' := fun f ↦ Lp.norm_compMeasurePreserving f
    (EquivariantHaarEquiv.symm e).measure_preserving

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem crossedBaseHaarEquiv_apply
    {X : HaarProbabilityAction K Ω}
    {Y : HaarProbabilityAction K Ξ}
    (e : EquivariantHaarEquiv X Y) (f : crossedBaseHilbert X) :
    crossedBaseHaarEquiv e f =
      Lp.compMeasurePreserving e.toMeasurableEquiv.symm
        (EquivariantHaarEquiv.symm e).measure_preserving f := rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def crossedActionL2Equiv (X : HaarProbabilityAction K Ω) (k : K) :
    crossedBaseHilbert X ≃ₗᵢ[ℂ] crossedBaseHilbert X where
  toLinearEquiv :=
    { toFun := Lp.compMeasurePreserving (X.action k⁻¹)
        (X.action_preserves_measure k⁻¹)
      invFun := Lp.compMeasurePreserving (X.action k)
        (X.action_preserves_measure k)
      left_inv := by
        intro f
        have h := Lp.compMeasurePreserving_comp_apply f
          (X.action_preserves_measure k⁻¹)
          (X.action_preserves_measure k)
        simpa only [map_inv, Equiv.Perm.coe_inv, Function.comp_def, Equiv.symm_apply_apply,
          show (fun z : Ω ↦ z) = id from rfl, Lp.compMeasurePreserving_id,
          AddMonoidHom.id_apply] using h.symm
      right_inv := by
        intro f
        have h := Lp.compMeasurePreserving_comp_apply f
          (X.action_preserves_measure k)
          (X.action_preserves_measure k⁻¹)
        simpa only [map_inv, Equiv.Perm.coe_inv, Function.comp_def, Equiv.apply_symm_apply,
          show (fun z : Ω ↦ z) = id from rfl, Lp.compMeasurePreserving_id,
          AddMonoidHom.id_apply] using h.symm
      map_add' := by
        intro f g
        exact map_add (Lp.compMeasurePreserving (X.action k⁻¹)
          (X.action_preserves_measure k⁻¹)) f g
      map_smul' := by
        intro c f
        exact map_smul (Lp.compMeasurePreservingₗ ℂ (X.action k⁻¹)
          (X.action_preserves_measure k⁻¹)) c f }
  norm_map' := fun f ↦ Lp.norm_compMeasurePreserving f
    (X.action_preserves_measure k⁻¹)



/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def crossedGroupUnitary (X : HaarProbabilityAction K Ω) (k : K) :
    crossedHilbert X ≃ₗᵢ[ℂ] crossedHilbert X :=
  (crossedIndexEquiv (H := crossedBaseHilbert X) (Equiv.mulLeft k)).trans
    (crossedFiberwiseEquiv (K := K) (crossedActionL2Equiv X k))



/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def crossedGeneratorSet (X : HaarProbabilityAction K Ω) :
    Set (crossedHilbert X →L[ℂ] crossedHilbert X) :=
  Set.range (crossedMultiplier X) ∪
    Set.range fun k : K ↦
      (crossedGroupUnitary X k).toContinuousLinearEquiv.toContinuousLinearMap

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def crossedVacuum (X : HaarProbabilityAction K Ω) : crossedHilbert X := by
  classical
  let : IsProbabilityMeasure X.measure := X.probability
  exact lp.single 2 (1 : K) (Lp.const 2 X.measure (1 : ℂ))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def crossedProductModel (X : HaarProbabilityAction K Ω) :
    CrossedProductModel (crossedHilbert X) where
  algebra := vonNeumannClosure (crossedGeneratorSet X)
  trace := fun T ↦ inner ℂ (crossedVacuum X)
    ((T : crossedHilbert X →L[ℂ] crossedHilbert X) (crossedVacuum X))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def crossedHaarHilbertEquiv
    {X : HaarProbabilityAction K Ω}
    {Y : HaarProbabilityAction K Ξ}
    (e : EquivariantHaarEquiv X Y) :
    crossedHilbert X ≃ₗᵢ[ℂ] crossedHilbert Y :=
  crossedFiberwiseEquiv (K := K) (crossedBaseHaarEquiv e)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem crossedHaarHilbertEquiv_apply
    {X : HaarProbabilityAction K Ω}
    {Y : HaarProbabilityAction K Ξ}
    (e : EquivariantHaarEquiv X Y)
    (ξ : crossedHilbert X) (k : K) :
    crossedHaarHilbertEquiv e ξ k = crossedBaseHaarEquiv e (ξ k) := rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem crossedBaseHaarEquiv_const_one
    {X : HaarProbabilityAction K Ω}
    {Y : HaarProbabilityAction K Ξ}
    (e : EquivariantHaarEquiv X Y) :
    letI : IsProbabilityMeasure X.measure := X.probability
    letI : IsProbabilityMeasure Y.measure := Y.probability
    crossedBaseHaarEquiv e (Lp.const 2 X.measure (1 : ℂ)) =
      Lp.const 2 Y.measure (1 : ℂ) := by
  let : IsProbabilityMeasure X.measure := X.probability
  let : IsProbabilityMeasure Y.measure := Y.probability
  apply Lp.ext
  let hp : MeasurePreserving
      (e.toMeasurableEquiv.symm : Ξ → Ω) Y.measure X.measure :=
    (EquivariantHaarEquiv.symm e).measure_preserving
  have hsource := Lp.coeFn_const (μ := X.measure) (p := 2) (1 : ℂ)
  have hsource' := hp.quasiMeasurePreserving.ae_eq_comp hsource
  filter_upwards [
    Lp.coeFn_compMeasurePreserving (Lp.const 2 X.measure (1 : ℂ)) hp,
    hsource',
    Lp.coeFn_const (μ := Y.measure) (p := 2) (1 : ℂ)]
    with z hcomp hsource' htarget
  change
    (Lp.compMeasurePreserving e.toMeasurableEquiv.symm hp
      (Lp.const 2 X.measure (1 : ℂ))) z =
      Lp.const 2 Y.measure (1 : ℂ) z
  calc
    _ = (Lp.const 2 X.measure (1 : ℂ))
      (e.toMeasurableEquiv.symm z) := hcomp
    _ = 1 := hsource'
    _ = _ := htarget.symm

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem crossedHaarHilbertEquiv_vacuum
    {X : HaarProbabilityAction K Ω}
    {Y : HaarProbabilityAction K Ξ}
    (e : EquivariantHaarEquiv X Y) :
    crossedHaarHilbertEquiv e (crossedVacuum X) = crossedVacuum Y := by
  classical
  let : IsProbabilityMeasure X.measure := X.probability
  let : IsProbabilityMeasure Y.measure := Y.probability
  apply lp.ext
  funext k
  by_cases hk : k = 1
  · subst k
    simpa only [crossedVacuum, crossedHaarHilbertEquiv_apply, lp.single_apply, Pi.single_eq_same,
      crossedBaseHaarEquiv_apply] using
      crossedBaseHaarEquiv_const_one e
  · simp only [crossedVacuum, crossedHaarHilbertEquiv_apply, lp.single_apply, ne_eq, hk,
      not_false_eq_true, Pi.single_eq_of_ne, map_zero]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem crossedBaseHaarEquiv_multiplier_apply
    {X : HaarProbabilityAction K Ω}
    {Y : HaarProbabilityAction K Ξ}
    (e : EquivariantHaarEquiv X Y)
    (f : crossedCoefficient X) (ξ : crossedBaseHilbert X) :
    crossedBaseHaarEquiv e (crossedBaseMultiplier X f ξ) =
      crossedBaseMultiplier Y
        (Lp.compMeasurePreserving e.toMeasurableEquiv.symm
          (EquivariantHaarEquiv.symm e).measure_preserving f)
        (crossedBaseHaarEquiv e ξ) := by
  apply Lp.ext
  let hs : MeasurePreserving
      (e.toMeasurableEquiv.symm : Ξ → Ω) Y.measure X.measure :=
    (EquivariantHaarEquiv.symm e).measure_preserving
  have hleft := Lp.coeFn_compMeasurePreserving
    (crossedBaseMultiplier X f ξ) hs
  have hmul := hs.quasiMeasurePreserving.ae
    (crossedBaseMultiplier_apply_ae X f ξ)
  have hf := Lp.coeFn_compMeasurePreserving f hs
  have hξ := Lp.coeFn_compMeasurePreserving ξ hs
  have hright := crossedBaseMultiplier_apply_ae Y
    (Lp.compMeasurePreserving e.toMeasurableEquiv.symm hs f)
    (crossedBaseHaarEquiv e ξ)
  filter_upwards [hleft, hmul, hf, hξ, hright]
    with z hleft hmul hf hξ hright
  simp only [Function.comp_apply] at hleft hf hξ
  change (Lp.compMeasurePreserving e.toMeasurableEquiv.symm hs
    (crossedBaseMultiplier X f ξ)) z = _
  calc
    _ = (crossedBaseMultiplier X f ξ)
      (e.toMeasurableEquiv.symm z) := hleft
    _ = f (e.toMeasurableEquiv.symm z) *
      ξ (e.toMeasurableEquiv.symm z) := hmul
    _ = (Lp.compMeasurePreserving e.toMeasurableEquiv.symm hs f) z *
      (crossedBaseHaarEquiv e ξ) z := by
        congr 1
        · exact hf.symm
        · exact hξ.symm
    _ = _ := hright.symm

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem crossedBaseHaarEquiv_action
    {X : HaarProbabilityAction K Ω}
    {Y : HaarProbabilityAction K Ξ}
    (e : EquivariantHaarEquiv X Y) (k : K) (ξ : crossedBaseHilbert X) :
    crossedBaseHaarEquiv e (crossedActionL2Equiv X k ξ) =
      crossedActionL2Equiv Y k (crossedBaseHaarEquiv e ξ) := by
  let hs : MeasurePreserving
      (e.toMeasurableEquiv.symm : Ξ → Ω) Y.measure X.measure :=
    (EquivariantHaarEquiv.symm e).measure_preserving
  let hX := X.action_preserves_measure k⁻¹
  let hY := Y.action_preserves_measure k⁻¹
  change
    Lp.compMeasurePreserving e.toMeasurableEquiv.symm hs
      (Lp.compMeasurePreserving (X.action k⁻¹) hX ξ) =
      Lp.compMeasurePreserving (Y.action k⁻¹) hY
        (Lp.compMeasurePreserving e.toMeasurableEquiv.symm hs ξ)
  have hleft := Lp.compMeasurePreserving_comp_apply ξ hX hs
  have hright := Lp.compMeasurePreserving_comp_apply ξ hs hY
  have hfun :
      (X.action k⁻¹ : Ω → Ω) ∘
        (e.toMeasurableEquiv.symm : Ξ → Ω) =
      (e.toMeasurableEquiv.symm : Ξ → Ω) ∘
        (Y.action k⁻¹ : Ξ → Ξ) := by
    funext z
    change X.action k⁻¹ (e.toMeasurableEquiv.symm z) =
      e.toMeasurableEquiv.symm (Y.action k⁻¹ z)
    apply e.toMeasurableEquiv.injective
    rw [e.equivariant]
    simp only [map_inv, MeasurableEquiv.apply_symm_apply, Equiv.Perm.coe_inv]
  calc
    _ = Lp.compMeasurePreserving
      ((X.action k⁻¹ : Ω → Ω) ∘
        (e.toMeasurableEquiv.symm : Ξ → Ω))
      (hX.comp hs) ξ := hleft.symm
    _ = Lp.compMeasurePreserving
      ((e.toMeasurableEquiv.symm : Ξ → Ω) ∘
        (Y.action k⁻¹ : Ξ → Ξ))
      (hs.comp hY) ξ := by
        apply Lp.ext
        have hL := Lp.coeFn_compMeasurePreserving ξ (hX.comp hs)
        have hR := Lp.coeFn_compMeasurePreserving ξ (hs.comp hY)
        filter_upwards [hL, hR] with z hzL hzR
        calc
          _ = ξ (((X.action k⁻¹ : Ω → Ω) ∘
            (e.toMeasurableEquiv.symm : Ξ → Ω)) z) := by
              simpa only [Function.comp_apply] using hzL
          _ = ξ (((e.toMeasurableEquiv.symm : Ξ → Ω) ∘
            (Y.action k⁻¹ : Ξ → Ξ)) z) :=
              congrArg ξ (congrFun hfun z)
          _ = _ := by simpa only [Function.comp_apply] using hzR.symm
    _ = _ := hright

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem crossedHaarHilbertEquiv_group_apply
    {X : HaarProbabilityAction K Ω}
    {Y : HaarProbabilityAction K Ξ}
    (e : EquivariantHaarEquiv X Y) (k : K) (ξ : crossedHilbert X) :
    crossedHaarHilbertEquiv e (crossedGroupUnitary X k ξ) =
      crossedGroupUnitary Y k (crossedHaarHilbertEquiv e ξ) := by
  apply lp.ext
  funext h
  exact crossedBaseHaarEquiv_action e k (ξ (k⁻¹ * h))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem crossedHaarHilbertEquiv_group_conj
    {X : HaarProbabilityAction K Ω}
    {Y : HaarProbabilityAction K Ξ}
    (e : EquivariantHaarEquiv X Y) (k : K) :
    (crossedHaarHilbertEquiv e).conjStarAlgEquiv
      (crossedGroupUnitary X k).toContinuousLinearEquiv.toContinuousLinearMap =
        (crossedGroupUnitary Y k).toContinuousLinearEquiv.toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro η
  obtain ⟨ξ, rfl⟩ := (crossedHaarHilbertEquiv e).surjective η
  simpa only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    LinearIsometryEquiv.symm_apply_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv] using crossedHaarHilbertEquiv_group_apply e k ξ

end

end

section

open ConnesRigidity MeasureTheory
open scoped ENNReal

section

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def carryCharacterFunction (n : ℕ) (η : E n) : CarryGroup n → ℂ :=
  fun z => (Additive.toMul η (Multiplicative.ofAdd z) : ℂ)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem measurable_carryCharacterFunction (n : ℕ) (η : E n) :
    Measurable (carryCharacterFunction n η) :=
  (carryComplexCharacter n η).continuous.measurable

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem norm_carryCharacterFunction (n : ℕ) (η : E n)
    (z : CarryGroup n) :
    ‖carryCharacterFunction n η z‖ = 1 :=
  Circle.norm_coe (Additive.toMul η (Multiplicative.ofAdd z))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def carryCharacterCoefficient (n : ℕ) (η : E n) :
    crossedCoefficient (paperCarryHaarAction n) :=
  (memLp_top_of_bound
    (measurable_carryCharacterFunction n η).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun z =>
        le_of_eq (norm_carryCharacterFunction n η z))).toLp
    (carryCharacterFunction n η)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem carryCharacterCoefficient_apply_ae (n : ℕ) (η : E n) :
    carryCharacterCoefficient n η =ᵐ[carryHaar n]
      carryCharacterFunction n η :=
  MemLp.coeFn_toLp _

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem carryCharacterMultiplier_character
    (n : ℕ) (η θ : E n) :
    crossedBaseMultiplier (paperCarryHaarAction n)
        (carryCharacterCoefficient n η) (carryCharacterL2 n θ) =
      carryCharacterL2 n (η + θ) := by
  apply Lp.ext
  filter_upwards [
    crossedBaseMultiplier_apply_ae (paperCarryHaarAction n)
      (carryCharacterCoefficient n η) (carryCharacterL2 n θ),
    carryCharacterCoefficient_apply_ae n η,
    ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2)
      (carryHaar n) (carryComplexCharacter n θ),
    ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2)
      (carryHaar n) (carryComplexCharacter n (η + θ))]
    with z hmul hcoeff hθ hsum
  change (carryCharacterL2 n θ : CarryGroup n → ℂ) z =
    carryCharacterFunction n θ z at hθ
  change (carryCharacterL2 n (η + θ) : CarryGroup n → ℂ) z =
    carryCharacterFunction n (η + θ) z at hsum
  change
    (crossedBaseMultiplier (paperCarryHaarAction n)
      (carryCharacterCoefficient n η) (carryCharacterL2 n θ) :
        CarryGroup n → ℂ) z =
      (carryCharacterL2 n (η + θ) : CarryGroup n → ℂ) z
  calc
    (crossedBaseMultiplier (paperCarryHaarAction n)
      (carryCharacterCoefficient n η) (carryCharacterL2 n θ) :
        CarryGroup n → ℂ) z =
      (carryCharacterCoefficient n η : CarryGroup n → ℂ) z *
        (carryCharacterL2 n θ : CarryGroup n → ℂ) z := hmul
    _ = carryCharacterFunction n η z * carryCharacterFunction n θ z :=
      congrArg₂ (· * ·) hcoeff hθ
    _ = carryCharacterFunction n (η + θ) z := by
      simp only [carryCharacterFunction, toMul_add, pontryaginDual_mul_apply, Circle.coe_mul]
    _ = (carryCharacterL2 n (η + θ) : CarryGroup n → ℂ) z := hsum.symm

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def splitCharacterFunction (d : D) : X × Y → ℂ :=
  fun z => (splitPontryaginCharacter d (Multiplicative.ofAdd z) : ℂ)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem measurable_splitCharacterFunction (d : D) :
    Measurable (splitCharacterFunction d) :=
  (splitComplexCharacter d).continuous.measurable

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem norm_splitCharacterFunction (d : D) (z : X × Y) :
    ‖splitCharacterFunction d z‖ = 1 :=
  Circle.norm_coe (splitPontryaginCharacter d (Multiplicative.ofAdd z))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def splitCharacterCoefficient (d : D) :
    crossedCoefficient paperSplitHaarAction :=
  (memLp_top_of_bound
    (measurable_splitCharacterFunction d).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun z =>
        le_of_eq (norm_splitCharacterFunction d z))).toLp
    (splitCharacterFunction d)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem splitCharacterCoefficient_apply_ae (d : D) :
    splitCharacterCoefficient d =ᵐ[productHaar]
      splitCharacterFunction d :=
  MemLp.coeFn_toLp _

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem splitCharacterMultiplier_character (d e : D) :
    crossedBaseMultiplier paperSplitHaarAction
        (splitCharacterCoefficient d) (splitCharacterL2 e) =
      splitCharacterL2 (d + e) := by
  apply Lp.ext
  filter_upwards [
    crossedBaseMultiplier_apply_ae paperSplitHaarAction
      (splitCharacterCoefficient d) (splitCharacterL2 e),
    splitCharacterCoefficient_apply_ae d,
    ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2)
      productHaar (splitComplexCharacter e),
    ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2)
      productHaar (splitComplexCharacter (d + e))]
    with z hmul hcoeff he hsum
  change (splitCharacterL2 e : X × Y → ℂ) z =
    splitCharacterFunction e z at he
  change (splitCharacterL2 (d + e) : X × Y → ℂ) z =
    splitCharacterFunction (d + e) z at hsum
  change
    (crossedBaseMultiplier paperSplitHaarAction
      (splitCharacterCoefficient d) (splitCharacterL2 e) : X × Y → ℂ) z =
      (splitCharacterL2 (d + e) : X × Y → ℂ) z
  calc
    (crossedBaseMultiplier paperSplitHaarAction
      (splitCharacterCoefficient d) (splitCharacterL2 e) : X × Y → ℂ) z =
      (splitCharacterCoefficient d : X × Y → ℂ) z *
        (splitCharacterL2 e : X × Y → ℂ) z := hmul
    _ = splitCharacterFunction d z * splitCharacterFunction e z :=
      congrArg₂ (· * ·) hcoeff he
    _ = splitCharacterFunction (d + e) z := by
      change splitComplexCharacter d z * splitComplexCharacter e z =
        splitComplexCharacter (d + e) z
      exact (congrArg (fun f : C(X × Y, ℂ) => f z)
        (splitComplexCharacter_add d e)).symm
    _ = (splitCharacterL2 (d + e) : X × Y → ℂ) z := hsum.symm

end

end

section

open ConnesRigidity MeasureTheory
open scoped ENNReal

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem carryCharacterL2_zero (n : ℕ) :
    carryCharacterL2 n 0 = Lp.const 2 (carryHaar n) (1 : ℂ) := by
  apply Lp.ext
  filter_upwards [
    (carryComplexCharacter n 0).coeFn_toLp (p := 2) (𝕜 := ℂ) (carryHaar n),
    Lp.coeFn_const (μ := carryHaar n) (p := 2) (1 : ℂ)] with z hchar hone
  change ((ContinuousMap.toLp 2 (carryHaar n) ℂ)
    (carryComplexCharacter n 0)) z = Lp.const 2 (carryHaar n) (1 : ℂ) z
  rw [hchar, hone]
  rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem carryFourierEquiv_zero_single (n : ℕ) [DecidableEq (E n)] :
    carryFourierEquiv n (lp.single 2 (0 : E n) (1 : ℂ)) =
      Lp.const 2 (carryHaar n) (1 : ℂ) := by
  rw [carryFourierEquiv_single, carryCharacterL2_zero]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def carryEAddAction (n : ℕ) (k : K) : E n ≃+ E n :=
  MulEquiv.toAdditive (kEAction n k)



/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem carryComplexCharacter_kEAction (n : ℕ) (k : K)
    (η : E n) (z : CarryGroup n) :
    carryComplexCharacter n (carryEAddAction n k η) z =
      carryComplexCharacter n η (kCarryAddAut n k⁻¹ z) := by
  rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem carryCharacterL2_kEAction (n : ℕ) (k : K) (η : E n) :
    carryCharacterL2 n (carryEAddAction n k η) =
      Lp.compMeasurePreserving
        (kCarryAddAut n k⁻¹ : CarryGroup n → CarryGroup n)
        (paperCarryAddAut_preserves_measure n k⁻¹)
        (carryCharacterL2 n η) := by
  apply Lp.ext
  have hleft :
      carryCharacterL2 n (carryEAddAction n k η) =ᵐ[carryHaar n]
        carryComplexCharacter n (carryEAddAction n k η) :=
    (carryComplexCharacter n (carryEAddAction n k η)).coeFn_toLp
      (p := 2) (𝕜 := ℂ) (carryHaar n)
  have hright := Lp.coeFn_compMeasurePreserving
    (carryCharacterL2 n η) (paperCarryAddAut_preserves_measure n k⁻¹)
  have hchar : carryCharacterL2 n η =ᵐ[carryHaar n]
      carryComplexCharacter n η :=
    (carryComplexCharacter n η).coeFn_toLp
      (p := 2) (𝕜 := ℂ) (carryHaar n)
  have hchar' : ∀ᵐ z ∂carryHaar n,
      carryCharacterL2 n η (kCarryAddAut n k⁻¹ z) =
        carryComplexCharacter n η (kCarryAddAut n k⁻¹ z) :=
    (paperCarryAddAut_preserves_measure n k⁻¹).quasiMeasurePreserving.tendsto_ae hchar
  filter_upwards [hleft, hright, hchar'] with z hzleft hzright hzchar
  rw [hzleft, hzright, Function.comp_apply, hzchar]
  exact carryComplexCharacter_kEAction n k η z

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem carry_l2Reindex_single
    {α β : Type*} (e : α ≃ β) [DecidableEq α] [DecidableEq β]
    (i : α) (c : ℂ) :
    l2Reindex e (lp.single 2 i c) = lp.single 2 (e i) c := by
  ext j
  simp only [l2Reindex_apply, lp.single_apply]
  by_cases h : e.symm j = i
  · have hj : j = e i := by simpa only [Equiv.apply_symm_apply] using congrArg e h
    simp only [hj, Equiv.symm_apply_apply, Pi.single_eq_same]
  · have hj : j ≠ e i := by
      intro hj
      apply h
      simp only [hj, Equiv.symm_apply_apply]
    simp only [ne_eq, h, not_false_eq_true, Pi.single_eq_of_ne, hj]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem carryFourier_kEAction_comp (n : ℕ) (k : K)
    (ξ : GroupL2 (E n)) :
    carryFourierEquiv n
        (l2Reindex (carryEAddAction n k).toEquiv ξ) =
      Lp.compMeasurePreserving
        (kCarryAddAut n k⁻¹ : CarryGroup n → CarryGroup n)
        (paperCarryAddAut_preserves_measure n k⁻¹)
        (carryFourierEquiv n ξ) := by
  classical
  let F : GroupL2 (E n) →L[ℂ] Lp ℂ 2 (carryHaar n) :=
    (carryFourierEquiv n).toContinuousLinearEquiv.toContinuousLinearMap
  let R : GroupL2 (E n) →L[ℂ] GroupL2 (E n) :=
    (l2Reindex (carryEAddAction n k).toEquiv).toContinuousLinearEquiv.toContinuousLinearMap
  let P : Lp ℂ 2 (carryHaar n) →L[ℂ] Lp ℂ 2 (carryHaar n) :=
    (Lp.compMeasurePreservingₗᵢ ℂ
      (kCarryAddAut n k⁻¹ : CarryGroup n → CarryGroup n)
      (paperCarryAddAut_preserves_measure n k⁻¹)).toContinuousLinearMap
  have hmaps : F.comp R = P.comp F := by
    apply lp.ext_continuousLinearMap (by norm_num)
    intro η
    apply ContinuousLinearMap.ext
    intro c
    change
      carryFourierEquiv n
        (l2Reindex (carryEAddAction n k).toEquiv (lp.single 2 η c)) =
      Lp.compMeasurePreserving
        (kCarryAddAut n k⁻¹ : CarryGroup n → CarryGroup n)
        (paperCarryAddAut_preserves_measure n k⁻¹)
        (carryFourierEquiv n (lp.single 2 η c))
    have hsingle : (lp.single 2 η c : GroupL2 (E n)) =
        c • (lp.single 2 η (1 : ℂ) : GroupL2 (E n)) := by
      simpa only [smul_eq_mul, mul_one] using (lp.single_smul (E := fun _ : E n => ℂ) 2 η c (1 : ℂ))
    rw [hsingle]
    simp only [map_smul]
    rw [carry_l2Reindex_single, carryFourierEquiv_single,
      carryFourierEquiv_single]
    change c • carryCharacterL2 n (carryEAddAction n k η) =
      (Lp.compMeasurePreservingₗ ℂ
        (kCarryAddAut n k⁻¹ : CarryGroup n → CarryGroup n)
        (paperCarryAddAut_preserves_measure n k⁻¹))
          (c • carryCharacterL2 n η)
    rw [map_smul]
    exact congrArg (c • ·) (carryCharacterL2_kEAction n k η)
  exact DFunLike.congr_fun hmaps ξ

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem carryFourier_kEAction (n : ℕ) (k : K) (ξ : GroupL2 (E n)) :
    carryFourierEquiv n
        (l2Reindex (carryEAddAction n k).toEquiv ξ) =
      crossedActionL2Equiv (paperCarryHaarAction n) k
        (carryFourierEquiv n ξ) :=
  carryFourier_kEAction_comp n k ξ

end

section

open MeasureTheory
open scoped ENNReal

section

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def complexUnitBallClip (z : ℂ) : ℂ :=
  (1 / max 1 ‖z‖ : ℝ) • z

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem continuous_complexUnitBallClip : Continuous complexUnitBallClip := by
  unfold complexUnitBallClip
  exact (Continuous.div continuous_const
      (continuous_const.max continuous_norm)
      (fun z => by positivity)).smul continuous_id

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem complexUnitBallClip_eq_self_of_norm_le {z : ℂ} (hz : ‖z‖ ≤ 1) :
    complexUnitBallClip z = z := by
  rw [complexUnitBallClip, max_eq_left hz]
  norm_num

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem complexUnitBallClip_norm_le (z : ℂ) : ‖complexUnitBallClip z‖ ≤ 1 := by
  by_cases hz : ‖z‖ ≤ 1
  · rw [complexUnitBallClip_eq_self_of_norm_le hz]
    exact hz
  · have hzpos : 0 < ‖z‖ := lt_of_lt_of_le zero_lt_one (le_of_not_ge hz)
    rw [complexUnitBallClip, max_eq_right (le_of_not_ge hz)]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hzpos)]
    rw [one_div, inv_mul_cancel₀ hzpos.ne']

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem complexUnitBallClip_sub_norm_le_two (z u : ℂ) (hu : ‖u‖ = 1) :
    ‖complexUnitBallClip z - u‖ ≤ 2 * ‖z - u‖ := by
  by_cases hz : ‖z‖ ≤ 1
  · rw [complexUnitBallClip_eq_self_of_norm_le hz]
    linarith [norm_nonneg (z - u)]
  · have hz1 : 1 < ‖z‖ := lt_of_not_ge hz
    have hzpos : 0 < ‖z‖ := zero_lt_one.trans hz1
    have hclip : complexUnitBallClip z = (1 / ‖z‖ : ℝ) • z := by
      rw [complexUnitBallClip, max_eq_right hz1.le]
    have hdiff : ‖complexUnitBallClip z - z‖ = ‖z‖ - 1 := by
      rw [hclip]
      rw [show (1 / ‖z‖ : ℝ) • z - z =
          ((1 / ‖z‖ : ℝ) - 1) • z by module]
      rw [norm_smul, Real.norm_eq_abs]
      have hscalar : |1 / ‖z‖ - 1| = 1 - 1 / ‖z‖ := by
        rw [abs_of_nonpos]
        · ring
        · exact sub_nonpos.mpr ((div_le_one hzpos).mpr hz1.le)
      rw [hscalar]
      field_simp
    have hradial : ‖z‖ - 1 ≤ ‖z - u‖ := by
      rw [← hu]
      exact norm_sub_norm_le z u
    calc
      ‖complexUnitBallClip z - u‖ =
          ‖(complexUnitBallClip z - z) + (z - u)‖ := by
            congr 1
            abel
      _ ≤ ‖complexUnitBallClip z - z‖ + ‖z - u‖ := norm_add_le _ _
      _ ≤ 2 * ‖z - u‖ := by rw [hdiff]; linarith

universe u

variable {Ω : Type u} [TopologicalSpace Ω] [CompactSpace Ω] [T2Space Ω]
  [SecondCountableTopology Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ] [μ.WeaklyRegular]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def unitCoefficient (u : Ω → ℂ) (hu : Measurable u)
    (hunit : ∀ x, ‖u x‖ = 1) : Lp ℂ ⊤ μ :=
  (memLp_top_of_bound hu.aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun x => (hunit x).le)).toLp u

omit [TopologicalSpace Ω] [CompactSpace Ω] [T2Space Ω] [SecondCountableTopology Ω]
  [BorelSpace Ω] [IsProbabilityMeasure μ] [μ.WeaklyRegular] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem unitCoefficient_coeFn (u : Ω → ℂ) (hu : Measurable u)
    (hunit : ∀ x, ‖u x‖ = 1) :
    unitCoefficient μ u hu hunit =ᵐ[μ] u :=
  MemLp.coeFn_toLp _

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def unitFunctionL2 (u : Ω → ℂ) (hu : Measurable u)
    (hunit : ∀ x, ‖u x‖ = 1) : Lp ℂ 2 μ :=
  (MemLp.of_bound hu.aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun x => (hunit x).le)).toLp u

omit [TopologicalSpace Ω] [CompactSpace Ω] [T2Space Ω] [SecondCountableTopology Ω]
  [BorelSpace Ω] [μ.WeaklyRegular] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem unitFunctionL2_coeFn (u : Ω → ℂ) (hu : Measurable u)
    (hunit : ∀ x, ‖u x‖ = 1) :
    unitFunctionL2 μ u hu hunit =ᵐ[μ] u :=
  MemLp.coeFn_toLp _

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def unitMultiplier (u : Ω → ℂ) (hu : Measurable u)
    (hunit : ∀ x, ‖u x‖ = 1) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL μ ⊤ 2 2
    (unitCoefficient μ u hu hunit)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def continuousMultiplier :
    C(Ω, ℂ) →L[ℂ] (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) :=
  ((ContinuousLinearMap.mul ℂ ℂ).holderL μ ⊤ 2 2).comp
    (ContinuousMap.toLp ⊤ μ ℂ)

omit [TopologicalSpace Ω] [CompactSpace Ω] [T2Space Ω] [SecondCountableTopology Ω]
  [BorelSpace Ω] [IsProbabilityMeasure μ] [μ.WeaklyRegular] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem unitMultiplier_coeFn (u : Ω → ℂ) (hu : Measurable u)
    (hunit : ∀ x, ‖u x‖ = 1) (f : Lp ℂ 2 μ) :
    unitMultiplier μ u hu hunit f =ᵐ[μ] fun x => u x * f x := by
  exact (ContinuousLinearMap.coeFn_holder (ContinuousLinearMap.mul ℂ ℂ)
    (unitCoefficient μ u hu hunit) f).trans <| by
      filter_upwards [unitCoefficient_coeFn μ u hu hunit] with x hx
      change unitCoefficient μ u hu hunit x * f x = u x * f x
      rw [hx]

omit [T2Space Ω] [SecondCountableTopology Ω] [μ.WeaklyRegular] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem continuousMultiplier_coeFn (q : C(Ω, ℂ)) (f : Lp ℂ 2 μ) :
    continuousMultiplier μ q f =ᵐ[μ] fun x => q x * f x := by
  exact (ContinuousLinearMap.coeFn_holder (ContinuousLinearMap.mul ℂ ℂ)
    ((ContinuousMap.toLp ⊤ μ ℂ) q) f).trans <| by
      filter_upwards [ContinuousMap.coeFn_toLp (p := ⊤) (𝕜 := ℂ) μ q] with x hx
      change ((ContinuousMap.toLp ⊤ μ ℂ) q) x * f x = q x * f x
      rw [hx]

omit [T2Space Ω] [SecondCountableTopology Ω] [μ.WeaklyRegular] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem continuous_sub_unit_multiplier_norm_le_two
    (u : Ω → ℂ) (hu : Measurable u)
    (hunit : ∀ x, ‖u x‖ = 1)
    (q : C(Ω, ℂ)) (hq : ∀ x, ‖q x‖ ≤ 1) (f : Lp ℂ 2 μ) :
    ‖continuousMultiplier μ q f - unitMultiplier μ u hu hunit f‖ ≤
      2 * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [
    Lp.coeFn_sub (continuousMultiplier μ q f) (unitMultiplier μ u hu hunit f),
    continuousMultiplier_coeFn μ q f,
    unitMultiplier_coeFn μ u hu hunit f
    ] with x hsub hqcoe hucoe
  rw [hsub]
  change ‖continuousMultiplier μ q f x - unitMultiplier μ u hu hunit f x‖ ≤
    2 * ‖f x‖
  rw [hqcoe, hucoe, ← sub_mul, norm_mul]
  have hqu : ‖q x - u x‖ ≤ 2 := by
    calc
      ‖q x - u x‖ ≤ ‖q x‖ + ‖u x‖ := norm_sub_le _ _
      _ ≤ 2 := by rw [hunit]; linarith [hq x]
  exact mul_le_mul_of_nonneg_right hqu (norm_nonneg _)

omit [T2Space Ω] [SecondCountableTopology Ω] [μ.WeaklyRegular] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem continuous_sub_unit_multiplier_on_continuous_norm_le
    (u : Ω → ℂ) (hu : Measurable u)
    (hunit : ∀ x, ‖u x‖ = 1)
    (q h : C(Ω, ℂ)) :
    ‖continuousMultiplier μ q ((ContinuousMap.toLp 2 μ ℂ) h) -
      unitMultiplier μ u hu hunit ((ContinuousMap.toLp 2 μ ℂ) h)‖ ≤
      ‖h‖ * ‖(ContinuousMap.toLp 2 μ ℂ) q - unitFunctionL2 μ u hu hunit‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [
    Lp.coeFn_sub
      (continuousMultiplier μ q ((ContinuousMap.toLp 2 μ ℂ) h))
      (unitMultiplier μ u hu hunit ((ContinuousMap.toLp 2 μ ℂ) h)),
    continuousMultiplier_coeFn μ q ((ContinuousMap.toLp 2 μ ℂ) h),
    unitMultiplier_coeFn μ u hu hunit ((ContinuousMap.toLp 2 μ ℂ) h),
    Lp.coeFn_sub ((ContinuousMap.toLp 2 μ ℂ) q) (unitFunctionL2 μ u hu hunit),
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) μ q,
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) μ h,
    unitFunctionL2_coeFn μ u hu hunit
    ] with x hout hqmul humul hdiff hqcoe hhcoe hucoe
  rw [hout, hdiff]
  change
    ‖continuousMultiplier μ q ((ContinuousMap.toLp 2 μ ℂ) h) x -
      unitMultiplier μ u hu hunit ((ContinuousMap.toLp 2 μ ℂ) h) x‖ ≤
      ‖h‖ * ‖((ContinuousMap.toLp 2 μ ℂ) q) x - unitFunctionL2 μ u hu hunit x‖
  rw [hqmul, humul, hqcoe, hhcoe, hucoe, ← sub_mul, norm_mul]
  nlinarith [ContinuousMap.norm_coe_le_norm h x, norm_nonneg (q x - u x)]

omit [T2Space Ω] [SecondCountableTopology Ω] [μ.WeaklyRegular] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem continuous_sub_unit_multiplier_norm_le
    (u : Ω → ℂ) (hu : Measurable u)
    (hunit : ∀ x, ‖u x‖ = 1)
    (q : C(Ω, ℂ)) (hq : ∀ x, ‖q x‖ ≤ 1)
    (f : Lp ℂ 2 μ) (h : C(Ω, ℂ)) :
    ‖continuousMultiplier μ q f - unitMultiplier μ u hu hunit f‖ ≤
      2 * ‖f - (ContinuousMap.toLp 2 μ ℂ) h‖ +
        ‖h‖ * ‖(ContinuousMap.toLp 2 μ ℂ) q - unitFunctionL2 μ u hu hunit‖ := by
  let hL2 := (ContinuousMap.toLp 2 μ ℂ) h
  have hdecomp :
      continuousMultiplier μ q f - unitMultiplier μ u hu hunit f =
        (continuousMultiplier μ q (f - hL2) -
          unitMultiplier μ u hu hunit (f - hL2)) +
        (continuousMultiplier μ q hL2 - unitMultiplier μ u hu hunit hL2) := by
    simp only [map_sub, hL2]
    abel
  rw [hdecomp]
  exact (norm_add_le _ _).trans <| add_le_add
    (continuous_sub_unit_multiplier_norm_le_two μ u hu hunit q hq (f - hL2))
    (continuous_sub_unit_multiplier_on_continuous_norm_le μ u hu hunit q h)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def clipContinuousMap (c : C(Ω, ℂ)) : C(Ω, ℂ) :=
  ⟨fun t => complexUnitBallClip (c t),
    continuous_complexUnitBallClip.comp c.continuous⟩

omit [CompactSpace Ω] [T2Space Ω] [SecondCountableTopology Ω] [MeasurableSpace Ω]
  [BorelSpace Ω] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem clipContinuousMap_norm_le (c : C(Ω, ℂ)) (t : Ω) :
    ‖clipContinuousMap c t‖ ≤ 1 :=
  complexUnitBallClip_norm_le _

omit [T2Space Ω] [SecondCountableTopology Ω] [μ.WeaklyRegular] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem clipContinuousMap_toLp_sub_unit_le (u : Ω → ℂ) (hu : Measurable u)
    (hunit : ∀ t, ‖u t‖ = 1) (c : C(Ω, ℂ)) :
    ‖(ContinuousMap.toLp 2 μ ℂ) (clipContinuousMap c) -
        unitFunctionL2 μ u hu hunit‖ ≤
      2 * ‖(ContinuousMap.toLp 2 μ ℂ) c -
        unitFunctionL2 μ u hu hunit‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [
    Lp.coeFn_sub ((ContinuousMap.toLp 2 μ ℂ) (clipContinuousMap c))
      (unitFunctionL2 μ u hu hunit),
    Lp.coeFn_sub ((ContinuousMap.toLp 2 μ ℂ) c)
      (unitFunctionL2 μ u hu hunit),
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) μ (clipContinuousMap c),
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) μ c,
    unitFunctionL2_coeFn μ u hu hunit
    ] with t hleft hright hclip hc hucoe
  rw [hleft, hright]
  change
    ‖((ContinuousMap.toLp 2 μ ℂ) (clipContinuousMap c)) t -
        unitFunctionL2 μ u hu hunit t‖ ≤
      2 * ‖((ContinuousMap.toLp 2 μ ℂ) c) t -
        unitFunctionL2 μ u hu hunit t‖
  rw [hclip, hc, hucoe]
  exact complexUnitBallClip_sub_norm_le_two (c t) (u t) (hunit t)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem exists_continuous_norm_le_one_approx (u : Ω → ℂ) (hu : Measurable u)
    (hunit : ∀ t, ‖u t‖ = 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ q : C(Ω, ℂ), (∀ t, ‖q t‖ ≤ 1) ∧
      ‖(ContinuousMap.toLp 2 μ ℂ) q -
          unitFunctionL2 μ u hu hunit‖ < ε := by
  obtain ⟨c, hc⟩ :=
    (ContinuousMap.toLp_denseRange ℂ μ ℂ
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞)).exists_dist_lt
      (unitFunctionL2 μ u hu hunit) (half_pos hε)
  refine ⟨clipContinuousMap c, clipContinuousMap_norm_le c, ?_⟩
  apply lt_of_le_of_lt
    (clipContinuousMap_toLp_sub_unit_le μ u hu hunit c)
  rw [dist_eq_norm] at hc
  rw [norm_sub_rev]
  linarith

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem exists_continuous_multiplier_approx_pair
    (u : Ω → ℂ) (hu : Measurable u)
    (hunit : ∀ x, ‖u x‖ = 1)
    (f₁ f₂ : Lp ℂ 2 μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ q : C(Ω, ℂ),
      (∀ x, ‖q x‖ ≤ 1) ∧
      ‖continuousMultiplier μ q f₁ - unitMultiplier μ u hu hunit f₁‖ < ε ∧
      ‖continuousMultiplier μ q f₂ - unitMultiplier μ u hu hunit f₂‖ < ε := by
  obtain ⟨h₁, hh₁⟩ :=
    (ContinuousMap.toLp_denseRange ℂ μ ℂ
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞)).exists_dist_lt
      f₁ (by positivity : 0 < ε / 8)
  obtain ⟨h₂, hh₂⟩ :=
    (ContinuousMap.toLp_denseRange ℂ μ ℂ
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞)).exists_dist_lt
      f₂ (by positivity : 0 < ε / 8)
  let δ : ℝ := ε / (4 * (‖h₁‖ + ‖h₂‖ + 1))
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  obtain ⟨q, hqbound, hq⟩ :=
    exists_continuous_norm_le_one_approx μ u hu hunit hδ
  refine ⟨q, hqbound, ?_, ?_⟩
  all_goals
    apply lt_of_le_of_lt
      (continuous_sub_unit_multiplier_norm_le
        μ u hu hunit q hqbound _ _)
  · rw [dist_eq_norm] at hh₁
    have hmul :
        ‖h₁‖ * ‖(ContinuousMap.toLp 2 μ ℂ) q -
            unitFunctionL2 μ u hu hunit‖ ≤ ‖h₁‖ * δ :=
      mul_le_mul_of_nonneg_left hq.le (norm_nonneg h₁)
    have hdelta : ‖h₁‖ * δ ≤ ε / 4 := by
      dsimp [δ]
      rw [← mul_div_assoc]
      apply (div_le_iff₀ (by positivity :
        0 < 4 * (‖h₁‖ + ‖h₂‖ + 1))).2
      nlinarith [norm_nonneg h₁, norm_nonneg h₂]
    linarith
  · rw [dist_eq_norm] at hh₂
    have hmul :
        ‖h₂‖ * ‖(ContinuousMap.toLp 2 μ ℂ) q -
            unitFunctionL2 μ u hu hunit‖ ≤ ‖h₂‖ * δ :=
      mul_le_mul_of_nonneg_left hq.le (norm_nonneg h₂)
    have hdelta : ‖h₂‖ * δ ≤ ε / 4 := by
      dsimp [δ]
      rw [← mul_div_assoc]
      apply (div_le_iff₀ (by positivity :
        0 < 4 * (‖h₁‖ + ‖h₂‖ + 1))).2
      nlinarith [norm_nonneg h₁, norm_nonneg h₂]
    linarith

omit [SecondCountableTopology Ω] [μ.WeaklyRegular] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem commute_continuousMultiplier_of_commute_characters
    {ι : Type*} (χ : ι → C(Ω, ℂ))
    (hdense : (Submodule.span ℂ (Set.range χ)).topologicalClosure = ⊤)
    (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hT : ∀ i, Commute T (continuousMultiplier μ (χ i)))
    (q : C(Ω, ℂ)) : Commute T (continuousMultiplier μ q) := by
  let leftMap : C(Ω, ℂ) →L[ℂ] (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) :=
    ((ContinuousLinearMap.mul ℂ (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)) T).comp
      (continuousMultiplier μ)
  let rightMap : C(Ω, ℂ) →L[ℂ] (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) :=
    ((ContinuousLinearMap.mul ℂ (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)).flip T).comp
      (continuousMultiplier μ)
  have hspan : Dense (↑(Submodule.span ℂ (Set.range χ)) : Set C(Ω, ℂ)) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr hdense
  have heq :
      (leftMap : C(Ω, ℂ) → (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)) = rightMap := by
    apply Continuous.ext_on hspan leftMap.continuous rightMap.continuous
    intro q hq
    refine Submodule.span_induction
      (p := fun q _ => leftMap q = rightMap q) ?_ ?_ ?_ ?_ hq
    · rintro _ ⟨i, rfl⟩
      exact (hT i).eq
    · exact (map_zero leftMap).trans (map_zero rightMap).symm
    · intro f g _ _ hf hg
      rw [map_add, map_add, hf, hg]
    · intro c f _ hf
      rw [map_smul, map_smul, hf]
  exact congrFun heq q

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem commute_unitMultiplier_of_commute_characters
    {ι : Type*} (χ : ι → C(Ω, ℂ))
    (hdense : (Submodule.span ℂ (Set.range χ)).topologicalClosure = ⊤)
    (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hT : ∀ i, Commute T (continuousMultiplier μ (χ i)))
    (u : Ω → ℂ) (hu : Measurable u) (hunit : ∀ x, ‖u x‖ = 1) :
    Commute T (unitMultiplier μ u hu hunit) := by
  change T * unitMultiplier μ u hu hunit =
    unitMultiplier μ u hu hunit * T
  apply ContinuousLinearMap.ext
  intro f
  change T (unitMultiplier μ u hu hunit f) =
    unitMultiplier μ u hu hunit (T f)
  let d : Lp ℂ 2 μ :=
    T (unitMultiplier μ u hu hunit f) - unitMultiplier μ u hu hunit (T f)
  by_contra hne
  have hdne : d ≠ 0 := by
    intro hd
    exact hne (sub_eq_zero.mp hd)
  have hdpos : 0 < ‖d‖ := norm_pos_iff.mpr hdne
  let ε : ℝ := ‖d‖ / (2 * (‖T‖ + 1))
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  obtain ⟨q, _hqbound, hqf, hqTf⟩ :=
    exists_continuous_multiplier_approx_pair μ u hu hunit f (T f) hε
  have hcomm :=
    commute_continuousMultiplier_of_commute_characters μ χ hdense T hT q
  have hcommf : T (continuousMultiplier μ q f) =
      continuousMultiplier μ q (T f) :=
    DFunLike.congr_fun hcomm.eq f
  have hdecomp :
      d = T (unitMultiplier μ u hu hunit f - continuousMultiplier μ q f) +
        (continuousMultiplier μ q (T f) - unitMultiplier μ u hu hunit (T f)) := by
    dsimp [d]
    rw [map_sub, hcommf]
    abel
  have hfirst :
      ‖T (unitMultiplier μ u hu hunit f - continuousMultiplier μ q f)‖ ≤
        ‖T‖ * ε := by
    apply (T.le_opNorm _).trans
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg T)
    rw [norm_sub_rev]
    exact hqf.le
  have htotal : ‖d‖ < ‖T‖ * ε + ε := by
    rw [hdecomp]
    exact (norm_add_le _ _).trans_lt (add_lt_add_of_le_of_lt hfirst hqTf)
  have heq : ‖T‖ * ε + ε = ‖d‖ / 2 := by
    dsimp [ε]
    field_simp
  rw [heq] at htotal
  linarith

end

end

section

open MeasureTheory
open scoped ENNReal ComplexConjugate

section

namespace FullUnitDecomposition

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def realUnit (x : ℝ) : ℂ :=
  (x : ℂ) + Complex.I * (Real.sqrt (1 - x ^ 2) : ℂ)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem continuous_realUnit : Continuous realUnit := by
  unfold realUnit
  fun_prop

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem norm_realUnit {x : ℝ} (hx : |x| ≤ 1) :
    ‖realUnit x‖ = 1 := by
  have hsq : ‖realUnit x‖ ^ 2 = 1 := by
    rw [Complex.sq_norm]
    exact Complex.normSq_ofReal_add_I_mul_sqrt_one_sub hx
  nlinarith [norm_nonneg (realUnit x)]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem realUnit_add_conj (x : ℝ) :
    realUnit x + starRingEnd ℂ (realUnit x) = 2 * (x : ℂ) := by
  apply Complex.ext <;> simp [realUnit]; ring

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem complex_four_unit_decomposition {z : ℂ} (_hz : ‖z‖ ≤ 1) :
    z = (realUnit z.re + starRingEnd ℂ (realUnit z.re)) / 2 +
      Complex.I * (realUnit z.im + starRingEnd ℂ (realUnit z.im)) / 2 := by
  rw [realUnit_add_conj, realUnit_add_conj]
  apply Complex.ext <;> simp

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def clip (z : ℂ) : ℂ :=
  (1 / max 1 ‖z‖ : ℝ) • z

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem continuous_clip : Continuous clip := by
  unfold clip
  exact (Continuous.div continuous_const
      (continuous_const.max continuous_norm)
      (fun z => by positivity)).smul continuous_id

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem clip_eq_self_of_norm_le {z : ℂ} (hz : ‖z‖ ≤ 1) : clip z = z := by
  rw [clip, max_eq_left hz]
  norm_num

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem norm_clip_le (z : ℂ) : ‖clip z‖ ≤ 1 := by
  by_cases hz : ‖z‖ ≤ 1
  · rw [clip_eq_self_of_norm_le hz]
    exact hz
  · have hzpos : 0 < ‖z‖ := lt_of_lt_of_le zero_lt_one (le_of_not_ge hz)
    rw [clip, max_eq_right (le_of_not_ge hz), norm_smul, Real.norm_eq_abs,
      abs_of_pos (one_div_pos.mpr hzpos), one_div, inv_mul_cancel₀ hzpos.ne']

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem lp_infty_ae_norm_le (f : Lp ℂ ⊤ μ) :
    ∀ᵐ x ∂μ, ‖f x‖ ≤ ‖f‖ := by
  have hnorm : lpNorm (fun x => f x) ⊤ μ = ‖f‖ := by
    rw [← toReal_eLpNorm (Lp.memLp f).aestronglyMeasurable,
      Lp.norm_def]
  simpa only [hnorm] using
    (ae_le_lpNorm_exponent_top (Lp.memLp f))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def normalizedCoefficient (f : Lp ℂ ⊤ μ) (x : Ω) : ℂ :=
  clip (((Lp.memLp f).aestronglyMeasurable.mk (fun y => f y) x) /
    ((‖f‖ + 1 : ℝ) : ℂ))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem measurable_normalizedCoefficient (f : Lp ℂ ⊤ μ) :
    Measurable (normalizedCoefficient f) := by
  unfold normalizedCoefficient
  exact continuous_clip.measurable.comp
    ((Lp.memLp f).aestronglyMeasurable.measurable_mk.div measurable_const)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem norm_normalizedCoefficient_le (f : Lp ℂ ⊤ μ) (x : Ω) :
    ‖normalizedCoefficient f x‖ ≤ 1 := norm_clip_le _

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem normalizedCoefficient_ae (f : Lp ℂ ⊤ μ) :
    normalizedCoefficient f =ᵐ[μ]
      fun x => f x / ((‖f‖ + 1 : ℝ) : ℂ) := by
  filter_upwards [lp_infty_ae_norm_le f,
    (Lp.memLp f).aestronglyMeasurable.ae_eq_mk] with x hx hrep
  unfold normalizedCoefficient
  rw [← hrep]
  apply clip_eq_self_of_norm_le
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < ‖f‖ + 1)]
  exact (div_le_one (by positivity : 0 < ‖f‖ + 1)).2 (by linarith)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def unitRe (f : Lp ℂ ⊤ μ) (x : Ω) : ℂ :=
  realUnit (normalizedCoefficient f x).re

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def unitReConj (f : Lp ℂ ⊤ μ) (x : Ω) : ℂ :=
  starRingEnd ℂ (unitRe f x)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def unitIm (f : Lp ℂ ⊤ μ) (x : Ω) : ℂ :=
  realUnit (normalizedCoefficient f x).im

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def unitImConj (f : Lp ℂ ⊤ μ) (x : Ω) : ℂ :=
  starRingEnd ℂ (unitIm f x)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem measurable_unitRe (f : Lp ℂ ⊤ μ) : Measurable (unitRe f) :=
  continuous_realUnit.measurable.comp
    (Complex.measurable_re.comp (measurable_normalizedCoefficient f))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem measurable_unitReConj (f : Lp ℂ ⊤ μ) : Measurable (unitReConj f) :=
  Complex.continuous_conj.measurable.comp (measurable_unitRe f)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem measurable_unitIm (f : Lp ℂ ⊤ μ) : Measurable (unitIm f) :=
  continuous_realUnit.measurable.comp
    (Complex.measurable_im.comp (measurable_normalizedCoefficient f))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem measurable_unitImConj (f : Lp ℂ ⊤ μ) : Measurable (unitImConj f) :=
  Complex.continuous_conj.measurable.comp (measurable_unitIm f)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem norm_unitRe (f : Lp ℂ ⊤ μ) (x : Ω) : ‖unitRe f x‖ = 1 :=
  norm_realUnit ((Complex.abs_re_le_norm _).trans
    (norm_normalizedCoefficient_le f x))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem norm_unitReConj (f : Lp ℂ ⊤ μ) (x : Ω) : ‖unitReConj f x‖ = 1 := by
  unfold unitReConj
  rw [Complex.norm_conj, norm_unitRe]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem norm_unitIm (f : Lp ℂ ⊤ μ) (x : Ω) : ‖unitIm f x‖ = 1 :=
  norm_realUnit ((Complex.abs_im_le_norm _).trans
    (norm_normalizedCoefficient_le f x))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem norm_unitImConj (f : Lp ℂ ⊤ μ) (x : Ω) : ‖unitImConj f x‖ = 1 := by
  unfold unitImConj
  rw [Complex.norm_conj, norm_unitIm]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem lp_infty_four_unit_decomposition (f : Lp ℂ ⊤ μ) :
    ∀ᵐ x ∂μ,
      f x = ((‖f‖ + 1 : ℝ) : ℂ) / 2 * unitRe f x +
        ((‖f‖ + 1 : ℝ) : ℂ) / 2 * unitReConj f x +
        (((‖f‖ + 1 : ℝ) : ℂ) / 2 * Complex.I) * unitIm f x +
        (((‖f‖ + 1 : ℝ) : ℂ) / 2 * Complex.I) * unitImConj f x := by
  filter_upwards [normalizedCoefficient_ae f] with x hx
  have hdecomp := complex_four_unit_decomposition
    (norm_normalizedCoefficient_le f x)
  rw [hx] at hdecomp
  simp only [unitReConj, unitImConj, unitRe, unitIm, hx]
  have hR : ((‖f‖ + 1 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (by positivity : 0 < ‖f‖ + 1))
  field_simp at hdecomp ⊢
  linear_combination hdecomp

end FullUnitDecomposition

section MultiplierClosure

variable {Ω : Type*} [TopologicalSpace Ω] [CompactSpace Ω] [T2Space Ω]
  [SecondCountableTopology Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ] [μ.WeaklyRegular]

omit [TopologicalSpace Ω] [CompactSpace Ω] [T2Space Ω] [SecondCountableTopology Ω]
  [BorelSpace Ω] [IsProbabilityMeasure μ] [μ.WeaklyRegular] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem lp_infty_eq_four_unitCoefficients (f : Lp ℂ ⊤ μ) :
    f =
      (((‖f‖ + 1 : ℝ) : ℂ) / 2) •
          unitCoefficient μ (FullUnitDecomposition.unitRe f)
            (FullUnitDecomposition.measurable_unitRe f)
            (FullUnitDecomposition.norm_unitRe f) +
      (((‖f‖ + 1 : ℝ) : ℂ) / 2) •
          unitCoefficient μ (FullUnitDecomposition.unitReConj f)
            (FullUnitDecomposition.measurable_unitReConj f)
            (FullUnitDecomposition.norm_unitReConj f) +
      ((((‖f‖ + 1 : ℝ) : ℂ) / 2) * Complex.I) •
          unitCoefficient μ (FullUnitDecomposition.unitIm f)
            (FullUnitDecomposition.measurable_unitIm f)
            (FullUnitDecomposition.norm_unitIm f) +
      ((((‖f‖ + 1 : ℝ) : ℂ) / 2) * Complex.I) •
          unitCoefficient μ (FullUnitDecomposition.unitImConj f)
            (FullUnitDecomposition.measurable_unitImConj f)
            (FullUnitDecomposition.norm_unitImConj f) := by
  apply Lp.ext
  let c : ℂ := ((‖f‖ + 1 : ℝ) : ℂ) / 2
  let u₁ := unitCoefficient μ (FullUnitDecomposition.unitRe f)
    (FullUnitDecomposition.measurable_unitRe f)
    (FullUnitDecomposition.norm_unitRe f)
  let u₂ := unitCoefficient μ (FullUnitDecomposition.unitReConj f)
    (FullUnitDecomposition.measurable_unitReConj f)
    (FullUnitDecomposition.norm_unitReConj f)
  let u₃ := unitCoefficient μ (FullUnitDecomposition.unitIm f)
    (FullUnitDecomposition.measurable_unitIm f)
    (FullUnitDecomposition.norm_unitIm f)
  let u₄ := unitCoefficient μ (FullUnitDecomposition.unitImConj f)
    (FullUnitDecomposition.measurable_unitImConj f)
    (FullUnitDecomposition.norm_unitImConj f)
  change (fun x => f x) =ᵐ[μ]
    (fun x => (c • u₁ + c • u₂ + (c * Complex.I) • u₃ +
      (c * Complex.I) • u₄) x)
  filter_upwards [
    FullUnitDecomposition.lp_infty_four_unit_decomposition f,
    unitCoefficient_coeFn μ (FullUnitDecomposition.unitRe f)
      (FullUnitDecomposition.measurable_unitRe f)
      (FullUnitDecomposition.norm_unitRe f),
    unitCoefficient_coeFn μ (FullUnitDecomposition.unitReConj f)
      (FullUnitDecomposition.measurable_unitReConj f)
      (FullUnitDecomposition.norm_unitReConj f),
    unitCoefficient_coeFn μ (FullUnitDecomposition.unitIm f)
      (FullUnitDecomposition.measurable_unitIm f)
      (FullUnitDecomposition.norm_unitIm f),
    unitCoefficient_coeFn μ (FullUnitDecomposition.unitImConj f)
      (FullUnitDecomposition.measurable_unitImConj f)
      (FullUnitDecomposition.norm_unitImConj f),
    Lp.coeFn_add (c • u₁ + c • u₂ + (c * Complex.I) • u₃)
      ((c * Complex.I) • u₄),
    Lp.coeFn_add (c • u₁ + c • u₂) ((c * Complex.I) • u₃),
    Lp.coeFn_add (c • u₁) (c • u₂),
    Lp.coeFn_smul c u₁,
    Lp.coeFn_smul c u₂,
    Lp.coeFn_smul (c * Complex.I) u₃,
    Lp.coeFn_smul (c * Complex.I) u₄
    ] with x hdecomp hu₁ hu₂ hu₃ hu₄ hadd₄ hadd₃ hadd₂
      hsmul₁ hsmul₂ hsmul₃ hsmul₄
  simp only [Pi.add_apply] at hadd₄ hadd₃ hadd₂
  simp only [Pi.smul_apply, smul_eq_mul] at hsmul₁ hsmul₂ hsmul₃ hsmul₄
  rw [hadd₄, hadd₃, hadd₂, hsmul₁, hsmul₂, hsmul₃, hsmul₄]
  change f x = c * u₁ x + c * u₂ x + (c * Complex.I) * u₃ x +
    (c * Complex.I) * u₄ x
  change u₁ x = FullUnitDecomposition.unitRe f x at hu₁
  change u₂ x = FullUnitDecomposition.unitReConj f x at hu₂
  change u₃ x = FullUnitDecomposition.unitIm f x at hu₃
  change u₄ x = FullUnitDecomposition.unitImConj f x at hu₄
  rw [hu₁, hu₂, hu₃, hu₄]
  exact hdecomp

omit [TopologicalSpace Ω] [CompactSpace Ω] [T2Space Ω] [SecondCountableTopology Ω]
  [BorelSpace Ω] [IsProbabilityMeasure μ] [μ.WeaklyRegular] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem commute_multiplier_of_commute_units
    (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hT : ∀ (u : Ω → ℂ) (hu : Measurable u)
      (hunit : ∀ x, ‖u x‖ = 1), Commute T (unitMultiplier μ u hu hunit))
    (f : Lp ℂ ⊤ μ) :
    Commute T ((ContinuousLinearMap.mul ℂ ℂ).holderL μ ⊤ 2 2 f) := by
  have h₁ := hT (FullUnitDecomposition.unitRe f)
    (FullUnitDecomposition.measurable_unitRe f)
    (FullUnitDecomposition.norm_unitRe f)
  have h₂ := hT (FullUnitDecomposition.unitReConj f)
    (FullUnitDecomposition.measurable_unitReConj f)
    (FullUnitDecomposition.norm_unitReConj f)
  have h₃ := hT (FullUnitDecomposition.unitIm f)
    (FullUnitDecomposition.measurable_unitIm f)
    (FullUnitDecomposition.norm_unitIm f)
  have h₄ := hT (FullUnitDecomposition.unitImConj f)
    (FullUnitDecomposition.measurable_unitImConj f)
    (FullUnitDecomposition.norm_unitImConj f)
  rw [lp_infty_eq_four_unitCoefficients μ f]
  simp only [map_add, map_smul]
  simpa only [unitMultiplier] using
    (((h₁.smul_right (((‖f‖ + 1 : ℝ) : ℂ) / 2)).add_right
      (h₂.smul_right (((‖f‖ + 1 : ℝ) : ℂ) / 2))).add_right
      (h₃.smul_right ((((‖f‖ + 1 : ℝ) : ℂ) / 2) * Complex.I))).add_right
      (h₄.smul_right ((((‖f‖ + 1 : ℝ) : ℂ) / 2) * Complex.I))

end MultiplierClosure

end

end

end ConnesRigidity

end
