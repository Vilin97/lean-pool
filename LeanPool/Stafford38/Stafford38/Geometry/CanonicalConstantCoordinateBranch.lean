/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.Stafford38.Characteristic.CanonicalBaseVariety
public import LeanPool.Stafford38.Stafford38.Geometry.ConstantCoordinateConormal
public import LeanPool.Stafford38.Stafford38.Geometry.LaurentConormalResidueExtension
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.Nullstellensatz


/-!
# Canonical constant-coordinate branch

If the distinguished coordinate is constant on a minimal component of a
radical affine variety, a minimal-prime multiplier and the Nullstellensatz
produce an ambient equation whose differential is the pure coordinate axis.
This gives the exact residue-extension endpoint used by the canonical
assembly, with residue extension equal to the ground field.
-/

@[expose] public section

namespace Stafford38.Geometry.CanonicalConstantCoordinateBranch

open Stafford38
open Stafford38.Characteristic
open Stafford38.Characteristic.CanonicalBaseVariety
open Stafford38.Characteristic.ReducedSupportIdeal
open Stafford38.CharacteristicInitialIdeal
open Stafford38.EulerSurjectivity
open Stafford38.Geometry.AffineConormalClosure
open Stafford38.Geometry.AffineConormalSpan
open Stafford38.Geometry.CoisotropicTranslation
open Stafford38.Geometry.ConstantCoordinateConormal
open Stafford38.Geometry.LaurentConormalResidueExtension
open Stafford38.Geometry.ScalarExtensionPoints
open Stafford38.GeometryRetractionSpecialization
open Stafford38.WeylEulerResidue
open Stafford38.WeylIteratedEquivalence

noncomputable section

universe u


private theorem exists_zero_eval_ne_of_isRadical_not_mem
    {k : Type u} [Field k] [IsAlgClosed k] {m : ℕ}
    (I : Ideal (MvPolynomial (Fin m) k)) (hI : I.IsRadical)
    {g : MvPolynomial (Fin m) k} (hg : g ∉ I) :
    ∃ y : Fin m → k,
      (∀ f ∈ I, MvPolynomial.eval y f = 0) ∧
      MvPolynomial.eval y g ≠ 0 := by
  classical
  by_contra h
  have hall : ∀ y : Fin m → k,
      y ∈ MvPolynomial.zeroLocus k I → MvPolynomial.eval y g = 0 := by
    intro y hy
    by_contra hgy
    exact h ⟨y, hy, hgy⟩
  have hgvanish : g ∈ MvPolynomial.vanishingIdeal k
      (MvPolynomial.zeroLocus k I) := hall
  rw [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical, hI.radical] at hgvanish
  exact hg hgvanish

/-- A coordinate which is constant on one minimal component of a radical
affine variety already contributes the pure coordinate covector to the
ambient equation-defined conormal at a suitable point.  The multiplier is
the standard zero-divisor witness for a minimal prime; radicality and the
Nullstellensatz choose a point where that multiplier does not vanish. -/
theorem exists_ambientConormalAxis_of_minimalPrime_coordinate_constant
    {k : Type u} [Field k] [IsAlgClosed k] {m : ℕ}
    (I P : Ideal (MvPolynomial (Fin m) k)) (hI : I.IsRadical)
    (hP : P ∈ I.minimalPrimes) (i : Fin m) (c : k)
    (hconstant : MvPolynomial.X i - MvPolynomial.C c ∈ P) :
    ∃ y : Fin m → k,
      (∀ f ∈ I, MvPolynomial.eval y f = 0) ∧
      coordinateCovector (fun j ↦ if j = i then 1 else 0) ∈
        affineConormalSpace y I := by
  classical
  let h : MvPolynomial (Fin m) k :=
    MvPolynomial.X i - MvPolynomial.C c
  obtain ⟨g, hgI, hhg⟩ :=
    Ideal.exists_mul_mem_of_mem_minimalPrimes hP hconstant
  obtain ⟨y, hy, hgy⟩ :=
    exists_zero_eval_ne_of_isRadical_not_mem I hI hgI
  have hhzero : MvPolynomial.eval y h = 0 := by
    have hproduct : MvPolynomial.eval y (h * g) = 0 := hy _ hhg
    rw [map_mul] at hproduct
    exact (mul_eq_zero.mp hproduct).resolve_right hgy
  have hdiff : differentialCovector y (h * g) =
      MvPolynomial.eval y g •
        coordinateCovector (fun j ↦ if j = i then 1 else 0) := by
    apply LinearMap.ext
    intro v
    change (∑ j, differentialAt y (h * g) j * v j) =
      MvPolynomial.eval y g *
        ∑ j, (if j = i then 1 else 0) * v j
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hji : j = i
    · subst j
      simp [differentialAt,  h, hhzero,
          mul_comm]
    · simp [differentialAt,  h, hhzero,
        hji, Ne.symm hji,   mul_comm]
  have hproductConormal : differentialCovector y (h * g) ∈
      affineConormalSpace y I := by
    rw [affineConormalSpace_eq_equationCovectorSpan]
    apply Submodule.subset_span
    exact ⟨⟨h * g, hhg⟩, rfl⟩
  refine ⟨y, hy, ?_⟩
  have hscaled := (affineConormalSpace y I).smul_mem
    (MvPolynomial.eval y g)⁻¹ hproductConormal
  rw [hdiff] at hscaled
  simpa [hgy] using hscaled

/-- The minimal-component constant-coordinate branch reaches the exact
residue-extension endpoint used by the canonical asymptotic assembly.  The
extension is again `K = k`; the only extra ingredient beyond the ambient
branch is the minimal-prime multiplier argument above. -/
theorem exists_residueExtensionConormalAxis_of_minimalPrime_coordinate_constant
    {k : Type u} [Field k] [IsAlgClosed k] {m : ℕ} (hm : 0 < m)
    (I P : Ideal (MvPolynomial (Fin m) k)) (hI : I.IsRadical)
    (hP : P ∈ I.minimalPrimes) (c : k)
    (hconstant : MvPolynomial.X ⟨0, hm⟩ - MvPolynomial.C c ∈ P) :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K)
      (y : Fin m → LaurentSeries K)
      (xi : Fin m → PowerSeries K),
      Sum.elim y
          (fun i ↦ algebraMap (PowerSeries K) (LaurentSeries K) (xi i)) ∈
        groundEquationConormalLocus (k := k) (K := K) I ∧
      residueColumn xi =
        (fun i : Fin m ↦ if i = ⟨0, hm⟩ then 1 else 0) := by
  classical
  let i : Fin m := ⟨0, hm⟩
  let h : MvPolynomial (Fin m) k :=
    MvPolynomial.X i - MvPolynomial.C c
  obtain ⟨g, hgI, hhg⟩ :=
    Ideal.exists_mul_mem_of_mem_minimalPrimes hP hconstant
  obtain ⟨y, hy, hgy⟩ :=
    exists_zero_eval_ne_of_isRadical_not_mem I hI hgI
  have hhzero : MvPolynomial.eval y h = 0 := by
    have hproduct : MvPolynomial.eval y (h * g) = 0 := hy _ hhg
    rw [map_mul] at hproduct
    exact (mul_eq_zero.mp hproduct).resolve_right hgy
  let yL : Fin m → LaurentSeries k := fun j ↦
    algebraMap k (LaurentSeries k) (y j)
  let xi : Fin m → PowerSeries k := fun j ↦
    PowerSeries.C (if j = i then 1 else 0)
  let IL := I.map
    (scalarPolynomialMap (k := k) (K := LaurentSeries k) (Fin m))
  let fL := scalarPolynomialMap
    (k := k) (K := LaurentSeries k) (Fin m) (h * g)
  have hyL : ∀ f ∈ IL, MvPolynomial.eval yL f = 0 := by
    rw [show (∀ f ∈ IL, MvPolynomial.eval yL f = 0) ↔
        yL ∈ MvPolynomial.zeroLocus (LaurentSeries k) IL by rfl]
    rw [mem_zeroLocus_map_iff]
    intro f hf
    change MvPolynomial.eval₂ (algebraMap k (LaurentSeries k))
      ((algebraMap k (LaurentSeries k)) ∘ y) f = 0
    rw [← MvPolynomial.eval₂_comp, hy f hf, map_zero]
  have hfL : fL ∈ IL := by
    exact Ideal.mem_map_of_mem
      (scalarPolynomialMap (k := k) (K := LaurentSeries k) (Fin m)) hhg
  have hgyL : algebraMap k (LaurentSeries k) (MvPolynomial.eval y g) ≠ 0 := by
    simpa only [map_zero] using
      (algebraMap k (LaurentSeries k)).injective.ne hgy
  have hdiffAtL (j : Fin m) :
      differentialAt yL fL j =
        algebraMap k (LaurentSeries k) (differentialAt y (h * g) j) := by
    rw [differentialAt_scalarPolynomialMap]
    change MvPolynomial.eval₂ (algebraMap k (LaurentSeries k))
      ((algebraMap k (LaurentSeries k)) ∘ y)
        (MvPolynomial.pderiv j (h * g)) = _
    rw [← MvPolynomial.eval₂_comp]
    rfl
  have hdiffL : differentialCovector yL fL =
      algebraMap k (LaurentSeries k) (MvPolynomial.eval y g) •
        coordinateCovector
          (fun j : Fin m ↦ if j = i then 1 else 0) := by
    apply LinearMap.ext
    intro v
    change (∑ j, differentialAt yL fL j * v j) =
      algebraMap k (LaurentSeries k) (MvPolynomial.eval y g) *
        ∑ j, (if j = i then 1 else 0) * v j
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hdiffAtL]
    by_cases hji : j = i
    · subst j
      simp [h, differentialAt,  hhzero,
          mul_comm]
    · simp [h, differentialAt,  hhzero,
        hji, Ne.symm hji,   mul_comm]
  have haxisConormal : coordinateCovector
      (fun j : Fin m ↦ if j = i then 1 else 0) ∈
        affineConormalSpace yL IL := by
    have hproductConormal : differentialCovector yL fL ∈
        affineConormalSpace yL IL := by
      rw [affineConormalSpace_eq_equationCovectorSpan]
      apply Submodule.subset_span
      exact ⟨⟨fL, hfL⟩, rfl⟩
    have hscaled := (affineConormalSpace yL IL).smul_mem
      ((algebraMap k (LaurentSeries k) (MvPolynomial.eval y g))⁻¹ :
        LaurentSeries k) hproductConormal
    rw [hdiffL] at hscaled
    simpa only [inv_smul_smul₀ hgyL] using hscaled
  have hphase : Sum.elim yL
      (fun j : Fin m ↦ if j = i then 1 else 0) ∈
        equationConormalLocus IL := ⟨hyL, haxisConormal⟩
  refine ⟨k, inferInstance, inferInstance, yL, xi, ?_, ?_⟩
  · change Sum.elim yL
      (fun j ↦ algebraMap (PowerSeries k) (LaurentSeries k) (xi j)) ∈
        groundEquationConormalLocus (k := k) (K := k) I
    simpa [xi, i, IL, groundEquationConormalLocus, groundPolynomialMap,
      groundLaurentMap, scalarPolynomialMap] using hphase
  · funext j
    simp [xi, i, residueColumn]

/-- An ambient constant-coordinate equation and one ambient zero produce the
exact existential residue-extension conormal axis.  No algebraic closure,
boundary valuation, or nonconstant-coordinate argument is needed. -/
theorem exists_residueExtensionConormalAxis_of_ambientCoordinate_constant
    {k : Type u} [Field k] {m : ℕ} (hm : 0 < m)
    (I : Ideal (MvPolynomial (Fin m) k))
    (hexists : ∃ y : Fin m → k,
      ∀ f ∈ I, MvPolynomial.eval y f = 0)
    (hconstant : ∃ c : k,
      MvPolynomial.X ⟨0, hm⟩ - MvPolynomial.C c ∈ I) :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K)
      (y : Fin m → LaurentSeries K)
      (xi : Fin m → PowerSeries K),
      Sum.elim y
          (fun i ↦ algebraMap (PowerSeries K) (LaurentSeries K) (xi i)) ∈
        groundEquationConormalLocus (k := k) (K := K) I ∧
      residueColumn xi =
        (fun i : Fin m ↦ if i = ⟨0, hm⟩ then 1 else 0) := by
  obtain ⟨y, hy⟩ := hexists
  obtain ⟨c, hc⟩ := hconstant
  obtain ⟨yL, xi, hphase, hresidue⟩ :=
    exists_laurentConormalAxis_of_coordinate_sub_constant_mem
      I y hy ⟨0, hm⟩ c hc
  refine ⟨k, inferInstance, inferInstance, yL, xi, ?_, hresidue⟩
  simpa [groundEquationConormalLocus, groundPolynomialMap, groundLaurentMap,
    scalarPolynomialMap] using hphase

/-- Canonical specialization of the ambient constant-coordinate branch.
Nonempty order-characteristic support supplies the required ambient base
zero.  The conclusion is exactly the point type consumed by the
higher-dimensional residue-extension assembly. -/
theorem exists_canonical_residueExtensionConormalAxis_of_baseCoordinate_constant
    {k : Type u} [Field k] [IsAlgClosed k]
    (n N : ℕ) (d : PresentedWeyl k (n + 1))
    (hsupp :
      (orderCharacteristicSupport k
        (canonicalRightIdeal (presentedCoordinate k n) d N)).Nonempty)
    (hconstant : ∃ c : k,
      MvPolynomial.X ⟨0, Nat.zero_lt_succ n⟩ - MvPolynomial.C c ∈
        reducedOrderBaseIdeal k
          (canonicalRightIdeal (presentedCoordinate k n) d N)) :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K)
      (y : Fin (n + 1) → LaurentSeries K)
      (xi : Fin (n + 1) → PowerSeries K),
      Sum.elim y
          (fun i ↦ algebraMap (PowerSeries K) (LaurentSeries K) (xi i)) ∈
        groundEquationConormalLocus (k := k) (K := K)
          (reducedOrderBaseIdeal k
            (canonicalRightIdeal (presentedCoordinate k n) d N)) ∧
      residueColumn xi =
        (fun i : Fin (n + 1) ↦
          if i = ⟨0, Nat.zero_lt_succ n⟩ then 1 else 0) := by
  apply exists_residueExtensionConormalAxis_of_ambientCoordinate_constant
    (Nat.zero_lt_succ n)
  · exact exists_reducedOrderBaseZero_of_support_nonempty
      (canonicalRightIdeal (presentedCoordinate k n) d N) hsupp
  · exact hconstant


end

end Stafford38.Geometry.CanonicalConstantCoordinateBranch
