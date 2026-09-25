/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.NormApproximation.FinitePlaces
public import LeanPool.ClassFieldTheory.GaloisCohomology.Kummer.Concrete.RootCharacters
public import Mathlib.Algebra.Group.Hom.Basic
public import Mathlib.Algebra.Group.Subgroup.Ker
/-!
# Kummer radicals and finite-place decomposition fields

For a finite Galois extension containing an `n`-th root `β` of a
base-field unit `a`, this file identifies the local `n`-th-power
condition on `a` with membership of `β` in the decomposition field.

The proof uses the canonical comparison between the two models of the
finite-place completion and the algebraic localization realization of
the decomposition field.  The only Kummer input is the usual fact that
two roots with the same `n`-th power differ by an `n`-th root of unity.
-/

@[expose] public section

open scoped NumberField
open NumberField IsDedekindDomain
open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalClassFieldTheory

noncomputable section

namespace KummerTheory

variable {K L : Type}
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

omit [NumberField K] [FiniteDimensional K L] in
open scoped Classical in
/-- If a Kummer radicand is an `n`-th power in an absolute-value
completion, its chosen root lies in the corresponding decomposition
field.  This is the completion-level source behind both the finite and
archimedean localization arguments. -/
theorem
    kummerRadicand_root_mem_decompositionFixedField_of_mem_nthPowerSubgroup
    (vK : AbsoluteValue K ℝ)
    (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L)
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (a : Kˣ) (beta : Lˣ)
    (hbeta :
      beta ^ (n : ℕ) =
        Units.map (algebraMap K L).toMonoidHom a)
    (ha :
      Units.map
            (algebraMap K vK.Completion).toMonoidHom a ∈
        (powMonoidHom (n : ℕ) :
          vK.Completionˣ →* vK.Completionˣ).range) :
    (beta : L) ∈
      IntermediateField.fixedField
        (absoluteValueDecompositionGroup K w.1) := by
  let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  let hK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  let := localizedCompletionGlobalAlgebra vK w
  let := localizedCompletionIsScalarTower vK w
  let C := vK.Completion
  let E := LocalizedCompletion vK w
  let toE :=
    AbsoluteValue.toAlgebraicLocalization vK w.1 w.2
  let aC : Cˣ :=
    Units.map (algebraMap K C).toMonoidHom a
  have hbeta_val :
      (beta : L) ^ (n : ℕ) =
        algebraMap K L (a : K) := by
    simpa using congrArg Units.val hbeta
  obtain ⟨yC, hyC⟩ :=
    (MonoidHom.mem_range
      (G := Cˣ)).mp ha
  rw [powMonoidHom_apply] at hyC
  let betaE : Eˣ :=
    Units.map toE.toMonoidHom beta
  let yE : Eˣ :=
    Units.map (algebraMap C E).toMonoidHom yC
  have hbetaE :
      betaE ^ (n : ℕ) =
        Units.map (algebraMap C E).toMonoidHom aC := by
    apply Units.ext
    change
      toE (beta : L) ^ (n : ℕ) =
        algebraMap C E (algebraMap K C (a : K))
    calc
      toE (beta : L) ^ (n : ℕ) =
          toE ((beta : L) ^ (n : ℕ)) := by
        exact
          (map_pow toE (beta : L) (n : ℕ)).symm
      _ = toE (algebraMap K L (a : K)) := by
        rw [hbeta_val]
      _ = algebraMap C E (algebraMap K C (a : K)) :=
        AbsoluteValue.toAlgebraicLocalization_algebraMap
          vK w.1 w.2 (a : K)
  have hyE :
      yE ^ (n : ℕ) =
        Units.map (algebraMap C E).toMonoidHom aC := by
    calc
      yE ^ (n : ℕ) =
          Units.map (algebraMap C E).toMonoidHom
            (yC ^ (n : ℕ)) := by
        exact
          (map_pow
            (Units.map (algebraMap C E).toMonoidHom)
            yC (n : ℕ)).symm
      _ = Units.map (algebraMap C E).toMonoidHom aC := by
        rw [hyC]
  let q : Eˣ := betaE / yE
  have hq : q ^ (n : ℕ) = 1 :=
    KummerTheory.div_pow_eq_one_of_pow_eq_pow
      (hbetaE.trans hyE.symm)
  obtain ⟨zeta, hzeta_mem⟩ := hmu
  have hzeta :
      IsPrimitiveRoot zeta (n : ℕ) :=
    (mem_primitiveRoots n.pos).mp hzeta_mem
  have hzetaE :
      IsPrimitiveRoot
        (algebraMap C E (algebraMap K C zeta))
        (n : ℕ) :=
    (hzeta.map_of_injective
        (algebraMap K C).injective).map_of_injective
      (algebraMap C E).injective
  have hq_val :
      (q : E) ^ (n : ℕ) = 1 := by
    simpa using congrArg Units.val hq
  obtain ⟨i, _hi, hzetaq⟩ :=
    hzetaE.eq_pow_of_pow_eq_one hq_val
  have hbeta_base :
      toE (beta : L) ∈
        Set.range (algebraMap C E) := by
    refine
      ⟨(algebraMap K C zeta) ^ i * (yC : C), ?_⟩
    calc
      algebraMap C E
            ((algebraMap K C zeta) ^ i * (yC : C)) =
          (algebraMap C E (algebraMap K C zeta)) ^ i *
            algebraMap C E (yC : C) := by
        rw [map_mul, map_pow]
      _ = (q : E) * (yE : E) := by
        rw [hzetaq]
        rfl
      _ = toE (beta : L) := by
        simpa [betaE] using
          congrArg Units.val
            (show q * yE = betaE by simp [q])
  have hcomap :
      (beta : L) ∈
        ((algebraMap C E).fieldRange).comap toE :=
    hbeta_base
  rw [
    localizedCompletion_baseField_comap_eq_fixedField_decompositionGroup
      vK hvK w] at hcomap
  simpa [C, E, toE] using hcomap

omit [FiniteDimensional K L] in
open scoped Classical in
/-- A Kummer radicand is an `n`-th power in the finite-place completion
exactly when its chosen root belongs to the decomposition field at the
chosen extension of that place. -/
theorem
    finitePlaceKummerRadicand_mem_nthPowerSubgroup_iff_root_mem_decompositionFixedField
    (v : HeightOneSpectrum (𝓞 K))
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (a : Kˣ) (beta : Lˣ)
    (hbeta :
      beta ^ (n : ℕ) =
        Units.map (algebraMap K L).toMonoidHom a) :
    Units.map
          (algebraMap K (v.adicCompletion K)).toMonoidHom a ∈
        (powMonoidHom (n : ℕ) :
          (v.adicCompletion K)ˣ →*
            (v.adicCompletion K)ˣ).range ↔
      (beta : L) ∈
        IntermediateField.fixedField
          (absoluteValueDecompositionGroup K
            (chosenFinitePlaceExtension (L := L) v).1) := by
  let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  let vK := HeightOneSpectrum.adicAbv K v
  let w := chosenFinitePlaceExtension (L := L) v
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial v
  let hK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  let := localizedCompletionGlobalAlgebra vK w
  let := localizedCompletionIsScalarTower vK w
  let C := vK.Completion
  let E := LocalizedCompletion vK w
  let toE :=
    AbsoluteValue.toAlgebraicLocalization vK w.1 w.2
  let e :
      Cˣ ≃ₜ* (v.adicCompletion K)ˣ :=
    finitePlaceCompletionUnitsContinuousMulEquiv v
  let aC : Cˣ :=
    Units.map (algebraMap K C).toMonoidHom a
  have he_base (u : Kˣ) :
      e (Units.map (algebraMap K C).toMonoidHom u) =
        Units.map
          (algebraMap K (v.adicCompletion K)).toMonoidHom u := by
    apply Units.ext
    let x : WithAbs vK :=
      (WithAbs.equiv vK).symm (u : K)
    change
      finitePlaceCompletionRingHom v (x : C) =
        algebraMap K (v.adicCompletion K) (u : K)
    rw [finitePlaceCompletionRingHom_coe]
    rfl
  have hbeta_val :
      (beta : L) ^ (n : ℕ) =
        algebraMap K L (a : K) := by
    simpa using congrArg Units.val hbeta
  constructor
  · intro ha
    apply
      kummerRadicand_root_mem_decompositionFixedField_of_mem_nthPowerSubgroup
        (K := K) (L := L) vK hvK w n hmu a beta hbeta
    obtain ⟨y, hy⟩ :=
      (MonoidHom.mem_range
        (G := (v.adicCompletion K)ˣ)).mp ha
    rw [powMonoidHom_apply] at hy
    apply
      (MonoidHom.mem_range
        (G := Cˣ)).mpr
    refine ⟨e.symm y, ?_⟩
    rw [powMonoidHom_apply]
    apply e.injective
    calc
      e ((e.symm y) ^ (n : ℕ)) =
          (e (e.symm y)) ^ (n : ℕ) :=
        map_pow e (e.symm y) (n : ℕ)
      _ = y ^ (n : ℕ) := by
        rw [e.apply_symm_apply]
      _ =
          Units.map
            (algebraMap K
              (v.adicCompletion K)).toMonoidHom a := hy
      _ = e aC := (he_base a).symm
  · intro hfixed
    have hcomap :
        (beta : L) ∈
          ((algebraMap C E).fieldRange).comap toE := by
      rw [
        localizedCompletion_baseField_comap_eq_fixedField_decompositionGroup
          vK hvK w]
      simpa [vK, w] using hfixed
    change
      toE (beta : L) ∈ Set.range (algebraMap C E)
      at hcomap
    obtain ⟨y, hy⟩ := hcomap
    have hy_ne : y ≠ 0 := by
      intro hy_zero
      have hbeta_zero : (beta : L) = 0 := by
        apply toE.injective
        calc
          toE (beta : L) =
              algebraMap C E y := hy.symm
          _ = 0 := by rw [hy_zero, map_zero]
          _ = toE 0 := (map_zero toE).symm
      exact beta.ne_zero hbeta_zero
    let yC : Cˣ := Units.mk0 y hy_ne
    have hyC : yC ^ (n : ℕ) = aC := by
      apply Units.ext
      apply (algebraMap C E).injective
      change
        algebraMap C E (y ^ (n : ℕ)) =
          algebraMap C E (algebraMap K C (a : K))
      calc
        algebraMap C E (y ^ (n : ℕ)) =
            (algebraMap C E y) ^ (n : ℕ) := by
          exact
            map_pow (algebraMap C E) y (n : ℕ)
        _ = toE (beta : L) ^ (n : ℕ) := by
          rw [hy]
        _ = toE ((beta : L) ^ (n : ℕ)) := by
          exact
            (map_pow toE (beta : L) (n : ℕ)).symm
        _ = toE (algebraMap K L (a : K)) := by
          rw [hbeta_val]
        _ = algebraMap C E (algebraMap K C (a : K)) :=
          AbsoluteValue.toAlgebraicLocalization_algebraMap
            vK w.1 w.2 (a : K)
    apply
      (MonoidHom.mem_range
        (G := (v.adicCompletion K)ˣ)).mpr
    refine ⟨e yC, ?_⟩
    rw [powMonoidHom_apply]
    calc
      (e yC) ^ (n : ℕ) =
          e (yC ^ (n : ℕ)) := by
        exact
          (map_pow e yC (n : ℕ)).symm
      _ = e aC := by rw [hyC]
      _ =
          Units.map
            (algebraMap K
              (v.adicCompletion K)).toMonoidHom a :=
        he_base a

end KummerTheory
