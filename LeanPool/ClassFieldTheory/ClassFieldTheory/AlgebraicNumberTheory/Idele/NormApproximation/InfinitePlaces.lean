/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalBlocks.TensorNorm
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.NormApproximation.FinitePlaces
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Ramification.Splitting.FinitePlace
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.RayClass.Approximation
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.RayClass.Topology
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Completion.FiniteLocalization
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.FieldTheory.IsAlgClosed.Basic
/-!
# Archimedean norm approximation

This file supplies the archimedean source used in the norm-approximation
argument. At a real place the positive units have
an `n`-th root, while at a complex place every unit has one.  Consequently
the standard positive subgroup is contained in the determinant-norm image
of every scalar extension of positive degree.
-/

@[expose] public section

open scoped NumberField TensorProduct
open NumberField IsDedekindDomain
open LocalFieldTheory

noncomputable section

open LocalClassFieldTheory

universe u v

section ArchimedeanNorm

variable {K : Type u} [Field K] [NumberField K]

omit [NumberField K] in
/-- Every element of the archimedean positive subgroup has an `n`-th
root for `n > 0`.  At complex places the positivity condition is
vacuous and algebraic closedness supplies the root. -/
theorem exists_infinitePositiveSubgroup_nthRoot
    (v : InfinitePlace K)
    (n : ℕ) (hn : 0 < n)
    (x : v.Completionˣ)
    (hx : x ∈ RayClass.infinitePositiveSubgroup v) :
    ∃ y : v.Completionˣ, y ^ n = x := by
  by_cases hv : v.IsReal
  · let e : v.Completion ≃+* ℝ :=
      InfinitePlace.Completion.ringEquivRealOfIsReal hv
    let eu : v.Completionˣ ≃* ℝˣ :=
      Units.mapEquiv e.toMulEquiv
    have hxpos : 0 < ((eu x : ℝˣ) : ℝ) := by
      exact
        ((RayClass.mem_infinitePositiveSubgroup_iff v x).mp hx) hv
    let yr : ℝ :=
      ((eu x : ℝˣ) : ℝ) ^ ((n : ℝ)⁻¹)
    have hyrpow :
        yr ^ n = ((eu x : ℝˣ) : ℝ) := by
      exact Real.rpow_inv_natCast_pow hxpos.le hn.ne'
    have hyrne : yr ≠ 0 := by
      intro hyr
      rw [hyr, zero_pow hn.ne'] at hyrpow
      exact (eu x).ne_zero hyrpow.symm
    let yu : ℝˣ := Units.mk0 yr hyrne
    refine ⟨eu.symm yu, ?_⟩
    apply eu.injective
    simp only [map_pow, eu.apply_symm_apply]
    apply Units.ext
    exact hyrpow
  · have hvc : v.IsComplex :=
      InfinitePlace.not_isReal_iff_isComplex.mp hv
    let e : v.Completion ≃+* ℂ :=
      InfinitePlace.Completion.ringEquivComplexOfIsComplex hvc
    let eu : v.Completionˣ ≃* ℂˣ :=
      Units.mapEquiv e.toMulEquiv
    obtain ⟨z, hz⟩ :=
      IsAlgClosed.exists_pow_nat_eq
        ((eu x : ℂˣ) : ℂ) hn
    have hz0 : z ≠ 0 := by
      intro hzero
      rw [hzero, zero_pow hn.ne'] at hz
      exact (eu x).ne_zero hz.symm
    let zu : ℂˣ := Units.mk0 z hz0
    refine ⟨eu.symm zu, ?_⟩
    apply eu.injective
    simp only [map_pow, eu.apply_symm_apply]
    apply Units.ext
    exact hz

variable {L : Type v} [Field L] [Algebra K L]
    [FiniteDimensional K L]

/-- Determinant norm on the actual tensor factor used by the infinite
component of the relative adele ring. -/
def infiniteTensorDetNorm
    (v : InfinitePlace K) :
    (v.Completion ⊗[K] L)ˣ →* v.Completionˣ :=
  Units.map (Algebra.norm v.Completion)

/-- Image of the determinant norm on an infinite tensor factor. -/
def infiniteTensorNormSubgroup
    (v : InfinitePlace K) :
    Subgroup v.Completionˣ :=
  (infiniteTensorDetNorm (K := K) (L := L) v).range

/-- The positive subgroup at an infinite place lies in the determinant
norm image of the corresponding local tensor algebra. -/
theorem infinitePositiveSubgroup_le_infiniteTensorNormSubgroup
    (v : InfinitePlace K) :
    RayClass.infinitePositiveSubgroup v ≤
      infiniteTensorNormSubgroup (K := K) (L := L) v := by
  intro x hx
  let n := Module.finrank K L
  have hn : 0 < n :=
    Module.finrank_pos
  obtain ⟨y, hy⟩ :=
    exists_infinitePositiveSubgroup_nthRoot
      v n hn x hx
  let z : (v.Completion ⊗[K] L)ˣ :=
    Units.map
      (algebraMap v.Completion
        (v.Completion ⊗[K] L)).toMonoidHom y
  refine ⟨z, ?_⟩
  apply Units.ext
  change
    Algebra.norm v.Completion
        (algebraMap v.Completion
          (v.Completion ⊗[K] L)
          (y : v.Completion)) =
      (x : v.Completion)
  rw [Algebra.norm_algebraMap,
    Module.finrank_baseChange]
  exact congrArg Units.val hy

end ArchimedeanNorm

variable {K : Type} [Field K] [NumberField K]
variable {L : Type} [Field L] [Algebra K L]
    [FiniteDimensional K L]

/-- Complete splitting at a finite place makes the chosen local norm
subgroup the whole multiplicative group. -/
theorem chosenFinitePlaceLocalNormSubgroup_eq_top_of_splitsCompletely
    [IsGalois K L]
    (v : HeightOneSpectrum (𝓞 K))
    (hsplit :
      FinitePlaceSplitsCompletely
        (K := K) (L := L) v) :
    chosenFinitePlaceLocalNormSubgroup
        (K := K) (L := L) v = ⊤ := by
  apply top_unique
  intro x _
  let vK :=
    NumberField.HeightOneSpectrum.adicAbv K v
  let w := chosenFinitePlaceExtension (L := L) v
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial v
  let hK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  let E :=
    AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
  let : FiniteDimensional vK.Completion E :=
    AlgebraicNumberTheory.Valuations.localizedCompletionModuleFinite
      vK hvK w
  have hdegree :
      Module.finrank vK.Completion E = 1 := by
    simpa [finitePlaceLocalDegree, vK, w, E] using
      (finitePlaceSplitsCompletely_iff_localDegree_eq_one
        (K := K) (L := L) v).mp hsplit
  let e :
      vK.Completionˣ ≃ₜ* (v.adicCompletion K)ˣ :=
    finitePlaceCompletionUnitsContinuousMulEquiv v
  change x ∈
    (localNormSubgroup vK.Completion E).map e.toMonoidHom
  refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
  refine
    ⟨LocalFieldTheory.IsNonarchimedeanLocalField.mapBaseUnitsToExtensionUnits
        vK.Completion E (e.symm x), ?_⟩
  change
    LocalFieldTheory.normUnits
        vK.Completion E
        (LocalFieldTheory.IsNonarchimedeanLocalField.mapBaseUnitsToExtensionUnits
          vK.Completion E (e.symm x)) =
      e.symm x
  simpa [hdegree] using
    (LocalFieldTheory.IsNonarchimedeanLocalField.normUnits_algebraMap_base
      (K := vK.Completion) (L := E) (e.symm x))

/-- Simultaneous weak approximation into the concrete finite local norm
subgroups and into the archimedean tensor-norm images. -/
theorem exists_principal_quotient_mem_localNormSubgroups
    [IsGalois K L]
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (a : IdeleGroup K) :
    ∃ x : Kˣ,
      (∀ v : ↥S,
        IdeleGroup.finiteComponent v.1 a *
            (IdeleGroup.finiteComponent v.1
              (IdeleGroup.principalIdele K x))⁻¹ ∈
          chosenFinitePlaceLocalNormSubgroup
            (K := K) (L := L) v.1) ∧
      (∀ w : InfinitePlace K,
        IdeleGroup.infiniteComponent w a *
            (IdeleGroup.infiniteComponent w
              (IdeleGroup.principalIdele K x))⁻¹ ∈
          infiniteTensorNormSubgroup
            (K := K) (L := L) w) := by
  obtain ⟨x, hfinite, hinfinite⟩ :=
    IdeleGroup.exists_principal_quotient_mem_openAllLocalSubgroups_finset
      S a
      (fun v =>
        chosenFinitePlaceLocalNormSubgroup
          (K := K) (L := L) v.1)
      (fun w => RayClass.infinitePositiveSubgroup w)
      (fun v =>
        chosenFinitePlaceLocalNormSubgroup_isOpen
          (K := K) (L := L) v.1)
      (fun w => RayClass.isOpen_infinitePositiveSubgroup w)
  refine ⟨x, hfinite, ?_⟩
  intro w
  exact
    infinitePositiveSubgroup_le_infiniteTensorNormSubgroup
      (K := K) (L := L) w (hinfinite w)

/-- If all finite places outside a finite set split completely, one
principal correction makes a given idele a determinant norm locally at
every finite and infinite place. -/
theorem exists_principal_quotient_locallyNormEverywhere_of_splitsOutside
    [IsGalois K L]
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hsplit :
      ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
        FinitePlaceSplitsCompletely
          (K := K) (L := L) v)
    (a : IdeleGroup K) :
    ∃ x : Kˣ,
      (∀ v : HeightOneSpectrum (𝓞 K),
        IdeleGroup.finiteComponent v a *
            (IdeleGroup.finiteComponent v
              (IdeleGroup.principalIdele K x))⁻¹ ∈
          chosenFinitePlaceLocalNormSubgroup
            (K := K) (L := L) v) ∧
      (∀ w : InfinitePlace K,
        IdeleGroup.infiniteComponent w a *
            (IdeleGroup.infiniteComponent w
              (IdeleGroup.principalIdele K x))⁻¹ ∈
          infiniteTensorNormSubgroup
            (K := K) (L := L) w) := by
  obtain ⟨x, hfinite, hinfinite⟩ :=
    exists_principal_quotient_mem_localNormSubgroups
      (K := K) (L := L) S a
  refine ⟨x, ?_, hinfinite⟩
  intro v
  by_cases hv : v ∈ S
  · exact hfinite ⟨v, hv⟩
  · rw [
      chosenFinitePlaceLocalNormSubgroup_eq_top_of_splitsCompletely
        (K := K) (L := L) v (hsplit v hv)]
    exact Subgroup.mem_top _
