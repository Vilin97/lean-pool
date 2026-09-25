/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.NormApproximation.InfinitePlaces
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.NormCore
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.SinglePlace
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
/-!
# Positive archimedean section of the idele norm

This module constructs an idele supported at one infinite place whose absolute
norm is a prescribed inverse.  Its finite components are trivial and all of
its infinite components lie in the standard positive subgroups.
-/

@[expose] public section

open scoped IsMulCommutative NNReal NumberField Topology
open NumberField IsDedekindDomain
open NumberField.Units.dirichletUnitTheorem

noncomputable
section

universe u

namespace IdeleGroup

variable {K : Type u} [Field K] [NumberField K]

open scoped Classical in
/-- A positive real unit placed in an archimedean completion.  At a complex
place it is first regarded as a complex unit. -/
private noncomputable def positiveArchimedeanLocalComponent
    (v : InfinitePlace K) :
    ℝ≥0ˣ →* v.Completionˣ := by
  by_cases hv : v.IsReal
  · exact
      (Units.mapEquiv
        (InfinitePlace.Completion.ringEquivRealOfIsReal
          hv).symm.toMulEquiv).toMonoidHom.comp
        (Units.map NNReal.toRealHom.toMonoidHom)
  · have hvc : v.IsComplex :=
      InfinitePlace.not_isReal_iff_isComplex.mp hv
    exact
      (Units.mapEquiv
        (InfinitePlace.Completion.ringEquivComplexOfIsComplex
          hvc).symm.toMulEquiv).toMonoidHom.comp
        ((Units.map Complex.ofRealHom.toMonoidHom).comp
          (Units.map NNReal.toRealHom.toMonoidHom))

open scoped Classical in
/-- The positive local archimedean component, with its natural continuity. -/
private noncomputable def positiveArchimedeanLocalComponentContinuous
    (v : InfinitePlace K) :
    ℝ≥0ˣ →ₜ* v.Completionˣ where
  __ := positiveArchimedeanLocalComponent v
  continuous_toFun := by
    by_cases hv : v.IsReal
    · have hcompletion :
          Continuous
            (Units.mapEquiv
              (InfinitePlace.Completion.ringEquivRealOfIsReal
                hv).symm.toMulEquiv) := by
        exact
          (RayClass.realCompletionContinuousMulEquiv v hv).symm.continuous.units_map
            (InfinitePlace.Completion.ringEquivRealOfIsReal
              hv).symm.toMonoidHom
      apply
        (hcompletion.comp
          (NNReal.continuous_coe.units_map
            NNReal.toRealHom.toMonoidHom)).congr
      intro r
      simp only [positiveArchimedeanLocalComponent,
        dite_eq_left hv]
      congr 2
    · have hvc : v.IsComplex :=
        InfinitePlace.not_isReal_iff_isComplex.mp hv
      have hcompletion :
          Continuous
            (Units.mapEquiv
              (InfinitePlace.Completion.ringEquivComplexOfIsComplex
                hvc).symm.toMulEquiv) := by
        exact
          (RayClass.complexCompletionContinuousMulEquiv v hvc).symm.continuous.units_map
            (InfinitePlace.Completion.ringEquivComplexOfIsComplex
              hvc).symm.toMonoidHom
      apply
        (hcompletion.comp
          ((Complex.continuous_ofReal.units_map
              Complex.ofRealHom.toMonoidHom).comp
            (NNReal.continuous_coe.units_map
              NNReal.toRealHom.toMonoidHom))).congr
      intro r
      simp only [positiveArchimedeanLocalComponent,
        dite_eq_right hv]
      congr 2

omit [NumberField K] in
open scoped Classical in
@[simp]
private theorem positiveArchimedeanLocalComponentContinuous_apply
    (v : InfinitePlace K) (r : ℝ≥0ˣ) :
    positiveArchimedeanLocalComponentContinuous v r =
      positiveArchimedeanLocalComponent v r :=
  rfl

omit [NumberField K] in
open scoped Classical in
private theorem positiveArchimedeanLocalComponent_nnnorm
    (v : InfinitePlace K) (r : ℝ≥0ˣ) :
    ‖((positiveArchimedeanLocalComponent v r :
        v.Completionˣ) : v.Completion)‖₊ =
      (r : ℝ≥0) := by
  by_cases hv : v.IsReal
  · let e : v.Completion ≃+* ℝ :=
      InfinitePlace.Completion.ringEquivRealOfIsReal hv
    have hcomponent :
        Units.mapEquiv e.toMulEquiv
            (positiveArchimedeanLocalComponent v r) =
          Units.map NNReal.toRealHom.toMonoidHom r := by
      simp only [positiveArchimedeanLocalComponent,
        dite_eq_left hv, MonoidHom.comp_apply]
      change
        Units.mapEquiv e.toMulEquiv
            (Units.mapEquiv e.symm.toMulEquiv
              (Units.map NNReal.toRealHom.toMonoidHom r)) =
          Units.map NNReal.toRealHom.toMonoidHom r
      exact
        (Units.mapEquiv e.toMulEquiv).apply_symm_apply
          (Units.map NNReal.toRealHom.toMonoidHom r)
    have hvalue :
        e
            ((positiveArchimedeanLocalComponent v r :
              v.Completionˣ) : v.Completion) =
          ((r : ℝ≥0ˣ) : ℝ) := by
      simpa [e] using congrArg Units.val hcomponent
    apply NNReal.eq
    simp only [coe_nnnorm]
    calc
      ‖((positiveArchimedeanLocalComponent v r :
          v.Completionˣ) : v.Completion)‖ =
          ‖e
            ((positiveArchimedeanLocalComponent v r :
              v.Completionˣ) : v.Completion)‖ :=
        ((InfinitePlace.Completion.isometryEquivRealOfIsReal
          hv).isometry.norm_map_of_map_zero
          (map_zero e) _).symm
      _ = ‖((r : ℝ≥0ˣ) : ℝ)‖ := by rw [hvalue]
      _ = ((r : ℝ≥0ˣ) : ℝ) :=
        Real.norm_of_nonneg (r : ℝ≥0).coe_nonneg
  · have hvc : v.IsComplex :=
      InfinitePlace.not_isReal_iff_isComplex.mp hv
    let e : v.Completion ≃+* ℂ :=
      InfinitePlace.Completion.ringEquivComplexOfIsComplex hvc
    have hcomponent :
        Units.mapEquiv e.toMulEquiv
            (positiveArchimedeanLocalComponent v r) =
          Units.map Complex.ofRealHom.toMonoidHom
            (Units.map NNReal.toRealHom.toMonoidHom r) := by
      simp only [positiveArchimedeanLocalComponent,
        dite_eq_right hv, MonoidHom.comp_apply]
      change
        Units.mapEquiv e.toMulEquiv
            (Units.mapEquiv e.symm.toMulEquiv
              (Units.map Complex.ofRealHom.toMonoidHom
                (Units.map NNReal.toRealHom.toMonoidHom r))) =
          Units.map Complex.ofRealHom.toMonoidHom
            (Units.map NNReal.toRealHom.toMonoidHom r)
      exact
        (Units.mapEquiv e.toMulEquiv).apply_symm_apply
          (Units.map Complex.ofRealHom.toMonoidHom
            (Units.map NNReal.toRealHom.toMonoidHom r))
    have hvalue :
        e
            ((positiveArchimedeanLocalComponent v r :
              v.Completionˣ) : v.Completion) =
          (((r : ℝ≥0ˣ) : ℝ) : ℂ) := by
      simpa [e] using congrArg Units.val hcomponent
    apply NNReal.eq
    simp only [coe_nnnorm]
    calc
      ‖((positiveArchimedeanLocalComponent v r :
          v.Completionˣ) : v.Completion)‖ =
          ‖e
            ((positiveArchimedeanLocalComponent v r :
              v.Completionˣ) : v.Completion)‖ :=
        ((InfinitePlace.Completion.isometryEquivComplexOfIsComplex
          hvc).isometry.norm_map_of_map_zero
          (map_zero e) _).symm
      _ = ‖(((r : ℝ≥0ˣ) : ℝ) : ℂ)‖ := by rw [hvalue]
      _ = ‖((r : ℝ≥0ˣ) : ℝ)‖ := Complex.norm_real _
      _ = ((r : ℝ≥0ˣ) : ℝ) :=
        Real.norm_of_nonneg (r : ℝ≥0).coe_nonneg

omit [NumberField K] in
open scoped Classical in
private theorem positiveArchimedeanLocalComponent_mem_positive
    (v : InfinitePlace K) (r : ℝ≥0ˣ) :
    positiveArchimedeanLocalComponent v r ∈
      RayClass.infinitePositiveSubgroup v := by
  rw [RayClass.mem_infinitePositiveSubgroup_iff]
  intro hv
  let e : v.Completion ≃+* ℝ :=
    InfinitePlace.Completion.ringEquivRealOfIsReal hv
  have hcomponent :
      Units.mapEquiv e.toMulEquiv
          (positiveArchimedeanLocalComponent v r) =
        Units.map NNReal.toRealHom.toMonoidHom r := by
    simp only [positiveArchimedeanLocalComponent,
      dite_eq_left hv, MonoidHom.comp_apply]
    change
      Units.mapEquiv e.toMulEquiv
          (Units.mapEquiv e.symm.toMulEquiv
            (Units.map NNReal.toRealHom.toMonoidHom r)) =
        Units.map NNReal.toRealHom.toMonoidHom r
    exact
      (Units.mapEquiv e.toMulEquiv).apply_symm_apply
        (Units.map NNReal.toRealHom.toMonoidHom r)
  have hvalue :
      e
          ((positiveArchimedeanLocalComponent v r :
            v.Completionˣ) : v.Completion) =
        ((r : ℝ≥0ˣ) : ℝ) := by
    simpa [e] using congrArg Units.val hcomponent
  change
    0 < e
      ((positiveArchimedeanLocalComponent v r :
        v.Completionˣ) : v.Completion)
  rw [hvalue]
  exact NNReal.coe_pos.mpr
    (pos_iff_ne_zero.mpr r.ne_zero)

open scoped Classical in
/-- The positive root needed to compensate for the multiplicity of the
chosen infinite place. -/
private noncomputable def positiveArchimedeanRoot :
    ℝ≥0ˣ →* ℝ≥0ˣ :=
  Units.map
    (NNReal.rpowMonoidHom
      (((w₀ (K := K)).mult : ℝ)⁻¹))

open scoped Classical in
/-- The positive root map used in the archimedean section is continuous. -/
private noncomputable def positiveArchimedeanRootContinuous :
    ℝ≥0ˣ →ₜ* ℝ≥0ˣ where
  __ := positiveArchimedeanRoot (K := K)
  continuous_toFun :=
    (NNReal.continuous_rpow_const
      (inv_nonneg.mpr (Nat.cast_nonneg _))).units_map
        (NNReal.rpowMonoidHom
          (((w₀ (K := K)).mult : ℝ)⁻¹))

open scoped Classical in
/-- The positive archimedean idele over a number field.  Its finite part is
one, and its sole nontrivial infinite component has been normalized so that
the total archimedean norm is the input. -/
noncomputable def positiveArchimedeanSection
    (K : Type u) [Field K] [NumberField K] :
    ℝ≥0ˣ →* IdeleGroup K :=
  (IdeleGroup.infinitePlaceIdele
      (w₀ (K := K))).comp
    ((positiveArchimedeanLocalComponent
        (w₀ (K := K))).comp
      (positiveArchimedeanRoot (K := K)))

open scoped Classical in
/-- The positive archimedean section as a continuous homomorphism. -/
noncomputable def positiveArchimedeanSectionContinuous
    (K : Type u) [Field K] [NumberField K] :
    ℝ≥0ˣ →ₜ* IdeleGroup K :=
  (IdeleGroup.infinitePlaceIdeleContinuous
      (w₀ (K := K))).comp
    ((positiveArchimedeanLocalComponentContinuous
        (w₀ (K := K))).comp
      (positiveArchimedeanRootContinuous (K := K)))

open scoped Classical in
@[simp]
theorem positiveArchimedeanSectionContinuous_apply
    (r : ℝ≥0ˣ) :
    positiveArchimedeanSectionContinuous K r =
      positiveArchimedeanSection K r :=
  rfl

open scoped Classical in
/-- The positive archimedean section is continuous. -/
theorem continuous_positiveArchimedeanSection :
    Continuous (positiveArchimedeanSection K) :=
  (positiveArchimedeanSectionContinuous K).continuous_toFun

open scoped Classical in
private theorem positiveArchimedeanSection_infiniteComponent_same
    (r : ℝ≥0ˣ) :
    IdeleGroup.infiniteComponent (w₀ (K := K))
        (positiveArchimedeanSection K r) =
      positiveArchimedeanLocalComponent
        (w₀ (K := K))
        (positiveArchimedeanRoot (K := K) r) := by
  change
    IdeleGroup.infiniteComponent (w₀ (K := K))
        (IdeleGroup.infinitePlaceIdele
          (w₀ (K := K))
          (positiveArchimedeanLocalComponent
            (w₀ (K := K))
            (positiveArchimedeanRoot (K := K) r))) = _
  rw [IdeleGroup.infinitePlaceIdele_infiniteComponent_same]

open scoped Classical in
private theorem positiveArchimedeanSection_infiniteComponent_of_ne
    (r : ℝ≥0ˣ) (v : InfinitePlace K)
    (hv : v ≠ w₀ (K := K)) :
    IdeleGroup.infiniteComponent v
        (positiveArchimedeanSection K r) =
      1 := by
  change
    IdeleGroup.infiniteComponent v
        (IdeleGroup.infinitePlaceIdele
          (w₀ (K := K))
          (positiveArchimedeanLocalComponent
            (w₀ (K := K))
            (positiveArchimedeanRoot (K := K) r))) = 1
  exact
    IdeleGroup.infinitePlaceIdele_infiniteComponent_of_ne
      (w₀ (K := K)) v _ hv

open scoped Classical in
/-- Every finite component of the positive archimedean idele is one. -/
theorem positiveArchimedeanSection_finiteComponent
    (r : ℝ≥0ˣ)
    (v : HeightOneSpectrum (𝓞 K)) :
    IdeleGroup.finiteComponent v
        (positiveArchimedeanSection K r) =
      1 := by
  change
    IdeleGroup.finiteComponent v
        (IdeleGroup.infinitePlaceIdele
          (w₀ (K := K))
          (positiveArchimedeanLocalComponent
            (w₀ (K := K))
            (positiveArchimedeanRoot (K := K) r))) = 1
  rw [IdeleGroup.infinitePlaceIdele_finiteComponent]

open scoped Classical in
/-- Every infinite component of the positive archimedean idele lies in the
standard positive subgroup. -/
theorem positiveArchimedeanSection_infiniteComponent_mem_positive
    (r : ℝ≥0ˣ) (v : InfinitePlace K) :
    IdeleGroup.infiniteComponent v
        (positiveArchimedeanSection K r) ∈
      RayClass.infinitePositiveSubgroup v := by
  by_cases hv : v = w₀ (K := K)
  · subst v
    rw [positiveArchimedeanSection_infiniteComponent_same]
    exact
      positiveArchimedeanLocalComponent_mem_positive
        (w₀ (K := K))
        (positiveArchimedeanRoot (K := K) r)
  · rw [positiveArchimedeanSection_infiniteComponent_of_ne
      r v hv]
    exact Subgroup.one_mem _

open scoped Classical in
/-- The positive archimedean idele has absolute idele norm `r⁻¹`. -/
theorem positiveArchimedeanSection_absoluteNorm
    (r : ℝ≥0ˣ) :
    IdeleGroup.absoluteNorm
        (positiveArchimedeanSection K r) =
      r⁻¹ := by
  have hlocal :=
    positiveArchimedeanLocalComponent_nnnorm
      (w₀ (K := K))
      (positiveArchimedeanRoot (K := K) r)
  have hlocal' :
      ‖((positiveArchimedeanLocalComponent
          (w₀ (K := K))
          (positiveArchimedeanRoot (K := K) r) :
            (w₀ (K := K)).Completionˣ) :
          (w₀ (K := K)).Completion)‖₊ =
        (r : ℝ≥0) ^
          (((w₀ (K := K)).mult : ℝ)⁻¹) := by
    simpa [positiveArchimedeanRoot] using hlocal
  have hinfinite :
      InfiniteIdeleGroup.archimedeanNorm
          (positiveArchimedeanSection K r).1 =
        r := by
    rw [InfiniteIdeleGroup.archimedeanNorm_apply]
    classical
    rw [Finset.prod_eq_single (w₀ (K := K))]
    · apply Units.ext
      change
        ‖((IdeleGroup.infiniteComponent (w₀ (K := K))
            (positiveArchimedeanSection K r) :
              (w₀ (K := K)).Completionˣ) :
            (w₀ (K := K)).Completion)‖₊ ^
            (w₀ (K := K)).mult =
          (r : ℝ≥0)
      rw [positiveArchimedeanSection_infiniteComponent_same,
        hlocal']
      exact
        NNReal.rpow_inv_natCast_pow
          (r : ℝ≥0) InfinitePlace.mult_ne_zero
    · intro v _ hv
      have hcomponent :
          InfiniteIdeleGroup.component v
              (positiveArchimedeanSection K r).1 =
            1 := by
        change
          IdeleGroup.infiniteComponent v
              (positiveArchimedeanSection K r) = 1
        exact
          positiveArchimedeanSection_infiniteComponent_of_ne
            r v hv
      rw [hcomponent, map_one, one_pow]
    · intro h
      exact (h (Finset.mem_univ _)).elim
  rw [IdeleGroup.absoluteNorm_apply]
  change
    FiniteIdeleGroup.absoluteNorm (1 : FiniteIdeleGroup K) *
        (InfiniteIdeleGroup.archimedeanNorm
          (positiveArchimedeanSection K r).1)⁻¹ =
      r⁻¹
  rw [map_one, hinfinite, one_mul]

open scoped Classical in
/-- Multiplying an idele by its positive archimedean correction produces an
idele of absolute norm one. -/
noncomputable def positiveArchimedeanNormOneCorrection
    (K : Type u) [Field K] [NumberField K]
    (a : IdeleGroup K) :
    IdeleGroup.normOneSubgroup (K := K) :=
  ⟨a * positiveArchimedeanSection K (IdeleGroup.absoluteNorm a), by
    change
      IdeleGroup.absoluteNorm
          (a * positiveArchimedeanSection K
            (IdeleGroup.absoluteNorm a)) =
        1
    rw [map_mul, positiveArchimedeanSection_absoluteNorm]
    exact mul_inv_cancel (IdeleGroup.absoluteNorm a)⟩

open scoped Classical in
/-- The underlying idele of the norm-one correction is its defining product. -/
@[simp]
theorem positiveArchimedeanNormOneCorrection_coe
    (a : IdeleGroup K) :
    (positiveArchimedeanNormOneCorrection K a : IdeleGroup K) =
      a * positiveArchimedeanSection K (IdeleGroup.absoluteNorm a) :=
  rfl

open scoped Classical in
/-- Every idele is its norm-one correction multiplied by the inverse of the
positive archimedean section. -/
theorem eq_positiveArchimedeanNormOneCorrection_mul_section_inv
    (a : IdeleGroup K) :
    a =
      (positiveArchimedeanNormOneCorrection K a : IdeleGroup K) *
        (positiveArchimedeanSection K
          (IdeleGroup.absoluteNorm a))⁻¹ := by
  rw [positiveArchimedeanNormOneCorrection_coe]
  exact (mul_inv_cancel_right a
    (positiveArchimedeanSection K
      (IdeleGroup.absoluteNorm a))).symm


end IdeleGroup
