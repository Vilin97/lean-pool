/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.CompletedZeta.ShapeTheta
public import LeanPool.Odlyzko.Theta.TraceCovolume

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

open Complex Module NumberField NumberField.InfinitePlace
open scoped nonZeroDivisors

namespace NumberField.Odlyzko

open mixedEmbedding

variable (K : Type*) [Field K] [NumberField K]

omit [NumberField K] in
open Classical in
private theorem radialMixedSpaceUnit_toLinearMap
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0) :
    ((radialMixedSpaceUnit K q hq).mulLeftLinearEquiv ℝ
        (mixedSpace K)).toLinearMap =
      LinearMap.prodMap
        (LinearMap.pi (fun w ↦
          (q w.1 • LinearMap.id).comp (LinearMap.proj w)))
        (LinearMap.pi (fun w ↦
          (q w.1 • LinearMap.id).comp (LinearMap.proj w))) := by
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · funext w
    simp [radialMixedSpaceUnit, mixedSpaceOfRealSpace_apply]
  · funext w
    simp [radialMixedSpaceUnit, mixedSpaceOfRealSpace_apply]

open Classical in
theorem det_radialMixedSpaceUnit
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0) :
    LinearMap.det
        ((radialMixedSpaceUnit K q hq).mulLeftLinearEquiv ℝ
          (mixedSpace K)).toLinearMap =
      (∏ w : {w : InfinitePlace K // IsReal w}, q w.1) *
        ∏ w : {w : InfinitePlace K // IsComplex w}, (q w.1) ^ 2 := by
  rw [radialMixedSpaceUnit_toLinearMap,
    LinearMap.det_prodMap, LinearMap.det_pi, LinearMap.det_pi]
  simp [LinearMap.det_smul]

open Classical in
theorem det_traceRadialScale
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0) :
    LinearMap.det (traceRadialScale K q hq).toLinearMap =
      (∏ w : {w : InfinitePlace K // IsReal w}, q w.1) *
        ∏ w : {w : InfinitePlace K // IsComplex w}, (q w.1) ^ 2 := by
  let r :=
    ((radialMixedSpaceUnit K q hq).mulLeftLinearEquiv ℝ
      (mixedSpace K)).toLinearMap
  have hdet :
      LinearMap.det (traceRadialScale K q hq).toLinearMap =
        LinearMap.det r := by
    exact LinearMap.det_conj r (traceToMixed K).symm.toLinearEquiv
  rw [hdet]
  exact det_radialMixedSpaceUnit K q hq

open Classical in
theorem covolume_shapeIdealLattice
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0) :
    ZLattice.covolume (shapeIdealLattice K I q hq) =
      |(∏ w : {w : InfinitePlace K // IsReal w}, q w.1) *
        ∏ w : {w : InfinitePlace K // IsComplex w}, (q w.1) ^ 2| *
        (FractionalIdeal.absNorm
          (I : FractionalIdeal (𝓞 K)⁰ K) * √|discr K|) := by
  have hsymm :
      LinearMap.det (traceRadialScale K q hq).symm.toLinearMap =
        (LinearMap.det (traceRadialScale K q hq).toLinearMap)⁻¹ :=
    LinearEquiv.det_coe_symm (traceRadialScale K q hq).toLinearEquiv
  rw [shapeIdealLattice,
    covolume_comap_continuousLinearEquiv
      (traceIdealLattice K I) MeasureTheory.volume
      (traceRadialScale K q hq).symm,
    hsymm,
    det_traceRadialScale, abs_inv, inv_inv,
    covolume_traceIdealLattice]

variable [IsTotallyComplex K]

open Classical in
theorem expMapBasis_neg
    (y : mixedEmbedding.realSpace K) (w : InfinitePlace K) :
    mixedEmbedding.fundamentalCone.expMapBasis (-y) w =
      (mixedEmbedding.fundamentalCone.expMapBasis y w)⁻¹ := by
  rw [mixedEmbedding.fundamentalCone.expMapBasis_apply,
    mixedEmbedding.fundamentalCone.expMapBasis_apply]
  simp [mixedEmbedding.fundamentalCone.expMap_apply, Real.exp_neg]

open Classical in
theorem covolume_shapeIdealLattice_expMapBasis
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (y : mixedEmbedding.realSpace K) :
    ZLattice.covolume
        (shapeIdealLattice K I
          (mixedEmbedding.fundamentalCone.expMapBasis y)
          (fun w ↦
            (mixedEmbedding.fundamentalCone.expMapBasis_pos y w).ne')) =
      Real.exp
          (y NumberField.Units.dirichletUnitTheorem.w₀ *
            (Module.finrank ℚ K : ℝ)) *
        (FractionalIdeal.absNorm
          (I : FractionalIdeal (𝓞 K)⁰ K) * √|discr K|) := by
  rw [covolume_shapeIdealLattice]
  have hreal :
      (∏ w : {w : InfinitePlace K // IsReal w},
        mixedEmbedding.fundamentalCone.expMapBasis y w.1) = 1 := by
    apply Finset.prod_eq_one
    intro w _
    exact False.elim
      (not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex w.1) w.2)
  have hcomplex :
      (∏ w : {w : InfinitePlace K // IsComplex w},
          (mixedEmbedding.fundamentalCone.expMapBasis y w.1) ^ 2) =
        (∏ w : InfinitePlace K,
          mixedEmbedding.fundamentalCone.expMapBasis y w) ^ 2 := by
    rw [← Finset.prod_pow]
    rw [← Equiv.prod_comp
      (Equiv.subtypeUnivEquiv
        (fun w : InfinitePlace K ↦ IsTotallyComplex.isComplex w))]
    simp
  rw [hreal, one_mul, hcomplex,
    prod_expMapBasis_eq_exp_half_finrank]
  have hexp :
      Real.exp
          (y NumberField.Units.dirichletUnitTheorem.w₀ *
            (Module.finrank ℚ K : ℝ) / 2) ^ 2 =
        Real.exp
          (y NumberField.Units.dirichletUnitTheorem.w₀ *
            (Module.finrank ℚ K : ℝ)) := by
    rw [pow_two, ← Real.exp_add]
    simp
  simp_all

end NumberField.Odlyzko
