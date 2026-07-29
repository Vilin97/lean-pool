/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.CompletedZeta.RadialKernelFormula
public import LeanPool.Odlyzko.Theta.PoissonSummation
public import LeanPool.Odlyzko.Theta.TraceDualLattice

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

open Complex NumberField NumberField.InfinitePlace
open scoped nonZeroDivisors

namespace NumberField.Odlyzko

open mixedEmbedding

variable (K : Type*) [Field K] [NumberField K]

open Classical in
/-- A radial mixed space unit used in the Odlyzko-bound argument. -/
noncomputable def radialMixedSpaceUnit
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0) :
    (mixedSpace K)ˣ where
  val := mixedSpaceOfRealSpace q
  inv := mixedSpaceOfRealSpace fun w ↦ (q w)⁻¹
  val_inv := by
    rw [mixedSpaceOfRealSpace_apply, mixedSpaceOfRealSpace_apply]
    apply Prod.ext
    · funext w
      simp [hq w.1]
    · funext w
      simp_all
  inv_val := by
    rw [mixedSpaceOfRealSpace_apply, mixedSpaceOfRealSpace_apply]
    apply Prod.ext
    · funext w
      simp [hq w.1]
    · funext w
      simp_all

omit [NumberField K] in
open Classical in
@[simp]
theorem radialMixedSpaceUnit_val
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0) :
    (radialMixedSpaceUnit K q hq : mixedSpace K) =
      mixedSpaceOfRealSpace q :=
  rfl

open Classical in
/-- A trace radial scale used in the Odlyzko-bound argument. -/
noncomputable def traceRadialScale
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0) :
    mixedEmbedding.euclidean.mixedSpace K ≃L[ℝ]
      mixedEmbedding.euclidean.mixedSpace K :=
  ((traceToMixed K).toLinearEquiv.trans
      ((radialMixedSpaceUnit K q hq).mulLeftLinearEquiv ℝ (mixedSpace K))).trans
    (traceToMixed K).symm.toLinearEquiv |>.toContinuousLinearEquiv

open Classical in
theorem traceToMixed_traceRadialScale
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0)
    (v : mixedEmbedding.euclidean.mixedSpace K) :
    traceToMixed K (traceRadialScale K q hq v) =
      mixedSpaceOfRealSpace q * traceToMixed K v := by
  rw [traceRadialScale]
  simp

open Classical in
theorem inner_traceRadialScale
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0)
    (v z : mixedEmbedding.euclidean.mixedSpace K) :
    inner ℝ (traceRadialScale K q hq v) z =
      inner ℝ v (traceRadialScale K q hq z) := by
  suffices
    (∑ w : {w : InfinitePlace K // IsReal w},
        (WithLp.fst z).ofLp w * (q w.1 * (WithLp.fst v).ofLp w)) +
      ∑ w : {w : InfinitePlace K // IsComplex w},
        (((WithLp.snd z).ofLp w).re *
            (Real.sqrt 2 *
              (q w.1 * divideBySqrtTwo ((WithLp.snd v).ofLp w)).re) +
          ((WithLp.snd z).ofLp w).im *
            (Real.sqrt 2 *
              (q w.1 * divideBySqrtTwo ((WithLp.snd v).ofLp w)).im)) =
      (∑ w : {w : InfinitePlace K // IsReal w},
          q w.1 * (WithLp.fst z).ofLp w * (WithLp.fst v).ofLp w) +
        ∑ w : {w : InfinitePlace K // IsComplex w},
          (Real.sqrt 2 *
              (q w.1 * divideBySqrtTwo ((WithLp.snd z).ofLp w)).re *
              ((WithLp.snd v).ofLp w).re +
            Real.sqrt 2 *
              (q w.1 * divideBySqrtTwo ((WithLp.snd z).ofLp w)).im *
              ((WithLp.snd v).ofLp w).im) by
    simpa [traceRadialScale, traceToMixed, unscaleComplexCoordinates,
      mixedEmbedding.euclidean.toMixed, mixedSpaceOfRealSpace_apply,
      radialMixedSpaceUnit, WithLp.prod_inner_apply, PiLp.inner_apply,
      LinearEquiv.prodCongr_symm, LinearEquiv.prodCongr_apply,
      ContinuousLinearEquiv.prodCongr_symm, ContinuousLinearEquiv.prodCongr_apply,
      ContinuousLinearEquiv.piCongrRight_symm_apply]
  apply congrArg₂ (· + ·)
  · grind
  · apply Finset.sum_congr rfl
    intro w _
    simp [divideBySqrtTwo]
    ring

open Classical in
theorem traceRadialScale_symm_apply
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0)
    (v : mixedEmbedding.euclidean.mixedSpace K) :
    (traceRadialScale K q hq).symm v =
      traceRadialScale K (fun w ↦ (q w)⁻¹)
        (fun w ↦ inv_ne_zero (hq w)) v := by
  apply (traceToMixed K).injective
  rw [traceToMixed_traceRadialScale]
  have h := traceToMixed_traceRadialScale K q hq
    ((traceRadialScale K q hq).symm v)
  rw [ContinuousLinearEquiv.apply_symm_apply] at h
  rw [mixedSpaceOfRealSpace_apply]
  apply Prod.ext
  · funext w
    have hw := congrFun (congrArg Prod.fst h) w
    change (traceToMixed K ((traceRadialScale K q hq).symm v)).1 w =
      (q w.1)⁻¹ * (traceToMixed K v).1 w
    change (traceToMixed K v).1 w =
      q w.1 * (traceToMixed K ((traceRadialScale K q hq).symm v)).1 w at hw
    rw [hw]
    simp_all
  · funext w
    have hw := congrFun (congrArg Prod.snd h) w
    change (traceToMixed K ((traceRadialScale K q hq).symm v)).2 w =
      ((↑((q w.1)⁻¹) : ℂ) * (traceToMixed K v).2 w)
    change (traceToMixed K v).2 w =
      (q w.1 : ℂ) *
        (traceToMixed K ((traceRadialScale K q hq).symm v)).2 w at hw
    rw [hw]
    simp_all

open Classical in
theorem traceConjugation_traceRadialScale
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0)
    (v : mixedEmbedding.euclidean.mixedSpace K) :
    traceConjugation K (traceRadialScale K q hq v) =
      traceRadialScale K q hq (traceConjugation K v) := by
  suffices
    (fun w ↦ (Real.sqrt 2 : ℂ) *
        ((q w.1 : ℂ) *
          starRingEnd ℂ (divideBySqrtTwo ((WithLp.snd v).ofLp w)))) =
      (ContinuousLinearEquiv.piCongrRight
        (fun _ ↦ divideBySqrtTwo)).symm
          ((fun w ↦ (q w.1 : ℂ)) *
            (ContinuousLinearEquiv.piCongrRight
              (fun _ ↦ divideBySqrtTwo))
                (fun w ↦ starRingEnd ℂ ((WithLp.snd v).ofLp w))) by
    simpa [traceConjugation, traceRadialScale, traceToMixed,
      unscaleComplexCoordinates, mixedEmbedding.euclidean.toMixed,
      mixedSpaceOfRealSpace_apply, radialMixedSpaceUnit,
      LinearEquiv.prodCongr_symm, LinearEquiv.prodCongr_apply,
      ContinuousLinearEquiv.prodCongr_symm, ContinuousLinearEquiv.prodCongr_apply,
      ContinuousLinearEquiv.piCongrRight_symm_apply]
  funext w
  rw [ContinuousLinearEquiv.piCongrRight_symm_apply,
    divideBySqrtTwo_symm_apply]
  simp [divideBySqrtTwo]

open Classical in
/-- A shape ideal lattice used in the Odlyzko-bound argument. -/
noncomputable def shapeIdealLattice
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0) :
    Submodule ℤ (mixedEmbedding.euclidean.mixedSpace K) :=
  ZLattice.comap ℝ (traceIdealLattice K I)
    (traceRadialScale K q hq).symm.toLinearMap

open Classical in
instance
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0) :
    DiscreteTopology (shapeIdealLattice K I q hq) := by
  unfold shapeIdealLattice
  infer_instance

open Classical in
instance
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0) :
    IsZLattice ℝ (shapeIdealLattice K I q hq) := by
  unfold shapeIdealLattice
  infer_instance

open Classical in
/-- A conjugate shape ideal lattice used in the Odlyzko-bound argument. -/
noncomputable def conjugateShapeIdealLattice
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0) :
    Submodule ℤ (mixedEmbedding.euclidean.mixedSpace K) :=
  (shapeIdealLattice K I q hq).map
    ((traceConjugation K).toLinearEquiv.restrictScalars ℤ).toLinearMap

open Classical in
theorem mem_conjugateShapeIdealLattice_iff
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0)
    (v : mixedEmbedding.euclidean.mixedSpace K) :
    v ∈ conjugateShapeIdealLattice K I q hq ↔
      traceConjugation K v ∈ shapeIdealLattice K I q hq := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro hv
    refine ⟨traceConjugation K v, hv, ?_⟩
    simp

open Classical in
theorem mem_conjugateTraceIdealLattice_iff
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (v : mixedEmbedding.euclidean.mixedSpace K) :
    v ∈ conjugateTraceIdealLattice K I ↔
      traceConjugation K v ∈ traceIdealLattice K I := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro hv
    refine ⟨traceConjugation K v, hv, ?_⟩
    simp

open Classical in
theorem mem_dualLattice_shapeIdealLattice_iff
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0)
    (v : mixedEmbedding.euclidean.mixedSpace K) :
    v ∈ dualLattice (shapeIdealLattice K I q hq) ↔
      traceRadialScale K q hq v ∈ dualLattice (traceIdealLattice K I) := by
  rw [mem_dualLattice_iff, mem_dualLattice_iff]
  constructor
  · intro hv x
    have hx :
        traceRadialScale K q hq (x : mixedEmbedding.euclidean.mixedSpace K) ∈
          shapeIdealLattice K I q hq := by
      change
        (traceRadialScale K q hq).symm
            (traceRadialScale K q hq
              (x : mixedEmbedding.euclidean.mixedSpace K)) ∈
          traceIdealLattice K I
      simp
    obtain ⟨n, hn⟩ := hv
      ⟨traceRadialScale K q hq
        (x : mixedEmbedding.euclidean.mixedSpace K), hx⟩
    exact ⟨n, (inner_traceRadialScale K q hq v x).trans hn⟩
  · intro hv z
    have hz :
        (traceRadialScale K q hq).symm
            (z : mixedEmbedding.euclidean.mixedSpace K) ∈
          traceIdealLattice K I :=
      z.prop
    obtain ⟨n, hn⟩ := hv
      ⟨(traceRadialScale K q hq).symm
        (z : mixedEmbedding.euclidean.mixedSpace K), hz⟩
    refine ⟨n, ?_⟩
    rw [inner_traceRadialScale K q hq,
      ContinuousLinearEquiv.apply_symm_apply] at hn
    simp_all

open Classical in
theorem dualLattice_shapeIdealLattice
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0) :
    dualLattice (shapeIdealLattice K I q hq) =
      conjugateShapeIdealLattice K (traceDualIdealUnit K I)
        (fun w ↦ (q w)⁻¹) (fun w ↦ inv_ne_zero (hq w)) := by
  ext v
  rw [mem_dualLattice_shapeIdealLattice_iff,
    dualLattice_traceIdealLattice,
    mem_conjugateTraceIdealLattice_iff,
    mem_conjugateShapeIdealLattice_iff]
  change
    traceConjugation K (traceRadialScale K q hq v) ∈
        traceIdealLattice K (traceDualIdealUnit K I) ↔
      (traceRadialScale K (fun w ↦ (q w)⁻¹)
        (fun w ↦ inv_ne_zero (hq w))).symm (traceConjugation K v) ∈
        traceIdealLattice K (traceDualIdealUnit K I)
  rw [traceRadialScale_symm_apply,
    traceConjugation_traceRadialScale]
  simp

open Classical in
theorem traceRadialScale_traceEmbedding_mem_shapeIdealLattice
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0) (x : K) :
    traceRadialScale K q hq (traceEmbedding K x) ∈
        shapeIdealLattice K I q hq ↔
      x ∈ (I : FractionalIdeal (𝓞 K)⁰ K) := by
  change
    (traceRadialScale K q hq).symm
        (traceRadialScale K q hq (traceEmbedding K x)) ∈
          traceIdealLattice K I ↔ _
  rw [ContinuousLinearEquiv.symm_apply_apply,
    traceEmbedding_mem_traceIdealLattice]

variable [IsTotallyComplex K]

open Classical in
theorem norm_sq_traceRadialScale_traceEmbedding
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0) (x : K) :
    ‖traceRadialScale K q hq (traceEmbedding K x)‖ ^ 2 =
      2 * ∑ w : InfinitePlace K, (w x) ^ 2 * (q w) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  suffices
    ‖WithLp.toLp 2
        (WithLp.toLp 2
            ((fun w ↦ q w.1) * (mixedEmbedding K x).1),
          WithLp.toLp 2
            ((ContinuousLinearEquiv.piCongrRight
              (fun _ ↦ divideBySqrtTwo)).symm
                ((fun w ↦ (q w.1 : ℂ)) * (mixedEmbedding K x).2)))‖ ^ 2 =
      2 * ∑ w : InfinitePlace K, (w x) ^ 2 * (q w) ^ 2 by
    simpa [traceRadialScale, traceEmbedding, traceToMixed,
      unscaleComplexCoordinates, mixedEmbedding.euclidean.toMixed,
      mixedSpaceOfRealSpace_apply, radialMixedSpaceUnit,
      LinearEquiv.prodCongr_symm, LinearEquiv.prodCongr_apply,
      ContinuousLinearEquiv.prodCongr_symm, ContinuousLinearEquiv.prodCongr_apply,
      ContinuousLinearEquiv.piCongrRight_symm_apply]
  rw [WithLp.prod_norm_sq_eq_of_L2]
  rw [PiLp.norm_sq_eq_of_L2]
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [WithLp.toLp_fst, WithLp.toLp_snd, Pi.mul_apply,
    mixedEmbedding_apply_isReal, mixedEmbedding_apply_isComplex,
    ContinuousLinearEquiv.piCongrRight_symm_apply,
    divideBySqrtTwo_symm_apply]
  change
    (∑ w : {w : InfinitePlace K // IsReal w},
        |q w.1 * embedding_of_isReal w.2 x| ^ 2) +
      ∑ w : {w : InfinitePlace K // IsComplex w},
        ‖Real.sqrt 2 • ((q w.1 : ℂ) * w.1.embedding x)‖ ^ 2 =
      2 * ∑ w : InfinitePlace K, (w x) ^ 2 * (q w) ^ 2
  simp only [_root_.norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg 2), norm_mul,
    Complex.norm_real, abs_mul]
  have hreal :
      (∑ w : {w : InfinitePlace K // IsReal w},
        (|q w.1| * |embedding_of_isReal w.2 x|) ^ 2) = 0 := by
    apply Finset.sum_eq_zero
    intro w _
    exact False.elim
      (not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex w.1) w.2)
  rw [hreal, zero_add]
  rw [← Equiv.sum_comp
    (Equiv.subtypeUnivEquiv (fun w : InfinitePlace K ↦ IsTotallyComplex.isComplex w))]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  dsimp [Equiv.subtypeUnivEquiv]
  rw [InfinitePlace.norm_embedding_eq]
  grind

open Classical in
theorem complexPlaceGaussian_eq_latticeGaussian
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0) (x : K) :
    complexPlaceGaussian K x q =
      latticeGaussian Real.pi
        (traceRadialScale K q hq (traceEmbedding K x)) := by
  rw [complexPlaceGaussian, latticeGaussian]
  norm_cast
  rw [norm_sq_traceRadialScale_traceEmbedding]
  ring_nf

end NumberField.Odlyzko
