/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.CompletedZeta.RadialKernelFormula
public import LeanPool.Odlyzko.Theta.PoissonSummation
public import LeanPool.Odlyzko.Theta.TraceDualLattice
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

section

open Complex Module NumberField NumberField.InfinitePlace
open scoped nonZeroDivisors

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K]

open Classical in
/-- A trace to euclidean used in the Odlyzko-bound argument. -/
noncomputable def traceToEuclidean :
    mixedEmbedding.euclidean.mixedSpace K ≃L[ℝ]
      mixedEmbedding.euclidean.mixedSpace K :=
  (traceToMixed K).trans (mixedEmbedding.euclidean.toMixed K).symm

open Classical in
theorem traceIdealLattice_eq_comap_euclideanIdealLattice
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    traceIdealLattice K I =
      ZLattice.comap ℝ (euclideanIdealLattice K I)
        (traceToEuclidean K).toLinearMap := by
  rfl

open Classical in
private theorem divideBySqrtTwo_toLinearMap :
    (divideBySqrtTwo : ℂ ≃L[ℝ] ℂ).toLinearMap =
      (Real.sqrt 2)⁻¹ • LinearMap.id := by
  rfl

open Classical in
private theorem det_divideBySqrtTwo :
    LinearMap.det (divideBySqrtTwo : ℂ ≃L[ℝ] ℂ).toLinearMap = 2⁻¹ := by
  rw [divideBySqrtTwo_toLinearMap, LinearMap.det_smul]
  simp

omit [NumberField K] in
open Classical in
private theorem unscaleComplexCoordinates_toLinearMap :
    (unscaleComplexCoordinates K).toLinearMap =
      LinearMap.pi (fun w ↦
        (divideBySqrtTwo : ℂ ≃L[ℝ] ℂ).toLinearMap.comp
          (LinearMap.proj w)) := by
  apply LinearMap.ext
  intro z
  funext w
  simp [unscaleComplexCoordinates]

open Classical in
private theorem det_unscaleComplexCoordinates :
    LinearMap.det (unscaleComplexCoordinates K).toLinearMap =
      (2⁻¹) ^ nrComplexPlaces K := by
  rw [unscaleComplexCoordinates_toLinearMap, LinearMap.det_pi]
  simp [det_divideBySqrtTwo]

open Classical in
private theorem det_traceToEuclidean :
    LinearMap.det (traceToEuclidean K).toLinearMap =
      (2⁻¹) ^ nrComplexPlaces K := by
  let u :=
    (ContinuousLinearEquiv.refl ℝ
      ({w : InfinitePlace K // IsReal w} → ℝ)).prodCongr
        (unscaleComplexCoordinates K)
  have hmap :
      (traceToEuclidean K).toLinearMap =
        (mixedEmbedding.euclidean.toMixed K).symm.toLinearMap.comp
          (u.toLinearMap.comp
            (mixedEmbedding.euclidean.toMixed K).toLinearMap) := by
    rfl
  rw [hmap]
  rw [show LinearMap.det
      ((mixedEmbedding.euclidean.toMixed K).symm.toLinearMap.comp
        (u.toLinearMap.comp
          (mixedEmbedding.euclidean.toMixed K).toLinearMap)) =
      LinearMap.det u.toLinearMap by
        exact LinearMap.det_conj u.toLinearMap
          (mixedEmbedding.euclidean.toMixed K).symm.toLinearEquiv]
  change LinearMap.det
      (LinearMap.prodMap
        (LinearMap.id (R := ℝ)
          (M := {w : InfinitePlace K // IsReal w} → ℝ))
        (unscaleComplexCoordinates K).toLinearMap) = _
  rw [LinearMap.det_prodMap, LinearMap.det_id, one_mul,
    det_unscaleComplexCoordinates]

open Classical in
theorem covolume_comap_continuousLinearEquiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (μ : MeasureTheory.Measure E) [MeasureTheory.Measure.IsAddHaarMeasure μ]
    (e : E ≃L[ℝ] E) :
    ZLattice.covolume
        (ZLattice.comap ℝ L e.toLinearMap) μ =
      |LinearMap.det e.toLinearMap|⁻¹ *
        ZLattice.covolume L μ := by
  let b := Free.chooseBasis ℤ L
  have hfund :
      ZSpan.fundamentalDomain
          ((b.ofZLatticeComap ℝ L e.toLinearEquiv).ofZLatticeBasis
            ℝ (ZLattice.comap ℝ L e.toLinearMap)) =
        e ⁻¹'
          ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ L) := by
    rw [← e.image_symm_eq_preimage, ← e.symm.coe_toLinearEquiv,
      ZSpan.map_fundamentalDomain]
    congr 1
    ext
    simp
  have hmeasure :
      μ (e ⁻¹' ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ L)) =
        ENNReal.ofReal |(LinearMap.det e.toLinearMap)⁻¹| *
          μ (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ L)) := by
    exact MeasureTheory.Measure.addHaar_preimage_linearMap
      μ (LinearEquiv.isUnit_det' e.toLinearEquiv).ne_zero _
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _
      μ
      (ZLattice.isAddFundamentalDomain
        (b.ofZLatticeComap ℝ L e.toLinearEquiv)
        μ),
    ZLattice.covolume_eq_measure_fundamentalDomain L
      μ (ZLattice.isAddFundamentalDomain b μ),
    hfund, MeasureTheory.measureReal_def,
    MeasureTheory.measureReal_def,
    hmeasure,
    ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (abs_nonneg _)]
  simp

open Classical in
theorem covolume_traceIdealLattice
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ZLattice.covolume (traceIdealLattice K I) =
      FractionalIdeal.absNorm
          (I : FractionalIdeal (𝓞 K)⁰ K) *
        √|discr K| := by
  rw [traceIdealLattice_eq_comap_euclideanIdealLattice K I,
    covolume_comap_continuousLinearEquiv
      (euclideanIdealLattice K I) MeasureTheory.volume
      (traceToEuclidean K),
    det_traceToEuclidean,
    covolume_euclideanIdealLattice]
  have hpos : 0 < (2⁻¹ : ℝ) ^ nrComplexPlaces K := by positivity
  grind

end NumberField.Odlyzko

end

section

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

end

section

open Complex NumberField NumberField.InfinitePlace
open scoped nonZeroDivisors

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K]

open Classical in
/-- An ideal element shape map used in the Odlyzko-bound argument. -/
noncomputable def idealElementShapeMap
    (J : (Ideal (𝓞 K))⁰)
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0)
    (x : ↥(J : Ideal (𝓞 K))) :
    shapeIdealLattice K (FractionalIdeal.mk0 K J) q hq :=
  ⟨traceRadialScale K q hq
      (traceEmbedding K (((x : 𝓞 K) : K))),
      (traceRadialScale_traceEmbedding_mem_shapeIdealLattice
        K (FractionalIdeal.mk0 K J) q hq _).2 (by
          rw [FractionalIdeal.coe_mk0, FractionalIdeal.mem_coeIdeal]
          exact ⟨x, x.prop, rfl⟩)⟩

open Classical in
theorem idealElementShapeMap_bijective
    (J : (Ideal (𝓞 K))⁰)
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0) :
    Function.Bijective (idealElementShapeMap K J q hq) := by
  constructor
  · intro x y hxy
    have htrace :
        traceEmbedding K (((x : 𝓞 K) : K)) =
          traceEmbedding K (((y : 𝓞 K) : K)) :=
      (traceRadialScale K q hq).injective (congrArg Subtype.val hxy)
    apply Subtype.ext
    apply RingOfIntegers.coe_injective
    apply mixedEmbedding_injective K
    simpa [traceEmbedding] using congrArg (traceToMixed K) htrace
  · intro v
    have hv :
        (traceRadialScale K q hq).symm (v : mixedEmbedding.euclidean.mixedSpace K) ∈
          traceIdealLattice K (FractionalIdeal.mk0 K J) :=
      v.prop
    obtain ⟨x, hx, hxv⟩ :=
      exists_traceEmbedding_eq_of_mem_traceIdealLattice
        K (FractionalIdeal.mk0 K J) hv
    rw [FractionalIdeal.coe_mk0, FractionalIdeal.mem_coeIdeal] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    refine ⟨⟨y, hy⟩, Subtype.ext ?_⟩
    change traceRadialScale K q hq (traceEmbedding K ((y : 𝓞 K) : K)) = v
    simp_all

open Classical in
/-- An ideal element shape equiv used in the Odlyzko-bound argument. -/
noncomputable def idealElementShapeEquiv
    (J : (Ideal (𝓞 K))⁰)
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0) :
    ↥(J : Ideal (𝓞 K)) ≃
      shapeIdealLattice K (FractionalIdeal.mk0 K J) q hq :=
  Equiv.ofBijective (idealElementShapeMap K J q hq)
    (idealElementShapeMap_bijective K J q hq)

open Classical in
@[simp]
theorem idealElementShapeEquiv_coe
    (J : (Ideal (𝓞 K))⁰)
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0)
    (x : ↥(J : Ideal (𝓞 K))) :
    ((idealElementShapeEquiv K J q hq x :
        shapeIdealLattice K (FractionalIdeal.mk0 K J) q hq) :
      mixedEmbedding.euclidean.mixedSpace K) =
      traceRadialScale K q hq
        (traceEmbedding K (((x : 𝓞 K) : K))) :=
  by rfl

variable [IsTotallyComplex K]

open Classical in
/-- A shape ideal theta used in the Odlyzko-bound argument. -/
noncomputable def shapeIdealTheta
    (J : (Ideal (𝓞 K))⁰)
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0) : ℂ :=
  latticeTheta
    (shapeIdealLattice K (FractionalIdeal.mk0 K J) q hq) Real.pi

open Classical in
theorem shapeIdealTheta_eq_tsum
    (J : (Ideal (𝓞 K))⁰)
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0) :
    shapeIdealTheta K J q hq =
      ∑' x : ↥(J : Ideal (𝓞 K)),
        complexPlaceGaussian K (((x : 𝓞 K) : K)) q := by
  rw [shapeIdealTheta, latticeTheta,
    ← (idealElementShapeEquiv K J q hq).tsum_eq]
  apply tsum_congr
  intro x
  rw [idealElementShapeEquiv_coe,
    ← complexPlaceGaussian_eq_latticeGaussian]

omit [IsTotallyComplex K] in
open Classical in
theorem dualLatticeTheta_shapeIdealLattice
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0) :
    dualLatticeTheta (shapeIdealLattice K I q hq) Real.pi =
      latticeTheta
        (shapeIdealLattice K (traceDualIdealUnit K I)
          (fun w ↦ (q w)⁻¹) (fun w ↦ inv_ne_zero (hq w))) Real.pi := by
  rw [dualLatticeTheta, dualLattice_shapeIdealLattice,
    conjugateShapeIdealLattice]
  exact latticeTheta_map_linearIsometryEquiv
    (shapeIdealLattice K (traceDualIdealUnit K I)
      (fun w ↦ (q w)⁻¹) (fun w ↦ inv_ne_zero (hq w)))
    (traceConjugation K) Real.pi

open Classical in
/-- A nonzero ideal element equiv singleton compl used in the Odlyzko-bound argument. -/
def nonzeroIdealElementEquivSingletonCompl
    (J : (Ideal (𝓞 K))⁰) :
    nonzeroIdealElement K J ≃
      {x : ↥(J : Ideal (𝓞 K)) // x ∉ ({0} : Finset ↥(J : Ideal (𝓞 K)))} where
  toFun x :=
    ⟨⟨x.1, x.2.1⟩, by
      simp only [Finset.mem_singleton]
      intro hx
      exact x.2.2 (congrArg Subtype.val hx)⟩
  invFun x :=
    ⟨x.1.1, x.1.2, by
      intro hx
      apply x.2
      simp_all⟩
  left_inv x := by
    simp
  right_inv x := by
    apply Subtype.ext
    simp

open Classical in
theorem shapeIdealTheta_eq_one_add_nonzero
    (J : (Ideal (𝓞 K))⁰)
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0) :
    shapeIdealTheta K J q hq =
      1 + ∑' x : nonzeroIdealElement K J,
        complexPlaceGaussian K (((x : 𝓞 K) : K)) q := by
  let f : ↥(J : Ideal (𝓞 K)) → ℂ :=
    fun x ↦ complexPlaceGaussian K (((x : 𝓞 K) : K)) q
  have hsL :
      Summable (fun v :
          shapeIdealLattice K (FractionalIdeal.mk0 K J) q hq ↦
        latticeGaussian Real.pi
          (v : mixedEmbedding.euclidean.mixedSpace K)) :=
    summable_latticeTheta
      (shapeIdealLattice K (FractionalIdeal.mk0 K J) q hq) Real.pi_pos
  have hs : Summable f := by
    have h := (Equiv.summable_iff
      (idealElementShapeEquiv K J q hq)).mpr hsL
    exact h.congr fun x ↦ by
      dsimp only [Function.comp_apply, f]
      rw [idealElementShapeEquiv_coe,
        ← complexPlaceGaussian_eq_latticeGaussian]
  rw [shapeIdealTheta_eq_tsum]
  change (∑' x, f x) = _
  rw [← hs.sum_add_tsum_subtype_compl ({0} : Finset ↥(J : Ideal (𝓞 K)))]
  simp only [Finset.sum_singleton, f, complexPlaceGaussian]
  have hzero :
      Complex.exp
        (-((2 * Real.pi *
          ∑ w : InfinitePlace K,
            (w (((0 : ↥(J : Ideal (𝓞 K))) : 𝓞 K) : K)) ^ 2 *
              (q w) ^ 2 : ℝ) : ℂ)) = 1 := by
    simp
  rw [hzero]
  rw [← (nonzeroIdealElementEquivSingletonCompl K J).tsum_eq]
  rfl

open Classical in
theorem nonzeroIdealShapeTheta_eq_shapeIdealTheta_sub_one
    (J : (Ideal (𝓞 K))⁰) (y : mixedEmbedding.realSpace K) :
    nonzeroIdealShapeTheta K J y =
      shapeIdealTheta K J (mixedEmbedding.fundamentalCone.expMapBasis y)
        (fun w ↦ (mixedEmbedding.fundamentalCone.expMapBasis_pos y w).ne') - 1 := by
  rw [shapeIdealTheta_eq_one_add_nonzero, nonzeroIdealShapeTheta]
  ring

end NumberField.Odlyzko

end

section

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

end

section

open Complex NumberField NumberField.InfinitePlace
open scoped nonZeroDivisors

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K]

open Classical in
/-- A fractional ideal element shape map used in the Odlyzko-bound argument. -/
noncomputable def fractionalIdealElementShapeMap
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0)
    (x : ↥((I : FractionalIdeal (𝓞 K)⁰ K) :
      Submodule (𝓞 K) K)) :
    shapeIdealLattice K I q hq :=
  ⟨traceRadialScale K q hq (traceEmbedding K (x : K)),
    (traceRadialScale_traceEmbedding_mem_shapeIdealLattice
      K I q hq _).2 x.prop⟩

open Classical in
theorem fractionalIdealElementShapeMap_bijective
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0) :
    Function.Bijective (fractionalIdealElementShapeMap K I q hq) := by
  constructor
  · intro x y hxy
    have htrace :
        traceEmbedding K (x : K) = traceEmbedding K (y : K) :=
      (traceRadialScale K q hq).injective (congrArg Subtype.val hxy)
    apply Subtype.ext
    apply mixedEmbedding_injective K
    simpa [traceEmbedding] using congrArg (traceToMixed K) htrace
  · intro v
    have hv :
        (traceRadialScale K q hq).symm
            (v : mixedEmbedding.euclidean.mixedSpace K) ∈
          traceIdealLattice K I :=
      v.prop
    obtain ⟨x, hx, hxv⟩ :=
      exists_traceEmbedding_eq_of_mem_traceIdealLattice K I hv
    refine ⟨⟨x, hx⟩, Subtype.ext ?_⟩
    change traceRadialScale K q hq (traceEmbedding K x) = v
    simp_all

open Classical in
/-- A fractional ideal element shape equiv used in the Odlyzko-bound argument. -/
noncomputable def fractionalIdealElementShapeEquiv
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0) :
    ↥((I : FractionalIdeal (𝓞 K)⁰ K) :
      Submodule (𝓞 K) K) ≃ shapeIdealLattice K I q hq :=
  Equiv.ofBijective (fractionalIdealElementShapeMap K I q hq)
    (fractionalIdealElementShapeMap_bijective K I q hq)

open Classical in
@[simp]
theorem fractionalIdealElementShapeEquiv_coe
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0)
    (x : ↥((I : FractionalIdeal (𝓞 K)⁰ K) :
      Submodule (𝓞 K) K)) :
    ((fractionalIdealElementShapeEquiv K I q hq x :
        shapeIdealLattice K I q hq) :
      mixedEmbedding.euclidean.mixedSpace K) =
      traceRadialScale K q hq (traceEmbedding K (x : K)) :=
  rfl

variable [IsTotallyComplex K]

open Classical in
/-- A fractional shape ideal theta used in the Odlyzko-bound argument. -/
noncomputable def fractionalShapeIdealTheta
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0) : ℂ :=
  latticeTheta (shapeIdealLattice K I q hq) Real.pi

open Classical in
theorem fractionalShapeIdealTheta_eq_tsum
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0) :
    fractionalShapeIdealTheta K I q hq =
      ∑' x : ↥((I : FractionalIdeal (𝓞 K)⁰ K) :
        Submodule (𝓞 K) K),
        complexPlaceGaussian K (x : K) q := by
  rw [fractionalShapeIdealTheta, latticeTheta,
    ← (fractionalIdealElementShapeEquiv K I q hq).tsum_eq]
  apply tsum_congr
  intro x
  rw [fractionalIdealElementShapeEquiv_coe,
    ← complexPlaceGaussian_eq_latticeGaussian]

omit [IsTotallyComplex K] in
open Classical in
theorem fractionalShapeIdealTheta_poissonSummation
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0) :
    fractionalShapeIdealTheta K I q hq =
      (Real.toNNReal
        (ZLattice.covolume (shapeIdealLattice K I q hq)))⁻¹ •
        fractionalShapeIdealTheta K (traceDualIdealUnit K I)
          (fun w ↦ (q w)⁻¹) (fun w ↦ inv_ne_zero (hq w)) := by
  rw [fractionalShapeIdealTheta,
    latticeGaussian_poissonSummation
      (shapeIdealLattice K I q hq) Real.pi_pos]
  have hpi : ((Real.pi : ℂ) / Real.pi) = 1 := by simp
  have hparam : Real.pi ^ 2 / Real.pi = Real.pi := by grind
  rw [hpi, one_cpow, one_mul, hparam,
    dualLatticeTheta_shapeIdealLattice]
  rfl

open Classical in
/-- A fractional ideal numerator used in the Odlyzko-bound argument. -/
noncomputable def fractionalIdealNumerator
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : (Ideal (𝓞 K))⁰ :=
  ⟨(I : FractionalIdeal (𝓞 K)⁰ K).num,
    mem_nonZeroDivisors_iff_ne_zero.mpr fun hnum ↦
      Units.ne_zero I
        (FractionalIdeal.num_eq_zero_iff.mp hnum)⟩

omit [IsTotallyComplex K] in
open Classical in
theorem mk0_fractionalIdealNumerator
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ClassGroup.mk0 (fractionalIdealNumerator K I) =
      ClassGroup.mk K I := by
  rw [← ClassGroup.mk_mk0 K]
  rw [← ClassGroup.mk_canonicalEquiv K (FractionRing (𝓞 K)) I]
  rw [← ClassGroup.mk_canonicalEquiv K (FractionRing (𝓞 K))
    (FractionalIdeal.mk0 K (fractionalIdealNumerator K I))]
  rw [FractionalIdeal.map_canonicalEquiv_mk0]
  symm
  apply ClassGroup.mk_eq_mk.mpr
  let d : (FractionRing (𝓞 K))ˣ := Units.mk0
    (algebraMap (𝓞 K) (FractionRing (𝓞 K))
      ((I : FractionalIdeal (𝓞 K)⁰ K).den : 𝓞 K))
    (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      (I : FractionalIdeal (𝓞 K)⁰ K).den.prop)
  refine ⟨d, ?_⟩
  apply Units.ext
  rw [Units.val_mul, coe_toPrincipalIdeal]
  simp only [d, Units.val_mk0]
  have h := congrArg
    (FractionalIdeal.canonicalEquiv (𝓞 K)⁰ K
      (FractionRing (𝓞 K)))
    (FractionalIdeal.den_mul_self_eq_num' (𝓞 K)⁰ K
      (I : FractionalIdeal (𝓞 K)⁰ K))
  rw [map_mul, FractionalIdeal.canonicalEquiv_spanSingleton] at h
  let m : K →+* FractionRing (𝓞 K) :=
    IsLocalization.map (M := (𝓞 K)⁰) (T := (𝓞 K)⁰)
      (FractionRing (𝓞 K)) (RingHom.id (𝓞 K))
      (by intro x hx; simpa using hx)
  have hm (r : 𝓞 K) :
      m (algebraMap (𝓞 K) K r) =
        algebraMap (𝓞 K) (FractionRing (𝓞 K)) r := by
    exact IsLocalization.map_eq (M := (𝓞 K)⁰) _ _
  change FractionalIdeal.spanSingleton (𝓞 K)⁰
      (m (algebraMap (𝓞 K) K
        ((I : FractionalIdeal (𝓞 K)⁰ K).den : 𝓞 K))) *
      (FractionalIdeal.canonicalEquiv (𝓞 K)⁰ K
        (FractionRing (𝓞 K))) (I : FractionalIdeal (𝓞 K)⁰ K) =
      (FractionalIdeal.canonicalEquiv (𝓞 K)⁰ K
        (FractionRing (𝓞 K)))
          ((I : FractionalIdeal (𝓞 K)⁰ K).num :
            FractionalIdeal (𝓞 K)⁰ K) at h
  rw [hm, FractionalIdeal.canonicalEquiv_coeIdeal] at h
  change
    (FractionalIdeal.canonicalEquiv (𝓞 K)⁰ K
        (FractionRing (𝓞 K)))
        (I : FractionalIdeal (𝓞 K)⁰ K) *
      FractionalIdeal.spanSingleton (𝓞 K)⁰
        (algebraMap (𝓞 K) (FractionRing (𝓞 K))
          ((I : FractionalIdeal (𝓞 K)⁰ K).den : 𝓞 K)) =
      ((I : FractionalIdeal (𝓞 K)⁰ K).num :
        FractionalIdeal (𝓞 K)⁰ (FractionRing (𝓞 K)))
  grind

omit [IsTotallyComplex K] in
open Classical in
theorem fractionalIdeal_den_ne_zero
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (((I : FractionalIdeal (𝓞 K)⁰ K).den : 𝓞 K)) ≠ 0 :=
  mem_nonZeroDivisors_iff_ne_zero.mp
    (I : FractionalIdeal (𝓞 K)⁰ K).den.prop

open Classical in
/-- A numerator radii used in the Odlyzko-bound argument. -/
noncomputable def numeratorRadii
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (q : InfinitePlace K → ℝ) : InfinitePlace K → ℝ :=
  fun w ↦ q w /
    w (algebraMap (𝓞 K) K
      ((I : FractionalIdeal (𝓞 K)⁰ K).den : 𝓞 K))

omit [IsTotallyComplex K] in
open Classical in
theorem numeratorRadii_ne_zero
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0) :
    ∀ w, numeratorRadii K I q w ≠ 0 := by
  intro w
  apply div_ne_zero (hq w)
  simp

omit [IsTotallyComplex K] in
open Classical in
theorem complexPlaceGaussian_equivNum
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (q : InfinitePlace K → ℝ)
    (x : ↥((I : FractionalIdeal (𝓞 K)⁰ K) :
      Submodule (𝓞 K) K)) :
    complexPlaceGaussian K (x : K) q =
      complexPlaceGaussian K
        (((FractionalIdeal.equivNum
          (fractionalIdeal_den_ne_zero K I) x :
            (I : FractionalIdeal (𝓞 K)⁰ K).num) : 𝓞 K) : K)
        (numeratorRadii K I q) := by
  rw [complexPlaceGaussian, complexPlaceGaussian]
  congr 1
  push_cast
  congr 2
  apply Finset.sum_congr rfl
  intro w _
  have heq :
      ((((FractionalIdeal.equivNum
        (fractionalIdeal_den_ne_zero K I) x :
          (I : FractionalIdeal (𝓞 K)⁰ K).num) : 𝓞 K) : K)) =
        algebraMap (𝓞 K) K
          ((I : FractionalIdeal (𝓞 K)⁰ K).den : 𝓞 K) * (x : K) := by
    calc
      _ = (I : FractionalIdeal (𝓞 K)⁰ K).den • (x : K) :=
        FractionalIdeal.equivNum_apply
          (fractionalIdeal_den_ne_zero K I) x
      _ = _ := rfl
  rw [heq]
  norm_cast
  change
    w (x : K) ^ 2 * q w ^ 2 =
      w ((algebraMap (𝓞 K) K
        ((I : FractionalIdeal (𝓞 K)⁰ K).den : 𝓞 K)) * (x : K)) ^ 2 *
        (q w /
          w (algebraMap (𝓞 K) K
            ((I : FractionalIdeal (𝓞 K)⁰ K).den : 𝓞 K))) ^ 2
  rw [map_mul]
  have hd :
      w (algebraMap (𝓞 K) K
        ((I : FractionalIdeal (𝓞 K)⁰ K).den : 𝓞 K)) ≠ 0 := by
    simp
  grind

open Classical in
theorem fractionalShapeIdealTheta_eq_numerator
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0) :
    fractionalShapeIdealTheta K I q hq =
      shapeIdealTheta K (fractionalIdealNumerator K I)
        (numeratorRadii K I q) (numeratorRadii_ne_zero K I q hq) := by
  rw [fractionalShapeIdealTheta_eq_tsum,
    shapeIdealTheta_eq_tsum]
  change
    (∑' x : ↥((I : FractionalIdeal (𝓞 K)⁰ K) :
        Submodule (𝓞 K) K),
      complexPlaceGaussian K (x : K) q) =
      ∑' x : (I : FractionalIdeal (𝓞 K)⁰ K).num,
        complexPlaceGaussian K (((x : 𝓞 K) : K))
          (numeratorRadii K I q)
  rw [← (FractionalIdeal.equivNum
    (fractionalIdeal_den_ne_zero K I)).toEquiv.tsum_eq]
  apply tsum_congr
  intro x
  exact complexPlaceGaussian_equivNum K I q x

open Classical in
/-- A denominator log coordinates used in the Odlyzko-bound argument. -/
noncomputable def denominatorLogCoordinates
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    mixedEmbedding.realSpace K :=
  mixedEmbedding.fundamentalCone.expMapBasis.symm
    (fun w ↦ w (algebraMap (𝓞 K) K
      ((I : FractionalIdeal (𝓞 K)⁰ K).den : 𝓞 K)))

omit [IsTotallyComplex K] in
open Classical in
theorem expMapBasis_denominatorLogCoordinates
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
      mixedEmbedding.fundamentalCone.expMapBasis
        (denominatorLogCoordinates K I) =
      fun w ↦ w (algebraMap (𝓞 K) K
        ((I : FractionalIdeal (𝓞 K)⁰ K).den : 𝓞 K)) := by
  apply mixedEmbedding.fundamentalCone.expMapBasis.right_inv
  exact Set.mem_univ_pi.mpr fun w ↦
    InfinitePlace.pos_iff.mpr
      ((FaithfulSMul.algebraMap_injective (𝓞 K) K).ne
        (fractionalIdeal_den_ne_zero K I))

omit [IsTotallyComplex K] in
open Classical in
theorem expMapBasis_add
    (x y : mixedEmbedding.realSpace K) :
    mixedEmbedding.fundamentalCone.expMapBasis (x + y) =
      mixedEmbedding.fundamentalCone.expMapBasis x *
        mixedEmbedding.fundamentalCone.expMapBasis y := by
  rw [mixedEmbedding.fundamentalCone.expMapBasis_apply,
    mixedEmbedding.fundamentalCone.expMapBasis_apply,
    mixedEmbedding.fundamentalCone.expMapBasis_apply]
  rw [map_add]
  exact mixedEmbedding.fundamentalCone.expMap_add _ _

open Classical in
theorem numeratorRadii_expMapBasis
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (y : mixedEmbedding.realSpace K) :
    numeratorRadii K I
        (mixedEmbedding.fundamentalCone.expMapBasis y) =
      mixedEmbedding.fundamentalCone.expMapBasis
        (y - denominatorLogCoordinates K I) := by
  rw [sub_eq_add_neg, expMapBasis_add]
  funext w
  rw [Pi.mul_apply, expMapBasis_neg,
    expMapBasis_denominatorLogCoordinates]
  rfl

open Classical in
theorem fractionalShapeIdealTheta_expMapBasis_eq_numerator
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (y : mixedEmbedding.realSpace K) :
    fractionalShapeIdealTheta K I
        (mixedEmbedding.fundamentalCone.expMapBasis y)
        (fun w ↦ (mixedEmbedding.fundamentalCone.expMapBasis_pos y w).ne') =
      shapeIdealTheta K (fractionalIdealNumerator K I)
        (mixedEmbedding.fundamentalCone.expMapBasis
          (y - denominatorLogCoordinates K I))
        (fun w ↦
          (mixedEmbedding.fundamentalCone.expMapBasis_pos
            (y - denominatorLogCoordinates K I) w).ne') := by
  rw [fractionalShapeIdealTheta_eq_numerator,
    shapeIdealTheta_eq_tsum, shapeIdealTheta_eq_tsum]
  have hq :
      numeratorRadii K I
          (mixedEmbedding.fundamentalCone.expMapBasis y) =
        mixedEmbedding.fundamentalCone.expMapBasis
          (y - denominatorLogCoordinates K I) :=
    numeratorRadii_expMapBasis K I y
  simp_all

end NumberField.Odlyzko

end
