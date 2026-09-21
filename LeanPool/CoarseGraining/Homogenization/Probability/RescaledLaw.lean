/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Probability.IndependentSums.WeakOrlicz
import LeanPool.CoarseGraining.Homogenization.Probability.LocalObservable
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! # Rescaled Law -/

open scoped Pointwise

namespace Homogenization

/-!
Triadically rescaled coefficient laws and random scale parameters.

The Chapter 4 probability layer is mostly law-centric: coefficient fields are
sampled from a measure on `CoeffField d`.  This module adds the basic transport
API for passing from a law to its triadically rescaled law and records the
lightweight random-scale package used by later quenched-scale arguments.
-/

/-- Dilate a vector by the triadic factor `3^n`. -/
noncomputable def triadicDilateVec {d : ℕ} (n : ℕ) (x : Vec d) : Vec d :=
  fun i => (3 : ℝ) ^ n * x i

/-- The image of a set under triadic dilation by `3^n`. -/
noncomputable def triadicDilateSet {d : ℕ} (n : ℕ) (U : Set (Vec d)) : Set (Vec d) :=
  {x | ∃ y ∈ U, x = triadicDilateVec n y}

/-- The integer shift in the original variables corresponding to an integer
shift after triadic rescaling. -/
def triadicScaleIntShift {d : ℕ} (n : ℕ) (z : Fin d → ℤ) : Fin d → ℤ :=
  fun i => ((3 ^ n : ℕ) : ℤ) * z i

/-- Rescale a coefficient field by the triadic factor `3^n`.

The rescaled field is `x ↦ a(3^n x)`.  Thus integer translations of the
rescaled field correspond to translations of the original field by integer
vectors multiplied by `3^n`. -/
noncomputable def rescaleCoeffField {d : ℕ} (n : ℕ) (a : CoeffField d) : CoeffField d :=
  fun x => a (triadicDilateVec n x)

@[simp] theorem triadicDilateVec_zero {d : ℕ} (x : Vec d) :
    triadicDilateVec (d := d) 0 x = x := by
  funext i
  simp [triadicDilateVec]

@[simp] theorem triadicDilateVec_mem_triadicDilateSet {d : ℕ} (n : ℕ)
    {U : Set (Vec d)} {x : Vec d} (hx : x ∈ U) :
    triadicDilateVec n x ∈ triadicDilateSet n U :=
  ⟨x, hx, rfl⟩

/-- Triadic dilation sends bounded subsets of the ambient space to bounded subsets. -/
theorem isBounded_triadicDilateSet {d : ℕ} (n : ℕ) {U : Set (Vec d)}
    (hU : Bornology.IsBounded U) :
    Bornology.IsBounded (triadicDilateSet n U) := by
  have hcont : Continuous (triadicDilateVec (d := d) n) := by
    change Continuous fun x : Fin d → ℝ => fun i => (3 : ℝ) ^ n * x i
    exact continuous_pi fun i => continuous_const.mul (continuous_apply i)
  simpa [triadicDilateSet, Set.image, eq_comm] using
    isBounded_image_of_continuous_vec hcont hU

@[simp] theorem rescaleCoeffField_zero {d : ℕ} (a : CoeffField d) :
    rescaleCoeffField 0 a = a := by
  funext x i j
  simp [rescaleCoeffField]

theorem rescaleCoeffField_add {d : ℕ} (m n : ℕ) (a : CoeffField d) :
    rescaleCoeffField (m + n) a =
      rescaleCoeffField n (rescaleCoeffField m a) := by
  funext x i j
  have hvec :
      triadicDilateVec (m + n) x = triadicDilateVec m (triadicDilateVec n x) := by
    funext k
    simp [triadicDilateVec, pow_add]
    ring
  simp [rescaleCoeffField, hvec]

theorem localTestObservable_rescaleCoeffField_eq_const_mul
    {d : ℕ} (k : ℕ) (e e' : Vec d) (φ : Vec d → ℝ) (a : CoeffField d) :
    localTestObservable e e' φ (rescaleCoeffField k a) =
      (((3 : ℝ) ^ k) ^ d)⁻¹ *
        localTestObservable e e'
          (fun y : Vec d => φ (((3 : ℝ) ^ k)⁻¹ • y)) a := by
  let r : ℝ := (3 : ℝ) ^ k
  have hr : 0 < r := by positivity
  let f : Vec d → ℝ := fun y => vecDot e' (matVecMul (a y) e) * φ (r⁻¹ • y)
  have hcv :
      ∫ x in (Set.univ : Set (Vec d)), f (r • x) ∂MeasureTheory.volume =
        (r ^ d)⁻¹ • ∫ y in r • (Set.univ : Set (Vec d)), f y ∂MeasureTheory.volume := by
    simpa [Vec] using
      (MeasureTheory.Measure.setIntegral_comp_smul_of_pos
        (μ := MeasureTheory.volume) (f := f) (s := Set.univ) hr)
  have huniv : r • (Set.univ : Set (Vec d)) = Set.univ := by
    ext y
    constructor
    · intro _; trivial
    · intro _
      refine ⟨r⁻¹ • y, trivial, ?_⟩
      ext i
      simp [Pi.smul_apply, smul_eq_mul, hr.ne']
  have htriadic : ∀ x : Vec d, triadicDilateVec k x = r • x := by
    intro x
    ext i
    simp [triadicDilateVec, r, Pi.smul_apply, smul_eq_mul]
  unfold localTestObservable
  calc
    ∫ x, (vecDot e' (matVecMul (rescaleCoeffField k a x) e) * φ x) ∂MeasureTheory.volume
        = ∫ x, f (r • x) ∂MeasureTheory.volume := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with x
          have hrx : r⁻¹ • (r • x) = x := by
            ext i
            simp [Pi.smul_apply, smul_eq_mul, hr.ne']
          simp [f, rescaleCoeffField, htriadic x, hrx]
    _ = ∫ x in (Set.univ : Set (Vec d)), f (r • x) ∂MeasureTheory.volume := by
          simp
    _ = (r ^ d)⁻¹ • ∫ y in r • (Set.univ : Set (Vec d)), f y ∂MeasureTheory.volume :=
          hcv
    _ = (r ^ d)⁻¹ *
          ∫ y, (vecDot e' (matVecMul (a y) e) *
            φ (((3 : ℝ) ^ k)⁻¹ • y)) ∂MeasureTheory.volume := by
          simp [f, r, huniv]

theorem localFiniteTestObservable_rescaleCoeffField_eq {d : ℕ} {ι : Type}
    (n : ℕ) (I : Finset ι) (e e' : ι → Vec d) (φ : ι → Vec d → ℝ)
    (a : CoeffField d) :
    localFiniteTestObservable I e e' φ (rescaleCoeffField n a) =
      localFiniteTestObservable I e e'
        (fun k y => (((3 : ℝ) ^ n) ^ d)⁻¹ * φ k (((3 : ℝ) ^ n)⁻¹ • y)) a := by
  let r : ℝ := (3 : ℝ) ^ n
  have hr : 0 < r := by positivity
  let c : ℝ := (r ^ d)⁻¹
  let f : Vec d → ℝ := fun y =>
    ∑ k ∈ I, vecDot (e' k) (matVecMul (a y) (e k)) * φ k (r⁻¹ • y)
  have hcv :
      ∫ x in (Set.univ : Set (Vec d)), f (r • x) ∂MeasureTheory.volume =
        (r ^ d)⁻¹ • ∫ y in r • (Set.univ : Set (Vec d)), f y ∂MeasureTheory.volume := by
    simpa [Vec] using
      (MeasureTheory.Measure.setIntegral_comp_smul_of_pos
        (μ := MeasureTheory.volume) (f := f) (s := Set.univ) hr)
  have huniv : r • (Set.univ : Set (Vec d)) = Set.univ := by
    ext y
    constructor
    · intro _; trivial
    · intro _
      refine ⟨r⁻¹ • y, trivial, ?_⟩
      ext i
      simp [Pi.smul_apply, smul_eq_mul, hr.ne']
  have htriadic : ∀ x : Vec d, triadicDilateVec n x = r • x := by
    intro x
    ext i
    simp [triadicDilateVec, r, Pi.smul_apply, smul_eq_mul]
  unfold localFiniteTestObservable
  calc
    ∫ x, (∑ k ∈ I, vecDot (e' k) (matVecMul (rescaleCoeffField n a x) (e k)) *
        φ k x) ∂MeasureTheory.volume
        = ∫ x, f (r • x) ∂MeasureTheory.volume := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with x
          have hrx : r⁻¹ • (r • x) = x := by
            ext i
            simp [Pi.smul_apply, smul_eq_mul, hr.ne']
          simp [f, rescaleCoeffField, htriadic x, hrx]
    _ = ∫ x in (Set.univ : Set (Vec d)), f (r • x) ∂MeasureTheory.volume := by
          simp
    _ = (r ^ d)⁻¹ • ∫ y in r • (Set.univ : Set (Vec d)), f y ∂MeasureTheory.volume :=
          hcv
    _ = c * ∫ y, f y ∂MeasureTheory.volume := by
          simp [c, huniv]
    _ = ∫ y, c * f y ∂MeasureTheory.volume := by
          exact (MeasureTheory.integral_const_mul c f).symm
    _ = ∫ y, (∑ k ∈ I, vecDot (e' k) (matVecMul (a y) (e k)) *
        ((((3 : ℝ) ^ n) ^ d)⁻¹ * φ k (((3 : ℝ) ^ n)⁻¹ • y)))
        ∂MeasureTheory.volume := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with y
          simp [f, c, r, Finset.mul_sum]
          ring_nf

theorem measurable_rescaleCoeffField {d : ℕ} (n : ℕ) :
    Measurable (rescaleCoeffField (d := d) n) := by
  refine measurable_coeffField_to_ambient ?_ (fun V hV => ?_)
  · refine measurable_pi_iff.2 fun x => measurable_pi_iff.2 fun i =>
      measurable_pi_iff.2 fun j => ?_
    exact measurable_coeffField_entry (d := d) (triadicDilateVec n x) i j
  · refine measurable_localSigma_of_local (T := rescaleCoeffField n) ?_ V hV
    intro W hW
    refine ⟨triadicDilateSet n W, ?_, ?_⟩
    · exact isBounded_triadicDilateSet n hW
    intro a b hab x hxW
    simp [rescaleCoeffField, hab (triadicDilateVec n x)
      (triadicDilateVec_mem_triadicDilateSet n hxW)]

theorem translateByInt_rescaleCoeffField_eq_rescaleCoeffField_translateByInt
    {d : ℕ} (n : ℕ) (z : Fin d → ℤ) (a : CoeffField d) :
    translateByInt z (rescaleCoeffField n a) =
      rescaleCoeffField n (translateByInt (triadicScaleIntShift n z) a) := by
  funext x i j
  have hvec :
      triadicDilateVec n (x + intVecToRealVec z) =
        triadicDilateVec n x + intVecToRealVec (triadicScaleIntShift n z) := by
    funext k
    simp [triadicDilateVec, triadicScaleIntShift, intVecToRealVec]
    ring
  change a (triadicDilateVec n (x + intVecToRealVec z)) i j =
    a (triadicDilateVec n x + intVecToRealVec (triadicScaleIntShift n z)) i j
  rw [hvec]
