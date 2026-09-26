/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Probability.Source.Coarse.Laws
public import LeanPool.CoarseGraining.Homogenization.Probability.RescaledLaw

/-!
# Triadic scaling of the exact coarse source carrier

This module keeps the source-side rescaling kernel independent of the regular
carrier.  The normalized action is the pullback `a ↦ (x ↦ a (3^k x))`; hence a
local observable on `U` pulls back to information on `3^k U`.
-/

@[expose] public section

namespace Homogenization.Source.Coarse

open MeasureTheory
open scoped Pointwise

theorem euclideanNorm_triadicDilateVec {d : ℕ} (k : ℕ) (x : Vec d) :
    euclideanNorm (triadicDilateVec k x) = (3 : ℝ) ^ k * euclideanNorm x := by
  have hk : 0 ≤ (3 : ℝ) ^ k := by positivity
  change euclideanNorm ((3 : ℝ) ^ k • x) = (3 : ℝ) ^ k * euclideanNorm x
  rw [Homogenization.euclideanNorm_smul, abs_of_nonneg hk]

/-- Precomposition by a positive scalar is an exact coarse-source carrier
endomorphism. -/
noncomputable def Carrier.smul {d : ℕ} (r : ℝ) (hr : 0 < r) (a : Carrier d) :
    Carrier d where
  val := fun x => a (r • x)
  property := by
    constructor
    · intro i j
      exact (a.2.1 i j).comp (measurable_id.const_smul r)
    · intro R hR
      let S : ℝ := max 1 (r * R)
      have hS : 1 ≤ S := le_max_left _ _
      obtain ⟨ε, hε, hεone, hEll⟩ := a.2.2 S hS
      refine ⟨ε, hε, hεone, ?_⟩
      intro x hx
      apply hEll (r • x)
      change euclideanNorm (r • x) < S
      rw [Homogenization.euclideanNorm_smul, abs_of_pos hr]
      apply lt_of_lt_of_le (mul_lt_mul_of_pos_left hx hr)
      exact le_max_right _ _

@[simp] theorem Carrier.smul_apply {d : ℕ} (r : ℝ) (hr : 0 < r)
    (a : Carrier d) (x : Vec d) :
    Carrier.smul r hr a x = a (r • x) :=
  rfl

/-- Exact-source triadic rescaling, with normalized coordinates `x ↦ 3^k x`. -/
noncomputable def Carrier.rescale {d : ℕ} (k : ℕ) : Carrier d → Carrier d :=
  Carrier.smul ((3 : ℝ) ^ k) (by positivity)

@[simp] theorem Carrier.rescale_apply {d : ℕ} (k : ℕ) (a : Carrier d) (x : Vec d) :
    Carrier.rescale k a x = a (triadicDilateVec k x) := by
  change a (((3 : ℝ) ^ k) • x) = a (triadicDilateVec k x)
  congr 1

/-- The positive-scale inverse of source triadic rescaling. -/
noncomputable def Carrier.dilateNat {d : ℕ} (k : ℕ) : Carrier d → Carrier d :=
  Carrier.smul (((3 : ℝ) ^ k)⁻¹) (inv_pos.mpr (by positivity))

@[simp] theorem Carrier.dilateNat_apply {d : ℕ} (k : ℕ) (a : Carrier d) (x : Vec d) :
    Carrier.dilateNat k a x = a (((3 : ℝ) ^ k)⁻¹ • x) :=
  rfl

private theorem Carrier.smul_dilateNat_rescale {d : ℕ} (k : ℕ) (a : Carrier d) :
    Carrier.dilateNat k (Carrier.rescale k a) = a := by
  apply Subtype.ext
  funext x i j
  have hk : ((3 : ℝ) ^ k) ≠ 0 := by positivity
  simp only [Carrier.dilateNat, Carrier.rescale, Carrier.smul_apply]
  rw [smul_smul, mul_inv_cancel₀ hk, one_smul]

private theorem Carrier.smul_rescale_dilateNat {d : ℕ} (k : ℕ) (a : Carrier d) :
    Carrier.rescale k (Carrier.dilateNat k a) = a := by
  apply Subtype.ext
  funext x i j
  have hk : ((3 : ℝ) ^ k) ≠ 0 := by positivity
  simp only [Carrier.dilateNat, Carrier.rescale, Carrier.smul_apply]
  rw [smul_smul, inv_mul_cancel₀ hk, one_smul]

private theorem smoothCompactProbe_inv_smul {d : ℕ} {r : ℝ} (hr : 0 < r)
    {φ : Vec d → ℝ} (hφ : SmoothCompactProbe φ) :
    SmoothCompactProbe (fun y => φ (r⁻¹ • y)) := by
  constructor
  · simpa [Function.comp_def] using
      hφ.smooth.comp (contDiff_const_smul r⁻¹)
  · show HasCompactSupport (φ ∘ Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr.ne'))
    simpa [Function.comp_def] using
      hφ.compact.comp_homeomorph (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr.ne'))

private theorem tsupport_inv_smul_subset_smul {d : ℕ} {r : ℝ} (hr : 0 < r)
    {U : Set (Vec d)} {φ : Vec d → ℝ} (hφU : tsupport φ ⊆ U) :
    tsupport (fun y => φ (r⁻¹ • y)) ⊆ r • U := by
  intro y hy
  have hy' : r⁻¹ • y ∈ tsupport φ := by
    rw [show (fun y : Vec d => φ (r⁻¹ • y)) =
        φ ∘ Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr.ne') by rfl,
      tsupport_comp_eq_preimage φ (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr.ne'))] at hy
    exact hy
  refine ⟨r⁻¹ • y, hφU hy', ?_⟩
  change r • (r⁻¹ • y) = y
  rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]

private theorem bilinearTest_smul {d : ℕ} (r : ℝ) (hr : 0 < r)
    (e e' : Vec d) (φ : Vec d → ℝ) (a : Carrier d) :
    bilinearTest e e' φ (Carrier.smul r hr a) =
      (r ^ d)⁻¹ * bilinearTest e e' (fun y => φ (r⁻¹ • y)) a := by
  let f : Vec d → ℝ := fun y =>
    vecDot e' (matVecMul (a y) e) * φ (r⁻¹ • y)
  have hcv :
      ∫ x in (Set.univ : Set (Vec d)), f (r • x) ∂volume =
        (r ^ d)⁻¹ • ∫ y in r • (Set.univ : Set (Vec d)), f y ∂volume := by
    simpa [Vec] using
      (MeasureTheory.Measure.setIntegral_comp_smul_of_pos
        (μ := volume) (f := f) (s := Set.univ) hr)
  have huniv : r • (Set.univ : Set (Vec d)) = Set.univ := by
    ext y
    constructor
    · intro _
      trivial
    · intro _
      refine ⟨r⁻¹ • y, trivial, ?_⟩
      change r • (r⁻¹ • y) = y
      rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  unfold bilinearTest
  calc
    ∫ x, (vecDot e' (matVecMul (Carrier.smul r hr a x) e) * φ x) ∂volume =
        ∫ x, f (r • x) ∂volume := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with x
          rw [Carrier.smul_apply]
          have hback : r⁻¹ • (r • x) = x := by
            rw [smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
          simp only [f, hback]
    _ = ∫ x in (Set.univ : Set (Vec d)), f (r • x) ∂volume := by simp
    _ = (r ^ d)⁻¹ • ∫ y in r • (Set.univ : Set (Vec d)), f y ∂volume := hcv
    _ = (r ^ d)⁻¹ * ∫ y, vecDot e' (matVecMul (a y) e) * φ (r⁻¹ • y) ∂volume := by
          simp [f, huniv]

theorem bilinearTest_rescale {d : ℕ} (k : ℕ) (e e' : Vec d)
    (φ : Vec d → ℝ) (a : Carrier d) :
    bilinearTest e e' φ (Carrier.rescale k a) =
      (((3 : ℝ) ^ k) ^ d)⁻¹ *
        bilinearTest e e' (fun y => φ (((3 : ℝ) ^ k)⁻¹ • y)) a := by
  exact bilinearTest_smul ((3 : ℝ) ^ k) (by positivity) e e' φ a

theorem measurableSet_triadicDilateSet {d : ℕ} (k : ℕ) {U : Set (Vec d)}
    (hU : MeasurableSet U) : MeasurableSet (triadicDilateSet k U) := by
  have hk : ((3 : ℝ) ^ k) ≠ 0 := by positivity
  have hInv : Measurable (fun x : Vec d => ((3 : ℝ) ^ k)⁻¹ • x) := by
    exact measurable_pi_lambda (fun i => (measurable_pi_apply i).const_mul _)
  have hset : triadicDilateSet k U =
      (fun x : Vec d => ((3 : ℝ) ^ k)⁻¹ • x) ⁻¹' U := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change ((3 : ℝ) ^ k)⁻¹ • triadicDilateVec k y ∈ U
      have hback : ((3 : ℝ) ^ k)⁻¹ • triadicDilateVec k y = y := by
        change ((3 : ℝ) ^ k)⁻¹ • (((3 : ℝ) ^ k) • y) = y
        rw [smul_smul, inv_mul_cancel₀ hk, one_smul]
      rwa [hback]
    · intro hx
      refine ⟨((3 : ℝ) ^ k)⁻¹ • x, hx, ?_⟩
      change x = ((3 : ℝ) ^ k) • (((3 : ℝ) ^ k)⁻¹ • x)
      rw [smul_smul, mul_inv_cancel₀ hk, one_smul]
  rw [hset]
  exact hU.preimage hInv

private theorem smoothCompactProbe_rescale {d : ℕ} (k : ℕ) {φ : Vec d → ℝ}
    (hφ : SmoothCompactProbe φ) :
    SmoothCompactProbe (fun y => φ (((3 : ℝ) ^ k)⁻¹ • y)) :=
  smoothCompactProbe_inv_smul (by positivity) hφ

private theorem tsupport_rescale_subset_triadicDilateSet {d : ℕ} (k : ℕ)
    {U : Set (Vec d)} {φ : Vec d → ℝ} (hφU : tsupport φ ⊆ U) :
    tsupport (fun y => φ (((3 : ℝ) ^ k)⁻¹ • y)) ⊆ triadicDilateSet k U := by
  intro y hy
  rcases tsupport_inv_smul_subset_smul (r := (3 : ℝ) ^ k) (by positivity) hφU hy
    with ⟨x, hx, rfl⟩
  refine ⟨x, hx, ?_⟩
  change ((3 : ℝ) ^ k) • x = triadicDilateVec k x
  congr 1

private theorem triadicDilateSet_univ {d : ℕ} (k : ℕ) :
    triadicDilateSet (d := d) k Set.univ = Set.univ := by
  ext x
  constructor
  · intro _
    trivial
  · intro _
    refine ⟨((3 : ℝ) ^ k)⁻¹ • x, trivial, ?_⟩
    change x = ((3 : ℝ) ^ k) • (((3 : ℝ) ^ k)⁻¹ • x)
    rw [smul_smul, mul_inv_cancel₀ (by positivity : ((3 : ℝ) ^ k) ≠ 0), one_smul]

private theorem localSigma_eq_of_eq {d : ℕ} {U V : Set (Vec d)} (h : U = V)
    (hU : MeasurableSet U) (hV : MeasurableSet V) :
    localSigma U hU = localSigma V hV := by
  cases h
  rfl

theorem measurable_rescale_localSigma {d : ℕ} (k : ℕ) (U : Set (Vec d))
    (hU : MeasurableSet U) :
    @Measurable (Carrier d) (Carrier d)
      (localSigma (triadicDilateSet k U) (measurableSet_triadicDilateSet k hU))
      (localSigma U hU)
      (Carrier.rescale k) := by
  rw [measurable_iff_comap_le, localSigma, localSigma,
    MeasurableSpace.comap_generateFrom]
  apply MeasurableSpace.generateFrom_le
  rintro s ⟨t, ⟨e, e', φ, hφ, hφU, q, hq, rfl⟩, rfl⟩
  let ψ : Vec d → ℝ := fun y => φ (((3 : ℝ) ^ k)⁻¹ • y)
  let c : ℝ := (((3 : ℝ) ^ k) ^ d)⁻¹
  let q' : Set ℝ := (fun z : ℝ => c * z) ⁻¹' q
  have hq' : MeasurableSet q' :=
    hq.preimage ((continuous_const.mul continuous_id).measurable)
  have htest : (fun a : Carrier d => bilinearTest e e' φ (Carrier.rescale k a)) =
      fun a => c * bilinearTest e e' ψ a := by
    funext a
    exact bilinearTest_rescale k e e' φ a
  change @MeasurableSet (Carrier d)
    (localSigma (triadicDilateSet k U) (measurableSet_triadicDilateSet k hU))
    ((fun a : Carrier d => bilinearTest e e' φ (Carrier.rescale k a)) ⁻¹' q)
  rw [htest]
  change @MeasurableSet (Carrier d)
    (localSigma (triadicDilateSet k U) (measurableSet_triadicDilateSet k hU))
    (bilinearTest e e' ψ ⁻¹' q')
  let : MeasurableSpace (Carrier d) :=
    localSigma (triadicDilateSet k U) (measurableSet_triadicDilateSet k hU)
  apply MeasurableSpace.measurableSet_generateFrom
  exact ⟨e, e', ψ, smoothCompactProbe_rescale k hφ,
    tsupport_rescale_subset_triadicDilateSet k hφU, q', hq', rfl⟩

theorem measurable_rescale_globalSigma {d : ℕ} (k : ℕ) :
    Measurable (Carrier.rescale (d := d) k) := by
  change @Measurable (Carrier d) (Carrier d)
    (localSigma Set.univ MeasurableSet.univ) (localSigma Set.univ MeasurableSet.univ)
    (Carrier.rescale k)
  have heq : localSigma (triadicDilateSet k Set.univ)
      (measurableSet_triadicDilateSet k MeasurableSet.univ)
      = localSigma Set.univ MeasurableSet.univ :=
    localSigma_eq_of_eq (triadicDilateSet_univ (d := d) k) _ _
  exact heq ▸ measurable_rescale_localSigma (d := d) k Set.univ MeasurableSet.univ

private theorem measurable_smul_globalSigma {d : ℕ} (r : ℝ) (hr : 0 < r) :
    Measurable (Carrier.smul (d := d) r hr) := by
  apply measurable_generateFrom
  rintro s ⟨e, e', φ, hφ, _hφU, q, hq, rfl⟩
  let ψ : Vec d → ℝ := fun y => φ (r⁻¹ • y)
  let c : ℝ := (r ^ d)⁻¹
  let q' : Set ℝ := (fun z : ℝ => c * z) ⁻¹' q
  have hq' : MeasurableSet q' :=
    hq.preimage ((continuous_const.mul continuous_id).measurable)
  have htest : (fun a : Carrier d => bilinearTest e e' φ (Carrier.smul r hr a)) =
      fun a => c * bilinearTest e e' ψ a := by
    funext a
    exact bilinearTest_smul r hr e e' φ a
  change MeasurableSet
    ((fun a : Carrier d => bilinearTest e e' φ (Carrier.smul r hr a)) ⁻¹' q)
  rw [htest]
  change MeasurableSet (bilinearTest e e' ψ ⁻¹' q')
  apply MeasurableSpace.measurableSet_generateFrom
  exact ⟨e, e', ψ, smoothCompactProbe_inv_smul hr hφ, Set.subset_univ _, q', hq', rfl⟩

theorem measurable_dilateNat_globalSigma {d : ℕ} (k : ℕ) :
    Measurable (Carrier.dilateNat (d := d) k) :=
  measurable_smul_globalSigma _ (inv_pos.mpr (by positivity))

noncomputable def Carrier.rescaleMeasurableEquiv {d : ℕ} (k : ℕ) :
    Carrier d ≃ᵐ Carrier d where
  toEquiv :=
    { toFun := Carrier.rescale k
      invFun := Carrier.dilateNat k
      left_inv := by exact Carrier.smul_dilateNat_rescale k
      right_inv := by exact Carrier.smul_rescale_dilateNat k }
  measurable_toFun := measurable_rescale_globalSigma k
  measurable_invFun := measurable_dilateNat_globalSigma k

theorem Carrier.translate_comp_rescale {d : ℕ} (k : ℕ) (z : Fin d → ℤ) :
    Carrier.translate z ∘ Carrier.rescale k =
      Carrier.rescale k ∘ Carrier.translate (triadicScaleIntShift k z) := by
  funext a
  apply Subtype.ext
  funext x i j
  change Carrier.translate z (Carrier.rescale k a) x i j =
    Carrier.rescale k (Carrier.translate (triadicScaleIntShift k z) a) x i j
  rw [Carrier.translate_apply, Carrier.rescale_apply]
  rw [Carrier.rescale_apply, Carrier.translate_apply]
  have hvec : triadicDilateVec k (x + intVecToRealVec z) =
      triadicDilateVec k x + intVecToRealVec (triadicScaleIntShift k z) := by
    ext l
    simp only [triadicDilateVec, triadicScaleIntShift, intVecToRealVec, Pi.add_apply]
    push_cast
    ring
  rw [hvec]

theorem Carrier.rotate_comp_rescale {d : ℕ} (R : Mat d)
    (hR : IsSignedPermutationMatrix R) (k : ℕ) :
    Carrier.rotate R hR ∘ Carrier.rescale k =
      Carrier.rescale k ∘ Carrier.rotate R hR := by
  funext a
  apply Subtype.ext
  funext x i j
  change Carrier.rotate R hR (Carrier.rescale k a) x i j =
    Carrier.rescale k (Carrier.rotate R hR a) x i j
  rw [Carrier.rotate_apply, Carrier.rescale_apply]
  rw [Carrier.rescale_apply, Carrier.rotate_apply]
  have hcomm : triadicDilateVec k (matVecMul R x) =
      matVecMul R (triadicDilateVec k x) := by
    change ((3 : ℝ) ^ k) • matVecMul R x =
      matVecMul R (((3 : ℝ) ^ k) • x)
    rw [matVecMul_smul]
  rw [hcomm]

theorem Carrier.adjoint_comp_rescale {d : ℕ} (k : ℕ) :
    Carrier.adjoint ∘ Carrier.rescale (d := d) k =
      Carrier.rescale k ∘ Carrier.adjoint := by
  funext a
  apply Subtype.ext
  funext x i j
  change Carrier.adjoint (Carrier.rescale k a) x i j =
    Carrier.rescale k (Carrier.adjoint a) x i j
  rw [Carrier.adjoint_apply, Carrier.rescale_apply]
  rw [Carrier.rescale_apply, Carrier.adjoint_apply]

theorem euclideanDist_triadicDilateVec {d : ℕ} (k : ℕ) (x y : Vec d) :
    euclideanDist (triadicDilateVec k x) (triadicDilateVec k y) =
      (3 : ℝ) ^ k * euclideanDist x y := by
  unfold euclideanDist
  have hsub : triadicDilateVec k x - triadicDilateVec k y =
      triadicDilateVec k (x - y) := by
    ext i
    simp only [triadicDilateVec, Pi.sub_apply]
    ring
  rw [hsub, euclideanNorm_triadicDilateVec]

theorem EuclideanUnitSeparated.triadicDilateSet {d : ℕ} {U V : Set (Vec d)}
    (hUV : EuclideanUnitSeparated U V) (k : ℕ) :
    EuclideanUnitSeparated (triadicDilateSet k U) (triadicDilateSet k V) := by
  intro x y hx hy
  rcases hx with ⟨x0, hx0, rfl⟩
  rcases hy with ⟨y0, hy0, rfl⟩
  rw [euclideanDist_triadicDilateVec]
  have hsep : 1 ≤ euclideanDist x0 y0 := hUV hx0 hy0
  have hscale : 1 ≤ (3 : ℝ) ^ k :=
    one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 3)
  calc
    1 = (1 : ℝ) * 1 := by ring
    _ ≤ (3 : ℝ) ^ k * euclideanDist x0 y0 :=
      mul_le_mul hscale hsep zero_le_one (by positivity)

end Homogenization.Source.Coarse
