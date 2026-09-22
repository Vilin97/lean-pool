/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CoerciveH1Dilation
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.AxisCube
import LeanPool.CoarseGraining.Homogenization.Sobolev.H1.Translation
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInterior
import LeanPool.CoarseGraining.Homogenization.Geometry.TriadicCubeTranslation
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.HarmonicGradientIterationGeometry

/-! # Axis Cube Harmonic Covariance -/

namespace Homogenization

open scoped ENNReal Pointwise

noncomputable section

namespace CubeCalderonZygmund

/-- The center of the open axis cube `axisCube z L`. -/
def axisCubeCenter {d : ℕ} (z : Vec d) (L : ℝ) : Vec d :=
  fun i => z i + L / 2

/-- The affine formula which, for positive `L`, maps the centered unit triadic
cube to `axisCube z L`. -/
def axisCubeAffine {d : ℕ} (z : Vec d) (L : ℝ) : Vec d → Vec d :=
  fun x => L • x + axisCubeCenter z L

/-- The inverse affine formula, which is an actual inverse when `L ≠ 0`. -/
def axisCubeAffineInv {d : ℕ} (z : Vec d) (L : ℝ) : Vec d → Vec d :=
  fun x => L⁻¹ • (x - axisCubeCenter z L)

@[simp] theorem axisCubeAffineInv_axisCubeAffine {d : ℕ} (z : Vec d) {L : ℝ}
    (hL : L ≠ 0) (x : Vec d) :
    axisCubeAffineInv z L (axisCubeAffine z L x) = x := by
  ext i
  simp [axisCubeAffineInv, axisCubeAffine, hL]

@[simp] theorem axisCubeAffine_axisCubeAffineInv {d : ℕ} (z : Vec d) {L : ℝ}
    (hL : L ≠ 0) (x : Vec d) :
    axisCubeAffine z L (axisCubeAffineInv z L x) = x := by
  ext i
  simp [axisCubeAffineInv, axisCubeAffine, hL]

/-- The affine parametrization as a measurable equivalence of the ambient
Euclidean space when its scale is nonzero. -/
def axisCubeAffineMeasurableEquiv {d : ℕ} (z : Vec d) {L : ℝ}
    (hL : L ≠ 0) : Vec d ≃ᵐ Vec d where
  toEquiv :=
    { toFun := axisCubeAffine z L
      invFun := axisCubeAffineInv z L
      left_inv := axisCubeAffineInv_axisCubeAffine z hL
      right_inv := axisCubeAffine_axisCubeAffineInv z hL }
  measurable_toFun := (measurable_const_smul L).add measurable_const
  measurable_invFun :=
    (measurable_const_smul L⁻¹).comp (measurable_id.sub measurable_const)

@[simp] theorem axisCubeAffineMeasurableEquiv_apply {d : ℕ} (z : Vec d) {L : ℝ}
    (hL : L ≠ 0) (x : Vec d) :
    axisCubeAffineMeasurableEquiv z hL x = axisCubeAffine z L x :=
  rfl

@[simp] theorem axisCubeAffineMeasurableEquiv_symm_apply {d : ℕ} (z : Vec d)
    {L : ℝ} (hL : L ≠ 0) (x : Vec d) :
    (axisCubeAffineMeasurableEquiv z hL).symm x = axisCubeAffineInv z L x :=
  rfl

@[simp] theorem axisCubeAffine_comp {d : ℕ} (z w : Vec d) (L S : ℝ)
    (x : Vec d) :
    axisCubeAffine z L (axisCubeAffine w S x) =
      axisCubeAffine (fun i => L * w i + axisCubeCenter z L i) (L * S) x := by
  ext i
  simp only [axisCubeAffine, axisCubeCenter, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem openCubeSet_originCube_zero_eq_centered_axisCube {d : ℕ} :
    openCubeSet (originCube d 0) =
      axisCube (fun _ => (-(1 / 2 : ℝ))) 1 := by
  ext x
  simp only [openCubeSet, originCube, cubeScaleFactor, axisCube, Set.mem_ofPred_eq,
    Set.mem_pi, Set.mem_univ, forall_true_left, Set.mem_Ioo, zpow_zero]
  constructor <;> intro hx <;> intro i
  · have hxi := hx i
    norm_num at hxi ⊢
    constructor <;> linarith [hxi.1, hxi.2]
  · have hxi := hx i
    norm_num at hxi ⊢
    constructor <;> linarith [hxi.1, hxi.2]

/-- An arbitrary positive-length axis cube is the centered-unit triadic cube,
dilated by its side length and translated to its center. -/
theorem axisCube_eq_translateSet_smul_openCubeSet_originCube_zero {d : ℕ}
    (z : Vec d) (L : ℝ) (hL : 0 < L) :
    axisCube z L =
      translateSet (axisCubeCenter z L) (L • openCubeSet (originCube d 0)) := by
  rw [openCubeSet_originCube_zero_eq_centered_axisCube]
  ext x
  rw [mem_translateSet_iff_sub_mem, Set.mem_smul_set_iff_inv_smul_mem₀ hL.ne']
  simp only [axisCube, Set.mem_pi, Set.mem_univ, forall_true_left, Set.mem_Ioo,
    axisCubeCenter, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  constructor <;> intro hx <;> intro i
  · have hxi := hx i
    have hlo : (-(1 / 2 : ℝ)) < (x i - (z i + L / 2)) / L := by
      apply (lt_div_iff₀ hL).mpr
      linarith [hxi.1]
    have hhi : (x i - (z i + L / 2)) / L < (1 / 2 : ℝ) := by
      apply (div_lt_iff₀ hL).mpr
      linarith [hxi.2]
    norm_num at hlo hhi ⊢
    constructor
    · convert hlo using 1
      all_goals first | rfl | ring
    · convert hhi using 1
      all_goals first | rfl | ring
  · have hxi := hx i
    norm_num at hxi ⊢
    have hlo : (-(1 / 2 : ℝ)) < (x i - (z i + L / 2)) / L := by
      simpa [div_eq_mul_inv, mul_comm] using hxi.1
    have hhi : (x i - (z i + L / 2)) / L < (1 / 2 : ℝ) := by
      simpa [div_eq_mul_inv, mul_comm] using hxi.2
    constructor
    · have := (lt_div_iff₀ hL).mp hlo
      linarith
    · have := (div_lt_iff₀ hL).mp hhi
      linarith

/-- The positive affine parametrization maps the centered unit cube exactly
onto its target axis cube. -/
theorem axisCubeAffine_image_openCubeSet_originCube_zero {d : ℕ}
    (z : Vec d) (L : ℝ) (hL : 0 < L) :
    axisCubeAffine z L '' openCubeSet (originCube d 0) = axisCube z L := by
  rw [axisCube_eq_translateSet_smul_openCubeSet_originCube_zero z L hL]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨L • x, ⟨x, hx, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, rfl⟩

/-- The target axis cube has the centered unit cube as its exact preimage under
the positive affine parametrization. -/
theorem axisCubeAffine_preimage_axisCube {d : ℕ}
    (z : Vec d) (L : ℝ) (hL : 0 < L) :
    axisCubeAffine z L ⁻¹' axisCube z L = openCubeSet (originCube d 0) := by
  rw [← axisCubeAffine_image_openCubeSet_originCube_zero z L hL]
  exact Set.preimage_image_eq _ (axisCubeAffineMeasurableEquiv z hL.ne').injective

/-- A positive affine cube parametrization maps every positive axis cube to
the axis cube with the expected affine corner and product side length. -/
theorem axisCubeAffine_image_axisCube {d : ℕ}
    (z w : Vec d) (L S : ℝ) (hL : 0 < L) (hS : 0 < S) :
    axisCubeAffine z L '' axisCube w S =
      axisCube (fun i => L * w i + axisCubeCenter z L i) (L * S) := by
  rw [← axisCubeAffine_image_openCubeSet_originCube_zero w S hS,
    Set.image_image]
  rw [show (fun x => axisCubeAffine z L (axisCubeAffine w S x)) =
      axisCubeAffine (fun i => L * w i + axisCubeCenter z L i) (L * S) by
    funext x
    exact axisCubeAffine_comp z w L S x]
  exact axisCubeAffine_image_openCubeSet_originCube_zero _ _ (mul_pos hL hS)

/-- Exact preimage form of `axisCubeAffine_image_axisCube`. -/
theorem axisCubeAffine_preimage_axisCube_affine {d : ℕ}
    (z w : Vec d) (L S : ℝ) (hL : 0 < L) (hS : 0 < S) :
    axisCubeAffine z L ⁻¹'
        axisCube (fun i => L * w i + axisCubeCenter z L i) (L * S) =
      axisCube w S := by
  rw [← axisCubeAffine_image_axisCube z w L S hL hS]
  exact Set.preimage_image_eq _ (axisCubeAffineMeasurableEquiv z hL.ne').injective

/-- Lower corner of the open axis-cube realization of a triadic cube. -/
def triadicCubeAxisCorner {d : ℕ} (Q : TriadicCube d) : Vec d :=
  fun i => ((Q.index i : ℝ) - 1 / 2) * cubeScaleFactor Q

/-- Every open triadic cube is exactly its lower-corner axis cube. -/
theorem openCubeSet_eq_axisCube_triadicCube {d : ℕ} (Q : TriadicCube d) :
    openCubeSet Q = axisCube (triadicCubeAxisCorner Q) (cubeScaleFactor Q) := by
  have hupper : ∀ i : Fin d,
      triadicCubeAxisCorner Q i + cubeScaleFactor Q =
        ((Q.index i : ℝ) + 1 / 2) * cubeScaleFactor Q := by
    intro i
    simp only [triadicCubeAxisCorner]
    ring
  ext x
  simp only [openCubeSet, axisCube, triadicCubeAxisCorner, Set.mem_ofPred_eq,
    Set.mem_pi, Set.mem_univ, forall_true_left, Set.mem_Ioo]
  constructor <;> intro hx <;> intro i
  · rw [show ((Q.index i : ℝ) - 1 / 2) * cubeScaleFactor Q +
        cubeScaleFactor Q =
      ((Q.index i : ℝ) + 1 / 2) * cubeScaleFactor Q by
        simpa only [triadicCubeAxisCorner] using hupper i]
    exact hx i
  · have hxi := hx i
    rw [show ((Q.index i : ℝ) - 1 / 2) * cubeScaleFactor Q +
        cubeScaleFactor Q =
      ((Q.index i : ℝ) + 1 / 2) * cubeScaleFactor Q by
        simpa only [triadicCubeAxisCorner] using hupper i] at hxi
    exact hxi

/-- Side length of the concentric depth-`n` contraction of `axisCube z L`. -/
def axisCubeConcentricDepthSide (L : ℝ) (n : ℕ) : ℝ :=
  L * (3 : ℝ) ^ (-(n : ℤ))

@[simp] theorem axisCubeConcentricDepthSide_zero (L : ℝ) :
    axisCubeConcentricDepthSide L 0 = L := by
  simp [axisCubeConcentricDepthSide]

theorem axisCubeConcentricDepthSide_pos {L : ℝ} (hL : 0 < L) (n : ℕ) :
    0 < axisCubeConcentricDepthSide L n := by
  unfold axisCubeConcentricDepthSide
  positivity

/-- Lower corner of the concentric depth-`n` contraction of `axisCube z L`. -/
def axisCubeConcentricDepthCorner {d : ℕ} (z : Vec d) (L : ℝ) (n : ℕ) :
    Vec d :=
  fun i => axisCubeCenter z L i - axisCubeConcentricDepthSide L n / 2

@[simp] theorem axisCubeConcentricDepthCorner_zero {d : ℕ} (z : Vec d) (L : ℝ) :
    axisCubeConcentricDepthCorner z L 0 = z := by
  ext i
  simp only [axisCubeConcentricDepthCorner, axisCubeConcentricDepthSide_zero,
    axisCubeCenter]
  ring

/-- The outer affine parametrization maps the centered depth-`n` source cube
exactly to the corresponding concentric contraction of its target cube. -/
theorem axisCubeAffine_image_openCubeSet_originCube_neg_nat {d : ℕ}
    (z : Vec d) (L : ℝ) (hL : 0 < L) (n : ℕ) :
    axisCubeAffine z L '' openCubeSet (originCube d (-(n : ℤ))) =
      axisCube (axisCubeConcentricDepthCorner z L n)
        (axisCubeConcentricDepthSide L n) := by
  rw [openCubeSet_eq_axisCube_triadicCube]
  have hscale : 0 < cubeScaleFactor (originCube d (-(n : ℤ))) := by
    change 0 < (3 : ℝ) ^ (-(n : ℤ))
    positivity
  rw [axisCubeAffine_image_axisCube z _ L _ hL hscale]
  congr 2
  · funext i
    simp only [triadicCubeAxisCorner, originCube, Pi.zero_apply, Int.cast_zero,
      zero_sub, axisCubeConcentricDepthCorner, axisCubeConcentricDepthSide,
      cubeScaleFactor]
    ring

/-- Exact preimage form of the fixed concentric depth transport. -/
theorem axisCubeAffine_preimage_concentricDepthAxisCube {d : ℕ}
    (z : Vec d) (L : ℝ) (hL : 0 < L) (n : ℕ) :
    axisCubeAffine z L ⁻¹'
        axisCube (axisCubeConcentricDepthCorner z L n)
          (axisCubeConcentricDepthSide L n) =
      openCubeSet (originCube d (-(n : ℤ))) := by
  rw [← axisCubeAffine_image_openCubeSet_originCube_neg_nat z L hL n]
  exact Set.preimage_image_eq _ (axisCubeAffineMeasurableEquiv z hL.ne').injective

@[simp] private theorem H1Function.grad_cast {d : ℕ} {U V : Set (Vec d)}
    (hUV : U = V) (u : H1Function U) (x : Vec d) :
    (hUV ▸ u).grad x = u.grad x := by
  cases hUV
  rfl

@[simp] private theorem H1Function.toFun_cast {d : ℕ} {U V : Set (Vec d)}
    (hUV : U = V) (u : H1Function U) (x : Vec d) :
    (hUV ▸ u).toFun x = u.toFun x := by
  cases hUV
  rfl

private theorem WeakPoissonEquationOn.castDomain {d : ℕ} {U V : Set (Vec d)}
    (hUV : U = V) {u : H1Function U} {f : Vec d → ℝ}
    (h : WeakPoissonEquationOn U u f) :
    WeakPoissonEquationOn V (hUV ▸ u) f := by
  cases hUV
  exact h

/-- Homogeneous weak Poisson equations are invariant under the gradient-preserving
pullback from `a • U` to `U`. -/
theorem WeakPoissonEquationOn.undilateSet_zero {d : ℕ} {U V : Set (Vec d)}
    {a : ℝ} (ha : 0 < a) (hV : V = a • U) {u : H1Function V}
    (h : WeakPoissonEquationOn V u 0) :
    WeakPoissonEquationOn U (u.undilateSet ha hV) 0 := by
  subst V
  intro φ hφ hφs hφ_sub
  let ψ : Vec d → ℝ := fun y => φ (a⁻¹ • y)
  have ha_ne : a ≠ 0 := ha.ne'
  have hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ := by
    simpa [ψ] using! hφ.comp (contDiff_const_smul a⁻¹)
  have hψ_supp : HasCompactSupport ψ := by
    show HasCompactSupport (φ ∘ Homeomorph.smulOfNeZero a⁻¹ (inv_ne_zero ha_ne))
    simpa [ψ, Function.comp] using
      hφs.comp_homeomorph (Homeomorph.smulOfNeZero a⁻¹ (inv_ne_zero ha_ne))
  have hψ_sub : tsupport ψ ⊆ a • U := by
    intro y hy
    have hy' : a⁻¹ • y ∈ tsupport φ := by
      rw [show ψ = φ ∘ Homeomorph.smulOfNeZero a⁻¹ (inv_ne_zero ha_ne) by rfl,
        tsupport_comp_eq_preimage φ (Homeomorph.smulOfNeZero a⁻¹ (inv_ne_zero ha_ne))] at hy
      exact hy
    exact ⟨a⁻¹ • y, hφ_sub hy', by simp [ha_ne, smul_smul]⟩
  have hgradψ : ∀ y : Vec d,
      euclideanGradient ψ y = a⁻¹ • euclideanGradient φ (a⁻¹ • y) := by
    intro y
    ext i
    unfold euclideanGradient euclideanCoordDeriv
    have hderiv :
        fderiv ℝ (fun z : Vec d => φ (a⁻¹ • z)) y =
          a⁻¹ • fderiv ℝ φ (a⁻¹ • y) := by
      simpa [ψ] using (fderiv_comp_smul (𝕜 := ℝ) (f := φ) (x := y) a⁻¹)
    change (fderiv ℝ ψ y) (basisVec i) =
      a⁻¹ * (fderiv ℝ φ (a⁻¹ • y)) (basisVec i)
    change (fderiv ℝ (fun z : Vec d => φ (a⁻¹ • z)) y) (basisVec i) = _
    rw [hderiv]
    rfl
  have htest :
      ∫ y in a • U, vecDot (u.grad y) (euclideanGradient ψ y) ∂MeasureTheory.volume = 0 := by
    simpa using h.test ψ hψ_smooth hψ_supp hψ_sub
  have hscaled :
      a⁻¹ * ∫ y in a • U,
          vecDot (u.grad y) (euclideanGradient φ (a⁻¹ • y)) ∂MeasureTheory.volume = 0 := by
    calc
      a⁻¹ * ∫ y in a • U,
          vecDot (u.grad y) (euclideanGradient φ (a⁻¹ • y)) ∂MeasureTheory.volume
        = ∫ y in a • U,
            a⁻¹ * vecDot (u.grad y) (euclideanGradient φ (a⁻¹ • y))
              ∂MeasureTheory.volume := by
            rw [MeasureTheory.integral_const_mul]
      _ = ∫ y in a • U, vecDot (u.grad y) (euclideanGradient ψ y)
              ∂MeasureTheory.volume := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards with y
            rw [hgradψ]
            simp only [vecDot, Pi.smul_apply, smul_eq_mul]
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            ring
      _ = 0 := htest
  have hinner :
      ∫ y in a • U,
          vecDot (u.grad y) (euclideanGradient φ (a⁻¹ • y)) ∂MeasureTheory.volume = 0 := by
    exact (mul_eq_zero.mp hscaled).resolve_left (inv_ne_zero ha_ne)
  have hchange :
      ∫ x in U, vecDot ((u.undilateSet ha rfl).grad x) (euclideanGradient φ x)
          ∂MeasureTheory.volume =
        (a ^ d)⁻¹ * ∫ y in a • U,
          vecDot (u.grad y) (euclideanGradient φ (a⁻¹ • y)) ∂MeasureTheory.volume := by
    simpa only [H1Function.undilateSet_grad, smul_smul, inv_mul_cancel₀ ha_ne,
      one_smul, Module.finrank_fin_fun] using!
      (MeasureTheory.Measure.setIntegral_comp_smul_of_pos
        (μ := MeasureTheory.volume)
        (f := fun y : Vec d =>
          vecDot (u.grad y) (euclideanGradient φ (a⁻¹ • y)))
        (s := U) ha)
  rw [hchange, hinner, mul_zero]
  simp

/-- Homogeneous weak Poisson equations are invariant under translation pullback. -/
theorem WeakPoissonEquationOn.untranslate_zero {d : ℕ} {U : Set (Vec d)}
    {z : Vec d} {u : H1Function (translateSet z U)}
    (h : WeakPoissonEquationOn (translateSet z U) u 0) :
    WeakPoissonEquationOn U (u.untranslate z) 0 := by
  have hdomain : translateSet (-z) (translateSet z U) = U := by
    simpa [sub_eq_add_neg] using (translateSet_translateSet (d := d) z (-z) U)
  have htranslated :
      WeakPoissonEquationOn (translateSet (-z) (translateSet z U))
        (u.translate (-z)) 0 := by
    simpa using! h.translate (-z)
  have hcast : WeakPoissonEquationOn U (hdomain ▸ u.translate (-z)) 0 :=
    WeakPoissonEquationOn.castDomain hdomain htranslated
  have hu : hdomain ▸ u.translate (-z) = u.untranslate z := by
    apply H1Function.ext
    · funext x
      simp [sub_eq_add_neg]
    · funext x
      simp [sub_eq_add_neg]
  simpa [hu] using hcast

/-- Pull an `H¹` function on a positive-length axis cube back to the fixed
centered unit triadic cube, with the standard value normalization that leaves
the gradient unscaled. -/
noncomputable def axisCubeHarmonicPullback {d : ℕ} (z : Vec d) {L : ℝ}
    (hL : 0 < L) (u : H1Function (axisCube z L)) :
    H1Function (openCubeSet (originCube d 0)) := by
  let U0 : Set (Vec d) := openCubeSet (originCube d 0)
  let c : Vec d := axisCubeCenter z L
  let V : Set (Vec d) := translateSet c (L • U0)
  have hV : axisCube z L = V := by
    simpa [U0, c, V] using
      axisCube_eq_translateSet_smul_openCubeSet_originCube_zero z L hL
  let uV : H1Function V := hV ▸ u
  let uD : H1Function (L • U0) := H1Function.untranslate c uV
  exact uD.undilateSet hL rfl

/-- Pullback to the centered unit cube preserves the homogeneous weak Poisson
equation. -/
theorem axisCubeHarmonicPullback_weakPoisson_zero {d : ℕ} (z : Vec d) {L : ℝ}
    (hL : 0 < L) {u : H1Function (axisCube z L)}
    (h : WeakPoissonEquationOn (axisCube z L) u 0) :
    WeakPoissonEquationOn (openCubeSet (originCube d 0))
      (axisCubeHarmonicPullback z hL u) 0 := by
  let U0 : Set (Vec d) := openCubeSet (originCube d 0)
  let c : Vec d := axisCubeCenter z L
  let V : Set (Vec d) := translateSet c (L • U0)
  have hV : axisCube z L = V := by
    simpa [U0, c, V] using
      axisCube_eq_translateSet_smul_openCubeSet_originCube_zero z L hL
  let uV : H1Function V := hV ▸ u
  have hVweak : WeakPoissonEquationOn V uV 0 :=
    WeakPoissonEquationOn.castDomain hV h
  have hD : WeakPoissonEquationOn (L • U0) (H1Function.untranslate c uV) 0 :=
    WeakPoissonEquationOn.untranslate_zero hVweak
  have hU : WeakPoissonEquationOn U0
      ((H1Function.untranslate c uV).undilateSet hL rfl) 0 :=
    WeakPoissonEquationOn.undilateSet_zero hL rfl hD
  simpa only [axisCubeHarmonicPullback] using hU

/-- The pushforward of centered-unit Lebesgue measure through the affine map.
For positive `L`, `axisCubeNormalizedMeasure_eq_smul_volume_restrict` below
identifies this with normalized Lebesgue measure on `axisCube z L`.  No such
axis-cube interpretation is claimed for nonpositive `L`. -/
noncomputable def axisCubeNormalizedMeasure {d : ℕ} (z : Vec d) (L : ℝ) :
    MeasureTheory.Measure (Vec d) :=
  MeasureTheory.Measure.map (axisCubeAffine z L)
    (MeasureTheory.volume.restrict (openCubeSet (originCube d 0)))

/-- For positive side length, the affine pushforward is exactly normalized
Lebesgue measure on the target axis cube. -/
theorem axisCubeNormalizedMeasure_eq_smul_volume_restrict {d : ℕ}
    (z : Vec d) (L : ℝ) (hL : 0 < L) :
    axisCubeNormalizedMeasure z L =
      ENNReal.ofReal ((L ^ d)⁻¹) •
        MeasureTheory.volume.restrict (axisCube z L) := by
  let U0 : Set (Vec d) := openCubeSet (originCube d 0)
  let c : Vec d := axisCubeCenter z L
  calc
    axisCubeNormalizedMeasure z L =
        MeasureTheory.Measure.map (fun x : Vec d => x + c)
          (MeasureTheory.Measure.map (fun x : Vec d => L • x)
            (MeasureTheory.volume.restrict U0)) := by
      rw [MeasureTheory.Measure.map_map (measurable_add_const c)
        (measurable_const_smul L)]
      rfl
    _ = MeasureTheory.Measure.map (fun x : Vec d => x + c)
          (ENNReal.ofReal ((L ^ d)⁻¹) •
            MeasureTheory.volume.restrict (L • U0)) := by
      rw [map_smul_volume_restrict hL U0]
    _ = ENNReal.ofReal ((L ^ d)⁻¹) •
          MeasureTheory.Measure.map (fun x : Vec d => x + c)
            (MeasureTheory.volume.restrict (L • U0)) := by
      rw [MeasureTheory.Measure.map_smul _ (f := fun x : Vec d => x + c)
        (measurable_id.add measurable_const).aemeasurable]
    _ = ENNReal.ofReal ((L ^ d)⁻¹) •
          MeasureTheory.volume.restrict (translateSet c (L • U0)) := by
      rw [(measurePreserving_addRight_restrict_translateSet c (L • U0)).map_eq]
    _ = ENNReal.ofReal ((L ^ d)⁻¹) •
          MeasureTheory.volume.restrict (axisCube z L) := by
      rw [axisCube_eq_translateSet_smul_openCubeSet_originCube_zero z L hL]

/-- Canonical normalized-volume form of the target measure at a fixed
concentric depth. -/
theorem axisCubeNormalizedMeasure_concentricDepth_eq_smul_volume_restrict
    {d : ℕ} (z : Vec d) (L : ℝ) (hL : 0 < L) (n : ℕ) :
    axisCubeNormalizedMeasure (axisCubeConcentricDepthCorner z L n)
        (axisCubeConcentricDepthSide L n) =
      ENNReal.ofReal (((axisCubeConcentricDepthSide L n) ^ d)⁻¹) •
        MeasureTheory.volume.restrict
          (axisCube (axisCubeConcentricDepthCorner z L n)
            (axisCubeConcentricDepthSide L n)) :=
  axisCubeNormalizedMeasure_eq_smul_volume_restrict _ _
    (axisCubeConcentricDepthSide_pos hL n)

/-- On a triadic cube, the affine pushforward normalization agrees exactly
with the project's canonical `normalizedCubeMeasure`. -/
theorem axisCubeNormalizedMeasure_triadicCube {d : ℕ} (Q : TriadicCube d) :
    axisCubeNormalizedMeasure (triadicCubeAxisCorner Q) (cubeScaleFactor Q) =
      normalizedCubeMeasure Q := by
  have hscale : 0 < cubeScaleFactor Q := by
    simpa [cubeScaleFactor] using
      (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)
  rw [axisCubeNormalizedMeasure_eq_smul_volume_restrict _ _ hscale,
    ← openCubeSet_eq_axisCube_triadicCube Q, normalizedCubeMeasure, cubeMeasure,
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q,
    cubeVolume_eq_scaleFactor_pow]

private theorem axisCubeConcentricDepthSide_eq_centralDescendant_cubeScaleFactor
    {d : ℕ} (Q : TriadicCube d) (n : ℕ) :
    axisCubeConcentricDepthSide (cubeScaleFactor Q) n =
      cubeScaleFactor (centralDescendant Q n) := by
  rw [centralDescendant_cubeScaleFactor]
  simp only [axisCubeConcentricDepthSide, zpow_neg, zpow_natCast, div_eq_mul_inv]

private theorem axisCubeConcentricDepthCorner_eq_centralDescendant_triadicCubeAxisCorner
    {d : ℕ} (Q : TriadicCube d) (n : ℕ) :
    axisCubeConcentricDepthCorner (triadicCubeAxisCorner Q) (cubeScaleFactor Q) n =
      triadicCubeAxisCorner (centralDescendant Q n) := by
  ext i
  simp only [triadicCubeAxisCorner, axisCubeConcentricDepthCorner, axisCubeCenter,
    axisCubeConcentricDepthSide]
  rw [centralDescendant_index Q n i, centralDescendant_cubeScaleFactor]
  simp only [zpow_neg, zpow_natCast, div_eq_mul_inv]
  field_simp [pow_ne_zero n (by norm_num : (3 : ℝ) ≠ 0)]
  simp only [Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
  ring

/-- The concentric depth-`n` axis cube of a triadic cube is exactly its
ordinary central depth-`n` descendant. -/
theorem axisCube_concentricDepth_eq_openCubeSet_centralDescendant {d : ℕ}
    (Q : TriadicCube d) (n : ℕ) :
    axisCube
        (axisCubeConcentricDepthCorner (triadicCubeAxisCorner Q) (cubeScaleFactor Q) n)
        (axisCubeConcentricDepthSide (cubeScaleFactor Q) n) =
      openCubeSet (centralDescendant Q n) := by
  rw [openCubeSet_eq_axisCube_triadicCube]
  rw [axisCubeConcentricDepthCorner_eq_centralDescendant_triadicCubeAxisCorner,
    axisCubeConcentricDepthSide_eq_centralDescendant_cubeScaleFactor]

/-- The affine normalized measure on a concentric depth-`n` axis cube is the
canonical normalized measure on the corresponding central descendant. -/
theorem axisCubeNormalizedMeasure_concentricDepth_eq_normalizedCubeMeasure_centralDescendant
    {d : ℕ} (Q : TriadicCube d) (n : ℕ) :
    axisCubeNormalizedMeasure
        (axisCubeConcentricDepthCorner (triadicCubeAxisCorner Q) (cubeScaleFactor Q) n)
        (axisCubeConcentricDepthSide (cubeScaleFactor Q) n) =
      normalizedCubeMeasure (centralDescendant Q n) := by
  rw [← axisCubeNormalizedMeasure_triadicCube (centralDescendant Q n)]
  rw [axisCubeConcentricDepthCorner_eq_centralDescendant_triadicCubeAxisCorner,
    axisCubeConcentricDepthSide_eq_centralDescendant_cubeScaleFactor]

/-- Affine pushforward of an affine-cube normalized measure is the normalized
measure with the composed affine corner and product scale.  This identity is
purely a pushforward identity and therefore does not require positive scales. -/
theorem map_axisCubeAffine_axisCubeNormalizedMeasure {d : ℕ}
    (z w : Vec d) (L S : ℝ) :
    MeasureTheory.Measure.map (axisCubeAffine z L)
        (axisCubeNormalizedMeasure w S) =
      axisCubeNormalizedMeasure
        (fun i => L * w i + axisCubeCenter z L i) (L * S) := by
  unfold axisCubeNormalizedMeasure
  have hout : Measurable (axisCubeAffine z L) :=
    (measurable_const_smul L).add measurable_const
  have hin : Measurable (axisCubeAffine w S) :=
    (measurable_const_smul S).add measurable_const
  calc
    MeasureTheory.Measure.map (axisCubeAffine z L)
        (MeasureTheory.Measure.map (axisCubeAffine w S)
          (MeasureTheory.volume.restrict (openCubeSet (originCube d 0)))) =
      MeasureTheory.Measure.map (axisCubeAffine z L ∘ axisCubeAffine w S)
        (MeasureTheory.volume.restrict (openCubeSet (originCube d 0))) :=
      MeasureTheory.Measure.map_map hout hin
    _ = MeasureTheory.Measure.map
        (axisCubeAffine (fun i => L * w i + axisCubeCenter z L i) (L * S))
        (MeasureTheory.volume.restrict (openCubeSet (originCube d 0))) := by
      apply MeasureTheory.Measure.map_congr
      filter_upwards with x
      exact axisCubeAffine_comp z w L S x

/-- The affine map preserves the centered-unit source measure and its
pushforward measure. -/
theorem measurePreserving_axisCubeAffine {d : ℕ} (z : Vec d) (L : ℝ) :
    MeasureTheory.MeasurePreserving (axisCubeAffine z L)
      (MeasureTheory.volume.restrict (openCubeSet (originCube d 0)))
      (axisCubeNormalizedMeasure z L) :=
  ⟨(measurable_const_smul L).add measurable_const, rfl⟩

/-- For nonzero scale, the inverse affine map preserves the pushforward
measure back to centered-unit Lebesgue measure. -/
theorem measurePreserving_axisCubeAffineInv {d : ℕ} (z : Vec d) {L : ℝ}
    (hL : L ≠ 0) :
    MeasureTheory.MeasurePreserving (axisCubeAffineInv z L)
      (axisCubeNormalizedMeasure z L)
      (MeasureTheory.volume.restrict (openCubeSet (originCube d 0))) := by
  simpa only [axisCubeAffineMeasurableEquiv_apply,
    axisCubeAffineMeasurableEquiv_symm_apply] using!
    (measurePreserving_axisCubeAffine z L).symm
      (axisCubeAffineMeasurableEquiv z hL)

/-- Strong a.e. measurability can be transported in either direction through
the nondegenerate affine parametrization. -/
theorem aestronglyMeasurable_axisCubeAffine_iff {d : ℕ} (z : Vec d) {L : ℝ}
    (hL : L ≠ 0) {E : Type*} [TopologicalSpace E] (f : Vec d → E) :
    MeasureTheory.AEStronglyMeasurable
        (fun x => f (axisCubeAffine z L x))
        (MeasureTheory.volume.restrict (openCubeSet (originCube d 0))) ↔
      MeasureTheory.AEStronglyMeasurable f (axisCubeNormalizedMeasure z L) := by
  constructor
  · intro hf
    have hcomp := hf.comp_measurePreserving
      (measurePreserving_axisCubeAffineInv z hL)
    have hfun : (fun x => f (axisCubeAffine z L x)) ∘ axisCubeAffineInv z L = f := by
      funext x
      exact congrArg f (axisCubeAffine_axisCubeAffineInv z hL x)
    rw [hfun] at hcomp
    exact hcomp
  · intro hf
    simpa only [Function.comp_apply] using!
      hf.comp_measurePreserving (measurePreserving_axisCubeAffine z L)

/-- `MemLp` is equivalent on the source and target of every nondegenerate
affine cube parametrization.  In particular, target integrability can be
deduced from source integrability without a circular target-measurability
hypothesis. -/
theorem memLp_axisCubeAffine_iff {d : ℕ} (z : Vec d) {L : ℝ}
    (hL : L ≠ 0) {E : Type*} [TopologicalSpace E] [ContinuousENorm E]
    (p : ℝ≥0∞) (f : Vec d → E) :
    MeasureTheory.MemLp (fun x => f (axisCubeAffine z L x)) p
        (MeasureTheory.volume.restrict (openCubeSet (originCube d 0))) ↔
      MeasureTheory.MemLp f p (axisCubeNormalizedMeasure z L) := by
  constructor
  · intro hf
    have hcomp := hf.comp_measurePreserving
      (measurePreserving_axisCubeAffineInv z hL)
    have hfun : (fun x => f (axisCubeAffine z L x)) ∘ axisCubeAffineInv z L = f := by
      funext x
      exact congrArg f (axisCubeAffine_axisCubeAffineInv z hL x)
    rw [hfun] at hcomp
    exact hcomp
  · intro hf
    simpa only [Function.comp_apply] using!
      hf.comp_measurePreserving (measurePreserving_axisCubeAffine z L)

/-- The fixed centered depth-`n` source measure pushes forward to the exact
normalized measure on the target concentric contraction. -/
theorem map_axisCubeAffine_normalizedCubeMeasure_originCube_neg_nat {d : ℕ}
    (z : Vec d) (L : ℝ) (n : ℕ) :
    MeasureTheory.Measure.map (axisCubeAffine z L)
        (normalizedCubeMeasure (originCube d (-(n : ℤ)))) =
      axisCubeNormalizedMeasure (axisCubeConcentricDepthCorner z L n)
        (axisCubeConcentricDepthSide L n) := by
  rw [← axisCubeNormalizedMeasure_triadicCube (originCube d (-(n : ℤ))),
    map_axisCubeAffine_axisCubeNormalizedMeasure]
  congr 2
  funext i
  simp only [triadicCubeAxisCorner, originCube, Pi.zero_apply, Int.cast_zero,
    zero_sub, axisCubeConcentricDepthCorner, axisCubeConcentricDepthSide,
    cubeScaleFactor]
  ring

/-- Measure-preserving form of the fixed concentric depth transport. -/
theorem measurePreserving_axisCubeAffine_originCube_neg_nat {d : ℕ}
    (z : Vec d) (L : ℝ) (n : ℕ) :
    MeasureTheory.MeasurePreserving (axisCubeAffine z L)
      (normalizedCubeMeasure (originCube d (-(n : ℤ))))
      (axisCubeNormalizedMeasure (axisCubeConcentricDepthCorner z L n)
        (axisCubeConcentricDepthSide L n)) :=
  ⟨(measurable_const_smul L).add measurable_const,
    map_axisCubeAffine_normalizedCubeMeasure_originCube_neg_nat z L n⟩

/-- Inverse measure-preserving form of the fixed concentric depth transport. -/
theorem measurePreserving_axisCubeAffineInv_originCube_neg_nat {d : ℕ}
    (z : Vec d) {L : ℝ} (hL : L ≠ 0) (n : ℕ) :
    MeasureTheory.MeasurePreserving (axisCubeAffineInv z L)
      (axisCubeNormalizedMeasure (axisCubeConcentricDepthCorner z L n)
        (axisCubeConcentricDepthSide L n))
      (normalizedCubeMeasure (originCube d (-(n : ℤ)))) := by
  simpa only [axisCubeAffineMeasurableEquiv_apply,
    axisCubeAffineMeasurableEquiv_symm_apply] using!
    (measurePreserving_axisCubeAffine_originCube_neg_nat z L n).symm
      (axisCubeAffineMeasurableEquiv z hL)

/-- Bidirectional strong a.e. measurability transport on a fixed concentric
depth. -/
theorem aestronglyMeasurable_axisCubeAffine_originCube_neg_nat_iff {d : ℕ}
    (z : Vec d) {L : ℝ} (hL : L ≠ 0) (n : ℕ)
    {E : Type*} [TopologicalSpace E] (f : Vec d → E) :
    MeasureTheory.AEStronglyMeasurable (fun x => f (axisCubeAffine z L x))
        (normalizedCubeMeasure (originCube d (-(n : ℤ)))) ↔
      MeasureTheory.AEStronglyMeasurable f
        (axisCubeNormalizedMeasure (axisCubeConcentricDepthCorner z L n)
          (axisCubeConcentricDepthSide L n)) := by
  constructor
  · intro hf
    have hcomp := hf.comp_measurePreserving
      (measurePreserving_axisCubeAffineInv_originCube_neg_nat z hL n)
    have hfun : (fun x => f (axisCubeAffine z L x)) ∘ axisCubeAffineInv z L = f := by
      funext x
      exact congrArg f (axisCubeAffine_axisCubeAffineInv z hL x)
    rw [hfun] at hcomp
    exact hcomp
  · intro hf
    simpa only [Function.comp_apply] using!
      hf.comp_measurePreserving (measurePreserving_axisCubeAffine_originCube_neg_nat z L n)

/-- Bidirectional `MemLp` transport on the fixed centered depth-`n` source and
its target concentric contraction. -/
theorem memLp_axisCubeAffine_originCube_neg_nat_iff {d : ℕ}
    (z : Vec d) {L : ℝ} (hL : L ≠ 0) (n : ℕ)
    {E : Type*} [TopologicalSpace E] [ContinuousENorm E]
    (p : ℝ≥0∞) (f : Vec d → E) :
    MeasureTheory.MemLp (fun x => f (axisCubeAffine z L x)) p
        (normalizedCubeMeasure (originCube d (-(n : ℤ)))) ↔
      MeasureTheory.MemLp f p
        (axisCubeNormalizedMeasure (axisCubeConcentricDepthCorner z L n)
          (axisCubeConcentricDepthSide L n)) := by
  constructor
  · intro hf
    have hcomp := hf.comp_measurePreserving
      (measurePreserving_axisCubeAffineInv_originCube_neg_nat z hL n)
    have hfun : (fun x => f (axisCubeAffine z L x)) ∘ axisCubeAffineInv z L = f := by
      funext x
      exact congrArg f (axisCubeAffine_axisCubeAffineInv z hL x)
    rw [hfun] at hcomp
    exact hcomp
  · intro hf
    simpa only [Function.comp_apply] using!
      hf.comp_measurePreserving (measurePreserving_axisCubeAffine_originCube_neg_nat z L n)

/-- The affine parametrization preserves every extended `Lᵖ` norm when the
target axis cube carries `axisCubeNormalizedMeasure`. -/
theorem eLpNorm_axisCubeAffine {d : ℕ} (z : Vec d) (L : ℝ)
    {E : Type*} [TopologicalSpace E] [ContinuousENorm E]
    (p : ℝ≥0∞) (f : Vec d → E)
    (hf : MeasureTheory.AEStronglyMeasurable f (axisCubeNormalizedMeasure z L)) :
    MeasureTheory.eLpNorm (fun x => f (axisCubeAffine z L x)) p
        (MeasureTheory.volume.restrict (openCubeSet (originCube d 0))) =
      MeasureTheory.eLpNorm f p (axisCubeNormalizedMeasure z L) := by
  symm
  apply MeasureTheory.eLpNorm_map_measure hf
  exact (measurable_const_smul L).add measurable_const |>.aemeasurable

/-- Source-side measurability is also sufficient for exact affine norm
transport when the affine map is nondegenerate. -/
theorem eLpNorm_axisCubeAffine_of_comp_aestronglyMeasurable {d : ℕ}
    (z : Vec d) {L : ℝ} (hL : L ≠ 0)
    {E : Type*} [TopologicalSpace E] [ContinuousENorm E]
    (p : ℝ≥0∞) (f : Vec d → E)
    (hf : MeasureTheory.AEStronglyMeasurable
      (fun x => f (axisCubeAffine z L x))
      (MeasureTheory.volume.restrict (openCubeSet (originCube d 0)))) :
    MeasureTheory.eLpNorm (fun x => f (axisCubeAffine z L x)) p
        (MeasureTheory.volume.restrict (openCubeSet (originCube d 0))) =
      MeasureTheory.eLpNorm f p (axisCubeNormalizedMeasure z L) := by
  exact eLpNorm_axisCubeAffine z L p f
    ((aestronglyMeasurable_axisCubeAffine_iff z hL f).1 hf)

/-- Exact extended `Lᵖ` norm transport from the fixed centered depth-`n`
source cube to the corresponding target concentric contraction. -/
theorem eLpNorm_axisCubeAffine_originCube_neg_nat {d : ℕ}
    (z : Vec d) {L : ℝ} (hL : L ≠ 0) (n : ℕ)
    {E : Type*} [TopologicalSpace E] [ContinuousENorm E]
    (p : ℝ≥0∞) (f : Vec d → E)
    (hf : MeasureTheory.AEStronglyMeasurable
      (fun x => f (axisCubeAffine z L x))
      (normalizedCubeMeasure (originCube d (-(n : ℤ))))) :
    MeasureTheory.eLpNorm (fun x => f (axisCubeAffine z L x)) p
        (normalizedCubeMeasure (originCube d (-(n : ℤ)))) =
      MeasureTheory.eLpNorm f p
        (axisCubeNormalizedMeasure (axisCubeConcentricDepthCorner z L n)
          (axisCubeConcentricDepthSide L n)) := by
  have hftarget :=
    (aestronglyMeasurable_axisCubeAffine_originCube_neg_nat_iff z hL n f).1 hf
  simpa only [Function.comp_apply] using!
    MeasureTheory.eLpNorm_comp_measurePreserving hftarget
      (measurePreserving_axisCubeAffine_originCube_neg_nat z L n)

/-- `MemLp` on the fixed centered source supplies the measurability needed for
the exact depth-`n` norm identity. -/
theorem eLpNorm_axisCubeAffine_originCube_neg_nat_of_memLp {d : ℕ}
    (z : Vec d) {L : ℝ} (hL : L ≠ 0) (n : ℕ)
    {E : Type*} [TopologicalSpace E] [ContinuousENorm E]
    (p : ℝ≥0∞) (f : Vec d → E)
    (hf : MeasureTheory.MemLp (fun x => f (axisCubeAffine z L x)) p
      (normalizedCubeMeasure (originCube d (-(n : ℤ))))) :
    MeasureTheory.eLpNorm (fun x => f (axisCubeAffine z L x)) p
        (normalizedCubeMeasure (originCube d (-(n : ℤ)))) =
      MeasureTheory.eLpNorm f p
        (axisCubeNormalizedMeasure (axisCubeConcentricDepthCorner z L n)
          (axisCubeConcentricDepthSide L n)) :=
  eLpNorm_axisCubeAffine_originCube_neg_nat z hL n p f hf.aestronglyMeasurable

/-- The corresponding real-valued normalized `Lᵖ` norms are affine invariant. -/
theorem eLpNormToReal_axisCubeAffine {d : ℕ} (z : Vec d) (L : ℝ)
    {E : Type*} [TopologicalSpace E] [ContinuousENorm E]
    (p : ℝ≥0∞) (f : Vec d → E)
    (hf : MeasureTheory.AEStronglyMeasurable f (axisCubeNormalizedMeasure z L)) :
    (MeasureTheory.eLpNorm (fun x => f (axisCubeAffine z L x)) p
        (MeasureTheory.volume.restrict (openCubeSet (originCube d 0)))).toReal =
      (MeasureTheory.eLpNorm f p (axisCubeNormalizedMeasure z L)).toReal := by
  exact congrArg ENNReal.toReal (eLpNorm_axisCubeAffine z L p f hf)

@[simp] theorem axisCubeHarmonicPullback_grad {d : ℕ} (z : Vec d) {L : ℝ}
    (hL : 0 < L) (u : H1Function (axisCube z L)) (x : Vec d) :
    (axisCubeHarmonicPullback z hL u).grad x =
      u.grad (axisCubeAffine z L x) := by
  simp [axisCubeHarmonicPullback, axisCubeAffine, H1Function.undilateSet,
    H1Function.unscale, H1Function.untranslate, hL.ne', add_comm]

/-- The fixed-depth `MemLp` transport specialized to a pulled-back harmonic
gradient coordinate. -/
theorem memLp_axisCubeHarmonicPullback_grad_originCube_neg_nat_iff {d : ℕ}
    (z : Vec d) {L : ℝ} (hL : 0 < L) (u : H1Function (axisCube z L))
    (n : ℕ) (p : ℝ≥0∞) (i : Fin d) :
    MeasureTheory.MemLp
        (fun x => (axisCubeHarmonicPullback z hL u).grad x i) p
        (normalizedCubeMeasure (originCube d (-(n : ℤ)))) ↔
      MeasureTheory.MemLp (fun x => u.grad x i) p
        (axisCubeNormalizedMeasure (axisCubeConcentricDepthCorner z L n)
          (axisCubeConcentricDepthSide L n)) := by
  simpa only [axisCubeHarmonicPullback_grad] using
    (memLp_axisCubeAffine_originCube_neg_nat_iff z hL.ne' n p
      (fun x => u.grad x i))

/-- Exact fixed-depth norm transport specialized to a pulled-back harmonic
gradient coordinate. -/
theorem eLpNorm_axisCubeHarmonicPullback_grad_originCube_neg_nat {d : ℕ}
    (z : Vec d) {L : ℝ} (hL : 0 < L) (u : H1Function (axisCube z L))
    (n : ℕ) (p : ℝ≥0∞) (i : Fin d)
    (hmem : MeasureTheory.MemLp
      (fun x => (axisCubeHarmonicPullback z hL u).grad x i) p
      (normalizedCubeMeasure (originCube d (-(n : ℤ))))) :
    MeasureTheory.eLpNorm
        (fun x => (axisCubeHarmonicPullback z hL u).grad x i) p
        (normalizedCubeMeasure (originCube d (-(n : ℤ)))) =
      MeasureTheory.eLpNorm (fun x => u.grad x i) p
        (axisCubeNormalizedMeasure (axisCubeConcentricDepthCorner z L n)
          (axisCubeConcentricDepthSide L n)) := by
  have hmem' : MeasureTheory.MemLp
      (fun x => u.grad (axisCubeAffine z L x) i) p
      (normalizedCubeMeasure (originCube d (-(n : ℤ)))) := by
    simpa only [axisCubeHarmonicPullback_grad] using hmem
  simpa only [axisCubeHarmonicPullback_grad] using
    (eLpNorm_axisCubeAffine_originCube_neg_nat_of_memLp z hL.ne' n p
      (fun x => u.grad x i) hmem')

@[simp] theorem axisCubeHarmonicPullback_toFun {d : ℕ} (z : Vec d) {L : ℝ}
    (hL : 0 < L) (u : H1Function (axisCube z L)) (x : Vec d) :
    (axisCubeHarmonicPullback z hL u).toFun x =
      L⁻¹ * u.toFun (axisCubeAffine z L x) := by
  simp [axisCubeHarmonicPullback, axisCubeAffine, H1Function.undilateSet,
    H1Function.unscale, H1Function.untranslate, add_comm]

end CubeCalderonZygmund

end

end Homogenization
