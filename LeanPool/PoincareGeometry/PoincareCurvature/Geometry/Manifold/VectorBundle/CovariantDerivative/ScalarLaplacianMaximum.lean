/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Analysis.LocalExtremaSecondDerivative
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.ScalarLaplacian
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.ConnectionLaplacianChart
public import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique

/-!
# Scalar Laplacians at local extrema

This file begins the intrinsic maximum-principle bridge.  In particular, a
local minimum on a boundaryless manifold is proved to be a critical point;
this is not included as an assumption in later geometric arguments.
-/

@[expose] public noncomputable section
open Bundle FiberBundle Filter Topology
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E]
  [IsManifold I ∞ M] [I.Boundaryless]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]

namespace CovariantDerivative
local notation "TM" => (TangentSpace I : M → Type _)
local notation "T₁" => (fun x : M => TM x →L[ℝ] ℝ)

/-- Chain rule along a curve whose manifold derivative is the prescribed
velocity.  The explicit tangent-space conversion is necessary because the
real line is represented as a manifold codomain by `TangentSpace 𝓘(ℝ)` before
being read back as an ordinary real number. -/
theorem deriv_comp_of_hasMFDerivAt_velocity
    {f : M → ℝ} {X : ∀ y : M, TM y} {γ : ℝ → M} {t : ℝ}
    (hf : MDiffAt f (γ t))
    (hγ : HasMFDerivAt 𝓘(ℝ) I γ t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X (γ t)))) :
    deriv (f ∘ γ) t =
      scalarDifferential (I := I) f (γ t) (X (γ t)) := by
  have hcomp : HasMFDerivAt 𝓘(ℝ) 𝓘(ℝ) (f ∘ γ) t
      ((mfderiv I 𝓘(ℝ) f (γ t)).comp
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X (γ t)))) :=
    HasMFDerivAt.comp t hf.hasMFDerivAt hγ
  have hfrechet := hcomp.2
  simp only [mfld_simps, hasFDerivWithinAt_univ] at hfrechet
  have hd := HasFDerivAt.hasDerivAt (F := ℝ) hfrechet
  convert! hd.deriv using 1
  change (mfderiv I 𝓘(ℝ) f (γ t)) (X (γ t)) =
    (mfderiv I 𝓘(ℝ) f (γ t)) ((1 : ℝ) • X (γ t))
  rw [one_smul]

/-- Intrinsic first-order chain rule for scalar functions.  The tangent
direction is realized by the local integral curve of its canonical smooth
extension, so the identity does not depend on a coordinate representation. -/
theorem scalarDifferential_comp_of_hasDerivAt
    {F : ℝ → ℝ} {f : M → ℝ} {x : M} {d : ℝ}
    (hF : HasDerivAt F d (f x)) (hf : MDiffAt f x) (u : TM x) :
    scalarDifferential (I := I) (F ∘ f) x u =
      d * scalarDifferential (I := I) f x u := by
  let X : ∀ y : M, TM y :=
    smoothExtend (I := I) (F := E) (V := TM) x u
  have hXone : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (T% X) := by
    simpa [X] using smoothExtend_contMDiff_one
      (I := I) (F := E) (V := TM) x u
  obtain ⟨γ, hγzero, hγ⟩ :
      ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurveAt γ X 0 :=
    exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless
      (I := I) (v := X) (t₀ := 0) (x₀ := x) hXone.contMDiffAt
  have hfzero : MDiffAt f (γ 0) := by
    simpa only [hγzero] using hf
  have hcurve := HasMFDerivAt.comp 0 hfzero.hasMFDerivAt hγ.hasMFDerivAt
  have hcurveFrechet := hcurve.2
  simp only [mfld_simps, hasFDerivWithinAt_univ] at hcurveFrechet
  have hcurveDeriv := hcurveFrechet.hasDerivAt
  have hfcurveEq : deriv (f ∘ γ) 0 =
      scalarDifferential (I := I) f x u := by
    have h := deriv_comp_of_hasMFDerivAt_velocity
      (I := I) hfzero hγ.hasMFDerivAt
    rw [hγzero] at h
    simpa [X, smoothExtend_apply] using h
  have hfcurve : HasDerivAt (f ∘ γ)
      (scalarDifferential (I := I) f x u) 0 :=
    hcurveDeriv.congr_deriv (by
      rw [← hcurveDeriv.deriv]
      exact hfcurveEq)
  have hcomp : MDiffAt (F ∘ f) x :=
    hF.differentiableAt.comp_mdifferentiableAt hf
  have hcomp0 : MDiffAt (F ∘ f) (γ 0) := by
    simpa only [hγzero] using hcomp
  have hA := deriv_comp_of_hasMFDerivAt_velocity
    (I := I) hcomp0 hγ.hasMFDerivAt
  rw [hγzero] at hA
  have hA2 : deriv ((F ∘ f) ∘ γ) 0 =
      scalarDifferential (I := I) (F ∘ f) x u := by
    simpa [X, smoothExtend_apply] using hA
  have hF0 : HasDerivAt F d ((f ∘ γ) 0) := by
    simpa [Function.comp_apply, hγzero] using hF
  have hB0 := HasDerivAt.comp 0 hF0 hfcurve
  have hB : HasDerivAt ((F ∘ f) ∘ γ)
      (d * scalarDifferential (I := I) f x u) 0 := by
    simpa [Function.comp_assoc] using hB0
  calc
    scalarDifferential (I := I) (F ∘ f) x u =
        deriv ((F ∘ f) ∘ γ) 0 := hA2.symm
    _ = d * scalarDifferential (I := I) f x u := hB.deriv

/-- The intrinsic scalar-Hessian chain rule.  It is stated with local
regularity at the base point: the outer function is differentiable along the
inner function near `x`, and its first derivative is differentiable at
`f x`. -/
theorem scalarHessian_comp_apply_of_hasDerivAt_deriv
    (cov : CovariantDerivative I E TM) {F : ℝ → ℝ} {f : M → ℝ}
    {x : M} {d₂ : ℝ}
    (hFnear : ∀ᶠ y in 𝓝 x,
      HasDerivAt F (deriv F (f y)) (f y))
    (hfnear : ∀ᶠ y in 𝓝 x, MDiffAt f y)
    (hdf : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I) f y)) x)
    (hF₂ : HasDerivAt (deriv F) d₂ (f x))
    (hdfcomp : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I) (F ∘ f) y)) x)
    (u v : TM x) :
    scalarHessian cov (F ∘ f) x u v =
      deriv F (f x) * scalarHessian cov f x u v +
        d₂ * scalarDifferential (I := I) f x u *
          scalarDifferential (I := I) f x v := by
  have hf₀ : MDiffAt f x := hfnear.self_of_nhds
  let a : M → ℝ := deriv F ∘ f
  have ha : MDiffAt a x := hF₂.differentiableAt.comp_mdifferentiableAt hf₀
  have hchain : ∀ᶠ y in 𝓝 x,
      scalarDifferential (I := I) (F ∘ f) y =
        a y • scalarDifferential (I := I) f y := by
    filter_upwards [hFnear, hfnear] with y hFy hfy
    ext w
    simpa [a, Function.comp_apply, smul_eq_mul] using
      scalarDifferential_comp_of_hasDerivAt (I := I) hFy hfy w
  have hprod : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        ((a • scalarDifferential (I := I) f) y)) x := by
    simpa [a] using ha.smul_section hdf
  have hconn := IsCovariantDerivativeOn.congr_of_eventuallyEq
    (hcov := (covectorCovariantDerivative cov).isCovariantDerivativeOnUniv)
    hdfcomp hprod Filter.univ_mem hchain
  have hleibniz :=
    (covectorCovariantDerivative cov).isCovariantDerivativeOn.leibniz
      hdf ha (x := x)
  have hconnUV := congrArg (fun A : TM x →L[ℝ] T₁ x => A u v) hconn
  have hleibUV := congrArg (fun A : TM x →L[ℝ] T₁ x => A u v) hleibniz
  have hleibUV' :
      covectorCovariantDerivative cov (a • scalarDifferential (I := I) f) x u v =
        a x * scalarHessian cov f x u v +
          scalarDifferential (I := I) a x u *
            scalarDifferential (I := I) f x v := by
    simpa [scalarHessian, add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply, smul_eq_mul] using hleibUV
  have haValue : a x = deriv F (f x) := rfl
  have haDiff : scalarDifferential (I := I) a x u =
      d₂ * scalarDifferential (I := I) f x u := by
    simpa [a] using
      scalarDifferential_comp_of_hasDerivAt (I := I) hF₂ hf₀ u
  change covectorCovariantDerivative cov
      (scalarDifferential (I := I) (F ∘ f)) x u v = _
  rw [hconnUV, hleibUV', haValue, haDiff]

/-- The cotangent section of a scalar composition is differentiable at the
base point whenever the inner differential section is.  This is the
regularity bridge that lets the Hessian chain rule be applied without
postulating regularity of the composite differential as a separate input. -/
theorem mdifferentiableAt_scalarDifferential_comp_of_hasDerivAt_deriv
    {F : ℝ → ℝ} {f : M → ℝ} {x : M} {d₂ : ℝ}
    (hFnear : ∀ᶠ y in 𝓝 x,
      HasDerivAt F (deriv F (f y)) (f y))
    (hfnear : ∀ᶠ y in 𝓝 x, MDiffAt f y)
    (hdf : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I) f y)) x)
    (hF₂ : HasDerivAt (deriv F) d₂ (f x)) :
    MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I) (F ∘ f) y)) x := by
  have hf₀ : MDiffAt f x := hfnear.self_of_nhds
  let a : M → ℝ := deriv F ∘ f
  have ha : MDiffAt a x := hF₂.differentiableAt.comp_mdifferentiableAt hf₀
  have hchain : ∀ᶠ y in 𝓝 x,
      scalarDifferential (I := I) (F ∘ f) y =
        a y • scalarDifferential (I := I) f y := by
    filter_upwards [hFnear, hfnear] with y hFy hfy
    ext w
    simpa [a, Function.comp_apply, smul_eq_mul] using
      scalarDifferential_comp_of_hasDerivAt (I := I) hFy hfy w
  have hprod : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        ((a • scalarDifferential (I := I) f) y)) x := by
    simpa [a] using ha.smul_section hdf
  have hsections :
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I) (F ∘ f) y)) =ᶠ[𝓝 x]
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        ((a • scalarDifferential (I := I) f) y)) := by
    filter_upwards [hchain] with y hy
    rw [hy]
    simp
  exact hprod.congr_of_eventuallyEq hsections

/-- Tracing the intrinsic scalar-Hessian chain rule gives the Laplace--Beltrami
chain rule.  The gradient-square term is written as its orthonormal-frame
sum, with no coordinate Laplacian substituted for the geometric one. -/
theorem scalarLaplacian_comp_eq
    (cov : CovariantDerivative I E TM) {F : ℝ → ℝ} {f : M → ℝ}
    {x : M} {d₂ : ℝ}
    (hFnear : ∀ᶠ y in 𝓝 x,
      HasDerivAt F (deriv F (f y)) (f y))
    (hfnear : ∀ᶠ y in 𝓝 x, MDiffAt f y)
    (hdf : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I) f y)) x)
    (hF₂ : HasDerivAt (deriv F) d₂ (f x))
    (hdfcomp : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I) (F ∘ f) y)) x) :
    scalarLaplacian cov (F ∘ f) x =
      deriv F (f x) * scalarLaplacian cov f x +
        d₂ * ∑ i : Fin (Module.finrank ℝ (TM x)),
          (scalarDifferential (I := I) f x
            (stdOrthonormalBasis ℝ (TM x) i)) ^ 2 := by
  let _ : FiniteDimensional ℝ (TM x) :=
    VectorBundle.finiteDimensional ℝ E TM x
  let b := stdOrthonormalBasis ℝ (TM x)
  rw [scalarLaplacian_eq_sum_orthonormalBasis cov (F ∘ f) x b,
    scalarLaplacian_eq_sum_orthonormalBasis cov f x b]
  simp_rw [scalarHessian_comp_apply_of_hasDerivAt_deriv cov
    hFnear hfnear hdf hF₂ hdfcomp]
  rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  simp [b, pow_two, mul_assoc]

/-- The scalar Laplacian chain rule with the composite differential's
regularity discharged from the ordinary first-differential regularity. -/
theorem scalarLaplacian_comp_eq_of_hasDerivAt_deriv
    (cov : CovariantDerivative I E TM) {F : ℝ → ℝ} {f : M → ℝ}
    {x : M} {d₂ : ℝ}
    (hFnear : ∀ᶠ y in 𝓝 x,
      HasDerivAt F (deriv F (f y)) (f y))
    (hfnear : ∀ᶠ y in 𝓝 x, MDiffAt f y)
    (hdf : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I) f y)) x)
    (hF₂ : HasDerivAt (deriv F) d₂ (f x)) :
    scalarLaplacian cov (F ∘ f) x =
      deriv F (f x) * scalarLaplacian cov f x +
        d₂ * ∑ i : Fin (Module.finrank ℝ (TM x)),
          (scalarDifferential (I := I) f x
            (stdOrthonormalBasis ℝ (TM x) i)) ^ 2 := by
  exact scalarLaplacian_comp_eq cov hFnear hfnear hdf hF₂
    (mdifferentiableAt_scalarDifferential_comp_of_hasDerivAt_deriv
      hFnear hfnear hdf hF₂)

/-- A scalar function has zero intrinsic differential at a local minimum on
a boundaryless manifold. -/
theorem scalarDifferential_eq_zero_of_isLocalMin
    {f : M → ℝ} {x : M} (hmin : IsLocalMin f x) (hf : MDiffAt f x) :
    scalarDifferential (I := I) f x = 0 := by
  let φ := extChartAt I x
  let z := φ x
  have hxSource : x ∈ φ.source := by
    simpa [φ] using mem_extChartAt_source x
  have hzTarget : z ∈ φ.target := φ.map_source hxSource
  have hsymm : φ.symm z = x := φ.left_inv hxSource
  have hsymmCont : ContinuousAt φ.symm z := by
    simpa [φ, z] using continuousAt_extChartAt_symm (I := I) x
  have hchartMin :
      IsLocalMin (writtenInExtChartAt I 𝓘(ℝ) x f) z := by
    have hbase : IsLocalMin f (φ.symm z) := by simpa [hsymm] using hmin
    have hcomp := hbase.comp_continuous hsymmCont
    simpa [writtenInExtChartAt, φ, z, Function.comp_def,
      chartAt_self_eq] using hcomp
  have hchartCritical :
      fderiv ℝ (writtenInExtChartAt I 𝓘(ℝ) x f) z = 0 :=
    hchartMin.fderiv_eq_zero
  ext u
  let X : ∀ y : M, TM y :=
    smoothExtend (I := I) (F := E) (V := TM) x u
  calc
    scalarDifferential (I := I) f x u = mvfderiv (I := I) f x (X x) := by
      rw [scalarDifferential_apply, show X x = u by simp [X, smoothExtend_apply]]
    _ = fderivWithin ℝ (writtenInExtChartAt I 𝓘(ℝ) x f) (Set.range I) z
          (VectorField.mpullbackWithin 𝓘(ℝ, E) I φ.symm X
            (Set.range I) z) := by
      simpa [φ, z] using mvfderiv_apply_eq_fderivWithin_fixedChart
        (I := I) (g := f) (X := X) (p := x) (y := x) hxSource hf
    _ = 0 := by
      rw [I.range_eq_univ, fderivWithin_univ, hchartCritical]
      exact ContinuousLinearMap.zero_apply _

/-- Every diagonal value of the intrinsic scalar Hessian is nonnegative at a
local minimum.  The proof realizes the tangent vector by the local integral
curve of its canonical smooth extension and differentiates the scalar along
that actual manifold curve twice. -/
theorem scalarHessian_self_nonneg_of_isLocalMin
    (cov : CovariantDerivative I E TM) {f : M → ℝ} {x : M}
    (hmin : IsLocalMin f x)
    (hfNear : ∀ᶠ y in 𝓝 x, MDiffAt f y)
    (hdf : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I) f y)) x)
    (u : TM x) :
    0 ≤ scalarHessian cov f x u u := by
  let X : ∀ y : M, TM y :=
    smoothExtend (I := I) (F := E) (V := TM) x u
  have hXone : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (T% X) := by
    simpa [X] using
      smoothExtend_contMDiff_one (I := I) (F := E) (V := TM) x u
  obtain ⟨γ, hγzero, hγ⟩ :=
    exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless
      (I := I) (v := X) (t₀ := 0) (x₀ := x) hXone.contMDiffAt
  have hlineMin : IsLocalMin (f ∘ γ) 0 := by
    have hbase : IsLocalMin f (γ 0) := by simpa only [hγzero] using hmin
    exact hbase.comp_continuous hγ.continuousAt
  have hfx : MDiffAt f x := hfNear.self_of_nhds
  have hlineCont : ContinuousAt (f ∘ γ) 0 := by
    have hfxzero : MDiffAt f (γ 0) := by simpa only [hγzero] using hfx
    exact hfxzero.continuousAt.comp hγ.continuousAt
  have hsecond : 0 ≤ deriv (deriv (f ∘ γ)) 0 :=
    hlineMin.deriv_deriv_nonneg hlineCont
  let g : M → ℝ := fun y =>
    scalarDifferential (I := I) f y (X y)
  have hγtend : Tendsto γ (𝓝 0) (𝓝 x) := by
    rw [← hγzero]
    exact hγ.continuousAt
  have hfCurve : ∀ᶠ s in 𝓝 0, MDiffAt f (γ s) :=
    hγtend.eventually hfNear
  have hfirstEq : deriv (f ∘ γ) =ᶠ[𝓝 0] g ∘ γ := by
    filter_upwards [hγ, hfCurve] with s hγs hfs
    simpa [g] using
      deriv_comp_of_hasMFDerivAt_velocity (I := I) hfs hγs
  have hXmd : MDiffAt (T% X) x :=
    (hXone x).mdifferentiableAt one_ne_zero
  have hgTotal := hdf.clm_bundle_apply hXmd
  have hg : MDiffAt g x := by
    have ht :=
      ((trivializationAt ℝ (Bundle.Trivial M ℝ) x).mdifferentiableAt_section_iff
        I g (FiberBundle.mem_baseSet_trivializationAt' x)).mp hgTotal
    simpa [Bundle.Trivial.eq_trivialization M ℝ] using ht
  have hcritical : scalarDifferential (I := I) f x = 0 :=
    scalarDifferential_eq_zero_of_isLocalMin hmin hfx
  have hsecondEq :
      deriv (deriv (f ∘ γ)) 0 = deriv (g ∘ γ) 0 :=
    Filter.EventuallyEq.deriv_eq hfirstEq
  have hgCurve : deriv (g ∘ γ) 0 = mvfderiv (I := I) g x u := by
    have hgzero : MDiffAt g (γ 0) := by simpa only [hγzero] using hg
    have h :=
      deriv_comp_of_hasMFDerivAt_velocity (I := I) hgzero hγ.hasMFDerivAt
    rw [hγzero] at h
    simpa [g, X, smoothExtend_apply] using h
  rw [scalarHessian_apply_of_mdifferentiableAt_of_differential_eq_zero
    cov f hdf hcritical u u]
  change 0 ≤ mvfderiv (I := I) g x u
  rw [← hgCurve, ← hsecondEq]
  exact hsecond

/-- The intrinsic scalar Laplacian is nonnegative at a local minimum. -/
theorem scalarLaplacian_nonneg_of_isLocalMin
    (cov : CovariantDerivative I E TM) {f : M → ℝ} {x : M}
    (hmin : IsLocalMin f x)
    (hfNear : ∀ᶠ y in 𝓝 x, MDiffAt f y)
    (hdf : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I) f y)) x) :
    0 ≤ scalarLaplacian cov f x := by
  let _ : FiniteDimensional ℝ (TM x) :=
    VectorBundle.finiteDimensional ℝ E TM x
  rw [scalarLaplacian_eq_sum_orthonormalBasis cov f x
    (stdOrthonormalBasis ℝ (TM x))]
  exact Finset.sum_nonneg fun i _ =>
    scalarHessian_self_nonneg_of_isLocalMin cov hmin hfNear hdf
      ((stdOrthonormalBasis ℝ (TM x)) i)

end CovariantDerivative
