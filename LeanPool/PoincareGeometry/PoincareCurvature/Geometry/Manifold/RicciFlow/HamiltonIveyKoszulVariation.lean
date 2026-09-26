/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/
module


/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.HamiltonIveyConnectionVariation
public import LeanPool.PoincareGeometry.PoincareCurvature.Analysis.MatrixInverseDerivative
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Bianchi
public import Mathlib.Analysis.InnerProductSpace.GramMatrix

/-!
# Differentiating the Levi-Civita Koszul identity

This file turns the static Koszul formula into a time-variation identity. It
keeps the mixed regularity needed to interchange a time derivative with a
spatial directional derivative explicit; slicewise smoothness alone does not
silently supply that interchange.
-/

@[expose] public section

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace CovariantDerivative.TimeDependentRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M]
  [IsManifold I (minSmoothness ℝ 3) M]
  [IsManifold I ((2 : ℕ∞) + 1) M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]

local notation "TM" => (TangentSpace I : M → Type _)

/-- The pointwise metric-derivative data already used by Ricci flow extend to
a moving vector argument. The proof is finite-dimensional: expand the moving
vector in an orthonormal basis for the metric at the evaluation time, then use
the scalar product rule on each coefficient/metric-component product. -/
theorem hasDerivAt_metricInner_left_of_pairwise_derivative
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (hdot : ∀ x : M, TM x →ₗ[ℝ] TM x →ₗ[ℝ] ℝ)
    {t : ℝ}
    (hmetric : ∀ (x : M) (u v : TM x),
      HasDerivAt (fun τ : ℝ => (g τ).inner x u v) (hdot x u v) t)
    (x : M) (σ : ℝ → TM x) (σdot v : TM x)
    (hσ : HasDerivAt (fun τ : ℝ => σ τ) σdot t) :
    HasDerivAt (fun τ : ℝ => (g τ).inner x (σ τ) v)
      (hdot x (σ t) v + (g t).inner x σdot v) t := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  let _ : FiniteDimensional ℝ (TM x) :=
    VectorBundle.finiteDimensional ℝ E (TangentSpace I : M → Type _) x
  let b : OrthonormalBasis (Fin (Module.finrank ℝ (TM x))) ℝ (TM x) :=
    stdOrthonormalBasis ℝ (TM x)
  let coeff : ℝ → Fin (Module.finrank ℝ (TM x)) → ℝ :=
    fun τ i => Inner.inner ℝ (b i) (σ τ)
  let metricComponent : ℝ → Fin (Module.finrank ℝ (TM x)) → ℝ :=
    fun τ i => (g τ).inner x (b i) v
  have hcoeff (i : Fin (Module.finrank ℝ (TM x))) :
      HasDerivAt (fun τ : ℝ => coeff τ i)
        (Inner.inner ℝ (b i) σdot) t := by
    have hb : HasDerivAt (fun _ : ℝ => b i) 0 t :=
      hasDerivAt_const (x := t) (c := b i)
    simpa [coeff] using
      (HasDerivAt.inner (𝕜 := ℝ) (E := TM x) hb hσ)
  have hcomponent (i : Fin (Module.finrank ℝ (TM x))) :
      HasDerivAt (fun τ : ℝ => metricComponent τ i)
        (hdot x (b i) v) t := by
    exact hmetric x (b i) v
  have hterm (i : Fin (Module.finrank ℝ (TM x))) :
      HasDerivAt
        (fun τ : ℝ => coeff τ i * metricComponent τ i)
        (Inner.inner ℝ (b i) σdot * metricComponent t i +
          coeff t i * hdot x (b i) v) t := by
    convert (hcoeff i).mul (hcomponent i) using 1 <;> rfl
  have hsum := HasDerivAt.sum (u := Finset.univ)
    (fun i (_hi : i ∈ Finset.univ) => hterm i)
  have hsumFun :
      (∑ i, fun τ : ℝ => coeff τ i * metricComponent τ i) =
        (fun τ : ℝ => ∑ i, coeff τ i * metricComponent τ i) := by
    funext τ
    simp
  rw [hsumFun] at hsum
  have hmetricExpand (w : TM x) :
      (g t).inner x w v =
        ∑ i, Inner.inner ℝ (b i) w * (g t).inner x (b i) v := by
    calc
      (g t).inner x w v =
          (g t).inner x (∑ i, Inner.inner ℝ (b i) w • b i) v := by
            exact congrArg (fun z : TM x => (g t).inner x z v)
              (b.sum_repr' w).symm
      _ = _ := by
        simp [map_sum, smul_eq_mul]
  have hdotExpand (w : TM x) :
      hdot x w v =
        ∑ i, Inner.inner ℝ (b i) w * hdot x (b i) v := by
    calc
      hdot x w v =
          hdot x (∑ i, Inner.inner ℝ (b i) w • b i) v := by
            exact congrArg (fun z : TM x => hdot x z v)
              (b.sum_repr' w).symm
      _ = _ := by
        simp [map_sum, smul_eq_mul]
  have hderivSum :
      (∑ i, (Inner.inner ℝ (b i) σdot * metricComponent t i +
          coeff t i * hdot x (b i) v)) =
        hdot x (σ t) v + (g t).inner x σdot v := by
    rw [Finset.sum_add_distrib]
    rw [← hmetricExpand σdot, ← hdotExpand (σ t)]
    exact add_comm _ _
  have hexpand (τ : ℝ) :
      (g τ).inner x (σ τ) v =
        ∑ i, coeff τ i * metricComponent τ i := by
    calc
      (g τ).inner x (σ τ) v =
          (g τ).inner x
            (∑ i, Inner.inner ℝ (b i) (σ τ) • b i) v := by
              exact congrArg (fun z : TM x => (g τ).inner x z v)
                (b.sum_repr' (σ τ)).symm
      _ = _ := by simp [coeff, metricComponent, map_sum, smul_eq_mul]
  have hfun :
      (fun τ : ℝ => (g τ).inner x (σ τ) v) =
        (fun τ : ℝ => ∑ i, coeff τ i * metricComponent τ i) := by
    funext τ
    exact hexpand τ
  rw [hfun]
  exact hsum.congr_deriv hderivSum
/-- Pairing with every fixed vector detects a time derivative of a moving
vector, even though the positive-definite metric used in the pairing also
varies. The proof writes the metric matrix in an orthonormal basis at the
evaluation time, differentiates its inverse, and then reconstructs the vector
derivative from its basis coefficients. -/
theorem hasDerivAt_vector_of_metric_pairings
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (hdot : ∀ x : M, TM x →ₗ[ℝ] TM x →ₗ[ℝ] ℝ)
    {t : ℝ}
    (hmetric : ∀ (x : M) (u v : TM x),
      HasDerivAt (fun τ : ℝ => (g τ).inner x u v) (hdot x u v) t)
    (x : M) (σ : ℝ → TM x) (σdot : TM x)
    (hpair : ∀ v : TM x,
      HasDerivAt (fun τ : ℝ => (g τ).inner x v (σ τ))
        (hdot x v (σ t) + (g t).inner x v σdot) t) :
    HasDerivAt (fun τ : ℝ => σ τ) σdot t := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  let _ : FiniteDimensional ℝ (TM x) :=
    VectorBundle.finiteDimensional ℝ E (TangentSpace I : M → Type _) x
  let n : ℕ := Module.finrank ℝ (TM x)
  let b : OrthonormalBasis (Fin n) ℝ (TM x) := stdOrthonormalBasis ℝ (TM x)
  let coeff : ℝ → Fin n → ℝ := fun τ i => Inner.inner ℝ (b i) (σ τ)
  let pairing : ℝ → Fin n → ℝ := fun τ i => (g τ).inner x (b i) (σ τ)
  have hinner_t (u v : TM x) : (g t).inner x u v = Inner.inner ℝ u v := rfl
  let gram : ℝ → Matrix (Fin n) (Fin n) ℝ :=
    fun τ i j => (g τ).inner x (b i) (b j)
  let gramDot : Matrix (Fin n) (Fin n) ℝ := fun i j => hdot x (b i) (b j)
  have hbLinear : LinearIndependent ℝ (fun i : Fin n => b i) := by
    simpa using b.toBasis.linearIndependent
  have hgramDet (τ : ℝ) : (gram τ).det ≠ 0 := by
    letI : RiemannianBundle TM := ⟨(g τ).toRiemannianMetric⟩
    have hgram : gram τ = Matrix.gram ℝ (fun i : Fin n => b i) := by
      ext i j
      rfl
    rw [hgram]
    exact Matrix.det_gram_ne_zero_iff_linearIndependent.mpr hbLinear
  have hgramAt : gram t = 1 := by
    ext i j
    simpa [gram, Matrix.one_apply, hinner_t] using
      (orthonormal_iff_ite.mp b.orthonormal i j)
  have hgramEntry (i j : Fin n) :
      HasDerivAt (fun τ : ℝ => gram τ i j) (gramDot i j) t := by
    exact hmetric x (b i) (b j)
  have hinvEntry (i j : Fin n) :
      HasDerivAt (fun τ : ℝ => (gram τ)⁻¹ i j)
        (-((gram t)⁻¹ * gramDot * (gram t)⁻¹) i j) t := by
    exact PoincareCurvature.hasDerivAt_nonsing_inv_entry
      (A := gram) (Adot := gramDot) hgramEntry hgramDet i j
  have hpairEntry (i : Fin n) :
      HasDerivAt (fun τ : ℝ => pairing τ i)
        (hdot x (b i) (σ t) + (g t).inner x (b i) σdot) t := by
    exact hpair (b i)
  have hpairExpand (τ : ℝ) : pairing τ = (gram τ).mulVec (coeff τ) := by
    ext i
    have hcoeff : (∑ j : Fin n, coeff τ j • b j) = σ τ := by
      simpa [coeff] using b.sum_repr' (σ τ)
    change (g τ).inner x (b i) (σ τ) = _
    rw [← hcoeff]
    simp [Matrix.mulVec, dotProduct, pairing, gram, coeff, map_sum,
      inner_smul_right, smul_eq_mul, mul_comm]
  have hcoeffInv (τ : ℝ) : (gram τ)⁻¹.mulVec (pairing τ) = coeff τ := by
    letI : Invertible (gram τ) := Matrix.invertibleOfIsUnitDet (gram τ)
      (isUnit_iff_ne_zero.mpr (hgramDet τ))
    exact Matrix.inv_mulVec_eq_vec (hpairExpand τ)
  have hproduct (i j : Fin n) :
      HasDerivAt
        (fun τ : ℝ => (gram τ)⁻¹ i j * pairing τ j)
        (-((gram t)⁻¹ * gramDot * (gram t)⁻¹) i j * pairing t j +
          (gram t)⁻¹ i j *
            (hdot x (b j) (σ t) + (g t).inner x (b j) σdot)) t := by
    exact (hinvEntry i j).mul (hpairEntry j)
  have hcoeffInvDeriv (i : Fin n) :
      HasDerivAt
        (fun τ : ℝ => (gram τ)⁻¹.mulVec (pairing τ) i)
        (∑ j : Fin n, (
          -((gram t)⁻¹ * gramDot * (gram t)⁻¹) i j * pairing t j +
            (gram t)⁻¹ i j *
              (hdot x (b j) (σ t) + (g t).inner x (b j) σdot))) t := by
    have hsum := HasDerivAt.fun_sum (u := Finset.univ)
      (fun j (_hj : j ∈ Finset.univ) => hproduct i j)
    simpa [Matrix.mulVec, dotProduct] using hsum
  have hcoeffDeriv (i : Fin n) :
      HasDerivAt (fun τ : ℝ => coeff τ i)
        (∑ j : Fin n, (
          -((gram t)⁻¹ * gramDot * (gram t)⁻¹) i j * pairing t j +
            (gram t)⁻¹ i j *
              (hdot x (b j) (σ t) + (g t).inner x (b j) σdot))) t := by
    have hfun : (fun τ : ℝ => coeff τ i) =
        (fun τ => (gram τ)⁻¹.mulVec (pairing τ) i) := by
      funext τ
      exact congrFun (hcoeffInv τ).symm i
    rw [hfun]
    exact hcoeffInvDeriv i
  have hhdotExpand (i : Fin n) :
      hdot x (b i) (σ t) =
        ∑ j : Fin n, gramDot i j * pairing t j := by
    have hrepr : (∑ j : Fin n, pairing t j • b j) = σ t := by
      simpa [pairing, hinner_t] using b.sum_repr' (σ t)
    calc
      hdot x (b i) (σ t) =
          hdot x (b i) (∑ j : Fin n, pairing t j • b j) := by rw [hrepr]
      _ = ∑ j : Fin n, pairing t j * hdot x (b i) (b j) := by
        simp [map_sum, smul_eq_mul]
      _ = ∑ j : Fin n, gramDot i j * pairing t j := by
        apply Finset.sum_congr rfl
        intro j hj
        simp [gramDot, mul_comm]
  have hsumNegative (i : Fin n) :
      (∑ j : Fin n, -gramDot i j * pairing t j) =
        -(∑ j : Fin n, gramDot i j * pairing t j) := by
    calc
      (∑ j : Fin n, -gramDot i j * pairing t j) =
          ∑ j : Fin n, -(gramDot i j * pairing t j) := by
            apply Finset.sum_congr rfl
            intro j hj
            ring
      _ = -(∑ j : Fin n, gramDot i j * pairing t j) := by
            rw [Finset.sum_neg_distrib]
  have hsumDiagonal (i : Fin n) :
      (∑ j : Fin n,
        (if i = j then 1 else 0) *
          (hdot x (b j) (σ t) + (g t).inner x (b j) σdot)) =
        hdot x (b i) (σ t) + (g t).inner x (b i) σdot := by
    classical
    simp
  have hcoeffDerivativeValue (i : Fin n) :
      (∑ j : Fin n, (
          -((gram t)⁻¹ * gramDot * (gram t)⁻¹) i j * pairing t j +
            (gram t)⁻¹ i j *
              (hdot x (b j) (σ t) + (g t).inner x (b j) σdot))) =
        Inner.inner ℝ (b i) σdot := by
    rw [hgramAt]
    simp only [inv_one, one_mul, mul_one]
    calc
      (∑ j : Fin n, (
          -gramDot i j * pairing t j +
            (1 : Matrix (Fin n) (Fin n) ℝ) i j *
              (hdot x (b j) (σ t) + (g t).inner x (b j) σdot))) =
          (∑ j : Fin n, -gramDot i j * pairing t j) +
            (∑ j : Fin n,
              (if i = j then 1 else 0) *
                (hdot x (b j) (σ t) + (g t).inner x (b j) σdot)) := by
        rw [Finset.sum_add_distrib]
        congr 1
      _ = -(∑ j : Fin n, gramDot i j * pairing t j) +
            (hdot x (b i) (σ t) + (g t).inner x (b i) σdot) := by
        rw [hsumNegative, hsumDiagonal]
      _ = Inner.inner ℝ (b i) σdot := by
        rw [← hhdotExpand i, hinner_t]
        ring
  have hcoeffDeriv' (i : Fin n) :
      HasDerivAt (fun τ : ℝ => coeff τ i) (Inner.inner ℝ (b i) σdot) t := by
    exact (hcoeffDeriv i).congr_deriv (hcoeffDerivativeValue i)
  have hsum : HasDerivAt
      (fun τ : ℝ => ∑ i : Fin n, coeff τ i • b i)
      (∑ i : Fin n, Inner.inner ℝ (b i) σdot • b i) t := by
    exact HasDerivAt.fun_sum (u := Finset.univ)
      (fun i (_hi : i ∈ Finset.univ) => (hcoeffDeriv' i).smul_const (b i))
  have hsumValue (τ : ℝ) : (∑ i : Fin n, coeff τ i • b i) = σ τ := by
    simpa [coeff] using b.sum_repr' (σ τ)
  have hsumVelocity : (∑ i : Fin n, Inner.inner ℝ (b i) σdot • b i) = σdot :=
    b.sum_repr' σdot
  have hfunction : (fun τ : ℝ => ∑ i : Fin n, coeff τ i • b i) = σ :=
    funext hsumValue
  rw [hfunction, hsumVelocity] at hsum
  exact hsum

/-- The covariant derivative of a time-velocity bilinear field, evaluated on
spatial vector fields. This is the expanded tensor-connection formula
`(∇_X h)(Y,Z) = X(h(Y,Z)) - h(∇_X Y,Z) - h(Y,∇_X Z)`. -/
def metricVelocityCovariantDerivativeAlong
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E)
      (V := (TangentSpace I : M → Type _)))
    (hdot : ∀ x : M, TM x →ₗ[ℝ] TM x →ₗ[ℝ] ℝ)
    (t : ℝ) (X Y Z : Π x : M, TM x) (x : M) : ℝ :=
  mvfderiv (I := I) (fun y ↦ hdot y (Y y) (Z y)) x (X x) -
    hdot x ((cov t).along X Y x) (Z x) -
    hdot x (Y x) ((cov t).along X Z x)

/-- The expanded covariant derivative is linear in the bilinear tensor being
differentiated. This makes the Ricci-flow substitution `hdot = -2 Ric` an
explicit scalar factor, once the spatial Ricci contraction is differentiable. -/
theorem metricVelocityCovariantDerivativeAlong_smul
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E)
      (V := (TangentSpace I : M → Type _)))
    (h : ∀ x : M, TM x →ₗ[ℝ] TM x →ₗ[ℝ] ℝ)
    (c t : ℝ) (X Y Z : Π x : M, TM x) (x : M)
    (hh : MDiffAt (fun y ↦ h y (Y y) (Z y)) x) :
    metricVelocityCovariantDerivativeAlong
        (I := I) (M := M) cov (fun y ↦ c • h y) t X Y Z x =
      c * metricVelocityCovariantDerivativeAlong
        (I := I) (M := M) cov h t X Y Z x := by
  have hc : MDiffAt (fun _ : M => c) x := mdifferentiableAt_const
  have hmvf := congrArg (fun L => L (X x))
    (mvfderiv_smul (I := I) hc hh)
  have hcderiv : mvfderiv (I := I) (fun _ : M => c) x = 0 := by
    rw [mvfderiv_const]
  let f : M → ℝ := fun y => h y (Y y) (Z y)
  have hfun :
      (fun y : M => (fun _ : M => c) y * f y) =
        (fun y : M => c * f y) := by
    funext y
    rfl
  have hmvfClean :
      mvfderiv (I := I) ((fun _ : M => c) • f) x (X x) =
        c * mvfderiv (I := I) f x (X x) := by
    rw [hcderiv] at hmvf
    simpa [smul_eq_mul] using hmvf
  have htransport := congrArg
    (fun q : M → ℝ => mvfderiv (I := I) q x (X x)) hfun
  have hmvfScalar :
      mvfderiv (I := I) (fun y : M => c * f y) x (X x) =
        c * mvfderiv (I := I) f x (X x) := by
    exact htransport.symm.trans hmvfClean
  have hscalarFun :
      (fun y : M => (c • h y) (Y y) (Z y)) =
        (fun y : M => c * h y (Y y) (Z y)) := by
    funext y
    simp [LinearMap.smul_apply, smul_eq_mul]
  have hmvf' :
      mvfderiv (I := I) (fun y ↦ (c • h y) (Y y) (Z y)) x (X x) =
        c * mvfderiv (I := I) (fun y ↦ h y (Y y) (Z y)) x (X x) := by
    exact (congrArg
      (fun q : M → ℝ => mvfderiv (I := I) q x (X x)) hscalarFun).trans hmvfScalar
  dsimp [metricVelocityCovariantDerivativeAlong]
  rw [← hscalarFun]
  rw [hmvf']
  ring

/-- The scalar right-hand side of the Koszul identity for a metric family. -/
def metricKoszulExpression
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (τ : ℝ) (X Y Z : Π x : M, TM x) (x : M) : ℝ :=
  mvfderiv (I := I) (fun y ↦ (g τ).inner y (Y y) (Z y)) x (X x) +
  mvfderiv (I := I) (fun y ↦ (g τ).inner y (X y) (Z y)) x (Y x) -
  mvfderiv (I := I) (fun y ↦ (g τ).inner y (X y) (Y y)) x (Z x) -
  (g τ).inner x (X x) (VectorField.mlieBracket I Y Z x) +
  (g τ).inner x (Y x) (VectorField.mlieBracket I Z X x) +
  (g τ).inner x (Z x) (VectorField.mlieBracket I X Y x)

/-- The metric-velocity right-hand side obtained by formally differentiating
the preceding Koszul expression. -/
def metricVelocityKoszulExpression
    (hdot : ∀ x : M, TM x →ₗ[ℝ] TM x →ₗ[ℝ] ℝ)
    (X Y Z : Π x : M, TM x) (x : M) : ℝ :=
  mvfderiv (I := I) (fun y ↦ hdot y (Y y) (Z y)) x (X x) +
  mvfderiv (I := I) (fun y ↦ hdot y (X y) (Z y)) x (Y x) -
  mvfderiv (I := I) (fun y ↦ hdot y (X y) (Y y)) x (Z x) -
  hdot x (X x) (VectorField.mlieBracket I Y Z x) +
  hdot x (Y x) (VectorField.mlieBracket I Z X x) +
  hdot x (Z x) (VectorField.mlieBracket I X Y x)

/-- Algebraically, the differentiated Koszul right-hand side is the metric
velocity paired with `∇_X Y`, plus the cyclic covariant derivative of the
metric velocity. This identity uses only symmetry of `hdot` and the actual
torsion-free property of the Levi-Civita slice. -/
theorem metricVelocityKoszulExpression_eq_cyclicCovariantDerivative
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E)
      (V := (TangentSpace I : M → Type _)))
    (hLevi : g.IsLeviCivita cov)
    (hcov : ∀ τ : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E)
      (V := (TangentSpace I : M → Type _)) (cov τ) 1)
    (hdot : ∀ x : M, TM x →ₗ[ℝ] TM x →ₗ[ℝ] ℝ)
    (hdotSymm : ∀ (x : M) (u v : TM x), hdot x u v = hdot x v u)
    (t : ℝ) {X Y Z : Π y : M, TM y} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun y ↦ TotalSpace.mk' E y (X y)))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun y ↦ TotalSpace.mk' E y (Y y)))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun y ↦ TotalSpace.mk' E y (Z y))) :
    metricVelocityKoszulExpression (I := I) (M := M) hdot X Y Z x =
      2 * hdot x ((cov t).along X Y x) (Z x) +
        metricVelocityCovariantDerivativeAlong
          (I := I) (M := M) cov hdot t X Y Z x +
        metricVelocityCovariantDerivativeAlong
          (I := I) (M := M) cov hdot t Y X Z x -
      metricVelocityCovariantDerivativeAlong
          (I := I) (M := M) cov hdot t Z X Y x := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : ContMDiffCovariantDerivative (cov t) 1 := hcov t
  have hbracketYZ : VectorField.mlieBracket I Y Z x =
      (cov t).along Y Z x - (cov t).along Z Y x := by
    exact (congrFun
      (CovariantDerivative.along_sub_eq_mlieBracket_of_torsion_eq_zero
        (cov := cov t) (hLevi t).1 hY hZ) x).symm
  have hbracketZX : VectorField.mlieBracket I Z X x =
      (cov t).along Z X x - (cov t).along X Z x := by
    exact (congrFun
      (CovariantDerivative.along_sub_eq_mlieBracket_of_torsion_eq_zero
        (cov := cov t) (hLevi t).1 hZ hX) x).symm
  have hbracketXY : VectorField.mlieBracket I X Y x =
      (cov t).along X Y x - (cov t).along Y X x := by
    exact (congrFun
      (CovariantDerivative.along_sub_eq_mlieBracket_of_torsion_eq_zero
        (cov := cov t) (hLevi t).1 hX hY) x).symm
  dsimp [metricVelocityKoszulExpression,
    metricVelocityCovariantDerivativeAlong]
  rw [hbracketYZ, hbracketZX, hbracketXY]
  simp only [LinearMap.map_sub]
  have hswapZX :
      hdot x (Y x) ((cov t).along Z X x) =
        hdot x ((cov t).along Z X x) (Y x) :=
    hdotSymm x (Y x) ((cov t).along Z X x)
  have hsymXY := hdotSymm x (Z x) ((cov t).along X Y x)
  have hsymYX := hdotSymm x (Z x) ((cov t).along Y X x)
  simp only [CovariantDerivative.along] at hsymXY hsymYX hswapZX
  simp only [CovariantDerivative.along]
  rw [hsymXY, hsymYX, hswapZX]
  ring_nf

/-- Pairwise mixed-derivative data differentiate the full scalar Koszul
expression. This isolates the time/space commutations without assuming any
time derivative of the connection. -/
theorem hasDerivAt_metricKoszulExpression
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (hdot : ∀ x : M, TM x →ₗ[ℝ] TM x →ₗ[ℝ] ℝ)
    {t : ℝ}
    (hmetric : ∀ (x : M) (u v : TM x),
      HasDerivAt (fun τ : ℝ => (g τ).inner x u v) (hdot x u v) t)
    {X Y Z : Π x : M, TM x} {x : M}
    (hmixedXYZ : HasDerivAt
      (fun τ : ℝ =>
        mvfderiv (I := I) (fun y ↦ (g τ).inner y (Y y) (Z y)) x (X x))
      (mvfderiv (I := I) (fun y ↦ hdot y (Y y) (Z y)) x (X x)) t)
    (hmixedYXZ : HasDerivAt
      (fun τ : ℝ =>
        mvfderiv (I := I) (fun y ↦ (g τ).inner y (X y) (Z y)) x (Y x))
      (mvfderiv (I := I) (fun y ↦ hdot y (X y) (Z y)) x (Y x)) t)
    (hmixedZXY : HasDerivAt
      (fun τ : ℝ =>
        mvfderiv (I := I) (fun y ↦ (g τ).inner y (X y) (Y y)) x (Z x))
      (mvfderiv (I := I) (fun y ↦ hdot y (X y) (Y y)) x (Z x)) t) :
    HasDerivAt (fun τ => metricKoszulExpression (I := I) (M := M)
      g τ X Y Z x)
      (metricVelocityKoszulExpression (I := I) (M := M)
        hdot X Y Z x) t := by
  have hbracketXYZ := hmetric x (X x) (VectorField.mlieBracket I Y Z x)
  have hbracketZXY := hmetric x (Y x) (VectorField.mlieBracket I Z X x)
  have hbracketXYZ' := hmetric x (Z x) (VectorField.mlieBracket I X Y x)
  let f₁ : ℝ → ℝ := fun τ =>
    mvfderiv (I := I) (fun y ↦ (g τ).inner y (Y y) (Z y)) x (X x)
  let f₂ : ℝ → ℝ := fun τ =>
    mvfderiv (I := I) (fun y ↦ (g τ).inner y (X y) (Z y)) x (Y x)
  let f₃ : ℝ → ℝ := fun τ =>
    mvfderiv (I := I) (fun y ↦ (g τ).inner y (X y) (Y y)) x (Z x)
  let f₄ : ℝ → ℝ := fun τ =>
    (g τ).inner x (X x) (VectorField.mlieBracket I Y Z x)
  let f₅ : ℝ → ℝ := fun τ =>
    (g τ).inner x (Y x) (VectorField.mlieBracket I Z X x)
  let f₆ : ℝ → ℝ := fun τ =>
    (g τ).inner x (Z x) (VectorField.mlieBracket I X Y x)
  have hsum :=
    (((((hmixedXYZ.add hmixedYXZ).sub hmixedZXY).sub hbracketXYZ).add
      hbracketZXY).add hbracketXYZ')
  have hsumFun :
      (((((f₁ + f₂) - f₃) - f₄) + f₅) + f₆) =
        (fun τ => metricKoszulExpression (I := I) (M := M) g τ X Y Z x) := by
    funext τ
    simp [f₁, f₂, f₃, f₄, f₅, f₆, metricKoszulExpression]
  change HasDerivAt (((((f₁ + f₂) - f₃) - f₄) + f₅) + f₆)
      (metricVelocityKoszulExpression (I := I) (M := M) hdot X Y Z x) t at hsum
  rw [hsumFun] at hsum
  simpa [metricVelocityKoszulExpression] using hsum

/-- Differentiating the actual slicewise Koszul identity gives the derivative
of the metric pairing with the time-dependent connection. Unlike the later
vector-valued connection-variation theorem, this scalar pairing step does not
assume `HasConnectionTimeVariationAt`. -/
theorem hasDerivAt_metricConnectionPairing_of_koszulExpression
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E)
      (V := (TangentSpace I : M → Type _)))
    (hcov : ∀ τ : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E)
      (V := (TangentSpace I : M → Type _)) (cov τ) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdot : ∀ x : M, TM x →ₗ[ℝ] TM x →ₗ[ℝ] ℝ)
    {t : ℝ}
    {X Y Z : Π x : M, TM x} {x : M}
    (hKoszul : HasDerivAt
      (fun τ => metricKoszulExpression (I := I) (M := M) g τ X Y Z x)
      (metricVelocityKoszulExpression (I := I) (M := M) hdot X Y Z x) t)
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun y ↦ TotalSpace.mk' E y (X y)))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun y ↦ TotalSpace.mk' E y (Y y)))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun y ↦ TotalSpace.mk' E y (Z y))) :
    HasDerivAt
      (fun τ : ℝ => (g τ).inner x ((cov τ).along X Y x) (Z x))
      ((1 / 2 : ℝ) * metricVelocityKoszulExpression
        (I := I) (M := M) hdot X Y Z x) t := by
  have hkoszul (τ : ℝ) :
      2 * (g τ).inner x ((cov τ).along X Y x) (Z x) =
        metricKoszulExpression (I := I) (M := M) g τ X Y Z x := by
    letI : RiemannianBundle TM := ⟨(g τ).toRiemannianMetric⟩
    have hinner (y : M) (u v : TM y) :
        (g τ).inner y u v = Inner.inner ℝ u v := rfl
    have hk := _root_.CovariantDerivative.koszul_formula
      (I := I) (E := E) (M := M) (cov := cov τ) (hLevi τ)
      (x := x) hX hY hZ
    simpa [metricKoszulExpression, hinner] using hk
  have hfunction :
      (fun τ : ℝ => (g τ).inner x ((cov τ).along X Y x) (Z x)) =
        (fun τ => (1 / 2 : ℝ) *
          metricKoszulExpression (I := I) (M := M) g τ X Y Z x) := by
    funext τ
    have hk := hkoszul τ
    apply (mul_left_cancel₀ (by norm_num : (2 : ℝ) ≠ 0))
    calc
      2 * ((g τ).inner x ((cov τ).along X Y x) (Z x)) = _ := hk
      _ = 2 * ((1 / 2 : ℝ) *
            metricKoszulExpression (I := I) (M := M) g τ X Y Z x) := by ring
  rw [hfunction]
  exact hKoszul.const_mul (1 / 2 : ℝ)

/-- The scalar time-differentiated Koszul identity determines the actual
time derivative of `∇_X Y` once its pointwise metric-dual formula is known.
The proof tests against canonical smooth extensions of every fibre vector,
then uses positive-definiteness to recover the vector derivative. -/
theorem hasDerivAt_along_const_of_koszul_variation_pairings
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E)
      (V := (TangentSpace I : M → Type _)))
    (hcov : ∀ τ : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E)
      (V := (TangentSpace I : M → Type _)) (cov τ) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdot : ∀ x : M, TM x →ₗ[ℝ] TM x →ₗ[ℝ] ℝ)
    {t : ℝ}
    (hmetric : ∀ (x : M) (u v : TM x),
      HasDerivAt (fun τ : ℝ => (g τ).inner x u v) (hdot x u v) t)
    {X Y : Π y : M, TM y} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun y ↦ TotalSpace.mk' E y (X y)))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun y ↦ TotalSpace.mk' E y (Y y)))
    (hmixedXYZ : ∀ (Z : Π y : M, TM y),
      ContMDiff I (I.prod 𝓘(ℝ, E)) 2
        (fun y ↦ TotalSpace.mk' E y (Z y)) → HasDerivAt
      (fun τ : ℝ =>
        mvfderiv (I := I) (fun y ↦ (g τ).inner y (Y y) (Z y)) x (X x))
      (mvfderiv (I := I) (fun y ↦ hdot y (Y y) (Z y)) x (X x)) t)
    (hmixedYXZ : ∀ (Z : Π y : M, TM y),
      ContMDiff I (I.prod 𝓘(ℝ, E)) 2
        (fun y ↦ TotalSpace.mk' E y (Z y)) → HasDerivAt
      (fun τ : ℝ =>
        mvfderiv (I := I) (fun y ↦ (g τ).inner y (X y) (Z y)) x (Y x))
      (mvfderiv (I := I) (fun y ↦ hdot y (X y) (Z y)) x (Y x)) t)
    (hmixedZXY : ∀ (Z : Π y : M, TM y),
      ContMDiff I (I.prod 𝓘(ℝ, E)) 2
        (fun y ↦ TotalSpace.mk' E y (Z y)) → HasDerivAt
      (fun τ : ℝ =>
        mvfderiv (I := I) (fun y ↦ (g τ).inner y (X y) (Y y)) x (Z x))
      (mvfderiv (I := I) (fun y ↦ hdot y (X y) (Y y)) x (Z x)) t)
    (Axy : TM x)
    (hAxy : ∀ v : TM x,
      metricVelocityKoszulExpression (I := I) (M := M) hdot X Y
          (CovariantDerivative.smoothExtend
            (I := I) (F := E) (V := (TangentSpace I : M → Type _)) x v) x =
        2 * (hdot x v ((cov t).along X Y x) + (g t).inner x v Axy)) :
    HasDerivAt (fun τ : ℝ => (cov τ).along X Y x) Axy t := by
  have hmetricSwap (τ : ℝ) (u v : TM x) :
      (g τ).inner x u v = (g τ).inner x v u := by
    letI : RiemannianBundle TM := ⟨(g τ).toRiemannianMetric⟩
    change Inner.inner ℝ u v = Inner.inner ℝ v u
    exact (real_inner_comm u v).symm
  have hpair : ∀ v : TM x,
      HasDerivAt (fun τ : ℝ => (g τ).inner x v ((cov τ).along X Y x))
        (hdot x v ((cov t).along X Y x) + (g t).inner x v Axy) t := by
    intro v
    let Z : Π y : M, TM y :=
      CovariantDerivative.smoothExtend
        (I := I) (F := E) (V := (TangentSpace I : M → Type _)) x v
    have hZ₂ : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (T% Z) := by
      simpa [Z] using CovariantDerivative.smoothExtend_contMDiff_two
        (I := I) (F := E) (V := (TangentSpace I : M → Type _)) x v
    have hKoszul := hasDerivAt_metricKoszulExpression
      (I := I) (M := M) g hdot (t := t) hmetric
      (X := X) (Y := Y) (Z := Z) (x := x)
      (hmixedXYZ Z hZ₂) (hmixedYXZ Z hZ₂) (hmixedZXY Z hZ₂)
    have hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (T% Z) :=
      hZ₂.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
    have hconn := hasDerivAt_metricConnectionPairing_of_koszulExpression
      (I := I) (M := M) g cov hcov hLevi hdot (t := t)
      (X := X) (Y := Y) (Z := Z) (x := x) hKoszul hX hY hZ
    have hconnPair : HasDerivAt
        (fun τ : ℝ => (g τ).inner x ((cov τ).along X Y x) v)
        ((1 / 2 : ℝ) * metricVelocityKoszulExpression
          (I := I) (M := M) hdot X Y Z x) t := by
      simpa [Z, CovariantDerivative.smoothExtend_apply] using hconn
    have hfunction :
        (fun τ : ℝ => (g τ).inner x v ((cov τ).along X Y x)) =
          (fun τ : ℝ => (g τ).inner x ((cov τ).along X Y x) v) := by
      funext τ
      exact hmetricSwap τ v ((cov τ).along X Y x)
    have hderiv :
        (1 / 2 : ℝ) * metricVelocityKoszulExpression
            (I := I) (M := M) hdot X Y Z x =
          hdot x v ((cov t).along X Y x) + (g t).inner x v Axy := by
      rw [hAxy v]
      ring
    rw [hfunction]
    exact hconnPair.congr_deriv hderiv
  exact hasDerivAt_vector_of_metric_pairings
    (I := I) (M := M) g hdot (t := t) hmetric x
    (fun τ => (cov τ).along X Y x) Axy hpair

/-- The metric-dual value in the preceding theorem can itself be constructed
from the differentiated Koszul pairings. Their scalar derivative is linear in
the test vector; finite-dimensional Riesz representation then supplies the
actual tangent-vector velocity. -/
theorem exists_hasDerivAt_along_const_of_koszulExpression
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E)
      (V := (TangentSpace I : M → Type _)))
    (hcov : ∀ τ : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E)
      (V := (TangentSpace I : M → Type _)) (cov τ) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdot : ∀ x : M, TM x →ₗ[ℝ] TM x →ₗ[ℝ] ℝ)
    {t : ℝ}
    (hmetric : ∀ (x : M) (u v : TM x),
      HasDerivAt (fun τ : ℝ => (g τ).inner x u v) (hdot x u v) t)
    {X Y : Π y : M, TM y} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun y ↦ TotalSpace.mk' E y (X y)))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun y ↦ TotalSpace.mk' E y (Y y)))
    (hmixedXYZ : ∀ (Z : Π y : M, TM y),
      ContMDiff I (I.prod 𝓘(ℝ, E)) 2
        (fun y ↦ TotalSpace.mk' E y (Z y)) → HasDerivAt
      (fun τ : ℝ =>
        mvfderiv (I := I) (fun y ↦ (g τ).inner y (Y y) (Z y)) x (X x))
      (mvfderiv (I := I) (fun y ↦ hdot y (Y y) (Z y)) x (X x)) t)
    (hmixedYXZ : ∀ (Z : Π y : M, TM y),
      ContMDiff I (I.prod 𝓘(ℝ, E)) 2
        (fun y ↦ TotalSpace.mk' E y (Z y)) → HasDerivAt
      (fun τ : ℝ =>
        mvfderiv (I := I) (fun y ↦ (g τ).inner y (X y) (Z y)) x (Y x))
      (mvfderiv (I := I) (fun y ↦ hdot y (X y) (Z y)) x (Y x)) t)
    (hmixedZXY : ∀ (Z : Π y : M, TM y),
      ContMDiff I (I.prod 𝓘(ℝ, E)) 2
        (fun y ↦ TotalSpace.mk' E y (Z y)) → HasDerivAt
      (fun τ : ℝ =>
        mvfderiv (I := I) (fun y ↦ (g τ).inner y (X y) (Y y)) x (Z x))
      (mvfderiv (I := I) (fun y ↦ hdot y (X y) (Y y)) x (Z x)) t) :
    ∃ Axy : TM x, HasDerivAt (fun τ : ℝ => (cov τ).along X Y x) Axy t := by
  let pairing : TM x → ℝ → ℝ := fun v τ =>
    (g τ).inner x ((cov τ).along X Y x) v
  let D : TM x → ℝ := fun v =>
    (1 / 2 : ℝ) * metricVelocityKoszulExpression (I := I) (M := M) hdot X Y
      (CovariantDerivative.smoothExtend
        (I := I) (F := E) (V := (TangentSpace I : M → Type _)) x v) x
  have hDpair (v : TM x) : HasDerivAt (pairing v) (D v) t := by
    let Z : Π y : M, TM y :=
      CovariantDerivative.smoothExtend
        (I := I) (F := E) (V := (TangentSpace I : M → Type _)) x v
    have hZ₂ : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (T% Z) := by
      simpa [Z] using CovariantDerivative.smoothExtend_contMDiff_two
        (I := I) (F := E) (V := (TangentSpace I : M → Type _)) x v
    have hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (T% Z) :=
      hZ₂.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
    have hKoszul := hasDerivAt_metricKoszulExpression
      (I := I) (M := M) g hdot (t := t) hmetric
      (X := X) (Y := Y) (Z := Z) (x := x)
      (hmixedXYZ Z hZ₂) (hmixedYXZ Z hZ₂) (hmixedZXY Z hZ₂)
    have hconn := hasDerivAt_metricConnectionPairing_of_koszulExpression
      (I := I) (M := M) g cov hcov hLevi hdot (t := t)
      (X := X) (Y := Y) (Z := Z) (x := x) hKoszul hX hY hZ
    simpa [pairing, D, Z, CovariantDerivative.smoothExtend_apply] using hconn
  have hpairAdd (u v : TM x) :
      pairing (u + v) = pairing u + pairing v := by
    funext τ
    simp [pairing, inner_add_right]
  have hpairSmul (c : ℝ) (v : TM x) :
      pairing (c • v) = fun τ => c * pairing v τ := by
    funext τ
    simp [pairing, inner_smul_right, smul_eq_mul]
  have hDadd (u v : TM x) : D (u + v) = D u + D v := by
    have hsum := (hDpair u).add (hDpair v)
    rw [← hpairAdd u v] at hsum
    exact (hDpair (u + v)).unique hsum
  have hDsmul (c : ℝ) (v : TM x) : D (c • v) = c * D v := by
    have hmul := (hDpair v).const_mul c
    rw [← hpairSmul c v] at hmul
    exact (hDpair (c • v)).unique hmul
  let δ : TM x →ₗ[ℝ] ℝ :=
    { toFun := fun v => D v - hdot x v ((cov t).along X Y x)
      map_add' := by
        intro u v
        change D (u + v) - (hdot x (u + v)) ((cov t).along X Y x) =
          (D u - (hdot x u) ((cov t).along X Y x)) +
            (D v - (hdot x v) ((cov t).along X Y x))
        rw [hDadd, (hdot x).map_add]
        simp only [LinearMap.add_apply]
        ring
      map_smul' := by
        intro c v
        change D (c • v) - (hdot x (c • v)) ((cov t).along X Y x) =
          c • (D v - (hdot x v) ((cov t).along X Y x))
        rw [hDsmul, (hdot x).map_smul]
        simp only [LinearMap.smul_apply, smul_eq_mul]
        ring }
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : FiniteDimensional ℝ (TM x) :=
    VectorBundle.finiteDimensional ℝ E (TangentSpace I : M → Type _) x
  letI : CompleteSpace (TM x) := FiniteDimensional.complete ℝ (TM x)
  let δcont : TM x →L[ℝ] ℝ :=
    ⟨δ, LinearMap.continuous_of_finiteDimensional δ⟩
  let Axy : TM x := (InnerProductSpace.toDual ℝ (TM x)).symm δcont
  have hdual (v : TM x) : (g t).inner x v Axy = δ v := by
    calc
      (g t).inner x v Axy = Inner.inner ℝ v Axy := rfl
      _ = Inner.inner ℝ Axy v := (real_inner_comm v Axy).symm
      _ = δcont v := by simp [Axy]
      _ = δ v := rfl
  have hAxy : ∀ v : TM x,
      metricVelocityKoszulExpression (I := I) (M := M) hdot X Y
          (CovariantDerivative.smoothExtend
            (I := I) (F := E) (V := (TangentSpace I : M → Type _)) x v) x =
        2 * (hdot x v ((cov t).along X Y x) + (g t).inner x v Axy) := by
    intro v
    rw [hdual v]
    change metricVelocityKoszulExpression (I := I) (M := M) hdot X Y
        (CovariantDerivative.smoothExtend
          (I := I) (F := E) (V := (TangentSpace I : M → Type _)) x v) x =
      2 * (hdot x v ((cov t).along X Y x) +
        (D v - hdot x v ((cov t).along X Y x)))
    dsimp [D]
    ring
  refine ⟨Axy, ?_⟩
  exact hasDerivAt_along_const_of_koszul_variation_pairings
    (I := I) (M := M) g cov hcov hLevi hdot (t := t) hmetric
    (X := X) (Y := Y) (x := x) hX hY hmixedXYZ hmixedYXZ hmixedZXY Axy hAxy

/-- The time derivative of the actual Levi-Civita connection on fixed fields
is represented by the cyclic covariant derivative of the metric velocity.
The vector is recovered from differentiated Koszul pairings; the cyclic
formula is then proved, not used as a definition of the derivative. -/
theorem exists_hasDerivAt_along_const_with_cyclic_metricVariation
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E)
      (V := (TangentSpace I : M → Type _)))
    (hcov : ∀ τ : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E)
      (V := (TangentSpace I : M → Type _)) (cov τ) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdot : ∀ x : M, TM x →ₗ[ℝ] TM x →ₗ[ℝ] ℝ)
    {t : ℝ}
    (hmetric : ∀ (x : M) (u v : TM x),
      HasDerivAt (fun τ : ℝ => (g τ).inner x u v) (hdot x u v) t)
    {X Y : Π y : M, TM y} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun y ↦ TotalSpace.mk' E y (X y)))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun y ↦ TotalSpace.mk' E y (Y y)))
    (hmixedXYZ : ∀ (Z : Π y : M, TM y),
      ContMDiff I (I.prod 𝓘(ℝ, E)) 2
        (fun y ↦ TotalSpace.mk' E y (Z y)) → HasDerivAt
      (fun τ : ℝ =>
        mvfderiv (I := I) (fun y ↦ (g τ).inner y (Y y) (Z y)) x (X x))
      (mvfderiv (I := I) (fun y ↦ hdot y (Y y) (Z y)) x (X x)) t)
    (hmixedYXZ : ∀ (Z : Π y : M, TM y),
      ContMDiff I (I.prod 𝓘(ℝ, E)) 2
        (fun y ↦ TotalSpace.mk' E y (Z y)) → HasDerivAt
      (fun τ : ℝ =>
        mvfderiv (I := I) (fun y ↦ (g τ).inner y (X y) (Z y)) x (Y x))
      (mvfderiv (I := I) (fun y ↦ hdot y (X y) (Z y)) x (Y x)) t)
    (hmixedZXY : ∀ (Z : Π y : M, TM y),
      ContMDiff I (I.prod 𝓘(ℝ, E)) 2
        (fun y ↦ TotalSpace.mk' E y (Z y)) → HasDerivAt
      (fun τ : ℝ =>
        mvfderiv (I := I) (fun y ↦ (g τ).inner y (X y) (Y y)) x (Z x))
      (mvfderiv (I := I) (fun y ↦ hdot y (X y) (Y y)) x (Z x)) t) :
    ∃ Axy : TM x,
      HasDerivAt (fun τ : ℝ => (cov τ).along X Y x) Axy t ∧
      ∀ (Z : Π y : M, TM y),
        ContMDiff I (I.prod 𝓘(ℝ, E)) 2
          (fun y ↦ TotalSpace.mk' E y (Z y)) →
        2 * (g t).inner x Axy (Z x) =
          metricVelocityCovariantDerivativeAlong
              (I := I) (M := M) cov hdot t X Y Z x +
            metricVelocityCovariantDerivativeAlong
              (I := I) (M := M) cov hdot t Y X Z x -
            metricVelocityCovariantDerivativeAlong
              (I := I) (M := M) cov hdot t Z X Y x := by
  have hdotSymm : ∀ (y : M) (u v : TM y),
      hdot y u v = hdot y v u := by
    intro y u v
    have hmetricSwap (τ : ℝ) :
        (g τ).inner y u v = (g τ).inner y v u := by
      letI : RiemannianBundle TM := ⟨(g τ).toRiemannianMetric⟩
      change Inner.inner ℝ u v = Inner.inner ℝ v u
      exact (real_inner_comm u v).symm
    have hfunction :
        (fun τ : ℝ => (g τ).inner y u v) =
          (fun τ : ℝ => (g τ).inner y v u) := funext hmetricSwap
    have hleft := hmetric y u v
    rw [hfunction] at hleft
    exact hleft.unique (hmetric y v u)
  obtain ⟨Axy, hAxy⟩ := exists_hasDerivAt_along_const_of_koszulExpression
    (I := I) (M := M) g cov hcov hLevi hdot (t := t) hmetric
    (X := X) (Y := Y) (x := x) hX hY hmixedXYZ hmixedYXZ hmixedZXY
  refine ⟨Axy, hAxy, ?_⟩
  intro Z hZ
  have hZ₁ : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (T% Z) :=
    hZ.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hKoszul := hasDerivAt_metricKoszulExpression
    (I := I) (M := M) g hdot (t := t) hmetric
    (X := X) (Y := Y) (Z := Z) (x := x)
    (hmixedXYZ Z hZ) (hmixedYXZ Z hZ) (hmixedZXY Z hZ)
  have hconnectionPairing := hasDerivAt_metricConnectionPairing_of_koszulExpression
    (I := I) (M := M) g cov hcov hLevi hdot (t := t)
    (X := X) (Y := Y) (Z := Z) (x := x) hKoszul hX hY hZ₁
  have hactualPairing := hasDerivAt_metricInner_left_of_pairwise_derivative
    (I := I) (M := M) g hdot (t := t) hmetric x
    (fun τ => (cov τ).along X Y x) Axy (Z x) hAxy
  have hKoszulDual : metricVelocityKoszulExpression
      (I := I) (M := M) hdot X Y Z x =
        2 * (hdot x ((cov t).along X Y x) (Z x) +
          (g t).inner x Axy (Z x)) := by
    have hderiv := hactualPairing.unique hconnectionPairing
    dsimp [CovariantDerivative.along] at hderiv
    dsimp [CovariantDerivative.along]
    linarith
  have hcyclic : metricVelocityKoszulExpression
      (I := I) (M := M) hdot X Y Z x =
        2 * hdot x ((cov t).along X Y x) (Z x) +
          metricVelocityCovariantDerivativeAlong
              (I := I) (M := M) cov hdot t X Y Z x +
            metricVelocityCovariantDerivativeAlong
              (I := I) (M := M) cov hdot t Y X Z x -
              metricVelocityCovariantDerivativeAlong
                (I := I) (M := M) cov hdot t Z X Y x := by
    exact metricVelocityKoszulExpression_eq_cyclicCovariantDerivative
      (I := I) (M := M) (g := g) (cov := cov) (hLevi := hLevi)
      (hcov := hcov) (hdot := hdot) (hdotSymm := hdotSymm) (t := t)
      (X := X) (Y := Y) (Z := Z) (x := x) hX hY hZ₁
  rw [hcyclic] at hKoszulDual
  linarith

/-- Differentiating the actual metric-compatibility identity in time gives the
two-term connection-velocity formula for `∇ hdot`. The only extra regularity
is the displayed mixed derivative commutation; the connection-variation rule
is applied to the actual Levi-Civita family. -/
theorem metricVelocityCovariantDerivative_eq_connectionVariation
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E)
      (V := (TangentSpace I : M → Type _)))
    (hLevi : g.IsLeviCivita cov)
    (A : ∀ x : M, TM x → TM x → TM x)
    (hdot : ∀ x : M, TM x →ₗ[ℝ] TM x →ₗ[ℝ] ℝ)
    {t : ℝ}
    (hvariation : TimeDependentCovariantDerivative.HasConnectionTimeVariationAt
      (I := I) (M := M) cov A t)
    (hmetric : ∀ (x : M) (u v : TM x),
      HasDerivAt (fun τ : ℝ => (g τ).inner x u v) (hdot x u v) t)
    {X Y Z : Π x : M, TM x} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun y ↦ TotalSpace.mk' E y (X y)))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun y ↦ TotalSpace.mk' E y (Y y)))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun y ↦ TotalSpace.mk' E y (Z y)))
    (hmixed : HasDerivAt
      (fun τ : ℝ =>
        mvfderiv (I := I) (fun y ↦ (g τ).inner y (Y y) (Z y)) x (X x))
      (mvfderiv (I := I) (fun y ↦ hdot y (Y y) (Z y)) x (X x)) t) :
    metricVelocityCovariantDerivativeAlong
        (I := I) (M := M) cov hdot t X Y Z x =
      (g t).inner x (A x (X x) (Y x)) (Z x) +
        (g t).inner x (Y x) (A x (X x) (Z x)) := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  have hXmd (y : M) : MDiffAt (T% X) y :=
    (hX y).mdifferentiableAt (by norm_num)
  have hYmd (y : M) : MDiffAt (T% Y) y :=
    (hY y).mdifferentiableAt (by norm_num)
  have hZmd (y : M) : MDiffAt (T% Z) y :=
    (hZ y).mdifferentiableAt (by norm_num)
  have hmetricSwap (τ : ℝ) (u v : TM x) :
      (g τ).inner x u v = (g τ).inner x v u := by
    letI : RiemannianBundle TM := ⟨(g τ).toRiemannianMetric⟩
    change Inner.inner ℝ u v = Inner.inner ℝ v u
    exact (real_inner_comm u v).symm
  have hmetricSwapFun (u v : TM x) :
      (fun τ : ℝ => (g τ).inner x u v) =
        (fun τ : ℝ => (g τ).inner x v u) := by
    funext τ
    exact hmetricSwap τ u v
  have hdotSwap (u v : TM x) : hdot x u v = hdot x v u := by
    have h₁ := hmetric x u v
    rw [hmetricSwapFun u v] at h₁
    exact h₁.unique (hmetric x v u)
  have hconnXY :=
    _root_.CovariantDerivative.TimeDependentCovariantDerivative.hasDerivAt_along_const_of_hasConnectionTimeVariationAt
      (I := I) (M := M) cov A hvariation X Y hXmd hYmd x
  have hconnXZ :=
    _root_.CovariantDerivative.TimeDependentCovariantDerivative.hasDerivAt_along_const_of_hasConnectionTimeVariationAt
      (I := I) (M := M) cov A hvariation X Z hXmd hZmd x
  let lhs : ℝ → ℝ := fun τ =>
    mvfderiv (I := I) (fun y ↦ (g τ).inner y (Y y) (Z y)) x (X x)
  let rhs : ℝ → ℝ := fun τ =>
    (g τ).inner x ((cov τ).along X Y x) (Z x) +
      (g τ).inner x (Y x) ((cov τ).along X Z x)
  have hfirst : HasDerivAt
      (fun τ : ℝ => (g τ).inner x ((cov τ).along X Y x) (Z x))
      (hdot x ((cov t).along X Y x) (Z x) +
        (g t).inner x (A x (X x) (Y x)) (Z x)) t :=
    hasDerivAt_metricInner_left_of_pairwise_derivative
      (I := I) (M := M) g hdot (t := t) hmetric x
      (fun τ => (cov τ).along X Y x) (A x (X x) (Y x)) (Z x) hconnXY
  have hsecondSwap :=
    hasDerivAt_metricInner_left_of_pairwise_derivative
      (I := I) (M := M) g hdot (t := t) hmetric x
      (fun τ => (cov τ).along X Z x) (A x (X x) (Z x)) (Y x) hconnXZ
  have hsecondEq :
      (fun τ : ℝ => (g τ).inner x (Y x) ((cov τ).along X Z x)) =
        (fun τ : ℝ => (g τ).inner x ((cov τ).along X Z x) (Y x)) := by
    funext τ
    exact hmetricSwap τ (Y x) ((cov τ).along X Z x)
  have hsecondSwap' : HasDerivAt
      (fun τ : ℝ => (g τ).inner x (Y x) ((cov τ).along X Z x))
      (hdot x ((cov t).along X Z x) (Y x) +
        (g t).inner x (A x (X x) (Z x)) (Y x)) t := by
    rw [hsecondEq]
    exact hsecondSwap
  have hsecond : HasDerivAt
      (fun τ : ℝ => (g τ).inner x (Y x) ((cov τ).along X Z x))
      (hdot x (Y x) ((cov t).along X Z x) +
        (g t).inner x (Y x) (A x (X x) (Z x))) t := by
    apply hsecondSwap'.congr_deriv
    have hdotEq := hdotSwap ((cov t).along X Z x) (Y x)
    have hinnerEq :
        (g t).inner x (A x (X x) (Z x)) (Y x) =
          (g t).inner x (Y x) (A x (X x) (Z x)) := by
      change Inner.inner ℝ (A x (X x) (Z x)) (Y x) =
        Inner.inner ℝ (Y x) (A x (X x) (Z x))
      exact (real_inner_comm _ _).symm
    rw [hdotEq, hinnerEq]
  have hrhs : HasDerivAt rhs
      (hdot x ((cov t).along X Y x) (Z x) +
          (g t).inner x (A x (X x) (Y x)) (Z x) +
        (hdot x (Y x) ((cov t).along X Z x) +
          (g t).inner x (Y x) (A x (X x) (Z x)))) t := by
    convert hfirst.add hsecond using 1 <;> rfl
  have hslice (τ : ℝ) : lhs τ = rhs τ := by
    letI : RiemannianBundle TM := ⟨(g τ).toRiemannianMetric⟩
    have hmetricCompat := (hLevi τ).2 (hYmd x) (hZmd x) (X x)
    have hinnerField :
        (fun y : M => (g τ).inner y (Y y) (Z y)) =
          (fun y : M => Inner.inner ℝ (Y y) (Z y)) := by
      funext y
      rfl
    calc
      lhs τ = mvfderiv (I := I)
          (fun y : M => Inner.inner ℝ (Y y) (Z y)) x (X x) := by
            exact congrArg (fun f => mvfderiv (I := I) f x (X x)) hinnerField
      _ = Inner.inner ℝ ((cov τ).along X Y x) (Z x) +
          Inner.inner ℝ (Y x) ((cov τ).along X Z x) := by
            simpa [CovariantDerivative.along] using hmetricCompat
      _ = rhs τ := by
            rfl
  have hfunction : lhs = rhs := funext hslice
  have hleft : HasDerivAt lhs
      (mvfderiv (I := I) (fun y ↦ hdot y (Y y) (Z y)) x (X x)) t := by
    simpa [lhs] using hmixed
  rw [hfunction] at hleft
  have hderivative := hleft.unique hrhs
  dsimp [metricVelocityCovariantDerivativeAlong, CovariantDerivative.along]
  rw [hderivative]
  simp only [CovariantDerivative.along_apply]
  ring

/-- The time derivative of a torsion-free connection is symmetric in its two
spatial inputs. This is derived by differentiating the slice-wise torsion
identity; it is not a separate symmetry assumption on `A`. -/
theorem connectionTimeVariation_symmetric_of_LeviCivita
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E)
      (V := (TangentSpace I : M → Type _)))
    (hcov : ∀ τ : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E)
      (V := (TangentSpace I : M → Type _)) (cov τ) 1)
    (hLevi : g.IsLeviCivita cov)
    (A : ∀ x : M, TM x → TM x → TM x)
    {t : ℝ}
    (hvariation : TimeDependentCovariantDerivative.HasConnectionTimeVariationAt
      (I := I) (M := M) cov A t)
    {X Y : Π x : M, TM x} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun y ↦ TotalSpace.mk' E y (X y)))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun y ↦ TotalSpace.mk' E y (Y y))) :
    A x (X x) (Y x) = A x (Y x) (X x) := by
  have hXmd (y : M) : MDiffAt (T% X) y :=
    (hX y).mdifferentiableAt (by norm_num)
  have hYmd (y : M) : MDiffAt (T% Y) y :=
    (hY y).mdifferentiableAt (by norm_num)
  have hconnXY :=
    _root_.CovariantDerivative.TimeDependentCovariantDerivative.hasDerivAt_along_const_of_hasConnectionTimeVariationAt
      (I := I) (M := M) cov A hvariation X Y hXmd hYmd x
  have hconnYX :=
    _root_.CovariantDerivative.TimeDependentCovariantDerivative.hasDerivAt_along_const_of_hasConnectionTimeVariationAt
      (I := I) (M := M) cov A hvariation Y X hYmd hXmd x
  have htorsion (τ : ℝ) :
      (cov τ).along X Y x - (cov τ).along Y X x =
        VectorField.mlieBracket I X Y x := by
    letI := hcov τ
    have hT : (cov τ).torsion = 0 := (hLevi τ).1
    have hglobal :=
      _root_.CovariantDerivative.along_sub_eq_mlieBracket_of_torsion_eq_zero
        (cov := cov τ) hT hX hY
    exact congrFun hglobal x
  have hfunction :
      (fun τ : ℝ => (cov τ).along X Y x - (cov τ).along Y X x) =
        (fun _ : ℝ => VectorField.mlieBracket I X Y x) := by
    funext τ
    exact htorsion τ
  have hderivative : HasDerivAt
      (fun τ : ℝ => (cov τ).along X Y x - (cov τ).along Y X x)
      (A x (X x) (Y x) - A x (Y x) (X x)) t := by
    convert hconnXY.sub hconnYX using 1 <;> rfl
  rw [hfunction] at hderivative
  have hconstant : HasDerivAt
      (fun _ : ℝ => VectorField.mlieBracket I X Y x) 0 t :=
    hasDerivAt_const (x := t) (c := VectorField.mlieBracket I X Y x)
  have hzero := hderivative.unique hconstant
  exact sub_eq_zero.mp hzero

/-- **Metric-to-Levi-Civita connection variation formula.** Combining the
time-differentiated metric-compatibility identity with time-differentiated
torsion yields the standard cyclic formula for the actual connection
variation. The three explicit `hmixed` hypotheses are precisely the
time/space derivative commutations used to differentiate compatibility. -/
theorem metricVelocityCovariantDerivative_connectionVariation_formula
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E)
      (V := (TangentSpace I : M → Type _)))
    (hcov : ∀ τ : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E)
      (V := (TangentSpace I : M → Type _)) (cov τ) 1)
    (hLevi : g.IsLeviCivita cov)
    (A : ∀ x : M, TM x → TM x → TM x)
    (hdot : ∀ x : M, TM x →ₗ[ℝ] TM x →ₗ[ℝ] ℝ)
    {t : ℝ}
    (hvariation : TimeDependentCovariantDerivative.HasConnectionTimeVariationAt
      (I := I) (M := M) cov A t)
    (hmetric : ∀ (x : M) (u v : TM x),
      HasDerivAt (fun τ : ℝ => (g τ).inner x u v) (hdot x u v) t)
    {X Y Z : Π x : M, TM x} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun y ↦ TotalSpace.mk' E y (X y)))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun y ↦ TotalSpace.mk' E y (Y y)))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun y ↦ TotalSpace.mk' E y (Z y)))
    (hmixedXYZ : HasDerivAt
      (fun τ : ℝ =>
        mvfderiv (I := I) (fun y ↦ (g τ).inner y (Y y) (Z y)) x (X x))
      (mvfderiv (I := I) (fun y ↦ hdot y (Y y) (Z y)) x (X x)) t)
    (hmixedYXZ : HasDerivAt
      (fun τ : ℝ =>
        mvfderiv (I := I) (fun y ↦ (g τ).inner y (X y) (Z y)) x (Y x))
      (mvfderiv (I := I) (fun y ↦ hdot y (X y) (Z y)) x (Y x)) t)
    (hmixedZXY : HasDerivAt
      (fun τ : ℝ =>
        mvfderiv (I := I) (fun y ↦ (g τ).inner y (X y) (Y y)) x (Z x))
      (mvfderiv (I := I) (fun y ↦ hdot y (X y) (Y y)) x (Z x)) t) :
    2 * (g t).inner x (A x (X x) (Y x)) (Z x) =
      metricVelocityCovariantDerivativeAlong
          (I := I) (M := M) cov hdot t X Y Z x +
        metricVelocityCovariantDerivativeAlong
          (I := I) (M := M) cov hdot t Y X Z x -
        metricVelocityCovariantDerivativeAlong
          (I := I) (M := M) cov hdot t Z X Y x := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  have h₁ := metricVelocityCovariantDerivative_eq_connectionVariation
    (I := I) (M := M) g cov hLevi A hdot (t := t) hvariation hmetric
    hX hY hZ hmixedXYZ
  have h₂ := metricVelocityCovariantDerivative_eq_connectionVariation
    (I := I) (M := M) g cov hLevi A hdot (t := t) hvariation hmetric
    hY hX hZ hmixedYXZ
  have h₃ := metricVelocityCovariantDerivative_eq_connectionVariation
    (I := I) (M := M) g cov hLevi A hdot (t := t) hvariation hmetric
    hZ hX hY hmixedZXY
  have hAXY := connectionTimeVariation_symmetric_of_LeviCivita
    (I := I) (M := M) g cov hcov hLevi A hvariation hX hY (x := x)
  have hAZX := connectionTimeVariation_symmetric_of_LeviCivita
    (I := I) (M := M) g cov hcov hLevi A hvariation hZ hX (x := x)
  have hAZY := connectionTimeVariation_symmetric_of_LeviCivita
    (I := I) (M := M) g cov hcov hLevi A hvariation hZ hY (x := x)
  have hinnerSwap (u v : TM x) :
      (g t).inner x u v = (g t).inner x v u := by
    change Inner.inner ℝ u v = Inner.inner ℝ v u
    exact (real_inner_comm u v).symm
  rw [← hAXY] at h₂
  rw [hAZX, hAZY, hinnerSwap (A x (X x) (Z x)) (Y x)] at h₃
  linarith [h₁, h₂, h₃]

/-- Scaled specialization of the cyclic connection-variation formula. In
particular, once the metric velocity is identified with `c • h`, the
connection variation is the same cyclic combination of the covariant
derivative of `h`, multiplied by `c`. -/
theorem metricVelocityCovariantDerivative_connectionVariation_formula_smul
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E)
      (V := (TangentSpace I : M → Type _)))
    (hcov : ∀ τ : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E)
      (V := (TangentSpace I : M → Type _)) (cov τ) 1)
    (hLevi : g.IsLeviCivita cov)
    (A : ∀ x : M, TM x → TM x → TM x)
    (h : ∀ x : M, TM x →ₗ[ℝ] TM x →ₗ[ℝ] ℝ)
    (c : ℝ) {t : ℝ}
    (hvariation : TimeDependentCovariantDerivative.HasConnectionTimeVariationAt
      (I := I) (M := M) cov A t)
    (hmetric : ∀ (x : M) (u v : TM x),
      HasDerivAt (fun τ : ℝ => (g τ).inner x u v) ((c • h x) u v) t)
    {X Y Z : Π x : M, TM x} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun y ↦ TotalSpace.mk' E y (X y)))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun y ↦ TotalSpace.mk' E y (Y y)))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun y ↦ TotalSpace.mk' E y (Z y)))
    (hXY : MDiffAt (fun y ↦ h y (Y y) (Z y)) x)
    (hYX : MDiffAt (fun y ↦ h y (X y) (Z y)) x)
    (hZX : MDiffAt (fun y ↦ h y (X y) (Y y)) x)
    (hmixedXYZ : HasDerivAt
      (fun τ : ℝ =>
        mvfderiv (I := I) (fun y ↦ (g τ).inner y (Y y) (Z y)) x (X x))
      (mvfderiv (I := I) (fun y ↦ (c • h y) (Y y) (Z y)) x (X x)) t)
    (hmixedYXZ : HasDerivAt
      (fun τ : ℝ =>
        mvfderiv (I := I) (fun y ↦ (g τ).inner y (X y) (Z y)) x (Y x))
      (mvfderiv (I := I) (fun y ↦ (c • h y) (X y) (Z y)) x (Y x)) t)
    (hmixedZXY : HasDerivAt
      (fun τ : ℝ =>
        mvfderiv (I := I) (fun y ↦ (g τ).inner y (X y) (Y y)) x (Z x))
      (mvfderiv (I := I) (fun y ↦ (c • h y) (X y) (Y y)) x (Z x)) t) :
    2 * (g t).inner x (A x (X x) (Y x)) (Z x) =
      c * (metricVelocityCovariantDerivativeAlong
          (I := I) (M := M) cov h t X Y Z x +
        metricVelocityCovariantDerivativeAlong
          (I := I) (M := M) cov h t Y X Z x -
        metricVelocityCovariantDerivativeAlong
          (I := I) (M := M) cov h t Z X Y x) := by
  let hdot : ∀ y : M, TM y →ₗ[ℝ] TM y →ₗ[ℝ] ℝ := fun y => c • h y
  have hmetric' : ∀ (y : M) (u v : TM y),
      HasDerivAt (fun τ : ℝ => (g τ).inner y u v) (hdot y u v) t := by
    intro y u v
    exact hmetric y u v
  have hformula := metricVelocityCovariantDerivative_connectionVariation_formula
    (I := I) (M := M) g cov hcov hLevi A hdot (t := t) hvariation hmetric'
      hX hY hZ hmixedXYZ hmixedYXZ hmixedZXY
  have hscaleXYZ := metricVelocityCovariantDerivativeAlong_smul
    (I := I) (M := M) cov h c t X Y Z x hXY
  have hscaleYXZ := metricVelocityCovariantDerivativeAlong_smul
    (I := I) (M := M) cov h c t Y X Z x hYX
  have hscaleZXY := metricVelocityCovariantDerivativeAlong_smul
    (I := I) (M := M) cov h c t Z X Y x hZX
  rw [hscaleXYZ, hscaleYXZ, hscaleZXY] at hformula
  calc
    2 * (g t).inner x (A x (X x) (Y x)) (Z x) =
        c * metricVelocityCovariantDerivativeAlong
              (I := I) (M := M) cov h t X Y Z x +
          c * metricVelocityCovariantDerivativeAlong
              (I := I) (M := M) cov h t Y X Z x -
          c * metricVelocityCovariantDerivativeAlong
              (I := I) (M := M) cov h t Z X Y x := hformula
    _ = _ := by ring

/-- Differentiating Koszul's identity gives the metric-paired connection
variation identity. The hypothesis `hKoszulRhs` packages the time derivative
of the full spatial Koszul expression; this is the explicit mixed regularity
needed and is not a consequence of slicewise smoothness alone. -/
theorem hasDerivAt_koszul_connection_variation
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E)
      (V := (TangentSpace I : M → Type _)))
    (hcov : ∀ τ : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E)
      (V := (TangentSpace I : M → Type _)) (cov τ) 1)
    (hLevi : g.IsLeviCivita cov)
    (A : ∀ x : M, TM x → TM x → TM x)
    (hdot : ∀ x : M, TM x →ₗ[ℝ] TM x →ₗ[ℝ] ℝ)
    {t : ℝ}
    (hvariation : TimeDependentCovariantDerivative.HasConnectionTimeVariationAt
      (I := I) (M := M) cov A t)
    (hmetric : ∀ (x : M) (u v : TM x),
      HasDerivAt (fun τ : ℝ => (g τ).inner x u v) (hdot x u v) t)
    {X Y Z : Π x : M, TM x} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun y ↦ TotalSpace.mk' E y (X y)))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun y ↦ TotalSpace.mk' E y (Y y)))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun y ↦ TotalSpace.mk' E y (Z y)))
    (hKoszulRhs : HasDerivAt
      (fun τ : ℝ =>
        mvfderiv (I := I) (fun y ↦ (g τ).inner y (Y y) (Z y)) x (X x) +
        mvfderiv (I := I) (fun y ↦ (g τ).inner y (X y) (Z y)) x (Y x) -
        mvfderiv (I := I) (fun y ↦ (g τ).inner y (X y) (Y y)) x (Z x) -
        (g τ).inner x (X x) (VectorField.mlieBracket I Y Z x) +
        (g τ).inner x (Y x) (VectorField.mlieBracket I Z X x) +
        (g τ).inner x (Z x) (VectorField.mlieBracket I X Y x))
      (mvfderiv (I := I) (fun y ↦ hdot y (Y y) (Z y)) x (X x) +
        mvfderiv (I := I) (fun y ↦ hdot y (X y) (Z y)) x (Y x) -
        mvfderiv (I := I) (fun y ↦ hdot y (X y) (Y y)) x (Z x) -
        hdot x (X x) (VectorField.mlieBracket I Y Z x) +
        hdot x (Y x) (VectorField.mlieBracket I Z X x) +
        hdot x (Z x) (VectorField.mlieBracket I X Y x)) t) :
    2 * (hdot x ((cov t).along X Y x) (Z x) +
      (g t).inner x (A x (X x) (Y x)) (Z x)) =
      mvfderiv (I := I) (fun y ↦ hdot y (Y y) (Z y)) x (X x) +
      mvfderiv (I := I) (fun y ↦ hdot y (X y) (Z y)) x (Y x) -
      mvfderiv (I := I) (fun y ↦ hdot y (X y) (Y y)) x (Z x) -
      hdot x (X x) (VectorField.mlieBracket I Y Z x) +
      hdot x (Y x) (VectorField.mlieBracket I Z X x) +
      hdot x (Z x) (VectorField.mlieBracket I X Y x) := by
  have hXmd (y : M) : MDiffAt (T% X) y :=
    (hX y).mdifferentiableAt (by norm_num)
  have hYmd (y : M) : MDiffAt (T% Y) y :=
    (hY y).mdifferentiableAt (by norm_num)
  have hZmd (y : M) : MDiffAt (T% Z) y :=
    (hZ y).mdifferentiableAt (by norm_num)
  have hconn :=
    _root_.CovariantDerivative.TimeDependentCovariantDerivative.hasDerivAt_along_const_of_hasConnectionTimeVariationAt
      (I := I) (M := M) cov A hvariation X Y hXmd hYmd x
  have hpairConn :
      HasDerivAt
        (fun τ : ℝ => (g τ).inner x ((cov τ).along X Y x) (Z x))
        (hdot x ((cov t).along X Y x) (Z x) +
          (g t).inner x (A x (X x) (Y x)) (Z x)) t := by
    exact hasDerivAt_metricInner_left_of_pairwise_derivative
      (I := I) (M := M) g hdot hmetric x
      (fun τ => (cov τ).along X Y x)
      (A x (X x) (Y x)) (Z x) hconn

  let bYZ : TM x := VectorField.mlieBracket I Y Z x
  let bZX : TM x := VectorField.mlieBracket I Z X x
  let bXY : TM x := VectorField.mlieBracket I X Y x
  let rhs : ℝ → ℝ := fun τ =>
    mvfderiv (I := I) (fun y ↦ (g τ).inner y (Y y) (Z y)) x (X x) +
    mvfderiv (I := I) (fun y ↦ (g τ).inner y (X y) (Z y)) x (Y x) -
    mvfderiv (I := I) (fun y ↦ (g τ).inner y (X y) (Y y)) x (Z x) -
    (g τ).inner x (X x) bYZ +
    (g τ).inner x (Y x) bZX +
    (g τ).inner x (Z x) bXY
  have hrhs : HasDerivAt rhs
      (mvfderiv (I := I) (fun y ↦ hdot y (Y y) (Z y)) x (X x) +
        mvfderiv (I := I) (fun y ↦ hdot y (X y) (Z y)) x (Y x) -
        mvfderiv (I := I) (fun y ↦ hdot y (X y) (Y y)) x (Z x) -
        hdot x (X x) bYZ + hdot x (Y x) bZX + hdot x (Z x) bXY) t := by
    simpa [rhs, bYZ, bZX, bXY] using hKoszulRhs
  let lhs : ℝ → ℝ := fun τ =>
    2 * ((g τ).inner x ((cov τ).along X Y x) (Z x))
  have hlhs : HasDerivAt lhs
      (2 * (hdot x ((cov t).along X Y x) (Z x) +
        (g t).inner x (A x (X x) (Y x)) (Z x))) t := by
    simpa [lhs] using hpairConn.const_mul 2
  have hkoszul : ∀ τ : ℝ, lhs τ = rhs τ := by
    intro τ
    letI : RiemannianBundle TM := ⟨(g τ).toRiemannianMetric⟩
    have hinner (y : M) (u v : TM y) :
        (g τ).inner y u v = Inner.inner ℝ u v := rfl
    have hLeviτ : (cov τ).IsLeviCivita := hLevi τ
    have hk := _root_.CovariantDerivative.koszul_formula (I := I) (E := E) (M := M)
      (cov := cov τ) hLeviτ (x := x) hX hY hZ
    simpa [lhs, rhs, bYZ, bZX, bXY, hinner] using hk
  have hfun : lhs = rhs := funext hkoszul
  rw [hfun] at hlhs
  have hderiv := hlhs.unique hrhs
  simpa [bYZ, bZX, bXY] using hderiv

end CovariantDerivative.TimeDependentRiemannianMetric

end
