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

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Contractions
public import Mathlib.Tactic

/-!
# The three-dimensional Einstein curvature identity

The first part proves independent pointwise algebra. The convention is
`R i j k l = ⟪R(eᵢ,eⱼ)eₖ,eₗ⟫`, so Ricci contracts the first and fourth slots.
The Einstein factor is twice the sectional curvature. In dimension three, skewness
in the first pair and pair symmetry suffice; first Bianchi is not needed for this implication.

The geometric wrappers use actual Levi-Civita curvature and Ricci from Contractions,
deriving pair symmetry from metric compatibility and first Bianchi. They prove that
an Einstein point in dimension three has sectional curvature equal to half its
Einstein factor. Global constancy of that factor is a separate Schur theorem.
-/

@[expose] public noncomputable section
open scoped BigOperators

namespace SchurThreeDimensional

/-- The algebraic three-dimensional Einstein identity, in an orthonormal frame.
The contraction convention agrees with `CovariantDerivative.ricciCurvature`.
No smoothness, connection, or manifold conclusion is asserted here. -/
theorem components_eq_constant_curvature
    (R : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) (κ : ℝ)
    (hskew : ∀ i j k l, R i j k l = -R j i k l)
    (hpair : ∀ i j k l, R i j k l = R k l i j)
    (hRic : ∀ j k, ∑ i, R i j k i = if j = k then κ else 0)
    (a b c d : Fin 3) :
    R a b c d = κ / 2 *
      ((if a = d then 1 else 0) * (if b = c then 1 else 0) -
       (if a = c then 1 else 0) * (if b = d then 1 else 0)) := by
  have hz (i k l : Fin 3) : R i i k l = 0 := by
    have := hskew i i k l
    linarith
  have ht (i j k l : Fin 3) : R i j k l = -R i j l k := by
    rw [hpair i j k l, hskew k l i j, ← hpair i j l k]
  have hzt (i j k : Fin 3) : R i j k k = 0 := by
    rw [hpair, hz]
  have hd0 := hRic 0 0
  have hd1 := hRic 1 1
  have hd2 := hRic 2 2
  have ho01 := hRic 0 1
  have ho02 := hRic 0 2
  have ho12 := hRic 1 2
  simp only [Fin.sum_univ_succ] at hd0 hd1 hd2 ho01 ho02 ho12
  norm_num [hz, hzt, Fin.reduceFinMk, Fin.ext_iff] at hd0 hd1 hd2 ho01 ho02 ho12
  have h01 : R 0 1 1 0 = κ / 2 := by
    linarith [hpair 1 0 0 1, hpair 2 0 0 2, hpair 2 1 1 2]
  have h02 : R 0 2 2 0 = κ / 2 := by
    linarith [hpair 1 0 0 1, hpair 2 0 0 2, hpair 2 1 1 2]
  have h12 : R 1 2 2 1 = κ / 2 := by
    linarith [hpair 1 0 0 1, hpair 2 0 0 2, hpair 2 1 1 2]
  have ht01 (i j) := ht i j 0 1
  have ht02 (i j) := ht i j 0 2
  have ht12 (i j) := ht i j 1 2
  have hm01 : R 0 1 2 0 = 0 := ho12
  have hm02 : R 0 1 2 1 = 0 := by
    linarith only [ho02, hskew 1 0 2 1]
  have hm12 : R 0 2 2 1 = 0 := by
    linarith only [ho01, hskew 2 0 1 2, ht 0 2 1 2]
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d
    <;> simp [hz, hzt, hskew 1 0, hskew 2 0, hskew 2 1,
      ht01, ht02, ht12, hpair 0 2 1 0, hpair 1 2 1 0, hpair 1 2 2 0,
      h01, h02, h12, hm01, hm02, hm12, Fin.ext_iff]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Basis-independent four-linear version of the three-dimensional Einstein identity.
An orthonormal basis indexed by `Fin 3` supplies exactly the dimension hypothesis.
The Ricci hypothesis is required only on basis vectors. -/
theorem tensor_eq_constant_curvature
    (e : OrthonormalBasis (Fin 3) ℝ V)
    (R : V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (κ : ℝ)
    (hskew : ∀ a b c d, R a b c d = -R b a c d)
    (hpair : ∀ a b c d, R a b c d = R c d a b)
    (hRic : ∀ j k, ∑ i, R (e i) (e j) (e k) (e i) =
      if j = k then κ else 0)
    (a b c d : V) :
    R a b c d = κ / 2 *
      (inner ℝ a d * inner ℝ b c - inner ℝ a c * inner ℝ b d) := by
  have hc := components_eq_constant_curvature
    (fun i j k l => R (e i) (e j) (e k) (e l)) κ
    (fun i j k l => hskew (e i) (e j) (e k) (e l))
    (fun i j k l => hpair (e i) (e j) (e k) (e l)) hRic
  rw [← e.sum_repr a, ← e.sum_repr b, ← e.sum_repr c, ← e.sum_repr d]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    Finset.sum_mul, Finset.mul_sum, inner_sum, sum_inner,
    inner_smul_left, inner_smul_right, conj_trivial, smul_eq_mul,
    e.inner_eq_ite]
  simp_rw [hc]
  simp only [Fin.sum_univ_succ]
  norm_num [Fin.ext_iff]
  ring

/-- The sectional numerator identity for arbitrary vectors, including degenerate planes. -/
theorem sectional_numerator_eq
    (e : OrthonormalBasis (Fin 3) ℝ V)
    (R : V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (κ : ℝ)
    (hskew : ∀ a b c d, R a b c d = -R b a c d)
    (hpair : ∀ a b c d, R a b c d = R c d a b)
    (hRic : ∀ j k, ∑ i, R (e i) (e j) (e k) (e i) =
      if j = k then κ else 0)
    (a b : V) :
    R a b b a = κ / 2 *
      (inner ℝ a a * inner ℝ b b - (inner ℝ a b) ^ 2) := by
  rw [tensor_eq_constant_curvature e R κ hskew hpair hRic]
  rw [real_inner_comm b a, pow_two]

/-- Pair interchange follows algebraically from the two skew symmetries and first Bianchi. -/
theorem pair_symmetry_of_bianchi {A : Type*}
    (R : A → A → A → A → ℝ)
    (hskew : ∀ a b c d, R a b c d = -R b a c d)
    (hlast : ∀ a b c d, R a b c d = -R a b d c)
    (hBianchi : ∀ a b c d, R a b c d + R b c a d + R c a b d = 0)
    (a b c d : A) : R a b c d = R c d a b := by
  linarith only [hBianchi a b c d, hBianchi a b d c,
    hBianchi a c d b, hBianchi b c d a,
    hskew c a b d, hlast a b d c, hskew d a b c,
    hlast a c d b, hskew d a c b, hlast a d c b,
    hlast b c d a, hlast c d b a, hskew d b c a, hlast b d c a]

/-- Lower the output of a trilinear curvature operator using the real inner product. -/
def lowerCurvature (R : V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] V) :
    V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] ℝ where
  toFun a :=
    { toFun := fun b =>
        { toFun := fun c => innerₛₗ ℝ (R a b c)
          map_add' := by intro c d; ext z; simp
          map_smul' := by intro r c; ext z; simp }
      map_add' := by intro b c; ext z w; simp
      map_smul' := by intro r b; ext z w; simp }
  map_add' := by intro a b; ext c d z; simp
  map_smul' := by intro r a; ext c d z; simp

@[simp] theorem lowerCurvature_apply
    (R : V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] V) (a b c d : V) :
    lowerCurvature R a b c d = inner ℝ (R a b c) d := rfl

section Geometry

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
  [cov.ContMDiffCovariantDerivative 1]

/-- Sectional curvature of an actual tangent connection on a nondegenerate two-plane.
This is the usual curvature numerator divided by its Gram determinant. The small
contracted-Bianchi project does not import the larger project's Sectional module. -/
def sectionalCurvature (x : M) (a b : TangentSpace I x)
    (_h : inner ℝ a a * inner ℝ b b - (inner ℝ a b) ^ 2 ≠ 0) : ℝ :=
  inner ℝ (cov.curvatureTensor x a b b) a /
    (inner ℝ a a * inner ℝ b b - (inner ℝ a b) ^ 2)

variable [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]
  [IsManifold I (minSmoothness ℝ 3) M]
  [IsManifold I ((2 : ℕ∞) + 1) M]

/-- Actual Levi-Civita curvature has pair interchange symmetry. All algebraic
symmetries are derived from metric compatibility and torsion-freeness. -/
theorem curvature_inner_pair_symmetry
    (hLevi : cov.IsLeviCivita) (x : M) (a b c d : TangentSpace I x) :
    inner ℝ (cov.curvatureTensor x a b c) d =
      inner ℝ (cov.curvatureTensor x c d a) b := by
  apply pair_symmetry_of_bianchi (fun a b c d =>
    inner ℝ (cov.curvatureTensor x a b c) d)
  · intro u v w z
    rw [CovariantDerivative.curvatureTensor_swap (cov := cov) x u v w,
      inner_neg_left]
  · intro u v w z
    have h := CovariantDerivative.curvatureTensor_inner_skew_adjoint_of_isMetricCompatibleTangent
      (covTM := cov) hLevi.2 x u v w z
    linarith [real_inner_comm w (cov.curvatureTensor x u v z)]
  · intro u v w z
    have h := congrArg (fun t : TangentSpace I x => inner ℝ t z)
      (cov.firstBianchi_curvatureTensor_of_torsion_eq_zero hLevi.1 x u v w)
    simpa only [inner_add_left, inner_zero_left] using h

/-- In dimension three, pointwise Einstein Ricci determines the full actual
Levi-Civita curvature tensor. The Einstein factor is supplied at this point;
no constancy across the manifold is assumed or concluded. -/
theorem curvature_inner_eq_of_einstein
    (hLevi : cov.IsLeviCivita) (hdim : Module.finrank ℝ E = 3)
    (x : M) (κ : ℝ)
    (hEinstein : ∀ u v : TangentSpace I x,
      cov.ricciCurvature x u v = κ * inner ℝ u v)
    (a b c d : TangentSpace I x) :
    inner ℝ (cov.curvatureTensor x a b c) d =
      κ / 2 * (inner ℝ a d * inner ℝ b c - inner ℝ a c * inner ℝ b d) := by
  let e : OrthonormalBasis (Fin 3) ℝ (TangentSpace I x) :=
    (stdOrthonormalBasis ℝ (TangentSpace I x)).reindex
      (finCongr (show Module.finrank ℝ (TangentSpace I x) = 3 from hdim))
  apply tensor_eq_constant_curvature e (lowerCurvature (cov.curvatureTensor x)) κ
  · intro u v w z
    simp only [lowerCurvature_apply]
    rw [CovariantDerivative.curvatureTensor_swap (cov := cov) x u v w,
      inner_neg_left]
  · intro u v w z
    exact curvature_inner_pair_symmetry cov hLevi x u v w z
  · intro j k
    have h := hEinstein (e j) (e k)
    rw [CovariantDerivative.ricciCurvature_apply,
      LinearMap.trace_eq_sum_inner _ e] at h
    simpa [lowerCurvature_apply, CovariantDerivative.ricciEndomorphism_apply,
      real_inner_comm, e.inner_eq_ite, mul_ite] using h

/-- The actual sectional numerator equals half the Einstein factor times the Gram
determinant, also for degenerate pairs. -/
theorem curvature_sectional_numerator_eq_of_einstein
    (hLevi : cov.IsLeviCivita) (hdim : Module.finrank ℝ E = 3)
    (x : M) (κ : ℝ)
    (hEinstein : ∀ u v : TangentSpace I x,
      cov.ricciCurvature x u v = κ * inner ℝ u v)
    (a b : TangentSpace I x) :
    inner ℝ (cov.curvatureTensor x a b b) a =
      κ / 2 * (inner ℝ a a * inner ℝ b b - (inner ℝ a b) ^ 2) := by
  rw [curvature_inner_eq_of_einstein cov hLevi hdim x κ hEinstein]
  rw [real_inner_comm b a, pow_two]

/-- Every nondegenerate tangent two-plane has sectional curvature κ/2 at a
three-dimensional Einstein point of a Levi-Civita connection. -/
theorem sectionalCurvature_eq_of_einstein
    (hLevi : cov.IsLeviCivita) (hdim : Module.finrank ℝ E = 3)
    (x : M) (κ : ℝ)
    (hEinstein : ∀ u v : TangentSpace I x,
      cov.ricciCurvature x u v = κ * inner ℝ u v)
    (a b : TangentSpace I x)
    (hne : inner ℝ a a * inner ℝ b b - (inner ℝ a b) ^ 2 ≠ 0) :
    sectionalCurvature cov x a b hne = κ / 2 := by
  unfold sectionalCurvature
  rw [curvature_sectional_numerator_eq_of_einstein cov hLevi hdim x κ hEinstein]
  exact mul_div_cancel_right₀ _ hne

end Geometry


end SchurThreeDimensional
