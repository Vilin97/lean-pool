/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Contractions
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.RaisedRicci
public import Mathlib.Tactic

/-!
# The three-dimensional curvature decomposition

This file proves the algebraic identity which writes a Riemann curvature
four-tensor in dimension three in terms of its Ricci contraction and scalar
curvature.  The geometric wrapper below uses the actual curvature commutator
and the actual Ricci trace; no curvature component is introduced by
definition.
-/

@[expose] public noncomputable section
open Bundle
open scoped BigOperators Manifold ContDiff

namespace CovariantDerivative

/-! The component proof is kept independent of manifolds so its finite
dimensional content is directly auditable. -/

theorem components_eq_threeDimensional_curvature
    (R : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ)
    (Ric : Fin 3 → Fin 3 → ℝ) (Scal : ℝ)
    (hskew : ∀ i j k l, R i j k l = -R j i k l)
    (hpair : ∀ i j k l, R i j k l = R k l i j)
    (hBianchi : ∀ i j k l, R i j k l + R j k i l + R k i j l = 0)
    (hRic : ∀ j k, Ric j k = ∑ i, R i j k i)
    (hScal : Scal = ∑ i, Ric i i)
    (a b c d : Fin 3) :
    R a b c d =
      Ric a d * (if b = c then 1 else 0) -
        Ric a c * (if b = d then 1 else 0) -
        Ric b d * (if a = c then 1 else 0) +
        Ric b c * (if a = d then 1 else 0) -
        Scal / 2 *
          ((if a = d then 1 else 0) * (if b = c then 1 else 0) -
            (if a = c then 1 else 0) * (if b = d then 1 else 0)) := by
  have hz (i k l : Fin 3) : R i i k l = 0 := by
    have h := hskew i i k l
    linarith
  have hlast (i j k l : Fin 3) : R i j k l = -R i j l k := by
    rw [hpair i j k l, hskew k l i j, ← hpair i j l k]
  have hzt (i j k : Fin 3) : R i j k k = 0 := by
    rw [hpair, hz]
  have hr00 := hRic 0 0
  have hr01 := hRic 0 1
  have hr02 := hRic 0 2
  have hr10 := hRic 1 0
  have hr11 := hRic 1 1
  have hr12 := hRic 1 2
  have hr20 := hRic 2 0
  have hr21 := hRic 2 1
  have hr22 := hRic 2 2
  have hb0120 := hBianchi 0 1 2 0
  have hb0121 := hBianchi 0 1 2 1
  have hb0122 := hBianchi 0 1 2 2
  have hb0210 := hBianchi 0 2 1 0
  have hb0211 := hBianchi 0 2 1 1
  have hb0212 := hBianchi 0 2 1 2
  have hb1020 := hBianchi 1 0 2 0
  have hb1021 := hBianchi 1 0 2 1
  have hb1022 := hBianchi 1 0 2 2
  have hb1200 := hBianchi 1 2 0 0
  have hb1201 := hBianchi 1 2 0 1
  have hb1202 := hBianchi 1 2 0 2
  have hb2010 := hBianchi 2 0 1 0
  have hb2011 := hBianchi 2 0 1 1
  have hb2012 := hBianchi 2 0 1 2
  have hb2100 := hBianchi 2 1 0 0
  have hb2101 := hBianchi 2 1 0 1
  have hb2102 := hBianchi 2 1 0 2
  simp only [Fin.sum_univ_succ] at hr00 hr01 hr02 hr10 hr11 hr12 hr20 hr21 hr22
  norm_num [hz, hzt, Fin.reduceFinMk, Fin.ext_iff] at hr00 hr01 hr02 hr10 hr11 hr12 hr20 hr21 hr22 hb0120 hb0121 hb0122 hb0210 hb0211 hb0212 hb1020 hb1021 hb1022 hb1200 hb1201 hb1202 hb2010 hb2011 hb2012 hb2100 hb2101 hb2102
  have hscal := hScal
  simp only [Fin.sum_univ_succ] at hscal
  norm_num [Fin.reduceFinMk, Fin.ext_iff] at hscal
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d
    <;> simp [hskew 1 0 0 0,
        hskew 1 0 0 1,
        hskew 1 0 0 2,
        hskew 1 0 1 0,
        hskew 1 0 1 1,
        hskew 1 0 1 2,
        hskew 1 0 2 0,
        hskew 1 0 2 1,
        hskew 1 0 2 2,
        hskew 2 0 0 0,
        hskew 2 0 0 1,
        hskew 2 0 0 2,
        hskew 2 0 1 0,
        hskew 2 0 1 1,
        hskew 2 0 1 2,
        hskew 2 0 2 0,
        hskew 2 0 2 1,
        hskew 2 0 2 2,
        hskew 2 1 0 0,
        hskew 2 1 0 1,
        hskew 2 1 0 2,
        hskew 2 1 1 0,
        hskew 2 1 1 1,
        hskew 2 1 1 2,
        hskew 2 1 2 0,
        hskew 2 1 2 1,
        hskew 2 1 2 2,
        hlast 0 0 1 0,
        hlast 0 1 1 0,
        hlast 0 2 1 0,
        hlast 1 0 1 0,
        hlast 1 1 1 0,
        hlast 1 2 1 0,
        hlast 2 0 1 0,
        hlast 2 1 1 0,
        hlast 2 2 1 0,
        hlast 0 0 2 0,
        hlast 0 1 2 0,
        hlast 0 2 2 0,
        hlast 1 0 2 0,
        hlast 1 1 2 0,
        hlast 1 2 2 0,
        hlast 2 0 2 0,
        hlast 2 1 2 0,
        hlast 2 2 2 0,
        hlast 0 0 2 1,
        hlast 0 1 2 1,
        hlast 0 2 2 1,
        hlast 1 0 2 1,
        hlast 1 1 2 1,
        hlast 1 2 2 1,
        hlast 2 0 2 1,
        hlast 2 1 2 1,
        hlast 2 2 2 1,
        hpair 0 2 0 1,
        hpair 1 2 0 1,
        hpair 1 2 0 2,
        hz, hzt, Fin.ext_iff] at *
    <;> linarith

private def lowerCurvature
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (R : V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] V) :
    V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] ℝ where
  toFun a :=
    { toFun := fun b =>
        { toFun := fun c =>
            innerₛₗ ℝ (R a b c)
          map_add' := by intro c d; ext z; simp
          map_smul' := by intro r c; ext z; simp }
      map_add' := by intro b c; ext z w; simp
      map_smul' := by intro r b; ext z w; simp }
  map_add' := by intro a b; ext c d z; simp
  map_smul' := by intro r a; ext c d z; simp

@[simp] private theorem lowerCurvature_apply
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (R : V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] V)
    (a b c d : V) :
    lowerCurvature R a b c d = inner ℝ (R a b c) d := rfl

theorem tensor_eq_threeDimensional_curvature
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (e : OrthonormalBasis (Fin 3) ℝ V)
    (R : V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (Ric : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Scal : ℝ)
    (hskew : ∀ a b c d, R a b c d = -R b a c d)
    (hpair : ∀ a b c d, R a b c d = R c d a b)
    (hBianchi : ∀ a b c d, R a b c d + R b c a d + R c a b d = 0)
    (hRic : ∀ j k, Ric (e j) (e k) = ∑ i, R (e i) (e j) (e k) (e i))
    (hScal : Scal = ∑ i, Ric (e i) (e i))
    (a b c d : V) :
    R a b c d =
      Ric a d * inner ℝ b c -
        Ric a c * inner ℝ b d -
        Ric b d * inner ℝ a c +
        Ric b c * inner ℝ a d -
        Scal / 2 *
          (inner ℝ a d * inner ℝ b c -
            inner ℝ a c * inner ℝ b d) := by
  have hc := components_eq_threeDimensional_curvature
    (fun i j k l => R (e i) (e j) (e k) (e l))
    (fun i j => Ric (e i) (e j)) Scal
    (fun i j k l => hskew (e i) (e j) (e k) (e l))
    (fun i j k l => hpair (e i) (e j) (e k) (e l))
    (fun i j k l => hBianchi (e i) (e j) (e k) (e l))
    hRic hScal
  rw [← e.sum_repr a, ← e.sum_repr b, ← e.sum_repr c, ← e.sum_repr d]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    Finset.sum_mul, Finset.mul_sum, inner_sum, sum_inner,
    inner_smul_left, inner_smul_right, conj_trivial, smul_eq_mul,
    e.inner_eq_ite]
  simp_rw [hc]
  simp only [Fin.sum_univ_three]
  norm_num [Fin.ext_iff]
  ring

private theorem pair_symmetry_of_bianchi
    {A : Type*} (R : A → A → A → A → ℝ)
    (hskew : ∀ a b c d, R a b c d = -R b a c d)
    (hlast : ∀ a b c d, R a b c d = -R a b d c)
    (hBianchi : ∀ a b c d, R a b c d + R b c a d + R c a b d = 0)
    (a b c d : A) : R a b c d = R c d a b := by
  linarith only [hBianchi a b c d, hBianchi a b d c,
    hBianchi a c d b, hBianchi b c d a,
    hskew c a b d, hlast a b d c, hskew d a b c,
    hlast a c d b, hskew d a c b, hlast a d c b,
    hlast b c d a, hlast c d b a, hskew d b c a, hlast b d c a]

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
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]
  [IsManifold I (minSmoothness ℝ 3) M]
  [IsManifold I ((2 : ℕ∞) + 1) M]

private theorem curvature_inner_pair_symmetry
    (hLevi : cov.IsLeviCivita) (x : M)
    (a b c d : TangentSpace I x) :
    inner ℝ (cov.curvatureTensor x a b c) d =
      inner ℝ (cov.curvatureTensor x c d a) b := by
  apply pair_symmetry_of_bianchi (fun a b c d =>
    inner ℝ (cov.curvatureTensor x a b c) d)
  · intro u v w z
    rw [curvatureTensor_swap (cov := cov) x u v w, inner_neg_left]
  · intro u v w z
    have h := curvatureTensor_inner_skew_adjoint_of_isMetricCompatibleTangent
      (covTM := cov) hLevi.2 x u v w z
    linarith [real_inner_comm w (cov.curvatureTensor x u v z)]
  · intro u v w z
    have h := congrArg (fun t : TangentSpace I x => inner ℝ t z)
      (firstBianchi_curvatureTensor_of_torsion_eq_zero
        (cov := cov) hLevi.1 x u v w)
    simpa only [inner_add_left, inner_zero_left] using h

/-- In dimension three, the actual Levi-Civita curvature tensor is determined
by its actual Ricci contraction and scalar curvature. -/
theorem curvature_inner_eq_threeDimensional_curvature
    (hLevi : cov.IsLeviCivita)
    (hdim : Module.finrank ℝ E = 3) (x : M)
    (a b c d : TangentSpace I x) :
    inner ℝ (cov.curvatureTensor x a b c) d =
      ricciCurvature (cov := cov) x a d * inner ℝ b c -
        ricciCurvature (cov := cov) x a c * inner ℝ b d -
        ricciCurvature (cov := cov) x b d * inner ℝ a c +
        ricciCurvature (cov := cov) x b c * inner ℝ a d -
        scalarCurvature (cov := cov) x / 2 *
          (inner ℝ a d * inner ℝ b c -
            inner ℝ a c * inner ℝ b d) := by
  let e : OrthonormalBasis (Fin 3) ℝ (TangentSpace I x) :=
    (stdOrthonormalBasis ℝ (TangentSpace I x)).reindex
      (finCongr (show Module.finrank ℝ (TangentSpace I x) = 3 from hdim))
  have h :=
    tensor_eq_threeDimensional_curvature
      (hskew := by
        intro u v w z
        simp only [lowerCurvature_apply]
        rw [curvatureTensor_swap (cov := cov) x u v w, inner_neg_left])
      (hpair := by
        intro u v w z
        exact curvature_inner_pair_symmetry cov hLevi x u v w z)
      (hBianchi := by
        intro u v w z
        have hB := firstBianchi_curvatureTensor_of_torsion_eq_zero
          (cov := cov) hLevi.1 x u v w
        have hB' := congrArg (fun t : TangentSpace I x => inner ℝ t z) hB
        simpa only [lowerCurvature_apply, inner_add_left, inner_zero_left] using hB')
      (hRic := by
        intro j k
        have hRic := ricciCurvature_eq_sum_curvature_orthonormalBasis
          cov x e (e j) (e k)
        simpa [lowerCurvature_apply, real_inner_comm] using hRic)
      (hScal := scalarCurvature_eq_sum_ricci_orthonormalBasis cov x e)
      e (lowerCurvature (cov.curvatureTensor x))
      (ricciCurvature (cov := cov) x) (scalarCurvature (cov := cov) x)
  simpa only [lowerCurvature_apply] using h a b c d

end Geometry

end CovariantDerivative
