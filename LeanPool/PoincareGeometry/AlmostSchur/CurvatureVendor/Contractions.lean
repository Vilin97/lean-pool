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

/- Adapted from Arthur Freitas Ramos's committed contracted-bianchi formalization.
Source commit: 12cebb809524d0cd185c6cd7bcb5b73d3562bce1
Source blob: bdd0708ef3bd896028b000907c5c7e801f1f6834
Source path: contracted-bianchi/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/Curvature/Contractions.lean
See PROVENANCE.json for the exact extraction and local changes. -/

public import LeanPool.PoincareGeometry.AlmostSchur.CurvatureVendor.Bianchi
public import Mathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.Geometry.Manifold.Riemannian.Basic
public import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
public import Mathlib.LinearAlgebra.Trace

/-!
# Ricci and scalar curvature

This file contracts the bundled curvature tensor on the tangent bundle to produce
Ricci curvature and scalar curvature.
-/

@[expose] public noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
  [cov.ContMDiffCovariantDerivative 1]

-- The source obtained this instance transitively from its LeviCivita module.
-- Keep it local to the extracted contraction proofs instead.
local instance curvatureVendorFiniteDimensional (x : M) :
    FiniteDimensional ℝ (TangentSpace I x) :=
  VectorBundle.finiteDimensional ℝ E (TangentSpace I : M → Type _) x

/-- The endomorphism whose trace defines Ricci curvature. -/
noncomputable def ricciEndomorphismAlmostSchur (x : M) (u w : TangentSpace I x) :
    TangentSpace I x →ₗ[ℝ] TangentSpace I x where
  toFun v := curvatureTensorAlmostSchur (cov := cov) x v u w
  map_add' v v' := by
    simpa using congrArg (fun f => f u w) ((curvatureTensorAlmostSchur (cov := cov) x).map_add v v')
  map_smul' c v := by
    simpa using congrArg (fun f => f u w) ((curvatureTensorAlmostSchur (cov := cov) x).map_smul c v)

@[simp]
lemma ricciEndomorphism_applyAlmostSchur (x : M) (u w v : TangentSpace I x) :
    ricciEndomorphismAlmostSchur (cov := cov) x u w v = curvatureTensorAlmostSchur (cov := cov) x v u w := rfl

@[simp]
lemma ricciEndomorphism_add_rightAlmostSchur (x : M) (u w w' : TangentSpace I x) :
    ricciEndomorphismAlmostSchur (cov := cov) x u (w + w') =
      ricciEndomorphismAlmostSchur (cov := cov) x u w + ricciEndomorphismAlmostSchur (cov := cov) x u w' := by
  ext v
  simpa [ricciEndomorphismAlmostSchur] using
    ((curvatureTensorAlmostSchur (cov := cov) x v u).map_add w w')

@[simp]
lemma ricciEndomorphism_smul_rightAlmostSchur (x : M) (u w : TangentSpace I x) (c : ℝ) :
    ricciEndomorphismAlmostSchur (cov := cov) x u (c • w) =
      c • ricciEndomorphismAlmostSchur (cov := cov) x u w := by
  ext v
  simpa [ricciEndomorphismAlmostSchur] using
    ((curvatureTensorAlmostSchur (cov := cov) x v u).map_smul c w)

@[simp]
lemma ricciEndomorphism_add_leftAlmostSchur (x : M) (u u' w : TangentSpace I x) :
    ricciEndomorphismAlmostSchur (cov := cov) x (u + u') w =
      ricciEndomorphismAlmostSchur (cov := cov) x u w + ricciEndomorphismAlmostSchur (cov := cov) x u' w := by
  ext v
  simpa [ricciEndomorphismAlmostSchur] using
    congrArg (fun f => f w) ((curvatureTensorAlmostSchur (cov := cov) x v).map_add u u')

@[simp]
lemma ricciEndomorphism_smul_leftAlmostSchur (x : M) (u w : TangentSpace I x) (c : ℝ) :
    ricciEndomorphismAlmostSchur (cov := cov) x (c • u) w =
      c • ricciEndomorphismAlmostSchur (cov := cov) x u w := by
  ext v
  simpa [ricciEndomorphismAlmostSchur] using
    congrArg (fun f => f w) ((curvatureTensorAlmostSchur (cov := cov) x v).map_smul c u)

/-- Ricci curvature obtained by tracing the first/output slots of the curvature tensor. -/
noncomputable def ricciCurvatureAlmostSchur (x : M) :
    TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ := by
  refine
    { toFun := fun u ↦
        { toFun := fun w ↦ LinearMap.trace ℝ (TangentSpace I x) (ricciEndomorphismAlmostSchur (cov := cov) x u w)
          map_add' := by
            intro w w'
            simpa [ricciEndomorphism_add_rightAlmostSchur] using
              (LinearMap.trace ℝ (TangentSpace I x)).map_add
                (ricciEndomorphismAlmostSchur (cov := cov) x u w)
                (ricciEndomorphismAlmostSchur (cov := cov) x u w')
          map_smul' := by
            intro c w
            simpa [ricciEndomorphism_smul_rightAlmostSchur] using
              (LinearMap.trace ℝ (TangentSpace I x)).map_smul c
                (ricciEndomorphismAlmostSchur (cov := cov) x u w) }
      map_add' := by
        intro u u'
        ext w
        simpa [ricciEndomorphism_add_leftAlmostSchur] using
          (LinearMap.trace ℝ (TangentSpace I x)).map_add
            (ricciEndomorphismAlmostSchur (cov := cov) x u w)
            (ricciEndomorphismAlmostSchur (cov := cov) x u' w)
      map_smul' := by
        intro c u
        ext w
        simpa [ricciEndomorphism_smul_leftAlmostSchur] using
          (LinearMap.trace ℝ (TangentSpace I x)).map_smul c
            (ricciEndomorphismAlmostSchur (cov := cov) x u w) }

@[simp]
lemma ricciCurvature_applyAlmostSchur (x : M) (u w : TangentSpace I x) :
    ricciCurvatureAlmostSchur (cov := cov) x u w =
      LinearMap.trace ℝ (TangentSpace I x) (ricciEndomorphismAlmostSchur (cov := cov) x u w) := rfl

/-- On a tangent fiber of dimension at most one, every curvature component vanishes. -/
lemma curvatureTensor_eq_zero_of_finrank_le_oneAlmostSchur
    (x : M) (hfin : Module.finrank ℝ (TangentSpace I x) ≤ 1)
    (u v w : TangentSpace I x) :
    curvatureTensorAlmostSchur (cov := cov) x u v w = 0 := by
  rcases (finrank_le_one_iff (K := ℝ) (V := TangentSpace I x)).1 hfin with
    ⟨e, hspan⟩
  rcases hspan u with ⟨cu, hcu⟩
  rcases hspan v with ⟨cv, hcv⟩
  rw [← hcu, ← hcv]
  calc
    curvatureTensorAlmostSchur (cov := cov) x (cu • e) (cv • e) w =
        cu • curvatureTensorAlmostSchur (cov := cov) x e (cv • e) w := by
      simpa using congrArg (fun f : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ]
          TangentSpace I x ↦ f (cv • e) w)
        ((curvatureTensorAlmostSchur (cov := cov) x).map_smul cu e)
    _ = cu • (cv • curvatureTensorAlmostSchur (cov := cov) x e e w) := by
      congr 1
      simpa using congrArg (fun f : TangentSpace I x →ₗ[ℝ] TangentSpace I x ↦ f w)
        ((curvatureTensorAlmostSchur (cov := cov) x e).map_smul cv e)
    _ = 0 := by simp

/-- On a zero-dimensional tangent fiber, every Ricci component vanishes. -/
lemma ricciCurvature_eq_zero_of_subsingleton_tangentAlmostSchur
    (x : M) [Subsingleton (TangentSpace I x)] (u w : TangentSpace I x) :
    ricciCurvatureAlmostSchur (cov := cov) x u w = 0 := by
  rw [ricciCurvature_applyAlmostSchur]
  have hEnd : ricciEndomorphismAlmostSchur (cov := cov) x u w = 0 := by
    ext v
    exact Subsingleton.elim _ _
  rw [hEnd]
  exact LinearMap.map_zero (LinearMap.trace ℝ (TangentSpace I x))

/-- On a tangent fiber of dimension at most one, every Ricci component vanishes. -/
lemma ricciCurvature_eq_zero_of_finrank_le_oneAlmostSchur
    (x : M) (hfin : Module.finrank ℝ (TangentSpace I x) ≤ 1)
    (u w : TangentSpace I x) :
    ricciCurvatureAlmostSchur (cov := cov) x u w = 0 := by
  rw [ricciCurvature_applyAlmostSchur]
  have hEnd : ricciEndomorphismAlmostSchur (cov := cov) x u w = 0 := by
    ext v
    exact curvatureTensor_eq_zero_of_finrank_le_oneAlmostSchur (cov := cov) x hfin v u w
  rw [hEnd]
  exact LinearMap.map_zero (LinearMap.trace ℝ (TangentSpace I x))

/-- Algebraic Ricci symmetry from first Bianchi plus pair symmetry of the Riemann curvature tensor.

This isolates the remaining Riemannian-curvature identity needed downstream: once the curvature
tensor has the usual pair symmetry, torsion-freeness turns the trace contraction into a symmetric
Ricci tensor. -/
theorem ricciCurvature_symm_of_curvature_inner_pair_symm_of_firstBianchiAlmostSchur
    (hBianchi : ∀ (x : M) (a b c : TangentSpace I x),
      curvatureTensorAlmostSchur (cov := cov) x a b c +
          curvatureTensorAlmostSchur (cov := cov) x b c a +
          curvatureTensorAlmostSchur (cov := cov) x c a b = 0)
    (hpair : ∀ (x : M) (a b c d : TangentSpace I x),
      inner ℝ (curvatureTensorAlmostSchur (cov := cov) x a b c) d =
        inner ℝ (curvatureTensorAlmostSchur (cov := cov) x c d a) b)
    (x : M) (u w : TangentSpace I x) :
    ricciCurvatureAlmostSchur (cov := cov) x u w = ricciCurvatureAlmostSchur (cov := cov) x w u := by
  let b : OrthonormalBasis (Fin (Module.finrank ℝ (TangentSpace I x))) ℝ
      (TangentSpace I x) :=
    stdOrthonormalBasis ℝ (TangentSpace I x)
  rw [ricciCurvature_applyAlmostSchur, ricciCurvature_applyAlmostSchur]
  rw [LinearMap.trace_eq_sum_inner _ b, LinearMap.trace_eq_sum_inner _ b]
  refine Finset.sum_congr rfl ?_
  intro i _
  let e : TangentSpace I x := b i
  have hInner := congrArg (fun z : TangentSpace I x => inner ℝ z e) (hBianchi x e u w)
  have hInner' :
      inner ℝ (curvatureTensorAlmostSchur (cov := cov) x e u w) e +
          inner ℝ (curvatureTensorAlmostSchur (cov := cov) x u w e) e +
          inner ℝ (curvatureTensorAlmostSchur (cov := cov) x w e u) e = 0 := by
    simpa only [inner_add_left, inner_zero_left] using hInner
  have hmiddle : inner ℝ (curvatureTensorAlmostSchur (cov := cov) x u w e) e = 0 := by
    calc
      inner ℝ (curvatureTensorAlmostSchur (cov := cov) x u w e) e
          = inner ℝ (curvatureTensorAlmostSchur (cov := cov) x e e u) w := hpair x u w e e
      _ = inner ℝ 0 w := by rw [curvatureTensor_selfAlmostSchur]
      _ = 0 := by simp
  have hthird :
      inner ℝ (curvatureTensorAlmostSchur (cov := cov) x w e u) e =
        - inner ℝ (curvatureTensorAlmostSchur (cov := cov) x e w u) e := by
    calc
      inner ℝ (curvatureTensorAlmostSchur (cov := cov) x w e u) e
          = inner ℝ (-curvatureTensorAlmostSchur (cov := cov) x e w u) e := by
            rw [curvatureTensor_swapAlmostSchur (cov := cov) x w e u]
      _ = - inner ℝ (curvatureTensorAlmostSchur (cov := cov) x e w u) e := by
            rw [inner_neg_left]
  have hterm :
      inner ℝ (curvatureTensorAlmostSchur (cov := cov) x e u w) e =
        inner ℝ (curvatureTensorAlmostSchur (cov := cov) x e w u) e := by
    rw [hmiddle, hthird] at hInner'
    linarith
  change inner ℝ (b i) (curvatureTensorAlmostSchur (cov := cov) x (b i) u w) =
    inner ℝ (b i) (curvatureTensorAlmostSchur (cov := cov) x (b i) w u)
  simpa [e, real_inner_comm] using hterm

/-- Torsion-free version of
`ricciCurvature_symm_of_curvature_inner_pair_symm_of_firstBianchiAlmostSchur`. -/
theorem ricciCurvature_symm_of_curvature_inner_pair_symm_of_torsion_eq_zeroAlmostSchur
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    (hT : cov.torsion = 0)
    (hpair : ∀ (x : M) (a b c d : TangentSpace I x),
      inner ℝ (curvatureTensorAlmostSchur (cov := cov) x a b c) d =
        inner ℝ (curvatureTensorAlmostSchur (cov := cov) x c d a) b)
    (x : M) (u w : TangentSpace I x) :
    ricciCurvatureAlmostSchur (cov := cov) x u w = ricciCurvatureAlmostSchur (cov := cov) x w u := by
  exact ricciCurvature_symm_of_curvature_inner_pair_symm_of_firstBianchiAlmostSchur
    (cov := cov)
    (fun x a b c =>
      firstBianchi_curvatureTensor_of_torsion_eq_zeroAlmostSchur (cov := cov) hT x a b c)
    hpair x u w

/-- Algebraic Ricci symmetry from first Bianchi plus skew-adjointness of each curvature operator.

This is the metric-compatibility-facing version of the Ricci-symmetry bridge: for a
metric-compatible tangent connection, the remaining geometric identity should be the
skew-adjointness of `R(a,b)` with respect to the metric. -/
theorem ricciCurvature_symm_of_curvature_inner_skew_adjoint_of_firstBianchiAlmostSchur
    (hBianchi : ∀ (x : M) (a b c : TangentSpace I x),
      curvatureTensorAlmostSchur (cov := cov) x a b c +
          curvatureTensorAlmostSchur (cov := cov) x b c a +
          curvatureTensorAlmostSchur (cov := cov) x c a b = 0)
    (hskew : ∀ (x : M) (a b c d : TangentSpace I x),
      inner ℝ (curvatureTensorAlmostSchur (cov := cov) x a b c) d +
        inner ℝ c (curvatureTensorAlmostSchur (cov := cov) x a b d) = 0)
    (x : M) (u w : TangentSpace I x) :
    ricciCurvatureAlmostSchur (cov := cov) x u w = ricciCurvatureAlmostSchur (cov := cov) x w u := by
  let b : OrthonormalBasis (Fin (Module.finrank ℝ (TangentSpace I x))) ℝ
      (TangentSpace I x) :=
    stdOrthonormalBasis ℝ (TangentSpace I x)
  rw [ricciCurvature_applyAlmostSchur, ricciCurvature_applyAlmostSchur]
  rw [LinearMap.trace_eq_sum_inner _ b, LinearMap.trace_eq_sum_inner _ b]
  refine Finset.sum_congr rfl ?_
  intro i _
  let e : TangentSpace I x := b i
  have hInner := congrArg (fun z : TangentSpace I x => inner ℝ z e) (hBianchi x e u w)
  have hInner' :
      inner ℝ (curvatureTensorAlmostSchur (cov := cov) x e u w) e +
          inner ℝ (curvatureTensorAlmostSchur (cov := cov) x u w e) e +
          inner ℝ (curvatureTensorAlmostSchur (cov := cov) x w e u) e = 0 := by
    simpa only [inner_add_left, inner_zero_left] using hInner
  have hmiddle : inner ℝ (curvatureTensorAlmostSchur (cov := cov) x u w e) e = 0 := by
    have h := hskew x u w e e
    have hcomm :
        inner ℝ e (curvatureTensorAlmostSchur (cov := cov) x u w e) =
          inner ℝ (curvatureTensorAlmostSchur (cov := cov) x u w e) e :=
      real_inner_comm (curvatureTensorAlmostSchur (cov := cov) x u w e) e
    linarith
  have hthird :
      inner ℝ (curvatureTensorAlmostSchur (cov := cov) x w e u) e =
        - inner ℝ (curvatureTensorAlmostSchur (cov := cov) x e w u) e := by
    calc
      inner ℝ (curvatureTensorAlmostSchur (cov := cov) x w e u) e
          = inner ℝ (-curvatureTensorAlmostSchur (cov := cov) x e w u) e := by
            rw [curvatureTensor_swapAlmostSchur (cov := cov) x w e u]
      _ = - inner ℝ (curvatureTensorAlmostSchur (cov := cov) x e w u) e := by
            rw [inner_neg_left]
  have hterm :
      inner ℝ (curvatureTensorAlmostSchur (cov := cov) x e u w) e =
        inner ℝ (curvatureTensorAlmostSchur (cov := cov) x e w u) e := by
    rw [hmiddle, hthird] at hInner'
    linarith
  change inner ℝ (b i) (curvatureTensorAlmostSchur (cov := cov) x (b i) u w) =
    inner ℝ (b i) (curvatureTensorAlmostSchur (cov := cov) x (b i) w u)
  simpa [e, real_inner_comm] using hterm

/-- Torsion-free version of
`ricciCurvature_symm_of_curvature_inner_skew_adjoint_of_firstBianchiAlmostSchur`. -/
theorem ricciCurvature_symm_of_curvature_inner_skew_adjoint_of_torsion_eq_zeroAlmostSchur
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    (hT : cov.torsion = 0)
    (hskew : ∀ (x : M) (a b c d : TangentSpace I x),
      inner ℝ (curvatureTensorAlmostSchur (cov := cov) x a b c) d +
        inner ℝ c (curvatureTensorAlmostSchur (cov := cov) x a b d) = 0)
    (x : M) (u w : TangentSpace I x) :
    ricciCurvatureAlmostSchur (cov := cov) x u w = ricciCurvatureAlmostSchur (cov := cov) x w u := by
  exact ricciCurvature_symm_of_curvature_inner_skew_adjoint_of_firstBianchiAlmostSchur
    (cov := cov)
    (fun x a b c =>
      firstBianchi_curvatureTensor_of_torsion_eq_zeroAlmostSchur (cov := cov) hT x a b c)
    hskew x u w

/-- Torsion-free metric-compatible tangent connections have symmetric Ricci curvature. -/
theorem ricciCurvature_symm_of_metricCompatibleTangent_of_torsion_eq_zeroAlmostSchur
    [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    (hT : cov.torsion = 0)
    (hmetric : cov.IsMetricCompatibleTangentAlmostSchur)
    (x : M) (u w : TangentSpace I x) :
    ricciCurvatureAlmostSchur (cov := cov) x u w = ricciCurvatureAlmostSchur (cov := cov) x w u := by
  exact ricciCurvature_symm_of_curvature_inner_skew_adjoint_of_torsion_eq_zeroAlmostSchur
    (cov := cov) hT
    (fun x a b c d =>
      curvatureTensor_inner_skew_adjoint_of_isMetricCompatibleTangentAlmostSchur
        (covTM := cov) hmetric x a b c d)
    x u w

/-- Scalar curvature obtained by tracing Ricci curvature against an orthonormal basis. -/
noncomputable def scalarCurvatureAlmostSchur (x : M) : ℝ := by
  letI : FiniteDimensional ℝ (TangentSpace I x) :=
    VectorBundle.finiteDimensional ℝ E (TangentSpace I : M → Type _) x
  exact
    ∑ i : Fin (Module.finrank ℝ (TangentSpace I x)),
      ricciCurvatureAlmostSchur (cov := cov) x
        ((stdOrthonormalBasis ℝ (TangentSpace I x)) i)
        ((stdOrthonormalBasis ℝ (TangentSpace I x)) i)

lemma scalarCurvature_eq_sumAlmostSchur (x : M) :
    scalarCurvatureAlmostSchur (cov := cov) x =
      (by
        letI : FiniteDimensional ℝ (TangentSpace I x) :=
          VectorBundle.finiteDimensional ℝ E (TangentSpace I : M → Type _) x
        exact
          ∑ i : Fin (Module.finrank ℝ (TangentSpace I x)),
            ricciCurvatureAlmostSchur (cov := cov) x
              ((stdOrthonormalBasis ℝ (TangentSpace I x)) i)
              ((stdOrthonormalBasis ℝ (TangentSpace I x)) i)) := by
  letI : FiniteDimensional ℝ (TangentSpace I x) :=
    VectorBundle.finiteDimensional ℝ E (TangentSpace I : M → Type _) x
  rfl

/-- On a zero-dimensional tangent fiber, scalar curvature vanishes. -/
lemma scalarCurvature_eq_zero_of_subsingleton_tangentAlmostSchur
    (x : M) [Subsingleton (TangentSpace I x)] :
    scalarCurvatureAlmostSchur (cov := cov) x = 0 := by
  rw [scalarCurvature_eq_sumAlmostSchur]
  simp [ricciCurvature_eq_zero_of_subsingleton_tangentAlmostSchur (cov := cov) x]


end CovariantDerivative
