/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.ConnectionChange
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.TangentFrameCoordinate

/-!
# Local-frame coordinates for vector-valued bilinear tensors

This module gives the coordinate product rule for a vector-valued bilinear
tangent tensor.  It retains all three connection-coefficient corrections:
the two moving tensor inputs and the moving output frame.
-/

@[expose] public noncomputable section
open Bundle FiberBundle
open scoped Manifold ContDiff BigOperators

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [SigmaCompactSpace M]

local notation "TM" => (TangentSpace I : M → Type _)
local notation "TCorr" =>
  (fun x : M => TM x →L[ℝ] TM x →L[ℝ] TM x)

/-- Reconstructing a tangent vector from its coefficients in a genuine local
frame. -/
private theorem localFrame_eq_sum_localFrameCoeff_smul
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) {x : M} (hx : x ∈ e.baseSet)
    (z : TM x) :
    z = ∑ i, e.localFrameCoeff I b i x z • e.localFrame b i x := by
  simpa using
    (e.eq_sum_localFrameCoeff_smul (I := I) (b := b)
      (s := FiberBundle.extend E z) (x' := x) hx)

/-- The directional derivative of a local output coefficient of
`A(F_j, F_i)`.  The first term is the corresponding coefficient of the
induced covariant derivative of `A`; the next two sums correct the moving
inputs, and the final sum corrects the moving output frame. -/
theorem mvfderiv_localFrameCoeff_vectorValuedBilinear_apply_eq_covariantDerivative_add_connection
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) (cov : CovariantDerivative I E TM)
    {A : ∀ y : M, TCorr y} {x : M} (hx : x ∈ e.baseSet)
    (u : TM x) (k i j : ι)
    (hA : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] E)) (E := TCorr) y (A y)) x) :
    mvfderiv (I := I) (fun y =>
        e.localFrameCoeff I b k y
          (A y (e.localFrame b j y) (e.localFrame b i y))) x u =
      e.localFrameCoeff I b k x
        (covariantDerivativeOneForm cov A x u
          (e.localFrame b j x) (e.localFrame b i x)) +
        (∑ p, e.localFrameCoeff I b p x
            (cov (e.localFrame b i) x u) *
          e.localFrameCoeff I b k x
            (A x (e.localFrame b j x) (e.localFrame b p x))) +
        (∑ p, e.localFrameCoeff I b p x
            (cov (e.localFrame b j) x u) *
          e.localFrameCoeff I b k x
            (A x (e.localFrame b p x) (e.localFrame b i x)) -
          ∑ p, e.localFrameCoeff I b p x
            (A x (e.localFrame b j x) (e.localFrame b i x)) *
          e.localFrameCoeff I b k x
            (cov (e.localFrame b p) x u)) := by
  have hframe (q : ι) : MDiffAt (T% (e.localFrame b q)) x :=
    (contMDiffAt_localFrame_of_mem (I := I) (e := e) (b := b)
      (n := 1) (i := q) (hx := hx)).mdifferentiableAt one_ne_zero
  have hS : MDiffAt (T% (fun y =>
      A y (e.localFrame b j y) (e.localFrame b i y))) x :=
    (hA.clm_bundle_apply (hframe j)).clm_bundle_apply (hframe i)
  have hraw := TangentFrame.localFrameCoeff_covariantDerivative_eq_mvfderiv_add_connection
    (I := I) e b cov hx hS u k
  have hDAraw := covariantDerivativeOneForm_apply_eq_along
    (I := I) cov A
      (X := smoothExtend (I := I) (F := E) (V := TM) x u)
      (Y := e.localFrame b i) (Z := e.localFrame b j) hA (hframe i) (hframe j)
  have hDA :
      cov (fun y => A y (e.localFrame b j y) (e.localFrame b i y)) x u =
        covariantDerivativeOneForm cov A x u
          (e.localFrame b j x) (e.localFrame b i x) +
          A x (e.localFrame b j x) (cov (e.localFrame b i) x u) +
          A x (cov (e.localFrame b j) x u) (e.localFrame b i x) := by
    have hDAexpanded :
        covariantDerivativeOneForm cov A x u
            (e.localFrame b j x) (e.localFrame b i x) =
          cov (fun y => A y (e.localFrame b j y) (e.localFrame b i y)) x u -
            A x (e.localFrame b j x) (cov (e.localFrame b i) x u) -
            A x (cov (e.localFrame b j) x u) (e.localFrame b i x) := by
      simpa only [covariantDerivativeOneFormAlong, CovariantDerivative.along,
        smoothExtend_apply] using hDAraw
    rw [hDAexpanded]
    abel
  have hAfi :
      A x (e.localFrame b j x) (cov (e.localFrame b i) x u) =
        ∑ p, e.localFrameCoeff I b p x
          (cov (e.localFrame b i) x u) •
          A x (e.localFrame b j x) (e.localFrame b p x) := by
    conv_lhs =>
      rw [localFrame_eq_sum_localFrameCoeff_smul (I := I) (e := e) b hx
        (cov (e.localFrame b i) x u)]
    simp only [map_sum, map_smul]
  have hAfj :
      A x (cov (e.localFrame b j) x u) (e.localFrame b i x) =
        ∑ p, e.localFrameCoeff I b p x
          (cov (e.localFrame b j) x u) •
          A x (e.localFrame b p x) (e.localFrame b i x) := by
    conv_lhs =>
      rw [localFrame_eq_sum_localFrameCoeff_smul (I := I) (e := e) b hx
        (cov (e.localFrame b j) x u)]
    simp only [map_sum, map_smul, sum_apply, smul_apply]
  have hCfi : e.localFrameCoeff I b k x
      (A x (e.localFrame b j x) (cov (e.localFrame b i) x u)) =
      ∑ p, e.localFrameCoeff I b p x
          (cov (e.localFrame b i) x u) *
        e.localFrameCoeff I b k x
          (A x (e.localFrame b j x) (e.localFrame b p x)) := by
    rw [hAfi]
    simp only [map_sum, map_smul, smul_eq_mul]
  have hCfj : e.localFrameCoeff I b k x
      (A x (cov (e.localFrame b j) x u) (e.localFrame b i x)) =
      ∑ p, e.localFrameCoeff I b p x
          (cov (e.localFrame b j) x u) *
        e.localFrameCoeff I b k x
          (A x (e.localFrame b p x) (e.localFrame b i x)) := by
    rw [hAfj]
    simp only [map_sum, map_smul, smul_eq_mul]
  have hcov : e.localFrameCoeff I b k x
      (cov (fun y => A y (e.localFrame b j y) (e.localFrame b i y)) x u) =
      e.localFrameCoeff I b k x
        (covariantDerivativeOneForm cov A x u
          (e.localFrame b j x) (e.localFrame b i x)) +
        (∑ p, e.localFrameCoeff I b p x
            (cov (e.localFrame b i) x u) *
          e.localFrameCoeff I b k x
            (A x (e.localFrame b j x) (e.localFrame b p x))) +
        ∑ p, e.localFrameCoeff I b p x
            (cov (e.localFrame b j) x u) *
          e.localFrameCoeff I b k x
            (A x (e.localFrame b p x) (e.localFrame b i x)) := by
    rw [hDA]
    simp only [map_add]
    rw [hCfi, hCfj]
  linarith [hraw, hcov]

end CovariantDerivative
