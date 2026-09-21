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

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita

/-!
# Metric-defect coordinates in an orthonormal local frame

This module records the first-order local-frame identity which converts the
ordinary derivative of a Gram coefficient into the metric defect and the two
connection-coefficient terms caused by the moving frame.
-/

@[expose] public noncomputable section
open Bundle FiberBundle
open scoped Manifold ContDiff

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]

local notation "TM" => (TangentSpace I : M → Type _)

/-- At an orthonormal frame value, the corresponding local-frame coordinate
is the Riemannian inner product with that frame vector. -/
theorem localFrameCoeff_eq_inner_of_orthonormal
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) {x : M} (hx : x ∈ e.baseSet)
    (horth : ∀ i j : ι,
      inner ℝ (e.localFrame b i x) (e.localFrame b j x) =
        if i = j then 1 else 0)
    (k : ι) (z : TM x) :
    e.localFrameCoeff I b k x z = inner ℝ (e.localFrame b k x) z := by
  have hcoeff : e.localFrameCoeff I b k x z = (e.basisAt b hx).repr z k := by
    simpa using
      (Bundle.Trivialization.localFrameCoeff_apply_of_mem_baseSet
        (I := I) (e := e) (b := b) hx (FiberBundle.extend E z) k)
  have horthBasis (i : ι) :
      inner ℝ ((e.basisAt b hx) k) ((e.basisAt b hx) i) =
        if k = i then 1 else 0 := by
    simpa [Bundle.Trivialization.localFrame_apply_of_mem_baseSet (e := e) (b := b) hx]
      using horth k i
  calc
    e.localFrameCoeff I b k x z = (e.basisAt b hx).repr z k := hcoeff
    _ = inner ℝ (e.localFrame b k x) z := by
      rw [Bundle.Trivialization.localFrame_apply_of_mem_baseSet (e := e) (b := b) hx]
      conv_rhs => rw [← (e.basisAt b hx).sum_repr z]
      rw [inner_sum]
      simp only [real_inner_smul_right]
      simp [horthBasis]

/-- The ordinary directional derivative of a local Gram coefficient equals
the metric defect plus the two connection coefficients of the moving local
frame.  The convention on the right is
`Γ p i = coeff p (∇_u F_i)`. -/
theorem mvfderiv_localFrameGramMatrix_apply_eq_metricDefect_add_connection
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (cov : CovariantDerivative I E TM)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) {x : M} (hx : x ∈ e.baseSet)
    (u : TM x) (i j : ι)
    (horth : ∀ p q : ι,
      inner ℝ (e.localFrame b p x) (e.localFrame b q x) =
        if p = q then 1 else 0) :
    mvfderiv (I := I)
        (fun y => localFrameGramMatrix (I := I) e b y i j) x u =
      cov.metricDefect x (e.localFrame b i x) (e.localFrame b j x) u +
        e.localFrameCoeff I b j x (cov (e.localFrame b i) x u) +
        e.localFrameCoeff I b i x (cov (e.localFrame b j) x u) := by
  have hFi : MDiffAt (T% (e.localFrame b i)) x :=
    (contMDiffAt_localFrame_of_mem (I := I) (e := e) (b := b)
      (n := 1) (i := i) (hx := hx)).mdifferentiableAt one_ne_zero
  have hFj : MDiffAt (T% (e.localFrame b j)) x :=
    (contMDiffAt_localFrame_of_mem (I := I) (e := e) (b := b)
      (n := 1) (i := j) (hx := hx)).mdifferentiableAt one_ne_zero
  have hdef := congrArg (fun L : TM x →L[ℝ] ℝ => L u)
    (cov.metricDefect_apply_sections hFi hFj)
  rw [metricDefectAux_apply] at hdef
  have hΓji := localFrameCoeff_eq_inner_of_orthonormal
    (I := I) e b hx horth j (cov (e.localFrame b i) x u)
  have hΓij := localFrameCoeff_eq_inner_of_orthonormal
    (I := I) e b hx horth i (cov (e.localFrame b j) x u)
  have hΓji' :
      inner ℝ (cov (e.localFrame b i) x u) (e.localFrame b j x) =
        e.localFrameCoeff I b j x (cov (e.localFrame b i) x u) := by
    rw [real_inner_comm]
    exact hΓji.symm
  change mvfderiv (I := I)
      (fun y => inner ℝ (e.localFrame b i y) (e.localFrame b j y)) x u = _
  rw [hΓji', hΓij.symm] at hdef
  linarith [hdef]

end CovariantDerivative
