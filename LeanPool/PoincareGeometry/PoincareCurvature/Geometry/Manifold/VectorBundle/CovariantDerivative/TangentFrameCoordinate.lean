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

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.DowngradeNormFree

/-!
# Tangent-frame coordinates for a covariant derivative

This is the tangent-bundle specialization of the local-frame coordinate
formula for a covariant derivative.  Keeping the statement at
`TangentSpace I` avoids the generic fiber-bundle instance elaboration that
arises when the formula is used inside Ricci--DeTurck calculations.
-/

@[expose] public noncomputable section
open Bundle FiberBundle
open scoped Manifold ContDiff Topology BigOperators

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [SigmaCompactSpace M]

local notation "TM" => (TangentSpace I : M → Type _)

namespace TangentFrame

/-- The local-frame coefficient of the covariant derivative of a tangent
section.  Its first term differentiates the selected coefficient; its finite
second term records the covariant derivatives of the frame vectors. -/
theorem localFrameCoeff_covariantDerivative_eq_mvfderiv_add_connection
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) (cov : CovariantDerivative I E TM)
    {σ : ∀ y : M, TM y} {x : M} (hx : x ∈ e.baseSet)
    (hσ : MDiffAt (T% σ) x) (v : TM x) (k : ι) :
    e.localFrameCoeff I b k x (cov σ x v) =
      mvfderiv (I := I) (fun y => e.localFrameCoeff I b k y (σ y)) x v +
        ∑ q, e.localFrameCoeff I b q x (σ x) *
          e.localFrameCoeff I b k x (cov (e.localFrame b q) x v) := by
  have hframeCoeff (q : ι) :
      e.localFrameCoeff I b k x (e.localFrame b q x) =
        if k = q then 1 else 0 := by
    rw [Bundle.Trivialization.localFrameCoeff_apply_of_mem_baseSet
      (I := I) (e := e) (b := b) hx (e.localFrame b q) k]
    rw [Bundle.Trivialization.localFrame_apply_of_mem_baseSet
      (e := e) (b := b) hx]
    simp [Module.Basis.repr_self, Finsupp.single_apply, eq_comm]
  have hdecomp :=
    covariantDerivative_apply_eq_sum_localFrame_add_sum_covariantDerivative_localFrame
      (I := I) e b cov hx hσ v
  have hread := congrArg (fun z : TM x => e.localFrameCoeff I b k x z) hdecomp
  rw [hread]
  simp only [map_add, map_sum, map_smul, LinearMap.piApply_apply, smul_eq_mul]
  simp_rw [hframeCoeff]
  simp

end TangentFrame

end CovariantDerivative
