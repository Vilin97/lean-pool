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

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.DeTurck

/-!
# Pointwise Levi-Civita correction formula for the intrinsic DeTurck field

This file replaces the noncanonical chosen Levi-Civita representative in the
intrinsic DeTurck connection difference by the explicit correction of an
arbitrary background connection.  It is a pointwise identity; joint
time--space regularity of the correction is supplied separately.
-/

@[expose] public noncomputable section

open Bundle FiberBundle
open scoped Manifold ContDiff Topology

namespace RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]

local notation "TM" => (TangentSpace I : M → Type _)

section ChosenLeviCivita

variable [SigmaCompactSpace M]

/-- The explicit slice correction that turns `background t` into the
Levi-Civita connection of `g t`. -/
noncomputable def explicitLeviCivitaCorrection
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ) (x : M) :
    TM x →L[ℝ] TM x →L[ℝ] TM x := by
  letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 1 E TM :=
    g.slice_isContMDiffRiemannianBundle t
  exact (background t).leviCivitaCorrection x
/-- The intrinsic DeTurck connection difference is the explicit Levi-Civita
correction of the background connection. -/
theorem intrinsicDeTurck_difference_apply_eq_leviCivitaCorrection
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ) (x : M) (v w : TM x) :
    (CovariantDerivative.difference
      ((chosenLeviCivitaFamily (I := I) (M := M) g) t) (background t) x v) w =
      explicitLeviCivitaCorrection (I := I) (M := M) g background t x v w := by
  letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 1 E TM :=
    g.slice_isContMDiffRiemannianBundle t
  have hchosen :
      (chosenLeviCivitaFamily (I := I) (M := M) g) t (extend E v) x =
        (g.leviCivitaConnection background) t (extend E v) x := by
    exact g.eq_of_isLeviCivita
      (chosenLeviCivitaFamily_isLeviCivita (I := I) (M := M) g)
      (g.leviCivitaConnection_isLeviCivita background)
      (mdifferentiableAt_extend (I := I) (F := E) v)
  rw [CovariantDerivative.difference_apply_eq_extend_tm]
  change
    ((chosenLeviCivitaFamily (I := I) (M := M) g) t (extend E v) x -
      (background t) (extend E v) x) w =
      explicitLeviCivitaCorrection (I := I) (M := M) g background t x v w
  rw [hchosen]
  simp [explicitLeviCivitaCorrection,
    CovariantDerivative.TimeDependentRiemannianMetric.leviCivitaConnection,
    CovariantDerivative.leviCivitaConnection, CovariantDerivative.addOneForm]

/-- In a local frame, the intrinsic DeTurck one-form is the trace of the
explicit Levi-Civita correction of the background connection. -/
theorem intrinsicDeTurckOneForm_apply_localFrame_eq_sum_leviCivitaCorrection
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {x : M} (hx : x ∈ e.baseSet) (i : ι) :
    intrinsicDeTurckOneForm (I := I) (M := M) g background t x
        (e.localFrame b i x) =
      ∑ j, e.localFrameCoeff I b j x
        (explicitLeviCivitaCorrection (I := I) (M := M) g background t x
          (e.localFrame b j x)
          (e.localFrame b i x)) := by
  rw [intrinsicDeTurckOneForm_apply_localFrame_eq_sum_localFrameCoeff
    (I := I) (M := M) g background t e b hx i]
  apply Finset.sum_congr rfl
  intro j _
  rw [intrinsicDeTurck_difference_apply_eq_leviCivitaCorrection]

end ChosenLeviCivita

end RicciFlow
