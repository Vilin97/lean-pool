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

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.DeTurckJointRegularity
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivitaCorrectionKoszul
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.ConnectionLaplacianLocalFrame

/-!
# Local-frame components of the explicit Levi-Civita correction

For a torsion-free background connection, this file writes the components of
the explicit correction from that connection to the slice Levi-Civita
connection in an arbitrary local tangent frame.  The formula keeps the
background metric defect visible: it makes no Ricci-flow cancellation or
regularity assertion.
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
local notation "⟪" x ", " y "⟫" => inner ℝ x y
/-- The frame pairing of the explicit correction is the torsion-free Koszul
polarization of the metric defect of the background connection.  The first
correction input is the differentiated vector and the second is the
direction, following `CovariantDerivative.leviCivitaCorrection`. -/
theorem explicitLeviCivitaCorrection_inner_localFrame_of_isTorsionFree
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ) (hbackground : (background t).IsTorsionFree)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    {ι : Type*}
    (b : Module.Basis ι ℝ E) (x : M) (i j l : ι) :
    letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
    2 * ⟪explicitLeviCivitaCorrection (I := I) (M := M) g background t x
        (e.localFrame b j x) (e.localFrame b i x), e.localFrame b l x⟫ =
      (background t).metricDefect x
          (e.localFrame b j x) (e.localFrame b l x) (e.localFrame b i x) +
        (background t).metricDefect x
          (e.localFrame b i x) (e.localFrame b l x) (e.localFrame b j x) -
        (background t).metricDefect x
          (e.localFrame b i x) (e.localFrame b j x) (e.localFrame b l x) := by
  letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 1 E TM :=
    g.slice_isContMDiffRiemannianBundle t
  simpa [explicitLeviCivitaCorrection] using
    (CovariantDerivative.leviCivitaCorrection_inner_of_isTorsionFree
      (I := I) (E := E) (cov := background t) hbackground x
      (e.localFrame b j x) (e.localFrame b i x) (e.localFrame b l x))
/-- The local-frame coefficient of the explicit correction is the inverse
Gram contraction of its torsion-free Koszul metric-defect components. -/
theorem explicitLeviCivitaCorrection_localFrameCoeff_of_isTorsionFree
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ) (hbackground : (background t).IsTorsionFree)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ E) {x : M} (hx : x ∈ e.baseSet) (i j k : ι) :
    letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
    e.localFrameCoeff I b k x
        (explicitLeviCivitaCorrection (I := I) (M := M) g background t x
          (e.localFrame b j x) (e.localFrame b i x)) =
      ∑ l : ι,
        CovariantDerivative.localFrameInverseGramMatrix (I := I) e b x k l *
          ((1 / 2 : ℝ) *
            ((background t).metricDefect x
                (e.localFrame b j x) (e.localFrame b l x) (e.localFrame b i x) +
              (background t).metricDefect x
                (e.localFrame b i x) (e.localFrame b l x) (e.localFrame b j x) -
              (background t).metricDefect x
                (e.localFrame b i x) (e.localFrame b j x) (e.localFrame b l x))) := by
  letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 1 E TM :=
    g.slice_isContMDiffRiemannianBundle t
  let omega : ∀ y : M, TangentSpace I y →L[ℝ] ℝ := fun y =>
    (InnerProductSpace.toDual ℝ (TM y))
      (explicitLeviCivitaCorrection (I := I) (M := M) g background t y
        (e.localFrame b j y) (e.localFrame b i y))
  have hriesz :
      CovariantDerivative.rieszMap (I := I) x (omega x) =
        explicitLeviCivitaCorrection (I := I) (M := M) g background t x
          (e.localFrame b j x) (e.localFrame b i x) := by
    change (InnerProductSpace.toDual ℝ (TM x)).symm
      ((InnerProductSpace.toDual ℝ (TM x))
        (explicitLeviCivitaCorrection (I := I) (M := M) g background t x
          (e.localFrame b j x) (e.localFrame b i x))) = _
    exact (InnerProductSpace.toDual ℝ (TM x)).symm_apply_apply _
  have hpair (l : ι) :
      2 * ⟪explicitLeviCivitaCorrection (I := I) (M := M) g background t x
          (e.localFrame b j x) (e.localFrame b i x), e.localFrame b l x⟫ =
        (background t).metricDefect x
            (e.localFrame b j x) (e.localFrame b l x) (e.localFrame b i x) +
          (background t).metricDefect x
            (e.localFrame b i x) (e.localFrame b l x) (e.localFrame b j x) -
          (background t).metricDefect x
            (e.localFrame b i x) (e.localFrame b j x) (e.localFrame b l x) := by
    simpa using
      (explicitLeviCivitaCorrection_inner_localFrame_of_isTorsionFree
        (I := I) (M := M) g background t hbackground e b x i j l)
  rw [← hriesz,
    CovariantDerivative.localFrameCoeff_rieszMap (I := I) (E := E) e b hx k]
  simp only [CovariantDerivative.localFrameInverseGramMatrix, omega]
  apply Finset.sum_congr rfl
  intro l _
  rw [show (InnerProductSpace.toDual ℝ (TM x))
      (explicitLeviCivitaCorrection (I := I) (M := M) g background t x
        (e.localFrame b j x) (e.localFrame b i x)) (e.localFrame b l x) =
      ⟪explicitLeviCivitaCorrection (I := I) (M := M) g background t x
        (e.localFrame b j x) (e.localFrame b i x), e.localFrame b l x⟫ by rfl]
  have hhalf :
      ⟪explicitLeviCivitaCorrection (I := I) (M := M) g background t x
          (e.localFrame b j x) (e.localFrame b i x), e.localFrame b l x⟫ =
        (1 / 2 : ℝ) *
          ((background t).metricDefect x
              (e.localFrame b j x) (e.localFrame b l x) (e.localFrame b i x) +
            (background t).metricDefect x
              (e.localFrame b i x) (e.localFrame b l x) (e.localFrame b j x) -
            (background t).metricDefect x
              (e.localFrame b i x) (e.localFrame b j x) (e.localFrame b l x)) := by
    linarith [hpair l]
  rw [hhalf]

end RicciFlow
