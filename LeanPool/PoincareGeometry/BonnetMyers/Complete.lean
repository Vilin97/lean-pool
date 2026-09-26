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

public import LeanPool.PoincareGeometry.BonnetMyers.Construction
public import LeanPool.PoincareGeometry.BonnetMyers.GlobalIndexNonnegative
public import LeanPool.PoincareGeometry.BonnetMyers.MetricSegmentSmooth
public import LeanPool.PoincareGeometry.BonnetMyers.RiemannianMinimizer
public import LeanPool.PoincareGeometry.BonnetMyers.RiemannianHopfRinow
public import LeanPool.PoincareGeometry.BonnetMyers.MetricConsequences
public import LeanPool.PoincareGeometry.BonnetMyers.GeometricIndex

/-!
# Completion of the independent Bonnet--Myers proof

This module combines the independently constructed Hopf--Rinow minimizer,
global geodesic and parallel-transport layers, the chartwise second variation,
and the Ricci comparison estimate.  It proves the public geometric statement
without importing the superseded external wrapper.
-/

@[expose] public section

noncomputable section

open Bundle Manifold Set Filter MeasureTheory
open scoped Manifold ContDiff ENNReal Topology Interval RealInnerProductSpace BigOperators

namespace BonnetMyersEntry

open IntrinsicGeodesic.GlobalGeodesic

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M] [ConnectedSpace M]

local notation "TM" => (TangentSpace I : M → Type _)
/-- Under the Ricci lower bound, the finite Riemannian metric is proper,
compact, and has the sharp Bonnet--Myers diameter bound. -/
theorem bonnetMyers_metric_conclusion
    [TopologicalSpace.MetrizableSpace M] [T3Space M]
    (g : ContMDiffRiemannianMetric I ∞ E TM) :
    letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E TM :=
      ⟨⟨g.inner, g.contMDiff.continuous, by intro x a b; rfl⟩⟩
    letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
    let cov := leviCivita (I := I) (M := M) g
    ∀ (K : ℝ), 0 < K → 2 ≤ Module.finrank ℝ E → CompleteSpace M →
      (∀ (x : M) (a : TM x),
        (((Module.finrank ℝ (TM x) : ℝ) - 1) * K) * inner ℝ a a ≤
          LinearMap.trace ℝ (TM x)
            (curvatureEndomorphism
              (R := curvature (I := I) (M := M) cov) x a)) →
      CompactSpace M ∧ Metric.ediam (Set.univ : Set M) ≤
        ENNReal.ofReal (Real.pi / Real.sqrt K) := by
  letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E TM :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x a b; rfl⟩⟩
  letI : IsContMDiffRiemannianBundle I 1 E TM := by infer_instance
  letI : IsContMDiffRiemannianBundle I 2 E TM := by infer_instance
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let cov := leviCivita (I := I) (M := M) g
  letI : CovariantDerivative.ContMDiffCovariantDerivative cov 1 := by
    simpa [cov] using (leviCivitaSmooth (I := I) (M := M) g)
  have hcov : CovariantDerivative.IsLeviCivita cov := by
    simpa [cov] using (leviCivita_isLeviCivita (I := I) (M := M) g)
  dsimp only
  intro K hK hn hcomplete hRic
  letI : MetricSpace M := finiteRiemannianMetricSpace (I := I) (M := M) g
  letI : ProperSpace M :=
    finiteRiemannianMetricSpace_properSpace (I := I) (M := M) g hcomplete
  let C : ℝ := Real.pi / Real.sqrt K
  have hC0 : 0 ≤ C := by
    dsimp [C]
    positivity
  have hdist : ∀ x z : M, dist x z ≤ C := by
    intro x z
    by_contra hnot
    have hlong : C < dist x z := lt_of_not_ge hnot
    have hD : 0 < dist x z := lt_of_le_of_lt hC0 hlong
    obtain ⟨σ, hσcontinuous, hσzero, hσlast, hσsegment⟩ :=
      finiteRiemannianMetricSpace_exists_riemannian_metric_segment_of_complete
        (I := I) (M := M) g hcomplete x z
    obtain ⟨τ, c, v, α, hτpos, hτD, hv, hασ⟩ :=
      riemannian_metric_segment_eq_global_unitGeodesic
        (I := I) (M := M) g hcomplete σ hσcontinuous hσsegment hD
    let t₀ : ℝ := -(τ : ℝ)
    have hunit : ‖velocity α t₀‖ = 1 := by
      rw [norm_velocity_eq_initial (I := I) (M := M) α hcov.2 t₀]
      exact hv
    have hnT : 2 ≤ Module.finrank ℝ (TM (curve α t₀)) := by
      rw [tangent_finrank_eq_model (I := I) (M := M)]
      exact hn
    obtain ⟨b, hb, p, hacc, hvelocity, horth, htransverse⟩ :=
      exists_global_adapted_parallelFrame
        (I := I) (M := M) α t₀ hcov.2 hunit (by omega)
    let s0 : MetricHopfRinow.SegmentParameter x z :=
      ⟨0, ⟨le_rfl, dist_nonneg⟩⟩
    let sD : MetricHopfRinow.SegmentParameter x z :=
      ⟨dist x z, ⟨dist_nonneg, le_rfl⟩⟩
    have hleft : curve (shift α t₀) 0 = x := by
      rw [shift_curve]
      calc
        curve α (t₀ + 0) = σ s0 := by
          simpa [t₀, s0] using hασ s0
        _ = x := hσzero
    have hright : curve (shift α t₀) (dist x z) = z := by
      rw [shift_curve]
      calc
        curve α (t₀ + dist x z) = σ sD := by
          convert hασ sD using 1 <;> simp [t₀, sD] <;> ring
        _ = z := hσlast
    have hendpoint : riemannianEDist I
        (curve (shift α t₀) 0) (curve (shift α t₀) (dist x z)) =
          ENNReal.ofReal (dist x z) := by
      rw [hleft, hright,
        finiteRiemannianMetricSpace_riemannianEDist_eq_ofReal_dist
          (I := I) (M := M) g]
    have hmin : ∀ i ∈ Finset.univ.erase (⟨0, by omega⟩ :
        Fin (Module.finrank ℝ (TM (curve α t₀)))),
        0 ≤ globalIndexForm (curvature (I := I) (M := M) cov) α t₀
          ((p i).sineTestField (dist x z))
          ((p i).sineTestDerivativeField (dist x z)) (dist x z) := by
      intro i hi
      exact (p i).globalIndexForm_sine_nonnegative_of_endpoint_minimizing
        hcov.2 hcov.1 hcomplete hD hunit hendpoint
    exact (no_long_global_geodesic_of_ricci_and_sine_index_nonnegative
      (I := I) (M := M) p horth hnT hvelocity hcov.2 hunit
        hK hlong hRic hmin).elim
  have hediam : Metric.ediam (Set.univ : Set M) ≤ ENNReal.ofReal C := by
    exact Metric.ediam_le_of_forall_dist_le
      (fun x _hx y _hy ↦ hdist x y)
  have hcompact : CompactSpace M :=
    compactSpace_of_ediam_univ_le hC0 hediam
  refine ⟨hcompact, ?_⟩
  simpa [C] using hediam
/-- The independent Bonnet--Myers development proves the complete public
statement: it constructs the Levi-Civita connection and curvature, derives
compactness from metric completeness and the Ricci bound, and obtains the
sharp diameter estimate. -/
theorem completeStatement_proved : completeStatement.{u,v,w} := by
  unfold completeStatement
  intro E hEadd hEscalar hEfinite hEne H hHtop I hIboundary
    M hMtop hchart hmanifold hMhausdorff hTMhausdorff hsigma hconnected g
  letI : IsManifold I 1 M := IsManifold.of_le (I := I) (M := M)
    (n := (∞ : WithTop ℕ∞)) (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  letI : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  letI : T3Space M := inferInstance
  letI : RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x a b; rfl⟩⟩
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let cov : CovariantDerivative I E (TangentSpace I : M → Type _) :=
    leviCivita (I := I) (M := M) g
  letI : CovariantDerivative.ContMDiffCovariantDerivative cov 1 := by
    simpa [cov] using (leviCivitaSmooth (I := I) (M := M) g)
  have hcov : CovariantDerivative.IsLeviCivita cov := by
    simpa [cov] using (leviCivita_isLeviCivita (I := I) (M := M) g)
  let R : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ]
      TangentSpace I x →L[ℝ] TangentSpace I x :=
    fun x ↦ curvature (cov := cov) x
  refine ⟨cov, hcov.1, ?_, R, ?_, ?_⟩
  · intro Y Z x hY hZ a
    exact hcov.2 hY hZ a
  · intro X Y Z hX hY hZ x
    exact curvature_apply_smooth (cov := cov) X Y Z hX hY hZ x
  · intro K hK hn hcomplete hRic
    apply bonnetMyers_metric_conclusion (I := I) (M := M) g K hK hn hcomplete
    intro x a
    have hdim := tangent_finrank_eq_model (I := I) (M := M) x
    rw [hdim]
    change (((Module.finrank ℝ E : ℝ) - 1) * K) * g.inner x a a ≤ _
    simpa only [R, cov, curvatureEndomorphism] using hRic x a

end BonnetMyersEntry
