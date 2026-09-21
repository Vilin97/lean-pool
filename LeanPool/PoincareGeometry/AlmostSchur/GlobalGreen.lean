/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.DivergenceRegularity
public import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Global Green formula

The compact manifold identity is assembled from compactly chart-supported
fields using a finite smooth partition of unity. The global measure is the
metric-density measure already characterized in every chart.
-/

@[expose] public noncomputable section
open Bundle FiberBundle Set MeasureTheory
open scoped Manifold ContDiff Topology BigOperators

namespace AlmostSchur

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M] [LindelofSpace M]

local notation "TM" => (TangentSpace I : M → Type _)

local instance : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
  continuousRiemannianBundle_of_contMDiff (I := I)

/-- The chart-supported Green formula also holds for the global measure,
because both integrands vanish outside the chart source. -/
theorem integral_mul_divergence_of_chart_support
    (cov : CovariantDerivative I E TM) (hm : tangentMetricCompatible cov)
    (ht : cov.torsion = 0) (c : M) (f : M → ℝ) (X : Π x : M, TM x)
    (hf : CMDiff 1 f) (hX : CMDiff 1 (T% X))
    (hc : HasCompactSupport (fun x => ‖X x‖))
    (hs : tsupport (fun x => ‖X x‖) ⊆ (extChartAt I c).source) :
    ∫ x, f x * divergence cov X x ∂riemannianVolume (I := I) =
      -∫ x, mvfderiv I f x (X x) ∂riemannianVolume (I := I) := by
  classical
  let b := (stdOrthonormalBasis ℝ E).toBasis
  have hν : (riemannianVolume (I := I)).restrict (extChartAt I c).source =
      chartMetricMeasure (I := I) b.addHaar b c := by
    rw [riemannianVolume_eq b, metricDensityMeasure_restrict, chartMetricMeasure_restrict_source]
  have hl : ∀ x, x ∉ (extChartAt I c).source → f x * divergence cov X x = 0 := by
    intro x hx
    rw [divergence_eq_zero_of_notMem_tsupport cov X x (hX.mdifferentiable (by simp) x)
      (fun h => hx (hs h)), mul_zero]
  have hr : ∀ x, x ∉ (extChartAt I c).source → mvfderiv I f x (X x) = 0 := by
    intro x hx
    have hn := image_eq_zero_of_notMem_tsupport (f := fun y => ‖X y‖) (fun h => hx (hs h))
    rw [norm_eq_zero.mp hn, map_zero]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hl,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero hr]
  change (∫ x, f x * divergence cov X x ∂(riemannianVolume (I := I)).restrict
    (extChartAt I c).source) = _
  rw [hν]
  exact integral_chartMetricMeasure_mul_divergence b.addHaar cov hm ht b c f X
    hf.contMDiffOn hX.contMDiffOn hc hs

variable [T2Space M] [CompactSpace M]

/-- A compact smooth manifold admits a finite smooth partition subordinate
to actual chart sources. -/
theorem exists_finite_smooth_chart_partition :
    ∃ s : Finset M, ∃ ρ : SmoothPartitionOfUnity s I M univ,
      ρ.IsSubordinate (fun c => (chartAt H (c : M)).source) := by
  classical
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun c : M => (chartAt H c).source) (fun c => (chartAt H c).open_source) (by
      intro x _
      exact mem_iUnion.mpr ⟨x, mem_chart_source H x⟩)
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate I isClosed_univ
    (fun c : s => (chartAt H (c : M)).source) (fun c => (chartAt H (c : M)).open_source) (by
      intro x hx
      obtain ⟨c, hc, hxc⟩ := mem_iUnion₂.mp (hs hx)
      exact mem_iUnion.mpr ⟨⟨c, hc⟩, hxc⟩)
  exact ⟨s, ρ, hρ⟩

/-- Green's identity on a compact boundaryless manifold, assembled from
the proved chart identities by a finite smooth partition of unity. -/
theorem integral_mul_divergence
    (cov : CovariantDerivative I E TM) (hm : tangentMetricCompatible cov)
    (ht : cov.torsion = 0) (f : M → ℝ) (X : Π x : M, TM x)
    (hf : CMDiff 1 f) (hX : CMDiff 1 (T% X)) :
    ∫ x, f x * divergence cov X x ∂riemannianVolume (I := I) =
      -∫ x, mvfderiv I f x (X x) ∂riemannianVolume (I := I) := by
  classical
  let ν := riemannianVolume (I := I) (M := M)
  letI : IsFiniteMeasure ν := ⟨(riemannianVolume_finite_positive (I := I)).2⟩
  obtain ⟨s, ρ, hρ⟩ := exists_finite_smooth_chart_partition (I := I) (M := M)
  let Y := fun (i : s) (x : M) => ρ i x • X x
  have hY (i : s) : CMDiff 1 (T% (Y i)) :=
    ((ρ i).contMDiff.of_le (by norm_num)).smul_section hX
  have hYs (i : s) : tsupport (fun x => ‖Y i x‖) ⊆ (extChartAt I (i : M)).source := by
    have hs : tsupport (fun x => ‖Y i x‖) ⊆ tsupport (ρ i) := by
      apply closure_mono
      intro x hx hzero
      apply hx
      simp only [Y, hzero, zero_smul, norm_zero]
    intro x hx
    simpa only [extChartAt_source] using hρ i (hs hx)
  have hloc (i : s) :
      (∫ x, f x * divergence cov (Y i) x ∂ν) =
        -∫ x, mvfderiv I f x (Y i x) ∂ν :=
    integral_mul_divergence_of_chart_support cov hm ht i f (Y i) hf (hY i)
      isClosed_closure.isCompact (hYs i)
  have hrec : X = fun x => ∑ i : s, Y i x := by
    funext x
    dsimp only [Y]
    rw [← Finset.sum_smul]
    have hsum : (∑ i : s, ρ i x) = 1 := by
      simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (mem_univ x)
    rw [hsum, one_smul]
  have hdiv (x : M) : divergence cov X x = ∑ i : s, divergence cov (Y i) x := by
    conv_lhs => rw [hrec]
    exact divergence_sum cov Finset.univ Y x (fun i _ => (hY i).mdifferentiable (by simp) x)
  have hdf (x : M) : mvfderiv I f x (X x) = ∑ i : s, mvfderiv I f x (Y i x) := by
    rw [congrFun hrec x, map_sum]
  have hl (i : s) : Integrable (fun x => f x * divergence cov (Y i) x) ν :=
    (hf.continuous.mul (continuous_divergence cov hm ht (Y i) (hY i))).integrable_of_hasCompactSupport
      isClosed_closure.isCompact
  have hr (i : s) : Integrable (fun x => mvfderiv I f x (Y i x)) ν :=
    (continuous_differential_apply cov hm ht f (Y i) hf (hY i)).integrable_of_hasCompactSupport
      isClosed_closure.isCompact
  change (∫ x, f x * divergence cov X x ∂ν) = -∫ x, mvfderiv I f x (X x) ∂ν
  simp_rw [hdiv, Finset.mul_sum, hdf]
  rw [integral_finsetSum _ (fun i _ => hl i), integral_finsetSum _ (fun i _ => hr i)]
  simp_rw [hloc]
  rw [Finset.sum_neg_distrib]

end AlmostSchur
