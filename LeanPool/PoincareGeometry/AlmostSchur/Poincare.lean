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

public import LeanPool.PoincareGeometry.AlmostSchur.PoincareCountersequence
public import LeanPool.PoincareGeometry.AlmostSchur.EnergyCompactness
public import LeanPool.PoincareGeometry.AlmostSchur.WeakChartLimit
public import LeanPool.PoincareGeometry.AlmostSchur.ChartWeakKernel
public import LeanPool.PoincareGeometry.AlmostSchur.ChartLpRegularity

/-! # Intrinsic Poincaré inequality

On a compact preconnected boundaryless Riemannian manifold, the actual-volume
L² norm of a mean-zero C¹ function is bounded by its intrinsic gradient energy.
The proof combines normalized countersequences, proved Sobolev compactness,
the chartwise weak-limit identity, and the proved manifold weak kernel.
-/

@[expose] public noncomputable section
open Bundle Set MeasureTheory Filter
open scoped Manifold ContDiff Topology ENNReal
open RellichKondrachov.Geometry.Manifold.Sobolev

namespace AlmostSchur

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless] [T2Space M] [CompactSpace M]
  [PreconnectedSpace M] [Nonempty M] [LindelofSpace M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]

local instance poincareMeasurableM : MeasurableSpace M := borel M
local instance poincareBorelM : BorelSpace M := ⟨rfl⟩
local instance poincareMeasurableE : MeasurableSpace E := borel E
local instance poincareBorelE : BorelSpace E := ⟨rfl⟩
local instance poincareMetricZero : IsContMDiffRiemannianBundle I (↑(0 : ℕ)) E
    (TangentSpace I : M → Type _) :=
  IsContMDiffRiemannianBundle.of_le (n := 1) (by norm_num)
local instance poincareContinuousMetric :
    IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
  continuousRiemannianBundle_of_contMDiff (I := I)
local instance poincareFiniteVolume :
    IsFiniteMeasure (riemannianVolume (I := I) (M := M)) :=
  ⟨(riemannianVolume_finite_positive (I := I)).2⟩

/-- The intrinsic Poincaré inequality for mean-zero C¹ functions, with no
assumed analytic compactness, weak regularity, or Poincaré bridge. The finite chart
data used in the proof are constructed from compactness. -/
theorem exists_poincare_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ f : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) 1 f →
      (∫ x, f x ∂riemannianVolume (I := I)) = 0 →
      lpNorm f 2 (riemannianVolume (I := I)) ≤
        C * Real.sqrt (dirichletForm (I := I) f f) := by
  classical
  by_contra hfail
  obtain ⟨f, hfLp, hf, hmean, hnorm, henergy⟩ := exists_poincare_countersequence hfail
  obtain ⟨d⟩ := exists_finiteChartData_chartAt (I := I) (M := M)
  have hbound (n : ℕ) : ‖(hfLp n).toLp (f n)‖ +
      Real.sqrt (dirichletForm (I := I) (f n) (f n)) ≤ 2 := by
    have hn : 1 / ((n : ℝ) + 1) ≤ 1 := by
      apply (div_le_iff₀ (by positivity : 0 < (n : ℝ) + 1)).2
      have := Nat.cast_nonneg (α := ℝ) n
      linarith
    rw [hnorm n]
    linarith [henergy n]
  obtain ⟨u, φ, hφ, hlim⟩ := exists_energyL2_subsequence d f hf hfLp 2 hbound
  have he0 : Tendsto (fun n => Real.sqrt (dirichletForm (I := I) (f n) (f n)))
      atTop (𝓝 0) :=
    squeeze_zero (fun _ => Real.sqrt_nonneg _) henergy
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hsubenergy := he0.comp hφ.tendsto_atTop
  have huMean : (∫ x, u x ∂riemannianVolume (I := I)) = 0 := by
    apply integral_L2_eq_zero_of_limit hlim
    intro n
    exact (integral_congr_ae (hfLp (φ n)).coeFn_toLp).trans (hmean (φ n))
  obtain ⟨k, hk⟩ := ae_eq_const_of_chart_weakDeriv_eq_zero
    (fun c => locallyIntegrableOn_chart_comp_lp c u) (fun c ψ hψ hc hs v => by
      exact integral_chart_limit_mul_fderiv_eq_zero
        (fun n => f (φ n)) (fun n => hf (φ n)) (fun n => hfLp (φ n))
        u hlim hsubenergy c ψ (hψ.of_le (by norm_num)) hc hs v)
  have htotal : 0 < (riemannianVolume (I := I) (M := M)).real univ := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos
      (riemannianVolume_finite_positive (I := I)).1.ne'
      (riemannianVolume_finite_positive (I := I)).2.ne
  have hk0 : k = 0 := by
    have h := (integral_congr_ae hk).symm.trans huMean
    rw [integral_const, smul_eq_mul] at h
    exact (mul_eq_zero.mp h).resolve_left htotal.ne'
  have hu0 : u = 0 := by
    apply Lp.ext
    exact (hk.trans (Filter.Eventually.of_forall (fun _ => hk0))).trans
      (Lp.coeFn_zero ℝ 2 (riemannianVolume (I := I))).symm
  have hunorm : ‖u‖ = 1 := by
    have hn := hlim.norm
    simp only [hnorm] at hn
    exact tendsto_nhds_unique hn tendsto_const_nhds
  rw [hu0, norm_zero] at hunorm
  norm_num at hunorm

end AlmostSchur
