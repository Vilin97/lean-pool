/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.LocalizedWeakJetIdentities
public import LeanPool.PoincareGeometry.AlmostSchur.ManifoldTestUniqueness
public import LeanPool.PoincareGeometry.AlmostSchur.EnergyGreen
public import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving

/-! # Classical representatives of weak Poisson solutions

This bridge does not assert all-order elliptic regularity. It glues local
smooth representatives, with respect to the actual manifold measure, and
then transfers the proved transposed equation to the classical Laplacian.
The local Fourier endpoint is available through the imports above; transporting
its almost-everywhere identity through a chart remains an explicit obligation.
-/

@[expose] public noncomputable section
open Bundle Set MeasureTheory Filter
open scoped Manifold ContDiff Topology
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
  [T2Space M] [CompactSpace M]

local instance : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
  continuousRiemannianBundle_of_contMDiff (I := I)
local instance : IsFiniteMeasure (riemannianVolume (I := I) (M := M)) :=
  ⟨(riemannianVolume_finite_positive (I := I)).2⟩
local instance : (riemannianVolume (I := I) (M := M)).IsOpenPosMeasure :=
  ⟨fun _ hs hne => ne_of_gt (riemannianVolume_open_pos (I := I) hs hne)⟩

/-- Smooth Euclidean representatives pull back smoothly on the chart source. -/
theorem smooth_representative_chart_pullback (c : M) (g : E → ℝ)
    (hg : ContDiff ℝ ∞ g) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun x => g (extChartAt I c x))
      (extChartAt I c).source := by
  rw [extChartAt_source]
  exact hg.contMDiff.comp_contMDiffOn contMDiffOn_extChartAt

/-- Consume all finite local jets. The explicit quasi-measure-preserving
certificate transports Euclidean AE equality to the manifold patch; chart
smoothness is proved, rather than postulated. -/
theorem local_smooth_representative_of_all_jets {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (c : M) {K O : Set E} {U : Set M}
    (J : ∀ n : ℕ, LocalL2DerivativeJet b K n) (v : Lp ℝ 2 (volume : Measure E))
    (hroot : ∀ n, (J n).value [] = v)
    {χ : E → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ interior K) (hO : IsOpen O) (hχ1 : ∀ x ∈ O, χ x = 1)
    (hUs : U ⊆ (extChartAt I c).source)
    (hmap_meas : AEMeasurable (extChartAt I c)
      ((riemannianVolume (I := I)).restrict U))
    (hmap_ac : Measure.map (extChartAt I c)
      ((riemannianVolume (I := I)).restrict U) ≪ volume.restrict O)
    (u : M → ℝ)
    (hvu : (fun x => v (extChartAt I c x)) =ᵐ[(riemannianVolume (I := I)).restrict U] u) :
    ∃ f : M → ℝ, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f U ∧
      f =ᵐ[(riemannianVolume (I := I)).restrict U] u := by
  obtain ⟨g, hg, hge⟩ := local_weak_jets_exists_smooth_representative
    b J v hroot hχ hcχ hsχ hO hχ1
  exact ⟨fun x => g (extChartAt I c x),
    (smooth_representative_chart_pullback c g hg).mono hUs,
    (ae_eq_comp' hmap_meas hge hmap_ac).trans hvu⟩

/-- The measure identity, not a chosen representative, forces overlap compatibility. -/
theorem smooth_representative_overlap (u f g : M → ℝ) {U V : Set M}
    (hU : IsOpen U) (hV : IsOpen V)
    (hf : ContinuousOn f U) (hg : ContinuousOn g V)
    (hfu : f =ᵐ[(riemannianVolume (I := I)).restrict U] u)
    (hgu : g =ᵐ[(riemannianVolume (I := I)).restrict V] u) :
    EqOn f g (U ∩ V) := by
  apply Measure.eqOn_open_of_ae_eq (μ := riemannianVolume (I := I)) _
    (hU.inter hV) (hf.mono inter_subset_left)
    (hg.mono inter_subset_right)
  have hf' : f =ᵐ[(riemannianVolume (I := I)).restrict (U ∩ V)] u :=
    ae_restrict_of_ae_restrict_of_subset inter_subset_left hfu
  have hg' : g =ᵐ[(riemannianVolume (I := I)).restrict (U ∩ V)] u :=
    ae_restrict_of_ae_restrict_of_subset inter_subset_right hgu
  exact hf'.trans hg'.symm

/-- A countable open cover of smooth local representatives gives one global
smooth representative. Compatibility and global AE equality are proved. -/
theorem exists_smooth_representative_of_open_cover {ι : Type*} [Countable ι]
    (u : M → ℝ) (U : ι → Set M) (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ x, ∃ i, x ∈ U i) (f : ι → M → ℝ)
    (hf : ∀ i, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (f i) (U i))
    (hae : ∀ i, f i =ᵐ[(riemannianVolume (I := I)).restrict (U i)] u) :
    ∃ g : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ g ∧
      g =ᵐ[riemannianVolume (I := I)] u ∧ ∀ i, EqOn g (f i) (U i) := by
  classical
  let pick : M → ι := fun x => (hcover x).choose
  have hpick (x : M) : x ∈ U (pick x) := (hcover x).choose_spec
  let g : M → ℝ := fun x => f (pick x) x
  have heq (i : ι) : EqOn g (f i) (U i) := by
    intro x hx
    exact smooth_representative_overlap (I := I) u (f (pick x)) (f i)
      (hU _) (hU _) (hf _).continuousOn (hf _).continuousOn
      (hae _) (hae _) ⟨hpick x, hx⟩
  refine ⟨g, ?_, ?_, heq⟩
  · intro x
    exact ((hf (pick x) x (hpick x)).contMDiffAt
      ((hU _).mem_nhds (hpick x))).congr_of_eventuallyEq
        (Filter.eventuallyEq_of_mem ((hU _).mem_nhds (hpick x)) (heq _))
  · have hlocal : ∀ i, g =ᵐ[(riemannianVolume (I := I)).restrict (U i)] u := by
      intro i
      filter_upwards [hae i, ae_restrict_mem (hU i).measurableSet] with x hx hxi
      exact (heq i hxi).trans hx
    have hunion : (⋃ i, U i) = univ := by
      ext x
      simp only [mem_iUnion, mem_univ, iff_true]
      exact hcover x
    have hall := (ae_eq_restrict_iUnion_iff U g u).2 hlocal
    simpa only [hunion, Measure.restrict_univ] using hall

variable [PreconnectedSpace M]

/-- A C² representative of the realized weak solution solves the classical
Poisson equation against any continuous representative of the forcing. -/
theorem laplacian_smooth_weakPoisson_representative
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hm : tangentMetricCompatible cov) (ht : cov.torsion = 0)
    (h : Lp ℝ 2 (riemannianVolume (I := I) (M := M)))
    (hh : (∫ x, h x ∂riemannianVolume (I := I)) = 0)
    (g F : M → ℝ) (hg : CMDiff 2 g) (hF : Continuous F)
    (hgu : g =ᵐ[riemannianVolume (I := I)]
      energyCompletionToL2 (weakPoissonSolution h))
    (hFh : F =ᵐ[riemannianVolume (I := I)] h) :
    laplacian cov g = F := by
  have hz := continuous_eq_zero_of_integral_mul_smooth_eq_zero (I := I)
    (fun x => laplacian cov g x - F x)
    ((continuous_laplacian cov hm ht g hg).sub hF) ?_
  · funext x
    exact sub_eq_zero.mp (congrFun hz x)
  intro φ hφ
  have hφ2 : CMDiff 2 φ := hφ.of_le (by decide)
  have heq : (∫ x, laplacian cov g x * φ x ∂riemannianVolume (I := I)) =
      ∫ x, F x * φ x ∂riemannianVolume (I := I) := by
    calc
      _ = ∫ x, φ x * laplacian cov g x ∂riemannianVolume (I := I) := by
        simp only [mul_comm]
      _ = -dirichletForm (I := I) φ g :=
        integral_mul_laplacian cov hm ht φ g (hφ.of_le (by norm_num)) hg
      _ = -dirichletForm (I := I) g φ := by rw [dirichletForm_symm φ g]
      _ = ∫ x, g x * laplacian cov φ x ∂riemannianVolume (I := I) :=
        (integral_mul_laplacian cov hm ht g φ (hg.of_le (by norm_num)) hφ2).symm
      _ = ∫ x, energyCompletionToL2 (weakPoissonSolution h) x * laplacian cov φ x
          ∂riemannianVolume (I := I) := integral_congr_ae (hgu.mul EventuallyEq.rfl)
      _ = ∫ x, h x * φ x ∂riemannianVolume (I := I) :=
        weakPoissonSolution_laplacian_test cov hm ht h hh φ hφ2
      _ = _ := integral_congr_ae (hFh.symm.mul EventuallyEq.rfl)
  simp_rw [sub_mul]
  change (∫ x, (laplacian cov g * φ) x - (F * φ) x ∂riemannianVolume (I := I)) = 0
  rw [integral_sub
    (((continuous_laplacian cov hm ht g hg).mul hφ.continuous).integrable_of_hasCompactSupport
      isClosed_closure.isCompact)
    ((hF.mul hφ.continuous).integrable_of_hasCompactSupport isClosed_closure.isCompact)]
  change (∫ x, laplacian cov g x * φ x ∂riemannianVolume (I := I)) -
    (∫ x, F x * φ x ∂riemannianVolume (I := I)) = 0
  exact sub_eq_zero.mpr heq

/-- Conditional classical existence for the actual variational solution.
The local regularity input is an open cover of genuine smooth representatives,
which can be supplied by `local_smooth_representative_of_all_jets`.
Mean zero and the pointwise equation are consequences, not extra hypotheses. -/
theorem exists_classical_weakPoisson_of_local_representatives
    {ι : Type*} [Countable ι]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hm : tangentMetricCompatible cov) (ht : cov.torsion = 0)
    (h : Lp ℝ 2 (riemannianVolume (I := I) (M := M)))
    (hh : (∫ x, h x ∂riemannianVolume (I := I)) = 0)
    (F : M → ℝ) (hF : Continuous F)
    (hFh : F =ᵐ[riemannianVolume (I := I)] h)
    (U : ι → Set M) (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ x, ∃ i, x ∈ U i) (f : ι → M → ℝ)
    (hf : ∀ i, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (f i) (U i))
    (hae : ∀ i, f i =ᵐ[(riemannianVolume (I := I)).restrict (U i)]
      energyCompletionToL2 (weakPoissonSolution h)) :
    ∃ g : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ g ∧
      g =ᵐ[riemannianVolume (I := I)] energyCompletionToL2 (weakPoissonSolution h) ∧
      (∫ x, g x ∂riemannianVolume (I := I)) = 0 ∧ laplacian cov g = F := by
  obtain ⟨g, hg, hge, _⟩ := exists_smooth_representative_of_open_cover
    (I := I) _ U hU hcover f hf hae
  refine ⟨g, hg, hge, ?_, ?_⟩
  · exact (integral_congr_ae hge).trans (integral_weakPoissonSolution h)
  · exact laplacian_smooth_weakPoisson_representative cov hm ht h hh g F
      (hg.of_le (by decide)) hF hge hFh

end AlmostSchur
