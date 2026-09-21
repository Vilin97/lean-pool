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

public import LeanPool.PoincareGeometry.AlmostSchur.LocalizationGradient
public import LeanPool.PoincareGeometry.AlmostSchur.GradientL2
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-! # Energy controls the finite-chart H¹ graph norm

Chart measures are exact pushforwards of the restricted manifold measure.
Consequently no density-comparison constants enter these estimates.
-/

@[expose] public noncomputable section

open Bundle Set MeasureTheory
open scoped Manifold ContDiff Topology ENNReal BigOperators
open RellichKondrachov.Geometry.Manifold.Sobolev FiniteChartData

namespace AlmostSchur

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless] [T2Space M] [CompactSpace M]

local instance localizationEnergyMeasurableM : MeasurableSpace M := borel M
local instance localizationEnergyBorelM : BorelSpace M := ⟨rfl⟩
local instance localizationEnergyMeasurableE : MeasurableSpace E := borel E
local instance localizationEnergyBorelE : BorelSpace E := ⟨rfl⟩

local notation "euclideanGrad" =>
  RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.grad

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] [CompactSpace M] in
/-- Pushforward and restriction turn a pointwise chart bound into an L² bound. -/
theorem norm_chart_toLp_le_lpNorm
    (d : FiniteChartData (H := H) (M := M) I) (μ : Measure M) (i : d.ι)
    {F : Type*} [NormedAddCommGroup F] (g : E → F)
    (hg : MemLp g 2 (chartMeasure (d := d) μ i))
    (q : M → ℝ) (hq : MemLp q 2 μ)
    (h : ∀ x ∈ (chartAt H (d.center i)).source,
      ‖g (extChartAt I (d.center i) x)‖ ≤ q x) :
    ‖hg.toLp g‖ ≤ lpNorm q 2 μ := by
  rw [Lp.norm_toLp, ← toReal_eLpNorm]
  apply ENNReal.toReal_mono hq.eLpNorm_ne_top
  rw [chartMeasure, eLpNorm_map_measure hg.aestronglyMeasurable (aemeasurable_extChartAt (d := d) μ i)]
  refine (eLpNorm_mono_ae_real (hg.aestronglyMeasurable.comp_aemeasurable
    (aemeasurable_extChartAt (d := d) μ i)) ?_).trans (eLpNorm_mono_measure q Measure.restrict_le_self)
  filter_upwards [ae_restrict_mem (isOpen_extChartAt_source (I := I) (d.center i)).measurableSet]
    with x hx
  exact h x (by simpa using hx)

omit [T2Space M] in
/-- The scalar chart graph component costs at most the global L² norm. -/
theorem norm_h1GraphChart_fst_le
    (d : FiniteChartData (H := H) (M := M) I) (μ : Measure M) [IsFiniteMeasure μ]
    (i : d.ι) (f : ↥(C1 (I := I))) :
    ‖(h1GraphChart (d := d) μ i f).1‖ ≤ lpNorm f.1 2 μ := by
  have hf : MemLp f.1 2 μ :=
    f.2.continuous.memLp_of_hasCompactSupport isClosed_closure.isCompact
  rw [h1GraphChart_fst]
  unfold RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.toL2
  have h := norm_chart_toLp_le_lpNorm d μ i (localize (d := d) f.1 i)
    (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.memLp_of_mem_C1c
      (chartMeasure (d := d) μ i)
      (localize_mem_C1c (d := d) f.2 i)) (fun x => ‖f.1 x‖) hf.norm ?_
  · simpa only [lpNorm_norm hf.aestronglyMeasurable] using h
  intro x hx
  have hx' : x ∈ (extChartAt I (d.center i)).source := by simpa using hx
  change ‖((extChartAt I (d.center i)).target.indicator
    (fun y => d.ρ i ((extChartAt I (d.center i)).symm y) *
      f.1 ((extChartAt I (d.center i)).symm y))) (extChartAt I (d.center i) x)‖ ≤ _
  rw [indicator_of_mem ((extChartAt I (d.center i)).map_source hx'),
    (extChartAt I (d.center i)).left_inv hx', norm_mul,
    Real.norm_eq_abs, abs_of_nonneg (d.ρ.nonneg i x)]
  exact mul_le_of_le_one_left (norm_nonneg _) (d.ρ.le_one i x)

section Gradient

variable [RiemannianBundle (TangentSpace I : M → Type _)]

omit [T2Space M] in
/-- Integrate any pointwise localized-gradient estimate against the exact chart measure. -/
theorem norm_h1GraphChart_snd_le
    (d : FiniteChartData (H := H) (M := M) I) (μ : Measure M) [IsFiniteMeasure μ]
    (i : d.ι) (f : ↥(C1 (I := I)))
    (hfG : MemLp (fun x => ‖gradient (I := I) f.1 x‖) 2 μ)
    {D B : ℝ} (hD : 0 ≤ D) (hB : 0 ≤ B)
    (hpoint : ∀ x ∈ (chartAt H (d.center i)).source,
      ‖euclideanGrad (localize (d := d) f.1 i) (extChartAt I (d.center i) x)‖ ≤
        D * |f.1 x| + B * ‖gradient (I := I) f.1 x‖) :
    ‖(h1GraphChart (d := d) μ i f).2‖ ≤
      D * lpNorm f.1 2 μ + B * lpNorm (fun x => ‖gradient (I := I) f.1 x‖) 2 μ := by
  have hf : MemLp f.1 2 μ :=
    f.2.continuous.memLp_of_hasCompactSupport isClosed_closure.isCompact
  have hsum := (hf.norm.const_smul D).add (hfG.const_smul B)
  rw [h1GraphChart_snd]
  unfold RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.toL2Grad
  refine (norm_chart_toLp_le_lpNorm d μ i _ _ _ hsum hpoint).trans ?_
  have h := lpNorm_add_le (hf.norm.const_smul D) (g := B • (fun x => ‖gradient (I := I) f.1 x‖))
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  simpa only [lpNorm_const_smul, NNReal.coe_mk, coe_nnnorm, Real.norm_eq_abs,
    abs_of_nonneg hD, abs_of_nonneg hB, lpNorm_norm hf.aestronglyMeasurable,
    lpNorm_fun_abs hf.aestronglyMeasurable] using h

omit [T2Space M] in
/-- Uniform graph-norm control before identifying the gradient L² norm with energy. -/
theorem exists_norm_c1ToH1_le_lpNorm
    [IsContinuousRiemannianBundle E (TangentSpace I : M → Type _)]
    (d : FiniteChartData (H := H) (M := M) I) (μ : Measure M) [IsFiniteMeasure μ] :
    ∃ C : ℝ, 0 < C ∧ ∀ f : ↥(C1 (I := I)),
      MemLp (fun x => ‖gradient (I := I) f.1 x‖) 2 μ →
      ‖c1ToH1 (d := d) μ f‖ ≤ C *
        (lpNorm f.1 2 μ + lpNorm (fun x => ‖gradient (I := I) f.1 x‖) 2 μ) := by
  classical
  choose D B hD hB hp using (fun i => exists_norm_grad_localize_le d i)
  let C : ℝ := 1 + ∑ i : d.ι, (D i + B i)
  have hsum : 0 ≤ ∑ i : d.ι, (D i + B i) := Finset.sum_nonneg fun i _ => add_nonneg (hD i) (hB i)
  have hC : 0 < C := by dsimp [C]; linarith
  refine ⟨C, hC, fun f hfG => ?_⟩
  have hCi (i : d.ι) : D i + B i ≤ C := by
    have h := Finset.single_le_sum (fun j _ => add_nonneg (hD j) (hB j))
      (Finset.mem_univ i)
    dsimp [C]
    linarith
  change ‖h1Graph (d := d) μ f‖ ≤ _
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hC.le (add_nonneg lpNorm_nonneg lpNorm_nonneg))).2
  intro i
  change ‖h1GraphChart (d := d) μ i f‖ ≤ _
  rw [Prod.norm_def]
  apply max_le
  · refine (norm_h1GraphChart_fst_le d μ i f).trans ?_
    have hC1 : 1 ≤ C := by dsimp [C]; linarith
    nlinarith [lpNorm_nonneg (f := f.1) (p := 2) (μ := μ),
      lpNorm_nonneg (f := fun x => ‖gradient (I := I) f.1 x‖) (p := 2) (μ := μ)]
  · refine (norm_h1GraphChart_snd_le d μ i f hfG (hD i) (hB i) (hp i f.1 f.2)).trans ?_
    have hdi : D i ≤ C := le_trans (le_add_of_nonneg_right (hB i)) (hCi i)
    have hbi : B i ≤ C := le_trans (le_add_of_nonneg_left (hD i)) (hCi i)
    nlinarith [lpNorm_nonneg (f := f.1) (p := 2) (μ := μ),
      lpNorm_nonneg (f := fun x => ‖gradient (I := I) f.1 x‖) (p := 2) (μ := μ)]

end Gradient

section Energy

variable [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [Nonempty M] [LindelofSpace M]

local instance localizationEnergyMetricZero : IsContMDiffRiemannianBundle I (↑(0 : ℕ)) E
    (TangentSpace I : M → Type _) :=
  IsContMDiffRiemannianBundle.of_le (n := 1) (by norm_num)

local instance localizationEnergyContinuousMetric :
    IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
  continuousRiemannianBundle_of_contMDiff (I := I)

local instance localizationEnergyFiniteVolume : IsFiniteMeasure (riemannianVolume (I := I) (M := M)) :=
  ⟨(riemannianVolume_finite_positive (I := I)).2⟩

/-- Actual Dirichlet energy controls the external max-Pi/product H¹ graph norm.
The real `lpNorm` here is taken against the actual normalized Riemannian volume. -/
theorem exists_norm_c1ToH1_le_energy (d : FiniteChartData (H := H) (M := M) I) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : ↥(C1 (I := I)),
      ‖c1ToH1 (d := d) (riemannianVolume (I := I)) f‖ ≤ C *
        (lpNorm f.1 2 (riemannianVolume (I := I)) +
          Real.sqrt (dirichletForm (I := I) f.1 f.1)) := by
  obtain ⟨C, hC, hb⟩ := exists_norm_c1ToH1_le_lpNorm d (riemannianVolume (I := I))
  refine ⟨C, hC, fun f => ?_⟩
  have h := hb f (memLp_norm_gradient f.2)
  have he := norm_toLp_gradient (I := I) f.2
  rw [Lp.norm_toLp, toReal_eLpNorm] at he
  simpa only [he] using h

/-- The same bound written with the norm of the actual global L² class. -/
theorem exists_norm_c1ToH1_le_energy_toLp (d : FiniteChartData (H := H) (M := M) I) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ↥(C1 (I := I)))
      (hf : MemLp f.1 2 (riemannianVolume (I := I))),
      ‖c1ToH1 (d := d) (riemannianVolume (I := I)) f‖ ≤
        C * (‖hf.toLp f.1‖ + Real.sqrt (dirichletForm (I := I) f.1 f.1)) := by
  obtain ⟨C, hC, hb⟩ := exists_norm_c1ToH1_le_energy d
  refine ⟨C, hC, fun f hf => ?_⟩
  simpa only [Lp.norm_toLp, toReal_eLpNorm] using hb f

end Energy

end AlmostSchur
