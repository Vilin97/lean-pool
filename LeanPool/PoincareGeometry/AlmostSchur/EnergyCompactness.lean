/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.LocalizationEnergy
public import LeanPool.PoincareGeometry.AlmostSchur.SobolevCompactness

/-! # Strong L² subsequences from intrinsic energy bounds

The chart graph bound is obtained from `LocalizationEnergy`, not assumed.
Reconstruction identifies the compactness limit sequence with the actual
global L² classes of the original C¹ functions.
-/

@[expose] public noncomputable section

open Bundle Set MeasureTheory
open scoped Manifold ContDiff Topology ENNReal
open RellichKondrachov.Geometry.Manifold.Sobolev FiniteChartData

namespace AlmostSchur

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless] [T2Space M] [CompactSpace M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [Nonempty M] [LindelofSpace M]

local instance energyCompactnessMeasurableM : MeasurableSpace M := borel M
local instance energyCompactnessBorelM : BorelSpace M := ⟨rfl⟩
local instance energyCompactnessMeasurableE : MeasurableSpace E := borel E
local instance energyCompactnessBorelE : BorelSpace E := ⟨rfl⟩
local instance energyCompactnessMetricZero : IsContMDiffRiemannianBundle I (↑(0 : ℕ)) E
    (TangentSpace I : M → Type _) :=
  IsContMDiffRiemannianBundle.of_le (n := 1) (by norm_num)
local instance energyCompactnessContinuousMetric :
    IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
  continuousRiemannianBundle_of_contMDiff (I := I)
local instance energyCompactnessFiniteVolume :
    IsFiniteMeasure (riemannianVolume (I := I) (M := M)) :=
  ⟨(riemannianVolume_finite_positive (I := I)).2⟩

/-- Energy and L² bounded C¹ sequences have strongly convergent subsequences
of their actual global L² classes. The `MemLp` witnesses can be any witnesses
for those functions; they are not additional quantitative bounds. -/
theorem exists_energyL2_subsequence
    (d : FiniteChartData (H := H) (M := M) I)
    (f : ℕ → M → ℝ) (hf : ∀ n, ContMDiff I 𝓘(ℝ, ℝ) 1 (f n))
    (hfLp : ∀ n, MemLp (f n) 2 (riemannianVolume (I := I)))
    (A : ℝ)
    (hbound : ∀ n, ‖(hfLp n).toLp (f n)‖ +
      Real.sqrt (dirichletForm (I := I) (f n) (f n)) ≤ A) :
    ∃ v : M →₂[riemannianVolume (I := I)] ℝ, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Filter.Tendsto
        (fun n => (hfLp (φ n)).toLp (f (φ n))) Filter.atTop (𝓝 v) := by
  let u (n : ℕ) : ↥(C1 (I := I)) := ⟨f n, hf n⟩
  obtain ⟨C, hC, hgraph⟩ := exists_norm_c1ToH1_le_energy_toLp d
  have hu (n : ℕ) : ‖c1ToH1 (d := d) (riemannianVolume (I := I)) (u n)‖ ≤ C * A :=
    (hgraph (u n) (hfLp n)).trans (mul_le_mul_of_nonneg_left (hbound n) hC.le)
  obtain ⟨v, φ, hφ, hlim⟩ := exists_sobolevL2_subsequence d
    (fun n => c1ToH1 (d := d) (riemannianVolume (I := I)) (u n)) (C * A) hu
  have heq (n : ℕ) :
      h1ToL2 (d := d) (riemannianVolume (I := I))
        (c1ToH1 (d := d) (riemannianVolume (I := I)) (u n)) =
      (hfLp n).toLp (f n) := by
    apply Lp.ext
    exact (h1ToL2_c1ToH1_ae_eq d (riemannianVolume (I := I)) (u n)).trans
      (hfLp n).coeFn_toLp.symm
  refine ⟨v, φ, hφ, ?_⟩
  simpa only [heq] using hlim

/-- A unit-L² sequence with energy at most one satisfies the compactness bound. -/
theorem exists_energyL2_subsequence_of_unit_norm
    (d : FiniteChartData (H := H) (M := M) I)
    (f : ℕ → M → ℝ) (hf : ∀ n, ContMDiff I 𝓘(ℝ, ℝ) 1 (f n))
    (hfLp : ∀ n, MemLp (f n) 2 (riemannianVolume (I := I)))
    (hnorm : ∀ n, ‖(hfLp n).toLp (f n)‖ = 1)
    (henergy : ∀ n, dirichletForm (I := I) (f n) (f n) ≤ 1) :
    ∃ v : M →₂[riemannianVolume (I := I)] ℝ, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Filter.Tendsto
        (fun n => (hfLp (φ n)).toLp (f (φ n))) Filter.atTop (𝓝 v) := by
  apply exists_energyL2_subsequence d f hf hfLp 2
  intro n
  have hs : Real.sqrt (dirichletForm (I := I) (f n) (f n)) ≤ 1 := by
    simpa using Real.sqrt_le_sqrt (henergy n)
  rw [hnorm n]
  linarith

end AlmostSchur
