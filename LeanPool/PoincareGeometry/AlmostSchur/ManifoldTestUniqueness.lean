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

public import LeanPool.PoincareGeometry.AlmostSchur.ChartTestLiftRegularity
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Global smooth-test uniqueness on the manifold

A continuous scalar function annihilating all smooth tests is zero.  The proof
constructs an actual compactly supported coordinate bump, lifts it through the
chart, and uses positivity of the constructed Riemannian volume on nonempty
open sets.  This is the local-to-classical endpoint needed after elliptic
regularity produces a continuous Poisson representative.
-/

@[expose] public noncomputable section
open Bundle Set MeasureTheory
open Filter
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

local instance manifoldTestContinuousMetric :
    IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
  continuousRiemannianBundle_of_contMDiff (I := I)

local instance manifoldTestFiniteVolume :
    IsFiniteMeasure (riemannianVolume (I := I) (M := M)) :=
  ⟨(riemannianVolume_finite_positive (I := I)).2⟩

local instance manifoldTestOpenPosVolume :
    (riemannianVolume (I := I) (M := M)).IsOpenPosMeasure :=
  ⟨fun _ hs hne => ne_of_gt (riemannianVolume_open_pos (I := I) hs hne)⟩

/-- A continuous function whose pairing with every smooth function vanishes
is everywhere nonpositive.  Applying this also to its negative gives
uniqueness. -/
theorem continuous_nonpos_of_integral_mul_smooth_eq_zero
    (g : M → ℝ) (hg : Continuous g)
    (htest : ∀ φ : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ φ →
      (∫ x, g x * φ x ∂riemannianVolume (I := I)) = 0) :
    g ≤ 0 := by
  intro x
  by_contra hx
  have hgx : 0 < g x := lt_of_not_ge hx
  let z₀ := extChartAt I x x
  have hinv : (extChartAt I x).symm z₀ = x :=
    (extChartAt I x).left_inv (mem_extChartAt_source x)
  have hcomp : ContinuousAt (fun z => g ((extChartAt I x).symm z)) z₀ := by
    have hgAt : ContinuousAt g ((extChartAt I x).symm z₀) := by
      simpa only [hinv] using hg.continuousAt
    exact hgAt.comp (continuousAt_extChartAt_symm x)
  let s : Set E := (extChartAt I x).target ∩
    (fun z => g ((extChartAt I x).symm z)) ⁻¹' Ioi 0
  have hs : s ∈ 𝓝 z₀ := inter_mem
    ((isOpen_extChartAt_target x).mem_nhds (mem_extChartAt_target x))
    (hcomp.preimage_mem_nhds (Ioi_mem_nhds (by simpa only [hinv] using hgx)))
  obtain ⟨φ, hφs, hcφ, hφ, hφrange, hφone⟩ :=
    exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) hs
  let ψ := chartTestLift (I := I) x φ
  have hφtarget : tsupport φ ⊆ (extChartAt I x).target :=
    hφs.trans inter_subset_left
  have hψ : ContMDiff I 𝓘(ℝ, ℝ) ∞ ψ :=
    contMDiff_chartTestLift_of_order (⊤ : ℕ∞) x φ hφ hcφ hφtarget
  have hcψ : HasCompactSupport ψ :=
    hasCompactSupport_chartTestLift x φ hcφ hφtarget
  have hψx : ψ x = 1 := by
    dsimp [ψ]
    rw [chartTestLift_of_mem x φ (mem_extChartAt_source x)]
    exact hφone
  have hnonneg : 0 ≤ fun y => g y * ψ y := by
    intro y
    by_cases hy : y ∈ (extChartAt I x).source
    · have hψeq : ψ y = φ (extChartAt I x y) := by
        dsimp [ψ]
        exact chartTestLift_of_mem x φ hy
      change 0 ≤ g y * ψ y
      rw [hψeq]
      have hφnonneg : 0 ≤ φ (extChartAt I x y) :=
        (hφrange ⟨_, rfl⟩).1
      by_cases hφzero : φ (extChartAt I x y) = 0
      · have hφzero' : φ (I (chartAt H x y)) = 0 := by
          simpa only [extChartAt_coe, Function.comp_apply] using hφzero
        simp [hφzero']
      have hzsupport : extChartAt I x y ∈ tsupport φ :=
        subset_tsupport _ hφzero
      have hzs := hφs hzsupport
      have hgy : 0 < g y := by
        have hp := hzs.2
        change 0 < g ((extChartAt I x).symm (extChartAt I x y)) at hp
        rwa [(extChartAt I x).left_inv hy] at hp
      exact mul_nonneg hgy.le hφnonneg
    · have hψzero : ψ y = 0 := by
        dsimp [ψ, chartTestLift]
        exact indicator_of_notMem hy _
      simp [hψzero]
  have hpos :
      0 < ∫ y, g y * ψ y ∂riemannianVolume (I := I) :=
    (hg.mul hψ.continuous).integral_pos_of_hasCompactSupport_nonneg_nonzero
      hcψ.mul_left hnonneg (by
        show g x * ψ x ≠ 0
        rw [hψx, mul_one]
        exact hgx.ne')
  exact (ne_of_gt hpos) (htest ψ hψ)

/-- Continuous functions are determined pointwise by their pairings with all
smooth manifold tests. -/
theorem continuous_eq_zero_of_integral_mul_smooth_eq_zero
    (g : M → ℝ) (hg : Continuous g)
    (htest : ∀ φ : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ φ →
      (∫ x, g x * φ x ∂riemannianVolume (I := I)) = 0) :
    g = 0 := by
  have hle := continuous_nonpos_of_integral_mul_smooth_eq_zero g hg htest
  have hnegtest : ∀ φ : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ φ →
      (∫ x, (-g x) * φ x ∂riemannianVolume (I := I)) = 0 := by
    intro φ hφ
    simpa only [neg_mul, integral_neg, htest φ hφ, neg_zero]
  have hleneg := continuous_nonpos_of_integral_mul_smooth_eq_zero
    (fun x => -g x) hg.neg hnegtest
  funext x
  exact le_antisymm (hle x) (neg_nonpos.mp (hleneg x))

end AlmostSchur
