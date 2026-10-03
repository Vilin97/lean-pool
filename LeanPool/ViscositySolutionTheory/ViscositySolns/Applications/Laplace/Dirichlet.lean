/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Applications.Laplace.PerronSolution
public import LeanPool.ViscositySolutionTheory.ViscositySolns.Applications.Laplace.Barriers.Pair
public import LeanPool.ViscositySolutionTheory.ViscositySolns.Applications.Laplace.WeakHarmonic.Solution
public import LeanPool.ViscositySolutionTheory.ViscositySolns.Applications.Laplace.Euclidean
public import LeanPool.ViscositySolutionTheory.ViscositySolns.Applications.Laplace.Weyl.Weyl

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# The Dirichlet problem for harmonic functions

Let `U ⊆ ℝᵈ` be a bounded open set satisfying a uniform exterior sphere
condition, for instance a bounded `C²` domain
(`uniformExteriorSphere_of_contDiff_levelSet`). For Lipschitz data `g` there is
a classical harmonic function `h ∈ C(Ū) ∩ C²(U)` with `h = g` on `∂U`, and the
boundary modulus of continuity depends only on `U` and the Lipschitz constant.

The proof is an application of the CIL Perron method:

1. exterior-sphere barriers (`exists_laplace_barrierPair_of_uniformExteriorSphereSq`)
   give a Dirichlet barrier pair with a Hölder-`1/2` boundary modulus;
2. the Perron theorem with the Laplace comparison principle
   (`exists_laplace_dirichlet_of_barrierPair`) gives a viscosity solution that
   is continuous on `Ū` and attains `g`;
3. a continuous viscosity solution of `-Δu = 0` is weakly harmonic
   (`integral_lapTrace_mul_eq_zero_of_viscositySolution_laplace`), hence smooth
   and classically harmonic by Weyl's lemma (`Analysis.weyl_of_weaklyHarmonicOn`).

The modulus is `ϖ t = K √t`.
-/

@[expose] public noncomputable section

open Filter Topology Set
open scoped Laplacian ContDiff NNReal

namespace ViscositySolns

/--
**Existence for the harmonic Dirichlet problem** on a bounded open set with a
uniform exterior sphere condition, with a boundary modulus of continuity that
is uniform over Lipschitz data with a fixed constant. No size bound on the data is needed.
-/
theorem dirichlet_harmonic_modulus_of_uniformExteriorSphere {d : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hext : UniformExteriorSphere U) (L : ℝ≥0) :
    ∃ ϖ : ℝ → ℝ, Tendsto ϖ (𝓝[≥] 0) (𝓝 0) ∧
      ∀ g : EuclideanSpace ℝ (Fin d) → ℝ, LipschitzOnWith L g (closure U) →
        ∃ h : EuclideanSpace ℝ (Fin d) → ℝ, ContinuousOn h (closure U) ∧
          ContDiffOn ℝ 2 h U ∧ (∀ x ∈ U, Δ h x = 0) ∧ (∀ x ∈ frontier U, h x = g x) ∧
          ∀ x₀ ∈ frontier U, ∀ x ∈ closure U, |h x - g x₀| ≤ ϖ ‖x - x₀‖ := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · -- In dimension zero the space is a point, so the frontier is empty.
    refine ⟨fun t => t, tendsto_id.mono_left nhdsWithin_le_nhds, fun g _ => ?_⟩
    refine ⟨fun _ => 0, continuousOn_const, contDiffOn_const, fun x _ => by simp, ?_, ?_⟩
    · simp
    · simp
  -- Pass to `Point d` coordinates.
  set C : Set (Point d) := toPoint '' U with hCdef
  have hCopen : IsOpen C := isOpen_image_toPoint hU
  have hCbdd : Bornology.IsBounded C := isBounded_image_toPoint hUb
  obtain ⟨R, hR⟩ := hext.image_toPoint
  obtain ⟨K, hK, hbarrier⟩ :=
    exists_laplace_barrierPair_of_uniformExteriorSphereSq hCopen hCbdd hR (L : ℝ) L.2
  refine ⟨fun t => K * Real.sqrt t, ?_, fun g hg => ?_⟩
  · have h : Tendsto (fun t => K * Real.sqrt t) (𝓝 0) (𝓝 (K * Real.sqrt 0)) :=
      tendsto_const_nhds.mul (Real.continuous_sqrt.tendsto 0)
    rw [Real.sqrt_zero, mul_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  set g' : Point d → ℝ := g ∘ toPoint.symm with hg'def
  obtain ⟨B, hBl, hBu, hBlt, hBut, hBmod⟩ := hbarrier g' (LipschitzOnWith.abs_sub_le_eucSq hg)
  obtain ⟨w, hwsol, hwcont, hwbd, hwsq⟩ :=
    exists_laplace_dirichlet_of_barrierPair hd hCopen hCbdd B hBl hBu hBlt hBut
  have hmapsClosure : MapsTo toPoint (closure U) (closure C) := fun x hx => by
    rw [hCdef, ← image_toPoint_closure]
    exact mem_image_of_mem _ hx
  have hmapsFrontier : MapsTo toPoint (frontier U) (frontier C) := fun x hx => by
    rw [hCdef, ← image_toPoint_frontier]
    exact mem_image_of_mem _ hx
  -- Classical regularity through weak harmonicity and Weyl's lemma.
  have hweak : Analysis.WeaklyHarmonicOn MeasureTheory.volume (w ∘ toPoint) U :=
    weaklyHarmonicOn_of_forall_integral_lapTrace fun χ hχ hχc hχC =>
      integral_lapTrace_mul_eq_zero_of_viscositySolution_laplace hCopen hwsol
        (hwcont.mono subset_closure) hχ hχc hχC
  have hcontU : ContinuousOn (w ∘ toPoint) U :=
    (hwcont.comp toPoint.continuous.continuousOn hmapsClosure).mono subset_closure
  obtain ⟨hsmooth, hharm⟩ := Analysis.weyl_of_weaklyHarmonicOn hU hcontU hweak
  refine ⟨w ∘ toPoint, hwcont.comp toPoint.continuous.continuousOn hmapsClosure,
    hsmooth.of_le (WithTop.coe_le_coe.mpr le_top), hharm, fun x hx => ?_, ?_⟩
  · simp [hwbd _ (hmapsFrontier hx), hg'def]
  · intro x₀ hx₀ x hx
    have hsq := hwsq _ (hmapsClosure hx)
    have hmod := hBmod _ (hmapsFrontier hx₀) _ (hmapsClosure hx)
    have hdist : Real.sqrt (Real.sqrt (eucSq (toPoint x) (toPoint x₀))) =
        Real.sqrt ‖x - x₀‖ := by
      rw [eucSq_toPoint, Real.sqrt_sq dist_nonneg, dist_eq_norm]
    have hgx₀ : g' (toPoint x₀) = g x₀ := by simp [hg'def]
    rw [hdist, hgx₀] at hmod
    rw [abs_le]
    simp only [Function.comp_apply]
    constructor <;> linarith [hsq.1, hsq.2, hmod.1, hmod.2]

end ViscositySolns
