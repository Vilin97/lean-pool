/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.EulerCorrectionLocal
import LeanPool.NavierStokesAndEuler.Euler.DivergenceFreeHeat
public import LeanPool.NavierStokesAndEuler.Euler.QuadraticHeatLocal
import LeanPool.NavierStokesAndEuler.Euler.QuadraticMildPasting

/-! Actual divergence-free continuation of the concrete viscous correction equation. -/

section

/-! Genuine finite-time continuation of actual viscous mild solutions from an a priori Sobolev
bound. -/

@[expose] public section

noncomputable section

namespace EulerBoundedMildContinuation

open MeasureTheory Set EulerCylinderSobolevSpace EulerSobolevHeat EulerVolterraConvolution
  EulerUniformHeatLocal EulerQuadraticSource EulerTimePathGluing EulerQuadraticMildPasting
open scoped Topology

/-- The next actual time window ends at the smaller of one full step and the terminal time. -/
theorem advance_time_eq (a δ S : ℝ) : a+min δ (S-a) = min (a+δ) S := by
  by_cases h : δ ≤ S-a
  · rw [min_eq_left h, min_eq_left (by linarith : a+δ ≤ S)]
  · rw [min_eq_right (le_of_not_ge h), min_eq_right (by linarith : S ≤ a+δ)]
    ring

/-- Repeated genuine local windows reach each successive point of a fixed finite time grid. -/
theorem advance_grid (S δ a : ℝ) (hδ : 0 ≤ δ) (n : ℕ)
    (hgrid : min ((n : ℝ) * δ) S ≤ a) :
    min (((n+1 : ℕ) : ℝ)*δ) S ≤ a+min δ (S-a) := by
  rw [advance_time_eq]
  apply le_min
  · by_cases hn : (n : ℝ)*δ ≤ S
    · have hna : (n : ℝ)*δ ≤ a := by simpa only [min_eq_left hn] using hgrid
      apply (min_le_left _ _).trans
      push_cast
      nlinarith only [hna]
    · have hSa : S ≤ a := by simpa only [min_eq_right (le_of_not_ge hn)] using hgrid
      exact (min_le_right _ _).trans (by linarith)
  · exact min_le_right _ _

variable (period : ℝ) [Fact (0 < period)]

/-- An actual uniform Sobolev bound on partial solutions yields a genuine solution on the whole
prescribed interval.
The continuation is constructed by finitely many actual local heat solves and exact nonlinear
pasting. -/
theorem exists_global_mild_of_bound (q : ℕ) (ν : ℝ) (hν : 0 < ν) (S : ℝ) (hS : 0 < S)
    (R : ℝ) (hR : 0 ≤ R) (u₀ : SobolevSpace period (q + 1)) (hu₀ : ‖u₀‖ ≤ R)
    (C : Coefficients (Icc (0 : ℝ) S) (SobolevSpace period (q + 1)) (SobolevSpace period q))
    (hbound : ∀ (T : ℝ) (hT : 0 ≤ T) (hTS : T ≤ S)
      (u : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1))),
      (∀ t, u t = quadraticDuhamel period ν hν hT hTS C u₀ u t) → ‖u‖ ≤ R) :
    ∃ u : C(Icc (0 : ℝ) S, SobolevSpace period (q+1)),
      ‖u‖ ≤ R ∧ u ⟨0,le_rfl,hS.le⟩ = u₀ ∧
        ∀ t, u t = quadraticDuhamel period ν hν hS.le le_rfl C u₀ u t := by
  obtain ⟨δ,hδ,_,hlocal⟩ := exists_uniform_restart_time period q ν hν S hS R hR C
  have hind : ∀ n : ℕ, ∃ (a : ℝ) (ha : 0 ≤ a) (haS : a ≤ S),
      min ((n : ℝ)*δ) S ≤ a ∧
      ∃ u : C(Icc (0 : ℝ) a, SobolevSpace period (q+1)),
        ∀ t, u t = quadraticDuhamel period ν hν ha haS C u₀ u t := by
    intro n
    induction n with
    | zero =>
      obtain ⟨u,_,_,hsol⟩ := hlocal 0 0 le_rfl le_rfl (by linarith) hδ.le u₀ hu₀
      refine ⟨0,le_rfl,hS.le,?_,u,?_⟩
      · simpa only [Nat.cast_zero,zero_mul] using min_le_left (0 : ℝ) S
      · apply (quadratic_mild_window_iff period ν hν le_rfl hS.le C u₀ u).mpr
        exact hsol
    | succ n ih =>
      obtain ⟨a,ha,haS,hgrid,u,hsolu⟩ := ih
      let b := min δ (S-a)
      have hb : 0 ≤ b := le_min hδ.le (sub_nonneg.mpr haS)
      have hbδ : b ≤ δ := min_le_left _ _
      have habS : a+b ≤ S := by have h := min_le_right δ (S-a); dsimp [b]; linarith
      have hu : ‖u ⟨a,ha,le_rfl⟩‖ ≤ R :=
        (u.norm_coe_le_norm _).trans (hbound a ha haS u hsolu)
      obtain ⟨v,_,hv0,hsolv⟩ := hlocal a b ha hb habS hbδ (u ⟨a,ha,le_rfl⟩) hu
      let w := gluePath a b ha hb u v hv0.symm
      have hw := glue_quadratic_mild period ν hν C a b ha hb haS habS u v hv0.symm u₀ hsolu hsolv
      exact ⟨a+b,add_nonneg ha hb,habS,advance_grid S δ a hδ.le n hgrid,w,hw⟩
  obtain ⟨n,hn⟩ := exists_nat_ge (S/δ)
  have hN : S ≤ (n : ℝ)*δ := (div_le_iff₀ hδ).mp hn
  obtain ⟨a,ha,haS,hgrid,u,hsol⟩ := hind n
  have hSa : S ≤ a := by simpa only [min_eq_right hN] using hgrid
  have he : a = S := le_antisymm haS hSa
  subst a
  refine ⟨u,hbound S ha haS u hsol,?_,hsol⟩
  have hz := hsol ⟨0,le_rfl,hS.le⟩
  simpa only [quadraticDuhamel, mul_zero, Real.toNNReal_zero, heatOperator_zero,
      intervalIntegral.integral_same, add_zero] using hz

end EulerBoundedMildContinuation

end
end

end

@[expose] public section

noncomputable section

namespace EulerCorrectionContinuation

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCorrectionOperators
  EulerQuadraticSource EulerDivergenceFreeHeat EulerBoundedMildContinuation
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- Every actual partial zero-initial correction solution preserves the lifted divergence
constraint. -/
theorem correction_mild_divergenceFree {q : ℕ} (hq : 6 ≤ q) (ν : ℝ) (hν : 0 < ν)
    {T S : ℝ} (hT : 0 ≤ T) (hTS : T ≤ S)
    (D : CorrectionData period q (Icc (0 : ℝ) S))
    (e : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1)))
    (hsol : ∀ t, e t = quadraticDuhamel period ν hν hT hTS (D.coefficients period hq) 0 e t) :
    ∀ t, value period (e t) ∈ divergenceFreeSpace period D.κ D.direction := by
  let F := ((D.coefficients period hq).comp (timeInclusion hTS)).apply
  have hF : Continuous (fun p : Icc (0 : ℝ) T × SobolevSpace period (q+1) => F p.1 p.2) :=
    ((D.coefficients period hq).comp (timeInclusion hTS)).continuous
  have hz := mild_solution_preserves_gradient_zero period D.κ D.direction ν hν T hT 0
    (map_zero _) F hF (fun t u => D.source_gradient_zero period hq (timeInclusion hTS t) u) e hsol
  intro t
  exact (gradientEvaluation_zero_iff period D.κ D.direction (e t)).mp (hz t)

/-- A genuine a-priori Sobolev bound continues the actual zero-initial viscous Euler correction
across the prescribed interval. -/
theorem exists_global_correction_of_bound {q : ℕ} (hq : 6 ≤ q) (ν : ℝ) (hν : 0 < ν)
    (S : ℝ) (hS : 0 < S) (R : ℝ) (hR : 0 ≤ R)
    (D : CorrectionData period q (Icc (0 : ℝ) S))
    (hbound : ∀ (T : ℝ) (hT : 0 ≤ T) (hTS : T ≤ S)
      (e : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1))),
      (∀ t, e t = quadraticDuhamel period ν hν hT hTS (D.coefficients period hq) 0 e t) → ‖e‖ ≤ R) :
    ∃ e : C(Icc (0 : ℝ) S, SobolevSpace period (q+1)),
      ‖e‖ ≤ R ∧ e ⟨0,le_rfl,hS.le⟩ = 0 ∧
      (∀ t, value period (e t) ∈ divergenceFreeSpace period D.κ D.direction) ∧
      ∀ t, e t = quadraticDuhamel period ν hν hS.le le_rfl (D.coefficients period hq) 0 e t := by
  obtain ⟨e,he,hi,hsol⟩ := exists_global_mild_of_bound period q ν hν S hS R hR 0
    (by simpa only [norm_zero] using hR) (D.coefficients period hq) hbound
  exact ⟨e,he,hi,correction_mild_divergenceFree period hq ν hν hS.le le_rfl D e hsol,hsol⟩

end EulerCorrectionContinuation
