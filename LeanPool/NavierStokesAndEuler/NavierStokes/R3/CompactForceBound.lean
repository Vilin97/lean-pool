/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ProblemStatement
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Topology.Algebra.Support

@[expose] public section

/-!
# A uniform spatial square-integral bound for compactly supported forces

Compact spacetime support gives one compact spatial set supporting all slices.
Continuity of the parameterized integral then supplies a finite bound on the
closed time interval `[0, 1]`.
-/


noncomputable section

open Set MeasureTheory

namespace NavierStokesR3.CompactForceBound

open NavierStokes.ProblemStatement

/-- A continuous force of compact spacetime support has uniformly bounded
spatial square integrals on the unit time interval. -/
theorem exists_uniform_l2sq_bound {f : VelocityField}
    (hf : Continuous f) (hcf : HasCompactSupport f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc (0 : ℝ) 1,
      Integrable (fun x : Space => ‖f (t, x)‖ ^ 2) volume ∧
        (∫ x : Space, ‖f (t, x)‖ ^ 2 ∂volume) ≤ C := by
  let K : Set Space := Prod.snd '' tsupport f
  have hK : IsCompact K := hcf.isCompact.image continuous_snd
  have hzero (t : ℝ) (x : Space) (hx : x ∉ K) : f (t, x) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hz
    exact hx ⟨(t, x), hz, rfl⟩
  have hcompact (t : ℝ) : HasCompactSupport (fun x : Space => ‖f (t, x)‖ ^ 2) := by
    apply HasCompactSupport.intro hK
    intro x hx
    simp only [hzero t x hx, norm_zero, zero_pow (by decide : 2 ≠ 0)]
  have hint (t : ℝ) : Integrable (fun x : Space => ‖f (t, x)‖ ^ 2) volume := by
    have hslice : Continuous (fun x : Space => f (t, x)) :=
      hf.comp (continuous_const.prodMk continuous_id)
    exact (hslice.norm.pow 2).integrable_of_hasCompactSupport (hcompact t)
  have hcontinuous :
      ContinuousOn (fun t : ℝ => ∫ x : Space, ‖f (t, x)‖ ^ 2 ∂volume)
        (Icc (0 : ℝ) 1) := by
    apply continuousOn_integral_of_compact_support hK
    · exact (hf.norm.pow 2).continuousOn
    · intro t x _ hx
      simp only [hzero t x hx, norm_zero, zero_pow (by decide : 2 ≠ 0)]
  obtain ⟨C, hC, hbound⟩ :=
    (isCompact_Icc.image_of_continuousOn hcontinuous).isBounded.exists_pos_norm_le
  refine ⟨C, hC.le, ?_⟩
  intro t ht
  refine ⟨hint t, ?_⟩
  have hnorm := hbound _ ⟨t, ht, rfl⟩
  exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hnorm)

end NavierStokesR3.CompactForceBound
