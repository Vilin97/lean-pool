/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Topology.Algebra.Support

@[expose] public section

/-!
# Vorticity support along ordinary particle trajectories

The ODE lemma only needs a bound on the coefficient along one compact
trajectory. It does not assume a spatially uniform bound on the velocity or
its derivatives. The transport theorem below uses an ordinary differential
equation for vorticity, not a prescribed support condition.
-/

noncomputable section

open Set InnerProductSpace
open scoped Topology

namespace Euler.ComparatorBridge

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Uniqueness of the zero solution of a continuous linear ODE, allowing only
interior derivatives and continuity at the two endpoints. -/
theorem linearODE_eq_zero (w : ℝ → E) (B : ℝ → E →L[ℝ] E) (T : ℝ)
    (hw : ContinuousOn w (Icc 0 T))
    (hB : ContinuousOn B (Icc 0 T))
    (hd : ∀ t ∈ Ioo 0 T, HasDerivAt w (B t (w t)) t)
    (hzero : w 0 = 0) (t : ℝ) (ht : t ∈ Icc 0 T) : w t = 0 := by
  obtain ⟨K, hK⟩ := (isCompact_Icc.image_of_continuousOn hB).isBounded.exists_norm_le
  let q : ℝ → ℝ := fun r => Real.exp (-(2 * K) * r) * ‖w r‖ ^ 2
  have hq : ContinuousOn q (Icc 0 T) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul (hw.norm.pow 2)
  have hqd (r : ℝ) (hr : r ∈ Ioo 0 T) :
      HasDerivAt q
        (Real.exp (-(2 * K) * r) *
          (2 * ⟪w r, B r (w r)⟫_ℝ - 2 * K * ‖w r‖ ^ 2)) r := by
    have h := (((hasDerivAt_id r).const_mul (-(2 * K))).exp).mul (hd r hr).norm_sq
    convert! h using 1
    simp only [id_eq]
    ring
  have hanti : AntitoneOn q (Icc 0 T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 T) hq
    · intro r hr
      exact (hqd r (by simpa only [interior_Icc] using hr)).differentiableAt.differentiableWithinAt
    · intro r hr
      have hr' : r ∈ Ioo 0 T := by simpa only [interior_Icc] using hr
      rw [(hqd r hr').deriv]
      apply mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
      have hnorm : ‖B r (w r)‖ ≤ K * ‖w r‖ :=
        ((B r).le_opNorm (w r)).trans
          (mul_le_mul_of_nonneg_right (hK _ (mem_image_of_mem B ⟨hr'.1.le, hr'.2.le⟩))
            (norm_nonneg _))
      have hi := (real_inner_le_norm (w r) (B r (w r))).trans
        (mul_le_mul_of_nonneg_left hnorm (norm_nonneg _))
      nlinarith
  have hqt : q t ≤ 0 := by
    have hz : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, ht.1.trans ht.2⟩
    simpa only [q, hzero, norm_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero] using
      hanti hz ht ht.1
  have hsq : ‖w t‖ ^ 2 ≤ 0 := by
    exact nonpos_of_mul_nonpos_right hqt (Real.exp_pos _)
  have hn : ‖w t‖ = 0 := by nlinarith [norm_nonneg (w t)]
  exact norm_eq_zero.mp hn


/-- A field satisfying the stretching equation along a genuine trajectory
stays zero on that trajectory if it is initially zero. Coefficient
boundedness follows from continuity on the compact time interval. -/
theorem transport_eq_zero_along_trajectory
    (ω u : ℝ × E → E) (X : ℝ → E) (T : ℝ)
    (hω : ContinuousOn ω (Icc 0 T ×ˢ (univ : Set E)))
    (hX : ContinuousOn X (Icc 0 T))
    (hB : ContinuousOn (fun r => fderiv ℝ (fun x => u (r, x)) (X r)) (Icc 0 T))
    (hωdiff : ∀ r ∈ Ioo 0 T, DifferentiableAt ℝ ω (r, X r))
    (hmaterial : ∀ r ∈ Ioo 0 T,
      fderiv ℝ ω (r, X r) (1, u (r, X r)) =
        fderiv ℝ (fun x => u (r, x)) (X r) (ω (r, X r)))
    (hXderiv : ∀ r ∈ Ioo 0 T, HasDerivAt X (u (r, X r)) r)
    (hzero : ω (0, X 0) = 0) (t : ℝ) (ht : t ∈ Icc 0 T) :
    ω (t, X t) = 0 := by
  apply linearODE_eq_zero (fun r => ω (r, X r))
    (fun r => fderiv ℝ (fun x => u (r, x)) (X r)) T
  · exact hω.comp (continuousOn_id.prodMk hX) (fun r hr => ⟨hr, mem_univ _⟩)
  · exact hB
  · intro r hr
    have h := (hωdiff r hr).hasFDerivAt.comp_hasDerivAt r
      ((hasDerivAt_id r).prodMk (hXderiv r hr))
    simpa only [Function.comp_def, id_eq, hmaterial r hr] using h
  · exact hzero
  · exact ht

omit [InnerProductSpace ℝ E] in
/-- Compact initial support remains in its compact image whenever zero
initial values are propagated along every trajectory and the flow has a
right inverse at the specified time. -/
theorem tsupport_subset_flow_image
    (ω : ℝ → E → E) (X : ℝ → E → E) (Y : E → E) (t : ℝ)
    (hc : HasCompactSupport (ω 0)) (hX : Continuous (X t))
    (hXY : ∀ x, X t (Y x) = x)
    (hzero : ∀ a, ω 0 a = 0 → ω t (X t a) = 0) :
    tsupport (ω t) ⊆ X t '' tsupport (ω 0) := by
  apply closure_minimal _ (hc.image hX).isClosed
  intro x hx
  by_contra hnot
  have hz : ω 0 (Y x) = 0 := by
    by_contra hnz
    exact hnot ⟨Y x, subset_tsupport _ hnz, hXY x⟩
  exact hx (by simpa only [hXY x] using hzero (Y x) hz)

omit [InnerProductSpace ℝ E] in
/-- In particular each time slice has compact support. -/
theorem hasCompactSupport_of_flow_image
    (ω : ℝ → E → E) (X : ℝ → E → E) (Y : E → E) (t : ℝ)
    (hc : HasCompactSupport (ω 0)) (hX : Continuous (X t))
    (hXY : ∀ x, X t (Y x) = x)
    (hzero : ∀ a, ω 0 a = 0 → ω t (X t a) = 0) :
    HasCompactSupport (ω t) :=
  (hc.image hX).of_isClosed_subset (isClosed_tsupport _)
    (tsupport_subset_flow_image ω X Y t hc hX hXY hzero)

end Euler.ComparatorBridge
