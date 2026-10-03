/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.Topology.Order.OrderClosed

/-!
# Pointwise weak-limit bounds and traces for Galerkin paths

These lemmas are the limit-identification half of the compactness step. They preserve the
uniform-in-time energy bound, the initial trace, and scalar weak continuity once a pointwise weak
subsequence has been extracted. They do not perform the extraction; the required uniform
equicontinuity estimates still have to be supplied by the Galerkin equation.
-/

@[expose] public section

noncomputable section

open Filter
open scoped Topology RealInnerProductSpace

namespace AVenhance.Infra.Parabolic.FourierGalerkin

/-- Weak convergence preserves a uniform norm bound in a real Hilbert space. -/
theorem norm_le_of_inner_tendsto {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {xSeq : ℕ → E} {x : E} {M : ℝ}
    (hlim : ∀ v, Tendsto (fun n => inner ℝ (xSeq n) v) atTop (𝓝 (inner ℝ x v)))
    (hbound : ∀ n, ‖xSeq n‖ ≤ M) : ‖x‖ ≤ M := by
  have hM : 0 ≤ M := (norm_nonneg (xSeq 0)).trans (hbound 0)
  have hquad : ‖x‖ ^ 2 ≤ M * ‖x‖ := by
    have hupper (n : ℕ) : inner ℝ (xSeq n) x ≤ M * ‖x‖ := by
      calc
        inner ℝ (xSeq n) x ≤ |inner ℝ (xSeq n) x| := le_abs_self _
        _ ≤ ‖xSeq n‖ * ‖x‖ := abs_real_inner_le_norm _ _
        _ ≤ M * ‖x‖ := mul_le_mul_of_nonneg_right (hbound n) (norm_nonneg _)
    have hlim' := le_of_tendsto' (hlim x) hupper
    simpa [real_inner_self_eq_norm_sq] using hlim'
  rcases eq_or_ne ‖x‖ 0 with hzero | hne
  · simpa [hzero] using hM
  · have hpos : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
    have hdiv := div_le_div_of_nonneg_right hquad (norm_nonneg x)
    have hresult : ‖x‖ ≤ M := by
      have hcancel : ‖x‖ ^ 2 / ‖x‖ = ‖x‖ := by
        rw [pow_two, mul_div_cancel_right₀ _ hne]
      have hcancelR : (M * ‖x‖) / ‖x‖ = M := by
        rw [mul_div_cancel_right₀ _ hne]
      rw [hcancel, hcancelR] at hdiv
      exact hdiv
    exact hresult

/-- A pointwise weak path limit inherits a weakly convergent sequence of initial traces. -/
theorem pointwiseWeakLimit_preserves_weak_initial {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {T : Type*} (t₀ : T)
    {uSeq : ℕ → T → E} {u : T → E} {u₀ : E}
    (hinit : ∀ v, Tendsto (fun n => inner ℝ (uSeq n t₀) v) atTop
      (𝓝 (inner ℝ u₀ v)))
    (hweak : ∀ v, Tendsto (fun n => inner ℝ (uSeq n t₀) v) atTop
      (𝓝 (inner ℝ (u t₀) v))) : u t₀ = u₀ := by
  have hpair (v : E) : inner ℝ (u t₀) v = inner ℝ u₀ v := by
    exact tendsto_nhds_unique (hweak v) (hinit v)
  have hleft : inner ℝ (u t₀ - u₀) (u t₀) = 0 := by
    rw [inner_sub_left, hpair (u t₀)]
    ring
  have hright : inner ℝ (u t₀ - u₀) u₀ = 0 := by
    rw [inner_sub_left, hpair u₀]
    ring
  have hzero : inner ℝ (u t₀ - u₀) (u t₀ - u₀) = 0 := by
    rw [inner_sub_right, hleft, hright]
    ring
  have hnorm : ‖u t₀ - u₀‖ = 0 := by
    have hsquare := real_inner_self_eq_norm_sq (u t₀ - u₀)
    rw [hzero] at hsquare
    nlinarith
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

/-- A bounded sequence in a separable real Hilbert space has a weakly convergent subsequence.

This is the one-space extraction primitive for the parabolic compactness argument. The energy
bound on the limit is included; applying it to a space-time graph carrier still requires that
carrier's separability and completeness to be established. -/
theorem exists_subseq_inner_tendsto_of_norm_bounded {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E] {xSeq : ℕ → E} {M : ℝ}
    (hbound : ∀ n, ‖xSeq n‖ ≤ M) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ x : E,
      (∀ v, Tendsto (fun n => inner ℝ (xSeq (φ n)) v) atTop (𝓝 (inner ℝ x v))) ∧
      ‖x‖ ≤ M := by
  let toWeak : E → WeakDual ℝ E := fun x =>
    StrongDual.toWeakDual (InnerProductSpace.toDualMap ℝ E x)
  let ball : Set (WeakDual ℝ E) :=
    WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ E) M
  have hmem (n : ℕ) : toWeak (xSeq n) ∈ ball := by
    change dist (WeakDual.toStrongDual (toWeak (xSeq n))) 0 ≤ M
    simpa [toWeak, dist_eq_norm] using hbound n
  obtain ⟨w, hw, φ, hφ, hconv⟩ :=
    (WeakDual.isSeqCompact_closedBall ℝ E (0 : StrongDual ℝ E) M).subseq_of_frequently_in
      (Filter.Frequently.of_forall hmem)
  let x : E := (InnerProductSpace.toDual ℝ E).symm (WeakDual.toStrongDual w)
  have hxpair (v : E) : inner ℝ x v = w v := by
    simp [x, InnerProductSpace.toDual_symm_apply]
  have hnorm : ‖x‖ = ‖WeakDual.toStrongDual w‖ := by
    dsimp [x]
    exact (InnerProductSpace.toDual ℝ E).symm.norm_map _
  have hball : ‖WeakDual.toStrongDual w‖ ≤ M := by
    have hw' : WeakDual.toStrongDual w ∈ Metric.closedBall (0 : StrongDual ℝ E) M := hw
    simpa [Metric.mem_closedBall, dist_eq_norm] using hw'
  refine ⟨φ, hφ, x, ?_, hnorm ▸ hball⟩
  intro v
  have heval : Tendsto (fun n => toWeak (xSeq (φ n)) v) atTop (𝓝 (w v)) := by
    have h := (WeakDual.eval_continuous (𝕜 := ℝ) (E := E) v).continuousAt.tendsto.comp hconv
    simpa [Function.comp_def] using h
  have hseq : (fun n => inner ℝ (xSeq (φ n)) v) =
      fun n => toWeak (xSeq (φ n)) v := by
    funext n
    simp [toWeak, InnerProductSpace.toDualMap_apply_apply,
      StrongDual.toWeakDual_apply]
  rw [hseq]
  simpa [hxpair v] using heval

/-- A single subsequence makes both components of a bounded product-Hilbert sequence converge
weakly. This packages simultaneous extraction for the space-time solution and its gradient. -/
theorem exists_subseq_inner_tendsto_pair_of_norm_bounded
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E] [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [CompleteSpace F] [TopologicalSpace.SeparableSpace F]
    {uSeq : ℕ → E} {vSeq : ℕ → F} {M : ℝ}
    (hbound : ∀ n, ‖WithLp.toLp 2 (uSeq n, vSeq n)‖ ≤ M) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ u : E, ∃ v : F,
      (∀ w, Tendsto (fun n => inner ℝ (uSeq (φ n)) w) atTop
        (𝓝 (inner ℝ u w))) ∧
      (∀ w, Tendsto (fun n => inner ℝ (vSeq (φ n)) w) atTop
        (𝓝 (inner ℝ v w))) ∧
      ‖WithLp.toLp 2 (u, v)‖ ≤ M := by
  let pairSeq : ℕ → WithLp 2 (E × F) := fun n => WithLp.toLp 2 (uSeq n, vSeq n)
  have hpair := exists_subseq_inner_tendsto_of_norm_bounded (xSeq := pairSeq) hbound
  obtain ⟨φ, hφ, pair, hweak, hpairBound⟩ := hpair
  let u : E := (WithLp.ofLp pair).1
  let v : F := (WithLp.ofLp pair).2
  have hweakE (w : E) :
      Tendsto (fun n => inner ℝ (uSeq (φ n)) w) atTop (𝓝 (inner ℝ u w)) := by
    have h := hweak (WithLp.toLp 2 (w, (0 : F)))
    have hseq : (fun n => inner ℝ (pairSeq (φ n)) (WithLp.toLp 2 (w, (0 : F)))) =
        fun n => inner ℝ (uSeq (φ n)) w := by
      funext n
      simp [pairSeq, WithLp.prod_inner_apply]
    have hlimit : inner ℝ pair (WithLp.toLp 2 (w, (0 : F))) = inner ℝ u w := by
      simp [u, WithLp.prod_inner_apply]
    rw [hseq, hlimit] at h
    exact h
  have hweakF (w : F) :
      Tendsto (fun n => inner ℝ (vSeq (φ n)) w) atTop (𝓝 (inner ℝ v w)) := by
    have h := hweak (WithLp.toLp 2 ((0 : E), w))
    have hseq : (fun n => inner ℝ (pairSeq (φ n)) (WithLp.toLp 2 ((0 : E), w))) =
        fun n => inner ℝ (vSeq (φ n)) w := by
      funext n
      simp [pairSeq, WithLp.prod_inner_apply]
    have hlimit : inner ℝ pair (WithLp.toLp 2 ((0 : E), w)) = inner ℝ v w := by
      simp [v, WithLp.prod_inner_apply]
    rw [hseq, hlimit] at h
    exact h
  have hpairEq : WithLp.toLp 2 (u, v) = pair := by
    change WithLp.toLp 2 (WithLp.ofLp pair) = pair
    exact WithLp.toLp_ofLp 2 pair
  refine ⟨φ, hφ, u, v, hweakE, hweakF, ?_⟩
  rw [hpairEq]
  exact hpairBound

end AVenhance.Infra.Parabolic.FourierGalerkin

end
