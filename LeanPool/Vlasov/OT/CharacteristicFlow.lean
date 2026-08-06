/-
Copyright (c) 2026 Joseph K. Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph K. Miller
-/
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Prod
import LeanPool.Vlasov.Basic
import LeanPool.Vlasov.ForMathlib.PicardLindelof
import LeanPool.Vlasov.OT.Coupling

/-!
# Characteristic flow for the Vlasov ODE + Lagrangian-Eulerian equivalence

This file builds on `LeanPool/Vlasov/OT/Coupling.lean` and provides the flow-side
infrastructure of the development:

* existence of the characteristic flow for the Vlasov field
  (`exists_vlasov_characteristicFlow`), via the vendored Picard–Lindelöf
  wrapper and a tight per-window construction valid for arbitrary Lipschitz
  constant;
* the Lagrangian → Eulerian equivalence — the pushforward of `f₀` under the
  characteristic flow satisfies the weak Vlasov equation;
* the localized solution predicates and the pushforward operator `Φ` feeding
  the well-posedness ladder, which lives in `LeanPool/Vlasov/OT/WellPosedness.lean`
  together with the marquee results.

The Grönwall step rests on the force estimate
‖∇W∗ρ − ∇W∗σ‖ ≤ L·W₁(ρ, σ) (`norm_convolveFunctionMeasure_sub_le`) and on
`wasserstein1_pushforward_le_iInf` from Coupling.lean.

**Mathlib-upstream targeting note.**  The position-Lipschitz of
convolution against a probability measure and the Picard-Lindelöf
wrapper for a phase-space ODE are domain-independent and Mathlib-
worthy; they would naturally live alongside the OT chapter in
`Mathlib/MeasureTheory/Wasserstein/CharacteristicFlow.lean` or split
between `Mathlib/Analysis/ODE/` and the OT chapter.  The Lagrangian →
Eulerian equivalence (pushforward of `f₀` under the characteristic
flow satisfies the weak Vlasov equation) is the genuine project
responsibility — a Fubini + measure-map +
differentiation-under-integral check that is not in Mathlib.

See `formalize/DESIGN.md` (in the source repository) for the overall design.
-/

namespace Vlasov

open MeasureTheory ENNReal

/-! ## Vlasov velocity field and its Lipschitz lemma -/

/-- The Vlasov phase-space vector field:
`b_t(x, v) := (v, −(∇W ∗ ρ_t)(x))`.

Note that the first component is the identity in `v` (the position
ODE `x' = v`) and the second component is the mean-field force
`−∇W ∗ ρ_t` evaluated at `x` (the velocity ODE `v' = −(∇W ∗ ρ)(x)`).
-/
noncomputable def vlasovVectorField
    {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (ρ : ℝ → Measure (PhysSpace d))
    (t : ℝ) (z : PhaseSpace d) : PhaseSpace d :=
  (z.2, -(convolveFunctionMeasure gradW (ρ t) z.1))

/-- Position-side Lipschitz of the convolution `∇W ∗ ρ`.
For `gradW` L-Lipschitz and `ρ` a probability measure with finite
first moment (which guarantees integrability of the kernel), the map
`x ↦ (∇W ∗ ρ)(x)` is L-Lipschitz.

Proof sketch: by `LipschitzWith.dist_le_mul` applied pointwise to
`gradW`, then integration over the probability measure `ρ`:
  ‖∫ y, gradW(x−y) ∂ρ − ∫ y, gradW(x'−y) ∂ρ‖
    = ‖∫ y, (gradW(x−y) − gradW(x'−y)) ∂ρ‖
    ≤ ∫ y, ‖gradW(x−y) − gradW(x'−y)‖ ∂ρ
    ≤ ∫ y, L · ‖x − x'‖ ∂ρ
    = L · ‖x − x'‖ · ρ(univ)
    = L · ‖x − x'‖   (probability measure).

The integrability hypotheses on `gradW(x − ·)` for two distinct `x`s
are needed for `integral_sub` and `norm_integral_le_integral_norm`
to fire.  At the dobrushin call site these follow from finite first
moment of `ρ` + Lipschitz growth of `gradW`. -/
lemma convolveFunctionMeasure_lipschitz_in_x
    {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : Measure (PhysSpace d)) [IsProbabilityMeasure ρ]
    (h_int : ∀ x : PhysSpace d, Integrable (fun y => gradW (x - y)) ρ) :
    LipschitzWith L (fun x => convolveFunctionMeasure gradW ρ x) := by
  refine LipschitzWith.of_dist_le_mul (fun x x' => ?_)
  unfold convolveFunctionMeasure
  rw [dist_eq_norm, ← integral_sub (h_int x) (h_int x')]
  -- Pointwise bound: ‖gradW(x − y) − gradW(x' − y)‖ ≤ L · ‖x − x'‖
  have h_pt : ∀ y, ‖gradW (x - y) - gradW (x' - y)‖ ≤ (L : ℝ) * ‖x - x'‖ :=
    fun y => by
    have h_sub : (x - y) - (x' - y) = x - x' := by
      rw [sub_sub_sub_cancel_right]
    have := hL.dist_le_mul (x - y) (x' - y)
    rw [dist_eq_norm, dist_eq_norm, h_sub] at this
    exact this
  -- Integrability of the pointwise bound function (a constant).
  have h_bound_int : Integrable (fun _ : PhysSpace d => (L : ℝ) * ‖x - x'‖) ρ :=
    integrable_const _
  -- Integrability of the norm of the difference, via mono'.
  have h_norm_int : Integrable (fun y => ‖gradW (x - y) - gradW (x' - y)‖) ρ :=
    Integrable.mono' h_bound_int ((h_int x).sub (h_int x')).norm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
        exact h_pt y)
  calc ‖∫ y, gradW (x - y) - gradW (x' - y) ∂ρ‖
      ≤ ∫ y, ‖gradW (x - y) - gradW (x' - y)‖ ∂ρ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ _, (L : ℝ) * ‖x - x'‖ ∂ρ :=
        integral_mono_ae h_norm_int h_bound_int (Filter.Eventually.of_forall h_pt)
    _ = (L : ℝ) * ‖x - x'‖ := by
        simp [integral_const, measureReal_def, measure_univ]

/-! ## Flow distance growth bound (Gronwall on the characteristic ODE)

A standalone regularity theorem about `IsCharacteristicFlow`: solutions of
the characteristic ODE have at most linear growth in their initial condition,
with a constant depending on `T`, the Lipschitz constant of `gradW`, and a
uniform first-moment bound on the measure curve `ρ`.

Math content: Gronwall on the position-velocity pair, using
  `‖(∇W ∗ ρ_t)(x)‖ ≤ ‖gradW 0‖ + L · (‖x‖ + ∫‖y‖dρ_t)`
as the velocity-field bound. -/

/-- **Flow distance growth bound** (`L`-Lipschitz `gradW`, uniform first moment
on `ρ`).  Solutions of the characteristic ODE grow at most linearly in their
initial condition: `‖(charX t z, charV t z)‖ ≤ C_T · (‖z‖ + 1)` for some
`C_T` depending only on `T`, `L`, `‖gradW 0‖`, and the uniform first-moment
bound `M_ρ`. -/
theorem flow_distance_growth_bound
    {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d))
    [∀ t, IsProbabilityMeasure (ρ t)]
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (hflow : IsCharacteristicFlow gradW ρ charX charV)
    (T : ℝ) (hT : 0 ≤ T)
    (M_ρ : ℝ) (hM_ρ_nn : 0 ≤ M_ρ)
    (hM_ρ : ∀ t ∈ Set.Icc 0 T, ∫ y, ‖y‖ ∂(ρ t) ≤ M_ρ)
    (h_y_int : ∀ t ∈ Set.Icc 0 T, Integrable (fun y : PhysSpace d => ‖y‖) (ρ t))
    (h_int : ∀ t (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ t)) :
    ∃ C_T, 0 ≤ C_T ∧
      ∀ t ∈ Set.Icc 0 T, ∀ z : PhaseSpace d,
        ‖(charX t z, charV t z)‖ ≤ C_T * (‖z‖ + 1) := by
  obtain ⟨hflow_init, hflow_x, hflow_v⟩ := hflow
  -- Gronwall parameters: K = 1 + L, ε₀ = ‖gradW 0‖ + L * M_ρ
  set K := 1 + (L : ℝ) with hK_def
  set ε₀ := ‖gradW 0‖ + (L : ℝ) * M_ρ with hε₀_def
  have hK_pos : 0 < K := by positivity
  have hε₀_nn : 0 ≤ ε₀ := by positivity
  -- Witness: C_T = gronwallBound 1 K ε₀ T
  use gronwallBound 1 K ε₀ T
  refine ⟨?_, ?_⟩
  · -- C_T ≥ 0: since gronwallBound 1 K ε₀ 0 = 1 and it's monotone
    have hmono := gronwallBound_mono (by norm_num : (0 : ℝ) ≤ 1) hε₀_nn hK_pos.le hT
    linarith [gronwallBound_x0 1 K ε₀]
  · intro t ht z
    -- Convolution bound: ‖(∇W ∗ ρ_t)(x)‖ ≤ ε₀ + L * ‖x‖
    have h_conv_bound : ∀ s ∈ Set.Icc 0 T, ∀ x : PhysSpace d,
        ‖convolveFunctionMeasure gradW (ρ s) x‖ ≤ ε₀ + (L : ℝ) * ‖x‖ := by
      intro s hs x
      unfold convolveFunctionMeasure
      -- Integrability of ‖x - y‖ via h_y_int and triangle
      have h_sub_int : Integrable (fun y => ‖x - y‖) (ρ s) :=
        Integrable.mono' ((integrable_const ‖x‖).add (h_y_int s hs))
          ((aestronglyMeasurable_const (b := x)).sub aestronglyMeasurable_id |>.norm)
          (Filter.Eventually.of_forall fun y => by
            simp only [Real.norm_of_nonneg (norm_nonneg _)]
            exact norm_sub_le x y)
      -- Integrability of the bound function
      have h_bnd_int : Integrable (fun y => ‖gradW 0‖ + (L : ℝ) * ‖x - y‖) (ρ s) :=
        (integrable_const _).add (h_sub_int.const_mul _)
      -- Pointwise bound: ‖gradW(x-y)‖ ≤ ‖gradW 0‖ + L*‖x-y‖
      have h_pt : ∀ y : PhysSpace d,
          ‖gradW (x - y)‖ ≤ ‖gradW 0‖ + (L : ℝ) * ‖x - y‖ := by
        intro y
        have hd := hL.dist_le_mul (x - y) 0
        simp only [dist_eq_norm, sub_zero] at hd
        have h_tri : ‖gradW (x - y)‖ ≤ ‖gradW 0‖ + ‖gradW (x - y) - gradW 0‖ := by
          have := norm_add_le (gradW (x - y) - gradW 0) (gradW 0)
          simp only [sub_add_cancel] at this; linarith
        linarith
      -- ‖∫ y, gradW(x - y) dρ_s‖ ≤ ∫ ‖gradW(x - y)‖ dρ_s ≤ ...
      calc ‖∫ y, gradW (x - y) ∂(ρ s)‖
          ≤ ∫ y, ‖gradW (x - y)‖ ∂(ρ s) := norm_integral_le_integral_norm _
        _ ≤ ∫ y, (‖gradW 0‖ + (L : ℝ) * ‖x - y‖) ∂(ρ s) :=
            integral_mono (h_int s x).norm h_bnd_int (fun y => h_pt y)
        _ = ‖gradW 0‖ + (L : ℝ) * ∫ y, ‖x - y‖ ∂(ρ s) := by
            rw [integral_add (integrable_const _) (h_sub_int.const_mul _)]
            simp [integral_const, measureReal_def, measure_univ,
                  integral_const_mul]
        _ ≤ ε₀ + (L : ℝ) * ‖x‖ := by
            have h_int_le : ∫ y, ‖x - y‖ ∂(ρ s) ≤ ‖x‖ + M_ρ := by
              calc ∫ y, ‖x - y‖ ∂(ρ s)
                  ≤ ∫ y, (‖x‖ + ‖y‖) ∂(ρ s) :=
                    integral_mono h_sub_int ((integrable_const _).add (h_y_int s hs))
                      (fun y => norm_sub_le x y)
                _ = ‖x‖ + ∫ y, ‖y‖ ∂(ρ s) := by
                    rw [integral_add (integrable_const _) (h_y_int s hs)]
                    simp [integral_const, measureReal_def, measure_univ]
                _ ≤ ‖x‖ + M_ρ := by linarith [hM_ρ s hs]
            simp only [hε₀_def]
            linarith [mul_le_mul_of_nonneg_left h_int_le (NNReal.coe_nonneg L)]
    -- Gronwall: apply norm_le_gronwallBound_of_norm_deriv_right_le
    -- f(s) = (charX s z, charV s z), f'(s) = (charV s z, -conv at charX s z)
    have h_f_cont : ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc 0 T) :=
      continuousOn_of_forall_continuousAt fun s _ =>
        (hflow_x s z).continuousAt.prodMk (hflow_v s z).continuousAt
    have h_deriv : ∀ s ∈ Set.Ico 0 T,
        HasDerivWithinAt (fun s => (charX s z, charV s z))
          (charV s z, -convolveFunctionMeasure gradW (ρ s) (charX s z)) (Set.Ici s) s :=
      fun s _ => ((hflow_x s z).prodMk (hflow_v s z)).hasDerivWithinAt
    have h_init : ‖(charX 0 z, charV 0 z)‖ ≤ ‖z‖ := by
      obtain ⟨hx0, hv0⟩ := hflow_init z
      simp [hx0, hv0, Prod.norm_def]
    have h_bound : ∀ s ∈ Set.Ico 0 T,
        ‖(charV s z, -convolveFunctionMeasure gradW (ρ s) (charX s z))‖ ≤
          K * ‖(charX s z, charV s z)‖ + ε₀ := by
      intro s hs
      have hs_mem : s ∈ Set.Icc 0 T := ⟨hs.1, le_of_lt hs.2⟩
      simp only [Prod.norm_def, norm_neg]
      have hFsz := le_max_left ‖charX s z‖ ‖charV s z‖
      have hGsz := le_max_right ‖charX s z‖ ‖charV s z‖
      have hM_nn : 0 ≤ max ‖charX s z‖ ‖charV s z‖ :=
        le_max_iff.mpr (Or.inl (norm_nonneg _))
      -- ‖charV s z‖ ≤ K * ‖f s‖ + ε₀
      have h_v_le : ‖charV s z‖ ≤ K * max ‖charX s z‖ ‖charV s z‖ + ε₀ :=
        calc ‖charV s z‖ ≤ max ‖charX s z‖ ‖charV s z‖ := hGsz
          _ ≤ K * max ‖charX s z‖ ‖charV s z‖ :=
              le_mul_of_one_le_left hM_nn (by linarith [NNReal.coe_nonneg L])
          _ ≤ K * max ‖charX s z‖ ‖charV s z‖ + ε₀ := le_add_of_nonneg_right hε₀_nn
      -- ‖conv‖ ≤ K * ‖f s‖ + ε₀
      have h_conv_le : ‖convolveFunctionMeasure gradW (ρ s) (charX s z)‖ ≤
          K * max ‖charX s z‖ ‖charV s z‖ + ε₀ :=
        calc ‖convolveFunctionMeasure gradW (ρ s) (charX s z)‖
            ≤ ε₀ + (L : ℝ) * ‖charX s z‖ := h_conv_bound s hs_mem _
          _ ≤ ε₀ + K * max ‖charX s z‖ ‖charV s z‖ := by
              have hLK : (L : ℝ) ≤ K := le_add_of_nonneg_left zero_le_one
              linarith [mul_le_mul_of_nonneg_left hFsz (NNReal.coe_nonneg L),
                        mul_le_mul_of_nonneg_right hLK hM_nn]
          _ = K * max ‖charX s z‖ ‖charV s z‖ + ε₀ := by ring
      exact max_le h_v_le h_conv_le
    -- Apply Gronwall
    have h_grw := norm_le_gronwallBound_of_norm_deriv_right_le
      h_f_cont h_deriv h_init h_bound t ht
    simp only [sub_zero] at h_grw
    -- gronwallBound ‖z‖ K ε₀ t ≤ gronwallBound 1 K ε₀ T * (‖z‖ + 1)
    calc ‖(charX t z, charV t z)‖
        ≤ gronwallBound ‖z‖ K ε₀ t := h_grw
      _ ≤ gronwallBound ‖z‖ K ε₀ T :=
          gronwallBound_mono (norm_nonneg _) hε₀_nn hK_pos.le ht.2
      _ ≤ gronwallBound 1 K ε₀ T * (‖z‖ + 1) := by
          rw [gronwallBound_of_K_ne_0 hK_pos.ne', gronwallBound_of_K_ne_0 hK_pos.ne']
          simp only [one_mul]
          have he1 : 0 ≤ Real.exp (K * T) - 1 :=
            by linarith [Real.one_le_exp (mul_nonneg hK_pos.le hT)]
          have hεK := div_nonneg hε₀_nn hK_pos.le
          nlinarith [norm_nonneg z, Real.exp_nonneg (K * T),
            mul_nonneg hεK he1, mul_nonneg (norm_nonneg z) (mul_nonneg hεK he1)]

/-- **Two-flow difference Gronwall bound** — the reusable core of the
integrated Dobrushin coupling bound.  The distance between two trajectories
`Φ_f · z₁`, `Φ_g · z₂` of flows generated by fields `b_f, b_g` (`b_f`
`L`-Lipschitz in space) grows by Gronwall: if the field difference *at the
second trajectory* is bounded by `ε` on `[0, T]` and the initial separation by
`δ`, then `‖Φ_f t z₁ - Φ_g t z₂‖ ≤ gronwallBound δ L ε t`.

Mirrors `flow_distance_growth_bound`'s Gronwall structure
(`norm_le_gronwallBound_of_norm_deriv_right_le`) but for the *difference* of two
flows.  In the integrated-bound application, `z₁ = ω.1`, `z₂ = ω.2` range over a
coupling `π₀` of `(f 0, g 0)`, `ε = (L : ℝ) * (wasserstein1 (f s) (g s)).toReal`
(the self-coupling diff-bound, uniform in the trajectory), and integrating this
pointwise bound over `π₀` against the pushforward bound gives the Dobrushin
estimate `W₁(f t, g t) ≤ … · W₁(f 0, g 0)`. -/
theorem flow_difference_growth_bound
    {α : Type*} [NormedAddCommGroup α] [NormedSpace ℝ α]
    (b_f b_g : ℝ → α → α) (L : NNReal) (hL_f : ∀ t, LipschitzWith L (b_f t))
    (Φ_f Φ_g : ℝ → α → α) (z₁ z₂ : α)
    (T : ℝ)
    (hcont_f : ContinuousOn (fun s => Φ_f s z₁) (Set.Icc 0 T))
    (hcont_g : ContinuousOn (fun s => Φ_g s z₂) (Set.Icc 0 T))
    (hΦ_f : ∀ s ∈ Set.Ico 0 T,
      HasDerivWithinAt (fun u => Φ_f u z₁) (b_f s (Φ_f s z₁)) (Set.Ici s) s)
    (hΦ_g : ∀ s ∈ Set.Ico 0 T,
      HasDerivWithinAt (fun u => Φ_g u z₂) (b_g s (Φ_g s z₂)) (Set.Ici s) s)
    (δ ε : ℝ) (h_init : ‖Φ_f 0 z₁ - Φ_g 0 z₂‖ ≤ δ)
    (h_diff : ∀ s ∈ Set.Icc 0 T,
      ‖b_f s (Φ_g s z₂) - b_g s (Φ_g s z₂)‖ ≤ ε) :
    ∀ t ∈ Set.Icc 0 T,
      ‖Φ_f t z₁ - Φ_g t z₂‖ ≤ gronwallBound δ (L : ℝ) ε t := by
  have hcont : ContinuousOn (fun s => Φ_f s z₁ - Φ_g s z₂) (Set.Icc 0 T) :=
    hcont_f.sub hcont_g
  have hderiv : ∀ s ∈ Set.Ico 0 T,
      HasDerivWithinAt (fun u => Φ_f u z₁ - Φ_g u z₂)
        (b_f s (Φ_f s z₁) - b_g s (Φ_g s z₂)) (Set.Ici s) s :=
    fun s hs => (hΦ_f s hs).sub (hΦ_g s hs)
  have hbound : ∀ s ∈ Set.Ico 0 T,
      ‖b_f s (Φ_f s z₁) - b_g s (Φ_g s z₂)‖ ≤
        (L : ℝ) * ‖Φ_f s z₁ - Φ_g s z₂‖ + ε := by
    intro s hs
    have hs_icc : s ∈ Set.Icc 0 T := ⟨hs.1, hs.2.le⟩
    have h_lip : ‖b_f s (Φ_f s z₁) - b_f s (Φ_g s z₂)‖ ≤
        (L : ℝ) * ‖Φ_f s z₁ - Φ_g s z₂‖ := by
      have := (hL_f s).dist_le_mul (Φ_f s z₁) (Φ_g s z₂)
      rwa [dist_eq_norm, dist_eq_norm] at this
    calc ‖b_f s (Φ_f s z₁) - b_g s (Φ_g s z₂)‖
        = ‖(b_f s (Φ_f s z₁) - b_f s (Φ_g s z₂)) +
            (b_f s (Φ_g s z₂) - b_g s (Φ_g s z₂))‖ := by congr 1; abel
      _ ≤ ‖b_f s (Φ_f s z₁) - b_f s (Φ_g s z₂)‖ +
            ‖b_f s (Φ_g s z₂) - b_g s (Φ_g s z₂)‖ := norm_add_le _ _
      _ ≤ (L : ℝ) * ‖Φ_f s z₁ - Φ_g s z₂‖ + ε :=
            add_le_add h_lip (h_diff s hs_icc)
  intro t ht
  have hg := norm_le_gronwallBound_of_norm_deriv_right_le hcont hderiv h_init hbound t ht
  simpa using hg

/-- **Per-trajectory mild (integral-form) difference bound.**
Mild-form companion to `flow_difference_growth_bound`:
the raw integral inequality
`‖γ_f t − γ_g t‖ ≤ ‖γ_f 0 − γ_g 0‖ + ∫₀ᵗ (L‖γ_f s − γ_g s‖ + ε s) ds`,
keeping the forcing `ε s` *inside* the integral.  After integrating this over
the base measure, the self-reference `ε s = L·W₁(f s,g s) ≤ L·Q(s)` is resolved
by `gronwall_mild_le` — avoiding the constant-`ε` smallness that
`flow_difference_growth_bound`'s closed form would force (and the blocked
windowing that smallness needs). -/
theorem flow_difference_mild_bound
    {α : Type*} [NormedAddCommGroup α] [NormedSpace ℝ α] [CompleteSpace α]
    (b_f b_g : ℝ → α → α) (L : NNReal) (hL_f : ∀ t, LipschitzWith L (b_f t))
    (γ_f γ_g : ℝ → α) (T : ℝ)
    (hcont_f : ContinuousOn γ_f (Set.Icc 0 T))
    (hcont_g : ContinuousOn γ_g (Set.Icc 0 T))
    (hderiv_f : ∀ s ∈ Set.Ioo (0 : ℝ) T,
      HasDerivWithinAt γ_f (b_f s (γ_f s)) (Set.Ioi s) s)
    (hderiv_g : ∀ s ∈ Set.Ioo (0 : ℝ) T,
      HasDerivWithinAt γ_g (b_g s (γ_g s)) (Set.Ioi s) s)
    (hint : IntervalIntegrable (fun s => b_f s (γ_f s) - b_g s (γ_g s))
      MeasureTheory.volume 0 T)
    (ε : ℝ → ℝ) (hε_int : IntervalIntegrable ε MeasureTheory.volume 0 T)
    (h_diff : ∀ s ∈ Set.Icc (0 : ℝ) T, ‖b_f s (γ_g s) - b_g s (γ_g s)‖ ≤ ε s) :
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      ‖γ_f t - γ_g t‖ ≤ ‖γ_f 0 - γ_g 0‖ +
        ∫ s in (0 : ℝ)..t, ((L : ℝ) * ‖γ_f s - γ_g s‖ + ε s) := by
  intro t ht
  have h0t : (0 : ℝ) ≤ t := ht.1
  have htT : t ≤ T := ht.2
  have hIcc_sub : Set.Icc (0 : ℝ) t ⊆ Set.Icc 0 T := Set.Icc_subset_Icc_right htT
  have hcont_diff : ContinuousOn (fun s => γ_f s - γ_g s) (Set.Icc 0 t) :=
    (hcont_f.mono hIcc_sub).sub (hcont_g.mono hIcc_sub)
  have hderiv_diff : ∀ s ∈ Set.Ioo (0 : ℝ) t,
      HasDerivWithinAt (fun s => γ_f s - γ_g s)
        (b_f s (γ_f s) - b_g s (γ_g s)) (Set.Ioi s) s := by
    intro s hs
    have hs' : s ∈ Set.Ioo (0 : ℝ) T := ⟨hs.1, hs.2.trans_le htT⟩
    exact (hderiv_f s hs').sub (hderiv_g s hs')
  have hint_t : IntervalIntegrable (fun s => b_f s (γ_f s) - b_g s (γ_g s))
      MeasureTheory.volume 0 t :=
    hint.mono_set (by
      rw [Set.uIcc_of_le h0t, Set.uIcc_of_le (h0t.trans htT)]; exact hIcc_sub)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le h0t hcont_diff
    hderiv_diff hint_t
  have hsplit : ∀ s ∈ Set.Icc (0 : ℝ) t,
      ‖b_f s (γ_f s) - b_g s (γ_g s)‖ ≤ (L:ℝ) * ‖γ_f s - γ_g s‖ + ε s := by
    intro s hs
    have hsT : s ∈ Set.Icc (0 : ℝ) T := hIcc_sub hs
    have h_lip : ‖b_f s (γ_f s) - b_f s (γ_g s)‖ ≤ (L:ℝ) * ‖γ_f s - γ_g s‖ := by
      have := (hL_f s).dist_le_mul (γ_f s) (γ_g s)
      rwa [dist_eq_norm, dist_eq_norm] at this
    calc ‖b_f s (γ_f s) - b_g s (γ_g s)‖
        = ‖(b_f s (γ_f s) - b_f s (γ_g s)) + (b_f s (γ_g s) - b_g s (γ_g s))‖ := by
          congr 1; abel
      _ ≤ ‖b_f s (γ_f s) - b_f s (γ_g s)‖ + ‖b_f s (γ_g s) - b_g s (γ_g s)‖ :=
          norm_add_le _ _
      _ ≤ (L:ℝ) * ‖γ_f s - γ_g s‖ + ε s := add_le_add h_lip (h_diff s hsT)
  have hci : IntervalIntegrable (fun s => (L:ℝ) * ‖γ_f s - γ_g s‖ + ε s)
      MeasureTheory.volume 0 t := by
    refine IntervalIntegrable.add (IntervalIntegrable.const_mul ?_ (L:ℝ))
      (hε_int.mono_set (by
        rw [Set.uIcc_of_le h0t, Set.uIcc_of_le (h0t.trans htT)]; exact hIcc_sub))
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le h0t]; exact hcont_diff.norm
  have hnorm_le : ‖∫ s in (0 : ℝ)..t, (b_f s (γ_f s) - b_g s (γ_g s))‖ ≤
      ∫ s in (0 : ℝ)..t, ((L:ℝ) * ‖γ_f s - γ_g s‖ + ε s) := by
    calc ‖∫ s in (0 : ℝ)..t, (b_f s (γ_f s) - b_g s (γ_g s))‖
        ≤ ∫ s in (0 : ℝ)..t, ‖b_f s (γ_f s) - b_g s (γ_g s)‖ :=
          intervalIntegral.norm_integral_le_integral_norm h0t
      _ ≤ ∫ s in (0 : ℝ)..t, ((L:ℝ) * ‖γ_f s - γ_g s‖ + ε s) :=
          intervalIntegral.integral_mono_on h0t hint_t.norm hci hsplit
  have ha_le : ‖γ_f t - γ_g t‖ ≤ ‖γ_f 0 - γ_g 0‖ +
      ‖∫ s in (0 : ℝ)..t, (b_f s (γ_f s) - b_g s (γ_g s))‖ := by
    have heq : (γ_f t - γ_g t) - (γ_f 0 - γ_g 0) =
        ∫ s in (0 : ℝ)..t, (b_f s (γ_f s) - b_g s (γ_g s)) := hftc.symm
    calc ‖γ_f t - γ_g t‖
        = ‖(γ_f 0 - γ_g 0) + ((γ_f t - γ_g t) - (γ_f 0 - γ_g 0))‖ := by congr 1; abel
      _ ≤ ‖γ_f 0 - γ_g 0‖ + ‖(γ_f t - γ_g t) - (γ_f 0 - γ_g 0)‖ := norm_add_le _ _
      _ = ‖γ_f 0 - γ_g 0‖ + ‖∫ s in (0 : ℝ)..t, (b_f s (γ_f s) - b_g s (γ_g s))‖ := by
          rw [heq]
  linarith [ha_le, hnorm_le]

/-- **Integrate a per-trajectory mild bound over the base measure (Tonelli step).**
Given a base probability measure `π` on `Ω` and a family `w : ℝ → Ω → α`, if each
trajectory satisfies the mild bound `‖w t ω‖ ≤ ‖w 0 ω‖ + ∫₀ᵗ (L‖w s ω‖ + ε s) ds`,
then the integrated quantity `Q t := ∫ ‖w t ω‖ ∂π` satisfies
`Q t ≤ Q 0 + ∫₀ᵗ (L · Q s + ε s) ds`. The `∫₀ᵗ L‖w s ω‖` term swaps via Tonelli. -/
theorem integral_mild_bound
    {Ω α : Type*} [MeasurableSpace Ω] [NormedAddCommGroup α]
    [MeasurableSpace α] [BorelSpace α]
    (π : Measure Ω) [IsProbabilityMeasure π]
    (w : ℝ → Ω → α) (L : ℝ) (hL : 0 ≤ L) (ε : ℝ → ℝ) (T : ℝ) (hT : 0 ≤ T)
    -- joint-measurability inputs (Carathéodory: continuous-in-time + measurable-in-ω)
    (hw_cont : ∀ ω, Continuous (fun s => w s ω))
    (hw_meas : ∀ s, Measurable (w s))
    -- domination: ‖w s ω‖ ≤ dom ω uniformly on [0,T], dom integrable
    (dom : Ω → ℝ) (hdom_int : Integrable dom π)
    (hdom : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ ω, ‖w s ω‖ ≤ dom ω)
    (hε_int : IntervalIntegrable ε MeasureTheory.volume 0 T)
    (hε_nn : ∀ s ∈ Set.Icc (0 : ℝ) T, 0 ≤ ε s)
    -- the per-trajectory mild bound (e.g. from flow_difference_mild_bound)
    (hper : ∀ ω, ∀ t ∈ Set.Icc (0 : ℝ) T,
      ‖w t ω‖ ≤ ‖w 0 ω‖ + ∫ s in (0 : ℝ)..t, (L * ‖w s ω‖ + ε s)) :
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      (∫ ω, ‖w t ω‖ ∂π) ≤ (∫ ω, ‖w 0 ω‖ ∂π) +
        ∫ s in (0 : ℝ)..t, (L * (∫ ω, ‖w s ω‖ ∂π) + ε s) := by
  -- joint measurability of `(s, ω) ↦ w s ω` and of its norm
  have hjoint : Measurable (Function.uncurry w) :=
    measurable_uncurry_of_continuous_of_measurable hw_cont hw_meas
  have hjoint_norm : Measurable (fun p : ℝ × Ω => ‖w p.1 p.2‖) := hjoint.norm
  -- abbreviation Q s := ∫ ω, ‖w s ω‖ ∂π
  set Q : ℝ → ℝ := fun s => ∫ ω, ‖w s ω‖ ∂π with hQ
  intro t ht
  have h0t : (0 : ℝ) ≤ t := ht.1
  have htT : t ≤ T := ht.2
  have hIcc_sub : Set.Icc (0 : ℝ) t ⊆ Set.Icc 0 T := Set.Icc_subset_Icc_right htT
  -- `w 0 ·` and `w t ·` are integrable over π (dominated by `dom`)
  have h0_mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_refl 0, hT⟩
  have ht_mem : t ∈ Set.Icc (0 : ℝ) T := ht
  have hint0 : Integrable (fun ω => ‖w 0 ω‖) π := by
    refine hdom_int.mono' ((hw_meas 0).norm.aestronglyMeasurable) ?_
    filter_upwards with ω
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact hdom 0 h0_mem ω
  have hintt : Integrable (fun ω => ‖w t ω‖) π := by
    refine hdom_int.mono' ((hw_meas t).norm.aestronglyMeasurable) ?_
    filter_upwards with ω
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact hdom t ht_mem ω
  -- the inner integrand `g s ω := L * ‖w s ω‖ + ε s`
  set g : ℝ → Ω → ℝ := fun s ω => L * ‖w s ω‖ + ε s with hg
  -- product measure for the Tonelli swap
  -- `volume.restrict (Set.uIoc 0 t)` is a finite measure (`uIoc 0 t = Ioc 0 t`)
  have huIoc : Set.uIoc (0 : ℝ) t = Set.Ioc 0 t := Set.uIoc_of_le h0t
  have hvol_lt : MeasureTheory.volume (Set.uIoc (0 : ℝ) t) < ⊤ := by
    rw [huIoc, Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
  haveI hfin_restrict : IsFiniteMeasure (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) t)) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]; exact hvol_lt
  -- `ε` is integrable over `volume.restrict (uIoc 0 t)`
  have hε_int_t : IntervalIntegrable ε MeasureTheory.volume 0 t :=
    hε_int.mono_set (by
      rw [Set.uIcc_of_le h0t, Set.uIcc_of_le hT]; exact Set.Icc_subset_Icc_right htT)
  have hε_intOn : Integrable ε (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) t)) :=
    hε_int_t.def'
  -- AEStronglyMeasurability of `uncurry g` over the product measure
  have hg_aesm : AEStronglyMeasurable (Function.uncurry g)
      ((MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) t)).prod π) := by
    have h1 : AEStronglyMeasurable (fun p : ℝ × Ω => L * ‖w p.1 p.2‖)
        ((MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) t)).prod π) :=
      (measurable_const.mul hjoint_norm).aestronglyMeasurable
    have h2 : AEStronglyMeasurable (fun p : ℝ × Ω => ε p.1)
        ((MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) t)).prod π) :=
      hε_intOn.aestronglyMeasurable.comp_fst
    exact h1.add h2
  -- product integrability of `uncurry g`, via the dominator `L·dom(ω) + ε(s)`
  have hdom_prod : Integrable (fun p : ℝ × Ω => L * dom p.2 + ε p.1)
      ((MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) t)).prod π) :=
    ((hdom_int.const_mul L).comp_snd
        (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) t))).add (hε_intOn.comp_fst π)
  have hae_fst : ∀ᵐ p : ℝ × Ω
      ∂((MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) t)).prod π), p.1 ∈ Set.uIoc (0 : ℝ) t :=
    (MeasureTheory.Measure.quasiMeasurePreserving_fst).tendsto_ae.eventually
      (MeasureTheory.ae_restrict_mem measurableSet_uIoc)
  have hg_int : Integrable (Function.uncurry g)
      ((MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) t)).prod π) := by
    refine hdom_prod.mono' hg_aesm ?_
    filter_upwards [hae_fst] with p hp
    have hp_icc : p.1 ∈ Set.Icc (0 : ℝ) T := by
      rw [huIoc] at hp; exact ⟨le_of_lt hp.1, hp.2.trans htT⟩
    have hwle : ‖w p.1 p.2‖ ≤ dom p.2 := hdom p.1 hp_icc p.2
    have hεnn : 0 ≤ ε p.1 := hε_nn p.1 hp_icc
    have hg_nn : 0 ≤ L * ‖w p.1 p.2‖ + ε p.1 :=
      add_nonneg (mul_nonneg hL (norm_nonneg _)) hεnn
    change ‖L * ‖w p.1 p.2‖ + ε p.1‖ ≤ L * dom p.2 + ε p.1
    rw [Real.norm_of_nonneg hg_nn]
    nlinarith [mul_le_mul_of_nonneg_left hwle hL]
  -- inner intervalIntegral = integral against the restricted measure
  have hconv : ∀ ω, (∫ s in (0 : ℝ)..t, g s ω)
      = ∫ s, g s ω ∂(MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) t)) := by
    intro ω
    rw [intervalIntegral.integral_of_le h0t, ← huIoc]
  -- marginal integrability `ω ↦ ∫ s, g s ω`
  have hmarg : Integrable
      (fun ω => ∫ s, g s ω ∂(MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) t))) π :=
    hg_int.integral_prod_right
  have hinner_int : Integrable (fun ω => ∫ s in (0 : ℝ)..t, g s ω) π := by
    simpa only [hconv] using hmarg
  -- per-`s` identity  ∫ ω, g s ω ∂π = L · (∫ ω, ‖w s ω‖ ∂π) + ε s
  have hg_int_s : ∀ s ∈ Set.Icc (0 : ℝ) T, Integrable (fun ω => ‖w s ω‖) π := by
    intro s hs
    refine hdom_int.mono' ((hw_meas s).norm.aestronglyMeasurable) ?_
    filter_upwards with ω
    rw [Real.norm_of_nonneg (norm_nonneg _)]; exact hdom s hs ω
  have hQg : ∀ s ∈ Set.Icc (0 : ℝ) T,
      (∫ ω, g s ω ∂π) = L * (∫ ω, ‖w s ω‖ ∂π) + ε s := by
    intro s hs
    simp only [hg]
    rw [integral_add ((hg_int_s s hs).const_mul L) (integrable_const _), integral_const_mul]
    congr 1
    simp [integral_const, measureReal_def, measure_univ]
  -- the double integral, via Tonelli
  have hdouble : (∫ ω, (∫ s in (0 : ℝ)..t, g s ω) ∂π)
      = ∫ s in (0 : ℝ)..t, (L * (∫ ω, ‖w s ω‖ ∂π) + ε s) := by
    calc (∫ ω, (∫ s in (0 : ℝ)..t, g s ω) ∂π)
        = ∫ ω, (∫ s, g s ω ∂(MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) t))) ∂π := by
          simp only [hconv]
      _ = ∫ s, (∫ ω, g s ω ∂π) ∂(MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) t)) :=
          (MeasureTheory.integral_integral_swap hg_int).symm
      _ = ∫ s in (0 : ℝ)..t, (∫ ω, g s ω ∂π) := by
          rw [huIoc, ← intervalIntegral.integral_of_le h0t]
      _ = ∫ s in (0 : ℝ)..t, (L * (∫ ω, ‖w s ω‖ ∂π) + ε s) := by
          refine intervalIntegral.integral_congr (fun s hs => ?_)
          rw [Set.uIcc_of_le h0t] at hs
          exact hQg s ⟨hs.1, hs.2.trans htT⟩
  -- assemble
  calc (∫ ω, ‖w t ω‖ ∂π)
      ≤ ∫ ω, (‖w 0 ω‖ + ∫ s in (0 : ℝ)..t, g s ω) ∂π :=
        integral_mono hintt (hint0.add hinner_int) (fun ω => hper ω t ht)
    _ = (∫ ω, ‖w 0 ω‖ ∂π) + ∫ ω, (∫ s in (0 : ℝ)..t, g s ω) ∂π :=
        integral_add hint0 hinner_int
    _ = (∫ ω, ‖w 0 ω‖ ∂π) + ∫ s in (0 : ℝ)..t, (L * (∫ ω, ‖w s ω‖ ∂π) + ε s) := by
        rw [hdouble]

/-- **Integrated coupling-Gronwall bound** (base-measure generic).

Given a base probability measure `π` on `Ω` and two parameter-families of
trajectories `X_f, X_g : ℝ → Ω → α` solving ODEs with `L`-Lipschitz vector fields
`b_f, b_g` on `[0, T]`, with a cross-field bound `‖b_f s y - b_g s y‖ ≤ ε s` whose
amplitude `ε s` is **self-referentially** controlled by the integrated trajectory
distance `Q s := ∫ ω, ‖X_f s ω - X_g s ω‖ ∂π` (i.e. `ε s ≤ L · Q s`), the
integrated distance obeys the closed Gronwall bound
`Q t ≤ Q 0 · exp (2 L t)` on `[0, T]`.

**Composition** (the collapse pipeline):
* per-`ω`, `flow_difference_mild_bound` gives the mild integral inequality
  `‖X_f t ω - X_g t ω‖ ≤ ‖X_f 0 ω - X_g 0 ω‖ + ∫₀ᵗ (L‖X_f s ω - X_g s ω‖ + ε s)`;
* `integral_mild_bound` integrates this over `π` (Tonelli on a nonnegative
  integrand), yielding `Q t ≤ Q 0 + ∫₀ᵗ (L·Q s + ε s)`;
* the self-reference `ε s ≤ L·Q s` collapses the integrand to `2 L · Q s`;
* `gronwall_mild_le` (scalar mild Gronwall) closes to `Q 0 · exp (2 L t)`.

**Clamp bridge**: `integral_mild_bound` and the DCT continuity of `Q`
require *global*-in-`s` continuity, but the flow regularity is only on the
window `[0, T]`.  We work with the clamped flow `s ↦ X_f (clamp s) ω` (globally
continuous, agreeing with `X_f` on `[0, T]`), apply the window machinery to it,
and transfer back on `[0, T]` where `clamp = id` via integrand congruence.

**Base-measure genericity**: `π` is abstract, so this serves both the
uniqueness call site (`π = f 0`, `Q 0 = 0`, Foundation-B-free) and the
mean-field call site (`π` an optimal coupling, `Q 0 = W₁(f 0, g 0)`). -/
theorem integrated_coupling_gronwall_bound
    {Ω α : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup α] [NormedSpace ℝ α] [CompleteSpace α]
    [MeasurableSpace α] [BorelSpace α] [MeasurableSub₂ α]
    (π : Measure Ω) [IsProbabilityMeasure π]
    (X_f X_g : ℝ → Ω → α) (b_f b_g : ℝ → α → α) (L : NNReal) (T : ℝ) (hT : 0 ≤ T)
    (hL_f : ∀ t, LipschitzWith L (b_f t))
    -- per-`ω` flow regularity (matches `flow_difference_mild_bound`)
    (hcont_f : ∀ ω, ContinuousOn (fun s => X_f s ω) (Set.Icc 0 T))
    (hcont_g : ∀ ω, ContinuousOn (fun s => X_g s ω) (Set.Icc 0 T))
    (hderiv_f : ∀ ω, ∀ s ∈ Set.Ioo (0 : ℝ) T,
      HasDerivWithinAt (fun s => X_f s ω) (b_f s (X_f s ω)) (Set.Ioi s) s)
    (hderiv_g : ∀ ω, ∀ s ∈ Set.Ioo (0 : ℝ) T,
      HasDerivWithinAt (fun s => X_g s ω) (b_g s (X_g s ω)) (Set.Ioi s) s)
    (hint : ∀ ω, IntervalIntegrable
      (fun s => b_f s (X_f s ω) - b_g s (X_g s ω)) MeasureTheory.volume 0 T)
    -- measurability + domination for the Tonelli / DCT
    (hmeas_f : ∀ s, Measurable (X_f s)) (hmeas_g : ∀ s, Measurable (X_g s))
    (dom : Ω → ℝ) (hdom_int : Integrable dom π)
    (hdom : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ ω, ‖X_f s ω - X_g s ω‖ ≤ dom ω)
    -- the cross-field bound `ε` and its self-reference to `Q`
    (ε : ℝ → ℝ) (hε_int : IntervalIntegrable ε MeasureTheory.volume 0 T)
    (hε_nn : ∀ s ∈ Set.Icc (0 : ℝ) T, 0 ≤ ε s)
    (h_diff : ∀ ω, ∀ s ∈ Set.Icc (0 : ℝ) T,
      ‖b_f s (X_g s ω) - b_g s (X_g s ω)‖ ≤ ε s)
    (h_self : ∀ s ∈ Set.Icc (0 : ℝ) T,
      ε s ≤ (L : ℝ) * ∫ ω, ‖X_f s ω - X_g s ω‖ ∂π) :
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      (∫ ω, ‖X_f t ω - X_g t ω‖ ∂π) ≤
        (∫ ω, ‖X_f 0 ω - X_g 0 ω‖ ∂π) * Real.exp (2 * (L:ℝ) * t) := by
  -- clamp into `[0, T]` (opaque; used only through its three properties)
  obtain ⟨clamp, hclamp_cont, hclamp_mem, hclamp_id⟩ :
      ∃ clamp : ℝ → ℝ, Continuous clamp ∧ (∀ s, clamp s ∈ Set.Icc (0 : ℝ) T) ∧
        (∀ s ∈ Set.Icc (0 : ℝ) T, clamp s = s) := by
    refine ⟨fun s => max 0 (min s T), ?_, ?_, ?_⟩
    · exact continuous_const.max (continuous_id.min continuous_const)
    · intro s; exact ⟨le_max_left _ _, max_le hT (min_le_right _ _)⟩
    · intro s hs; change max 0 (min s T) = s
      rw [min_eq_left hs.2, max_eq_right hs.1]
  -- the clamped difference flow `W s ω = X_f (clamp s) ω - X_g (clamp s) ω`
  set W : ℝ → Ω → α := fun s ω => X_f (clamp s) ω - X_g (clamp s) ω with hW_def
  have hW_cont : ∀ ω, Continuous (fun s => W s ω) := by
    intro ω; simp only [hW_def]
    exact ((hcont_f ω).sub (hcont_g ω)).comp_continuous hclamp_cont hclamp_mem
  have hW_meas : ∀ s, Measurable (W s) := by
    intro s; simp only [hW_def]
    exact (hmeas_f (clamp s)).sub (hmeas_g (clamp s))
  have hW_dom : ∀ s, ∀ ω, ‖W s ω‖ ≤ dom ω := by
    intro s ω; simp only [hW_def]; exact hdom (clamp s) (hclamp_mem s) ω
  -- on `[0, T]`, `W` agrees with the unclamped difference, so the integrals agree
  have hQW_eq : ∀ s ∈ Set.Icc (0 : ℝ) T,
      (∫ ω, ‖W s ω‖ ∂π) = ∫ ω, ‖X_f s ω - X_g s ω‖ ∂π := by
    intro s hs
    apply integral_congr_ae
    filter_upwards with ω
    simp only [hW_def, hclamp_id s hs]
  -- per-`ω` mild bound (unclamped) via `flow_difference_mild_bound`
  have hper_w : ∀ ω, ∀ t ∈ Set.Icc (0 : ℝ) T,
      ‖X_f t ω - X_g t ω‖ ≤ ‖X_f 0 ω - X_g 0 ω‖ +
        ∫ s in (0 : ℝ)..t, ((L:ℝ) * ‖X_f s ω - X_g s ω‖ + ε s) := fun ω =>
    flow_difference_mild_bound b_f b_g L hL_f (fun s => X_f s ω) (fun s => X_g s ω) T
      (hcont_f ω) (hcont_g ω) (hderiv_f ω) (hderiv_g ω) (hint ω) ε hε_int (h_diff ω)
  -- transfer the mild bound to the clamped flow `W` (needed by `integral_mild_bound`)
  have hper_W : ∀ ω, ∀ t ∈ Set.Icc (0 : ℝ) T,
      ‖W t ω‖ ≤ ‖W 0 ω‖ + ∫ s in (0 : ℝ)..t, ((L:ℝ) * ‖W s ω‖ + ε s) := by
    intro ω t ht
    have h0t : (0 : ℝ) ≤ t := ht.1
    have hWt : W t ω = X_f t ω - X_g t ω := by simp only [hW_def, hclamp_id t ht]
    have hW0 : W 0 ω = X_f 0 ω - X_g 0 ω := by
      simp only [hW_def, hclamp_id 0 ⟨le_refl 0, hT⟩]
    have hintegrand : (∫ s in (0 : ℝ)..t, ((L:ℝ) * ‖W s ω‖ + ε s))
        = ∫ s in (0 : ℝ)..t, ((L:ℝ) * ‖X_f s ω - X_g s ω‖ + ε s) := by
      refine intervalIntegral.integral_congr (fun s hs => ?_)
      rw [Set.uIcc_of_le h0t] at hs
      have hsT : s ∈ Set.Icc (0 : ℝ) T := ⟨hs.1, hs.2.trans ht.2⟩
      simp only [hW_def, hclamp_id s hsT]
    rw [hWt, hW0, hintegrand]; exact hper_w ω t ht
  -- integrate over `π` (Tonelli): `Q t ≤ Q 0 + ∫₀ᵗ (L·Q s + ε s)`
  have hQW := integral_mild_bound π W (L:ℝ) (NNReal.coe_nonneg L) ε T hT
    hW_cont hW_meas dom hdom_int (fun s _ ω => hW_dom s ω) hε_int hε_nn hper_W
  -- `Q` is globally continuous via DCT (clamped flow globally dominated)
  have hQW_cont : Continuous (fun s => ∫ ω, ‖W s ω‖ ∂π) := by
    refine continuous_of_dominated
      (fun s => (hW_meas s).norm.aestronglyMeasurable)
      (fun s => Filter.Eventually.of_forall (fun ω => ?_)) hdom_int
      (Filter.Eventually.of_forall (fun ω => (hW_cont ω).norm))
    rw [Real.norm_of_nonneg (norm_nonneg _)]; exact hW_dom s ω
  -- collapse the integrand to `2 L · Q s` using the self-reference
  have hmild_W : ∀ t ∈ Set.Icc (0 : ℝ) T,
      (∫ ω, ‖W t ω‖ ∂π) ≤ (∫ ω, ‖W 0 ω‖ ∂π)
        + (2 * (L:ℝ)) * ∫ s in (0 : ℝ)..t, (∫ ω, ‖W s ω‖ ∂π) := by
    intro t ht
    have h0t : (0 : ℝ) ≤ t := ht.1
    have hstep := hQW t ht
    have hII_lhs : IntervalIntegrable
        (fun s => (L:ℝ) * (∫ ω, ‖W s ω‖ ∂π) + ε s) MeasureTheory.volume 0 t :=
      ((hQW_cont.intervalIntegrable 0 t).const_mul (L:ℝ)).add
        (hε_int.mono_set (by
          rw [Set.uIcc_of_le h0t, Set.uIcc_of_le hT]
          exact Set.Icc_subset_Icc_right ht.2))
    have hII_rhs : IntervalIntegrable
        (fun s => (2 * (L:ℝ)) * (∫ ω, ‖W s ω‖ ∂π)) MeasureTheory.volume 0 t :=
      (hQW_cont.intervalIntegrable 0 t).const_mul (2 * (L:ℝ))
    have hmono : (∫ s in (0 : ℝ)..t, ((L:ℝ) * (∫ ω, ‖W s ω‖ ∂π) + ε s))
        ≤ ∫ s in (0 : ℝ)..t, (2 * (L:ℝ)) * (∫ ω, ‖W s ω‖ ∂π) := by
      refine intervalIntegral.integral_mono_on h0t hII_lhs hII_rhs (fun s hs => ?_)
      have hsT : s ∈ Set.Icc (0 : ℝ) T := ⟨hs.1, hs.2.trans ht.2⟩
      have hεle : ε s ≤ (L:ℝ) * (∫ ω, ‖W s ω‖ ∂π) := by
        calc ε s ≤ (L:ℝ) * (∫ ω, ‖X_f s ω - X_g s ω‖ ∂π) := h_self s hsT
          _ = (L:ℝ) * (∫ ω, ‖W s ω‖ ∂π) := by rw [hQW_eq s hsT]
      have hring : (2 * (L:ℝ)) * (∫ ω, ‖W s ω‖ ∂π)
          = (L:ℝ) * (∫ ω, ‖W s ω‖ ∂π) + (L:ℝ) * (∫ ω, ‖W s ω‖ ∂π) := by ring
      rw [hring]; linarith [hεle]
    calc (∫ ω, ‖W t ω‖ ∂π)
        ≤ (∫ ω, ‖W 0 ω‖ ∂π)
          + ∫ s in (0 : ℝ)..t, ((L:ℝ) * (∫ ω, ‖W s ω‖ ∂π) + ε s) := hstep
      _ ≤ (∫ ω, ‖W 0 ω‖ ∂π)
          + ∫ s in (0 : ℝ)..t, (2 * (L:ℝ)) * (∫ ω, ‖W s ω‖ ∂π) := by linarith [hmono]
      _ = (∫ ω, ‖W 0 ω‖ ∂π)
          + (2 * (L:ℝ)) * ∫ s in (0 : ℝ)..t, (∫ ω, ‖W s ω‖ ∂π) := by
            rw [intervalIntegral.integral_const_mul]
  -- scalar mild Gronwall on `Q`
  have hgron := gronwall_mild_le (fun s => ∫ ω, ‖W s ω‖ ∂π)
    (∫ ω, ‖W 0 ω‖ ∂π) (2 * (L:ℝ)) T
    (by have := NNReal.coe_nonneg L; linarith)
    (integral_nonneg (fun ω => norm_nonneg _))
    hQW_cont (fun s => integral_nonneg (fun ω => norm_nonneg _)) hmild_W
  -- transfer back to the unclamped difference on `[0, T]`
  intro t ht
  rw [← hQW_eq t ht, ← hQW_eq 0 ⟨le_refl 0, hT⟩]
  exact hgron t ht

/-- **`IsCharacteristicFlowOn`-flavored variant of `flow_distance_growth_bound`**.

Same Gronwall growth bound, but for a flow specified by **boundary regularity
hypotheses** (`h_init`, `h_cont_Icc`, `h_deriv_Ico`) instead of the universal-in-`t`
ODE of `IsCharacteristicFlow`.  This matches what
`exists_vlasov_characteristicFlow_global_smallT` produces (modulo deriving the
boundary regularity from `IsCharacteristicFlowOn`'s `Ioo 0 T` ODE clauses), and
mirrors the hypothesis-passing pattern of `charFlow_measurable_via_gronwall`.

**Used by**: `Phi_step` to derive the per-`z` growth bound
(`PhiAsVlasovMeasureCurve`'s `h_growth` hypothesis); window uniqueness is a
natural secondary consumer.

**Proof body**: identical to `flow_distance_growth_bound`'s except the three
`hflow`-derived facts (`h_f_cont`, `h_deriv`, `h_init_norm`) are now taken
directly from the boundary regularity hypotheses.  Same Gronwall step, same
final algebra.

**Metric-dependence note**:
This bound uses the unbounded position difference `‖X^M(t,z) - X^{M'}(t,z)‖`,
which forces Gronwall and produces exponential-in-`T` constants
`C_T ≈ exp((1+L)·T)`.  The `Wbar = W_{min(|x-y|,1)}` analog (Dobrushin 1979, §5)
uses the bounded-and-Lipschitz absorption
  `|B_μ(x) - B_{μ'}(x)| ≤ max(2‖B‖_∞, C_B) · min(|x₁-x₂|, 1)`
and produces *linear-in-`T`* constants (Dobrushin 1979, eq. 5.7), changing this
output shape from `C_T · (‖z‖ + 1)` to a bounded analog. -/
theorem flow_distance_growth_bound_on
    {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d))
    [∀ t, IsProbabilityMeasure (ρ t)]
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (T : ℝ) (hT : 0 ≤ T)
    -- Boundary regularity, replacing IsCharacteristicFlow's universal ODE.
    (h_init : ∀ z : PhaseSpace d, (charX 0 z, charV 0 z) = z)
    (h_cont_Icc : ∀ z : PhaseSpace d,
        ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc (0 : ℝ) T))
    (h_deriv_Ico : ∀ z : PhaseSpace d, ∀ s ∈ Set.Ico (0 : ℝ) T,
        HasDerivWithinAt (fun s' => (charX s' z, charV s' z))
          (vlasovVectorField gradW ρ s (charX s z, charV s z))
          (Set.Ici s) s)
    -- ρ regularity, identical to flow_distance_growth_bound's hypotheses.
    (M_ρ : ℝ) (hM_ρ_nn : 0 ≤ M_ρ)
    (hM_ρ : ∀ t ∈ Set.Icc 0 T, ∫ y, ‖y‖ ∂(ρ t) ≤ M_ρ)
    (h_y_int : ∀ t ∈ Set.Icc 0 T, Integrable (fun y : PhysSpace d => ‖y‖) (ρ t))
    (h_int : ∀ t (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ t)) :
    ∃ C_T, 0 ≤ C_T ∧
      ∀ t ∈ Set.Icc 0 T, ∀ z : PhaseSpace d,
        ‖(charX t z, charV t z)‖ ≤ C_T * (‖z‖ + 1) := by
  -- Gronwall parameters: K = 1 + L, ε₀ = ‖gradW 0‖ + L * M_ρ.  Identical to
  -- `flow_distance_growth_bound`.
  set K := 1 + (L : ℝ) with hK_def
  set ε₀ := ‖gradW 0‖ + (L : ℝ) * M_ρ with hε₀_def
  have hK_pos : 0 < K := by positivity
  have hε₀_nn : 0 ≤ ε₀ := by positivity
  -- Witness: C_T = gronwallBound 1 K ε₀ T.
  use gronwallBound 1 K ε₀ T
  refine ⟨?_, ?_⟩
  · have hmono := gronwallBound_mono (by norm_num : (0 : ℝ) ≤ 1) hε₀_nn hK_pos.le hT
    linarith [gronwallBound_x0 1 K ε₀]
  · intro t ht z
    -- Convolution bound: ‖(∇W ∗ ρ_t)(x)‖ ≤ ε₀ + L * ‖x‖.  Identical derivation.
    have h_conv_bound : ∀ s ∈ Set.Icc 0 T, ∀ x : PhysSpace d,
        ‖convolveFunctionMeasure gradW (ρ s) x‖ ≤ ε₀ + (L : ℝ) * ‖x‖ := by
      intro s hs x
      unfold convolveFunctionMeasure
      have h_sub_int : Integrable (fun y => ‖x - y‖) (ρ s) :=
        Integrable.mono' ((integrable_const ‖x‖).add (h_y_int s hs))
          ((aestronglyMeasurable_const (b := x)).sub aestronglyMeasurable_id |>.norm)
          (Filter.Eventually.of_forall fun y => by
            simp only [Real.norm_of_nonneg (norm_nonneg _)]
            exact norm_sub_le x y)
      have h_bnd_int : Integrable (fun y => ‖gradW 0‖ + (L : ℝ) * ‖x - y‖) (ρ s) :=
        (integrable_const _).add (h_sub_int.const_mul _)
      have h_pt : ∀ y : PhysSpace d,
          ‖gradW (x - y)‖ ≤ ‖gradW 0‖ + (L : ℝ) * ‖x - y‖ := by
        intro y
        have hd := hL.dist_le_mul (x - y) 0
        simp only [dist_eq_norm, sub_zero] at hd
        have h_tri : ‖gradW (x - y)‖ ≤ ‖gradW 0‖ + ‖gradW (x - y) - gradW 0‖ := by
          have := norm_add_le (gradW (x - y) - gradW 0) (gradW 0)
          simp only [sub_add_cancel] at this
          linarith
        linarith
      calc ‖∫ y, gradW (x - y) ∂(ρ s)‖
          ≤ ∫ y, ‖gradW (x - y)‖ ∂(ρ s) := norm_integral_le_integral_norm _
        _ ≤ ∫ y, (‖gradW 0‖ + (L : ℝ) * ‖x - y‖) ∂(ρ s) :=
            integral_mono (h_int s x).norm h_bnd_int h_pt
        _ = ‖gradW 0‖ + (L : ℝ) * ∫ y, ‖x - y‖ ∂(ρ s) := by
            rw [integral_add (integrable_const _) (h_sub_int.const_mul _)]
            simp [integral_const, measureReal_def, measure_univ, integral_const_mul]
        _ ≤ ‖gradW 0‖ + (L : ℝ) * (‖x‖ + M_ρ) := by
            have hint_bd : ∫ y, ‖x - y‖ ∂(ρ s) ≤ ‖x‖ + M_ρ := by
              calc ∫ y, ‖x - y‖ ∂(ρ s)
                  ≤ ∫ y, (‖x‖ + ‖y‖) ∂(ρ s) :=
                    integral_mono h_sub_int
                      ((integrable_const _).add (h_y_int s hs))
                      (fun y => norm_sub_le x y)
                _ = ‖x‖ + ∫ y, ‖y‖ ∂(ρ s) := by
                    rw [integral_add (integrable_const _) (h_y_int s hs)]
                    simp [integral_const, measureReal_def, measure_univ]
                _ ≤ ‖x‖ + M_ρ := by linarith [hM_ρ s hs]
            have := mul_le_mul_of_nonneg_left hint_bd L.coe_nonneg
            linarith
        _ = ε₀ + (L : ℝ) * ‖x‖ := by
            simp only [hε₀_def]; ring
    -- Gronwall step.  Boundary regularity comes from hypotheses, not from
    -- IsCharacteristicFlow.
    have h_f_cont : ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc 0 T) :=
      h_cont_Icc z
    have h_deriv : ∀ s ∈ Set.Ico 0 T,
        HasDerivWithinAt (fun s => (charX s z, charV s z))
          (charV s z, -convolveFunctionMeasure gradW (ρ s) (charX s z))
          (Set.Ici s) s := by
      intro s hs
      have hderiv := h_deriv_Ico z s hs
      -- vlasovVectorField gradW ρ s (charX s z, charV s z) = (charV s z, -conv ...)
      unfold vlasovVectorField at hderiv
      exact hderiv
    have h_init_norm : ‖(charX 0 z, charV 0 z)‖ ≤ ‖z‖ := by
      rw [h_init z]
    have h_bound : ∀ s ∈ Set.Ico 0 T,
        ‖(charV s z, -convolveFunctionMeasure gradW (ρ s) (charX s z))‖ ≤
          K * ‖(charX s z, charV s z)‖ + ε₀ := by
      intro s hs
      have hs_mem : s ∈ Set.Icc 0 T := ⟨hs.1, le_of_lt hs.2⟩
      simp only [Prod.norm_def, norm_neg]
      have hFsz := le_max_left ‖charX s z‖ ‖charV s z‖
      have hGsz := le_max_right ‖charX s z‖ ‖charV s z‖
      have hM_nn : 0 ≤ max ‖charX s z‖ ‖charV s z‖ :=
        le_max_iff.mpr (Or.inl (norm_nonneg _))
      have h_v_le : ‖charV s z‖ ≤ K * max ‖charX s z‖ ‖charV s z‖ + ε₀ :=
        calc ‖charV s z‖ ≤ max ‖charX s z‖ ‖charV s z‖ := hGsz
          _ ≤ K * max ‖charX s z‖ ‖charV s z‖ :=
              le_mul_of_one_le_left hM_nn (by linarith [NNReal.coe_nonneg L])
          _ ≤ K * max ‖charX s z‖ ‖charV s z‖ + ε₀ := le_add_of_nonneg_right hε₀_nn
      have h_conv_le : ‖convolveFunctionMeasure gradW (ρ s) (charX s z)‖ ≤
          K * max ‖charX s z‖ ‖charV s z‖ + ε₀ :=
        calc ‖convolveFunctionMeasure gradW (ρ s) (charX s z)‖
            ≤ ε₀ + (L : ℝ) * ‖charX s z‖ := h_conv_bound s hs_mem _
          _ ≤ ε₀ + K * max ‖charX s z‖ ‖charV s z‖ := by
              have hLK : (L : ℝ) ≤ K := le_add_of_nonneg_left zero_le_one
              linarith [mul_le_mul_of_nonneg_left hFsz (NNReal.coe_nonneg L),
                        mul_le_mul_of_nonneg_right hLK hM_nn]
          _ = K * max ‖charX s z‖ ‖charV s z‖ + ε₀ := by ring
      exact max_le h_v_le h_conv_le
    have h_grw := norm_le_gronwallBound_of_norm_deriv_right_le
      h_f_cont h_deriv h_init_norm h_bound t ht
    simp only [sub_zero] at h_grw
    calc ‖(charX t z, charV t z)‖
        ≤ gronwallBound ‖z‖ K ε₀ t := h_grw
      _ ≤ gronwallBound ‖z‖ K ε₀ T :=
          gronwallBound_mono (norm_nonneg _) hε₀_nn hK_pos.le ht.2
      _ ≤ gronwallBound 1 K ε₀ T * (‖z‖ + 1) := by
          rw [gronwallBound_of_K_ne_0 hK_pos.ne', gronwallBound_of_K_ne_0 hK_pos.ne']
          simp only [one_mul]
          have he1 : 0 ≤ Real.exp (K * T) - 1 :=
            by linarith [Real.one_le_exp (mul_nonneg hK_pos.le hT)]
          have hεK := div_nonneg hε₀_nn hK_pos.le
          nlinarith [norm_nonneg z, Real.exp_nonneg (K * T),
            mul_nonneg hεK he1, mul_nonneg (norm_nonneg z) (mul_nonneg hεK he1)]

/-- **Piece A (Option 2): time-dependent moment-envelope growth bound.**

Sharper sibling of `flow_distance_growth_bound_on`.  Instead of a single
constant moment bound `M_ρ` (which forces the constant-sup growth constant
`C_T` and, downstream, an `M_f₀`-dependent fixed-point on the curve space),
this takes a **monotone time-dependent envelope** `m : ℝ → ℝ` bounding the
spatial-marginal first moment, and concludes the **time-local** Gronwall bound

  `‖(charX t z, charV t z)‖ ≤ gronwallBound ‖z‖ (1+L) (‖gradW 0‖ + L · m t) t`,

with the force constant `ε(t) = ‖gradW 0‖ + L · m t` evaluated at the SAME time
`t` (not the sup `m T`).  Monotonicity of `m` lets the per-`t` Gronwall on
`[0, t]` use the endpoint value `ε(t)` while validating the derivative bound at
every `s ≤ t` (since `ε(s) ≤ ε(t)`).

**Why this is the option-2 foundation**: integrating the conclusion over a
probability `f₀` gives `M_{Φρ}(t) ≤ A(t) + B(t)·m(t)` with
`A(t) = M_f₀·e^{(1+L)t} + (‖gradW 0‖/(1+L))(e^{(1+L)t}-1)` and
`B(t) = (L/(1+L))(e^{(1+L)t}-1)` — crucially an **`M_f₀`-free** coefficient.
The canonical envelope `m*(t) := A(t)/(1-B(T))` is then Φ-invariant under the
**data-independent** constraint `B(T) < 1`, dissolving the constant-`M`
fixed-point without a data-dependent hypothesis.  (Contrast the constant-sup
bound, which feeds `m(T)` into `ε` and re-derives an `M_f₀`-dependent
smallness.) -/
theorem flow_distance_growth_bound_on_timedep
    {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d))
    [∀ t, IsProbabilityMeasure (ρ t)]
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (T : ℝ) (_hT : 0 ≤ T)
    (h_init : ∀ z : PhaseSpace d, (charX 0 z, charV 0 z) = z)
    (h_cont_Icc : ∀ z : PhaseSpace d,
        ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc (0 : ℝ) T))
    (h_deriv_Ico : ∀ z : PhaseSpace d, ∀ s ∈ Set.Ico (0 : ℝ) T,
        HasDerivWithinAt (fun s' => (charX s' z, charV s' z))
          (vlasovVectorField gradW ρ s (charX s z, charV s z))
          (Set.Ici s) s)
    (m : ℝ → ℝ) (hm_mono : MonotoneOn m (Set.Icc 0 T))
    (hm : ∀ t ∈ Set.Icc 0 T, ∫ y, ‖y‖ ∂(ρ t) ≤ m t)
    (h_y_int : ∀ t ∈ Set.Icc 0 T, Integrable (fun y : PhysSpace d => ‖y‖) (ρ t))
    (h_int : ∀ t (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ t)) :
    ∀ t ∈ Set.Icc 0 T, ∀ z : PhaseSpace d,
      ‖(charX t z, charV t z)‖ ≤
        gronwallBound ‖z‖ (1 + (L : ℝ)) (‖gradW 0‖ + (L : ℝ) * m t) t := by
  intro t ht z
  set K : ℝ := 1 + (L : ℝ) with hK_def
  -- m t ≥ 0 (moment of a probability measure is nonneg, bounded by m t).
  have hmt_nn : 0 ≤ m t :=
    le_trans (integral_nonneg (fun y => norm_nonneg y)) (hm t ht)
  set εt : ℝ := ‖gradW 0‖ + (L : ℝ) * m t with hεt_def
  have hK_pos : 0 < K := by positivity
  have hεt_nn : 0 ≤ εt := by positivity
  -- Convolution force bound on [0, t], using m s ≤ m t (monotone).
  have h_conv_bound : ∀ s ∈ Set.Icc 0 t, ∀ x : PhysSpace d,
      ‖convolveFunctionMeasure gradW (ρ s) x‖ ≤ εt + (L : ℝ) * ‖x‖ := by
    intro s hs x
    have hs_T : s ∈ Set.Icc 0 T := ⟨hs.1, le_trans hs.2 ht.2⟩
    have hms_le_mt : m s ≤ m t := hm_mono hs_T ht hs.2
    unfold convolveFunctionMeasure
    have h_sub_int : Integrable (fun y => ‖x - y‖) (ρ s) :=
      Integrable.mono' ((integrable_const ‖x‖).add (h_y_int s hs_T))
        ((aestronglyMeasurable_const (b := x)).sub aestronglyMeasurable_id |>.norm)
        (Filter.Eventually.of_forall fun y => by
          simp only [Real.norm_of_nonneg (norm_nonneg _)]; exact norm_sub_le x y)
    have h_bnd_int : Integrable (fun y => ‖gradW 0‖ + (L : ℝ) * ‖x - y‖) (ρ s) :=
      (integrable_const _).add (h_sub_int.const_mul _)
    have h_pt : ∀ y : PhysSpace d,
        ‖gradW (x - y)‖ ≤ ‖gradW 0‖ + (L : ℝ) * ‖x - y‖ := by
      intro y
      have hd := hL.dist_le_mul (x - y) 0
      simp only [dist_eq_norm, sub_zero] at hd
      have h_tri : ‖gradW (x - y)‖ ≤ ‖gradW 0‖ + ‖gradW (x - y) - gradW 0‖ := by
        have := norm_add_le (gradW (x - y) - gradW 0) (gradW 0)
        simp only [sub_add_cancel] at this; linarith
      linarith
    calc ‖∫ y, gradW (x - y) ∂(ρ s)‖
        ≤ ∫ y, ‖gradW (x - y)‖ ∂(ρ s) := norm_integral_le_integral_norm _
      _ ≤ ∫ y, (‖gradW 0‖ + (L : ℝ) * ‖x - y‖) ∂(ρ s) :=
          integral_mono (h_int s x).norm h_bnd_int h_pt
      _ = ‖gradW 0‖ + (L : ℝ) * ∫ y, ‖x - y‖ ∂(ρ s) := by
          rw [integral_add (integrable_const _) (h_sub_int.const_mul _)]
          simp [integral_const, measureReal_def, measure_univ, integral_const_mul]
      _ ≤ εt + (L : ℝ) * ‖x‖ := by
          have h_int_le : ∫ y, ‖x - y‖ ∂(ρ s) ≤ ‖x‖ + m t := by
            calc ∫ y, ‖x - y‖ ∂(ρ s)
                ≤ ∫ y, (‖x‖ + ‖y‖) ∂(ρ s) :=
                  integral_mono h_sub_int ((integrable_const _).add (h_y_int s hs_T))
                    (fun y => norm_sub_le x y)
              _ = ‖x‖ + ∫ y, ‖y‖ ∂(ρ s) := by
                  rw [integral_add (integrable_const _) (h_y_int s hs_T)]
                  simp [integral_const, measureReal_def, measure_univ]
              _ ≤ ‖x‖ + m t := by linarith [hm s hs_T, hms_le_mt]
          simp only [hεt_def]
          nlinarith [mul_le_mul_of_nonneg_left h_int_le (NNReal.coe_nonneg L)]
  -- Gronwall on [0, t] with the endpoint force constant εt.
  have ht0 : (0 : ℝ) ≤ t := ht.1
  have h_f_cont : ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc 0 t) :=
    (h_cont_Icc z).mono (Set.Icc_subset_Icc_right ht.2)
  have h_deriv : ∀ s ∈ Set.Ico 0 t,
      HasDerivWithinAt (fun s => (charX s z, charV s z))
        (charV s z, -convolveFunctionMeasure gradW (ρ s) (charX s z))
        (Set.Ici s) s := by
    intro s hs
    have hs_T : s ∈ Set.Ico 0 T := ⟨hs.1, lt_of_lt_of_le hs.2 ht.2⟩
    have hderiv := h_deriv_Ico z s hs_T
    unfold vlasovVectorField at hderiv
    exact hderiv
  have h_init_norm : ‖(charX 0 z, charV 0 z)‖ ≤ ‖z‖ := by rw [h_init z]
  have h_bound : ∀ s ∈ Set.Ico 0 t,
      ‖(charV s z, -convolveFunctionMeasure gradW (ρ s) (charX s z))‖ ≤
        K * ‖(charX s z, charV s z)‖ + εt := by
    intro s hs
    have hs_mem : s ∈ Set.Icc 0 t := ⟨hs.1, le_of_lt hs.2⟩
    simp only [Prod.norm_def, norm_neg]
    have hFsz := le_max_left ‖charX s z‖ ‖charV s z‖
    have hGsz := le_max_right ‖charX s z‖ ‖charV s z‖
    have hM_nn : 0 ≤ max ‖charX s z‖ ‖charV s z‖ :=
      le_max_iff.mpr (Or.inl (norm_nonneg _))
    have h_v_le : ‖charV s z‖ ≤ K * max ‖charX s z‖ ‖charV s z‖ + εt :=
      calc ‖charV s z‖ ≤ max ‖charX s z‖ ‖charV s z‖ := hGsz
        _ ≤ K * max ‖charX s z‖ ‖charV s z‖ :=
            le_mul_of_one_le_left hM_nn (by linarith [NNReal.coe_nonneg L])
        _ ≤ K * max ‖charX s z‖ ‖charV s z‖ + εt := le_add_of_nonneg_right hεt_nn
    have h_conv_le : ‖convolveFunctionMeasure gradW (ρ s) (charX s z)‖ ≤
        K * max ‖charX s z‖ ‖charV s z‖ + εt :=
      calc ‖convolveFunctionMeasure gradW (ρ s) (charX s z)‖
          ≤ εt + (L : ℝ) * ‖charX s z‖ := h_conv_bound s hs_mem _
        _ ≤ εt + K * max ‖charX s z‖ ‖charV s z‖ := by
            have hLK : (L : ℝ) ≤ K := le_add_of_nonneg_left zero_le_one
            linarith [mul_le_mul_of_nonneg_left hFsz (NNReal.coe_nonneg L),
                      mul_le_mul_of_nonneg_right hLK hM_nn]
        _ = K * max ‖charX s z‖ ‖charV s z‖ + εt := by ring
    exact max_le h_v_le h_conv_le
  have h_grw := norm_le_gronwallBound_of_norm_deriv_right_le
    h_f_cont h_deriv h_init_norm h_bound t (Set.right_mem_Icc.mpr ht0)
  simpa using h_grw

/-- **Piece A.3 (Option 2): the canonical moment envelope closes (data-free).**

Pure-algebra companion to `flow_distance_growth_bound_on_timedep`.  Under the
**`M_f₀`-free** smallness `B(T) := (L/(1+L))(e^{(1+L)T}-1) < 1`, the explicit
envelope `m*(t) := gronwallBound M_f₀ (1+L) g0 t / (1 - B(T))` is a Gronwall
super-solution:

* monotone on `[0, T]`,
* dominates the initial moment `M_f₀`,
* **Φ-invariant** at the moment level:
  `gronwallBound M_f₀ (1+L) (g0 + L·m* t) t ≤ m* t`.

Composed with Piece A integrated over `f₀` (which gives
`M_{Φρ}(t) ≤ gronwallBound M_f₀ (1+L) (g0 + L·m(t)) t`, `g0 = ‖gradW 0‖`), this
shows the Picard iterates stay inside the fixed envelope `m*` with **no**
data-dependent hypothesis — the faithful dissolution of the constant-`M`
fixed-point.  This lemma is the measure-free heart of the option-2 escape;
Pieces B–D thread it through the curve space, `Phi_step`, and #11. -/
theorem gronwall_envelope_exists
    (M_f₀ g0 : ℝ) (hM_f₀ : 0 ≤ M_f₀) (hg0 : 0 ≤ g0)
    (L : NNReal) (T : ℝ) (hT : 0 ≤ T)
    (hB : (L : ℝ) / (1 + (L : ℝ)) * (Real.exp ((1 + (L : ℝ)) * T) - 1) < 1) :
    ∃ m : ℝ → ℝ, MonotoneOn m (Set.Icc 0 T) ∧
      (∀ t ∈ Set.Icc 0 T, M_f₀ ≤ m t) ∧
      (∀ t ∈ Set.Icc 0 T,
        gronwallBound M_f₀ (1 + (L : ℝ)) (g0 + (L : ℝ) * m t) t ≤ m t) := by
  set K : ℝ := 1 + (L : ℝ) with hK_def
  have hK_pos : 0 < K := by positivity
  have hK_ne : K ≠ 0 := ne_of_gt hK_pos
  have hL_nn : (0 : ℝ) ≤ (L : ℝ) := L.coe_nonneg
  -- B(t) and its monotonicity.
  set Bf : ℝ → ℝ := fun t => (L : ℝ) / K * (Real.exp (K * t) - 1) with hBf_def
  have hBT_lt : Bf T < 1 := hB
  have hD_pos : 0 < 1 - Bf T := by linarith
  have hD_nn : (0 : ℝ) ≤ 1 - Bf T := hD_pos.le
  have hD_ne : (1 - Bf T) ≠ 0 := ne_of_gt hD_pos
  have hLK_nn : 0 ≤ (L : ℝ) / K := div_nonneg hL_nn hK_pos.le
  have hBf_T_nn : 0 ≤ Bf T := by
    have he1 : 0 ≤ Real.exp (K * T) - 1 := by
      have : (1 : ℝ) ≤ Real.exp (K * T) := Real.one_le_exp (by positivity)
      linarith
    exact mul_nonneg hLK_nn he1
  have hBf_le : ∀ t ∈ Set.Icc (0 : ℝ) T, Bf t ≤ Bf T := by
    intro t ht
    have hexp : Real.exp (K * t) ≤ Real.exp (K * T) :=
      Real.exp_le_exp.mpr (by nlinarith [ht.2, hK_pos.le])
    simp only [hBf_def]
    nlinarith [hexp, hLK_nn]
  -- A(t) := gronwallBound M_f₀ K g0 t, expanded + nonneg + monotone.
  set Af : ℝ → ℝ := fun t => gronwallBound M_f₀ K g0 t with hAf_def
  have hAf_expand : ∀ t,
      Af t = M_f₀ * Real.exp (K * t) + g0 / K * (Real.exp (K * t) - 1) := by
    intro t; simp only [hAf_def]; rw [gronwallBound_of_K_ne_0 hK_ne]
  have hAf_nn : ∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ Af t := by
    intro t ht
    rw [hAf_expand t]
    have he1 : 0 ≤ Real.exp (K * t) - 1 := by
      have : (1 : ℝ) ≤ Real.exp (K * t) := Real.one_le_exp (by nlinarith [ht.1, hK_pos.le])
      linarith
    have hgK_nn : 0 ≤ g0 / K := div_nonneg hg0 hK_pos.le
    positivity
  have hAf_mono : MonotoneOn Af (Set.Icc 0 T) := by
    intro s _ t _ hst
    simp only [hAf_def]
    exact gronwallBound_mono hM_f₀ hg0 hK_pos.le hst
  refine ⟨fun t => Af t / (1 - Bf T), ?_, ?_, ?_⟩
  · -- monotone: Af increasing, positive constant divisor.
    intro s hs t ht hst
    change Af s / (1 - Bf T) ≤ Af t / (1 - Bf T)
    gcongr
    exact hAf_mono hs ht hst
  · -- M_f₀ ≤ m t.
    intro t ht
    have h0_mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_refl 0, hT⟩
    have hAf0 : Af 0 = M_f₀ := by rw [hAf_expand 0]; simp [Real.exp_zero]
    have h_mono : Af 0 / (1 - Bf T) ≤ Af t / (1 - Bf T) := by
      gcongr
      exact hAf_mono h0_mem ht ht.1
    rw [hAf0] at h_mono
    have h_self : M_f₀ ≤ M_f₀ / (1 - Bf T) := by
      rw [le_div_iff₀ hD_pos]; nlinarith [hM_f₀, hBf_T_nn]
    linarith
  · -- Φ-invariance.
    intro t ht
    change gronwallBound M_f₀ K (g0 + (L : ℝ) * (Af t / (1 - Bf T))) t
        ≤ Af t / (1 - Bf T)
    have h_lhs : gronwallBound M_f₀ K (g0 + (L : ℝ) * (Af t / (1 - Bf T))) t
              = Af t + Bf t * (Af t / (1 - Bf T)) := by
      rw [gronwallBound_of_K_ne_0 hK_ne, hAf_expand t]
      simp only [hBf_def]; ring
    rw [h_lhs]
    have hkey : 0 ≤ Af t * (Bf T - Bf t) :=
      mul_nonneg (hAf_nn t ht) (by linarith [hBf_le t ht])
    have hexpand : Af t / (1 - Bf T) - (Af t + Bf t * (Af t / (1 - Bf T)))
                 = Af t * (Bf T - Bf t) / (1 - Bf T) := by
      field_simp
      ring
    linarith [div_nonneg hkey hD_pos.le, hexpand]

/-- **Piece A.2 (Option 2): integrate the per-`z` growth bound to a moment bound.**

The measure-level bridge between Piece A and Piece A.3: given the per-`z`
time-local growth bound (Piece A's conclusion, taken here as the hypothesis
`h_growth` so this lemma is decoupled from the flow construction), the
**position pushforward** `Measure.map (charX t ·) f₀` has first moment bounded
by the same Gronwall functional evaluated at the *initial* moment `∫‖z‖ ∂f₀`:

  `∫ x, ‖x‖ ∂(Measure.map (charX t ·) f₀) ≤ gronwallBound (∫‖z‖ ∂f₀) (1+L) (g0 + L·m t) t`.

Proof: `integral_map` exchanges the pushforward; `‖charX t z‖ ≤ ‖(charX t z, charV t z)‖`
+ `h_growth` bounds the integrand by `gronwallBound ‖z‖ …`, which is affine in `‖z‖`,
so its `f₀`-integral is `gronwallBound (∫‖z‖) …` (probability measure ⇒ the constant
term integrates to itself).

Composing with `gronwall_envelope_exists` (Piece A.3): when `m = m*` the canonical
envelope and `g0 = ‖gradW 0‖`, the RHS is `≤ m* t`, i.e. `Φ` maps the envelope to
itself at the moment level — the measure-level statement of the data-free escape. -/
theorem phi_moment_envelope_le {d : ℕ}
    (L : NNReal) (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (g0 : ℝ) (T : ℝ) (m : ℝ → ℝ)
    (h_growth : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ z : PhaseSpace d,
      ‖(charX t z, charV t z)‖ ≤ gronwallBound ‖z‖ (1 + (L : ℝ)) (g0 + (L : ℝ) * m t) t)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (hf₀_int : Integrable (fun z : PhaseSpace d => ‖z‖) f₀)
    (h_meas : ∀ t ∈ Set.Icc (0 : ℝ) T,
      AEMeasurable (fun z : PhaseSpace d => charX t z) f₀) :
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∫ x, ‖x‖ ∂(Measure.map (fun z : PhaseSpace d => charX t z) f₀)
        ≤ gronwallBound (∫ z, ‖z‖ ∂f₀) (1 + (L : ℝ)) (g0 + (L : ℝ) * m t) t := by
  intro t ht
  set K : ℝ := 1 + (L : ℝ) with hK_def
  set εt : ℝ := g0 + (L : ℝ) * m t with hεt_def
  have hK_ne : K ≠ 0 := by positivity
  -- gronwallBound is affine in its initial value: gb r = e^{Kt}·r + C.
  have h_gb : ∀ r : ℝ,
      gronwallBound r K εt t = Real.exp (K * t) * r + εt / K * (Real.exp (K * t) - 1) := by
    intro r; rw [gronwallBound_of_K_ne_0 hK_ne]; ring
  have h_dom_int : Integrable (fun z : PhaseSpace d => gronwallBound ‖z‖ K εt t) f₀ := by
    simp only [h_gb]
    exact (hf₀_int.const_mul _).add (integrable_const _)
  have h_charX_le : ∀ z : PhaseSpace d, ‖charX t z‖ ≤ gronwallBound ‖z‖ K εt t := fun z =>
    le_trans (norm_fst_le (charX t z, charV t z)) (h_growth t ht z)
  have h_charX_int : Integrable (fun z : PhaseSpace d => ‖charX t z‖) f₀ :=
    h_dom_int.mono' ((h_meas t ht).norm.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_of_nonneg (norm_nonneg _)]; exact h_charX_le z)
  rw [integral_map (h_meas t ht) continuous_norm.aestronglyMeasurable]
  calc ∫ z, ‖charX t z‖ ∂f₀
      ≤ ∫ z, gronwallBound ‖z‖ K εt t ∂f₀ :=
        integral_mono h_charX_int h_dom_int h_charX_le
    _ = gronwallBound (∫ z, ‖z‖ ∂f₀) K εt t := by
        simp only [h_gb]
        rw [integral_add (hf₀_int.const_mul _) (integrable_const _), integral_const_mul,
            integral_const]
        simp [measureReal_def, measure_univ]

/-! ## Characteristic flow existence (Picard-Lindelöf wrapper)

This section wraps the vendored parametric Picard-Lindelöf theorem
(`LeanPool.Vlasov.ForMathlib.PicardLindelof`) to extract a characteristic flow
`(charX, charV)` for the Vlasov ODE.
The four `IsPicardLindelof` hypotheses (Lipschitz-on-ball,
continuous-in-time, norm bound, contraction) are derived from
`convolveFunctionMeasure_lipschitz_in_x`, plus narrow-continuity of the
spatial-marginal curve `ρ`, plus a uniform norm bound from the
finite-mass assumption.

The contraction condition `L · max(tmax − t₀, t₀ − tmin) ≤ a − r`
pins down the local time-interval size relative to the ball radius.
For the dobrushin application we work on a finite interval `[0, T]`;
the existence theorem is parametrised by `T` and produces a flow
on `Set.Icc 0 T` (extending the local flow by stitching overlapping
windows; technically a separate iteration argument, deferred to
the proof body).

This sub-section first establishes the **global Lipschitz constant**
for `vlasovVectorField` (a direct composition of
`convolveFunctionMeasure_lipschitz_in_x` with the 1-Lipschitz
identity on the velocity coordinate, combined via `LipschitzWith.prodMk`).
The global Lipschitz immediately restricts to any closed ball,
giving the first of the four `IsPicardLindelof` fields.

The full `exists_vlasov_characteristicFlow` proof packages the global
norm bound into a per-window `IsPicardLindelof`, invokes the vendored
Picard-Lindelöf (`exists_vlasov_extend_one_window`), and stitches
`N = ⌈T/δ⌉` windows per-`z` via `HasDerivWithinAt.union` under the
position/velocity inductive invariant.  Downstream callers discharge its
`hR`/`hbound` hypotheses; the single-ball `hR` discharge in
`exists_vlasov_trajectory` is what introduces the
`LocalSmallnessPLBuffer L T := L·T² < 1` constraint — see that
theorem's docstring for the arbitrary-`L` discussion. -/

/-- Localized variant of `IsCharacteristicFlow` from `Basic.lean`:
the same initial condition + position/velocity ODEs, but quantified
over a chosen time set `s_t : Set ℝ` and initial-condition set
`s_z : Set (PhaseSpace d)`.

The global `IsCharacteristicFlow gradW ρ charX charV` is the
specialisation `IsCharacteristicFlowOn ... Set.univ Set.univ`
(modulo the unconditional init clause). -/
def IsCharacteristicFlowOn
    {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (ρ : ℝ → Measure (PhysSpace d))
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (s_t : Set ℝ) (s_z : Set (PhaseSpace d)) : Prop :=
  (∀ z ∈ s_z, charX 0 z = z.1 ∧ charV 0 z = z.2) ∧
  (∀ t ∈ s_t, ∀ z ∈ s_z, HasDerivAt (fun s => charX s z) (charV t z) t) ∧
  (∀ t ∈ s_t, ∀ z ∈ s_z, HasDerivAt (fun s => charV s z)
      (-(convolveFunctionMeasure gradW (ρ t) (charX t z))) t)

/-- Monotonicity of `IsCharacteristicFlowOn` in both the time set and the
initial-condition set.  Used at the end of the global existence theorem
to restrict a flow produced on `Ioo 0 (N·δ)` (covering all of `[0, T]`)
down to `Ioo 0 T`. -/
lemma IsCharacteristicFlowOn.mono
    {d : ℕ}
    {gradW : PhysSpace d → PhysSpace d}
    {ρ : ℝ → Measure (PhysSpace d)}
    {charX charV : ℝ → PhaseSpace d → PhysSpace d}
    {s_t s_t' : Set ℝ} {s_z s_z' : Set (PhaseSpace d)}
    (h : IsCharacteristicFlowOn gradW ρ charX charV s_t s_z)
    (hs_t : s_t' ⊆ s_t) (hs_z : s_z' ⊆ s_z) :
    IsCharacteristicFlowOn gradW ρ charX charV s_t' s_z' := by
  refine ⟨fun z hz => h.1 z (hs_z hz), fun t ht z hz => ?_, fun t ht z hz => ?_⟩
  · exact h.2.1 t (hs_t ht) z (hs_z hz)
  · exact h.2.2 t (hs_t ht) z (hs_z hz)

/-! ### Localized Vlasov-solution predicates on `[0, T]`

The globally-quantified predicates `IsVlasovSolution` and
`IsLagrangianVlasovSolution` (both in `Basic.lean`) require the weak PDE and
the characteristic flow to hold *universally in `t : ℝ`*.  For local existence
(`vlasovWellPosedness_local`), the Picard iteration only produces a solution
on a small time window `[0, T₀]`; the underlying characteristic flow comes
from `exists_vlasov_characteristicFlow_global_smallT`, which exposes
`IsCharacteristicFlowOn ... (Ioo 0 T) Set.univ` — open-interval ODE
behaviour, not the universal-in-`t` form `IsCharacteristicFlow` demands.

The `_On`-localized predicates below mirror the global ones with their
quantification restricted to `[0, T]`.  Local existence produces the
localized predicate; the forward-iteration continuation glues local windows
to recover the universal-in-`t` `IsLagrangianVlasovSolution` required by the
marquee `vlasovWellPosedness` theorem.

The `_On` family lives in this file so it can compose with
`IsCharacteristicFlowOn` (which lives here too); the global versions stay in
`Basic.lean` as the abstract endpoints. -/

/-- Localized weak Vlasov evolution equation on `Ioo 0 T`.  Same as
`WeakEvolutionEq` (`Basic.lean`) but with the derivative claim
restricted to the *open* interval `t ∈ Set.Ioo 0 T`.

**Why `Ioo` not `Icc`**: the characteristic flow only provides
ODE behaviour on `Ioo 0 T` (the boundary derivatives at `t = 0` and
`t = T` are genuinely unavailable from open-interval HasDerivAt alone).
The Vlasov solution's weak PDE inherits the same regularity: it holds on
the open interval where the characteristic flow is differentiable, and
the initial condition at `t = 0` is captured separately by the
pushforward equation in `IsLagrangianVlasovSolutionOn`. -/
def WeakEvolutionEqOn {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (μ : ℝ → Measure (PhaseSpace d))
    (φ : PhaseSpace d → ℝ)
    (gradXφ gradVφ : PhaseSpace d → PhysSpace d)
    (R_N : ℝ → ℝ) (T : ℝ) : Prop :=
  ∀ t ∈ Set.Ioo (0 : ℝ) T,
    HasDerivAt (fun s => ∫ z, φ z ∂μ s)
      (∫ z, (@inner ℝ (PhysSpace d) _ z.2 (gradXφ z) -
              @inner ℝ (PhysSpace d) _
                (convolveFunctionMeasure gradW (spatialMarginal (μ t)) z.1)
                (gradVφ z))
        ∂μ t
        + R_N t) t

/-- Localized Vlasov solution on `[0, T]`.  Mirror of `IsVlasovSolution`
with the weak PDE restricted to `[0, T]` via `WeakEvolutionEqOn`. -/
def IsVlasovSolutionOn {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (f : ℝ → Measure (PhaseSpace d)) (T : ℝ) : Prop :=
  ∀ (φ : PhaseSpace d → ℝ),
    ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
    ∀ (gradXφ gradVφ : PhaseSpace d → PhysSpace d),
      (∀ z, gradXφ z = gradient (fun x => φ (x, z.2)) z.1) →
      (∀ z, gradVφ z = gradient (fun v => φ (z.1, v)) z.2) →
      WeakEvolutionEqOn gradW f φ gradXφ gradVφ (fun _ => 0) T

/-- Localized Lagrangian Vlasov solution on `[0, T]`.  Mirror of
`IsLagrangianVlasovSolution` (`Basic.lean`) with:

* the weak PDE restricted to `[0, T]` (via `IsVlasovSolutionOn`),
* the characteristic flow restricted to `IsCharacteristicFlowOn ... (Ioo 0 T)
  Set.univ` (the natural output shape of the flow construction),
* the initial-condition clause stated explicitly (since `IsCharacteristicFlowOn`'s
  initial-condition clause is over `s_z`, here `Set.univ`, so it gives the
  same content; we restate it for direct usability),
* the pushforward equation restricted to `t ∈ Set.Icc 0 T`,
* the AEMeasurability clause restricted to `s ∈ Set.Icc 0 T`.

Every conjunct is the localized analogue of `IsLagrangianVlasovSolution`'s.
The forward-iteration continuation bridges to the global predicate by gluing
local windows. -/
def IsLagrangianVlasovSolutionOn {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (f : ℝ → Measure (PhaseSpace d)) (T : ℝ) : Prop :=
  IsVlasovSolutionOn gradW f T ∧
  ∃ charX charV : ℝ → PhaseSpace d → PhysSpace d,
    IsCharacteristicFlowOn gradW (fun t => spatialMarginal (f t)) charX charV
      (Set.Ioo 0 T) Set.univ ∧
    (∀ t ∈ Set.Icc (0 : ℝ) T,
      f t = Measure.map (fun z : PhaseSpace d => (charX t z, charV t z)) (f 0)) ∧
    (∀ s ∈ Set.Icc (0 : ℝ) T,
      AEMeasurable (fun z : PhaseSpace d => (charX s z, charV s z)) (f 0)) ∧
    -- **Boundary regularity**: the flow is continuous up to the *closed*
    -- window `[0, T]`.  This is the weakest-sufficient boundary fact for
    -- closed-window W₁-continuity soundness — closed-window W₁-continuity <==
    -- closed-window narrow continuity of `f` <== `ContinuousOn` of the flow
    -- (pushforward + DCT).  Exposed because the `Ioo`-only flow conjunct
    -- above leaves the endpoints `t ∈ {0,T}` unconstrained; producers supply
    -- this from data already in hand.
    (∀ z : PhaseSpace d,
      ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc (0 : ℝ) T))

/-- A global `IsVlasovSolution` restricts to `IsVlasovSolutionOn T` for any
`T : ℝ`.  Projects the universal HasDerivAt claim onto `Ioo 0 T` by direct
specialization (the restricted set is open, so HasDerivAt and
HasDerivWithinAt coincide there). -/
lemma IsVlasovSolution.toOn {d : ℕ}
    {gradW : PhysSpace d → PhysSpace d}
    {f : ℝ → Measure (PhaseSpace d)} (h : IsVlasovSolution gradW f) (T : ℝ) :
    IsVlasovSolutionOn gradW f T := by
  intro φ hφ_smooth hφ_compact gradXφ gradVφ hgradXφ hgradVφ t _ht
  exact h φ hφ_smooth hφ_compact gradXφ gradVφ hgradXφ hgradVφ t

/-- A global `IsLagrangianVlasovSolution` restricts to
`IsLagrangianVlasovSolutionOn T` for any `T : ℝ`.

The flow witness restricts via `IsCharacteristicFlowOn`'s natural relationship
to the universal `IsCharacteristicFlow` (open Ioo ⊆ ℝ).  The pushforward and
AEMeasurability conjuncts restrict trivially since the originals are
universal. -/
lemma IsLagrangianVlasovSolution.toOn {d : ℕ}
    {gradW : PhysSpace d → PhysSpace d}
    {f : ℝ → Measure (PhaseSpace d)}
    (h : IsLagrangianVlasovSolution gradW f) (T : ℝ) :
    IsLagrangianVlasovSolutionOn gradW f T := by
  obtain ⟨h_sol, charX, charV, h_flow, h_push, h_meas⟩ := h
  refine ⟨h_sol.toOn T, charX, charV, ?_, ?_, ?_, ?_⟩
  · -- IsCharacteristicFlowOn from IsCharacteristicFlow.
    exact ⟨fun z _ => h_flow.1 z,
           fun t _ z _ => h_flow.2.1 t z,
           fun t _ z _ => h_flow.2.2 t z⟩
  · intro t _; exact h_push t
  · intro s _; exact h_meas s
  · -- Boundary ContinuousOn from universal HasDerivAt → continuity everywhere.
    intro z
    have hX : Continuous (fun s => charX s z) :=
      continuous_iff_continuousAt.mpr (fun t => (h_flow.2.1 t z).continuousAt)
    have hV : Continuous (fun s => charV s z) :=
      continuous_iff_continuousAt.mpr (fun t => (h_flow.2.2 t z).continuousAt)
    exact (hX.prodMk hV).continuousOn

/-- Global Lipschitz constant for the Vlasov phase-space vector field.
`b_t(x, v) = (v, -(∇W ∗ ρ_t)(x))` is `max(1, L)`-Lipschitz when
`gradW` is `L`-Lipschitz: the velocity-side projection `(x, v) ↦ v`
is 1-Lipschitz (`LipschitzWith.prod_snd`), and the force-side map
`(x, v) ↦ -(∇W ∗ ρ_t)(x)` is `L`-Lipschitz (compose
`convolveFunctionMeasure_lipschitz_in_x` with `Neg.neg` and
`Prod.fst`, both 1-Lipschitz).  Combining the two via
`LipschitzWith.prodMk` yields `max(1, L)` on the product. -/
lemma vlasovVectorField_lipschitzWith
    {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d)) [∀ t, IsProbabilityMeasure (ρ t)]
    (h_int : ∀ t (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ t))
    (t : ℝ) :
    LipschitzWith (max 1 L) (vlasovVectorField gradW ρ t) := by
  -- Force-side `x ↦ (∇W ∗ ρ_t)(x)` is `L`-Lipschitz.
  have h_conv : LipschitzWith L
      (fun x : PhysSpace d => convolveFunctionMeasure gradW (ρ t) x) :=
    convolveFunctionMeasure_lipschitz_in_x gradW L hL (ρ t) (h_int t)
  -- Negate (`Neg.neg` is 1-Lipschitz): `x ↦ -(∇W ∗ ρ_t)(x)` is still `L`-Lipschitz.
  have h_neg_conv : LipschitzWith L
      (fun x : PhysSpace d => -convolveFunctionMeasure gradW (ρ t) x) := by
    simpa [Function.comp_def] using LipschitzWith.id.neg.comp h_conv
  -- Compose with `Prod.fst` (1-Lipschitz): `z ↦ -(∇W ∗ ρ_t)(z.1)` is `L`-Lipschitz.
  have h_force : LipschitzWith L
      (fun z : PhaseSpace d => -convolveFunctionMeasure gradW (ρ t) z.1) := by
    simpa [Function.comp_def] using h_neg_conv.comp
      (LipschitzWith.prod_fst (α := PhysSpace d) (β := PhysSpace d))
  -- Combine velocity-side projection (1-Lipschitz) with force-side (L-Lipschitz).
  exact (LipschitzWith.prod_snd (α := PhysSpace d) (β := PhysSpace d)).prodMk h_force

/-- Pointwise norm bound for the Vlasov phase-space vector field.
`‖b_t(x, v)‖ ≤ max(‖v‖, ‖(∇W ∗ ρ_t)(x)‖)` for the product `max`-norm
on `PhaseSpace d = PhysSpace d × PhysSpace d`.

This is the decomposition used to derive `IsPicardLindelof.norm_le`
once a uniform bound `M` for `‖(∇W ∗ ρ_t)(x)‖` on a closed ball is
known (e.g. from finite-first-moment + Lipschitz growth of `gradW`). -/
lemma vlasovVectorField_norm_le
    {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (ρ : ℝ → Measure (PhysSpace d)) (t : ℝ) (z : PhaseSpace d) :
    ‖vlasovVectorField gradW ρ t z‖ ≤
      max ‖z.2‖ ‖convolveFunctionMeasure gradW (ρ t) z.1‖ := by
  unfold vlasovVectorField
  -- Prod norm is the max of component norms; neg preserves norm.
  simp [Prod.norm_def, norm_neg]

/-- **Local-flow** existence for the Vlasov ODE.

Wraps the vendored parametric Picard-Lindelöf
(`IsPicardLindelof.exists_forall_mem_closedBall_eq_forall_mem_Icc_hasDerivWithinAt_confined`,
`LeanPool.Vlasov.ForMathlib.PicardLindelof`)
into a `HasDerivAt`-on-`Ioo`-shaped characteristic flow.  The result
holds for initial conditions inside `closedBall z₀ (a/2)` and for
times in `Ioo 0 δ` where `δ` is a Picard-derived constant.

The new hypothesis `hbound` (uniform norm bound on the convolution
force on a slightly larger ball, over `[0, 1]`) is the genuine input
the Picard wrapper needs: the contraction condition + the `norm_le`
field of `IsPicardLindelof` both require a global bound on `‖b_t‖`.

The global existence form `exists_vlasov_characteristicFlow` (below)
is the stitched version on `[0, T]`, iterating this local theorem on
overlapping windows and gluing with `ODE_solution_unique`. -/
theorem exists_vlasov_characteristicFlow_local
    {d : ℕ}
    (W : PhysSpace d → ℝ)
    (gradW : PhysSpace d → PhysSpace d)
    (_hgradW : ∀ x, gradW x = gradient W x)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d))
    [∀ t, IsProbabilityMeasure (ρ t)]
    (h_int : ∀ t (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ t))
    (hρ_cont : ∀ x : PhysSpace d,
      Continuous (fun t => convolveFunctionMeasure gradW (ρ t) x))
    -- Local-flow data: the basepoint `z₀`, the ball radius `a`, and a
    -- uniform force bound `M` on `closedBall z₀.1 (3a/2)` over `[0,1]`.
    (z₀ : PhaseSpace d) (a : NNReal) (ha : 0 < a)
    (M : NNReal)
    (hbound : ∀ t ∈ Set.Icc (0 : ℝ) (1 : ℝ),
              ∀ x ∈ Metric.closedBall z₀.1 (3 * (a : ℝ) / 2),
              ‖convolveFunctionMeasure gradW (ρ t) x‖ ≤ M) :
    ∃ (δ : ℝ) (_ : 0 < δ) (charX charV : ℝ → PhaseSpace d → PhysSpace d),
      IsCharacteristicFlowOn gradW ρ charX charV
        (Set.Ioo 0 δ) (Metric.closedBall z₀ ((a : ℝ) / 2)) := by
  classical
  -- IsPicardLindelof parameter choices.
  set K_pl : NNReal := max 1 L with hK_pl_def
  set r_pl : NNReal := a / 2 with hr_pl_def
  set L_pl : NNReal := ‖z₀.2‖₊ + a + M with hL_pl_def
  -- δ chosen to satisfy the contraction L_pl · δ ≤ a − r_pl = a/2.
  set δ : ℝ := min 1 ((a : ℝ) / 2 / ((L_pl : ℝ) + 1)) with hδ_def
  have ha_real : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have h_denom_pos : (0 : ℝ) < (L_pl : ℝ) + 1 := by positivity
  have h_ratio_pos : (0 : ℝ) < (a : ℝ) / 2 / ((L_pl : ℝ) + 1) := by positivity
  have hδ_pos : (0 : ℝ) < δ := lt_min one_pos h_ratio_pos
  have hδ_le_one : δ ≤ 1 := min_le_left _ _
  have hδ_le_ratio : δ ≤ (a : ℝ) / 2 / ((L_pl : ℝ) + 1) := min_le_right _ _
  -- t₀ ∈ Icc 0 δ.
  let t₀ : Set.Icc (0 : ℝ) δ := ⟨0, Set.mem_Icc.mpr ⟨le_refl 0, le_of_lt hδ_pos⟩⟩
  -- Assemble IsPicardLindelof.
  have hpl : IsPicardLindelof (vlasovVectorField gradW ρ) t₀ z₀ a r_pl L_pl K_pl := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- (a) lipschitzOnWith via vlasovVectorField_lipschitzWith.
      intro t _
      exact (vlasovVectorField_lipschitzWith gradW L hL ρ h_int t).lipschitzOnWith
    · -- (b) continuousOn: velocity component constant in t, force continuous by hρ_cont.
      intro x _
      apply Continuous.continuousOn
      simp only [vlasovVectorField]
      exact Continuous.prodMk continuous_const (hρ_cont x.1).neg
    · -- (c) norm_le.
      intro t ht x hx
      have h_norm_field := vlasovVectorField_norm_le gradW ρ t x
      have hdist_le : dist x z₀ ≤ (a : ℝ) := hx
      have hdist_le_norm : ‖x - z₀‖ ≤ (a : ℝ) := by rwa [dist_eq_norm] at hdist_le
      have h_x2_proj : ‖x.2 - z₀.2‖ ≤ ‖x - z₀‖ := by
        rw [Prod.norm_def]; exact le_max_right _ _
      have h_x2_bound : ‖x.2‖ ≤ ‖z₀.2‖ + (a : ℝ) := by
        have h1 : ‖x.2‖ = ‖(x.2 - z₀.2) + z₀.2‖ := by rw [sub_add_cancel]
        have h2 : ‖(x.2 - z₀.2) + z₀.2‖ ≤ ‖x.2 - z₀.2‖ + ‖z₀.2‖ := norm_add_le _ _
        linarith [h_x2_proj, hdist_le_norm]
      have h_x1_proj : dist x.1 z₀.1 ≤ dist x z₀ := by
        simp only [Prod.dist_eq]; exact le_max_left _ _
      have h_x1_ball : x.1 ∈ Metric.closedBall z₀.1 (3 * (a : ℝ) / 2) := by
        have hx1d : dist x.1 z₀.1 ≤ (a : ℝ) := le_trans h_x1_proj hdist_le
        have : dist x.1 z₀.1 ≤ 3 * (a : ℝ) / 2 := by
          have ha_nn : (0 : ℝ) ≤ (a : ℝ) := le_of_lt ha_real
          linarith
        exact this
      have h_t_Icc : t ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨ht.1, le_trans ht.2 hδ_le_one⟩
      have h_force_bound : ‖convolveFunctionMeasure gradW (ρ t) x.1‖ ≤ (M : ℝ) :=
        hbound t h_t_Icc x.1 h_x1_ball
      have h_Lpl_eq : (L_pl : ℝ) = ‖z₀.2‖ + (a : ℝ) + (M : ℝ) := by
        simp [hL_pl_def, NNReal.coe_add, coe_nnnorm]
      calc ‖vlasovVectorField gradW ρ t x‖
          ≤ max ‖x.2‖ ‖convolveFunctionMeasure gradW (ρ t) x.1‖ := h_norm_field
        _ ≤ (L_pl : ℝ) := by
            rw [h_Lpl_eq]
            apply max_le
            · linarith [NNReal.coe_nonneg M]
            · linarith [norm_nonneg z₀.2, NNReal.coe_nonneg a]
    · -- (d) mul_max_le: L_pl · max(δ − 0, 0 − 0) = L_pl · δ ≤ a − a/2 = a/2.
      show (L_pl : ℝ) * max (δ - (t₀ : ℝ)) ((t₀ : ℝ) - 0) ≤ (a : ℝ) - (r_pl : ℝ)
      have ht₀_eq : (t₀ : ℝ) = 0 := rfl
      simp only [ht₀_eq, sub_zero, sub_self, max_eq_left (le_of_lt hδ_pos)]
      have h_a_minus_r : (a : ℝ) - (r_pl : ℝ) = (a : ℝ) / 2 := by
        simp [hr_pl_def, NNReal.coe_div]
        ring
      rw [h_a_minus_r]
      -- L_pl * δ ≤ a/2 since δ ≤ (a/2)/(L_pl+1) and L_pl ≤ L_pl + 1.
      have h_Lpl_nn : (0 : ℝ) ≤ (L_pl : ℝ) := L_pl.coe_nonneg
      have h_a_nn : (0 : ℝ) ≤ (a : ℝ) / 2 := by linarith [ha_real]
      have h_step : (L_pl : ℝ) * δ ≤ (L_pl : ℝ) *
          ((a : ℝ) / 2 / ((L_pl : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left hδ_le_ratio h_Lpl_nn
      have h_rewrite : (L_pl : ℝ) * ((a : ℝ) / 2 / ((L_pl : ℝ) + 1))
          = (L_pl : ℝ) / ((L_pl : ℝ) + 1) * ((a : ℝ) / 2) := by ring
      have h_frac_le : (L_pl : ℝ) / ((L_pl : ℝ) + 1) ≤ 1 := by
        rw [div_le_one h_denom_pos]; linarith
      have h_bound : (L_pl : ℝ) / ((L_pl : ℝ) + 1) * ((a : ℝ) / 2) ≤ (a : ℝ) / 2 := by
        calc (L_pl : ℝ) / ((L_pl : ℝ) + 1) * ((a : ℝ) / 2)
            ≤ 1 * ((a : ℝ) / 2) :=
              mul_le_mul_of_nonneg_right h_frac_le h_a_nn
          _ = (a : ℝ) / 2 := one_mul _
      linarith [h_step, h_rewrite ▸ h_step, h_bound]
  -- Invoke headline Picard-Lindelöf.
  obtain ⟨α, hα⟩ := hpl.exists_forall_mem_closedBall_eq_forall_mem_Icc_hasDerivWithinAt_confined
  -- α : PhaseSpace d → ℝ → PhaseSpace d.  Define charX, charV by projection.
  refine ⟨δ, hδ_pos, fun t z => (α z t).1, fun t z => (α z t).2, ?_, ?_, ?_⟩
  · -- Initial condition: α z 0 = z gives both component equalities.
    intro z hz
    have hz_in_r : z ∈ Metric.closedBall z₀ (r_pl : ℝ) := by
      have hreq : (r_pl : ℝ) = (a : ℝ) / 2 := by simp [hr_pl_def, NNReal.coe_div]
      rw [Metric.mem_closedBall] at hz ⊢
      rw [hreq]; exact hz
    have h_init : α z (t₀ : ℝ) = z := (hα z hz_in_r).1
    have ht₀_eq : (t₀ : ℝ) = 0 := rfl
    rw [ht₀_eq] at h_init
    refine ⟨?_, ?_⟩
    · change (α z 0).1 = z.1; rw [h_init]
    · change (α z 0).2 = z.2; rw [h_init]
  · -- Position ODE: HasDerivAt (charX · z) (charV t z) t.
    intro t ht z hz
    have hz_in_r : z ∈ Metric.closedBall z₀ (r_pl : ℝ) := by
      have : (r_pl : ℝ) = (a : ℝ) / 2 := by simp [hr_pl_def, NNReal.coe_div]
      rw [Metric.mem_closedBall] at hz ⊢; rw [this]; exact hz
    have h_t_Icc : t ∈ Set.Icc (0 : ℝ) δ := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    have h_dw := (hα z hz_in_r).2.1 t h_t_Icc
    have h_icc_nhds : Set.Icc (0 : ℝ) δ ∈ nhds t := Icc_mem_nhds ht.1 ht.2
    have h_d : HasDerivAt (α z) (vlasovVectorField gradW ρ t (α z t)) t :=
      h_dw.hasDerivAt h_icc_nhds
    have h_proj : HasDerivAt (fun s => (α z s).1)
        (vlasovVectorField gradW ρ t (α z t)).1 t :=
      (hasFDerivAt_fst (E := PhysSpace d) (F := PhysSpace d)).comp_hasDerivAt t h_d
    simpa [vlasovVectorField] using h_proj
  · -- Velocity ODE: HasDerivAt (charV · z) (−(∇W∗ρ)(charX t z)) t.
    intro t ht z hz
    have hz_in_r : z ∈ Metric.closedBall z₀ (r_pl : ℝ) := by
      have : (r_pl : ℝ) = (a : ℝ) / 2 := by simp [hr_pl_def, NNReal.coe_div]
      rw [Metric.mem_closedBall] at hz ⊢; rw [this]; exact hz
    have h_t_Icc : t ∈ Set.Icc (0 : ℝ) δ := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    have h_dw := (hα z hz_in_r).2.1 t h_t_Icc
    have h_icc_nhds : Set.Icc (0 : ℝ) δ ∈ nhds t := Icc_mem_nhds ht.1 ht.2
    have h_d : HasDerivAt (α z) (vlasovVectorField gradW ρ t (α z t)) t :=
      h_dw.hasDerivAt h_icc_nhds
    have h_proj : HasDerivAt (fun s => (α z s).2)
        (vlasovVectorField gradW ρ t (α z t)).2 t :=
      (hasFDerivAt_snd (E := PhysSpace d) (F := PhysSpace d)).comp_hasDerivAt t h_d
    simpa [vlasovVectorField] using h_proj

/-- **Per-z, time-shifted single-trajectory Picard with a uniform velocity-bound parameter.**

Given a fixed phase-space point `w`, a starting time `t_start`, an a priori
velocity bound `V_max ≥ ‖w.2‖`, and a uniform force bound around `w` on the
time interval `[t_start, t_start + 1]`, this produces a single trajectory
`β : ℝ → PhaseSpace d` solving the Vlasov ODE on `Ioo t_start (t_start + δ)`
with `β t_start = w`.

**Why `V_max` as a separate parameter:** the Picard contraction time δ
depends on the norm-bound `L_pl := V_max + a + M` for the vector field on
the local ball.  Phrasing this via an explicit `V_max ≥ ‖w.2‖` rather than
the tight `‖w.2‖` makes δ uniform in `w` for any iteration centered at
points `w` whose velocity component is bounded by `V_max`.  This is the
input that lets the N-window iteration in
`exists_vlasov_characteristicFlow` pick a single δ valid across all
windows (by combining with the a priori bound
`‖w_n(z).2‖ ≤ ‖z₀.2‖ + a/2 + M·(T+1)` on a finite `[0, T]`-interval).

Implementation: build an IsPicardLindelof centered at `w` over `[t_start,
t_start + δ]` with `L_pl := V_max + a + M`.  Invoke the vendored headline
theorem.  Take the single trajectory `β t := α w t`. -/
lemma exists_vlasov_extend_one_window
    {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d))
    [∀ t, IsProbabilityMeasure (ρ t)]
    (h_int : ∀ t (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ t))
    (hρ_cont : ∀ x : PhysSpace d,
      Continuous (fun t => convolveFunctionMeasure gradW (ρ t) x))
    (w : PhaseSpace d) (a : NNReal) (ha : 0 < a) (M : NNReal)
    (V_max : NNReal) (hV : ‖w.2‖ ≤ (V_max : ℝ))
    (t_start : ℝ)
    (hbound : ∀ t ∈ Set.Icc t_start (t_start + 1),
              ∀ x ∈ Metric.closedBall w.1 (3 * (a : ℝ) / 2),
              ‖convolveFunctionMeasure gradW (ρ t) x‖ ≤ M) :
    ∃ (δ : ℝ) (_ : 0 < δ) (β : ℝ → PhaseSpace d),
      δ = min 1 ((a : ℝ) / 2 / (((V_max + a + M : NNReal) : ℝ) + 1)) ∧
      β t_start = w ∧
      (∀ t ∈ Set.Ioo t_start (t_start + δ),
        HasDerivAt (fun s => (β s).1) (β t).2 t ∧
        HasDerivAt (fun s => (β s).2)
          (-(convolveFunctionMeasure gradW (ρ t) (β t).1)) t) ∧
      (∀ t ∈ Set.Icc t_start (t_start + δ),
        HasDerivWithinAt (fun s => (β s).1) (β t).2
          (Set.Icc t_start (t_start + δ)) t ∧
        HasDerivWithinAt (fun s => (β s).2)
          (-(convolveFunctionMeasure gradW (ρ t) (β t).1))
          (Set.Icc t_start (t_start + δ)) t) ∧
      (∀ s ∈ Set.Icc t_start (t_start + δ), β s ∈ Metric.closedBall w (a : ℝ)) := by
  classical
  set K_pl : NNReal := max 1 L with hK_pl_def
  set r_pl : NNReal := a / 2 with hr_pl_def
  set L_pl : NNReal := V_max + a + M with hL_pl_def
  set δ : ℝ := min 1 ((a : ℝ) / 2 / ((L_pl : ℝ) + 1)) with hδ_def
  have ha_real : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have h_denom_pos : (0 : ℝ) < (L_pl : ℝ) + 1 := by positivity
  have h_ratio_pos : (0 : ℝ) < (a : ℝ) / 2 / ((L_pl : ℝ) + 1) := by positivity
  have hδ_pos : (0 : ℝ) < δ := lt_min one_pos h_ratio_pos
  have hδ_le_one : δ ≤ 1 := min_le_left _ _
  have hδ_le_ratio : δ ≤ (a : ℝ) / 2 / ((L_pl : ℝ) + 1) := min_le_right _ _
  let t₀ : Set.Icc t_start (t_start + δ) :=
    ⟨t_start, Set.mem_Icc.mpr ⟨le_refl _, by linarith⟩⟩
  have hpl : IsPicardLindelof (vlasovVectorField gradW ρ) t₀ w a r_pl L_pl K_pl := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro t _
      exact (vlasovVectorField_lipschitzWith gradW L hL ρ h_int t).lipschitzOnWith
    · intro x _
      apply Continuous.continuousOn
      simp only [vlasovVectorField]
      exact Continuous.prodMk continuous_const (hρ_cont x.1).neg
    · intro t ht x hx
      have h_norm_field := vlasovVectorField_norm_le gradW ρ t x
      have hdist_le : dist x w ≤ (a : ℝ) := hx
      have hdist_le_norm : ‖x - w‖ ≤ (a : ℝ) := by rwa [dist_eq_norm] at hdist_le
      have h_x2_proj : ‖x.2 - w.2‖ ≤ ‖x - w‖ := by
        rw [Prod.norm_def]; exact le_max_right _ _
      have h_x2_bound : ‖x.2‖ ≤ ‖w.2‖ + (a : ℝ) := by
        have h1 : ‖x.2‖ = ‖(x.2 - w.2) + w.2‖ := by rw [sub_add_cancel]
        have h2 : ‖(x.2 - w.2) + w.2‖ ≤ ‖x.2 - w.2‖ + ‖w.2‖ := norm_add_le _ _
        linarith [h_x2_proj, hdist_le_norm]
      have h_x1_proj : dist x.1 w.1 ≤ dist x w := by
        simp only [Prod.dist_eq]; exact le_max_left _ _
      have h_x1_ball : x.1 ∈ Metric.closedBall w.1 (3 * (a : ℝ) / 2) := by
        rw [Metric.mem_closedBall]
        have hx1d : dist x.1 w.1 ≤ (a : ℝ) := le_trans h_x1_proj hdist_le
        have ha_nn : (0 : ℝ) ≤ (a : ℝ) := le_of_lt ha_real
        linarith
      have h_t_Icc : t ∈ Set.Icc t_start (t_start + 1) :=
        ⟨ht.1, le_trans ht.2 (by linarith [hδ_le_one])⟩
      have h_force_bound : ‖convolveFunctionMeasure gradW (ρ t) x.1‖ ≤ (M : ℝ) :=
        hbound t h_t_Icc x.1 h_x1_ball
      have h_Lpl_eq : (L_pl : ℝ) = (V_max : ℝ) + (a : ℝ) + (M : ℝ) := by
        simp [hL_pl_def, NNReal.coe_add]
      have h_x2_bound' : ‖x.2‖ ≤ (V_max : ℝ) + (a : ℝ) :=
        le_trans h_x2_bound (by linarith [hV])
      calc ‖vlasovVectorField gradW ρ t x‖
          ≤ max ‖x.2‖ ‖convolveFunctionMeasure gradW (ρ t) x.1‖ := h_norm_field
        _ ≤ (L_pl : ℝ) := by
            rw [h_Lpl_eq]
            apply max_le
            · linarith [NNReal.coe_nonneg M, h_x2_bound']
            · linarith [norm_nonneg w.2, NNReal.coe_nonneg a, NNReal.coe_nonneg V_max]
    · show (L_pl : ℝ) * max ((t_start + δ) - (t₀ : ℝ)) ((t₀ : ℝ) - t_start)
          ≤ (a : ℝ) - (r_pl : ℝ)
      have ht₀_eq : (t₀ : ℝ) = t_start := rfl
      simp only [ht₀_eq, add_sub_cancel_left, sub_self, max_eq_left (le_of_lt hδ_pos)]
      have h_a_minus_r : (a : ℝ) - (r_pl : ℝ) = (a : ℝ) / 2 := by
        simp [hr_pl_def, NNReal.coe_div]; ring
      rw [h_a_minus_r]
      have h_Lpl_nn : (0 : ℝ) ≤ (L_pl : ℝ) := L_pl.coe_nonneg
      have h_a_nn : (0 : ℝ) ≤ (a : ℝ) / 2 := by linarith [ha_real]
      have h_step : (L_pl : ℝ) * δ ≤ (L_pl : ℝ) *
          ((a : ℝ) / 2 / ((L_pl : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left hδ_le_ratio h_Lpl_nn
      have h_rewrite : (L_pl : ℝ) * ((a : ℝ) / 2 / ((L_pl : ℝ) + 1))
          = (L_pl : ℝ) / ((L_pl : ℝ) + 1) * ((a : ℝ) / 2) := by ring
      have h_frac_le : (L_pl : ℝ) / ((L_pl : ℝ) + 1) ≤ 1 := by
        rw [div_le_one h_denom_pos]; linarith
      have h_bound : (L_pl : ℝ) / ((L_pl : ℝ) + 1) * ((a : ℝ) / 2) ≤ (a : ℝ) / 2 := by
        calc (L_pl : ℝ) / ((L_pl : ℝ) + 1) * ((a : ℝ) / 2)
            ≤ 1 * ((a : ℝ) / 2) :=
              mul_le_mul_of_nonneg_right h_frac_le h_a_nn
          _ = (a : ℝ) / 2 := one_mul _
      linarith [h_step, h_rewrite ▸ h_step, h_bound]
  obtain ⟨α, hα⟩ := hpl.exists_forall_mem_closedBall_eq_forall_mem_Icc_hasDerivWithinAt_confined
  have hw_in_r : w ∈ Metric.closedBall w ((r_pl : ℝ)) := by
    rw [Metric.mem_closedBall, dist_self]
    exact r_pl.coe_nonneg
  have hα_w := hα w hw_in_r
  refine ⟨δ, hδ_pos, fun t => α w t, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · have h_init : α w (t₀ : ℝ) = w := hα_w.1
    have ht₀_eq : (t₀ : ℝ) = t_start := rfl
    rw [ht₀_eq] at h_init
    exact h_init
  · intro t ht
    have h_t_Icc : t ∈ Set.Icc t_start (t_start + δ) :=
      ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    have h_dw := hα_w.2.1 t h_t_Icc
    have h_icc_nhds : Set.Icc t_start (t_start + δ) ∈ nhds t := Icc_mem_nhds ht.1 ht.2
    have h_d : HasDerivAt (α w) (vlasovVectorField gradW ρ t (α w t)) t :=
      h_dw.hasDerivAt h_icc_nhds
    refine ⟨?_, ?_⟩
    · have h_proj : HasDerivAt (fun s => (α w s).1)
          (vlasovVectorField gradW ρ t (α w t)).1 t :=
        (hasFDerivAt_fst (E := PhysSpace d) (F := PhysSpace d)).comp_hasDerivAt t h_d
      simpa [vlasovVectorField] using h_proj
    · have h_proj : HasDerivAt (fun s => (α w s).2)
          (vlasovVectorField gradW ρ t (α w t)).2 t :=
        (hasFDerivAt_snd (E := PhysSpace d) (F := PhysSpace d)).comp_hasDerivAt t h_d
      simpa [vlasovVectorField] using h_proj
  · intro t ht
    have h_dw := hα_w.2.1 t ht
    refine ⟨?_, ?_⟩
    · have h_proj : HasDerivWithinAt (fun s => (α w s).1)
          (vlasovVectorField gradW ρ t (α w t)).1
          (Set.Icc t_start (t_start + δ)) t :=
        (hasFDerivAt_fst (E := PhysSpace d) (F := PhysSpace d)).comp_hasDerivWithinAt t h_dw
      simpa [vlasovVectorField] using h_proj
    · have h_proj : HasDerivWithinAt (fun s => (α w s).2)
          (vlasovVectorField gradW ρ t (α w t)).2
          (Set.Icc t_start (t_start + δ)) t :=
        (hasFDerivAt_snd (E := PhysSpace d) (F := PhysSpace d)).comp_hasDerivWithinAt t h_dw
      simpa [vlasovVectorField] using h_proj
  · -- confinement: β s ∈ closedBall w a (delivered by `_confined` variant)
    intro s hs
    exact hα_w.2.2 s hs

/-! ### Per-window helpers for the N-window induction in
    `exists_vlasov_characteristicFlow`.

    These three top-level lemmas are generic in `(β, ODE, confinement,
    field bound, IH bound, reference point)` with no mention of the
    N-window induction context (no `γ_k`, `k`, `N`, `z₀`).  This
    genericity gives each helper its own elaboration budget AND makes
    them composable for future call sites — the Lagrangian → Eulerian
    chain rule, well-posedness's Banach iteration, etc.

    Composition order: Helper 1 (confinement) → Helper 2 (window-wide
    velocity bound) → Helper 3 (endpoint position bound).
-/

/-- **Helper 1: Picard window confinement (projection from phase-space ball).**

For a trajectory β satisfying the Vlasov ODE on a Picard window
`[t_start, t_start + δ]` centered at `w`, the position component
stays within the local force-bound ball:
`(β s).1 ∈ closedBall w.1 (3a/2)` for `s` in the window.

**Argument.**  The strengthened Picard-Lindelöf theorem
`exists_forall_mem_closedBall_eq_forall_mem_Icc_hasDerivWithinAt_confined`
(`LeanPool.Vlasov.ForMathlib.PicardLindelof`) exposes
`FunSpace.compProj_mem_closedBall` at the public theorem level,
delivering `β s ∈ closedBall w a` (phase-space ball of radius `a` —
the outer Lipschitz radius) as a side product of the existence
guarantee.  We project this to the position component via
`Prod.dist_eq` + `le_max_left`, then loosen `a ≤ 3a/2` by arithmetic.
The result is a 3-5 line projection.

**Hypothesis `hβ_confined`** is supplied by Vlasov-side callers from
the widened `exists_vlasov_extend_one_window` output.  The other
hypotheses (ODE, field
bound, contraction inequality) are retained for genericity / call
site compatibility; they are not consumed by the projection body but
remain available for future call sites that want to re-derive the
confinement directly (e.g. via supremum trick) without invoking
the vendored Mathlib API. -/
lemma vlasov_window_confinement
    {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (_hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d))
    (_h_int : ∀ t (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ t))
    (_hρ_cont : ∀ x : PhysSpace d,
      Continuous (fun t => convolveFunctionMeasure gradW (ρ t) x))
    (w : PhaseSpace d) (a : NNReal) (_ha : 0 < a) (M : NNReal)
    (V_max : NNReal) (_hV : ‖w.2‖ ≤ (V_max : ℝ))
    (t_start δ : ℝ) (_hδ_pos : 0 < δ) (_hδ_le_one : δ ≤ 1)
    (_hδ_contract : δ ≤ (a : ℝ) / 2 / (((V_max + a + M : NNReal) : ℝ) + 1))
    (_hbound : ∀ t ∈ Set.Icc t_start (t_start + 1),
              ∀ x ∈ Metric.closedBall w.1 (3 * (a : ℝ) / 2),
              ‖convolveFunctionMeasure gradW (ρ t) x‖ ≤ M)
    (β : ℝ → PhaseSpace d) (_hβ_init : β t_start = w)
    (_hβ_ode_Icc : ∀ t ∈ Set.Icc t_start (t_start + δ),
      HasDerivWithinAt (fun s => (β s).1) (β t).2
        (Set.Icc t_start (t_start + δ)) t ∧
      HasDerivWithinAt (fun s => (β s).2)
        (-(convolveFunctionMeasure gradW (ρ t) (β t).1))
        (Set.Icc t_start (t_start + δ)) t)
    (hβ_confined : ∀ s ∈ Set.Icc t_start (t_start + δ),
      β s ∈ Metric.closedBall w (a : ℝ)) :
    ∀ s ∈ Set.Icc t_start (t_start + δ),
      (β s).1 ∈ Metric.closedBall w.1 (3 * (a : ℝ) / 2) := by
  intro s hs
  have h_phase : β s ∈ Metric.closedBall w (a : ℝ) := hβ_confined s hs
  rw [Metric.mem_closedBall] at h_phase ⊢
  -- dist (β s).1 w.1 ≤ dist (β s) w ≤ a ≤ 3a/2
  have h_proj : dist (β s).1 w.1 ≤ dist (β s) w := by
    rw [Prod.dist_eq]; exact le_max_left _ _
  have h_a_nn : (0 : ℝ) ≤ (a : ℝ) := a.coe_nonneg
  linarith

/-- **Helper 2: Window-wide velocity bound.**

For a trajectory β with velocity-component ODE
`(β · ).2' = -(∇W ∗ ρ_·)((β ·).1)` on `[t_start, t_start + δ]` and
force bound M (made applicable by `h_β_in_ball`), the velocity at
every interior `s` is bounded by `h_vel_init + M · (s - t_start)`.

**Math sketch.**  One application of
`Convex.norm_image_sub_le_of_norm_hasDerivWithin_le` on `(β · ).2`
over the convex window `Icc t_start (t_start + δ)`, with `y := s`
universally quantified:
  `‖(β s).2 - (β t_start).2‖ ≤ M · ‖s - t_start‖ = M · (s - t_start)`.
Triangle with `‖(β t_start).2‖ = ‖w.2‖ ≤ h_vel_init` (using `hβ_init`)
gives the conclusion.

The universal quantification over `y` in the mean-value lemma is what
makes this WINDOW-WIDE from ONE invocation — no per-s re-application. -/
lemma vlasov_window_velocity_bound
    {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (ρ : ℝ → Measure (PhysSpace d))
    (w : PhaseSpace d) (a : NNReal) (M : NNReal)
    (t_start δ : ℝ) (hδ_pos : 0 < δ) (hδ_le_one : δ ≤ 1)
    (h_vel_init : ℝ) (hβ_init_vel_bound : ‖w.2‖ ≤ h_vel_init)
    (β : ℝ → PhaseSpace d) (hβ_init : β t_start = w)
    (hβ_ode_Icc : ∀ t ∈ Set.Icc t_start (t_start + δ),
      HasDerivWithinAt (fun s => (β s).2)
        (-(convolveFunctionMeasure gradW (ρ t) (β t).1))
        (Set.Icc t_start (t_start + δ)) t)
    (h_β_in_ball : ∀ s ∈ Set.Icc t_start (t_start + δ),
      (β s).1 ∈ Metric.closedBall w.1 (3 * (a : ℝ) / 2))
    (hbound : ∀ t ∈ Set.Icc t_start (t_start + 1),
              ∀ x ∈ Metric.closedBall w.1 (3 * (a : ℝ) / 2),
              ‖convolveFunctionMeasure gradW (ρ t) x‖ ≤ M) :
    ∀ s ∈ Set.Icc t_start (t_start + δ),
      ‖(β s).2‖ ≤ h_vel_init + (M : ℝ) * (s - t_start) := by
  intro s hs
  -- Convexity of the window.
  have h_convex : Convex ℝ (Set.Icc t_start (t_start + δ)) := convex_Icc _ _
  have h_t_start_in : t_start ∈ Set.Icc t_start (t_start + δ) :=
    ⟨le_refl _, by linarith⟩
  -- Force bound on the window (via h_β_in_ball).
  have h_force_window : ∀ u ∈ Set.Icc t_start (t_start + δ),
      ‖-(convolveFunctionMeasure gradW (ρ u) (β u).1)‖ ≤ (M : ℝ) := by
    intro u hu
    rw [norm_neg]
    have hu_time : u ∈ Set.Icc t_start (t_start + 1) :=
      ⟨hu.1, le_trans hu.2 (by linarith [hδ_le_one])⟩
    exact hbound u hu_time (β u).1 (h_β_in_ball u hu)
  -- Velocity ODE on the window.
  have h_vel_ode : ∀ u ∈ Set.Icc t_start (t_start + δ),
      HasDerivWithinAt (fun v => (β v).2)
        (-(convolveFunctionMeasure gradW (ρ u) (β u).1))
        (Set.Icc t_start (t_start + δ)) u :=
    fun u hu => hβ_ode_Icc u hu
  -- Apply Convex.norm_image_sub_le with x := t_start, y := s.
  have h_mv : ‖(β s).2 - (β t_start).2‖ ≤ (M : ℝ) * ‖s - t_start‖ :=
    h_convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      h_vel_ode h_force_window h_t_start_in hs
  have h_diff_nn : 0 ≤ s - t_start := by linarith [hs.1]
  rw [Real.norm_of_nonneg h_diff_nn] at h_mv
  -- β t_start = w, so (β t_start).2 = w.2.
  have h_β_t_start_vel : (β t_start).2 = w.2 := by rw [hβ_init]
  -- Triangle: ‖(β s).2‖ ≤ ‖(β s).2 - (β t_start).2‖ + ‖(β t_start).2‖.
  have h_decomp : (β s).2 = ((β s).2 - (β t_start).2) + (β t_start).2 :=
    (sub_add_cancel _ _).symm
  have h_triangle : ‖(β s).2‖
      ≤ ‖(β s).2 - (β t_start).2‖ + ‖(β t_start).2‖ := by
    calc ‖(β s).2‖ = ‖((β s).2 - (β t_start).2) + (β t_start).2‖ := by rw [← h_decomp]
      _ ≤ _ := norm_add_le _ _
  -- Combine: ‖(β s).2‖ ≤ M·(s - t_start) + ‖w.2‖ ≤ h_vel_init + M·(s - t_start).
  rw [h_β_t_start_vel] at h_triangle
  -- h_mv has `(β t_start).2`; rewrite to `w.2` for compatibility.
  rw [h_β_t_start_vel] at h_mv
  linarith [h_mv, hβ_init_vel_bound]

/-- **Helper 3: Window endpoint position bound.**

For a trajectory β with position-component ODE
`(β · ).1' = (β · ).2` on `[t_start, t_start + δ]` and a uniform
velocity bound `V_bound` (typically Helper 2's output composed with
a worst-case substitution), the position at `t_start + δ` is bounded
relative to an explicit reference point `x_ref`:
  `‖(β (t_start + δ)).1 - x_ref‖ ≤ h_pos_init + V_bound · δ`
where `h_pos_init ≥ ‖w.1 - x_ref‖`.

**Math sketch.**  One application of
`Convex.norm_image_sub_le_of_norm_hasDerivWithin_le` on `(β · ).1`
over the convex window with `x := t_start`, `y := t_start + δ`:
  `‖(β (t_start + δ)).1 - (β t_start).1‖ ≤ V_bound · δ` (using
  `hβ_init` for `(β t_start).1 = w.1`).
Triangle with `‖w.1 - x_ref‖ ≤ h_pos_init` gives the conclusion.

**Genericity.**  `x_ref : PhysSpace d` is an explicit parameter, NOT
hardcoded to the N-window induction's `z₀.1`.  This makes the helper
reusable for the Lagrangian → Eulerian chain rule (reference point:
support of test function φ), well-posedness's Banach iteration
(reference point: fixed-point candidate), etc. -/
lemma vlasov_window_position_bound
    {d : ℕ}
    (_gradW : PhysSpace d → PhysSpace d)
    (_ρ : ℝ → Measure (PhysSpace d))
    (w : PhaseSpace d)
    (t_start δ : ℝ) (hδ_pos : 0 < δ)
    (V_bound : ℝ)
    (x_ref : PhysSpace d)
    (h_pos_init : ℝ) (hβ_init_pos_bound : ‖w.1 - x_ref‖ ≤ h_pos_init)
    (β : ℝ → PhaseSpace d) (hβ_init : β t_start = w)
    (hβ_ode_Icc : ∀ t ∈ Set.Icc t_start (t_start + δ),
      HasDerivWithinAt (fun s => (β s).1) (β t).2
        (Set.Icc t_start (t_start + δ)) t)
    (h_window_vel : ∀ s ∈ Set.Icc t_start (t_start + δ),
      ‖(β s).2‖ ≤ V_bound) :
    ‖(β (t_start + δ)).1 - x_ref‖ ≤ h_pos_init + V_bound * δ := by
  -- Convexity of the window.
  have h_convex : Convex ℝ (Set.Icc t_start (t_start + δ)) := convex_Icc _ _
  have h_t_start_in : t_start ∈ Set.Icc t_start (t_start + δ) :=
    ⟨le_refl _, by linarith⟩
  have h_t_end_in : t_start + δ ∈ Set.Icc t_start (t_start + δ) :=
    ⟨by linarith, le_refl _⟩
  -- Position ODE on the window.
  have h_pos_ode : ∀ u ∈ Set.Icc t_start (t_start + δ),
      HasDerivWithinAt (fun v => (β v).1) (β u).2
        (Set.Icc t_start (t_start + δ)) u :=
    fun u hu => hβ_ode_Icc u hu
  -- Apply Convex.norm_image_sub_le with x := t_start, y := t_start + δ.
  have h_mv : ‖(β (t_start + δ)).1 - (β t_start).1‖
              ≤ V_bound * ‖(t_start + δ) - t_start‖ :=
    h_convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      h_pos_ode h_window_vel h_t_start_in h_t_end_in
  have h_δ_eq : (t_start + δ) - t_start = δ := by ring
  rw [h_δ_eq, Real.norm_of_nonneg (le_of_lt hδ_pos)] at h_mv
  -- β t_start = w, so (β t_start).1 = w.1.
  have h_β_t_start_pos : (β t_start).1 = w.1 := by rw [hβ_init]
  rw [h_β_t_start_pos] at h_mv
  -- Triangle: ‖(β (t_start+δ)).1 - x_ref‖
  --        ≤ ‖(β (t_start+δ)).1 - w.1‖ + ‖w.1 - x_ref‖
  --        ≤ V_bound · δ + h_pos_init.
  have h_decomp : (β (t_start + δ)).1 - x_ref
                = ((β (t_start + δ)).1 - w.1) + (w.1 - x_ref) := by
    rw [sub_add_sub_cancel]
  have h_triangle : ‖(β (t_start + δ)).1 - x_ref‖
      ≤ ‖(β (t_start + δ)).1 - w.1‖ + ‖w.1 - x_ref‖ := by
    calc ‖(β (t_start + δ)).1 - x_ref‖
        = ‖((β (t_start + δ)).1 - w.1) + (w.1 - x_ref)‖ := by rw [← h_decomp]
      _ ≤ _ := norm_add_le _ _
  linarith [h_mv, hβ_init_pos_bound]

/-- **Tight per-window Picard with an EXPLICIT step δ and an ADAPTIVE force-window.**

Tight form of `exists_vlasov_extend_one_window`: the force bound is required
only on `[t_start, t_start + δ]` (the actual step), not the loose unit window
`[t_start, t_start + 1]`, and `δ` is supplied by the caller (so the N-window
chain can tile exactly, `N·δ = T`, dissolving the `(T+1)²` → `T²` smallness). -/
lemma exists_vlasov_extend_one_window_tight
    {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d))
    [∀ t, IsProbabilityMeasure (ρ t)]
    (h_int : ∀ t (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ t))
    (hρ_cont : ∀ x : PhysSpace d,
      Continuous (fun t => convolveFunctionMeasure gradW (ρ t) x))
    (w : PhaseSpace d) (a : NNReal) (ha : 0 < a) (M : NNReal)
    (V_max : NNReal) (hV : ‖w.2‖ ≤ (V_max : ℝ))
    (t_start : ℝ)
    (δ : ℝ) (hδ_pos : 0 < δ)
    (hδ_le : δ ≤ (a : ℝ) / 2 / (((V_max + a + M : NNReal) : ℝ) + 1))
    (hbound : ∀ t ∈ Set.Icc t_start (t_start + δ),
              ∀ x ∈ Metric.closedBall w.1 (3 * (a : ℝ) / 2),
              ‖convolveFunctionMeasure gradW (ρ t) x‖ ≤ M) :
    ∃ β : ℝ → PhaseSpace d,
      β t_start = w ∧
      (∀ t ∈ Set.Ioo t_start (t_start + δ),
        HasDerivAt (fun s => (β s).1) (β t).2 t ∧
        HasDerivAt (fun s => (β s).2)
          (-(convolveFunctionMeasure gradW (ρ t) (β t).1)) t) ∧
      (∀ t ∈ Set.Icc t_start (t_start + δ),
        HasDerivWithinAt (fun s => (β s).1) (β t).2
          (Set.Icc t_start (t_start + δ)) t ∧
        HasDerivWithinAt (fun s => (β s).2)
          (-(convolveFunctionMeasure gradW (ρ t) (β t).1))
          (Set.Icc t_start (t_start + δ)) t) ∧
      (∀ s ∈ Set.Icc t_start (t_start + δ), β s ∈ Metric.closedBall w (a : ℝ)) := by
  classical
  set K_pl : NNReal := max 1 L with hK_pl_def
  set r_pl : NNReal := a / 2 with hr_pl_def
  set L_pl : NNReal := V_max + a + M with hL_pl_def
  have ha_real : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have h_denom_pos : (0 : ℝ) < (L_pl : ℝ) + 1 := by positivity
  have hδ_le_ratio : δ ≤ (a : ℝ) / 2 / ((L_pl : ℝ) + 1) := hδ_le
  let t₀ : Set.Icc t_start (t_start + δ) :=
    ⟨t_start, Set.mem_Icc.mpr ⟨le_refl _, by linarith⟩⟩
  have hpl : IsPicardLindelof (vlasovVectorField gradW ρ) t₀ w a r_pl L_pl K_pl := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro t _
      exact (vlasovVectorField_lipschitzWith gradW L hL ρ h_int t).lipschitzOnWith
    · intro x _
      apply Continuous.continuousOn
      simp only [vlasovVectorField]
      exact Continuous.prodMk continuous_const (hρ_cont x.1).neg
    · intro t ht x hx
      have h_norm_field := vlasovVectorField_norm_le gradW ρ t x
      have hdist_le : dist x w ≤ (a : ℝ) := hx
      have hdist_le_norm : ‖x - w‖ ≤ (a : ℝ) := by rwa [dist_eq_norm] at hdist_le
      have h_x2_proj : ‖x.2 - w.2‖ ≤ ‖x - w‖ := by
        rw [Prod.norm_def]; exact le_max_right _ _
      have h_x2_bound : ‖x.2‖ ≤ ‖w.2‖ + (a : ℝ) := by
        have h1 : ‖x.2‖ = ‖(x.2 - w.2) + w.2‖ := by rw [sub_add_cancel]
        have h2 : ‖(x.2 - w.2) + w.2‖ ≤ ‖x.2 - w.2‖ + ‖w.2‖ := norm_add_le _ _
        linarith [h_x2_proj, hdist_le_norm]
      have h_x1_proj : dist x.1 w.1 ≤ dist x w := by
        simp only [Prod.dist_eq]; exact le_max_left _ _
      have h_x1_ball : x.1 ∈ Metric.closedBall w.1 (3 * (a : ℝ) / 2) := by
        rw [Metric.mem_closedBall]
        have hx1d : dist x.1 w.1 ≤ (a : ℝ) := le_trans h_x1_proj hdist_le
        have ha_nn : (0 : ℝ) ≤ (a : ℝ) := le_of_lt ha_real
        linarith
      have h_force_bound : ‖convolveFunctionMeasure gradW (ρ t) x.1‖ ≤ (M : ℝ) :=
        hbound t ht x.1 h_x1_ball
      have h_Lpl_eq : (L_pl : ℝ) = (V_max : ℝ) + (a : ℝ) + (M : ℝ) := by
        simp [hL_pl_def, NNReal.coe_add]
      have h_x2_bound' : ‖x.2‖ ≤ (V_max : ℝ) + (a : ℝ) :=
        le_trans h_x2_bound (by linarith [hV])
      calc ‖vlasovVectorField gradW ρ t x‖
          ≤ max ‖x.2‖ ‖convolveFunctionMeasure gradW (ρ t) x.1‖ := h_norm_field
        _ ≤ (L_pl : ℝ) := by
            rw [h_Lpl_eq]
            apply max_le
            · linarith [NNReal.coe_nonneg M, h_x2_bound']
            · linarith [norm_nonneg w.2, NNReal.coe_nonneg a, NNReal.coe_nonneg V_max]
    · show (L_pl : ℝ) * max ((t_start + δ) - (t₀ : ℝ)) ((t₀ : ℝ) - t_start)
          ≤ (a : ℝ) - (r_pl : ℝ)
      have ht₀_eq : (t₀ : ℝ) = t_start := rfl
      simp only [ht₀_eq, add_sub_cancel_left, sub_self, max_eq_left (le_of_lt hδ_pos)]
      have h_a_minus_r : (a : ℝ) - (r_pl : ℝ) = (a : ℝ) / 2 := by
        simp [hr_pl_def, NNReal.coe_div]; ring
      rw [h_a_minus_r]
      have h_Lpl_nn : (0 : ℝ) ≤ (L_pl : ℝ) := L_pl.coe_nonneg
      have h_a_nn : (0 : ℝ) ≤ (a : ℝ) / 2 := by linarith [ha_real]
      have h_step : (L_pl : ℝ) * δ ≤ (L_pl : ℝ) *
          ((a : ℝ) / 2 / ((L_pl : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left hδ_le_ratio h_Lpl_nn
      have h_rewrite : (L_pl : ℝ) * ((a : ℝ) / 2 / ((L_pl : ℝ) + 1))
          = (L_pl : ℝ) / ((L_pl : ℝ) + 1) * ((a : ℝ) / 2) := by ring
      have h_frac_le : (L_pl : ℝ) / ((L_pl : ℝ) + 1) ≤ 1 := by
        rw [div_le_one h_denom_pos]; linarith
      have h_bound : (L_pl : ℝ) / ((L_pl : ℝ) + 1) * ((a : ℝ) / 2) ≤ (a : ℝ) / 2 := by
        calc (L_pl : ℝ) / ((L_pl : ℝ) + 1) * ((a : ℝ) / 2)
            ≤ 1 * ((a : ℝ) / 2) :=
              mul_le_mul_of_nonneg_right h_frac_le h_a_nn
          _ = (a : ℝ) / 2 := one_mul _
      linarith [h_step, h_rewrite ▸ h_step, h_bound]
  obtain ⟨α, hα⟩ := hpl.exists_forall_mem_closedBall_eq_forall_mem_Icc_hasDerivWithinAt_confined
  have hw_in_r : w ∈ Metric.closedBall w ((r_pl : ℝ)) := by
    rw [Metric.mem_closedBall, dist_self]
    exact r_pl.coe_nonneg
  have hα_w := hα w hw_in_r
  refine ⟨fun t => α w t, ?_, ?_, ?_, ?_⟩
  · have h_init : α w (t₀ : ℝ) = w := hα_w.1
    have ht₀_eq : (t₀ : ℝ) = t_start := rfl
    rw [ht₀_eq] at h_init
    exact h_init
  · intro t ht
    have h_t_Icc : t ∈ Set.Icc t_start (t_start + δ) :=
      ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    have h_dw := hα_w.2.1 t h_t_Icc
    have h_icc_nhds : Set.Icc t_start (t_start + δ) ∈ nhds t := Icc_mem_nhds ht.1 ht.2
    have h_d : HasDerivAt (α w) (vlasovVectorField gradW ρ t (α w t)) t :=
      h_dw.hasDerivAt h_icc_nhds
    refine ⟨?_, ?_⟩
    · have h_proj : HasDerivAt (fun s => (α w s).1)
          (vlasovVectorField gradW ρ t (α w t)).1 t :=
        (hasFDerivAt_fst (E := PhysSpace d) (F := PhysSpace d)).comp_hasDerivAt t h_d
      simpa [vlasovVectorField] using h_proj
    · have h_proj : HasDerivAt (fun s => (α w s).2)
          (vlasovVectorField gradW ρ t (α w t)).2 t :=
        (hasFDerivAt_snd (E := PhysSpace d) (F := PhysSpace d)).comp_hasDerivAt t h_d
      simpa [vlasovVectorField] using h_proj
  · intro t ht
    have h_dw := hα_w.2.1 t ht
    refine ⟨?_, ?_⟩
    · have h_proj : HasDerivWithinAt (fun s => (α w s).1)
          (vlasovVectorField gradW ρ t (α w t)).1
          (Set.Icc t_start (t_start + δ)) t :=
        (hasFDerivAt_fst (E := PhysSpace d) (F := PhysSpace d)).comp_hasDerivWithinAt t h_dw
      simpa [vlasovVectorField] using h_proj
    · have h_proj : HasDerivWithinAt (fun s => (α w s).2)
          (vlasovVectorField gradW ρ t (α w t)).2
          (Set.Icc t_start (t_start + δ)) t :=
        (hasFDerivAt_snd (E := PhysSpace d) (F := PhysSpace d)).comp_hasDerivWithinAt t h_dw
      simpa [vlasovVectorField] using h_proj
  · intro s hs
    exact hα_w.2.2 s hs

/-- On the degenerate interval `Icc c c`, every function trivially has every
within-derivative at `c` (the point is not an accumulation point of the
singleton).  Serves the `T = 0` branch and the tiling base case of the tight
flow construction. -/
private lemma hasDerivWithinAt_Icc_self {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (v : E) (c : ℝ) :
    HasDerivWithinAt f v (Set.Icc c c) c := by
  have h_notAccPt : ¬ AccPt c (Filter.principal (Set.Icc c c)) := by
    rw [accPt_iff_clusterPt, Filter.inf_principal]
    simp [ClusterPt, Set.Icc_self]
  rw [hasDerivWithinAt_iff_hasFDerivWithinAt]
  exact HasFDerivWithinAt.of_not_accPt h_notAccPt

/-- Adaptive-window force bound for the tight tiling: on any window
`[c, c + δ] ⊆ [0, T]` whose entry position `p` satisfies the linear drift
invariant `‖p - z₀.1‖ ≤ a/2 + V_max·c`, the global `hbound` (radius `R` from
the tight `hR`) restricts to the moving ball `closedBall p (3a/2)`. -/
private lemma charFlowTight_window_forceBound
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (ρ : ℝ → Measure (PhysSpace d))
    (z₀ : PhaseSpace d) (a M V_max R : NNReal) (T : ℝ) (hT : 0 ≤ T)
    (hV_max_def : V_max = ‖z₀.2‖₊ + a / 2 + M * Real.toNNReal T)
    (hR : 2 * (a : ℝ) + (‖z₀.2‖ + (a : ℝ) / 2) * T + (M : ℝ) * T ^ 2 ≤ R)
    (hbound : ∀ t ∈ Set.Icc (0 : ℝ) T,
              ∀ x ∈ Metric.closedBall z₀.1 (R : ℝ),
              ‖convolveFunctionMeasure gradW (ρ t) x‖ ≤ M)
    (c δ : ℝ) (hc_nn : 0 ≤ c) (hc_le_T : c ≤ T) (hcδ_le_T : c + δ ≤ T)
    (p : PhysSpace d)
    (hp : ‖p - z₀.1‖ ≤ (a : ℝ) / 2 + (V_max : ℝ) * c) :
    ∀ t ∈ Set.Icc c (c + δ), ∀ x ∈ Metric.closedBall p (3 * (a : ℝ) / 2),
      ‖convolveFunctionMeasure gradW (ρ t) x‖ ≤ M := by
  intro t ht x hx
  have h_t_in_global : t ∈ Set.Icc (0 : ℝ) T :=
    ⟨le_trans hc_nn ht.1, le_trans ht.2 hcδ_le_T⟩
  have h_x_local : dist x p ≤ 3 * (a : ℝ) / 2 := hx
  have h_pos_chain : dist x z₀.1
      ≤ 3 * (a : ℝ) / 2 + ((a : ℝ) / 2 + (V_max : ℝ) * c) := by
    calc dist x z₀.1
        ≤ dist x p + dist p z₀.1 := dist_triangle _ _ _
      _ ≤ 3 * (a : ℝ) / 2 + _ := by
          rw [dist_eq_norm]
          exact add_le_add h_x_local hp
  have h_V_max_coe : (V_max : ℝ) = ‖z₀.2‖ + (a : ℝ) / 2 + (M : ℝ) * T := by
    have h_V_def : (V_max : ℝ) = ‖z₀.2‖ + (a : ℝ) / 2 + (M : ℝ) * (T.toNNReal : ℝ) := by
      simp [hV_max_def, NNReal.coe_add, coe_nnnorm, NNReal.coe_mul, NNReal.coe_div]
    rw [h_V_def, Real.coe_toNNReal _ hT]
  have h_V_max_nn : (0 : ℝ) ≤ (V_max : ℝ) := V_max.coe_nonneg
  have h_R_expand : 2 * (a : ℝ) + (V_max : ℝ) * T ≤ R := by
    have h_ring : 2 * (a : ℝ) + (‖z₀.2‖ + (a : ℝ) / 2 + (M : ℝ) * T) * T
        = 2 * (a : ℝ) + (‖z₀.2‖ + (a : ℝ) / 2) * T + (M : ℝ) * T ^ 2 := by ring
    rw [h_V_max_coe, h_ring]; exact hR
  have h_x_in_R : dist x z₀.1 ≤ (R : ℝ) := by
    have h_pos_worst : (V_max : ℝ) * c ≤ (V_max : ℝ) * T :=
      mul_le_mul_of_nonneg_left hc_le_T h_V_max_nn
    linarith [h_pos_chain]
  exact hbound t h_t_in_global x h_x_in_R

/-- Mean-value velocity carry along one window: if `β` solves the velocity ODE
on `[c, b]` with force bounded by `Mr`, then `‖(β s).2‖` grows at most linearly
from its entry value.  Shared by the velocity- and position-invariant steps of
`charFlowTight_window_step`. -/
private lemma charFlowTight_window_velocity_carry
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (ρ : ℝ → Measure (PhysSpace d))
    (β : ℝ → PhaseSpace d) (c b : ℝ) (hcb : c ≤ b) (Mr : ℝ)
    (h_vel : ∀ s ∈ Set.Icc c b,
      HasDerivWithinAt (fun u => (β u).2)
        (-(convolveFunctionMeasure gradW (ρ s) (β s).1)) (Set.Icc c b) s)
    (h_force : ∀ s ∈ Set.Icc c b,
      ‖convolveFunctionMeasure gradW (ρ s) (β s).1‖ ≤ Mr) :
    ∀ s ∈ Set.Icc c b, ‖(β s).2‖ ≤ ‖(β c).2‖ + Mr * (s - c) := by
  intro s hs
  have h_convex : Convex ℝ (Set.Icc c b) := convex_Icc _ _
  have h_c_in : c ∈ Set.Icc c b := ⟨le_refl _, hcb⟩
  have h_force_neg : ∀ u ∈ Set.Icc c b,
      ‖-(convolveFunctionMeasure gradW (ρ u) (β u).1)‖ ≤ Mr := by
    intro u hu; rw [norm_neg]; exact h_force u hu
  have h_mv : ‖(β s).2 - (β c).2‖ ≤ Mr * ‖s - c‖ :=
    h_convex.norm_image_sub_le_of_norm_hasDerivWithin_le h_vel h_force_neg h_c_in hs
  have h_diff_nn : 0 ≤ s - c := by linarith [hs.1]
  rw [Real.norm_of_nonneg h_diff_nn] at h_mv
  have h_triangle : ‖(β s).2‖ ≤ ‖(β s).2 - (β c).2‖ + ‖(β c).2‖ := by
    have h_decomp : (β s).2 = ((β s).2 - (β c).2) + (β c).2 :=
      (sub_add_cancel _ _).symm
    calc ‖(β s).2‖ = ‖((β s).2 - (β c).2) + (β c).2‖ := by rw [← h_decomp]
      _ ≤ _ := norm_add_le _ _
  linarith

/-- Gluing step for the tight tiling: the `Set.piecewise (Set.Iic c)` splice of
a left solution on `[0, c]` and a right solution on `[c, b]` (agreeing at the
join) solves the characteristic ODE system on all of `[0, b]`, via
`HasDerivWithinAt.union` on `Icc 0 c ∪ Icc c b = Icc 0 b`. -/
private lemma charFlowTight_piecewise_ode
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (ρ : ℝ → Measure (PhysSpace d))
    (γL β : ℝ → PhaseSpace d)
    (c b : ℝ) (hc_nn : 0 ≤ c) (hcb : c ≤ b)
    (h_join : β c = γL c)
    (h_ode_L : ∀ t ∈ Set.Icc (0 : ℝ) c,
      HasDerivWithinAt (fun s => (γL s).1) (γL t).2 (Set.Icc (0 : ℝ) c) t ∧
      HasDerivWithinAt (fun s => (γL s).2)
        (-(convolveFunctionMeasure gradW (ρ t) (γL t).1)) (Set.Icc (0 : ℝ) c) t)
    (h_ode_R : ∀ t ∈ Set.Icc c b,
      HasDerivWithinAt (fun s => (β s).1) (β t).2 (Set.Icc c b) t ∧
      HasDerivWithinAt (fun s => (β s).2)
        (-(convolveFunctionMeasure gradW (ρ t) (β t).1)) (Set.Icc c b) t) :
    ∀ t ∈ Set.Icc (0 : ℝ) b,
      HasDerivWithinAt (fun s => (Set.piecewise (Set.Iic c) γL β s).1)
        (Set.piecewise (Set.Iic c) γL β t).2 (Set.Icc (0 : ℝ) b) t ∧
      HasDerivWithinAt (fun s => (Set.piecewise (Set.Iic c) γL β s).2)
        (-(convolveFunctionMeasure gradW (ρ t)
            (Set.piecewise (Set.Iic c) γL β t).1)) (Set.Icc (0 : ℝ) b) t := by
  classical
  intro t ht
  have h_left : ∀ y ≤ c, Set.piecewise (Set.Iic c) γL β y = γL y := fun y hy =>
    Set.piecewise_eq_of_mem _ _ _ hy
  have h_right : ∀ y, c < y → Set.piecewise (Set.Iic c) γL β y = β y := fun y hy =>
    Set.piecewise_eq_of_notMem _ _ _ (not_le.mpr hy)
  have h_at_join : Set.piecewise (Set.Iic c) γL β c = γL c := h_left _ (le_refl _)
  have h_on_right_Icc : ∀ y ∈ Set.Icc c b,
      Set.piecewise (Set.Iic c) γL β y = β y := by
    intro y hy
    rcases eq_or_lt_of_le hy.1 with hy_eq | hy_lt
    · rw [← hy_eq, h_at_join, h_join]
    · exact h_right y hy_lt
  have h_set_union : Set.Icc (0 : ℝ) c ∪ Set.Icc c b = Set.Icc (0 : ℝ) b :=
    Set.Icc_union_Icc_eq_Icc hc_nn hcb
  have hA_pos : HasDerivWithinAt (fun s => (Set.piecewise (Set.Iic c) γL β s).1)
      (Set.piecewise (Set.Iic c) γL β t).2 (Set.Icc (0 : ℝ) c) t := by
    by_cases ht_left : t ≤ c
    · have ht_in : t ∈ Set.Icc (0 : ℝ) c := ⟨ht.1, ht_left⟩
      have h_γL_pos := (h_ode_L t ht_in).1
      have h_deriv_eq : (Set.piecewise (Set.Iic c) γL β t).2 = (γL t).2 := by
        rw [h_left t ht_left]
      rw [h_deriv_eq]
      refine h_γL_pos.congr (fun y hy => ?_) ?_
      · rw [h_left y hy.2]
      · rw [h_left t ht_left]
    · rw [not_le] at ht_left
      rw [hasDerivWithinAt_iff_hasFDerivWithinAt]
      apply HasFDerivWithinAt.of_notMem_closure
      rw [closure_Icc, Set.mem_Icc]
      rintro ⟨_, _⟩; linarith
  have hB_pos : HasDerivWithinAt (fun s => (Set.piecewise (Set.Iic c) γL β s).1)
      (Set.piecewise (Set.Iic c) γL β t).2 (Set.Icc c b) t := by
    by_cases ht_right : c ≤ t
    · have ht_in : t ∈ Set.Icc c b := ⟨ht_right, ht.2⟩
      have h_β_pos := (h_ode_R t ht_in).1
      have h_deriv_eq : (Set.piecewise (Set.Iic c) γL β t).2 = (β t).2 := by
        rw [h_on_right_Icc t ht_in]
      rw [h_deriv_eq]
      refine h_β_pos.congr (fun y hy => ?_) ?_
      · rw [h_on_right_Icc y hy]
      · rw [h_on_right_Icc t ht_in]
    · rw [not_le] at ht_right
      rw [hasDerivWithinAt_iff_hasFDerivWithinAt]
      apply HasFDerivWithinAt.of_notMem_closure
      rw [closure_Icc, Set.mem_Icc]
      rintro ⟨_, _⟩; linarith
  have hA_vel : HasDerivWithinAt (fun s => (Set.piecewise (Set.Iic c) γL β s).2)
      (-(convolveFunctionMeasure gradW (ρ t)
          (Set.piecewise (Set.Iic c) γL β t).1)) (Set.Icc (0 : ℝ) c) t := by
    by_cases ht_left : t ≤ c
    · have ht_in : t ∈ Set.Icc (0 : ℝ) c := ⟨ht.1, ht_left⟩
      have h_γL_vel := (h_ode_L t ht_in).2
      have h_pos_eq : (Set.piecewise (Set.Iic c) γL β t).1 = (γL t).1 := by
        rw [h_left t ht_left]
      rw [h_pos_eq]
      refine h_γL_vel.congr (fun y hy => ?_) ?_
      · rw [h_left y hy.2]
      · rw [h_left t ht_left]
    · rw [not_le] at ht_left
      rw [hasDerivWithinAt_iff_hasFDerivWithinAt]
      apply HasFDerivWithinAt.of_notMem_closure
      rw [closure_Icc, Set.mem_Icc]
      rintro ⟨_, _⟩; linarith
  have hB_vel : HasDerivWithinAt (fun s => (Set.piecewise (Set.Iic c) γL β s).2)
      (-(convolveFunctionMeasure gradW (ρ t)
          (Set.piecewise (Set.Iic c) γL β t).1)) (Set.Icc c b) t := by
    by_cases ht_right : c ≤ t
    · have ht_in : t ∈ Set.Icc c b := ⟨ht_right, ht.2⟩
      have h_β_vel := (h_ode_R t ht_in).2
      have h_pos_eq : (Set.piecewise (Set.Iic c) γL β t).1 = (β t).1 := by
        rw [h_on_right_Icc t ht_in]
      rw [h_pos_eq]
      refine h_β_vel.congr (fun y hy => ?_) ?_
      · rw [h_on_right_Icc y hy]
      · rw [h_on_right_Icc t ht_in]
    · rw [not_le] at ht_right
      rw [hasDerivWithinAt_iff_hasFDerivWithinAt]
      apply HasFDerivWithinAt.of_notMem_closure
      rw [closure_Icc, Set.mem_Icc]
      rintro ⟨_, _⟩; linarith
  constructor
  · have h_union_pos := hA_pos.union hB_pos
    rw [h_set_union] at h_union_pos
    exact h_union_pos
  · have h_union_vel := hA_vel.union hB_vel
    rw [h_set_union] at h_union_vel
    exact h_union_vel

/-- One tiling step for the tight flow: extend a trajectory satisfying the
tight invariants on `[0, c]` to `[0, c + δ']` via
`exists_vlasov_extend_one_window_tight`, splicing with `Set.piecewise`
(`charFlowTight_piecewise_ode`) and carrying the linear velocity- and
position-drift invariants (`charFlowTight_window_velocity_carry` +
`vlasov_window_position_bound`). -/
private lemma charFlowTight_window_step
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d))
    [∀ t, IsProbabilityMeasure (ρ t)]
    (h_int : ∀ t (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ t))
    (hρ_cont : ∀ x : PhysSpace d,
      Continuous (fun t => convolveFunctionMeasure gradW (ρ t) x))
    (z₀ : PhaseSpace d) (a : NNReal) (ha : 0 < a)
    (M V_max R : NNReal) (T : ℝ) (hT : 0 ≤ T)
    (hV_max_def : V_max = ‖z₀.2‖₊ + a / 2 + M * Real.toNNReal T)
    (hR : 2 * (a : ℝ) + (‖z₀.2‖ + (a : ℝ) / 2) * T + (M : ℝ) * T ^ 2 ≤ R)
    (hbound : ∀ t ∈ Set.Icc (0 : ℝ) T,
              ∀ x ∈ Metric.closedBall z₀.1 (R : ℝ),
              ‖convolveFunctionMeasure gradW (ρ t) x‖ ≤ M)
    (δ' : ℝ) (hδ'_pos : 0 < δ')
    (hδ'_le_max : δ' ≤ (a : ℝ) / 2 / (((V_max + a + M : NNReal) : ℝ) + 1))
    (z : PhaseSpace d) (c : ℝ) (hc_nn : 0 ≤ c) (hcδ_le_T : c + δ' ≤ T)
    (γ_k : ℝ → PhaseSpace d) (h_γ0 : γ_k 0 = z)
    (h_ode_k : ∀ t ∈ Set.Icc (0 : ℝ) c,
      HasDerivWithinAt (fun s => (γ_k s).1) (γ_k t).2 (Set.Icc (0 : ℝ) c) t ∧
      HasDerivWithinAt (fun s => (γ_k s).2)
        (-(convolveFunctionMeasure gradW (ρ t) (γ_k t).1)) (Set.Icc (0 : ℝ) c) t)
    (h_vel_k : ‖(γ_k c).2‖ ≤ ‖z₀.2‖ + (a : ℝ) / 2 + (M : ℝ) * c)
    (h_pos_k : ‖(γ_k c).1 - z₀.1‖ ≤ (a : ℝ) / 2 + (V_max : ℝ) * c) :
    ∃ γ : ℝ → PhaseSpace d, γ 0 = z ∧
      (∀ t ∈ Set.Icc (0 : ℝ) (c + δ'),
        HasDerivWithinAt (fun s => (γ s).1) (γ t).2
          (Set.Icc (0 : ℝ) (c + δ')) t ∧
        HasDerivWithinAt (fun s => (γ s).2)
          (-(convolveFunctionMeasure gradW (ρ t) (γ t).1))
          (Set.Icc (0 : ℝ) (c + δ')) t) ∧
      ‖(γ (c + δ')).2‖ ≤ ‖z₀.2‖ + (a : ℝ) / 2 + (M : ℝ) * (c + δ') ∧
      ‖(γ (c + δ')).1 - z₀.1‖ ≤ (a : ℝ) / 2 + (V_max : ℝ) * (c + δ') := by
  classical
  have hc_lt_b : c < c + δ' := by linarith
  have hc_le_T : c ≤ T := by linarith
  have hM_nn : (0 : ℝ) ≤ (M : ℝ) := M.coe_nonneg
  have h_V_max_coe : (V_max : ℝ) = ‖z₀.2‖ + (a : ℝ) / 2 + (M : ℝ) * T := by
    have h_V_def : (V_max : ℝ) = ‖z₀.2‖ + (a : ℝ) / 2 + (M : ℝ) * (T.toNNReal : ℝ) := by
      simp [hV_max_def, NNReal.coe_add, coe_nnnorm, NNReal.coe_mul, NNReal.coe_div]
    rw [h_V_def, Real.coe_toNNReal _ hT]
  have h_vel_Vmax : ‖(γ_k c).2‖ ≤ (V_max : ℝ) := by
    rw [h_V_max_coe]
    calc ‖(γ_k c).2‖
        ≤ ‖z₀.2‖ + (a : ℝ) / 2 + (M : ℝ) * c := h_vel_k
      _ ≤ ‖z₀.2‖ + (a : ℝ) / 2 + (M : ℝ) * T := by
          linarith [mul_le_mul_of_nonneg_left hc_le_T hM_nn]
  have hbound_local := charFlowTight_window_forceBound gradW ρ z₀ a M V_max R T hT
    hV_max_def hR hbound c δ' hc_nn hc_le_T hcδ_le_T (γ_k c).1 h_pos_k
  obtain ⟨β, hβ_init, _hβ_ode_Ioo, hβ_ode_Icc, hβ_confined⟩ :=
    exists_vlasov_extend_one_window_tight gradW L hL ρ h_int hρ_cont
      (γ_k c) a ha M V_max h_vel_Vmax c δ' hδ'_pos hδ'_le_max hbound_local
  have h_β_in_ball : ∀ s ∈ Set.Icc c (c + δ'),
      (β s).1 ∈ Metric.closedBall (γ_k c).1 (3 * (a : ℝ) / 2) := by
    intro s hs
    have h_phase : β s ∈ Metric.closedBall (γ_k c) (a : ℝ) := hβ_confined s hs
    rw [Metric.mem_closedBall] at h_phase ⊢
    have h_proj : dist (β s).1 (γ_k c).1 ≤ dist (β s) (γ_k c) := by
      rw [Prod.dist_eq]; exact le_max_left _ _
    have h_a_nn : (0 : ℝ) ≤ (a : ℝ) := a.coe_nonneg
    linarith
  have h_force_window : ∀ s ∈ Set.Icc c (c + δ'),
      ‖convolveFunctionMeasure gradW (ρ s) (β s).1‖ ≤ (M : ℝ) := fun s hs =>
    hbound_local s hs (β s).1 (h_β_in_ball s hs)
  have h_vel_carry := charFlowTight_window_velocity_carry gradW ρ β c (c + δ')
    (le_of_lt hc_lt_b) (M : ℝ) (fun s hs => (hβ_ode_Icc s hs).2) h_force_window
  have h_β_c_vel : (β c).2 = (γ_k c).2 := by rw [hβ_init]
  have h_ode_pw := charFlowTight_piecewise_ode gradW ρ γ_k β c (c + δ') hc_nn
    (le_of_lt hc_lt_b) hβ_init h_ode_k hβ_ode_Icc
  have h_right_end : Set.piecewise (Set.Iic c) γ_k β (c + δ') = β (c + δ') :=
    Set.piecewise_eq_of_notMem _ _ _ (not_le.mpr hc_lt_b)
  have h_left0 : Set.piecewise (Set.Iic c) γ_k β 0 = γ_k 0 :=
    Set.piecewise_eq_of_mem _ _ _ hc_nn
  refine ⟨Set.piecewise (Set.Iic c) γ_k β, by rw [h_left0, h_γ0], h_ode_pw, ?_, ?_⟩
  · -- Velocity invariant at the new endpoint, via the mean-value carry.
    rw [h_right_end]
    have h_carry_b := h_vel_carry (c + δ') ⟨le_of_lt hc_lt_b, le_refl _⟩
    rw [h_β_c_vel] at h_carry_b
    have h_ring : (M : ℝ) * (c + δ' - c) = (M : ℝ) * δ' := by ring
    rw [h_ring] at h_carry_b
    calc ‖(β (c + δ')).2‖
        ≤ ‖(γ_k c).2‖ + (M : ℝ) * δ' := h_carry_b
      _ ≤ ‖z₀.2‖ + (a : ℝ) / 2 + (M : ℝ) * c + (M : ℝ) * δ' := by linarith [h_vel_k]
      _ = ‖z₀.2‖ + (a : ℝ) / 2 + (M : ℝ) * (c + δ') := by ring
  · -- Position invariant at the new endpoint, via the window position bound.
    rw [h_right_end]
    have h_window_vel_Vmax : ∀ s ∈ Set.Icc c (c + δ'),
        ‖(β s).2‖ ≤ (V_max : ℝ) := by
      intro s hs
      have h_carry_s := h_vel_carry s hs
      rw [h_β_c_vel] at h_carry_s
      have h_s_le_T : s ≤ T := le_trans hs.2 hcδ_le_T
      have h_M_split : (M : ℝ) * (s - c) + (M : ℝ) * c = (M : ℝ) * s := by ring
      have h_M_mono : (M : ℝ) * s ≤ (M : ℝ) * T :=
        mul_le_mul_of_nonneg_left h_s_le_T hM_nn
      rw [h_V_max_coe]
      linarith [h_carry_s, h_vel_k]
    have h_pos_carry :=
      vlasov_window_position_bound gradW ρ (γ_k c) c δ' hδ'_pos
        (V_max : ℝ) z₀.1 ((a : ℝ) / 2 + (V_max : ℝ) * c) h_pos_k β hβ_init
        (fun t ht => (hβ_ode_Icc t ht).1) h_window_vel_Vmax
    calc ‖(β (c + δ')).1 - z₀.1‖
        ≤ (a : ℝ) / 2 + (V_max : ℝ) * c + (V_max : ℝ) * δ' := h_pos_carry
      _ = (a : ℝ) / 2 + (V_max : ℝ) * (c + δ') := by ring

/-- Per-`z` trajectory for the tight flow: `N`-fold exact tiling of
`[0, N·δ']` by windows of width `δ'`, by induction via
`charFlowTight_window_step`, carrying the tight velocity/position invariants
through the induction and discarding them at the end. -/
private lemma charFlowTight_perZ_trajectory
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d))
    [∀ t, IsProbabilityMeasure (ρ t)]
    (h_int : ∀ t (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ t))
    (hρ_cont : ∀ x : PhysSpace d,
      Continuous (fun t => convolveFunctionMeasure gradW (ρ t) x))
    (z₀ : PhaseSpace d) (a : NNReal) (ha : 0 < a)
    (M V_max R : NNReal) (T : ℝ) (hT : 0 ≤ T)
    (hV_max_def : V_max = ‖z₀.2‖₊ + a / 2 + M * Real.toNNReal T)
    (hR : 2 * (a : ℝ) + (‖z₀.2‖ + (a : ℝ) / 2) * T + (M : ℝ) * T ^ 2 ≤ R)
    (hbound : ∀ t ∈ Set.Icc (0 : ℝ) T,
              ∀ x ∈ Metric.closedBall z₀.1 (R : ℝ),
              ‖convolveFunctionMeasure gradW (ρ t) x‖ ≤ M)
    (N : ℕ) (δ' : ℝ) (hδ'_pos : 0 < δ')
    (hδ'_le_max : δ' ≤ (a : ℝ) / 2 / (((V_max + a + M : NNReal) : ℝ) + 1))
    (hNδ'_le_T : (N : ℝ) * δ' ≤ T)
    (z : PhaseSpace d) (hz : z ∈ Metric.closedBall z₀ ((a : ℝ) / 2)) :
    ∃ γ : ℝ → PhaseSpace d,
      γ 0 = z ∧
      ∀ t ∈ Set.Icc (0 : ℝ) ((N : ℝ) * δ'),
        HasDerivWithinAt (fun s => (γ s).1) (γ t).2
          (Set.Icc (0 : ℝ) ((N : ℝ) * δ')) t ∧
        HasDerivWithinAt (fun s => (γ s).2)
          (-(convolveFunctionMeasure gradW (ρ t) (γ t).1))
          (Set.Icc (0 : ℝ) ((N : ℝ) * δ')) t := by
  suffices h_strong : ∀ k : ℕ, k ≤ N → ∃ γ : ℝ → PhaseSpace d,
      γ 0 = z ∧
      (∀ t ∈ Set.Icc (0 : ℝ) ((k : ℝ) * δ'),
        HasDerivWithinAt (fun s => (γ s).1) (γ t).2
          (Set.Icc (0 : ℝ) ((k : ℝ) * δ')) t ∧
        HasDerivWithinAt (fun s => (γ s).2)
          (-(convolveFunctionMeasure gradW (ρ t) (γ t).1))
          (Set.Icc (0 : ℝ) ((k : ℝ) * δ')) t) ∧
      ‖(γ ((k : ℝ) * δ')).2‖ ≤
        ‖z₀.2‖ + (a : ℝ) / 2 + (M : ℝ) * ((k : ℝ) * δ') ∧
      ‖(γ ((k : ℝ) * δ')).1 - z₀.1‖ ≤
        (a : ℝ) / 2 + (V_max : ℝ) * ((k : ℝ) * δ') by
    obtain ⟨γ, hγ0, hode, _, _⟩ := h_strong N (le_refl N)
    exact ⟨γ, hγ0, hode⟩
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨fun _ => z, rfl, ?_, ?_, ?_⟩
    · intro t ht
      have ht_eq : t = 0 := le_antisymm (by simpa using ht.2) ht.1
      subst ht_eq
      have h_set_eq : Set.Icc (0 : ℝ) (((0 : ℕ) : ℝ) * δ') = Set.Icc (0 : ℝ) 0 := by
        norm_num
      rw [h_set_eq]
      exact ⟨hasDerivWithinAt_Icc_self _ _ _, hasDerivWithinAt_Icc_self _ _ _⟩
    · have hdist : ‖z - z₀‖ ≤ (a : ℝ) / 2 := by
        rw [← dist_eq_norm]; exact hz
      have h_z2_proj : ‖z.2 - z₀.2‖ ≤ ‖z - z₀‖ := by
        rw [Prod.norm_def]; exact le_max_right _ _
      have h_z2_bound : ‖z.2‖ ≤ ‖z₀.2‖ + (a : ℝ) / 2 := by
        have h1 : ‖z.2‖ = ‖(z.2 - z₀.2) + z₀.2‖ := by rw [sub_add_cancel]
        have h2 : ‖(z.2 - z₀.2) + z₀.2‖ ≤ ‖z.2 - z₀.2‖ + ‖z₀.2‖ := norm_add_le _ _
        linarith [h_z2_proj, hdist]
      change ‖((fun _ => z) (((0 : ℕ) : ℝ) * δ')).2‖ ≤
        ‖z₀.2‖ + (a : ℝ) / 2 + (M : ℝ) * (((0 : ℕ) : ℝ) * δ')
      simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero]
      linarith
    · have hdist : ‖z - z₀‖ ≤ (a : ℝ) / 2 := by
        rw [← dist_eq_norm]; exact hz
      have h_z1_proj : ‖z.1 - z₀.1‖ ≤ ‖z - z₀‖ := by
        rw [Prod.norm_def]; exact le_max_left _ _
      change ‖((fun _ => z) (((0 : ℕ) : ℝ) * δ')).1 - z₀.1‖ ≤
        (a : ℝ) / 2 + (V_max : ℝ) * (((0 : ℕ) : ℝ) * δ')
      simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero]
      linarith
  | succ k ih =>
    intro hk_succ_le_N
    obtain ⟨γ_k, h_γ0, h_ode_k, h_vel_k, h_pos_k⟩ :=
      ih (Nat.le_of_succ_le hk_succ_le_N)
    have h_kδ_nn : (0 : ℝ) ≤ (k : ℝ) * δ' := by positivity
    have h_kδ_succ_eq : (k : ℝ) * δ' + δ' = ((k + 1 : ℕ) : ℝ) * δ' := by
      push_cast; ring
    have h_succ_kδ_le_T : ((k + 1 : ℕ) : ℝ) * δ' ≤ T := by
      calc ((k + 1 : ℕ) : ℝ) * δ'
          ≤ (N : ℝ) * δ' := by
            have h_cast : ((k + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by
              exact_mod_cast hk_succ_le_N
            exact mul_le_mul_of_nonneg_right h_cast (le_of_lt hδ'_pos)
        _ ≤ T := hNδ'_le_T
    obtain ⟨γ, hγ0, h_ode, h_vel, h_pos⟩ :=
      charFlowTight_window_step gradW L hL ρ h_int hρ_cont z₀ a ha M V_max R T hT
        hV_max_def hR hbound δ' hδ'_pos hδ'_le_max z ((k : ℝ) * δ') h_kδ_nn
        (by rw [h_kδ_succ_eq]; exact h_succ_kδ_le_T) γ_k h_γ0 h_ode_k h_vel_k h_pos_k
    rw [← h_kδ_succ_eq]
    exact ⟨γ, hγ0, h_ode, h_vel, h_pos⟩

/-- **Tight global per-ball flow: `[0,T]` force-window, `T²` smallness (no `+1`).**

Tight form of `exists_vlasov_characteristicFlow`.  By tiling `[0,T]`
EXACTLY (`N = ⌈T/δ_max⌉` windows of width `δ' = T/N ≤ δ_max`, so `N·δ' = T`) and
calling `exists_vlasov_extend_one_window_tight` with the adaptive force-window
`[k·δ', (k+1)·δ']`, the global force-bound is required only on `[0,T]` and the
position drift is `M·T²` (not `M·(T+1)²`).  Consumers' R-selection then needs only
`L·T² < 1`, satisfiable for any `L` (threshold `T < 1/√L`), dissolving the `L<1`
restriction. -/
theorem exists_vlasov_characteristicFlow_tight
    {d : ℕ} [NeZero d]
    (W : PhysSpace d → ℝ)
    (gradW : PhysSpace d → PhysSpace d)
    (_hgradW : ∀ x, gradW x = gradient W x)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d))
    [∀ t, IsProbabilityMeasure (ρ t)]
    (h_int : ∀ t (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ t))
    (hρ_cont : ∀ x : PhysSpace d,
      Continuous (fun t => convolveFunctionMeasure gradW (ρ t) x))
    (z₀ : PhaseSpace d) (a : NNReal) (ha : 0 < a)
    (M : NNReal) (T : ℝ) (hT : 0 ≤ T)
    (R : NNReal)
    (hR : 2 * (a : ℝ) + (‖z₀.2‖ + (a : ℝ) / 2) * T + (M : ℝ) * T ^ 2 ≤ R)
    (hbound : ∀ t ∈ Set.Icc (0 : ℝ) T,
              ∀ x ∈ Metric.closedBall z₀.1 (R : ℝ),
              ‖convolveFunctionMeasure gradW (ρ t) x‖ ≤ M) :
    ∃ (charX charV : ℝ → PhaseSpace d → PhysSpace d),
      IsCharacteristicFlowOn gradW ρ charX charV
        (Set.Ioo 0 T) (Metric.closedBall z₀ ((a : ℝ) / 2)) ∧
      (∀ z ∈ Metric.closedBall z₀ ((a : ℝ) / 2),
        ∀ t ∈ Set.Icc (0 : ℝ) T,
          HasDerivWithinAt (fun s => charX s z) (charV t z)
            (Set.Icc (0 : ℝ) T) t ∧
          HasDerivWithinAt (fun s => charV s z)
            (-(convolveFunctionMeasure gradW (ρ t) (charX t z)))
            (Set.Icc (0 : ℝ) T) t) := by
  classical
  -- ============================================================
  -- Parameter setup (uniform across all windows and initial z).
  -- TIGHT: V_max uses `T` (not `T+1`); EXACT tiling N·δ' = T.
  -- ============================================================
  set V_max : NNReal :=
    ‖z₀.2‖₊ + a / 2 + M * Real.toNNReal T with hV_max_def
  have ha_real : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have h_denom_pos : (0 : ℝ) < (((V_max + a + M : NNReal) : ℝ) + 1) := by positivity
  set δ_max : ℝ := (a : ℝ) / 2 / (((V_max + a + M : NNReal) : ℝ) + 1) with hδ_max_def
  have hδ_max_pos : (0 : ℝ) < δ_max := by rw [hδ_max_def]; positivity
  -- T = 0 edge case: the conclusion's intervals collapse.
  rcases eq_or_lt_of_le hT with hT_eq | hT_pos
  · -- T = 0: Ioo 0 0 = ∅, Icc 0 0 = {0}.  Build the trivial flow γ_func z s = z.
    subst hT_eq
    -- charX/charV constant in time, equal to z (resp. its components).
    refine ⟨fun _ z => z.1, fun _ z => z.2, ⟨?_, ?_, ?_⟩, ?_⟩
    · intro z hz; exact ⟨rfl, rfl⟩
    · intro t ht z hz; exact absurd (lt_trans ht.1 ht.2) (lt_irrefl 0)
    · intro t ht z hz; exact absurd (lt_trans ht.1 ht.2) (lt_irrefl 0)
    · intro z hz t ht
      have ht_eq : t = 0 := le_antisymm ht.2 ht.1
      subst ht_eq
      exact ⟨hasDerivWithinAt_Icc_self _ _ _, hasDerivWithinAt_Icc_self _ _ _⟩
  · -- T > 0: EXACT tiling.
    -- N := ⌈T/δ_max⌉₊ windows of width δ' = T/N ≤ δ_max, so N·δ' = T.
    set N : ℕ := ⌈T / δ_max⌉₊ with hN_def
    have hN_pos : 0 < N := by
      rw [hN_def, Nat.ceil_pos]
      positivity
    have hN_real_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN_pos
    set δ' : ℝ := T / (N : ℝ) with hδ'_def
    have hδ'_pos : (0 : ℝ) < δ' := by rw [hδ'_def]; positivity
    have hNδ'_eq : (N : ℝ) * δ' = T := by
      rw [hδ'_def]; field_simp
    -- δ' ≤ δ_max because N ≥ T/δ_max.
    have hδ'_le_max : δ' ≤ δ_max := by
      have h_ceil : T / δ_max ≤ (N : ℝ) := Nat.le_ceil _
      rw [hδ'_def, div_le_iff₀ hN_real_pos]
      calc T = (T / δ_max) * δ_max := by field_simp
        _ ≤ (N : ℝ) * δ_max :=
            mul_le_mul_of_nonneg_right h_ceil (le_of_lt hδ_max_pos)
        _ = δ_max * (N : ℝ) := by ring
    -- ============================================================
    -- Per-z induction: a curve solving the ODE on [0, N·δ'] = [0, T].
    -- ============================================================
    have h_perZ : ∀ z ∈ Metric.closedBall z₀ ((a : ℝ) / 2),
        ∃ γ : ℝ → PhaseSpace d,
          γ 0 = z ∧
          ∀ t ∈ Set.Icc (0 : ℝ) ((N : ℝ) * δ'),
            HasDerivWithinAt (fun s => (γ s).1) (γ t).2
              (Set.Icc (0 : ℝ) ((N : ℝ) * δ')) t ∧
            HasDerivWithinAt (fun s => (γ s).2)
              (-(convolveFunctionMeasure gradW (ρ t) (γ t).1))
              (Set.Icc (0 : ℝ) ((N : ℝ) * δ')) t :=
      fun z hz =>
        charFlowTight_perZ_trajectory gradW L hL ρ h_int hρ_cont z₀ a ha M V_max R
          T hT hV_max_def hR hbound N δ' hδ'_pos
          (by rw [← hδ_max_def]; exact hδ'_le_max) (le_of_eq hNδ'_eq) z hz
    -- ============================================================
    -- Bundle per-z curves into a joint flow via Classical.choose.
    -- ============================================================
    let γ_func : PhaseSpace d → ℝ → PhaseSpace d := fun z =>
      if hz : z ∈ Metric.closedBall z₀ ((a : ℝ) / 2)
      then Classical.choose (h_perZ z hz)
      else (fun _ => z)
    have h_Icc_T_sub : Set.Icc (0 : ℝ) T ⊆ Set.Icc (0 : ℝ) ((N : ℝ) * δ') :=
      fun t ht => ⟨ht.1, le_trans ht.2 (le_of_eq hNδ'_eq.symm)⟩
    have h_dw_on_big :
        ∀ z ∈ Metric.closedBall z₀ ((a : ℝ) / 2),
          ∀ t ∈ Set.Icc (0 : ℝ) ((N : ℝ) * δ'),
            HasDerivWithinAt (fun s => (γ_func z s).1) (γ_func z t).2
              (Set.Icc (0 : ℝ) ((N : ℝ) * δ')) t ∧
            HasDerivWithinAt (fun s => (γ_func z s).2)
              (-(convolveFunctionMeasure gradW (ρ t) (γ_func z t).1))
              (Set.Icc (0 : ℝ) ((N : ℝ) * δ')) t := by
      intro z hz t ht
      have h_func_eq : γ_func z = Classical.choose (h_perZ z hz) := by
        simp only [γ_func, dif_pos hz]
      have h_ode := (Classical.choose_spec (h_perZ z hz)).2
      have h_pos_dw := (h_ode t ht).1
      have h_vel_dw := (h_ode t ht).2
      have h_eq_fun_pos : (fun s => (γ_func z s).1)
          = (fun s => ((Classical.choose (h_perZ z hz)) s).1) := by
        funext s; rw [h_func_eq]
      have h_eq_fun_vel : (fun s => (γ_func z s).2)
          = (fun s => ((Classical.choose (h_perZ z hz)) s).2) := by
        funext s; rw [h_func_eq]
      have h_eq_pt_vel : (γ_func z t).2 = (Classical.choose (h_perZ z hz) t).2 := by
        rw [h_func_eq]
      have h_eq_pt_pos : (γ_func z t).1 = (Classical.choose (h_perZ z hz) t).1 := by
        rw [h_func_eq]
      refine ⟨?_, ?_⟩
      · rw [h_eq_fun_pos, h_eq_pt_vel]; exact h_pos_dw
      · rw [h_eq_fun_vel, h_eq_pt_pos]; exact h_vel_dw
    refine ⟨fun t z => (γ_func z t).1, fun t z => (γ_func z t).2,
           ⟨?_, ?_, ?_⟩, ?_⟩
    · intro z hz
      have h_init : Classical.choose (h_perZ z hz) 0 = z :=
        (Classical.choose_spec (h_perZ z hz)).1
      have h_func_eq : γ_func z = Classical.choose (h_perZ z hz) := by
        simp only [γ_func, dif_pos hz]
      refine ⟨?_, ?_⟩
      · change (γ_func z 0).1 = z.1
        rw [h_func_eq, h_init]
      · change (γ_func z 0).2 = z.2
        rw [h_func_eq, h_init]
    · intro t ht z hz
      have h_t_in : t ∈ Set.Icc (0 : ℝ) ((N : ℝ) * δ') := by
        refine ⟨le_of_lt ht.1, le_trans (le_of_lt ht.2) (le_of_eq hNδ'_eq.symm)⟩
      have hT_lt_N : t < (N : ℝ) * δ' := lt_of_lt_of_le ht.2 (le_of_eq hNδ'_eq.symm)
      have h_icc_nhds : Set.Icc (0 : ℝ) ((N : ℝ) * δ') ∈ nhds t :=
        Icc_mem_nhds ht.1 hT_lt_N
      exact ((h_dw_on_big z hz t h_t_in).1).hasDerivAt h_icc_nhds
    · intro t ht z hz
      have h_t_in : t ∈ Set.Icc (0 : ℝ) ((N : ℝ) * δ') := by
        refine ⟨le_of_lt ht.1, le_trans (le_of_lt ht.2) (le_of_eq hNδ'_eq.symm)⟩
      have hT_lt_N : t < (N : ℝ) * δ' := lt_of_lt_of_le ht.2 (le_of_eq hNδ'_eq.symm)
      have h_icc_nhds : Set.Icc (0 : ℝ) ((N : ℝ) * δ') ∈ nhds t :=
        Icc_mem_nhds ht.1 hT_lt_N
      exact ((h_dw_on_big z hz t h_t_in).2).hasDerivAt h_icc_nhds
    · intro z hz t ht
      have h_t_in_big : t ∈ Set.Icc (0 : ℝ) ((N : ℝ) * δ') :=
        h_Icc_T_sub ht
      obtain ⟨h_pos_big, h_vel_big⟩ := h_dw_on_big z hz t h_t_in_big
      exact ⟨h_pos_big.mono h_Icc_T_sub, h_vel_big.mono h_Icc_T_sub⟩

/-- **Two-window** characteristic-flow existence.

A flow on `Ioo 0 (2δ)` for some `δ > 0` and initial conditions in
`closedBall z₀ (a/2)`.  Produces a strictly longer window than
`exists_vlasov_characteristicFlow_local` (which gave `Ioo 0 δ` with
the larger `δ := (a/2)/(L_pl + 1)`); here we tighten the contraction
constraint to `L_pl · (2δ) ≤ a/2`, yielding the smaller
`δ := (a/2)/(2·(L_pl + 1))` but covering a `2δ`-long interval.

**Implementation note.**  This is a single Picard call (the vendored
`_confined` wrapper) with
`tmax = 2δ`, not a literal "two-window stitch" via uniqueness on
overlapping windows.  Mathematically the two are equivalent: a
single Picard with an extended `tmax` and tightened `δ` recovers the
same set of solutions that a two-window stitch would produce.  The
genuine two-window stitch (per-z second Picard at varying centers
glued via `ODE_solution_unique`) becomes essential only when the
single-Picard contraction cannot be satisfied — i.e., when the total
time window needed exceeds the asymptotic threshold `≈ 1/2` regardless
of `a`.  For the upcoming N-window induction follow-up, this single-
Picard extension is iterated, with each iteration using a per-z
center from the previous window's endpoint. -/
theorem exists_vlasov_characteristicFlow_twoWindow
    {d : ℕ}
    (W : PhysSpace d → ℝ)
    (gradW : PhysSpace d → PhysSpace d)
    (_hgradW : ∀ x, gradW x = gradient W x)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d))
    [∀ t, IsProbabilityMeasure (ρ t)]
    (h_int : ∀ t (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ t))
    (hρ_cont : ∀ x : PhysSpace d,
      Continuous (fun t => convolveFunctionMeasure gradW (ρ t) x))
    (z₀ : PhaseSpace d) (a : NNReal) (ha : 0 < a)
    (M : NNReal)
    (hbound : ∀ t ∈ Set.Icc (0 : ℝ) (1 : ℝ),
              ∀ x ∈ Metric.closedBall z₀.1 (3 * (a : ℝ) / 2),
              ‖convolveFunctionMeasure gradW (ρ t) x‖ ≤ M) :
    ∃ (δ : ℝ) (_ : 0 < δ) (charX charV : ℝ → PhaseSpace d → PhysSpace d),
      IsCharacteristicFlowOn gradW ρ charX charV
        (Set.Ioo 0 (2 * δ)) (Metric.closedBall z₀ ((a : ℝ) / 2)) := by
  classical
  -- IsPicardLindelof parameter choices.  Same K_pl, r_pl, L_pl as `_local`;
  -- only the time-step δ is halved to fit the 2δ contraction.
  set K_pl : NNReal := max 1 L with hK_pl_def
  set r_pl : NNReal := a / 2 with hr_pl_def
  set L_pl : NNReal := ‖z₀.2‖₊ + a + M with hL_pl_def
  -- δ chosen so the doubled window 2δ still satisfies L_pl · (2δ) ≤ a/2.
  set δ : ℝ := min (1 / 2) ((a : ℝ) / 2 / (2 * ((L_pl : ℝ) + 1))) with hδ_def
  have ha_real : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have h_denom_pos : (0 : ℝ) < 2 * ((L_pl : ℝ) + 1) := by positivity
  have h_ratio_pos : (0 : ℝ) < (a : ℝ) / 2 / (2 * ((L_pl : ℝ) + 1)) := by positivity
  have hδ_pos : (0 : ℝ) < δ := lt_min (by norm_num) h_ratio_pos
  have hδ_le_half : δ ≤ 1 / 2 := min_le_left _ _
  have hδ_le_ratio : δ ≤ (a : ℝ) / 2 / (2 * ((L_pl : ℝ) + 1)) := min_le_right _ _
  have h_2δ_pos : (0 : ℝ) < 2 * δ := by linarith
  have h_2δ_le_one : 2 * δ ≤ 1 := by linarith
  -- t₀ ∈ Icc 0 (2δ).
  let t₀ : Set.Icc (0 : ℝ) (2 * δ) :=
    ⟨0, Set.mem_Icc.mpr ⟨le_refl 0, le_of_lt h_2δ_pos⟩⟩
  -- Assemble IsPicardLindelof on time window [0, 2δ].
  have hpl : IsPicardLindelof (vlasovVectorField gradW ρ) t₀ z₀ a r_pl L_pl K_pl := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro t _
      exact (vlasovVectorField_lipschitzWith gradW L hL ρ h_int t).lipschitzOnWith
    · intro x _
      apply Continuous.continuousOn
      simp only [vlasovVectorField]
      exact Continuous.prodMk continuous_const (hρ_cont x.1).neg
    · -- norm_le — verbatim from `_local` (uses hbound on Icc 0 1, ball 3a/2).
      intro t ht x hx
      have h_norm_field := vlasovVectorField_norm_le gradW ρ t x
      have hdist_le : dist x z₀ ≤ (a : ℝ) := hx
      have hdist_le_norm : ‖x - z₀‖ ≤ (a : ℝ) := by rwa [dist_eq_norm] at hdist_le
      have h_x2_proj : ‖x.2 - z₀.2‖ ≤ ‖x - z₀‖ := by
        rw [Prod.norm_def]; exact le_max_right _ _
      have h_x2_bound : ‖x.2‖ ≤ ‖z₀.2‖ + (a : ℝ) := by
        have h1 : ‖x.2‖ = ‖(x.2 - z₀.2) + z₀.2‖ := by rw [sub_add_cancel]
        have h2 : ‖(x.2 - z₀.2) + z₀.2‖ ≤ ‖x.2 - z₀.2‖ + ‖z₀.2‖ := norm_add_le _ _
        linarith [h_x2_proj, hdist_le_norm]
      have h_x1_proj : dist x.1 z₀.1 ≤ dist x z₀ := by
        simp only [Prod.dist_eq]; exact le_max_left _ _
      have h_x1_ball : x.1 ∈ Metric.closedBall z₀.1 (3 * (a : ℝ) / 2) := by
        have hx1d : dist x.1 z₀.1 ≤ (a : ℝ) := le_trans h_x1_proj hdist_le
        have : dist x.1 z₀.1 ≤ 3 * (a : ℝ) / 2 := by
          have ha_nn : (0 : ℝ) ≤ (a : ℝ) := le_of_lt ha_real
          linarith
        exact this
      have h_t_Icc : t ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨ht.1, le_trans ht.2 h_2δ_le_one⟩
      have h_force_bound : ‖convolveFunctionMeasure gradW (ρ t) x.1‖ ≤ (M : ℝ) :=
        hbound t h_t_Icc x.1 h_x1_ball
      have h_Lpl_eq : (L_pl : ℝ) = ‖z₀.2‖ + (a : ℝ) + (M : ℝ) := by
        simp [hL_pl_def, NNReal.coe_add, coe_nnnorm]
      calc ‖vlasovVectorField gradW ρ t x‖
          ≤ max ‖x.2‖ ‖convolveFunctionMeasure gradW (ρ t) x.1‖ := h_norm_field
        _ ≤ (L_pl : ℝ) := by
            rw [h_Lpl_eq]
            apply max_le
            · linarith [NNReal.coe_nonneg M]
            · linarith [norm_nonneg z₀.2, NNReal.coe_nonneg a]
    · -- mul_max_le: L_pl · (2δ) ≤ a − a/2 = a/2.  Tighter constraint than `_local`.
      show (L_pl : ℝ) * max (2 * δ - (t₀ : ℝ)) ((t₀ : ℝ) - 0) ≤ (a : ℝ) - (r_pl : ℝ)
      have ht₀_eq : (t₀ : ℝ) = 0 := rfl
      simp only [ht₀_eq, sub_zero, sub_self, max_eq_left (le_of_lt h_2δ_pos)]
      have h_a_minus_r : (a : ℝ) - (r_pl : ℝ) = (a : ℝ) / 2 := by
        simp [hr_pl_def, NNReal.coe_div]; ring
      rw [h_a_minus_r]
      have h_Lpl_nn : (0 : ℝ) ≤ (L_pl : ℝ) := L_pl.coe_nonneg
      have h_a_nn : (0 : ℝ) ≤ (a : ℝ) / 2 := by linarith [ha_real]
      have h_step : (L_pl : ℝ) * (2 * δ) ≤ (L_pl : ℝ) *
          (2 * ((a : ℝ) / 2 / (2 * ((L_pl : ℝ) + 1)))) := by
        apply mul_le_mul_of_nonneg_left _ h_Lpl_nn
        linarith [hδ_le_ratio]
      have h_simp : (L_pl : ℝ) *
          (2 * ((a : ℝ) / 2 / (2 * ((L_pl : ℝ) + 1))))
          = (L_pl : ℝ) / ((L_pl : ℝ) + 1) * ((a : ℝ) / 2) := by
        field_simp
      have h_frac_le : (L_pl : ℝ) / ((L_pl : ℝ) + 1) ≤ 1 := by
        have h_pos : (0 : ℝ) < (L_pl : ℝ) + 1 := by linarith
        rw [div_le_one h_pos]; linarith
      have h_bound : (L_pl : ℝ) / ((L_pl : ℝ) + 1) * ((a : ℝ) / 2) ≤ (a : ℝ) / 2 := by
        calc (L_pl : ℝ) / ((L_pl : ℝ) + 1) * ((a : ℝ) / 2)
            ≤ 1 * ((a : ℝ) / 2) :=
              mul_le_mul_of_nonneg_right h_frac_le h_a_nn
          _ = (a : ℝ) / 2 := one_mul _
      linarith [h_step, h_simp ▸ h_step, h_bound]
  -- Invoke headline Picard-Lindelöf on the doubled window.
  obtain ⟨α, hα⟩ := hpl.exists_forall_mem_closedBall_eq_forall_mem_Icc_hasDerivWithinAt_confined
  -- Define charX, charV by projection.
  refine ⟨δ, hδ_pos, fun t z => (α z t).1, fun t z => (α z t).2, ?_, ?_, ?_⟩
  · -- Initial condition.
    intro z hz
    have hz_in_r : z ∈ Metric.closedBall z₀ (r_pl : ℝ) := by
      have hreq : (r_pl : ℝ) = (a : ℝ) / 2 := by simp [hr_pl_def, NNReal.coe_div]
      rw [Metric.mem_closedBall] at hz ⊢
      rw [hreq]; exact hz
    have h_init : α z (t₀ : ℝ) = z := (hα z hz_in_r).1
    have ht₀_eq : (t₀ : ℝ) = 0 := rfl
    rw [ht₀_eq] at h_init
    refine ⟨?_, ?_⟩
    · change (α z 0).1 = z.1; rw [h_init]
    · change (α z 0).2 = z.2; rw [h_init]
  · -- Position ODE on Ioo 0 (2δ).
    intro t ht z hz
    have hz_in_r : z ∈ Metric.closedBall z₀ (r_pl : ℝ) := by
      have hreq : (r_pl : ℝ) = (a : ℝ) / 2 := by simp [hr_pl_def, NNReal.coe_div]
      rw [Metric.mem_closedBall] at hz ⊢; rw [hreq]; exact hz
    have h_t_Icc : t ∈ Set.Icc (0 : ℝ) (2 * δ) := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    have h_dw := (hα z hz_in_r).2.1 t h_t_Icc
    have h_icc_nhds : Set.Icc (0 : ℝ) (2 * δ) ∈ nhds t := Icc_mem_nhds ht.1 ht.2
    have h_d : HasDerivAt (α z) (vlasovVectorField gradW ρ t (α z t)) t :=
      h_dw.hasDerivAt h_icc_nhds
    have h_proj : HasDerivAt (fun s => (α z s).1)
        (vlasovVectorField gradW ρ t (α z t)).1 t :=
      (hasFDerivAt_fst (E := PhysSpace d) (F := PhysSpace d)).comp_hasDerivAt t h_d
    simpa [vlasovVectorField] using h_proj
  · -- Velocity ODE on Ioo 0 (2δ).
    intro t ht z hz
    have hz_in_r : z ∈ Metric.closedBall z₀ (r_pl : ℝ) := by
      have hreq : (r_pl : ℝ) = (a : ℝ) / 2 := by simp [hr_pl_def, NNReal.coe_div]
      rw [Metric.mem_closedBall] at hz ⊢; rw [hreq]; exact hz
    have h_t_Icc : t ∈ Set.Icc (0 : ℝ) (2 * δ) := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    have h_dw := (hα z hz_in_r).2.1 t h_t_Icc
    have h_icc_nhds : Set.Icc (0 : ℝ) (2 * δ) ∈ nhds t := Icc_mem_nhds ht.1 ht.2
    have h_d : HasDerivAt (α z) (vlasovVectorField gradW ρ t (α z t)) t :=
      h_dw.hasDerivAt h_icc_nhds
    have h_proj : HasDerivAt (fun s => (α z s).2)
        (vlasovVectorField gradW ρ t (α z t)).2 t :=
      (hasFDerivAt_snd (E := PhysSpace d) (F := PhysSpace d)).comp_hasDerivAt t h_d
    simpa [vlasovVectorField] using h_proj


/-! ## Lagrangian → Eulerian: pushforward solves weak Vlasov

The pushforward `vlasovSolutionViaPushforward charX charV f₀` satisfies
`IsVlasovSolution`.  This connects the ODE side (`IsCharacteristicFlow`,
pointwise `HasDerivAt`) to the PDE side (`IsVlasovSolution`,
`WeakEvolutionEq` distributional formulation), closing the Lagrangian-
Eulerian loop that Mathlib does not provide.

**Decomposition.**  Four named helpers, used as black boxes by the wrapper:

  * **SC.1** `vlasov_pushforward_integral_eq_compose` — change of
    variables: `∫ φ d(map flow_s f₀) = ∫ (φ ∘ flow_s) df₀`.  Direct
    `integral_map`.
  * **SC.2** `vlasov_traj_chain_rule` — pointwise chain rule:
    `HasDerivAt (s ↦ φ (charX s z, charV s z)) [formula] t`, using
    `hflow`'s ODE pointwise `HasDerivAt`s and the chain rule on `φ`.
  * **SC.3** `vlasov_pushforward_hasDerivAt_under_integral` —
    differentiation-under-integral via
    `hasDerivAt_integral_of_dominated_loc_of_lip`.  Requires a
    dominated-integrable Lipschitz bound on `s ↦ φ ∘ flow_s` uniform
    in `z`; this is the diff-under-integral technical heart.
  * **SC.4** `vlasov_rhs_pushforward_back` — push the chain-rule RHS
    back through `integral_map` to match `WeakEvolutionEq`'s shape.
    Symmetric to SC.1.

The wrapper composes them: SC.1 (rewrite LHS) → SC.3 (diff-under-integral,
consuming SC.2 pointwise) → SC.4 (rewrite RHS), together with the
AE-strong-measurability of the dot-product integrand (continuity threading
via smoothness of `φ` and Lipschitz of `gradW`). -/

/-- **SC.1: integral change-of-variables for the Vlasov pushforward.**
Direct application of `integral_map`. -/
lemma vlasov_pushforward_integral_eq_compose
    {d : ℕ}
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d))
    (s : ℝ)
    (h_meas : AEMeasurable (fun z : PhaseSpace d => (charX s z, charV s z)) f₀)
    (φ : PhaseSpace d → ℝ)
    (hφ_aesm : AEStronglyMeasurable φ
                  (vlasovSolutionViaPushforward charX charV f₀ s)) :
    ∫ z, φ z ∂(vlasovSolutionViaPushforward charX charV f₀ s) =
      ∫ z, φ (charX s z, charV s z) ∂f₀ := by
  unfold vlasovSolutionViaPushforward
  exact integral_map h_meas hφ_aesm

/-- **SC.2: pointwise chain rule along the characteristic trajectory.**

For fixed `t` and fixed `z`, the curve `s ↦ φ (charX s z, charV s z)`
has derivative
`⟨charV t z, gradXφ (charX t z, charV t z)⟩
 − ⟨(∇W ∗ ρ_t)(charX t z), gradVφ (charX t z, charV t z)⟩`
at `t`.  Proof: chain rule on `φ ∘ (charX · z, charV · z)`, using
`hflow`'s pointwise `HasDerivAt`s and the gradient formula for `φ`'s
directional derivative. -/
lemma vlasov_traj_chain_rule
    {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (ρ : ℝ → Measure (PhysSpace d))
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (φ : PhaseSpace d → ℝ)
    (hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ)
    (gradXφ gradVφ : PhaseSpace d → PhysSpace d)
    (hgradXφ : ∀ z, gradXφ z = gradient (fun x => φ (x, z.2)) z.1)
    (hgradVφ : ∀ z, gradVφ z = gradient (fun v => φ (z.1, v)) z.2)
    (hX_deriv : ∀ t z, HasDerivAt (fun s => charX s z) (charV t z) t)
    (hV_deriv : ∀ t z, HasDerivAt (fun s => charV s z)
        (-(convolveFunctionMeasure gradW (ρ t) (charX t z))) t)
    (t : ℝ) (z : PhaseSpace d) :
    HasDerivAt (fun s => φ (charX s z, charV s z))
      (@inner ℝ (PhysSpace d) _ (charV t z) (gradXφ (charX t z, charV t z))
       - @inner ℝ (PhysSpace d) _
          (convolveFunctionMeasure gradW (ρ t) (charX t z))
          (gradVφ (charX t z, charV t z))) t := by
  -- Strategy: (a) Joint pair has HasDerivAt with derivative
  -- `(charV t z, -(∇W∗ρ_t)(charX t z))`.
  -- (b) `φ` is `ContDiff` so has an FDeriv at the image point.
  -- (c) Chain rule (`HasFDerivAt.comp_hasDerivAt`) gives HasDerivAt of
  -- the composite, with derivative `fderiv φ (flow_t z) (charV t z, -(∇W∗ρ_t)(charX t z))`.
  -- (d) The product fderiv splits via the gradient formula:
  --     `fderiv φ (x,v) (a,b) = ⟨gradXφ (x,v), a⟩ + ⟨gradVφ (x,v), b⟩`.
  -- (e) Substituting `(a,b) := (charV t z, -(∇W∗ρ_t)(charX t z))` and using
  --     bilinearity of inner product with the negation gives the claimed formula.
  --
  -- Step (a): joint pair HasDerivAt
  have hpair : HasDerivAt (fun s => (charX s z, charV s z))
      (charV t z, -(convolveFunctionMeasure gradW (ρ t) (charX t z))) t :=
    (hX_deriv t z).prodMk (hV_deriv t z)
  -- Step (b): φ has FDeriv at the image point
  have hFDeriv : HasFDerivAt φ (fderiv ℝ φ (charX t z, charV t z)) (charX t z, charV t z) :=
    (hφ_smooth.differentiable (by simp) _).hasFDerivAt
  -- Step (c): chain rule
  have hchain : HasDerivAt (fun s => φ (charX s z, charV s z))
      ((fderiv ℝ φ (charX t z, charV t z))
        (charV t z, -(convolveFunctionMeasure gradW (ρ t) (charX t z)))) t :=
    hFDeriv.comp_hasDerivAt t hpair
  -- Step (d): compute the value equality
  have hval : (fderiv ℝ φ (charX t z, charV t z))
      (charV t z, -(convolveFunctionMeasure gradW (ρ t) (charX t z))) =
      @inner ℝ (PhysSpace d) _ (charV t z) (gradXφ (charX t z, charV t z))
       - @inner ℝ (PhysSpace d) _
          (convolveFunctionMeasure gradW (ρ t) (charX t z))
          (gradVφ (charX t z, charV t z)) := by
    -- Set up partial derivative identities (same pattern as h_integrand_aesm)
    set z₀ := (charX t z, charV t z)
    have hdiffφ : DifferentiableAt ℝ φ z₀ :=
      hφ_smooth.differentiable (by simp) z₀
    have hfderiv_X : fderiv ℝ (fun x => φ (x, z₀.2)) z₀.1 =
        (fderiv ℝ φ z₀).comp (ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d)) := by
      have h1 : HasFDerivAt φ (fderiv ℝ φ z₀) z₀ := hdiffφ.hasFDerivAt
      have h2 : HasFDerivAt (fun x : PhysSpace d => (x, z₀.2))
          (ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d)) z₀.1 :=
        hasFDerivAt_prodMk_left z₀.1 z₀.2
      exact (h1.comp z₀.1 h2).fderiv
    have hfderiv_V : fderiv ℝ (fun v => φ (z₀.1, v)) z₀.2 =
        (fderiv ℝ φ z₀).comp (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d)) := by
      have h1 : HasFDerivAt φ (fderiv ℝ φ z₀) z₀ := hdiffφ.hasFDerivAt
      have h2 : HasFDerivAt (fun v : PhysSpace d => (z₀.1, v))
          (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d)) z₀.2 :=
        hasFDerivAt_prodMk_right z₀.1 z₀.2
      exact (h1.comp z₀.2 h2).fderiv
    -- Decompose fderiv φ z₀ applied to (a, b) via inl/inr
    set F := fderiv ℝ φ z₀
    set a := charV t z
    set b := -(convolveFunctionMeasure gradW (ρ t) (charX t z))
    have hdecomp : F (a, b) = F (ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d) a) +
        F (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d) b) := by
      rw [ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply]
      simp [← F.map_add]
    -- Differentiability of partial functions
    have hdiffX : DifferentiableAt ℝ (fun x => φ (x, z₀.2)) z₀.1 :=
      hdiffφ.comp z₀.1 (differentiableAt_id.prodMk (differentiableAt_const z₀.2))
    have hdiffV : DifferentiableAt ℝ (fun v => φ (z₀.1, v)) z₀.2 :=
      hdiffφ.comp z₀.2 ((differentiableAt_const z₀.1).prodMk differentiableAt_id)
    -- The two partial gradient inner products
    have hX_inner : (fderiv ℝ φ z₀) (ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d) a) =
        @inner ℝ (PhysSpace d) _ a (gradXφ z₀) := by
      have hstep : (fderiv ℝ φ z₀) (ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d) a) =
          fderiv ℝ (fun x => φ (x, z₀.2)) z₀.1 a := by rw [hfderiv_X]; rfl
      rw [hstep, ← inner_gradient_left, ← hgradXφ z₀, real_inner_comm]
    have hV_inner : (fderiv ℝ φ z₀) (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d) b) =
        @inner ℝ (PhysSpace d) _ b (gradVφ z₀) := by
      have hstep : (fderiv ℝ φ z₀) (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d) b) =
          fderiv ℝ (fun v => φ (z₀.1, v)) z₀.2 b := by rw [hfderiv_V]; rfl
      rw [hstep, ← inner_gradient_left, ← hgradVφ z₀, real_inner_comm]
    rw [hdecomp, hX_inner, hV_inner, show b = -(convolveFunctionMeasure gradW (ρ t) (charX t z))
        from rfl, inner_neg_left]
    ring
  rwa [hval] at hchain

/-- **`_at` variant of SC.2: pointwise chain rule at a specific `(t, z)`**.

Mirror of `vlasov_traj_chain_rule` (just above), generalized to take the
flow's HasDerivAt hypotheses at the specific `(t, z)` of interest rather
than universally `∀ t z`.  This is the form needed by the `_On` PDE
transport: the flow construction produces `IsCharacteristicFlowOn
... (Ioo 0 T) Set.univ` which gives HasDerivAt only at `t ∈ Ioo 0 T`, so
the universal-`t` form can't be supplied.

This `_at` variant is the foundation; downstream `_on` variants of the
SC.5-SC.8 helpers and the `vlasov_pushforward_hasDerivAt_under_integral`
consumer all compose against this one.

**Proof body**: identical to `vlasov_traj_chain_rule`'s body modulo the
hypothesis-naming.  The original uses `hX_deriv t z`, `hV_deriv t z`
exactly once each (at the `prodMk` step); we replace these with
`hX_deriv_at`, `hV_deriv_at` directly.  All other steps are
specific-`(t, z)` already. -/
lemma vlasov_traj_chain_rule_at
    {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (ρ : ℝ → Measure (PhysSpace d))
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (φ : PhaseSpace d → ℝ)
    (hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ)
    (gradXφ gradVφ : PhaseSpace d → PhysSpace d)
    (hgradXφ : ∀ z, gradXφ z = gradient (fun x => φ (x, z.2)) z.1)
    (hgradVφ : ∀ z, gradVφ z = gradient (fun v => φ (z.1, v)) z.2)
    (t : ℝ) (z : PhaseSpace d)
    (hX_deriv_at : HasDerivAt (fun s => charX s z) (charV t z) t)
    (hV_deriv_at : HasDerivAt (fun s => charV s z)
        (-(convolveFunctionMeasure gradW (ρ t) (charX t z))) t) :
    HasDerivAt (fun s => φ (charX s z, charV s z))
      (@inner ℝ (PhysSpace d) _ (charV t z) (gradXφ (charX t z, charV t z))
       - @inner ℝ (PhysSpace d) _
          (convolveFunctionMeasure gradW (ρ t) (charX t z))
          (gradVφ (charX t z, charV t z))) t := by
  -- Step (a): joint pair HasDerivAt — uses hX_deriv_at, hV_deriv_at directly.
  have hpair : HasDerivAt (fun s => (charX s z, charV s z))
      (charV t z, -(convolveFunctionMeasure gradW (ρ t) (charX t z))) t :=
    hX_deriv_at.prodMk hV_deriv_at
  -- Step (b): φ has FDeriv at the image point.
  have hFDeriv : HasFDerivAt φ (fderiv ℝ φ (charX t z, charV t z)) (charX t z, charV t z) :=
    (hφ_smooth.differentiable (by simp) _).hasFDerivAt
  -- Step (c): chain rule.
  have hchain : HasDerivAt (fun s => φ (charX s z, charV s z))
      ((fderiv ℝ φ (charX t z, charV t z))
        (charV t z, -(convolveFunctionMeasure gradW (ρ t) (charX t z)))) t :=
    hFDeriv.comp_hasDerivAt t hpair
  -- Step (d): compute the value equality (identical to original).
  have hval : (fderiv ℝ φ (charX t z, charV t z))
      (charV t z, -(convolveFunctionMeasure gradW (ρ t) (charX t z))) =
      @inner ℝ (PhysSpace d) _ (charV t z) (gradXφ (charX t z, charV t z))
       - @inner ℝ (PhysSpace d) _
          (convolveFunctionMeasure gradW (ρ t) (charX t z))
          (gradVφ (charX t z, charV t z)) := by
    set z₀ := (charX t z, charV t z)
    have hdiffφ : DifferentiableAt ℝ φ z₀ :=
      hφ_smooth.differentiable (by simp) z₀
    have hfderiv_X : fderiv ℝ (fun x => φ (x, z₀.2)) z₀.1 =
        (fderiv ℝ φ z₀).comp (ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d)) := by
      have h1 : HasFDerivAt φ (fderiv ℝ φ z₀) z₀ := hdiffφ.hasFDerivAt
      have h2 : HasFDerivAt (fun x : PhysSpace d => (x, z₀.2))
          (ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d)) z₀.1 :=
        hasFDerivAt_prodMk_left z₀.1 z₀.2
      exact (h1.comp z₀.1 h2).fderiv
    have hfderiv_V : fderiv ℝ (fun v => φ (z₀.1, v)) z₀.2 =
        (fderiv ℝ φ z₀).comp (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d)) := by
      have h1 : HasFDerivAt φ (fderiv ℝ φ z₀) z₀ := hdiffφ.hasFDerivAt
      have h2 : HasFDerivAt (fun v : PhysSpace d => (z₀.1, v))
          (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d)) z₀.2 :=
        hasFDerivAt_prodMk_right z₀.1 z₀.2
      exact (h1.comp z₀.2 h2).fderiv
    set F := fderiv ℝ φ z₀
    set a := charV t z
    set b := -(convolveFunctionMeasure gradW (ρ t) (charX t z))
    have hdecomp : F (a, b) = F (ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d) a) +
        F (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d) b) := by
      rw [ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply]
      simp [← F.map_add]
    have hdiffX : DifferentiableAt ℝ (fun x => φ (x, z₀.2)) z₀.1 :=
      hdiffφ.comp z₀.1 (differentiableAt_id.prodMk (differentiableAt_const z₀.2))
    have hdiffV : DifferentiableAt ℝ (fun v => φ (z₀.1, v)) z₀.2 :=
      hdiffφ.comp z₀.2 ((differentiableAt_const z₀.1).prodMk differentiableAt_id)
    have hX_inner : (fderiv ℝ φ z₀) (ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d) a) =
        @inner ℝ (PhysSpace d) _ a (gradXφ z₀) := by
      have hstep : (fderiv ℝ φ z₀) (ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d) a) =
          fderiv ℝ (fun x => φ (x, z₀.2)) z₀.1 a := by rw [hfderiv_X]; rfl
      rw [hstep, ← inner_gradient_left, ← hgradXφ z₀, real_inner_comm]
    have hV_inner : (fderiv ℝ φ z₀) (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d) b) =
        @inner ℝ (PhysSpace d) _ b (gradVφ z₀) := by
      have hstep : (fderiv ℝ φ z₀) (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d) b) =
          fderiv ℝ (fun v => φ (z₀.1, v)) z₀.2 b := by rw [hfderiv_V]; rfl
      rw [hstep, ← inner_gradient_left, ← hgradVφ z₀, real_inner_comm]
    rw [hdecomp, hX_inner, hV_inner, show b = -(convolveFunctionMeasure gradW (ρ t) (charX t z))
        from rfl, inner_neg_left]
    ring
  rwa [hval] at hchain

/-- **Dominated-bundle data for SC.3.**

Packages the four ancillary hypotheses required by Mathlib's
`hasDerivAt_integral_of_dominated_loc_of_lip` (excluding the pointwise
`HasDerivAt` which SC.2 already provides):
  * a neighborhood `nhd ∈ nhds t` on which the dominated Lipschitz bound holds;
  * eventual AE-strong-measurability of `(z ↦ φ ∘ flow_s)` for `s` near `t`;
  * integrability of the integrand at `s = t`;
  * AE-strong-measurability of the pointwise derivative as a function of `z`;
  * a `bound : PhaseSpace d → ℝ` with `Integrable bound f₀` such that, ae-z,
    the curve `s ↦ φ(charX s z, charV s z)` is `Real.nnabs (bound z)`-Lipschitz
    on `nhd`.

The dominated-bound clause is the technical heart: deriving it requires
a uniform-in-`z` bound on the flow speed `(charV s z, V'(s,z))` on the
support of `φ`, which the eventual `vlasovWellPosedness` caller will
produce from Picard-Lindelof local-flow boundedness + `HasCompactSupport φ`. -/
def DiffUnderIntegralData
    {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (ρ : ℝ → Measure (PhysSpace d))
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d))
    (φ : PhaseSpace d → ℝ)
    (gradXφ gradVφ : PhaseSpace d → PhysSpace d)
    (t : ℝ) : Prop :=
  ∃ (nhd : Set ℝ) (bound : PhaseSpace d → ℝ),
    nhd ∈ nhds t ∧
    (∀ᶠ s' in nhds t,
      AEStronglyMeasurable (fun z => φ (charX s' z, charV s' z)) f₀) ∧
    Integrable (fun z => φ (charX t z, charV t z)) f₀ ∧
    AEStronglyMeasurable
      (fun z => @inner ℝ (PhysSpace d) _ (charV t z) (gradXφ (charX t z, charV t z))
                - @inner ℝ (PhysSpace d) _
                    (convolveFunctionMeasure gradW (ρ t) (charX t z))
                    (gradVφ (charX t z, charV t z))) f₀ ∧
    (∀ᵐ z ∂f₀,
      LipschitzOnWith (Real.nnabs (bound z))
        (fun s' => φ (charX s' z, charV s' z)) nhd) ∧
    Integrable bound f₀

/-- **SC.3: differentiation under the integral for the pushforward integral.**

`HasDerivAt (s ↦ ∫ z, φ (charX s z, charV s z) ∂f₀) (∫ z, [pointwise deriv] ∂f₀) t`,
where the pointwise derivative at `t` is the chain-rule formula from SC.2.

Proven by direct application of Mathlib's
`hasDerivAt_integral_of_dominated_loc_of_lip`, given the
`DiffUnderIntegralData` bundle and the pointwise derivative from SC.2.

Taking `h_data : DiffUnderIntegralData ...` as a hypothesis keeps SC.3's
body a one-line Mathlib application; the burden of producing the
dominated-bundle data moves to the caller (discharged from compact support
of `φ` plus Picard regularity). -/
lemma vlasov_pushforward_hasDerivAt_under_integral
    {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (ρ : ℝ → Measure (PhysSpace d))
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d))
    (φ : PhaseSpace d → ℝ)
    (gradXφ gradVφ : PhaseSpace d → PhysSpace d)
    (t : ℝ)
    (h_pointwise : ∀ z, HasDerivAt (fun s => φ (charX s z, charV s z))
      (@inner ℝ (PhysSpace d) _ (charV t z) (gradXφ (charX t z, charV t z))
       - @inner ℝ (PhysSpace d) _
          (convolveFunctionMeasure gradW (ρ t) (charX t z))
          (gradVφ (charX t z, charV t z))) t)
    (h_data : DiffUnderIntegralData gradW ρ charX charV f₀ φ gradXφ gradVφ t) :
    HasDerivAt (fun s => ∫ z, φ (charX s z, charV s z) ∂f₀)
      (∫ z, @inner ℝ (PhysSpace d) _ (charV t z) (gradXφ (charX t z, charV t z))
            - @inner ℝ (PhysSpace d) _
                (convolveFunctionMeasure gradW (ρ t) (charX t z))
                (gradVφ (charX t z, charV t z))
          ∂f₀) t := by
  obtain ⟨nhd, bound, hnhd, hF_meas, hF_int, hF'_meas, h_lipsch, h_bound_int⟩ := h_data
  exact (hasDerivAt_integral_of_dominated_loc_of_lip
    (μ := f₀) (x₀ := t) (bound := bound) (s := nhd)
    (F := fun s' z => φ (charX s' z, charV s' z))
    hnhd hF_meas hF_int hF'_meas
    h_lipsch h_bound_int
    (Filter.Eventually.of_forall h_pointwise)).2

/-- **SC.4: push the chain-rule RHS back through `integral_map`.**

`∫ z, [formula(charX t z, charV t z)] df₀ = ∫ y, [formula(y)] d(map flow_t f₀)`.

Symmetric to SC.1; the same `integral_map` invocation, applied to the
dot-product integrand.  Closes by `integral_map` after establishing AE-
strong-measurability of the integrand. -/
lemma vlasov_rhs_pushforward_back
    {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d))
    (t : ℝ)
    (h_meas : AEMeasurable (fun z : PhaseSpace d => (charX t z, charV t z)) f₀)
    (gradXφ gradVφ : PhaseSpace d → PhysSpace d)
    (h_integrand_aesm : AEStronglyMeasurable
      (fun y : PhaseSpace d =>
        @inner ℝ (PhysSpace d) _ y.2 (gradXφ y)
        - @inner ℝ (PhysSpace d) _
            (convolveFunctionMeasure gradW
              (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t)) y.1)
            (gradVφ y))
      (vlasovSolutionViaPushforward charX charV f₀ t)) :
    ∫ z, @inner ℝ (PhysSpace d) _ (charV t z) (gradXφ (charX t z, charV t z))
         - @inner ℝ (PhysSpace d) _
            (convolveFunctionMeasure gradW
              (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t))
              (charX t z))
            (gradVφ (charX t z, charV t z))
        ∂f₀
      = ∫ y, @inner ℝ (PhysSpace d) _ y.2 (gradXφ y)
             - @inner ℝ (PhysSpace d) _
                (convolveFunctionMeasure gradW
                  (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t)) y.1)
                (gradVφ y)
            ∂(vlasovSolutionViaPushforward charX charV f₀ t) := by
  -- Direct application of integral_map in reverse direction, on the dot-product
  -- integrand.  The integrand at `(charX t z, charV t z)` is precisely the
  -- pre-image of the y-integrand under the pushforward map.
  unfold vlasovSolutionViaPushforward at h_integrand_aesm ⊢
  exact (integral_map h_meas h_integrand_aesm).symm

/-! ## Lagrangian → Eulerian bundle sub-helpers (SC.5 – SC.8)

The `DiffUnderIntegralData` bundle inside the wrapper is decomposed
into four named regularity sub-helpers:

  * **SC.5** `vlasov_compose_flow_aestronglymeas` — eventual
    AE-strong-measurability of `φ ∘ flow_s` near `t`.
  * **SC.6** `vlasov_compose_flow_integrable_at` — integrability of
    `φ ∘ flow_t` against `f₀` (uses `HasCompactSupport φ`).
  * **SC.7** `vlasov_pointwise_deriv_aestronglymeas` — AE-strong-
    measurability of the chain-rule pointwise derivative (same shape
    as the wrapper's `h_integrand_aesm` proof).
  * **SC.8** `vlasov_trajectory_lipschitz_bound` — the dominated
    Lipschitz bound on `s ↦ φ(charX s z, charV s z)` with an
    `f₀`-integrable Lipschitz coefficient, from a uniform velocity bound
    on `nhd × (flow_t)⁻¹(supp φ)`. -/

/-- **SC.5: AE-strong-measurability of `φ ∘ flow_s` for s near t.**

The composition `z ↦ φ (charX s' z, charV s' z)` is AE-strongly-
measurable wrt `f₀` for every `s'`, in particular for `s'` in any
neighborhood of `t`.  Uses continuity of `φ` plus
`h_flow_meas`'s AE-measurability of the flow pair. -/
lemma vlasov_compose_flow_aestronglymeas
    {d : ℕ}
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d))
    (φ : PhaseSpace d → ℝ) (hφ_cont : Continuous φ)
    (h_flow_meas : ∀ s, AEMeasurable
      (fun z : PhaseSpace d => (charX s z, charV s z)) f₀)
    (t : ℝ) :
    ∀ᶠ s' in nhds t, AEStronglyMeasurable
      (fun z => φ (charX s' z, charV s' z)) f₀ := by
  apply Filter.Eventually.of_forall
  intro s'
  exact hφ_cont.comp_aestronglyMeasurable (h_flow_meas s').aestronglyMeasurable

/-- **SC.6: Integrability of `φ ∘ flow_t` against `f₀`.**

`HasCompactSupport φ` + `Continuous φ` give boundedness; combined with
`[IsProbabilityMeasure f₀]` this yields integrability. -/
lemma vlasov_compose_flow_integrable_at
    {d : ℕ}
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (φ : PhaseSpace d → ℝ)
    (hφ_cont : Continuous φ)
    (hφ_compact : HasCompactSupport φ)
    (t : ℝ)
    (h_flow_meas_t : AEMeasurable
      (fun z : PhaseSpace d => (charX t z, charV t z)) f₀) :
    Integrable (fun z => φ (charX t z, charV t z)) f₀ := by
  obtain ⟨C, hC⟩ := hφ_cont.bounded_above_of_compact_support hφ_compact
  exact Integrable.of_bound
    (hφ_cont.comp_aestronglyMeasurable h_flow_meas_t.aestronglyMeasurable)
    C (Filter.Eventually.of_forall (fun z => hC _))

/-- **SC.7: AE-strong-measurability of the pointwise derivative.**

The chain-rule pointwise derivative integrand
`⟨charV t z, gradXφ(flow_t z)⟩ - ⟨convolve_t(charX t z), gradVφ(flow_t z)⟩`
is AE-strongly-measurable wrt `f₀`.  Same continuity argument as the
wrapper's `h_integrand_aesm` proof. -/
lemma vlasov_pointwise_deriv_aestronglymeas
    {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (ρ : ℝ → Measure (PhysSpace d))
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d))
    (φ : PhaseSpace d → ℝ) (hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ)
    (gradXφ gradVφ : PhaseSpace d → PhysSpace d)
    (hgradXφ : ∀ z, gradXφ z = gradient (fun x => φ (x, z.2)) z.1)
    (hgradVφ : ∀ z, gradVφ z = gradient (fun v => φ (z.1, v)) z.2)
    (hconv_cont : ∀ s, Continuous (fun x =>
        convolveFunctionMeasure gradW (ρ s) x))
    (t : ℝ)
    (h_flow_meas_t : AEMeasurable
      (fun z : PhaseSpace d => (charX t z, charV t z)) f₀) :
    AEStronglyMeasurable
      (fun z => @inner ℝ (PhysSpace d) _ (charV t z) (gradXφ (charX t z, charV t z))
                - @inner ℝ (PhysSpace d) _
                    (convolveFunctionMeasure gradW (ρ t) (charX t z))
                    (gradVφ (charX t z, charV t z))) f₀ := by
  -- The integrand factors as g ∘ (fun z => (charX t z, charV t z)), where
  -- g : PhaseSpace d → ℝ is the same continuous function as in the wrapper's
  -- h_integrand_aesm (g y = ⟨y.2, gradXφ y⟩ - ⟨convolve y.1, gradVφ y⟩).
  -- Step 1: establish that gradXφ and gradVφ are continuous (same argument as wrapper).
  have hfderiv_X : ∀ z : PhaseSpace d,
      fderiv ℝ (fun x => φ (x, z.2)) z.1 =
      (fderiv ℝ φ z).comp (ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d)) :=
    fun z => by
      have h1 : HasFDerivAt φ (fderiv ℝ φ z) z :=
        (hφ_smooth.differentiable (by simp) z).hasFDerivAt
      have h2 : HasFDerivAt (fun x : PhysSpace d => (x, z.2))
          (ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d)) z.1 :=
        hasFDerivAt_prodMk_left z.1 z.2
      exact (h1.comp z.1 h2).fderiv
  have heqX : gradXφ = fun z => gradient (fun x => φ (x, z.2)) z.1 := funext hgradXφ
  have hfderiv_V : ∀ z : PhaseSpace d,
      fderiv ℝ (fun v => φ (z.1, v)) z.2 =
      (fderiv ℝ φ z).comp (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d)) :=
    fun z => by
      have h1 : HasFDerivAt φ (fderiv ℝ φ z) z :=
        (hφ_smooth.differentiable (by simp) z).hasFDerivAt
      have h2 : HasFDerivAt (fun v : PhysSpace d => (z.1, v))
          (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d)) z.2 :=
        hasFDerivAt_prodMk_right z.1 z.2
      exact (h1.comp z.2 h2).fderiv
  have heqV : gradVφ = fun z => gradient (fun v => φ (z.1, v)) z.2 := funext hgradVφ
  -- Step 2: show that g : PhaseSpace d → ℝ is continuous.
  have hg_cont : Continuous (fun y : PhaseSpace d =>
      @inner ℝ (PhysSpace d) _ y.2 (gradXφ y)
      - @inner ℝ (PhysSpace d) _
          (convolveFunctionMeasure gradW (ρ t) y.1) (gradVφ y)) := by
    apply Continuous.sub
    · apply Continuous.inner continuous_snd
      simp_rw [heqX, gradient, hfderiv_X]
      exact (InnerProductSpace.toDual ℝ (PhysSpace d)).symm.continuous.comp
        ((ContinuousLinearMap.isBoundedLinearMap_comp_right
          (ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d))).continuous.comp
          (hφ_smooth.continuous_fderiv (by simp)))
    · apply Continuous.inner
      · exact (hconv_cont t).comp continuous_fst
      · simp_rw [heqV, gradient, hfderiv_V]
        exact (InnerProductSpace.toDual ℝ (PhysSpace d)).symm.continuous.comp
          ((ContinuousLinearMap.isBoundedLinearMap_comp_right
            (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d))).continuous.comp
            (hφ_smooth.continuous_fderiv (by simp)))
  -- Step 3: the integrand equals g ∘ flow. Apply Continuous.comp_aestronglyMeasurable.
  exact hg_cont.comp_aestronglyMeasurable h_flow_meas_t.aestronglyMeasurable


/-- **`_lag` variant of SC.8** — `vlasov_trajectory_lipschitz_bound` with the
flow-growth prerequisites supplied as explicit hypotheses, enabling the
dominated Lipschitz bound to be derived via Gronwall on the characteristic
ODE (see `flow_distance_growth_bound` above).  Used by `_lag` variants
of the Lagrangian → Eulerian chain that route through
`IsLagrangianVlasovSolution`. -/
lemma vlasov_trajectory_lipschitz_bound_lag
    {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d))
    [∀ s, IsProbabilityMeasure (ρ s)]
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (hf₀_fm : Integrable (fun z : PhaseSpace d => ‖z‖) f₀)
    (φ : PhaseSpace d → ℝ)
    (hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ)
    (hflow : IsCharacteristicFlow gradW ρ charX charV)
    (_hgradW_cont : Continuous gradW)
    (_hconv_cont : ∀ s, Continuous (fun x =>
        convolveFunctionMeasure gradW (ρ s) x))
    (t : ℝ) (ht_pos : 0 < t)
    (M_ρ : ℝ) (hM_ρ_nn : 0 ≤ M_ρ)
    (hM_ρ : ∀ s ∈ Set.Icc 0 (t + 1), ∫ y, ‖y‖ ∂(ρ s) ≤ M_ρ)
    (h_y_int : ∀ s ∈ Set.Icc 0 (t + 1),
      Integrable (fun y : PhysSpace d => ‖y‖) (ρ s))
    (h_int : ∀ s (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ s)) :
    ∃ (nhd : Set ℝ) (bound : PhaseSpace d → ℝ),
      nhd ∈ nhds t ∧
      (∀ᵐ z ∂f₀, LipschitzOnWith (Real.nnabs (bound z))
        (fun s' => φ (charX s' z, charV s' z)) nhd) ∧
      Integrable bound f₀ := by
  obtain ⟨hflow_init, hflow_x, hflow_v⟩ := hflow
  -- Step 1: Get Gronwall growth bound C_T on [0, t+1]
  obtain ⟨C_T, hC_T_nn, hC_T⟩ := flow_distance_growth_bound gradW L hL ρ charX charV
      ⟨hflow_init, hflow_x, hflow_v⟩ (t + 1) (by linarith) M_ρ hM_ρ_nn hM_ρ h_y_int h_int
  -- Step 2: Bound ‖fderiv ℝ φ‖ uniformly (compact support + continuous fderiv)
  have hφ_diff : Differentiable ℝ φ := hφ_smooth.differentiable (by norm_num)
  have hfderiv_cont : Continuous (fderiv ℝ φ) :=
    hφ_smooth.continuous_fderiv (by norm_num)
  have hfderiv_compact : HasCompactSupport (fderiv ℝ φ) :=
    HasCompactSupport.fderiv (𝕜 := ℝ) hφ_compact
  obtain ⟨M_φ, hM_φ⟩ := hfderiv_cont.bounded_above_of_compact_support hfderiv_compact
  have hM_φ_nn : 0 ≤ M_φ :=
    le_trans (norm_nonneg (fderiv ℝ φ (0 : PhaseSpace d))) (hM_φ _)
  -- Gronwall constants: K = 1 + L, ε₀ = ‖gradW 0‖ + L * M_ρ
  set K := 1 + (L : ℝ)
  set ε₀ := ‖gradW 0‖ + (L : ℝ) * M_ρ
  have hK_pos : 0 < K := by positivity
  have hε₀_nn : 0 ≤ ε₀ := by positivity
  -- Convolution bound (same derivation as flow_distance_growth_bound)
  have h_conv_bound : ∀ s ∈ Set.Icc 0 (t + 1), ∀ x : PhysSpace d,
      ‖convolveFunctionMeasure gradW (ρ s) x‖ ≤ ε₀ + (L : ℝ) * ‖x‖ := by
    intro s hs x
    unfold convolveFunctionMeasure
    have h_sub_int : Integrable (fun y => ‖x - y‖) (ρ s) :=
      Integrable.mono' ((integrable_const ‖x‖).add (h_y_int s hs))
        ((aestronglyMeasurable_const (b := x)).sub aestronglyMeasurable_id |>.norm)
        (Filter.Eventually.of_forall fun y => by
          simp only [Real.norm_of_nonneg (norm_nonneg _)]; exact norm_sub_le x y)
    have h_pt : ∀ y : PhysSpace d,
        ‖gradW (x - y)‖ ≤ ‖gradW 0‖ + (L : ℝ) * ‖x - y‖ := by
      intro y
      have hd := hL.dist_le_mul (x - y) 0
      simp only [dist_eq_norm, sub_zero] at hd
      have h_tri : ‖gradW (x - y)‖ ≤ ‖gradW 0‖ + ‖gradW (x - y) - gradW 0‖ := by
        have := norm_add_le (gradW (x - y) - gradW 0) (gradW 0)
        simp only [sub_add_cancel] at this; linarith
      linarith
    have h_bnd_int : Integrable (fun y => ‖gradW 0‖ + (L : ℝ) * ‖x - y‖) (ρ s) :=
      (integrable_const _).add (h_sub_int.const_mul _)
    calc ‖∫ y, gradW (x - y) ∂(ρ s)‖
        ≤ ∫ y, ‖gradW (x - y)‖ ∂(ρ s) := norm_integral_le_integral_norm _
      _ ≤ ∫ y, (‖gradW 0‖ + (L : ℝ) * ‖x - y‖) ∂(ρ s) :=
          integral_mono (h_int s x).norm h_bnd_int (fun y => h_pt y)
      _ = ‖gradW 0‖ + (L : ℝ) * ∫ y, ‖x - y‖ ∂(ρ s) := by
          rw [integral_add (integrable_const _) (h_sub_int.const_mul _)]
          simp [integral_const, measureReal_def, measure_univ, integral_const_mul]
      _ ≤ ε₀ + (L : ℝ) * ‖x‖ := by
          have h_int_le : ∫ y, ‖x - y‖ ∂(ρ s) ≤ ‖x‖ + M_ρ := by
            calc ∫ y, ‖x - y‖ ∂(ρ s)
                ≤ ∫ y, (‖x‖ + ‖y‖) ∂(ρ s) :=
                  integral_mono h_sub_int ((integrable_const _).add (h_y_int s hs))
                    (fun y => norm_sub_le x y)
              _ = ‖x‖ + ∫ y, ‖y‖ ∂(ρ s) := by
                  rw [integral_add (integrable_const _) (h_y_int s hs)]
                  simp [integral_const, measureReal_def, measure_univ]
              _ ≤ ‖x‖ + M_ρ := by linarith [hM_ρ s hs]
          simp only [ε₀]; linarith [mul_le_mul_of_nonneg_left h_int_le (NNReal.coe_nonneg L)]
  -- Step 3: Choose neighborhood nhd = Ioo (t/2) (t + 1/2) ⊆ Icc 0 (t+1)
  refine ⟨Set.Ioo (t / 2) (t + 1 / 2),
    fun z => M_φ * (K * C_T + ε₀) * (‖z‖ + 1), ?_, ?_, ?_⟩
  · -- nhd ∈ nhds t
    exact Ioo_mem_nhds (by linarith) (by linarith)
  · -- LipschitzOnWith for ae-z
    apply Filter.Eventually.of_forall
    intro z
    -- For each z, apply MVT on convex nhd
    -- For each z, prove the derivative bound then apply MVT
    -- Define the derivative value as a function
    let deriv_val : ℝ → PhaseSpace d → ℝ := fun s z =>
      (fderiv ℝ φ (charX s z, charV s z))
        (charV s z, -(convolveFunctionMeasure gradW (ρ s) (charX s z)))
    -- The derivative witness function f' for lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    apply Convex.lipschitzOnWith_of_nnnorm_hasDerivWithin_le (convex_Ioo _ _)
      (f' := fun s => deriv_val s z)
    · -- HasDerivWithinAt for each s ∈ nhd
      intro s hs
      have h_flow_deriv : HasDerivAt (fun s' => (charX s' z, charV s' z))
          (charV s z, -(convolveFunctionMeasure gradW (ρ s) (charX s z))) s :=
        (hflow_x s z).prodMk (hflow_v s z)
      have h_φ_fderiv : HasFDerivAt φ (fderiv ℝ φ (charX s z, charV s z))
          (charX s z, charV s z) :=
        hφ_diff (charX s z, charV s z) |>.hasFDerivAt
      exact (h_φ_fderiv.comp_hasDerivAt s h_flow_deriv).hasDerivWithinAt
    · -- Bound ‖deriv_val s z‖₊ ≤ Real.nnabs (M_φ * (K * C_T + ε₀) * (‖z‖ + 1))
      intro s hs
      rw [← NNReal.coe_le_coe]
      simp only []
      have hs_mem : s ∈ Set.Icc 0 (t + 1) :=
        ⟨le_of_lt (by linarith [hs.1]),
         le_of_lt (by linarith [hs.2])⟩
      have h_flow_bnd : ‖(charX s z, charV s z)‖ ≤ C_T * (‖z‖ + 1) :=
        hC_T s hs_mem z
      have h_x_bnd : ‖charX s z‖ ≤ C_T * (‖z‖ + 1) := by
        have hpn : ‖(charX s z, charV s z)‖ = max ‖charX s z‖ ‖charV s z‖ :=
          Prod.norm_def _
        linarith [le_max_left ‖charX s z‖ ‖charV s z‖, hpn ▸ h_flow_bnd]
      have h_v_bnd2 : ‖charV s z‖ ≤ C_T * (‖z‖ + 1) := by
        have hpn : ‖(charX s z, charV s z)‖ = max ‖charX s z‖ ‖charV s z‖ :=
          Prod.norm_def _
        linarith [le_max_right ‖charX s z‖ ‖charV s z‖, hpn ▸ h_flow_bnd]
      have h_c_bnd : ‖convolveFunctionMeasure gradW (ρ s) (charX s z)‖ ≤
          ε₀ + (L : ℝ) * C_T * (‖z‖ + 1) := by
        have := h_conv_bound s hs_mem (charX s z)
        linarith [mul_le_mul_of_nonneg_left h_x_bnd (NNReal.coe_nonneg L)]
      have h_vel_bnd : ‖(charV s z, -(convolveFunctionMeasure gradW (ρ s) (charX s z)))‖
          ≤ K * C_T * (‖z‖ + 1) + ε₀ := by
        rw [Prod.norm_def]
        simp only [norm_neg]
        have hK1 : (1 : ℝ) ≤ K := by linarith [NNReal.coe_nonneg L]
        have hz1 : (0 : ℝ) ≤ ‖z‖ + 1 := by linarith [norm_nonneg z]
        apply max_le
        · -- ‖charV s z‖ ≤ K * C_T * (‖z‖ + 1) + ε₀
          have h1 : C_T * (‖z‖ + 1) ≤ K * C_T * (‖z‖ + 1) := by
            have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK1 hC_T_nn) hz1
            linarith
          linarith
        · -- ‖conv‖ ≤ K * C_T * (‖z‖ + 1) + ε₀
          have hLK : (L : ℝ) ≤ K := by linarith [NNReal.coe_nonneg L]
          have h2 : (L : ℝ) * C_T * (‖z‖ + 1) ≤ K * C_T * (‖z‖ + 1) := by
            have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hLK hC_T_nn) hz1
            linarith
          linarith
      rw [Real.coe_nnabs, abs_of_nonneg (by positivity)]
      calc ‖deriv_val s z‖
          ≤ ‖fderiv ℝ φ (charX s z, charV s z)‖ *
            ‖(charV s z, -(convolveFunctionMeasure gradW (ρ s) (charX s z)))‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ M_φ * (K * C_T * (‖z‖ + 1) + ε₀) := by
            apply mul_le_mul (hM_φ _) h_vel_bnd (norm_nonneg _) hM_φ_nn
        _ ≤ M_φ * (K * C_T + ε₀) * (‖z‖ + 1) := by
            have hz1 : 1 ≤ ‖z‖ + 1 := by linarith [norm_nonneg z]
            nlinarith [mul_nonneg hM_φ_nn hε₀_nn,
                       mul_nonneg (mul_nonneg hM_φ_nn hε₀_nn)
                         (by linarith [norm_nonneg z] : (0 : ℝ) ≤ ‖z‖),
                       mul_nonneg hM_φ_nn hC_T_nn]
  · -- Integrable bound z
    have h_bound_eq : (fun z : PhaseSpace d => M_φ * (K * C_T + ε₀) * (‖z‖ + 1)) =
        fun z => M_φ * (K * C_T + ε₀) * ‖z‖ + M_φ * (K * C_T + ε₀) := by
      ext z; ring
    rw [h_bound_eq]
    exact (hf₀_fm.const_mul _).add (integrable_const _)

/-- **`_on` variant of SC.8** — `vlasov_trajectory_lipschitz_bound` with
`IsCharacteristicFlowOn ... (Ioo 0 T) Set.univ` instead of universal
`IsCharacteristicFlow`, and with boundary regularity hypotheses
(`h_init`, `h_cont_Icc`, `h_deriv_Ico`) supplied explicitly.  Required by
the `_On` PDE transport (`vlasovSolutionViaPushforward_isVlasovSolutionOn`).

The body transports `vlasov_trajectory_lipschitz_bound_lag`'s argument with
two substitutions:
1. `flow_distance_growth_bound` → `flow_distance_growth_bound_on`, using the
   boundary regularity hypotheses.
2. `(hflow_x s z).prodMk (hflow_v s z)` → `hflow_on.2.1 s ... z ...` for
   `s` in the chosen neighborhood (within `Ioo 0 T`).

The neighborhood `nhd` is chosen to stay within `Ioo 0 T` (where `hflow_on`
is defined), e.g. `Ioo (max 0 (t/2)) (min T (t + 1/2))`. -/
lemma vlasov_trajectory_lipschitz_bound_on
    {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d))
    [∀ s, IsProbabilityMeasure (ρ s)]
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (hf₀_fm : Integrable (fun z : PhaseSpace d => ‖z‖) f₀)
    (φ : PhaseSpace d → ℝ)
    (hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ)
    {T : ℝ} (hT : 0 < T)
    (hflow_on : IsCharacteristicFlowOn gradW ρ charX charV
                                       (Set.Ioo 0 T) Set.univ)
    -- Boundary regularity for `flow_distance_growth_bound_on`.
    (h_init : ∀ z : PhaseSpace d, (charX 0 z, charV 0 z) = z)
    (h_cont_Icc : ∀ z : PhaseSpace d,
      ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc 0 T))
    (h_deriv_Ico : ∀ z : PhaseSpace d, ∀ s ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt (fun s' => (charX s' z, charV s' z))
        (vlasovVectorField gradW ρ s (charX s z, charV s z))
        (Set.Ici s) s)
    (_hgradW_cont : Continuous gradW)
    (_hconv_cont : ∀ s, Continuous (fun x =>
        convolveFunctionMeasure gradW (ρ s) x))
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (M_ρ : ℝ) (hM_ρ_nn : 0 ≤ M_ρ)
    (hM_ρ : ∀ s ∈ Set.Icc 0 T, ∫ y, ‖y‖ ∂(ρ s) ≤ M_ρ)
    (h_y_int : ∀ s ∈ Set.Icc 0 T,
      Integrable (fun y : PhysSpace d => ‖y‖) (ρ s))
    (h_int : ∀ s (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ s)) :
    ∃ (nhd : Set ℝ) (bound : PhaseSpace d → ℝ),
      nhd ∈ nhds t ∧
      (∀ᵐ z ∂f₀, LipschitzOnWith (Real.nnabs (bound z))
        (fun s' => φ (charX s' z, charV s' z)) nhd) ∧
      Integrable bound f₀ := by
  -- Step 1: Get Gronwall growth bound C_T on [0, T].
  obtain ⟨C_T, hC_T_nn, hC_T⟩ := flow_distance_growth_bound_on gradW L hL ρ charX charV
      T (le_of_lt hT) h_init h_cont_Icc h_deriv_Ico M_ρ hM_ρ_nn hM_ρ h_y_int h_int
  -- Step 2: Bound ‖fderiv ℝ φ‖ uniformly (compact support + continuous fderiv).
  have hφ_diff : Differentiable ℝ φ := hφ_smooth.differentiable (by norm_num)
  have hfderiv_cont : Continuous (fderiv ℝ φ) :=
    hφ_smooth.continuous_fderiv (by norm_num)
  have hfderiv_compact : HasCompactSupport (fderiv ℝ φ) :=
    HasCompactSupport.fderiv (𝕜 := ℝ) hφ_compact
  obtain ⟨M_φ, hM_φ⟩ := hfderiv_cont.bounded_above_of_compact_support hfderiv_compact
  have hM_φ_nn : 0 ≤ M_φ :=
    le_trans (norm_nonneg (fderiv ℝ φ (0 : PhaseSpace d))) (hM_φ _)
  -- Gronwall constants: K = 1 + L, ε₀ = ‖gradW 0‖ + L * M_ρ.
  set K := 1 + (L : ℝ)
  set ε₀ := ‖gradW 0‖ + (L : ℝ) * M_ρ
  have hK_pos : 0 < K := by positivity
  have hε₀_nn : 0 ≤ ε₀ := by positivity
  -- Convolution bound on [0, T] (same derivation as `_lag`, now Icc 0 T-restricted).
  have h_conv_bound : ∀ s ∈ Set.Icc 0 T, ∀ x : PhysSpace d,
      ‖convolveFunctionMeasure gradW (ρ s) x‖ ≤ ε₀ + (L : ℝ) * ‖x‖ := by
    intro s hs x
    unfold convolveFunctionMeasure
    have h_sub_int : Integrable (fun y => ‖x - y‖) (ρ s) :=
      Integrable.mono' ((integrable_const ‖x‖).add (h_y_int s hs))
        ((aestronglyMeasurable_const (b := x)).sub aestronglyMeasurable_id |>.norm)
        (Filter.Eventually.of_forall fun y => by
          simp only [Real.norm_of_nonneg (norm_nonneg _)]; exact norm_sub_le x y)
    have h_pt : ∀ y : PhysSpace d,
        ‖gradW (x - y)‖ ≤ ‖gradW 0‖ + (L : ℝ) * ‖x - y‖ := by
      intro y
      have hd := hL.dist_le_mul (x - y) 0
      simp only [dist_eq_norm, sub_zero] at hd
      have h_tri : ‖gradW (x - y)‖ ≤ ‖gradW 0‖ + ‖gradW (x - y) - gradW 0‖ := by
        have := norm_add_le (gradW (x - y) - gradW 0) (gradW 0)
        simp only [sub_add_cancel] at this; linarith
      linarith
    have h_bnd_int : Integrable (fun y => ‖gradW 0‖ + (L : ℝ) * ‖x - y‖) (ρ s) :=
      (integrable_const _).add (h_sub_int.const_mul _)
    calc ‖∫ y, gradW (x - y) ∂(ρ s)‖
        ≤ ∫ y, ‖gradW (x - y)‖ ∂(ρ s) := norm_integral_le_integral_norm _
      _ ≤ ∫ y, (‖gradW 0‖ + (L : ℝ) * ‖x - y‖) ∂(ρ s) :=
          integral_mono (h_int s x).norm h_bnd_int (fun y => h_pt y)
      _ = ‖gradW 0‖ + (L : ℝ) * ∫ y, ‖x - y‖ ∂(ρ s) := by
          rw [integral_add (integrable_const _) (h_sub_int.const_mul _)]
          simp [integral_const, measureReal_def, measure_univ, integral_const_mul]
      _ ≤ ε₀ + (L : ℝ) * ‖x‖ := by
          have h_int_le : ∫ y, ‖x - y‖ ∂(ρ s) ≤ ‖x‖ + M_ρ := by
            calc ∫ y, ‖x - y‖ ∂(ρ s)
                ≤ ∫ y, (‖x‖ + ‖y‖) ∂(ρ s) :=
                  integral_mono h_sub_int ((integrable_const _).add (h_y_int s hs))
                    (fun y => norm_sub_le x y)
              _ = ‖x‖ + ∫ y, ‖y‖ ∂(ρ s) := by
                  rw [integral_add (integrable_const _) (h_y_int s hs)]
                  simp [integral_const, measureReal_def, measure_univ]
              _ ≤ ‖x‖ + M_ρ := by linarith [hM_ρ s hs]
          simp only [ε₀]; linarith [mul_le_mul_of_nonneg_left h_int_le (NNReal.coe_nonneg L)]
  -- Step 3: Choose nhd = Ioo (t/2) ((t+T)/2) ⊆ Ioo 0 T.  t/2 < t (since t>0) and
  -- t < (t+T)/2 (since t < T), so t ∈ nhd; further nhd ⊆ Icc 0 T for bounding.
  refine ⟨Set.Ioo (t / 2) ((t + T) / 2),
    fun z => M_φ * (K * C_T + ε₀) * (‖z‖ + 1), ?_, ?_, ?_⟩
  · -- nhd ∈ nhds t.
    exact Ioo_mem_nhds (by linarith [ht.1]) (by linarith [ht.2])
  · -- LipschitzOnWith for ae-z, via MVT on the convex nhd.
    apply Filter.Eventually.of_forall
    intro z
    let deriv_val : ℝ → PhaseSpace d → ℝ := fun s z =>
      (fderiv ℝ φ (charX s z, charV s z))
        (charV s z, -(convolveFunctionMeasure gradW (ρ s) (charX s z)))
    apply Convex.lipschitzOnWith_of_nnnorm_hasDerivWithin_le (convex_Ioo _ _)
      (f' := fun s => deriv_val s z)
    · -- HasDerivWithinAt for each s ∈ nhd; uses hflow_on at s ∈ Ioo 0 T.
      intro s hs
      have hs_Ioo : s ∈ Set.Ioo (0 : ℝ) T :=
        ⟨by linarith [hs.1, ht.1], by linarith [hs.2, ht.2]⟩
      have hX_at := hflow_on.2.1 s hs_Ioo z (Set.mem_univ z)
      have hV_at := hflow_on.2.2 s hs_Ioo z (Set.mem_univ z)
      have h_flow_deriv : HasDerivAt (fun s' => (charX s' z, charV s' z))
          (charV s z, -(convolveFunctionMeasure gradW (ρ s) (charX s z))) s :=
        hX_at.prodMk hV_at
      have h_φ_fderiv : HasFDerivAt φ (fderiv ℝ φ (charX s z, charV s z))
          (charX s z, charV s z) :=
        hφ_diff (charX s z, charV s z) |>.hasFDerivAt
      exact (h_φ_fderiv.comp_hasDerivAt s h_flow_deriv).hasDerivWithinAt
    · -- Bound ‖deriv_val s z‖₊ ≤ M_φ * (K * C_T + ε₀) * (‖z‖ + 1).
      intro s hs
      rw [← NNReal.coe_le_coe]
      simp only []
      have hs_mem : s ∈ Set.Icc 0 T :=
        ⟨le_of_lt (by linarith [hs.1, ht.1]),
         le_of_lt (by linarith [hs.2, ht.2])⟩
      have h_flow_bnd : ‖(charX s z, charV s z)‖ ≤ C_T * (‖z‖ + 1) :=
        hC_T s hs_mem z
      have h_x_bnd : ‖charX s z‖ ≤ C_T * (‖z‖ + 1) := by
        have hpn : ‖(charX s z, charV s z)‖ = max ‖charX s z‖ ‖charV s z‖ :=
          Prod.norm_def _
        linarith [le_max_left ‖charX s z‖ ‖charV s z‖, hpn ▸ h_flow_bnd]
      have h_v_bnd2 : ‖charV s z‖ ≤ C_T * (‖z‖ + 1) := by
        have hpn : ‖(charX s z, charV s z)‖ = max ‖charX s z‖ ‖charV s z‖ :=
          Prod.norm_def _
        linarith [le_max_right ‖charX s z‖ ‖charV s z‖, hpn ▸ h_flow_bnd]
      have h_c_bnd : ‖convolveFunctionMeasure gradW (ρ s) (charX s z)‖ ≤
          ε₀ + (L : ℝ) * C_T * (‖z‖ + 1) := by
        have := h_conv_bound s hs_mem (charX s z)
        linarith [mul_le_mul_of_nonneg_left h_x_bnd (NNReal.coe_nonneg L)]
      have h_vel_bnd : ‖(charV s z, -(convolveFunctionMeasure gradW (ρ s) (charX s z)))‖
          ≤ K * C_T * (‖z‖ + 1) + ε₀ := by
        rw [Prod.norm_def]
        simp only [norm_neg]
        have hK1 : (1 : ℝ) ≤ K := by linarith [NNReal.coe_nonneg L]
        have hz1 : (0 : ℝ) ≤ ‖z‖ + 1 := by linarith [norm_nonneg z]
        apply max_le
        · have h1 : C_T * (‖z‖ + 1) ≤ K * C_T * (‖z‖ + 1) := by
            have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK1 hC_T_nn) hz1
            linarith
          linarith
        · have hLK : (L : ℝ) ≤ K := by linarith [NNReal.coe_nonneg L]
          have h2 : (L : ℝ) * C_T * (‖z‖ + 1) ≤ K * C_T * (‖z‖ + 1) := by
            have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hLK hC_T_nn) hz1
            linarith
          linarith
      rw [Real.coe_nnabs, abs_of_nonneg (by positivity)]
      calc ‖deriv_val s z‖
          ≤ ‖fderiv ℝ φ (charX s z, charV s z)‖ *
            ‖(charV s z, -(convolveFunctionMeasure gradW (ρ s) (charX s z)))‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ M_φ * (K * C_T * (‖z‖ + 1) + ε₀) := by
            apply mul_le_mul (hM_φ _) h_vel_bnd (norm_nonneg _) hM_φ_nn
        _ ≤ M_φ * (K * C_T + ε₀) * (‖z‖ + 1) := by
            have hz1 : 1 ≤ ‖z‖ + 1 := by linarith [norm_nonneg z]
            nlinarith [mul_nonneg hM_φ_nn hε₀_nn,
                       mul_nonneg (mul_nonneg hM_φ_nn hε₀_nn)
                         (by linarith [norm_nonneg z] : (0 : ℝ) ≤ ‖z‖),
                       mul_nonneg hM_φ_nn hC_T_nn]
  · -- Integrable bound (same as `_lag`).
    have h_bound_eq : (fun z : PhaseSpace d => M_φ * (K * C_T + ε₀) * (‖z‖ + 1)) =
        fun z => M_φ * (K * C_T + ε₀) * ‖z‖ + M_φ * (K * C_T + ε₀) := by
      ext z; ring
    rw [h_bound_eq]
    exact (hf₀_fm.const_mul _).add (integrable_const _)

/-- **`_On`-flavored Lagrangian → Eulerian producer for `IsVlasovSolutionOn`**.

The `_on` analog of `vlasovSolutionViaPushforward_isVlasovSolution`,
taking the characteristic flow in `IsCharacteristicFlowOn ...
(Set.Ioo 0 T) Set.univ` form (the flow construction's natural output) and
producing the weak Vlasov PDE in localized `IsVlasovSolutionOn` form (also
on `Ioo 0 T`).

The global proof's structure transports to the `_On` form:
* `intro t` becomes `intro t ht` with `ht : t ∈ Set.Ioo 0 T`.
* `hflow.2.1 t z` (HasDerivAt universal) becomes
  `hflow_on.2.1 t ht z (Set.mem_univ z)` (HasDerivAt at the specific
  `t ∈ Ioo 0 T`, `z ∈ Set.univ`).
* The conclusion stays at `HasDerivAt` (since `t ∈ Ioo` is an interior
  point of the predicate's quantification set; no `HasDerivWithinAt`
  conversion needed).
* The sub-helpers `vlasov_traj_chain_rule`, `vlasov_compose_flow_*`,
  `vlasov_pushforward_hasDerivAt_under_integral`,
  `vlasov_rhs_pushforward_back` all consume flow hypotheses at a
  *specific `t`*, not universally, so they transport unchanged after
  threading the `ht : t ∈ Ioo 0 T` constraint. -/
theorem vlasovSolutionViaPushforward_isVlasovSolutionOn
    {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (hf₀_fm : Integrable (fun z : PhaseSpace d => ‖z‖) f₀)
    {T : ℝ} (hT : 0 < T)
    (hflow_on : IsCharacteristicFlowOn gradW
                (fun t => spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t))
                charX charV (Set.Ioo 0 T) Set.univ)
    -- Boundary regularity (discharged by the boundary-regularity helper at the call site).
    (h_init : ∀ z : PhaseSpace d, (charX 0 z, charV 0 z) = z)
    (h_cont_Icc : ∀ z : PhaseSpace d,
      ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc (0 : ℝ) T))
    (h_deriv_Ico : ∀ z : PhaseSpace d, ∀ s ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt (fun s' => (charX s' z, charV s' z))
        (vlasovVectorField gradW
          (fun t => spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t)) s
          (charX s z, charV s z))
        (Set.Ici s) s)
    -- ρ-regularity on Icc 0 T (the pushforward's spatial marginal).
    (M_ρ : ℝ) (hM_ρ_nn : 0 ≤ M_ρ)
    (hM_ρ : ∀ s ∈ Set.Icc (0 : ℝ) T,
      ∫ y, ‖y‖ ∂(spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s)) ≤ M_ρ)
    (h_y_int : ∀ s ∈ Set.Icc (0 : ℝ) T,
      Integrable (fun y : PhysSpace d => ‖y‖)
        (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s)))
    (h_int : ∀ s (x : PhysSpace d),
      Integrable (fun y => gradW (x - y))
        (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s)))
    [∀ s, IsProbabilityMeasure
      (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s))]
    (_hself : IsCharacteristicFlowSelfConsistent charX f₀
              (fun t => spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t)))
    (h_flow_meas : ∀ s, AEMeasurable
      (fun z : PhaseSpace d => (charX s z, charV s z)) f₀)
    (hgradW_cont : Continuous gradW)
    (hconv_cont : ∀ s, Continuous (fun x =>
        convolveFunctionMeasure gradW
          (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s)) x)) :
    IsVlasovSolutionOn gradW (vlasovSolutionViaPushforward charX charV f₀) T := by
  -- Unfold IsVlasovSolutionOn; for each test function φ, prove WeakEvolutionEqOn at t ∈ Ioo 0 T.
  intro φ hφ_smooth hφ_compact gradXφ gradVφ hgradXφ hgradVφ t ht
  -- Notation aliases (same as L2735).
  set ρ : ℝ → Measure (PhysSpace d) :=
    fun t => spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t) with hρ_def
  have hφ_cont : Continuous φ := hφ_smooth.continuous
  have hφ_aesm_general : ∀ μ : Measure (PhaseSpace d),
      AEStronglyMeasurable φ μ := fun μ => hφ_cont.aestronglyMeasurable
  -- SC.1 (same): unify ∫ φ d(vlasov s) with ∫ (φ ∘ flow_s) df₀.
  have h_compose : ∀ s, ∫ z, φ z ∂(vlasovSolutionViaPushforward charX charV f₀ s) =
      ∫ z, φ (charX s z, charV s z) ∂f₀ := fun s =>
    vlasov_pushforward_integral_eq_compose charX charV f₀ s
      (h_flow_meas s) φ (hφ_aesm_general _)
  -- SC.2 `_at`: pointwise chain rule at every z, AT the specific t ∈ Ioo 0 T.
  have h_pointwise : ∀ z, HasDerivAt (fun s => φ (charX s z, charV s z))
      (@inner ℝ (PhysSpace d) _ (charV t z) (gradXφ (charX t z, charV t z))
       - @inner ℝ (PhysSpace d) _
          (convolveFunctionMeasure gradW (ρ t) (charX t z))
          (gradVφ (charX t z, charV t z))) t := by
    intro z
    have hX_at := hflow_on.2.1 t ht z (Set.mem_univ z)
    have hV_at := hflow_on.2.2 t ht z (Set.mem_univ z)
    exact vlasov_traj_chain_rule_at gradW ρ charX charV φ hφ_smooth
      gradXφ gradVφ hgradXφ hgradVφ t z hX_at hV_at
  -- SC.3: DiffUnderIntegralData via SC.5-SC.8 (`_on` for SC.8).
  have h_diff_data : DiffUnderIntegralData gradW ρ charX charV f₀
      φ gradXφ gradVφ t := by
    -- Use `_on` variant of SC.8.
    obtain ⟨nhd, bound, hnhd, h_lipsch, h_bound_int⟩ :=
      vlasov_trajectory_lipschitz_bound_on gradW L hL ρ charX charV f₀
        hf₀_fm φ hφ_smooth hφ_compact hT hflow_on h_init h_cont_Icc h_deriv_Ico
        hgradW_cont hconv_cont t ht M_ρ hM_ρ_nn hM_ρ h_y_int h_int
    refine ⟨nhd, bound, hnhd, ?_, ?_, ?_, h_lipsch, h_bound_int⟩
    · exact vlasov_compose_flow_aestronglymeas charX charV f₀ φ
        hφ_cont h_flow_meas t
    · exact vlasov_compose_flow_integrable_at charX charV f₀ φ
        hφ_cont hφ_compact t (h_flow_meas t)
    · exact vlasov_pointwise_deriv_aestronglymeas gradW ρ charX charV f₀
        φ hφ_smooth gradXφ gradVφ hgradXφ hgradVφ hconv_cont t (h_flow_meas t)
  have h_under_integral :=
    vlasov_pushforward_hasDerivAt_under_integral gradW ρ charX charV f₀
      φ gradXφ gradVφ t h_pointwise h_diff_data
  -- SC.4: push the integrand back through `integral_map`.
  have h_integrand_aesm : AEStronglyMeasurable
      (fun y : PhaseSpace d =>
        @inner ℝ (PhysSpace d) _ y.2 (gradXφ y)
        - @inner ℝ (PhysSpace d) _
            (convolveFunctionMeasure gradW (ρ t) y.1) (gradVφ y))
      (vlasovSolutionViaPushforward charX charV f₀ t) := by
    apply Continuous.aestronglyMeasurable
    apply Continuous.sub
    · apply Continuous.inner continuous_snd
      have hfderiv_X : ∀ z : PhaseSpace d,
          fderiv ℝ (fun x => φ (x, z.2)) z.1 =
          (fderiv ℝ φ z).comp (ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d)) :=
        fun z => by
          have h1 : HasFDerivAt φ (fderiv ℝ φ z) z :=
            (hφ_smooth.differentiable (by simp) z).hasFDerivAt
          have h2 : HasFDerivAt (fun x : PhysSpace d => (x, z.2))
              (ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d)) z.1 :=
            hasFDerivAt_prodMk_left z.1 z.2
          exact (h1.comp z.1 h2).fderiv
      have heqX : gradXφ = fun z => gradient (fun x => φ (x, z.2)) z.1 := funext hgradXφ
      simp_rw [heqX, gradient, hfderiv_X]
      exact (InnerProductSpace.toDual ℝ (PhysSpace d)).symm.continuous.comp
        ((ContinuousLinearMap.isBoundedLinearMap_comp_right
          (ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d))).continuous.comp
          (hφ_smooth.continuous_fderiv (by simp)))
    · apply Continuous.inner
      · exact (hconv_cont t).comp continuous_fst
      · have hfderiv_V : ∀ z : PhaseSpace d,
            fderiv ℝ (fun v => φ (z.1, v)) z.2 =
            (fderiv ℝ φ z).comp (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d)) :=
          fun z => by
            have h1 : HasFDerivAt φ (fderiv ℝ φ z) z :=
              (hφ_smooth.differentiable (by simp) z).hasFDerivAt
            have h2 : HasFDerivAt (fun v : PhysSpace d => (z.1, v))
                (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d)) z.2 :=
              hasFDerivAt_prodMk_right z.1 z.2
            exact (h1.comp z.2 h2).fderiv
        have heqV : gradVφ = fun z => gradient (fun v => φ (z.1, v)) z.2 := funext hgradVφ
        simp_rw [heqV, gradient, hfderiv_V]
        exact (InnerProductSpace.toDual ℝ (PhysSpace d)).symm.continuous.comp
          ((ContinuousLinearMap.isBoundedLinearMap_comp_right
            (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d))).continuous.comp
            (hφ_smooth.continuous_fderiv (by simp)))
  have h_push_back :=
    vlasov_rhs_pushforward_back gradW charX charV f₀ t
      (h_flow_meas t) gradXφ gradVφ h_integrand_aesm
  -- Compose: rewrite LHS via h_compose, apply h_under_integral, then rewrite via h_push_back.
  have hLHS : (fun s => ∫ z, φ z ∂(vlasovSolutionViaPushforward charX charV f₀ s)) =
              (fun s => ∫ z, φ (charX s z, charV s z) ∂f₀) := funext h_compose
  rw [hLHS]
  rw [show (∫ z, @inner ℝ (PhysSpace d) _ z.2 (gradXφ z)
              - @inner ℝ (PhysSpace d) _
                  (convolveFunctionMeasure gradW
                    (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t)) z.1)
                  (gradVφ z)
            ∂(vlasovSolutionViaPushforward charX charV f₀ t)
            + (fun _ => (0 : ℝ)) t)
          = ∫ z, @inner ℝ (PhysSpace d) _ z.2 (gradXφ z)
                  - @inner ℝ (PhysSpace d) _
                      (convolveFunctionMeasure gradW
                        (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t)) z.1)
                      (gradVφ z)
                ∂(vlasovSolutionViaPushforward charX charV f₀ t) from by ring]
  rw [← h_push_back]
  exact h_under_integral

/-- **`_On`-flavored Lagrangian → Eulerian producer for `IsLagrangianVlasovSolutionOn`**.

Same hypothesis package as the global
`vlasovSolutionViaPushforward_isLagrangianVlasovSolution`, but takes the
characteristic flow in `IsCharacteristicFlowOn ... (Set.Ioo 0 T) Set.univ`
form (the flow construction's natural output) and produces the strictly
stronger `IsLagrangianVlasovSolutionOn` predicate.

**Composes**:
* `vlasovSolutionViaPushforward_isVlasovSolutionOn` (above) for the
  weak-PDE conjunct.
* the flow construction's output for the flow-witness conjunct.
* Trivial pushforward + AEMeasurability bundling for the remaining
  conjuncts (identical to the global wrapper's body, adapted to use
  `IsCharacteristicFlowOn`'s initial-condition clause).

This is the **packaging layer**; the substantive PDE proof lives in
`vlasovSolutionViaPushforward_isVlasovSolutionOn` above. -/
theorem vlasovSolutionViaPushforward_isLagrangianVlasovSolutionOn
    {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (hf₀_fm : Integrable (fun z : PhaseSpace d => ‖z‖) f₀)
    {T : ℝ} (hT : 0 < T)
    (hflow_on : IsCharacteristicFlowOn gradW
                (fun t => spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t))
                charX charV (Set.Ioo 0 T) Set.univ)
    (h_init : ∀ z : PhaseSpace d, (charX 0 z, charV 0 z) = z)
    (h_cont_Icc : ∀ z : PhaseSpace d,
      ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc (0 : ℝ) T))
    (h_deriv_Ico : ∀ z : PhaseSpace d, ∀ s ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt (fun s' => (charX s' z, charV s' z))
        (vlasovVectorField gradW
          (fun t => spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t)) s
          (charX s z, charV s z))
        (Set.Ici s) s)
    (M_ρ : ℝ) (hM_ρ_nn : 0 ≤ M_ρ)
    (hM_ρ : ∀ s ∈ Set.Icc (0 : ℝ) T,
      ∫ y, ‖y‖ ∂(spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s)) ≤ M_ρ)
    (h_y_int : ∀ s ∈ Set.Icc (0 : ℝ) T,
      Integrable (fun y : PhysSpace d => ‖y‖)
        (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s)))
    (h_int : ∀ s (x : PhysSpace d),
      Integrable (fun y => gradW (x - y))
        (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s)))
    [∀ s, IsProbabilityMeasure
      (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s))]
    (hself : IsCharacteristicFlowSelfConsistent charX f₀
              (fun t => spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t)))
    (h_flow_meas : ∀ s, AEMeasurable
      (fun z : PhaseSpace d => (charX s z, charV s z)) f₀)
    (hgradW_cont : Continuous gradW)
    (hconv_cont : ∀ s, Continuous (fun x =>
        convolveFunctionMeasure gradW
          (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s)) x)) :
    IsLagrangianVlasovSolutionOn gradW
      (vlasovSolutionViaPushforward charX charV f₀) T := by
  refine ⟨vlasovSolutionViaPushforward_isVlasovSolutionOn gradW L hL charX charV f₀
            hf₀_fm hT hflow_on h_init h_cont_Icc h_deriv_Ico M_ρ hM_ρ_nn hM_ρ
            h_y_int h_int hself h_flow_meas hgradW_cont hconv_cont,
          charX, charV, hflow_on, ?_, ?_, h_cont_Icc⟩
  · -- Pushforward equation: f t = (flow_t)_# (f 0) for t ∈ Icc 0 T.
    -- Identical to the global wrapper's body, using IsCharacteristicFlowOn's
    -- initial-condition clause `hflow_on.1 z (Set.mem_univ z)`.
    have h_init : (fun z : PhaseSpace d => (charX 0 z, charV 0 z)) = id := by
      funext z
      have h := hflow_on.1 z (Set.mem_univ z)
      exact Prod.ext h.1 h.2
    have h0 : vlasovSolutionViaPushforward charX charV f₀ 0 = f₀ := by
      simp [vlasovSolutionViaPushforward, h_init, Measure.map_id]
    intro t _ht
    rw [h0]
    rfl
  · -- AEMeasurability on Icc 0 T.  Same h0 step as above.
    intro s _hs
    have h_init : (fun z : PhaseSpace d => (charX 0 z, charV 0 z)) = id := by
      funext z
      have h := hflow_on.1 z (Set.mem_univ z)
      exact Prod.ext h.1 h.2
    have h0 : vlasovSolutionViaPushforward charX charV f₀ 0 = f₀ := by
      simp [vlasovSolutionViaPushforward, h_init, Measure.map_id]
    rw [h0]
    exact h_flow_meas s

/-! ## Integration smoke test

A small theorem demonstrating that the three OT files compose: given
two characteristic flows on the same initial probability measures
with finite first moment, the Wasserstein-1 distance between the
pushed-forward measures at time `t` is bounded by the infimum (over
couplings of the *initial* measures) of the pushed-forward edist
cost.

This is **exactly the shape** the USC and derivBound closures in
`LeanPool/Vlasov/Basic.lean` need: it turns a coupling at time 0 into a
W₁-upper-bound at time t.  The Gronwall-on-the-joint-ODE step (which
controls the cost growth) is the next piece — orthogonal to OT,
sits in the dynamics layer.

The theorem is a direct application of `wasserstein1_pushforward_le_iInf`
from `Coupling.lean`; the integration test confirms the type chain
composes correctly when the maps are characteristic flows. -/

theorem wasserstein1_lagrangian_pushforward_bound
    {d : ℕ}
    (charX_f charV_f charX_g charV_g : ℝ → PhaseSpace d → PhysSpace d)
    (f₀ g₀ : Measure (PhaseSpace d))
    (t : ℝ)
    (h_meas_f : Measurable (fun z : PhaseSpace d => (charX_f t z, charV_f t z)))
    (h_meas_g : Measurable (fun z : PhaseSpace d => (charX_g t z, charV_g t z)))
    (h_fmpr_f : IsProbabilityMeasure
                (Measure.map (fun z : PhaseSpace d => (charX_f t z, charV_f t z)) f₀))
    (h_fmpr_g : IsProbabilityMeasure
                (Measure.map (fun z : PhaseSpace d => (charX_g t z, charV_g t z)) g₀))
    (x₀ : PhaseSpace d)
    (h_fm_f : Integrable (fun y : PhaseSpace d => dist y x₀)
              (Measure.map (fun z : PhaseSpace d => (charX_f t z, charV_f t z)) f₀))
    (h_fm_g : Integrable (fun y : PhaseSpace d => dist y x₀)
              (Measure.map (fun z : PhaseSpace d => (charX_g t z, charV_g t z)) g₀)) :
    wasserstein1
      (Measure.map (fun z : PhaseSpace d => (charX_f t z, charV_f t z)) f₀)
      (Measure.map (fun z : PhaseSpace d => (charX_g t z, charV_g t z)) g₀) ≤
      ⨅ (π : Measure (PhaseSpace d × PhaseSpace d)) (_ : IsCoupling π f₀ g₀),
        ∫⁻ z, edist (charX_f t z.1, charV_f t z.1)
                    (charX_g t z.2, charV_g t z.2) ∂π :=
  wasserstein1_pushforward_le_iInf
    (fun z => (charX_f t z, charV_f t z))
    (fun z => (charX_g t z, charV_g t z))
    h_meas_f h_meas_g f₀ g₀ x₀ h_fmpr_f h_fmpr_g h_fm_f h_fm_g

/-! ## Banach fixed-point scaffolding for `vlasovWellPosedness` -/
-- The infrastructure here makes the Φ-well-definedness, Gronwall-contraction
-- and Picard-iteration steps compose cleanly:
--   * `VlasovMeasureCurve T M`: admissible curves of probability measures
--     on `PhysSpace d` with uniform first-moment bound `M` on `[0, T]`.
--     The four structural fields are exactly what `Φ` preserves.
--   * `supW1On`: sup-W₁ pseudodistance over a set of times; the natural
--     contraction metric for the Picard iteration.
--   * `vlasovMeasureCurve_convCont`: convolution continuity in `t` derived
--     from the W₁-continuity field via `norm_convolveFunctionMeasure_sub_le`.
--   * `constantCurve`: the constant curve `t ↦ μ₀`, used as the Picard
--     iteration's starting point and as a sanity-check witness that the
--     structure is inhabited.

/-- The sup-W₁ pseudodistance between two curves of measures over a set of
times `S`.  Returns `⨆ t ∈ S, wasserstein1 (ρ t) (σ t)` in `ℝ≥0∞`.

* Symmetric (`supW1On_comm`) and satisfies the triangle inequality
  (`supW1On_triangle`).
* Finite (≠ ⊤) when both curves are `VlasovMeasureCurve`s on `[0, T]` with
  the same moment bound, via `supW1On_ne_top_of_VlasovMeasureCurve`.

Used as the contraction metric for the Picard iteration. -/
noncomputable def supW1On {d : ℕ}
    (S : Set ℝ) (ρ σ : ℝ → Measure (PhysSpace d)) : ℝ≥0∞ :=
  ⨆ (t : ℝ) (_ : t ∈ S), wasserstein1 (ρ t) (σ t)

lemma supW1On_comm {d : ℕ} (S : Set ℝ)
    (ρ σ : ℝ → Measure (PhysSpace d)) :
    supW1On S ρ σ = supW1On S σ ρ := by
  unfold supW1On
  refine iSup_congr fun t => ?_
  refine iSup_congr fun _ => ?_
  exact wasserstein1_comm _ _

lemma supW1On_self {d : ℕ} (S : Set ℝ)
    (ρ : ℝ → Measure (PhysSpace d)) :
    supW1On S ρ ρ = 0 := by
  unfold supW1On
  simp [wasserstein1_self]

lemma supW1On_triangle {d : ℕ} (S : Set ℝ)
    (ρ σ τ : ℝ → Measure (PhysSpace d)) :
    supW1On S ρ τ ≤ supW1On S ρ σ + supW1On S σ τ := by
  unfold supW1On
  refine iSup_le fun t => iSup_le fun ht => ?_
  calc wasserstein1 (ρ t) (τ t)
      ≤ wasserstein1 (ρ t) (σ t) + wasserstein1 (σ t) (τ t) :=
        wasserstein1_triangle _ _ _
    _ ≤ (⨆ s ∈ S, wasserstein1 (ρ s) (σ s))
        + (⨆ s ∈ S, wasserstein1 (σ s) (τ s)) := by
        gcongr
        · exact le_iSup_of_le t (le_iSup_of_le ht le_rfl)
        · exact le_iSup_of_le t (le_iSup_of_le ht le_rfl)

/-- **Iterated triangle inequality for `supW1On` over a sequence**.

For any sequence `x : ℕ → ℝ → Measure (PhysSpace d)` and `m ≤ n`:
`supW1On S (x m) (x n) ≤ ∑ k ∈ Ico m n, supW1On S (x k) (x (k+1))`.

**Generic structural lemma** — stated over an arbitrary sequence and time
set `S`, not specialised to Picard iteration.  Downstream consumers (the
Cauchy-from-contraction argument, the forward-iteration continuation, window
uniqueness) compose against this generic form.

The entire proof stays in ENNReal — `supW1On` is ENNReal-valued, the sum is
in ENNReal, ENNReal addition is well-defined with `⊤` as absorbing element,
so no finiteness side conditions arise.  Project to ℝ via `.toReal` only at
the boundary (or not at all, as in the ENNReal-form Cauchy argument).

Proof: induction on `n` starting from `n = m` via `Nat.le_induction`.
Base case is the empty sum via `supW1On_self`.  Inductive step combines
`supW1On_triangle` with `Finset.sum_Ico_succ_top`. -/
lemma supW1On_iterated_triangle {d : ℕ} (S : Set ℝ)
    (x : ℕ → ℝ → Measure (PhysSpace d))
    (m n : ℕ) (hmn : m ≤ n) :
    supW1On S (x m) (x n) ≤
      ∑ k ∈ Finset.Ico m n, supW1On S (x k) (x (k+1)) := by
  induction n, hmn using Nat.le_induction with
  | base =>
    -- Empty sum: Ico m m = ∅.
    rw [Finset.Ico_self, Finset.sum_empty]
    rw [supW1On_self]
  | succ n hmn ih =>
    calc supW1On S (x m) (x (n+1))
        ≤ supW1On S (x m) (x n) + supW1On S (x n) (x (n+1)) :=
          supW1On_triangle S (x m) (x n) (x (n+1))
      _ ≤ (∑ k ∈ Finset.Ico m n, supW1On S (x k) (x (k+1))) +
          supW1On S (x n) (x (n+1)) := by
          exact add_le_add ih (le_refl _)
      _ = ∑ k ∈ Finset.Ico m (n+1), supW1On S (x k) (x (k+1)) := by
          rw [Finset.sum_Ico_succ_top hmn]

/-! ## Metric-dependent smallness predicates -/
--
-- The existence-and-contraction analysis uses TWO independent smallness
-- constraints, captured as two separate predicates:
--   * `LocalSmallnessPLBuffer L T := L · T² < 1` — per-ball
--     Picard-Lindelöf flow ball-geometry (the L-Lipschitz R-existence
--     fixed-point).
--   * `LocalSmallnessContraction L T := L · (exp((max 1 L)·T) - 1) / (max 1 L) < 1`
--     — supW1On contraction-ratio (Gronwall on the W₁-based flow).
--
-- These are kept as two predicates because they are genuinely independent
-- mathematical constraints from distinct sub-arguments: the ball-geometry
-- shape does NOT imply the exponential contraction constraint, and is not
-- implied by it.  Carrying them separately keeps each predicate matched to
-- its own sub-argument rather than fusing two distinct claims.
--
-- The truncated-distance Wasserstein `Wbar = W_{min(|x-y|,1)}` (Dobrushin 1979,
-- §5) is an alternative metric that replaces the `LocalSmallnessContraction`
-- exponential with a linear-in-T form.

/-- **Smallness predicate for the per-ball Picard-Lindelöf flow's
ball-geometry constraint.**

Defined as `(L : ℝ) * T ^ 2 < 1`, this is the smallness condition
the per-ball flow's R-selection requires: `R · (1 - L·T²) ≥ N(z)`
forces R > 0 only when `L·T² < 1`.  It comes from the tight
adaptive-window Picard-Lindelöf geometry + L-Lipschitz fixed-point
analysis, NOT from contraction.

This is kept separate from the supW1On *contraction-ratio* constraint
`LocalSmallnessContraction` (below): the two are genuinely independent
mathematical constraints from distinct sub-arguments, so each predicate
stays matched to its own sub-argument. -/
def LocalSmallnessPLBuffer (L : NNReal) (T : ℝ) : Prop :=
  (L : ℝ) * T ^ 2 < 1

/-- **Smallness predicate for the supW1On contraction-ratio constraint.**

For `Phi_supW1_contraction`'s output to satisfy `q < 1` — the genuine
M-independent contraction ratio — the constraint is
`L · (exp((max 1 L)·T) - 1) / (max 1 L) < 1`.  This comes from Gronwall
on the W₁-based contraction analysis, inherited off
`vlasovVectorField_lipschitzWith` (the joint phase-space
`max(1, L)`-Lipschitz constant).

When `max(1, L) = 1` the constraint simplifies to `L · (exp T - 1) < 1`. -/
def LocalSmallnessContraction (L : NNReal) (T : ℝ) : Prop :=
  (L : ℝ) * (Real.exp ((max 1 (L : ℝ)) * T) - 1) / (max 1 (L : ℝ)) < 1

/-- The curve metric used by the `VlasovMeasureCurve` Banach iteration:
`supW1On` (sup of `W₁` distances over the time window).

Defined as `abbrev` so the abbreviation unfolds transparently — proofs that
reference `supW1On` work against `CurveMetric` without modification.  New
consumers can use `CurveMetric` directly for explicit metric-agnosticism. -/
noncomputable abbrev CurveMetric {d : ℕ}
    (S : Set ℝ) (ρ σ : ℝ → Measure (PhysSpace d)) : ℝ≥0∞ :=
  supW1On S ρ σ

/-- Admissible Vlasov measure curves on `[0, T]`: a curve of probability
measures on `PhysSpace d` with uniform first-moment bound `M`, pointwise
integrability of `‖·‖`, and W₁-continuity at every time in `[0, T]`.

The W₁-continuity field is phrased per-base-point `s ∈ [0, T]` as
`ContinuousWithinAt` of `t ↦ W₁(ρ s, ρ t).toReal` at `s` (which equals 0 at
`t = s`).  This is strictly stronger than naive ContinuousOn on the diagonal
— it gives the dominator we need for derived convolution continuity
(`vlasovMeasureCurve_convCont`) and for the Picard limit's bundling.

`d` is an explicit parameter so that `VlasovMeasureCurve d T M` is fully
determined at use sites (otherwise `NeZero d` cannot be resolved from the
non-discriminating real-valued T, M alone). -/
structure VlasovMeasureCurve (d : ℕ) [NeZero d] (T : ℝ) (M : ℝ → ℝ) where
  /-- The underlying curve of spatial measures, `t ↦ ρ t`. -/
  ρ : ℝ → Measure (PhysSpace d)
  isProb : ∀ t, IsProbabilityMeasure (ρ t)
  hasMoment : ∀ t ∈ Set.Icc (0 : ℝ) T, ∫ y, ‖y‖ ∂(ρ t) ≤ M t
  yIntegrable : ∀ t ∈ Set.Icc (0 : ℝ) T, Integrable (fun y : PhysSpace d => ‖y‖) (ρ t)
  hW1Cont : ∀ s ∈ Set.Icc (0 : ℝ) T,
    ContinuousWithinAt (fun t => (wasserstein1 (ρ s) (ρ t)).toReal)
                       (Set.Icc 0 T) s

/-- `supW1On` of two `VlasovMeasureCurve`s on `[0, T]` with moment bound `M`
is bounded by `2M`, hence finite.

Combines pointwise `wasserstein1_le_moments_sum` with `iSup_le` over the
compact time set. -/
lemma supW1On_le_two_moment_of_VlasovMeasureCurve {d : ℕ} [NeZero d]
    {T : ℝ} {M : ℝ → ℝ} (Mbar : ℝ) (hMbar : ∀ t ∈ Set.Icc 0 T, M t ≤ Mbar)
    (ρ σ : VlasovMeasureCurve d T M) :
    supW1On (Set.Icc 0 T) ρ.ρ σ.ρ ≤ ENNReal.ofReal (2 * Mbar) := by
  unfold supW1On
  refine iSup_le fun t => iSup_le fun ht => ?_
  -- Pointwise: W₁(ρ_t, σ_t) ≤ ofReal(∫‖y‖d(ρ_t) + ∫‖y‖d(σ_t)) ≤ ofReal(M + M)
  have h_bound : wasserstein1 (ρ.ρ t) (σ.ρ t) ≤
      ENNReal.ofReal (∫ y, ‖y‖ ∂(ρ.ρ t) + ∫ y, ‖y‖ ∂(σ.ρ t)) := by
    haveI : IsProbabilityMeasure (ρ.ρ t) := ρ.isProb t
    haveI : IsProbabilityMeasure (σ.ρ t) := σ.isProb t
    exact wasserstein1_le_moments_sum (ρ.ρ t) (σ.ρ t)
      (ρ.yIntegrable t ht) (σ.yIntegrable t ht)
  refine h_bound.trans ?_
  apply ENNReal.ofReal_le_ofReal
  have hρ_t : ∫ y, ‖y‖ ∂(ρ.ρ t) ≤ M t := ρ.hasMoment t ht
  have hσ_t : ∫ y, ‖y‖ ∂(σ.ρ t) ≤ M t := σ.hasMoment t ht
  linarith [hMbar t ht]

/-- `supW1On` of two `VlasovMeasureCurve`s is finite (≠ ⊤). -/
lemma supW1On_ne_top_of_VlasovMeasureCurve {d : ℕ} [NeZero d] {T : ℝ} {M : ℝ → ℝ}
    (Mbar : ℝ) (hMbar : ∀ t ∈ Set.Icc 0 T, M t ≤ Mbar)
    (ρ σ : VlasovMeasureCurve d T M) :
    supW1On (Set.Icc 0 T) ρ.ρ σ.ρ ≠ ⊤ :=
  ne_of_lt ((supW1On_le_two_moment_of_VlasovMeasureCurve Mbar hMbar ρ σ).trans_lt
            ENNReal.ofReal_lt_top)

/-- Convolution continuity in time, derived from the structural
`hW1Cont` field via `norm_convolveFunctionMeasure_sub_le`.

For each `x ∈ PhysSpace d`, the map `t ↦ (∇W ∗ ρ_t)(x)` is continuous on
`[0, T]`.  Used inside `Φ`'s well-definedness proof to discharge the
convolution-continuity hypothesis of `exists_vlasov_characteristicFlow`. -/
lemma vlasovMeasureCurve_convCont {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    {T : ℝ} {M : ℝ → ℝ} (ρ : VlasovMeasureCurve d T M)
    (x : PhysSpace d)
    (h_int : ∀ t ∈ Set.Icc (0 : ℝ) T,
              Integrable (fun y => gradW (x - y)) (ρ.ρ t)) :
    ContinuousOn (fun t => convolveFunctionMeasure gradW (ρ.ρ t) x)
                 (Set.Icc 0 T) := by
  -- Strategy: at every base `s ∈ [0, T]`, the Lipschitz convolution estimate
  --   ‖conv(ρ_s, x) - conv(ρ_t, x)‖ ≤ L · W₁(ρ_s, ρ_t).toReal
  -- composes with the hW1Cont field (W₁(ρ_s, ρ_t).toReal → 0 as t → s within
  -- [0, T]) to give ContinuousWithinAt at s.
  intro s hs
  haveI hPs : IsProbabilityMeasure (ρ.ρ s) := ρ.isProb s
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  have hCont := ρ.hW1Cont s hs
  rw [Metric.continuousWithinAt_iff] at hCont
  have h_self : (wasserstein1 (ρ.ρ s) (ρ.ρ s)).toReal = 0 := by
    rw [wasserstein1_self]; rfl
  -- Pick δ from hCont for tolerance ε / (L + 1)  (so that L · δ < ε)
  set η : ℝ := ε / ((L : ℝ) + 1) with hη_def
  have hLp1_pos : (0 : ℝ) < (L : ℝ) + 1 := by
    have : (0 : ℝ) ≤ L := L.coe_nonneg
    linarith
  have hη_pos : 0 < η := div_pos hε hLp1_pos
  obtain ⟨δ, hδ_pos, hδ_bound⟩ := hCont η hη_pos
  refine ⟨δ, hδ_pos, fun t ht hdist => ?_⟩
  have hδb := hδ_bound ht hdist
  rw [h_self, Real.dist_eq, sub_zero] at hδb
  have hW1_nn : 0 ≤ (wasserstein1 (ρ.ρ s) (ρ.ρ t)).toReal := ENNReal.toReal_nonneg
  have hW1_lt : (wasserstein1 (ρ.ρ s) (ρ.ρ t)).toReal < η := by
    rwa [abs_of_nonneg hW1_nn] at hδb
  haveI hPt : IsProbabilityMeasure (ρ.ρ t) := ρ.isProb t
  have h_finite : wasserstein1 (ρ.ρ s) (ρ.ρ t) ≠ ⊤ :=
    wasserstein1_ne_top_of_finite_moment _ _
      (ρ.yIntegrable s hs) (ρ.yIntegrable t ht)
  have h_lip := norm_convolveFunctionMeasure_sub_le gradW L hL
    (ρ.ρ s) (ρ.ρ t) x h_finite (h_int s hs) (h_int t ht)
  -- h_lip : ‖conv(ρ_s, x) - conv(ρ_t, x)‖ ≤ L · W₁(ρ_s, ρ_t).toReal
  rw [dist_eq_norm]
  calc ‖convolveFunctionMeasure gradW (ρ.ρ t) x
        - convolveFunctionMeasure gradW (ρ.ρ s) x‖
      = ‖convolveFunctionMeasure gradW (ρ.ρ s) x
          - convolveFunctionMeasure gradW (ρ.ρ t) x‖ := norm_sub_rev _ _
    _ ≤ (L : ℝ) * (wasserstein1 (ρ.ρ s) (ρ.ρ t)).toReal := h_lip
    _ ≤ (L : ℝ) * η := by
        apply mul_le_mul_of_nonneg_left (le_of_lt hW1_lt) L.coe_nonneg
    _ < ((L : ℝ) + 1) * η := by nlinarith
    _ = ε := by
        rw [hη_def]
        field_simp

/-! ### Constant extension past `[0, T]`

A `VlasovMeasureCurve d T M` has its structural properties (moment bound,
integrability of `‖·‖`, W₁-continuity) only on `Icc 0 T`.
`exists_vlasov_characteristicFlow_global_smallT` takes universal-in-`t`
hypotheses (the proof internally accesses `ρ` at `t ∈ Icc 0 (T + 1)` —
see `exists_vlasov_trajectory`'s `hbound_local` — but the exposed
signature is universal).

The constant-extension wrapper `VlasovMeasureCurve.extend` produces a
curve on all of `ℝ` by clamping `t` to `Icc 0 T`: `extend t := ρ.ρ (clamp t)`
where `clamp t := max 0 (min t T)`.  Outside `Icc 0 T` the extended
curve takes the boundary value (`ρ.ρ 0` for `t < 0`; `ρ.ρ T` for
`t > T`).  This is the canonical mathematical extension — a Vlasov
solution defined on a finite horizon is naturally extended by holding
the endpoint value past the horizon — and it makes the structural
properties hold universally without modifying the flow construction itself.

Discharge of `hρ_cont` (universal convolveFunctionMeasure continuity)
routes through `vlasovMeasureCurve_convCont` precomposed with the
continuous clamp via `ContinuousOn.comp_continuous`. -/

/-- Clamp `t : ℝ` to `Icc 0 T`.  Used by `VlasovMeasureCurve.extend` to
extend a curve from `Icc 0 T` to all of `ℝ`. -/
def clampToIcc (T t : ℝ) : ℝ := max 0 (min t T)

lemma clampToIcc_mem {T : ℝ} (hT : 0 ≤ T) (t : ℝ) :
    clampToIcc T t ∈ Set.Icc (0 : ℝ) T := by
  unfold clampToIcc
  refine Set.mem_Icc.mpr ⟨le_max_left _ _, max_le hT (min_le_right _ _)⟩

lemma clampToIcc_continuous (T : ℝ) : Continuous (clampToIcc T) := by
  unfold clampToIcc
  exact continuous_const.max (continuous_id.min continuous_const)

/-- Constant extension of a `VlasovMeasureCurve d T M`'s underlying curve
`ρ.ρ` from `Icc 0 T` to all of `ℝ`.  Defined as `ρ.ρ` composed with the
clamp `max 0 (min t T)`.

For `t ∈ Icc 0 T`: `extend t = ρ.ρ t`.
For `t < 0`: `extend t = ρ.ρ 0`.
For `t > T`: `extend t = ρ.ρ T`.

The extension preserves all structural properties (`IsProbabilityMeasure`,
moment bound, integrability of `‖·‖`) universally in `t`, and extends
W₁-continuity to convolveFunctionMeasure-continuity universally in `t`
via `clampToIcc_continuous` + `vlasovMeasureCurve_convCont`. -/
noncomputable def VlasovMeasureCurve.extend {d : ℕ} [NeZero d] {T : ℝ} {M : ℝ → ℝ}
    (ρ : VlasovMeasureCurve d T M) : ℝ → Measure (PhysSpace d) :=
  fun t => ρ.ρ (clampToIcc T t)

/-- The extended curve is a probability measure at every `t : ℝ`. -/
instance VlasovMeasureCurve.extend_isProb {d : ℕ} [NeZero d] {T : ℝ} {M : ℝ → ℝ}
    (ρ : VlasovMeasureCurve d T M) (t : ℝ) :
    IsProbabilityMeasure (ρ.extend t) :=
  ρ.isProb _

/-- The extended curve has `‖·‖` integrable at every `t : ℝ`. -/
lemma VlasovMeasureCurve.extend_yIntegrable {d : ℕ} [NeZero d] {T : ℝ} {M : ℝ → ℝ}
    (hT : 0 ≤ T) (ρ : VlasovMeasureCurve d T M) (t : ℝ) :
    Integrable (fun y : PhysSpace d => ‖y‖) (ρ.extend t) :=
  ρ.yIntegrable _ (clampToIcc_mem hT t)

/-- The extended curve preserves the moment bound `M` universally in `t`. -/
lemma VlasovMeasureCurve.extend_hasMoment {d : ℕ} [NeZero d] {T : ℝ} {M : ℝ → ℝ}
    (hT : 0 ≤ T) (ρ : VlasovMeasureCurve d T M) (t : ℝ) :
    ∫ y, ‖y‖ ∂(ρ.extend t) ≤ M (clampToIcc T t) :=
  ρ.hasMoment _ (clampToIcc_mem hT t)

/-- Convolution continuity on the extended curve, universal in `t`.

Composed from `vlasovMeasureCurve_convCont` (ContinuousOn on `Icc 0 T`)
with `clampToIcc_continuous` via `ContinuousOn.comp_continuous`.  This
provides the flow construction's universal `hρ_cont` hypothesis directly
from a `VlasovMeasureCurve`'s structural fields. -/
lemma VlasovMeasureCurve.extend_convCont {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    {T : ℝ} {M : ℝ → ℝ} (hT : 0 ≤ T) (ρ : VlasovMeasureCurve d T M)
    (x : PhysSpace d)
    (h_int : ∀ t ∈ Set.Icc (0 : ℝ) T,
              Integrable (fun y => gradW (x - y)) (ρ.ρ t)) :
    Continuous (fun t => convolveFunctionMeasure gradW (ρ.extend t) x) := by
  -- The function decomposes as `(fun s => convolveFunctionMeasure gradW (ρ.ρ s) x) ∘ clamp`.
  -- Inner is ContinuousOn (Icc 0 T) via vlasovMeasureCurve_convCont.
  -- Clamp is continuous and lands in Icc 0 T.
  have h_convCont := vlasovMeasureCurve_convCont gradW L hL ρ x h_int
  exact h_convCont.comp_continuous (clampToIcc_continuous T) (clampToIcc_mem hT)

/-- The constant curve at a probability measure with finite first moment is
a valid `VlasovMeasureCurve` on `[0, T]` for any `T` and any moment
bound `M ≥ ∫‖y‖dμ₀`. -/
def constantCurve {d : ℕ} [NeZero d] {T : ℝ} {M : ℝ → ℝ}
    (μ₀ : Measure (PhysSpace d)) [IsProbabilityMeasure μ₀]
    (hμ_int : Integrable (fun y : PhysSpace d => ‖y‖) μ₀)
    (hM : ∀ t ∈ Set.Icc (0 : ℝ) T, ∫ y, ‖y‖ ∂μ₀ ≤ M t) :
    VlasovMeasureCurve d T M where
  ρ := fun _ => μ₀
  isProb := fun _ => inferInstance
  hasMoment := hM
  yIntegrable := fun _ _ => hμ_int
  hW1Cont := fun s _ => by
    -- The function `t ↦ (wasserstein1 μ₀ μ₀).toReal` is identically 0;
    -- ContinuousWithinAt of a constant is immediate.
    have h_zero : (fun t : ℝ => (wasserstein1 μ₀ μ₀).toReal)
                  = fun _ => (0 : ℝ) := by
      funext _; rw [wasserstein1_self]; rfl
    rw [h_zero]
    exact continuousWithinAt_const

/-- **Per-z trajectory existence for small T.**

For each `z : PhaseSpace d`, produces a trajectory `γ : ℝ → PhaseSpace d` with
`γ 0 = z` satisfying the Vlasov ODE on `Ioo 0 T`.

**Smallness constraint**: `L · T² < 1`.  Comes from `exists_vlasov_characteristicFlow`'s
`hR` inequality, whose `M·T²` term has quadratic-in-T growth.  Solving
the algebraic constraint per-z yields a finite `R(z)` and `M(z)`, with the
existence-bound on `T` driven by `L·T² < 1`.

The forward-iteration continuation extends to arbitrary T via shifted
initial data; the small-T regime here is where the contraction operates. -/
theorem exists_vlasov_trajectory
    {d : ℕ} [NeZero d]
    (W : PhysSpace d → ℝ)
    (gradW : PhysSpace d → PhysSpace d)
    (hgradW : ∀ x, gradW x = gradient W x)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d))
    [∀ t, IsProbabilityMeasure (ρ t)]
    (h_int : ∀ t (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ t))
    (hρ_cont : ∀ x : PhysSpace d,
      Continuous (fun t => convolveFunctionMeasure gradW (ρ t) x))
    (h_y_int : ∀ t, Integrable (fun y : PhysSpace d => ‖y‖) (ρ t))
    (M_ρ : ℝ) (hM_ρ_nn : 0 ≤ M_ρ)
    (hM_ρ : ∀ t, ∫ y, ‖y‖ ∂(ρ t) ≤ M_ρ)
    (T : ℝ) (hT : 0 ≤ T)
    (hTL_PL : LocalSmallnessPLBuffer L T)
    (z : PhaseSpace d) :
    ∃ γ : ℝ → PhaseSpace d,
      γ 0 = z ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) T,
        HasDerivAt (fun s => (γ s).1) (γ t).2 t ∧
        HasDerivAt (fun s => (γ s).2)
          (-(convolveFunctionMeasure gradW (ρ t) (γ t).1)) t) ∧
      -- **Boundary regularity**: HasDerivWithinAt on `Icc 0 T` for every
      -- t ∈ Icc 0 T, derived from the per-ball flow's boundary conjunct.
      -- Closes the t = 0 (and t = T) boundary case for consumers like
      -- `flow_distance_growth_bound_on`.
      (∀ t ∈ Set.Icc (0 : ℝ) T,
        HasDerivWithinAt (fun s => (γ s).1) (γ t).2 (Set.Icc 0 T) t ∧
        HasDerivWithinAt (fun s => (γ s).2)
          (-(convolveFunctionMeasure gradW (ρ t) (γ t).1)) (Set.Icc 0 T) t) := by
  -- ============================================================
  -- Compute R(z), M(z) from the algebraic constraint:
  --   R ≥ 2 + (‖z.2‖ + 1/2)·T + M·T²
  --   M ≤ ‖gradW(0)‖ + L·(R + ‖z.1‖ + M_ρ)         (from L-Lipschitz)
  -- Substituting: R·(1 - L·T²) ≥ N(z)
  --   where N(z) := 2 + (‖z.2‖ + 1/2)·T
  --                + (‖gradW(0)‖ + L·‖z.1‖ + L·M_ρ)·T²
  -- Use R := N(z) / (1 - L·T²)  (positive since `hTL_PL`).
  -- ============================================================
  -- **`LocalSmallnessPLBuffer` unfold site.**  This body consumes the
  -- PL-buffer constraint `L · T² < 1` directly for R-existence — the
  -- linarith on the next line derives `hTL_pos := 1 - L·T² > 0` from
  -- `hTL_PL`'s algebraic form, and the subsequent `R := N(z) / (1 - L·T²)`
  -- selection depends on the quadratic shape.  This is a SINGLE-PURPOSE use
  -- of the PL-buffer predicate: no contraction-flavored step in this body
  -- discharges off the same hypothesis.  The `LocalSmallnessContraction`
  -- predicate is governed separately at `_picard_fixedPointFlow`'s `hq_lt`
  -- close, NOT here.
  have hTL : (L : ℝ) * T ^ 2 < 1 := hTL_PL
  set hTL_pos : (0 : ℝ) < 1 - (L : ℝ) * T ^ 2 := by linarith with hTL_pos_def
  -- N(z) is the right-hand-side numerator; non-negative.
  set N_z : ℝ := 2 + (‖z.2‖ + 1 / 2) * T
                 + (‖gradW 0‖ + (L : ℝ) * ‖z.1‖ + (L : ℝ) * M_ρ) * T ^ 2
    with hN_z_def
  have hN_z_nn : 0 ≤ N_z := by
    have h1 : 0 ≤ ‖z.2‖ + 1 / 2 := by positivity
    have h2 : 0 ≤ ‖gradW 0‖ + (L : ℝ) * ‖z.1‖ + (L : ℝ) * M_ρ := by
      have hgW : 0 ≤ ‖gradW 0‖ := norm_nonneg _
      have hLz1 : 0 ≤ (L : ℝ) * ‖z.1‖ := mul_nonneg L.coe_nonneg (norm_nonneg _)
      have hLMρ : 0 ≤ (L : ℝ) * M_ρ := mul_nonneg L.coe_nonneg hM_ρ_nn
      linarith
    have hT1nn : 0 ≤ T + 1 := by linarith
    have hT1sq : 0 ≤ T ^ 2 := sq_nonneg _
    have := mul_nonneg h1 hT1nn
    have := mul_nonneg h2 hT1sq
    rw [hN_z_def]; positivity
  -- R_real := N(z) / (1 - L·T²)
  set R_real : ℝ := N_z / (1 - (L : ℝ) * T ^ 2) with hR_real_def
  have hR_real_nn : 0 ≤ R_real := div_nonneg hN_z_nn (le_of_lt hTL_pos)
  set R : NNReal := Real.toNNReal R_real with hR_def
  have hR_eq : (R : ℝ) = R_real := Real.coe_toNNReal _ hR_real_nn
  -- M_real := ‖gradW(0)‖ + L · (R + ‖z.1‖ + M_ρ)
  set M_real : ℝ :=
    ‖gradW 0‖ + (L : ℝ) * ((R : ℝ) + ‖z.1‖ + M_ρ) with hM_real_def
  have hM_real_nn : 0 ≤ M_real := by
    have : 0 ≤ (L : ℝ) * ((R : ℝ) + ‖z.1‖ + M_ρ) := by
      apply mul_nonneg L.coe_nonneg
      have hR_nn : 0 ≤ (R : ℝ) := NNReal.coe_nonneg R
      have : 0 ≤ ‖z.1‖ := norm_nonneg _
      linarith
    linarith [norm_nonneg (gradW 0)]
  set M : NNReal := Real.toNNReal M_real with hM_def
  have hM_eq : (M : ℝ) = M_real := Real.coe_toNNReal _ hM_real_nn
  -- ============================================================
  -- Verify hR_local: 2·a + (‖z.2‖ + a/2)·T + M·T² ≤ R
  -- with a = 1.
  -- After substitution: this is N_z ≤ R = R_real * (1 - L·T²) + correction.
  -- The construction gives R · (1 - L·T²) = N_z, so the inequality is tight.
  -- ============================================================
  have ha : (0 : NNReal) < 1 := by norm_num
  have hR_local : 2 * ((1 : NNReal) : ℝ)
                  + (‖z.2‖ + ((1 : NNReal) : ℝ) / 2) * T
                  + (M : ℝ) * T ^ 2 ≤ R := by
    -- Prove the equivalent inequality in real form, then transport via hM_eq, hR_eq.
    have hne : 1 - (L : ℝ) * T ^ 2 ≠ 0 := ne_of_gt hTL_pos
    have h_R_rel : R_real * (1 - (L : ℝ) * T ^ 2) = N_z := by
      simp only [hR_real_def]
      field_simp
    have h_LHS_eq : (2 : ℝ) + (‖z.2‖ + 1 / 2) * T + M_real * T ^ 2
                  = N_z + (L : ℝ) * R_real * T ^ 2 := by
      -- M_real contains (R : ℝ); substitute via hR_eq before ring.
      simp only [hM_real_def, hN_z_def, hR_eq]; ring
    have h_target_eq : N_z + (L : ℝ) * R_real * T ^ 2 = R_real := by
      nlinarith [h_R_rel]
    have h_real : (2 : ℝ) + (‖z.2‖ + 1 / 2) * T + M_real * T ^ 2 ≤ R_real := by
      linarith [h_LHS_eq, h_target_eq]
    -- Cast to NNReal form: ((1 : NNReal) : ℝ) = 1 and 2 * 1 = 2.
    have h_one : ((1 : NNReal) : ℝ) = 1 := by norm_cast
    rw [hM_eq, hR_eq, h_one]
    linarith [h_real]
  -- ============================================================
  -- Verify hbound_local: force bound on closedBall z.1 R for t ∈ Icc 0 T.
  -- Uses ‖conv(ρ t, x)‖ ≤ ‖gradW(0)‖ + L · ∫‖x-y‖ dρ_t ≤ ‖gradW(0)‖ + L·(‖x‖ + M_ρ).
  -- For x ∈ closedBall z.1 R: ‖x‖ ≤ R + ‖z.1‖, so bound ≤ M_real = M.
  -- ============================================================
  have hbound_local : ∀ t ∈ Set.Icc (0 : ℝ) T,
                     ∀ x ∈ Metric.closedBall z.1 (R : ℝ),
                     ‖convolveFunctionMeasure gradW (ρ t) x‖ ≤ M := by
    intro t _ht x hx
    have hx_norm : ‖x‖ ≤ (R : ℝ) + ‖z.1‖ := by
      have hdx : dist x z.1 ≤ (R : ℝ) := hx
      have hxz : ‖x - z.1‖ ≤ (R : ℝ) := by rwa [dist_eq_norm] at hdx
      have h_tri := norm_add_le (x - z.1) z.1
      rw [sub_add_cancel] at h_tri
      linarith
    -- ‖∫ gradW(x - y) dρ_t(y)‖ ≤ ∫ ‖gradW(x - y)‖ dρ_t(y).
    have h_sub_int : Integrable (fun y => ‖x - y‖) (ρ t) := by
      have habs_meas : AEStronglyMeasurable (fun y : PhysSpace d => ‖x - y‖) (ρ t) :=
        ((aestronglyMeasurable_const (b := x)).sub aestronglyMeasurable_id).norm
      refine Integrable.mono' ((integrable_const ‖x‖).add (h_y_int t)) habs_meas ?_
      refine Filter.Eventually.of_forall fun y => ?_
      simp only [Real.norm_of_nonneg (norm_nonneg _)]
      exact norm_sub_le x y
    have h_bnd_int : Integrable (fun y => ‖gradW 0‖ + (L : ℝ) * ‖x - y‖) (ρ t) :=
      (integrable_const _).add (h_sub_int.const_mul _)
    have h_pt : ∀ y : PhysSpace d,
        ‖gradW (x - y)‖ ≤ ‖gradW 0‖ + (L : ℝ) * ‖x - y‖ := by
      intro y
      have hd := hL.dist_le_mul (x - y) 0
      simp only [dist_eq_norm, sub_zero] at hd
      have h_tri : ‖gradW (x - y)‖ ≤ ‖gradW 0‖ + ‖gradW (x - y) - gradW 0‖ := by
        have := norm_add_le (gradW (x - y) - gradW 0) (gradW 0)
        simp only [sub_add_cancel] at this
        linarith
      linarith
    rw [hM_eq, hM_real_def]
    calc ‖convolveFunctionMeasure gradW (ρ t) x‖
        = ‖∫ y, gradW (x - y) ∂(ρ t)‖ := rfl
      _ ≤ ∫ y, ‖gradW (x - y)‖ ∂(ρ t) := norm_integral_le_integral_norm _
      _ ≤ ∫ y, (‖gradW 0‖ + (L : ℝ) * ‖x - y‖) ∂(ρ t) :=
          integral_mono (h_int t x).norm h_bnd_int h_pt
      _ = ‖gradW 0‖ + (L : ℝ) * ∫ y, ‖x - y‖ ∂(ρ t) := by
          rw [integral_add (integrable_const _) (h_sub_int.const_mul _)]
          simp [integral_const, measureReal_def, measure_univ, integral_const_mul]
      _ ≤ ‖gradW 0‖ + (L : ℝ) * (‖x‖ + M_ρ) := by
          have hint_bd : ∫ y, ‖x - y‖ ∂(ρ t) ≤ ‖x‖ + M_ρ := by
            calc ∫ y, ‖x - y‖ ∂(ρ t)
                ≤ ∫ y, (‖x‖ + ‖y‖) ∂(ρ t) :=
                  integral_mono h_sub_int
                    ((integrable_const _).add (h_y_int t))
                    (fun y => norm_sub_le x y)
              _ = ‖x‖ + ∫ y, ‖y‖ ∂(ρ t) := by
                  rw [integral_add (integrable_const _) (h_y_int t)]
                  simp [integral_const, measureReal_def, measure_univ]
              _ ≤ ‖x‖ + M_ρ := by linarith [hM_ρ t]
          have := mul_le_mul_of_nonneg_left hint_bd L.coe_nonneg
          linarith
      _ ≤ ‖gradW 0‖ + (L : ℝ) * ((R : ℝ) + ‖z.1‖ + M_ρ) := by
          have hL_nn : 0 ≤ (L : ℝ) := L.coe_nonneg
          have hMρ_nn : 0 ≤ M_ρ := hM_ρ_nn
          have h_bound : ‖x‖ + M_ρ ≤ (R : ℝ) + ‖z.1‖ + M_ρ := by linarith
          have := mul_le_mul_of_nonneg_left h_bound hL_nn
          linarith
  -- ============================================================
  -- Apply exists_vlasov_characteristicFlow with z₀ = z, a = 1.
  -- ============================================================
  obtain ⟨charX, charV, hflow, h_boundary⟩ :=
    exists_vlasov_characteristicFlow_tight W gradW hgradW L hL
      ρ h_int hρ_cont z 1 ha M T hT R hR_local hbound_local
  -- Extract trajectory at w = z (z is the center of the ball, trivially in it).
  have hz_in : z ∈ Metric.closedBall z (((1 : NNReal) : ℝ) / 2) := by
    rw [Metric.mem_closedBall, dist_self]
    have : ((1 : NNReal) : ℝ) / 2 = (1 : ℝ) / 2 := by push_cast; ring
    linarith
  obtain ⟨hinit, hode_x, hode_v⟩ := hflow
  refine ⟨fun t => (charX t z, charV t z), ?_, ?_, ?_⟩
  · -- γ 0 = z
    have h0 := hinit z hz_in
    exact Prod.ext h0.1 h0.2
  · -- ODE on Ioo 0 T.
    intro t ht
    exact ⟨hode_x t ht z hz_in, hode_v t ht z hz_in⟩
  · -- Boundary regularity on Icc 0 T: lifted from the per-ball flow's
    -- enriched conjunct h_boundary.
    intro t ht
    exact h_boundary z hz_in t ht

/-- **True global-in-z characteristic flow on a small-T interval.**

For `L · T² < 1`, produces a characteristic flow `(charX, charV)` defined
for *every* `z : PhaseSpace d` (not just z in a ball), satisfying the Vlasov
ODE on `Ioo 0 T`.

This is the foundation the Φ pushforward construction depends on; the
forward-iteration continuation extends to arbitrary T via shifted-initial-data
iteration.

**Architecture**: per-z application of `exists_vlasov_characteristicFlow`
with `z₀ = z, a = 1` (via `exists_vlasov_trajectory` helper), bundled
into a global flow via `Classical.choose`.  See helper's docstring for the
algebraic R(z), M(z) computation.

**Measurability**: NOT exposed.  The per-z Classical.choose bundling
doesn't propagate continuity-in-z.  A measurable variant
(`exists_vlasov_characteristicFlow_global_on_ball_measurable`) covers
the analogous question for the ball-localized flow; a parallel
`_global_smallT_measurable` companion can be added when needed. -/
theorem exists_vlasov_characteristicFlow_global_smallT
    {d : ℕ} [NeZero d]
    (W : PhysSpace d → ℝ)
    (gradW : PhysSpace d → PhysSpace d)
    (hgradW : ∀ x, gradW x = gradient W x)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d))
    [∀ t, IsProbabilityMeasure (ρ t)]
    (h_int : ∀ t (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ t))
    (hρ_cont : ∀ x : PhysSpace d,
      Continuous (fun t => convolveFunctionMeasure gradW (ρ t) x))
    (h_y_int : ∀ t, Integrable (fun y : PhysSpace d => ‖y‖) (ρ t))
    (M_ρ : ℝ) (hM_ρ_nn : 0 ≤ M_ρ)
    (hM_ρ : ∀ t, ∫ y, ‖y‖ ∂(ρ t) ≤ M_ρ)
    (T : ℝ) (hT : 0 ≤ T)
    (hTL_PL : LocalSmallnessPLBuffer L T) :
    ∃ (charX charV : ℝ → PhaseSpace d → PhysSpace d),
      IsCharacteristicFlowOn gradW ρ charX charV (Set.Ioo 0 T) Set.univ ∧
      -- **Boundary regularity bundle**: expose the HasDerivWithinAt on
      -- `Icc 0 T` for every z and t ∈ Icc 0 T.  Lifted from the per-z
      -- trajectory's boundary-regularity conjunct.
      (∀ z : PhaseSpace d, ∀ t ∈ Set.Icc (0 : ℝ) T,
        HasDerivWithinAt (fun s => charX s z) (charV t z) (Set.Icc 0 T) t ∧
        HasDerivWithinAt (fun s => charV s z)
          (-(convolveFunctionMeasure gradW (ρ t) (charX t z)))
          (Set.Icc 0 T) t) := by
  classical
  -- Per-z trajectory existence (with boundary regularity).
  have h_perZ : ∀ z : PhaseSpace d, ∃ γ : ℝ → PhaseSpace d,
      γ 0 = z ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) T,
        HasDerivAt (fun s => (γ s).1) (γ t).2 t ∧
        HasDerivAt (fun s => (γ s).2)
          (-(convolveFunctionMeasure gradW (ρ t) (γ t).1)) t) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) T,
        HasDerivWithinAt (fun s => (γ s).1) (γ t).2 (Set.Icc 0 T) t ∧
        HasDerivWithinAt (fun s => (γ s).2)
          (-(convolveFunctionMeasure gradW (ρ t) (γ t).1)) (Set.Icc 0 T) t) := by
    intro z
    exact exists_vlasov_trajectory W gradW hgradW L hL ρ h_int hρ_cont
      h_y_int M_ρ hM_ρ_nn hM_ρ T hT hTL_PL z
  -- Bundle via Classical.choose.
  let γ_func : PhaseSpace d → ℝ → PhaseSpace d := fun z =>
    Classical.choose (h_perZ z)
  refine ⟨fun t z => (γ_func z t).1, fun t z => (γ_func z t).2,
         ⟨?_, ?_, ?_⟩, ?_⟩
  · -- (i) Initial condition: γ_func z 0 = z for all z (Set.univ).
    intro z _
    have h_init : γ_func z 0 = z := (Classical.choose_spec (h_perZ z)).1
    exact ⟨congrArg Prod.fst h_init, congrArg Prod.snd h_init⟩
  · -- (ii) Position ODE at t ∈ Ioo 0 T.
    intro t ht z _
    exact ((Classical.choose_spec (h_perZ z)).2.1 t ht).1
  · -- (iii) Velocity ODE at t ∈ Ioo 0 T.
    intro t ht z _
    exact ((Classical.choose_spec (h_perZ z)).2.1 t ht).2
  · -- (iv) Boundary regularity bundle on Icc 0 T for every z.
    intro z t ht
    exact (Classical.choose_spec (h_perZ z)).2.2 t ht

/-! ## The pushforward operator Φ and its well-definedness -/
-- The pushforward operator Φ takes a characteristic flow `charX : ℝ → PhaseSpace
-- d → PhysSpace d` and an initial measure `f₀ : Measure (PhaseSpace d)`, and
-- produces a time-indexed curve of measures on `PhysSpace d` via
-- `Φ charX f₀ t := Measure.map (fun z => charX t z) f₀`.
--
-- Its well-definedness comprises:
--   * `Phi`: the bare definition.
--   * `Phi_isProbabilityMeasure`: under AEMeasurable hypothesis.
--   * `Phi_hasMoment_le`: under measurability + per-z growth-bound hypothesis.
--   * `Phi_yIntegrable`: derived from hasMoment_le.
--   * `Phi_hW1Cont`: W₁-continuity via DCT.
--   * `PhiAsVlasovMeasureCurve`: the full bundling into a `VlasovMeasureCurve d T M`.
--
-- The measurability + growth-bound hypotheses are passed through as inputs; their
-- discharge happens at the call site (the Picard iteration), where the concrete
-- flow is constructed and the hypotheses follow from the construction.

/-- The Φ pushforward operator: maps a characteristic flow + initial measure to
the time-indexed pushforward measure on `PhysSpace d`. -/
noncomputable def Phi {d : ℕ}
    (charX : ℝ → PhaseSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d)) : ℝ → Measure (PhysSpace d) :=
  fun t => Measure.map (fun z => charX t z) f₀

/-- `Phi charX f₀ t` is a probability measure when `charX t` is AE-measurable
wrt `f₀`. -/
theorem Phi_isProbabilityMeasure {d : ℕ}
    (charX : ℝ → PhaseSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (h_meas : ∀ t, AEMeasurable (fun z : PhaseSpace d => charX t z) f₀)
    (t : ℝ) :
    IsProbabilityMeasure (Phi charX f₀ t) := by
  unfold Phi
  exact MeasureTheory.Measure.isProbabilityMeasure_map (h_meas t)

/-- Uniform first-moment bound on `Phi charX f₀` under a per-z position growth
hypothesis `‖charX t z‖ ≤ C_T · (‖z‖ + 1)`.

Composes `integral_map` (which exchanges the pushforward) with the pointwise
growth bound + linearity of integration over `f₀`. -/
theorem Phi_hasMoment_le {d : ℕ}
    (charX : ℝ → PhaseSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (h_meas : ∀ t, AEMeasurable (fun z : PhaseSpace d => charX t z) f₀)
    (T : ℝ) (_hT : 0 ≤ T)
    (C_T : ℝ) (hC_T_nn : 0 ≤ C_T)
    (h_growth : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ z : PhaseSpace d,
      ‖charX t z‖ ≤ C_T * (‖z‖ + 1))
    (h_f₀_int : Integrable (fun z : PhaseSpace d => ‖z‖) f₀)
    (M_f₀ : ℝ) (hM_f₀ : ∫ z, ‖z‖ ∂f₀ ≤ M_f₀)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ∫ y, ‖y‖ ∂(Phi charX f₀ t) ≤ C_T * (M_f₀ + 1) := by
  unfold Phi
  -- ∫ y ‖y‖ ∂(Measure.map (charX t) f₀) = ∫ z ‖charX t z‖ ∂f₀  via integral_map.
  rw [integral_map (h_meas t) (Continuous.aestronglyMeasurable continuous_norm)]
  -- ≤ ∫ z (C_T·(‖z‖+1)) ∂f₀  via pointwise growth bound.
  have h_growth_t := h_growth t ht
  -- Both sides integrable; use integral_mono.
  have h_growth_int : Integrable (fun z : PhaseSpace d => C_T * (‖z‖ + 1)) f₀ := by
    have : Integrable (fun z : PhaseSpace d => ‖z‖ + 1) f₀ :=
      h_f₀_int.add (integrable_const _)
    exact this.const_mul _
  have h_lhs_int : Integrable (fun z : PhaseSpace d => ‖charX t z‖) f₀ := by
    refine Integrable.mono' h_growth_int ((h_meas t).norm.aestronglyMeasurable) ?_
    refine Filter.Eventually.of_forall fun z => ?_
    have hbd := h_growth_t z
    have h_rhs_nn : 0 ≤ C_T * (‖z‖ + 1) := by
      apply mul_nonneg hC_T_nn
      linarith [norm_nonneg z]
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    linarith
  calc ∫ z, ‖charX t z‖ ∂f₀
      ≤ ∫ z, C_T * (‖z‖ + 1) ∂f₀ :=
        integral_mono h_lhs_int h_growth_int (fun z => h_growth_t z)
    _ = C_T * ∫ z, (‖z‖ + 1) ∂f₀ := by
        rw [integral_const_mul]
    _ = C_T * (∫ z, ‖z‖ ∂f₀ + 1) := by
        congr 1
        rw [integral_add h_f₀_int (integrable_const _)]
        simp [integral_const, measureReal_def, measure_univ]
    _ ≤ C_T * (M_f₀ + 1) := by
        have h_M_nn : 0 ≤ M_f₀ + 1 := by
          have : 0 ≤ ∫ z, ‖z‖ ∂f₀ := integral_nonneg (fun _ => norm_nonneg _)
          linarith [hM_f₀]
        apply mul_le_mul_of_nonneg_left _ hC_T_nn
        linarith

/-- `‖·‖` is integrable wrt `Phi charX f₀ t` under the growth hypothesis. -/
theorem Phi_yIntegrable {d : ℕ}
    (charX : ℝ → PhaseSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (h_meas : ∀ t, AEMeasurable (fun z : PhaseSpace d => charX t z) f₀)
    (T : ℝ) (_hT : 0 ≤ T)
    (C_T : ℝ) (_hC_T_nn : 0 ≤ C_T)
    (h_growth : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ z : PhaseSpace d,
      ‖charX t z‖ ≤ C_T * (‖z‖ + 1))
    (h_f₀_int : Integrable (fun z : PhaseSpace d => ‖z‖) f₀)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    Integrable (fun y : PhysSpace d => ‖y‖) (Phi charX f₀ t) := by
  -- Integrable wrt pushforward iff ‖·‖ ∘ (charX t) is integrable wrt f₀.
  unfold Phi
  rw [integrable_map_measure (Continuous.aestronglyMeasurable continuous_norm)
      (h_meas t)]
  -- Now integrable wrt f₀.
  have h_growth_t := h_growth t ht
  have h_growth_int : Integrable (fun z : PhaseSpace d => C_T * (‖z‖ + 1)) f₀ := by
    have : Integrable (fun z : PhaseSpace d => ‖z‖ + 1) f₀ :=
      h_f₀_int.add (integrable_const _)
    exact this.const_mul _
  refine Integrable.mono' h_growth_int ?_ ?_
  · -- AEStronglyMeasurable of ‖·‖ ∘ charX t.
    exact ((h_meas t).aestronglyMeasurable.norm)
  · refine Filter.Eventually.of_forall fun z => ?_
    have hbd := h_growth_t z
    -- Goal shape: ‖((fun a => ‖a‖) ∘ (fun z => charX t z)) z‖ ≤ C_T * (‖z‖ + 1).
    -- The composition simplifies to ‖‖charX t z‖‖, then Real.norm_of_nonneg.
    simp only [Function.comp_apply]
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact hbd

/-- **W₁ bound on Φ pushforwards via 1-Lipschitz test functions.**

For any two time points `s, t`, the Wasserstein-1 distance between
`Phi charX f₀ s` and `Phi charX f₀ t` is bounded by the integral
`∫ z, ‖charX s z - charX t z‖ ∂f₀`.

**Proof strategy** (KR-dual direct): for each 1-Lipschitz `φ : PhysSpace d → ℝ`,
`integral_map` converts `∫ φ d(charX_·)#f₀` to `∫ z, φ(charX_· z) ∂f₀`.
The integral diff is bounded pointwise by `‖charX s z - charX t z‖` (1-Lipschitz
of φ), then by integral monotonicity.

**Architectural note**: `wasserstein1_pushforward_le_iInf` (`Coupling.lean`)
requires endomaps `Φ Ψ : α → α`.  Our `charX t : PhaseSpace d → PhysSpace d`
is cross-type, so we work directly with the KR-dual sup — cleaner than
re-deriving the coupling theory.

All `Integrable.mono'` dominator facts are built as named `have` statements
before the call (no inline `?_`).  The `integrable_map_measure` bridge uses
`.mpr` to handle the `g ∘ f` ↔ `fun z => g (f z)` syntactic mismatch.

Used by `Phi_hW1Cont` to bound W₁(Φ_s, Φ_t) by an integral that DCT controls
as `t → s`. -/
theorem wasserstein1_Phi_le_integral_diff {d : ℕ}
    (charX : ℝ → PhaseSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (h_meas : ∀ t, AEMeasurable (fun z : PhaseSpace d => charX t z) f₀)
    -- ‖charX t z‖ integrable wrt f₀ for each t.
    (h_int_charX : ∀ t, Integrable (fun z : PhaseSpace d => ‖charX t z‖) f₀)
    (s t : ℝ)
    -- ‖charX s z - charX t z‖ integrable wrt f₀ (follows from h_int_charX s, t + triangle).
    (h_diff_int : Integrable (fun z : PhaseSpace d => ‖charX s z - charX t z‖) f₀) :
    wasserstein1 (Phi charX f₀ s) (Phi charX f₀ t) ≤
      ENNReal.ofReal (∫ z, ‖charX s z - charX t z‖ ∂f₀) := by
  simp only [wasserstein1_eq_iSup_lipschitz]
  unfold Phi
  refine iSup_le fun φ => iSup_le fun hφ => ?_
  apply ENNReal.ofReal_le_ofReal
  -- ============================================================
  -- Setup: φ is 1-Lipschitz; AEStronglyMeasurable wrt each pushforward.
  -- ============================================================
  have hφ_cont : Continuous φ := hφ.continuous
  have hφ_meas_νs : AEStronglyMeasurable φ (Measure.map (fun z => charX s z) f₀) :=
    hφ_cont.aestronglyMeasurable
  have hφ_meas_νt : AEStronglyMeasurable φ (Measure.map (fun z => charX t z) f₀) :=
    hφ_cont.aestronglyMeasurable
  -- ============================================================
  -- 1-Lipschitz dominator: |φ y| ≤ |φ 0| + ‖y‖.
  -- ============================================================
  have hφ_abs_bound : ∀ y : PhysSpace d, |φ y| ≤ |φ 0| + ‖y‖ := fun y => by
    have h_lip := hφ.dist_le_mul y 0
    rw [Real.dist_eq, dist_zero_right, NNReal.coe_one, one_mul] at h_lip
    calc |φ y| = |(φ y - φ 0) + φ 0| := by ring_nf
      _ ≤ |φ y - φ 0| + |φ 0| := abs_add_le _ _
      _ ≤ ‖y‖ + |φ 0| := by linarith
      _ = |φ 0| + ‖y‖ := by ring
  -- ============================================================
  -- EXPLICIT DOMINATOR CONSTRUCTION (CLAUDE.md L7).
  -- Build h_norm_int_νs and h_norm_int_νt via `.mpr` (CLAUDE.md L8) —
  -- this avoids the `g ∘ f` ↔ `fun z => g (f z)` rewrite mismatch.
  -- ============================================================
  have h_norm_int_νs : Integrable (fun y : PhysSpace d => ‖y‖)
      (Measure.map (fun z => charX s z) f₀) :=
    (integrable_map_measure (Continuous.aestronglyMeasurable continuous_norm)
      (h_meas s)).mpr (h_int_charX s)
  have h_norm_int_νt : Integrable (fun y : PhysSpace d => ‖y‖)
      (Measure.map (fun z => charX t z) f₀) :=
    (integrable_map_measure (Continuous.aestronglyMeasurable continuous_norm)
      (h_meas t)).mpr (h_int_charX t)
  -- Dominator `|φ 0| + ‖y‖` integrable wrt each pushforward.
  have h_dom_νs : Integrable (fun y : PhysSpace d => |φ 0| + ‖y‖)
      (Measure.map (fun z => charX s z) f₀) :=
    (integrable_const _).add h_norm_int_νs
  have h_dom_νt : Integrable (fun y : PhysSpace d => |φ 0| + ‖y‖)
      (Measure.map (fun z => charX t z) f₀) :=
    (integrable_const _).add h_norm_int_νt
  -- φ integrable wrt each pushforward (via `Integrable.mono'` with explicit dominator).
  have hφ_int_νs : Integrable φ (Measure.map (fun z => charX s z) f₀) := by
    refine Integrable.mono' h_dom_νs hφ_meas_νs ?_
    refine Filter.Eventually.of_forall fun y => ?_
    have h_dom_nn : 0 ≤ |φ 0| + ‖y‖ :=
      add_nonneg (abs_nonneg _) (norm_nonneg _)
    rw [Real.norm_eq_abs]
    exact hφ_abs_bound y
  have hφ_int_νt : Integrable φ (Measure.map (fun z => charX t z) f₀) := by
    refine Integrable.mono' h_dom_νt hφ_meas_νt ?_
    refine Filter.Eventually.of_forall fun y => ?_
    have h_dom_nn : 0 ≤ |φ 0| + ‖y‖ :=
      add_nonneg (abs_nonneg _) (norm_nonneg _)
    rw [Real.norm_eq_abs]
    exact hφ_abs_bound y
  -- ============================================================
  -- Convert pushforward integrals via `integral_map`.
  -- The RHS of `integral_map` is point-full `f (g x)` (NOT `(f ∘ g) x`),
  -- so no L8 bridge needed here.
  -- ============================================================
  rw [integral_map (h_meas s) hφ_meas_νs,
      integral_map (h_meas t) hφ_meas_νt]
  -- Goal: ∫ z, φ (charX s z) ∂f₀ - ∫ z, φ (charX t z) ∂f₀
  --        ≤ ∫ z, ‖charX s z - charX t z‖ ∂f₀.
  -- ============================================================
  -- Pull-back integrability of `fun z => φ (charX · z)` to wrt f₀ via `.mp`.
  -- ============================================================
  have hφ_comp_int_s : Integrable (fun z : PhaseSpace d => φ (charX s z)) f₀ :=
    (integrable_map_measure hφ_meas_νs (h_meas s)).mp hφ_int_νs
  have hφ_comp_int_t : Integrable (fun z : PhaseSpace d => φ (charX t z)) f₀ :=
    (integrable_map_measure hφ_meas_νt (h_meas t)).mp hφ_int_νt
  -- Combine into single integral; bound by Lipschitz inequality.
  rw [← integral_sub hφ_comp_int_s hφ_comp_int_t]
  have h_pt : ∀ z : PhaseSpace d,
      φ (charX s z) - φ (charX t z) ≤ ‖charX s z - charX t z‖ := fun z => by
    have h_lip := hφ.dist_le_mul (charX s z) (charX t z)
    rw [Real.dist_eq, dist_eq_norm, NNReal.coe_one, one_mul] at h_lip
    -- h_lip : |φ (charX s z) - φ (charX t z)| ≤ ‖charX s z - charX t z‖.
    linarith [abs_le.mp h_lip |>.2]
  exact integral_mono (hφ_comp_int_s.sub hφ_comp_int_t) h_diff_int h_pt

/-- **DCT step — the integral `∫ z, ‖charX s z - charX t z‖ ∂f₀`
tends to 0 as `t → s` within `Icc 0 T`.**

Combines pointwise continuity `t ↦ charX t z` (from the flow's HasDerivAt
→ ContinuousAt) with a uniform dominator `2·C_T·(‖z‖+1)` (from the per-z
growth bound) via Mathlib's filter-DCT.  The dominator integrability is
built as a named `have` before the DCT call. -/
theorem Phi_integral_diff_tendsto_zero {d : ℕ}
    (charX : ℝ → PhaseSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (h_meas : ∀ t, AEMeasurable (fun z : PhaseSpace d => charX t z) f₀)
    (T : ℝ) (_hT : 0 ≤ T)
    (C_T : ℝ) (hC_T_nn : 0 ≤ C_T)
    (h_growth : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ z : PhaseSpace d,
      ‖charX t z‖ ≤ C_T * (‖z‖ + 1))
    (h_f₀_int : Integrable (fun z : PhaseSpace d => ‖z‖) f₀)
    -- Continuity of t ↦ charX t z at base s (from HasDerivAt).
    (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) T)
    (h_charX_cont : ∀ z, ContinuousWithinAt (fun t => charX t z) (Set.Icc 0 T) s) :
    Filter.Tendsto (fun t => ∫ z, ‖charX s z - charX t z‖ ∂f₀)
      (nhdsWithin s (Set.Icc 0 T)) (nhds 0) := by
  -- ============================================================
  -- Dominator: `bound z := 2 * C_T * (‖z‖ + 1)` integrable wrt f₀.
  -- ============================================================
  set bound : PhaseSpace d → ℝ :=
    fun z => 2 * C_T * (‖z‖ + 1) with hbound_def
  have h_bound_int : Integrable bound f₀ := by
    have h1 : Integrable (fun z : PhaseSpace d => ‖z‖ + 1) f₀ :=
      h_f₀_int.add (integrable_const _)
    exact h1.const_mul _
  -- ============================================================
  -- AE strong measurability of (fun z => ‖charX s z - charX t z‖) wrt f₀, eventually in t.
  -- ============================================================
  have h_F_meas : ∀ᶠ t in nhdsWithin s (Set.Icc 0 T),
      AEStronglyMeasurable (fun z : PhaseSpace d => ‖charX s z - charX t z‖) f₀ := by
    refine Filter.Eventually.of_forall fun t => ?_
    exact ((h_meas s).sub (h_meas t)).norm.aestronglyMeasurable
  -- ============================================================
  -- Pointwise bound: ‖‖charX s z - charX t z‖‖ ≤ bound z eventually.
  -- ============================================================
  have h_F_bound : ∀ᶠ t in nhdsWithin s (Set.Icc 0 T),
      ∀ᵐ z ∂f₀, ‖‖charX s z - charX t z‖‖ ≤ bound z := by
    refine Filter.eventually_iff_exists_mem.mpr ⟨Set.Icc 0 T, ?_, ?_⟩
    · exact self_mem_nhdsWithin
    · intro t ht
      refine Filter.Eventually.of_forall fun z => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      have h_tri := norm_sub_le (charX s z) (charX t z)
      have h_s := h_growth s hs z
      have h_t := h_growth t ht z
      have h_C_nn_2 : 0 ≤ 2 * C_T := by linarith
      have hz_nn : 0 ≤ ‖z‖ + 1 := by linarith [norm_nonneg z]
      calc ‖charX s z - charX t z‖
          ≤ ‖charX s z‖ + ‖charX t z‖ := h_tri
        _ ≤ C_T * (‖z‖ + 1) + C_T * (‖z‖ + 1) := by linarith
        _ = 2 * C_T * (‖z‖ + 1) := by ring
  -- ============================================================
  -- Pointwise limit: ‖charX s z - charX t z‖ → 0 as t → s within Icc 0 T.
  -- ============================================================
  have h_F_lim : ∀ᵐ z ∂f₀, Filter.Tendsto
      (fun t => ‖charX s z - charX t z‖) (nhdsWithin s (Set.Icc 0 T)) (nhds 0) := by
    refine Filter.Eventually.of_forall fun z => ?_
    -- t ↦ charX s z - charX t z → 0 as t → s, because charX(·) z → charX s z.
    have h_tendsto : Filter.Tendsto (fun t => charX t z) (nhdsWithin s (Set.Icc 0 T))
                       (nhds (charX s z)) := h_charX_cont z
    have h_sub : Filter.Tendsto (fun t => charX s z - charX t z)
                   (nhdsWithin s (Set.Icc 0 T)) (nhds 0) := by
      have h_cancel : (charX s z - charX s z : PhysSpace d) = 0 := sub_self _
      rw [← h_cancel]
      exact (tendsto_const_nhds (x := charX s z)).sub h_tendsto
    have h_norm_tendsto :
        Filter.Tendsto (fun t => ‖charX s z - charX t z‖)
          (nhdsWithin s (Set.Icc 0 T)) (nhds ‖(0 : PhysSpace d)‖) :=
      (continuous_norm.tendsto 0).comp h_sub
    simpa using h_norm_tendsto
  -- ============================================================
  -- Apply Mathlib's filter-DCT.
  -- ============================================================
  have h_dct := MeasureTheory.tendsto_integral_filter_of_dominated_convergence (μ := f₀)
    bound h_F_meas h_F_bound h_bound_int h_F_lim
  -- h_dct : Tendsto (fun t => ∫ z, ‖charX s z - charX t z‖ ∂f₀)
  --   (nhdsWithin s (Icc 0 T)) (nhds (∫ z, 0 ∂f₀))
  -- ∫ z, 0 ∂f₀ = 0
  simp only [integral_zero] at h_dct
  exact h_dct

/-- **W₁-continuity of `t ↦ Phi charX f₀ t` at every base point `s ∈ Icc 0 T`.**

Composes the W₁ bound (`wasserstein1_Phi_le_integral_diff`) with the DCT step
(`Phi_integral_diff_tendsto_zero`) to conclude that
`(wasserstein1 (Phi charX f₀ s) (Phi charX f₀ t)).toReal → 0` as `t → s`. -/
theorem Phi_hW1Cont {d : ℕ}
    (charX : ℝ → PhaseSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (h_meas : ∀ t, AEMeasurable (fun z : PhaseSpace d => charX t z) f₀)
    (h_int_charX : ∀ t, Integrable (fun z : PhaseSpace d => ‖charX t z‖) f₀)
    (T : ℝ) (hT : 0 ≤ T)
    (C_T : ℝ) (hC_T_nn : 0 ≤ C_T)
    (h_growth : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ z : PhaseSpace d,
      ‖charX t z‖ ≤ C_T * (‖z‖ + 1))
    (h_f₀_int : Integrable (fun z : PhaseSpace d => ‖z‖) f₀)
    (h_charX_cont : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ z,
      ContinuousWithinAt (fun t => charX t z) (Set.Icc 0 T) s) :
    ∀ s ∈ Set.Icc (0 : ℝ) T,
      ContinuousWithinAt
        (fun t => (wasserstein1 (Phi charX f₀ s) (Phi charX f₀ t)).toReal)
        (Set.Icc 0 T) s := by
  intro s hs
  -- ContinuousWithinAt at s ↔ Tendsto · → value-at-s within filter.
  -- Value at t = s: wasserstein1_self = 0.
  rw [ContinuousWithinAt]
  have h_value_at_s : (wasserstein1 (Phi charX f₀ s) (Phi charX f₀ s)).toReal = 0 := by
    rw [wasserstein1_self]; rfl
  rw [h_value_at_s]
  -- DCT gives ∫-tendsto-zero.
  have h_dct := Phi_integral_diff_tendsto_zero charX f₀ h_meas T hT C_T hC_T_nn
    h_growth h_f₀_int s hs (h_charX_cont s hs)
  -- Combine: W₁ bound ⇒ toReal bound ⇒ tendsto-zero.
  -- Strategy: bound the W₁.toReal by the integral via wasserstein1_Phi_le_integral_diff.
  -- Then use squeeze on Tendsto.
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  -- From h_dct: ∃ δ, ∀ t ∈ Icc 0 T, dist t s < δ → |∫ ...| < ε.
  rw [Metric.tendsto_nhdsWithin_nhds] at h_dct
  obtain ⟨δ, hδ_pos, hδ_bd⟩ := h_dct ε hε
  -- Use the same δ.
  refine ⟨δ, hδ_pos, fun t ht hdt => ?_⟩
  -- Goal: dist ((wasserstein1 (Phi s) (Phi t)).toReal) 0 < ε.
  rw [Real.dist_eq, sub_zero]
  -- |(W₁ s t).toReal| ≤ |∫ ...|.
  haveI hΦs_prob : IsProbabilityMeasure (Phi charX f₀ s) :=
    Phi_isProbabilityMeasure charX f₀ h_meas s
  haveI hΦt_prob : IsProbabilityMeasure (Phi charX f₀ t) :=
    Phi_isProbabilityMeasure charX f₀ h_meas t
  have h_yint_s : Integrable (fun y : PhysSpace d => ‖y‖) (Phi charX f₀ s) :=
    Phi_yIntegrable charX f₀ h_meas T hT C_T hC_T_nn h_growth h_f₀_int s hs
  have h_yint_t : Integrable (fun y : PhysSpace d => ‖y‖) (Phi charX f₀ t) :=
    Phi_yIntegrable charX f₀ h_meas T hT C_T hC_T_nn h_growth h_f₀_int t ht
  have h_W1_finite : wasserstein1 (Phi charX f₀ s) (Phi charX f₀ t) ≠ ⊤ :=
    wasserstein1_ne_top_of_finite_moment _ _ h_yint_s h_yint_t
  have h_diff_int_t : Integrable (fun z : PhaseSpace d => ‖charX s z - charX t z‖) f₀ := by
    -- Inline the integrability proof to avoid the `Filter.eventually_iff_exists_mem`
    -- destructuring's metavariable mismatch.
    have h_dom_int : Integrable (fun z : PhaseSpace d => 2 * C_T * (‖z‖ + 1)) f₀ :=
      (h_f₀_int.add (integrable_const _)).const_mul _
    refine Integrable.mono' h_dom_int
      (((h_meas s).sub (h_meas t)).norm.aestronglyMeasurable) ?_
    refine Filter.Eventually.of_forall fun z => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    have h_tri := norm_sub_le (charX s z) (charX t z)
    have h_s := h_growth s hs z
    have h_t := h_growth t ht z
    calc ‖charX s z - charX t z‖
        ≤ ‖charX s z‖ + ‖charX t z‖ := h_tri
      _ ≤ C_T * (‖z‖ + 1) + C_T * (‖z‖ + 1) := by linarith
      _ = 2 * C_T * (‖z‖ + 1) := by ring
  have h_W1_le := wasserstein1_Phi_le_integral_diff charX f₀ h_meas h_int_charX
    s t h_diff_int_t
  -- |∫ ‖charX s z - charX t z‖ ∂f₀| < ε from hδ_bd.
  have h_int_bd := hδ_bd ht hdt
  rw [Real.dist_eq, sub_zero] at h_int_bd
  -- Combine: (W₁ s t).toReal ≤ ofReal(∫ ‖...‖).toReal ≤ |∫ ‖...‖| < ε.
  have h_int_nn : 0 ≤ ∫ z, ‖charX s z - charX t z‖ ∂f₀ :=
    integral_nonneg (fun _ => norm_nonneg _)
  have h_toReal_le : (wasserstein1 (Phi charX f₀ s) (Phi charX f₀ t)).toReal ≤
      ∫ z, ‖charX s z - charX t z‖ ∂f₀ := by
    have h_ofReal_eq : (ENNReal.ofReal (∫ z, ‖charX s z - charX t z‖ ∂f₀)).toReal
                      = ∫ z, ‖charX s z - charX t z‖ ∂f₀ := by
      rw [ENNReal.toReal_ofReal h_int_nn]
    rw [← h_ofReal_eq]
    exact ENNReal.toReal_mono ENNReal.ofReal_ne_top h_W1_le
  have h_toReal_nn : 0 ≤ (wasserstein1 (Phi charX f₀ s) (Phi charX f₀ t)).toReal :=
    ENNReal.toReal_nonneg
  rw [abs_of_nonneg h_toReal_nn]
  calc (wasserstein1 (Phi charX f₀ s) (Phi charX f₀ t)).toReal
      ≤ ∫ z, ‖charX s z - charX t z‖ ∂f₀ := h_toReal_le
    _ < ε := by
        have h_abs_eq : |∫ z, ‖charX s z - charX t z‖ ∂f₀|
                      = ∫ z, ‖charX s z - charX t z‖ ∂f₀ := abs_of_nonneg h_int_nn
        linarith [h_int_bd, h_abs_eq.symm.le, abs_nonneg (∫ z, ‖charX s z - charX t z‖ ∂f₀)]

/-- **Full bundling of Φ into a `VlasovMeasureCurve`.**

Given the four hypothesis bundles (measurability, growth, f₀'s integrability,
flow continuity), bundles the three pushforward well-definedness properties +
`Phi_hW1Cont` into a `VlasovMeasureCurve d T M'` where `M' := C_T · (M_f₀ + 1)`.

This is the structured output that the contraction estimate and Banach
iteration consume. -/
noncomputable def PhiAsVlasovMeasureCurve {d : ℕ} [NeZero d]
    (charX : ℝ → PhaseSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (h_meas : ∀ t, AEMeasurable (fun z : PhaseSpace d => charX t z) f₀)
    (h_int_charX : ∀ t, Integrable (fun z : PhaseSpace d => ‖charX t z‖) f₀)
    (T : ℝ) (hT : 0 ≤ T)
    (C_T : ℝ) (hC_T_nn : 0 ≤ C_T)
    (h_growth : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ z : PhaseSpace d,
      ‖charX t z‖ ≤ C_T * (‖z‖ + 1))
    (h_f₀_int : Integrable (fun z : PhaseSpace d => ‖z‖) f₀)
    (M_f₀ : ℝ) (hM_f₀ : ∫ z, ‖z‖ ∂f₀ ≤ M_f₀)
    (h_charX_cont : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ z,
      ContinuousWithinAt (fun t => charX t z) (Set.Icc 0 T) s) :
    VlasovMeasureCurve d T (fun _ => C_T * (M_f₀ + 1)) where
  ρ := Phi charX f₀
  isProb := Phi_isProbabilityMeasure charX f₀ h_meas
  hasMoment := fun t ht =>
    Phi_hasMoment_le charX f₀ h_meas T hT C_T hC_T_nn h_growth h_f₀_int M_f₀ hM_f₀ t ht
  yIntegrable := fun t ht =>
    Phi_yIntegrable charX f₀ h_meas T hT C_T hC_T_nn h_growth h_f₀_int t ht
  hW1Cont :=
    Phi_hW1Cont charX f₀ h_meas h_int_charX T hT C_T hC_T_nn h_growth h_f₀_int
      h_charX_cont

/-- **Measurability of a characteristic flow given Picard-style boundary
regularity.**

Given a flow `(charX, charV)` that:
* matches the initial condition at `t = 0`,
* is continuous in `t` on `Icc 0 T` for each `z` (i.e. Picard-solution
  regularity at the boundary),
* satisfies the Vlasov ODE in `HasDerivWithinAt`-on-`Ico` form,

we prove that for each `t ∈ Icc 0 T`, the map `z ↦ (charX t z, charV t z)`
is Borel-measurable on `PhaseSpace d`.

**Proof strategy** (Gronwall on flow difference, via Mathlib's
`dist_le_of_trajectories_ODE`):  the Vlasov vector field is
`max(1, L)`-Lipschitz uniformly in `t` (`vlasovVectorField_lipschitzWith`),
so two trajectories `f, g : ℝ → PhaseSpace d` starting from `z₁, z₂` satisfy
`dist (f t) (g t) ≤ dist(z₁, z₂) · exp(max(1, L) · t)` for `t ∈ Icc 0 T`.
This is exp(K·t)-Lipschitz-in-`z`, hence continuous in `z`, hence Borel-
measurable.

**Why the boundary regularity is taken as hypothesis**: the flow
construction's `IsCharacteristicFlowOn ... (Ioo 0 T) Set.univ` gives
`HasDerivAt` only on the open interval `Ioo 0 T`.  Mathlib's
`dist_le_of_trajectories_ODE` requires `ContinuousOn` on `Icc 0 T` plus
`HasDerivWithinAt` on `Ico 0 T` (closed at the left endpoint).  The boundary
regularity at `t = 0` is a property of the underlying Picard construction,
not derivable from `IsCharacteristicFlowOn` alone.  The Picard iteration
discharges these hypotheses from the concrete construction.

This is what the Picard construction plugs into the Φ pipeline. -/
theorem charFlow_measurable_via_gronwall
    {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d))
    [∀ t, IsProbabilityMeasure (ρ t)]
    (h_int : ∀ t (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ t))
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (T : ℝ) (_hT : 0 ≤ T)
    (h_init : ∀ z : PhaseSpace d, (charX 0 z, charV 0 z) = z)
    (h_cont_Icc : ∀ z,
      ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc (0 : ℝ) T))
    (h_deriv_Ico : ∀ z, ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt (fun s => (charX s z, charV s z))
        (vlasovVectorField gradW ρ t (charX t z, charV t z))
        (Set.Ici t) t) :
    ∀ t ∈ Set.Icc (0 : ℝ) T,
        Measurable (fun z : PhaseSpace d => (charX t z, charV t z)) := by
  intro t ht
  -- ============================================================
  -- Vector field is max(1, L)-Lipschitz uniformly in t.
  -- ============================================================
  set K : NNReal := max 1 L with hK_def
  have h_vf_lip : ∀ s, LipschitzWith K (vlasovVectorField gradW ρ s) := fun s =>
    vlasovVectorField_lipschitzWith gradW L hL ρ h_int s
  -- ============================================================
  -- Gronwall on flow difference: dist-bound on Icc 0 T.
  -- ============================================================
  have h_dist_bound : ∀ z₁ z₂ : PhaseSpace d,
      dist ((charX t z₁, charV t z₁) : PhaseSpace d) (charX t z₂, charV t z₂) ≤
      dist z₁ z₂ * Real.exp ((K : ℝ) * (t - 0)) := by
    intro z₁ z₂
    -- Apply dist_le_of_trajectories_ODE with f, g = per-z trajectories.
    have h := dist_le_of_trajectories_ODE
      (v := fun s => vlasovVectorField gradW ρ s)
      (f := fun s => (charX s z₁, charV s z₁))
      (g := fun s => (charX s z₂, charV s z₂))
      (K := K) (a := 0) (b := T)
      (δ := dist z₁ z₂)
      h_vf_lip
      (h_cont_Icc z₁) (h_deriv_Ico z₁)
      (h_cont_Icc z₂) (h_deriv_Ico z₂)
      ?_ t ht
    · exact h
    · -- dist (f 0) (g 0) = dist z₁ z₂ via h_init.  Need to beta-reduce first.
      change dist ((charX 0 z₁, charV 0 z₁) : PhaseSpace d) (charX 0 z₂, charV 0 z₂)
           ≤ dist z₁ z₂
      rw [h_init z₁, h_init z₂]
  -- ============================================================
  -- Convert dist-bound to continuity in z via Metric.continuous_iff.
  -- ============================================================
  have h_cont_z : Continuous (fun z : PhaseSpace d => (charX t z, charV t z)) := by
    rw [Metric.continuous_iff]
    intro z₀ ε hε
    -- Lipschitz constant exp(K * t); pick δ := ε / exp(K * t).
    have h_exp_pos : 0 < Real.exp ((K : ℝ) * (t - 0)) := Real.exp_pos _
    refine ⟨ε / Real.exp ((K : ℝ) * (t - 0)), div_pos hε h_exp_pos, ?_⟩
    intro z hz
    -- dist (f z₀) (f z) ≤ exp(K*t) * dist z₀ z < exp(K*t) * (ε / exp(K*t)) = ε.
    have h_bd := h_dist_bound z₀ z
    -- Note: dist_bound gives `dist (f z₀) (f z)`, but `Metric.continuous_iff`
    -- gives `dist z z₀ < δ → dist (f z) (f z₀) < ε`.  Symmetric: use dist_comm.
    rw [dist_comm] at hz
    have h_chain : dist ((charX t z₀, charV t z₀) : PhaseSpace d) (charX t z, charV t z)
                  < ε := by
      calc dist ((charX t z₀, charV t z₀) : PhaseSpace d) (charX t z, charV t z)
          ≤ dist z₀ z * Real.exp ((K : ℝ) * (t - 0)) := h_bd
        _ < (ε / Real.exp ((K : ℝ) * (t - 0))) * Real.exp ((K : ℝ) * (t - 0)) :=
            mul_lt_mul_of_pos_right hz h_exp_pos
        _ = ε := div_mul_cancel₀ ε (ne_of_gt h_exp_pos)
    rwa [dist_comm] at h_chain
  exact h_cont_z.measurable

/-- **Step 0b — the flow's Lipschitz-in-`z` bound (open-interval form).**

Extracted from `charFlow_measurable_via_gronwall_Ioo`'s internal
`h_dist_bound`.  Given the open-interval flow ODE, the characteristic flow
`z ↦ (charX t z, charV t z)` is Lipschitz in the initial datum `z` with
constant `exp((max 1 L) · (t − 0))`, uniformly for `t ∈ [0, T]`.

Same hypotheses as `charFlow_measurable_via_gronwall_Ioo`; the conclusion
is the Grönwall distance bound used by both that lemma (to derive
continuity-in-`z` hence measurability) and the moment-free dominator in
`dobrushin_uniqueness_On`. -/
theorem charFlow_lipschitzInZ_via_gronwall_Ioo
    {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d))
    [∀ t, IsProbabilityMeasure (ρ t)]
    (h_int : ∀ t (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ t))
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (T : ℝ) (hT : 0 ≤ T)
    (h_init : ∀ z : PhaseSpace d, (charX 0 z, charV 0 z) = z)
    (h_cont_Icc : ∀ z,
      ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc (0 : ℝ) T))
    (h_deriv_Ioo : ∀ z, ∀ t ∈ Set.Ioo (0 : ℝ) T,
      HasDerivWithinAt (fun s => (charX s z, charV s z))
        (vlasovVectorField gradW ρ t (charX t z, charV t z))
        (Set.Ici t) t) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ z₁ z₂ : PhaseSpace d,
        dist ((charX t z₁, charV t z₁) : PhaseSpace d) (charX t z₂, charV t z₂) ≤
        dist z₁ z₂ * Real.exp (((max 1 L : NNReal) : ℝ) * (t - 0)) := by
  intro t ht
  -- Vector field is max(1, L)-Lipschitz uniformly in s.
  set K : NNReal := max 1 L with hK_def
  have h_vf_lip : ∀ s, LipschitzWith K (vlasovVectorField gradW ρ s) := fun s =>
    vlasovVectorField_lipschitzWith gradW L hL ρ h_int s
  intro z₁ z₂
  -- Abbreviations for the two per-z trajectories.
  set F : ℝ → PhaseSpace d := fun s => (charX s z₁, charV s z₁) with hF_def
  set G : ℝ → PhaseSpace d := fun s => (charX s z₂, charV s z₂) with hG_def
  -- Split on whether t = 0 or 0 < t.
  rcases eq_or_lt_of_le ht.1 with h_t0 | h_pos
  · -- t = 0: both trajectories evaluate to their initial conditions.
    subst h_t0
    simp only [h_init z₁, h_init z₂, sub_self, mul_zero,
      Real.exp_zero, mul_one, le_refl]
  · -- 0 < t: take the s₀ → 0⁺ limit of Grönwall bounds on [s₀, t].
    -- Per-s₀ Grönwall bound on the window [s₀, t] ⊆ [0, T].
    have h_perS0 : ∀ s₀ ∈ Set.Ioo (0 : ℝ) t,
        dist (F t) (G t) ≤ dist (F s₀) (G s₀) * Real.exp ((K : ℝ) * (t - s₀)) := by
      intro s₀ hs₀
      -- Window inclusions.
      have hsub_Ico : Set.Ico s₀ t ⊆ Set.Ioo (0 : ℝ) T := fun s hs =>
        ⟨lt_of_lt_of_le hs₀.1 hs.1, lt_of_lt_of_le hs.2 ht.2⟩
      have hsub_Icc : Set.Icc s₀ t ⊆ Set.Icc (0 : ℝ) T :=
        Set.Icc_subset_Icc hs₀.1.le ht.2
      have h := dist_le_of_trajectories_ODE
        (v := fun s => vlasovVectorField gradW ρ s)
        (f := F) (g := G)
        (K := K) (a := s₀) (b := t)
        (δ := dist (F s₀) (G s₀))
        h_vf_lip
        ((h_cont_Icc z₁).mono hsub_Icc)
        (fun s hs => h_deriv_Ioo z₁ s (hsub_Ico hs))
        ((h_cont_Icc z₂).mono hsub_Icc)
        (fun s hs => h_deriv_Ioo z₂ s (hsub_Ico hs))
        (le_refl _) t ⟨hs₀.2.le, le_refl t⟩
      exact h
    -- The filter 𝓝[Ioo 0 t] 0 is NeBot since 0 < t.
    have : (nhdsWithin (0 : ℝ) (Set.Ioo 0 t)).NeBot :=
      left_nhdsWithin_Ioo_neBot h_pos
    -- Tendsto F to z₁ along 𝓝[Ioo 0 t] 0.
    have hIoo_sub_Icc : Set.Ioo (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T := fun s hs =>
      ⟨hs.1.le, le_trans hs.2.le ht.2⟩
    have hF0 : F 0 = z₁ := h_init z₁
    have hG0 : G 0 = z₂ := h_init z₂
    have h_tendsto_F : Filter.Tendsto F (nhdsWithin (0 : ℝ) (Set.Ioo 0 t))
        (nhds z₁) := by
      have hcw : ContinuousWithinAt F (Set.Icc (0 : ℝ) T) 0 :=
        (h_cont_Icc z₁) 0 ⟨le_refl 0, hT⟩
      have : Filter.Tendsto F (nhdsWithin (0 : ℝ) (Set.Icc 0 T)) (nhds (F 0)) :=
        hcw
      rw [hF0] at this
      exact this.mono_left (nhdsWithin_mono 0 hIoo_sub_Icc)
    have h_tendsto_G : Filter.Tendsto G (nhdsWithin (0 : ℝ) (Set.Ioo 0 t))
        (nhds z₂) := by
      have hcw : ContinuousWithinAt G (Set.Icc (0 : ℝ) T) 0 :=
        (h_cont_Icc z₂) 0 ⟨le_refl 0, hT⟩
      have : Filter.Tendsto G (nhdsWithin (0 : ℝ) (Set.Icc 0 T)) (nhds (G 0)) :=
        hcw
      rw [hG0] at this
      exact this.mono_left (nhdsWithin_mono 0 hIoo_sub_Icc)
    -- Tendsto of dist (F s₀) (G s₀) to dist z₁ z₂.
    have h_tendsto_dist :
        Filter.Tendsto (fun s₀ => dist (F s₀) (G s₀))
          (nhdsWithin (0 : ℝ) (Set.Ioo 0 t)) (nhds (dist z₁ z₂)) :=
      h_tendsto_F.dist h_tendsto_G
    -- Tendsto of exp(K*(t-s₀)) to exp(K*(t-0)).
    have h_tendsto_exp :
        Filter.Tendsto (fun s₀ => Real.exp ((K : ℝ) * (t - s₀)))
          (nhdsWithin (0 : ℝ) (Set.Ioo 0 t))
          (nhds (Real.exp ((K : ℝ) * (t - 0)))) := by
      have hcont : Continuous (fun s₀ : ℝ => Real.exp ((K : ℝ) * (t - s₀))) := by
        fun_prop
      exact (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
    -- Product of the two limits.
    have h_lim :
        Filter.Tendsto (fun s₀ => dist (F s₀) (G s₀) * Real.exp ((K : ℝ) * (t - s₀)))
          (nhdsWithin (0 : ℝ) (Set.Ioo 0 t))
          (nhds (dist z₁ z₂ * Real.exp ((K : ℝ) * (t - 0)))) :=
      h_tendsto_dist.mul h_tendsto_exp
    -- The per-s₀ bound holds eventually along the filter.
    have h_event :
        ∀ᶠ s₀ in nhdsWithin (0 : ℝ) (Set.Ioo 0 t),
          dist (F t) (G t) ≤ dist (F s₀) (G s₀) * Real.exp ((K : ℝ) * (t - s₀)) :=
      eventually_nhdsWithin_of_forall h_perS0
    -- Pass to the limit.
    exact ge_of_tendsto h_lim h_event

/-- **Open-interval variant of `charFlow_measurable_via_gronwall`.**

Identical to `charFlow_measurable_via_gronwall` except the derivative
hypothesis is on the OPEN interval `Set.Ioo 0 T` instead of the
half-open `Set.Ico 0 T`.  This matches the regularity that an
`IsCharacteristicFlowOn ... (Set.Ioo 0 T)` predicate directly produces
(the ODE holds on the open interval, with the endpoints handled by
continuity).

The proof reuses the per-window Grönwall distance bound, but obtains the
`t = 0` endpoint distance bound by taking a one-sided limit
`s₀ → 0⁺` of the Grönwall bounds on `[s₀, t]` (each of which only needs
the derivative on `Set.Ico s₀ t ⊆ Set.Ioo 0 T`), rather than applying
Grönwall directly on `[0, t]`. -/
theorem charFlow_measurable_via_gronwall_Ioo
    {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d))
    [∀ t, IsProbabilityMeasure (ρ t)]
    (h_int : ∀ t (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ t))
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (T : ℝ) (hT : 0 ≤ T)
    (h_init : ∀ z : PhaseSpace d, (charX 0 z, charV 0 z) = z)
    (h_cont_Icc : ∀ z,
      ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc (0 : ℝ) T))
    (h_deriv_Ioo : ∀ z, ∀ t ∈ Set.Ioo (0 : ℝ) T,
      HasDerivWithinAt (fun s => (charX s z, charV s z))
        (vlasovVectorField gradW ρ t (charX t z, charV t z))
        (Set.Ici t) t) :
    ∀ t ∈ Set.Icc (0 : ℝ) T,
        Measurable (fun z : PhaseSpace d => (charX t z, charV t z)) := by
  intro t ht
  -- ============================================================
  -- Vector field is max(1, L)-Lipschitz uniformly in t.
  -- ============================================================
  set K : NNReal := max 1 L with hK_def
  have h_vf_lip : ∀ s, LipschitzWith K (vlasovVectorField gradW ρ s) := fun s =>
    vlasovVectorField_lipschitzWith gradW L hL ρ h_int s
  -- ============================================================
  -- Gronwall on flow difference: dist-bound on Icc 0 T (step 0b, extracted
  -- to `charFlow_lipschitzInZ_via_gronwall_Ioo`).
  -- ============================================================
  have h_dist_bound : ∀ z₁ z₂ : PhaseSpace d,
      dist ((charX t z₁, charV t z₁) : PhaseSpace d) (charX t z₂, charV t z₂) ≤
      dist z₁ z₂ * Real.exp ((K : ℝ) * (t - 0)) :=
    charFlow_lipschitzInZ_via_gronwall_Ioo gradW L hL ρ h_int charX charV T hT
      h_init h_cont_Icc h_deriv_Ioo t ht
  -- ============================================================
  -- Convert dist-bound to continuity in z via Metric.continuous_iff.
  -- ============================================================
  have h_cont_z : Continuous (fun z : PhaseSpace d => (charX t z, charV t z)) := by
    rw [Metric.continuous_iff]
    intro z₀ ε hε
    -- Lipschitz constant exp(K * t); pick δ := ε / exp(K * t).
    have h_exp_pos : 0 < Real.exp ((K : ℝ) * (t - 0)) := Real.exp_pos _
    refine ⟨ε / Real.exp ((K : ℝ) * (t - 0)), div_pos hε h_exp_pos, ?_⟩
    intro z hz
    -- dist (f z₀) (f z) ≤ exp(K*t) * dist z₀ z < exp(K*t) * (ε / exp(K*t)) = ε.
    have h_bd := h_dist_bound z₀ z
    -- Note: dist_bound gives `dist (f z₀) (f z)`, but `Metric.continuous_iff`
    -- gives `dist z z₀ < δ → dist (f z) (f z₀) < ε`.  Symmetric: use dist_comm.
    rw [dist_comm] at hz
    have h_chain : dist ((charX t z₀, charV t z₀) : PhaseSpace d) (charX t z, charV t z)
                  < ε := by
      calc dist ((charX t z₀, charV t z₀) : PhaseSpace d) (charX t z, charV t z)
          ≤ dist z₀ z * Real.exp ((K : ℝ) * (t - 0)) := h_bd
        _ < (ε / Real.exp ((K : ℝ) * (t - 0))) * Real.exp ((K : ℝ) * (t - 0)) :=
            mul_lt_mul_of_pos_right hz h_exp_pos
        _ = ε := div_mul_cancel₀ ε (ne_of_gt h_exp_pos)
    rwa [dist_comm] at h_chain
  exact h_cont_z.measurable

/-- **Boundary regularity of a global-in-z flow.**

Given a flow `(charX, charV)` produced by
`exists_vlasov_characteristicFlow_global_smallT` with the open-interval
predicate `IsCharacteristicFlowOn ... (Set.Ioo 0 T) Set.univ`, this helper
extracts the closed-interval boundary regularity package needed by both
`flow_distance_growth_bound_on` and `charFlow_measurable_via_gronwall`:

* `h_init` — the initial-condition clause at `t = 0`,
* `h_cont_Icc` — continuity of `(charX, charV)(·, z)` on the closed
  interval `Icc 0 T`,
* `h_deriv_Ico` — HasDerivWithinAt on `Ico 0 T` (closed at the left
  endpoint).

The open-interval predicate `IsCharacteristicFlowOn` exposes only the
`Ioo`-HasDerivAt clause, while `flow_distance_growth_bound_on` and the
measurability lemma need `Icc`-ContinuousOn + `Ico`-HasDerivWithinAt.
The per-ball flow → per-z trajectory → global-in-z chain carries the
closed-interval `HasDerivWithinAt`-on-`Icc 0 T` data as a separate
conjunct; this theorem takes it as the explicit hypothesis `h_boundary`
and transports it into the precise form needed:

* `h_init` from `hflow.1 z (Set.mem_univ z)` (initial-condition clause).
* `h_cont_Icc` from `h_boundary`'s HasDerivWithinAt → ContinuousWithinAt
  → ContinuousOn (joining components via `Prod`).
* `h_deriv_Ico` from `h_boundary`'s HasDerivWithinAt-on-Icc lifted to
  HasDerivWithinAt-on-Ici at boundary points via `mono_of_mem_nhdsWithin`
  (the local-equivalence-of-filters argument). -/
theorem characteristicFlow_boundary_regularity
    {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (ρ : ℝ → Measure (PhysSpace d))
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (T : ℝ) (_hT : 0 ≤ T)
    (hflow : IsCharacteristicFlowOn gradW ρ charX charV
                                    (Set.Ioo 0 T) Set.univ)
    -- The boundary regularity is an explicit input.  The global-in-z →
    -- per-z → per-ball chain produces it as a separate conjunct alongside
    -- `IsCharacteristicFlowOn`; this helper transports the input forward
    -- into the precise form the Gronwall growth bound needs.
    (h_boundary : ∀ z : PhaseSpace d, ∀ t ∈ Set.Icc (0 : ℝ) T,
        HasDerivWithinAt (fun s => charX s z) (charV t z) (Set.Icc 0 T) t ∧
        HasDerivWithinAt (fun s => charV s z)
          (-(convolveFunctionMeasure gradW (ρ t) (charX t z)))
          (Set.Icc 0 T) t) :
    (∀ z : PhaseSpace d, (charX 0 z, charV 0 z) = z) ∧
    (∀ z : PhaseSpace d,
      ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc (0 : ℝ) T)) ∧
    (∀ z : PhaseSpace d, ∀ s ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt (fun s' => (charX s' z, charV s' z))
        (vlasovVectorField gradW ρ s (charX s z, charV s z))
        (Set.Ici s) s) := by
  refine ⟨?_, ?_, ?_⟩
  · -- h_init: from hflow's initial-condition clause at every z ∈ univ.
    intro z
    obtain ⟨hX, hV⟩ := hflow.1 z (Set.mem_univ z)
    exact Prod.ext hX hV
  · -- h_cont_Icc: from h_boundary's HasDerivWithinAt → ContinuousWithinAt →
    -- ContinuousOn, joined componentwise via Prod.
    intro z s hs
    obtain ⟨h_pos_dw, h_vel_dw⟩ := h_boundary z s hs
    have h_pos_cwn : ContinuousWithinAt (fun s' => charX s' z) (Set.Icc 0 T) s :=
      h_pos_dw.continuousWithinAt
    have h_vel_cwn : ContinuousWithinAt (fun s' => charV s' z) (Set.Icc 0 T) s :=
      h_vel_dw.continuousWithinAt
    exact h_pos_cwn.prodMk h_vel_cwn
  · -- h_deriv_Ico: from h_boundary's HasDerivWithinAt-on-Icc lifted to Ici.
    -- For s ∈ Ico 0 T, Icc 0 T ∈ 𝓝[Ici s] s (since [s, s+ε) ⊆ Icc 0 T
    -- for small ε), so HasDerivWithinAt _ _ (Icc 0 T) s implies
    -- HasDerivWithinAt _ _ (Ici s) s via mono_of_mem_nhdsWithin.
    intro z s hs
    have hs_Icc : s ∈ Set.Icc (0 : ℝ) T := ⟨hs.1, le_of_lt hs.2⟩
    obtain ⟨h_pos_dw, h_vel_dw⟩ := h_boundary z s hs_Icc
    -- Membership: Icc 0 T ∈ nhdsWithin (Ici s) s.  Witness: take the
    -- open neighborhood `Iio T` ∋ s (since s < T from hs.2); then
    -- `Iio T ∩ Ici s = [s, T) ⊆ [0, T] = Icc 0 T`.
    have h_mem : Set.Icc (0 : ℝ) T ∈ nhdsWithin s (Set.Ici s) := by
      rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
      refine ⟨Set.Iio T, Iio_mem_nhds hs.2, ?_⟩
      intro u hu
      refine ⟨?_, ?_⟩
      · -- u ≥ 0: from u ∈ Ici s ⊆ Ici 0 (since s ≥ 0 by hs.1).
        exact le_trans hs.1 hu.2
      · -- u ≤ T: from u ∈ Iio T (so u < T).
        exact le_of_lt hu.1
    have h_pos_Ici : HasDerivWithinAt (fun s' => charX s' z) (charV s z)
                       (Set.Ici s) s :=
      h_pos_dw.mono_of_mem_nhdsWithin h_mem
    have h_vel_Ici : HasDerivWithinAt (fun s' => charV s' z)
                       (-(convolveFunctionMeasure gradW (ρ s) (charX s z)))
                       (Set.Ici s) s :=
      h_vel_dw.mono_of_mem_nhdsWithin h_mem
    -- Join componentwise into the joint Prod-valued HasDerivWithinAt.
    -- vlasovVectorField gradW ρ s (charX s z, charV s z)
    --   = (charV s z, -(convolveFunctionMeasure gradW (ρ s) (charX s z))).
    have h_prod : HasDerivWithinAt
        (fun s' : ℝ => (charX s' z, charV s' z))
        (charV s z, -(convolveFunctionMeasure gradW (ρ s) (charX s z)))
        (Set.Ici s) s := h_pos_Ici.prodMk h_vel_Ici
    -- Convert from componentwise to the vector-field form.
    change HasDerivWithinAt (fun s' => (charX s' z, charV s' z))
            (vlasovVectorField gradW ρ s (charX s z, charV s z)) (Set.Ici s) s
    convert h_prod using 1
    rfl

/-- **Single Picard step `VlasovMeasureCurve d T M → VlasovMeasureCurve d T M'`**.

Composes `exists_vlasov_characteristicFlow_global_smallT` +
`characteristicFlow_boundary_regularity` + `flow_distance_growth_bound_on` +
`charFlow_measurable_via_gronwall` + `PhiAsVlasovMeasureCurve` into a
single Picard step.

**Output bundle** (sigma form): the flow + growth constant + bundled
output curve + local pushforward equation on `Icc 0 T`.  Internally,
`σ.ρ = Phi charX_clamped f₀` where `charX_clamped t := charX (clampToIcc T t)`;
on `Icc 0 T` the clamp is the identity so the pushforward equation
holds with the un-clamped `charX`. -/
theorem Phi_step
    {d : ℕ} [NeZero d]
    (W : PhysSpace d → ℝ)
    (gradW : PhysSpace d → PhysSpace d)
    (hgradW : ∀ x, gradW x = gradient W x)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (h_f₀_int : Integrable (fun z : PhaseSpace d => ‖z‖) f₀)
    (M_f₀ : ℝ) (hM_f₀ : ∫ z, ‖z‖ ∂f₀ ≤ M_f₀)
    {T : ℝ} {M : ℝ → ℝ} (hT : 0 ≤ T)
    (Mbar : ℝ) (hMbar_nn : 0 ≤ Mbar) (hMbar : ∀ t ∈ Set.Icc 0 T, M t ≤ Mbar)
    (hM_mono : MonotoneOn M (Set.Icc 0 T))
    (hTL_PL : LocalSmallnessPLBuffer L T)
    (ρ : VlasovMeasureCurve d T M)
    (h_int_ext : ∀ t (x : PhysSpace d),
                  Integrable (fun y => gradW (x - y)) (ρ.extend t)) :
    ∃ (charX charV : ℝ → PhaseSpace d → PhysSpace d) (C_T : ℝ),
      0 ≤ C_T ∧
      IsCharacteristicFlowOn gradW ρ.extend charX charV (Set.Ioo 0 T) Set.univ ∧
      -- **Piece A (time-local envelope) growth bound** — exposes the per-`z`
      -- bound `flow_distance_growth_bound_on_timedep` produces against the input
      -- moment envelope `M`.  Piece D integrates this (A.2) and closes it against
      -- the canonical envelope (A.3) to re-bundle `σ` into the fixed envelope
      -- space, dissolving the M-fixed-point.
      (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ z : PhaseSpace d,
        ‖(charX t z, charV t z)‖ ≤
          gronwallBound ‖z‖ (1 + (L : ℝ)) (‖gradW 0‖ + (L : ℝ) * M t) t) ∧
      ∃ σ : VlasovMeasureCurve d T (fun _ => C_T * (M_f₀ + 1)),
        ∀ t ∈ Set.Icc (0 : ℝ) T,
          σ.ρ t = Measure.map (fun z : PhaseSpace d => charX t z) f₀ := by
  haveI hExt_prob : ∀ t, IsProbabilityMeasure (ρ.extend t) :=
    VlasovMeasureCurve.extend_isProb ρ
  have hρ_cont : ∀ x : PhysSpace d,
      Continuous (fun t => convolveFunctionMeasure gradW (ρ.extend t) x) := by
    intro x
    have h_int_Icc : ∀ t ∈ Set.Icc (0 : ℝ) T,
        Integrable (fun y => gradW (x - y)) (ρ.ρ t) := by
      intro t ht
      have h_eq : ρ.extend t = ρ.ρ t := by
        unfold VlasovMeasureCurve.extend clampToIcc
        congr 1
        rw [min_eq_left ht.2, max_eq_right ht.1]
      rw [← h_eq]; exact h_int_ext t x
    exact VlasovMeasureCurve.extend_convCont gradW L hL hT ρ x h_int_Icc
  have h_y_int : ∀ t, Integrable (fun y : PhysSpace d => ‖y‖) (ρ.extend t) :=
    fun t => VlasovMeasureCurve.extend_yIntegrable hT ρ t
  have hM_ρ : ∀ t, ∫ y, ‖y‖ ∂(ρ.extend t) ≤ Mbar :=
    fun t => le_trans (VlasovMeasureCurve.extend_hasMoment hT ρ t)
      (hMbar (clampToIcc T t) (clampToIcc_mem hT t))
  obtain ⟨charX, charV, hflow_on, h_boundary⟩ :=
    exists_vlasov_characteristicFlow_global_smallT W gradW hgradW L hL
      ρ.extend h_int_ext hρ_cont h_y_int Mbar hMbar_nn hM_ρ T hT hTL_PL
  obtain ⟨h_init, h_cont_Icc, h_deriv_Ico⟩ :=
    characteristicFlow_boundary_regularity gradW ρ.extend charX charV T hT
      hflow_on h_boundary
  -- Piece A (time-local envelope) per-`z` growth bound against the input
  -- envelope `M` (on `Icc`, `ρ.extend t = ρ.ρ t`, so `ρ`'s moment bound `M t`
  -- feeds the time-local Gronwall forcing).
  have hm_M : ∀ t ∈ Set.Icc (0 : ℝ) T, ∫ y, ‖y‖ ∂(ρ.extend t) ≤ M t := by
    intro t ht
    have h_eq : ρ.extend t = ρ.ρ t := by
      unfold VlasovMeasureCurve.extend clampToIcc
      congr 1
      rw [min_eq_left ht.2, max_eq_right ht.1]
    rw [h_eq]; exact ρ.hasMoment t ht
  have h_growth_timedep : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ z : PhaseSpace d,
      ‖(charX t z, charV t z)‖ ≤
        gronwallBound ‖z‖ (1 + (L : ℝ)) (‖gradW 0‖ + (L : ℝ) * M t) t :=
    flow_distance_growth_bound_on_timedep gradW L hL ρ.extend charX charV T hT
      h_init h_cont_Icc h_deriv_Ico M hM_mono hm_M (fun t _ => h_y_int t) h_int_ext
  obtain ⟨C_T, hC_T_nn, h_growth⟩ :=
    flow_distance_growth_bound_on gradW L hL ρ.extend charX charV T hT
      h_init h_cont_Icc h_deriv_Ico Mbar hMbar_nn
      (fun t _ => hM_ρ t) (fun t _ => h_y_int t) h_int_ext
  have h_meas_Icc : ∀ t ∈ Set.Icc (0 : ℝ) T,
      Measurable (fun z : PhaseSpace d => (charX t z, charV t z)) :=
    charFlow_measurable_via_gronwall gradW L hL ρ.extend h_int_ext charX charV
      T hT h_init h_cont_Icc h_deriv_Ico
  let charX_clamped : ℝ → PhaseSpace d → PhysSpace d :=
    fun t z => charX (clampToIcc T t) z
  have h_meas_clamped : ∀ t,
      AEMeasurable (fun z : PhaseSpace d => charX_clamped t z) f₀ := by
    intro t
    have h_clamp_mem := clampToIcc_mem hT t
    have h_meas_full := h_meas_Icc (clampToIcc T t) h_clamp_mem
    exact (measurable_fst.comp h_meas_full).aemeasurable
  have h_growth_clamped : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ z : PhaseSpace d,
      ‖charX_clamped t z‖ ≤ C_T * (‖z‖ + 1) := by
    intro t ht z
    have h_clamp_eq : clampToIcc T t = t := by
      unfold clampToIcc
      rw [min_eq_left ht.2, max_eq_right ht.1]
    change ‖charX (clampToIcc T t) z‖ ≤ _
    rw [h_clamp_eq]
    have h_full := h_growth t ht z
    have h_proj : ‖charX t z‖ ≤ ‖(charX t z, charV t z)‖ := by
      simp [Prod.norm_def]
    linarith
  have h_int_charX_clamped : ∀ t,
      Integrable (fun z : PhaseSpace d => ‖charX_clamped t z‖) f₀ := by
    intro t
    have h_clamp_mem := clampToIcc_mem hT t
    have h_bound : ∀ z, ‖charX_clamped t z‖ ≤ C_T * (‖z‖ + 1) := by
      intro z
      change ‖charX (clampToIcc T t) z‖ ≤ _
      have h_full := h_growth (clampToIcc T t) h_clamp_mem z
      have h_proj : ‖charX (clampToIcc T t) z‖ ≤
                    ‖(charX (clampToIcc T t) z, charV (clampToIcc T t) z)‖ := by
        simp [Prod.norm_def]
      linarith
    have h_dom_int : Integrable (fun z : PhaseSpace d => C_T * (‖z‖ + 1)) f₀ := by
      have h1 : Integrable (fun z : PhaseSpace d => C_T * ‖z‖) f₀ :=
        h_f₀_int.const_mul C_T
      have h2 : Integrable (fun _ : PhaseSpace d => C_T) f₀ := integrable_const _
      have h_eq : (fun z : PhaseSpace d => C_T * (‖z‖ + 1)) =
                  fun z => C_T * ‖z‖ + C_T := by funext z; ring
      rw [h_eq]; exact h1.add h2
    have h_aesm : AEStronglyMeasurable
        (fun z : PhaseSpace d => ‖charX_clamped t z‖) f₀ :=
      (h_meas_clamped t).norm.aestronglyMeasurable
    refine h_dom_int.mono' h_aesm ?_
    refine Filter.Eventually.of_forall fun z => ?_
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact h_bound z
  have h_charX_cont_clamped : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ z,
      ContinuousWithinAt (fun t => charX_clamped t z) (Set.Icc 0 T) s := by
    intro s hs z
    have h_full := (h_cont_Icc z).continuousWithinAt hs
    have h_charX_cwn : ContinuousWithinAt (fun t => charX t z) (Set.Icc 0 T) s :=
      h_full.fst
    have h_eq_on : ∀ t ∈ Set.Icc (0 : ℝ) T, charX_clamped t z = charX t z := by
      intro t ht
      change charX (clampToIcc T t) z = charX t z
      have h_clamp_eq : clampToIcc T t = t := by
        unfold clampToIcc
        rw [min_eq_left ht.2, max_eq_right ht.1]
      rw [h_clamp_eq]
    exact h_charX_cwn.congr h_eq_on (h_eq_on s hs)
  let σ : VlasovMeasureCurve d T (fun _ => C_T * (M_f₀ + 1)) :=
    PhiAsVlasovMeasureCurve charX_clamped f₀ h_meas_clamped h_int_charX_clamped
      T hT C_T hC_T_nn h_growth_clamped h_f₀_int M_f₀ hM_f₀ h_charX_cont_clamped
  refine ⟨charX, charV, C_T, hC_T_nn, hflow_on, h_growth_timedep, σ, ?_⟩
  intro t ht
  change Phi charX_clamped f₀ t = Measure.map (fun z => charX t z) f₀
  unfold Phi
  have h_clamp_eq : clampToIcc T t = t := by
    unfold clampToIcc
    rw [min_eq_left ht.2, max_eq_right ht.1]
  congr 1
  funext z
  change charX (clampToIcc T t) z = charX t z
  rw [h_clamp_eq]

/-- **`Φ`-step landing in the fixed envelope space.**

`Phi_step` produces a flow `(charX, charV)` against `ρ.extend` and bundles its
position pushforward into the *constant* space `VlasovMeasureCurve d T (fun _ =>
C_T·(M_f₀+1))`.  The constant bound grows with each `Φ`-iteration (the moment
fixed-point pathology).  This wrapper **re-bundles the same pushforward into
the fixed envelope space** `VlasovMeasureCurve d T m`, where `m` is the
canonical Gronwall envelope of `gronwall_envelope_exists`: because `m` is
`Φ`-invariant at the moment level, `Φ` maps `space(m)` to itself, so the Picard
sequence stays in one fixed curve space — dissolving the fixed-point in `M`.

The moment re-bundling is the measure-level data-free escape:
`∫‖x‖∂(map (charX t) f₀) ≤ gronwallBound (∫z‖z‖∂f₀) (1+L) (‖gradW 0‖ + L·m t) t`
(`phi_moment_envelope_le`, fed the per-`z` growth bound `Phi_step`
exposes) `≤ m t` (envelope invariance `hm_inv`).

Output also exposes the **boundary-regularity bundle** (as
`exists_vlasov_characteristicFlow_global_smallT`) so the Picard recursion can
discharge `Phi_supW1_contraction`'s per-`z` regularity hypotheses at each step.

The envelope's anchor moment is the **phase-space** `∫z‖z‖∂f₀` (matching the
`integral_map` initial value), NOT the spatial marginal. -/
theorem Phi_step_envelope
    {d : ℕ} [NeZero d]
    (W : PhysSpace d → ℝ)
    (gradW : PhysSpace d → PhysSpace d)
    (hgradW : ∀ x, gradW x = gradient W x)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (h_f₀_int : Integrable (fun z : PhaseSpace d => ‖z‖) f₀)
    {T : ℝ} (hT : 0 ≤ T)
    (m : ℝ → ℝ) (hm_mono : MonotoneOn m (Set.Icc 0 T))
    (hm_nn : ∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ m t)
    (hm_inv : ∀ t ∈ Set.Icc (0 : ℝ) T,
      gronwallBound (∫ z, ‖z‖ ∂f₀) (1 + (L : ℝ)) (‖gradW 0‖ + (L : ℝ) * m t) t ≤ m t)
    (hTL_PL : LocalSmallnessPLBuffer L T)
    (ρ : VlasovMeasureCurve d T m)
    (h_int_ext : ∀ t (x : PhysSpace d),
                  Integrable (fun y => gradW (x - y)) (ρ.extend t)) :
    ∃ (charX charV : ℝ → PhaseSpace d → PhysSpace d),
      IsCharacteristicFlowOn gradW ρ.extend charX charV (Set.Ioo 0 T) Set.univ ∧
      (∀ z : PhaseSpace d, ∀ t ∈ Set.Icc (0 : ℝ) T,
        HasDerivWithinAt (fun s => charX s z) (charV t z) (Set.Icc 0 T) t ∧
        HasDerivWithinAt (fun s => charV s z)
          (-(convolveFunctionMeasure gradW (ρ.extend t) (charX t z)))
          (Set.Icc 0 T) t) ∧
      ∃ σ : VlasovMeasureCurve d T m,
        ∀ t ∈ Set.Icc (0 : ℝ) T,
          σ.ρ t = Measure.map (fun z : PhaseSpace d => charX t z) f₀ := by
  haveI hExt_prob : ∀ t, IsProbabilityMeasure (ρ.extend t) :=
    VlasovMeasureCurve.extend_isProb ρ
  have hρ_cont : ∀ x : PhysSpace d,
      Continuous (fun t => convolveFunctionMeasure gradW (ρ.extend t) x) := by
    intro x
    have h_int_Icc : ∀ t ∈ Set.Icc (0 : ℝ) T,
        Integrable (fun y => gradW (x - y)) (ρ.ρ t) := by
      intro t ht
      have h_eq : ρ.extend t = ρ.ρ t := by
        unfold VlasovMeasureCurve.extend clampToIcc
        congr 1
        rw [min_eq_left ht.2, max_eq_right ht.1]
      rw [← h_eq]; exact h_int_ext t x
    exact VlasovMeasureCurve.extend_convCont gradW L hL hT ρ x h_int_Icc
  have h_y_int : ∀ t, Integrable (fun y : PhysSpace d => ‖y‖) (ρ.extend t) :=
    fun t => VlasovMeasureCurve.extend_yIntegrable hT ρ t
  have hMbar_nn : 0 ≤ m T := hm_nn T ⟨hT, le_refl T⟩
  have hMbar : ∀ t ∈ Set.Icc (0 : ℝ) T, m t ≤ m T :=
    fun t ht => hm_mono ht ⟨hT, le_refl T⟩ ht.2
  have hM_ρ : ∀ t, ∫ y, ‖y‖ ∂(ρ.extend t) ≤ m T :=
    fun t => le_trans (VlasovMeasureCurve.extend_hasMoment hT ρ t)
      (hMbar (clampToIcc T t) (clampToIcc_mem hT t))
  obtain ⟨charX, charV, hflow_on, h_boundary⟩ :=
    exists_vlasov_characteristicFlow_global_smallT W gradW hgradW L hL
      ρ.extend h_int_ext hρ_cont h_y_int (m T) hMbar_nn hM_ρ T hT hTL_PL
  obtain ⟨h_init, h_cont_Icc, h_deriv_Ico⟩ :=
    characteristicFlow_boundary_regularity gradW ρ.extend charX charV T hT
      hflow_on h_boundary
  have hm_M : ∀ t ∈ Set.Icc (0 : ℝ) T, ∫ y, ‖y‖ ∂(ρ.extend t) ≤ m t := by
    intro t ht
    have h_eq : ρ.extend t = ρ.ρ t := by
      unfold VlasovMeasureCurve.extend clampToIcc
      congr 1
      rw [min_eq_left ht.2, max_eq_right ht.1]
    rw [h_eq]; exact ρ.hasMoment t ht
  have h_growth_timedep : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ z : PhaseSpace d,
      ‖(charX t z, charV t z)‖ ≤
        gronwallBound ‖z‖ (1 + (L : ℝ)) (‖gradW 0‖ + (L : ℝ) * m t) t :=
    flow_distance_growth_bound_on_timedep gradW L hL ρ.extend charX charV T hT
      h_init h_cont_Icc h_deriv_Ico m hm_mono hm_M (fun t _ => h_y_int t) h_int_ext
  obtain ⟨C_T, hC_T_nn, h_growth⟩ :=
    flow_distance_growth_bound_on gradW L hL ρ.extend charX charV T hT
      h_init h_cont_Icc h_deriv_Ico (m T) hMbar_nn
      (fun t _ => hM_ρ t) (fun t _ => h_y_int t) h_int_ext
  have h_meas_Icc : ∀ t ∈ Set.Icc (0 : ℝ) T,
      Measurable (fun z : PhaseSpace d => (charX t z, charV t z)) :=
    charFlow_measurable_via_gronwall gradW L hL ρ.extend h_int_ext charX charV
      T hT h_init h_cont_Icc h_deriv_Ico
  let charX_clamped : ℝ → PhaseSpace d → PhysSpace d :=
    fun t z => charX (clampToIcc T t) z
  have h_meas_clamped : ∀ t,
      AEMeasurable (fun z : PhaseSpace d => charX_clamped t z) f₀ := by
    intro t
    have h_clamp_mem := clampToIcc_mem hT t
    have h_meas_full := h_meas_Icc (clampToIcc T t) h_clamp_mem
    exact (measurable_fst.comp h_meas_full).aemeasurable
  have h_growth_clamped : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ z : PhaseSpace d,
      ‖charX_clamped t z‖ ≤ C_T * (‖z‖ + 1) := by
    intro t ht z
    have h_clamp_eq : clampToIcc T t = t := by
      unfold clampToIcc
      rw [min_eq_left ht.2, max_eq_right ht.1]
    change ‖charX (clampToIcc T t) z‖ ≤ _
    rw [h_clamp_eq]
    have h_full := h_growth t ht z
    have h_proj : ‖charX t z‖ ≤ ‖(charX t z, charV t z)‖ := by
      simp [Prod.norm_def]
    linarith
  have h_int_charX_clamped : ∀ t,
      Integrable (fun z : PhaseSpace d => ‖charX_clamped t z‖) f₀ := by
    intro t
    have h_clamp_mem := clampToIcc_mem hT t
    have h_bound : ∀ z, ‖charX_clamped t z‖ ≤ C_T * (‖z‖ + 1) := by
      intro z
      change ‖charX (clampToIcc T t) z‖ ≤ _
      have h_full := h_growth (clampToIcc T t) h_clamp_mem z
      have h_proj : ‖charX (clampToIcc T t) z‖ ≤
                    ‖(charX (clampToIcc T t) z, charV (clampToIcc T t) z)‖ := by
        simp [Prod.norm_def]
      linarith
    have h_dom_int : Integrable (fun z : PhaseSpace d => C_T * (‖z‖ + 1)) f₀ := by
      have h1 : Integrable (fun z : PhaseSpace d => C_T * ‖z‖) f₀ :=
        h_f₀_int.const_mul C_T
      have h2 : Integrable (fun _ : PhaseSpace d => C_T) f₀ := integrable_const _
      have h_eq : (fun z : PhaseSpace d => C_T * (‖z‖ + 1)) =
                  fun z => C_T * ‖z‖ + C_T := by funext z; ring
      rw [h_eq]; exact h1.add h2
    have h_aesm : AEStronglyMeasurable
        (fun z : PhaseSpace d => ‖charX_clamped t z‖) f₀ :=
      (h_meas_clamped t).norm.aestronglyMeasurable
    refine h_dom_int.mono' h_aesm ?_
    refine Filter.Eventually.of_forall fun z => ?_
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact h_bound z
  have h_charX_cont_clamped : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ z,
      ContinuousWithinAt (fun t => charX_clamped t z) (Set.Icc 0 T) s := by
    intro s hs z
    have h_full := (h_cont_Icc z).continuousWithinAt hs
    have h_charX_cwn : ContinuousWithinAt (fun t => charX t z) (Set.Icc 0 T) s :=
      h_full.fst
    have h_eq_on : ∀ t ∈ Set.Icc (0 : ℝ) T, charX_clamped t z = charX t z := by
      intro t ht
      change charX (clampToIcc T t) z = charX t z
      have h_clamp_eq : clampToIcc T t = t := by
        unfold clampToIcc
        rw [min_eq_left ht.2, max_eq_right ht.1]
      rw [h_clamp_eq]
    exact h_charX_cwn.congr h_eq_on (h_eq_on s hs)
  let σ_const := PhiAsVlasovMeasureCurve charX_clamped f₀ h_meas_clamped
    h_int_charX_clamped T hT C_T hC_T_nn h_growth_clamped h_f₀_int
    (∫ z, ‖z‖ ∂f₀) (le_refl _) h_charX_cont_clamped
  -- On `Icc`, the clamped pushforward equals the raw pushforward.
  have h_rho_eq : ∀ t ∈ Set.Icc (0 : ℝ) T,
      σ_const.ρ t = Measure.map (fun z : PhaseSpace d => charX t z) f₀ := by
    intro t ht
    change Phi charX_clamped f₀ t = Measure.map (fun z => charX t z) f₀
    unfold Phi
    have h_clamp_eq : clampToIcc T t = t := by
      unfold clampToIcc
      rw [min_eq_left ht.2, max_eq_right ht.1]
    congr 1
    funext z
    change charX (clampToIcc T t) z = charX t z
    rw [h_clamp_eq]
  -- Moment re-bundle (the data-free escape): A.2 integrates the per-`z`
  -- envelope growth to a moment bound, A.3's `hm_inv` closes it against `m`.
  have h_meas_charX_Icc : ∀ t ∈ Set.Icc (0 : ℝ) T,
      AEMeasurable (fun z : PhaseSpace d => charX t z) f₀ :=
    fun t ht => (measurable_fst.comp (h_meas_Icc t ht)).aemeasurable
  have h_moment_m : ∀ t ∈ Set.Icc (0 : ℝ) T, ∫ y, ‖y‖ ∂(σ_const.ρ t) ≤ m t := by
    intro t ht
    rw [h_rho_eq t ht]
    calc ∫ y, ‖y‖ ∂(Measure.map (fun z : PhaseSpace d => charX t z) f₀)
        ≤ gronwallBound (∫ z, ‖z‖ ∂f₀) (1 + (L : ℝ))
            (‖gradW 0‖ + (L : ℝ) * m t) t :=
          phi_moment_envelope_le L charX charV (‖gradW 0‖) T m h_growth_timedep
            f₀ h_f₀_int h_meas_charX_Icc t ht
      _ ≤ m t := hm_inv t ht
  -- Re-bundle `σ_const` (constant space) into the fixed envelope space `m`:
  -- only `hasMoment` changes; the other fields are `m`-independent.
  let σ : VlasovMeasureCurve d T m :=
    { ρ := σ_const.ρ
      isProb := σ_const.isProb
      hasMoment := h_moment_m
      yIntegrable := σ_const.yIntegrable
      hW1Cont := σ_const.hW1Cont }
  exact ⟨charX, charV, hflow_on, h_boundary, σ, h_rho_eq⟩

/-- **Pointwise Gronwall on flow difference.**

Given two characteristic flow trajectories `γ_ρ, γ_σ : ℝ → PhaseSpace d`
starting at the same initial condition `z`, driven by *different* measure
curves `ρ, σ` with `supW1On(Icc 0 T) ρ σ ≤ D`, the pointwise difference
satisfies a Gronwall-type bound:
`‖γ_ρ(t) - γ_σ(t)‖ ≤ gronwallBound 0 K (L · D) t`
where `K := max(1, L)`.

**Proof strategy** (Gronwall on the trajectory-difference function):
* Set `f(s) := γ_ρ(s) - γ_σ(s)`.  Then `f(0) = 0` (both start at `z`).
* `f'(s) = vlasovVectorField gradW ρ s (γ_ρ s) − vlasovVectorField gradW σ s (γ_σ s)`.
* Split via triangle:
  `f'(s) = [VF_ρ γ_ρ − VF_ρ γ_σ]  +  [VF_ρ γ_σ − VF_σ γ_σ]`
* First bracket bounded by `K · ‖γ_ρ - γ_σ‖ = K · ‖f s‖` via
  `vlasovVectorField_lipschitzWith`.
* Second bracket: the velocity components cancel (`VF`'s first component is
  `z.2`, identical in both); only the force components differ.  Bounded by
  `L · W₁(ρ_s, σ_s).toReal ≤ L · D` via `norm_convolveFunctionMeasure_sub_le`.
* Apply `norm_le_gronwallBound_of_norm_deriv_right_le` with `δ := 0`,
  `K := max(1, L)`, `ε := L · D`.

**Boundary regularity** identical to `charFlow_measurable_via_gronwall`:
`ContinuousOn (Icc 0 T)` + `HasDerivWithinAt` on `Ico 0 T` for each
trajectory.  The Picard construction discharges these hypotheses.

Used by the main contraction lemma to bound
`supW1On(Icc 0 T)(Phi ρ)(Phi σ)` by `K_contract(T) · supW1On(Icc 0 T) ρ σ`
where `K_contract(T) := (L/K) · (exp(K·T) - 1) → 0` as `T → 0`. -/
theorem flow_difference_gronwall_bound {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ σ : ℝ → Measure (PhysSpace d))
    [∀ t, IsProbabilityMeasure (ρ t)] [∀ t, IsProbabilityMeasure (σ t)]
    (h_int_ρ : ∀ t (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ t))
    (h_int_σ : ∀ t (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (σ t))
    (T : ℝ) (_hT : 0 ≤ T)
    (D : ℝ) (_hD_nn : 0 ≤ D)
    (h_W1_fin : ∀ s ∈ Set.Icc (0 : ℝ) T, wasserstein1 (ρ s) (σ s) ≠ ⊤)
    (h_W1_bound : ∀ s ∈ Set.Icc (0 : ℝ) T, (wasserstein1 (ρ s) (σ s)).toReal ≤ D)
    (γ_ρ γ_σ : ℝ → PhaseSpace d)
    (z : PhaseSpace d)
    (h_init_ρ : γ_ρ 0 = z) (h_init_σ : γ_σ 0 = z)
    (h_cont_ρ : ContinuousOn γ_ρ (Set.Icc (0 : ℝ) T))
    (h_cont_σ : ContinuousOn γ_σ (Set.Icc (0 : ℝ) T))
    (h_deriv_ρ : ∀ s ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt γ_ρ (vlasovVectorField gradW ρ s (γ_ρ s)) (Set.Ici s) s)
    (h_deriv_σ : ∀ s ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt γ_σ (vlasovVectorField gradW σ s (γ_σ s)) (Set.Ici s) s) :
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      ‖γ_ρ t - γ_σ t‖ ≤
        gronwallBound 0 ((max 1 L : NNReal) : ℝ) ((L : ℝ) * D) t := by
  -- ============================================================
  -- Setup: K = max(1, L), f(s) = γ_ρ(s) - γ_σ(s).
  -- ============================================================
  set K_NN : NNReal := max 1 L with hK_NN_def
  set K_lip : ℝ := (K_NN : ℝ) with hK_lip_def
  have hK_NN_eq : K_lip = ((max 1 L : NNReal) : ℝ) := rfl
  set f : ℝ → PhaseSpace d := fun s => γ_ρ s - γ_σ s with hf_def
  set f' : ℝ → PhaseSpace d := fun s =>
    vlasovVectorField gradW ρ s (γ_ρ s) - vlasovVectorField gradW σ s (γ_σ s)
    with hf'_def
  -- ============================================================
  -- Continuity + right-derivative of f on the relevant intervals.
  -- ============================================================
  have h_f_cont : ContinuousOn f (Set.Icc (0 : ℝ) T) := h_cont_ρ.sub h_cont_σ
  have h_f_deriv : ∀ s ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt f (f' s) (Set.Ici s) s := fun s hs =>
    (h_deriv_ρ s hs).sub (h_deriv_σ s hs)
  -- ============================================================
  -- Initial: ‖f 0‖ = 0.
  -- ============================================================
  have h_f0 : ‖f 0‖ ≤ 0 := by
    change ‖γ_ρ 0 - γ_σ 0‖ ≤ 0
    rw [h_init_ρ, h_init_σ, sub_self, norm_zero]
  -- ============================================================
  -- Differential bound: ‖f'(s)‖ ≤ K_lip · ‖f(s)‖ + L · D for s ∈ Ico 0 T.
  -- ============================================================
  have h_f'_bound : ∀ s ∈ Set.Ico (0 : ℝ) T,
      ‖f' s‖ ≤ K_lip * ‖f s‖ + (L : ℝ) * D := by
    intro s hs
    -- s ∈ Icc 0 T from s ∈ Ico 0 T
    have hs_Icc : s ∈ Set.Icc (0 : ℝ) T := ⟨hs.1, le_of_lt hs.2⟩
    -- ============================================================
    -- Triangle split: f'(s) = [VF_ρ γ_ρ − VF_ρ γ_σ] + [VF_ρ γ_σ − VF_σ γ_σ]
    -- ============================================================
    have h_split : f' s =
        (vlasovVectorField gradW ρ s (γ_ρ s) -
         vlasovVectorField gradW ρ s (γ_σ s)) +
        (vlasovVectorField gradW ρ s (γ_σ s) -
         vlasovVectorField gradW σ s (γ_σ s)) := by
      simp only [hf'_def]; abel
    have h_tri : ‖f' s‖ ≤
        ‖vlasovVectorField gradW ρ s (γ_ρ s) - vlasovVectorField gradW ρ s (γ_σ s)‖ +
        ‖vlasovVectorField gradW ρ s (γ_σ s) - vlasovVectorField gradW σ s (γ_σ s)‖ := by
      rw [h_split]; exact norm_add_le _ _
    -- ============================================================
    -- First bracket: ‖VF_ρ γ_ρ − VF_ρ γ_σ‖ ≤ K_lip · ‖γ_ρ - γ_σ‖.
    -- ============================================================
    have h_vf_lip := vlasovVectorField_lipschitzWith gradW L hL ρ h_int_ρ s
    have h_first : ‖vlasovVectorField gradW ρ s (γ_ρ s) -
                    vlasovVectorField gradW ρ s (γ_σ s)‖ ≤
                   K_lip * ‖γ_ρ s - γ_σ s‖ := by
      have h := h_vf_lip.dist_le_mul (γ_ρ s) (γ_σ s)
      rw [dist_eq_norm, dist_eq_norm] at h
      exact h
    -- ============================================================
    -- Second bracket: VF_ρ γ_σ − VF_σ γ_σ = (0, conv σ - conv ρ at γ_σ.1).
    -- Norm = ‖conv ρ - conv σ at γ_σ.1‖ ≤ L * W₁(ρ_s, σ_s).toReal ≤ L * D.
    -- ============================================================
    have h_VF_diff_explicit :
        vlasovVectorField gradW ρ s (γ_σ s) - vlasovVectorField gradW σ s (γ_σ s) =
        (0, convolveFunctionMeasure gradW (σ s) (γ_σ s).1 -
            convolveFunctionMeasure gradW (ρ s) (γ_σ s).1) := by
      simp only [vlasovVectorField, Prod.mk_sub_mk, sub_self, neg_sub_neg]
    have h_second_norm :
        ‖vlasovVectorField gradW ρ s (γ_σ s) - vlasovVectorField gradW σ s (γ_σ s)‖ =
        ‖convolveFunctionMeasure gradW (σ s) (γ_σ s).1 -
         convolveFunctionMeasure gradW (ρ s) (γ_σ s).1‖ := by
      rw [h_VF_diff_explicit]
      simp [Prod.norm_def]
    have h_conv_lip := norm_convolveFunctionMeasure_sub_le gradW L hL
      (σ s) (ρ s) (γ_σ s).1
      (by rw [wasserstein1_comm]; exact h_W1_fin s hs_Icc)
      (h_int_σ s _) (h_int_ρ s _)
    have h_W1_comm : (wasserstein1 (σ s) (ρ s)).toReal =
                     (wasserstein1 (ρ s) (σ s)).toReal := by
      rw [wasserstein1_comm]
    have h_second : ‖vlasovVectorField gradW ρ s (γ_σ s) -
                     vlasovVectorField gradW σ s (γ_σ s)‖ ≤ (L : ℝ) * D := by
      rw [h_second_norm]
      calc ‖convolveFunctionMeasure gradW (σ s) (γ_σ s).1 -
            convolveFunctionMeasure gradW (ρ s) (γ_σ s).1‖
          ≤ (L : ℝ) * (wasserstein1 (σ s) (ρ s)).toReal := h_conv_lip
        _ = (L : ℝ) * (wasserstein1 (ρ s) (σ s)).toReal := by rw [h_W1_comm]
        _ ≤ (L : ℝ) * D := by
            apply mul_le_mul_of_nonneg_left (h_W1_bound s hs_Icc) L.coe_nonneg
    -- ============================================================
    -- Combine: ‖f'(s)‖ ≤ K_lip · ‖f(s)‖ + L · D.
    -- ============================================================
    calc ‖f' s‖
        ≤ ‖vlasovVectorField gradW ρ s (γ_ρ s) -
            vlasovVectorField gradW ρ s (γ_σ s)‖ +
          ‖vlasovVectorField gradW ρ s (γ_σ s) -
            vlasovVectorField gradW σ s (γ_σ s)‖ := h_tri
      _ ≤ K_lip * ‖γ_ρ s - γ_σ s‖ + (L : ℝ) * D := by
          linarith [h_first, h_second]
      _ = K_lip * ‖f s‖ + (L : ℝ) * D := by
          simp only [hf_def]
  -- ============================================================
  -- Apply norm_le_gronwallBound_of_norm_deriv_right_le.
  -- ============================================================
  intro t ht
  have h := norm_le_gronwallBound_of_norm_deriv_right_le
    h_f_cont h_f_deriv h_f0 h_f'_bound t ht
  -- h : ‖f t‖ ≤ gronwallBound 0 K_lip (L · D) (t - 0)
  simp only [sub_zero] at h
  exact h

/-- **W₁ pushforward bound for two arbitrary maps.**

Generalizes `wasserstein1_Phi_le_integral_diff` (which handled a single
flow at two times) to two arbitrary maps `f, g : PhaseSpace d → PhysSpace d`.
For pushforwards of the same initial measure `f₀`:
`W₁(f_# f₀, g_# f₀) ≤ ENNReal.ofReal (∫ z, ‖f z - g z‖ ∂f₀)`.

**Proof structure** parallel to `wasserstein1_Phi_le_integral_diff`: KR-
dual direct, with `integral_map` converting pushforward integrals + the
1-Lipschitz bound `|φ y - φ y'| ≤ ‖y - y'‖`.  Dominators are built as named
`have`s, and the `_map_measure` family is bridged via `.mp`/`.mpr`.

Used by `Phi_pointwise_contraction` (below) with
`f := charX_ρ t, g := charX_σ t` to bound the pushforward W₁ in terms of
the pointwise flow difference. -/
theorem wasserstein1_pushforward_pair_le_integral_norm_diff {d : ℕ}
    (f g : PhaseSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (h_meas_f : AEMeasurable f f₀) (h_meas_g : AEMeasurable g f₀)
    (h_int_f : Integrable (fun z : PhaseSpace d => ‖f z‖) f₀)
    (h_int_g : Integrable (fun z : PhaseSpace d => ‖g z‖) f₀)
    (h_diff_int : Integrable (fun z : PhaseSpace d => ‖f z - g z‖) f₀) :
    wasserstein1 (Measure.map f f₀) (Measure.map g f₀) ≤
      ENNReal.ofReal (∫ z, ‖f z - g z‖ ∂f₀) := by
  simp only [wasserstein1_eq_iSup_lipschitz]
  refine iSup_le fun φ => iSup_le fun hφ => ?_
  apply ENNReal.ofReal_le_ofReal
  have hφ_cont : Continuous φ := hφ.continuous
  have hφ_meas_νf : AEStronglyMeasurable φ (Measure.map f f₀) :=
    hφ_cont.aestronglyMeasurable
  have hφ_meas_νg : AEStronglyMeasurable φ (Measure.map g f₀) :=
    hφ_cont.aestronglyMeasurable
  have hφ_abs_bound : ∀ y : PhysSpace d, |φ y| ≤ |φ 0| + ‖y‖ := fun y => by
    have h_lip := hφ.dist_le_mul y 0
    rw [Real.dist_eq, dist_zero_right, NNReal.coe_one, one_mul] at h_lip
    calc |φ y| = |(φ y - φ 0) + φ 0| := by ring_nf
      _ ≤ |φ y - φ 0| + |φ 0| := abs_add_le _ _
      _ ≤ ‖y‖ + |φ 0| := by linarith
      _ = |φ 0| + ‖y‖ := by ring
  have h_norm_int_νf : Integrable (fun y : PhysSpace d => ‖y‖)
      (Measure.map f f₀) :=
    (integrable_map_measure (Continuous.aestronglyMeasurable continuous_norm)
      h_meas_f).mpr h_int_f
  have h_norm_int_νg : Integrable (fun y : PhysSpace d => ‖y‖)
      (Measure.map g f₀) :=
    (integrable_map_measure (Continuous.aestronglyMeasurable continuous_norm)
      h_meas_g).mpr h_int_g
  have h_dom_νf : Integrable (fun y : PhysSpace d => |φ 0| + ‖y‖)
      (Measure.map f f₀) :=
    (integrable_const _).add h_norm_int_νf
  have h_dom_νg : Integrable (fun y : PhysSpace d => |φ 0| + ‖y‖)
      (Measure.map g f₀) :=
    (integrable_const _).add h_norm_int_νg
  have hφ_int_νf : Integrable φ (Measure.map f f₀) := by
    refine Integrable.mono' h_dom_νf hφ_meas_νf ?_
    refine Filter.Eventually.of_forall fun y => ?_
    rw [Real.norm_eq_abs]
    exact hφ_abs_bound y
  have hφ_int_νg : Integrable φ (Measure.map g f₀) := by
    refine Integrable.mono' h_dom_νg hφ_meas_νg ?_
    refine Filter.Eventually.of_forall fun y => ?_
    rw [Real.norm_eq_abs]
    exact hφ_abs_bound y
  rw [integral_map h_meas_f hφ_meas_νf, integral_map h_meas_g hφ_meas_νg]
  have hφ_comp_int_f : Integrable (fun z : PhaseSpace d => φ (f z)) f₀ :=
    (integrable_map_measure hφ_meas_νf h_meas_f).mp hφ_int_νf
  have hφ_comp_int_g : Integrable (fun z : PhaseSpace d => φ (g z)) f₀ :=
    (integrable_map_measure hφ_meas_νg h_meas_g).mp hφ_int_νg
  rw [← integral_sub hφ_comp_int_f hφ_comp_int_g]
  have h_pt : ∀ z : PhaseSpace d,
      φ (f z) - φ (g z) ≤ ‖f z - g z‖ := fun z => by
    have h_lip := hφ.dist_le_mul (f z) (g z)
    rw [Real.dist_eq, dist_eq_norm, NNReal.coe_one, one_mul] at h_lip
    linarith [abs_le.mp h_lip |>.2]
  exact integral_mono (hφ_comp_int_f.sub hφ_comp_int_g) h_diff_int h_pt

/-- **Pointwise contraction estimate at time t.**

Composes the pointwise Gronwall (`flow_difference_gronwall_bound`)
with the W₁ pair bound to get:
`(wasserstein1 (charX_ρ t # f₀) (charX_σ t # f₀)).toReal ≤ gronwallBound 0 K (L·D) t`
for `t ∈ Icc 0 T`, where `K := max(1, L)` and `D := supW1On(Icc 0 T) ρ σ`.

**Proof**: the pointwise Gronwall gives
`‖charX_ρ t z - charX_σ t z‖ ≤ gronwallBound 0 K (L·D) t`
uniformly in z.  Integrating over f₀ (a probability measure) gives the same
bound on `∫ ‖charX_ρ t z - charX_σ t z‖ ∂f₀`.  The W₁ pair bound then
transfers to the Wasserstein side.

Taking sup over `t ∈ Icc 0 T` derives the contraction
`supW1On(Phi_ρ)(Phi_σ) ≤ K_contract(T) · D` where
`K_contract(T) := (L/K)·(exp(K·T)−1) → 0` as `T → 0`. -/
theorem Phi_pointwise_contraction {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ σ : ℝ → Measure (PhysSpace d))
    [∀ t, IsProbabilityMeasure (ρ t)] [∀ t, IsProbabilityMeasure (σ t)]
    (h_int_ρ : ∀ t (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ t))
    (h_int_σ : ∀ t (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (σ t))
    (T : ℝ) (hT : 0 ≤ T)
    (D : ℝ) (hD_nn : 0 ≤ D)
    (h_W1_fin : ∀ s ∈ Set.Icc (0 : ℝ) T, wasserstein1 (ρ s) (σ s) ≠ ⊤)
    (h_W1_bound : ∀ s ∈ Set.Icc (0 : ℝ) T, (wasserstein1 (ρ s) (σ s)).toReal ≤ D)
    -- Two flows (ρ-driven and σ-driven) starting at f₀-distributed initials.
    (charX_ρ charV_ρ charX_σ charV_σ : ℝ → PhaseSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (h_meas_ρ : ∀ t ∈ Set.Icc (0 : ℝ) T,
      AEMeasurable (fun z : PhaseSpace d => charX_ρ t z) f₀)
    (h_meas_σ : ∀ t ∈ Set.Icc (0 : ℝ) T,
      AEMeasurable (fun z : PhaseSpace d => charX_σ t z) f₀)
    (h_int_charX_ρ : ∀ t ∈ Set.Icc (0 : ℝ) T,
      Integrable (fun z : PhaseSpace d => ‖charX_ρ t z‖) f₀)
    (h_int_charX_σ : ∀ t ∈ Set.Icc (0 : ℝ) T,
      Integrable (fun z : PhaseSpace d => ‖charX_σ t z‖) f₀)
    -- Per-z trajectories satisfy boundary regularity (the Picard construction
    -- discharges these).  Phrased per-z, but uniformly across z : PhaseSpace d.
    (h_init_ρ : ∀ z, (charX_ρ 0 z, charV_ρ 0 z) = z)
    (h_init_σ : ∀ z, (charX_σ 0 z, charV_σ 0 z) = z)
    (h_cont_ρ : ∀ z,
      ContinuousOn (fun s => (charX_ρ s z, charV_ρ s z)) (Set.Icc (0 : ℝ) T))
    (h_cont_σ : ∀ z,
      ContinuousOn (fun s => (charX_σ s z, charV_σ s z)) (Set.Icc (0 : ℝ) T))
    (h_deriv_ρ : ∀ z, ∀ s ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt (fun s' => (charX_ρ s' z, charV_ρ s' z))
        (vlasovVectorField gradW ρ s (charX_ρ s z, charV_ρ s z))
        (Set.Ici s) s)
    (h_deriv_σ : ∀ z, ∀ s ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt (fun s' => (charX_σ s' z, charV_σ s' z))
        (vlasovVectorField gradW σ s (charX_σ s z, charV_σ s z))
        (Set.Ici s) s)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    (wasserstein1 (Measure.map (fun z => charX_ρ t z) f₀)
                  (Measure.map (fun z => charX_σ t z) f₀)).toReal ≤
      gronwallBound 0 ((max 1 L : NNReal) : ℝ) ((L : ℝ) * D) t := by
  -- ============================================================
  -- Pointwise Gronwall bound: applies for each z, uniformly.
  -- ============================================================
  set K_lip : ℝ := ((max 1 L : NNReal) : ℝ) with hK_lip_def
  set C_T : ℝ := gronwallBound 0 K_lip ((L : ℝ) * D) t with hC_T_def
  have h_pt_bound : ∀ z : PhaseSpace d,
      ‖(charX_ρ t z, charV_ρ t z) - (charX_σ t z, charV_σ t z)‖ ≤ C_T := by
    intro z
    have h := flow_difference_gronwall_bound gradW L hL ρ σ h_int_ρ h_int_σ
      T hT D hD_nn h_W1_fin h_W1_bound
      (fun s => (charX_ρ s z, charV_ρ s z))
      (fun s => (charX_σ s z, charV_σ s z))
      z (h_init_ρ z) (h_init_σ z) (h_cont_ρ z) (h_cont_σ z)
      (h_deriv_ρ z) (h_deriv_σ z) t ht
    exact h
  -- ============================================================
  -- Project to position component: ‖charX_ρ t z - charX_σ t z‖ ≤ C_T.
  -- ============================================================
  have h_proj_bound : ∀ z : PhaseSpace d,
      ‖charX_ρ t z - charX_σ t z‖ ≤ C_T := fun z => by
    have h := h_pt_bound z
    -- ‖charX_ρ - charX_σ‖ ≤ ‖(charX_ρ, charV_ρ) - (charX_σ, charV_σ)‖.
    have h_proj :
        ‖charX_ρ t z - charX_σ t z‖ ≤
        ‖((charX_ρ t z, charV_ρ t z) - (charX_σ t z, charV_σ t z) : PhaseSpace d)‖ := by
      rw [Prod.norm_def]
      simp only [Prod.fst_sub]
      exact le_max_left _ _
    linarith
  -- ============================================================
  -- C_T is non-negative (gronwallBound at 0 with δ = 0 and ε ≥ 0).
  -- ============================================================
  have hC_T_nn : 0 ≤ C_T := by
    have h_LD_nn : 0 ≤ (L : ℝ) * D := mul_nonneg L.coe_nonneg hD_nn
    have h_K_pos : 0 ≤ K_lip := by
      have h_max_le : (1 : ℝ) ≤ ((max 1 L : NNReal) : ℝ) := by
        push_cast
        exact le_max_left _ _
      linarith
    have ht_nn : 0 ≤ t := ht.1
    -- gronwallBound monotone in x from x = 0
    have := gronwallBound_mono (δ := (0 : ℝ)) (K := K_lip) (ε := (L : ℝ) * D)
      (le_refl 0) h_LD_nn h_K_pos ht_nn
    rw [gronwallBound_x0] at this
    exact this
  -- ============================================================
  -- Integrability of `‖charX_ρ t z - charX_σ t z‖` wrt f₀.
  -- ============================================================
  have h_diff_int_f₀ : Integrable (fun z : PhaseSpace d =>
      ‖charX_ρ t z - charX_σ t z‖) f₀ := by
    -- Bounded by C_T (constant), integrable on probability measure.
    refine Integrable.mono' (integrable_const C_T)
      (((h_meas_ρ t ht).sub (h_meas_σ t ht)).norm.aestronglyMeasurable) ?_
    refine Filter.Eventually.of_forall fun z => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact h_proj_bound z
  -- ============================================================
  -- Apply the W₁ pair bound.
  -- ============================================================
  have h_W1 := wasserstein1_pushforward_pair_le_integral_norm_diff
    (fun z => charX_ρ t z) (fun z => charX_σ t z) f₀
    (h_meas_ρ t ht) (h_meas_σ t ht) (h_int_charX_ρ t ht) (h_int_charX_σ t ht) h_diff_int_f₀
  -- ============================================================
  -- ∫ z, ‖charX_ρ t z - charX_σ t z‖ ∂f₀ ≤ C_T.
  -- ============================================================
  have h_integral_bound : ∫ z, ‖charX_ρ t z - charX_σ t z‖ ∂f₀ ≤ C_T := by
    calc ∫ z, ‖charX_ρ t z - charX_σ t z‖ ∂f₀
        ≤ ∫ _, C_T ∂f₀ := integral_mono h_diff_int_f₀ (integrable_const _) h_proj_bound
      _ = C_T := by
          simp [integral_const, measureReal_def, measure_univ]
  -- ============================================================
  -- Convert ENNReal.ofReal bound to .toReal bound.
  -- ============================================================
  have h_W1_le_ofReal : (wasserstein1 (Measure.map (fun z => charX_ρ t z) f₀)
                                       (Measure.map (fun z => charX_σ t z) f₀)).toReal ≤
                       (ENNReal.ofReal C_T).toReal := by
    apply ENNReal.toReal_mono ENNReal.ofReal_ne_top
    refine le_trans h_W1 ?_
    exact ENNReal.ofReal_le_ofReal h_integral_bound
  rw [ENNReal.toReal_ofReal hC_T_nn] at h_W1_le_ofReal
  exact h_W1_le_ofReal

/-- **sup-W₁ contraction estimate over `Icc 0 T`.**

Combines the pointwise contraction (`Phi_pointwise_contraction`) with
`gronwallBound`'s monotonicity in `t` to derive:
`(supW1On(Icc 0 T) Phi_ρ Phi_σ).toReal ≤ gronwallBound 0 K (L·D) T`
where `K := max(1, L)` and `D := supW1On(Icc 0 T) ρ σ` bound.

**For the Banach fixed-point**: expanding `gronwallBound`'s explicit
form `(ε/K)·(exp(K·t) − 1)`, the bound is `(L·D/K) · (exp(K·T) − 1) =
D · K_contract(T)` where `K_contract(T) := (L/K)·(exp(K·T) − 1) → 0` as
`T → 0`.  This is the contraction factor the Banach iteration exploits.

**Metric-dependence note**:
The contraction factor `K_contract(T) := (L/K)·(exp(K·T) − 1)` is
*exponential in T*.  For contraction (`K_contract < 1`), this requires
`L · (exp T - 1) < 1` when `K = 1` — exactly the
`LocalSmallnessContraction L T` predicate.  This is genuinely independent
of the per-ball Picard-Lindelöf flow's quadratic-in-`T` ball-geometry
constraint `LocalSmallnessPLBuffer L T := L·T² < 1`; the two predicates
match the two distinct sub-arguments.

Under the `Wbar` refactor (Dobrushin 1979, §5), the contraction factor
becomes `C₂(L) · T` — *linear in T*, no exponential.
`LocalSmallnessContraction` would reduce to `C₂(L) · T < 1`;
`LocalSmallnessPLBuffer` is independent of that change. -/
theorem Phi_supW1_contraction {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ σ : ℝ → Measure (PhysSpace d))
    [∀ t, IsProbabilityMeasure (ρ t)] [∀ t, IsProbabilityMeasure (σ t)]
    (h_int_ρ : ∀ t (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ t))
    (h_int_σ : ∀ t (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (σ t))
    (T : ℝ) (hT : 0 ≤ T)
    (D : ℝ) (hD_nn : 0 ≤ D)
    (h_W1_fin : ∀ s ∈ Set.Icc (0 : ℝ) T, wasserstein1 (ρ s) (σ s) ≠ ⊤)
    (h_W1_bound : ∀ s ∈ Set.Icc (0 : ℝ) T, (wasserstein1 (ρ s) (σ s)).toReal ≤ D)
    (charX_ρ charV_ρ charX_σ charV_σ : ℝ → PhaseSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (h_meas_ρ : ∀ t ∈ Set.Icc (0 : ℝ) T,
      AEMeasurable (fun z : PhaseSpace d => charX_ρ t z) f₀)
    (h_meas_σ : ∀ t ∈ Set.Icc (0 : ℝ) T,
      AEMeasurable (fun z : PhaseSpace d => charX_σ t z) f₀)
    (h_int_charX_ρ : ∀ t ∈ Set.Icc (0 : ℝ) T,
      Integrable (fun z : PhaseSpace d => ‖charX_ρ t z‖) f₀)
    (h_int_charX_σ : ∀ t ∈ Set.Icc (0 : ℝ) T,
      Integrable (fun z : PhaseSpace d => ‖charX_σ t z‖) f₀)
    -- The pushforwards have finite first moments (for W₁ finiteness).
    (h_yint_Phi_ρ : ∀ t ∈ Set.Icc (0 : ℝ) T,
      Integrable (fun y : PhysSpace d => ‖y‖)
        (Measure.map (fun z => charX_ρ t z) f₀))
    (h_yint_Phi_σ : ∀ t ∈ Set.Icc (0 : ℝ) T,
      Integrable (fun y : PhysSpace d => ‖y‖)
        (Measure.map (fun z => charX_σ t z) f₀))
    -- Per-z trajectory regularity (the Picard construction discharges these).
    (h_init_ρ : ∀ z, (charX_ρ 0 z, charV_ρ 0 z) = z)
    (h_init_σ : ∀ z, (charX_σ 0 z, charV_σ 0 z) = z)
    (h_cont_ρ : ∀ z,
      ContinuousOn (fun s => (charX_ρ s z, charV_ρ s z)) (Set.Icc (0 : ℝ) T))
    (h_cont_σ : ∀ z,
      ContinuousOn (fun s => (charX_σ s z, charV_σ s z)) (Set.Icc (0 : ℝ) T))
    (h_deriv_ρ : ∀ z, ∀ s ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt (fun s' => (charX_ρ s' z, charV_ρ s' z))
        (vlasovVectorField gradW ρ s (charX_ρ s z, charV_ρ s z))
        (Set.Ici s) s)
    (h_deriv_σ : ∀ z, ∀ s ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt (fun s' => (charX_σ s' z, charV_σ s' z))
        (vlasovVectorField gradW σ s (charX_σ s z, charV_σ s z))
        (Set.Ici s) s) :
    (supW1On (Set.Icc (0 : ℝ) T)
        (fun t => Measure.map (fun z => charX_ρ t z) f₀)
        (fun t => Measure.map (fun z => charX_σ t z) f₀)).toReal ≤
      gronwallBound 0 ((max 1 L : NNReal) : ℝ) ((L : ℝ) * D) T := by
  -- ============================================================
  -- Setup.
  -- ============================================================
  set K_lip : ℝ := ((max 1 L : NNReal) : ℝ) with hK_lip_def
  set C_T : ℝ := gronwallBound 0 K_lip ((L : ℝ) * D) T with hC_T_def
  have h_LD_nn : 0 ≤ (L : ℝ) * D := mul_nonneg L.coe_nonneg hD_nn
  have h_K_pos : 0 ≤ K_lip := by
    have h_max_le : (1 : ℝ) ≤ K_lip := by exact le_max_left _ _
    linarith
  have hC_T_nn : 0 ≤ C_T := by
    have := gronwallBound_mono (δ := (0 : ℝ)) (K := K_lip) (ε := (L : ℝ) * D)
      (le_refl 0) h_LD_nn h_K_pos hT
    rw [gronwallBound_x0] at this
    exact this
  -- ============================================================
  -- Pointwise bound (from `Phi_pointwise_contraction`): for each t ∈ Icc 0 T,
  --   wasserstein1 (Phi_ρ t) (Phi_σ t) ≤ ENNReal.ofReal C_T.
  -- ============================================================
  have h_pt_bound : ∀ t ∈ Set.Icc (0 : ℝ) T,
      wasserstein1 (Measure.map (fun z => charX_ρ t z) f₀)
                   (Measure.map (fun z => charX_σ t z) f₀) ≤
      ENNReal.ofReal C_T := by
    intro t ht
    haveI hΦρ_t : IsProbabilityMeasure (Measure.map (fun z => charX_ρ t z) f₀) :=
      MeasureTheory.Measure.isProbabilityMeasure_map (h_meas_ρ t ht)
    haveI hΦσ_t : IsProbabilityMeasure (Measure.map (fun z => charX_σ t z) f₀) :=
      MeasureTheory.Measure.isProbabilityMeasure_map (h_meas_σ t ht)
    -- W₁ is finite (probability + finite first moment).
    have h_W1_t_ne_top :
        wasserstein1 (Measure.map (fun z => charX_ρ t z) f₀)
                     (Measure.map (fun z => charX_σ t z) f₀) ≠ ⊤ :=
      wasserstein1_ne_top_of_finite_moment _ _ (h_yint_Phi_ρ t ht) (h_yint_Phi_σ t ht)
    -- Pointwise contraction at time t.
    have h_pt := Phi_pointwise_contraction gradW L hL ρ σ h_int_ρ h_int_σ
      T hT D hD_nn h_W1_fin h_W1_bound
      charX_ρ charV_ρ charX_σ charV_σ f₀
      h_meas_ρ h_meas_σ h_int_charX_ρ h_int_charX_σ
      h_init_ρ h_init_σ h_cont_ρ h_cont_σ h_deriv_ρ h_deriv_σ t ht
    -- h_pt : (W₁ ...).toReal ≤ gronwallBound 0 K_lip (L*D) t
    -- Monotonicity of gronwallBound in t: t ≤ T ⇒ value at t ≤ value at T = C_T.
    have h_gronwall_mono : gronwallBound 0 K_lip ((L : ℝ) * D) t ≤ C_T := by
      apply gronwallBound_mono (le_refl 0) h_LD_nn h_K_pos ht.2
    have h_W1_real_le : (wasserstein1 (Measure.map (fun z => charX_ρ t z) f₀)
                                       (Measure.map (fun z => charX_σ t z) f₀)).toReal ≤ C_T :=
      le_trans h_pt h_gronwall_mono
    -- Lift from .toReal-bound to ENNReal bound (using W₁ ≠ ⊤).
    rw [← ENNReal.ofReal_toReal h_W1_t_ne_top]
    exact ENNReal.ofReal_le_ofReal h_W1_real_le
  -- ============================================================
  -- supW1On ≤ ENNReal.ofReal C_T.
  -- ============================================================
  have h_sup_bound : supW1On (Set.Icc (0 : ℝ) T)
        (fun t => Measure.map (fun z => charX_ρ t z) f₀)
        (fun t => Measure.map (fun z => charX_σ t z) f₀) ≤
      ENNReal.ofReal C_T := by
    unfold supW1On
    refine iSup_le fun t => iSup_le fun ht => h_pt_bound t ht
  -- ============================================================
  -- .toReal: (supW1On ...).toReal ≤ C_T.
  -- ============================================================
  calc (supW1On (Set.Icc (0 : ℝ) T)
          (fun t => Measure.map (fun z => charX_ρ t z) f₀)
          (fun t => Measure.map (fun z => charX_σ t z) f₀)).toReal
      ≤ (ENNReal.ofReal C_T).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top h_sup_bound
    _ = C_T := ENNReal.toReal_ofReal hC_T_nn

/-- **Picard-iteration geometric bound.**

Given a sequence with geometric contraction `supW1On (x k) (x (k+1)) ≤
ENNReal.ofReal (q^k * D₀)` for `0 ≤ q < 1`, the iterated triangle
inequality + `ENNReal.ofReal_sum_of_nonneg` + Mathlib's `geom_sum_Ico_le_of_lt_one`
gives:
`supW1On (x m) (x n) ≤ ENNReal.ofReal (D₀ * q^m / (1 - q))` for `m ≤ n`.

The argument is pure ENNReal modulo one cleanly-localized `ENNReal.ofReal`
boundary at the bridge between the structural argument (supW1On in ENNReal)
and the closed-form algebra (real geometric series).  The Finset partial sum
bound comes from `Mathlib/Algebra/Order/Field/GeomSum.lean`'s
`geom_sum_Ico_le_of_lt_one` — no case-split on `q = 0` vs `q > 0` needed,
no shifting tricks via `Finset.sum_Ico_eq_sum_range`. -/
lemma picard_iterate_geometric_bound {d : ℕ} (S : Set ℝ)
    (x : ℕ → ℝ → Measure (PhysSpace d))
    (q : ℝ) (hq_nn : 0 ≤ q) (hq_lt : q < 1)
    (D₀ : ℝ) (hD₀_nn : 0 ≤ D₀)
    (h_contract : ∀ k, supW1On S (x k) (x (k + 1)) ≤ ENNReal.ofReal (q ^ k * D₀))
    (m n : ℕ) (hmn : m ≤ n) :
    supW1On S (x m) (x n) ≤ ENNReal.ofReal (D₀ * q^m / (1 - q)) := by
  -- Iterated triangle gives the sum bound.
  have h_tri := supW1On_iterated_triangle S x m n hmn
  have h_sum_bound :
      ∑ k ∈ Finset.Ico m n, supW1On S (x k) (x (k+1)) ≤
      ∑ k ∈ Finset.Ico m n, ENNReal.ofReal (q^k * D₀) :=
    Finset.sum_le_sum (fun k _ => h_contract k)
  -- ENNReal.ofReal of finite sum (all non-negative).
  have h_qk_D₀_nn : ∀ k ∈ Finset.Ico m n, (0 : ℝ) ≤ q^k * D₀ := fun k _ =>
    mul_nonneg (pow_nonneg hq_nn k) hD₀_nn
  have h_sum_eq :
      ∑ k ∈ Finset.Ico m n, ENNReal.ofReal (q^k * D₀) =
      ENNReal.ofReal (∑ k ∈ Finset.Ico m n, q^k * D₀) :=
    (ENNReal.ofReal_sum_of_nonneg h_qk_D₀_nn).symm
  -- Real-valued geometric bound: factor D₀ + apply geom_sum_Ico_le_of_lt_one.
  have h1mq_pos : 0 < 1 - q := by linarith
  have h_real_bound : ∑ k ∈ Finset.Ico m n, q^k * D₀ ≤ D₀ * q^m / (1 - q) := by
    have h_factor : ∑ k ∈ Finset.Ico m n, q^k * D₀ =
                    D₀ * ∑ k ∈ Finset.Ico m n, q^k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [h_factor]
    calc D₀ * ∑ k ∈ Finset.Ico m n, q^k
        ≤ D₀ * (q^m / (1 - q)) :=
          mul_le_mul_of_nonneg_left (geom_sum_Ico_le_of_lt_one hq_nn hq_lt) hD₀_nn
      _ = D₀ * q^m / (1 - q) := by ring
  -- Chain everything.
  calc supW1On S (x m) (x n)
      ≤ ∑ k ∈ Finset.Ico m n, supW1On S (x k) (x (k+1)) := h_tri
    _ ≤ ∑ k ∈ Finset.Ico m n, ENNReal.ofReal (q^k * D₀) := h_sum_bound
    _ = ENNReal.ofReal (∑ k ∈ Finset.Ico m n, q^k * D₀) := h_sum_eq
    _ ≤ ENNReal.ofReal (D₀ * q^m / (1 - q)) :=
        ENNReal.ofReal_le_ofReal h_real_bound

/-- **Picard iteration is Cauchy from contraction.**

Standard Banach-fixed-point Cauchy condition derived from the geometric
contraction.

**Output form** matches `exists_wasserstein1_limit_of_cauchy`'s ENNReal-form
Cauchy hypothesis: for every `ε : ENNReal` with `0 < ε`, there is `N` such
that `supW1On (x m) (x n) < ε` for all `m, n ≥ N`.

**Proof sketch**: for the symmetric case (m > n), use `supW1On_comm`.
For `ε = ⊤`, any N works.  For `ε < ⊤`, pick N such that
`D₀ * q^N / (1-q) < ε.toReal`; combine with the geometric bound. -/
theorem picard_iterate_isCauchy_of_contraction {d : ℕ} (S : Set ℝ)
    (x : ℕ → ℝ → Measure (PhysSpace d))
    (q : ℝ) (hq_nn : 0 ≤ q) (hq_lt : q < 1)
    (D₀ : ℝ) (hD₀_nn : 0 ≤ D₀)
    (h_contract : ∀ k, supW1On S (x k) (x (k + 1)) ≤ ENNReal.ofReal (q ^ k * D₀)) :
    ∀ ε : ENNReal, 0 < ε → ∃ N, ∀ m n, N ≤ m → N ≤ n → supW1On S (x m) (x n) < ε := by
  intro ε hε
  have h1mq_pos : 0 < 1 - q := by linarith
  -- Helper: bound supW1On(x m, x n) in both orderings.
  have h_bound_both : ∀ m n, supW1On S (x m) (x n) ≤
      ENNReal.ofReal (D₀ * q^(min m n) / (1 - q)) := by
    intro m n
    by_cases h_order : m ≤ n
    · rw [min_eq_left h_order]
      exact picard_iterate_geometric_bound S x q hq_nn hq_lt D₀ hD₀_nn h_contract m n h_order
    · rw [supW1On_comm, min_eq_right (le_of_lt (not_le.mp h_order))]
      exact picard_iterate_geometric_bound S x q hq_nn hq_lt D₀ hD₀_nn h_contract n m
        (le_of_lt (not_le.mp h_order))
  -- Case split on ε = ⊤.
  by_cases hε_top : ε = ⊤
  · refine ⟨0, fun m n _ _ => ?_⟩
    rw [hε_top]
    exact lt_of_le_of_lt (h_bound_both m n) ENNReal.ofReal_lt_top
  · -- ε < ⊤ case.
    have hε_real_pos : 0 < ε.toReal := by
      rw [ENNReal.toReal_pos_iff]
      exact ⟨hε, lt_top_iff_ne_top.mpr hε_top⟩
    -- Tendsto of q^N → 0 gives existence of N.
    have h_pow_tendsto : Filter.Tendsto (fun n : ℕ => D₀ * q^n / (1 - q))
                          Filter.atTop (nhds 0) := by
      have h_pow : Filter.Tendsto (fun n : ℕ => q^n) Filter.atTop (nhds 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one hq_nn hq_lt
      have h_factored : (fun n : ℕ => D₀ * q^n / (1 - q)) =
                       fun n : ℕ => (D₀ / (1 - q)) * q^n := by
        funext n; ring
      rw [h_factored]
      have h_zero_eq : (0 : ℝ) = (D₀ / (1 - q)) * 0 := by ring
      rw [h_zero_eq]
      exact h_pow.const_mul _
    rw [Metric.tendsto_atTop] at h_pow_tendsto
    obtain ⟨N, hN⟩ := h_pow_tendsto ε.toReal hε_real_pos
    refine ⟨N, fun m n hm hn => ?_⟩
    -- Apply the bound and the tendsto-induced threshold.
    have h_min_ge : N ≤ min m n := le_min hm hn
    have h_bound_real_lt : D₀ * q^(min m n) / (1 - q) < ε.toReal := by
      have h_dist := hN (min m n) h_min_ge
      rw [Real.dist_eq] at h_dist
      have h_val_nn : 0 ≤ D₀ * q^(min m n) / (1 - q) :=
        div_nonneg (mul_nonneg hD₀_nn (pow_nonneg hq_nn _)) (le_of_lt h1mq_pos)
      rw [abs_sub_lt_iff] at h_dist
      linarith [h_dist.1]
    calc supW1On S (x m) (x n)
        ≤ ENNReal.ofReal (D₀ * q^(min m n) / (1 - q)) := h_bound_both m n
      _ < ENNReal.ofReal ε.toReal :=
          (ENNReal.ofReal_lt_ofReal_iff hε_real_pos).mpr h_bound_real_lt
      _ = ε := ENNReal.ofReal_toReal hε_top

/-- **Pointwise W₁ bounded by `supW1On`**.

For `t ∈ S`, the per-`t` Wasserstein-1 distance is bounded by the sup-W₁
over `S`.  Routine `le_iSup` chain.  Mirror image of the `supW1On`-shape
lemmas (`supW1On_triangle`, `supW1On_self`) — the per-point extraction
from the sup. -/
lemma wasserstein1_le_supW1On {d : ℕ}
    (S : Set ℝ) (ρ σ : ℝ → Measure (PhysSpace d))
    (t : ℝ) (ht : t ∈ S) :
    wasserstein1 (ρ t) (σ t) ≤ supW1On S ρ σ := by
  unfold supW1On
  exact le_iSup_of_le t (le_iSup_of_le ht le_rfl)

/-- **Uniform-in-`t` W₁-tendsto from supW1On Cauchy + per-`t`
pointwise W₁-tendsto**.

Given a sequence `x n : ℝ → Measure (PhysSpace d)` Cauchy in `supW1On S` and
per-`t` pointwise W₁-tendsto to `y t`, the convergence is uniform in `t ∈ S`:
for every `ε : ENNReal` with `0 < ε`, there is `N` such that
`wasserstein1 (x n t) (y t) ≤ ε` for all `n ≥ N` and `t ∈ S`.

**Proof idea**: triangle through `x m t` for arbitrarily large `m`:
`wasserstein1 (x n t) (y t) ≤ wasserstein1 (x n t) (x m t) + wasserstein1 (x m t) (y t)`.
The first term `≤ supW1On (x n) (x m) < ε` by Cauchy; the second `→ 0` by
pointwise tendsto.  Apply `ENNReal.le_of_forall_pos_le_add` for the limit
passage. -/
lemma picard_iterate_limit_uniform_tendsto {d : ℕ}
    (S : Set ℝ) (x : ℕ → ℝ → Measure (PhysSpace d))
    (y : ℝ → Measure (PhysSpace d))
    (h_cauchy : ∀ ε : ENNReal, 0 < ε → ∃ N, ∀ m n, N ≤ m → N ≤ n →
                supW1On S (x m) (x n) < ε)
    (h_pointwise : ∀ t ∈ S,
        Filter.Tendsto (fun n => wasserstein1 (x n t) (y t)) Filter.atTop (nhds 0)) :
    ∀ ε : ENNReal, 0 < ε → ∃ N, ∀ n, N ≤ n → ∀ t ∈ S,
        wasserstein1 (x n t) (y t) ≤ ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := h_cauchy ε hε
  refine ⟨N, fun n hn t ht => ?_⟩
  -- Use ENNReal.le_of_forall_pos_le_add to reduce to `≤ ε + ε'` for ε' > 0.
  apply ENNReal.le_of_forall_pos_le_add
  intro ε' hε'_pos _
  -- Pick m ≥ N such that wasserstein1 (x m t) (y t) ≤ ε'.
  have h_tend := h_pointwise t ht
  rw [ENNReal.tendsto_atTop_zero] at h_tend
  have hε'_ennreal_pos : (0 : ENNReal) < (ε' : ENNReal) := by
    exact_mod_cast hε'_pos
  obtain ⟨M, hM⟩ := h_tend (ε' : ENNReal) hε'_ennreal_pos
  let m := max N M
  have hmN : N ≤ m := le_max_left _ _
  have hmM : M ≤ m := le_max_right _ _
  -- Apply triangle inequality.
  calc wasserstein1 (x n t) (y t)
      ≤ wasserstein1 (x n t) (x m t) + wasserstein1 (x m t) (y t) :=
        wasserstein1_triangle _ _ _
    _ ≤ supW1On S (x n) (x m) + wasserstein1 (x m t) (y t) :=
        add_le_add (wasserstein1_le_supW1On S (x n) (x m) t ht) le_rfl
    _ ≤ ε + (ε' : ENNReal) := by
        gcongr
        · exact le_of_lt (hN n m hn hmN)
        · exact hM m hmM

/-- **Bundle the Picard iteration's W₁-limit as a `VlasovMeasureCurve`**.

Given a sequence of `VlasovMeasureCurve d T M` iterates with the geometric
contraction property `supW1On (x k) (x (k+1)) ≤ ofReal (q^k * D₀)`,
produce a limit `ρ_lim : VlasovMeasureCurve d T M` such that
`wasserstein1 ((x n).ρ t) (ρ_lim.ρ t) → 0` pointwise (and, by the helper
`picard_iterate_limit_uniform_tendsto`, uniformly) in `t ∈ Icc 0 T`.

**Proof strategy**:

1. Apply `picard_iterate_isCauchy_of_contraction` to get supW1On Cauchy.
2. Per-`t ∈ Icc 0 T`, the pointwise sequence `n ↦ (x n).ρ t` is Cauchy in
   W₁ (by `wasserstein1_le_supW1On` from the sup-Cauchy).
3. Invoke `exists_wasserstein1_limit_of_cauchy` per-`t` to obtain the
   pointwise limit `ρ_lim t` (with probability, integrability, moment bound,
   W₁-tendsto, all from the strengthened placeholder).
4. Extend `ρ_lim` to all of `ℝ` by `(x 0).ρ` outside `Icc 0 T` (so the
   `isProb` field — universal in `t` — holds).
5. Verify the four `VlasovMeasureCurve` fields:
   * `isProb`: from the placeholder (inside `Icc 0 T`) + `(x 0).isProb`
     (outside).
   * `hasMoment`: from the placeholder's strengthened moment-preservation
     conjunct (`∫‖y‖ ∂μ ≤ M`).
   * `yIntegrable`: from the placeholder.
   * `hW1Cont`: ε/3 triangle through `x N`, using
     `picard_iterate_limit_uniform_tendsto` for the uniform tendsto +
     `(x N).hW1Cont` for the middle term. -/
theorem picard_iterate_exists_limit {d : ℕ} [NeZero d]
    {T : ℝ} {M : ℝ → ℝ}
    (x : ℕ → VlasovMeasureCurve d T M)
    (q : ℝ) (hq_nn : 0 ≤ q) (hq_lt : q < 1)
    (D₀ : ℝ) (hD₀_nn : 0 ≤ D₀)
    (h_contract : ∀ k, supW1On (Set.Icc 0 T) (x k).ρ (x (k + 1)).ρ ≤
                       ENNReal.ofReal (q ^ k * D₀)) :
    ∃ ρ_lim : VlasovMeasureCurve d T M,
      ∀ t ∈ Set.Icc (0 : ℝ) T,
        Filter.Tendsto (fun n => wasserstein1 ((x n).ρ t) (ρ_lim.ρ t))
          Filter.atTop (nhds 0) := by
  -- Step 1: supW1On-Cauchy from the contraction.
  have h_cauchy := picard_iterate_isCauchy_of_contraction
    (Set.Icc (0 : ℝ) T) (fun n => (x n).ρ) q hq_nn hq_lt D₀ hD₀_nn h_contract
  -- Step 2: per-t Cauchy from the supW1On bound.
  have h_per_t_cauchy : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ ε : ENNReal, 0 < ε →
      ∃ N, ∀ m n, N ≤ m → N ≤ n →
        wasserstein1 ((x m).ρ t) ((x n).ρ t) < ε := by
    intro t ht ε hε
    obtain ⟨N, hN⟩ := h_cauchy ε hε
    refine ⟨N, fun m n hm hn => ?_⟩
    exact lt_of_le_of_lt (wasserstein1_le_supW1On _ _ _ t ht) (hN m n hm hn)
  -- Step 3: per-t Classical.choose to extract the limit measure.
  have h_per_t : ∀ t ∈ Set.Icc (0 : ℝ) T, ∃ μ : Measure (PhysSpace d),
      IsProbabilityMeasure μ ∧
      Integrable (fun y : PhysSpace d => ‖y‖) μ ∧
      ∫ y, ‖y‖ ∂μ ≤ M t ∧
      Filter.Tendsto (fun n => wasserstein1 ((x n).ρ t) μ) Filter.atTop (nhds 0) := by
    intro t ht
    haveI : ∀ n, IsProbabilityMeasure ((x n).ρ t) := fun n => (x n).isProb t
    exact exists_wasserstein1_limit_of_cauchy (fun n => (x n).ρ t) (M t)
      (fun n => (x n).hasMoment t ht) (fun n => (x n).yIntegrable t ht)
      (h_per_t_cauchy t ht)
  -- Step 4: define ρ_lim via dependent choice on whether t ∈ Icc 0 T.
  let ρ_lim : ℝ → Measure (PhysSpace d) := fun t =>
    if ht : t ∈ Set.Icc (0 : ℝ) T then Classical.choose (h_per_t t ht)
    else (x 0).ρ t
  -- Helper accessor on Icc.
  have hρ_spec : ∀ t (ht : t ∈ Set.Icc (0 : ℝ) T),
      ρ_lim t = Classical.choose (h_per_t t ht) := by
    intro t ht
    simp only [ρ_lim, dif_pos ht]
  -- Step 5: verify the four VlasovMeasureCurve fields.
  -- isProb: universal in t.
  have h_isProb : ∀ t, IsProbabilityMeasure (ρ_lim t) := by
    intro t
    by_cases ht : t ∈ Set.Icc (0 : ℝ) T
    · rw [hρ_spec t ht]
      exact (Classical.choose_spec (h_per_t t ht)).1
    · simp only [ρ_lim, dif_neg ht]
      exact (x 0).isProb t
  -- hasMoment: from the placeholder's strengthened conclusion.
  have h_hasMoment : ∀ t ∈ Set.Icc (0 : ℝ) T, ∫ y, ‖y‖ ∂(ρ_lim t) ≤ M t := by
    intro t ht
    rw [hρ_spec t ht]
    exact (Classical.choose_spec (h_per_t t ht)).2.2.1
  -- yIntegrable: from the placeholder.
  have h_yIntegrable : ∀ t ∈ Set.Icc (0 : ℝ) T,
      Integrable (fun y : PhysSpace d => ‖y‖) (ρ_lim t) := by
    intro t ht
    rw [hρ_spec t ht]
    exact (Classical.choose_spec (h_per_t t ht)).2.1
  -- Pointwise tendsto on Icc 0 T (also part of the conclusion).
  have h_tendsto : ∀ t ∈ Set.Icc (0 : ℝ) T,
      Filter.Tendsto (fun n => wasserstein1 ((x n).ρ t) (ρ_lim t))
        Filter.atTop (nhds 0) := by
    intro t ht
    have h_spec := (Classical.choose_spec (h_per_t t ht)).2.2.2
    rw [hρ_spec t ht]
    exact h_spec
  -- Uniform tendsto from the helper.
  have h_uniform := picard_iterate_limit_uniform_tendsto
    (Set.Icc (0 : ℝ) T) (fun n => (x n).ρ) ρ_lim h_cauchy h_tendsto
  -- hW1Cont: ε/3 argument through x N.
  have h_hW1Cont : ∀ s ∈ Set.Icc (0 : ℝ) T,
      ContinuousWithinAt (fun t => (wasserstein1 (ρ_lim s) (ρ_lim t)).toReal)
                         (Set.Icc 0 T) s := by
    intro s hs
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    -- Self-distance at t = s is 0.
    have h_self : (wasserstein1 (ρ_lim s) (ρ_lim s)).toReal = 0 := by
      rw [wasserstein1_self]; rfl
    -- Pick N via uniform tendsto for tolerance ENNReal.ofReal (ε/3).
    have hε3 : 0 < ε / 3 := by linarith
    have hε3_nn : 0 < ENNReal.ofReal (ε / 3) := by
      exact_mod_cast ENNReal.ofReal_pos.mpr hε3
    obtain ⟨N, hN_uniform⟩ := h_uniform (ENNReal.ofReal (ε / 3)) hε3_nn
    -- Use (x N).hW1Cont for the middle term.
    have hN_cont := (x N).hW1Cont s hs
    rw [Metric.continuousWithinAt_iff] at hN_cont
    have h_self_N : (wasserstein1 ((x N).ρ s) ((x N).ρ s)).toReal = 0 := by
      rw [wasserstein1_self]; rfl
    obtain ⟨δ, hδ_pos, hδ_bound⟩ := hN_cont (ε / 3) hε3
    refine ⟨δ, hδ_pos, fun t ht hdist => ?_⟩
    -- Triangle bound in ENNReal then toReal.
    have h_W1_first : wasserstein1 (ρ_lim s) ((x N).ρ s) ≤ ENNReal.ofReal (ε / 3) := by
      rw [wasserstein1_comm]
      exact hN_uniform N le_rfl s hs
    have h_W1_third : wasserstein1 ((x N).ρ t) (ρ_lim t) ≤ ENNReal.ofReal (ε / 3) :=
      hN_uniform N le_rfl t ht
    -- Finiteness of the limit's W₁.
    haveI hPs_inf : IsProbabilityMeasure (ρ_lim s) := h_isProb s
    haveI hPt_inf : IsProbabilityMeasure (ρ_lim t) := h_isProb t
    have h_finite : wasserstein1 (ρ_lim s) (ρ_lim t) ≠ ⊤ :=
      wasserstein1_ne_top_of_finite_moment _ _
        (h_yIntegrable s hs) (h_yIntegrable t ht)
    -- Triangle.
    have h_tri : wasserstein1 (ρ_lim s) (ρ_lim t) ≤
        wasserstein1 (ρ_lim s) ((x N).ρ s) + wasserstein1 ((x N).ρ s) ((x N).ρ t) +
          wasserstein1 ((x N).ρ t) (ρ_lim t) := by
      calc wasserstein1 (ρ_lim s) (ρ_lim t)
          ≤ wasserstein1 (ρ_lim s) ((x N).ρ t) + wasserstein1 ((x N).ρ t) (ρ_lim t) :=
            wasserstein1_triangle _ _ _
        _ ≤ (wasserstein1 (ρ_lim s) ((x N).ρ s) + wasserstein1 ((x N).ρ s) ((x N).ρ t))
              + wasserstein1 ((x N).ρ t) (ρ_lim t) :=
            add_le_add (wasserstein1_triangle _ _ _) le_rfl
    -- Bound the middle term via hδ_bound.
    have h_mid_lt : (wasserstein1 ((x N).ρ s) ((x N).ρ t)).toReal < ε / 3 := by
      have hδb := hδ_bound ht hdist
      rw [h_self_N, Real.dist_eq, sub_zero] at hδb
      have h_nn : 0 ≤ (wasserstein1 ((x N).ρ s) ((x N).ρ t)).toReal :=
        ENNReal.toReal_nonneg
      rwa [abs_of_nonneg h_nn] at hδb
    -- Convert toReal and bound by ε/3 + ε/3 + ε/3 = ε.
    have h_W1_first_ne_top : wasserstein1 (ρ_lim s) ((x N).ρ s) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top h_W1_first
    have h_W1_third_ne_top : wasserstein1 ((x N).ρ t) (ρ_lim t) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top h_W1_third
    haveI hPNs : IsProbabilityMeasure ((x N).ρ s) := (x N).isProb s
    haveI hPNt : IsProbabilityMeasure ((x N).ρ t) := (x N).isProb t
    have h_mid_ne_top : wasserstein1 ((x N).ρ s) ((x N).ρ t) ≠ ⊤ :=
      wasserstein1_ne_top_of_finite_moment _ _
        ((x N).yIntegrable s hs) ((x N).yIntegrable t ht)
    have h_W1_first_real : (wasserstein1 (ρ_lim s) ((x N).ρ s)).toReal ≤ ε / 3 := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h_W1_first
      rwa [ENNReal.toReal_ofReal hε3.le] at this
    have h_W1_third_real : (wasserstein1 ((x N).ρ t) (ρ_lim t)).toReal ≤ ε / 3 := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h_W1_third
      rwa [ENNReal.toReal_ofReal hε3.le] at this
    -- Apply ENNReal.toReal to the triangle.
    have h_tri_real : (wasserstein1 (ρ_lim s) (ρ_lim t)).toReal ≤
        (wasserstein1 (ρ_lim s) ((x N).ρ s)).toReal +
          (wasserstein1 ((x N).ρ s) ((x N).ρ t)).toReal +
          (wasserstein1 ((x N).ρ t) (ρ_lim t)).toReal := by
      have h_add_ne_top : wasserstein1 (ρ_lim s) ((x N).ρ s) +
                          wasserstein1 ((x N).ρ s) ((x N).ρ t) +
                          wasserstein1 ((x N).ρ t) (ρ_lim t) ≠ ⊤ := by
        simp [h_W1_first_ne_top, h_mid_ne_top, h_W1_third_ne_top]
      have := ENNReal.toReal_mono h_add_ne_top h_tri
      rw [ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨h_W1_first_ne_top, h_mid_ne_top⟩)
            h_W1_third_ne_top,
          ENNReal.toReal_add h_W1_first_ne_top h_mid_ne_top] at this
      exact this
    rw [Real.dist_eq, h_self, sub_zero,
        abs_of_nonneg ENNReal.toReal_nonneg]
    linarith [h_tri_real, h_mid_lt, h_W1_first_real, h_W1_third_real]
  -- Bundle.
  refine ⟨{ρ := ρ_lim, isProb := h_isProb, hasMoment := h_hasMoment,
           yIntegrable := h_yIntegrable, hW1Cont := h_hW1Cont}, ?_⟩
  intro t ht
  exact h_tendsto t ht

end Vlasov
