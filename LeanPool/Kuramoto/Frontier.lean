/-
Copyright (c) 2026 Ben Cassie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Cassie
-/

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Data.Nat.Nth
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import LeanPool.Kuramoto.Weighted
import LeanPool.Kuramoto.Contraction
import LeanPool.Kuramoto.OrderParameter
import LeanPool.Kuramoto.GradientFlow

/-!
# Kuramoto Frontier: ODE Solutions, Lyapunov Stability, and Synchronisation

This file extends the Kuramoto oscillator library with results on:
1. ODE existence and uniqueness (the vector field is smooth, hence locally Lipschitz)
2. Lyapunov stability along trajectories
3. Local synchronisation under the semicircle condition
4. Phase diameter non-expansion
5. Convergence to synchrony

We build on the algebraic identities proved in `Weighted.lean`, `Contraction.lean`,
and `GradientFlow.lean`.
-/

open Real Finset

/-! ## Target 1: Smoothness of the Kuramoto vector field and ODE existence -/

/-- The Kuramoto vector field as a function `(Fin N → ℝ) → (Fin N → ℝ)`. -/
noncomputable def kuramotoVectorField (K : ℝ) (N : ℕ) (W : Fin N → Fin N → ℝ) :
    (Fin N → ℝ) → (Fin N → ℝ) :=
  fun θ i => weightedKuramotoF K N W i θ

/-
The Kuramoto vector field is smooth (infinitely differentiable).
-/
theorem kuramotoVectorField_contDiff (K : ℝ) (N : ℕ) (W : Fin N → Fin N → ℝ) :
    ContDiff ℝ ⊤ (kuramotoVectorField K N W) := by
      apply_rules [ ContDiff.mul, ContDiff.sum, contDiff_const, contDiff_apply ];
      fun_prop

/-
The Kuramoto vector field is locally Lipschitz at every point.
-/
theorem kuramotoVectorField_locallyLipschitz (K : ℝ) (N : ℕ) (W : Fin N → Fin N → ℝ) :
    ∀ θ₀ : Fin N → ℝ, ∃ (ε : ℝ) (_ : 0 < ε) (L : NNReal),
      LipschitzOnWith L (kuramotoVectorField K N W) (Metric.ball θ₀ ε) := by
  have h_lipschitz : ∀ θ₀ : (Fin N) → ℝ, ∃ ε > 0, ∃ L, LipschitzOnWith L
      (kuramotoVectorField K N W) (Metric.ball θ₀ ε) := by
    intro θ₀
    have h_cont_diff : ContDiff ℝ 1 (kuramotoVectorField K N W) := by
      exact ContDiff.of_le ( kuramotoVectorField_contDiff K N W ) ( by norm_num )
    have h_lipschitz : ∃ ε > 0, ∃ L, ∀ x ∈ Metric.ball θ₀ ε, ∀ y ∈ Metric.ball θ₀ ε,
        ‖kuramotoVectorField K N W x - kuramotoVectorField K N W y‖ ≤ L * ‖x - y‖ := by
      have h_lipschitz : ∃ ε > 0, ∃ L, ∀ x ∈ Metric.ball θ₀ ε, ‖fderiv ℝ (kuramotoVectorField K N
                                                                          W) x‖ ≤ L := by
        have := h_cont_diff.continuous_fderiv;
        exact ⟨ 1, zero_lt_one, _, fun x hx => le_csSup ( IsCompact.bddAbove <|
                                                         isCompact_closedBall θ₀ 1 |>
                                                         IsCompact.image <| continuous_norm.comp <|
                                                         this one_ne_zero ) <| Set.mem_image_of_mem
               _ <| Metric.mem_closedBall.mpr <| le_of_lt hx ⟩;
      obtain ⟨ ε, ε_pos, L, hL ⟩ := h_lipschitz;
      use ε, ε_pos, L;
      intro x hx y hy;
      have := @Convex.norm_image_sub_le_of_norm_fderiv_le;
      simpa only [ norm_sub_rev ] using this ( fun z hz => h_cont_diff.contDiffAt.differentiableAt
                                              ( by norm_num ) ) hL ( convex_ball θ₀ ε ) hx hy;
    obtain ⟨ ε, hε, L, hL ⟩ := h_lipschitz;
    exact ⟨ ε, hε, ⟨ L.toNNReal, by
      simpa [ lipschitzOnWith_iff_norm_sub_le ] using fun x hx y hy =>
        le_trans ( hL x hx y hy )
          ( mul_le_mul_of_nonneg_right ( le_max_left _ _ ) ( norm_nonneg _ ) ) ⟩ ⟩;
  grind +qlia

/-
ODE existence for the Kuramoto system.
-/
theorem kuramoto_ode_exists (K : ℝ) (N : ℕ) (W : Fin N → Fin N → ℝ)
    (θ₀ : Fin N → ℝ) :
    ∃ (θ : ℝ → Fin N → ℝ),
      θ 0 = θ₀ ∧
      ∃ (ε : ℝ) (_ : 0 < ε),
        ∀ t ∈ Set.Ioo (-ε) ε, HasDerivAt θ (kuramotoVectorField K N W (θ t)) t := by
          have h_cont_diff : ContDiff ℝ 1 (kuramotoVectorField K N W) := by
            exact ContDiff.of_le ( kuramotoVectorField_contDiff K N W ) ( by norm_num );
          have := @ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀;
          simpa using this ( h_cont_diff.contDiffAt ) 0

/-
ODE forward uniqueness.
-/
theorem kuramoto_ode_unique (K : ℝ) (N : ℕ) (W : Fin N → Fin N → ℝ)
    (θ θ' : ℝ → Fin N → ℝ) {T : ℝ} (_hT : 0 ≤ T)
    (hinit : θ 0 = θ' 0)
    (hf : ContinuousOn θ (Set.Icc 0 T))
    (hf' : ∀ t ∈ Set.Ico 0 T, HasDerivWithinAt θ
      (kuramotoVectorField K N W (θ t)) (Set.Ici t) t)
    (hg : ContinuousOn θ' (Set.Icc 0 T))
    (hg' : ∀ t ∈ Set.Ico 0 T, HasDerivWithinAt θ'
      (kuramotoVectorField K N W (θ' t)) (Set.Ici t) t)
    (hLip : ∃ (M : NNReal), LipschitzWith M (kuramotoVectorField K N W)) :
    Set.EqOn θ θ' (Set.Icc 0 T) := by
      have picard_lindelof : ∀ {f g : ℝ → (Fin N → ℝ)}, ContinuousOn f (Set.Icc 0 T) → ContinuousOn
          g (Set.Icc 0 T) →
          (∀ t ∈ Set.Ico 0 T, HasDerivWithinAt f (kuramotoVectorField K N W (f t)) (Set.Ici t) t) →
          (∀ t ∈ Set.Ico 0 T, HasDerivWithinAt g (kuramotoVectorField K N W (g t)) (Set.Ici t) t) →
          f 0 = g 0 → Set.EqOn f g (Set.Icc 0 T) := by
        intros f g hf hg hf' hg' hinit
        have := @ODE_solution_unique;
        exact this ( fun t => hLip.choose_spec ) hf hf' hg hg' hinit;
      exact picard_lindelof hf hg hf' hg' hinit

/-! ## Target 2: Lyapunov stability along trajectories -/

theorem lyapunov_derivative_eq
    (K : ℝ) (N : ℕ) (W : Fin N → Fin N → ℝ) (hW : ∀ i j, W i j = W j i)
    (θ : Fin N → ℝ) :
    ∑ i, weightedKuramotoF K N W i θ *
      deriv (fun x => weightedKuramotoV K N W (Function.update θ i x)) (θ i) =
    -(∑ i, weightedKuramotoF K N W i θ ^ 2) := by
      rw [ ← Finset.sum_neg_distrib ];
      exact Finset.sum_congr rfl fun i _ => by rw [ weighted_gradient_identity K N W hW θ
                                                   i ]; ring;

theorem lyapunov_derivative_nonpos
    (K : ℝ) (hK : 0 < K) (N : ℕ) (W : Fin N → Fin N → ℝ) (hW : ∀ i j, W i j = W j i)
    (θ : Fin N → ℝ) :
    ∑ i, weightedKuramotoF K N W i θ *
      deriv (fun x => weightedKuramotoV K N W (Function.update θ i x)) (θ i) ≤ 0 := by
        apply weighted_lyapunov_descent K hK N W hW θ

theorem lyapunov_nonincreasing_along_trajectory
    (K : ℝ) (_hK : 0 < K) (N : ℕ) (W : Fin N → Fin N → ℝ) (_hW : ∀ i j, W i j = W j i)
    (θ : ℝ → Fin N → ℝ)
    (hsol : ∀ t, HasDerivAt θ (kuramotoVectorField K N W (θ t)) t) :
    ∀ t, HasDerivAt (fun s => weightedKuramotoV K N W (θ s))
      (∑ i, weightedKuramotoF K N W i (θ t) *
        deriv (fun x => weightedKuramotoV K N W (Function.update (θ t) i x)) ((θ t) i)) t := by
  intros t
  have h_diff : DifferentiableAt ℝ (fun s => weightedKuramotoV K N W s) (θ t) := by
    apply_rules [ DifferentiableAt.neg, DifferentiableAt.const_mul, DifferentiableAt.sum,
                 DifferentiableAt.cos, differentiableAt_id, differentiableAt_const ];
    fun_prop;
  have hcomp := HasFDerivAt.comp_hasDerivAt t ( h_diff.hasFDerivAt ) ( hsol t );
  refine hcomp.congr_deriv ?_;
  have h_fderiv : ∀ i, deriv (fun x => weightedKuramotoV K N W (Function.update (θ t) i x)) (θ t i)
    = (fderiv ℝ (fun s => weightedKuramotoV K N W s) (θ t)) (fun j => if j = i then 1 else 0) := by
    intro i; rw [ deriv ];
    rw [ show ( fun x => weightedKuramotoV K N W ( Function.update ( θ t ) i x ) )
          = ( fun s => weightedKuramotoV K N W s ) ∘ ( fun x => Function.update ( θ t ) i x )
          by ext; rfl,
        fderiv_comp ] <;> norm_num [ h_diff ];
    · rw [ deriv_pi ] <;> norm_num [ Function.update_apply ];
      · exact congr_arg _ ( funext fun j => by aesop );
      · exact fun j => by split_ifs <;> norm_num;
    · intro j; by_cases hj : j = i <;> simp +decide [ hj ];
  rw [ show kuramotoVectorField K N W ( θ t ) = ∑ i, ( weightedKuramotoF K N W i ( θ t ) ) • ( fun
                                                                                              j =>
                                                                                              if j =
                                                                                              i then
                                                                                              1 else
                                                                                              0 :
                                                                                              Fin N
                                                                                              → ℝ )
      from ?_ ];
  · rw [ map_sum, Finset.sum_congr rfl ]; intros; aesop;
  · ext i; simp +decide [ kuramotoVectorField ];

/-! ## Target 3: Local synchronisation under the semicircle condition -/

theorem semicircle_extremal_contraction
    (K : ℝ) (_hK : 0 < K) (N : ℕ) (_hN : 0 < N)
    (W : Fin N → Fin N → ℝ) (_hW : ∀ i j, W i j = W j i)
    (hWnn : ∀ i j, 0 ≤ W i j)
    (θ : Fin N → ℝ) (i j : Fin N) (_hij : i ≠ j)
    (_hWij : 0 < W i j)
    (hWeq : ∀ k, W i k = W j k)
    (hmax : ∀ k, θ k ≤ θ i)
    (hmin : ∀ k, θ j ≤ θ k)
    (hgap : θ i - θ j < Real.pi) :
    weightedKuramotoF K N W i θ - weightedKuramotoF K N W j θ ≤ 0 := by
      unfold weightedKuramotoF; simp +decide [ *, Finset.mul_sum _ _ _ ]; ring_nf;
      refine Finset.sum_le_sum fun k _ => ?_; simp +decide [ *, mul_assoc ]; ring_nf; (
      exact mul_nonpos_of_nonneg_of_nonpos ( hWnn _ _ )
          ( Real.sin_nonpos_of_nonpos_of_neg_pi_le ( by linarith [ hmax k, hmin k ] )
            ( by linarith [ hmax k, hmin k ] ) ) |> le_trans <| mul_nonneg ( hWnn _ _ )
          ( Real.sin_nonneg_of_nonneg_of_le_pi ( by linarith [ hmax k, hmin k ] )
            ( by linarith [ hmax k, hmin k ] ) ));

lemma sin_nonneg_of_phase_between
    (θ : Fin N → ℝ) (i j k : Fin N)
    (hmax : θ k ≤ θ i) (hmin : θ j ≤ θ k)
    (hgap : θ i - θ j < Real.pi) :
    0 ≤ Real.sin (θ k - θ j) ∧ 0 ≤ Real.sin (θ i - θ k) := by
      constructor <;> exact Real.sin_nonneg_of_nonneg_of_le_pi ( by linarith ) ( by linarith )

/-! ## Target 4: Phase diameter non-expansion -/

theorem extremal_gap_derivative_nonpos
    (K : ℝ) (hK : 0 < K) (N : ℕ) (hN : 0 < N)
    (W : Fin N → Fin N → ℝ) (hW : ∀ i j, W i j = W j i)
    (hWnn : ∀ i j, 0 ≤ W i j)
    (hWeq : ∀ i j k, W i k = W j k)
    (θ : ℝ → Fin N → ℝ)
    (hsol : ∀ t, HasDerivAt θ (kuramotoVectorField K N W (θ t)) t)
    (t : ℝ) (i j : Fin N) (hij : i ≠ j)
    (hWij : 0 < W i j)
    (hmax : ∀ k, θ t k ≤ θ t i)
    (hmin : ∀ k, θ t j ≤ θ t k)
    (hgap : θ t i - θ t j < Real.pi) :
    HasDerivAt (fun s => θ s i - θ s j)
      (weightedKuramotoF K N W i (θ t) - weightedKuramotoF K N W j (θ t)) t ∧
    weightedKuramotoF K N W i (θ t) - weightedKuramotoF K N W j (θ t) ≤ 0 := by
      constructor;
      · exact HasDerivAt.sub ( hasDerivAt_pi.1 ( hsol t ) i ) ( hasDerivAt_pi.1 ( hsol t ) j )
      · apply_rules [ semicircle_extremal_contraction ]

/-! ## Target 5: Convergence to synchrony -/

theorem kuramotoR_norm_eq_one_at_synchrony
    (N : ℕ) (hN : 0 < N) (θ : Fin N → ℝ)
    (hsync : ∀ i j : Fin N, θ i = θ j) :
    ‖kuramotoR N θ‖ = 1 := by
      unfold kuramotoR; norm_num [ ← hsync ⟨ 0, hN ⟩ ];
      linarith

theorem weightedKuramotoV_bounded_below
    (K : ℝ) (hK : 0 < K) (N : ℕ)
    (W : Fin N → Fin N → ℝ) (hWnn : ∀ i j, 0 ≤ W i j) (hWle : ∀ i j, W i j ≤ 1)
    (θ : Fin N → ℝ) :
    -(K / 2) * (N : ℝ) ^ 2 ≤ weightedKuramotoV K N W θ := by
      exact mul_le_mul_of_nonpos_left ( le_trans ( Finset.sum_le_sum fun i _ =>
          Finset.sum_le_sum fun j _ => show W i j * Real.cos ( θ j - θ i ) ≤ 1 by
            nlinarith [ hWnn i j, hWle i j, Real.cos_le_one ( θ j - θ i ) ] )
          ( by norm_num; nlinarith ) ) ( by linarith )

/-! ### Helper lemmas for convergence proof -/

/-
Barbalat's lemma (Lipschitz version): A non-negative Lipschitz function whose
    antiderivative is bounded above tends to zero at infinity.
-/
private theorem barbalat_of_nonneg_lipschitz {f F : ℝ → ℝ} {C : ℝ}
    (hf_nn : ∀ t, 0 ≤ f t)
    (hf_lip : ∀ s t, |f s - f t| ≤ C * |s - t|)
    (hC_pos : 0 < C)
    (hF_deriv : ∀ t, HasDerivAt F (f t) t)
    (hF_bdd : BddAbove (Set.range F)) :
    Filter.Tendsto f Filter.atTop (nhds 0) := by
  -- By contradiction, assume that $f$ does not tend to $0$ as $t$ tends to infinity.
  by_contra h_contra;
  -- Since $f$ does not tend to zero, there exists some $\epsilon > 0$ such that for all $T$, there
  -- exists $t > T$ with $f(t) \geq \epsilon$.
  obtain ⟨ε, hε_pos, hε⟩ : ∃ ε > 0, ∀ T, ∃ t > T, f t ≥ ε := by
    rw [ Metric.tendsto_nhds ] at h_contra;
    simp +zetaDelta only [gt_iff_lt, dist_zero_right, norm_eq_abs, Filter.eventually_atTop,
      not_forall, not_exists, not_lt, ge_iff_le] at *;
    exact ⟨ h_contra.choose, h_contra.choose_spec.1, fun T => by
      obtain ⟨ t, ht₁, ht₂ ⟩ := h_contra.choose_spec.2 ( T + 1 )
      exact ⟨ t, by linarith, by linarith [ abs_of_nonneg ( hf_nn t ) ] ⟩ ⟩;
  -- Choose a subsequence $t_n \to \infty$ such that $f(t_n) \geq \epsilon$.
  obtain ⟨t_n, ht_n⟩ : ∃ t_n : ℕ → ℝ, (∀ n, t_n n > n) ∧ (∀ n, f (t_n n) ≥ ε) ∧
      (∀ n, t_n (n + 1) > t_n n + ε / (2 * C)) := by
    choose t ht using hε;
    use fun n => Nat.recOn n ( t 0 ) fun n ih => t ( ih + ε / ( 2 * C ) + 1 );
    refine ⟨ ?_, ?_, ?_ ⟩ <;> intro n <;> induction n <;> norm_num at *;
    any_goals linarith [ ht 0, ht ( t 0 + ε / ( 2 * C ) + 1 ) ];
    · linarith [ ht ( Nat.rec ( t 0 ) ( fun n ih => t ( ih + ε / ( 2 * C ) + 1 ) ) ‹_› + ε / ( 2 *
                                                                                              C ) +
                     1 ), div_pos hε_pos ( mul_pos zero_lt_two hC_pos ) ];
    · exact ht _ |>.2;
    · linarith [ ht ( t ( Nat.rec ( t 0 ) ( fun n ih => t ( ih + ε / ( 2 * C ) + 1 ) ) ‹_›
        + ε / ( 2 * C ) + 1 ) + ε / ( 2 * C ) + 1 ) ];
  -- By the properties of the antiderivative, we have $F(t_n + \frac{\epsilon}{2C}) - F(t_n) \geq
  -- \frac{\epsilon^2}{4C}$.
  have h_antideriv : ∀ n, F (t_n n + ε / (2 * C)) - F (t_n n) ≥ ε^2 / (4 * C) := by
    -- By the properties of the antiderivative, we have $F(t_n + \frac{\epsilon}{2C}) - F(t_n) \geq
    -- \int_{t_n}^{t_n + \frac{\epsilon}{2C}} f(s) \, ds$.
    have h_antideriv_integral : ∀ n, F (t_n n + ε / (2 * C)) - F (t_n n) ≥ ∫ s in t_n n..t_n n + ε
        / (2 * C), f s := by
      intro n
      rw [ intervalIntegral.integral_eq_sub_of_hasDerivAt ( fun x _ => hF_deriv x ) ?_ ]
      apply_rules [ ContinuousOn.intervalIntegrable ]
      exact Continuous.continuousOn ( by
        exact continuous_iff_continuousAt.mpr fun x => by
          exact tendsto_iff_norm_sub_tendsto_zero.mpr <| squeeze_zero
            ( fun _ => by positivity ) ( fun _ => hf_lip _ _ ) <|
            Continuous.tendsto' ( by continuity ) _ _ <| by simp )
    -- Since $f(s) \geq \frac{\epsilon}{2}$ for all $s \in [t_n, t_n + \frac{\epsilon}{2C}]$, we
    -- have $\int_{t_n}^{t_n + \frac{\epsilon}{2C}} f(s) \, ds \geq \int_{t_n}^{t_n +
    -- \frac{\epsilon}{2C}} \frac{\epsilon}{2} \, ds$.
    have h_integral_bound : ∀ n, ∫ s in t_n n..t_n n + ε / (2 * C), f s ≥ ∫ s in t_n n..t_n n + ε /
        (2 * C), ε / 2 := by
      intro n; refine intervalIntegral.integral_mono_on ?_ ?_ ?_ ?_ <;> norm_num;
      · positivity;
      · apply_rules [ Continuous.intervalIntegrable ];
        rw [ Metric.continuous_iff ];
        exact fun x ε hε => ⟨ ε / C, div_pos hε hC_pos, fun y hy => by
          rw [ lt_div_iff₀' hC_pos ] at hy; exact lt_of_le_of_lt ( hf_lip _ _ ) hy ⟩;
      · intro x hx₁ hx₂; have := hf_lip x ( t_n n ); rw [ abs_le ] at this; cases abs_cases ( x -
                                                                                              t_n
                                                                                              n )
        <;> nlinarith [ ht_n.2.1 n, mul_div_cancel₀ ε ( by positivity : ( 2 * C ) ≠ 0 ) ];
    intro n; specialize h_antideriv_integral n; specialize h_integral_bound n; norm_num at *;
      ring_nf at *; nlinarith [ inv_mul_cancel_left₀ hC_pos.ne' ε ];
  -- Since $F$ is non-decreasing, we have $F(t_n + \frac{\epsilon}{2C}) \leq F(t_{n+1})$.
  have h_non_decreasing : ∀ n, F (t_n n + ε / (2 * C)) ≤ F (t_n (n + 1)) := by
    intros n
    have h_non_decreasing : ∀ a b, a ≤ b → F a ≤ F b := by
      intros a b hab; exact (by
      by_cases h_eq : a = b;
      · rw [ h_eq ];
      · have := exists_deriv_eq_slope F ( lt_of_le_of_ne hab h_eq );
        exact this ( continuousOn_of_forall_continuousAt fun x hx =>
            HasDerivAt.continuousAt ( hF_deriv x ) )
          ( fun x hx => DifferentiableAt.differentiableWithinAt
            ( hF_deriv x |> HasDerivAt.differentiableAt ) ) |> fun ⟨ c, hc₁, hc₂ ⟩ => by
          have := hF_deriv c; have := this.deriv
          rw [ eq_div_iff ] at hc₂ <;> nlinarith [ hf_nn c, hc₁.1, hc₁.2 ];);
    exact h_non_decreasing _ _ ( le_of_lt ( ht_n.2.2 n ) );
  -- By induction, we can show that $F(t_n) \geq F(t_0) + n \cdot \frac{\epsilon^2}{4C}$.
  have h_induction : ∀ n, F (t_n n) ≥ F (t_n 0) + n * (ε^2 / (4 * C)) := by
    exact fun n => Nat.recOn n ( by norm_num ) fun n ihn => by push_cast; linarith [ h_antideriv n,
                                                                                    h_non_decreasing
                                                                                    n ];
  -- Since $F$ is bounded above, this leads to a contradiction.
  have h_contradiction : Filter.Tendsto (fun n => F (t_n n)) Filter.atTop Filter.atTop := by
    exact Filter.tendsto_atTop_mono h_induction ( tendsto_const_nhds.add_atTop <|
      tendsto_natCast_atTop_atTop.atTop_mul_const ( by positivity ) );
  exact absurd ( h_contradiction.eventually_gt_atTop hF_bdd.choose ) fun h => by
    obtain ⟨ n, hn ⟩ := h.exists
    linarith [ hF_bdd.choose_spec ( Set.mem_range_self ( t_n n ) ) ];

/-
For all-to-all coupling, the extremal velocity difference is strictly negative
    when the phase diameter is in (0, π). This is stronger than
    `semicircle_extremal_contraction` which gives ≤ 0 and requires W i k = W j k.
-/
private lemma allToAll_strict_extremal_contraction
    (K : ℝ) (hK : 0 < K) (N : ℕ) (_hN : 2 ≤ N)
    (W : Fin N → Fin N → ℝ) (hWdiag : ∀ i, W i i = 0)
    (hWoff : ∀ i j, i ≠ j → W i j = 1)
    (θ : Fin N → ℝ) (a b : Fin N) (hab : a ≠ b)
    (hmax : ∀ k, θ k ≤ θ a)
    (hmin : ∀ k, θ b ≤ θ k)
    (hgap_pos : 0 < θ a - θ b) (hgap_pi : θ a - θ b < Real.pi) :
    weightedKuramotoF K N W a θ - weightedKuramotoF K N W b θ < 0 := by
  unfold weightedKuramotoF;
  -- Split the sums into parts involving $a$ and $b$.
  have h_split : ∑ j, W a j * Real.sin (θ j - θ a) = ∑ j ∈ Finset.univ \ {a, b}, Real.sin
      (θ j - θ a) + Real.sin (θ b - θ a) ∧ ∑ j, W b j * Real.sin (θ j - θ b) = ∑ j ∈ Finset.univ \
      {a, b}, Real.sin (θ j - θ b) + Real.sin (θ a - θ b) := by
    simp +decide only [subset_univ, sum_sdiff_eq_sub, mem_singleton, not_false_eq_true,
      sum_insert, sub_self, sin_zero, sum_singleton, zero_add, sub_add_cancel, add_zero, hab];
    exact ⟨ Finset.sum_congr rfl fun j hj => by by_cases h : a = j <;> aesop,
           Finset.sum_congr rfl fun j hj => by by_cases h : b = j <;> aesop ⟩;
  -- Since $\sin(\theta_k - \theta_a) - \sin(\theta_k - \theta_b) \leq 0$ for all $k \neq a, b$, we
  -- have:
  have h_sin_diff_nonpos : ∑ j ∈ Finset.univ \ {a, b},
      (Real.sin (θ j - θ a) - Real.sin (θ j - θ b)) ≤ 0 := by
    refine Finset.sum_nonpos ?_;
    intro i hi; rw [ Real.sin_sub_sin ]; ring_nf; norm_num;
    exact mul_nonpos_of_nonpos_of_nonneg ( mul_nonpos_of_nonpos_of_nonneg
        ( Real.sin_nonpos_of_nonpos_of_neg_pi_le ( by linarith [ hmax i, hmin i ] )
          ( by linarith [ hmax i, hmin i ] ) )
        ( Real.cos_nonneg_of_mem_Icc
          ⟨ by linarith [ hmax i, hmin i ], by linarith [ hmax i, hmin i ] ⟩ ) ) zero_le_two;
  simp_all +decide [ Finset.sum_sub_distrib ];
  linarith [ show Real.sin ( θ a - θ b ) > 0 from
      Real.sin_pos_of_pos_of_lt_pi ( by linarith ) ( by linarith ),
    show Real.sin ( θ b - θ a ) ≤ 0 from
      Real.sin_nonpos_of_nonpos_of_neg_pi_le ( by linarith ) ( by linarith ) ]

/-
If every function in a finite family is differentiable and initially ≤ C,
    and whenever any function reaches C and is the maximum of all, its derivative
    is strictly negative, then all functions stay ≤ C forever.
-/
private lemma finite_max_stays_below {n : ℕ} (hn : 0 < n)
    (g : Fin n → ℝ → ℝ) (C : ℝ)
    (hg_diff : ∀ i, Differentiable ℝ (g i))
    (hg_init : ∀ i, g i 0 ≤ C)
    (hg_strict : ∀ t i, 0 ≤ t → (∀ j, g j t ≤ C) → g i t = C → (∀ j, g j t ≤ g i t) → deriv (g i) t
     < 0) :
    ∀ t, 0 ≤ t → ∀ i, g i t ≤ C := by
  intros t ht
  by_contra h_contra;
  -- Let $s = \inf \{ t \geq 0 \mid \exists i, g i t > C \}$
  set s := sInf {t | 0 ≤ t ∧ ∃ i, g i t > C} with hs_def
  have hs_pos : 0 < s := by
    have hs_pos : ∃ ε > 0, ∀ t, 0 ≤ t → t < ε → ∀ i, g i t ≤ C := by
      by_cases h_exists : ∃ i, g i 0 = C ∧ deriv (g i) 0 < 0;
      · obtain ⟨ i, hi₁, hi₂ ⟩ := h_exists
        have h_deriv_neg : ∃ ε > 0, ∀ t, 0 < t → t < ε → g i t < C := by
          have := hg_diff i;
          have := this 0;
          have := this.hasDerivAt.tendsto_slope_zero;
          have := Metric.tendsto_nhdsWithin_nhds.mp this ( -deriv ( g i ) 0 ) ( by linarith );
            norm_num at this;
          obtain ⟨ δ, hδ₁, hδ₂ ⟩ := this
          exact ⟨ δ, hδ₁, fun t ht₁ ht₂ => by
            have := hδ₂ ( ne_of_gt ht₁ ) ( abs_lt.mpr ⟨ by linarith, by linarith ⟩ )
            nlinarith [ abs_lt.mp this, mul_inv_cancel₀ ( ne_of_gt ht₁ ) ] ⟩;
        obtain ⟨ ε, hε_pos, hε ⟩ := h_deriv_neg
        have h_deriv_neg_all : ∃ ε > 0, ∀ t, 0 < t → t < ε → ∀ j, g j t ≤ C := by
          have h_deriv_neg_all : ∀ j, ∃ ε_j > 0, ∀ t, 0 < t → t < ε_j → g j t ≤ C := by
            intro j
            by_cases hj : g j 0 = C ∧ deriv (g j) 0 < 0;
            · have := hg_diff j;
              have := this 0;
              have := this.hasDerivAt.tendsto_slope_zero;
              have := Metric.tendsto_nhdsWithin_nhds.mp this ( -deriv ( g j ) 0 ) ( by linarith );
              obtain ⟨ δ, hδ_pos, H ⟩ := this
              exact ⟨ δ, hδ_pos, fun t ht₁ ht₂ => by
                have := H ( show t ≠ 0 by linarith ) ( by simpa [ abs_of_pos ht₁ ] using ht₂ )
                norm_num at this
                nlinarith [ abs_lt.mp this, mul_inv_cancel₀ ( ne_of_gt ht₁ ) ] ⟩;
            · by_cases hj : g j 0 < C;
              · have := Metric.continuous_iff.mp ( show Continuous ( g j ) from hg_diff j |>
                                                  Differentiable.continuous ) 0;
                exact Exists.elim ( this ( C - g j 0 ) ( sub_pos.mpr hj ) ) fun δ hδ =>
                  ⟨ δ, hδ.1, fun t ht₁ ht₂ => by
                    linarith [ abs_lt.mp ( hδ.2 t ( by simpa [ abs_of_pos ht₁ ] using ht₂ ) ) ] ⟩;
              · grind;
          choose ε_j hε_j_pos hε_j using h_deriv_neg_all;
          exact ⟨ Finset.min' ( Finset.univ.image ε_j )
              ⟨ _, Finset.mem_image_of_mem ε_j ( Finset.mem_univ i ) ⟩, by
            have := Finset.min'_mem ( Finset.univ.image ε_j )
              ⟨ _, Finset.mem_image_of_mem ε_j ( Finset.mem_univ i ) ⟩
            aesop, fun t ht₁ ht₂ j => hε_j j t ht₁ <| lt_of_lt_of_le ht₂ <|
            Finset.min'_le _ _ <| Finset.mem_image_of_mem ε_j <| Finset.mem_univ j ⟩
        obtain ⟨ ε', hε'_pos, hε' ⟩ := h_deriv_neg_all
        use min ε ε';
        exact ⟨ lt_min hε_pos hε'_pos, fun t ht₁ ht₂ j =>
          if hj : t = 0 then by simpa [ hj ] using hg_init j
          else hε' t ( lt_of_le_of_ne ht₁ ( Ne.symm hj ) )
            ( lt_of_lt_of_le ht₂ ( min_le_right _ _ ) ) j ⟩;
      · have h_exists : ∀ i, g i 0 < C := by
          exact fun i => lt_of_le_of_ne ( hg_init i ) fun hi => h_exists
            ⟨ i, hi, hg_strict 0 i ( by norm_num ) ( fun j => hg_init j ) hi
              ( fun j => by linarith [ hg_init j ] ) ⟩;
        have h_exists : ∀ i, ∃ ε > 0, ∀ t, 0 ≤ t → t < ε → g i t < C := by
          exact fun i => by
            rcases Metric.mem_nhds_iff.mp ( hg_diff i |> Differentiable.continuous
              |> Continuous.continuousAt |> fun h => h.eventually ( gt_mem_nhds <| h_exists i ) )
              with ⟨ ε, ε_pos, hε ⟩
            exact ⟨ ε, ε_pos, fun t ht₁ ht₂ => hε <| mem_ball_zero_iff.mpr <|
              abs_lt.mpr ⟨ by linarith, by linarith ⟩ ⟩;
        choose ε hε_pos hε using h_exists;
        exact ⟨ Finset.min' ( Finset.univ.image ε )
            ⟨ _, Finset.mem_image_of_mem ε ( Finset.mem_univ ⟨ 0, hn ⟩ ) ⟩, by
          have := Finset.min'_mem ( Finset.univ.image ε )
            ⟨ _, Finset.mem_image_of_mem ε ( Finset.mem_univ ⟨ 0, hn ⟩ ) ⟩
          aesop, fun t ht₁ ht₂ i => le_of_lt ( hε i t ht₁ ( lt_of_lt_of_le ht₂
            ( Finset.min'_le _ _ ( Finset.mem_image_of_mem ε ( Finset.mem_univ i ) ) ) ) ) ⟩;
    obtain ⟨ ε, ε_pos, hε ⟩ := hs_pos
    exact lt_of_lt_of_le ε_pos <| le_csInf ⟨ t, ht, by push Not at h_contra; tauto ⟩
      fun t ht => le_of_not_gt fun h => by
        have := hε t ht.1 h; obtain ⟨ i, hi ⟩ := ht.2; linarith [ this i ];
  -- Since $g_i(s) \leq C$ for all $i$, and $g_i$ is differentiable, we have $g_i(s) = C$ for some
  -- $i$.
  obtain ⟨i, hi⟩ : ∃ i, g i s = C ∧ ∀ j, g j s ≤ C := by
    have hs_le_C : ∀ i, g i s ≤ C := by
      intro i
      by_cases h_exists : ∃ t ∈ Set.Ico 0 s, g i t > C;
      · obtain ⟨ t, ht₁, ht₂ ⟩ := h_exists;
        exact absurd ( csInf_le ( show BddBelow { t : ℝ | 0 ≤ t ∧ ∃ i, g i t > C } from
          ⟨ 0, fun t ht => ht.1 ⟩ ) ⟨ ht₁.1, i, ht₂ ⟩ ) ( by linarith [ ht₁.2 ] );
      · have hs_le_C : Filter.Tendsto (fun t => g i t) (nhdsWithin s (Set.Iio s)) (nhds (g i
                                                                                         s)) := by
          exact hg_diff i |> Differentiable.continuous |> Continuous.continuousWithinAt;
        exact le_of_tendsto hs_le_C ( Filter.eventually_of_mem ( Ioo_mem_nhdsLT hs_pos )
          fun t ht => le_of_not_gt fun h => h_exists ⟨ t, ⟨ ht.1.le, ht.2 ⟩, h ⟩ );
    have hs_eq_C : ∃ i, g i s = C := by
      have hs_eq_C : ∃ i, g i s ≥ C := by
        have hs_eq_C : ∃ seq : ℕ → ℝ, (∀ n, 0 ≤ seq n ∧ ∃ i, g i (seq n) >
                                       C) ∧ Filter.Tendsto seq Filter.atTop (nhds s) := by
          have hs_eq_C : ∀ ε > 0, ∃ t, 0 ≤ t ∧ ∃ i, g i t > C ∧ |t - s| < ε := by
            exact fun ε ε_pos => by
              rcases exists_lt_of_csInf_lt ( show { t : ℝ | 0 ≤ t ∧ ∃ i, g i t > C }.Nonempty from
                ⟨ t, ht, by push Not at h_contra; tauto ⟩ ) ( lt_add_of_pos_right s ε_pos )
                with ⟨ t, ht₁, ht₂ ⟩
              exact ⟨ t, ht₁.1, ht₁.2.choose, ht₁.2.choose_spec, abs_lt.mpr
                ⟨ by linarith [ ht₂, csInf_le ⟨ 0, fun t ht => ht.1 ⟩ ht₁ ],
                  by linarith [ ht₂, csInf_le ⟨ 0, fun t ht => ht.1 ⟩ ht₁ ] ⟩ ⟩;
          exact ⟨ fun n => Classical.choose ( hs_eq_C ( 1 / ( n + 1 ) ) ( by positivity ) ),
            fun n => ⟨ Classical.choose_spec ( hs_eq_C ( 1 / ( n + 1 ) ) ( by positivity ) ) |>.1,
              Classical.choose_spec ( hs_eq_C ( 1 / ( n + 1 ) ) ( by positivity ) ) |>.2.choose,
              Classical.choose_spec ( hs_eq_C ( 1 / ( n + 1 ) ) ( by positivity ) )
                |>.2.choose_spec.1 ⟩,
            tendsto_iff_norm_sub_tendsto_zero.mpr <| squeeze_zero ( fun _ => by positivity )
              ( fun n => Classical.choose_spec ( hs_eq_C ( 1 / ( n + 1 ) ) ( by positivity ) )
                |>.2.choose_spec.2.le ) <| tendsto_one_div_add_atTop_nhds_zero_nat ⟩;
        obtain ⟨ seq, hseq₁, hseq₂ ⟩ := hs_eq_C;
        choose f hf using fun n => hseq₁ n |>.2;
        -- Since $f$ is a function from $\mathbb{N}$ to $\text{Fin } n$, and $\text{Fin } n$ is
        -- finite, there must exist some $i$ such that $f(n) = i$ for infinitely many $n$.
        obtain ⟨i, hi⟩ : ∃ i : Fin n, Set.Infinite {n | f n = i} := by
          by_cases h_finite : ∀ i : Fin n, Set.Finite {n | f n = i};
          · exact absurd ( Set.Finite.subset ( Set.Finite.biUnion
              ( Set.toFinite ( Finset.univ : Finset ( Fin n ) ) ) fun i _ => h_finite i )
              fun x hx => by aesop ) ( Set.infinite_univ );
          · exact by push Not at h_finite; exact h_finite;
        have hs_eq_C : Filter.Tendsto (fun n => g i (seq (Nat.nth (fun n => f n = i)
                                                          n))) Filter.atTop (nhds (g i s)) := by
          exact hg_diff i |> Differentiable.continuous |> Continuous.continuousAt |>
            fun h => h.tendsto.comp <| hseq₂.comp <| Filter.tendsto_atTop_atTop.mpr
              fun x => ⟨ x, fun n hn => Nat.le_nth ( by aesop ) |> le_trans hn ⟩;
        exact ⟨ i, le_of_tendsto_of_tendsto' tendsto_const_nhds hs_eq_C fun n => le_of_lt <| by
          simpa [ Nat.nth_mem_of_infinite hi ] using hf ( Nat.nth ( fun n => f n = i ) n ) ⟩;
      exact ⟨ hs_eq_C.choose, le_antisymm ( hs_le_C _ ) hs_eq_C.choose_spec ⟩;
    exact ⟨ hs_eq_C.choose, hs_eq_C.choose_spec, hs_le_C ⟩;
  have h_deriv_neg : deriv (g i) s < 0 := by
    exact hg_strict s i hs_pos.le hi.2 hi.1 fun j => by linarith [ hi.2 j ];
  have h_deriv_neg : Filter.Tendsto (fun t => (g i t - g i s) / (t - s)) (nhdsWithin s (Set.Iio s))
      (nhds (deriv (g i) s)) := by
    have h_deriv_neg : HasDerivAt (g i) (deriv (g i) s) s := by
      exact DifferentiableAt.hasDerivAt ( hg_diff i |> Differentiable.differentiableAt );
    rw [ hasDerivAt_iff_tendsto_slope ] at h_deriv_neg;
    simpa [ slope_fun_def_field,
           div_eq_inv_mul ] using h_deriv_neg.mono_left ( nhdsWithin_mono _ <| by simp +decide );
  have := h_deriv_neg.eventually ( gt_mem_nhds ‹_› );
  replace := this.and ( Ioo_mem_nhdsLT hs_pos )
  obtain ⟨ x, hx₁, hx₂ ⟩ := this.exists
  rw [ div_lt_iff_of_neg ] at hx₁ <;> nlinarith [ hi.2 i, show g i x ≤ C from
    le_of_not_gt fun hx₃ => by
      linarith [ show s ≤ x from csInf_le ⟨ 0, fun t ht => ht.1 ⟩ ⟨ by linarith, i, hx₃ ⟩ ] ];

/-
Corollary of `finite_max_stays_below` for a general Fintype index.
-/
private lemma finite_max_stays_below' {ι : Type*} [Finite ι] [Nonempty ι]
    (g : ι → ℝ → ℝ) (C : ℝ)
    (hg_diff : ∀ i, Differentiable ℝ (g i))
    (hg_init : ∀ i, g i 0 ≤ C)
    (hg_strict : ∀ t i, 0 ≤ t → (∀ j, g j t ≤ C) → g i t = C → (∀ j, g j t ≤ g i t) → deriv (g i) t
     < 0) :
    ∀ t, 0 ≤ t → ∀ i, g i t ≤ C := by
  letI := Fintype.ofFinite ι;
  intro t ht i;
  convert finite_max_stays_below ( Fintype.card_pos )
    ( fun j => g ( Fintype.equivFin ι |>.symm j ) ) C ( fun j => hg_diff _ ) ( fun j => hg_init _ )
    ( fun t j ht₁ ht₂ ht₃ ht₄ => ?_ ) ( t ) ht ( Fintype.equivFin ι i ) using 1;
  · simp +decide;
  · exact hg_strict t _ ht₁ ( fun k => by simpa using ht₂ ( Fintype.equivFin ι k ) )
      ( by simpa using ht₃ ) ( fun k => by simpa using ht₄ ( Fintype.equivFin ι k ) )

/-- The phase diameter is non-increasing along the all-to-all Kuramoto ODE,
    so the semicircle condition is preserved for all forward time. -/
private theorem semicircle_preserved
    (K : ℝ) (hK : 0 < K) (N : ℕ) (hN : 2 ≤ N)
    (W : Fin N → Fin N → ℝ) (hWdiag : ∀ i, W i i = 0)
    (hWoff : ∀ i j, i ≠ j → W i j = 1)
    (θ : ℝ → Fin N → ℝ)
    (hsol : ∀ t, HasDerivAt θ (kuramotoVectorField K N W (θ t)) t)
    (hsemi0 : ∀ a b : Fin N, |θ 0 a - θ 0 b| < Real.pi)
    (t : ℝ) (ht : 0 ≤ t) (a b : Fin N) :
    |θ t a - θ t b| < Real.pi := by
  -- Define D₀ as the initial max signed difference over all pairs
  set D₀ := Finset.sup' (Finset.univ : Finset (Fin N × Fin N))
    ⟨(⟨0, by omega⟩, ⟨0, by omega⟩), Finset.mem_univ _⟩
    (fun p : Fin N × Fin N => θ 0 p.1 - θ 0 p.2) with hD₀_def
  have hD₀_lt_pi : D₀ < Real.pi := by
    rw [Finset.sup'_lt_iff]
    exact fun p _ => lt_of_le_of_lt (le_abs_self _) (hsemi0 p.1 p.2)
  have hD₀_init : ∀ p : Fin N × Fin N, θ 0 p.1 - θ 0 p.2 ≤ D₀ :=
    fun p => Finset.le_sup' (fun p : Fin N × Fin N => θ 0 p.1 - θ 0 p.2) (Finset.mem_univ p)
  -- Use C = (D₀ + π) / 2 which is always in (0, π)
  set C := (D₀ + Real.pi) / 2
  have hD₀_ge : 0 ≤ D₀ := le_trans (le_of_eq (sub_self (θ 0 ⟨0, by omega⟩)).symm)
    (hD₀_init (⟨0, by omega⟩, ⟨0, by omega⟩))
  have hC_pos : 0 < C := by simp only [C]; linarith [Real.pi_pos]
  have hC_lt_pi : C < Real.pi := by simp only [C]; linarith
  have hC_gt_D₀ : D₀ < C := by simp only [C]; linarith [Real.pi_pos]
  -- Show all signed differences stay ≤ C < π
  suffices h_all : ∀ s, 0 ≤ s → ∀ p : Fin N × Fin N, θ s p.1 - θ s p.2 ≤ C by
    exact abs_lt.mpr ⟨by linarith [h_all t ht (b, a)], by linarith [h_all t ht (a, b)]⟩
  haveI : Nonempty (Fin N × Fin N) := ⟨(⟨0, by omega⟩, ⟨0, by omega⟩)⟩
  exact finite_max_stays_below'
    (fun p : Fin N × Fin N => fun s => θ s p.1 - θ s p.2) C
    (fun p => Differentiable.sub
      (fun s => differentiableAt_pi.1 (hsol s).differentiableAt p.1)
      (fun s => differentiableAt_pi.1 (hsol s).differentiableAt p.2))
    (fun p => le_of_lt (lt_of_le_of_lt (hD₀_init p) hC_gt_D₀))
    (fun s p hs hle heq hmax => by
      have hab : p.1 ≠ p.2 := by
        intro h; simp [h] at heq; linarith
      have hmax_phase : ∀ k, θ s k ≤ θ s p.1 := fun k => by
        linarith [hle (k, p.2)]
      have hmin_phase : ∀ k, θ s p.2 ≤ θ s k := fun k => by
        linarith [hle (p.1, k)]
      rw [show deriv (fun s => θ s p.1 - θ s p.2) s =
        weightedKuramotoF K N W p.1 (θ s) - weightedKuramotoF K N W p.2 (θ s) from
        HasDerivAt.deriv (HasDerivAt.sub (hasDerivAt_pi.1 (hsol s) p.1)
          (hasDerivAt_pi.1 (hsol s) p.2))]
      exact allToAll_strict_extremal_contraction K hK N hN W hWdiag hWoff
        (θ s) p.1 p.2 hab hmax_phase hmin_phase (by linarith) (by linarith))

/-
∑ F_i² → 0 along the Kuramoto ODE, proved via Lyapunov-Barbalat:
    V has derivative −∑ F_i², V is bounded below, and ∑ F_i² is Lipschitz.
-/
private theorem sum_F_sq_tendsto_zero
    (K : ℝ) (hK : 0 < K) (N : ℕ) (hN : 2 ≤ N)
    (W : Fin N → Fin N → ℝ) (hWsym : ∀ i j, W i j = W j i)
    (hWdiag : ∀ i, W i i = 0) (hWoff : ∀ i j, i ≠ j → W i j = 1)
    (θ : ℝ → Fin N → ℝ)
    (hsol : ∀ t, HasDerivAt θ (kuramotoVectorField K N W (θ t)) t) :
    Filter.Tendsto (fun t => ∑ i : Fin N, (weightedKuramotoF K N W i (θ t)) ^ 2)
      Filter.atTop (nhds 0) := by
  -- First, note that the function $f(t) := \sum_i (F_i(t))^2$ is Lipschitz.
  have h_lipschitz : ∃ C > 0, ∀ s t, |∑ i, (weightedKuramotoF K N W i (θ s))^2 - ∑ i,
      (weightedKuramotoF K N W i (θ t))^2| ≤ C * |s - t| := by
    -- The derivative of $F_i(t)$ is bounded.
    have h_deriv_bound : ∃ C > 0, ∀ t, ∀ i, |deriv (fun t => weightedKuramotoF K N W i (θ t)) t| ≤
        C := by
      -- The derivative of $F_i(t)$ is given by the chain rule.
      have h_deriv : ∀ t i, deriv (fun t => weightedKuramotoF K N W i (θ t)) t = K * ∑ j, W i j *
          Real.cos ((θ t) j - (θ t) i) *
          (weightedKuramotoF K N W j (θ t) - weightedKuramotoF K N W i (θ t)) := by
        intro t i;
        have h_deriv : deriv (fun t => weightedKuramotoF K N W i (θ t)) t = K * ∑ j, W i j * deriv
            (fun t => Real.sin ((θ t) j - (θ t) i)) t := by
          simp +decide [ weightedKuramotoF ];
          have h_deriv : ∀ j, DifferentiableAt ℝ (fun t => Real.sin ((θ t) j - (θ t) i)) t := by
            intro j
            exact DifferentiableAt.sin ( DifferentiableAt.sub
              ( differentiableAt_pi.1 ( hsol t |> HasDerivAt.differentiableAt ) j )
              ( differentiableAt_pi.1 ( hsol t |> HasDerivAt.differentiableAt ) i ) );
          norm_num [ h_deriv ];
        rw [ h_deriv ];
        refine congrArg _ ( Finset.sum_congr rfl fun j _ => ?_ );
        have hsin_deriv :
            deriv (fun t => Real.sin ((θ t) j - (θ t) i)) t
              = Real.cos ((θ t) j - (θ t) i)
                * (weightedKuramotoF K N W j (θ t) - weightedKuramotoF K N W i (θ t)) :=
          ( HasDerivAt.sin ( HasDerivAt.sub ( hasDerivAt_pi.1 ( hsol t ) j )
            ( hasDerivAt_pi.1 ( hsol t ) i ) ) ).deriv;
        rw [ hsin_deriv ]; ring;
      -- Each term in the sum is bounded by $K \cdot 1 \cdot 2K \cdot N = 2K^2N$.
      have h_term_bound : ∀ t i j, |W i j * Real.cos ((θ t) j - (θ t) i) *
          (weightedKuramotoF K N W j (θ t) - weightedKuramotoF K N W i (θ t))| ≤ 2 * K * N := by
        intros t i j
        have h_term_bound : |weightedKuramotoF K N W j (θ t) - weightedKuramotoF K N W i (θ t)| ≤ 2
            * K * N := by
          have h_term_bound : ∀ i, |weightedKuramotoF K N W i (θ t)| ≤ K * N := by
            intros i
            have h_term_bound : |∑ j, W i j * Real.sin ((θ t) j - (θ t) i)| ≤ N := by
              have h_term_bound : ∀ j, |W i j * Real.sin ((θ t) j - (θ t) i)| ≤ 1 := by
                intros j
                by_cases hij : i = j
                · simp [hij, hWdiag]
                · simp only [hWoff i j hij, one_mul]
                  exact abs_le.mpr
                    ⟨by nlinarith [Real.neg_one_le_sin (θ t j - θ t i),
                          Real.sin_le_one (θ t j - θ t i)],
                      by nlinarith [Real.neg_one_le_sin (θ t j - θ t i),
                          Real.sin_le_one (θ t j - θ t i)]⟩;
              exact le_trans ( Finset.abs_sum_le_sum_abs _ _ )
                ( le_trans ( Finset.sum_le_sum fun _ _ => h_term_bound _ ) ( by norm_num ) );
            exact abs_le.mpr ⟨ by unfold weightedKuramotoF; nlinarith [ abs_le.mp h_term_bound ],
                              by unfold weightedKuramotoF; nlinarith [ abs_le.mp h_term_bound ] ⟩;
          exact abs_le.mpr
            ⟨ by linarith [ abs_le.mp ( h_term_bound i ), abs_le.mp ( h_term_bound j ) ],
              by linarith [ abs_le.mp ( h_term_bound i ), abs_le.mp ( h_term_bound j ) ] ⟩;
        rw [ abs_mul, abs_mul ];
        exact le_trans ( mul_le_of_le_one_left ( abs_nonneg _ ) ( mul_le_one₀
          ( abs_le.mpr ⟨ by cases eq_or_ne i j <;> aesop, by cases eq_or_ne i j <;> aesop ⟩ )
          ( abs_nonneg _ ) ( Real.abs_cos_le_one _ ) ) ) h_term_bound;
      refine ⟨ K * ( 2 * K * N * N ), ?_, ?_ ⟩ <;> norm_num [ h_deriv ];
      · positivity;
      · exact fun t i => by
          rw [ abs_of_pos hK ]
          exact mul_le_mul_of_nonneg_left ( le_trans ( Finset.abs_sum_le_sum_abs _ _ )
            ( le_trans ( Finset.sum_le_sum fun _ _ => h_term_bound _ _ _ )
              ( by norm_num; nlinarith ) ) ) hK.le;
    -- Using the bound on the derivative, we can show that $f(t)$ is Lipschitz.
    obtain ⟨C, hC_pos, hC_bound⟩ := h_deriv_bound;
    have h_lipschitz : ∀ s t, ∀ i, |weightedKuramotoF K N W i (θ s) - weightedKuramotoF K N W i
        (θ t)| ≤ C * |s - t| := by
      -- By the mean value theorem, for any $s, t \in \mathbb{R}$, there exists $c \in (s, t)$ such
      -- that
      have h_mvt : ∀ s t i, s < t → ∃ c ∈ Set.Ioo s t, deriv
          (fun t => weightedKuramotoF K N W i (θ t)) c =
          (weightedKuramotoF K N W i (θ t) - weightedKuramotoF K N W i (θ s)) / (t - s) := by
        intros s t i hst; apply_rules [ exists_deriv_eq_slope ];
        · refine Continuous.continuousOn ?_;
          have h_cont : Continuous θ := by
            exact continuous_iff_continuousAt.mpr fun t => HasDerivAt.continuousAt ( hsol t );
          exact Continuous.mul continuous_const <| continuous_finsetSum _ fun j _ => Continuous.mul
            ( continuous_const ) <| Real.continuous_sin.comp <| Continuous.sub
            ( continuous_apply j |> Continuous.comp <| h_cont )
            ( continuous_apply i |> Continuous.comp <| h_cont );
        · have h_diff : DifferentiableOn ℝ (fun t => θ t) (Set.Ioo s t) := by
            exact fun x hx => ( hsol x |> HasDerivAt.differentiableAt |>
                               DifferentiableAt.differentiableWithinAt );
          simp only [weightedKuramotoF];
          fun_prop (disch := norm_num);
      intro s t i; rcases lt_trichotomy s t with ( h | rfl | h ) <;> norm_num;
      · obtain ⟨ c, hc₁, hc₂ ⟩ := h_mvt s t i h
        rw [ abs_le ]
        constructor <;> cases abs_cases ( s - t ) <;> nlinarith [ abs_le.mp ( hC_bound c i ),
          mul_div_cancel₀ ( weightedKuramotoF K N W i ( θ t ) - weightedKuramotoF K N W i ( θ s ) )
            ( sub_ne_zero_of_ne h.ne' ) ];
      · obtain ⟨ c, hc₁, hc₂ ⟩ := h_mvt t s i h
        rw [ abs_le ]
        constructor <;> cases abs_cases ( s - t ) <;> nlinarith [ abs_le.mp ( hC_bound c i ),
          mul_div_cancel₀ ( weightedKuramotoF K N W i ( θ s ) - weightedKuramotoF K N W i ( θ t ) )
            ( sub_ne_zero_of_ne h.ne' ) ];
    -- Using the bound on the derivative, we can show that $f(t)$ is Lipschitz with constant $2KN
    -- \cdot C$.
    use 2 * K * N * C * N;
    refine ⟨ by positivity, fun s t => ?_ ⟩;
    -- Using the bound on the derivative, we can show that $|F_i(t)| \leq KN$.
    have h_bound : ∀ t i, |weightedKuramotoF K N W i (θ t)| ≤ K * N := by
      intros t i
      simp only [weightedKuramotoF, abs_mul];
      rw [ abs_of_pos hK ];
      gcongr;
      refine le_trans ( Finset.abs_sum_le_sum_abs _ _ ) ?_;
      exact le_trans ( Finset.sum_le_sum fun _ _ => show |_| ≤ 1 by
          rw [ abs_mul ]
          exact mul_le_one₀
            ( abs_le.mpr ⟨ by cases eq_or_ne i ‹_› <;> aesop, by cases eq_or_ne i ‹_› <;> aesop ⟩ )
            ( abs_nonneg _ ) ( Real.abs_sin_le_one _ ) ) ( by norm_num );
    rw [ ← Finset.sum_sub_distrib ];
    refine le_trans ( Finset.abs_sum_le_sum_abs _ _ ) ?_;
    refine le_trans ( Finset.sum_le_sum (g := fun i => 2 * K * N * C * |s - t|)
      fun i _ => ?_ ) ?_;
    · rw [ abs_le ];
      constructor <;> nlinarith [ abs_le.mp ( h_lipschitz s t i ), abs_le.mp ( h_bound s i ),
                                 abs_le.mp ( h_bound t i ), mul_nonneg hK.le ( Nat.cast_nonneg N ),
                                 mul_nonneg hK.le hC_pos.le,
                                 mul_nonneg ( Nat.cast_nonneg N ) hC_pos.le ];
    · norm_num [ mul_assoc, mul_comm, mul_left_comm ];
  obtain ⟨C, hC_pos, hC⟩ := h_lipschitz
  have h_f_nonneg : ∀ t, 0 ≤ ∑ i, (weightedKuramotoF K N W i (θ t))^2 := by
    exact fun t => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h_F_deriv : ∀ t, HasDerivAt (fun s => -(weightedKuramotoV K N W (θ s)))
      (∑ i, (weightedKuramotoF K N W i (θ t))^2) t := by
    intro t;
    refine ( HasDerivAt.neg
      ( lyapunov_nonincreasing_along_trajectory K hK N W hWsym θ hsol t ) ).congr_deriv ?_;
    rw [ lyapunov_derivative_eq K N W hWsym ( θ t ) ]; ring;
  have h_F_bdd : BddAbove (Set.range (fun t => -(weightedKuramotoV K N W (θ t)))) := by
    use (K / 2) * (N : ℝ) ^ 2;
    rintro x ⟨ t, rfl ⟩
    exact le_trans ( neg_le_neg <| weightedKuramotoV_bounded_below K hK N W ( fun i j => by
      by_cases hij : i = j <;> simp +decide [ * ] ) ( fun i j => by
      by_cases hij : i = j <;> simp +decide [ * ] ) ( θ t ) ) ( by nlinarith );
  exact barbalat_of_nonneg_lipschitz h_f_nonneg (fun s t => hC s t) hC_pos h_F_deriv h_F_bdd

/-- Analysis core: if `sin (D t) → 0` and `D t` is eventually confined to
    `[0, C]` with `C < π`, then `D t → 0`. The upper `sin` branch near `π` is
    cut off by `C < π`, so a small `sin (D t)` forces `D t` small (proved via
    the positive compact minimum of `sin` on `[ε, C]`). -/
private theorem diam_tendsto_zero_of_sin_tendsto_zero
    {D : ℝ → ℝ} {C : ℝ} (hC : C < Real.pi)
    (hD0 : ∀ᶠ t in Filter.atTop, 0 ≤ D t)
    (hDC : ∀ᶠ t in Filter.atTop, D t ≤ C)
    (hsin : Filter.Tendsto (fun t => Real.sin (D t)) Filter.atTop (nhds 0)) :
    Filter.Tendsto D Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨M0, hM0⟩ := Filter.eventually_atTop.1 (hD0.and hDC)
  by_cases hεC : ε ≤ C
  · have hne : (Set.Icc ε C).Nonempty := ⟨ε, ⟨le_refl _, hεC⟩⟩
    obtain ⟨x₀, hx₀mem, hx₀min⟩ :=
      isCompact_Icc.exists_isMinOn hne Real.continuous_sin.continuousOn
    have hmpos : 0 < Real.sin x₀ :=
      Real.sin_pos_of_pos_of_lt_pi (lt_of_lt_of_le hε hx₀mem.1)
        (lt_of_le_of_lt hx₀mem.2 hC)
    obtain ⟨M, hM⟩ := (Metric.tendsto_atTop.1 hsin) (Real.sin x₀) hmpos
    refine ⟨max M M0, fun t ht => ?_⟩
    have htM : M ≤ t := le_trans (le_max_left _ _) ht
    have htM0 : M0 ≤ t := le_trans (le_max_right _ _) ht
    obtain ⟨hd0, hdc⟩ := hM0 t htM0
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hd0]
    by_contra hcon; rw [not_lt] at hcon
    have hmem : D t ∈ Set.Icc ε C := ⟨hcon, hdc⟩
    have h1 : Real.sin x₀ ≤ Real.sin (D t) := isMinOn_iff.1 hx₀min (D t) hmem
    have h2 := hM t htM; rw [Real.dist_eq, sub_zero] at h2
    have h3 : Real.sin (D t) ≤ |Real.sin (D t)| := le_abs_self _
    linarith
  · refine ⟨M0, fun t ht => ?_⟩
    obtain ⟨hd0, hdc⟩ := hM0 t ht
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hd0]
    exact lt_of_le_of_lt hdc (not_le.1 hεC)

/-- If `∑ (g t i)² → 0` then `∑ |g t i| → 0` (each coordinate is squeezed to
    zero by the sum of squares, then the finite sum of absolute values). -/
private theorem sum_abs_tendsto_zero_of_sum_sq {n : ℕ} {g : ℝ → Fin n → ℝ}
    (h : Filter.Tendsto (fun t => ∑ i, (g t i) ^ 2) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun t => ∑ i, |g t i|) Filter.atTop (nhds 0) := by
  have hcoord : ∀ i : Fin n, Filter.Tendsto (fun t => |g t i|) Filter.atTop (nhds 0) := by
    intro i
    have hsq : Filter.Tendsto (fun t => (g t i) ^ 2) Filter.atTop (nhds 0) :=
      squeeze_zero (fun t => sq_nonneg _)
        (fun t => Finset.single_le_sum (fun j _ => sq_nonneg (g t j)) (Finset.mem_univ i)) h
    have hsqrt : Filter.Tendsto (fun t => Real.sqrt ((g t i) ^ 2)) Filter.atTop
        (nhds (Real.sqrt 0)) := (Real.continuous_sqrt.tendsto 0).comp hsq
    simpa [Real.sqrt_sq_eq_abs, Real.sqrt_zero] using hsqrt
  have := tendsto_finsetSum (Finset.univ : Finset (Fin n)) (fun i _ => hcoord i)
  simpa using this

/-- For the min-phase index `m` and max-phase index `M` of a configuration,
    `K · sin (φ_M − φ_m) ≤ F_m`: every off-diagonal sine term is non-negative
    (phases lie in `[φ_m, φ_M] ⊂ [0,π)`), and the `M`-term contributes exactly
    `sin (φ_M − φ_m)`. -/
private theorem weightedF_min_ge_Ksin {n : ℕ} (K : ℝ) (hK : 0 < K)
    (W : Fin n → Fin n → ℝ) (hWdiag : ∀ i, W i i = 0) (hWoff : ∀ i j, i ≠ j → W i j = 1)
    (φ : Fin n → ℝ) (m M : Fin n)
    (hmin : ∀ k, φ m ≤ φ k) (hmax : ∀ k, φ k ≤ φ M)
    (hC : φ M - φ m < Real.pi) :
    K * Real.sin (φ M - φ m) ≤ weightedKuramotoF K n W m φ := by
  unfold weightedKuramotoF
  have hterm_nonneg : ∀ j, 0 ≤ W m j * Real.sin (φ j - φ m) := by
    intro j
    by_cases hjm : j = m
    · subst hjm; simp [hWdiag]
    · rw [hWoff m j (Ne.symm hjm), one_mul]
      exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hmin j]) (by linarith [hmax j])
  have hWmM : W m M * Real.sin (φ M - φ m) = Real.sin (φ M - φ m) := by
    by_cases hMm : M = m
    · subst hMm; simp [hWdiag]
    · rw [hWoff m M (Ne.symm hMm)]; ring
  have hle : W m M * Real.sin (φ M - φ m) ≤ ∑ j, W m j * Real.sin (φ j - φ m) :=
    Finset.single_le_sum (fun j _ => hterm_nonneg j) (Finset.mem_univ M)
  rw [hWmM] at hle
  exact mul_le_mul_of_nonneg_left hle (le_of_lt hK)

/-- Uniform semicircle confinement: there is a single `C < π` bounding every
    pairwise phase difference for all forward time. Exposes the uniform bound
    `C = (D₀+π)/2` that `semicircle_preserved` constructs internally. -/
private theorem semicircle_preserved_uniform
    (K : ℝ) (hK : 0 < K) (N : ℕ) (hN : 2 ≤ N)
    (W : Fin N → Fin N → ℝ) (hWdiag : ∀ i, W i i = 0)
    (hWoff : ∀ i j, i ≠ j → W i j = 1)
    (θ : ℝ → Fin N → ℝ)
    (hsol : ∀ t, HasDerivAt θ (kuramotoVectorField K N W (θ t)) t)
    (hsemi0 : ∀ a b : Fin N, |θ 0 a - θ 0 b| < Real.pi) :
    ∃ C : ℝ, C < Real.pi ∧ ∀ s, 0 ≤ s → ∀ a b : Fin N, |θ s a - θ s b| ≤ C := by
  set D₀ := Finset.sup' (Finset.univ : Finset (Fin N × Fin N))
    ⟨(⟨0, by omega⟩, ⟨0, by omega⟩), Finset.mem_univ _⟩
    (fun p : Fin N × Fin N => θ 0 p.1 - θ 0 p.2) with hD₀_def
  have hD₀_lt_pi : D₀ < Real.pi := by
    rw [Finset.sup'_lt_iff]
    exact fun p _ => lt_of_le_of_lt (le_abs_self _) (hsemi0 p.1 p.2)
  have hD₀_init : ∀ p : Fin N × Fin N, θ 0 p.1 - θ 0 p.2 ≤ D₀ :=
    fun p => Finset.le_sup' (fun p : Fin N × Fin N => θ 0 p.1 - θ 0 p.2) (Finset.mem_univ p)
  set C := (D₀ + Real.pi) / 2 with hC_def
  have hD₀_ge : 0 ≤ D₀ := le_trans (le_of_eq (sub_self (θ 0 ⟨0, by omega⟩)).symm)
    (hD₀_init (⟨0, by omega⟩, ⟨0, by omega⟩))
  have hC_lt_pi : C < Real.pi := by simp only [C]; linarith
  have hC_gt_D₀ : D₀ < C := by simp only [C]; linarith [Real.pi_pos]
  have h_all : ∀ s, 0 ≤ s → ∀ p : Fin N × Fin N, θ s p.1 - θ s p.2 ≤ C := by
    haveI : Nonempty (Fin N × Fin N) := ⟨(⟨0, by omega⟩, ⟨0, by omega⟩)⟩
    exact finite_max_stays_below'
      (fun p : Fin N × Fin N => fun s => θ s p.1 - θ s p.2) C
      (fun p => Differentiable.sub
        (fun s => differentiableAt_pi.1 (hsol s).differentiableAt p.1)
        (fun s => differentiableAt_pi.1 (hsol s).differentiableAt p.2))
      (fun p => le_of_lt (lt_of_le_of_lt (hD₀_init p) hC_gt_D₀))
      (fun s p hs hle heq hmax => by
        have hab : p.1 ≠ p.2 := by
          intro h; simp [h] at heq; linarith
        have hmax_phase : ∀ k, θ s k ≤ θ s p.1 := fun k => by
          linarith [hle (k, p.2)]
        have hmin_phase : ∀ k, θ s p.2 ≤ θ s k := fun k => by
          linarith [hle (p.1, k)]
        rw [show deriv (fun s => θ s p.1 - θ s p.2) s =
          weightedKuramotoF K N W p.1 (θ s) - weightedKuramotoF K N W p.2 (θ s) from
          HasDerivAt.deriv (HasDerivAt.sub (hasDerivAt_pi.1 (hsol s) p.1)
            (hasDerivAt_pi.1 (hsol s) p.2))]
        exact allToAll_strict_extremal_contraction K hK N hN W hWdiag hWoff
          (θ s) p.1 p.2 hab hmax_phase hmin_phase (by linarith) (by linarith))
  exact ⟨C, hC_lt_pi, fun s hs a b =>
    abs_le.mpr ⟨by linarith [h_all s hs (b, a)], h_all s hs (a, b)⟩⟩

/-- Under uniform semicircle confinement (`|θ a − θ b| ≤ C < π` for all
    forward time) and ∑ F_i² → 0, all phase differences tend to 0. The phase
    diameter `D t` is squeezed: `K·sin(D t) ≤ F_{argmin} ≤ ∑|F_i| → 0`, so
    `sin(D t) → 0`, hence `D t → 0` (analysis core), hence every pairwise
    difference → 0. -/
private theorem phase_diffs_tend_to_zero
    (K : ℝ) (hK : 0 < K) (N : ℕ) (hN : 2 ≤ N)
    (W : Fin N → Fin N → ℝ) (hWdiag : ∀ i, W i i = 0)
    (hWoff : ∀ i j, i ≠ j → W i j = 1)
    (θ : ℝ → Fin N → ℝ)
    (C : ℝ) (hCpi : C < Real.pi)
    (hdiam : ∀ s, 0 ≤ s → ∀ a b : Fin N, |θ s a - θ s b| ≤ C)
    (hF_zero : Filter.Tendsto (fun t => ∑ i : Fin N, (weightedKuramotoF K N W i (θ t)) ^ 2)
      Filter.atTop (nhds 0)) :
    ∀ a b : Fin N, Filter.Tendsto (fun t => θ t a - θ t b) Filter.atTop (nhds 0) := by
  have hpairne : (Finset.univ : Finset (Fin N × Fin N)).Nonempty :=
    ⟨(⟨0, by omega⟩, ⟨0, by omega⟩), Finset.mem_univ _⟩
  set D : ℝ → ℝ := fun t => (Finset.univ : Finset (Fin N × Fin N)).sup' hpairne
      (fun p => θ t p.1 - θ t p.2) with hD_def
  have hD_nonneg : ∀ t, 0 ≤ D t := by
    intro t
    have h0 : θ t (⟨0, by omega⟩ : Fin N) - θ t (⟨0, by omega⟩ : Fin N) ≤ D t :=
      Finset.le_sup' (fun p : Fin N × Fin N => θ t p.1 - θ t p.2)
        (Finset.mem_univ ((⟨0, by omega⟩ : Fin N), (⟨0, by omega⟩ : Fin N)))
    simpa using h0
  have hD_le : ∀ t, 0 ≤ t → D t ≤ C := by
    intro t ht
    refine Finset.sup'_le hpairne _ (fun p _ => ?_)
    exact le_trans (le_abs_self _) (hdiam t ht p.1 p.2)
  have hsumabs : Filter.Tendsto (fun t => ∑ i, |weightedKuramotoF K N W i (θ t)|)
      Filter.atTop (nhds 0) := sum_abs_tendsto_zero_of_sum_sq hF_zero
  have hKsin : Filter.Tendsto (fun t => K * Real.sin (D t)) Filter.atTop (nhds 0) := by
    refine squeeze_zero' ?_ ?_ hsumabs
    · filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
      have hs0 : 0 ≤ Real.sin (D t) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (hD_nonneg t)
          (le_of_lt (lt_of_le_of_lt (hD_le t ht) hCpi))
      exact mul_nonneg (le_of_lt hK) hs0
    · filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
      obtain ⟨p, -, hp_eq⟩ := Finset.exists_mem_eq_sup' hpairne
        (fun p : Fin N × Fin N => θ t p.1 - θ t p.2)
      have hDval : D t = θ t p.1 - θ t p.2 := hp_eq
      have hmax : ∀ k, θ t k ≤ θ t p.1 := by
        intro k
        have hk : θ t k - θ t p.2 ≤ D t :=
          Finset.le_sup' (fun q : Fin N × Fin N => θ t q.1 - θ t q.2)
            (Finset.mem_univ ((k, p.2) : Fin N × Fin N))
        linarith
      have hmin : ∀ k, θ t p.2 ≤ θ t k := by
        intro k
        have hk : θ t p.1 - θ t k ≤ D t :=
          Finset.le_sup' (fun q : Fin N × Fin N => θ t q.1 - θ t q.2)
            (Finset.mem_univ ((p.1, k) : Fin N × Fin N))
        linarith
      have hDpi : θ t p.1 - θ t p.2 < Real.pi := by
        have := hD_le t ht; linarith
      have hFm : K * Real.sin (θ t p.1 - θ t p.2) ≤ weightedKuramotoF K N W p.2 (θ t) :=
        weightedF_min_ge_Ksin K hK W hWdiag hWoff (θ t) p.2 p.1 hmin hmax hDpi
      have hle_abs : weightedKuramotoF K N W p.2 (θ t)
          ≤ |weightedKuramotoF K N W p.2 (θ t)| := le_abs_self _
      have hsum : |weightedKuramotoF K N W p.2 (θ t)|
          ≤ ∑ i, |weightedKuramotoF K N W i (θ t)| :=
        Finset.single_le_sum (f := fun i => |weightedKuramotoF K N W i (θ t)|)
          (fun i _ => abs_nonneg _) (Finset.mem_univ p.2)
      rw [hDval]; linarith
  have hsin : Filter.Tendsto (fun t => Real.sin (D t)) Filter.atTop (nhds 0) := by
    have h := hKsin.const_mul K⁻¹
    simpa [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hK)] using h
  have hDtends : Filter.Tendsto D Filter.atTop (nhds 0) :=
    diam_tendsto_zero_of_sin_tendsto_zero hCpi
      (Filter.Eventually.of_forall hD_nonneg)
      ((Filter.eventually_ge_atTop (0 : ℝ)).mono (fun t ht => hD_le t ht))
      hsin
  intro a b
  refine squeeze_zero_norm' ?_ hDtends
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
  have h1 : θ t a - θ t b ≤ D t :=
    Finset.le_sup' (fun q : Fin N × Fin N => θ t q.1 - θ t q.2)
      (Finset.mem_univ ((a, b) : Fin N × Fin N))
  have h2 : θ t b - θ t a ≤ D t :=
    Finset.le_sup' (fun q : Fin N × Fin N => θ t q.1 - θ t q.2)
      (Finset.mem_univ ((b, a) : Fin N × Fin N))
  rw [Real.norm_eq_abs]
  exact abs_le.mpr ⟨by linarith, h1⟩

/-
If all phase differences → 0, then ‖kuramotoR N (θ t)‖ → 1.
-/
private theorem R_norm_of_phase_convergence
    (N : ℕ) (hN : 2 ≤ N)
    (θ : ℝ → Fin N → ℝ)
    (hconv : ∀ a b : Fin N, Filter.Tendsto (fun t => θ t a - θ t b) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun t => ‖kuramotoR N (θ t)‖) Filter.atTop (nhds 1) := by
  -- We can factor out $e^{i\theta_0}$ from the sum.
  suffices h_factor : Filter.Tendsto
      (fun t => ‖(∑ k, Complex.exp (Complex.I * (θ t k - θ t ⟨0, by omega⟩))) / N‖) Filter.atTop
      (nhds 1) by
    convert h_factor using 2; norm_num [ Complex.norm_exp, Complex.norm_exp, mul_sub ];
    norm_num [ Complex.norm_exp, mul_sub, Complex.exp_sub, mul_comm Complex.I _, kuramotoR ];
    rw [ ← Finset.sum_div, norm_div, Complex.norm_exp_ofReal_mul_I, div_one ];
  -- Since $\theta_k - \theta_0 \to 0$, we have $\sum_{k=1}^N e^{i(\theta_k - \theta_0)} \to N$.
  have h_sum : Filter.Tendsto
      (fun t => ∑ k : Fin N, Complex.exp (Complex.I * (θ t k - θ t ⟨0, by omega⟩))) Filter.atTop
      (nhds (∑ k : Fin N, Complex.exp (Complex.I * 0))) := by
    refine tendsto_finsetSum _ fun i _ => ?_;
    have hinner : Filter.Tendsto
        (fun t => Complex.I * ((θ t i : ℂ) - (θ t ⟨0, by omega⟩ : ℂ)))
        Filter.atTop (nhds (Complex.I * 0)) := by
      refine tendsto_const_nhds.mul ?_;
      have hcast : Filter.Tendsto
          (fun t => ((θ t i - θ t ⟨0, by omega⟩ : ℝ) : ℂ))
          Filter.atTop (nhds ((0 : ℝ) : ℂ)) :=
        Complex.continuous_ofReal.continuousAt.tendsto.comp ( hconv i ⟨ 0, by linarith ⟩ );
      have hcast' : Filter.Tendsto
          (fun t => ((θ t i : ℂ)) - ((θ t ⟨0, by omega⟩ : ℂ)))
          Filter.atTop (nhds 0) := by
        simpa [ Complex.ofReal_sub ] using hcast;
      exact hcast';
    exact ( Complex.continuous_exp.continuousAt.tendsto.comp hinner );
  convert Filter.Tendsto.norm ( h_sum.div_const ( N : ℂ ) ) using 2; norm_num [ show N ≠ 0
                                                                                by linarith ]

/-- Full convergence to synchrony under all-to-all coupling, K > 0, and
    initial phases in an open semicircle. -/
theorem allToAll_convergence_to_synchrony
    (K : ℝ) (hK : 0 < K) (N : ℕ) (hN : 2 ≤ N)
    (W : Fin N → Fin N → ℝ) (hWdiag : ∀ i, W i i = 0)
    (hWoff : ∀ i j, i ≠ j → W i j = 1)
    (θ : ℝ → Fin N → ℝ)
    (hsol : ∀ t, HasDerivAt θ (kuramotoVectorField K N W (θ t)) t)
    (hsemi : ∀ a b : Fin N, |θ 0 a - θ 0 b| < Real.pi) :
    Filter.Tendsto (fun t => ‖kuramotoR N (θ t)‖) Filter.atTop (nhds 1) := by
  have hWsym : ∀ i j, W i j = W j i := by
    intro i j; by_cases hij : i = j
    · subst hij; rfl
    · rw [hWoff i j hij, hWoff j i (Ne.symm hij)]
  obtain ⟨C, hCpi, hdiam⟩ := semicircle_preserved_uniform K hK N hN W hWdiag hWoff θ hsol hsemi
  have hF_zero := sum_F_sq_tendsto_zero K hK N hN W hWsym hWdiag hWoff θ hsol
  have hconv := phase_diffs_tend_to_zero K hK N hN W hWdiag hWoff θ C hCpi hdiam hF_zero
  exact R_norm_of_phase_convergence N hN θ hconv
