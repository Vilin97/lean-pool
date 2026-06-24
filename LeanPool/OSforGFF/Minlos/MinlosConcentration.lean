/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/

import LeanPool.OSforGFF.Minlos.SazonovTightness
import LeanPool.OSforGFF.Minlos.NuclearSpace
import LeanPool.OSforGFF.Minlos.PietschBridge
import Mathlib.Data.Finsupp.Encodable

/-!
# Minlos Concentration Bound

Proves `nuclear_cylindrical_concentration` — the concentration bound for
nuclear cylindrical measures. `minlos_concentration` is a convenience wrapper.

## Architecture

1. **Helper lemmas** (proved): pointwise CF estimates (`cf_norm_le_one`,
   `cf_nhds_ball`, `one_sub_re_nonneg`, `quadratic_bound_outside`).

2. **Monotonicity lemmas** (proved): `seminorm_mono_of_le`, `finset_sup_le_of_mono`
   derive seminorm monotonicity from consecutive HS embeddings.

3. **Core bounds** (proved):
   - `joint_kernel_bound_finite`: Gaussian averaging on kernel elements
   - `tail_bound_uniform`: Dimension-free Gaussian averaging + Gram matrix + Chebyshev
   - `gram_schmidt_seminorm`: ONB construction for Hilbertian seminorms

4. **Theorem** `nuclear_cylindrical_concentration`: fully proved via
   Gram-Schmidt ONB, kernel concentration, tail bound, and continuity from below.

5. **Theorem** `minlos_concentration`: wrapper applying the above.

## References

- Gel'fand-Vilenkin, "Generalized Functions" Vol. 4, Ch. IV, §3.3
- Bogachev, "Gaussian Measures", Ch. 2-3
- Trèves, "Topological Vector Spaces", Ch. 50-51
-/

open BigOperators MeasureTheory Complex TopologicalSpace Finsupp

noncomputable section

private lemma real_inner_eq_mul (a b : ℝ) : @inner ℝ ℝ _ a b = b * a :=
  RCLike.inner_apply a b

/-! ## CF constantly 1 implies random variable is 0 a.e. -/

/-- If X : Ω → ℝ is measurable and ∫ exp(I * ↑(t * X(ω))) dν = 1 for all t ∈ ℝ,
    then X = 0 ν-a.e.

    Proof sketch: Re(1 - ∫ exp(itX)) = ∫ (1 - cos(tX)) = 0. Since 1 - cos ≥ 0,
    cos(tX) = 1 a.e. for each t. Over countably many t ∈ ℚ simultaneously,
    this forces X = 0.
-/
lemma ae_eq_zero_of_charfun_eq_one {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} [IsProbabilityMeasure ν]
    {X : Ω → ℝ} (hX : Measurable X)
    (hcf : ∀ t : ℝ, ∫ ω, exp (I * ↑(t * X ω)) ∂ν = 1) :
    ∀ᵐ ω ∂ν, X ω = 0 := by
  -- Step 1: Show ν.map X = dirac 0 via charFun equality
  have h_eq : ν.map X = Measure.dirac (0 : ℝ) := by
    apply Measure.ext_of_charFun
    funext t
    rw [charFun_dirac]
    simp only [inner_zero_left]
    rw [charFun_apply, integral_map hX.aemeasurable
      (by fun_prop : AEStronglyMeasurable (fun x => cexp (@inner ℝ ℝ _ x t * I)) _)]
    have h_inner : ∀ ω, cexp (@inner ℝ ℝ _ (X ω) t * I) = exp (I * ↑(t * X ω)) := by
      intro ω
      have : @inner ℝ ℝ _ (X ω) t = t * X ω := by
        change t * starRingEnd ℝ (X ω) = t * X ω; simp
      rw [this]; push_cast; ring_nf
    simp_rw [h_inner]
    rw [hcf t]
    simp [Complex.ofReal_zero, zero_mul, Complex.exp_zero]
  -- Step 2: Deduce X = 0 a.e.
  have h_ae : ∀ᵐ y ∂(ν.map X), y = 0 := by
    rw [h_eq]; exact ae_dirac_iff (measurableSet_singleton 0) |>.mpr rfl
  rwa [show (∀ᵐ ω ∂ν, X ω = 0) ↔ ∀ᵐ y ∂(ν.map X), y = 0 from
    (ae_map_iff hX.aemeasurable (measurableSet_singleton 0)).symm]

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-! ## Helper lemmas -/

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- The characteristic functional satisfies `‖Φ(x)‖ ≤ 1`, as the integral
    of a unit-modulus function against a probability measure.
-/
lemma cf_norm_le_one
    (Φ : E → ℂ) (ν : Measure (E → ℝ)) [IsProbabilityMeasure ν]
    (h_cf_joint : ∀ (n : ℕ) (s : Fin n → ℝ) (x : Fin n → E),
      ∫ ω : E → ℝ, exp (I * ↑(∑ i, s i * ω (x i))) ∂ν =
        Φ (∑ i, s i • x i))
    (x : E) : ‖Φ x‖ ≤ 1 := by
  have h := h_cf_joint 1 (fun _ => 1) (fun _ => x)
  simp only [Fin.sum_univ_one, one_smul, one_mul] at h
  rw [← h]
  calc ‖∫ ω, exp (I * ↑(ω x)) ∂ν‖
      ≤ ∫ ω, ‖exp (I * ↑(ω x))‖ ∂ν := norm_integral_le_integral_norm _
    _ = ∫ ω, 1 ∂ν := by
        congr 1; ext ω; rw [Complex.norm_exp]
        simp [Complex.mul_re, Complex.I_re, Complex.I_im,
              Complex.ofReal_re, Complex.ofReal_im]
    _ = 1 := by simp

/-- `1 - Re(z) ≤ 2` when `‖z‖ ≤ 1`. -/
lemma one_sub_re_le_two_of_norm_le (z : ℂ) (hz : ‖z‖ ≤ 1) : 1 - z.re ≤ 2 := by
  have h1 : |z.re| ≤ ‖z‖ := abs_re_le_norm z
  have h2 : -1 ≤ z.re := by linarith [abs_le.mp (h1.trans hz)]
  linarith

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- Quadratic bound outside a seminorm ball: if `q(x) ≥ δ > 0` and `‖Φ(x)‖ ≤ 1`,
    then `1 - Re(Φ(x)) ≤ (2/δ²) · q(x)²`.
-/
lemma quadratic_bound_outside
    (Φ : E → ℂ) (h_norm_le : ∀ x : E, ‖Φ x‖ ≤ 1)
    (q : Seminorm ℝ E) (δ : ℝ) (hδ : 0 < δ)
    (x : E) (hx : δ ≤ q x) :
    1 - (Φ x).re ≤ (2 / δ ^ 2) * q x ^ 2 := by
  have h_re : 1 - (Φ x).re ≤ 2 := one_sub_re_le_two_of_norm_le _ (h_norm_le x)
  calc 1 - (Φ x).re ≤ 2 := h_re
    _ = (2 / δ ^ 2) * δ ^ 2 := by field_simp
    _ ≤ (2 / δ ^ 2) * q x ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact sq_le_sq' (by linarith) hx

omit [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- CF norm bound gives `1 - Re(Φ(x)) ≥ 0`. -/
lemma one_sub_re_nonneg
    (Φ : E → ℂ) (h_norm_le : ∀ x : E, ‖Φ x‖ ≤ 1) (x : E) :
    0 ≤ 1 - (Φ x).re := by
  have h1 : |Complex.re (Φ x)| ≤ ‖Φ x‖ := abs_re_le_norm _
  have h2 : (Φ x).re ≤ 1 := by linarith [abs_le.mp (h1.trans (h_norm_le x))]
  linarith

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- From `Continuous Φ`, `Φ 0 = 1`, and `WithSeminorms p`: extract a finite set
    of seminorm indices s and radius r > 0 such that `(s.sup p)(x) < r`
    implies `‖1 - Φ(x)‖ < ε`.
-/
lemma cf_nhds_ball
    (Φ : E → ℂ) (h_cf_cont : Continuous Φ) (h_normalized : Φ 0 = 1)
    (p : ℕ → Seminorm ℝ E) (hp_top : WithSeminorms (fun n => p n))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (s : Finset ℕ) (r : ℝ), 0 < r ∧
      ∀ x, (s.sup p) x < r → ‖1 - Φ x‖ < ε := by
  have h_cont_at : ContinuousAt Φ 0 := h_cf_cont.continuousAt
  rw [ContinuousAt, h_normalized] at h_cont_at
  have h_nhds : {x | ‖1 - Φ x‖ < ε} ∈ nhds (0 : E) := by
    have hsub : Φ ⁻¹' Metric.ball 1 ε ⊆ {x : E | ‖1 - Φ x‖ < ε} := by
      intro x hx; simp only [Set.mem_preimage, Metric.mem_ball, dist_eq_norm] at hx
      simp only [Set.mem_setOf_eq]; rwa [norm_sub_rev]
    exact Filter.mem_of_superset
      (h_cont_at (Metric.isOpen_ball.mem_nhds (by simp [Metric.mem_ball, dist_self, hε]))) hsub
  rw [hp_top.hasBasis_zero_ball.mem_iff] at h_nhds
  obtain ⟨⟨s, r⟩, hr, h_sub⟩ := h_nhds
  refine ⟨s, r, hr, fun x hx => h_sub ?_⟩
  rw [Seminorm.ball_zero_eq]; exact hx


/-! ## Monotonicity from consecutive HS embeddings -/

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- From consecutive HS embeddings, `p n ≤ p m` whenever `n ≤ m`. -/
lemma seminorm_mono_of_le (p : ℕ → Seminorm ℝ E)
    (hp_hs : ∀ n, (p (n + 1)).IsHilbertSchmidtEmbedding (p n))
    {n m : ℕ} (h : n ≤ m) : p n ≤ p m := by
  induction m with
  | zero => simp [Nat.le_zero.mp h]
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le h with rfl | hlt
    · exact le_refl _
    · exact le_trans (ih (Nat.lt_succ_iff.mp hlt)) (hp_hs k).1

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- For a finite set of indices, `s.sup p ≤ p m` when `m` dominates every index in `s`
    (which holds when `m ≥ max s`, given monotonicity).
-/
lemma finset_sup_le_of_mono (p : ℕ → Seminorm ℝ E)
    (hp_hs : ∀ n, (p (n + 1)).IsHilbertSchmidtEmbedding (p n))
    (s : Finset ℕ) (m : ℕ) (hm : ∀ n ∈ s, n ≤ m) :
    s.sup p ≤ p m := by
  apply Finset.sup_le
  intro n hn
  exact seminorm_mono_of_le p hp_hs (hm n hn)


/-! ## Combined quadratic bound -/

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- **Combined quadratic bound** from CF continuity: for any ε > 0, there exist m₀ : ℕ
    and K ≥ 0 such that `1 - Re(Φ(x)) ≤ ε + K · (p m₀)(x)²` for all x.
-/
lemma combined_quadratic_bound
    (Φ : E → ℂ) (ν : Measure (E → ℝ)) [IsProbabilityMeasure ν]
    (h_cf_cont : Continuous Φ) (h_normalized : Φ 0 = 1)
    (h_cf_joint : ∀ (n : ℕ) (s : Fin n → ℝ) (x : Fin n → E),
      ∫ ω : E → ℝ, exp (I * ↑(∑ i, s i * ω (x i))) ∂ν =
        Φ (∑ i, s i • x i))
    (p : ℕ → Seminorm ℝ E) (hp_top : WithSeminorms (fun n => p n))
    (hp_hs : ∀ n, (p (n + 1)).IsHilbertSchmidtEmbedding (p n))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (m₀ : ℕ) (K : ℝ), 0 ≤ K ∧
      ∀ x : E, 1 - (Φ x).re ≤ ε + K * (p m₀) x ^ 2 := by
  obtain ⟨s, r, hr, h_ball⟩ := cf_nhds_ball Φ h_cf_cont h_normalized p hp_top ε hε
  have h_norm_le : ∀ x : E, ‖Φ x‖ ≤ 1 := cf_norm_le_one Φ ν h_cf_joint
  set m₀ := s.sup id
  have hm₀ : ∀ n ∈ s, n ≤ m₀ := fun n hn => Finset.le_sup (f := id) hn
  have h_mono : s.sup p ≤ p m₀ := finset_sup_le_of_mono p hp_hs s m₀ hm₀
  refine ⟨m₀, 2 / r ^ 2, by positivity, fun x => ?_⟩
  by_cases hx : (s.sup p) x < r
  · -- Inside ball: ‖1 - Φ(x)‖ < ε, so 1 - Re(Φ(x)) < ε
    have h1 : 1 - (Φ x).re ≤ ‖1 - Φ x‖ := by
      have := abs_re_le_norm (1 - Φ x)
      simp only [Complex.sub_re, Complex.one_re] at this
      linarith [abs_le.mp this]
    have h3 : (0 : ℝ) ≤ 2 / r ^ 2 * (p m₀) x ^ 2 := by positivity
    linarith [h_ball x hx]
  · -- Outside ball: use quadratic_bound_outside with q = p m₀
    push Not at hx
    have hx' : r ≤ (p m₀) x := le_trans hx (h_mono x)
    have := quadratic_bound_outside Φ h_norm_le (p m₀) r hr x hx'
    linarith


/-! ## CF vanishes on seminorm kernel -/

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- If `q(z) = 0` and `q` dominates the CF near 0 (i.e., for any ε > 0, there's a q-ball
    where `‖1 - Φ‖ < ε`), then `Φ(t • z) = 1` for all `t`.

    Proof: `q(t•z) = |t| · q(z) = 0 < r` for any `r > 0`, so `‖1 - Φ(t•z)‖ < ε`
    for all `ε > 0`.
-/
lemma cf_kernel_of_ball_bound
    (Φ : E → ℂ)
    (q : Seminorm ℝ E) (z : E) (hz : q z = 0)
    (h_dom : ∀ ε > 0, ∃ r > 0, ∀ x, q x < r → ‖1 - Φ x‖ < ε) (t : ℝ) :
    Φ (t • z) = 1 := by
  by_contra h_ne
  have h_pos : 0 < ‖1 - Φ (t • z)‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm h_ne))
  obtain ⟨r, hr, h_bound⟩ := h_dom _ h_pos
  have h_qtz : q (t • z) < r := by
    calc q (t • z) = ‖t‖ * q z := map_smul_eq_mul q t z
      _ = ‖t‖ * 0 := by rw [hz]
      _ = 0 := mul_zero _
      _ < r := hr
  linarith [h_bound (t • z) h_qtz]

/-! ## Linear combination a.e. from joint CF -/

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- If `x = ∑ j, β j • e j` in E (real coefficients), then `ω(x) = ∑ j, β j * ω(e j)`
    for ν-a.e. ω. Uses `h_cf_joint` directly — no linearity of ω assumed.

    This is the key trick: the joint CF condition forces the "linear decomposition"
    to hold a.e. even for real (not just rational) coefficients.
-/
lemma linear_combination_ae
    (Φ : E → ℂ) (ν : Measure (E → ℝ)) [IsProbabilityMeasure ν]
    (h_cf_joint : ∀ (n : ℕ) (s : Fin n → ℝ) (x : Fin n → E),
      ∫ ω : E → ℝ, exp (I * ↑(∑ i, s i * ω (x i))) ∂ν =
        Φ (∑ i, s i • x i))
    (h_normalized : Φ 0 = 1)
    {k : ℕ} (e : Fin k → E) (β : Fin k → ℝ) :
    ∀ᵐ ω ∂ν, ω (∑ j, β j • e j) = ∑ j, β j * ω (e j) := by
  set x := ∑ j, β j • e j with x_def
  set X : (E → ℝ) → ℝ := fun ω => ω x - ∑ j, β j * ω (e j)
  have hX_meas : Measurable X := by
    apply Measurable.sub (measurable_pi_apply x)
    exact Finset.measurable_sum _ (fun j _ => (measurable_pi_apply (e j)).const_mul _)
  have hX_cf : ∀ t : ℝ, ∫ ω, exp (I * ↑(t * X ω)) ∂ν = 1 := by
    intro t
    let s' : Fin (k + 1) → ℝ := Fin.cons t (fun j => -t * β j)
    let x' : Fin (k + 1) → E := Fin.cons x e
    have h := h_cf_joint (k + 1) s' x'
    have h_sum_x : ∑ i : Fin (k + 1), s' i • x' i = 0 := by
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, s', x']
      rw [show ∑ j : Fin k, (-t * β j) • e j = -(t • ∑ j, β j • e j) from by
        rw [Finset.smul_sum, ← Finset.sum_neg_distrib]
        congr 1; ext j; simp [neg_smul, neg_mul, smul_smul]]
      simp [x_def]
    have h_sum_ω : ∀ ω', (∑ i : Fin (k + 1), s' i * ω' (x' i)) = t * X ω' := by
      intro ω'
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, s', x', X, mul_sub]
      congr 1
      rw [show ∑ j : Fin k, -t * β j * ω' (e j) =
          -(t * ∑ j, β j * ω' (e j)) from by
        rw [Finset.mul_sum, ← Finset.sum_neg_distrib]; congr 1; ext j; ring]
    rw [h_sum_x, h_normalized] at h
    rwa [show (fun ω' => exp (I * ↑(t * X ω'))) =
      (fun ω' => exp (I * ↑(∑ i : Fin (k + 1), s' i * ω' (x' i)))) from by
      funext ω'; congr 2; exact_mod_cast (h_sum_ω ω').symm]
  have := ae_eq_zero_of_charfun_eq_one hX_meas hX_cf
  filter_upwards [this] with ω hω
  linarith [show X ω = 0 from hω]


/-! ## Pushforward CF for finite evaluation maps -/

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- The pushforward of ν to `Fin k → ℝ` via evaluation at vectors `e₀,...,e_{k-1}`
    has characteristic function `v ↦ Φ(∑ vⱼ • eⱼ)`. This is a direct consequence
    of `h_cf_joint` and `integral_map`.
-/
lemma pushforward_charfun_eq
    (Φ : E → ℂ) (ν : Measure (E → ℝ)) [IsProbabilityMeasure ν]
    (h_cf_joint : ∀ (n : ℕ) (s : Fin n → ℝ) (x : Fin n → E),
      ∫ ω : E → ℝ, exp (I * ↑(∑ i, s i * ω (x i))) ∂ν =
        Φ (∑ i, s i • x i))
    {k : ℕ} (e : Fin k → E) (v : Fin k → ℝ) :
    ∫ y : Fin k → ℝ, exp (I * ↑(∑ j, v j * y j))
      ∂(ν.map (fun ω j => ω (e j))) = Φ (∑ j, v j • e j) := by
  have hg : Measurable (fun ω : E → ℝ => (fun j => ω (e j) : Fin k → ℝ)) :=
    measurable_pi_lambda _ (fun j => measurable_pi_apply (e j))
  rw [integral_map hg.aemeasurable (Continuous.aestronglyMeasurable (by fun_prop))]
  exact h_cf_joint k v e


/-! ## Concentration on good set via Cauchy-Schwarz + Parseval -/

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- **Cauchy-Schwarz + Parseval concentration bound**: if ω is linear on combinations of
    a p-orthonormal sequence `{eⱼ}` and `∑ ω(eⱼ)² ≤ R²`, then for any linear combination
    `x = ∑ βⱼ eⱼ`, we have `|ω(x)| ≤ R · p(x)`.

    This is the pointwise bound at the heart of the concentration argument:
    ω in the "good set" (bounded evaluation norm) respects the seminorm.
-/
lemma bound_on_good_set
    (p : Seminorm ℝ E) (hp : p.IsHilbertian)
    {k : ℕ} (e : Fin k → E) (he : p.IsOrthonormalSeq e)
    (R : ℝ) (hR : 0 < R)
    (ω : E → ℝ)
    (h_linear : ∀ (β : Fin k → ℝ), ω (∑ j, β j • e j) = ∑ j, β j * ω (e j))
    (h_norm : ∑ j : Fin k, (ω (e j)) ^ 2 ≤ R ^ 2)
    (β : Fin k → ℝ) :
    |ω (∑ j, β j • e j)| ≤ R * p (∑ j, β j • e j) := by
  rw [h_linear]
  -- Parseval: p(∑ βⱼ eⱼ)² = ∑ βⱼ²
  have h_parseval := Seminorm.sq_sum_orthonormal p hp e he β
  -- Cauchy-Schwarz: (∑ βⱼ ω(eⱼ))² ≤ (∑ βⱼ²)(∑ ω(eⱼ)²)
  have h_cs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ β (fun j => ω (e j))
  -- Combined: (∑ βⱼ ω(eⱼ))² ≤ (R · p(x))²
  have h_sq : (∑ j : Fin k, β j * ω (e j)) ^ 2 ≤ (R * p (∑ j, β j • e j)) ^ 2 := by
    calc (∑ j : Fin k, β j * ω (e j)) ^ 2
        ≤ (∑ j, β j ^ 2) * (∑ j, (ω (e j)) ^ 2) := h_cs
      _ = p (∑ j, β j • e j) ^ 2 * (∑ j, (ω (e j)) ^ 2) := by rw [h_parseval]
      _ ≤ p (∑ j, β j • e j) ^ 2 * R ^ 2 :=
          mul_le_mul_of_nonneg_left h_norm (sq_nonneg _)
      _ = (R * p (∑ j, β j • e j)) ^ 2 := by ring
  exact abs_le_of_sq_le_sq h_sq (by positivity)


/-! ## Kernel elements vanish a.e. -/

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- If `p(z) = 0` and `p` dominates the CF (i.e., the CF at multiples of z
    is always 1), then `ω(z) = 0` for ν-a.e. ω. Proof: the CF of ω(z)
    is constantly 1, so ω(z) = 0 a.e. by `ae_eq_zero_of_charfun_eq_one`.
-/
lemma kernel_eval_ae_zero
    (Φ : E → ℂ) (ν : Measure (E → ℝ)) [IsProbabilityMeasure ν]
    (h_cf_joint : ∀ (n : ℕ) (s : Fin n → ℝ) (x : Fin n → E),
      ∫ ω : E → ℝ, exp (I * ↑(∑ i, s i * ω (x i))) ∂ν =
        Φ (∑ i, s i • x i))
    (_h_normalized : Φ 0 = 1)
    (p : Seminorm ℝ E) (z : E) (_hz : p z = 0)
    (h_cf_kernel : ∀ t : ℝ, Φ (t • z) = 1) :
    ∀ᵐ ω ∂ν, ω z = 0 := by
  apply ae_eq_zero_of_charfun_eq_one (measurable_pi_apply z)
  intro t
  have h := h_cf_joint 1 (fun _ => t) (fun _ => z)
  simp only [Fin.sum_univ_one] at h
  rw [h_cf_kernel t] at h; exact h


/-! ## ℚ-linearity for all Finsupp simultaneously -/

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- For ν-a.e. ω, the evaluation `ω(x_c)` equals the ℚ-linear combination
    `∑ cᵢ ω(dᵢ)` for **all** `c : ℕ →₀ ℚ` simultaneously.

    Uses countable intersection (`eventually_countable_forall`) since `ℕ →₀ ℚ`
    is countable, plus `linear_combination_ae` for each individual `c`.
-/
lemma q_linear_ae_all
    (Φ : E → ℂ) (ν : Measure (E → ℝ)) [IsProbabilityMeasure ν]
    (h_cf_joint : ∀ (n : ℕ) (s : Fin n → ℝ) (x : Fin n → E),
      ∫ ω : E → ℝ, exp (I * ↑(∑ i, s i * ω (x i))) ∂ν =
        Φ (∑ i, s i • x i))
    (h_normalized : Φ 0 = 1)
    (d : ℕ → E) :
    ∀ᵐ ω ∂ν, ∀ c : ℕ →₀ ℚ,
      ω (c.sum fun i a => (a : ℝ) • d i) = c.sum fun i a => (a : ℝ) * ω (d i) := by
  rw [eventually_countable_forall]
  intro c
  -- Enumerate support: Fin-indexed vectors and coefficients
  let e : Fin c.support.card → E := fun j => d (c.support.equivFin.symm j)
  let β : Fin c.support.card → ℝ := fun j => (c (c.support.equivFin.symm j) : ℝ)
  -- Apply linear_combination_ae with the Fin-indexed data
  have := linear_combination_ae Φ ν h_cf_joint h_normalized e β
  filter_upwards [this] with ω hω
  -- Both sides equal the Fin-indexed sum, via sum_coe_sort + Equiv.sum_comp
  change ω (∑ a ∈ c.support, (↑(c a) : ℝ) • d a) =
    ∑ a ∈ c.support, (↑(c a) : ℝ) * ω (d a)
  have h1 : (∑ a ∈ c.support, (↑(c a) : ℝ) • d a : E) = ∑ j, β j • e j := by
    rw [← c.support.sum_coe_sort]; exact (Equiv.sum_comp c.support.equivFin.symm _).symm
  have h2 : (∑ a ∈ c.support, (↑(c a) : ℝ) * ω (d a) : ℝ) = ∑ j, β j * ω (e j) := by
    rw [← c.support.sum_coe_sort]; exact (Equiv.sum_comp c.support.equivFin.symm _).symm
  rw [h1, h2]; exact hω


/-! ## Bad set definitions for continuity from below -/

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- The "bad set" for the concentration bound: the set of ω where some
    ℚ-linear combination of dense vectors violates the seminorm bound.
-/
def concentrationBadSet (d : ℕ → E) (p : Seminorm ℝ E) (C : ℝ) :
    Set (E → ℝ) :=
  {ω | ∃ c : ℕ →₀ ℚ,
    ¬ (|ω (c.sum fun i a => (a : ℝ) • d i)| ≤
      C * p (c.sum fun i a => (a : ℝ) • d i))}

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- The "restricted bad set" B_N: bad set restricted to ℚ-linear combinations
    with support in `{0, ..., N-1}`.
-/
def concentrationBadSetN (d : ℕ → E) (p : Seminorm ℝ E) (C : ℝ) (N : ℕ) :
    Set (E → ℝ) :=
  {ω | ∃ c : ℕ →₀ ℚ, c.support ⊆ Finset.range N ∧
    ¬ (|ω (c.sum fun i a => (a : ℝ) • d i)| ≤
      C * p (c.sum fun i a => (a : ℝ) • d i))}

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- B_N ⊆ B_M when N ≤ M. -/
lemma concentrationBadSetN_mono (d : ℕ → E) (p : Seminorm ℝ E) (C : ℝ)
    {N M : ℕ} (h : N ≤ M) :
    concentrationBadSetN d p C N ⊆ concentrationBadSetN d p C M := by
  intro ω hω
  obtain ⟨c, hc_supp, hc_bad⟩ := hω
  exact ⟨c, hc_supp.trans (Finset.range_mono h), hc_bad⟩

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- The full bad set equals the union of the restricted bad sets.
    Every `c : ℕ →₀ ℚ` has finite support contained in some `Finset.range N`.
-/
lemma concentrationBadSet_eq_iUnion (d : ℕ → E) (p : Seminorm ℝ E) (C : ℝ) :
    concentrationBadSet d p C = ⋃ N, concentrationBadSetN d p C N := by
  ext ω
  simp only [concentrationBadSet, concentrationBadSetN, Set.mem_setOf_eq, Set.mem_iUnion]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c.support.sup id + 1, c, ?_, hc⟩
    intro i hi
    exact Finset.mem_range.mpr (by
      have : i ≤ c.support.sup id := Finset.le_sup (f := id) hi
      omega)
  · rintro ⟨_, c, _, hc⟩
    exact ⟨c, hc⟩

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- If `ν(B_N) ≤ δ` for all N, then `ν(full bad set) ≤ δ`.
    Uses continuity of measure from below (`tendsto_measure_iUnion`).
-/
lemma concentrationBadSet_measure_le (d : ℕ → E) (p : Seminorm ℝ E) (C : ℝ)
    (ν : Measure (E → ℝ)) (δ : ENNReal)
    (h_bound : ∀ N, ν (concentrationBadSetN d p C N) ≤ δ) :
    ν (concentrationBadSet d p C) ≤ δ := by
  rw [concentrationBadSet_eq_iUnion]
  exact le_of_tendsto' (tendsto_measure_iUnion_atTop
    (fun _ _ h => concentrationBadSetN_mono d p C h)) h_bound


/-! ## Seminorm Gram-Schmidt (proved) -/

section GramSchmidt

variable {F : Type*} [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]

omit [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] in
/-- If `p(z) = 0`, then `p(x + z) = p(x)`. -/
private lemma gs_seminorm_add_kernel (p : Seminorm ℝ F) (x z : F) (hz : p z = 0) :
    p (x + z) = p x := by
  apply le_antisymm
  · calc p (x + z) ≤ p x + p z := map_add_le_add p x z
    _ = p x := by rw [hz, add_zero]
  · calc p x = p (x + z + (-z)) := by congr 1; abel
    _ ≤ p (x + z) + p (-z) := map_add_le_add p _ _
    _ = p (x + z) := by rw [map_neg_eq_map, hz, add_zero]

omit [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] in
private lemma gs_innerProd_sub_left (p : Seminorm ℝ F) (hp : p.IsHilbertian)
    (x₁ x₂ y : F) :
    p.innerProd (x₁ - x₂) y = p.innerProd x₁ y - p.innerProd x₂ y := by
  rw [sub_eq_add_neg, p.innerProd_add_left hp x₁ (-x₂) y, p.innerProd_neg_left]
  ring

omit [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] in
private lemma gs_innerProd_smul_right (p : Seminorm ℝ F) (hp : p.IsHilbertian)
    (a : ℝ) (x y : F) :
    p.innerProd x (a • y) = a * p.innerProd x y := by
  rw [p.innerProd_comm, p.innerProd_smul_left hp, p.innerProd_comm]

omit [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] in
private lemma gs_innerProd_sum_right (p : Seminorm ℝ F) (hp : p.IsHilbertian)
    {ι : Type*} (s : Finset ι) (x : F) (f : ι → F) :
    p.innerProd x (∑ j ∈ s, f j) = ∑ j ∈ s, p.innerProd x (f j) := by
  rw [p.innerProd_comm, p.innerProd_sum_left hp]
  congr 1; ext j; rw [p.innerProd_comm]

omit [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] in
/-- Pythagorean theorem: if `ip(x, y) = 0` then `p(x+y)^2 = p(x)^2 + p(y)^2`. -/
private lemma gs_pythagoras (p : Seminorm ℝ F)
    (hp : p.IsHilbertian) (x y : F) (hxy : p.innerProd x y = 0) :
    p (x + y) ^ 2 = p x ^ 2 + p y ^ 2 := by
  have h1 : p (x + y) ^ 2 = p (x - y) ^ 2 := by
    simp only [Seminorm.innerProd] at hxy; linarith
  linarith [hp x y]

omit [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] in
/-- **Gram-Schmidt for Hilbertian seminorms**: given N vectors in F and a Hilbertian
    seminorm p, there exist k orthonormal vectors such that every element of
    the span of the original vectors decomposes as a p-ONB combination plus a kernel
    element (where p vanishes).
-/
lemma gram_schmidt_seminorm_aux (p : Seminorm ℝ F) (hp : p.IsHilbertian)
    (N : ℕ) (d : Fin N → F) :
    ∃ (k : ℕ) (e : Fin k → F),
      p.IsOrthonormalSeq e ∧
      (∀ (β : Fin N → ℝ), ∃ (α : Fin k → ℝ),
        p (∑ i, β i • d i - ∑ j, α j • e j) = 0 ∧
        p (∑ i, β i • d i) ^ 2 = ∑ j, α j ^ 2) := by
  induction N with
  | zero =>
    exact ⟨0, Fin.elim0, fun i => Fin.elim0 i, fun β => ⟨Fin.elim0, by simp, by simp⟩⟩
  | succ n ih =>
    obtain ⟨k, e, he_orth, he_decomp⟩ := ih (fun i => d (Fin.castSucc i))
    -- v = d(last n), projection coefficients c_j = ip(v, e_j)
    set v := d (Fin.last n) with hv_def
    set c : Fin k → ℝ := fun j => p.innerProd v (e j) with hc_def
    -- u = v - Σ c_j e_j is the residual
    set u := v - ∑ j : Fin k, c j • e j with hu_def
    -- u ⊥ e_j for all j
    have hu_orth : ∀ j : Fin k, p.innerProd u (e j) = 0 := by
      intro j; change p.innerProd (v - ∑ i : Fin k, c i • e i) (e j) = 0
      rw [gs_innerProd_sub_left p hp, p.innerProd_sum_left hp]
      simp_rw [p.innerProd_smul_left hp]
      suffices h : ∑ i : Fin k, c i * p.innerProd (e i) (e j) = c j by linarith
      conv_lhs => arg 2; ext i; rw [he_orth i j]
      simp [Finset.sum_ite_eq', Finset.mem_univ]
    -- u ⊥ (Σ c_j e_j)
    have hu_proj_orth : p.innerProd u (∑ j : Fin k, c j • e j) = 0 := by
      rw [gs_innerProd_sum_right p hp]
      simp_rw [gs_innerProd_smul_right p hp]; simp [hu_orth]
    -- Pythagoras: u + proj = v
    have hv_eq : u + ∑ j : Fin k, c j • e j = v := sub_add_cancel v _
    have h_pyth := gs_pythagoras p hp u (∑ j : Fin k, c j • e j) hu_proj_orth
    -- p(proj)^2 = Σ c_j^2
    have h_proj_sq : p (∑ j : Fin k, c j • e j) ^ 2 = ∑ j : Fin k, c j ^ 2 :=
      p.sq_sum_orthonormal hp e he_orth c
    -- Splitting Fin (n+1) sums
    have h_split : ∀ β : Fin (n + 1) → ℝ,
        ∑ i : Fin (n + 1), β i • d i =
        (∑ i : Fin n, β (Fin.castSucc i) • d (Fin.castSucc i)) +
        β (Fin.last n) • v := by
      intro β; rw [Fin.sum_univ_castSucc]
    -- Helper: decompose the ONB sum
    have h_onb_decomp : ∀ (α' : Fin k → ℝ) (b : ℝ),
        ∑ j : Fin k, (α' j + b * c j) • e j =
        (∑ j, α' j • e j) + b • ∑ j : Fin k, c j • e j := by
      intro α' b
      simp_rw [add_smul, Finset.sum_add_distrib, mul_smul, Finset.smul_sum]
    -- Helper: b • v = b • proj + b • u
    have hv_decomp : ∀ b' : ℝ,
        b' • v = b' • (∑ j : Fin k, c j • e j) + b' • u := by
      intro b'; change b' • v = b' • (∑ j : Fin k, c j • e j) +
        b' • (v - ∑ j : Fin k, c j • e j)
      rw [← smul_add]; congr 1; abel
    -- Case split on whether p(u) = 0 or p(u) > 0
    by_cases hu0 : p u = 0
    · -- Case 1: u is in the kernel. Same ONB works.
      refine ⟨k, e, he_orth, ?_⟩
      intro β
      obtain ⟨α', hα'_ker, hα'_parseval⟩ := he_decomp (fun i => β (Fin.castSucc i))
      let b := β (Fin.last n)
      have hbu : p (b • u) = 0 := by rw [map_smul_eq_mul, hu0, mul_zero]
      refine ⟨fun j => α' j + b * c j, ?_, ?_⟩
      · -- p(full sum - ONB combination) = 0
        have h_eq : ∑ i : Fin (n + 1), β i • d i -
            ∑ j : Fin k, (α' j + b * c j) • e j =
            (∑ i : Fin n, β (Fin.castSucc i) • d (Fin.castSucc i) -
              ∑ j, α' j • e j) + b • u := by
          rw [h_split β, h_onb_decomp α' b, hu_def, smul_sub]; abel
        rw [h_eq, gs_seminorm_add_kernel p _ _ hbu, hα'_ker]
      · -- p(full sum)^2 = Σ (α'j + b*cj)^2
        rw [h_split β]
        conv_lhs =>
          rw [show β (Fin.last n) = b from rfl,
              show v = (∑ j : Fin k, c j • e j) +
                (v - ∑ j : Fin k, c j • e j) from (add_sub_cancel _ _).symm]
        rw [show (∑ i : Fin n, β (Fin.castSucc i) • d (Fin.castSucc i)) +
            b • ((∑ j : Fin k, c j • e j) + (v - ∑ j : Fin k, c j • e j)) =
            (∑ j : Fin k, (α' j + b * c j) • e j) +
            ((∑ i : Fin n, β (Fin.castSucc i) • d (Fin.castSucc i) -
              ∑ j, α' j • e j) +
            b • (v - ∑ j : Fin k, c j • e j)) from by
          rw [h_onb_decomp, smul_add]; abel]
        have h_ker :
            p ((∑ i : Fin n, β (Fin.castSucc i) • d (Fin.castSucc i) -
              ∑ j, α' j • e j) +
            b • (v - ∑ j : Fin k, c j • e j)) = 0 :=
          (gs_seminorm_add_kernel p _ _ hbu).trans hα'_ker
        rw [gs_seminorm_add_kernel p _ _ h_ker, p.sq_sum_orthonormal hp e he_orth]
    · -- Case 2: p(u) > 0. Extend ONB with normalized u.
      have hpu_pos : 0 < p u := lt_of_le_of_ne (apply_nonneg p u) (Ne.symm hu0)
      let e_new := (p u)⁻¹ • u
      have he_new_norm : p e_new = 1 := by
        change p ((p u)⁻¹ • u) = 1
        rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpu_pos),
            inv_mul_cancel₀ (ne_of_gt hpu_pos)]
      have he_new_orth_e : ∀ j : Fin k, p.innerProd e_new (e j) = 0 := by
        intro j; change p.innerProd ((p u)⁻¹ • u) (e j) = 0
        rw [p.innerProd_smul_left hp]; simp [hu_orth j]
      have hu_eq_smul : u = p u • e_new := by
        change u = p u • ((p u)⁻¹ • u)
        rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hpu_pos), one_smul]
      -- Extended ONB: e_new at index 0, old e at indices 1..k
      let e' : Fin (k + 1) → F := Fin.cons e_new e
      have he'_orth : p.IsOrthonormalSeq e' := by
        intro i j
        refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j
        · -- (0,0)
          change p.innerProd e_new e_new = if (0 : Fin (k + 1)) = 0 then 1 else 0
          rw [if_pos rfl, p.innerProd_self, he_new_norm, one_pow]
        · -- (0, succ j')
          change p.innerProd e_new (e j') = if (0 : Fin (k + 1)) = j'.succ then 1 else 0
          rw [if_neg (Fin.succ_ne_zero j').symm, he_new_orth_e j']
        · -- (succ i', 0)
          change p.innerProd (e i') e_new = if i'.succ = (0 : Fin (k + 1)) then 1 else 0
          rw [if_neg (Fin.succ_ne_zero i'), p.innerProd_comm, he_new_orth_e i']
        · -- (succ i', succ j')
          change p.innerProd (e i') (e j') = if i'.succ = j'.succ then 1 else 0
          rw [show (if i'.succ = j'.succ then (1:ℝ) else 0) =
            if i' = j' then 1 else 0 from by simp [Fin.ext_iff]]
          exact he_orth i' j'
      refine ⟨k + 1, e', he'_orth, ?_⟩
      intro β
      obtain ⟨α', hα'_ker, hα'_parseval⟩ := he_decomp (fun i => β (Fin.castSucc i))
      let b := β (Fin.last n)
      let α_new : Fin (k + 1) → ℝ := Fin.cons (b * p u) (fun j => α' j + b * c j)
      -- Key identity: the extended ONB sum equals old ONB sum + b•v
      have h_ext_sum : ∑ j : Fin (k + 1), α_new j • e' j =
          (∑ j, α' j • e j) + b • v := by
        change ∑ j : Fin (k + 1),
            (Fin.cons (b * p u) (fun j => α' j + b * c j) : Fin (k + 1) → ℝ) j •
            (Fin.cons e_new e : Fin (k + 1) → F) j =
          (∑ j, α' j • e j) + b • v
        rw [Fin.sum_univ_succ]; simp only [Fin.cons_zero, Fin.cons_succ]
        rw [h_onb_decomp α' b]
        -- Goal: (b*pu)•e_new + (Σ α'j•ej + b•Σ cj•ej) = Σ α'j•ej + b•v
        -- Since e_new = pu⁻¹•u, (b*pu)•(pu⁻¹•u) = b•u
        -- And b•v = b•Σ cj•ej + b•u (from hv_decomp)
        conv_rhs => rw [show b • v = b • (∑ j : Fin k, c j • e j) + b • u from hv_decomp b]
        change (β (Fin.last n) * p u) • ((p u)⁻¹ • u) +
            (∑ j, α' j • e j + β (Fin.last n) • ∑ j : Fin k, c j • e j) =
          ∑ j, α' j • e j +
            (β (Fin.last n) • ∑ j : Fin k, c j • e j +
              β (Fin.last n) • (v - ∑ j : Fin k, c j • e j))
        rw [smul_smul, mul_assoc, mul_inv_cancel₀ (ne_of_gt hpu_pos), mul_one]
        abel
      refine ⟨α_new, ?_, ?_⟩
      · -- kernel: p(full sum - extended ONB sum) = 0
        rw [show ∑ i : Fin (n + 1), β i • d i - ∑ j : Fin (k + 1), α_new j • e' j =
            ∑ i : Fin n, β (Fin.castSucc i) • d (Fin.castSucc i) -
              ∑ j, α' j • e j from by rw [h_ext_sum, h_split]; abel]
        exact hα'_ker
      · -- Parseval: p(full sum)^2 = Σ α_new(j)^2
        rw [h_split]
        -- Rearrange: Σ β'i d(ci) + b•v = (Σ α'j ej + b•v) + kernel_residual
        have h_rearr :
            (∑ i : Fin n, β (Fin.castSucc i) • d (Fin.castSucc i)) +
              β (Fin.last n) • v =
            (∑ j : Fin (k + 1), α_new j • e' j) +
            (∑ i : Fin n, β (Fin.castSucc i) • d (Fin.castSucc i) -
              ∑ j, α' j • e j) := by
          rw [h_ext_sum]; abel
        rw [h_rearr, gs_seminorm_add_kernel p _ _ hα'_ker,
            p.sq_sum_orthonormal hp e' he'_orth]

end GramSchmidt

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
lemma gram_schmidt_seminorm (p : Seminorm ℝ E) (hp : p.IsHilbertian)
    (N : ℕ) (d : Fin N → E) :
    ∃ (k : ℕ) (e : Fin k → E),
      p.IsOrthonormalSeq e ∧
      (∀ (β : Fin N → ℝ), ∃ (α : Fin k → ℝ),
        p (∑ i, β i • d i - ∑ j, α j • e j) = 0 ∧
        p (∑ i, β i • d i) ^ 2 = ∑ j, α j ^ 2) :=
  gram_schmidt_seminorm_aux p hp N d


/-! ## Per-N concentration bound -/

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- For each N, the restricted bad set B_N has measure bounded by the tail probability
    of the squared evaluation norm on a p-ONB.

    Key argument: on the a.e. set where all decompositions hold,
    Cauchy-Schwarz + Parseval gives |ω(x_c)| ≤ R · p(x_c) whenever Σ ω(eⱼ)² ≤ R².
    So B_N ⊆ {Σ ω(eⱼ)² > R²} ∪ (null set).
-/
lemma concentrationBadSetN_measure_bound
    (Φ : E → ℂ) (ν : Measure (E → ℝ)) [IsProbabilityMeasure ν]
    (h_cf_joint : ∀ (n : ℕ) (s : Fin n → ℝ) (x : Fin n → E),
      ∫ ω : E → ℝ, exp (I * ↑(∑ i, s i * ω (x i))) ∂ν =
        Φ (∑ i, s i • x i))
    (h_normalized : Φ 0 = 1)
    (d : ℕ → E) (p : Seminorm ℝ E) (_hp : p.IsHilbertian)
    (h_cf_kernel : ∀ z, p z = 0 → ∀ t : ℝ, Φ (t • z) = 1)
    {k : ℕ} (e : Fin k → E) (_he : p.IsOrthonormalSeq e)
    (h_decomp : ∀ c : ℕ →₀ ℚ, ∃ (α : Fin k → ℝ),
      p (c.sum (fun i a => (a : ℝ) • d i) - ∑ j, α j • e j) = 0 ∧
      p (c.sum (fun i a => (a : ℝ) • d i)) ^ 2 = ∑ j, α j ^ 2)
    (R : ℝ) (hR : 0 < R) (N : ℕ) :
    ν (concentrationBadSetN d p R N) ≤
      ν {ω : E → ℝ | R ^ 2 < ∑ j : Fin k, (ω (e j)) ^ 2} := by
  -- Choose decomposition coefficients for each c
  choose α hα_ker hα_parseval using h_decomp
  -- Step 1: For a.e. ω, for all c, ω(x_c) = Σ α(c)_j ω(e_j)
  have h_ae_decomp : ∀ᵐ ω ∂ν, ∀ c : ℕ →₀ ℚ,
      ω (c.sum (fun i a => (a : ℝ) • d i)) = ∑ j, (α c) j * ω (e j) := by
    rw [eventually_countable_forall]; intro c
    -- z_c = x_c - Σ α_j e_j is in the kernel of p
    set z_c := c.sum (fun i a => (a : ℝ) • d i) - ∑ j, (α c) j • e j
    -- ω(z_c) = 0 a.e. via kernel_eval_ae_zero + h_cf_kernel
    have h_z_zero := kernel_eval_ae_zero Φ ν h_cf_joint h_normalized p z_c
      (hα_ker c) (h_cf_kernel z_c (hα_ker c))
    -- x_c = z_c + Σ α_j e_j, so linear_combination_ae with (z_c, e₁,...,eₖ)
    -- and coefficients (1, α₁,...,αₖ) gives ω(x_c) = ω(z_c) + Σ α_j ω(e_j) a.e.
    let e' : Fin (k + 1) → E := Fin.cons z_c e
    let β' : Fin (k + 1) → ℝ := Fin.cons 1 (α c)
    have h_sum_eq : (∑ j, β' j • e' j) = c.sum (fun i a => (a : ℝ) • d i) := by
      rw [Fin.sum_univ_succ]
      simp only [e', β', Fin.cons_zero, Fin.cons_succ, one_smul]
      exact sub_add_cancel _ _
    have h_lin := linear_combination_ae Φ ν h_cf_joint h_normalized e' β'
    filter_upwards [h_z_zero, h_lin] with ω h_z h_xc
    -- h_xc: ω(Σ β'_j • e'_j) = Σ β'_j * ω(e'_j)
    rw [h_sum_eq] at h_xc; rw [h_xc, Fin.sum_univ_succ]
    simp only [e', β', Fin.cons_zero, Fin.cons_succ, one_mul, h_z, zero_add]
  -- Step 2: concentrationBadSetN ⊆ {R² < Σ ω(e_j)²} ∪ (null set)
  set tail := {ω : E → ℝ | R ^ 2 < ∑ j : Fin k, (ω (e j)) ^ 2}
  set null_set := {ω : E → ℝ | ¬∀ c : ℕ →₀ ℚ,
    ω (c.sum (fun i a => (a : ℝ) • d i)) = ∑ j, (α c) j * ω (e j)}
  have h_null : ν null_set = 0 := ae_iff.mp h_ae_decomp
  have h_sub : concentrationBadSetN d p R N ⊆ tail ∪ null_set := by
    intro ω hω
    by_contra h_not
    simp only [Set.mem_union, not_or] at h_not
    obtain ⟨h_not_tail, h_not_null⟩ := h_not
    simp only [tail, null_set, Set.mem_setOf_eq, not_lt, not_not] at h_not_tail h_not_null
    -- h_not_tail: Σ ω(e_j)² ≤ R²
    -- h_not_null: ∀ c, ω(x_c) = Σ α(c)_j ω(e_j)
    obtain ⟨c, _, hc_bad⟩ := hω
    apply hc_bad
    rw [h_not_null c]
    -- |Σ α(c)_j ω(e_j)| ≤ R · p(x_c) by Cauchy-Schwarz + Parseval
    have h_cs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (α c) (fun j => ω (e j))
    have h_sq : (∑ j, (α c) j * ω (e j)) ^ 2 ≤
        (R * p (c.sum fun i a => (a : ℝ) • d i)) ^ 2 := by
      calc (∑ j, (α c) j * ω (e j)) ^ 2
          ≤ (∑ j, (α c) j ^ 2) * (∑ j, ω (e j) ^ 2) := h_cs
        _ = p (c.sum fun i a => (a : ℝ) • d i) ^ 2 * (∑ j, ω (e j) ^ 2) := by
            rw [hα_parseval c]
        _ ≤ p (c.sum fun i a => (a : ℝ) • d i) ^ 2 * R ^ 2 :=
            mul_le_mul_of_nonneg_left h_not_tail (sq_nonneg _)
        _ = (R * p (c.sum fun i a => (a : ℝ) • d i)) ^ 2 := by ring
    exact abs_le_of_sq_le_sq h_sq (by positivity)
  calc ν (concentrationBadSetN d p R N)
      ≤ ν (tail ∪ null_set) := measure_mono h_sub
    _ ≤ ν tail + ν null_set := measure_union_le _ _
    _ = ν tail := by rw [h_null, add_zero]


/-! ## Nuclear cylindrical concentration -/

/- **Nuclear cylindrical concentration** (Gel'fand-Vilenkin Vol.4, Ch.IV §3.3).

Given:
- A separable, nonempty locally convex space `E`,
- Hilbertian seminorms `p` with consecutive Hilbert-Schmidt embeddings
  (`(p (n+1)).IsHilbertSchmidtEmbedding (p n)`) generating the topology,
- A cylindrical probability measure `ν` with continuous characteristic
  functional `Φ` satisfying `Φ(0) = 1` and the joint CF condition
  `∫ exp(i ∑ sⱼ ω(xⱼ)) dν = Φ(∑ sⱼ xⱼ)`,
- A dense sequence `d : ℕ → E`,

the conclusion is: for any `ε > 0`, there exist `m, C : ℕ` such that
  `ν {ω | ∃ c : ℕ →₀ ℚ, |ω(x_c)| > C · (p m)(x_c)} < ε`.

**Proof**:
1. CF continuity at 0 → seminorm ball where `‖1 - Φ‖ < ε/2`.
2. Quadratic bound: `1 - Re Φ(x) ≤ ε/2 + (2/r²) · (p m₀)(x)²`.
3. Gaussian averaging on `(p m₁)`-orthonormal `{eⱼ}`:
   `𝔼[1 - exp(-σ² ω(eⱼ)²/2)] ≤ ε/2 + 2σ²(2/r²)(p m₀)(eⱼ)²`.
4. Sum over `j` using HS bound `∑ (p m₀)(eⱼ)² ≤ C_HS` → tail control.
5. Chebyshev + Bessel inequality for ℚ-linear combinations.

**References:**
- Gel'fand & Vilenkin, *Generalized Functions* Vol. 4, Ch. IV, §3.3
- Bogachev, *Gaussian Measures*, Ch. 2–3
- Minlos, *Generalized Random Processes*, Theorems 2.1–2.3 -/
/-! ### Kernel evaluation a.e. bound -/

/-- **Joint kernel bound for finite collection**.
    If z₁,...,zₙ are kernel elements (p_m(zᵢ) = 0) and the quadratic CF bound gives
    `1 - Re(Φ(∑ tᵢ zᵢ)) ≤ ε_q` for all t, then `P(∃i, ω(zᵢ) ≠ 0) ≤ ε_q`.
    Proved by pushforward to ℝⁿ and multivariate Gaussian averaging.
-/
private lemma joint_kernel_bound_finite
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (Φ : E → ℂ) (ν : Measure (E → ℝ)) [IsProbabilityMeasure ν]
    (h_cf_joint : ∀ (n : ℕ) (s : Fin n → ℝ) (x : Fin n → E),
      ∫ ω : E → ℝ, exp (I * ↑(∑ i, s i * ω (x i))) ∂ν =
        Φ (∑ i, s i • x i))
    (_h_normalized : Φ 0 = 1)
    (ε_q : ℝ) (hε_q : 0 < ε_q)
    (n : ℕ) (z : Fin n → E)
    (h_cf_bound : ∀ t : Fin n → ℝ,
      1 - (Φ (∑ i, t i • z i)).re ≤ ε_q) :
    ν {ω : E → ℝ | ∃ i : Fin n, ω (z i) ≠ 0} ≤ ENNReal.ofReal ε_q := by
  -- Case n = 0: the set is empty
  rcases n with _ | n
  · simp
  -- Strategy: pushforward ν to EuclideanSpace, apply fubini_gaussian_charFun,
  -- bound by ε_q using CF bound, then monotone convergence.
  --
  -- Step 0: Construct pushforward probability measure on V := EuclideanSpace ℝ (Fin (n+1))
  set V := EuclideanSpace ℝ (Fin (n + 1)) with hV_def
  let toLp := MeasurableEquiv.toLp (p := 2) (X := Fin (n + 1) → ℝ)
  let eval_z : (E → ℝ) → V := fun ω => toLp (fun j => ω (z j))
  have h_meas_z : Measurable eval_z :=
    toLp.measurable.comp (measurable_pi_lambda _ (fun j => measurable_pi_apply (z j)))
  let μ := ν.map eval_z
  haveI h_prob : IsProbabilityMeasure μ :=
    Measure.isProbabilityMeasure_map h_meas_z.aemeasurable
  let μ' : ProbabilityMeasure V := ⟨μ, h_prob⟩
  -- Step 1: Coordinate access: (eval_z ω) i = ω (z i)
  have h_coord : ∀ (ω : E → ℝ) (i : Fin (n + 1)), (eval_z ω) i = ω (z i) := fun _ _ => rfl
  -- Step 2: Inner product on V: ⟨eval_z(ω), v⟩ = ∑ j, v j * ω(z j)
  have h_inner : ∀ (ω : E → ℝ) (v : V),
      @inner ℝ V _ (eval_z ω) v = ∑ j, v j * ω (z j) := by
    intro ω v; erw [PiLp.inner_apply]
    simp only [real_inner_eq_mul, h_coord]
  -- Step 3: CF of μ' equals v ↦ Φ(∑ vⱼ zⱼ)
  have h_cf : ∀ v : V, charFun μ'.toMeasure v = Φ (∑ i, v i • z i) := by
    intro v; rw [charFun_apply]
    change ∫ y : V, cexp (@inner ℝ V _ y v * I) ∂(ν.map eval_z) = Φ (∑ i, v i • z i)
    rw [integral_map h_meas_z.aemeasurable (by fun_prop)]
    simp_rw [h_inner]
    have h_eq : ∀ ω : E → ℝ,
        cexp (↑(∑ j : Fin (n + 1), v j * ω (z j)) * I) =
        cexp (I * ↑(∑ j, v j * ω (z j))) := by
      intro ω; congr 1; ring
    simp_rw [h_eq]
    exact h_cf_joint (n + 1) (fun j => v j) z
  -- Step 4: CF bound on V: 1 - Re(charFun μ' v) ≤ ε_q for all v
  have h_cf_re_bound : ∀ v : V, 1 - (charFun μ'.toMeasure v).re ≤ ε_q := by
    intro v; rw [h_cf]; exact h_cf_bound (fun j => v j)
  -- Step 5: Gaussian averaging bound
  have h_gauss : ∀ σ : ℝ, 0 < σ →
      ∫ y, (1 - Real.exp (-(σ ^ 2 * ‖y‖ ^ 2 / 2))) ∂μ'.toMeasure ≤ ε_q := by
    intro σ hσ
    rw [fubini_gaussian_charFun μ' (charFun μ'.toMeasure) (fun _ => rfl) σ hσ]
    set C := ∫ x : V, gaussDensity σ x with hC_def
    have hC_pos : 0 < C := gaussDensity_integral_pos' (V := V) σ hσ
    have hCinv_nn : 0 ≤ C⁻¹ := inv_nonneg.mpr hC_pos.le
    calc C⁻¹ * ∫ x : V, gaussDensity σ x * (1 - (charFun μ'.toMeasure x).re)
        ≤ C⁻¹ * ∫ x : V, gaussDensity σ x * ε_q := by
          apply mul_le_mul_of_nonneg_left _ hCinv_nn
          apply integral_mono
          · have h1 := gaussDensity_mul_charFun_re_integrable' μ' _ (fun _ => rfl) σ hσ
            exact (gaussDensity_integrable' (V := V) σ hσ).sub h1 |>.congr
              (Filter.Eventually.of_forall fun x => by simp [Pi.sub_apply]; ring)
          · exact (gaussDensity_integrable' (V := V) σ hσ).mul_const ε_q
          · intro x
            apply mul_le_mul_of_nonneg_left (h_cf_re_bound x) (gaussDensity_nonneg' σ x)
      _ = ε_q := by
          rw [integral_mul_const ε_q (fun x => gaussDensity σ x)]
          rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hC_pos), one_mul]
  -- Step 6: Convert integral bound on V to bound on E → ℝ
  have h_norm_sq : ∀ ω : E → ℝ, ‖eval_z ω‖ ^ 2 = ∑ i, ω (z i) ^ 2 := by
    intro ω
    rw [EuclideanSpace.norm_eq]
    rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
    congr 1; ext i; simp [h_coord]
  have h_gauss_orig : ∀ σ : ℝ, 0 < σ →
      ∫ ω, (1 - Real.exp (-(σ ^ 2 * (∑ i, ω (z i) ^ 2) / 2))) ∂ν ≤ ε_q := by
    intro σ hσ
    have := h_gauss σ hσ
    rw [show μ'.toMeasure = ν.map eval_z from rfl] at this
    rw [integral_map h_meas_z.aemeasurable] at this
    · convert this using 1; congr 1; ext ω; congr 2; rw [h_norm_sq]
    · exact (continuous_const.sub (by fun_prop :
        Continuous (fun y : V => Real.exp (-(σ ^ 2 * ‖y‖ ^ 2 / 2))))).aestronglyMeasurable
  -- Step 7: Conclude via level sets + Chebyshev + continuity from below
  set S : (E → ℝ) → ℝ := fun ω => ∑ i, ω (z i) ^ 2
  have h_bad_eq : {ω : E → ℝ | ∃ i, ω (z i) ≠ 0} = {ω | 0 < S ω} := by
    ext ω; simp only [S, Set.mem_setOf_eq]
    constructor
    · rintro ⟨i, hi⟩
      exact Finset.sum_pos' (fun j _ => sq_nonneg _) ⟨i, Finset.mem_univ _, by positivity⟩
    · intro hS; by_contra h_all; push Not at h_all
      exact absurd (Finset.sum_eq_zero (fun i _ => by rw [h_all i, sq, mul_zero])) (ne_of_gt hS)
  have h_union : {ω : E → ℝ | 0 < S ω} =
      ⋃ m : ℕ, {ω | (1 : ℝ) / (↑m + 1) ≤ S ω} := by
    ext ω; simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · intro hS
      obtain ⟨m, hm⟩ := exists_nat_gt (1 / S ω)
      refine ⟨m, ?_⟩
      rw [div_le_iff₀ (show (0 : ℝ) < ↑m + 1 from by positivity)]
      have := (div_lt_iff₀ hS).mp hm
      linarith
    · rintro ⟨m, hm⟩; exact lt_of_lt_of_le (by positivity) hm
  have h_mono : Monotone (fun m : ℕ => {ω : E → ℝ | (1 : ℝ) / (↑m + 1) ≤ S ω}) := by
    intro m₁ m₂ h ω hω; simp only [Set.mem_setOf_eq] at hω ⊢
    exact le_trans (div_le_div_of_nonneg_left zero_le_one (by positivity : (0 : ℝ) < ↑m₁ + 1)
      (by exact_mod_cast Nat.add_le_add_right h 1)) hω
  have h_level : ∀ m : ℕ,
      ν {ω : E → ℝ | (1 : ℝ) / (↑m + 1) ≤ S ω} ≤ ENNReal.ofReal ε_q := by
    intro m
    set δ := (1 : ℝ) / (↑m + 1)
    have hδ_pos : 0 < δ := by positivity
    have hA_ne_top : ν {ω | δ ≤ S ω} ≠ ⊤ :=
      ne_top_of_le_ne_top (measure_ne_top ν Set.univ) (measure_mono (Set.subset_univ _))
    rw [← ENNReal.ofReal_toReal hA_ne_top]; apply ENNReal.ofReal_le_ofReal
    have h_cheb : ∀ σ : ℝ, 0 < σ →
        (1 - Real.exp (-(σ ^ 2 * δ / 2))) * (ν {ω | δ ≤ S ω}).toReal ≤ ε_q := by
      intro σ hσ
      have h_int_σ := h_gauss_orig σ hσ
      set c_σ := 1 - Real.exp (-(σ ^ 2 * δ / 2))
      have hc_σ_nn : 0 ≤ c_σ := by
        simp only [c_σ]; linarith [Real.exp_le_one_iff.mpr (by nlinarith : -(σ ^ 2 * δ / 2) ≤ 0)]
      have h_nn : ∀ ω, 0 ≤ 1 - Real.exp (-(σ ^ 2 * (S ω) / 2)) := by
        intro ω
        have : S ω = ∑ i : Fin (n + 1), ω (z i) ^ 2 := rfl
        linarith [Real.exp_le_one_iff.mpr (show -(σ ^ 2 * (S ω) / 2) ≤ 0 by
          nlinarith [sq_nonneg σ, Finset.sum_nonneg
            (fun i (_ : i ∈ Finset.univ) => sq_nonneg (ω (z i)))])]
      have h_S_meas : Measurable S :=
        Finset.measurable_sum _ (fun i _ => (measurable_pi_apply (z i)).pow_const 2)
      have h_exp_int : Integrable (fun ω : E → ℝ => Real.exp (-(σ ^ 2 * (S ω) / 2))) ν := by
        apply (integrable_const (1 : ℝ)).mono'
        · exact ((measurable_const.mul h_S_meas |>.div_const 2 |>.neg).exp.aestronglyMeasurable)
        · filter_upwards with ω
          simp only [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
          exact Real.exp_le_one_iff.mpr (by
            nlinarith [sq_nonneg σ,
              Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => sq_nonneg (ω (z i)))])
      have h_f_int : Integrable (fun ω : E → ℝ => 1 - Real.exp (-(σ ^ 2 * (S ω) / 2))) ν :=
        (integrable_const 1).sub h_exp_int
      calc c_σ * (ν {ω | δ ≤ S ω}).toReal
          = ∫ _ in {ω | δ ≤ S ω}, c_σ ∂ν := by
            rw [setIntegral_const, measureReal_def, smul_eq_mul, mul_comm]
        _ ≤ ∫ ω in {ω | δ ≤ S ω}, (1 - Real.exp (-(σ ^ 2 * (S ω) / 2))) ∂ν := by
            apply setIntegral_mono_on (integrable_const _) h_f_int.integrableOn
              (measurableSet_le measurable_const h_S_meas)
              fun ω hω => by
                simp only [Set.mem_setOf_eq] at hω
                have : Real.exp (-(σ ^ 2 * (S ω) / 2)) ≤ Real.exp (-(σ ^ 2 * δ / 2)) :=
                  Real.exp_le_exp_of_le (by nlinarith [sq_nonneg σ])
                linarith
        _ ≤ ∫ ω, (1 - Real.exp (-(σ ^ 2 * (S ω) / 2))) ∂ν :=
            setIntegral_le_integral h_f_int (Filter.Eventually.of_forall h_nn)
        _ ≤ ε_q := h_int_σ
    apply le_of_forall_pos_lt_add
    intro η hη
    set target := Real.log ((ε_q + η) / η) with h_target
    have h_target_pos : 0 < target := by
      rw [h_target]; exact Real.log_pos (by rw [lt_div_iff₀ hη]; linarith)
    set σ₀ := Real.sqrt (2 * target / δ + 1)
    have hσ₀_pos : 0 < σ₀ := Real.sqrt_pos_of_pos (by positivity)
    have hσ₀_sq : σ₀ ^ 2 = 2 * target / δ + 1 := by
      simp only [σ₀, sq]
      exact Real.mul_self_sqrt (by positivity : (0 : ℝ) ≤ 2 * target / δ + 1)
    have h_exp_small : Real.exp (-(σ₀ ^ 2 * δ / 2)) < η / (ε_q + η) := by
      rw [hσ₀_sq]
      have h_neg_eq : -((2 * target / δ + 1) * δ / 2) = -(target + δ / 2) := by
        field_simp
      rw [h_neg_eq]
      have h_ratio_pos : (0 : ℝ) < η / (ε_q + η) := by positivity
      rw [← Real.lt_log_iff_exp_lt h_ratio_pos]
      have h_log_ratio : Real.log (η / (ε_q + η)) = -target := by
        rw [Real.log_div (by linarith) (by linarith : ε_q + η ≠ 0)]
        have : Real.log (ε_q + η) - Real.log η = target := by
          rw [← Real.log_div (by linarith) (by linarith : η ≠ 0), h_target]
        linarith
      linarith [h_log_ratio]
    have h_bound := h_cheb σ₀ hσ₀_pos
    have h_sum_one : ε_q / (ε_q + η) + η / (ε_q + η) = 1 := by field_simp
    have h_c_lb : ε_q / (ε_q + η) < 1 - Real.exp (-(σ₀ ^ 2 * δ / 2)) := by linarith
    have h_c_pos : 0 < 1 - Real.exp (-(σ₀ ^ 2 * δ / 2)) :=
      lt_trans (by positivity : (0 : ℝ) < ε_q / (ε_q + η)) h_c_lb
    calc (ν {ω | δ ≤ S ω}).toReal
        ≤ ε_q / (1 - Real.exp (-(σ₀ ^ 2 * δ / 2))) := by
          rwa [le_div_iff₀ h_c_pos, mul_comm]
      _ < ε_q / (ε_q / (ε_q + η)) := by
          apply div_lt_div_of_pos_left hε_q (by positivity) h_c_lb
      _ = ε_q + η := by field_simp
  rw [h_bad_eq, h_union]
  exact le_of_tendsto' (tendsto_measure_iUnion_atTop h_mono) h_level

private lemma kernel_concentration_bound
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (Φ : E → ℂ) (ν : Measure (E → ℝ)) [IsProbabilityMeasure ν]
    (h_cf_joint : ∀ (n : ℕ) (s : Fin n → ℝ) (x : Fin n → E),
      ∫ ω : E → ℝ, exp (I * ↑(∑ i, s i * ω (x i))) ∂ν =
        Φ (∑ i, s i • x i))
    (h_normalized : Φ 0 = 1)
    (p_m : Seminorm ℝ E)
    (ε_q : ℝ) (hε_q : 0 < ε_q)
    (h_kernel_bound : ∀ x : E, p_m x = 0 → ∀ t : ℝ, 1 - (Φ (t • x)).re ≤ ε_q)
    (d : ℕ → E) (N : ℕ)
    {k : ℕ} (e : Fin k → E)
    (α_map : (ℕ →₀ ℚ) → Fin k → ℝ)
    (h_ker_decomp : ∀ c : ℕ →₀ ℚ, c.support ⊆ Finset.range N →
      p_m (c.sum (fun i a => (a : ℝ) • d i) - ∑ j, α_map c j • e j) = 0) :
    ν {ω : E → ℝ | ∃ c : ℕ →₀ ℚ, c.support ⊆ Finset.range N ∧
      ω (c.sum (fun i a => (a : ℝ) • d i)) ≠
        ∑ j : Fin k, α_map c j * ω (e j)} ≤
      ENNReal.ofReal ε_q := by
  -- Define kernel elements z_c for each c
  let z (c : ℕ →₀ ℚ) : E := c.sum (fun i a => (a : ℝ) • d i) - ∑ j, α_map c j • e j
  -- Step 1: Linearity gives ω(z_c) = ω(x_c) - ∑ α_j ω(e_j) a.e.
  -- So {ω(x_c) ≠ ∑ α_j ω(e_j)} = {ω(z_c) ≠ 0} up to null set
  -- (using linear_combination_ae for each c)
  -- Step 2: For finite sets S of c's, ∑ t_c z_c ∈ ker(p_m)
  have h_kernel_sum : ∀ (n : ℕ) (c_list : Fin n → ℕ →₀ ℚ)
      (h_supp : ∀ i, (c_list i).support ⊆ Finset.range N)
      (t : Fin n → ℝ),
      p_m (∑ i, t i • z (c_list i)) = 0 := by
    intro n c_list h_supp t
    apply le_antisymm _ (apply_nonneg _ _)
    have h_each : ∀ i, p_m (z (c_list i)) = 0 := fun i => h_ker_decomp _ (h_supp i)
    -- Each t_i • z(c_i) ∈ ker(p_m), and ker(p_m) is closed under sums
    -- because p_m is a seminorm.
    suffices h : ∀ (S : Finset (Fin n)),
        p_m (∑ i ∈ S, t i • z (c_list i)) = 0 by
      linarith [h Finset.univ, apply_nonneg p_m (∑ i, t i • z (c_list i))]
    intro S
    induction S using Finset.induction with
    | empty => simp [map_zero]
    | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      have hv : p_m (t a • z (c_list a)) = 0 := by
        rw [map_smul_eq_mul, h_each, mul_zero]
      linarith [map_add_le_add p_m (t a • z (c_list a))
        (∑ x ∈ s, t x • z (c_list x)), apply_nonneg p_m
        (t a • z (c_list a) + ∑ x ∈ s, t x • z (c_list x))]
  -- Step 3: Joint CF bound: 1 - Re(Φ(∑ t_i z_i)) ≤ ε_q
  have h_joint_cf : ∀ (n : ℕ) (c_list : Fin n → ℕ →₀ ℚ)
      (h_supp : ∀ i, (c_list i).support ⊆ Finset.range N)
      (t : Fin n → ℝ),
      1 - (Φ (∑ i, t i • z (c_list i))).re ≤ ε_q := by
    intro n c_list h_supp t
    have h_ker := h_kernel_sum n c_list h_supp t
    have h_bound := h_kernel_bound _ h_ker 1
    rwa [one_smul] at h_bound
  -- Step 4: Linearity a.e.: for each c, ω(z_c) = ω(x_c) - ∑ α_j ω(e_j) a.e.
  -- The bad set ⊆ {∃ c, ω(z_c) ≠ 0} ∪ {linearity fails}
  -- where ν({linearity fails}) = 0.
  -- Define x_c for readability
  let x_c (c : ℕ →₀ ℚ) : E := c.sum (fun i a => (a : ℝ) • d i)
  -- Step 4a: For each c, linearity holds a.e.
  have h_lin_ae : ∀ c : ℕ →₀ ℚ, c.support ⊆ Finset.range N →
      ∀ᵐ ω ∂ν, ω (x_c c) = ω (z c) + ∑ j, α_map c j * ω (e j) := by
    intro c hc
    -- z_c = x_c - ∑ α_j e_j, so x_c = z_c + ∑ α_j e_j
    -- Use linear_combination_ae with (z_c, e_1,...,e_k) and coefficients (1, α_1,...,α_k)
    let e' : Fin (k + 1) → E := Fin.cons (z c) e
    let β' : Fin (k + 1) → ℝ := Fin.cons 1 (α_map c)
    have h_sum_eq : ∑ j : Fin (k + 1), β' j • e' j = x_c c := by
      rw [Fin.sum_univ_succ]
      simp only [e', β', Fin.cons_zero, Fin.cons_succ, one_smul]
      exact sub_add_cancel _ _
    have h_lin := linear_combination_ae Φ ν h_cf_joint h_normalized e' β'
    filter_upwards [h_lin] with ω hω
    rw [h_sum_eq] at hω
    rw [hω, Fin.sum_univ_succ]
    simp [e', β', Fin.cons_zero, Fin.cons_succ, one_mul]
  -- Step 4b: The bad set is contained in {∃ c, ω(z_c) ≠ 0} ∪ linearity_null
  set bad_set := {ω : E → ℝ | ∃ c : ℕ →₀ ℚ, c.support ⊆ Finset.range N ∧
    ω (x_c c) ≠ ∑ j : Fin k, α_map c j * ω (e j)}
  set z_bad := {ω : E → ℝ | ∃ c : ℕ →₀ ℚ, c.support ⊆ Finset.range N ∧ ω (z c) ≠ 0}
  -- Linearity holds a.e. for all c simultaneously (countable intersection)
  have h_lin_all : ∀ᵐ ω ∂ν, ∀ c : ℕ →₀ ℚ, c.support ⊆ Finset.range N →
      ω (x_c c) = ω (z c) + ∑ j, α_map c j * ω (e j) := by
    rw [eventually_countable_forall]
    intro c
    by_cases hc : c.support ⊆ Finset.range N
    · filter_upwards [h_lin_ae c hc] with ω hω _
      exact hω
    · filter_upwards with ω hc'
      exact absurd hc' hc
  have h_sub : bad_set ⊆ z_bad ∪ {ω | ¬∀ c : ℕ →₀ ℚ, c.support ⊆ Finset.range N →
      ω (x_c c) = ω (z c) + ∑ j, α_map c j * ω (e j)} := by
    intro ω hω
    by_cases h_all : ∀ c : ℕ →₀ ℚ, c.support ⊆ Finset.range N →
        ω (x_c c) = ω (z c) + ∑ j, α_map c j * ω (e j)
    · left
      obtain ⟨c, hc_supp, hc_bad⟩ := hω
      refine ⟨c, hc_supp, ?_⟩
      rw [h_all c hc_supp] at hc_bad
      intro hz; apply hc_bad; linarith
    · right; exact h_all
  have h_null : ν {ω | ¬∀ c : ℕ →₀ ℚ, c.support ⊆ Finset.range N →
      ω (x_c c) = ω (z c) + ∑ j, α_map c j * ω (e j)} = 0 :=
    ae_iff.mp h_lin_all
  -- Step 5: Bound ν(z_bad) using joint_kernel_bound_finite
  -- z_bad = {∃ c, c.support ⊆ range N ∧ ω(z_c) ≠ 0}
  -- = ⋃_{finite S} {∃ c ∈ S, c.support ⊆ range N ∧ ω(z_c) ≠ 0}
  -- For each finite S, joint_kernel_bound_finite gives ν ≤ ofReal ε_q
  -- By continuity from below, ν(z_bad) ≤ ofReal ε_q
  -- Step 5: joint_kernel_bound_finite establishes ν(z_bad) ≤ ofReal ε_q
  have h_z_bad_bound : ν z_bad ≤ ENNReal.ofReal ε_q := by
    -- z_bad = {ω | ∃ c, c.support ⊆ range N ∧ ω(z c) ≠ 0}
    -- Enumerate all (ℕ →₀ ℚ) elements: this type is countable
    -- For any finite list of kernel elements, joint_kernel_bound_finite gives ε_q
    -- Write z_bad = ⋃_c {ω(z c) ≠ 0}, a countable union (restricted to supp ⊆ range N)
    -- Use tendsto_measure_iUnion via an enumeration
    -- Since ℕ →₀ ℚ is countable, enumerate as f : ℕ → (ℕ →₀ ℚ)
    haveI : Countable (ℕ →₀ ℚ) := inferInstance
    -- Define the sets for finite prefixes
    -- For M, consider the first M elements of the enumeration
    -- The monotone sequence {∃ c ∈ {f(0),...,f(M-1)}, ...} increases to z_bad
    -- Apply joint_kernel_bound_finite for each M
    -- For each M, filter to those f(i) with support ⊆ range N
    -- The joint bound uses the z(f(i)) as the kernel elements
    -- This is straightforward but requires some bookkeeping
    -- Use the fact that for a countable union of measurable sets,
    -- if every finite sub-union has measure ≤ δ, then the full union has measure ≤ δ
    -- (This is le_of_tendsto' + tendsto_measure_iUnion)
    -- The key: for any finite set S of c's with support in range N,
    -- ν{∃ c ∈ S, ω(z c) ≠ 0} ≤ ofReal ε_q
    have h_finite_bound : ∀ (n : ℕ) (c_list : Fin n → ℕ →₀ ℚ),
        (∀ i, (c_list i).support ⊆ Finset.range N) →
        ν {ω | ∃ i : Fin n, ω (z (c_list i)) ≠ 0} ≤ ENNReal.ofReal ε_q := by
      intro n c_list h_supp
      exact joint_kernel_bound_finite Φ ν h_cf_joint h_normalized ε_q hε_q n
        (fun i => z (c_list i))
        (fun t => h_joint_cf n c_list h_supp t)
    -- z_bad ⊆ {∃ c, ω(z c) ≠ 0} (we can drop the support condition since
    -- z(c) for c outside range N is not constrained, but z_bad already restricts)
    -- For each c in z_bad, we have c.support ⊆ range N, so z(c) ∈ ker(p_m)
    -- Enumerate ℕ →₀ ℚ
    haveI : Nonempty (ℕ →₀ ℚ) := ⟨0⟩
    obtain ⟨f, hf_surj⟩ := exists_surjective_nat (ℕ →₀ ℚ)
    -- Define increasing sets S_M
    let S (M : ℕ) : Set (E → ℝ) := {ω | ∃ i : Fin M,
      (f i).support ⊆ Finset.range N ∧ ω (z (f i)) ≠ 0}
    -- S is monotone
    have h_mono : Monotone S := by
      intro M₁ M₂ hle ω ⟨⟨i, hi⟩, hsupp, hne⟩
      exact ⟨⟨i, Nat.lt_of_lt_of_le hi hle⟩, hsupp, hne⟩
    -- z_bad = ⋃_M S_M
    have h_union : z_bad = ⋃ M, S M := by
      ext ω
      simp only [z_bad, S, Set.mem_setOf_eq, Set.mem_iUnion]
      constructor
      · rintro ⟨c, hsupp, hne⟩
        obtain ⟨i, rfl⟩ := hf_surj c
        exact ⟨i + 1, ⟨i, Nat.lt_succ_iff.mpr le_rfl⟩, hsupp, hne⟩
      · rintro ⟨M, ⟨i, _⟩, hsupp, hne⟩
        exact ⟨f i, hsupp, hne⟩
    -- Each S M has measure ≤ ofReal ε_q
    have h_S_bound : ∀ M, ν (S M) ≤ ENNReal.ofReal ε_q := by
      intro M
      -- Collect those i < M where f(i).support ⊆ range N
      let good : Finset (Fin M) :=
        Finset.univ.filter (fun i => (f i).support ⊆ Finset.range N)
      -- S M = {∃ i ∈ good, ω(z(f i)) ≠ 0}
      have h_S_eq : S M = {ω | ∃ i ∈ good, ω (z (f i)) ≠ 0} := by
        ext ω
        simp only [S, good, Set.mem_setOf_eq, Finset.mem_filter, Finset.mem_univ,
          true_and]
      rw [h_S_eq]
      -- Now apply h_finite_bound with the filtered list
      let n := good.card
      let c_list : Fin n → ℕ →₀ ℚ := fun j => f (good.equivFin.symm j)
      have h_c_supp : ∀ j, (c_list j).support ⊆ Finset.range N := by
        intro j
        simpa only [good, Finset.mem_filter, Finset.mem_univ, true_and]
          using (good.equivFin.symm j).2
      -- {∃ i ∈ good, ω(z(f i)) ≠ 0} = {∃ j : Fin n, ω(z(c_list j)) ≠ 0}
      have h_set_eq : {ω : E → ℝ | ∃ i ∈ good, ω (z (f i)) ≠ 0} =
          {ω | ∃ j : Fin n, ω (z (c_list j)) ≠ 0} := by
        ext ω
        simp only [Set.mem_setOf_eq, c_list]
        constructor
        · rintro ⟨i, hi, hne⟩
          exact ⟨good.equivFin ⟨i, hi⟩, by rwa [Equiv.symm_apply_apply]⟩
        · rintro ⟨j, hne⟩
          exact ⟨good.equivFin.symm j, (good.equivFin.symm j).2,
            by rwa [show f (good.equivFin.symm j) = c_list j from rfl]⟩
      rw [h_set_eq]
      exact h_finite_bound n c_list h_c_supp
    rw [h_union]
    exact le_of_tendsto' (tendsto_measure_iUnion_atTop h_mono) h_S_bound
  -- Step 6: Combine
  calc ν bad_set
      ≤ ν (z_bad ∪ {ω | ¬∀ c, c.support ⊆ Finset.range N →
          ω (x_c c) = ω (z c) + ∑ j, α_map c j * ω (e j)}) := measure_mono h_sub
    _ ≤ ν z_bad + ν {ω | ¬∀ c, c.support ⊆ Finset.range N →
          ω (x_c c) = ω (z c) + ∑ j, α_map c j * ω (e j)} := measure_union_le _ _
    _ = ν z_bad + 0 := by rw [h_null]
    _ = ν z_bad := add_zero _
    _ ≤ ENNReal.ofReal ε_q := h_z_bad_bound

/-! ### Tail bound for evaluation on ONB (key step) -/

private lemma gaussian_charFun_quad_average_bound
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    (μ' : ProbabilityMeasure V) (σ ε_q K C_HS : ℝ) (hσ : 0 < σ)
    (hK : 0 ≤ K) (hC_HS : 0 ≤ C_HS) (S : V →L[ℝ] V) (hS_pos : S.IsPositive)
    (hpw : ∀ x : V, 1 - (charFun μ'.toMeasure x).re ≤ ε_q + K * quadForm S x)
    (h_trace : ∀ (ι : Type*) [Fintype ι] (b : OrthonormalBasis ι ℝ V),
      ∑ i, @inner ℝ V _ (b i) (S (b i)) ≤ C_HS) :
    ∫ y, (1 - Real.exp (-(σ ^ 2 * ‖y‖ ^ 2 / 2))) ∂μ'.toMeasure ≤
      ε_q + K * σ ^ 2 * C_HS := by
  rw [fubini_gaussian_charFun μ' (charFun μ'.toMeasure) (fun _ => rfl) σ hσ]
  set C := ∫ x : V, gaussDensity σ x
  have hC_pos : 0 < C := gaussDensity_integral_pos' (V := V) σ hσ
  have hCinv_nn : 0 ≤ C⁻¹ := inv_nonneg.mpr hC_pos.le
  have hgqf_int : Integrable (fun x => gaussDensity σ x * quadForm S x) volume :=
    gaussDensity_mul_quadForm_integrable' (V := V) σ hσ S
  have hg_int := gaussDensity_integrable' (V := V) σ hσ
  have hprod_int : Integrable (fun x => gaussDensity σ x *
      (1 - (charFun μ'.toMeasure x).re)) volume := by
    have h1 := gaussDensity_mul_charFun_re_integrable' μ' _ (fun _ => rfl) σ hσ
    exact hg_int.sub h1 |>.congr
      (Filter.Eventually.of_forall fun x => by simp [Pi.sub_apply]; ring)
  have hprod2_int : Integrable (fun x => gaussDensity σ x *
      (ε_q + K * quadForm S x)) volume := by
    have : (fun x => gaussDensity σ x * (ε_q + K * quadForm S x)) =
        (fun x => ε_q * gaussDensity σ x + K * (gaussDensity σ x * quadForm S x)) := by
      ext x; ring
    rw [this]; exact (hg_int.const_mul ε_q).add (hgqf_int.const_mul K)
  calc C⁻¹ * ∫ x : V, gaussDensity σ x * (1 - (charFun μ'.toMeasure x).re)
      ≤ C⁻¹ * ∫ x : V, gaussDensity σ x * (ε_q + K * quadForm S x) := by
        apply mul_le_mul_of_nonneg_left _ hCinv_nn
        exact integral_mono hprod_int hprod2_int fun x =>
          mul_le_mul_of_nonneg_left (hpw x) (gaussDensity_nonneg' σ x)
    _ = ε_q + K * (C⁻¹ * ∫ x : V, gaussDensity σ x * quadForm S x) := by
        rw [show (fun x => gaussDensity σ x * (ε_q + K * quadForm S x)) =
          (fun x => ε_q * gaussDensity σ x + K * (gaussDensity σ x * quadForm S x))
          from by ext x; ring]
        rw [integral_add (hg_int.const_mul ε_q) (hgqf_int.const_mul K),
          integral_const_mul, integral_const_mul, mul_add]
        congr 1
        · rw [mul_comm C⁻¹ (ε_q * C), mul_assoc, mul_inv_cancel₀ (ne_of_gt hC_pos),
            mul_one]
        · ring
    _ ≤ ε_q + K * (σ ^ 2 * C_HS) := by
        have h_gq := gaussian_quadForm_integral_le (V := V) σ hσ S hS_pos C_HS hC_HS
          h_trace
        have : K * (C⁻¹ * ∫ x : V, gaussDensity σ x * quadForm S x) ≤
            K * (σ ^ 2 * C_HS) :=
          mul_le_mul_of_nonneg_left h_gq hK
        linarith
    _ = ε_q + K * σ ^ 2 * C_HS := by ring

private lemma tail_bound_uniform_gaussian_average
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (Φ : E → ℂ) (ν : Measure (E → ℝ)) [IsProbabilityMeasure ν]
    (h_cf_joint : ∀ (n : ℕ) (s : Fin n → ℝ) (x : Fin n → E),
      ∫ ω : E → ℝ, exp (I * ↑(∑ i, s i * ω (x i))) ∂ν =
        Φ (∑ i, s i • x i))
    (p_inner : Seminorm ℝ E) (hp_inner : p_inner.IsHilbertian)
    (ε_q K : ℝ) (hK : 0 ≤ K)
    (hε_q : 0 < ε_q)
    (h_quad : ∀ x : E, 1 - (Φ x).re ≤ ε_q + K * p_inner x ^ 2)
    (C_HS : ℝ) (hC_HS : 0 ≤ C_HS)
    (p_outer : Seminorm ℝ E)
    (h_HS : ∀ (n : ℕ) (e : Fin n → E),
      p_outer.IsOrthonormalSeq e → ∑ i, p_inner (e i) ^ 2 ≤ C_HS)
    (σ : ℝ) (hσ : 0 < σ) (k : ℕ) (e : Fin k → E)
    (he : p_outer.IsOrthonormalSeq e) :
    ∫ ω, (1 - Real.exp (-(σ ^ 2 * (∑ i, ω (e i) ^ 2) / 2))) ∂ν ≤
      ε_q + K * σ ^ 2 * C_HS := by
  rcases k with _ | k
  · simp [Finset.sum_empty, Real.exp_zero]
    linarith [hε_q, mul_nonneg (mul_nonneg hK (sq_nonneg σ)) hC_HS]
  set V := EuclideanSpace ℝ (Fin (k + 1)) with hV_def
  let toLp := MeasurableEquiv.toLp (p := 2) (X := Fin (k + 1) → ℝ)
  let eval_e : (E → ℝ) → V := fun ω => toLp (fun j => ω (e j))
  have h_meas_e : Measurable eval_e :=
    toLp.measurable.comp (measurable_pi_lambda _ (fun j => measurable_pi_apply (e j)))
  let μ := ν.map eval_e
  haveI h_prob : IsProbabilityMeasure μ :=
    Measure.isProbabilityMeasure_map h_meas_e.aemeasurable
  let μ' : ProbabilityMeasure V := ⟨μ, h_prob⟩
  have h_coord : ∀ (ω : E → ℝ) (i : Fin (k + 1)), (eval_e ω) i = ω (e i) := fun _ _ => rfl
  have h_inner_V : ∀ (ω : E → ℝ) (v : V),
      @inner ℝ V _ (eval_e ω) v = ∑ j, v j * ω (e j) := by
    intro ω v; erw [PiLp.inner_apply]
    simp only [real_inner_eq_mul, h_coord]
  have h_cf : ∀ v : V, charFun μ'.toMeasure v = Φ (∑ i, v i • e i) := by
    intro v; rw [charFun_apply]
    change ∫ y : V, cexp (@inner ℝ V _ y v * I) ∂(ν.map eval_e) = Φ (∑ i, v i • e i)
    rw [integral_map h_meas_e.aemeasurable (by fun_prop)]
    simp_rw [h_inner_V, show ∀ ω : E → ℝ,
      cexp (↑(∑ j, v j * ω (e j)) * I) = cexp (I * ↑(∑ j, v j * ω (e j)))
      from fun _ => by congr 1; ring]
    exact h_cf_joint (k + 1) (fun j => v j) e
  let Mij : Fin (k + 1) → Fin (k + 1) → ℝ := fun j l => p_inner.innerProd (e j) (e l)
  let S_fun : V → V := fun v => toLp (fun j => ∑ l, Mij j l * v l)
  have hS_coord : ∀ (v : V) (j : Fin (k + 1)),
      (S_fun v) j = ∑ l, Mij j l * v l := fun _ _ => rfl
  have hS_coord' : ∀ (v : V) (j : Fin (k + 1)),
      (S_fun v).ofLp j = ∑ l, Mij j l * v.ofLp l := fun u j => hS_coord u j
  have hS_add : ∀ v w : V, S_fun (v + w) = S_fun v + S_fun w := by
    intro v w; apply PiLp.ext; intro j
    change ∑ l, Mij j l * ((v + w : V) : Fin _ → ℝ) l =
      ((∑ l, Mij j l * (v : Fin _ → ℝ) l) + (∑ l, Mij j l * (w : Fin _ → ℝ) l))
    rw [show ((v + w : V) : Fin _ → ℝ) = (v : Fin _ → ℝ) + (w : Fin _ → ℝ) from rfl]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun l _ => by simp [Pi.add_apply]; ring
  have hS_smul : ∀ (c : ℝ) (v : V), S_fun (c • v) = c • S_fun v := by
    intro c v; apply PiLp.ext; intro j
    change ∑ l, Mij j l * ((c • v : V) : Fin _ → ℝ) l =
      c * (∑ l, Mij j l * (v : Fin _ → ℝ) l)
    rw [show ((c • v : V) : Fin _ → ℝ) = c • (v : Fin _ → ℝ) from rfl]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by simp [Pi.smul_apply, smul_eq_mul]; ring
  let S_lm : V →ₗ[ℝ] V := {
    toFun := S_fun
    map_add' := hS_add
    map_smul' := hS_smul }
  let S : V →L[ℝ] V := LinearMap.toContinuousLinearMap S_lm
  have h_qf : ∀ v : V, quadForm S v = p_inner (∑ i, v i • e i) ^ 2 := by
    intro v
    change @inner ℝ V _ v (S_fun v) = _
    erw [PiLp.inner_apply]
    simp_rw [real_inner_eq_mul, hS_coord', Finset.sum_mul]
    rw [← Seminorm.innerProd_self p_inner, p_inner.innerProd_sum_left hp_inner]
    simp_rw [gs_innerProd_sum_right p_inner hp_inner,
      p_inner.innerProd_smul_left hp_inner, gs_innerProd_smul_right p_inner hp_inner]
    congr 1; ext j; congr 1; ext l; ring
  have hS_pos : S.IsPositive := by
    refine ⟨fun v w => ?_, fun v => ?_⟩
    · change @inner ℝ V _ (S_fun v) w = @inner ℝ V _ v (S_fun w)
      have h_expand_inner : ∀ (a b : V),
          @inner ℝ V _ (S_fun a) b = ∑ j, ∑ l, Mij j l * a l * b j := by
        intro a b; erw [PiLp.inner_apply]
        simp_rw [real_inner_eq_mul, hS_coord', Finset.mul_sum]
        congr 1; ext j; congr 1; ext l; ring
      rw [h_expand_inner]
      rw [show @inner ℝ V _ v (S_fun w) = @inner ℝ V _ (S_fun w) v from
        (real_inner_comm v (S_fun w)).symm]
      rw [h_expand_inner]
      rw [Finset.sum_comm (f := fun j l => Mij j l * w l * v j)]
      congr 1; ext j; congr 1; ext l
      have : Mij l j = Mij j l := (Seminorm.innerProd_comm p_inner _ _).symm
      rw [this]; ring
    · have : 0 ≤ quadForm S v := by rw [h_qf]; positivity
      simp only [quadForm] at this ⊢
      rwa [real_inner_comm] at this
  have h_trace : ∀ (ι : Type) [Fintype ι] (b : OrthonormalBasis ι ℝ V),
      ∑ i, @inner ℝ V _ (b i) (S (b i)) ≤ C_HS := by
    intro ι _ b
    have hqf_b : ∀ i, @inner ℝ V _ (b i) (S (b i)) =
        p_inner (∑ j, (b i) j • e j) ^ 2 := by
      intro i; exact h_qf (b i)
    simp_rw [hqf_b]
    have h_expand : ∀ i, p_inner (∑ j, (b i) j • e j) ^ 2 =
        ∑ j, ∑ l, (b i) j * (b i) l * Mij j l := by
      intro i
      rw [← Seminorm.innerProd_self p_inner, p_inner.innerProd_sum_left hp_inner]
      simp_rw [gs_innerProd_sum_right p_inner hp_inner,
        p_inner.innerProd_smul_left hp_inner, gs_innerProd_smul_right p_inner hp_inner]
      congr 1; ext j; congr 1; ext l; ring
    simp_rw [h_expand]
    rw [Finset.sum_comm]
    conv_lhs => arg 2; ext j; rw [Finset.sum_comm]
    simp_rw [show ∀ (j l : Fin (k+1)) (i : ι),
      (b i) j * (b i) l * Mij j l = Mij j l * ((b i) j * (b i) l) from
      fun _ _ _ => by ring]
    simp_rw [← Finset.mul_sum]
    have h_parseval : ∀ (j l : Fin (k + 1)),
        ∑ i, (b i) j * (b i) l = if j = l then 1 else 0 := by
      intro j l
      have key := b.sum_inner_mul_inner
        (EuclideanSpace.single j (1 : ℝ)) (EuclideanSpace.single l 1)
      have h_single_left : ∀ (v : V),
          @inner ℝ V _ (EuclideanSpace.single j 1) v = v j := by
        intro v; erw [PiLp.inner_apply]
        simp only [real_inner_eq_mul]
        simp [PiLp.single_apply]
      have h_single_right : ∀ (v : V),
          @inner ℝ V _ v (EuclideanSpace.single l 1) = v l := by
        intro v; erw [PiLp.inner_apply]
        simp only [real_inner_eq_mul]
        simp [PiLp.single_apply]
      simp only [h_single_left, h_single_right, PiLp.single_apply] at key
      exact key.symm.symm
    suffices h_suff : ∑ j, Mij j j ≤ C_HS by
      apply le_trans _ h_suff
      apply le_of_eq
      apply Finset.sum_congr rfl; intro j _
      have h_collapse_j : ∀ l, Mij j l * (∑ i, (b i) j * (b i) l) =
          if j = l then Mij j l else 0 := by
        intro l; rw [h_parseval j l]; split_ifs <;> simp [*]
      simp only [h_collapse_j]
      simp
    simp_rw [show ∀ j : Fin (k + 1), Mij j j = p_inner (e j) ^ 2 from
      fun j => Seminorm.innerProd_self p_inner (e j)]
    exact h_HS (k + 1) e he
  have h_norm_sq : ∀ ω : E → ℝ, ‖eval_e ω‖ ^ 2 = ∑ i, ω (e i) ^ 2 := by
    intro ω
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
    congr 1; ext i; simp [h_coord]
  have hpw : ∀ x : V, 1 - (charFun μ'.toMeasure x).re ≤ ε_q + K * quadForm S x := by
    intro x; rw [h_cf, h_qf]; exact h_quad _
  have h_gauss_V := gaussian_charFun_quad_average_bound μ' σ ε_q K C_HS hσ hK
    hC_HS S hS_pos hpw h_trace
  rw [show μ'.toMeasure = ν.map eval_e from rfl] at h_gauss_V
  rw [integral_map h_meas_e.aemeasurable] at h_gauss_V
  · convert h_gauss_V using 1; congr 1; ext ω; congr 2; rw [h_norm_sq]
  · exact (continuous_const.sub (by fun_prop :
      Continuous (fun y : V => Real.exp (-(σ ^ 2 * ‖y‖ ^ 2 / 2))))).aestronglyMeasurable

/-- Tail probability `ν{∑ ω(eⱼ)² > R²}` can be made arbitrarily small by choosing
    R large. The bound is UNIFORM in the dimension k of the ONB.

    Uses Gaussian averaging on the pushforward measure to ℝ^k:
    `𝔼[1 - exp(-σ²∑ω(eⱼ)²/2)] ≤ ε_q + 2σ²K·C_HS`
    Combined with the exponential Chebyshev bound `P(‖Y‖ ≥ R) ≤ C/(1-exp(-σ²R²/2))`,
    choose σ, R to make the tail probability ≤ δ.
-/
private lemma tail_bound_uniform
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (Φ : E → ℂ) (ν : Measure (E → ℝ)) [IsProbabilityMeasure ν]
    (h_cf_joint : ∀ (n : ℕ) (s : Fin n → ℝ) (x : Fin n → E),
      ∫ ω : E → ℝ, exp (I * ↑(∑ i, s i * ω (x i))) ∂ν =
        Φ (∑ i, s i • x i))
    (_h_norm_le : ∀ x : E, ‖Φ x‖ ≤ 1)
    (p_inner : Seminorm ℝ E) (hp_inner : p_inner.IsHilbertian)
    (ε_q K : ℝ) (hε_q : 0 < ε_q) (hK : 0 ≤ K)
    (h_quad : ∀ x : E, 1 - (Φ x).re ≤ ε_q + K * p_inner x ^ 2)
    (C_HS : ℝ) (hC_HS : 0 ≤ C_HS)
    (δ : ℝ) (hδ : 0 < δ) (hε_q_lt_δ : ε_q < δ)
    (p_outer : Seminorm ℝ E)
    (h_HS : ∀ (n : ℕ) (e : Fin n → E),
      p_outer.IsOrthonormalSeq e → ∑ i, p_inner (e i) ^ 2 ≤ C_HS) :
    ∃ (R : ℝ), 0 < R ∧ ∀ (k : ℕ) (e : Fin k → E),
      p_outer.IsOrthonormalSeq e →
      ν {ω : E → ℝ | R ^ 2 < ∑ j : Fin k, (ω (e j)) ^ 2} ≤ ENNReal.ofReal δ := by
  -- Strategy: Since ε_q < δ, choose σ > 0 small so that ε_q + Kσ²C_HS < δ.
  -- For each k and ONB e, pushforward to V := EuclideanSpace ℝ (Fin k),
  -- construct Gram matrix S with quadForm(S,v) = p_inner(∑vⱼeⱼ)² and Tr(S) ≤ C_HS.
  -- Gaussian averaging: E[1-exp(-σ²||Y||²/2)] ≤ ε_q + Kσ²C_HS (dimension-free).
  -- Chebyshev: P(||Y||²>R²) ≤ (ε_q + Kσ²C_HS)/(1-exp(-σ²R²/2)) ≤ δ for R large.
  -- Step 1: Gaussian averaging bound on ν for ANY k and ONB
  -- For any σ > 0, k, and p_outer-ONB e of size k:
  -- ∫ (1-exp(-σ²·∑ω(eⱼ)²/2)) dν ≤ ε_q + K·σ²·C_HS
  have h_gauss_ν := tail_bound_uniform_gaussian_average Φ ν h_cf_joint p_inner hp_inner
    ε_q K hK hε_q h_quad C_HS hC_HS p_outer h_HS
  -- Step 2: Choose σ and R (depending on ε_q, K, C_HS, δ, not on k)
  set gap := δ - ε_q
  have h_gap_pos : 0 < gap := by linarith
  set σ₀ : ℝ := if K * C_HS = 0 then 1 else Real.sqrt (gap / (2 * (K * C_HS)))
  have hσ₀_pos : 0 < σ₀ := by
    simp only [σ₀]; split_ifs with h
    · exact one_pos
    · apply Real.sqrt_pos_of_pos; positivity
  have h_bound_σ : ε_q + K * σ₀ ^ 2 * C_HS < δ := by
    simp only [σ₀]; split_ifs with h
    · have : K * 1 ^ 2 * C_HS = K * C_HS := by ring
      rw [this, h, add_zero]; exact hε_q_lt_δ
    · have hKC_pos : 0 < K * C_HS :=
        lt_of_le_of_ne (mul_nonneg hK hC_HS) (Ne.symm h)
      have hσ_sq : Real.sqrt (gap / (2 * (K * C_HS))) ^ 2 = gap / (2 * (K * C_HS)) :=
        Real.sq_sqrt (by positivity)
      calc ε_q + K * Real.sqrt (gap / (2 * (K * C_HS))) ^ 2 * C_HS
          = ε_q + K * C_HS * (gap / (2 * (K * C_HS))) := by rw [hσ_sq]; ring
        _ = ε_q + gap / 2 := by
            congr 1
            rw [show K * C_HS * (gap / (2 * (K * C_HS))) =
              gap * (K * C_HS) / (2 * (K * C_HS)) from by ring]
            rw [mul_div_mul_right gap 2 (ne_of_gt hKC_pos)]
        _ < δ := by simp only [gap]; linarith
  set bound_σ := ε_q + K * σ₀ ^ 2 * C_HS
  have h_bound_σ_pos : 0 < bound_σ := by positivity
  -- Choose R so that bound_σ / (1 - exp(-σ₀²R²/2)) ≤ δ
  set denom_target := 1 - bound_σ / δ
  have h_dt_pos : 0 < denom_target := by
    simp only [denom_target]; rw [sub_pos, div_lt_one hδ]; exact h_bound_σ
  have h_dt_le_one : denom_target ≤ 1 := by
    simp only [denom_target]; linarith [div_nonneg h_bound_σ_pos.le hδ.le]
  have hlog_nn : 0 ≤ -Real.log denom_target := by
    rw [neg_nonneg]; exact Real.log_nonpos h_dt_pos.le h_dt_le_one
  set R := Real.sqrt (2 * (-Real.log denom_target) / σ₀ ^ 2 + 1)
  have hR_pos : 0 < R := by
    apply Real.sqrt_pos_of_pos
    have : 0 ≤ 2 * (-Real.log denom_target) / σ₀ ^ 2 := by positivity
    linarith
  refine ⟨R, hR_pos, fun k e he => ?_⟩
  -- Step 3: For k = 0, the set is empty
  rcases k with _ | k
  · have : {ω : E → ℝ | R ^ 2 < ∑ j : Fin 0, (ω (e j)) ^ 2} = ∅ := by
      ext ω; simp [Finset.sum_empty, not_lt.mpr (sq_nonneg R)]
    rw [this, measure_empty]; exact bot_le
  -- Step 4: Chebyshev on ν
  -- From h_gauss_ν with σ₀: ∫(1-exp(-σ₀²·∑ω(eⱼ)²/2))dν ≤ bound_σ
  set T : (E → ℝ) → ℝ := fun ω => ∑ i : Fin (k + 1), ω (e i) ^ 2
  have hA_ne_top : ν {ω | R ^ 2 < T ω} ≠ ⊤ :=
    ne_top_of_le_ne_top (measure_ne_top ν Set.univ) (measure_mono (Set.subset_univ _))
  rw [← ENNReal.ofReal_toReal hA_ne_top]
  apply ENNReal.ofReal_le_ofReal
  have h_T_meas : Measurable T :=
    Finset.measurable_sum _ (fun i _ => (measurable_pi_apply (e i)).pow_const 2)
  -- Chebyshev: (1 - exp(-σ₀²R²/2)) · P(T > R²) ≤ bound_σ
  have h_cheb_σ₀ :
      (1 - Real.exp (-(σ₀ ^ 2 * R ^ 2 / 2))) * (ν {ω | R ^ 2 < T ω}).toReal ≤ bound_σ := by
    have h_int := h_gauss_ν σ₀ hσ₀_pos (k + 1) e he
    set c := 1 - Real.exp (-(σ₀ ^ 2 * R ^ 2 / 2))
    have hc_nn : 0 ≤ c := by
      simp only [c]; linarith [Real.exp_le_one_iff.mpr (by nlinarith : -(σ₀ ^ 2 * R ^ 2 / 2) ≤ 0)]
    have h_nn : ∀ ω : E → ℝ, 0 ≤ 1 - Real.exp (-(σ₀ ^ 2 * (T ω) / 2)) := by
      intro ω
      linarith [Real.exp_le_one_iff.mpr (show -(σ₀ ^ 2 * (T ω) / 2) ≤ 0 by
        nlinarith [sq_nonneg σ₀, Finset.sum_nonneg
          (fun i (_ : i ∈ Finset.univ) => sq_nonneg (ω (e i)))])]
    have h_exp_int : Integrable (fun ω : E → ℝ => Real.exp (-(σ₀ ^ 2 * (T ω) / 2))) ν := by
      apply (integrable_const (1 : ℝ)).mono'
      · exact ((measurable_const.mul h_T_meas |>.div_const 2 |>.neg).exp.aestronglyMeasurable)
      · filter_upwards with ω
        simp only [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
        exact Real.exp_le_one_iff.mpr (by
          nlinarith [sq_nonneg σ₀,
            Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => sq_nonneg (ω (e i)))])
    have h_f_int : Integrable (fun ω : E → ℝ => 1 - Real.exp (-(σ₀ ^ 2 * (T ω) / 2))) ν :=
      (integrable_const 1).sub h_exp_int
    calc c * (ν {ω | R ^ 2 < T ω}).toReal
        ≤ c * (ν {ω | R ^ 2 ≤ T ω}).toReal := by
          apply mul_le_mul_of_nonneg_left _ hc_nn
          exact ENNReal.toReal_mono (measure_ne_top ν _)
            (measure_mono (fun ω (hω : R ^ 2 < T ω) => le_of_lt hω))
      _ = ∫ _ in {ω | R ^ 2 ≤ T ω}, c ∂ν := by
          rw [setIntegral_const, measureReal_def, smul_eq_mul, mul_comm]
      _ ≤ ∫ ω in {ω | R ^ 2 ≤ T ω}, (1 - Real.exp (-(σ₀ ^ 2 * (T ω) / 2))) ∂ν := by
          apply setIntegral_mono_on (integrable_const _) h_f_int.integrableOn
            (measurableSet_le measurable_const h_T_meas)
            fun ω hω => by
              simp only [Set.mem_setOf_eq] at hω
              have : Real.exp (-(σ₀ ^ 2 * (T ω) / 2)) ≤ Real.exp (-(σ₀ ^ 2 * R ^ 2 / 2)) :=
                Real.exp_le_exp_of_le (by nlinarith [sq_nonneg σ₀])
              linarith
      _ ≤ ∫ ω, (1 - Real.exp (-(σ₀ ^ 2 * (T ω) / 2))) ∂ν :=
          setIntegral_le_integral h_f_int (Filter.Eventually.of_forall h_nn)
      _ ≤ bound_σ := h_int
  -- R choice ensures 1 - exp(-σ₀²R²/2) ≥ 1 - denom_target = bound_σ/δ
  have hR_sq : R ^ 2 = 2 * (-Real.log denom_target) / σ₀ ^ 2 + 1 := by
    simp only [R, sq]; exact Real.mul_self_sqrt (by positivity)
  have hσR_bound : σ₀ ^ 2 * R ^ 2 / 2 ≥ -Real.log denom_target := by
    rw [hR_sq]; have hσ₀_sq_pos : 0 < σ₀ ^ 2 := by positivity
    have h1 : σ₀ ^ 2 * (2 * (-Real.log denom_target) / σ₀ ^ 2 + 1) / 2 =
        -Real.log denom_target + σ₀ ^ 2 / 2 := by
      field_simp
    linarith [hσ₀_sq_pos]
  have h_exp_bound : Real.exp (-(σ₀ ^ 2 * R ^ 2 / 2)) ≤ denom_target := by
    rw [← Real.le_log_iff_exp_le h_dt_pos]; linarith [hσR_bound]
  have h_dt_lt_one : denom_target < 1 := by
    simp only [denom_target]; linarith [div_pos h_bound_σ_pos hδ]
  have h_denom_pos : 0 < 1 - Real.exp (-(σ₀ ^ 2 * R ^ 2 / 2)) := by
    linarith [h_exp_bound, h_dt_lt_one]
  have h_denom_bound : bound_σ / δ ≤ 1 - Real.exp (-(σ₀ ^ 2 * R ^ 2 / 2)) := by
    have : 1 - denom_target = bound_σ / δ := by simp only [denom_target]; ring
    linarith [h_exp_bound]
  calc (ν {ω | R ^ 2 < T ω}).toReal
      ≤ bound_σ / (1 - Real.exp (-(σ₀ ^ 2 * R ^ 2 / 2))) := by
        rw [le_div_iff₀ h_denom_pos, mul_comm]; exact h_cheb_σ₀
    _ ≤ bound_σ / (bound_σ / δ) := by
        apply div_le_div_of_nonneg_left h_bound_σ_pos.le (div_pos h_bound_σ_pos hδ) h_denom_bound
    _ = δ := by field_simp

/-! ### Restricted bad set bound with kernel contribution -/

/-- For each N, the restricted bad set B_N has measure bounded by the sum of:
    (a) the tail probability of the squared evaluation norm on a p-ONB, and
    (b) the kernel concentration probability.

    This is the version of `concentrationBadSetN_measure_bound` that does NOT require
    the CF kernel condition `Φ(t·z) = 1`, instead accounting for the kernel
    contribution via an additive probability bound.
-/
private lemma badSetN_bound_with_kernel
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (_Φ : E → ℂ) (ν : Measure (E → ℝ)) [IsProbabilityMeasure ν]
    (d : ℕ → E) (p_m : Seminorm ℝ E)
    {k : ℕ} (e : Fin k → E)
    (α_map : (ℕ →₀ ℚ) → Fin k → ℝ)
    (R : ℝ) (hR : 0 < R) (N : ℕ)
    (h_parseval : ∀ c : ℕ →₀ ℚ, c.support ⊆ Finset.range N →
      p_m (c.sum (fun i a => (a : ℝ) • d i)) ^ 2 = ∑ j, α_map c j ^ 2)
    (ε_ker : ENNReal)
    (h_ker : ν {ω : E → ℝ | ∃ c : ℕ →₀ ℚ, c.support ⊆ Finset.range N ∧
      ω (c.sum (fun i a => (a : ℝ) • d i)) ≠
        ∑ j, α_map c j * ω (e j)} ≤ ε_ker) :
    ν (concentrationBadSetN d p_m R N) ≤
      ν {ω : E → ℝ | R ^ 2 < ∑ j : Fin k, (ω (e j)) ^ 2} + ε_ker := by
  -- On the set where:
  --   (1) ∀ c with support in range N, ω(x_c) = ∑ α_j ω(e_j)
  --   (2) ∑ ω(e_j)² ≤ R²
  -- Cauchy-Schwarz gives |ω(x_c)| ≤ R · p_m(x_c) for all such c.
  -- So B_N ⊆ {tail > R²} ∪ {kernel bad}
  set tail := {ω : E → ℝ | R ^ 2 < ∑ j : Fin k, (ω (e j)) ^ 2}
  set kernel_bad := {ω : E → ℝ | ∃ c : ℕ →₀ ℚ, c.support ⊆ Finset.range N ∧
    ω (c.sum (fun i a => (a : ℝ) • d i)) ≠
      ∑ j, α_map c j * ω (e j)}
  -- Step 1: Show B_N ⊆ tail ∪ kernel_bad
  have h_sub : concentrationBadSetN d p_m R N ⊆ tail ∪ kernel_bad := by
    intro ω hω
    by_contra h_not
    simp only [Set.mem_union, not_or] at h_not
    obtain ⟨h_not_tail, h_not_ker⟩ := h_not
    simp only [tail, kernel_bad, Set.mem_setOf_eq, not_lt, not_exists, not_and,
      ne_eq, not_not] at h_not_tail h_not_ker
    -- h_not_tail: ∑ ω(e_j)² ≤ R²
    -- h_not_ker: ∀ c, c.support ⊆ range N → ω(x_c) = ∑ α_j(c) ω(e_j)
    obtain ⟨c, hc_supp, hc_bad⟩ := hω
    apply hc_bad
    rw [h_not_ker c hc_supp]
    -- Need: |∑ α_j(c) ω(e_j)| ≤ R · p_m(x_c)
    have h_pars := h_parseval c hc_supp
    have h_cs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (α_map c) (fun j => ω (e j))
    have h_sq : (∑ j, α_map c j * ω (e j)) ^ 2 ≤
        (R * p_m (c.sum fun i a => (a : ℝ) • d i)) ^ 2 := by
      calc (∑ j, α_map c j * ω (e j)) ^ 2
          ≤ (∑ j, α_map c j ^ 2) * (∑ j, ω (e j) ^ 2) := h_cs
        _ = p_m (c.sum fun i a => (a : ℝ) • d i) ^ 2 * (∑ j, ω (e j) ^ 2) := by
            rw [h_pars]
        _ ≤ p_m (c.sum fun i a => (a : ℝ) • d i) ^ 2 * R ^ 2 :=
            mul_le_mul_of_nonneg_left h_not_tail (sq_nonneg _)
        _ = (R * p_m (c.sum fun i a => (a : ℝ) • d i)) ^ 2 := by ring
    exact abs_le_of_sq_le_sq h_sq (by positivity)
  -- Step 2: Measure bound
  calc ν (concentrationBadSetN d p_m R N)
      ≤ ν (tail ∪ kernel_bad) := measure_mono h_sub
    _ ≤ ν tail + ν kernel_bad := measure_union_le _ _
    _ ≤ ν tail + ε_ker := by gcongr

/-! ### Main theorem -/

/-- **Nuclear cylindrical concentration** (Gel'fand-Vilenkin Vol.4, Ch.IV §3.3).

    Given Hilbertian seminorms with consecutive HS embeddings generating the topology,
    a cylindrical probability measure with continuous CF, and any sequence of vectors,
    there exist `m, C : ℕ` such that the concentration bound holds.
-/
theorem nuclear_cylindrical_concentration
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [SeparableSpace E] [Nonempty E]
    (Φ : E → ℂ) (ν : Measure (E → ℝ)) [IsProbabilityMeasure ν]
    (h_cf_cont : Continuous Φ)
    (h_cf_joint : ∀ (n : ℕ) (s : Fin n → ℝ) (x : Fin n → E),
      ∫ ω : E → ℝ, exp (I * ↑(∑ i, s i * ω (x i))) ∂ν =
        Φ (∑ i, s i • x i))
    (h_normalized : Φ 0 = 1)
    (d : ℕ → E) (p : ℕ → Seminorm ℝ E) (hp_top : WithSeminorms (fun n => p n))
    (hp_hilb : ∀ n, (p n).IsHilbertian)
    (hp_hs : ∀ n, (p (n + 1)).IsHilbertSchmidtEmbedding (p n))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (m C : ℕ),
      ν {ω | ∃ c : ℕ →₀ ℚ,
        ¬ (|ω (c.sum fun i a => (a : ℝ) • d i)| ≤
          (C : ℝ) * (p m) (c.sum fun i a => (a : ℝ) • d i))} < ENNReal.ofReal ε := by
  -- Step 1: Get quadratic bound from CF continuity
  have h_norm_le : ∀ x : E, ‖Φ x‖ ≤ 1 := cf_norm_le_one Φ ν h_cf_joint
  obtain ⟨m₀, K, hK, h_quad⟩ := combined_quadratic_bound Φ ν h_cf_cont h_normalized
    h_cf_joint p hp_top hp_hs (ε / 8) (by linarith)
  -- Step 2: Set m = m₀ + 1 so ker(p m) ⊆ ker(p m₀)
  set m := m₀ + 1
  -- Step 3: HS constant for embedding p m₀ → p m
  obtain ⟨h_le_m, C_HS, h_HS_bound⟩ := hp_hs m₀
  have hC_HS : 0 ≤ C_HS := h_HS_bound 0 Fin.elim0 (fun i => Fin.elim0 i)
  -- Step 4: Quadratic bound on kernel elements
  have h_kernel_quad : ∀ x : E, (p m) x = 0 → ∀ t : ℝ,
      1 - (Φ (t • x)).re ≤ ε / 8 := by
    intro x hx t
    have h_pm₀_zero : (p m₀) x = 0 := by
      have h_mono : (p m₀) x ≤ (p m) x := h_le_m x
      linarith [apply_nonneg (p m₀) x]
    calc 1 - (Φ (t • x)).re
        ≤ ε / 8 + K * (p m₀) (t • x) ^ 2 := h_quad (t • x)
      _ = ε / 8 + K * (‖t‖ * (p m₀) x) ^ 2 := by rw [map_smul_eq_mul]
      _ = ε / 8 := by rw [h_pm₀_zero, mul_zero, sq, mul_zero, mul_zero, add_zero]
  -- Step 5: Gram-Schmidt decomposition for each N
  -- For each N, gram_schmidt_seminorm gives ONB for p m restricted to d|Fin N.
  -- The decomposition is for c with support in range N (i.e. Fin N-indexed sums).
  have h_gs : ∀ N : ℕ, ∃ (k : ℕ) (e : Fin k → E)
      (α_map : (ℕ →₀ ℚ) → Fin k → ℝ),
      (p m).IsOrthonormalSeq e ∧
      (∀ c : ℕ →₀ ℚ, c.support ⊆ Finset.range N →
        (p m) (c.sum (fun i a => (a : ℝ) • d i) - ∑ j, α_map c j • e j) = 0) ∧
      (∀ c : ℕ →₀ ℚ, c.support ⊆ Finset.range N →
        (p m) (c.sum (fun i a => (a : ℝ) • d i)) ^ 2 = ∑ j, α_map c j ^ 2) := by
    intro N
    -- Apply Gram-Schmidt to the finite restriction d|_{Fin N}
    obtain ⟨k, e, he, h_decomp_fin⟩ := gram_schmidt_seminorm (p m) (hp_hilb m) N
      (fun i => d (i : ℕ))
    -- Build the coefficient map: for c with support in range N, convert to Fin N → ℝ
    -- and apply the Gram-Schmidt decomposition
    let β_of_c (c : ℕ →₀ ℚ) : Fin N → ℝ := fun i => (c (i : ℕ) : ℝ)
    -- The α_map uses the Gram-Schmidt decomposition applied to β_of_c
    let α_map (c : ℕ →₀ ℚ) : Fin k → ℝ := (h_decomp_fin (β_of_c c)).choose
    refine ⟨k, e, α_map, he, fun c hc => ?_, fun c hc => ?_⟩
    all_goals {
      -- Both goals need: c.sum (fun i a => (a : ℝ) • d i) = ∑ i : Fin N, β_of_c c i • d ↑i
      -- when c.support ⊆ range N
      have h_sum_eq : c.sum (fun i a => (a : ℝ) • d i) =
          ∑ i : Fin N, β_of_c c i • d (i : ℕ) := by
        -- Convert Fin N sum to sum over Finset.range N
        have h_fin_range : ∑ i : Fin N, β_of_c c i • d (i : ℕ) =
            ∑ i ∈ Finset.range N, (c i : ℝ) • d i := by
          rw [Finset.sum_range]
        rw [Finsupp.sum, h_fin_range]
        apply Finset.sum_subset hc
        intro i _ hi
        simp only [Finsupp.mem_support_iff, not_not] at hi
        simp [hi]
      first
      | (rw [h_sum_eq]; exact (h_decomp_fin (β_of_c c)).choose_spec.1)
      | (rw [h_sum_eq]; exact (h_decomp_fin (β_of_c c)).choose_spec.2)
    }
  -- Step 6: Choose R large enough for the tail bound (uniform in k)
  -- The Gaussian averaging + Chebyshev argument gives: for any δ > 0,
  -- there exists R > 0 such that for ANY p m-ONB e with ∑(p m₀)(eⱼ)² ≤ C_HS,
  -- ν{∑ ω(eⱼ)² > R²} ≤ ofReal δ.
  -- This R depends only on ε_q, K, C_HS, δ, NOT on k or e.
  -- We need R such that the tail contribution is ≤ ofReal(ε/4).
  -- Also need the kernel contribution ≤ ofReal(ε/4).
  -- Total: ε/4 + ε/4 = ε/2, and we need < ε.
  --
  -- Choose C large enough (exists by tail_bound_uniform).
  suffices h_exists_C : ∃ C_real : ℝ, 0 < C_real ∧
      ∀ N, ν (concentrationBadSetN d (p m) C_real N) ≤
        ENNReal.ofReal (ε / 2) by
    obtain ⟨C_real, hC_pos, h_bound⟩ := h_exists_C
    refine ⟨m, Nat.ceil C_real + 1, ?_⟩
    -- The bad set with ⌈C_real⌉ + 1 ⊆ bad set with C_real
    -- (larger constant makes the bound easier to satisfy)
    have hC_ge : C_real ≤ ↑(Nat.ceil C_real + 1) := by
      calc C_real ≤ ↑(Nat.ceil C_real) := Nat.le_ceil C_real
        _ ≤ ↑(Nat.ceil C_real + 1) := by exact_mod_cast Nat.le_succ _
    apply lt_of_le_of_lt
    · apply concentrationBadSet_measure_le
      intro N
      calc ν (concentrationBadSetN d (p m) (↑(Nat.ceil C_real + 1)) N)
          ≤ ν (concentrationBadSetN d (p m) C_real N) := by
            apply measure_mono
            intro ω hω
            obtain ⟨c, hc_supp, hc_bad⟩ := hω
            refine ⟨c, hc_supp, fun h_le => hc_bad ?_⟩
            -- h_le : |ω(x)| ≤ C_real · p(x)
            -- Need: |ω(x)| ≤ C_nat · p(x)
            exact le_trans h_le (mul_le_mul_of_nonneg_right hC_ge (apply_nonneg _ _))
        _ ≤ ENNReal.ofReal (ε / 2) := h_bound N
    · exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by linarith) |>.mpr (by linarith)
  -- Now prove the suffices: ∃ C_real, 0 < C_real ∧ ∀ N, ν(B_N) ≤ ofReal(ε/2)
  -- Step 6a: Get uniform tail bound R
  obtain ⟨R, hR_pos, h_tail_unif⟩ := tail_bound_uniform Φ ν h_cf_joint h_norm_le
    (p m₀) (hp_hilb m₀) (ε / 8) K (by linarith) hK h_quad C_HS hC_HS (ε / 4) (by linarith)
    (by linarith) (p m) h_HS_bound
  -- Step 6b: Use C_real = R
  refine ⟨R, hR_pos, fun N => ?_⟩
  -- For this N, get Gram-Schmidt data
  obtain ⟨k, e, α_map, he_orth, h_ker_decomp, h_pars⟩ := h_gs N
  -- Step 6c: Kernel concentration bound
  have h_ker_bound := kernel_concentration_bound Φ ν h_cf_joint h_normalized
    (p m) (ε / 8) (by linarith) h_kernel_quad d N e α_map h_ker_decomp
  -- Step 6d: Apply badSetN_bound_with_kernel
  have h_bn := badSetN_bound_with_kernel Φ ν d (p m) e α_map R hR_pos N h_pars
    (ENNReal.ofReal (ε / 8)) h_ker_bound
  -- Step 6e: Get tail bound for this specific ONB
  have h_tail := h_tail_unif k e he_orth
  -- Step 6f: Combine: ν(B_N) ≤ ν(tail) + ofReal(ε/8) ≤ ofReal(ε/4) + ofReal(ε/8) ≤ ofReal(ε/2)
  calc ν (concentrationBadSetN d (p m) R N)
      ≤ ν {ω | R ^ 2 < ∑ j : Fin k, (ω (e j)) ^ 2} + ENNReal.ofReal (ε / 8) := h_bn
    _ ≤ ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 8) := by gcongr
    _ ≤ ENNReal.ofReal (ε / 4 + ε / 8) := ENNReal.ofReal_add (by linarith) (by linarith) |>.symm.le
    _ ≤ ENNReal.ofReal (ε / 2) := by
        apply ENNReal.ofReal_le_ofReal; linarith


/-! ## Main theorem -/

/-- **Minlos concentration bound** — wrapper around
`nuclear_cylindrical_concentration`.
-/
theorem minlos_concentration [SeparableSpace E] [Nonempty E]
    (Φ : E → ℂ) (ν : Measure (E → ℝ)) [IsProbabilityMeasure ν]
    (h_cf_cont : Continuous Φ)
    (h_cf_joint : ∀ (n : ℕ) (s : Fin n → ℝ) (x : Fin n → E),
      ∫ ω : E → ℝ, exp (I * ↑(∑ i, s i * ω (x i))) ∂ν =
        Φ (∑ i, s i • x i))
    (h_normalized : Φ 0 = 1)
    (d : ℕ → E) (p : ℕ → Seminorm ℝ E) (hp_top : WithSeminorms (fun n => p n))
    (hp_hilb : ∀ n, (p n).IsHilbertian)
    (hp_hs : ∀ n, (p (n + 1)).IsHilbertSchmidtEmbedding (p n))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (m C : ℕ),
      ν {ω | ∃ c : ℕ →₀ ℚ,
        ¬ (|ω (c.sum fun i a => (a : ℝ) • d i)| ≤
          (C : ℝ) * (p m) (c.sum fun i a => (a : ℝ) • d i))} < ENNReal.ofReal ε :=
  nuclear_cylindrical_concentration (E := E) Φ ν h_cf_cont h_cf_joint h_normalized d p hp_top
    hp_hilb hp_hs ε hε

end
