/-
Copyright (c) 2026 Jonathan Conrad, Paula Muermann, Maryna Viazovska. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Conrad, Paula Muermann, Maryna Viazovska
-/
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import LeanPool.PentagonalNumberTheoremAnalytic.QSeries.JacobiTripleProduct

/-!
# Locally uniform convergence and analytic Jacobi triple product

We prove that both sides of the Jacobi triple product (JTP) identity converge
locally uniformly for $\|q\| < 1$ on $\{z \neq 0\}$, and deduce the **analytic JTP**:
the identity holds for **all** $\|q\| < 1$ and $z \neq 0$ (removing the earlier
restriction $\|z\| < 1$).

## Main results

* `QSeries.summable_pow_mul_pow_choose_two'` — Summability of the nonneg bilateral
  sum for **all** $z$ when $\|q\| < 1$.
* `QSeries.tendstoLocallyUniformlyOn_jacobiProd` — The product side converges
  locally uniformly on $\{z \neq 0\}$.
* `QSeries.tendstoLocallyUniformlyOn_jacobiBilateral` — The series side
  converges locally uniformly on $\{z \neq 0\}$.
* `QSeries.jacobiTripleProduct'` — The analytic JTP for all
  $\|q\| < 1$ and $z \neq 0$.
-/

open Finset Filter
open scoped Topology

namespace QSeries

noncomputable section

/-- Ratio-test core for the Weierstrass `M`-test bounds appearing in the Jacobi triple
product: for `‖q‖ < 1` the family `k ↦ c ^ (k + j) * ‖q‖ ^ (k + 2 * j).choose 2` is summable
for every real `c` and every shift `j`. -/
theorem summable_pow_add_mul_norm_pow_choose_two {q : ℂ} (hq : ‖q‖ < 1) (c : ℝ) (j : ℕ) :
    Summable fun k : ℕ => c ^ (k + j) * ‖q‖ ^ (k + 2 * j).choose 2 := by
  have h_lim : Tendsto (fun k : ℕ => |c| * ‖q‖ ^ (k + 2 * j)) atTop (𝓝 0) := by
    simpa using
      (((tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg q) hq).comp
        (tendsto_add_atTop_nat (2 * j))).const_mul |c|)
  refine summable_of_ratio_norm_eventually_le (r := 1 / 2) (by norm_num) ?_
  filter_upwards [h_lim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with k hk
  have hstep : (k + 1 + 2 * j).choose 2 = (k + 2 * j).choose 2 + (k + 2 * j) := by
    rw [show k + 1 + 2 * j = k + 2 * j + 1 by ring, Nat.choose_succ_succ,
      Nat.choose_one_right, add_comm]
  have key : ‖c ^ (k + 1 + j) * ‖q‖ ^ (k + 1 + 2 * j).choose 2‖
      = |c| * ‖q‖ ^ (k + 2 * j) * ‖c ^ (k + j) * ‖q‖ ^ (k + 2 * j).choose 2‖ := by
    rw [hstep]
    simp only [norm_mul, norm_pow, Real.norm_eq_abs, abs_norm]
    ring
  rw [key]
  exact mul_le_mul_of_nonneg_right hk.le (norm_nonneg _)

/-- The nonneg bilateral sum $\sum_{k \ge 0} z^k q^{\binom{k}{2}}$ converges
for **all** $z \in \mathbb{C}$ when $\|q\| < 1$. -/
theorem summable_pow_mul_pow_choose_two' {q z : ℂ} (hq : ‖q‖ < 1) :
    Summable (fun k : ℕ => z ^ k * q ^ k.choose 2) := by
  refine Summable.of_norm ?_
  simpa using summable_pow_add_mul_norm_pow_choose_two hq ‖z‖ 0

/-- Summability of the Weierstrass M-test bound $R^k \|q\|^{\binom{k}{2}}$ for any real $R$. -/
theorem summable_pow_mul_norm_pow_choose_two {q : ℂ} (hq : ‖q‖ < 1) (R : ℝ) :
    Summable (fun k : ℕ => R ^ k * ‖q‖ ^ k.choose 2) := by
  simpa using summable_pow_add_mul_norm_pow_choose_two hq R 0

/-- Summability of the Weierstrass M-test bound $(R')^{m+1} \|q\|^{\binom{m+2}{2}}$
for any real $R'$. -/
theorem summable_pow_succ_mul_norm_pow_choose_two {q : ℂ} (hq : ‖q‖ < 1) (R' : ℝ) :
    Summable (fun m : ℕ => R' ^ (m + 1) * ‖q‖ ^ (m + 2).choose 2) := by
  simpa using summable_pow_add_mul_norm_pow_choose_two hq R' 1

/-- Extended product expansion for all $z$. -/
theorem hasSum_pow_choose_two_mul_pow_mul_qPochhammerInf' {q z : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ => q ^ n.choose 2 * z ^ n * qPochhammerInf (q * q ^ n) q)
      (qPochhammerInf q q * qPochhammerInf (-z) q) := by
  (convert HasSum.mul_left (qPochhammerInf q q) (euler_second_identity' hq) using 1; try rfl)
  ext n
  by_cases hn : qPochhammer q q n = 0
  · exact absurd hn <| qPochhammer_ne_zero hq (by linarith) n
  · simp only [div_eq_mul_inv, mul_assoc, mul_comm]
    congr 1
    rw [qPochhammerInf_self_eq_qPochhammer_mul hq n]
    field_simp

/-- The nonneg partial sums $\sum_{k < N} z^k q^{\binom{k}{2}}$ converge uniformly on
$\{z : \|z\| \le R\}$ by the Weierstrass M-test. -/
theorem tendstoUniformlyOn_sum_pow_mul_pow_choose_two {q : ℂ} (hq : ‖q‖ < 1) (R : ℝ) :
    TendstoUniformlyOn
      (fun N z => ∑ k ∈ Finset.range N, z ^ k * q ^ k.choose 2)
      (fun z => ∑' k : ℕ, z ^ k * q ^ k.choose 2)
      atTop (Metric.closedBall 0 R) := by
  refine tendstoUniformlyOn_tsum_nat (summable_pow_mul_norm_pow_choose_two hq R) fun n z hz => ?_
  rw [norm_mul, norm_pow, norm_pow]
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (norm_nonneg z) (mem_closedBall_zero_iff.mp hz) n) (by positivity)

/-- The negative-index partial sums converge uniformly on $\{z : \|z^{-1}\| \le R'\}$. -/
theorem tendstoUniformlyOn_sum_inv_pow_mul_pow_choose_two {q : ℂ} (hq : ‖q‖ < 1) (R' : ℝ) :
    TendstoUniformlyOn
      (fun N z => ∑ m ∈ Finset.range N, z⁻¹ ^ (m + 1) * q ^ (m + 2).choose 2)
      (fun z => ∑' m : ℕ, z⁻¹ ^ (m + 1) * q ^ (m + 2).choose 2)
      atTop {z : ℂ | ‖z⁻¹‖ ≤ R'} := by
  refine tendstoUniformlyOn_tsum_nat (summable_pow_succ_mul_norm_pow_choose_two hq R')
    fun m z hz => ?_
  rw [norm_mul, norm_pow, norm_pow]
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (norm_nonneg _) hz (m + 1)) (by positivity)

/-- Convert Finset-indexed `TendstoUniformlyOn` to ℕ-indexed via `Finset.range`. -/
private lemma tendstoUniformlyOn_prod_range_of_finset {α β : Type*}
    [CommMonoid β] [UniformSpace β] {f : ℕ → α → β} {g : α → β} {s : Set α}
    (h : TendstoUniformlyOn (fun (S : Finset ℕ) (x : α) => ∏ i ∈ S, f i x) g
         Filter.atTop s) :
    TendstoUniformlyOn (fun (n : ℕ) (x : α) => ∏ i ∈ Finset.range n, f i x) g
         Filter.atTop s := by
  intro U hU
  have h1 := h U hU
  rw [Filter.Eventually] at h1 ⊢
  have h_range : Filter.Tendsto Finset.range (Filter.atTop : Filter ℕ)
      (Filter.atTop : Filter (Finset ℕ)) := by
    rw [Filter.tendsto_atTop_atTop]
    intro s
    exact ⟨(s.sup id) + 1, fun n hn x hx =>
      Finset.mem_range.mpr (by have := Finset.le_sup (f := id) hx; simp at this; omega)⟩
  exact h_range.eventually h1

/-- The partial Pochhammer products $(a;q)_n$ converge locally uniformly in $a$
when $\|q\| < 1$. -/
theorem tendstoLocallyUniformly_qPochhammer {q : ℂ} (hq : ‖q‖ < 1) :
    TendstoLocallyUniformly
      (fun n a => qPochhammer a q n)
      (fun a => qPochhammerInf a q) atTop := by
  unfold qPochhammer qPochhammerInf
  have h_uniform : ∀ K : Set ℂ, IsCompact K →
      TendstoUniformlyOn (fun n a => ∏ k ∈ Finset.range n, (1 - a * q ^ k))
        (fun a => ∏' k : ℕ, (1 - a * q ^ k)) atTop K := by
    intro K hK
    set M := sSup ((fun a : ℂ => ‖a‖) '' K)
    have h_summable : Summable fun k : ℕ => M * ‖q‖ ^ k :=
      Summable.mul_left _ <| summable_geometric_of_lt_one (norm_nonneg q) hq
    have h_le : ∀ x ∈ K, ‖x‖ ≤ M := fun x hx =>
      le_csSup (hK.image continuous_norm).bddAbove (Set.mem_image_of_mem _ hx)
    have h_bound : ∀ᶠ i in cofinite, ∀ x ∈ K, ‖-x * q ^ i‖ ≤ M * ‖q‖ ^ i := by
      filter_upwards with i x hx
      simpa using mul_le_mul_of_nonneg_right (h_le x hx) (by positivity : (0 : ℝ) ≤ ‖q‖ ^ i)
    have h_prod := Summable.hasProdUniformlyOn_one_add hK h_summable h_bound
      fun i => continuousOn_id.neg.mul continuousOn_const
    convert tendstoUniformlyOn_prod_range_of_finset h_prod.tendstoUniformlyOn using 1
    · exact funext fun n => funext fun x => Finset.prod_congr rfl fun _ _ => by ring
    · exact funext fun x => tprod_congr fun i => by ring
  rw [Metric.tendstoLocallyUniformly_iff]
  intro ε hε x
  have hK := Metric.tendstoUniformlyOn_iff.mp
    (h_uniform (Metric.closedBall x 1) (ProperSpace.isCompact_closedBall x 1))
  exact ⟨Metric.closedBall x 1, Metric.closedBall_mem_nhds _ zero_lt_one, hK ε hε⟩

/-- Precomposing a uniform limit with a map sending `s` into the domain set `t`. -/
private lemma tendstoUniformlyOn_comp_of_mapsTo {s t : Set ℂ} {f : ℕ → ℂ → ℂ} {F φ : ℂ → ℂ}
    (h : TendstoUniformlyOn f F atTop t) (hφ : ∀ z ∈ s, φ z ∈ t) :
    TendstoUniformlyOn (fun n z => f n (φ z)) (fun z => F (φ z)) atTop s := by
  intro U hU
  filter_upwards [h U hU] with n hn z hz
  exact hn (φ z) (hφ z hz)

/-- On the closed ball of radius `‖z₀‖ / 2` around `z₀` every point has norm at least
`‖z₀‖ / 2`; so on such a ball `z` stays away from `0`. -/
private lemma half_norm_le_norm_of_mem_closedBall {z₀ z : ℂ}
    (hz : z ∈ Metric.closedBall z₀ (‖z₀‖ / 2)) : ‖z₀‖ / 2 ≤ ‖z‖ := by
  rw [Metric.mem_closedBall, dist_eq_norm'] at hz
  have := norm_sub_norm_le z₀ z
  linarith

/-- On a ball of radius `‖z₀‖ / 2` around `z₀ ≠ 0` the inverse `z⁻¹` is bounded
by `2 / ‖z₀‖`. -/
private lemma norm_inv_le_of_mem_ball {z₀ z : ℂ} (hz₀ : z₀ ≠ 0)
    (hz : z ∈ Metric.ball z₀ (‖z₀‖ / 2)) : ‖z⁻¹‖ ≤ 2 / ‖z₀‖ := by
  have hz₀' : 0 < ‖z₀‖ := norm_pos_iff.mpr hz₀
  have hzn := half_norm_le_norm_of_mem_closedBall (Metric.ball_subset_closedBall hz)
  rw [norm_inv, inv_eq_one_div, div_le_div_iff₀ (by linarith) hz₀']
  linarith

/-- The partial sums of the bilateral Jacobi series converge locally uniformly on
$\{z \neq 0\}$ for fixed $\|q\| < 1$. -/
theorem tendstoLocallyUniformlyOn_jacobiBilateral {q : ℂ} (hq : ‖q‖ < 1) :
    TendstoLocallyUniformlyOn
      (fun N z =>
        (∑ k ∈ Finset.range N, z ^ k * q ^ k.choose 2) +
        (∑ m ∈ Finset.range N, z⁻¹ ^ (m + 1) * q ^ (m + 2).choose 2))
      (fun z => jacobiBilateral q z) atTop {z : ℂ | z ≠ 0} := by
  refine TendstoLocallyUniformlyOn.add ?_ ?_
  · apply TendstoLocallyUniformly.tendstoLocallyUniformlyOn
    rw [Metric.tendstoLocallyUniformly_iff]
    intro ε hε x
    have h_nonneg := Metric.tendstoUniformlyOn_iff.mp
      (tendstoUniformlyOn_sum_pow_mul_pow_choose_two hq (‖x‖ + 1))
    exact ⟨Metric.closedBall 0 (‖x‖ + 1),
      Metric.closedBall_mem_nhds_of_mem (by norm_num), h_nonneg ε hε⟩
  · intro ε hε z₀ hz₀
    have hr₀ : 0 < ‖z₀‖ / 2 := by
      have : 0 < ‖z₀‖ := norm_pos_iff.mpr hz₀
      linarith
    have hsub : Metric.ball z₀ (‖z₀‖ / 2) ∩ {z : ℂ | z ≠ 0} ⊆ {z : ℂ | ‖z⁻¹‖ ≤ 2 / ‖z₀‖} :=
      fun x hx => norm_inv_le_of_mem_ball hz₀ hx.1
    have hr := (tendstoUniformlyOn_sum_inv_pow_mul_pow_choose_two hq (2 / ‖z₀‖)).mono hsub
    exact ⟨Metric.ball z₀ (‖z₀‖ / 2) ∩ {z | z ≠ 0},
      Filter.inter_mem (mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds z₀ hr₀))
        self_mem_nhdsWithin, hr ε hε⟩

/-- Uniform convergence of the product of two bounded sequences in a normed ring. -/
lemma tendstoUniformlyOn_mul_of_bounded {s : Set ℂ}
    {f₁ f₂ : ℕ → ℂ → ℂ} {F₁ F₂ : ℂ → ℂ}
    (h₁ : TendstoUniformlyOn f₁ F₁ atTop s)
    (h₂ : TendstoUniformlyOn f₂ F₂ atTop s)
    (hb₁ : ∃ C, ∀ n, ∀ z ∈ s, ‖f₁ n z‖ ≤ C)
    (hb₂ : ∃ C, ∀ z ∈ s, ‖F₂ z‖ ≤ C) :
    TendstoUniformlyOn (fun n z => f₁ n z * f₂ n z) (fun z => F₁ z * F₂ z) atTop s := by
  obtain ⟨C₁, hC₁⟩ := hb₁
  obtain ⟨C₂, hC₂⟩ := hb₂
  rcases s.eq_empty_or_nonempty with rfl | ⟨z₀, hz₀⟩
  · simp [TendstoUniformlyOn]
  have hC₁0 : 0 ≤ C₁ := (norm_nonneg _).trans (hC₁ 0 z₀ hz₀)
  have hC₂0 : 0 ≤ C₂ := (norm_nonneg _).trans (hC₂ z₀ hz₀)
  rw [Metric.tendstoUniformlyOn_iff] at h₁ h₂ ⊢
  intro ε hε
  filter_upwards [h₁ _ (by positivity : 0 < ε / (2 * (C₂ + 1))),
    h₂ _ (by positivity : 0 < ε / (2 * (C₁ + 1)))] with n hn₁ hn₂ z hz
  have e₁ : ‖F₁ z - f₁ n z‖ * (2 * (C₂ + 1)) < ε := by
    rw [← lt_div_iff₀ (by positivity), ← dist_eq_norm]; exact hn₁ z hz
  have e₂ : ‖F₂ z - f₂ n z‖ * (2 * (C₁ + 1)) < ε := by
    rw [← lt_div_iff₀ (by positivity), ← dist_eq_norm]; exact hn₂ z hz
  have h_diff : ‖F₁ z * F₂ z - f₁ n z * f₂ n z‖
      ≤ ‖F₁ z - f₁ n z‖ * ‖F₂ z‖ + ‖f₁ n z‖ * ‖F₂ z - f₂ n z‖ := by
    rw [show F₁ z * F₂ z - f₁ n z * f₂ n z
        = (F₁ z - f₁ n z) * F₂ z + f₁ n z * (F₂ z - f₂ n z) from by ring,
      ← norm_mul, ← norm_mul]
    exact norm_add_le _ _
  rw [dist_eq_norm]
  refine h_diff.trans_lt (lt_of_le_of_lt (add_le_add
    (mul_le_mul_of_nonneg_left (hC₂ z hz) (norm_nonneg _))
    (mul_le_mul_of_nonneg_right (hC₁ n z hz) (norm_nonneg _))) ?_)
  nlinarith [norm_nonneg (F₁ z - f₁ n z), norm_nonneg (F₂ z - f₂ n z)]

/-- The partial Pochhammer products are uniformly bounded on any closed ball. -/
lemma exists_norm_qPochhammer_le {q : ℂ} (hq : ‖q‖ < 1) (R : ℝ) :
    ∃ C, ∀ n, ∀ a ∈ Metric.closedBall (0 : ℂ) R, ‖qPochhammer a q n‖ ≤ C := by
  refine ⟨Real.exp (R / (1 - ‖q‖)), fun n a ha => ?_⟩
  have haR : ‖a‖ ≤ R := mem_closedBall_zero_iff.mp ha
  have hR : 0 ≤ R := (norm_nonneg a).trans haR
  have hterm : ∀ k : ℕ, 0 ≤ R * ‖q‖ ^ k := fun k => mul_nonneg hR (by positivity)
  have h_prod_le : ‖qPochhammer a q n‖ ≤ ∏ k ∈ Finset.range n, (1 + R * ‖q‖ ^ k) := by
    have h_bound : ∀ k ∈ Finset.range n, ‖1 - a * q ^ k‖ ≤ 1 + R * ‖q‖ ^ k := fun k _ =>
      (norm_sub_le _ _).trans <| by
        simpa [norm_mul] using
          add_le_add_left (mul_le_mul_of_nonneg_right haR (by positivity : (0 : ℝ) ≤ ‖q‖ ^ k)) 1
    simpa [qPochhammer] using Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) h_bound
  have h_exp_bound : ∏ k ∈ Finset.range n, (1 + R * ‖q‖ ^ k)
      ≤ Real.exp (∑ k ∈ Finset.range n, R * ‖q‖ ^ k) := by
    rw [Real.exp_sum]
    exact Finset.prod_le_prod₀ (fun k _ => by linarith [hterm k])
      fun k _ => by rw [add_comm]; exact Real.add_one_le_exp _
  refine h_prod_le.trans <| h_exp_bound.trans <| Real.exp_le_exp.mpr ?_
  rw [← Finset.mul_sum, div_eq_mul_inv]
  refine mul_le_mul_of_nonneg_left ?_ hR
  rw [← tsum_geometric_of_lt_one (norm_nonneg q) hq]
  exact Summable.sum_le_tsum _ (fun _ _ => by positivity)
    (summable_geometric_of_lt_one (norm_nonneg q) hq)

/-- The Pochhammer products $(a;q)_n$ converge uniformly on any closed ball as $n \to \infty$. -/
lemma tendstoUniformlyOn_qPochhammer_closedBall {q : ℂ} (hq : ‖q‖ < 1) (R : ℝ) :
    TendstoUniformlyOn (fun n a => qPochhammer a q n)
      (fun a => qPochhammerInf a q) atTop (Metric.closedBall 0 R) :=
  (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
    (ProperSpace.isCompact_closedBall (0 : ℂ) R)).mp
    (tendstoLocallyUniformly_qPochhammer hq).tendstoLocallyUniformlyOn

/-- The infinite Pochhammer product $\mathrm{qPochhammerInf}$ is uniformly bounded on any
closed ball. -/
lemma exists_norm_qPochhammerInf_le {q : ℂ} (hq : ‖q‖ < 1) (R : ℝ) :
    ∃ C, ∀ a ∈ Metric.closedBall (0 : ℂ) R, ‖qPochhammerInf a q‖ ≤ C := by
  obtain ⟨C, hC⟩ := exists_norm_qPochhammer_le hq R
  obtain ⟨N, hN⟩ : ∃ N, ∀ n ≥ N, ∀ a ∈ Metric.closedBall (0 : ℂ) R,
      ‖qPochhammerInf a q - qPochhammer a q n‖ < 1 := by
    simpa [dist_eq_norm] using Metric.tendstoUniformlyOn_iff.mp
      (tendstoUniformlyOn_qPochhammer_closedBall hq R) 1 zero_lt_one
  refine ⟨C + 1, fun a ha => ?_⟩
  have h1 := hN N le_rfl a ha
  have h2 := hC N a ha
  refine le_trans ?_ (by linarith :
    ‖qPochhammerInf a q - qPochhammer a q N‖ + ‖qPochhammer a q N‖ ≤ C + 1)
  simpa using norm_add_le (qPochhammerInf a q - qPochhammer a q N) (qPochhammer a q N)

/-- For `z` in the closed ball of radius `‖z₀‖ / 2` around `z₀ ≠ 0`,
`-q / z` lies in the closed ball of radius `2 * ‖q‖ / ‖z₀‖` around `0`. -/
private lemma neg_div_mem_closedBall {q z₀ z : ℂ} (hz₀ : z₀ ≠ 0)
    (hz : z ∈ Metric.closedBall z₀ (‖z₀‖ / 2)) :
    -q / z ∈ Metric.closedBall (0 : ℂ) (2 * ‖q‖ / ‖z₀‖) := by
  have hz₀' : 0 < ‖z₀‖ := norm_pos_iff.mpr hz₀
  have hzn := half_norm_le_norm_of_mem_closedBall hz
  rw [mem_closedBall_zero_iff, norm_div, norm_neg, div_le_div_iff₀ (by linarith) hz₀']
  nlinarith [norm_nonneg q]

/-- The Pochhammer products `qPochhammer (-z) q n` converge uniformly to
`qPochhammerInf (-z) q` on any `Metric.closedBall z₀ r` when `‖q‖ < 1`. -/
lemma tendstoUniformlyOn_qPochhammer_neg_closedBall {q : ℂ} (hq : ‖q‖ < 1) (z₀ : ℂ) (r : ℝ) :
    TendstoUniformlyOn (fun n z => qPochhammer (-z) q n)
      (fun z => qPochhammerInf (-z) q) atTop (Metric.closedBall z₀ r) := by
  refine tendstoUniformlyOn_comp_of_mapsTo
    (tendstoUniformlyOn_qPochhammer_closedBall hq (‖z₀‖ + r)) fun z hz => ?_
  rw [Metric.mem_closedBall, dist_eq_norm] at hz
  rw [mem_closedBall_zero_iff, norm_neg]
  linarith [norm_sub_norm_le z z₀]

/-- The Pochhammer products `qPochhammer (-q / z) q n` converge uniformly to
`qPochhammerInf (-q / z) q` on `Metric.closedBall z₀ (‖z₀‖ / 2)` for `z₀ ≠ 0`,
`‖q‖ < 1`. -/
lemma tendstoUniformlyOn_qPochhammer_neg_div {q : ℂ} (hq : ‖q‖ < 1) {z₀ : ℂ} (hz₀ : z₀ ≠ 0) :
    TendstoUniformlyOn (fun n z => qPochhammer (-q / z) q n)
      (fun z => qPochhammerInf (-q / z) q) atTop (Metric.closedBall z₀ (‖z₀‖ / 2)) :=
  tendstoUniformlyOn_comp_of_mapsTo
    (tendstoUniformlyOn_qPochhammer_closedBall hq (2 * ‖q‖ / ‖z₀‖))
    fun _ hz => neg_div_mem_closedBall hz₀ hz

/-- The partial products `qPochhammer q q n * qPochhammer (-z) q n * qPochhammer (-q / z) q n`
converge locally uniformly to `jacobiProd q z` on `{z : ℂ | z ≠ 0}` when `‖q‖ < 1`. -/
theorem tendstoLocallyUniformlyOn_jacobiProd {q : ℂ} (hq : ‖q‖ < 1) :
    TendstoLocallyUniformlyOn
      (fun n z => qPochhammer q q n * qPochhammer (-z) q n * qPochhammer (-q / z) q n)
      (fun z => jacobiProd q z) atTop {z : ℂ | z ≠ 0} := by
  have h_suff : ∀ z₀ : ℂ, z₀ ≠ 0 →
      TendstoUniformlyOn
        (fun n z => qPochhammer q q n * qPochhammer (-z) q n * qPochhammer (-q / z) q n)
        (fun z => jacobiProd q z) atTop (Metric.closedBall z₀ (‖z₀‖ / 2)) := by
    intro z₀ hz₀
    have hmem₁ : ∀ z ∈ Metric.closedBall z₀ (‖z₀‖ / 2),
        -z ∈ Metric.closedBall (0 : ℂ) (‖z₀‖ + ‖z₀‖ / 2) := by
      intro z hz
      rw [Metric.mem_closedBall, dist_eq_norm] at hz
      rw [mem_closedBall_zero_iff, norm_neg]
      linarith [norm_sub_norm_le z z₀]
    have hmem₂ : ∀ z ∈ Metric.closedBall z₀ (‖z₀‖ / 2),
        -q / z ∈ Metric.closedBall (0 : ℂ) (2 * ‖q‖ / ‖z₀‖) :=
      fun z hz => neg_div_mem_closedBall hz₀ hz
    have hmemq : ∀ z ∈ Metric.closedBall z₀ (‖z₀‖ / 2), q ∈ Metric.closedBall (0 : ℂ) 1 :=
      fun _ _ => mem_closedBall_zero_iff.mpr hq.le
    have h_neg := tendstoUniformlyOn_qPochhammer_neg_closedBall hq z₀ (‖z₀‖ / 2)
    have h_div := tendstoUniformlyOn_qPochhammer_neg_div hq hz₀
    have h_qq : TendstoUniformlyOn (fun n z => qPochhammer q q n)
        (fun _ : ℂ => qPochhammerInf q q) atTop (Metric.closedBall z₀ (‖z₀‖ / 2)) :=
      tendstoUniformlyOn_comp_of_mapsTo (φ := fun _ => q)
        (tendstoUniformlyOn_qPochhammer_closedBall hq 1) hmemq
    obtain ⟨B₁, hB₁⟩ := exists_norm_qPochhammer_le hq (‖z₀‖ + ‖z₀‖ / 2)
    obtain ⟨Bq, hBq⟩ := exists_norm_qPochhammer_le hq 1
    obtain ⟨C₁, hC₁⟩ := exists_norm_qPochhammerInf_le hq (‖z₀‖ + ‖z₀‖ / 2)
    obtain ⟨C₂, hC₂⟩ := exists_norm_qPochhammerInf_le hq (2 * ‖q‖ / ‖z₀‖)
    have h_BC := tendstoUniformlyOn_mul_of_bounded h_neg h_div
      ⟨B₁, fun n z hz => hB₁ n (-z) (hmem₁ z hz)⟩
      ⟨C₂, fun z hz => hC₂ _ (hmem₂ z hz)⟩
    have hb : ∀ z ∈ Metric.closedBall z₀ (‖z₀‖ / 2),
        ‖qPochhammerInf (-z) q * qPochhammerInf (-q / z) q‖ ≤ C₁ * C₂ := by
      intro z hz
      rw [norm_mul]
      exact mul_le_mul (hC₁ _ (hmem₁ z hz)) (hC₂ _ (hmem₂ z hz)) (norm_nonneg _)
        ((norm_nonneg _).trans (hC₁ _ (hmem₁ z hz)))
    have h_ABC := tendstoUniformlyOn_mul_of_bounded h_qq h_BC
      ⟨Bq, fun n z hz => hBq n q (hmemq z hz)⟩ ⟨C₁ * C₂, hb⟩
    simpa only [← mul_assoc, jacobiProd] using h_ABC
  intro ε hε z₀ hz₀
  refine ⟨Metric.closedBall z₀ (‖z₀‖ / 2) ∩ {z | z ≠ 0}, ?_, ?_⟩
  · exact mem_nhdsWithin_of_mem_nhds (Filter.inter_mem
      (Metric.closedBall_mem_nhds _ <| half_pos <| norm_pos_iff.mpr hz₀)
      (isOpen_ne.mem_nhds hz₀))
  · exact (h_suff z₀ hz₀ ε hε).mono fun n hn y hy => hn y hy.1

/-- The bilateral series satisfies $g(qz) = g(z)/z$ for **all** $z \neq 0$. -/
theorem jacobiBilateral_mul_eq_div' {q z : ℂ} (hq : ‖q‖ < 1) (hq' : q ≠ 0)
    (hz' : z ≠ 0) :
    jacobiBilateral q (q * z) = jacobiBilateral q z / z := by
  have h_split : jacobiBilateral q (q * z) =
      jacobiBilateralPos q (q * z) + jacobiBilateralNeg q (q * z) := rfl
  have h_pos : jacobiBilateralPos q (q * z) = (jacobiBilateralPos q z - 1) / z := by
    unfold jacobiBilateralPos
    rw [eq_div_iff hz']; symm
    simp +decide only [mul_comm]
    rw [← Summable.sum_add_tsum_nat_add 1]
    · norm_num [pow_succ', mul_pow, mul_assoc, mul_comm, mul_left_comm, tsum_mul_left]
      norm_num [Nat.choose_succ_succ, pow_add, mul_assoc, mul_comm, mul_left_comm]
    · convert summable_pow_mul_pow_choose_two' hq using 1
  have h_neg : jacobiBilateralNeg q (q * z) = (jacobiBilateralNeg q z + 1) / z := by
    unfold jacobiBilateralNeg
    simp +decide only [mul_inv_rev, mul_comm, pow_succ, mul_assoc, tsum_mul_left, inv_pow,
      div_eq_mul_inv]
    ring_nf
    rw [Summable.tsum_eq_zero_add]
    · norm_num [hq', hz']; ring_nf
      simp +decide only [ne_eq, hq', not_false_eq_true, mul_inv_cancel₀, mul_comm, mul_one,
        inv_pow, mul_left_comm, tsum_mul_left, mul_assoc, add_right_inj]
      ring_nf
      rw [← tsum_mul_left]; rw [← tsum_mul_left]; congr; ext x
      rw [show (3 + x).choose 2 = (2 + x).choose 2 + (2 + x) by
            simp +arith +decide [Nat.choose]]; ring_nf
      simp +decide [mul_assoc, mul_comm, mul_left_comm, hq']
    · have := summable_inv_pow_mul_pow_choose_two (z := q * z) hq
      (convert this.mul_left (q * z) using 2; first | rfl | ring_nf)
      simp +decide [hq', hz', mul_assoc, mul_comm q]
  rw [h_split, h_pos, h_neg,
      show jacobiBilateral q z = jacobiBilateralPos q z + jacobiBilateralNeg q z from rfl]
  ring

/-- Iterating the product-side FE $N$ times. -/
theorem jacobiProd_eq_pow_mul_pow_choose_two_mul {q z : ℂ} (hq : ‖q‖ < 1) (hq' : q ≠ 0)
    (hz : z ≠ 0) (N : ℕ) :
    jacobiProd q z = z ^ N * q ^ N.choose 2 * jacobiProd q (q ^ N * z) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
      rw [ih, pow_succ']
      rw [show jacobiProd q (q ^ N * z) =
            jacobiProd q (q * (q ^ N * z)) * (q ^ N * z) by
        rw [eq_comm, jacobiProd_mul_eq_div]
        · rw [div_mul_cancel₀ _ (mul_ne_zero (pow_ne_zero _ hq') hz)]
        · exact hq
        · assumption
        · aesop]; ring_nf
      rw [show (1 + N).choose 2 = N.choose 2 + N by
        rw [Nat.add_comm, Nat.choose_succ_succ]; norm_num; ring]; ring

/-- Iterating the series-side FE $N$ times. -/
theorem jacobiBilateral_eq_pow_mul_pow_choose_two_mul {q z : ℂ} (hq : ‖q‖ < 1) (hq' : q ≠ 0)
    (hz : z ≠ 0) (N : ℕ) :
    jacobiBilateral q z =
      z ^ N * q ^ N.choose 2 * jacobiBilateral q (q ^ N * z) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
      have h_fe : jacobiBilateral q (q * (q ^ N * z)) =
          jacobiBilateral q (q ^ N * z) / (q ^ N * z) :=
        jacobiBilateral_mul_eq_div' hq hq' (mul_ne_zero (pow_ne_zero _ hq') hz)
      simp_all +decide [Nat.choose_succ_succ, pow_succ', mul_assoc, mul_comm,
                         mul_left_comm, div_eq_mul_inv]
      simp +decide [pow_add, mul_assoc, hq']

/-- **Analytic Jacobi triple product identity.**
For $\|q\| < 1$ and $z \neq 0$:
$$(q;q)_\infty \cdot (-z;q)_\infty \cdot (-q/z;q)_\infty
  \;=\; \sum_{k \in \mathbb{Z}} z^k \, q^{k(k-1)/2}.$$

This extends the basic JTP (which required $\|z\| < 1$) to **all** $z \neq 0$
using the functional equation $f(qz) = f(z)/z$ satisfied by both sides. -/
theorem jacobiTripleProduct' {q z : ℂ} (hq : ‖q‖ < 1) (hz : z ≠ 0) :
    jacobiProd q z = jacobiBilateral q z := by
  by_cases hq' : q = 0
  · subst hq'
    unfold jacobiProd jacobiBilateral jacobiBilateralPos jacobiBilateralNeg qPochhammerInf
    norm_num [Finset.sum_range_succ', Nat.choose]
    rw [tprod_eq_prod, tsum_eq_sum]
    any_goals exact {0, 1}
    · norm_num [Finset.prod, Finset.sum]
    · rintro (_ | _ | b) <;> simp +decide [Nat.choose]
    · aesop
  · obtain ⟨N, hN⟩ : ∃ N : ℕ, ‖q ^ N * z‖ < 1 := by
      simpa using (summable_geometric_of_lt_one (by positivity) hq) |> fun h =>
        h.mul_right _ |> fun h =>
        h.tendsto_atTop_zero.eventually (gt_mem_nhds zero_lt_one) |> fun h => h.exists
    rw [jacobiProd_eq_pow_mul_pow_choose_two_mul hq hq' hz N,
        jacobiBilateral_eq_pow_mul_pow_choose_two_mul hq hq' hz N,
        jacobiTripleProduct hq hN (by aesop)]

end

end QSeries
