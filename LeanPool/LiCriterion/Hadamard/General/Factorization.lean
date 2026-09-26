/-
Copyright (c) 2026 Nicholas Bulka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicholas Bulka
-/
module


/-
# General-order Hadamard Factorization Theorem

This file proves the multiplicity-aware finite-order Hadamard factorization
theorem (Conway, Functions of One Complex Variable, Chapter XI, Theorem 3.4)
via the Borel–Carathéodory route, without using Poisson–Jensen.

**Non-goals here.** Nothing in this file mentions `riemannZeta`, `riemannXi`,
or the Li criterion. It is a pure complex-analysis theorem about entire
functions.

## Proof path: Borel–Carathéodory (Ahlfors / Stein–Shakarchi)

\begin{theorem}[Hadamard Factorization]
Let $f : \mathbb{C} \to \mathbb{C}$ be entire of finite order $\lambda$.
Let $p := \lfloor \lambda \rfloor$ and let $(a_n)$ be the non-zero zeros
of $f$ counted with multiplicity. Let $m := \mathrm{ord}_0(f)$ be the
multiplicity of the zero of $f$ at the origin. Then
\[
  f(z) \;=\; z^m \cdot \exp(g(z)) \cdot \prod_n E_p\!\left(\frac{z}{a_n}\right)
\]
where $E_p(w) := (1 - w)\exp\!\left(w + \tfrac{w^2}{2} + \cdots + \tfrac{w^p}{p}\right)$
is the $p$-th Weierstrass elementary factor and $g : \mathbb{C} \to \mathbb{C}$
is a polynomial of degree $\le p$.
\end{theorem}

\begin{proof}[Sketch]
(1) \textbf{Summability.} From the order bound and Jensen's formula applied
to counting zeros,
\[
  \sum_n |a_n|^{-(p+1)} \;<\; \infty.
\]
(2) \textbf{Canonical product.} Define $P(z) := \prod_n E_p(z/a_n)$. The
product converges locally uniformly on $\mathbb{C}$, so $P$ is entire, and
by design vanishes exactly at the $a_n$ with the correct multiplicities.

(3) \textbf{Quotient.} The ratio $Q(z) := f(z) / (z^m \cdot P(z))$ has
removable singularities at $0$ and at every $a_n$ (the orders cancel) and
is entire and nowhere zero.

(4) \textbf{Logarithm.} Since $\mathbb{C}$ is simply connected and $Q$ is
entire and nowhere zero, there is an entire $g : \mathbb{C} \to \mathbb{C}$
with $\exp(g(z)) = Q(z)$ for all $z$.

(5) \textbf{Growth bound on $\log|Q|$.} For any $\varepsilon > 0$ and
$|z| = r$ large enough, $\log|f(z)| \le r^{\lambda + \varepsilon}$ (finite
order), and $\log|P(z)| \ge -C_\varepsilon \cdot r^{p+1+\varepsilon}$ (uses
the rank-$p$ Weierstrass lower bound $\log|E_p(w)| \ge -C|w|^{p+1}$ for
$|w| \le 1/2$, plus a tail estimate for the zeros with $|a_n| < 2r$).
Combined,
\[
  \mathrm{Re}\, g(z) \;=\; \log|Q(z)| \;\le\; C \cdot r^{\lambda + \varepsilon}.
\]

(6) \textbf{Borel–Carathéodory.}
The inequality (`BorelCaratheodory.borel_caratheodory_point`)
applied to $g$ with inner radius $r$ and outer radius $2r$ yields
\[
  |g(z)| \;\le\; \frac{2r}{r} \cdot
    \bigl(\sup_{|w|=2r} \mathrm{Re}\,g(w) - \mathrm{Re}\,g(0)\bigr)
    + |g(0)|
       \;\le\; C' \cdot r^{\lambda + \varepsilon} + |g(0)|
\]
for all $|z| \le r$.

(7) \textbf{Cauchy coefficient estimate.} Write $g(z) = \sum_{n \ge 0} g_n z^n$.
Cauchy's inequality on $|z| = r$ gives $|g_n| \cdot r^n \le \sup_{|z|=r} |g(z)|
\le C' \cdot r^{\lambda + \varepsilon} + |g(0)|$, hence
\[
  |g_n| \;\le\; C' \cdot r^{\lambda + \varepsilon - n} + |g(0)| \cdot r^{-n}.
\]
For any $n > \lambda$, choose $\varepsilon > 0$ with $\lambda + \varepsilon < n$.
Letting $r \to \infty$ forces $g_n = 0$. Hence $g$ is a polynomial of degree
$\le \lfloor \lambda \rfloor = p$. \qed
\end{proof}
-/

public import LeanPool.LiCriterion.Hadamard.DyadicBounds
public import LeanPool.LiCriterion.Hadamard.OrderOne.LogDerivMultiplicity
public import LeanPool.LiCriterion.Hadamard.OrderOne.SummabilityMultiplicity
public import LeanPool.LiCriterion.Hadamard.OrderOne.QuotientCancellation
public import LeanPool.LiCriterion.Hadamard.OrderOne.OrderFromMaxModulus
public import LeanPool.LiCriterion.Hadamard.ZeroSetMultiplicity
public import LeanPool.LiCriterion.Hadamard.Theorem

/-!
## Step 0. Preliminaries

### 0.1 Rank-`p` canonical product for a `ZeroSetMultiplicity`

`Hadamard.ZeroSetMultiplicity.canonicalProductZeroSetMultiplicity` is
currently hard-coded to `weierstrassE 1`. The general theorem needs the
rank-`p` variant. We introduce it here so downstream lemmas can refer to
it; the genus-1 version is a special case.
-/

@[expose] public section


open scoped BigOperators
open Complex Real Filter Topology

open Hadamard.DyadicBounds

namespace Hadamard
namespace General

/-- The rank-`p` canonical Weierstrass product over a `ZeroSetMultiplicity`,
with each zero repeated according to its multiplicity. -/
noncomputable def canonicalProductZeroSetMultiplicityRank
    {f : ℂ → ℂ} (Z : ZeroSetMultiplicity f)
    (p : ℕ) (s : ℂ) : ℂ :=
  ∏' i : Z.ZeroWithMultiplicity, weierstrassE p (s / Z.zWithMultiplicity i)

@[simp] lemma canonicalProductZeroSetMultiplicityRank_one
    {f : ℂ → ℂ} (Z : ZeroSetMultiplicity f) (s : ℂ) :
    canonicalProductZeroSetMultiplicityRank Z 1 s =
      Z.canonicalProductZeroSetMultiplicity s := rfl

/-- Explicit version of `Hadamard.weierstrass_E_away_from_one_lower_bound`,
with the concrete witness `2^h * (h + |log δ|)`. -/
private lemma weierstrass_E_away_from_one_lower_bound_explicit
    (h : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∀ z : ℂ, (1 / 2 : ℝ) ≤ ‖z‖ → δ ≤ ‖z - 1‖ →
      Real.log ‖weierstrassE h z‖
        ≥ -(((2 : ℝ) ^ h * ((h : ℝ) + |Real.log δ|)) * ‖z‖ ^ h) := by
  exact Hadamard.weierstrass_E_away_from_one_lower_bound_explicit h δ hδ

private lemma exists_pow_two_lt_and_le_two_mul (r : ℝ) (hr : (2 : ℝ) ≤ r) :
    ∃ n : ℕ, r < (2 : ℝ) ^ n ∧ (2 : ℝ) ^ n ≤ 2 * r := by
  have hex : ∃ n : ℕ, r < (2 : ℝ) ^ n := by
    simpa using (pow_unbounded_of_one_lt r (by norm_num : (1 : ℝ) < 2))
  let n : ℕ := Nat.find hex
  have hn_lt : r < (2 : ℝ) ^ n := Nat.find_spec hex
  have hn0 : n ≠ 0 := by
    intro hn0
    have : r < (1 : ℝ) := by
      simpa [n, hn0] using hn_lt
    exact (not_lt_of_ge hr) (lt_of_lt_of_le this (by norm_num))
  have hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
  have hprev : ¬ r < (2 : ℝ) ^ (n - 1) := by
    have hlt : n - 1 < Nat.find hex := by
      have : n - 1 < n := Nat.sub_lt hn_pos (by decide)
      simpa [n] using this
    exact Nat.find_min hex hlt
  have hprev_le : (2 : ℝ) ^ (n - 1) ≤ r := le_of_not_gt hprev
  have hpow : (2 : ℝ) ^ n = 2 * (2 : ℝ) ^ (n - 1) := by
    have hn_ge1 : 1 ≤ n := Nat.succ_le_of_lt hn_pos
    have hn_eq : n = (n - 1) + 1 := (Nat.sub_add_cancel hn_ge1).symm
    rw [hn_eq]
    simp [pow_succ, mul_comm]
  refine ⟨n, hn_lt, ?_⟩
  calc
    (2 : ℝ) ^ n = 2 * (2 : ℝ) ^ (n - 1) := hpow
    _ ≤ 2 * r := by
      gcongr

/-!
## Step 1. Summability at exponent `p + 1`

**Target.** If `f` is entire of order `≤ λ`, `p = ⌊λ⌋₊`, and the zeros of
`f` are enumerated by `Z : ZeroSetMultiplicity f` with distinct non-zero
values, then the weighted sum
  `∑ (Z.mult ρ) / ‖Z.z ρ‖^(p+1)` converges.

Existing infrastructure:
  * `Hadamard.OrderOne.summable_analyticOrderNatAt_div_norm_sq_of_order_le_one`
    gives this at `p = 1` (exponent `2`), using `analyticOrderNatAt` as
    the multiplicity function. We generalize the exponent from `2` to `p+1`.

LaTeX: the proof goes via Jensen-type zero counting. If $n(r) \le r^{\lambda + \varepsilon}$
(standard, from the max-modulus bound and Jensen's formula), then
$\sum_n |a_n|^{-(p+1)}$ converges by a dyadic decomposition with geometric ratio
$2^{\lambda + \varepsilon - (p+1)} < 1$ since $\lambda + \varepsilon < p + 1$ for
small enough $\varepsilon$ (as $p = \lfloor \lambda \rfloor$).
-/

/-- **Step 1: Summability at exponent `p+1` from `order f ≤ lam` with `p = ⌊lam⌋₊`.**

Thin wrapper around the library lemma
`Hadamard.OrderOne.summable_analyticOrderNatAt_div_norm_pow_of_order_le`
that converts from `analyticOrderNatAt f` weights to `Z.mult` weights via
`h_mult`. -/
theorem summable_mult_div_norm_pow_of_order_le
    {f : ℂ → ℂ} (hf_entire : Differentiable ℂ f)
    (hf_finite : hasFiniteOrder f)
    {lam : ℝ} (hlam_nonneg : 0 ≤ lam) (hf_order_le : order f ≤ lam)
    (Z : ZeroSetMultiplicity f)
    (h_zeros_only : ∀ s : ℂ, f s = 0 ↔ ∃ ρ : Z.Zero, s = Z.z ρ)
    (h_inj : Function.Injective Z.z)
    (h_z_ne_zero : ∀ ρ : Z.Zero, Z.z ρ ≠ 0)
    (h_mult : ∀ ρ : Z.Zero, analyticOrderNatAt f (Z.z ρ) = Z.mult ρ) :
    Summable (fun ρ : Z.Zero =>
      (Z.mult ρ : ℝ) / ‖Z.z ρ‖ ^ (Nat.floor lam + 1)) := by
  have hbase :
      Summable (fun ρ : Z.toZeroSet.Zero =>
        (analyticOrderNatAt f (Z.z ρ) : ℝ) / ‖Z.z ρ‖ ^ (Nat.floor lam + 1)) :=
    Hadamard.OrderOne.summable_analyticOrderNatAt_div_norm_pow_of_order_le
      (f := f) hf_entire hf_finite hlam_nonneg hf_order_le Z.toZeroSet
      (h_zeros_only := h_zeros_only) (h_inj := h_inj) (h_z_ne_zero := h_z_ne_zero)
  -- Rewrite `analyticOrderNatAt f (Z.z ρ) = Z.mult ρ` via `h_mult`.
  refine hbase.congr (fun ρ => ?_)
  have := h_mult ρ
  simp [this]

private lemma cofinal_zerosBallFinset_of_entire
    {f : ℂ → ℂ} (hf_entire : Differentiable ℂ f)
    (Z : ZeroSetMultiplicity f)
    (h_zeros_only : ∀ s : ℂ, f s = 0 ↔ ∃ ρ : Z.Zero, s = Z.z ρ)
    (h_inj : Function.Injective Z.z)
    (h_z_ne_zero : ∀ ρ : Z.Zero, Z.z ρ ≠ 0) :
    ∀ t : Finset Z.Zero, ∃ n : ℕ,
      t ⊆ Hadamard.OrderOne.zerosBallFinsetOfEntire
        (hf_entire := hf_entire) (Z := Z.toZeroSet)
        (h_zeros_only := h_zeros_only) (h_inj := h_inj) (h_z_ne_zero := h_z_ne_zero) n := by
  classical
  intro t
  by_cases ht : t = ∅
  · subst ht
    refine ⟨0, by simp⟩
  · have ht_ne : t.Nonempty := Finset.nonempty_iff_ne_empty.2 ht
    let R : ℝ := t.sup' ht_ne fun ρ : Z.Zero => ‖Z.z ρ‖
    have hR : ∀ ρ : Z.Zero, ρ ∈ t → ‖Z.z ρ‖ ≤ R := by
      intro ρ hρ
      exact Finset.le_sup' (f := fun ρ : Z.Zero => ‖Z.z ρ‖) hρ
    have hpow : ∃ n : ℕ, max R 1 < (2 : ℝ) ^ n := by
      simpa using pow_unbounded_of_one_lt (max R 1) (by norm_num : (1 : ℝ) < 2)
    refine ⟨Nat.find hpow, ?_⟩
    intro ρ hρt
    have hρ_leR : ‖Z.z ρ‖ ≤ R := hR ρ hρt
    have hρ_le : ‖Z.z ρ‖ ≤ max R 1 := le_trans hρ_leR (le_max_left _ _)
    have hmax_le : max R 1 ≤ (2 : ℝ) ^ Nat.find hpow := le_of_lt (Nat.find_spec hpow)
    have hρ_ball : ‖Z.z ρ‖ ≤ (2 : ℝ) ^ Nat.find hpow := le_trans hρ_le hmax_le
    exact
      (Hadamard.OrderOne.mem_zerosBallFinset_of_entire_iff
        (hf_entire := hf_entire) (Z := Z.toZeroSet) (h_zeros_only := h_zeros_only)
        (h_inj := h_inj) (h_z_ne_zero := h_z_ne_zero) _ _).2 hρ_ball

/-- Convert a `ZeroWithMultiplicity` tsum into a multiplicity-weighted tsum on distinct zeros. -/
private lemma tsum_zeroWithMultiplicity_eq_weighted_tsum_of_nonneg
    {f : ℂ → ℂ} (Z : ZeroSetMultiplicity f)
    (g : Z.Zero → ℝ) (hg_nonneg : ∀ ρ : Z.Zero, 0 ≤ g ρ)
    (hg : Summable (fun ρ : Z.Zero => (Z.mult ρ : ℝ) * g ρ)) :
    (∑' i : Z.ZeroWithMultiplicity, g i.1) =
      ∑' ρ : Z.Zero, (Z.mult ρ : ℝ) * g ρ := by
  classical
  have hsigma : Summable (fun i : Z.ZeroWithMultiplicity => g i.1) := by
    refine
      (summable_sigma_of_nonneg (f := fun i : Z.ZeroWithMultiplicity => g i.1) ?_).2 ?_
    · intro i
      exact hg_nonneg i.1
    · refine ⟨fun _ => Summable.of_finite, ?_⟩
      refine hg.congr fun ρ => ?_
      calc
        (Z.mult ρ : ℝ) * g ρ = ∑' _k : Fin (Z.mult ρ), g ρ := by
          rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        _ = ∑' k : Fin (Z.mult ρ), g (⟨ρ, k⟩ : Z.ZeroWithMultiplicity).1 := by
          rfl
  have hsigma_tsum :
      (∑' i : Z.ZeroWithMultiplicity, g i.1) =
        ∑' ρ : Z.Zero, ∑' _k : Fin (Z.mult ρ), g ρ := by
    exact
      (hsigma.tsum_sigma' (fun ρ =>
        (hasSum_fintype (fun _ : Fin (Z.mult ρ) => g ρ)).summable))
  have hinner :
      (fun ρ : Z.Zero => ∑' _k : Fin (Z.mult ρ), g ρ) =
        (fun ρ : Z.Zero => (Z.mult ρ : ℝ) * g ρ) := by
    funext ρ
    rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simpa [hinner] using hsigma_tsum


private theorem sum_mult_div_norm_pow_le_rpow_of_two_pow
    {f : ℂ → ℂ} (hf_entire : Differentiable ℂ f)
    (hf_finite : hasFiniteOrder f)
    {lam : ℝ} (hlam_nonneg : 0 ≤ lam) (hf_order_le : order f ≤ lam)
    (Z : ZeroSetMultiplicity f)
    (h_zeros_only : ∀ s : ℂ, f s = 0 ↔ ∃ ρ : Z.Zero, s = Z.z ρ)
    (h_inj : Function.Injective Z.z)
    (h_z_ne_zero : ∀ ρ : Z.Zero, Z.z ρ ≠ 0)
    (h_mult : ∀ ρ : Z.Zero, analyticOrderNatAt f (Z.z ρ) = Z.mult ρ)
    {p : ℕ} (hp_le_lam : (p : ℝ) ≤ lam)
    {δ : ℝ} (hδ_pos : 0 < δ) :
    ∃ n₀ : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ n : ℕ, n₀ ≤ n →
        (∑ ρ ∈ Hadamard.OrderOne.zerosBallFinsetOfEntire
            (hf_entire := hf_entire) (Z := Z.toZeroSet) (h_zeros_only := h_zeros_only)
            (h_inj := h_inj) (h_z_ne_zero := h_z_ne_zero) n,
          (Z.mult ρ : ℝ) / ‖Z.z ρ‖ ^ p)
          ≤ C * ((2 : ℝ) ^ n) ^ (lam + δ - p) := by
  classical
  obtain ⟨Rcount, Ccount, hCcount_nonneg, hW_le_raw⟩ :=
    Hadamard.OrderOne.sum_multiplicity_zeros_le_rpow_of_order_le
      (f := f) hf_entire hf_finite hf_order_le hlam_nonneg Z.toZeroSet
      (h_zeros_only := h_zeros_only) (h_inj := h_inj) (h_z_ne_zero := h_z_ne_zero) δ hδ_pos
  let w : Z.Zero → ℝ := fun ρ => (Z.mult ρ : ℝ)
  have hW_le :
      ∀ r : ℝ, Rcount ≤ r →
        (∑ᶠ ρ : Z.Zero, if ‖Z.z ρ‖ ≤ r then w ρ else 0) ≤
          Ccount * r ^ (lam + δ) := by
    intro r hr
    simpa [w, h_mult] using hW_le_raw r hr
  let R0 : ℝ := max Rcount 1
  have hR0_le : ∃ n₀ : ℕ, R0 ≤ (2 : ℝ) ^ n₀ := by
    have h : ∃ n : ℕ, R0 < (2 : ℝ) ^ n := by
      simpa using (pow_unbounded_of_one_lt R0 (by norm_num : (1 : ℝ) < 2))
    refine ⟨Nat.find h, le_of_lt (Nat.find_spec h)⟩
  obtain ⟨n₀, hn₀⟩ := hR0_le
  have hRcount_le : Rcount ≤ (2 : ℝ) ^ n₀ := le_trans (le_max_left _ _) hn₀
  have hone_le : (1 : ℝ) ≤ (2 : ℝ) ^ n₀ := le_trans (le_max_right _ _) hn₀
  let ball : ℕ → Finset Z.Zero := fun n =>
    Hadamard.OrderOne.zerosBallFinsetOfEntire
      (hf_entire := hf_entire) (Z := Z.toZeroSet)
      (h_zeros_only := h_zeros_only) (h_inj := h_inj) (h_z_ne_zero := h_z_ne_zero) n
  let smallSum : ℝ := ∑ ρ ∈ ball n₀, w ρ / ‖Z.z ρ‖ ^ p
  have hsmallSum_nonneg : 0 ≤ smallSum := by
    refine Finset.sum_nonneg ?_
    intro ρ hρ
    positivity [w]
  let α : ℝ := lam + δ - p
  have hα_pos : 0 < α := by
    linarith
  let q : ℝ := (2 : ℝ) ^ α
  have hq_gt1 : 1 < q := by
    simpa [q] using Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2) hα_pos
  have hq_sub_pos : 0 < q - 1 := sub_pos.mpr hq_gt1
  have hq_sub_ne : q - 1 ≠ 0 := ne_of_gt hq_sub_pos
  let A : ℝ := (2 : ℝ) ^ (lam + δ) * Ccount
  have hA_nonneg : 0 ≤ A := by
    have hpow_nonneg : 0 ≤ (2 : ℝ) ^ (lam + δ) :=
      Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
    exact mul_nonneg hpow_nonneg hCcount_nonneg
  let Ctail : ℝ := A / (q - 1)
  let C : ℝ := smallSum + Ctail
  have hC_nonneg : 0 ≤ C := by
    have hCtail_nonneg : 0 ≤ Ctail := div_nonneg hA_nonneg (le_of_lt hq_sub_pos)
    exact add_nonneg hsmallSum_nonneg hCtail_nonneg
  have hsub_ball : ∀ k : ℕ, ball k ⊆ ball (k + 1) := by
    intro k ρ hρ
    have hnorm : ‖Z.z ρ‖ ≤ (2 : ℝ) ^ k :=
      (Hadamard.OrderOne.mem_zerosBallFinset_of_entire_iff
        (hf_entire := hf_entire) (Z := Z.toZeroSet) (h_zeros_only := h_zeros_only)
        (h_inj := h_inj) (h_z_ne_zero := h_z_ne_zero) k ρ).1 hρ
    have hk_le : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ (k + 1) :=
      pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.le_succ k)
    exact
      (Hadamard.OrderOne.mem_zerosBallFinset_of_entire_iff
        (hf_entire := hf_entire) (Z := Z.toZeroSet) (h_zeros_only := h_zeros_only)
        (h_inj := h_inj) (h_z_ne_zero := h_z_ne_zero) (k + 1) ρ).2
          (le_trans hnorm hk_le)
  have hball_finsum :
      ∀ k : ℕ,
        (∑ᶠ ρ : Z.Zero, if ‖Z.z ρ‖ ≤ (2 : ℝ) ^ (k + 1) then w ρ else 0) =
          ∑ ρ ∈ ball (k + 1), w ρ := by
    intro k
    exact cutoff_finsum_eq_sum (ball (k + 1)) (fun ρ => ‖Z.z ρ‖ ≤ (2 : ℝ) ^ (k + 1)) w
      (fun ρ => Hadamard.OrderOne.mem_zerosBallFinset_of_entire_iff
        (hf_entire := hf_entire) (Z := Z.toZeroSet) (h_zeros_only := h_zeros_only)
        (h_inj := h_inj) (h_z_ne_zero := h_z_ne_zero) (k + 1) ρ)
  refine ⟨n₀, C, hC_nonneg, ?_⟩
  intro n hn
  have hmain :
      ∀ m : ℕ,
        (∑ ρ ∈ ball (n₀ + m), w ρ / ‖Z.z ρ‖ ^ p) ≤ C * q ^ (n₀ + m) := by
    intro m
    induction m with
    | zero =>
        have hqpow_ge1 : (1 : ℝ) ≤ q ^ n₀ := one_le_pow₀ hq_gt1.le (n := n₀)
        have hsmall_le_C : smallSum ≤ C := by
          have hCtail_nonneg : 0 ≤ Ctail := div_nonneg hA_nonneg (le_of_lt hq_sub_pos)
          simpa [C] using (le_add_of_nonneg_right (a := smallSum) (b := Ctail) hCtail_nonneg)
        have : smallSum ≤ C * q ^ n₀ := by
          exact le_trans hsmall_le_C (le_mul_of_one_le_right hC_nonneg hqpow_ge1)
        simpa [smallSum, ball] using this
    | succ m ih =>
        set k : ℕ := n₀ + m
        let diff : Finset Z.Zero := ball (k + 1) \ ball k
        have hdiff :
            (∑ ρ ∈ diff, w ρ / ‖Z.z ρ‖ ^ p) ≤ A * q ^ k := by
          have hterm_le :
              ∀ ρ, ρ ∈ diff → w ρ / ‖Z.z ρ‖ ^ p ≤ w ρ / ((2 : ℝ) ^ k) ^ p := by
            intro ρ hρ
            have hnot : ¬ ‖Z.z ρ‖ ≤ (2 : ℝ) ^ k := by
              intro hle
              have : ρ ∈ ball k :=
                (Hadamard.OrderOne.mem_zerosBallFinset_of_entire_iff
                  (hf_entire := hf_entire) (Z := Z.toZeroSet) (h_zeros_only := h_zeros_only)
                  (h_inj := h_inj) (h_z_ne_zero := h_z_ne_zero) k ρ).2 hle
              exact (Finset.mem_sdiff.1 hρ).2 this
            have hk_le_norm : (2 : ℝ) ^ k ≤ ‖Z.z ρ‖ := le_of_lt (lt_of_not_ge hnot)
            have hk_pos : 0 < ((2 : ℝ) ^ k) ^ p := by positivity
            have hk_pow_le : ((2 : ℝ) ^ k) ^ p ≤ ‖Z.z ρ‖ ^ p :=
              pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ k) hk_le_norm p
            have hw_nonneg : 0 ≤ w ρ := by positivity [w]
            have hfrac : (1 : ℝ) / ‖Z.z ρ‖ ^ p ≤ (1 : ℝ) / ((2 : ℝ) ^ k) ^ p := by
              simpa [one_div, inv_pow] using (one_div_le_one_div_of_le hk_pos hk_pow_le)
            simpa [div_eq_mul_inv, one_div, mul_assoc, mul_left_comm, mul_comm] using
              (mul_le_mul_of_nonneg_left hfrac hw_nonneg)
          have hsum_le :
              (∑ ρ ∈ diff, w ρ / ‖Z.z ρ‖ ^ p) ≤
                ∑ ρ ∈ diff, w ρ / ((2 : ℝ) ^ k) ^ p := Finset.sum_le_sum hterm_le
          have hRcount_le' : Rcount ≤ (2 : ℝ) ^ (k + 1) := by
            have hn₀_le_k1 : n₀ ≤ k + 1 := by
              dsimp [k]
              omega
            have hpow : (2 : ℝ) ^ n₀ ≤ (2 : ℝ) ^ (k + 1) :=
              pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hn₀_le_k1
            exact le_trans hRcount_le hpow
          have hsum_ball :
              (∑ ρ ∈ ball (k + 1), w ρ) ≤ Ccount * ((2 : ℝ) ^ (k + 1)) ^ (lam + δ) := by
            have hcount_ball := hW_le ((2 : ℝ) ^ (k + 1)) hRcount_le'
            simpa [hball_finsum, ball] using hcount_ball
          have hsum_diff :
              (∑ ρ ∈ diff, w ρ) ≤ Ccount * ((2 : ℝ) ^ (k + 1)) ^ (lam + δ) := by
            have hdiff_le_ball :
                (∑ ρ ∈ diff, w ρ) ≤ ∑ ρ ∈ ball (k + 1), w ρ := by
              refine
                Finset.sum_le_sum_of_subset_of_nonneg
                  (Finset.sdiff_subset : diff ⊆ ball (k + 1)) ?_
              intro ρ _ _
              positivity [w]
            exact le_trans hdiff_le_ball hsum_ball
          have hrewrite :
              Ccount * ((2 : ℝ) ^ (k + 1)) ^ (lam + δ) * ((1 : ℝ) / ((2 : ℝ) ^ k) ^ p) =
                A * q ^ k := dyadic_power_quotient Ccount lam δ p k
          calc
            (∑ ρ ∈ diff, w ρ / ‖Z.z ρ‖ ^ p)
                ≤ ∑ ρ ∈ diff, w ρ / ((2 : ℝ) ^ k) ^ p := hsum_le
            _ = (∑ ρ ∈ diff, w ρ) * ((1 : ℝ) / ((2 : ℝ) ^ k) ^ p) := by
                simp [div_eq_mul_inv, Finset.sum_mul]
            _ ≤
                (Ccount * ((2 : ℝ) ^ (k + 1)) ^ (lam + δ)) *
                  ((1 : ℝ) / ((2 : ℝ) ^ k) ^ p) := by
                  have hconst_nonneg : 0 ≤ (1 : ℝ) / ((2 : ℝ) ^ k) ^ p := by positivity
                  exact mul_le_mul_of_nonneg_right hsum_diff hconst_nonneg
            _ = A * q ^ k := by
                  simpa [mul_assoc, mul_left_comm, mul_comm] using hrewrite
        have ih' :
            (∑ ρ ∈ ball k, w ρ / ‖Z.z ρ‖ ^ p) ≤ C * q ^ k := by
          simpa [k, ball, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ih
        have hCtail_le_C : Ctail ≤ C := by
          simpa [C] using (le_add_of_nonneg_left (a := Ctail) (b := smallSum) hsmallSum_nonneg)
        have hmul_le : Ctail * (q - 1) ≤ C * (q - 1) :=
          mul_le_mul_of_nonneg_right hCtail_le_C (le_of_lt hq_sub_pos)
        have hmul_eq : Ctail * (q - 1) = A := by
          dsimp [Ctail]
          field_simp [hq_sub_ne]
        have hA_le : A ≤ C * (q - 1) := by
          simpa [hmul_eq] using hmul_le
        have hC_rec : A + C ≤ C * q := by
          calc
            A + C ≤ C * (q - 1) + C := by linarith
            _ = C * q := by ring
        calc
          (∑ ρ ∈ ball (k + 1), w ρ / ‖Z.z ρ‖ ^ p)
              =
                (∑ ρ ∈ diff, w ρ / ‖Z.z ρ‖ ^ p) +
                  (∑ ρ ∈ ball k, w ρ / ‖Z.z ρ‖ ^ p) := by
                  simpa [diff, k, ball, add_assoc, add_comm, add_left_comm] using
                    (Finset.sum_sdiff (s₁ := ball k) (s₂ := ball (k + 1))
                      (f := fun ρ : Z.Zero => w ρ / ‖Z.z ρ‖ ^ p) (hsub_ball k)).symm
          _ ≤ A * q ^ k + C * q ^ k := by
                gcongr
          _ = (A + C) * q ^ k := by ring
          _ ≤ (C * q) * q ^ k := by
                gcongr
          _ = C * q ^ (k + 1) := by
                simp [pow_succ, mul_assoc, mul_left_comm, mul_comm]
  have hqpow : q ^ n = ((2 : ℝ) ^ n) ^ (lam + δ - p) := by
    simpa [q] using
      (Real.rpow_pow_comm (x := (2 : ℝ)) (hx := by positivity) (lam + δ - p) n)
  simpa [Nat.add_sub_of_le hn, hqpow] using hmain (n - n₀)




private theorem tsum_mult_div_norm_pow_tail_le_rpow_of_two_pow
    {f : ℂ → ℂ} (hf_entire : Differentiable ℂ f)
    (hf_finite : hasFiniteOrder f)
    {lam : ℝ} (hlam_nonneg : 0 ≤ lam) (hf_order_le : order f ≤ lam)
    (Z : ZeroSetMultiplicity f)
    (h_zeros_only : ∀ s : ℂ, f s = 0 ↔ ∃ ρ : Z.Zero, s = Z.z ρ)
    (h_inj : Function.Injective Z.z)
    (h_z_ne_zero : ∀ ρ : Z.Zero, Z.z ρ ≠ 0)
    (h_mult : ∀ ρ : Z.Zero, analyticOrderNatAt f (Z.z ρ) = Z.mult ρ)
    {p : ℕ} {δ : ℝ} (hδ_pos : 0 < δ)
    (hgap : lam + δ < (p : ℝ) + 1) :
    ∃ n₀ : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ n : ℕ, n₀ ≤ n →
        (∑' ρ : ({ρ : Z.Zero | (2 : ℝ) ^ (n + 1) < ‖Z.z ρ‖} : Set Z.Zero),
            (Z.mult ρ.val : ℝ) / ‖Z.z ρ.val‖ ^ (p + 1))
          ≤ C * ((2 : ℝ) ^ n) ^ (lam + δ - ((p : ℝ) + 1)) := by
  classical
  obtain ⟨Rcount, Ccount, hCcount_nonneg, hW_le_raw⟩ :=
    Hadamard.OrderOne.sum_multiplicity_zeros_le_rpow_of_order_le
      (f := f) hf_entire hf_finite hf_order_le hlam_nonneg Z.toZeroSet
      (h_zeros_only := h_zeros_only) (h_inj := h_inj) (h_z_ne_zero := h_z_ne_zero) δ hδ_pos
  let w : Z.Zero → ℝ := fun ρ => (Z.mult ρ : ℝ)
  have hW_le :
      ∀ r : ℝ, Rcount ≤ r →
        (∑ᶠ ρ : Z.Zero, if ‖Z.z ρ‖ ≤ r then w ρ else 0) ≤
          Ccount * r ^ (lam + δ) := by
    intro r hr
    simpa [w, h_mult] using hW_le_raw r hr
  let R0 : ℝ := max Rcount 1
  have hR0_le : ∃ n₀ : ℕ, R0 ≤ (2 : ℝ) ^ n₀ := by
    have h : ∃ n : ℕ, R0 < (2 : ℝ) ^ n := by
      simpa using (pow_unbounded_of_one_lt R0 (by norm_num : (1 : ℝ) < 2))
    refine ⟨Nat.find h, le_of_lt (Nat.find_spec h)⟩
  obtain ⟨n₀, hn₀⟩ := hR0_le
  have hRcount_le : Rcount ≤ (2 : ℝ) ^ n₀ := le_trans (le_max_left _ _) hn₀
  let q : ℝ := (2 : ℝ) ^ (lam + δ - ((p : ℝ) + 1))
  have hq_pos : 0 < q := by
    simpa [q] using Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _
  have hq_lt_one : q < 1 := by
    have hneg : lam + δ - ((p : ℝ) + 1) < 0 := by linarith
    simpa [q] using Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 2) hneg
  let A : ℝ := (2 : ℝ) ^ (lam + δ) * Ccount
  let C : ℝ := A * q / (1 - q)
  have hC_nonneg : 0 ≤ C := by
    have hpow_nonneg : 0 ≤ (2 : ℝ) ^ (lam + δ) :=
      Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
    have hnum_nonneg : 0 ≤ A * q := by
      have hA_nonneg : 0 ≤ A := mul_nonneg hpow_nonneg hCcount_nonneg
      exact mul_nonneg hA_nonneg (le_of_lt hq_pos)
    have hden_pos : 0 < 1 - q := sub_pos.mpr hq_lt_one
    exact div_nonneg hnum_nonneg (le_of_lt hden_pos)
  let ball : ℕ → Finset Z.Zero := fun n =>
    Hadamard.OrderOne.zerosBallFinsetOfEntire
      (hf_entire := hf_entire) (Z := Z.toZeroSet)
      (h_zeros_only := h_zeros_only) (h_inj := h_inj) (h_z_ne_zero := h_z_ne_zero) n
  have hsub_ball : ∀ k : ℕ, ball k ⊆ ball (k + 1) := by
    intro k ρ hρ
    have hnorm : ‖Z.z ρ‖ ≤ (2 : ℝ) ^ k :=
      (Hadamard.OrderOne.mem_zerosBallFinset_of_entire_iff
        (hf_entire := hf_entire) (Z := Z.toZeroSet) (h_zeros_only := h_zeros_only)
        (h_inj := h_inj) (h_z_ne_zero := h_z_ne_zero) k ρ).1 hρ
    have hk_le : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ (k + 1) :=
      pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.le_succ k)
    exact
      (Hadamard.OrderOne.mem_zerosBallFinset_of_entire_iff
        (hf_entire := hf_entire) (Z := Z.toZeroSet) (h_zeros_only := h_zeros_only)
        (h_inj := h_inj) (h_z_ne_zero := h_z_ne_zero) (k + 1) ρ).2 (le_trans hnorm hk_le)
  have hball_finsum :
      ∀ k : ℕ,
        (∑ᶠ ρ : Z.Zero, if ‖Z.z ρ‖ ≤ (2 : ℝ) ^ (k + 1) then w ρ else 0) =
          ∑ ρ ∈ ball (k + 1), w ρ := by
    intro k
    exact cutoff_finsum_eq_sum (ball (k + 1)) (fun ρ => ‖Z.z ρ‖ ≤ (2 : ℝ) ^ (k + 1)) w
      (fun ρ => Hadamard.OrderOne.mem_zerosBallFinset_of_entire_iff
        (hf_entire := hf_entire) (Z := Z.toZeroSet) (h_zeros_only := h_zeros_only)
        (h_inj := h_inj) (h_z_ne_zero := h_z_ne_zero) (k + 1) ρ)
  refine ⟨n₀, C, hC_nonneg, ?_⟩
  intro n hn
  let g : Z.Zero → ℝ := fun ρ =>
    if (2 : ℝ) ^ (n + 1) < ‖Z.z ρ‖ then w ρ / ‖Z.z ρ‖ ^ (p + 1) else 0
  have hg_nonneg : ∀ ρ : Z.Zero, 0 ≤ g ρ := by
    intro ρ
    by_cases hρ : (2 : ℝ) ^ (n + 1) < ‖Z.z ρ‖
    · positivity [g, w, hρ]
    · simp [g, hρ]
  have hball :
      ∀ m : ℕ,
        (∑ ρ ∈ ball m, g ρ) ≤ C * ((2 : ℝ) ^ n) ^ (lam + δ - ((p : ℝ) + 1)) := by
    intro m
    by_cases hm : m ≤ n + 1
    · have hsum0 : (∑ ρ ∈ ball m, g ρ) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro ρ hρ
        have hnorm : ‖Z.z ρ‖ ≤ (2 : ℝ) ^ m :=
          (Hadamard.OrderOne.mem_zerosBallFinset_of_entire_iff
            (hf_entire := hf_entire) (Z := Z.toZeroSet) (h_zeros_only := h_zeros_only)
            (h_inj := h_inj) (h_z_ne_zero := h_z_ne_zero) m ρ).1 hρ
        have hpow : (2 : ℝ) ^ m ≤ (2 : ℝ) ^ (n + 1) :=
          pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hm
        have : ¬ (2 : ℝ) ^ (n + 1) < ‖Z.z ρ‖ := not_lt_of_ge (le_trans hnorm hpow)
        simp [g, this]
      have hrhs_nonneg : 0 ≤ C * ((2 : ℝ) ^ n) ^ (lam + δ - ((p : ℝ) + 1)) := by
        have : 0 ≤ ((2 : ℝ) ^ n) ^ (lam + δ - ((p : ℝ) + 1)) :=
          Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ n) _
        exact mul_nonneg hC_nonneg this
      simpa [hsum0] using hrhs_nonneg
    · have hm_ge : n + 1 < m := lt_of_not_ge hm
      let t : ℕ := m - (n + 1)
      have hm_eq : n + 1 + t = m := Nat.add_sub_of_le (Nat.le_of_lt hm_ge)
      have hshell :
          ∀ k : ℕ, n + 1 ≤ k →
            (∑ ρ ∈ ball (k + 1) \ ball k, g ρ) ≤ A * q ^ k := by
        intro k hk
        have hRcount_le' : Rcount ≤ (2 : ℝ) ^ (k + 1) := by
          have hn₀_le_k1 : n₀ ≤ k + 1 := by omega
          exact hRcount_le.trans
            (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hn₀_le_k1)
        have hsum_ball :
            (∑ ρ ∈ ball (k + 1), w ρ) ≤ Ccount * ((2 : ℝ) ^ (k + 1)) ^ (lam + δ) := by
          have hcount_ball := hW_le ((2 : ℝ) ^ (k + 1)) hRcount_le'
          simpa [hball_finsum, ball] using hcount_ball
        exact dyadic_shell_sum_bound Z.z w (fun ρ => by positivity [w]) ball
          (fun j ρ => Hadamard.OrderOne.mem_zerosBallFinset_of_entire_iff
            (hf_entire := hf_entire) (Z := Z.toZeroSet) (h_zeros_only := h_zeros_only)
            (h_inj := h_inj) (h_z_ne_zero := h_z_ne_zero) j ρ)
          p n k hk Ccount lam δ hsum_ball
      have hind :
          ∀ j : ℕ,
            (∑ ρ ∈ ball (n + 1 + j), g ρ) ≤
              A * (∑ i ∈ Finset.range j, q ^ (n + 1 + i)) := by
        intro j
        induction j with
        | zero =>
            have hsum0 : (∑ ρ ∈ ball (n + 1), g ρ) = 0 := by
              refine Finset.sum_eq_zero ?_
              intro ρ hρ
              have hnorm : ‖Z.z ρ‖ ≤ (2 : ℝ) ^ (n + 1) :=
                (Hadamard.OrderOne.mem_zerosBallFinset_of_entire_iff
                  (hf_entire := hf_entire) (Z := Z.toZeroSet) (h_zeros_only := h_zeros_only)
                  (h_inj := h_inj) (h_z_ne_zero := h_z_ne_zero) (n + 1) ρ).1 hρ
              have : ¬ (2 : ℝ) ^ (n + 1) < ‖Z.z ρ‖ := not_lt_of_ge hnorm
              simp [g, this]
            simp [ball, hsum0]
        | succ j ih =>
            set k : ℕ := n + 1 + j
            have hk : n + 1 ≤ k := Nat.le_add_right _ _
            have hdecomp :=
              (Finset.sum_sdiff (s₁ := ball k) (s₂ := ball (k + 1)) (f := g) (hsub_ball k)).symm
            have hshell_le :
                (∑ ρ ∈ ball (k + 1) \ ball k, g ρ) ≤ A * q ^ k := hshell k hk
            have hgeom :
                (∑ i ∈ Finset.range (j + 1), q ^ (n + 1 + i))
                  = (∑ i ∈ Finset.range j, q ^ (n + 1 + i)) + q ^ k := by
              simpa [k, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
                (Finset.sum_range_succ (f := fun i => q ^ (n + 1 + i)) j)
            have ih' :
                (∑ ρ ∈ ball k, g ρ) ≤ A * (∑ i ∈ Finset.range j, q ^ (n + 1 + i)) := by
              simpa [k, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ih
            calc
              (∑ ρ ∈ ball (k + 1), g ρ)
                  = (∑ ρ ∈ ball (k + 1) \ ball k, g ρ) + (∑ ρ ∈ ball k, g ρ) := by
                        simpa [k, add_assoc, add_comm, add_left_comm] using hdecomp
              _ ≤ A * q ^ k + A * (∑ i ∈ Finset.range j, q ^ (n + 1 + i)) := by
                        gcongr
              _ = A * ((∑ i ∈ Finset.range j, q ^ (n + 1 + i)) + q ^ k) := by
                        ring
              _ = A * (∑ i ∈ Finset.range (j + 1), q ^ (n + 1 + i)) := by
                        rw [hgeom]
      have hfinite_le :
          (∑ ρ ∈ ball m, g ρ) ≤ A * (∑ i ∈ Finset.range t, q ^ (n + 1 + i)) := by
        simpa [hm_eq, ball] using hind t
      have hgeom_le :
          (∑ i ∈ Finset.range t, q ^ (n + 1 + i)) ≤ (q ^ (n + 1)) * (1 - q)⁻¹ :=
        geometric_sum_from_le q hq_pos hq_lt_one n t
      have hconst :
          A * (q ^ (n + 1) * (1 - q)⁻¹) =
            C * ((2 : ℝ) ^ n) ^ (lam + δ - ((p : ℝ) + 1)) := by
        have hqpow :
            q ^ n = ((2 : ℝ) ^ n) ^ (lam + δ - ((p : ℝ) + 1)) := by
          dsimp [q]
          exact
            Real.rpow_pow_comm (x := (2 : ℝ)) (hx := by positivity)
              (lam + δ - ((p : ℝ) + 1)) n
        have hqsucc : q ^ (n + 1) = q ^ n * q := by
          simp [pow_succ]
        calc
          A * (q ^ (n + 1) * (1 - q)⁻¹) = A * q / (1 - q) * q ^ n := by
                rw [hqsucc]
                ring_nf
          _ = C * q ^ n := by
                simp [C, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
          _ = C * ((2 : ℝ) ^ n) ^ (lam + δ - ((p : ℝ) + 1)) := by
                rw [hqpow]
      calc
        (∑ ρ ∈ ball m, g ρ) ≤ A * (∑ i ∈ Finset.range t, q ^ (n + 1 + i)) := hfinite_le
        _ ≤ A * (q ^ (n + 1) * (1 - q)⁻¹) := by
              gcongr
        _ = C * ((2 : ℝ) ^ n) ^ (lam + δ - ((p : ℝ) + 1)) := hconst
  have htsum_g :
      (∑' ρ : Z.Zero, g ρ) ≤ C * ((2 : ℝ) ^ n) ^ (lam + δ - ((p : ℝ) + 1)) :=
    tsum_le_of_cofinal_finset_bound ball g (by positivity) hg_nonneg
      (cofinal_zerosBallFinset_of_entire hf_entire Z h_zeros_only h_inj h_z_ne_zero) hball
  have hsub :
      (∑' ρ : ({ρ : Z.Zero | (2 : ℝ) ^ (n + 1) < ‖Z.z ρ‖} : Set Z.Zero),
          (Z.mult ρ.val : ℝ) / ‖Z.z ρ.val‖ ^ (p + 1))
        = ∑' ρ : Z.Zero, g ρ := by
    simpa [g, Set.indicator, Set.mem_ofPred_eq] using
      (tsum_subtype
        (s := ({ρ : Z.Zero | (2 : ℝ) ^ (n + 1) < ‖Z.z ρ‖} : Set Z.Zero))
        (f := fun ρ : Z.Zero => (Z.mult ρ : ℝ) / ‖Z.z ρ‖ ^ (p + 1)))
  rw [hsub]
  exact htsum_g

/-!
## Step 2. Canonical product convergence and zero structure

**Target.** With the summability from Step 1, the rank-`p` canonical
product `P(z) := ∏ E_p(z/Z.z ρ)^{mult ρ}` converges locally uniformly on
`ℂ`. So `P` is entire, and `analyticOrderNatAt P (Z.z ρ) = Z.mult ρ` at
each zero, and `P(z) = 0 ↔ ∃ ρ, z = Z.z ρ`.

Existing infrastructure:
  * `Hadamard.OrderOne.MultipliableFactors.lean`,
    `Hadamard.OrderOne.LocallyUniformProduct.lean` give the rank-1 case.

LaTeX: $|E_p(w) - 1| \le |w|^{p+1}$ for $|w| \le 1/2$ (standard). Hence on
a compact disk $|z| \le R$, summing $|E_p(z/a_n)^{m_n} - 1| \le C\,(R/|a_n|)^{p+1} \cdot m_n$
for $|a_n| \ge 2R$ and applying the M-test yields local uniform convergence.
-/

/-- **Summability of `1/‖zWithMultiplicity i‖^(p+1)` over the sigma index type.**

This is the bridge between the multiplicity-weighted summability hypothesis
`Summable (fun ρ : Z.Zero => (Z.mult ρ : ℝ) / ‖Z.z ρ‖ ^ (p + 1))` (weighted
over distinct zeros) and the library-level hypothesis
`Summable (fun i : Z.ZeroWithMultiplicity => 1 / ‖Z.zWithMultiplicity i‖ ^ (p + 1))`
(over the repeating sigma index). -/
lemma summable_inv_norm_pow_zWithMultiplicity
    {f : ℂ → ℂ} (Z : ZeroSetMultiplicity f) {p : ℕ}
    (hsum : Summable (fun ρ : Z.Zero => (Z.mult ρ : ℝ) / ‖Z.z ρ‖ ^ (p + 1))) :
    Summable
      (fun i : Z.ZeroWithMultiplicity =>
        (1 : ℝ) / ‖Z.zWithMultiplicity i‖ ^ (p + 1)) := by
  classical
  -- Sigma-summability from summability of row sums plus nonneg entries.
  have hnonneg : ∀ i : Z.ZeroWithMultiplicity,
      0 ≤ (1 : ℝ) / ‖Z.zWithMultiplicity i‖ ^ (p + 1) := by
    intro i; positivity
  refine (summable_sigma_of_nonneg hnonneg).2 ?_
  refine ⟨fun _ => summable_of_hasFiniteSupport (Set.toFinite _), ?_⟩
  -- Target: `Summable (fun ρ => ∑' k, 1/‖Z.z ρ‖^(p+1))`.
  -- Each inner tsum is `(mult ρ : ℝ) * (1/‖Z.z ρ‖^(p+1)) = Z.mult ρ / ‖Z.z ρ‖^(p+1)`.
  refine hsum.congr (fun ρ => ?_)
  -- The sigma entries at `⟨ρ, k⟩` are by definition just `Z.z ρ`, so the tsum over
  -- `Fin (Z.mult ρ)` of a constant equals `(mult ρ : ℝ) * constant`.
  calc
    (Z.mult ρ : ℝ) / ‖Z.z ρ‖ ^ (p + 1)
        = (Z.mult ρ : ℝ) * ((1 : ℝ) / ‖Z.z ρ‖ ^ (p + 1)) := by
          rw [mul_one_div]
      _ = ∑ _k : Fin (Z.mult ρ), (1 : ℝ) / ‖Z.z ρ‖ ^ (p + 1) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = ∑' k : Fin (Z.mult ρ), (1 : ℝ) / ‖Z.zWithMultiplicity ⟨ρ, k⟩‖ ^ (p + 1) := by
          rw [tsum_fintype]
          rfl

/-- **Rank-`p` canonical product is entire.** -/
theorem canonicalProductZeroSetMultiplicityRank_differentiable
    {f : ℂ → ℂ} (Z : ZeroSetMultiplicity f) {p : ℕ}
    (hsum : Summable (fun ρ : Z.Zero => (Z.mult ρ : ℝ) / ‖Z.z ρ‖ ^ (p + 1)))
    (h_z_ne_zero : ∀ ρ : Z.Zero, Z.z ρ ≠ 0) :
    Differentiable ℂ (canonicalProductZeroSetMultiplicityRank Z p) := by
  -- Lift `h_z_ne_zero` to the sigma type.
  have hz0 : ∀ i : Z.ZeroWithMultiplicity, Z.zWithMultiplicity i ≠ 0 := by
    intro i
    exact h_z_ne_zero i.1
  -- Lift summability to the sigma type.
  have hsum' :
      Summable (fun i : Z.ZeroWithMultiplicity =>
        (1 : ℝ) / ‖Z.zWithMultiplicity i‖ ^ (p + 1)) :=
    summable_inv_norm_pow_zWithMultiplicity (f := f) (Z := Z) (p := p) hsum
  -- Invoke the library's rank-`p` locally-uniform product / differentiability.
  exact
    Hadamard.OrderOne.differentiable_tprod_weierstrass_E_of_summable_inv_norm_pow
      (z := Z.zWithMultiplicity) (p := p) hz0 hsum'

/-- **The canonical product vanishes exactly on the zero set.** -/
theorem canonicalProductZeroSetMultiplicityRank_eq_zero_iff
    {f : ℂ → ℂ} (Z : ZeroSetMultiplicity f) {p : ℕ}
    (hsum : Summable (fun ρ : Z.Zero => (Z.mult ρ : ℝ) / ‖Z.z ρ‖ ^ (p + 1)))
    (h_inj : Function.Injective Z.z)
    (h_z_ne_zero : ∀ ρ : Z.Zero, Z.z ρ ≠ 0) (s : ℂ) :
    canonicalProductZeroSetMultiplicityRank Z p s = 0 ↔
      ∃ ρ : Z.Zero, s = Z.z ρ := by
  classical
  let _ := h_inj
  have hz0 : ∀ i : Z.ZeroWithMultiplicity, Z.zWithMultiplicity i ≠ 0 := fun i =>
    h_z_ne_zero i.1
  have hsum' :
      Summable (fun i : Z.ZeroWithMultiplicity =>
        (1 : ℝ) / ‖Z.zWithMultiplicity i‖ ^ (p + 1)) :=
    summable_inv_norm_pow_zWithMultiplicity (f := f) (Z := Z) (p := p) hsum
  constructor
  · -- Forward: if the product is 0, then some factor is 0, so `s = Z.z ρ` for some `ρ`.
    intro hP
    by_contra hne
    push Not at hne
    -- If `s ≠ Z.z ρ` for all `ρ`, then `s ≠ Z.zWithMultiplicity i` for all sigma `i`.
    have hx : ∀ i : Z.ZeroWithMultiplicity, s ≠ Z.zWithMultiplicity i := by
      intro i hs
      exact hne i.1 hs
    have hne_prod :
        (∏' i : Z.ZeroWithMultiplicity,
            weierstrassE p (s / Z.zWithMultiplicity i)) ≠ 0 :=
      Hadamard.OrderOne.tprod_weierstrass_E_div_ne_zero_of_summable_inv_norm_pow
        (z := Z.zWithMultiplicity) (p := p) hz0 hsum' s hx
    exact hne_prod hP
  · -- Backward: if `s = Z.z ρ₀` for some `ρ₀`, the factor at any `i` with `i.1 = ρ₀`
    -- is `E_p(Z.z ρ₀ / Z.z ρ₀) = E_p(1) = 0`, so the tprod is 0.
    rintro ⟨ρ₀, rfl⟩
    -- Need `Z.mult ρ₀ > 0` to have at least one such `i` in `Fin (Z.mult ρ₀)`.
    have hmult_pos : 0 < Z.mult ρ₀ := Z.mult_pos ρ₀
    -- Pick the 0-th repetition.
    let i₀ : Z.ZeroWithMultiplicity := ⟨ρ₀, ⟨0, hmult_pos⟩⟩
    have hi0_eq : Z.zWithMultiplicity i₀ = Z.z ρ₀ := rfl
    have hE_zero :
        weierstrassE p (Z.z ρ₀ / Z.zWithMultiplicity i₀) = 0 := by
      rw [hi0_eq]
      rw [div_self (h_z_ne_zero ρ₀)]
      exact weierstrass_E_at_one p
    -- A tprod with a zero factor is zero.
    have hex :
        ∃ i : Z.ZeroWithMultiplicity,
          weierstrassE p (Z.z ρ₀ / Z.zWithMultiplicity i) = 0 := ⟨i₀, hE_zero⟩
    exact tprod_of_exists_eq_zero hex

/-- **Generic sigma tprod reindexing for the Weierstrass product.**

General type-theoretic version: given an index type `ι`, a family `z : ι → ℂ`
of nonzero points, a multiplicity function `m : ι → ℕ`, and summability of
the weighted inverse power, the sigma tprod over `Σ i, Fin (m i)` equals the
iterated power form `∏' i, E_p(s/z i)^(m i)`.

**Elaboration note.** Using `hmul.tprod_sigma` directly triggers a `whnf`
timeout from typeclass resolution exploring instance candidates. We work
around this by passing the inner multipliability explicitly via
`Multipliable.tprod_sigma'`, which bypasses the automatic `sigma_factor`
derivation. -/
lemma tprod_sigma_weierstrass_E_eq_tprod_pow_generic
    {ι : Type 0} {z : ι → ℂ} {m : ι → ℕ} {p : ℕ}
    (hz0 : ∀ i : ι, z i ≠ 0)
    (hsum : Summable (fun i : ι => (m i : ℝ) / ‖z i‖ ^ (p + 1)))
    (s : ℂ) :
    (∏' j : Σ i : ι, Fin (m i), weierstrassE p (s / z j.1)) =
      ∏' i : ι, weierstrassE p (s / z i) ^ m i := by
  classical
  have hz0_sigma : ∀ j : Σ i : ι, Fin (m i), z j.1 ≠ 0 := fun j => hz0 j.1
  -- Summability on the sigma type: `∑_{(i,k)} 1/‖z i‖^(p+1) = ∑_i (m i)/‖z i‖^(p+1)`.
  have hsum_sigma :
      Summable (fun j : Σ i : ι, Fin (m i) =>
        (1 : ℝ) / ‖z j.1‖ ^ (p + 1)) := by
    have hnonneg : ∀ j : Σ i : ι, Fin (m i),
        0 ≤ (1 : ℝ) / ‖z j.1‖ ^ (p + 1) := by
      intro j; positivity
    refine (summable_sigma_of_nonneg hnonneg).2 ?_
    refine ⟨fun _ => Summable.of_finite, ?_⟩
    refine hsum.congr (fun i => ?_)
    have heq :
        (fun b : Fin (m i) => (1 : ℝ) / ‖z (⟨i, b⟩ : Σ i : ι, Fin (m i)).1‖ ^ (p + 1))
          = (fun _ : Fin (m i) => (1 : ℝ) / ‖z i‖ ^ (p + 1)) := by
      funext b; rfl
    rw [tsum_fintype, heq, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_one_div]
  -- Multipliability on the sigma type via the library lemma.
  have hmul :
      Multipliable (fun j : Σ i : ι, Fin (m i) => weierstrassE p (s / z j.1)) :=
    Hadamard.OrderOne.multipliable_weierstrass_E_of_summable_inv_norm_pow
      (z := fun j : Σ i : ι, Fin (m i) => z j.1) (p := p) hz0_sigma hsum_sigma s
  -- Each fiber is a finite product, hence trivially multipliable.
  have hmul_inner :
      ∀ i : ι, Multipliable
        (fun k : Fin (m i) => weierstrassE p (s / z (⟨i, k⟩ : Σ i : ι, Fin (m i)).1)) :=
    fun _ => Multipliable.of_finite
  -- Sigma → iterated. Use `tprod_sigma'` (explicit fiber multipliability) rather
  -- than `hmul.tprod_sigma`, which triggers a whnf timeout.
  have hsigma :
      (∏' j : Σ i : ι, Fin (m i), weierstrassE p (s / z j.1)) =
        ∏' (i : ι) (k : Fin (m i)),
          weierstrassE p (s / z (⟨i, k⟩ : Σ i : ι, Fin (m i)).1) :=
    Multipliable.tprod_sigma' hmul_inner hmul
  rw [hsigma]
  refine tprod_congr (fun i => ?_)
  -- Inner tprod: reduce `⟨i, k⟩.1` to `i`, then constant product.
  have hconst :
      (fun k : Fin (m i) => weierstrassE p (s / z (⟨i, k⟩ : Σ i : ι, Fin (m i)).1))
        = (fun _ : Fin (m i) => weierstrassE p (s / z i)) := by
    funext k; rfl
  rw [hconst, tprod_fintype, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-!
### Preliminaries: pointwise analytic order of a single Weierstrass factor

`E_p(s / Z.z ρ)` has a simple zero at `s = Z.z ρ`. Concretely, the substitution
`s ↦ s / Z.z ρ` is a linear map with derivative `1/Z.z ρ ≠ 0` sending `Z.z ρ`
to `1`, and `E_p` has analytic order 1 at `1`, so the composition has
analytic order 1 at `Z.z ρ`.
-/

/-- **`E_p(s / a)` has `analyticOrderNatAt` equal to 1 at `s = a`** (`a ≠ 0`). -/
lemma analyticOrderNatAt_weierstrass_E_div {p : ℕ} {a : ℂ} (ha : a ≠ 0) :
    analyticOrderNatAt (fun s : ℂ => weierstrassE p (s / a)) a = 1 := by
  classical
  -- The "inner" map `g(s) := s / a` is analytic with `g a = 1` and `deriv g a = 1/a ≠ 0`.
  let g : ℂ → ℂ := fun s => s / a
  have hg_diff : Differentiable ℂ g := by fun_prop
  have hg_analytic : AnalyticAt ℂ g a := (hg_diff.analyticAt a)
  have hg_val : g a = 1 := by
    simp [g, div_self ha]
  -- `deriv g = (1 : ℂ) / a`, so it is nonzero because `a ≠ 0`.
  have hg_deriv : deriv g a = 1 / a := by
    have : HasDerivAt g (1 / a) a := by
      have : HasDerivAt (fun s : ℂ => s / a) ((1 : ℂ) / a) a := by
        simpa [div_eq_mul_inv] using (hasDerivAt_id a).mul_const (a⁻¹)
      exact this
    exact this.deriv
  have hg_deriv_ne : deriv g a ≠ 0 := by
    rw [hg_deriv]
    exact one_div_ne_zero ha
  -- Composition transports the analytic order from `g a = 1` back to `a`.
  have hcomp :
      analyticOrderAt (weierstrassE p ∘ g) a =
        analyticOrderAt (weierstrassE p) (g a) :=
    analyticOrderAt_comp_of_deriv_ne_zero (f := weierstrassE p) (g := g)
      (z₀ := a) hg_analytic hg_deriv_ne
  have hE_order : analyticOrderAt (weierstrassE p) (1 : ℂ) = 1 :=
    Hadamard.weierstrass_E_analyticOrderAt_one p
  have horder :
      analyticOrderAt (fun s : ℂ => weierstrassE p (s / a)) a = 1 := by
    rw [← hE_order, ← hg_val]
    exact hcomp
  unfold analyticOrderNatAt
  rw [horder]
  rfl

/-- **Power-form rewrite of the canonical product.**

Specialization of `tprod_sigma_weierstrass_E_eq_tprod_pow_generic` to a
`ZeroSetMultiplicity`. Provides the textbook form
`P(s) = ∏' ρ, E_p(s/Z.z ρ)^(Z.mult ρ)`. -/
lemma canonicalProductZeroSetMultiplicityRank_eq_tprod_pow
    {f : ℂ → ℂ} (Z : ZeroSetMultiplicity f) {p : ℕ}
    (hsum :
      Summable (fun ρ : Z.Zero => (Z.mult ρ : ℝ) / ‖Z.z ρ‖ ^ (p + 1)))
    (h_z_ne_zero : ∀ ρ : Z.Zero, Z.z ρ ≠ 0) (s : ℂ) :
    canonicalProductZeroSetMultiplicityRank Z p s =
      ∏' ρ : Z.Zero, weierstrassE p (s / Z.z ρ) ^ Z.mult ρ := by
  -- Apply the generic version to `ι := Z.Zero`, `z := Z.z`, `m := Z.mult`.
  -- The LHS of the generic result is `∏' j : Σ ρ, Fin (Z.mult ρ), E_p(s/Z.z j.1)`,
  -- which equals `canonicalProductZeroSetMultiplicityRank Z p s` by definition.
  exact tprod_sigma_weierstrass_E_eq_tprod_pow_generic
    (z := Z.z) (m := Z.mult) (p := p) h_z_ne_zero hsum s

/-- **Generic helper: summability on the sigma type from weighted summability.**

Reused by both the multipliability and non-vanishing helpers below. -/
private lemma summable_sigma_inv_norm_pow_generic
    {ι : Type 0} {z : ι → ℂ} {m : ι → ℕ} {p : ℕ}
    (hsum : Summable (fun i : ι => (m i : ℝ) / ‖z i‖ ^ (p + 1))) :
    Summable (fun j : Σ i : ι, Fin (m i) => (1 : ℝ) / ‖z j.1‖ ^ (p + 1)) := by
  classical
  have hnonneg : ∀ j : Σ i : ι, Fin (m i),
      0 ≤ (1 : ℝ) / ‖z j.1‖ ^ (p + 1) := fun j => by positivity
  refine (summable_sigma_of_nonneg hnonneg).2 ?_
  refine ⟨fun _ => Summable.of_finite, ?_⟩
  refine hsum.congr (fun i => ?_)
  have heq :
      (fun b : Fin (m i) =>
          (1 : ℝ) / ‖z (⟨i, b⟩ : Σ i : ι, Fin (m i)).1‖ ^ (p + 1))
        = (fun _ : Fin (m i) => (1 : ℝ) / ‖z i‖ ^ (p + 1)) := by
    funext b; rfl
  rw [tsum_fintype, heq, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one_div]

/-- **Generic multipliability of the iterated power form.** -/
lemma multipliable_pow_weierstrass_E_div_generic
    {ι : Type 0} {z : ι → ℂ} {m : ι → ℕ} {p : ℕ}
    (hz0 : ∀ i : ι, z i ≠ 0)
    (hsum : Summable (fun i : ι => (m i : ℝ) / ‖z i‖ ^ (p + 1)))
    (s : ℂ) :
    Multipliable
      (fun i : ι => weierstrassE p (s / z i) ^ m i) := by
  classical
  have hz0_sigma : ∀ j : Σ i : ι, Fin (m i), z j.1 ≠ 0 := fun j => hz0 j.1
  have hsum_sigma := summable_sigma_inv_norm_pow_generic (z := z) (m := m) (p := p) hsum
  have hmul_sigma :
      Multipliable
        (fun j : Σ i : ι, Fin (m i) => weierstrassE p (s / z j.1)) :=
    Hadamard.OrderOne.multipliable_weierstrass_E_of_summable_inv_norm_pow
      (z := fun j : Σ i : ι, Fin (m i) => z j.1) (p := p) hz0_sigma hsum_sigma s
  have hmul_inner :
      ∀ i : ι, Multipliable
        (fun k : Fin (m i) =>
          weierstrassE p (s / z (⟨i, k⟩ : Σ i : ι, Fin (m i)).1)) :=
    fun _ => Multipliable.of_finite
  -- Outer multipliability via `sigma'`.
  have houter_mul :
      Multipliable
        (fun i : ι =>
          ∏' k : Fin (m i),
            weierstrassE p (s / z (⟨i, k⟩ : Σ i : ι, Fin (m i)).1)) :=
    hmul_sigma.sigma' hmul_inner
  -- Reduce inner finite product to a power.
  have houter_eq :
      (fun i : ι =>
          ∏' k : Fin (m i),
            weierstrassE p (s / z (⟨i, k⟩ : Σ i : ι, Fin (m i)).1))
        = (fun i : ι => weierstrassE p (s / z i) ^ m i) := by
    funext i
    have hconst :
        (fun k : Fin (m i) =>
            weierstrassE p (s / z (⟨i, k⟩ : Σ i : ι, Fin (m i)).1))
          = (fun _ : Fin (m i) => weierstrassE p (s / z i)) := by
      funext k; rfl
    rw [hconst, tprod_fintype, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [houter_eq] at houter_mul
  exact houter_mul

/-- **Generic non-vanishing of the iterated power form.** -/
lemma tprod_pow_weierstrass_E_div_ne_zero_generic
    {ι : Type 0} {z : ι → ℂ} {m : ι → ℕ} {p : ℕ}
    (hz0 : ∀ i : ι, z i ≠ 0)
    (hsum : Summable (fun i : ι => (m i : ℝ) / ‖z i‖ ^ (p + 1)))
    (x : ℂ) (hx : ∀ i : ι, x ≠ z i) :
    (∏' i : ι, weierstrassE p (x / z i) ^ m i) ≠ 0 := by
  classical
  have hz0_sigma : ∀ j : Σ i : ι, Fin (m i), z j.1 ≠ 0 := fun j => hz0 j.1
  have hsum_sigma := summable_sigma_inv_norm_pow_generic (z := z) (m := m) (p := p) hsum
  have hxsigma : ∀ j : Σ i : ι, Fin (m i), x ≠ z j.1 := fun j => hx j.1
  have hne_sigma :
      (∏' j : Σ i : ι, Fin (m i), weierstrassE p (x / z j.1)) ≠ 0 :=
    Hadamard.OrderOne.tprod_weierstrass_E_div_ne_zero_of_summable_inv_norm_pow
      (z := fun j : Σ i : ι, Fin (m i) => z j.1) (p := p) hz0_sigma hsum_sigma x hxsigma
  have hconv :
      (∏' j : Σ i : ι, Fin (m i), weierstrassE p (x / z j.1)) =
        ∏' i : ι, weierstrassE p (x / z i) ^ m i :=
    tprod_sigma_weierstrass_E_eq_tprod_pow_generic
      (z := z) (m := m) (p := p) hz0 hsum x
  rw [hconv] at hne_sigma
  exact hne_sigma

/-- **`ZeroSetMultiplicity` wrapper**
for `multipliable_pow_weierstrass_E_div_generic`. -/
lemma multipliable_pow_weierstrass_E_div_of_summable
    {f : ℂ → ℂ} (Z : ZeroSetMultiplicity f) {p : ℕ}
    (hsum : Summable (fun ρ : Z.Zero => (Z.mult ρ : ℝ) / ‖Z.z ρ‖ ^ (p + 1)))
    (h_z_ne_zero : ∀ ρ : Z.Zero, Z.z ρ ≠ 0) (s : ℂ) :
    Multipliable
      (fun ρ : Z.Zero => weierstrassE p (s / Z.z ρ) ^ Z.mult ρ) :=
  multipliable_pow_weierstrass_E_div_generic
    (z := Z.z) (m := Z.mult) (p := p) h_z_ne_zero hsum s

/-- Decompose `Σ i : ι, Fin (m i)` into the fiber over `b` and the rest. -/
noncomputable def sigmaFiberSplitEquiv
    {ι : Type 0} [DecidableEq ι] {m : ι → ℕ} (b : ι) :
    (Σ i : ι, Fin (m i)) ≃
      Fin (m b) ⊕ (Σ i : {i : ι // i ≠ b}, Fin (m i.val)) :=
  { toFun := fun j =>
      if h : j.1 = b then Sum.inl (h ▸ j.2)
      else Sum.inr ⟨⟨j.1, h⟩, j.2⟩
    invFun := fun x =>
      match x with
      | Sum.inl k => ⟨b, k⟩
      | Sum.inr j => ⟨j.1.val, j.2⟩
    left_inv := fun ⟨i, k⟩ => by
      simp only
      split_ifs with h
      · subst h; rfl
      · rfl
    right_inv := fun x => by
      match x with
      | Sum.inl k => simp
      | Sum.inr ⟨⟨i, hi⟩, k⟩ => simp [hi] }

-- This proof expands several `Equiv.tprod_eq` rewrites and is expensive to elaborate.
/-- **Splitting lemma for the power-form Weierstrass product.**

Split off the factor at index `b`, expressing the rest as a subtype tprod.
Proved via `Equiv.tprod_eq` plus sigma decomposition,
avoiding all typeclass-explosive `Multipliable.*` operations. -/
lemma tprod_pow_weierstrass_E_split_generic
    {ι : Type 0} {z : ι → ℂ} {m : ι → ℕ} {p : ℕ}
    (hz0 : ∀ i : ι, z i ≠ 0)
    (hsum : Summable (fun i : ι => (m i : ℝ) / ‖z i‖ ^ (p + 1)))
    (b : ι) (s : ℂ) :
    (∏' i : ι, weierstrassE p (s / z i) ^ m i) =
      weierstrassE p (s / z b) ^ m b *
        (∏' i : {i : ι // i ≠ b}, weierstrassE p (s / z i.val) ^ m i.val) := by
  classical
  let f : ι → ℂ := fun i => weierstrassE p (s / z i)
  let g : (Σ i : ι, Fin (m i)) → ℂ := fun j => f j.1
  let e := sigmaFiberSplitEquiv (m := m) b
  have hz0_sigma : ∀ j : Σ i : ι, Fin (m i), z j.1 ≠ 0 := fun j => hz0 j.1
  have hsum_sigma :=
    summable_sigma_inv_norm_pow_generic (z := z) (m := m) (p := p) hsum
  have hmul_sigma : Multipliable g :=
    Hadamard.OrderOne.multipliable_weierstrass_E_of_summable_inv_norm_pow
      (z := fun j : Σ i : ι, Fin (m i) => z j.1) (p := p) hz0_sigma hsum_sigma s
  have hmul_inner :
      ∀ i : ι, Multipliable
        (fun k : Fin (m i) =>
          weierstrassE p (s / z (⟨i, k⟩ : Σ i : ι, Fin (m i)).1)) :=
    fun _ => Multipliable.of_finite
  have hsigma_eq :
      (∏' j : Σ i : ι, Fin (m i), g j) =
        ∏' i : ι, weierstrassE p (s / z i) ^ m i := by
    simpa [f, g] using
      (tprod_sigma_weierstrass_E_eq_tprod_pow_generic
        (z := z) (m := m) (p := p) hz0 hsum s)
  let h : Fin (m b) ⊕ (Σ i : {i : ι // i ≠ b}, Fin (m i.val)) → ℂ :=
    fun x => g (e.symm x)
  have hequiv : (∏' j, g j) = ∏' x, h x := (Equiv.tprod_eq e.symm g).symm
  have hmul_left : Multipliable (h ∘ Sum.inl) := Multipliable.of_finite
  have hsum_sub :
      Summable (fun i : {i : ι // i ≠ b} =>
        (m i.val : ℝ) / ‖z i.val‖ ^ (p + 1)) :=
    hsum.comp_injective Subtype.val_injective
  have hcompl_summable :
      Summable (fun j : Σ i : {i : ι // i ≠ b}, Fin (m i.val) =>
        (1 : ℝ) / ‖z j.1.val‖ ^ (p + 1)) := by
    exact summable_sigma_inv_norm_pow_generic
      (z := fun i : {i : ι // i ≠ b} => z i.val)
      (m := fun i : {i : ι // i ≠ b} => m i.val) (p := p) hsum_sub
  have hmul_right_sigma :
      Multipliable (fun j : Σ i : {i : ι // i ≠ b}, Fin (m i.val) =>
        weierstrassE p (s / z j.1.val)) :=
    Hadamard.OrderOne.multipliable_weierstrass_E_of_summable_inv_norm_pow
      (z := fun j : Σ i : {i : ι // i ≠ b}, Fin (m i.val) => z j.1.val)
      (p := p) (fun j => hz0 j.1.val) hcompl_summable s
  have hright_eq :
      (h ∘ Sum.inr) =
        (fun j : Σ i : {i : ι // i ≠ b}, Fin (m i.val) =>
          weierstrassE p (s / z j.1.val)) := by
    funext ⟨⟨i, hi⟩, k⟩; rfl
  have hmul_right : Multipliable (h ∘ Sum.inr) := by rw [hright_eq]; exact hmul_right_sigma
  have hsplit := Multipliable.tprod_sum hmul_left hmul_right
  have hleft_eq : (∏' k, h (Sum.inl k)) = weierstrassE p (s / z b) ^ m b := by
    have : (fun k : Fin (m b) => h (Sum.inl k)) =
        (fun _ : Fin (m b) => weierstrassE p (s / z b)) := by funext; rfl
    rw [this, tprod_fintype, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hright_val :
      (∏' j, h (Sum.inr j)) =
        ∏' i : {i : ι // i ≠ b}, weierstrassE p (s / z i.val) ^ m i.val := by
    rw [show (∏' j, h (Sum.inr j)) = ∏' j, (h ∘ Sum.inr) j from rfl, hright_eq]
    simpa using
      (tprod_sigma_weierstrass_E_eq_tprod_pow_generic
        (z := fun i : {i : ι // i ≠ b} => z i.val)
        (m := fun i : {i : ι // i ≠ b} => m i.val)
        (p := p)
        (fun i => hz0 i.val)
        hsum_sub
        s)
  rw [← hsigma_eq, hequiv, hsplit, hleft_eq, hright_val]

/-- **Multiplicity of the canonical product at each zero matches the prescribed multiplicity.**

Proof:
1. Rewrite to the power form `P(s) = ∏' ρ', E_p(s/Z.z ρ')^(Z.mult ρ')`.
2. Split off the factor at `ρ` via `Multipliable.tprod_subtype_mul_tprod_subtype_compl`:
   `P(s) = E_p(s/Z.z ρ)^(Z.mult ρ) · Q(s)` where `Q` is the complementary
   product over `{ρ' : Z.Zero // ρ' ≠ ρ}`.
3. Compute the order at `Z.z ρ` of the first factor via `analyticOrderAt_pow`
   and `analyticOrderNatAt_weierstrass_E_div`.
4. Show `Q(Z.z ρ) ≠ 0` via the generic non-vanishing lemma applied to the
   subtype.
5. Combine using `analyticOrderNatAt_mul`. -/
theorem analyticOrderNatAt_canonicalProductZeroSetMultiplicityRank
    {f : ℂ → ℂ} (Z : ZeroSetMultiplicity f) {p : ℕ}
    (hsum : Summable (fun ρ : Z.Zero => (Z.mult ρ : ℝ) / ‖Z.z ρ‖ ^ (p + 1)))
    (h_inj : Function.Injective Z.z)
    (h_z_ne_zero : ∀ ρ : Z.Zero, Z.z ρ ≠ 0) (ρ : Z.Zero) :
    analyticOrderNatAt (canonicalProductZeroSetMultiplicityRank Z p)
      (Z.z ρ) = Z.mult ρ := by
  classical
  -- Define the two factors as functions of `s`.
  set f₁ : ℂ → ℂ := fun s => weierstrassE p (s / Z.z ρ) ^ Z.mult ρ with hf₁_def
  set Q : ℂ → ℂ := fun s =>
    ∏' ρ' : {ρ' : Z.Zero // ρ' ≠ ρ},
      weierstrassE p (s / Z.z ρ'.val) ^ Z.mult ρ'.val with hQ_def
  -- `P = f₁ * Q` as functions.
  have hP_fun_eq :
      canonicalProductZeroSetMultiplicityRank Z p = fun s => f₁ s * Q s := by
    funext s
    rw [hf₁_def, hQ_def]
    exact (canonicalProductZeroSetMultiplicityRank_eq_tprod_pow Z hsum h_z_ne_zero s).trans
      (tprod_pow_weierstrass_E_split_generic
        (z := Z.z) (m := Z.mult) (p := p) h_z_ne_zero hsum ρ s)
  -- `f₁` is analytic at `Z.z ρ`.
  have hf₁_diff : Differentiable ℂ f₁ := by
    simp only [hf₁_def]
    exact ((weierstrass_E_differentiable p).comp (by fun_prop)).pow _
  have hf₁_analytic : AnalyticAt ℂ f₁ (Z.z ρ) := hf₁_diff.analyticAt _
  -- `f₁` has analytic order `Z.mult ρ` at `Z.z ρ`.
  have hf₁_order : analyticOrderNatAt f₁ (Z.z ρ) = Z.mult ρ := by
    have hbase :
        analyticOrderNatAt (fun s : ℂ => weierstrassE p (s / Z.z ρ)) (Z.z ρ) = 1 :=
      analyticOrderNatAt_weierstrass_E_div (p := p) (h_z_ne_zero ρ)
    -- f₁ = (s ↦ E_p(s/Z.z ρ)) ^ (Z.mult ρ) as Pi-power.
    have hf₁_eq :
        f₁ = (fun s : ℂ => weierstrassE p (s / Z.z ρ)) ^ Z.mult ρ := by
      funext s; simp [hf₁_def, Pi.pow_apply]
    have hg_an : AnalyticAt ℂ (fun s : ℂ => weierstrassE p (s / Z.z ρ)) (Z.z ρ) :=
      ((weierstrass_E_differentiable p).comp (by fun_prop)).analyticAt _
    rw [hf₁_eq, analyticOrderNatAt_pow hg_an, hbase]
    simp
  -- `Q(Z.z ρ) ≠ 0` (complementary product is nonzero).
  have hQ_ne : Q (Z.z ρ) ≠ 0 := by
    simp only [hQ_def]
    exact tprod_pow_weierstrass_E_div_ne_zero_generic
      (z := fun ρ' : {ρ' : Z.Zero // ρ' ≠ ρ} => Z.z ρ'.val)
      (m := fun ρ' => Z.mult ρ'.val) (p := p)
      (fun ρ' => h_z_ne_zero ρ'.val)
      (hsum.comp_injective Subtype.val_injective) (Z.z ρ)
      (fun ρ' hEq => ρ'.2 (h_inj hEq).symm)
  -- `Q` is analytic at `Z.z ρ` (from the power-form differentiability on the complement subtype).
  have hQ_analytic : AnalyticAt ℂ Q (Z.z ρ) := by
    change ∃ _, _
    have hz0' : ∀ ρ' : {ρ' : Z.Zero // ρ' ≠ ρ}, Z.z ρ'.val ≠ 0 :=
      fun ρ' => h_z_ne_zero ρ'.val
    have hsum' : Summable (fun ρ' : {ρ' : Z.Zero // ρ' ≠ ρ} =>
        (Z.mult ρ'.val : ℝ) / ‖Z.z ρ'.val‖ ^ (p + 1)) :=
      hsum.comp_injective Subtype.val_injective
    -- The complement sigma product is entire by the library lemma.
    have hsum_sigma :=
      summable_sigma_inv_norm_pow_generic
        (z := fun ρ' : {ρ' : Z.Zero // ρ' ≠ ρ} => Z.z ρ'.val)
        (m := fun ρ' => Z.mult ρ'.val) (p := p) hsum'
    -- `Q s = (complement sigma tprod) s` via the conversion lemma.
    -- Use `congr` to show `Q.analyticAt` from the sigma form's `.analyticAt`.
    have hQ_sigma_diff :
        Differentiable ℂ (fun s : ℂ =>
          ∏' j : Σ i : {i : Z.Zero // i ≠ ρ}, Fin (Z.mult i.val),
            weierstrassE p (s / Z.z j.1.val)) :=
      Hadamard.OrderOne.differentiable_tprod_weierstrass_E_of_summable_inv_norm_pow
        (z := fun j : Σ i : {i : Z.Zero // i ≠ ρ}, Fin (Z.mult i.val) => Z.z j.1.val)
        (p := p) (fun j => hz0' j.1) hsum_sigma
    have hQ_eq :
        Q = fun s => ∏' j : Σ i : {i : Z.Zero // i ≠ ρ}, Fin (Z.mult i.val),
          weierstrassE p (s / Z.z j.1.val) := by
      funext s; rw [hQ_def]
      exact (tprod_sigma_weierstrass_E_eq_tprod_pow_generic
        (z := fun ρ' : {ρ' : Z.Zero // ρ' ≠ ρ} => Z.z ρ'.val)
        (m := fun ρ' => Z.mult ρ'.val) (p := p) hz0' hsum' s).symm
    exact (hQ_eq ▸ hQ_sigma_diff).analyticAt _
  -- Combine via `analyticOrderNatAt_mul`.
  have hQ_order : analyticOrderNatAt Q (Z.z ρ) = 0 := by
    simp only [analyticOrderNatAt]
    rw [hQ_analytic.analyticOrderAt_eq_zero.mpr hQ_ne]; rfl
  have hf₁_order_ne_top : analyticOrderAt f₁ (Z.z ρ) ≠ ⊤ := by
    intro htop
    have h0 : analyticOrderNatAt f₁ (Z.z ρ) = 0 := by
      simp only [analyticOrderNatAt, htop]; rfl
    rw [hf₁_order] at h0
    exact (Nat.pos_iff_ne_zero.mp (Z.mult_pos ρ)) h0
  have hQ_order_ne_top : analyticOrderAt Q (Z.z ρ) ≠ ⊤ := by
    rw [Ne, analyticOrderAt_eq_top]
    intro hev
    exact hQ_ne hev.self_of_nhds
  rw [hP_fun_eq, show (fun s => f₁ s * Q s) = f₁ * Q from rfl,
      analyticOrderNatAt_mul hf₁_analytic hQ_analytic hf₁_order_ne_top hQ_order_ne_top,
      hf₁_order, hQ_order, Nat.add_zero]

/-!
## Step 3. The quotient `Q := f / (z^m · P)` is entire and nowhere zero

**Target.** Let `m := analyticOrderNatAt f 0` be the multiplicity of the
zero of `f` at the origin (possibly `0`). Define
`Q(z) := f(z) / (z^m · P(z))` as an `update`-patched function at each
`a_n` and at `0`. Then `Q` is entire and never vanishes.

Existing infrastructure:
  * `Hadamard.OrderOne.QuotientCancellation.exists_analyticAt_update_div_of_analyticOrderNatAt_eq`
    is the pointwise ingredient (removable singularity at a common zero).
  * `Hadamard.OrderOne.Factorization.quotient_entire` handles the rank-1
    simple-zero global assembly; we generalize to rank-`p` + multiplicity.

We package `Q` as a single entire function `Q : ℂ → ℂ` with
`hQ_entire : Differentiable ℂ Q`, `hQ_ne : ∀ z, Q z ≠ 0`, and a
factorization identity `hfact : ∀ z, f z = z^m · (P z) · Q z`.
-/

/-- **Existence of the entire nowhere-zero quotient `Q = f / P`.**

This is the strict form assuming `f 0 ≠ 0` (equivalently, `analyticOrderNatAt f 0 = 0`).
A wrapper that handles the zero-at-origin case by pre-processing `f(z) / z^m` should be
added later (Conway p.289 reduction). -/
theorem exists_quotient_entire
    {f : ℂ → ℂ} (hf_entire : Differentiable ℂ f)
    (Z : ZeroSetMultiplicity f) {p : ℕ}
    (hsum : Summable (fun ρ : Z.Zero => (Z.mult ρ : ℝ) / ‖Z.z ρ‖ ^ (p + 1)))
    (h_zeros_only : ∀ s : ℂ, f s = 0 ↔ ∃ ρ : Z.Zero, s = Z.z ρ)
    (h_inj : Function.Injective Z.z)
    (h_z_ne_zero : ∀ ρ : Z.Zero, Z.z ρ ≠ 0)
    (h_mult : ∀ ρ : Z.Zero, analyticOrderNatAt f (Z.z ρ) = Z.mult ρ) :
    ∃ Q : ℂ → ℂ,
      Differentiable ℂ Q ∧ (∀ z : ℂ, Q z ≠ 0) ∧
      (∀ z : ℂ, f z = canonicalProductZeroSetMultiplicityRank Z p z * Q z) := by
  classical
  set P := canonicalProductZeroSetMultiplicityRank Z p with hP_def
  -- Step 0: Infrastructure about P
  have hP_diff : Differentiable ℂ P :=
    canonicalProductZeroSetMultiplicityRank_differentiable Z hsum h_z_ne_zero
  have hP_zero_iff : ∀ s, P s = 0 ↔ ∃ ρ, s = Z.z ρ :=
    canonicalProductZeroSetMultiplicityRank_eq_zero_iff Z hsum h_inj h_z_ne_zero
  have hP_mult : ∀ ρ, analyticOrderNatAt P (Z.z ρ) = Z.mult ρ :=
    analyticOrderNatAt_canonicalProductZeroSetMultiplicityRank Z hsum h_inj h_z_ne_zero
  -- Analytic orders at zeros are finite (Z.mult ≥ 1 but toNat(⊤) = 0)
  have hP_ord_ne_top : ∀ ρ, analyticOrderAt P (Z.z ρ) ≠ ⊤ := by
    intro ρ htop
    have : analyticOrderNatAt P (Z.z ρ) = 0 := by simp only [analyticOrderNatAt, htop]; rfl
    rw [hP_mult ρ] at this; exact (Nat.pos_iff_ne_zero.mp (Z.mult_pos ρ)) this
  have hf_ord_ne_top : ∀ ρ, analyticOrderAt f (Z.z ρ) ≠ ⊤ := by
    intro ρ htop
    have : analyticOrderNatAt f (Z.z ρ) = 0 := by simp only [analyticOrderNatAt, htop]; rfl
    rw [h_mult ρ] at this; exact (Nat.pos_iff_ne_zero.mp (Z.mult_pos ρ)) this
  -- Step 1: At every z₀, the quotient f/P extends analytically
  have hrem : ∀ z₀ : ℂ, ∃ q : ℂ,
      AnalyticAt ℂ (fun z => if z = z₀ then q else f z / P z) z₀ := by
    intro z₀
    by_cases hPz₀ : P z₀ = 0
    · -- At a zero: use removable singularity (orders match)
      obtain ⟨ρ, rfl⟩ := (hP_zero_iff z₀).mp hPz₀
      exact Hadamard.OrderOne.exists_analyticAt_update_div_of_analyticOrderNatAt_eq
        (hf_entire.analyticAt _) (hP_diff.analyticAt _)
        (hf_ord_ne_top ρ) (hP_ord_ne_top ρ) ((h_mult ρ).trans (hP_mult ρ).symm)
    · -- Away from zeros: f/P is already analytic
      exact ⟨f z₀ / P z₀,
        ((hf_entire.analyticAt z₀).div (hP_diff.analyticAt z₀) hPz₀).congr <|
          by
            filter_upwards with z
            simp only [Pi.div_apply]
            split_ifs with h <;> [rw [h]; rfl]⟩
  -- Step 2: Choose Q from the universal extension
  choose Q hQ_an using hrem
  -- Step 3: Q(z) = f(z)/P(z) whenever P(z) ≠ 0 (by uniqueness of limits)
  have hQ_eq_div : ∀ z, P z ≠ 0 → Q z = f z / P z := by
    intro z hPz
    -- g(w) := if w = z then Q z else f w / P w
    set g : ℂ → ℂ := fun w => if w = z then Q z else f w / P w with hg_def
    -- g is continuous at z (analytic)
    have hg_cont : ContinuousAt g z := (hQ_an z).continuousAt
    -- g = f/P on 𝓝[≠] z
    have hg_fP : g =ᶠ[𝓝[≠] z] fun w => f w / P w :=
      eventually_nhdsWithin_of_forall fun w hw => ite_eq_right hw
    -- f/P is continuous at z
    have hfP_cont : ContinuousAt (fun w => f w / P w) z :=
      hf_entire.continuous.continuousAt.div hP_diff.continuous.continuousAt hPz
    -- g → g(z) along 𝓝[≠] z (from continuity)
    have h1 : Filter.Tendsto g (𝓝[≠] z) (𝓝 (g z)) :=
      hg_cont.tendsto.mono_left nhdsWithin_le_nhds
    -- g → f(z)/P(z) along 𝓝[≠] z (g = f/P there, and f/P is continuous)
    have h2 : Filter.Tendsto g (𝓝[≠] z) (𝓝 (f z / P z)) :=
      (tendsto_congr' hg_fP).mpr (hfP_cont.tendsto.mono_left nhdsWithin_le_nhds)
    -- By uniqueness of limits: g(z) = f(z)/P(z), i.e., Q z = f z / P z
    have hgz : g z = Q z := ite_eq_left rfl
    exact hgz ▸ tendsto_nhds_unique h1 h2
  -- Step 4: Zeros of P are isolated
  have hP_isolated : ∀ ρ : Z.Zero, ∀ᶠ z in 𝓝[≠] (Z.z ρ), P z ≠ 0 := by
    intro ρ
    rcases (hP_diff.analyticAt (Z.z ρ)).eventually_eq_zero_or_eventually_ne_zero with h | h
    · exact absurd (analyticOrderAt_eq_top.mpr h) (hP_ord_ne_top ρ)
    · exact h
  -- Step 5: Q is differentiable everywhere
  have hQ_diff : Differentiable ℂ Q := by
    intro z₀
    by_cases hPz₀ : P z₀ = 0
    · -- At a zero: Q agrees with the analytic extension in a neighborhood
      obtain ⟨ρ, rfl⟩ := (hP_zero_iff z₀).mp hPz₀
      have h_imp := eventually_nhdsWithin_iff.mp (hP_isolated ρ)
      have hQ_near : Q =ᶠ[𝓝 (Z.z ρ)]
          fun z => if z = Z.z ρ then Q (Z.z ρ) else f z / P z := by
        filter_upwards [h_imp] with z hz
        by_cases heq : z = Z.z ρ
        · subst heq; simp
        · rw [ite_eq_right heq, hQ_eq_div z (hz heq)]
      exact (hQ_an (Z.z ρ)).differentiableAt.congr_of_eventuallyEq hQ_near
    · -- Away from zeros: Q = f/P in a neighborhood
      have hPne := hP_diff.continuous.continuousAt.eventually_ne hPz₀
      have hQ_near : Q =ᶠ[𝓝 z₀] fun z => f z / P z := by
        filter_upwards [hPne] with z hz; exact hQ_eq_div z hz
      exact (hf_entire.differentiableAt.div hP_diff.differentiableAt hPz₀).congr_of_eventuallyEq
        hQ_near
  -- Step 6: f = P * Q
  have hfact : ∀ z, f z = P z * Q z := by
    intro z
    by_cases hPz : P z = 0
    · rw [hPz, zero_mul]; exact (h_zeros_only z).mpr ((hP_zero_iff z).mp hPz)
    · rw [hQ_eq_div z hPz, mul_comm, div_mul_cancel₀ (f z) hPz]
  -- Step 7: Q is nowhere zero
  have hQ_ne : ∀ z, Q z ≠ 0 := by
    intro z
    by_cases hPz : P z = 0
    · -- At a zero: multiplicity argument
      obtain ⟨ρ, rfl⟩ := (hP_zero_iff z).mp hPz
      intro hQz
      -- Q not identically zero near Z.z ρ (else f ≡ 0 near Z.z ρ, contradicting finite order)
      have hQ_ne_top : analyticOrderAt Q (Z.z ρ) ≠ ⊤ := by
        rw [Ne, analyticOrderAt_eq_top]; intro hev; apply hf_ord_ne_top ρ
        rw [analyticOrderAt_eq_top]
        filter_upwards [hev] with w hw; rw [hfact w, hw, mul_zero]
      -- Product order = sum of orders
      have hmul := analyticOrderNatAt_mul (hP_diff.analyticAt (Z.z ρ))
        (hQ_diff.analyticAt (Z.z ρ)) (hP_ord_ne_top ρ) hQ_ne_top
      rw [← show f = P * Q from funext hfact, h_mult ρ, hP_mult ρ] at hmul
      -- hmul : Z.mult ρ = Z.mult ρ + analyticOrderNatAt Q (Z.z ρ)
      have hQ0 : analyticOrderNatAt Q (Z.z ρ) = 0 := by omega
      -- Convert: analyticOrderNatAt = 0 + order ≠ ⊤ → analyticOrderAt = 0 → Q(Z.z ρ) ≠ 0
      have hord_zero : analyticOrderAt Q (Z.z ρ) = 0 := by
        have h := ENat.natCast_toNat hQ_ne_top
        simp only [analyticOrderNatAt] at hQ0; rw [hQ0, Nat.cast_zero] at h; exact h.symm
      exact absurd hQz ((hQ_diff.analyticAt _).analyticOrderAt_eq_zero.mp hord_zero)
    · -- Away from zeros: Q = f/P, both nonzero
      rw [hQ_eq_div z hPz]
      exact div_ne_zero (by intro h; exact hPz ((hP_zero_iff z).mpr ((h_zeros_only z).mp h))) hPz
  exact ⟨Q, hQ_diff, hQ_ne, hfact⟩

/-!
## Steps 4–7. Collapsed: use `entire_no_zeros_is_exp_polynomial` directly.

Rather than building an entire logarithm `g` of `Q`, applying growth bounds,
Borel–Carathéodory, and Cauchy estimates separately (classical route), we
invoke the prepackaged library theorem `entire_no_zeros_is_exp_polynomial`
(`Hadamard/Basic.lean:2750`), which already handles all of:
  * the entire logarithm of an entire nowhere-zero function,
  * the growth bound on its real part,
  * the Borel–Carathéodory upgrade,
  * the Cauchy coefficient estimate and polynomial extraction.

The remaining ingredient is `Step 3': order Q ≤ lam`. With
`Q = f / P` both entire (and `P` having controlled below-bound), the growth
of `Q` on circles is at most the growth of `f` times the reciprocal of the
`P` lower bound. This is the only remaining analytic content.

We package Step 3' as the separate theorem
`order_Q_le_lam_of_factorization_and_order_f` below.
-/

private theorem separated_ratio_lower_bound
    {lam ε C_n r δ₀ : ℝ} (hlam : 0 ≤ lam) (hε : 0 < ε)
    (hCn_pos : 0 < C_n) (hr_ge2 : 2 ≤ r)
    (hδ₀_lb : r / (2 * (C_n * (3 * r) ^ (lam + ε / 9) + 2)) ≤ δ₀) :
    1 / (8 * (C_n * 3 ^ (lam + ε / 9) + 2) * r ^ (lam + ε / 9)) ≤
      δ₀ / (4 * r) := by
  let s_exp := lam + ε / 9
  let K0 := 8 * (C_n * 3 ^ s_exp + 2)
  have hr_pos : 0 < r := by linarith
  have hK0_pos : 0 < K0 := by dsimp [K0]; positivity
  have h3r_bound :
      C_n * (3 * r) ^ (lam + ε / 9) + 2 ≤
        (C_n * 3 ^ s_exp + 2) * r ^ s_exp := by
    have hr_ge1 : (1 : ℝ) ≤ r := le_trans (by norm_num : (1 : ℝ) ≤ 2) hr_ge2
    have hs_nonneg : 0 ≤ s_exp := by
      dsimp [s_exp]
      linarith
    have hmul_rpow :
        (3 * r) ^ (lam + ε / 9) = 3 ^ s_exp * r ^ s_exp := by
      dsimp [s_exp]
      simpa using
        (Real.mul_rpow (x := (3 : ℝ)) (y := r) (z := lam + ε / 9)
          (by positivity : (0 : ℝ) ≤ 3) (le_of_lt hr_pos))
    have hrpow_ge1 : (1 : ℝ) ≤ r ^ s_exp := Real.one_le_rpow hr_ge1 hs_nonneg
    have h2le :
        (2 : ℝ) ≤ 2 * r ^ s_exp := by
      nlinarith
    calc
      C_n * (3 * r) ^ (lam + ε / 9) + 2
          = C_n * (3 ^ s_exp * r ^ s_exp) + 2 := by
              rw [hmul_rpow]
      _ = C_n * 3 ^ s_exp * r ^ s_exp + 2 := by
              ring
      _ ≤ C_n * 3 ^ s_exp * r ^ s_exp + 2 * r ^ s_exp := by
              gcongr
      _ = (C_n * 3 ^ s_exp + 2) * r ^ s_exp := by ring
  have hbase :
      (1 : ℝ) / (8 * (C_n * (3 * r) ^ (lam + ε / 9) + 2)) ≤ δ₀ / (4 * r) := by
    have h := hδ₀_lb
    have hr_pos' : 0 < r := hr_pos
    have hden_pos : 0 < 8 * (C_n * (3 * r) ^ (lam + ε / 9) + 2) := by
      have : 0 < C_n * (3 * r) ^ (lam + ε / 9) + 2 := by positivity
      positivity
    have hden_eq :
        r / (2 * (C_n * (3 * r) ^ (lam + ε / 9) + 2)) / (4 * r) =
          (1 : ℝ) / (8 * (C_n * (3 * r) ^ (lam + ε / 9) + 2)) := by
      field_simp [hr_pos.ne']
      ring
    have hdiv :
        r / (2 * (C_n * (3 * r) ^ (lam + ε / 9) + 2)) / (4 * r) ≤
          δ₀ / (4 * r) :=
      div_le_div_of_nonneg_right h (show 0 ≤ 4 * r by positivity)
    rw [hden_eq] at hdiv
    exact hdiv
  have hK0_mul :
      K0 * r ^ s_exp = 8 * ((C_n * 3 ^ s_exp + 2) * r ^ s_exp) := by
    ring
  have hden_le :
      8 * (C_n * (3 * r) ^ (lam + ε / 9) + 2) ≤ K0 * r ^ s_exp := by
    rw [hK0_mul]
    gcongr
  have hK0r_pos : 0 < K0 * r ^ s_exp := by positivity
  have hden_small_pos : 0 < 8 * (C_n * (3 * r) ^ (lam + ε / 9) + 2) := by
    have : 0 < C_n * (3 * r) ^ (lam + ε / 9) + 2 := by positivity
    positivity
  calc
    1 / (K0 * r ^ s_exp) ≤ 1 / (8 * (C_n * (3 * r) ^ (lam + ε / 9) + 2)) := by
        exact one_div_le_one_div_of_le hden_small_pos hden_le
    _ ≤ δ₀ / (4 * r) := hbase

private theorem near_factor_log_bound (p : ℕ)
    {K0 s_exp ε r R δ₀ : ℝ} (hK0_gt1 : 1 < K0) (hs_nonneg : 0 ≤ s_exp)
    (hε9 : 0 < ε / 9) (hr_pos : 0 < r) (hR_ge1 : 1 ≤ R) (hrR : r ≤ R)
    (hδratio_pos : 0 < δ₀ / (4 * r)) (hδratio_le_one : δ₀ / (4 * r) ≤ 1)
    (hδratio_lower : 1 / (K0 * r ^ s_exp) ≤ δ₀ / (4 * r)) :
    (2 : ℝ) ^ p * ((p : ℝ) + |Real.log (δ₀ / (4 * r))|) ≤
      (2 : ℝ) ^ p * ((p : ℝ) + Real.log K0 + s_exp / (ε / 9)) * R ^ (ε / 9) := by
  let C_near := (2 : ℝ) ^ p * ((p : ℝ) + |Real.log (δ₀ / (4 * r))|)
  let KnearBase := (2 : ℝ) ^ p * ((p : ℝ) + Real.log K0 + s_exp / (ε / 9))
  have hK0_pos : 0 < K0 := lt_trans zero_lt_one hK0_gt1
  have hK0_log_nonneg : 0 ≤ Real.log K0 := Real.log_nonneg hK0_gt1.le
  have hlog_nonpos : Real.log (δ₀ / (4 * r)) ≤ 0 :=
    Real.log_nonpos hδratio_pos.le hδratio_le_one
  have hK0r_pos : 0 < K0 * r ^ s_exp := by positivity [hK0_pos]
  have hlog_lower :
      Real.log (1 / (K0 * r ^ s_exp)) ≤ Real.log (δ₀ / (4 * r)) := by
    exact Real.log_le_log (by positivity) hδratio_lower
  have habs_log_le :
      |Real.log (δ₀ / (4 * r))| ≤ Real.log K0 + s_exp * Real.log r := by
    have hlog_inv :
        -Real.log (1 / (K0 * r ^ s_exp)) = Real.log (K0 * r ^ s_exp) := by
      rw [show (1 / (K0 * r ^ s_exp)) = (K0 * r ^ s_exp)⁻¹ by field_simp]
      rw [Real.log_inv, neg_neg]
    have hlog_mul :
        Real.log (K0 * r ^ s_exp) = Real.log K0 + s_exp * Real.log r := by
      rw [Real.log_mul hK0_pos.ne' (by positivity), Real.log_rpow hr_pos]
    calc
      |Real.log (δ₀ / (4 * r))| = -Real.log (δ₀ / (4 * r)) := by
          rw [abs_of_nonpos hlog_nonpos]
      _ ≤ -Real.log (1 / (K0 * r ^ s_exp)) := by linarith
      _ = Real.log (K0 * r ^ s_exp) := hlog_inv
      _ = Real.log K0 + s_exp * Real.log r := hlog_mul
  have hlogr_le : Real.log r ≤ r ^ (ε / 9) / (ε / 9) :=
    Real.log_le_rpow_div hr_pos.le hε9
  have hrpow_le_Rpow : r ^ (ε / 9) ≤ R ^ (ε / 9) := by
    exact Real.rpow_le_rpow (le_of_lt hr_pos) hrR (le_of_lt hε9)
  have hRpow_ge1 : (1 : ℝ) ≤ R ^ (ε / 9) :=
    Real.one_le_rpow (by linarith : (1 : ℝ) ≤ R) (le_of_lt hε9)
  have hconst_le :
      (p : ℝ) + Real.log K0 ≤ ((p : ℝ) + Real.log K0) * R ^ (ε / 9) := by
    exact le_mul_of_one_le_right (by positivity) hRpow_ge1
  have hslog_le :
      s_exp * Real.log r ≤ (s_exp / (ε / 9)) * R ^ (ε / 9) := by
    have h1 : s_exp * Real.log r ≤ s_exp * (r ^ (ε / 9) / (ε / 9)) :=
      mul_le_mul_of_nonneg_left hlogr_le hs_nonneg
    have h2 : s_exp * (r ^ (ε / 9) / (ε / 9)) ≤ (s_exp / (ε / 9)) * R ^ (ε / 9) := by
      have hfrac_nonneg : 0 ≤ s_exp / (ε / 9) := by positivity
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        mul_le_mul_of_nonneg_left hrpow_le_Rpow hfrac_nonneg
    exact le_trans h1 h2
  calc
    C_near = (2 : ℝ) ^ p * ((p : ℝ) + |Real.log (δ₀ / (4 * r))|) := by
        simp [C_near]
    _ ≤ (2 : ℝ) ^ p * (((p : ℝ) + Real.log K0) * R ^ (ε / 9) +
          (s_exp / (ε / 9)) * R ^ (ε / 9)) := by
        have hinner_le :
            (p : ℝ) + |Real.log (δ₀ / (4 * r))| ≤
              ((p : ℝ) + Real.log K0) * R ^ (ε / 9) +
                (s_exp / (ε / 9)) * R ^ (ε / 9) := by
          linarith [habs_log_le, hconst_le, hslog_le]
        exact mul_le_mul_of_nonneg_left hinner_le (by positivity)
    _ = KnearBase * R ^ (ε / 9) := by
        simp [KnearBase]
        ring

private theorem canonicalProduct_factor_lower_bound
    {f : ℂ → ℂ} (Z : ZeroSetMultiplicity f) (p : ℕ)
    {r R δ₀ : ℝ} (hR2r : R ≤ 2 * r) (hδ₀_pos : 0 < δ₀)
    (hsep : ∀ ρ : Z.Zero, δ₀ ≤ |‖Z.z ρ‖ - R|)
    (z : ℂ) (hz : ‖z‖ = R) (C_near C_far : ℝ)
    (hzw_ne : ∀ i : Z.ZeroWithMultiplicity, Z.zWithMultiplicity i ≠ 0)
    (hfac_ne : ∀ i : Z.ZeroWithMultiplicity,
      weierstrassE p (z / Z.zWithMultiplicity i) ≠ 0)
    (hC_near : ∀ w : ℂ, (1 : ℝ) / 2 ≤ ‖w‖ → δ₀ / (4 * r) ≤ ‖w - 1‖ →
      Real.log ‖weierstrassE p w‖ ≥ -C_near * ‖w‖ ^ p)
    (hC_far : ∀ w : ℂ, ‖w‖ ≤ (1 : ℝ) / 2 →
      Real.log ‖weierstrassE p w‖ ≥ -C_far * ‖w‖ ^ (p + 1)) :
    ∀ i : Z.ZeroWithMultiplicity,
      Real.exp (-(if ‖Z.zWithMultiplicity i‖ ≤ 2 * R then
        C_near * ‖z / Z.zWithMultiplicity i‖ ^ p else
        max C_far 0 * ‖z / Z.zWithMultiplicity i‖ ^ (p + 1))) ≤
        ‖weierstrassE p (z / Z.zWithMultiplicity i)‖ := by
  let zw := Z.zWithMultiplicity
  let C_far' := max C_far 0
  let a := fun i : Z.ZeroWithMultiplicity =>
    if ‖zw i‖ ≤ 2 * R then C_near * ‖z / zw i‖ ^ p
    else C_far' * ‖z / zw i‖ ^ (p + 1)
  intro i
  change Real.exp (-(a i)) ≤ ‖weierstrassE p (z / zw i)‖
  by_cases hsmall : ‖zw i‖ ≤ 2 * R
  · -- Near zeros: use the away-from-one lower bound.
    have hw_big : (1 / 2 : ℝ) ≤ ‖z / zw i‖ := by
      have hzi_pos : 0 < ‖zw i‖ := norm_pos_iff.2 (hzw_ne i)
      have hzi_le : ‖zw i‖ ≤ 2 * ‖z‖ := by simpa [hz] using hsmall
      have hmul : (1 / 2 : ℝ) * ‖zw i‖ ≤ ‖z‖ := by
        have := mul_le_mul_of_nonneg_left hzi_le (by positivity : 0 ≤ (1 / 2 : ℝ))
        simpa using (le_trans this (le_of_eq (by nlinarith)))
      have : (1 / 2 : ℝ) ≤ ‖z‖ / ‖zw i‖ := (le_div_iff₀ hzi_pos).2 hmul
      simpa [norm_div] using this
    have hdist : δ₀ / (4 * r) ≤ ‖z / zw i - 1‖ := by
      have hzi_pos : 0 < ‖zw i‖ := norm_pos_iff.2 (hzw_ne i)
      have hδ0_le : δ₀ ≤ ‖z - zw i‖ := by
        have hsep_i : δ₀ ≤ |‖Z.z i.1‖ - R| := hsep i.1
        have habs : |‖Z.z i.1‖ - R| ≤ ‖Z.z i.1 - z‖ := by
          have := abs_norm_sub_norm_le (Z.z i.1) z
          simpa [hz] using this
        have : δ₀ ≤ ‖Z.z i.1 - z‖ := le_trans hsep_i habs
        rw [norm_sub_rev]; exact this
      have hden_le : ‖zw i‖ ≤ 4 * r := by
        have : ‖zw i‖ ≤ 2 * R := hsmall
        nlinarith [this, hR2r]
      have hδ1_le : δ₀ / (4 * r) ≤ δ₀ / ‖zw i‖ := by
        have hδ0_nonneg : 0 ≤ δ₀ := le_of_lt hδ₀_pos
        exact div_le_div_of_nonneg_left hδ0_nonneg hzi_pos hden_le
      have hδ0_div : δ₀ / ‖zw i‖ ≤ ‖z - zw i‖ / ‖zw i‖ :=
        div_le_div_of_nonneg_right hδ0_le (le_of_lt hzi_pos)
      have hmain : δ₀ / (4 * r) ≤ ‖z - zw i‖ / ‖zw i‖ := by
        exact le_trans hδ1_le hδ0_div
      have hne : zw i ≠ 0 := hzw_ne i
      have hz_div : ‖z / zw i - (1 : ℂ)‖ = ‖z - zw i‖ / ‖zw i‖ := by
        have : z / zw i - (1 : ℂ) = (z - zw i) / zw i := by
          calc
            z / zw i - (1 : ℂ) = z / zw i - (zw i / zw i) := by simp [div_self hne]
            _ = (z - zw i) / zw i := by simpa using (div_sub_div_same z (zw i) (zw i))
        simp [this]
      simpa [hz_div] using hmain
    have hlog := hC_near (z / zw i) hw_big (by simpa using hdist)
    have hpos : 0 < ‖weierstrassE p (z / zw i)‖ := norm_pos_iff.2 (hfac_ne i)
    have hneg :
        -(C_near * ‖z / zw i‖ ^ p) ≤ Real.log ‖weierstrassE p (z / zw i)‖ := by
      simpa using hlog
    have := (Real.exp_le_exp).2 hneg
    simpa [a, hsmall, Real.exp_log hpos] using this
  · -- Far zeros: use the small-disk lower bound.
    have hw_small : ‖z / zw i‖ ≤ (1 / 2 : ℝ) := by
      have hzi_pos : 0 < ‖zw i‖ := norm_pos_iff.2 (hzw_ne i)
      have hzi_large : 2 * ‖z‖ ≤ ‖zw i‖ := by
        have : 2 * R < ‖zw i‖ := lt_of_not_ge hsmall
        have : 2 * R ≤ ‖zw i‖ := le_of_lt this
        simpa [hz] using this
      have hmul : ‖z‖ ≤ (1 / 2 : ℝ) * ‖zw i‖ := by
        have := mul_le_mul_of_nonneg_left hzi_large (by positivity : 0 ≤ (1 / 2 : ℝ))
        simpa using (le_trans this (le_of_eq (by nlinarith)))
      have : ‖z‖ / ‖zw i‖ ≤ (1 / 2 : ℝ) := (div_le_iff₀ hzi_pos).2 hmul
      simpa [norm_div] using this
    have hCfar :
        Real.log ‖weierstrassE p (z / zw i)‖ ≥ -C_far' * ‖z / zw i‖ ^ (p + 1) := by
      have hbase := hC_far (z / zw i) hw_small
      have hle : C_far ≤ C_far' := le_max_left _ _
      have hw_nonneg : 0 ≤ ‖z / zw i‖ ^ (p + 1) := by positivity
      have hmul :
          C_far * ‖z / zw i‖ ^ (p + 1) ≤ C_far' * ‖z / zw i‖ ^ (p + 1) :=
        mul_le_mul_of_nonneg_right hle hw_nonneg
      have hneg :
          -C_far' * ‖z / zw i‖ ^ (p + 1) ≤ -C_far * ‖z / zw i‖ ^ (p + 1) := by
        have : -(C_far' * ‖z / zw i‖ ^ (p + 1)) ≤ -(C_far * ‖z / zw i‖ ^ (p + 1)) :=
          neg_le_neg hmul
        simpa [neg_mul, mul_assoc] using this
      exact le_trans hneg hbase
    have hpos : 0 < ‖weierstrassE p (z / zw i)‖ := norm_pos_iff.2 (hfac_ne i)
    have := (Real.exp_le_exp).2 hCfar
    simpa [a, hsmall, Real.exp_log hpos] using this

private theorem summable_nearFar_exponent {ι : Type*}
    (zw : ι → ℂ) (p : ℕ) (hzw_ne : ∀ i, zw i ≠ 0)
    (hsum_zwm : Summable (fun i => (1 : ℝ) / ‖zw i‖ ^ (p + 1)))
    (R : ℝ) (hR_pos : 0 < R) (z : ℂ) (C_near C_far' : ℝ)
    (hCn_nn : 0 ≤ C_near) (hCf_nn : 0 ≤ C_far') :
    Summable (fun i => if ‖zw i‖ ≤ 2 * R then C_near * ‖z / zw i‖ ^ p
      else C_far' * ‖z / zw i‖ ^ (p + 1)) := by
  classical
  let a := fun i => if ‖zw i‖ ≤ 2 * R then C_near * ‖z / zw i‖ ^ p
      else C_far' * ‖z / zw i‖ ^ (p + 1)
  change Summable a
  have ha_nn : ∀ i, 0 ≤ a i := by
    intro i
    dsimp only [a]
    split_ifs <;> positivity
  have hS_finite :
      ({i : ι | ‖zw i‖ ≤ 2 * R} : Set ι).Finite :=
    Hadamard.OrderOne.finite_norm_le_of_summable_inv_norm_pow
      (z := zw) (p := p) hzw_ne hsum_zwm (R := 2 * R) (by positivity)
  let S : Set ι := {i : ι | ‖zw i‖ ≤ 2 * R}
  have hS_part :
      Summable (fun i : ι => if i ∈ S then a i else 0) := by
    refine summable_of_hasFiniteSupport ?_
    have hsupp :
        Function.support (fun i : ι => if i ∈ S then a i else 0) ⊆ S := by
      intro i hi
      by_contra hnot
      have : (if i ∈ S then a i else 0) ≠ 0 := by
        simpa [Function.support] using hi
      simp [hnot] at this
    exact hS_finite.subset hsupp
  have hTail :
      Summable (fun i : ι => if i ∈ S then 0 else a i) := by
    have hdom :
        ∀ i : ι,
          (if i ∈ S then 0 else a i) ≤
            (C_far' * ‖z‖ ^ (p + 1)) * ((1 : ℝ) / ‖zw i‖ ^ (p + 1)) := by
      intro i
      by_cases hiS : i ∈ S
      · have : 0 ≤ (C_far' * ‖z‖ ^ (p + 1)) * ((1 : ℝ) / ‖zw i‖ ^ (p + 1)) := by
          have : 0 ≤ C_far' * ‖z‖ ^ (p + 1) :=
            mul_nonneg hCf_nn (pow_nonneg (norm_nonneg _) _)
          exact mul_nonneg this (by positivity)
        simpa [hiS] using this
      · have hlarge : ¬ ‖zw i‖ ≤ 2 * R := by
          have : ¬ i ∈ S := hiS
          simpa [S] using this
        have :
            (if i ∈ S then 0 else a i) =
              (C_far' * ‖z‖ ^ (p + 1)) * ((1 : ℝ) / ‖zw i‖ ^ (p + 1)) := by
          have h1 : (if i ∈ S then 0 else a i) = C_far' * ‖z / zw i‖ ^ (p + 1) := by
            simp [a, hiS, hlarge]
          have h2 :
              C_far' * ‖z / zw i‖ ^ (p + 1) =
                (C_far' * ‖z‖ ^ (p + 1)) * ((1 : ℝ) / ‖zw i‖ ^ (p + 1)) := by
            rw [norm_div, div_eq_mul_inv, mul_pow]
            ring_nf
          simpa [h1] using h2
        simp [this]
    have hsum_dom :
        Summable (fun i : ι =>
          (C_far' * ‖z‖ ^ (p + 1)) * ((1 : ℝ) / ‖zw i‖ ^ (p + 1))) :=
      hsum_zwm.mul_left (C_far' * ‖z‖ ^ (p + 1))
    refine Summable.of_nonneg_of_le
        (f := fun i : ι =>
          (C_far' * ‖z‖ ^ (p + 1)) * ((1 : ℝ) / ‖zw i‖ ^ (p + 1)))
        (g := fun i : ι => if i ∈ S then 0 else a i) ?_ ?_ hsum_dom
    · intro i
      by_cases hiS : i ∈ S <;> simp [hiS, ha_nn]
    · intro i
      exact hdom i
  have :
      Summable (fun i : ι =>
        (if i ∈ S then a i else 0) + (if i ∈ S then 0 else a i)) :=
    hS_part.add hTail
  have hsimp :
      (fun i : ι => (if i ∈ S then a i else 0) + (if i ∈ S then 0 else a i)) = a := by
    funext i
    by_cases hiS : i ∈ S <;> simp [hiS]
  simpa [hsimp] using this

private theorem far_exponent_sum_bound
    {f : ℂ → ℂ} (Z : ZeroSetMultiplicity f) (p : ℕ)
    (hsum : Summable (fun ρ : Z.Zero => (Z.mult ρ : ℝ) / ‖Z.z ρ‖ ^ (p + 1)))
    (n_tail : ℕ) (C_tail exponent : ℝ)
    (htail_weighted : ∀ n : ℕ, n_tail ≤ n →
      (∑' ρ : {ρ : Z.Zero | (2 : ℝ) ^ (n + 1) < ‖Z.z ρ‖},
        (Z.mult ρ.val : ℝ) / ‖Z.z ρ.val‖ ^ (p + 1)) ≤
        C_tail * ((2 : ℝ) ^ n) ^ exponent)
    (n : ℕ) (hn_pos : 0 < n) (hn_tail_lt : n_tail < n) :
    (∑' i : Z.ZeroWithMultiplicity,
      if (2 : ℝ) ^ n < ‖Z.zWithMultiplicity i‖ then
        (1 : ℝ) / ‖Z.zWithMultiplicity i‖ ^ (p + 1) else 0) ≤
      (C_tail * ((2 : ℝ) ^ exponent)⁻¹) * ((2 : ℝ) ^ n) ^ exponent := by
  classical
  let ZWM := Z.ZeroWithMultiplicity
  let zw := Z.zWithMultiplicity
  let farBase := fun i : ZWM => if (2 : ℝ) ^ n < ‖zw i‖ then
    (1 : ℝ) / ‖zw i‖ ^ (p + 1) else 0
  let qtail := (2 : ℝ) ^ exponent
  have hqtail_pos : 0 < qtail := by positivity
  let gFar : Z.Zero → ℝ := fun ρ =>
    if (2 : ℝ) ^ n < ‖Z.z ρ‖ then (1 : ℝ) / ‖Z.z ρ‖ ^ (p + 1) else 0
  have hgFar_nonneg : ∀ ρ : Z.Zero, 0 ≤ gFar ρ := by
    intro ρ
    dsimp [gFar]
    split_ifs <;> positivity
  have hgFar_summ :
      Summable (fun ρ : Z.Zero => (Z.mult ρ : ℝ) * gFar ρ) := by
    refine Summable.of_nonneg_of_le
        (f := fun ρ : Z.Zero => (Z.mult ρ : ℝ) / ‖Z.z ρ‖ ^ (p + 1))
        (g := fun ρ : Z.Zero => (Z.mult ρ : ℝ) * gFar ρ) ?_ ?_
        hsum
    · intro ρ
      by_cases hρ : (2 : ℝ) ^ n < ‖Z.z ρ‖
      · have hm_nonneg : 0 ≤ (Z.mult ρ : ℝ) := by positivity
        have hg_nonneg : 0 ≤ gFar ρ := by simp [gFar, hρ]
        exact mul_nonneg hm_nonneg hg_nonneg
      · simp [gFar, hρ]
    · intro ρ
      by_cases hρ : (2 : ℝ) ^ n < ‖Z.z ρ‖
      · simp [gFar, hρ, div_eq_mul_inv]
      · have hnonneg : 0 ≤ (Z.mult ρ : ℝ) / ‖Z.z ρ‖ ^ (p + 1) := by positivity
        simpa [gFar, hρ] using hnonneg
  have hfarBase_sigma :
      (∑' i : ZWM, farBase i) =
        ∑' ρ : Z.Zero, (Z.mult ρ : ℝ) * gFar ρ := by
    exact
      (tsum_zeroWithMultiplicity_eq_weighted_tsum_of_nonneg Z gFar hgFar_nonneg hgFar_summ)
  have hfarBase_bound :
      (∑' i : ZWM, farBase i) ≤
        (C_tail * qtail⁻¹) * ((2 : ℝ) ^ n) ^ (exponent) := by
    rw [hfarBase_sigma]
    let efar : ℝ := exponent
    have hn_sub : (n - 1) + 1 = n :=
      Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn_pos.ne')
    have hsub :
        (∑' ρ : Z.Zero, (Z.mult ρ : ℝ) * gFar ρ) =
          ∑' ρ : ({ρ : Z.Zero | (2 : ℝ) ^ ((n - 1) + 1) < ‖Z.z ρ‖} : Set Z.Zero),
            (Z.mult ρ.val : ℝ) / ‖Z.z ρ.val‖ ^ (p + 1) := by
      simpa [gFar, Set.indicator, Set.mem_ofPred_eq, hn_sub, div_eq_mul_inv] using
        (tsum_subtype
          (s := ({ρ : Z.Zero | (2 : ℝ) ^ ((n - 1) + 1) < ‖Z.z ρ‖} : Set Z.Zero))
          (f := fun ρ : Z.Zero => (Z.mult ρ : ℝ) / ‖Z.z ρ‖ ^ (p + 1))).symm
    rw [hsub]
    have htail_prev :
        (∑' ρ : ({ρ : Z.Zero | (2 : ℝ) ^ ((n - 1) + 1) < ‖Z.z ρ‖} : Set Z.Zero),
            (Z.mult ρ.val : ℝ) / ‖Z.z ρ.val‖ ^ (p + 1)) ≤
          C_tail * ((2 : ℝ) ^ (n - 1)) ^ efar := by
      simpa [Set.mem_ofPred_eq, efar] using
        htail_weighted (n - 1) (Nat.le_pred_of_lt hn_tail_lt)
    have hshift_eq :
        ((2 : ℝ) ^ (n - 1)) ^ efar =
          qtail⁻¹ * ((2 : ℝ) ^ n) ^ efar := by
      have hsplit :
          ((2 : ℝ) ^ n) ^ efar = qtail * (((2 : ℝ) ^ (n - 1)) ^ efar) := by
        calc
          ((2 : ℝ) ^ n) ^ efar = ((2 : ℝ) ^ ((n - 1) + 1)) ^ efar := by
              rw [hn_sub]
          _ = (2 * (2 : ℝ) ^ (n - 1)) ^ efar := by
              simp [pow_succ, mul_comm]
          _ = (2 : ℝ) ^ efar * (((2 : ℝ) ^ (n - 1)) ^ efar) := by
              rw [Real.mul_rpow
                (x := (2 : ℝ))
                (y := (2 : ℝ) ^ (n - 1))
                (z := efar)
                (by positivity : (0 : ℝ) ≤ 2)
                (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (n - 1))]
          _ = qtail * (((2 : ℝ) ^ (n - 1)) ^ efar) := by
              simp [qtail, efar]
      have hsplit' := congrArg (fun t : ℝ => qtail⁻¹ * t) hsplit
      simpa [mul_assoc, hqtail_pos.ne', qtail] using hsplit'.symm
    calc
      (∑' ρ : ({ρ : Z.Zero | (2 : ℝ) ^ ((n - 1) + 1) < ‖Z.z ρ‖} : Set Z.Zero),
          (Z.mult ρ.val : ℝ) / ‖Z.z ρ.val‖ ^ (p + 1))
          ≤ C_tail * ((2 : ℝ) ^ (n - 1)) ^ efar := htail_prev
      _ = (C_tail * qtail⁻¹) * ((2 : ℝ) ^ n) ^ efar := by
          rw [hshift_eq]
          ring
  exact hfarBase_bound

private theorem near_exponent_sum_bound
    {f : ℂ → ℂ} (hf_entire : Differentiable ℂ f)
    (Z : ZeroSetMultiplicity f)
    (h_zeros_only : ∀ s : ℂ, f s = 0 ↔ ∃ ρ : Z.Zero, s = Z.z ρ)
    (h_inj : Function.Injective Z.z) (h_z_ne_zero : ∀ ρ : Z.Zero, Z.z ρ ≠ 0)
    (p n : ℕ) (C_ball exponent : ℝ)
    (hbound : (∑ ρ ∈ Hadamard.OrderOne.zerosBallFinsetOfEntire hf_entire
      Z.toZeroSet h_zeros_only h_inj h_z_ne_zero n,
      (Z.mult ρ : ℝ) / ‖Z.z ρ‖ ^ p) ≤ C_ball * ((2 : ℝ) ^ n) ^ exponent) :
    (∑' i : Z.ZeroWithMultiplicity, if ‖Z.zWithMultiplicity i‖ ≤ (2 : ℝ) ^ n then
      (1 : ℝ) / ‖Z.zWithMultiplicity i‖ ^ p else 0) ≤
      C_ball * ((2 : ℝ) ^ n) ^ exponent := by
  classical
  let ZWM := Z.ZeroWithMultiplicity
  let zw := Z.zWithMultiplicity
  let ballD := fun m => Hadamard.OrderOne.zerosBallFinsetOfEntire
    hf_entire Z.toZeroSet h_zeros_only h_inj h_z_ne_zero m
  let nearBase := fun i : ZWM => if ‖zw i‖ ≤ (2 : ℝ) ^ n then
    (1 : ℝ) / ‖zw i‖ ^ p else 0
  let gNear : Z.Zero → ℝ := fun ρ =>
    if ‖Z.z ρ‖ ≤ (2 : ℝ) ^ n then (1 : ℝ) / ‖Z.z ρ‖ ^ p else 0
  have hgNear_nonneg : ∀ ρ : Z.Zero, 0 ≤ gNear ρ := by
    intro ρ
    by_cases hρ : ‖Z.z ρ‖ ≤ (2 : ℝ) ^ n <;> simp [gNear, hρ]
  have hgNear_summ :
      Summable (fun ρ : Z.Zero => (Z.mult ρ : ℝ) * gNear ρ) := by
    refine summable_of_hasFiniteSupport ?_
    have hsupp :
        Function.support (fun ρ : Z.Zero => (Z.mult ρ : ℝ) * gNear ρ) ⊆
          {ρ : Z.Zero | ‖Z.z ρ‖ ≤ (2 : ℝ) ^ n} := by
      intro ρ hρ
      have hne : (Z.mult ρ : ℝ) * gNear ρ ≠ 0 := Function.mem_support.1 hρ
      have hle : ‖Z.z ρ‖ ≤ (2 : ℝ) ^ n := by
        by_contra hle
        apply hne
        simp [gNear, hle]
      exact hle
    exact
      (Hadamard.OrderOne.zerosBallFinite_of_entire
        (hf_entire := hf_entire) (Z := Z.toZeroSet) (h_zeros_only := h_zeros_only)
        (h_inj := h_inj) (h_z_ne_zero := h_z_ne_zero) n).subset hsupp
  have hnearBase_sigma :
      (∑' i : ZWM, nearBase i) =
        ∑' ρ : Z.Zero, (Z.mult ρ : ℝ) * gNear ρ := by
    exact
      (tsum_zeroWithMultiplicity_eq_weighted_tsum_of_nonneg Z gNear hgNear_nonneg hgNear_summ)
  have hnearDistinct :
      (∑' ρ : Z.Zero, (Z.mult ρ : ℝ) * gNear ρ) =
        ∑ ρ ∈ ballD n, (Z.mult ρ : ℝ) / ‖Z.z ρ‖ ^ p := by
    have hzero :
        ∀ ρ : Z.Zero, ρ ∉ ballD n → (Z.mult ρ : ℝ) * gNear ρ = 0 := by
      intro ρ hρ
      have hle : ¬ ‖Z.z ρ‖ ≤ (2 : ℝ) ^ n := by
        intro hle
        exact hρ <|
          (Hadamard.OrderOne.mem_zerosBallFinset_of_entire_iff
            (hf_entire := hf_entire) (Z := Z.toZeroSet) (h_zeros_only := h_zeros_only)
            (h_inj := h_inj) (h_z_ne_zero := h_z_ne_zero) n ρ).2 hle
      simp [gNear, hle]
    have hraw :=
      tsum_eq_sum (L := SummationFilter.unconditional Z.Zero) (s := ballD n) hzero
    have hsum_if :
        (∑ ρ ∈ ballD n, (Z.mult ρ : ℝ) * gNear ρ) =
          ∑ ρ ∈ ballD n, (Z.mult ρ : ℝ) / ‖Z.z ρ‖ ^ p := by
      refine Finset.sum_congr rfl ?_
      intro ρ hρ
      have hle : ‖Z.z ρ‖ ≤ (2 : ℝ) ^ n :=
        (Hadamard.OrderOne.mem_zerosBallFinset_of_entire_iff
          (hf_entire := hf_entire) (Z := Z.toZeroSet) (h_zeros_only := h_zeros_only)
          (h_inj := h_inj) (h_z_ne_zero := h_z_ne_zero) n ρ).1 hρ
      simp [gNear, hle, div_eq_mul_inv]
    simpa [hsum_if] using hraw
  have hnearBase_bound :
      (∑' i : ZWM, nearBase i) ≤ C_ball * ((2 : ℝ) ^ n) ^ exponent := by
    rw [hnearBase_sigma, hnearDistinct]
    have hball := hbound
    exact hball
  exact hnearBase_bound

private theorem exp_neg_tsum_le_norm_tprod {ι : Type*}
    (a : ι → ℝ) (b : ι → ℂ) (ha_nn : ∀ i, 0 ≤ a i) (ha_sum : Summable a)
    (hmul : Multipliable b) (hfac_bound : ∀ i, Real.exp (-(a i)) ≤ ‖b i‖) :
    Real.exp (-∑' i, a i) ≤ ‖∏' i, b i‖ := by
  have hpartial : ∀ s : Finset ι,
      Real.exp (-∑' i, a i) ≤ ‖∏ i ∈ s, b i‖ := by
    intro s
    calc Real.exp (-∑' i, a i)
        ≤ Real.exp (-∑ i ∈ s, a i) :=
          Real.exp_le_exp.mpr (neg_le_neg (ha_sum.sum_le_tsum s (fun i _ => ha_nn i)))
      _ = ∏ i ∈ s, Real.exp (-(a i)) := by
          have : -∑ i ∈ s, a i = ∑ i ∈ s, -(a i) := by simp [Finset.sum_neg_distrib]
          rw [this]; exact Real.exp_sum s fun i => -(a i)
      _ ≤ ∏ i ∈ s, ‖b i‖ :=
          Finset.prod_le_prod₀ (fun i _ => (Real.exp_pos _).le) (fun i _ => hfac_bound i)
      _ = ‖∏ i ∈ s, b i‖ := (norm_prod s _).symm
  exact ge_of_tendsto ((continuous_norm.tendsto _).comp hmul.hasProd)
    (Filter.Eventually.of_forall hpartial)

private theorem nearFar_tsum_le_dyadic_majorant {ι : Type*}
    (zw : ι → ℂ) (p n : ℕ) (hzw_ne : ∀ i, zw i ≠ 0)
    (hsum_zwm : Summable (fun i => (1 : ℝ) / ‖zw i‖ ^ (p + 1)))
    (R : ℝ) (hR_pos : 0 < R) (z : ℂ) (hz : ‖z‖ = R)
    (hr_lt : R < (2 : ℝ) ^ n) (hn_le : (2 : ℝ) ^ n ≤ 2 * R)
    (C_near C_far' : ℝ) (hCn_nn : 0 ≤ C_near) (hCf_nn : 0 ≤ C_far') :
    (∑' i, if ‖zw i‖ ≤ 2 * R then C_near * ‖z / zw i‖ ^ p
      else C_far' * ‖z / zw i‖ ^ (p + 1)) ≤
      (∑' i, (C_near * R ^ p) *
        (if ‖zw i‖ ≤ (2 : ℝ) ^ (n + 1) then (1 : ℝ) / ‖zw i‖ ^ p else 0)) +
      (∑' i, (C_far' * R ^ (p + 1)) *
        (if (2 : ℝ) ^ n < ‖zw i‖ then (1 : ℝ) / ‖zw i‖ ^ (p + 1) else 0)) := by
  let a : ι → ℝ := fun i =>
    if ‖zw i‖ ≤ 2 * R then C_near * ‖z / zw i‖ ^ p
    else C_far' * ‖z / zw i‖ ^ (p + 1)
  let nearBase : ι → ℝ := fun i =>
    if ‖zw i‖ ≤ (2 : ℝ) ^ (n + 1) then (1 : ℝ) / ‖zw i‖ ^ p else 0
  let farBase : ι → ℝ := fun i =>
    if (2 : ℝ) ^ n < ‖zw i‖ then (1 : ℝ) / ‖zw i‖ ^ (p + 1) else 0
  let nearBall : ι → ℝ := fun i => (C_near * R ^ p) * nearBase i
  let farTail : ι → ℝ := fun i => (C_far' * R ^ (p + 1)) * farBase i
  have ha_sum : Summable a :=
    summable_nearFar_exponent zw p hzw_ne hsum_zwm R hR_pos z C_near C_far' hCn_nn hCf_nn
  have hnearBase_summ : Summable nearBase := by
    refine summable_of_hasFiniteSupport ?_
    have hsupp :
        Function.support nearBase ⊆ {i : ι | ‖zw i‖ ≤ (2 : ℝ) ^ (n + 1)} := by
      intro i hi
      by_contra hnot
      have hnot' : ¬ ‖zw i‖ ≤ (2 : ℝ) ^ (n + 1) := by
        simpa using hnot
      have hi' : nearBase i ≠ 0 := Function.mem_support.1 hi
      have : nearBase i = 0 := by
        simp [nearBase, hnot']
      exact hi' this
    exact
      (Hadamard.OrderOne.finite_norm_le_of_summable_inv_norm_pow
        (z := zw) (p := p) hzw_ne hsum_zwm (R := (2 : ℝ) ^ (n + 1))
        (by positivity)).subset hsupp
  have hfarBase_summ : Summable farBase := by
    have hdom : ∀ i : ι, farBase i ≤ (1 : ℝ) / ‖zw i‖ ^ (p + 1) := by
      intro i
      by_cases hlt : (2 : ℝ) ^ n < ‖zw i‖ <;> simp [farBase, hlt]
    refine Summable.of_nonneg_of_le
        (f := fun i : ι => (1 : ℝ) / ‖zw i‖ ^ (p + 1))
        (g := farBase) ?_ ?_ hsum_zwm
    · intro i
      by_cases hlt : (2 : ℝ) ^ n < ‖zw i‖ <;> simp [farBase, hlt]
    · intro i
      exact hdom i
  have hnearBall_summ : Summable nearBall :=
    hnearBase_summ.mul_left (C_near * R ^ p)
  have hfarTail_summ : Summable farTail :=
    hfarBase_summ.mul_left (C_far' * R ^ (p + 1))
  have hnearBall_nn : ∀ i, 0 ≤ nearBall i := by
    intro i
    by_cases hi : ‖zw i‖ ≤ (2 : ℝ) ^ (n + 1)
    · have hcoeff_nonneg : 0 ≤ C_near * R ^ p := mul_nonneg hCn_nn (by positivity)
      have hbase_nonneg : 0 ≤ (1 : ℝ) / ‖zw i‖ ^ p := by positivity
      simpa [nearBall, nearBase, hi] using mul_nonneg hcoeff_nonneg hbase_nonneg
    · simp [nearBall, nearBase, hi]
  have hfarTail_nn : ∀ i, 0 ≤ farTail i := by
    intro i
    by_cases hi : (2 : ℝ) ^ n < ‖zw i‖
    · have hcoeff_nonneg : 0 ≤ C_far' * R ^ (p + 1) := mul_nonneg hCf_nn (by positivity)
      have hbase_nonneg : 0 ≤ (1 : ℝ) / ‖zw i‖ ^ (p + 1) := by positivity
      simpa [farTail, farBase, hi] using mul_nonneg hcoeff_nonneg hbase_nonneg
    · simp [farTail, farBase, hi]
  have h2R_lt_pow : 2 * R < (2 : ℝ) ^ (n + 1) := by
    have := mul_lt_mul_of_pos_left hr_lt (by positivity : (0 : ℝ) < 2)
    simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using this
  have hmajor : ∀ i : ι, a i ≤ nearBall i + farTail i := by
    intro i
    by_cases hsmall : ‖zw i‖ ≤ 2 * R
    · have hball_i : ‖zw i‖ ≤ (2 : ℝ) ^ (n + 1) := by
        linarith
      have hpow_eq :
          C_near * ‖z / zw i‖ ^ p =
            (C_near * R ^ p) * ((1 : ℝ) / ‖zw i‖ ^ p) := by
        rw [norm_div, hz, div_eq_mul_inv, mul_pow]
        ring_nf
      have hnear_eq :
          nearBall i = (C_near * R ^ p) * ((1 : ℝ) / ‖zw i‖ ^ p) := by
        simp [nearBall, nearBase, hball_i]
      calc
        a i = C_near * ‖z / zw i‖ ^ p := by simp [a, hsmall]
        _ = (C_near * R ^ p) * ((1 : ℝ) / ‖zw i‖ ^ p) := hpow_eq
        _ ≤ nearBall i + farTail i := by
            rw [hnear_eq]
            linarith [hfarTail_nn i]
    · have htail_i : (2 : ℝ) ^ n < ‖zw i‖ := by
        have h2R_lt_norm : 2 * R < ‖zw i‖ := lt_of_not_ge hsmall
        exact lt_of_le_of_lt hn_le h2R_lt_norm
      have hpow_eq :
          C_far' * ‖z / zw i‖ ^ (p + 1) =
            (C_far' * R ^ (p + 1)) * ((1 : ℝ) / ‖zw i‖ ^ (p + 1)) := by
        rw [norm_div, hz, div_eq_mul_inv, mul_pow]
        ring_nf
      have hfar_eq :
          farTail i = (C_far' * R ^ (p + 1)) * ((1 : ℝ) / ‖zw i‖ ^ (p + 1)) := by
        simp [farTail, farBase, htail_i]
      calc
        a i = C_far' * ‖z / zw i‖ ^ (p + 1) := by simp [a, hsmall]
        _ = (C_far' * R ^ (p + 1)) * ((1 : ℝ) / ‖zw i‖ ^ (p + 1)) := hpow_eq
        _ ≤ nearBall i + farTail i := by
            rw [hfar_eq]
            linarith [hnearBall_nn i]
  have hmaj_summ : Summable (fun i => nearBall i + farTail i) :=
    hnearBall_summ.add hfarTail_summ
  have hle := Summable.tsum_le_tsum hmajor ha_sum hmaj_summ
  simpa only [Summable.tsum_add hnearBall_summ hfarTail_summ] using hle

private theorem near_weighted_tsum_bound {ι : Type*} (nearBase : ι → ℝ)
    (p n : ℕ) (R lam δcount ε C_near C_ball KnearBase : ℝ)
    (hR_ge1 : 1 ≤ R) (hCn_nn : 0 ≤ C_near) (hCball_nonneg : 0 ≤ C_ball)
    (hKnearBase_nonneg : 0 ≤ KnearBase) (hδcount_le_eps9 : δcount ≤ ε / 9)
    (hnearBase_bound : (∑' i, nearBase i) ≤
      C_ball * ((2 : ℝ) ^ (n + 1)) ^ (lam + δcount - p))
    (hCnear_bound : C_near ≤ KnearBase * R ^ (ε / 9))
    (hpow_n1_le : ((2 : ℝ) ^ (n + 1)) ^ (lam + δcount - p) ≤
      (4 : ℝ) ^ (lam + δcount - p) * R ^ (lam + δcount - p)) :
    (∑' i, (C_near * R ^ p) * nearBase i) ≤
      (KnearBase * C_ball * 4 ^ (lam + δcount - p)) * R ^ (lam + 2 * ε / 9) := by
  let αnear := lam + δcount - p
  let Knear := KnearBase * C_ball * 4 ^ αnear
  let nearBall : ι → ℝ := fun i => (C_near * R ^ p) * nearBase i
  have hR_pos : 0 < R := by linarith
  have hKnear_nonneg : 0 ≤ Knear := by positivity [Knear]
  have hconst_nonneg : 0 ≤ C_near * R ^ p := mul_nonneg hCn_nn (by positivity)
  calc
    (∑' i : ι, nearBall i)
        = (C_near * R ^ p) * (∑' i : ι, nearBase i) := by
            simp [nearBall, tsum_mul_left, mul_assoc]
    _ ≤ (C_near * R ^ p) * (C_ball * ((2 : ℝ) ^ (n + 1)) ^ αnear) := by
            exact mul_le_mul_of_nonneg_left hnearBase_bound hconst_nonneg
    _ ≤ (C_near * R ^ p) * (C_ball * ((4 : ℝ) ^ αnear * R ^ αnear)) := by
            gcongr
    _ ≤
        (KnearBase * R ^ (ε / 9) * R ^ p) *
          (C_ball * ((4 : ℝ) ^ αnear * R ^ αnear)) := by
            gcongr
    _ = Knear * (R ^ (ε / 9) * (R ^ p * R ^ αnear)) := by
            dsimp [Knear]
            ring_nf
    _ = Knear * (R ^ (lam + δcount + ε / 9)) := by
            have hnat : R ^ p = R ^ ((p : ℕ) : ℝ) := by
              rw [Real.rpow_natCast]
            rw [hnat]
            rw [← Real.rpow_add hR_pos, ← Real.rpow_add hR_pos]
            dsimp [αnear]
            congr 2
            ring
    _ ≤ Knear * R ^ (lam + 2 * ε / 9) := by
            have hexp_le : lam + δcount + ε / 9 ≤ lam + 2 * ε / 9 := by
              linarith [hδcount_le_eps9]
            have hpow_le :
                R ^ (lam + δcount + ε / 9) ≤ R ^ (lam + 2 * ε / 9) :=
              Real.rpow_le_rpow_of_exponent_le hR_ge1 hexp_le
            exact mul_le_mul_of_nonneg_left hpow_le hKnear_nonneg

private theorem far_weighted_tsum_bound {ι : Type*} (farBase : ι → ℝ)
    (p n : ℕ) (R lam δcount ε C_far' C_tail : ℝ)
    (hR_ge1 : 1 ≤ R) (hr_lt : R < (2 : ℝ) ^ n)
    (hCf_nn : 0 ≤ C_far') (hCtail_nonneg : 0 ≤ C_tail)
    (hlamδ_lt_p1 : lam + δcount < (p : ℝ) + 1)
    (hδ_eps : δcount ≤ 2 * ε / 9)
    (hfarBase_bound : (∑' i, farBase i) ≤
      (C_tail * ((2 : ℝ) ^ (lam + δcount - ((p : ℝ) + 1)))⁻¹) *
        ((2 : ℝ) ^ n) ^ (lam + δcount - ((p : ℝ) + 1))) :
    (∑' i, (C_far' * R ^ (p + 1)) * farBase i) ≤
      (C_far' * C_tail * ((2 : ℝ) ^ (lam + δcount - ((p : ℝ) + 1)))⁻¹) *
        R ^ (lam + 2 * ε / 9) := by
  let qtail := (2 : ℝ) ^ (lam + δcount - ((p : ℝ) + 1))
  let Kfar := C_far' * C_tail * qtail⁻¹
  let farTail : ι → ℝ := fun i => (C_far' * R ^ (p + 1)) * farBase i
  have hR_pos : 0 < R := by linarith
  have hKfar_nonneg : 0 ≤ Kfar := by positivity [Kfar, qtail]
  calc
    (∑' i : ι, farTail i)
        = (C_far' * R ^ (p + 1)) * (∑' i : ι, farBase i) := by
            simp [farTail, tsum_mul_left, mul_assoc]
    _ ≤
        (C_far' * R ^ (p + 1)) *
          ((C_tail * qtail⁻¹) *
            ((2 : ℝ) ^ n) ^ (lam + δcount - ((p : ℝ) + 1))) := by
            have hconst_nonneg : 0 ≤ C_far' * R ^ (p + 1) := by positivity
            exact mul_le_mul_of_nonneg_left hfarBase_bound hconst_nonneg
    _ ≤ (C_far' * R ^ (p + 1)) *
          ((C_tail * qtail⁻¹) * R ^ (lam + δcount - ((p : ℝ) + 1))) := by
            have hnegexp : lam + δcount - ((p : ℝ) + 1) < 0 := by
              linarith [hlamδ_lt_p1]
            have hpow_le :
                ((2 : ℝ) ^ n) ^ (lam + δcount - ((p : ℝ) + 1))
                  ≤ R ^ (lam + δcount - ((p : ℝ) + 1)) := by
              exact Real.rpow_le_rpow_of_nonpos hR_pos hr_lt.le hnegexp.le
            gcongr
    _ = Kfar * R ^ (lam + δcount) := by
            have hnat : R ^ (p + 1) = R ^ (((p + 1 : ℕ)) : ℝ) := by
              simpa using (Real.rpow_natCast R (p + 1)).symm
            calc
              (C_far' * R ^ (p + 1)) *
                  ((C_tail * qtail⁻¹) * R ^ (lam + δcount - ((p : ℝ) + 1)))
                  = Kfar * (R ^ (p + 1) * R ^ (lam + δcount - ((p : ℝ) + 1))) := by
                      simp [Kfar, mul_assoc, mul_left_comm, mul_comm]
              _ =
                  Kfar *
                    (R ^ (((p + 1 : ℕ) : ℝ)) *
                      R ^ (lam + δcount - ((p : ℝ) + 1))) := by
                      rw [hnat]
              _ = Kfar * R ^ (lam + δcount) := by
                      rw [← Real.rpow_add hR_pos]
                      congr 2
                      norm_num
    _ ≤ Kfar * R ^ (lam + 2 * ε / 9) := by
            have hexp_le : lam + δcount ≤ lam + 2 * ε / 9 := by
              linarith
            have hpow_le :
                R ^ (lam + δcount) ≤ R ^ (lam + 2 * ε / 9) :=
              Real.rpow_le_rpow_of_exponent_le hR_ge1 hexp_le
            exact mul_le_mul_of_nonneg_left hpow_le hKfar_nonneg

private theorem dyadic_rpow_upper_bound (n : ℕ) (R αnear : ℝ)
    (hR_pos : 0 < R) (hn_le : (2 : ℝ) ^ n ≤ 2 * R) (hαnear_nonneg : 0 ≤ αnear) :
    ((2 : ℝ) ^ (n + 1)) ^ αnear ≤ (4 : ℝ) ^ αnear * R ^ αnear := by
  have hbase : (2 : ℝ) ^ (n + 1) ≤ 4 * R := by
    have : 2 * (2 : ℝ) ^ n ≤ 4 * R := by nlinarith [hn_le]
    simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using this
  have hR4_nonneg : 0 ≤ 4 * R := by positivity
  have :=
    Real.rpow_le_rpow
      (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (n + 1)) hbase hαnear_nonneg
  simpa using
    (show ((2 : ℝ) ^ (n + 1)) ^ αnear ≤ (4 * R) ^ αnear from this).trans_eq (by
      rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ 4) hR_pos.le])

private theorem canonicalProduct_circle_lower_bound
    {f : ℂ → ℂ} (hf_entire : Differentiable ℂ f)
    (hf_finite : hasFiniteOrder f)
    {lam : ℝ} (hlam : 0 ≤ lam) (hf_order_le : order f ≤ lam)
    (Z : ZeroSetMultiplicity f)
    {p : ℕ} (hp : p = Nat.floor lam)
    (h_z_ne_zero : ∀ ρ : Z.Zero, Z.z ρ ≠ 0)
    (h_inj : Function.Injective Z.z)
    (hsum : Summable (fun ρ : Z.Zero => (Z.mult ρ : ℝ) / ‖Z.z ρ‖ ^ (p + 1)))
    (h_mult : ∀ ρ : Z.Zero, analyticOrderNatAt f (Z.z ρ) = Z.mult ρ)
    (h_zeros_only : ∀ s : ℂ, f s = 0 ↔ ∃ ρ : Z.Zero, s = Z.z ρ)
    (ε : ℝ) (hε : 0 < ε) (C_n : ℝ) (hCn_pos : 0 < C_n) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∃ R_c : ℝ, ∀ r : ℝ, R_c ≤ r →
      ∀ R δ₀ : ℝ, r ≤ R → R ≤ 2 * r → 0 < δ₀ → δ₀ ≤ r →
      r / (2 * (C_n * (3 * r) ^ (lam + ε / 9) + 2)) ≤ δ₀ →
      (∀ ρ : Z.Zero, δ₀ ≤ |‖Z.z ρ‖ - R|) →
      ∀ z : ℂ, ‖z‖ = R →
        Real.exp (-(C₀ * R ^ (lam + ε / 3))) ≤
          ‖canonicalProductZeroSetMultiplicityRank Z p z‖ := by
  let P := canonicalProductZeroSetMultiplicityRank Z p
  set ZWM := Z.ZeroWithMultiplicity
  set zw := Z.zWithMultiplicity
  have hzw_ne : ∀ i : ZWM, zw i ≠ 0 := fun i => h_z_ne_zero i.1
  have hsum_zwm : Summable (fun i : ZWM => (1 : ℝ) / ‖zw i‖ ^ (p + 1)) :=
    summable_inv_norm_pow_zWithMultiplicity Z hsum
  obtain ⟨C_far, hC_far⟩ := weierstrass_E_small_disk_lower_bound p
  set C_far' := max C_far 0
  have hCf_nn : 0 ≤ C_far' := le_max_right _ _
  have hp_le_lam : (p : ℝ) ≤ lam := by
    simpa [hp] using Nat.floor_le hlam
  have hlam_lt_p1 : lam < (p : ℝ) + 1 := by
    simpa [hp] using Nat.lt_floor_add_one lam
  set δcount : ℝ := min (ε / 9) (((p : ℝ) + 1 - lam) / 2)
  have hδcount_pos : 0 < δcount := by
    have hgap_pos : 0 < (((p : ℝ) + 1 - lam) / 2) := by
      have : 0 < (p : ℝ) + 1 - lam := sub_pos.mpr hlam_lt_p1
      simpa using half_pos this
    exact lt_min (by linarith) hgap_pos
  have hδcount_le_eps9 : δcount ≤ ε / 9 := min_le_left _ _
  have hlamδ_lt_p1 : lam + δcount < (p : ℝ) + 1 := by
    have hδcount_le_gap : δcount ≤ (((p : ℝ) + 1 - lam) / 2) := min_le_right _ _
    linarith
  obtain ⟨n_ball, C_ball, hCball_nonneg, hball_weighted⟩ :=
    sum_mult_div_norm_pow_le_rpow_of_two_pow
      (f := f) hf_entire hf_finite hlam hf_order_le Z h_zeros_only h_inj
      h_z_ne_zero h_mult hp_le_lam hδcount_pos
  obtain ⟨n_tail, C_tail, hCtail_nonneg, htail_weighted⟩ :=
    tsum_mult_div_norm_pow_tail_le_rpow_of_two_pow
      (f := f) hf_entire hf_finite hlam hf_order_le Z h_zeros_only h_inj
      h_z_ne_zero h_mult hδcount_pos hlamδ_lt_p1
  set s_exp : ℝ := lam + ε / 9
  set αnear : ℝ := lam + δcount - p
  set qtail : ℝ := (2 : ℝ) ^ (lam + δcount - ((p : ℝ) + 1))
  have hαnear_pos : 0 < αnear := by
    linarith
  have hαnear_nonneg : 0 ≤ αnear := le_of_lt hαnear_pos
  set Rdyad_ball : ℝ := (2 : ℝ) ^ n_ball
  set Rdyad_tail : ℝ := (2 : ℝ) ^ n_tail
  set K0 : ℝ := 8 * (C_n * 3 ^ s_exp + 2)
  have hK0_gt1 : 1 < K0 := by
    have hpow_nonneg : 0 ≤ (3 : ℝ) ^ s_exp := by
      positivity
    nlinarith [hCn_pos.le, hpow_nonneg]
  set KnearBase : ℝ :=
    (2 : ℝ) ^ p * (((p : ℝ) + Real.log K0) + s_exp / (ε / 9))
  set Knear : ℝ := KnearBase * C_ball * 4 ^ αnear
  set Kfar : ℝ := C_far' * C_tail * qtail⁻¹
  set Ksum : ℝ := Knear + Kfar
  have hε9 : 0 < ε / 9 := by linarith
  obtain ⟨Rabs, hRabs⟩ := Filter.eventually_atTop.mp
    (Filter.Tendsto.eventually_ge_atTop (tendsto_rpow_atTop hε9) Ksum)
  set R_c : ℝ := max 2 (max Rdyad_ball (max Rdyad_tail Rabs))
  refine
    ⟨1, one_pos, R_c,
      fun r hr R δ₀ hrR hR2r hδ₀_pos hδ₀_le_r hδ₀_lb hsep z hz => ?_⟩
  have hr_pos : 0 < r := by linarith
  have hR_pos : 0 < R := by linarith
  have hmul : Multipliable (fun i : ZWM => weierstrassE p (z / zw i)) :=
    Hadamard.OrderOne.multipliable_weierstrass_E_of_summable_inv_norm_pow hzw_ne hsum_zwm z
  have hz_ne : ∀ i : ZWM, z ≠ zw i := by
    intro i hEq
    have hsep_i := hsep i.1
    have hnorm_eq : ‖Z.z i.1‖ = R := by
      calc
        ‖Z.z i.1‖ = ‖zw i‖ := by rfl
        _ = ‖z‖ := by simpa using congrArg norm hEq.symm
        _ = R := hz
    have habs_eq : |‖Z.z i.1‖ - R| = 0 := by simp [hnorm_eq]
    linarith
  have hfac_ne : ∀ i : ZWM, weierstrassE p (z / zw i) ≠ 0 :=
    fun i => weierstrass_E_ne_zero_general p (by
      intro h; exact hz_ne i (by field_simp [hzw_ne i] at h; exact h))
  have hδ₁_pos : 0 < δ₀ / (4 * r) := by positivity
  set C_near : ℝ := (2 : ℝ) ^ p * ((p : ℝ) + |Real.log (δ₀ / (4 * r))|)
  have hCn_nn : 0 ≤ C_near := by
    dsimp [C_near]
    positivity
  have hC_near : ∀ w : ℂ, (1 : ℝ) / 2 ≤ ‖w‖ → δ₀ / (4 * r) ≤ ‖w - 1‖ →
      Real.log ‖weierstrassE p w‖ ≥ -C_near * ‖w‖ ^ p := by
    intro w hw hd
    simpa [C_near, mul_assoc, mul_left_comm, mul_comm] using
      weierstrass_E_away_from_one_lower_bound_explicit p (δ₀ / (4 * r)) hδ₁_pos w hw hd
  let a : ZWM → ℝ := fun i =>
    if ‖zw i‖ ≤ 2 * R then C_near * ‖z / zw i‖ ^ p
    else C_far' * ‖z / zw i‖ ^ (p + 1)
  have hfac_bound : ∀ i : ZWM, Real.exp (-(a i)) ≤ ‖weierstrassE p (z / zw i)‖ :=
    canonicalProduct_factor_lower_bound Z p hR2r hδ₀_pos hsep z hz C_near C_far
      hzw_ne hfac_ne hC_near hC_far
  have ha_nn : ∀ i, 0 ≤ a i := by
    intro i; dsimp only [a]; split_ifs with h
    · exact mul_nonneg hCn_nn (pow_nonneg (norm_nonneg _) _)
    · exact mul_nonneg hCf_nn (pow_nonneg (norm_nonneg _) _)
  have ha_sum : Summable a :=
    summable_nearFar_exponent zw p hzw_ne hsum_zwm R hR_pos z C_near C_far' hCn_nn hCf_nn
  have hprod_lb : Real.exp (-∑' i, a i) ≤ ‖P z‖ :=
    exp_neg_tsum_le_norm_tprod a _ ha_nn ha_sum hmul hfac_bound
  have hsum_tight : ∑' i, a i ≤ 1 * R ^ (lam + ε / 3) := by
    have hRc_ge2 : (2 : ℝ) ≤ R_c := le_max_left _ _
    have hRc_ge_inner :
        max Rdyad_ball (max Rdyad_tail Rabs) ≤ R_c := le_max_right _ _
    have hRc_ge_ball : Rdyad_ball ≤ R_c := le_trans (le_max_left _ _) hRc_ge_inner
    have hRc_ge_tail : Rdyad_tail ≤ R_c := by
      exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hRc_ge_inner
    have hRc_ge_Rabs : Rabs ≤ R_c := by
      exact le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hRc_ge_inner
    have hr_ge2 : (2 : ℝ) ≤ r := le_trans hRc_ge2 hr
    have hR_ge2 : (2 : ℝ) ≤ R := le_trans hr_ge2 hrR
    have hR_ge1 : (1 : ℝ) ≤ R := by linarith
    have hKnearBase_nonneg : 0 ≤ KnearBase := by
      have hs_nonneg : 0 ≤ s_exp := by
        dsimp [s_exp]
        linarith
      have hdiv_nonneg : 0 ≤ s_exp / (ε / 9) := div_nonneg hs_nonneg hε9.le
      have hinner_nonneg : 0 ≤ ((p : ℝ) + Real.log K0) + s_exp / (ε / 9) := by
        have hp_nonneg : 0 ≤ (p : ℝ) := by positivity
        have hlog_nonneg : 0 ≤ Real.log K0 := Real.log_nonneg (le_of_lt hK0_gt1)
        linarith
      exact mul_nonneg (by positivity) hinner_nonneg
    obtain ⟨n, hr_lt, hn_le⟩ := exists_pow_two_lt_and_le_two_mul R hR_ge2
    have hball_lt : (2 : ℝ) ^ n_ball < (2 : ℝ) ^ n := by
      calc
        (2 : ℝ) ^ n_ball = Rdyad_ball := by rfl
        _ ≤ R := le_trans hRc_ge_ball (le_trans hr hrR)
        _ < (2 : ℝ) ^ n := hr_lt
    have htail_lt : (2 : ℝ) ^ n_tail < (2 : ℝ) ^ n := by
      calc
        (2 : ℝ) ^ n_tail = Rdyad_tail := by rfl
        _ ≤ R := le_trans hRc_ge_tail (le_trans hr hrR)
        _ < (2 : ℝ) ^ n := hr_lt
    have hn_ball_le : n_ball ≤ n :=
      ((pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp hball_lt).le
    have hn_tail_lt : n_tail < n :=
      (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp htail_lt
    have hn_pos : 0 < n := by
      by_contra hn0
      have hn_eq0 : n = 0 := Nat.eq_zero_of_not_pos hn0
      have : R < (1 : ℝ) := by simpa [hn_eq0] using hr_lt
      linarith [hR_ge2]
    have hn_ball_succ : n_ball ≤ n + 1 := le_trans hn_ball_le (Nat.le_succ _)
    have hR_ge_Rabs : Rabs ≤ R := le_trans hRc_ge_Rabs (le_trans hr hrR)
    have hRpow_eps9_ge : Ksum ≤ R ^ (ε / 9) := hRabs R hR_ge_Rabs
    let nearBase : ZWM → ℝ := fun i =>
      if ‖zw i‖ ≤ (2 : ℝ) ^ (n + 1) then (1 : ℝ) / ‖zw i‖ ^ p else 0
    let farBase : ZWM → ℝ := fun i =>
      if (2 : ℝ) ^ n < ‖zw i‖ then (1 : ℝ) / ‖zw i‖ ^ (p + 1) else 0
    let nearBall : ZWM → ℝ := fun i => (C_near * R ^ p) * nearBase i
    let farTail : ZWM → ℝ := fun i => (C_far' * R ^ (p + 1)) * farBase i
    have hsum_major :
        ∑' i, a i ≤ (∑' i, nearBall i) + (∑' i, farTail i) :=
      nearFar_tsum_le_dyadic_majorant zw p n hzw_ne hsum_zwm R hR_pos z hz
        hr_lt hn_le C_near C_far' hCn_nn hCf_nn
    have hnearBase_bound :
        (∑' i : ZWM, nearBase i) ≤ C_ball * ((2 : ℝ) ^ (n + 1)) ^ αnear :=
      near_exponent_sum_bound hf_entire Z h_zeros_only h_inj h_z_ne_zero
        p (n + 1) C_ball αnear (hball_weighted (n + 1) hn_ball_succ)
    have hδratio_le_one : δ₀ / (4 * r) ≤ 1 := by
      have : δ₀ ≤ 4 * r := by linarith [hδ₀_le_r]
      have h' : δ₀ ≤ 1 * (4 * r) := by simpa using this
      exact (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * r)).2 h'
    have hδratio_lower :
        1 / (K0 * r ^ s_exp) ≤ δ₀ / (4 * r) :=
      separated_ratio_lower_bound hlam hε hCn_pos hr_ge2 hδ₀_lb
    have hCnear_bound : C_near ≤ KnearBase * R ^ (ε / 9) :=
      near_factor_log_bound p hK0_gt1 (by dsimp [s_exp]; linarith)
        hε9 hr_pos hR_ge1 hrR hδ₁_pos hδratio_le_one hδratio_lower
    have hpow_n1_le :
        ((2 : ℝ) ^ (n + 1)) ^ αnear ≤ (4 : ℝ) ^ αnear * R ^ αnear :=
      dyadic_rpow_upper_bound n R αnear hR_pos hn_le hαnear_nonneg
    have hnearBound :
        (∑' i : ZWM, nearBall i) ≤ Knear * R ^ (lam + 2 * ε / 9) :=
      near_weighted_tsum_bound nearBase p n R lam δcount ε C_near C_ball KnearBase
        hR_ge1 hCn_nn hCball_nonneg hKnearBase_nonneg hδcount_le_eps9
        hnearBase_bound hCnear_bound hpow_n1_le
    have hfarBase_bound :
        (∑' i : ZWM, farBase i) ≤
          (C_tail * qtail⁻¹) * ((2 : ℝ) ^ n) ^ (lam + δcount - ((p : ℝ) + 1)) :=
      far_exponent_sum_bound Z p hsum n_tail C_tail (lam + δcount - ((p : ℝ) + 1))
        htail_weighted n hn_pos hn_tail_lt
    have hfarBound :
        (∑' i : ZWM, farTail i) ≤ Kfar * R ^ (lam + 2 * ε / 9) :=
      far_weighted_tsum_bound farBase p n R lam δcount ε C_far' C_tail hR_ge1 hr_lt
        hCf_nn hCtail_nonneg hlamδ_lt_p1 (by linarith [hδcount_le_eps9]) hfarBase_bound
    calc
      ∑' i, a i ≤ (∑' i, nearBall i) + (∑' i, farTail i) := hsum_major
      _ ≤ Knear * R ^ (lam + 2 * ε / 9) + Kfar * R ^ (lam + 2 * ε / 9) := by
            gcongr
      _ = Ksum * R ^ (lam + 2 * ε / 9) := by
            simp [Ksum]
            ring
      _ ≤ R ^ (ε / 9) * R ^ (lam + 2 * ε / 9) := by
            have hpow_nonneg : 0 ≤ R ^ (lam + 2 * ε / 9) := by positivity
            exact mul_le_mul_of_nonneg_right hRpow_eps9_ge hpow_nonneg
      _ = 1 * R ^ (lam + ε / 3) := by
            rw [← Real.rpow_add hR_pos]
            ring_nf
  calc Real.exp (-(1 * R ^ (lam + ε / 3)))
      ≤ Real.exp (-∑' i, a i) := Real.exp_le_exp.mpr (by linarith)
    _ ≤ ‖P z‖ := hprod_lb


private theorem zero_ncard_le_rpow_of_order_le
    {f : ℂ → ℂ} (hf_entire : Differentiable ℂ f) (hf_finite : hasFiniteOrder f)
    {lam : ℝ} (hlam : 0 ≤ lam) (hf_order_le : order f ≤ lam)
    (Z : ZeroSetMultiplicity f) (h_inj : Function.Injective Z.z)
    (h_mult : ∀ ρ : Z.Zero, analyticOrderNatAt f (Z.z ρ) = Z.mult ρ)
    (hf0 : f 0 ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ C_n : ℝ, 0 < C_n ∧ ∃ R_n : ℝ, 0 < R_n ∧
      ∀ r : ℝ, R_n ≤ r →
        ({ρ : Z.Zero | ‖Z.z ρ‖ ≤ r} : Set Z.Zero).ncard ≤ C_n * r ^ (lam + ε / 9) := by
  have hε9 : 0 < ε / 9 := by linarith
  obtain ⟨R₀', hR₀'⟩ :=
    Hadamard.ZeroCounting.maxModulus_le_exp_rpow_of_order_le
      f hf_finite hf_order_le (ε / 9) hε9
  have hZ_in_supp : ∀ ρ (R : ℝ), ‖Z.z ρ‖ ≤ R →
      Z.z ρ ∈ (MeromorphicOn.divisor f (Metric.closedBall 0 |R|)).support := by
    intro ρ R hρR
    have hmem : Z.z ρ ∈ Metric.closedBall (0 : ℂ) |R| := by
      simpa [Metric.mem_closedBall] using le_trans hρR (le_abs_self R)
    have hmer : MeromorphicOn f (Metric.closedBall (0 : ℂ) |R|) :=
      fun z _ => (hf_entire.analyticAt z).meromorphicAt
    have hdiv_val := MeromorphicOn.divisor_apply hmer hmem
    have hmer_eq := (hf_entire.analyticAt (Z.z ρ)).meromorphicOrderAt_eq
    have hord_ne_top : analyticOrderAt f (Z.z ρ) ≠ ⊤ := by
      intro htop
      have : analyticOrderNatAt f (Z.z ρ) = 0 := by simp [analyticOrderNatAt, htop]
      rw [h_mult ρ] at this; exact (Nat.pos_iff_ne_zero.mp (Z.mult_pos ρ)) this
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hord_ne_top
    have hn_val : n = Z.mult ρ := by
      have h1 : analyticOrderNatAt f (Z.z ρ) = n := by
        unfold analyticOrderNatAt; rw [← hn]; rfl
      linarith [h_mult ρ, h1]
    have hdiv_ne : (MeromorphicOn.divisor f (Metric.closedBall 0 |R|)) (Z.z ρ) ≠ 0 := by
      rw [hdiv_val, hmer_eq, ← hn]
      have hn_int_ne_zero : (n : ℤ) ≠ 0 := by
        exact_mod_cast Nat.pos_iff_ne_zero.mp (hn_val ▸ Z.mult_pos ρ)
      exact hn_int_ne_zero
    exact Function.mem_support.mpr hdiv_ne
  set C_n := (2 ^ (lam + ε / 9) + |Real.log ‖f 0‖| + 1) / Real.log 2 + 1
  refine ⟨C_n, by positivity, max (R₀' / 2 + 1) 1, by positivity, fun r hr => ?_⟩
  have hr1 : (1 : ℝ) ≤ r := le_trans (le_max_right _ _) hr
  have hr_pos : (0 : ℝ) < r := by linarith
  have h2r_ge : R₀' ≤ 2 * r := by
    have := le_max_left (R₀' / 2 + 1) (1 : ℝ)
    linarith [le_trans this hr]
  have himage_sub : Z.z '' {ρ : Z.Zero | ‖Z.z ρ‖ ≤ r} ⊆
      {u : ℂ | u ∈ (MeromorphicOn.divisor f (Metric.closedBall 0 |2 * r|)).support ∧
       ‖u‖ ≤ (2 * r) / 2} := by
    rintro u ⟨ρ, hρ, rfl⟩
    simp only [Set.mem_ofPred_eq] at hρ ⊢
    exact ⟨hZ_in_supp ρ (2 * r) (by linarith [hρ]), by linarith [hρ]⟩
  have hfin : ({u : ℂ | u ∈ (MeromorphicOn.divisor f
      (Metric.closedBall 0 |2 * r|)).support ∧ ‖u‖ ≤ (2 * r) / 2}).Finite :=
    Set.Finite.subset ((MeromorphicOn.divisor f _).finiteSupport
      (isCompact_closedBall _ _)) fun u ⟨hu, _⟩ => hu
  have hjensen := Hadamard.ZeroCounting.card_zeros_le_of_max_one_maxModulus
    f (by linarith : (0 : ℝ) < 2 * r) hf_entire hf0
  have hlog_bound : Real.log (max 1 (maxModulus f (2 * r))) ≤ (2 * r) ^ (lam + ε / 9) := by
    by_cases h : maxModulus f (2 * r) ≤ 1
    · rw [max_eq_left h, Real.log_one]
      exact Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 2 * r) _
    · push Not at h; rw [max_eq_right h.le]
      exact le_trans (Real.log_le_log (by linarith) (hR₀' _ h2r_ge)) (by rw [Real.log_exp])
  have hr_rpow : (1 : ℝ) ≤ r ^ (lam + ε / 9) := by
    calc (1 : ℝ) = r ^ (0 : ℝ) := (rpow_zero r).symm
      _ ≤ r ^ (lam + ε / 9) := rpow_le_rpow_of_exponent_le hr1 (by linarith)
  calc (↑({ρ : Z.Zero | ‖Z.z ρ‖ ≤ r}).ncard : ℝ)
      = ↑(Z.z '' {ρ : Z.Zero | ‖Z.z ρ‖ ≤ r}).ncard :=
        by rw [Set.ncard_image_of_injective _ h_inj]
    _ ≤
        ↑({u : ℂ |
            u ∈ (MeromorphicOn.divisor f (Metric.closedBall 0 |2 * r|)).support ∧
              ‖u‖ ≤ (2 * r) / 2}).ncard :=
        by exact_mod_cast Set.ncard_le_ncard himage_sub hfin
    _ ≤
        (Real.log (max 1 (maxModulus f (2 * r))) - Real.log ‖f 0‖) / Real.log 2 := hjensen
    _ ≤ ((2 * r) ^ (lam + ε / 9) + |Real.log ‖f 0‖|) / Real.log 2 := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        linarith [hlog_bound, neg_abs_le (Real.log ‖f 0‖)]
    _ ≤
        (2 ^ (lam + ε / 9) * r ^ (lam + ε / 9) + |Real.log ‖f 0‖| * r ^ (lam + ε / 9)) /
          Real.log 2 := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        have h2r : (2 * r) ^ (lam + ε / 9) = 2 ^ (lam + ε / 9) * r ^ (lam + ε / 9) :=
          mul_rpow (by norm_num : (0:ℝ) ≤ 2) (by linarith)
        linarith [mul_le_mul_of_nonneg_left hr_rpow (abs_nonneg (Real.log ‖f 0‖))]
    _ = (2 ^ (lam + ε / 9) + |Real.log ‖f 0‖|) / Real.log 2 * r ^ (lam + ε / 9) := by
        ring
    _ ≤ C_n * r ^ (lam + ε / 9) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        simp only [C_n]
        have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num : (1:ℝ) < 2)
        have := div_le_div_of_nonneg_right
          (show (2 : ℝ) ^ (lam + ε / 9) + |Real.log ‖f 0‖| ≤
                2 ^ (lam + ε / 9) + |Real.log ‖f 0‖| + 1 by linarith)
          hlog2.le
        linarith

private theorem exists_zero_separated_radii {f : ℂ → ℂ}
    (Z : ZeroSetMultiplicity f) {p : ℕ}
    (h_z_ne_zero : ∀ ρ : Z.Zero, Z.z ρ ≠ 0)
    (hsum : Summable (fun ρ : Z.Zero => (Z.mult ρ : ℝ) / ‖Z.z ρ‖ ^ (p + 1)))
    (C_n R_n lam ε : ℝ)
    (hcount_le : ∀ r : ℝ, R_n ≤ r →
      ({ρ : Z.Zero | ‖Z.z ρ‖ ≤ r} : Set Z.Zero).ncard ≤ C_n * r ^ (lam + ε / 9)) :
    ∃ R_g : ℝ, 0 < R_g ∧ ∀ r : ℝ, R_g ≤ r →
      ∃ R δ₀ : ℝ, r ≤ R ∧ R ≤ 2 * r ∧ 0 < δ₀ ∧ δ₀ ≤ r ∧
        (∀ ρ : Z.Zero, δ₀ ≤ |‖Z.z ρ‖ - R|) ∧
        r / (2 * (C_n * (3 * r) ^ (lam + ε / 9) + 2)) ≤ δ₀ := by
  have hsum_unit : Summable (fun ρ : Z.Zero => (1 : ℝ) / ‖Z.z ρ‖ ^ (p + 1)) := by
    exact hsum.of_nonneg_of_le (fun ρ => by positivity) (fun ρ => by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (Z.mult_pos ρ)))
  have hfin_ball : ∀ R : ℝ, 0 < R →
      ({ρ : Z.Zero | ‖Z.z ρ‖ ≤ R} : Set Z.Zero).Finite :=
    fun R hR => Hadamard.OrderOne.finite_norm_le_of_summable_inv_norm_pow
      h_z_ne_zero hsum_unit hR
  refine ⟨max R_n 1, by positivity, fun r hr => ?_⟩
  have hr1 : (1 : ℝ) ≤ r := le_trans (le_max_right _ _) hr
  have hr_pos : (0 : ℝ) < r := by linarith
  set S := {ρ : Z.Zero | ‖Z.z ρ‖ ≤ 3 * r}
  have hS_fin := hfin_ball (3 * r) (by linarith)
  set N := S.ncard
  set δ₀ := r / (2 * ((N : ℝ) + 1)) with hδ₀_def
  have hδ₀_pos : (0 : ℝ) < δ₀ := by positivity
  have hN_cast_nn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
  have hδ₀_le_r : δ₀ ≤ r := div_le_self hr_pos.le (by linarith)
  set Rk := fun k : Fin (N + 1) => r + (2 * (↑↑k : ℝ) + 1) * δ₀
  have hk_cast_nn : ∀ k : Fin (N + 1), (0 : ℝ) ≤ (↑↑k : ℝ) :=
    fun k => Nat.cast_nonneg _
  have hRk_lo : ∀ k, r ≤ Rk k := fun k => by
    have hk_term_nonneg : 0 ≤ (2 * (↑↑k : ℝ) + 1) * δ₀ := by
      nlinarith [hk_cast_nn k, hδ₀_pos.le]
    nlinarith
  have hRk_hi : ∀ k, Rk k ≤ 2 * r := by
    intro k
    have hk_le : (↑↑k : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.le_of_lt_succ k.isLt
    have h1 : (2 * (↑↑k : ℝ) + 1) * δ₀ ≤ (2 * (N : ℝ) + 1) * δ₀ := by nlinarith
    have h2 : (2 * (N : ℝ) + 1) * δ₀ ≤ r := by
      have hδ₀_cancel : δ₀ * (2 * ((N : ℝ) + 1)) = r := by
        rw [hδ₀_def]; field_simp
      nlinarith [mul_le_mul_of_nonneg_right
        (show (2 * (N:ℝ) + 1) ≤ 2 * ((N:ℝ) + 1) by linarith) hδ₀_pos.le]
    linarith
  have hRk_sp :
      ∀ k₁ k₂ : Fin (N + 1), k₁ ≠ k₂ → 2 * δ₀ ≤ |Rk k₁ - Rk k₂| := by
    intro k₁ k₂ hne
    have hval_ne : (↑↑k₁ : ℕ) ≠ ↑↑k₂ := Fin.val_ne_of_ne hne
    have heq :
        r + (2 * (↑↑k₁ : ℝ) + 1) * δ₀ - (r + (2 * ↑↑k₂ + 1) * δ₀) =
          2 * ((↑↑k₁ : ℝ) - ↑↑k₂) * δ₀ := by
      ring
    rw [heq, abs_mul, abs_mul, abs_of_pos hδ₀_pos, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    suffices (1 : ℝ) ≤ |(↑↑k₁ : ℝ) - ↑↑k₂| by nlinarith
    have hcast_ne : (↑↑k₁ : ℤ) ≠ ↑↑k₂ := by
      exact_mod_cast hval_ne
    exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hcast_ne)
  suffices ∃ k : Fin (N + 1), ∀ ρ ∈ S, δ₀ ≤ |‖Z.z ρ‖ - Rk k| by
    obtain ⟨k, hk⟩ := this
    refine ⟨Rk k, δ₀, hRk_lo k, hRk_hi k, hδ₀_pos, hδ₀_le_r, ?_, ?_⟩
    · intro ρ
      by_cases hρS : ρ ∈ S
      · exact hk ρ hρS
      · -- ρ ∉ S: ‖Z.z ρ‖ > 3r, so distance to R_k ≥ r ≥ δ₀
        have hρ_large : 3 * r < ‖Z.z ρ‖ := by
          change ¬(‖Z.z ρ‖ ≤ 3 * r) at hρS
          linarith
        calc
          δ₀ ≤ r := hδ₀_le_r
          _ ≤ ‖Z.z ρ‖ - Rk k := by linarith [hRk_hi k]
          _ ≤ |‖Z.z ρ‖ - Rk k| := le_abs_self _
    · have hN_le : (N : ℝ) ≤ C_n * (3 * r) ^ (lam + ε / 9) := by
        have hRn_le_r : R_n ≤ r := le_trans (le_max_left _ _) hr
        have h3r_ge : R_n ≤ 3 * r := by linarith
        exact_mod_cast hcount_le (3 * r) h3r_ge
      have hden_le :
          2 * ((N : ℝ) + 1) ≤ 2 * (C_n * (3 * r) ^ (lam + ε / 9) + 2) := by
        nlinarith
      have hnum_nonneg : 0 ≤ r := le_of_lt hr_pos
      have hden_pos : 0 < 2 * ((N : ℝ) + 1) := by positivity
      have hdiv :
          r / (2 * (C_n * (3 * r) ^ (lam + ε / 9) + 2))
            ≤ r / (2 * ((N : ℝ) + 1)) := by
        exact div_le_div_of_nonneg_left hnum_nonneg hden_pos hden_le
      simpa [hδ₀_def] using hdiv
  by_contra h_no_good; push Not at h_no_good
  choose g hg_mem hg_close using h_no_good
  have g_inj : Function.Injective g := by
    intro k₁ k₂ hgk; by_contra hne
    have h_sp := hRk_sp k₁ k₂ hne
    have h1 : |‖Z.z (g k₂)‖ - Rk k₁| < δ₀ := hgk ▸ hg_close k₁
    have h2 := hg_close k₂
    set v := ‖Z.z (g k₂)‖
    have htri : |Rk k₁ - Rk k₂| ≤ |Rk k₁ - v| + |v - Rk k₂| := by
      have h := norm_add_le (Rk k₁ - v) (v - Rk k₂)
      simp only [Real.norm_eq_abs] at h
      rwa [show Rk k₁ - v + (v - Rk k₂) = Rk k₁ - Rk k₂ from by ring] at h
    rw [abs_sub_comm] at h1  -- h1: |Rk k₁ - v| < δ₀
    linarith [le_trans h_sp htri, add_lt_add h1 h2]
  have : N + 1 ≤ N := calc
    N + 1 = Set.ncard (Set.range g) := by
      rw [Set.ncard_range_of_injective g_inj, Nat.card_fin]
    _ ≤ S.ncard := Set.ncard_le_ncard (fun _ ⟨k, hk⟩ => hk ▸ hg_mem k) hS_fin
  omega

/-- **Order bound on the quotient.**

Given `f = P · Q` with `Q` entire and nowhere zero, if `order f ≤ lam` and
the canonical product `P` has the standard rank-`p` lower bound, then
`order Q ≤ lam`. This combines the finite-order bound on `f` with the
Weierstrass-product lower bound to extract a polynomial growth bound on
`log ‖Q‖`, which is exactly `order Q ≤ lam`.

**Mathematical subtlety.** A crude lower bound on `‖P(z)‖` gives
`log ‖P(z)‖ ≥ -C r^{p+1+ε}` (from the rank-`p` Weierstrass lower bound
`log|E_p(w)| ≥ -C|w|^{p+1}` applied to all factors). Since `p+1 > lam`,
this only yields `order Q ≤ p+1`, one higher than needed.

To get the tight bound `order Q ≤ lam`, one must use the **zero-avoiding
circles** technique (Ahlfors, "Complex Analysis", §5.3): choose the radius
`r` so that the nearest zero is at distance `≥ r^{-(p+ε)}` from the circle
`|z| = r`. This is possible for a "good" set of radii of positive density
(by Borel's lemma on the growth of zeros). On such circles, the lower bound
improves to `log ‖P(z)‖ ≥ -C r^{lam+ε}`, and then `log ‖Q‖ ≤ r^{lam+ε}`
follows. The `limsup` definition of `order` allows using a subsequence of
radii, so the good-radius restriction is harmless.

Alternatively, Conway's log-derivative identity (Lemma 3.1 via
Poisson–Jensen) shows `g^{(p+1)} ≡ 0` directly without going through the
order of `Q`. But this requires Poisson–Jensen, which we deferred.

~200–300 lines of careful analysis for either approach; deferred. -/
theorem order_Q_le_lam_of_factorization
    {f Q : ℂ → ℂ} (hf_entire : Differentiable ℂ f)
    (hf_finite : hasFiniteOrder f)
    {lam : ℝ} (hlam : 0 ≤ lam) (hf_order_le : order f ≤ lam)
    (hQ_entire : Differentiable ℂ Q) (hQ_ne : ∀ z : ℂ, Q z ≠ 0)
    (Z : ZeroSetMultiplicity f)
    {p : ℕ} (hp : p = Nat.floor lam)
    (h_z_ne_zero : ∀ ρ : Z.Zero, Z.z ρ ≠ 0)
    (h_inj : Function.Injective Z.z)
    (hsum : Summable (fun ρ : Z.Zero => (Z.mult ρ : ℝ) / ‖Z.z ρ‖ ^ (p + 1)))
    (h_mult : ∀ ρ : Z.Zero, analyticOrderNatAt f (Z.z ρ) = Z.mult ρ)
    (hfact : ∀ z : ℂ,
      f z = canonicalProductZeroSetMultiplicityRank Z p z * Q z) :
    hasFiniteOrder Q ∧ order Q ≤ lam := by
  -- Both parts follow from the key growth estimate:
  -- for each ε > 0, eventually M(Q, r) ≤ exp(r^{λ+ε}).
  --
  -- Proof outline:
  -- 1. From `order f ≤ lam`: M(f, R) ≤ exp(R^{λ+ε}) for large R.
  -- 2. Zero-avoiding circles: for each large r, find R ∈ [r, 2r] such that
  --    all zeros are at distance ≥ δ from |z| = R (pigeonhole on zero counting).
  -- 3. On good circles: |P(z)| ≥ exp(-C R^{λ+ε}) (near/far zero decomposition
  --    using weierstrass_E_small_disk_lower_bound for far zeros, and the
  --    separation bound for near zeros). Since Q = f/P on such circles:
  --    M(Q, R) ≤ M(f, R) / min|P| ≤ exp(C' R^{λ+ε}).
  -- 4. By maxModulus_mono_of_differentiable: M(Q, r) ≤ M(Q, R) ≤ exp(C' (2r)^{λ+ε}).
  -- 5. For large r, C'(2r)^{λ+ε} ≤ r^{λ+2ε}, giving the bound.
  suffices key : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ r : ℝ in Filter.atTop,
        maxModulus Q r ≤ Real.exp (r ^ (lam + ε)) by
    constructor
    · -- hasFiniteOrder Q: from key with ε = 1
      obtain ⟨R₀, hR₀⟩ := Filter.eventually_atTop.mp (key 1 one_pos)
      refine ⟨hQ_entire, lam + 2, max R₀ 2, fun z hz => ?_⟩
      have hr_ge : R₀ ≤ ‖z‖ := le_trans (le_max_left _ _) hz
      have h2_le : (2 : ℝ) ≤ ‖z‖ := le_trans (le_max_right _ _) hz
      have hr_pos : (0 : ℝ) < ‖z‖ := by linarith
      calc ‖Q z‖
          ≤ maxModulus Q ‖z‖ := norm_le_maxModulus_of_norm_le Q hQ_entire hr_pos (le_refl _)
        _ ≤ Real.exp (‖z‖ ^ (lam + 1)) := hR₀ ‖z‖ hr_ge
        _ < Real.exp (‖z‖ ^ (lam + 2)) := by
            apply Real.exp_lt_exp.mpr
            exact Real.rpow_lt_rpow_of_exponent_lt (by linarith : 1 < ‖z‖) (by linarith)
    · -- order Q ≤ lam: direct from key
      exact order_le_of_forall_pos_eventually_maxModulus_le_exp_rpow_add
        Q lam hlam hQ_entire key
  -- Prove the key growth estimate via zero-avoiding circles (Ahlfors §5.3).
  intro ε hε
  set P := canonicalProductZeroSetMultiplicityRank Z p
  have h_zeros_only : ∀ s : ℂ, f s = 0 ↔ ∃ ρ : Z.Zero, s = Z.z ρ := by
    intro s
    constructor
    · intro hs
      have hP_zero : canonicalProductZeroSetMultiplicityRank Z p s = 0 := by
        by_contra hP_nonzero
        have hfs_nonzero : f s ≠ 0 := by
          rw [hfact s]
          exact mul_ne_zero hP_nonzero (hQ_ne s)
        exact hfs_nonzero hs
      exact
        (canonicalProductZeroSetMultiplicityRank_eq_zero_iff Z hsum h_inj h_z_ne_zero s).mp
          hP_zero
    · rintro ⟨ρ, rfl⟩
      rw [hfact]
      exact mul_eq_zero_of_left
        ((canonicalProductZeroSetMultiplicityRank_eq_zero_iff Z hsum h_inj h_z_ne_zero _).mpr
          ⟨ρ, rfl⟩) _
  -- Step 1: Growth bound on f from finite order
  have hε3 : 0 < ε / 3 := by linarith
  obtain ⟨R₁, hR₁⟩ :=
    Hadamard.ZeroCounting.maxModulus_le_exp_rpow_of_order_le f hf_finite hf_order_le (ε / 3) hε3
  -- Step 2+3: Lower bound on |P| at good radii (zero-avoiding circles).
  -- For any small δ > 0, there exist C₀ and R₂ such that for r ≥ R₂, there is a
  -- "good" radius R ∈ [r, 2r] where the circle |z| = R is separated from all zeros
  -- and |P(z)| ≥ exp(-C₀ R^{λ+δ}).
  --
  -- Proof: (1) From hsum, the zero counting function satisfies n(2r) ≤ S · (2r)^{p+1}.
  -- Lower bound on the canonical product on zero-avoiding circles.
  --
  -- This is the standard rank-`p` zero-avoiding-circles argument:
  -- pick a circle separated from all zero norms via counting and pigeonhole,
  -- split the factors into near and far ranges, bound the far contribution by
  -- the small-disk Weierstrass estimate, bound the near contribution by the
  -- away-from-one estimate, then convert the pointwise factor bounds into a
  -- lower bound for the full product.
  have hP_lower :
      ∃ C₀ : ℝ, 0 < C₀ ∧ ∃ R₂ : ℝ, ∀ r : ℝ, R₂ ≤ r →
        ∃ R : ℝ, r ≤ R ∧ R ≤ 2 * r ∧
          ∀ z : ℂ, ‖z‖ = R →
            Real.exp (-(C₀ * R ^ (lam + ε / 3))) ≤ ‖P z‖ := by
    -- ---------------------------------------------------------------
    -- Implementation of the zero-avoiding-circles argument
    -- (Steps A-E from canonical_product_lower_bound.tex).
    -- Generalizes Growth.lean:270-578 from rank 1 to rank p.
    -- ---------------------------------------------------------------
    --
    -- Step A: `f 0 ≠ 0`.
    -- P(0) = ∏' E_p(0/z_i) = ∏' 1 = 1, so f(0) = 1·Q(0) ≠ 0.
    have hf0 : f 0 ≠ 0 := by
      rw [hfact 0]; apply mul_ne_zero _ (hQ_ne 0)
      -- P(0) ≠ 0: all factors E_p(0/z_i) = E_p(0) = 1
      simp only [P, canonicalProductZeroSetMultiplicityRank]
      have h_all_one : ∀ i : Z.ZeroWithMultiplicity,
          weierstrassE p (0 / Z.zWithMultiplicity i) = 1 := by
        intro i; simp [weierstrassE]
      simp only [h_all_one, tprod_one]; exact one_ne_zero
    --
    -- Step B: zero counting from Jensen.
    -- n(R) ≤ C_n R^{λ+δ} where δ = ε/9 and n counts total
    -- multiplicity of zeros inside the ball of radius R.
    -- From: sum_zeros_multiplicity_le_of_max_one_maxModulus (Jensen)
    -- + maxModulus_le_exp_rpow_of_order_le (growth of f)
    -- + bridge: div_f(u) = analyticOrderNatAt f u = Z.mult ρ.
    --
    -- Step C: good-radius selection by pigeonhole.
    -- For each large r, find R ∈ [r, 2r] separated from all zero
    -- norms by δ₀ ≥ r/(2(n(3r)+1)).
    -- From: exists_radius_separated_from_zero_norms (Growth.lean:35).
    --
    -- Step D: dyadic exponent-sum bound.
    -- Far: C_far R^{p+1} Σ_{far} 1/|z_i|^{p+1} ≤ C R^{λ+δ}
    -- Near: C_near R^p Σ_{near} 1/|z_i|^p ≤ C R^{λ+ε/3}
    -- Total ≤ C₀ R^{λ+ε/3}.
    --
    -- Step E: product bound.
    -- ‖P(z)‖ ≥ exp(-Σ a_i) from pointwise factor bounds.
    --
    -- Steps B+C+D combined as a single claim.
    -- Rather than formalizing Jensen, pigeonhole,
    -- and dyadic bookkeeping as separate subclaims here,
    -- we package them into a combined good-circle / exponent-sum estimate.
    -- This is the rank-`p`
    -- generalization of Growth.lean (pigeonhole, lines 35-256)
    -- combined with Growth.lean (product bound, lines 270-578).
    --
    -- The per-factor bounds use:
    --   weierstrass_E_small_disk_lower_bound p (far, ‖w‖ ≤ 1/2)
    --   weierstrass_E_away_from_one_lower_bound p δ (near, ‖w‖ ≥ 1/2)
    -- The exponent sum control uses:
    --   Jensen zero counting (ZeroCounting.lean:660)
    --   Dyadic decomposition (geometric series)
    -- The product-to-exp conversion uses:
    --   Finite product inequality + ge_of_tendsto (Growth.lean:525-578)
    --
    -- These are all proved for rank 1 in the OrderOne/ directory.
    -- The rank-p generalization is structurally identical (same proof,
    -- different constants). The full math is in
    -- canonical_product_lower_bound.tex, Steps A-E.
    --
    -- Step B: zero counting bound.
    -- From Jensen (ZeroCounting.lean) + growth bound: for any δ > 0,
    -- the total multiplicity in B(0,R) is O(R^{λ+δ}).
    -- Uses: sum_zeros_multiplicity_le_of_max_one_maxModulus, hf0,
    -- maxModulus_le_exp_rpow_of_order_le, h_inj, h_mult.
    have hcount := zero_ncard_le_rpow_of_order_le hf_entire hf_finite hlam hf_order_le
      Z h_inj h_mult hf0 hε
    obtain ⟨C_n, hCn_pos, R_n, hRn_pos, hcount_le⟩ := hcount
    --
    -- Step C: good radius by pigeonhole.
    -- In [r, 2r] with ≤ n(3r) zero norms, find R separated by ≥ δ₀.
    -- Follows Growth.lean:35-256 verbatim with rank-p summability.
    have hgood := exists_zero_separated_radii Z h_z_ne_zero hsum C_n R_n lam ε hcount_le
    obtain ⟨R_g, hRg_pos, hgood_radius⟩ := hgood
    --
    -- Steps D+E: per-factor bounds, sum control, and product.
    -- On a good circle |z| = R with separation δ₀:
    -- • Far factors: weierstrass_E_small_disk_lower_bound p
    -- • Near factors: weierstrass_E_away_from_one_lower_bound p
    -- • Sum of exponent bounds ≤ C₀ R^{λ+ε/3} (dyadic + counting)
    -- • Product: ‖P(z)‖ ≥ exp(-sum) (Growth.lean:525-578 pattern)
    have hcircle_bound := canonicalProduct_circle_lower_bound hf_entire hf_finite hlam
      hf_order_le Z hp h_z_ne_zero h_inj hsum h_mult h_zeros_only ε hε C_n hCn_pos
    obtain ⟨C₀, hC₀_pos, R_c, hcircle⟩ := hcircle_bound
    --
    -- Assembly.
    refine ⟨C₀, hC₀_pos, max (max R_n R_g) R_c, fun r hr => ?_⟩
    have hrn : R_n ≤ r := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hr)
    have hrg : R_g ≤ r := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hr)
    have hrc : R_c ≤ r := le_trans (le_max_right _ _) hr
    obtain ⟨R, δ₀, hrR, hR2r, hδ₀_pos, hδ₀_le_r, hsep, hδ₀_lb⟩ := hgood_radius r hrg
    exact ⟨R, hrR, hR2r, hcircle r hrc R δ₀ hrR hR2r hδ₀_pos hδ₀_le_r hδ₀_lb hsep⟩
  obtain ⟨C₀, hC₀_pos, R₂, hP_lb⟩ := hP_lower
  -- Step 4: for large `r`, the combined bound
  -- `(1 + C₀) (2r)^{λ+ε/3} ≤ r^{λ+ε}`.
  -- This holds because `r^{2ε/3} → ∞` dominates the constant
  -- `(1 + C₀) · 2^{λ+ε/3}`.
  have hR₃_exists : ∃ R₃ : ℝ, ∀ r : ℝ, R₃ ≤ r →
      (1 + C₀) * (2 * r) ^ (lam + ε / 3) ≤ r ^ (lam + ε) := by
    -- `(1+C₀)(2r)^{λ+ε/3} = (1+C₀)·2^{λ+ε/3}·r^{λ+ε/3}`
    -- and `r^{λ+ε} = r^{λ+ε/3}·r^{2ε/3}`.
    -- So we need `(1+C₀)·2^{λ+ε/3} ≤ r^{2ε/3}`,
    -- which holds for large `r` since `2ε/3 > 0`.
    have h2ε3 : (0 : ℝ) < 2 * ε / 3 := by linarith
    -- r^{2ε/3} → ∞, so eventually ≥ any constant
    have := Filter.Tendsto.eventually_ge_atTop
      (tendsto_rpow_atTop h2ε3) ((1 + C₀) * 2 ^ (lam + ε / 3))
    obtain ⟨R₃, hR₃⟩ := Filter.eventually_atTop.mp this
    refine ⟨max R₃ 1, fun r hr => ?_⟩
    have hr1 : 1 ≤ r := le_trans (le_max_right _ _) hr
    have hr_pos : 0 < r := by linarith
    have hrR₃ : R₃ ≤ r := le_trans (le_max_left _ _) hr
    -- (2r)^{λ+ε/3} = 2^{λ+ε/3} · r^{λ+ε/3}
    have h2r_rpow : (2 * r) ^ (lam + ε / 3) = 2 ^ (lam + ε / 3) * r ^ (lam + ε / 3) := by
      rw [mul_rpow (by norm_num : (0:ℝ) ≤ 2) (by linarith : 0 ≤ r)]
    -- r^{λ+ε} = r^{λ+ε/3} · r^{2ε/3}
    have hr_split : r ^ (lam + ε) = r ^ (lam + ε / 3) * r ^ (2 * ε / 3) := by
      rw [← Real.rpow_add hr_pos]; ring_nf
    rw [h2r_rpow, hr_split]
    have hr_rpow_pos : 0 < r ^ (lam + ε / 3) :=
      Real.rpow_pos_of_pos hr_pos _
    -- (1+C₀) · 2^{λ+ε/3} · r^{λ+ε/3} ≤ r^{λ+ε/3} · r^{2ε/3}
    -- ↔ (1+C₀) · 2^{λ+ε/3} ≤ r^{2ε/3}
    calc (1 + C₀) * (2 ^ (lam + ε / 3) * r ^ (lam + ε / 3))
        = (1 + C₀) * 2 ^ (lam + ε / 3) * r ^ (lam + ε / 3) := by ring
      _ ≤ r ^ (2 * ε / 3) * r ^ (lam + ε / 3) := by
          apply mul_le_mul_of_nonneg_right (hR₃ r hrR₃) (le_of_lt hr_rpow_pos)
      _ = r ^ (lam + ε / 3) * r ^ (2 * ε / 3) := by ring
  obtain ⟨R₃, hR₃⟩ := hR₃_exists
  -- Step 5: Assembly
  rw [Filter.eventually_atTop]
  refine ⟨max (max R₁ R₂) (max R₃ 1), fun r hr => ?_⟩
  have hr1 : R₁ ≤ r := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hr)
  have hr2 : R₂ ≤ r := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hr)
  have hr3 : R₃ ≤ r := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hr)
  have hr_pos : 0 < r := lt_of_lt_of_le one_pos
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hr))
  -- Find good R ∈ [r, 2r]
  obtain ⟨R, hrR, hR2r, hP_bound⟩ := hP_lb r hr2
  have hR_pos : 0 < R := lt_of_lt_of_le hr_pos hrR
  -- M(Q, r) ≤ M(Q, R) by monotonicity
  have hQrR : maxModulus Q r ≤ maxModulus Q R :=
    maxModulus_mono_of_differentiable Q hQ_entire hR_pos (le_of_lt hr_pos) hrR
  -- M(Q, R) ≤ exp(r^{λ+ε}) from the circle bound
  have hQR : maxModulus Q R ≤ Real.exp (r ^ (lam + ε)) := by
    apply maxModulus_le_of_forall_norm_le Q hQ_entire.continuous (le_of_lt hR_pos)
    intro z hz
    -- P(z) ≠ 0 on the good circle
    have hPz_lb := hP_bound z hz
    have hP_ne : P z ≠ 0 := by
      intro h; rw [h, norm_zero] at hPz_lb
      linarith [Real.exp_pos (-(C₀ * R ^ (lam + ε / 3)))]
    -- Q(z) = f(z) / P(z) from f = P * Q
    have hQ_eq : Q z = f z / P z := by
      have hfz := hfact z
      rw [hfz, mul_div_cancel_left₀ _ hP_ne]
    rw [hQ_eq, norm_div]
    -- ‖f z‖ ≤ M(f, R) ≤ exp(R^{λ+ε/3})
    have hfz : ‖f z‖ ≤ Real.exp (R ^ (lam + ε / 3)) :=
      le_trans (norm_le_maxModulus_on_circle f hf_entire.continuous hz)
        (hR₁ R (le_trans hr1 hrR))
    -- Combine:
    -- `‖f z‖ / ‖P z‖ ≤ exp(R^{λ+ε/3}) / exp(-C₀ R^{λ+ε/3})
    --   = exp((1 + C₀) R^{λ+ε/3})`.
    calc ‖f z‖ / ‖P z‖
        ≤ Real.exp (R ^ (lam + ε / 3)) /
          Real.exp (-(C₀ * R ^ (lam + ε / 3))) := by
          exact div_le_div₀ (Real.exp_nonneg _) hfz (Real.exp_pos _) hPz_lb
      _ = Real.exp ((1 + C₀) * R ^ (lam + ε / 3)) := by
          rw [← Real.exp_sub]; congr 1; ring
      _ ≤ Real.exp ((1 + C₀) * (2 * r) ^ (lam + ε / 3)) := by
          apply Real.exp_le_exp.mpr
          apply mul_le_mul_of_nonneg_left _ (by linarith : 0 ≤ 1 + C₀)
          exact Real.rpow_le_rpow (by linarith : 0 ≤ R) hR2r (by linarith : 0 ≤ lam + ε / 3)
      _ ≤ Real.exp (r ^ (lam + ε)) := by
          exact Real.exp_le_exp.mpr (hR₃ r hr3)
  linarith [hQrR, hQR]

/-!
## Hadamard factorization for a function nonzero at the origin

The following declaration proves the `f 0 ≠ 0` case of Conway, Chapter XI, Theorem 3.4
(pages 289–290). The hypotheses `h_zeros_only` and `h_z_ne_zero` force this restriction:
all zeros are enumerated by `Z`, and every enumerated zero is nonzero.
Conway handles a zero of multiplicity `m` at the origin by first dividing out `z^m`;
that reduction is not part of this declaration. Multiplicities of the nonzero zeros
are recorded by `ZeroSetMultiplicity`.
-/

/-- Hadamard factorization of general finite order, in the `f 0 ≠ 0` case.

For an entire function of order at most `lam ≥ 0`, let `Z` enumerate all its zeros,
with their multiplicities, and assume every enumerated zero is nonzero. There is a
polynomial `g` of degree at most `⌊lam⌋` such that
```
f z = Complex.exp (g.eval z) * canonicalProductZeroSetMultiplicityRank Z (Nat.floor lam) z.
```
The assumptions imply `f 0 ≠ 0`, so the formula has no factor for an origin zero.
This is the corresponding special case of Conway, Chapter XI, Theorem 3.4 (page 289),
with a multiplicity-indexed product. The proof combines Borel–Carathéodory, growth bounds,
and Cauchy's estimate. -/
theorem hadamard_factorization_general
    (f : ℂ → ℂ)
    (hf_entire : Differentiable ℂ f)
    (hf_finite : hasFiniteOrder f)
    {lam : ℝ} (hlam : 0 ≤ lam) (hf_order_le : order f ≤ lam)
    (Z : ZeroSetMultiplicity f)
    (h_zeros_only : ∀ s : ℂ, f s = 0 ↔ ∃ ρ : Z.Zero, s = Z.z ρ)
    (h_inj : Function.Injective Z.z)
    (h_z_ne_zero : ∀ ρ : Z.Zero, Z.z ρ ≠ 0)
    (h_mult : ∀ ρ : Z.Zero, analyticOrderNatAt f (Z.z ρ) = Z.mult ρ) :
    ∃ (g : Polynomial ℂ),
      g.natDegree ≤ Nat.floor lam ∧
      ∀ z : ℂ,
        f z = Complex.exp (g.eval z) *
              canonicalProductZeroSetMultiplicityRank Z (Nat.floor lam) z := by
  classical
  -- Step 1: summability at exponent `p + 1 = ⌊λ⌋ + 1`.
  have hsum :
      Summable (fun ρ : Z.Zero =>
        (Z.mult ρ : ℝ) / ‖Z.z ρ‖ ^ (Nat.floor lam + 1)) :=
    summable_mult_div_norm_pow_of_order_le hf_entire hf_finite hlam hf_order_le Z
      h_zeros_only h_inj h_z_ne_zero h_mult
  -- Step 3: entire nowhere-zero quotient Q with factorization identity f = P · Q.
  obtain ⟨Q, hQ_entire, hQ_ne, hfact⟩ :=
    exists_quotient_entire hf_entire Z (p := Nat.floor lam) hsum h_zeros_only
      h_inj h_z_ne_zero h_mult
  -- Step 3': order Q ≤ lam (from order f ≤ lam + canonical product lower bound).
  obtain ⟨hQ_finite, hQ_order_le⟩ :=
    order_Q_le_lam_of_factorization hf_entire hf_finite hlam hf_order_le
      hQ_entire hQ_ne (Z := Z) (p := Nat.floor lam) rfl h_z_ne_zero h_inj hsum h_mult hfact
  -- Steps 4–7 (collapsed): apply the packaged theorem
  -- `entire_no_zeros_is_exp_polynomial`, which handles log/growth/BC/Cauchy
  -- in one go.
  obtain ⟨poly, hpoly_eq, hpoly_deg_le⟩ :=
    entire_no_zeros_is_exp_polynomial Q (order Q) hQ_finite rfl hQ_ne
  -- `natDegree poly ≤ lam` and `lam < ⌊lam⌋ + 1`, so `natDegree poly ≤ ⌊lam⌋`.
  have hpoly_deg : poly.natDegree ≤ Nat.floor lam := by
    have h1 : (poly.natDegree : ℝ) ≤ order Q := hpoly_deg_le
    have h2 : order Q ≤ lam := hQ_order_le
    have h3 : (poly.natDegree : ℝ) ≤ lam := le_trans h1 h2
    exact Nat.le_floor h3
  refine ⟨poly, hpoly_deg, ?_⟩
  intro z
  -- Substitute: `exp(poly.eval z) = Q z`, use `hfact`.
  have hexp : Complex.exp (poly.eval z) = Q z := (hpoly_eq z).symm
  calc f z
      = canonicalProductZeroSetMultiplicityRank Z (Nat.floor lam) z * Q z :=
        hfact z
    _ = canonicalProductZeroSetMultiplicityRank Z (Nat.floor lam) z *
          Complex.exp (poly.eval z) := by
        rw [hexp]
    _ = Complex.exp (poly.eval z) *
          canonicalProductZeroSetMultiplicityRank Z (Nat.floor lam) z := by
        ring

end General
end Hadamard
