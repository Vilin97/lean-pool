/-
Copyright (c) 2026 Makoto Yamashita. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Makoto Yamashita
-/

import LeanPool.HSDInteriorPointLP.FixedYTMTheory

/-!
# Generated predictor-corrector algorithm and final convergence theorem

This is the main file to edit when the algorithmic proof changes.  The iterate
sequence is generated recursively from the initial point, so the dependency on the
fixed YTM theory is explicit and there is no hidden import of an old numbered file.

Lean-reading hints for beginners:
* `induction k with | zero => ... | succ k ih => ...` proves a statement for all
  natural numbers by proving the base case and the successor case.
* `calc ...` is a readable chain of equalities/inequalities.
* `omega` solves arithmetic goals over natural numbers and integers.
-/
noncomputable section

open scoped BigOperators

namespace HSDInteriorPointLP

/-!
## Lean comments for readers who know interior-point methods

This file is the final iteration-count layer.  The mathematical objects are the
predictor point, the corrector point, and the contraction estimate for the
homogenized gap.  A few Lean proof commands occur repeatedly.

* `intro k` introduces the iteration index in a theorem whose conclusion starts
  with `∀ k, ...`.
* `induction k with ...` proves a statement for all natural numbers by showing
  the base case `0` and then the step from `k` to `k+1`.
* `have h := ...` records an intermediate estimate, such as one-step contraction.
* `rw [lemma]` rewrites the current goal using an equality.
* `simpa [name₁, name₂] using h` unfolds the listed definitions, simplifies both
  sides, and then applies the already-proved fact `h`.
* `simp` is used only in very small base cases, such as `c^0 = 1`.
* `ring` closes purely algebraic real-number identities.
* `linarith` and `nlinarith` are used in imported files for linear and nonlinear
  real inequalities; here most inequalities are chained explicitly with `calc`.
-/

/-- A generated predictor-corrector algorithm: the iterate sequence is no longer a
field.  It is obtained recursively from the initial point by applying the canonical
Newton predictor step and the canonical Newton corrector step. -/
structure HSDGeneratedAlgorithm (n : Nat) where
  /-- Number of equality constraints in the LP data. -/
  m : Nat
  /-- Linear-programming data. -/
  P : LPData m n
  /-- Standard assumptions on the LP data. -/
  std : LPStandardAssumptions P
  /-- Initial HSD state. -/
  w0 : HSState n
  /-- Initial tight-neighborhood certificate. -/
  initial_neigh : HSDNeighborhood ytmBetaTight w0

namespace HSDGeneratedAlgorithm

/-- Canonical fixed predictor step from a tight-neighborhood point. -/
noncomputable def predictorStep {n : Nat} (alg : HSDGeneratedAlgorithm n)
    (w : HSState n) (h : HSDNeighborhood ytmBetaTight w) : HSState n :=
  addStep w (HSDNewtonDirection alg.P alg.std w h.1 0) (ytmPredictorAlpha n)

/-- Canonical full corrector step from a wide-neighborhood point. -/
noncomputable def correctorStep {n : Nat} (alg : HSDGeneratedAlgorithm n)
    (w : HSState n) (h : HSDNeighborhood ytmBetaWide w) : HSState n :=
  addStep w (HSDNewtonDirection alg.P alg.std w h.1 1) 1

/-- The generated predictor step stays in the wide neighborhood. -/
theorem predictorStep_wide {n : Nat} (alg : HSDGeneratedAlgorithm n)
    (w : HSState n) (h : HSDNeighborhood ytmBetaTight w) :
    HSDNeighborhood ytmBetaWide (alg.predictorStep w h) := by
  have hdir : HSDStepDirection w (HSDNewtonDirection alg.P alg.std w h.1 0) 0 :=
    HSDNewtonDirection_step alg.P alg.std w h.1 0
  have hg := predictor_step_guarantee_fixed_alpha
    (w := w) (d := HSDNewtonDirection alg.P alg.std w h.1 0) h hdir
  -- `hg.neighborhood_next` is stated for `addStep ...`; `simpa` unfolds
  -- `predictorStep` so that its type matches the generated step.
  simpa [predictorStep] using hg.neighborhood_next

/-- The generated corrector step returns to the tight neighborhood. -/
theorem correctorStep_tight {n : Nat} (alg : HSDGeneratedAlgorithm n)
    (w : HSState n) (h : HSDNeighborhood ytmBetaWide w) :
    HSDNeighborhood ytmBetaTight (alg.correctorStep w h) := by
  have hdir : HSDStepDirection w (HSDNewtonDirection alg.P alg.std w h.1 1) 1 :=
    HSDNewtonDirection_step alg.P alg.std w h.1 1
  have hg := corrector_step_guarantee_of_wide
    (w := w) (d := HSDNewtonDirection alg.P alg.std w h.1 1) h hdir
  simpa [correctorStep] using hg.neighborhood_next

/-- Even iterates, carrying the proof that they are in the tight neighborhood. -/
noncomputable def evenState {n : Nat} (alg : HSDGeneratedAlgorithm n) :
    Nat → {w : HSState n // HSDNeighborhood ytmBetaTight w}
  | 0 => ⟨alg.w0, alg.initial_neigh⟩
  | k + 1 =>
      let e := evenState alg k
      let o := alg.predictorStep e.1 e.2
      let ho := alg.predictorStep_wide e.1 e.2
      ⟨alg.correctorStep o ho, alg.correctorStep_tight o ho⟩

/-- The even iterate at predictor-corrector pair `k`. -/
noncomputable def even {n : Nat} (alg : HSDGeneratedAlgorithm n) (k : Nat) :
    HSState n :=
  (alg.evenState k).1

/-- Tight-neighborhood proof for generated even iterates. -/
theorem even_tight {n : Nat} (alg : HSDGeneratedAlgorithm n) (k : Nat) :
    HSDNeighborhood ytmBetaTight (alg.even k) :=
  (alg.evenState k).2

/-- The odd iterate obtained after the predictor step from `even k`. -/
noncomputable def odd {n : Nat} (alg : HSDGeneratedAlgorithm n) (k : Nat) :
    HSState n :=
  alg.predictorStep (alg.even k) (alg.even_tight k)

/-- Wide-neighborhood proof for generated odd iterates. -/
theorem odd_wide {n : Nat} (alg : HSDGeneratedAlgorithm n) (k : Nat) :
    HSDNeighborhood ytmBetaWide (alg.odd k) := by
  unfold odd
  exact alg.predictorStep_wide (alg.even k) (alg.even_tight k)

/-- Predictor gap decrease for generated odd iterates. -/
theorem predictor_gap_decrease {n : Nat}
    (alg : HSDGeneratedAlgorithm n) (k : Nat) :
    gap (alg.odd k) ≤ ytmContraction n * gap (alg.even k) := by
  have hdir : HSDStepDirection
      (alg.even k)
      (HSDNewtonDirection alg.P alg.std (alg.even k) (alg.even_tight k).1 0) 0 :=
    HSDNewtonDirection_step alg.P alg.std (alg.even k) (alg.even_tight k).1 0
  have hg := predictor_step_guarantee_fixed_alpha
    (w := alg.even k)
    (d := HSDNewtonDirection alg.P alg.std (alg.even k) (alg.even_tight k).1 0)
    (alg.even_tight k) hdir
  simpa [odd, predictorStep, ytmContraction] using hg.gap_decrease

/-- Corrector gap preservation for generated even iterates. -/
theorem corrector_gap_preserve {n : Nat}
    (alg : HSDGeneratedAlgorithm n) (k : Nat) :
    gap (alg.even (k + 1)) = gap (alg.odd k) := by
  have hdir : HSDStepDirection
      (alg.odd k)
      (HSDNewtonDirection alg.P alg.std (alg.odd k) (alg.odd_wide k).1 1) 1 :=
    HSDNewtonDirection_step alg.P alg.std (alg.odd k) (alg.odd_wide k).1 1
  have hg := corrector_step_guarantee_of_wide
    (w := alg.odd k)
    (d := HSDNewtonDirection alg.P alg.std (alg.odd k) (alg.odd_wide k).1 1)
    (alg.odd_wide k) hdir
  simpa [even, evenState, odd, correctorStep] using hg.gap_preserve

/-- One generated predictor-corrector pair contracts the gap. -/
theorem two_step_gap_contracts {n : Nat}
    (alg : HSDGeneratedAlgorithm n) (k : Nat) :
    gap (alg.even (k + 1)) ≤ ytmContraction n * gap (alg.even k) := by
  rw [alg.corrector_gap_preserve k]
  exact alg.predictor_gap_decrease k

/-- Initial gap positivity is derived from the initial neighborhood. -/
theorem initial_gap_pos {n : Nat} (alg : HSDGeneratedAlgorithm n) :
    0 < gap (alg.even 0) := by
  -- `even 0` is definitionally the initial point `w0`.
  -- `simpa` unfolds `even` and `evenState` and applies positivity of interior points.
  simpa [even, evenState] using gap_pos_of_interior alg.w0 alg.initial_neigh.1

/-- Generated even iterates satisfy the exponential power bound. -/
theorem even_gap_contracts_pow {n : Nat}
    (alg : HSDGeneratedAlgorithm n) :
    ∀ k : Nat,
      gap (alg.even k) ≤ (ytmContraction n) ^ k * gap (alg.even 0) := by
  -- Introduce the pair index `k`; the goal is now the power bound for this `k`.
  intro k
  -- Induction is over the number of completed predictor-corrector pairs.
  induction k with
  | zero =>
      -- Base case: `(ytmContraction n)^0 = 1`, so the bound is immediate.
      simp
  | succ k ih =>
      have hstep := alg.two_step_gap_contracts k
      have hnonneg := ytmContraction_nonneg n
      calc
        gap (alg.even (k + 1))
            ≤ ytmContraction n * gap (alg.even k) := hstep
        _ ≤ ytmContraction n *
              ((ytmContraction n) ^ k * gap (alg.even 0)) := by
            exact mul_le_mul_of_nonneg_left ih hnonneg
        _ = (ytmContraction n) ^ (k + 1) * gap (alg.even 0) := by
            -- This is only the identity `c * (c^k * g) = c^(k+1) * g`.
            ring

/-- Generated odd iterates satisfy the corresponding one-predictor-shifted bound. -/
theorem odd_gap_contracts_pow {n : Nat}
    (alg : HSDGeneratedAlgorithm n) (k : Nat) :
    gap (alg.odd k) ≤
      (ytmContraction n) ^ (k + 1) * gap (alg.even 0) := by
  have hpred := alg.predictor_gap_decrease k
  have heven := alg.even_gap_contracts_pow k
  have hnonneg := ytmContraction_nonneg n
  calc
    gap (alg.odd k) ≤ ytmContraction n * gap (alg.even k) := hpred
    _ ≤ ytmContraction n *
          ((ytmContraction n) ^ k * gap (alg.even 0)) := by
        exact mul_le_mul_of_nonneg_left heven hnonneg
    _ = (ytmContraction n) ^ (k + 1) * gap (alg.even 0) := by
        ring

/-- Logarithmic pair bound for the generated algorithm, using
`L = log(gap0 / ε)` as in the paper-style iteration estimate. -/
def logL {n : Nat} (alg : HSDGeneratedAlgorithm n) (ε : ℝ) : ℝ :=
  Real.log (gap (alg.even 0) / ε)

/-- Pair-count ceiling bound computed from the generated algorithm's initial gap. -/
def logPairBound {n : Nat} (alg : HSDGeneratedAlgorithm n) (ε : ℝ) : Nat :=
  ytmLogPairBoundL n (alg.logL ε)

/-- Ordinary iteration-count bound, twice the pair-count bound. -/
def logIterationBound {n : Nat} (alg : HSDGeneratedAlgorithm n) (ε : ℝ) : Nat :=
  2 * alg.logPairBound ε

/-- The generated pair bound implies the required power condition. -/
theorem power_condition_of_logPairBound {n : Nat}
    (alg : HSDGeneratedAlgorithm n) (ε : ℝ) (hε : 0 < ε) :
    (ytmContraction n) ^ alg.logPairBound ε * gap (alg.even 0) ≤ ε := by
  have hgap0 : 0 < gap (alg.even 0) := alg.initial_gap_pos
  have hpow := YTM_contraction_power_le_exp (n := n) (alg.logPairBound ε)
  have hK :
      (Real.sqrt (hdim n) / ytmStepConstant) *
          Real.log (gap (alg.even 0) / ε) ≤ (alg.logPairBound ε : ℝ) := by
    -- `logPairBound` is a ceiling.  After unfolding, `Nat.le_ceil` gives
    -- `real expression ≤ Nat.ceil real expression`.
    unfold logPairBound logL ytmLogPairBoundL
    exact Nat.le_ceil _
  have hexp := ytm_exp_mul_gap_le_of_log_bound
    (n := n) (alg.logPairBound ε) hgap0 hε hK
  calc
    (ytmContraction n) ^ alg.logPairBound ε * gap (alg.even 0)
        ≤ Real.exp
            (-(ytmStepConstant / Real.sqrt (hdim n) *
              (alg.logPairBound ε : ℝ))) * gap (alg.even 0) := by
          exact mul_le_mul_of_nonneg_right hpow (le_of_lt hgap0)
    _ ≤ ε := hexp


/-- Gap stopping at the generated logarithmic pair bound. -/
theorem gap_stop_even_at_logPairBound {n : Nat}
    (alg : HSDGeneratedAlgorithm n) (ε : ℝ) (hε : 0 < ε) :
    YTMGapStop ε (alg.even (alg.logPairBound ε)) := by
  exact YTMGapStop_of_gap_le
    (le_trans (alg.even_gap_contracts_pow (alg.logPairBound ε))
      (alg.power_condition_of_logPairBound ε hε))

/-- The predictor point at the same pair index also satisfies the gap test. -/
theorem gap_stop_odd_at_logPairBound {n : Nat}
    (alg : HSDGeneratedAlgorithm n) (ε : ℝ) (hε : 0 < ε) :
    YTMGapStop ε (alg.odd (alg.logPairBound ε)) := by
  have heven : gap (alg.even (alg.logPairBound ε)) ≤ ε :=
    (alg.gap_stop_even_at_logPairBound ε hε)
  have hpred := alg.predictor_gap_decrease (alg.logPairBound ε)
  have hc_nonneg := ytmContraction_nonneg n
  have hc_le_one := ytmContraction_le_one n
  calc
    gap (alg.odd (alg.logPairBound ε))
        ≤ ytmContraction n * gap (alg.even (alg.logPairBound ε)) := hpred
    _ ≤ ytmContraction n * ε := by
        exact mul_le_mul_of_nonneg_left heven hc_nonneg
    _ ≤ 1 * ε := by
        exact mul_le_mul_of_nonneg_right hc_le_one (le_of_lt hε)
    _ = ε := by ring

/-- Generated even iterate satisfies the `μ ≤ ε` test at the log bound. -/
theorem mu_stop_even_at_logPairBound {n : Nat}
    (alg : HSDGeneratedAlgorithm n) (ε : ℝ) (hε : 0 < ε) :
    YTMMuStop ε (alg.even (alg.logPairBound (hdim n * ε))) := by
  have hscaled : 0 < hdim n * ε := mul_pos (hdim_pos n) hε
  have hgap : YTMGapStop (hdim n * ε)
      (alg.even (alg.logPairBound (hdim n * ε))) :=
    alg.gap_stop_even_at_logPairBound (hdim n * ε) hscaled
  exact YTMMuStop_of_gap_le_hdim_mul hgap

/-- Generated odd iterate satisfies the `μ ≤ ε` test at the log bound. -/
theorem mu_stop_odd_at_logPairBound {n : Nat}
    (alg : HSDGeneratedAlgorithm n) (ε : ℝ) (hε : 0 < ε) :
    YTMMuStop ε (alg.odd (alg.logPairBound (hdim n * ε))) := by
  have hscaled : 0 < hdim n * ε := mul_pos (hdim_pos n) hε
  have hgap : YTMGapStop (hdim n * ε)
      (alg.odd (alg.logPairBound (hdim n * ε))) :=
    alg.gap_stop_odd_at_logPairBound (hdim n * ε) hscaled
  exact YTMMuStop_of_gap_le_hdim_mul hgap

/-- Abstract paper-style stopping condition: the residual predicates are parameters,
because the current HLP skeleton has not yet introduced concrete primal and dual
residual maps. -/
structure PaperStyleStop {n : Nat}
    (PrimalResidualStop DualResidualStop : HSState n → Prop)
    (ε : ℝ) (w : HSState n) : Prop where
  mu_stop : YTMMuStop ε w
  primal_stop : PrimalResidualStop w
  dual_stop : DualResidualStop w

/-- Once residual estimates are available, this packages them with `μ ≤ ε`. -/
theorem PaperStyleStop.of_mu_and_residuals {n : Nat}
    {PrimalResidualStop DualResidualStop : HSState n → Prop}
    {ε : ℝ} {w : HSState n}
    (hmu : YTMMuStop ε w)
    (hp : PrimalResidualStop w) (hd : DualResidualStop w) :
    PaperStyleStop PrimalResidualStop DualResidualStop ε w :=
  ⟨hmu, hp, hd⟩

end HSDGeneratedAlgorithm

end HSDInteriorPointLP
