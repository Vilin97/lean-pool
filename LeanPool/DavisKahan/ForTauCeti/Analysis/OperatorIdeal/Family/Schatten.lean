/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.ScalarTransport
public import LeanPool.DavisKahan.ForTauCeti.Analysis.Normed.FiniteLpGauge
public import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.Family.KyFan
public import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.Family.TraceClass
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.HilbertSchmidt.Energy
public import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.Family.HilbertSchmidt
public import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.EnergyComparison

/-!
# Schatten norms from approximation numbers

The extended Schatten norm is the power sum of the approximation numbers. It is
finite exactly on the corresponding Schatten class. This module proves its
analytic laws, lower semicontinuity, and its identifications at exponents one
and two. The sole family construction, including completeness, is obtained from
`SymmetricGauge` in `Family.SymmetricGauge`.
-/

open scoped ENNReal NNReal InnerProductSpace

public section

namespace ContinuousLinearMap

universe u v w

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} {F : Type w}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

section Truncation

/-- The prefix sums of a truncated sequence are the sequence's own partial sums, capped at the
truncation length.  This is the only bridge the file needs between
`TauCeti.FiniteVector.prefixSum` on `Fin k` and `Finset.range`. -/
theorem _root_.TauCeti.FiniteVector.prefixSum_comp_val {k : ℕ} (f : ℕ → ℝ) (j : ℕ) :
    TauCeti.FiniteVector.prefixSum j (fun i : Fin k => f i) =
      ∑ n ∈ Finset.range (min j k), f n := by
  classical
  rw [TauCeti.FiniteVector.prefixSum, Finset.sum_filter, Fin.sum_univ_eq_sum_range
    (fun m => if m < j then f m else 0) k, ← Finset.sum_filter]
  congr 1
  ext m
  simp only [Finset.mem_filter, Finset.mem_range, Nat.lt_min]
  exact and_comm

end Truncation

section Finite


/-- **The Schatten triangle inequality on a truncation.**  Every partial `ℓᵖ` sum of the
approximation numbers of `S + T` is bounded by the *full* partial sums of `S` and of `T` at
the same length.

The proof is the whole point of the module: the truncated sequences are weakly majorized —
antitone and nonnegative because approximation numbers are, and prefix-comparable because
that comparison *is* `kyFanGauge_add_le` — so
`TauCeti.FiniteVector.lpGauge_mono_weaklyMajorized`
applies, and finite Minkowski splits the right-hand side. -/
theorem lpGauge_approximationNumber_add_le {p : ℝ} (hp : 1 ≤ p) (S T : E →L[𝕜] F) (k : ℕ) :
    TauCeti.FiniteVector.lpGauge p (fun i : Fin k => (S + T).approximationNumber i) ≤
      TauCeti.FiniteVector.lpGauge p (fun i : Fin k => S.approximationNumber i) +
        TauCeti.FiniteVector.lpGauge p (fun i : Fin k => T.approximationNumber i) := by
  classical
  have hmaj : TauCeti.FiniteVector.WeaklyMajorized
      (fun i : Fin k => (S + T).approximationNumber i)
      (fun i : Fin k => S.approximationNumber i + T.approximationNumber i) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact fun i j hij => (S + T).approximationNumber_antitone (by exact_mod_cast hij)
    · exact fun i j hij =>
        add_le_add (S.approximationNumber_antitone (by exact_mod_cast hij))
          (T.approximationNumber_antitone (by exact_mod_cast hij))
    · exact fun i => (S + T).approximationNumber_nonneg i
    · exact fun i =>
        add_nonneg (S.approximationNumber_nonneg i) (T.approximationNumber_nonneg i)
    · intro j
      rw [TauCeti.FiniteVector.prefixSum_comp_val (fun n => (S + T).approximationNumber n) j,
        show (fun i : Fin k => S.approximationNumber i + T.approximationNumber i)
          = (fun i : Fin k => (fun n => S.approximationNumber n + T.approximationNumber n) i)
          from rfl,
        TauCeti.FiniteVector.prefixSum_comp_val
          (fun n => S.approximationNumber n + T.approximationNumber n) j,
        Finset.sum_add_distrib]
      exact kyFanGauge_add_le S T (min j k)
  calc TauCeti.FiniteVector.lpGauge p (fun i : Fin k => (S + T).approximationNumber i)
      ≤ TauCeti.FiniteVector.lpGauge p
          (fun i : Fin k => S.approximationNumber i + T.approximationNumber i) :=
        TauCeti.FiniteVector.lpGauge_mono_weaklyMajorized hp hmaj
    _ ≤ _ := TauCeti.FiniteVector.lpGauge_add_le hp _ _

end Finite


section Gauge

/-- The **Schatten `p`-norm**, valued in `ℝ≥0∞` and therefore defined for every bounded
operator: it is `∞` exactly when `T` is not Schatten-`p`. -/
@[expose]
noncomputable def schattenENorm (p : ℝ) (T : E →L[𝕜] F) : ℝ≥0∞ :=
  (∑' n : ℕ, ENNReal.ofReal (T.approximationNumber n) ^ p) ^ p⁻¹

-- Reading the finite gauge in `ℝ≥0∞` is arithmetic; neither space needs to be complete.
omit [CompleteSpace E] [CompleteSpace F] in
/-- The truncated `ℓᵖ` gauge, read in `ℝ≥0∞`.  This is the bridge between the real finite
theory, where the majorization argument lives, and the `ℝ≥0∞` gauge, where the ideal laws
are stated unconditionally. -/
theorem ofReal_lpGauge_approximationNumber {p : ℝ} (hp0 : 0 < p) (T : E →L[𝕜] F) (k : ℕ) :
    ENNReal.ofReal
        (TauCeti.FiniteVector.lpGauge p (fun i : Fin k => T.approximationNumber i)) =
      (∑ n ∈ Finset.range k, ENNReal.ofReal (T.approximationNumber n) ^ p) ^ p⁻¹ := by
  have hsum : ∀ i : Fin k, |T.approximationNumber i| ^ p = T.approximationNumber i ^ p :=
    fun i => by rw [abs_of_nonneg (T.approximationNumber_nonneg i)]
  rw [TauCeti.FiniteVector.lpGauge, one_div]
  rw [← ENNReal.ofReal_rpow_of_nonneg
    (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (abs_nonneg _) _) (by positivity)]
  congr 1
  rw [ENNReal.ofReal_sum_of_nonneg fun i _ => Real.rpow_nonneg (abs_nonneg _) _,
    Fin.sum_univ_eq_sum_range
      (fun m => ENNReal.ofReal (|T.approximationNumber m| ^ p)) k]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [abs_of_nonneg (T.approximationNumber_nonneg m),
    ENNReal.ofReal_rpow_of_nonneg (T.approximationNumber_nonneg m) hp0.le]

-- A partial sum is at most its `tsum`; again no completeness is used.
omit [CompleteSpace E] [CompleteSpace F] in
/-- Every truncated `ℓᵖ` gauge is dominated by the whole Schatten norm. -/
theorem ofReal_lpGauge_le_schattenENorm {p : ℝ} (hp0 : 0 < p) (T : E →L[𝕜] F) (k : ℕ) :
    ENNReal.ofReal
        (TauCeti.FiniteVector.lpGauge p (fun i : Fin k => T.approximationNumber i)) ≤
      T.schattenENorm p := by
  rw [ofReal_lpGauge_approximationNumber hp0 T k, schattenENorm]
  exact ENNReal.rpow_le_rpow (ENNReal.sum_le_tsum _) (by positivity)

section Triangle


/-- **The Schatten triangle inequality.**

Each truncation is handled by `lpGauge_approximationNumber_add_le`, whose right-hand side is
already bounded by the two whole gauges; the `tsum` on the left is the supremum of those
truncations, so the bound passes to the limit with nothing further to prove. -/
theorem schattenENorm_add_le {p : ℝ} (hp : 1 ≤ p) (S T : E →L[𝕜] F) :
    (S + T).schattenENorm p ≤ S.schattenENorm p + T.schattenENorm p := by
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp
  set R := S.schattenENorm p + T.schattenENorm p with hR
  have hstep : ∀ k : ℕ,
      (∑ n ∈ Finset.range k, ENNReal.ofReal ((S + T).approximationNumber n) ^ p) ^ p⁻¹ ≤ R := by
    intro k
    rw [← ofReal_lpGauge_approximationNumber hp0 (S + T) k]
    calc ENNReal.ofReal
          (TauCeti.FiniteVector.lpGauge p (fun i : Fin k => (S + T).approximationNumber i))
        ≤ ENNReal.ofReal
            (TauCeti.FiniteVector.lpGauge p (fun i : Fin k => S.approximationNumber i) +
              TauCeti.FiniteVector.lpGauge p (fun i : Fin k => T.approximationNumber i)) :=
          ENNReal.ofReal_le_ofReal (lpGauge_approximationNumber_add_le hp S T k)
      _ = _ := ENNReal.ofReal_add (TauCeti.FiniteVector.lpGauge_nonneg _ _)
          (TauCeti.FiniteVector.lpGauge_nonneg _ _)
      _ ≤ R := add_le_add (ofReal_lpGauge_le_schattenENorm hp0 S k)
          (ofReal_lpGauge_le_schattenENorm hp0 T k)
  -- The partial sums are bounded by `R ^ p`, and `∑'` is their supremum.
  have hpow : ∀ k : ℕ,
      ∑ n ∈ Finset.range k, ENNReal.ofReal ((S + T).approximationNumber n) ^ p ≤ R ^ p := by
    intro k
    have h := ENNReal.rpow_le_rpow (hstep k) hp0.le
    rwa [← ENNReal.rpow_mul, inv_mul_cancel₀ hp0.ne', ENNReal.rpow_one] at h
  have htsum : ∑' n : ℕ, ENNReal.ofReal ((S + T).approximationNumber n) ^ p ≤ R ^ p :=
    ENNReal.tsum_eq_iSup_nat.trans_le (iSup_le hpow)
  have := ENNReal.rpow_le_rpow htsum (by positivity : (0 : ℝ) ≤ p⁻¹)
  rwa [← ENNReal.rpow_mul, mul_inv_cancel₀ hp0.ne', ENNReal.rpow_one] at this

end Triangle

-- Scaling scales every approximation number, so it scales the whole sum; completeness is
-- not used.
omit [CompleteSpace E] [CompleteSpace F] in
/-- **Absolute homogeneity.** -/
theorem schattenENorm_smul {p : ℝ} (hp0 : 0 < p) (c : 𝕜) (T : E →L[𝕜] F) :
    (c • T).schattenENorm p = ‖c‖ₑ * T.schattenENorm p := by
  have hterm : ∀ n : ℕ, ENNReal.ofReal ((c • T).approximationNumber n) ^ p =
      ‖c‖ₑ ^ p * ENNReal.ofReal (T.approximationNumber n) ^ p := by
    intro n
    rw [approximationNumber_smul, ENNReal.ofReal_mul (norm_nonneg c), ofReal_norm,
      ENNReal.mul_rpow_of_nonneg _ _ hp0.le]
  rw [schattenENorm, schattenENorm]
  simp only [hterm]
  rw [ENNReal.tsum_mul_left, ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ p⁻¹),
    ← ENNReal.rpow_mul, mul_inv_cancel₀ hp0.ne', ENNReal.rpow_one]

-- The zeroth term alone gives the bound, so no completeness is needed.
omit [CompleteSpace E] [CompleteSpace F] in
/-- **The Schatten norm dominates the operator norm**, being its zeroth term. -/
theorem enorm_le_schattenENorm {p : ℝ} (hp0 : 0 < p) (T : E →L[𝕜] F) :
    ‖T‖ₑ ≤ T.schattenENorm p := by
  have hz : ‖T‖ₑ ^ p ≤ ∑' n : ℕ, ENNReal.ofReal (T.approximationNumber n) ^ p := by
    refine le_trans (le_of_eq ?_) (ENNReal.le_tsum 0)
    rw [← ofReal_norm, ← T.approximationNumber_index_zero]
  have := ENNReal.rpow_le_rpow hz (by positivity : (0 : ℝ) ≤ p⁻¹)
  rwa [← ENNReal.rpow_mul, mul_inv_cancel₀ hp0.ne', ENNReal.rpow_one] at this

/-- **Adjoint invariance**, immediate from invariance of the approximation numbers.  This is
what makes the Schatten family *symmetric*. -/
theorem schattenENorm_adjoint (p : ℝ) (T : E →L[𝕜] F) :
    T.adjoint.schattenENorm p = T.schattenENorm p := by
  simp only [schattenENorm, approximationNumber_adjoint]

omit [CompleteSpace E] [CompleteSpace F] in
/-- **The two-sided ideal bound.** -/
theorem schattenENorm_comp_le {p : ℝ} (hp0 : 0 < p) {G H : Type*}
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] 
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] 
    (L : F →L[𝕜] G) (T : E →L[𝕜] F) (R : H →L[𝕜] E) :
    (L ∘L T ∘L R).schattenENorm p ≤ ‖L‖ₑ * T.schattenENorm p * ‖R‖ₑ := by
  have hterm : ∀ n : ℕ, ENNReal.ofReal ((L ∘L T ∘L R).approximationNumber n) ^ p ≤
      (‖L‖ₑ * ‖R‖ₑ) ^ p * ENNReal.ofReal (T.approximationNumber n) ^ p := by
    intro n
    have h := ENNReal.ofReal_le_ofReal (approximationNumber_comp_comp_le L T R n)
    refine le_trans (ENNReal.rpow_le_rpow h hp0.le) (le_of_eq ?_)
    -- The `rw` chain this replaced repeated `ofReal_norm` twice and
    -- `mul_rpow_of_nonneg` three times, once per occurrence.
    simp only [ENNReal.ofReal_mul (mul_nonneg (norm_nonneg L) (T.approximationNumber_nonneg n)),
      ENNReal.ofReal_mul (norm_nonneg L), ofReal_norm,
      ENNReal.mul_rpow_of_nonneg _ _ hp0.le]
    ring
  calc (L ∘L T ∘L R).schattenENorm p
      ≤ ((‖L‖ₑ * ‖R‖ₑ) ^ p * ∑' n : ℕ, ENNReal.ofReal (T.approximationNumber n) ^ p) ^ p⁻¹ := by
        refine ENNReal.rpow_le_rpow ?_ (by positivity)
        rw [← ENNReal.tsum_mul_left]
        exact ENNReal.tsum_le_tsum hterm
    _ = ‖L‖ₑ * T.schattenENorm p * ‖R‖ₑ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ p⁻¹),
          ← ENNReal.rpow_mul, mul_inv_cancel₀ hp0.ne', ENNReal.rpow_one, schattenENorm]
        ring

-- Lower semicontinuity is about the approximation-number sequence; no completeness is used.
omit [CompleteSpace E] [CompleteSpace F] in
/-- **The Schatten norm is lower semicontinuous along operator-norm convergence**, stated at
the `p`-th power.

Same shape as `nuclearENorm_le_liminf`: the summands are continuous images of the
approximation numbers and `ENNReal.tsum_le_liminf_tsum` handles the sum.

**Stated at the `p`-th power deliberately**, which is also why the Hilbert--Schmidt twin is
stated at the square.  Pulling `^ p⁻¹` out of a `liminf` needs that map to commute with
`liminf`, which is true but is a separate lemma about `ℝ≥0∞`; at the `p`-th power the sum is
literally the `liminf`'s subject and nothing has to commute.  Consumers undo it with
`ENNReal.rpow_le_rpow_iff`. -/
theorem schattenENorm_rpow_le_liminf {p : ℝ} (hp0 : 0 < p) {u : Filter ℕ} [u.NeBot]
    {T : ℕ → E →L[𝕜] F} {L : E →L[𝕜] F}
    (hop : Filter.Tendsto (fun n => ‖T n - L‖) u (nhds 0)) :
    L.schattenENorm p ^ p ≤ Filter.liminf (fun n => (T n).schattenENorm p ^ p) u := by
  have hpow : ∀ S : E →L[𝕜] F, S.schattenENorm p ^ p
      = ∑' i : ℕ, ENNReal.ofReal (S.approximationNumber i) ^ p := by
    intro S
    rw [schattenENorm, ← ENNReal.rpow_mul, inv_mul_cancel₀ hp0.ne', ENNReal.rpow_one]
  simp only [hpow]
  refine ENNReal.tsum_le_liminf_tsum fun i => ?_
  refine (ENNReal.continuous_rpow_const.tendsto _).comp ?_
  refine (ENNReal.continuous_ofReal.tendsto _).comp ?_
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun _ => dist_nonneg) (fun n => ?_) hop
  rw [Real.dist_eq]
  exact abs_approximationNumber_sub_approximationNumber_le (T n) L i

omit [CompleteSpace E] [CompleteSpace F] in
/-- The Schatten norm is unchanged by negation, term by term. -/
@[simp] theorem schattenENorm_neg (p : ℝ) (T : E →L[𝕜] F) :
    (-T).schattenENorm p = T.schattenENorm p := by
  simp only [schattenENorm, approximationNumber_neg]

omit [CompleteSpace E] [CompleteSpace F] in
/-- `T` is **Schatten-`p`** when its Schatten norm is finite.

`@[expose]`: membership in the Schatten family's carrier is this predicate by definition, and
the carrier lemmas downstream are stated with `rfl`. -/
@[expose]
def IsSchattenClass (p : ℝ) (T : E →L[𝕜] F) : Prop := T.schattenENorm p ≠ ∞

section AgreementAtOne

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} {F : Type w}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

omit [CompleteSpace E] [CompleteSpace F] in
/-- **At `p = 1` the Schatten norm is the nuclear norm.**  Both are `tsum`s of the same
sequence and the exponents are `1` and `1⁻¹`, so this is arithmetic in `ℝ≥0∞` rather than a
theorem about operators.

The exponent-two counterpart uses the basis-independent energy identity proved
in `ApproximationNumber.EnergyComparison`. -/
theorem schattenENorm_one (T : E →L[𝕜] F) : T.schattenENorm 1 = T.nuclearENorm := by
  simp [schattenENorm, nuclearENorm]

end AgreementAtOne

section AgreementAtTwo

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} {F : Type w}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- **The Schatten-2 norm is the Hilbert--Schmidt norm.**  Both are the square root of the
same `ℝ≥0∞` quantity, by the identity above. -/
theorem schattenENorm_two (T : E →L[𝕜] F) :
    T.schattenENorm 2 = T.hilbertSchmidtENorm := by
  classical
  obtain ⟨w, b, -⟩ := exists_hilbertBasis 𝕜 E
  rw [schattenENorm, T.hilbertSchmidtENorm_eq b,
    ← tsum_approximationNumber_sq_eq_hilbertSchmidtEnergy T b]
  norm_num


end AgreementAtTwo

end Gauge

end ContinuousLinearMap
