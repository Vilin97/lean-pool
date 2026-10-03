/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.Analytic.LogExpAdditivity

/-! # Log Exp Composition -/

@[expose] public section
open Filter
open Polynomial
open scoped Topology
open scoped PowerSeries.WithPiTopology

/-!
# Exact logarithm--exponential compositions

This file evaluates the two formal composition identities used in
the deep exponential–logarithm equivalence, on the sharp ramified
convergence ball.  The source lemmas below justify the Cauchy products and
the unconditional regrouping involved in power-series substitution.
-/

noncomputable
section

attribute [local instance] Classical.propDecidable

universe u

namespace LocalFieldTheory.DiscreteValuationField
namespace MultiplicativeIntegerValuation

variable {K : Type u} [Field K]

/-- A convergent one-variable power series may be raised to a natural power
by taking its nonarchimedean Cauchy product. -/
theorem hasSum_powerSeries_pow_coeff_mul_pow
    [UniformSpace K] [IsUniformAddGroup K] [T3Space K]
    [NonarchimedeanRing K]
    (g : PowerSeries K) (x y : K)
    (hgy : HasSum (fun d : ℕ => PowerSeries.coeff d g * x ^ d) y)
    (q : ℕ) :
    HasSum (fun d : ℕ => PowerSeries.coeff d (g ^ q) * x ^ d) (y ^ q) := by
  induction q with
  | zero =>
      have hsingle :
          HasSum (fun d : ℕ => if d = 0 then (1 : K) else 0) 1 := by
        apply hasSum_single 0
        intro d hd
        simp [hd]
      have hsingle' :
          HasSum (fun d : ℕ => PowerSeries.coeff d (1 : PowerSeries K) * x ^ d) 1 :=
        hsingle.congr_fun fun d => by
          by_cases hd : d = 0
          · subst d
            simp
          · simp [PowerSeries.coeff_one, hd]
      simpa only [pow_zero] using hsingle'
  | succ q ih =>
      have hprod := ih.mul_of_nonarchimedean hgy
      have hsigma :
          HasSum
            (fun nd : Sigma fun d : ℕ => ↑(Finset.antidiagonal d) =>
              (PowerSeries.coeff nd.2.1.1 (g ^ q) * x ^ nd.2.1.1) *
                (PowerSeries.coeff nd.2.1.2 g * x ^ nd.2.1.2))
            (y ^ q * y) := by
        simpa [Function.comp_def] using
          (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.hasSum_iff).2 hprod
      have hsumCauchy :
          HasSum
            (fun d : ℕ =>
              ∑ ij : ↑(Finset.antidiagonal d),
                (PowerSeries.coeff ij.1.1 (g ^ q) * x ^ ij.1.1) *
                  (PowerSeries.coeff ij.1.2 g * x ^ ij.1.2))
            (y ^ q * y) :=
        hsigma.sigma fun d => hasSum_fintype _
      rw [show g ^ (q + 1) = g ^ q * g by rw [pow_succ],
        show y ^ (q + 1) = y ^ q * y by rw [pow_succ]]
      refine hsumCauchy.congr_fun ?_
      intro d
      rw [PowerSeries.coeff_mul, Finset.sum_mul]
      rw [← Finset.sum_attach, Finset.attach_eq_univ]
      apply Finset.sum_congr rfl
      intro ij _
      have hijsum : ij.1.1 + ij.1.2 = d :=
        Finset.mem_antidiagonal.mp ij.2
      have hpow : x ^ d = x ^ ij.1.1 * x ^ ij.1.2 := by
        calc
          x ^ d = x ^ (ij.1.1 + ij.1.2) :=
            congrArg (fun n : ℕ => x ^ n) hijsum.symm
          _ = x ^ ij.1.1 * x ^ ij.1.2 := pow_add _ _ _
      rw [hpow]
      ring

/-- If every evaluated coefficient of a series is at most `r`, then every
evaluated coefficient of its `q`-th power is at most `r^q`. -/
theorem valuation_powerSeries_pow_coeff_mul_pow_le
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    (g : PowerSeries K) (x : K) (r : WithZero (Multiplicative ℤ))
    (hcoeff : ∀ d : ℕ, v (PowerSeries.coeff d g * x ^ d) ≤ r)
    (q d : ℕ) :
    v (PowerSeries.coeff d (g ^ q) * x ^ d) ≤ r ^ q := by
  induction q generalizing d with
  | zero =>
      by_cases hd : d = 0
      · subst d
        simp
      · simp [PowerSeries.coeff_one, hd]
  | succ q ih =>
      rw [pow_succ, PowerSeries.coeff_mul, Finset.sum_mul]
      apply v.map_sum_le
      intro ij hij
      have hijsum : ij.1 + ij.2 = d := Finset.mem_antidiagonal.mp hij
      have heq :
          (PowerSeries.coeff ij.1 (g ^ q) * PowerSeries.coeff ij.2 g) * x ^ d =
            (PowerSeries.coeff ij.1 (g ^ q) * x ^ ij.1) *
              (PowerSeries.coeff ij.2 g * x ^ ij.2) := by
        rw [← hijsum, pow_add]
        ring
      rw [heq, v.map_mul, pow_succ]
      exact mul_le_mul (ih ij.1) (hcoeff ij.2) (by simp) (by simp)

/-- The valuation of a term in the expanded substitution is bounded by the
corresponding outer-series term. -/
theorem valuation_powerSeries_subst_sigmaTerm_le_outerTerm
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    (f g : PowerSeries K) (x : K)
    (hcoeff : ∀ d : ℕ,
      v (PowerSeries.coeff d g * x ^ d) ≤ v x)
    (q d : ℕ) :
    v (PowerSeries.coeff q f * PowerSeries.coeff d (g ^ q) * x ^ d) ≤
      v (PowerSeries.coeff q f * x ^ q) := by
  have hpow :=
    valuation_powerSeries_pow_coeff_mul_pow_le
      v g x (v x) hcoeff q d
  calc
    v (PowerSeries.coeff q f * PowerSeries.coeff d (g ^ q) * x ^ d) =
        v (PowerSeries.coeff q f) *
          v (PowerSeries.coeff d (g ^ q) * x ^ d) := by
      rw [mul_assoc, v.map_mul]
    _ ≤ v (PowerSeries.coeff q f) * (v x) ^ q :=
      by gcongr
    _ = v (PowerSeries.coeff q f * x ^ q) := by
      rw [v.map_mul, v.map_pow]

/-- The doubly indexed family expanding `f(g(X))` is unconditionally
summable.  Large outer degrees are controlled uniformly by the convergent
evaluation of `f` at `x`; the finitely many remaining outer degrees are
controlled by the convergent Cauchy powers of `g`. -/
theorem summable_powerSeries_subst_sigma_of_outer_summable
    [Valued K (WithZero (Multiplicative ℤ))] [CompleteSpace K]
    [NonarchimedeanRing K]
    (f g : PowerSeries K) (x y : K)
    (hgy : HasSum (fun d : ℕ => PowerSeries.coeff d g * x ^ d) y)
    (houter : Summable (fun q : ℕ => PowerSeries.coeff q f * x ^ q))
    (hcoeff : ∀ d : ℕ,
      Valued.v (PowerSeries.coeff d g * x ^ d) ≤ Valued.v x) :
    Summable
      (fun qd : Sigma fun _ : ℕ => ℕ =>
        PowerSeries.coeff qd.1 f *
          PowerSeries.coeff qd.2 (g ^ qd.1) * x ^ qd.2) := by
  let term : (Sigma fun _ : ℕ => ℕ) → K := fun qd =>
    PowerSeries.coeff qd.1 f *
      PowerSeries.coeff qd.2 (g ^ qd.1) * x ^ qd.2
  let outerTerm : ℕ → K := fun q => PowerSeries.coeff q f * x ^ q
  change Summable term
  rw [NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero]
  rw [tendsto_def]
  intro s hs
  have hrepr := Valued.mem_nhds_zero.mp hs
  let γ := Classical.choose hrepr
  have hγ := Classical.choose_spec hrepr
  have hball :
      {z : K |
        Valued.v z < MonoidWithZeroHom.ValueGroup₀.embedding γ.1} ∈ nhds (0 : K) := by
    apply Valued.mem_nhds_zero.mpr
    exact ⟨γ, by
      intro z hz
      change Valued.v.restrict z < γ.1 at hz
      rw [Valuation.restrict_lt_iff_lt_embedding] at hz
      exact hz⟩
  have houterZero : Tendsto outerTerm cofinite (nhds (0 : K)) := by
    simpa [outerTerm] using houter.tendsto_cofinite_zero
  have houterEventually :
      ∀ᶠ q : ℕ in cofinite,
        Valued.v (outerTerm q) <
          MonoidWithZeroHom.ValueGroup₀.embedding γ.1 :=
    houterZero.eventually hball
  let goodOuter : Set ℕ :=
    {q | Valued.v (outerTerm q) <
      MonoidWithZeroHom.ValueGroup₀.embedding γ.1}
  have hgoodOuter : goodOuter ∈ cofinite := by
    change {q : ℕ |
      Valued.v (outerTerm q) <
        MonoidWithZeroHom.ValueGroup₀.embedding γ.1} ∈ cofinite
    exact houterEventually
  have hbadOuterFinite : goodOuterᶜ.Finite :=
    Filter.mem_cofinite.mp hgoodOuter
  let Q : Finset ℕ := hbadOuterFinite.toFinset
  have hpower : ∀ q : ℕ,
      HasSum
        (fun d : ℕ => PowerSeries.coeff d (g ^ q) * x ^ d)
        (y ^ q) :=
    fun q => hasSum_powerSeries_pow_coeff_mul_pow g x y hgy q
  have hfiber : ∀ q : ℕ,
      HasSum (fun d : ℕ => term ⟨q, d⟩)
        (PowerSeries.coeff q f * y ^ q) := by
    intro q
    simpa [term, mul_assoc] using
      (hpower q).mul_left (PowerSeries.coeff q f)
  let badFiber : ℕ → Set ℕ := fun q => {d | term ⟨q, d⟩ ∉ s}
  have hbadFiberFinite : ∀ q : ℕ, (badFiber q).Finite := by
    intro q
    have hevent := (hfiber q).summable.tendsto_cofinite_zero.eventually hs
    apply (Filter.mem_cofinite.mp hevent).subset
    intro d hd
    exact hd
  let D : ℕ → Finset ℕ := fun q => (hbadFiberFinite q).toFinset
  let E : Finset (Sigma fun _ : ℕ => ℕ) := Q.sigma D
  apply Filter.mem_cofinite.mpr
  apply E.finite_toSet.subset
  intro qd hbad
  by_contra hnotE
  have hgood : term qd ∈ s := by
    by_cases hq : qd.1 ∈ Q
    · have hdnot : qd.2 ∉ D qd.1 := by
        intro hd
        apply hnotE
        exact Finset.mem_sigma.mpr ⟨hq, hd⟩
      by_contra hterm
      apply hdnot
      simp [D, badFiber, hterm]
    · have houterGood :
          Valued.v (outerTerm qd.1) <
            MonoidWithZeroHom.ValueGroup₀.embedding γ.1 := by
        have hgoodMem : qd.1 ∈ goodOuter := by
          by_contra hnotGood
          apply hq
          simpa [Q] using hnotGood
        exact hgoodMem
      apply hγ
      change Valued.v.restrict (term qd) < γ.1
      rw [Valuation.restrict_lt_iff_lt_embedding]
      have hbound :=
        valuation_powerSeries_subst_sigmaTerm_le_outerTerm
          Valued.v f g x hcoeff qd.1 qd.2
      exact lt_of_le_of_lt (by simpa [term, outerTerm] using hbound) houterGood
  exact hbad hgood

/-- Expanded substitution has the value obtained by first evaluating the
inner series and then the outer series. -/
theorem hasSum_powerSeries_subst_sigma
    [Valued K (WithZero (Multiplicative ℤ))] [CompleteSpace K]
    [NonarchimedeanRing K]
    (f g : PowerSeries K) (x y z : K)
    (hgy : HasSum (fun d : ℕ => PowerSeries.coeff d g * x ^ d) y)
    (houterX : Summable
      (fun q : ℕ => PowerSeries.coeff q f * x ^ q))
    (houterY : HasSum
      (fun q : ℕ => PowerSeries.coeff q f * y ^ q) z)
    (hcoeff : ∀ d : ℕ,
      Valued.v (PowerSeries.coeff d g * x ^ d) ≤ Valued.v x) :
    HasSum
      (fun qd : Sigma fun _ : ℕ => ℕ =>
        PowerSeries.coeff qd.1 f *
          PowerSeries.coeff qd.2 (g ^ qd.1) * x ^ qd.2)
      z := by
  have hsigma :=
    summable_powerSeries_subst_sigma_of_outer_summable
      f g x y hgy houterX hcoeff
  have hinner : ∀ q : ℕ,
      HasSum
        (fun d : ℕ =>
          PowerSeries.coeff q f * PowerSeries.coeff d (g ^ q) * x ^ d)
        (PowerSeries.coeff q f * y ^ q) := by
    intro q
    simpa [mul_assoc] using
      (hasSum_powerSeries_pow_coeff_mul_pow g x y hgy q).mul_left
        (PowerSeries.coeff q f)
  exact HasSum.sigma_of_hasSum houterY hinner hsigma

/-- Regrouping the expanded substitution by the final monomial degree gives
the coefficient evaluation of the formal substitution itself.  Finiteness
of every regrouped fiber is supplied by `PowerSeries.coeff_subst_finite'`. -/
theorem hasSum_powerSeries_subst_coeff_mul_pow_of_sigma
    [Valued K (WithZero (Multiplicative ℤ))]
    (f g : PowerSeries K) (x z : K)
    (hg0 : PowerSeries.constantCoeff g = 0)
    (hsigma :
      HasSum
        (fun qd : Sigma fun _ : ℕ => ℕ =>
          PowerSeries.coeff qd.1 f *
            PowerSeries.coeff qd.2 (g ^ qd.1) * x ^ qd.2)
        z) :
    HasSum
      (fun d : ℕ =>
        PowerSeries.coeff d (PowerSeries.subst g f) * x ^ d)
      z := by
  have hg : PowerSeries.HasSubst g :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hg0
  let sigmaTerm : (Sigma fun _ : ℕ => ℕ) → K := fun qd =>
    PowerSeries.coeff qd.1 f *
      PowerSeries.coeff qd.2 (g ^ qd.1) * x ^ qd.2
  have hsigma' : HasSum sigmaTerm z := by
    simpa [sigmaTerm] using hsigma
  let swap :
      (Sigma fun _ : ℕ => ℕ) ≃ (Sigma fun _ : ℕ => ℕ) :=
    { toFun := fun dq => ⟨dq.2, dq.1⟩
      invFun := fun qd => ⟨qd.2, qd.1⟩
      left_inv := by intro dq; cases dq; rfl
      right_inv := by intro qd; cases qd; rfl }
  have hswapped : HasSum (sigmaTerm ∘ swap) z :=
    (swap.hasSum_iff).2 hsigma'
  have hfiber : ∀ d : ℕ,
      HasSum
        (fun q : ℕ => (sigmaTerm ∘ swap) ⟨d, q⟩)
        (PowerSeries.coeff d (PowerSeries.subst g f) * x ^ d) := by
    intro d
    let base : ℕ → K := fun q =>
      PowerSeries.coeff q f • PowerSeries.coeff d (g ^ q)
    let fiberTerm : ℕ → K := fun q => base q * x ^ d
    have hsupport : base.support.Finite := by
      rw [← Function.HasFiniteSupport]
      simpa only [base] using PowerSeries.coeff_subst_finite' hg f d
    let S : Finset ℕ := hsupport.toFinset
    have hfinite :
        HasSum fiberTerm (∑ q ∈ S, fiberTerm q) := by
      apply hasSum_sum_of_ne_finset_zero
      intro q hq
      have hbase : base q = 0 := by
        by_contra hne
        apply hq
        simp [S, hne]
      simp [fiberTerm, hbase]
    have hsum :
        (∑ q ∈ S, fiberTerm q) =
          PowerSeries.coeff d (PowerSeries.subst g f) * x ^ d := by
      rw [PowerSeries.coeff_subst' hg f d]
      rw [finsum_eq_sum _ hsupport]
      rw [Finset.sum_mul]
    rw [hsum] at hfinite
    simpa [fiberTerm, base, sigmaTerm, swap, Function.comp_def,
      smul_eq_mul, mul_assoc] using hfinite
  exact hswapped.sigma hfiber

/-- A source-level evaluation theorem for convergent formal substitution. -/
theorem hasSum_powerSeries_subst_coeff_mul_pow
    [Valued K (WithZero (Multiplicative ℤ))] [CompleteSpace K]
    [NonarchimedeanRing K]
    (f g : PowerSeries K) (x y z : K)
    (hg0 : PowerSeries.constantCoeff g = 0)
    (hgy : HasSum (fun d : ℕ => PowerSeries.coeff d g * x ^ d) y)
    (houterX : Summable
      (fun q : ℕ => PowerSeries.coeff q f * x ^ q))
    (houterY : HasSum
      (fun q : ℕ => PowerSeries.coeff q f * y ^ q) z)
    (hcoeff : ∀ d : ℕ,
      Valued.v (PowerSeries.coeff d g * x ^ d) ≤ Valued.v x) :
    HasSum
      (fun d : ℕ =>
        PowerSeries.coeff d (PowerSeries.subst g f) * x ^ d)
      z := by
  apply hasSum_powerSeries_subst_coeff_mul_pow_of_sigma f g x z hg0
  exact hasSum_powerSeries_subst_sigma
    f g x y z hgy houterX houterY hcoeff

/-! ## Scaled logarithm and exponential input estimates -/

/-- Scaled evaluation of the formal exponential series. -/
theorem hasSum_formalExpPowerSeries_eval_expSeriesField_ofWithZeroValuation_scaled
    [Algebra ℚ K]
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) (x : K)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p n.factorial : ℤ))))
    (hthreshold : ∀ hx : x ≠ 0,
      (e : ℝ) / ((p : ℝ) - 1) <
        ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℝ))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    HasSum
      (fun n : ℕ =>
        PowerSeries.coeff n (PowerSeries.exp K) * x ^ n)
      (expSeriesFieldOfWithZeroValuation v x hnK) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  have hsum :=
    hasSum_expSeriesTermField_expSeriesField_ofWithZeroValuation_scaled_of_threshold
      (v := v) (p := p) e x hnK hnval hthreshold hcomplete
  exact hsum.congr_fun fun n =>
    formalExpPowerSeries_coeff_mul_pow_eq_expSeriesTermField
      (K := K) x hnK n

/-- Evaluation commutes with subtracting the constant power series `1`. -/
theorem hasSum_powerSeries_sub_one_coeff_mul_pow
    [Valued K (WithZero (Multiplicative ℤ))]
    (f : PowerSeries K) (x z : K)
    (hf : HasSum (fun d : ℕ => PowerSeries.coeff d f * x ^ d) z) :
    HasSum
      (fun d : ℕ => PowerSeries.coeff d (f - 1) * x ^ d)
      (z - 1) := by
  have hsingle :
      HasSum (fun d : ℕ => if d = 0 then (1 : K) else 0) 1 := by
    apply hasSum_single 0
    intro d hd
    simp [hd]
  have hone :
      HasSum
        (fun d : ℕ => PowerSeries.coeff d (1 : PowerSeries K) * x ^ d)
        1 :=
    hsingle.congr_fun fun d => by
      by_cases hd : d = 0
      · subst d
        simp
      · simp [PowerSeries.coeff_one, hd]
  refine (hf.sub hone).congr_fun ?_
  intro d
  rw [map_sub]
  ring

/-- The scaled threshold implies that the argument lies in the open unit
ball, including the zero argument. -/
theorem valuation_lt_one_ofWithZeroValuation_scaled_threshold_real
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) {x : K}
    (hthreshold : ∀ hx : x ≠ 0,
      (e : ℝ) / ((p : ℝ) - 1) <
        ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℝ)) :
    v x < (1 : WithZero (Multiplicative ℤ)) := by
  by_cases hx : x = 0
  · simp [hx]
  · have hp_two : (2 : ℕ) ≤ p := (Fact.out : Nat.Prime p).two_le
    have hp_two_real : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp_two
    have hp_sub_pos : 0 < ((p : ℝ) - 1) := by linarith
    have hnonneg : 0 ≤ (e : ℝ) / ((p : ℝ) - 1) :=
      div_nonneg (Nat.cast_nonneg e) hp_sub_pos.le
    have hxval_pos_real :
        (0 : ℝ) <
          ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℝ) :=
      lt_of_le_of_lt hnonneg (hthreshold hx)
    have hxval_pos :
        0 < (ofWithZeroValuation v).val (Units.mk0 x hx) := by
      exact_mod_cast hxval_pos_real
    exact valuation_lt_one_of_ofWithZeroValuation_val_pos
      v (Units.mk0 x hx) hxval_pos

/-- On the sharp scaled threshold, every evaluated coefficient of the formal
logarithm is bounded by the linear term. -/
theorem valuation_powerSeries_log_coeff_mul_pow_le_self_scaled
    [Algebra ℚ K]
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) {x : K}
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p (n + 1) : ℤ))))
    (hthreshold : ∀ hx : x ≠ 0,
      (e : ℝ) / ((p : ℝ) - 1) <
        ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℝ))
    (d : ℕ) :
    v (PowerSeries.coeff d (PowerSeries.log K) * x ^ d) ≤
      v x := by
  by_cases hx : x = 0
  · subst x
    by_cases hd : d = 0
    · subst d
      simp [PowerSeries.coeff_log]
    · simp [hd]
  · have hthresholdRat :
        (e : ℚ) / ((p : ℚ) - 1) <
          ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℚ) := by
      exact_mod_cast hthreshold hx
    cases d with
    | zero => simp [PowerSeries.coeff_log]
    | succ n =>
        cases n with
        | zero =>
            rw [powerSeries_log_coeff_mul_pow_eq_signedLogSeriesTermField
              (K := K) x hnK 0]
            simp
        | succ n =>
            rw [powerSeries_log_coeff_mul_pow_eq_signedLogSeriesTermField
              (K := K) x hnK (n + 1)]
            exact le_of_lt
              (valuation_signedLogSeriesTermField_lt_self_of_scaled_inv_sub_one_lt
                (v := v) (p := p) e (x := x) hx hnK hnval hthresholdRat
                (by omega : n + 1 ≠ 0))

/-- On the sharp scaled threshold, every evaluated coefficient of
`exp(X)-1` is bounded by its linear term. -/
theorem valuation_formalExp_sub_one_coeff_mul_pow_le_self_scaled
    [Algebra ℚ K]
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) {x : K}
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p n.factorial : ℤ))))
    (hthreshold : ∀ hx : x ≠ 0,
      (e : ℝ) / ((p : ℝ) - 1) <
        ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℝ))
    (d : ℕ) :
    v (PowerSeries.coeff d ((PowerSeries.exp K) - 1) * x ^ d) ≤ v x := by
  by_cases hx : x = 0
  · subst x
    by_cases hd : d = 0
    · subst d
      simp
    · simp [hd]
  · have hthresholdRat :
        (e : ℚ) / ((p : ℚ) - 1) <
          ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℚ) := by
      exact_mod_cast hthreshold hx
    cases d with
    | zero => simp
    | succ n =>
        cases n with
        | zero => simp [PowerSeries.coeff_exp]
        | succ n =>
            have hcoeff :
                PowerSeries.coeff (n + 2) ((PowerSeries.exp K) - 1) * x ^ (n + 2) =
                  expSeriesTermField x hnK (n + 2) := by
              rw [map_sub]
              have hone :
                  PowerSeries.coeff (n + 2) (1 : PowerSeries K) = 0 := by
                simp [PowerSeries.coeff_one]
              rw [hone, sub_zero]
              exact
                formalExpPowerSeries_coeff_mul_pow_eq_expSeriesTermField
                  (K := K) x hnK (n + 2)
            rw [hcoeff]
            exact le_of_lt
              (valuation_expSeriesTermField_lt_self_of_scaled_inv_sub_one_lt
                (v := v) (p := p) e (x := x) hx hnK hnval hthresholdRat
                (by omega : 2 ≤ n + 2))

/-! ## Evaluation of the two formal identities -/

/-- Evaluation of the formal series `X`. -/
theorem hasSum_powerSeries_X_coeff_mul_pow
    [Valued K (WithZero (Multiplicative ℤ))] (x : K) :
    HasSum
      (fun d : ℕ => PowerSeries.coeff d (PowerSeries.X : PowerSeries K) * x ^ d)
      x := by
  have hsingle :
      HasSum (fun d : ℕ => if d = 1 then x else 0) x := by
    apply hasSum_single 1
    intro d hd
    simp [hd]
  exact hsingle.congr_fun fun d => by
    by_cases hd : d = 1
    · subst d
      simp [PowerSeries.coeff_X]
    · simp [PowerSeries.coeff_X, hd]

/-- Evaluation of the formal series `1 + X`. -/
theorem hasSum_powerSeries_one_add_X_coeff_mul_pow
    [Valued K (WithZero (Multiplicative ℤ))] (x : K) :
    HasSum
      (fun d : ℕ =>
        PowerSeries.coeff d (1 + PowerSeries.X : PowerSeries K) * x ^ d)
      (1 + x) := by
  have hsingle :
      HasSum (fun d : ℕ => if d = 0 then (1 : K) else 0) 1 := by
    apply hasSum_single 0
    intro d hd
    simp [hd]
  have hone :
      HasSum
        (fun d : ℕ => PowerSeries.coeff d (1 : PowerSeries K) * x ^ d)
        1 :=
    hsingle.congr_fun fun d => by
      by_cases hd : d = 0
      · subst d
        simp
      · simp [PowerSeries.coeff_one, hd]
  have hx := hasSum_powerSeries_X_coeff_mul_pow (K := K) x
  refine (hone.add hx).congr_fun ?_
  intro d
  rw [map_add]
  ring

/-- The deep exponential–logarithm equivalence, exact principal-unit composite:
on the sharp scaled threshold, evaluating the formal identity
`exp(log(1+X)) = 1+X` gives `exp(log(1+x)) = 1+x`. -/
theorem expSeries_logOnePlusSeries_eq_one_add_ofWithZeroValuation_scaled_of_threshold
    [Algebra ℚ K]
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) (x : K)
    (hnKlog : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnvalLog : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p (n + 1) : ℤ))))
    (hnKexp : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnvalExp : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p n.factorial : ℤ))))
    (hthreshold : ∀ hx : x ≠ 0,
      (e : ℝ) / ((p : ℝ) - 1) <
        ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℝ))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    expSeriesFieldOfWithZeroValuation v
        (logOnePlusSeriesFieldOfWithZeroValuation v x hnKlog) hnKexp =
      1 + x := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let : CompleteSpace K := hcomplete
  have : NonarchimedeanRing K := nonarchimedeanRing_ofWithZeroValuation v
  let : IsAddTorsionFree K := IsAddTorsionFree.of_module_rat K
  by_cases hx : x = 0
  · subst x
    simp
  · let y : K := logOnePlusSeriesFieldOfWithZeroValuation v x hnKlog
    have hvx_lt_one : v x < (1 : WithZero (Multiplicative ℤ)) :=
      valuation_lt_one_ofWithZeroValuation_scaled_threshold_real
        (v := v) (p := p) e hthreshold
    have hthresholdRat :
        (e : ℚ) / ((p : ℚ) - 1) <
          ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℚ) := by
      exact_mod_cast hthreshold hx
    have hvy_eq : v y = v x := by
      simpa [y] using
        valuation_logOnePlusSeriesField_eq_self_of_scaled_inv_sub_one_lt
          (v := v) (p := p) e (x := x) hx hnKlog hnvalLog hvx_lt_one
          hthresholdRat hcomplete
    have hy : y ≠ 0 := by
      intro hy0
      have hzero : v y = 0 := by simp [hy0]
      have hxzero : v x = 0 := by simpa [hvy_eq] using hzero
      exact ((_root_.Valuation.ne_zero_iff v).2 hx) hxzero
    have hyval_eq :
        (ofWithZeroValuation v).val (Units.mk0 y hy) =
          (ofWithZeroValuation v).val (Units.mk0 x hx) :=
      ofWithZeroValuation_val_eq_of_valuation_eq v hvy_eq
    have hythreshold : ∀ hy' : y ≠ 0,
        (e : ℝ) / ((p : ℝ) - 1) <
          ((ofWithZeroValuation v).val (Units.mk0 y hy') : ℝ) := by
      intro hy'
      have hyproof : Units.mk0 y hy' = Units.mk0 y hy := by
        ext
        rfl
      rw [hyproof, hyval_eq]
      exact hthreshold hx
    have hinner :
        HasSum
          (fun d : ℕ =>
            PowerSeries.coeff d (PowerSeries.log K) * x ^ d)
          y := by
      simpa [y] using
        hasSum_powerSeries_log_eval_nat_logOnePlusSeriesField_ofWithZeroValuation_scaled
          (v := v) (p := p) e x hnKlog hnvalLog hvx_lt_one hcomplete
    have houterX :
        HasSum
          (fun q : ℕ => PowerSeries.coeff q (PowerSeries.exp K) * x ^ q)
          (expSeriesFieldOfWithZeroValuation v x hnKexp) :=
      hasSum_formalExpPowerSeries_eval_expSeriesField_ofWithZeroValuation_scaled
        (v := v) (p := p) e x hnKexp hnvalExp hthreshold hcomplete
    have houterY :
        HasSum
          (fun q : ℕ => PowerSeries.coeff q (PowerSeries.exp K) * y ^ q)
          (expSeriesFieldOfWithZeroValuation v y hnKexp) :=
      hasSum_formalExpPowerSeries_eval_expSeriesField_ofWithZeroValuation_scaled
        (v := v) (p := p) e y hnKexp hnvalExp hythreshold hcomplete
    have hcoeff : ∀ d : ℕ,
        v (PowerSeries.coeff d (PowerSeries.log K) * x ^ d) ≤ v x :=
      valuation_powerSeries_log_coeff_mul_pow_le_self_scaled
        (v := v) (p := p) e hnKlog hnvalLog hthreshold
    have hcomp :
        HasSum
          (fun d : ℕ =>
            PowerSeries.coeff d
                (PowerSeries.subst (PowerSeries.log K)
                  (PowerSeries.exp K)) * x ^ d)
          (expSeriesFieldOfWithZeroValuation v y hnKexp) :=
      hasSum_powerSeries_subst_coeff_mul_pow
        (PowerSeries.exp K) (PowerSeries.log K) x y
          (expSeriesFieldOfWithZeroValuation v y hnKexp)
          PowerSeries.constantCoeff_log hinner
          houterX.summable houterY hcoeff
    rw [PowerSeries.exp_subst_log_eq_one_add_X K] at hcomp
    exact hcomp.unique (hasSum_powerSeries_one_add_X_coeff_mul_pow (K := K) x)

/-- The deep exponential–logarithm equivalence, exact maximal-ideal composite:
on the sharp scaled threshold, evaluating the formal identity
`log(exp(X)) = X` gives `log(exp(x)) = x`. -/
theorem logOnePlusSeries_expSeries_sub_one_eq_self_ofWithZeroValuation_scaled_of_threshold
    [Algebra ℚ K]
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) (x : K)
    (hnKexp : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnvalExp : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p n.factorial : ℤ))))
    (hnKlog : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnvalLog : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p (n + 1) : ℤ))))
    (hthreshold : ∀ hx : x ≠ 0,
      (e : ℝ) / ((p : ℝ) - 1) <
        ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℝ))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    logOnePlusSeriesFieldOfWithZeroValuation v
        (expSeriesFieldOfWithZeroValuation v x hnKexp - 1) hnKlog =
      x := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let : CompleteSpace K := hcomplete
  have : NonarchimedeanRing K := nonarchimedeanRing_ofWithZeroValuation v
  let : IsAddTorsionFree K := IsAddTorsionFree.of_module_rat K
  by_cases hx : x = 0
  · subst x
    simp
  · let y : K := expSeriesFieldOfWithZeroValuation v x hnKexp - 1
    have hvx_lt_one : v x < (1 : WithZero (Multiplicative ℤ)) :=
      valuation_lt_one_ofWithZeroValuation_scaled_threshold_real
        (v := v) (p := p) e hthreshold
    have hthresholdRat :
        (e : ℚ) / ((p : ℚ) - 1) <
          ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℚ) := by
      exact_mod_cast hthreshold hx
    have hvy_eq : v y = v x := by
      simpa [y] using
        valuation_expSeriesField_sub_one_eq_self_ofWithZeroValuation_scaled_of_threshold
          (v := v) (p := p) e (x := x) hx hnKexp hnvalExp
          hthresholdRat hcomplete
    have hvy_lt_one : v y < (1 : WithZero (Multiplicative ℤ)) := by
      simpa [hvy_eq] using hvx_lt_one
    have hexp :
        HasSum
          (fun d : ℕ => PowerSeries.coeff d (PowerSeries.exp K) * x ^ d)
          (expSeriesFieldOfWithZeroValuation v x hnKexp) :=
      hasSum_formalExpPowerSeries_eval_expSeriesField_ofWithZeroValuation_scaled
        (v := v) (p := p) e x hnKexp hnvalExp hthreshold hcomplete
    have hinner :
        HasSum
          (fun d : ℕ =>
            PowerSeries.coeff d ((PowerSeries.exp K) - 1) * x ^ d)
          y := by
      simpa [y] using
        hasSum_powerSeries_sub_one_coeff_mul_pow
          (PowerSeries.exp K) x
            (expSeriesFieldOfWithZeroValuation v x hnKexp) hexp
    have houterX :
        HasSum
          (fun q : ℕ =>
            PowerSeries.coeff q (PowerSeries.log K) * x ^ q)
          (logOnePlusSeriesFieldOfWithZeroValuation v x hnKlog) :=
      hasSum_powerSeries_log_eval_nat_logOnePlusSeriesField_ofWithZeroValuation_scaled
        (v := v) (p := p) e x hnKlog hnvalLog hvx_lt_one hcomplete
    have houterY :
        HasSum
          (fun q : ℕ =>
            PowerSeries.coeff q (PowerSeries.log K) * y ^ q)
          (logOnePlusSeriesFieldOfWithZeroValuation v y hnKlog) :=
      hasSum_powerSeries_log_eval_nat_logOnePlusSeriesField_ofWithZeroValuation_scaled
        (v := v) (p := p) e y hnKlog hnvalLog hvy_lt_one hcomplete
    have hcoeff : ∀ d : ℕ,
        v (PowerSeries.coeff d ((PowerSeries.exp K) - 1) * x ^ d) ≤ v x :=
      valuation_formalExp_sub_one_coeff_mul_pow_le_self_scaled
        (v := v) (p := p) e hnKexp hnvalExp hthreshold
    have hg0 :
        PowerSeries.constantCoeff ((PowerSeries.exp K) - 1) = 0 := by
      simp
    have hcomp :
        HasSum
          (fun d : ℕ =>
            PowerSeries.coeff d
                (PowerSeries.subst ((PowerSeries.exp K) - 1)
                  (PowerSeries.log K)) * x ^ d)
          (logOnePlusSeriesFieldOfWithZeroValuation v y hnKlog) :=
      hasSum_powerSeries_subst_coeff_mul_pow
        (PowerSeries.log K) ((PowerSeries.exp K) - 1) x y
          (logOnePlusSeriesFieldOfWithZeroValuation v y hnKlog)
          hg0 hinner houterX.summable houterY hcoeff
    rw [PowerSeries.log_subst_exp_sub_one_eq_X K] at hcomp
    exact hcomp.unique (hasSum_powerSeries_X_coeff_mul_pow (K := K) x)

end MultiplicativeIntegerValuation
end LocalFieldTheory.DiscreteValuationField
