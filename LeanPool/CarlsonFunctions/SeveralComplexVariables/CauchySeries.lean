/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Data.Fin.Tuple.NatAntidiagonal
public import LeanPool.CarlsonFunctions.SeveralComplexVariables.CauchyIntegral

/-!
# Multivariable Cauchy coefficients and series

Cauchy coefficients, their estimates, and their packaging as a `FormalMultilinearSeries`.
`hasFPowerSeriesOnBall_polydiscCauchy_full` represents the function on the entire open
equal-radius polydisc. The original half-radius theorem remains as a compatibility wrapper.
Diagonal coefficients are identified with iterated Fréchet derivatives.

Apply Mathlib's `HasFPowerSeriesOnBall.tendstoLocallyUniformlyOn` and
`HasFPowerSeriesOnBall.uniform_geometric_approx` to obtain locally uniform partial-sum
convergence and geometric remainder bounds on smaller polydiscs. Individual mixed coefficients
and radius independence are developed in `CauchyCoefficients`; the separate-radius multi-index
expansion, its uniform convergence and remainder estimates are in `PolydiscTaylor`.
-/

@[expose] public section

open Complex Filter Function MeasureTheory Metric Set
open scoped Classical ENNReal NNReal Real Topology

namespace SeveralComplexVariables

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-! ### Multi-index Cauchy series -/

/-- The continuous multilinear monomial associated to a multi-index of total degree `n`. -/
noncomputable def multiIndexMonomial {d n : ℕ} (m : Fin d → ℕ)
    (hm : ∑ i, m i = n) :
    ContinuousMultilinearMap ℂ (fun _ : Fin n => (Fin d → ℂ)) ℂ := by
  let e : (Σ i, Fin (m i)) ≃ Fin n := Fintype.equivFinOfCardEq (by simpa using hm)
  exact ((ContinuousMultilinearMap.mkPiAlgebra ℂ (Σ i, Fin (m i)) ℂ).compContinuousLinearMap
    (fun q => ContinuousLinearMap.proj q.1)).domDomCongr e

/-- On the diagonal, `multiIndexMonomial` evaluates to the usual multi-index monomial. -/
lemma multiIndexMonomial_apply {d n : ℕ} (m : Fin d → ℕ)
    (hm : ∑ i, m i = n) (w : Fin d → ℂ) :
    multiIndexMonomial m hm (fun _ => w) = ∏ i, w i ^ m i := by
  simp [multiIndexMonomial, Fintype.prod_sigma]

/-- The operator norm of `multiIndexMonomial` is at most one for the sup norm. -/
lemma norm_multiIndexMonomial_le {d n : ℕ} (m : Fin d → ℕ)
    (hm : ∑ i, m i = n) : ‖multiIndexMonomial m hm‖ ≤ 1 := by
  rw [multiIndexMonomial, ContinuousMultilinearMap.norm_domDomCongr]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [ContinuousMultilinearMap.norm_mkPiAlgebra]
  simp only [one_mul]
  refine Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun q _ => ?_
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => ?_
  simpa using norm_le_pi_norm w q.1

/-- Absolute summability of a finite product of geometric series. -/
lemma summable_norm_pi_geometric {K : Type*} [NormedCommRing K]
    {d : ℕ} (x : Fin d → K) (hx : ∀ i, ‖x i‖ < 1) :
    Summable fun m : Fin d → ℕ => ‖∏ i, x i ^ m i‖ := by
  induction d with
  | zero =>
      exact (hasSum_single (0 : Fin 0 → ℕ) fun m hm =>
        (hm (Subsingleton.elim _ _)).elim).summable
  | succ d ih =>
      let e := Fin.consEquiv (fun _ : Fin (d + 1) => ℕ)
      have hhead : Summable (fun n : ℕ => ‖x 0 ^ n‖) :=
        summable_norm_geometric_of_norm_lt_one (hx 0)
      have htail := ih (fun i => x i.succ) (fun i => hx i.succ)
      have hprod := hhead.mul_of_nonneg htail (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
      rw [← e.summable_iff]
      refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ?_ hprod
      intro p
      simpa only [Function.comp_apply, e, Fin.consEquiv_apply, Fin.prod_univ_succ,
        Fin.cons_zero, Fin.cons_succ] using
        norm_mul_le (x 0 ^ p.1) (∏ i, x i.succ ^ p.2 i)

/-- The multivariable geometric series sums to the product of its one-variable sums. -/
lemma hasSum_pi_geometric {K : Type*} [NormedField K] [CompleteSpace K]
    {d : ℕ} (x : Fin d → K) (hx : ∀ i, ‖x i‖ < 1) :
    HasSum (fun m : Fin d → ℕ => ∏ i, x i ^ m i) (∏ i, (1 - x i)⁻¹) := by
  induction d with
  | zero =>
      simp
  | succ d ih =>
      let e := Fin.consEquiv (fun _ : Fin (d + 1) => ℕ)
      have hhead : HasSum (fun n : ℕ => x 0 ^ n) (1 - x 0)⁻¹ :=
        hasSum_geometric_of_norm_lt_one (hx 0)
      have htail : HasSum (fun m : Fin d → ℕ => ∏ i, x i.succ ^ m i)
          (∏ i : Fin d, (1 - x i.succ)⁻¹) :=
        ih (fun i => x i.succ) (fun i => hx i.succ)
      have hnormHead : Summable (fun n : ℕ => ‖x 0 ^ n‖) :=
        summable_norm_geometric_of_norm_lt_one (hx 0)
      have hnormTail : Summable (fun m : Fin d → ℕ => ‖∏ i, x i.succ ^ m i‖) :=
        summable_norm_pi_geometric _ (fun i => hx i.succ)
      have hsummul : Summable
          (fun p : ℕ × (Fin d → ℕ) => x 0 ^ p.1 * ∏ i, x i.succ ^ p.2 i) :=
        (hnormHead.mul_norm hnormTail).of_norm
      have hprod : HasSum
          (fun p : ℕ × (Fin d → ℕ) => x 0 ^ p.1 * ∏ i, x i.succ ^ p.2 i)
          ((1 - x 0)⁻¹ * ∏ i : Fin d, (1 - x i.succ)⁻¹) := by
        rw [← hhead.tsum_eq, ← htail.tsum_eq,
          tsum_mul_tsum_of_summable_norm hnormHead hnormTail]
        exact hsummul.hasSum
      rw [← e.hasSum_iff]
      convert hprod using 1
      · ext p
        simp [e, Fin.prod_univ_succ]
      · simp [Fin.prod_univ_succ, mul_comm]

private lemma hasSum_antidiagonalTuple_geometric {K : Type*} [NormedField K] [CompleteSpace K]
    {d : ℕ} (x : Fin d → K)
    (hx : ∀ i, ‖x i‖ < 1) :
    HasSum (fun n : ℕ => ∑ m ∈ Finset.Nat.antidiagonalTuple d n, ∏ i, x i ^ m i)
      (∏ i, (1 - x i)⁻¹) := by
  have h := hasSum_pi_geometric x hx
  let e := Finset.Nat.sigmaAntidiagonalTupleEquivTuple d
  have he0 : HasSum
      ((fun m : Fin d → ℕ => ∏ i, x i ^ m i) ∘ e)
      (∏ i, (1 - x i)⁻¹) := e.hasSum_iff.mpr h
  have he : HasSum
      (fun p : Σ n, Finset.Nat.antidiagonalTuple d n =>
        ∏ i, x i ^ (p.2 : Fin d → ℕ) i)
      (∏ i, (1 - x i)⁻¹) := by
    convert he0 using 1
    · ext p
      rfl
  have hfin : ∀ n, HasSum
      (fun m : Finset.Nat.antidiagonalTuple d n => ∏ i, x i ^ (m : Fin d → ℕ) i)
      (∑ m ∈ Finset.Nat.antidiagonalTuple d n, ∏ i, x i ^ m i) := by
    intro n
    rw [← Finset.sum_finset_coe]
    exact hasSum_fintype (f := fun m : Finset.Nat.antidiagonalTuple d n =>
      ∏ i, x i ^ (m : Fin d → ℕ) i)
  exact he.sigma hfin

/-- The multi-index Cauchy coefficient of a vector-valued function on a polydisc. -/
noncomputable def polydiscCauchyCoeff {d : ℕ} (f : (Fin d → ℂ) → E)
    (c : Fin d → ℂ) (R : ℝ) (m : Fin d → ℕ) : E :=
  ((2 * π * I : ℂ) ^ d)⁻¹ • torusIntegral
    (fun z => (∏ i, (z i - c i)⁻¹ ^ (m i + 1)) • f z) c (fun _ => R)

/-- The formal multilinear series obtained by grouping the polydisc Cauchy coefficients by total
degree. -/
noncomputable def polydiscCauchySeries {d : ℕ} (f : (Fin d → ℂ) → E)
    (c : Fin d → ℂ) (R : ℝ) : FormalMultilinearSeries ℂ (Fin d → ℂ) E := fun n =>
  ∑ m : Finset.Nat.antidiagonalTuple d n,
    (multiIndexMonomial (m : Fin d → ℕ)
      (Finset.Nat.mem_antidiagonalTuple.mp m.property)).smulRight
        (polydiscCauchyCoeff f c R m)

omit [CompleteSpace E] in
/-- Evaluation of the homogeneous terms of `polydiscCauchySeries` on the diagonal. -/
lemma polydiscCauchySeries_apply {d n : ℕ} (f : (Fin d → ℂ) → E)
    (c h : Fin d → ℂ) (R : ℝ) :
    polydiscCauchySeries f c R n (fun _ => h) =
      ∑ m : Finset.Nat.antidiagonalTuple d n,
        (∏ i, h i ^ (m : Fin d → ℕ) i) • polydiscCauchyCoeff f c R m := by
  simp [polydiscCauchySeries, multiIndexMonomial_apply]

omit [CompleteSpace E] in
/-- Cauchy's coefficient estimate for the multi-index coefficients of a bounded function on a
closed polydisc. -/
lemma norm_polydiscCauchyCoeff_le {d : ℕ} {f : (Fin d → ℂ) → E}
    {c : Fin d → ℂ} {R M : ℝ} (hR : 0 < R)
    (hM : ∀ z ∈ closedPolydisc c R, ‖f z‖ ≤ M) (m : Fin d → ℕ) :
    ‖polydiscCauchyCoeff f c R m‖ ≤ M * R⁻¹ ^ (∑ i, m i) := by
  have hM0 : 0 ≤ M := (norm_nonneg (f c)).trans (hM c (by
    intro i _
    simp [mem_closedBall, dist_self, hR.le]))
  rw [polydiscCauchyCoeff, norm_smul]
  refine (mul_le_mul_of_nonneg_left (norm_torusIntegral_le_of_norm_le_const
    (C := M * R⁻¹ ^ (∑ i, (m i + 1))) ?_)
    (norm_nonneg _)).trans_eq ?_
  · intro θ
    rw [norm_smul]
    calc
      ‖∏ i, (torusMap c (fun _ => R) θ i - c i)⁻¹ ^ (m i + 1)‖ *
          ‖f (torusMap c (fun _ => R) θ)‖
          ≤ ‖∏ i, (torusMap c (fun _ => R) θ i - c i)⁻¹ ^ (m i + 1)‖ * M :=
        mul_le_mul_of_nonneg_left (hM _ (torusMap_mem_closedPolydisc hR.le θ))
          (norm_nonneg _)
      _ = M * R⁻¹ ^ (∑ i, (m i + 1)) := by
        simp only [norm_prod, norm_pow, norm_inv, torusMap_coord_norm hR.le]
        rw [Finset.prod_pow_eq_pow_sum]
        ring
  · simp only [norm_inv, norm_pow, norm_mul, norm_ofNat, norm_real, norm_I, mul_one,
      Real.norm_eq_abs, abs_of_pos hR, abs_of_pos Real.pi_pos, Fin.prod_const]
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
    field_simp
    simp only [one_div, pow_add]
    calc
      R ^ d * M * (R⁻¹ ^ (∑ x, m x) * R⁻¹ ^ d) =
          M * R⁻¹ ^ (∑ x, m x) * (R ^ d * R⁻¹ ^ d) := by ring
      _ = M * R⁻¹ ^ ∑ x, m x := by
        rw [← mul_pow, mul_inv_cancel₀ hR.ne', one_pow, mul_one]

omit [CompleteSpace E] in
private lemma norm_polydiscCauchySeries_mul_pow_le {d : ℕ} {f : (Fin d → ℂ) → E}
    {c : Fin d → ℂ} {R M r : ℝ} (hR : 0 < R) (hr : 0 ≤ r)
    (hM : ∀ z ∈ closedPolydisc c R, ‖f z‖ ≤ M) (n : ℕ) :
    ‖polydiscCauchySeries f c R n‖ * r ^ n ≤
      M * ∑ m : Finset.Nat.antidiagonalTuple d n,
        ∏ i, (r * R⁻¹) ^ (m : Fin d → ℕ) i := by
  have hM0 : 0 ≤ M := (norm_nonneg (f c)).trans (hM c (by
    intro i _
    simp [mem_closedBall, dist_self, hR.le]))
  rw [polydiscCauchySeries]
  calc
    ‖∑ m : Finset.Nat.antidiagonalTuple d n,
        (multiIndexMonomial (m : Fin d → ℕ)
          (Finset.Nat.mem_antidiagonalTuple.mp m.property)).smulRight
            (polydiscCauchyCoeff f c R m)‖ * r ^ n
        ≤ (∑ m : Finset.Nat.antidiagonalTuple d n,
            ‖(multiIndexMonomial (m : Fin d → ℕ)
              (Finset.Nat.mem_antidiagonalTuple.mp m.property)).smulRight
                (polydiscCauchyCoeff f c R m)‖) * r ^ n := by
          gcongr
          exact norm_sum_le _ _
    _ ≤ (∑ _m : Finset.Nat.antidiagonalTuple d n, M * R⁻¹ ^ n) * r ^ n := by
          gcongr with m
          rw [ContinuousMultilinearMap.norm_smulRight]
          calc
            ‖multiIndexMonomial (m : Fin d → ℕ)
                (Finset.Nat.mem_antidiagonalTuple.mp m.property)‖ *
                  ‖polydiscCauchyCoeff f c R m‖
                ≤ 1 * (M * R⁻¹ ^ (∑ i, (m : Fin d → ℕ) i)) := by
                  gcongr
                  · exact norm_multiIndexMonomial_le _ _
                  · exact norm_polydiscCauchyCoeff_le hR hM _
            _ = M * R⁻¹ ^ n := by
                  rw [Finset.Nat.mem_antidiagonalTuple.mp m.property]
                  ring
      _ = M * ∑ m : Finset.Nat.antidiagonalTuple d n,
          ∏ i, (r * R⁻¹) ^ (m : Fin d → ℕ) i := by
        rw [Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m _
        simp_rw [mul_pow]
        rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
          Finset.prod_pow_eq_pow_sum,
          Finset.Nat.mem_antidiagonalTuple.mp m.property]
        ring

omit [CompleteSpace E] in
private lemma summable_norm_polydiscCauchySeries_mul_pow {d : ℕ}
    {f : (Fin d → ℂ) → E} {c : Fin d → ℂ} {R M r : ℝ} (hR : 0 < R)
    (hr : 0 ≤ r) (hrR : r < R)
    (hM : ∀ z ∈ closedPolydisc c R, ‖f z‖ ≤ M) :
    Summable fun n => ‖polydiscCauchySeries f c R n‖ * r ^ n := by
  have hq0 : 0 ≤ r * R⁻¹ := mul_nonneg hr (inv_nonneg.mpr hR.le)
  have hq1 : r * R⁻¹ < 1 := by
    rw [← div_eq_mul_inv, div_lt_one hR]
    exact hrR
  have hq1norm : ∀ _i : Fin d, ‖(r * R⁻¹ : ℝ)‖ < 1 := fun _ => by
    rw [Real.norm_eq_abs, abs_of_nonneg hq0]
    exact hq1
  have hseries : HasSum (fun n : ℕ =>
      ∑ m ∈ Finset.Nat.antidiagonalTuple d n,
        ∏ i, (r * R⁻¹) ^ (m : Fin d → ℕ) i)
      (∏ _i : Fin d, (1 - r * R⁻¹)⁻¹) :=
    hasSum_antidiagonalTuple_geometric (K := ℝ) (fun _ => r * R⁻¹) hq1norm
  have hgeom : Summable fun n : ℕ =>
      ∑ m : Finset.Nat.antidiagonalTuple d n,
        ∏ i, (r * R⁻¹) ^ (m : Fin d → ℕ) i := by
    exact hseries.summable.congr fun n =>
      (Finset.sum_finset_coe
        (fun m : Fin d → ℕ => ∏ i, (r * R⁻¹) ^ m i)
        (Finset.Nat.antidiagonalTuple d n)).symm
  have hmajor : Summable fun n => M *
      ∑ m : Finset.Nat.antidiagonalTuple d n,
        ∏ i, (r * R⁻¹) ^ (m : Fin d → ℕ) i := hgeom.mul_left M
  refine Summable.of_nonneg_of_le (fun _ => mul_nonneg (norm_nonneg _) (pow_nonneg hr _))
    (norm_polydiscCauchySeries_mul_pow_le hR hr hM) ?_
  exact hmajor

private lemma hasSum_polydiscCauchyKernel {d : ℕ} {z c h : Fin d → ℂ}
    (hz : ∀ i, z i ≠ c i) (hh : ∀ i, ‖h i‖ < ‖z i - c i‖) :
    HasSum (fun n : ℕ => ∑ m : Finset.Nat.antidiagonalTuple d n,
        (∏ i, h i ^ (m : Fin d → ℕ) i) *
          ∏ i, (z i - c i)⁻¹ ^ ((m : Fin d → ℕ) i + 1))
      (∏ i, (z i - (c + h) i)⁻¹) := by
  have hx : ∀ i, ‖h i / (z i - c i)‖ < 1 := by
    intro i
    rw [norm_div, div_lt_one (norm_pos_iff.mpr (sub_ne_zero.mpr (hz i)))]
    exact hh i
  have hs := (hasSum_antidiagonalTuple_geometric
    (fun i => h i / (z i - c i)) hx).mul_right (∏ i, (z i - c i)⁻¹)
  have hterm : (fun n : ℕ => ∑ m : Finset.Nat.antidiagonalTuple d n,
        (∏ i, h i ^ (m : Fin d → ℕ) i) *
          ∏ i, (z i - c i)⁻¹ ^ ((m : Fin d → ℕ) i + 1)) =
      fun n => (∑ m : Finset.Nat.antidiagonalTuple d n,
        ∏ i, (h i / (z i - c i)) ^ (m : Fin d → ℕ) i) *
          ∏ i, (z i - c i)⁻¹ := by
    funext n
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro m _
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [pow_succ, div_pow, inv_pow]
    field_simp [sub_ne_zero.mpr (hz i)]
  have hconst : (∏ i, (z i - (c + h) i)⁻¹) =
      (∏ i, (1 - h i / (z i - c i))⁻¹) * ∏ i, (z i - c i)⁻¹ := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    have hzi : z i - c i ≠ 0 := sub_ne_zero.mpr (hz i)
    have hzih : z i - (c + h) i ≠ 0 := by
      intro heq
      have : z i - c i = h i := by
        calc
          z i - c i = (c + h) i - c i := by rw [sub_eq_zero.mp heq]
          _ = h i := by simp [Pi.add_apply]
      have hi := hh i
      rw [this] at hi
      exact (lt_irrefl _ hi)
    simp only [Pi.add_apply]
    field_simp [hzi, hzih]
    ring
  have hsource : (fun n => (∑ m : Finset.Nat.antidiagonalTuple d n,
        ∏ i, (h i / (z i - c i)) ^ (m : Fin d → ℕ) i) *
          ∏ i, (z i - c i)⁻¹) =
      fun n => (∑ m ∈ Finset.Nat.antidiagonalTuple d n,
        ∏ i, (h i / (z i - c i)) ^ m i) * ∏ i, (z i - c i)⁻¹ := by
    funext n
    exact congrArg (fun v => v * ∏ i, (z i - c i)⁻¹)
      (Finset.sum_finset_coe
        (fun m : Fin d → ℕ => ∏ i, (h i / (z i - c i)) ^ m i)
        (Finset.Nat.antidiagonalTuple d n))
  rw [hterm, hsource, hconst]
  exact hs

omit [CompleteSpace E] in
/-- A uniformly absolutely summable series may be integrated termwise on a torus. -/
lemma hasSum_torusIntegral_of_uniform {d : ℕ} {κ : Type*} [Countable κ]
    {F : κ → (Fin d → ℂ) → E}
    {g : (Fin d → ℂ) → E} {c : Fin d → ℂ} {R : Fin d → ℝ} {a : κ → ℝ}
    (ha : Summable a)
    (hFint : ∀ n, TorusIntegrable (F n) c R)
    (hbound : ∀ n θ, ‖F n (torusMap c R θ)‖ ≤ a n)
    (hsum : ∀ θ, HasSum (fun n => F n (torusMap c R θ)) (g (torusMap c R θ))) :
    HasSum (fun n => torusIntegral (F n) c R) (torusIntegral g c R) := by
  let J : (Fin d → ℝ) → ℂ := fun θ => ∏ i, R i * exp (θ i * I) * I
  have h := MeasureTheory.hasSum_integral_of_dominated_convergence
    (μ := volume.restrict (Icc (0 : Fin d → ℝ) fun _ => 2 * π))
    (F := fun n θ => J θ • F n (torusMap c R θ))
    (f := fun θ => J θ • g (torusMap c R θ))
    (fun n _ => (∏ i, |R i|) * a n)
    (fun n => (hFint n).function_integrable.1)
    (fun n => ae_of_all _ fun θ => by
      rw [norm_smul]
      have hJ : ‖J θ‖ = ∏ i, |R i| := by simp [J]
      rw [hJ]
      exact mul_le_mul_of_nonneg_left (hbound n θ) (by positivity))
    (ae_of_all _ fun _ => (ha.mul_left (∏ i, |R i|)))
    (by
      simp only [tsum_mul_left]
      exact integrableOn_const (hs := measure_Icc_lt_top.ne))
    (ae_of_all _ fun θ => (hsum θ).const_smul (J θ))
  simpa [torusIntegral, J] using h

private noncomputable def polydiscCauchyTerm {d : ℕ} (f : (Fin d → ℂ) → E)
    (c h : Fin d → ℂ) (n : ℕ) (z : Fin d → ℂ) : E :=
  (∑ m : Finset.Nat.antidiagonalTuple d n,
    (∏ i, h i ^ (m : Fin d → ℕ) i) *
      ∏ i, (z i - c i)⁻¹ ^ ((m : Fin d → ℕ) i + 1)) • f z

omit [CompleteSpace E] in
private lemma torusIntegral_fintype_sum {d : ℕ} {α : Type*} [Fintype α]
    {F : α → (Fin d → ℂ) → E} {c : Fin d → ℂ} {R : Fin d → ℝ}
    (hF : ∀ a, TorusIntegrable (F a) c R) :
    torusIntegral (fun z => ∑ a, F a z) c R = ∑ a, torusIntegral (F a) c R := by
  simp only [torusIntegral, Finset.smul_sum]
  exact integral_finsetSum _ fun a _ => (hF a).function_integrable

omit [CompleteSpace E] in
private lemma torusIntegrable_polydiscCauchySummand {d : ℕ}
    {f : (Fin d → ℂ) → E} {c h : Fin d → ℂ} {R : ℝ} (hR : 0 < R)
    (hfc : ContinuousOn f (closedPolydisc c R)) (m : Fin d → ℕ) :
    TorusIntegrable (fun z => ((∏ i, h i ^ m i) *
      ∏ i, (z i - c i)⁻¹ ^ (m i + 1)) • f z) c (fun _ => R) := by
  have hfθ : ContinuousOn (fun θ => f (torusMap c (fun _ => R) θ))
      (Icc (0 : Fin d → ℝ) fun _ => 2 * π) :=
    hfc.comp (continuous_torusMap c R).continuousOn
      (fun θ _ => torusMap_mem_closedPolydisc hR.le θ)
  have hscalar : ContinuousOn (fun θ : Fin d → ℝ =>
      (∏ i, h i ^ m i) *
        ∏ i, (torusMap c (fun _ => R) θ i - c i)⁻¹ ^ (m i + 1))
      (Icc (0 : Fin d → ℝ) fun _ => 2 * π) := by
    refine continuousOn_const.mul (continuousOn_finsetProd _ fun i _ => ?_)
    refine (((((continuous_apply i).comp (continuous_torusMap c R)).continuousOn).sub
      continuousOn_const).inv₀ ?_).pow _
    intro θ _
    apply sub_ne_zero.mpr
    intro heq
    have := torusMap_coord_norm (c := c) hR.le θ i
    have heq' : torusMap c (fun _ => R) θ i = c i := by
      simpa only [Function.comp_apply] using heq
    rw [heq', sub_self, norm_zero] at this
    exact hR.ne' this.symm
  exact (hscalar.smul hfθ).integrableOn_compact isCompact_Icc

omit [CompleteSpace E] in
private lemma torusIntegrable_polydiscCauchyTerm {d n : ℕ}
    {f : (Fin d → ℂ) → E} {c h : Fin d → ℂ} {R : ℝ} (hR : 0 < R)
    (hfc : ContinuousOn f (closedPolydisc c R)) :
    TorusIntegrable (polydiscCauchyTerm f c h n) c (fun _ => R) := by
  have hfθ : ContinuousOn (fun θ => f (torusMap c (fun _ => R) θ))
      (Icc (0 : Fin d → ℝ) fun _ => 2 * π) :=
    hfc.comp (continuous_torusMap c R).continuousOn
      (fun θ _ => torusMap_mem_closedPolydisc hR.le θ)
  have hscalar : ContinuousOn (fun θ : Fin d → ℝ =>
      ∑ m : Finset.Nat.antidiagonalTuple d n,
        (∏ i, h i ^ (m : Fin d → ℕ) i) *
          ∏ i, (torusMap c (fun _ => R) θ i - c i)⁻¹ ^
            ((m : Fin d → ℕ) i + 1))
      (Icc (0 : Fin d → ℝ) fun _ => 2 * π) := by
    refine continuousOn_finsetSum _ fun m _ =>
      continuousOn_const.mul (continuousOn_finsetProd _ fun i _ => ?_)
    refine (((((continuous_apply i).comp (continuous_torusMap c R)).continuousOn).sub
      continuousOn_const).inv₀ ?_).pow _
    intro θ _
    apply sub_ne_zero.mpr
    intro heq
    have := torusMap_coord_norm (c := c) hR.le θ i
    have heq' : torusMap c (fun _ => R) θ i = c i := by
      simpa only [Function.comp_apply] using heq
    rw [heq', sub_self, norm_zero] at this
    exact hR.ne' this.symm
  exact (hscalar.smul hfθ).integrableOn_compact isCompact_Icc

omit [CompleteSpace E] in
private lemma norm_polydiscCauchyTerm_le {d n : ℕ} {f : (Fin d → ℂ) → E}
    {c h : Fin d → ℂ} {R M : ℝ} (hR : 0 < R)
    (hM : ∀ z ∈ closedPolydisc c R, ‖f z‖ ≤ M) (θ : Fin d → ℝ) :
    ‖polydiscCauchyTerm f c h n (torusMap c (fun _ => R) θ)‖ ≤
      (M * R⁻¹ ^ d) * ∑ m : Finset.Nat.antidiagonalTuple d n,
        ∏ i, (‖h i‖ * R⁻¹) ^ (m : Fin d → ℕ) i := by
  have hM0 : 0 ≤ M := (norm_nonneg (f c)).trans (hM c (by
    intro i _
    simp [mem_closedBall, dist_self, hR.le]))
  rw [polydiscCauchyTerm, norm_smul]
  calc
    ‖∑ m : Finset.Nat.antidiagonalTuple d n,
        (∏ i, h i ^ (m : Fin d → ℕ) i) *
          ∏ i, (torusMap c (fun _ => R) θ i - c i)⁻¹ ^
            ((m : Fin d → ℕ) i + 1)‖ *
          ‖f (torusMap c (fun _ => R) θ)‖
        ≤ (∑ m : Finset.Nat.antidiagonalTuple d n,
            ‖(∏ i, h i ^ (m : Fin d → ℕ) i) *
              ∏ i, (torusMap c (fun _ => R) θ i - c i)⁻¹ ^
                ((m : Fin d → ℕ) i + 1)‖) * M := by
          gcongr
          · exact norm_sum_le _ _
          · exact hM _ (torusMap_mem_closedPolydisc hR.le θ)
    _ = (M * R⁻¹ ^ d) * ∑ m : Finset.Nat.antidiagonalTuple d n,
          ∏ i, (‖h i‖ * R⁻¹) ^ (m : Fin d → ℕ) i := by
        rw [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro m _
        simp only [norm_mul, norm_prod, norm_pow, norm_inv,
          torusMap_coord_norm hR.le]
        simp_rw [pow_succ, mul_pow]
        simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
          Fintype.card_fin]
        ring

omit [CompleteSpace E] in
private lemma polydiscCauchySeries_apply_eq_torusIntegral {d n : ℕ}
    {f : (Fin d → ℂ) → E} {c h : Fin d → ℂ} {R : ℝ} (hR : 0 < R)
    (hfc : ContinuousOn f (closedPolydisc c R)) :
    polydiscCauchySeries f c R n (fun _ => h) =
      ((2 * π * I : ℂ) ^ d)⁻¹ •
        torusIntegral (polydiscCauchyTerm f c h n) c (fun _ => R) := by
  let A : ℂ := ((2 * π * I : ℂ) ^ d)⁻¹
  let a : Finset.Nat.antidiagonalTuple d n → ℂ :=
    fun m => ∏ i, h i ^ (m : Fin d → ℕ) i
  let K : Finset.Nat.antidiagonalTuple d n → (Fin d → ℂ) → E :=
    fun m z => (∏ i, (z i - c i)⁻¹ ^ ((m : Fin d → ℕ) i + 1)) • f z
  rw [polydiscCauchySeries_apply]
  simp only [polydiscCauchyCoeff]
  change (∑ m, a m • (A • torusIntegral (K m) c (fun _ => R))) =
    A • torusIntegral (polydiscCauchyTerm f c h n) c (fun _ => R)
  have hInt : ∀ m, TorusIntegrable (fun z => a m • K m z) c (fun _ => R) := by
    intro m
    simpa only [a, K, smul_smul] using
      (torusIntegrable_polydiscCauchySummand (f := f) (c := c) (h := h) hR hfc
        (m : Fin d → ℕ))
  calc
    (∑ m, a m • (A • torusIntegral (K m) c (fun _ => R))) =
        A • ∑ m, a m • torusIntegral (K m) c (fun _ => R) := by
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro m _
      simp only [smul_smul]
      rw [mul_comm]
    _ = A • ∑ m, torusIntegral (fun z => a m • K m z) c (fun _ => R) := by
      congr 1
      apply Finset.sum_congr rfl
      intro m _
      exact (torusIntegral_smul (a m) (K m) c (fun _ => R)).symm
    _ = A • torusIntegral (fun z => ∑ m, a m • K m z) c (fun _ => R) := by
      rw [torusIntegral_fintype_sum hInt]
    _ = A • torusIntegral (polydiscCauchyTerm f c h n) c (fun _ => R) := by
      congr 2
      funext z
      rw [polydiscCauchyTerm, Finset.sum_smul]
      apply Finset.sum_congr rfl
      intro m _
      simp only [a, K, smul_smul]

omit [CompleteSpace E] in
private lemma hasSum_polydiscCauchySeries_integral {d : ℕ}
    {f : (Fin d → ℂ) → E} {c h : Fin d → ℂ} {R M : ℝ} (hR : 0 < R)
    (hh : ∀ i, ‖h i‖ < R) (hfc : ContinuousOn f (closedPolydisc c R))
    (hM : ∀ z ∈ closedPolydisc c R, ‖f z‖ ≤ M) :
    HasSum (fun n => polydiscCauchySeries f c R n (fun _ => h))
      (((2 * π * I : ℂ) ^ d)⁻¹ • torusIntegral
        (fun z => (∏ i, (z i - (c + h) i)⁻¹) • f z) c (fun _ => R)) := by
  let q : Fin d → ℝ := fun i => ‖h i‖ * R⁻¹
  let a : ℕ → ℝ := fun n => (M * R⁻¹ ^ d) *
    ∑ m : Finset.Nat.antidiagonalTuple d n,
      ∏ i, q i ^ (m : Fin d → ℕ) i
  have hq0 : ∀ i, 0 ≤ q i := fun i => mul_nonneg (norm_nonneg _) (inv_nonneg.mpr hR.le)
  have hq1 : ∀ i, ‖q i‖ < 1 := by
    intro i
    rw [Real.norm_eq_abs, abs_of_nonneg (hq0 i)]
    simp only [q]
    rw [← div_eq_mul_inv, div_lt_one hR]
    exact hh i
  have hgeom : Summable fun n =>
      ∑ m : Finset.Nat.antidiagonalTuple d n,
        ∏ i, q i ^ (m : Fin d → ℕ) i := by
    exact (hasSum_antidiagonalTuple_geometric q hq1).summable.congr fun n =>
      (Finset.sum_finset_coe
        (fun m : Fin d → ℕ => ∏ i, q i ^ m i)
        (Finset.Nat.antidiagonalTuple d n)).symm
  have ha : Summable a := by
    change Summable fun n => (M * R⁻¹ ^ d) *
      ∑ m : Finset.Nat.antidiagonalTuple d n,
        ∏ i, q i ^ (m : Fin d → ℕ) i
    exact hgeom.mul_left (M * R⁻¹ ^ d)
  have ht := hasSum_torusIntegral_of_uniform (E := E)
    (g := fun z => (∏ i, (z i - (c + h) i)⁻¹) • f z) ha
    (fun n => torusIntegrable_polydiscCauchyTerm hR hfc)
    (fun n θ => by
      simpa [a, q] using norm_polydiscCauchyTerm_le hR hM θ)
    (fun θ => by
      have hz : ∀ i, torusMap c (fun _ => R) θ i ≠ c i := by
        intro i heq
        have := torusMap_coord_norm (c := c) hR.le θ i
        rw [heq, sub_self, norm_zero] at this
        exact hR.ne' this.symm
      have hk := hasSum_polydiscCauchyKernel
        (z := torusMap c (fun _ => R) θ) (c := c) (h := h) hz (fun i => by
          rw [torusMap_coord_norm (c := c) hR.le θ i]
          exact hh i)
      simpa [polydiscCauchyTerm] using
        hk.smul_const (f (torusMap c (fun _ => R) θ)))
  have hs := ht.const_smul (((2 * π * I : ℂ) ^ d)⁻¹)
  simpa only [polydiscCauchySeries_apply_eq_torusIntegral hR hfc] using hs

/-- The Cauchy series converges to the function at every point of the open polydisc. -/
theorem hasSum_polydiscCauchySeries {d : ℕ}
    {f : (Fin d → ℂ) → E} {c h : Fin d → ℂ} {R M : ℝ} (hR : 0 < R)
    (hh : ∀ i, ‖h i‖ < R) (hfc : ContinuousOn f (closedPolydisc c R))
    (hfa : ∀ z ∈ closedPolydisc c R, ∀ i,
      AnalyticAt ℂ (fun x => f (update z i x)) (z i))
    (hM : ∀ z ∈ closedPolydisc c R, ‖f z‖ ≤ M) :
    HasSum (fun n => polydiscCauchySeries f c R n (fun _ => h)) (f (c + h)) := by
  have H := hasSum_polydiscCauchySeries_integral hR hh hfc hM
  rwa [polydisc_cauchy hR (fun i => by simpa using hh i) hfc hfa] at H

/-- The Cauchy series represents the function on the full open supremum-norm ball,
not just the half-radius ball needed by the original Osgood proof. -/
theorem hasFPowerSeriesOnBall_polydiscCauchy_full {d : ℕ}
    {f : (Fin d → ℂ) → E} {c : Fin d → ℂ} {R M : ℝ} (hR : 0 < R)
    (hfc : ContinuousOn f (closedPolydisc c R))
    (hfa : ∀ z ∈ closedPolydisc c R, ∀ i,
      AnalyticAt ℂ (fun x => f (update z i x)) (z i))
    (hM : ∀ z ∈ closedPolydisc c R, ‖f z‖ ≤ M) :
    HasFPowerSeriesOnBall f (polydiscCauchySeries f c R) c (ENNReal.ofReal R) := by
  refine ⟨?_, ENNReal.ofReal_pos.mpr hR, ?_⟩
  · apply le_of_forall_lt_imp_le_of_dense
    intro q hq
    have hqtop : q ≠ ⊤ := ne_top_of_lt hq
    have hqR : (q.toNNReal : ℝ) < R := by
      have H := (ENNReal.toReal_lt_toReal hqtop ENNReal.ofReal_ne_top).mpr hq
      simpa [ENNReal.toReal_ofReal hR.le, ENNReal.coe_toNNReal_eq_toReal] using H
    simpa [ENNReal.coe_toNNReal hqtop] using
      (polydiscCauchySeries f c R).le_radius_of_summable_norm
        (summable_norm_polydiscCauchySeries_mul_pow hR q.toNNReal.coe_nonneg hqR hM)
  · intro h hh
    let r : ℝ≥0 := ⟨R, hR.le⟩
    have hr : (r : ℝ≥0∞) = ENNReal.ofReal R := by
      rw [ENNReal.coe_nnreal_eq]
      rfl
    rw [← hr, Metric.mem_eball, edist_eq_enorm_sub, sub_zero, enorm_lt_coe] at hh
    exact hasSum_polydiscCauchySeries hR
      (fun i => (norm_le_pi_norm h i).trans_lt hh) hfc hfa hM

/-- A continuous, separately analytic function on a closed polydisc is represented on the
concentric polydisc of half the radius by its multivariable Cauchy series. -/
theorem hasFPowerSeriesOnBall_polydiscCauchy {d : ℕ}
    {f : (Fin d → ℂ) → E} {c : Fin d → ℂ} {R M : ℝ} (hR : 0 < R)
    (hfc : ContinuousOn f (closedPolydisc c R))
    (hfa : ∀ z ∈ closedPolydisc c R, ∀ i,
      AnalyticAt ℂ (fun x => f (update z i x)) (z i))
    (hM : ∀ z ∈ closedPolydisc c R, ‖f z‖ ≤ M) :
    HasFPowerSeriesOnBall f (polydiscCauchySeries f c R) c
      (ENNReal.ofReal (R / 2)) := by
  exact (hasFPowerSeriesOnBall_polydiscCauchy_full hR hfc hfa hM).mono
    (ENNReal.ofReal_pos.mpr (by positivity))
    (ENNReal.ofReal_le_ofReal (by linarith))

/-- On the diagonal, the Cauchy series is the usual Taylor series of iterated Fréchet
derivatives. This uses Mathlib's general coefficient theorem, not a new derivative theory. -/
theorem polydiscCauchySeries_diag_eq_iteratedFDeriv {d : ℕ}
    {f : (Fin d → ℂ) → E} {c : Fin d → ℂ} {R M : ℝ} (hR : 0 < R)
    (hfc : ContinuousOn f (closedPolydisc c R))
    (hfa : ∀ z ∈ closedPolydisc c R, ∀ i,
      AnalyticAt ℂ (fun x => f (update z i x)) (z i))
    (hM : ∀ z ∈ closedPolydisc c R, ‖f z‖ ≤ M) (n : ℕ) (v : Fin d → ℂ) :
    polydiscCauchySeries f c R n (fun _ => v) =
      (n.factorial : ℂ)⁻¹ • iteratedFDeriv ℂ n f c (fun _ => v) := by
  have h := hasFPowerSeriesOnBall_polydiscCauchy_full hR hfc hfa hM
  rw [← h.factorial_smul v n, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr n.factorial_ne_zero), one_smul]

end SeveralComplexVariables

end
