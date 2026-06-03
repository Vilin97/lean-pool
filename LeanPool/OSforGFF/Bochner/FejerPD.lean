/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/


import LeanPool.OSforGFF.Bochner.PositiveDefinite
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Fourier transform of L¹ positive-definite functions is nonneg

We prove: for φ : V → ℂ continuous, integrable, and positive-definite on a
finite-dimensional real inner product space V, Re(𝓕φ(ξ)) ≥ 0 for all ξ.

## Proof strategy

For fixed ξ, note that ψ(x) = φ(x) · exp(-2πi⟨x,ξ⟩) is PD (Schur product of
φ and the PD function exp(2πi⟨·,-ξ⟩)), continuous, and integrable with
𝓕φ(ξ) = ∫ ψ. So it suffices to show Re(∫ ψ) ≥ 0 for any PD continuous L¹ ψ.

For R > 0, define J_R = (1/μ(B_R)) ∫∫_{B_R × B_R} ψ(x-y) dx dy.

**Step A**: Re(J_R) ≥ 0 because the double integral is approximated by
PD double sums (Riemann sums on V × V with PD structure).

**Step B**: By Fubini, J_R = ∫ ψ(v) · [μ(B_R ∩ (v+B_R))/μ(B_R)] dv.
The kernel → 1 pointwise and is bounded by 1, so DCT gives J_R → ∫ ψ.

**Step C**: ge_of_tendsto' gives Re(∫ ψ) ≥ 0.

## References

- Rudin, *Fourier Analysis on Groups*, Theorem 1.4.3
- Folland, *A Course in Abstract Harmonic Analysis*, §4.2, Lemma 4.8
-/

open MeasureTheory Complex Filter Topology BigOperators
open scoped Real FourierTransform InnerProductSpace

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-! ### Helper: exp(2πi⟨·,ξ⟩) is positive definite -/

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The exponential character x ↦ exp(2πi⟨x,ξ⟩) is positive definite.
    The PD sum equals |∑ cₖ exp(2πi⟨xₖ,ξ⟩)|².
-/
private lemma isPositiveDefinite_exp_inner (ξ : V) :
    IsPositiveDefinite (fun x : V => cexp (2 * ↑π * ↑⟪x, ξ⟫_ℝ * I)) where
  hermitian x := by
    rw [starRingEnd_apply, star_def, ← Complex.exp_conj]
    congr 1
    have : (starRingEnd ℂ) (2 * ↑π * ↑⟪x, ξ⟫_ℝ * I) = 2 * ↑π * ↑⟪x, ξ⟫_ℝ * (-I) := by
      simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
    rw [this, inner_neg_left, Complex.ofReal_neg]; ring
  nonneg m x c := by
    -- Show the sum equals |∑ cₖ exp(2πi⟨xₖ,ξ⟩)|² ≥ 0
    -- Use e_k = exp(-2πi⟨x_k,ξ⟩) so that conj(e_i)*e_j = exp(2πi⟨x_i-x_j,ξ⟩)
    set e := fun k : Fin m => cexp (-(2 * ↑π * ↑⟪x k, ξ⟫_ℝ * I))
    have halg : ∀ i j : Fin m,
        (starRingEnd ℂ) (c i) * c j * cexp (2 * ↑π * ↑⟪x i - x j, ξ⟫_ℝ * I) =
        (starRingEnd ℂ) (c i * e i) * (c j * e j) := by
      intro i j
      have : cexp (2 * ↑π * ↑⟪x i - x j, ξ⟫_ℝ * I) =
          (starRingEnd ℂ) (e i) * e j := by
        rw [← Complex.exp_conj, ← Complex.exp_add]
        congr 1
        simp only [map_neg, map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
        rw [inner_sub_left, Complex.ofReal_sub]
        ring
      rw [this, map_mul, mul_mul_mul_comm]
    simp_rw [halg]
    -- Now sum = ∑ᵢ∑ⱼ conj(dᵢ)dⱼ = |∑ dₖ|² where dₖ = cₖeₖ
    set d := fun k => c k * e k
    rw [show ∑ i, ∑ j, (starRingEnd ℂ) (d i) * d j =
        (starRingEnd ℂ) (∑ k, d k) * ∑ k, d k from by
      rw [map_sum, Finset.sum_mul_sum]]
    rw [starRingEnd_apply, star_def, ← Complex.normSq_eq_conj_mul_self]
    simp [Complex.normSq_nonneg]

/-! ### Haar measure neg-invariance -/

/-- Volume on a finite-dimensional inner product space is neg-invariant.
    Proof: negation is a linear isometry equiv, which preserves addHaar measure.
-/
instance volumeIsNegInvariant : (volume : Measure V).IsNegInvariant := by
  constructor; exact ((LinearIsometryEquiv.neg ℝ (E := V)).measurePreserving).map_eq

/-- Haar translation: ∫ f(a - x) dx = ∫ f(x) dx. -/
private lemma integral_sub_left_eq (f : V → ℂ) (a : V) :
    ∫ x, f (a - x) = ∫ x, f x := by
  simp_rw [sub_eq_add_neg]
  have h1 : ∫ x : V, f (a + -x) = ∫ x : V, f (a + x) :=
    integral_neg_eq_self (fun y : V => f (a + y)) volume
  rw [h1]; exact integral_add_left_eq_self f a

/-! ### Step A: The PD double integral has nonneg real part -/

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [BorelSpace V] in
open Classical in
/-- For a simple function sₙ : V → V and any g : V → ℂ,
    ∫ g(sₙ x) dμ = ∑ u ∈ sₙ.range, μ(sₙ⁻¹'{u}).toReal • g u.
-/
private lemma integral_simpleFunc_comp (sn : SimpleFunc V V) (g : V → ℂ)
    (μ : Measure V) [IsFiniteMeasure μ] :
    ∫ x, g (sn x) ∂μ = ∑ u ∈ sn.range, (μ (⇑sn ⁻¹' {u})).toReal • g u := by
  have hpw : ∀ x, g (sn x) =
      ∑ u ∈ sn.range, (⇑sn ⁻¹' {u}).indicator (fun _ => g u) x := by
    intro x
    simp only [Set.indicator, Set.mem_preimage, Set.mem_singleton_iff]
    simp_rw [eq_comm (a := sn x)]
    rw [Finset.sum_ite_eq' sn.range (sn x) (fun u => g u)]; simp
  simp_rw [hpw]
  rw [integral_finsetSum _ (fun u _ => (integrable_const _).indicator
    (sn.measurableSet_preimage _))]
  congr 1; ext u
  rw [integral_indicator (sn.measurableSet_preimage _), setIntegral_const]; rfl

/-- The double integral of a PD function over S × S has nonneg real part.
    Proof: Approximate id : V → V by simple functions sₙ. For each sₙ, the double
    integral ∫∫ ψ(sₙ(x)-sₙ(y)) dμ dμ expands as ∑ᵢⱼ μ(Aᵢ)μ(Aⱼ)ψ(uᵢ-uⱼ),
    a PD double sum with real coefficients, so Re ≥ 0. The sums converge to
    ∫∫ ψ(x-y) dμ dμ by DCT, so Re ≥ 0 passes to the limit.
    See Rudin, *Fourier Analysis on Groups*, proof of Theorem 1.4.3, step 1.
-/
private lemma pd_double_integral_re_nonneg (ψ : V → ℂ) (hpd : IsPositiveDefinite ψ)
    (hcont : Continuous ψ) (S : Set V) (_hSmeas : MeasurableSet S)
    (hSbdd : Bornology.IsBounded S) :
    0 ≤ (∫ x in S, ∫ y in S, ψ (x - y)).re := by
  let μ := (volume : Measure V).restrict S
  -- 1. Approximate id by simple functions, show double integral converges
  have h_approx : ∃ (s : ℕ → SimpleFunc V V),
      Filter.Tendsto (fun n => ∫ x, ∫ y, ψ (s n x - s n y) ∂μ ∂μ)
        Filter.atTop (nhds (∫ x, ∫ y, ψ (x - y) ∂μ ∂μ)) := by
    -- Simple functions approximating id : V → V
    have hid : StronglyMeasurable (id : V → V) := stronglyMeasurable_id
    refine ⟨hid.approx, ?_⟩
    have h_ptwise : ∀ x, Filter.Tendsto (fun n => hid.approx n x) Filter.atTop (nhds x) :=
      fun x => by simpa using hid.tendsto_approx x
    -- Uniform bound from PD condition: ‖ψ(z)‖ ≤ (ψ 0).re for all z
    have hbound : ∀ z, ‖ψ z‖ ≤ (ψ 0).re := hpd.bounded_by_zero
    have hfm : IsFiniteMeasure μ :=
      ⟨by simpa [μ] using hSbdd.measure_lt_top⟩
    -- Inner integral converges for each x via DCT
    have h_inner_conv : ∀ x, Filter.Tendsto
        (fun n => ∫ y, ψ (hid.approx n x - hid.approx n y) ∂μ)
        Filter.atTop (nhds (∫ y, ψ (x - y) ∂μ)) := by
      intro x
      have hmeas : ∀ n, AEStronglyMeasurable
          (fun y => ψ (hid.approx n x - hid.approx n y)) μ := by
        intro n
        have hsf : (fun y => ψ (hid.approx n x - hid.approx n y)) =
            ⇑((hid.approx n).map (fun v => ψ (hid.approx n x - v))) := by
          ext y; simp [SimpleFunc.map_apply]
        rw [hsf]; exact (SimpleFunc.map _ _).aestronglyMeasurable
      have hbd : ∀ n, ∀ᵐ y ∂μ, ‖ψ (hid.approx n x - hid.approx n y)‖ ≤ (ψ 0).re :=
        fun n => ae_of_all _ (fun y => hbound _)
      have hlim : ∀ᵐ y ∂μ, Filter.Tendsto
          (fun n => ψ (hid.approx n x - hid.approx n y))
          Filter.atTop (nhds (ψ (x - y))) :=
        ae_of_all _ (fun y =>
          (hcont.continuousAt.tendsto.comp ((h_ptwise x).sub (h_ptwise y))))
      exact tendsto_integral_of_dominated_convergence
        (fun _ => (ψ 0).re) hmeas (integrable_const _) hbd hlim
    -- Outer integral converges via DCT
    have hmeas2 : ∀ n, AEStronglyMeasurable
        (fun x => ∫ y, ψ (hid.approx n x - hid.approx n y) ∂μ) μ := by
      intro n
      have hsf : (fun x => ∫ y, ψ (hid.approx n x - hid.approx n y) ∂μ) =
          ⇑((hid.approx n).map
            (fun u => ∫ y, ψ (u - hid.approx n y) ∂μ)) := by
        ext x; simp [SimpleFunc.map_apply]
      rw [hsf]; exact (SimpleFunc.map _ _).aestronglyMeasurable
    have hbd2 : ∀ n, ∀ᵐ x ∂μ,
        ‖∫ y, ψ (hid.approx n x - hid.approx n y) ∂μ‖ ≤
          (ψ 0).re * (μ Set.univ).toReal := by
      intro n; exact ae_of_all _ (fun x => by
        calc ‖∫ y, ψ (hid.approx n x - hid.approx n y) ∂μ‖
            ≤ ∫ y, ‖ψ (hid.approx n x - hid.approx n y)‖ ∂μ :=
              norm_integral_le_integral_norm _
          _ ≤ ∫ _, (ψ 0).re ∂μ :=
              integral_mono_of_nonneg (ae_of_all _ (fun _ => norm_nonneg _))
                (integrable_const _) (ae_of_all _ (fun _ => hbound _))
          _ = (ψ 0).re * (μ Set.univ).toReal := by
              rw [integral_const, smul_eq_mul, mul_comm]; rfl)
    exact tendsto_integral_of_dominated_convergence
      (fun _ => (ψ 0).re * (μ Set.univ).toReal)
      hmeas2 (integrable_const _) hbd2 (ae_of_all _ h_inner_conv)
  rcases h_approx with ⟨s, hs_tendsto⟩
  -- 2. For any simple function, double integral expands to PD sum with Re ≥ 0
  have h_sum : ∀ n, 0 ≤ (∫ x, ∫ y, ψ (s n x - s n y) ∂μ ∂μ).re := by
    intro n
    let sn := s n
    let R := sn.range
    have hfm : IsFiniteMeasure μ :=
      ⟨by simpa [μ] using hSbdd.measure_lt_top⟩
    have h_double_integral : (∫ x, ∫ y, ψ (sn x - sn y) ∂μ ∂μ) =
        ∑ u ∈ R, ∑ v ∈ R,
          ((μ (sn ⁻¹' {u})).toReal : ℂ) *
          ((μ (sn ⁻¹' {v})).toReal : ℂ) * ψ (u - v) := by
      -- Inner integral: ∫ y, ψ(sn x - sn y) dμ = ∑ v, μ(sn⁻¹'{v}).toReal • ψ(sn x - v)
      have h_inner : ∀ x, ∫ y, ψ (sn x - sn y) ∂μ =
          ∑ v ∈ R, (μ (⇑sn ⁻¹' {v})).toReal • ψ (sn x - v) :=
        fun x => integral_simpleFunc_comp sn (fun v => ψ (sn x - v)) μ
      simp_rw [h_inner, Complex.real_smul]
      -- Swap integral and finite sum
      rw [integral_finsetSum _ (fun v _ => ?_)]
      · -- Expand outer integral via integral_simpleFunc_comp
        have h_expand : ∀ v, ∫ a, (↑(μ (⇑sn ⁻¹' {v})).toReal : ℂ) * ψ (sn a - v) ∂μ =
            ∑ u ∈ R, (μ (⇑sn ⁻¹' {u})).toReal •
              ((↑(μ (⇑sn ⁻¹' {v})).toReal : ℂ) * ψ (u - v)) := fun v =>
          integral_simpleFunc_comp sn
            (fun w => (↑(μ (⇑sn ⁻¹' {v})).toReal : ℂ) * ψ (w - v)) μ
        simp_rw [h_expand]
        -- Swap sum order: ∑ v, ∑ u, ... = ∑ u, ∑ v, ...
        rw [Finset.sum_comm]
        -- Now match summands pointwise
        congr 1; ext u; congr 1; ext v
        rw [Complex.real_smul]
        ring
      · -- c * ψ(sn · - v) is integrable on finite measure
        refine Integrable.const_mul ?_ _
        -- ψ(sn · - v) = (sn.map (ψ(· - v))) which is a simple function, hence integrable
        have hsf : (fun x => ψ (sn x - v)) = ⇑(sn.map (fun u => ψ (u - v))) := by
          ext x; simp [SimpleFunc.map_apply]
        rw [hsf]
        exact SimpleFunc.integrable_of_isFiniteMeasure _
    rw [h_double_integral]
    -- Reindex the Finset sum to Fin m
    let m := R.card
    have ⟨e, _⟩ : ∃ e : Fin m ≃ R, True := ⟨R.equivFin.symm, trivial⟩
    have h_reindex : (∑ u ∈ R, ∑ v ∈ R,
        ((μ (sn ⁻¹' {u})).toReal : ℂ) *
        ((μ (sn ⁻¹' {v})).toReal : ℂ) * ψ (u - v)) =
      ∑ i : Fin m, ∑ j : Fin m,
        ((μ (sn ⁻¹' {(e i : V)})).toReal : ℂ) *
        ((μ (sn ⁻¹' {(e j : V)})).toReal : ℂ) * ψ ((e i : V) - (e j : V)) := by
      rw [← Finset.sum_coe_sort R]
      exact Fintype.sum_equiv e.symm _ _ (fun i => by
        rw [← Finset.sum_coe_sort R]
        exact Fintype.sum_equiv e.symm _ _ (fun j => by simp))
    rw [h_reindex]
    -- Apply PD condition
    let c : Fin m → ℂ := fun i => ((μ (sn ⁻¹' {(e i : V)})).toReal : ℂ)
    let x_pts : Fin m → V := fun i => (e i : V)
    have hpd_eval := hpd.nonneg m x_pts c
    -- Measures are real, so conj = id
    have hpd_match : (∑ i : Fin m, ∑ j : Fin m,
        starRingEnd ℂ (c i) * c j * ψ (x_pts i - x_pts j)) =
      ∑ i : Fin m, ∑ j : Fin m, c i * c j * ψ (x_pts i - x_pts j) := by
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      change (starRingEnd ℂ) (((μ (sn ⁻¹' {(e i : V)})).toReal : ℂ)) * _ * _ = _
      rw [starRingEnd_apply, star_def, Complex.conj_ofReal]
    rwa [hpd_match] at hpd_eval
  -- 3. Pass to the limit
  have h_re_tendsto : Filter.Tendsto
      (fun n => (∫ x, ∫ y, ψ (s n x - s n y) ∂μ ∂μ).re)
      Filter.atTop (nhds (∫ x, ∫ y, ψ (x - y) ∂μ ∂μ).re) :=
    (Complex.continuous_re.tendsto _).comp hs_tendsto
  exact ge_of_tendsto' h_re_tendsto h_sum

/-! ### Integral of PD function has nonneg real part -/

/-- The overlap ratio vol(B_R ∩ B_R(v)) / vol(B_R) for the Fejér average. -/
private def overlapRatio (R : ℝ) (v : V) : ℝ :=
  if (volume (Metric.closedBall (0 : V) R)).toReal = 0 then 0
  else (volume (Metric.closedBall (0 : V) R ∩ Metric.closedBall v R)).toReal /
       (volume (Metric.closedBall (0 : V) R)).toReal

/-- The overlap ratio is between 0 and 1. -/
private lemma overlapRatio_le_one (R : ℝ) (v : V) : overlapRatio R v ≤ 1 := by
  unfold overlapRatio; split_ifs with h
  · exact zero_le_one
  · exact div_le_one_of_le₀
      (ENNReal.toReal_mono (ne_of_lt measure_closedBall_lt_top)
        (measure_mono Set.inter_subset_left))
      ENNReal.toReal_nonneg

/-- The overlap ratio is nonneg. -/
private lemma overlapRatio_nonneg (R : ℝ) (v : V) : 0 ≤ overlapRatio R v := by
  unfold overlapRatio; split_ifs
  · exact le_refl 0
  · exact div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg

/-- The overlap ratio is measurable as a function of v. -/
private lemma measurable_overlapRatio (R : ℝ) : Measurable (overlapRatio R : V → ℝ) := by
  unfold overlapRatio
  split_ifs with h
  · exact measurable_const
  · apply Measurable.div_const
    let E := {p : V × V | p.2 ∈ Metric.closedBall (0 : V) R ∧ dist p.2 p.1 ≤ R}
    have hE : MeasurableSet E :=
      .inter (measurableSet_closedBall.preimage measurable_snd)
        ((isClosed_le (continuous_snd.dist continuous_fst) continuous_const).measurableSet)
    have hfib : ∀ v : V, Prod.mk v ⁻¹' E =
        Metric.closedBall (0 : V) R ∩ Metric.closedBall v R := by
      intro v; ext x; simp [E, Metric.mem_closedBall, Set.mem_inter_iff, dist_comm x v]
    change Measurable fun v => (volume (Metric.closedBall (0 : V) R ∩
        Metric.closedBall v R)).toReal
    simp_rw [← hfib]
    exact (measurable_measure_prodMk_left hE (ν := volume)).ennreal_toReal

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- Ball containment: closedBall 0 (R - ‖v‖) ⊆ closedBall 0 R ∩ closedBall v R. -/
private lemma closedBall_sub_norm_subset (v : V) (R : ℝ) :
    Metric.closedBall (0 : V) (R - ‖v‖) ⊆
    Metric.closedBall (0 : V) R ∩ Metric.closedBall v R := by
  intro x hx
  simp only [Metric.mem_closedBall, dist_zero_right] at hx
  constructor
  · exact Metric.mem_closedBall.mpr (by rw [dist_zero_right]; linarith [norm_nonneg v])
  · refine Metric.mem_closedBall.mpr ?_
    have h1 : dist x v ≤ dist x 0 + dist 0 v := dist_triangle x 0 v
    simp only [dist_zero_right, dist_zero_left] at h1
    linarith

/-- The overlap ratio → 1 as R → ∞ for fixed v.
    Proof: closedBall 0 (R-‖v‖) ⊆ closedBall 0 R ∩ closedBall v R, so
    overlapRatio ≥ ((R-‖v‖)/R)^d → 1. Upper bound is 1. Squeeze.
-/
private lemma overlapRatio_tendsto_one (v : V) :
    Filter.Tendsto (fun n : ℕ => overlapRatio (n : ℝ) v) Filter.atTop (nhds 1) := by
  -- Use squeeze: lower bound → 1, upper bound = 1
  set d := Module.finrank ℝ V
  apply Filter.Tendsto.squeeze'
    -- lower bound: ((n - ‖v‖) / n) ^ d → 1
    (show Filter.Tendsto (fun n : ℕ =>
        ((↑n - ‖v‖) / ↑n) ^ d) Filter.atTop (nhds 1) by
      have h : Filter.Tendsto (fun n : ℕ => (↑n - ‖v‖) / (↑n : ℝ)) Filter.atTop (nhds 1) := by
        have h1 : ∀ᶠ n : ℕ in Filter.atTop, (↑n - ‖v‖) / (↑n : ℝ) = 1 - ‖v‖ / ↑n := by
          filter_upwards [Filter.eventually_gt_atTop 0] with n hn; field_simp
        have hc : Filter.Tendsto (fun n : ℕ => ‖v‖ / (↑n : ℝ)) Filter.atTop (nhds 0) :=
          tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
        exact Tendsto.congr' (EventuallyEq.symm h1)
          (by simpa using Tendsto.sub tendsto_const_nhds hc)
      simpa using h.pow (n := d))
    -- upper bound: constant 1
    tendsto_const_nhds
    -- overlapRatio ≥ lower bound: closedBall 0 (n-‖v‖) ⊆ intersection,
    -- so ratio ≥ vol(B_{n-‖v‖})/vol(B_n) = ((n-‖v‖)/n)^d by Haar formula
    (by filter_upwards [Filter.eventually_gt_atTop (⌈‖v‖⌉₊)] with n hn
        have hn_gt : ‖v‖ < (n : ℝ) :=
          lt_of_le_of_lt (Nat.le_ceil _) (Nat.cast_lt.mpr hn)
        have hn_pos : (0 : ℝ) < n := by linarith [norm_nonneg v]
        have hsub_nn : (0 : ℝ) ≤ ↑n - ‖v‖ := by linarith
        have hvol_pos := Metric.measure_closedBall_pos (volume : Measure V) 0 hn_pos
        have hvol_ne_top : volume (Metric.closedBall (0 : V) (↑n)) ≠ ⊤ :=
          ne_of_lt measure_closedBall_lt_top
        have hvol_toReal_pos : 0 < (volume (Metric.closedBall (0 : V) (↑n))).toReal :=
          ENNReal.toReal_pos (ne_of_gt hvol_pos) hvol_ne_top
        unfold overlapRatio; rw [if_neg (ne_of_gt hvol_toReal_pos)]
        have hball_pos : 0 < (volume (Metric.ball (0 : V) 1)).toReal :=
          ENNReal.toReal_pos (ne_of_gt (Metric.measure_ball_pos volume 0 one_pos))
            (ne_of_lt measure_ball_lt_top)
        have hvol_sub : (volume (Metric.closedBall (0 : V) (↑n - ‖v‖))).toReal =
            (↑n - ‖v‖) ^ d * (volume (Metric.ball (0 : V) 1)).toReal := by
          rw [Measure.addHaar_closedBall volume (0 : V) hsub_nn, ENNReal.toReal_mul,
              ENNReal.toReal_ofReal (by positivity)]
        have hvol_n : (volume (Metric.closedBall (0 : V) (↑n))).toReal =
            (↑n) ^ d * (volume (Metric.ball (0 : V) 1)).toReal := by
          rw [Measure.addHaar_closedBall volume (0 : V) hn_pos.le, ENNReal.toReal_mul,
              ENNReal.toReal_ofReal (by positivity)]
        calc ((↑n - ‖v‖) / ↑n) ^ d
            = (↑n - ‖v‖) ^ d / (↑n) ^ d := by rw [div_pow]
          _ = ((↑n - ‖v‖) ^ d * (volume (Metric.ball (0 : V) 1)).toReal) /
              ((↑n) ^ d * (volume (Metric.ball (0 : V) 1)).toReal) := by
              rw [mul_div_mul_right _ _ (ne_of_gt hball_pos)]
          _ = (volume (Metric.closedBall (0 : V) (↑n - ‖v‖))).toReal /
              (volume (Metric.closedBall (0 : V) (↑n))).toReal := by
              rw [hvol_sub, hvol_n]
          _ ≤ (volume (Metric.closedBall (0 : V) (↑n) ∩ Metric.closedBall v (↑n))).toReal /
              (volume (Metric.closedBall (0 : V) (↑n))).toReal := by
              exact div_le_div_of_nonneg_right
                (ENNReal.toReal_mono
                  (ne_of_lt (lt_of_le_of_lt (measure_mono Set.inter_subset_left)
                    measure_closedBall_lt_top))
                  (measure_mono (closedBall_sub_norm_subset v ↑n)))
                hvol_toReal_pos.le)
    -- overlapRatio ≤ 1 (always)
    (Filter.Eventually.of_forall (fun n => overlapRatio_le_one (n : ℝ) v))

/-- Inner integral substitution via Haar invariance:
    ∫ y in closedBall 0 R, ψ(x-y) = ∫ v in closedBall x R, ψ(v).
-/
private lemma inner_integral_sub (ψ : V → ℂ) (x : V) (R : ℝ) :
    ∫ y in Metric.closedBall (0 : V) R, ψ (x - y) =
    ∫ v in Metric.closedBall x R, ψ v := by
  rw [← integral_indicator measurableSet_closedBall,
      ← integral_indicator measurableSet_closedBall]
  have hind : ∀ y : V, (Metric.closedBall (0 : V) R).indicator (fun y => ψ (x - y)) y =
      (Metric.closedBall x R).indicator ψ (x - y) := by
    intro y
    simp only [Set.indicator, Metric.mem_closedBall]
    have : dist (x - y) x = dist y 0 := by simp [dist_eq_norm]
    rw [this]
  simp_rw [hind]
  simp_rw [sub_eq_add_neg]
  have h1 : ∫ y : V, (Metric.closedBall x R).indicator ψ (x + -y) =
      ∫ y : V, (Metric.closedBall x R).indicator ψ (x + y) :=
    integral_neg_eq_self (fun y : V => (Metric.closedBall x R).indicator ψ (x + y)) volume
  rw [h1]
  exact integral_add_left_eq_self ((Metric.closedBall x R).indicator ψ) x

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- Indicator equivalence: for x ∈ B and the intersection set B ∩ closedBall v R,
    the nested indicators agree. Uses dist_comm to convert v ∈ closedBall x R
    to x ∈ closedBall v R.
-/
private lemma indicator_closedBall_inter (ψ : V → ℂ) (R : ℝ) (x v : V) :
    (Metric.closedBall (0 : V) R).indicator
      (fun x => (Metric.closedBall x R).indicator ψ v) x =
    (Metric.closedBall (0 : V) R ∩ Metric.closedBall v R).indicator
      (fun _ => ψ v) x := by
  simp only [Set.indicator, Metric.mem_closedBall, Set.mem_inter_iff, dist_comm v x]
  split_ifs <;> first | rfl | (exfalso; tauto)

/-- The integrand (B ∩ closedBall v R).indicator is integrable on V × V.
    Rewrite as indicator of the compact product set S = {(x,v) | x ∈ B, dist x v ≤ R}
    applied to the continuous function ψ ∘ snd.
-/
private lemma integrable_indicator_prod (ψ : V → ℂ) (hcont : Continuous ψ)
    (_hint : Integrable ψ) (R : ℝ) :
    Integrable (Function.uncurry fun x v =>
      (Metric.closedBall (0 : V) R ∩ Metric.closedBall v R).indicator
        (fun _ => ψ v) x)
      (Measure.prod volume volume) := by
  -- Rewrite as indicator on product set S = {(x,v) | x ∈ B, dist x v ≤ R}
  set S := {p : V × V | p.1 ∈ Metric.closedBall (0 : V) R ∧ dist p.1 p.2 ≤ R}
  have hfeq : (Function.uncurry fun x v =>
      (Metric.closedBall (0 : V) R ∩ Metric.closedBall v R).indicator
        (fun _ => ψ v) x) = S.indicator (ψ ∘ Prod.snd) := by
    ext ⟨x, v⟩
    simp only [Function.uncurry, Set.indicator,
      Metric.mem_closedBall, Set.mem_inter_iff, Function.comp, dist_zero_right, S,
      Set.mem_setOf_eq]
  rw [hfeq]
  have hS_closed : IsClosed S :=
    (Metric.isClosed_closedBall.preimage continuous_fst).inter
      (isClosed_le (Continuous.dist continuous_fst continuous_snd) continuous_const)
  have hS_bdd : Bornology.IsBounded S := by
    apply Metric.isBounded_closedBall (x := (0 : V × V)) (r := |R| + |R|) |>.subset
    intro ⟨x, v⟩ ⟨hx, hdist⟩
    simp only [Metric.mem_closedBall, dist_zero_right] at hx
    simp only [Metric.mem_closedBall, Prod.dist_eq] at hdist ⊢
    simp only [Prod.fst_zero, Prod.snd_zero, dist_zero_right]
    apply max_le
    · linarith [le_abs_self R, abs_nonneg R]
    · have hv : ‖v‖ ≤ ‖x‖ + ‖v - x‖ := norm_le_insert' v x
      rw [← dist_eq_norm, dist_comm] at hv
      linarith [le_abs_self R]
  exact ((hcont.comp continuous_snd).continuousOn.integrableOn_compact
    (Metric.isCompact_of_isClosed_isBounded hS_closed hS_bdd)).integrable_indicator
    hS_closed.measurableSet

/-- Fubini identity: the averaged double integral equals ∫ ψ · overlapRatio.
    After the inner integral substitution (Haar invariance), we have
    ∫ x in B, ∫ v in closedBall x R, ψ(v). Converting to indicator functions
    on V × V using the key equivalence v ∈ closedBall x R ↔ x ∈ closedBall v R
    (dist_comm), we apply integral_integral_swap (Fubini). The inner integral
    over x evaluates to vol(B ∩ closedBall v R) · ψ(v).
    See Folland, *A Course in Abstract Harmonic Analysis*, §4.2.
-/
private lemma fejer_avg_eq_integral (ψ : V → ℂ) (hcont : Continuous ψ)
    (hint : Integrable ψ) (R : ℝ) (hR : 0 < R) :
    (volume (Metric.closedBall (0 : V) R)).toReal⁻¹ •
      ∫ x in Metric.closedBall (0 : V) R,
        ∫ y in Metric.closedBall (0 : V) R, ψ (x - y) =
    ∫ v, (overlapRatio R v : ℂ) * ψ v := by
  let B := Metric.closedBall (0 : V) R
  -- Step 0: Inner integral substitution (Haar invariance)
  rw [setIntegral_congr_fun measurableSet_closedBall
    (fun x _ => inner_integral_sub ψ x R)]
  -- Volume positivity
  have hvol_ne : (volume B).toReal ≠ 0 :=
    ne_of_gt (ENNReal.toReal_pos (ne_of_gt (Metric.measure_closedBall_pos volume 0 hR))
      (ne_of_lt measure_closedBall_lt_top))
  -- Step 1: Convert nested set integrals to indicator form on V × V
  have h_to_ind : ∫ x in B, ∫ v in Metric.closedBall x R, ψ v =
      ∫ x, ∫ v, (B ∩ Metric.closedBall v R).indicator (fun _ => ψ v) x := by
    trans ∫ x, B.indicator (fun x => ∫ v, (Metric.closedBall x R).indicator ψ v) x
    · rw [integral_indicator measurableSet_closedBall]
      congr 1; funext x; exact (integral_indicator measurableSet_closedBall).symm
    · congr 1; funext x
      by_cases hx : x ∈ B
      · rw [Set.indicator_of_mem hx]; congr 1; funext v
        rw [← indicator_closedBall_inter ψ R x v, Set.indicator_of_mem hx]
      · rw [Set.indicator_of_notMem hx]
        rw [show (fun v => (B ∩ Metric.closedBall v R).indicator (fun _ => ψ v) x) = 0 from by
          funext v; exact Set.indicator_of_notMem (fun h => hx h.1) _]
        simp
  -- Suffices: prove the unscaled Fubini identity, then handle scaling
  suffices h_fubini : ∫ x in B, ∫ v in Metric.closedBall x R, ψ v =
      ∫ v, (volume (B ∩ Metric.closedBall v R)).toReal • ψ v by
    rw [h_fubini]
    -- Push vol(B)⁻¹ inside integral and simplify to overlapRatio
    calc (volume B).toReal⁻¹ •
        ∫ v, (volume (B ∩ Metric.closedBall v R)).toReal • ψ v
      = ∫ v, (volume B).toReal⁻¹ •
          ((volume (B ∩ Metric.closedBall v R)).toReal • ψ v) :=
          (integral_smul _ _).symm
      _ = ∫ v, (overlapRatio R v : ℂ) * ψ v := by
          congr 1; funext v
          rw [smul_comm, ← smul_assoc, Complex.real_smul]
          congr 1; rw [Complex.ofReal_inj]
          simp only [B]; rw [overlapRatio, if_neg hvol_ne, div_eq_mul_inv,
            smul_eq_mul]
  -- Prove h_fubini: Fubini via indicators
  rw [h_to_ind]
  -- Step 2: Fubini swap
  rw [integral_integral_swap (integrable_indicator_prod ψ hcont hint R)]
  -- Step 3: Evaluate inner integral for each v
  congr 1; funext v; show _ = (volume (B ∩ Metric.closedBall v R)).toReal • ψ v
  rw [integral_indicator (measurableSet_closedBall.inter measurableSet_closedBall),
      setIntegral_const]; rfl

/-- For a continuous integrable PD function ψ, Re(∫ ψ) ≥ 0.
    This is the core result: the Fejér-averaged double integral J_R converges
    to ∫ ψ and has Re ≥ 0 for each R.
-/
private lemma pd_integral_re_nonneg (ψ : V → ℂ) (hpd : IsPositiveDefinite ψ)
    (hint : Integrable ψ) (hcont : Continuous ψ) :
    0 ≤ (∫ x, ψ x).re := by
  -- Define J_n = (1/vol(B_n)) double_integral_{B_n×B_n} ψ(x-y) dx dy
  set J : ℕ → ℂ := fun n =>
    if n = 0 then ψ 0
    else (volume (Metric.closedBall (0 : V) (n : ℝ))).toReal⁻¹ •
      ∫ x in Metric.closedBall (0 : V) (n : ℝ),
        ∫ y in Metric.closedBall (0 : V) (n : ℝ), ψ (x - y) with hJ_def
  -- Re(J_n) ≥ 0 for each n
  have hnn : ∀ n : ℕ, 0 ≤ (J n).re := by
    intro n
    simp only [J]
    split_ifs with h
    · exact hpd.eval_zero_nonneg
    · rw [Complex.smul_re]
      apply mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg)
      exact pd_double_integral_re_nonneg ψ hpd hcont _ measurableSet_closedBall
        Metric.isBounded_closedBall
  -- J_n → ∫ ψ via Fubini identity + DCT
  have hconv : Filter.Tendsto J Filter.atTop (nhds (∫ x, ψ x)) := by
    -- For n ≥ 1, J n = ∫ overlapRatio(n,v) * ψ(v) dv by Fubini
    -- overlapRatio → 1, |overlapRatio * ψ| ≤ |ψ|, so DCT gives J → ∫ ψ
    -- Rewrite goal: suffices that ∫ h_n · ψ → ∫ ψ where h_n → 1, |h_n| ≤ 1
    suffices h : Filter.Tendsto
        (fun n : ℕ => ∫ v, (overlapRatio (n : ℝ) v : ℂ) * ψ v)
        Filter.atTop (nhds (∫ x, ψ x)) by
      apply h.congr'
      filter_upwards [Filter.eventually_ne_atTop 0] with n hn
      simp only [J, if_neg hn]
      exact (fejer_avg_eq_integral ψ hcont hint n (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))).symm
    -- Now apply DCT: h_n(v) * ψ(v) → 1 * ψ(v) = ψ(v), with bound |ψ|
    rw [show (∫ x, ψ x) = ∫ x, (1 : ℂ) * ψ x by simp]
    apply tendsto_integral_of_dominated_convergence (fun v => ‖ψ v‖)
    · intro n
      exact (continuous_ofReal.measurable.comp
        (measurable_overlapRatio n)).aestronglyMeasurable.mul
        hcont.aestronglyMeasurable
    · exact hint.norm -- bound is integrable
    · intro n; filter_upwards with v
      rw [norm_mul, Complex.norm_real]
      exact mul_le_of_le_one_left (norm_nonneg _)
        (abs_le.mpr ⟨by linarith [overlapRatio_nonneg (n : ℝ) v],
          overlapRatio_le_one (n : ℝ) v⟩)
    · filter_upwards with v
      have h1 := overlapRatio_tendsto_one v
      have h2 : Filter.Tendsto (fun n : ℕ => (overlapRatio (n : ℝ) v : ℂ))
          Filter.atTop (nhds (1 : ℂ)) :=
        (Complex.continuous_ofReal.tendsto 1).comp h1
      exact h2.mul tendsto_const_nhds
  -- Conclude by ge_of_tendsto'
  exact ge_of_tendsto' ((Complex.continuous_re.tendsto _).comp hconv) hnn

/-! ### Step B + C: The main theorem -/

/-- The Fourier transform of a continuous integrable positive-definite function
    on a finite-dimensional real inner product space has nonneg real part.
-/
theorem pd_l1_fourier_re_nonneg_theorem
    (φ : V → ℂ) (hpd : IsPositiveDefinite φ)
    (hint : Integrable φ) (hcont : Continuous φ)
    (ξ : V) : 0 ≤ (𝓕 φ ξ).re := by
  -- Step 1: 𝓕 φ ξ = ∫ v, φ v * exp(-2πi⟨v,ξ⟩)
  have hF : 𝓕 φ ξ = ∫ v, φ v * cexp (-(2 * ↑π * ↑⟪v, ξ⟫_ℝ * I)) := by
    change ∫ v, 𝐞 (-(innerSL ℝ v ξ)) • φ v = _
    congr 1; ext v
    rw [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, mul_comm]
    congr 1; congr 1
    simp only [innerSL_apply_apply]; push_cast; ring
  rw [hF]
  -- Step 2: The integrand is ψ(v) where ψ = φ · exp(2πi⟨·,-ξ⟩) is PD
  have hψ_eq : (fun v => φ v * cexp (-(2 * ↑π * ↑⟪v, ξ⟫_ℝ * I))) =
      (fun v => φ v * cexp (2 * ↑π * ↑⟪v, -ξ⟫_ℝ * I)) := by
    ext v; congr 1; congr 1; rw [inner_neg_right, Complex.ofReal_neg]; ring
  rw [hψ_eq]
  have hψ_pd : IsPositiveDefinite (fun v => φ v * cexp (2 * ↑π * ↑⟪v, -ξ⟫_ℝ * I)) :=
    hpd.mul (isPositiveDefinite_exp_inner (-ξ))
  -- Step 3: ψ is continuous and integrable
  have hexp_cont : Continuous (fun v : V => cexp (2 * ↑π * ↑⟪v, -ξ⟫_ℝ * I)) :=
    Complex.continuous_exp.comp (((continuous_const.mul
      (continuous_ofReal.comp ((innerSL ℝ).flip (-ξ)).continuous)).mul continuous_const))
  have hψ_cont : Continuous (fun v => φ v * cexp (2 * ↑π * ↑⟪v, -ξ⟫_ℝ * I)) :=
    hcont.mul hexp_cont
  have hψ_int : Integrable (fun v => φ v * cexp (2 * ↑π * ↑⟪v, -ξ⟫_ℝ * I)) := by
    refine Integrable.mono hint hψ_cont.aestronglyMeasurable ?_
    filter_upwards with v
    rw [norm_mul]
    have : ‖cexp (2 * ↑π * ↑⟪v, -ξ⟫_ℝ * I)‖ = 1 := by
      have h : 2 * ↑π * ↑⟪v, -ξ⟫_ℝ * I = ↑(2 * π * ⟪v, -ξ⟫_ℝ) * I := by push_cast; ring
      rw [h, norm_exp_ofReal_mul_I]
    rw [this, mul_one]
  -- Step 4: Apply pd_integral_re_nonneg
  exact pd_integral_re_nonneg _ hψ_pd hψ_int hψ_cont

end
