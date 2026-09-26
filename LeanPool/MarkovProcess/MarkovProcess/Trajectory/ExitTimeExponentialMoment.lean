/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.MarkovProcess.MarkovProcess.Killed.Kernel


/-!
# A positive exponential moment for the exit time

A uniform bound on the survival probability at one horizon `t0` propagates to the multiples of
that horizon by the Chapman--Kolmogorov law for the killed kernels: if the process started
anywhere survives the horizon `t0` inside the open set `U` with probability at most `q`, then it
survives `k` horizons with probability at most `q ^ k`
(`IsConservative.measure_lt_exitTime_nsmul_le`).  Summing the resulting geometric layers bounds a
*positive* exponential moment of the exit time
(`IsConservative.lintegral_exponentialStoppingWeight_exitTime_le`), for every rate `lam` with
`q * exp (lam * t0) < 1`.

The positive exponential weight is `ContinuousPath.exponentialStoppingWeight`, which takes the
value `⊤` where the time is infinite.  That branch is forced: reading the extended time through
`ENNReal.toReal` would return `1` at `⊤` and silently discard the paths that never leave `U`.  A
finite integral of the weight therefore certifies almost-sure finiteness
(`ContinuousPath.ae_lt_top_of_lintegral_exponentialStoppingWeight_ne_top`), which the survival
bound supplies on its own
(`IsConservative.ae_exitTime_lt_top_of_measure_lt_exitTime_le`).

Two consequences are recorded.  An expected-exit-time bound `E_y τ_U ≤ M` valid from every
starting point supplies the survival hypothesis at the horizon `t0 = K M` with `q = K⁻¹` by
Markov's inequality, for every multiplier `K > 1`
(`IsConservative.lintegral_exponentialStoppingWeight_exitTime_le_of_lintegral_le_mul`; the
multiplier `K = 2` is
`IsConservative.lintegral_exponentialStoppingWeight_exitTime_le_of_lintegral_le`), and a large
multiplier normalizes the moment to `2` at a rate that is still positive
(`IsConservative.lintegral_exponentialStoppingWeight_exitTime_le_two_of_lintegral_le`).  The
elementary pointwise bound `t ^ p ≤ (p / (lam * e)) ^ p * exp (lam * t)` converts an
exponential moment into every polynomial moment
(`IsConservative.lintegral_exitTime_pow_le`).

Every statement is an inequality of `ℝ≥0∞`-valued integrals; no integrability side condition and
no real-valued restatement appears.
-/

@[expose] public section

noncomputable section PortComputability

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace MarkovProcess

namespace ContinuousPath

variable {alpha : Type*} [TopologicalSpace alpha]

/-- The exponential weight at rate `lam` of an extended-real time functional, with the value `⊤`
on the infinite branch. -/
noncomputable def exponentialStoppingWeight (lam : ℝ) (sigma : ContinuousPath alpha → ℝ≥0∞)
    (omega : ContinuousPath alpha) : ℝ≥0∞ :=
  if sigma omega = ⊤ then ⊤ else ENNReal.ofReal (Real.exp (lam * (sigma omega).toReal))

/-- On the finite branch the exponential weight is the ordinary exponential. -/
theorem exponentialStoppingWeight_of_ne_top (lam : ℝ) (sigma : ContinuousPath alpha → ℝ≥0∞)
    {omega : ContinuousPath alpha} (h : sigma omega ≠ ⊤) :
    exponentialStoppingWeight lam sigma omega =
      ENNReal.ofReal (Real.exp (lam * (sigma omega).toReal)) :=
  ite_eq_right h

/-- On the infinite branch the exponential weight is `⊤`. -/
theorem exponentialStoppingWeight_of_eq_top (lam : ℝ) (sigma : ContinuousPath alpha → ℝ≥0∞)
    {omega : ContinuousPath alpha} (h : sigma omega = ⊤) :
    exponentialStoppingWeight lam sigma omega = ⊤ :=
  ite_eq_left h

/-- At a nonnegative rate the exponential weight is at least one. -/
theorem one_le_exponentialStoppingWeight (lam : ℝ) (hlam : 0 ≤ lam)
    (sigma : ContinuousPath alpha → ℝ≥0∞) (omega : ContinuousPath alpha) :
    1 ≤ exponentialStoppingWeight lam sigma omega := by
  by_cases h : sigma omega = ⊤
  · rw [exponentialStoppingWeight_of_eq_top lam sigma h]
    exact le_top
  · rw [exponentialStoppingWeight_of_ne_top lam sigma h, ENNReal.one_le_ofReal]
    exact Real.one_le_exp (mul_nonneg hlam ENNReal.toReal_nonneg)

/-- The exponential weight of a measurable time functional is measurable. -/
theorem measurable_exponentialStoppingWeight (lam : ℝ) {sigma : ContinuousPath alpha → ℝ≥0∞}
    (hsigma : Measurable sigma) : Measurable (exponentialStoppingWeight lam sigma) := by
  classical
  refine Measurable.ite (hsigma (measurableSet_singleton ⊤)) measurable_const ?_
  exact ENNReal.measurable_ofReal.comp (Real.continuous_exp.measurable.comp
    (measurable_const.mul (ENNReal.measurable_toReal.comp hsigma)))

/-- A finite integral of the positive exponential weight forces the time to be finite almost
everywhere. -/
theorem ae_lt_top_of_lintegral_exponentialStoppingWeight_ne_top (lam : ℝ)
    {sigma : ContinuousPath alpha → ℝ≥0∞} (hsigma : Measurable sigma)
    {mu : Measure (ContinuousPath alpha)}
    (h : ∫⁻ omega, exponentialStoppingWeight lam sigma omega ∂mu ≠ ⊤) :
    ∀ᵐ omega ∂mu, sigma omega < ⊤ := by
  have hfin := ae_lt_top (measurable_exponentialStoppingWeight lam hsigma) h
  filter_upwards [hfin] with omega homega
  by_contra hnot
  rw [exponentialStoppingWeight_of_eq_top lam sigma (top_unique (not_lt.mp hnot))] at homega
  exact homega.ne rfl

end ContinuousPath

namespace SubMarkovKernelSemigroup

section

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [Nonempty alpha] [LocallyCompactSpace alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)

/-- **Submultiplicativity of survival.**  A uniform bound `q` on the probability of remaining in
the open set `U` past the horizon `t0`, valid from every starting point, gives the bound `q ^ k`
at the `k`-th multiple of that horizon. -/
theorem IsConservative.measure_lt_exitTime_nsmul_le
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    (U : Set alpha) (hU : IsOpen U) (q : ℝ≥0∞) (t0 : NNReal)
    (hq : ∀ y, IsConservative.continuousProcess P hP y
      {omega | (t0 : ℝ≥0∞) < ContinuousPath.exitTime U omega} ≤ q)
    (k : ℕ) (x : alpha) :
    IsConservative.continuousProcess P hP x
        {omega | ((k • t0 : NNReal) : ℝ≥0∞) < ContinuousPath.exitTime U omega} ≤ q ^ k := by
  have hstep : ∀ y, IsConservative.killedKernel P hP U hU t0 y Set.univ ≤ q := by
    intro y
    rw [IsConservative.killedKernel_apply_univ]
    exact hq y
  have hkey : ∀ (n : ℕ) (y : alpha),
      IsConservative.killedKernel P hP U hU (n • t0) y Set.univ ≤ q ^ n := by
    intro n
    induction n with
    | zero =>
        intro y
        rw [pow_zero, zero_nsmul, IsConservative.killedKernel_apply_univ]
        exact prob_le_one
    | succ n ih =>
        intro y
        rw [succ_nsmul, IsConservative.killedKernel_add P hP U hU hFeller hK (n • t0) t0,
          Kernel.comp_apply' _ _ _ MeasurableSet.univ]
        calc
          ∫⁻ z, IsConservative.killedKernel P hP U hU t0 z Set.univ
              ∂(IsConservative.killedKernel P hP U hU (n • t0) y)
              ≤ ∫⁻ _z, q ∂(IsConservative.killedKernel P hP U hU (n • t0) y) :=
            lintegral_mono hstep
          _ = q * IsConservative.killedKernel P hP U hU (n • t0) y Set.univ := by
            rw [lintegral_const]
          _ ≤ q * q ^ n := mul_le_mul_right (ih y) q
          _ = q ^ (n + 1) := by rw [pow_succ, mul_comm]
  have hx := hkey k x
  rwa [IsConservative.killedKernel_apply_univ] at hx

/-- The pointwise geometric layering behind the exponential moment: the exponential weight of an
extended time is dominated by one initial layer plus the layers indexed by the multiples of the
horizon which the time exceeds. -/
private theorem exponentialWeight_le_add_tsum (lam : ℝ) (hlam : 0 ≤ lam) (t0 : NNReal)
    (tau : ℝ≥0∞) :
    (if tau = ⊤ then ⊤ else ENNReal.ofReal (Real.exp (lam * tau.toReal))) ≤
      ENNReal.ofReal (Real.exp (lam * (t0 : ℝ))) +
        ∑' k : ℕ, ({u : ℝ≥0∞ | (((k + 1) • t0 : NNReal) : ℝ≥0∞) < u}.indicator
          (fun _ ↦ ENNReal.ofReal (Real.exp (lam * (t0 : ℝ))) ^ (k + 2)) tau) := by
  classical
  set a : ℝ≥0∞ := ENNReal.ofReal (Real.exp (lam * (t0 : ℝ))) with ha
  have ha1 : 1 ≤ a := by
    rw [ha, ENNReal.one_le_ofReal]
    exact Real.one_le_exp (mul_nonneg hlam t0.coe_nonneg)
  have hpow : ∀ m : ℕ, ENNReal.ofReal (Real.exp (lam * ((m • t0 : NNReal) : ℝ))) = a ^ m := by
    intro m
    rw [ha, ← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul]
    congr 2
    push_cast [nsmul_eq_mul]
    ring
  by_cases hall : ∀ m : ℕ, ((m • t0 : NNReal) : ℝ≥0∞) < tau
  · have hterm : ∀ k : ℕ, (1 : ℝ≥0∞) ≤
        {u : ℝ≥0∞ | (((k + 1) • t0 : NNReal) : ℝ≥0∞) < u}.indicator (fun _ ↦ a ^ (k + 2)) tau := by
      intro k
      have hmem : tau ∈ {u : ℝ≥0∞ | (((k + 1) • t0 : NNReal) : ℝ≥0∞) < u} := hall (k + 1)
      rw [Set.indicator_of_mem hmem]
      exact one_le_pow₀ ha1
    have htop : (∑' k : ℕ, ({u : ℝ≥0∞ | (((k + 1) • t0 : NNReal) : ℝ≥0∞) < u}.indicator
        (fun _ ↦ a ^ (k + 2)) tau)) = ⊤ := by
      refine top_unique ?_
      calc
        (⊤ : ℝ≥0∞) = ∑' _k : ℕ, (1 : ℝ≥0∞) :=
          (ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero).symm
        _ ≤ _ := ENNReal.tsum_le_tsum hterm
    rw [htop, add_top]
    exact le_top
  · push Not at hall
    obtain ⟨m0, hm0⟩ := hall
    have hex : ∃ m : ℕ, tau ≤ ((m • t0 : NNReal) : ℝ≥0∞) := ⟨m0, hm0⟩
    set m := Nat.find hex with hm
    have hmspec : tau ≤ ((m • t0 : NNReal) : ℝ≥0∞) := Nat.find_spec hex
    have hne : tau ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hmspec
    rw [ite_eq_right hne]
    have hle : ENNReal.ofReal (Real.exp (lam * tau.toReal)) ≤ a ^ m := by
      rw [← hpow m]
      refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
      refine mul_le_mul_of_nonneg_left ?_ hlam
      exact (ENNReal.toReal_le_coe_of_le_coe hmspec)
    refine hle.trans ?_
    match hmatch : m with
    | 0 => simpa only [pow_zero] using le_add_right ha1
    | 1 => simpa only [pow_one] using le_add_right le_rfl
    | (j + 2) =>
        have hlt : ((((j + 1) : ℕ) • t0 : NNReal) : ℝ≥0∞) < tau := by
          have := Nat.find_min hex (m := j + 1) (by omega)
          exact not_le.mp this
        refine le_add_left ?_
        refine le_trans (le_of_eq ?_)
          (ENNReal.le_tsum (f := fun k : ℕ ↦
            {u : ℝ≥0∞ | (((k + 1) • t0 : NNReal) : ℝ≥0∞) < u}.indicator
              (fun _ ↦ a ^ (k + 2)) tau) j)
        have hmem : tau ∈ {u : ℝ≥0∞ | (((j + 1) • t0 : NNReal) : ℝ≥0∞) < u} := hlt
        rw [Set.indicator_of_mem hmem]

/-- **A positive exponential moment for the exit time.**  Under a uniform survival bound `q` at
the horizon `t0` and a rate `lam` small enough that `q * exp (lam * t0) < 1`, the exponential
weight of the exit time is integrable with an explicit geometric bound. -/
theorem IsConservative.lintegral_exponentialStoppingWeight_exitTime_le
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    (U : Set alpha) (hU : IsOpen U) (q : ℝ≥0∞) (t0 : NNReal) (lam : ℝ) (hlam : 0 ≤ lam)
    (hcontr : q * ENNReal.ofReal (Real.exp (lam * (t0 : ℝ))) < 1)
    (hq : ∀ y, IsConservative.continuousProcess P hP y
      {omega | (t0 : ℝ≥0∞) < ContinuousPath.exitTime U omega} ≤ q)
    (x : alpha) :
    ∫⁻ omega, ContinuousPath.exponentialStoppingWeight lam (ContinuousPath.exitTime U) omega
        ∂(IsConservative.continuousProcess P hP x)
      ≤ ENNReal.ofReal (Real.exp (lam * (t0 : ℝ))) *
        (1 - q * ENNReal.ofReal (Real.exp (lam * (t0 : ℝ))))⁻¹ := by
  classical
  set Q : Measure (ContinuousPath alpha) := IsConservative.continuousProcess P hP x with hQ
  set a : ℝ≥0∞ := ENNReal.ofReal (Real.exp (lam * (t0 : ℝ))) with ha
  have hExit : Measurable fun omega : ContinuousPath alpha ↦ ContinuousPath.exitTime U omega :=
    ContinuousPath.measurable_exitTime U hU
  set B : ℕ → Set (ContinuousPath alpha) := fun k ↦
    {omega | (((k + 1) • t0 : NNReal) : ℝ≥0∞) < ContinuousPath.exitTime U omega} with hB
  have hBmeas : ∀ k, MeasurableSet (B k) := fun k ↦ measurableSet_lt measurable_const hExit
  have hpoint : ∀ omega : ContinuousPath alpha,
      ContinuousPath.exponentialStoppingWeight lam (ContinuousPath.exitTime U) omega ≤
        a + ∑' k : ℕ, (B k).indicator (fun _ ↦ a ^ (k + 2)) omega := by
    intro omega
    have h := exponentialWeight_le_add_tsum lam hlam t0 (ContinuousPath.exitTime U omega)
    refine h.trans (le_of_eq ?_)
    congr 1
  have hlayer : ∀ k : ℕ, ∫⁻ omega, (B k).indicator (fun _ ↦ a ^ (k + 2)) omega ∂Q ≤
      a ^ (k + 2) * q ^ (k + 1) := by
    intro k
    rw [lintegral_indicator_const (hBmeas k)]
    exact mul_le_mul_right (hP.measure_lt_exitTime_nsmul_le P hFeller hK U hU q t0 hq (k + 1) x)
      (a ^ (k + 2))
  have hsum : (∑' k : ℕ, a ^ (k + 2) * q ^ (k + 1)) = a * ((a * q) * (1 - a * q)⁻¹) := by
    rw [← ENNReal.tsum_geometric_add_one (a * q), ← ENNReal.tsum_mul_left]
    refine tsum_congr fun k ↦ ?_
    rw [mul_pow, ← mul_assoc, ← pow_succ']
  have hcontr' : a * q < 1 := by rwa [mul_comm]
  have hfinal : a + a * ((a * q) * (1 - a * q)⁻¹) = a * (1 - q * a)⁻¹ := by
    have hne : (1 : ℝ≥0∞) - a * q ≠ 0 := by
      simp only [ne_eq, tsub_eq_zero_iff_le, not_le]
      exact hcontr'
    have htop : (1 : ℝ≥0∞) - a * q ≠ ⊤ := by
      exact ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
    have hid : (1 : ℝ≥0∞) - a * q + a * q = 1 := tsub_add_cancel_of_le hcontr'.le
    have hgeom : (1 : ℝ≥0∞) + (a * q) * (1 - a * q)⁻¹ = (1 - a * q)⁻¹ := by
      calc
        (1 : ℝ≥0∞) + (a * q) * (1 - a * q)⁻¹
            = (1 - a * q) * (1 - a * q)⁻¹ + (a * q) * (1 - a * q)⁻¹ := by
          rw [ENNReal.mul_inv_cancel hne htop]
        _ = ((1 - a * q) + a * q) * (1 - a * q)⁻¹ := (add_mul _ _ _).symm
        _ = (1 - a * q)⁻¹ := by rw [hid, one_mul]
    calc
      a + a * ((a * q) * (1 - a * q)⁻¹) = a * (1 + (a * q) * (1 - a * q)⁻¹) := by ring
      _ = a * (1 - a * q)⁻¹ := by rw [hgeom]
      _ = a * (1 - q * a)⁻¹ := by rw [mul_comm a q]
  calc
    ∫⁻ omega, ContinuousPath.exponentialStoppingWeight lam (ContinuousPath.exitTime U) omega ∂Q
        ≤ ∫⁻ omega, (a + ∑' k : ℕ, (B k).indicator (fun _ ↦ a ^ (k + 2)) omega) ∂Q :=
      lintegral_mono hpoint
    _ = a + ∫⁻ omega, ∑' k : ℕ, (B k).indicator (fun _ ↦ a ^ (k + 2)) omega ∂Q := by
      rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
    _ = a + ∑' k : ℕ, ∫⁻ omega, (B k).indicator (fun _ ↦ a ^ (k + 2)) omega ∂Q := by
      rw [lintegral_tsum fun k ↦ (measurable_const.indicator (hBmeas k)).aemeasurable]
    _ ≤ a + ∑' k : ℕ, a ^ (k + 2) * q ^ (k + 1) :=
      add_le_add le_rfl (ENNReal.tsum_le_tsum hlayer)
    _ = a + a * ((a * q) * (1 - a * q)⁻¹) := by rw [hsum]
    _ = a * (1 - q * a)⁻¹ := hfinal

/-- **A uniform survival bound makes the exit time almost surely finite.**  The geometric bound
`a * (1 - q * a)⁻¹` of the exponential moment is finite exactly because `q * a < 1`, so the
exponential weight is almost everywhere finite and hence so is the exit time. -/
theorem IsConservative.ae_exitTime_lt_top_of_measure_lt_exitTime_le
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    (U : Set alpha) (hU : IsOpen U) (q : ℝ≥0∞) (t0 : NNReal) (lam : ℝ) (hlam : 0 ≤ lam)
    (hcontr : q * ENNReal.ofReal (Real.exp (lam * (t0 : ℝ))) < 1)
    (hq : ∀ y, IsConservative.continuousProcess P hP y
      {omega | (t0 : ℝ≥0∞) < ContinuousPath.exitTime U omega} ≤ q)
    (x : alpha) :
    ∀ᵐ omega ∂(IsConservative.continuousProcess P hP x),
      ContinuousPath.exitTime U omega < ⊤ := by
  refine ContinuousPath.ae_lt_top_of_lintegral_exponentialStoppingWeight_ne_top lam
    (ContinuousPath.measurable_exitTime U hU) ?_
  refine ne_top_of_le_ne_top ?_ (hP.lintegral_exponentialStoppingWeight_exitTime_le P hFeller hK
    U hU q t0 lam hlam hcontr hq x)
  refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.inv_ne_top.mpr ?_)
  simpa only [ne_eq, tsub_eq_zero_iff_le, not_le] using hcontr

/-- **Markov's inequality at a free multiple of the mean.**  A uniform bound `M` on the expected
exit time from `U` bounds the probability of surviving the horizon `K * M` by `K⁻¹`, for every
multiplier `K > 1`, hence gives an exponential moment at every rate with `exp (lam * K * M) < K`.
Enlarging `K` makes the survival probability at one horizon as small as one likes, at the price of
a longer horizon; the normalized form is
`IsConservative.lintegral_exponentialStoppingWeight_exitTime_le_two_of_lintegral_le`. -/
theorem IsConservative.lintegral_exponentialStoppingWeight_exitTime_le_of_lintegral_le_mul
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    (U : Set alpha) (hU : IsOpen U) (M : NNReal)
    (hM : ∀ y, ∫⁻ omega, ContinuousPath.exitTime U omega
      ∂(IsConservative.continuousProcess P hP y) ≤ (M : ℝ≥0∞))
    (K : ℝ≥0) (hK1 : 1 < K) (lam : ℝ) (hlam : 0 ≤ lam)
    (hrate : Real.exp (lam * ((K : ℝ) * (M : ℝ))) < (K : ℝ)) (x : alpha) :
    ∫⁻ omega, ContinuousPath.exponentialStoppingWeight lam (ContinuousPath.exitTime U) omega
        ∂(IsConservative.continuousProcess P hP x)
      ≤ ENNReal.ofReal (Real.exp (lam * ((K : ℝ) * (M : ℝ)))) *
        (1 - (K : ℝ≥0∞)⁻¹ * ENNReal.ofReal (Real.exp (lam * ((K : ℝ) * (M : ℝ)))))⁻¹ := by
  have hKpos : (0 : ℝ≥0) < K := lt_trans zero_lt_one hK1
  have hK0 : ((K : ℝ≥0) : ℝ≥0∞) ≠ 0 := by
    simpa only [ne_eq, ENNReal.coe_eq_zero] using hKpos.ne'
  have hcast : (((K * M : NNReal) : ℝ)) = (K : ℝ) * (M : ℝ) := by push_cast; ring
  have hExit : Measurable fun omega : ContinuousPath alpha ↦ ContinuousPath.exitTime U omega :=
    ContinuousPath.measurable_exitTime U hU
  have hq : ∀ y, IsConservative.continuousProcess P hP y
      {omega | ((K * M : NNReal) : ℝ≥0∞) < ContinuousPath.exitTime U omega} ≤ (K : ℝ≥0∞)⁻¹ := by
    intro y
    rcases eq_or_lt_of_le (zero_le : (0 : NNReal) ≤ M) with hM0 | hM0
    · have hzero : ∫⁻ omega, ContinuousPath.exitTime U omega
          ∂(IsConservative.continuousProcess P hP y) = 0 := by
        refine le_antisymm ?_ zero_le
        simpa only [← hM0, ENNReal.coe_zero] using! hM y
      have hae : ∀ᵐ omega ∂(IsConservative.continuousProcess P hP y),
          ContinuousPath.exitTime U omega = 0 := (lintegral_eq_zero_iff hExit).mp hzero
      have hnull : IsConservative.continuousProcess P hP y
          {omega | ((K * M : NNReal) : ℝ≥0∞) < ContinuousPath.exitTime U omega} = 0 :=
        measure_mono_null (fun omega homega ↦ (zero_le.trans_lt homega).ne') (ae_iff.mp hae)
      rw [hnull]
      exact zero_le
    · have hpos : ((K * M : NNReal) : ℝ≥0∞) ≠ 0 := by
        simp only [ne_eq, ENNReal.coe_eq_zero, mul_eq_zero, not_or]
        exact ⟨hKpos.ne', hM0.ne'⟩
      have hmarkov := mul_meas_ge_le_lintegral₀ (μ := IsConservative.continuousProcess P hP y)
        hExit.aemeasurable ((K * M : NNReal) : ℝ≥0∞)
      have hquot : ((K * M : NNReal) : ℝ≥0∞) * (K : ℝ≥0∞)⁻¹ = (M : ℝ≥0∞) := by
        rw [ENNReal.coe_mul, mul_comm ((K : ℝ≥0∞)) ((M : ℝ≥0∞)), mul_assoc,
          ENNReal.mul_inv_cancel hK0 ENNReal.coe_ne_top, mul_one]
      have hle : ((K * M : NNReal) : ℝ≥0∞) * IsConservative.continuousProcess P hP y
          {omega | ((K * M : NNReal) : ℝ≥0∞) ≤ ContinuousPath.exitTime U omega} ≤
            ((K * M : NNReal) : ℝ≥0∞) * (K : ℝ≥0∞)⁻¹ := by
        rw [hquot]
        exact hmarkov.trans (hM y)
      have hcancel := (ENNReal.mul_le_mul_iff_right hpos ENNReal.coe_ne_top).mp hle
      refine le_trans (measure_mono ?_) hcancel
      intro omega homega
      exact le_of_lt (Set.mem_ofPred_eq ▸ homega)
  have hcontr : (K : ℝ≥0∞)⁻¹ * ENNReal.ofReal (Real.exp (lam * ((K : ℝ) * (M : ℝ)))) < 1 := by
    have hlt : ENNReal.ofReal (Real.exp (lam * ((K : ℝ) * (M : ℝ)))) < (K : ℝ≥0∞) := by
      rw [← ENNReal.ofReal_coe_nnreal]
      exact (ENNReal.ofReal_lt_ofReal_iff (by exact_mod_cast hKpos)).mpr hrate
    calc
      (K : ℝ≥0∞)⁻¹ * ENNReal.ofReal (Real.exp (lam * ((K : ℝ) * (M : ℝ))))
          < (K : ℝ≥0∞)⁻¹ * (K : ℝ≥0∞) :=
        ENNReal.mul_lt_mul_right (ENNReal.inv_ne_zero.mpr ENNReal.coe_ne_top)
          (ENNReal.inv_ne_top.mpr hK0) hlt
      _ = 1 := ENNReal.inv_mul_cancel hK0 ENNReal.coe_ne_top
  have hmain := hP.lintegral_exponentialStoppingWeight_exitTime_le P hFeller hK U hU
    ((K : ℝ≥0∞)⁻¹) (K * M) lam hlam (by rwa [hcast]) hq x
  rwa [hcast] at hmain

/-- **A normalized exponential moment.**  The rate condition
`exp (lam * K * M) * (K + 2) ≤ 2 * K`, that is `lam ≤ log (2 K / (K + 2)) / (K M)`, normalizes the
exponential moment of the exit time to `2`.  It leaves room for a positive rate as soon as
`K > 2` and `M > 0`; for instance `lam = log (19 / 10) / (K M)` is admissible whenever
`38 ≤ K`. -/
theorem IsConservative.lintegral_exponentialStoppingWeight_exitTime_le_two_of_lintegral_le
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    (U : Set alpha) (hU : IsOpen U) (M : NNReal)
    (hM : ∀ y, ∫⁻ omega, ContinuousPath.exitTime U omega
      ∂(IsConservative.continuousProcess P hP y) ≤ (M : ℝ≥0∞))
    (K : ℝ≥0) (hK1 : 1 < K) (lam : ℝ) (hlam : 0 ≤ lam)
    (hrate : Real.exp (lam * ((K : ℝ) * (M : ℝ))) * ((K : ℝ) + 2) ≤ 2 * (K : ℝ)) (x : alpha) :
    ∫⁻ omega, ContinuousPath.exponentialStoppingWeight lam (ContinuousPath.exitTime U) omega
        ∂(IsConservative.continuousProcess P hP x) ≤ 2 := by
  set A : ℝ := Real.exp (lam * ((K : ℝ) * (M : ℝ))) with hA
  have hApos : (0 : ℝ) < A := Real.exp_pos _
  have hKpos : (0 : ℝ) < (K : ℝ) := by
    exact_mod_cast lt_trans zero_lt_one hK1
  have hKne : (K : ℝ) ≠ 0 := hKpos.ne'
  have hKsq : (0 : ℝ) < (K : ℝ) * (K : ℝ) := mul_pos hKpos hKpos
  have hK2 : (0 : ℝ) < (K : ℝ) + 2 := by linarith only [hKpos]
  have hAK : A < (K : ℝ) := by
    have hwide : 2 * (K : ℝ) < (K : ℝ) * ((K : ℝ) + 2) := by linarith only [hKsq]
    exact lt_of_mul_lt_mul_right (hrate.trans_lt hwide) hK2.le
  refine (hP.lintegral_exponentialStoppingWeight_exitTime_le_of_lintegral_le_mul P hFeller hK
    U hU M hM K hK1 lam hlam hAK x).trans ?_
  have hstep : (K : ℝ≥0∞)⁻¹ * ENNReal.ofReal A = ENNReal.ofReal (A / (K : ℝ)) := by
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_inv_of_pos hKpos,
      ← ENNReal.ofReal_mul (by positivity), div_eq_inv_mul]
  have hsub : (1 : ℝ≥0∞) - ENNReal.ofReal (A / (K : ℝ)) = ENNReal.ofReal (1 - A / (K : ℝ)) := by
    rw [ENNReal.ofReal_sub _ (by positivity), ENNReal.ofReal_one]
  have hgoal : A ≤ 2 * (1 - A / (K : ℝ)) := by
    rw [← sub_nonneg]
    have hid : 2 * (1 - A / (K : ℝ)) - A = (2 * (K : ℝ) - A * ((K : ℝ) + 2)) / (K : ℝ) := by
      field_simp
      ring
    rw [hid]
    exact div_nonneg (by linarith only [hrate]) hKpos.le
  rw [hstep, hsub, ← div_eq_mul_inv,
    ENNReal.div_le_iff_le_mul (Or.inr (by simp)) (Or.inl ENNReal.ofReal_ne_top),
    show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
  exact ENNReal.ofReal_le_ofReal hgoal

/-- **Markov's inequality supplies the survival hypothesis.**  A uniform bound `M` on the expected
exit time from `U` bounds the probability of surviving the horizon `2 M` by one half, hence gives
an exponential moment at every rate with `exp (lam * 2 M) < 2`.  This is the multiplier `K = 2` of
`IsConservative.lintegral_exponentialStoppingWeight_exitTime_le_of_lintegral_le_mul`. -/
theorem IsConservative.lintegral_exponentialStoppingWeight_exitTime_le_of_lintegral_le
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    (U : Set alpha) (hU : IsOpen U) (M : NNReal)
    (hM : ∀ y, ∫⁻ omega, ContinuousPath.exitTime U omega
      ∂(IsConservative.continuousProcess P hP y) ≤ (M : ℝ≥0∞))
    (lam : ℝ) (hlam : 0 ≤ lam) (hrate : Real.exp (lam * (2 * (M : ℝ))) < 2) (x : alpha) :
    ∫⁻ omega, ContinuousPath.exponentialStoppingWeight lam (ContinuousPath.exitTime U) omega
        ∂(IsConservative.continuousProcess P hP x)
      ≤ ENNReal.ofReal (Real.exp (lam * (2 * (M : ℝ)))) *
        (1 - 2⁻¹ * ENNReal.ofReal (Real.exp (lam * (2 * (M : ℝ)))))⁻¹ := by
  have hmain := hP.lintegral_exponentialStoppingWeight_exitTime_le_of_lintegral_le_mul P hFeller
    hK U hU M hM 2 one_lt_two lam hlam (by simpa only [NNReal.coe_ofNat] using hrate) x
  simpa only [NNReal.coe_ofNat, ENNReal.coe_ofNat] using hmain

/-- The elementary bound `t ^ p ≤ (p / (lam * e)) ^ p * exp (lam * t)` on the nonnegative
half-line. -/
private theorem pow_le_mul_exp (lam : ℝ) (hlam : 0 < lam) (p : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    t ^ p ≤ ((p : ℝ) / (lam * Real.exp 1)) ^ p * Real.exp (lam * t) := by
  rcases Nat.eq_zero_or_pos p with hp | hp
  · subst hp
    simpa only [pow_zero, one_mul] using Real.one_le_exp (mul_nonneg hlam.le ht)
  have hpR : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp
  have hst : 0 ≤ lam * t := mul_nonneg hlam.le ht
  have h1 : lam * t / (p : ℝ) ≤ Real.exp (lam * t / (p : ℝ) - 1) := by
    have h := Real.add_one_le_exp (lam * t / (p : ℝ) - 1)
    linarith only [h]
  have h2 : (lam * t / (p : ℝ)) ^ p ≤ Real.exp (lam * t / (p : ℝ) - 1) ^ p :=
    pow_le_pow_left₀ (by positivity) h1 p
  have h3 : Real.exp (lam * t / (p : ℝ) - 1) ^ p = Real.exp (lam * t) / Real.exp 1 ^ p := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_sub]
    congr 1
    field_simp
  rw [h3] at h2
  have h4 := mul_le_mul_of_nonneg_left h2
    (by positivity : (0 : ℝ) ≤ ((p : ℝ) / lam) ^ p)
  have h5 : ((p : ℝ) / lam) ^ p * (lam * t / (p : ℝ)) ^ p = t ^ p := by
    rw [← mul_pow]
    congr 1
    field_simp
  have h6 : ((p : ℝ) / lam) ^ p * (Real.exp (lam * t) / Real.exp 1 ^ p) =
      ((p : ℝ) / (lam * Real.exp 1)) ^ p * Real.exp (lam * t) := by
    rw [div_pow, div_pow, mul_pow]
    field_simp
  rw [h5, h6] at h4
  exact h4

omit [LocallyCompactSpace alpha] in
/-- **Every polynomial moment from one exponential moment.**  For a positive rate the exit time
has all its moments controlled by the exponential moment, with the explicit constant
`(p / (lam * e)) ^ p`.  Taking `p = 2` bounds the second moment. -/
theorem IsConservative.lintegral_exitTime_pow_le
    (U : Set alpha) (lam : ℝ) (hlam : 0 < lam) (p : ℕ) (x : alpha) :
    ∫⁻ omega, ContinuousPath.exitTime U omega ^ p ∂(IsConservative.continuousProcess P hP x)
      ≤ ENNReal.ofReal (((p : ℝ) / (lam * Real.exp 1)) ^ p) *
        ∫⁻ omega, ContinuousPath.exponentialStoppingWeight lam (ContinuousPath.exitTime U) omega
          ∂(IsConservative.continuousProcess P hP x) := by
  have hconst : (0 : ℝ) < ((p : ℝ) / (lam * Real.exp 1)) ^ p := by
    rcases Nat.eq_zero_or_pos p with hp | hp
    · simp only [hp, pow_zero]
      norm_num
    · have : (0 : ℝ) < (p : ℝ) / (lam * Real.exp 1) := by
        have hpR : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp
        positivity
      exact pow_pos this p
  have hpoint : ∀ omega : ContinuousPath alpha,
      ContinuousPath.exitTime U omega ^ p ≤
        ENNReal.ofReal (((p : ℝ) / (lam * Real.exp 1)) ^ p) *
          ContinuousPath.exponentialStoppingWeight lam (ContinuousPath.exitTime U) omega := by
    intro omega
    by_cases hne : ContinuousPath.exitTime U omega = ⊤
    · rw [ContinuousPath.exponentialStoppingWeight_of_eq_top lam _ hne,
        ENNReal.mul_top (by simpa only [ne_eq, ENNReal.ofReal_eq_zero, not_le] using hconst)]
      exact le_top
    · rw [ContinuousPath.exponentialStoppingWeight_of_ne_top lam _ hne,
        ← ENNReal.ofReal_mul hconst.le]
      nth_rewrite 1 [← ENNReal.ofReal_toReal hne]
      rw [← ENNReal.ofReal_pow ENNReal.toReal_nonneg]
      exact ENNReal.ofReal_le_ofReal
        (pow_le_mul_exp lam hlam p _ ENNReal.toReal_nonneg)
  calc
    ∫⁻ omega, ContinuousPath.exitTime U omega ^ p ∂(IsConservative.continuousProcess P hP x)
        ≤ ∫⁻ omega, ENNReal.ofReal (((p : ℝ) / (lam * Real.exp 1)) ^ p) *
            ContinuousPath.exponentialStoppingWeight lam (ContinuousPath.exitTime U) omega
          ∂(IsConservative.continuousProcess P hP x) := lintegral_mono hpoint
    _ = ENNReal.ofReal (((p : ℝ) / (lam * Real.exp 1)) ^ p) *
          ∫⁻ omega, ContinuousPath.exponentialStoppingWeight lam
            (ContinuousPath.exitTime U) omega ∂(IsConservative.continuousProcess P hP x) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

end

end SubMarkovKernelSemigroup

end MarkovProcess

end PortComputability
