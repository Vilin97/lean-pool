/-
Copyright (c) 2026 The lean-malliavin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-malliavin contributors
-/
module

public import LeanPool.Malliavin.Malliavin.ItoConstruction

/-!
# Brownian terminal values for iterated Itô integrals

This file begins the Brownian-linked iterated-Itô construction by packaging the product of a
finite chain of Brownian increments as an element of `L²(P)`.  These terminal values are the
required images of ordered-box kernels in `IteratedIntegralFamily.IsBrownian`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal InnerProductSpace

noncomputable
section

namespace Malliavin

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}

attribute [local instance] gaussianSFinite

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
/-- A finite product of Brownian increments has finite second moment. -/
theorem memLp_chainIntegral (hB : IsPreBrownianReal B P) {n : ℕ}
    (u v : Fin n → ℝ≥0) :
    MemLp (chainIntegral B u v) 2 P := by
  let _ : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  rcases n with _ | n
  · convert (memLp_const (μ := P) (p := (2 : ℝ≥0∞)) (1 : ℝ)) using 1
    funext w
    simp [chainIntegral]
  · unfold chainIntegral
    let q : ℝ≥0∞ := 2 * (n + 1)
    have hn0 : (n + 1 : ℝ≥0∞) ≠ 0 := by norm_num
    have hnTop : (n + 1 : ℝ≥0∞) ≠ ∞ := by
      simpa only [Nat.cast_add, Nat.cast_one] using ENNReal.natCast_ne_top (n + 1)
    have hq : q ≠ ∞ := ENNReal.mul_ne_top (by norm_num) hnTop
    have hf : ∀ i ∈ (Finset.univ : Finset (Fin (n + 1))),
        MemLp (fun w ↦ B (v i) w - B (u i) w) q P := by
      intro i _
      exact hB.isGaussianProcess.hasGaussianLaw_sub.memLp hq
    have hprod :=
      MeasureTheory.MemLp.fun_prod (s := (Finset.univ : Finset (Fin (n + 1)))) hf
    have hqinv : q⁻¹ = (2 : ℝ≥0∞)⁻¹ * (n + 1 : ℝ≥0∞)⁻¹ := by
      dsimp only [q]
      exact ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))
    have hexp : ((n + 1 : ℝ≥0∞) * q⁻¹)⁻¹ = 2 := by
      rw [hqinv, mul_left_comm, ENNReal.mul_inv_cancel hn0 hnTop, mul_one, inv_inv]
    have hsum : (∑ _ : Fin (n + 1), q⁻¹) = (n + 1 : ℝ≥0∞) * q⁻¹ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Nat.cast_add, Nat.cast_one]
    rw [hsum, hexp] at hprod
    exact hprod

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
/-- The product of a finite chain of Brownian increments, as a random variable in `L²(P)`. -/
noncomputable def chainIntegralLp (hB : IsPreBrownianReal B P) {n : ℕ}
    (u v : Fin n → ℝ≥0) : RandomL2 P :=
  (memLp_chainIntegral hB u v).toLp (chainIntegral B u v)

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
/-- A representative of the `L²` Brownian chain product is the pointwise product of increments. -/
theorem coeFn_chainIntegralLp (hB : IsPreBrownianReal B P) {n : ℕ}
    (u v : Fin n → ℝ≥0) :
    (chainIntegralLp hB u v : W → ℝ) =ᵐ[P] chainIntegral B u v :=
  MemLp.coeFn_toLp _

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [MeasurableSpace W]
    [BorelSpace W] [SecondCountableTopology W] [IsGaussian P] in
/-- Splitting off the last increment in a nonempty Brownian chain. -/
theorem chainIntegral_succ {n : ℕ} (u v : Fin (n + 1) → ℝ≥0) (w : W) :
    chainIntegral B u v w =
      chainIntegral B (fun i : Fin n ↦ u i.castSucc) (fun i : Fin n ↦ v i.castSucc) w *
        (B (v (Fin.last n)) w - B (u (Fin.last n)) w) := by
  unfold chainIntegral
  rw [Fin.prod_univ_castSucc]

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
/-- If all endpoints precede `t`, a Brownian chain product is strongly measurable for the
natural filtration at `t`. -/
theorem stronglyMeasurable_chainIntegral_natural
    (hsm : ∀ s, StronglyMeasurable (B s)) {n : ℕ}
    (u v : Fin n → ℝ≥0) (t : ℝ≥0)
    (hu : ∀ i, u i ≤ t) (hv : ∀ i, v i ≤ t) :
    StronglyMeasurable[(Filtration.natural B hsm) t] (chainIntegral B u v) := by
  classical
  unfold chainIntegral
  have hfactor : ∀ i : Fin n,
      StronglyMeasurable[(Filtration.natural B hsm) t]
        (fun w ↦ B (v i) w - B (u i) w) := fun i ↦
    ((Filtration.stronglyAdapted_natural hsm).stronglyMeasurable_le (hv i)).sub
      ((Filtration.stronglyAdapted_natural hsm).stronglyMeasurable_le (hu i))
  induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
  | empty =>
      have hone : StronglyMeasurable[(Filtration.natural B hsm) t]
          (fun _ : W ↦ (1 : ℝ)) := stronglyMeasurable_const
      simpa using hone
  | insert i s hi ih =>
      have hmul := (hfactor i).mul ih
      convert hmul using 1
      funext w
      simp only [Pi.mul_apply, Finset.prod_insert hi]

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
/-- A Brownian chain whose endpoints precede `t`, bundled as an `𝓕_t`-measurable `L²` random
variable. -/
noncomputable def adaptedChainIntegralLp
    (hB : IsPreBrownianReal B P) (hsm : ∀ s, StronglyMeasurable (B s))
    {n : ℕ} (u v : Fin n → ℝ≥0) (t : ℝ≥0)
    (hu : ∀ i, u i ≤ t) (hv : ∀ i, v i ≤ t) :
    lpMeas ℝ ℝ ((Filtration.natural B hsm) t) 2 P :=
  ⟨chainIntegralLp hB u v,
    (stronglyMeasurable_chainIntegral_natural hsm u v t hu hv).aestronglyMeasurable.congr
      (coeFn_chainIntegralLp hB u v).symm⟩

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
/-- Forgetting adapted measurability recovers the Brownian chain product in ambient `L²(P)`. -/
@[simp]
theorem adaptedChainIntegralLp_coe
    (hB : IsPreBrownianReal B P) (hsm : ∀ s, StronglyMeasurable (B s))
    {n : ℕ} (u v : Fin n → ℝ≥0) (t : ℝ≥0)
    (hu : ∀ i, u i ≤ t) (hv : ∀ i, v i ≤ t) :
    (adaptedChainIntegralLp hB hsm u v t hu hv : RandomL2 P) = chainIntegralLp hB u v :=
  rfl

omit [CompleteSpace W] [BorelSpace W] [SecondCountableTopology W] in
/-- The empty Brownian chain is the constant-one random variable. -/
theorem chainIntegralLp_zero (hB : IsPreBrownianReal B P)
    (u v : Fin 0 → ℝ≥0) :
    chainIntegralLp hB u v = Lp.const 2 P (1 : ℝ) := by
  apply Lp.ext
  filter_upwards [coeFn_chainIntegralLp hB u v, Lp.coeFn_const 2 P (1 : ℝ)]
    with w hchain hone
  rw [hchain, hone]
  simp [chainIntegral]

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
/-- The prefix of an ordered Brownian increment chain, bundled at the starting time of its last
increment. -/
noncomputable def orderedChainPrefixAdapted
    (hB : IsPreBrownianReal B P) (hsm : ∀ s, StronglyMeasurable (B s))
    {n : ℕ} (u v : Fin (n + 1) → ℝ≥0)
    (huv : ∀ i, u i ≤ v i)
    (hord : ∀ i j, i < j → v i ≤ u j) :
    lpMeas ℝ ℝ ((Filtration.natural B hsm) (u (Fin.last n))) 2 P :=
  adaptedChainIntegralLp hB hsm
    (fun i : Fin n ↦ u i.castSucc) (fun i : Fin n ↦ v i.castSucc)
    (u (Fin.last n))
    (fun i ↦ (huv i.castSucc).trans (hord i.castSucc (Fin.last n) i.castSucc_lt_last))
    (fun i ↦ hord i.castSucc (Fin.last n) i.castSucc_lt_last)

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
/-- The ambient value of the adapted prefix is the `L²` product of the preceding increments. -/
@[simp]
theorem orderedChainPrefixAdapted_coe
    (hB : IsPreBrownianReal B P) (hsm : ∀ s, StronglyMeasurable (B s))
    {n : ℕ} (u v : Fin (n + 1) → ℝ≥0)
    (huv : ∀ i, u i ≤ v i)
    (hord : ∀ i j, i < j → v i ≤ u j) :
    (orderedChainPrefixAdapted hB hsm u v huv hord : RandomL2 P) =
      chainIntegralLp hB (fun i : Fin n ↦ u i.castSucc)
        (fun i : Fin n ↦ v i.castSucc) :=
  rfl

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
/-- A nonempty ordered Brownian chain is the elementary Brownian terminal value obtained by
integrating its adapted prefix over the final interval. -/
theorem chainIntegralLp_succ_eq_elementaryBrownianValue
    (hB : IsPreBrownianReal B P) (hsm : ∀ s, StronglyMeasurable (B s))
    {n : ℕ} (u v : Fin (n + 1) → ℝ≥0)
    (huv : ∀ i, u i ≤ v i)
    (hord : ∀ i j, i < j → v i ≤ u j) :
    chainIntegralLp hB u v =
      elementaryBrownianValue hB hsm rfl (huv (Fin.last n))
        (orderedChainPrefixAdapted hB hsm u v huv hord) := by
  apply Lp.ext
  filter_upwards [coeFn_chainIntegralLp hB u v,
    coeFn_chainIntegralLp hB (fun i : Fin n ↦ u i.castSucc)
      (fun i : Fin n ↦ v i.castSucc),
    coeFn_elementaryBrownianValue hB hsm rfl (huv (Fin.last n))
      (orderedChainPrefixAdapted hB hsm u v huv hord)] with w hfull hprefix hvalue
  rw [hfull, hvalue, chainIntegral_succ]
  change _ =
    (chainIntegralLp hB (fun i : Fin n ↦ u i.castSucc)
      (fun i : Fin n ↦ v i.castSucc) : W → ℝ) w * _
  rw [hprefix]

omit [CompleteSpace W] [BorelSpace W] in
/-- **Iterated-Itô successor identity on ordered boxes.**  The product of an ordered chain of
`n + 1` Brownian increments is the constructed natural Itô integral of the preceding chain,
used as the adapted coefficient on the final interval. -/
theorem chainIntegralLp_succ_eq_naturalItoIntegral
    (hB : IsPreBrownianReal B P) (hsm : ∀ s, StronglyMeasurable (B s))
    {n : ℕ} (u v : Fin (n + 1) → ℝ≥0)
    (huv : ∀ i, u i ≤ v i)
    (hord : ∀ i j, i < j → v i ≤ u j) :
    chainIntegralLp hB u v =
      naturalItoIntegral hB hsm rfl
        (elementaryPredictable (Filtration.natural B hsm)
          (u (Fin.last n)) (v (Fin.last n))
          (orderedChainPrefixAdapted hB hsm u v huv hord)) := by
  rw [naturalItoIntegral_elementaryPredictable hB hsm rfl]
  exact chainIntegralLp_succ_eq_elementaryBrownianValue hB hsm u v huv hord

omit [CompleteSpace W] [BorelSpace W] in
/-- Every nonempty ordered Brownian chain product is centered. -/
theorem integral_chainIntegralLp_succ
    (hB : IsPreBrownianReal B P) (hsm : ∀ s, StronglyMeasurable (B s))
    {n : ℕ} (u v : Fin (n + 1) → ℝ≥0)
    (huv : ∀ i, u i ≤ v i)
    (hord : ∀ i j, i < j → v i ≤ u j) :
    ∫ w, chainIntegralLp hB u v w ∂P = 0 := by
  rw [chainIntegralLp_succ_eq_naturalItoIntegral hB hsm u v huv hord]
  exact integral_naturalItoIntegral hB hsm rfl _

omit [CompleteSpace W] [BorelSpace W] [SecondCountableTopology W] in
/-- The inner product of two elementary predictable processes factors into the overlap of their
time intervals and the inner product of their coefficients. -/
theorem inner_elementaryPredictable
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (a b c d : ℝ≥0)
    (Z : lpMeas ℝ ℝ (𝓕 a) 2 P) (Y : lpMeas ℝ ℝ (𝓕 c) 2 P) :
    inner ℝ (elementaryPredictable 𝓕 a b Z) (elementaryPredictable 𝓕 c d Y) =
      nonnegativeLebesgueMeasure.real (Set.Ioc a b ∩ Set.Ioc c d) *
        inner ℝ (Z : RandomL2 P) (Y : RandomL2 P) := by
  change inner ℝ (elementaryPredictable 𝓕 a b Z : TimeProcessL2 P)
      (elementaryPredictable 𝓕 c d Y : TimeProcessL2 P) = _
  rw [elementaryPredictable_coeLp, elementaryPredictable_coeLp, inner_tensor]
  unfold iocIndicator
  rw [L2.real_inner_indicatorConstLp_one_indicatorConstLp_one measurableSet_Ioc
    measurableSet_Ioc (nonnegativeLebesgueMeasure_Ioc_ne_top a b)
    (nonnegativeLebesgueMeasure_Ioc_ne_top c d)]

omit [CompleteSpace W] [BorelSpace W] in
/-- Recursive Gram identity for two ordered Brownian chains of arbitrary positive orders. -/
theorem inner_chainIntegralLp_succ_succ
    (hB : IsPreBrownianReal B P) (hsm : ∀ s, StronglyMeasurable (B s))
    {m n : ℕ} (u v : Fin (m + 1) → ℝ≥0) (x y : Fin (n + 1) → ℝ≥0)
    (huv : ∀ i, u i ≤ v i) (hxy : ∀ i, x i ≤ y i)
    (huord : ∀ i j, i < j → v i ≤ u j)
    (hxord : ∀ i j, i < j → y i ≤ x j) :
    inner ℝ (chainIntegralLp hB u v) (chainIntegralLp hB x y) =
      nonnegativeLebesgueMeasure.real
          (Set.Ioc (u (Fin.last m)) (v (Fin.last m)) ∩
            Set.Ioc (x (Fin.last n)) (y (Fin.last n))) *
        inner ℝ
          (chainIntegralLp hB (fun i : Fin m ↦ u i.castSucc)
            (fun i : Fin m ↦ v i.castSucc))
          (chainIntegralLp hB (fun i : Fin n ↦ x i.castSucc)
            (fun i : Fin n ↦ y i.castSucc)) := by
  rw [chainIntegralLp_succ_eq_elementaryBrownianValue hB hsm u v huv huord,
    chainIntegralLp_succ_eq_elementaryBrownianValue hB hsm x y hxy hxord,
    inner_elementaryBrownianValue_eq_inner_elementaryPredictable hB hsm rfl,
    inner_elementaryPredictable]
  rfl

omit [CompleteSpace W] [BorelSpace W] in
/-- Recursive Gram identity for two ordered Brownian chains of the same positive order. -/
theorem inner_chainIntegralLp_succ
    (hB : IsPreBrownianReal B P) (hsm : ∀ s, StronglyMeasurable (B s))
    {n : ℕ} (u v x y : Fin (n + 1) → ℝ≥0)
    (huv : ∀ i, u i ≤ v i) (hxy : ∀ i, x i ≤ y i)
    (huord : ∀ i j, i < j → v i ≤ u j)
    (hxord : ∀ i j, i < j → y i ≤ x j) :
    inner ℝ (chainIntegralLp hB u v) (chainIntegralLp hB x y) =
      nonnegativeLebesgueMeasure.real
          (Set.Ioc (u (Fin.last n)) (v (Fin.last n)) ∩
            Set.Ioc (x (Fin.last n)) (y (Fin.last n))) *
        inner ℝ
          (chainIntegralLp hB (fun i : Fin n ↦ u i.castSucc)
            (fun i : Fin n ↦ v i.castSucc))
          (chainIntegralLp hB (fun i : Fin n ↦ x i.castSucc)
            (fun i : Fin n ↦ y i.castSucc)) := by
  exact inner_chainIntegralLp_succ_succ hB hsm u v x y huv hxy huord hxord

omit [CompleteSpace W] [BorelSpace W] in
/-- **Gram identity for ordered Brownian chains.**  The inner product of two products of `n`
ordered increments is the product of the lengths of the coordinatewise interval overlaps. -/
theorem inner_chainIntegralLp
    (hB : IsPreBrownianReal B P) (hsm : ∀ s, StronglyMeasurable (B s))
    {n : ℕ} (u v x y : Fin n → ℝ≥0)
    (huv : ∀ i, u i ≤ v i) (hxy : ∀ i, x i ≤ y i)
    (huord : ∀ i j, i < j → v i ≤ u j)
    (hxord : ∀ i j, i < j → y i ≤ x j) :
    inner ℝ (chainIntegralLp hB u v) (chainIntegralLp hB x y) =
      ∏ i, nonnegativeLebesgueMeasure.real
        (Set.Ioc (u i) (v i) ∩ Set.Ioc (x i) (y i)) := by
  induction n with
  | zero =>
      rw [chainIntegralLp_zero hB u v, chainIntegralLp_zero hB x y, L2.inner_def]
      have hone : (fun w ↦ inner ℝ ((Lp.const 2 P (1 : ℝ) : W → ℝ) w)
          ((Lp.const 2 P (1 : ℝ) : W → ℝ) w)) =ᵐ[P] fun _ ↦ (1 : ℝ) := by
        filter_upwards [Lp.coeFn_const 2 P (1 : ℝ), Lp.coeFn_const 2 P (1 : ℝ)]
          with w h1 h2
        rw [h1]
        simp only [Function.const_apply, RCLike.inner_apply, conj_trivial, one_mul]
      rw [integral_congr_ae hone]
      simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one,
        one_smul, Finset.univ_eq_empty, Finset.prod_empty]
  | succ n ih =>
      rw [inner_chainIntegralLp_succ hB hsm u v x y huv hxy huord hxord,
        ih (fun i ↦ u i.castSucc) (fun i ↦ v i.castSucc)
          (fun i ↦ x i.castSucc) (fun i ↦ y i.castSucc)
          (fun i ↦ huv i.castSucc) (fun i ↦ hxy i.castSucc)
          (fun i j hij ↦ huord i.castSucc j.castSucc
            (Fin.castSucc_lt_castSucc_iff.mpr hij))
          (fun i j hij ↦ hxord i.castSucc j.castSucc
            (Fin.castSucc_lt_castSucc_iff.mpr hij)),
        Fin.prod_univ_castSucc, mul_comm]

omit [CompleteSpace W] [BorelSpace W] in
/-- Ordered Brownian chain products of different orders are orthogonal in `L²(P)`. -/
theorem inner_chainIntegralLp_of_ne
    (hB : IsPreBrownianReal B P) (hsm : ∀ s, StronglyMeasurable (B s))
    {m n : ℕ} (u v : Fin m → ℝ≥0) (x y : Fin n → ℝ≥0)
    (huv : ∀ i, u i ≤ v i) (hxy : ∀ i, x i ≤ y i)
    (huord : ∀ i j, i < j → v i ≤ u j)
    (hxord : ∀ i j, i < j → y i ≤ x j)
    (hmn : m ≠ n) :
    inner ℝ (chainIntegralLp hB u v) (chainIntegralLp hB x y) = 0 := by
  induction m generalizing n with
  | zero =>
      cases n with
      | zero => exact (hmn rfl).elim
      | succ n =>
          rw [chainIntegralLp_zero hB u v, real_inner_comm,
            ← integral_eq_inner_const,
            integral_chainIntegralLp_succ hB hsm x y hxy hxord]
  | succ m ih =>
      cases n with
      | zero =>
          rw [chainIntegralLp_zero hB x y, ← integral_eq_inner_const,
            integral_chainIntegralLp_succ hB hsm u v huv huord]
      | succ n =>
          rw [inner_chainIntegralLp_succ_succ hB hsm u v x y huv hxy huord hxord,
            ih (fun i ↦ u i.castSucc) (fun i ↦ v i.castSucc)
              (fun i ↦ x i.castSucc) (fun i ↦ y i.castSucc)
              (fun i ↦ huv i.castSucc) (fun i ↦ hxy i.castSucc)
              (fun i j hij ↦ huord i.castSucc j.castSucc
                (Fin.castSucc_lt_castSucc_iff.mpr hij))
              (fun i j hij ↦ hxord i.castSucc j.castSucc
                (Fin.castSucc_lt_castSucc_iff.mpr hij))
              (fun h ↦ hmn (congrArg Nat.succ h)),
            mul_zero]

namespace BrownianIteratedConstruction

/-- Endpoint data for an ordered time box contained in the strict simplex. -/
structure OrderedBoxIndex (n : ℕ) where
  /-- The lower endpoint of each component interval. -/
  u : Fin n → ℝ≥0
  /-- The upper endpoint of each component interval. -/
  v : Fin n → ℝ≥0
  /-- Each component interval has ordered endpoints. -/
  valid : ∀ i, u i ≤ v i
  /-- Earlier intervals lie entirely before later intervals. -/
  ordered : ∀ i j, i < j → v i ≤ u j

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [MeasurableSpace W]
    [BorelSpace W] [SecondCountableTopology W] [IsGaussian P] in
/-- An ordered box is contained in the strict time simplex. -/
theorem orderedBox_subset_simplex {n : ℕ} (a : OrderedBoxIndex n) :
    orderedBox a.u a.v ⊆ simplex ℝ≥0 n := by
  intro t ht
  rw [mem_simplex]
  intro i j hij
  have hit : t i ∈ Set.Ioc (a.u i) (a.v i) := ht i (Set.mem_univ i)
  have hjt : t j ∈ Set.Ioc (a.u j) (a.v j) := ht j (Set.mem_univ j)
  exact lt_of_le_of_lt (hit.2.trans (a.ordered i j hij)) hjt.1

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [MeasurableSpace W]
    [BorelSpace W] [SecondCountableTopology W] [IsGaussian P] in
/-- An ordered box has finite measure after restriction to the simplex. -/
theorem restrictedSimplexMeasure_orderedBox_ne_top {n : ℕ} (a : OrderedBoxIndex n) :
    ((iteratedKernelMeasure n).restrict (simplex ℝ≥0 n)) (orderedBox a.u a.v) ≠ ∞ := by
  exact ne_top_of_le_ne_top (iteratedKernelMeasure_orderedBox_ne_top a.u a.v)
    (Measure.restrict_apply_le _ _)

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [MeasurableSpace W]
    [BorelSpace W] [SecondCountableTopology W] [IsGaussian P] in
/-- The indicator of an ordered box in the restricted-simplex kernel space. -/
noncomputable def orderedBoxSimplexKernel {n : ℕ} (a : OrderedBoxIndex n) :
    IteratedIntegralConstruction.SimplexKernel n :=
  indicatorConstLp 2 (measurableSet_orderedBox a.u a.v)
    (restrictedSimplexMeasure_orderedBox_ne_top a) (1 : ℝ)

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [MeasurableSpace W]
    [BorelSpace W] [SecondCountableTopology W] [IsGaussian P] in
/-- The restricted-simplex Gram matrix of ordered-box indicators. -/
theorem inner_orderedBoxSimplexKernel {n : ℕ} (a b : OrderedBoxIndex n) :
    inner ℝ (orderedBoxSimplexKernel a) (orderedBoxSimplexKernel b) =
      ∏ i, nonnegativeLebesgueMeasure.real
        (Set.Ioc (a.u i) (a.v i) ∩ Set.Ioc (b.u i) (b.v i)) := by
  rw [orderedBoxSimplexKernel, orderedBoxSimplexKernel,
    L2.real_inner_indicatorConstLp_one_indicatorConstLp_one
      (measurableSet_orderedBox a.u a.v) (measurableSet_orderedBox b.u b.v)
      (restrictedSimplexMeasure_orderedBox_ne_top a)
      (restrictedSimplexMeasure_orderedBox_ne_top b)]
  have hsubset : orderedBox a.u a.v ∩ orderedBox b.u b.v ⊆ simplex ℝ≥0 n :=
    Set.inter_subset_left.trans (orderedBox_subset_simplex a)
  rw [measureReal_def, Measure.restrict_apply
    ((measurableSet_orderedBox a.u a.v).inter (measurableSet_orderedBox b.u b.v)),
    Set.inter_eq_left.mpr hsubset]
  change ((iteratedKernelMeasure n)
    ((Set.univ.pi fun i ↦ Set.Ioc (a.u i) (a.v i)) ∩
      Set.univ.pi fun i ↦ Set.Ioc (b.u i) (b.v i))).toReal = _
  rw [← Set.pi_inter_distrib, iteratedKernelMeasure, Measure.pi_pi, ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro i _
  rfl

omit [CompleteSpace W] [BorelSpace W] in
/-- The source ordered-box kernel and its Brownian chain value have the same Gram matrix. -/
theorem inner_orderedBoxSimplexKernel_eq_chainIntegralLp
    (hB : IsPreBrownianReal B P) (hsm : ∀ s, StronglyMeasurable (B s))
    {n : ℕ} (a b : OrderedBoxIndex n) :
    inner ℝ (orderedBoxSimplexKernel a) (orderedBoxSimplexKernel b) =
      inner ℝ (chainIntegralLp hB a.u a.v) (chainIntegralLp hB b.u b.v) := by
  rw [inner_orderedBoxSimplexKernel,
    inner_chainIntegralLp hB hsm a.u a.v b.u b.v a.valid b.valid a.ordered b.ordered]

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [MeasurableSpace W]
    [BorelSpace W] [SecondCountableTopology W] [IsGaussian P] in
/-- Formal finite combinations of ordered-box indicators in simplex `L²`. -/
noncomputable def orderedBoxToSimplexKernel (n : ℕ) :
    (OrderedBoxIndex n →₀ ℝ) →ₗ[ℝ] IteratedIntegralConstruction.SimplexKernel n :=
  Finsupp.linearCombination ℝ orderedBoxSimplexKernel

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
/-- The corresponding formal finite combinations of Brownian chain products. -/
noncomputable def orderedBoxToRandom (hB : IsPreBrownianReal B P) (n : ℕ) :
    (OrderedBoxIndex n →₀ ℝ) →ₗ[ℝ] RandomL2 P :=
  Finsupp.linearCombination ℝ fun a ↦ chainIntegralLp hB a.u a.v

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [MeasurableSpace W]
    [BorelSpace W] [SecondCountableTopology W] [IsGaussian P] in
theorem orderedBoxToSimplexKernel_single {n : ℕ} (a : OrderedBoxIndex n) (c : ℝ) :
    orderedBoxToSimplexKernel n (Finsupp.single a c) = c • orderedBoxSimplexKernel a :=
  Finsupp.linearCombination_single _ _ _

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
theorem orderedBoxToRandom_single (hB : IsPreBrownianReal B P)
    {n : ℕ} (a : OrderedBoxIndex n) (c : ℝ) :
    orderedBoxToRandom hB n (Finsupp.single a c) = c • chainIntegralLp hB a.u a.v :=
  Finsupp.linearCombination_single _ _ _

omit [CompleteSpace W] [BorelSpace W] in
/-- The two formal-combination maps have identical Gram matrices. -/
theorem inner_orderedBoxToRandom
    (hB : IsPreBrownianReal B P) (hsm : ∀ s, StronglyMeasurable (B s))
    {n : ℕ} (c d : OrderedBoxIndex n →₀ ℝ) :
    inner ℝ (orderedBoxToRandom hB n c) (orderedBoxToRandom hB n d) =
      inner ℝ (orderedBoxToSimplexKernel n c) (orderedBoxToSimplexKernel n d) := by
  unfold orderedBoxToRandom orderedBoxToSimplexKernel
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, sum_inner, inner_sum,
    real_inner_smul_left, real_inner_smul_right,
    ← inner_orderedBoxSimplexKernel_eq_chainIntegralLp hB hsm]

omit [CompleteSpace W] [BorelSpace W] in
/-- Norm equality on formal ordered-box combinations. -/
theorem norm_orderedBoxToRandom
    (hB : IsPreBrownianReal B P) (hsm : ∀ s, StronglyMeasurable (B s))
    {n : ℕ} (c : OrderedBoxIndex n →₀ ℝ) :
    ‖orderedBoxToRandom hB n c‖ = ‖orderedBoxToSimplexKernel n c‖ := by
  have h := inner_orderedBoxToRandom hB hsm c c
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [MeasurableSpace W]
    [BorelSpace W] [SecondCountableTopology W] [IsGaussian P] in
/-- The deterministic density input needed to complete ordered-box values to the whole simplex. -/
def OrderedBoxDense (n : ℕ) : Prop :=
  DenseRange (orderedBoxToSimplexKernel n)

omit [CompleteSpace W] [BorelSpace W] in
/-- Completion of the Brownian ordered-box map to all square-integrable simplex kernels. -/
noncomputable def simplexIntegral
    (hB : IsPreBrownianReal B P) (n : ℕ) :
    IteratedIntegralConstruction.SimplexKernel n →L[ℝ] RandomL2 P :=
  (orderedBoxToRandom hB n).extendOfNorm (orderedBoxToSimplexKernel n)

omit [CompleteSpace W] [BorelSpace W] in
/-- The completed map agrees with the Brownian map on every formal combination. -/
theorem simplexIntegral_orderedBoxToSimplexKernel
    (hB : IsPreBrownianReal B P) (hsm : ∀ s, StronglyMeasurable (B s))
    {n : ℕ} (hdense : OrderedBoxDense n) (c : OrderedBoxIndex n →₀ ℝ) :
    simplexIntegral hB n (orderedBoxToSimplexKernel n c) =
      orderedBoxToRandom hB n c := by
  exact LinearMap.extendOfNorm_eq hdense
    ⟨1, fun d ↦ by rw [norm_orderedBoxToRandom hB hsm d, one_mul]⟩ c

omit [CompleteSpace W] [BorelSpace W] in
/-- In particular, the completed map sends an ordered-box indicator to its chain product. -/
theorem simplexIntegral_orderedBoxSimplexKernel
    (hB : IsPreBrownianReal B P) (hsm : ∀ s, StronglyMeasurable (B s))
    {n : ℕ} (hdense : OrderedBoxDense n) (a : OrderedBoxIndex n) :
    simplexIntegral hB n (orderedBoxSimplexKernel a) =
      chainIntegralLp hB a.u a.v := by
  have h := simplexIntegral_orderedBoxToSimplexKernel hB hsm hdense
    (Finsupp.single a (1 : ℝ))
  simpa only [orderedBoxToSimplexKernel_single, orderedBoxToRandom_single, one_smul] using h

omit [CompleteSpace W] [BorelSpace W] in
/-- The completed Brownian simplex integral preserves inner products. -/
theorem inner_simplexIntegral
    (hB : IsPreBrownianReal B P) (hsm : ∀ s, StronglyMeasurable (B s))
    {n : ℕ} (hdense : OrderedBoxDense n)
    (f g : IteratedIntegralConstruction.SimplexKernel n) :
    inner ℝ (simplexIntegral hB n f) (simplexIntegral hB n g) =
      inner ℝ f g := by
  refine hdense.induction_on₂
    (p := fun f g ↦ inner ℝ (simplexIntegral hB n f)
      (simplexIntegral hB n g) = inner ℝ f g) ?_ ?_ f g
  · exact isClosed_eq
      (((simplexIntegral hB n).continuous.comp continuous_fst).inner
        ((simplexIntegral hB n).continuous.comp continuous_snd))
      (continuous_fst.inner continuous_snd)
  · intro c d
    rw [simplexIntegral_orderedBoxToSimplexKernel hB hsm hdense,
      simplexIntegral_orderedBoxToSimplexKernel hB hsm hdense,
      inner_orderedBoxToRandom hB hsm]

omit [CompleteSpace W] [BorelSpace W] in
/-- Formal Brownian combinations of different orders are orthogonal. -/
theorem inner_orderedBoxToRandom_of_ne
    (hB : IsPreBrownianReal B P) (hsm : ∀ s, StronglyMeasurable (B s))
    {m n : ℕ} (hmn : m ≠ n)
    (c : OrderedBoxIndex m →₀ ℝ) (d : OrderedBoxIndex n →₀ ℝ) :
    inner ℝ (orderedBoxToRandom hB m c) (orderedBoxToRandom hB n d) = 0 := by
  unfold orderedBoxToRandom
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, sum_inner, inner_sum,
    real_inner_smul_left, real_inner_smul_right]
  apply Finset.sum_eq_zero
  intro a _ha
  apply Finset.sum_eq_zero
  intro b _hb
  rw [inner_chainIntegralLp_of_ne hB hsm b.u b.v a.u a.v b.valid a.valid
    b.ordered a.ordered hmn, mul_zero, mul_zero]

omit [CompleteSpace W] [BorelSpace W] in
/-- Every formal combination of positive-order Brownian chains is centered. -/
theorem integral_orderedBoxToRandom_succ
    (hB : IsPreBrownianReal B P) (hsm : ∀ s, StronglyMeasurable (B s))
    {n : ℕ} (c : OrderedBoxIndex (n + 1) →₀ ℝ) :
    ∫ w, orderedBoxToRandom hB (n + 1) c w ∂P = 0 := by
  rw [← CameronMartin.expectationMap_apply]
  unfold orderedBoxToRandom
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
  apply Finset.sum_eq_zero
  intro a _ha
  rw [map_smul, CameronMartin.expectationMap_apply,
    integral_chainIntegralLp_succ hB hsm a.u a.v a.valid a.ordered, smul_zero]

omit [CompleteSpace W] [BorelSpace W] in
/-- The completed simplex integral is centered at every positive order. -/
theorem integral_simplexIntegral_succ
    (hB : IsPreBrownianReal B P) (hsm : ∀ s, StronglyMeasurable (B s))
    {n : ℕ} (hdense : OrderedBoxDense (n + 1))
    (f : IteratedIntegralConstruction.SimplexKernel (n + 1)) :
    ∫ w, simplexIntegral hB (n + 1) f w ∂P = 0 := by
  rw [← CameronMartin.expectationMap_apply]
  let L := (CameronMartin.expectationMap P).comp (simplexIntegral hB (n + 1))
  change L f = 0
  refine hdense.induction_on f (isClosed_eq L.continuous continuous_const) ?_
  intro c
  change CameronMartin.expectationMap P
    (simplexIntegral hB (n + 1) (orderedBoxToSimplexKernel (n + 1) c)) = 0
  rw [simplexIntegral_orderedBoxToSimplexKernel hB hsm hdense,
    CameronMartin.expectationMap_apply, integral_orderedBoxToRandom_succ hB hsm]

omit [CompleteSpace W] [BorelSpace W] in
/-- Completed Brownian simplex integrals of different orders are orthogonal. -/
theorem inner_simplexIntegral_of_ne
    (hB : IsPreBrownianReal B P) (hsm : ∀ s, StronglyMeasurable (B s))
    {m n : ℕ} (hmn : m ≠ n) (hdense_m : OrderedBoxDense m)
    (hdense_n : OrderedBoxDense n)
    (f : IteratedIntegralConstruction.SimplexKernel m)
    (g : IteratedIntegralConstruction.SimplexKernel n) :
    inner ℝ (simplexIntegral hB m f) (simplexIntegral hB n g) = 0 := by
  refine hdense_m.induction_on f
    (isClosed_eq ((simplexIntegral hB m).continuous.inner continuous_const)
      continuous_const) ?_
  intro c
  refine hdense_n.induction_on g
    (isClosed_eq (continuous_const.inner (simplexIntegral hB n).continuous)
      continuous_const) ?_
  intro d
  rw [simplexIntegral_orderedBoxToSimplexKernel hB hsm hdense_m,
    simplexIntegral_orderedBoxToSimplexKernel hB hsm hdense_n,
    inner_orderedBoxToRandom_of_ne hB hsm hmn]

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [MeasurableSpace W]
    [BorelSpace W] [SecondCountableTopology W] [IsGaussian P] in
theorem restrictedSimplexMeasure_le (n : ℕ) :
    (iteratedKernelMeasure n).restrict (simplex ℝ≥0 n) ≤
      (1 : ℝ≥0∞) • iteratedKernelMeasure n := by
  simpa only [one_smul] using
    (Measure.restrict_le_self :
      (iteratedKernelMeasure n).restrict (simplex ℝ≥0 n) ≤ iteratedKernelMeasure n)

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [MeasurableSpace W]
    [BorelSpace W] [SecondCountableTopology W] [IsGaussian P] in
/-- Restriction of a full product kernel to the strict simplex. -/
noncomputable def restrictToSimplex (n : ℕ) :
    IteratedKernel n →L[ℝ] IteratedIntegralConstruction.SimplexKernel n :=
  Lp.LpToLpOfMeasureLeSMul (p := (2 : ℝ≥0∞)) (c := 1)
    (by norm_num) (restrictedSimplexMeasure_le n)

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [MeasurableSpace W]
    [BorelSpace W] [SecondCountableTopology W] [IsGaussian P] in
theorem restrictToSimplex_ae (n : ℕ) (f : IteratedKernel n) :
    restrictToSimplex n f =ᵐ[(iteratedKernelMeasure n).restrict (simplex ℝ≥0 n)] f :=
  Lp.coeFn_LpToLpOfMeasureLeSMul (p := (2 : ℝ≥0∞)) (c := 1)
    (by norm_num) (restrictedSimplexMeasure_le n) f

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [MeasurableSpace W]
    [BorelSpace W] [SecondCountableTopology W] [IsGaussian P] in
/-- Restricting an ordered-box kernel gives its simplex-space indicator. -/
theorem restrictToSimplex_boxKernel {n : ℕ} (a : OrderedBoxIndex n) :
    restrictToSimplex n (boxKernel a.u a.v) = orderedBoxSimplexKernel a := by
  apply Lp.ext
  unfold boxKernel orderedBoxSimplexKernel
  filter_upwards [restrictToSimplex_ae n _,
    ae_restrict_of_ae (indicatorConstLp_coeFn (p := 2) (μ := iteratedKernelMeasure n)
      (hs := measurableSet_orderedBox a.u a.v) (c := (1 : ℝ))),
    (indicatorConstLp_coeFn (p := 2)
      (μ := (iteratedKernelMeasure n).restrict (simplex ℝ≥0 n))
      (hs := measurableSet_orderedBox a.u a.v) (c := (1 : ℝ)))]
      with t hrestrict hfull hsimp
  exact hrestrict.trans (hfull.trans hsimp.symm)

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [MeasurableSpace W]
    [BorelSpace W] [SecondCountableTopology W] [IsGaussian P] in
/-- Inner products after restriction are exactly the simplex integrals. -/
theorem inner_restrictToSimplex (n : ℕ) (f g : IteratedKernel n) :
    inner ℝ (restrictToSimplex n f) (restrictToSimplex n g) =
      ∫ t in simplex ℝ≥0 n, inner ℝ (f t) (g t) ∂iteratedKernelMeasure n := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [restrictToSimplex_ae n f, restrictToSimplex_ae n g] with t hft hgt
  rw [hft, hgt]

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [MeasurableSpace W]
    [BorelSpace W] [SecondCountableTopology W] [IsGaussian P] in
/-- Restriction to the simplex is contractive. -/
theorem norm_restrictToSimplex_le (n : ℕ) (f : IteratedKernel n) :
    ‖restrictToSimplex n f‖ ≤ ‖f‖ := by
  have hop : ‖restrictToSimplex n‖ ≤ 1 := by
    simpa only [restrictToSimplex, ENNReal.toReal_one, Real.one_rpow] using
      (Lp.norm_LpToLpOfMeasureLeSMul_le
        (E := ℝ) (p := (2 : ℝ≥0∞)) (c := 1)
        (by norm_num) (restrictedSimplexMeasure_le n))
  calc
    ‖restrictToSimplex n f‖ ≤ ‖restrictToSimplex n‖ * ‖f‖ :=
      ContinuousLinearMap.le_opNorm (restrictToSimplex n) f
    _ ≤ 1 * ‖f‖ := mul_le_mul_of_nonneg_right hop (norm_nonneg f)
    _ = ‖f‖ := one_mul _

omit [CompleteSpace W] [BorelSpace W] in
/-- The positive-order Brownian integral on full product kernels, obtained by restricting to the
simplex and applying the completed ordered-box map. -/
noncomputable def positiveIntegralCLM (hB : IsPreBrownianReal B P) (n : ℕ) :
    IteratedKernel (n + 1) →L[ℝ] RandomL2 P :=
  (simplexIntegral hB (n + 1)).comp (restrictToSimplex (n + 1))

omit [CompleteSpace W] [BorelSpace W] in
/-- The positive-order full-kernel operator has the required Brownian ordered-box value. -/
theorem positiveIntegralCLM_box
    (hB : IsPreBrownianReal B P) (hsm : ∀ s, StronglyMeasurable (B s))
    {n : ℕ} (hdense : OrderedBoxDense (n + 1)) (a : OrderedBoxIndex (n + 1)) :
    positiveIntegralCLM hB n (boxKernel a.u a.v) = chainIntegralLp hB a.u a.v := by
  rw [positiveIntegralCLM, ContinuousLinearMap.comp_apply, restrictToSimplex_boxKernel,
    simplexIntegral_orderedBoxSimplexKernel hB hsm hdense]

omit [CompleteSpace W] [BorelSpace W] in
/-- Polarized simplex isometry for the completed positive-order operator. -/
theorem inner_positiveIntegralCLM
    (hB : IsPreBrownianReal B P) (hsm : ∀ s, StronglyMeasurable (B s))
    {n : ℕ} (hdense : OrderedBoxDense (n + 1))
    (f g : IteratedKernel (n + 1)) :
    inner ℝ (positiveIntegralCLM hB n f) (positiveIntegralCLM hB n g) =
      ∫ t in simplex ℝ≥0 (n + 1), inner ℝ (f t) (g t)
        ∂iteratedKernelMeasure (n + 1) := by
  rw [positiveIntegralCLM, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, inner_simplexIntegral hB hsm hdense,
    inner_restrictToSimplex]

omit [CompleteSpace W] [BorelSpace W] in
/-- Every completed positive-order operator is centered. -/
theorem integral_positiveIntegralCLM
    (hB : IsPreBrownianReal B P) (hsm : ∀ s, StronglyMeasurable (B s))
    {n : ℕ} (hdense : OrderedBoxDense (n + 1)) (f : IteratedKernel (n + 1)) :
    ∫ w, positiveIntegralCLM hB n f w ∂P = 0 := by
  exact integral_simplexIntegral_succ hB hsm hdense (restrictToSimplex (n + 1) f)

omit [CompleteSpace W] [BorelSpace W] in
/-- Completed positive-order operators of different orders are orthogonal. -/
theorem inner_positiveIntegralCLM_of_ne
    (hB : IsPreBrownianReal B P) (hsm : ∀ s, StronglyMeasurable (B s))
    {m n : ℕ} (hmn : m ≠ n) (hdense_m : OrderedBoxDense (m + 1))
    (hdense_n : OrderedBoxDense (n + 1))
    (f : IteratedKernel (m + 1)) (g : IteratedKernel (n + 1)) :
    inner ℝ (positiveIntegralCLM hB m f) (positiveIntegralCLM hB n g) = 0 := by
  exact inner_simplexIntegral_of_ne hB hsm (fun h ↦ hmn (Nat.succ.inj h))
    hdense_m hdense_n (restrictToSimplex (m + 1) f) (restrictToSimplex (n + 1) g)

omit [CompleteSpace W] [BorelSpace W] in
/-- The completed positive-order operator is contractive on the full product kernel space. -/
theorem norm_positiveIntegralCLM_le
    (hB : IsPreBrownianReal B P) (hsm : ∀ s, StronglyMeasurable (B s))
    {n : ℕ} (hdense : OrderedBoxDense (n + 1)) (f : IteratedKernel (n + 1)) :
    ‖positiveIntegralCLM hB n f‖ ≤ ‖f‖ := by
  have hinner := inner_simplexIntegral hB hsm hdense
    (restrictToSimplex (n + 1) f) (restrictToSimplex (n + 1) f)
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hinner
  have hnorm : ‖positiveIntegralCLM hB n f‖ = ‖restrictToSimplex (n + 1) f‖ := by
    change ‖simplexIntegral hB (n + 1) (restrictToSimplex (n + 1) f)‖ = _
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hinner
  rw [hnorm]
  exact norm_restrictToSimplex_le (n + 1) f

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [MeasurableSpace W]
    [BorelSpace W] [SecondCountableTopology W] [IsGaussian P] in
/-- Density of ordered boxes at every positive order.  This is the sole deterministic analytic
input to the completed Brownian family below. -/
def PositiveOrderedBoxDense : Prop :=
  ∀ n : ℕ, OrderedBoxDense (n + 1)

omit [CompleteSpace W] [BorelSpace W] in
/-- The completed all-order operator: canonical constants at order zero and Brownian simplex
integrals at every positive order. -/
noncomputable def integralCLM (hB : IsPreBrownianReal B P) :
    (n : ℕ) → IteratedKernel n →L[ℝ] RandomL2 P
  | 0 => iteratedIntegralCLM hB 0
  | n + 1 => positiveIntegralCLM hB n

omit [CompleteSpace W] [BorelSpace W] in
theorem integralCLM_sameOrder
    (hB : IsPreBrownianReal B P) (hsm : ∀ s, StronglyMeasurable (B s))
    (hdense : PositiveOrderedBoxDense) (n : ℕ) (f g : IteratedKernel n) :
    inner ℝ (integralCLM hB n f) (integralCLM hB n g) =
      ∫ t in simplex ℝ≥0 n, inner ℝ (f t) (g t) ∂iteratedKernelMeasure n := by
  cases n with
  | zero => exact inner_iteratedIntegralCLM hB 0 f g
  | succ n => exact inner_positiveIntegralCLM hB hsm (hdense n) f g

omit [CompleteSpace W] [BorelSpace W] in
theorem integralCLM_centered
    (hB : IsPreBrownianReal B P) (hsm : ∀ s, StronglyMeasurable (B s))
    (hdense : PositiveOrderedBoxDense) (n : ℕ) (hn : 0 < n) (f : IteratedKernel n) :
    ∫ w, integralCLM hB n f w ∂P = 0 := by
  cases n with
  | zero => exact (Nat.lt_irrefl 0 hn).elim
  | succ n => exact integral_positiveIntegralCLM hB hsm (hdense n) f

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
theorem integralCLM_zeroOrder (hB : IsPreBrownianReal B P) (f : IteratedKernel 0) :
    (fun w ↦ integralCLM hB 0 f w) =ᵐ[P]
      fun _ ↦ ∫ t, f t ∂iteratedKernelMeasure 0 :=
  iteratedIntegralCLM_zeroOrder hB f

omit [CompleteSpace W] [BorelSpace W] in
/-- The canonical zeroth-order output is orthogonal to every centered completed positive output. -/
theorem inner_integralCLM_zero_positive
    (hB : IsPreBrownianReal B P) (hsm : ∀ s, StronglyMeasurable (B s))
    {n : ℕ} (hdense : OrderedBoxDense (n + 1))
    (f : IteratedKernel 0) (g : IteratedKernel (n + 1)) :
    inner ℝ (integralCLM hB 0 f) (positiveIntegralCLM hB n g) = 0 := by
  let c := ∫ t, f t ∂iteratedKernelMeasure 0
  rw [L2.inner_def]
  calc
    (∫ w, inner ℝ (integralCLM hB 0 f w) (positiveIntegralCLM hB n g w) ∂P) =
        ∫ w, positiveIntegralCLM hB n g w * c ∂P := by
      apply integral_congr_ae
      filter_upwards [integralCLM_zeroOrder hB f] with w hw
      rw [hw]
      simp only [RCLike.inner_apply, conj_trivial, c]
    _ = (∫ w, positiveIntegralCLM hB n g w ∂P) * c := integral_mul_const _ _
    _ = 0 := by rw [integral_positiveIntegralCLM hB hsm hdense, zero_mul]

omit [CompleteSpace W] [BorelSpace W] in
theorem integralCLM_differentOrder
    (hB : IsPreBrownianReal B P) (hsm : ∀ s, StronglyMeasurable (B s))
    (hdense : PositiveOrderedBoxDense) {m n : ℕ} (hmn : m ≠ n)
    (f : IteratedKernel m) (g : IteratedKernel n) :
    inner ℝ (integralCLM hB m f) (integralCLM hB n g) = 0 := by
  cases m with
  | zero =>
      cases n with
      | zero => exact (hmn rfl).elim
      | succ n => exact inner_integralCLM_zero_positive hB hsm (hdense n) f g
  | succ m =>
      cases n with
      | zero =>
          rw [real_inner_comm]
          exact inner_integralCLM_zero_positive hB hsm (hdense m) g f
      | succ n =>
          exact inner_positiveIntegralCLM_of_ne hB hsm
            (fun h ↦ hmn (congrArg Nat.succ h)) (hdense m) (hdense n) f g

omit [CompleteSpace W] [BorelSpace W] in
theorem integralCLM_norm_le
    (hB : IsPreBrownianReal B P) (hsm : ∀ s, StronglyMeasurable (B s))
    (hdense : PositiveOrderedBoxDense) (n : ℕ) (f : IteratedKernel n) :
    ‖integralCLM hB n f‖ ≤ ‖f‖ := by
  cases n with
  | zero => exact norm_iteratedIntegralCLM_le hB 0 f
  | succ n => exact norm_positiveIntegralCLM_le hB hsm (hdense n) f

omit [CompleteSpace W] [BorelSpace W] in
/-- A completed Brownian iterated-integral family, conditional only on ordered-box density in the
restricted simplex kernel spaces. -/
noncomputable def family
    (hB : IsPreBrownianReal B P) (hsm : ∀ s, StronglyMeasurable (B s))
    (hdense : PositiveOrderedBoxDense) : IteratedIntegralFamily P where
  integral := integralCLM hB
  sameOrder := integralCLM_sameOrder hB hsm hdense
  centered := integralCLM_centered hB hsm hdense
  zeroOrder := integralCLM_zeroOrder hB
  differentOrder := integralCLM_differentOrder hB hsm hdense
  norm_integral_le := integralCLM_norm_le hB hsm hdense

omit [CompleteSpace W] [BorelSpace W] in
/-- The completed family satisfies the Brownian ordered-box compatibility at every order. -/
theorem family_isBrownian
    (hB : IsPreBrownianReal B P) (hsm : ∀ s, StronglyMeasurable (B s))
    (hdense : PositiveOrderedBoxDense) :
    (family hB hsm hdense).IsBrownian B := by
  apply IteratedIntegralFamily.IsBrownian.of_pos
  intro n hn u v huv hord
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  let a : OrderedBoxIndex (k + 1) := ⟨u, v, huv, hord⟩
  have hbox := positiveIntegralCLM_box hB hsm (hdense k) a
  change positiveIntegralCLM hB k (boxKernel u v) = chainIntegralLp hB u v at hbox
  rw [show (family hB hsm hdense).integral (k + 1) = positiveIntegralCLM hB k from rfl,
    hbox]
  exact coeFn_chainIntegralLp hB u v

end BrownianIteratedConstruction

end Malliavin

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
