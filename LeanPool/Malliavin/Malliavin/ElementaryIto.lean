/-
Copyright (c) 2026 The lean-malliavin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-malliavin contributors
-/
module

public import LeanPool.Malliavin.Malliavin.ClarkOcone

/-!
# The Itô isometry on adapted elementary processes

This file proves the cross-inner-product identities needed to assemble the Brownian Itô integral
from the dense elementary span. Terminal Brownian values are orthogonal on chronologically
disjoint intervals, and on a common interval their inner product agrees with that of the
corresponding predictable tensors. These are the diagonal and off-diagonal ingredients of the
finite-step Itô isometry.

The first part records these identities for the elementary values attached to an abstract
`ClarkOconeFamily`. The second part removes that dependency: `elementaryBrownianValue` constructs
`Z (B_b - B_a)` directly from a pre-Brownian coordinate process and its natural filtration, while
`inner_partitionElementaryBrownianValue` and `norm_partitionElementaryBrownianValue` prove the
construction-level Itô isometry for every adapted step process on a common partition. Exact
comparison theorems connect these genuine Brownian values back to the family-level API.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace

noncomputable
section

namespace Malliavin

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}

/-- Terminal values of chronologically disjoint adapted elementary terms are orthogonal. -/
theorem ClarkOconeFamily.inner_elementaryIntegralValue_eq_zero_of_le
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›} (C : ClarkOconeFamily B P 𝓕)
    {a b c d : ℝ≥0} (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (Z : lpMeas ℝ ℝ (𝓕 a) 2 P) (Y : lpMeas ℝ ℝ (𝓕 c) 2 P) :
    inner ℝ (C.elementaryIntegralValue hab Z) (C.elementaryIntegralValue hcd Y) = 0 := by
  have hac : a ≤ c := hab.trans hbc
  have hBadapted : StronglyAdapted 𝓕 B := by
    rw [C.naturalFiltration]
    exact Filtration.stronglyAdapted_natural C.stronglyMeasurable
  have hZc : AEStronglyMeasurable[𝓕 c] (Z : W → ℝ) P :=
    AEStronglyMeasurable.mono (𝓕.mono hac) (lpMeas.aestronglyMeasurable Z)
  have hYc : AEStronglyMeasurable[𝓕 c] (Y : W → ℝ) P :=
    lpMeas.aestronglyMeasurable Y
  have hΔabc : AEStronglyMeasurable[𝓕 c] (fun w ↦ B b w - B a w) P :=
    ((hBadapted.stronglyMeasurable_le hbc).sub
      (hBadapted.stronglyMeasurable_le hac)).aestronglyMeasurable
  have hG : AEStronglyMeasurable[𝓕 c]
      (fun w ↦ ((Z : W → ℝ) w * (B b w - B a w)) * (Y : W → ℝ) w) P :=
    (hZc.mul hΔabc).mul hYc
  have hind := C.indep_increment_of_adapted hcd hG
  have hΔcd : AEStronglyMeasurable (fun w ↦ B d w - B c w) P :=
    C.isPreBrownian.isGaussianProcess.hasGaussianLaw_sub.memLp_two.aestronglyMeasurable
  have hGamb : AEStronglyMeasurable
      (fun w ↦ ((Z : W → ℝ) w * (B b w - B a w)) * (Y : W → ℝ) w) P :=
    AEStronglyMeasurable.mono (𝓕.le c) hG
  have hfactor := hind.integral_mul_eq_mul_integral hΔcd hGamb
  rw [L2.inner_def]
  calc
    ∫ w, ⟪C.elementaryIntegralValue hab Z w,
        C.elementaryIntegralValue hcd Y w⟫_ℝ ∂P =
        ∫ w, (B d w - B c w) *
          (((Z : W → ℝ) w * (B b w - B a w)) * (Y : W → ℝ) w) ∂P := by
      apply integral_congr_ae
      filter_upwards [C.coeFn_elementaryIntegralValue hab Z,
        C.coeFn_elementaryIntegralValue hcd Y] with w hfirst hsecond
      rw [hfirst, hsecond]
      simp only [RCLike.inner_apply, conj_trivial]
      ring
    _ = (∫ w, B d w - B c w ∂P) *
        ∫ w, ((Z : W → ℝ) w * (B b w - B a w)) * (Y : W → ℝ) w ∂P := by
      simpa only [Pi.mul_apply] using hfactor
    _ = 0 := by
      rw [integral_sub (C.isPreBrownian.integrable_eval d)
          (C.isPreBrownian.integrable_eval c),
        C.isPreBrownian.integral_eval, C.isPreBrownian.integral_eval, sub_zero, zero_mul]

namespace LegacyTensor

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
/-- Chronologically disjoint elementary predictable terms are orthogonal in product `L²`. -/
theorem inner_elementaryPredictable_eq_zero_of_le
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) {a b c d : ℝ≥0} (hbc : b ≤ c)
    (Z : lpMeas ℝ ℝ (𝓕 a) 2 P) (Y : lpMeas ℝ ℝ (𝓕 c) 2 P) :
    inner ℝ (elementaryPredictable 𝓕 a b Z) (elementaryPredictable 𝓕 c d Y) = 0 := by
  change inner ℝ (elementaryPredictable 𝓕 a b Z : TimeProcessL2 P)
    (elementaryPredictable 𝓕 c d Y : TimeProcessL2 P) = 0
  rw [elementaryPredictable_coeLp, elementaryPredictable_coeLp, L2.inner_def]
  apply integral_eq_zero_of_ae
  have habInd : ∀ᵐ p : ℝ≥0 × W ∂legacyProduct nonnegativeLebesgueMeasure P,
      (iocIndicator a b : ℝ≥0 → ℝ) p.1 =
        (Set.Ioc a b).indicator (1 : ℝ≥0 → ℝ) p.1 :=
    legacyProduct_quasiMeasurePreserving_fst.ae_eq_comp
      (indicatorConstLp_coeFn (p := 2) (hs := measurableSet_Ioc)
        (hμs := nonnegativeLebesgueMeasure_Ioc_ne_top a b) (c := (1 : ℝ)))
  have hcdInd : ∀ᵐ p : ℝ≥0 × W ∂legacyProduct nonnegativeLebesgueMeasure P,
      (iocIndicator c d : ℝ≥0 → ℝ) p.1 =
        (Set.Ioc c d).indicator (1 : ℝ≥0 → ℝ) p.1 :=
    legacyProduct_quasiMeasurePreserving_fst.ae_eq_comp
      (indicatorConstLp_coeFn (p := 2) (hs := measurableSet_Ioc)
        (hμs := nonnegativeLebesgueMeasure_Ioc_ne_top c d) (c := (1 : ℝ)))
  have hdisj : Disjoint (Set.Ioc a b) (Set.Ioc c d) := by
    rw [Set.Ioc_disjoint_Ioc]
    exact (min_le_left b d).trans (hbc.trans (le_max_right a c))
  filter_upwards [coeFn_tensor (iocIndicator a b) (Z : RandomL2 P),
    coeFn_tensor (iocIndicator c d) (Y : RandomL2 P), habInd, hcdInd]
    with p hfirst hsecond habp hcdp
  rw [hfirst, hsecond, habp, hcdp]
  simp only [RCLike.inner_apply, conj_trivial]
  by_cases hp : p.1 ∈ Set.Ioc a b
  · have hp' : p.1 ∉ Set.Ioc c d := Set.disjoint_left.mp hdisj hp
    simp only [hp', not_false_eq_true, Set.indicator_of_notMem, zero_mul, hp,
      Set.indicator_of_mem, Pi.one_apply,
      one_mul, Pi.zero_apply]
  · simp only [hp, not_false_eq_true, Set.indicator_of_notMem, zero_mul, mul_zero, Pi.zero_apply]

end LegacyTensor

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
/-- Chronologically disjoint elementary predictable terms are orthogonal in product `L²`. -/
theorem inner_elementaryPredictable_eq_zero_of_le [SFinite P]
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) {a b c d : ℝ≥0} (hbc : b ≤ c)
    (Z : lpMeas ℝ ℝ (𝓕 a) 2 P) (Y : lpMeas ℝ ℝ (𝓕 c) 2 P) :
    inner ℝ (elementaryPredictable 𝓕 a b Z) (elementaryPredictable 𝓕 c d Y) = 0 := by
  change inner ℝ (elementaryPredictable 𝓕 a b Z : TimeProcessL2 P)
    (elementaryPredictable 𝓕 c d Y : TimeProcessL2 P) = 0
  rw [elementaryPredictable_coeLp, elementaryPredictable_coeLp, L2.inner_def]
  apply integral_eq_zero_of_ae
  have habInd : ∀ᵐ p : ℝ≥0 × W ∂nonnegativeLebesgueMeasure.prod P,
      (iocIndicator a b : ℝ≥0 → ℝ) p.1 =
        (Set.Ioc a b).indicator (1 : ℝ≥0 → ℝ) p.1 :=
    Measure.quasiMeasurePreserving_fst.ae_eq_comp
      (indicatorConstLp_coeFn (p := 2) (hs := measurableSet_Ioc)
        (hμs := nonnegativeLebesgueMeasure_Ioc_ne_top a b) (c := (1 : ℝ)))
  have hcdInd : ∀ᵐ p : ℝ≥0 × W ∂nonnegativeLebesgueMeasure.prod P,
      (iocIndicator c d : ℝ≥0 → ℝ) p.1 =
        (Set.Ioc c d).indicator (1 : ℝ≥0 → ℝ) p.1 :=
    Measure.quasiMeasurePreserving_fst.ae_eq_comp
      (indicatorConstLp_coeFn (p := 2) (hs := measurableSet_Ioc)
        (hμs := nonnegativeLebesgueMeasure_Ioc_ne_top c d) (c := (1 : ℝ)))
  have hdisj : Disjoint (Set.Ioc a b) (Set.Ioc c d) := by
    rw [Set.Ioc_disjoint_Ioc]
    exact (min_le_left b d).trans (hbc.trans (le_max_right a c))
  filter_upwards [coeFn_tensor (iocIndicator a b) (Z : RandomL2 P),
    coeFn_tensor (iocIndicator c d) (Y : RandomL2 P), habInd, hcdInd]
    with p hfirst hsecond habp hcdp
  rw [hfirst, hsecond, habp, hcdp]
  simp only [RCLike.inner_apply, conj_trivial]
  by_cases hp : p.1 ∈ Set.Ioc a b
  · have hp' : p.1 ∉ Set.Ioc c d := Set.disjoint_left.mp hdisj hp
    simp only [hp', not_false_eq_true, Set.indicator_of_notMem, zero_mul, hp,
      Set.indicator_of_mem, Pi.one_apply,
      one_mul, Pi.zero_apply]
  · simp only [hp, not_false_eq_true, Set.indicator_of_notMem, zero_mul, mul_zero, Pi.zero_apply]

/-- The Itô cross-inner-product identity for two chronologically disjoint elementary terms. -/
theorem ClarkOconeFamily.inner_elementaryIntegralValue_eq_inner_elementaryPredictable_of_le
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›} (C : ClarkOconeFamily B P 𝓕)
    {a b c d : ℝ≥0} (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (Z : lpMeas ℝ ℝ (𝓕 a) 2 P) (Y : lpMeas ℝ ℝ (𝓕 c) 2 P) :
    inner ℝ (C.elementaryIntegralValue hab Z) (C.elementaryIntegralValue hcd Y) =
      inner ℝ (elementaryPredictable 𝓕 a b Z) (elementaryPredictable 𝓕 c d Y) := by
  rw [C.inner_elementaryIntegralValue_eq_zero_of_le hab hbc hcd Z Y,
    inner_elementaryPredictable_eq_zero_of_le 𝓕 hbc Z Y]

/-- The Itô cross-inner-product identity for two elementary terms on the same interval. -/
theorem ClarkOconeFamily.inner_elementaryIntegralValue_eq_inner_elementaryPredictable_same
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›} (C : ClarkOconeFamily B P 𝓕)
    {a b : ℝ≥0} (hab : a ≤ b)
    (Z Y : lpMeas ℝ ℝ (𝓕 a) 2 P) :
    inner ℝ (C.elementaryIntegralValue hab Z) (C.elementaryIntegralValue hab Y) =
      inner ℝ (elementaryPredictable 𝓕 a b Z) (elementaryPredictable 𝓕 a b Y) := by
  have hZY : AEStronglyMeasurable[𝓕 a]
      (fun w ↦ (Z : W → ℝ) w * (Y : W → ℝ) w) P :=
    (lpMeas.aestronglyMeasurable Z).mul (lpMeas.aestronglyMeasurable Y)
  have hindSq : IndepFun (fun w ↦ (B b w - B a w) ^ 2)
      (fun w ↦ (Z : W → ℝ) w * (Y : W → ℝ) w) P :=
    (C.indep_increment_of_adapted hab hZY).comp
      (measurable_id.pow_const 2) measurable_id
  have hΔ : MemLp (fun w ↦ B b w - B a w) 2 P :=
    C.isPreBrownian.isGaussianProcess.hasGaussianLaw_sub.memLp_two
  have hfactor := hindSq.integral_mul_eq_mul_integral
    hΔ.integrable_sq.aestronglyMeasurable
    (AEStronglyMeasurable.mono (𝓕.le a) hZY)
  have hout : inner ℝ (C.elementaryIntegralValue hab Z)
      (C.elementaryIntegralValue hab Y) =
        (∫ w, (B b w - B a w) ^ 2 ∂P) *
          ∫ w, (Z : W → ℝ) w * (Y : W → ℝ) w ∂P := by
    rw [L2.inner_def]
    calc
      ∫ w, ⟪C.elementaryIntegralValue hab Z w,
          C.elementaryIntegralValue hab Y w⟫_ℝ ∂P =
          ∫ w, (B b w - B a w) ^ 2 *
            ((Z : W → ℝ) w * (Y : W → ℝ) w) ∂P := by
        apply integral_congr_ae
        filter_upwards [C.coeFn_elementaryIntegralValue hab Z,
          C.coeFn_elementaryIntegralValue hab Y] with w hfirst hsecond
        rw [hfirst, hsecond]
        simp only [RCLike.inner_apply, conj_trivial]
        ring
      _ = (∫ w, (B b w - B a w) ^ 2 ∂P) *
          ∫ w, (Z : W → ℝ) w * (Y : W → ℝ) w ∂P := by
        simpa only [Pi.mul_apply] using hfactor
  have hinc : inner ℝ
      (brownianLp C.isPreBrownian b - brownianLp C.isPreBrownian a)
      (brownianLp C.isPreBrownian b - brownianLp C.isPreBrownian a) =
        inner ℝ (iocIndicator a b) (iocIndicator a b) := by
    rw [← wienerIntegral_indicatorConstLp_Ioc C.isPreBrownian hab,
      inner_wienerIntegral]
    rfl
  have hΔtime : (∫ w, (B b w - B a w) ^ 2 ∂P) =
      inner ℝ (iocIndicator a b) (iocIndicator a b) := by
    rw [← hinc, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (brownianLp C.isPreBrownian b)
      (brownianLp C.isPreBrownian a), coeFn_brownianLp C.isPreBrownian b,
      coeFn_brownianLp C.isPreBrownian a] with w hsub hb ha
    rw [hsub]
    simp only [Pi.sub_apply, RCLike.inner_apply, conj_trivial]
    rw [hb, ha]
    ring
  have hZYinner : (∫ w, (Z : W → ℝ) w * (Y : W → ℝ) w ∂P) =
      inner ℝ (Z : RandomL2 P) (Y : RandomL2 P) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards with w
    simp only [RCLike.inner_apply, conj_trivial]
    ring
  rw [hout, hΔtime, hZYinner]
  change inner ℝ (iocIndicator a b) (iocIndicator a b) *
      inner ℝ (Z : RandomL2 P) (Y : RandomL2 P) =
    inner ℝ (tensor (iocIndicator a b) (Z : RandomL2 P))
      (tensor (iocIndicator a b) (Y : RandomL2 P))
  rw [inner_tensor]

/-- The predictable process obtained by summing adapted elementary terms over a partition. -/
noncomputable def partitionElementaryPredictable
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›} {n : ℕ} (Q : Partition n)
    (Z : (i : Fin n) → lpMeas ℝ ℝ (𝓕 (Q.t i.castSucc)) 2 P) :
    PredictableProcessL2 𝓕 P :=
  Finset.univ.sum fun i ↦
    elementaryPredictable 𝓕 (Q.t i.castSucc) (Q.t i.succ) (Z i)

/-- The sum of the terminal values of adapted elementary terms over a partition. -/
noncomputable def ClarkOconeFamily.partitionElementaryIntegralValue
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›} (C : ClarkOconeFamily B P 𝓕)
    {n : ℕ} (Q : Partition n)
    (Z : (i : Fin n) → lpMeas ℝ ℝ (𝓕 (Q.t i.castSucc)) 2 P) : RandomL2 P :=
  Finset.univ.sum fun i ↦
    C.elementaryIntegralValue
      (Q.mono.monotone (Fin.castSucc_le_succ i)) (Z i)

/-- The Itô inner-product identity for two adapted elementary step processes on a
common partition. -/
theorem ClarkOconeFamily.inner_partitionElementaryIntegralValue
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›} (C : ClarkOconeFamily B P 𝓕)
    {n : ℕ} (Q : Partition n)
    (Z Y : (i : Fin n) → lpMeas ℝ ℝ (𝓕 (Q.t i.castSucc)) 2 P) :
    inner ℝ (C.partitionElementaryIntegralValue Q Z)
        (C.partitionElementaryIntegralValue Q Y) =
      inner ℝ (partitionElementaryPredictable Q Z)
        (partitionElementaryPredictable Q Y) := by
  simp only [partitionElementaryIntegralValue, partitionElementaryPredictable,
    sum_inner, inner_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have hiord : Q.t i.castSucc ≤ Q.t i.succ :=
    Q.mono.monotone (Fin.castSucc_le_succ i)
  have hjord : Q.t j.castSucc ≤ Q.t j.succ :=
    Q.mono.monotone (Fin.castSucc_le_succ j)
  by_cases hij : i = j
  · subst j
    exact C.inner_elementaryIntegralValue_eq_inner_elementaryPredictable_same
      hiord (Z i) (Y i)
  · rcases Fin.lt_or_lt_of_ne hij with hij | hji
    · calc
        inner ℝ (C.elementaryIntegralValue hjord (Z j))
            (C.elementaryIntegralValue hiord (Y i)) =
            inner ℝ (C.elementaryIntegralValue hiord (Y i))
              (C.elementaryIntegralValue hjord (Z j)) := real_inner_comm _ _
        _ = inner ℝ
              (elementaryPredictable 𝓕 (Q.t i.castSucc) (Q.t i.succ) (Y i))
              (elementaryPredictable 𝓕 (Q.t j.castSucc) (Q.t j.succ) (Z j)) :=
          C.inner_elementaryIntegralValue_eq_inner_elementaryPredictable_of_le
            hiord (partition_succ_le_castSucc Q hij) hjord (Y i) (Z j)
        _ = inner ℝ
              (elementaryPredictable 𝓕 (Q.t j.castSucc) (Q.t j.succ) (Z j))
              (elementaryPredictable 𝓕 (Q.t i.castSucc) (Q.t i.succ) (Y i)) :=
          real_inner_comm _ _
    · exact C.inner_elementaryIntegralValue_eq_inner_elementaryPredictable_of_le
        hjord (partition_succ_le_castSucc Q hji) hiord (Z j) (Y i)

/-- The finite adapted-step Brownian integral preserves squared norms. -/
theorem ClarkOconeFamily.norm_sq_partitionElementaryIntegralValue
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›} (C : ClarkOconeFamily B P 𝓕)
    {n : ℕ} (Q : Partition n)
    (Z : (i : Fin n) → lpMeas ℝ ℝ (𝓕 (Q.t i.castSucc)) 2 P) :
    ‖C.partitionElementaryIntegralValue Q Z‖ ^ 2 =
      ‖partitionElementaryPredictable Q Z‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
  exact C.inner_partitionElementaryIntegralValue Q Z Z

/-- The finite adapted-step Brownian integral is an isometry. -/
theorem ClarkOconeFamily.norm_partitionElementaryIntegralValue
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›} (C : ClarkOconeFamily B P 𝓕)
    {n : ℕ} (Q : Partition n)
    (Z : (i : Fin n) → lpMeas ℝ ℝ (𝓕 (Q.t i.castSucc)) 2 P) :
    ‖C.partitionElementaryIntegralValue Q Z‖ =
      ‖partitionElementaryPredictable Q Z‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  exact C.norm_sq_partitionElementaryIntegralValue Q Z

/-- Elementary Brownian compatibility evaluates the designated Itô integral on every adapted
step process carried by a partition. -/
theorem ClarkOconeFamily.IsBrownianOnElementary.itoIntegral_partitionElementaryPredictable
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›} {C : ClarkOconeFamily B P 𝓕}
    (hC : C.IsBrownianOnElementary) {n : ℕ} (Q : Partition n)
    (Z : (i : Fin n) → lpMeas ℝ ℝ (𝓕 (Q.t i.castSucc)) 2 P) :
    C.itoIntegral (partitionElementaryPredictable Q Z) =
      C.partitionElementaryIntegralValue Q Z := by
  rw [partitionElementaryPredictable, partitionElementaryIntegralValue, map_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  exact hC (Q.mono.monotone (Fin.castSucc_le_succ i)) (Z i)

/-! ## Construction without a `ClarkOconeFamily` -/

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
/-- Future Brownian increments are independent of every random variable measurable for a
filtration identified with the natural Brownian filtration. -/
theorem indep_increment_of_natural_adapted
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm)
    {a b : ℝ≥0} (hab : a ≤ b) {Z : W → ℝ}
    (hZ : AEStronglyMeasurable[𝓕 a] Z P) :
    IndepFun (fun w ↦ B b w - B a w) Z P := by
  let Zm : W → ℝ := hZ.mk Z
  have hshift := hB.indepFun_shift a
  have heval : Measurable (fun x : ℝ≥0 → ℝ ↦ x (b - a)) := measurable_pi_apply _
  have hfuturePast := hshift.comp heval measurable_id
  have hfuturePast' : IndepFun (fun w ↦ B b w - B a w)
      (fun w (t : Set.Iic a) ↦ B t w) P := by
    convert hfuturePast using 1
    · funext w
      change B b w - B a w = B (a + (b - a)) w - B a w
      rw [add_comm, tsub_add_cancel_of_le hab]
    · rfl
  have hind := (IndepFun_iff_Indep _ _ _).mp hfuturePast'
  have hnat_a : 𝓕 a =
      MeasurableSpace.comap (fun w (t : Set.Iic a) ↦ B t w) inferInstance := by
    rw [hnat, Filtration.natural_eq_comap]
  rw [← hnat_a] at hind
  have hZm : @Measurable W ℝ (𝓕 a) inferInstance Zm :=
    hZ.stronglyMeasurable_mk.measurable
  have hindZm := indep_of_indep_of_le_right hind hZm.comap_le
  have hfunZm : IndepFun (fun w ↦ B b w - B a w) Zm P :=
    (IndepFun_iff_Indep _ _ _).mpr hindZm
  exact hfunZm.congr Filter.EventuallyEq.rfl hZ.ae_eq_mk.symm

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
/-- An adapted `L²` coefficient times a future Brownian increment is again in `L²`. -/
theorem memLp_natural_adapted_mul_increment
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm)
    {a b : ℝ≥0} (hab : a ≤ b) (Z : lpMeas ℝ ℝ (𝓕 a) 2 P) :
    MemLp (fun w ↦ (Z : W → ℝ) w * (B b w - B a w)) 2 P := by
  have hΔ : MemLp (fun w ↦ B b w - B a w) 2 P :=
    hB.isGaussianProcess.hasGaussianLaw_sub.memLp_two
  have hind := indep_increment_of_natural_adapted hB hsm hnat hab
    (lpMeas.aestronglyMeasurable Z)
  have hindSq : IndepFun (fun w ↦ (B b w - B a w) ^ 2)
      (fun w ↦ (Z : W → ℝ) w ^ 2) P :=
    hind.comp (measurable_id.pow_const 2) (measurable_id.pow_const 2)
  have hint : Integrable ((fun w ↦ (B b w - B a w) ^ 2) *
      fun w ↦ (Z : W → ℝ) w ^ 2) P :=
    hindSq.integrable_mul hΔ.integrable_sq
      (Lp.memLp (Z : Lp ℝ 2 P)).integrable_sq
  have hZamb : AEStronglyMeasurable (Z : W → ℝ) P :=
    AEStronglyMeasurable.mono (𝓕.le a) (lpMeas.aestronglyMeasurable Z)
  have hmeas : AEStronglyMeasurable
      (fun w ↦ (Z : W → ℝ) w * (B b w - B a w)) P :=
    hZamb.mul hΔ.aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq hmeas).2
  refine hint.congr (Filter.Eventually.of_forall fun w ↦ ?_)
  simp only [Pi.mul_apply]
  ring

/-- The genuine Brownian terminal value `Z (B_b - B_a)` of an adapted elementary process,
constructed without a `ClarkOconeFamily`. -/
noncomputable def elementaryBrownianValue
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm)
    {a b : ℝ≥0} (hab : a ≤ b) (Z : lpMeas ℝ ℝ (𝓕 a) 2 P) : RandomL2 P :=
  (memLp_natural_adapted_mul_increment hB hsm hnat hab Z).toLp
    (fun w ↦ (Z : W → ℝ) w * (B b w - B a w))

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
/-- A representative of the constructed elementary Brownian terminal value. -/
theorem coeFn_elementaryBrownianValue
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm)
    {a b : ℝ≥0} (hab : a ≤ b) (Z : lpMeas ℝ ℝ (𝓕 a) 2 P) :
    (elementaryBrownianValue hB hsm hnat hab Z : W → ℝ) =ᵐ[P]
      fun w ↦ (Z : W → ℝ) w * (B b w - B a w) :=
  MemLp.coeFn_toLp _

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
/-- The elementary Brownian terminal value is additive in its adapted coefficient. -/
theorem elementaryBrownianValue_add
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm)
    {a b : ℝ≥0} (hab : a ≤ b) (Z Y : lpMeas ℝ ℝ (𝓕 a) 2 P) :
    elementaryBrownianValue hB hsm hnat hab (Z + Y) =
      elementaryBrownianValue hB hsm hnat hab Z +
        elementaryBrownianValue hB hsm hnat hab Y := by
  apply Lp.ext
  filter_upwards [coeFn_elementaryBrownianValue hB hsm hnat hab (Z + Y),
    coeFn_elementaryBrownianValue hB hsm hnat hab Z,
    coeFn_elementaryBrownianValue hB hsm hnat hab Y,
    Lp.coeFn_add (Z : RandomL2 P) (Y : RandomL2 P),
    Lp.coeFn_add (elementaryBrownianValue hB hsm hnat hab Z)
      (elementaryBrownianValue hB hsm hnat hab Y)]
    with w hsum hZ hY hZY hvalue
  rw [hsum, hvalue, Pi.add_apply, hZ, hY]
  change (Z.1 + Y.1 : RandomL2 P) w * (B b w - B a w) =
    (Z : W → ℝ) w * (B b w - B a w) +
      (Y : W → ℝ) w * (B b w - B a w)
  rw [hZY, Pi.add_apply]
  ring

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
/-- The elementary Brownian terminal value commutes with real scalar multiplication. -/
theorem elementaryBrownianValue_smul
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm)
    {a b : ℝ≥0} (hab : a ≤ b) (c : ℝ) (Z : lpMeas ℝ ℝ (𝓕 a) 2 P) :
    elementaryBrownianValue hB hsm hnat hab (c • Z) =
      c • elementaryBrownianValue hB hsm hnat hab Z := by
  apply Lp.ext
  filter_upwards [coeFn_elementaryBrownianValue hB hsm hnat hab (c • Z),
    coeFn_elementaryBrownianValue hB hsm hnat hab Z,
    Lp.coeFn_smul c (Z : RandomL2 P),
    Lp.coeFn_smul c (elementaryBrownianValue hB hsm hnat hab Z)]
    with w hsmul hZ hcZ hvalue
  rw [hsmul, hvalue, Pi.smul_apply, hZ]
  change (c • Z.1 : RandomL2 P) w * (B b w - B a w) =
    c • ((Z : W → ℝ) w * (B b w - B a w))
  rw [hcZ, Pi.smul_apply]
  simp only [smul_eq_mul]
  ring

/-- For a fixed interval, the genuine Brownian terminal value is a linear function of the
adapted coefficient. -/
noncomputable def elementaryBrownianValueLinear
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm)
    {a b : ℝ≥0} (hab : a ≤ b) : lpMeas ℝ ℝ (𝓕 a) 2 P →ₗ[ℝ] RandomL2 P where
  toFun := elementaryBrownianValue hB hsm hnat hab
  map_add' := elementaryBrownianValue_add hB hsm hnat hab
  map_smul' := elementaryBrownianValue_smul hB hsm hnat hab

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
/-- The fixed-interval linear map evaluates to the elementary Brownian value. -/
@[simp]
theorem elementaryBrownianValueLinear_apply
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm)
    {a b : ℝ≥0} (hab : a ≤ b) (Z : lpMeas ℝ ℝ (𝓕 a) 2 P) :
    elementaryBrownianValueLinear hB hsm hnat hab Z =
      elementaryBrownianValue hB hsm hnat hab Z :=
  rfl

/-- A family's elementary terminal value is exactly the construction-level Brownian value. -/
theorem ClarkOconeFamily.elementaryIntegralValue_eq_elementaryBrownianValue
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›} (C : ClarkOconeFamily B P 𝓕)
    {a b : ℝ≥0} (hab : a ≤ b) (Z : lpMeas ℝ ℝ (𝓕 a) 2 P) :
    C.elementaryIntegralValue hab Z =
      elementaryBrownianValue C.isPreBrownian C.stronglyMeasurable
        C.naturalFiltration hab Z := by
  apply Lp.ext
  exact (C.coeFn_elementaryIntegralValue hab Z).trans
    (coeFn_elementaryBrownianValue C.isPreBrownian C.stronglyMeasurable
      C.naturalFiltration hab Z).symm

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
/-- Constructed elementary Brownian values on chronologically disjoint intervals are
orthogonal. -/
theorem inner_elementaryBrownianValue_eq_zero_of_le
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm)
    {a b c d : ℝ≥0} (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (Z : lpMeas ℝ ℝ (𝓕 a) 2 P) (Y : lpMeas ℝ ℝ (𝓕 c) 2 P) :
    inner ℝ (elementaryBrownianValue hB hsm hnat hab Z)
      (elementaryBrownianValue hB hsm hnat hcd Y) = 0 := by
  have hac : a ≤ c := hab.trans hbc
  have hBadapted : StronglyAdapted 𝓕 B := by
    rw [hnat]
    exact Filtration.stronglyAdapted_natural hsm
  have hZc : AEStronglyMeasurable[𝓕 c] (Z : W → ℝ) P :=
    AEStronglyMeasurable.mono (𝓕.mono hac) (lpMeas.aestronglyMeasurable Z)
  have hYc : AEStronglyMeasurable[𝓕 c] (Y : W → ℝ) P :=
    lpMeas.aestronglyMeasurable Y
  have hΔabc : AEStronglyMeasurable[𝓕 c] (fun w ↦ B b w - B a w) P :=
    ((hBadapted.stronglyMeasurable_le hbc).sub
      (hBadapted.stronglyMeasurable_le hac)).aestronglyMeasurable
  have hG : AEStronglyMeasurable[𝓕 c]
      (fun w ↦ ((Z : W → ℝ) w * (B b w - B a w)) * (Y : W → ℝ) w) P :=
    (hZc.mul hΔabc).mul hYc
  have hind := indep_increment_of_natural_adapted hB hsm hnat hcd hG
  have hΔcd : AEStronglyMeasurable (fun w ↦ B d w - B c w) P :=
    hB.isGaussianProcess.hasGaussianLaw_sub.memLp_two.aestronglyMeasurable
  have hGamb : AEStronglyMeasurable
      (fun w ↦ ((Z : W → ℝ) w * (B b w - B a w)) * (Y : W → ℝ) w) P :=
    AEStronglyMeasurable.mono (𝓕.le c) hG
  have hfactor := hind.integral_mul_eq_mul_integral hΔcd hGamb
  rw [L2.inner_def]
  calc
    ∫ w, ⟪elementaryBrownianValue hB hsm hnat hab Z w,
        elementaryBrownianValue hB hsm hnat hcd Y w⟫_ℝ ∂P =
        ∫ w, (B d w - B c w) *
          (((Z : W → ℝ) w * (B b w - B a w)) * (Y : W → ℝ) w) ∂P := by
      apply integral_congr_ae
      filter_upwards [coeFn_elementaryBrownianValue hB hsm hnat hab Z,
        coeFn_elementaryBrownianValue hB hsm hnat hcd Y] with w hfirst hsecond
      rw [hfirst, hsecond]
      simp only [RCLike.inner_apply, conj_trivial]
      ring
    _ = (∫ w, B d w - B c w ∂P) *
        ∫ w, ((Z : W → ℝ) w * (B b w - B a w)) * (Y : W → ℝ) w ∂P := by
      simpa only [Pi.mul_apply] using hfactor
    _ = 0 := by
      rw [integral_sub (hB.integrable_eval d) (hB.integrable_eval c),
        hB.integral_eval, hB.integral_eval, sub_zero, zero_mul]

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
/-- The cross-inner-product identity for chronologically disjoint constructed elementary
Brownian values. -/
theorem inner_elementaryBrownianValue_eq_inner_elementaryPredictable_of_le
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm)
    {a b c d : ℝ≥0} (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (Z : lpMeas ℝ ℝ (𝓕 a) 2 P) (Y : lpMeas ℝ ℝ (𝓕 c) 2 P) :
    let : SFinite P :=
      @probability_sFinite W _ P hB.isGaussianProcess.isProbabilityMeasure
    inner ℝ (elementaryBrownianValue hB hsm hnat hab Z)
      (elementaryBrownianValue hB hsm hnat hcd Y) =
    inner ℝ (elementaryPredictable 𝓕 a b Z)
      (elementaryPredictable 𝓕 c d Y) := by
  let : SFinite P :=
      @probability_sFinite W _ P hB.isGaussianProcess.isProbabilityMeasure
  rw [inner_elementaryBrownianValue_eq_zero_of_le hB hsm hnat hab hbc hcd Z Y,
    inner_elementaryPredictable_eq_zero_of_le 𝓕 hbc Z Y]

omit [CompleteSpace W] [BorelSpace W] in
/-- The cross-inner-product identity for two constructed elementary Brownian values on the same
interval. -/
theorem inner_elementaryBrownianValue_eq_inner_elementaryPredictable_same
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm)
    {a b : ℝ≥0} (hab : a ≤ b) (Z Y : lpMeas ℝ ℝ (𝓕 a) 2 P) :
    inner ℝ (elementaryBrownianValue hB hsm hnat hab Z)
      (elementaryBrownianValue hB hsm hnat hab Y) =
    inner ℝ (elementaryPredictable 𝓕 a b Z)
      (elementaryPredictable 𝓕 a b Y) := by
  have hZY : AEStronglyMeasurable[𝓕 a]
      (fun w ↦ (Z : W → ℝ) w * (Y : W → ℝ) w) P :=
    (lpMeas.aestronglyMeasurable Z).mul (lpMeas.aestronglyMeasurable Y)
  have hindSq : IndepFun (fun w ↦ (B b w - B a w) ^ 2)
      (fun w ↦ (Z : W → ℝ) w * (Y : W → ℝ) w) P :=
    (indep_increment_of_natural_adapted hB hsm hnat hab hZY).comp
      (measurable_id.pow_const 2) measurable_id
  have hΔ : MemLp (fun w ↦ B b w - B a w) 2 P :=
    hB.isGaussianProcess.hasGaussianLaw_sub.memLp_two
  have hfactor := hindSq.integral_mul_eq_mul_integral
    hΔ.integrable_sq.aestronglyMeasurable
    (AEStronglyMeasurable.mono (𝓕.le a) hZY)
  have hout : inner ℝ (elementaryBrownianValue hB hsm hnat hab Z)
      (elementaryBrownianValue hB hsm hnat hab Y) =
        (∫ w, (B b w - B a w) ^ 2 ∂P) *
          ∫ w, (Z : W → ℝ) w * (Y : W → ℝ) w ∂P := by
    rw [L2.inner_def]
    calc
      ∫ w, ⟪elementaryBrownianValue hB hsm hnat hab Z w,
          elementaryBrownianValue hB hsm hnat hab Y w⟫_ℝ ∂P =
          ∫ w, (B b w - B a w) ^ 2 *
            ((Z : W → ℝ) w * (Y : W → ℝ) w) ∂P := by
        apply integral_congr_ae
        filter_upwards [coeFn_elementaryBrownianValue hB hsm hnat hab Z,
          coeFn_elementaryBrownianValue hB hsm hnat hab Y] with w hfirst hsecond
        rw [hfirst, hsecond]
        simp only [RCLike.inner_apply, conj_trivial]
        ring
      _ = (∫ w, (B b w - B a w) ^ 2 ∂P) *
          ∫ w, (Z : W → ℝ) w * (Y : W → ℝ) w ∂P := by
        simpa only [Pi.mul_apply] using hfactor
  have hinc : inner ℝ (brownianLp hB b - brownianLp hB a)
      (brownianLp hB b - brownianLp hB a) =
        inner ℝ (iocIndicator a b) (iocIndicator a b) := by
    rw [← wienerIntegral_indicatorConstLp_Ioc hB hab, inner_wienerIntegral]
    rfl
  have hΔtime : (∫ w, (B b w - B a w) ^ 2 ∂P) =
      inner ℝ (iocIndicator a b) (iocIndicator a b) := by
    rw [← hinc, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (brownianLp hB b) (brownianLp hB a),
      coeFn_brownianLp hB b, coeFn_brownianLp hB a] with w hsub hb ha
    rw [hsub]
    simp only [Pi.sub_apply, RCLike.inner_apply, conj_trivial]
    rw [hb, ha]
    ring
  have hZYinner : (∫ w, (Z : W → ℝ) w * (Y : W → ℝ) w ∂P) =
      inner ℝ (Z : RandomL2 P) (Y : RandomL2 P) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards with w
    simp only [RCLike.inner_apply, conj_trivial]
    ring
  rw [hout, hΔtime, hZYinner]
  change inner ℝ (iocIndicator a b) (iocIndicator a b) *
      inner ℝ (Z : RandomL2 P) (Y : RandomL2 P) =
    inner ℝ (tensor (iocIndicator a b) (Z : RandomL2 P))
      (tensor (iocIndicator a b) (Y : RandomL2 P))
  rw [inner_tensor]

/-- The sum of genuine Brownian terminal values of an adapted step process over a partition. -/
noncomputable def partitionElementaryBrownianValue
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm) {n : ℕ} (Q : Partition n)
    (Z : (i : Fin n) → lpMeas ℝ ℝ (𝓕 (Q.t i.castSucc)) 2 P) : RandomL2 P :=
  Finset.univ.sum fun i ↦ elementaryBrownianValue hB hsm hnat
    (Q.mono.monotone (Fin.castSucc_le_succ i)) (Z i)

omit [CompleteSpace W] [BorelSpace W] in
/-- The construction-level Itô inner-product identity for adapted step processes on a common
partition. -/
theorem inner_partitionElementaryBrownianValue
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm) {n : ℕ} (Q : Partition n)
    (Z Y : (i : Fin n) → lpMeas ℝ ℝ (𝓕 (Q.t i.castSucc)) 2 P) :
    inner ℝ (partitionElementaryBrownianValue hB hsm hnat Q Z)
        (partitionElementaryBrownianValue hB hsm hnat Q Y) =
      inner ℝ (partitionElementaryPredictable Q Z)
        (partitionElementaryPredictable Q Y) := by
  simp only [partitionElementaryBrownianValue, partitionElementaryPredictable,
    sum_inner, inner_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have hiord : Q.t i.castSucc ≤ Q.t i.succ :=
    Q.mono.monotone (Fin.castSucc_le_succ i)
  have hjord : Q.t j.castSucc ≤ Q.t j.succ :=
    Q.mono.monotone (Fin.castSucc_le_succ j)
  by_cases hij : i = j
  · subst j
    exact inner_elementaryBrownianValue_eq_inner_elementaryPredictable_same
      hB hsm hnat hiord (Z i) (Y i)
  · rcases Fin.lt_or_lt_of_ne hij with hij | hji
    · calc
        inner ℝ (elementaryBrownianValue hB hsm hnat hjord (Z j))
            (elementaryBrownianValue hB hsm hnat hiord (Y i)) =
            inner ℝ (elementaryBrownianValue hB hsm hnat hiord (Y i))
              (elementaryBrownianValue hB hsm hnat hjord (Z j)) := real_inner_comm _ _
        _ = inner ℝ
              (elementaryPredictable 𝓕 (Q.t i.castSucc) (Q.t i.succ) (Y i))
              (elementaryPredictable 𝓕 (Q.t j.castSucc) (Q.t j.succ) (Z j)) :=
          inner_elementaryBrownianValue_eq_inner_elementaryPredictable_of_le
            hB hsm hnat hiord (partition_succ_le_castSucc Q hij) hjord (Y i) (Z j)
        _ = inner ℝ
              (elementaryPredictable 𝓕 (Q.t j.castSucc) (Q.t j.succ) (Z j))
              (elementaryPredictable 𝓕 (Q.t i.castSucc) (Q.t i.succ) (Y i)) :=
          real_inner_comm _ _
    · exact inner_elementaryBrownianValue_eq_inner_elementaryPredictable_of_le
        hB hsm hnat hjord (partition_succ_le_castSucc Q hji) hiord (Z j) (Y i)

omit [CompleteSpace W] [BorelSpace W] in
/-- Construction-level Itô isometry for common-partition adapted `L²` step processes. -/
theorem norm_partitionElementaryBrownianValue
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm) {n : ℕ} (Q : Partition n)
    (Z : (i : Fin n) → lpMeas ℝ ℝ (𝓕 (Q.t i.castSucc)) 2 P) :
    ‖partitionElementaryBrownianValue hB hsm hnat Q Z‖ =
      ‖partitionElementaryPredictable Q Z‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
  exact inner_partitionElementaryBrownianValue hB hsm hnat Q Z Z

/-- The family-dependent partition value agrees with the construction-level Brownian value. -/
theorem ClarkOconeFamily.partitionElementaryIntegralValue_eq_partitionElementaryBrownianValue
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›} (C : ClarkOconeFamily B P 𝓕)
    {n : ℕ} (Q : Partition n)
    (Z : (i : Fin n) → lpMeas ℝ ℝ (𝓕 (Q.t i.castSucc)) 2 P) :
    C.partitionElementaryIntegralValue Q Z =
      partitionElementaryBrownianValue C.isPreBrownian C.stronglyMeasurable
        C.naturalFiltration Q Z := by
  simp only [partitionElementaryIntegralValue, partitionElementaryBrownianValue]
  apply Finset.sum_congr rfl
  intro i _hi
  exact C.elementaryIntegralValue_eq_elementaryBrownianValue
    (Q.mono.monotone (Fin.castSucc_le_succ i)) (Z i)

end Malliavin

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
