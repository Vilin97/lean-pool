/-
Copyright (c) 2026 The lean-malliavin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-malliavin contributors
-/
import LeanPool.Malliavin.Malliavin.BrownianWickPurePowerComparison
import LeanPool.Malliavin.Malliavin.BrownianMultipleIntegralBoxSpan
import LeanPool.Malliavin.Malliavin.PastCylinderDensity

/-!
# Brownian pure powers from Malliavin--Itô duality

On a generated linear Wiener space, the unconditional Malliavin--Itô duality recursively
computes the pairing of a Wick power with every ordered Brownian increment chain.  Ordered-box
density then identifies the Wick power with the canonical pure-power multiple integral.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace

noncomputable
section

namespace Malliavin.BrownianIteratedConstruction

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}

/-- The continuous linear functional represented by a formal Brownian step sum. -/
noncomputable def brownianStepDual (coordinate : ℝ≥0 → StrongDual ℝ W)
    (v : ℝ≥0 →₀ ℝ) : StrongDual ℝ W :=
  v.sum fun t c ↦ c • coordinate t

omit [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
theorem brownianStepDual_apply (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (v : ℝ≥0 →₀ ℝ) (w : W) :
    brownianStepDual coordinate v w = stepSum B v w := by
  unfold brownianStepDual stepSum
  simp only [Finsupp.sum]
  change (ContinuousLinearMap.apply ℝ ℝ w)
    (∑ t ∈ v.support, v t • coordinate t) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro t ht
  rw [map_smul, coordinate_apply]
  rfl

/-- Under the first-chaos equivalence, the Cameron--Martin generator of a formal step sum is
sent back to its deterministic step kernel. -/
theorem wienerIntegralEquiv_symm_ofDual_brownianStepDual
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B) (v : ℝ≥0 →₀ ℝ) :
    (wienerIntegralEquiv hB).symm
        (LinearIsometryEquiv.ofEq _ _
          (space_eq_firstChaos hB coordinate coordinate_apply generated)
          (CameronMartin.ofDual P (brownianStepDual coordinate v))) =
      stepToLp v := by
  apply (wienerIntegralEquiv hB).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  apply Subtype.ext
  rw [LinearIsometryEquiv.coe_ofEq_apply, coe_wienerIntegralEquiv_apply,
    wienerIntegral_stepToLp]
  unfold stepToRandom brownianStepDual
  simp only [Finsupp.linearCombination_apply, Finsupp.sum]
  change (((CameronMartin.ofDual P)
      (∑ t ∈ v.support, v t • coordinate t) : CameronMartin.Space P) : Lp ℝ 2 P) = _
  rw [map_sum]
  simp only [map_smul, Submodule.coe_sum, Submodule.coe_smul]
  apply Finset.sum_congr rfl
  intro t ht
  rw [brownianLp_eq_ofDual hB coordinate coordinate_apply]

/-- A Wick power of a formal Brownian step sum belongs to the first Malliavin Sobolev space
when the Brownian coordinates are continuous linear functionals. -/
theorem brownianWickPowerLp_mem_domD12
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (v : ℝ≥0 →₀ ℝ) (n : ℕ) :
    brownianWickPowerLp hB v n ∈ domD12 P := by
  let p := varianceHermite (‖stepToLp v‖ ^ 2) n
  let F : (Fin 1 → ℝ) → ℝ := fun y ↦ p.eval (y 0)
  let L : Fin 1 → StrongDual ℝ W := fun _ ↦ brownianStepDual coordinate v
  let C := coeffMass p + coeffMass p.derivative
  let c : ℝ := p.natDegree
  have hC : 0 ≤ C := add_nonneg (coeffMass_nonneg _) (coeffMass_nonneg _)
  have hc : 0 ≤ c := Nat.cast_nonneg _
  have hF : ContDiff ℝ 1 F := contDiff_oneCoord (contDiff_polynomial_eval p)
  have hbound : ∀ y, |F y| ≤ C * Real.exp (c * ‖y‖) := by
    intro y
    exact abs_oneCoord_le hC hc (abs_polynomial_eval_le' p) y
  have hbound' : ∀ y, ‖fderiv ℝ F y‖ ≤ C * Real.exp (c * ‖y‖) := by
    intro y
    exact norm_fderiv_oneCoord_le (contDiff_polynomial_eval p) hC hc
      (abs_polynomial_deriv_le' p) y
  have hmem := (cylinder_expGrowth_mem_domD12 P hF hC hc hbound hbound' L).1
  have heq :
      (memLp_cylinder_expGrowth P hF hC hc hbound L).toLp _ =
        brownianWickPowerLp hB v n := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp
        (memLp_cylinder_expGrowth P hF hC hc hbound L),
      coeFn_brownianWickPowerLp hB v n] with w hleft hright
    rw [hleft, hright]
    exact congrArg p.eval (brownianStepDual_apply coordinate coordinate_apply v w)
  rwa [heq] at hmem

/-- The time-realized Malliavin derivative of a Wick power is its predecessor tensored with the
deterministic step kernel. -/
theorem timeDerivative_mderivClosure_brownianWickPowerLp
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B) (v : ℝ≥0 →₀ ℝ) (n : ℕ) :
    timeDerivative hB coordinate coordinate_apply generated
        (mderivClosure P (brownianWickPowerLp hB v n)) =
      tensor (stepToLp v) ((n : ℝ) • brownianWickPowerLp hB v (n - 1)) := by
  let p := varianceHermite (‖stepToLp v‖ ^ 2) n
  let F : (Fin 1 → ℝ) → ℝ := fun y ↦ p.eval (y 0)
  let L : Fin 1 → StrongDual ℝ W := fun _ ↦ brownianStepDual coordinate v
  let C := coeffMass p + coeffMass p.derivative
  let c : ℝ := p.natDegree
  have hC : 0 ≤ C := add_nonneg (coeffMass_nonneg _) (coeffMass_nonneg _)
  have hc : 0 ≤ c := Nat.cast_nonneg _
  have hF : ContDiff ℝ 1 F := contDiff_oneCoord (contDiff_polynomial_eval p)
  have hbound : ∀ y, |F y| ≤ C * Real.exp (c * ‖y‖) := by
    intro y
    exact abs_oneCoord_le hC hc (abs_polynomial_eval_le' p) y
  have hbound' : ∀ y, ‖fderiv ℝ F y‖ ≤ C * Real.exp (c * ‖y‖) := by
    intro y
    exact norm_fderiv_oneCoord_le (contDiff_polynomial_eval p) hC hc
      (abs_polynomial_deriv_le' p) y
  have heq :
      (memLp_cylinder_expGrowth P hF hC hc hbound L).toLp _ =
        brownianWickPowerLp hB v n := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp
        (memLp_cylinder_expGrowth P hF hC hc hbound L),
      coeFn_brownianWickPowerLp hB v n] with w hleft hright
    rw [hleft, hright]
    exact congrArg p.eval (brownianStepDual_apply coordinate coordinate_apply v w)
  have hderiv :
      (memLp_mderiv_cylinder_expGrowth P hF hC hc hbound' L).toLp _ =
        smulLp (CameronMartin.ofDual P (brownianStepDual coordinate v))
          ((n : ℝ) • brownianWickPowerLp hB v (n - 1)) := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp
        (memLp_mderiv_cylinder_expGrowth P hF hC hc hbound' L),
      coeFn_smulLp (CameronMartin.ofDual P (brownianStepDual coordinate v))
        ((n : ℝ) • brownianWickPowerLp hB v (n - 1)),
      Lp.coeFn_smul (n : ℝ) (brownianWickPowerLp hB v (n - 1)),
      coeFn_brownianWickPowerLp hB v (n - 1)] with w hleft hsmul hnsmul hwick
    rw [hleft, hsmul, hnsmul, Pi.smul_apply, hwick]
    change mderiv P (fun y ↦ p.eval (brownianStepDual coordinate v y)) w = _
    rw [mderiv_comp P ((contDiff_polynomial_eval p).differentiable one_ne_zero _)
      (brownianStepDual coordinate v).differentiableAt,
      mderiv_dual, Polynomial.deriv]
    change p.derivative.eval (brownianStepDual coordinate v w) • _ = _
    rw [show p.derivative = Polynomial.C (n : ℝ) *
        varianceHermite (‖stepToLp v‖ ^ 2) (n - 1) by
      exact derivative_varianceHermite (‖stepToLp v‖ ^ 2) n]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, smul_eq_mul]
    rw [brownianStepDual_apply coordinate coordinate_apply]
  rw [← heq,
    (cylinder_expGrowth_mem_domD12 P hF hC hc hbound hbound' L).2,
    hderiv, timeDerivative_smulLp,
    wienerIntegralEquiv_symm_ofDual_brownianStepDual hB coordinate coordinate_apply generated]

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W] [IsGaussian P] in
/-- Pairing a deterministic pure-power kernel with a box factors into its one-dimensional
pairings. -/
theorem inner_iteratedKernelPurePower_boxKernel (n : ℕ)
    (f : Lp ℝ 2 nonnegativeLebesgueMeasure) (u v : Fin n → ℝ≥0) :
    inner ℝ (iteratedKernelPurePower n f) (boxKernel u v) =
      ∏ i, inner ℝ f (iocIndicator (u i) (v i)) := by
  rw [MeasureTheory.L2.inner_def]
  have hpure := coeFn_iteratedKernelPurePower n f
  have hbox : (boxKernel u v : (Fin n → ℝ≥0) → ℝ) =ᵐ[iteratedKernelMeasure n]
      (orderedBox u v).indicator fun _ ↦ (1 : ℝ) :=
    indicatorConstLp_coeFn
  calc
    (∫ t, inner ℝ (iteratedKernelPurePower n f t) (boxKernel u v t)
        ∂iteratedKernelMeasure n) =
        ∫ t, ∏ i, f (t i) *
          (Set.Ioc (u i) (v i)).indicator (fun _ ↦ (1 : ℝ)) (t i)
          ∂iteratedKernelMeasure n := by
      apply integral_congr_ae
      filter_upwards [hpure, hbox] with t hpure_t hbox_t
      rw [hpure_t, hbox_t]
      simp only [RCLike.inner_apply, conj_trivial, iteratedKernelPurePowerFun]
      by_cases ht : t ∈ orderedBox u v
      · rw [Set.indicator_of_mem ht]
        have hti : ∀ i, t i ∈ Set.Ioc (u i) (v i) := by
          intro i
          exact ht i (Set.mem_univ i)
        simp only [hti, Set.indicator_of_mem, mul_one, one_mul]
      · rw [Set.indicator_of_notMem ht, zero_mul]
        have hnot : ¬ ∀ i, t i ∈ Set.Ioc (u i) (v i) := by
          intro hall
          exact ht fun i _ ↦ hall i
        push Not at hnot
        obtain ⟨i, hi⟩ := hnot
        symm
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        rw [Set.indicator_of_notMem hi, mul_zero]
    _ = ∏ i, ∫ x, f x *
          (Set.Ioc (u i) (v i)).indicator (fun _ ↦ (1 : ℝ)) x
          ∂nonnegativeLebesgueMeasure := by
      change (∫ t, ∏ i, f (t i) *
          (Set.Ioc (u i) (v i)).indicator (fun _ ↦ (1 : ℝ)) (t i)
          ∂(Measure.pi fun _ : Fin n ↦ nonnegativeLebesgueMeasure)) = _
      exact integral_fintype_prod_eq_prod
        (E := fun _ : Fin n ↦ ℝ≥0)
        (f := fun i x ↦ f x *
          (Set.Ioc (u i) (v i)).indicator (fun _ ↦ (1 : ℝ)) x)
        (μ := fun _ : Fin n ↦ nonnegativeLebesgueMeasure)
    _ = ∏ i, inner ℝ f (iocIndicator (u i) (v i)) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [MeasureTheory.L2.inner_def]
      apply integral_congr_ae
      filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := measurableSet_Ioc)
        (hμs := nonnegativeLebesgueMeasure_Ioc_ne_top (u i) (v i))
        (c := (1 : ℝ))] with x hx
      unfold iocIndicator
      rw [hx]
      simp only [RCLike.inner_apply, conj_trivial]
      ring

/-- Recursive Malliavin--Itô duality computes the pairing of an order-`n` Wick power with an
ordered Brownian increment chain. -/
theorem inner_brownianWickPowerLp_chainIntegralLp
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B) (hsm : ∀ t, StronglyMeasurable (B t))
    (v : ℝ≥0 →₀ ℝ) {n : ℕ} (a : OrderedBoxIndex n) :
    inner ℝ (brownianWickPowerLp hB v n) (chainIntegralLp hB a.u a.v) =
      (n.factorial : ℝ) *
        ∏ i, inner ℝ (stepToLp v) (iocIndicator (a.u i) (a.v i)) := by
  induction n with
  | zero =>
      rw [chainIntegralLp_zero hB, ← brownianWickPowerLp_zero hB v,
        inner_brownianWickPowerLp]
      simp
  | succ n ih =>
      let headBox : OrderedBoxIndex n :=
        { u := fun i ↦ a.u i.castSucc
          v := fun i ↦ a.v i.castSucc
          valid := fun i ↦ a.valid i.castSucc
          ordered := fun i j hij ↦ a.ordered i.castSucc j.castSucc
            (Fin.castSucc_lt_castSucc_iff.mpr hij) }
      let Z := orderedChainPrefixAdapted hB hsm a.u a.v a.valid a.ordered
      let U := elementaryPredictable (Filtration.natural B hsm)
        (a.u (Fin.last n)) (a.v (Fin.last n)) Z
      let F : Malliavin.D12 P :=
        ⟨brownianWickPowerLp hB v (n + 1),
          brownianWickPowerLp_mem_domD12 hB coordinate coordinate_apply v (n + 1)⟩
      have hexpect : expectationL2 (brownianWickPowerLp hB v (n + 1)) = 0 := by
        rw [expectationL2, integral_brownianWickPowerLp hB v (Nat.succ_pos n)]
        simp
      have hdual := Malliavin.naturalItoDuality_natural hB coordinate coordinate_apply
        generated hsm rfl F U
      have hchain : chainIntegralLp hB a.u a.v = naturalItoIntegral hB hsm rfl U := by
        exact chainIntegralLp_succ_eq_naturalItoIntegral
          hB hsm a.u a.v a.valid a.ordered
      have hleft :
          inner ℝ (brownianWickPowerLp hB v (n + 1))
              (chainIntegralLp hB a.u a.v) =
            inner ℝ (predictableProjection (Filtration.natural B hsm)
              (timeDerivative hB coordinate coordinate_apply generated
                (mderivD12 P F))) U := by
        rw [hchain]
        simpa only [F, hexpect, sub_zero] using hdual
      let D := timeDerivative hB coordinate coordinate_apply generated (mderivD12 P F)
      have horth := Malliavin.inner_predictableProjection_sub
        (Filtration.natural B hsm) D U
      have hproj :
          inner ℝ (predictableProjection (Filtration.natural B hsm) D) U =
            inner ℝ D (U : TimeProcessL2 P) := by
        rw [inner_sub_left] at horth
        exact sub_eq_zero.mp horth
      rw [hleft, hproj]
      change inner ℝ
        (timeDerivative hB coordinate coordinate_apply generated
          (mderivClosure P (brownianWickPowerLp hB v (n + 1))))
        (U : TimeProcessL2 P) = _
      rw [timeDerivative_mderivClosure_brownianWickPowerLp,
        show n + 1 - 1 = n by omega, elementaryPredictable_coeLp, inner_tensor,
        real_inner_smul_left,
        show (Z : RandomL2 P) = chainIntegralLp hB headBox.u headBox.v by rfl,
        ih headBox]
      simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
        Fin.prod_univ_castSucc]
      ring

omit [CompleteSpace W] [BorelSpace W] in
/-- The canonical pure-power multiple integral has the same pairing with every ordered Brownian
increment chain. -/
theorem inner_brownianPurePowerIntegral_chainIntegralLp
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (f : Lp ℝ 2 nonnegativeLebesgueMeasure) {n : ℕ} (a : OrderedBoxIndex n) :
    inner ℝ (brownianPurePowerIntegral hB n f) (chainIntegralLp hB a.u a.v) =
      (n.factorial : ℝ) *
        ∏ i, inner ℝ f (iocIndicator (a.u i) (a.v i)) := by
  rw [← brownianMultipleIntegralCLM_orderedBox hB hsm a,
    brownianPurePowerIntegral, inner_brownianMultipleIntegralCLM hB hsm,
    symmetrizeL_iteratedKernelPurePower,
    ← inner_symmetrizeL_left n (iteratedKernelPurePower n f) (boxKernel a.u a.v),
    symmetrizeL_iteratedKernelPurePower,
    inner_iteratedKernelPurePower_boxKernel]

/-- Wick and canonical pure-power values induce the same linear functional on every ordered
chain of the matching order. -/
theorem inner_brownianWickPowerLp_chainIntegralLp_eq_purePower
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B) (hsm : ∀ t, StronglyMeasurable (B t))
    (v : ℝ≥0 →₀ ℝ) {n : ℕ} (a : OrderedBoxIndex n) :
    inner ℝ (brownianWickPowerLp hB v n) (chainIntegralLp hB a.u a.v) =
      inner ℝ (brownianPurePowerIntegral hB n (stepToLp v))
        (chainIntegralLp hB a.u a.v) := by
  rw [inner_brownianWickPowerLp_chainIntegralLp
      hB coordinate coordinate_apply generated hsm,
    inner_brownianPurePowerIntegral_chainIntegralLp hB hsm]

/-- On a generated linear Wiener space, every Wick power of a formal step sum is its canonical
pure-power multiple integral. -/
theorem brownianWickPowerLp_eq_purePowerIntegral_of_generated
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B) (hsm : ∀ t, StronglyMeasurable (B t))
    (v : ℝ≥0 →₀ ℝ) (n : ℕ) :
    brownianWickPowerLp hB v n =
      brownianPurePowerIntegral hB n (stepToLp v) := by
  cases n with
  | zero => exact (brownianPurePowerIntegral_zero_step hB v).symm
  | succ n =>
      apply (brownianWickPowerLp_eq_purePowerIntegral_iff_inner
        hB hsm v (n + 1)).2
      let wick := brownianWickPowerLp hB v (n + 1)
      let pure := brownianPurePowerIntegral hB (n + 1) (stepToLp v)
      let T : RandomL2 P →L[ℝ] ℝ := innerSL ℝ wick - innerSL ℝ pure
      let K : Submodule ℝ (RandomL2 P) := T.ker
      have hrange : brownianOrderedBoxOrderRange hB (n + 1) ≤ K := by
        rintro z ⟨c, rfl⟩
        change T (orderedBoxToRandom hB (n + 1) c) = 0
        change inner ℝ wick (orderedBoxToRandom hB (n + 1) c) -
          inner ℝ pure (orderedBoxToRandom hB (n + 1) c) = 0
        unfold orderedBoxToRandom
        simp only [Finsupp.linearCombination_apply, Finsupp.sum]
        rw [inner_sum, inner_sum]
        simp only [real_inner_smul_right]
        apply sub_eq_zero.mpr
        apply Finset.sum_congr rfl
        intro a ha
        rw [inner_brownianWickPowerLp_chainIntegralLp_eq_purePower
          hB coordinate coordinate_apply generated hsm]
      have hclosure :
          (brownianOrderedBoxOrderRange hB (n + 1)).topologicalClosure ≤ K := by
        apply Submodule.topologicalClosure_minimal
        · exact hrange
        · exact ContinuousLinearMap.isClosed_ker T
      have hpure : pure ∈ K := by
        apply hclosure
        rw [brownianOrderedBoxOrderRange_closure_eq_homogeneousChaos hB hsm n]
        exact brownianPurePowerIntegral_mem_brownianHomogeneousChaos
          hB (n + 1) (stepToLp v)
      change inner ℝ wick pure - inner ℝ pure pure = 0 at hpure
      rw [sub_eq_zero] at hpure
      rw [hpure, inner_brownianPurePowerIntegral hB hsm,
        real_inner_self_eq_norm_sq]

/-- Generated linear Brownian coordinates satisfy the full higher Hermite/multiple-integral
identity. -/
theorem higherHermiteMultipleIntegralIdentity_of_generated
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B) (hsm : ∀ t, StronglyMeasurable (B t)) :
    BrownianHigherHermiteMultipleIntegralIdentity hB := by
  intro v n hn
  exact brownianWickPowerLp_eq_purePowerIntegral_of_generated
    hB coordinate coordinate_apply generated hsm v n

/-- Generated linear Brownian coordinates satisfy the equivalent all-orders scalar mixed-inner
identity. -/
theorem wickPurePowerMixedInnerIdentity_of_generated
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B) (hsm : ∀ t, StronglyMeasurable (B t)) :
    BrownianWickPurePowerMixedInnerIdentity hB :=
  (higherHermiteMultipleIntegralIdentity_iff_fullMixedInner hB hsm).1
    (higherHermiteMultipleIntegralIdentity_of_generated
      hB coordinate coordinate_apply generated hsm)

/-- Consequently, the canonical pure-power multiple integrals satisfy the two-step Itô product
recurrence. -/
theorem purePowerRecurrence_of_generated
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B) (hsm : ∀ t, StronglyMeasurable (B t)) :
    BrownianPurePowerHermiteRecurrence hB :=
  purePowerRecurrence_of_higherHermiteMultipleIntegralIdentity hB hsm
    (higherHermiteMultipleIntegralIdentity_of_generated
      hB coordinate coordinate_apply generated hsm)

end Malliavin.BrownianIteratedConstruction

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
