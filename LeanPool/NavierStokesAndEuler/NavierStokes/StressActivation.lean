/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.OutgoingSchedule
public import LeanPool.NavierStokesAndEuler.NavierStokes.ParametricFlatFactor
public import LeanPool.NavierStokesAndEuler.NavierStokes.ReferencePath
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Actual initial stress activation

The activation integrates damped genuine reference derivatives. Error factors
are constructed from the flat primitive integral, never supplied as input.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.StressActivation

open Set Filter MeasureTheory Metric
open ProfileHistories
open scoped Topology ContDiff

/-- Log domain, bundling `carrier`, `isOpen`, `scale_mem`. -/
noncomputable def logDomain (J : Set ℝ) (hJ : IsOpen J) : RadialDomain where
  carrier := univ ×ˢ J
  isOpen := isOpen_univ.prod hJ
  scale_mem := fun _ hp _ _ => ⟨mem_univ _, hp.2⟩

/-- Activation, given by `(1 - κ) * OutgoingSchedule.sigma (y / T)`. -/
noncomputable def activation (T κ y : ℝ) : ℝ :=
  (1 - κ) * OutgoingSchedule.sigma (y / T)

/-- Damping, given by `1 - activation T κ y`. -/
noncomputable def damping (T κ y : ℝ) : ℝ := 1 - activation T κ y

theorem activation_smooth (T κ : ℝ) : ContDiff ℝ ∞ (activation T κ) :=
  contDiff_const.mul (OutgoingSchedule.sigma_contDiff.comp (contDiff_id.div_const T))

theorem damping_smooth (T κ : ℝ) : ContDiff ℝ ∞ (damping T κ) :=
  contDiff_const.sub (activation_smooth T κ)

theorem activation_nonneg (T κ y : ℝ) (hκ : κ ≤ 1) : 0 ≤ activation T κ y :=
  mul_nonneg (sub_nonneg.mpr hκ) (OutgoingSchedule.sigma_nonneg _)

theorem activation_le_one (T κ y : ℝ) (hκ : κ ∈ Icc (0 : ℝ) 1) :
    activation T κ y ≤ 1 := by
  have hs := OutgoingSchedule.sigma_le_one (y / T)
  have hl := OutgoingSchedule.sigma_nonneg (y / T)
  dsimp [activation]
  nlinarith [mul_nonneg hκ.1 hl]

theorem activation_monotone {T κ : ℝ} (hT : 0 < T) (hκ : κ ≤ 1) :
    Monotone (activation T κ) := by
  intro x y hxy
  exact mul_le_mul_of_nonneg_left
    (OutgoingSchedule.sigma_monotone ((div_le_div_iff_of_pos_right hT).mpr hxy))
    (sub_nonneg.mpr hκ)

theorem activation_zero {T : ℝ} (hT : 0 < T) (κ : ℝ) {y : ℝ} (hy : y ≤ 0) :
    activation T κ y = 0 := by
  simp [activation, OutgoingSchedule.sigma_zero
    (div_nonpos_of_nonpos_of_nonneg hy hT.le)]

/-- Weighted field, defined pointwise by `activation T κ p.1 * B p`. -/
noncomputable def weightedField (T κ : ℝ) (B : Field) : Field :=
  fun p => activation T κ p.1 * B p

/-- Weighted primitive, given by `primitive (weightedField T κ B)`. -/
noncomputable def weightedPrimitive (T κ : ℝ) (B : Field) : Field :=
  primitive (weightedField T κ B)

theorem weightedField_smooth (T κ : ℝ) {J : Set ℝ} (hJ : IsOpen J) {B : Field}
    (hB : ContDiffOn ℝ ∞ B (logDomain J hJ).carrier) :
    ContDiffOn ℝ ∞ (weightedField T κ B) (logDomain J hJ).carrier :=
  ((activation_smooth T κ).comp contDiff_fst).contDiffOn.mul hB

theorem weightedPrimitive_smooth (T κ : ℝ) {J : Set ℝ} (hJ : IsOpen J) {B : Field}
    (hB : ContDiffOn ℝ ∞ B (logDomain J hJ).carrier) :
    ContDiffOn ℝ ∞ (weightedPrimitive T κ B) (logDomain J hJ).carrier :=
  primitive_smooth (logDomain J hJ) (weightedField_smooth T κ hJ hB)

theorem weightedPrimitive_hasDerivAt (T κ : ℝ) {J : Set ℝ} (hJ : IsOpen J) {B : Field}
    (hB : ContDiffOn ℝ ∞ B (logDomain J hJ).carrier) (y : ℝ) {η : ℝ} (hη : η ∈ J) :
    HasDerivAt (fun x => weightedPrimitive T κ B (x, η))
      (activation T κ y * B (y, η)) y :=
  primitive_hasDerivAt (logDomain J hJ) (weightedField_smooth T κ hJ hB)
    (p := (y, η)) ⟨mem_univ _, hη⟩

theorem weightedPrimitive_zero {T : ℝ} (hT : 0 < T) (κ : ℝ) (B : Field)
    {y : ℝ} (hy : y ≤ 0) (η : ℝ) : weightedPrimitive T κ B (y, η) = 0 := by
  unfold weightedPrimitive primitive weightedField
  calc
    _ = ∫ _x in (0 : ℝ)..y, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hx0 : x ≤ 0 := (show x ∈ Icc y 0 by simpa only [uIcc_of_ge hy] using hx).2
      simp [activation_zero hT κ hx0]
    _ = 0 := by simp

/-- Direct integration of the reference derivative times the prescribed damping. -/
noncomputable def controlled (T κ : ℝ) (F : Field) : Field := fun p =>
  F (0, p.2) + primitive (fun q => damping T κ q.1 * radialPartial F q) p

theorem controlled_smooth (T κ : ℝ) {J : Set ℝ} (hJ : IsOpen J) {F : Field}
    (hF : ContDiffOn ℝ ∞ F (logDomain J hJ).carrier) :
    ContDiffOn ℝ ∞ (controlled T κ F) (logDomain J hJ).carrier := by
  apply ContDiffOn.add
  · exact hF.comp (contDiff_const.prodMk contDiff_snd).contDiffOn
      (fun p hp => ⟨mem_univ _, hp.2⟩)
  · exact primitive_smooth (logDomain J hJ)
      (((damping_smooth T κ).comp contDiff_fst).contDiffOn.mul
        (radialPartial_smooth (logDomain J hJ) hF))

theorem controlled_hasDerivAt (T κ : ℝ) {J : Set ℝ} (hJ : IsOpen J) {F : Field}
    (hF : ContDiffOn ℝ ∞ F (logDomain J hJ).carrier) (y : ℝ) {η : ℝ} (hη : η ∈ J) :
    HasDerivAt (fun x => controlled T κ F (x, η))
      (damping T κ y * radialPartial F (y, η)) y := by
  simpa only [controlled, zero_add, Function.comp_def] using (hasDerivAt_const y (F (0, η))).fun_add
    (primitive_hasDerivAt (logDomain J hJ)
      (((damping_smooth T κ).comp contDiff_fst).contDiffOn.mul
        (radialPartial_smooth (logDomain J hJ) hF)) (p := (y, η)) ⟨mem_univ _, hη⟩)

@[simp] theorem controlled_initial (T κ : ℝ) (F : Field) (η : ℝ) :
    controlled T κ F (0, η) = F (0, η) := by simp [controlled, primitive]

theorem controlled_sub (T κ : ℝ) {J : Set ℝ} (hJ : IsOpen J) {F : Field}
    (hF : ContDiffOn ℝ ∞ F (logDomain J hJ).carrier) (y : ℝ) {η : ℝ} (hη : η ∈ J) :
    controlled T κ F (y, η) - F (y, η) =
      -weightedPrimitive T κ (radialPartial F) (y, η) := by
  have hD := radialPartial_smooth (logDomain J hJ) hF
  have hi := radial_slice_intervalIntegrable (logDomain J hJ) hD
    (p := (y, η)) ⟨mem_univ _, hη⟩
  have hw := radial_slice_intervalIntegrable (logDomain J hJ)
    (weightedField_smooth T κ hJ hD) (p := (y, η)) ⟨mem_univ _, hη⟩
  change IntervalIntegrable (fun t => radialPartial F (t, η)) volume 0 y at hi
  change IntervalIntegrable (fun t => activation T κ t * radialPartial F (t, η)) volume 0 y at hw
  have hf : (∫ t in (0 : ℝ)..y, radialPartial F (t, η)) = F (y, η) - F (0, η) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => F (t, η))
    (fun t _ => radialPartial_hasDerivAt (logDomain J hJ) hF
      (p := (t, η)) ⟨mem_univ _, hη⟩) hi
  have he : (∫ t in (0 : ℝ)..y, damping T κ t * radialPartial F (t, η)) =
      (∫ t in (0 : ℝ)..y, radialPartial F (t, η)) -
        ∫ t in (0 : ℝ)..y, activation T κ t * radialPartial F (t, η) := by
    rw [← intervalIntegral.integral_sub hi hw]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp [damping]
    ring
  dsimp [controlled, weightedPrimitive, primitive, weightedField]
  rw [he, hf]
  ring

/-! ## A local-parameter version of the proved flat factor theorem -/

theorem flatFactor_local {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {c : ℝ} (hc : 0 < c) (j : ℕ)
    {J : Set E} (hJ : IsOpen J) {b : E × ℝ → ℝ}
    (hb : ContDiffOn ℝ ∞ b (J ×ˢ univ)) :
    ContDiffOn ℝ ∞ (ParametricFlatFactor.factor c j b) (J ×ˢ univ) := by
  intro p hp
  obtain ⟨r, hr, hrs⟩ : ∃ r, 0 < r ∧ closedBall p.1 r ⊆ J :=
    nhds_basis_closedBall.mem_iff.mp (hJ.mem_nhds hp.1)
  let χ : ContDiffBump p.1 :=
    { rIn := r / 2, rOut := r, rIn_pos := half_pos hr, rIn_lt_rOut := half_lt_self hr }
  let b' : E × ℝ → ℝ := fun q => χ q.1 * b q
  have hlocal : ContDiff ℝ ∞ b' := by
    apply contDiff_iff_contDiffAt.mpr
    intro q
    by_cases hq : q.1 ∈ J
    · exact (χ.contDiff.contDiffAt.comp q contDiffAt_fst).mul
        (hb.contDiffAt ((hJ.prod isOpen_univ).mem_nhds ⟨hq, mem_univ _⟩))
    · have hn : q.1 ∉ tsupport (χ : E → ℝ) := by
        rw [χ.tsupport_eq]
        exact fun hq' => hq (hrs hq')
      have hz : (χ : E → ℝ) =ᶠ[𝓝 q.1] 0 := notMem_tsupport_iff_eventuallyEq.mp hn
      have heq : b' =ᶠ[𝓝 q] 0 := by
        filter_upwards [continuousAt_fst.eventually hz] with z hz
        change χ z.1 * b z = 0
        change χ z.1 = 0 at hz
        rw [hz, zero_mul]
      exact contDiffAt_const.congr_of_eventuallyEq heq
  have heq : ParametricFlatFactor.factor c j b =ᶠ[𝓝 p]
      ParametricFlatFactor.factor c j b' := by
    filter_upwards [continuousAt_fst.eventually χ.eventuallyEq_one] with q hq
    unfold ParametricFlatFactor.factor
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun t => by
      dsimp [ParametricFlatFactor.kernel, b']
      rw [hq]
      simp
  exact ((ParametricFlatFactor.factor_contDiff hc j hlocal).contDiffAt.congr_of_eventuallyEq
    heq).contDiffWithinAt

/-- Step denominator, given by `FlatCutoff.edge 1 (y / T) + FlatCutoff.edge 1 (1 - y / T)`. -/
noncomputable def stepDenominator (T y : ℝ) : ℝ :=
  FlatCutoff.edge 1 (y / T) + FlatCutoff.edge 1 (1 - y / T)

theorem stepDenominator_pos (T y : ℝ) : 0 < stepDenominator T y :=
  OutgoingSchedule.sigma_denom_pos (y / T)

theorem stepDenominator_smooth (T : ℝ) : ContDiff ℝ ∞ (stepDenominator T) :=
  ((FlatCutoff.edge_contDiff (by norm_num : (0 : ℝ) < 1)).comp
    (contDiff_id.div_const T)).add
      ((FlatCutoff.edge_contDiff (by norm_num : (0 : ℝ) < 1)).comp
        (contDiff_const.sub (contDiff_id.div_const T)))

theorem edge_scaled {T : ℝ} (hT : 0 < T) (y : ℝ) :
    FlatCutoff.edge 1 (y / T) = FlatCutoff.edge (T ^ 2) y := by
  by_cases hy : y ≤ 0
  · rw [FlatCutoff.edge_of_nonpos 1 (div_nonpos_of_nonpos_of_nonneg hy hT.le),
      FlatCutoff.edge_of_nonpos (T ^ 2) hy]
  · have hy' : 0 < y := lt_of_not_ge hy
    rw [FlatCutoff.edge_of_pos 1 (div_pos hy' hT), FlatCutoff.edge_of_pos (T ^ 2) hy']
    congr 1
    field_simp

theorem activation_flat_form {T : ℝ} (hT : 0 < T) (κ y : ℝ) :
    activation T κ y = (1 - κ) * FlatCutoff.edge (T ^ 2) y / stepDenominator T y := by
  unfold activation OutgoingSchedule.sigma stepDenominator
  rw [edge_scaled hT]
  ring

/-- Flat coefficient, given by `B (q.2, q.1) / stepDenominator T q.2`. -/
noncomputable def flatCoefficient (T : ℝ) (B : Field) (q : ℝ × ℝ) : ℝ :=
  B (q.2, q.1) / stepDenominator T q.2

/-- Division by `y e_a` is implemented by a smooth transformed integral. -/
noncomputable def primitiveFactor (T : ℝ) (B : Field) (p : Point) : ℝ :=
  p.1 ^ 2 * stepDenominator T p.1 *
    ParametricFlatFactor.factor (T ^ 2) 0 (flatCoefficient T B) (p.2, p.1)

theorem flatCoefficient_smooth (T : ℝ) {J : Set ℝ} (hJ : IsOpen J) {B : Field}
    (hB : ContDiffOn ℝ ∞ B (logDomain J hJ).carrier) :
    ContDiffOn ℝ ∞ (flatCoefficient T B) (J ×ˢ univ) :=
  (hB.comp (contDiff_snd.prodMk contDiff_fst).contDiffOn (fun _ hp => ⟨hp.2, hp.1⟩)).div
    ((stepDenominator_smooth T).comp contDiff_snd).contDiffOn
    (fun p _ => (stepDenominator_pos T p.2).ne')

theorem primitiveFactor_smooth {T : ℝ} (hT : 0 < T) {J : Set ℝ} (hJ : IsOpen J)
    {B : Field} (hB : ContDiffOn ℝ ∞ B (logDomain J hJ).carrier) :
    ContDiffOn ℝ ∞ (primitiveFactor T B) (logDomain J hJ).carrier := by
  exact ((contDiff_fst.pow 2).mul ((stepDenominator_smooth T).comp contDiff_fst)).contDiffOn.mul
    ((flatFactor_local (sq_pos_of_pos hT) 0 hJ (flatCoefficient_smooth T hJ hB)).comp
      (contDiff_snd.prodMk contDiff_fst).contDiffOn (fun _ hp => ⟨hp.2, hp.1⟩))

@[simp] theorem primitiveFactor_zero (T : ℝ) (B : Field) (η : ℝ) :
    primitiveFactor T B (0, η) = 0 := by simp [primitiveFactor]

theorem weightedPrimitive_factorization {T : ℝ} (hT : 0 < T) (κ : ℝ) (B : Field)
    (p : Point) : weightedPrimitive T κ B p = p.1 * activation T κ p.1 * primitiveFactor T B p := by
  have hrepr : weightedPrimitive T κ B p = (1 - κ) *
      ParametricFlatFactor.primitive (T ^ 2) 0 (flatCoefficient T B) (p.2, p.1) := by
    unfold weightedPrimitive primitive weightedField ParametricFlatFactor.primitive
        FlatPrimitive.primitive
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    rw [activation_flat_form hT]
    dsimp [FlatPrimitive.integrand, flatCoefficient]
    ring
  rw [hrepr, ParametricFlatFactor.primitive_eq_scale_mul_factor, activation_flat_form hT]
  dsimp [FlatPrimitive.scale, primitiveFactor]
  field_simp [(stepDenominator_pos T p.1).ne']

/-- The basic quantitative estimate is uniform as `κ` tends to zero and in
the ramp length: its constant is only a bound for the reference coefficient. -/
theorem weightedPrimitive_bound {T κ M y : ℝ} (hT : 0 < T) (hκ : κ ≤ 1)
    (hM : 0 ≤ M) (hy : 0 ≤ y) (B : Field) (η : ℝ)
    (hB : ∀ t ∈ Icc (0 : ℝ) y, |B (t, η)| ≤ M) :
    |weightedPrimitive T κ B (y, η)| ≤ M * y * activation T κ y := by
  have hb : ∀ t ∈ uIoc (0 : ℝ) y,
      ‖activation T κ t * B (t, η)‖ ≤ M * activation T κ y := by
    intro t ht
    have ht' : t ∈ Ioc (0 : ℝ) y := by simpa only [uIoc_of_le hy] using ht
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (activation_nonneg T κ t hκ)]
    calc
      _ ≤ activation T κ t * M := mul_le_mul_of_nonneg_left (hB t ⟨ht'.1.le, ht'.2⟩)
        (activation_nonneg T κ t hκ)
      _ ≤ activation T κ y * M := mul_le_mul_of_nonneg_right (activation_monotone hT hκ ht'.2) hM
      _ = _ := mul_comm _ _
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const hb
  simpa only [weightedPrimitive, primitive, weightedField, Real.norm_eq_abs,
    sub_zero, abs_of_nonneg hy, mul_assoc, mul_left_comm, mul_comm] using hi

theorem controlled_difference_factorization {T : ℝ} (hT : 0 < T) (κ : ℝ)
    {J : Set ℝ} (hJ : IsOpen J) {F : Field}
    (hF : ContDiffOn ℝ ∞ F (logDomain J hJ).carrier) (y : ℝ) {η : ℝ} (hη : η ∈ J) :
    controlled T κ F (y, η) - F (y, η) =
      y * activation T κ y * (-primitiveFactor T (radialPartial F) (y, η)) := by
  rw [controlled_sub T κ hJ hF y hη, weightedPrimitive_factorization hT]
  ring

theorem weightedPrimitive_scale (T κ : ℝ) (B : Field) (p : Point) :
    weightedPrimitive T κ B p = (1 - κ) * weightedPrimitive T 0 B p := by
  unfold weightedPrimitive primitive weightedField activation
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  ring

/-- Mean exp, given by `average (fun p : Point => Real.exp p.1) (x, 0)`. -/
noncomputable def meanExp (x : ℝ) : ℝ :=
  average (fun p : Point => Real.exp p.1) (x, 0)

theorem meanExp_smooth : ContDiff ℝ ∞ meanExp := by
  have hf : ContDiffOn ℝ ∞ (fun p : Point => Real.exp p.1)
      (logDomain univ isOpen_univ).carrier := contDiff_fst.exp.contDiffOn
  have ha := average_smooth (logDomain univ isOpen_univ) hf
  have ha' : ContDiff ℝ ∞ (average (fun p : Point => Real.exp p.1)) := by
    simpa only [logDomain, univ_prod_univ, contDiffOn_univ] using ha
  exact ha'.comp (contDiff_id.prodMk contDiff_const)

theorem exp_sub_one (x : ℝ) : Real.exp x - 1 = x * meanExp x := by
  have hi : (∫ t in (0 : ℝ)..x, Real.exp t) = Real.exp x - 1 := by
    simpa only [Real.exp_zero] using intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => Real.hasDerivAt_exp t) (Real.continuous_exp.intervalIntegrable 0 x)
  calc
    _ = primitive (fun p : Point => Real.exp p.1) (x, 0) := hi.symm
    _ = _ := primitive_eq_mul_average _ _

/-- Reference angular, defined pointwise by `Real.exp (L p)`. -/
noncomputable def referenceAngular (L : Field) : Field := fun p => Real.exp (L p)
/-- Activated angular, defined pointwise by `Real.exp (controlled T κ L p)`. -/
noncomputable def activatedAngular (T κ : ℝ) (L : Field) : Field :=
  fun p => Real.exp (controlled T κ L p)
/-- Reference P1, defined pointwise by `-2 * radialPartial L p`. -/
noncomputable def referenceP1 (L : Field) : Field := fun p => -2 * radialPartial L p
/-- Radius, given by `X0 * Real.exp y`. -/
noncomputable def radius (X0 y : ℝ) : ℝ := X0 * Real.exp y
/-- Reference ns, defined pointwise by `-2 * radialPartial U p / radius X0 p.1`. -/
noncomputable def referenceNs (X0 : ℝ) (U : Field) : Field :=
  fun p => -2 * radialPartial U p / radius X0 p.1

theorem activatedAngular_pos (T κ : ℝ) (L : Field) (p : Point) :
    0 < activatedAngular T κ L p := Real.exp_pos _

theorem activatedAngular_smooth (T κ : ℝ) {J : Set ℝ} (hJ : IsOpen J) {L : Field}
    (hL : ContDiffOn ℝ ∞ L (logDomain J hJ).carrier) :
    ContDiffOn ℝ ∞ (activatedAngular T κ L) (logDomain J hJ).carrier :=
  (controlled_smooth T κ hJ hL).exp

/-- The first equation in (18), for the logarithm of the actual positive field. -/
theorem activation_angular_equation (T κ : ℝ) {J : Set ℝ} (hJ : IsOpen J) {L : Field}
    (hL : ContDiffOn ℝ ∞ L (logDomain J hJ).carrier) (y : ℝ) {η : ℝ} (hη : η ∈ J) :
    HasDerivAt (fun x => Real.log (activatedAngular T κ L (x, η)))
      (-(damping T κ y * referenceP1 L (y, η)) / 2) y := by
  simp only [activatedAngular, Real.log_exp]
  convert! controlled_hasDerivAt T κ hJ hL y hη using 1
  unfold referenceP1
  ring

/-- The second equation in (18), with `n_s` obtained from the reference field. -/
theorem activation_axial_equation (T κ : ℝ) {X0 : ℝ} (hX0 : 0 < X0)
    {J : Set ℝ} (hJ : IsOpen J) {U : Field}
    (hU : ContDiffOn ℝ ∞ U (logDomain J hJ).carrier) (y : ℝ) {η : ℝ} (hη : η ∈ J) :
    HasDerivAt (fun x => controlled T κ U (x, η))
      (-(damping T κ y * radius X0 y * referenceNs X0 U (y, η)) / 2) y := by
  convert! controlled_hasDerivAt T κ hJ hU y hη using 1
  have hr : radius X0 y ≠ 0 := ne_of_gt (mul_pos hX0 (Real.exp_pos y))
  unfold referenceNs
  field_simp

/-- Relative factor, given by `-primitiveFactor T (radialPartial L) p * meanExp
(-weightedPrimitive T κ (radialPartial L) p)`. -/
noncomputable def relativeFactor (T κ : ℝ) (L : Field) (p : Point) : ℝ :=
  -primitiveFactor T (radialPartial L) p *
    meanExp (-weightedPrimitive T κ (radialPartial L) p)

theorem relativeFactor_smooth {T : ℝ} (hT : 0 < T) (κ : ℝ)
    {J : Set ℝ} (hJ : IsOpen J) {L : Field}
    (hL : ContDiffOn ℝ ∞ L (logDomain J hJ).carrier) :
    ContDiffOn ℝ ∞ (relativeFactor T κ L) (logDomain J hJ).carrier := by
  have hD := radialPartial_smooth (logDomain J hJ) hL
  exact (primitiveFactor_smooth hT hJ hD).neg.mul
    (meanExp_smooth.comp_contDiffOn (weightedPrimitive_smooth T κ hJ hD).neg)

@[simp] theorem relativeFactor_zero (T κ : ℝ) (L : Field) (η : ℝ) :
    relativeFactor T κ L (0, η) = 0 := by simp [relativeFactor]

theorem angular_relative_difference {T : ℝ} (hT : 0 < T) (κ : ℝ)
    {J : Set ℝ} (hJ : IsOpen J) {L : Field}
    (hL : ContDiffOn ℝ ∞ L (logDomain J hJ).carrier) (y : ℝ) {η : ℝ} (hη : η ∈ J) :
    activatedAngular T κ L (y, η) / referenceAngular L (y, η) - 1 =
      y * activation T κ y * relativeFactor T κ L (y, η) := by
  rw [activatedAngular, referenceAngular, ← Real.exp_sub,
    controlled_sub T κ hJ hL y hη, exp_sub_one]
  unfold relativeFactor
  rw [weightedPrimitive_factorization hT]
  ring

theorem controlled_eq_reference_before {T : ℝ} (hT : 0 < T) (κ : ℝ)
    {J : Set ℝ} (hJ : IsOpen J) {F : Field}
    (hF : ContDiffOn ℝ ∞ F (logDomain J hJ).carrier) {y : ℝ} (hy : y ≤ 0)
    {η : ℝ} (hη : η ∈ J) : controlled T κ F (y, η) = F (y, η) := by
  have he := controlled_sub T κ hJ hF y hη
  rw [weightedPrimitive_zero hT κ _ hy, neg_zero] at he
  exact sub_eq_zero.mp he

/-! ## Actual parameter jets, uniformly including κ=0 -/

/-- Family point: an abbreviation for `(ℝ × ℝ) × ℝ`. -/
abbrev FamilyPoint := (ℝ × ℝ) × ℝ

/-- Relative family, given by `relativeFactor T q.1.1 L (q.1.2, q.2)`. -/
noncomputable def relativeFamily (T : ℝ) (L : Field) (q : FamilyPoint) : ℝ :=
  relativeFactor T q.1.1 L (q.1.2, q.2)

/-- Difference family, given by `-primitiveFactor T (radialPartial F) (q.1.2, q.2)`. -/
noncomputable def differenceFamily (T : ℝ) (F : Field) (q : FamilyPoint) : ℝ :=
  -primitiveFactor T (radialPartial F) (q.1.2, q.2)

theorem relativeFamily_smooth {T : ℝ} (hT : 0 < T) {J : Set ℝ} (hJ : IsOpen J)
    {L : Field} (hL : ContDiffOn ℝ ∞ L (logDomain J hJ).carrier) :
    ContDiffOn ℝ ∞ (relativeFamily T L) ((univ : Set (ℝ × ℝ)) ×ˢ J) := by
  have hD := radialPartial_smooth (logDomain J hJ) hL
  have hp := primitiveFactor_smooth hT hJ hD
  have hw := weightedPrimitive_smooth T 0 hJ hD
  intro q hq
  have hm : ContDiffAt ℝ ∞ (fun z : FamilyPoint => (z.1.2, z.2)) q :=
    contDiffAt_fst.snd.prodMk contDiffAt_snd
  have hp' := (hp.contDiffAt ((logDomain J hJ).isOpen.mem_nhds
    (show (q.1.2, q.2) ∈ (logDomain J hJ).carrier from ⟨mem_univ _, hq.2⟩))).comp q hm
  have hw' := (hw.contDiffAt ((logDomain J hJ).isOpen.mem_nhds
    (show (q.1.2, q.2) ∈ (logDomain J hJ).carrier from ⟨mem_univ _, hq.2⟩))).comp q hm
  have hh : ContDiffAt ℝ ∞
      (fun z : FamilyPoint => -primitiveFactor T (radialPartial L) (z.1.2, z.2) *
        meanExp (-((1 - z.1.1) * weightedPrimitive T 0 (radialPartial L) (z.1.2, z.2)))) q :=
    hp'.neg.mul (meanExp_smooth.contDiffAt.comp q
      ((contDiffAt_const.sub contDiffAt_fst.fst).mul hw').neg)
  convert! hh.contDiffWithinAt using 1
  funext z
  simp only [relativeFamily, relativeFactor, weightedPrimitive_scale T z.1.1]

theorem differenceFamily_smooth {T : ℝ} (hT : 0 < T) {J : Set ℝ} (hJ : IsOpen J)
    {F : Field} (hF : ContDiffOn ℝ ∞ F (logDomain J hJ).carrier) :
    ContDiffOn ℝ ∞ (differenceFamily T F) ((univ : Set (ℝ × ℝ)) ×ˢ J) :=
  ((primitiveFactor_smooth hT hJ (radialPartial_smooth (logDomain J hJ) hF)).neg).comp
    (contDiff_fst.snd.prodMk contDiff_snd).contDiffOn (fun _ hp => ⟨mem_univ _, hp.2⟩)

/-- Compactness bounds the genuine η derivatives of a jointly smooth family.
In particular the compact κ range contains zero; inverse powers of κ cannot enter. -/
theorem compact_parameter_jet_bound {J K : Set ℝ} (hJ : IsOpen J)
    (hK : IsCompact K) (hKJ : K ⊆ J) {H : FamilyPoint → ℝ}
    (hH : ContDiffOn ℝ ∞ H ((univ : Set (ℝ × ℝ)) ×ˢ J)) (T : ℝ) (n : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ κ ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) T, ∀ η ∈ K,
      |iteratedDeriv n (fun ξ => H ((κ, y), ξ)) η| ≤ M := by
  have hc : ContinuousOn
      (fun q : FamilyPoint => iteratedFDeriv ℝ n (fun ξ => H (q.1, ξ)) q.2)
      ((univ : Set (ℝ × ℝ)) ×ˢ J) := by
    intro q hq
    exact (ParametricFlatFactor.contDiffAt_partial_iteratedFDeriv
      (fun v ξ => H (v, ξ)) n q.1 q.2
      (hH.contDiffAt ((isOpen_univ.prod hJ).mem_nhds hq))).continuousAt.continuousWithinAt
  have hcompact : IsCompact ((Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) T) ×ˢ K) :=
    (isCompact_Icc.prod isCompact_Icc).prod hK
  obtain ⟨M, hM⟩ := hcompact.exists_bound_of_continuousOn
    (hc.mono (fun q hq => ⟨mem_univ _, hKJ hq.2⟩))
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  intro κ hκ y hy η hη
  have hb := hM ((κ, y), η) ⟨⟨hκ, hy⟩, hη⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] at hb
  exact hb.trans (le_max_left _ _)

theorem scaled_family_jet_bound {T : ℝ} (_hT : 0 < T) {J K : Set ℝ}
    (hJ : IsOpen J) (hK : IsCompact K) (hKJ : K ⊆ J)
    {H : FamilyPoint → ℝ} (hH : ContDiffOn ℝ ∞ H ((univ : Set (ℝ × ℝ)) ×ˢ J))
    {E : ℝ → ℝ → ℝ → ℝ}
    (hE : ∀ κ y, ∀ η ∈ J, E κ y η = y * activation T κ y * H ((κ, y), η))
    (n : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ κ ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) T, ∀ η ∈ K,
      |iteratedDeriv n (E κ y) η| ≤ M * y * activation T κ y := by
  obtain ⟨M, hM, hbound⟩ := compact_parameter_jet_bound hJ hK hKJ hH T n
  refine ⟨M, hM, ?_⟩
  intro κ hκ y hy η hη
  have heq : E κ y =ᶠ[𝓝 η] (fun ξ => y * activation T κ y * H ((κ, y), ξ)) := by
    filter_upwards [hJ.mem_nhds (hKJ hη)] with ξ hξ
    exact hE κ y ξ hξ
  rw [heq.iteratedDeriv_eq n]
  have hh : ContDiffAt ℝ ∞ (fun ξ => H ((κ, y), ξ)) η :=
    (hH.contDiffAt ((isOpen_univ.prod hJ).mem_nhds ⟨mem_univ _, hKJ hη⟩)).comp η
      (contDiffAt_const.prodMk contDiffAt_id)
  rw [iteratedDeriv_const_mul (n := n) _ (hh.of_le (WithTop.coe_le_coe.mpr le_top)), abs_mul,
    abs_of_nonneg (mul_nonneg hy.1 (activation_nonneg T κ y hκ.2))]
  have hb := mul_le_mul_of_nonneg_left (hbound κ hκ y hy η hη)
    (mul_nonneg hy.1 (activation_nonneg T κ y hκ.2))
  nlinarith

theorem controlled_parameter_jet_bounds {T : ℝ} (hT : 0 < T) {J K : Set ℝ}
    (hJ : IsOpen J) (hK : IsCompact K) (hKJ : K ⊆ J) {F : Field}
    (hF : ContDiffOn ℝ ∞ F (logDomain J hJ).carrier) (n : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ κ ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) T, ∀ η ∈ K,
      |iteratedDeriv n (fun ξ => controlled T κ F (y, ξ) - F (y, ξ)) η| ≤
        M * y * activation T κ y := by
  apply scaled_family_jet_bound hT hJ hK hKJ (differenceFamily_smooth hT hJ hF)
  intro κ y η hη
  exact controlled_difference_factorization hT κ hJ hF y hη

theorem angular_relative_parameter_jet_bounds {T : ℝ} (hT : 0 < T) {J K : Set ℝ}
    (hJ : IsOpen J) (hK : IsCompact K) (hKJ : K ⊆ J) {L : Field}
    (hL : ContDiffOn ℝ ∞ L (logDomain J hJ).carrier) (n : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ κ ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) T, ∀ η ∈ K,
      |iteratedDeriv n (fun ξ =>
        activatedAngular T κ L (y, ξ) / referenceAngular L (y, ξ) - 1) η| ≤
          M * y * activation T κ y := by
  apply scaled_family_jet_bound hT hJ hK hKJ (relativeFamily_smooth hT hJ hL)
  intro κ y η hη
  exact angular_relative_difference hT κ hJ hL y hη

/-! ## Flat integrals of smoothly parameterized families -/

/-- Family flat coefficient, given by `B ((q.1.1, q.2), q.1.2) / stepDenominator T q.2`. -/
noncomputable def familyFlatCoefficient (T : ℝ) (B : FamilyPoint → ℝ)
    (q : (ℝ × ℝ) × ℝ) : ℝ :=
  B ((q.1.1, q.2), q.1.2) / stepDenominator T q.2

/-- Family primitive factor, given by `q.1.2 ^ 2 * stepDenominator T q.1.2 *
ParametricFlatFactor.factor (T ^ 2) 0 (familyFlatCoefficient T B) ((q.1.1, q.2), q.1.2)`. -/
noncomputable def familyPrimitiveFactor (T : ℝ) (B : FamilyPoint → ℝ)
    (q : FamilyPoint) : ℝ :=
  q.1.2 ^ 2 * stepDenominator T q.1.2 *
    ParametricFlatFactor.factor (T ^ 2) 0 (familyFlatCoefficient T B)
      ((q.1.1, q.2), q.1.2)

theorem familyPrimitiveFactor_eq (T : ℝ) (B : FamilyPoint → ℝ) (κ y η : ℝ) :
    familyPrimitiveFactor T B ((κ, y), η) =
      primitiveFactor T (fun p => B ((κ, p.1), p.2)) (y, η) := rfl

theorem familyPrimitiveFactor_smooth {T : ℝ} (hT : 0 < T) {J : Set ℝ} (hJ : IsOpen J)
    {B : FamilyPoint → ℝ}
    (hB : ContDiffOn ℝ ∞ B ((univ : Set (ℝ × ℝ)) ×ˢ J)) :
    ContDiffOn ℝ ∞ (familyPrimitiveFactor T B) ((univ : Set (ℝ × ℝ)) ×ˢ J) := by
  have hb : ContDiffOn ℝ ∞ (familyFlatCoefficient T B) ((univ ×ˢ J) ×ˢ (univ : Set ℝ)) :=
    (hB.comp ((contDiff_fst.fst.prodMk contDiff_snd).prodMk contDiff_fst.snd).contDiffOn
      (fun _ hp => ⟨mem_univ _, hp.1.2⟩)).div
        ((stepDenominator_smooth T).comp contDiff_snd).contDiffOn
        (fun q _ => (stepDenominator_pos T q.2).ne')
  have hf := flatFactor_local (sq_pos_of_pos hT) 0 (isOpen_univ.prod hJ) hb
  exact ((contDiff_fst.snd.pow 2).mul
    ((stepDenominator_smooth T).comp contDiff_fst.snd)).contDiffOn.mul
      (hf.comp ((contDiff_fst.fst.prodMk contDiff_snd).prodMk contDiff_fst.snd).contDiffOn
        (fun _ hp => ⟨⟨mem_univ _, hp.2⟩, mem_univ _⟩))

theorem weighted_family_parameter_jet_bounds {T : ℝ} (hT : 0 < T) {J K : Set ℝ}
    (hJ : IsOpen J) (hK : IsCompact K) (hKJ : K ⊆ J)
    {B : FamilyPoint → ℝ} (hB : ContDiffOn ℝ ∞ B ((univ : Set (ℝ × ℝ)) ×ˢ J)) (n : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ κ ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) T, ∀ η ∈ K,
      |iteratedDeriv n (fun ξ =>
        weightedPrimitive T κ (fun p => B ((κ, p.1), p.2)) (y, ξ)) η| ≤
          M * y * activation T κ y := by
  apply scaled_family_jet_bound hT hJ hK hKJ (familyPrimitiveFactor_smooth hT hJ hB)
  intro κ y η _
  rw [familyPrimitiveFactor_eq]
  exact weightedPrimitive_factorization hT κ _ _

/-! ## The five actual pressure and moment histories -/

/-- History row data for stress activation. -/
inductive HistoryRow
  | mass | angular | transport | energy | pressure

/-- These are the integrands used by `ProfileHistories.Profiles`. -/
noncomputable def radialDensity : HistoryRow → ℝ → ℝ → ℝ → ℝ
  | .mass, _, _, u => u
  | .angular, x, f, _ => 2 * x * f
  | .transport, x, f, u => u * (2 * x * f)
  | .energy, x, f, u => u ^ 2 - x * f ^ 2
  | .pressure, _, f, _ => f ^ 2

/-- The Jacobian `X` converts the physical radial histories to log time. -/
noncomputable def logDensity (X0 : ℝ) (f U : Field) (r : HistoryRow) : Field :=
  fun p => radius X0 p.1 * radialDensity r (radius X0 p.1) (f p) (U p)

/-- The initial row values are shared; every subsequent value is recomputed. -/
noncomputable def logHistory (X0 : ℝ) (initial : HistoryRow → ℝ → ℝ)
    (f U : Field) (r : HistoryRow) : Field :=
  fun p => initial r p.2 + primitive (logDensity X0 f U r) p

theorem radius_smooth (X0 : ℝ) : ContDiff ℝ ∞ (radius X0) :=
  contDiff_const.mul Real.contDiff_exp

theorem logDensity_smooth (X0 : ℝ) {J : Set ℝ} (hJ : IsOpen J) {f U : Field}
    (hf : ContDiffOn ℝ ∞ f (logDomain J hJ).carrier)
    (hU : ContDiffOn ℝ ∞ U (logDomain J hJ).carrier) (r : HistoryRow) :
    ContDiffOn ℝ ∞ (logDensity X0 f U r) (logDomain J hJ).carrier := by
  have hx := ((radius_smooth X0).comp contDiff_fst).contDiffOn
    (s := (logDomain J hJ).carrier)
  cases r with
  | mass => exact hx.mul hU
  | angular => exact hx.mul ((contDiffOn_const.mul hx).mul hf)
  | transport => exact hx.mul (hU.mul ((contDiffOn_const.mul hx).mul hf))
  | energy => exact hx.mul ((hU.pow 2).sub (hx.mul (hf.pow 2)))
  | pressure => exact hx.mul (hf.pow 2)

theorem logHistory_smooth (X0 : ℝ) (initial : HistoryRow → ℝ → ℝ)
    {J : Set ℝ} (hJ : IsOpen J) {f U : Field}
    (hf : ContDiffOn ℝ ∞ f (logDomain J hJ).carrier)
    (hU : ContDiffOn ℝ ∞ U (logDomain J hJ).carrier) (r : HistoryRow)
    (hi : ContDiffOn ℝ ∞ (initial r) J) :
    ContDiffOn ℝ ∞ (logHistory X0 initial f U r) (logDomain J hJ).carrier :=
  (hi.comp contDiffOn_snd (fun _ hp => hp.2)).add
    (primitive_smooth (logDomain J hJ) (logDensity_smooth X0 hJ hf hU r))

@[simp] theorem logHistory_initial (X0 : ℝ) (initial : HistoryRow → ℝ → ℝ)
    (f U : Field) (r : HistoryRow) (η : ℝ) :
    logHistory X0 initial f U r (0, η) = initial r η := by
  simp [logHistory, primitive]

/-- Field family, given by `F (q.1.2, q.2)`. -/
noncomputable def fieldFamily (F : Field) (q : FamilyPoint) : ℝ := F (q.1.2, q.2)

theorem fieldFamily_smooth {J : Set ℝ} (hJ : IsOpen J) {F : Field}
    (hF : ContDiffOn ℝ ∞ F (logDomain J hJ).carrier) :
    ContDiffOn ℝ ∞ (fieldFamily F) ((univ : Set (ℝ × ℝ)) ×ˢ J) :=
  hF.comp (contDiff_fst.snd.prodMk contDiff_snd).contDiffOn
    (fun _ hp => ⟨mem_univ _, hp.2⟩)

/-- Controlled family, given by `controlled T q.1.1 F (q.1.2, q.2)`. -/
noncomputable def controlledFamily (T : ℝ) (F : Field) (q : FamilyPoint) : ℝ :=
  controlled T q.1.1 F (q.1.2, q.2)

theorem controlledFamily_smooth (T : ℝ) {J : Set ℝ} (hJ : IsOpen J) {F : Field}
    (hF : ContDiffOn ℝ ∞ F (logDomain J hJ).carrier) :
    ContDiffOn ℝ ∞ (controlledFamily T F) ((univ : Set (ℝ × ℝ)) ×ˢ J) := by
  have hw := fieldFamily_smooth hJ
    (weightedPrimitive_smooth T 0 hJ (radialPartial_smooth (logDomain J hJ) hF))
  have hc : ContDiffOn ℝ ∞
      (fun q : FamilyPoint => fieldFamily F q -
        (1 - q.1.1) * fieldFamily (weightedPrimitive T 0 (radialPartial F)) q)
      ((univ : Set (ℝ × ℝ)) ×ˢ J) :=
    (fieldFamily_smooth hJ hF).sub
      ((contDiffOn_const.sub contDiffOn_fst.fst).mul hw)
  apply hc.congr
  intro q hq
  have he := controlled_sub T q.1.1 hJ hF q.1.2 hq.2
  rw [weightedPrimitive_scale] at he
  dsimp only [controlledFamily, fieldFamily]
  linarith

/-- Angular family, given by `activatedAngular T q.1.1 L (q.1.2, q.2)`. -/
noncomputable def angularFamily (T : ℝ) (L : Field) (q : FamilyPoint) : ℝ :=
  activatedAngular T q.1.1 L (q.1.2, q.2)

theorem angularFamily_smooth (T : ℝ) {J : Set ℝ} (hJ : IsOpen J) {L : Field}
    (hL : ContDiffOn ℝ ∞ L (logDomain J hJ).carrier) :
    ContDiffOn ℝ ∞ (angularFamily T L) ((univ : Set (ℝ × ℝ)) ×ˢ J) :=
  (controlledFamily_smooth T hJ hL).exp

/-- Angular difference family, given by `fieldFamily (referenceAngular L) q * relativeFamily T L
q`. -/
noncomputable def angularDifferenceFamily (T : ℝ) (L : Field) (q : FamilyPoint) : ℝ :=
  fieldFamily (referenceAngular L) q * relativeFamily T L q

theorem angularDifferenceFamily_smooth {T : ℝ} (hT : 0 < T)
    {J : Set ℝ} (hJ : IsOpen J) {L : Field}
    (hL : ContDiffOn ℝ ∞ L (logDomain J hJ).carrier) :
    ContDiffOn ℝ ∞ (angularDifferenceFamily T L) ((univ : Set (ℝ × ℝ)) ×ˢ J) :=
  (fieldFamily_smooth hJ hL.exp).mul (relativeFamily_smooth hT hJ hL)

theorem angular_difference_factorization {T : ℝ} (hT : 0 < T) (κ : ℝ)
    {J : Set ℝ} (hJ : IsOpen J) {L : Field}
    (hL : ContDiffOn ℝ ∞ L (logDomain J hJ).carrier) (y : ℝ) {η : ℝ} (hη : η ∈ J) :
    activatedAngular T κ L (y, η) - referenceAngular L (y, η) =
      y * activation T κ y * angularDifferenceFamily T L ((κ, y), η) := by
  have hr : referenceAngular L (y, η) ≠ 0 := (Real.exp_pos _).ne'
  calc
    _ = referenceAngular L (y, η) *
        (activatedAngular T κ L (y, η) / referenceAngular L (y, η) - 1) := by
      field_simp
    _ = _ := by
      rw [angular_relative_difference hT κ hJ hL y hη]
      dsimp only [angularDifferenceFamily, fieldFamily, relativeFamily]
      ring

/-- Density difference family as an element of `ℝ`. -/
noncomputable def densityDifferenceFamily (T X0 : ℝ) (L U : Field)
    (r : HistoryRow) (q : FamilyPoint) : ℝ :=
  let x := radius X0 q.1.2
  let df := angularDifferenceFamily T L q
  let du := differenceFamily T U q
  let fa := angularFamily T L q
  let fr := fieldFamily (referenceAngular L) q
  let ua := controlledFamily T U q
  let ur := fieldFamily U q
  match r with
  | .mass => x * du
  | .angular => 2 * x ^ 2 * df
  | .transport => 2 * x ^ 2 * (df * ua + fr * du)
  | .energy => x * (du * (ua + ur) - x * df * (fa + fr))
  | .pressure => x * df * (fa + fr)

theorem densityDifferenceFamily_smooth {T : ℝ} (hT : 0 < T) (X0 : ℝ)
    {J : Set ℝ} (hJ : IsOpen J) {L U : Field}
    (hL : ContDiffOn ℝ ∞ L (logDomain J hJ).carrier)
    (hU : ContDiffOn ℝ ∞ U (logDomain J hJ).carrier) (r : HistoryRow) :
    ContDiffOn ℝ ∞ (densityDifferenceFamily T X0 L U r)
      ((univ : Set (ℝ × ℝ)) ×ˢ J) := by
  have hx := ((radius_smooth X0).comp contDiff_fst.snd).contDiffOn
    (s := ((univ : Set (ℝ × ℝ)) ×ˢ J))
  have hdf := angularDifferenceFamily_smooth hT hJ hL
  have hdu := differenceFamily_smooth hT hJ hU
  have hfa := angularFamily_smooth T hJ hL
  have hfr := fieldFamily_smooth hJ hL.exp
  have hua := controlledFamily_smooth T hJ hU
  have hur := fieldFamily_smooth hJ hU
  cases r with
  | mass => exact hx.mul hdu
  | angular => exact (contDiffOn_const.mul (hx.pow 2)).mul hdf
  | transport =>
    exact (contDiffOn_const.mul (hx.pow 2)).mul ((hdf.mul hua).add (hfr.mul hdu))
  | energy => exact hx.mul ((hdu.mul (hua.add hur)).sub ((hx.mul hdf).mul (hfa.add hfr)))
  | pressure => exact (hx.mul hdf).mul (hfa.add hfr)

theorem density_difference_factorization {T : ℝ} (hT : 0 < T) (κ X0 : ℝ)
    {J : Set ℝ} (hJ : IsOpen J) {L U : Field}
    (hL : ContDiffOn ℝ ∞ L (logDomain J hJ).carrier)
    (hU : ContDiffOn ℝ ∞ U (logDomain J hJ).carrier)
    (r : HistoryRow) (y : ℝ) {η : ℝ} (hη : η ∈ J) :
    logDensity X0 (activatedAngular T κ L) (controlled T κ U) r (y, η) -
      logDensity X0 (referenceAngular L) U r (y, η) =
        y * activation T κ y * densityDifferenceFamily T X0 L U r ((κ, y), η) := by
  have hf := angular_difference_factorization hT κ hJ hL y hη
  have hu := controlled_difference_factorization hT κ hJ hU y hη
  have hf' : angularFamily T L ((κ, y), η) = fieldFamily (referenceAngular L) ((κ, y), η) +
      y * activation T κ y * angularDifferenceFamily T L ((κ, y), η) := by
    dsimp only [angularFamily, fieldFamily]
    linarith
  have hu' : controlledFamily T U ((κ, y), η) = fieldFamily U ((κ, y), η) +
      y * activation T κ y * differenceFamily T U ((κ, y), η) := by
    dsimp only [controlledFamily, fieldFamily, differenceFamily]
    linarith
  change radius X0 y * radialDensity r (radius X0 y) (angularFamily T L ((κ, y), η))
      (controlledFamily T U ((κ, y), η)) -
    radius X0 y * radialDensity r (radius X0 y) (fieldFamily (referenceAngular L) ((κ, y), η))
      (fieldFamily U ((κ, y), η)) = _
  cases r <;> dsimp only [radialDensity, densityDifferenceFamily] <;>
    simp only [hf', hu'] <;> ring

/-- History integrand family, given by `q.1.2 * densityDifferenceFamily T X0 L U r q`. -/
noncomputable def historyIntegrandFamily (T X0 : ℝ) (L U : Field)
    (r : HistoryRow) (q : FamilyPoint) : ℝ :=
  q.1.2 * densityDifferenceFamily T X0 L U r q

theorem historyIntegrandFamily_smooth {T : ℝ} (hT : 0 < T) (X0 : ℝ)
    {J : Set ℝ} (hJ : IsOpen J) {L U : Field}
    (hL : ContDiffOn ℝ ∞ L (logDomain J hJ).carrier)
    (hU : ContDiffOn ℝ ∞ U (logDomain J hJ).carrier) (r : HistoryRow) :
    ContDiffOn ℝ ∞ (historyIntegrandFamily T X0 L U r)
      ((univ : Set (ℝ × ℝ)) ×ˢ J) :=
  contDiffOn_fst.snd.mul (densityDifferenceFamily_smooth hT X0 hJ hL hU r)

theorem history_difference_integral {T : ℝ} (hT : 0 < T) (κ X0 : ℝ)
    (initial : HistoryRow → ℝ → ℝ) {J : Set ℝ} (hJ : IsOpen J) {L U : Field}
    (hL : ContDiffOn ℝ ∞ L (logDomain J hJ).carrier)
    (hU : ContDiffOn ℝ ∞ U (logDomain J hJ).carrier)
    (r : HistoryRow) (y : ℝ) {η : ℝ} (hη : η ∈ J) :
    logHistory X0 initial (activatedAngular T κ L) (controlled T κ U) r (y, η) -
      logHistory X0 initial (referenceAngular L) U r (y, η) =
        weightedPrimitive T κ (fun p => historyIntegrandFamily T X0 L U r ((κ, p.1), p.2))
          (y, η) := by
  have ha := radial_slice_intervalIntegrable (logDomain J hJ)
    (logDensity_smooth X0 hJ (activatedAngular_smooth T κ hJ hL)
      (controlled_smooth T κ hJ hU) r) (p := (y, η)) ⟨mem_univ _, hη⟩
  have hr := radial_slice_intervalIntegrable (logDomain J hJ)
    (logDensity_smooth X0 hJ hL.exp hU r) (p := (y, η)) ⟨mem_univ _, hη⟩
  change IntervalIntegrable
    (fun t => logDensity X0 (activatedAngular T κ L) (controlled T κ U) r (t, η)) volume 0 y at ha
  change IntervalIntegrable (fun t => logDensity X0 (referenceAngular L) U r (t, η)) volume 0 y
      at hr
  dsimp only [logHistory, primitive]
  rw [add_sub_add_left_eq_sub, ← intervalIntegral.integral_sub ha hr]
  unfold weightedPrimitive primitive weightedField
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [density_difference_factorization hT κ X0 hJ hL hU r t hη]
  dsimp only [historyIntegrandFamily]
  ring

/-- History difference family, given by `familyPrimitiveFactor T (historyIntegrandFamily T X0 L
U r)`. -/
noncomputable def historyDifferenceFamily (T X0 : ℝ) (L U : Field)
    (r : HistoryRow) : FamilyPoint → ℝ :=
  familyPrimitiveFactor T (historyIntegrandFamily T X0 L U r)

theorem historyDifferenceFamily_smooth {T : ℝ} (hT : 0 < T) (X0 : ℝ)
    {J : Set ℝ} (hJ : IsOpen J) {L U : Field}
    (hL : ContDiffOn ℝ ∞ L (logDomain J hJ).carrier)
    (hU : ContDiffOn ℝ ∞ U (logDomain J hJ).carrier) (r : HistoryRow) :
    ContDiffOn ℝ ∞ (historyDifferenceFamily T X0 L U r)
      ((univ : Set (ℝ × ℝ)) ×ˢ J) :=
  familyPrimitiveFactor_smooth hT hJ (historyIntegrandFamily_smooth hT X0 hJ hL hU r)

@[simp] theorem historyDifferenceFamily_zero (T X0 : ℝ) (L U : Field)
    (r : HistoryRow) (κ η : ℝ) :
    historyDifferenceFamily T X0 L U r ((κ, 0), η) = 0 := by
  simp [historyDifferenceFamily, familyPrimitiveFactor]

theorem history_difference_factorization {T : ℝ} (hT : 0 < T) (κ X0 : ℝ)
    (initial : HistoryRow → ℝ → ℝ) {J : Set ℝ} (hJ : IsOpen J) {L U : Field}
    (hL : ContDiffOn ℝ ∞ L (logDomain J hJ).carrier)
    (hU : ContDiffOn ℝ ∞ U (logDomain J hJ).carrier)
    (r : HistoryRow) (y : ℝ) {η : ℝ} (hη : η ∈ J) :
    logHistory X0 initial (activatedAngular T κ L) (controlled T κ U) r (y, η) -
      logHistory X0 initial (referenceAngular L) U r (y, η) =
        y * activation T κ y * historyDifferenceFamily T X0 L U r ((κ, y), η) := by
  rw [history_difference_integral hT κ X0 initial hJ hL hU r y hη,
    weightedPrimitive_factorization hT]
  rfl

theorem history_parameter_jet_bounds {T : ℝ} (hT : 0 < T) (X0 : ℝ)
    (initial : HistoryRow → ℝ → ℝ) {J K : Set ℝ}
    (hJ : IsOpen J) (hK : IsCompact K) (hKJ : K ⊆ J) {L U : Field}
    (hL : ContDiffOn ℝ ∞ L (logDomain J hJ).carrier)
    (hU : ContDiffOn ℝ ∞ U (logDomain J hJ).carrier) (r : HistoryRow) (n : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ κ ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) T, ∀ η ∈ K,
      |iteratedDeriv n (fun ξ =>
        logHistory X0 initial (activatedAngular T κ L) (controlled T κ U) r (y, ξ) -
          logHistory X0 initial (referenceAngular L) U r (y, ξ)) η| ≤
            M * y * activation T κ y := by
  apply scaled_family_jet_bound hT hJ hK hKJ (historyDifferenceFamily_smooth hT X0 hJ hL hU r)
  intro κ y η hη
  exact history_difference_factorization hT κ X0 initial hJ hL hU r y hη

/-! ## Identification with the physical `ProfileHistories` integrals -/

/-- Profile density, defined pointwise by `radialDensity r p.1 (P.f p) (P.U p)`. -/
noncomputable def profileDensity {D : RadialDomain} (P : Profiles D)
    (r : HistoryRow) : Field := fun p => radialDensity r p.1 (P.f p) (P.U p)

/-- Profile history as an element of `HistoryRow → Field | .mass => P.M | .angular => P.I |
.transport => P.J | .energy => P.S | .pressure => P.pressure`. -/
noncomputable def profileHistory {D : RadialDomain} (P : Profiles D) : HistoryRow → Field
  | .mass => P.M
  | .angular => P.I
  | .transport => P.J
  | .energy => P.S
  | .pressure => P.pressure

/-- Profile initial as an element of `HistoryRow → ℝ → ℝ | .pressure => P.pressure0 | _ => fun _
=> 0`. -/
noncomputable def profileInitial {D : RadialDomain} (P : Profiles D) : HistoryRow → ℝ → ℝ
  | .pressure => P.pressure0
  | _ => fun _ => 0

theorem profileHistory_eq_initial_add_primitive {D : RadialDomain} (P : Profiles D)
    (r : HistoryRow) (p : Point) :
    profileHistory P r p = profileInitial P r p.2 + primitive (profileDensity P r) p := by
  cases r <;> simp only [profileHistory, profileInitial, zero_add] <;> rfl

theorem profileDensity_smooth {D : RadialDomain} (P : Profiles D) (r : HistoryRow) :
    ContDiffOn ℝ ∞ (profileDensity P r) D.carrier := by
  cases r with
  | mass => exact P.U_smooth
  | angular => exact P.H_smooth
  | transport => exact P.transportDensity_smooth
  | energy => exact P.energyDensity_smooth
  | pressure => exact P.f_smooth.pow 2

theorem profileHistory_smooth {D : RadialDomain} (P : Profiles D) (r : HistoryRow) :
    ContDiffOn ℝ ∞ (profileHistory P r) D.carrier := by
  cases r with
  | mass => exact P.M_smooth
  | angular => exact P.I_smooth
  | transport => exact P.J_smooth
  | energy => exact P.S_smooth
  | pressure => exact P.pressure_smooth

theorem profileHistory_hasDerivAt {D : RadialDomain} (P : Profiles D) (r : HistoryRow)
    {p : Point} (hp : p ∈ D.carrier) :
    HasDerivAt (fun x => profileHistory P r (x, p.2)) (profileDensity P r p) p.1 := by
  have hi := (hasDerivAt_const p.1 (profileInitial P r p.2)).add
    (primitive_hasDerivAt D (profileDensity_smooth P r) hp)
  simp only [zero_add] at hi
  convert! hi using 1
  funext x
  exact profileHistory_eq_initial_add_primitive P r (x, p.2)

/-- Log pullback, defined pointwise by `F (radius X0 p.1, p.2)`. -/
noncomputable def logPullback (X0 : ℝ) (F : Field) : Field :=
  fun p => F (radius X0 p.1, p.2)

theorem radius_hasDerivAt (X0 y : ℝ) : HasDerivAt (radius X0) (radius X0 y) y :=
  (Real.hasDerivAt_exp y).const_mul X0

/-- The change to log radius is proved by differentiating the actual physical
history. This includes the pressure constant and all four moment histories. -/
theorem profileHistory_log_integral {D : RadialDomain} (P : Profiles D)
    (X0 : ℝ) (r : HistoryRow) (y η : ℝ)
    (hmem : ∀ t : ℝ, (radius X0 t, η) ∈ D.carrier) :
    logHistory X0 (fun s ξ => profileHistory P s (X0, ξ))
      (logPullback X0 P.f) (logPullback X0 P.U) r (y, η) =
        profileHistory P r (radius X0 y, η) := by
  have hd : ∀ t : ℝ, HasDerivAt (fun x => profileHistory P r (radius X0 x, η))
      (radius X0 t * profileDensity P r (radius X0 t, η)) t := by
    intro t
    convert! (profileHistory_hasDerivAt P r (hmem t)).comp t (radius_hasDerivAt X0 t) using 1
    ring
  have hc : Continuous (fun t => radius X0 t * profileDensity P r (radius X0 t, η)) := by
    apply (radius_smooth X0).continuous.mul
    apply continuous_iff_continuousAt.mpr
    intro t
    exact ((profileDensity_smooth P r).continuousOn.continuousAt
      (D.isOpen.mem_nhds (hmem t))).comp (f := fun t : ℝ => (radius X0 t, η))
        ((radius_smooth X0).continuous.continuousAt.prodMk continuousAt_const)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun x => profileHistory P r (radius X0 x, η))
    (fun t _ => hd t) (hc.intervalIntegrable 0 y)
  change profileHistory P r (X0, η) +
    (∫ t in (0 : ℝ)..y, radius X0 t * profileDensity P r (radius X0 t, η)) = _
  rw [hi]
  simp only [radius, Real.exp_zero, mul_one]
  ring

theorem profileHistory_congr_up_to {D : RadialDomain} (P Q : Profiles D)
    (r : HistoryRow) {X η : ℝ} (hX : 0 ≤ X)
    (h0 : profileInitial P r η = profileInitial Q r η)
    (hf : ∀ x ∈ Icc (0 : ℝ) X, P.f (x, η) = Q.f (x, η))
    (hu : ∀ x ∈ Icc (0 : ℝ) X, P.U (x, η) = Q.U (x, η)) :
    profileHistory P r (X, η) = profileHistory Q r (X, η) := by
  rw [profileHistory_eq_initial_add_primitive, profileHistory_eq_initial_add_primitive]
  dsimp only
  rw [h0]
  congr 1
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le hX] at hx
  dsimp only [profileDensity]
  rw [hf x hx, hu x hx]

theorem logHistory_congr_slice (X0 : ℝ) (initial₁ initial₂ : HistoryRow → ℝ → ℝ)
    (f₁ U₁ f₂ U₂ : Field) (r : HistoryRow) (y η : ℝ)
    (hi : initial₁ r η = initial₂ r η)
    (hf : ∀ t : ℝ, f₁ (t, η) = f₂ (t, η))
    (hu : ∀ t : ℝ, U₁ (t, η) = U₂ (t, η)) :
    logHistory X0 initial₁ f₁ U₁ r (y, η) = logHistory X0 initial₂ f₂ U₂ r (y, η) := by
  dsimp only [logHistory]
  rw [hi]
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only [logDensity]
  rw [hf t, hu t]

/-! ## Attaching the actual ramp to the proved natural reference path -/

namespace FromReference

open ReferencePath

variable (N : ReferencePath.Input)

/-- Ref log, given by `ReferencePath.continuation δ N.logF`. -/
noncomputable def refLog (δ : ℝ) : Field := ReferencePath.continuation δ N.logF
/-- Ref axial, given by `ReferencePath.continuation δ N.logU`. -/
noncomputable def refAxial (δ : ℝ) : Field := ReferencePath.continuation δ N.logU

theorem refLog_smooth {δ : ℝ} (hδ : 0 < δ) (hδT : 2 * δ < rampLimit) :
    ContDiffOn ℝ ∞ (refLog N δ) (logDomain parameterInterval parameterInterval_open).carrier :=
  ReferencePath.continuation_smooth rampLimit_pos hδ hδT parameterInterval_open N.logF_smooth

theorem refAxial_smooth {δ : ℝ} (hδ : 0 < δ) (hδT : 2 * δ < rampLimit) :
    ContDiffOn ℝ ∞ (refAxial N δ) (logDomain parameterInterval parameterInterval_open).carrier :=
  ReferencePath.continuation_smooth rampLimit_pos hδ hδT parameterInterval_open N.logU_smooth

/-- F, defined pointwise by `if p.1 ≤ N.endpoint then N.refF δ p else activatedAngular T κ
(refLog N δ) (N.logTime p.1, p.2)`. -/
noncomputable def f (T κ δ : ℝ) : Field := fun p =>
  if p.1 ≤ N.endpoint then N.refF δ p else
    activatedAngular T κ (refLog N δ) (N.logTime p.1, p.2)

/-- U, defined pointwise by `if p.1 ≤ N.endpoint then N.refU δ p else controlled T κ (refAxial N
δ) (N.logTime p.1, p.2)`. -/
noncomputable def U (T κ δ : ℝ) : Field := fun p =>
  if p.1 ≤ N.endpoint then N.refU δ p else
    controlled T κ (refAxial N δ) (N.logTime p.1, p.2)

theorem f_eq_reference (T κ δ : ℝ) {p : Point} (hp : p.1 ≤ N.endpoint) :
    f N T κ δ p = N.refF δ p := ite_eq_left hp

theorem U_eq_reference (T κ δ : ℝ) {p : Point} (hp : p.1 ≤ N.endpoint) :
    U N T κ δ p = N.refU δ p := ite_eq_left hp

theorem f_eq_logtime {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2 * δ < rampLimit) (κ : ℝ) {p : Point}
    (hη : p.2 ∈ parameterInterval) (hX : 0 < p.1) :
    f N T κ δ p = activatedAngular T κ (refLog N δ) (N.logTime p.1, p.2) := by
  by_cases hp : p.1 ≤ N.endpoint
  · have ht : N.logTime p.1 ≤ 0 := (N.logTime_le_iff hX).2
      (by simpa only [Real.exp_zero, mul_one] using hp)
    rw [f_eq_reference N T κ δ hp, activatedAngular,
      controlled_eq_reference_before hT κ parameterInterval_open (refLog_smooth N hδ hδT) ht hη]
    exact N.refF_eq_logtime hδ hδT hη hX
  · exact ite_eq_right hp

theorem U_eq_logtime {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2 * δ < rampLimit) (κ : ℝ) {p : Point}
    (hη : p.2 ∈ parameterInterval) (hX : 0 < p.1) :
    U N T κ δ p = controlled T κ (refAxial N δ) (N.logTime p.1, p.2) := by
  by_cases hp : p.1 ≤ N.endpoint
  · have ht : N.logTime p.1 ≤ 0 := (N.logTime_le_iff hX).2
      (by simpa only [Real.exp_zero, mul_one] using hp)
    rw [U_eq_reference N T κ δ hp,
      controlled_eq_reference_before hT κ parameterInterval_open (refAxial_smooth N hδ hδT) ht hη]
    exact N.refU_eq_logtime hδ hδT hη hX
  · exact ite_eq_right hp

theorem f_smooth {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2 * δ < rampLimit) (κ : ℝ) :
    ContDiffOn ℝ ∞ (f N T κ δ) N.radialDomain.carrier := by
  intro p hp
  by_cases hX : 0 < p.1
  · have hs := ((activatedAngular_smooth T κ parameterInterval_open (refLog_smooth N hδ
      hδT)).contDiffAt
      ((logDomain parameterInterval parameterInterval_open).isOpen.mem_nhds
        (show (N.logTime p.1, p.2) ∈ (logDomain parameterInterval parameterInterval_open).carrier
            from
          ⟨mem_univ _, hp.2⟩))).comp p (N.logtime_smoothAt hX)
    have heq : f N T κ δ =ᶠ[𝓝 p]
        (fun q => activatedAngular T κ (refLog N δ) (N.logTime q.1, q.2)) := by
      filter_upwards [continuousAt_fst.eventually (Ioi_mem_nhds hX),
        continuousAt_snd.eventually (parameterInterval_open.mem_nhds hp.2)] with q hqX hqη
      exact f_eq_logtime N hT hδ hδT κ hqη hqX
    exact (hs.congr_of_eventuallyEq heq).contDiffWithinAt
  · have hbefore : p.1 < N.endpoint := (le_of_not_gt hX).trans_lt N.endpoint_pos
    have hs := (N.refF_smooth hδ hδT).contDiffAt (N.radialDomain.isOpen.mem_nhds hp)
    have heq : f N T κ δ =ᶠ[𝓝 p] N.refF δ := by
      filter_upwards [continuousAt_fst.eventually (Iio_mem_nhds hbefore)] with q hq
      exact f_eq_reference N T κ δ hq.le
    exact (hs.congr_of_eventuallyEq heq).contDiffWithinAt

theorem U_smooth {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2 * δ < rampLimit) (κ : ℝ) :
    ContDiffOn ℝ ∞ (U N T κ δ) N.radialDomain.carrier := by
  intro p hp
  by_cases hX : 0 < p.1
  · have hs := ((controlled_smooth T κ parameterInterval_open (refAxial_smooth N hδ hδT)).contDiffAt
      ((logDomain parameterInterval parameterInterval_open).isOpen.mem_nhds
        (show (N.logTime p.1, p.2) ∈ (logDomain parameterInterval parameterInterval_open).carrier
            from
          ⟨mem_univ _, hp.2⟩))).comp p (N.logtime_smoothAt hX)
    have heq : U N T κ δ =ᶠ[𝓝 p]
        (fun q => controlled T κ (refAxial N δ) (N.logTime q.1, q.2)) := by
      filter_upwards [continuousAt_fst.eventually (Ioi_mem_nhds hX),
        continuousAt_snd.eventually (parameterInterval_open.mem_nhds hp.2)] with q hqX hqη
      exact U_eq_logtime N hT hδ hδT κ hqη hqX
    exact (hs.congr_of_eventuallyEq heq).contDiffWithinAt
  · have hbefore : p.1 < N.endpoint := (le_of_not_gt hX).trans_lt N.endpoint_pos
    have hs := (N.refU_smooth hδ hδT).contDiffAt (N.radialDomain.isOpen.mem_nhds hp)
    have heq : U N T κ δ =ᶠ[𝓝 p] N.refU δ := by
      filter_upwards [continuousAt_fst.eventually (Iio_mem_nhds hbefore)] with q hq
      exact U_eq_reference N T κ δ hq.le
    exact (hs.congr_of_eventuallyEq heq).contDiffWithinAt

theorem f_pos (T κ δ : ℝ) {p : Point} (hp : p ∈ N.radialDomain.carrier) (hX : 0 ≤ p.1) :
    0 < f N T κ δ p := by
  by_cases hx : p.1 ≤ N.endpoint
  · rw [f_eq_reference N T κ δ hx]
    exact N.refF_pos δ hp hX
  · rw [f, ite_eq_right hx]
    exact activatedAngular_pos T κ _ _

/-- These are the actual radial pressure and lag inputs, recomputed from ACT. -/
noncomputable def histories {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2 * δ < rampLimit) (κ : ℝ) (P0 : ℝ → ℝ) (hP0 : ContDiff ℝ ∞ P0) :
    Profiles N.radialDomain where
  f := f N T κ δ
  U := U N T κ δ
  f_smooth := f_smooth N hT hδ hδT κ
  U_smooth := U_smooth N hT hδ hδT κ
  pressure0 := P0
  pressure0_smooth := fun _ _ => hP0.contDiffAt

theorem histories_initial {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2 * δ < rampLimit) (κ : ℝ) (P0 : ℝ → ℝ) (hP0 : ContDiff ℝ ∞ P0)
    (r : HistoryRow) (η : ℝ) :
    profileHistory (histories N hT hδ hδT κ P0 hP0) r (N.endpoint, η) =
      profileHistory (N.histories hδ hδT P0 hP0) r (N.endpoint, η) := by
  apply profileHistory_congr_up_to _ _ r N.endpoint_pos.le
  · cases r <;> rfl
  · intro x hx
    exact f_eq_reference N T κ δ hx.2
  · intro x hx
    exact U_eq_reference N T κ δ hx.2

theorem log_radius_mem (y : ℝ) {η : ℝ} (hη : η ∈ parameterInterval) :
    (radius N.endpoint y, η) ∈ N.radialDomain.carrier := by
  refine ⟨?_, hη⟩
  have hx : 0 < N.scale * radius N.endpoint y :=
    mul_pos N.scale_pos (mul_pos N.endpoint_pos (Real.exp_pos y))
  linarith

theorem f_logPullback {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2 * δ < rampLimit) (κ y : ℝ) {η : ℝ} (hη : η ∈ parameterInterval) :
    logPullback N.endpoint (f N T κ δ) (y, η) =
      activatedAngular T κ (refLog N δ) (y, η) := by
  unfold logPullback
  rw [f_eq_logtime N hT hδ hδT κ hη (mul_pos N.endpoint_pos (Real.exp_pos y))]
  simp only [radius, N.logTime_fromLog]

theorem U_logPullback {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2 * δ < rampLimit) (κ y : ℝ) {η : ℝ} (hη : η ∈ parameterInterval) :
    logPullback N.endpoint (U N T κ δ) (y, η) =
      controlled T κ (refAxial N δ) (y, η) := by
  unfold logPullback
  rw [U_eq_logtime N hT hδ hδT κ hη (mul_pos N.endpoint_pos (Real.exp_pos y))]
  simp only [radius, N.logTime_fromLog]

theorem refF_logPullback {δ : ℝ} (hδ : 0 < δ) (hδT : 2 * δ < rampLimit)
    (y : ℝ) {η : ℝ} (hη : η ∈ parameterInterval) :
    logPullback N.endpoint (N.refF δ) (y, η) = referenceAngular (refLog N δ) (y, η) := by
  unfold logPullback
  rw [N.refF_eq_logtime hδ hδT hη (mul_pos N.endpoint_pos (Real.exp_pos y))]
  simp only [radius, N.logTime_fromLog]
  rfl

theorem refU_logPullback {δ : ℝ} (hδ : 0 < δ) (hδT : 2 * δ < rampLimit)
    (y : ℝ) {η : ℝ} (hη : η ∈ parameterInterval) :
    logPullback N.endpoint (N.refU δ) (y, η) = refAxial N δ (y, η) := by
  unfold logPullback
  rw [N.refU_eq_logtime hδ hδT hη (mul_pos N.endpoint_pos (Real.exp_pos y))]
  simp only [radius, N.logTime_fromLog]
  rfl

theorem histories_log_formula {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2 * δ < rampLimit) (κ : ℝ) (P0 : ℝ → ℝ) (hP0 : ContDiff ℝ ∞ P0)
    (r : HistoryRow) (y : ℝ) {η : ℝ} (hη : η ∈ parameterInterval) :
    profileHistory (histories N hT hδ hδT κ P0 hP0) r (radius N.endpoint y, η) =
      logHistory N.endpoint
        (fun s ξ => profileHistory (N.histories hδ hδT P0 hP0) s (N.endpoint, ξ))
        (activatedAngular T κ (refLog N δ)) (controlled T κ (refAxial N δ)) r (y, η) := by
  rw [← profileHistory_log_integral (histories N hT hδ hδT κ P0 hP0) N.endpoint r y η
    (fun t => log_radius_mem N t hη)]
  apply logHistory_congr_slice
  · exact histories_initial N hT hδ hδT κ P0 hP0 r η
  · intro t
    exact f_logPullback N hT hδ hδT κ t hη
  · intro t
    exact U_logPullback N hT hδ hδT κ t hη

theorem reference_histories_log_formula {δ : ℝ} (hδ : 0 < δ) (hδT : 2 * δ < rampLimit)
    (P0 : ℝ → ℝ) (hP0 : ContDiff ℝ ∞ P0) (r : HistoryRow) (y : ℝ)
    {η : ℝ} (hη : η ∈ parameterInterval) :
    profileHistory (N.histories hδ hδT P0 hP0) r (radius N.endpoint y, η) =
      logHistory N.endpoint
        (fun s ξ => profileHistory (N.histories hδ hδT P0 hP0) s (N.endpoint, ξ))
        (referenceAngular (refLog N δ)) (refAxial N δ) r (y, η) := by
  rw [← profileHistory_log_integral (N.histories hδ hδT P0 hP0) N.endpoint r y η
    (fun t => log_radius_mem N t hη)]
  apply logHistory_congr_slice
  · rfl
  · intro t
    exact refF_logPullback N hδ hδT t hη
  · intro t
    exact refU_logPullback N hδ hδT t hη

/-- The five *physical* histories inherit the constructed smooth factor. -/
theorem histories_difference_factorization {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2 * δ < rampLimit) (κ : ℝ) (P0 : ℝ → ℝ) (hP0 : ContDiff ℝ ∞ P0)
    (r : HistoryRow) (y : ℝ) {η : ℝ} (hη : η ∈ parameterInterval) :
    profileHistory (histories N hT hδ hδT κ P0 hP0) r (radius N.endpoint y, η) -
      profileHistory (N.histories hδ hδT P0 hP0) r (radius N.endpoint y, η) =
        y * activation T κ y *
          historyDifferenceFamily T N.endpoint (refLog N δ) (refAxial N δ) r ((κ, y), η) := by
  rw [histories_log_formula N hT hδ hδT κ P0 hP0 r y hη,
    reference_histories_log_formula N hδ hδT P0 hP0 r y hη]
  exact history_difference_factorization hT κ N.endpoint _ parameterInterval_open
    (refLog_smooth N hδ hδT) (refAxial_smooth N hδ hδT) r y hη

theorem histories_parameter_jet_bounds {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2 * δ < rampLimit) (P0 : ℝ → ℝ) (hP0 : ContDiff ℝ ∞ P0)
    {K : Set ℝ} (hK : IsCompact K) (hKJ : K ⊆ parameterInterval) (r : HistoryRow) (n : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ κ ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) T, ∀ η ∈ K,
      |iteratedDeriv n (fun ξ =>
        profileHistory (histories N hT hδ hδT κ P0 hP0) r (radius N.endpoint y, ξ) -
          profileHistory (N.histories hδ hδT P0 hP0) r (radius N.endpoint y, ξ)) η| ≤
            M * y * activation T κ y := by
  apply scaled_family_jet_bound hT parameterInterval_open hK hKJ
    (historyDifferenceFamily_smooth hT N.endpoint parameterInterval_open
      (refLog_smooth N hδ hδT) (refAxial_smooth N hδ hδT) r)
  intro κ y η hη
  exact histories_difference_factorization N hT hδ hδT κ P0 hP0 r y hη

theorem angular_equation {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2 * δ < rampLimit) (κ y : ℝ) {η : ℝ} (hη : η ∈ parameterInterval) :
    HasDerivAt (fun t => Real.log (f N T κ δ (radius N.endpoint t, η)))
      (-(damping T κ y * referenceP1 (refLog N δ) (y, η)) / 2) y := by
  convert! activation_angular_equation T κ parameterInterval_open (refLog_smooth N hδ hδT) y hη
      using 1
  funext t
  exact congrArg Real.log (f_logPullback N hT hδ hδT κ t hη)

theorem axial_equation {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2 * δ < rampLimit) (κ y : ℝ) {η : ℝ} (hη : η ∈ parameterInterval) :
    HasDerivAt (fun t => U N T κ δ (radius N.endpoint t, η))
      (-(damping T κ y * radius N.endpoint y * referenceNs N.endpoint (refAxial N δ) (y, η)) / 2) y
          := by
  convert! activation_axial_equation T κ N.endpoint_pos parameterInterval_open
    (refAxial_smooth N hδ hδT) y hη using 1
  funext t
  exact U_logPullback N hT hδ hδT κ t hη

end FromReference

/-! ## Exact shear identities and cancellation of the common damping -/

/-- Actual P1, given by `-2 * deriv (fun y => Real.log (activatedAngular T κ L (y, p.2))) p.1`. -/
noncomputable def actualP1 (T κ : ℝ) (L : Field) (p : Point) : ℝ :=
  -2 * deriv (fun y => Real.log (activatedAngular T κ L (y, p.2))) p.1

/-- Velocity, given by `Real.sqrt (2 * radius X0 p.1) * f p`. -/
noncomputable def velocity (X0 : ℝ) (f : Field) (p : Point) : ℝ :=
  Real.sqrt (2 * radius X0 p.1) * f p

/-- Reference P2, given by `-2 * radialPartial U p / velocity X0 (referenceAngular L) p`. -/
noncomputable def referenceP2 (X0 : ℝ) (L U : Field) (p : Point) : ℝ :=
  -2 * radialPartial U p / velocity X0 (referenceAngular L) p

/-- Actual P2, given by `-2 * deriv (fun y => controlled T κ U (y, p.2)) p.1 / velocity X0
(activatedAngular T κ L) p`. -/
noncomputable def actualP2 (T κ X0 : ℝ) (L U : Field) (p : Point) : ℝ :=
  -2 * deriv (fun y => controlled T κ U (y, p.2)) p.1 /
    velocity X0 (activatedAngular T κ L) p

/-- Shear slope, given by `actualP2 T κ X0 L U p / actualP1 T κ L p`. -/
noncomputable def shearSlope (T κ X0 : ℝ) (L U : Field) (p : Point) : ℝ :=
  actualP2 T κ X0 L U p / actualP1 T κ L p

/-- Shear size, given by `actualP1 T κ L p + actualP2 T κ X0 L U p ^ 2 / actualP1 T κ L p`. -/
noncomputable def shearSize (T κ X0 : ℝ) (L U : Field) (p : Point) : ℝ :=
  actualP1 T κ L p + actualP2 T κ X0 L U p ^ 2 / actualP1 T κ L p

/-- Reference size, given by `referenceP1 L p + referenceP2 X0 L U p ^ 2 / referenceP1 L p`. -/
noncomputable def referenceSize (X0 : ℝ) (L U : Field) (p : Point) : ℝ :=
  referenceP1 L p + referenceP2 X0 L U p ^ 2 / referenceP1 L p

theorem damping_ge (T κ y : ℝ) (hκ : κ ≤ 1) : κ ≤ damping T κ y := by
  have hs := mul_le_mul_of_nonneg_left (OutgoingSchedule.sigma_le_one (y / T))
    (sub_nonneg.mpr hκ)
  dsimp only [damping, activation]
  nlinarith

theorem damping_pos (T κ y : ℝ) (hκ : κ ∈ Ioc (0 : ℝ) 1) : 0 < damping T κ y :=
  hκ.1.trans_le (damping_ge T κ y hκ.2)

theorem actualP1_eq (T κ : ℝ) {J : Set ℝ} (hJ : IsOpen J) {L : Field}
    (hL : ContDiffOn ℝ ∞ L (logDomain J hJ).carrier) (y : ℝ) {η : ℝ} (hη : η ∈ J) :
    actualP1 T κ L (y, η) = damping T κ y * referenceP1 L (y, η) := by
  unfold actualP1
  rw [(activation_angular_equation T κ hJ hL y hη).deriv]
  ring

theorem actualP1_pos (T : ℝ) {κ : ℝ} (hκ : κ ∈ Ioc (0 : ℝ) 1)
    {J : Set ℝ} (hJ : IsOpen J) {L : Field}
    (hL : ContDiffOn ℝ ∞ L (logDomain J hJ).carrier) (y : ℝ) {η : ℝ} (hη : η ∈ J)
    (hp : 0 < referenceP1 L (y, η)) : 0 < actualP1 T κ L (y, η) := by
  rw [actualP1_eq T κ hJ hL y hη]
  exact mul_pos (damping_pos T κ y hκ) hp

theorem actualP2_eq (T κ : ℝ) {X0 : ℝ} (hX0 : 0 < X0)
    {J : Set ℝ} (hJ : IsOpen J) {L U : Field}
    (hU : ContDiffOn ℝ ∞ U (logDomain J hJ).carrier) (y : ℝ) {η : ℝ} (hη : η ∈ J) :
    actualP2 T κ X0 L U (y, η) = damping T κ y * referenceP2 X0 L U (y, η) *
      (referenceAngular L (y, η) / activatedAngular T κ L (y, η)) := by
  have hs : Real.sqrt (2 * radius X0 y) ≠ 0 :=
    (Real.sqrt_pos.2 (mul_pos (by norm_num) (mul_pos hX0 (Real.exp_pos y)))).ne'
  have hr : referenceAngular L (y, η) ≠ 0 := (Real.exp_pos _).ne'
  have ha : activatedAngular T κ L (y, η) ≠ 0 := (activatedAngular_pos T κ L _).ne'
  unfold actualP2
  rw [(controlled_hasDerivAt T κ hJ hU y hη).deriv]
  dsimp only [referenceP2, velocity]
  field_simp [hs, hr, ha]

/-- The reference shear ratio contains no inverse power of the damping. -/
theorem shearSlope_eq (T : ℝ) {κ X0 : ℝ} (hκ : κ ∈ Ioc (0 : ℝ) 1) (hX0 : 0 < X0)
    {J : Set ℝ} (hJ : IsOpen J) {L U : Field}
    (hL : ContDiffOn ℝ ∞ L (logDomain J hJ).carrier)
    (hU : ContDiffOn ℝ ∞ U (logDomain J hJ).carrier) (y : ℝ) {η : ℝ} (hη : η ∈ J)
    (hp : referenceP1 L (y, η) ≠ 0) :
    shearSlope T κ X0 L U (y, η) =
      (referenceP2 X0 L U (y, η) / referenceP1 L (y, η)) *
        (referenceAngular L (y, η) / activatedAngular T κ L (y, η)) := by
  have hd := (damping_pos T κ y hκ).ne'
  have ha := (activatedAngular_pos T κ L (y, η)).ne'
  unfold shearSlope
  rw [actualP1_eq T κ hJ hL y hη, actualP2_eq T κ hX0 hJ hU y hη]
  field_simp [hd, hp, ha]

theorem shearSize_error (T : ℝ) {κ X0 : ℝ} (hκ : κ ∈ Ioc (0 : ℝ) 1) (hX0 : 0 < X0)
    {J : Set ℝ} (hJ : IsOpen J) {L U : Field}
    (hL : ContDiffOn ℝ ∞ L (logDomain J hJ).carrier)
    (hU : ContDiffOn ℝ ∞ U (logDomain J hJ).carrier) (y : ℝ) {η : ℝ} (hη : η ∈ J)
    (hp : referenceP1 L (y, η) ≠ 0) :
    shearSize T κ X0 L U (y, η) - damping T κ y * referenceSize X0 L U (y, η) =
      damping T κ y * (referenceP2 X0 L U (y, η) ^ 2 / referenceP1 L (y, η)) *
        ((referenceAngular L (y, η) / activatedAngular T κ L (y, η)) ^ 2 - 1) := by
  have hd := (damping_pos T κ y hκ).ne'
  have ha := (activatedAngular_pos T κ L (y, η)).ne'
  unfold shearSize referenceSize
  rw [actualP1_eq T κ hJ hL y hη, actualP2_eq T κ hX0 hJ hU y hη]
  field_simp; ring

theorem controlled_bound {T κ M y : ℝ} (hT : 0 < T) (hκ : κ ≤ 1)
    (hM : 0 ≤ M) (hy : 0 ≤ y) {J : Set ℝ} (hJ : IsOpen J) {F : Field}
    (hF : ContDiffOn ℝ ∞ F (logDomain J hJ).carrier) {η : ℝ} (hη : η ∈ J)
    (hB : ∀ t ∈ Icc (0 : ℝ) y, |radialPartial F (t, η)| ≤ M) :
    |controlled T κ F (y, η) - F (y, η)| ≤ M * y * activation T κ y := by
  rw [controlled_sub T κ hJ hF y hη, abs_neg]
  exact weightedPrimitive_bound hT hκ hM hy (radialPartial F) η hB

end NavierStokes.StressActivation
