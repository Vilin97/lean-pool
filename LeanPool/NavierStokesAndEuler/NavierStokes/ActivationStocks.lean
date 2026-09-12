/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.NavierStokes.NaturalEntrance
public import LeanPool.NavierStokesAndEuler.NavierStokes.StressActivation
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Actual lag stocks during the activation ramp

The stock formulas are obtained from the genuine five profile histories.
Smooth difference factors are constructed from the field and history factors;
no estimate for a stock difference is supplied as an assumption.
-/

section

/-!
# Bounds for a shrinking activation ramp

The clock `u = y / T` keeps the cutoff fixed while the width tends to zero.
All error factors below are actual transformed integrals and are smooth at
`T = 0`. Compactness therefore gives width-uniform parameter-jet estimates.
-/

@[expose] public section

noncomputable section

namespace NavierStokes.ActivationBounds

open Set Filter MeasureTheory Metric ProfileHistories StressActivation
open scoped Topology ContDiff

section ParameterFactor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Parameter coefficient, given by `B (q.1.1, (q.2, q.1.2)) / stepDenominator 1 q.2`. -/
noncomputable def parameterCoefficient (B : E × Point → ℝ) (q : (E × ℝ) × ℝ) : ℝ :=
  B (q.1.1, (q.2, q.1.2)) / stepDenominator 1 q.2

/-- Parameter factor, given by `q.2.1 ^ 2 * stepDenominator 1 q.2.1 *
ParametricFlatFactor.factor 1 0 (parameterCoefficient B) ((q.1, q.2.2), q.2.1)`. -/
noncomputable def parameterFactor (B : E × Point → ℝ) (q : E × Point) : ℝ :=
  q.2.1 ^ 2 * stepDenominator 1 q.2.1 *
    ParametricFlatFactor.factor 1 0 (parameterCoefficient B) ((q.1, q.2.2), q.2.1)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
theorem parameterFactor_eq (B : E × Point → ℝ) (q : E) (p : Point) :
    parameterFactor B (q, p) = primitiveFactor 1 (fun z => B (q, z)) p := by
  simp only [parameterFactor, primitiveFactor, one_pow]
  rfl

theorem parameterFactor_smooth {S : Set E} (hS : IsOpen S) {J : Set ℝ} (hJ : IsOpen J)
    {B : E × Point → ℝ} (hB : ContDiffOn ℝ ∞ B (S ×ˢ (univ ×ˢ J))) :
    ContDiffOn ℝ ∞ (parameterFactor B) (S ×ˢ (univ ×ˢ J)) := by
  have hb : ContDiffOn ℝ ∞ (parameterCoefficient B) ((S ×ˢ J) ×ˢ (univ : Set ℝ)) :=
    (hB.comp (contDiff_fst.fst.prodMk (contDiff_snd.prodMk contDiff_fst.snd)).contDiffOn
      (fun _ hp => ⟨hp.1.1, mem_univ _, hp.1.2⟩)).div
        ((stepDenominator_smooth 1).comp contDiff_snd).contDiffOn
        (fun q _ => (stepDenominator_pos 1 q.2).ne')
  have hf := flatFactor_local (by norm_num : (0 : ℝ) < 1) 0 (hS.prod hJ) hb
  exact ((contDiff_snd.fst.pow 2).mul
    ((stepDenominator_smooth 1).comp contDiff_snd.fst)).contDiffOn.mul
      (hf.comp ((contDiff_fst.prodMk contDiff_snd.snd).prodMk contDiff_snd.fst).contDiffOn
        (fun _ hp => ⟨⟨hp.1, hp.2.2⟩, mem_univ _⟩))

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
@[simp] theorem parameterFactor_zero (B : E × Point → ℝ) (q : E) (η : ℝ) :
    parameterFactor B (q, (0, η)) = 0 := by simp [parameterFactor]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
theorem parameterFactor_identity (B : E × Point → ℝ) (q : E) (κ : ℝ) (p : Point) :
    weightedPrimitive 1 κ (fun z => B (q, z)) p =
      p.1 * activation 1 κ p.1 * parameterFactor B (q, p) := by
  rw [parameterFactor_eq]
  exact weightedPrimitive_factorization (by norm_num) κ _ p

omit [FiniteDimensional ℝ E] in
/-- A compact family bounds genuine parameter derivatives, with no restriction
on the number of auxiliary parameters. -/
theorem compact_parameter_jet_bound {S Q : Set E} (hS : IsOpen S) (hQ : IsCompact Q)
    (hQS : Q ⊆ S) {J K : Set ℝ} (hJ : IsOpen J) (hK : IsCompact K) (hKJ : K ⊆ J)
    {H : E × Point → ℝ} (hH : ContDiffOn ℝ ∞ H (S ×ˢ (univ ×ˢ J))) (n : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ q ∈ Q, ∀ u ∈ Icc (0 : ℝ) 1, ∀ η ∈ K,
      |iteratedDeriv n (fun ξ => H (q, (u, ξ))) η| ≤ M := by
  have hc : ContinuousOn
      (fun z : E × Point => iteratedFDeriv ℝ n (fun ξ => H (z.1, (z.2.1, ξ))) z.2.2)
      (S ×ˢ (univ ×ˢ J)) := by
    intro z hz
    have hp : ContDiffAt ℝ ∞ (fun w : (E × ℝ) × ℝ => H (w.1.1, (w.1.2, w.2)))
        ((z.1, z.2.1), z.2.2) :=
      (hH.contDiffAt ((hS.prod (isOpen_univ.prod hJ)).mem_nhds hz)).comp _
        (contDiffAt_fst.fst.prodMk (contDiffAt_fst.snd.prodMk contDiffAt_snd))
    have hd := ParametricFlatFactor.contDiffAt_partial_iteratedFDeriv
      (fun (v : E × ℝ) ξ => H (v.1, (v.2, ξ))) n (z.1, z.2.1) z.2.2 hp
    exact ((hd.comp z ((contDiffAt_fst.prodMk contDiffAt_snd.fst).prodMk
      contDiffAt_snd.snd)).continuousAt).continuousWithinAt
  obtain ⟨M, hM⟩ := (hQ.prod (isCompact_Icc.prod hK)).exists_bound_of_continuousOn
    (hc.mono (fun z hz => ⟨hQS hz.1, mem_univ _, hKJ hz.2.2⟩))
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  intro q hq u hu η hη
  have hb := hM (q, (u, η)) ⟨hq, hu, hη⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] at hb
  exact hb.trans (le_max_left _ _)

end ParameterFactor

/-- Scaled point: an abbreviation for `(ℝ × ℝ) × Point`. -/
abbrev ScaledPoint := (ℝ × ℝ) × Point

/-- Scaled domain, given by `univ ×ˢ (univ ×ˢ J)`. -/
noncomputable def scaledDomain (J : Set ℝ) : Set ScaledPoint := univ ×ˢ (univ ×ˢ J)

theorem scaledDomain_open {J : Set ℝ} (hJ : IsOpen J) : IsOpen (scaledDomain J) :=
  isOpen_univ.prod (isOpen_univ.prod hJ)

/-- The auxiliary parameters are `(κ,T)` and the point is `(u,η)`. -/
noncomputable def rescale (F : Field) (q : ScaledPoint) : ℝ :=
  F (q.1.2 * q.2.1, q.2.2)

theorem rescale_smooth {J : Set ℝ} (hJ : IsOpen J) {F : Field}
    (hF : ContDiffOn ℝ ∞ F (logDomain J hJ).carrier) :
    ContDiffOn ℝ ∞ (rescale F) (scaledDomain J) :=
  hF.comp ((contDiff_fst.snd.mul contDiff_snd.fst).prodMk contDiff_snd.snd).contDiffOn
    (fun _ hp => ⟨mem_univ _, hp.2.2⟩)

/-- Scaled distance, given by `q.1.2 * q.2.1 * activation 1 q.1.1 q.2.1`. -/
noncomputable def scaledDistance (q : ScaledPoint) : ℝ :=
  q.1.2 * q.2.1 * activation 1 q.1.1 q.2.1

theorem scaledDistance_smooth : ContDiff ℝ ∞ scaledDistance := by
  exact (contDiff_fst.snd.mul contDiff_snd.fst).mul
    ((contDiff_const.sub contDiff_fst.fst).mul
      (OutgoingSchedule.sigma_contDiff.comp (contDiff_snd.fst.div_const 1)))

theorem activation_scaled {T : ℝ} (hT : T ≠ 0) (κ u : ℝ) :
    activation T κ (T * u) = activation 1 κ u := by
  simp [activation, mul_div_cancel_left₀ u hT]

theorem primitive_rescaled (T : ℝ) (F : Field) (u η : ℝ) :
    primitive F (T * u, η) = T * primitive (fun p => F (T * p.1, p.2)) (u, η) := by
  have ha : ProfileHistories.average F (T * u, η) =
      ProfileHistories.average (fun p => F (T * p.1, p.2)) (u, η) := by
    unfold ProfileHistories.average
    apply intervalIntegral.integral_congr
    intro v _
    dsimp only
    congr 1
    ring_nf
  rw [primitive_eq_mul_average, primitive_eq_mul_average]
  dsimp only
  rw [ha]
  ring

theorem weightedPrimitive_rescaled {T : ℝ} (hT : T ≠ 0) (κ : ℝ) (B : Field) (u η : ℝ) :
    weightedPrimitive T κ B (T * u, η) =
      T * weightedPrimitive 1 κ (fun p => B (T * p.1, p.2)) (u, η) := by
  unfold weightedPrimitive
  rw [primitive_rescaled]
  congr 1
  congr 1
  funext p
  dsimp only [weightedField]
  rw [activation_scaled hT]

/-- Primitive error factor, given by `parameterFactor (rescale B)`. -/
noncomputable def primitiveErrorFactor (B : Field) : ScaledPoint → ℝ :=
  parameterFactor (rescale B)

theorem primitiveErrorFactor_smooth {J : Set ℝ} (hJ : IsOpen J) {B : Field}
    (hB : ContDiffOn ℝ ∞ B (logDomain J hJ).carrier) :
    ContDiffOn ℝ ∞ (primitiveErrorFactor B) (scaledDomain J) :=
  parameterFactor_smooth isOpen_univ hJ (rescale_smooth hJ hB)

theorem weightedPrimitive_scaled_factor {T : ℝ} (hT : T ≠ 0) (κ : ℝ) (B : Field) (u η : ℝ) :
    weightedPrimitive T κ B (T * u, η) =
      scaledDistance ((κ, T), (u, η)) * primitiveErrorFactor B ((κ, T), (u, η)) := by
  rw [weightedPrimitive_rescaled hT]
  change T * weightedPrimitive 1 κ (fun p => rescale B ((κ, T), p)) (u, η) = _
  rw [parameterFactor_identity]
  dsimp only [scaledDistance, primitiveErrorFactor]
  ring

/-- Controlled error factor, defined pointwise by `-primitiveErrorFactor (radialPartial F) q`. -/
noncomputable def controlledErrorFactor (F : Field) : ScaledPoint → ℝ :=
  fun q => -primitiveErrorFactor (radialPartial F) q

theorem controlledErrorFactor_smooth {J : Set ℝ} (hJ : IsOpen J) {F : Field}
    (hF : ContDiffOn ℝ ∞ F (logDomain J hJ).carrier) :
    ContDiffOn ℝ ∞ (controlledErrorFactor F) (scaledDomain J) :=
  (primitiveErrorFactor_smooth hJ (radialPartial_smooth (logDomain J hJ) hF)).neg

theorem controlled_scaled_factor {T : ℝ} (hT : T ≠ 0) (κ : ℝ)
    {J : Set ℝ} (hJ : IsOpen J) {F : Field}
    (hF : ContDiffOn ℝ ∞ F (logDomain J hJ).carrier) (u : ℝ) {η : ℝ} (hη : η ∈ J) :
    controlled T κ F (T * u, η) - F (T * u, η) =
      scaledDistance ((κ, T), (u, η)) * controlledErrorFactor F ((κ, T), (u, η)) := by
  rw [controlled_sub T κ hJ hF _ hη, weightedPrimitive_scaled_factor hT]
  dsimp only [controlledErrorFactor]
  ring

/-- Controlled value, given by `rescale F q + scaledDistance q * controlledErrorFactor F q`. -/
noncomputable def controlledValue (F : Field) (q : ScaledPoint) : ℝ :=
  rescale F q + scaledDistance q * controlledErrorFactor F q

theorem controlledValue_smooth {J : Set ℝ} (hJ : IsOpen J) {F : Field}
    (hF : ContDiffOn ℝ ∞ F (logDomain J hJ).carrier) :
    ContDiffOn ℝ ∞ (controlledValue F) (scaledDomain J) :=
  (rescale_smooth hJ hF).add (scaledDistance_smooth.contDiffOn.mul (controlledErrorFactor_smooth hJ
      hF))

theorem controlledValue_eq {T : ℝ} (hT : T ≠ 0) (κ : ℝ)
    {J : Set ℝ} (hJ : IsOpen J) {F : Field}
    (hF : ContDiffOn ℝ ∞ F (logDomain J hJ).carrier) (u : ℝ) {η : ℝ} (hη : η ∈ J) :
    controlledValue F ((κ, T), (u, η)) = controlled T κ F (T * u, η) := by
  have h := controlled_scaled_factor hT κ hJ hF u hη
  dsimp only [controlledValue, rescale]
  linarith

/-- Angular value, defined pointwise by `Real.exp (controlledValue L q)`. -/
noncomputable def angularValue (L : Field) : ScaledPoint → ℝ :=
  fun q => Real.exp (controlledValue L q)

/-- Relative error factor, given by `controlledErrorFactor L q * meanExp (scaledDistance q *
controlledErrorFactor L q)`. -/
noncomputable def relativeErrorFactor (L : Field) (q : ScaledPoint) : ℝ :=
  controlledErrorFactor L q * meanExp (scaledDistance q * controlledErrorFactor L q)

theorem relativeErrorFactor_smooth {J : Set ℝ} (hJ : IsOpen J) {L : Field}
    (hL : ContDiffOn ℝ ∞ L (logDomain J hJ).carrier) :
    ContDiffOn ℝ ∞ (relativeErrorFactor L) (scaledDomain J) :=
  (controlledErrorFactor_smooth hJ hL).mul
    (meanExp_smooth.comp_contDiffOn (scaledDistance_smooth.contDiffOn.mul
      (controlledErrorFactor_smooth hJ hL)))

theorem angular_relative_scaled_factor {T : ℝ} (hT : T ≠ 0) (κ : ℝ)
    {J : Set ℝ} (hJ : IsOpen J) {L : Field}
    (hL : ContDiffOn ℝ ∞ L (logDomain J hJ).carrier) (u : ℝ) {η : ℝ} (hη : η ∈ J) :
    activatedAngular T κ L (T * u, η) / referenceAngular L (T * u, η) - 1 =
      scaledDistance ((κ, T), (u, η)) * relativeErrorFactor L ((κ, T), (u, η)) := by
  rw [activatedAngular, referenceAngular, ← Real.exp_sub, controlled_scaled_factor hT κ hJ hL u hη,
    exp_sub_one]
  dsimp only [relativeErrorFactor]
  ring

/-- Angular error factor, given by `Real.exp (rescale L q) * relativeErrorFactor L q`. -/
noncomputable def angularErrorFactor (L : Field) (q : ScaledPoint) : ℝ :=
  Real.exp (rescale L q) * relativeErrorFactor L q

theorem angularErrorFactor_smooth {J : Set ℝ} (hJ : IsOpen J) {L : Field}
    (hL : ContDiffOn ℝ ∞ L (logDomain J hJ).carrier) :
    ContDiffOn ℝ ∞ (angularErrorFactor L) (scaledDomain J) :=
  (rescale_smooth hJ hL).exp.mul (relativeErrorFactor_smooth hJ hL)

theorem angular_scaled_factor {T : ℝ} (hT : T ≠ 0) (κ : ℝ)
    {J : Set ℝ} (hJ : IsOpen J) {L : Field}
    (hL : ContDiffOn ℝ ∞ L (logDomain J hJ).carrier) (u : ℝ) {η : ℝ} (hη : η ∈ J) :
    activatedAngular T κ L (T * u, η) - referenceAngular L (T * u, η) =
      scaledDistance ((κ, T), (u, η)) * angularErrorFactor L ((κ, T), (u, η)) := by
  have hn : referenceAngular L (T * u, η) ≠ 0 := (Real.exp_pos _).ne'
  calc
    _ = referenceAngular L (T * u, η) *
        (activatedAngular T κ L (T * u, η) / referenceAngular L (T * u, η) - 1) := by
      field_simp
    _ = _ := by
      rw [angular_relative_scaled_factor hT κ hJ hL u hη]
      dsimp only [angularErrorFactor, referenceAngular, rescale]
      ring

/-- A smooth fixed-clock factor gives one constant for every positive ramp
width up to `T0`, including widths arbitrarily close to zero. -/
theorem width_uniform_jet_bound {J K : Set ℝ} (hJ : IsOpen J) (hK : IsCompact K)
    (hKJ : K ⊆ J) {H : ScaledPoint → ℝ}
    (hH : ContDiffOn ℝ ∞ H (scaledDomain J))
    {E : ℝ → ℝ → ℝ → ℝ → ℝ}
    (hE : ∀ κ T, 0 < T → ∀ u η, η ∈ J →
      E κ T (T * u) η = scaledDistance ((κ, T), (u, η)) * H ((κ, T), (u, η)))
    (T0 : ℝ) (n : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ T ∈ Ioc (0 : ℝ) T0, ∀ κ ∈ Icc (0 : ℝ) 1,
      ∀ y ∈ Icc (0 : ℝ) T, ∀ η ∈ K,
        |iteratedDeriv n (E κ T y) η| ≤ M * y * activation T κ y := by
  obtain ⟨M, hM, hb⟩ := compact_parameter_jet_bound isOpen_univ
    (isCompact_Icc.prod isCompact_Icc)
    (subset_univ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) T0)) hJ hK hKJ hH n
  refine ⟨M, hM, ?_⟩
  intro T hT κ hκ y hy η hη
  let u := y / T
  have hu : u ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hy.1 hT.1.le, (div_le_one hT.1).2 hy.2⟩
  have hTu : T * u = y := by dsimp only [u]; field_simp [hT.1.ne']
  have hs : scaledDistance ((κ, T), (u, η)) = y * activation T κ y := by
    dsimp only [scaledDistance]
    rw [← activation_scaled hT.1.ne' κ u, hTu]
  have heq : E κ T y =ᶠ[𝓝 η]
      (fun ξ => scaledDistance ((κ, T), (u, η)) * H ((κ, T), (u, ξ))) := by
    filter_upwards [hJ.mem_nhds (hKJ hη)] with ξ hξ
    rw [← hTu]
    exact hE κ T hT.1 u ξ hξ
  rw [heq.iteratedDeriv_eq n]
  have hh : ContDiffAt ℝ ∞ (fun ξ => H ((κ, T), (u, ξ))) η :=
    (hH.contDiffAt ((scaledDomain_open hJ).mem_nhds
      ⟨mem_univ _, mem_univ _, hKJ hη⟩)).comp η
        (contDiffAt_const.prodMk (contDiffAt_const.prodMk contDiffAt_id))
  rw [iteratedDeriv_const_mul (n := n) _ (hh.of_le (WithTop.coe_le_coe.mpr le_top)),
    abs_mul, hs, abs_of_nonneg (mul_nonneg hy.1 (activation_nonneg T κ y hκ.2))]
  have hm := mul_le_mul_of_nonneg_left
    (hb (κ, T) ⟨hκ, hT.1.le, hT.2⟩ u hu η hη)
    (mul_nonneg hy.1 (activation_nonneg T κ y hκ.2))
  nlinarith

theorem weightedPrimitive_uniform_jets {J K : Set ℝ} (hJ : IsOpen J) (hK : IsCompact K)
    (hKJ : K ⊆ J) {B : Field} (hB : ContDiffOn ℝ ∞ B (logDomain J hJ).carrier)
    (T0 : ℝ) (n : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ T ∈ Ioc (0 : ℝ) T0, ∀ κ ∈ Icc (0 : ℝ) 1,
      ∀ y ∈ Icc (0 : ℝ) T, ∀ η ∈ K,
        |iteratedDeriv n (fun ξ => weightedPrimitive T κ B (y, ξ)) η| ≤
          M * y * activation T κ y := by
  apply width_uniform_jet_bound hJ hK hKJ (primitiveErrorFactor_smooth hJ hB)
  intro κ T hT u η _
  exact weightedPrimitive_scaled_factor hT.ne' κ B u η

theorem controlled_uniform_jets {J K : Set ℝ} (hJ : IsOpen J) (hK : IsCompact K)
    (hKJ : K ⊆ J) {F : Field} (hF : ContDiffOn ℝ ∞ F (logDomain J hJ).carrier)
    (T0 : ℝ) (n : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ T ∈ Ioc (0 : ℝ) T0, ∀ κ ∈ Icc (0 : ℝ) 1,
      ∀ y ∈ Icc (0 : ℝ) T, ∀ η ∈ K,
        |iteratedDeriv n (fun ξ => controlled T κ F (y, ξ) - F (y, ξ)) η| ≤
          M * y * activation T κ y := by
  apply width_uniform_jet_bound hJ hK hKJ (controlledErrorFactor_smooth hJ hF)
  intro κ T hT u η hη
  exact controlled_scaled_factor hT.ne' κ hJ hF u hη

theorem angular_relative_uniform_jets {J K : Set ℝ} (hJ : IsOpen J) (hK : IsCompact K)
    (hKJ : K ⊆ J) {L : Field} (hL : ContDiffOn ℝ ∞ L (logDomain J hJ).carrier)
    (T0 : ℝ) (n : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ T ∈ Ioc (0 : ℝ) T0, ∀ κ ∈ Icc (0 : ℝ) 1,
      ∀ y ∈ Icc (0 : ℝ) T, ∀ η ∈ K,
        |iteratedDeriv n (fun ξ =>
          activatedAngular T κ L (y, ξ) / referenceAngular L (y, ξ) - 1) η| ≤
            M * y * activation T κ y := by
  apply width_uniform_jet_bound hJ hK hKJ (relativeErrorFactor_smooth hJ hL)
  intro κ T hT u η hη
  exact angular_relative_scaled_factor hT.ne' κ hJ hL u hη

theorem angular_uniform_jets {J K : Set ℝ} (hJ : IsOpen J) (hK : IsCompact K)
    (hKJ : K ⊆ J) {L : Field} (hL : ContDiffOn ℝ ∞ L (logDomain J hJ).carrier)
    (T0 : ℝ) (n : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ T ∈ Ioc (0 : ℝ) T0, ∀ κ ∈ Icc (0 : ℝ) 1,
      ∀ y ∈ Icc (0 : ℝ) T, ∀ η ∈ K,
        |iteratedDeriv n (fun ξ =>
          activatedAngular T κ L (y, ξ) - referenceAngular L (y, ξ)) η| ≤
            M * y * activation T κ y := by
  apply width_uniform_jet_bound hJ hK hKJ (angularErrorFactor_smooth hJ hL)
  intro κ T hT u η hη
  exact angular_scaled_factor hT.ne' κ hJ hL u hη

/-! ## Width-uniform factors for the actual five histories -/

/-- Density error factor as an element of `ℝ`. -/
noncomputable def densityErrorFactor (X0 : ℝ) (L U : Field)
    (r : HistoryRow) (q : ScaledPoint) : ℝ :=
  let x := radius X0 (q.1.2 * q.2.1)
  let df := angularErrorFactor L q
  let du := controlledErrorFactor U q
  let fa := angularValue L q
  let fr := Real.exp (rescale L q)
  let ua := controlledValue U q
  let ur := rescale U q
  match r with
  | .mass => x * du
  | .angular => 2 * x ^ 2 * df
  | .transport => 2 * x ^ 2 * (df * ua + fr * du)
  | .energy => x * (du * (ua + ur) - x * df * (fa + fr))
  | .pressure => x * df * (fa + fr)

theorem densityErrorFactor_smooth (X0 : ℝ) {J : Set ℝ} (hJ : IsOpen J) {L U : Field}
    (hL : ContDiffOn ℝ ∞ L (logDomain J hJ).carrier)
    (hU : ContDiffOn ℝ ∞ U (logDomain J hJ).carrier) (r : HistoryRow) :
    ContDiffOn ℝ ∞ (densityErrorFactor X0 L U r) (scaledDomain J) := by
  have hx := ((radius_smooth X0).comp (contDiff_fst.snd.mul contDiff_snd.fst)).contDiffOn
    (s := scaledDomain J)
  have hdf := angularErrorFactor_smooth hJ hL
  have hdu := controlledErrorFactor_smooth hJ hU
  have hfa := (controlledValue_smooth hJ hL).exp
  have hfr := (rescale_smooth hJ hL).exp
  have hua := controlledValue_smooth hJ hU
  have hur := rescale_smooth hJ hU
  cases r with
  | mass => exact hx.mul hdu
  | angular => exact (contDiffOn_const.mul (hx.pow 2)).mul hdf
  | transport =>
    exact (contDiffOn_const.mul (hx.pow 2)).mul ((hdf.mul hua).add (hfr.mul hdu))
  | energy => exact hx.mul ((hdu.mul (hua.add hur)).sub ((hx.mul hdf).mul (hfa.add hfr)))
  | pressure => exact (hx.mul hdf).mul (hfa.add hfr)

theorem density_scaled_factor {T : ℝ} (hT : T ≠ 0) (κ X0 : ℝ)
    {J : Set ℝ} (hJ : IsOpen J) {L U : Field}
    (hL : ContDiffOn ℝ ∞ L (logDomain J hJ).carrier)
    (hU : ContDiffOn ℝ ∞ U (logDomain J hJ).carrier)
    (r : HistoryRow) (u : ℝ) {η : ℝ} (hη : η ∈ J) :
    logDensity X0 (activatedAngular T κ L) (controlled T κ U) r (T * u, η) -
      logDensity X0 (referenceAngular L) U r (T * u, η) =
        scaledDistance ((κ, T), (u, η)) * densityErrorFactor X0 L U r ((κ, T), (u, η)) := by
  have hf := angular_scaled_factor hT κ hJ hL u hη
  have hu := controlled_scaled_factor hT κ hJ hU u hη
  have hfa : angularValue L ((κ, T), (u, η)) = activatedAngular T κ L (T * u, η) := by
    rw [angularValue, controlledValue_eq hT κ hJ hL u hη]
    rfl
  have hua := controlledValue_eq hT κ hJ hU u hη
  have hf' : angularValue L ((κ, T), (u, η)) = Real.exp (rescale L ((κ, T), (u, η))) +
      scaledDistance ((κ, T), (u, η)) * angularErrorFactor L ((κ, T), (u, η)) := by
    rw [hfa]
    dsimp only [rescale, referenceAngular] at hf ⊢
    linarith
  have hu' : controlledValue U ((κ, T), (u, η)) = rescale U ((κ, T), (u, η)) +
      scaledDistance ((κ, T), (u, η)) * controlledErrorFactor U ((κ, T), (u, η)) := rfl
  change radius X0 (T * u) * radialDensity r (radius X0 (T * u))
      (activatedAngular T κ L (T * u, η)) (controlled T κ U (T * u, η)) -
    radius X0 (T * u) * radialDensity r (radius X0 (T * u))
      (Real.exp (rescale L ((κ, T), (u, η)))) (rescale U ((κ, T), (u, η))) = _
  rw [← hfa, ← hua]
  cases r <;> dsimp only [radialDensity, densityErrorFactor] <;>
    simp only [hf', hu'] <;> ring

/-- History coefficient, given by `q.1.2 * q.2.1 * densityErrorFactor X0 L U r q`. -/
noncomputable def historyCoefficient (X0 : ℝ) (L U : Field)
    (r : HistoryRow) (q : ScaledPoint) : ℝ :=
  q.1.2 * q.2.1 * densityErrorFactor X0 L U r q

/-- History error factor, given by `parameterFactor (historyCoefficient X0 L U r)`. -/
noncomputable def historyErrorFactor (X0 : ℝ) (L U : Field)
    (r : HistoryRow) : ScaledPoint → ℝ :=
  parameterFactor (historyCoefficient X0 L U r)

theorem historyErrorFactor_smooth (X0 : ℝ) {J : Set ℝ} (hJ : IsOpen J) {L U : Field}
    (hL : ContDiffOn ℝ ∞ L (logDomain J hJ).carrier)
    (hU : ContDiffOn ℝ ∞ U (logDomain J hJ).carrier) (r : HistoryRow) :
    ContDiffOn ℝ ∞ (historyErrorFactor X0 L U r) (scaledDomain J) :=
  parameterFactor_smooth isOpen_univ hJ
    ((contDiffOn_fst.snd.mul contDiffOn_snd.fst).mul (densityErrorFactor_smooth X0 hJ hL hU r))

@[simp] theorem historyErrorFactor_zero (X0 : ℝ) (L U : Field)
    (r : HistoryRow) (κ T η : ℝ) : historyErrorFactor X0 L U r ((κ, T), (0, η)) = 0 := by
  exact parameterFactor_zero _ _ _

theorem history_scaled_factor {T : ℝ} (hT : T ≠ 0) (κ X0 : ℝ)
    (initial : HistoryRow → ℝ → ℝ) {J : Set ℝ} (hJ : IsOpen J) {L U : Field}
    (hL : ContDiffOn ℝ ∞ L (logDomain J hJ).carrier)
    (hU : ContDiffOn ℝ ∞ U (logDomain J hJ).carrier)
    (r : HistoryRow) (u : ℝ) {η : ℝ} (hη : η ∈ J) :
    logHistory X0 initial (activatedAngular T κ L) (controlled T κ U) r (T * u, η) -
      logHistory X0 initial (referenceAngular L) U r (T * u, η) =
        scaledDistance ((κ, T), (u, η)) * historyErrorFactor X0 L U r ((κ, T), (u, η)) := by
  let D : Field := fun p => logDensity X0 (activatedAngular T κ L) (controlled T κ U) r p -
    logDensity X0 (referenceAngular L) U r p
  have ha := radial_slice_intervalIntegrable (logDomain J hJ)
    (logDensity_smooth X0 hJ (activatedAngular_smooth T κ hJ hL)
      (controlled_smooth T κ hJ hU) r) (p := (T * u, η)) ⟨mem_univ _, hη⟩
  have hr := radial_slice_intervalIntegrable (logDomain J hJ)
    (logDensity_smooth X0 hJ hL.exp hU r) (p := (T * u, η)) ⟨mem_univ _, hη⟩
  change IntervalIntegrable
    (fun t => logDensity X0 (activatedAngular T κ L) (controlled T κ U) r (t, η)) volume 0 (T * u)
        at ha
  change IntervalIntegrable
    (fun t => logDensity X0 (referenceAngular L) U r (t, η)) volume 0 (T * u) at hr
  have hsub : logHistory X0 initial (activatedAngular T κ L) (controlled T κ U) r (T * u, η) -
      logHistory X0 initial (referenceAngular L) U r (T * u, η) = primitive D (T * u, η) := by
    dsimp only [logHistory, primitive, D]
    rw [add_sub_add_left_eq_sub, intervalIntegral.integral_sub ha hr]
  rw [hsub, primitive_rescaled]
  calc
    T * primitive (fun p => D (T * p.1, p.2)) (u, η) =
        T * weightedPrimitive 1 κ (fun p => historyCoefficient X0 L U r ((κ, T), p)) (u, η) := by
      congr 1
      apply intervalIntegral.integral_congr
      intro v _
      dsimp only [D, weightedField]
      rw [density_scaled_factor hT κ X0 hJ hL hU r v hη]
      dsimp only [scaledDistance, historyCoefficient]
      ring
    _ = _ := by
      rw [parameterFactor_identity]
      dsimp only [scaledDistance, historyErrorFactor]
      ring

theorem history_uniform_jets (X0 : ℝ) (initial : HistoryRow → ℝ → ℝ)
    {J K : Set ℝ} (hJ : IsOpen J) (hK : IsCompact K) (hKJ : K ⊆ J) {L U : Field}
    (hL : ContDiffOn ℝ ∞ L (logDomain J hJ).carrier)
    (hU : ContDiffOn ℝ ∞ U (logDomain J hJ).carrier)
    (T0 : ℝ) (r : HistoryRow) (n : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ T ∈ Ioc (0 : ℝ) T0, ∀ κ ∈ Icc (0 : ℝ) 1,
      ∀ y ∈ Icc (0 : ℝ) T, ∀ η ∈ K,
        |iteratedDeriv n (fun ξ =>
          logHistory X0 initial (activatedAngular T κ L) (controlled T κ U) r (y, ξ) -
            logHistory X0 initial (referenceAngular L) U r (y, ξ)) η| ≤
              M * y * activation T κ y := by
  apply width_uniform_jet_bound hJ hK hKJ (historyErrorFactor_smooth X0 hJ hL hU r)
  intro κ T hT u η hη
  exact history_scaled_factor hT.ne' κ X0 initial hJ hL hU r u hη

/-! ## Genuine parameter differentiation of the scaled factors -/

/-- Eta D, given by `deriv (fun ξ => H (q.1, (q.2.1, ξ))) q.2.2`. -/
noncomputable def etaD (H : ScaledPoint → ℝ) (q : ScaledPoint) : ℝ :=
  deriv (fun ξ => H (q.1, (q.2.1, ξ))) q.2.2

/-- Eta linear, given by `fderiv ℝ H q ((0, 0), (0, 1))`. -/
noncomputable def etaLinear (H : ScaledPoint → ℝ) (q : ScaledPoint) : ℝ :=
  fderiv ℝ H q ((0, 0), (0, 1))

theorem etaLinear_hasDerivAt {J : Set ℝ} (hJ : IsOpen J) {H : ScaledPoint → ℝ}
    (hH : ContDiffOn ℝ ∞ H (scaledDomain J)) {q : ScaledPoint} (hq : q ∈ scaledDomain J) :
    HasDerivAt (fun ξ => H (q.1, (q.2.1, ξ))) (etaLinear H q) q.2.2 := by
  have hd := (hH.contDiffAt ((scaledDomain_open hJ).mem_nhds hq)).differentiableAt (by simp)
  have h := hd.hasFDerivAt.comp_hasDerivAt q.2.2
    ((hasDerivAt_const q.2.2 q.1).prodMk
      ((hasDerivAt_const q.2.2 q.2.1).prodMk (hasDerivAt_id q.2.2)))
  simp only [Function.comp_def, id_eq] at h
  exact h

theorem etaD_eq_etaLinear {J : Set ℝ} (hJ : IsOpen J) {H : ScaledPoint → ℝ}
    (hH : ContDiffOn ℝ ∞ H (scaledDomain J)) {q : ScaledPoint} (hq : q ∈ scaledDomain J) :
    etaD H q = etaLinear H q := (etaLinear_hasDerivAt hJ hH hq).deriv

theorem etaD_smooth {J : Set ℝ} (hJ : IsOpen J) {H : ScaledPoint → ℝ}
    (hH : ContDiffOn ℝ ∞ H (scaledDomain J)) :
    ContDiffOn ℝ ∞ (etaD H) (scaledDomain J) := by
  have hl : ContDiffOn ℝ ∞ (etaLinear H) (scaledDomain J) :=
    (hH.fderiv_of_isOpen (scaledDomain_open hJ) (by simp)).clm_apply contDiffOn_const
  exact hl.congr (fun _ hq => etaD_eq_etaLinear hJ hH hq)

theorem etaD_hasDerivAt {J : Set ℝ} (hJ : IsOpen J) {H : ScaledPoint → ℝ}
    (hH : ContDiffOn ℝ ∞ H (scaledDomain J)) {q : ScaledPoint} (hq : q ∈ scaledDomain J) :
    HasDerivAt (fun ξ => H (q.1, (q.2.1, ξ))) (etaD H q) q.2.2 := by
  rw [etaD_eq_etaLinear hJ hH hq]
  exact etaLinear_hasDerivAt hJ hH hq

theorem etaD_scaledDistance_mul (H : ScaledPoint → ℝ) (q : ScaledPoint) :
    etaD (fun z => scaledDistance z * H z) q = scaledDistance q * etaD H q := by
  exact deriv_const_mul_field (scaledDistance q)

theorem etaD_rescale {J : Set ℝ} (hJ : IsOpen J) {F : Field}
    (hF : ContDiffOn ℝ ∞ F (logDomain J hJ).carrier) {q : ScaledPoint}
    (hq : q ∈ scaledDomain J) : etaD (rescale F) q = rescale (parameterPartial F) q :=
  (parameterPartial_hasDerivAt (logDomain J hJ) hF
    (p := (q.1.2 * q.2.1, q.2.2)) ⟨mem_univ _, hq.2.2⟩).deriv

theorem etaD_congr {J : Set ℝ} (hJ : IsOpen J) {H G : ScaledPoint → ℝ}
    (h : ∀ q ∈ scaledDomain J, H q = G q) {q : ScaledPoint} (hq : q ∈ scaledDomain J) :
    etaD H q = etaD G q := by
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [hJ.mem_nhds hq.2.2] with ξ hξ
  exact h (q.1, (q.2.1, ξ)) ⟨hq.1, hq.2.1, hξ⟩

/-! ## Independence of the continuation length on the natural overlap -/

theorem continuation_radialPartial {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ)
    (hδR : 2 * δ < R) {J : Set ℝ} (hJ : IsOpen J) {G : Field}
    (hG : ContDiffOn ℝ ∞ G (ReferencePath.earlyStrip R hR J hJ).carrier)
    {p : Point} (hη : p.2 ∈ J) :
    radialPartial (ReferencePath.continuation δ G) p =
      ReferencePath.slopeCutoff δ p.1 * radialPartial G p :=
  (radialPartial_hasDerivAt (ReferencePath.fullStrip J hJ)
    (ReferencePath.continuation_smooth hR hδ hδR hJ hG) (p := p) ⟨mem_univ _, hη⟩).unique
      (ReferencePath.continuation_hasDerivAt hR hδ hδR hJ hG (p := p) hη)

theorem controlled_continuation_independent {R δ₁ δ₂ : ℝ} (hR : 0 < R)
    (hδ₁ : 0 < δ₁) (hδ₁R : 2 * δ₁ < R) (hδ₂ : 0 < δ₂) (hδ₂R : 2 * δ₂ < R)
    {J : Set ℝ} (hJ : IsOpen J) {G : Field}
    (hG : ContDiffOn ℝ ∞ G (ReferencePath.earlyStrip R hR J hJ).carrier)
    (T κ : ℝ) {p : Point} (hη : p.2 ∈ J) (hp₁ : p.1 ≤ δ₁) (hp₂ : p.1 ≤ δ₂) :
    controlled T κ (ReferencePath.continuation δ₁ G) p =
      controlled T κ (ReferencePath.continuation δ₂ G) p := by
  have hzero₁ := ReferencePath.continuation_eq_natural hR hδ₁ hδ₁R hJ hG
    (p := (0, p.2)) hη hδ₁.le
  have hzero₂ := ReferencePath.continuation_eq_natural hR hδ₂ hδ₂R hJ hG
    (p := (0, p.2)) hη hδ₂.le
  unfold controlled
  rw [hzero₁, hzero₂]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  have ht₁ : t ≤ δ₁ := (mem_uIcc.mp ht).elim
    (fun h => h.2.trans hp₁) (fun h => h.2.trans hδ₁.le)
  have ht₂ : t ≤ δ₂ := (mem_uIcc.mp ht).elim
    (fun h => h.2.trans hp₂) (fun h => h.2.trans hδ₂.le)
  dsimp only
  rw [continuation_radialPartial hR hδ₁ hδ₁R hJ hG (p := (t, p.2)) hη,
    continuation_radialPartial hR hδ₂ hδ₂R hJ hG (p := (t, p.2)) hη,
    ReferencePath.slopeCutoff_one hδ₁ ht₁, ReferencePath.slopeCutoff_one hδ₂ ht₂]

theorem profileInitial_congr {D : RadialDomain} (P Q : Profiles D)
    (h0 : ∀ η, P.pressure0 η = Q.pressure0 η) (r : HistoryRow) (η : ℝ) :
    profileInitial P r η = profileInitial Q r η := by
  cases r <;> simp only [profileInitial]
  exact h0 η

namespace NaturalOverlap

open ReferencePath

variable (N : ReferencePath.Input)

theorem f_independent {T δ₁ δ₂ : ℝ} (hT : 0 < T)
    (hδ₁ : 0 < δ₁) (hδ₁R : 2 * δ₁ < rampLimit)
    (hδ₂ : 0 < δ₂) (hδ₂R : 2 * δ₂ < rampLimit) (κ : ℝ)
    {p : Point} (hη : p.2 ∈ parameterInterval)
    (hp₁ : p.1 ≤ radius N.endpoint δ₁) (hp₂ : p.1 ≤ radius N.endpoint δ₂) :
    FromReference.f N T κ δ₁ p = FromReference.f N T κ δ₂ p := by
  by_cases hx : p.1 ≤ N.endpoint
  · rw [FromReference.f_eq_reference N T κ δ₁ hx, FromReference.f_eq_reference N T κ δ₂ hx,
      N.refF_eq_natural_initial δ₁ hx, N.refF_eq_natural_initial δ₂ hx]
  · have hX : 0 < p.1 := N.endpoint_pos.trans (lt_of_not_ge hx)
    rw [FromReference.f_eq_logtime N hT hδ₁ hδ₁R κ hη hX,
      FromReference.f_eq_logtime N hT hδ₂ hδ₂R κ hη hX]
    unfold activatedAngular FromReference.refLog
    congr 1
    exact controlled_continuation_independent rampLimit_pos hδ₁ hδ₁R hδ₂ hδ₂R
      parameterInterval_open N.logF_smooth T κ (p := (N.logTime p.1, p.2)) hη
        ((N.logTime_le_iff hX).2 hp₁) ((N.logTime_le_iff hX).2 hp₂)

theorem U_independent {T δ₁ δ₂ : ℝ} (hT : 0 < T)
    (hδ₁ : 0 < δ₁) (hδ₁R : 2 * δ₁ < rampLimit)
    (hδ₂ : 0 < δ₂) (hδ₂R : 2 * δ₂ < rampLimit) (κ : ℝ)
    {p : Point} (hη : p.2 ∈ parameterInterval)
    (hp₁ : p.1 ≤ radius N.endpoint δ₁) (hp₂ : p.1 ≤ radius N.endpoint δ₂) :
    FromReference.U N T κ δ₁ p = FromReference.U N T κ δ₂ p := by
  by_cases hx : p.1 ≤ N.endpoint
  · rw [FromReference.U_eq_reference N T κ δ₁ hx, FromReference.U_eq_reference N T κ δ₂ hx,
      N.refU_eq_natural_initial δ₁ hx, N.refU_eq_natural_initial δ₂ hx]
  · have hX : 0 < p.1 := N.endpoint_pos.trans (lt_of_not_ge hx)
    rw [FromReference.U_eq_logtime N hT hδ₁ hδ₁R κ hη hX,
      FromReference.U_eq_logtime N hT hδ₂ hδ₂R κ hη hX]
    exact controlled_continuation_independent rampLimit_pos hδ₁ hδ₁R hδ₂ hδ₂R
      parameterInterval_open N.logU_smooth T κ (p := (N.logTime p.1, p.2)) hη
        ((N.logTime_le_iff hX).2 hp₁) ((N.logTime_le_iff hX).2 hp₂)

/-- Equality is from the axis up to the comparison radius, so all recomputed
histories are equal, not just their endpoint fields. -/
theorem histories_independent {T δ₁ δ₂ : ℝ} (hT : 0 < T)
    (hδ₁ : 0 < δ₁) (hδ₁R : 2 * δ₁ < rampLimit)
    (hδ₂ : 0 < δ₂) (hδ₂R : 2 * δ₂ < rampLimit) (κ : ℝ)
    (P0 : ℝ → ℝ) (hP0 : ContDiff ℝ ∞ P0) (r : HistoryRow)
    {p : Point} (hη : p.2 ∈ parameterInterval) (hX : 0 ≤ p.1)
    (hp₁ : p.1 ≤ radius N.endpoint δ₁) (hp₂ : p.1 ≤ radius N.endpoint δ₂) :
    profileHistory (FromReference.histories N hT hδ₁ hδ₁R κ P0 hP0) r p =
      profileHistory (FromReference.histories N hT hδ₂ hδ₂R κ P0 hP0) r p := by
  let A := FromReference.histories N hT hδ₁ hδ₁R κ P0 hP0
  let B := FromReference.histories N hT hδ₂ hδ₂R κ P0 hP0
  have h0 : profileInitial A r p.2 = profileInitial B r p.2 :=
    profileInitial_congr A B (fun _ => rfl) r p.2
  have hf : ∀ x ∈ Icc (0 : ℝ) p.1, A.f (x, p.2) = B.f (x, p.2) := by
    intro x hx
    exact f_independent N hT hδ₁ hδ₁R hδ₂ hδ₂R κ (p := (x, p.2)) hη
      (hx.2.trans hp₁) (hx.2.trans hp₂)
  have hu : ∀ x ∈ Icc (0 : ℝ) p.1, A.U (x, p.2) = B.U (x, p.2) := by
    intro x hx
    exact U_independent N hT hδ₁ hδ₁R hδ₂ hδ₂R κ (p := (x, p.2)) hη
      (hx.2.trans hp₁) (hx.2.trans hp₂)
  exact profileHistory_congr_up_to A B r hX h0 hf hu

theorem reference_histories_independent {δ₁ δ₂ : ℝ}
    (hδ₁ : 0 < δ₁) (hδ₁R : 2 * δ₁ < rampLimit)
    (hδ₂ : 0 < δ₂) (hδ₂R : 2 * δ₂ < rampLimit)
    (P0 : ℝ → ℝ) (hP0 : ContDiff ℝ ∞ P0) (r : HistoryRow)
    {p : Point} (hη : p.2 ∈ parameterInterval) (hX : 0 ≤ p.1)
    (hp₁ : p.1 ≤ radius N.endpoint δ₁) (hp₂ : p.1 ≤ radius N.endpoint δ₂) :
    profileHistory (N.histories hδ₁ hδ₁R P0 hP0) r p =
      profileHistory (N.histories hδ₂ hδ₂R P0 hP0) r p := by
  let A := N.histories hδ₁ hδ₁R P0 hP0
  let B := N.histories hδ₂ hδ₂R P0 hP0
  have h0 : profileInitial A r p.2 = profileInitial B r p.2 :=
    profileInitial_congr A B (fun _ => rfl) r p.2
  have hf : ∀ x ∈ Icc (0 : ℝ) p.1, A.f (x, p.2) = B.f (x, p.2) := by
    intro x hx
    exact (N.refF_eq_natural hδ₁ hδ₁R (p := (x, p.2)) hη (hx.2.trans hp₁)).trans
      (N.refF_eq_natural hδ₂ hδ₂R (p := (x, p.2)) hη (hx.2.trans hp₂)).symm
  have hu : ∀ x ∈ Icc (0 : ℝ) p.1, A.U (x, p.2) = B.U (x, p.2) := by
    intro x hx
    exact (N.refU_eq_natural hδ₁ hδ₁R (p := (x, p.2)) hη (hx.2.trans hp₁)).trans
      (N.refU_eq_natural hδ₂ hδ₂R (p := (x, p.2)) hη (hx.2.trans hp₂)).symm
  exact profileHistory_congr_up_to A B r hX h0 hf hu

theorem radius_mono {s t : ℝ} (hst : s ≤ t) : radius N.endpoint s ≤ radius N.endpoint t :=
  mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hst) N.endpoint_pos.le

theorem fixed_history_scaled_factor {T δ : ℝ} (hT : 0 < T)
    (hδ : 0 < δ) (hδR : 2 * δ < rampLimit) (κ : ℝ)
    (P0 : ℝ → ℝ) (hP0 : ContDiff ℝ ∞ P0) (r : HistoryRow)
    (u : ℝ) {η : ℝ} (hη : η ∈ parameterInterval) :
    profileHistory (FromReference.histories N hT hδ hδR κ P0 hP0) r
        (radius N.endpoint (T * u), η) -
      profileHistory (N.histories hδ hδR P0 hP0) r (radius N.endpoint (T * u), η) =
        scaledDistance ((κ, T), (u, η)) *
          historyErrorFactor N.endpoint (FromReference.refLog N δ) (FromReference.refAxial N δ) r
            ((κ, T), (u, η)) := by
  rw [FromReference.histories_log_formula N hT hδ hδR κ P0 hP0 r (T * u) hη,
    FromReference.reference_histories_log_formula N hδ hδR P0 hP0 r (T * u) hη]
  exact history_scaled_factor hT.ne' κ N.endpoint _ parameterInterval_open
    (FromReference.refLog_smooth N hδ hδR) (FromReference.refAxial_smooth N hδ hδR) r u hη

/-- The manuscript uses the same width for ACT and REF. Its first-ramp
histories have the fixed-reference factors whenever `T ≤ δ0`. -/
theorem diagonal_history_scaled_factor {T δ0 : ℝ} (hT : 0 < T)
    (hTR : 2 * T < rampLimit) (hδ0 : 0 < δ0) (hδ0R : 2 * δ0 < rampLimit)
    (hTδ0 : T ≤ δ0) (κ : ℝ) (P0 : ℝ → ℝ) (hP0 : ContDiff ℝ ∞ P0)
    (r : HistoryRow) {u η : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) (hη : η ∈ parameterInterval) :
    profileHistory (FromReference.histories N hT hT hTR κ P0 hP0) r
        (radius N.endpoint (T * u), η) -
      profileHistory (N.histories hT hTR P0 hP0) r (radius N.endpoint (T * u), η) =
        scaledDistance ((κ, T), (u, η)) *
          historyErrorFactor N.endpoint (FromReference.refLog N δ0) (FromReference.refAxial N δ0) r
            ((κ, T), (u, η)) := by
  have hy : T * u ≤ T := mul_le_of_le_one_right hT.le hu.2
  have hx : 0 ≤ radius N.endpoint (T * u) := (mul_pos N.endpoint_pos (Real.exp_pos _)).le
  have hxT := radius_mono N hy
  have hxδ0 := radius_mono N (hy.trans hTδ0)
  rw [histories_independent N hT hT hTR hδ0 hδ0R κ P0 hP0 r hη hx hxT hxδ0,
    reference_histories_independent N hT hTR hδ0 hδ0R P0 hP0 r hη hx hxT hxδ0]
  exact fixed_history_scaled_factor N hT hδ0 hδ0R κ P0 hP0 r u hη

theorem diagonal_histories_uniform_jets {δ0 : ℝ} (hδ0 : 0 < δ0)
    (hδ0R : 2 * δ0 < rampLimit) (P0 : ℝ → ℝ) (hP0 : ContDiff ℝ ∞ P0)
    {K : Set ℝ} (hK : IsCompact K) (hKJ : K ⊆ parameterInterval) (r : HistoryRow) (n : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ T (hT : T ∈ Ioc (0 : ℝ) δ0) (hTR : 2 * T < rampLimit),
      ∀ κ ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) T, ∀ η ∈ K,
        |iteratedDeriv n (fun ξ =>
          profileHistory (FromReference.histories N hT.1 hT.1 hTR κ P0 hP0) r (radius N.endpoint y,
              ξ) -
            profileHistory (N.histories hT.1 hTR P0 hP0) r (radius N.endpoint y, ξ)) η| ≤
              M * y * activation T κ y := by
  obtain ⟨M, hM, hb⟩ := history_uniform_jets N.endpoint (fun _ _ => 0)
    parameterInterval_open hK hKJ (FromReference.refLog_smooth N hδ0 hδ0R)
      (FromReference.refAxial_smooth N hδ0 hδ0R) δ0 r n
  refine ⟨M, hM, ?_⟩
  intro T hT hTR κ hκ y hy η hη
  let u := y / T
  have hu : u ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hy.1 hT.1.le, (div_le_one hT.1).2 hy.2⟩
  have hTu : T * u = y := by dsimp only [u]; field_simp [hT.1.ne']
  have heq : (fun ξ =>
      profileHistory (FromReference.histories N hT.1 hT.1 hTR κ P0 hP0) r (radius N.endpoint y, ξ) -
        profileHistory (N.histories hT.1 hTR P0 hP0) r (radius N.endpoint y, ξ)) =ᶠ[𝓝 η]
      (fun ξ => logHistory N.endpoint (fun _ _ => 0)
          (activatedAngular T κ (FromReference.refLog N δ0))
          (controlled T κ (FromReference.refAxial N δ0)) r (y, ξ) -
        logHistory N.endpoint (fun _ _ => 0) (referenceAngular (FromReference.refLog N δ0))
          (FromReference.refAxial N δ0) r (y, ξ)) := by
    filter_upwards [parameterInterval_open.mem_nhds (hKJ hη)] with ξ hξ
    rw [← hTu]
    exact (diagonal_history_scaled_factor N hT.1 hTR hδ0 hδ0R hT.2 κ P0 hP0 r hu hξ).trans
      (history_scaled_factor hT.1.ne' κ N.endpoint (fun _ _ => 0) parameterInterval_open
        (FromReference.refLog_smooth N hδ0 hδ0R) (FromReference.refAxial_smooth N hδ0 hδ0R) r u
            hξ).symm
  rw [heq.iteratedDeriv_eq n]
  exact hb T hT κ hκ y hy η hη

end NaturalOverlap

end NavierStokes.ActivationBounds

end
end

end

@[expose] public section

noncomputable section

namespace NavierStokes.ActivationStocks

open Set Filter ProfileHistories StressActivation
open scoped Topology ContDiff

/-- Mass flux, given by `X - 2 * NaturalAxisData.D h * η * M - NaturalAxisData.d η * Mη`. -/
noncomputable def massFlux (h X η M Mη : ℝ) : ℝ :=
  X - 2 * NaturalAxisData.D h * η * M - NaturalAxisData.d η * Mη

/-- Angular remainder, given by `(1 - h) * I - NaturalAxisData.D h * η * Iη - NaturalAxisData.d
η * Jη + 2 * (h - NaturalAxisData.D h) * η * J`. -/
noncomputable def angularRemainder (h η I Iη J Jη : ℝ) : ℝ :=
  (1 - h) * I - NaturalAxisData.D h * η * Iη - NaturalAxisData.d η * Jη +
    2 * (h - NaturalAxisData.D h) * η * J

/-- Stock one, given by `(-massFlux h X η M Mη + angularRemainder h η I Iη J Jη / (2 * X * f)) /
NaturalAxisData.L h η`. -/
noncomputable def stockOne (h X η f M Mη I Iη J Jη : ℝ) : ℝ :=
  (-massFlux h X η M Mη + angularRemainder h η I Iη J Jη / (2 * X * f)) /
    NaturalAxisData.L h η

/-- Stock two as an element of `ℝ`. -/
noncomputable def stockTwo (h X η f U M Mη S Sη P Pη : ℝ) : ℝ :=
  (-massFlux h X η M Mη * U + NaturalAxisData.D h * (M - η * Mη) +
    4 * h * η * S - NaturalAxisData.d η * Sη +
    X * (4 * NaturalAxisData.A h * η * P - NaturalAxisData.d η * Pη)) /
      (NaturalAxisData.L h η * Real.sqrt (2 * X) * f)

/-- Profile stock one, given by `p.1 * P.angularLag h p / NaturalAxisData.L h p.2`. -/
noncomputable def profileStockOne {D : RadialDomain} (P : Profiles D) (h : ℝ)
    (p : Point) : ℝ := p.1 * P.angularLag h p / NaturalAxisData.L h p.2

/-- Profile stock two, given by `p.1 * P.axialLag h p / (NaturalAxisData.L h p.2 * P.E p)`. -/
noncomputable def profileStockTwo {D : RadialDomain} (P : Profiles D) (h : ℝ)
    (p : Point) : ℝ := p.1 * P.axialLag h p / (NaturalAxisData.L h p.2 * P.E p)

theorem profile_massFlux {D : RadialDomain} (P : Profiles D) (h : ℝ)
    {p : Point} (hp : p ∈ D.carrier) :
    p.1 * P.W h p = massFlux h p.1 p.2 (P.M p) (parameterPartial P.M p) := by
  rw [P.XW_eq_histories]
  have hm : parameterPartial P.M p = primitive (parameterPartial P.U) p :=
    parameterPartial_primitive D P.U_smooth hp
  rw [hm]
  rfl

theorem profileStockOne_eq {D : RadialDomain} (P : Profiles D) (h : ℝ)
    {p : Point} (hp : p ∈ D.carrier) (hX : p.1 ≠ 0) (hf : P.f p ≠ 0) :
    profileStockOne P h p = stockOne h p.1 p.2 (P.f p)
      (P.M p) (parameterPartial P.M p) (P.I p) (parameterPartial P.I p)
      (P.J p) (parameterPartial P.J p) := by
  rw [profileStockOne, P.angularLag_integrated h hp hX (P.H_ne_zero hX hf)]
  change p.1 * (-P.W h p + angularRemainder h p.2 (P.I p)
      (parameterPartial P.I p) (P.J p) (parameterPartial P.J p) / (p.1 * P.H p)) /
        NaturalAxisData.L h p.2 = _
  calc
    _ = (-p.1 * P.W h p + angularRemainder h p.2 (P.I p)
        (parameterPartial P.I p) (P.J p) (parameterPartial P.J p) / P.H p) /
          NaturalAxisData.L h p.2 := by
      congr 1
      rw [mul_add, ← mul_div_assoc, mul_div_mul_left _ _ hX]
      ring
    _ = _ := by
      rw [show -p.1 * P.W h p = -(p.1 * P.W h p) by ring, profile_massFlux P h hp]
      rfl

theorem profileStockTwo_eq {D : RadialDomain} (P : Profiles D) (h : ℝ)
    {p : Point} (hp : p ∈ D.carrier) (hX : 0 < p.1) :
    profileStockTwo P h p = stockTwo h p.1 p.2 (P.f p) (P.U p)
      (P.M p) (parameterPartial P.M p) (P.S p) (parameterPartial P.S p)
      (P.pressure p) (parameterPartial P.pressure p) := by
  rw [profileStockTwo, P.axialLag_integrated h hp hX]
  unfold stockTwo
  rw [show NaturalAxisData.L h p.2 * Real.sqrt (2 * p.1) * P.f p =
    NaturalAxisData.L h p.2 * P.E p by dsimp only [Profiles.E]; ring]
  congr 1
  rw [← profile_massFlux P h hp]
  dsimp only [StressAlgebra.axialExponent, StressAlgebra.velocityExponent,
    StressAlgebra.coordinateFactor, NaturalAxisData.D, NaturalAxisData.A, NaturalAxisData.d]
  field_simp; ring

section SmoothPairs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Two actual smooth values with an explicitly constructed smooth factor
for their difference. The following algebra constructs new factors. -/
structure SmoothPair (Ω : Set E) (w : E → ℝ) where
  /-- Actual of `SmoothPair`, of type `E → ℝ`. -/
  actual : E → ℝ
  /-- Reference of `SmoothPair`, of type `E → ℝ`. -/
  reference : E → ℝ
  /-- Factor of `SmoothPair`, of type `E → ℝ`. -/
  factor : E → ℝ
  actual_smooth : ContDiffOn ℝ ∞ actual Ω
  reference_smooth : ContDiffOn ℝ ∞ reference Ω
  factor_smooth : ContDiffOn ℝ ∞ factor Ω
  difference : ∀ p ∈ Ω, actual p - reference p = w p * factor p

namespace SmoothPair

variable {Ω : Set E} {w : E → ℝ}

/-- Common, bundling `actual`, `reference`, `factor`, `actual_smooth` and the required
compatibility proofs. -/
noncomputable def common (F : E → ℝ) (hF : ContDiffOn ℝ ∞ F Ω) : SmoothPair Ω w where
  actual := F
  reference := F
  factor := fun _ => 0
  actual_smooth := hF
  reference_smooth := hF
  factor_smooth := contDiffOn_const
  difference := by intro p hp; simp

/-- Add, bundling `actual`, `reference`, `factor`, `actual_smooth` and the required
compatibility proofs. -/
noncomputable def add (A B : SmoothPair Ω w) : SmoothPair Ω w where
  actual := fun p => A.actual p + B.actual p
  reference := fun p => A.reference p + B.reference p
  factor := fun p => A.factor p + B.factor p
  actual_smooth := A.actual_smooth.add B.actual_smooth
  reference_smooth := A.reference_smooth.add B.reference_smooth
  factor_smooth := A.factor_smooth.add B.factor_smooth
  difference := by intro p hp; nlinarith [A.difference p hp, B.difference p hp]

/-- Neg, bundling `actual`, `reference`, `factor`, `actual_smooth` and the required
compatibility proofs. -/
noncomputable def neg (A : SmoothPair Ω w) : SmoothPair Ω w where
  actual := fun p => -A.actual p
  reference := fun p => -A.reference p
  factor := fun p => -A.factor p
  actual_smooth := A.actual_smooth.neg
  reference_smooth := A.reference_smooth.neg
  factor_smooth := A.factor_smooth.neg
  difference := by intro p hp; nlinarith [A.difference p hp]

/-- Sub, given by `A.add B.neg`. -/
noncomputable def sub (A B : SmoothPair Ω w) : SmoothPair Ω w := A.add B.neg

/-- Mul, bundling `actual`, `reference`, `factor`, `actual_smooth` and the required
compatibility proofs. -/
noncomputable def mul (A B : SmoothPair Ω w) : SmoothPair Ω w where
  actual := fun p => A.actual p * B.actual p
  reference := fun p => A.reference p * B.reference p
  factor := fun p => A.factor p * B.actual p + A.reference p * B.factor p
  actual_smooth := A.actual_smooth.mul B.actual_smooth
  reference_smooth := A.reference_smooth.mul B.reference_smooth
  factor_smooth := (A.factor_smooth.mul B.actual_smooth).add (A.reference_smooth.mul
      B.factor_smooth)
  difference := by
    intro p hp
    calc
      _ = (A.actual p - A.reference p) * B.actual p +
          A.reference p * (B.actual p - B.reference p) := by ring
      _ = _ := by rw [A.difference p hp, B.difference p hp]; ring

/-- Inv, bundling `actual`, `reference`, `factor`, `actual_smooth` and the required
compatibility proofs. -/
noncomputable def inv (A : SmoothPair Ω w)
    (ha : ∀ p ∈ Ω, A.actual p ≠ 0) (hr : ∀ p ∈ Ω, A.reference p ≠ 0) : SmoothPair Ω w where
  actual := fun p => (A.actual p)⁻¹
  reference := fun p => (A.reference p)⁻¹
  factor := fun p => -A.factor p / (A.actual p * A.reference p)
  actual_smooth := A.actual_smooth.inv ha
  reference_smooth := A.reference_smooth.inv hr
  factor_smooth := A.factor_smooth.neg.div (A.actual_smooth.mul A.reference_smooth)
    (fun p hp => mul_ne_zero (ha p hp) (hr p hp))
  difference := by
    intro p hp
    have hpa := ha p hp
    have hpr := hr p hp
    calc
      _ = -(A.actual p - A.reference p) / (A.actual p * A.reference p) := by field_simp; ring
      _ = _ := by rw [A.difference p hp]; ring

/-- Div, given by `A.mul (B.inv ha hr)`. -/
noncomputable def div (A B : SmoothPair Ω w)
    (ha : ∀ p ∈ Ω, B.actual p ≠ 0) (hr : ∀ p ∈ Ω, B.reference p ≠ 0) : SmoothPair Ω w :=
  A.mul (B.inv ha hr)

end SmoothPair

end SmoothPairs

/-- Eta D, given by `deriv (fun η => F (p.1, η)) p.2`. -/
noncomputable def etaD (F : Field) (p : Point) : ℝ :=
  deriv (fun η => F (p.1, η)) p.2

theorem etaD_eq_parameterPartial {D : RadialDomain} {F : Field}
    (hF : ContDiffOn ℝ ∞ F D.carrier) {p : Point} (hp : p ∈ D.carrier) :
    etaD F p = parameterPartial F p :=
  (parameterPartial_hasDerivAt D hF hp).deriv

/-- Log view one, constructed using `stockOne`. -/
noncomputable def logViewOne (h X0 : ℝ) (f : Field) (H : HistoryRow → Field) (p : Point) : ℝ :=
  stockOne h (radius X0 p.1) p.2 (f p) (H .mass p) (etaD (H .mass) p)
    (H .angular p) (etaD (H .angular) p) (H .transport p) (etaD (H .transport) p)

/-- Log view two, constructed using `stockTwo`. -/
noncomputable def logViewTwo (h X0 : ℝ) (f U : Field) (H : HistoryRow → Field) (p : Point) : ℝ :=
  stockTwo h (radius X0 p.1) p.2 (f p) (U p) (H .mass p) (etaD (H .mass) p)
    (H .energy p) (etaD (H .energy) p) (H .pressure p) (etaD (H .pressure) p)

theorem etaD_history_identity {D : RadialDomain} (P : Profiles D) (r : HistoryRow)
    {J : Set ℝ} (hJ : IsOpen J) {X y η : ℝ} (hη : η ∈ J) {H : Field}
    (hmem : (X, η) ∈ D.carrier)
    (heq : ∀ ξ ∈ J, H (y, ξ) = profileHistory P r (X, ξ)) :
    etaD H (y, η) = parameterPartial (profileHistory P r) (X, η) := by
  have hevent : (fun ξ => H (y, ξ)) =ᶠ[𝓝 η] fun ξ => profileHistory P r (X, ξ) := by
    filter_upwards [hJ.mem_nhds hη] with ξ hξ
    exact heq ξ hξ
  exact hevent.deriv_eq.trans (parameterPartial_hasDerivAt D (profileHistory_smooth P r) hmem).deriv

theorem profileStockOne_logView {D : RadialDomain} (P : Profiles D) (h X0 : ℝ)
    {J : Set ℝ} (hJ : IsOpen J) {p : Point} (hη : p.2 ∈ J)
    (hmem : (radius X0 p.1, p.2) ∈ D.carrier) (hX : radius X0 p.1 ≠ 0)
    {f : Field} {H : HistoryRow → Field}
    (hfield : f p = P.f (radius X0 p.1, p.2)) (hf : f p ≠ 0)
    (hH : ∀ r ξ, ξ ∈ J → H r (p.1, ξ) = profileHistory P r (radius X0 p.1, ξ)) :
    profileStockOne P h (radius X0 p.1, p.2) = logViewOne h X0 f H p := by
  have hpf : P.f (radius X0 p.1, p.2) ≠ 0 := hfield ▸ hf
  rw [profileStockOne_eq P h hmem hX hpf]
  have hd (r : HistoryRow) : etaD (H r) p =
      parameterPartial (profileHistory P r) (radius X0 p.1, p.2) :=
    etaD_history_identity P r hJ hη hmem (hH r)
  dsimp only [logViewOne]
  rw [hfield, show H .mass p = profileHistory P .mass (radius X0 p.1, p.2) from hH .mass p.2 hη,
    show H .angular p = profileHistory P .angular (radius X0 p.1, p.2) from hH .angular p.2 hη,
    show H .transport p = profileHistory P .transport (radius X0 p.1, p.2) from hH .transport p.2
        hη,
    hd .mass, hd .angular, hd .transport]
  rfl

theorem profileStockTwo_logView {D : RadialDomain} (P : Profiles D) (h X0 : ℝ)
    {J : Set ℝ} (hJ : IsOpen J) {p : Point} (hη : p.2 ∈ J)
    (hmem : (radius X0 p.1, p.2) ∈ D.carrier) (hX : 0 < radius X0 p.1)
    {f U : Field} {H : HistoryRow → Field}
    (hfield : f p = P.f (radius X0 p.1, p.2))
    (hU : U p = P.U (radius X0 p.1, p.2))
    (hH : ∀ r ξ, ξ ∈ J → H r (p.1, ξ) = profileHistory P r (radius X0 p.1, ξ)) :
    profileStockTwo P h (radius X0 p.1, p.2) = logViewTwo h X0 f U H p := by
  rw [profileStockTwo_eq P h hmem hX]
  have hd (r : HistoryRow) : etaD (H r) p =
      parameterPartial (profileHistory P r) (radius X0 p.1, p.2) :=
    etaD_history_identity P r hJ hη hmem (hH r)
  dsimp only [logViewTwo]
  rw [hfield, hU,
    show H .mass p = profileHistory P .mass (radius X0 p.1, p.2) from hH .mass p.2 hη,
    show H .energy p = profileHistory P .energy (radius X0 p.1, p.2) from hH .energy p.2 hη,
    show H .pressure p = profileHistory P .pressure (radius X0 p.1, p.2) from hH .pressure p.2 hη,
    hd .mass, hd .energy, hd .pressure]
  rfl

namespace FromReference

open ReferencePath

variable (N : ReferencePath.Input)

/-- Initial, defined pointwise by `profileHistory (N.histories hδ hδT P0 hP0) r (N.endpoint,
η)`. -/
noncomputable def initial {δ : ℝ} (hδ : 0 < δ) (hδT : 2 * δ < rampLimit)
    (P0 : ℝ → ℝ) (hP0 : ContDiff ℝ ∞ P0) : HistoryRow → ℝ → ℝ :=
  fun r η => profileHistory (N.histories hδ hδT P0 hP0) r (N.endpoint, η)

theorem initial_smooth {δ : ℝ} (hδ : 0 < δ) (hδT : 2 * δ < rampLimit)
    (P0 : ℝ → ℝ) (hP0 : ContDiff ℝ ∞ P0) (r : HistoryRow) :
    ContDiffOn ℝ ∞ (initial N hδ hδT P0 hP0 r) parameterInterval := by
  apply (profileHistory_smooth (N.histories hδ hδT P0 hP0) r).comp
    (contDiff_const.prodMk contDiff_id).contDiffOn
  intro η hη
  simpa only [radius, Real.exp_zero, mul_one, id_eq] using
    StressActivation.FromReference.log_radius_mem N 0 hη

theorem actual_stockOne_logView {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2 * δ < rampLimit) (κ h : ℝ) (P0 : ℝ → ℝ) (hP0 : ContDiff ℝ ∞ P0)
    (y : ℝ) {η : ℝ} (hη : η ∈ parameterInterval) :
    profileStockOne (StressActivation.FromReference.histories N hT hδ hδT κ P0 hP0) h
      (radius N.endpoint y, η) =
      logViewOne h N.endpoint (activatedAngular T κ (StressActivation.FromReference.refLog N δ))
        (logHistory N.endpoint (initial N hδ hδT P0 hP0)
          (activatedAngular T κ (StressActivation.FromReference.refLog N δ))
          (controlled T κ (StressActivation.FromReference.refAxial N δ))) (y, η) := by
  apply profileStockOne_logView (StressActivation.FromReference.histories N hT hδ hδT κ P0 hP0)
    h N.endpoint parameterInterval_open (p := (y, η)) hη
    (StressActivation.FromReference.log_radius_mem N y hη)
    (mul_pos N.endpoint_pos (Real.exp_pos y)).ne'
  · exact (StressActivation.FromReference.f_logPullback N hT hδ hδT κ y hη).symm
  · exact (Real.exp_pos _).ne'
  · intro r ξ hξ
    exact (StressActivation.FromReference.histories_log_formula N hT hδ hδT κ P0 hP0 r y hξ).symm

theorem actual_stockTwo_logView {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2 * δ < rampLimit) (κ h : ℝ) (P0 : ℝ → ℝ) (hP0 : ContDiff ℝ ∞ P0)
    (y : ℝ) {η : ℝ} (hη : η ∈ parameterInterval) :
    profileStockTwo (StressActivation.FromReference.histories N hT hδ hδT κ P0 hP0) h
      (radius N.endpoint y, η) =
      logViewTwo h N.endpoint (activatedAngular T κ (StressActivation.FromReference.refLog N δ))
        (controlled T κ (StressActivation.FromReference.refAxial N δ))
        (logHistory N.endpoint (initial N hδ hδT P0 hP0)
          (activatedAngular T κ (StressActivation.FromReference.refLog N δ))
          (controlled T κ (StressActivation.FromReference.refAxial N δ))) (y, η) := by
  apply profileStockTwo_logView (StressActivation.FromReference.histories N hT hδ hδT κ P0 hP0)
    h N.endpoint parameterInterval_open (p := (y, η)) hη
    (StressActivation.FromReference.log_radius_mem N y hη)
    (mul_pos N.endpoint_pos (Real.exp_pos y))
  · exact (StressActivation.FromReference.f_logPullback N hT hδ hδT κ y hη).symm
  · exact (StressActivation.FromReference.U_logPullback N hT hδ hδT κ y hη).symm
  · intro r ξ hξ
    exact (StressActivation.FromReference.histories_log_formula N hT hδ hδT κ P0 hP0 r y hξ).symm

theorem reference_stockOne_logView {δ : ℝ} (hδ : 0 < δ) (hδT : 2 * δ < rampLimit)
    (h : ℝ) (P0 : ℝ → ℝ) (hP0 : ContDiff ℝ ∞ P0)
    (y : ℝ) {η : ℝ} (hη : η ∈ parameterInterval) :
    profileStockOne (N.histories hδ hδT P0 hP0) h (radius N.endpoint y, η) =
      logViewOne h N.endpoint (referenceAngular (StressActivation.FromReference.refLog N δ))
        (logHistory N.endpoint (initial N hδ hδT P0 hP0)
          (referenceAngular (StressActivation.FromReference.refLog N δ))
          (StressActivation.FromReference.refAxial N δ)) (y, η) := by
  apply profileStockOne_logView (N.histories hδ hδT P0 hP0)
    h N.endpoint parameterInterval_open (p := (y, η)) hη
    (StressActivation.FromReference.log_radius_mem N y hη)
    (mul_pos N.endpoint_pos (Real.exp_pos y)).ne'
  · exact (StressActivation.FromReference.refF_logPullback N hδ hδT y hη).symm
  · exact (Real.exp_pos _).ne'
  · intro r ξ hξ
    exact (StressActivation.FromReference.reference_histories_log_formula N hδ hδT P0 hP0 r y
        hξ).symm

theorem reference_stockTwo_logView {δ : ℝ} (hδ : 0 < δ) (hδT : 2 * δ < rampLimit)
    (h : ℝ) (P0 : ℝ → ℝ) (hP0 : ContDiff ℝ ∞ P0)
    (y : ℝ) {η : ℝ} (hη : η ∈ parameterInterval) :
    profileStockTwo (N.histories hδ hδT P0 hP0) h (radius N.endpoint y, η) =
      logViewTwo h N.endpoint (referenceAngular (StressActivation.FromReference.refLog N δ))
        (StressActivation.FromReference.refAxial N δ)
        (logHistory N.endpoint (initial N hδ hδT P0 hP0)
          (referenceAngular (StressActivation.FromReference.refLog N δ))
          (StressActivation.FromReference.refAxial N δ)) (y, η) := by
  apply profileStockTwo_logView (N.histories hδ hδT P0 hP0)
    h N.endpoint parameterInterval_open (p := (y, η)) hη
    (StressActivation.FromReference.log_radius_mem N y hη)
    (mul_pos N.endpoint_pos (Real.exp_pos y))
  · exact (StressActivation.FromReference.refF_logPullback N hδ hδT y hη).symm
  · exact (StressActivation.FromReference.refU_logPullback N hδ hδT y hη).symm
  · intro r ξ hξ
    exact (StressActivation.FromReference.reference_histories_log_formula N hδ hδT P0 hP0 r y
        hξ).symm

end FromReference

open ActivationBounds (ScaledPoint scaledDomain scaledDistance)

/-- Stock pair: an abbreviation for `SmoothPair (scaledDomain J) scaledDistance`. -/
abbrev StockPair (J : Set ℝ) := SmoothPair (scaledDomain J) scaledDistance

/-- Parameter differentiation preserves the same flat-distance factor. -/
noncomputable def etaPair {J : Set ℝ} (hJ : IsOpen J) (A : StockPair J) : StockPair J where
  actual := ActivationBounds.etaD A.actual
  reference := ActivationBounds.etaD A.reference
  factor := ActivationBounds.etaD A.factor
  actual_smooth := ActivationBounds.etaD_smooth hJ A.actual_smooth
  reference_smooth := ActivationBounds.etaD_smooth hJ A.reference_smooth
  factor_smooth := ActivationBounds.etaD_smooth hJ A.factor_smooth
  difference := by
    intro q hq
    have he := ActivationBounds.etaD_congr hJ A.difference hq
    have hs : ActivationBounds.etaD (fun z => A.actual z - A.reference z) q =
        ActivationBounds.etaD A.actual q - ActivationBounds.etaD A.reference q :=
      ((ActivationBounds.etaD_hasDerivAt hJ A.actual_smooth hq).sub
        (ActivationBounds.etaD_hasDerivAt hJ A.reference_smooth hq)).deriv
    rw [hs, ActivationBounds.etaD_scaledDistance_mul] at he
    exact he

theorem etaPair_actual_eq {J : Set ℝ} (hJ : IsOpen J) (A : StockPair J)
    (F : Field) (κ T u : ℝ) {η : ℝ} (hη : η ∈ J)
    (heq : ∀ ξ ∈ J, A.actual ((κ, T), (u, ξ)) = F (T * u, ξ)) :
    (etaPair hJ A).actual ((κ, T), (u, η)) = etaD F (T * u, η) := by
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [hJ.mem_nhds hη] with ξ hξ
  exact heq ξ hξ

theorem etaPair_reference_eq {J : Set ℝ} (hJ : IsOpen J) (A : StockPair J)
    (F : Field) (κ T u : ℝ) {η : ℝ} (hη : η ∈ J)
    (heq : ∀ ξ ∈ J, A.reference ((κ, T), (u, ξ)) = F (T * u, ξ)) :
    (etaPair hJ A).reference ((κ, T), (u, η)) = etaD F (T * u, η) := by
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [hJ.mem_nhds hη] with ξ hξ
  exact heq ξ hξ

/-- Controlled pair, bundling `actual`, `reference`, `factor`, `actual_smooth` and the required
compatibility proofs. -/
noncomputable def controlledPair {J : Set ℝ} (hJ : IsOpen J) {U : Field}
    (hU : ContDiffOn ℝ ∞ U (logDomain J hJ).carrier) : StockPair J where
  actual := ActivationBounds.controlledValue U
  reference := ActivationBounds.rescale U
  factor := ActivationBounds.controlledErrorFactor U
  actual_smooth := ActivationBounds.controlledValue_smooth hJ hU
  reference_smooth := ActivationBounds.rescale_smooth hJ hU
  factor_smooth := ActivationBounds.controlledErrorFactor_smooth hJ hU
  difference := by intro q hq; dsimp only [ActivationBounds.controlledValue]; ring

/-- Angular pair, bundling `actual`, `reference`, `factor`, `actual_smooth` and the required
compatibility proofs. -/
noncomputable def angularPair {J : Set ℝ} (hJ : IsOpen J) {L : Field}
    (hL : ContDiffOn ℝ ∞ L (logDomain J hJ).carrier) : StockPair J where
  actual := ActivationBounds.angularValue L
  reference := fun q => Real.exp (ActivationBounds.rescale L q)
  factor := ActivationBounds.angularErrorFactor L
  actual_smooth := (ActivationBounds.controlledValue_smooth hJ hL).exp
  reference_smooth := (ActivationBounds.rescale_smooth hJ hL).exp
  factor_smooth := ActivationBounds.angularErrorFactor_smooth hJ hL
  difference := by
    intro q hq
    dsimp only [ActivationBounds.angularValue, ActivationBounds.controlledValue,
      ActivationBounds.angularErrorFactor, ActivationBounds.relativeErrorFactor]
    rw [Real.exp_add]
    rw [show Real.exp (ActivationBounds.rescale L q) *
        Real.exp (scaledDistance q * ActivationBounds.controlledErrorFactor L q) -
          Real.exp (ActivationBounds.rescale L q) =
        Real.exp (ActivationBounds.rescale L q) *
          (Real.exp (scaledDistance q * ActivationBounds.controlledErrorFactor L q) - 1) by ring]
    rw [StressActivation.exp_sub_one]
    ring

/-- History pair, bundling `actual`, `reference`, `factor`, `actual_smooth` and the required
compatibility proofs. -/
noncomputable def historyPair (X0 : ℝ) (initial : HistoryRow → ℝ → ℝ)
    {J : Set ℝ} (hJ : IsOpen J) {L U : Field}
    (hL : ContDiffOn ℝ ∞ L (logDomain J hJ).carrier)
    (hU : ContDiffOn ℝ ∞ U (logDomain J hJ).carrier)
    (hi : ∀ r, ContDiffOn ℝ ∞ (initial r) J) (r : HistoryRow) : StockPair J where
  actual := fun q => ActivationBounds.rescale (logHistory X0 initial (referenceAngular L) U r) q +
    scaledDistance q * ActivationBounds.historyErrorFactor X0 L U r q
  reference := ActivationBounds.rescale (logHistory X0 initial (referenceAngular L) U r)
  factor := ActivationBounds.historyErrorFactor X0 L U r
  actual_smooth := (ActivationBounds.rescale_smooth hJ
    (logHistory_smooth X0 initial hJ hL.exp hU r (hi r))).add
      (ActivationBounds.scaledDistance_smooth.contDiffOn.mul
        (ActivationBounds.historyErrorFactor_smooth X0 hJ hL hU r))
  reference_smooth := ActivationBounds.rescale_smooth hJ
    (logHistory_smooth X0 initial hJ hL.exp hU r (hi r))
  factor_smooth := ActivationBounds.historyErrorFactor_smooth X0 hJ hL hU r
  difference := by intro q hq; ring

theorem historyPair_actual_eq (X0 : ℝ) (initial : HistoryRow → ℝ → ℝ)
    {J : Set ℝ} (hJ : IsOpen J) {L U : Field}
    (hL : ContDiffOn ℝ ∞ L (logDomain J hJ).carrier)
    (hU : ContDiffOn ℝ ∞ U (logDomain J hJ).carrier)
    (hi : ∀ r, ContDiffOn ℝ ∞ (initial r) J)
    {T : ℝ} (hT : T ≠ 0) (κ : ℝ) (r : HistoryRow) (u : ℝ) {η : ℝ} (hη : η ∈ J) :
    (historyPair X0 initial hJ hL hU hi r).actual ((κ, T), (u, η)) =
      logHistory X0 initial (activatedAngular T κ L) (controlled T κ U) r (T * u, η) := by
  have he := ActivationBounds.history_scaled_factor hT κ X0 initial hJ hL hU r u hη
  dsimp only [historyPair, ActivationBounds.rescale]
  linarith

theorem angularPair_actual_eq {J : Set ℝ} (hJ : IsOpen J) {L : Field}
    (hL : ContDiffOn ℝ ∞ L (logDomain J hJ).carrier)
    {T : ℝ} (hT : T ≠ 0) (κ u : ℝ) {η : ℝ} (hη : η ∈ J) :
    (angularPair hJ hL).actual ((κ, T), (u, η)) = activatedAngular T κ L (T * u, η) := by
  dsimp only [angularPair, ActivationBounds.angularValue, activatedAngular]
  rw [ActivationBounds.controlledValue_eq hT κ hJ hL u hη]

/-- Scaled radius, given by `radius X0 (q.1.2 * q.2.1)`. -/
noncomputable def scaledRadius (X0 : ℝ) (q : ScaledPoint) : ℝ := radius X0 (q.1.2 * q.2.1)

theorem scaledRadius_smooth (X0 : ℝ) : ContDiff ℝ ∞ (scaledRadius X0) :=
  (radius_smooth X0).comp (contDiff_fst.snd.mul contDiff_snd.fst)

theorem scaledRadius_pos {X0 : ℝ} (hX0 : 0 < X0) (q : ScaledPoint) : 0 < scaledRadius X0 q :=
  mul_pos hX0 (Real.exp_pos _)

/-- Constant pair, given by `SmoothPair.common (fun _ => c) contDiffOn_const`. -/
noncomputable def constantPair (J : Set ℝ) (c : ℝ) : StockPair J :=
  SmoothPair.common (fun _ => c) contDiffOn_const

/-- Parameter pair, given by `SmoothPair.common (fun q => g q.2.2) (hg.comp
contDiff_snd.snd).contDiffOn`. -/
noncomputable def parameterPair (J : Set ℝ) (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g) : StockPair J :=
  SmoothPair.common (fun q => g q.2.2) (hg.comp contDiff_snd.snd).contDiffOn

/-- Radius pair, given by `SmoothPair.common (scaledRadius X0) (scaledRadius_smooth
X0).contDiffOn`. -/
noncomputable def radiusPair (J : Set ℝ) (X0 : ℝ) : StockPair J :=
  SmoothPair.common (scaledRadius X0) (scaledRadius_smooth X0).contDiffOn

/-- Sqrt radius pair, constructed using `SmoothPair.common`. -/
noncomputable def sqrtRadiusPair (J : Set ℝ) {X0 : ℝ} (hX0 : 0 < X0) : StockPair J :=
  SmoothPair.common (fun q => Real.sqrt (2 * scaledRadius X0 q)) (by
    exact ((contDiff_const.mul (scaledRadius_smooth X0)).sqrt
      (fun q => (mul_pos (by norm_num) (scaledRadius_pos hX0 q)).ne')).contDiffOn)

/-- D pair, given by `parameterPair J NaturalAxisData.d (contDiff_const.sub (contDiff_id.pow
2))`. -/
noncomputable def dPair (J : Set ℝ) : StockPair J :=
  parameterPair J NaturalAxisData.d (contDiff_const.sub (contDiff_id.pow 2))

/-- L pair, given by `parameterPair J (NaturalAxisData.L h) (contDiff_const.sub
(contDiff_const.mul (contDiff_id.pow 2)))`. -/
noncomputable def lPair (J : Set ℝ) (h : ℝ) : StockPair J :=
  parameterPair J (NaturalAxisData.L h)
    (contDiff_const.sub (contDiff_const.mul (contDiff_id.pow 2)))

/-- Eta pair common, given by `parameterPair J id contDiff_id`. -/
noncomputable def etaPairCommon (J : Set ℝ) : StockPair J := parameterPair J id contDiff_id

/-- Mass flux pair as an element of `StockPair J`. -/
noncomputable def massFluxPair {J : Set ℝ} (h X0 : ℝ)
    (H Hη : HistoryRow → StockPair J) : StockPair J :=
  ((radiusPair J X0).sub
    ((parameterPair J (fun η => 2 * NaturalAxisData.D h * η) (contDiff_const.mul contDiff_id)).mul
      (H .mass))).sub ((dPair J).mul (Hη .mass))

/-- Angular remainder pair as an element of `StockPair J`. -/
noncomputable def angularRemainderPair {J : Set ℝ} (h : ℝ)
    (H Hη : HistoryRow → StockPair J) : StockPair J :=
  ((((constantPair J (1 - h)).mul (H .angular)).sub
    ((parameterPair J (fun η => NaturalAxisData.D h * η) (contDiff_const.mul contDiff_id)).mul
      (Hη .angular))).sub ((dPair J).mul (Hη .transport))).add
        ((parameterPair J (fun η => 2 * (h - NaturalAxisData.D h) * η)
          (contDiff_const.mul contDiff_id)).mul (H .transport))

/-- Stock one pair as an element of `StockPair J`. -/
noncomputable def stockOnePair {J : Set ℝ} (h : ℝ) {X0 : ℝ} (hX0 : 0 < X0)
    (hcoef : ∀ η ∈ J, NaturalAxisData.L h η ≠ 0)
    (F : StockPair J) (H Hη : HistoryRow → StockPair J)
    (hfa : ∀ q ∈ scaledDomain J, F.actual q ≠ 0)
    (hfr : ∀ q ∈ scaledDomain J, F.reference q ≠ 0) : StockPair J := by
  let den := ((constantPair J 2).mul (radiusPair J X0)).mul F
  have hda : ∀ q ∈ scaledDomain J, den.actual q ≠ 0 := by
    intro q hq
    change 2 * scaledRadius X0 q * F.actual q ≠ 0
    exact mul_ne_zero (mul_ne_zero (by norm_num) (scaledRadius_pos hX0 q).ne') (hfa q hq)
  have hdr : ∀ q ∈ scaledDomain J, den.reference q ≠ 0 := by
    intro q hq
    change 2 * scaledRadius X0 q * F.reference q ≠ 0
    exact mul_ne_zero (mul_ne_zero (by norm_num) (scaledRadius_pos hX0 q).ne') (hfr q hq)
  let num := (massFluxPair h X0 H Hη).neg.add ((angularRemainderPair h H Hη).div den hda hdr)
  exact num.div (lPair J h) (fun q hq => hcoef q.2.2 hq.2.2) (fun q hq => hcoef q.2.2 hq.2.2)

/-- Stock two pair as an element of `StockPair J`. -/
noncomputable def stockTwoPair {J : Set ℝ} (h : ℝ) {X0 : ℝ} (hX0 : 0 < X0)
    (hcoef : ∀ η ∈ J, NaturalAxisData.L h η ≠ 0)
    (F U : StockPair J) (H Hη : HistoryRow → StockPair J)
    (hfa : ∀ q ∈ scaledDomain J, F.actual q ≠ 0)
    (hfr : ∀ q ∈ scaledDomain J, F.reference q ≠ 0) : StockPair J := by
  let num := (((((massFluxPair h X0 H Hη).neg.mul U).add
    ((constantPair J (NaturalAxisData.D h)).mul ((H .mass).sub ((etaPairCommon J).mul (Hη
        .mass))))).add
    ((parameterPair J (fun η => 4 * h * η) (contDiff_const.mul contDiff_id)).mul (H .energy))).sub
    ((dPair J).mul (Hη .energy))).add
      ((radiusPair J X0).mul (((parameterPair J (fun η => 4 * NaturalAxisData.A h * η)
        (contDiff_const.mul contDiff_id)).mul (H .pressure)).sub ((dPair J).mul (Hη .pressure))))
  let den := ((lPair J h).mul (sqrtRadiusPair J hX0)).mul F
  have hda : ∀ q ∈ scaledDomain J, den.actual q ≠ 0 := by
    intro q hq
    exact mul_ne_zero (mul_ne_zero (hcoef q.2.2 hq.2.2)
      (Real.sqrt_pos.mpr (mul_pos (by norm_num) (scaledRadius_pos hX0 q))).ne') (hfa q hq)
  have hdr : ∀ q ∈ scaledDomain J, den.reference q ≠ 0 := by
    intro q hq
    exact mul_ne_zero (mul_ne_zero (hcoef q.2.2 hq.2.2)
      (Real.sqrt_pos.mpr (mul_pos (by norm_num) (scaledRadius_pos hX0 q))).ne') (hfr q hq)
  exact num.div den hda hdr

theorem stockOnePair_actual {J : Set ℝ} (h : ℝ) {X0 : ℝ} (hX0 : 0 < X0)
    (hcoef : ∀ η ∈ J, NaturalAxisData.L h η ≠ 0)
    (F : StockPair J) (H Hη : HistoryRow → StockPair J)
    (hfa : ∀ q ∈ scaledDomain J, F.actual q ≠ 0)
    (hfr : ∀ q ∈ scaledDomain J, F.reference q ≠ 0) (q : ScaledPoint) :
    (stockOnePair h hX0 hcoef F H Hη hfa hfr).actual q =
      stockOne h (scaledRadius X0 q) q.2.2 (F.actual q)
        ((H .mass).actual q) ((Hη .mass).actual q)
        ((H .angular).actual q) ((Hη .angular).actual q)
        ((H .transport).actual q) ((Hη .transport).actual q) := by
  dsimp only [stockOnePair, massFluxPair, angularRemainderPair, constantPair, parameterPair,
    radiusPair, dPair, lPair, SmoothPair.common, SmoothPair.add, SmoothPair.sub,
    SmoothPair.neg, SmoothPair.mul, SmoothPair.div, SmoothPair.inv,
    stockOne, massFlux, angularRemainder]
  ring

theorem stockOnePair_reference {J : Set ℝ} (h : ℝ) {X0 : ℝ} (hX0 : 0 < X0)
    (hcoef : ∀ η ∈ J, NaturalAxisData.L h η ≠ 0)
    (F : StockPair J) (H Hη : HistoryRow → StockPair J)
    (hfa : ∀ q ∈ scaledDomain J, F.actual q ≠ 0)
    (hfr : ∀ q ∈ scaledDomain J, F.reference q ≠ 0) (q : ScaledPoint) :
    (stockOnePair h hX0 hcoef F H Hη hfa hfr).reference q =
      stockOne h (scaledRadius X0 q) q.2.2 (F.reference q)
        ((H .mass).reference q) ((Hη .mass).reference q)
        ((H .angular).reference q) ((Hη .angular).reference q)
        ((H .transport).reference q) ((Hη .transport).reference q) := by
  dsimp only [stockOnePair, massFluxPair, angularRemainderPair, constantPair, parameterPair,
    radiusPair, dPair, lPair, SmoothPair.common, SmoothPair.add, SmoothPair.sub,
    SmoothPair.neg, SmoothPair.mul, SmoothPair.div, SmoothPair.inv,
    stockOne, massFlux, angularRemainder]
  ring

theorem stockTwoPair_actual {J : Set ℝ} (h : ℝ) {X0 : ℝ} (hX0 : 0 < X0)
    (hcoef : ∀ η ∈ J, NaturalAxisData.L h η ≠ 0)
    (F U : StockPair J) (H Hη : HistoryRow → StockPair J)
    (hfa : ∀ q ∈ scaledDomain J, F.actual q ≠ 0)
    (hfr : ∀ q ∈ scaledDomain J, F.reference q ≠ 0) (q : ScaledPoint) :
    (stockTwoPair h hX0 hcoef F U H Hη hfa hfr).actual q =
      stockTwo h (scaledRadius X0 q) q.2.2 (F.actual q) (U.actual q)
        ((H .mass).actual q) ((Hη .mass).actual q)
        ((H .energy).actual q) ((Hη .energy).actual q)
        ((H .pressure).actual q) ((Hη .pressure).actual q) := by
  dsimp only [stockTwoPair, massFluxPair, constantPair, parameterPair,
    radiusPair, sqrtRadiusPair, etaPairCommon, dPair, lPair, SmoothPair.common,
    SmoothPair.add, SmoothPair.sub, SmoothPair.neg, SmoothPair.mul, SmoothPair.div,
    SmoothPair.inv, stockTwo, massFlux, id_eq]
  ring

theorem stockTwoPair_reference {J : Set ℝ} (h : ℝ) {X0 : ℝ} (hX0 : 0 < X0)
    (hcoef : ∀ η ∈ J, NaturalAxisData.L h η ≠ 0)
    (F U : StockPair J) (H Hη : HistoryRow → StockPair J)
    (hfa : ∀ q ∈ scaledDomain J, F.actual q ≠ 0)
    (hfr : ∀ q ∈ scaledDomain J, F.reference q ≠ 0) (q : ScaledPoint) :
    (stockTwoPair h hX0 hcoef F U H Hη hfa hfr).reference q =
      stockTwo h (scaledRadius X0 q) q.2.2 (F.reference q) (U.reference q)
        ((H .mass).reference q) ((Hη .mass).reference q)
        ((H .energy).reference q) ((Hη .energy).reference q)
        ((H .pressure).reference q) ((Hη .pressure).reference q) := by
  dsimp only [stockTwoPair, massFluxPair, constantPair, parameterPair,
    radiusPair, sqrtRadiusPair, etaPairCommon, dPair, lPair, SmoothPair.common,
    SmoothPair.add, SmoothPair.sub, SmoothPair.neg, SmoothPair.mul, SmoothPair.div,
    SmoothPair.inv, stockTwo, massFlux, id_eq]
  ring

section ConstructedFactors

variable (h : ℝ) {X0 : ℝ} (hX0 : 0 < X0) (initial : HistoryRow → ℝ → ℝ)
    {J : Set ℝ} (hJ : IsOpen J) {L U : Field}
    (hL : ContDiffOn ℝ ∞ L (logDomain J hJ).carrier)
    (hU : ContDiffOn ℝ ∞ U (logDomain J hJ).carrier)
    (hi : ∀ r, ContDiffOn ℝ ∞ (initial r) J)
    (hcoef : ∀ η ∈ J, NaturalAxisData.L h η ≠ 0)

/-- Activation one pair, constructed using `stockOnePair`. -/
noncomputable def activationOnePair : StockPair J :=
  stockOnePair h hX0 hcoef (angularPair hJ hL)
    (historyPair X0 initial hJ hL hU hi)
    (fun r => etaPair hJ (historyPair X0 initial hJ hL hU hi r))
    (fun _q _ => (Real.exp_pos _).ne') (fun _q _ => (Real.exp_pos _).ne')

/-- Activation two pair, constructed using `stockTwoPair`. -/
noncomputable def activationTwoPair : StockPair J :=
  stockTwoPair h hX0 hcoef (angularPair hJ hL) (controlledPair hJ hU)
    (historyPair X0 initial hJ hL hU hi)
    (fun r => etaPair hJ (historyPair X0 initial hJ hL hU hi r))
    (fun _q _ => (Real.exp_pos _).ne') (fun _q _ => (Real.exp_pos _).ne')

theorem historyEtaPair_actual {T : ℝ} (hT : T ≠ 0) (κ u : ℝ)
    {η : ℝ} (hη : η ∈ J) (r : HistoryRow) :
    (etaPair hJ (historyPair X0 initial hJ hL hU hi r)).actual ((κ, T), (u, η)) =
      etaD (logHistory X0 initial (activatedAngular T κ L) (controlled T κ U) r) (T * u, η) := by
  refine etaPair_actual_eq hJ (historyPair X0 initial hJ hL hU hi r) _ κ T u hη ?_
  intro ξ hξ
  exact historyPair_actual_eq X0 initial hJ hL hU hi hT κ r u hξ

theorem historyEtaPair_reference (q : ScaledPoint) (r : HistoryRow) :
    (etaPair hJ (historyPair X0 initial hJ hL hU hi r)).reference q =
      etaD (logHistory X0 initial (referenceAngular L) U r) (q.1.2 * q.2.1, q.2.2) := rfl

theorem activationOnePair_actual {T : ℝ} (hT : T ≠ 0) (κ u : ℝ)
    {η : ℝ} (hη : η ∈ J) :
    (activationOnePair h hX0 initial hJ hL hU hi hcoef).actual ((κ, T), (u, η)) =
      logViewOne h X0 (activatedAngular T κ L)
        (logHistory X0 initial (activatedAngular T κ L) (controlled T κ U)) (T * u, η) := by
  erw [activationOnePair, stockOnePair_actual]
  dsimp only [logViewOne, scaledRadius]
  rw [angularPair_actual_eq hJ hL hT κ u hη,
    historyPair_actual_eq X0 initial hJ hL hU hi hT κ .mass u hη,
    historyPair_actual_eq X0 initial hJ hL hU hi hT κ .angular u hη,
    historyPair_actual_eq X0 initial hJ hL hU hi hT κ .transport u hη,
    historyEtaPair_actual initial hJ hL hU hi hT κ u hη .mass,
    historyEtaPair_actual initial hJ hL hU hi hT κ u hη .angular,
    historyEtaPair_actual initial hJ hL hU hi hT κ u hη .transport]

theorem activationOnePair_reference (q : ScaledPoint) :
    (activationOnePair h hX0 initial hJ hL hU hi hcoef).reference q =
      logViewOne h X0 (referenceAngular L)
        (logHistory X0 initial (referenceAngular L) U) (q.1.2 * q.2.1, q.2.2) := by
  erw [activationOnePair, stockOnePair_reference]
  rfl

theorem activationTwoPair_actual {T : ℝ} (hT : T ≠ 0) (κ u : ℝ)
    {η : ℝ} (hη : η ∈ J) :
    (activationTwoPair h hX0 initial hJ hL hU hi hcoef).actual ((κ, T), (u, η)) =
      logViewTwo h X0 (activatedAngular T κ L) (controlled T κ U)
        (logHistory X0 initial (activatedAngular T κ L) (controlled T κ U)) (T * u, η) := by
  erw [activationTwoPair, stockTwoPair_actual]
  dsimp only [logViewTwo, scaledRadius]
  rw [angularPair_actual_eq hJ hL hT κ u hη,
    historyPair_actual_eq X0 initial hJ hL hU hi hT κ .mass u hη,
    historyPair_actual_eq X0 initial hJ hL hU hi hT κ .energy u hη,
    historyPair_actual_eq X0 initial hJ hL hU hi hT κ .pressure u hη,
    historyEtaPair_actual initial hJ hL hU hi hT κ u hη .mass,
    historyEtaPair_actual initial hJ hL hU hi hT κ u hη .energy,
    historyEtaPair_actual initial hJ hL hU hi hT κ u hη .pressure]
  change stockTwo _ _ _ _ (ActivationBounds.controlledValue U ((κ, T), (u, η))) _ _ _ _ _ _ = _
  rw [ActivationBounds.controlledValue_eq hT κ hJ hU u hη]

theorem activationTwoPair_reference (q : ScaledPoint) :
    (activationTwoPair h hX0 initial hJ hL hU hi hcoef).reference q =
      logViewTwo h X0 (referenceAngular L) U
        (logHistory X0 initial (referenceAngular L) U) (q.1.2 * q.2.1, q.2.2) := by
  erw [activationTwoPair, stockTwoPair_reference]
  rfl

include hX0 hJ hL hU hi hcoef in
/-- Both stock errors have actual smooth factors on a domain containing
the zero-width face. The input hypotheses concern only fields, initial
history values, and the nonzero coordinate coefficient. -/
theorem exists_log_stock_factors :
    ∃ P Q : ScaledPoint → ℝ,
      ContDiffOn ℝ ∞ P (scaledDomain J) ∧ ContDiffOn ℝ ∞ Q (scaledDomain J) ∧
      ∀ T : ℝ, T ≠ 0 → ∀ κ u η : ℝ, η ∈ J →
        logViewOne h X0 (activatedAngular T κ L)
            (logHistory X0 initial (activatedAngular T κ L) (controlled T κ U)) (T * u, η) -
          logViewOne h X0 (referenceAngular L)
            (logHistory X0 initial (referenceAngular L) U) (T * u, η) =
            scaledDistance ((κ, T), (u, η)) * P ((κ, T), (u, η)) ∧
        logViewTwo h X0 (activatedAngular T κ L) (controlled T κ U)
            (logHistory X0 initial (activatedAngular T κ L) (controlled T κ U)) (T * u, η) -
          logViewTwo h X0 (referenceAngular L) U
            (logHistory X0 initial (referenceAngular L) U) (T * u, η) =
            scaledDistance ((κ, T), (u, η)) * Q ((κ, T), (u, η)) := by
  let A := activationOnePair h hX0 initial hJ hL hU hi hcoef
  let B := activationTwoPair h hX0 initial hJ hL hU hi hcoef
  refine ⟨A.factor, B.factor, A.factor_smooth, B.factor_smooth, ?_⟩
  intro T hT κ u η hη
  have hq : ((κ, T), (u, η)) ∈ scaledDomain J := ⟨mem_univ _, mem_univ _, hη⟩
  constructor
  · have he := A.difference ((κ, T), (u, η)) hq
    rwa [activationOnePair_actual h hX0 initial hJ hL hU hi hcoef hT κ u hη,
      activationOnePair_reference h hX0 initial hJ hL hU hi hcoef] at he
  · have he := B.difference ((κ, T), (u, η)) hq
    rwa [activationTwoPair_actual h hX0 initial hJ hL hU hi hcoef hT κ u hη,
      activationTwoPair_reference h hX0 initial hJ hL hU hi hcoef] at he

theorem activationOnePair_zero (κ u : ℝ) {η : ℝ} (hη : η ∈ J) :
    (activationOnePair h hX0 initial hJ hL hU hi hcoef).actual ((κ, 0), (u, η)) =
      (activationOnePair h hX0 initial hJ hL hU hi hcoef).reference ((κ, 0), (u, η)) := by
  have he := (activationOnePair h hX0 initial hJ hL hU hi hcoef).difference
    ((κ, 0), (u, η)) ⟨mem_univ _, mem_univ _, hη⟩
  simpa only [scaledDistance, zero_mul, sub_eq_zero] using he

theorem activationTwoPair_zero (κ u : ℝ) {η : ℝ} (hη : η ∈ J) :
    (activationTwoPair h hX0 initial hJ hL hU hi hcoef).actual ((κ, 0), (u, η)) =
      (activationTwoPair h hX0 initial hJ hL hU hi hcoef).reference ((κ, 0), (u, η)) := by
  have he := (activationTwoPair h hX0 initial hJ hL hU hi hcoef).difference
    ((κ, 0), (u, η)) ⟨mem_univ _, mem_univ _, hη⟩
  simpa only [scaledDistance, zero_mul, sub_eq_zero] using he

include hX0 hJ hL hU hi hcoef in
theorem log_stocks_uniform_jets {K : Set ℝ} (hK : IsCompact K) (hKJ : K ⊆ J)
    (T0 : ℝ) (n : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ T ∈ Ioc (0 : ℝ) T0, ∀ κ ∈ Icc (0 : ℝ) 1,
      ∀ y ∈ Icc (0 : ℝ) T, ∀ η ∈ K,
        |iteratedDeriv n (fun ξ =>
          logViewOne h X0 (activatedAngular T κ L)
              (logHistory X0 initial (activatedAngular T κ L) (controlled T κ U)) (y, ξ) -
            logViewOne h X0 (referenceAngular L)
              (logHistory X0 initial (referenceAngular L) U) (y, ξ)) η| ≤ M * y * activation T κ y ∧
        |iteratedDeriv n (fun ξ =>
          logViewTwo h X0 (activatedAngular T κ L) (controlled T κ U)
              (logHistory X0 initial (activatedAngular T κ L) (controlled T κ U)) (y, ξ) -
            logViewTwo h X0 (referenceAngular L) U
              (logHistory X0 initial (referenceAngular L) U) (y, ξ)) η| ≤ M * y * activation T κ y
                  := by
  obtain ⟨P, Q, hP, hQ, hfactor⟩ := exists_log_stock_factors h hX0 initial hJ hL hU hi hcoef
  obtain ⟨M₁, hM₁, hb₁⟩ := ActivationBounds.width_uniform_jet_bound hJ hK hKJ hP
    (E := fun κ T y η => logViewOne h X0 (activatedAngular T κ L)
      (logHistory X0 initial (activatedAngular T κ L) (controlled T κ U)) (y, η) -
        logViewOne h X0 (referenceAngular L) (logHistory X0 initial (referenceAngular L) U) (y, η))
    (fun κ T hT u η hη => (hfactor T hT.ne' κ u η hη).1) T0 n
  obtain ⟨M₂, hM₂, hb₂⟩ := ActivationBounds.width_uniform_jet_bound hJ hK hKJ hQ
    (E := fun κ T y η => logViewTwo h X0 (activatedAngular T κ L) (controlled T κ U)
      (logHistory X0 initial (activatedAngular T κ L) (controlled T κ U)) (y, η) -
        logViewTwo h X0 (referenceAngular L) U (logHistory X0 initial (referenceAngular L) U) (y,
            η))
    (fun κ T hT u η hη => (hfactor T hT.ne' κ u η hη).2) T0 n
  refine ⟨max M₁ M₂, hM₁.trans (le_max_left _ _), ?_⟩
  intro T hT κ hκ y hy η hη
  have hb1 := hb₁ T hT κ hκ y hy η hη
  have hb2 := hb₂ T hT κ hκ y hy η hη
  have ha : 0 ≤ y * activation T κ y := mul_nonneg hy.1 (activation_nonneg T κ y hκ.2)
  have hinc1 := mul_nonneg (sub_nonneg.mpr (le_max_left M₁ M₂)) ha
  have hinc2 := mul_nonneg (sub_nonneg.mpr (le_max_right M₁ M₂)) ha
  constructor <;> nlinarith

end ConstructedFactors

namespace FromReference

open ReferencePath

variable (N : ReferencePath.Input)

/-- The factors concern the actual recomputed ACT and REF lag histories.
Their common scaled domain contains `T=0`. -/
theorem exists_physical_stock_factors {δ : ℝ} (hδ : 0 < δ) (hδT : 2 * δ < rampLimit)
    (h : ℝ) (hcoef : ∀ η ∈ parameterInterval, NaturalAxisData.L h η ≠ 0)
    (P0 : ℝ → ℝ) (hP0 : ContDiff ℝ ∞ P0) :
    ∃ P Q : ScaledPoint → ℝ,
      ContDiffOn ℝ ∞ P (scaledDomain parameterInterval) ∧
      ContDiffOn ℝ ∞ Q (scaledDomain parameterInterval) ∧
      ∀ T : ℝ, ∀ hT : 0 < T, ∀ κ u η : ℝ, η ∈ parameterInterval →
        profileStockOne (StressActivation.FromReference.histories N hT hδ hδT κ P0 hP0) h
            (radius N.endpoint (T * u), η) -
          profileStockOne (N.histories hδ hδT P0 hP0) h (radius N.endpoint (T * u), η) =
            scaledDistance ((κ, T), (u, η)) * P ((κ, T), (u, η)) ∧
        profileStockTwo (StressActivation.FromReference.histories N hT hδ hδT κ P0 hP0) h
            (radius N.endpoint (T * u), η) -
          profileStockTwo (N.histories hδ hδT P0 hP0) h (radius N.endpoint (T * u), η) =
            scaledDistance ((κ, T), (u, η)) * Q ((κ, T), (u, η)) := by
  obtain ⟨P, Q, hP, hQ, hf⟩ := exists_log_stock_factors h N.endpoint_pos
    (initial N hδ hδT P0 hP0) parameterInterval_open
    (StressActivation.FromReference.refLog_smooth N hδ hδT)
    (StressActivation.FromReference.refAxial_smooth N hδ hδT)
    (initial_smooth N hδ hδT P0 hP0) hcoef
  refine ⟨P, Q, hP, hQ, ?_⟩
  intro T hT κ u η hη
  rw [actual_stockOne_logView N hT hδ hδT κ h P0 hP0 (T * u) hη,
    reference_stockOne_logView N hδ hδT h P0 hP0 (T * u) hη,
    actual_stockTwo_logView N hT hδ hδT κ h P0 hP0 (T * u) hη,
    reference_stockTwo_logView N hδ hδT h P0 hP0 (T * u) hη]
  exact hf T hT.ne' κ u η hη

/-- One constant controls both actual stock errors for every sufficiently
small positive width and all activation parameters, including `κ=0`. -/
theorem physical_stocks_uniform_bound {δ : ℝ} (hδ : 0 < δ) (hδT : 2 * δ < rampLimit)
    (h : ℝ) (hcoef : ∀ η ∈ parameterInterval, NaturalAxisData.L h η ≠ 0)
    (P0 : ℝ → ℝ) (hP0 : ContDiff ℝ ∞ P0) (T0 : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ T : ℝ, ∀ hT : 0 < T, T ≤ T0 → ∀ κ ∈ Icc (0 : ℝ) 1,
      ∀ y ∈ Icc (0 : ℝ) T, ∀ η ∈ Icc (-1 : ℝ) 1,
        |profileStockOne (StressActivation.FromReference.histories N hT hδ hδT κ P0 hP0) h
            (radius N.endpoint y, η) -
          profileStockOne (N.histories hδ hδT P0 hP0) h (radius N.endpoint y, η)| ≤
            M * y * activation T κ y ∧
        |profileStockTwo (StressActivation.FromReference.histories N hT hδ hδT κ P0 hP0) h
            (radius N.endpoint y, η) -
          profileStockTwo (N.histories hδ hδT P0 hP0) h (radius N.endpoint y, η)| ≤
            M * y * activation T κ y := by
  have hKJ : Icc (-1 : ℝ) 1 ⊆ parameterInterval :=
    NaturalAxisCoefficients.original_interval_interior
  obtain ⟨M, hM, hbound⟩ := log_stocks_uniform_jets h N.endpoint_pos
    (initial N hδ hδT P0 hP0) parameterInterval_open
    (StressActivation.FromReference.refLog_smooth N hδ hδT)
    (StressActivation.FromReference.refAxial_smooth N hδ hδT)
    (initial_smooth N hδ hδT P0 hP0) hcoef isCompact_Icc hKJ T0 0
  refine ⟨M, hM, ?_⟩
  intro T hT hTT κ hκ y hy η hη
  rw [actual_stockOne_logView N hT hδ hδT κ h P0 hP0 y (hKJ hη),
    reference_stockOne_logView N hδ hδT h P0 hP0 y (hKJ hη),
    actual_stockTwo_logView N hT hδ hδT κ h P0 hP0 y (hKJ hη),
    reference_stockTwo_logView N hδ hδT h P0 hP0 y (hKJ hη)]
  simpa only [iteratedDeriv_zero] using hbound T ⟨hT, hTT⟩ κ hκ y hy η hη

end FromReference

/-! ## Agreement of the reference stocks with the natural stress-free stocks -/

theorem profileHistory_congr_across {D E : RadialDomain} (P : Profiles D) (Q : Profiles E)
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

theorem profiles_stocks_congr {D E : RadialDomain} (P : Profiles D) (Q : Profiles E)
    (h : ℝ) {J : Set ℝ} (hJ : IsOpen J) {X η : ℝ} (hη : η ∈ J)
    (hp : (X, η) ∈ D.carrier) (hq : (X, η) ∈ E.carrier) (hX : 0 < X)
    (hf : P.f (X, η) = Q.f (X, η)) (hfne : Q.f (X, η) ≠ 0)
    (hu : P.U (X, η) = Q.U (X, η))
    (hH : ∀ r ξ, ξ ∈ J → profileHistory P r (X, ξ) = profileHistory Q r (X, ξ)) :
    profileStockOne P h (X, η) = profileStockOne Q h (X, η) ∧
      profileStockTwo P h (X, η) = profileStockTwo Q h (X, η) := by
  have hD (r : HistoryRow) : parameterPartial (profileHistory P r) (X, η) =
      parameterPartial (profileHistory Q r) (X, η) := by
    have he : (fun ξ => profileHistory P r (X, ξ)) =ᶠ[𝓝 η]
        fun ξ => profileHistory Q r (X, ξ) := by
      filter_upwards [hJ.mem_nhds hη] with ξ hξ
      exact hH r ξ hξ
    exact (parameterPartial_hasDerivAt D (profileHistory_smooth P r) hp).deriv.symm.trans
      (he.deriv_eq.trans (parameterPartial_hasDerivAt E (profileHistory_smooth Q r) hq).deriv)
  constructor
  · rw [profileStockOne_eq P h hp hX.ne' (hf.trans_ne hfne),
      profileStockOne_eq Q h hq hX.ne' hfne]
    change stockOne h X η (P.f (X, η))
      (profileHistory P .mass (X, η)) (parameterPartial (profileHistory P .mass) (X, η))
      (profileHistory P .angular (X, η)) (parameterPartial (profileHistory P .angular) (X, η))
      (profileHistory P .transport (X, η)) (parameterPartial (profileHistory P .transport) (X, η))
          = _
    rw [hf, hH .mass η hη, hH .angular η hη, hH .transport η hη,
      hD .mass, hD .angular, hD .transport]
    rfl
  · rw [profileStockTwo_eq P h hp hX, profileStockTwo_eq Q h hq hX]
    change stockTwo h X η (P.f (X, η)) (P.U (X, η))
      (profileHistory P .mass (X, η)) (parameterPartial (profileHistory P .mass) (X, η))
      (profileHistory P .energy (X, η)) (parameterPartial (profileHistory P .energy) (X, η))
      (profileHistory P .pressure (X, η)) (parameterPartial (profileHistory P .pressure) (X, η)) = _
    rw [hf, hu, hH .mass η hη, hH .energy η hη, hH .pressure η hη,
      hD .mass, hD .energy, hD .pressure]
    rfl

/-- Natural domain, bundling `carrier`, `isOpen`, `scale_mem`. -/
noncomputable def naturalDomain {Λ : ℝ} (hΛ : 0 < Λ) : RadialDomain where
  carrier := NaturalProfile.domain Λ
  isOpen := NaturalProfile.domain_isOpen Λ
  scale_mem := by
    intro p hp t ht
    apply NaturalProfile.domain_segment hΛ hp
    rcases le_total 0 p.1 with hx | hx
    · rw [uIcc_of_le hx]
      exact ⟨mul_nonneg ht.1 hx, mul_le_of_le_one_left hx ht.2⟩
    · rw [uIcc_of_ge hx]
      constructor
      · nlinarith [ht.2]
      · exact mul_nonpos_of_nonneg_of_nonpos ht.1 hx

section NaturalHistories

open NaturalProfile NaturalAxisBridge

variable {h j σ Λ C : ℝ} {P0 : ℝ → ℝ} {d : NaturalAxisCoefficients.AnalyticInputs h j σ P0}
    (F : ProfileFamily d Λ C) (hΛ : 0 < Λ) (hP0 : ContDiff ℝ ∞ P0)

/-- Natural histories, bundling `f`, `U`, `f_smooth`, `U_smooth` and the required compatibility
proofs. -/
noncomputable def naturalHistories : Profiles (naturalDomain hΛ) where
  f := F.f
  U := F.U
  f_smooth := F.natural.f_smooth
  U_smooth := F.natural.U_smooth
  pressure0 := P0
  pressure0_smooth := fun _ _ => hP0.contDiffAt

include hΛ in
theorem radialPartial_natural_field {G : Field} (hG : ContDiffOn ℝ ∞ G (domain Λ))
    {p : Point} (hp : p ∈ domain Λ) : radialPartial G p = partialY G p :=
  (radialPartial_hasDerivAt (naturalDomain hΛ) hG hp).deriv.symm

include hΛ in
theorem parameterPartial_natural_field {G : Field} (hG : ContDiffOn ℝ ∞ G (domain Λ))
    {p : Point} (hp : p ∈ domain Λ) : parameterPartial G p = partialEta G p :=
  (parameterPartial_hasDerivAt (naturalDomain hΛ) hG hp).deriv.symm

theorem naturalHistories_average {p : Point} (hp : p ∈ domain Λ) :
    (naturalHistories F hΛ hP0).Ubar p = F.Ubar p := by
  change average F.U p = F.Ubar p
  by_cases hx : p.1 = 0
  · have he : p = (0, p.2) := Prod.ext hx rfl
    have hu0 : F.U (0, p.2) = NaturalAxisData.U j p.2 := F.natural.U_axis p.2 hp.2
    have hv0 : F.Ubar (0, p.2) = NaturalAxisData.U j p.2 := F.natural.average_axis p.2 hp.2
    rw [he, average_at_axis, hu0, hv0]
  · rw [average_eq_quotient F.U hx]
    change (∫ x in (0 : ℝ)..p.1, F.U (x, p.2)) / p.1 = F.Ubar p
    have hint : p.1 * F.Ubar p = ∫ x in (0 : ℝ)..p.1, F.U (x, p.2) :=
      F.natural.average_integral p hp
    rw [← hint, mul_div_cancel_left₀ _ hx]

theorem naturalHistories_pressure {p : Point} (hp : p ∈ domain Λ) :
    (naturalHistories F hΛ hP0).pressure p = F.Pi p := by
  have he := F.natural.pressure_integral p hp
  change F.Pi p - P0 p.2 = ∫ x in (0 : ℝ)..p.1, F.f (x, p.2) ^ 2 at he
  change P0 p.2 + (∫ x in (0 : ℝ)..p.1, F.f (x, p.2) ^ 2) = F.Pi p
  linarith

theorem naturalHistories_average_derivative {p : Point} (hp : p ∈ domain Λ) :
    parameterPartial (naturalHistories F hΛ hP0).Ubar p = partialEta F.Ubar p := by
  have he : (naturalHistories F hΛ hP0).Ubar =ᶠ[𝓝 p] F.Ubar := by
    filter_upwards [(domain_isOpen Λ).mem_nhds hp] with q hq
    exact naturalHistories_average F hΛ hP0 hq
  change fderiv ℝ _ p (0, 1) = _
  rw [he.fderiv_eq]
  exact parameterPartial_natural_field hΛ F.natural.average_smooth hp

theorem naturalHistories_pressure_derivative {p : Point} (hp : p ∈ domain Λ) :
    parameterPartial (naturalHistories F hΛ hP0).pressure p = partialEta F.Pi p := by
  have he : (naturalHistories F hΛ hP0).pressure =ᶠ[𝓝 p] F.Pi := by
    filter_upwards [(domain_isOpen Λ).mem_nhds hp] with q hq
    exact naturalHistories_pressure F hΛ hP0 hq
  change fderiv ℝ _ p (0, 1) = _
  rw [he.fderiv_eq]
  exact parameterPartial_natural_field hΛ F.natural.pressure_smooth hp

theorem naturalHistories_W {p : Point} (hp : p ∈ domain Λ) :
    (naturalHistories F hΛ hP0).W h p = transportW h F.Ubar p := by
  rw [Profiles.W_formula _ h hp, naturalHistories_average F hΛ hP0 hp,
    naturalHistories_average_derivative F hΛ hP0 hp]
  rfl

theorem naturalHistories_angularSource {p : Point} (hp : p ∈ domain Λ) (hf : F.f p ≠ 0) :
    (naturalHistories F hΛ hP0).angularSource h p =
      (2 * p.1 * F.f p) * NaturalEntrance.Sq h F.f F.U F.Ubar p := by
  let P := naturalHistories F hΛ hP0
  have hrad : radialPartial P.H p = 2 * F.f p + 2 * p.1 * partialY F.f p := by
    have hd := ((hasDerivAt_id p.1).const_mul 2).mul
      (radialPartial_hasDerivAt (naturalDomain hΛ) (F := F.f) F.natural.f_smooth hp)
    have he := (radialPartial_hasDerivAt (naturalDomain hΛ) P.H_smooth hp).unique hd
    simpa only [one_mul, mul_one, id_eq, Prod.eta,
      radialPartial_natural_field hΛ (G := F.f) F.natural.f_smooth hp] using he
  have heta : parameterPartial P.H p = 2 * p.1 * partialEta F.f p := by
    rw [P.parameterPartial_H hp]
    exact congrArg (fun t => 2 * p.1 * t)
      (parameterPartial_natural_field hΛ (G := F.f) F.natural.f_smooth hp)
  change P.angularSource h p = _
  rw [Profiles.angularSource, hrad, heta, naturalHistories_W F hΛ hP0 hp]
  dsimp only [StressAlgebra.angularSource, P, naturalHistories, Profiles.H,
    NaturalEntrance.Sq, transportH, NaturalAxisData.D, NaturalAxisData.d,
    StressAlgebra.axialExponent, StressAlgebra.coordinateFactor]
  field_simp

theorem naturalHistories_axialSource {p : Point} (hp : p ∈ domain Λ) :
    (naturalHistories F hΛ hP0).axialSource h p =
      NaturalEntrance.Sn h F.U F.Ubar F.Pi p := by
  rw [Profiles.axialSource, naturalHistories_W F hΛ hP0 hp,
    naturalHistories_pressure F hΛ hP0 hp, naturalHistories_pressure_derivative F hΛ hP0 hp]
  change StressAlgebra.axialSource h p.2 p.1 (transportW h F.Ubar p) (F.U p)
    (radialPartial F.U p) (parameterPartial F.U p) (F.Pi p) (F.f p ^ 2) (partialEta F.Pi p) = _
  rw [radialPartial_natural_field hΛ (G := F.U) F.natural.U_smooth hp,
    parameterPartial_natural_field hΛ (G := F.U) F.natural.U_smooth hp]
  dsimp only [NaturalEntrance.Sn]
  have hpressure : partialY F.Pi p = F.f p ^ 2 := F.natural.pressure_equation p hp
  rw [hpressure]
  dsimp only [StressAlgebra.axialSource, StressAlgebra.axialExponent,
    StressAlgebra.velocityExponent, StressAlgebra.coordinateFactor,
    NaturalAxisData.A, NaturalAxisData.D, NaturalAxisData.d, transportH]
  ring

theorem naturalHistories_stocks {p : Point} (hp : p ∈ domain Λ) (hX : 0 < p.1)
    (hL : NaturalAxisData.L h p.2 ≠ 0)
    (hf : ∀ x ∈ uIcc (0 : ℝ) p.1, F.f (x, p.2) ≠ 0) :
    profileStockOne (naturalHistories F hΛ hP0) h p = NaturalEntrance.p1 F.f p ∧
      profileStockTwo (naturalHistories F hΛ hP0) h p = NaturalEntrance.p2 F.f F.U p := by
  let P := naturalHistories F hΛ hP0
  have hi : primitive (P.angularSource h) p =
      ∫ x in (0 : ℝ)..p.1, (2 * x * F.f (x, p.2)) * NaturalEntrance.Sq h F.f F.U F.Ubar (x, p.2) :=
          by
    apply intervalIntegral.integral_congr
    intro x hx
    exact naturalHistories_angularSource F hΛ hP0 (domain_segment hΛ hp hx) (hf x hx)
  have hn : primitive (P.axialSource h) p =
      ∫ x in (0 : ℝ)..p.1, NaturalEntrance.Sn h F.U F.Ubar F.Pi (x, p.2) := by
    apply intervalIntegral.integral_congr
    intro x hx
    exact naturalHistories_axialSource F hΛ hP0 (domain_segment hΛ hp hx)
  have hq := NaturalEntrance.p1_eq_scaled_regularAngularLag F.natural hΛ hp hX.ne' hL hf
  have hns : NaturalEntrance.ns F.U p =
      NaturalEntrance.regularAxialLag h F.U F.Ubar F.Pi p / NaturalAxisData.L h p.2 :=
    NaturalEntrance.ns_eq_scaled_regularAxialLag F.natural hΛ hp hX.ne' hL
  constructor
  · change p.1 * (primitive (P.angularSource h) p / (p.1 * (2 * p.1 * F.f p))) /
      NaturalAxisData.L h p.2 = _
    rw [hi]
    exact hq.symm
  · change p.1 * (primitive (P.axialSource h) p / p.1) /
      (NaturalAxisData.L h p.2 * (Real.sqrt (2 * p.1) * F.f p)) = _
    rw [hn]
    dsimp only [NaturalEntrance.p2, NaturalEntrance.angularVelocity]
    rw [hns]
    dsimp only [NaturalEntrance.regularAxialLag]
    ring

/-- On the full natural part of REF, including its endpoint, the actual
integral-defined stocks equal the stress-free derivative coordinates.
The proof transfers all five history rows and their genuine parameter
derivatives from the natural solution. -/
theorem reference_stocks_natural {δ : ℝ} (hδ : 0 < δ)
    (hδT : 2 * δ < ReferencePath.rampLimit)
    (hsmall : NaturalAxisData.SmallParameters h j) (y : ℝ) (hy : y ≤ δ)
    {η : ℝ} (hη : η ∈ Icc (-1 : ℝ) 1) :
    let N := ReferencePath.Input.ofNatural hΛ F
    let p := N.fromLog (y, η)
    profileStockOne (N.histories hδ hδT P0 hP0) h p = NaturalEntrance.p1 F.f p ∧
      profileStockTwo (N.histories hδ hδT P0 hP0) h p = NaturalEntrance.p2 F.f F.U p := by
  let N := ReferencePath.Input.ofNatural hΛ F
  let P := N.histories hδ hδT P0 hP0
  let Q := naturalHistories F hΛ hP0
  let p := N.fromLog (y, η)
  change profileStockOne P h p = NaturalEntrance.p1 F.f p ∧
    profileStockTwo P h p = NaturalEntrance.p2 F.f F.U p
  have hηJ : η ∈ ReferencePath.parameterInterval :=
      NaturalAxisCoefficients.original_interval_interior hη
  have hyT : y < ReferencePath.rampLimit := by linarith
  have hp : p ∈ domain Λ := N.fromLog_mem ⟨hyT, hηJ⟩
  have hpN : p ∈ N.radialDomain.carrier :=
    StressActivation.FromReference.log_radius_mem N y hηJ
  have hX : 0 < p.1 := mul_pos N.endpoint_pos (Real.exp_pos _)
  have hupper : p.1 ≤ N.endpoint * Real.exp δ :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hy) N.endpoint_pos.le
  have hfp : 0 < Q.f p := N.fromLog_f_pos ⟨hyT, hηJ⟩
  have hfields : P.f p = Q.f p := N.refF_eq_natural hδ hδT hηJ hupper
  have hUfields : P.U p = Q.U p := N.refU_eq_natural hδ hδT hηJ hupper
  have hrows : ∀ r ξ, ξ ∈ ReferencePath.parameterInterval →
      profileHistory P r (p.1, ξ) = profileHistory Q r (p.1, ξ) := by
    intro r ξ hξ
    apply profileHistory_congr_across P Q r hX.le
    · cases r <;> rfl
    · intro x hx
      exact N.refF_eq_natural hδ hδT hξ (hx.2.trans hupper)
    · intro x hx
      exact N.refU_eq_natural hδ hδT hξ (hx.2.trans hupper)
  have hagree := profiles_stocks_congr P Q h ReferencePath.parameterInterval_open hηJ
    hpN hp hX hfields hfp.ne' hUfields hrows
  have hY : Λ * p.1 ≤ 41 / 10 := by
    have hs : Λ * p.1 = 4 * Real.exp y := N.fromLog_scaled (y, η)
    have he : Real.exp y < 41 / 40 := by
      simpa only [ReferencePath.rampLimit, Real.exp_log (by norm_num : (0 : ℝ) < 41 / 40)] using
        Real.exp_lt_exp.mpr hyT
    rw [hs]
    linarith
  have hf : ∀ x ∈ uIcc (0 : ℝ) p.1, F.f (x, p.2) ≠ 0 := by
    intro x hx
    have hx' : x ∈ Icc (0 : ℝ) p.1 := by simpa only [uIcc_of_le hX.le] using hx
    exact (F.positive (x, p.2) (domain_segment hΛ hp hx) (mul_nonneg hΛ.le hx'.1)
      ((mul_le_mul_of_nonneg_left hx'.2 hΛ.le).trans hY)).ne'
  have hnat := naturalHistories_stocks F hΛ hP0 hp hX (NaturalAxisData.L_pos hsmall hη).ne' hf
  exact ⟨hagree.1.trans hnat.1, hagree.2.trans hnat.2⟩

end NaturalHistories

end NavierStokes.ActivationStocks

end
