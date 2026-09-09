/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.StressActivation
import Mathlib.Analysis.Calculus.Deriv.Prod

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
