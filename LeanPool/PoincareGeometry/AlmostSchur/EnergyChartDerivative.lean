/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.EnergyL2
public import LeanPool.PoincareGeometry.AlmostSchur.EnergyL2Completion
public import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Coordinate weak derivatives of energy-completion elements

The core map uses actual coordinate derivatives and the intrinsic energy bound
`exists_chart_derivative_L2_bound`. Extension uses Mathlib's
`LinearMap.extendOfNorm`; its norm bound is proved from the actual energy norm,
not assumed. The scalar direction and compact coordinate set are fixed parameters.
The completed integration-by-parts identity follows by continuity of both L²
pairings and density of the actual C¹ core. It does not assume weak regularity.
-/

@[expose] public noncomputable section
open Bundle Set MeasureTheory Filter
open scoped Manifold ContDiff Topology
namespace AlmostSchur

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M] [LindelofSpace M]
  [T2Space M] [CompactSpace M]

local instance : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
  continuousRiemannianBundle_of_contMDiff (I := I)

/-- Coordinate derivatives of core functions are locally square integrable. -/
theorem energyChartDerivative_memLp (c : M) {K : Set E}
    (hK : IsCompact K) (hKt : K ⊆ (extChartAt I c).target)
    (v : E) (f : EnergySpace (I := I) (M := M)) :
    MemLp (fun z => fderiv ℝ (f.val ∘ (extChartAt I c).symm) z v) 2
      ((volume : Measure E).restrict K) := by
  obtain ⟨_, _, h⟩ := exists_chart_derivative_L2_bound (I := I) c hK hKt
  exact (h f.val f.property.1 v).choose

/-- Core coordinate functions are differentiable at every chart-target point. -/
theorem energyChartDerivative_differentiableAt (c : M)
    (f : EnergySpace (I := I) (M := M)) {z : E} (hz : z ∈ (extChartAt I c).target) :
    DifferentiableAt ℝ (f.val ∘ (extChartAt I c).symm) z :=
  ((contDiffOn_chart_comp c f.val f.property.1.contMDiffOn).differentiableOn
    (by norm_num)).differentiableAt ((isOpen_extChartAt_target c).mem_nhds hz)

/-- Actual directional coordinate differentiation, as a linear map on the energy core. -/
def energyChartDerivativeLinear (c : M) {K : Set E}
    (hK : IsCompact K) (hKt : K ⊆ (extChartAt I c).target) (v : E) :
    EnergySpace (I := I) (M := M) →ₗ[ℝ] Lp ℝ 2 ((volume : Measure E).restrict K) where
  toFun f := (energyChartDerivative_memLp c hK hKt v f).toLp _
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(energyChartDerivative_memLp c hK hKt v (f + g)).coeFn_toLp,
      (energyChartDerivative_memLp c hK hKt v f).coeFn_toLp,
      (energyChartDerivative_memLp c hK hKt v g).coeFn_toLp,
      Lp.coeFn_add ((energyChartDerivative_memLp c hK hKt v f).toLp _)
        ((energyChartDerivative_memLp c hK hKt v g).toLp _),
      ae_restrict_mem hK.measurableSet] with z hfg hf hg hadd hz
    rw [hfg, hadd]
    change fderiv ℝ (fun y => f.val ((extChartAt I c).symm y) +
      g.val ((extChartAt I c).symm y)) z v = _ + _
    rw [hf, hg]
    simpa only [Function.comp_apply, add_apply] using
      congrArg (fun T : E →L[ℝ] ℝ => T v)
        (fderiv_fun_add (energyChartDerivative_differentiableAt c f (hKt hz))
          (energyChartDerivative_differentiableAt c g (hKt hz)))
  map_smul' a f := by
    apply Lp.ext
    filter_upwards [(energyChartDerivative_memLp c hK hKt v (a • f)).coeFn_toLp,
      (energyChartDerivative_memLp c hK hKt v f).coeFn_toLp,
      Lp.coeFn_smul a ((energyChartDerivative_memLp c hK hKt v f).toLp _),
      ae_restrict_mem hK.measurableSet] with z haf hf hsmul hz
    simp only [RingHom.id_apply]
    rw [haf, hsmul]
    change fderiv ℝ (fun y => a • f.val ((extChartAt I c).symm y)) z v = a • _
    rw [hf]
    simpa only [Function.comp_apply, smul_apply] using
      congrArg (fun T : E →L[ℝ] ℝ => T v)
        (fderiv_fun_const_smul (energyChartDerivative_differentiableAt c f (hKt hz)) a)

/-- Representative identity for the core derivative map. -/
theorem energyChartDerivativeLinear_ae_eq (c : M) {K : Set E}
    (hK : IsCompact K) (hKt : K ⊆ (extChartAt I c).target) (v : E)
    (f : EnergySpace (I := I) (M := M)) :
    (energyChartDerivativeLinear c hK hKt v f : E → ℝ) =ᵐ[(volume : Measure E).restrict K]
      (fun z => fderiv ℝ (f.val ∘ (extChartAt I c).symm) z v) :=
  (energyChartDerivative_memLp c hK hKt v f).coeFn_toLp

variable [PreconnectedSpace M]

/-- One chart constant bounds the core maps in every direction by intrinsic energy. -/
theorem exists_energyChartDerivativeLinear_bound (c : M) {K : Set E}
    (hK : IsCompact K) (hKt : K ⊆ (extChartAt I c).target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (v : E) (f : EnergySpace (I := I) (M := M)),
      ‖energyChartDerivativeLinear c hK hKt v f‖ ≤ C * ‖v‖ * ‖f‖ := by
  obtain ⟨C, hC, hb⟩ := exists_chart_derivative_L2_bound (I := I) c hK hKt
  refine ⟨C, hC, fun v f => ?_⟩
  obtain ⟨hd, hbound⟩ := hb f.val f.property.1 v
  simpa only [energyChartDerivativeLinear, LinearMap.coe_mk, AddHom.coe_mk, energySpace_norm]
    using hbound

/-- The bounded directional coordinate derivative extends to the Hilbert completion. -/
def energyChartDerivative (c : M) {K : Set E}
    (hK : IsCompact K) (hKt : K ⊆ (extChartAt I c).target) (v : E) :
    EnergyCompletion (I := I) (M := M) →L[ℝ] Lp ℝ 2 ((volume : Measure E).restrict K) :=
  (energyChartDerivativeLinear c hK hKt v).extendOfNorm
    (energyToCompletion (I := I) (M := M)).toLinearMap

/-- Extension agrees with actual coordinate differentiation on the dense C¹ core. -/
theorem energyChartDerivative_energyToCompletion (c : M) {K : Set E}
    (hK : IsCompact K) (hKt : K ⊆ (extChartAt I c).target) (v : E)
    (f : EnergySpace (I := I) (M := M)) :
    energyChartDerivative c hK hKt v (energyToCompletion f) =
      energyChartDerivativeLinear c hK hKt v f := by
  obtain ⟨C, _, hC⟩ := exists_energyChartDerivativeLinear_bound c hK hKt
  apply LinearMap.extendOfNorm_eq (denseRange_energyToCompletion (I := I) (M := M))
  refine ⟨C * ‖v‖, fun g => ?_⟩
  simpa only [LinearIsometry.coe_toLinearMap, LinearIsometry.norm_map] using hC v g

/-- The same chart constant bounds the completed derivative in every direction. -/
theorem exists_energyChartDerivative_bound (c : M) {K : Set E}
    (hK : IsCompact K) (hKt : K ⊆ (extChartAt I c).target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (v : E) (u : EnergyCompletion (I := I) (M := M)),
      ‖energyChartDerivative c hK hKt v u‖ ≤ C * ‖v‖ * ‖u‖ := by
  obtain ⟨C, hC0, hC⟩ := exists_energyChartDerivativeLinear_bound c hK hKt
  refine ⟨C, hC0, fun v u => ?_⟩
  apply LinearMap.norm_extendOfNorm_apply_le (denseRange_energyToCompletion (I := I) (M := M))
  intro f
  simpa only [LinearIsometry.coe_toLinearMap, LinearIsometry.norm_map] using hC v f

/-- The completed coordinate derivative is a genuine weak derivative of the
actual L² realization. Both pairings are passed through the dense core. The test
may be C¹, and only its topological support must lie in the compact coordinate set. -/
theorem setIntegral_energyChartDerivative (c : M) {K : Set E}
    (hK : IsCompact K) (hKt : K ⊆ (extChartAt I c).target) (v : E)
    (u : EnergyCompletion (I := I) (M := M))
    (φ : E → ℝ) (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ)
    (hφK : tsupport φ ⊆ K) :
    (∫ z in K, energyCompletionToL2 u ((extChartAt I c).symm z) * fderiv ℝ φ z v) =
      -(∫ z in K, energyChartDerivative c hK hKt v u z * φ z) := by
  let μ := (volume : Measure E).restrict K
  obtain ⟨_, _, T, _, hTa⟩ := exists_chartL2Pullback (I := I) c hK hKt
  let P : EnergyCompletion (I := I) (M := M) →L[ℝ] Lp ℝ 2 μ :=
    T.comp (energyCompletionToL2 (I := I) (M := M))
  let D := energyChartDerivative c hK hKt v
  have hφLp : MemLp φ 2 μ :=
    (hφ.continuous.memLp_of_hasCompactSupport hcφ).mono_measure Measure.restrict_le_self
  have hdφLp : MemLp (fun z => fderiv ℝ φ z v) 2 μ :=
    (((hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hcφ.fderiv_apply ℝ v)).mono_measure Measure.restrict_le_self
  let Φ := hφLp.toLp φ
  let dΦ := hdφLp.toLp (fun z => fderiv ℝ φ z v)
  have hpair (F G : Lp ℝ 2 μ) : inner ℝ F G = ∫ z, F z * G z ∂μ := by
    simp only [L2.inner_def, RCLike.inner_apply, conj_trivial, mul_comm]
  have hl (F : E → ℝ) :
      (∫ z in K, F z * fderiv ℝ φ z v) = ∫ z, F z * fderiv ℝ φ z v := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    have hz' : z ∉ tsupport (fun z => fderiv ℝ φ z v) :=
      fun hh => hz (hφK (tsupport_fderiv_apply_subset ℝ v hh))
    rw [image_eq_zero_of_notMem_tsupport hz', mul_zero]
  have hr (F : E → ℝ) : (∫ z in K, F z * φ z) = ∫ z, F z * φ z := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    rw [image_eq_zero_of_notMem_tsupport (fun hh => hz (hφK hh)), mul_zero]
  have hidentity : ∀ w : EnergyCompletion (I := I) (M := M),
      inner ℝ (P w) dΦ = -inner ℝ (D w) Φ := by
    intro w
    refine (denseRange_energyToCompletion (I := I) (M := M)).induction_on
      (p := fun w => inner ℝ (P w) dΦ = -inner ℝ (D w) Φ) w ?_ ?_
    · exact isClosed_eq (P.continuous.inner continuous_const)
        (D.continuous.inner continuous_const).neg
    · intro f
      have hP : (P (energyToCompletion f) : E → ℝ) =ᵐ[μ]
          f.val ∘ (extChartAt I c).symm :=
        (hTa _).trans (ae_eq_comp_chart_symm (energyCompletionToL2_core_ae_eq f) c hK hKt)
      have hD : (D (energyToCompletion f) : E → ℝ) =ᵐ[μ]
          (fun z => fderiv ℝ (f.val ∘ (extChartAt I c).symm) z v) := by
        dsimp only [D]
        rw [energyChartDerivative_energyToCompletion]
        exact energyChartDerivativeLinear_ae_eq c hK hKt v f
      rw [hpair, hpair]
      have hleft : (∫ z, P (energyToCompletion f) z * dΦ z ∂μ) =
          ∫ z, (f.val ∘ (extChartAt I c).symm) z * fderiv ℝ φ z v := by
        rw [← hl]
        apply integral_congr_ae
        filter_upwards [hP, hdφLp.coeFn_toLp] with z hz hz'
        rw [hz, hz']
      have hright : (∫ z, D (energyToCompletion f) z * Φ z ∂μ) =
          ∫ z, fderiv ℝ (f.val ∘ (extChartAt I c).symm) z v * φ z := by
        rw [← hr]
        apply integral_congr_ae
        filter_upwards [hD, hφLp.coeFn_toLp] with z hz hz'
        rw [hz, hz']
      rw [hleft, hright]
      exact integral_mul_fderiv_openDomain (isOpen_extChartAt_target c)
        _ φ (contDiffOn_chart_comp c f.val f.property.1.contMDiffOn) hφ hcφ
        (hφK.trans hKt) v
  have hleft : inner ℝ (P u) dΦ =
      ∫ z in K, energyCompletionToL2 u ((extChartAt I c).symm z) * fderiv ℝ φ z v := by
    rw [hpair]
    apply integral_congr_ae
    filter_upwards [hTa (energyCompletionToL2 u), hdφLp.coeFn_toLp] with z hz hz'
    change T (energyCompletionToL2 u) z * dΦ z = _
    rw [hz, hz']
    rfl
  have hright : inner ℝ (D u) Φ = ∫ z in K, D u z * φ z := by
    rw [hpair]
    apply integral_congr_ae
    filter_upwards [hφLp.coeFn_toLp] with z hz
    rw [hz]
  rw [← hleft, ← hright]
  exact hidentity u

/-- Whole-space test integral form of the completed weak derivative identity.
The derivative class on the right is integrated only over its defining compact set. -/
theorem integral_energyCompletionToL2_mul_fderiv (c : M) {K : Set E}
    (hK : IsCompact K) (hKt : K ⊆ (extChartAt I c).target) (v : E)
    (u : EnergyCompletion (I := I) (M := M))
    (φ : E → ℝ) (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ)
    (hφK : tsupport φ ⊆ K) :
    (∫ z, energyCompletionToL2 u ((extChartAt I c).symm z) * fderiv ℝ φ z v) =
      -(∫ z in K, energyChartDerivative c hK hKt v u z * φ z) := by
  rw [← setIntegral_energyChartDerivative c hK hKt v u φ hφ hcφ hφK]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro z hz
  have hz' : z ∉ tsupport (fun z => fderiv ℝ φ z v) :=
    fun hh => hz (hφK (tsupport_fderiv_apply_subset ℝ v hh))
  rw [image_eq_zero_of_notMem_tsupport hz', mul_zero]

end AlmostSchur
