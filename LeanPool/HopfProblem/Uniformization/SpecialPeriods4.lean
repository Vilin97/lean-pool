/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.Threefold.SpecialPeriods4
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods1
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods2
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods3
import all LeanPool.HopfProblem.Threefold.SpecialPeriods4

/-!
# Hopf problem: uniformization · special periods 4

Supporting definitions and proofs for this stage of the six-sphere construction.
-/


open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

noncomputable section

namespace Mathoverflow1973

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

private instance SpecialPeriods.modularRegularBase_pathConnected :
    PathConnectedSpace ModularRegularBase :=
  ModularCoverTools.complex_compl_pair_pathConnected 0 1728

private theorem SpecialPeriods.modularRegularValues_dense : Dense modularRegularValues :=
  ModularCoverTools.complex_compl_pair_dense 0 1728

private theorem SpecialPeriods.modularRegularQuotientJ_exists_subsingleton_fibre :
    ∃ c : ModularRegularBase, Subsingleton (modularRegularQuotientJ ⁻¹' { c }) := by
  obtain ⟨R, hR, hlarge⟩ := modularQuotientJ_unique_fibre_at_large_values
  let r : ℝ := Max.max R 1728 + 1
  have hrpos : 0 < r := by dsimp [r]; linarith [le_max_right R (1728 : ℝ)]
  have hrbig : 1728 < r := by dsimp [r]; linarith [le_max_right R (1728 : ℝ)]
  have hrR : R < r := by dsimp [r]; linarith [le_max_left R (1728 : ℝ)]
  let c : ModularRegularBase :=
    ⟨(r : ℂ),
      (mem_modularRegularValues _).mpr ⟨by exact_mod_cast hrpos.ne', by exact_mod_cast hrbig.ne'⟩⟩
  have hRc : R < ‖(c : ℂ)‖ := by
    change R < ‖(r : ℂ)‖
    simpa only [Complex.norm_real, Real.norm_of_nonneg hrpos.le] using hrR
  obtain ⟨x, hx, hunique⟩ := hlarge c hRc
  refine ⟨c, ⟨?_⟩⟩
  intro u v
  apply Subtype.ext
  apply Subtype.ext
  have hu : modularQuotientJ (u.1 : ModularOrbitSpace) = (c : ℂ) :=
    congrArg Subtype.val (show modularRegularQuotientJ u.1 = c from u.2)
  have hv : modularQuotientJ (v.1 : ModularOrbitSpace) = (c : ℂ) :=
    congrArg Subtype.val (show modularRegularQuotientJ v.1 = c from v.2)
  exact (hunique _ hu).trans (hunique _ hv).symm

private theorem SpecialPeriods.modularRegularQuotientJ_injective :
    Function.Injective modularRegularQuotientJ := by
  obtain ⟨c, hc⟩ := modularRegularQuotientJ_exists_subsingleton_fibre
  exact
    ModularCoverTools.injective_of_covering_singleton_fibre modularRegularQuotientJ_isCoveringMap
      c hc

private theorem SpecialPeriods.modularQuotientJ_injOn_regular :
    Set.InjOn modularQuotientJ (modularQuotientJ ⁻¹' modularRegularValues) := by
  intro x hx y hy hxy
  have h : (⟨x, hx⟩ : ModularRegularOrbitSpace) = ⟨y, hy⟩ :=
    modularRegularQuotientJ_injective (Subtype.ext hxy)
  exact congrArg Subtype.val h

private theorem SpecialPeriods.modularQuotientJ_injective : Function.Injective modularQuotientJ :=
  ModularCoverTools.injective_of_open_dense modularQuotientJ_isOpenMap modularRegularValues_dense
    modularQuotientJ_injOn_regular

private theorem SpecialPeriods.modularJ_eq_iff_mem_orbit (z w : ℍ) :
    modularJ z = modularJ w ↔ z ∈ MulAction.orbit SL(2, ℤ) w := by
  constructor
  · intro h
    exact Quotient.exact (modularQuotientJ_injective h)
  · intro h
    exact congrArg modularQuotientJ (Quotient.sound h)

private theorem SpecialPeriods.modularJ_eq_iff_exists_smul (z w : ℍ) :
    modularJ z = modularJ w ↔ ∃ γ : SL(2, ℤ), γ • w = z :=
  modularJ_eq_iff_mem_orbit z w

private theorem SpecialPeriods.exists_analytic_unit_root {g : ℂ → ℂ} {a : ℂ} {m : ℕ}
    (hg : AnalyticAt ℂ g a) (hga : g a ≠ 0) (hm : 0 < m) :
    ∃ r : ℂ → ℂ, AnalyticAt ℂ r a ∧ r a ≠ 0 ∧ ∀ᶠ w in 𝓝 a, r w ^ m = g w := by
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (g a) hm
  have hb0 : b ≠ 0 := by
    intro h
    apply hga
    rw [← hb, h, zero_pow hm.ne']
  have hpow : AnalyticAt ℂ (fun w : ℂ => w ^ m) b := analyticAt_id.pow m
  have hderiv : deriv (fun w : ℂ => w ^ m) b ≠ 0 := by
    rw [deriv_pow_field]
    exact mul_ne_zero (Nat.cast_ne_zero.mpr hm.ne') (pow_ne_zero _ hb0)
  let R : ℂ → ℂ := hpow.hasStrictDerivAt.localInverse (fun w : ℂ => w ^ m) _ b hderiv
  have hRa : AnalyticAt ℂ R (g a) := by
    rw [← hb]
    exact hpow.analyticAt_localInverse hderiv
  have hRb : R (g a) = b := by
    rw [← hb]
    exact HasStrictFDerivAt.localInverse_apply_image ..
  have hRpow : ∀ᶠ y in 𝓝 (g a), R y ^ m = y := by
    rw [← hb]
    exact hpow.hasStrictDerivAt.eventually_right_inverse hderiv
  refine ⟨fun w => R (g w), hRa.comp hg, ?_, ?_⟩
  · change R (g a) ≠ 0
    rw [hRb]
    exact hb0
  · exact hg.continuousAt.tendsto.eventually hRpow

private theorem SpecialPeriods.exists_analytic_power_coordinate {F : ℂ → ℂ} {a : ℂ} {m : ℕ}
    (hF : AnalyticAt ℂ F a) (horder : analyticOrderAt F a = m) (hm : 0 < m) :
    ∃ h : ℂ → ℂ, AnalyticAt ℂ h a ∧ h a = 0 ∧ deriv h a ≠ 0 ∧ ∀ᶠ w in 𝓝 a, F w = h w ^ m := by
  obtain ⟨g, hg, hga, hFg⟩ := hF.analyticOrderAt_eq_natCast.mp horder
  obtain ⟨r, hr, hra, hrpow⟩ := exists_analytic_unit_root hg hga hm
  let h : ℂ → ℂ := fun w => (w - a) * r w
  have hh : AnalyticAt ℂ h a := (analyticAt_id.sub analyticAt_const).mul hr
  have hderiv : deriv h a = r a := by
    simpa only [h, id_eq, sub_self, MulZeroClass.zero_mul, one_mul, add_zero] using
      (((hasDerivAt_id a).sub_const a).fun_mul hr.differentiableAt.hasDerivAt).deriv
  refine ⟨h, hh, by simp [h], hderiv ▸ hra, ?_⟩
  filter_upwards [hFg, hrpow] with w hw hwr
  rw [hw, smul_eq_mul, ← hwr, ← mul_pow]

private theorem
    SpecialPeriods.exists_analytic_power_chart_in {F : ℂ → ℂ} {a : ℂ} {m : ℕ} {U : Set ℂ}
    (hF : AnalyticAt ℂ F a) (horder : analyticOrderAt F a = m) (hm : 0 < m) (hU : U ∈ 𝓝 a) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ,
      a ∈ e.source ∧
        e a = 0 ∧
          e.source ⊆ U ∧
            AnalyticOnNhd ℂ e e.source ∧
              AnalyticOnNhd ℂ e.symm e.target ∧ ∀ w ∈ e.source, F w = e w ^ m := by
  obtain ⟨h, hh, hha, hdh, hpower⟩ := exists_analytic_power_coordinate hF horder hm
  obtain ⟨e₀, hae₀, he₀, hea, hei⟩ := exists_analytic_openPartialHomeomorph hh hdh
  have hboth : ∀ᶠ w in 𝓝 a, F w = h w ^ m ∧ w ∈ U := hpower.and hU
  obtain ⟨V, hV, hVo, haV⟩ := eventually_nhds_iff.mp hboth
  let e : OpenPartialHomeomorph ℂ ℂ := e₀.restrOpen V hVo
  refine ⟨e, ⟨hae₀, haV⟩, ?_, ?_, ?_, ?_, ?_⟩
  · exact (he₀ a).trans hha
  · intro w hw
    exact (hV w hw.2).2
  · intro w hw
    exact hea w hw.1
  · intro w hw
    exact hei w hw.1
  · intro w hw
    exact (hV w hw.2).1.trans (congrArg (· ^ m) (he₀ w).symm)

private theorem SpecialPeriods.exists_analytic_power_chart {F : ℂ → ℂ} {a : ℂ} {m : ℕ}
    (hF : AnalyticAt ℂ F a) (horder : analyticOrderAt F a = m) (hm : 0 < m) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ,
      a ∈ e.source ∧
        e a = 0 ∧
          AnalyticOnNhd ℂ e e.source ∧
            AnalyticOnNhd ℂ e.symm e.target ∧ ∀ w ∈ e.source, F w = e w ^ m := by
  obtain ⟨e, ha, he, _, hf, hi, hp⟩ :=
    exists_analytic_power_chart_in hF horder hm (Filter.univ_mem : Set.univ ∈ 𝓝 a)
  exact ⟨e, ha, he, hf, hi, hp⟩

private theorem
    SpecialPeriods.power_chart_inverse_identity (e : OpenPartialHomeomorph ℂ ℂ) {F : ℂ → ℂ}
    {m : ℕ} (hp : ∀ w ∈ e.source, F w = e w ^ m) : ∀ w ∈ e.target, F (e.symm w) = w ^ m := by
  intro w hw
  rw [hp _ (e.map_target hw), e.right_inv hw]

private theorem SpecialPeriods.modularJ_cubic_chart (z : ℍ) (hz : modularJ z = 0) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ,
      (z : ℂ) ∈ e.source ∧
        e z = 0 ∧
          e.source ⊆ UpperHalfPlane.upperHalfPlaneSet ∧
            AnalyticOnNhd ℂ e e.source ∧
              AnalyticOnNhd ℂ e.symm e.target ∧
                (∀ w ∈ e.source, modularJ (UpperHalfPlane.ofComplex w) = e w ^ 3) ∧
                  (∀ w ∈ e.target, modularJ (UpperHalfPlane.ofComplex (e.symm w)) = w ^ 3) := by
  obtain ⟨e, ha, he, hU, hf, hi, hp⟩ :=
    exists_analytic_power_chart_in (modularJ_analyticAt z)
      (analyticOrderAt_modularJ_of_eq_zero z hz) (by decide : 0 < 3)
      (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)
  exact ⟨e, ha, he, hU, hf, hi, hp, power_chart_inverse_identity e hp⟩

private theorem SpecialPeriods.modularJ_quadratic_chart (z : ℍ) (hz : modularJ z = 1728) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ,
      (z : ℂ) ∈ e.source ∧
        e z = 0 ∧
          e.source ⊆ UpperHalfPlane.upperHalfPlaneSet ∧
            AnalyticOnNhd ℂ e e.source ∧
              AnalyticOnNhd ℂ e.symm e.target ∧
                (∀ w ∈ e.source, modularJ (UpperHalfPlane.ofComplex w) - 1728 = e w ^ 2) ∧
                  (∀ w ∈ e.target,
                    modularJ (UpperHalfPlane.ofComplex (e.symm w)) - 1728 = w ^ 2) := by
  obtain ⟨e, ha, he, hU, hf, hi, hp⟩ :=
    exists_analytic_power_chart_in ((modularJ_analyticAt z).sub analyticAt_const)
      (analyticOrderAt_modularJ_sub_1728_of_eq z hz) (by decide : 0 < 2)
      (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)
  exact ⟨e, ha, he, hU, hf, hi, hp, power_chart_inverse_identity e hp⟩

private theorem SpecialPeriods.modularJ_rhoPoint_cubic_chart :
    ∃ e : OpenPartialHomeomorph ℂ ℂ,
      rho ∈ e.source ∧
        e rho = 0 ∧
          e.source ⊆ UpperHalfPlane.upperHalfPlaneSet ∧
            AnalyticOnNhd ℂ e e.source ∧
              AnalyticOnNhd ℂ e.symm e.target ∧
                (∀ w ∈ e.source, modularJ (UpperHalfPlane.ofComplex w) = e w ^ 3) ∧
                  (∀ w ∈ e.target, modularJ (UpperHalfPlane.ofComplex (e.symm w)) = w ^ 3) :=
  modularJ_cubic_chart rhoPoint modularJ_rhoPoint

private theorem SpecialPeriods.modularJ_I_quadratic_chart :
    ∃ e : OpenPartialHomeomorph ℂ ℂ,
      Complex.I ∈ e.source ∧
        e Complex.I = 0 ∧
          e.source ⊆ UpperHalfPlane.upperHalfPlaneSet ∧
            AnalyticOnNhd ℂ e e.source ∧
              AnalyticOnNhd ℂ e.symm e.target ∧
                (∀ w ∈ e.source, modularJ (UpperHalfPlane.ofComplex w) - 1728 = e w ^ 2) ∧
                  (∀ w ∈ e.target,
                    modularJ (UpperHalfPlane.ofComplex (e.symm w)) - 1728 = w ^ 2) :=
  modularJ_quadratic_chart UpperHalfPlane.I modularJ_I

private theorem
    SpecialPeriods.analytic_chart_inverse_order_one (e : OpenPartialHomeomorph ℂ ℂ) {a : ℂ}
    (ha : a ∈ e.source) (he : e a = 0) (hf : AnalyticOnNhd ℂ e e.source)
    (hi : AnalyticOnNhd ℂ e.symm e.target) : analyticOrderAt (fun z : ℂ => e.symm z - a) 0 = 1 := by
  have ht : (0 : ℂ) ∈ e.target := he ▸ e.map_source ha
  have hia : e.symm 0 = a := by rw [← he, e.left_inv ha]
  have hfi : AnalyticAt ℂ e (e.symm 0) := hia ▸ hf a ha
  have hii := hi 0 ht
  have hc := hfi.differentiableAt.hasDerivAt.comp 0 hii.differentiableAt.hasDerivAt
  have hnear : ∀ᶠ z : ℂ in 𝓝 0, z ∈ e.target := e.open_target.mem_nhds ht
  have heq : (fun z : ℂ => e (e.symm z)) =ᶠ[𝓝 0] id := hnear.mono fun z hz => e.right_inv hz
  have hm : deriv e (e.symm 0) * deriv e.symm 0 = 1 :=
    (hc.congr_of_eventuallyEq heq.symm).unique (hasDerivAt_id 0)
  have hne : deriv e.symm 0 ≠ 0 := by
    intro h
    rw [h, MulZeroClass.mul_zero] at hm
    exact zero_ne_one hm
  simpa only [hia] using hii.analyticOrderAt_sub_eq_one_of_deriv_ne_zero hne

private theorem
    SpecialPeriods.analytic_chart_inverse_power_order (e : OpenPartialHomeomorph ℂ ℂ) {a : ℂ}
    (ha : a ∈ e.source) (he : e a = 0) (hf : AnalyticOnNhd ℂ e e.source)
    (hi : AnalyticOnNhd ℂ e.symm e.target) (c : ℂ) (hc : c ≠ 0) (k : ℕ) (hk : 0 < k) :
    analyticOrderAt (fun z : ℂ => e.symm (c * z ^ k) - a) 0 = (k : ℕ∞) := by
  have ht : (0 : ℂ) ∈ e.target := he ▸ e.map_source ha
  have hg : AnalyticAt ℂ (fun z : ℂ => c * z ^ k) 0 := by fun_prop
  have hg0 : c * (0 : ℂ) ^ k = 0 := by simp [hk.ne']
  have hi0 : AnalyticAt ℂ (fun z : ℂ => e.symm z - a) (c * (0 : ℂ) ^ k) := by
    rw [hg0]
    exact (hi 0 ht).sub analyticAt_const
  have horder : analyticOrderAt (fun z : ℂ => c * z ^ k) 0 = (k : ℕ∞) := by
    rw [hg.analyticOrderAt_eq_natCast]
    refine ⟨fun _ => c, analyticAt_const, hc, ?_⟩
    exact Filter.Eventually.of_forall fun z => by simp [mul_comm]
  have hcomp := hi0.analyticOrderAt_comp (g := fun z : ℂ => c * z ^ k) (z₀ := 0) hg
  simpa only [Function.comp_def, hg0, sub_zero, analytic_chart_inverse_order_one e ha he hf hi,
    horder, one_mul] using hcomp

private theorem SpecialPeriods.analytic_chart_deriv_ne_zero (e : OpenPartialHomeomorph ℂ ℂ) {a : ℂ}
    (ha : a ∈ e.source) (hf : AnalyticOnNhd ℂ e e.source) (hi : AnalyticOnNhd ℂ e.symm e.target) :
    deriv e a ≠ 0 := by
  have hii := hi (e a) (e.map_source ha)
  have hc := hii.differentiableAt.hasDerivAt.comp a (hf a ha).differentiableAt.hasDerivAt
  have hnear : ∀ᶠ z : ℂ in 𝓝 a, z ∈ e.source := e.open_source.mem_nhds ha
  have heq : (fun z : ℂ => e.symm (e z)) =ᶠ[𝓝 a] id := hnear.mono fun z hz => e.left_inv hz
  have hm : deriv e.symm (e a) * deriv e a = 1 :=
    (hc.congr_of_eventuallyEq heq.symm).unique (hasDerivAt_id a)
  intro h
  rw [h, MulZeroClass.mul_zero] at hm
  exact zero_ne_one hm

private def SpecialPeriods.modularRhoAction (w : ℂ) : ℂ :=
  (w - 1) / w

private def SpecialPeriods.modularIAction (w : ℂ) : ℂ :=
  -1 / w

private theorem SpecialPeriods.modularRhoAction_coe (z : ℍ) :
    modularRhoAction z = (((ModularGroup.T * ModularGroup.S) • z : ℍ) : ℂ) := by
  rw [SemigroupAction.mul_smul, UpperHalfPlane.modular_T_smul, UpperHalfPlane.modular_S_smul]
  simp only [modularRhoAction, UpperHalfPlane.coe_vadd, Complex.ofReal_one, inv_neg]
  field_simp [z.ne_zero]
  ring

private theorem SpecialPeriods.modularIAction_coe (z : ℍ) :
    modularIAction z = ((ModularGroup.S • z : ℍ) : ℂ) := by
  rw [UpperHalfPlane.modular_S_smul]
  simp [modularIAction, inv_neg, div_eq_mul_inv]

private theorem SpecialPeriods.modularRhoAction_deriv_rho : deriv modularRhoAction rho = -rho := by
  have h := ((hasDerivAt_id rho).sub_const 1).div (hasDerivAt_id rho) rho_ne_zero
  change HasDerivAt modularRhoAction _ rho at h
  rw [h.deriv]
  simp only [id_eq, one_mul, mul_one]
  field_simp [rho_ne_zero]
  linear_combination rho_cube

private theorem SpecialPeriods.modularSL_holomorphic (g : SL(2, ℤ)) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun z : ℍ => g • z) :=
  UpperHalfPlane.contMDiff_smul (g := Matrix.SpecialLinearGroup.mapGL ℝ g) (by simp)

private theorem SpecialPeriods.upperHalfPlane_holomorphic_eq_of_eventuallyEq {f g : ℍ → ℍ}
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g) {a : ℍ} (he : f =ᶠ[𝓝 a] g) :
    f = g := by
  have hfc : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z => (f z : ℂ)) :=
    (UpperHalfPlane.contMDiff_coe.comp hf).mdifferentiable (by simp)
  have hgc : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z => (g z : ℂ)) :=
    (UpperHalfPlane.contMDiff_coe.comp hg).mdifferentiable (by simp)
  have hz : ∀ᶠ z in 𝓝[≠] a, (f z : ℂ) - (g z : ℂ) = 0 :=
    (he.mono fun z hz => by rw [hz, sub_self]).filter_mono nhdsWithin_le_nhds
  have hzero := UpperHalfPlane.eq_zero_of_frequently (hfc.sub hgc) hz.frequently
  funext z
  apply UpperHalfPlane.ext
  exact sub_eq_zero.mp (congrFun hzero z)

private theorem SpecialPeriods.realSL_action_identity_of_two_fixed (g : SL(2, ℝ)) {a b : ℍ}
    (ha : g • a = a) (hb : g • b = b) (hab : a ≠ b) : ∀ z : ℍ, g • z = z := by
  have hc : Triangle.cayleyCoordinate a b ≠ 0 := by
    apply div_ne_zero _ (Triangle.sub_conj_ne_zero a b)
    apply sub_ne_zero.mpr
    intro h
    exact hab (UpperHalfPlane.ext h).symm
  have hm : Triangle.slMultiplier g a = 1 := by
    have h := Triangle.cayleyCoordinate_smul g a b ha
    rw [hb] at h
    exact mul_right_cancel₀ hc (by simpa only [one_mul] using h.symm)
  intro z
  apply (Triangle.cayleyBiholomorph a).injective
  apply Subtype.ext
  change Triangle.cayleyCoordinate a (g • z) = Triangle.cayleyCoordinate a z
  rw [Triangle.cayleyCoordinate_smul g a z ha, hm, one_mul]

private theorem SpecialPeriods.integerSL_real_action (g : SL(2, ℤ)) (z : ℍ) :
    (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) g) • z = g • z := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_specialLinearGroup_apply, UpperHalfPlane.coe_specialLinearGroup_apply]
  rfl

private theorem SpecialPeriods.modularSL_action_identity_of_two_fixed (g : SL(2, ℤ)) {a b : ℍ}
    (ha : g • a = a) (hb : g • b = b) (hab : a ≠ b) : ∀ z : ℍ, g • z = z := by
  have h :=
    realSL_action_identity_of_two_fixed (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) g)
      (by simpa only [integerSL_real_action] using ha)
      (by simpa only [integerSL_real_action] using hb) hab
  simpa only [integerSL_real_action] using h

private theorem SpecialPeriods.modularJ_equal_lifts_differ_by_SL {f g : ℍ → ℍ}
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g)
    (hJ : ∀ z, modularJ (f z) = modularJ (g z)) (a : ℍ)
    (ha : modularJ (f a) ∈ modularRegularValues) : ∃ γ : SL(2, ℤ), ∀ z, γ • f z = g z := by
  obtain ⟨γ, hγ⟩ := (modularJ_eq_iff_exists_smul (g a) (f a)).mp (hJ a).symm
  have hga : modularJ (g a) ∈ modularRegularValues := (hJ a) ▸ ha
  obtain ⟨U, hUo, hgaU, hUi⟩ :=
    modularJ_regular_injOn_neighbourhood (g a) ((mem_modularRegularValues _).mp hga).1
      ((mem_modularRegularValues _).mp hga).2
  have hγf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun z => γ • f z) := (modularSL_holomorphic γ).comp hf
  have hnear₁ : ∀ᶠ z in 𝓝 a, γ • f z ∈ U := by
    apply hγf.continuous.continuousAt.preimage_mem_nhds
    simpa only [hγ] using hUo.mem_nhds hgaU
  have hnear₂ : ∀ᶠ z in 𝓝 a, g z ∈ U :=
    hg.continuous.continuousAt.preimage_mem_nhds (hUo.mem_nhds hgaU)
  have he : (fun z => γ • f z) =ᶠ[𝓝 a] g := by
    filter_upwards [hnear₁, hnear₂] with z h₁ h₂
    exact hUi h₁ h₂ ((modularJ_SL_invariant γ (f z)).trans (hJ z))
  refine ⟨γ, ?_⟩
  exact congrFun (upperHalfPlane_holomorphic_eq_of_eventuallyEq hγf hg he)

private theorem SpecialPeriods.modular_T_has_no_fixed_point (z : ℍ) : ModularGroup.T • z ≠ z := by
  intro h
  have hc := congrArg (fun w : ℍ => (w : ℂ)) h
  rw [UpperHalfPlane.modular_T_smul, UpperHalfPlane.coe_vadd] at hc
  have hr := congrArg Complex.re hc
  simp only [Complex.add_re, Complex.ofReal_one, Complex.one_re] at hr
  linarith

private theorem SpecialPeriods.modularRho_fixed_iff (z : ℍ) :
    (ModularGroup.T * ModularGroup.S) • z = z ↔ z = rhoPoint := by
  constructor
  · intro hz
    by_contra hzr
    have hid :=
      modularSL_action_identity_of_two_fixed (ModularGroup.T * ModularGroup.S) TS_smul_rhoPoint hz
        (Ne.symm hzr)
    have hI := hid UpperHalfPlane.I
    rw [SemigroupAction.mul_smul, S_smul_I] at hI
    exact modular_T_has_no_fixed_point UpperHalfPlane.I hI
  · rintro rfl
    exact TS_smul_rhoPoint

private theorem SpecialPeriods.modularI_fixed_iff (z : ℍ) :
    ModularGroup.S • z = z ↔ z = UpperHalfPlane.I := by
  constructor
  · intro hz
    by_contra hzi
    have hid := modularSL_action_identity_of_two_fixed ModularGroup.S S_smul_I hz (Ne.symm hzi)
    have hρ : ModularGroup.T • rhoPoint = rhoPoint := by
      simpa only [SemigroupAction.mul_smul, hid rhoPoint] using TS_smul_rhoPoint
    exact modular_T_has_no_fixed_point rhoPoint hρ
  · rintro rfl
    exact S_smul_I

private def SpecialPeriods.TauCovariant (τ : ℍ → ℍ) : Prop :=
  (∀ z : ℍ, (τ (Triangle.generatorOneSL • z) : ℂ) = ((τ z : ℂ) - 1) / (τ z : ℂ)) ∧
    (∀ z : ℍ, (τ (Triangle.generatorTwoSL • z) : ℂ) = -1 / (τ z : ℂ))

private theorem SpecialPeriods.tau_covariant_values {τ : ℍ → ℍ} (hτ : TauCovariant τ) :
    τ Triangle.centerOne = rhoPoint ∧ τ Triangle.centerTwo = UpperHalfPlane.I := by
  constructor
  · apply (modularRho_fixed_iff _).mp
    apply UpperHalfPlane.ext
    rw [← modularRhoAction_coe]
    have h := hτ.1 Triangle.centerOne
    rw [Triangle.generatorOne_fix] at h
    exact h.symm
  · apply (modularI_fixed_iff _).mp
    apply UpperHalfPlane.ext
    rw [← modularIAction_coe]
    have h := hτ.2 Triangle.centerTwo
    rw [Triangle.generatorTwo_fix] at h
    exact h.symm

private theorem SpecialPeriods.ModularGermLift.enat_eq_nat_of_mul_eq_mo1973_17094 {x : ℕ∞}
    {m n : ℕ} (hm : 0 < m) (h : (m : ℕ∞) * x = (m * n : ℕ)) : x = n := by
  have hm0 : (m : ℕ∞) ≠ 0 := by exact_mod_cast hm.ne'
  have hfin : x ≠ ⊤ := by
    intro hx
    rw [hx, ENat.mul_top hm0] at h
    exact ENat.top_ne_natCast _ h
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hfin
  rw [← hk] at h
  have hkn : k = n := by
    have hmul : m * k = m * n := by exact_mod_cast h
    exact Nat.eq_of_mul_eq_mul_left hm hmul
  rw [← hk, hkn]

private theorem SpecialPeriods.ModularGermLift.modularJ_lift_order_mul {F τ : ℂ → ℂ} {a : ℂ}
    (hτ : AnalyticAt ℂ τ a) (hpos : 0 < (τ a).im)
    (hJ : (fun z => SpecialPeriods.modularJ (UpperHalfPlane.ofComplex (τ z))) =ᶠ[𝓝 a] F) :
    analyticOrderAt F a =
      analyticOrderAt (SpecialPeriods.modularJ ∘ UpperHalfPlane.ofComplex) (τ a) *
        analyticOrderAt (fun z => τ z - τ a) a := by
  have hj : AnalyticAt ℂ (SpecialPeriods.modularJ ∘ UpperHalfPlane.ofComplex) (τ a) := by
    simpa only [UpperHalfPlane.ofComplex_apply_of_im_pos hpos] using
      SpecialPeriods.modularJ_analyticAt (UpperHalfPlane.ofComplex (τ a))
  exact (analyticOrderAt_congr hJ).symm.trans (hj.analyticOrderAt_comp hτ)

private theorem
    SpecialPeriods.ModularGermLift.modularJ_lift_sub_1728_order_mul {F τ : ℂ → ℂ} {a : ℂ}
    (hτ : AnalyticAt ℂ τ a) (hpos : 0 < (τ a).im)
    (hJ : (fun z => SpecialPeriods.modularJ (UpperHalfPlane.ofComplex (τ z))) =ᶠ[𝓝 a] F) :
    analyticOrderAt (fun z => F z - 1728) a =
      analyticOrderAt (fun z => SpecialPeriods.modularJ (UpperHalfPlane.ofComplex z) - 1728)
          (τ a) *
        analyticOrderAt (fun z => τ z - τ a) a := by
  have hjbase : AnalyticAt ℂ (SpecialPeriods.modularJ ∘ UpperHalfPlane.ofComplex) (τ a) := by
    simpa only [UpperHalfPlane.ofComplex_apply_of_im_pos hpos] using
      SpecialPeriods.modularJ_analyticAt (UpperHalfPlane.ofComplex (τ a))
  have hj :
    AnalyticAt ℂ (fun z => SpecialPeriods.modularJ (UpperHalfPlane.ofComplex z) - 1728) (τ a) :=
    hjbase.sub analyticAt_const
  have he :
    (fun z => SpecialPeriods.modularJ (UpperHalfPlane.ofComplex (τ z)) - 1728) =ᶠ[𝓝 a]
      (fun z => F z - 1728) :=
    hJ.sub (Filter.EventuallyEq.rfl)
  exact (analyticOrderAt_congr he).symm.trans (hj.analyticOrderAt_comp hτ)

private theorem
    SpecialPeriods.ModularGermLift.modularJ_lift_order_of_zero {F τ : ℂ → ℂ} {a : ℂ} {n : ℕ}
    (hτ : AnalyticAt ℂ τ a) (hpos : 0 < (τ a).im)
    (hJ : (fun z => SpecialPeriods.modularJ (UpperHalfPlane.ofComplex (τ z))) =ᶠ[𝓝 a] F)
    (ha : F a = 0) (horder : analyticOrderAt F a = (3 * n : ℕ)) :
    analyticOrderAt (fun z => τ z - τ a) a = n := by
  have hj0 : SpecialPeriods.modularJ (UpperHalfPlane.ofComplex (τ a)) = 0 :=
    hJ.self_of_nhds.trans ha
  have hjord : analyticOrderAt (SpecialPeriods.modularJ ∘ UpperHalfPlane.ofComplex) (τ a) = 3 := by
    simpa only [UpperHalfPlane.ofComplex_apply_of_im_pos hpos] using
      SpecialPeriods.analyticOrderAt_modularJ_of_eq_zero (UpperHalfPlane.ofComplex (τ a)) hj0
  have hmul := modularJ_lift_order_mul hτ hpos hJ
  rw [horder, hjord] at hmul
  exact enat_eq_nat_of_mul_eq_mo1973_17094 (by decide : 0 < 3) hmul.symm

private theorem
    SpecialPeriods.ModularGermLift.modularJ_lift_order_of_1728 {F τ : ℂ → ℂ} {a : ℂ} {n : ℕ}
    (hτ : AnalyticAt ℂ τ a) (hpos : 0 < (τ a).im)
    (hJ : (fun z => SpecialPeriods.modularJ (UpperHalfPlane.ofComplex (τ z))) =ᶠ[𝓝 a] F)
    (ha : F a = 1728) (horder : analyticOrderAt (fun z => F z - 1728) a = (2 * n : ℕ)) :
    analyticOrderAt (fun z => τ z - τ a) a = n := by
  have hj1728 : SpecialPeriods.modularJ (UpperHalfPlane.ofComplex (τ a)) = 1728 :=
    hJ.self_of_nhds.trans ha
  have hjord :
    analyticOrderAt (fun z => SpecialPeriods.modularJ (UpperHalfPlane.ofComplex z) - 1728) (τ a) =
      2 := by
    simpa only [UpperHalfPlane.ofComplex_apply_of_im_pos hpos] using
      SpecialPeriods.analyticOrderAt_modularJ_sub_1728_of_eq (UpperHalfPlane.ofComplex (τ a))
        hj1728
  have hmul := modularJ_lift_sub_1728_order_mul hτ hpos hJ
  rw [horder, hjord] at hmul
  exact enat_eq_nat_of_mul_eq_mo1973_17094 (by decide : 0 < 2) hmul.symm

private theorem SpecialPeriods.ModularGermLift.E₄_lift_order_of_zero {τ : ℂ → ℂ} {a : ℂ}
    (hτ : AnalyticAt ℂ τ a) (hpos : 0 < (τ a).im)
    (ha : ModularForm.E₄ (UpperHalfPlane.ofComplex (τ a)) = 0) :
    analyticOrderAt (fun z => ModularForm.E₄ (UpperHalfPlane.ofComplex (τ z))) a =
      analyticOrderAt (fun z => τ z - τ a) a := by
  have hE : AnalyticAt ℂ (ModularForm.E₄ ∘ UpperHalfPlane.ofComplex) (τ a) := by
    simpa only [UpperHalfPlane.ofComplex_apply_of_im_pos hpos] using
      SpecialPeriods.modularForm_analyticAt ModularForm.E₄ (UpperHalfPlane.ofComplex (τ a))
  have ho : analyticOrderAt (ModularForm.E₄ ∘ UpperHalfPlane.ofComplex) (τ a) = 1 := by
    simpa only [UpperHalfPlane.ofComplex_apply_of_im_pos hpos] using
      SpecialPeriods.analyticOrderAt_E₄_of_eq_zero (UpperHalfPlane.ofComplex (τ a)) ha
  calc
    analyticOrderAt (fun z => ModularForm.E₄ (UpperHalfPlane.ofComplex (τ z))) a =
        analyticOrderAt (ModularForm.E₄ ∘ UpperHalfPlane.ofComplex) (τ a) *
          analyticOrderAt (fun z => τ z - τ a) a :=
      hE.analyticOrderAt_comp hτ
    _ = analyticOrderAt (fun z => τ z - τ a) a := by rw [ho, one_mul]

private theorem SpecialPeriods.ModularGermLift.E₆_lift_order_of_zero {τ : ℂ → ℂ} {a : ℂ}
    (hτ : AnalyticAt ℂ τ a) (hpos : 0 < (τ a).im)
    (ha : ModularForm.E₆ (UpperHalfPlane.ofComplex (τ a)) = 0) :
    analyticOrderAt (fun z => ModularForm.E₆ (UpperHalfPlane.ofComplex (τ z))) a =
      analyticOrderAt (fun z => τ z - τ a) a := by
  have hE : AnalyticAt ℂ (ModularForm.E₆ ∘ UpperHalfPlane.ofComplex) (τ a) := by
    simpa only [UpperHalfPlane.ofComplex_apply_of_im_pos hpos] using
      SpecialPeriods.modularForm_analyticAt ModularForm.E₆ (UpperHalfPlane.ofComplex (τ a))
  have ho : analyticOrderAt (ModularForm.E₆ ∘ UpperHalfPlane.ofComplex) (τ a) = 1 := by
    simpa only [UpperHalfPlane.ofComplex_apply_of_im_pos hpos] using
      SpecialPeriods.analyticOrderAt_E₆_of_eq_zero (UpperHalfPlane.ofComplex (τ a)) ha
  calc
    analyticOrderAt (fun z => ModularForm.E₆ (UpperHalfPlane.ofComplex (τ z))) a =
        analyticOrderAt (ModularForm.E₆ ∘ UpperHalfPlane.ofComplex) (τ a) *
          analyticOrderAt (fun z => τ z - τ a) a :=
      hE.analyticOrderAt_comp hτ
    _ = analyticOrderAt (fun z => τ z - τ a) a := by rw [ho, one_mul]

private theorem SpecialPeriods.ModularGermLift.analyticAt_upperHalfPlane_lift {τ : ℍ → ℍ}
    (hτ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) τ) (a : ℍ) :
    AnalyticAt ℂ (fun z => (τ (UpperHalfPlane.ofComplex z) : ℂ)) (a : ℂ) :=
  (UpperHalfPlane.mdifferentiable_iff.mp (UpperHalfPlane.mdifferentiable_coe.comp hτ)).analyticAt
    (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds a.im_pos)

private theorem
    SpecialPeriods.ModularGermLift.native_modular_equation_eventually {τ : ℍ → ℍ} {F : ℍ → ℂ}
    (hJ : ∀ a : ℍ, SpecialPeriods.modularJ (τ a) = F a) (a : ℍ) :
    (fun z : ℂ =>
        SpecialPeriods.modularJ
          (UpperHalfPlane.ofComplex (τ (UpperHalfPlane.ofComplex z)))) =ᶠ[𝓝 (a : ℂ)]
      (F ∘ UpperHalfPlane.ofComplex) := by
  filter_upwards with z
  simpa only [UpperHalfPlane.ofComplex_apply, Function.comp_apply] using
    hJ (UpperHalfPlane.ofComplex z)

private theorem
    SpecialPeriods.ModularGermLift.native_modularJ_lift_order_of_zero {τ : ℍ → ℍ} {F : ℍ → ℂ}
    (hτ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) τ) (hJ : ∀ a : ℍ, SpecialPeriods.modularJ (τ a) = F a) {a : ℍ}
    {n : ℕ} (ha : F a = 0)
    (horder : analyticOrderAt (F ∘ UpperHalfPlane.ofComplex) (a : ℂ) = (3 * n : ℕ)) :
    analyticOrderAt (fun z : ℂ => (τ (UpperHalfPlane.ofComplex z) : ℂ) - (τ a : ℂ)) (a : ℂ) = n :=
  by
  simpa only [UpperHalfPlane.ofComplex_apply] using
    modularJ_lift_order_of_zero (analyticAt_upperHalfPlane_lift hτ a)
      (by simpa only [UpperHalfPlane.ofComplex_apply, UpperHalfPlane.coe_im] using (τ a).im_pos)
      (native_modular_equation_eventually hJ a)
      (by simpa only [Function.comp_apply, UpperHalfPlane.ofComplex_apply] using ha) horder

private theorem
    SpecialPeriods.ModularGermLift.native_modularJ_lift_order_of_1728 {τ : ℍ → ℍ} {F : ℍ → ℂ}
    (hτ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) τ) (hJ : ∀ a : ℍ, SpecialPeriods.modularJ (τ a) = F a) {a : ℍ}
    {n : ℕ} (ha : F a = 1728)
    (horder :
      analyticOrderAt (fun z : ℂ => F (UpperHalfPlane.ofComplex z) - 1728) (a : ℂ) =
        (2 * n : ℕ)) :
    analyticOrderAt (fun z : ℂ => (τ (UpperHalfPlane.ofComplex z) : ℂ) - (τ a : ℂ)) (a : ℂ) = n :=
  by
  simpa only [UpperHalfPlane.ofComplex_apply] using
    modularJ_lift_order_of_1728 (analyticAt_upperHalfPlane_lift hτ a)
      (by simpa only [UpperHalfPlane.ofComplex_apply, UpperHalfPlane.coe_im] using (τ a).im_pos)
      (native_modular_equation_eventually hJ a)
      (by simpa only [Function.comp_apply, UpperHalfPlane.ofComplex_apply] using ha) horder

private theorem SpecialPeriods.ModularGermLift.native_E₄_lift_order_of_zero {τ : ℍ → ℍ}
    (hτ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) τ) {a : ℍ} (ha : ModularForm.E₄ (τ a) = 0) :
    analyticOrderAt (fun z : ℂ => ModularForm.E₄ (τ (UpperHalfPlane.ofComplex z))) (a : ℂ) =
      analyticOrderAt (fun z : ℂ => (τ (UpperHalfPlane.ofComplex z) : ℂ) - (τ a : ℂ)) (a : ℂ) := by
  simpa only [UpperHalfPlane.ofComplex_apply] using
    E₄_lift_order_of_zero (analyticAt_upperHalfPlane_lift hτ a)
      (by simpa only [UpperHalfPlane.ofComplex_apply, UpperHalfPlane.coe_im] using (τ a).im_pos)
      (by simpa only [UpperHalfPlane.ofComplex_apply] using ha)

private theorem SpecialPeriods.ModularGermLift.native_E₆_lift_order_of_zero {τ : ℍ → ℍ}
    (hτ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) τ) {a : ℍ} (ha : ModularForm.E₆ (τ a) = 0) :
    analyticOrderAt (fun z : ℂ => ModularForm.E₆ (τ (UpperHalfPlane.ofComplex z))) (a : ℂ) =
      analyticOrderAt (fun z : ℂ => (τ (UpperHalfPlane.ofComplex z) : ℂ) - (τ a : ℂ)) (a : ℂ) := by
  simpa only [UpperHalfPlane.ofComplex_apply] using
    E₆_lift_order_of_zero (analyticAt_upperHalfPlane_lift hτ a)
      (by simpa only [UpperHalfPlane.ofComplex_apply, UpperHalfPlane.coe_im] using (τ a).im_pos)
      (by simpa only [UpperHalfPlane.ofComplex_apply] using ha)

private theorem
    SpecialPeriods.ModularGermLift.native_E₆_order_of_source_order {τ : ℍ → ℍ} {F : ℍ → ℂ}
    (hτ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) τ) (hJ : ∀ a : ℍ, SpecialPeriods.modularJ (τ a) = F a) {a : ℍ}
    {n : ℕ} (ha : F a = 1728)
    (horder :
      analyticOrderAt (fun z : ℂ => F (UpperHalfPlane.ofComplex z) - 1728) (a : ℂ) =
        (2 * n : ℕ)) :
    analyticOrderAt (fun z : ℂ => ModularForm.E₆ (τ (UpperHalfPlane.ofComplex z))) (a : ℂ) = n := by
  have hE : ModularForm.E₆ (τ a) = 0 :=
    (SpecialPeriods.modularJ_eq_1728_iff (τ a)).mp ((hJ a).trans ha)
  exact
    (native_E₆_lift_order_of_zero hτ hE).trans
      (native_modularJ_lift_order_of_1728 hτ hJ ha horder)

private theorem SpecialPeriods.ModularGermLift.native_E₆_order_of_source_four_order {τ : ℍ → ℍ}
    {F : ℍ → ℂ} (hτ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) τ)
    (hJ : ∀ a : ℍ, SpecialPeriods.modularJ (τ a) = F a) {a : ℍ} {k : ℕ} (ha : F a = 1728)
    (horder :
      analyticOrderAt (fun z : ℂ => F (UpperHalfPlane.ofComplex z) - 1728) (a : ℂ) =
        (4 * k : ℕ)) :
    analyticOrderAt (fun z : ℂ => ModularForm.E₆ (τ (UpperHalfPlane.ofComplex z))) (a : ℂ) =
      (2 * k : ℕ) := by
  apply native_E₆_order_of_source_order hτ hJ ha
  simpa only [← Nat.mul_assoc] using horder

private theorem SpecialPeriods.ModularGermLift.native_E₆_finite_even_zeros {τ : ℍ → ℍ} {F : ℍ → ℂ}
    (hτ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) τ) (hJ : ∀ a : ℍ, SpecialPeriods.modularJ (τ a) = F a)
    (hsource :
      ∀ a : ℍ,
        F a = 1728 →
          ∃ k : ℕ,
            analyticOrderAt (fun z : ℂ => F (UpperHalfPlane.ofComplex z) - 1728) (a : ℂ) =
              (4 * k : ℕ)) :
    ∀ a : ℍ,
      ModularForm.E₆ (τ a) = 0 →
        ∃ n : ℕ,
          analyticOrderAt (fun z : ℂ => ModularForm.E₆ (τ (UpperHalfPlane.ofComplex z))) (a : ℂ) =
            (2 * n : ℕ) := by
  intro a ha
  have hFa : F a = 1728 := (hJ a).symm.trans ((SpecialPeriods.modularJ_eq_1728_iff (τ a)).mpr ha)
  obtain ⟨k, hk⟩ := hsource a hFa
  exact ⟨k, native_E₆_order_of_source_four_order hτ hJ hFa hk⟩

private theorem
    SpecialPeriods.realSL_actions_eq_of_fixed_deriv (g h : SL(2, ℝ)) (a : ℍ) (hg : g • a = a)
    (hh : h • a = a)
    (hd :
      deriv (fun z : ℂ => ((g • UpperHalfPlane.ofComplex z : ℍ) : ℂ)) (a : ℂ) =
        deriv (fun z : ℂ => ((h • UpperHalfPlane.ofComplex z : ℍ) : ℂ)) (a : ℂ)) :
    ∀ z : ℍ, g • z = h • z := by
  have hm : Triangle.slMultiplier g a = Triangle.slMultiplier h a := by
    simpa only [Triangle.sl_deriv_smul] using hd
  intro z
  apply (Triangle.cayleyBiholomorph a).injective
  apply Subtype.ext
  change Triangle.cayleyCoordinate a (g • z) = Triangle.cayleyCoordinate a (h • z)
  rw [Triangle.cayleyCoordinate_smul g a z hg, Triangle.cayleyCoordinate_smul h a z hh, hm]

private theorem SpecialPeriods.modularSL_actions_eq_of_fixed_deriv (g h : SL(2, ℤ)) (a : ℍ)
    (hg : g • a = a) (hh : h • a = a)
    (hd :
      deriv (fun z : ℂ => ((g • UpperHalfPlane.ofComplex z : ℍ) : ℂ)) (a : ℂ) =
        deriv (fun z : ℂ => ((h • UpperHalfPlane.ofComplex z : ℍ) : ℂ)) (a : ℂ)) :
    ∀ z : ℍ, g • z = h • z := by
  simpa only [integerSL_real_action] using
    realSL_actions_eq_of_fixed_deriv (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) g)
      (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) h) a
      (by simpa only [integerSL_real_action] using hg)
      (by simpa only [integerSL_real_action] using hh)
      (by simpa only [integerSL_real_action] using hd)

private theorem SpecialPeriods.modularSL_ambient_deriv_eq (g : SL(2, ℤ)) (f : ℂ → ℂ)
    (hf : ∀ z : ℍ, f z = ((g • z : ℍ) : ℂ)) (a : ℍ) :
    deriv (fun z : ℂ => ((g • UpperHalfPlane.ofComplex z : ℍ) : ℂ)) (a : ℂ) = deriv f (a : ℂ) := by
  apply Filter.EventuallyEq.deriv_eq
  have hpos : ∀ᶠ z : ℂ in 𝓝 (a : ℂ), 0 < z.im :=
    UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds a.im_pos
  filter_upwards [hpos] with z hz
  simpa only [UpperHalfPlane.ofComplex_apply_of_im_pos hz] using
    (hf (UpperHalfPlane.ofComplex z)).symm

private theorem SpecialPeriods.modularRho_ambient_deriv :
    deriv
        (fun z : ℂ => (((ModularGroup.T * ModularGroup.S) • UpperHalfPlane.ofComplex z : ℍ) : ℂ))
        (rhoPoint : ℂ) =
      -rho :=
  (modularSL_ambient_deriv_eq (ModularGroup.T * ModularGroup.S) modularRhoAction
        modularRhoAction_coe rhoPoint).trans
    modularRhoAction_deriv_rho

private theorem
    SpecialPeriods.modularJ_invariant_lift_action {τ : ℍ → ℍ} (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ)
    (A : SL(2, ℝ)) (hJ : ∀ z : ℍ, modularJ (τ (A • z)) = modularJ (τ z)) (x : ℍ)
    (hx : modularJ (τ x) ∈ modularRegularValues) : ∃ γ : SL(2, ℤ), ∀ z : ℍ, γ • τ z = τ (A • z) :=
  by
  exact
    modularJ_equal_lifts_differ_by_SL hτ (hτ.comp (Triangle.specialLinear_holomorphic A))
      (fun z => (hJ z).symm) x hx

private theorem
    SpecialPeriods.analytic_semiconjugacy_multiplier (τ A B : ℂ → ℂ) (a b ξ η : ℂ) (k : ℕ)
    (hτ : AnalyticAt ℂ τ a) (hτa : τ a = b)
    (horder : analyticOrderAt (fun z => τ z - b) a = (k : ℕ∞)) (hA : HasDerivAt A ξ a)
    (hAa : A a = a) (hB : HasDerivAt B η b) (hBb : B b = b) (hsem : τ ∘ A =ᶠ[𝓝 a] B ∘ τ) :
    η = ξ ^ k := by
  obtain ⟨u, hu, hu0, hfactor⟩ := (hτ.sub analyticAt_const).analyticOrderAt_eq_natCast.mp horder
  have hf : ∀ᶠ z in 𝓝 a, τ z - b = (z - a) ^ k * u z := by
    simpa only [Pi.sub_apply, smul_eq_mul] using hfactor
  have hAt : Filter.Tendsto A (𝓝 a) (𝓝 a) := by
    simpa only [ContinuousAt, hAa] using hA.continuousAt
  have hfA : ∀ᶠ z in 𝓝 a, τ (A z) - b = (A z - a) ^ k * u (A z) := hAt.eventually hf
  have he : (fun z => dslope A a z ^ k * u (A z)) =ᶠ[𝓝[≠] a] (fun z => u z * dslope B b (τ z)) := by
    filter_upwards [hf.filter_mono nhdsWithin_le_nhds, hfA.filter_mono nhdsWithin_le_nhds,
      hsem.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hfz hfAz hsemz hza
    have hAz : A z - a = (z - a) * dslope A a z := by
      simpa only [smul_eq_mul, hAa] using (sub_smul_dslope A a z).symm
    have hBz : B (τ z) - b = (τ z - b) * dslope B b (τ z) := by
      simpa only [smul_eq_mul, hBb] using (sub_smul_dslope B b (τ z)).symm
    apply mul_left_cancel₀ (pow_ne_zero k (sub_ne_zero.mpr hza))
    calc
      (z - a) ^ k * (dslope A a z ^ k * u (A z)) = ((z - a) * dslope A a z) ^ k * u (A z) := by
        rw [mul_pow, mul_assoc]
      _ = (A z - a) ^ k * u (A z) := by rw [← hAz]
      _ = τ (A z) - b := hfAz.symm
      _ = B (τ z) - b := (congrArg (fun w => w - b) hsemz)
      _ = (τ z - b) * dslope B b (τ z) := hBz
      _ = (z - a) ^ k * (u z * dslope B b (τ z)) := by rw [hfz, mul_assoc]
  have hcL : ContinuousAt (fun z => dslope A a z ^ k * u (A z)) a :=
    ((continuousAt_dslope_same.mpr hA.differentiableAt).pow k).mul
      (hu.continuousAt.comp_of_eq hA.continuousAt hAa)
  have hcR : ContinuousAt (fun z => u z * dslope B b (τ z)) a :=
    hu.continuousAt.mul
      ((continuousAt_dslope_same.mpr hB.differentiableAt).comp_of_eq hτ.continuousAt hτa)
  have hcenter :=
    tendsto_nhds_unique_of_eventuallyEq hcL.continuousWithinAt hcR.continuousWithinAt he
  have hcoeff : ξ ^ k * u a = u a * η := by
    simpa only [hAa, hτa, dslope_same, hA.deriv, hB.deriv] using hcenter
  apply mul_right_cancel₀ hu0
  rw [mul_comm η (u a)]
  exact hcoeff.symm

private theorem SpecialPeriods.analytic_semiconjugacy_deriv_pow (τ A B : ℂ → ℂ) (a b : ℂ) (k : ℕ)
    (hτ : AnalyticAt ℂ τ a) (hτa : τ a = b)
    (horder : analyticOrderAt (fun z => τ z - b) a = (k : ℕ∞)) (hA : AnalyticAt ℂ A a)
    (hAa : A a = a) (hB : AnalyticAt ℂ B b) (hBb : B b = b) (hsem : τ ∘ A =ᶠ[𝓝 a] B ∘ τ) :
    deriv B b = deriv A a ^ k :=
  analytic_semiconjugacy_multiplier τ A B a b (deriv A a) (deriv B b) k hτ hτa horder
    hA.differentiableAt.hasDerivAt hAa hB.differentiableAt.hasDerivAt hBb hsem

private theorem SpecialPeriods.tau_covariant_triangle_action {τ : ℍ → ℍ} (hτ : TauCovariant τ)
    (g : TriangleGroup) (z : ℍ) :
    τ (triangleGeometricRepresentation g z) = triangleModularAction g (τ z) := by
  let H :=
    TauEquivariance.intertwiningSubgroup triangleGeometricRepresentation triangleModularAction τ
  have hgen : ({ triangleGenerator₁, triangleGenerator₂ } : Set TriangleGroup) ⊆ H := by
    intro h hh
    rcases Set.mem_insert_iff.mp hh with rfl | hh
    · intro x
      apply UpperHalfPlane.ext
      rw [triangleGeometricRepresentation_generator₁_apply, triangleModularAction_generator₁_coe]
      exact hτ.1 x
    · have he : h = triangleGenerator₂ := Set.mem_singleton_iff.mp hh
      subst h
      intro x
      apply UpperHalfPlane.ext
      rw [triangleGeometricRepresentation_generator₂_apply, triangleModularAction_generator₂_coe]
      exact hτ.2 x
  have htop : (⊤ : Subgroup TriangleGroup) ≤ H := by
    rw [← triangle_generators_generate]
    exact (Subgroup.closure_le _).mpr hgen
  exact htop (Subgroup.mem_top g) z

private theorem SpecialPeriods.tau_covariant_cusp {τ : ℍ → ℍ} (hτ : TauCovariant τ) (z : ℍ) :
    τ (triangleGeometricRepresentation triangleCuspGenerator z) = (-1 : ℝ) +ᵥ τ z := by
  rw [tau_covariant_triangle_action hτ, triangleModularAction_cusp_apply]

private theorem SpecialPeriods.tau_covariant_cusp_coe {τ : ℍ → ℍ} (hτ : TauCovariant τ) (z : ℍ) :
    (τ (triangleGeometricRepresentation triangleCuspGenerator z) : ℂ) = (τ z : ℂ) - 1 := by
  rw [tau_covariant_triangle_action hτ, triangleModularAction_cusp_coe]

private theorem
    SpecialPeriods.modular_lift_action_of_order {τ : ℍ → ℍ} (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ)
    (A : SL(2, ℝ)) (a : ℍ) (hAa : A • a = a) (k : ℕ)
    (horder :
      analyticOrderAt (fun z : ℂ => (τ (UpperHalfPlane.ofComplex z) : ℂ) - (τ a : ℂ)) (a : ℂ) =
        (k : ℕ∞))
    (B : SL(2, ℤ)) (hBb : B • τ a = τ a)
    (hBderiv :
      deriv (fun z : ℂ => ((B • UpperHalfPlane.ofComplex z : ℍ) : ℂ)) (τ a : ℂ) =
        Triangle.slMultiplier A a ^ k)
    (hJ : ∀ z : ℍ, modularJ (τ (A • z)) = modularJ (τ z)) (x : ℍ)
    (hx : modularJ (τ x) ∈ modularRegularValues) : ∀ z : ℍ, τ (A • z) = B • τ z := by
  obtain ⟨γ, hγ⟩ := modularJ_invariant_lift_action hτ A hJ x hx
  have hγfix : γ • τ a = τ a := by simpa only [hAa] using hγ a
  let t : ℂ → ℂ := fun z => (τ (UpperHalfPlane.ofComplex z) : ℂ)
  let α : ℂ → ℂ := fun z => ((A • UpperHalfPlane.ofComplex z : ℍ) : ℂ)
  let β : ℂ → ℂ := fun z => ((γ • UpperHalfPlane.ofComplex z : ℍ) : ℂ)
  have ht : AnalyticAt ℂ t (a : ℂ) :=
    ModularGermLift.analyticAt_upperHalfPlane_lift (hτ.mdifferentiable (by simp)) a
  have hα : AnalyticAt ℂ α (a : ℂ) :=
    ModularGermLift.analyticAt_upperHalfPlane_lift
      ((Triangle.specialLinear_holomorphic A).mdifferentiable (by simp)) a
  have hβ : AnalyticAt ℂ β (τ a : ℂ) :=
    ModularGermLift.analyticAt_upperHalfPlane_lift
      ((modularSL_holomorphic γ).mdifferentiable (by simp)) (τ a)
  have ht₀ : t (a : ℂ) = (τ a : ℂ) := by simp only [t, UpperHalfPlane.ofComplex_apply]
  have hα₀ : α (a : ℂ) = (a : ℂ) := by simp only [α, UpperHalfPlane.ofComplex_apply, hAa]
  have hβ₀ : β (τ a : ℂ) = (τ a : ℂ) := by simp only [β, UpperHalfPlane.ofComplex_apply, hγfix]
  have hsem : t ∘ α =ᶠ[𝓝 (a : ℂ)] β ∘ t := by
    filter_upwards with w
    simpa only [t, α, β, Function.comp_apply, UpperHalfPlane.ofComplex_apply] using
      (congrArg (fun z : ℍ => (z : ℂ)) (hγ (UpperHalfPlane.ofComplex w))).symm
  have hm :=
    analytic_semiconjugacy_deriv_pow t α β (a : ℂ) (τ a : ℂ) k ht ht₀ horder hα hα₀ hβ hβ₀ hsem
  have hderiv :
    deriv (fun z : ℂ => ((γ • UpperHalfPlane.ofComplex z : ℍ) : ℂ)) (τ a : ℂ) =
      Triangle.slMultiplier A a ^ k := by simpa only [α, β, Triangle.sl_deriv_smul] using hm
  have he := modularSL_actions_eq_of_fixed_deriv γ B (τ a) hγfix hBb (hderiv.trans hBderiv.symm)
  intro z
  exact (hγ z).symm.trans (he (τ z))

private theorem
    SpecialPeriods.exists_regular_modular_value_of_j_values {X : Type*} [TopologicalSpace X]
    [PreconnectedSpace X] {τ : X → ℍ} (hτ : Continuous τ) (a b : X) (ha : modularJ (τ a) = 0)
    (hb : modularJ (τ b) = 1728) : ∃ x, modularJ (τ x) ∈ modularRegularValues := by
  let F : X → ℝ := fun x => (modularJ (τ x)).re
  have hF : Continuous F := Complex.continuous_re.comp (modularJ_continuous.comp hτ)
  have hmid : (864 : ℝ) ∈ Set.Icc (F a) (F b) := by norm_num [F, ha, hb]
  obtain ⟨x, hx⟩ := intermediate_value_univ a b hF hmid
  refine ⟨x, (mem_modularRegularValues _).mpr ⟨?_, ?_⟩⟩
  · intro hz
    have hh : F x = 0 := by simp [F, hz]
    linarith
  · intro hz
    have hh : F x = 1728 := by norm_num [F, hz]
    linarith

private theorem SpecialPeriods.modular_lift_first_generator_of_rho_order {τ : ℍ → ℍ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (ha : τ Triangle.centerOne = rhoPoint)
    (horder :
      analyticOrderAt (fun z : ℂ => (τ (UpperHalfPlane.ofComplex z) : ℂ) - rho)
          (Triangle.centerOne : ℂ) =
        1)
    (hJ : ∀ z : ℍ, modularJ (τ (Triangle.generatorOneSL • z)) = modularJ (τ z)) (x : ℍ)
    (hx : modularJ (τ x) ∈ modularRegularValues) :
    ∀ z : ℍ, τ (Triangle.generatorOneSL • z) = triangleModularA • τ z := by
  rw [triangleModularA_eq_T_mul_S]
  exact
    modular_lift_action_of_order hτ Triangle.generatorOneSL Triangle.centerOne
      Triangle.generatorOne_fix 1 (by simpa [ha] using horder) (ModularGroup.T * ModularGroup.S)
      (by rw [ha]; exact TS_smul_rhoPoint)
      (by rw [ha, modularRho_ambient_deriv, Triangle.generatorOne_multiplier, pow_one]) hJ x hx

private theorem
    SpecialPeriods.modularSL_actions_eq_of_two_values (B C : SL(2, ℤ)) (a b : ℍ) (hab : a ≠ b)
    (ha : B • a = C • a) (hb : B • b = C • b) : ∀ z : ℍ, B • z = C • z := by
  have ha' : (C⁻¹ * B) • a = a := by rw [SemigroupAction.mul_smul, ha, inv_smul_smul]
  have hb' : (C⁻¹ * B) • b = b := by rw [SemigroupAction.mul_smul, hb, inv_smul_smul]
  have h := modularSL_action_identity_of_two_fixed (C⁻¹ * B) ha' hb' hab
  intro z
  simpa only [SemigroupAction.mul_smul, smul_inv_smul] using congrArg (fun w : ℍ => C • w) (h z)

private theorem SpecialPeriods.modular_lift_product_cusp_action {τ : ℍ → ℍ} (B : SL(2, ℤ))
    (hA : ∀ z : ℍ, τ (Triangle.generatorOneSL • z) = triangleModularA • τ z)
    (hB : ∀ z : ℍ, B • τ z = τ (Triangle.generatorTwoSL • z)) :
    ∀ z : ℍ, (triangleModularA * B)⁻¹ • τ z = τ (Triangle.cuspSL • z) := by
  intro z
  rw [inv_smul_eq_iff, SemigroupAction.mul_smul, hB, ← hA, ← SemigroupAction.mul_smul, ←
    SemigroupAction.mul_smul, Triangle.generatorOneSL_mul_generatorTwoSL_mul_cuspSL, one_smul]

private theorem SpecialPeriods.modular_lift_cusp_monodromy_comparison {τ : ℍ → ℍ} (B C : SL(2, ℤ))
    (hA : ∀ z : ℍ, τ (Triangle.generatorOneSL • z) = triangleModularA • τ z)
    (hB : ∀ z : ℍ, B • τ z = τ (Triangle.generatorTwoSL • z))
    (hC : ∀ z : ℍ, τ (Triangle.cuspSL • z) = C • τ z) (a b : ℍ) (hab : τ a ≠ τ b) :
    ∀ z : ℍ, (triangleModularA * B)⁻¹ • z = C • z := by
  have hp := modular_lift_product_cusp_action B hA hB
  exact
    modularSL_actions_eq_of_two_values _ _ (τ a) (τ b) hab ((hp a).trans (hC a))
      ((hp b).trans (hC b))

private theorem SpecialPeriods.modular_lift_cusp_monodromy_conjugate {τ : ℍ → ℍ} (γ C : SL(2, ℤ))
    (hC : ∀ z : ℍ, τ (Triangle.cuspSL • z) = C • τ z) :
    ∀ z : ℍ, γ • τ (Triangle.cuspSL • z) = (γ * C * γ⁻¹) • (γ • τ z) := by
  intro z
  rw [hC, SemigroupAction.mul_smul, SemigroupAction.mul_smul, inv_smul_smul]

private theorem SpecialPeriods.modular_lift_monodromy_fixes_image {τ : ℍ → ℍ} (A : SL(2, ℝ)) (a : ℍ)
    (hAa : A • a = a) (γ : SL(2, ℤ)) (hγ : ∀ z : ℍ, γ • τ z = τ (A • z)) : γ • τ a = τ a := by
  simpa only [hAa] using hγ a

private theorem SpecialPeriods.modular_lift_monodromy_deriv_of_order {τ : ℍ → ℍ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (A : SL(2, ℝ)) (a : ℍ) (hAa : A • a = a) (k : ℕ)
    (horder :
      analyticOrderAt (fun z : ℂ => (τ (UpperHalfPlane.ofComplex z) : ℂ) - (τ a : ℂ)) (a : ℂ) =
        (k : ℕ∞))
    (γ : SL(2, ℤ)) (hγ : ∀ z : ℍ, γ • τ z = τ (A • z)) :
    deriv (fun w : ℂ => ((γ • UpperHalfPlane.ofComplex w : ℍ) : ℂ)) (τ a : ℂ) =
      Triangle.slMultiplier A a ^ k := by
  have hγfix := modular_lift_monodromy_fixes_image A a hAa γ hγ
  let t : ℂ → ℂ := fun z => (τ (UpperHalfPlane.ofComplex z) : ℂ)
  let α : ℂ → ℂ := fun z => ((A • UpperHalfPlane.ofComplex z : ℍ) : ℂ)
  let β : ℂ → ℂ := fun z => ((γ • UpperHalfPlane.ofComplex z : ℍ) : ℂ)
  have ht : AnalyticAt ℂ t (a : ℂ) :=
    ModularGermLift.analyticAt_upperHalfPlane_lift (hτ.mdifferentiable (by simp)) a
  have hα : AnalyticAt ℂ α (a : ℂ) :=
    ModularGermLift.analyticAt_upperHalfPlane_lift
      ((Triangle.specialLinear_holomorphic A).mdifferentiable (by simp)) a
  have hβ : AnalyticAt ℂ β (τ a : ℂ) :=
    ModularGermLift.analyticAt_upperHalfPlane_lift
      ((modularSL_holomorphic γ).mdifferentiable (by simp)) (τ a)
  have ht₀ : t (a : ℂ) = (τ a : ℂ) := by simp only [t, UpperHalfPlane.ofComplex_apply]
  have hα₀ : α (a : ℂ) = (a : ℂ) := by simp only [α, UpperHalfPlane.ofComplex_apply, hAa]
  have hβ₀ : β (τ a : ℂ) = (τ a : ℂ) := by simp only [β, UpperHalfPlane.ofComplex_apply, hγfix]
  have hsem : t ∘ α =ᶠ[𝓝 (a : ℂ)] β ∘ t := by
    filter_upwards with w
    simpa only [t, α, β, Function.comp_apply, UpperHalfPlane.ofComplex_apply] using
      (congrArg (fun z : ℍ => (z : ℂ)) (hγ (UpperHalfPlane.ofComplex w))).symm
  have hm :=
    analytic_semiconjugacy_deriv_pow t α β (a : ℂ) (τ a : ℂ) k ht ht₀ horder hα hα₀ hβ hβ₀ hsem
  simpa only [α, β, Triangle.sl_deriv_smul] using hm

private theorem SpecialPeriods.modular_lift_generatorTwo_monodromy_deriv {τ : ℍ → ℍ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ)
    (horder :
      analyticOrderAt
          (fun z : ℂ => (τ (UpperHalfPlane.ofComplex z) : ℂ) - (τ Triangle.centerTwo : ℂ))
          (Triangle.centerTwo : ℂ) =
        2)
    (γ : SL(2, ℤ)) (hγ : ∀ z : ℍ, γ • τ z = τ (Triangle.generatorTwoSL • z)) :
    deriv (fun w : ℂ => ((γ • UpperHalfPlane.ofComplex w : ℍ) : ℂ)) (τ Triangle.centerTwo : ℂ) =
      -1 := by
  simpa only [Triangle.generatorTwo_multiplier, neg_sq, Complex.I_sq] using
    modular_lift_monodromy_deriv_of_order hτ Triangle.generatorTwoSL Triangle.centerTwo
      Triangle.generatorTwo_fix 2 horder γ hγ

private def SpecialPeriods.modularSCyclicConjugate (k : Fin 3) : SL(2, ℤ) :=
  triangleModularA ^ (k : ℕ) * ModularGroup.S * (triangleModularA ^ (k : ℕ))⁻¹

private theorem SpecialPeriods.modularSCyclicConjugate_zero_matrix :
    (modularSCyclicConjugate 0 : Matrix (Fin 2) (Fin 2) ℤ) = !![0, -1; 1, 0] := by decide

private theorem SpecialPeriods.modularSCyclicConjugate_one_matrix :
    (modularSCyclicConjugate 1 : Matrix (Fin 2) (Fin 2) ℤ) = !![1, -2; 1, -1] := by decide

private theorem SpecialPeriods.modularSCyclicConjugate_two_matrix :
    (modularSCyclicConjugate 2 : Matrix (Fin 2) (Fin 2) ℤ) = !![1, -1; 2, -1] := by decide

private theorem SpecialPeriods.triangleModularA_product_trace (B : SL(2, ℤ)) :
    Matrix.trace (triangleModularA * B).val = B 0 0 + B 0 1 - B 1 0 := by
  change Matrix.trace ((triangleModularA : Matrix (Fin 2) (Fin 2) ℤ) * B.val) = _
  rw [Matrix.trace_fin_two]
  simp [triangleModularA, Matrix.mul_apply, Fin.sum_univ_two]
  ring

private theorem SpecialPeriods.trace_zero_entry_one_one_mo1973_17146 (B : SL(2, ℤ))
    (htr : Matrix.trace B.val = 0) : B 1 1 = -(B 0 0) := by
  rw [Matrix.trace_fin_two] at htr
  omega

private theorem SpecialPeriods.modular_trace_zero_trace_neg_two_classification (B : SL(2, ℤ))
    (htr : Matrix.trace B.val = 0) (hprod : Matrix.trace (triangleModularA * B).val = -2) :
    ∃ k : Fin 3, B = modularSCyclicConjugate k := by
  have h11 := trace_zero_entry_one_one_mo1973_17146 B htr
  have hdet : -(B 0 0) ^ 2 - B 0 1 * B 1 0 = 1 := by
    have hd : B 0 0 * B 1 1 - B 0 1 * B 1 0 = 1 :=
      (Matrix.det_fin_two B.val).symm.trans B.property
    rw [h11] at hd
    nlinarith [hd]
  rw [triangleModularA_product_trace] at hprod
  rcases GlobalTauNormalization.trace_neg_two_triples (B 0 0) (B 0 1) (B 1 0) hdet hprod with
    ⟨hp, hq, hr⟩ | ⟨hp, hq, hr⟩ | ⟨hp, hq, hr⟩
  · refine ⟨0, Subtype.ext ?_⟩
    rw [modularSCyclicConjugate_zero_matrix]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hp, hq, hr, h11]
  · refine ⟨1, Subtype.ext ?_⟩
    rw [modularSCyclicConjugate_one_matrix]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hp, hq, hr, h11]
  · refine ⟨2, Subtype.ext ?_⟩
    rw [modularSCyclicConjugate_two_matrix]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hp, hq, hr, h11]

private theorem SpecialPeriods.modular_trace_zero_parabolic_pair_classification (B : SL(2, ℤ))
    (htr : Matrix.trace B.val = 0)
    (hprod :
      Matrix.trace (triangleModularA * B).val = 2 ∨
        Matrix.trace (triangleModularA * B).val = -2) :
    ∃ k : Fin 3, B = modularSCyclicConjugate k ∨ B = -modularSCyclicConjugate k := by
  rcases hprod with hprod | hprod
  · have htr' : Matrix.trace (-B).val = 0 := by
      change Matrix.trace (-B.val) = 0
      rw [Matrix.trace_neg, htr, neg_zero]
    have hprod' : Matrix.trace (triangleModularA * (-B)).val = -2 := by
      rw [mul_neg]
      change Matrix.trace (-(triangleModularA * B).val) = -2
      rw [Matrix.trace_neg, hprod]
    obtain ⟨k, hk⟩ := modular_trace_zero_trace_neg_two_classification (-B) htr' hprod'
    refine ⟨k, Or.inr ?_⟩
    simpa only [neg_neg] using congrArg (fun C : SL(2, ℤ) => -C) hk
  · obtain ⟨k, hk⟩ := modular_trace_zero_trace_neg_two_classification B htr hprod
    exact ⟨k, Or.inl hk⟩

private def SpecialPeriods.modularCyclicNormalizer (k : Fin 3) : SL(2, ℤ) :=
  (triangleModularA ^ (k : ℕ))⁻¹

private theorem SpecialPeriods.modularCyclicNormalizer_conjugate_A (k : Fin 3) :
    modularCyclicNormalizer k * triangleModularA * (modularCyclicNormalizer k)⁻¹ =
      triangleModularA := by fin_cases k <;> decide

private theorem SpecialPeriods.modularCyclicNormalizer_conjugate_S (k : Fin 3) :
    modularCyclicNormalizer k * modularSCyclicConjugate k * (modularCyclicNormalizer k)⁻¹ =
      ModularGroup.S := by simp [modularCyclicNormalizer, modularSCyclicConjugate, mul_assoc]

private theorem SpecialPeriods.modular_pair_signed_conjugation_normalization (B : SL(2, ℤ))
    (htr : Matrix.trace B.val = 0)
    (hprod :
      Matrix.trace (triangleModularA * B).val = 2 ∨
        Matrix.trace (triangleModularA * B).val = -2) :
    ∃ k : Fin 3,
      modularCyclicNormalizer k * B * (modularCyclicNormalizer k)⁻¹ = ModularGroup.S ∨
        modularCyclicNormalizer k * B * (modularCyclicNormalizer k)⁻¹ = -ModularGroup.S := by
  obtain ⟨k, hk | hk⟩ := modular_trace_zero_parabolic_pair_classification B htr hprod
  · refine ⟨k, Or.inl ?_⟩
    rw [hk]
    exact modularCyclicNormalizer_conjugate_S k
  · refine ⟨k, Or.inr ?_⟩
    rw [hk, mul_neg, neg_mul, modularCyclicNormalizer_conjugate_S]

private theorem SpecialPeriods.modular_pair_projective_conjugation_normalization (B : SL(2, ℤ))
    (htr : Matrix.trace B.val = 0)
    (hprod :
      Matrix.trace (triangleModularA * B).val = 2 ∨
        Matrix.trace (triangleModularA * B).val = -2) :
    ∃ k : Fin 3,
      modularProjectivization (modularCyclicNormalizer k * B * (modularCyclicNormalizer k)⁻¹) =
        modularProjectivization ModularGroup.S := by
  obtain ⟨k, hk | hk⟩ := modular_pair_signed_conjugation_normalization B htr hprod
  · exact ⟨k, congrArg modularProjectivization hk⟩
  · exact
      ⟨k,
        (congrArg modularProjectivization hk).trans (modularProjectivization_neg ModularGroup.S)⟩

private theorem
    SpecialPeriods.triangleModularA_smul_rhoPoint : triangleModularA • rhoPoint = rhoPoint := by
  rw [triangleModularA_eq_T_mul_S]
  exact TS_smul_rhoPoint

private theorem SpecialPeriods.triangleModularA_pow_smul_rhoPoint (n : ℕ) :
    triangleModularA ^ n • rhoPoint = rhoPoint := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, SemigroupAction.mul_smul, triangleModularA_smul_rhoPoint, ih]

private theorem SpecialPeriods.modularCyclicNormalizer_smul_rhoPoint (k : Fin 3) :
    modularCyclicNormalizer k • rhoPoint = rhoPoint := by
  rw [modularCyclicNormalizer, inv_smul_eq_iff]
  exact (triangleModularA_pow_smul_rhoPoint k).symm

private theorem SpecialPeriods.modularCyclicNormalizer_intertwines_A (k : Fin 3) (z : ℍ) :
    modularCyclicNormalizer k • (triangleModularA • z) =
      triangleModularA • (modularCyclicNormalizer k • z) := by
  have he :=
    congrArg (fun C : SL(2, ℤ) => C • (modularCyclicNormalizer k • z))
      (modularCyclicNormalizer_conjugate_A k)
  simpa only [SemigroupAction.mul_smul, inv_smul_smul] using he

private theorem SpecialPeriods.normalized_B_action_mo1973_17159 (k : Fin 3) (B : SL(2, ℤ))
    (hB :
      modularProjectivization (modularCyclicNormalizer k * B * (modularCyclicNormalizer k)⁻¹) =
        modularProjectivization ModularGroup.S)
    (z : ℍ) :
    modularCyclicNormalizer k • (B • z) = ModularGroup.S • (modularCyclicNormalizer k • z) := by
  have he :=
    congrArg (fun C : PSL(2, ℤ) => modularPSLPermutation C (modularCyclicNormalizer k • z)) hB
  simpa only [modularPSLPermutation_projectivization, SemigroupAction.mul_smul,
    inv_smul_smul] using he

private theorem SpecialPeriods.normalized_product_projective_mo1973_17160 (k : Fin 3)
    (B : SL(2, ℤ))
    (hB :
      modularProjectivization (modularCyclicNormalizer k * B * (modularCyclicNormalizer k)⁻¹) =
        modularProjectivization ModularGroup.S) :
    modularProjectivization
        (modularCyclicNormalizer k * (triangleModularA * B) * (modularCyclicNormalizer k)⁻¹) =
      modularProjectivization ModularGroup.T := by
  have he :
    modularCyclicNormalizer k * (triangleModularA * B) * (modularCyclicNormalizer k)⁻¹ =
      (modularCyclicNormalizer k * triangleModularA * (modularCyclicNormalizer k)⁻¹) *
        (modularCyclicNormalizer k * B * (modularCyclicNormalizer k)⁻¹) := by group
  rw [he, map_mul, modularCyclicNormalizer_conjugate_A, hB]
  exact triangleModularGenerator₁_mul_generator₂

private theorem SpecialPeriods.normalized_cusp_projective_mo1973_17161 (k : Fin 3) (B : SL(2, ℤ))
    (hB :
      modularProjectivization (modularCyclicNormalizer k * B * (modularCyclicNormalizer k)⁻¹) =
        modularProjectivization ModularGroup.S) :
    modularProjectivization
        (modularCyclicNormalizer k * (triangleModularA * B)⁻¹ * (modularCyclicNormalizer k)⁻¹) =
      modularProjectivization ModularGroup.T⁻¹ := by
  have he :
    modularCyclicNormalizer k * (triangleModularA * B)⁻¹ * (modularCyclicNormalizer k)⁻¹ =
      (modularCyclicNormalizer k * (triangleModularA * B) * (modularCyclicNormalizer k)⁻¹)⁻¹ := by
    group
  rw [he, map_inv, normalized_product_projective_mo1973_17160 k B hB, ← map_inv]

private theorem SpecialPeriods.normalized_cusp_action_mo1973_17162 (k : Fin 3) (B : SL(2, ℤ))
    (hB :
      modularProjectivization (modularCyclicNormalizer k * B * (modularCyclicNormalizer k)⁻¹) =
        modularProjectivization ModularGroup.S)
    (z : ℍ) :
    modularCyclicNormalizer k • ((triangleModularA * B)⁻¹ • z) =
      ModularGroup.T⁻¹ • (modularCyclicNormalizer k • z) := by
  have he :=
    congrArg (fun C : PSL(2, ℤ) => modularPSLPermutation C (modularCyclicNormalizer k • z))
      (normalized_cusp_projective_mo1973_17161 k B hB)
  simpa only [modularPSLPermutation_projectivization, SemigroupAction.mul_smul,
    inv_smul_smul] using he

private theorem SpecialPeriods.modular_pair_cyclic_normalization (B : SL(2, ℤ))
    (htr : Matrix.trace B.val = 0)
    (hprod :
      Matrix.trace (triangleModularA * B).val = 2 ∨
        Matrix.trace (triangleModularA * B).val = -2) :
    ∃ k : Fin 3,
      modularCyclicNormalizer k • rhoPoint = rhoPoint ∧
        (∀ z : ℍ,
            modularCyclicNormalizer k • (triangleModularA • z) =
              triangleModularA • (modularCyclicNormalizer k • z)) ∧
          (∀ z : ℍ,
              modularCyclicNormalizer k • (B • z) =
                ModularGroup.S • (modularCyclicNormalizer k • z)) ∧
            (∀ z : ℍ,
              modularCyclicNormalizer k • ((triangleModularA * B)⁻¹ • z) =
                ModularGroup.T⁻¹ • (modularCyclicNormalizer k • z)) := by
  obtain ⟨k, hk⟩ := modular_pair_projective_conjugation_normalization B htr hprod
  exact
    ⟨k, modularCyclicNormalizer_smul_rhoPoint k, modularCyclicNormalizer_intertwines_A k,
      normalized_B_action_mo1973_17159 k B hk, normalized_cusp_action_mo1973_17162 k B hk⟩

private theorem SpecialPeriods.modular_pair_elliptic_value_normalization (B : SL(2, ℤ))
    (htr : Matrix.trace B.val = 0)
    (hprod :
      Matrix.trace (triangleModularA * B).val = 2 ∨ Matrix.trace (triangleModularA * B).val = -2)
    (z : ℍ) (hz : B • z = z) :
    ∃ k : Fin 3,
      modularCyclicNormalizer k • rhoPoint = rhoPoint ∧
        modularCyclicNormalizer k • z = UpperHalfPlane.I ∧
          (∀ w : ℍ,
              modularCyclicNormalizer k • (triangleModularA • w) =
                triangleModularA • (modularCyclicNormalizer k • w)) ∧
            (∀ w : ℍ,
                modularCyclicNormalizer k • (B • w) =
                  ModularGroup.S • (modularCyclicNormalizer k • w)) ∧
              (∀ w : ℍ,
                modularCyclicNormalizer k • ((triangleModularA * B)⁻¹ • w) =
                  ModularGroup.T⁻¹ • (modularCyclicNormalizer k • w)) := by
  obtain ⟨k, hρ, hA, hB, hcusp⟩ := modular_pair_cyclic_normalization B htr hprod
  refine ⟨k, hρ, ?_, hA, hB, hcusp⟩
  apply (modularI_fixed_iff _).mp
  exact (hB z).symm.trans (congrArg (fun w : ℍ => modularCyclicNormalizer k • w) hz)

private theorem
    SpecialPeriods.realSL_fixed_multiplier_eq_neg_one_iff_trace_zero (B : SL(2, ℝ)) (b : ℍ)
    (hfix : B • b = b) : Triangle.slMultiplier B b = -1 ↔ Matrix.trace B.val = 0 := by
  have hd := Triangle.slDenom_ne_zero B b
  have hidentity := Triangle.sl_fixed_denominator_identity B b hfix
  constructor
  · intro hmul
    have hsquare : Triangle.slDenom B b ^ 2 = -1 := by
      have he := (div_eq_iff (pow_ne_zero 2 hd)).mp hmul
      linear_combination he
    have hproduct : ((B 0 0 : ℂ) + (B 1 1 : ℂ)) * Triangle.slDenom B b = 0 := by
      dsimp [Triangle.slDenom] at hidentity hsquare ⊢
      linear_combination hidentity + hsquare
    have hsum := (mul_eq_zero.mp hproduct).resolve_right hd
    rw [Matrix.trace_fin_two]
    exact_mod_cast hsum
  · intro htrace
    rw [Matrix.trace_fin_two] at htrace
    have hsum : (B 0 0 : ℂ) + (B 1 1 : ℂ) = 0 := by exact_mod_cast htrace
    have hsquare : Triangle.slDenom B b ^ 2 = -1 := by
      dsimp [Triangle.slDenom] at hidentity ⊢
      linear_combination -hidentity + ((B 1 0 : ℂ) * (b : ℂ) + (B 1 1 : ℂ)) * hsum
    rw [Triangle.slMultiplier, hsquare]
    norm_num

private theorem SpecialPeriods.realSL_fixed_deriv_eq_neg_one_iff_trace_zero (B : SL(2, ℝ)) (b : ℍ)
    (hfix : B • b = b) :
    deriv (fun z : ℂ => ((B • UpperHalfPlane.ofComplex z : ℍ) : ℂ)) (b : ℂ) = -1 ↔
      Matrix.trace B.val = 0 := by
  rw [Triangle.sl_deriv_smul]
  exact realSL_fixed_multiplier_eq_neg_one_iff_trace_zero B b hfix

private theorem
    SpecialPeriods.modularSL_fixed_deriv_eq_neg_one_iff_trace_zero (B : SL(2, ℤ)) (b : ℍ)
    (hfix : B • b = b) :
    deriv (fun z : ℂ => ((B • UpperHalfPlane.ofComplex z : ℍ) : ℂ)) (b : ℂ) = -1 ↔
      Matrix.trace B.val = 0 := by
  have hfixR : Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) B • b = b := by
    rw [integerSL_real_action]
    exact hfix
  have htrace :
    Matrix.trace (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) B).val = 0 ↔
      Matrix.trace B.val = 0 := by
    rw [Matrix.trace_fin_two, Matrix.trace_fin_two]
    change (B 0 0 : ℝ) + (B 1 1 : ℝ) = 0 ↔ B 0 0 + B 1 1 = 0
    rw [← Int.cast_add, Int.cast_eq_zero]
  have h :=
    (realSL_fixed_deriv_eq_neg_one_iff_trace_zero
          (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) B) b hfixR).trans
      htrace
  simpa only [integerSL_real_action] using h

private theorem SpecialPeriods.modularSL_trace_zero_of_fixed_deriv_neg_one (B : SL(2, ℤ)) (b : ℍ)
    (hfix : B • b = b)
    (hderiv : deriv (fun z : ℂ => ((B • UpperHalfPlane.ofComplex z : ℍ) : ℂ)) (b : ℂ) = -1) :
    Matrix.trace B.val = 0 :=
  (modularSL_fixed_deriv_eq_neg_one_iff_trace_zero B b hfix).mp hderiv

private theorem SpecialPeriods.modularSL_trace_inv (B : SL(2, ℤ)) :
    Matrix.trace (B⁻¹).val = Matrix.trace B.val := by
  change Matrix.trace (Matrix.adjugate B.val) = Matrix.trace B.val
  simp [Matrix.trace_fin_two, Matrix.adjugate_fin_two, add_comm]

private theorem SpecialPeriods.modularSL_trace_conjugate (u B : SL(2, ℤ)) :
    Matrix.trace (u * B * u⁻¹).val = Matrix.trace B.val := by
  change
    Matrix.trace
        ((u : Matrix (Fin 2) (Fin 2) ℤ) * B.val * ((u⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) =
      _
  have hinv :
    ((u⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * (u : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
    exact congrArg (fun C : SL(2, ℤ) => C.val) (inv_mul_cancel u)
  rw [Matrix.trace_mul_cycle, hinv, one_mul]

private theorem SpecialPeriods.modularSL_actions_eq_iff (B C : SL(2, ℤ)) :
    (∀ z : ℍ, B • z = C • z) ↔ B = C ∨ B = -C := by
  constructor
  · intro h
    have he :
      Triangle.realSLPermutation (B : SL(2, ℝ)) = Triangle.realSLPermutation (C : SL(2, ℝ)) := by
      apply Equiv.ext
      intro z
      change
        (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) B) • z =
          (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) C) • z
      simpa only [integerSL_real_action] using h z
    rcases (Triangle.realSLPermutation_eq_iff _ _).mp he with he | he
    · exact Or.inl (Matrix.SpecialLinearGroup.map_intCast_injective (R := ℝ) he)
    · right
      apply Matrix.SpecialLinearGroup.map_intCast_injective (R := ℝ)
      simpa only [Matrix.SpecialLinearGroup.coe_int_neg] using he
  · rintro (rfl | rfl) z
    · rfl
    · exact ModularGroup.SL_neg_smul C z

private theorem SpecialPeriods.modularSL_trace_two_or_neg_two_of_actions_eq (B C : SL(2, ℤ))
    (h : ∀ z : ℍ, B • z = C • z) (hC : Matrix.trace C.val = 2 ∨ Matrix.trace C.val = -2) :
    Matrix.trace B.val = 2 ∨ Matrix.trace B.val = -2 := by
  rcases (modularSL_actions_eq_iff B C).mp h with rfl | rfl
  · exact hC
  · change Matrix.trace (-C.val) = 2 ∨ Matrix.trace (-C.val) = -2
    rw [Matrix.trace_neg]
    rcases hC with hC | hC
    · right
      rw [hC]
    · left
      rw [hC, neg_neg]

private theorem SpecialPeriods.modularSL_trace_two_or_neg_two_of_inverse_actions_eq (B C : SL(2, ℤ))
    (h : ∀ z : ℍ, B⁻¹ • z = C • z) (hC : Matrix.trace C.val = 2 ∨ Matrix.trace C.val = -2) :
    Matrix.trace B.val = 2 ∨ Matrix.trace B.val = -2 := by
  simpa only [modularSL_trace_inv] using modularSL_trace_two_or_neg_two_of_actions_eq B⁻¹ C h hC

private theorem SpecialPeriods.modular_pair_trace_two_or_neg_two_of_cusp_actions_eq (B C : SL(2, ℤ))
    (h : ∀ z : ℍ, (triangleModularA * B)⁻¹ • z = C • z)
    (hC : Matrix.trace C.val = 2 ∨ Matrix.trace C.val = -2) :
    Matrix.trace (triangleModularA * B).val = 2 ∨ Matrix.trace (triangleModularA * B).val = -2 :=
  modularSL_trace_two_or_neg_two_of_inverse_actions_eq (triangleModularA * B) C h hC

private theorem SpecialPeriods.exists_cyclic_normalization_of_rho_lift (F : ℍ → ℂ) {τ : ℍ → ℍ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (hJ : ∀ z : ℍ, modularJ (τ z) = F z)
    (ha : τ Triangle.centerOne = rhoPoint) (hFb : F Triangle.centerTwo = 1728)
    (hF₁ : ∀ z : ℍ, F (Triangle.generatorOneSL • z) = F z)
    (hF₂ : ∀ z : ℍ, F (Triangle.generatorTwoSL • z) = F z)
    (horder₁ : analyticOrderAt (F ∘ UpperHalfPlane.ofComplex) (Triangle.centerOne : ℂ) = 3)
    (horder₂ :
      analyticOrderAt (fun z : ℂ => F (UpperHalfPlane.ofComplex z) - 1728)
          (Triangle.centerTwo : ℂ) =
        4)
    (C : SL(2, ℤ)) (hCtr : Matrix.trace C.val = 2 ∨ Matrix.trace C.val = -2)
    (hC : ∀ z : ℍ, τ (Triangle.cuspSL • z) = C • τ z) :
    ∃ k : Fin 3,
      TauCovariant (fun z => modularCyclicNormalizer k • τ z) ∧
        modularCyclicNormalizer k • τ Triangle.centerOne = rhoPoint ∧
          modularCyclicNormalizer k • τ Triangle.centerTwo = UpperHalfPlane.I := by
  have hJa : modularJ (τ Triangle.centerOne) = 0 := by rw [ha, modularJ_rhoPoint]
  have hJb : modularJ (τ Triangle.centerTwo) = 1728 := (hJ _).trans hFb
  have hFa : F Triangle.centerOne = 0 := (hJ _).symm.trans hJa
  obtain ⟨x, hx⟩ :=
    exists_regular_modular_value_of_j_values hτ.continuous Triangle.centerOne Triangle.centerTwo
      hJa hJb
  have hτMD := hτ.mdifferentiable (by simp)
  have ho₁ :=
    ModularGermLift.native_modularJ_lift_order_of_zero hτMD hJ (n := 1) hFa
      (by simpa using horder₁)
  have ho₂ :=
    ModularGermLift.native_modularJ_lift_order_of_1728 hτMD hJ (n := 2) hFb
      (by simpa using horder₂)
  have hA :=
    modular_lift_first_generator_of_rho_order hτ ha (by simpa [ha] using ho₁)
      (by intro z; rw [hJ, hJ, hF₁]) x hx
  obtain ⟨B, hB⟩ :=
    modularJ_invariant_lift_action hτ Triangle.generatorTwoSL (by intro z; rw [hJ, hJ, hF₂]) x hx
  have hBfix :=
    modular_lift_monodromy_fixes_image Triangle.generatorTwoSL Triangle.centerTwo
      Triangle.generatorTwo_fix B hB
  have hBderiv := modular_lift_generatorTwo_monodromy_deriv hτ (by simpa using ho₂) B hB
  have hBtr := modularSL_trace_zero_of_fixed_deriv_neg_one B (τ Triangle.centerTwo) hBfix hBderiv
  have hab : τ Triangle.centerOne ≠ τ Triangle.centerTwo := by
    intro he
    have hh := congrArg modularJ he
    rw [hJa, hJb] at hh
    norm_num at hh
  have hcomp :=
    modular_lift_cusp_monodromy_comparison B C hA hB hC Triangle.centerOne Triangle.centerTwo hab
  have hprod := modular_pair_trace_two_or_neg_two_of_cusp_actions_eq B C hcomp hCtr
  obtain ⟨k, hkρ, hki, hkA, hkB, _⟩ :=
    modular_pair_elliptic_value_normalization B hBtr hprod (τ Triangle.centerTwo) hBfix
  refine ⟨k, ⟨?_, ?_⟩, ?_, hki⟩
  · intro z
    change ((modularCyclicNormalizer k • τ (Triangle.generatorOneSL • z) : ℍ) : ℂ) = _
    rw [hA, hkA, triangleModularA_eq_T_mul_S, ← modularRhoAction_coe]
    rfl
  · intro z
    change ((modularCyclicNormalizer k • τ (Triangle.generatorTwoSL • z) : ℍ) : ℂ) = _
    rw [← hB z, hkB, ← modularIAction_coe]
    rfl
  · rw [ha, hkρ]

private theorem SpecialPeriods.exists_normalized_covariant_modular_translate (F : ℍ → ℂ) {τ : ℍ → ℍ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (hJ : ∀ z : ℍ, modularJ (τ z) = F z)
    (hFa : F Triangle.centerOne = 0) (hFb : F Triangle.centerTwo = 1728)
    (hF₁ : ∀ z : ℍ, F (Triangle.generatorOneSL • z) = F z)
    (hF₂ : ∀ z : ℍ, F (Triangle.generatorTwoSL • z) = F z)
    (horder₁ : analyticOrderAt (F ∘ UpperHalfPlane.ofComplex) (Triangle.centerOne : ℂ) = 3)
    (horder₂ :
      analyticOrderAt (fun z : ℂ => F (UpperHalfPlane.ofComplex z) - 1728)
          (Triangle.centerTwo : ℂ) =
        4)
    (C : SL(2, ℤ)) (hCtr : Matrix.trace C.val = 2 ∨ Matrix.trace C.val = -2)
    (hC : ∀ z : ℍ, τ (Triangle.cuspSL • z) = C • τ z) :
    ∃ γ : SL(2, ℤ),
      TauCovariant (fun z => γ • τ z) ∧
        γ • τ Triangle.centerOne = rhoPoint ∧ γ • τ Triangle.centerTwo = UpperHalfPlane.I := by
  have hzero : modularJ rhoPoint = modularJ (τ Triangle.centerOne) := by
    rw [modularJ_rhoPoint, hJ, hFa]
  obtain ⟨δ, hδ⟩ := (modularJ_eq_iff_exists_smul rhoPoint (τ Triangle.centerOne)).mp hzero
  let σ : ℍ → ℍ := fun z => δ • τ z
  have hσ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω σ := (modularSL_holomorphic δ).comp hτ
  have hσJ : ∀ z : ℍ, modularJ (σ z) = F z := by
    intro z
    exact (modularJ_SL_invariant δ (τ z)).trans (hJ z)
  have hσa : σ Triangle.centerOne = rhoPoint := hδ
  have hCtr' : Matrix.trace (δ * C * δ⁻¹).val = 2 ∨ Matrix.trace (δ * C * δ⁻¹).val = -2 := by
    simpa only [modularSL_trace_conjugate] using hCtr
  have hC' : ∀ z : ℍ, σ (Triangle.cuspSL • z) = (δ * C * δ⁻¹) • σ z :=
    modular_lift_cusp_monodromy_conjugate δ C hC
  obtain ⟨k, hkc, hka, hkb⟩ :=
    exists_cyclic_normalization_of_rho_lift F hσ hσJ hσa hFb hF₁ hF₂ horder₁ horder₂ (δ * C * δ⁻¹)
      hCtr' hC'
  refine ⟨modularCyclicNormalizer k * δ, ?_, ?_, ?_⟩
  · simpa only [TauCovariant, σ, SemigroupAction.mul_smul] using hkc
  · simpa only [σ, SemigroupAction.mul_smul] using hka
  · simpa only [σ, SemigroupAction.mul_smul] using hkb

private theorem
    SpecialPeriods.modular_Tinv_vadd (z : ℍ) : ModularGroup.T⁻¹ • z = (-1 : ℝ) +ᵥ z := by
  simpa using UpperHalfPlane.modular_T_zpow_smul z (-1)

private theorem
    SpecialPeriods.tau_cusp_monodromy_of_formula {τ : ℍ → ℍ} (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ)
    {r : ℝ} (hr : 0 < r) {h : ℂ → ℂ}
    (hformula :
      ∀ z : ℍ,
        ‖Function.Periodic.qParam Triangle.width (z : ℂ)‖ < r →
          (τ z : ℂ) = TauCusp.correctedLogarithmWidth Triangle.width h (z : ℂ)) :
    ∀ z : ℍ, τ (Triangle.cuspSL • z) = ModularGroup.T⁻¹ • τ z := by
  intro z
  have he :=
    TauCusp.global_native_sub_int_mul_width_of_cuspFormula Triangle.width Triangle.width_pos hr hτ
      hformula (1 : ℤ) z
  have hz : ((Triangle.cuspSL • z : ℍ) : ℂ) = (z : ℂ) - Triangle.width := by
    rw [Triangle.cuspSL_apply, UpperHalfPlane.coe_vadd]
    push_cast
    ring
  have harg :
    UpperHalfPlane.ofComplex ((z : ℂ) - (1 : ℂ) * Triangle.width) = Triangle.cuspSL • z := by
    rw [one_mul, ← hz, UpperHalfPlane.ofComplex_apply]
  apply UpperHalfPlane.ext
  calc
    (τ (Triangle.cuspSL • z) : ℂ) = (τ z : ℂ) - 1 := by simpa only [Int.cast_one, harg] using he
    _ = ((ModularGroup.T⁻¹ • τ z : ℍ) : ℂ) := by
      rw [modular_Tinv_vadd, UpperHalfPlane.coe_vadd]
      push_cast
      ring

private theorem SpecialPeriods.tau_covariant_cuspSL {τ : ℍ → ℍ} (hτ : TauCovariant τ) (z : ℍ) :
    τ (Triangle.cuspSL • z) = ModularGroup.T⁻¹ • τ z := by
  rw [Triangle.cuspSL_apply, modular_Tinv_vadd]
  simpa only [triangleGeometricRepresentation_cusp_apply] using tau_covariant_cusp hτ z

private theorem SpecialPeriods.modular_translate_commutes_Tinv_of_cusp_covariance {τ : ℍ → ℍ}
    (γ : SL(2, ℤ)) (hC : ∀ z : ℍ, τ (Triangle.cuspSL • z) = ModularGroup.T⁻¹ • τ z)
    (hcov : TauCovariant (fun z => γ • τ z)) (a b : ℍ) (hab : τ a ≠ τ b) :
    ∀ z : ℍ, γ • (ModularGroup.T⁻¹ • z) = ModularGroup.T⁻¹ • (γ • z) := by
  have hvalues (z : ℍ) : (γ * ModularGroup.T⁻¹) • τ z = (ModularGroup.T⁻¹ * γ) • τ z := by
    rw [SemigroupAction.mul_smul, SemigroupAction.mul_smul, ← hC z]
    exact tau_covariant_cuspSL hcov z
  simpa only [SemigroupAction.mul_smul] using
    modularSL_actions_eq_of_two_values (γ * ModularGroup.T⁻¹) (ModularGroup.T⁻¹ * γ) (τ a) (τ b)
      hab (hvalues a) (hvalues b)

private theorem SpecialPeriods.modularSL_commutes_T_inv_of_actions_commute (γ : SL(2, ℤ))
    (h : ∀ z : ℍ, γ • (ModularGroup.T⁻¹ • z) = ModularGroup.T⁻¹ • (γ • z)) :
    Commute γ ModularGroup.T⁻¹ := by
  have hconj : ∀ z : ℍ, (γ * ModularGroup.T⁻¹ * γ⁻¹) • z = ModularGroup.T⁻¹ • z := by
    intro z
    simp only [SemigroupAction.mul_smul]
    rw [h, smul_inv_smul]
  rcases (modularSL_actions_eq_iff (γ * ModularGroup.T⁻¹ * γ⁻¹) ModularGroup.T⁻¹).mp hconj with
    he | he
  · change γ * ModularGroup.T⁻¹ = ModularGroup.T⁻¹ * γ
    have hm := congrArg (fun B : SL(2, ℤ) => B * γ) he
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using hm
  · have ht := congrArg (fun B : SL(2, ℤ) => Matrix.trace B.val) he
    rw [modularSL_trace_conjugate] at ht
    change
      Matrix.trace (ModularGroup.T⁻¹ : SL(2, ℤ)).val =
        Matrix.trace (-((ModularGroup.T⁻¹ : SL(2, ℤ)).val)) at ht
    have hT : Matrix.trace (ModularGroup.T⁻¹ : SL(2, ℤ)).val = 2 := by decide
    rw [Matrix.trace_neg, hT] at ht
    norm_num at ht

private theorem SpecialPeriods.modularSL_lower_left_zero_of_commutes_T_inv_mo1973_17251
    (γ : SL(2, ℤ)) (h : Commute γ ModularGroup.T⁻¹) : γ 1 0 = 0 := by
  have he := congrArg (fun B : SL(2, ℤ) => B 0 0) h.eq
  change
    (γ.val * (ModularGroup.T⁻¹ : SL(2, ℤ)).val) 0 0 =
      ((ModularGroup.T⁻¹ : SL(2, ℤ)).val * γ.val) 0 0 at he
  rw [ModularGroup.coe_T_inv] at he
  simp [Matrix.mul_apply, Fin.sum_univ_two] at he
  omega

private theorem SpecialPeriods.modularSL_integer_translation_of_commutes_T_inv_action (γ : SL(2, ℤ))
    (h : ∀ z : ℍ, γ • (ModularGroup.T⁻¹ • z) = ModularGroup.T⁻¹ • (γ • z)) :
    ∃ n : ℤ, ∀ z : ℍ, γ • z = (n : ℝ) +ᵥ z := by
  have hc :=
    modularSL_lower_left_zero_of_commutes_T_inv_mo1973_17251 γ
      (modularSL_commutes_T_inv_of_actions_commute γ h)
  obtain ⟨n, hn⟩ := ModularGroup.exists_eq_T_zpow_of_c_eq_zero (g := γ) hc
  exact ⟨n, fun z => (hn z).trans (UpperHalfPlane.modular_T_zpow_smul z n)⟩

private theorem
    SpecialPeriods.modularSL_integer_translation_coe_of_commutes_T_inv_action (γ : SL(2, ℤ))
    (h : ∀ z : ℍ, γ • (ModularGroup.T⁻¹ • z) = ModularGroup.T⁻¹ • (γ • z)) :
    ∃ n : ℤ, ∀ z : ℍ, ((γ • z : ℍ) : ℂ) = (z : ℂ) + (n : ℂ) := by
  obtain ⟨n, hn⟩ := modularSL_integer_translation_of_commutes_T_inv_action γ h
  refine ⟨n, fun z => ?_⟩
  rw [hn z, UpperHalfPlane.coe_vadd]
  simp [add_comm]

private theorem
    SpecialPeriods.ModularGermLift.analyticAt_modular_smul_of_im_pos (γ : SL(2, ℤ)) {w : ℂ}
    (hw : 0 < w.im) : AnalyticAt ℂ (fun v : ℂ => ((γ • UpperHalfPlane.ofComplex v : ℍ) : ℂ)) w := by
  change
    AnalyticAt ℂ
      (fun v : ℂ => ((Matrix.SpecialLinearGroup.mapGL ℝ γ • UpperHalfPlane.ofComplex v : ℍ) : ℂ))
      w
  apply UpperHalfPlane.analyticAt_smul (τ := (⟨w, hw⟩ : ℍ))
  change 0 < ((Matrix.SpecialLinearGroup.mapGL ℝ γ).det : ℝ)
  simp

private theorem
    SpecialPeriods.ModularGermLift.analyticAt_modular_smul (γ : SL(2, ℤ)) {σ : ℂ → ℂ} {a : ℂ}
    (hσ : AnalyticAt ℂ σ a) (hσa : 0 < (σ a).im) :
    AnalyticAt ℂ (fun z => ((γ • UpperHalfPlane.ofComplex (σ z) : ℍ) : ℂ)) a :=
  (analyticAt_modular_smul_of_im_pos γ hσa).comp hσ

private theorem SpecialPeriods.ModularGermLift.analyticOnNhd_modular_smul (γ : SL(2, ℤ)) {σ : ℂ → ℂ}
    {U : Set ℂ} (hσ : AnalyticOnNhd ℂ σ U)
    (hσU : Set.MapsTo σ U UpperHalfPlane.upperHalfPlaneSet) :
    AnalyticOnNhd ℂ (fun z => ((γ • UpperHalfPlane.ofComplex (σ z) : ℍ) : ℂ)) U := fun a ha =>
  analyticAt_modular_smul γ (hσ a ha) (hσU ha)

private theorem SpecialPeriods.ModularGermLift.modularJ_modular_smul (γ : SL(2, ℤ)) (w : ℂ) :
    SpecialPeriods.modularJ
        (UpperHalfPlane.ofComplex ((γ • UpperHalfPlane.ofComplex w : ℍ) : ℂ)) =
      SpecialPeriods.modularJ (UpperHalfPlane.ofComplex w) := by
  rw [UpperHalfPlane.ofComplex_apply]
  exact SpecialPeriods.modularJ_SL_invariant γ (UpperHalfPlane.ofComplex w)

private theorem SpecialPeriods.ModularGermLift.modularGroup_countable : Countable SL(2, ℤ) := by
  unfold Matrix.SpecialLinearGroup Matrix
  infer_instance

private theorem SpecialPeriods.ModularGermLift.exists_eqOn_of_countable_analytic_cover {ι : Type*}
    [Countable ι] {U : Set ℂ} {f : ℂ → ℂ} {g : ι → ℂ → ℂ} (hU : IsOpen U) (hUc : IsPreconnected U)
    (hUn : U.Nonempty) (hf : AnalyticOnNhd ℂ f U) (hg : ∀ i, AnalyticOnNhd ℂ (g i) U)
    (hcover : ∀ z ∈ U, ∃ i, f z = g i z) : ∃ i, Set.EqOn f (g i) U := by
  let : BaireSpace U := hU.baireSpace
  obtain ⟨a, ha⟩ := hUn
  let : Nonempty U := ⟨⟨a, ha⟩⟩
  let C : ι → Set U := fun i => {z | f z = g i z}
  have hC (i : ι) : IsClosed (C i) :=
    isClosed_eq hf.continuousOn.domRestrict (hg i).continuousOn.domRestrict
  have hCU : ⋃ i, C i = Set.univ := by
    ext z
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact hcover z z.2
  obtain ⟨i, z, hz⟩ := nonempty_interior_of_iUnion_of_closed hC hCU
  let V : Set ℂ := Subtype.val '' interior (C i)
  have hV : IsOpen V := hU.isOpenMap_subtype_val _ isOpen_interior
  have hzV : (z : ℂ) ∈ V := Set.mem_image_of_mem Subtype.val hz
  have heq : f =ᶠ[𝓝 (z : ℂ)] g i := by
    filter_upwards [hV.mem_nhds hzV] with w hw
    obtain ⟨v, hv, rfl⟩ := hw
    have hvC : v ∈ C i := interior_subset hv
    exact hvC
  exact ⟨i, hf.eqOn_of_preconnected_of_eventuallyEq (hg i) hUc z.2 heq⟩

private theorem SpecialPeriods.ModularGermLift.exists_modular_alignment {U : Set ℂ} {τ σ : ℂ → ℂ}
    (hU : IsOpen U) (hUc : IsPreconnected U) (hUn : U.Nonempty) (hτ : AnalyticOnNhd ℂ τ U)
    (hσ : AnalyticOnNhd ℂ σ U) (hτU : Set.MapsTo τ U UpperHalfPlane.upperHalfPlaneSet)
    (hσU : Set.MapsTo σ U UpperHalfPlane.upperHalfPlaneSet)
    (hJ :
      Set.EqOn (fun z => SpecialPeriods.modularJ (UpperHalfPlane.ofComplex (τ z)))
        (fun z => SpecialPeriods.modularJ (UpperHalfPlane.ofComplex (σ z))) U) :
    ∃ γ : SL(2, ℤ), Set.EqOn τ (fun z => ((γ • UpperHalfPlane.ofComplex (σ z) : ℍ) : ℂ)) U := by
  let : Countable SL(2, ℤ) := modularGroup_countable
  apply
    exists_eqOn_of_countable_analytic_cover hU hUc hUn hτ
      (fun γ => analyticOnNhd_modular_smul γ hσ hσU)
  intro z hz
  obtain ⟨γ, hγ⟩ :=
    (SpecialPeriods.modularJ_eq_iff_exists_smul (UpperHalfPlane.ofComplex (τ z))
          (UpperHalfPlane.ofComplex (σ z))).mp
      (hJ hz)
  refine ⟨γ, ?_⟩
  have hc := congrArg (fun w : ℍ => (w : ℂ)) hγ
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos (hτU hz)] at hc
  exact hc.symm

private theorem SpecialPeriods.ModularGermLift.exists_modular_alignment_germ {τ σ : ℂ → ℂ} {a : ℂ}
    (hτ : AnalyticAt ℂ τ a) (hσ : AnalyticAt ℂ σ a) (hτa : 0 < (τ a).im) (hσa : 0 < (σ a).im)
    (hJ :
      (fun z => SpecialPeriods.modularJ (UpperHalfPlane.ofComplex (τ z))) =ᶠ[𝓝 a]
        (fun z => SpecialPeriods.modularJ (UpperHalfPlane.ofComplex (σ z)))) :
    ∃ γ : SL(2, ℤ), τ =ᶠ[𝓝 a] (fun z => ((γ • UpperHalfPlane.ofComplex (σ z) : ℍ) : ℂ)) := by
  have hpτ : ∀ᶠ z in 𝓝 a, τ z ∈ UpperHalfPlane.upperHalfPlaneSet :=
    hτ.continuousAt.preimage_mem_nhds (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hτa)
  have hpσ : ∀ᶠ z in 𝓝 a, σ z ∈ UpperHalfPlane.upperHalfPlaneSet :=
    hσ.continuousAt.preimage_mem_nhds (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hσa)
  have hn :
    {z |
        AnalyticAt ℂ τ z ∧
          AnalyticAt ℂ σ z ∧
            τ z ∈ UpperHalfPlane.upperHalfPlaneSet ∧
              σ z ∈ UpperHalfPlane.upperHalfPlaneSet ∧
                SpecialPeriods.modularJ (UpperHalfPlane.ofComplex (τ z)) =
                  SpecialPeriods.modularJ (UpperHalfPlane.ofComplex (σ z))} ∈
      𝓝 a :=
    hτ.eventually_analyticAt.and (hσ.eventually_analyticAt.and (hpτ.and (hpσ.and hJ)))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hn
  obtain ⟨γ, hγ⟩ :=
    exists_modular_alignment Metric.isOpen_ball (convex_ball a ε).isPreconnected
      ⟨a, Metric.mem_ball_self hε⟩ (fun z hz => (hball hz).1) (fun z hz => (hball hz).2.1)
      (fun z hz => (hball hz).2.2.1) (fun z hz => (hball hz).2.2.2.1)
      (fun z hz => (hball hz).2.2.2.2)
  exact ⟨γ, Filter.eventually_of_mem (Metric.ball_mem_nhds a hε) (fun _ hz => hγ hz)⟩

private def
    AnalyticRootCover.ambientVal (S : TopologicalSpace.Opens ℂ) (V : TopologicalSpace.Opens S)
    (x : V) : ℂ :=
  ((x : S) : ℂ)

private theorem AnalyticRootCover.ambientVal_injective (S : TopologicalSpace.Opens ℂ)
    (V : TopologicalSpace.Opens S) : Function.Injective (ambientVal S V) :=
  Subtype.val_injective.comp Subtype.val_injective

private def
    AnalyticRootCover.ambientOpen (S : TopologicalSpace.Opens ℂ) (V : TopologicalSpace.Opens S) :
    TopologicalSpace.Opens ℂ :=
  ⟨Subtype.val '' (V : Set S), S.isOpen.isOpenMap_subtype_val _ V.isOpen⟩

private theorem AnalyticRootCover.ambientVal_mem (S : TopologicalSpace.Opens ℂ)
    (V : TopologicalSpace.Opens S) (x : V) : ambientVal S V x ∈ ambientOpen S V :=
  ⟨(x : S), x.2, rfl⟩

private theorem AnalyticRootCover.mem_ambientOpen (S : TopologicalSpace.Opens ℂ)
    (V : TopologicalSpace.Opens S) {z : ℂ} :
    z ∈ ambientOpen S V ↔ ∃ x : V, ambientVal S V x = z := by
  constructor
  · rintro ⟨x, hx, hxz⟩
    exact ⟨⟨x, hx⟩, hxz⟩
  · rintro ⟨x, rfl⟩
    exact ambientVal_mem S V x

@[simp]
private theorem AnalyticRootCover.coe_mem_ambientOpen (S : TopologicalSpace.Opens ℂ)
    (V : TopologicalSpace.Opens S) (x : S) : (x : ℂ) ∈ ambientOpen S V ↔ x ∈ V := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    have he : y = x := Subtype.ext hyx
    subst y
    exact hy
  · intro hx
    exact ⟨x, hx, rfl⟩

private def
    AnalyticRootCover.extendSection (S : TopologicalSpace.Opens ℂ) (V : TopologicalSpace.Opens S)
    (s : V → ℂ) : ℂ → ℂ :=
  Function.extend (ambientVal S V) s 0

@[simp]
private theorem AnalyticRootCover.extendSection_apply (S : TopologicalSpace.Opens ℂ)
    (V : TopologicalSpace.Opens S) (s : V → ℂ) (x : V) :
    extendSection S V s (ambientVal S V x) = s x :=
  (ambientVal_injective S V).extend_apply s 0 x

private theorem AnalyticRootCover.extendSection_agrees (S : TopologicalSpace.Opens ℂ)
    (V : TopologicalSpace.Opens S) (s : V → ℂ) (f : ℂ → ℂ)
    (hf : ∀ x, s x = f (ambientVal S V x)) : Set.EqOn (extendSection S V s) f (ambientOpen S V) :=
  by
  intro z hz
  obtain ⟨x, rfl⟩ := (mem_ambientOpen S V).mp hz
  rw [extendSection_apply]
  exact hf x

private theorem AnalyticRootCover.extension_agreement (S : TopologicalSpace.Opens ℂ)
    (V : TopologicalSpace.Opens S) (f : ℂ → ℂ) :
    Set.EqOn (extendSection S V (fun x => f (ambientVal S V x))) f (ambientOpen S V) :=
  extendSection_agrees S V _ f (fun _ => rfl)

private theorem AnalyticRootCover.extendSection_restrict_agrees (S : TopologicalSpace.Opens ℂ)
    {U V : TopologicalSpace.Opens S} (i : U ⟶ V) (s : V → ℂ) :
    Set.EqOn (extendSection S U (fun x => s (Set.inclusion i.le x))) (extendSection S V s)
      (ambientOpen S U) := by
  intro z hz
  obtain ⟨x, rfl⟩ := (mem_ambientOpen S U).mp hz
  rw [extendSection_apply]
  exact (extendSection_apply S V s (Set.inclusion i.le x)).symm

private theorem AnalyticRootCover.extendSection_restrict_eventuallyEq (S : TopologicalSpace.Opens ℂ)
    {U V : TopologicalSpace.Opens S} (i : U ⟶ V) (s : V → ℂ) (x : U) :
    extendSection S U (fun y => s (Set.inclusion i.le y)) =ᶠ[𝓝 (ambientVal S U x)]
      extendSection S V s := by
  filter_upwards [(ambientOpen S U).isOpen.mem_nhds (ambientVal_mem S U x)] with z hz
  exact extendSection_restrict_agrees S i s hz

private def AnalyticRootCover.IsRootSection (S : TopologicalSpace.Opens ℂ) (F : ℂ → ℂ)
    {V : TopologicalSpace.Opens S} (s : V → ℂ) : Prop :=
  ∀ x : V, AnalyticAt ℂ (extendSection S V s) (ambientVal S V x) ∧ s x ^ 2 = F (ambientVal S V x)

private def AnalyticRootCover.rootLocalPredicate (S : TopologicalSpace.Opens ℂ) (F : ℂ → ℂ) :
    TopCat.LocalPredicate (fun _ : TopCat.of S => ℂ)
    where
  pred {_} s := IsRootSection S F s
  res {_ _} i s
    hs := by
    intro x
    refine ⟨?_, (hs (Set.inclusion i.le x)).2⟩
    exact (hs (Set.inclusion i.le x)).1.congr (extendSection_restrict_eventuallyEq S i s x).symm
  locality {U} s
    hs := by
    intro x
    obtain ⟨V, hxV, i, hV⟩ := hs x
    let y : V := ⟨(x : S), hxV⟩
    have hix : Set.inclusion i.le y = x := Subtype.ext rfl
    refine ⟨?_, ?_⟩
    · exact (hV y).1.congr (extendSection_restrict_eventuallyEq S i s y)
    · have hsq : s (Set.inclusion i.le y) ^ 2 = F (ambientVal S U x) := (hV y).2
      rwa [hix] at hsq

private def AnalyticRootCover.rootPresheaf (S : TopologicalSpace.Opens ℂ) (F : ℂ → ℂ) :
    (TopCat.of S).Presheaf (Type 0) :=
  TopCat.subpresheafToTypes (rootLocalPredicate S F).toPrelocalPredicate

private abbrev AnalyticRootCover.RootSection (S : TopologicalSpace.Opens ℂ) (F : ℂ → ℂ)
    (V : TopologicalSpace.Opens S) :=
  (rootPresheaf S F).obj (Opposite.op V)

private theorem AnalyticRootCover.rootSection_analytic (S : TopologicalSpace.Opens ℂ) (F : ℂ → ℂ)
    {V : TopologicalSpace.Opens S} (s : RootSection S F V) (x : V) :
    AnalyticAt ℂ (extendSection S V s.1) (ambientVal S V x) :=
  (s.2 x).1

private theorem AnalyticRootCover.rootSection_sq (S : TopologicalSpace.Opens ℂ) (F : ℂ → ℂ)
    {V : TopologicalSpace.Opens S} (s : RootSection S F V) (x : V) :
    s.1 x ^ 2 = F (ambientVal S V x) :=
  (s.2 x).2

@[simp]
private theorem AnalyticRootCover.rootPresheaf_map_apply (S : TopologicalSpace.Opens ℂ) (F : ℂ → ℂ)
    {U V : TopologicalSpace.Opens S} (i : U ⟶ V) (s : RootSection S F V) (x : U) :
    ((rootPresheaf S F).map i.op s).1 x = s.1 (Set.inclusion i.le x) :=
  rfl

private theorem AnalyticRootCover.RootSection.analyticOnNhd_extend {S : TopologicalSpace.Opens ℂ}
    {F : ℂ → ℂ} {V : TopologicalSpace.Opens S} (s : AnalyticRootCover.RootSection S F V) :
    AnalyticOnNhd ℂ (AnalyticRootCover.extendSection S V s.1)
      (AnalyticRootCover.ambientOpen S V) := by
  intro z hz
  obtain ⟨x, rfl⟩ := (AnalyticRootCover.mem_ambientOpen S V).mp hz
  exact AnalyticRootCover.rootSection_analytic S F s x

private theorem AnalyticRootCover.RootSection.square_eq {S : TopologicalSpace.Opens ℂ} {F : ℂ → ℂ}
    {V : TopologicalSpace.Opens S} (s : AnalyticRootCover.RootSection S F V) {z : ℂ}
    (hz : z ∈ AnalyticRootCover.ambientOpen S V) :
    AnalyticRootCover.extendSection S V s.1 z ^ 2 = F z := by
  obtain ⟨x, rfl⟩ := (AnalyticRootCover.mem_ambientOpen S V).mp hz
  rw [AnalyticRootCover.extendSection_apply]
  exact AnalyticRootCover.rootSection_sq S F s x

@[ext]
private theorem AnalyticRootCover.RootSection.ext {S : TopologicalSpace.Opens ℂ} {F : ℂ → ℂ}
    {V : TopologicalSpace.Opens S} {s t : AnalyticRootCover.RootSection S F V}
    (he : ∀ x, s.1 x = t.1 x) : s = t :=
  Subtype.ext (funext he)

private def AnalyticRootCover.rootSectionOfAnalytic (S : TopologicalSpace.Opens ℂ) (F : ℂ → ℂ)
    {V : TopologicalSpace.Opens S} (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (ambientOpen S V))
    (hsq : ∀ x : V, f (ambientVal S V x) ^ 2 = F (ambientVal S V x)) : RootSection S F V := by
  refine ⟨fun x => f (ambientVal S V x), fun x => ⟨?_, hsq x⟩⟩
  apply (hf _ (ambientVal_mem S V x)).congr
  filter_upwards [(ambientOpen S V).isOpen.mem_nhds (ambientVal_mem S V x)] with z hz
  exact (extension_agreement S V f hz).symm

private theorem AnalyticRootCover.extend_rootSectionOfAnalytic_eqOn (S : TopologicalSpace.Opens ℂ)
    (F : ℂ → ℂ) {V : TopologicalSpace.Opens S} (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (ambientOpen S V))
    (hsq : ∀ x : V, f (ambientVal S V x) ^ 2 = F (ambientVal S V x)) :
    Set.EqOn (extendSection S V (rootSectionOfAnalytic S F f hf hsq).1) f (ambientOpen S V) :=
  extension_agreement S V f

private def SpecialPeriods.ModularGermLift.extendLiftSection (S : TopologicalSpace.Opens ℂ)
    (V : TopologicalSpace.Opens S) (s : V → ℍ) : ℂ → ℂ :=
  AnalyticRootCover.extendSection S V (fun x => (s x : ℂ))

@[simp]
private theorem
    SpecialPeriods.ModularGermLift.extendLiftSection_apply (S : TopologicalSpace.Opens ℂ)
    (V : TopologicalSpace.Opens S) (s : V → ℍ) (x : V) :
    extendLiftSection S V s (AnalyticRootCover.ambientVal S V x) = (s x : ℂ) :=
  AnalyticRootCover.extendSection_apply S V (fun y => (s y : ℂ)) x

private theorem SpecialPeriods.ModularGermLift.extendLiftSection_restrict_eventuallyEq
    (S : TopologicalSpace.Opens ℂ) {U V : TopologicalSpace.Opens S} (i : U ⟶ V) (s : V → ℍ)
    (x : U) :
    extendLiftSection S U
        (fun y => s (Set.inclusion i.le y)) =ᶠ[𝓝 (AnalyticRootCover.ambientVal S U x)]
      extendLiftSection S V s :=
  AnalyticRootCover.extendSection_restrict_eventuallyEq S i (fun y => (s y : ℂ)) x

private def SpecialPeriods.ModularGermLift.IsLiftSection (S : TopologicalSpace.Opens ℂ) (F : ℂ → ℂ)
    {V : TopologicalSpace.Opens S} (s : V → ℍ) : Prop :=
  ∀ x : V,
    AnalyticAt ℂ (extendLiftSection S V s) (AnalyticRootCover.ambientVal S V x) ∧
      SpecialPeriods.modularJ (s x) = F (AnalyticRootCover.ambientVal S V x)

private def
    SpecialPeriods.ModularGermLift.liftLocalPredicate (S : TopologicalSpace.Opens ℂ) (F : ℂ → ℂ) :
    TopCat.LocalPredicate (fun _ : TopCat.of S => ℍ)
    where
  pred {_} s := IsLiftSection S F s
  res {_ _} i s
    hs := by
    intro x
    refine ⟨?_, (hs (Set.inclusion i.le x)).2⟩
    exact
      (hs (Set.inclusion i.le x)).1.congr (extendLiftSection_restrict_eventuallyEq S i s x).symm
  locality {U} s
    hs := by
    intro x
    obtain ⟨V, hxV, i, hV⟩ := hs x
    let y : V := ⟨(x : S), hxV⟩
    have hix : Set.inclusion i.le y = x := Subtype.ext rfl
    refine ⟨?_, ?_⟩
    · exact (hV y).1.congr (extendLiftSection_restrict_eventuallyEq S i s y)
    · have he :
        SpecialPeriods.modularJ (s (Set.inclusion i.le y)) =
          F (AnalyticRootCover.ambientVal S U x) :=
        (hV y).2
      rwa [hix] at he

private def SpecialPeriods.ModularGermLift.liftPresheaf (S : TopologicalSpace.Opens ℂ) (F : ℂ → ℂ) :
    (TopCat.of S).Presheaf (Type 0) :=
  TopCat.subpresheafToTypes (liftLocalPredicate S F).toPrelocalPredicate

private abbrev SpecialPeriods.ModularGermLift.LiftSection (S : TopologicalSpace.Opens ℂ) (F : ℂ → ℂ)
    (V : TopologicalSpace.Opens S) :=
  (liftPresheaf S F).obj (Opposite.op V)

private theorem SpecialPeriods.ModularGermLift.liftSection_analytic (S : TopologicalSpace.Opens ℂ)
    (F : ℂ → ℂ) {V : TopologicalSpace.Opens S} (s : LiftSection S F V) (x : V) :
    AnalyticAt ℂ (extendLiftSection S V s.1) (AnalyticRootCover.ambientVal S V x) :=
  (s.2 x).1

private theorem SpecialPeriods.ModularGermLift.liftSection_modular (S : TopologicalSpace.Opens ℂ)
    (F : ℂ → ℂ) {V : TopologicalSpace.Opens S} (s : LiftSection S F V) (x : V) :
    SpecialPeriods.modularJ (s.1 x) = F (AnalyticRootCover.ambientVal S V x) :=
  (s.2 x).2

@[simp]
private theorem SpecialPeriods.ModularGermLift.liftPresheaf_map_apply (S : TopologicalSpace.Opens ℂ)
    (F : ℂ → ℂ) {U V : TopologicalSpace.Opens S} (i : U ⟶ V) (s : LiftSection S F V) (x : U) :
    ((liftPresheaf S F).map i.op s).1 x = s.1 (Set.inclusion i.le x) :=
  rfl

private theorem SpecialPeriods.ModularGermLift.LiftSection.analyticOnNhd_extend
    {S : TopologicalSpace.Opens ℂ} {F : ℂ → ℂ} {V : TopologicalSpace.Opens S}
    (s : SpecialPeriods.ModularGermLift.LiftSection S F V) :
    AnalyticOnNhd ℂ (SpecialPeriods.ModularGermLift.extendLiftSection S V s.1)
      (AnalyticRootCover.ambientOpen S V) := by
  intro z hz
  obtain ⟨x, rfl⟩ := (AnalyticRootCover.mem_ambientOpen S V).mp hz
  exact SpecialPeriods.ModularGermLift.liftSection_analytic S F s x

private theorem
    SpecialPeriods.ModularGermLift.LiftSection.mapsTo_extend {S : TopologicalSpace.Opens ℂ}
    {F : ℂ → ℂ} {V : TopologicalSpace.Opens S}
    (s : SpecialPeriods.ModularGermLift.LiftSection S F V) :
    Set.MapsTo (SpecialPeriods.ModularGermLift.extendLiftSection S V s.1)
      (AnalyticRootCover.ambientOpen S V) UpperHalfPlane.upperHalfPlaneSet := by
  intro z hz
  obtain ⟨x, rfl⟩ := (AnalyticRootCover.mem_ambientOpen S V).mp hz
  rw [SpecialPeriods.ModularGermLift.extendLiftSection_apply]
  exact (s.1 x).im_pos

private theorem SpecialPeriods.ModularGermLift.LiftSection.modular_eq {S : TopologicalSpace.Opens ℂ}
    {F : ℂ → ℂ} {V : TopologicalSpace.Opens S}
    (s : SpecialPeriods.ModularGermLift.LiftSection S F V) {z : ℂ}
    (hz : z ∈ AnalyticRootCover.ambientOpen S V) :
    SpecialPeriods.modularJ
        (UpperHalfPlane.ofComplex (SpecialPeriods.ModularGermLift.extendLiftSection S V s.1 z)) =
      F z := by
  obtain ⟨x, rfl⟩ := (AnalyticRootCover.mem_ambientOpen S V).mp hz
  rw [SpecialPeriods.ModularGermLift.extendLiftSection_apply, UpperHalfPlane.ofComplex_apply]
  exact SpecialPeriods.ModularGermLift.liftSection_modular S F s x

@[ext]
private theorem
    SpecialPeriods.ModularGermLift.LiftSection.ext {S : TopologicalSpace.Opens ℂ} {F : ℂ → ℂ}
    {V : TopologicalSpace.Opens S} {s t : SpecialPeriods.ModularGermLift.LiftSection S F V}
    (he : ∀ x, s.1 x = t.1 x) : s = t :=
  Subtype.ext (funext he)

private def
    SpecialPeriods.ModularGermLift.liftSectionOfComplex (S : TopologicalSpace.Opens ℂ) (F : ℂ → ℂ)
    {V : TopologicalSpace.Opens S} (r : ℂ → ℂ)
    (hr : AnalyticOnNhd ℂ r (AnalyticRootCover.ambientOpen S V))
    (hpos : Set.MapsTo r (AnalyticRootCover.ambientOpen S V) UpperHalfPlane.upperHalfPlaneSet)
    (hJ :
      Set.EqOn (fun z => SpecialPeriods.modularJ (UpperHalfPlane.ofComplex (r z))) F
        (AnalyticRootCover.ambientOpen S V)) :
    LiftSection S F V := by
  refine
    ⟨fun x =>
      ⟨r (AnalyticRootCover.ambientVal S V x), hpos (AnalyticRootCover.ambientVal_mem S V x)⟩,
      fun x => ⟨?_, ?_⟩⟩
  · apply (hr _ (AnalyticRootCover.ambientVal_mem S V x)).congr
    filter_upwards [(AnalyticRootCover.ambientOpen S V).isOpen.mem_nhds
        (AnalyticRootCover.ambientVal_mem S V x)] with
      z hz
    exact (AnalyticRootCover.extension_agreement S V r hz).symm
  · simpa only [UpperHalfPlane.ofComplex_apply_of_im_pos
          (hpos (AnalyticRootCover.ambientVal_mem S V x))] using
      hJ (AnalyticRootCover.ambientVal_mem S V x)

private theorem SpecialPeriods.ModularGermLift.extend_liftSectionOfComplex_eqOn
    (S : TopologicalSpace.Opens ℂ) (F : ℂ → ℂ) {V : TopologicalSpace.Opens S} (r : ℂ → ℂ)
    (hr : AnalyticOnNhd ℂ r (AnalyticRootCover.ambientOpen S V))
    (hpos : Set.MapsTo r (AnalyticRootCover.ambientOpen S V) UpperHalfPlane.upperHalfPlaneSet)
    (hJ :
      Set.EqOn (fun z => SpecialPeriods.modularJ (UpperHalfPlane.ofComplex (r z))) F
        (AnalyticRootCover.ambientOpen S V)) :
    Set.EqOn (extendLiftSection S V (liftSectionOfComplex S F r hr hpos hJ).1) r
      (AnalyticRootCover.ambientOpen S V) :=
  AnalyticRootCover.extension_agreement S V r

private theorem
    SpecialPeriods.ModularGermLift.germ_eq_iff_eventuallyEq (S : TopologicalSpace.Opens ℂ)
    (F : ℂ → ℂ) {U V : TopologicalSpace.Opens (TopCat.of S)} (x : S) (hxU : x ∈ U) (hxV : x ∈ V)
    (s : LiftSection S F U) (t : LiftSection S F V) :
    (liftPresheaf S F).germ U x hxU s = (liftPresheaf S F).germ V x hxV t ↔
      extendLiftSection S U s.1 =ᶠ[𝓝 (x : ℂ)] extendLiftSection S V t.1 := by
  constructor
  · intro h
    obtain ⟨W, hxW, iU, iV, hst⟩ := (liftPresheaf S F).germ_eq x hxU hxV s t h
    have hxA : (x : ℂ) ∈ AnalyticRootCover.ambientOpen S W :=
      AnalyticRootCover.ambientVal_mem S W ⟨x, hxW⟩
    filter_upwards [(AnalyticRootCover.ambientOpen S W).isOpen.mem_nhds hxA] with z hz
    obtain ⟨y, hyW, rfl⟩ := hz
    have hval := congrArg (fun r : LiftSection S F W => r.1 ⟨y, hyW⟩) hst
    rw [liftPresheaf_map_apply, liftPresheaf_map_apply] at hval
    calc
      extendLiftSection S U s.1 (y : ℂ) = (s.1 (Set.inclusion iU.le ⟨y, hyW⟩) : ℂ) :=
        extendLiftSection_apply S U s.1 (Set.inclusion iU.le ⟨y, hyW⟩)
      _ = (t.1 (Set.inclusion iV.le ⟨y, hyW⟩) : ℂ) := (congrArg (fun w : ℍ => (w : ℂ)) hval)
      _ = extendLiftSection S V t.1 (y : ℂ) :=
        (extendLiftSection_apply S V t.1 (Set.inclusion iV.le ⟨y, hyW⟩)).symm
  · intro h
    obtain ⟨A, hA, hAo, hxA⟩ := mem_nhds_iff.mp h
    let B : TopologicalSpace.Opens (TopCat.of S) :=
      TopologicalSpace.Opens.comap ⟨Subtype.val, continuous_subtype_val⟩ ⟨A, hAo⟩
    let W : TopologicalSpace.Opens (TopCat.of S) := (U ⊓ V) ⊓ B
    have hxW : x ∈ W := ⟨⟨hxU, hxV⟩, hxA⟩
    let iU : W ⟶ U := CategoryTheory.homOfLE (inf_le_left.trans inf_le_left)
    let iV : W ⟶ V := CategoryTheory.homOfLE (inf_le_left.trans inf_le_right)
    apply (liftPresheaf S F).germ_ext W hxW iU iV
    apply Subtype.ext
    funext y
    rw [liftPresheaf_map_apply, liftPresheaf_map_apply]
    apply UpperHalfPlane.coe_injective
    calc
      (s.1 (Set.inclusion iU.le y) : ℂ) =
          extendLiftSection S U s.1 (AnalyticRootCover.ambientVal S W y) :=
        (extendLiftSection_apply S U s.1 (Set.inclusion iU.le y)).symm
      _ = extendLiftSection S V t.1 (AnalyticRootCover.ambientVal S W y) := (hA y.2.2)
      _ = (t.1 (Set.inclusion iV.le y) : ℂ) :=
        extendLiftSection_apply S V t.1 (Set.inclusion iV.le y)

private theorem
    SpecialPeriods.exists_analytic_lift_through_power_chart {F G : ℂ → ℂ} {a b : ℂ} {m k : ℕ}
    (hF : AnalyticAt ℂ F a) (horder : analyticOrderAt F a = (m * k : ℕ)) (hm : 0 < m) (hk : 0 < k)
    (e : OpenPartialHomeomorph ℂ ℂ) (hb : b ∈ e.source) (he : e b = 0)
    (hf : AnalyticOnNhd ℂ e e.source) (hi : AnalyticOnNhd ℂ e.symm e.target)
    (hG : ∀ z ∈ e.target, G (e.symm z) = z ^ m) :
    ∃ r : ℝ,
      0 < r ∧
        ∃ τ : ℂ → ℂ,
          AnalyticOnNhd ℂ τ (Metric.ball a r) ∧
            τ a = b ∧
              Set.MapsTo τ (Metric.ball a r) e.source ∧
                (∀ z ∈ Metric.ball a r, G (τ z) = F z) ∧
                  analyticOrderAt (fun z => τ z - b) a = (k : ℕ∞) := by
  obtain ⟨d, ha, hd, hdf, hdi, hp⟩ := exists_analytic_power_chart hF horder (Nat.mul_pos hm hk)
  have ht : (0 : ℂ) ∈ e.target := he ▸ e.map_source hb
  have hc : ContinuousAt (fun z : ℂ => d z ^ k) a := (hdf a ha).continuousAt.pow k
  have hnear : ∀ᶠ z : ℂ in 𝓝 a, d z ^ k ∈ e.target := by
    apply hc.preimage_mem_nhds
    simpa only [hd, zero_pow hk.ne'] using e.open_target.mem_nhds ht
  have hsrc : ∀ᶠ z : ℂ in 𝓝 a, z ∈ d.source := d.open_source.mem_nhds ha
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hsrc.and hnear)
  refine ⟨r, hr, fun z => e.symm (d z ^ k), ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact (hi _ (hball hz).2).comp (f := fun w : ℂ => d w ^ k) ((hdf z (hball hz).1).pow k)
  · change e.symm (d a ^ k) = b
    rw [hd, zero_pow hk.ne', ← he, e.left_inv hb]
  · intro z hz
    exact e.map_target (hball hz).2
  · intro z hz
    change G (e.symm (d z ^ k)) = F z
    rw [hG _ (hball hz).2, hp _ (hball hz).1, ← pow_mul, Nat.mul_comm k m]
  · calc
      analyticOrderAt (fun z => e.symm (d z ^ k) - b) a =
          analyticOrderAt (fun z : ℂ => e.symm (z ^ k) - b) (d a) :=
        analyticOrderAt_comp_of_deriv_ne_zero (f := fun z : ℂ => e.symm (z ^ k) - b) (hdf a ha)
          (analytic_chart_deriv_ne_zero d ha hdf hdi)
      _ = (k : ℕ∞) := by
        rw [hd]
        simpa only [one_mul] using
          analytic_chart_inverse_power_order e hb he hf hi 1 one_ne_zero k hk

private theorem
    SpecialPeriods.exists_modularJ_lift_of_order_multiple_three {F : ℂ → ℂ} {a : ℂ} {k : ℕ}
    (hF : AnalyticAt ℂ F a) (horder : analyticOrderAt F a = (3 * k : ℕ)) (hk : 0 < k) :
    ∃ r : ℝ,
      0 < r ∧
        ∃ τ : ℂ → ℂ,
          AnalyticOnNhd ℂ τ (Metric.ball a r) ∧
            τ a = rho ∧
              Set.MapsTo τ (Metric.ball a r) UpperHalfPlane.upperHalfPlaneSet ∧
                (∀ z ∈ Metric.ball a r, modularJ (UpperHalfPlane.ofComplex (τ z)) = F z) ∧
                  analyticOrderAt (fun z => τ z - rho) a = (k : ℕ∞) := by
  obtain ⟨e, hb, he, hU, hf, hi, _, hp⟩ := modularJ_rhoPoint_cubic_chart
  obtain ⟨r, hr, τ, hτ, hτa, hτU, hτj, hτord⟩ :=
    exists_analytic_lift_through_power_chart (G := fun w => modularJ (UpperHalfPlane.ofComplex w))
      hF horder (by decide : 0 < 3) hk e hb he hf hi hp
  exact ⟨r, hr, τ, hτ, hτa, fun z hz => hU (hτU hz), hτj, hτord⟩

private theorem
    SpecialPeriods.exists_modularJ_lift_of_order_multiple_two {F : ℂ → ℂ} {a : ℂ} {k : ℕ}
    (hF : AnalyticAt ℂ F a) (horder : analyticOrderAt (fun z => F z - 1728) a = (2 * k : ℕ))
    (hk : 0 < k) :
    ∃ r : ℝ,
      0 < r ∧
        ∃ τ : ℂ → ℂ,
          AnalyticOnNhd ℂ τ (Metric.ball a r) ∧
            τ a = Complex.I ∧
              Set.MapsTo τ (Metric.ball a r) UpperHalfPlane.upperHalfPlaneSet ∧
                (∀ z ∈ Metric.ball a r, modularJ (UpperHalfPlane.ofComplex (τ z)) = F z) ∧
                  analyticOrderAt (fun z => τ z - Complex.I) a = (k : ℕ∞) := by
  obtain ⟨e, hb, he, hU, hf, hi, _, hp⟩ := modularJ_I_quadratic_chart
  obtain ⟨r, hr, τ, hτ, hτa, hτU, hτj, hτord⟩ :=
    exists_analytic_lift_through_power_chart (G := fun w =>
      modularJ (UpperHalfPlane.ofComplex w) - 1728) (hF.sub analyticAt_const) horder
      (by decide : 0 < 2) hk e hb he hf hi hp
  refine ⟨r, hr, τ, hτ, hτa, fun z hz => hU (hτU hz), ?_, hτord⟩
  intro z hz
  exact sub_left_inj.mp (hτj z hz)

private theorem SpecialPeriods.ModularGermLift.exists_regular_local_lift_at {F : ℂ → ℂ} {a : ℂ}
    (hF : AnalyticAt ℂ F a) (b : ℍ) (hb : SpecialPeriods.modularJ b = F a) (h₀ : F a ≠ 0)
    (h₁ : F a ≠ 1728) :
    ∃ r : ℝ,
      0 < r ∧
        ∃ τ : ℂ → ℂ,
          AnalyticOnNhd ℂ τ (Metric.ball a r) ∧
            τ a = (b : ℂ) ∧
              Set.MapsTo τ (Metric.ball a r) UpperHalfPlane.upperHalfPlaneSet ∧
                ∀ z ∈ Metric.ball a r,
                  SpecialPeriods.modularJ (UpperHalfPlane.ofComplex (τ z)) = F z := by
  have hb₀ : SpecialPeriods.modularJ b ≠ 0 := hb ▸ h₀
  have hb₁ : SpecialPeriods.modularJ b ≠ 1728 := hb ▸ h₁
  let g : ℂ → ℂ := SpecialPeriods.modularLocalInverse b hb₀ hb₁
  let τ : ℂ → ℂ := fun z => g (F z)
  have hg : AnalyticAt ℂ g (F a) := by
    rw [← hb]
    exact SpecialPeriods.modularLocalInverse_analyticAt b hb₀ hb₁
  have hτ : AnalyticAt ℂ τ a := hg.comp hF
  have hτa : τ a = (b : ℂ) := by
    dsimp only [τ]
    rw [← hb]
    simpa only [UpperHalfPlane.ofComplex_apply] using
      (SpecialPeriods.modularLocalInverse_eventually_left_inverse b hb₀ hb₁).self_of_nhds
  have hU : ∀ᶠ z in 𝓝 a, τ z ∈ UpperHalfPlane.upperHalfPlaneSet := by
    apply hτ.continuousAt.preimage_mem_nhds
    rw [hτa]
    exact UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds b.im_pos
  have hinv : ∀ᶠ w in 𝓝 (F a), SpecialPeriods.modularJ (UpperHalfPlane.ofComplex (g w)) = w := by
    rw [← hb]
    exact SpecialPeriods.modularLocalInverse_eventually_right_inverse b hb₀ hb₁
  have hj : ∀ᶠ z in 𝓝 a, SpecialPeriods.modularJ (UpperHalfPlane.ofComplex (τ z)) = F z :=
    hF.continuousAt.tendsto.eventually hinv
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hτ.eventually_analyticAt.and (hU.and hj))
  exact
    ⟨r, hr, τ, fun z hz => (hball hz).1, hτa, fun z hz => (hball hz).2.1, fun z hz =>
      (hball hz).2.2⟩

private theorem SpecialPeriods.ModularGermLift.exists_local_lift {F : ℂ → ℂ} {a : ℂ}
    (hF : AnalyticAt ℂ F a) (h₃ : F a = 0 → ∃ k : ℕ, analyticOrderAt F a = (3 * k : ℕ))
    (h₂ : F a = 1728 → ∃ k : ℕ, analyticOrderAt (fun z => F z - 1728) a = (2 * k : ℕ)) :
    ∃ r : ℝ,
      0 < r ∧
        ∃ τ : ℂ → ℂ,
          AnalyticOnNhd ℂ τ (Metric.ball a r) ∧
            Set.MapsTo τ (Metric.ball a r) UpperHalfPlane.upperHalfPlaneSet ∧
              ∀ z ∈ Metric.ball a r,
                SpecialPeriods.modularJ (UpperHalfPlane.ofComplex (τ z)) = F z := by
  by_cases ha₀ : F a = 0
  · obtain ⟨k, hk⟩ := h₃ ha₀
    have hkpos : 0 < k := by
      apply Nat.pos_of_ne_zero
      intro hk₀
      exact
        (hF.analyticOrderAt_ne_zero.mpr ha₀)
          (by simpa only [hk₀, MulZeroClass.mul_zero, Nat.cast_zero] using hk)
    obtain ⟨r, hr, τ, hτ, -, hU, hj, -⟩ :=
      SpecialPeriods.exists_modularJ_lift_of_order_multiple_three hF hk hkpos
    exact ⟨r, hr, τ, hτ, hU, hj⟩
  · by_cases ha₁ : F a = 1728
    · obtain ⟨k, hk⟩ := h₂ ha₁
      have hkpos : 0 < k := by
        apply Nat.pos_of_ne_zero
        intro hk₀
        have hshift : AnalyticAt ℂ (fun z => F z - 1728) a := hF.sub analyticAt_const
        have hn : analyticOrderAt (fun z => F z - 1728) a ≠ 0 :=
          hshift.analyticOrderAt_ne_zero.mpr (sub_eq_zero.mpr ha₁)
        exact hn (by simpa only [hk₀, MulZeroClass.mul_zero, Nat.cast_zero] using hk)
      obtain ⟨r, hr, τ, hτ, -, hU, hj, -⟩ :=
        SpecialPeriods.exists_modularJ_lift_of_order_multiple_two hF hk hkpos
      exact ⟨r, hr, τ, hτ, hU, hj⟩
    · obtain ⟨b, hb⟩ := SpecialPeriods.modularJ_surjective (F a)
      obtain ⟨r, hr, τ, hτ, -, hU, hj⟩ := exists_regular_local_lift_at hF b hb ha₀ ha₁
      exact ⟨r, hr, τ, hτ, hU, hj⟩

private theorem SpecialPeriods.ModularGermLift.exists_local_lift_ball_subset {F : ℂ → ℂ} {a : ℂ}
    {S : Set ℂ} (hS : IsOpen S) (ha : a ∈ S) (hF : AnalyticAt ℂ F a)
    (h₃ : F a = 0 → ∃ k : ℕ, analyticOrderAt F a = (3 * k : ℕ))
    (h₂ : F a = 1728 → ∃ k : ℕ, analyticOrderAt (fun z => F z - 1728) a = (2 * k : ℕ)) :
    ∃ r : ℝ,
      0 < r ∧
        Metric.ball a r ⊆ S ∧
          ∃ τ : ℂ → ℂ,
            AnalyticOnNhd ℂ τ (Metric.ball a r) ∧
              Set.MapsTo τ (Metric.ball a r) UpperHalfPlane.upperHalfPlaneSet ∧
                ∀ z ∈ Metric.ball a r,
                  SpecialPeriods.modularJ (UpperHalfPlane.ofComplex (τ z)) = F z := by
  obtain ⟨r, hr, τ, hτ, hU, hj⟩ := exists_local_lift hF h₃ h₂
  obtain ⟨s, hs, hsS⟩ := Metric.mem_nhds_iff.mp (hS.mem_nhds ha)
  have hsub : Metric.ball a (Min.min r s) ⊆ Metric.ball a r :=
    Metric.ball_subset_ball (min_le_left _ _)
  refine
    ⟨Min.min r s, lt_min hr hs, (Metric.ball_subset_ball (min_le_right _ _)).trans hsS, τ,
      hτ.mono hsub, ?_, ?_⟩
  · exact hU.mono_left hsub
  · exact fun z hz => hj z (hsub hz)

private theorem
    AnalyticRootCover.eventuallyEq_zero_or_eventuallyEq_zero_of_mul_eq_zero {r s : ℂ → ℂ}
    {a : ℂ} (hr : AnalyticAt ℂ r a) (hs : AnalyticAt ℂ s a) (hmul : ∀ᶠ z in 𝓝 a, r z * s z = 0) :
    r =ᶠ[𝓝 a] 0 ∨ s =ᶠ[𝓝 a] 0 := by
  have hfrequent : ∃ᶠ z in 𝓝[≠] a, r z = 0 ∨ s z = 0 := by
    apply (hmul.filter_mono nhdsWithin_le_nhds).frequently.mono
    intro z hz
    exact mul_eq_zero.mp hz
  rcases Filter.frequently_or_distrib.mp hfrequent with hrzero | hszero
  · exact Or.inl (hr.frequently_zero_iff_eventually_zero.mp hrzero)
  · exact Or.inr (hs.frequently_zero_iff_eventually_zero.mp hszero)

private theorem AnalyticRootCover.eventuallyEq_or_neg_of_sq_eq {r s : ℂ → ℂ} {a : ℂ}
    (hr : AnalyticAt ℂ r a) (hs : AnalyticAt ℂ s a)
    (hsq : (fun z => r z ^ 2) =ᶠ[𝓝 a] (fun z => s z ^ 2)) :
    r =ᶠ[𝓝 a] s ∨ r =ᶠ[𝓝 a] (fun z => -s z) := by
  have hmul : ∀ᶠ z in 𝓝 a, (r - s) z * (r + s) z = 0 := by
    filter_upwards [hsq] with z hz
    calc
      (r - s) z * (r + s) z = r z ^ 2 - s z ^ 2 := by dsimp; ring
      _ = 0 := sub_eq_zero.mpr hz
  rcases eventuallyEq_zero_or_eventuallyEq_zero_of_mul_eq_zero (hr.sub hs) (hr.add hs) hmul with
    hsub | hadd
  · exact Or.inl (hsub.mono fun z hz => sub_eq_zero.mp hz)
  · exact Or.inr (hadd.mono fun z hz => eq_neg_iff_add_eq_zero.mpr hz)

private theorem AnalyticRootCover.eqOn_of_eventuallyEq {r s : ℂ → ℂ} {V : Set ℂ} {a : ℂ}
    (hr : AnalyticOnNhd ℂ r V) (hs : AnalyticOnNhd ℂ s V) (hV : IsPreconnected V) (ha : a ∈ V)
    (heq : r =ᶠ[𝓝 a] s) : Set.EqOn r s V :=
  hr.eqOn_of_preconnected_of_eventuallyEq hs hV ha heq

private theorem AnalyticRootCover.exists_analytic_square_root {F : ℂ → ℂ} {a : ℂ} {n : ℕ}
    (hF : AnalyticAt ℂ F a) (horder : analyticOrderAt F a = (2 * n : ℕ)) :
    ∃ r : ℂ → ℂ, AnalyticAt ℂ r a ∧ (∀ᶠ z in 𝓝 a, r z ^ 2 = F z) ∧ analyticOrderAt r a = n := by
  obtain ⟨u, hu, hua, hFu⟩ := hF.analyticOrderAt_eq_natCast.mp horder
  obtain ⟨q, hq, hqa, hqpow⟩ :=
    SpecialPeriods.exists_analytic_unit_root hu hua (by norm_num : 0 < (2 : ℕ))
  let r : ℂ → ℂ := fun z => (z - a) ^ n * q z
  have hr : AnalyticAt ℂ r a := ((analyticAt_id.sub analyticAt_const).pow n).mul hq
  refine ⟨r, hr, ?_, ?_⟩
  · filter_upwards [hFu, hqpow] with z hFz hqz
    change ((z - a) ^ n * q z) ^ 2 = F z
    rw [mul_pow, hqz, ← pow_mul, Nat.mul_comm n 2]
    simpa only [smul_eq_mul] using hFz.symm
  · apply hr.analyticOrderAt_eq_natCast.mpr
    refine ⟨q, hq, hqa, ?_⟩
    exact Filter.Eventually.of_forall (fun _ => rfl)

private theorem
    AnalyticRootCover.exists_analytic_square_root_ball {F : ℂ → ℂ} {a : ℂ} {n : ℕ} {S : Set ℂ}
    (hF : AnalyticAt ℂ F a) (horder : analyticOrderAt F a = (2 * n : ℕ)) (hS : S ∈ 𝓝 a) :
    ∃ ε > 0,
      ∃ r : ℂ → ℂ,
        Metric.ball a ε ⊆ S ∧
          AnalyticOnNhd ℂ r (Metric.ball a ε) ∧
            Set.EqOn (fun z => r z ^ 2) F (Metric.ball a ε) ∧ analyticOrderAt r a = n := by
  obtain ⟨r, hr, hroot, horderR⟩ := exists_analytic_square_root hF horder
  have hn : {z | z ∈ S ∧ AnalyticAt ℂ r z ∧ r z ^ 2 = F z} ∈ 𝓝 a :=
    Filter.Eventually.and hS (hr.eventually_analyticAt.and hroot)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨ε, hε, r, ?_, ?_, ?_, horderR⟩
  · exact fun z hz => (hball hz).1
  · exact fun z hz => (hball hz).2.1
  · exact fun z hz => (hball hz).2.2

private theorem
    AnalyticRootCover.germ_eq_iff_eventuallyEq (S : TopologicalSpace.Opens ℂ) (F : ℂ → ℂ)
    {U V : TopologicalSpace.Opens (TopCat.of S)} (x : S) (hxU : x ∈ U) (hxV : x ∈ V)
    (s : RootSection S F U) (t : RootSection S F V) :
    (rootPresheaf S F).germ U x hxU s = (rootPresheaf S F).germ V x hxV t ↔
      extendSection S U s.1 =ᶠ[𝓝 (x : ℂ)] extendSection S V t.1 := by
  constructor
  · intro h
    obtain ⟨W, hxW, iU, iV, hst⟩ := (rootPresheaf S F).germ_eq x hxU hxV s t h
    have hxA : (x : ℂ) ∈ ambientOpen S W := ambientVal_mem S W ⟨x, hxW⟩
    filter_upwards [(ambientOpen S W).isOpen.mem_nhds hxA] with z hz
    obtain ⟨y, hyW, rfl⟩ := hz
    have hval := congrArg (fun r : RootSection S F W => r.1 ⟨y, hyW⟩) hst
    rw [rootPresheaf_map_apply, rootPresheaf_map_apply] at hval
    calc
      extendSection S U s.1 (y : ℂ) = s.1 (Set.inclusion iU.le ⟨y, hyW⟩) :=
        extendSection_apply S U s.1 (Set.inclusion iU.le ⟨y, hyW⟩)
      _ = t.1 (Set.inclusion iV.le ⟨y, hyW⟩) := hval
      _ = extendSection S V t.1 (y : ℂ) :=
        (extendSection_apply S V t.1 (Set.inclusion iV.le ⟨y, hyW⟩)).symm
  · intro h
    obtain ⟨A, hA, hAo, hxA⟩ := mem_nhds_iff.mp h
    let B : TopologicalSpace.Opens (TopCat.of S) :=
      TopologicalSpace.Opens.comap ⟨Subtype.val, continuous_subtype_val⟩ ⟨A, hAo⟩
    let W : TopologicalSpace.Opens (TopCat.of S) := (U ⊓ V) ⊓ B
    have hxW : x ∈ W := ⟨⟨hxU, hxV⟩, hxA⟩
    let iU : W ⟶ U := CategoryTheory.homOfLE (inf_le_left.trans inf_le_left)
    let iV : W ⟶ V := CategoryTheory.homOfLE (inf_le_left.trans inf_le_right)
    apply (rootPresheaf S F).germ_ext W hxW iU iV
    apply Subtype.ext
    funext y
    rw [rootPresheaf_map_apply, rootPresheaf_map_apply]
    calc
      s.1 (Set.inclusion iU.le y) = extendSection S U s.1 (ambientVal S W y) :=
        (extendSection_apply S U s.1 (Set.inclusion iU.le y)).symm
      _ = extendSection S V t.1 (ambientVal S W y) := (hA y.2.2)
      _ = t.1 (Set.inclusion iV.le y) := extendSection_apply S V t.1 (Set.inclusion iV.le y)

private def AnalyticRootCover.RootSection.neg {S : TopologicalSpace.Opens ℂ} {F : ℂ → ℂ}
    {U : TopologicalSpace.Opens S} (s : AnalyticRootCover.RootSection S F U) :
    AnalyticRootCover.RootSection S F U :=
  AnalyticRootCover.rootSectionOfAnalytic S F
    (fun z => -AnalyticRootCover.extendSection S U s.1 z) (analyticOnNhd_extend s).neg
    (fun x => by
      rw [neg_sq]
      exact square_eq s (AnalyticRootCover.ambientVal_mem S U x))

private theorem
    AnalyticRootCover.RootSection.extend_neg_eqOn {S : TopologicalSpace.Opens ℂ} {F : ℂ → ℂ}
    {U : TopologicalSpace.Opens S} (s : AnalyticRootCover.RootSection S F U) :
    Set.EqOn (AnalyticRootCover.extendSection S U s.neg.1)
      (fun z => -AnalyticRootCover.extendSection S U s.1 z) (AnalyticRootCover.ambientOpen S U) :=
  by exact AnalyticRootCover.extend_rootSectionOfAnalytic_eqOn S F _ _ _

private theorem AnalyticRootCover.germ_eq_or_neg {S : TopologicalSpace.Opens ℂ} {F : ℂ → ℂ}
    {U V : TopologicalSpace.Opens S} (x : S) (hxU : x ∈ U) (hxV : x ∈ V) (s : RootSection S F U)
    (t : RootSection S F V) :
    (rootPresheaf S F).germ V x hxV t = (rootPresheaf S F).germ U x hxU s ∨
      (rootPresheaf S F).germ V x hxV t = (rootPresheaf S F).germ U x hxU s.neg := by
  have hxUA : (x : ℂ) ∈ ambientOpen S U := (coe_mem_ambientOpen S U x).mpr hxU
  have hxVA : (x : ℂ) ∈ ambientOpen S V := (coe_mem_ambientOpen S V x).mpr hxV
  have hsquare :
    (fun z => extendSection S V t.1 z ^ 2) =ᶠ[𝓝 (x : ℂ)] (fun z => extendSection S U s.1 z ^ 2) :=
    by
    filter_upwards [(ambientOpen S U).isOpen.mem_nhds hxUA,
      (ambientOpen S V).isOpen.mem_nhds hxVA] with z hzU hzV
    exact (RootSection.square_eq t hzV).trans (RootSection.square_eq s hzU).symm
  rcases
    eventuallyEq_or_neg_of_sq_eq (RootSection.analyticOnNhd_extend t _ hxVA)
      (RootSection.analyticOnNhd_extend s _ hxUA) hsquare with
    hpos | hneg
  · exact Or.inl ((germ_eq_iff_eventuallyEq S F x hxV hxU t s).mpr hpos)
  · apply Or.inr
    apply (germ_eq_iff_eventuallyEq S F x hxV hxU t s.neg).mpr
    filter_upwards [hneg, (ambientOpen S U).isOpen.mem_nhds hxUA] with z hz hzU
    exact hz.trans (RootSection.extend_neg_eqOn s hzU).symm

private theorem AnalyticRootCover.germ_injective {S : TopologicalSpace.Opens ℂ} {F : ℂ → ℂ}
    {U : TopologicalSpace.Opens S} (hU : IsPreconnected (ambientOpen S U : Set ℂ)) (x : S)
    (hx : x ∈ U) : Function.Injective ((rootPresheaf S F).germ U x hx) := by
  intro s t hst
  have he :=
    eqOn_of_eventuallyEq (RootSection.analyticOnNhd_extend s) (RootSection.analyticOnNhd_extend t)
      hU ((coe_mem_ambientOpen S U x).mpr hx) ((germ_eq_iff_eventuallyEq S F x hx hx s t).mp hst)
  apply RootSection.ext
  intro y
  simpa only [extendSection_apply] using he (ambientVal_mem S U y)

private theorem AnalyticRootCover.germ_surjective {S : TopologicalSpace.Opens ℂ} {F : ℂ → ℂ}
    {U : TopologicalSpace.Opens S} (s : RootSection S F U) (x : S) (hx : x ∈ U) :
    Function.Surjective ((rootPresheaf S F).germ U x hx) := by
  intro g
  obtain ⟨V, hxV, t, ht⟩ := (rootPresheaf S F).exists_germ_eq g
  rcases germ_eq_or_neg x hx hxV s t with hpos | hneg
  · exact ⟨s, hpos.symm.trans ht⟩
  · exact ⟨s.neg, hneg.symm.trans ht⟩

private theorem AnalyticRootCover.germ_bijective {S : TopologicalSpace.Opens ℂ} {F : ℂ → ℂ}
    {U : TopologicalSpace.Opens S} (hU : IsPreconnected (ambientOpen S U : Set ℂ))
    (s : RootSection S F U) (x : S) (hx : x ∈ U) :
    Function.Bijective ((rootPresheaf S F).germ U x hx) :=
  ⟨germ_injective hU x hx, germ_surjective s x hx⟩

private theorem AnalyticRootCover.ambientOpen_comap_of_subset (S : TopologicalSpace.Opens ℂ)
    (A : TopologicalSpace.Opens ℂ) (hAS : A ≤ S) :
    ambientOpen S (TopologicalSpace.Opens.comap ⟨Subtype.val, continuous_subtype_val⟩ A) = A := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hz
    exact ⟨⟨z, hAS hz⟩, hz, rfl⟩

private theorem
    AnalyticRootCover.exists_root_neighborhood (S : TopologicalSpace.Opens ℂ) (F : ℂ → ℂ)
    (hF : AnalyticOnNhd ℂ F S) (horder : ∀ a ∈ S, ∃ n : ℕ, analyticOrderAt F a = (2 * n : ℕ))
    (x : S) :
    ∃ U : TopologicalSpace.Opens S,
      x ∈ U ∧ IsPreconnected (ambientOpen S U : Set ℂ) ∧ Nonempty (RootSection S F U) := by
  obtain ⟨n, hn⟩ := horder x x.2
  obtain ⟨ε, hε, r, hball, hr, hsquare, _⟩ :=
    exists_analytic_square_root_ball (hF x x.2) hn (S.isOpen.mem_nhds x.2)
  let A : TopologicalSpace.Opens ℂ := ⟨Metric.ball (x : ℂ) ε, Metric.isOpen_ball⟩
  let U : TopologicalSpace.Opens S :=
    TopologicalSpace.Opens.comap ⟨Subtype.val, continuous_subtype_val⟩ A
  have hUA : ambientOpen S U = A := ambientOpen_comap_of_subset S A hball
  have hxU : x ∈ U := Metric.mem_ball_self hε
  refine ⟨U, hxU, ?_, ?_⟩
  · rw [hUA]
    exact (convex_ball (x : ℂ) ε).isPreconnected
  · have hrU : AnalyticOnNhd ℂ r (ambientOpen S U) := by rwa [hUA]
    refine ⟨rootSectionOfAnalytic S F r hrU (fun y => hsquare ?_)⟩
    have hy := ambientVal_mem S U y
    rwa [hUA] at hy

private theorem AnalyticRootCover.rootPresheaf_locally_bijective (S : TopologicalSpace.Opens ℂ)
    (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F S)
    (horder : ∀ a ∈ S, ∃ n : ℕ, analyticOrderAt F a = (2 * n : ℕ)) :
    ∀ x : S,
      ∃ U : TopologicalSpace.Opens S,
        x ∈ U ∧ ∀ y (hy : y ∈ U), Function.Bijective ((rootPresheaf S F).germ U y hy) := by
  intro x
  obtain ⟨U, hx, hU, ⟨s⟩⟩ := exists_root_neighborhood S F hF horder x
  exact ⟨U, hx, fun y hy => germ_bijective hU s y hy⟩

private theorem AnalyticRootCover.rootStalk_nonempty (S : TopologicalSpace.Opens ℂ) (F : ℂ → ℂ)
    (hF : AnalyticOnNhd ℂ F S) (horder : ∀ a ∈ S, ∃ n : ℕ, analyticOrderAt F a = (2 * n : ℕ))
    (x : S) : Nonempty ((rootPresheaf S F).stalk x) := by
  obtain ⟨U, hx, _, ⟨s⟩⟩ := exists_root_neighborhood S F hF horder x
  exact ⟨(rootPresheaf S F).germ U x hx s⟩

private def
    SpecialPeriods.ModularGermLift.LiftSection.smul {S : TopologicalSpace.Opens ℂ} {F : ℂ → ℂ}
    {U : TopologicalSpace.Opens S} (s : SpecialPeriods.ModularGermLift.LiftSection S F U)
    (γ : SL(2, ℤ)) : SpecialPeriods.ModularGermLift.LiftSection S F U :=
  SpecialPeriods.ModularGermLift.liftSectionOfComplex S F
    (fun z =>
      ((γ •
            UpperHalfPlane.ofComplex
              (SpecialPeriods.ModularGermLift.extendLiftSection S U s.1 z) :
          ℍ) :
        ℂ))
    (SpecialPeriods.ModularGermLift.analyticOnNhd_modular_smul γ s.analyticOnNhd_extend
      s.mapsTo_extend)
    (fun _ _ => (γ • UpperHalfPlane.ofComplex _).im_pos)
    (fun _ hz =>
      (SpecialPeriods.ModularGermLift.modularJ_modular_smul γ _).trans (s.modular_eq hz))

private theorem
    SpecialPeriods.ModularGermLift.LiftSection.extend_smul_eqOn {S : TopologicalSpace.Opens ℂ}
    {F : ℂ → ℂ} {U : TopologicalSpace.Opens S}
    (s : SpecialPeriods.ModularGermLift.LiftSection S F U) (γ : SL(2, ℤ)) :
    Set.EqOn (SpecialPeriods.ModularGermLift.extendLiftSection S U (s.smul γ).1)
      (fun z =>
        ((γ •
              UpperHalfPlane.ofComplex
                (SpecialPeriods.ModularGermLift.extendLiftSection S U s.1 z) :
            ℍ) :
          ℂ))
      (AnalyticRootCover.ambientOpen S U) :=
  SpecialPeriods.ModularGermLift.extend_liftSectionOfComplex_eqOn S F _ _ _ _

private theorem
    SpecialPeriods.ModularGermLift.germ_eq_smul {S : TopologicalSpace.Opens ℂ} {F : ℂ → ℂ}
    {U V : TopologicalSpace.Opens S} (x : S) (hxU : x ∈ U) (hxV : x ∈ V) (s : LiftSection S F U)
    (t : LiftSection S F V) :
    ∃ γ : SL(2, ℤ),
      (liftPresheaf S F).germ V x hxV t = (liftPresheaf S F).germ U x hxU (s.smul γ) := by
  have hxUA : (x : ℂ) ∈ AnalyticRootCover.ambientOpen S U :=
    (AnalyticRootCover.coe_mem_ambientOpen S U x).mpr hxU
  have hxVA : (x : ℂ) ∈ AnalyticRootCover.ambientOpen S V :=
    (AnalyticRootCover.coe_mem_ambientOpen S V x).mpr hxV
  have hJ :
    (fun z =>
        SpecialPeriods.modularJ
          (UpperHalfPlane.ofComplex (extendLiftSection S V t.1 z))) =ᶠ[𝓝 (x : ℂ)]
      (fun z =>
        SpecialPeriods.modularJ (UpperHalfPlane.ofComplex (extendLiftSection S U s.1 z))) := by
    filter_upwards [(AnalyticRootCover.ambientOpen S U).isOpen.mem_nhds hxUA,
      (AnalyticRootCover.ambientOpen S V).isOpen.mem_nhds hxVA] with z hzU hzV
    exact (t.modular_eq hzV).trans (s.modular_eq hzU).symm
  obtain ⟨γ, hγ⟩ :=
    exists_modular_alignment_germ (t.analyticOnNhd_extend _ hxVA) (s.analyticOnNhd_extend _ hxUA)
      (t.mapsTo_extend hxVA) (s.mapsTo_extend hxUA) hJ
  refine ⟨γ, (germ_eq_iff_eventuallyEq S F x hxV hxU t (s.smul γ)).mpr ?_⟩
  filter_upwards [hγ, (AnalyticRootCover.ambientOpen S U).isOpen.mem_nhds hxUA] with z hz hzU
  exact hz.trans (s.extend_smul_eqOn γ hzU).symm

private theorem
    SpecialPeriods.ModularGermLift.germ_injective {S : TopologicalSpace.Opens ℂ} {F : ℂ → ℂ}
    {U : TopologicalSpace.Opens S}
    (hU : IsPreconnected (AnalyticRootCover.ambientOpen S U : Set ℂ)) (x : S) (hx : x ∈ U) :
    Function.Injective ((liftPresheaf S F).germ U x hx) := by
  intro s t hst
  have he :=
    AnalyticRootCover.eqOn_of_eventuallyEq (LiftSection.analyticOnNhd_extend s)
      (LiftSection.analyticOnNhd_extend t) hU
      ((AnalyticRootCover.coe_mem_ambientOpen S U x).mpr hx)
      ((germ_eq_iff_eventuallyEq S F x hx hx s t).mp hst)
  apply LiftSection.ext
  intro y
  apply UpperHalfPlane.coe_injective
  simpa only [extendLiftSection_apply] using he (AnalyticRootCover.ambientVal_mem S U y)

private theorem
    SpecialPeriods.ModularGermLift.germ_surjective {S : TopologicalSpace.Opens ℂ} {F : ℂ → ℂ}
    {U : TopologicalSpace.Opens S} (s : LiftSection S F U) (x : S) (hx : x ∈ U) :
    Function.Surjective ((liftPresheaf S F).germ U x hx) := by
  intro g
  obtain ⟨V, hxV, t, ht⟩ := (liftPresheaf S F).exists_germ_eq g
  obtain ⟨γ, hγ⟩ := germ_eq_smul x hx hxV s t
  exact ⟨s.smul γ, hγ.symm.trans ht⟩

private theorem
    SpecialPeriods.ModularGermLift.germ_bijective {S : TopologicalSpace.Opens ℂ} {F : ℂ → ℂ}
    {U : TopologicalSpace.Opens S}
    (hU : IsPreconnected (AnalyticRootCover.ambientOpen S U : Set ℂ)) (s : LiftSection S F U)
    (x : S) (hx : x ∈ U) : Function.Bijective ((liftPresheaf S F).germ U x hx) :=
  ⟨germ_injective hU x hx, germ_surjective s x hx⟩

private theorem
    SpecialPeriods.ModularGermLift.exists_lift_neighborhood (S : TopologicalSpace.Opens ℂ)
    (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F S)
    (h₃ : ∀ a ∈ S, F a = 0 → ∃ k : ℕ, analyticOrderAt F a = (3 * k : ℕ))
    (h₂ : ∀ a ∈ S, F a = 1728 → ∃ k : ℕ, analyticOrderAt (fun z => F z - 1728) a = (2 * k : ℕ))
    (x : S) :
    ∃ U : TopologicalSpace.Opens S,
      x ∈ U ∧
        IsPreconnected (AnalyticRootCover.ambientOpen S U : Set ℂ) ∧
          Nonempty (LiftSection S F U) := by
  obtain ⟨r, hr, hball, τ, hτ, hpos, hJ⟩ :=
    exists_local_lift_ball_subset S.isOpen x.2 (hF x x.2) (h₃ x x.2) (h₂ x x.2)
  let A : TopologicalSpace.Opens ℂ := ⟨Metric.ball (x : ℂ) r, Metric.isOpen_ball⟩
  let U : TopologicalSpace.Opens S :=
    TopologicalSpace.Opens.comap ⟨Subtype.val, continuous_subtype_val⟩ A
  have hUA : AnalyticRootCover.ambientOpen S U = A :=
    AnalyticRootCover.ambientOpen_comap_of_subset S A hball
  refine ⟨U, Metric.mem_ball_self hr, ?_, ?_⟩
  · rw [hUA]
    exact (convex_ball (x : ℂ) r).isPreconnected
  · have hτU : AnalyticOnNhd ℂ τ (AnalyticRootCover.ambientOpen S U) := by rwa [hUA]
    have hposU :
      Set.MapsTo τ (AnalyticRootCover.ambientOpen S U) UpperHalfPlane.upperHalfPlaneSet := by
      rwa [hUA]
    refine ⟨liftSectionOfComplex S F τ hτU hposU ?_⟩
    intro z hz
    apply hJ z
    rwa [hUA] at hz

private theorem SpecialPeriods.ModularGermLift.liftPresheaf_locally_bijective
    (S : TopologicalSpace.Opens ℂ) (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F S)
    (h₃ : ∀ a ∈ S, F a = 0 → ∃ k : ℕ, analyticOrderAt F a = (3 * k : ℕ))
    (h₂ : ∀ a ∈ S, F a = 1728 → ∃ k : ℕ, analyticOrderAt (fun z => F z - 1728) a = (2 * k : ℕ)) :
    ∀ x : S,
      ∃ U : TopologicalSpace.Opens S,
        x ∈ U ∧ ∀ y (hy : y ∈ U), Function.Bijective ((liftPresheaf S F).germ U y hy) := by
  intro x
  obtain ⟨U, hx, hU, ⟨s⟩⟩ := exists_lift_neighborhood S F hF h₃ h₂ x
  exact ⟨U, hx, fun y hy => germ_bijective hU s y hy⟩

private theorem
    AnalyticRootCover.square_root_order {f r : ℂ → ℂ} {a : ℂ} {n : ℕ} (hr : AnalyticAt ℂ r a)
    (heq : (fun z => r z ^ 2) =ᶠ[𝓝 a] f) (horder : analyticOrderAt f a = (2 * n : ℕ)) :
    analyticOrderAt r a = n := by
  have hpow : 2 • analyticOrderAt r a = (2 * n : ℕ) := by
    rw [← analyticOrderAt_pow hr 2]
    exact (analyticOrderAt_congr heq).trans horder
  have hfin : analyticOrderAt r a ≠ ⊤ := by
    intro ht
    simp only [ht, two_nsmul, top_add, ENat.top_ne_natCast] at hpow
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hfin
  rw [← hk] at hpow
  have hkn : k = n := by
    rw [two_nsmul] at hpow
    have he : k + k = 2 * n := by exact_mod_cast hpow
    omega
  rw [← hk, hkn]

private theorem AnalyticRootCover.even_order_at_all_points {f : ℂ → ℂ} {U : Set ℂ}
    (hf : AnalyticOnNhd ℂ f U)
    (hzero : ∀ a ∈ U, f a = 0 → ∃ n : ℕ, analyticOrderAt f a = (2 * n : ℕ)) :
    ∀ a ∈ U, ∃ n : ℕ, analyticOrderAt f a = (2 * n : ℕ) := by
  intro a ha
  by_cases hfa : f a = 0
  · exact hzero a ha hfa
  · exact
      ⟨0, by
        simpa only [MulZeroClass.mul_zero, Nat.cast_zero] using
          (hf a ha).analyticOrderAt_eq_zero.mpr hfa⟩

private abbrev AnalyticRootCoverContinuation.predicatePresheaf {X : TopCat.{0}} {Y : Type}
    (P : TopCat.LocalPredicate (fun _ : X => Y)) : TopCat.Presheaf (Type) X :=
  TopCat.subpresheafToTypes P.toPrelocalPredicate

private def AnalyticRootCoverContinuation.etaleValue {X : TopCat.{0}} {Y : Type}
    (P : TopCat.LocalPredicate (fun _ : X => Y)) (g : (predicatePresheaf P).EtaleSpace) : Y :=
  TopCat.stalkToFiber P g.base g.germ

private def AnalyticRootCoverContinuation.sectionGerm {X : TopCat.{0}} {Y : Type}
    (P : TopCat.LocalPredicate (fun _ : X => Y)) (U : TopologicalSpace.Opens X)
    (s : (predicatePresheaf P).obj (Opposite.op U)) (x : U) : (predicatePresheaf P).EtaleSpace :=
  ⟨x.1, (predicatePresheaf P).germ U x.1 x.2 s⟩

private theorem AnalyticRootCoverContinuation.etaleValue_sectionGerm {X : TopCat.{0}} {Y : Type}
    (P : TopCat.LocalPredicate (fun _ : X => Y)) (U : TopologicalSpace.Opens X)
    (s : (predicatePresheaf P).obj (Opposite.op U)) (x : U) :
    etaleValue P (sectionGerm P U s x) = s.1 x :=
  TopCat.stalkToFiber_germ P U x.1 x.2 s

private theorem AnalyticRootCoverContinuation.etaleSection_localGerms {X : TopCat.{0}} {Y : Type}
    (P : TopCat.LocalPredicate (fun _ : X => Y)) (σ : C(X, (predicatePresheaf P).EtaleSpace))
    (hσ : ∀ x : X, (σ x).base = x) (x : X) :
    ∃ (U : TopologicalSpace.Opens X) (_hx : x ∈ U) (s :
      (predicatePresheaf P).obj (Opposite.op U)),
      ∀ (y : X) (hy : y ∈ U), σ y = sectionGerm P U s ⟨y, hy⟩ := by
  obtain ⟨U, hxU, s, hs⟩ :=
    TopCat.Presheaf.EtaleSpace.exists_section_of_tendsto (σ.continuous.continuousAt (x := x))
  have hvalues : ∀ᶠ y in 𝓝 x, ∃ hy : y ∈ U, σ y = sectionGerm P U s ⟨y, hy⟩ := by
    filter_upwards [hs] with y hy
    obtain ⟨hyU, hg⟩ := hy
    refine ⟨hσ y ▸ hyU, ?_⟩
    calc
      σ y = sectionGerm P U s ⟨(σ y).base, hyU⟩ := by
        change σ y = ⟨(σ y).base, (predicatePresheaf P).germ U (σ y).base hyU s⟩
        rw [← hg]
      _ = sectionGerm P U s ⟨y, hσ y ▸ hyU⟩ := congrArg (sectionGerm P U s) (Subtype.ext (hσ y))
  obtain ⟨V, hV, hVo, hxV⟩ := eventually_nhds_iff.mp hvalues
  let W : TopologicalSpace.Opens X := ⟨V, hVo⟩
  have hWU : W ≤ U := fun y hy => (hV y hy).choose
  let i : W ⟶ U := CategoryTheory.homOfLE hWU
  refine ⟨W, hxV, (predicatePresheaf P).map i.op s, ?_⟩
  intro y hy
  have hg := (hV y hy).choose_spec
  convert hg using 1
  dsimp only [sectionGerm]
  rw [(predicatePresheaf P).germ_res_apply]

private theorem AnalyticRootCoverContinuation.etaleSection_locally {X : TopCat.{0}} {Y : Type}
    (P : TopCat.LocalPredicate (fun _ : X => Y)) (σ : C(X, (predicatePresheaf P).EtaleSpace))
    (hσ : ∀ x : X, (σ x).base = x) (x : X) :
    ∃ (U : TopologicalSpace.Opens X) (_hx : x ∈ U) (s :
      (predicatePresheaf P).obj (Opposite.op U)),
      ∀ (y : X) (hy : y ∈ U), etaleValue P (σ y) = s.1 ⟨y, hy⟩ := by
  obtain ⟨U, hxU, s, hs⟩ := etaleSection_localGerms P σ hσ x
  refine ⟨U, hxU, s, ?_⟩
  intro y hy
  rw [hs y hy, etaleValue_sectionGerm]

private theorem AnalyticRootCoverContinuation.etaleSection_pred {X : TopCat.{0}} {Y : Type}
    (P : TopCat.LocalPredicate (fun _ : X => Y)) (σ : C(X, (predicatePresheaf P).EtaleSpace))
    (hσ : ∀ x : X, (σ x).base = x) : P.pred (U := ⊤) (fun x => etaleValue P (σ x.1)) := by
  apply P.locality
  intro x
  obtain ⟨U, hxU, s, hs⟩ := etaleSection_locally P σ hσ x.1
  refine ⟨U, hxU, CategoryTheory.homOfLE le_top, ?_⟩
  convert s.2 using 1
  funext y
  exact hs y.1 y.2

private def AnalyticRootCoverContinuation.sectionOfEtaleSection {X : TopCat.{0}} {Y : Type}
    (P : TopCat.LocalPredicate (fun _ : X => Y)) (σ : C(X, (predicatePresheaf P).EtaleSpace))
    (hσ : ∀ x : X, (σ x).base = x) : (predicatePresheaf P).obj (Opposite.op ⊤) :=
  ⟨fun x => etaleValue P (σ x.1), etaleSection_pred P σ hσ⟩

private theorem AnalyticRootCoverContinuation.sectionOfEtaleSection_germ {X : TopCat.{0}} {Y : Type}
    (P : TopCat.LocalPredicate (fun _ : X => Y)) (σ : C(X, (predicatePresheaf P).EtaleSpace))
    (hσ : ∀ x : X, (σ x).base = x) (x : X) :
    sectionGerm P ⊤ (sectionOfEtaleSection P σ hσ) ⟨x, trivial⟩ = σ x := by
  obtain ⟨U, hxU, s, hs⟩ := etaleSection_localGerms P σ hσ x
  let i : U ⟶ (⊤ : TopologicalSpace.Opens X) := CategoryTheory.homOfLE le_top
  have heq : (predicatePresheaf P).map i.op (sectionOfEtaleSection P σ hσ) = s := by
    apply Subtype.ext
    funext y
    change etaleValue P (σ y.1) = s.1 y
    rw [hs y.1 y.2, etaleValue_sectionGerm]
  have hg :
    (predicatePresheaf P).germ ⊤ x trivial (sectionOfEtaleSection P σ hσ) =
      (predicatePresheaf P).germ U x hxU s := by
    rw [← (predicatePresheaf P).germ_res_apply i x hxU, heq]
  calc
    sectionGerm P ⊤ (sectionOfEtaleSection P σ hσ) ⟨x, trivial⟩ = sectionGerm P U s ⟨x, hxU⟩ := by
      dsimp only [sectionGerm]
      rw [hg]
    _ = σ x := (hs x hxU).symm

private theorem AnalyticRootCoverContinuation.exists_global_section_with_germ_of_germ_bijective
    {X : TopCat.{0}} {Y : Type} [SimplyConnectedSpace X] [LocallyPathConnectedSpace X]
    (P : TopCat.LocalPredicate (fun _ : X => Y))
    (hbij :
      ∀ x : X,
        ∃ U : TopologicalSpace.Opens X,
          x ∈ U ∧ ∀ (y : X) (hy : y ∈ U), Function.Bijective ((predicatePresheaf P).germ U y hy))
    (x₀ : X) (g₀ : (predicatePresheaf P).stalk x₀) :
    ∃ s : (predicatePresheaf P).obj (Opposite.op ⊤),
      (predicatePresheaf P).germ ⊤ x₀ trivial s = g₀ := by
  have hc : IsCoveringMap (TopCat.Presheaf.EtaleSpace.base (F := predicatePresheaf P)) :=
    TopCat.Presheaf.EtaleSpace.isCoveringMap_base hbij
  obtain ⟨σ, hσ, -⟩ := hc.existsUnique_continuousMap_lifts (ContinuousMap.id X) x₀ ⟨x₀, g₀⟩ rfl
  have hbase (x : X) : (σ x).base = x := congrFun hσ.2 x
  refine ⟨sectionOfEtaleSection P σ hbase, ?_⟩
  have hg := (sectionOfEtaleSection_germ P σ hbase x₀).trans hσ.1
  simpa only [sectionGerm, TopCat.Presheaf.EtaleSpace.mk.injEq, heq_eq_eq, true_and] using hg

private theorem
    AnalyticRootCover.ambientOpen_top (S : TopologicalSpace.Opens ℂ) : ambientOpen S ⊤ = S := by
  ext z
  constructor
  · rintro ⟨x, _, rfl⟩
    exact x.2
  · intro hz
    exact ⟨⟨z, hz⟩, trivial, rfl⟩

private theorem AnalyticRootCover.exists_global_rootSection_with_germ (S : TopologicalSpace.Opens ℂ)
    (F : ℂ → ℂ) [SimplyConnectedSpace S] (hF : AnalyticOnNhd ℂ F S)
    (horder : ∀ a ∈ S, ∃ n : ℕ, analyticOrderAt F a = (2 * n : ℕ)) (x : S)
    (g : (rootPresheaf S F).stalk x) :
    ∃ s : RootSection S F ⊤, (rootPresheaf S F).germ ⊤ x trivial s = g := by
  let : LocallyPathConnectedSpace S := S.isOpen.locallyPathConnectedSpace
  exact
    AnalyticRootCoverContinuation.exists_global_section_with_germ_of_germ_bijective
      (rootLocalPredicate S F) (rootPresheaf_locally_bijective S F hF horder) x g

private theorem
    AnalyticRootCover.exists_global_rootSection (S : TopologicalSpace.Opens ℂ) (F : ℂ → ℂ)
    [SimplyConnectedSpace S] (hF : AnalyticOnNhd ℂ F S)
    (horder : ∀ a ∈ S, ∃ n : ℕ, analyticOrderAt F a = (2 * n : ℕ)) :
    Nonempty (RootSection S F ⊤) := by
  let x : S := Classical.choice inferInstance
  obtain ⟨g⟩ := rootStalk_nonempty S F hF horder x
  obtain ⟨s, _⟩ := exists_global_rootSection_with_germ S F hF horder x g
  exact ⟨s⟩

private theorem AnalyticRootCover.exists_analytic_square_root_on (S : TopologicalSpace.Opens ℂ)
    (F : ℂ → ℂ) [SimplyConnectedSpace S] (hF : AnalyticOnNhd ℂ F S)
    (horder : ∀ a ∈ S, ∃ n : ℕ, analyticOrderAt F a = (2 * n : ℕ)) :
    ∃ r : ℂ → ℂ,
      AnalyticOnNhd ℂ r S ∧
        Set.EqOn (fun z => r z ^ 2) F S ∧
          ∀ a ∈ S, ∀ n : ℕ, analyticOrderAt F a = (2 * n : ℕ) → analyticOrderAt r a = n := by
  obtain ⟨s⟩ := exists_global_rootSection S F hF horder
  have hr : AnalyticOnNhd ℂ (extendSection S ⊤ s.1) S := by
    simpa only [ambientOpen_top] using RootSection.analyticOnNhd_extend s
  have hsquare : Set.EqOn (fun z => extendSection S ⊤ s.1 z ^ 2) F S := by
    intro z hz
    apply RootSection.square_eq (S := S) (F := F) (V := ⊤) s
    rw [ambientOpen_top]
    exact hz
  refine ⟨extendSection S ⊤ s.1, hr, hsquare, ?_⟩
  intro a ha n hn
  exact
    square_root_order (hr a ha)
      (Filter.eventually_of_mem (S.isOpen.mem_nhds ha) (fun _ hz => hsquare hz)) hn

private theorem AnalyticRootCover.exists_analytic_square_root_on_of_even_zeros
    (S : TopologicalSpace.Opens ℂ) (F : ℂ → ℂ) [SimplyConnectedSpace S] (hF : AnalyticOnNhd ℂ F S)
    (hzero : ∀ a ∈ S, F a = 0 → ∃ n : ℕ, analyticOrderAt F a = (2 * n : ℕ)) :
    ∃ r : ℂ → ℂ,
      AnalyticOnNhd ℂ r S ∧
        Set.EqOn (fun z => r z ^ 2) F S ∧
          ∀ a ∈ S, ∀ n : ℕ, analyticOrderAt F a = (2 * n : ℕ) → analyticOrderAt r a = n :=
  exists_analytic_square_root_on S F hF (even_order_at_all_points hF hzero)

private theorem SpecialPeriods.ModularGermLift.exists_global_liftSection_with_germ
    (S : TopologicalSpace.Opens ℂ) (F : ℂ → ℂ) [SimplyConnectedSpace S] (hF : AnalyticOnNhd ℂ F S)
    (h₃ : ∀ a ∈ S, F a = 0 → ∃ k : ℕ, analyticOrderAt F a = (3 * k : ℕ))
    (h₂ : ∀ a ∈ S, F a = 1728 → ∃ k : ℕ, analyticOrderAt (fun z => F z - 1728) a = (2 * k : ℕ))
    (x : S) (g : (liftPresheaf S F).stalk x) :
    ∃ s : LiftSection S F ⊤, (liftPresheaf S F).germ ⊤ x trivial s = g := by
  let : LocallyPathConnectedSpace S := S.isOpen.locallyPathConnectedSpace
  exact
    AnalyticRootCoverContinuation.exists_global_section_with_germ_of_germ_bijective
      (liftLocalPredicate S F) (liftPresheaf_locally_bijective S F hF h₃ h₂) x g

private theorem SpecialPeriods.ModularGermLift.exists_analytic_modularJ_lift_on_with_germ
    (S : TopologicalSpace.Opens ℂ) (F : ℂ → ℂ) [SimplyConnectedSpace S] (hF : AnalyticOnNhd ℂ F S)
    (h₃ : ∀ a ∈ S, F a = 0 → ∃ k : ℕ, analyticOrderAt F a = (3 * k : ℕ))
    (h₂ : ∀ a ∈ S, F a = 1728 → ∃ k : ℕ, analyticOrderAt (fun z => F z - 1728) a = (2 * k : ℕ))
    {U : TopologicalSpace.Opens S} (x : S) (hx : x ∈ U) (s : LiftSection S F U) :
    ∃ τ : ℂ → ℂ,
      AnalyticOnNhd ℂ τ S ∧
        Set.MapsTo τ S UpperHalfPlane.upperHalfPlaneSet ∧
          Set.EqOn (fun z => SpecialPeriods.modularJ (UpperHalfPlane.ofComplex (τ z))) F S ∧
            τ =ᶠ[𝓝 (x : ℂ)] extendLiftSection S U s.1 := by
  obtain ⟨t, ht⟩ :=
    exists_global_liftSection_with_germ S F hF h₃ h₂ x ((liftPresheaf S F).germ U x hx s)
  refine ⟨extendLiftSection S ⊤ t.1, ?_, ?_, ?_, ?_⟩
  · simpa only [AnalyticRootCover.ambientOpen_top] using t.analyticOnNhd_extend
  · simpa only [AnalyticRootCover.ambientOpen_top] using t.mapsTo_extend
  · intro z hz
    apply LiftSection.modular_eq (S := S) (F := F) (V := ⊤) t
    rwa [AnalyticRootCover.ambientOpen_top]
  · exact (germ_eq_iff_eventuallyEq S F (U := ⊤) (V := U) x trivial hx t s).mp ht

private theorem
    SpecialPeriods.ModularGermLift.exists_liftSection_of_germ (S : TopologicalSpace.Opens ℂ)
    (F : ℂ → ℂ) {a : ℂ} (ha : a ∈ S) (τ₀ : ℂ → ℂ) (hτ₀ : AnalyticAt ℂ τ₀ a) (hpos : 0 < (τ₀ a).im)
    (hJ₀ : (fun z => SpecialPeriods.modularJ (UpperHalfPlane.ofComplex (τ₀ z))) =ᶠ[𝓝 a] F) :
    ∃ (U : TopologicalSpace.Opens S) (_hx : (⟨a, ha⟩ : S) ∈ U) (s : LiftSection S F U),
      extendLiftSection S U s.1 =ᶠ[𝓝 a] τ₀ := by
  have hposnear : ∀ᶠ z in 𝓝 a, τ₀ z ∈ UpperHalfPlane.upperHalfPlaneSet :=
    hτ₀.continuousAt.preimage_mem_nhds (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hpos)
  have hSnear : ∀ᶠ z in 𝓝 a, z ∈ S := S.isOpen.mem_nhds ha
  obtain ⟨r, hr, hball⟩ :=
    Metric.mem_nhds_iff.mp (hSnear.and (hτ₀.eventually_analyticAt.and (hposnear.and hJ₀)))
  let A : TopologicalSpace.Opens ℂ := ⟨Metric.ball a r, Metric.isOpen_ball⟩
  let U : TopologicalSpace.Opens S :=
    TopologicalSpace.Opens.comap ⟨Subtype.val, continuous_subtype_val⟩ A
  have hUA : AnalyticRootCover.ambientOpen S U = A :=
    AnalyticRootCover.ambientOpen_comap_of_subset S A (fun _ hz => (hball hz).1)
  have hτU : AnalyticOnNhd ℂ τ₀ (AnalyticRootCover.ambientOpen S U) := by
    rw [hUA]
    exact fun z hz => (hball hz).2.1
  have hposU :
    Set.MapsTo τ₀ (AnalyticRootCover.ambientOpen S U) UpperHalfPlane.upperHalfPlaneSet := by
    rw [hUA]
    exact fun z hz => (hball hz).2.2.1
  have hJU :
    Set.EqOn (fun z => SpecialPeriods.modularJ (UpperHalfPlane.ofComplex (τ₀ z))) F
      (AnalyticRootCover.ambientOpen S U) := by
    rw [hUA]
    exact fun z hz => (hball hz).2.2.2
  let s : LiftSection S F U := liftSectionOfComplex S F τ₀ hτU hposU hJU
  refine ⟨U, Metric.mem_ball_self hr, s, ?_⟩
  filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr)] with z hz
  apply extend_liftSectionOfComplex_eqOn S F τ₀ hτU hposU hJU
  rwa [hUA]

private theorem SpecialPeriods.ModularGermLift.exists_analytic_modularJ_lift_extending
    (S : TopologicalSpace.Opens ℂ) (F : ℂ → ℂ) [SimplyConnectedSpace S] (hF : AnalyticOnNhd ℂ F S)
    (h₃ : ∀ a ∈ S, F a = 0 → ∃ k : ℕ, analyticOrderAt F a = (3 * k : ℕ))
    (h₂ : ∀ a ∈ S, F a = 1728 → ∃ k : ℕ, analyticOrderAt (fun z => F z - 1728) a = (2 * k : ℕ))
    {a : ℂ} (ha : a ∈ S) (τ₀ : ℂ → ℂ) (hτ₀ : AnalyticAt ℂ τ₀ a) (hpos : 0 < (τ₀ a).im)
    (hJ₀ : (fun z => SpecialPeriods.modularJ (UpperHalfPlane.ofComplex (τ₀ z))) =ᶠ[𝓝 a] F) :
    ∃ τ : ℂ → ℂ,
      AnalyticOnNhd ℂ τ S ∧
        Set.MapsTo τ S UpperHalfPlane.upperHalfPlaneSet ∧
          Set.EqOn (fun z => SpecialPeriods.modularJ (UpperHalfPlane.ofComplex (τ z))) F S ∧
            τ =ᶠ[𝓝 a] τ₀ := by
  obtain ⟨U, hx, s, hs⟩ := exists_liftSection_of_germ S F ha τ₀ hτ₀ hpos hJ₀
  obtain ⟨τ, hτ, hτpos, hJ, heq⟩ :=
    exists_analytic_modularJ_lift_on_with_germ S F hF h₃ h₂ ⟨a, ha⟩ hx s
  exact ⟨τ, hτ, hτpos, hJ, heq.trans hs⟩

private def AnalyticRootCover.upperHalfPlaneOpen : TopologicalSpace.Opens ℂ :=
  ⟨UpperHalfPlane.upperHalfPlaneSet, UpperHalfPlane.isOpen_upperHalfPlaneSet⟩

private instance AnalyticRootCover.instContractibleSpace1 : ContractibleSpace upperHalfPlaneOpen :=
  (convex_halfSpace_im_gt 0).contractibleSpace ⟨Complex.I, by simp⟩

private theorem AnalyticRootCover.exists_analytic_square_root_upperHalfPlane (F : ℂ → ℂ)
    (hF : AnalyticOnNhd ℂ F UpperHalfPlane.upperHalfPlaneSet)
    (hzero :
      ∀ a ∈ UpperHalfPlane.upperHalfPlaneSet,
        F a = 0 → ∃ n : ℕ, analyticOrderAt F a = (2 * n : ℕ)) :
    ∃ r : ℂ → ℂ,
      AnalyticOnNhd ℂ r UpperHalfPlane.upperHalfPlaneSet ∧
        Set.EqOn (fun z => r z ^ 2) F UpperHalfPlane.upperHalfPlaneSet ∧
          ∀ a ∈ UpperHalfPlane.upperHalfPlaneSet,
            ∀ n : ℕ, analyticOrderAt F a = (2 * n : ℕ) → analyticOrderAt r a = n :=
  exists_analytic_square_root_on_of_even_zeros upperHalfPlaneOpen F hF hzero

public
theorem AnalyticRootCover.exists_holomorphic_square_root_upperHalfPlane (f : ℍ → ℂ)
    (hf : MDifferentiable 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f)
    (hzero :
      ∀ a : ℍ,
        f a = 0 → ∃ n : ℕ, analyticOrderAt (f ∘ UpperHalfPlane.ofComplex) (a : ℂ) = (2 * n : ℕ)) :
    ∃ r : ℍ → ℂ,
      ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω r ∧
        (∀ a : ℍ, r a ^ 2 = f a) ∧
          ∀ a : ℍ,
            ∀ n : ℕ,
              analyticOrderAt (f ∘ UpperHalfPlane.ofComplex) (a : ℂ) = (2 * n : ℕ) →
                analyticOrderAt (r ∘ UpperHalfPlane.ofComplex) (a : ℂ) = n := by
  let F : ℂ → ℂ := f ∘ UpperHalfPlane.ofComplex
  have hF : AnalyticOnNhd ℂ F UpperHalfPlane.upperHalfPlaneSet :=
    (UpperHalfPlane.mdifferentiable_iff.mp hf).analyticOnNhd
      UpperHalfPlane.isOpen_upperHalfPlaneSet
  have hzeroF :
    ∀ a ∈ UpperHalfPlane.upperHalfPlaneSet,
      F a = 0 → ∃ n : ℕ, analyticOrderAt F a = (2 * n : ℕ) := by
    intro a ha hfa
    apply hzero ⟨a, ha⟩
    simpa only [F, Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos ha] using hfa
  obtain ⟨g, hg, hgsquare, hgorder⟩ := exists_analytic_square_root_upperHalfPlane F hF hzeroF
  let r : ℍ → ℂ := fun a => g a
  refine ⟨r, ?_, ?_, ?_⟩
  · intro a
    exact (hg a a.im_pos).contDiffAt.contMDiffAt.comp a (UpperHalfPlane.contMDiff_coe a)
  · intro a
    simpa only [r, F, Function.comp_apply, UpperHalfPlane.ofComplex_apply] using hgsquare a.im_pos
  · intro a n hn
    have he : (r ∘ UpperHalfPlane.ofComplex) =ᶠ[𝓝 (a : ℂ)] g := by
      filter_upwards [UpperHalfPlane.eventuallyEq_coe_comp_ofComplex a.im_pos] with z hz
      exact congrArg g hz
    exact (analyticOrderAt_congr he).trans (hgorder a a.im_pos n hn)

private def SpecialPeriods.ModularGermLift.upperHalfPlaneLift (g : ℂ → ℂ) : ℍ → ℍ := fun z =>
  UpperHalfPlane.ofComplex (g (z : ℂ))

private theorem SpecialPeriods.ModularGermLift.upperHalfPlaneLift_holomorphic {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g UpperHalfPlane.upperHalfPlaneSet)
    (hpos : Set.MapsTo g UpperHalfPlane.upperHalfPlaneSet UpperHalfPlane.upperHalfPlaneSet) :
    ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (upperHalfPlaneLift g) := by
  intro z
  exact
    (UpperHalfPlane.contMDiffAt_ofComplex (hpos z.im_pos)).comp z
      ((hg z z.im_pos).contDiffAt.contMDiffAt.comp z (UpperHalfPlane.contMDiff_coe z))

private theorem SpecialPeriods.ModularGermLift.upperHalfPlaneLift_eventuallyEq {g : ℂ → ℂ}
    (hpos : Set.MapsTo g UpperHalfPlane.upperHalfPlaneSet UpperHalfPlane.upperHalfPlaneSet)
    (a : ℍ) :
    (fun z => (upperHalfPlaneLift g (UpperHalfPlane.ofComplex z) : ℂ)) =ᶠ[𝓝 (a : ℂ)] g := by
  filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds a.im_pos] with z hz
  change (UpperHalfPlane.ofComplex (g (UpperHalfPlane.ofComplex z : ℂ)) : ℂ) = g z
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz,
    UpperHalfPlane.ofComplex_apply_of_im_pos (hpos hz)]

private theorem SpecialPeriods.ModularGermLift.upperHalfPlane_critical_orders {F : ℍ → ℂ}
    (h₃ :
      ∀ a : ℍ,
        F a = 0 → ∃ k : ℕ, analyticOrderAt (F ∘ UpperHalfPlane.ofComplex) (a : ℂ) = (3 * k : ℕ))
    (h₂ :
      ∀ a : ℍ,
        F a = 1728 →
          ∃ k : ℕ,
            analyticOrderAt (fun z => F (UpperHalfPlane.ofComplex z) - 1728) (a : ℂ) =
              (2 * k : ℕ)) :
    (∀ a ∈ UpperHalfPlane.upperHalfPlaneSet,
        (F ∘ UpperHalfPlane.ofComplex) a = 0 →
          ∃ k : ℕ, analyticOrderAt (F ∘ UpperHalfPlane.ofComplex) a = (3 * k : ℕ)) ∧
      (∀ a ∈ UpperHalfPlane.upperHalfPlaneSet,
        (F ∘ UpperHalfPlane.ofComplex) a = 1728 →
          ∃ k : ℕ,
            analyticOrderAt (fun z => (F ∘ UpperHalfPlane.ofComplex) z - 1728) a = (2 * k : ℕ)) :=
  by
  constructor
  · intro a ha hFa
    apply h₃ ⟨a, ha⟩
    simpa only [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos ha] using hFa
  · intro a ha hFa
    apply h₂ ⟨a, ha⟩
    simpa only [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos ha] using hFa

private theorem
    SpecialPeriods.ModularGermLift.exists_holomorphic_modularJ_lift_upperHalfPlane_extending
    (F : ℍ → ℂ) (hF : MDifferentiable 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) F)
    (h₃ :
      ∀ a : ℍ,
        F a = 0 → ∃ k : ℕ, analyticOrderAt (F ∘ UpperHalfPlane.ofComplex) (a : ℂ) = (3 * k : ℕ))
    (h₂ :
      ∀ a : ℍ,
        F a = 1728 →
          ∃ k : ℕ,
            analyticOrderAt (fun z => F (UpperHalfPlane.ofComplex z) - 1728) (a : ℂ) =
              (2 * k : ℕ))
    (a : ℍ) (τ₀ : ℂ → ℂ) (hτ₀ : AnalyticAt ℂ τ₀ (a : ℂ)) (hpos₀ : 0 < (τ₀ a).im)
    (hJ₀ :
      (fun z => SpecialPeriods.modularJ (UpperHalfPlane.ofComplex (τ₀ z))) =ᶠ[𝓝 (a : ℂ)]
        F ∘ UpperHalfPlane.ofComplex) :
    ∃ τ : ℍ → ℍ,
      ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω τ ∧
        (∀ z : ℍ, SpecialPeriods.modularJ (τ z) = F z) ∧
          (fun z => (τ (UpperHalfPlane.ofComplex z) : ℂ)) =ᶠ[𝓝 (a : ℂ)] τ₀ := by
  have hF' : AnalyticOnNhd ℂ (F ∘ UpperHalfPlane.ofComplex) UpperHalfPlane.upperHalfPlaneSet :=
    (UpperHalfPlane.mdifferentiable_iff.mp hF).analyticOnNhd
      UpperHalfPlane.isOpen_upperHalfPlaneSet
  obtain ⟨h₃', h₂'⟩ := upperHalfPlane_critical_orders h₃ h₂
  obtain ⟨g, hg, hpos, hJ, hg₀⟩ :=
    exists_analytic_modularJ_lift_extending AnalyticRootCover.upperHalfPlaneOpen
      (F ∘ UpperHalfPlane.ofComplex) hF' h₃' h₂' a.im_pos τ₀ hτ₀ hpos₀ hJ₀
  refine
    ⟨upperHalfPlaneLift g, upperHalfPlaneLift_holomorphic hg hpos, ?_,
      (upperHalfPlaneLift_eventuallyEq hpos a).trans hg₀⟩
  intro z
  simpa only [upperHalfPlaneLift, Function.comp_apply, UpperHalfPlane.ofComplex_apply] using
    hJ z.im_pos

end Mathoverflow1973

end
