/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.FunctionSpace
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.LaurentSeries

/-!
# Laurent approximation and coefficient projections

Finite Laurent sums approximate holomorphic functions uniformly on compact subsets. The
coefficient functionals are continuous independently of Laurent expansion. The projections,
their mutual orthogonality, and convergence in the compact-open holomorphic space are derived
from the Laurent expansion theorem. Only the elementary analytic consequences of
[Scheidemann][Scheidemann2005] (2005), Section 2.2, are used; no representation theory of
compact groups is introduced.

## Main results

`exists_finite_laurent_approximation` approximates a holomorphic function uniformly on a compact
set by a finite Laurent sum. `exists_laurentCoeffCLM` and `exists_laurentTermCLM` are the
continuous coefficient and term projections on the compact-open holomorphic space.

## References

* [V. Scheidemann, *Introduction to Complex Analysis in Several Variables*][Scheidemann2005]
-/

public noncomputable section

open Set Filter MeasureTheory Complex
open scoped Topology

namespace SeveralComplexVariables

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- Integration on a fixed coordinate torus is a continuous linear coefficient functional on the
compact-open space of holomorphic maps. This construction does not require Laurent expansion or
connectedness. -/
theorem exists_laurentCoeffCLM (U : TopologicalSpace.Opens (Fin n → ℂ))
    (hR : IsReinhardt (U : Set (Fin n → ℂ)))
    {r : Fin n → ℝ} (hr : ∀ i, 0 < r i) (hrU : (fun i => (r i : ℂ)) ∈ U)
    (m : Fin n → ℤ) :
    ∃ A : HolomorphicMap U F →L[ℂ] F, ∀ f,
      A f = multivariableLaurentCoeff (openExtension U f.val) r m := by
  classical
  let := U.isOpen.locallyCompactSpace
  let K := Icc (0 : Fin n → ℝ) (fun _ => 2 * Real.pi)
  have hK : IsCompact K := isCompact_Icc
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let : MeasureSpace K := Measure.Subtype.measureSpace
  let : IsFiniteMeasure (volume : Measure K) := ⟨by
    rw [Measure.Subtype.volume_univ hK.measurableSet.nullMeasurableSet]
    exact hK.measure_lt_top⟩
  have htor (θ : Fin n → ℝ) : torusMap 0 r θ ∈ U := by
    apply hR hrU
    intro i
    simpa only [Pi.zero_apply, sub_zero, Complex.norm_of_nonneg (hr i).le] using
      norm_torusMap_sub (c := 0) (fun i => (hr i).le) θ i
  let γ : C(K, U) := ⟨fun θ => ⟨torusMap 0 r θ, htor θ⟩,
    ((continuous_torusMap 0 r).comp continuous_subtype_val).subtype_mk _⟩
  have hnz (θ : K) (i : Fin n) : torusMap 0 r θ i ≠ 0 :=
    torusMap_apply_ne_of_norm_sub_lt (c := 0) (w := 0) hr (by simpa using hr i)
  let b : C(K, ℂ) := ⟨fun θ =>
    (∏ i, (r i : ℂ) * exp ((θ.val i : ℂ) * I) * I) *
      ∏ i, torusMap 0 r θ i ^ (-m i - 1), by
    apply Continuous.mul
    · apply continuous_finsetProd
      intro i _
      exact ((continuous_const.mul
        (Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp
          ((continuous_apply i).comp continuous_subtype_val)).mul continuous_const))).mul
            continuous_const)
    · apply continuous_finsetProd
      intro i _
      exact ((continuous_apply i).comp ((continuous_torusMap 0 r).comp
        continuous_subtype_val)).zpow₀ (-m i - 1) (fun θ => Or.inl (hnz θ i))⟩
  let T : HolomorphicMap U F →L[ℂ] C(K, F) :=
    { toFun := fun f => ⟨fun θ => b θ • f.val (γ θ),
        b.continuous.smul (f.val.continuous.comp γ.continuous)⟩
      map_add' := by intros; ext; simp
      map_smul' := by
        intro c f
        ext θ
        exact smul_comm (b θ) c (f.val (γ θ))
      cont := by
        apply ContinuousMap.continuous_of_continuous_uncurry
        exact (b.continuous.comp continuous_snd).smul
          (continuous_eval.comp
            ((continuous_subtype_val.comp continuous_fst).prodMk
              (γ.continuous.comp continuous_snd))) }
  let J : C(K, F) →L[ℂ] F :=
    (L1.integralCLM' ℂ).comp (ContinuousMap.toLp 1 volume ℂ)
  let A : HolomorphicMap U F →L[ℂ] F :=
    ((2 * Real.pi * I : ℂ) ^ n)⁻¹ • J.comp T
  refine ⟨A, fun f => ?_⟩
  have hJ : J (T f) = ∫ θ : K, T f θ := by
    change L1.integralCLM' ℂ (ContinuousMap.toLp 1 volume ℂ (T f)) = _
    rw [← L1.integral_eq' ℂ, L1.integral_eq_integral]
    exact integral_congr_ae (ContinuousMap.coeFn_toLp (𝕜 := ℂ) volume (T f))
  change ((2 * Real.pi * I : ℂ) ^ n)⁻¹ • J (T f) = _
  rw [hJ, multivariableLaurentCoeff, torusIntegral, ← integral_subtype hK.measurableSet]
  congr 1
  apply integral_congr_ae
  filter_upwards with θ
  change b θ • f.val (γ θ) = _
  rw [openExtension_apply U _ (htor θ)]
  exact mul_smul _ _ _

/-- Each Laurent term defines a continuous operator with values in holomorphic maps. Vanishing of
forbidden coefficients uses the Laurent expansion theorem. -/
theorem exists_laurentTermCLM (U : TopologicalSpace.Opens (Fin n → ℂ))
    (hc : IsConnected (U : Set (Fin n → ℂ))) (hR : IsReinhardt (U : Set (Fin n → ℂ)))
    {r : Fin n → ℝ} (hr : ∀ i, 0 < r i) (hrU : (fun i => (r i : ℂ)) ∈ U)
    (m : Fin n → ℤ) :
    ∃ P : HolomorphicMap U F →L[ℂ] HolomorphicMap U F, ∀ f z,
      (P f).val z = multivariableLaurentTerm
        (multivariableLaurentCoeff (openExtension U f.val) r) m z := by
  classical
  obtain ⟨A, hA⟩ := exists_laurentCoeffCLM (F := F) U hR hr hrU m
  by_cases hm : ∀ i, m i < 0 → ∀ z ∈ U, z i ≠ 0
  · let a : (Fin n → ℂ) → ℂ := fun z => ∏ i, z i ^ m i
    have ha : AnalyticOnNhd ℂ a U := by
      intro z hz
      apply Finset.analyticAt_fun_prod
      intro i _
      by_cases hi : 0 ≤ m i
      · exact ((ContinuousLinearMap.proj (R := ℂ) i).analyticAt z).zpow_nonneg hi
      · exact ((ContinuousLinearMap.proj (R := ℂ) i).analyticAt z).zpow
          (hm i (lt_of_not_ge hi) z hz)
    let B : F →L[ℂ] HolomorphicMap U F :=
      { toFun := fun v =>
          ⟨⟨fun z => a z • v, ha.continuousOn.domRestrict.smul continuous_const⟩, by
            apply AnalyticOnNhd.congr U.isOpen (ha.smul (analyticOnNhd_const (v := v)))
            intro z hz
            rw [openExtension_apply U _ hz]
            rfl⟩
        map_add' := by intros; ext; exact smul_add _ _ _
        map_smul' := by intros; ext; exact smul_comm _ _ _
        cont := by
          apply Continuous.subtype_mk
          apply ContinuousMap.continuous_of_continuous_uncurry
          exact (ha.continuousOn.domRestrict.comp continuous_snd).smul continuous_fst }
    refine ⟨B.comp A, fun f z => ?_⟩
    change a z • A f = _
    rw [hA]
    rfl
  · push Not at hm
    obtain ⟨i, hi, z, hz, hzi⟩ := hm
    refine ⟨0, fun f w => ?_⟩
    have hzero := (multivariableLaurent_expansion U.isOpen hc.isPreconnected hR f.property hr
      hrU).2.2.1
      m i ⟨z, hz, hzi⟩ hi
    simp [multivariableLaurentTerm, hzero]

/-- Finite canonical Laurent sums approximate uniformly on any given compact subset. Depends on the
Laurent expansion theorem, with no finite-dimensional target restriction. -/
theorem exists_finite_laurent_approximation {U K : Set (Fin n → ℂ)}
    (ho : IsOpen U) (hc : IsConnected U) (hR : IsReinhardt U)
    {f : (Fin n → ℂ) → F} (hf : AnalyticOnNhd ℂ f U)
    {r : Fin n → ℝ} (hr : ∀ i, 0 < r i) (hrU : (fun i => (r i : ℂ)) ∈ U)
    (hK : IsCompact K) (hKU : K ⊆ U) {ε : ℝ} (hε : 0 < ε) :
    ∃ s : Finset (Fin n → ℤ), ∀ z ∈ K,
      ‖f z - ∑ m ∈ s, multivariableLaurentTerm (multivariableLaurentCoeff f r) m z‖ < ε := by
  have h := hasSumUniformlyOn_iff_tendstoUniformlyOn.mp
    (hasSumUniformlyOn_multivariableLaurent ho hc.isPreconnected hR hf hr hrU hK hKU)
  obtain ⟨s, hs⟩ := (Metric.tendstoUniformlyOn_iff.mp h ε hε).exists
  exact ⟨s, fun z hz => by simpa [dist_eq_norm] using hs z hz⟩

/-- Continuous Laurent projections, their coefficient formulas, and their mutual orthogonality
follow from continuity of torus integration, holomorphy of permitted monomials, and Laurent
uniqueness. Terms with forbidden negative exponents are zero. The finite partial sums converge
in the existing compact-open topology. This deduction depends on the Laurent expansion theorem. -/
theorem exists_laurentProjections (U : TopologicalSpace.Opens (Fin n → ℂ))
    (hc : IsConnected (U : Set (Fin n → ℂ))) (hR : IsReinhardt (U : Set (Fin n → ℂ)))
    {r : Fin n → ℝ} (hr : ∀ i, 0 < r i) (hrU : (fun i => (r i : ℂ)) ∈ U) :
    ∃ P : (Fin n → ℤ) → HolomorphicMap U F →L[ℂ] HolomorphicMap U F,
      (∀ m f z, (P m f).val z =
        multivariableLaurentTerm (multivariableLaurentCoeff (openExtension U f.val) r) m z) ∧
      (∀ m k f, P m (P k f) = if m = k then P m f else 0) ∧
      (∀ f, Tendsto (fun s : Finset (Fin n → ℤ) => ∑ m ∈ s, P m f) atTop (𝓝 f)) := by
  classical
  choose P hP using fun m => exists_laurentTermCLM (F := F) U hc hR hr hrU m
  refine ⟨P, hP, ?_, ?_⟩
  · intro m k f
    let c : (Fin n → ℤ) → F := fun j => if j = k then
      multivariableLaurentCoeff (openExtension U f.val) r k else 0
    have hsingle : HasSum (fun j => if j = k then P k f else 0) (P k f) :=
      hasSum_ite_eq k (P k f)
    have hs : HasSumLocallyUniformlyOn (multivariableLaurentTerm c)
        (openExtension U (P k f).val) U := by
      apply (holomorphicMap_tendsto_iff.mp hsingle).congr
      intro s z hz
      rw [openExtension_apply U _ hz]
      simp only [Submodule.coe_sum, ContinuousMap.sum_apply]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j = k
      · subst j
        simp only [ite_true, hP, multivariableLaurentTerm, c]
      · simp [hj, c, multivariableLaurentTerm]
    have hcoeff := (multivariableLaurent_expansion U.isOpen hc.isPreconnected hR
      (P k f).property hr hrU).2.2.2.2 c hs
    ext z
    rw [hP, ← hcoeff]
    by_cases hmk : m = k
    · subst m
      simp only [c, ite_true, multivariableLaurentTerm]
      exact (hP k f z).symm
    · simp [c, hmk, multivariableLaurentTerm]
  · intro f
    rw [holomorphicMap_tendsto_iff]
    apply (multivariableLaurent_expansion U.isOpen hc.isPreconnected hR f.property hr hrU).1.congr
    intro s z hz
    rw [openExtension_apply U _ hz]
    simp only [Submodule.coe_sum, ContinuousMap.sum_apply]
    exact Finset.sum_congr rfl (fun m _ => (hP m f ⟨z, hz⟩).symm)

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
