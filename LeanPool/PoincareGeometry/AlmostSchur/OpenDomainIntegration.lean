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

public import LeanPool.PoincareGeometry.AlmostSchur.LocalIntegration
public import LeanPool.PoincareGeometry.AlmostSchur.LocalMetricDivergence

/-!
# Green identities on open coordinate domains

Only the compactly supported flux must extend smoothly by zero. Scalar test
functions and densities need regularity only on the open domain containing its
topological support.
-/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators Matrix.Norms.Elementwise

namespace AlmostSchur

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Smoothness on an open set containing the topological support implies
global smoothness: the function is locally zero at every other point. -/
theorem contDiff_of_tsupport_subset {n : WithTop ENat} {f : V → F} {U : Set V}
    (hU : IsOpen U) (hf : ContDiffOn ℝ n f U) (hs : tsupport f ⊆ U) :
    ContDiff ℝ n f := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport f
  · exact hf.contDiffAt (hU.mem_nhds (hs hx))
  · exact contDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hx)

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  {μ : Measure V} [Measure.IsAddHaarMeasure μ]

/-- Scalar integration by parts needs test-function regularity only on an
open neighborhood of the compactly supported second factor. -/
theorem integral_mul_fderiv_openDomain {U : Set V} (hU : IsOpen U) (f g : V → ℝ)
    (hf : ContDiffOn ℝ 1 f U) (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g)
    (hs : tsupport g ⊆ U) (v : V) :
    ∫ x, f x * fderiv ℝ g x v ∂μ = -∫ x, fderiv ℝ f x v * g x ∂μ := by
  have hfg : Continuous (fun x => f x * g x) :=
    (hf.continuousOn.mul hg.continuous.continuousOn).continuous_of_tsupport_subset hU
      (tsupport_mul_subset_right.trans hs)
  have hfg' : Continuous (fun x => f x * fderiv ℝ g x v) :=
    (hf.continuousOn.mul ((hg.continuous_fderiv (by norm_num)).clm_apply
      continuous_const).continuousOn).continuous_of_tsupport_subset hU
        (tsupport_mul_subset_right.trans ((tsupport_fderiv_apply_subset ℝ v).trans hs))
  have hf'g : Continuous (fun x => fderiv ℝ f x v * g x) :=
    (((hf.continuousOn_fderiv_of_isOpen hU (by norm_num)).clm_apply continuousOn_const).mul
      hg.continuous.continuousOn).continuous_of_tsupport_subset hU
        (tsupport_mul_subset_right.trans hs)
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (hf'g.integrable_of_hasCompactSupport hc.mul_left)
    (hfg'.integrable_of_hasCompactSupport (hc.fderiv_apply ℝ v).mul_left)
    (hfg.integrable_of_hasCompactSupport hc.mul_left)
    (fun x hx => (hf.contDiffAt (hU.mem_nhds (hs hx))).differentiableAt (by norm_num))
    (fun x _ => hg.differentiable (by norm_num) x)

/-- Both derivative products in the open-domain Green formula are integrable. -/
theorem integrable_fderiv_products_openDomain {U : Set V} (hU : IsOpen U) (f g : V → ℝ)
    (hf : ContDiffOn ℝ 1 f U) (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g)
    (hs : tsupport g ⊆ U) (v : V) :
    Integrable (fun x => f x * fderiv ℝ g x v) μ ∧
      Integrable (fun x => fderiv ℝ f x v * g x) μ := by
  constructor
  · apply Continuous.integrable_of_hasCompactSupport _ (hc.fderiv_apply ℝ v).mul_left
    exact (hf.continuousOn.mul ((hg.continuous_fderiv (by norm_num)).clm_apply
      continuous_const).continuousOn).continuous_of_tsupport_subset hU
        (tsupport_mul_subset_right.trans ((tsupport_fderiv_apply_subset ℝ v).trans hs))
  · apply Continuous.integrable_of_hasCompactSupport _ hc.mul_left
    exact (((hf.continuousOn_fderiv_of_isOpen hU (by norm_num)).clm_apply continuousOn_const).mul
      hg.continuous.continuousOn).continuous_of_tsupport_subset hU
        (tsupport_mul_subset_right.trans hs)

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W]
  {ν : Measure W} [Measure.IsAddHaarMeasure ν]

omit [MeasurableSpace W] [BorelSpace W] in
/-- The derivative trace of a C1 field is continuous on its open domain. -/
theorem continuousOn_localDivergence {U : Set W} (hU : IsOpen U) (X : W → W)
    (hX : ContDiffOn ℝ 1 X U) : ContinuousOn (localDivergence X) U := by
  classical
  let b := stdOrthonormalBasis ℝ W
  have heq : localDivergence X = fun x => ∑ i, inner ℝ (b i) (fderiv ℝ X x (b i)) := by
    funext x
    exact localDivergence_eq_sum X x b
  rw [heq]
  apply continuousOn_finset_sum
  intro i _
  exact continuousOn_const.inner
    ((hX.continuousOn_fderiv_of_isOpen hU (by norm_num)).clm_apply continuousOn_const)

omit [MeasurableSpace W] [BorelSpace W] in
/-- Positive C1 density and C1 field give continuous density divergence. -/
theorem continuousOn_localDensityDivergence {U : Set W} (hU : IsOpen U)
    (ρ : W → ℝ) (X : W → W) (hρ : ContDiffOn ℝ 1 ρ U)
    (hX : ContDiffOn ℝ 1 X U) (hpos : ∀ x ∈ U, 0 < ρ x) :
    ContinuousOn (localDensityDivergence ρ X) U :=
  (continuousOn_localDivergence hU _ (hρ.smul hX)).div hρ.continuousOn
    (fun x hx => (hpos x hx).ne')

/-- Vector Green identity on an open domain: the test function is C1 only
on that domain, and the vector field has compact support inside it. -/
theorem integral_mul_localDivergence_openDomain {U : Set W} (hU : IsOpen U)
    (f : W → ℝ) (X : W → W) (hf : ContDiffOn ℝ 1 f U)
    (hX : ContDiffOn ℝ 1 X U) (hc : HasCompactSupport X) (hs : tsupport X ⊆ U) :
    ∫ x, f x * localDivergence X x ∂ν = -∫ x, fderiv ℝ f x (X x) ∂ν := by
  classical
  have hXg := contDiff_of_tsupport_subset hU hX hs
  let b := stdOrthonormalBasis ℝ W
  have hcomp (i : Fin (Module.finrank ℝ W)) :
      ContDiff ℝ 1 (fun x => inner ℝ (b i) (X x)) :=
    (innerSL ℝ (b i)).contDiff.comp hXg
  have hcompc (i : Fin (Module.finrank ℝ W)) :
      HasCompactSupport (fun x => inner ℝ (b i) (X x)) := hc.comp_left (by simp)
  have hcomps (i : Fin (Module.finrank ℝ W)) :
      tsupport (fun x => inner ℝ (b i) (X x)) ⊆ U :=
    (tsupport_comp_subset (g := fun v : W => inner ℝ (b i) v) (by simp) X).trans hs
  have hder (i : Fin (Module.finrank ℝ W)) (x : W) :
      fderiv ℝ (fun y => inner ℝ (b i) (X y)) x (b i) =
        inner ℝ (b i) (fderiv ℝ X x (b i)) :=
    congrArg (fun L : W →L[ℝ] ℝ => L (b i))
      (((innerSL ℝ (b i)).hasFDerivAt.comp x
        (hXg.differentiable (by norm_num) x).hasFDerivAt).fderiv)
  have hi (i : Fin (Module.finrank ℝ W)) :
      ∫ x, f x * inner ℝ (b i) (fderiv ℝ X x (b i)) ∂ν =
        -∫ x, fderiv ℝ f x (b i) * inner ℝ (b i) (X x) ∂ν := by
    simp_rw [← hder]
    exact integral_mul_fderiv_openDomain hU f _ hf (hcomp i) (hcompc i) (hcomps i) (b i)
  have hl (i : Fin (Module.finrank ℝ W)) :
      Integrable (fun x => f x * inner ℝ (b i) (fderiv ℝ X x (b i))) ν := by
    simp_rw [← hder]
    exact (integrable_fderiv_products_openDomain hU f _ hf
      (hcomp i) (hcompc i) (hcomps i) (b i)).1
  have hr (i : Fin (Module.finrank ℝ W)) :
      Integrable (fun x => fderiv ℝ f x (b i) * inner ℝ (b i) (X x)) ν :=
    (integrable_fderiv_products_openDomain hU f _ hf
      (hcomp i) (hcompc i) (hcomps i) (b i)).2
  simp_rw [localDivergence_eq_sum X _ b, Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => hl i)]
  simp_rw [hi]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum _ (fun i _ => hr i)]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    dsimp only
    conv_rhs => rw [← b.sum_repr (X x)]
    simp [_root_.map_sum, map_smul, OrthonormalBasis.repr_apply_apply, mul_comm]

/-- The density integral on an open domain only requires continuity and
nonnegativity of the density on that domain. -/
theorem setIntegral_localDensityMeasure_openDomain {U : Set W} (hU : IsOpen U)
    (ρ : W → ℝ) (hρ : ContinuousOn ρ U) (hpos : ∀ x ∈ U, 0 ≤ ρ x) (f : W → ℝ) :
    ∫ x in U, f x ∂localDensityMeasure ν ρ = ∫ x in U, ρ x * f x ∂ν := by
  unfold localDensityMeasure
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul₀
    (hρ.aemeasurable hU.measurableSet).ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) _ hU.measurableSet]
  apply setIntegral_congr_fun hU.measurableSet
  intro x hx
  dsimp only
  rw [ENNReal.toReal_ofReal (hpos x hx), smul_eq_mul]

/-- Weighted Green identity with all metric-density assumptions confined to
the open chart domain. No smooth positive extension of the density is needed. -/
theorem setIntegral_mul_localDensityDivergence_openDomain {U : Set W} (hU : IsOpen U)
    (ρ f : W → ℝ) (X : W → W) (hρ : ContDiffOn ℝ 1 ρ U)
    (hpos : ∀ x ∈ U, 0 < ρ x) (hf : ContDiffOn ℝ 1 f U)
    (hX : ContDiffOn ℝ 1 X U) (hc : HasCompactSupport X) (hs : tsupport X ⊆ U) :
    ∫ x in U, f x * localDensityDivergence ρ X x ∂localDensityMeasure ν ρ =
      -∫ x in U, fderiv ℝ f x (X x) ∂localDensityMeasure ν ρ := by
  let Y := fun x => ρ x • X x
  have hYs : tsupport Y ⊆ U := (tsupport_smul_subset_right ρ X).trans hs
  have hYc : HasCompactSupport Y := hc.smul_left
  have hYd : ContDiffOn ℝ 1 Y U := hρ.smul hX
  rw [setIntegral_localDensityMeasure_openDomain hU ρ hρ.continuousOn
    (fun x hx => (hpos x hx).le),
    setIntegral_localDensityMeasure_openDomain hU ρ hρ.continuousOn
      (fun x hx => (hpos x hx).le)]
  have hl : ∀ x ∈ U, ρ x * (f x * localDensityDivergence ρ X x) =
      f x * localDivergence Y x := by
    intro x hx
    dsimp only [localDensityDivergence, Y]
    field_simp [(hpos x hx).ne']
  rw [setIntegral_congr_fun hU.measurableSet hl]
  have hr : ∀ x ∈ U, ρ x * fderiv ℝ f x (X x) = fderiv ℝ f x (Y x) := by
    intro x _
    simp only [Y, map_smul, smul_eq_mul]
  rw [setIntegral_congr_fun hU.measurableSet hr]
  have hlz : ∀ x, x ∉ U → f x * localDivergence Y x = 0 := by
    intro x hx
    have hn : x ∉ tsupport Y := fun h => hx (hYs h)
    simp [localDivergence, fderiv_of_notMem_tsupport ℝ hn]
  have hrz : ∀ x, x ∉ U → fderiv ℝ f x (Y x) = 0 := by
    intro x hx
    have hn : x ∉ tsupport Y := fun h => hx (hYs h)
    rw [image_eq_zero_of_notMem_tsupport hn, map_zero]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hlz,
    setIntegral_eq_integral_of_forall_compl_eq_zero hrz]
  exact integral_mul_localDivergence_openDomain hU f Y hf hYd hYc hYs

/-- Open-domain geometric Green formula for the coordinate connection trace.
Metric compatibility and zero torsion are required only on the chart domain. -/
theorem setIntegral_mul_localConnectionDivergence_openDomain
    {κ : Type*} [Fintype κ] [DecidableEq κ] {U : Set W} (hU : IsOpen U)
    (b : Module.Basis κ ℝ W) (G : W → Matrix κ κ ℝ)
    (Γ : W → W →L[ℝ] W →L[ℝ] W) (f : W → ℝ) (X : W → W)
    (hG : ContDiffOn ℝ 1 G U) (hpos : ∀ x ∈ U, (G x).PosDef)
    (hf : ContDiffOn ℝ 1 f U) (hX : ContDiffOn ℝ 1 X U)
    (hc : HasCompactSupport X) (hs : tsupport X ⊆ U)
    (hcompat : ∀ x ∈ U, localMetricCompatible b G Γ x)
    (htorsion : ∀ x ∈ U, ∀ u v, Γ x u v = Γ x v u) :
    ∫ x in U, f x * localConnectionDivergence Γ X x
        ∂localDensityMeasure ν (fun y => matrixDensity (G y)) =
      -∫ x in U, fderiv ℝ f x (X x)
        ∂localDensityMeasure ν (fun y => matrixDensity (G y)) := by
  have hρ : ContDiffOn ℝ 1 (fun y => matrixDensity (G y)) U := by
    apply ContDiffOn.sqrt
    · exact (determinantMultilinear (ι := κ)).contDiff.comp_contDiffOn hG
    · intro x hx
      exact (hpos x hx).det_pos.ne'
  have heq : ∀ x ∈ U, f x * localConnectionDivergence Γ X x =
      f x * localDensityDivergence (fun y => matrixDensity (G y)) X x := by
    intro x hx
    rw [localConnectionDivergence_eq_density b G Γ X x
      ((hG.contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num)) (hpos x hx)
      ((hX.contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num))
      (hcompat x hx) (htorsion x hx)]
  rw [setIntegral_congr_fun hU.measurableSet heq]
  exact setIntegral_mul_localDensityDivergence_openDomain hU _ f X hρ
    (fun x hx => matrixDensity_pos _ (hpos x hx)) hf hX hc hs

end AlmostSchur
