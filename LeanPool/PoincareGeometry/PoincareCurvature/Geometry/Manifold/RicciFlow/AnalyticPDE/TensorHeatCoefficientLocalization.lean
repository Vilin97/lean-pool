/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/
module


/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorHeatLocalizedInverse
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.CompactCoefficientExtension
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorHeatGeometricRegularity
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.FiniteSmoothTrivializingCover

/-!
# Producing localized tensor-heat coefficient data

This legacy-import bridge combines chart-local `C¹` coefficient fields,
compactly supported extensions, and a normalized cutoff into the exact
quantitative data consumed by `TensorHeatLocalizedInverse`.
-/

@[expose] public section

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace RicciFlow
namespace AnalyticPDE

variable {X W : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

@[reducible] local instance coefficientLocalizationFirstNormedAddCommGroup :
    NormedAddCommGroup (X →L[ℝ] W) := ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance coefficientLocalizationFirstNormedSpace :
    NormedSpace ℝ (X →L[ℝ] W) := ContinuousLinearMap.toNormedSpace
@[reducible] local instance coefficientLocalizationSecondNormedAddCommGroup :
    NormedAddCommGroup (X →L[ℝ] X →L[ℝ] W) :=
  ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance coefficientLocalizationSecondNormedSpace :
    NormedSpace ℝ (X →L[ℝ] X →L[ℝ] W) := ContinuousLinearMap.toNormedSpace
@[reducible] local instance coefficientLocalizationPrincipalNormedAddCommGroup :
    NormedAddCommGroup ((X →L[ℝ] X →L[ℝ] W) →L[ℝ] W) :=
  ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance coefficientLocalizationPrincipalNormedSpace :
    NormedSpace ℝ ((X →L[ℝ] X →L[ℝ] W) →L[ℝ] W) :=
  ContinuousLinearMap.toNormedSpace
@[reducible] local instance coefficientLocalizationFirstCoeffNormedAddCommGroup :
    NormedAddCommGroup ((X →L[ℝ] W) →L[ℝ] W) :=
  ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance coefficientLocalizationFirstCoeffNormedSpace :
    NormedSpace ℝ ((X →L[ℝ] W) →L[ℝ] W) :=
  ContinuousLinearMap.toNormedSpace

namespace TensorHeatLocalizedCoefficientData

/-- Assemble quantitative localization data from a normalized cutoff and
three compactly supported coefficient extensions. -/
def ofExtensions
    (χ : NormalizedCutoffControl X)
    {A₀ : X → ((X →L[ℝ] X →L[ℝ] W) →L[ℝ] W)}
    {B₀ : X → ((X →L[ℝ] W) →L[ℝ] W)}
    {C₀ : X → (W →L[ℝ] W)}
    {K U : Set X}
    (Aext : CompactCoefficientExtension X _ A₀ K U)
    (Bext : CompactCoefficientExtension X _ B₀ K U)
    (Cext : CompactCoefficientExtension X _ C₀ K U)
    (center : X) : TensorHeatLocalizedCoefficientData X W where
  cutoff := χ.cutoff
  principal := Aext.extension
  first := Bext.extension
  zero := Cext.extension
  center := center
  cutoffBound := 1
  cutoffLipschitz := χ.lipschitzBound
  supportRadius := χ.supportRadius
  principalLipschitz := Aext.lipschitzBound
  firstBound := Bext.bound
  firstLipschitz := Bext.lipschitzBound
  zeroBound := Cext.bound
  zeroLipschitz := Cext.lipschitzBound
  cutoffBound_nonneg := by norm_num
  cutoffLipschitz_nonneg := χ.lipschitzBound_nonneg
  supportRadius_nonneg := χ.supportRadius_nonneg
  principalLipschitz_nonneg := Aext.lipschitzBound_nonneg
  firstBound_nonneg := Bext.bound_nonneg
  firstLipschitz_nonneg := Bext.lipschitzBound_nonneg
  zeroBound_nonneg := Cext.bound_nonneg
  zeroLipschitz_nonneg := Cext.lipschitzBound_nonneg
  norm_cutoff_le := χ.abs_le_one
  cutoff_lipschitz := χ.abs_sub_le
  support_radius := χ.support_norm_le
  principal_lipschitz := Aext.norm_sub_le
  norm_first_le := Bext.norm_le
  first_lipschitz := Bext.norm_sub_le
  norm_zero_le := Cext.norm_le
  zero_lipschitz := Cext.norm_sub_le

/-- Three chart-local `C¹` coefficient fields admit simultaneous compactly
supported quantitative localization on any compact core inside their common
open domain.  The resulting fields agree with the originals near the core,
and the cutoff itself equals one there. -/
theorem exists_of_contDiffOn
    {A₀ : X → ((X →L[ℝ] X →L[ℝ] W) →L[ℝ] W)}
    {B₀ : X → ((X →L[ℝ] W) →L[ℝ] W)}
    {C₀ : X → (W →L[ℝ] W)}
    {K U : Set X}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hA : ContDiffOn ℝ 1 A₀ U)
    (hB : ContDiffOn ℝ 1 B₀ U)
    (hC : ContDiffOn ℝ 1 C₀ U)
    (center : X) :
    ∃ D : TensorHeatLocalizedCoefficientData X W,
      D.center = center ∧
      (∀ᶠ x in nhdsSet K, D.principal x = A₀ x) ∧
      (∀ᶠ x in nhdsSet K, D.first x = B₀ x) ∧
      (∀ᶠ x in nhdsSet K, D.zero x = C₀ x) ∧
      (∀ᶠ x in nhdsSet K, D.cutoff x = 1) := by
  obtain ⟨χ, _hχsupp, hχone, _hχrange⟩ :=
    exists_normalizedCutoffControl_one_nhdsSet_of_isCompact hK hU hKU
  obtain ⟨Aext⟩ := exists_compactCoefficientExtension_of_contDiffOn hK hU hKU hA
  obtain ⟨Bext⟩ := exists_compactCoefficientExtension_of_contDiffOn hK hU hKU hB
  obtain ⟨Cext⟩ := exists_compactCoefficientExtension_of_contDiffOn hK hU hKU hC
  refine ⟨ofExtensions χ Aext Bext Cext center, ?_⟩
  exact ⟨rfl, Aext.eventuallyEq_original, Bext.eventuallyEq_original,
    Cext.eventuallyEq_original, hχone⟩

/-- Assemble localized coefficient data with the two logically distinct
localizations separated: the coefficient extensions agree with the original
fields near the unscaled compact core `K`, while the normalized cutoff is one
on the closed unit ball in the rescaled variable.  This is the form needed to
identify the localized operator with the genuine chart operator. -/
theorem exists_of_contDiffOn_unitCutoff
    {A₀ : X → ((X →L[ℝ] X →L[ℝ] W) →L[ℝ] W)}
    {B₀ : X → ((X →L[ℝ] W) →L[ℝ] W)}
    {C₀ : X → (W →L[ℝ] W)}
    {K U : Set X}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hA : ContDiffOn ℝ 1 A₀ U)
    (hB : ContDiffOn ℝ 1 B₀ U)
    (hC : ContDiffOn ℝ 1 C₀ U)
    (center : X) :
    ∃ D : TensorHeatLocalizedCoefficientData X W,
      D.center = center ∧
      (∀ᶠ x in nhdsSet K, D.principal x = A₀ x) ∧
      (∀ᶠ x in nhdsSet K, D.first x = B₀ x) ∧
      (∀ᶠ x in nhdsSet K, D.zero x = C₀ x) ∧
      (∀ x ∈ Metric.closedBall (0 : X) 1, D.cutoff x = 1) := by
  obtain ⟨χ, hχone, _hχsupp⟩ :=
    exists_normalizedCutoffControl_one_on_closedBall (X := X)
  obtain ⟨Aext⟩ := exists_compactCoefficientExtension_of_contDiffOn hK hU hKU hA
  obtain ⟨Bext⟩ := exists_compactCoefficientExtension_of_contDiffOn hK hU hKU hB
  obtain ⟨Cext⟩ := exists_compactCoefficientExtension_of_contDiffOn hK hU hKU hC
  refine ⟨ofExtensions χ Aext Bext Cext center, ?_⟩
  exact ⟨rfl, Aext.eventuallyEq_original, Bext.eventuallyEq_original,
    Cext.eventuallyEq_original, hχone⟩

/-- If the chosen chart center belongs to the compact core, the localized
principal field has exactly the original principal coefficient there. -/
theorem principal_center_eq_of_mem
    {A₀ : X → ((X →L[ℝ] X →L[ℝ] W) →L[ℝ] W)}
    (D : TensorHeatLocalizedCoefficientData X W) {K : Set X}
    (hA : ∀ᶠ x in nhdsSet K, D.principal x = A₀ x)
    (hc : D.center ∈ K) :
    D.principal D.center = A₀ D.center := by
  have hnhds : ∀ᶠ x in nhds D.center, D.principal x = A₀ x :=
    (mem_nhdsSet_iff_forall.mp hA) D.center hc
  exact hnhds.self_of_nhds

/-- An eventual property at a center holds on every sufficiently small
positive affine image of the normalized closed unit ball.  This elementary
radius-extraction lemma is the bridge between neighborhood-valued extension
agreement and the normalized variables used by parabolic scaling. -/
theorem exists_radius_affine_closedBall_subset_of_eventually
    {P : X → Prop} {center : X} (hP : ∀ᶠ x in nhds center, P x) :
    ∃ ε > 0, ∀ r : ℝ, 0 < r → r < ε →
      ∀ z ∈ Metric.closedBall (0 : X) 1, P (center + r • z) := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hP
  refine ⟨ε, hε, ?_⟩
  intro r hr hrε z hz
  apply hball
  rw [Metric.mem_ball, dist_eq_norm]
  have hzNorm : ‖z‖ ≤ 1 := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hz
  calc
    ‖center + r • z - center‖ = ‖r • z‖ := by rw [add_sub_cancel_left]
    _ = r * ‖z‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    _ ≤ r * 1 := mul_le_mul_of_nonneg_left hzNorm hr.le
    _ < ε := by simpa using hrε

/-- Exact scale-correct agreement of the localized coefficient fields with
three physical coefficient functions throughout the normalized unit ball. -/
def FieldsAgreeOnUnitBall
    (D : TensorHeatLocalizedCoefficientData X W)
    (A₀ : X → ((X →L[ℝ] X →L[ℝ] W) →L[ℝ] W))
    (B₀ : X → ((X →L[ℝ] W) →L[ℝ] W))
    (C₀ : X → (W →L[ℝ] W))
    (U : Set X) (center : X) {t₀ T α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (r : ℝ) : Prop :=
  ∀ z : ℝ × X, z.2 ∈ Metric.closedBall (0 : X) 1 →
    center + r • z.2 ∈ U ∧
    ParabolicC0AlphaSpace.toFun
        (D.principalField (t₀ := t₀) (T := T) hα hα1 r) z =
      A₀ (center + r • z.2) ∧
    ParabolicC0AlphaSpace.toFun
        (D.firstField (t₀ := t₀) (T := T) hα hα1 r) z =
      r • B₀ (center + r • z.2) ∧
    ParabolicC0AlphaSpace.toFun
        (D.zeroField (t₀ := t₀) (T := T) hα hα1 r) z =
      r ^ 2 • C₀ (center + r • z.2)

/-- Near a compact core, extension agreement plus a normalized unit cutoff
gives exact equality between all three localized coefficient fields and the
genuinely centered-rescaled coefficients.  The returned radius also keeps
the physical affine image inside the original coefficient domain `U`. -/
theorem exists_radius_fields_eq_actual_on_unitBall
    {A₀ : X → ((X →L[ℝ] X →L[ℝ] W) →L[ℝ] W)}
    {B₀ : X → ((X →L[ℝ] W) →L[ℝ] W)}
    {C₀ : X → (W →L[ℝ] W)}
    (D : TensorHeatLocalizedCoefficientData X W)
    {K U : Set X} {center : X}
    (hcenter : D.center = center) (hc : center ∈ K)
    (hU : IsOpen U) (hKU : K ⊆ U)
    (hA : ∀ᶠ x in nhdsSet K, D.principal x = A₀ x)
    (hB : ∀ᶠ x in nhdsSet K, D.first x = B₀ x)
    (hC : ∀ᶠ x in nhdsSet K, D.zero x = C₀ x)
    (hcut : ∀ z ∈ Metric.closedBall (0 : X) 1, D.cutoff z = 1)
    {t₀ T α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ ε > 0, ∀ r : ℝ, 0 < r → r < ε →
      FieldsAgreeOnUnitBall (t₀ := t₀) (T := T)
        D A₀ B₀ C₀ U center hα hα1 r := by
  have hAcenter : ∀ᶠ x in nhds center, D.principal x = A₀ x :=
    (mem_nhdsSet_iff_forall.mp hA) center hc
  have hBcenter : ∀ᶠ x in nhds center, D.first x = B₀ x :=
    (mem_nhdsSet_iff_forall.mp hB) center hc
  have hCcenter : ∀ᶠ x in nhds center, D.zero x = C₀ x :=
    (mem_nhdsSet_iff_forall.mp hC) center hc
  have hUcenter : ∀ᶠ x in nhds center, x ∈ U :=
    hU.mem_nhds (hKU hc)
  obtain ⟨ε, hε, hεball⟩ :=
    exists_radius_affine_closedBall_subset_of_eventually
      (hUcenter.and (hAcenter.and (hBcenter.and hCcenter)))
  refine ⟨ε, hε, ?_⟩
  intro r hr hrε z hz
  obtain ⟨hzU, hzA, hzB, hzC⟩ := hεball r hr hrε z.2 hz
  have hzCut : D.cutoff z.2 = 1 := hcut z.2 hz
  refine ⟨hzU, ?_, ?_, ?_⟩
  · rw [D.toFun_principalField_of_cutoff_eq_one hα hα1 r z hzCut,
      hcenter, hzA]
  · rw [D.toFun_firstField_of_cutoff_eq_one hα hα1 r z hzCut,
      hcenter, hzB]
  · rw [D.toFun_zeroField_of_cutoff_eq_one hα hα1 r z hzCut,
      hcenter, hzC]

end TensorHeatLocalizedCoefficientData

/-! ## Actual connection-Laplacian coefficients -/

open Bundle FiberBundle CovariantDerivative
open PoincareCurvature.Bundle.Trivialization
open scoped Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]

variable {d : ℕ}

local notation "TM" => (TangentSpace I : M → Type _)
local notation "W₂" => (Fin d × Fin d → ℝ)
local notation "T₂" => (fun x : M => TM x →L[ℝ] TM x →L[ℝ] ℝ)
local notation "T₃" => (fun x : M => TM x →L[ℝ] T₂ x)

/- Select the same model and fiber norms as the geometric regularity theorem,
so its induced-connection class hypotheses refer to definitionally identical
two- and three-covariant-tensor bundles. -/
@[reducible] local instance localizationTwoModelNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  CovariantDerivative.coordinateTwoModelNormedAddCommGroup
@[reducible] local instance localizationTwoModelNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  CovariantDerivative.coordinateTwoModelNormedSpace
@[reducible] local instance localizationTwoFiberNormedAddCommGroup (x : M) :
    NormedAddCommGroup (T₂ x) :=
  CovariantDerivative.coordinateTwoFiberNormedAddCommGroup x
@[reducible] local instance localizationTwoFiberNormedSpace (x : M) :
    NormedSpace ℝ (T₂ x) :=
  CovariantDerivative.coordinateTwoFiberNormedSpace x
@[reducible] local instance localizationThreeModelNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  CovariantDerivative.coordinateThreeModelNormedAddCommGroup
@[reducible] local instance localizationThreeModelNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  CovariantDerivative.coordinateThreeModelNormedSpace
@[reducible] local instance localizationThreeFiberNormedAddCommGroup (x : M) :
    NormedAddCommGroup (T₃ x) :=
  CovariantDerivative.coordinateThreeFiberNormedAddCommGroup x
@[reducible] local instance localizationThreeFiberNormedSpace (x : M) :
    NormedSpace ℝ (T₃ x) :=
  CovariantDerivative.coordinateThreeFiberNormedSpace x

/-- The manifold patch cut out by a coordinate ball of radius `r` around
the preferred chart center. -/
def actualLocalTensorHeatPatch (p : M) (r : ℝ) : Set M :=
  (extChartAt I p).source ∩
    extChartAt I p ⁻¹' Metric.ball ((extChartAt I p) p) r

theorem isOpen_actualLocalTensorHeatPatch (p : M) (r : ℝ) :
    IsOpen (actualLocalTensorHeatPatch (I := I) p r) :=
  (continuousOn_extChartAt (I := I) p).isOpen_inter_preimage
    (isOpen_extChartAt_source (I := I) p) Metric.isOpen_ball

theorem mem_actualLocalTensorHeatPatch (p : M) {r : ℝ} (hr : 0 < r) :
    p ∈ actualLocalTensorHeatPatch (I := I) p r :=
  ⟨mem_extChartAt_source (I := I) p, Metric.mem_ball_self hr⟩

theorem actualLocalTensorHeatPatch_subset_chartSource (p : M) (r : ℝ) :
    actualLocalTensorHeatPatch (I := I) p r ⊆ (extChartAt I p).source :=
  inter_subset_left

/-- A point of a radius-`r` coordinate ball has normalized displacement in
the closed unit ball. -/
theorem inv_smul_sub_mem_closedBall_one_of_mem_ball
    {center y : E} {r : ℝ} (hr : 0 < r)
    (hy : y ∈ Metric.ball center r) :
    r⁻¹ • (y - center) ∈ Metric.closedBall (0 : E) 1 := by
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, norm_smul,
    Real.norm_eq_abs, abs_inv, abs_of_pos hr]
  rw [inv_mul_le_one₀ hr]
  rw [Metric.mem_ball, dist_eq_norm] at hy
  exact hy.le

/-- Exact unit-ball coefficient agreement forces the corresponding
radius-adapted manifold patch to remain in any physical domain `S` encoded
through the inverse chart. -/
theorem actualLocalTensorHeatPatch_subset_of_fieldsAgree
    {W' : Type*} [NormedAddCommGroup W'] [NormedSpace ℝ W']
    (D : TensorHeatLocalizedCoefficientData E W')
    {A₀ : E → ((E →L[ℝ] E →L[ℝ] W') →L[ℝ] W')}
    {B₀ : E → ((E →L[ℝ] W') →L[ℝ] W')}
    {C₀ : E → (W' →L[ℝ] W')} {S : Set M}
    {t₀ T α r : ℝ} (hα : 0 < α) (hα1 : α < 1) (hr : 0 < r)
    (hagree : TensorHeatLocalizedCoefficientData.FieldsAgreeOnUnitBall
      (t₀ := t₀) (T := T) D A₀ B₀ C₀
      ((extChartAt I p).target ∩ (extChartAt I p).symm ⁻¹' S)
      ((extChartAt I p) p) hα hα1 r) :
    actualLocalTensorHeatPatch (I := I) p r ⊆ S := by
  intro y hy
  let z : E := r⁻¹ • ((extChartAt I p) y - (extChartAt I p) p)
  have hz : z ∈ Metric.closedBall (0 : E) 1 :=
    inv_smul_sub_mem_closedBall_one_of_mem_ball hr hy.2
  have hphysical := (hagree (0, z) hz).1
  have hscale : (extChartAt I p) p + r • z = (extChartAt I p) y := by
    dsimp [z]
    rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul, add_sub_cancel]
  rw [hscale] at hphysical
  have hsource : y ∈ (extChartAt I p).source := hy.1
  have hinv : (extChartAt I p).symm ((extChartAt I p) y) = y :=
    (extChartAt I p).left_inv hsource
  have hyS := hphysical.2
  change (extChartAt I p).symm ((extChartAt I p) y) ∈ S at hyS
  rwa [hinv] at hyS

/-- End-to-end local solvability for the coefficient fields derived from the
actual connection Laplacian.  The only analytic input is `C¹` regularity of
those three *defined* coefficient fields on the chosen chart domain; no
coordinate operator or differential identity is postulated. -/
theorem exists_radius_actualLocalTensorHeatSolutionL_of_contDiffOn
    (cov : CovariantDerivative I E TM)
    (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis (Fin d) ℝ E) {x : M}
    (hxFrame : x ∈ e.baseSet)
    (hxChart : x ∈ (extChartAt I p).source)
    {K U : Set E}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hxK : (extChartAt I p) x ∈ K)
    (hA : ContDiffOn ℝ 1
      (localTensorHeatPrincipalCoefficient (I := I) p e b) U)
    (hB : ContDiffOn ℝ 1
      (localTensorHeatFirstCoefficient (I := I) cov p e b) U)
    (hC : ContDiffOn ℝ 1
      (localTensorHeatZeroCoefficient (I := I) cov p e b) U)
    {t₀ T α : ℝ} (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1) :
    ∃ D : TensorHeatLocalizedCoefficientData E W₂,
      D.center = (extChartAt I p) x ∧
      (∀ᶠ z in nhdsSet K,
        D.principal z = localTensorHeatPrincipalCoefficient (I := I) p e b z) ∧
      (∀ᶠ z in nhdsSet K,
        D.first z = localTensorHeatFirstCoefficient (I := I) cov p e b z) ∧
      (∀ᶠ z in nhdsSet K,
        D.zero z = localTensorHeatZeroCoefficient (I := I) cov p e b z) ∧
      (∀ᶠ z in nhdsSet K, D.cutoff z = 1) ∧
      ∃ δ > 0, ∀ r : ℝ, 0 < r → r < δ →
        ∃ Q : ParabolicC0AlphaBanach E W₂ α
              (parabolicFiniteCylinder E t₀ T) →L[ℝ]
            FiniteParabolicC2AlphaBanach E W₂ t₀ T α,
          (FiniteParabolicC2AlphaBanach.coordinateCauchyL
            (D.principalField hα hα1 r) (D.firstField hα hα1 r)
            (D.zeroField hα hα1 r)).comp Q =
          ContinuousLinearMap.id ℝ
            (ParabolicC0AlphaBanach E W₂ α
              (parabolicFiniteCylinder E t₀ T)) := by
  obtain ⟨D, hDcenter, hDA, hDB, hDC, hDχ⟩ :=
    TensorHeatLocalizedCoefficientData.exists_of_contDiffOn
      hK hU hKU hA hB hC ((extChartAt I p) x)
  have hcenter : D.principal D.center =
      frozenLocalTensorHeatPrincipalCoefficient (I := I) p e b x := by
    have hc := TensorHeatLocalizedCoefficientData.principal_center_eq_of_mem
      D hDA (hDcenter ▸ hxK)
    rw [hDcenter]
    rw [hDcenter] at hc
    simpa [frozenLocalTensorHeatPrincipalCoefficient] using hc
  refine ⟨D, hDcenter, hDA, hDB, hDC, hDχ, ?_⟩
  exact exists_radius_localizedTensorHeatSolutionL
    (I := I) p e b hxFrame hxChart hT hα hα1 D hcenter

/-- End-to-end local solvability for the actual connection-Laplacian
coefficients, retaining the canonical zero-initial-trace identity supplied by
the localized inverse construction. -/
theorem exists_radius_actualLocalTensorHeatSolutionL_of_contDiffOn_zeroTrace
    (cov : CovariantDerivative I E TM)
    (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis (Fin d) ℝ E) {x : M}
    (hxFrame : x ∈ e.baseSet)
    (hxChart : x ∈ (extChartAt I p).source)
    {K U : Set E}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hxK : (extChartAt I p) x ∈ K)
    (hA : ContDiffOn ℝ 1
      (localTensorHeatPrincipalCoefficient (I := I) p e b) U)
    (hB : ContDiffOn ℝ 1
      (localTensorHeatFirstCoefficient (I := I) cov p e b) U)
    (hC : ContDiffOn ℝ 1
      (localTensorHeatZeroCoefficient (I := I) cov p e b) U)
    {t₀ T α : ℝ} (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1) :
    ∃ D : TensorHeatLocalizedCoefficientData E W₂,
      D.center = (extChartAt I p) x ∧
      (∀ᶠ z in nhdsSet K,
        D.principal z = localTensorHeatPrincipalCoefficient (I := I) p e b z) ∧
      (∀ᶠ z in nhdsSet K,
        D.first z = localTensorHeatFirstCoefficient (I := I) cov p e b z) ∧
      (∀ᶠ z in nhdsSet K,
        D.zero z = localTensorHeatZeroCoefficient (I := I) cov p e b z) ∧
      (∀ᶠ z in nhdsSet K, D.cutoff z = 1) ∧
      ∃ δ > 0, ∀ r : ℝ, 0 < r → r < δ →
        ∃ Q : ParabolicC0AlphaBanach E W₂ α
              (parabolicFiniteCylinder E t₀ T) →L[ℝ]
            FiniteParabolicC2AlphaBanach E W₂ t₀ T α,
          (FiniteParabolicC2AlphaBanach.coordinateCauchyL
            (D.principalField hα hα1 r) (D.firstField hα hα1 r)
            (D.zeroField hα hα1 r)).comp Q =
            ContinuousLinearMap.id ℝ
              (ParabolicC0AlphaBanach E W₂ α
                (parabolicFiniteCylinder E t₀ T)) ∧
          (FiniteParabolicC2AlphaBanach.initialTraceL
            (X := E) (E := W₂) hT hα).comp Q = 0 := by
  obtain ⟨D, hDcenter, hDA, hDB, hDC, hDχ⟩ :=
    TensorHeatLocalizedCoefficientData.exists_of_contDiffOn
      hK hU hKU hA hB hC ((extChartAt I p) x)
  have hcenter : D.principal D.center =
      frozenLocalTensorHeatPrincipalCoefficient (I := I) p e b x := by
    have hc := TensorHeatLocalizedCoefficientData.principal_center_eq_of_mem
      D hDA (hDcenter ▸ hxK)
    rw [hDcenter]
    rw [hDcenter] at hc
    simpa [frozenLocalTensorHeatPrincipalCoefficient] using hc
  refine ⟨D, hDcenter, hDA, hDB, hDC, hDχ, ?_⟩
  exact exists_radius_localizedTensorHeatSolutionL_zeroTrace
    (I := I) p e b hxFrame hxChart hT hα hα1 D hcenter

/-- Scale-correct local inversion for the actual connection-Laplacian
coefficients.  The same positive radius controls the zero-trace inverse,
exact agreement with the centered-rescaled genuine coefficients on the
normalized unit ball, and containment in the chart-and-frame domain `U`. -/
theorem exists_radius_actualLocalTensorHeatSolutionL_of_contDiffOn_unitBall_zeroTrace
    (cov : CovariantDerivative I E TM)
    (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis (Fin d) ℝ E) {x : M}
    (hxFrame : x ∈ e.baseSet)
    (hxChart : x ∈ (extChartAt I p).source)
    {K U : Set E}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hxK : (extChartAt I p) x ∈ K)
    (hA : ContDiffOn ℝ 1
      (localTensorHeatPrincipalCoefficient (I := I) p e b) U)
    (hB : ContDiffOn ℝ 1
      (localTensorHeatFirstCoefficient (I := I) cov p e b) U)
    (hC : ContDiffOn ℝ 1
      (localTensorHeatZeroCoefficient (I := I) cov p e b) U)
    {t₀ T α : ℝ} (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1) :
    ∃ D : TensorHeatLocalizedCoefficientData E W₂,
      D.center = (extChartAt I p) x ∧
      (∀ᶠ z in nhdsSet K,
        D.principal z = localTensorHeatPrincipalCoefficient (I := I) p e b z) ∧
      (∀ᶠ z in nhdsSet K,
        D.first z = localTensorHeatFirstCoefficient (I := I) cov p e b z) ∧
      (∀ᶠ z in nhdsSet K,
        D.zero z = localTensorHeatZeroCoefficient (I := I) cov p e b z) ∧
      (∀ z ∈ Metric.closedBall (0 : E) 1, D.cutoff z = 1) ∧
      ∃ δ > 0, ∀ r : ℝ, 0 < r → r < δ →
        TensorHeatLocalizedCoefficientData.FieldsAgreeOnUnitBall
          (t₀ := t₀) (T := T)
          D (localTensorHeatPrincipalCoefficient (I := I) p e b)
          (localTensorHeatFirstCoefficient (I := I) cov p e b)
          (localTensorHeatZeroCoefficient (I := I) cov p e b)
          U ((extChartAt I p) x) hα hα1 r ∧
        ∃ Q : ParabolicC0AlphaBanach E W₂ α
              (parabolicFiniteCylinder E t₀ T) →L[ℝ]
            FiniteParabolicC2AlphaBanach E W₂ t₀ T α,
          (FiniteParabolicC2AlphaBanach.coordinateCauchyL
            (D.principalField hα hα1 r) (D.firstField hα hα1 r)
            (D.zeroField hα hα1 r)).comp Q =
              ContinuousLinearMap.id ℝ
                (ParabolicC0AlphaBanach E W₂ α
                  (parabolicFiniteCylinder E t₀ T)) ∧
          (FiniteParabolicC2AlphaBanach.initialTraceL
            (X := E) (E := W₂) hT hα).comp Q = 0 := by
  obtain ⟨D, hDcenter, hDA, hDB, hDC, hDcut⟩ :=
    TensorHeatLocalizedCoefficientData.exists_of_contDiffOn_unitCutoff
      hK hU hKU hA hB hC ((extChartAt I p) x)
  have hcenter : D.principal D.center =
      frozenLocalTensorHeatPrincipalCoefficient (I := I) p e b x := by
    have hc := TensorHeatLocalizedCoefficientData.principal_center_eq_of_mem
      D hDA (hDcenter ▸ hxK)
    rw [hDcenter]
    rw [hDcenter] at hc
    simpa [frozenLocalTensorHeatPrincipalCoefficient] using hc
  obtain ⟨ε, hε, hagree⟩ :=
    TensorHeatLocalizedCoefficientData.exists_radius_fields_eq_actual_on_unitBall
      D hDcenter hxK hU hKU hDA hDB hDC hDcut hα hα1
  obtain ⟨δ, hδ, hsolve⟩ :=
    exists_radius_localizedTensorHeatSolutionL_zeroTrace
      (I := I) p e b hxFrame hxChart hT hα hα1 D hcenter
  refine ⟨D, hDcenter, hDA, hDB, hDC, hDcut,
    min ε δ, lt_min hε hδ, ?_⟩
  intro r hr hrmin
  have hrε : r < ε := hrmin.trans_le (min_le_left ε δ)
  have hrδ : r < δ := hrmin.trans_le (min_le_right ε δ)
  exact ⟨hagree r hr hrε, hsolve r hr hrδ⟩

/-- Local right-invertibility for the coefficient fields of the genuine
connection Laplacian, with all coefficient regularity derived from the
Riemannian metric, the moving frame, and the induced tensor connections.

Unlike `exists_radius_actualLocalTensorHeatSolutionL_of_contDiffOn`, this
statement has no hypotheses asserting regularity of the assembled coordinate
operators. -/
theorem exists_radius_actualLocalTensorHeatSolutionL
    [I.Boundaryless]
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 3 E TM I]
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 2]
    [ContMDiffCovariantDerivative
      (covariantThreeTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (hpFrame : p ∈ e.baseSet)
    (b : Module.Basis (Fin d) ℝ E)
    {t₀ T α : ℝ} (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1) :
    ∃ D : TensorHeatLocalizedCoefficientData E W₂,
      D.center = (extChartAt I p) p ∧
      (∀ᶠ z in nhdsSet ({(extChartAt I p) p} : Set E),
        D.principal z = localTensorHeatPrincipalCoefficient (I := I) p e b z) ∧
      (∀ᶠ z in nhdsSet ({(extChartAt I p) p} : Set E),
        D.first z = localTensorHeatFirstCoefficient (I := I) cov p e b z) ∧
      (∀ᶠ z in nhdsSet ({(extChartAt I p) p} : Set E),
        D.zero z = localTensorHeatZeroCoefficient (I := I) cov p e b z) ∧
      (∀ᶠ z in nhdsSet ({(extChartAt I p) p} : Set E), D.cutoff z = 1) ∧
      ∃ δ > 0, ∀ r : ℝ, 0 < r → r < δ →
        ∃ Q : ParabolicC0AlphaBanach E W₂ α
              (parabolicFiniteCylinder E t₀ T) →L[ℝ]
            FiniteParabolicC2AlphaBanach E W₂ t₀ T α,
          (FiniteParabolicC2AlphaBanach.coordinateCauchyL
            (D.principalField hα hα1 r) (D.firstField hα hα1 r)
            (D.zeroField hα hα1 r)).comp Q =
          ContinuousLinearMap.id ℝ
            (ParabolicC0AlphaBanach E W₂ α
              (parabolicFiniteCylinder E t₀ T)) := by
  let U := (extChartAt I p).target ∩ (extChartAt I p).symm ⁻¹' e.baseSet
  let K : Set E := {(extChartAt I p) p}
  have hU : IsOpen U :=
    (continuousOn_extChartAt_symm (I := I) p).isOpen_inter_preimage
      (isOpen_extChartAt_target p) e.open_baseSet
  have hpTarget : (extChartAt I p) p ∈ (extChartAt I p).target :=
    mem_extChartAt_target p
  have hpU : (extChartAt I p) p ∈ U := by
    refine ⟨hpTarget, ?_⟩
    simpa using hpFrame
  obtain ⟨hA, hB, hC⟩ :=
    contDiffOn_actualTensorHeatCoefficients (I := I) cov p e b
  exact exists_radius_actualLocalTensorHeatSolutionL_of_contDiffOn
    (I := I) cov p e b hpFrame (mem_extChartAt_source p)
      (K := K) (U := U) isCompact_singleton
      hU (by simpa [K] using hpU) (by simp [K])
      hA hB hC hT hα hα1

/-- Local right-invertibility for the genuine connection Laplacian together
with the canonical zero-initial-trace identity, with coefficient regularity
derived from the geometric data. -/
theorem exists_radius_actualLocalTensorHeatSolutionL_zeroTrace
    [I.Boundaryless]
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 3 E TM I]
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 2]
    [ContMDiffCovariantDerivative
      (covariantThreeTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (hpFrame : p ∈ e.baseSet)
    (b : Module.Basis (Fin d) ℝ E)
    {t₀ T α : ℝ} (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1) :
    ∃ D : TensorHeatLocalizedCoefficientData E W₂,
      D.center = (extChartAt I p) p ∧
      (∀ᶠ z in nhdsSet ({(extChartAt I p) p} : Set E),
        D.principal z = localTensorHeatPrincipalCoefficient (I := I) p e b z) ∧
      (∀ᶠ z in nhdsSet ({(extChartAt I p) p} : Set E),
        D.first z = localTensorHeatFirstCoefficient (I := I) cov p e b z) ∧
      (∀ᶠ z in nhdsSet ({(extChartAt I p) p} : Set E),
        D.zero z = localTensorHeatZeroCoefficient (I := I) cov p e b z) ∧
      (∀ᶠ z in nhdsSet ({(extChartAt I p) p} : Set E), D.cutoff z = 1) ∧
      ∃ δ > 0, ∀ r : ℝ, 0 < r → r < δ →
        ∃ Q : ParabolicC0AlphaBanach E W₂ α
              (parabolicFiniteCylinder E t₀ T) →L[ℝ]
            FiniteParabolicC2AlphaBanach E W₂ t₀ T α,
          (FiniteParabolicC2AlphaBanach.coordinateCauchyL
            (D.principalField hα hα1 r) (D.firstField hα hα1 r)
            (D.zeroField hα hα1 r)).comp Q =
            ContinuousLinearMap.id ℝ
              (ParabolicC0AlphaBanach E W₂ α
                (parabolicFiniteCylinder E t₀ T)) ∧
          (FiniteParabolicC2AlphaBanach.initialTraceL
            (X := E) (E := W₂) hT hα).comp Q = 0 := by
  let U := (extChartAt I p).target ∩ (extChartAt I p).symm ⁻¹' e.baseSet
  let K : Set E := {(extChartAt I p) p}
  have hU : IsOpen U :=
    (continuousOn_extChartAt_symm (I := I) p).isOpen_inter_preimage
      (isOpen_extChartAt_target p) e.open_baseSet
  have hpTarget : (extChartAt I p) p ∈ (extChartAt I p).target :=
    mem_extChartAt_target p
  have hpU : (extChartAt I p) p ∈ U := by
    refine ⟨hpTarget, ?_⟩
    simpa using hpFrame
  obtain ⟨hA, hB, hC⟩ :=
    contDiffOn_actualTensorHeatCoefficients (I := I) cov p e b
  exact exists_radius_actualLocalTensorHeatSolutionL_of_contDiffOn_zeroTrace
    (I := I) cov p e b hpFrame (mem_extChartAt_source p)
      (K := K) (U := U) isCompact_singleton
      hU (by simpa [K] using hpU) (by simp [K])
      hA hB hC hT hα hα1

/-- Point-centered, scale-correct local inversion for the genuine connection
Laplacian.  The returned radius is already small enough both for analytic
invertibility and for exact coefficient agreement throughout the normalized
closed unit ball. -/
theorem exists_radius_actualLocalTensorHeatUnitBall_zeroTrace
    [I.Boundaryless]
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 3 E TM I]
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 2]
    [ContMDiffCovariantDerivative
      (covariantThreeTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (hpFrame : p ∈ e.baseSet)
    (b : Module.Basis (Fin d) ℝ E)
    {t₀ T α : ℝ} (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1) :
    ∃ D : TensorHeatLocalizedCoefficientData E W₂,
      D.center = (extChartAt I p) p ∧
      (∀ z ∈ Metric.closedBall (0 : E) 1, D.cutoff z = 1) ∧
      ∃ δ > 0, ∀ r : ℝ, 0 < r → r < δ →
        TensorHeatLocalizedCoefficientData.FieldsAgreeOnUnitBall
          (t₀ := t₀) (T := T)
          D (localTensorHeatPrincipalCoefficient (I := I) p e b)
          (localTensorHeatFirstCoefficient (I := I) cov p e b)
          (localTensorHeatZeroCoefficient (I := I) cov p e b)
          ((extChartAt I p).target ∩ (extChartAt I p).symm ⁻¹' e.baseSet)
          ((extChartAt I p) p) hα hα1 r ∧
        ∃ Q : ParabolicC0AlphaBanach E W₂ α
              (parabolicFiniteCylinder E t₀ T) →L[ℝ]
            FiniteParabolicC2AlphaBanach E W₂ t₀ T α,
          (FiniteParabolicC2AlphaBanach.coordinateCauchyL
            (D.principalField hα hα1 r) (D.firstField hα hα1 r)
            (D.zeroField hα hα1 r)).comp Q =
              ContinuousLinearMap.id ℝ
                (ParabolicC0AlphaBanach E W₂ α
                  (parabolicFiniteCylinder E t₀ T)) ∧
          (FiniteParabolicC2AlphaBanach.initialTraceL
            (X := E) (E := W₂) hT hα).comp Q = 0 := by
  let U := (extChartAt I p).target ∩ (extChartAt I p).symm ⁻¹' e.baseSet
  let K : Set E := {(extChartAt I p) p}
  have hU : IsOpen U :=
    (continuousOn_extChartAt_symm (I := I) p).isOpen_inter_preimage
      (isOpen_extChartAt_target p) e.open_baseSet
  have hpU : (extChartAt I p) p ∈ U := by
    refine ⟨mem_extChartAt_target p, ?_⟩
    simpa using hpFrame
  obtain ⟨hA, hB, hC⟩ :=
    contDiffOn_actualTensorHeatCoefficients (I := I) cov p e b
  obtain ⟨D, hDcenter, _hDA, _hDB, _hDC, hDcut, δ, hδ, hlocal⟩ :=
    exists_radius_actualLocalTensorHeatSolutionL_of_contDiffOn_unitBall_zeroTrace
      (I := I) cov p e b hpFrame (mem_extChartAt_source p)
        (K := K) (U := U) isCompact_singleton hU
        (by simpa [K] using hpU) (by simp [K])
        hA hB hC hT hα hα1
  exact ⟨D, hDcenter, hDcut, δ, hδ, hlocal⟩

/-- A radius-adapted finite smooth cover carrying exact local zero-trace
inverses for the genuine connection Laplacian.  Radii and local analytic data
are chosen pointwise first; compactness and a smooth partition of unity are
applied only afterwards, so every subordinate support lies in a patch whose
own scaling radius has already been verified. -/
theorem exists_finiteSmoothActualLocalTensorHeatCover_zeroTrace
    [CompactSpace M] [SigmaCompactSpace M]
    [I.Boundaryless]
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 3 E TM I]
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 2]
    [ContMDiffCovariantDerivative
      (covariantThreeTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    (b : Module.Basis (Fin d) ℝ E)
    {t₀ T α : ℝ} (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1) :
    ∃ (radius : M → ℝ)
      (D : M → TensorHeatLocalizedCoefficientData E W₂)
      (Q : M → ParabolicC0AlphaBanach E W₂ α
            (parabolicFiniteCylinder E t₀ T) →L[ℝ]
          FiniteParabolicC2AlphaBanach E W₂ t₀ T α),
      (∀ p, 0 < radius p) ∧
      (∀ p, (D p).center = (extChartAt I p) p) ∧
      (∀ p, TensorHeatLocalizedCoefficientData.FieldsAgreeOnUnitBall
        (t₀ := t₀) (T := T)
        (D p)
        (localTensorHeatPrincipalCoefficient (I := I) p
          (trivializationAt E TM p) b)
        (localTensorHeatFirstCoefficient (I := I) cov p
          (trivializationAt E TM p) b)
        (localTensorHeatZeroCoefficient (I := I) cov p
          (trivializationAt E TM p) b)
        ((extChartAt I p).target ∩
          (extChartAt I p).symm ⁻¹' (trivializationAt E TM p).baseSet)
        ((extChartAt I p) p) hα hα1 (radius p)) ∧
      (∀ p,
        (FiniteParabolicC2AlphaBanach.coordinateCauchyL
          ((D p).principalField hα hα1 (radius p))
          ((D p).firstField hα hα1 (radius p))
          ((D p).zeroField hα hα1 (radius p))).comp (Q p) =
            ContinuousLinearMap.id ℝ
              (ParabolicC0AlphaBanach E W₂ α
                (parabolicFiniteCylinder E t₀ T))) ∧
      (∀ p, (FiniteParabolicC2AlphaBanach.initialTraceL
        (X := E) (E := W₂) hT hα).comp (Q p) = 0) ∧
      (∀ p, actualLocalTensorHeatPatch (I := I) p (radius p) ⊆
        (trivializationAt E TM p).baseSet) ∧
      Nonempty
        (FiniteSmoothPointwiseSubordinateCover I
          (fun p => actualLocalTensorHeatPatch (I := I) p (radius p))) := by
  classical
  have hall : ∀ p : M,
      ∃ D : TensorHeatLocalizedCoefficientData E W₂,
        D.center = (extChartAt I p) p ∧
        (∀ z ∈ Metric.closedBall (0 : E) 1, D.cutoff z = 1) ∧
        ∃ δ > 0, ∀ r : ℝ, 0 < r → r < δ →
          TensorHeatLocalizedCoefficientData.FieldsAgreeOnUnitBall
            (t₀ := t₀) (T := T) D
            (localTensorHeatPrincipalCoefficient (I := I) p
              (trivializationAt E TM p) b)
            (localTensorHeatFirstCoefficient (I := I) cov p
              (trivializationAt E TM p) b)
            (localTensorHeatZeroCoefficient (I := I) cov p
              (trivializationAt E TM p) b)
            ((extChartAt I p).target ∩
              (extChartAt I p).symm ⁻¹' (trivializationAt E TM p).baseSet)
            ((extChartAt I p) p) hα hα1 r ∧
          ∃ Q : ParabolicC0AlphaBanach E W₂ α
                (parabolicFiniteCylinder E t₀ T) →L[ℝ]
              FiniteParabolicC2AlphaBanach E W₂ t₀ T α,
            (FiniteParabolicC2AlphaBanach.coordinateCauchyL
              (D.principalField hα hα1 r) (D.firstField hα hα1 r)
              (D.zeroField hα hα1 r)).comp Q =
                ContinuousLinearMap.id ℝ
                  (ParabolicC0AlphaBanach E W₂ α
                    (parabolicFiniteCylinder E t₀ T)) ∧
            (FiniteParabolicC2AlphaBanach.initialTraceL
              (X := E) (E := W₂) hT hα).comp Q = 0 := fun p =>
    exists_radius_actualLocalTensorHeatUnitBall_zeroTrace
      (I := I) cov p (trivializationAt E TM p)
      (mem_baseSet_trivializationAt E TM p) b hT hα hα1
  choose D hDcenter hDcut δ hδ hrun using hall
  let radius : M → ℝ := fun p => δ p / 2
  have hradius : ∀ p, 0 < radius p := fun p => by
    dsimp [radius]
    linarith [hδ p]
  have hradius_lt : ∀ p, radius p < δ p := fun p => by
    dsimp [radius]
    linarith [hδ p]
  have hselected := fun p => hrun p (radius p) (hradius p) (hradius_lt p)
  let Q : M → ParabolicC0AlphaBanach E W₂ α
        (parabolicFiniteCylinder E t₀ T) →L[ℝ]
      FiniteParabolicC2AlphaBanach E W₂ t₀ T α :=
    fun p => Classical.choose (hselected p).2
  have hQspec := fun p => Classical.choose_spec (hselected p).2
  have hpatch : ∀ p,
      actualLocalTensorHeatPatch (I := I) p (radius p) ⊆
        (trivializationAt E TM p).baseSet := fun p =>
    actualLocalTensorHeatPatch_subset_of_fieldsAgree
      (I := I) (p := p) (D p) hα hα1 (hradius p) (hselected p).1
  have hcover :=
    FiniteSmoothPointwiseSubordinateCover.exists_of_isOpen_mem
      (I := I)
      (fun p => actualLocalTensorHeatPatch (I := I) p (radius p))
      (fun p => isOpen_actualLocalTensorHeatPatch (I := I) p (radius p))
      (fun p => mem_actualLocalTensorHeatPatch (I := I) p (hradius p))
  refine ⟨radius, D, Q, hradius, hDcenter,
    (fun p => (hselected p).1), ?_, ?_, hpatch, hcover⟩
  · intro p
    exact (hQspec p).1
  · intro p
    exact (hQspec p).2

/-- Local solvability for the genuine connection-Laplacian coefficients with
arbitrary initial data represented by a higher-parabolic extension.  Besides
the operator identities, this returns the actual affine solution and its
Schauder bound for every forcing and extension. -/
theorem exists_radius_actualLocalTensorHeatSolution_with_initialTrace
    [I.Boundaryless]
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 3 E TM I]
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 2]
    [ContMDiffCovariantDerivative
      (covariantThreeTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (hpFrame : p ∈ e.baseSet)
    (b : Module.Basis (Fin d) ℝ E)
    {t₀ T α : ℝ} (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1) :
    ∃ D : TensorHeatLocalizedCoefficientData E W₂,
      D.center = (extChartAt I p) p ∧
      (∀ᶠ z in nhdsSet ({(extChartAt I p) p} : Set E),
        D.principal z = localTensorHeatPrincipalCoefficient (I := I) p e b z) ∧
      (∀ᶠ z in nhdsSet ({(extChartAt I p) p} : Set E),
        D.first z = localTensorHeatFirstCoefficient (I := I) cov p e b z) ∧
      (∀ᶠ z in nhdsSet ({(extChartAt I p) p} : Set E),
        D.zero z = localTensorHeatZeroCoefficient (I := I) cov p e b z) ∧
      (∀ᶠ z in nhdsSet ({(extChartAt I p) p} : Set E), D.cutoff z = 1) ∧
      ∃ δ > 0, ∀ r : ℝ, 0 < r → r < δ →
        ∃ Q : ParabolicC0AlphaBanach E W₂ α
              (parabolicFiniteCylinder E t₀ T) →L[ℝ]
            FiniteParabolicC2AlphaBanach E W₂ t₀ T α,
          (FiniteParabolicC2AlphaBanach.coordinateCauchyL
            (D.principalField hα hα1 r) (D.firstField hα hα1 r)
            (D.zeroField hα hα1 r)).comp Q =
              ContinuousLinearMap.id ℝ
                (ParabolicC0AlphaBanach E W₂ α
                  (parabolicFiniteCylinder E t₀ T)) ∧
          (FiniteParabolicC2AlphaBanach.initialTraceL
            (X := E) (E := W₂) hT hα).comp Q = 0 ∧
          ∀ (h : FiniteParabolicC2AlphaBanach E W₂ t₀ T α)
            (q : ParabolicC0AlphaBanach E W₂ α
              (parabolicFiniteCylinder E t₀ T)),
            ∃ u : FiniteParabolicC2AlphaBanach E W₂ t₀ T α,
              FiniteParabolicC2AlphaBanach.coordinateCauchyL
                  (D.principalField hα hα1 r) (D.firstField hα hα1 r)
                  (D.zeroField hα hα1 r) u = q ∧
              FiniteParabolicC2AlphaBanach.initialTraceL hT hα u =
                FiniteParabolicC2AlphaBanach.initialTraceL hT hα h ∧
              ‖u‖ ≤ ‖h‖ + ‖Q‖ *
                ‖q - FiniteParabolicC2AlphaBanach.coordinateCauchyL
                  (D.principalField hα hα1 r) (D.firstField hα hα1 r)
                  (D.zeroField hα hα1 r) h‖ := by
  obtain ⟨D, hDcenter, hDA, hDB, hDC, hDχ, δ, hδ, hsolve⟩ :=
    exists_radius_actualLocalTensorHeatSolutionL_zeroTrace
      (I := I) cov p e hpFrame b hT hα hα1
  refine ⟨D, hDcenter, hDA, hDB, hDC, hDχ, δ, hδ, ?_⟩
  intro r hr hrδ
  obtain ⟨Q, hPQ, htrace⟩ := hsolve r hr hrδ
  refine ⟨Q, hPQ, htrace, ?_⟩
  intro h q
  exact LinearParabolicParametrix.exists_solution_with_trace_of_rightInverse_zeroTrace
    (FiniteParabolicC2AlphaBanach.initialTraceL hT hα)
    (FiniteParabolicC2AlphaBanach.coordinateCauchyL
      (D.principalField hα hα1 r) (D.firstField hα hα1 r)
      (D.zeroField hα hα1 r)) Q hPQ htrace h q

/-- Local solvability for the genuine connection-Laplacian coefficients with
an arbitrary bounded spatial `C^{2,α}` initial datum.  The datum is extended
constantly in time and the zero-trace inverse corrects its equation defect,
so the returned solution has exactly the prescribed canonical trace together
with an explicit affine Schauder estimate. -/
theorem exists_radius_actualLocalTensorHeatSolution_with_spatialInitialData
    [I.Boundaryless]
    [IsContMDiffRiemannianBundle I 2 E TM]
    [ContMDiffVectorBundle 3 E TM I]
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 2]
    [ContMDiffCovariantDerivative
      (covariantThreeTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (hpFrame : p ∈ e.baseSet)
    (b : Module.Basis (Fin d) ℝ E)
    {t₀ T α : ℝ} (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1) :
    ∃ D : TensorHeatLocalizedCoefficientData E W₂,
      D.center = (extChartAt I p) p ∧
      (∀ᶠ z in nhdsSet ({(extChartAt I p) p} : Set E),
        D.principal z = localTensorHeatPrincipalCoefficient (I := I) p e b z) ∧
      (∀ᶠ z in nhdsSet ({(extChartAt I p) p} : Set E),
        D.first z = localTensorHeatFirstCoefficient (I := I) cov p e b z) ∧
      (∀ᶠ z in nhdsSet ({(extChartAt I p) p} : Set E),
        D.zero z = localTensorHeatZeroCoefficient (I := I) cov p e b z) ∧
      (∀ᶠ z in nhdsSet ({(extChartAt I p) p} : Set E), D.cutoff z = 1) ∧
      ∃ δ > 0, ∀ r : ℝ, 0 < r → r < δ →
        ∃ Q : ParabolicC0AlphaBanach E W₂ α
              (parabolicFiniteCylinder E t₀ T) →L[ℝ]
            FiniteParabolicC2AlphaBanach E W₂ t₀ T α,
          (FiniteParabolicC2AlphaBanach.coordinateCauchyL
            (D.principalField hα hα1 r) (D.firstField hα hα1 r)
            (D.zeroField hα hα1 r)).comp Q =
              ContinuousLinearMap.id ℝ
                (ParabolicC0AlphaBanach E W₂ α
                  (parabolicFiniteCylinder E t₀ T)) ∧
          (FiniteParabolicC2AlphaBanach.initialTraceL
            (X := E) (E := W₂) hT hα).comp Q = 0 ∧
          ∀ (D₀ : BoundedSpatialC2AlphaData E W₂ α)
            (q : ParabolicC0AlphaBanach E W₂ α
              (parabolicFiniteCylinder E t₀ T)),
            ∃ u : FiniteParabolicC2AlphaBanach E W₂ t₀ T α,
              FiniteParabolicC2AlphaBanach.coordinateCauchyL
                  (D.principalField hα hα1 r) (D.firstField hα hα1 r)
                  (D.zeroField hα hα1 r) u = q ∧
              FiniteParabolicC2AlphaBanach.initialTraceL hT hα u = D₀.value ∧
              ‖u‖ ≤
                ‖D₀.timeIndependentExtension (t₀ := t₀) (T := T) hα‖ +
                ‖Q‖ *
                  ‖q - FiniteParabolicC2AlphaBanach.coordinateCauchyL
                    (D.principalField hα hα1 r) (D.firstField hα hα1 r)
                    (D.zeroField hα hα1 r)
                    (D₀.timeIndependentExtension
                      (t₀ := t₀) (T := T) hα)‖ := by
  obtain ⟨D, hDcenter, hDA, hDB, hDC, hDχ, δ, hδ, hsolve⟩ :=
    exists_radius_actualLocalTensorHeatSolution_with_initialTrace
      (I := I) cov p e hpFrame b hT hα hα1
  refine ⟨D, hDcenter, hDA, hDB, hDC, hDχ, δ, hδ, ?_⟩
  intro r hr hrδ
  obtain ⟨Q, hPQ, htrace, hsolveQ⟩ := hsolve r hr hrδ
  refine ⟨Q, hPQ, htrace, ?_⟩
  intro D₀ q
  obtain ⟨u, hPu, huTrace, huNorm⟩ :=
    hsolveQ (D₀.timeIndependentExtension (t₀ := t₀) (T := T) hα) q
  refine ⟨u, hPu, ?_, huNorm⟩
  rw [huTrace, D₀.initialTraceL_timeIndependentExtension hT hα]

end AnalyticPDE
end RicciFlow
