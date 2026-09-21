/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.ChartNormBounds
public import LeanPool.PoincareGeometry.AlmostSchur.ConnectionCoordinates

/-! # Pointwise gradient control for chart localization

The constants depend only on the fixed chart and cutoff. No L² localization
estimate is used or proved here.
-/

@[expose] public noncomputable section

open Bundle FiberBundle Set
open scoped Manifold ContDiff Topology
open RellichKondrachov.Geometry.Manifold.Sobolev

namespace AlmostSchur

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [IsManifold I ∞ M] [I.Boundaryless]
  [T2Space M] [CompactSpace M]
  [RiemannianBundle (TangentSpace I : M → Type _)]

local notation "euclideanGrad" =>
  RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.grad

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] [CompactSpace M]
  [RiemannianBundle (TangentSpace I : M → Type _)] in
/-- Localization factors through the fixed cutoff, even off the chart target. -/
theorem localize_eq_localize_one_mul (d : FiniteChartData (H := H) (M := M) I)
    (i : d.ι) (f : M → ℝ) :
    FiniteChartData.localize (d := d) f i = fun y =>
      FiniteChartData.localize (d := d) (fun _ => (1 : ℝ)) i y *
        (f ∘ (extChartAt I (d.center i)).symm) y := by
  funext y
  by_cases hy : y ∈ (extChartAt I (d.center i)).target <;>
    simp only [FiniteChartData.localize,
      FiniteChartData.vendorGeometryManifoldSobolevLocalization_chart,
      indicator, hy, if_true, if_false, Function.comp_apply, mul_one, zero_mul]

omit [I.Boundaryless] [T2Space M] [RiemannianBundle (TangentSpace I : M → Type _)] in
/-- The coordinate gradient vanishes outside the cutoff's topological support. -/
theorem grad_localize_eq_zero_off_tsupport
    (d : FiniteChartData (H := H) (M := M) I) (i : d.ι) (f : M → ℝ)
    {x : M} (hx : x ∈ (chartAt H (d.center i)).source)
    (hK : x ∉ tsupport (d.ρ i : M → ℝ)) :
    euclideanGrad (FiniteChartData.localize (d := d) f i)
      (extChartAt I (d.center i) x) = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro hy
  have hy' := FiniteChartData.tsupport_localize_subset_rhoSupportImage (d := d) f i
    (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.tsupport_grad_subset _ hy)
  obtain ⟨z, hz, heq⟩ := hy'
  have hzs := FiniteChartData.rhoSupportClosure_subset_source (d := d) i hz
  have hx' : x ∈ (extChartAt I (d.center i)).source := by simpa using hx
  have hzx : z = x := (extChartAt I (d.center i)).injOn hzs hx' heq
  apply hK
  simpa only [← hzx, FiniteChartData.rhoSupportClosure, tsupport] using hz

omit [T2Space M] in
/-- The pointwise localization bound, with explicit fixed nonnegative constants. -/
theorem norm_grad_localize_le
    (d : FiniteChartData (H := H) (M := M) I) (i : d.ι)
    {D B : ℝ} (hD0 : 0 ≤ D) (hB0 : 0 ≤ B)
    (hD : ∀ y : E,
      ‖fderiv ℝ (FiniteChartData.localize (d := d) (fun _ => (1 : ℝ)) i) y‖ ≤ D)
    (hB : ∀ x ∈ tsupport (d.ρ i : M → ℝ),
      ‖(trivializationAt E (TangentSpace I) (d.center i)).symmL ℝ x‖ ≤ B)
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) 1 f)
    {x : M} (hx : x ∈ (chartAt H (d.center i)).source) :
    ‖euclideanGrad (FiniteChartData.localize (d := d) f i)
      (extChartAt I (d.center i) x)‖ ≤ D * |f x| + B * ‖gradient (I := I) f x‖ := by
  by_cases hK : x ∈ tsupport (d.ρ i : M → ℝ)
  · let φ := extChartAt I (d.center i)
    let a := FiniteChartData.localize (d := d) (fun _ => (1 : ℝ)) i
    let g := f ∘ φ.symm
    have hx' : x ∈ φ.source := by simpa [φ] using hx
    have ha : DifferentiableAt ℝ a (φ x) :=
      (FiniteChartData.localize_mem_C1c (d := d) (f := fun _ => (1 : ℝ))
        contMDiff_const i).1.differentiable (by norm_num) _
    have hgM := (mdifferentiableAt_iff_source_of_mem_source (I := I)
      (I' := 𝓘(ℝ, ℝ)) hx).1 (hf.mdifferentiableAt (by norm_num))
    have hg : DifferentiableAt ℝ g (φ x) := by
      simpa [I.range_eq_univ, mdifferentiableWithinAt_univ,
        mdifferentiableAt_iff_differentiableAt, g, φ] using hgM
    have hcoord : fderiv ℝ g (φ x) =
        (mvfderiv I f x).comp
          ((trivializationAt E (TangentSpace I) (d.center i)).symmL ℝ x) := by
      ext u
      exact fderiv_chart_comp f (d.center i) x hx
        (hf.mdifferentiableAt (by norm_num)) u
    have hgn : ‖fderiv ℝ g (φ x)‖ ≤ B * ‖gradient (I := I) f x‖ := by
      rw [hcoord, norm_gradient]
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (by nlinarith [hB x hK, norm_nonneg (mvfderiv I f x)])
    have hav : a (φ x) = d.ρ i x := by
      change ((extChartAt I (d.center i)).target.indicator
        (fun y => d.ρ i ((extChartAt I (d.center i)).symm y) * 1)) (φ x) = _
      rw [indicator_of_mem (φ.map_source hx'), φ.left_inv hx', mul_one]
    have hgv : g (φ x) = f x := by simp [g, φ.left_inv hx']
    have hn : ‖euclideanGrad (FiniteChartData.localize (d := d) f i) (φ x)‖ =
        ‖fderiv ℝ (FiniteChartData.localize (d := d) f i) (φ x)‖ :=
      (InnerProductSpace.toDual ℝ E).symm.norm_map _
    rw [hn, localize_eq_localize_one_mul d i f, fderiv_fun_mul ha hg]
    calc
      ‖a (φ x) • fderiv ℝ g (φ x) + g (φ x) • fderiv ℝ a (φ x)‖
          ≤ ‖a (φ x)‖ * ‖fderiv ℝ g (φ x)‖ +
              ‖g (φ x)‖ * ‖fderiv ℝ a (φ x)‖ := by
            simpa only [norm_smul] using norm_add_le
              (a (φ x) • fderiv ℝ g (φ x)) (g (φ x) • fderiv ℝ a (φ x))
      _ ≤ D * |f x| + B * ‖gradient (I := I) f x‖ := by
        rw [hav, hgv, Real.norm_eq_abs, abs_of_nonneg (d.ρ.nonneg i x), Real.norm_eq_abs]
        have hfirst : d.ρ i x * ‖fderiv ℝ g (φ x)‖ ≤
            B * ‖gradient (I := I) f x‖ :=
          (mul_le_of_le_one_left (norm_nonneg _) (d.ρ.le_one i x)).trans hgn
        have hsecond := mul_le_mul_of_nonneg_left (hD (φ x)) (abs_nonneg (f x))
        dsimp only [a] at *
        nlinarith
  · rw [grad_localize_eq_zero_off_tsupport d i f hx hK, norm_zero]
    positivity

omit [T2Space M] in
/-- Fixed chart/cutoff constants work simultaneously for every C¹ scalar function. -/
theorem exists_norm_grad_localize_le
    [IsContinuousRiemannianBundle E (TangentSpace I : M → Type _)]
    (d : FiniteChartData (H := H) (M := M) I) (i : d.ι) :
    ∃ D B : ℝ, 0 ≤ D ∧ 0 ≤ B ∧
      ∀ (f : M → ℝ), ContMDiff I 𝓘(ℝ, ℝ) 1 f →
        ∀ x ∈ (chartAt H (d.center i)).source,
          ‖euclideanGrad (FiniteChartData.localize (d := d) f i)
            (extChartAt I (d.center i) x)‖ ≤
              D * |f x| + B * ‖gradient (I := I) f x‖ := by
  obtain ⟨D, hD0, hD⟩ := exists_bound_fderiv_localize_one d i
  obtain ⟨B, hB0, hB⟩ := exists_bound_tangentChart_symmL (I := I) (d.center i)
    (FiniteChartData.isCompact_rhoSupportClosure (d := d) i)
    (by simpa using FiniteChartData.rhoSupportClosure_subset_source (d := d) i)
  exact ⟨D, B, hD0, hB0, fun f hf x hx => norm_grad_localize_le d i hD0 hB0 hD hB f hf hx⟩

end AlmostSchur
