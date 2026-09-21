/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.LichnerowiczObata.RadialEndpointDistance
public import LeanPool.PoincareGeometry.AlmostSchur.ConnectionCoordinates
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Topology.DiscreteSubset

/-! # Local isolation of Obata critical points -/

@[expose] public noncomputable section
open Bundle Set AlmostSchur Manifold Filter
open scoped Manifold ContDiff Topology

namespace LichnerowiczObata

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]

local notation "TM" => (TangentSpace I : M → Type _)
local notation "LC" => (leviCivitaConnection (I := I) (M := M))

local instance : IsContMDiffRiemannianBundle I (↑(1 : ℕ)) E TM :=
  IsContMDiffRiemannianBundle.of_le (n := 1) (by norm_num)

/-- Gradient components in the tangent trivialization induced by a chart. -/
def obataGradientCoordinates (f : M → ℝ) (c : M) (z : E) : E :=
  (trivializationAt E TM c).continuousLinearMapAt ℝ ((extChartAt I c).symm z)
    (gradient (I := I) f ((extChartAt I c).symm z))

/-- At a critical point the connection term vanishes, so the Obata
Hessian equation becomes a scalar identity for the ordinary derivative. -/
theorem fderiv_obataGradientCoordinates {K : ℝ} {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f) {x : M}
    (hg : gradient (I := I) f x = 0)
    (hH : ∀ v w : TM x, hessian LC f x v w = -K * f x * inner ℝ v w) :
    fderiv ℝ (obataGradientCoordinates (I := I) f x) (extChartAt I x x) =
      (-K * f x) • (1 : E →L[ℝ] E) := by
  classical
  let e := trivializationAt E TM x
  have hc (v : TM x) : LC (gradient (I := I) f) x v = (-K * f x) • v := by
    apply ext_inner_right ℝ
    intro w
    rw [real_inner_smul_left]
    exact hH v w
  ext u
  have he := covariantDerivative_chart LC (Module.finBasis ℝ E)
    (gradient (I := I) f) x x (mem_chart_source H x) (mdifferentiableAt_gradient (hf x)) u
  change e.continuousLinearMapAt ℝ x (LC (gradient (I := I) f) x (e.symmL ℝ x u)) =
    frameConnectionCoefficients LC e (Module.finBasis ℝ E) x u
      (e.continuousLinearMapAt ℝ x (gradient (I := I) f x)) +
      fderiv ℝ (obataGradientCoordinates (I := I) f x) (extChartAt I x x) u at he
  rw [hg, map_zero, map_zero, zero_add, hc, map_smul,
    e.continuousLinearMapAt_symmL (mem_chart_source H x)] at he
  exact he.symm

omit [ContMDiffVectorBundle 1 E TM I] in
/-- The coordinate gradient is C1 whenever the Obata function is C2. -/
theorem contDiffAt_obataGradientCoordinates {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f) (x : M) :
    ContDiffAt ℝ 1 (obataGradientCoordinates (I := I) f x) (extChartAt I x x) := by
  let e := trivializationAt E TM x
  let φ := extChartAt I x
  have hx : x ∈ e.baseSet := mem_chart_source H x
  have hg := (e.contMDiffAt_section_iff (IB := I) hx).mp (contMDiffAt_gradient 1 (hf x))
  have he : ContMDiffAt I 𝓘(ℝ, E) 1
      (fun y => e.continuousLinearMapAt ℝ y (gradient (I := I) f y)) x := by
    apply hg.congr_of_eventuallyEq
    filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
    exact e.continuousLinearMapAt_apply_of_mem ℝ hy _
  have hi : ContMDiffAt 𝓘(ℝ, E) I 1 φ.symm (φ x) :=
    (contMDiffOn_extChartAt_symm x).contMDiffAt
      ((isOpen_extChartAt_target (I := I) x).mem_nhds (φ.map_source (mem_extChartAt_source x)))
  exact (he.comp_of_eq hi (φ.left_inv (mem_extChartAt_source x))).contDiffAt

/-- Invertibility of the coordinate gradient derivative isolates every
critical point with a nonzero Obata value. -/
theorem obata_critical_isolated {K : ℝ} (hK : K ≠ 0) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f) {x : M}
    (hg : gradient (I := I) f x = 0) (hfx : f x ≠ 0)
    (hH : ∀ v w : TM x, hessian LC f x v w = -K * f x * inner ℝ v w) :
    ∀ᶠ y in 𝓝 x, gradient (I := I) f y = 0 → y = x := by
  let φ := extChartAt I x
  let W := obataGradientCoordinates (I := I) f x
  have hc : -K * f x ≠ 0 := mul_ne_zero (neg_ne_zero.mpr hK) hfx
  let L : E ≃L[ℝ] E := ContinuousLinearEquiv.smulLeft (Units.mk0 (-K * f x) hc)
  have hd := (contDiffAt_obataGradientCoordinates hf x).hasStrictFDerivAt (by norm_num)
  rw [fderiv_obataGradientCoordinates hf hg hH] at hd
  have hL : (-K * f x) • (1 : E →L[ℝ] E) = (L : E →L[ℝ] E) := by
    ext u
    rfl
  rw [hL] at hd
  let F := hd.toOpenPartialHomeomorph W
  have hF : φ x ∈ F.source := hd.mem_toOpenPartialHomeomorph_source
  have hFs : F.source ∈ 𝓝 (φ x) := F.open_source.mem_nhds hF
  filter_upwards [(isOpen_extChartAt_source (I := I) x).mem_nhds (mem_extChartAt_source x),
    (continuousAt_extChartAt (I := I) x) hFs] with y hy hyF
  intro hygrad
  apply φ.injOn hy (mem_extChartAt_source x)
  apply F.injOn hyF hF
  change W (φ y) = W (φ x)
  have hyy : (extChartAt I x).symm ((extChartAt I x) y) = y := (extChartAt I x).left_inv hy
  have hxx : (extChartAt I x).symm ((extChartAt I x) x) = x :=
    (extChartAt I x).left_inv (mem_extChartAt_source x)
  dsimp only [W, obataGradientCoordinates, φ]
  rw [hyy, hxx, hygrad, hg]
  simp only [map_zero]

/-- All critical points of a nonconstant compact Obata function form a
discrete subset; nonzero critical values are proved, not assumed. -/
theorem isDiscrete_obata_critical_set [CompactSpace M] [Nonempty M] [PreconnectedSpace M]
    {K : ℝ} (hK : 0 < K) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f)
    (hnon : ∃ x y, f x ≠ f y)
    (hH : ∀ (x : M) (v w : TM x), hessian LC f x v w = -K * f x * inner ℝ v w) :
    IsDiscrete {x : M | gradient (I := I) f x = 0} := by
  obtain ⟨a, ha, hb, hcrit⟩ := obata_critical_values hK hf hnon hH
  rw [isDiscrete_iff_forall_mem_exists_isOpen]
  intro x hx
  have hfx : f x ≠ 0 := by
    rcases (hcrit x).mp hx with he | he
    · rw [he]; exact ha.ne'
    · rw [he]; exact neg_ne_zero.mpr ha.ne'
  have hi := obata_critical_isolated hK.ne' hf hx hfx (hH x)
  obtain ⟨U, hU, hUo, hxU⟩ := mem_nhds_iff.mp hi
  refine ⟨U, hUo, ?_⟩
  ext y
  constructor
  · intro hy
    exact mem_singleton_iff.mpr (hU hy.1 hy.2)
  · intro hy
    rw [mem_singleton_iff] at hy
    subst y
    exact ⟨hxU, hx⟩

/-- Compactness and the actual C1 gradient reduce the possible poles to
a finite set. This does not yet prove that exactly two remain. -/
theorem finite_obata_critical_set [CompactSpace M] [Nonempty M] [PreconnectedSpace M]
    {K : ℝ} (hK : 0 < K) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f)
    (hnon : ∃ x y, f x ≠ f y)
    (hH : ∀ (x : M) (v w : TM x), hessian LC f x v w = -K * f x * inner ℝ v w) :
    {x : M | gradient (I := I) f x = 0}.Finite := by
  have hc : IsClosed {x : M | gradient (I := I) f x = 0} := by
    simpa only [norm_eq_zero] using
      isClosed_eq (continuous_norm_gradient (hf.of_le (by norm_num : (1 : ℕ∞ω) ≤ 2)))
        (continuous_const (y := (0 : ℝ)))
  exact hc.isCompact.finite (isDiscrete_obata_critical_set hK hf hnon hH)

end LichnerowiczObata
