/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.FlatCutoff

/-!
# Jointly smooth zero extension from locally uniform Gaussian bounds

The bounds concern the actual full Fréchet derivative tensors of a function
on `U × (0,∞)`. They are uniform in a neighborhood of each parameter point.
Every tensor is extended by zero. One extra inverse power in the Gaussian
bound proves that its derivative at the edge is zero, using
`δ ≤ ‖(p,δ) - (p₀,0)‖`. No pointwise-to-joint limit inference is used.
-/

@[expose] public section


noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace NavierStokes.FlatZeroExtension

open FlatCutoff

variable {E F : Type*}

section Zero

variable [Zero F]

/-- Preserve positive edge distance and use zero on the other side. -/
def zeroExtension (f : E × ℝ → F) (p : E × ℝ) : F :=
  if 0 < p.2 then f p else 0

theorem zeroExtension_of_pos (f : E × ℝ → F) {p : E × ℝ} (hp : 0 < p.2) :
    zeroExtension f p = f p := ite_eq_left hp

theorem zeroExtension_of_nonpos (f : E × ℝ → F) {p : E × ℝ} (hp : p.2 ≤ 0) :
    zeroExtension f p = 0 := ite_eq_right (not_lt_of_ge hp)

@[simp] theorem zeroExtension_edge (f : E × ℝ → F) (x : E) :
    zeroExtension f (x, 0) = 0 := zeroExtension_of_nonpos f le_rfl

variable [TopologicalSpace E]

theorem zeroExtension_germ_pos (f : E × ℝ → F) {p : E × ℝ} (hp : 0 < p.2) :
    zeroExtension f =ᶠ[𝓝 p] f := by
  filter_upwards [continuousAt_snd.eventually (Ioi_mem_nhds hp)] with q hq
  exact zeroExtension_of_pos f hq

theorem zeroExtension_germ_neg (f : E × ℝ → F) {p : E × ℝ} (hp : p.2 < 0) :
    zeroExtension f =ᶠ[𝓝 p] (fun _ => 0) := by
  filter_upwards [continuousAt_snd.eventually (Iio_mem_nhds hp)] with q hq
  exact zeroExtension_of_nonpos f hq.le

end Zero

variable [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A locally uniform bound. The constant, inverse-power loss, and parameter
neighborhood may depend on the parameter point. The interval `(0,1)` is only
used near the edge. -/
def LocalGaussianBound (c : ℝ) (U : Set E) (g : E × ℝ → F) : Prop :=
  ∀ x ∈ U, ∃ V ∈ 𝓝 x, ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ,
    ∀ y ∈ V ∩ U, ∀ δ ∈ Ioo (0 : ℝ) 1,
      ‖g (y, δ)‖ ≤ C * edge c δ / δ ^ N

/-- Every actual tensor is bounded, with constants and losses allowed to
depend on its derivative order as well as the parameter point. -/
def LocalGaussianJets (c : ℝ) (U : Set E) (f : E × ℝ → F) : Prop :=
  ∀ n : ℕ, LocalGaussianBound c U (iteratedFDeriv ℝ n f)

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
theorem LocalGaussianBound.of_uniform {c C : ℝ} {N : ℕ} {U : Set E}
    {g : E × ℝ → F} (hC : 0 ≤ C)
    (hbound : ∀ y ∈ U, ∀ δ ∈ Ioo (0 : ℝ) 1,
      ‖g (y, δ)‖ ≤ C * edge c δ / δ ^ N) : LocalGaussianBound c U g := by
  intro _ _
  refine ⟨univ, univ_mem, C, hC, N, ?_⟩
  intro y hy δ hδ
  exact hbound y hy.2 δ hδ

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- Adapter from the unextended exponential written in analytic estimates. -/
theorem LocalGaussianBound.of_exp_bound {c : ℝ} {U : Set E} {g : E × ℝ → F}
    (hbound : ∀ x ∈ U, ∃ V ∈ 𝓝 x, ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ,
      ∀ y ∈ V ∩ U, ∀ δ ∈ Ioo (0 : ℝ) 1,
        ‖g (y, δ)‖ ≤ C * Real.exp (-c / δ ^ 2) / δ ^ N) :
    LocalGaussianBound c U g := by
  intro x hx
  obtain ⟨V, hV, C, hC, N, hb⟩ := hbound x hx
  refine ⟨V, hV, C, hC, N, ?_⟩
  intro y hy δ hδ
  rw [edge_of_pos c hδ.1]
  exact hb y hy δ hδ

theorem edge_div_pow_tendsto_zero {c : ℝ} (hc : 0 < c) (N : ℕ) :
    Tendsto (fun δ : ℝ => edge c δ / δ ^ N) (𝓝 0) (𝓝 0) := by
  simpa only [iteratedDeriv_zero] using weighted_iteratedDeriv_tendsto_zero hc 0 N

/-- A bound on values alone, uniform in the parameter, proves a zero full
derivative at the edge. This applies later to every actual tensor. -/
theorem hasFDerivAt_zeroExtension_edge {c : ℝ} (hc : 0 < c)
    {U : Set E} (hU : IsOpen U) {g : E × ℝ → F}
    (hB : LocalGaussianBound c U g) {x : E} (hx : x ∈ U) :
    HasFDerivAt (zeroExtension g) (0 : (E × ℝ) →L[ℝ] F) (x, 0) := by
  obtain ⟨V, hV, C, _, N, hbound⟩ := hB x hx
  rw [hasFDerivAt_iff_isLittleO]
  simp only [zeroExtension_edge, _root_.zero_apply, sub_zero]
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  have hlim : Tendsto (fun δ : ℝ => C * edge c δ / δ ^ (N + 1)) (𝓝 0) (𝓝 0) := by
    simpa only [mul_zero, mul_div_assoc] using
      (edge_div_pow_tendsto_zero hc (N + 1)).const_mul C
  have hδlim : Tendsto (Prod.snd : E × ℝ → ℝ) (𝓝 (x, 0)) (𝓝 0) := continuousAt_snd
  have hsmall : ∀ᶠ p : E × ℝ in 𝓝 (x, 0), C * edge c p.2 / p.2 ^ (N + 1) < ε :=
    (hlim.comp hδlim).eventually (Iio_mem_nhds hε)
  have hparam : ∀ᶠ p : E × ℝ in 𝓝 (x, 0), p.1 ∈ V ∩ U :=
    continuousAt_fst.preimage_mem_nhds (inter_mem hV (hU.mem_nhds hx))
  have hdist : ∀ᶠ p : E × ℝ in 𝓝 (x, 0), p.2 < 1 :=
    continuousAt_snd.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hsmall, hparam, hdist] with p hp hpU hp1
  by_cases hp0 : 0 < p.2
  · rw [zeroExtension_of_pos g hp0]
    have hscaled : C * edge c p.2 / p.2 ^ N ≤ ε * p.2 := by
      apply (div_le_iff₀ hp0).mp
      simpa only [div_div, pow_succ] using hp.le
    have hδ : p.2 ≤ ‖p - (x, 0)‖ := by
      calc
        p.2 = ‖(p - (x, 0)).2‖ := by simp [Real.norm_eq_abs, abs_of_pos hp0]
        _ ≤ ‖p - (x, 0)‖ := norm_snd_le _
    exact (hbound p.1 hpU p.2 ⟨hp0, hp1⟩).trans
      (hscaled.trans (mul_le_mul_of_nonneg_left hδ hε.le))
  · rw [zeroExtension_of_nonpos g (le_of_not_gt hp0), norm_zero]
    exact mul_nonneg hε.le (norm_nonneg _)

/-- Zero extension of each actual derivative tensor. -/
noncomputable def extendedJets (f : E × ℝ → F) (p : E × ℝ) :
    FormalMultilinearSeries ℝ (E × ℝ) F :=
  fun n => zeroExtension (iteratedFDeriv ℝ n f) p

theorem iteratedFDeriv_hasFDerivAt {f : E × ℝ → F} {p : E × ℝ}
    (hf : ContDiffAt ℝ ∞ f p) (n : ℕ) :
    HasFDerivAt (iteratedFDeriv ℝ n f) (iteratedFDeriv ℝ (n + 1) f p).curryLeft p := by
  have hi : ContDiffAt ℝ 1 (iteratedFDeriv ℝ n f) p :=
    hf.iteratedFDeriv_right (by exact_mod_cast (le_top : 1 + (n : ℕ∞) ≤ ⊤))
  have hd := (hi.differentiableAt (by simp)).hasFDerivAt
  rw [fderiv_iteratedFDeriv] at hd
  exact hd

/-- The derivative recurrence holds for the extended tensors on both sides
and at the edge. The edge case comes from the proved small-o bound. -/
theorem extendedJets_hasFDerivAt {c : ℝ} (hc : 0 < c)
    {U : Set E} (hU : IsOpen U) {f : E × ℝ → F}
    (hf : ContDiffOn ℝ ∞ f (U ×ˢ Ioi 0)) (hB : LocalGaussianJets c U f)
    (n : ℕ) {p : E × ℝ} (hp : p ∈ U ×ˢ (univ : Set ℝ)) :
    HasFDerivAt (fun q => extendedJets f q n) (extendedJets f p (n + 1)).curryLeft p := by
  change HasFDerivAt (zeroExtension (iteratedFDeriv ℝ n f))
    (zeroExtension (iteratedFDeriv ℝ (n + 1) f) p).curryLeft p
  rcases lt_trichotomy p.2 0 with hneg | heq | hpos
  · rw [zeroExtension_of_nonpos _ hneg.le]
    convert! (hasFDerivAt_const (0 : (E × ℝ)[×n]→L[ℝ] F) p).congr_of_eventuallyEq
      (zeroExtension_germ_neg _ hneg) using 1
  · have hp₀ : p = (p.1, 0) := Prod.ext rfl heq
    rw [hp₀, zeroExtension_edge]
    convert! hasFDerivAt_zeroExtension_edge hc hU (hB n) hp.1 using 1
  · rw [zeroExtension_of_pos _ hpos]
    have hfp := hf.contDiffAt ((hU.prod isOpen_Ioi).mem_nhds ⟨hp.1, hpos⟩)
    exact (iteratedFDeriv_hasFDerivAt hfp n).congr_of_eventuallyEq
      (zeroExtension_germ_pos _ hpos)

/-- The proved extended tensors form the actual Taylor family of the zero
extension on the open set `U × ℝ`. -/
theorem hasFTaylorSeriesUpToOn_zeroExtension {c : ℝ} (hc : 0 < c)
    {U : Set E} (hU : IsOpen U) {f : E × ℝ → F}
    (hf : ContDiffOn ℝ ∞ f (U ×ˢ Ioi 0)) (hB : LocalGaussianJets c U f) :
    HasFTaylorSeriesUpToOn ∞ (zeroExtension f) (extendedJets f) (U ×ˢ univ) := by
  constructor
  · intro p _
    by_cases hp : 0 < p.2
    · simp only [extendedJets, zeroExtension, ite_eq_left hp]
      rfl
    · simp only [extendedJets, zeroExtension, ite_eq_right hp]
      rfl
  · intro n _ p hp
    exact (extendedJets_hasFDerivAt hc hU hf hB n hp).hasFDerivWithinAt
  · intro n _ p hp
    exact (extendedJets_hasFDerivAt hc hU hf hB n hp).continuousAt.continuousWithinAt

/-- Main gluing theorem. Neither the parameter space nor the target needs a
finite-dimensionality or completeness hypothesis. -/
theorem contDiffOn_zeroExtension {c : ℝ} (hc : 0 < c)
    {U : Set E} (hU : IsOpen U) {f : E × ℝ → F}
    (hf : ContDiffOn ℝ ∞ f (U ×ˢ Ioi 0)) (hB : LocalGaussianJets c U f) :
    ContDiffOn ℝ ∞ (zeroExtension f) (U ×ˢ univ) :=
  (hasFTaylorSeriesUpToOn_zeroExtension hc hU hf hB).contDiffOn

/-- The ordinary full tensors of the extension equal the zero extensions
of the original ordinary full tensors. -/
theorem iteratedFDeriv_zeroExtension {c : ℝ} (hc : 0 < c)
    {U : Set E} (hU : IsOpen U) {f : E × ℝ → F}
    (hf : ContDiffOn ℝ ∞ f (U ×ˢ Ioi 0)) (hB : LocalGaussianJets c U f)
    (n : ℕ) {p : E × ℝ} (hp : p ∈ U ×ˢ (univ : Set ℝ)) :
    iteratedFDeriv ℝ n (zeroExtension f) p = zeroExtension (iteratedFDeriv ℝ n f) p := by
  have h := hasFTaylorSeriesUpToOn_zeroExtension hc hU hf hB
  have he := (h.eq_iteratedFDerivWithin_of_uniqueDiffOn
    (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n).le
    (hU.prod isOpen_univ).uniqueDiffOn hp).symm
  rwa [iteratedFDerivWithin_of_isOpen n (hU.prod isOpen_univ) hp] at he

theorem iteratedFDeriv_zeroExtension_nonpos {c : ℝ} (hc : 0 < c)
    {U : Set E} (hU : IsOpen U) {f : E × ℝ → F}
    (hf : ContDiffOn ℝ ∞ f (U ×ˢ Ioi 0)) (hB : LocalGaussianJets c U f)
    (n : ℕ) {p : E × ℝ} (hp : p.1 ∈ U) (hδ : p.2 ≤ 0) :
    iteratedFDeriv ℝ n (zeroExtension f) p = 0 := by
  rw [iteratedFDeriv_zeroExtension hc hU hf hB n ⟨hp, mem_univ _⟩,
    zeroExtension_of_nonpos _ hδ]

/-- In particular every mixed derivative at the joining edge is zero. -/
theorem iteratedFDeriv_zeroExtension_edge {c : ℝ} (hc : 0 < c)
    {U : Set E} (hU : IsOpen U) {f : E × ℝ → F}
    (hf : ContDiffOn ℝ ∞ f (U ×ˢ Ioi 0)) (hB : LocalGaussianJets c U f)
    (n : ℕ) {x : E} (hx : x ∈ U) :
    iteratedFDeriv ℝ n (zeroExtension f) (x, 0) = 0 :=
  iteratedFDeriv_zeroExtension_nonpos hc hU hf hB n hx le_rfl

/-- The main theorem stated directly with local exponential estimates of
every actual tensor. The interval and neighborhood bounds remain explicit. -/
theorem contDiffOn_zeroExtension_of_exp_bounds {c : ℝ} (hc : 0 < c)
    {U : Set E} (hU : IsOpen U) {f : E × ℝ → F}
    (hf : ContDiffOn ℝ ∞ f (U ×ˢ Ioi 0))
    (hbound : ∀ n : ℕ, ∀ x ∈ U, ∃ V ∈ 𝓝 x, ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ,
      ∀ y ∈ V ∩ U, ∀ δ ∈ Ioo (0 : ℝ) 1,
        ‖iteratedFDeriv ℝ n f (y, δ)‖ ≤ C * Real.exp (-c / δ ^ 2) / δ ^ N) :
    ContDiffOn ℝ ∞ (zeroExtension f) (U ×ˢ univ) :=
  contDiffOn_zeroExtension hc hU hf (fun n => LocalGaussianBound.of_exp_bound (hbound n))

theorem contDiff_zeroExtension {c : ℝ} (hc : 0 < c) {f : E × ℝ → F}
    (hf : ContDiffOn ℝ ∞ f (univ ×ˢ Ioi 0)) (hB : LocalGaussianJets c univ f) :
    ContDiff ℝ ∞ (zeroExtension f) := by
  simpa only [univ_prod_univ, contDiffOn_univ] using
    contDiffOn_zeroExtension hc isOpen_univ hf hB

end NavierStokes.FlatZeroExtension
