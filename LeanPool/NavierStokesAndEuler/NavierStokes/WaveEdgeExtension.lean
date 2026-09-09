/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.PrimaryCopyBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.PhysicalClassBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.FlatZeroExtension
public import LeanPool.NavierStokesAndEuler.NavierStokes.VariableGaugeMean

@[expose] public section

/-!
# Smooth zero extension across both moving radial edges

The raw coefficient is used only inside the annulus. Gaussian bounds on
its actual full derivative tensors prove that its literal zero extension
has all derivatives zero on both moving boundary hypersurfaces.
-/

noncomputable section

namespace NavierStokes.WaveEdgeExtension

open Set Filter Function PrimaryCopyBounds
open scoped Topology ContDiff

variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def window (ρ : D → ℝ) (a b : ℝ) : Set D :=
  {x | a < ρ x ∧ ρ x < b}

noncomputable def windowDomain (Ω : Set D) (ρ : D → ℝ) (a b : ℝ) : Set D :=
  Ω ∩ window ρ a b

noncomputable def extension (ρ : D → ℝ) (a b : ℝ) (f : D → E) (x : D) : E :=
  by classical exact if x ∈ window ρ a b then f x else 0

omit [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedSpace ℝ E] in
theorem extension_inside (ρ : D → ℝ) (a b : ℝ) (f : D → E) {x : D}
    (hx : x ∈ window ρ a b) : extension ρ a b f x = f x := by classical exact ite_eq_left hx

omit [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedSpace ℝ E] in
theorem extension_outside (ρ : D → ℝ) (a b : ℝ) (f : D → E) {x : D}
    (hx : x ∉ window ρ a b) : extension ρ a b f x = 0 := by classical exact ite_eq_right hx

omit [NormedSpace ℝ D] in
theorem windowDomain_open {Ω : Set D} (hΩ : IsOpen Ω) {ρ : D → ℝ}
    (hρ : ContinuousOn ρ Ω) (a b : ℝ) : IsOpen (windowDomain Ω ρ a b) := by
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  exact inter_mem (hΩ.mem_nhds hx.1)
    ((hρ x hx.1).continuousAt (hΩ.mem_nhds hx.1) (isOpen_Ioo.mem_nhds hx.2))

omit [NormedSpace ℝ D] [NormedSpace ℝ E] in
theorem extension_germ_inside {ρ : D → ℝ} (a b : ℝ) (f : D → E) {x : D}
    (hρ : ContinuousAt ρ x) (hx : x ∈ window ρ a b) :
    extension ρ a b f =ᶠ[𝓝 x] f := by
  filter_upwards [hρ (isOpen_Ioo.mem_nhds hx)] with y hy
  exact extension_inside ρ a b f hy

omit [NormedSpace ℝ D] [NormedSpace ℝ E] in
theorem extension_germ_left {ρ : D → ℝ} (a b : ℝ) (f : D → E) {x : D}
    (hρ : ContinuousAt ρ x) (hx : ρ x < a) :
    extension ρ a b f =ᶠ[𝓝 x] fun _ => 0 := by
  filter_upwards [hρ (Iio_mem_nhds hx)] with y hy
  exact extension_outside ρ a b f (fun hw => (not_lt_of_ge hy.le) hw.1)

omit [NormedSpace ℝ D] [NormedSpace ℝ E] in
theorem extension_germ_right {ρ : D → ℝ} (a b : ℝ) (f : D → E) {x : D}
    (hρ : ContinuousAt ρ x) (hx : b < ρ x) :
    extension ρ a b f =ᶠ[𝓝 x] fun _ => 0 := by
  filter_upwards [hρ (Ioi_mem_nhds hx)] with y hy
  exact extension_outside ρ a b f (fun hw => (not_lt_of_ge hy.le) hw.2)

/-- A local bound on actual tensors from the interior side of an edge. -/
def EdgeControl (ρ : D → ℝ) (a b : ℝ) (d : D → ℝ) (c : ℝ)
    (g : D → E) (x : D) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ᶠ y in 𝓝 x, y ∈ window ρ a b →
    0 < d y ∧ ‖g y‖ ≤ C * FlatCutoff.edge c (d y) / (d y) ^ N

/-- A smooth defining function may replace the straight edge coordinate.
Its actual derivative controls its distance by ambient distance. -/
theorem hasFDerivAt_extension_boundary {ρ d : D → ℝ} {a b c : ℝ}
    {g : D → E} {x : D} (hc : 0 < c) (hx : x ∉ window ρ a b)
    (hd : DifferentiableAt ℝ d x) (hdx : d x = 0)
    (hB : EdgeControl ρ a b d c g x) :
    HasFDerivAt (extension ρ a b g) (0 : D →L[ℝ] E) x := by
  obtain ⟨C, hC, N, hbound⟩ := hB
  obtain ⟨K, hK, hLip⟩ := hd.isBigO_sub.exists_pos
  have hdist : ∀ᶠ y in 𝓝 x, ‖d y‖ ≤ K * ‖y - x‖ := by
    simpa only [hdx, sub_zero] using hLip.bound
  rw [hasFDerivAt_iff_isLittleO]
  simp only [extension_outside ρ a b g hx, _root_.zero_apply, sub_zero]
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  have hlim : Tendsto (fun t : ℝ => C * FlatCutoff.edge c t / t ^ (N + 1))
      (𝓝 0) (𝓝 0) := by
    simpa only [mul_zero, mul_div_assoc] using
      (FlatZeroExtension.edge_div_pow_tendsto_zero hc (N + 1)).const_mul C
  have hdc : Tendsto d (𝓝 x) (𝓝 0) := by simpa only [ContinuousAt, hdx] using hd.continuousAt
  have hsmall : ∀ᶠ y in 𝓝 x, C * FlatCutoff.edge c (d y) / (d y) ^ (N + 1) < ε / K :=
    (hlim.comp hdc).eventually (Iio_mem_nhds (div_pos hε hK))
  filter_upwards [hbound, hdist, hsmall] with y hy hdy hsy
  by_cases hi : y ∈ window ρ a b
  · rw [extension_inside ρ a b g hi]
    obtain ⟨hpos, hgb⟩ := hy hi
    have hs : C * FlatCutoff.edge c (d y) / (d y) ^ N ≤ (ε / K) * d y := by
      apply (div_le_iff₀ hpos).mp
      simpa only [div_div, pow_succ] using hsy.le
    have hdle : d y ≤ K * ‖y - x‖ := by
      simpa only [Real.norm_eq_abs, abs_of_pos hpos] using hdy
    calc
      _ ≤ C * FlatCutoff.edge c (d y) / (d y) ^ N := hgb
      _ ≤ (ε / K) * d y := hs
      _ ≤ (ε / K) * (K * ‖y - x‖) := mul_le_mul_of_nonneg_left hdle (div_pos hε hK).le
      _ = ε * ‖y - x‖ := by field_simp
  · rw [extension_outside ρ a b g hi, norm_zero]
    exact mul_nonneg hε.le (norm_nonneg _)

noncomputable def logCoordinate (ρ : D → ℝ) (a : ℝ) (x : D) : ℝ :=
  WeightedRadialPrimitive.logPosition a (ρ x)

theorem logCoordinate_differentiableAt {ρ : D → ℝ} {a : ℝ} (ha : 0 < a) {x : D}
    (hρ : DifferentiableAt ℝ ρ x) (hx : 0 < ρ x) :
    DifferentiableAt ℝ (logCoordinate ρ a) x := by
  change DifferentiableAt ℝ (fun y => Real.log (ρ y / a)) x
  have hdiv : DifferentiableAt ℝ (fun y => ρ y / a) x := by
    simpa only [div_eq_mul_inv] using hρ.mul_const a⁻¹
  exact hdiv.log (div_ne_zero hx.ne' ha.ne')

def BoundaryControls (Ω : Set D) (ρ : D → ℝ) (a b cL cR : ℝ) (f : D → E) : Prop :=
  (∀ n x, x ∈ Ω → ρ x = a →
    EdgeControl ρ a b (logCoordinate ρ a) cL (iteratedFDeriv ℝ n f) x) ∧
  (∀ n x, x ∈ Ω → ρ x = b →
    EdgeControl ρ a b (fun y => WeightedRadialPrimitive.logLength a b - logCoordinate ρ a y)
      cR (iteratedFDeriv ℝ n f) x)

noncomputable def extendedJets (ρ : D → ℝ) (a b : ℝ) (f : D → E) (x : D) :
    FormalMultilinearSeries ℝ D E := fun n => extension ρ a b (iteratedFDeriv ℝ n f) x

private theorem tensor_hasFDerivAt {f : D → E} {x : D} (hf : ContDiffAt ℝ ∞ f x) (n : ℕ) :
    HasFDerivAt (iteratedFDeriv ℝ n f) (iteratedFDeriv ℝ (n + 1) f x).curryLeft x := by
  have hi : ContDiffAt ℝ 1 (iteratedFDeriv ℝ n f) x :=
    hf.iteratedFDeriv_right (by exact_mod_cast (le_top : 1 + (n : ℕ∞) ≤ ⊤))
  have hd := (hi.differentiableAt (by simp)).hasFDerivAt
  simp only [fderiv_iteratedFDeriv, Function.comp_apply] at hd
  exact hd

theorem extendedJets_hasFDerivAt {Ω : Set D} (hΩ : IsOpen Ω) {ρ : D → ℝ}
    (hρ : ContDiffOn ℝ ∞ ρ Ω) {a b cL cR : ℝ} (ha : 0 < a) (hab : a < b)
    (hcL : 0 < cL) (hcR : 0 < cR) {f : D → E}
    (hf : ContDiffOn ℝ ∞ f (windowDomain Ω ρ a b))
    (hB : BoundaryControls Ω ρ a b cL cR f)
    (n : ℕ) {x : D} (hx : x ∈ Ω) :
    HasFDerivAt (fun y => extendedJets ρ a b f y n)
      (extendedJets ρ a b f x (n + 1)).curryLeft x := by
  have hρc := (hρ.contDiffAt (hΩ.mem_nhds hx)).continuousAt
  have hρd := (hρ.contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by simp)
  change HasFDerivAt (extension ρ a b (iteratedFDeriv ℝ n f))
    (extension ρ a b (iteratedFDeriv ℝ (n + 1) f) x).curryLeft x
  have hcurry : (0 : D[×(n + 1)]→L[ℝ] E).curryLeft = 0 := by
    ext u v
    rfl
  rcases lt_trichotomy (ρ x) a with hleft | heq | hleft
  · have hn : x ∉ window ρ a b := fun h => (not_lt_of_ge hleft.le) h.1
    rw [extension_outside ρ a b _ hn, hcurry]
    simpa using (hasFDerivAt_const (0 : D[×n]→L[ℝ] E) x).congr_of_eventuallyEq
      (extension_germ_left a b _ hρc hleft)
  · have hn : x ∉ window ρ a b := by simp only [window, Set.mem_ofPred_eq, heq, lt_self_iff_false,
    false_and, not_false_eq_true]
    rw [extension_outside ρ a b _ hn, hcurry]
    have hlog := logCoordinate_differentiableAt ha hρd (by simpa only [heq] using ha)
    have hzero : logCoordinate ρ a x = 0 := by
      simp only [logCoordinate, WeightedRadialPrimitive.logPosition, heq, div_self ha.ne',
        Real.log_one]
    simpa using hasFDerivAt_extension_boundary hcL hn hlog hzero (hB.1 n x hx heq)
  · rcases lt_trichotomy (ρ x) b with hright | heq | hright
    · have hin : x ∈ window ρ a b := ⟨hleft, hright⟩
      rw [extension_inside ρ a b _ hin]
      have hd := tensor_hasFDerivAt
        (hf.contDiffAt ((windowDomain_open hΩ hρ.continuousOn a b).mem_nhds ⟨hx, hin⟩)) n
      exact hd.congr_of_eventuallyEq (extension_germ_inside a b _ hρc hin)
    · have hn : x ∉ window ρ a b := fun h => by simpa only [heq, lt_self_iff_false] using h.2
      rw [extension_outside ρ a b _ hn, hcurry]
      have hlog := logCoordinate_differentiableAt ha hρd (by simpa only [heq] using ha.trans hab)
      have hzero : WeightedRadialPrimitive.logLength a b - logCoordinate ρ a x = 0 := by
        simp only [logCoordinate, heq, WeightedRadialPrimitive.logPosition,
          WeightedRadialPrimitive.logLength, sub_self]
      simpa using hasFDerivAt_extension_boundary hcR hn ((differentiableAt_const _).sub hlog)
        hzero (hB.2 n x hx heq)
    · have hn : x ∉ window ρ a b := fun h => (not_lt_of_ge hright.le) h.2
      rw [extension_outside ρ a b _ hn, hcurry]
      simpa using (hasFDerivAt_const (0 : D[×n]→L[ℝ] E) x).congr_of_eventuallyEq
        (extension_germ_right a b _ hρc hright)

theorem hasFTaylorSeriesUpToOn_extension {Ω : Set D} (hΩ : IsOpen Ω) {ρ : D → ℝ}
    (hρ : ContDiffOn ℝ ∞ ρ Ω) {a b cL cR : ℝ} (ha : 0 < a) (hab : a < b)
    (hcL : 0 < cL) (hcR : 0 < cR) {f : D → E}
    (hf : ContDiffOn ℝ ∞ f (windowDomain Ω ρ a b))
    (hB : BoundaryControls Ω ρ a b cL cR f) :
    HasFTaylorSeriesUpToOn ∞ (extension ρ a b f) (extendedJets ρ a b f) Ω := by
  classical
  constructor
  · intro x hx
    by_cases hi : x ∈ window ρ a b
    · simp only [extendedJets, extension, ite_eq_left hi]
      rfl
    · simp only [extendedJets, extension, ite_eq_right hi]
      rfl
  · intro n _ x hx
    exact (extendedJets_hasFDerivAt hΩ hρ ha hab hcL hcR hf hB n hx).hasFDerivWithinAt
  · intro n _ x hx
    exact (extendedJets_hasFDerivAt hΩ hρ ha hab hcL hcR hf hB n hx).continuousAt.continuousWithinAt

theorem extension_contDiffOn {Ω : Set D} (hΩ : IsOpen Ω) {ρ : D → ℝ}
    (hρ : ContDiffOn ℝ ∞ ρ Ω) {a b cL cR : ℝ} (ha : 0 < a) (hab : a < b)
    (hcL : 0 < cL) (hcR : 0 < cR) {f : D → E}
    (hf : ContDiffOn ℝ ∞ f (windowDomain Ω ρ a b))
    (hB : BoundaryControls Ω ρ a b cL cR f) :
    ContDiffOn ℝ ∞ (extension ρ a b f) Ω :=
  (hasFTaylorSeriesUpToOn_extension hΩ hρ ha hab hcL hcR hf hB).contDiffOn

theorem iteratedFDeriv_extension {Ω : Set D} (hΩ : IsOpen Ω) {ρ : D → ℝ}
    (hρ : ContDiffOn ℝ ∞ ρ Ω) {a b cL cR : ℝ} (ha : 0 < a) (hab : a < b)
    (hcL : 0 < cL) (hcR : 0 < cR) {f : D → E}
    (hf : ContDiffOn ℝ ∞ f (windowDomain Ω ρ a b))
    (hB : BoundaryControls Ω ρ a b cL cR f) (n : ℕ) {x : D} (hx : x ∈ Ω) :
    iteratedFDeriv ℝ n (extension ρ a b f) x = extension ρ a b (iteratedFDeriv ℝ n f) x := by
  have h := hasFTaylorSeriesUpToOn_extension hΩ hρ ha hab hcL hcR hf hB
  have he := (h.eq_iteratedFDerivWithin_of_uniqueDiffOn
    (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n).le hΩ.uniqueDiffOn hx).symm
  rwa [iteratedFDerivWithin_of_isOpen n hΩ hx] at he

theorem iteratedFDeriv_extension_edge {Ω : Set D} (hΩ : IsOpen Ω) {ρ : D → ℝ}
    (hρ : ContDiffOn ℝ ∞ ρ Ω) {a b cL cR : ℝ} (ha : 0 < a) (hab : a < b)
    (hcL : 0 < cL) (hcR : 0 < cR) {f : D → E}
    (hf : ContDiffOn ℝ ∞ f (windowDomain Ω ρ a b))
    (hB : BoundaryControls Ω ρ a b cL cR f) (n : ℕ) {x : D} (hx : x ∈ Ω)
    (hedge : ρ x = a ∨ ρ x = b) :
    iteratedFDeriv ℝ n (extension ρ a b f) x = 0 := by
  rw [iteratedFDeriv_extension hΩ hρ ha hab hcL hcR hf hB n hx]
  apply extension_outside
  rcases hedge with hl | hr
  · intro h; exact (not_lt_of_ge hl.le) h.1
  · intro h; exact (not_lt_of_ge hr.ge) h.2

/-! ## Explicit two-edge Gaussian bounds -/

theorem sqrt_zeta {L t : ℝ} (ht : t ∈ Ioo 0 L) (cL cR : ℝ) :
    Real.sqrt (WeightedRadialPrimitive.zeta cL cR L t) =
      WeightedRadialPrimitive.zeta (cL / 2) (cR / 2) L t := by
  rw [Real.sqrt_eq_rpow, PhysicalClassBounds.zeta_rpow ht]
  congr 1 <;> ring

theorem half_weight_left {cL cR L t : ℝ} (hcR : 0 ≤ cR) (ht : 0 < t)
    (ht1 : t ≤ 1) (htL : t ≤ L / 2) (m : ℕ) :
    (max 1 (WeightedRadialPrimitive.delta L t)⁻¹) ^ m *
        Real.sqrt (WeightedRadialPrimitive.zeta cL cR L t) ≤
      FlatCutoff.edge (cL / 2) t / t ^ m := by
  have hinside : t ∈ Ioo 0 L := ⟨ht, by linarith⟩
  have hδ : WeightedRadialPrimitive.delta L t = t := by
    rw [WeightedRadialPrimitive.delta_left_half htL, min_eq_right ht1]
  have hi : 1 ≤ t⁻¹ := (one_le_inv₀ ht).mpr ht1
  rw [hδ, max_eq_right hi, sqrt_zeta hinside]
  have he : WeightedRadialPrimitive.zeta (cL / 2) (cR / 2) L t ≤ FlatCutoff.edge (cL / 2) t :=
    mul_le_of_le_one_right (FlatCutoff.edge_nonneg _ _)
      (WeightedRadialPrimitive.edge_le_one (div_nonneg hcR (by norm_num)) _)
  calc
    _ ≤ (t⁻¹) ^ m * FlatCutoff.edge (cL / 2) t :=
      mul_le_mul_of_nonneg_left he (pow_nonneg (inv_nonneg.mpr ht.le) _)
    _ = _ := by simp only [inv_pow, div_eq_mul_inv, mul_comm]

theorem half_weight_right {cL cR L t : ℝ} (hcL : 0 ≤ cL) (ht : t < L)
    (ht1 : L - t ≤ 1) (htL : L / 2 ≤ t) (m : ℕ) :
    (max 1 (WeightedRadialPrimitive.delta L t)⁻¹) ^ m *
        Real.sqrt (WeightedRadialPrimitive.zeta cL cR L t) ≤
      FlatCutoff.edge (cR / 2) (L - t) / (L - t) ^ m := by
  have h := half_weight_left (cL := cR) (cR := cL) hcL (sub_pos.mpr ht) ht1
    (show L - t ≤ L / 2 by linarith) m
  simpa only [WeightedRadialPrimitive.delta, WeightedRadialPrimitive.zeta,
    sub_sub_cancel, min_comm (L - t) t, mul_comm] using h

noncomputable def flatWeight (ρ : D → ℝ) (a b cL cR : ℝ) (x : D) : ℝ :=
  WeightedRadialPrimitive.zeta cL cR (WeightedRadialPrimitive.logLength a b) (logCoordinate ρ a x)

noncomputable def edgeGrowth (ρ : D → ℝ) (a b : ℝ) (x : D) : ℝ :=
  max 1 (WeightedRadialPrimitive.delta (WeightedRadialPrimitive.logLength a b) (logCoordinate ρ a
    x))⁻¹

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem edgeGrowth_one_le (ρ : D → ℝ) (a b : ℝ) (x : D) : 1 ≤ edgeGrowth ρ a b x :=
  le_max_left _ _

omit [NormedSpace ℝ D] [NormedSpace ℝ E] in
private theorem edgeControl_of_factor {ρ d H P : D → ℝ} {a b c C : ℝ}
    {g : D → E} {x : D} {N : ℕ} (hC : 0 ≤ C) (hP : ContinuousAt P x)
    (hH : ∀ y, 0 ≤ H y)
    (hb : ∀ᶠ y in 𝓝 x, y ∈ window ρ a b → ‖g y‖ ≤ C * H y * P y)
    (hh : ∀ᶠ y in 𝓝 x, y ∈ window ρ a b →
      0 < d y ∧ H y ≤ FlatCutoff.edge c (d y) / (d y) ^ N) :
    EdgeControl ρ a b d c g x := by
  let M := |P x| + 1
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hPM : P x < M := by dsimp [M]; linarith [le_abs_self (P x)]
  have hp' : ∀ᶠ y in 𝓝 x, P y < M := hP.eventually (Iio_mem_nhds hPM)
  have hp : ∀ᶠ y in 𝓝 x, P y ≤ M := hp'.mono (fun _ hy => hy.le)
  refine ⟨C * M, mul_nonneg hC hM, N, ?_⟩
  filter_upwards [hb, hh, hp] with y hby hhy hpy
  intro hi
  refine ⟨(hhy hi).1, ?_⟩
  calc
    _ ≤ C * H y * P y := hby hi
    _ ≤ C * H y * M := mul_le_mul_of_nonneg_left hpy (mul_nonneg hC (hH y))
    _ = (C * M) * H y := by ring
    _ ≤ (C * M) * (FlatCutoff.edge c (d y) / (d y) ^ N) :=
      mul_le_mul_of_nonneg_left (hhy hi).2 (mul_nonneg hC hM)
    _ = _ := by rw [mul_div_assoc]

/-- The actual square-root two-edge weight supplies both boundary controls.
The envelope only needs to be continuous near the boundary, where its local
bound is absorbed into the constant. -/
theorem boundaryControls_of_majorants {Ω : Set D} (hΩ : IsOpen Ω) {ρ P : D → ℝ}
    (hρ : ContDiffOn ℝ ∞ ρ Ω) (hP : ContinuousOn P Ω)
    {a b cL cR : ℝ} (ha : 0 < a) (hab : a < b) (hcL : 0 < cL) (hcR : 0 < cR)
    {f : D → E}
    (hb : ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ y ∈ windowDomain Ω ρ a b,
      ‖iteratedFDeriv ℝ m f y‖ ≤ C * edgeGrowth ρ a b y ^ N *
        Real.sqrt (flatWeight ρ a b cL cR y) * P y) :
    BoundaryControls Ω ρ a b (cL / 2) (cR / 2) f := by
  have hL := WeightedRadialPrimitive.logLength_pos ha hab
  constructor
  · intro m x hx hxa
    obtain ⟨C, hC, N, hbound⟩ := hb m
    have hd := logCoordinate_differentiableAt ha
      ((hρ.contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by simp)) (by simpa only [hxa] using ha)
    have hzero : logCoordinate ρ a x = 0 := by
      simp only [logCoordinate, WeightedRadialPrimitive.logPosition, hxa, div_self ha.ne',
        Real.log_one]
    apply edgeControl_of_factor (H := fun y => edgeGrowth ρ a b y ^ N *
      Real.sqrt (flatWeight ρ a b cL cR y)) hC ((hP x hx).continuousAt (hΩ.mem_nhds hx))
    · intro y
      exact mul_nonneg (pow_nonneg (zero_le_one.trans (edgeGrowth_one_le ρ a b y)) _)
        (Real.sqrt_nonneg _)
    · filter_upwards [hΩ.mem_nhds hx] with y hy
      intro hi
      simpa only [mul_assoc] using hbound y ⟨hy, hi⟩
    · have hsmall : ∀ᶠ y in 𝓝 x, logCoordinate ρ a y < 1 ∧
          logCoordinate ρ a y < WeightedRadialPrimitive.logLength a b / 2 :=
        (hd.continuousAt.eventually (Iio_mem_nhds (by simpa only [hzero] using zero_lt_one))).and
          (hd.continuousAt.eventually (Iio_mem_nhds (by simpa only [hzero] using half_pos hL)))
      filter_upwards [hsmall] with y hy
      intro hi
      have ht := WeightedRadialPrimitive.logPosition_mem ha hi
      refine ⟨ht.1, ?_⟩
      exact half_weight_left hcR.le ht.1 hy.1.le hy.2.le N
  · intro m x hx hxb
    obtain ⟨C, hC, N, hbound⟩ := hb m
    have hd := logCoordinate_differentiableAt ha
      ((hρ.contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by simp)) (by simpa only [hxb] using
        ha.trans hab)
    have hd' := (differentiableAt_const (WeightedRadialPrimitive.logLength a b)).fun_sub hd
    have hzero : WeightedRadialPrimitive.logLength a b - logCoordinate ρ a x = 0 := by
      simp only [logCoordinate, hxb, WeightedRadialPrimitive.logPosition,
        WeightedRadialPrimitive.logLength, sub_self]
    apply edgeControl_of_factor (H := fun y => edgeGrowth ρ a b y ^ N *
      Real.sqrt (flatWeight ρ a b cL cR y)) hC ((hP x hx).continuousAt (hΩ.mem_nhds hx))
    · intro y
      exact mul_nonneg (pow_nonneg (zero_le_one.trans (edgeGrowth_one_le ρ a b y)) _)
        (Real.sqrt_nonneg _)
    · filter_upwards [hΩ.mem_nhds hx] with y hy
      intro hi
      simpa only [mul_assoc] using hbound y ⟨hy, hi⟩
    · have hsmall : ∀ᶠ y in 𝓝 x, WeightedRadialPrimitive.logLength a b - logCoordinate ρ a y < 1 ∧
          WeightedRadialPrimitive.logLength a b - logCoordinate ρ a y <
            WeightedRadialPrimitive.logLength a b / 2 :=
        (hd'.continuousAt.eventually (Iio_mem_nhds (by simpa only [hzero] using zero_lt_one))).and
          (hd'.continuousAt.eventually (Iio_mem_nhds (by simpa only [hzero] using half_pos hL)))
      filter_upwards [hsmall] with y hy
      intro hi
      have ht := WeightedRadialPrimitive.logPosition_mem ha hi
      refine ⟨sub_pos.mpr ht.2, ?_⟩
      exact half_weight_right hcL.le ht.2 hy.1.le (by
        change WeightedRadialPrimitive.logLength a b / 2 ≤ logCoordinate ρ a y
        linarith [hy.2]) N

section NativeBounds

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {ι : Type*}

/-- Reduce the actual native class estimate without differentiating the
weight or discarding any of its flat-edge factor. -/
theorem native_jet_majorant {V : JetDomain ι X} {Ω : Set X} {ρ : X → ℝ}
    {a b cL cR : ℝ} {A S : ι → ℝ} {P : ι → X → ℝ} {f : ι → X → E}
    (hf : NativeJets V (fun i x => A i * Real.sqrt (flatWeight ρ a b cL cR x) * P i x) f)
    (hA : ∀ i, 0 ≤ A i) (hS : ∀ i, 1 ≤ S i)
    (hP : ∀ i x, x ∈ Ω → 0 ≤ P i x)
    (hdom : ∀ i, windowDomain Ω ρ a b ⊆ V.carrier i)
    (q : ℕ) (hG : ∀ i x, x ∈ windowDomain Ω ρ a b →
      V.growth i x ≤ S i * edgeGrowth ρ a b x ^ q)
    (i : ι) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ x ∈ windowDomain Ω ρ a b,
      ‖iteratedFDeriv ℝ m (f i) x‖ ≤
        C * edgeGrowth ρ a b x ^ N * Real.sqrt (flatWeight ρ a b cL cR x) * P i x := by
  obtain ⟨C, hC, p, hb⟩ := hf.bound m
  refine ⟨C * S i ^ p * A i, by have := hA i; have := hS i; positivity, q * p, ?_⟩
  intro x hx
  have hw : 0 ≤ A i * Real.sqrt (flatWeight ρ a b cL cR x) * P i x :=
    mul_nonneg (mul_nonneg (hA i) (Real.sqrt_nonneg _)) (hP i x hx.1)
  calc
    _ ≤ C * V.growth i x ^ p * (A i * Real.sqrt (flatWeight ρ a b cL cR x) * P i x) :=
      hb i x (hdom i hx) m le_rfl
    _ ≤ C * (S i * edgeGrowth ρ a b x ^ q) ^ p *
        (A i * Real.sqrt (flatWeight ρ a b cL cR x) * P i x) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (zero_le_one.trans (V.one_le_growth i (hdom i hx))) (hG i x hx) p)
        (zero_le_one.trans hC)) hw
    _ = _ := by rw [mul_pow, ← pow_mul]; ring

/-- Smooth zero extension of an actual native coefficient. No smoothness
of the raw coefficient is assumed outside the open moving annulus. -/
theorem NativeJets.moving_zero_extension {V : JetDomain ι X} {Ω : Set X}
    (hΩ : IsOpen Ω) {ρ : X → ℝ} (hρ : ContDiffOn ℝ ∞ ρ Ω)
    {a b cL cR : ℝ} (ha : 0 < a) (hab : a < b) (hcL : 0 < cL) (hcR : 0 < cR)
    {A S : ι → ℝ} {P : ι → X → ℝ} {f : ι → X → E}
    (hf : NativeJets V (fun i x => A i * Real.sqrt (flatWeight ρ a b cL cR x) * P i x) f)
    (hA : ∀ i, 0 ≤ A i) (hS : ∀ i, 1 ≤ S i)
    (hP : ∀ i, ContinuousOn (P i) Ω) (hP0 : ∀ i x, x ∈ Ω → 0 ≤ P i x)
    (hdom : ∀ i, windowDomain Ω ρ a b ⊆ V.carrier i)
    (q : ℕ) (hG : ∀ i x, x ∈ windowDomain Ω ρ a b →
      V.growth i x ≤ S i * edgeGrowth ρ a b x ^ q) :
    ∀ i, ContDiffOn ℝ ∞ (extension ρ a b (f i)) Ω ∧
      (∀ n x, x ∈ Ω → iteratedFDeriv ℝ n (extension ρ a b (f i)) x =
        extension ρ a b (iteratedFDeriv ℝ n (f i)) x) ∧
      (∀ n x, x ∈ Ω → (ρ x = a ∨ ρ x = b) →
        iteratedFDeriv ℝ n (extension ρ a b (f i)) x = 0) := by
  intro i
  have hB := boundaryControls_of_majorants hΩ hρ (hP i) ha hab hcL hcR
    (native_jet_majorant hf hA hS hP0 hdom q hG i)
  have hs := (hf.smooth i).mono (hdom i)
  exact ⟨extension_contDiffOn hΩ hρ ha hab (half_pos hcL) (half_pos hcR) hs hB,
    fun n x hx => iteratedFDeriv_extension hΩ hρ ha hab (half_pos hcL) (half_pos hcR) hs hB n hx,
    fun n x hx he => iteratedFDeriv_extension_edge hΩ hρ ha hab (half_pos hcL) (half_pos hcR) hs hB
      n hx he⟩

end NativeBounds

/-! ## The actual moving radial profile in native coordinates -/

abbrev NativePoint := PhaseCalculus.Slow × TorusInverse.Plane

noncomputable def nativeSlowDomain : Set NativePoint := {x | 0 < x.1.2.2}

noncomputable def nativeRadius (h : ℝ) (x : NativePoint) : ℝ :=
  PrimaryTargetBounds.profileRadius h x.1

theorem nativeSlowDomain_open : IsOpen nativeSlowDomain :=
  isOpen_lt continuous_const continuous_fst.snd.snd

theorem nativeRadius_eq_qLength (h : ℝ) (x : NativePoint) :
    nativeRadius h x = x.1.1 / VariableGaugeMean.qLength (2 * h) (x.1.2.2, x.1.2.1) := by
  unfold nativeRadius PrimaryTargetBounds.profileRadius
  rw [BaseChartJets.normalizedCoordinates_eq]
  rfl

theorem nativeRadius_smooth {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2) :
    ContDiffOn ℝ ∞ (nativeRadius h) nativeSlowDomain := by
  intro x hx
  have hq := BaseChartJets.normalizedCoordinates_q_pos hh hh1 hx
  have hc := (BaseChartJets.normalizedCoordinates_smoothAt hh hh1 hx).comp x contDiffAt_fst
  exact (contDiffAt_fst.fst.div (hc.fst.sqrt hq.ne') (Real.sqrt_pos.mpr hq).ne').contDiffWithinAt

noncomputable def nativeExtension {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)
    (f : NativePoint → E) : NativePoint → E :=
  extension (nativeRadius F.data.h) (PrimaryTargetBounds.leftRadius W)
    (PrimaryTargetBounds.rightRadius W) f

theorem native_flatWeight {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F) (x :
  NativePoint) :
    flatWeight (nativeRadius F.data.h) (PrimaryTargetBounds.leftRadius W)
      (PrimaryTargetBounds.rightRadius W)
      (FinalSlowBase.edgeExponent W / 4) 1 x = PrimaryTargetBounds.movingWeight W x.1 := rfl

omit [NormedSpace ℝ E] in
theorem nativeExtension_inside {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)
    (f : NativePoint → E) {x : NativePoint}
    (hx : nativeRadius F.data.h x ∈ Ioo (PrimaryTargetBounds.leftRadius W)
      (PrimaryTargetBounds.rightRadius W)) :
    nativeExtension W f x = f x := extension_inside _ _ _ _ hx

omit [NormedSpace ℝ E] in
theorem nativeExtension_outside {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)
    (f : NativePoint → E) {x : NativePoint}
    (hx : nativeRadius F.data.h x ∉ Ioo (PrimaryTargetBounds.leftRadius W)
      (PrimaryTargetBounds.rightRadius W)) :
    nativeExtension W f x = 0 := extension_outside _ _ _ _ hx

omit [NormedSpace ℝ E] in
/-- The literal extension is zero on all nonpositive physical radii. -/
theorem nativeExtension_nonpositive {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)
    (f : NativePoint → E) {x : NativePoint} (hR : x.1.1 ≤ 0) : nativeExtension W f x = 0 := by
  apply nativeExtension_outside W f
  intro hx
  have hnonpos : nativeRadius F.data.h x ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg hR (Real.sqrt_nonneg _)
  exact (not_lt_of_ge hnonpos) ((PrimaryTargetBounds.leftRadius_pos W).trans hx.1)

/-- Direct adapter for the exact moving weight used by the primary and
signed constructions, in the native `(R,Z,T,u,v)` variable ordering. -/
theorem NativeJets.native_zero_extension {F : OutgoingProfile.Profile} (W : NominalProfile.Witness
  F)
    {ι : Type*} {V : JetDomain ι NativePoint} {A S : ι → ℝ}
    {P : ι → NativePoint → ℝ} {f : ι → NativePoint → E}
    (hf : NativeJets V (fun i x => A i * Real.sqrt (PrimaryTargetBounds.movingWeight W x.1) * P i
      x) f)
    (hA : ∀ i, 0 ≤ A i) (hS : ∀ i, 1 ≤ S i)
    (hP : ∀ i, ContinuousOn (P i) nativeSlowDomain)
    (hP0 : ∀ i x, x ∈ nativeSlowDomain → 0 ≤ P i x)
    (hdom : ∀ i, windowDomain nativeSlowDomain (nativeRadius F.data.h)
      (PrimaryTargetBounds.leftRadius W) (PrimaryTargetBounds.rightRadius W) ⊆ V.carrier i)
    (q : ℕ) (hG : ∀ i x, x ∈ windowDomain nativeSlowDomain (nativeRadius F.data.h)
      (PrimaryTargetBounds.leftRadius W) (PrimaryTargetBounds.rightRadius W) →
      V.growth i x ≤ S i * edgeGrowth (nativeRadius F.data.h)
        (PrimaryTargetBounds.leftRadius W) (PrimaryTargetBounds.rightRadius W) x ^ q) :
    ∀ i, ContDiffOn ℝ ∞ (nativeExtension W (f i)) nativeSlowDomain ∧
      (∀ n x, x ∈ nativeSlowDomain → iteratedFDeriv ℝ n (nativeExtension W (f i)) x =
        nativeExtension W (iteratedFDeriv ℝ n (f i)) x) ∧
      (∀ n x, x ∈ nativeSlowDomain →
        (nativeRadius F.data.h x = PrimaryTargetBounds.leftRadius W ∨
          nativeRadius F.data.h x = PrimaryTargetBounds.rightRadius W) →
        iteratedFDeriv ℝ n (nativeExtension W (f i)) x = 0) := by
  have hclass : NativeJets V (fun i x => A i * Real.sqrt (flatWeight (nativeRadius F.data.h)
      (PrimaryTargetBounds.leftRadius W) (PrimaryTargetBounds.rightRadius W)
      (FinalSlowBase.edgeExponent W / 4) 1 x) * P i x) f := hf
  exact NativeJets.moving_zero_extension nativeSlowDomain_open (nativeRadius_smooth F.data.h_pos
    F.data.h_lt_half)
    (PrimaryTargetBounds.leftRadius_pos W) (PrimaryTargetBounds.radii_ordered W)
    (div_pos (FinalSlowBase.edgeExponent_pos W) (by norm_num)) (by norm_num)
    hclass hA hS hP hP0 hdom q hG

/-! ## Exact comparison with the inner-coordinate edge distance -/

theorem inner_edgeDistance_eq {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)
    {r : ℝ} (hr : 0 < r) (η : ℝ) :
    FinalSlowBase.edgeDistance W (r ^ 2 / 2, η) =
      min 1 (min (2 * WeightedRadialPrimitive.logPosition (PrimaryTargetBounds.leftRadius W) r)
        (2 * (WeightedRadialPrimitive.logLength (PrimaryTargetBounds.leftRadius W)
          (PrimaryTargetBounds.rightRadius W) -
            WeightedRadialPrimitive.logPosition (PrimaryTargetBounds.leftRadius W) r))) := by
  have ha := PrimaryTargetBounds.leftRadius_pos W
  have hb := PrimaryTargetBounds.rightRadius_pos W
  have hasq : (PrimaryTargetBounds.leftRadius W) ^ 2 / 2 = NominalConeAssembly.activeLeft W := by
    rw [PrimaryTargetBounds.leftRadius,
      Real.sq_sqrt (mul_nonneg (by norm_num) (NominalConeAssembly.activeLeft_pos W).le)]
    ring
  have hbsq : (PrimaryTargetBounds.rightRadius W) ^ 2 / 2 = NominalConeAssembly.activeRight W := by
    rw [PrimaryTargetBounds.rightRadius,
      Real.sq_sqrt (mul_nonneg (by norm_num) (LeadingStressWeights.activeRight_pos W).le)]
    ring
  have halog := PrimaryTargetBounds.log_square_half ha
  have hblog := PrimaryTargetBounds.log_square_half hb
  rw [hasq] at halog
  rw [hbsq] at hblog
  have hl : Real.log (r ^ 2 / 2) - FinalSlowBase.logLeft W =
      2 * WeightedRadialPrimitive.logPosition (PrimaryTargetBounds.leftRadius W) r := by
    rw [FinalSlowBase.logLeft, WeightedRadialPrimitive.logPosition,
      Real.log_div hr.ne' ha.ne', PrimaryTargetBounds.log_square_half hr, halog]
    ring
  have hh : FinalSlowBase.logRight W - Real.log (r ^ 2 / 2) =
      2 * (WeightedRadialPrimitive.logLength (PrimaryTargetBounds.leftRadius W)
        (PrimaryTargetBounds.rightRadius W) -
          WeightedRadialPrimitive.logPosition (PrimaryTargetBounds.leftRadius W) r) := by
    rw [FinalSlowBase.logRight, WeightedRadialPrimitive.logLength,
      WeightedRadialPrimitive.logPosition, Real.log_div hb.ne' ha.ne',
      Real.log_div hr.ne' ha.ne', PrimaryTargetBounds.log_square_half hr, hblog]
    ring
  change min 1 (min (Real.log (r ^ 2 / 2) - FinalSlowBase.logLeft W)
    (FinalSlowBase.logRight W - Real.log (r ^ 2 / 2))) = _
  rw [hl, hh]

/-- The inverse edge factor in the actual inner-coordinate estimates is
bounded by the radial logarithmic factor, with constant exactly one. -/
theorem inner_edgeGrowth_le_native {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)
    {x : NativePoint} (hT : x ∈ nativeSlowDomain)
    (hx : nativeRadius F.data.h x ∈ Ioo (PrimaryTargetBounds.leftRadius W)
      (PrimaryTargetBounds.rightRadius W)) :
    max 1 (FinalSlowBase.edgeDistance W
      (BaseChartJets.normalizedCoordinates F.data.h x.1).2)⁻¹ ≤
        edgeGrowth (nativeRadius F.data.h) (PrimaryTargetBounds.leftRadius W)
          (PrimaryTargetBounds.rightRadius W) x := by
  have hr : 0 < nativeRadius F.data.h x := (PrimaryTargetBounds.leftRadius_pos W).trans hx.1
  have hpair : (BaseChartJets.normalizedCoordinates F.data.h x.1).2 =
      ((nativeRadius F.data.h x) ^ 2 / 2,
        (BaseChartJets.normalizedCoordinates F.data.h x.1).2.2) :=
    Prod.ext (PrimaryTargetBounds.profileRadius_sq hT).symm rfl
  rw [hpair, inner_edgeDistance_eq W hr]
  have ht := WeightedRadialPrimitive.logPosition_mem (PrimaryTargetBounds.leftRadius_pos W) hx
  have hd := WeightedRadialPrimitive.delta_pos ht
  have hcomp : WeightedRadialPrimitive.delta
      (WeightedRadialPrimitive.logLength (PrimaryTargetBounds.leftRadius W)
        (PrimaryTargetBounds.rightRadius W))
      (WeightedRadialPrimitive.logPosition (PrimaryTargetBounds.leftRadius W) (nativeRadius
        F.data.h x)) ≤
      min 1 (min
        (2 * WeightedRadialPrimitive.logPosition (PrimaryTargetBounds.leftRadius W) (nativeRadius
          F.data.h x))
        (2 * (WeightedRadialPrimitive.logLength (PrimaryTargetBounds.leftRadius W)
          (PrimaryTargetBounds.rightRadius W) -
          WeightedRadialPrimitive.logPosition (PrimaryTargetBounds.leftRadius W) (nativeRadius
            F.data.h x)))) := by
    apply min_le_min le_rfl
    apply min_le_min <;> linarith [ht.1, ht.2]
  apply max_le_max le_rfl
  simpa only [one_div, logCoordinate] using one_div_le_one_div_of_le hd hcomp

/-- Regularity of the literal native extension, including its exact
full-tensor values at both moving edges. -/
structure NativeRegularity {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)
    (f : NativePoint → E) : Prop where
  smooth : ContDiffOn ℝ ∞ (nativeExtension W f) nativeSlowDomain
  jets : ∀ n x, x ∈ nativeSlowDomain →
    iteratedFDeriv ℝ n (nativeExtension W f) x = nativeExtension W (iteratedFDeriv ℝ n f) x
  edge : ∀ n x, x ∈ nativeSlowDomain →
    (nativeRadius F.data.h x = PrimaryTargetBounds.leftRadius W ∨
      nativeRadius F.data.h x = PrimaryTargetBounds.rightRadius W) →
    iteratedFDeriv ℝ n (nativeExtension W f) x = 0

theorem NativeRegularity.jet_inside {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
    {f : NativePoint → E} (h : NativeRegularity W f) (n : ℕ) {x : NativePoint}
    (hx : x ∈ nativeSlowDomain)
    (hi : nativeRadius F.data.h x ∈ Ioo (PrimaryTargetBounds.leftRadius W)
      (PrimaryTargetBounds.rightRadius W)) :
    iteratedFDeriv ℝ n (nativeExtension W f) x = iteratedFDeriv ℝ n f x := by
  rw [h.jets n x hx, nativeExtension_inside W _ hi]

theorem NativeRegularity.jet_outside {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
    {f : NativePoint → E} (h : NativeRegularity W f) (n : ℕ) {x : NativePoint}
    (hx : x ∈ nativeSlowDomain)
    (hi : nativeRadius F.data.h x ∉ Ioo (PrimaryTargetBounds.leftRadius W)
      (PrimaryTargetBounds.rightRadius W)) :
    iteratedFDeriv ℝ n (nativeExtension W f) x = 0 := by
  rw [h.jets n x hx, nativeExtension_outside W _ hi]

theorem NativeJets.native_regular_of_inner_growth {F : OutgoingProfile.Profile} (W :
  NominalProfile.Witness F)
    {ι : Type*} {V : JetDomain ι NativePoint} {A S : ι → ℝ}
    {P : ι → NativePoint → ℝ} {f : ι → NativePoint → E}
    (hf : NativeJets V (fun i x => A i * Real.sqrt (PrimaryTargetBounds.movingWeight W x.1) * P i
      x) f)
    (hA : ∀ i, 0 ≤ A i) (hS : ∀ i, 1 ≤ S i)
    (hP : ∀ i, ContinuousOn (P i) nativeSlowDomain)
    (hP0 : ∀ i x, x ∈ nativeSlowDomain → 0 ≤ P i x)
    (hdom : ∀ i, windowDomain nativeSlowDomain (nativeRadius F.data.h)
      (PrimaryTargetBounds.leftRadius W) (PrimaryTargetBounds.rightRadius W) ⊆ V.carrier i)
    (q : ℕ) (hG : ∀ i x, x ∈ windowDomain nativeSlowDomain (nativeRadius F.data.h)
      (PrimaryTargetBounds.leftRadius W) (PrimaryTargetBounds.rightRadius W) →
      V.growth i x ≤ S i * (max 1 (FinalSlowBase.edgeDistance W
        (BaseChartJets.normalizedCoordinates F.data.h x.1).2)⁻¹) ^ q) :
    ∀ i, NativeRegularity W (f i) := by
  have hG' : ∀ i x, x ∈ windowDomain nativeSlowDomain (nativeRadius F.data.h)
      (PrimaryTargetBounds.leftRadius W) (PrimaryTargetBounds.rightRadius W) →
      V.growth i x ≤ S i * edgeGrowth (nativeRadius F.data.h)
        (PrimaryTargetBounds.leftRadius W) (PrimaryTargetBounds.rightRadius W) x ^ q := by
    intro i x hx
    exact (hG i x hx).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (zero_le_one.trans (le_max_left _ _))
        (inner_edgeGrowth_le_native W hx.1 hx.2) q) (zero_le_one.trans (hS i)))
  intro i
  obtain ⟨hs, hj, he⟩ := NativeJets.native_zero_extension W hf hA hS hP hP0 hdom q hG' i
  exact ⟨hs, hj, he⟩

/-! ## The constructed primary pulse and its actual envelope -/

theorem pulseEnvelope_continuousOn {ι : Type*} {U : PhaseJetBounds.Domain ι PhaseCalculus.Slow}
    (F : Fin 2 → PrimaryPulseBounds.PhaseConstruction U)
    (χ : ι → NativePoint → PhaseCalculus.Slow × ℝ)
    (hχ : ∀ i, ContinuousOn (fun x => (χ i x).2) nativeSlowDomain) (j : Fin 2) (i : ι) :
    ContinuousOn (pulseEnvelope F χ j i) nativeSlowDomain := by
  have hc : Continuous (PrimaryPulseBounds.referenceP ((F j).lam i) ((F j).u i) ((F j).L i)) :=
    continuous_iff_continuousAt.mpr (fun t => (PrimaryPulseBounds.referenceP_hasDerivAt _ _ _
      t).continuousAt)
  exact hc.comp_continuousOn (continuousOn_const.mul (hχ i))

theorem pulseEnvelope_nonneg {ι : Type*} {U : PhaseJetBounds.Domain ι PhaseCalculus.Slow}
    (F : Fin 2 → PrimaryPulseBounds.PhaseConstruction U)
    (χ : ι → NativePoint → PhaseCalculus.Slow × ℝ) (j : Fin 2) (i : ι) (x : NativePoint) :
    0 ≤ pulseEnvelope F χ j i x := (PrimaryPulseBounds.referenceP_pos _ _ _ _).le

/-- Apply the extension construction directly to the actual Cramer-scaled
homogeneous pulse. The only raw regularity premise is its already-derived
native interior jet estimate. -/
theorem primaryVelocity_native_regular {F₀ : OutgoingProfile.Profile} (W : NominalProfile.Witness
  F₀)
    {ι : Type*} {U : PhaseJetBounds.Domain ι PhaseCalculus.Slow}
    (F : Fin 2 → PrimaryPulseBounds.PhaseConstruction U)
    (pref : Fin 2 → ι → ℝ) (χ : ι → NativePoint → PhaseCalculus.Slow × ℝ)
    (ε : ι → ℝ) (T : ι → NativePoint → SmoothCovariance.Vec2) (mask : ι → NativePoint → ℝ)
    {V : JetDomain ι NativePoint} (j : Fin 2)
    (hf : NativeJets V (fun i x => Real.sqrt (ε i) *
      (Real.sqrt (PrimaryTargetBounds.movingWeight W x.1) * pulseEnvelope F χ j i x))
      (primaryVelocity F pref χ ε T mask j))
    {S : ι → ℝ} (hS : ∀ i, 1 ≤ S i)
    (hχ : ∀ i, ContinuousOn (fun x => (χ i x).2) nativeSlowDomain)
    (hdom : ∀ i, windowDomain nativeSlowDomain (nativeRadius F₀.data.h)
      (PrimaryTargetBounds.leftRadius W) (PrimaryTargetBounds.rightRadius W) ⊆ V.carrier i)
    (q : ℕ) (hG : ∀ i x, x ∈ windowDomain nativeSlowDomain (nativeRadius F₀.data.h)
      (PrimaryTargetBounds.leftRadius W) (PrimaryTargetBounds.rightRadius W) →
      V.growth i x ≤ S i * (max 1 (FinalSlowBase.edgeDistance W
        (BaseChartJets.normalizedCoordinates F₀.data.h x.1).2)⁻¹) ^ q) :
    ∀ i, NativeRegularity W (primaryVelocity F pref χ ε T mask j i) := by
  apply NativeJets.native_regular_of_inner_growth W (by simpa only [mul_assoc] using hf)
    (fun i => Real.sqrt_nonneg (ε i)) hS
    (pulseEnvelope_continuousOn F χ hχ j) (fun i x _ => pulseEnvelope_nonneg F χ j i x) hdom q hG

/-! ## Localization before radial extension -/

section ZeroGermCover

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {ι : Type*}

/-- Enlarge only the domain of an already localized coefficient. The same
constants bound every derivative; outside the native chart its actual zero
germ supplies all zero tensors. -/
theorem NativeJets.on_zero_germ_cover {V V' : JetDomain ι X}
    {w : ι → X → ℝ} {f : ι → X → E} (hf : NativeJets V w f)
    (hcover : ∀ i x, x ∈ V'.carrier i →
      x ∈ V.carrier i ∨ f i =ᶠ[𝓝 x] fun _ => 0)
    (hw : ∀ i x, x ∈ V'.carrier i → 0 ≤ w i x)
    (hG : ∀ i x, x ∈ V'.carrier i → x ∈ V.carrier i →
      V.growth i x ≤ V'.growth i x) : NativeJets V' w f := by
  refine ⟨hw, ?_, ?_⟩
  · intro i x hx
    rcases hcover i x hx with hi | hz
    · exact ((hf.smooth i).contDiffAt ((V.isOpen i).mem_nhds hi)).contDiffWithinAt
    · exact (contDiffAt_const.congr_of_eventuallyEq hz).contDiffWithinAt
  · intro m
    obtain ⟨C, hC, p, hb⟩ := hf.bound m
    refine ⟨C, hC, p, ?_⟩
    intro i x hx j hj
    rcases hcover i x hx with hi | hz
    · exact (hb i x hi j hj).trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (zero_le_one.trans (V.one_le_growth i hi)) (hG i x hx hi) p)
          (zero_le_one.trans hC)) (hw i x hx))
    · rw [PhysicalWaveSum.iteratedFDeriv_eq_of_eventuallyEq hz j, iteratedFDeriv_fun_zero]
      simp only [Pi.zero_apply, norm_zero]
      exact mul_nonneg (mul_nonneg (zero_le_one.trans hC)
        (pow_nonneg (zero_le_one.trans (V'.one_le_growth i hx)) _)) (hw i x hx)

end ZeroGermCover

/-- A domain for the literal localized field over the full open native
annulus. Its growth allows the source chart scale and the given slow factor. -/
noncomputable def nativeDomain {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)
    {ι : Type*} (V : JetDomain ι NativePoint) (S : ι → ℝ) (q : ℕ) : JetDomain ι NativePoint where
  scale := V.scale
  carrier := fun _ => windowDomain nativeSlowDomain (nativeRadius F.data.h)
    (PrimaryTargetBounds.leftRadius W) (PrimaryTargetBounds.rightRadius W)
  isOpen := fun _ => windowDomain_open nativeSlowDomain_open
    (nativeRadius_smooth F.data.h_pos F.data.h_lt_half).continuousOn _ _
  one_le_scale := V.one_le_scale
  growth := fun i x => max (V.scale i) (S i) * edgeGrowth (nativeRadius F.data.h)
    (PrimaryTargetBounds.leftRadius W) (PrimaryTargetBounds.rightRadius W) x ^ q
  scale_le_growth := by
    intro i x _
    exact (le_max_left _ _).trans (le_mul_of_one_le_right
      (zero_le_one.trans ((V.one_le_scale i).trans (le_max_left _ _)))
      (one_le_pow₀ (edgeGrowth_one_le _ _ _ _)))

/-- The source chart need only cover points where the actual localized
formula has a nonzero germ. This permits slow-cell and outer-slot localization
before taking the radial zero extension. -/
theorem NativeJets.native_regular_of_zero_germ_cover
    {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)
    {ι : Type*} {V : JetDomain ι NativePoint} {A S : ι → ℝ}
    {P : ι → NativePoint → ℝ} {f : ι → NativePoint → E}
    (hf : NativeJets V (fun i x => A i * Real.sqrt (PrimaryTargetBounds.movingWeight W x.1) * P i
      x) f)
    (hA : ∀ i, 0 ≤ A i)
    (hP : ∀ i, ContinuousOn (P i) nativeSlowDomain)
    (hP0 : ∀ i x, x ∈ nativeSlowDomain → 0 ≤ P i x)
    (hcover : ∀ i x, x ∈ windowDomain nativeSlowDomain (nativeRadius F.data.h)
      (PrimaryTargetBounds.leftRadius W) (PrimaryTargetBounds.rightRadius W) →
      x ∈ V.carrier i ∨ f i =ᶠ[𝓝 x] fun _ => 0)
    (q : ℕ) (hG : ∀ i x, x ∈ windowDomain nativeSlowDomain (nativeRadius F.data.h)
      (PrimaryTargetBounds.leftRadius W) (PrimaryTargetBounds.rightRadius W) →
      x ∈ V.carrier i → V.growth i x ≤ S i * (max 1 (FinalSlowBase.edgeDistance W
        (BaseChartJets.normalizedCoordinates F.data.h x.1).2)⁻¹) ^ q) :
    ∀ i, NativeRegularity W (f i) := by
  have hG' : ∀ i x, x ∈ (nativeDomain W V S q).carrier i → x ∈ V.carrier i →
      V.growth i x ≤ (nativeDomain W V S q).growth i x := by
    intro i x hx hi
    calc
      _ ≤ S i * (max 1 (FinalSlowBase.edgeDistance W
          (BaseChartJets.normalizedCoordinates F.data.h x.1).2)⁻¹) ^ q := hG i x hx hi
      _ ≤ max (V.scale i) (S i) * (max 1 (FinalSlowBase.edgeDistance W
          (BaseChartJets.normalizedCoordinates F.data.h x.1).2)⁻¹) ^ q :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg (zero_le_one.trans (le_max_left _
          _)) _)
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (zero_le_one.trans (le_max_left _ _))
          (inner_edgeGrowth_le_native W hx.1 hx.2) q)
        (zero_le_one.trans ((V.one_le_scale i).trans (le_max_left _ _)))
  have hfull := NativeJets.on_zero_germ_cover (V' := nativeDomain W V S q) hf hcover
    (fun i x hx => mul_nonneg (mul_nonneg (hA i) (Real.sqrt_nonneg _)) (hP0 i x hx.1)) hG'
  intro i
  obtain ⟨hs, hj, he⟩ := NativeJets.native_zero_extension W hfull hA
    (fun i => (V.one_le_scale i).trans (le_max_left _ _)) hP hP0 (fun _ => Subset.rfl)
    q (fun _ _ _ => le_rfl) i
  exact ⟨hs, hj, he⟩

theorem primaryVelocity_native_regular_of_zero_germ_cover
    {F₀ : OutgoingProfile.Profile} (W : NominalProfile.Witness F₀)
    {ι : Type*} {U : PhaseJetBounds.Domain ι PhaseCalculus.Slow}
    (F : Fin 2 → PrimaryPulseBounds.PhaseConstruction U)
    (pref : Fin 2 → ι → ℝ) (χ : ι → NativePoint → PhaseCalculus.Slow × ℝ)
    (ε : ι → ℝ) (T : ι → NativePoint → SmoothCovariance.Vec2) (mask : ι → NativePoint → ℝ)
    {V : JetDomain ι NativePoint} (j : Fin 2)
    (hf : NativeJets V (fun i x => Real.sqrt (ε i) *
      (Real.sqrt (PrimaryTargetBounds.movingWeight W x.1) * pulseEnvelope F χ j i x))
      (primaryVelocity F pref χ ε T mask j))
    {S : ι → ℝ} (hχ : ∀ i, ContinuousOn (fun x => (χ i x).2) nativeSlowDomain)
    (hcover : ∀ i x, x ∈ windowDomain nativeSlowDomain (nativeRadius F₀.data.h)
      (PrimaryTargetBounds.leftRadius W) (PrimaryTargetBounds.rightRadius W) →
      x ∈ V.carrier i ∨ primaryVelocity F pref χ ε T mask j i =ᶠ[𝓝 x] fun _ => 0)
    (q : ℕ) (hG : ∀ i x, x ∈ windowDomain nativeSlowDomain (nativeRadius F₀.data.h)
      (PrimaryTargetBounds.leftRadius W) (PrimaryTargetBounds.rightRadius W) →
      x ∈ V.carrier i → V.growth i x ≤ S i * (max 1 (FinalSlowBase.edgeDistance W
        (BaseChartJets.normalizedCoordinates F₀.data.h x.1).2)⁻¹) ^ q) :
    ∀ i, NativeRegularity W (primaryVelocity F pref χ ε T mask j i) := by
  exact NativeJets.native_regular_of_zero_germ_cover W (by simpa only [mul_assoc] using hf)
    (fun i => Real.sqrt_nonneg (ε i)) (pulseEnvelope_continuousOn F χ hχ j)
    (fun i x _ => pulseEnvelope_nonneg F χ j i x) hcover q hG

/-- Extending by zero does not enlarge an interior tensor bound. This
pointwise form keeps any constants already uniform in the external labels. -/
theorem NativeRegularity.jet_bound {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
    {f : NativePoint → E} (h : NativeRegularity W f) (n : ℕ) {x : NativePoint}
    (hx : x ∈ nativeSlowDomain) {B : ℝ} (hB : 0 ≤ B)
    (hb : nativeRadius F.data.h x ∈ Ioo (PrimaryTargetBounds.leftRadius W)
      (PrimaryTargetBounds.rightRadius W) → ‖iteratedFDeriv ℝ n f x‖ ≤ B) :
    ‖iteratedFDeriv ℝ n (nativeExtension W f) x‖ ≤ B := by
  by_cases hi : nativeRadius F.data.h x ∈ Ioo (PrimaryTargetBounds.leftRadius W)
      (PrimaryTargetBounds.rightRadius W)
  · rw [h.jet_inside n hx hi]
    exact hb hi
  · rw [h.jet_outside n hx hi, norm_zero]
    exact hB

/-- Every pre-existing uniform native constant and polynomial degree is
unchanged by the literal extension. The regularity at the new radial boundary
is supplied by the construction above. -/
theorem NativeJets.nativeExtension_jets {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)
    {ι : Type*} {V : JetDomain ι NativePoint} {w : ι → NativePoint → ℝ}
    {f : ι → NativePoint → E} (hf : NativeJets V w f)
    (hreg : ∀ i, NativeRegularity W (f i))
    (hslow : ∀ i, V.carrier i ⊆ nativeSlowDomain) :
    NativeJets V w (fun i => nativeExtension W (f i)) := by
  refine ⟨hf.nonneg, fun i => (hreg i).smooth.mono (hslow i), ?_⟩
  intro m
  obtain ⟨C, hC, p, hb⟩ := hf.bound m
  refine ⟨C, hC, p, ?_⟩
  intro i x hx j hj
  exact (hreg i).jet_bound j (hslow i hx)
    (mul_nonneg (mul_nonneg (zero_le_one.trans hC)
      (pow_nonneg (zero_le_one.trans (V.one_le_growth i hx)) _)) (hf.nonneg i x hx))
    (fun _ => hb i x hx j hj)

/-! ## The same extension in the mean-field variable ordering -/

/-- The actual permutation from `(R,((T,Z),Y))` to `((R,(Z,T)),Y)`. -/
noncomputable def meanNative : LocalSignedRequest.Point ≃ₗᵢ[ℝ] NativePoint where
  toLinearEquiv := {
    toFun := fun x => ((x.1, (x.2.1.2, x.2.1.1)), x.2.2)
    invFun := fun x => (x.1.1, ((x.1.2.2, x.1.2.1), x.2))
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  norm_map' := by
    intro x
    change max (max ‖x.1‖ (max ‖x.2.1.2‖ ‖x.2.1.1‖)) ‖x.2.2‖ =
      max ‖x.1‖ (max (max ‖x.2.1.1‖ ‖x.2.1.2‖) ‖x.2.2‖)
    rw [max_comm ‖x.2.1.2‖ ‖x.2.1.1‖, max_assoc]

theorem meanNative_apply (x : LocalSignedRequest.Point) :
    meanNative x = (PrimaryTargetBounds.meanPoint x, x.2.2) := rfl

theorem nativeRadius_meanNative {F : OutgoingProfile.Profile} (x : LocalSignedRequest.Point) :
    nativeRadius F.data.h (meanNative x) = (LocalSignedRequest.profileMap (2 * F.data.h) x).1 := by
  unfold nativeRadius PrimaryTargetBounds.profileRadius
  rw [meanNative_apply, PrimaryTargetBounds.meanPoint_scalar]
  rfl

noncomputable def meanExtension {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)
    (f : NativePoint → E) (x : LocalSignedRequest.Point) : E := nativeExtension W f (meanNative x)

omit [NormedSpace ℝ E] in
theorem meanExtension_inside {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)
    (f : NativePoint → E) {x : LocalSignedRequest.Point}
    (hx : (LocalSignedRequest.profileMap (2 * F.data.h) x).1 ∈
      Ioo (PrimaryTargetBounds.leftRadius W) (PrimaryTargetBounds.rightRadius W)) :
    meanExtension W f x = f (meanNative x) :=
  nativeExtension_inside W f (by rwa [nativeRadius_meanNative])

omit [NormedSpace ℝ E] in
theorem meanExtension_outside {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)
    (f : NativePoint → E) {x : LocalSignedRequest.Point}
    (hx : (LocalSignedRequest.profileMap (2 * F.data.h) x).1 ∉
      Ioo (PrimaryTargetBounds.leftRadius W) (PrimaryTargetBounds.rightRadius W)) :
    meanExtension W f x = 0 := nativeExtension_outside W f (by rwa [nativeRadius_meanNative])

theorem NativeRegularity.mean_smooth {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
    {f : NativePoint → E} (h : NativeRegularity W f) :
    ContDiffOn ℝ ∞ (meanExtension W f) {x : LocalSignedRequest.Point | 0 < x.2.1.1} :=
  h.smooth.comp meanNative.contDiff.contDiffOn (fun _ hx => hx)

/-- Reordering the coordinates preserves the norm of every full tensor. -/
theorem meanExtension_jet_norm {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)
    (f : NativePoint → E) (n : ℕ) (x : LocalSignedRequest.Point) :
    ‖iteratedFDeriv ℝ n (meanExtension W f) x‖ =
      ‖iteratedFDeriv ℝ n (nativeExtension W f) (meanNative x)‖ :=
  meanNative.norm_iteratedFDeriv_comp_right (nativeExtension W f) x n

theorem NativeRegularity.mean_edge {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
    {f : NativePoint → E} (h : NativeRegularity W f) (n : ℕ) {x : LocalSignedRequest.Point}
    (hx : 0 < x.2.1.1)
    (he : (LocalSignedRequest.profileMap (2 * F.data.h) x).1 = PrimaryTargetBounds.leftRadius W ∨
      (LocalSignedRequest.profileMap (2 * F.data.h) x).1 = PrimaryTargetBounds.rightRadius W) :
    iteratedFDeriv ℝ n (meanExtension W f) x = 0 := by
  apply norm_eq_zero.mp
  rw [meanExtension_jet_norm, h.edge n (meanNative x) hx (by rwa [nativeRadius_meanNative]),
    norm_zero]

end NavierStokes.WaveEdgeExtension
