/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.GaussianTailFlat
public import LeanPool.NavierStokesAndEuler.NavierStokes.CommonCoverClass
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Source envelopes along an entire common-cover slot path

The common-cover envelope is an actual sum over native copies. Injectivity
of the padded native rectangle identifies the one copy met by a slot path.
The source itself is not assumed periodic on the native torus.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.WaveEnvelopeTransport

open Set Function Filter
open scoped ContDiff Topology BigOperators
open CommonCoverSolve CommonCoverClass TorusInverse

private theorem nat_le_infty (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ :=
  ENat.natCast_le_of_coe_top_le_withTop le_rfl n

/-- The full padded integration rectangle, including both time endpoints. -/
noncomputable def rectangle (r L : ℝ) : Set Plane := Icc (-r) r ×ˢ Icc 0 L

/-- Native region, given by `(fun z => g.center + g.basis z) '' rectangle r L`. -/
noncomputable def nativeRegion (g : Geometry) (r L : ℝ) : Set Plane :=
  (fun z => g.center + g.basis z) '' rectangle r L

/-- A geometric injectivity condition, independent of all source fields. -/
noncomputable def Separated (g : Geometry) (r L : ℝ) : Prop :=
  InjOn TorusAverages.quotientPoint (nativeRegion g r L)

theorem native_coordinate_lattice (g : Geometry) (k : Frequency) (Y : Plane) :
    g.center + g.basis (g.coordinates k Y) =
      TorusAverages.latticePoint (-k) + coverPower g.gap Y := by
  have hneg : TorusAverages.latticePoint (-k) = -TorusAverages.latticePoint k := by
    ext <;> simp [TorusAverages.latticePoint]
  rw [Geometry.coordinates, ContinuousLinearEquiv.apply_symm_apply, hneg]
  abel

theorem copy_unique {g : Geometry} {r L : ℝ} (hsep : Separated g r L)
    {k l : Frequency} {Y : Plane} (hk : g.coordinates k Y ∈ rectangle r L)
    (hl : g.coordinates l Y ∈ rectangle r L) : k = l := by
  have hkm : TorusAverages.latticePoint (-k) + coverPower g.gap Y ∈ nativeRegion g r L := by
    rw [← native_coordinate_lattice]
    exact ⟨g.coordinates k Y, hk, rfl⟩
  have hlm : TorusAverages.latticePoint (-l) + coverPower g.gap Y ∈ nativeRegion g r L := by
    rw [← native_coordinate_lattice]
    exact ⟨g.coordinates l Y, hl, rfl⟩
  exact neg_injective (TorusAverages.latticeTranslate_unique hsep hkm hlm)

/-- The envelope of the grouped label on the common cover. The summands
are nonzero only on their own native integration rectangles. -/
noncomputable def copyEnvelope (g : Geometry) (r L : ℝ) (W : ℝ → ℝ) (Y : Plane) : ℝ := by
  classical
  exact ∑' k : Frequency, if g.coordinates k Y ∈ rectangle r L then W (g.coordinates k Y).2 else 0

theorem copyEnvelope_nonneg (g : Geometry) (r L : ℝ) {W : ℝ → ℝ}
    (hW : ∀ s, 0 ≤ W s) (Y : Plane) : 0 ≤ copyEnvelope g r L W Y := by
  classical
  apply tsum_nonneg
  intro k
  split_ifs
  · exact hW _
  · exact le_rfl

theorem copyEnvelope_eq_copy {g : Geometry} {r L : ℝ} (hsep : Separated g r L)
    (W : ℝ → ℝ) {k : Frequency} {Y : Plane} (hk : g.coordinates k Y ∈ rectangle r L) :
    copyEnvelope g r L W Y = W (g.coordinates k Y).2 := by
  classical
  unfold copyEnvelope
  rw [tsum_eq_single k]
  · simp only [ite_eq_left hk]
  · intro l hl
    split_ifs with hmem
    · exact (hl (copy_unique hsep hmem hk)).elim
    · rfl

theorem coordinates_path_in_rectangle (g : Geometry) (k : Frequency) (Y : Plane)
    {r L s : ℝ} (hξ : (g.coordinates k Y).1 ∈ Icc (-r) r) (hs : s ∈ Icc 0 L) :
    g.coordinates k (g.path k Y s) ∈ rectangle r L := by
  rw [g.coordinates_path]
  exact ⟨hξ, hs⟩

/-- Exact envelope identification at every integration time, including
the entry and exit. No bound at the current point is extrapolated. -/
theorem copyEnvelope_path {g : Geometry} {r L : ℝ} (hsep : Separated g r L)
    (W : ℝ → ℝ) (k : Frequency) (Y : Plane)
    (hξ : (g.coordinates k Y).1 ∈ Icc (-r) r) {s : ℝ} (hs : s ∈ Icc 0 L) :
    copyEnvelope g r L W (g.path k Y s) = W s := by
  rw [copyEnvelope_eq_copy hsep W (coordinates_path_in_rectangle g k Y hξ hs),
    g.coordinates_path]

theorem entire_path_in_rectangle (g : Geometry) (k : Frequency) (Y : Plane)
    {r L : ℝ} (hξ : (g.coordinates k Y).1 ∈ Icc (-r) r) :
    MapsTo (g.path k Y) (Icc 0 L) {Z | g.coordinates k Z ∈ rectangle r L} :=
  fun _ hs => coordinates_path_in_rectangle g k Y hξ hs

theorem path_transverse (g : Geometry) (k : Frequency) (Y : Plane) (s : ℝ) :
    (g.coordinates k (g.path k Y s)).1 = (g.coordinates k Y).1 := by
  rw [g.coordinates_path]

theorem path_time (g : Geometry) (k : Frequency) (Y : Plane) (s : ℝ) :
    (g.coordinates k (g.path k Y s)).2 = s := by rw [g.coordinates_path]

section SlowCoordinates

variable {P : Type} {V : Type*}

theorem source_path_observable (g : Geometry) (k : Frequency) (F : P → V)
    (z : P × Plane) (s : ℝ) : F (sourceArgument g k (z, s)).1 = F z.1 := rfl

theorem source_path_mem (g : Geometry) (k : Frequency) {U : Set P}
    {z : P × Plane} (hz : z.1 ∈ U) (s : ℝ) :
    sourceArgument g k (z, s) ∈ U ×ˢ univ := ⟨hz, mem_univ _⟩

theorem source_path_domain (g : Geometry) (k : Frequency) (U : Set P) (r L : ℝ) :
    MapsTo (sourceArgument (P := P) g k)
      ({z : P × Plane | z.1 ∈ U ∧ (g.coordinates k z.2).1 ∈ Icc (-r) r} ×ˢ Icc 0 L)
      {z : P × Plane | z.1 ∈ U ∧ g.coordinates k z.2 ∈ rectangle r L} := by
  rintro ⟨⟨p, Y⟩, s⟩ ⟨⟨hp, hξ⟩, hs⟩
  exact ⟨hp, coordinates_path_in_rectangle g k Y hξ hs⟩

end SlowCoordinates

/-- The actual GaussianTailFlat cutoff is evaluated at the integration
time, on the same native copy used to evaluate the source. -/
theorem cutoff_on_path (g : Geometry) (k : Frequency) (Y : Plane) (L s : ℝ) :
    GaussianTailFlat.slotCutoff L (g.coordinates k (g.path k Y s)).2 =
      GaussianTailFlat.slotCutoff L s := by rw [g.coordinates_path]

theorem reference_envelope_on_path {g : Geometry} {r L : ℝ}
    (hsep : Separated g r L) (lam u : ℝ) (k : Frequency) (Y : Plane)
    (hξ : (g.coordinates k Y).1 ∈ Icc (-r) r) {s : ℝ} (hs : s ∈ Icc 0 L) :
    copyEnvelope g r L (GaussianEnvelope.envelope (GaussianEnvelope.referenceRate lam u L) (L / 2))
      (g.path k Y s) =
      GaussianEnvelope.envelope (GaussianEnvelope.referenceRate lam u L) (L / 2) s :=
  copyEnvelope_path hsep _ k Y hξ hs

theorem reference_envelope_path_gaussian {g : Geometry} {r L lam u : ℝ}
    (hsep : Separated g r L) (hlam : 0 < lam) (hu : 0 < u) (hL : 0 < L)
    (k : Frequency) (Y : Plane) (hξ : (g.coordinates k Y).1 ∈ Icc (-r) r)
    {s : ℝ} (hs : s ∈ Icc 0 L) :
    Real.exp (-(u * GaussianEnvelope.referenceMaxSlope lam u) * (s - L / 2) ^ 2 / (2 * L)) ≤
      copyEnvelope g r L (GaussianEnvelope.envelope (GaussianEnvelope.referenceRate lam u L) (L /
          2))
        (g.path k Y s) ∧
      copyEnvelope g r L (GaussianEnvelope.envelope (GaussianEnvelope.referenceRate lam u L) (L /
          2))
        (g.path k Y s) ≤
      Real.exp (-(u * GaussianEnvelope.referenceMinSlope lam u) * (s - L / 2) ^ 2 / (2 * L)) := by
  rw [reference_envelope_on_path hsep lam u k Y hξ hs]
  exact GaussianEnvelope.reference_gaussian_bounds hlam hu hL hs

/-- A concrete geometric criterion, uniform in the band and covering gap.
After multiplying slot time by `ci`, the full rectangle has transverse
half-width `r0`, so its injectivity does not deteriorate as `L` grows. -/
theorem separated_bandGeometry (B : Plane ≃L[ℝ] Plane) (h : ℝ) (n gap : ℕ)
    (center : Plane) {r r0 R : ℝ} (hr : r < R) (hr0 : r0 < R)
    (hsmall : ‖(B : Plane →L[ℝ] Plane)‖ * R < 1 / 2) :
    Separated (bandGeometry B h n gap center) r (ChartScales.slotLength r0 h n) := by
  apply (TorusAverages.quotientPoint_injOn_small_chart B (center + B (0, r0)) R hsmall).mono
  rintro Y ⟨z, hz, rfl⟩
  have hci := ChartScales.timeCoefficient_pos h n
  have htime : 0 ≤ ChartScales.timeCoefficient h n * z.2 ∧
      ChartScales.timeCoefficient h n * z.2 ≤ 2 * r0 := by
    refine ⟨mul_nonneg hci.le hz.2.1, ?_⟩
    have ht := (le_div_iff₀ hci).1 hz.2.2
    simpa only [mul_comm] using ht
  refine ⟨(z.1, ChartScales.timeCoefficient h n * z.2 - r0), ?_, ?_⟩
  · rw [Metric.mem_ball, dist_zero_right, Prod.norm_def, max_lt_iff,
      Real.norm_eq_abs, Real.norm_eq_abs]
    constructor
    · exact (abs_le.mpr hz.1).trans_lt hr
    · apply (abs_le.mpr ?_).trans_lt hr0
      dsimp only
      constructor <;> linarith [htime.1, htime.2]
  · change (center + B (0, r0)) + B (z.1, ChartScales.timeCoefficient h n * z.2 - r0) =
      center + scaledBasis B _ _ z
    rw [scaledBasis_apply, add_assoc, ← map_add]
    congr 2
    ext <;> simp

theorem exists_separated_native_rectangle (B : Plane ≃L[ℝ] Plane) :
    ∃ r : ℝ, 0 < r ∧ ∀ h : ℝ, ∀ n gap : ℕ, ∀ center : Plane,
      Separated (bandGeometry B h n gap center) r (ChartScales.slotLength r h n) := by
  let M := ‖(B : Plane →L[ℝ] Plane)‖
  let r := 1 / (8 * (M + 1))
  have hM : 0 ≤ M := norm_nonneg _
  have hr : 0 < r := by dsimp [r]; positivity
  refine ⟨r, hr, fun h n gap center => separated_bandGeometry B h n gap center
    (R := 2 * r) (by linarith) (by linarith) ?_⟩
  change M * (2 * (1 / (8 * (M + 1)))) < 1 / 2
  apply (mul_lt_mul_iff_of_pos_right (show 0 < 8 * (M + 1) by positivity)).1
  field_simp
  linarith

section GroupedSources

open WeightedClasses

variable {P V : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Copy cell, given by `{z | g.coordinates k z.2 ∈ rectangle r L}`. -/
noncomputable def copyCell (g : Geometry) (r L : ℝ) (k : Frequency) : Set (P × Plane) :=
  {z | g.coordinates k z.2 ∈ rectangle r L}

omit [NormedSpace ℝ P] in
theorem copyCell_closed (g : Geometry) (r L : ℝ) (k : Frequency) :
    IsClosed (copyCell (P := P) g r L k) :=
  (isClosed_Icc.prod isClosed_Icc).preimage
    ((g.coordinates_contDiff k).continuous.comp continuous_snd)

omit [NormedSpace ℝ P] in
theorem copyCell_locallyFinite (g : Geometry) (r L : ℝ) :
    LocallyFinite (copyCell (P := P) g r L) := by
  classical
  let κ : Plane → ℝ := (rectangle r L).indicator (fun _ => 1)
  have hκ : HasCompactSupport κ :=
    HasCompactSupport.intro' (K := rectangle r L) (isCompact_Icc.prod isCompact_Icc)
      (isClosed_Icc.prod isClosed_Icc) (fun z hz => by simp [κ, hz])
  intro z
  obtain ⟨s, hs⟩ := g.finite_copy_cutoffs hκ (‖z.2‖ + 1)
  refine ⟨{y : P × Plane | ‖y.2‖ < ‖z.2‖ + 1},
    (isOpen_lt continuous_snd.norm continuous_const).mem_nhds (by simp), ?_⟩
  apply s.finite_toSet.subset
  intro k hk
  obtain ⟨y, hy, hnorm⟩ := hk
  by_contra hnot
  have hh := hs y.2 hnorm.le k hnot
  change g.coordinates k y.2 ∈ rectangle r L at hy
  simp [κ, hy] at hh

/-- Coefficients may differ in every native copy. This is an actual sum
of common-cover fields, with no substitution of a native-periodic source. -/
noncomputable def grouped (F : Frequency → P × Plane → V) (z : P × Plane) : V :=
  ∑' k : Frequency, F k z

omit [NormedSpace ℝ P] [NormedSpace ℝ V] in
theorem grouped_eventually_eq_copy {g : Geometry} {r L : ℝ}
    (hsep : Separated g r L) (F : Frequency → P × Plane → V)
    (hsupport : ∀ k, support (F k) ⊆ copyCell g r L k)
    {k : Frequency} {z : P × Plane} (hz : z ∈ copyCell g r L k) :
    grouped F =ᶠ[𝓝 z] F k := by
  classical
  have hn := (copyCell_locallyFinite (P := P) g r L).iInter_compl_mem_nhds
    (copyCell_closed g r L) z
  filter_upwards [hn] with y hy
  apply tsum_eq_single k
  intro l hl
  have hznot : z ∉ copyCell g r L l := fun hzl => hl (copy_unique hsep hzl hz)
  have hynot := mem_iInter₂.mp hy l hznot
  by_contra hne
  exact hynot (hsupport l hne)

omit [NormedSpace ℝ P] [NormedSpace ℝ V] in
theorem grouped_eventually_zero {g : Geometry} {r L : ℝ}
    (F : Frequency → P × Plane → V)
    (hsupport : ∀ k, support (F k) ⊆ copyCell g r L k)
    {z : P × Plane} (hz : ∀ k, z ∉ copyCell g r L k) :
    grouped F =ᶠ[𝓝 z] fun _ => 0 := by
  classical
  have hn := (copyCell_locallyFinite (P := P) g r L).iInter_compl_mem_nhds
    (copyCell_closed g r L) z
  filter_upwards [hn] with y hy
  have hzero : ∀ k, F k y = 0 := by
    intro k
    by_contra hne
    exact (mem_iInter₂.mp hy k (hz k)) (hsupport k hne)
  simp only [grouped, hzero, tsum_zero]

omit [NormedSpace ℝ P] [NormedSpace ℝ V] in
theorem grouped_on_entire_path {g : Geometry} {r L : ℝ}
    (hsep : Separated g r L) (F : Frequency → P × Plane → V)
    (hsupport : ∀ k, support (F k) ⊆ copyCell g r L k)
    (k : Frequency) (p : P) (Y : Plane)
    (hξ : (g.coordinates k Y).1 ∈ Icc (-r) r) :
    ∀ v ∈ Icc 0 L, grouped F (p, g.path k Y v) = F k (p, g.path k Y v) := by
  intro v hv
  have hmem : (p, g.path k Y v) ∈ copyCell g r L k :=
    coordinates_path_in_rectangle g k Y hξ hv
  exact (grouped_eventually_eq_copy hsep F hsupport hmem).self_of_nhds

omit [NormedSpace ℝ P] [NormedSpace ℝ V] in
/-- A transverse support exclusion for the actual copy coefficient excludes
the entire grouped source on the entire integration path. -/
theorem grouped_path_zero_of_transverse_support {g : Geometry} {r L : ℝ}
    (hsep : Separated g r L) (F : Frequency → P × Plane → V)
    (hsupport : ∀ k, support (F k) ⊆ copyCell g r L k)
    (k : Frequency) (p : P) (Y : Plane) (T : Set ℝ)
    (htransverse : support (F k) ⊆ {z | (g.coordinates k z.2).1 ∈ T})
    (hξ : (g.coordinates k Y).1 ∈ Icc (-r) r) (hξT : (g.coordinates k Y).1 ∉ T) :
    ∀ v ∈ Icc 0 L, grouped F (p, g.path k Y v) = 0 := by
  intro v hv
  rw [grouped_on_entire_path hsep F hsupport k p Y hξ v hv]
  by_contra hne
  have hh := htransverse hne
  exact hξT (by simpa only [Set.mem_ofPred_eq, path_transverse] using hh)

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedSpace ℝ V] in
theorem grouped_path_zero_of_slow_support (g : Geometry)
    (F : Frequency → P × Plane → V) (U : Set P)
    (hsupport : ∀ k, support (F k) ⊆ {z | z.1 ∈ U})
    (k : Frequency) {p : P} (hp : p ∉ U) (Y : Plane) (v : ℝ) :
    grouped F (p, g.path k Y v) = 0 := by
  have hz : ∀ l, F l (p, g.path k Y v) = 0 := by
    intro l
    by_contra hne
    exact hp (hsupport l hne)
  simp only [grouped, hz, tsum_zero]

private theorem jet_congr {f g : P × Plane → V} {x : P × Plane}
    (he : f =ᶠ[𝓝 x] g) (j : ℕ) : iteratedFDeriv ℝ j f x = iteratedFDeriv ℝ j g x := by
  have he' : f =ᶠ[𝓝[univ] x] g := by simpa only [nhdsWithin_univ] using he
  simpa only [iteratedFDerivWithin_univ] using
    he'.iteratedFDerivWithin_eq (𝕜 := ℝ) he.self_of_nhds j

/-- Uniform bounds on the actual supported copy coefficients give the
WaveClass of their actual grouped field. Local finiteness and geometric
separation justify all derivatives of the sum. -/
theorem grouped_waveClass (s : StripData P) (g : ℕ → Geometry) (r L : ℕ → ℝ)
    (hsep : ∀ n, Separated (g n) (r n) (L n))
    (W : ℕ → ℝ → ℝ) (hW : ∀ n v, 0 ≤ W n v) (α : ℝ)
    (F : ℕ → Frequency → P × Plane → V)
    (hFs : ∀ n k, ContDiffOn ℝ ∞ (F n k) (sourceStrip s).domain)
    (hFsupport : ∀ n k, support (F n k) ⊆ copyCell (g n) (r n) (L n) k)
    (hFjets : ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∃ d : ℕ, ∀ n k z,
      z.1 ∈ s.domain → ∀ j ≤ N, ‖iteratedFDeriv ℝ j (F n k) z‖ ≤
        C * s.epsilon n ^ α * s.growth n z.1 ^ d * Real.sqrt (s.zeta z.1) *
          W n ((g n).coordinates k z.2).2) :
    WaveClass (sourceStrip s) (fun n z => copyEnvelope (g n) (r n) (L n) (W n) z.2)
      α (fun n => grouped (F n)) := by
  classical
  refine ⟨fun n z _ => mul_nonneg (Real.sqrt_nonneg _) (copyEnvelope_nonneg _ _ _ (hW n) _), ?_, ?_⟩
  · intro n z hz
    by_cases hk : ∃ k, z ∈ copyCell (g n) (r n) (L n) k
    · obtain ⟨k, hk⟩ := hk
      exact ((hFs n k).contDiffAt ((sourceStrip s).isOpen_domain.mem_nhds hz)).congr_of_eventuallyEq
        (grouped_eventually_eq_copy (hsep n) (F n) (hFsupport n) hk) |>.contDiffWithinAt
    · have hn : ∀ k, z ∉ copyCell (g n) (r n) (L n) k := by simpa using hk
      exact (contDiffAt_const.congr_of_eventuallyEq
        (grouped_eventually_zero (F n) (hFsupport n) hn)).contDiffWithinAt
  · intro N
    obtain ⟨C, hC, d, hb⟩ := hFjets N
    refine ⟨C, hC, d, ?_⟩
    intro n z hz j hj
    by_cases hk : ∃ k, z ∈ copyCell (g n) (r n) (L n) k
    · obtain ⟨k, hk⟩ := hk
      rw [jet_congr (grouped_eventually_eq_copy (hsep n) (F n) (hFsupport n) hk) j]
      have hh := hb n k z hz j hj
      change ‖iteratedFDeriv ℝ j (F n k) z‖ ≤
        C * s.epsilon n ^ α * s.growth n z.1 ^ d *
          (Real.sqrt (s.zeta z.1) * copyEnvelope (g n) (r n) (L n) (W n) z.2)
      rw [copyEnvelope_eq_copy (hsep n) (W n) hk]
      nlinarith
    · have hn : ∀ k, z ∉ copyCell (g n) (r n) (L n) k := by simpa using hk
      rw [jet_congr (grouped_eventually_zero (F n) (hFsupport n) hn) j,
        iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
      exact majorant_nonneg _ _ _ hC _ _ _
        (mul_nonneg (Real.sqrt_nonneg _) (copyEnvelope_nonneg _ _ _ (hW n) _))

end GroupedSources

section SourceJetTransport

open WeightedClasses

variable {P V : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Full joint derivatives of the actual source along every point of the
slot. The inverse-edge factor remains frozen in `s.growth n z.1`.
The source may depend on the common coordinate in any way allowed by its
actual WaveClass; native periodicity is not a premise. -/
theorem waveClass_sourceArgument_bound
    (s : StripData P) (B : Plane ≃L[ℝ] Plane) {h : ℝ} (hh : 0 ≤ h)
    (gapBound : ℕ) (band gap : ℕ → ℕ) (center : ℕ → Plane) (r L : ℕ → ℝ)
    (hband : ∀ n, 4 ≤ band n) (hgap : ∀ n, gap n ≤ gapBound)
    (hslow : ∀ n, s.slow n = ChartScales.S (band n))
    (hsep : ∀ n, Separated (bandGeometry B h (band n) (gap n) (center n)) (r n) (L n))
    (W : ℕ → ℝ → ℝ) (hW : ∀ n v, 0 ≤ W n v)
    {α : ℝ} {f : ℕ → P × Plane → V}
    (hf : WaveClass (sourceStrip s)
      (fun n z => copyEnvelope (bandGeometry B h (band n) (gap n) (center n)) (r n) (L n) (W n) z.2)
      α f) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ d : ℕ, ∀ n (k : Frequency) (z : P × Plane), z.1 ∈ s.domain →
      ((bandGeometry B h (band n) (gap n) (center n)).coordinates k z.2).1 ∈ Icc (-(r n)) (r n) →
      ∀ v ∈ Icc 0 (L n), ∀ j ≤ N,
      ‖iteratedFDeriv ℝ j
        (fun x : Joint P => f n (sourceArgument (bandGeometry B h (band n) (gap n) (center n)) k x))
        (z, v)‖ ≤
      C * s.growth n z.1 ^ d * (s.epsilon n ^ α * Real.sqrt (s.zeta z.1)) * W n v := by
  obtain ⟨A, hA, p, ha⟩ := hf.bounds N
  let K := bandArgumentCost B gapBound
  have hK : 1 ≤ K := bandArgumentCost_one_le B gapBound
  refine ⟨A * K ^ N, by positivity, p + N, ?_⟩
  intro n k z hz hξ v hv j hj
  let g := bandGeometry B h (band n) (gap n) (center n)
  have hmap : sourceArgument g k (z, v) ∈ (sourceStrip s).domain := hz
  have hlocal : sourceArgument g k 0 + sourceLinear P g (z, v) ∈ (sourceStrip s).domain := by
    rw [← sourceArgument_affine]
    exact hmap
  have hjet := CommonCoverClass.norm_affine_jet_le_on (sourceStrip s).isOpen_domain
    (hf.smooth n) (sourceLinear P g) (sourceArgument g k 0) hlocal j
  simp_rw [← sourceArgument_affine] at hjet
  have hsrc := ha n (sourceArgument g k (z, v)) hmap j hj
  change ‖iteratedFDeriv ℝ j (f n) (sourceArgument g k (z, v))‖ ≤
    A * s.epsilon n ^ α * s.growth n z.1 ^ p *
      (Real.sqrt (s.zeta z.1) * copyEnvelope g (r n) (L n) (W n) (g.path k z.2 v)) at hsrc
  rw [copyEnvelope_path (hsep n) (W n) k z.2 hξ hv] at hsrc
  have hG := s.one_le_growth n z.1
  have hGn := s.growth_nonneg n z.1
  have hlin : ‖sourceLinear P g‖ ≤ K * s.growth n z.1 := by
    apply (norm_sourceLinear_le g).trans
    apply (bandGeometry_argumentCost_le B hh (hband n) (hgap n) (center n)).trans
    rw [← hslow n]
    exact mul_le_mul_of_nonneg_left (s.slow_le_growth n z.1) (zero_le_one.trans hK)
  have hpow : ‖sourceLinear P g‖ ^ j ≤ K ^ N * s.growth n z.1 ^ N := by
    rw [← mul_pow]
    exact (pow_le_pow_left₀ (norm_nonneg _) hlin j).trans
      (pow_le_pow_right₀ (one_le_mul_of_one_le_of_one_le hK hG) hj)
  have hw := hW n v
  have he := s.epsilon_pos n
  calc
    _ ≤ ‖iteratedFDeriv ℝ j (f n) (sourceArgument g k (z, v))‖ *
        ‖sourceLinear P g‖ ^ j := hjet
    _ ≤ (A * s.epsilon n ^ α * s.growth n z.1 ^ p * (Real.sqrt (s.zeta z.1) * W n v)) *
        (K ^ N * s.growth n z.1 ^ N) :=
      mul_le_mul hsrc hpow (pow_nonneg (norm_nonneg _) _) (by positivity)
    _ = _ := by rw [pow_add]; ring

end SourceJetTransport

section ForcingJetTransport

open WeightedClasses

variable {X P V H : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem clm_apply_jet_bound_on {U : Set X} (hU : IsOpen U)
    {A : X → V →L[ℝ] H} {f : X → V} (hA : ContDiffOn ℝ ∞ A U)
    (hf : ContDiffOn ℝ ∞ f U) {x : X} (hx : x ∈ U) (N : ℕ) {C D : ℝ}
    (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hAj : ∀ j ≤ N, ‖iteratedFDeriv ℝ j A x‖ ≤ C)
    (hfj : ∀ j ≤ N, ‖iteratedFDeriv ℝ j f x‖ ≤ D) (j : ℕ) (hj : j ≤ N) :
    ‖iteratedFDeriv ℝ j (fun y => A y (f y)) x‖ ≤ (2 : ℝ) ^ N * C * D := by
  have hb := norm_iteratedFDerivWithin_clm_apply hA hf hU.uniqueDiffOn hx (nat_le_infty j)
  simp only [iteratedFDerivWithin_of_isOpen _ hU hx] at hb
  apply hb.trans
  calc
    _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * C * D := by
      apply Finset.sum_le_sum
      intro i hi
      have hij : i ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hAj i (hij.trans hj)) (Nat.cast_nonneg _))
        (hfj (j - i) ((Nat.sub_le _ _).trans hj)) (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) hC)
    _ = (2 : ℝ) ^ j * C * D := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      congr 2
      exact_mod_cast Nat.sum_range_choose j
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj) hC) hD

/-- The actual projected source operator along the whole integration path.
Only native forcing-map jets and the original common-cover source class are
inputs. Both affine pullbacks and their Leibniz product are differentiated. -/
theorem waveClass_forcingAlong_bound
    (s : StripData P) (B : Plane ≃L[ℝ] Plane) {h : ℝ} (hh : 0 ≤ h)
    (gapBound : ℕ) (band gap : ℕ → ℕ) (center : ℕ → Plane) (r L : ℕ → ℝ)
    (hband : ∀ n, 4 ≤ band n) (hgap : ∀ n, gap n ≤ gapBound)
    (hslow : ∀ n, s.slow n = ChartScales.S (band n))
    (hsep : ∀ n, Separated (bandGeometry B h (band n) (gap n) (center n)) (r n) (L n))
    (W : ℕ → ℝ → ℝ) (hW : ∀ n v, 0 ≤ W n v)
    (I : ℕ → Set ℝ) (hI : ∀ n, IsOpen (I n)) (hLI : ∀ n, Icc 0 (L n) ⊆ I n)
    (d : ℕ → LinearData P V H) {α : ℝ}
    (hf : WaveClass (sourceStrip s)
      (fun n z => copyEnvelope (bandGeometry B h (band n) (gap n) (center n)) (r n) (L n) (W n) z.2)
      α (fun n => (d n).source))
    (hB : ∀ n, ContDiffOn ℝ ∞ (d n).forcingMap (s.domain ×ˢ (univ ×ˢ I n)))
    (hBj : ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∃ p : ℕ,
      ∀ n x, x ∈ s.domain → ∀ ξ ∈ Icc (-(r n)) (r n), ∀ v ∈ Icc 0 (L n), ∀ j ≤ N,
        ‖iteratedFDeriv ℝ j (d n).forcingMap (x, (ξ, v))‖ ≤ C * s.growth n x ^ p)
    (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ p : ℕ, ∀ n (k : Frequency) (z : P × Plane), z.1 ∈ s.domain →
      ((bandGeometry B h (band n) (gap n) (center n)).coordinates k z.2).1 ∈ Icc (-(r n)) (r n) →
      ∀ v ∈ Icc 0 (L n), ∀ j ≤ N,
      ‖iteratedFDeriv ℝ j
        ((d n).forcingAlong (bandGeometry B h (band n) (gap n) (center n)) k) (z, v)‖ ≤
      C * s.growth n z.1 ^ p * (s.epsilon n ^ α * Real.sqrt (s.zeta z.1)) * W n v := by
  obtain ⟨C, hC, p, hsource⟩ := waveClass_sourceArgument_bound s B hh gapBound band gap center r L
    hband hgap hslow hsep W hW hf N
  obtain ⟨A, hA, q, hnative⟩ := hBj N
  let K := bandArgumentCost B gapBound
  have hK : 1 ≤ K := bandArgumentCost_one_le B gapBound
  refine ⟨(2 : ℝ) ^ N * A * K ^ N * C, by positivity, q + N + p, ?_⟩
  intro n k z hz hξ v hv j hj
  let g := bandGeometry B h (band n) (gap n) (center n)
  let U := (s.domain ×ˢ (univ : Set Plane)) ×ˢ I n
  have hU : IsOpen U := (s.isOpen_domain.prod isOpen_univ).prod (hI n)
  have hx : (z, v) ∈ U := ⟨⟨hz, mem_univ _⟩, hLI n hv⟩
  have hnativeOpen : IsOpen (s.domain ×ˢ (univ : Set ℝ) ×ˢ I n) :=
    s.isOpen_domain.prod (isOpen_univ.prod (hI n))
  have hBs : ContDiffOn ℝ ∞ (fun y => (d n).forcingMap (nativeArgument g k y)) U :=
    (hB n).comp (nativeArgument_smooth g k).contDiffOn (fun y hy => ⟨hy.1.1, mem_univ _, hy.2⟩)
  have hfs : ContDiffOn ℝ ∞ (fun y => (d n).source (sourceArgument g k y)) U :=
    (hf.smooth n).comp (sourceArgument_smooth g k).contDiffOn (fun y hy => hy.1.1)
  have hGn := s.growth_nonneg n z.1
  have hG := s.one_le_growth n z.1
  have hw := hW n v
  have he := s.epsilon_pos n
  have hlin : ‖nativeLinear P g‖ ≤ K * s.growth n z.1 := by
    apply (norm_nativeLinear_le g).trans
    apply (bandGeometry_argumentCost_le B hh (hband n) (hgap n) (center n)).trans
    rw [← hslow n]
    exact mul_le_mul_of_nonneg_left (s.slow_le_growth n z.1) (zero_le_one.trans hK)
  have hBbound : ∀ i ≤ N,
      ‖iteratedFDeriv ℝ i (fun y => (d n).forcingMap (nativeArgument g k y)) (z, v)‖ ≤
        A * K ^ N * s.growth n z.1 ^ (q + N) := by
    intro i hi
    have hpoint : nativeArgument g k 0 + nativeLinear P g (z, v) ∈
        s.domain ×ˢ (univ : Set ℝ) ×ˢ I n := by
      rw [← nativeArgument_affine]
      exact ⟨hz, mem_univ _, hLI n hv⟩
    have hb := CommonCoverClass.norm_affine_jet_le_on hnativeOpen (hB n)
      (nativeLinear P g) (nativeArgument g k 0) hpoint i
    simp_rw [← nativeArgument_affine] at hb
    have hpow : ‖nativeLinear P g‖ ^ i ≤ K ^ N * s.growth n z.1 ^ N := by
      rw [← mul_pow]
      exact (pow_le_pow_left₀ (norm_nonneg _) hlin i).trans
        (pow_le_pow_right₀ (one_le_mul_of_one_le_of_one_le hK hG) hi)
    calc
      _ ≤ ‖iteratedFDeriv ℝ i (d n).forcingMap (nativeArgument g k (z, v))‖ *
          ‖nativeLinear P g‖ ^ i := hb
      _ ≤ (A * s.growth n z.1 ^ q) * (K ^ N * s.growth n z.1 ^ N) :=
        mul_le_mul (hnative n z.1 hz _ hξ v hv i hi) hpow
          (pow_nonneg (norm_nonneg _) _) (by positivity)
      _ = _ := by rw [pow_add]; ring
  have hb := clm_apply_jet_bound_on hU hBs hfs hx N (by positivity)
    (show 0 ≤ C * s.growth n z.1 ^ p * (s.epsilon n ^ α * Real.sqrt (s.zeta z.1)) * W n v by
        positivity)
    hBbound (fun i hi => hsource n k z hz hξ v hv i hi) j hj
  change ‖iteratedFDeriv ℝ j ((d n).forcingAlong g k) (z, v)‖ ≤ _ at hb
  apply hb.trans_eq
  rw [pow_add]
  ring

end ForcingJetTransport

section NativePathAndSupport

variable {P V H : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
/-- The path used by the source estimate is the manuscript's literal path,
with its actual time coefficient and inverse integer covering. -/
theorem native_source_path (h : ℝ) (n gap : ℕ) (center : Plane) (k : Frequency)
    (z : P × Plane) (v : ℝ) :
    sourceArgument (bandGeometry nativeBasis h n gap center) k (z, v) =
      (z.1, z.2 + (coverPower gap).symm
        ((ChartScales.timeCoefficient h n *
          (v - ((bandGeometry nativeBasis h n gap center).coordinates k z.2).2)) •
            PhysicalGraphBounds.timeDirection)) := by
  exact congrArg (fun Y => (z.1, Y)) (native_band_path h n gap center k z.2 v)

omit [NormedSpace ℝ P] in
/-- The constructed zero-entry solve vanishes where the grouped source has
no transverse support, using its values along every integration time. -/
theorem anchoredSolve_zero_of_grouped_transverse_support
    (d : LinearData P V H) {g : Geometry} {r L : ℝ} (hL : 0 ≤ L)
    (hsep : Separated g r L) (F : Frequency → P × Plane → V)
    (hsource : d.source = grouped F)
    (hsupport : ∀ k, support (F k) ⊆ copyCell g r L k)
    (k : Frequency) (p : P) (Y : Plane) (T : Set ℝ)
    (htransverse : support (F k) ⊆ {z | (g.coordinates k z.2).1 ∈ T})
    (hξ : (g.coordinates k Y).1 ∈ Icc (-r) r) (hξT : (g.coordinates k Y).1 ∉ T)
    (v : ℝ) : d.anchoredSolve g hL k (p, Y) v = 0 := by
  apply d.anchoredSolve_zero_of_source_zero g hL k p Y
  rw [hsource]
  exact grouped_path_zero_of_transverse_support hsep F hsupport k p Y T htransverse hξ hξT

end NativePathAndSupport

end NavierStokes.WaveEnvelopeTransport
