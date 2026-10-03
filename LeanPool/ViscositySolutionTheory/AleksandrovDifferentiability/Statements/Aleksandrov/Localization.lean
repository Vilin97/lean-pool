/-
Copyright (c) 2026 AleksandrovDifferentiability contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/

module

public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Statements.Aleksandrov.Transport
public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Statements.Cube.ClusterDensity

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Localization from source cubes to affine images

This file starts the final source-document localization step. The first lemma separates the
pointwise chain-rule part from the still-remaining measure-identification and countable-cover
arguments: a.e. second-order differentiability of the pullback `z ↦ u (a + r • z)` pushes forward
to a.e. second-order differentiability of `u` with respect to the image measure.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped MeasureTheory

namespace AleksandrovDifferentiability

/-- The affine image `a + r • Q_R` of a source cube. -/
def sourceAffineCubeImage (n : ℕ) (a : SourceCubeSpace n) (r R : ℝ) :
    Set (SourceCubeSpace n) :=
  (fun z : SourceCubeSpace n => a + r • z) '' sourceOpenCube n R

/-- Affine source-cube images are monotone in the source radius. -/
theorem sourceAffineCubeImage_subset_of_le
    {n : ℕ} (a : SourceCubeSpace n) (r : ℝ) {R S : ℝ} (hRS : R ≤ S) :
    sourceAffineCubeImage n a r R ⊆ sourceAffineCubeImage n a r S :=
  Set.image_mono (sourceOpenCube_subset_of_le hRS)

/-- Parameters for affine source cubes whose enlarged `Q_3` image stays inside `Ω`. -/
def SourceAffineCubeCoverIndex (n : ℕ) (Ω : Set (SourceCubeSpace n)) :=
  {p : SourceCubeSpace n × ℝ // 0 < p.2 ∧ sourceAffineCubeImage n p.1 p.2 3 ⊆ Ω}

/-- Parameters for affine source cubes with enough extra room to bound the `Q_3` pullback.

The normalized theorem assumes boundedness on `Q_3`. For an arbitrary finite convex function on
an open set, this boundedness is obtained from continuity on a compact cube sitting strictly
inside the domain. Recording that the larger open image `a + r • Q_4` lies in `Ω` gives that
compact room for the closed `Q_3` cube. -/
def SourceAffineCompactCubeCoverIndex (n : ℕ) (Ω : Set (SourceCubeSpace n)) :=
  {p : SourceCubeSpace n × ℝ // 0 < p.2 ∧ sourceAffineCubeImage n p.1 p.2 4 ⊆ Ω}

/-- Assemble restricted a.e. statements across a countable cover.

This is the measure-theoretic core of the source localization step: after proving an a.e.
statement on each source-cube image in a countable cover, it suffices to restrict from the
countable union back to the target domain. No measurability hypothesis on the cover pieces is
needed, because the statement is phrased directly with restricted measures. -/
theorem ae_restrict_of_subset_iUnion_of_ae_restrict
    {α ι : Type*} [MeasurableSpace α] [Countable ι] {μ : Measure α}
    {Ω : Set α} {U : ι → Set α} {p : α → Prop}
    (hcover : Ω ⊆ ⋃ i, U i)
    (hU : ∀ i, ∀ᵐ x ∂μ.restrict (U i), p x) :
    ∀ᵐ x ∂μ.restrict Ω, p x := by
  have hUnion : ∀ᵐ x ∂μ.restrict (⋃ i, U i), p x :=
    (ae_restrict_iUnion_iff (μ := μ) U p).2 hU
  exact hUnion.filter_mono (ae_mono (Measure.restrict_mono hcover le_rfl))

/-- A scaled source cube of radius `R` sits in a metric ball when the scale is small enough.

This is the elementary geometric estimate behind the source localization step. It uses the
explicit bound `‖z‖ ≤ sqrt n * R` for `z ∈ Q_R`. -/
theorem affine_image_sourceOpenCube_subset_ball
    {n : ℕ} (c : SourceCubeSpace n) {r R ε : ℝ}
    (hr : 0 ≤ r) (hR : 0 ≤ R) (hsmall : (Real.sqrt (n : ℝ) * R) * r < ε) :
    sourceAffineCubeImage n c r R ⊆ Metric.ball c ε := by
  rintro y ⟨z, hz, rfl⟩
  rw [Metric.mem_ball, dist_eq_norm]
  have hz_norm :
      ‖z‖ ≤ Real.sqrt (n : ℝ) * R :=
    norm_le_sqrt_card_mul_of_mem_sourceOpenCube (n := n) (r := R) hR hz
  have hnorm :
      ‖r • z‖ ≤ r * (Real.sqrt (n : ℝ) * R) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr]
    exact mul_le_mul_of_nonneg_left hz_norm hr
  have hlt : ‖r • z‖ < ε :=
    lt_of_le_of_lt hnorm (by simpa [mul_comm] using hsmall)
  simpa using hlt

/-- A scaled source `Q_3` sits in a metric ball when the scale is small enough. -/
theorem affine_image_sourceOpenCube_three_subset_ball
    {n : ℕ} (c : SourceCubeSpace n) {r ε : ℝ}
    (hr : 0 ≤ r) (hsmall : (Real.sqrt (n : ℝ) * 3) * r < ε) :
    sourceAffineCubeImage n c r 3 ⊆ Metric.ball c ε := by
  exact affine_image_sourceOpenCube_subset_ball c hr (by norm_num) hsmall

/-- Pointwise source-cube localization inside an open set, with an arbitrary outer radius.

For every point of an open set and every nonnegative outer source radius `R`, there is a positive
affine scale such that the image of `Q_R` stays inside the open set, while the point itself lies
in the corresponding image of `Q_1`. -/
theorem exists_affine_sourceOpenCube_one_mem_and_outer_subset_of_isOpen
    {n : ℕ} {Ω : Set (SourceCubeSpace n)} (hΩ : IsOpen Ω)
    {x : SourceCubeSpace n} (hx : x ∈ Ω) {R : ℝ} (hR : 0 ≤ R) :
    ∃ r : ℝ, 0 < r ∧
      x ∈ sourceAffineCubeImage n x r 1 ∧
      sourceAffineCubeImage n x r R ⊆ Ω := by
  rcases Metric.isOpen_iff.mp hΩ x hx with ⟨ε, hε, hball⟩
  rcases exists_pos_mul_lt hε (Real.sqrt (n : ℝ) * R) with ⟨r, hrpos, hrsmall⟩
  refine ⟨r, hrpos, ?_, ?_⟩
  · exact ⟨0, zero_mem_sourceOpenCube (n := n) (by norm_num), by simp⟩
  · exact (affine_image_sourceOpenCube_subset_ball
      (n := n) x hrpos.le hR hrsmall).trans hball

/-- Pointwise source-cube localization with outer radius `3`. -/
theorem exists_affine_sourceOpenCube_one_mem_and_three_subset_of_isOpen
    {n : ℕ} {Ω : Set (SourceCubeSpace n)} (hΩ : IsOpen Ω)
    {x : SourceCubeSpace n} (hx : x ∈ Ω) :
    ∃ r : ℝ, 0 < r ∧
      x ∈ sourceAffineCubeImage n x r 1 ∧
      sourceAffineCubeImage n x r 3 ⊆ Ω := by
  exact exists_affine_sourceOpenCube_one_mem_and_outer_subset_of_isOpen
    hΩ hx (R := 3) (by norm_num)

/-- Pointwise source-cube localization with outer radius `4`.

This is the variant used for open-domain localization, because `Q_4` inside `Ω` leaves compact
room for the closed `Q_3` cube used to prove the boundedness hypothesis of the normalized
source-cube theorem. -/
theorem exists_affine_sourceOpenCube_one_mem_and_four_subset_of_isOpen
    {n : ℕ} {Ω : Set (SourceCubeSpace n)} (hΩ : IsOpen Ω)
    {x : SourceCubeSpace n} (hx : x ∈ Ω) :
    ∃ r : ℝ, 0 < r ∧
      x ∈ sourceAffineCubeImage n x r 1 ∧
      sourceAffineCubeImage n x r 4 ⊆ Ω := by
  exact exists_affine_sourceOpenCube_one_mem_and_outer_subset_of_isOpen
    hΩ hx (R := 4) (by norm_num)

/-- Affine images of source open cubes are open when the scale is nonzero. -/
theorem isOpen_sourceAffineCubeImage
    {n : ℕ} (a : SourceCubeSpace n) {r R : ℝ} (hr : r ≠ 0) :
    IsOpen (sourceAffineCubeImage n a r R) := by
  have hsmul :
      IsOpen ((fun z : SourceCubeSpace n => r • z) '' sourceOpenCube n R) :=
    isOpenMap_smul₀ hr _ (isOpen_sourceOpenCube (n := n) R)
  have hadd :
      IsOpen ((fun y : SourceCubeSpace n => a + y) ''
        ((fun z : SourceCubeSpace n => r • z) '' sourceOpenCube n R)) :=
    isOpenMap_add_left a _ hsmul
  simpa [sourceAffineCubeImage, Set.image_image, Function.comp_def] using hadd

/-- Countable Lindelöf subcover by affine source cubes whose enlarged cubes stay in an open set.

The index type still records the actual centers and scales. This is the countability refinement
of `exists_affine_sourceOpenCube_one_mem_and_three_subset_of_isOpen`; a later theorem can apply
the one-cube a.e. result on each selected index and assemble them with
`secondOrderDifferentiableAEOn_of_subset_iUnion`. -/
theorem exists_countable_sourceAffineCubeCoverIndex_of_isOpen
    {n : ℕ} {Ω : Set (SourceCubeSpace n)} (hΩ : IsOpen Ω) :
    ∃ I : Set (SourceAffineCubeCoverIndex n Ω), I.Countable ∧
      Ω ⊆ ⋃ i ∈ I, sourceAffineCubeImage n i.1.1 i.1.2 1 := by
  let U : SourceAffineCubeCoverIndex n Ω → Set (SourceCubeSpace n) :=
    fun i => sourceAffineCubeImage n i.1.1 i.1.2 1
  have hUopen : ∀ i, IsOpen (U i) := by
    intro i
    exact isOpen_sourceAffineCubeImage i.1.1 (ne_of_gt i.2.1)
  have hcover : Ω ⊆ ⋃ i, U i := by
    intro x hx
    rcases exists_affine_sourceOpenCube_one_mem_and_three_subset_of_isOpen hΩ hx with
      ⟨r, hrpos, hxone, hthree⟩
    exact Set.mem_iUnion.2 ⟨⟨(x, r), hrpos, hthree⟩, hxone⟩
  rcases (HereditarilyLindelofSpace.isLindelof Ω).elim_countable_subcover
      U hUopen hcover with
    ⟨I, hIcount, hIcover⟩
  exact ⟨I, hIcount, hIcover⟩

/-- Countable Lindelöf subcover by compactly contained affine source cubes.

The selected `Q_1` images cover `Ω`, while each selected index records the stronger inclusion
`a + r • Q_4 ⊆ Ω`. This is the localization cover used for the final open-domain theorem,
because it leaves room to bound the pullback on `Q_3`. -/
theorem exists_countable_sourceAffineCompactCubeCoverIndex_of_isOpen
    {n : ℕ} {Ω : Set (SourceCubeSpace n)} (hΩ : IsOpen Ω) :
    ∃ I : Set (SourceAffineCompactCubeCoverIndex n Ω), I.Countable ∧
      Ω ⊆ ⋃ i ∈ I, sourceAffineCubeImage n i.1.1 i.1.2 1 := by
  let U : SourceAffineCompactCubeCoverIndex n Ω → Set (SourceCubeSpace n) :=
    fun i => sourceAffineCubeImage n i.1.1 i.1.2 1
  have hUopen : ∀ i, IsOpen (U i) := by
    intro i
    exact isOpen_sourceAffineCubeImage i.1.1 (ne_of_gt i.2.1)
  have hcover : Ω ⊆ ⋃ i, U i := by
    intro x hx
    rcases exists_affine_sourceOpenCube_one_mem_and_four_subset_of_isOpen hΩ hx with
      ⟨r, hrpos, hxone, hfour⟩
    exact Set.mem_iUnion.2 ⟨⟨(x, r), hrpos, hfour⟩, hxone⟩
  rcases (HereditarilyLindelofSpace.isLindelof Ω).elim_countable_subcover
      U hUopen hcover with
    ⟨I, hIcount, hIcover⟩
  exact ⟨I, hIcount, hIcover⟩

/-- Convexity inherited by the affine pullback on a source cube. -/
theorem ConvexOn.comp_sourceAffineCube
    {n : ℕ} {Ω : Set (SourceCubeSpace n)} {u : SourceCubeSpace n → ℝ}
    (hu : ConvexOn ℝ Ω u) {a : SourceCubeSpace n} {r R : ℝ}
    (himage : sourceAffineCubeImage n a r R ⊆ Ω) :
    ConvexOn ℝ (sourceOpenCube n R) (fun y : SourceCubeSpace n => u (a + r • y)) := by
  refine ⟨convex_sourceOpenCube R, ?_⟩
  intro x hx y hy α β hα hβ hsum
  have hxΩ : a + r • x ∈ Ω := himage ⟨x, hx, rfl⟩
  have hyΩ : a + r • y ∈ Ω := himage ⟨y, hy, rfl⟩
  have hcombo :
      a + r • (α • x + β • y) =
        α • (a + r • x) + β • (a + r • y) := by
    ext i
    have hai : a i = α * a i + β * a i := by
      calc
        a i = (α + β) * a i := by rw [hsum]; ring
        _ = α * a i + β * a i := by ring
    simp only [smul_add, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    nth_rewrite 1 [hai]
    ring
  calc
    u (a + r • (α • x + β • y))
        = u (α • (a + r • x) + β • (a + r • y)) := by rw [hcombo]
    _ ≤ α • u (a + r • x) + β • u (a + r • y) :=
        hu.2 hxΩ hyΩ hα hβ hsum

/-- Convexity inherited by the affine pullback on `Q_3` from a compact-room index. -/
theorem SourceAffineCompactCubeCoverIndex.convexOn_pullback_sourceOpenCube_three
    {n : ℕ} {Ω : Set (SourceCubeSpace n)} {u : SourceCubeSpace n → ℝ}
    (i : SourceAffineCompactCubeCoverIndex n Ω) (hu : ConvexOn ℝ Ω u) :
    ConvexOn ℝ (sourceOpenCube n 3)
      (fun y : SourceCubeSpace n => u (i.1.1 + i.1.2 • y)) :=
  ConvexOn.comp_sourceAffineCube hu
    ((sourceAffineCubeImage_subset_of_le i.1.1 i.1.2 (by norm_num)).trans i.2.2)

/-- The closed `Q_3` pullback of a compact-room affine cube stays inside the open domain. -/
theorem SourceAffineCompactCubeCoverIndex.mapsTo_closedCube_three
    {n : ℕ} {Ω : Set (SourceCubeSpace n)} (i : SourceAffineCompactCubeCoverIndex n Ω) :
    Set.MapsTo (fun y : SourceCubeSpace n => i.1.1 + i.1.2 • y)
      (sourceClosedCube n 3) Ω := by
  intro y hy
  exact i.2.2
    ⟨y, sourceClosedCube_subset_sourceOpenCube_of_lt (n := n) (r := 3) (R := 4)
      (by norm_num) hy, rfl⟩

/-- Continuity inherited on the compact closed `Q_3` from convexity on the open domain. -/
theorem SourceAffineCompactCubeCoverIndex.continuousOn_pullback_sourceClosedCube_three
    {n : ℕ} {Ω : Set (SourceCubeSpace n)} {u : SourceCubeSpace n → ℝ}
    (i : SourceAffineCompactCubeCoverIndex n Ω) (hΩ : IsOpen Ω)
    (hu : ConvexOn ℝ Ω u) :
    ContinuousOn (fun y : SourceCubeSpace n => u (i.1.1 + i.1.2 • y))
      (sourceClosedCube n 3) := by
  have hc : Continuous (fun y : SourceCubeSpace n => i.1.1 + i.1.2 • y) := by fun_prop
  exact (hu.continuousOn hΩ).comp' hc.continuousOn i.mapsTo_closedCube_three

/-- Boundedness on `Q_3` inherited from compact containment in an open convex domain. -/
theorem SourceAffineCompactCubeCoverIndex.boundedOn_pullback_sourceOpenCube_three
    {n : ℕ} {Ω : Set (SourceCubeSpace n)} {u : SourceCubeSpace n → ℝ}
    (i : SourceAffineCompactCubeCoverIndex n Ω) (hΩ : IsOpen Ω)
    (hu : ConvexOn ℝ Ω u) :
    BoundedOn (sourceOpenCube n 3)
      (fun y : SourceCubeSpace n => u (i.1.1 + i.1.2 • y)) :=
  BoundedOn.sourceOpenCube_of_continuousOn_sourceClosedCube (n := n) (r := 3)
    (by norm_num) (i.continuousOn_pullback_sourceClosedCube_three hΩ hu)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E]

/-- Countable-cover assembly specialized to second-order differentiability. -/
theorem secondOrderDifferentiableAEOn_of_subset_iUnion
    {ι : Type*} [Countable ι] {μ : Measure E}
    {Ω : Set E} {U : ι → Set E} {u : E → ℝ}
    (hcover : Ω ⊆ ⋃ i, U i)
    (hU : ∀ i, SecondOrderDifferentiableAEOn μ (U i) u) :
    SecondOrderDifferentiableAEOn μ Ω u :=
  ae_restrict_of_subset_iUnion_of_ae_restrict hcover hU

/-- Null-bad-set version of `secondOrderDifferentiableAEOn_of_subset_iUnion`. -/
theorem measure_secondOrderBadSetOn_eq_zero_of_subset_iUnion
    {ι : Type*} [Countable ι] {μ : Measure E}
    {Ω : Set E} {U : ι → Set E} {u : E → ℝ}
    (hΩ : MeasurableSet Ω) (hcover : Ω ⊆ ⋃ i, U i)
    (hU : ∀ i, SecondOrderDifferentiableAEOn μ (U i) u) :
    μ (secondOrderBadSetOn Ω u) = 0 :=
  (secondOrderDifferentiableAEOn_iff_measure_secondOrderBadSetOn_eq_zero hΩ).mp
    (secondOrderDifferentiableAEOn_of_subset_iUnion hcover hU)

variable [BorelSpace E]

/-- Lebesgue measure is scaled by a nonzero scalar dilation and unchanged by translation. -/
theorem map_volume_add_smul
    [FiniteDimensional ℝ E] (a : E) {r : ℝ} (hr : r ≠ 0) :
    Measure.map (fun z : E => a + r • z) volume =
      ENNReal.ofReal (abs (r ^ Module.finrank ℝ E)⁻¹) • (volume : Measure E) := by
  calc
    Measure.map (fun z : E => a + r • z) volume =
        Measure.map (fun y : E => a + y)
          (Measure.map (fun z : E => r • z) volume) := by
      rw [Measure.map_map]
      · rfl
      · exact (measurableEmbedding_addLeft a).measurable
      · exact measurable_const_smul r
    _ = Measure.map (fun y : E => a + y)
          (ENNReal.ofReal (abs (r ^ Module.finrank ℝ E)⁻¹) • (volume : Measure E)) := by
      rw [Measure.map_addHaar_smul (μ := (volume : Measure E)) hr]
    _ = ENNReal.ofReal (abs (r ^ Module.finrank ℝ E)⁻¹) •
          Measure.map (fun y : E => a + y) (volume : Measure E) := by
      rw [Measure.map_smul]
      exact (measurable_const_add a).aemeasurable
    _ = ENNReal.ofReal (abs (r ^ Module.finrank ℝ E)⁻¹) • (volume : Measure E) := by
      rw [Measure.IsAddLeftInvariant.map_add_left_eq_self]

/-- Restricted version of `map_volume_add_smul` on an affine image. -/
theorem restrict_map_volume_add_smul_image
    [FiniteDimensional ℝ E] (a : E) {r : ℝ} (hr : r ≠ 0) (s : Set E) :
    (Measure.map (fun z : E => a + r • z) volume).restrict
        ((fun z : E => a + r • z) '' s) =
      ENNReal.ofReal (abs (r ^ Module.finrank ℝ E)⁻¹) •
        (volume : Measure E).restrict ((fun z : E => a + r • z) '' s) := by
  rw [map_volume_add_smul (E := E) a hr, Measure.restrict_smul]

/-- Push a.e. second-order differentiability through a nonzero scalar dilation and translation.

This is the measure-level form of the source localization map `z ↦ a + r z`. It does not yet
identify the pushforward measure with Lebesgue measure on the affine image of the source cube;
that is the next measure-transport component of the open-domain localization proof. -/
theorem ae_map_add_smul_secondOrderDifferentiableAt
    {u : E → ℝ} {a : E} {r : ℝ} (hr : r ≠ 0) {μ : Measure E}
    (h : ∀ᵐ z ∂μ, SecondOrderDifferentiableAt (fun y : E => u (a + r • y)) z) :
    ∀ᵐ x ∂(μ.map fun z : E => a + r • z), SecondOrderDifferentiableAt u x := by
  have hsmul : MeasurableEmbedding (fun z : E => r • z) :=
    measurableEmbedding_const_smul₀ hr
  have hadd : MeasurableEmbedding (fun z : E => a + z) :=
    measurableEmbedding_addLeft a
  have haffine : MeasurableEmbedding (fun z : E => a + r • z) := by
    simpa [Function.comp_def] using hadd.comp hsmul
  rw [haffine.ae_map_iff]
  exact h.mono fun z hz => SecondOrderDifferentiableAt.of_comp_add_smul hr hz

/-- Restricted-image version of `ae_map_add_smul_secondOrderDifferentiableAt`.

If the pullback is second-order differentiable a.e. on `s`, then `u` is second-order
differentiable a.e. on the affine image of `s`, measured using the pushforward of `μ` restricted
to that image. -/
theorem ae_restrict_image_add_smul_secondOrderDifferentiableAt
    {u : E → ℝ} {a : E} {r : ℝ} (hr : r ≠ 0) {μ : Measure E} {s : Set E}
    (h :
      ∀ᵐ z ∂(μ.restrict s),
        SecondOrderDifferentiableAt (fun y : E => u (a + r • y)) z) :
    ∀ᵐ x ∂((μ.map fun z : E => a + r • z).restrict
        ((fun z : E => a + r • z) '' s)),
      SecondOrderDifferentiableAt u x := by
  let φ : E → E := fun z : E => a + r • z
  have hsmul : MeasurableEmbedding (fun z : E => r • z) :=
    measurableEmbedding_const_smul₀ hr
  have hadd : MeasurableEmbedding (fun z : E => a + z) :=
    measurableEmbedding_addLeft a
  have hφ : MeasurableEmbedding φ := by
    simpa [φ, Function.comp_def] using hadd.comp hsmul
  have hmap :
      ∀ᵐ x ∂((μ.restrict s).map φ), SecondOrderDifferentiableAt u x := by
    simpa [φ] using
      (ae_map_add_smul_secondOrderDifferentiableAt (E := E) (u := u) (a := a)
        (r := r) hr (μ := μ.restrict s) h)
  have hpreimage : φ ⁻¹' (φ '' s) = s := by
    ext z
    constructor
    · rintro ⟨w, hw, hzw⟩
      have hz_eq_w : z = w := hφ.injective hzw.symm
      simpa [hz_eq_w] using hw
    · intro hz
      exact ⟨z, hz, rfl⟩
  have hmeasure : (μ.restrict s).map φ = (μ.map φ).restrict (φ '' s) := by
    rw [hφ.restrict_map μ (φ '' s), hpreimage]
  simpa [φ, hmeasure] using hmap

/-- One-cube affine-image localization of the normalized source-cube theorem.

For a fixed affine map `z ↦ a + r • z`, if the pullback satisfies the boundedness and convexity
hypotheses of the normalized theorem on `Q_3`, then `u` is second-order differentiable a.e. on the
affine image of `Q_1`, measured by the restricted pushforward of Lebesgue measure. -/
theorem ae_restrict_affineImage_sourceOpenCube_secondOrderDifferentiableAt
    {n : ℕ} (hn : 1 ≤ n) {u : SourceCubeSpace n → ℝ}
    {a : SourceCubeSpace n} {r : ℝ} (hr : r ≠ 0)
    (hbounded :
      BoundedOn (sourceOpenCube n 3) (fun y : SourceCubeSpace n => u (a + r • y)))
    (hconvex :
      ConvexOn ℝ (sourceOpenCube n 3) (fun y : SourceCubeSpace n => u (a + r • y))) :
    ∀ᵐ x ∂((volume.map fun z : SourceCubeSpace n => a + r • z).restrict
        ((fun z : SourceCubeSpace n => a + r • z) '' sourceOpenCube n 1)),
      SecondOrderDifferentiableAt u x :=
  ae_restrict_image_add_smul_secondOrderDifferentiableAt
    (E := SourceCubeSpace n) (u := u) (a := a) (r := r) hr
    (μ := volume) (s := sourceOpenCube n 1)
    (ae_restrict_sourceOpenCube_secondOrderDifferentiableAt hn hbounded hconvex)

/-- One-cube affine-image localization with Lebesgue measure restricted to the affine image. -/
theorem ae_volume_restrict_affineImage_sourceOpenCube_secondOrderDifferentiableAt
    {n : ℕ} (hn : 1 ≤ n) {u : SourceCubeSpace n → ℝ}
    {a : SourceCubeSpace n} {r : ℝ} (hr : r ≠ 0)
    (hbounded :
      BoundedOn (sourceOpenCube n 3) (fun y : SourceCubeSpace n => u (a + r • y)))
    (hconvex :
      ConvexOn ℝ (sourceOpenCube n 3) (fun y : SourceCubeSpace n => u (a + r • y))) :
    ∀ᵐ x ∂((volume : Measure (SourceCubeSpace n)).restrict
        ((fun z : SourceCubeSpace n => a + r • z) '' sourceOpenCube n 1)),
      SecondOrderDifferentiableAt u x := by
  let c : ENNReal :=
    ENNReal.ofReal (abs (r ^ Module.finrank ℝ (SourceCubeSpace n))⁻¹)
  have hc : c ≠ 0 := by
    rw [ENNReal.ofReal_ne_zero_iff]
    exact abs_pos.mpr (inv_ne_zero (pow_ne_zero _ hr))
  have hpush :
      ∀ᵐ x ∂((volume.map fun z : SourceCubeSpace n => a + r • z).restrict
          ((fun z : SourceCubeSpace n => a + r • z) '' sourceOpenCube n 1)),
        SecondOrderDifferentiableAt u x :=
    ae_restrict_affineImage_sourceOpenCube_secondOrderDifferentiableAt
      hn hr hbounded hconvex
  have hmeasure :
      (volume.map fun z : SourceCubeSpace n => a + r • z).restrict
          ((fun z : SourceCubeSpace n => a + r • z) '' sourceOpenCube n 1) =
        c • (volume : Measure (SourceCubeSpace n)).restrict
          ((fun z : SourceCubeSpace n => a + r • z) '' sourceOpenCube n 1) := by
    simpa [c] using
      (restrict_map_volume_add_smul_image
        (E := SourceCubeSpace n) a hr (sourceOpenCube n 1))
  have hscaled :
      ∀ᵐ x ∂(c • (volume : Measure (SourceCubeSpace n)).restrict
          ((fun z : SourceCubeSpace n => a + r • z) '' sourceOpenCube n 1)),
        SecondOrderDifferentiableAt u x := by
    simpa [hmeasure] using hpush
  simpa [ae_iff, hc] using hscaled

/-- One selected compact-room affine cube satisfies the Lebesgue-restricted a.e. conclusion. -/
theorem SourceAffineCompactCubeCoverIndex.ae_volume_restrict_image_secondOrderDifferentiableAt
    {n : ℕ} (hn : 1 ≤ n) {Ω : Set (SourceCubeSpace n)}
    {u : SourceCubeSpace n → ℝ} (i : SourceAffineCompactCubeCoverIndex n Ω)
    (hΩ : IsOpen Ω) (hu : ConvexOn ℝ Ω u) :
    ∀ᵐ x ∂((volume : Measure (SourceCubeSpace n)).restrict
        (sourceAffineCubeImage n i.1.1 i.1.2 1)),
      SecondOrderDifferentiableAt u x := by
  simpa [sourceAffineCubeImage] using
    ae_volume_restrict_affineImage_sourceOpenCube_secondOrderDifferentiableAt
      (n := n) hn (u := u) (a := i.1.1) (r := i.1.2) (ne_of_gt i.2.1)
      (i.boundedOn_pullback_sourceOpenCube_three hΩ hu)
      (i.convexOn_pullback_sourceOpenCube_three hu)

/-- Open-domain localization in source-cube coordinates.

This is the source's cube-to-open-domain localization step in the positive-dimensional source
coordinate model: cover the open domain by countably many compact-room affine `Q_1` images,
apply the normalized theorem on each image, and assemble the restricted a.e. conclusions. -/
theorem ae_volume_restrict_open_secondOrderDifferentiableAt_sourceCubeSpace
    {n : ℕ} (hn : 1 ≤ n) {Ω : Set (SourceCubeSpace n)}
    {u : SourceCubeSpace n → ℝ} (hΩ : IsOpen Ω) (hu : ConvexOn ℝ Ω u) :
    ∀ᵐ x ∂((volume : Measure (SourceCubeSpace n)).restrict Ω),
      SecondOrderDifferentiableAt u x := by
  rcases exists_countable_sourceAffineCompactCubeCoverIndex_of_isOpen
      (n := n) (Ω := Ω) hΩ with
    ⟨I, hIcount, hcover⟩
  let U : I → Set (SourceCubeSpace n) :=
    fun i => sourceAffineCubeImage n i.1.1.1 i.1.1.2 1
  have : Countable I := hIcount.to_subtype
  refine ae_restrict_of_subset_iUnion_of_ae_restrict
    (μ := (volume : Measure (SourceCubeSpace n))) (Ω := Ω) (U := U)
    (p := fun x => SecondOrderDifferentiableAt u x) ?_ ?_
  · intro x hx
    have hxcover := hcover hx
    simp only [Set.mem_iUnion] at hxcover ⊢
    rcases hxcover with ⟨i, hxcover_i⟩
    rcases hxcover_i with ⟨hiI, hxi⟩
    exact ⟨⟨i, hiI⟩, hxi⟩
  · intro i
    exact i.1.ae_volume_restrict_image_secondOrderDifferentiableAt hn hΩ hu

/-- Positive-dimensional source-coordinate version of the convex Aleksandrov a.e. statement. -/
theorem convexAleksandrovAEStatement_sourceCubeSpace_of_one_le
    {n : ℕ} (hn : 1 ≤ n) (Ω : Set (SourceCubeSpace n)) (u : SourceCubeSpace n → ℝ) :
    ConvexAleksandrovAEStatement (SourceCubeSpace n) Ω u := by
  intro hΩ hu
  exact ae_volume_restrict_open_secondOrderDifferentiableAt_sourceCubeSpace hn hΩ hu

/-- Full finite-dimensional convex Aleksandrov a.e. statement, obtained from the source-coordinate
localization theorem by an orthonormal-coordinate linear isometry equivalence. -/
theorem convexAleksandrovAEStatement_finiteDimensional
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) :
    ConvexAleksandrovAEStatement E Ω u := by
  by_cases hzero : Module.finrank ℝ E = 0
  · intro _hΩ _hu
    exact Filter.Eventually.of_forall fun x =>
      secondOrderDifferentiableAt_of_finrank_eq_zero hzero u x
  · have hpos : 1 ≤ Module.finrank ℝ E := Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero hzero)
    let e : E ≃ₗᵢ[ℝ] SourceCubeSpace (Module.finrank ℝ E) :=
      (stdOrthonormalBasis ℝ E).repr
    exact
      ConvexAleksandrovAEStatement.of_image_linearIsometryEquiv (e := e)
        (convexAleksandrovAEStatement_sourceCubeSpace_of_one_le
          (n := Module.finrank ℝ E) hpos (e '' Ω) (u ∘ e.symm))

end AleksandrovDifferentiability
