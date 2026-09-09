/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.OffplaneCorrectionExtensions
public import LeanPool.NavierStokesAndEuler.NavierStokes.AnnularEndpoint
public import LeanPool.NavierStokesAndEuler.NavierStokes.LocalPhysicalCopyBounds

@[expose] public section

/-!
# Endpoint extensions for locally constructed diagonal stages

The raw stages only need endpoint models where the physical scale is below
their construction threshold. Farther away, the same cutoffs give a common
zero neighborhood. On the central plane, a uniform outer annulus removes
every positive stage at once and the initial cutoff is identically one.

These results concern the full actual sum, including stage zero. They do
not assume that its away-from-origin extensions have already been built.
-/

noncomputable section

namespace NavierStokes.MixedDiagonalExtensions

open Set Filter ProblemStatement
open JointResidualLimits (OneSidedExtension AwayExtensions)
open scoped Topology ContDiff

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Transfer a genuine local extension using equality on a past
neighborhood; no equality on the future side is needed. -/
theorem extension_of_eventuallyEq {f g : SpaceTime → V} {x : Space}
    (hfg : f =ᶠ[𝓝[SpacetimeEndpoint.openPast 1] (1, x)] g)
    (e : OneSidedExtension g x) : Nonempty (OneSidedExtension f x) := by
  obtain ⟨U, hU, hxU, he⟩ := mem_nhdsWithin.mp hfg
  refine ⟨{ value := e.value
            domain := e.domain ∩ U
            isOpen := e.isOpen.inter hU
            mem := ⟨e.mem, hxU⟩
            smooth := e.smooth.mono inter_subset_left
            agrees := ?_ }⟩
  intro w hw
  exact (e.agrees ⟨hw.1.1, hw.2⟩).trans (he ⟨hw.1.2, hw.2⟩).symm

theorem extension_of_eventually_zero {f : SpaceTime → V} {x : Space}
    (hf : f =ᶠ[𝓝[SpacetimeEndpoint.openPast 1] (1, x)] fun _ => 0) :
    Nonempty (OneSidedExtension f x) := by
  obtain ⟨U, hU, hxU, he⟩ := mem_nhdsWithin.mp hf
  exact ⟨AnnularEndpoint.zeroExtension hU hxU he⟩

/-- At a nonzero axial coordinate the actual implicit scale has the
positive limit used by the continued finite-stage models. -/
theorem physicalQ_tendsto_endpoint {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {x : Space} (hx : x 2 ≠ 0) :
    Tendsto (PhysicalWaveSum.physicalQ h)
      (𝓝[SpacetimeEndpoint.openPast 1] (1, x))
      (𝓝 (EndpointCoordinates.endpointRoot (2 * h) (x 2))) := by
  have hc := (EndpointCoordinates.cartesianExtension_smoothAt hh hh1
    (EndpointCoordinates.cartesian_endpoint_mem hh hh1 hx)).fst.continuousAt
  have he : (fun w => (EndpointCoordinates.cartesianExtension h w).1) =ᶠ[
      𝓝[SpacetimeEndpoint.openPast 1] (1, x)] PhysicalWaveSum.physicalQ h := by
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact OffplaneCorrectionExtensions.physicalQExtension_eq hh hh1 hw.1
  have ht := (hc.tendsto.mono_left nhdsWithin_le_nhds).congr' he
  simpa only [EndpointCoordinates.cartesianExtension_endpoint hh hh1 hx] using ht

/-- Above the support of the first cutoff, monotonicity kills every
stage on one common past neighborhood, regardless of raw totalizations. -/
theorem sum_eventually_zero_of_scale_large {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {a : ℕ → ℝ} (ha0 : 0 < a 0) (ham : ∀ j, a 0 ≤ a j)
    (F : ℕ → SpaceTime → V) {x : Space} (hx : x 2 ≠ 0)
    (hlarge : 1 / a 0 < EndpointCoordinates.endpointRoot (2 * h) (x 2)) :
    SolenoidalDiagonal.potentialSum a (PhysicalWaveSum.physicalQ h) F =ᶠ[
      𝓝[SpacetimeEndpoint.openPast 1] (1, x)] fun _ => 0 := by
  filter_upwards [(physicalQ_tendsto_endpoint hh hh1 hx).eventually
    (lt_mem_nhds hlarge)] with w hw
  have hz (j : ℕ) : SolenoidalDiagonal.cutStage a (PhysicalWaveSum.physicalQ h) F j w = 0 := by
    have haj := ha0.trans_le (ham j)
    have hcut := SmoothCutoffs.scaledCutoff_zero_of_inv_le haj
      ((one_div_le_one_div_of_le ha0 (ham j)).trans hw.le)
    simp only [SolenoidalDiagonal.cutStage, hcut, zero_smul]
  simp only [SolenoidalDiagonal.potentialSum, hz, tsum_zero]

/-- Only raw endpoint models strictly below `qbig` are required. The
strict support gap at the initial cutoff covers the other branch. -/
theorem offplane_extension_local {h qbig : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {a : ℕ → ℝ} (hat : Tendsto a atTop atTop)
    (ha0 : 0 < a 0) (ham : ∀ j, a 0 ≤ a j) (hgap : 1 / a 0 < qbig)
    {F : ℕ → SpaceTime → V} {x : Space} (hx : x 2 ≠ 0)
    (he : EndpointCoordinates.endpointRoot (2 * h) (x 2) < qbig →
      ∀ j, Nonempty (OneSidedExtension (F j) x)) :
    Nonempty (OneSidedExtension
      (SolenoidalDiagonal.potentialSum a (PhysicalWaveSum.physicalQ h) F) x) := by
  by_cases hsmall : EndpointCoordinates.endpointRoot (2 * h) (x 2) < qbig
  · exact OffplaneCorrectionExtensions.diagonal_extension hh hh1 hat hx (he hsmall)
  · exact extension_of_eventually_zero
      (sum_eventually_zero_of_scale_large hh hh1 ha0 ham F hx
        (hgap.trans_le (le_of_not_gt hsmall)))

/-- Uniform outer support is needed only where the raw stage is used.
The constant is shared by all positive stages in the central-plane theorem. -/
def SublevelShrinkingSupport (h C qbig : ℝ) (f : SpaceTime → V) : Prop :=
  ∀ w, w.1 < 1 → PhysicalWaveSum.physicalQ h w < qbig → f w ≠ 0 →
    AnnularEndpoint.radius w ≤ AnnularEndpoint.outerRadius h C w

omit [NormedSpace ℝ V] in
theorem SublevelShrinkingSupport.of_global {h C qbig : ℝ} {f : SpaceTime → V}
    (hf : AnnularEndpoint.ShrinkingSupport h C f) :
    SublevelShrinkingSupport h C qbig f := fun w ht _ hn => hf w ht hn

omit [NormedSpace ℝ V] in
theorem SublevelShrinkingSupport.eventually_zero {h C qbig : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (hqbig : 0 < qbig) {f : SpaceTime → V}
    (hf : SublevelShrinkingSupport h C qbig f) {x : Space}
    (hx : x ≠ 0) (hz : x 2 = 0) :
    f =ᶠ[𝓝[SpacetimeEndpoint.openPast 1] (1, x)] fun _ => 0 := by
  obtain ⟨U, hU, hxU, hsep⟩ := AnnularEndpoint.exists_separating_neighborhood hh hh1 C hx hz
  have hq := AnnularEndpoint.physicalQ_tendsto_zero hh hh1 hz
  filter_upwards [nhdsWithin_le_nhds (hU.mem_nhds hxU), self_mem_nhdsWithin,
    hq.eventually (gt_mem_nhds hqbig)] with w hw ht hsmall
  by_contra hn
  exact (not_lt_of_ge (hf w ht.1 hsmall hn)) (hsep w hw ht.1)

/-- A finite initialization may be kept inside stage zero. Its supported
change leaves the original anchored base extension unchanged locally. -/
theorem initial_add_extension {h C qbig : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (hqbig : 0 < qbig)
    {base delta : SpaceTime → V} (hd : SublevelShrinkingSupport h C qbig delta)
    {x : Space} (hx : x ≠ 0) (hz : x 2 = 0) (eb : OneSidedExtension base x) :
    Nonempty (OneSidedExtension (fun w => base w + delta w) x) := by
  apply extension_of_eventuallyEq (g := base) ?_ eb
  filter_upwards [hd.eventually_zero hh hh1 hqbig hx hz] with w hw
  simp only [hw, add_zero]

/-- The outer support of an actual copy-and-label sum follows from its
primitive geometric data; no global raw smoothness is required. -/
theorem localCopy_sum_support {H gap : ℕ} {K : Type*}
    {f : PhysicalCopyBounds.CopyFamily H K} {a b h r0 Z : ℝ}
    (hf : LocalPhysicalCopyBounds.SupportData f a b h r0 Z gap) :
    AnnularEndpoint.ShrinkingSupport h (2 * b * Real.sqrt 2) (f.sum a h r0) := by
  apply AnnularEndpoint.shrinkingSupport_of_normalized_annulus
  intro w ht hn
  obtain ⟨I, k, hk⟩ := f.sum_nonzero_term hn
  have hamp := PhysicalWaveSum.globalWave_ne_zero_amp hk
  have hm := PhysicalWaveSum.physicalMask_support_subset _ _ (hf.mask_support k I w ht hamp)
  exact ⟨I.1.val.1, (hf.geometry_support k I w hamp).1,
    (PhysicalWaveSum.labelRegion_active_relation hm).2⟩

theorem localCopy_vector_support {H gap : ℕ} {K : Type*}
    {f : Fin 3 → PhysicalCopyBounds.CopyFamily H K} {a b h r0 Z : ℝ}
    (hf : ∀ i, LocalPhysicalCopyBounds.SupportData (f i) a b h r0 Z gap) :
    AnnularEndpoint.ShrinkingSupport h (2 * b * Real.sqrt 2)
      (PhysicalCopyBounds.vectorSum f a h r0) := by
  apply AnnularEndpoint.ShrinkingSupport.finset_sum
  intro i _
  exact (localCopy_sum_support (hf i)).map_zero
    (fun _ z => PhysicalWaveSum.realCoordinate i z) (by intro; simp)

/-- At a nonzero point of the central plane, every positive stage
vanishes together and stage zero is retained without its cutoff. -/
theorem sum_eventually_eq_initial {h C qbig : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (hqbig : 0 < qbig)
    (a : ℕ → ℝ) {F : ℕ → SpaceTime → V}
    (hs : ∀ j, j ≠ 0 → SublevelShrinkingSupport h C qbig (F j))
    {x : Space} (hx : x ≠ 0) (hz : x 2 = 0) :
    SolenoidalDiagonal.potentialSum a (PhysicalWaveSum.physicalQ h) F =ᶠ[
      𝓝[SpacetimeEndpoint.openPast 1] (1, x)] F 0 := by
  have hq := AnnularEndpoint.physicalQ_tendsto_zero hh hh1 hz
  obtain ⟨U, hU, hxU, hsep⟩ := AnnularEndpoint.exists_separating_neighborhood hh hh1 C hx hz
  have hcut := (SmoothCutoffs.scaledCutoff_eventually_one_at_zero (a 0)).comp_tendsto hq
  filter_upwards [nhdsWithin_le_nhds (hU.mem_nhds hxU), self_mem_nhdsWithin,
    hq.eventually (gt_mem_nhds hqbig), hcut] with w hw ht hsmall hc
  have hzero (j : ℕ) (hj : j ≠ 0) : F j w = 0 := by
    by_contra hn
    exact (not_lt_of_ge (hs j hj w ht.1 hsmall hn)) (hsep w hw ht.1)
  have he : SolenoidalDiagonal.potentialSum a (PhysicalWaveSum.physicalQ h) F w =
      SolenoidalDiagonal.cutStage a (PhysicalWaveSum.physicalQ h) F 0 w := by
    apply tsum_eq_single 0
    intro j hj
    simp only [SolenoidalDiagonal.cutStage, hzero j hj, smul_zero]
  rw [he]
  change SmoothCutoffs.scaledCutoff (a 0) (PhysicalWaveSum.physicalQ h w) • F 0 w = F 0 w
  change SmoothCutoffs.scaledCutoff (a 0) (PhysicalWaveSum.physicalQ h w) = 1 at hc
  rw [hc, one_smul]

theorem central_extension_local {h C qbig : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (hqbig : 0 < qbig)
    (a : ℕ → ℝ) {F : ℕ → SpaceTime → V}
    (hs : ∀ j, j ≠ 0 → SublevelShrinkingSupport h C qbig (F j))
    {x : Space} (hx : x ≠ 0) (hz : x 2 = 0)
    (e0 : OneSidedExtension (F 0) x) :
    Nonempty (OneSidedExtension
      (SolenoidalDiagonal.potentialSum a (PhysicalWaveSum.physicalQ h) F) x) :=
  extension_of_eventuallyEq (sum_eventually_eq_initial hh hh1 hqbig a hs hx hz) e0

/-- Construct the full sum's away extensions from finite raw endpoint
models in their valid domain and the initial field on the central plane. -/
theorem diagonal_awayExtensions_local {h C qbig : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (hqbig : 0 < qbig)
    {a : ℕ → ℝ} (hat : Tendsto a atTop atTop)
    (ha0 : 0 < a 0) (ham : ∀ j, a 0 ≤ a j) (hgap : 1 / a 0 < qbig)
    {F : ℕ → SpaceTime → V}
    (hs : ∀ j, j ≠ 0 → SublevelShrinkingSupport h C qbig (F j))
    (he0 : ∀ x : Space, x ≠ 0 → x 2 = 0 → Nonempty (OneSidedExtension (F 0) x))
    (he : ∀ x : Space, x 2 ≠ 0 →
      EndpointCoordinates.endpointRoot (2 * h) (x 2) < qbig →
      ∀ j, Nonempty (OneSidedExtension (F j) x)) :
    AwayExtensions (SolenoidalDiagonal.potentialSum a (PhysicalWaveSum.physicalQ h) F) := by
  intro x hx
  by_cases hz : x 2 = 0
  · exact central_extension_local hh hh1 hqbig a hs hx hz (Classical.choice (he0 x hx hz))
  · exact offplane_extension_local hh hh1 hat ha0 ham hgap hz (he x hz)

end NavierStokes.MixedDiagonalExtensions
