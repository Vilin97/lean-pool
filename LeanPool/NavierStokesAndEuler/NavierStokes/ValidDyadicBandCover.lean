/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.NavierStokes.CutStageEstimates
public import LeanPool.NavierStokesAndEuler.NavierStokes.EndpointCoordinates
public import LeanPool.NavierStokesAndEuler.NavierStokes.JointResidualLimits
import LeanPool.NavierStokesAndEuler.NavierStokes.MixedDiagonalExtensions
import LeanPool.NavierStokesAndEuler.NavierStokes.PhysicalMeanJetBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.SpatialCurl

/-!
# Gluing on the actual open dyadic validity regions

The band floor is fixed.  A sufficiently small positive physical scale is
inside an open validity region of some band above that floor.  The local
formulas below are supplied on those open regions, rather than by the
values of a fixed reference formula on its excluded dyadic faces.

This module transfers local formulas, jets, zero germs, and already proved
local endpoint extensions.  It does not manufacture their local smoothness
or identify them with a reference formula outside its validity region.
-/

section

/-!
# A representative on the union of valid open charts

Local formulas are identified only where both charts are valid.  The
chosen representative agrees with every valid chart on an ambient
neighborhood.  No regularity at the boundary of the union is asserted.
-/

@[expose] public section

noncomputable section

namespace NavierStokes.ValidBandGluing

open Set Filter Function
open scoped Topology ContDiff

variable {ι D E : Type*}

/-- Domain, given by `⋃ i, U i`. -/
def domain (U : ι → Set D) : Set D := ⋃ i, U i

/-- Compatible, given by `∀ i j, EqOn (f i) (f j) (U i ∩ U j)`. -/
def Compatible (U : ι → Set D) (f : ι → D → E) : Prop :=
  ∀ i j, EqOn (f i) (f j) (U i ∩ U j)

/-- Choose a chart only at points covered by at least one valid chart.
The value outside the valid union is the stated zero totalization. -/
noncomputable def representative [Zero E] (U : ι → Set D) (f : ι → D → E) (x : D) : E := by
  classical
  exact if h : ∃ i, x ∈ U i then f (Classical.choose h) x else 0

theorem mem_domain_iff {U : ι → Set D} {x : D} : x ∈ domain U ↔ ∃ i, x ∈ U i :=
  mem_iUnion

theorem representative_zero [Zero E] {U : ι → Set D} {f : ι → D → E}
    {x : D} (hx : x ∉ domain U) : representative U f x = 0 := by
  have hn : ¬ ∃ i, x ∈ U i := fun h => hx (mem_domain_iff.mpr h)
  simp only [representative, dite_eq_right hn]

theorem representative_eq_of_mem [Zero E] {U : ι → Set D} {f : ι → D → E}
    (hf : Compatible U f) {i : ι} {x : D} (hx : x ∈ U i) :
    representative U f x = f i x := by
  classical
  have h : ∃ j, x ∈ U j := ⟨i, hx⟩
  simp only [representative, dite_eq_left h]
  exact hf (Classical.choose h) i ⟨Classical.choose_spec h, hx⟩

theorem representative_eqOn [Zero E] {U : ι → Set D} {f : ι → D → E}
    (hf : Compatible U f) (i : ι) : EqOn (representative U f) (f i) (U i) :=
  fun _ hx => representative_eq_of_mem hf hx

theorem representative_unique_on_domain [Zero E] {U : ι → Set D} {f : ι → D → E}
    (hf : Compatible U f) {g : D → E} (hg : ∀ i, EqOn g (f i) (U i)) :
    EqOn (representative U f) g (domain U) := by
  intro x hx
  obtain ⟨i, hi⟩ := mem_domain_iff.mp hx
  exact (representative_eq_of_mem hf hi).trans (hg i hi).symm

section Topology

variable [TopologicalSpace D]

theorem domain_open {U : ι → Set D} (hU : ∀ i, IsOpen (U i)) : IsOpen (domain U) :=
  isOpen_iUnion hU

theorem representative_germ [Zero E] {U : ι → Set D} {f : ι → D → E}
    (hU : ∀ i, IsOpen (U i)) (hf : Compatible U f) {i : ι} {x : D} (hx : x ∈ U i) :
    representative U f =ᶠ[𝓝 x] f i :=
  eventually_of_mem ((hU i).mem_nhds hx) (fun _ hy => representative_eq_of_mem hf hy)

/-- The zero totalization has a zero germ off the closure. No such claim
is made at an excluded face in the closure of the valid union. -/
theorem representative_zero_germ [Zero E] {U : ι → Set D} {f : ι → D → E}
    {x : D} (hx : x ∉ closure (domain U)) : representative U f =ᶠ[𝓝 x] fun _ => 0 := by
  filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hx] with y hy
  exact representative_zero (fun h => hy (subset_closure h))

theorem representative_continuousOn [TopologicalSpace E] [Zero E]
    {U : ι → Set D} {f : ι → D → E} (hU : ∀ i, IsOpen (U i)) (hf : Compatible U f)
    (hs : ∀ i, ContinuousOn (f i) (U i)) : ContinuousOn (representative U f) (domain U) := by
  intro x hx
  obtain ⟨i, hi⟩ := mem_domain_iff.mp hx
  exact ((hs i).continuousAt ((hU i).mem_nhds hi)).congr
    (representative_germ hU hf hi).symm |>.continuousWithinAt

end Topology

section Derivatives

variable [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {U : ι → Set D} {f : ι → D → E}

theorem representative_contDiffAt {n : WithTop ℕ∞}
    (hU : ∀ i, IsOpen (U i)) (hf : Compatible U f) {i : ι} {x : D} (hx : x ∈ U i)
    (hs : ContDiffOn ℝ n (f i) (U i)) : ContDiffAt ℝ n (representative U f) x :=
  (hs.contDiffAt ((hU i).mem_nhds hx)).congr_of_eventuallyEq (representative_germ hU hf hx)

theorem representative_contDiffOn {n : WithTop ℕ∞}
    (hU : ∀ i, IsOpen (U i)) (hf : Compatible U f)
    (hs : ∀ i, ContDiffOn ℝ n (f i) (U i)) : ContDiffOn ℝ n (representative U f) (domain U) := by
  intro x hx
  obtain ⟨i, hi⟩ := mem_domain_iff.mp hx
  exact (representative_contDiffAt hU hf hi (hs i)).contDiffWithinAt

theorem representative_fderiv_eq (hU : ∀ i, IsOpen (U i)) (hf : Compatible U f)
    {i : ι} {x : D} (hx : x ∈ U i) :
    fderiv ℝ (representative U f) x = fderiv ℝ (f i) x :=
  (representative_germ hU hf hx).fderiv_eq

/-- The actual multilinear derivative tensors agree as functions near
each valid point. No differentiability premise is needed for germ locality. -/
theorem representative_iteratedFDeriv_germ (hU : ∀ i, IsOpen (U i)) (hf : Compatible U f)
    {i : ι} {x : D} (hx : x ∈ U i) (m : ℕ) :
    iteratedFDeriv ℝ m (representative U f) =ᶠ[𝓝 x] iteratedFDeriv ℝ m (f i) := by
  have he : representative U f =ᶠ[𝓝[univ] x] f i := by
    simpa only [nhdsWithin_univ] using representative_germ hU hf hx
  simpa only [nhdsWithin_univ, iteratedFDerivWithin_univ] using
    he.iteratedFDerivWithin (𝕜 := ℝ) m

theorem representative_iteratedFDeriv_eq (hU : ∀ i, IsOpen (U i)) (hf : Compatible U f)
    {i : ι} {x : D} (hx : x ∈ U i) (m : ℕ) :
    iteratedFDeriv ℝ m (representative U f) x = iteratedFDeriv ℝ m (f i) x :=
  (representative_iteratedFDeriv_germ hU hf hx m).self_of_nhds

theorem representative_jet_bound (hU : ∀ i, IsOpen (U i)) (hf : Compatible U f)
    {i : ι} {x : D} (hx : x ∈ U i) (m : ℕ) {B : ℝ}
    (hb : ‖iteratedFDeriv ℝ m (f i) x‖ ≤ B) :
    ‖iteratedFDeriv ℝ m (representative U f) x‖ ≤ B := by
  rw [representative_iteratedFDeriv_eq hU hf hx m]
  exact hb

/-- The same pointwise majorant transfers on the entire union. There is
no multiplicity factor, regardless of the number of overlapping charts. -/
theorem representative_jet_bound_on_union (hU : ∀ i, IsOpen (U i)) (hf : Compatible U f)
    (m : ℕ) {B : D → ℝ} (hb : ∀ i, ∀ x ∈ U i, ‖iteratedFDeriv ℝ m (f i) x‖ ≤ B x) :
    ∀ x ∈ domain U, ‖iteratedFDeriv ℝ m (representative U f) x‖ ≤ B x := by
  intro x hx
  obtain ⟨i, hi⟩ := mem_domain_iff.mp hx
  exact representative_jet_bound hU hf hi m (hb i x hi)

theorem representative_finite_jets_bound (hU : ∀ i, IsOpen (U i)) (hf : Compatible U f)
    (N : ℕ) {B : ℕ → D → ℝ}
    (hb : ∀ i, ∀ m ≤ N, ∀ x ∈ U i, ‖iteratedFDeriv ℝ m (f i) x‖ ≤ B m x) :
    ∀ m ≤ N, ∀ x ∈ domain U, ‖iteratedFDeriv ℝ m (representative U f) x‖ ≤ B m x := by
  intro m hm
  exact representative_jet_bound_on_union hU hf m (fun i x hx => hb i m hm x hx)

theorem representative_jet_apply_eq (hU : ∀ i, IsOpen (U i)) (hf : Compatible U f)
    {i : ι} {x : D} (hx : x ∈ U i) (m : ℕ) (v : Fin m → D) :
    iteratedFDeriv ℝ m (representative U f) x v = iteratedFDeriv ℝ m (f i) x v := by
  rw [representative_iteratedFDeriv_eq hU hf hx m]

end Derivatives

section PhysicalCurl

open ProblemStatement

theorem spatialCurl_eq_of_germ {A B : VelocityField} {x : SpaceTime}
    (h : A =ᶠ[𝓝 x] B) : SpatialCurl.spatialCurl A x = SpatialCurl.spatialCurl B x := by
  have hs : (fun y : Space => A (x.1, y)) =ᶠ[𝓝 x.2] fun y => B (x.1, y) :=
    h.comp_tendsto (by
      change Tendsto (fun y : Space => (x.1, y)) (𝓝 x.2) (𝓝 (x.1, x.2))
      exact continuousAt_const.prodMk continuousAt_id)
  exact congrArg SpatialCurl.curlLinear hs.fderiv_eq

theorem representative_spatialCurl_eq {U : ι → Set SpaceTime} {A : ι → VelocityField}
    (hU : ∀ i, IsOpen (U i)) (hA : Compatible U A) {i : ι} {x : SpaceTime} (hx : x ∈ U i) :
    SpatialCurl.spatialCurl (representative U A) x = SpatialCurl.spatialCurl (A i) x :=
  spatialCurl_eq_of_germ (representative_germ hU hA hx)

theorem representative_spatialCurl_germ {U : ι → Set SpaceTime} {A : ι → VelocityField}
    (hU : ∀ i, IsOpen (U i)) (hA : Compatible U A) {i : ι} {x : SpaceTime} (hx : x ∈ U i) :
    SpatialCurl.spatialCurl (representative U A) =ᶠ[𝓝 x] SpatialCurl.spatialCurl (A i) :=
  eventually_of_mem ((hU i).mem_nhds hx) (fun _ hy => representative_spatialCurl_eq hU hA hy)

end PhysicalCurl

end NavierStokes.ValidBandGluing

end
end

end

@[expose] public section

noncomputable section

namespace NavierStokes.ValidDyadicBandCover

open Set Filter ProblemStatement PhysicalWaveSum
open scoped Topology ContDiff

/-- Strictly inside the band: the normalized physical scale is in `(1/2,2)`. -/
noncomputable def band (h : ℝ) (n : ℕ) : Set SpaceTime :=
  {w | w ∈ preterminal ∧ ChartScales.Q n / 2 < physicalQ h w ∧
    physicalQ h w < 2 * ChartScales.Q n}

theorem mem_band_iff {h : ℝ} {n : ℕ} {w : SpaceTime} :
    w ∈ band h n ↔ w ∈ preterminal ∧
      physicalQ h w / ChartScales.Q n ∈ Ioo (1 / 2 : ℝ) 2 := by
  have hQ := ChartScales.Q_pos n
  simp only [band, Set.mem_ofPred_eq, mem_Ioo, lt_div_iff₀ hQ, div_lt_iff₀ hQ]
  constructor <;> rintro ⟨ht, hl, hr⟩ <;> refine ⟨ht, ?_, hr⟩ <;> linarith

theorem band_open {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2) (n : ℕ) :
    IsOpen (band h n) := by
  apply isOpen_iff_mem_nhds.mpr
  intro w hw
  have hc := (physicalQ_smoothAt hh hh1 hw.1).continuousAt
  exact inter_mem (preterminal_open.mem_nhds hw.1)
    (inter_mem (hc (isOpen_Ioi.mem_nhds hw.2.1))
      (hc (isOpen_Iio.mem_nhds hw.2.2)))

/-- The selected band has the stronger comparison `q ≤ Q_n < 2q`. -/
theorem exists_band {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2) (N : ℕ)
    {w : SpaceTime} (ht : w ∈ preterminal) (hq : physicalQ h w ≤ ChartScales.Q N) :
    ∃ n : ℕ, N ≤ n ∧ w ∈ band h n ∧ physicalQ h w ≤ ChartScales.Q n := by
  obtain ⟨n, hn, hlo, hhi⟩ := PhysicalMeanJetBounds.exists_comparable_band N
    (physicalQ_pos hh hh1 ht) hq
  refine ⟨n, hn, ⟨ht, ?_, ?_⟩, hlo⟩
  · linarith
  · have := ChartScales.Q_pos n
    linarith

/-- Index: an abbreviation for `{n : ℕ // N ≤ n}`. -/
abbrev Index (N : ℕ) := {n : ℕ // N ≤ n}

/-- Charts, given by `band h n.val`. -/
noncomputable def charts (h : ℝ) (N : ℕ) (n : Index N) : Set SpaceTime := band h n.val

theorem sublevel_covered {h qbig : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2) (N : ℕ)
    (hqbig : qbig ≤ ChartScales.Q N) :
    CutStageEstimates.physicalSublevel h qbig ⊆ ValidBandGluing.domain (charts h N) := by
  intro w hw
  obtain ⟨n, hn, hb, _⟩ := exists_band hh hh1 N hw.1 (hw.2.le.trans hqbig)
  exact ValidBandGluing.mem_domain_iff.mpr ⟨⟨n, hn⟩, hb⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Compatible, given by `ValidBandGluing.Compatible (charts h N) (fun n => f n.val)`. -/
def Compatible (h : ℝ) (N : ℕ) (f : ℕ → SpaceTime → E) : Prop :=
  ValidBandGluing.Compatible (charts h N) (fun n => f n.val)

/-- Field, given by `ValidBandGluing.representative (charts h N) (fun n => f n.val)`. -/
noncomputable def field (h : ℝ) (N : ℕ) (f : ℕ → SpaceTime → E) : SpaceTime → E :=
  ValidBandGluing.representative (charts h N) (fun n => f n.val)

omit [NormedSpace ℝ E] in
theorem field_eq {h : ℝ} {N n : ℕ} {f : ℕ → SpaceTime → E}
    (hf : Compatible h N f) (hn : N ≤ n) {w : SpaceTime} (hw : w ∈ band h n) :
    field h N f w = f n w :=
  ValidBandGluing.representative_eq_of_mem hf (i := ⟨n, hn⟩) hw

omit [NormedSpace ℝ E] in
theorem field_germ {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {N n : ℕ} {f : ℕ → SpaceTime → E} (hf : Compatible h N f)
    (hn : N ≤ n) {w : SpaceTime} (hw : w ∈ band h n) :
    field h N f =ᶠ[𝓝 w] f n :=
  ValidBandGluing.representative_germ (fun n : Index N => band_open hh hh1 n.val)
    hf (i := ⟨n, hn⟩) hw

theorem field_smooth {h qbig : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {N : ℕ} {f : ℕ → SpaceTime → E} (hf : Compatible h N f)
    (hqbig : qbig ≤ ChartScales.Q N)
    (hs : ∀ n, N ≤ n → ContDiffOn ℝ ∞ (f n) (band h n)) :
    ContDiffOn ℝ ∞ (field h N f) (CutStageEstimates.physicalSublevel h qbig) :=
  (ValidBandGluing.representative_contDiffOn (fun n : Index N => band_open hh hh1 n.val)
    hf (fun n : Index N => hs n.val n.property)).mono (sublevel_covered hh hh1 N hqbig)

theorem field_jet_eq {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {N n : ℕ} {f : ℕ → SpaceTime → E} (hf : Compatible h N f)
    (hn : N ≤ n) {w : SpaceTime} (hw : w ∈ band h n) (m : ℕ) :
    iteratedFDeriv ℝ m (field h N f) w = iteratedFDeriv ℝ m (f n) w :=
  ValidBandGluing.representative_iteratedFDeriv_eq
    (fun n : Index N => band_open hh hh1 n.val) hf (i := ⟨n, hn⟩) hw m

/-- Pointwise transfer keeps any additional hypotheses on the physical
point available to the caller, such as a fixed time bound. -/
theorem field_jet_bound_at {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {N : ℕ} {f : ℕ → SpaceTime → E} (hf : Compatible h N f)
    {w : SpaceTime} (ht : w ∈ preterminal) (hq : physicalQ h w ≤ ChartScales.Q N)
    (m : ℕ) {B : ℝ}
    (hb : ∀ n, N ≤ n → w ∈ band h n → physicalQ h w ≤ ChartScales.Q n →
      ‖iteratedFDeriv ℝ m (f n) w‖ ≤ B) :
    ‖iteratedFDeriv ℝ m (field h N f) w‖ ≤ B := by
  obtain ⟨n, hn, hband, hcomp⟩ := exists_band hh hh1 N ht hq
  rw [field_jet_eq hh hh1 hf hn hband m]
  exact hb n hn hband hcomp

/-- Select a comparable chart for the bound, independently of the chart
chosen internally by `field`.  No chart-count factor is incurred. -/
theorem field_jet_bound {h qbig : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {N : ℕ} {f : ℕ → SpaceTime → E} (hf : Compatible h N f)
    (hqbig : qbig ≤ ChartScales.Q N) (m : ℕ) (B : SpaceTime → ℝ)
    (hb : ∀ n, N ≤ n → ∀ w ∈ band h n, physicalQ h w ≤ ChartScales.Q n →
      ‖iteratedFDeriv ℝ m (f n) w‖ ≤ B w) :
    ∀ w ∈ CutStageEstimates.physicalSublevel h qbig,
      ‖iteratedFDeriv ℝ m (field h N f) w‖ ≤ B w := by
  intro w hw
  exact field_jet_bound_at hh hh1 hf hw.1 (hw.2.le.trans hqbig) m
    (fun n hn hband hcomp => hb n hn w hband hcomp)

omit [NormedSpace ℝ E] in
/-- A local support proof in any valid chart supplies the actual zero
germ of the representative, including at the physical axis. -/
theorem field_zero_germ {h qbig : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {N : ℕ} {f : ℕ → SpaceTime → E} (hf : Compatible h N f)
    (hqbig : qbig ≤ ChartScales.Q N) {w : SpaceTime}
    (hw : w ∈ CutStageEstimates.physicalSublevel h qbig)
    (hz : ∀ n, N ≤ n → w ∈ band h n → f n =ᶠ[𝓝 w] fun _ => 0) :
    field h N f =ᶠ[𝓝 w] fun _ => 0 := by
  obtain ⟨n, hn, hband, _⟩ := exists_band hh hh1 N hw.1 (hw.2.le.trans hqbig)
  exact (field_germ hh hh1 hf hn hband).trans (hz n hn hband)

/-- Endpoint selection concerns only the positive limiting scale.  The
endpoint itself is not inserted into any preterminal formula. -/
theorem endpoint_band {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2) (N : ℕ)
    {x : Space} (hx : x 2 ≠ 0)
    (hq : EndpointCoordinates.endpointRoot (2 * h) (x 2) ≤ ChartScales.Q N) :
    ∃ n : ℕ, N ≤ n ∧
      ChartScales.Q n / 2 < EndpointCoordinates.endpointRoot (2 * h) (x 2) ∧
      EndpointCoordinates.endpointRoot (2 * h) (x 2) < 2 * ChartScales.Q n ∧
      ∀ᶠ w in 𝓝[SpacetimeEndpoint.openPast 1] (1, x), w ∈ band h n := by
  obtain ⟨n, hn, hlo, hhi⟩ := PhysicalMeanJetBounds.exists_comparable_band N
    (EndpointCoordinates.endpointRoot_pos (2 * h) hx) hq
  have hl : ChartScales.Q n / 2 < EndpointCoordinates.endpointRoot (2 * h) (x 2) := by
    linarith
  have hr : EndpointCoordinates.endpointRoot (2 * h) (x 2) < 2 * ChartScales.Q n := by
    have := ChartScales.Q_pos n
    linarith
  refine ⟨n, hn, hl, hr, ?_⟩
  have ht := MixedDiagonalExtensions.physicalQ_tendsto_endpoint hh hh1 hx
  filter_upwards [self_mem_nhdsWithin, ht.eventually (isOpen_Ioo.mem_nhds ⟨hl, hr⟩)] with w hw hq
  exact ⟨hw.1, hq⟩

/-- A proved continuation of the selected current-chart formula transfers
to the representative.  Local continuation remains a necessary premise. -/
theorem field_endpoint_extension {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {N : ℕ} {f : ℕ → SpaceTime → E} (hf : Compatible h N f)
    {x : Space} (hx : x 2 ≠ 0)
    (hq : EndpointCoordinates.endpointRoot (2 * h) (x 2) ≤ ChartScales.Q N)
    (he : ∀ n, N ≤ n →
      ChartScales.Q n / 2 < EndpointCoordinates.endpointRoot (2 * h) (x 2) →
      EndpointCoordinates.endpointRoot (2 * h) (x 2) < 2 * ChartScales.Q n →
      Nonempty (JointResidualLimits.OneSidedExtension (f n) x)) :
    Nonempty (JointResidualLimits.OneSidedExtension (field h N f) x) := by
  obtain ⟨n, hn, hl, hr, hg⟩ := endpoint_band hh hh1 N hx hq
  apply MixedDiagonalExtensions.extension_of_eventuallyEq _ (Classical.choice (he n hn hl hr))
  filter_upwards [hg] with w hw
  exact field_eq hf hn hw

end NavierStokes.ValidDyadicBandCover
