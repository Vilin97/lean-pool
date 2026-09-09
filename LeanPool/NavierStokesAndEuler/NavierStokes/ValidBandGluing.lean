/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.SpatialCurl

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
