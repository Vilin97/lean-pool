/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.SmoothCutoffs
public import LeanPool.NavierStokesAndEuler.NavierStokes.DiagonalScale
public import LeanPool.NavierStokesAndEuler.NavierStokes.SpatialCurl
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Topology.LocallyFinite

@[expose] public section

/-!
# Smooth solenoidal diagonal sums

The sum in this file is an actual `tsum` of cut potentials. At each point
where the continuous scale `q` is positive, an entire tail is identically zero
on a common neighborhood. Thus the sum equals a finite prefix locally.
Smoothness requires smooth `q` and smooth potentials; mere continuity of `q`
is sufficient for local finiteness only. The resulting spatial curl is smooth
and divergence-free. No residual estimate or singular endpoint regularity is
assumed or proved here.
-/

noncomputable section

namespace NavierStokes.SolenoidalDiagonal

open Set Filter Function
open scoped Topology BigOperators ContDiff

section Topological

variable {X V : Type*} [TopologicalSpace X]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Cut the potential before applying any velocity derivative. -/
def cutStage (a : ℕ → ℝ) (q : X → ℝ) (A : ℕ → X → V) (j : ℕ) (x : X) : V :=
  SmoothCutoffs.scaledCutoff (a j) (q x) • A j x

/-- The actual infinite sum; local finiteness below proves it is well behaved
on the positive-scale domain. -/
def potentialSum (a : ℕ → ℝ) (q : X → ℝ) (A : ℕ → X → V) (x : X) : V :=
  ∑' j : ℕ, cutStage a q A j x

def partialPotential (a : ℕ → ℝ) (q : X → ℝ) (A : ℕ → X → V)
    (N : ℕ) (x : X) : V :=
  ∑ j ∈ Finset.range N, cutStage a q A j x

/-- A common neighborhood, not merely a pointwise support bound, kills all
sufficiently late stages. No regularity of the potentials is needed. -/
theorem eventually_zero_tail {a : ℕ → ℝ} (ha : Tendsto a atTop atTop)
    {q : X → ℝ} {x : X} (hq : ContinuousAt q x) (hqx : 0 < q x)
    (A : ℕ → X → V) :
    ∃ N : ℕ, ∀ᶠ y in 𝓝 x, ∀ j : ℕ, N ≤ j → cutStage a q A j y = 0 := by
  obtain ⟨N, hN⟩ := SmoothCutoffs.scaledCutoffs_zero_on_common_neighborhood a ha hqx
  refine ⟨N, ?_⟩
  filter_upwards [hq (lt_mem_nhds (half_lt_self hqx))] with y hy
  intro j hj
  simp only [cutStage, hN j hj (q y) hy, zero_smul]

/-- Local equality to a finite prefix establishes the meaning of the `tsum`.
The prefix length works for all derivative orders. -/
theorem potentialSum_eventuallyEq_partial {a : ℕ → ℝ} (ha : Tendsto a atTop atTop)
    {q : X → ℝ} {x : X} (hq : ContinuousAt q x) (hqx : 0 < q x)
    (A : ℕ → X → V) :
    ∃ N : ℕ, potentialSum a q A =ᶠ[𝓝 x] partialPotential a q A N := by
  obtain ⟨N, hN⟩ := eventually_zero_tail ha hq hqx A
  refine ⟨N, hN.mono ?_⟩
  intro y hy
  apply tsum_eq_sum
  intro j hj
  exact hy j (Nat.le_of_not_gt (by simpa only [Finset.mem_range] using hj))

theorem summable_cutStage {a : ℕ → ℝ} (ha : Tendsto a atTop atTop)
    {q : X → ℝ} {x : X} (hq : ContinuousAt q x) (hqx : 0 < q x)
    (A : ℕ → X → V) : Summable (fun j => cutStage a q A j x) := by
  obtain ⟨N, hN⟩ := eventually_zero_tail ha hq hqx A
  apply summable_of_ne_finset_zero (s := Finset.range N)
  intro j hj
  exact hN.self_of_nhds j (Nat.le_of_not_gt (by simpa only [Finset.mem_range] using hj))

/-- The family of supports is locally finite on every domain on which `q`
is continuous and positive. -/
theorem locallyFinite_cutStage_support {a : ℕ → ℝ} (ha : Tendsto a atTop atTop)
    {q : X → ℝ} (hq : Continuous q) (hqpos : ∀ x, 0 < q x)
    (A : ℕ → X → V) : LocallyFinite (fun j => support (cutStage a q A j)) := by
  intro x
  obtain ⟨N, hN⟩ := eventually_zero_tail ha hq.continuousAt (hqpos x) A
  refine ⟨{y | ∀ j : ℕ, N ≤ j → cutStage a q A j y = 0}, hN, ?_⟩
  apply (Finset.range N).finite_toSet.subset
  intro j hj
  rcases hj with ⟨y, hy, hzero⟩
  change j ∈ Finset.range N
  apply Finset.mem_range.mpr
  by_contra hlt
  exact hy (hzero j (Nat.le_of_not_gt hlt))

theorem locallyFinite_cutStage_support_on {a : ℕ → ℝ} (ha : Tendsto a atTop atTop)
    {q : X → ℝ} {U : Set X} (hq : ContinuousOn q U)
    (hqpos : ∀ x ∈ U, 0 < q x) (A : ℕ → X → V) :
    LocallyFinite (fun j => support (fun x : U => cutStage a q A j x)) := by
  exact locallyFinite_cutStage_support ha hq.domRestrict (fun x => hqpos x x.property)
    (fun j x => A j x)

end Topological

section Smooth

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem cutStage_contDiffAt {a : ℕ → ℝ} {q : E → ℝ} {A : ℕ → E → V}
    {x : E} (hq : ContDiffAt ℝ ∞ q x) (hA : ∀ j, ContDiffAt ℝ ∞ (A j) x)
    (j : ℕ) : ContDiffAt ℝ ∞ (cutStage a q A j) x :=
  ((SmoothCutoffs.scaledCutoff_contDiff (a j)).comp_contDiffAt x hq).smul (hA j)

/-- Smoothness is proved for the constructed sum, not postulated. -/
theorem potentialSum_contDiffAt {a : ℕ → ℝ} (ha : Tendsto a atTop atTop)
    {q : E → ℝ} {A : ℕ → E → V} {x : E} (hqx : 0 < q x)
    (hq : ContDiffAt ℝ ∞ q x) (hA : ∀ j, ContDiffAt ℝ ∞ (A j) x) :
    ContDiffAt ℝ ∞ (potentialSum a q A) x := by
  obtain ⟨N, hN⟩ := potentialSum_eventuallyEq_partial ha hq.continuousAt hqx A
  have hpartial : ContDiffAt ℝ ∞ (partialPotential a q A N) x :=
    ContDiffAt.sum (fun j _ => cutStage_contDiffAt hq hA j)
  exact hpartial.congr_of_eventuallyEq hN

theorem potentialSum_contDiffOn {a : ℕ → ℝ} (ha : Tendsto a atTop atTop)
    {q : E → ℝ} {A : ℕ → E → V} {U : Set E} (hU : IsOpen U)
    (hqpos : ∀ x ∈ U, 0 < q x) (hq : ContDiffOn ℝ ∞ q U)
    (hA : ∀ j, ContDiffOn ℝ ∞ (A j) U) :
    ContDiffOn ℝ ∞ (potentialSum a q A) U := by
  intro x hx
  exact (potentialSum_contDiffAt ha (hqpos x hx) (hq.contDiffAt (hU.mem_nhds hx))
    (fun j => (hA j).contDiffAt (hU.mem_nhds hx))).contDiffWithinAt

/-- Equality on a neighborhood preserves every iterated actual Fréchet
derivative, including the totalized derivative at nonsmooth points. -/
theorem iteratedFDeriv_eventuallyEq {f g : E → V} {x : E}
    (h : f =ᶠ[𝓝 x] g) (k : ℕ) :
    iteratedFDeriv ℝ k f =ᶠ[𝓝 x] iteratedFDeriv ℝ k g := by
  have h' : f =ᶠ[𝓝[univ] x] g := by simpa only [nhdsWithin_univ] using h
  simpa only [nhdsWithin_univ, iteratedFDerivWithin_univ] using
    h'.iteratedFDerivWithin (𝕜 := ℝ) k

theorem potentialSum_allJets_eventuallyEq_partial {a : ℕ → ℝ}
    (ha : Tendsto a atTop atTop) {q : E → ℝ} {A : ℕ → E → V} {x : E}
    (hq : ContinuousAt q x) (hqx : 0 < q x) :
    ∃ N : ℕ, ∀ k : ℕ,
      iteratedFDeriv ℝ k (potentialSum a q A) =ᶠ[𝓝 x]
        iteratedFDeriv ℝ k (partialPotential a q A N) := by
  obtain ⟨N, hN⟩ := potentialSum_eventuallyEq_partial ha hq hqx A
  exact ⟨N, fun k => iteratedFDeriv_eventuallyEq hN k⟩

theorem iteratedFDeriv_partialPotential {a : ℕ → ℝ} {q : E → ℝ}
    {A : ℕ → E → V} {x : E} (hq : ContDiffAt ℝ ∞ q x)
    (hA : ∀ j, ContDiffAt ℝ ∞ (A j) x) (N k : ℕ) :
    iteratedFDeriv ℝ k (partialPotential a q A N) x =
      ∑ j ∈ Finset.range N, iteratedFDeriv ℝ k (cutStage a q A j) x := by
  have hstage : ∀ j ∈ Finset.range N,
      ContDiffWithinAt ℝ k (cutStage a q A j) univ x := by
    intro j _
    exact ((cutStage_contDiffAt hq hA j).of_le
      (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))).contDiffWithinAt
  unfold partialPotential
  simpa only [iteratedFDerivWithin_univ] using
    iteratedFDerivWithin_fun_sum_apply uniqueDiffOn_univ (mem_univ x) hstage

/-- Every derivative is locally the finite sum of the corresponding stage
derivatives. The prefix length is independent of the derivative order. -/
theorem potentialSum_allJets_eventuallyEq_sum {a : ℕ → ℝ}
    (ha : Tendsto a atTop atTop) {q : E → ℝ} {A : ℕ → E → V}
    {U : Set E} (hU : IsOpen U) (hqpos : ∀ x ∈ U, 0 < q x)
    (hq : ContDiffOn ℝ ∞ q U) (hA : ∀ j, ContDiffOn ℝ ∞ (A j) U)
    {x : E} (hx : x ∈ U) :
    ∃ N : ℕ, ∀ k : ℕ, ∀ᶠ y in 𝓝 x,
      iteratedFDeriv ℝ k (potentialSum a q A) y =
        ∑ j ∈ Finset.range N, iteratedFDeriv ℝ k (cutStage a q A j) y := by
  obtain ⟨N, hN⟩ := potentialSum_allJets_eventuallyEq_partial (A := A) ha
    (hq.contDiffAt (hU.mem_nhds hx)).continuousAt (hqpos x hx)
  refine ⟨N, fun k => ?_⟩
  filter_upwards [hN k, hU.mem_nhds hx] with y hy hyU
  exact hy.trans (iteratedFDeriv_partialPotential (hq.contDiffAt (hU.mem_nhds hyU))
    (fun j => (hA j).contDiffAt (hU.mem_nhds hyU)) N k)

end Smooth

section Spatial

open ProblemStatement

/-- The constructed velocity is the actual spatial curl of the summed
potential, with time held fixed by `SpatialCurl.spatialCurl`. -/
def velocitySum (a : ℕ → ℝ) (q : SpaceTime → ℝ) (A : ℕ → VelocityField) :
    VelocityField :=
  SpatialCurl.spatialCurl (potentialSum a q A)

theorem velocitySum_contDiffAt {a : ℕ → ℝ} (ha : Tendsto a atTop atTop)
    {q : SpaceTime → ℝ} {A : ℕ → VelocityField} {z : SpaceTime}
    (hqz : 0 < q z) (hq : ContDiffAt ℝ ∞ q z)
    (hA : ∀ j, ContDiffAt ℝ ∞ (A j) z) :
    ContDiffAt ℝ ∞ (velocitySum a q A) z :=
  SpatialCurl.contDiffAt_spatialCurl (potentialSum_contDiffAt ha hqz hq hA) (by simp)

theorem velocitySum_contDiffOn {a : ℕ → ℝ} (ha : Tendsto a atTop atTop)
    {q : SpaceTime → ℝ} {A : ℕ → VelocityField} {U : Set SpaceTime}
    (hU : IsOpen U) (hqpos : ∀ z ∈ U, 0 < q z) (hq : ContDiffOn ℝ ∞ q U)
    (hA : ∀ j, ContDiffOn ℝ ∞ (A j) U) :
    ContDiffOn ℝ ∞ (velocitySum a q A) U := by
  intro z hz
  exact (velocitySum_contDiffAt ha (hqpos z hz) (hq.contDiffAt (hU.mem_nhds hz))
    (fun j => (hA j).contDiffAt (hU.mem_nhds hz))).contDiffWithinAt

/-- Incompressibility follows from actual second-derivative symmetry, already
proved in `SpatialCurl`, applied to the constructed smooth potential. -/
theorem divergence_velocitySum {a : ℕ → ℝ} (ha : Tendsto a atTop atTop)
    {q : SpaceTime → ℝ} {A : ℕ → VelocityField} {z : SpaceTime}
    (hqz : 0 < q z) (hq : ContDiffAt ℝ ∞ q z)
    (hA : ∀ j, ContDiffAt ℝ ∞ (A j) z) :
    spatialDivergence (velocitySum a q A) z.1 z.2 = 0 := by
  have hsum : ContDiffAt ℝ ∞ (potentialSum a q A) z :=
    potentialSum_contDiffAt ha hqz hq hA
  have hslice : ContDiffAt ℝ ∞ (fun y : Space => potentialSum a q A (z.1, y)) z.2 :=
    hsum.comp (f := fun y : Space => (z.1, y)) z.2
      (contDiffAt_const.prodMk contDiffAt_id)
  have hslice2 : ContDiffAt ℝ 2 (fun y : Space => potentialSum a q A (z.1, y)) z.2 :=
    hslice.of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  exact SpatialCurl.spatialDivergence_spatialCurl (potentialSum a q A) z.1 z.2 hslice2

theorem divergence_velocitySum_on {a : ℕ → ℝ} (ha : Tendsto a atTop atTop)
    {q : SpaceTime → ℝ} {A : ℕ → VelocityField} {U : Set SpaceTime}
    (hU : IsOpen U) (hqpos : ∀ z ∈ U, 0 < q z) (hq : ContDiffOn ℝ ∞ q U)
    (hA : ∀ j, ContDiffOn ℝ ∞ (A j) U) :
    ∀ z ∈ U, spatialDivergence (velocitySum a q A) z.1 z.2 = 0 := by
  intro z hz
  exact divergence_velocitySum ha (hqpos z hz) (hq.contDiffAt (hU.mem_nhds hz))
    (fun j => (hA j).contDiffAt (hU.mem_nhds hz))

theorem spatialCurl_eq_of_eventuallyEq {A B : VelocityField} {z : SpaceTime}
    (h : A =ᶠ[𝓝 z] B) : SpatialCurl.spatialCurl A z = SpatialCurl.spatialCurl B z := by
  apply SpatialCurl.curl_eq_of_eventuallyEq
  exact h.comp_tendsto (continuous_const.prodMk continuous_id).continuousAt

theorem spatialCurl_eventuallyEq {A B : VelocityField} {z : SpaceTime}
    (h : A =ᶠ[𝓝 z] B) : SpatialCurl.spatialCurl A =ᶠ[𝓝 z] SpatialCurl.spatialCurl B :=
  h.eventuallyEq_nhds.mono fun _ hz => spatialCurl_eq_of_eventuallyEq hz

theorem spatialCurl_partialPotential {a : ℕ → ℝ} {q : SpaceTime → ℝ}
    {A : ℕ → VelocityField} {z : SpaceTime} (hq : ContDiffAt ℝ ∞ q z)
    (hA : ∀ j, ContDiffAt ℝ ∞ (A j) z) (N : ℕ) :
    SpatialCurl.spatialCurl (partialPotential a q A N) z =
      ∑ j ∈ Finset.range N, SpatialCurl.spatialCurl (cutStage a q A j) z := by
  have hstage : ∀ j ∈ Finset.range N,
      DifferentiableAt ℝ (fun y : Space => cutStage a q A j (z.1, y)) z.2 := by
    intro j _
    exact ((cutStage_contDiffAt hq hA j).comp z.2
      (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  simpa only [partialPotential, SpatialCurl.spatialCurl, SpatialCurl.curl, map_sum] using
    congrArg SpatialCurl.curlLinear (fderiv_fun_sum hstage)

/-- The curl of the summed potential is locally the finite sum of the curls
of the cut potentials. Thus it also realizes the manuscript's stage sum. -/
theorem velocitySum_eventuallyEq_sum {a : ℕ → ℝ} (ha : Tendsto a atTop atTop)
    {q : SpaceTime → ℝ} {A : ℕ → VelocityField} {U : Set SpaceTime}
    (hU : IsOpen U) (hqpos : ∀ z ∈ U, 0 < q z) (hq : ContDiffOn ℝ ∞ q U)
    (hA : ∀ j, ContDiffOn ℝ ∞ (A j) U) {z : SpaceTime} (hz : z ∈ U) :
    ∃ N : ℕ, velocitySum a q A =ᶠ[𝓝 z]
      (fun w => ∑ j ∈ Finset.range N, SpatialCurl.spatialCurl (cutStage a q A j) w) := by
  obtain ⟨N, hN⟩ := potentialSum_eventuallyEq_partial ha
    (hq.contDiffAt (hU.mem_nhds hz)).continuousAt (hqpos z hz) A
  refine ⟨N, ?_⟩
  filter_upwards [spatialCurl_eventuallyEq hN, hU.mem_nhds hz] with w hw hwU
  exact hw.trans (spatialCurl_partialPotential (hq.contDiffAt (hU.mem_nhds hwU))
    (fun j => (hA j).contDiffAt (hU.mem_nhds hwU)) N)

/-- A direct open-domain theorem for the constructed potential and velocity. -/
theorem smooth_solenoidal_diagonal {a : ℕ → ℝ} (ha : Tendsto a atTop atTop)
    {q : SpaceTime → ℝ} {A : ℕ → VelocityField} {U : Set SpaceTime}
    (hU : IsOpen U) (hqpos : ∀ z ∈ U, 0 < q z) (hq : ContDiffOn ℝ ∞ q U)
    (hA : ∀ j, ContDiffOn ℝ ∞ (A j) U) :
    LocallyFinite (fun j => support (fun z : U => cutStage a q A j z)) ∧
    ContDiffOn ℝ ∞ (potentialSum a q A) U ∧
    ContDiffOn ℝ ∞ (velocitySum a q A) U ∧
    (∀ z ∈ U, spatialDivergence (velocitySum a q A) z.1 z.2 = 0) :=
  ⟨locallyFinite_cutStage_support_on ha hq.continuousOn hqpos A,
    potentialSum_contDiffOn ha hU hqpos hq hA,
    velocitySum_contDiffOn ha hU hqpos hq hA,
    divergence_velocitySum_on ha hU hqpos hq hA⟩

/-- Integer schedules from `DiagonalScale` supply the required real divergence
of the cutoff scales. -/
theorem realScales_tendsto {a : ℕ → ℕ} (ha : StrictMono a) :
    Tendsto (fun j => (a j : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp ha.tendsto_atTop

theorem doublingEnvelope_tendsto (b : ℕ → ℕ) :
    Tendsto (fun j => (DiagonalScale.doublingEnvelope b j : ℝ)) atTop atTop :=
  realScales_tendsto (DiagonalScale.doublingEnvelope_strictMono b)

/-- The numerical diagonal schedule and the smooth solenoidal construction
can be chosen together. The numerical bounds are not asserted to be estimates
for the potentials; that requires the manuscript's separate analytic input. -/
theorem exists_diagonal_scales_smooth_solenoidal
    (C p : ℕ → ℕ → ℝ) (g : ℕ → ℝ) (hg : ∀ j, 1 ≤ j → 0 < g j) (B : ℕ)
    {q : SpaceTime → ℝ} {A : ℕ → VelocityField} {U : Set SpaceTime}
    (hU : IsOpen U) (hqpos : ∀ z ∈ U, 0 < q z) (hq : ContDiffOn ℝ ∞ q U)
    (hA : ∀ j, ContDiffOn ℝ ∞ (A j) U) :
    ∃ a : ℕ → ℕ,
      B ≤ a 0 ∧ (∀ j, 0 < a j) ∧ (∀ j, 2 * a j ≤ a (j + 1)) ∧ StrictMono a ∧
      (∀ j, 1 ≤ j → ∀ m, m ≤ j + 2 → ∀ r : ℝ, 0 < r → r ≤ 1 / (a j : ℝ) →
        |DiagonalScale.logPowerWeight (C j m) (p j m) (g j / 2) r| ≤ (1 / 2 : ℝ) ^ j) ∧
      ContDiffOn ℝ ∞ (potentialSum (fun j => (a j : ℝ)) q A) U ∧
      ContDiffOn ℝ ∞ (velocitySum (fun j => (a j : ℝ)) q A) U ∧
      (∀ z ∈ U, spatialDivergence (velocitySum (fun j => (a j : ℝ)) q A) z.1 z.2 = 0) := by
  obtain ⟨a, hB, hpos, hdouble, hmono, _, hweight⟩ :=
    DiagonalScale.exists_diagonal_scales C p g hg B
  have hatop := realScales_tendsto hmono
  exact ⟨a, hB, hpos, hdouble, hmono, hweight,
    potentialSum_contDiffOn hatop hU hqpos hq hA,
    velocitySum_contDiffOn hatop hU hqpos hq hA,
    divergence_velocitySum_on hatop hU hqpos hq hA⟩

end Spatial

end NavierStokes.SolenoidalDiagonal
