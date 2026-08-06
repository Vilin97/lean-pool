/-
Copyright (c) 2026 Joseph K. Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph K. Miller
-/
import Mathlib.Analysis.Convex.Cone.InnerDual
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Topology.MetricSpace.Sequences
import LeanPool.Vlasov.OT.Wasserstein

/-!
# Coupling-based Wasserstein-1 distance

OT infrastructure on pseudometric spaces:

  1. Couplings and the Monge-Kantorovich definition of `W_1`.
  2. The easy direction of Kantorovich-Rubinstein duality,
     `wasserstein1_dual μ ν ≤ wasserstein1Coupling μ ν`.
  3. The hard direction `wasserstein1Coupling μ ν ≤ wasserstein1_dual μ ν`
     (via finite-range approximation + finite transportation LP duality),
     yielding the full KR equality `wasserstein1_eq_coupling`.

The dobrushin proof uses the coupling-cost bound to control W₁ growth along
characteristic flows.

See `formalize/DESIGN.md` (in the source repository) for the overall design choices.
-/

/-
The contents of this file — `IsCoupling`, `wasserstein1Coupling`, both
directions of KR, `IsCoupling.map`, and `wasserstein1_pushforward_le_iInf` —
are domain-independent OT on pseudometric spaces (natural Mathlib home:
`Mathlib/MeasureTheory/Wasserstein/Coupling.lean` under `namespace
MeasureTheory`).  We keep `namespace Vlasov` so the project is self-contained.
-/

namespace Vlasov

open MeasureTheory ProbabilityTheory ENNReal
open scoped ProbabilityTheory

/-! ## Couplings -/

/-- A coupling of measures `μ` on `α` and `ν` on `β` is a measure `π` on the
product space whose marginals are exactly `μ` and `ν`.

We use the convention that `Prod.fst` is the `α`-marginal and `Prod.snd` is
the `β`-marginal. -/
def IsCoupling {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (π : Measure (α × β)) (μ : Measure α) (ν : Measure β) : Prop :=
  Measure.map Prod.fst π = μ ∧ Measure.map Prod.snd π = ν

/-! ## Coupling-based Wasserstein-1 distance -/

/-- The coupling-based Wasserstein-1 distance: infimum of `∫⁻ edist(x,y) dπ(x,y)`
over all couplings `π` of `(μ, ν)`.  This is the Monge-Kantorovich definition,
to be compared with the dual definition `wasserstein1` (in `LeanPool/Vlasov/OT/Wasserstein.lean`)
via Kantorovich-Rubinstein duality.

We use the Lebesgue lower integral `∫⁻` of `edist` (extended distance, valued
in `ℝ≥0∞`) rather than the Bochner integral `∫` of `dist` (valued in `ℝ`).
This is the standard OT convention: a coupling π whose cost is non-integrable
contributes `⊤` to the infimum (rather than the Bochner junk-value 0), so the
infimum correctly identifies the OT-optimal coupling.  Returns `⊤` if no
coupling exists. -/
noncomputable def wasserstein1Coupling
    {α : Type*} [MeasurableSpace α] [PseudoMetricSpace α]
    (μ ν : Measure α) : ENNReal :=
  ⨅ (π : Measure (α × α)) (_ : IsCoupling π μ ν),
    ∫⁻ z, edist z.1 z.2 ∂π

/-! ## Kantorovich-Rubinstein: easy direction

The dual-formula `wasserstein1` is at most the coupling-formula
`wasserstein1Coupling`.  The one-line argument in the OT literature:
for any 1-Lipschitz `φ` and any coupling `π`,

  ∫φ d(μ - ν) = ∫(φ x - φ y) dπ ≤ ∫ |φ x - φ y| dπ ≤ ∫ dist(x,y) dπ.

The reverse inequality is the hard direction `wassersteinCostCoupling_le_dual`.
-/

/-- KR easy direction.  Under finite-moment assumptions on `μ` and `ν`, the
dual-formula `wasserstein1 μ ν` is bounded above by the coupling-formula
`wasserstein1Coupling μ ν`.

By `iSup_le` and `le_iInf`, it suffices to show that for every 1-Lipschitz `φ`
and every coupling `π` of `(μ, ν)`:
`ENNReal.ofReal (∫φ dμ − ∫φ dν) ≤ ∫⁻ edist z.1 z.2 ∂π`.  When the coupling cost
is `⊤` the bound is trivial; otherwise `edist`-integrability of `π` gives
`dist`-integrability, change of variables through the marginals rewrites
`∫φ dμ - ∫φ dν = ∫(φ(z.1) - φ(z.2)) dπ`, and `|φ(z.1) - φ(z.2)| ≤ dist(z.1, z.2)`
(1-Lipschitz) closes it (integrability via the finite first moments of `μ`, `ν`). -/
theorem wasserstein1_le_wasserstein1Coupling
    {α : Type*} [MeasurableSpace α] [PseudoMetricSpace α] [BorelSpace α]
    [SecondCountableTopology α]
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (x₀ : α)
    (hμ_fm : Integrable (fun y => dist y x₀) μ)
    (hν_fm : Integrable (fun y => dist y x₀) ν) :
    wasserstein1 μ ν ≤ wasserstein1Coupling μ ν := by
  rw [wasserstein1_eq_iSup_lipschitz]
  refine iSup_le fun φ => iSup_le fun hφ => ?_
  refine le_iInf fun π => le_iInf fun hπ => ?_
  -- Goal: ENNReal.ofReal (∫φ dμ - ∫φ dν) ≤ ∫⁻ z, edist z.1 z.2 ∂π
  by_cases h_top : ∫⁻ z, edist z.1 z.2 ∂π = ⊤
  · rw [h_top]; exact le_top
  push Not at h_top
  -- Step 1: π inherits IsProbabilityMeasure from its first marginal μ.
  haveI hπ_prob : IsProbabilityMeasure π := by
    refine ⟨?_⟩
    have h_eq : π Set.univ = μ Set.univ := by
      rw [← hπ.1, Measure.map_apply measurable_fst MeasurableSet.univ,
          Set.preimage_univ]
    rw [h_eq, measure_univ]
  -- Step 2: `dist z.1 z.2` is Integrable wrt π (from h_top, via edist = ofReal dist).
  have h_dist_meas : AEStronglyMeasurable (fun z : α × α => dist z.1 z.2) π :=
    (measurable_fst.dist measurable_snd).aestronglyMeasurable
  have h_enorm_eq : ∀ z : α × α, ‖dist z.1 z.2‖ₑ = edist z.1 z.2 := fun z => by
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg dist_nonneg, edist_dist]
  have h_dist_int : Integrable (fun z : α × α => dist z.1 z.2) π := by
    refine ⟨h_dist_meas, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    simp_rw [h_enorm_eq]
    exact h_top.lt_top
  -- Step 3: 1-Lipschitz φ is integrable wrt μ and wrt ν, via |φ y| ≤ |φ x₀| + dist y x₀
  -- and the finite-first-moment hypothesis on each marginal.
  have hφ_cont : Continuous φ := hφ.continuous
  have hφ_meas_μ : AEStronglyMeasurable φ μ := hφ_cont.aestronglyMeasurable
  have hφ_meas_ν : AEStronglyMeasurable φ ν := hφ_cont.aestronglyMeasurable
  have h_pt_bound : ∀ y, |φ y| ≤ |φ x₀| + dist y x₀ := fun y => by
    calc |φ y|
        = |(φ y - φ x₀) + φ x₀|             := by ring_nf
      _ ≤ |φ y - φ x₀| + |φ x₀|              := abs_add_le _ _
      _ ≤ dist y x₀ + |φ x₀|                 := by
            have := hφ.dist_le_mul y x₀
            rw [Real.dist_eq, NNReal.coe_one, one_mul] at this
            linarith
      _ = |φ x₀| + dist y x₀                 := by ring
  have h_dom_μ : Integrable (fun y => |φ x₀| + dist y x₀) μ :=
    (integrable_const _).add hμ_fm
  have h_dom_ν : Integrable (fun y => |φ x₀| + dist y x₀) ν :=
    (integrable_const _).add hν_fm
  have hφ_int_μ : Integrable φ μ :=
    h_dom_μ.mono hφ_meas_μ (Filter.Eventually.of_forall fun y => by
      simp only [Real.norm_eq_abs]
      rw [abs_of_nonneg (add_nonneg (abs_nonneg _) dist_nonneg)]
      exact h_pt_bound y)
  have hφ_int_ν : Integrable φ ν :=
    h_dom_ν.mono hφ_meas_ν (Filter.Eventually.of_forall fun y => by
      simp only [Real.norm_eq_abs]
      rw [abs_of_nonneg (add_nonneg (abs_nonneg _) dist_nonneg)]
      exact h_pt_bound y)
  -- Step 4: φ ∘ Prod.fst integrable wrt π (since fst-marginal = μ).
  have hφ_fst_meas : AEStronglyMeasurable (fun z : α × α => φ z.1) π :=
    (hφ_cont.comp continuous_fst).aestronglyMeasurable
  have hφ_snd_meas : AEStronglyMeasurable (fun z : α × α => φ z.2) π :=
    (hφ_cont.comp continuous_snd).aestronglyMeasurable
  have h_diff_bound : ∀ z : α × α, |φ z.1 - φ z.2| ≤ dist z.1 z.2 := fun z => by
    have := hφ.dist_le_mul z.1 z.2
    rwa [Real.dist_eq, NNReal.coe_one, one_mul] at this
  -- φ z.1 − φ z.2 is integrable wrt π (bounded by integrable dist).
  have h_diff_int : Integrable (fun z : α × α => φ z.1 - φ z.2) π :=
    h_dist_int.mono (hφ_fst_meas.sub hφ_snd_meas) (Filter.Eventually.of_forall fun z => by
      simp only [Real.norm_eq_abs]
      rw [abs_of_nonneg dist_nonneg]
      exact h_diff_bound z)
  -- Step 5: change of variables via marginals.
  have hφ_meas_pf : AEStronglyMeasurable φ (Measure.map Prod.fst π) := by
    rw [hπ.1]; exact hφ_meas_μ
  have hφ_meas_ps : AEStronglyMeasurable φ (Measure.map Prod.snd π) := by
    rw [hπ.2]; exact hφ_meas_ν
  have h_cov_μ : ∫ y, φ y ∂μ = ∫ z, φ z.1 ∂π := by
    conv_lhs => rw [← hπ.1]
    exact integral_map measurable_fst.aemeasurable hφ_meas_pf
  have h_cov_ν : ∫ y, φ y ∂ν = ∫ z, φ z.2 ∂π := by
    conv_lhs => rw [← hπ.2]
    exact integral_map measurable_snd.aemeasurable hφ_meas_ps
  -- ∫(φ z.1) dπ and ∫(φ z.2) dπ are individually integrable.
  have hφ_fst_int : Integrable (fun z : α × α => φ z.1) π := by
    have h := hφ_int_μ
    rw [← hπ.1] at h
    exact (integrable_map_measure hφ_meas_pf measurable_fst.aemeasurable).mp h
  have hφ_snd_int : Integrable (fun z : α × α => φ z.2) π := by
    have h := hφ_int_ν
    rw [← hπ.2] at h
    exact (integrable_map_measure hφ_meas_ps measurable_snd.aemeasurable).mp h
  -- Step 6: ∫φ dμ − ∫φ dν = ∫(φ z.1 − φ z.2) dπ
  rw [h_cov_μ, h_cov_ν, ← integral_sub hφ_fst_int hφ_snd_int]
  -- Step 7: bound the integrand by dist (using 1-Lip), then integrate.
  have h_real_bound : ∫ z, (φ z.1 - φ z.2) ∂π ≤ ∫ z, dist z.1 z.2 ∂π := by
    apply integral_mono_ae h_diff_int h_dist_int
    exact Filter.Eventually.of_forall fun z => (le_abs_self _).trans (h_diff_bound z)
  -- Step 8: ofReal(∫(φ z.1 − φ z.2) dπ) ≤ ofReal(∫ dist dπ) = ∫⁻ edist dπ.
  refine (ENNReal.ofReal_le_ofReal h_real_bound).trans ?_
  -- ofReal(∫ dist dπ) = ∫⁻ ofReal(dist) dπ = ∫⁻ edist dπ
  rw [ofReal_integral_eq_lintegral_ofReal h_dist_int
        (Filter.Eventually.of_forall fun _ => dist_nonneg)]
  -- ∫⁻ ofReal(dist z.1 z.2) ∂π ≤ ∫⁻ edist z.1 z.2 ∂π  (equal pointwise via edist_dist)
  apply le_of_eq
  apply lintegral_congr
  intro z
  exact (edist_dist z.1 z.2).symm

/-! ## Hard Kantorovich–Rubinstein duality

This section proves the hard direction `wassersteinCostCoupling_le_dual`
(coupling-inf ≤ dual-sup) and derives the KR equality from it together with the
easy direction above.  Everything is stated **cost-generically** over a
continuous pseudometric cost `c`, so an alternative cutoff cost
`c = min (dist ·) 1` instantiates the same statements verbatim.
-/

/-- Cost-generic coupling cost: the infimum over couplings `π` of `(μ, ν)` of
`∫⁻ ofReal (c z.1 z.2) ∂π`.  At `c = dist` this is `wasserstein1Coupling`
(`edist = ofReal ∘ dist`); see `wasserstein1Coupling_eq`. -/
noncomputable def wassersteinCostCoupling
    {α : Type*} [MeasurableSpace α]
    (c : α → α → ℝ) (μ ν : Measure α) : ENNReal :=
  ⨅ (π : Measure (α × α)) (_ : IsCoupling π μ ν),
    ∫⁻ z, ENNReal.ofReal (c z.1 z.2) ∂π

/-- At `c = dist`, the cost-generic coupling cost reduces to `wasserstein1Coupling`
(since `edist x y = ofReal (dist x y)`). -/
lemma wasserstein1Coupling_eq
    {α : Type*} [MeasurableSpace α] [PseudoMetricSpace α] (μ ν : Measure α) :
    wasserstein1Coupling μ ν = wassersteinCostCoupling (fun x y => dist x y) μ ν := by
  unfold wasserstein1Coupling wassersteinCostCoupling
  refine iInf_congr fun π => iInf_congr fun _ => ?_
  exact lintegral_congr fun z => edist_dist z.1 z.2

/-! ### Kantorovich–Rubinstein duality (hard direction) helpers

The lemmas below decompose `wassersteinCostCoupling_le_dual` via discrete
approximation + limit.  All are general optimal-transport facts (not
Vlasov-specific), stated cost-generically over a continuous pseudometric cost.
-/

/-- **Symmetry of the coupling cost.**
For a symmetric cost, `wassersteinCostCoupling c μ ν = wassersteinCostCoupling c ν μ`
(push a coupling forward under `Prod.swap`). -/
theorem wassersteinCostCoupling_comm
    {α : Type*} [MeasurableSpace α]
    (c : α → α → ℝ) (hc_symm : ∀ x y, c x y = c y x)
    (hc_meas : Measurable (fun p : α × α => c p.1 p.2))
    (μ ν : Measure α) :
    wassersteinCostCoupling c μ ν = wassersteinCostCoupling c ν μ := by
  -- One direction; the swap of a coupling of (a,b) is a coupling of (b,a) with equal cost.
  have key : ∀ (a b : Measure α),
      wassersteinCostCoupling c a b ≤ wassersteinCostCoupling c b a := by
    intro a b
    unfold wassersteinCostCoupling
    refine le_iInf fun π => le_iInf fun hπ => ?_
    -- π : IsCoupling π b a; `map swap π` couples (a, b).
    have hswap : IsCoupling (Measure.map Prod.swap π) a b := by
      refine ⟨?_, ?_⟩
      · rw [Measure.map_map measurable_fst measurable_swap]; exact hπ.2
      · rw [Measure.map_map measurable_snd measurable_swap]; exact hπ.1
    refine iInf_le_of_le (Measure.map Prod.swap π) (iInf_le_of_le hswap (le_of_eq ?_))
    calc ∫⁻ z, ENNReal.ofReal (c z.1 z.2) ∂(Measure.map Prod.swap π)
        = ∫⁻ z, ENNReal.ofReal (c (Prod.swap z).1 (Prod.swap z).2) ∂π :=
          lintegral_map (ENNReal.measurable_ofReal.comp hc_meas) measurable_swap
      _ = ∫⁻ z, ENNReal.ofReal (c z.1 z.2) ∂π := by
          refine lintegral_congr fun z => ?_
          simp only [Prod.fst_swap, Prod.snd_swap]
          exact congrArg ENNReal.ofReal (hc_symm z.2 z.1)
  exact le_antisymm (key μ ν) (key ν μ)

/-- **Gluing of couplings.**  Given a
coupling `π₁` of `(μ, ρ)` and a coupling `π₂` of `(ρ, ν)`, disintegrating `π₂` over
its `ρ`-marginal (`condKernel`) and re-binding along `π₁`'s `ρ`-marginal yields a
coupling `π₃` of `(μ, ν)` whose cost is at most the sum of the two costs (ground-cost
triangle `c x z ≤ c x y + c y z`).  The load-bearing facts are the two marginals
(`map fst π₃ = μ` via `fst_compProd`; `map snd π₃ = ν` via `snd_compProd` + the
`bind`/`map`/`comap` law). -/
theorem exists_coupling_glue
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α]
    (c : α → α → ℝ)
    (hc_triangle : ∀ x y z, c x z ≤ c x y + c y z)
    (hc_meas : Measurable (fun p : α × α => c p.1 p.2))
    (μ ν ρ : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ρ]
    (π₁ : Measure (α × α)) (h₁ : IsCoupling π₁ μ ρ)
    (π₂ : Measure (α × α)) (h₂ : IsCoupling π₂ ρ ν) :
    ∃ π₃ : Measure (α × α), IsCoupling π₃ μ ν ∧
      ∫⁻ z, ENNReal.ofReal (c z.1 z.2) ∂π₃
        ≤ (∫⁻ z, ENNReal.ofReal (c z.1 z.2) ∂π₁)
          + (∫⁻ z, ENNReal.ofReal (c z.1 z.2) ∂π₂) := by
  haveI : Nonempty α := nonempty_of_isProbabilityMeasure μ
  haveI hπ₁ : IsProbabilityMeasure π₁ := by
    constructor
    have h : π₁ Set.univ = μ Set.univ := by
      rw [← h₁.1, Measure.map_apply measurable_fst MeasurableSet.univ, Set.preimage_univ]
    rw [h, measure_univ]
  haveI hπ₂ : IsProbabilityMeasure π₂ := by
    constructor
    have h : π₂ Set.univ = ρ Set.univ := by
      rw [← h₂.1, Measure.map_apply measurable_fst MeasurableSet.univ, Set.preimage_univ]
    rw [h, measure_univ]
  set κ₂ : Kernel α α := π₂.condKernel with hκ₂
  haveI : IsMarkovKernel κ₂ := by rw [hκ₂]; infer_instance
  set κ₂' : Kernel (α × α) α := κ₂.comap Prod.snd measurable_snd with hκ₂'
  set glued : Measure ((α × α) × α) := π₁ ⊗ₘ κ₂' with hglued
  set proj : (α × α) × α → α × α := fun w => (w.1.1, w.2) with hproj
  have hproj_meas : Measurable proj :=
    (measurable_fst.comp measurable_fst).prodMk measurable_snd
  have hg : Measurable (fun z : α × α => ENNReal.ofReal (c z.1 z.2)) :=
    ENNReal.measurable_ofReal.comp hc_meas
  have hdisint : π₂.fst ⊗ₘ κ₂ = π₂ := by
    rw [hκ₂]; exact Measure.disintegrate π₂ π₂.condKernel
  have hρπ₂ : ρ ⊗ₘ κ₂ = π₂ := by rw [show ρ = π₂.fst from h₂.1.symm]; exact hdisint
  refine ⟨glued.map proj, ⟨?_, ?_⟩, ?_⟩
  · -- fst marginal = μ
    rw [Measure.map_map measurable_fst hproj_meas]
    have hcomp : (Prod.fst ∘ proj) = (Prod.fst ∘ Prod.fst : (α × α) × α → α) := rfl
    rw [hcomp, ← Measure.map_map measurable_fst measurable_fst,
      show Measure.map Prod.fst glued = π₁ from Measure.fst_compProd π₁ κ₂']
    exact h₁.1
  · -- snd marginal = ν
    rw [Measure.map_map measurable_snd hproj_meas]
    have hcomp : (Prod.snd ∘ proj) = (Prod.snd : (α × α) × α → α) := rfl
    rw [hcomp, show Measure.map Prod.snd glued = κ₂' ∘ₘ π₁ from Measure.snd_compProd π₁ κ₂']
    have hLHS : κ₂' ∘ₘ π₁ = Measure.bind π₁ (fun p => κ₂ p.2) :=
      Measure.bind_congr_right
        (Filter.Eventually.of_forall fun p => Kernel.comap_apply κ₂ measurable_snd p)
    have hbindmap : κ₂ ∘ₘ (Measure.map Prod.snd π₁) = Measure.bind π₁ (fun p => κ₂ p.2) := by
      rw [show Measure.map Prod.snd π₁ = Measure.bind π₁ (fun p => Measure.dirac p.2) from
            (Measure.bind_dirac_eq_map π₁ measurable_snd).symm,
        show (κ₂ ∘ₘ Measure.bind π₁ (fun p => Measure.dirac p.2))
            = Measure.bind (Measure.bind π₁ (fun p => Measure.dirac p.2)) κ₂ from rfl,
        Measure.bind_bind
          (by fun_prop : Measurable (fun p : α × α => Measure.dirac p.2)).aemeasurable
          κ₂.aemeasurable]
      exact Measure.bind_congr_right
        (Filter.Eventually.of_forall fun p => Measure.dirac_bind κ₂.measurable p.2)
    have hRHS : ν = Measure.bind π₁ (fun p => κ₂ p.2) := by
      calc ν = π₂.snd := h₂.2.symm
        _ = (π₂.fst ⊗ₘ κ₂).snd := by rw [hdisint]
        _ = κ₂ ∘ₘ π₂.fst := Measure.snd_compProd π₂.fst κ₂
        _ = κ₂ ∘ₘ ρ := by rw [show π₂.fst = ρ from h₂.1]
        _ = κ₂ ∘ₘ (Measure.map Prod.snd π₁) := by
            rw [show ρ = Measure.map Prod.snd π₁ from h₁.2.symm]
        _ = Measure.bind π₁ (fun p => κ₂ p.2) := hbindmap
    rw [hLHS, hRHS]
  · -- cost bound: lintegral_compProd (Tonelli) + ground-cost triangle + Markov.
    have hF : Measurable (fun w : (α × α) × α => ENNReal.ofReal (c w.1.1 w.2)) :=
      hg.comp hproj_meas
    have hLcost : ∫⁻ z, ENNReal.ofReal (c z.1 z.2) ∂(glued.map proj)
        = ∫⁻ p, ∫⁻ z, ENNReal.ofReal (c p.1 z) ∂(κ₂ p.2) ∂π₁ := by
      rw [hglued]
      calc ∫⁻ z, ENNReal.ofReal (c z.1 z.2) ∂((π₁ ⊗ₘ κ₂').map proj)
          = ∫⁻ w, ENNReal.ofReal (c w.1.1 w.2) ∂(π₁ ⊗ₘ κ₂') := by
            rw [lintegral_map hg hproj_meas]
        _ = ∫⁻ p, ∫⁻ z, ENNReal.ofReal (c p.1 z) ∂(κ₂' p) ∂π₁ := Measure.lintegral_compProd hF
        _ = ∫⁻ p, ∫⁻ z, ENNReal.ofReal (c p.1 z) ∂(κ₂ p.2) ∂π₁ := by
            simp only [hκ₂', Kernel.comap_apply]
    -- the c(y,z) leaf: the second piece reduces to the π₂-cost (sibling of snd-marginal).
    have hkey2 : ∫⁻ p, (∫⁻ z, ENNReal.ofReal (c p.2 z) ∂(κ₂ p.2)) ∂π₁
        = ∫⁻ z, ENNReal.ofReal (c z.1 z.2) ∂π₂ := by
      have hF_meas : Measurable (fun y : α => ∫⁻ z, ENNReal.ofReal (c y z) ∂(κ₂ y)) :=
        Measurable.lintegral_kernel_prod_right' hg
      calc ∫⁻ p, (∫⁻ z, ENNReal.ofReal (c p.2 z) ∂(κ₂ p.2)) ∂π₁
          = ∫⁻ y, (∫⁻ z, ENNReal.ofReal (c y z) ∂(κ₂ y)) ∂(Measure.map Prod.snd π₁) :=
            (lintegral_map hF_meas measurable_snd).symm
        _ = ∫⁻ y, (∫⁻ z, ENNReal.ofReal (c y z) ∂(κ₂ y)) ∂ρ := by rw [h₁.2]
        _ = ∫⁻ w, ENNReal.ofReal (c w.1 w.2) ∂(ρ ⊗ₘ κ₂) := (Measure.lintegral_compProd hg).symm
        _ = ∫⁻ z, ENNReal.ofReal (c z.1 z.2) ∂π₂ := by rw [hρπ₂]
    rw [hLcost]
    have hbound : ∫⁻ p, ∫⁻ z, ENNReal.ofReal (c p.1 z) ∂(κ₂ p.2) ∂π₁
        ≤ ∫⁻ p, (ENNReal.ofReal (c p.1 p.2)
            + ∫⁻ z, ENNReal.ofReal (c p.2 z) ∂(κ₂ p.2)) ∂π₁ := by
      refine lintegral_mono fun p => ?_
      calc ∫⁻ z, ENNReal.ofReal (c p.1 z) ∂(κ₂ p.2)
          ≤ ∫⁻ z, (ENNReal.ofReal (c p.1 p.2) + ENNReal.ofReal (c p.2 z)) ∂(κ₂ p.2) := by
            refine lintegral_mono fun z => ?_
            exact (ENNReal.ofReal_le_ofReal (hc_triangle p.1 p.2 z)).trans ENNReal.ofReal_add_le
        _ = ENNReal.ofReal (c p.1 p.2) + ∫⁻ z, ENNReal.ofReal (c p.2 z) ∂(κ₂ p.2) := by
            rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
    refine hbound.trans (le_of_eq ?_)
    rw [lintegral_add_left hg, hkey2]

/-- **Triangle inequality for the
coupling cost.**  Gluing of couplings through a common middle measure
(`exists_coupling_glue`), then the `iInf` arithmetic. -/
theorem wassersteinCostCoupling_triangle
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α]
    (c : α → α → ℝ)
    (hc_triangle : ∀ x y z, c x z ≤ c x y + c y z)
    (hc_meas : Measurable (fun p : α × α => c p.1 p.2))
    (μ ν ρ : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ρ] :
    wassersteinCostCoupling c μ ν
      ≤ wassersteinCostCoupling c μ ρ + wassersteinCostCoupling c ρ ν := by
  -- ε→0; the ⊤-case is the clean early-out (le_of_forall_pos_le_add supplies RHS < ⊤).
  refine ENNReal.le_of_forall_pos_le_add fun ε hε hAB => ?_
  have hAfin : wassersteinCostCoupling c μ ρ < ⊤ := (ENNReal.add_lt_top.mp hAB).1
  have hBfin : wassersteinCostCoupling c ρ ν < ⊤ := (ENNReal.add_lt_top.mp hAB).2
  have hδ : (0 : ℝ≥0∞) < (ε : ℝ≥0∞) / 2 :=
    ENNReal.div_pos (ENNReal.coe_pos.mpr hε).ne' (by norm_num)
  -- ε-optimal couplings (free from the iInf — no attainment needed).
  obtain ⟨π₁, h₁, hc₁⟩ : ∃ π₁, IsCoupling π₁ μ ρ ∧
      (∫⁻ z, ENNReal.ofReal (c z.1 z.2) ∂π₁) < wassersteinCostCoupling c μ ρ + (ε : ℝ≥0∞) / 2 := by
    have hlt : wassersteinCostCoupling c μ ρ < wassersteinCostCoupling c μ ρ + (ε : ℝ≥0∞) / 2 :=
      ENNReal.lt_add_right hAfin.ne hδ.ne'
    unfold wassersteinCostCoupling at hlt
    rw [iInf_lt_iff] at hlt
    obtain ⟨π, hπ⟩ := hlt
    rw [iInf_lt_iff] at hπ
    obtain ⟨h, hcost⟩ := hπ
    exact ⟨π, h, hcost⟩
  obtain ⟨π₂, h₂, hc₂⟩ : ∃ π₂, IsCoupling π₂ ρ ν ∧
      (∫⁻ z, ENNReal.ofReal (c z.1 z.2) ∂π₂) < wassersteinCostCoupling c ρ ν + (ε : ℝ≥0∞) / 2 := by
    have hlt : wassersteinCostCoupling c ρ ν < wassersteinCostCoupling c ρ ν + (ε : ℝ≥0∞) / 2 :=
      ENNReal.lt_add_right hBfin.ne hδ.ne'
    unfold wassersteinCostCoupling at hlt
    rw [iInf_lt_iff] at hlt
    obtain ⟨π, hπ⟩ := hlt
    rw [iInf_lt_iff] at hπ
    obtain ⟨h, hcost⟩ := hπ
    exact ⟨π, h, hcost⟩
  obtain ⟨π₃, h₃, hcost⟩ :=
    exists_coupling_glue c hc_triangle hc_meas μ ν ρ π₁ h₁ π₂ h₂
  calc wassersteinCostCoupling c μ ν
      ≤ ∫⁻ z, ENNReal.ofReal (c z.1 z.2) ∂π₃ :=
        iInf_le_of_le π₃ (iInf_le_of_le h₃ le_rfl)
    _ ≤ (∫⁻ z, ENNReal.ofReal (c z.1 z.2) ∂π₁)
          + (∫⁻ z, ENNReal.ofReal (c z.1 z.2) ∂π₂) := hcost
    _ ≤ (wassersteinCostCoupling c μ ρ + (ε : ℝ≥0∞) / 2)
          + (wassersteinCostCoupling c ρ ν + (ε : ℝ≥0∞) / 2) := add_le_add hc₁.le hc₂.le
    _ = wassersteinCostCoupling c μ ρ + wassersteinCostCoupling c ρ ν + (ε : ℝ≥0∞) := by
        rw [add_add_add_comm, ENNReal.add_halves]

/-- **Graph-coupling bound.**  The
coupling cost between `μ` and a pushforward `Measure.map T μ` is at most the
integrated transport cost of `T`, witnessed by the graph coupling
`(id, T)_# μ`. -/
theorem wassersteinCostCoupling_map_le
    {α : Type*} [MeasurableSpace α] [PseudoMetricSpace α] [BorelSpace α]
    [SecondCountableTopology α]
    (c : α → α → ℝ) (hc_cont : Continuous (fun p : α × α => c p.1 p.2))
    (μ : Measure α)
    (T : α → α) (hT : Measurable T) :
    wassersteinCostCoupling c μ (Measure.map T μ)
      ≤ ∫⁻ x, ENNReal.ofReal (c x (T x)) ∂μ := by
  -- the graph coupling `(id, T)_# μ` couples `μ` and `T_# μ`; its cost is the integral.
  have hg : Measurable (fun x : α => (x, T x)) := measurable_id.prodMk hT
  have hγ : IsCoupling (Measure.map (fun x => (x, T x)) μ) μ (Measure.map T μ) := by
    refine ⟨?_, ?_⟩
    · rw [Measure.map_map measurable_fst hg]
      rw [show (Prod.fst ∘ fun x : α => (x, T x)) = id from rfl, Measure.map_id]
    · rw [Measure.map_map measurable_snd hg]; rfl
  unfold wassersteinCostCoupling
  refine iInf_le_of_le (Measure.map (fun x => (x, T x)) μ) (iInf_le_of_le hγ (le_of_eq ?_))
  calc ∫⁻ z, ENNReal.ofReal (c z.1 z.2) ∂(Measure.map (fun x => (x, T x)) μ)
      = ∫⁻ x, ENNReal.ofReal (c (x, T x).1 (x, T x).2) ∂μ :=
        lintegral_map (ENNReal.measurable_ofReal.comp hc_cont.measurable) hg
    _ = ∫⁻ x, ENNReal.ofReal (c x (T x)) ∂μ := rfl

/-- **Finite-range step map construction.**
Given a measurable pairwise-disjoint partition `As : ℕ → Set α` covering `univ` with
representatives `as : ℕ → α` and a fallback point `x₀`, the truncated step map
`T x = as n` when `x ∈ As n` for some `n < N`, `T x = x₀` otherwise, is measurable
and has finite range contained in `{as n | n < N} ∪ {x₀}`. -/
lemma finiteRange_approxMap_measurable
    {α : Type*} [MeasurableSpace α]
    (As : ℕ → Set α) (hAs_mble : ∀ n, MeasurableSet (As n))
    (hAs_disj : Pairwise fun n m => Disjoint (As n) (As m))
    (as : ℕ → α) (x₀ : α) (N : ℕ) :
    ∃ T : α → α,
      Measurable T ∧
      (Set.range T).Finite ∧
      (∀ n < N, ∀ x ∈ As n, T x = as n) ∧
      (∀ x ∈ (⋃ n ∈ Finset.range N, As n)ᶜ, T x = x₀) := by
  classical
  -- measurability of the recursive step map, for any list of indices
  have hmeas : ∀ l : List ℕ,
      Measurable (fun x => l.foldr (fun n acc => if x ∈ As n then as n else acc) x₀) := by
    intro l
    induction l with
    | nil => simp only [List.foldr_nil]; exact measurable_const
    | cons k l ih =>
      simp only [List.foldr_cons]
      exact Measurable.ite (hAs_mble k) measurable_const ih
  -- the folded value is always `x₀` or `as k` for some `k` in the list
  have hval : ∀ (l : List ℕ) (x : α),
      (l.foldr (fun n acc => if x ∈ As n then as n else acc) x₀ = x₀) ∨
      (∃ k ∈ l, l.foldr (fun n acc => if x ∈ As n then as n else acc) x₀ = as k) := by
    intro l
    induction l with
    | nil => intro x; left; rfl
    | cons k l ih =>
      intro x
      simp only [List.foldr_cons]
      by_cases hk : x ∈ As k
      · right; exact ⟨k, List.mem_cons_self, if_pos hk⟩
      · rw [if_neg hk]
        rcases ih x with h | ⟨k', hk', h⟩
        · left; exact h
        · right; exact ⟨k', List.mem_cons_of_mem k hk', h⟩
  -- kept property: disjointness pins the matched index
  have hkept : ∀ (l : List ℕ) (x : α) (n : ℕ), n ∈ l → x ∈ As n →
      (∀ m ∈ l, x ∈ As m → m = n) →
      l.foldr (fun n acc => if x ∈ As n then as n else acc) x₀ = as n := by
    intro l
    induction l with
    | nil => intro x n hn _ _; simp at hn
    | cons k l ih =>
      intro x n hn hxn huniq
      simp only [List.foldr_cons]
      by_cases hk : x ∈ As k
      · rw [if_pos hk, huniq k (List.mem_cons_self) hk]
      · rw [if_neg hk]
        have hnk : n ≠ k := fun h => hk (h ▸ hxn)
        have hnl : n ∈ l := (List.mem_cons.mp hn).resolve_left hnk
        exact ih x n hnl hxn (fun m hm hxm => huniq m (List.mem_cons_of_mem k hm) hxm)
  -- tail property: off all cells the fold returns the fallback
  have htail : ∀ (l : List ℕ) (x : α), (∀ m ∈ l, x ∉ As m) →
      l.foldr (fun n acc => if x ∈ As n then as n else acc) x₀ = x₀ := by
    intro l
    induction l with
    | nil => intro x _; rfl
    | cons k l ih =>
      intro x hx
      simp only [List.foldr_cons]
      rw [if_neg (hx k (List.mem_cons_self))]
      exact ih x (fun m hm => hx m (List.mem_cons_of_mem k hm))
  refine ⟨fun x => (List.range N).foldr (fun n acc => if x ∈ As n then as n else acc) x₀,
    hmeas (List.range N), ?_, ?_, ?_⟩
  · -- finite range
    apply Set.Finite.subset ((((Finset.range N).finite_toSet).image as).insert x₀)
    rintro _ ⟨x, rfl⟩
    simp only []
    rcases hval (List.range N) x with h | ⟨k, hk, h⟩
    · rw [h]; exact Set.mem_insert _ _
    · rw [h]
      exact Set.mem_insert_of_mem _
        (Set.mem_image_of_mem as
          (Finset.mem_coe.mpr (Finset.mem_range.mpr (List.mem_range.mp hk))))
  · -- kept
    intro n hn x hx
    refine hkept (List.range N) x n (List.mem_range.mpr hn) hx (fun m hm hxm => ?_)
    by_contra hmn
    exact absurd hx (Set.disjoint_left.mp (hAs_disj hmn) hxm)
  · -- tail
    intro x hx
    refine htail (List.range N) x (fun m hm hxm => ?_)
    exact hx (Set.mem_iUnion₂.mpr ⟨m, Finset.mem_range.mpr (List.mem_range.mp hm), hxm⟩)

/-- **Integrable nonneg → lintegral ofReal finite.**
If `f : α → ℝ` is integrable with respect to `μ` and a.e. nonneg, then
`∫⁻ x, ENNReal.ofReal (f x) ∂μ ≠ ∞`.
Key tools: `hasFiniteIntegral_iff_ofReal` and `Integrable.hasFiniteIntegral`. -/
lemma lintegral_ofReal_ne_top_of_integrable_nonneg
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} (hf : Integrable f μ) (hfnn : ∀ᵐ x ∂μ, 0 ≤ f x) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≠ ∞ := by
  rw [← lt_top_iff_ne_top]
  exact (hasFiniteIntegral_iff_ofReal hfnn).mp hf.hasFiniteIntegral

/-- **Tail cost control via absolute continuity.**
If `∫⁻ x, ENNReal.ofReal (f x) ∂μ ≠ ∞` and `μ ((S n)ᶜ) → 0` as `n → ∞`, then the tail
costs `∫⁻ x in (S n)ᶜ, ENNReal.ofReal (f x) ∂μ → 0`.
Follows from `MeasureTheory.tendsto_setLIntegral_zero` (absolute continuity of the integral). -/
lemma lintegral_ofReal_tail_tendsto_zero
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} (hfint : ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≠ ∞)
    {S : ℕ → Set α}
    (hS_tendsto : Filter.Tendsto (fun n => μ ((S n)ᶜ)) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => ∫⁻ x in (S n)ᶜ, ENNReal.ofReal (f x) ∂μ)
      Filter.atTop (nhds 0) := by
  exact tendsto_setLIntegral_zero hfint hS_tendsto

/-- **Kept-cells cost bound.**
For a step map `T` with `T x = as n` on `As n` (for `n < N`), where we have a pointwise
bound `∀ n < N, ∀ x ∈ As n, c x (T x) ≤ δ` (established from the cell diameter), the
lintegral of `ENNReal.ofReal (c x (T x))` over the kept cells is at most `ENNReal.ofReal δ`
since `μ univ = 1`. -/
lemma lintegral_ofReal_kept_cells_le
    {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ]
    (c : α → α → ℝ)
    (As : ℕ → Set α)
    (N : ℕ) (δ : ℝ)
    (T : α → α)
    (hcT_le : ∀ n < N, ∀ x ∈ As n, c x (T x) ≤ δ) :
    ∫⁻ x in ⋃ n ∈ Finset.range N, As n, ENNReal.ofReal (c x (T x)) ∂μ
      ≤ ENNReal.ofReal δ := by
  have hpt : ∀ x ∈ (⋃ n ∈ Finset.range N, As n),
      ENNReal.ofReal (c x (T x)) ≤ ENNReal.ofReal δ := by
    intro x hx
    rw [Set.mem_iUnion₂] at hx
    obtain ⟨n, hn, hxn⟩ := hx
    exact ENNReal.ofReal_le_ofReal (hcT_le n (Finset.mem_range.mp hn) x hxn)
  calc ∫⁻ x in ⋃ n ∈ Finset.range N, As n, ENNReal.ofReal (c x (T x)) ∂μ
      ≤ ∫⁻ _ in ⋃ n ∈ Finset.range N, As n, ENNReal.ofReal δ ∂μ :=
        setLIntegral_mono measurable_const hpt
    _ = ENNReal.ofReal δ * μ (⋃ n ∈ Finset.range N, As n) := setLIntegral_const _ _
    _ ≤ ENNReal.ofReal δ * 1 := by gcongr; exact prob_le_one
    _ = ENNReal.ofReal δ := mul_one _

/-- **Tail mass of a measurable cover → 0.**
For a finite measure and a measurable cover `⋃ n, As n = univ`, the mass of the complement
of the partial unions `⋃ j < n, As j` tends to `0` (continuity from above:
`⋂ n (⋃ j<n As j)ᶜ = ∅`). -/
lemma measure_compl_biUnion_range_tendsto_zero
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {As : ℕ → Set α} (hAs_mble : ∀ n, MeasurableSet (As n))
    (hAs_cover : ⋃ n, As n = Set.univ) :
    Filter.Tendsto (fun n => μ ((⋃ j ∈ Finset.range n, As j)ᶜ)) Filter.atTop (nhds 0) := by
  -- partial unions are monotone, so their complements are antitone
  have hBmono : ∀ a b : ℕ, a ≤ b →
      (⋃ j ∈ Finset.range a, As j) ⊆ (⋃ j ∈ Finset.range b, As j) := by
    intro a b hab x hx
    rw [Set.mem_iUnion₂] at hx ⊢
    obtain ⟨j, hj, hxj⟩ := hx
    exact ⟨j, Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hj) hab), hxj⟩
  have hanti : Antitone (fun n => (⋃ j ∈ Finset.range n, As j)ᶜ) :=
    fun a b hab => Set.compl_subset_compl.mpr (hBmono a b hab)
  have hmeas : ∀ n, MeasurableSet ((⋃ j ∈ Finset.range n, As j)ᶜ) :=
    fun n => (MeasurableSet.biUnion (Finset.countable_toSet _) (fun j _ => hAs_mble j)).compl
  -- the union of all partial unions is everything
  have hUnion : (⋃ n, ⋃ j ∈ Finset.range n, As j) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    have hxu : x ∈ ⋃ j, As j := by rw [hAs_cover]; exact Set.mem_univ x
    rw [Set.mem_iUnion] at hxu
    obtain ⟨j, hxj⟩ := hxu
    rw [Set.mem_iUnion]
    exact ⟨j + 1, Set.mem_iUnion₂.mpr ⟨j, Finset.mem_range.mpr (Nat.lt_succ_self j), hxj⟩⟩
  have hInter : (⋂ n, (⋃ j ∈ Finset.range n, As j)ᶜ) = ∅ := by
    rw [← Set.compl_iUnion, hUnion, Set.compl_univ]
  have key := tendsto_measure_iInter_atTop (μ := μ)
    (fun n => (hmeas n).nullMeasurableSet) hanti ⟨0, measure_ne_top μ _⟩
  rw [hInter, measure_empty] at key
  exact key

/-- **Finite-range approximation.**
For a probability measure with finite first moment, the transport cost to a
finite-range pushforward can be made arbitrarily small (partition into
small-diameter cells + finite-moment tail control). -/
theorem exists_finiteRange_map_cost_le
    {α : Type*} [MeasurableSpace α] [PseudoMetricSpace α] [BorelSpace α]
    [SecondCountableTopology α]
    (c : α → α → ℝ) (_hc_nonneg : ∀ x y, 0 ≤ c x y)
    (hc_le_dist : ∀ x y, c x y ≤ dist x y)
    (μ : Measure α) [IsProbabilityMeasure μ] (x₀ : α)
    (_hμ_cm : Integrable (fun y => c y x₀) μ)
    (ε : ℝ) (_hε : 0 < ε) :
    ∃ T : α → α, Measurable T ∧ (Set.range T).Finite ∧
      ∫⁻ x, ENNReal.ofReal (c x (T x)) ∂μ ≤ ENNReal.ofReal ε := by
  -- Step 1: get a dist-diameter partition (cells of diam ≤ ε/2)
  haveI : TopologicalSpace.SeparableSpace α := inferInstance
  obtain ⟨As, hAs_mble, hAs_bdd, hAs_diam, hAs_cover, hAs_disj⟩ :=
    SeparableSpace.exists_measurable_partition_diam_le α (half_pos _hε)
  -- per-cell representatives (x₀ on empty cells)
  classical
  set as : ℕ → α := fun n => if h : (As n).Nonempty then h.some else x₀ with has_def
  -- Step 2: lintegral ofReal (c · x₀) is finite
  have hfint : ∫⁻ x, ENNReal.ofReal (c x x₀) ∂μ ≠ ∞ :=
    lintegral_ofReal_ne_top_of_integrable_nonneg _hμ_cm
      (Filter.Eventually.of_forall (fun x => _hc_nonneg x x₀))
  -- Step 3: tail mass μ (⋃ j ∈ range n, As j)ᶜ → 0
  have htail_mass : Filter.Tendsto (fun n => μ ((⋃ j ∈ Finset.range n, As j)ᶜ))
      Filter.atTop (nhds 0) :=
    measure_compl_biUnion_range_tendsto_zero hAs_mble hAs_cover
  -- Step 4: tail costs → 0
  have htail_cost : Filter.Tendsto
      (fun n => ∫⁻ x in (⋃ j ∈ Finset.range n, As j)ᶜ, ENNReal.ofReal (c x x₀) ∂μ)
      Filter.atTop (nhds 0) :=
    lintegral_ofReal_tail_tendsto_zero hfint htail_mass
  -- Step 5: extract N with tail cost ≤ ε/2
  obtain ⟨N, hN⟩ : ∃ N, ∫⁻ x in (⋃ j ∈ Finset.range N, As j)ᶜ, ENNReal.ofReal (c x x₀) ∂μ ≤
      ENNReal.ofReal (ε / 2) := by
    rw [ENNReal.tendsto_nhds_zero] at htail_cost
    have hev := htail_cost (ENNReal.ofReal (ε / 2)) (ENNReal.ofReal_pos.mpr (half_pos _hε))
    rw [Filter.eventually_atTop] at hev
    obtain ⟨N, hN⟩ := hev
    exact ⟨N, hN N le_rfl⟩
  -- Step 6: build finite-range step map T sending each kept cell `As n` to its
  -- representative `as n` (and the tail to `x₀`).
  obtain ⟨T, hT_mble, hT_fin, hT_kept, hT_tail⟩ :=
    finiteRange_approxMap_measurable As hAs_mble hAs_disj as x₀ N
  refine ⟨T, hT_mble, hT_fin, ?_⟩
  -- Step 7: decompose the total lintegral into kept + tail parts
  have hS_mble : MeasurableSet (⋃ n ∈ Finset.range N, As n) :=
    MeasurableSet.biUnion (Finset.countable_toSet _) (fun n _ => hAs_mble n)
  rw [show ∫⁻ x, ENNReal.ofReal (c x (T x)) ∂μ =
      ∫⁻ x in ⋃ n ∈ Finset.range N, As n, ENNReal.ofReal (c x (T x)) ∂μ +
      ∫⁻ x in (⋃ n ∈ Finset.range N, As n)ᶜ, ENNReal.ofReal (c x (T x)) ∂μ
    from (lintegral_add_compl _ hS_mble).symm]
  -- Step 8a: bound kept cells via the kept-cell lemma
  have hkept : ∫⁻ x in ⋃ n ∈ Finset.range N, As n, ENNReal.ofReal (c x (T x)) ∂μ ≤
      ENNReal.ofReal (ε / 2) :=
    lintegral_ofReal_kept_cells_le c As N (ε / 2) T
      (fun n hn x hx => by
        rw [hT_kept n hn x hx]
        have hxn : (As n).Nonempty := ⟨x, hx⟩
        have hasn : as n ∈ As n := by
          simp only [has_def, dif_pos hxn]; exact hxn.some_mem
        calc c x (as n) ≤ dist x (as n) := hc_le_dist x (as n)
          _ ≤ Metric.diam (As n) := Metric.dist_le_diam_of_mem (hAs_bdd n) hx hasn
          _ ≤ ε / 2 := hAs_diam n)
  -- Step 8b: bound tail by hN (T x = x₀ on tail, so cost = c x x₀ ≤ ε/2)
  have htail : ∫⁻ x in (⋃ n ∈ Finset.range N, As n)ᶜ, ENNReal.ofReal (c x (T x)) ∂μ ≤
      ENNReal.ofReal (ε / 2) := by
    have heq : Set.EqOn (fun x => ENNReal.ofReal (c x (T x))) (fun x => ENNReal.ofReal (c x x₀))
        (⋃ n ∈ Finset.range N, As n)ᶜ := by
      intro x hx
      simp only []
      congr 1
      rw [hT_tail x hx]
    rw [setLIntegral_congr_fun hS_mble.compl heq]
    exact hN
  -- Step 9: combine: ε/2 + ε/2 = ε
  have hε_split : ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) = ENNReal.ofReal ε := by
    rw [← ENNReal.ofReal_add (le_of_lt (half_pos _hε)) (le_of_lt (half_pos _hε))]
    congr 1; ring
  calc ∫⁻ x in ⋃ n ∈ Finset.range N, As n, ENNReal.ofReal (c x (T x)) ∂μ +
        ∫⁻ x in (⋃ n ∈ Finset.range N, As n)ᶜ, ENNReal.ofReal (c x (T x)) ∂μ
      ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := by gcongr
    _ = ENNReal.ofReal ε := hε_split

/-! ### Finite transportation LP: compactness leaves

Two standalone compactness facts underpinning the finite Kantorovich-duality kernel
`finiteRange_transportation_dual`:

* `exists_transport_min` — the transport polytope `{P ≥ 0 : rowsums = a, colsums = b}` is
  compact and nonempty, so the primal cost `⟨Cost, P⟩` attains its minimum (extreme value
  theorem on a closed bounded polytope in the finite-dimensional space `m → n → ℝ`).
* `isClosed_transport_cone` — the image cone `Φ(orthant) = {(rowsums P, colsums P, ⟨Cost,P⟩ + s)
  : P ≥ 0, s ≥ 0}` (marginals + relaxed cost coordinate, the slack `s` making the cost
  coordinate an *inequality*) is closed (Bolzano–Weierstrass), which is the `ProperCone`
  obligation for the geometric Farkas separation `ProperCone.hyperplane_separation_point`.

Both use the geometric `ι → ℝ` route (plain products, no `EuclideanSpace` inner-product
instances). -/

section TransportLP

open Filter Topology Bornology

variable {m n : Type*} [Fintype m] [Fintype n]

/-- **Primal attainment for the finite transportation LP.**  The feasible polytope
`{P ≥ 0 : rowsums = a, colsums = b}` is compact (closed + bounded in finite dimension) and
nonempty (it contains the product `a ⊗ b`), so the linear cost
`⟨Cost, P⟩ = ∑ᵢⱼ Costᵢⱼ Pᵢⱼ` attains its minimum on it. -/
theorem exists_transport_min
    (a : m → ℝ) (b : n → ℝ) (Cost : m → n → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j)
    (hasum : ∑ i, a i = 1) (hbsum : ∑ j, b j = 1) :
    ∃ P : m → n → ℝ,
      (∀ i j, 0 ≤ P i j) ∧ (∀ i, ∑ j, P i j = a i) ∧ (∀ j, ∑ i, P i j = b j) ∧
      ∀ Q : m → n → ℝ,
        (∀ i j, 0 ≤ Q i j) → (∀ i, ∑ j, Q i j = a i) → (∀ j, ∑ i, Q i j = b j) →
        (∑ i, ∑ j, Cost i j * P i j) ≤ ∑ i, ∑ j, Cost i j * Q i j := by
  classical
  set F : Set (m → n → ℝ) :=
    {P | (∀ i j, 0 ≤ P i j) ∧ (∀ i, ∑ j, P i j = a i) ∧ (∀ j, ∑ i, P i j = b j)} with hF_def
  -- nonempty: product coupling `a ⊗ b`
  have hFne : F.Nonempty := by
    refine ⟨fun i j => a i * b j, fun i j => mul_nonneg (ha i) (hb j), ?_, ?_⟩
    · intro i; rw [← Finset.mul_sum, hbsum, mul_one]
    · intro j; rw [← Finset.sum_mul, hasum, one_mul]
  -- closed: finite intersection of closed conditions
  have hFcl : IsClosed F := by
    have e1 : IsClosed {P : m → n → ℝ | ∀ i j, 0 ≤ P i j} := by
      rw [Set.setOf_forall]; refine isClosed_iInter fun i => ?_
      rw [Set.setOf_forall]; refine isClosed_iInter fun j => ?_
      exact isClosed_le continuous_const (by fun_prop)
    have e2 : IsClosed {P : m → n → ℝ | ∀ i, ∑ j, P i j = a i} := by
      rw [Set.setOf_forall]; refine isClosed_iInter fun i => ?_
      exact isClosed_eq (by fun_prop) continuous_const
    have e3 : IsClosed {P : m → n → ℝ | ∀ j, ∑ i, P i j = b j} := by
      rw [Set.setOf_forall]; refine isClosed_iInter fun j => ?_
      exact isClosed_eq (by fun_prop) continuous_const
    have hEq : F = {P : m → n → ℝ | ∀ i j, 0 ≤ P i j} ∩
        {P : m → n → ℝ | ∀ i, ∑ j, P i j = a i} ∩
        {P : m → n → ℝ | ∀ j, ∑ i, P i j = b j} := by
      ext P; constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩
    rw [hEq]; exact (e1.inter e2).inter e3
  -- bounded: every feasible `P` has sup-norm ≤ 1
  have hFbd : Bornology.IsBounded F := by
    apply (Metric.isBounded_closedBall (x := (0 : m → n → ℝ)) (r := 1)).subset
    intro P hP
    simp only [Metric.mem_closedBall, dist_zero_right]
    rw [pi_norm_le_iff_of_nonneg zero_le_one]; intro i
    rw [pi_norm_le_iff_of_nonneg zero_le_one]; intro j
    obtain ⟨hnn, hrow, _⟩ := hP
    rw [Real.norm_eq_abs, abs_le]
    refine ⟨by linarith [hnn i j], ?_⟩
    calc P i j ≤ ∑ j', P i j' := Finset.single_le_sum (fun j' _ => hnn i j') (Finset.mem_univ j)
      _ = a i := hrow i
      _ ≤ ∑ i', a i' := Finset.single_le_sum (fun i' _ => ha i') (Finset.mem_univ i)
      _ = 1 := hasum
  -- compact, then extreme value theorem on the linear cost
  have hFcompact : IsCompact F := Metric.isCompact_of_isClosed_isBounded hFcl hFbd
  have hcont : Continuous (fun P : m → n → ℝ => ∑ i, ∑ j, Cost i j * P i j) := by fun_prop
  obtain ⟨P, hPF, hPmin⟩ := hFcompact.exists_isMinOn hFne hcont.continuousOn
  obtain ⟨hP1, hP2, hP3⟩ := hPF
  exact ⟨P, hP1, hP2, hP3, fun Q hQ1 hQ2 hQ3 => isMinOn_iff.mp hPmin Q ⟨hQ1, hQ2, hQ3⟩⟩

/-- **Closedness of the transport image cone** (the `ProperCone` obligation for geometric
Farkas).  The image of the orthant `{(P, s) : P ≥ 0, s ≥ 0}` under the affine-marginal +
relaxed-cost map `Φ(P, s) = (rowsums P, colsums P, ⟨Cost, P⟩ + s)` is closed.  Proof by
Bolzano–Weierstrass: a convergent sequence in the image has convergent marginals, hence the
matrices `Pₖ` are bounded (mass conservation), so a subsequence converges to a feasible limit
`P*` matching the limit marginals; the slack `s* = (limit cost coord) − ⟨Cost, P*⟩ ≥ 0`. -/
theorem isClosed_transport_cone (Cost : m → n → ℝ) :
    IsClosed {w : (m → ℝ) × (n → ℝ) × ℝ |
      ∃ (P : m → n → ℝ) (s : ℝ), (∀ i j, 0 ≤ P i j) ∧ 0 ≤ s ∧
        w = (fun i => ∑ j, P i j, fun j => ∑ i, P i j,
              (∑ i, ∑ j, Cost i j * P i j) + s)} := by
  classical
  apply IsSeqClosed.isClosed
  intro w p hw_mem hw_tend
  obtain ⟨p1, p2, p3⟩ := p
  simp only [Set.mem_setOf_eq] at hw_mem
  choose P s hPnn hsnn hweq using hw_mem
  -- componentwise convergence of `w`
  have hfst : Tendsto (fun k => (w k).1) atTop (𝓝 p1) := (continuous_fst.tendsto _).comp hw_tend
  have hsnd1 : Tendsto (fun k => (w k).2.1) atTop (𝓝 p2) :=
    ((continuous_fst.comp continuous_snd).tendsto _).comp hw_tend
  have hsnd2 : Tendsto (fun k => (w k).2.2) atTop (𝓝 p3) :=
    ((continuous_snd.comp continuous_snd).tendsto _).comp hw_tend
  -- rewrite via the witness equations
  have hrow : Tendsto (fun k => (fun i => ∑ j, P k i j : m → ℝ)) atTop (𝓝 p1) := by
    have heq : (fun k => (fun i => ∑ j, P k i j : m → ℝ)) = (fun k => (w k).1) := by
      funext k; rw [hweq k]
    rw [heq]; exact hfst
  have hcol : Tendsto (fun k => (fun j => ∑ i, P k i j : n → ℝ)) atTop (𝓝 p2) := by
    have heq : (fun k => (fun j => ∑ i, P k i j : n → ℝ)) = (fun k => (w k).2.1) := by
      funext k; rw [hweq k]
    rw [heq]; exact hsnd1
  have hcost2 : Tendsto (fun k => (∑ i, ∑ j, Cost i j * P k i j) + s k) atTop (𝓝 p3) := by
    have heq : (fun k => (∑ i, ∑ j, Cost i j * P k i j) + s k) = (fun k => (w k).2.2) := by
      funext k; rw [hweq k]
    rw [heq]; exact hsnd2
  -- the matrices `Pₖ` are uniformly bounded (each entry ≤ its row sum ≤ ‖row sums‖)
  have hRowBd : IsBounded (Set.range (fun k => (fun i => ∑ j, P k i j : m → ℝ))) :=
    hrow.cauchySeq.isBounded_range
  have hPbound : ∀ k, ‖P k‖ ≤ ‖(fun i => ∑ j, P k i j : m → ℝ)‖ := by
    intro k
    rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]; intro i
    rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]; intro j
    rw [Real.norm_eq_abs, abs_of_nonneg (hPnn k i j)]
    calc P k i j ≤ ∑ j', P k i j' :=
          Finset.single_le_sum (fun j' _ => hPnn k i j') (Finset.mem_univ j)
      _ ≤ ‖(fun i => ∑ j, P k i j : m → ℝ)‖ := by
          refine le_trans (le_abs_self _) ?_
          rw [← Real.norm_eq_abs]
          exact norm_le_pi_norm (fun i => ∑ j, P k i j : m → ℝ) i
  obtain ⟨R, hR⟩ := hRowBd.subset_closedBall (0 : m → ℝ)
  have hPbd : IsBounded (Set.range P) := by
    apply (Metric.isBounded_closedBall (x := (0 : m → n → ℝ)) (r := R)).subset
    rintro _ ⟨k, rfl⟩
    simp only [Metric.mem_closedBall, dist_zero_right]
    refine le_trans (hPbound k) ?_
    have hmem := hR (Set.mem_range_self k)
    simpa only [Metric.mem_closedBall, dist_zero_right] using hmem
  -- Bolzano–Weierstrass: extract a convergent subsequence `P (φ ·) → Pstar`
  obtain ⟨Pstar, -, φ, hφ_mono, hφ_tend⟩ :=
    tendsto_subseq_of_bounded hPbd (fun k => Set.mem_range_self k)
  -- `Pstar` is a feasible matrix matching the limit marginals
  have hPstar_nn : ∀ i j, 0 ≤ Pstar i j := by
    intro i j
    have hev : Continuous (fun Q : m → n → ℝ => Q i j) := by fun_prop
    exact ge_of_tendsto' ((hev.tendsto Pstar).comp hφ_tend) (fun k => hPnn (φ k) i j)
  have hrowstar : (fun i => ∑ j, Pstar i j : m → ℝ) = p1 := by
    have hcont : Tendsto (fun k => (fun i => ∑ j, P (φ k) i j : m → ℝ)) atTop
        (𝓝 (fun i => ∑ j, Pstar i j : m → ℝ)) := by
      have hC : Continuous (fun Q : m → n → ℝ => (fun i => ∑ j, Q i j : m → ℝ)) := by fun_prop
      exact (hC.tendsto Pstar).comp hφ_tend
    exact tendsto_nhds_unique hcont (hrow.comp hφ_mono.tendsto_atTop)
  have hcolstar : (fun j => ∑ i, Pstar i j : n → ℝ) = p2 := by
    have hcont : Tendsto (fun k => (fun j => ∑ i, P (φ k) i j : n → ℝ)) atTop
        (𝓝 (fun j => ∑ i, Pstar i j : n → ℝ)) := by
      have hC : Continuous (fun Q : m → n → ℝ => (fun j => ∑ i, Q i j : n → ℝ)) := by fun_prop
      exact (hC.tendsto Pstar).comp hφ_tend
    exact tendsto_nhds_unique hcont (hcol.comp hφ_mono.tendsto_atTop)
  -- the slack at the limit is nonnegative
  have hs_tend : Tendsto (fun k => s (φ k)) atTop
      (𝓝 (p3 - ∑ i, ∑ j, Cost i j * Pstar i j)) := by
    have hcs : Tendsto (fun k => (∑ i, ∑ j, Cost i j * P (φ k) i j) + s (φ k)) atTop (𝓝 p3) :=
      hcost2.comp hφ_mono.tendsto_atTop
    have hc : Tendsto (fun k => ∑ i, ∑ j, Cost i j * P (φ k) i j) atTop
        (𝓝 (∑ i, ∑ j, Cost i j * Pstar i j)) := by
      have hC : Continuous (fun Q : m → n → ℝ => ∑ i, ∑ j, Cost i j * Q i j) := by fun_prop
      exact (hC.tendsto Pstar).comp hφ_tend
    simpa only [add_sub_cancel_left] using hcs.sub hc
  have hsstar_nn : 0 ≤ p3 - ∑ i, ∑ j, Cost i j * Pstar i j :=
    ge_of_tendsto' hs_tend (fun k => hsnn (φ k))
  -- assemble: `(p1, p2, p3) ∈ K` with witnesses `Pstar`, `p3 − ⟨Cost, Pstar⟩`
  refine ⟨Pstar, p3 - ∑ i, ∑ j, Cost i j * Pstar i j, hPstar_nn, hsstar_nn, ?_⟩
  have h3 : (∑ i, ∑ j, Cost i j * Pstar i j) + (p3 - ∑ i, ∑ j, Cost i j * Pstar i j) = p3 := by
    ring
  rw [hrowstar, hcolstar, h3]

/-- The transport image cone `Φ(orthant) = {(rowsums P, colsums P, ⟨Cost,P⟩ + s) : P ≥ 0,
s ≥ 0}` packaged as a `ProperCone` over `ℝ`: a `PointedCone` (`0`, `+`, `ℝ≥0`-smul closure
— `Φ` is linear and the orthant a cone) that is closed (`isClosed_transport_cone`).  This is
the `ProperCone` obligation for the geometric Farkas separation
`ProperCone.hyperplane_separation_point`. -/
def transportProperCone (Cost : m → n → ℝ) :
    ProperCone ℝ ((m → ℝ) × (n → ℝ) × ℝ) where
  toSubmodule :=
    { carrier := {w : (m → ℝ) × (n → ℝ) × ℝ |
        ∃ (P : m → n → ℝ) (s : ℝ), (∀ i j, 0 ≤ P i j) ∧ 0 ≤ s ∧
          w = (fun i => ∑ j, P i j, fun j => ∑ i, P i j,
                (∑ i, ∑ j, Cost i j * P i j) + s)}
      zero_mem' := ⟨0, 0, fun _ _ => le_refl 0, le_refl 0, by
        refine Prod.ext ?_ (Prod.ext ?_ ?_)
        · funext i; simp
        · funext j; simp
        · simp⟩
      add_mem' := by
        rintro x y ⟨P1, s1, hP1, hs1, rfl⟩ ⟨P2, s2, hP2, hs2, rfl⟩
        refine ⟨P1 + P2, s1 + s2, fun i j => add_nonneg (hP1 i j) (hP2 i j),
          add_nonneg hs1 hs2, ?_⟩
        refine Prod.ext (funext fun i => ?_) (Prod.ext (funext fun j => ?_) ?_)
        · change (∑ j, P1 i j) + (∑ j, P2 i j) = ∑ j, (P1 i j + P2 i j)
          rw [Finset.sum_add_distrib]
        · change (∑ i, P1 i j) + (∑ i, P2 i j) = ∑ i, (P1 i j + P2 i j)
          rw [Finset.sum_add_distrib]
        · change ((∑ i, ∑ j, Cost i j * P1 i j) + s1) + ((∑ i, ∑ j, Cost i j * P2 i j) + s2)
              = (∑ i, ∑ j, Cost i j * (P1 i j + P2 i j)) + (s1 + s2)
          simp_rw [mul_add, Finset.sum_add_distrib]; ring
      smul_mem' := by
        rintro c x ⟨P, s, hP, hs, rfl⟩
        refine ⟨(c : ℝ) • P, (c : ℝ) • s, fun i j => mul_nonneg c.2 (hP i j),
          mul_nonneg c.2 hs, ?_⟩
        refine Prod.ext (funext fun i => ?_) (Prod.ext (funext fun j => ?_) ?_)
        · change (c : ℝ) * (∑ j, P i j) = ∑ j, (c : ℝ) * P i j
          rw [Finset.mul_sum]
        · change (c : ℝ) * (∑ i, P i j) = ∑ i, (c : ℝ) * P i j
          rw [Finset.mul_sum]
        · change (c : ℝ) * ((∑ i, ∑ j, Cost i j * P i j) + s)
              = (∑ i, ∑ j, Cost i j * ((c : ℝ) * P i j)) + (c : ℝ) * s
          simp_rw [mul_add, Finset.mul_sum]; ring }
  isClosed' := isClosed_transport_cone Cost

/-- **Per-ε Farkas separation.**  Given the optimal plan `P` (primal value `V = ⟨Cost,P⟩`),
for every `ε > 0` there is a dual-feasible pair `(u, v)` whose value exceeds `V − ε`.  Proof:
`(a, b, V − ε) ∉ transportProperCone` (no feasible plan beats `V`), so
`ProperCone.hyperplane_separation_point` yields a separating functional `f`; reading off
`λ = f(0,0,1)`, `Uᵢ = f(eᵢ,0,0)`, `Wⱼ = f(0,eⱼ,0)` gives `Uᵢ + Wⱼ + λ·Costᵢⱼ ≥ 0` and
`∑aᵢUᵢ + ∑bⱼWⱼ + λ(V−ε) < 0`; `λ > 0` is forced (else the optimal `P` contradicts the
strict inequality), and `u = −U/λ`, `v = −W/λ` are feasible with value `> V − ε`. -/
theorem finiteTransport_dual_eps
    (a : m → ℝ) (b : n → ℝ) (Cost : m → n → ℝ)
    (P : m → n → ℝ) (hPnn : ∀ i j, 0 ≤ P i j)
    (hProw : ∀ i, ∑ j, P i j = a i) (hPcol : ∀ j, ∑ i, P i j = b j)
    (hPmin : ∀ Q : m → n → ℝ, (∀ i j, 0 ≤ Q i j) → (∀ i, ∑ j, Q i j = a i) →
      (∀ j, ∑ i, Q i j = b j) → (∑ i, ∑ j, Cost i j * P i j) ≤ ∑ i, ∑ j, Cost i j * Q i j)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (u : m → ℝ) (v : n → ℝ), (∀ i j, u i + v j ≤ Cost i j) ∧
      (∑ i, ∑ j, Cost i j * P i j) - ε < (∑ i, a i * u i) + ∑ j, b j * v j := by
  classical
  set V : ℝ := ∑ i, ∑ j, Cost i j * P i j with hV_def
  -- the point `(a, b, V − ε)` is not in the cone: no feasible plan beats `V`
  have hnotmem : ((a, b, V - ε) : (m → ℝ) × (n → ℝ) × ℝ) ∉ transportProperCone Cost := by
    rintro ⟨Q, s, hQnn, hs, hQeq⟩
    rw [Prod.mk.injEq, Prod.mk.injEq] at hQeq
    obtain ⟨haQ, hbQ, hcQ⟩ := hQeq
    have hQrow : ∀ i, ∑ j, Q i j = a i := fun i => (congrFun haQ i).symm
    have hQcol : ∀ j, ∑ i, Q i j = b j := fun j => (congrFun hbQ j).symm
    have hmin := hPmin Q hQnn hQrow hQcol
    -- `V - ε = ⟨Cost,Q⟩ + s` so `⟨Cost,Q⟩ = V - ε - s ≤ V - ε < V`
    linarith [hmin, hcQ, hs, hε]
  -- separating functional
  obtain ⟨f, hf_nn, hf_neg⟩ := (transportProperCone Cost).hyperplane_separation_point hnotmem
  -- coordinate functionals via inclusions
  set fm : (m → ℝ) →L[ℝ] ℝ :=
    f.comp (ContinuousLinearMap.inl ℝ (m → ℝ) ((n → ℝ) × ℝ)) with hfm_def
  set fn : (n → ℝ) →L[ℝ] ℝ :=
    f.comp ((ContinuousLinearMap.inr ℝ (m → ℝ) ((n → ℝ) × ℝ)).comp
      (ContinuousLinearMap.inl ℝ (n → ℝ) ℝ)) with hfn_def
  set lam : ℝ := f (0, 0, 1) with hlam_def
  set U : m → ℝ := fun i => fm (Pi.single i 1) with hU_def
  set Wv : n → ℝ := fun j => fn (Pi.single j 1) with hW_def
  have hUi : ∀ i, U i = fm (Pi.single i 1) := fun _ => rfl
  have hWj : ∀ j, Wv j = fn (Pi.single j 1) := fun _ => rfl
  -- the splitting identity `f (x, y, z) = fm x + fn y + z·lam`
  have hsplit : ∀ (x : m → ℝ) (y : n → ℝ) (z : ℝ),
      f (x, y, z) = fm x + fn y + z * lam := by
    intro x y z
    have e : ((x, y, z) : (m → ℝ) × (n → ℝ) × ℝ)
        = (x, (0 : n → ℝ), (0 : ℝ)) + ((0 : m → ℝ), y, (0 : ℝ))
          + ((0 : m → ℝ), (0 : n → ℝ), z) := by
      refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp
    rw [e, map_add, map_add]
    have h3 : f ((0 : m → ℝ), (0 : n → ℝ), z) = z * lam := by
      rw [show ((0 : m → ℝ), (0 : n → ℝ), z)
            = z • ((0 : m → ℝ), (0 : n → ℝ), (1 : ℝ)) by simp, map_smul, smul_eq_mul]
    rw [h3]
    rfl
  -- `fm a = ∑ aᵢ Uᵢ`, `fn b = ∑ bⱼ Wⱼ`
  have hfm_sum : fm a = ∑ i, a i * U i := by
    have hbasis : a = ∑ i, a i • (Pi.single i 1 : m → ℝ) := by
      funext k; rw [Finset.sum_apply]
      simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq, Finset.mem_univ, if_true]
    conv_lhs => rw [hbasis]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul, hUi]
  have hfn_sum : fn b = ∑ j, b j * Wv j := by
    have hbasis : b = ∑ j, b j • (Pi.single j 1 : n → ℝ) := by
      funext k; rw [Finset.sum_apply]
      simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq, Finset.mem_univ, if_true]
    conv_lhs => rw [hbasis]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, smul_eq_mul, hWj]
  -- cone membership of the basis points
  have hmem_s : ((0 : m → ℝ), (0 : n → ℝ), (1 : ℝ)) ∈ transportProperCone Cost :=
    ⟨0, 1, fun _ _ => le_refl 0, zero_le_one, by
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · funext i; simp
      · funext j; simp
      · simp⟩
  have hlam_nn : 0 ≤ lam := hf_nn _ hmem_s
  -- the single-entry membership giving `0 ≤ Uᵢ + Wⱼ + Costᵢⱼ·lam`
  have hij : ∀ i j, 0 ≤ U i + Wv j + Cost i j * lam := by
    intro i j
    have hmem_ij : ((Pi.single i 1 : m → ℝ), (Pi.single j 1 : n → ℝ), Cost i j)
        ∈ transportProperCone Cost := by
      refine ⟨fun i' j' => if i' = i then (if j' = j then (1 : ℝ) else 0) else 0, 0,
        fun i' j' => ?_, le_refl 0, ?_⟩
      · dsimp only; split_ifs <;> norm_num
      · refine Prod.ext (funext fun i' => ?_) (Prod.ext (funext fun j' => ?_) ?_)
        · dsimp only
          rw [Pi.single_apply]
          by_cases hi : i' = i
          · subst hi; simp [Finset.sum_ite_eq']
          · simp [hi]
        · dsimp only
          rw [Pi.single_apply,
            Finset.sum_ite_eq' Finset.univ i (fun _ => if j' = j then (1 : ℝ) else 0)]
          simp
        · dsimp only
          simp only [add_zero, mul_ite, mul_one, mul_zero]
          rw [Finset.sum_eq_single i (fun i' _ hi' => by simp [hi']) (by simp)]
          rw [Finset.sum_eq_single j (fun j' _ hj' => by simp [hj']) (by simp)]
          simp
    have hnn := hf_nn _ hmem_ij
    linarith [hnn, hsplit (Pi.single i 1 : m → ℝ) (Pi.single j 1 : n → ℝ) (Cost i j),
      hUi i, hWj j]
  -- `lam > 0`
  have hlam_pos : 0 < lam := by
    rcases lt_or_eq_of_le hlam_nn with h | h
    · exact h
    · exfalso
      -- with `lam = 0`: `Uᵢ + Wⱼ ≥ 0`, so `∑ Pᵢⱼ(Uᵢ+Wⱼ) ≥ 0 = fm a + fn b`, contradicting `< 0`
      have hUW : ∀ i j, 0 ≤ U i + Wv j := by
        intro i j; have := hij i j; rw [← h] at this; simpa using this
      have hsum_nn : 0 ≤ ∑ i, ∑ j, P i j * (U i + Wv j) :=
        Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
          mul_nonneg (hPnn i j) (hUW i j)
      have hsum_eq : (∑ i, ∑ j, P i j * (U i + Wv j)) = fm a + fn b := by
        rw [hfm_sum, hfn_sum]
        simp_rw [mul_add, Finset.sum_add_distrib]
        congr 1
        · refine Finset.sum_congr rfl fun i _ => ?_
          rw [← Finset.sum_mul, hProw i]
        · rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← Finset.sum_mul, hPcol j]
      have hneg : f (a, b, V - ε) < 0 := hf_neg
      rw [hsplit, ← h] at hneg
      simp only [mul_zero, add_zero] at hneg
      rw [hsum_eq] at hsum_nn
      linarith
  -- build `u, v` and verify
  refine ⟨fun i => -U i / lam, fun j => -Wv j / lam, fun i j => ?_, ?_⟩
  · -- feasibility: `-Uᵢ/lam + (-Wⱼ/lam) ≤ Costᵢⱼ`
    rw [← add_div, div_le_iff₀ hlam_pos]
    nlinarith [hij i j]
  · -- value `> V - ε`
    have key1 : (∑ i, a i * (-U i / lam)) = (∑ i, a i * U i) * (-lam⁻¹) := by
      rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun i _ => ?_
      rw [div_eq_mul_inv]; ring
    have key2 : (∑ j, b j * (-Wv j / lam)) = (∑ j, b j * Wv j) * (-lam⁻¹) := by
      rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun j _ => ?_
      rw [div_eq_mul_inv]; ring
    have hval : (∑ i, a i * (-U i / lam)) + ∑ j, b j * (-Wv j / lam)
        = (-(fm a) - fn b) / lam := by
      rw [key1, key2, hfm_sum, hfn_sum, div_eq_mul_inv]; ring
    rw [hval]
    have hneg : f (a, b, V - ε) < 0 := hf_neg
    rw [hsplit] at hneg
    rw [lt_div_iff₀ hlam_pos]
    nlinarith [hneg]

/-- **ε-approximate finite LP duality with optimal plan.**  Packages the primal optimum
`P` (`exists_transport_min`) with an ε-optimal dual pair (`finiteTransport_dual_eps`): for
every `ε > 0`, an optimal feasible plan `P` and a dual-feasible `(u, v)` with the primal
cost `⟨Cost, P⟩` within `ε` of the dual value.  The downstream KR bridge then sends the ε to
the Kantorovich sup (no attainment needed — ε-optimal throughout). -/
theorem finiteTransport_dual_eps_plan
    (a : m → ℝ) (b : n → ℝ) (Cost : m → n → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j)
    (hasum : ∑ i, a i = 1) (hbsum : ∑ j, b j = 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (P : m → n → ℝ) (u : m → ℝ) (v : n → ℝ),
      (∀ i j, 0 ≤ P i j) ∧ (∀ i, ∑ j, P i j = a i) ∧ (∀ j, ∑ i, P i j = b j) ∧
      (∀ i j, u i + v j ≤ Cost i j) ∧
      (∑ i, ∑ j, Cost i j * P i j) - ε < (∑ i, a i * u i) + ∑ j, b j * v j := by
  obtain ⟨P, hPnn, hProw, hPcol, hPmin⟩ := exists_transport_min a b Cost ha hb hasum hbsum
  obtain ⟨u, v, hfeas, hval⟩ :=
    finiteTransport_dual_eps a b Cost P hPnn hProw hPcol hPmin ε hε
  exact ⟨P, u, v, hPnn, hProw, hPcol, hfeas, hval⟩

end TransportLP

/-- **Transportation dual potentials (ε-form).**
For finite-range pushforwards `Measure.map T μ`, `Measure.map S ν` and every `ε > 0`, finite
transportation LP duality yields a measurable dual pair `u, v` with `u a + v b ≤ c a b` on the
supports `range T`, `range S`, whose value `∫u dμ' + ∫v dν'` bounds the coupling infimum from
above *up to `ε`*.  Proof: the finite LP gives (`finiteTransport_dual_eps_plan`) an optimal
plan `P` and a dual pair within `ε`; the matrix→measure bridge sends `P` to a coupling
realising `coupling-inf ≤ ofReal⟨Cost,P⟩` and identifies `∫u dμ' = ∑ aᵢ uᵢ` (integral against
a finitely-supported pushforward), and the dual potentials lift to measurable `α → ℝ`.  The `ε`
is consumed at the Kantorovich sup downstream — no attainment needed.  **Metric-free**: no
symmetry/triangle (those enter only in the c-transform `cTransform_dual_witness`). -/
theorem finiteRange_transportation_dual
    {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α]
    (c : α → α → ℝ) (hc_nonneg : ∀ x y, 0 ≤ c x y)
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (T S : α → α) (hT : Measurable T) (hS : Measurable S)
    (hTfin : (Set.range T).Finite) (hSfin : (Set.range S).Finite)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ u v : α → ℝ, Measurable u ∧ Measurable v ∧
      (∀ a ∈ Set.range T, ∀ b ∈ Set.range S, u a + v b ≤ c a b) ∧
      wassersteinCostCoupling c (Measure.map T μ) (Measure.map S ν)
        ≤ ENNReal.ofReal ((∫ x, u x ∂(Measure.map T μ)) + ∫ x, v x ∂(Measure.map S ν))
          + ENNReal.ofReal ε := by
  classical
  haveI hαne : Nonempty α := nonempty_of_isProbabilityMeasure μ
  -- finite index types = supports of the pushforwards
  obtain ⟨t₀, ht₀⟩ := Set.range_nonempty T
  obtain ⟨s₀, hs₀⟩ := Set.range_nonempty S
  haveI : Nonempty (hTfin.toFinset) :=
    ⟨⟨t₀, by rw [Set.Finite.mem_toFinset]; exact ht₀⟩⟩
  haveI : Nonempty (hSfin.toFinset) :=
    ⟨⟨s₀, by rw [Set.Finite.mem_toFinset]; exact hs₀⟩⟩
  -- weights and cost matrix over the finite supports
  set a : hTfin.toFinset → ℝ := fun i => ((Measure.map T μ) {(i : α)}).toReal with ha_def
  set b : hSfin.toFinset → ℝ := fun j => ((Measure.map S ν) {(j : α)}).toReal with hb_def
  set Cost : hTfin.toFinset → hSfin.toFinset → ℝ := fun i j => c (i : α) (j : α) with hCost_def
  have ha_nn : ∀ i, 0 ≤ a i := fun _ => ENNReal.toReal_nonneg
  have hb_nn : ∀ j, 0 ≤ b j := fun _ => ENNReal.toReal_nonneg
  haveI hμP : IsProbabilityMeasure (Measure.map T μ) :=
    Measure.isProbabilityMeasure_map hT.aemeasurable
  haveI hνP : IsProbabilityMeasure (Measure.map S ν) :=
    Measure.isProbabilityMeasure_map hS.aemeasurable
  -- atom decompositions of the finite-range pushforwards
  have hμmap : Measure.map T μ
      = ∑ x ∈ hTfin.toFinset, (Measure.map T μ {x}) • Measure.dirac x := by
    refine (Measure.ae_mem_finset_iff (μ := Measure.map T μ) (s := hTfin.toFinset)).mp ?_
    rw [ae_iff, show {a | ¬ (a ∈ hTfin.toFinset)} = (↑hTfin.toFinset : Set α)ᶜ from by ext a; simp,
      Measure.map_apply hT (hTfin.toFinset.measurableSet.compl), Set.preimage_compl]
    have huniv : T ⁻¹' (↑hTfin.toFinset : Set α) = Set.univ := by
      ext y; simp only [Set.mem_preimage, Set.mem_univ, iff_true, Finset.mem_coe,
        Set.Finite.mem_toFinset]; exact Set.mem_range_self y
    rw [huniv, Set.compl_univ, measure_empty]
  have hνmap : Measure.map S ν
      = ∑ y ∈ hSfin.toFinset, (Measure.map S ν {y}) • Measure.dirac y := by
    refine (Measure.ae_mem_finset_iff (μ := Measure.map S ν) (s := hSfin.toFinset)).mp ?_
    rw [ae_iff, show {a | ¬ (a ∈ hSfin.toFinset)} = (↑hSfin.toFinset : Set α)ᶜ from by ext a; simp,
      Measure.map_apply hS (hSfin.toFinset.measurableSet.compl), Set.preimage_compl]
    have huniv : S ⁻¹' (↑hSfin.toFinset : Set α) = Set.univ := by
      ext y; simp only [Set.mem_preimage, Set.mem_univ, iff_true, Finset.mem_coe,
        Set.Finite.mem_toFinset]; exact Set.mem_range_self y
    rw [huniv, Set.compl_univ, measure_empty]
  -- the singleton masses sum to 1
  have hμmass : (∑ x ∈ hTfin.toFinset, (Measure.map T μ {x})) = 1 := by
    have h1 : (∑ x ∈ hTfin.toFinset, (Measure.map T μ {x}) • Measure.dirac x) Set.univ = 1 := by
      rw [← hμmap]; exact measure_univ
    simpa only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul,
      measure_univ, mul_one] using h1
  have hνmass : (∑ y ∈ hSfin.toFinset, (Measure.map S ν {y})) = 1 := by
    have h1 : (∑ y ∈ hSfin.toFinset, (Measure.map S ν {y}) • Measure.dirac y) Set.univ = 1 := by
      rw [← hνmap]; exact measure_univ
    simpa only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul,
      measure_univ, mul_one] using h1
  have ha_sum : ∑ i, a i = 1 := by
    have hcoe : (∑ i, a i) = ∑ x ∈ hTfin.toFinset, ((Measure.map T μ) {x}).toReal :=
      Finset.sum_coe_sort hTfin.toFinset (fun x => ((Measure.map T μ) {x}).toReal)
    rw [hcoe, ← ENNReal.toReal_sum (fun x _ => measure_ne_top _ _), hμmass, ENNReal.toReal_one]
  have hb_sum : ∑ j, b j = 1 := by
    have hcoe : (∑ j, b j) = ∑ y ∈ hSfin.toFinset, ((Measure.map S ν) {y}).toReal :=
      Finset.sum_coe_sort hSfin.toFinset (fun y => ((Measure.map S ν) {y}).toReal)
    rw [hcoe, ← ENNReal.toReal_sum (fun y _ => measure_ne_top _ _), hνmass, ENNReal.toReal_one]
  -- finite LP: optimal plan P and an ε-optimal dual pair (u, v)
  obtain ⟨P, u, v, hPnn, hProw, hPcol, hfeas, hval⟩ :=
    finiteTransport_dual_eps_plan a b Cost ha_nn hb_nn ha_sum hb_sum ε hε
  -- lift the finite dual potentials to functions on α
  set ulift : α → ℝ := fun x => if h : x ∈ hTfin.toFinset then u ⟨x, h⟩ else 0 with hulift_def
  set vlift : α → ℝ := fun y => if h : y ∈ hSfin.toFinset then v ⟨y, h⟩ else 0 with hvlift_def
  -- ulift as a finite sum of indicator functions on the atoms (gives measurability + integral)
  have hulift_eq : ulift = fun x => ∑ i ∈ hTfin.toFinset.attach,
      Set.indicator {(i : α)} (fun _ => u i) x := by
    funext x
    simp only [hulift_def, Set.indicator_apply, Set.mem_singleton_iff]
    by_cases hx : x ∈ hTfin.toFinset
    · rw [dif_pos hx, Finset.sum_eq_single (⟨x, hx⟩ : hTfin.toFinset)]
      · simp
      · intro i _ hi; rw [if_neg (fun h => hi (Subtype.ext h.symm))]
      · intro h; exact absurd (Finset.mem_attach _ _) h
    · rw [dif_neg hx]
      refine (Finset.sum_eq_zero fun i _ => ?_).symm
      rw [if_neg (fun (h : x = (↑i : α)) => hx (h.symm ▸ i.2))]
  have hvlift_eq : vlift = fun y => ∑ j ∈ hSfin.toFinset.attach,
      Set.indicator {(j : α)} (fun _ => v j) y := by
    funext y
    simp only [hvlift_def, Set.indicator_apply, Set.mem_singleton_iff]
    by_cases hy : y ∈ hSfin.toFinset
    · rw [dif_pos hy, Finset.sum_eq_single (⟨y, hy⟩ : hSfin.toFinset)]
      · simp
      · intro j _ hj; rw [if_neg (fun h => hj (Subtype.ext h.symm))]
      · intro h; exact absurd (Finset.mem_attach _ _) h
    · rw [dif_neg hy]
      refine (Finset.sum_eq_zero fun j _ => ?_).symm
      rw [if_neg (fun (h : y = (↑j : α)) => hy (h.symm ▸ j.2))]
  have hulift_meas : Measurable ulift := by
    rw [hulift_eq]
    exact Finset.measurable_sum _ fun i _ =>
      (measurable_const).indicator (measurableSet_singleton _)
  have hvlift_meas : Measurable vlift := by
    rw [hvlift_eq]
    exact Finset.measurable_sum _ fun j _ =>
      (measurable_const).indicator (measurableSet_singleton _)
  refine ⟨ulift, vlift, hulift_meas, hvlift_meas, ?_, ?_⟩
  · -- feasibility on supports
    intro a' ha' b' hb'
    have hia : a' ∈ hTfin.toFinset := by rw [Set.Finite.mem_toFinset]; exact ha'
    have hjb : b' ∈ hSfin.toFinset := by rw [Set.Finite.mem_toFinset]; exact hb'
    have hua : ulift a' = u ⟨a', hia⟩ := dif_pos hia
    have hvb : vlift b' = v ⟨b', hjb⟩ := dif_pos hjb
    rw [hua, hvb]
    exact hfeas ⟨a', hia⟩ ⟨b', hjb⟩
  · -- the matrix→measure bridge bound
    -- integral identities: ∫ ulift dμ' = ∑ aᵢ uᵢ
    have hint_u : ∫ x, ulift x ∂(Measure.map T μ) = ∑ i, a i * u i := by
      rw [hulift_eq, integral_finsetSum _
        (fun i _ => (integrable_const (u i)).indicator (measurableSet_singleton _))]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_indicator_const _ (measurableSet_singleton _), smul_eq_mul]
      simp only [ha_def, measureReal_def]
    have hint_v : ∫ y, vlift y ∂(Measure.map S ν) = ∑ j, b j * v j := by
      rw [hvlift_eq, integral_finsetSum _
        (fun j _ => (integrable_const (v j)).indicator (measurableSet_singleton _))]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_indicator_const _ (measurableSet_singleton _), smul_eq_mul]
      simp only [hb_def, measureReal_def]
    -- optimal coupling realises coupling-inf ≤ ofReal ⟨Cost, P⟩
    have hcoup : wassersteinCostCoupling c (Measure.map T μ) (Measure.map S ν)
        ≤ ENNReal.ofReal (∑ i, ∑ j, Cost i j * P i j) := by
      set π : Measure (α × α) := ∑ i, ∑ j,
        ENNReal.ofReal (P i j) • Measure.dirac ((↑i : α), (↑j : α)) with hπ_def
      have hofw : ∀ i : hTfin.toFinset, ENNReal.ofReal (a i) = Measure.map T μ {↑i} := fun i => by
        rw [ha_def]; exact ENNReal.ofReal_toReal (measure_ne_top _ _)
      have hofb : ∀ j : hSfin.toFinset, ENNReal.ofReal (b j) = Measure.map S ν {↑j} := fun j => by
        rw [hb_def]; exact ENNReal.ofReal_toReal (measure_ne_top _ _)
      have hfst : Measure.map Prod.fst π = Measure.map T μ := by
        ext E hE
        rw [Measure.map_apply measurable_fst hE, hπ_def, hμmap]
        simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul,
          Measure.dirac_apply]
        rw [← Finset.sum_coe_sort hTfin.toFinset
          (fun x => Measure.map T μ {x} * Set.indicator E 1 x)]
        refine Finset.sum_congr rfl fun i _ => ?_
        have hind : ∀ j : hSfin.toFinset,
            Set.indicator (Prod.fst ⁻¹' E) (1 : α × α → ℝ≥0∞) (↑i, ↑j)
              = Set.indicator E 1 (↑i : α) :=
          fun j => by simp only [Set.indicator_apply, Set.mem_preimage, Pi.one_apply]
        simp_rw [hind, ← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun j _ => hPnn i j),
          hProw, hofw]
      have hsnd : Measure.map Prod.snd π = Measure.map S ν := by
        ext E hE
        rw [Measure.map_apply measurable_snd hE, hπ_def, hνmap]
        simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul,
          Measure.dirac_apply]
        rw [Finset.sum_comm, ← Finset.sum_coe_sort hSfin.toFinset
          (fun y => Measure.map S ν {y} * Set.indicator E 1 y)]
        refine Finset.sum_congr rfl fun j _ => ?_
        have hind : ∀ i : hTfin.toFinset,
            Set.indicator (Prod.snd ⁻¹' E) (1 : α × α → ℝ≥0∞) (↑i, ↑j)
              = Set.indicator E 1 (↑j : α) :=
          fun i => by simp only [Set.indicator_apply, Set.mem_preimage, Pi.one_apply]
        simp_rw [hind, ← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun i _ => hPnn i j),
          hPcol, hofb]
      have hπ_cost : ∫⁻ z, ENNReal.ofReal (c z.1 z.2) ∂π
          = ENNReal.ofReal (∑ i, ∑ j, Cost i j * P i j) := by
        rw [hπ_def]
        simp only [lintegral_finsetSum_measure, lintegral_smul_measure, lintegral_dirac,
          smul_eq_mul, hCost_def]
        rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => Finset.sum_nonneg fun j _ =>
          mul_nonneg (hc_nonneg _ _) (hPnn i j))]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => mul_nonneg (hc_nonneg _ _) (hPnn i j))]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← ENNReal.ofReal_mul (hPnn i j), mul_comm (P i j) (c (↑i) (↑j))]
      unfold wassersteinCostCoupling
      exact le_trans (iInf_le_of_le π (iInf_le _ ⟨hfst, hsnd⟩)) (le_of_eq hπ_cost)
    have hCP : (∑ i, ∑ j, Cost i j * P i j)
        ≤ ((∫ x, ulift x ∂(Measure.map T μ)) + ∫ y, vlift y ∂(Measure.map S ν)) + ε := by
      rw [hint_u, hint_v]; linarith [hval]
    calc wassersteinCostCoupling c (Measure.map T μ) (Measure.map S ν)
        ≤ ENNReal.ofReal (∑ i, ∑ j, Cost i j * P i j) := hcoup
      _ ≤ ENNReal.ofReal (((∫ x, ulift x ∂(Measure.map T μ))
            + ∫ y, vlift y ∂(Measure.map S ν)) + ε) := ENNReal.ofReal_le_ofReal hCP
      _ ≤ ENNReal.ofReal ((∫ x, ulift x ∂(Measure.map T μ))
            + ∫ y, vlift y ∂(Measure.map S ν)) + ENNReal.ofReal ε := ENNReal.ofReal_add_le

/-- **c-transform: dual pair → single globally-admissible potential.**
Given transportation dual potentials `u, v` with `u a + v b ≤ c a b` on the finite
supports and `c` a (pseudo)metric cost, the c-transform
`g x = ⨆ a ∈ range T, (u a − c x a)` is globally `c`-admissible
(`|g x − g y| ≤ c x y`, by triangle + symmetry) and dominates the dual value:
`g a ≥ u a` (the `a' = a` term, `c a a = 0`) and `g b ≤ −v b`
(from `u a − c a b ≤ −v b`), so `∫u dμ' + ∫v dν' ≤ ∫g dμ' − ∫g dν'`.  **This is where
`hc_triangle`/`hc_symm` are load-bearing** — it converts the Farkas dual *pair* into the
single 1-Lipschitz potential the Kantorovich dual sup ranges over. -/
theorem cTransform_dual_witness
    {α : Type*} [MeasurableSpace α]
    (c : α → α → ℝ) (hc_self : ∀ x, c x x = 0)
    (hc_symm : ∀ x y, c x y = c y x) (hc_triangle : ∀ x y z, c x z ≤ c x y + c y z)
    (hc_meas : Measurable (fun p : α × α => c p.1 p.2))
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (T S : α → α) (hT : Measurable T) (hS : Measurable S)
    (hTfin : (Set.range T).Finite) (hSfin : (Set.range S).Finite)
    (u v : α → ℝ) (hu : Measurable u) (hv : Measurable v)
    (hdual : ∀ a ∈ Set.range T, ∀ b ∈ Set.range S, u a + v b ≤ c a b) :
    ∃ g : α → ℝ, (∀ x y, |g x - g y| ≤ c x y) ∧
      (∫ x, u x ∂(Measure.map T μ)) + (∫ x, v x ∂(Measure.map S ν))
        ≤ ∫ x, g x ∂(Measure.map T μ) - ∫ x, g x ∂(Measure.map S ν) := by
  classical
  haveI : Nonempty α := nonempty_of_isProbabilityMeasure μ
  set A : Finset α := hTfin.toFinset with hA_def
  set B : Finset α := hSfin.toFinset with hB_def
  have hmemA : ∀ a ∈ Set.range T, a ∈ A := fun a ha => by
    rw [hA_def, Set.Finite.mem_toFinset]; exact ha
  have hmemB : ∀ b ∈ Set.range S, b ∈ B := fun b hb => by
    rw [hB_def, Set.Finite.mem_toFinset]; exact hb
  have hAne : A.Nonempty := by
    obtain ⟨a, ha⟩ := Set.range_nonempty T; exact ⟨a, hmemA a ha⟩
  have hBne : B.Nonempty := by
    obtain ⟨b, hb⟩ := Set.range_nonempty S; exact ⟨b, hmemB b hb⟩
  -- the c-transform potential g x = ⨆ a ∈ A, (u a − c x a)
  set g : α → ℝ := fun x => A.sup' hAne (fun a => u a - c x a) with hg_def
  -- measurability of g (finite sup of measurable fibres)
  have hpair : ∀ a : α, Measurable (fun x : α => (x, a)) := fun a => by fun_prop
  have hF_meas : ∀ a, Measurable (fun x => u a - c x a) := fun a =>
    measurable_const.sub (hc_meas.comp (hpair a))
  have hg_meas : Measurable g := by
    have heq : g = A.sup' hAne (fun a x => u a - c x a) := by
      funext x; exact (Finset.sup'_apply hAne (fun a x => u a - c x a) x).symm
    rw [heq]; exact Finset.measurable_sup' hAne (fun a _ => hF_meas a)
  -- g a ≥ u a on range T (the a-term, c a a = 0)
  have hg_ge_u : ∀ a' ∈ Set.range T, u a' ≤ g a' := by
    intro a' ha'
    have h : u a' - c a' a' ≤ g a' := Finset.le_sup' (fun a => u a - c a' a) (hmemA a' ha')
    rwa [hc_self, sub_zero] at h
  -- g b ≤ −v b on range S (from u a − c a b ≤ −v b)
  have hg_le_negv : ∀ b ∈ Set.range S, g b ≤ -v b := by
    intro b hb
    change A.sup' hAne (fun a => u a - c b a) ≤ -v b
    apply Finset.sup'_le
    intro a haA
    have ha : a ∈ Set.range T := by rw [hA_def, Set.Finite.mem_toFinset] at haA; exact haA
    have hd := hdual a ha b hb
    have hsymm : c b a = c a b := hc_symm b a
    linarith
  -- global c-admissibility (triangle + symmetry)
  have hg_adm : ∀ x y, |g x - g y| ≤ c x y := by
    have key : ∀ x y, g x ≤ g y + c x y := by
      intro x y
      change A.sup' hAne (fun a => u a - c x a) ≤ g y + c x y
      apply Finset.sup'_le
      intro a haA
      have h1 : u a - c y a ≤ g y := Finset.le_sup' (fun a => u a - c y a) haA
      have h2 : c y a ≤ c y x + c x a := hc_triangle y x a
      have h3 : c x y = c y x := hc_symm x y
      linarith
    intro x y
    rw [abs_sub_le_iff]
    refine ⟨by linarith [key x y], ?_⟩
    have hk := key y x; have hs := hc_symm x y; linarith
  -- bounded ⇒ integrable on a finite measure
  have bdd_integ : ∀ (m : Measure α) [IsFiniteMeasure m] (f : α → ℝ) (C : ℝ),
      Measurable f → (∀ y, |f y| ≤ C) → Integrable f m := by
    intro m _ f C hf hC
    exact (integrable_const C).mono' hf.aestronglyMeasurable
      (ae_of_all m (fun y => by rw [Real.norm_eq_abs]; exact hC y))
  have hu_int : Integrable (fun y => u (T y)) μ :=
    bdd_integ μ _ (A.sup' hAne (fun a => |u a|)) (hu.comp hT)
      (fun y => Finset.le_sup' (fun a => |u a|) (hmemA (T y) (Set.mem_range_self y)))
  have hgT_int : Integrable (fun y => g (T y)) μ :=
    bdd_integ μ _ (A.sup' hAne (fun a => |g a|)) (hg_meas.comp hT)
      (fun y => Finset.le_sup' (fun a => |g a|) (hmemA (T y) (Set.mem_range_self y)))
  have hv_int : Integrable (fun y => v (S y)) ν :=
    bdd_integ ν _ (B.sup' hBne (fun b => |v b|)) (hv.comp hS)
      (fun y => Finset.le_sup' (fun b => |v b|) (hmemB (S y) (Set.mem_range_self y)))
  have hgnegS_int : Integrable (fun y => -(g (S y))) ν :=
    (bdd_integ ν _ (B.sup' hBne (fun b => |g b|)) (hg_meas.comp hS)
      (fun y => Finset.le_sup' (fun b => |g b|) (hmemB (S y) (Set.mem_range_self y)))).neg
  -- assemble: change of variables, then monotonicity on the supports
  refine ⟨g, hg_adm, ?_⟩
  rw [integral_map hT.aemeasurable hu.aestronglyMeasurable,
      integral_map hS.aemeasurable hv.aestronglyMeasurable,
      integral_map hT.aemeasurable hg_meas.aestronglyMeasurable,
      integral_map hS.aemeasurable hg_meas.aestronglyMeasurable]
  have hmono1 : (∫ y, u (T y) ∂μ) ≤ ∫ y, g (T y) ∂μ :=
    integral_mono hu_int hgT_int (fun y => hg_ge_u (T y) (Set.mem_range_self y))
  have hmono2 : (∫ y, v (S y) ∂ν) ≤ ∫ y, -(g (S y)) ∂ν :=
    integral_mono hv_int hgnegS_int
      (fun y => by have := hg_le_negv (S y) (Set.mem_range_self y); linarith)
  rw [integral_neg] at hmono2
  linarith

/-- **Finite Kantorovich–Rubinstein
duality.**  For finitely-supported (finite-range pushforward) probability measures,
the coupling-infimum is at most the dual-supremum.  Proof = finite transportation LP
duality (Farkas, `finiteRange_transportation_dual`) producing a dual pair, then the
c-transform (`cTransform_dual_witness`) converting it to a single globally-admissible
potential, which the dual sup dominates (`le_iSup₂`). -/
theorem wassersteinCostCoupling_le_dual_of_finiteRange
    {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α]
    (c : α → α → ℝ) (hc_nonneg : ∀ x y, 0 ≤ c x y) (hc_self : ∀ x, c x x = 0)
    (hc_symm : ∀ x y, c x y = c y x) (hc_triangle : ∀ x y z, c x z ≤ c x y + c y z)
    (hc_meas : Measurable (fun p : α × α => c p.1 p.2))
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (T S : α → α) (hT : Measurable T) (hS : Measurable S)
    (hTfin : (Set.range T).Finite) (hSfin : (Set.range S).Finite) :
    wassersteinCostCoupling c (Measure.map T μ) (Measure.map S ν)
      ≤ wassersteinCost c (Measure.map T μ) (Measure.map S ν) := by
  -- ε → 0 at the Kantorovich sup level: the ε-family dual bound has no attainment.
  refine ENNReal.le_of_forall_pos_le_add fun η hη _ => ?_
  obtain ⟨u, v, hu, hv, hdual, hval⟩ :=
    finiteRange_transportation_dual c hc_nonneg μ ν T S hT hS hTfin hSfin (η : ℝ)
      (by exact_mod_cast hη)
  obtain ⟨g, hg_adm, hg_val⟩ :=
    cTransform_dual_witness c hc_self hc_symm hc_triangle hc_meas μ ν T S hT hS
      hTfin hSfin u v hu hv hdual
  calc wassersteinCostCoupling c (Measure.map T μ) (Measure.map S ν)
      ≤ ENNReal.ofReal ((∫ x, u x ∂(Measure.map T μ)) + ∫ x, v x ∂(Measure.map S ν))
          + ENNReal.ofReal (η : ℝ) := hval
    _ ≤ ENNReal.ofReal (∫ x, g x ∂(Measure.map T μ) - ∫ x, g x ∂(Measure.map S ν))
          + ENNReal.ofReal (η : ℝ) :=
        add_le_add (ENNReal.ofReal_le_ofReal hg_val) le_rfl
    _ ≤ wassersteinCost c (Measure.map T μ) (Measure.map S ν) + ENNReal.ofReal (η : ℝ) :=
        add_le_add (by
          unfold wassersteinCost
          exact le_iSup_of_le g (le_iSup
            (f := fun (_ : ∀ x y, |g x - g y| ≤ c x y) =>
              ENNReal.ofReal (∫ x, g x ∂(Measure.map T μ) - ∫ x, g x ∂(Measure.map S ν)))
            hg_adm)) le_rfl
    _ = wassersteinCost c (Measure.map T μ) (Measure.map S ν) + (η : ℝ≥0∞) := by
        rw [ENNReal.ofReal_coe_nnreal]

/-- **Single-map dual bound.**  The
dual cost between a pushforward `Measure.map T μ` and `μ` is at most the integrated
transport cost of `T`.  Direct dual-side analogue of `wassersteinCostCoupling_map_le`:
for any `c`-admissible test `f` (oscillation `≤ c`, hence continuous), the change of
variables `∫ f d(T_# μ) = ∫ f∘T dμ` plus `|f(Tx) − f x| ≤ c x (Tx)` gives the bound;
the finite `c`-moment `hμ_cm` controls test-function integrability. -/
theorem wassersteinCost_dual_singleMap_le
    {α : Type*} [MeasurableSpace α] [PseudoMetricSpace α] [BorelSpace α]
    [SecondCountableTopology α]
    (c : α → α → ℝ) (hc_nonneg : ∀ x y, 0 ≤ c x y) (hc_self : ∀ x, c x x = 0)
    (hc_symm : ∀ x y, c x y = c y x)
    (hc_cont : Continuous (fun p : α × α => c p.1 p.2))
    (μ : Measure α) [IsProbabilityMeasure μ] (x₀ : α)
    (hμ_cm : Integrable (fun y => c y x₀) μ)
    (T : α → α) (hT : Measurable T) :
    wassersteinCost c (Measure.map T μ) μ ≤ ∫⁻ x, ENNReal.ofReal (c x (T x)) ∂μ := by
  unfold wassersteinCost
  refine iSup_le fun f => iSup_le fun hf => ?_
  by_cases hItop : (∫⁻ x, ENNReal.ofReal (c x (T x)) ∂μ) = ⊤
  · rw [hItop]; exact le_top
  -- f is continuous: oscillation `≤ c`, `c` continuous, `c a a = 0`.
  have hf_cont : Continuous f := by
    rw [Metric.continuous_iff]
    intro a ε hε
    have hca : Continuous (fun x => c x a) :=
      hc_cont.comp (continuous_id.prodMk continuous_const)
    have hca0 : Filter.Tendsto (fun x => c x a) (nhds a) (nhds 0) := by
      have h := hca.tendsto a
      rwa [hc_self a] at h
    obtain ⟨δ, hδ0, hδ⟩ := Metric.tendsto_nhds_nhds.1 hca0 ε hε
    refine ⟨δ, hδ0, fun x hx => ?_⟩
    have hcxa : dist (c x a) 0 < ε := hδ hx
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hc_nonneg x a)] at hcxa
    calc dist (f x) (f a) = |f x - f a| := Real.dist_eq _ _
      _ ≤ c x a := hf x a
      _ < ε := hcxa
  have hf_meas : Measurable f := hf_cont.measurable
  -- `f` is `μ`-integrable: `|f x| ≤ |f x₀| + c x x₀`, with `c · x₀` integrable.
  have hf_int_mu : Integrable f μ := by
    have hbound : ∀ x, |f x| ≤ |f x₀| + c x x₀ := fun x => by
      calc |f x|
          = |(f x - f x₀) + f x₀| := by ring_nf
        _ ≤ |f x - f x₀| + |f x₀| := abs_add_le _ _
        _ ≤ c x x₀ + |f x₀| := by have := hf x x₀; linarith
        _ = |f x₀| + c x x₀ := by ring
    refine ((integrable_const |f x₀|).add hμ_cm).mono hf_cont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    simp only [Real.norm_eq_abs, Pi.add_apply,
      abs_of_nonneg (add_nonneg (abs_nonneg (f x₀)) (hc_nonneg x x₀))]
    exact hbound x
  -- `c · (T ·)` is integrable (the `I < ⊤` case).
  have hcT_meas : Measurable (fun x => c x (T x)) :=
    hc_cont.measurable.comp (measurable_id.prodMk hT)
  have hcT_int : Integrable (fun x => c x (T x)) μ := by
    refine ⟨hcT_meas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    have henorm : ∀ x, ‖c x (T x)‖ₑ = ENNReal.ofReal (c x (T x)) := fun x => by
      rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hc_nonneg x (T x))]
    simp_rw [henorm]
    exact lt_top_iff_ne_top.mpr hItop
  -- `f ∘ T` is `μ`-integrable: `|f (T x)| ≤ |f x| + c x (T x)`.
  have hfT_int : Integrable (fun x => f (T x)) μ := by
    have hbound2 : ∀ x, |f (T x)| ≤ |f x| + c x (T x) := fun x => by
      have h1 := hf (T x) x
      rw [hc_symm (T x) x] at h1
      calc |f (T x)|
          = |(f (T x) - f x) + f x| := by ring_nf
        _ ≤ |f (T x) - f x| + |f x| := abs_add_le _ _
        _ ≤ c x (T x) + |f x| := by linarith
        _ = |f x| + c x (T x) := by ring
    refine (hf_int_mu.abs.add hcT_int).mono (hf_meas.comp hT).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    simp only [Real.norm_eq_abs, Pi.add_apply,
      abs_of_nonneg (add_nonneg (abs_nonneg (f x)) (hc_nonneg x (T x)))]
    exact hbound2 x
  -- change of variables + integrand bound.
  have hcov : (∫ x, f x ∂(Measure.map T μ)) = ∫ x, f (T x) ∂μ :=
    integral_map hT.aemeasurable hf_cont.aestronglyMeasurable
  rw [hcov, ← integral_sub hfT_int hf_int_mu]
  have hmono : (∫ x, (f (T x) - f x) ∂μ) ≤ ∫ x, c x (T x) ∂μ := by
    refine integral_mono_ae (hfT_int.sub hf_int_mu) hcT_int
      (Filter.Eventually.of_forall fun x => ?_)
    have h1 := hf (T x) x
    rw [hc_symm (T x) x] at h1
    calc f (T x) - f x ≤ |f (T x) - f x| := le_abs_self _
      _ ≤ c x (T x) := h1
  refine (ENNReal.ofReal_le_ofReal hmono).trans (le_of_eq ?_)
  exact ofReal_integral_eq_lintegral_ofReal hcT_int
    (Filter.Eventually.of_forall fun x => hc_nonneg x (T x))

/-- **Dual-side stability under
pushforward.**  A `c`-admissible test function changes value by at most the
transport cost, so the dual sup over `(T_# μ, S_# ν)` exceeds that over `(μ, ν)`
by at most the two transport costs.  Dual triangle (`wassersteinCost_triangle`)
through `μ` then `ν`, with each single-map leg bounded by
`wassersteinCost_dual_singleMap_le`. -/
theorem wassersteinCost_dual_le_add_map
    {α : Type*} [MeasurableSpace α] [PseudoMetricSpace α] [BorelSpace α]
    [SecondCountableTopology α]
    (c : α → α → ℝ) (hc_nonneg : ∀ x y, 0 ≤ c x y) (hc_self : ∀ x, c x x = 0)
    (hc_symm : ∀ x y, c x y = c y x)
    (hc_cont : Continuous (fun p : α × α => c p.1 p.2))
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (T S : α → α) (hT : Measurable T) (hS : Measurable S)
    (x₀ : α)
    (hμ_cm : Integrable (fun y => c y x₀) μ) (hν_cm : Integrable (fun y => c y x₀) ν) :
    wassersteinCost c (Measure.map T μ) (Measure.map S ν)
      ≤ wassersteinCost c μ ν
        + (∫⁻ x, ENNReal.ofReal (c x (T x)) ∂μ)
        + (∫⁻ y, ENNReal.ofReal (c y (S y)) ∂ν) := by
  have htri1 := wassersteinCost_triangle c (Measure.map T μ) μ (Measure.map S ν)
  have htri2 := wassersteinCost_triangle c μ ν (Measure.map S ν)
  have hT_bound : wassersteinCost c (Measure.map T μ) μ
      ≤ ∫⁻ x, ENNReal.ofReal (c x (T x)) ∂μ :=
    wassersteinCost_dual_singleMap_le c hc_nonneg hc_self hc_symm hc_cont μ x₀ hμ_cm T hT
  have hS_bound : wassersteinCost c ν (Measure.map S ν)
      ≤ ∫⁻ y, ENNReal.ofReal (c y (S y)) ∂ν := by
    rw [wassersteinCost_comm c ν (Measure.map S ν)]
    exact wassersteinCost_dual_singleMap_le c hc_nonneg hc_self hc_symm hc_cont ν x₀ hν_cm S hS
  calc wassersteinCost c (Measure.map T μ) (Measure.map S ν)
      ≤ wassersteinCost c (Measure.map T μ) μ + wassersteinCost c μ (Measure.map S ν) := htri1
    _ ≤ wassersteinCost c (Measure.map T μ) μ
          + (wassersteinCost c μ ν + wassersteinCost c ν (Measure.map S ν)) :=
        add_le_add le_rfl htri2
    _ ≤ (∫⁻ x, ENNReal.ofReal (c x (T x)) ∂μ)
          + (wassersteinCost c μ ν + (∫⁻ y, ENNReal.ofReal (c y (S y)) ∂ν)) :=
        add_le_add hT_bound (add_le_add le_rfl hS_bound)
    _ = wassersteinCost c μ ν
          + (∫⁻ x, ENNReal.ofReal (c x (T x)) ∂μ)
          + (∫⁻ y, ENNReal.ofReal (c y (S y)) ∂ν) := by abel

/-- **Hard direction of Kantorovich–Rubinstein duality** — the primal
coupling-formula is at most the dual-formula.

For probability measures `μ, ν` with finite first moment on a Polish (here
second-countable Borel pseudometric, standard Borel) space and a continuous
pseudometric cost `c`:  `wassersteinCostCoupling c μ ν ≤ wassersteinCost c μ ν`.
The reverse inequality is the easy direction
`wasserstein1_le_wasserstein1Coupling`; together they give the full KR equality
`wasserstein1_eq_coupling`.

This is an `inf ≤ sup` statement, so the infimum need not be attained — the bound
is reached ε-optimally.  Stated cost-generically over a continuous pseudometric
`c`, so a cutoff cost `c = min (dist ·) 1` reuses it verbatim.

**Proof** (discrete approximation + limit).  For `ε > 0` pick finite-range
`T, S` with transport cost `≤ ε/4` each (`exists_finiteRange_map_cost_le`).  With
`μ' = Measure.map T μ`, `ν' = Measure.map S ν`:
`W_c(μ,ν) ≤ W_c(μ,μ') + W_c(μ',ν') + W_c(ν',ν)`
(`wassersteinCostCoupling_triangle` ×2, `…_comm`); the outer terms `≤ ε/4`
(`wassersteinCostCoupling_map_le`); `W_c(μ',ν') ≤ dual(μ',ν')`
(`wassersteinCostCoupling_le_dual_of_finiteRange`); `dual(μ',ν') ≤ dual(μ,ν) +
ε/2` (`wassersteinCost_dual_le_add_map`).  Chain → `W_c(μ,ν) ≤ dual(μ,ν) + ε`;
`ε → 0` (`ENNReal.le_of_forall_pos_le_add`).  The triangle step needs
`StandardBorelSpace α` (disintegration); consumers instantiate at the Polish
`PhaseSpace d`. -/
theorem wassersteinCostCoupling_le_dual
    {α : Type*} [MeasurableSpace α] [PseudoMetricSpace α] [BorelSpace α]
    [SecondCountableTopology α] [StandardBorelSpace α]
    (c : α → α → ℝ)
    (hc_nonneg : ∀ x y, 0 ≤ c x y)
    (hc_self : ∀ x, c x x = 0)
    (hc_symm : ∀ x y, c x y = c y x)
    (hc_triangle : ∀ x y z, c x z ≤ c x y + c y z)
    (hc_cont : Continuous (fun p : α × α => c p.1 p.2))
    (hc_le_dist : ∀ x y, c x y ≤ dist x y)
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (x₀ : α)
    (hμ_cm : Integrable (fun y => c y x₀) μ)
    (hν_cm : Integrable (fun y => c y x₀) ν) :
    wassersteinCostCoupling c μ ν ≤ wassersteinCost c μ ν := by
  -- ε→0; for each ε pick finite-range approximants T, S with transport cost ≤ ε/4.
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _hb => ?_
  have hε4 : (0 : ℝ) < (ε : ℝ) / 4 := by positivity
  obtain ⟨T, hT, hTfin, hTcost⟩ :=
    exists_finiteRange_map_cost_le c hc_nonneg hc_le_dist μ x₀ hμ_cm
      ((ε : ℝ) / 4) hε4
  obtain ⟨S, hS, hSfin, hScost⟩ :=
    exists_finiteRange_map_cost_le c hc_nonneg hc_le_dist ν x₀ hν_cm
      ((ε : ℝ) / 4) hε4
  haveI : IsProbabilityMeasure (Measure.map T μ) := Measure.isProbabilityMeasure_map hT.aemeasurable
  haveI : IsProbabilityMeasure (Measure.map S ν) := Measure.isProbabilityMeasure_map hS.aemeasurable
  set q : ℝ≥0∞ := ENNReal.ofReal ((ε : ℝ) / 4) with hq
  -- triangle through the two approximants
  have htri1 := wassersteinCostCoupling_triangle c hc_triangle hc_cont.measurable
    μ ν (Measure.map T μ)
  have htri2 := wassersteinCostCoupling_triangle c hc_triangle hc_cont.measurable
    (Measure.map T μ) ν (Measure.map S ν)
  -- the two outer transport terms are ≤ q
  have hμμ' : wassersteinCostCoupling c μ (Measure.map T μ) ≤ q :=
    (wassersteinCostCoupling_map_le c hc_cont μ T hT).trans hTcost
  have hν'ν : wassersteinCostCoupling c (Measure.map S ν) ν ≤ q := by
    rw [wassersteinCostCoupling_comm c hc_symm hc_cont.measurable (Measure.map S ν) ν]
    exact (wassersteinCostCoupling_map_le c hc_cont ν S hS).trans hScost
  -- the middle: finite KR duality, then dual stability, then bound the two costs by q
  have hmid : wassersteinCostCoupling c (Measure.map T μ) (Measure.map S ν)
      ≤ wassersteinCost c μ ν + q + q :=
    (wassersteinCostCoupling_le_dual_of_finiteRange c hc_nonneg hc_self hc_symm hc_triangle
        hc_cont.measurable μ ν T S hT hS hTfin hSfin).trans
      ((wassersteinCost_dual_le_add_map c hc_nonneg hc_self hc_symm hc_cont μ ν T S hT hS
          x₀ hμ_cm hν_cm).trans
        (add_le_add (add_le_add le_rfl hTcost) hScost))
  -- 4q = ofReal ε = ↑ε
  have hq4 : q + q + q + q = (ε : ℝ≥0∞) := by
    have h4 : q + q + q + q
        = ENNReal.ofReal ((ε : ℝ) / 4 + (ε : ℝ) / 4 + (ε : ℝ) / 4 + (ε : ℝ) / 4) := by
      rw [hq, ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
    rw [h4, show (ε : ℝ) / 4 + (ε : ℝ) / 4 + (ε : ℝ) / 4 + (ε : ℝ) / 4 = (ε : ℝ) from by ring,
      ENNReal.ofReal_coe_nnreal]
  calc wassersteinCostCoupling c μ ν
      ≤ wassersteinCostCoupling c μ (Measure.map T μ)
          + wassersteinCostCoupling c (Measure.map T μ) ν := htri1
    _ ≤ q + (wassersteinCostCoupling c (Measure.map T μ) (Measure.map S ν)
          + wassersteinCostCoupling c (Measure.map S ν) ν) := add_le_add hμμ' htri2
    _ ≤ q + ((wassersteinCost c μ ν + q + q) + q) := add_le_add le_rfl (add_le_add hmid hν'ν)
    _ = wassersteinCost c μ ν + (q + q + q + q) := by ring
    _ = wassersteinCost c μ ν + (ε : ℝ≥0∞) := by rw [hq4]

/-- KR duality at `c = dist`: `wasserstein1 = wasserstein1Coupling`.  Combines the
hard-direction inequality `wassersteinCostCoupling_le_dual` with the easy direction
`wasserstein1_le_wasserstein1Coupling`. -/
theorem wasserstein1_eq_coupling
    {α : Type*} [MeasurableSpace α] [PseudoMetricSpace α] [BorelSpace α]
    [SecondCountableTopology α] [StandardBorelSpace α]
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (x₀ : α)
    (hμ_fm : Integrable (fun y => dist y x₀) μ)
    (hν_fm : Integrable (fun y => dist y x₀) ν) :
    wasserstein1 μ ν = wasserstein1Coupling μ ν := by
  refine le_antisymm (wasserstein1_le_wasserstein1Coupling μ ν x₀ hμ_fm hν_fm) ?_
  rw [wasserstein1Coupling_eq]
  exact wassersteinCostCoupling_le_dual (fun x y => dist x y) (fun _ _ => dist_nonneg)
    (fun x => dist_self x) (fun x y => dist_comm x y) (fun x y z => dist_triangle x y z)
    (continuous_fst.dist continuous_snd) (fun x y => le_refl (dist x y)) μ ν x₀ hμ_fm hν_fm

/-! ## Pushforward of couplings

These lemmas bridge from coupling-based bounds on initial measures (`μ`, `ν`) to
coupling-based bounds on pushed-forward measures (`Φ_# μ`, `Ψ_# ν`), which is how
the Dobrushin proof connects characteristic flows back to W₁ growth.
-/

/-- Pushforward of a coupling under a pair of measurable maps is a coupling
of the pushed-forward marginals.  Pure measure theory; no metric structure
needed.

This is the *generic α/β shape* — the codomain types `α'`, `β'` can be
arbitrary measurable spaces, not necessarily equal to the domain.  This
matters because the characteristic-flow application uses
`(Prod.map Φ Ψ)` with `Φ` and `Ψ` distinct maps; the diagonal
case `α' = α, Φ = Ψ` is a specialization. -/
lemma IsCoupling.map {α β α' β' : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace α'] [MeasurableSpace β']
    {π : Measure (α × β)} {μ : Measure α} {ν : Measure β}
    (hπ : IsCoupling π μ ν)
    (Φ : α → α') (Ψ : β → β')
    (hΦ : Measurable Φ) (hΨ : Measurable Ψ) :
    IsCoupling (Measure.map (Prod.map Φ Ψ) π) (Measure.map Φ μ) (Measure.map Ψ ν) := by
  refine ⟨?_, ?_⟩
  · -- fst marginal: Measure.map Prod.fst (Measure.map (Prod.map Φ Ψ) π) = Measure.map Φ μ
    have h_comp_fst : Prod.fst ∘ Prod.map Φ Ψ = Φ ∘ Prod.fst := by funext; rfl
    rw [Measure.map_map measurable_fst (hΦ.prodMap hΨ), h_comp_fst,
        ← Measure.map_map hΦ measurable_fst, hπ.1]
  · -- snd marginal: Measure.map Prod.snd (Measure.map (Prod.map Φ Ψ) π) = Measure.map Ψ ν
    have h_comp_snd : Prod.snd ∘ Prod.map Φ Ψ = Ψ ∘ Prod.snd := by funext; rfl
    rw [Measure.map_map measurable_snd (hΦ.prodMap hΨ), h_comp_snd,
        ← Measure.map_map hΨ measurable_snd, hπ.2]

/-- The dual-formula `wasserstein1` of the pushed-forward measures is bounded
above by the infimum over couplings of the original measures of the
pushed-forward cost.  This is the "iInf trick":

  wasserstein1 (Φ_# μ) (Ψ_# ν)
    ≤ wasserstein1Coupling (Φ_# μ) (Ψ_# ν)            (KR easy)
    = ⨅ π' (coupling of Φ_# μ, Ψ_# ν), ∫⁻ edist dπ'
    ≤ ⨅ π  (coupling of μ, ν), ∫⁻ edist (Φ z.1, Ψ z.2) dπ   (push couplings via IsCoupling.map)

Used in the dobrushin proof: applied with `Φ`, `Ψ` the characteristic
flows of `f`, `g` at time `t` (or the difference flow), this turns a
W₁-bound on `(f_t, g_t)` into a coupling-cost bound on `(f_0, g_0)`
that can be controlled by Gronwall. -/
lemma wasserstein1_pushforward_le_iInf
    {α : Type*} [MeasurableSpace α] [PseudoMetricSpace α] [BorelSpace α]
    [SecondCountableTopology α]
    (Φ Ψ : α → α) (hΦ : Measurable Φ) (hΨ : Measurable Ψ)
    (μ ν : Measure α)
    (x₀ : α)
    (hΦμ_prob : IsProbabilityMeasure (Measure.map Φ μ))
    (hΨν_prob : IsProbabilityMeasure (Measure.map Ψ ν))
    (hΦμ_fm : Integrable (fun y => dist y x₀) (Measure.map Φ μ))
    (hΨν_fm : Integrable (fun y => dist y x₀) (Measure.map Ψ ν)) :
    wasserstein1 (Measure.map Φ μ) (Measure.map Ψ ν) ≤
      ⨅ (π : Measure (α × α)) (_ : IsCoupling π μ ν),
        ∫⁻ z, edist (Φ z.1) (Ψ z.2) ∂π := by
  haveI := hΦμ_prob
  haveI := hΨν_prob
  -- Step 1: KR easy applied to (Φ_# μ, Ψ_# ν).
  have h_kr := wasserstein1_le_wasserstein1Coupling
    (Measure.map Φ μ) (Measure.map Ψ ν) x₀ hΦμ_fm hΨν_fm
  refine le_trans h_kr ?_
  -- Step 2: bound wasserstein1Coupling via a specific pushed-forward coupling.
  refine le_iInf fun π => le_iInf fun hπ => ?_
  -- The pushed-forward coupling IS a coupling of (Φ_# μ, Ψ_# ν) by IsCoupling.map.
  have hπ_pushed : IsCoupling (Measure.map (Prod.map Φ Ψ) π)
                              (Measure.map Φ μ) (Measure.map Ψ ν) :=
    hπ.map Φ Ψ hΦ hΨ
  -- So wasserstein1Coupling ≤ ∫⁻ edist d(pushed-forward π).
  have h_inf : wasserstein1Coupling (Measure.map Φ μ) (Measure.map Ψ ν) ≤
      ∫⁻ z, edist z.1 z.2 ∂(Measure.map (Prod.map Φ Ψ) π) := by
    refine iInf_le_of_le (Measure.map (Prod.map Φ Ψ) π) ?_
    exact iInf_le _ hπ_pushed
  refine le_trans h_inf ?_
  -- Step 3: pushforward of the lintegral.
  -- ∫⁻ z, edist z.1 z.2 ∂(Φ × Ψ)_# π = ∫⁻ z, edist (Φ z.1) (Ψ z.2) ∂π
  rw [lintegral_map (measurable_fst.edist measurable_snd) (hΦ.prodMap hΨ)]
  -- After rw: ∫⁻ z, edist (Prod.map Φ Ψ z).1 (Prod.map Φ Ψ z).2 ∂π ≤ ∫⁻ z, edist (Φ z.1) (Ψ z.2) ∂π
  -- (Prod.map Φ Ψ z).1 = Φ z.1 and .2 = Ψ z.2 by definition; the integrals are pointwise equal.
  rfl

end Vlasov
