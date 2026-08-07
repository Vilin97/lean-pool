/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.Abel.WeakToMero
import LeanPool.JacobianDiffgeo.Abel.DolbeaultBridge

/-!
# abel-theorem: the sufficiency direction (`docs/design/abel-theorem.md` §4.1 D1, §2.1)

Unit: abel-theorem. Namespace `RS.Abel`. The unit's centerpiece.

## Status: the external blocker (`serre-duality-tails` not existing) has CLEARED; the isolated
hypotheses below are now DISCHARGED modulo that unit's ONE remaining fact

**UPDATE (upgrade-discharge pass)**: `WeakSolutionUpgrade X` and `WeakSolutionUpgradeFinset X ι`
are now PROVEN in `UpgradeDischarge.lean` (`weakSolutionUpgrade_of_surjective` /
`weakSolutionUpgradeFinset_of_surjective`), gated ONLY on `serre-duality-tails`'s single
remaining external fact `Function.Surjective (RS.LaurentTail.tailToH1 (0 : RS.Divisor X))` —
the same gate `DolbeaultBridge.lean` carries. The defs below are kept as the frozen consumer
interface (`period-lattice-rank` cites them); the historical account of the gap follows.

`exists_mero_of_pathIntegral_mem`'s proof is complete through step 4 of the design's own §2.1
proof plan (loop cancellation via `Loops.lean` + the weak solution `f` via
`RS.AbelWeak.exists_weakSolutionOfPair`, fully built — see `AbelWeak/GeneralChain.lean`). Step 6
of the plan (the abstract Dolbeault-upgrade bridge itself, "a vanishing residue pairing forces
`d''`-exactness") is now **fully proved**, `DolbeaultBridge.lean`'s
`exists_dbar_eq_zero_of_forall_basis_pairing_eq_zero`, gated ONLY on
`serre-duality-tails`'s own one remaining external fact
(`Function.Surjective (RS.LaurentTail.tailToH1 (0 : RS.Divisor X))`, a genuine Cousin-I/Mittag-
Leffler-style existence theorem, out of scope for this challenge per `laurent-tails`' own
`Comparison.lean` file-end note) — see that file's docstring for the full account of why the
design's ORIGINAL bridge shape (through `H1Tail.equiv`, the FULL unconditional Čech comparison)
had to be restated at the tail level instead.

**What remains open, and why it is a genuinely different (non-external, new-content) gap from the
one just closed**: design step 5 — packaging a weak solution `f`'s chart-local `d''f/f` data into
one concrete `η : RS.Form01 X`, and PROVING `η` pairs to zero against a basis of `Form1 X` (via
the residue identity, `abel-weak-solutions` §7.3, tied to `f`'s own `GeneralChain` construction) —
was never built by any unit (`abel-weak-solutions` explicitly does not build a global object, by
its own design; this unit's own design doc calls it "this unit's own packaging step", §2.1 step 5,
independent of `serre-duality-tails`). Investigation for this pass (recorded in full in the
build-log) confirmed this is substantial, genuinely new analytic content — assembling a finite
`DbarGlueData`-style cover of `X` compatible with `f`'s own chain construction, and connecting its
pairing to `pathIntegral_eq_sum_chartChain`'s telescoping, tied to `GeneralChain.lean`'s internal
(not exported) chain data — comparable in scope to a further sibling unit, not a short remainder.
It is isolated as PRECISELY as possible below as the single hypothesis `WeakSolutionUpgrade`
(bundling design steps 5 AND 7 — the CR-promotion order bookkeeping of step 7 was investigated in
detail and found tractable, given step 5, via `Jacobian/Dbar/Operator.lean`'s
`contMDiffOn_omega_of_isDbarOn_zero` + mathlib's `Complex.differentiableOn_compl_singleton_and_
continuousAt_iff` removable-singularity theorem + `meromorphicOrderAt_mul`/`_zpow_id_sub_const` —
but was not completed this pass on top of everything else). `WeakSolutionUpgrade`'s docstring
records the exact discharge roadmap: apply the packaging construction to get `η` and its
pairing-vanishing, feed `η` into the NOW-PROVEN `exists_dbar_eq_zero_of_forall_basis_pairing_eq_
zero` to get `u`, then run the (sketched, tractable) step-7 argument.

The **easy/necessity direction** (§2.2, "`∃F` with one simple pole `⟹` `genus X = 0`") is fully
built, no admitted steps: `genus_eq_zero_of_exists_simple_pole` (`WeakToMero.lean`).
-/

open scoped ContDiff Manifold

noncomputable section

namespace RS.Abel

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

omit [CompactSpace X] in
/-- **The one remaining, precisely-isolated hypothesis** (see the file docstring): Forster's own
Lemma 20.3 + design §4.1 steps 5 and 7, bundled — given a weak solution `f` of a pair `(P, Q)`
along a path `δ` whose integral against EVERY holomorphic `1`-form vanishes EXACTLY (not just on
a basis; `Loops.lean`'s `exists_zeroPeriod_path` already delivers exactly this strength), `f`
upgrades to an honest meromorphic function with the same simple-zero/simple-pole data. The
ABSTRACT half of this fact (a vanishing residue pairing forces `d''`-exactness) is
`exists_dbar_eq_zero_of_forall_basis_pairing_eq_zero` (`DolbeaultBridge.lean`), PROVEN, gated
only on `serre-duality-tails`'s own remaining external blocker. Discharging `WeakSolutionUpgrade`
in full needs, additionally: (1) package `f`'s chart-local `wirtingerDbar f / f` data into a
global `η : RS.Form01 X` (design §4.1 step 5, e.g. via a `DbarGlueData`-style finite cover tied to
`f`'s own `ChartChain`/`GeneralChain` construction) and show `η` pairs to zero against a basis of
`Form1 X` (via `abel-weak-solutions`' §7.3 residue identity + `pathIntegral_eq_sum_chartChain`,
run against each basis element, using this hypothesis's own zero-period assumption); (2) feed `η`
into `exists_dbar_eq_zero_of_forall_basis_pairing_eq_zero` (supplying its own
`Function.Surjective (RS.LaurentTail.tailToH1 (0 : RS.Divisor X))` gate) to get
`u : RS.SmoothC X` with `RS.dbar u = η`; (3) set `F := fun z => Complex.exp (-(u z)) * f z` and
promote to genuine holomorphy off `Q` (design §4.1 step 7) via
`Jacobian.Dbar.Operator.contMDiffOn_omega_of_isDbarOn_zero` (applied on the open set `{Q}ᶜ`, using
`wirtingerDbar_exp_neg_mul_eq_zero`, ALREADY BUILT in `WeakToMero.lean`, for the `IsDbarOn F 0`
hypothesis off `{P, Q}`, plus a short direct `wirtingerDbar f P = 0` computation from `f`'s own
`IsWeakSolutionAt f P 1` local model to extend `IsDbarOn` across `P` too), package as
`MeroGermOn.mk F hF : RS.Mero X`, and read off the order claims from `f`'s known local models via
`ordAtX_eq_of_mem_source`'s chart-invariance (no rechart needed) + `meromorphicOrderAt_mul`/
`meromorphicOrderAt_zpow_id_sub_const` at `P`, and (using mathlib's
`Complex.differentiableOn_compl_singleton_and_continuousAt_iff` removable-singularity theorem to
extend holomorphy of the local `ψ`-cofactor across the puncture) similarly at `Q`. Investigated
and found tractable in outline this pass (recorded above and in the build log) but not completed
on top of everything else — this is precisely the boundary of what this pass closed. -/
def WeakSolutionUpgrade (X : Type*) [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] : Prop :=
  ∀ {f : X → ℂ} {P Q : X}, Q ≠ P → ∀ δ : Path Q P, RS.AbelWeak.IsWeakSolutionOfPair f P Q →
    (∀ θ : RS.Form1 X, RS.pathIntegral δ θ = 0) →
    ∃ F : RS.Mero X, F ≠ 0 ∧ F.ord P = 1 ∧ F.ord Q = -1 ∧ ∀ z, z ≠ Q → z ≠ P → F.ord z = 0

/-- **Forster 20.7, sufficiency direction, two-point form** (§4.1 D1, the blueprint's literal
"two-point Abel–Jacobi value" statement). Proof complete through step 4 of the design's §2.1 plan
(loop cancellation, `Loops.lean`, + weak-solution existence, `AbelWeak.exists_weakSolutionOfPair`,
fully built); steps 5-7 (the Dolbeault-upgrade bridge's packaging half + CR-promotion) are
isolated as the explicit hypothesis `hupgrade : WeakSolutionUpgrade X` — see that def's docstring
and the file docstring for the precise account of what is proven vs. what remains. -/
theorem exists_mero_of_pathIntegral_mem (hupgrade : WeakSolutionUpgrade X) {P Q : X}
    (hPQ : Q ≠ P) (δ : Path Q P)
    (hmem : (fun k => RS.pathIntegral δ (RS.basis X k)) ∈ RS.periodSubgroup X) :
    ∃ F : RS.Mero X, F ≠ 0 ∧ F.ord P = 1 ∧ F.ord Q = -1 ∧
      ∀ z, z ≠ Q → z ≠ P → F.ord z = 0 := by
  -- Steps 1-3 (§2.1): loop cancellation — `δ'` has EXACT zero period against every `ω`.
  obtain ⟨δ', hδ'⟩ := RS.Abel.exists_zeroPeriod_path δ hmem
  -- Step 4: the weak solution of the pair `(P, Q)` along `δ'` (fully general chart chain,
  -- `AbelWeak/GeneralChain.lean`).
  obtain ⟨f, U, hf, hUopen, hUcompact, hPU, hQU, hf1⟩ :=
    RS.AbelWeak.exists_weakSolutionOfPair hPQ δ'
  -- Steps 5-7: the one remaining hypothesis, see `WeakSolutionUpgrade`'s docstring.
  exact hupgrade hPQ δ' hf hδ'

/-- **The necessity-composed genus-`0` corollary** (the shape `ofCurve_inj'`'s proof needs):
if the basis-period vector of SOME connecting path lies in `RS.periodSubgroup X` for `Q ≠ P`,
then `genus X = 0`. Composes `exists_mero_of_pathIntegral_mem` with the ALREADY-BUILT necessity
shortcut `genus_eq_zero_of_exists_simple_pole` (`WeakToMero.lean`). -/
theorem genus_eq_zero_of_pathIntegral_mem (hupgrade : WeakSolutionUpgrade X) {P Q : X}
    (hPQ : Q ≠ P) (δ : Path Q P)
    (hmem : (fun k => RS.pathIntegral δ (RS.basis X k)) ∈ RS.periodSubgroup X) :
    genus X = 0 := by
  obtain ⟨F, -, hordP, hordQ, hreg⟩ := exists_mero_of_pathIntegral_mem hupgrade hPQ δ hmem
  refine genus_eq_zero_of_exists_simple_pole F Q hordQ (fun x hx => ?_)
  rcases eq_or_ne x P with rfl | hxP
  · rw [hordP]; norm_num
  · rw [hreg x hx hxP]

/-! ## The `k`-point generalization (§4.1, the shape `period-lattice-rank`'s Thm 21.4(b) needs) -/

omit [CompactSpace X] in
/-- The `Finset`-generalized analogue of `WeakSolutionUpgrade`, bundling Forster's Lemma 20.1
multiplicativity (weak solutions of pairwise-disjoint pairs multiply, `IsWeakSolutionOfFinset` /
`isWeakSolutionOfFinset_prod`, ALREADY BUILT — `AbelWeak/WeakSolution.lean`) with design steps 5
and 7 run once for the assembled product weak solution (`η := ∑ i, η i`, the design's own
account of the `k`-point case, §4.1). Same discharge roadmap as `WeakSolutionUpgrade`'s own
docstring, mechanically re-run for a `Finset`-indexed family instead of a single pair. -/
def WeakSolutionUpgradeFinset (X : Type*) [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] (ι : Type*) [Fintype ι] :
    Prop :=
  ∀ {f : X → ℂ} {a x : ι → X},
    Function.Injective a → Function.Injective x → (∀ i j, a i ≠ x j) →
    (γ : (i : ι) → Path (a i) (x i)) → RS.AbelWeak.IsWeakSolutionOfFinset f a x →
    (∀ θ : RS.Form1 X, ∑ i, RS.pathIntegral (γ i) θ = 0) →
    ∃ F : RS.Mero X, F ≠ 0 ∧ (∀ i, F.ord (x i) = 1) ∧ (∀ i, F.ord (a i) = -1) ∧
      ∀ z, (∀ i, z ≠ a i) → (∀ i, z ≠ x i) → F.ord z = 0

/-- **Forster 20.7, sufficiency direction, `k`-point form** (§4.1 D1 — the shape
`period-lattice-rank`'s own Thm 21.4(b) argument needs, `k` ranging over every `1 ≤ k ≤ genus X`
there, NOT merely the two-point specialization). Steps 1-4 (loop cancellation against the TOTAL
period, generalized from `Loops.lean`'s own two-point argument; a weak solution per pair via
`RS.AbelWeak.exists_weakSolutionOfPair`; Forster's Lemma 20.1 multiplicativity assembling the
product) are fully proved below; steps 5-7 are `WeakSolutionUpgradeFinset`, the `Finset`
generalization of `Sufficiency.lean`'s own `WeakSolutionUpgrade` (same precisely-isolated
remaining content, see that def's docstring). -/
theorem exists_mero_of_periodVector_mem {ι : Type*} [Fintype ι]
    (hupgradeFinset : WeakSolutionUpgradeFinset X ι)
    (a x : ι → X) (ha : Function.Injective a) (hx : Function.Injective x)
    (hax : ∀ i j, a i ≠ x j) (γ : (i : ι) → Path (a i) (x i))
    (hmem : (fun k => ∑ i, RS.pathIntegral (γ i) (RS.basis X k)) ∈ RS.periodSubgroup X) :
    ∃ F : RS.Mero X, F ≠ 0 ∧ (∀ i, F.ord (x i) = 1) ∧ (∀ i, F.ord (a i) = -1) ∧
      ∀ z, (∀ i, z ≠ a i) → (∀ i, z ≠ x i) → F.ord z = 0 := by
  classical
  rcases isEmpty_or_nonempty ι with hE | hN
  · -- Vacuous case (`ι` empty, no pairs at all): the constant `1` trivially works.
    refine ⟨1, one_ne_zero, fun i => (hE.false i).elim, fun i => (hE.false i).elim,
      fun z _ _ => ?_⟩
    exact RS.MeroGermOn.ord_one isOpen_univ (Set.mem_univ z)
  · -- Steps 1-3, `k`-point form: cancel the TOTAL period against one fixed index `i₀`.
    obtain ⟨i0⟩ := hN
    obtain ⟨α, hα⟩ := mem_periodSubgroup_iff_exists_loop.mp hmem
    let σ : Path (a i0) (Classical.arbitrary X) :=
      PathConnectedSpace.somePath (a i0) (Classical.arbitrary X)
    let β : Path (a i0) (a i0) := (σ.trans α).trans σ.symm
    have hβ_period : ∀ k, RS.pathIntegral β (RS.basis X k) = RS.pathIntegral α (RS.basis X k) :=
      fun k => RS.period_conj σ α (RS.basis X k)
    let γ' : (i : ι) → Path (a i) (x i) := Function.update γ i0 (β.symm.trans (γ i0))
    have hγ'_i0 : γ' i0 = β.symm.trans (γ i0) := Function.update_self i0 _ γ
    have hγ'_ne : ∀ i, i ≠ i0 → γ' i = γ i := fun i hi => Function.update_of_ne hi _ γ
    have hbasis : ∀ k, ∑ i, RS.pathIntegral (γ' i) (RS.basis X k) = 0 := by
      intro k
      have hstep : ∑ i, RS.pathIntegral (γ' i) (RS.basis X k)
          = RS.pathIntegral (γ' i0) (RS.basis X k)
            + ∑ i ∈ Finset.univ.erase i0, RS.pathIntegral (γ' i) (RS.basis X k) :=
        (Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i0)).symm
      have hstep2 : ∑ i, RS.pathIntegral (γ i) (RS.basis X k)
          = RS.pathIntegral (γ i0) (RS.basis X k)
            + ∑ i ∈ Finset.univ.erase i0, RS.pathIntegral (γ i) (RS.basis X k) :=
        (Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i0)).symm
      have herase_eq : ∑ i ∈ Finset.univ.erase i0, RS.pathIntegral (γ' i) (RS.basis X k)
          = ∑ i ∈ Finset.univ.erase i0, RS.pathIntegral (γ i) (RS.basis X k) :=
        Finset.sum_congr rfl (fun i hi => by rw [hγ'_ne i (Finset.ne_of_mem_erase hi)])
      have hα_k : RS.pathIntegral α (RS.basis X k) = ∑ i, RS.pathIntegral (γ i) (RS.basis X k) := by
        have := congrFun hα k
        simpa [RS.periodVector, RS.period] using this
      rw [hstep, herase_eq, hγ'_i0, RS.pathIntegral_trans, RS.pathIntegral_symm, hβ_period k,
        hα_k, hstep2]
      ring
    have hlin : ∀ θ : RS.Form1 X, ∑ i, RS.pathIntegral (γ' i) θ = 0 := by
      have hL : (∑ i, RS.pathIntegralₗ (γ' i) : RS.Form1 X →ₗ[ℂ] ℂ) = 0 := by
        apply (RS.basis X).ext
        intro k
        simp only [LinearMap.sum_apply]
        exact hbasis k
      intro θ
      have hθ := congrFun (congrArg DFunLike.coe hL) θ
      simp only [LinearMap.sum_apply] at hθ
      exact hθ
    -- Step 4, `k`-point form: a weak solution per (pairwise-disjoint) pair.
    choose f U hf hUopen hUcompact hxU haU hf1 using
      fun i => RS.AbelWeak.exists_weakSolutionOfPair (hax i i) (γ' i)
    -- Forster's Lemma 20.1: multiply the pairwise-disjoint weak solutions.
    have hfin : RS.AbelWeak.IsWeakSolutionOfFinset (fun z => ∏ i, f i z) a x :=
      RS.AbelWeak.isWeakSolutionOfFinset_prod ha hx hax hf
    exact hupgradeFinset ha hx hax γ' hfin hlin

end RS.Abel

end
