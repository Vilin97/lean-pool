/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.AbelWeak.SingleChart
import LeanPool.JacobianDiffgeo.Path
import LeanPool.JacobianDiffgeo.PlanarStokes

/-!
# Chain assembly (`abel-weak-solutions`, §7)

Unit: abel-weak-solutions (`docs/design/abel-weak-solutions.md` §7). Three deliverables:

* `exists_weakSolutionOfFinset` — the **SCOPE ADDITION** k-point layer
  (`docs/design/abel-theorem.md` §1.4/§4.1): assembled directly from
  `SingleChart.exists_weakSolutionOfPair_chart` (one call per index `i`, each pair already
  living inside its own chart neighbourhood — exactly what `abel-theorem`'s own Thm 21.4(a)
  disjoint-chart construction sets up, per its design §1.4: "`k` pairwise disjoint two-point
  pieces, each already a `Path (a i) (x i)` living inside its own chart neighborhood") plus
  `WeakSolution.isWeakSolutionOfFinset_prod`.
* `pathIntegral_eq_sum_chartChain` (§7.2) — the CC6-compliant telescoped path-integral identity,
  pure `Path`-API bookkeeping (no Stokes).
* the Lemma-20.3-specialized residue identity (§7.3) — the harder, Stokes-driven half, via the
  two-puncture `planar-stokes-atoms` export
  `RS.integral_wirtingerDbar_mul_inv_sub_sub_inv_sub_eq`.

**Status note on the general multi-chart `exists_weakSolutionOfPair`** (design §6.3/§7.1, for an
arbitrary path not confined to one chart): this file does NOT build it (only the disjoint-chart
`k`-point layer above, and the telescoping/residue atoms). It is now built, in
`Rechart.lean` + `GeneralChain.lean` (added by the `abel-theorem` builder, authorized to close
this exact gap) — see the root file `Jacobian/AbelWeak.lean` for the full account: the missing
piece was a "rechart" lemma for `IsWeakSolutionAt` (transporting a simple-zero/pole local model
across a holomorphic chart transition via mathlib's removable-singularity theorem), plus a chain
induction gluing `SingleChart` pieces at every interior breakpoint via a fully general
order-additive `IsWeakSolutionAt.mul`.
-/

open scoped ContDiff Manifold
open IsManifold Metric Set Filter Topology

noncomputable section

namespace RS.AbelWeak

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ## The `k`-point layer (SCOPE ADDITION, `abel-theorem`'s Thm 21.4(a)/(b) finding) -/

/-- **Forster's Lemma 20.1, assembled**: given `k` pairwise-disjoint pairs `(x i, a i)`, each
already living inside a common chart `e i` (matching the shape `abel-theorem`'s own disjoint-chart
21.4(a) construction produces), there is a weak solution of the whole `k`-point configuration,
equal to `1` outside a compact neighbourhood of the union of the per-pair chart balls. -/
theorem exists_weakSolutionOfFinset {ι : Type*} [Finite ι]
    (a x : ι → X) (ha : Function.Injective a) (hx : Function.Injective x)
    (hax : ∀ i j, a i ≠ x j)
    {e : ι → OpenPartialHomeomorph X ℂ} (he : ∀ i, e i ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X)
    (has : ∀ i, a i ∈ (e i).source) (hxs : ∀ i, x i ∈ (e i).source)
    {c : ι → ℂ} {ρ : ι → ℝ} (hρ : ∀ i, 0 < ρ i)
    (haQ : ∀ i, e i (a i) - c i ∈ Metric.ball (0 : ℂ) (ρ i))
    (haP : ∀ i, e i (x i) - c i ∈ Metric.ball (0 : ℂ) (ρ i))
    (ψ : ι → ContDiffBump (0 : ℂ)) (hρψ : ∀ i, ρ i < (ψ i).rIn)
    (hballsub : ∀ i, Metric.closedBall (c i) (ψ i).rOut ⊆ (e i).target) :
    ∃ (f : X → ℂ) (U : Set X), IsWeakSolutionOfFinset f a x ∧
      IsOpen U ∧ IsCompact (closure U) ∧ (∀ i, x i ∈ U) ∧ (∀ i, a i ∈ U) ∧
      (∀ z ∉ U, f z = 1) := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  choose f hf hUopen hUcompact hxU haU hf1 using
    fun i => exists_weakSolutionOfPair_chart (hax i i).symm (he i) (hxs i) (has i)
      (hρ i) (haQ i) (haP i) (ψ i) (hρψ i) (hballsub i)
  set U : ι → Set X := fun i => (e i).symm '' Metric.ball (c i) (ψ i).rOut with hU_def
  refine ⟨fun z => ∏ i, f i z, ⋃ i, U i, isWeakSolutionOfFinset_prod ha hx hax hf,
    isOpen_iUnion hUopen, ?_, fun i => Set.mem_iUnion.mpr ⟨i, hxU i⟩,
    fun i => Set.mem_iUnion.mpr ⟨i, haU i⟩, ?_⟩
  · have hclosed : IsClosed (⋃ i, closure (U i)) :=
      isClosed_iUnion_of_finite (fun i => isClosed_closure)
    have hsub : (⋃ i, U i) ⊆ ⋃ i, closure (U i) :=
      Set.iUnion_mono (fun i => subset_closure)
    have h1 : closure (⋃ i, U i) ⊆ ⋃ i, closure (U i) := closure_minimal hsub hclosed
    have h2 : IsCompact (⋃ i, closure (U i)) := isCompact_iUnion (fun i => hUcompact i)
    exact h2.of_isClosed_subset isClosed_closure h1
  · intro z hz
    simp only [Set.mem_iUnion, not_exists] at hz
    have : ∀ i, f i z = 1 := fun i => hf1 i z (hz i)
    simp [this]

/-! ## §7.2: the telescoped path-integral identity (pure `Path`-API, no Stokes) -/

omit [T2Space X] in
/-- **The CC6-compliant replacement for Forster's `∫∫_X`-formula (D5)**: for any `ω : Form1 X` and
any `ChartChain` `C` adapted to `γ`, `pathIntegral γ ω` is exactly the finite telescoped sum of
chart-local holomorphic-primitive differences. -/
theorem pathIntegral_eq_sum_chartChain {x y : X} {γ : Path x y} (C : RS.ChartChain γ)
    (η : RS.Form1 X) (g : (k : ℕ) → ℂ → ℂ)
    (hg : ∀ k, k < C.n → ∀ z ∈ Metric.ball (C.c k) (C.r k),
      HasDerivAt (g k) (RS.coeffIn (C.e k) η z) z) :
    RS.pathIntegral γ η =
      ∑ k ∈ Finset.range C.n,
          (g k (C.e k (γ.extend (C.t (k + 1)))) - g k (C.e k (γ.extend (C.t k)))) := by
  obtain ⟨F, hF, hF0⟩ := RS.exists_isPrimitiveAlong γ η
  have hFeq : RS.pathIntegral γ η = F 1 - F 0 := hF.pathIntegral_eq
  -- Per-piece cell primitive and comparison with `F`.
  have hstep : ∀ k, k < C.n →
      F (C.t (k + 1)) - F (C.t k)
        = g k (C.e k (γ.extend (C.t (k + 1)))) - g k (C.e k (γ.extend (C.t k))) := by
    intro k hk
    set Gk : ℝ → ℂ := fun u => g k (C.e k (γ.extend u)) with hGk_def
    have hGprim : RS.IsPrimitiveAlongMap γ.extend η Gk (Set.Icc (C.t k) (C.t (k + 1))) :=
      RS.isPrimitiveAlongMap_of_ball (C.he k) (hg k hk) (fun u hu => C.maps k u hu)
    have hFprim : RS.IsPrimitiveAlongMap γ.extend η F (Set.Icc (C.t k) (C.t (k + 1))) :=
      hF.mono (Set.subset_univ _)
    have hmem0 : C.t k ∈ Set.Icc (C.t k) (C.t (k + 1)) := ⟨le_rfl, C.mono (Nat.le_succ k)⟩
    have hmem1 : C.t (k + 1) ∈ Set.Icc (C.t k) (C.t (k + 1)) := ⟨C.mono (Nat.le_succ k), le_rfl⟩
    have hsub := hFprim.sub_eq_sub (isPreconnected_Icc) γ.continuous_extend.continuousOn
      hGprim hmem0 hmem1
    change F (C.t (k + 1)) - F (C.t k) = Gk (C.t (k + 1)) - Gk (C.t k)
    linear_combination hsub
  -- Telescope `F 1 - F 0` over the chain.
  have htelescope_gen : ∀ n : ℕ,
      F (C.t n) - F (C.t 0) = ∑ k ∈ Finset.range n, (F (C.t (k + 1)) - F (C.t k)) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, ← ih]; ring
  have htelescope : F 1 - F 0 = ∑ k ∈ Finset.range C.n, (F (C.t (k + 1)) - F (C.t k)) := by
    have h1 := htelescope_gen C.n
    rw [C.ht1 C.n le_rfl, C.ht0] at h1
    exact h1
  rw [hFeq, htelescope]
  exact Finset.sum_congr rfl (fun k hk => hstep k (Finset.mem_range.mp hk))

/-! ## §7.3: the Lemma-20.3-specialized residue identity (Stokes-driven) -/

/-- **Forster's Lemma 20.3, specialized to `n = 2`** (the residue identity `abel-theorem` needs
to translate its period-vanishing hypothesis into a statement about a weak solution's chart-local
log-derivative): for the two-puncture kernel `(w - b)⁻¹ - (w - a)⁻¹` (residues `+1` at `b`, `-1`
at `a` — matching a weak solution's own `df/f` local model, §7.3 step 3) and ANY `C¹`
compactly-supported `g` on an open `U`, the area integral of `dbarg` against that kernel recovers
`g b - g a`, with **no local-constancy hypothesis on `g`** (the `abel-weak-solutions` refinement
of `planar-stokes-atoms`' Atom 2 that this unit's design flagged as needed, §7.3/§10/§11 risk R1
— already supplied by `planar-stokes-atoms`' own
`RS.integral_wirtingerDbar_mul_inv_sub_sub_inv_sub_eq`, cited directly here). -/
theorem residue_identity_two_point {a b : ℂ} {U : Set ℂ} {g : ℂ → ℂ}
    (hU : IsOpen U) (hg : ContDiffOn ℝ 1 g U) (hcs : HasCompactSupport g)
    (hsub : tsupport g ⊆ U) :
    (-1 / Real.pi : ℂ) * ∫ w : ℂ, wirtingerDbar g w * ((w - b)⁻¹ - (w - a)⁻¹) = g b - g a := by
  rw [RS.integral_wirtingerDbar_mul_inv_sub_sub_inv_sub_eq hU hg hcs hsub]
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

/-- The two-puncture kernel `(z - b)⁻¹ - (z - a)⁻¹` is EXACTLY the logarithmic derivative
`deriv h z / h z` of the rational function `h z := (z - b) / (z - a)` (the inner-ball formula a
`SingleChart` weak solution literally equals near its zero/pole pair) — connecting §7.3's
abstract kernel to `f`'s own chart-local log-derivative coefficient, as `abel-theorem`'s
translation step needs. -/
theorem logDeriv_rat_eq {a b z : ℂ} (hza : z ≠ a) (hzb : z ≠ b) :
    deriv (fun w : ℂ => (w - b) / (w - a)) z / ((z - b) / (z - a)) = (z - b)⁻¹ - (z - a)⁻¹ := by
  have hderiv : HasDerivAt (fun w : ℂ => (w - b) / (w - a))
      ((1 * (z - a) - (z - b) * 1) / (z - a) ^ 2) z := by
    have := ((hasDerivAt_id z).sub_const b).fun_div ((hasDerivAt_id z).sub_const a)
      (sub_ne_zero.mpr hza)
    simpa using this
  rw [hderiv.deriv]
  have hane : (z - a) ≠ 0 := sub_ne_zero.mpr hza
  have hbne : (z - b) ≠ 0 := sub_ne_zero.mpr hzb
  field_simp

end RS.AbelWeak

end
