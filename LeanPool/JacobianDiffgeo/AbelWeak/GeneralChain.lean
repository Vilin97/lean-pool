/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.AbelWeak.Rechart
import LeanPool.JacobianDiffgeo.AbelWeak.SingleChart
import LeanPool.JacobianDiffgeo.Path.Chain

/-!
# The general multi-chart `exists_weakSolutionOfPair`

Unit: abel-weak-solutions, closing the gap recorded in this unit's own root docstring and in
`docs/design/abel-theorem.md` §1.4/§4.1. Builds the fully general two-point weak solution for an
ARBITRARY connecting path (not confined to one chart), by inducting along a `RS.ChartChain`
and gluing adjacent `SingleChart` pieces via `Rechart.lean`'s `IsWeakSolutionAt.mul`.

## The induction, in one paragraph

Given `δ : Path Q P`, obtain a `ChartChain δ` (`C`) and set `M k := δ.extend (C.t k)` (the
breakpoints, `M 0 = Q`, `M C.n = P`). By induction on `m`, build `f_m` agreeing with the eventual
answer's local model at `M 0` (order `ordAt m (M 0) ∈ {-1, 0}`) and at the CURRENT endpoint `M m`
(order `ordAt m (M m) ∈ {0, 1}`), smooth away from `M 0`, nonvanishing away from `{M 0, M m}`, and
`= 1` outside a compact-closure open set `U_m ∋ M 0`. The step `m → m + 1`: if `M (m+1) = M m` the
piece is degenerate (nothing to do); otherwise get a fresh `SingleChart` weak solution `g` of the
pair `(M (m+1), M m)` inside the chain's own `m`-th chart-ball (shrunk via three nested midpoint
radii so `SingleChart`'s bump-function hypotheses fit inside the chart's target), and glue `f_m`
and `g` via `IsWeakSolutionAt.mul` at every point where either has nonzero order — this is at most
THREE points (`M 0`, `M m`, `M (m+1)`, with the possible coincidences `M 0 = M m` or `M 0 = M
(m+1)` handled by 3 exhaustive cases, `chainFinishSame`/`chainFinish` doing the bookkeeping). At
`m = C.n` the invariant is exactly `IsWeakSolutionOfPair f P Q`; `Q ∈ U` is tracked throughout
(seeded by a small chart-ball `B0 ∋ M 0` at the base case) and `P ∈ U` follows by contradiction
(a weak solution of nonzero order genuinely vanishes at its own point, contradicting the `= 1`
off-`U` value if `P ∉ U`).
-/

open scoped ContDiff Manifold
open IsManifold Metric Set Filter Topology

noncomputable section

namespace RS.AbelWeak

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ## Small helpers -/

omit [T2Space X] [IsManifold 𝓘(ℂ) ω X] in
/-- `IsWeakSolutionAt` transports along eventual equality of the underlying function. -/
theorem IsWeakSolutionAt.congr_of_eventuallyEq {f g : X → ℂ} {a : X} {k : ℤ}
    (hf : IsWeakSolutionAt f a k) (hfg : f =ᶠ[𝓝 a] g) : IsWeakSolutionAt g a k := by
  obtain ⟨e, he, ha, ψ, hψne, hψdiff, hfeq⟩ := hf
  exact ⟨e, he, ha, ψ, hψne, hψdiff, hfg.symm.trans hfeq⟩

omit [T2Space X] [IsManifold 𝓘(ℂ) ω X] in
/-- A weak solution of NONZERO order genuinely vanishes at its own point (a pole is assigned the
junk value `0` there too, by the `zpow`-at-zero convention; a zero vanishes for real). -/
theorem IsWeakSolutionAt.apply_eq_zero_of_ne_zero {f : X → ℂ} {a : X} {k : ℤ}
    (hf : IsWeakSolutionAt f a k) (hk : k ≠ 0) : f a = 0 := by
  obtain ⟨e, he, ha, ψ, hψne, hψdiff, hfeq⟩ := hf
  have h1 : f a = ψ (e a) * (e a - e a) ^ k := hfeq.self_of_nhds
  rwa [sub_self, zero_zpow k hk, mul_zero] at h1

omit [T2Space X] in
/-- The constant function `1` is (trivially) a weak solution of order `0` at any point. -/
theorem isWeakSolutionAt_one_zero (a : X) : IsWeakSolutionAt (fun _ : X => (1 : ℂ)) a 0 := by
  refine ⟨chartAt ℂ a, IsManifold.chart_mem_maximalAtlas a, mem_chart_source ℂ a,
    fun _ => 1, ?_, contDiffAt_const, ?_⟩
  · exact Filter.Eventually.of_forall fun _ => one_ne_zero
  · exact Filter.Eventually.of_forall fun _ => by simp

/-- A function that is `ContMDiffOn` away from `p` and nonvanishing away from `{p, q}` is,
at any OTHER point `x ∉ {p, q}`, a weak solution of order `0` (smooth, nonvanishing — no genuine
zero or pole there). -/
theorem isWeakSolutionAt_zero_of_ne {f : X → ℂ} {p q x : X}
    (hcm : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f {p}ᶜ) (hne : ∀ y, y ≠ p → y ≠ q → f y ≠ 0)
    (hxp : x ≠ p) (hxq : x ≠ q) : IsWeakSolutionAt f x 0 := by
  have hcm' : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f x :=
      hcm.contMDiffAt (isOpen_compl_singleton.mem_nhds hxp)
  have hfx : f x ≠ 0 := hne x hxp hxq
  have hxmem : chartAt ℂ x ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X := IsManifold.chart_mem_maximalAtlas x
  refine ⟨chartAt ℂ x, hxmem, mem_chart_source ℂ x,
    fun z => f ((chartAt ℂ x).symm z), ?_, ?_, ?_⟩
  · have h1 : ContinuousAt (⇑(chartAt ℂ x).symm) (chartAt ℂ x x) :=
      (contMDiffAt_symm_of_mem_maximalAtlas hxmem
        ((chartAt ℂ x).map_source (mem_chart_source ℂ x))).continuousAt
    have h2 : ContinuousAt f ((chartAt ℂ x).symm (chartAt ℂ x x)) := by
      rw [(chartAt ℂ x).left_inv (mem_chart_source ℂ x)]; exact hcm'.continuousAt
    have h3 : ContinuousAt (fun z => f ((chartAt ℂ x).symm z)) (chartAt ℂ x x) := h2.comp h1
    have h4 : f ((chartAt ℂ x).symm (chartAt ℂ x x)) ≠ 0 := by
      rw [(chartAt ℂ x).left_inv (mem_chart_source ℂ x)]; exact hfx
    exact h3.eventually_ne h4
  · exact contDiffAt_comp_symm_of_contMDiffAt hxmem
      (mem_chart_source ℂ x) hcm'
  · filter_upwards [(chartAt ℂ x).open_source.mem_nhds (mem_chart_source ℂ x)] with y hy
    rw [(chartAt ℂ x).left_inv hy, zpow_zero, mul_one]

omit [T2Space X] [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- Converse of `isWeakSolutionAt_zero_of_ne`'s conclusion: order `0` at `a` unfolds to genuine
smoothness and nonvanishing there. -/
theorem IsWeakSolutionAt.contMDiffAt_and_ne_zero_of_zero {f : X → ℂ} {a : X}
    (hf : IsWeakSolutionAt f a 0) :
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f a ∧ f a ≠ 0 := by
  obtain ⟨e, he, ha, ψ, hψne, hψdiff, hfeq⟩ := hf
  have heq : f =ᶠ[𝓝 a] fun x => ψ (e x) := by
    filter_upwards [hfeq] with x hx; rw [hx, zpow_zero, mul_one]
  have hcm : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (fun x => ψ (e x)) a :=
    contMDiffAt_comp_of_contDiffAt he ha hψdiff
  have hfa : f a = ψ (e a) := heq.self_of_nhds
  exact ⟨hcm.congr_of_eventuallyEq heq, hfa ▸ hψne.self_of_nhds⟩

omit [T2Space X] in
/-- Two-factor product bridge (Compat, mirroring `contMDiffAt_finsetProd_real`: no
`ContMDiffMul 𝓘(ℝ, ℂ) ∞ ℂ` instance is registered, so this routes through `ContDiffAt ℝ` in the
chart `extChartAt 𝓘(ℂ) x`). -/
private theorem contMDiffAt_mul_real {f g : X → ℂ} {x : X}
    (hf : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f x) (hg : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ g x) :
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (fun y => f y * g y) x := by
  rw [RS.contMDiffAt_real_iff_contDiffAt] at hf hg ⊢
  exact hf.mul hg

omit [T2Space X] in
/-- A nonnegative order (`k ≥ 0`, i.e. a genuine zero, `k > 0`, or the order-`0` case) unfolds to
genuine smoothness (no `≠ 0` conclusion — a zero really does vanish there). -/
theorem IsWeakSolutionAt.contMDiffAt_of_nonneg {f : X → ℂ} {a : X} {k : ℤ}
    (hf : IsWeakSolutionAt f a k) (hk : 0 ≤ k) : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f a := by
  obtain ⟨e, he, ha, ψ, hψne, hψdiff, hfeq⟩ := hf
  lift k to ℕ using hk with n
  have heq : f =ᶠ[𝓝 a] fun x => ψ (e x) * (e x - e a) ^ n := by
    filter_upwards [hfeq] with x hx; rw [hx, zpow_natCast]
  have hecm : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (⇑e) a :=
    RS.contMDiffAt_real_of_holomorphicAt (contMDiffAt_of_mem_maximalAtlas he ha)
  have hesub : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (fun x => e x - e a) a := hecm.sub contMDiffAt_const
  have hepow : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (fun x => (e x - e a) ^ n) a := by
    have hprod := contMDiffAt_finsetProd_real (ι := Fin n) (t := Finset.univ)
      (f := fun _ : Fin n => fun x => e x - e a) (fun i _ => hesub)
    simpa using hprod
  have hψe : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (fun x => ψ (e x)) a :=
    contMDiffAt_comp_of_contDiffAt he ha hψdiff
  exact (contMDiffAt_mul_real hψe hepow).congr_of_eventuallyEq heq

/-- The shared "finish" step of the chain induction: given the invariant data at level `m`
(base `f`, exclusion point `p`, current endpoint `q`) and a fresh `SingleChart` piece's raw data
(`g`, exclusion point `q`, new endpoint `r`), TOGETHER WITH the already-assembled merged function
`h` (agreeing with `f * g` off `{p, q, r}`, with tracked facts at `p`, `q` (order `0`), and `r`),
produce the invariant data at level `m + 1` (exclusion point still `p`, new current endpoint `r`).
-/
private theorem chainFinish {f g h : X → ℂ} {p q r : X} {U V : Set X} {k0 k1 : ℤ}
    (hUopen : IsOpen U) (hUcompact : IsCompact (closure U)) (hpU : p ∈ U)
    (hoff : ∀ x ∉ U, x ≠ p → f x = 1)
    (hcm : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f {p}ᶜ)
    (hne : ∀ x, x ≠ p → x ≠ q → f x ≠ 0)
    (hVopen : IsOpen V) (hVcompact : IsCompact (closure V))
    (hqV : q ∈ V) (hrV : r ∈ V) (hg1 : ∀ x ∉ V, g x = 1)
    (hgcm : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ g {q}ᶜ) (hgne : ∀ x, x ≠ r → x ≠ q → g x ≠ 0)
    (hh0 : IsWeakSolutionAt h p k0) (hh1 : IsWeakSolutionAt h r k1)
    (hhq : IsWeakSolutionAt h q 0) (hk1 : 0 ≤ k1)
    (hheq : ∀ x, x ≠ p → x ≠ q → x ≠ r → h x = f x * g x) :
    ∃ (f' : X → ℂ) (U' : Set X), IsOpen U' ∧ IsCompact (closure U') ∧ p ∈ U' ∧ r ∈ U' ∧
      (∀ x ∉ U', x ≠ p → f' x = 1) ∧
      ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f' {p}ᶜ ∧
      (∀ x, x ≠ p → x ≠ r → f' x ≠ 0) ∧
      IsWeakSolutionAt f' p k0 ∧ IsWeakSolutionAt f' r k1 := by
  refine ⟨h, U ∪ V, hUopen.union hVopen, ?_, Or.inl hpU, Or.inr hrV, ?_, ?_, ?_, hh0, hh1⟩
  · rw [closure_union]; exact hUcompact.union hVcompact
  · intro x hx hxp
    have hxU : x ∉ U := fun hu => hx (Or.inl hu)
    have hxV : x ∉ V := fun hv => hx (Or.inr hv)
    have hxq : x ≠ q := fun heqx => hxV (heqx ▸ hqV)
    have hxr : x ≠ r := fun heqx => hxV (heqx ▸ hrV)
    rw [hheq x hxp hxq hxr, hoff x hxU hxp, hg1 x hxV]; ring
  · intro x hxp
    by_cases hxq : x = q
    · rw [hxq]; exact hhq.contMDiffAt_and_ne_zero_of_zero.1.contMDiffWithinAt
    · by_cases hxr : x = r
      · rw [hxr]; exact (hh1.contMDiffAt_of_nonneg hk1).contMDiffWithinAt
      · have heqx : h =ᶠ[𝓝 x] (fun y => f y * g y) := by
          filter_upwards [isOpen_compl_singleton.mem_nhds hxp,
            isOpen_compl_singleton.mem_nhds hxq, isOpen_compl_singleton.mem_nhds hxr]
            with y hyp hyq hyr
          exact hheq y hyp hyq hyr
        have hfcm : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f x :=
          hcm.contMDiffAt (isOpen_compl_singleton.mem_nhds hxp)
        have hgcm' : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ g x :=
          hgcm.contMDiffAt (isOpen_compl_singleton.mem_nhds hxq)
        exact ((contMDiffAt_mul_real hfcm hgcm').congr_of_eventuallyEq heqx).contMDiffWithinAt
  · intro x hxp hxr
    by_cases hxq : x = q
    · rw [hxq]; exact hhq.contMDiffAt_and_ne_zero_of_zero.2
    · rw [hheq x hxp hxq hxr]
      exact mul_ne_zero (hne x hxp hxq) (hgne x hxr hxq)

/-- Variant of `chainFinish` for the case `q = p` (the OLD current endpoint coincides with the
chain's basepoint): only TWO points (`p`, `r`) need tracking, no separate order-`0` fact at `q`
is needed (it never arises: `x ≠ p` already excludes `x = q`). -/
private theorem chainFinishSame {f g h : X → ℂ} {p r : X} {U V : Set X} {k0 k1 : ℤ}
    (hUopen : IsOpen U) (hUcompact : IsCompact (closure U))
    (hoff : ∀ x ∉ U, x ≠ p → f x = 1)
    (hcm : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f {p}ᶜ)
    (hne : ∀ x, x ≠ p → f x ≠ 0)
    (hVopen : IsOpen V) (hVcompact : IsCompact (closure V))
    (hpV : p ∈ V) (hrV : r ∈ V) (hg1 : ∀ x ∉ V, g x = 1)
    (hgcm : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ g {p}ᶜ) (hgne : ∀ x, x ≠ r → x ≠ p → g x ≠ 0)
    (hh0 : IsWeakSolutionAt h p k0) (hh1 : IsWeakSolutionAt h r k1) (hk1 : 0 ≤ k1)
    (hheq : ∀ x, x ≠ p → x ≠ r → h x = f x * g x) :
    ∃ (f' : X → ℂ) (U' : Set X), IsOpen U' ∧ IsCompact (closure U') ∧ p ∈ U' ∧ r ∈ U' ∧
      (∀ x ∉ U', x ≠ p → f' x = 1) ∧
      ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f' {p}ᶜ ∧
      (∀ x, x ≠ p → x ≠ r → f' x ≠ 0) ∧
      IsWeakSolutionAt f' p k0 ∧ IsWeakSolutionAt f' r k1 := by
  refine ⟨h, U ∪ V, hUopen.union hVopen, ?_, Or.inr hpV, Or.inr hrV, ?_, ?_, ?_, hh0, hh1⟩
  · rw [closure_union]; exact hUcompact.union hVcompact
  · intro x hx hxp
    have hxU : x ∉ U := fun hu => hx (Or.inl hu)
    have hxV : x ∉ V := fun hv => hx (Or.inr hv)
    have hxr : x ≠ r := fun heqx => hxV (heqx ▸ hrV)
    rw [hheq x hxp hxr, hoff x hxU hxp, hg1 x hxV]; ring
  · intro x hxp
    by_cases hxr : x = r
    · rw [hxr]; exact (hh1.contMDiffAt_of_nonneg hk1).contMDiffWithinAt
    · have heqx : h =ᶠ[𝓝 x] (fun y => f y * g y) := by
        filter_upwards [isOpen_compl_singleton.mem_nhds hxp,
          isOpen_compl_singleton.mem_nhds hxr] with y hyp hyr
        exact hheq y hyp hyr
      have hfcm : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f x :=
        hcm.contMDiffAt (isOpen_compl_singleton.mem_nhds hxp)
      have hgcm' : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ g x :=
        hgcm.contMDiffAt (isOpen_compl_singleton.mem_nhds hxp)
      exact ((contMDiffAt_mul_real hfcm hgcm').congr_of_eventuallyEq heqx).contMDiffWithinAt
  · intro x hxp hxr
    rw [hheq x hxp hxr]
    exact mul_ne_zero (hne x hxp) (hgne x hxr hxp)

/-! ## The general chain induction -/

omit [IsManifold 𝓘(ℂ) ω X] in
/-- Merge two independently-repaired functions (each a `Function.update` of a COMMON base `f₀` at
its own point) into one, at two DISTINCT points `y₁ ≠ y₂`. -/
private theorem merge_two {f₀ h₁ h₂ : X → ℂ} {y₁ y₂ : X} {k₁ k₂ : ℤ} (hy : y₁ ≠ y₂)
    (hh1_ord : IsWeakSolutionAt h₁ y₁ k₁) (hh1_eq : ∀ x, x ≠ y₁ → h₁ x = f₀ x)
    (hh2_ord : IsWeakSolutionAt h₂ y₂ k₂) (hh2_eq : ∀ x, x ≠ y₂ → h₂ x = f₀ x) :
    ∃ h : X → ℂ, IsWeakSolutionAt h y₁ k₁ ∧ IsWeakSolutionAt h y₂ k₂ ∧
      ∀ x, x ≠ y₁ → x ≠ y₂ → h x = f₀ x := by
  classical
  refine ⟨Function.update h₁ y₂ (h₂ y₂), ?_, ?_, ?_⟩
  · apply hh1_ord.congr_of_eventuallyEq
    filter_upwards [isOpen_compl_singleton.mem_nhds hy] with x hx
    exact (Function.update_of_ne hx _ _).symm
  · apply hh2_ord.congr_of_eventuallyEq
    filter_upwards [isOpen_compl_singleton.mem_nhds hy.symm] with x hx1
    rcases eq_or_ne x y₂ with rfl | hxne2
    · rw [Function.update_self]
    · rw [Function.update_of_ne hxne2, hh1_eq x hx1, hh2_eq x hxne2]
  · intro x hx1 hx2
    rw [Function.update_of_ne hx2, hh1_eq x hx1]

omit [IsManifold 𝓘(ℂ) ω X] in
/-- Merge-three variant: `h₁` already carries facts at TWO distinct points `y₁ ≠ y₂` (agreeing
with the base `f₀` off both), `h₂` carries a fresh fact at a THIRD point `y₃` distinct from both. -/
private theorem merge_two' {f₀ h₁ h₂ : X → ℂ} {y₁ y₂ y₃ : X} {k₁ k₂ k₃ : ℤ}
    (hy13 : y₁ ≠ y₃) (hy23 : y₂ ≠ y₃)
    (hh1_ord1 : IsWeakSolutionAt h₁ y₁ k₁) (hh1_ord2 : IsWeakSolutionAt h₁ y₂ k₂)
    (hh1_eq : ∀ x, x ≠ y₁ → x ≠ y₂ → h₁ x = f₀ x)
    (hh2_ord : IsWeakSolutionAt h₂ y₃ k₃) (hh2_eq : ∀ x, x ≠ y₃ → h₂ x = f₀ x) :
    ∃ h : X → ℂ, IsWeakSolutionAt h y₁ k₁ ∧ IsWeakSolutionAt h y₂ k₂ ∧ IsWeakSolutionAt h y₃ k₃ ∧
      ∀ x, x ≠ y₁ → x ≠ y₂ → x ≠ y₃ → h x = f₀ x := by
  classical
  refine ⟨Function.update h₁ y₃ (h₂ y₃), ?_, ?_, ?_, ?_⟩
  · apply hh1_ord1.congr_of_eventuallyEq
    filter_upwards [isOpen_compl_singleton.mem_nhds hy13] with x hx
    exact (Function.update_of_ne hx _ _).symm
  · apply hh1_ord2.congr_of_eventuallyEq
    filter_upwards [isOpen_compl_singleton.mem_nhds hy23] with x hx
    exact (Function.update_of_ne hx _ _).symm
  · apply hh2_ord.congr_of_eventuallyEq
    filter_upwards [isOpen_compl_singleton.mem_nhds hy13.symm,
      isOpen_compl_singleton.mem_nhds hy23.symm] with x hx1 hx2
    rcases eq_or_ne x y₃ with rfl | hxne3
    · rw [Function.update_self]
    · rw [Function.update_of_ne hxne3, hh1_eq x hx1 hx2, hh2_eq x hxne3]
  · intro x hx1 hx2 hx3
    rw [Function.update_of_ne hx3, hh1_eq x hx1 hx2]

open scoped Classical in
/-- The chain induction behind `exists_weakSolutionOfPair`: a weak solution along the first `m`
steps of the chart chain, with the endpoint orders prescribed. Split out to keep that proof under
the 200-line size we hold ourselves to; the `M`/`ordAt` abbreviations are rebuilt here so the
argument reads exactly as it did inline. -/
private theorem exists_weakSolution_chain_step {P Q : X} {δ : Path Q P} (C : ChartChain δ)
    (B0 : Set X) (hB0open : IsOpen B0) (hB0compact : IsCompact (closure B0))
    (hB0mem : δ.extend (C.t 0) ∈ B0) :
    ∀ m ≤ C.n, ∃ (f : X → ℂ) (U : Set X), IsOpen U ∧ IsCompact (closure U) ∧
    δ.extend (C.t 0) ∈ U ∧
    (∀ x ∉ U, x ≠ δ.extend (C.t 0) → f x = 1) ∧
    ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f {δ.extend (C.t 0)}ᶜ ∧
    (∀ x, x ≠ δ.extend (C.t 0) → x ≠ δ.extend (C.t m) → f x ≠ 0) ∧
    IsWeakSolutionAt f (δ.extend (C.t 0))
        ((if δ.extend (C.t 0) = δ.extend (C.t 0) then (-1 : ℤ) else 0) +
          (if δ.extend (C.t 0) = δ.extend (C.t m) then (1 : ℤ) else 0)) ∧
      IsWeakSolutionAt f (δ.extend (C.t m))
        ((if δ.extend (C.t m) = δ.extend (C.t 0) then (-1 : ℤ) else 0) +
          (if δ.extend (C.t m) = δ.extend (C.t m) then (1 : ℤ) else 0)) := by
  set M : ℕ → X := fun k => δ.extend (C.t k) with hM_def
  set ordAt : ℕ → X → ℤ :=
    fun m x => (if x = M 0 then (-1 : ℤ) else 0) + (if x = M m then (1 : ℤ) else 0)
    with hordAt_def
  change ∀ m ≤ C.n, ∃ (f : X → ℂ) (U : Set X), IsOpen U ∧ IsCompact (closure U) ∧
    M 0 ∈ U ∧
    (∀ x ∉ U, x ≠ M 0 → f x = 1) ∧
    ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f {M 0}ᶜ ∧
    (∀ x, x ≠ M 0 → x ≠ M m → f x ≠ 0) ∧
    IsWeakSolutionAt f (M 0) (ordAt m (M 0)) ∧ IsWeakSolutionAt f (M m) (ordAt m (M m))
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨fun _ => 1, B0, hB0open, hB0compact, hB0mem, ?_, ?_, ?_, ?_, ?_⟩
    · intro x _ _; rfl
    · exact fun x _ => contMDiffAt_const.contMDiffWithinAt
    · intro x _ _; exact one_ne_zero
    · have hval : ordAt 0 (M 0) = 0 := by simp [hordAt_def]
      rw [hval]; exact isWeakSolutionAt_one_zero (M 0)
    · have hval : ordAt 0 (M 0) = 0 := by simp [hordAt_def]
      rw [hval]; exact isWeakSolutionAt_one_zero (M 0)
  | succ m ih =>
    intro hm1
    obtain ⟨f, U, hUopen, hUcompact, hM0U, hoff, hcm, hne, hwp0, hwpm⟩ :=
      ih (Nat.le_of_succ_le hm1)
    by_cases hdeg : M (m + 1) = M m
    · have heq0 : ordAt (m + 1) (M 0) = ordAt m (M 0) := by
        simp only [hordAt_def]; rw [hdeg]
      have heqm : ordAt (m + 1) (M (m + 1)) = ordAt m (M m) := by
        simp only [hordAt_def]; rw [hdeg]
      refine ⟨f, U, hUopen, hUcompact, hM0U, ?_, hcm, ?_, ?_, ?_⟩
      · intro x hx1 hx2; exact hoff x hx1 hx2
      · rw [hdeg]; exact hne
      · rw [heq0]; exact hwp0
      · rw [heqm, hdeg]; exact hwpm
    · -- genuine new piece: `M m ≠ M (m + 1)`.
      rename' hdeg => hdeg'
      have hdeg : M (m + 1) ≠ M m := hdeg'
      have hicc1 : C.t m ∈ Set.Icc (C.t m) (C.t (m + 1)) := ⟨le_rfl, C.mono (Nat.le_succ m)⟩
      have hicc2 : C.t (m + 1) ∈ Set.Icc (C.t m) (C.t (m + 1)) :=
        ⟨C.mono (Nat.le_succ m), le_rfl⟩
      have hL := C.maps m (C.t m) hicc1
      have hR := C.maps m (C.t (m + 1)) hicc2
      have hQs : M m ∈ (C.e m).source := hL.1
      have hPs : M (m + 1) ∈ (C.e m).source := hR.1
      have hQball : C.e m (M m) ∈ Metric.ball (C.c m) (C.r m) := hL.2
      have hPball : C.e m (M (m + 1)) ∈ Metric.ball (C.c m) (C.r m) := hR.2
      have hr0 : 0 < C.r m := C.hr m
      have hdQ : dist (C.e m (M m)) (C.c m) < C.r m := hQball
      have hdP : dist (C.e m (M (m + 1))) (C.c m) < C.r m := hPball
      set ρ : ℝ := (max (dist (C.e m (M m)) (C.c m)) (dist (C.e m (M (m + 1))) (C.c m))
        + C.r m) / 2 with hρ_def
      set rIn : ℝ := (ρ + C.r m) / 2 with hrIn_def
      set rOut : ℝ := (rIn + C.r m) / 2 with hrOut_def
      have hρpos : 0 < ρ := by
        have := le_max_left (dist (C.e m (M m)) (C.c m)) (dist (C.e m (M (m+1))) (C.c m))
        have h2 : (0:ℝ) ≤ dist (C.e m (M m)) (C.c m) := dist_nonneg
        rw [hρ_def]; linarith
      have hρlt : ρ < C.r m := by
        rw [hρ_def]
        rcases le_total (dist (C.e m (M m)) (C.c m)) (dist (C.e m (M (m+1))) (C.c m)) with h|h
        · rw [max_eq_right h]; linarith
        · rw [max_eq_left h]; linarith
      have hrInlt : ρ < rIn := by rw [hrIn_def]; linarith
      have hrOutlt : rIn < rOut := by rw [hrOut_def]; linarith
      have hrOutR : rOut < C.r m := by rw [hrOut_def]; linarith
      have haQ : C.e m (M m) - C.c m ∈ Metric.ball (0 : ℂ) ρ := by
        rw [Metric.mem_ball, dist_zero_right]
        rw [dist_eq_norm] at hdQ
        calc ‖C.e m (M m) - C.c m‖ ≤ max (dist (C.e m (M m)) (C.c m))
              (dist (C.e m (M (m+1))) (C.c m)) := by
                rw [← dist_eq_norm]; exact le_max_left _ _
          _ < ρ := by rw [hρ_def]; linarith
      have haP : C.e m (M (m + 1)) - C.c m ∈ Metric.ball (0 : ℂ) ρ := by
        rw [Metric.mem_ball, dist_zero_right]
        rw [dist_eq_norm] at hdP
        calc ‖C.e m (M (m + 1)) - C.c m‖ ≤ max (dist (C.e m (M m)) (C.c m))
              (dist (C.e m (M (m+1))) (C.c m)) := by
                rw [← dist_eq_norm]; exact le_max_right _ _
          _ < ρ := by rw [hρ_def]; linarith
      set ψ : ContDiffBump (0 : ℂ) := ⟨rIn, rOut, by linarith, hrOutlt⟩ with hψ_def
      have hballsub : Metric.closedBall (C.c m) ψ.rOut ⊆ (C.e m).target := by
        have h1 : Metric.closedBall (C.c m) rOut ⊆ Metric.ball (C.c m) (C.r m) :=
          Metric.closedBall_subset_ball hrOutR
        exact h1.trans (C.ball_subset m)
      obtain ⟨g, hg, hUgopen, hUgcompact, hM1Ug, hMUg, hg1⟩ :=
        exists_weakSolutionOfPair_chart hdeg (C.he m) hPs hQs hρpos haQ haP ψ hrInlt hballsub
      -- `f`'s and `g`'s local model at ANY point (not just their own special ones).
      have hfAt : ∀ y, IsWeakSolutionAt f y (ordAt m y) := by
        intro y
        by_cases hy0 : y = M 0
        · rw [hy0]; exact hwp0
        · by_cases hym : y = M m
          · rw [hym]; exact hwpm
          · have hzero : ordAt m y = 0 := by
              simp only [hordAt_def]; rw [if_neg hy0, if_neg hym]; ring
            rw [hzero]; exact isWeakSolutionAt_zero_of_ne hcm hne hy0 hym
      have hgAt : ∀ y, IsWeakSolutionAt g y
          ((if y = M (m + 1) then (1 : ℤ) else 0) + (if y = M m then (-1 : ℤ) else 0)) := by
        intro y
        by_cases hy1 : y = M (m + 1)
        · have hval : (if y = M (m + 1) then (1 : ℤ) else 0) + (if y = M m then (-1 : ℤ) else 0)
              = 1 := by
            rw [if_pos hy1, if_neg (hy1 ▸ hdeg : y ≠ M m)]; ring
          rw [hval, hy1]; exact hg.weakAt_P
        · by_cases hym : y = M m
          · have hval : (if y = M (m + 1) then (1 : ℤ) else 0)
                + (if y = M m then (-1 : ℤ) else 0) = -1 := by
              rw [if_neg hy1, if_pos hym]; ring
            rw [hval, hym]; exact hg.weakAt_Q
          · have hval : (if y = M (m + 1) then (1 : ℤ) else 0)
                + (if y = M m then (-1 : ℤ) else 0) = 0 := by
              rw [if_neg hy1, if_neg hym]; ring
            rw [hval]
            exact isWeakSolutionAt_zero_of_ne hg.contMDiffOn
              (fun z h1 h2 => hg.ne_zero_off z h2 h1) hym hy1
      have hsum : ∀ y, ordAt m y +
          ((if y = M (m + 1) then (1 : ℤ) else 0) + (if y = M m then (-1 : ℤ) else 0))
            = ordAt (m + 1) y := by
        intro y
        simp only [hordAt_def]
        have hcancel : (if y = M m then (1 : ℤ) else 0) + (if y = M m then (-1 : ℤ) else 0)
            = 0 := by by_cases h : y = M m <;> simp [h]
        linarith [hcancel]
      obtain ⟨hMm, hMm_ord0, hMm_eq0⟩ := (hfAt (M m)).mul (hgAt (M m))
      obtain ⟨hMm1, hMm1_ord0, hMm1_eq0⟩ := (hfAt (M (m + 1))).mul (hgAt (M (m + 1)))
      have hMm_ord : IsWeakSolutionAt hMm (M m) (ordAt (m + 1) (M m)) := hsum (M m) ▸ hMm_ord0
      have hMm1_ord : IsWeakSolutionAt hMm1 (M (m + 1)) (ordAt (m + 1) (M (m + 1))) :=
        hsum (M (m + 1)) ▸ hMm1_ord0
      have hk1 : 0 ≤ ordAt (m + 1) (M (m + 1)) := by
        simp only [hordAt_def]; split_ifs <;> omega
      have hgne' : ∀ x, x ≠ M (m + 1) → x ≠ M m → g x ≠ 0 :=
        fun x h1 h2 => hg.ne_zero_off x h1 h2
      by_cases hM0m : M 0 = M m
      · -- Case (ii): `M 0 = M m ≠ M (m + 1)`.
        have hne1 : M 0 ≠ M (m + 1) := by rw [hM0m]; exact hdeg.symm
        have hh0 : IsWeakSolutionAt hMm (M 0) (ordAt (m + 1) (M 0)) := by
          rw [hM0m]; exact hMm_ord
        have hh0_eq : ∀ x, x ≠ M 0 → hMm x = f x * g x := fun x hx =>
          hMm_eq0 x (by rw [← hM0m]; exact hx)
        obtain ⟨h, hh_ordA, hh_ordB, hh_eq⟩ := merge_two hne1 hh0 hh0_eq hMm1_ord hMm1_eq0
        have hMUg' : M 0 ∈ ↑(C.e m).symm '' Metric.ball (C.c m) ψ.rOut := by
          rw [hM0m]; exact hMUg
        have hne'' : ∀ x, x ≠ M 0 → f x ≠ 0 := fun x hx => hne x hx (by rw [← hM0m]; exact hx)
        have hgcm'' : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ g {M 0}ᶜ := by rw [hM0m]; exact hg.contMDiffOn
        have hgne'' : ∀ x, x ≠ M (m + 1) → x ≠ M 0 → g x ≠ 0 :=
          fun x h1 h2 => hg.ne_zero_off x h1 (by rw [← hM0m]; exact h2)
        obtain ⟨f', U', h1o, h2o, h3o, h4o, h5o, h6o, h7o, h8o, h9o⟩ :=
          chainFinishSame hUopen hUcompact hoff hcm hne'' hUgopen hUgcompact hMUg' hM1Ug hg1
            hgcm'' hgne'' hh_ordA hh_ordB hk1 (fun x hxp hxr => hh_eq x hxp hxr)
        exact ⟨f', U', h1o, h2o, h3o, h5o, h6o, h7o, h8o, h9o⟩
      · have hMmzero : ordAt (m + 1) (M m) = 0 := by
          simp only [hordAt_def]; rw [if_neg (Ne.symm hM0m), if_neg hdeg.symm]; ring
        by_cases hM01 : M 0 = M (m + 1)
        · -- Case (iii): `M 0 = M (m + 1) ≠ M m`.
          have hne2 : M m ≠ M 0 := by rw [hM01]; exact hdeg.symm
          have hh1 : IsWeakSolutionAt hMm1 (M 0) (ordAt (m + 1) (M 0)) := by
            rw [hM01]; exact hMm1_ord
          have hh1_eq : ∀ x, x ≠ M 0 → hMm1 x = f x * g x := fun x hx =>
            hMm1_eq0 x (by rw [← hM01]; exact hx)
          obtain ⟨h, hh_ordA, hh_ordB, hh_eq⟩ := merge_two hne2 hMm_ord hMm_eq0 hh1 hh1_eq
          have hh_ordA0 : IsWeakSolutionAt h (M m) 0 := hMmzero ▸ hh_ordA
          have hh_ordB' : IsWeakSolutionAt h (M (m + 1)) (ordAt (m + 1) (M (m + 1))) := by
            rw [← hM01]; exact hh_ordB
          obtain ⟨f', U', h1o, h2o, h3o, h4o, h5o, h6o, h7o, h8o, h9o⟩ :=
            chainFinish hUopen hUcompact hM0U hoff hcm hne hUgopen hUgcompact hMUg hM1Ug hg1
              hg.contMDiffOn hgne' hh_ordB hh_ordB' hh_ordA0 hk1 (fun x hxp hxq hxr =>
                hh_eq x hxq hxp)
          exact ⟨f', U', h1o, h2o, h3o, h5o, h6o, h7o, h8o, h9o⟩
        · -- Case (i): three genuinely distinct points.
          obtain ⟨h0, h0_ord0, h0_eq0⟩ := (hfAt (M 0)).mul (hgAt (M 0))
          have h0_ord : IsWeakSolutionAt h0 (M 0) (ordAt (m + 1) (M 0)) := hsum (M 0) ▸ h0_ord0
          obtain ⟨h12, hh12_ordA, hh12_ordB, hh12_eq⟩ :=
            merge_two hdeg.symm hMm_ord hMm_eq0 hMm1_ord hMm1_eq0
          obtain ⟨h, hh_ordA, hh_ordB, hh_ordC, hh_eq⟩ :=
            merge_two' (Ne.symm hM0m) (Ne.symm hM01) hh12_ordA hh12_ordB hh12_eq h0_ord h0_eq0
          have hh_ordA0 : IsWeakSolutionAt h (M m) 0 := hMmzero ▸ hh_ordA
          obtain ⟨f', U', h1o, h2o, h3o, h4o, h5o, h6o, h7o, h8o, h9o⟩ :=
            chainFinish hUopen hUcompact hM0U hoff hcm hne hUgopen hUgcompact hMUg hM1Ug hg1
              hg.contMDiffOn hgne' hh_ordC hh_ordB hh_ordA0 hk1 (fun x hxp hxq hxr =>
                hh_eq x hxq hxr hxp)
          exact ⟨f', U', h1o, h2o, h3o, h5o, h6o, h7o, h8o, h9o⟩

/-- **The general multi-chart weak solution** (§6.3/§7.1 of `abel-weak-solutions.md`, the gap
this file closes): for an ARBITRARY path `δ : Path Q P` (not confined to one chart), there is a
weak solution of the pair `(P, Q)`. Built by inducting along a `RS.ChartChain δ`
(`Jacobian.Path.Chain`), gluing one `SingleChart` piece per chain link via `IsWeakSolutionAt.mul`
(`Rechart.lean`) — the `+1`-order zero of one piece cancels the `-1`-order pole of the next at
every interior breakpoint, including the (rare, but real) case where the breakpoint recurs at the
chain's own basepoint `Q`. -/
theorem exists_weakSolutionOfPair {P Q : X} (hPQ : Q ≠ P) (δ : Path Q P) :
    ∃ (f : X → ℂ) (U : Set X), IsWeakSolutionOfPair f P Q ∧
      IsOpen U ∧ IsCompact (closure U) ∧ P ∈ U ∧ Q ∈ U ∧ (∀ x ∉ U, f x = 1) := by
  classical
  obtain ⟨C⟩ := RS.exists_chartChain δ
  set M : ℕ → X := fun k => δ.extend (C.t k) with hM_def
  have hM0 : M 0 = Q := by rw [hM_def]; simp only; rw [C.ht0, δ.extend_zero]
  have hMn : M C.n = P := by rw [hM_def]; simp only; rw [C.ht1 C.n le_rfl, δ.extend_one]
  set ordAt : ℕ → X → ℤ :=
    fun m x => (if x = M 0 then (-1 : ℤ) else 0) + (if x = M m then (1 : ℤ) else 0)
    with hordAt_def
  -- A fixed small chart-ball neighbourhood of `M 0`, seeding `U` so `M 0 ∈ U` throughout.
  obtain ⟨r0, hr0pos, hr0sub⟩ := Metric.isOpen_iff.mp (chartAt ℂ (M 0)).open_target
    (chartAt ℂ (M 0) (M 0)) (mem_chart_target ℂ (M 0))
  set B0 : Set X := (chartAt ℂ (M 0)).symm '' Metric.ball (chartAt ℂ (M 0) (M 0)) (r0 / 2)
    with hB0_def
  have hr0halflt : r0 / 2 < r0 := by linarith
  have hballsub0 : Metric.ball (chartAt ℂ (M 0) (M 0)) (r0 / 2) ⊆ (chartAt ℂ (M 0)).target :=
    (Metric.ball_subset_ball hr0halflt.le).trans hr0sub
  have hB0open : IsOpen B0 :=
    (chartAt ℂ (M 0)).symm.isOpen_image_of_subset_source Metric.isOpen_ball hballsub0
  have hcballsub0 : Metric.closedBall (chartAt ℂ (M 0) (M 0)) (r0 / 2) ⊆ (chartAt ℂ (M 0)).target :=
    (Metric.closedBall_subset_ball hr0halflt).trans hr0sub
  have hB0compact : IsCompact (closure B0) := by
    have hK : IsCompact ((chartAt ℂ (M 0)).symm ''
        Metric.closedBall (chartAt ℂ (M 0) (M 0)) (r0 / 2)) :=
      (isCompact_closedBall _ _).image_of_continuousOn
        ((chartAt ℂ (M 0)).symm.continuousOn.mono hcballsub0)
    have hsub : closure B0 ⊆ (chartAt ℂ (M 0)).symm ''
        Metric.closedBall (chartAt ℂ (M 0) (M 0)) (r0 / 2) :=
      closure_minimal (Set.image_mono Metric.ball_subset_closedBall) hK.isClosed
    exact hK.of_isClosed_subset isClosed_closure hsub
  have hB0mem : M 0 ∈ B0 :=
    ⟨chartAt ℂ (M 0) (M 0), Metric.mem_ball_self (by linarith), (chartAt ℂ (M 0)).left_inv
      (mem_chart_source ℂ (M 0))⟩
  have main := exists_weakSolution_chain_step C B0 hB0open hB0compact hB0mem
  obtain ⟨f, U, hUopen, hUcompact, hM0U, hoff, hcm, hne, hwQ, hwP⟩ := main C.n le_rfl
  have hM0ne : M 0 ≠ M C.n := by rw [hM0, hMn]; exact hPQ
  have hordQ : ordAt C.n (M 0) = -1 := by simp [hordAt_def, hM0ne]
  have hordP : ordAt C.n (M C.n) = 1 := by simp [hordAt_def, Ne.symm hM0ne]
  have hQU : Q ∈ U := hM0 ▸ hM0U
  have hwQ' : IsWeakSolutionAt f Q (-1) := by rw [← hM0, ← hordQ]; exact hwQ
  have hwP' : IsWeakSolutionAt f P 1 := by rw [← hMn, ← hordP]; exact hwP
  have hPU : P ∈ U := by
    by_contra hPnotU
    have hPne0 : P ≠ M 0 := by rw [← hMn]; exact (Ne.symm hM0ne)
    have hfP1 : f P = 1 := hoff P hPnotU hPne0
    have hfP0 : f P = 0 := hwP'.apply_eq_zero_of_ne_zero one_ne_zero
    rw [hfP0] at hfP1; exact zero_ne_one hfP1
  refine ⟨f, U, ⟨?_, ?_, hwP', hwQ'⟩, hUopen, hUcompact, hPU, hQU, ?_⟩
  · rw [← hM0]; exact hcm
  · intro x hxP hxQ
    apply hne x
    · change x ≠ M 0
      rw [hM0]; exact hxQ
    · change x ≠ M C.n
      rw [hMn]; exact hxP
  · intro x hx
    exact hoff x hx (fun hxeq => hx (hxeq ▸ hM0U))

end RS.AbelWeak

end
