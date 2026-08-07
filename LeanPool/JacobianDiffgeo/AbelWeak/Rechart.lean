/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.AbelWeak.WeakSolution
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Rechart: `IsWeakSolutionAt` is chart-independent, and general order-additive multiplication

Unit: abel-weak-solutions, closing the gap recorded in this unit's own root docstring and in
`docs/design/abel-theorem.md` §1.4/§4.1 (task: authorized edit inside `Jacobian/AbelWeak/`). The
missing piece for the general multi-chart `exists_weakSolutionOfPair` was a "rechart" lemma:
`IsWeakSolutionAt`'s local model, witnessed in one `maximalAtlas` chart, can be re-witnessed in
ANY OTHER `maximalAtlas` chart at the same point, via mathlib's removable-singularity theorem
applied to the transition map's divided difference (`dslope`). This file builds that lemma
(`exists_localModel_of_isWeakSolutionAt`) and its main consumer, a fully general order-additive
multiplication (`IsWeakSolutionAt.mul`): combining `IsWeakSolutionAt f a k1` and
`IsWeakSolutionAt g a k2` (witnessed in POSSIBLY DIFFERENT charts) gives a function `h`, equal to
`f * g` everywhere except possibly at `a` itself, with `IsWeakSolutionAt h a (k1 + k2)`.

**The junk-value subtlety** (why `h` cannot always literally be `f * g`): `IsWeakSolutionAt`'s
local model is a FULL-neighbourhood equality `f =ᶠ[𝓝 a] fun x => ψ (e x) * (e x - e a) ^ k`,
which pins down the actual value of `f` at `a` itself via the `zpow`-at-zero junk convention
(`0 ^ k = 0` for `k ≠ 0`, `0 ^ 0 = 1`). For `k1, k2` both nonzero with `k1 + k2 = 0` (the
"cancellation" case genuinely needed by the chain induction: a `+1`-order zero of one piece
meeting a `-1`-order pole of the next), `(f * g) a = f a * g a = 0 * 0 = 0` (both individual junk
values), but the model at order `0` demands the value at `a` be `ψ (e a) * φ (e a) ≠ 0` (the
correct removable-singularity limit). So `f * g` and the desired weak solution of order `k1 + k2`
genuinely disagree AT `a` in this case; `Function.update` at the single point `a` repairs this,
uniformly for every `k1, k2` (no case split needed: `Function.update`'s value
`ψ (e a) * φ (e a) * (0 : ℂ) ^ (k1 + k2)` matches BOTH the cancelling case, `= ψ (e a) * φ (e a)`
when `k1 + k2 = 0`, AND the generic case, `= 0`, matching what the naive product already gives).
-/

open scoped ContDiff Manifold
open IsManifold Filter Topology Set

noncomputable section

namespace RS.AbelWeak

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ## A planar helper: `ContDiffAt` of a fixed integer power of a nonvanishing function -/

/-- A real-`C^∞` function, nonvanishing at a point, raised to any FIXED integer power, is again
real-`C^∞` there (`ContDiffAt.pow`/`ContDiffAt.inv` case split on the sign of `k`). -/
private theorem contDiffAt_zpow_of_ne_zero {f : ℂ → ℂ} {z : ℂ} {k : ℤ}
    (hf : ContDiffAt ℝ ∞ f z) (hfz0 : f z ≠ 0) :
    ContDiffAt ℝ ∞ (fun w => f w ^ k) z := by
  obtain ⟨n, rfl | rfl⟩ := k.eq_nat_or_neg
  · simpa using hf.pow n
  · have h1 : ContDiffAt ℝ ∞ (fun w => f w ^ n) z := by simpa using hf.pow n
    have h1z : f z ^ n ≠ 0 := pow_ne_zero n hfz0
    -- the ascription pins the `NormedSpace ℝ ℂ` instance path to the goal's (`ContDiffAt.inv`
    -- produces the `NormedAlgebra` one, which does not match syntactically)
    have h2 : ContDiffAt ℝ ∞ (fun w => (f w ^ n)⁻¹) z := h1.inv h1z
    simpa [zpow_neg, zpow_natCast] using h2

/-! ## The rechart lemma -/

omit [T2Space X] [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- **The rechart lemma**: `IsWeakSolutionAt f a k`'s local model, witnessed by SOME chart `e`, is
also witnessed by ANY OTHER `maximalAtlas` chart `e'` at `a`. Proof: the transition map
`S := e ∘ e'.symm` is holomorphic (chart compatibility) hence `AnalyticAt`; its "divided
difference" `H := dslope S (e' a)` is `AnalyticAt` too (`HasFPowerSeriesAt.
has_fpower_series_dslope_fslope`), agrees with `S`'s derivative at `e' a` (`dslope_same`), and
that derivative is NONZERO because `S` has a two-sided holomorphic inverse (the reverse
transition `T`), so `T ∘ S = id` near `e' a` forces `(deriv T (S (e' a))) * (deriv S (e' a)) = 1`
by the chain rule. The unconditional identity `sub_smul_dslope` (`(b - a) • dslope f a b
= f b - f a`, no case split on `b = a`) then gives the exact factorisation
`e x - e a = (e' x - e' a) * H (e' x)` needed to rewrite the local model. -/
theorem exists_localModel_of_isWeakSolutionAt {f : X → ℂ} {a : X} {k : ℤ}
    (hf : IsWeakSolutionAt f a k) {e' : OpenPartialHomeomorph X ℂ}
    (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X) (ha' : a ∈ e'.source) :
    ∃ ψ' : ℂ → ℂ, (∀ᶠ z in 𝓝 (e' a), ψ' z ≠ 0) ∧ ContDiffAt ℝ ∞ ψ' (e' a) ∧
      f =ᶠ[𝓝 a] (fun x => ψ' (e' x) * (e' x - e' a) ^ k) := by
  obtain ⟨e, he, ha, ψ, hψne, hψdiff, hfeq⟩ := hf
  set S : ℂ → ℂ := fun w => e (e'.symm w) with hS_def
  set T : ℂ → ℂ := fun z => e' (e.symm z) with hT_def
  set w0 : ℂ := e' a with hw0_def
  have heaa' : (e'.symm w0 : X) = a := by rw [hw0_def]; exact e'.left_inv ha'
  have hae : (e.symm (e a) : X) = a := e.left_inv ha
  have hSmdiff : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω S w0 := by
    have h1 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (⇑e'.symm) w0 :=
      contMDiffAt_symm_of_mem_maximalAtlas he' (e'.map_source ha')
    have h2 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (⇑e) (e'.symm w0) := by
      apply contMDiffAt_of_mem_maximalAtlas he; rw [heaa']; exact ha
    exact h2.comp w0 h1
  have hTmdiff : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω T (e a) := by
    have h1 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (⇑e.symm) (e a) :=
      contMDiffAt_symm_of_mem_maximalAtlas he (e.map_source ha)
    have h2 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (⇑e') (e.symm (e a)) := by
      apply contMDiffAt_of_mem_maximalAtlas he'; rw [hae]; exact ha'
    exact h2.comp (e a) h1
  have hSanalytic : AnalyticAt ℂ S w0 := (contMDiffAt_iff_contDiffAt.1 hSmdiff).analyticAt
  have hTanalytic : AnalyticAt ℂ T (e a) := (contMDiffAt_iff_contDiffAt.1 hTmdiff).analyticAt
  have hSw0 : S w0 = e a := by change e (e'.symm w0) = e a; rw [heaa']
  have he'symm_cont : ContinuousAt (⇑e'.symm) w0 :=
    (contMDiffAt_symm_of_mem_maximalAtlas he' (e'.map_source ha')).continuousAt
  have hTS : (fun w => T (S w)) =ᶠ[𝓝 w0] id := by
    have h1 : ∀ᶠ w in 𝓝 w0, (e'.symm w : X) ∈ e.source := by
      have h1' : Tendsto (⇑e'.symm) (𝓝 w0) (𝓝 a) := by rw [← heaa']; exact he'symm_cont
      exact h1'.eventually (e.open_source.mem_nhds ha)
    have h2 : ∀ᶠ w in 𝓝 w0, w ∈ e'.target := e'.open_target.eventually_mem (e'.map_source ha')
    filter_upwards [h1, h2] with w hw1 hw2
    change e' (e.symm (e (e'.symm w))) = w
    rw [e.left_inv hw1, e'.right_inv hw2]
  have hderivS : DifferentiableAt ℂ S w0 := hSanalytic.differentiableAt
  have hderivT' : DifferentiableAt ℂ T (S w0) := by
    rw [hSw0]; exact hTanalytic.differentiableAt
  have hcompderiv : HasDerivAt (fun w => T (S w)) (deriv T (S w0) * deriv S w0) w0 :=
    hderivT'.hasDerivAt.comp w0 hderivS.hasDerivAt
  have hidderiv : HasDerivAt (fun w => T (S w)) 1 w0 := by
    have h := (hasDerivAt_id w0).congr_of_eventuallyEq hTS
    simpa using h
  have hderivprod : deriv T (S w0) * deriv S w0 = 1 := hcompderiv.unique hidderiv
  have hSderiv_ne : deriv S w0 ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hderivprod; exact one_ne_zero hderivprod.symm
  obtain ⟨p, hp⟩ := id hSanalytic
  have hdslope_fps : HasFPowerSeriesAt (dslope S w0) p.fslope w0 :=
    hp.has_fpower_series_dslope_fslope
  set H : ℂ → ℂ := dslope S w0 with hH_def
  have hHanalytic : AnalyticAt ℂ H w0 := ⟨p.fslope, hdslope_fps⟩
  have hHw0 : H w0 = deriv S w0 := dslope_same S w0
  have hHw0_ne : H w0 ≠ 0 := by rw [hHw0]; exact hSderiv_ne
  have hHcontDiffAtC : ContDiffAt ℂ ∞ H w0 := hHanalytic.contDiffAt
  have hHcontDiffAt : ContDiffAt ℝ ∞ H w0 := hHcontDiffAtC.restrict_scalars ℝ
  have hHcont : ContinuousAt H w0 := hHcontDiffAtC.continuousAt
  have hHne : ∀ᶠ w in 𝓝 w0, H w ≠ 0 := hHcont.eventually_ne hHw0_ne
  have hSeq : ∀ᶠ x in 𝓝 a, S (e' x) = e x := by
    filter_upwards [e'.open_source.mem_nhds ha'] with x hx2
    change e (e'.symm (e' x)) = e x
    rw [e'.left_inv hx2]
  have htrans : ∀ᶠ x in 𝓝 a, e x - e a = (e' x - w0) * H (e' x) := by
    filter_upwards [hSeq] with x hex
    have hfact : S (e' x) - S w0 = (e' x - w0) * H (e' x) := by
      rw [← sub_smul_dslope S w0 (e' x), smul_eq_mul]
    rw [hex, hSw0] at hfact; exact hfact
  -- Assemble the new cofactor `ψ' z := ψ (S z) * H z ^ k`.
  have hScont : ContinuousAt S w0 := hSanalytic.continuousAt
  have hψSne : ∀ᶠ z in 𝓝 w0, ψ (S z) ≠ 0 := by
    have : Tendsto S (𝓝 w0) (𝓝 (e a)) := by rw [← hSw0]; exact hScont
    exact this.eventually hψne
  have hSContDiffAt : ContDiffAt ℝ ∞ S w0 := hSanalytic.contDiffAt.restrict_scalars ℝ
  have hψdiff' : ContDiffAt ℝ ∞ ψ (S w0) := by rw [hSw0]; exact hψdiff
  have hψScontDiffAt : ContDiffAt ℝ ∞ (fun z => ψ (S z)) w0 := hψdiff'.comp w0 hSContDiffAt
  have hHzpow : ContDiffAt ℝ ∞ (fun z => H z ^ k) w0 :=
      contDiffAt_zpow_of_ne_zero hHcontDiffAt hHw0_ne
  refine ⟨fun z => ψ (S z) * H z ^ k, ?_, ?_, ?_⟩
  · filter_upwards [hψSne, hHne] with z hz1 hz2
    exact mul_ne_zero hz1 (zpow_ne_zero k hz2)
  · exact hψScontDiffAt.mul hHzpow
  · filter_upwards [hfeq, htrans, hSeq] with x hx1 hx2 hx3
    rw [hx1, hx2, mul_zpow, ← hx3]
    ring

/-! ## General order-additive multiplication -/

omit [T2Space X] [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- **General order-additive multiplication** (subsumes `IsWeakSolutionAt.mul_of_contMDiffAt`'s
`k2 = 0` case, and the "opposite order cancellation" the general chain induction needs at every
interior breakpoint): given `IsWeakSolutionAt f a k1` and `IsWeakSolutionAt g a k2` (witnessed by
POSSIBLY DIFFERENT charts, aligned here via `exists_localModel_of_isWeakSolutionAt`), there is a
function `h`, equal to `f * g` everywhere EXCEPT possibly at `a` (see the file docstring for why
`a` needs a genuine `Function.update`, not the naive product), with
`IsWeakSolutionAt h a (k1 + k2)`. -/
theorem IsWeakSolutionAt.mul {f g : X → ℂ} {a : X} {k1 k2 : ℤ}
    (hf : IsWeakSolutionAt f a k1) (hg : IsWeakSolutionAt g a k2) :
    ∃ h : X → ℂ, IsWeakSolutionAt h a (k1 + k2) ∧ ∀ x, x ≠ a → h x = f x * g x := by
  obtain ⟨e, he, ha, ψ1, hψ1ne, hψ1diff, hfeq⟩ := hf
  obtain ⟨ψ2, hψ2ne, hψ2diff, hgeq⟩ := exists_localModel_of_isWeakSolutionAt hg he ha
  classical
  set h : X → ℂ :=
    Function.update (fun x => f x * g x) a (ψ1 (e a) * ψ2 (e a) * (0 : ℂ) ^ (k1 + k2)) with hh_def
  refine ⟨h, ⟨e, he, ha, fun z => ψ1 z * ψ2 z, ?_, ?_, ?_⟩, ?_⟩
  · filter_upwards [hψ1ne, hψ2ne] with z hz1 hz2; exact mul_ne_zero hz1 hz2
  · exact hψ1diff.mul hψ2diff
  · filter_upwards [hfeq, hgeq, e.open_source.mem_nhds ha] with x hx1 hx2 hx3
    rcases eq_or_ne x a with rfl | hxa
    · show h x = ψ1 (e x) * ψ2 (e x) * (e x - e x) ^ (k1 + k2)
      rw [sub_self, hh_def, Function.update_self]
    · have hexne : e x - e a ≠ 0 := by
        rw [sub_ne_zero]
        intro hc
        exact hxa (by rw [← e.left_inv hx3, hc, e.left_inv ha])
      have hzpoweq : (e x - e a) ^ k1 * (e x - e a) ^ k2 = (e x - e a) ^ (k1 + k2) :=
        (zpow_add₀ hexne k1 k2).symm
      change h x = ψ1 (e x) * ψ2 (e x) * (e x - e a) ^ (k1 + k2)
      rw [hh_def, Function.update_of_ne hxa, hx1, hx2, ← hzpoweq]
      ring
  · intro x hxa
    rw [hh_def, Function.update_of_ne hxa]

end RS.AbelWeak

end
