/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.Homotopy.Path
import Mathlib.Analysis.Convex.Segment

/-!
# Planar atoms for paths-and-integrals (CC6)

Unit: paths-and-integrals (`docs/design/paths-and-integrals.md` §2.3). Pure-`ℂ` content, no
manifold imports: this file is meant to be reused by `dbar-solvability`, `residue-calculus`,
`monodromy`, and `abel-weak-solutions` for disk primitives and convex-minus-countable
path-connectivity — do not re-prove these atoms elsewhere.

Main declarations:
* `RS.exists_hasDerivAt_ball` — a holomorphic function on a disk has a primitive with a
  prescribed value at any interior point (Morera, via mathlib's `HasPrimitives.lean`).
* `RS.eventuallyEq_of_hasDerivAt_eq` — two local primitives of the same function that agree at a
  point agree on a neighborhood of it.
* `RS.Convex.isPathConnected_diff_countable` — an open convex planar set minus a countable set is
  path-connected.
* `RS.exists_homotopy_range_subset_of_convex` — any two paths with the same endpoints inside a
  convex planar set are homotopic rel endpoints through the set (affine homotopy).
-/

noncomputable section

namespace RS

open Complex Metric Set
open scoped Topology Convex

/-- Primitive with prescribed value on a ball inside a domain of analyticity. -/
theorem exists_hasDerivAt_ball {f : ℂ → ℂ} {U : Set ℂ} (hf : AnalyticOnNhd ℂ f U)
    {c z₀ w : ℂ} {r : ℝ} (hb : ball c r ⊆ U) (_hz₀ : z₀ ∈ ball c r) :
    ∃ g : ℂ → ℂ, g z₀ = w ∧ ∀ z ∈ ball c r, HasDerivAt g (f z) z := by
  obtain ⟨g, hg₀, hg⟩ := (hf.differentiableOn.mono hb).isExactOn_ball.with_val_at z₀ w
  exact ⟨g, hg₀, hg⟩

/-- Two local primitives of the same function with equal value agree nearby. -/
theorem eventuallyEq_of_hasDerivAt_eq {f g d : ℂ → ℂ} {z₀ : ℂ}
    (hf : ∀ᶠ z in 𝓝 z₀, HasDerivAt f (d z) z) (hg : ∀ᶠ z in 𝓝 z₀, HasDerivAt g (d z) z)
    (h : f z₀ = g z₀) : f =ᶠ[𝓝 z₀] g := by
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp (hf.and hg)
  have key : ∀ z ∈ ball z₀ r, (fun w => f w - g w) z = (fun w => f w - g w) z₀ := by
    intro z hz
    refine (convex_ball z₀ r).is_const_of_fderivWithin_eq_zero (𝕜 := ℂ)
      (fun w hw =>
        (((hball w hw).1.fun_sub (hball w hw).2).differentiableAt.differentiableWithinAt))
      (fun w hw => ?_) hz (mem_ball_self hr)
    have h0' : HasDerivAt (fun w => f w - g w) 0 w := by
      simpa using ((hball w hw).1.fun_sub (hball w hw).2)
    rw [fderivWithin_of_isOpen isOpen_ball hw]
    simpa using h0'.hasFDerivAt.fderiv
  filter_upwards [ball_mem_nhds z₀ hr] with z hz
  have hz' := key z hz
  simp only at hz'
  linear_combination hz' + h

/-! ### An open convex planar set minus a countable set is path-connected

Adaptation of `Set.Countable.isPathConnected_compl_of_one_lt_rank`
(`Analysis/Normed/Module/Connected.lean`), relativized to a convex open subset `s` instead of
the whole space: the auxiliary point `z t := c + t • y` is kept inside a ball around the
midpoint `c` that lies in `s` (openness), instead of ranging over all of `t : ℝ`. -/

theorem Convex.isPathConnected_diff_countable {s : Set ℂ} (hs : Convex ℝ s) (ho : IsOpen s)
    (hne : s.Nonempty) {T : Set ℂ} (hT : T.Countable) : IsPathConnected (s \ T) := by
  -- `s \ T` is nonempty: `Tᶜ` is dense, `s` is open nonempty.
  obtain ⟨a, haT, has⟩ := (hT.dense_compl ℝ).exists_mem_open ho hne
  refine ⟨a, ⟨has, haT⟩, ?_⟩
  intro b hb
  obtain ⟨hbs, hbT⟩ := hb
  rcases eq_or_ne a b with rfl | hab
  · exact JoinedIn.refl ⟨has, haT⟩
  -- `c` = midpoint of `a`, `b`; `x` = half the difference; both in `s` by convexity.
  set c : ℂ := (2 : ℝ)⁻¹ • (a + b) with hc_def
  set x : ℂ := (2 : ℝ)⁻¹ • (b - a) with hx_def
  have hcs : c ∈ s := by
    have h := hs has hbs (a := (2 : ℝ)⁻¹) (b := (2 : ℝ)⁻¹) (by norm_num) (by norm_num) (by norm_num)
    simpa [hc_def, smul_add] using h
  have hIa : c - x = a := by simp only [hc_def, hx_def]; module
  have hIb : c + x = b := by simp only [hc_def, hx_def]; module
  have hx_ne_zero : x ≠ 0 := by simpa [hx_def] using sub_ne_zero.2 hab.symm
  obtain ⟨y, hy⟩ : ∃ y, LinearIndependent ℝ ![x, y] :=
    exists_linearIndependent_pair_of_one_lt_rank (by rw [Complex.rank_real_complex]; norm_num)
      hx_ne_zero
  -- a ball around `c` inside `s` (openness), and the ‖y‖-scaled radius so `c + t • y ∈ s`.
  obtain ⟨ε, hε, hballs⟩ := Metric.isOpen_iff.mp ho c hcs
  have hy_ne_zero : y ≠ 0 := by
    intro hy0
    apply hy.ne_zero 1
    simpa using hy0
  set ρ : ℝ := ε / ‖y‖ with hρ_def
  have hρ_pos : 0 < ρ := div_pos hε (norm_pos_iff.mpr hy_ne_zero)
  have hzmem : ∀ t : ℝ, t ∈ Ioo (-ρ) ρ → c + t • y ∈ s := by
    intro t ht
    refine hballs ?_
    simp only [mem_ball]
    have : ‖t • y‖ = |t| * ‖y‖ := by rw [norm_smul, Real.norm_eq_abs]
    have habs : |t| < ρ := abs_lt.mpr ht
    calc dist (c + t • y) c = ‖t • y‖ := by rw [dist_eq_norm]; ring_nf
      _ = |t| * ‖y‖ := this
      _ < ρ * ‖y‖ := by
          exact mul_lt_mul_of_pos_right habs (norm_pos_iff.mpr hy_ne_zero)
      _ = ε := by rw [hρ_def]; exact div_mul_cancel₀ ε (norm_ne_zero_iff.mpr hy_ne_zero)
  -- The two exceptional sets of parameters `t` whose connecting segment meets `T`.
  have hA : Set.Countable {t : ℝ | ([c + x -[ℝ] c + t • y] ∩ T).Nonempty} := by
    apply countable_ofPred_nonempty_of_disjoint _ (fun t ↦ inter_subset_right) hT
    intro t t' htt'
    apply disjoint_iff_inter_eq_empty.2
    have N : {c + x} ∩ T = ∅ := by
      simpa only [singleton_inter_eq_empty, mem_compl_iff, hIb] using hbT
    rw [inter_assoc, inter_comm T, inter_assoc, inter_self, ← inter_assoc, ← subset_empty_iff, ← N]
    apply inter_subset_inter_left
    exact (segment_inter_eq_endpoint_of_linearIndependent_of_ne hy htt'.symm c).subset
  have hB : Set.Countable {t : ℝ | ([c - x -[ℝ] c + t • y] ∩ T).Nonempty} := by
    apply countable_ofPred_nonempty_of_disjoint _ (fun t ↦ inter_subset_right) hT
    intro t t' htt'
    apply disjoint_iff_inter_eq_empty.2
    have N : {c - x} ∩ T = ∅ := by
      simpa only [singleton_inter_eq_empty, mem_compl_iff, hIa] using haT
    rw [inter_assoc, inter_comm T, inter_assoc, inter_self, ← inter_assoc, ← subset_empty_iff, ← N]
    apply inter_subset_inter_left
    rw [sub_eq_add_neg _ x]
    refine (segment_inter_eq_endpoint_of_linearIndependent_of_ne ?_ htt'.symm c).subset
    convert hy.units_smul ![-1, 1] <;> [skip; rfl; rfl]
    simp [← List.ofFn_inj]
  -- pick `t` in `Ioo (-ρ) ρ` outside both countable exceptional sets.
  have hopen : IsOpen (Ioo (-ρ) ρ) := isOpen_Ioo
  have hnonempty : (Ioo (-ρ) ρ).Nonempty := nonempty_Ioo.mpr (by linarith)
  obtain ⟨t, htnotin, ht_mem⟩ :=
    ((hA.union hB).dense_compl ℝ).exists_mem_open hopen hnonempty
  simp only [compl_union, mem_inter_iff, mem_compl_iff, mem_ofPred_eq, not_nonempty_iff_eq_empty]
    at htnotin
  set z : ℂ := c + t • y with hz_def
  have hzs : z ∈ s := hzmem t ht_mem
  have JA : JoinedIn (s \ T) a z := by
    apply JoinedIn.of_segment_subset
    rw [subset_sdiff]
    refine ⟨hs.segment_subset has hzs, ?_⟩
    rw [disjoint_iff_inter_eq_empty]
    have heq : [a -[ℝ] z] = [c - x -[ℝ] z] := by rw [hIa]
    rw [heq]
    exact htnotin.2
  have JB : JoinedIn (s \ T) b z := by
    apply JoinedIn.of_segment_subset
    rw [subset_sdiff]
    refine ⟨hs.segment_subset hbs hzs, ?_⟩
    rw [disjoint_iff_inter_eq_empty]
    have heq : [b -[ℝ] z] = [c + x -[ℝ] z] := by rw [hIb]
    rw [heq]
    exact htnotin.1
  exact JA.trans JB.symm

/-- Any two paths with the same endpoints inside a convex planar set are homotopic
rel endpoints, through the set. -/
theorem exists_homotopy_range_subset_of_convex {a b : ℂ} {s : Set ℂ} (hs : Convex ℝ s)
    {p q : Path a b} (hp : range ⇑p ⊆ s) (hq : range ⇑q ⊆ s) :
    ∃ H : p.Homotopy q, ∀ z, H z ∈ s := by
  have hcont : Continuous (fun z : ↥unitInterval × ↥unitInterval =>
      (1 - (z.1 : ℝ)) • p z.2 + (z.1 : ℝ) • q z.2) := by fun_prop
  have hmem : ∀ z : ↥unitInterval × ↥unitInterval,
      (1 - (z.1 : ℝ)) • p z.2 + (z.1 : ℝ) • q z.2 ∈ s := fun z =>
    hs (hp (mem_range_self _)) (hq (mem_range_self _))
      (by unit_interval) (by unit_interval) (by ring)
  refine ⟨{ toFun := fun z => (1 - (z.1 : ℝ)) • p z.2 + (z.1 : ℝ) • q z.2
            continuous_toFun := hcont
            map_zero_left := fun u => by simp
            map_one_left := fun u => by simp
            prop' := fun t x hx => ?_ }, fun z => hmem z⟩
  rcases hx with hx | hx
  · rw [hx]
    change (1 - ((t : ℝ))) • p 0 + (t : ℝ) • q 0 = p 0
    rw [p.source, q.source]
    module
  · rw [Set.mem_singleton_iff] at hx
    rw [hx]
    change (1 - ((t : ℝ))) • p 1 + (t : ℝ) • q 1 = p 1
    rw [p.target, q.target]
    module

end RS

end
