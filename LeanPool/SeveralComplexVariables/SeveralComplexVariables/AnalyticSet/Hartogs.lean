/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.AnalyticSet.Removable
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.HartogsContinuation

/-!
# Hartogs extension across analytic subsets

A Hartogs figure avoiding an analytic exceptional set determines an extension on the whole
cylinder. The complement of a proper analytic subset is connected, so the identity principle
identifies this extension with the original function. Isolated two-dimensional slices supply
such figures near the exceptional set.

## Main results

`IsAnalyticSet.exists_extension_of_hartogsCylinder_subset` extends across a Hartogs figure that
avoids the analytic set. `exists_hartogs_neighborhood` produces such a figure near an isolated
two-dimensional slice. `IsAnalyticSet.exists_local_extension_of_isolated_two_slice` is local
extension from that figure.
-/

public noncomputable section

open Set Filter Metric
open scoped Topology

namespace SeveralComplexVariables

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- A Hartogs cylinder avoiding an analytic subset gives an extension across that subset.
Connectedness of its complement ensures agreement everywhere it is defined. -/
theorem IsAnalyticSet.exists_extension_of_hartogsCylinder_subset
    {D D₀ : Set E} {ρ R : ℝ} {A : Set (E × ℂ)}
    (hA : IsAnalyticSet (D ×ˢ ball 0 R) A)
    (hD : IsOpen D) (hc : IsPreconnected D) (hD₀ : IsOpen D₀) (hne : D₀.Nonempty)
    (hsub : D₀ ⊆ D) (hρ : 0 ≤ ρ) (hρR : ρ < R)
    (hHA : hartogsCylinder D D₀ ρ R ⊆ (D ×ˢ ball 0 R) \ A)
    {f : E × ℂ → F} (hf : AnalyticOnNhd ℂ f ((D ×ˢ ball 0 R) \ A)) :
    ∃ g, AnalyticOnNhd ℂ g (D ×ˢ ball 0 R) ∧ EqOn g f ((D ×ˢ ball 0 R) \ A) := by
  obtain ⟨g, hg, heq⟩ := exists_extension_hartogsCylinder hD hc hD₀ hne hsub hρ hρR
    (hf.mono hHA)
  obtain ⟨b, hb⟩ := hne
  have hbH : (b, (0 : ℂ)) ∈ hartogsCylinder D D₀ ρ R :=
    Or.inr ⟨hb, mem_ball_self (hρ.trans_lt hρR)⟩
  have hproper : A ≠ D ×ˢ ball 0 R := by
    intro h
    exact (hHA hbH).2 (h.symm ▸ (hHA hbH).1)
  have hconn := hA.isConnected_sdiff
    ⟨⟨(b, 0), (hHA hbH).1⟩, hc.prod isPreconnected_ball⟩ hproper
  have hH : IsOpen (hartogsCylinder D D₀ ρ R) :=
    (hD.prod (isOpen_ball.sdiff isClosed_closedBall)).union (hD₀.prod isOpen_ball)
  exact ⟨g, hg, (hg.mono sdiff_subset).eqOn_of_preconnected_of_eventuallyEq hf
    hconn.isPreconnected (hHA hbH) ((hH.eventually_mem hbH).mono (fun _ hz => heq hz))⟩

/-- The small base disc of an off-center Hartogs figure lies in the large base disc. -/
private theorem offCenter_ball_subset {R : ℝ} (hR : 0 < R) :
    ball ((R / 2 : ℝ) : ℂ) (R / 4) ⊆ ball 0 R := by
  apply ball_subset_ball'
  simp only [dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hR)]
  linarith

/-- An off-center Hartogs figure fits inside a compact shell avoiding the origin. -/
private theorem offCenter_hartogsCylinder_subset_shell {R : ℝ} (hR : 0 < R) :
    hartogsCylinder (ball (0 : ℂ) R) (ball ((R / 2 : ℝ) : ℂ) (R / 4)) (R / 2) R ⊆
      closedBall (0 : ℂ × ℂ) R \ ball 0 (R / 4) := by
  intro p hp
  have hpR : p ∈ ball (0 : ℂ × ℂ) R := by
    rw [← ball_prod_same]
    rcases hp with hp | hp
    · exact ⟨hp.1, hp.2.1⟩
    · exact ⟨offCenter_ball_subset hR hp.1, hp.2⟩
  refine ⟨ball_subset_closedBall hpR, ?_⟩
  intro hp0
  have hsmall : p ∈ ball (0 : ℂ) (R / 4) ×ˢ ball 0 (R / 4) := by
    rwa [ball_prod_same]
  rcases hp with hp | hp
  · exact hp.2.2 (ball_subset_closedBall ((ball_subset_ball (by linarith)) hsmall.2))
  · have hd := dist_triangle ((R / 2 : ℝ) : ℂ) p.1 0
    have h₁ := mem_ball.mp hp.1
    have h₂ := mem_ball.mp hsmall.1
    rw [dist_comm p.1 ((R / 2 : ℝ) : ℂ)] at h₁
    simp only [dist_zero_right] at h₂
    simp only [dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (half_pos hR)] at hd
    linarith

omit [FiniteDimensional ℂ E] in
/-- Compact subsets of an open set remain in it under small translations of a fixed continuous
linear image. -/
private theorem eventually_add_image_subset {P : Type*} [NormedAddCommGroup P]
    [NormedSpace ℂ P] {K : Set P} (hK : IsCompact K) {V : Set E} (hV : IsOpen V)
    {a : E} (L : P →L[ℂ] E) (hsub : ∀ p ∈ K, a + L p ∈ V) :
    ∀ᶠ z in 𝓝 a, ∀ p ∈ K, z + L p ∈ V := by
  apply hK.eventually_forall_of_forall_eventually
  intro p hp
  exact (continuous_fst.add (L.continuous.comp continuous_snd)).continuousAt.preimage_mem_nhds
    (hV.mem_nhds (hsub p hp))

omit [FiniteDimensional ℂ E] in
/-- An isolated two-dimensional slice supplies a Hartogs figure, together with nearby parallel
translates, that avoids the exceptional set. -/
private theorem exists_hartogs_neighborhood {U A : Set E}
    (hU : IsOpen U) (hUA : IsOpen (U \ A)) {a : E} (ha : a ∈ U)
    (L : (ℂ × ℂ) →L[ℂ] E)
    (hisol : ∀ᶠ p in 𝓝 (0 : ℂ × ℂ), a + L p ∈ A → p = 0) :
    ∃ δ R : ℝ, 0 < δ ∧ 0 < R ∧
      (∀ q ∈ (ball a δ ×ˢ ball (0 : ℂ) R) ×ˢ ball (0 : ℂ) R,
        q.1.1 + L (q.1.2, q.2) ∈ U) ∧
      (∀ q ∈ hartogsCylinder (ball a δ ×ˢ ball (0 : ℂ) R)
        (ball a δ ×ˢ ball ((R / 2 : ℝ) : ℂ) (R / 4)) (R / 2) R,
        q.1.1 + L (q.1.2, q.2) ∈ U \ A) := by
  have hstay : ∀ᶠ p in 𝓝 (0 : ℂ × ℂ), a + L p ∈ U :=
    (continuous_const.add L.continuous).continuousAt.preimage_mem_nhds
      (by simpa using hU.mem_nhds ha)
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp (hstay.and hisol)
  let R := ε / 2
  have hR : 0 < R := half_pos hε
  have hcentral (p : ℂ × ℂ) (hp : p ∈ closedBall 0 R) :
      a + L p ∈ U ∧ (a + L p ∈ A → p = 0) :=
    hεsub (closedBall_subset_ball (half_lt_self hε) hp)
  let K := closedBall (0 : ℂ × ℂ) R \ ball 0 (R / 4)
  have hK : IsCompact K := (isCompact_closedBall _ _).diff isOpen_ball
  have hcentralK (p : ℂ × ℂ) (hp : p ∈ K) : a + L p ∈ U \ A := by
    refine ⟨(hcentral p hp.1).1, fun hpA => ?_⟩
    have hp0 := (hcentral p hp.1).2 hpA
    exact hp.2 (hp0 ▸ mem_ball_self (by dsimp [R]; positivity))
  have hfull := eventually_add_image_subset (isCompact_closedBall (0 : ℂ × ℂ) R)
    hU L (fun p hp => (hcentral p hp).1)
  have hshell := eventually_add_image_subset hK hUA L hcentralK
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp (hfull.and hshell)
  refine ⟨δ, R, hδ, hR, ?_, ?_⟩
  · intro q hq
    apply (hδsub hq.1.1).1 (q.1.2, q.2)
    rw [← closedBall_prod_same]
    exact ⟨ball_subset_closedBall hq.1.2, ball_subset_closedBall hq.2⟩
  · intro q hq
    have hz : q.1.1 ∈ ball a δ := by rcases hq with hq | hq <;> exact hq.1.1
    apply (hδsub hz).2 (q.1.2, q.2)
    apply offCenter_hartogsCylinder_subset_shell hR
    rcases hq with hq | hq
    · exact Or.inl ⟨hq.1.2, hq.2⟩
    · exact Or.inr ⟨hq.1.2, hq.2⟩

/-- An analytic subset with an isolated two-dimensional slice admits local extension of every
holomorphic function on its complement. No boundedness is assumed. -/
theorem IsAnalyticSet.exists_local_extension_of_isolated_two_slice
    {U A : Set E} (hA : IsAnalyticSet U A) {a : E} (ha : a ∈ U)
    (L : (ℂ × ℂ) →L[ℂ] E)
    (hisol : ∀ᶠ p in 𝓝 (0 : ℂ × ℂ), a + L p ∈ A → p = 0)
    {f : E → F} (hf : AnalyticOnNhd ℂ f (U \ A)) :
    ∃ r : ℝ, 0 < r ∧ ∃ g : E → F,
      AnalyticOnNhd ℂ g (ball a r) ∧ EqOn g f (ball a r \ A) := by
  obtain ⟨δ, R, hδ, hR, hfull, hshell⟩ :=
    exists_hartogs_neighborhood hA.isOpen_domain hA.isOpen_sdiff ha L hisol
  let D := ball a δ ×ˢ ball (0 : ℂ) R
  let D₀ := ball a δ ×ˢ ball ((R / 2 : ℝ) : ℂ) (R / 4)
  let B := D ×ˢ ball (0 : ℂ) R
  let T : (E × ℂ) × ℂ → E := fun q => q.1.1 + L (q.1.2, q.2)
  have hT : AnalyticOnNhd ℂ T B := fun q _ =>
    (analyticAt_fst.comp analyticAt_fst).add ((L.analyticAt _).comp
      ((analyticAt_snd.comp analyticAt_fst).prod analyticAt_snd))
  have hD : IsOpen D := isOpen_ball.prod isOpen_ball
  have hB : IsOpen B := hD.prod isOpen_ball
  have hpre : IsAnalyticSet B (B ∩ T ⁻¹' A) := hA.preimage hB hT hfull
  have hfT : AnalyticOnNhd ℂ (f ∘ T) (B \ (B ∩ T ⁻¹' A)) := by
    intro q hq
    exact (hf (T q) ⟨hfull q hq.1, fun hqA => hq.2 ⟨hq.1, hqA⟩⟩).comp (hT q hq.1)
  have hH : hartogsCylinder D D₀ (R / 2) R ⊆ B \ (B ∩ T ⁻¹' A) := by
    intro q hq
    have hqB : q ∈ B := by
      rcases hq with hq | hq
      · exact ⟨hq.1, hq.2.1⟩
      · exact ⟨⟨hq.1.1, offCenter_ball_subset hR hq.1.2⟩, hq.2⟩
    exact ⟨hqB, fun hqA => (hshell q hq).2 hqA.2⟩
  obtain ⟨G, hG, hGF⟩ := hpre.exists_extension_of_hartogsCylinder_subset hD
    (isPreconnected_ball.prod isPreconnected_ball) (isOpen_ball.prod isOpen_ball)
    ⟨(a, ((R / 2 : ℝ) : ℂ)), mem_ball_self hδ, mem_ball_self (by positivity)⟩
    (prod_mono_right (offCenter_ball_subset hR)) (half_pos hR).le (half_lt_self hR) hH hfT
  refine ⟨δ, hδ, fun z => G ((z, 0), 0), ?_, ?_⟩
  · intro z hz
    exact (hG ((z, 0), 0) ⟨⟨hz, mem_ball_self hR⟩, mem_ball_self hR⟩).comp
      (f := fun z : E => ((z, (0 : ℂ)), (0 : ℂ)))
      ((analyticAt_id.prod analyticAt_const).prod analyticAt_const)
  · intro z hz
    have hzB : ((z, (0 : ℂ)), (0 : ℂ)) ∈ B :=
      ⟨⟨hz.1, mem_ball_self hR⟩, mem_ball_self hR⟩
    have hL0 : L ((0 : ℂ), (0 : ℂ)) = 0 := L.map_zero
    have heq := hGF ⟨hzB, fun hp => hz.2 (by simpa [T, hL0] using hp.2)⟩
    simpa [T, hL0] using heq

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
