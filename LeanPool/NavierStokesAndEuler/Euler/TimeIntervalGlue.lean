/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TimeH1ContinuousDerivative
public import Mathlib.Topology.Piecewise

@[expose] public section

/-! Genuine first-order evolution paths glue through a matching interior trace. -/

noncomputable section

namespace EulerTimeIntervalGlue

open Set Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def glue (τ : ℝ) (f g : ℝ → E) (t : ℝ) : E := if t ≤ τ then f t else g t

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem glue_left (τ : ℝ) (f g : ℝ → E) (t : ℝ) (ht : t ≤ τ) : glue τ f g t=f t := by
  simp only [glue, ht, ite_true]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem glue_right (τ : ℝ) (f g : ℝ → E) (hmatch : f τ=g τ) (t : ℝ) (ht : τ ≤ t) :
    glue τ f g t=g t := by
  rcases ht.eq_or_lt with h | h
  · subst t
    simpa only [glue, le_refl, ite_true] using hmatch
  · simp only [glue, not_le.mpr h, ite_false]

omit [NormedSpace ℝ E] in
theorem glue_continuous (τ : ℝ) (f g : ℝ → E) (hmatch : f τ=g τ)
    (hf : Continuous f) (hg : Continuous g) : Continuous (glue τ f g) := by
  apply Continuous.if_le hf hg continuous_id continuous_const
  intro t ht
  change t=τ at ht
  subst t
  exact hmatch

/-- Matching the value and derivative gives the genuine derivative even at the joining time. -/
theorem glue_hasDerivWithinAt (S τ : ℝ) (hτ0 : 0 ≤ τ) (hτS : τ ≤ S)
    (f g f' g' : ℝ → E) (hmatch : f τ=g τ) (hmatch' : f' τ=g' τ)
    (hf : ∀ t ∈ Icc 0 τ, HasDerivWithinAt f (f' t) (Icc 0 τ) t)
    (hg : ∀ t ∈ Icc τ S, HasDerivWithinAt g (g' t) (Icc τ S) t)
    (t : ℝ) (ht : t ∈ Icc 0 S) :
    HasDerivWithinAt (glue τ f g) (glue τ f' g' t) (Icc 0 S) t := by
  rcases lt_trichotomy t τ with hlt | heq | hgt
  · have hlocal : Icc (0 : ℝ) τ ∈ 𝓝[Icc 0 S] t := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hlt), self_mem_nhdsWithin]
        with x hx hxs
      exact ⟨hxs.1, hx.le⟩
    have he : glue τ f g =ᶠ[𝓝[Icc 0 S] t] f := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hlt)] with x hx
      exact glue_left τ f g x hx.le
    rw [glue_left τ f' g' t hlt.le]
    exact ((hf t ⟨ht.1,hlt.le⟩).mono_of_mem_nhdsWithin hlocal).congr_of_eventuallyEq
      he (glue_left τ f g t hlt.le)
  · subst t
    have hl : HasDerivWithinAt (glue τ f g) (f' τ) (Icc 0 τ) τ :=
      (hf τ ⟨hτ0,le_rfl⟩).congr_of_mem
        (fun x hx => glue_left τ f g x hx.2) ⟨hτ0,le_rfl⟩
    have hr : HasDerivWithinAt (glue τ f g) (f' τ) (Icc τ S) τ := by
      rw [hmatch']
      exact (hg τ ⟨le_rfl,hτS⟩).congr_of_mem
        (fun x hx => glue_right τ f g hmatch x hx.1) ⟨le_rfl,hτS⟩
    have hunion : Icc (0 : ℝ) τ ∪ Icc τ S=Icc 0 S := by
      ext x
      simp only [mem_union, mem_Icc]
      constructor
      · rintro (h | h) <;> constructor <;> linarith
      · intro h
        by_cases hx : x ≤ τ
        · exact Or.inl ⟨h.1,hx⟩
        · exact Or.inr ⟨(not_le.mp hx).le,h.2⟩
    rw [glue_left τ f' g' τ le_rfl]
    simpa only [hunion] using hl.union hr
  · have hlocal : Icc τ S ∈ 𝓝[Icc 0 S] t := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hgt), self_mem_nhdsWithin]
        with x hx hxs
      exact ⟨hx.le,hxs.2⟩
    have he : glue τ f g =ᶠ[𝓝[Icc 0 S] t] g := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hgt)] with x hx
      exact glue_right τ f g hmatch x hx.le
    rw [glue_right τ f' g' hmatch' t hgt.le]
    exact ((hg t ⟨hgt.le,ht.2⟩).mono_of_mem_nhdsWithin hlocal).congr_of_eventuallyEq
      he (glue_right τ f g hmatch t hgt.le)

/-- For the same first-order equation the derivative matching follows from value matching. -/
theorem glue_evolution (S τ : ℝ) (hτ0 : 0 ≤ τ) (hτS : τ ≤ S)
    (f g : ℝ → E) (rhs : ℝ → E → E) (hmatch : f τ=g τ)
    (hf : ∀ t ∈ Icc 0 τ, HasDerivWithinAt f (rhs t (f t)) (Icc 0 τ) t)
    (hg : ∀ t ∈ Icc τ S, HasDerivWithinAt g (rhs t (g t)) (Icc τ S) t)
    (t : ℝ) (ht : t ∈ Icc 0 S) :
    HasDerivWithinAt (glue τ f g) (rhs t (glue τ f g t)) (Icc 0 S) t := by
  have h := glue_hasDerivWithinAt S τ hτ0 hτS f g (fun s => rhs s (f s))
    (fun s => rhs s (g s)) hmatch (congrArg (rhs τ) hmatch) hf hg t ht
  have he : glue τ (fun s => rhs s (f s)) (fun s => rhs s (g s)) t=rhs t (glue τ f g t) := by
    by_cases hx : t ≤ τ <;> simp only [glue, hx, ite_true, ite_false]
  exact he ▸ h

omit [NormedSpace ℝ E] in
/-- Joining the intervals does not change a shared pointwise time-profile bound. -/
theorem glue_weighted_bound (S τ : ℝ) (f g : ℝ → E) (γ : ℝ → ℝ) (C : ℝ)
    (hf : ∀ t ∈ Icc 0 τ, ‖f t‖ ≤ C*γ t)
    (hg : ∀ t ∈ Icc τ S, ‖g t‖ ≤ C*γ t)
    (t : ℝ) (ht : t ∈ Icc 0 S) : ‖glue τ f g t‖ ≤ C*γ t := by
  by_cases h : t ≤ τ
  · rw [glue_left τ f g t h]
    exact hf t ⟨ht.1,h⟩
  · simp only [glue, h, ite_false]
    exact hg t ⟨(not_le.mp h).le,ht.2⟩

end EulerTimeIntervalGlue
