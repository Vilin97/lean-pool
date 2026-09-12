/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.VolterraConvolution
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
public import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevBlocks
import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevLinear
import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevCoefficient
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Normed.Order.Lattice

/-!
# Joining an actual history with a forward elapsed-time path

The two continuous paths have matching traces. This wrapper uses the fixed
linear gluing map, proves the true time derivative through the junction,
and preserves the original ordered-word Sobolev radius.
-/

section

/-! Gluing matching continuous paths is one fixed linear contraction. -/

section

/-! Genuine first-order evolution paths glue through a matching interior trace. -/

@[expose] public section

noncomputable section

namespace EulerTimeIntervalGlue

open Set Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Glue, with branches according to `t ≤ τ`. -/
def glue (τ : ℝ) (f g : ℝ → E) (t : ℝ) : E := if t ≤ τ then f t else g t

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem glue_left (τ : ℝ) (f g : ℝ → E) (t : ℝ) (ht : t ≤ τ) : glue τ f g t=f t := by
  simp only [glue, ht, ite_true]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem glue_right (τ : ℝ) (f g : ℝ → E) (hmatch : f τ = g τ) (t : ℝ) (ht : τ ≤ t) :
    glue τ f g t=g t := by
  rcases ht.eq_or_lt with h | h
  · subst t
    simpa only [glue, le_refl, ite_true] using hmatch
  · simp only [glue, not_le.mpr h, ite_false]

omit [NormedSpace ℝ E] in
theorem glue_continuous (τ : ℝ) (f g : ℝ → E) (hmatch : f τ = g τ)
    (hf : Continuous f) (hg : Continuous g) : Continuous (glue τ f g) := by
  apply Continuous.if_le hf hg continuous_id continuous_const
  intro t ht
  change t=τ at ht
  subst t
  exact hmatch

/-- Matching the value and derivative gives the genuine derivative even at the joining time. -/
theorem glue_hasDerivWithinAt (S τ : ℝ) (hτ0 : 0 ≤ τ) (hτS : τ ≤ S)
    (f g f' g' : ℝ → E) (hmatch : f τ = g τ) (hmatch' : f' τ = g' τ)
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
    (f g : ℝ → E) (rhs : ℝ → E → E) (hmatch : f τ = g τ)
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
    (hf : ∀ t ∈ Icc 0 τ, ‖f t‖ ≤ C * γ t)
    (hg : ∀ t ∈ Icc τ S, ‖g t‖ ≤ C * γ t)
    (t : ℝ) (ht : t ∈ Icc 0 S) : ‖glue τ f g t‖ ≤ C*γ t := by
  by_cases h : t ≤ τ
  · rw [glue_left τ f g t h]
    exact hf t ⟨ht.1,h⟩
  · simp only [glue, h, ite_false]
    exact hg t ⟨(not_le.mp h).le,ht.2⟩

end EulerTimeIntervalGlue

end
end

end

@[expose] public section

noncomputable section

namespace EulerPacketTimePathGluing

open Set EulerTimeIntervalGlue

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

local instance compactInterval (a b : ℝ) : CompactSpace (Icc a b) :=
  isCompact_iff_compactSpace.mp isCompact_Icc

/-- Pair: an abbreviation for `C(Icc (0 : ℝ) τ,E) × C(Icc τ S,E)`. -/
abbrev Pair (S τ : ℝ) (E : Type*) [TopologicalSpace E] :=
  C(Icc (0 : ℝ) τ,E) × C(Icc τ S,E)

/-- Mismatch as an element of `Pair S τ E →L[ℝ] E`. -/
def mismatch (S τ : ℝ) (hτ0 : 0 ≤ τ) (hτS : τ ≤ S) : Pair S τ E →L[ℝ] E :=
  (ContinuousMap.evalCLM ℝ ⟨τ,hτ0,le_rfl⟩).comp
      (ContinuousLinearMap.fst ℝ C(Icc (0 : ℝ) τ,E) C(Icc τ S,E)) -
    (ContinuousMap.evalCLM ℝ ⟨τ,le_rfl,hτS⟩).comp
      (ContinuousLinearMap.snd ℝ C(Icc (0 : ℝ) τ,E) C(Icc τ S,E))

/-- Matching: an abbreviation for `(mismatch (E := E) S τ hτ0 hτS).ker`. -/
abbrev Matching (S τ : ℝ) (hτ0 : 0 ≤ τ) (hτS : τ ≤ S) : Submodule ℝ (Pair S τ E) :=
  (mismatch (E := E) S τ hτ0 hτS).ker

theorem matching_values (S τ : ℝ) (hτ0 : 0 ≤ τ) (hτS : τ ≤ S)
    (u : Matching (E := E) S τ hτ0 hτS) :
    u.val.1 ⟨τ,hτ0,le_rfl⟩=u.val.2 ⟨τ,le_rfl,hτS⟩ := by
  have h : mismatch S τ hτ0 hτS u.val=0 := u.property
  exact sub_eq_zero.mp h

/-- Glue path as an element of `C(Icc (0 : ℝ) S,E)`. -/
def gluePath (S τ : ℝ) (hτ0 : 0 ≤ τ) (hτS : τ ≤ S)
    (u : Matching (E := E) S τ hτ0 hτS) : C(Icc (0 : ℝ) S,E) :=
  ⟨fun t => glue τ (fun r => u.val.1 (projIcc 0 τ hτ0 r))
      (fun r => u.val.2 (projIcc τ S hτS r)) t,
    (glue_continuous τ _ _ (by
      simpa only [Function.comp_def, projIcc_of_mem hτ0 ⟨hτ0,le_rfl⟩,
        projIcc_of_mem hτS ⟨le_rfl,hτS⟩] using matching_values S τ hτ0 hτS u)
      (u.val.1.continuous.comp continuous_projIcc)
      (u.val.2.continuous.comp continuous_projIcc)).comp continuous_subtype_val⟩

theorem gluePath_norm_le (S τ : ℝ) (hτ0 : 0 ≤ τ) (hτS : τ ≤ S)
    (u : Matching (E := E) S τ hτ0 hτS) : ‖gluePath S τ hτ0 hτS u‖ ≤ ‖u‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg u)).2
  intro t
  change ‖glue τ (fun r => u.val.1 (projIcc 0 τ hτ0 r))
    (fun r => u.val.2 (projIcc τ S hτS r)) t‖ ≤ ‖u‖
  by_cases ht : (t : ℝ) ≤ τ
  · rw [glue_left τ _ _ t ht]
    exact (u.val.1.norm_coe_le_norm _).trans (norm_fst_le u.val)
  · simp only [glue, ht, ite_false]
    exact (u.val.2.norm_coe_le_norm _).trans (norm_snd_le u.val)

/-- Glue operator as an element of `Matching (E := E) S τ hτ0 hτS →L[ℝ] C(Icc (0 : ℝ) S,E)`. -/
def glueOperator (S τ : ℝ) (hτ0 : 0 ≤ τ) (hτS : τ ≤ S) :
    Matching (E := E) S τ hτ0 hτS →L[ℝ] C(Icc (0 : ℝ) S,E) :=
  ({ toFun := gluePath S τ hτ0 hτS
     map_add' := by
       intro u v
       ext t
       by_cases ht : (t : ℝ) ≤ τ <;> simp [gluePath, glue, ht]
     map_smul' := by
       intro c u
       ext t
       by_cases ht : (t : ℝ) ≤ τ <;> simp [gluePath, glue, ht] } :
      Matching (E := E) S τ hτ0 hτS →ₗ[ℝ] C(Icc (0 : ℝ) S,E)).mkContinuous
    1 (fun u => by
      change ‖gluePath S τ hτ0 hτS u‖ ≤ 1 * ‖u‖
      simpa only [one_mul] using gluePath_norm_le S τ hτ0 hτS u)

theorem glueOperator_norm_le_one (S τ : ℝ) (hτ0 : 0 ≤ τ) (hτS : τ ≤ S) :
    ‖glueOperator (E := E) S τ hτ0 hτS‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  change ‖gluePath S τ hτ0 hτS u‖ ≤ 1 * ‖u‖
  simpa only [one_mul] using gluePath_norm_le S τ hτ0 hτS u

end EulerPacketTimePathGluing

end
end

end

section

/-!
Smoothness of matching path pairs is derived from smoothness of the two paths.
A fixed linear repair provides the subspace-valued map; it is the identity on
matching data.  The final word estimate uses the exact subtype norm, not the
norm of this auxiliary repair.
-/

section

/-! Matching time paths glue without any external-word or fixed-Sobolev loss. -/

@[expose] public section

noncomputable section

namespace EulerPacketTimePathGluing

open Set EulerTimeIntervalGlue EulerParameterWordGevrey
open scoped ContDiff

variable {X E ι : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

attribute [local instance] compactInterval

@[simp] theorem glueOperator_apply (S τ : ℝ) (hτ0 : 0 ≤ τ) (hτS : τ ≤ S)
    (u : Matching (E := E) S τ hτ0 hτS) :
    glueOperator S τ hτ0 hτS u = gluePath S τ hτ0 hτS u := rfl

theorem gluePath_left (S τ : ℝ) (hτ0 : 0 ≤ τ) (hτS : τ ≤ S)
    (u : Matching (E := E) S τ hτ0 hτS) (t : Icc (0 : ℝ) τ) :
    gluePath S τ hτ0 hτS u ⟨t, t.property.1, t.property.2.trans hτS⟩=u.val.1 t := by
  change glue τ (fun r => u.val.1 (projIcc 0 τ hτ0 r))
    (fun r => u.val.2 (projIcc τ S hτS r)) t = _
  rw [glue_left τ _ _ t t.property.2, projIcc_of_mem hτ0 t.property]

theorem gluePath_right (S τ : ℝ) (hτ0 : 0 ≤ τ) (hτS : τ ≤ S)
    (u : Matching (E := E) S τ hτ0 hτS) (t : Icc τ S) :
    gluePath S τ hτ0 hτS u ⟨t, hτ0.trans t.property.1, t.property.2⟩=u.val.2 t := by
  change glue τ (fun r => u.val.1 (projIcc 0 τ hτ0 r))
    (fun r => u.val.2 (projIcc τ S hτS r)) t = _
  rw [glue_right τ _ _ (by
    simpa only [projIcc_of_mem hτ0 ⟨hτ0,le_rfl⟩,
      projIcc_of_mem hτS ⟨le_rfl,hτS⟩] using matching_values S τ hτ0 hτS u)
    t t.property.1, projIcc_of_mem hτS t.property]

theorem glue_family_contDiff (S τ : ℝ) (hτ0 : 0 ≤ τ) (hτS : τ ≤ S)
    (f : X → Matching (E := E) S τ hτ0 hτS) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun x => gluePath S τ hτ0 hτS (f x)) := by
  simpa only [Function.comp_def, glueOperator_apply] using
    (glueOperator (E := E) S τ hτ0 hτS).contDiff.comp hf

theorem glue_word_derivative (S τ : ℝ) (hτ0 : 0 ≤ τ) (hτS : τ ≤ S)
    (directions : ι → X) (f : X → Matching (E := E) S τ hτ0 hτS)
    (hf : ContDiff ℝ ∞ f) {n : ℕ} (w : Fin n → ι) (x : X) :
    wordDerivative directions (fun y => gluePath S τ hτ0 hτS (f y)) w x =
      gluePath S τ hτ0 hτS (wordDerivative directions f w x) := by
  simpa only [Function.comp_def, glueOperator_apply] using
    wordDerivative_comp_clm directions (glueOperator (E := E) S τ hτ0 hτS) f hf w x

variable [Fintype ι]

theorem glue_word_bound (S τ : ℝ) (hτ0 : 0 ≤ τ) (hτS : τ ≤ S)
    (directions : ι → X) (f : X → Matching (E := E) S τ hτ0 hτS)
    (hf : ContDiff ℝ ∞ f) (n : ℕ) (x : X) :
    wordSum directions (fun y => gluePath S τ hτ0 hτS (f y)) n x ≤
      wordSum directions f n x := by
  have h := wordSum_comp_clm_le directions (glueOperator S τ hτ0 hτS) f hf n x
  exact h.trans ((mul_le_mul_of_nonneg_right
    (glueOperator_norm_le_one S τ hτ0 hτS) (wordSum_nonneg directions f n x)).trans_eq (one_mul _))

/-- Fixed H6 is the specialization q=6; no tensor-to-word conversion occurs. -/
theorem glue_block_bound (S τ : ℝ) (hτ0 : 0 ≤ τ) (hτS : τ ≤ S)
    (directions : ι → X) (q : ℕ) (f : X → Matching (E := E) S τ hτ0 hτS)
    (hf : ContDiff ℝ ∞ f) (n : ℕ) (x : X) :
    block directions q (fun y => gluePath S τ hτ0 hτS (f y)) n x ≤
      block directions q f n x := by
  have h := block_comp_clm_le directions q (glueOperator S τ hτ0 hτS) f hf n x
  exact h.trans ((mul_le_mul_of_nonneg_right
    (glueOperator_norm_le_one S τ hτ0 hτS) (block_nonneg directions q f n x)).trans_eq (one_mul _))

end EulerPacketTimePathGluing

end
end

end

@[expose] public section

noncomputable section

namespace EulerPacketTimePathGluing

open Set Finset EulerParameterWordGevrey
open scoped ContDiff

variable {X E ι : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

attribute [local instance] compactInterval

/-- Repair pair as an element of `Pair S τ E →L[ℝ] Pair S τ E`. -/
def repairPair (S τ : ℝ) (hτ0 : 0 ≤ τ) (hτS : τ ≤ S) : Pair S τ E →L[ℝ] Pair S τ E :=
  (ContinuousLinearMap.fst ℝ C(Icc (0 : ℝ) τ,E) C(Icc τ S,E)).prod
    ((ContinuousLinearMap.snd ℝ C(Icc (0 : ℝ) τ,E) C(Icc τ S,E)) +
      (ContinuousLinearMap.const ℝ (Icc τ S)).comp (mismatch S τ hτ0 hτS))

theorem repairPair_mem (S τ : ℝ) (hτ0 : 0 ≤ τ) (hτS : τ ≤ S) (u : Pair S τ E) :
    repairPair S τ hτ0 hτS u ∈ Matching S τ hτ0 hτS := by
  change u.1 ⟨τ,hτ0,le_rfl⟩-
    (u.2 ⟨τ,le_rfl,hτS⟩+(u.1 ⟨τ,hτ0,le_rfl⟩-u.2 ⟨τ,le_rfl,hτS⟩))=0
  abel

/-- Matching projection, given by `(repairPair S τ hτ0 hτS).codRestrict (Matching S τ hτ0 hτS)
(repairPair_mem S τ hτ0 hτS)`. -/
def matchingProjection (S τ : ℝ) (hτ0 : 0 ≤ τ) (hτS : τ ≤ S) :
    Pair S τ E →L[ℝ] Matching (E := E) S τ hτ0 hτS :=
  (repairPair S τ hτ0 hτS).codRestrict (Matching S τ hτ0 hτS)
    (repairPair_mem S τ hτ0 hτS)

theorem matchingProjection_value (S τ : ℝ) (hτ0 : 0 ≤ τ) (hτS : τ ≤ S)
    (u : Pair S τ E) (hu : u.1 ⟨τ, hτ0, le_rfl⟩ = u.2 ⟨τ, le_rfl, hτS⟩) :
    (matchingProjection S τ hτ0 hτS u).val=u := by
  apply Prod.ext
  · rfl
  · ext t
    change u.2 t+(u.1 ⟨τ,hτ0,le_rfl⟩-u.2 ⟨τ,le_rfl,hτS⟩)=u.2 t
    rw [hu, sub_self, add_zero]

/-- Matching family, defined pointwise by `matchingProjection S τ hτ0 hτS (u x,v x)`. -/
def matchingFamily (S τ : ℝ) (hτ0 : 0 ≤ τ) (hτS : τ ≤ S)
    (u : X → C(Icc (0 : ℝ) τ, E)) (v : X → C(Icc τ S, E)) :
    X → Matching (E := E) S τ hτ0 hτS :=
  fun x => matchingProjection S τ hτ0 hτS (u x,v x)

theorem matchingFamily_contDiff (S τ : ℝ) (hτ0 : 0 ≤ τ) (hτS : τ ≤ S)
    (u : X → C(Icc (0 : ℝ) τ, E)) (v : X → C(Icc τ S, E))
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) :
    ContDiff ℝ ∞ (matchingFamily S τ hτ0 hτS u v) :=
  (matchingProjection (E := E) S τ hτ0 hτS).contDiff.comp (hu.prodMk hv)

variable [Fintype ι]

theorem wordSum_subtype (S τ : ℝ) (hτ0 : 0 ≤ τ) (hτS : τ ≤ S)
    (directions : ι → X) (f : X → Matching (E := E) S τ hτ0 hτS)
    (hf : ContDiff ℝ ∞ f) (n : ℕ) (x : X) :
    wordSum directions (fun y => (f y).val) n x=wordSum directions f n x := by
  unfold wordSum
  apply sum_congr rfl
  intro w _
  have h := wordDerivative_comp_clm directions (Matching (E := E) S τ hτ0 hτS).subtypeL f hf w x
  change wordDerivative directions (fun y => (f y).val) w x=(wordDerivative directions f w x).val
      at h
  rw [h]
  rfl

theorem wordSum_pair_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (directions : ι → X) (f : X → E × F) (hf : ContDiff ℝ ∞ f) (n : ℕ) (x : X) :
    wordSum directions f n x ≤ wordSum directions (fun y => (f y).1) n x +
      wordSum directions (fun y => (f y).2) n x := by
  unfold wordSum
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro w _
  have h₁ := wordDerivative_comp_clm directions (ContinuousLinearMap.fst ℝ E F) f hf w x
  have h₂ := wordDerivative_comp_clm directions (ContinuousLinearMap.snd ℝ E F) f hf w x
  change wordDerivative directions (fun y => (f y).1) w x=(wordDerivative directions f w x).1 at h₁
  change wordDerivative directions (fun y => (f y).2) w x=(wordDerivative directions f w x).2 at h₂
  rw [h₁, h₂, Prod.norm_def]
  exact max_le (le_add_of_nonneg_right (norm_nonneg _)) (le_add_of_nonneg_left (norm_nonneg _))

/-- Independently smooth matching inputs give the same-radius glued block bound. -/
theorem matchingFamily_glue_block (S τ : ℝ) (hτ0 : 0 ≤ τ) (hτS : τ ≤ S)
    (directions : ι → X) (q : ℕ) (u : X → C(Icc (0 : ℝ) τ, E)) (v : X → C(Icc τ S, E))
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (hmatch : ∀ x, u x ⟨τ, hτ0, le_rfl⟩ = v x ⟨τ, le_rfl, hτS⟩) (n : ℕ) (x : X) :
    block directions q (fun y => gluePath S τ hτ0 hτS (matchingFamily S τ hτ0 hτS u v y)) n x ≤
      block directions q u n x+block directions q v n x := by
  let f := matchingFamily S τ hτ0 hτS u v
  have hf : ContDiff ℝ ∞ f := matchingFamily_contDiff S τ hτ0 hτS u v hu hv
  have he : (fun y => (f y).val)=(fun y => (u y,v y)) :=
    funext (fun y => matchingProjection_value S τ hτ0 hτS (u y,v y) (hmatch y))
  apply (glue_block_bound S τ hτ0 hτS directions q f hf n x).trans
  rw [block_eq_sum_levels directions q f hf n x,
    block_eq_sum_levels directions q u hu n x, block_eq_sum_levels directions q v hv n x,
    ← sum_add_distrib]
  apply sum_le_sum
  intro k _
  rw [← wordSum_subtype S τ hτ0 hτS directions f hf, he]
  exact wordSum_pair_le directions (fun y => (u y,v y)) (hu.prodMk hv) _ x

end EulerPacketTimePathGluing

end
end

end

section

/-! The actual affine time shift used by the forward transverse solve. -/

@[expose] public section

noncomputable section

namespace EulerPacketTimePathGluing

open Set EulerParameterWordGevrey
open scoped ContDiff

variable {X E ι : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

attribute [local instance] compactInterval

/-- Elapsed time as an element of `C(Icc τ S, Icc (0 : ℝ) (S-τ))`. -/
def elapsedTime (S τ : ℝ) : C(Icc τ S, Icc (0 : ℝ) (S-τ)) :=
  ⟨fun t => ⟨(t:ℝ)-τ, sub_nonneg.mpr t.property.1, sub_le_sub_right t.property.2 τ⟩,
    (continuous_subtype_val.sub continuous_const).subtype_mk _⟩

/-- Shift path, given by `ContinuousMap.compCLM ℝ E (elapsedTime S τ)`. -/
def shiftPath (S τ : ℝ) : C(Icc (0 : ℝ) (S-τ), E) →L[ℝ] C(Icc τ S,E) :=
  ContinuousMap.compCLM ℝ E (elapsedTime S τ)

theorem shiftPath_apply (S τ : ℝ) (u : C(Icc (0 : ℝ) (S - τ), E)) (t : Icc τ S) :
    shiftPath S τ u t = u ⟨(t:ℝ)-τ,sub_nonneg.mpr t.property.1,sub_le_sub_right t.property.2 τ⟩ :=
        rfl

theorem shiftPath_norm_le_one (S τ : ℝ) : ‖shiftPath (E := E) S τ‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  rw [one_mul]
  apply (ContinuousMap.norm_le _ (norm_nonneg u)).2
  intro t
  exact u.norm_coe_le_norm _

theorem shiftPath_initial (S τ : ℝ) (hτS : τ ≤ S) (u : C(Icc (0 : ℝ) (S - τ), E)) :
    shiftPath S τ u ⟨τ,le_rfl,hτS⟩ = u ⟨0,le_rfl,sub_nonneg.mpr hτS⟩ := by
  simp only [shiftPath_apply, sub_self]

/-- Literal elapsed-time paths retain the same fixed-Sobolev word bound. -/
theorem shiftPath_block_bound [Fintype ι] (S τ : ℝ) (directions : ι → X) (q : ℕ)
    (f : X → C(Icc (0 : ℝ) (S - τ), E)) (hf : ContDiff ℝ ∞ f) (n : ℕ) (x : X) :
    block directions q (fun y => shiftPath S τ (f y)) n x ≤ block directions q f n x := by
  have h := block_comp_clm_le directions q (shiftPath S τ) f hf n x
  exact h.trans ((mul_le_mul_of_nonneg_right (shiftPath_norm_le_one S τ)
    (block_nonneg directions q f n x)).trans_eq (one_mul _))

end EulerPacketTimePathGluing

end
end

end

@[expose] public section

noncomputable section

namespace EulerElapsedTimePathGluing

open Set ContinuousLinearMap EulerTimeIntervalGlue EulerPacketTimePathGluing
  EulerVolterraConvolution EulerParameterWordGevrey
open scoped ContDiff

attribute [local instance] EulerPacketTimePathGluing.compactInterval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (S τ : ℝ) (hτ0 : 0 ≤ τ) (hτS : τ ≤ S)
  (u : C(Icc (0 : ℝ) τ, E)) (v : C(Icc (0 : ℝ) (S - τ), E))
  (hmatch : u ⟨τ, hτ0, le_rfl⟩ = v ⟨0, le_rfl, sub_nonneg.mpr hτS⟩)

/-- Pair, given by `⟨(u,shiftPath S τ v),by change u ⟨τ,hτ0,le_rfl⟩-shiftPath S τ v
⟨τ,le_rfl,hτS⟩ = 0 rw [shiftPath_initial S τ hτS,hmatch,sub_self]⟩`. -/
def pair : Matching (E := E) S τ hτ0 hτS :=
  ⟨(u,shiftPath S τ v),by
    change u ⟨τ,hτ0,le_rfl⟩-shiftPath S τ v ⟨τ,le_rfl,hτS⟩ = 0
    rw [shiftPath_initial S τ hτS,hmatch,sub_self]⟩

/-- Join, given by `gluePath S τ hτ0 hτS (pair S τ hτ0 hτS u v hmatch)`. -/
def join : C(Icc (0 : ℝ) S,E) := gluePath S τ hτ0 hτS (pair S τ hτ0 hτS u v hmatch)

theorem join_eq_projection : join S τ hτ0 hτS u v hmatch =
    gluePath S τ hτ0 hτS (matchingProjection S τ hτ0 hτS (u,shiftPath S τ v)) := by
  apply congrArg (gluePath S τ hτ0 hτS)
  apply Subtype.ext
  exact (matchingProjection_value S τ hτ0 hτS (u,shiftPath S τ v) (by
    change u ⟨τ,hτ0,le_rfl⟩ = shiftPath S τ v ⟨τ,le_rfl,hτS⟩
    rw [shiftPath_initial S τ hτS]
    exact hmatch)).symm

theorem join_extend (t : ℝ) (ht : t ∈ Icc (0 : ℝ) S) :
    extendPath S (hτ0.trans hτS) (join S τ hτ0 hτS u v hmatch) t =
      glue τ (extendPath τ hτ0 u) (fun r => extendPath (S-τ) (sub_nonneg.mpr hτS) v (r-τ)) t := by
  change glue τ (fun r => u (projIcc 0 τ hτ0 r))
      (fun r => shiftPath S τ v (projIcc τ S hτS r)) (projIcc 0 S (hτ0.trans hτS) t) = _
  rw [projIcc_of_mem (hτ0.trans hτS) ht]
  by_cases h : t ≤ τ
  · simp only [glue,h,ite_true]
    rfl
  · have hr : t ∈ Icc τ S := ⟨(not_le.mp h).le,ht.2⟩
    have he : t-τ ∈ Icc (0 : ℝ) (S-τ) :=
      ⟨sub_nonneg.mpr hr.1,sub_le_sub_right hr.2 τ⟩
    simp only [glue,h,ite_false,projIcc_of_mem hτS hr,shiftPath_apply,
      extendPath,projIcc_of_mem (sub_nonneg.mpr hτS) he]

theorem join_left (t : Icc (0 : ℝ) τ) :
    join S τ hτ0 hτS u v hmatch ⟨t,t.property.1,t.property.2.trans hτS⟩ = u t := by
  have he := join_extend S τ hτ0 hτS u v hmatch t ⟨t.property.1,t.property.2.trans hτS⟩
  simpa only [extendPath,projIcc_of_mem (hτ0.trans hτS) ⟨t.property.1,t.property.2.trans hτS⟩,
    glue,t.property.2,ite_true,projIcc_of_mem hτ0 t.property] using he

theorem join_right (t : Icc τ S) :
    join S τ hτ0 hτS u v hmatch ⟨t,hτ0.trans t.property.1,t.property.2⟩ =
      v ⟨(t : ℝ)-τ,sub_nonneg.mpr t.property.1,sub_le_sub_right t.property.2 τ⟩ := by
  have hreal : extendPath τ hτ0 u τ = extendPath (S-τ) (sub_nonneg.mpr hτS) v (τ-τ) := by
    simpa only [extendPath,sub_self,projIcc_of_mem hτ0 ⟨hτ0,le_rfl⟩,
      projIcc_of_mem (sub_nonneg.mpr hτS) ⟨le_rfl,sub_nonneg.mpr hτS⟩] using hmatch
  have he := join_extend S τ hτ0 hτS u v hmatch t ⟨hτ0.trans t.property.1,t.property.2⟩
  rw [glue_right τ _ _ hreal t t.property.1] at he
  simpa only [extendPath,projIcc_of_mem (hτ0.trans hτS) ⟨hτ0.trans t.property.1,t.property.2⟩,
    projIcc_of_mem (sub_nonneg.mpr hτS) ⟨sub_nonneg.mpr t.property.1,sub_le_sub_right t.property.2
        τ⟩] using he

/-- Genuine within-time differentiation holds even at the joining time. -/
theorem join_hasDerivWithinAt
    (u' : C(Icc (0 : ℝ) τ, E)) (v' : C(Icc (0 : ℝ) (S - τ), E))
    (hmatch' : u' ⟨τ, hτ0, le_rfl⟩ = v' ⟨0, le_rfl, sub_nonneg.mpr hτS⟩)
    (hu : ∀ t : Icc (0 : ℝ) τ,
      HasDerivWithinAt (extendPath τ hτ0 u) (u' t) (Icc (0 : ℝ) τ) t)
    (hv : ∀ t : Icc (0 : ℝ) (S-τ),
      HasDerivWithinAt (extendPath (S-τ) (sub_nonneg.mpr hτS) v) (v' t) (Icc (0 : ℝ) (S-τ)) t)
    (t : Icc (0 : ℝ) S) :
    HasDerivWithinAt (extendPath S (hτ0.trans hτS) (join S τ hτ0 hτS u v hmatch))
      (join S τ hτ0 hτS u' v' hmatch' t) (Icc (0 : ℝ) S) t := by
  have hr : MapsTo (fun s : ℝ => s-τ) (Icc τ S) (Icc (0 : ℝ) (S-τ)) :=
    fun s hs => ⟨sub_nonneg.mpr hs.1,sub_le_sub_right hs.2 τ⟩
  have hm : extendPath τ hτ0 u τ = extendPath (S-τ) (sub_nonneg.mpr hτS) v (τ-τ) := by
    simpa only [extendPath,sub_self,projIcc_of_mem hτ0 ⟨hτ0,le_rfl⟩,
      projIcc_of_mem (sub_nonneg.mpr hτS) ⟨le_rfl,sub_nonneg.mpr hτS⟩] using hmatch
  have hm' : extendPath τ hτ0 u' τ = extendPath (S-τ) (sub_nonneg.mpr hτS) v' (τ-τ) := by
    simpa only [extendPath,sub_self,projIcc_of_mem hτ0 ⟨hτ0,le_rfl⟩,
      projIcc_of_mem (sub_nonneg.mpr hτS) ⟨le_rfl,sub_nonneg.mpr hτS⟩] using hmatch'
  have hu' (s : ℝ) (hs : s ∈ Icc (0 : ℝ) τ) :
      HasDerivWithinAt (extendPath τ hτ0 u) (extendPath τ hτ0 u' s) (Icc (0 : ℝ) τ) s := by
    simpa only [extendPath,projIcc_of_mem hτ0 hs] using hu ⟨s,hs⟩
  have hv' (s : ℝ) (hs : s ∈ Icc τ S) :
      HasDerivWithinAt (fun r => extendPath (S-τ) (sub_nonneg.mpr hτS) v (r-τ))
        (extendPath (S-τ) (sub_nonneg.mpr hτS) v' (s-τ)) (Icc τ S) s := by
    have hd := (hv ⟨s-τ,hr hs⟩).scomp s ((hasDerivAt_id s).sub_const τ).hasDerivWithinAt hr
    simpa only [one_smul,Function.comp_def,id_eq,extendPath,
      projIcc_of_mem (sub_nonneg.mpr hτS) (hr hs)] using hd
  have hd := glue_hasDerivWithinAt S τ hτ0 hτS (extendPath τ hτ0 u)
    (fun r => extendPath (S-τ) (sub_nonneg.mpr hτS) v (r-τ))
    (extendPath τ hτ0 u') (fun r => extendPath (S-τ) (sub_nonneg.mpr hτS) v' (r-τ))
    hm hm' hu' hv' t t.property
  rw [← join_extend S τ hτ0 hτS u' v' hmatch' t t.property] at hd
  simpa only [extendPath,projIcc_of_mem (hτ0.trans hτS) t.property] using
    hd.congr_of_mem (fun s hs => join_extend S τ hτ0 hτS u v hmatch s hs) t.property

section Parameter

variable {X ι : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [Fintype ι]
  (p : X → C(Icc (0 : ℝ) τ, E)) (q : X → C(Icc (0 : ℝ) (S - τ), E))
  (hp : ContDiff ℝ ∞ p) (hq : ContDiff ℝ ∞ q)
  (hm : ∀ x, p x ⟨τ, hτ0, le_rfl⟩ = q x ⟨0, le_rfl, sub_nonneg.mpr hτS⟩)

include hp hq hm in
theorem join_contDiff : ContDiff ℝ ∞ (fun x => join S τ hτ0 hτS (p x) (q x) (hm x)) := by
  simp_rw [join_eq_projection]
  exact (glueOperator (E := E) S τ hτ0 hτS).contDiff.comp
    (matchingFamily_contDiff S τ hτ0 hτS p (fun x => shiftPath S τ (q x))
      hp ((shiftPath (E := E) S τ).contDiff.comp hq))

include hp hq hm in
/-- The fixed Sobolev block is bounded by the sum of the input blocks, with
no new radius or derivative factor from the time junction. -/
theorem join_block_bound (directions : ι → X) (k n : ℕ) (x : X) :
    block directions k (fun y => join S τ hτ0 hτS (p y) (q y) (hm y)) n x ≤
      block directions k p n x+block directions k q n x := by
  simp_rw [join_eq_projection]
  have hm' (y) : p y ⟨τ,hτ0,le_rfl⟩ = shiftPath S τ (q y) ⟨τ,le_rfl,hτS⟩ := by
    rw [shiftPath_initial S τ hτS]
    exact hm y
  have hb := matchingFamily_glue_block S τ hτ0 hτS directions k p (fun y => shiftPath S τ (q y))
    hp ((shiftPath (E := E) S τ).contDiff.comp hq) hm' n x
  exact hb.trans (by
    gcongr
    exact shiftPath_block_bound S τ directions k q hq n x)

end Parameter
end EulerElapsedTimePathGluing
