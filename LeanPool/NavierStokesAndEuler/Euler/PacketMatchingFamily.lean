/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketTimeWordGluing
public import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevCoefficient

@[expose] public section

/-!
Smoothness of matching path pairs is derived from smoothness of the two paths.
A fixed linear repair provides the subspace-valued map; it is the identity on
matching data.  The final word estimate uses the exact subtype norm, not the
norm of this auxiliary repair.
-/

noncomputable section

namespace EulerPacketTimePathGluing

open Set Finset EulerParameterWordGevrey
open scoped ContDiff

variable {X E ι : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

attribute [local instance] compactInterval

def repairPair (S τ : ℝ) (hτ0 : 0 ≤ τ) (hτS : τ ≤ S) : Pair S τ E →L[ℝ] Pair S τ E :=
  (ContinuousLinearMap.fst ℝ C(Icc (0 : ℝ) τ,E) C(Icc τ S,E)).prod
    ((ContinuousLinearMap.snd ℝ C(Icc (0 : ℝ) τ,E) C(Icc τ S,E))+
      (ContinuousLinearMap.const ℝ (Icc τ S)).comp (mismatch S τ hτ0 hτS))

theorem repairPair_mem (S τ : ℝ) (hτ0 : 0 ≤ τ) (hτS : τ ≤ S) (u : Pair S τ E) :
    repairPair S τ hτ0 hτS u ∈ Matching S τ hτ0 hτS := by
  change u.1 ⟨τ,hτ0,le_rfl⟩-
    (u.2 ⟨τ,le_rfl,hτS⟩+(u.1 ⟨τ,hτ0,le_rfl⟩-u.2 ⟨τ,le_rfl,hτS⟩))=0
  abel

def matchingProjection (S τ : ℝ) (hτ0 : 0 ≤ τ) (hτS : τ ≤ S) :
    Pair S τ E →L[ℝ] Matching (E := E) S τ hτ0 hτS :=
  (repairPair S τ hτ0 hτS).codRestrict (Matching S τ hτ0 hτS)
    (repairPair_mem S τ hτ0 hτS)

theorem matchingProjection_value (S τ : ℝ) (hτ0 : 0 ≤ τ) (hτS : τ ≤ S)
    (u : Pair S τ E) (hu : u.1 ⟨τ,hτ0,le_rfl⟩=u.2 ⟨τ,le_rfl,hτS⟩) :
    (matchingProjection S τ hτ0 hτS u).val=u := by
  apply Prod.ext
  · rfl
  · ext t
    change u.2 t+(u.1 ⟨τ,hτ0,le_rfl⟩-u.2 ⟨τ,le_rfl,hτS⟩)=u.2 t
    rw [hu, sub_self, add_zero]

def matchingFamily (S τ : ℝ) (hτ0 : 0 ≤ τ) (hτS : τ ≤ S)
    (u : X → C(Icc (0 : ℝ) τ,E)) (v : X → C(Icc τ S,E)) :
    X → Matching (E := E) S τ hτ0 hτS :=
  fun x => matchingProjection S τ hτ0 hτS (u x,v x)

theorem matchingFamily_contDiff (S τ : ℝ) (hτ0 : 0 ≤ τ) (hτS : τ ≤ S)
    (u : X → C(Icc (0 : ℝ) τ,E)) (v : X → C(Icc τ S,E))
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
    wordSum directions f n x ≤ wordSum directions (fun y => (f y).1) n x+
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
    (directions : ι → X) (q : ℕ) (u : X → C(Icc (0 : ℝ) τ,E)) (v : X → C(Icc τ S,E))
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (hmatch : ∀ x, u x ⟨τ,hτ0,le_rfl⟩=v x ⟨τ,le_rfl,hτS⟩) (n : ℕ) (x : X) :
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
