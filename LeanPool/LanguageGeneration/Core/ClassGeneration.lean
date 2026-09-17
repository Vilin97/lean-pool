/-
Copyright (c) 2026 Shuangping Li, Peng Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuangping Li, Peng Zhang
-/
import LeanPool.LanguageGeneration.Core.GenericGeneration

/-!
# Generation properties for classes of languages

Paper-independent quantifier patterns for generation from positive data over
an arbitrary example type.
-/

namespace GenLimit.Generic

/-- Every language in the class is infinite. -/
def UUS (H : LanguageClass α) : Prop :=
  ∀ L, L ∈ H → L.Infinite

/-- `gen` eventually generates fresh elements of every presented target. -/
def IsLimitGenerator (gen : Generator α) (H : LanguageClass α) : Prop :=
  ∀ L, L ∈ H → ∀ stream : Stream α, Presents stream L →
    ∃ T, ∀ s, T ≤ s → CorrectAt gen L stream s

/-- Generation in the limit from positive presentations. -/
def GeneratableInLimit (H : LanguageClass α) : Prop :=
  ∃ gen : Generator α, IsLimitGenerator gen H

/-- `d` is a uniform distinct-sample threshold for `gen` on `H`. -/
def IsUniformGeneratorAt
    (gen : Generator α) (H : LanguageClass α) (d : ℕ) : Prop :=
  ∀ L, L ∈ H → ∀ stream : Stream α, StreamIn stream L →
    ∀ t, (sample stream t).card = d →
      ∀ s, t ≤ s → CorrectAt gen L stream s

/-- One generator and one threshold work uniformly over the class. -/
def UniformlyGeneratable (H : LanguageClass α) : Prop :=
  ∃ gen : Generator α, ∃ d : ℕ, IsUniformGeneratorAt gen H d

/-- One generator works with a target-dependent distinct-sample threshold. -/
def IsNonuniformGenerator (gen : Generator α) (H : LanguageClass α) : Prop :=
  ∀ L, L ∈ H → ∃ d : ℕ,
    ∀ stream : Stream α, StreamIn stream L →
      ∀ t, (sample stream t).card = d →
        ∀ s, t ≤ s → CorrectAt gen L stream s

/-- One generator works with target-dependent thresholds. -/
def NonuniformlyGeneratable (H : LanguageClass α) : Prop :=
  ∃ gen : Generator α, IsNonuniformGenerator gen H

theorem uniform_implies_nonuniform
    {H : LanguageClass α} (h : UniformlyGeneratable H) :
    NonuniformlyGeneratable H := by
  obtain ⟨G, d, hG⟩ := h
  refine ⟨G, ?_⟩
  intro L hLH
  exact ⟨d, hG L hLH⟩

theorem nonuniform_implies_limit
    {H : LanguageClass α} (hUUS : UUS H)
    (h : NonuniformlyGeneratable H) :
    GeneratableInLimit H := by
  obtain ⟨G, hG⟩ := h
  refine ⟨G, ?_⟩
  intro L hLH stream hP
  obtain ⟨d, hd⟩ := hG L hLH
  obtain ⟨T, hT⟩ :=
    exists_sample_card_eq_of_presents_infinite hP (hUUS L hLH) d
  refine ⟨T, ?_⟩
  intro s hTs
  exact hd stream (streamIn_of_presents hP) T hT s hTs

theorem uniform_implies_limit
    {H : LanguageClass α} (hUUS : UUS H)
    (h : UniformlyGeneratable H) :
    GeneratableInLimit H :=
  nonuniform_implies_limit hUUS (uniform_implies_nonuniform h)

end GenLimit.Generic
