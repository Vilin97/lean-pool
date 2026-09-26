/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.TanTwoTheta.BoundedOffDiagonalHalfLine
public import LeanPool.DavisKahan.DavisKahan.SpectralTheory.AbstractSpectrum

/-! # Bounded Off Diagonal Ordered Sets -/

@[expose] public section

open TauCeti.DavisKahan.Sylvester

/-!
# Ordered spectral sets and separating half-line centers

This leaf isolates the order-theoretic step needed by the bounded
`tangent-two-theta` theorem.  If every point of a nonempty bounded-above set
`s` lies at least `d` below every point of `t`, then `sSup s` is a separating
center: `s` lies in its lower half-line and `t` lies above the center plus
`d`.

Applied to `OrderedInternalGap`, this produces one of the two possible
oriented half-line configurations.  Subsequent leaves transport these
restricted spectral sets to the compressed self-adjoint blocks and handle the
reverse orientation.
-/

namespace TauCeti
namespace DavisKahanExt

open DavisKahan.Foundation

/-- A nonempty bounded-above ordered lower set admits a separating supremum
center. -/
theorem exists_halfLine_center_of_ordered_sets
    {s t : Set ℝ} {d : ℝ}
    (hs : s.Nonempty) (hs_bdd : BddAbove s)
    (hordered : ∀ a ∈ s, ∀ b ∈ t, a + d ≤ b) :
    ∃ c : ℝ, s ⊆ Set.Iic c ∧ t ⊆ Set.Ici (c + d) := by
  refine ⟨sSup s, ?_, ?_⟩
  · intro a ha
    exact le_csSup hs_bdd ha
  · intro b hb
    have hsup : sSup s ≤ b - d := by
      apply csSup_le hs
      intro a ha
      have hab := hordered a ha b hb
      linarith
    calc
      sSup s + d ≤ (b - d) + d := by
        simpa [add_comm] using add_le_add_right hsup d
      _ = b := sub_add_cancel b d

/-- Ordered separation of two restricted spectra supplies a common separating
half-line center once the lower restricted spectrum is nonempty and bounded
above. -/
theorem OrderedSpectraSeparated.exists_halfLine_center
    {𝕜 E F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    {A : E →L[𝕜] E} {U : Submodule 𝕜 E}
    {B : F →L[𝕜] F} {V : Submodule 𝕜 F} {d : ℝ}
    (h : OrderedSpectraSeparated A U B V d)
    (hne : (restrictedSpectrum A U).Nonempty)
    (hbdd : BddAbove (restrictedSpectrum A U)) :
    ∃ c : ℝ,
      restrictedSpectrum A U ⊆ Set.Iic c ∧
      restrictedSpectrum B V ⊆ Set.Ici (c + d) := by
  exact exists_halfLine_center_of_ordered_sets hne hbdd h.2.2

/-- An ordered internal gap gives one of the two oriented spectral half-line
configurations.  The hypotheses are stated for both restricted spectra so the
result remains explicit about the degenerate-subspace cases. -/
theorem _root_.TauCeti.DavisKahan.Foundation.OrderedInternalGap.exists_oriented_halfLine_center
    {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    {A : E →L[𝕜] E} {U : Submodule 𝕜 E} {d : ℝ}
    (hgap : OrderedInternalGap A U d)
    (hU_ne : (restrictedSpectrum A U).Nonempty)
    (hU_bdd : BddAbove (restrictedSpectrum A U))
    (hUc_ne : (restrictedSpectrum A Uᗮ).Nonempty)
    (hUc_bdd : BddAbove (restrictedSpectrum A Uᗮ)) :
    (∃ c : ℝ,
      restrictedSpectrum A U ⊆ Set.Iic c ∧
      restrictedSpectrum A Uᗮ ⊆ Set.Ici (c + d)) ∨
    (∃ c : ℝ,
      restrictedSpectrum A Uᗮ ⊆ Set.Iic c ∧
      restrictedSpectrum A U ⊆ Set.Ici (c + d)) := by
  rcases hgap with hforward | hreverse
  · rcases hforward with ⟨_, _, hordered⟩
    exact Or.inl
      (exists_halfLine_center_of_ordered_sets hU_ne hU_bdd hordered)
  · rcases hreverse with ⟨_, _, hordered⟩
    exact Or.inr
      (exists_halfLine_center_of_ordered_sets hUc_ne hUc_bdd hordered)

end DavisKahanExt
end TauCeti
