/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.ProbeMax

/-! # Probe Envelope -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

open MeasureTheory
open scoped BigOperators ENNReal

/-!
# Concrete finite-probe envelope

This file packages the deterministic finite-basis envelope used by the
quenched bad-pair estimates.
-/

noncomputable section

/-- Dimension-only finite-probe constant in the quenched envelope. -/
noncomputable def quenchedProbeEnvelopeConst (d : ℕ) : ℝ :=
  4 * (Fintype.card (BlockCoord d) : ℝ) *
    (Fintype.card (NormalizedProbeIndex d) : ℝ)

theorem quenchedProbeEnvelopeConst_nonneg (d : ℕ) :
    0 ≤ quenchedProbeEnvelopeConst d := by
  unfold quenchedProbeEnvelopeConst
  positivity

theorem quenchedProbeEnvelopeConst_pos (d : ℕ) [NeZero d] :
    0 < quenchedProbeEnvelopeConst d := by
  classical
  unfold quenchedProbeEnvelopeConst
  have hcoord : 0 < (Fintype.card (BlockCoord d) : ℝ) := by
    exact_mod_cast
      (Fintype.card_pos_iff.mpr (inferInstance : Nonempty (BlockCoord d)))
  have hprobe : 0 < (Fintype.card (NormalizedProbeIndex d) : ℝ) := by
    let α : BlockCoord d := Classical.choice (inferInstance : Nonempty (BlockCoord d))
    exact_mod_cast
      (Fintype.card_pos_iff.mpr
        (show Nonempty (NormalizedProbeIndex d) from
          ⟨(α, α, NormalizedProbeKind.coord)⟩))
  positivity

/-- The finite-probe envelope controlling all localized unit-vector responses. -/
noncomputable def quenchedProbeEnvelope
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P)
    (hStruct : Ch04.RestrictionStructuralLaw P)
    (m n : ℕ) : RegCoeffField d → ℝ :=
  fun a =>
    quenchedProbeEnvelopeConst d *
      localizedNormalizedProbeJMax hP hStruct m n a

theorem localizedLimitNormalizedJMax_le_quenchedProbeEnvelope_ae
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct)
    {m n : ℕ} (hnm : n ≤ m)
    (e : FullBlockVec d) (he : dotProduct e e ≤ 1) :
    (localizedLimitNormalizedJMax hP hStruct m n e) ≤ᵐ[P]
      quenchedProbeEnvelope hP hStruct m n := by
  have hraw :=
    localizedLimitNormalizedJMax_le_normalizedProbeJMax_ae
      hP hStruct hΓ hnm e he
  filter_upwards [hraw] with a hraw_a
  calc
    localizedLimitNormalizedJMax hP hStruct m n e a
        ≤ (4 * (Fintype.card (BlockCoord d) : ℝ) *
            (Fintype.card (NormalizedProbeIndex d) : ℝ)) *
          localizedNormalizedProbeJMax hP hStruct m n a := hraw_a
    _ = quenchedProbeEnvelope hP hStruct m n a := by
        simp [quenchedProbeEnvelope, quenchedProbeEnvelopeConst]

end

end Section57
end Ch05
end Book
end Homogenization
