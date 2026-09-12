/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketKnownPieceScales
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderFieldWeight
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderFieldUnique
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderHighPartBounds
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderWeightedLinear

/-! Quantitative bounds on the actual masked fields used in the known forcing. -/

@[expose] public section


noncomputable section

namespace EulerPacketCylinderField

open Set EulerSmoothLimit EulerPacketPointJets EulerPacketProfileRecursion
  EulerPacketTimeProfile EulerPacketShiftArithmetic

variable {P T : ℝ} [Fact (0 < P)] {p : ℕ} {a : ℕ → Profile}

/-- Prefix bound data, collecting `high`, `mean`, `corrector`. -/
structure PrefixBound (F : PrefixFields P T p a) (hT : 0 ≤ T)
    (S : Scales (Icc (0 : ℝ) T)) (R : ℝ) : Prop where
  high : ∀ i (hi : i < p), 1 ≤ i →
    ((F.high i hi).normalized hT (S.high i) (S.high_pos i)).WordBound 6 R 1 (highShift i)
  mean : ∀ i (hi : i < p), 2 ≤ i →
    ((F.mean i hi).normalized hT (S.mean i) (S.mean_pos i)).WordBound 6 R 1 (meanShift i)
  corrector : ∀ i (hi : i < p), 1 ≤ i →
    ((F.corrector i hi).normalized hT (S.high i) (S.high_pos i)).WordBound 6 R 1 (highShift i)

namespace PrefixBound

variable {F : PrefixFields P T p a} {hT : 0 ≤ T}
  {S : Scales (Icc (0 : ℝ) T)} {R : ℝ} (B : PrefixBound F hT S R)

include B

theorem piece (hR : 0 ≤ R) (k : KnownPiece) (i : ℕ) :
    ((F.piece k i).normalized hT (k.profile S i) (k.profile_pos S i)).WordBound 6 R 1 (k.shift i)
        := by
  by_cases hi : k.active p i
  · cases k with
    | high =>
      have hb := B.high i hi.2 hi.1
      apply hb.of_path_eq
      apply Field.path_eq_of_raw_eq
      intro t x θ
      change (S.high i (projIcc 0 T hT t))⁻¹ • (a i).high (t,(x,θ)) =
        (S.high i (projIcc 0 T hT t))⁻¹ • KnownPiece.high.raw p a i (t,(x,θ))
      simp only [KnownPiece.raw,hi,ite_true]
    | mean =>
      have hb := B.mean i hi.2 hi.1
      apply hb.of_path_eq
      apply Field.path_eq_of_raw_eq
      intro t x θ
      change (S.mean i (projIcc 0 T hT t))⁻¹ • (a i).mean (t,(x,θ)) =
        (S.mean i (projIcc 0 T hT t))⁻¹ • KnownPiece.mean.raw p a i (t,(x,θ))
      simp only [KnownPiece.raw,hi,ite_true]
    | corrector =>
      have hip : i-1 < p := by simp only [KnownPiece.active] at hi; omega
      have hi1 : 1 ≤ i-1 := by simp only [KnownPiece.active] at hi; omega
      have hb := B.corrector (i-1) hip hi1
      apply hb.of_path_eq
      apply Field.path_eq_of_raw_eq
      intro t x θ
      change (S.high (i-1) (projIcc 0 T hT t))⁻¹ • (a (i-1)).corrector (t,(x,θ)) =
        (S.high (i-1) (projIcc 0 T hT t))⁻¹ • KnownPiece.corrector.raw p a i (t,(x,θ))
      simp only [KnownPiece.raw,hi,ite_true]
  · have hz : ∀ (t : Icc (0 : ℝ) T) x θ, k.raw p a i (t,(x,θ)) = 0 := by
      intro t x θ
      simp only [KnownPiece.raw,hi,ite_false,Pi.zero_apply]
    exact (Field.wordBound_normalized_of_zero (F.piece k i) hz hT
      (k.profile S i) (k.profile_pos S i) 6 R (k.shift i)).mono_amplitude hR zero_le_one

theorem pieceJet (hR : 0 ≤ R) (O : Operators) (k : KnownPiece) (i : ℕ) :
    ((F.pieceJet O k i).field.normalized hT (k.profile S i) (k.profile_pos S i)).WordBound 6 R 1
      (k.shift i) := B.piece hR k i

end PrefixBound
end EulerPacketCylinderField
