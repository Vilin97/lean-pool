/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketKnownPieceBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketProfileCoarseBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderBoundTransfer

@[expose] public section

/-! Uniform bounds on the actual finite velocity jets, including the terminal corrector. -/

noncomputable section

namespace EulerPacketCylinderField

open Set EulerSmoothLimit EulerPacketPointJets EulerPacketProfileRecursion
  EulerPacketTimeProfile EulerPacketShiftArithmetic

theorem KnownPiece.profile_le_coarse {K : Type*} [TopologicalSpace K]
    (k : KnownPiece) (S : Scales K) (i : ℕ) (hi : 1 ≤ i) (t : K) :
    k.profile S i t ≤ S.H0^(2*i) := by
  apply (k.profile_le_envelope S i t).trans
  cases k <;> first | exact S.high_le_coarse i hi t | exact S.mean_le_coarse i t

namespace PrefixBound

variable {P T : ℝ} [Fact (0 < P)] {p : ℕ} {a : ℕ → Profile}
  {F : PrefixFields P T p a} {hT : 0 ≤ T} {S : Scales (Icc (0 : ℝ) T)} {R : ℝ}
  (B : PrefixBound F hT S R)

include B

theorem piece_unnormalized (hR : 1 ≤ R) (k : KnownPiece) (i : ℕ) (hi : 1 ≤ i) :
    (F.piece k i).WordBound 6 R (S.H0^(2*i)) (highShift i) := by
  have h := (B.piece (zero_le_one.trans hR) k i).remove_profile hT (k.profile S i) (k.profile_pos S
    i)
    (S.H0^(2*i)) (pow_nonneg S.H0_pos.le _) (k.profile_le_coarse S i hi)
  have h' : (F.piece k i).WordBound 6 R (S.H0^(2*i)) (k.shift i) := by simpa only [mul_one] using h
  exact h'.mono_shift hR (pow_nonneg S.H0_pos.le _) (k.shift_le_high i)

theorem knownJet_bound (O : Operators) (hp : 2 ≤ p) (hR : 1 ≤ R)
    (hc : (a 0).corrector = 0) (hb : (a 1).mean = 0) (i : ℕ) :
    (F.knownJet O (by omega) i).field.WordBound 6 R (3*S.H0^(2*i)) (highShift i) := by
  let J := F.knownJet O (by omega) i
  by_cases hi0 : i = 0
  · subst i
    have hz : ∀ (t : Icc (0 : ℝ) T) x θ, J.raw (t,(x,θ)) = 0 := by
      intro t x θ
      have hj := (J.value_eq t x θ).symm
      change J.raw (t,(x,θ)) = _ at hj
      rw [hj]
      simp [knownJets,history,velocityJet,show 0 < p by omega]
    exact (Field.wordBound_of_zero J.field hz 6 R (highShift 0)).mono_amplitude
      (zero_le_one.trans hR) (by norm_num : (0 : ℝ) ≤ 3*S.H0^(2*0))
  · have hi : 1 ≤ i := by omega
    have hhi := B.piece_unnormalized hR .high i hi
    have hme := B.piece_unnormalized hR .mean i hi
    have hco := B.piece_unnormalized hR .corrector i hi
    have hs := (hhi.add hme).add hco
    have he : S.H0^(2*i)+S.H0^(2*i)+S.H0^(2*i) = 3*S.H0^(2*i) := by ring
    rw [he] at hs
    apply hs.of_raw_eq J.field
    intro t x θ
    exact (J.value_eq t x θ).symm.trans
      (congrArg Prod.fst (knownJets_eq_pieces O p hp a hc hb (t,(x,θ)) i))

end PrefixBound
end EulerPacketCylinderField
