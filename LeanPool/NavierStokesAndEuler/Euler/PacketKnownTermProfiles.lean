/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketKnownDecomposition
public import LeanPool.NavierStokesAndEuler.Euler.PacketKnownPieceScales

/-! The time-profile inequalities for every surviving term of the mean and high forces. -/

@[expose] public section


namespace EulerPacketCylinderField.KnownTerm

open EulerPacketTimeProfile

variable {K : Type*} [TopologicalSpace K]

/-- Profile fits as an element of `Prop`. -/
def ProfileFits (k : KnownTerm) (S : Scales K) (p i j : ℕ) (b : C(K, ℝ)) : Prop :=
  match k with
  | .previousLinear | .previousPressure => ∀ t, S.high (p-1) t ≤ b t
  | .slow l r => i+j=p → l.active p i → r.active p j →
      ∀ t, l.profile S i t*r.profile S j t ≤ b t
  | .fastMeanHigh => i+j=p+1 → KnownPiece.mean.active p i → KnownPiece.high.active p j →
      ∀ t, KnownPiece.mean.profile S i t*KnownPiece.high.profile S j t ≤ b t
  | .fastMeanCorrector => i+j=p+1 → KnownPiece.mean.active p i → KnownPiece.corrector.active p j →
      ∀ t, KnownPiece.mean.profile S i t*KnownPiece.corrector.profile S j t ≤ b t
  | .fastCorrectorHigh => i+j=p+1 → KnownPiece.corrector.active p i → KnownPiece.high.active p j →
      ∀ t, KnownPiece.corrector.profile S i t*KnownPiece.high.profile S j t ≤ b t
  | .fastCorrectorCorrector =>
      i+j=p+1 → KnownPiece.corrector.active p i → KnownPiece.corrector.active p j →
      ∀ t, KnownPiece.corrector.profile S i t*KnownPiece.corrector.profile S j t ≤ b t

theorem mean_profile_fits (k : KnownTerm) (S : Scales K) (p i j : ℕ)
    (hp : 2 ≤ p) (hk : k.zeroMean = false) : k.ProfileFits S p i j (S.mean p) := by
  cases k with
  | previousLinear => exact S.previous_linear_mean_bound p hp
  | previousPressure => exact S.previous_linear_mean_bound p hp
  | slow l r =>
      intro hn hl hr
      exact KnownPiece.slow_profile_mean l r S i j p
        (l.active_one_le p i hl) (r.active_one_le p j hr) hn
  | fastMeanHigh => simp [zeroMean] at hk
  | fastMeanCorrector => simp [zeroMean] at hk
  | fastCorrectorHigh =>
      intro hn hl hr
      exact KnownPiece.fast_corrector_profile_mean .high S i j p (by decide) hl.1 hr.1 hn
  | fastCorrectorCorrector =>
      intro hn hl hr
      exact KnownPiece.fast_corrector_profile_mean .corrector S i j p (by decide) hl.1
        (KnownPiece.active_one_le .corrector p j hr) hn

theorem high_profile_fits (k : KnownTerm) (S : Scales K) (p i j : ℕ)
    (hk : k.meanOnly = false) : k.ProfileFits S p i j (S.high p) := by
  cases k with
  | previousLinear => exact S.high_mono (Nat.sub_le p 1)
  | previousPressure => exact S.high_mono (Nat.sub_le p 1)
  | slow l r =>
      have hnot : ¬ (l = .mean ∧ r = .mean) := by
        rintro ⟨rfl,rfl⟩
        simp [meanOnly] at hk
      intro hn hl hr
      exact KnownPiece.slow_profile_high l r S i j p
        (l.active_one_le p i hl) (r.active_one_le p j hr) hn hnot
  | fastMeanHigh =>
      intro hn hl hr
      exact KnownPiece.fast_mean_profile_high .high S i j p (by decide)
        (KnownPiece.active_one_le .mean p i hl) hr.1 hn
  | fastMeanCorrector =>
      intro hn hl hr
      exact KnownPiece.fast_mean_profile_high .corrector S i j p (by decide)
        (KnownPiece.active_one_le .mean p i hl) (KnownPiece.active_one_le .corrector p j hr) hn
  | fastCorrectorHigh =>
      intro hn hl hr
      exact KnownPiece.fast_corrector_profile_high .high S i j p (by decide) hl.1 hr.1 hn
  | fastCorrectorCorrector =>
      intro hn hl hr
      exact KnownPiece.fast_corrector_profile_high .corrector S i j p (by decide) hl.1
        (KnownPiece.active_one_le .corrector p j hr) hn

end EulerPacketCylinderField.KnownTerm
