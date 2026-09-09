/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketKnownPieces
public import LeanPool.NavierStokesAndEuler.Euler.PacketTimeProfiles
public import LeanPool.NavierStokesAndEuler.Euler.PacketShiftArithmetic

/-! Uniform shifts and actual time profiles for the three known pieces of every grade. -/

@[expose] public section


noncomputable section

namespace EulerPacketCylinderField.KnownPiece

open EulerPacketTimeProfile EulerPacketShiftArithmetic

/-- Shift as an element of `ℕ`. -/
def shift (k : KnownPiece) (i : ℕ) : ℕ :=
  match k with
  | .high => highShift i
  | .mean => meanShift i
  | .corrector => highShift (i-1)

variable {K : Type*} [TopologicalSpace K]

/-- Profile as an element of `C(K,ℝ)`. -/
def profile (k : KnownPiece) (S : Scales K) (i : ℕ) : C(K,ℝ) :=
  match k with
  | .high => S.high i
  | .mean => S.mean i
  | .corrector => S.high (i-1)

/-- Envelope as an element of `C(K,ℝ)`. -/
def envelope (k : KnownPiece) (S : Scales K) (i : ℕ) : C(K,ℝ) :=
  match k with
  | .high | .corrector => S.high i
  | .mean => S.mean i

theorem profile_pos (k : KnownPiece) (S : Scales K) (i : ℕ) (t : K) :
    0 < k.profile S i t := by
  cases k <;> first | exact S.high_pos _ _ | exact S.mean_pos _ _

theorem envelope_pos (k : KnownPiece) (S : Scales K) (i : ℕ) (t : K) :
    0 < k.envelope S i t := by
  cases k <;> first | exact S.high_pos _ _ | exact S.mean_pos _ _

theorem profile_le_envelope (k : KnownPiece) (S : Scales K) (i : ℕ) (t : K) :
    k.profile S i t ≤ k.envelope S i t := by
  cases k
  · exact le_rfl
  · exact le_rfl
  · exact S.high_mono (Nat.sub_le i 1) t

theorem profile_le_high (k : KnownPiece) (S : Scales K) (i : ℕ) (hk : k ≠ .mean) (t : K) :
    k.profile S i t ≤ S.high i t := by
  cases k
  · exact le_rfl
  · exact (hk rfl).elim
  · exact S.high_mono (Nat.sub_le i 1) t

theorem active_one_le (k : KnownPiece) (p i : ℕ) (hi : k.active p i) : 1 ≤ i := by
  cases k <;> simp only [active] at hi <;> omega

theorem shift_le_high (k : KnownPiece) (i : ℕ) : k.shift i ≤ highShift i := by
  cases k <;> dsimp only [shift,highShift,meanShift] <;> omega

theorem slow_shift_room (k l : KnownPiece) (i j p : ℕ)
    (hi : 1 ≤ i) (hj : 1 ≤ j) (hij : i + j = p) :
    k.shift i+l.shift j+1 < meanForceShift p := by
  have hk := k.shift_le_high i
  have hl := l.shift_le_high j
  have hs := slow_high_high_room i j p hi hj hij
  omega

theorem slow_shift_room_high (k l : KnownPiece) (i j p : ℕ)
    (hi : 1 ≤ i) (hj : 1 ≤ j) (hij : i + j = p) :
    k.shift i+l.shift j+1 < highForceShift p :=
  lt_of_lt_of_le (slow_shift_room k l i j p hi hj hij) (mean_force_le_high_force p)

theorem fast_mean_shift_room (l : KnownPiece) (i j p : ℕ)
    (hi : 2 ≤ i) (hj : 1 ≤ j) (hij : i + j = p + 1) :
    KnownPiece.mean.shift i+l.shift j+1 < highForceShift p := by
  have hl := l.shift_le_high j
  have hs := fast_mean_high_room i j p hi hj hij
  change meanShift i+_+1 < _
  omega

theorem fast_corrector_shift_room (l : KnownPiece) (i j p : ℕ)
    (hi : 2 ≤ i) (hj : 1 ≤ j) (hij : i + j = p + 1) :
    KnownPiece.corrector.shift i+l.shift j+1 < meanForceShift p := by
  have hl := l.shift_le_high j
  have hs := fast_corrector_high_room i j p hi hj hij
  change highShift (i-1)+_+1 < _
  omega

private theorem envelope_slow_mean (k l : KnownPiece) (S : Scales K) (i j p : ℕ)
    (hi : 1 ≤ i) (hj : 1 ≤ j) (hij : i + j = p) (t : K) :
    k.envelope S i t*l.envelope S j t ≤ S.mean p t := by
  cases k <;> cases l <;> dsimp only [envelope]
  all_goals first
    | exact S.slow_high_high_mean_bound i j p hi hj hij t
    | exact S.slow_mean_high_mean_bound i j p hi hj hij t
    | exact S.slow_mean_mean_bound i j p hi hj hij t
    | simpa only [mul_comm] using S.slow_mean_high_mean_bound j i p hj hi (by omega) t

private theorem envelope_slow_high (k l : KnownPiece) (S : Scales K) (i j p : ℕ)
    (hi : 1 ≤ i) (hj : 1 ≤ j) (hij : i + j = p)
    (hhigh : ¬ (k = .mean ∧ l = .mean)) (t : K) :
    k.envelope S i t*l.envelope S j t ≤ S.high p t := by
  cases k <;> cases l <;> dsimp only [envelope]
  all_goals first
    | exact S.slow_high_high_high_bound i j p hi hj hij t
    | exact S.slow_mean_high_high_bound i j p hi hj hij t
    | simpa only [mul_comm] using S.slow_mean_high_high_bound j i p hj hi (by omega) t
    | exact (hhigh ⟨rfl,rfl⟩).elim

theorem slow_profile_mean (k l : KnownPiece) (S : Scales K) (i j p : ℕ)
    (hi : 1 ≤ i) (hj : 1 ≤ j) (hij : i + j = p) (t : K) :
    k.profile S i t*l.profile S j t ≤ S.mean p t :=
  (mul_le_mul (k.profile_le_envelope S i t) (l.profile_le_envelope S j t)
    (l.profile_pos S j t).le (k.envelope_pos S i t).le).trans
      (envelope_slow_mean k l S i j p hi hj hij t)

theorem slow_profile_high (k l : KnownPiece) (S : Scales K) (i j p : ℕ)
    (hi : 1 ≤ i) (hj : 1 ≤ j) (hij : i + j = p)
    (hhigh : ¬ (k = .mean ∧ l = .mean)) (t : K) :
    k.profile S i t*l.profile S j t ≤ S.high p t :=
  (mul_le_mul (k.profile_le_envelope S i t) (l.profile_le_envelope S j t)
    (l.profile_pos S j t).le (k.envelope_pos S i t).le).trans
      (envelope_slow_high k l S i j p hi hj hij hhigh t)

theorem fast_mean_profile_high (l : KnownPiece) (S : Scales K) (i j p : ℕ)
    (hl : l ≠ .mean) (hi : 1 ≤ i) (hj : 1 ≤ j) (hij : i + j = p + 1) (t : K) :
    KnownPiece.mean.profile S i t*l.profile S j t ≤ S.high p t :=
  (mul_le_mul_of_nonneg_left (l.profile_le_high S j hl t) (S.mean_pos i t).le).trans_eq
    (S.fast_mean_high_bound i j p hi hj hij t)

theorem fast_corrector_profile_mean (l : KnownPiece) (S : Scales K) (i j p : ℕ)
    (hl : l ≠ .mean) (hi : 2 ≤ i) (hj : 1 ≤ j) (hij : i + j = p + 1) (t : K) :
    KnownPiece.corrector.profile S i t*l.profile S j t ≤ S.mean p t :=
  (mul_le_mul_of_nonneg_left (l.profile_le_high S j hl t) (S.high_pos (i-1) t).le).trans
    (S.fast_corrector_high_mean_bound i j p hi hj hij t)

theorem fast_corrector_profile_high (l : KnownPiece) (S : Scales K) (i j p : ℕ)
    (hl : l ≠ .mean) (hi : 2 ≤ i) (hj : 1 ≤ j) (hij : i + j = p + 1) (t : K) :
    KnownPiece.corrector.profile S i t*l.profile S j t ≤ S.high p t :=
  (mul_le_mul_of_nonneg_left (l.profile_le_high S j hl t) (S.high_pos (i-1) t).le).trans
    (S.fast_corrector_high_high_bound i j p hi hj hij t)

end EulerPacketCylinderField.KnownPiece
