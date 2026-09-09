/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketKnownPieceBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderLinearTermBudget

@[expose] public section

/-! Bounds on the actual masked slow and fast products, with zero terms charged no shifts. -/

noncomputable section

namespace EulerPacketCylinderField.PrefixBound

open Set EulerSmoothLimit EulerPacketPointJets EulerPacketProfileRecursion
  EulerPacketTimeProfile EulerParameterWordGevrey

variable {P T : ℝ} [Fact (0 < P)] {p : ℕ} {a : ℕ → Profile}
  {F : PrefixFields P T p a} {hT : 0 ≤ T} {S : Scales (Icc (0 : ℝ) T)} {R : ℝ}
  (BF : PrefixBound F hT S R) {O : Operators} {C : CoefficientData P T O} (BC : CoefficientBudget C)

include BF

theorem maskedSlow_bound (l r : KnownPiece) (i j n : ℕ) {raw : VectorField} (W : Field P T raw)
    (he : ∀ (t : Icc (0 : ℝ) T) x θ, raw (t,(x,θ)) = if i+j=n then
      slowAdvection (O.inverseFrame (t,(x,θ))) (l.jet O p a (t,(x,θ)) i) (r.jet O p a (t,(x,θ)) j)
        else 0)
    (b : C(Icc (0 : ℝ) T,ℝ)) (hb : ∀ t, 0 < b t)
    (hR : 0 ≤ R) (hRc : sobolevCoefficientRadius (Fin 4) BC.Rc ≤ R)
    (hprofile : i+j=n → l.active p i → r.active p j →
      ∀ t, l.profile S i t*r.profile S j t ≤ b t) :
    (W.normalized hT b hb).WordBound 6 R BC.slowCost
      (if i+j=n ∧ l.active p i ∧ r.active p j then l.shift i+r.shift j+1 else 0) := by
  by_cases hactive : i+j=n ∧ l.active p i ∧ r.active p j
  · have hbound := BC.slow_bound (F.pieceJet O l i) (F.pieceJet O r j) hT
      (l.profile S i) (r.profile S j) b (l.profile_pos S i) (r.profile_pos S j) hb
      (BF.pieceJet hR O l i) (BF.pieceJet hR O r j) hR hRc
      (hprofile hactive.1 hactive.2.1 hactive.2.2)
    have ht := hbound.normalized_of_raw_eq W hT b hb (fun t x θ => by
      rw [he t x θ,ite_eq_left hactive.1])
    simpa only [ite_eq_left hactive] using ht
  · have hz : ∀ (t : Icc (0 : ℝ) T) x θ, raw (t,(x,θ)) = 0 := by
      intro t x θ
      rw [he t x θ]
      by_cases hn : i+j=n
      · rw [ite_eq_left hn]
        by_cases hl : l.active p i
        · have hr : ¬ r.active p j := fun hr => hactive ⟨hn,hl,hr⟩
          rw [r.jet_zero_of_inactive O p a (t,(x,θ)) j hr,map_zero]
        · rw [l.jet_zero_of_inactive O p a (t,(x,θ)) i hl,map_zero,LinearMap.zero_apply]
      · rw [ite_eq_right hn]
    have ht := (Field.wordBound_normalized_of_zero W hz hT b hb 6 R 0).mono_amplitude hR
      BC.slowCost_nonneg
    simpa only [ite_eq_right hactive] using ht

theorem maskedFast_bound (l r : KnownPiece) (i j n : ℕ) {raw : VectorField} (W : Field P T raw)
    (he : ∀ (t : Icc (0 : ℝ) T) x θ, raw (t,(x,θ)) = if i+j=n then
      fastAdvection (O.normal (t,(x,θ))) (l.jet O p a (t,(x,θ)) i) (r.jet O p a (t,(x,θ)) j) else 0)
    (b : C(Icc (0 : ℝ) T,ℝ)) (hb : ∀ t, 0 < b t)
    (hR : 0 ≤ R) (hRc : sobolevCoefficientRadius (Fin 4) BC.Rc ≤ R)
    (hprofile : i+j=n → l.active p i → r.active p j →
      ∀ t, l.profile S i t*r.profile S j t ≤ b t) :
    (W.normalized hT b hb).WordBound 6 R BC.fastCost
      (if i+j=n ∧ l.active p i ∧ r.active p j then l.shift i+r.shift j+1 else 0) := by
  by_cases hactive : i+j=n ∧ l.active p i ∧ r.active p j
  · have hbound := BC.fast_bound (F.pieceJet O l i) (F.pieceJet O r j) hT
      (l.profile S i) (r.profile S j) b (l.profile_pos S i) (r.profile_pos S j) hb
      (BF.pieceJet hR O l i) (BF.pieceJet hR O r j) hR hRc
      (hprofile hactive.1 hactive.2.1 hactive.2.2)
    have ht := hbound.normalized_of_raw_eq W hT b hb (fun t x θ => by
      rw [he t x θ,ite_eq_left hactive.1])
    simpa only [ite_eq_left hactive] using ht
  · have hz : ∀ (t : Icc (0 : ℝ) T) x θ, raw (t,(x,θ)) = 0 := by
      intro t x θ
      rw [he t x θ]
      by_cases hn : i+j=n
      · rw [ite_eq_left hn]
        by_cases hl : l.active p i
        · have hr : ¬ r.active p j := fun hr => hactive ⟨hn,hl,hr⟩
          rw [r.jet_zero_of_inactive O p a (t,(x,θ)) j hr,map_zero]
        · rw [l.jet_zero_of_inactive O p a (t,(x,θ)) i hl,map_zero,LinearMap.zero_apply]
      · rw [ite_eq_right hn]
    have ht := (Field.wordBound_normalized_of_zero W hz hT b hb 6 R 0).mono_amplitude hR
      BC.fastCost_nonneg
    simpa only [ite_eq_right hactive] using ht

end EulerPacketCylinderField.PrefixBound
