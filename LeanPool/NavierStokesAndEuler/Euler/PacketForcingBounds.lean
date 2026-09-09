/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderKnownForce
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderTermBudget
public import LeanPool.NavierStokesAndEuler.Euler.PacketKnownPieceBounds
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderBoundTransfer
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderLinearTermBudget
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderProfileChange
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderWeightedLinear
import LeanPool.NavierStokesAndEuler.Euler.PacketGradeAbsorption
import LeanPool.NavierStokesAndEuler.Euler.PacketKnownTermBounds
import LeanPool.NavierStokesAndEuler.Euler.PacketKnownTermSums

/-! Actual mean and high forcing estimates at one fixed radius, uniform in the packet grade. -/

@[expose] public section


noncomputable section

namespace EulerPacketCylinderField.PrefixBound

open Set Finset EulerSmoothLimit EulerPacketPointJets EulerPacketProfileRecursion
  EulerPacketTimeProfile EulerPacketShiftArithmetic EulerParameterWordGevrey

variable {P T : ℝ} [Fact (0 < P)] {p : ℕ} {a : ℕ → Profile}
  {F : PrefixFields P T p a} {O : Operators} {C : CoefficientData P T O}
  (hp : 2 ≤ p) (hT : 0 < T) {correctorT : VectorField} (Ct : Field P T correctorT)
  (hCt : TimeDerivative hT.le (F.corrector (p - 1) (Nat.sub_one_lt_of_lt hp)) Ct)
  (pressure : Field P T (pressureGradient (a (p - 1)).highPressure))
  {S : Scales (Icc (0 : ℝ) T)} {R : ℝ}
  (BF : PrefixBound F hT.le S R) (BC : CoefficientBudget C)
  (hCtBound : (Ct.normalized hT.le (S.high (p - 1)) (S.high_pos (p - 1))).WordBound 6 R 1 (highShift
      (p - 1)))
  (hPressureBound : (pressure.normalized hT.le (S.high (p - 1)) (S.high_pos (p - 1))).WordBound 6 R
      1
    (highShift (p - 1)))
  (hR : 1 ≤ R) (hRc : sobolevCoefficientRadius (Fin 4) BC.Rc ≤ R) (hcost : BC.termCost ≤ R)
  (hc : (a 0).corrector = 0) (hB₁ : (a 1).mean = 0)
  (hA : ∀ i, i < p → ∀ (t : Icc (0 : ℝ) T) x θ,
    inner ℝ (O.normal (t, (x, θ))) ((a i).high (t, (x, θ))) = 0)
  (hB : ∀ i, i < p → ∀ (t : Icc (0 : ℝ) T) x θ,
    (a i).mean (t, (x, θ)) = (a i).mean (t, (x, 0)))

include BF hCtBound hPressureBound hR hRc hcost hc hB₁ hA hB

theorem meanForce_bound :
    ((F.meanForce C (by
        omega) hT Ct hCt pressure).normalized hT.le (S.mean p) (S.mean_pos p)).WordBound
      6 R 1 (meanForceShift p) := by
  let f : KnownTermIndex → VectorField := fun q => q.1.meanRaw O p a q.2.1 q.2.2
  let W : ∀ q, Field P T (f q) := fun q => F.meanTermField C (by
      omega) hT Ct hCt pressure q.1 q.2.1 q.2.2
  let G := Field.finsetSum (knownTermIndices p) f W
  have hd : 0 < meanForceShift p := by have h := force_shift_dominates_grade p hp; omega
  have hcount : (knownTermIndices p).card ≤ (meanForceShift p)^2 := by
    have hc0 := knownTermIndices_card_room p
    have hc1 := (padded_grade_count p hp).1
    omega
  have hs : (G.normalized hT.le (S.mean p) (S.mean_pos p)).WordBound 6 R 1 (meanForceShift p) :=
    Field.wordBound_normalized_finset_absorb hT.le (S.mean p) (S.mean_pos p)
      (knownTermIndices p) f W 6 R BC.termCost (meanForceShift p)
      (fun q => q.1.meanBudgetShift p q.2.1 q.2.2) hR BC.termCost_nonneg hcost hd hcount
      (fun q _ => q.1.meanBudgetShift_lt p q.2.1 q.2.2 hp)
      (fun q _ => mean_term_bound hp hT Ct hCt pressure BF BC hCtBound hPressureBound
        (zero_le_one.trans hR) hRc q.1 q.2.1 q.2.2)
  exact (hs.normalized_neg hT.le).normalized_of_raw_eq
    (F.meanForce C (by omega) hT Ct hCt pressure) hT.le (S.mean p) (S.mean_pos p)
    (fun t x θ => by
      simpa only [Pi.neg_apply,Finset.sum_apply,f] using
        F.meanForce_decomposition C hp hT Ct hCt pressure hc hB₁ hA hB t x θ)

theorem highForce_bound (newMean : Field P T (meanResult O p a).1)
    (hnew : (newMean.normalized hT.le (S.mean p) (S.mean_pos p)).WordBound 6 R 1 (meanShift p)) :
    ((F.highForce C hp hT Ct hCt pressure newMean).normalized hT.le (S.high p) (S.high_pos
        p)).WordBound
      6 R 1 (highForceShift p) := by
  let A := SpatialJetField.fastAdvection C.normal (SpatialJetField.ofField O.interval newMean)
    (SpatialJetField.ofField O.interval (F.high 1 (by omega)))
  have hA0 : (A.normalized hT.le (S.high p) (S.high_pos p)).WordBound 6 R BC.fastCost
      (meanShift p+highShift 1+1) :=
    BC.fast_bound (SpatialJetField.ofField O.interval newMean)
      (SpatialJetField.ofField O.interval (F.high 1 (by omega))) hT.le
      (S.mean p) (S.high 1) (S.high p) (S.mean_pos p) (S.high_pos 1) (S.high_pos p)
      hnew (BF.high 1 (by omega) (by omega)) (zero_le_one.trans hR) hRc
      (fun t => (S.fast_mean_high_bound p 1 p (by omega) (by omega) rfl t).le)
  have hA1 := hA0.mono_amplitude (zero_le_one.trans hR) BC.fastCost_le
  let f : Option KnownTermIndex → VectorField := fun q =>
    match q with
    | none => fun z => fastAdvection (O.normal z) (slicedJet O.interval (meanResult O p a).1 z)
        (slicedJet O.interval (a 1).high z)
    | some q => q.1.highRaw O p a q.2.1 q.2.2
  let W : ∀ q, Field P T (f q) := fun q =>
    match q with
    | none => A
    | some q => F.highTermField C (by omega) hT Ct hCt pressure q.1 q.2.1 q.2.2
  let shift : Option KnownTermIndex → ℕ := fun q =>
    match q with
    | none => meanShift p+highShift 1+1
    | some q => q.1.budgetShift p q.2.1 q.2.2
  let G := Field.finsetSum (knownTermIndices p).insertNone f W
  have hd : 0 < highForceShift p := by have h := force_shift_dominates_grade p hp; omega
  have hcount : (knownTermIndices p).insertNone.card ≤ (highForceShift p)^2 := by
    rw [card_insertNone]
    exact (knownTermIndices_card_room p).trans (padded_grade_count p hp).2
  have hshift : ∀ q ∈ (knownTermIndices p).insertNone, shift q < highForceShift p := by
    intro q _
    cases q with
    | none =>
        change meanShift p+highShift 1+1 < highForceShift p
        have hh := fast_mean_high_room p 1 p hp (by omega) rfl
        omega
    | some q => exact q.1.budgetShift_lt_high p q.2.1 q.2.2 hp
  have hblocks : ∀ q ∈ (knownTermIndices p).insertNone,
      ((W q).normalized hT.le (S.high p) (S.high_pos p)).WordBound 6 R BC.termCost (shift q) := by
    intro q _
    cases q with
    | none => exact hA1
    | some q =>
        exact high_term_bound hp hT Ct hCt pressure BF BC hCtBound hPressureBound
          (zero_le_one.trans hR) hRc q.1 q.2.1 q.2.2
  have hs : (G.normalized hT.le (S.high p) (S.high_pos p)).WordBound 6 R 1 (highForceShift p) :=
    Field.wordBound_normalized_finset_absorb hT.le (S.high p) (S.high_pos p)
      (knownTermIndices p).insertNone f W 6 R BC.termCost (highForceShift p) shift
      hR BC.termCost_nonneg hcost hd hcount hshift hblocks
  apply (hs.normalized_neg hT.le).normalized_of_raw_eq
    (F.highForce C hp hT Ct hCt pressure newMean) hT.le (S.high p) (S.high_pos p)
  intro t x θ
  simp only [Pi.neg_apply,Finset.sum_apply]
  change highForce O p a (t,(x,θ)) = -(∑ q ∈ (knownTermIndices p).insertNone, f q (t,(x,θ)))
  rw [F.highForce_decomposition C hp hT Ct hCt pressure hc hB₁ hA hB,Finset.sum_insertNone]
  dsimp only [f]
  abel

end EulerPacketCylinderField.PrefixBound
