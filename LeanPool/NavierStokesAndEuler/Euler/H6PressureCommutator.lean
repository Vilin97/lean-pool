/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.H6Pressure

/-! Positive external-order commutators in actual fixed-order Sobolev blocks. -/

@[expose] public section


noncomputable section

namespace EulerH6Pressure

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerSpatialSobolevInverse
  EulerJetProductBounds EulerPressureJetIdentities EulerPressureSpatialRegularity
open scoped Topology

variable (period : ℝ) [Fact (0 < period)] {directions : Fin 4 → LiftTangent}

/-- The zero field has a genuine strong Sobolev jet at every finite order. -/
def zeroJet : (q : ℕ) → EulerSpatialSobolevInverse.SpatialJet period directions q (0 : LiftL2
    period)
  | 0 => .zero 0
  | q + 1 => .succ (fun _ => 0) (fun _ => zeroJet q) (fun _ => by
      simpa only [map_zero] using hasDerivAt_const (0 : ℝ) (0 : LiftL2 period))

theorem zeroJet_norm (q : ℕ) : (zeroJet period (directions := directions) q).sobolevNorm = 0 := by
  induction q with
  | zero => simp [zeroJet, EulerSpatialSobolevInverse.SpatialJet.sobolevNorm]
  | succ q ih => simp [zeroJet, EulerSpatialSobolevInverse.SpatialJet.sobolevNorm, ih]

@[simp]
theorem sobolevSize_zero (q : ℕ) : sobolevSize period (directions := directions) q 0 = 0 := by
  rw [sobolevSize_eq period (zeroJet period q), zeroJet_norm]

variable {period}

/-- An actual base-order Sobolev jet for the external product commutator. -/
def commutatorJet {s q n : ℕ} {A : SmoothCoefficient period} {f : LiftL2 period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period directions s A)
    (J : EulerSpatialSobolevInverse.SpatialJet period directions s f)
    (w : Fin n → Fin 4) (h : n + q ≤ s) :
    EulerSpatialSobolevInverse.SpatialJet period directions q
      ((EulerSpatialSobolevInverse.SpatialJet.multiply K J).word w - A.operator (J.word w)) :=
  (SpatialJet.derivativeJet (EulerSpatialSobolevInverse.SpatialJet.multiply K J) w h).sub
    (EulerSpatialSobolevInverse.SpatialJet.multiply (CoefficientJet.restrict K q (by omega))
      (SpatialJet.derivativeJet J w h))

/-- Sum of the actual base Sobolev norms of the external product commutators. -/
def commutatorBlock {s : ℕ} {A : SmoothCoefficient period} {f : LiftL2 period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period directions s A)
    (J : EulerSpatialSobolevInverse.SpatialJet period directions s f) (q n : ℕ) : ℝ :=
  ∑ w : Fin n → Fin 4, sobolevSize period (directions := directions) q
    ((EulerSpatialSobolevInverse.SpatialJet.multiply K J).word w - A.operator (J.word w))

theorem commutatorBlock_zero {s q : ℕ} {A : SmoothCoefficient period} {f : LiftL2 period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period directions s A)
    (J : EulerSpatialSobolevInverse.SpatialJet period directions s f) : commutatorBlock K J q 0 = 0
        := by
  simp [commutatorBlock]

theorem commutatorBlock_nonneg {s q n : ℕ} {A : SmoothCoefficient period} {f : LiftL2 period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period directions s A)
    (J : EulerSpatialSobolevInverse.SpatialJet period directions s f) : 0 ≤ commutatorBlock K J q n
        :=
  Finset.sum_nonneg (fun _ _ => sobolevSize_nonneg _ _)

/-- Truncation preserves every valid external commutator as an actual L² field. -/
theorem commutatorBlock_truncate {s q n : ℕ} {A : SmoothCoefficient period} {f : LiftL2 period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period directions (s + 1) A)
    (J : EulerSpatialSobolevInverse.SpatialJet period directions (s + 1) f) (h : n ≤ s) :
    commutatorBlock K.truncate J.truncate q n = commutatorBlock K J q n := by
  unfold commutatorBlock
  apply Finset.sum_congr rfl
  intro w _
  rw [EulerPressureJetIdentities.SpatialJet.word_unique
    (EulerSpatialSobolevInverse.SpatialJet.multiply K.truncate J.truncate)
    (EulerSpatialSobolevInverse.SpatialJet.multiply K J) rfl h (by omega) w,
    EulerPressureJetIdentities.SpatialJet.word_unique J.truncate J rfl h (by omega) w]

/-- The external commutator recurrence uses a fixed Sobolev norm at every leaf. -/
theorem commutatorBlock_succ_le {s q n : ℕ} {A : SmoothCoefficient period} {f : LiftL2 period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period directions (s + 1) A)
    (J : EulerSpatialSobolevInverse.SpatialJet period directions (s + 1) f) (h : n + q ≤ s) :
    commutatorBlock K J q (n + 1) ≤
      match K, J with
      | .succ _ lowerA _, .succ _ lowerF _ =>
          ∑ i, (commutatorBlock K.truncate (lowerF i) q n +
            blockNorm period (EulerSpatialSobolevInverse.SpatialJet.multiply (lowerA i) J.truncate)
                q n) := by
  cases K with
  | succ dA lowerA hA =>
    cases J with
    | succ df lowerF hF =>
      let K := EulerSpatialSobolevInverse.CoefficientJet.succ dA lowerA hA
      let J := EulerSpatialSobolevInverse.SpatialJet.succ df lowerF hF
      rw [commutatorBlock, sum_word_snoc]
      apply Finset.sum_le_sum
      intro i _
      rw [commutatorBlock, blockNorm_eq_word_sizes _ h, ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro w _
      rw [multiply_word_snoc]
      simp only [EulerSpatialSobolevInverse.SpatialJet.word_succ, Fin.init_snoc]
      have hlast : (Fin.snoc (α := fun _ : Fin (n + 1) => Fin 4) w i) (Fin.last n) = i := by
        simp [Fin.snoc]
      rw [hlast]
      have he :
          (EulerSpatialSobolevInverse.SpatialJet.multiply K.truncate (lowerF i)).word w +
            (EulerSpatialSobolevInverse.SpatialJet.multiply (lowerA i) J.truncate).word w -
            A.operator ((lowerF i).word w) =
          ((EulerSpatialSobolevInverse.SpatialJet.multiply K.truncate (lowerF i)).word w -
            A.operator ((lowerF i).word w)) +
            (EulerSpatialSobolevInverse.SpatialJet.multiply (lowerA i) J.truncate).word w := by abel
      rw [he]
      exact sobolevSize_add_le
        (commutatorJet K.truncate (lowerF i) w h)
        (SpatialJet.derivativeJet (EulerSpatialSobolevInverse.SpatialJet.multiply (lowerA i)
            J.truncate) w h)

/-- The complete external commutator estimate has only positive coefficient derivative orders. -/
theorem commutatorBlock_bound {s q n : ℕ} {A : SmoothCoefficient period} {f : LiftL2 period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period directions s A)
    (J : EulerSpatialSobolevInverse.SpatialJet period directions s f) (h : n + q ≤ s) :
    commutatorBlock K J q n ≤
      commutatorConvolution (coefficientBlock period K q) (blockNorm period J q) n := by
  induction n generalizing s A f with
  | zero => simp [commutatorConvolution_eq_sum, commutatorBlock_zero]
  | succ n ih =>
    cases s with
    | zero => omega
    | succ s =>
      cases K with
      | succ dA lowerA hA =>
        cases J with
        | succ df lowerF hF =>
          let K := EulerSpatialSobolevInverse.CoefficientJet.succ dA lowerA hA
          let J := EulerSpatialSobolevInverse.SpatialJet.succ df lowerF hF
          have ht : ∀ i,
              commutatorBlock K.truncate (lowerF i) q n +
                blockNorm period (EulerSpatialSobolevInverse.SpatialJet.multiply (lowerA i)
                    J.truncate) q n ≤
              commutatorConvolution (coefficientBlock period K q) (blockNorm period (lowerF i) q) n
                  +
                leibnizConvolution (coefficientBlock period (lowerA i) q) (blockNorm period J q) n
                    := by
            intro i
            have hleft := ih K.truncate (lowerF i) (by omega : n + q ≤ s)
            have hright := multiply_blockNorm_bound (lowerA i) J.truncate (by omega : n + q ≤ s)
            have heqL : commutatorConvolution (coefficientBlock period K.truncate q)
                (blockNorm period (lowerF i) q) n =
                commutatorConvolution (coefficientBlock period K q) (blockNorm period (lowerF i) q)
                    n :=
              commutatorConvolution_congr _ _ _ _ n
                (fun l hl => coefficientBlock_truncate K (by omega)) (fun _ _ => rfl)
            have heqR : leibnizConvolution (coefficientBlock period (lowerA i) q)
                (blockNorm period J.truncate q) n =
                leibnizConvolution (coefficientBlock period (lowerA i) q) (blockNorm period J q) n
                    :=
              leibnizConvolution_congr _ _ _ _ n
                (fun _ _ => rfl) (fun l hl => blockNorm_truncate J (by omega))
            rw [heqL] at hleft
            rw [heqR] at hright
            exact add_le_add hleft hright
          calc
            _ ≤ ∑ i, (commutatorBlock K.truncate (lowerF i) q n +
                blockNorm period (EulerSpatialSobolevInverse.SpatialJet.multiply (lowerA i)
                    J.truncate) q n) :=
              commutatorBlock_succ_le K J (by omega)
            _ ≤ ∑ i, (commutatorConvolution (coefficientBlock period K q)
                  (blockNorm period (lowerF i) q) n +
                leibnizConvolution (coefficientBlock period (lowerA i) q) (blockNorm period J q) n)
                    :=
              Finset.sum_le_sum (fun i _ => ht i)
            _ = commutatorConvolution (coefficientBlock period K q)
                  (fun l => ∑ i, blockNorm period (lowerF i) q l) n +
                leibnizConvolution (fun l => ∑ i, coefficientBlock period (lowerA i) q l)
                  (blockNorm period J q) n := by
              rw [Finset.sum_add_distrib, sum_commutatorConvolution_right,
                  sum_leibnizConvolution_left]
            _ = commutatorConvolution (coefficientBlock period K q) (blockNorm period J q) (n + 1)
                := by
              rw [commutatorConvolution_succ]
              congr 2
              · funext l; exact (blockNorm_succ J q l).symm
              · funext l; exact (coefficientBlock_succ dA lowerA hA q l).symm

end EulerH6Pressure
