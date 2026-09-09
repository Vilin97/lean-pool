/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevGevrey
public import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevCoefficient

@[expose] public section

/-!
# One-time coefficient absorption for a genuine fixed-Sobolev inverse

Only the given operator coefficients use tensor bounds. Forcing and solved
fields retain their literal fixed-base ordered-word blocks at the same radius.
-/

noncomputable section

namespace EulerParameterWordGevrey

open ContinuousLinearMap EulerGevrey
open scoped ContDiff

/-- For fixed q this is an explicit polynomial in the original inverse,
coefficient, and forcing constants. It has no grade dependence. -/
def inverseBlockCost (ι : Type*) [Fintype ι] (q : ℕ) (I Rc C D : ℝ) : ℝ :=
  1+sobolevInverseCost I (sobolevCoefficientAmplitude ι q Rc C) q*
    (sobolevCoefficientAmplitude ι q Rc C+D)

variable {P E ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]

/-- The source radius is chosen once from coefficient data; each inverse
application increases the grade by one without changing that radius. -/
theorem inverse_block_gevrey_of_tensor (directions : ι → P)
    (hd : ∀ i, ‖directions i‖ ≤ 1) (q : ℕ)
    (A : P → E →L[ℝ] E) (u f : P → E)
    (hA : ContDiff ℝ ∞ A) (hu : ContDiff ℝ ∞ u) (hf : ContDiff ℝ ∞ f)
    (heq : ∀ y, A y (u y) = f y)
    (inverse : P → E →L[ℝ] E) (hleft : ∀ x v, inverse x (A x v) = v)
    (I Rc C D R : ℝ) (hRc : 0 ≤ Rc) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hinv : ∀ x, ‖inverse x‖ ≤ I)
    (hcoeff : ∀ n x, ‖iteratedFDeriv ℝ n A x‖ ≤ C*majorant Rc 0 n)
    (hR : 2*inverseBlockCost ι q I Rc C D*(sobolevCoefficientRadius ι Rc+1) ≤ R)
    (d : ℕ) (hforce : ∀ n x, block directions q f n x ≤ D*majorant R d n)
    (n : ℕ) (x : P) : block directions q u n x ≤ majorant R (d+1) n := by
  have hI : 0 ≤ I := (norm_nonneg (inverse x)).trans (hinv x)
  have hB : 0 ≤ sobolevCoefficientAmplitude ι q Rc C :=
    sobolevCoefficientAmplitude_nonneg q Rc C hRc hC
  have hcost := sobolevInverseCost_nonneg I _ hI hB q
  have hM : 1 ≤ inverseBlockCost ι q I Rc C D := by
    unfold inverseBlockCost
    linarith [mul_nonneg hcost (add_nonneg hB hD)]
  have hMC : sobolevInverseCost I (sobolevCoefficientAmplitude ι q Rc C) q*
      sobolevCoefficientAmplitude ι q Rc C ≤ inverseBlockCost ι q I Rc C D := by
    unfold inverseBlockCost
    nlinarith
  have hMD : sobolevInverseCost I (sobolevCoefficientAmplitude ι q Rc C) q*D ≤
      inverseBlockCost ι q I Rc C D := by
    unfold inverseBlockCost
    nlinarith
  apply block_inverse_gevrey directions q A u f hA hu hf heq inverse hleft
    I (sobolevCoefficientAmplitude ι q Rc C) (sobolevCoefficientAmplitude ι q Rc C) D
    (inverseBlockCost ι q I Rc C D) (sobolevCoefficientRadius ι Rc) R
    hB hD hM hMC hMD (sobolevCoefficientRadius_nonneg Rc hRc) hR hinv
    (baseSize_of_tensor_bound directions hd q A hA Rc C hRc hC hcoeff) _ d hforce n x
  intro j y
  simpa only [majorant, Nat.add_zero] using
    coefficientBlock_of_tensor_bound directions hd q A hA Rc C hRc hC hcoeff (j+1) y

end EulerParameterWordGevrey
