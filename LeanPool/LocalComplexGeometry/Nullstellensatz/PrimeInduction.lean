/-
Copyright (c) 2026 BochaoKong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BochaoKong
-/

import LeanPool.LocalComplexGeometry.Nullstellensatz.Coordinates
import LeanPool.LocalComplexGeometry.Nullstellensatz.PrimeBase
import LeanPool.LocalComplexGeometry.WPTBridge.PreparedAssociate

/-!
# Reduction of the prime theorem to prepared coordinates

This file performs the outer, unconditional part of Rueckert's prime-ideal
induction.  A nonzero prime contains a nonzero nonunit germ.  After a linear
coordinate change that germ is associated to a positive-degree prepared
polynomial.  Coordinate invariance then reduces the prime zero-set theorem to
the prepared-prime step isolated below.
-/


namespace LocalComplexGeometry

open WPTBridge

noncomputable section

/-- The single remaining successor step in prepared coordinates.  Unlike the
comparator theorem, its hypotheses expose the exact prepared polynomial that
drives generic-fiber elimination. -/
def PreparedPrimeZeroSetStep (n : ℕ) : Prop :=
  ∀ {d : ℕ}
    (_hd : 0 < d)
    (a : Fin d → ClassicalComplexWPT.Base n → ℂ)
    (ha : ∀ i, AnalyticAt ℂ (a i) 0)
    (_ha0 : ∀ i, a i 0 = 0)
    (P : Ideal (HolomorphicGerm (n + 1))),
    P.IsPrime → preparedPolynomialGerm a ha ∈ P →
      vanishingIdeal (idealZeroSetGerm P) = P

/-- Every member of a proper prime ideal in the local holomorphic germ ring
vanishes at the origin. -/
theorem evalAtOrigin_eq_zero_of_mem_prime {n : ℕ}
    {P : Ideal (HolomorphicGerm n)} (hP : P.IsPrime)
    {f : HolomorphicGerm n} (hf : f ∈ P) :
    evalAtOrigin f = 0 := by
  by_contra hf0
  have hunit : IsUnit f := (holomorphicGerm_isUnit_iff f).2 hf0
  exact hP.ne_top (P.eq_top_of_isUnit_mem hf hunit)

/-- A prepared-prime step implies the full prime zero-set property in the
successor dimension. -/
theorem primeZeroSetProperty_succ_of_preparedPrimeZeroSetStep {n : ℕ}
    (hstep : PreparedPrimeZeroSetStep n) :
    PrimeZeroSetProperty (n + 1) := by
  intro P hP
  by_cases hPzero : P = ⊥
  · subst P
    rw [idealZeroSetGerm_bot, vanishingIdeal_top]
  · obtain ⟨f, hfP, hf_ne⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot hPzero
    have hf_zero : evalAtOrigin f = 0 :=
      evalAtOrigin_eq_zero_of_mem_prime hP hfP
    obtain ⟨L, d, H, a, u, hd, hH, hcoord, hH0, horder, hprep⟩ :=
      exists_regularized_weierstrassPreparation_pos hf_ne hf_zero
    let e : HolomorphicGerm (n + 1) ≃+* HolomorphicGerm (n + 1) :=
      coordinatePullback L
    let J : Ideal (HolomorphicGerm (n + 1)) := P.map e
    let : P.IsPrime := hP
    have hJprime : J.IsPrime := by
      dsimp [J]
      infer_instance
    have hcoord_mem : coordinatePullback L f ∈ J := by
      exact Ideal.mem_map_of_mem e hfP
    have hassoc : Associated (coordinatePullback L f)
        (preparedPolynomialGerm a hprep.1) :=
      coordinatePullback_associated_preparedPolynomialGerm
        L H a u hcoord hprep
    have hprepared_mem : preparedPolynomialGerm a hprep.1 ∈ J :=
      (Ideal.mem_iff_of_associated hassoc).mp hcoord_mem
    have hJzero : vanishingIdeal (idealZeroSetGerm J) = J :=
      hstep hd a hprep.1 hprep.2.1 J hJprime hprepared_mem
    exact
      (vanishingIdeal_idealZeroSetGerm_eq_iff_coordinateMap L P).mp hJzero

/-- Dimension induction closes the complete prime theorem once the prepared
successor step has been supplied in every dimension. -/
theorem primeZeroSetProperty_of_preparedPrimeZeroSetStep
    (hstep : ∀ n, PreparedPrimeZeroSetStep n) :
    ∀ n, PrimeZeroSetProperty n
  | 0 => primeZeroSetProperty_zero
  | n + 1 => primeZeroSetProperty_succ_of_preparedPrimeZeroSetStep (hstep n)

end

end LocalComplexGeometry
