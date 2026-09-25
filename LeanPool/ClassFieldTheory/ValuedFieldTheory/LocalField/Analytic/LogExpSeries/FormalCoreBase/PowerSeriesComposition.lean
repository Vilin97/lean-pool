/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.RingTheory.PowerSeries.Log
public import Mathlib.RingTheory.PowerSeries.WellKnown
/-!
# Formal logarithm and exponential composition

This module develops the formal composition identities between Mathlib's
`PowerSeries.log` and `PowerSeries.exp` that are used by the local-field
logarithm and exponential.
-/

@[expose] public section

noncomputable section

attribute [local instance] Classical.propDecidable

namespace PowerSeries

/-- The alternating geometric series is the formal inverse of `1 + X`. -/
theorem alternating_mul_one_add_X
    (A : Type*) [CommRing A] :
    (PowerSeries.mk fun n : ℕ => (-1 : A) ^ n) *
        (1 + PowerSeries.X : PowerSeries A) = 1 := by
  have h :=
    congrArg (PowerSeries.evalNegHom (A := A))
      (PowerSeries.mk_one_mul_one_sub_eq_one A)
  have hmk' :
      PowerSeries.evalNegHom (PowerSeries.mk (1 : ℕ → A)) =
        PowerSeries.mk fun n : ℕ => (-1 : A) ^ n := by
    ext n
    simp [PowerSeries.evalNegHom, PowerSeries.rescale_mk]
  simpa [hmk', sub_eq_add_neg] using h

/-- A torsion-free power series with zero constant coefficient satisfying
`f' * (1 + X) = f` is zero. -/
theorem eq_zero_of_derivative_mul_one_add_X_eq_self
    (A : Type*) [CommRing A] [IsAddTorsionFree A] {f : PowerSeries A}
    (hD :
      PowerSeries.derivative f * (1 + PowerSeries.X : PowerSeries A) = f)
    (hc : PowerSeries.constantCoeff f = 0) :
    f = 0 := by
  ext n
  induction n with
  | zero =>
      rw [PowerSeries.coeff_zero_eq_constantCoeff, hc]
      simp
  | succ n ih =>
      cases n with
      | zero =>
          have hcoeff := congrArg (PowerSeries.coeff 0) hD
          have hmul :
              PowerSeries.derivative f *
                  (1 + PowerSeries.X : PowerSeries A) =
                PowerSeries.derivative f +
                  PowerSeries.derivative f * PowerSeries.X := by
            ring
          rw [hmul, map_add, PowerSeries.coeff_zero_mul_X,
            add_zero, PowerSeries.coeff_zero_eq_constantCoeff, hc] at hcoeff
          rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
            PowerSeries.coeff_derivative] at hcoeff
          simpa using hcoeff
      | succ n =>
          have hcoeff := congrArg (PowerSeries.coeff (n + 1)) hD
          have hmul :
              PowerSeries.derivative f *
                  (1 + PowerSeries.X : PowerSeries A) =
                PowerSeries.derivative f +
                  PowerSeries.derivative f * PowerSeries.X := by
            ring
          rw [hmul, map_add, PowerSeries.coeff_succ_mul_X,
            PowerSeries.coeff_derivative, PowerSeries.coeff_derivative] at hcoeff
          simp only [Nat.cast_add, Nat.cast_one, ih, map_zero, zero_mul, add_zero] at hcoeff
          have hzero :
              PowerSeries.coeff (n + 2) f *
                  ((Nat.succ (n + 1) : ℕ) : A) = 0 := by
            simpa using hcoeff
          rw [mul_comm, ← nsmul_eq_mul] at hzero
          simpa using
            (smul_right_inj (Nat.succ_ne_zero (n + 1))).mp
              (by simpa using hzero)

/-- A torsion-free power series with constant coefficient one satisfying
`f' * (1 + X) = f` is `1 + X`. -/
theorem eq_one_add_X_of_derivative_mul_one_add_X_eq_self
    (A : Type*) [CommRing A] [IsAddTorsionFree A] {f : PowerSeries A}
    (hD :
      PowerSeries.derivative f * (1 + PowerSeries.X : PowerSeries A) = f)
    (hc : PowerSeries.constantCoeff f = 1) :
    f = 1 + PowerSeries.X := by
  have hbase :
      PowerSeries.derivative (1 + PowerSeries.X : PowerSeries A) *
          (1 + PowerSeries.X : PowerSeries A) =
        (1 + PowerSeries.X : PowerSeries A) := by
    simp
  have hzero :
      PowerSeries.derivative (f - (1 + PowerSeries.X : PowerSeries A)) *
          (1 + PowerSeries.X : PowerSeries A) =
        f - (1 + PowerSeries.X : PowerSeries A) := by
    rw [map_sub, sub_mul, hD, hbase]
  have hczero :
      PowerSeries.constantCoeff
          (f - (1 + PowerSeries.X : PowerSeries A)) = 0 := by
    simp [hc]
  have h := eq_zero_of_derivative_mul_one_add_X_eq_self
    A hzero hczero
  exact sub_eq_zero.mp h

/-- A power series with derivative one and constant coefficient zero is `X`. -/
theorem eq_X_of_derivative_eq_one
    (A : Type*) [CommRing A] [IsAddTorsionFree A] {f : PowerSeries A}
    (hD : PowerSeries.derivative f = 1)
    (hc : PowerSeries.constantCoeff f = 0) :
    f = PowerSeries.X := by
  apply PowerSeries.derivative.ext
  · rw [hD, PowerSeries.derivative_X]
  · simp [hc]

/-- Substituting Mathlib's formal logarithm into its exponential yields
`1 + X`. -/
theorem exp_subst_log_eq_one_add_X
    (A : Type*) [CommRing A] [Algebra ℚ A] [IsAddTorsionFree A] :
    PowerSeries.subst (PowerSeries.log A) (PowerSeries.exp A) =
      (1 + PowerSeries.X : PowerSeries A) := by
  let l : PowerSeries A := PowerSeries.log A
  have hl0 : PowerSeries.constantCoeff l = 0 :=
    PowerSeries.constantCoeff_log
  have hl : PowerSeries.HasSubst l := by
    simpa [l] using PowerSeries.HasSubst.log (A := A)
  let f : PowerSeries A := PowerSeries.subst l (PowerSeries.exp A)
  have hD :
      PowerSeries.derivative f * (1 + PowerSeries.X : PowerSeries A) = f := by
    dsimp [f]
    rw [PowerSeries.derivative_subst hl]
    rw [PowerSeries.derivative_exp]
    calc
      (PowerSeries.subst l (PowerSeries.exp A) *
            PowerSeries.derivative l) *
          (1 + PowerSeries.X : PowerSeries A) =
        PowerSeries.subst l (PowerSeries.exp A) *
          (PowerSeries.derivative l *
            (1 + PowerSeries.X : PowerSeries A)) := by
          ring
      _ = PowerSeries.subst l (PowerSeries.exp A) * 1 := by
          rw [show
            PowerSeries.derivative l *
              (1 + PowerSeries.X : PowerSeries A) = 1 by
              simpa [l] using
                PowerSeries.derivative_log_mul_one_add_X (A := A)]
      _ = PowerSeries.subst l (PowerSeries.exp A) := by
          rw [mul_one]
  have hc : PowerSeries.constantCoeff f = 1 := by
    dsimp [f]
    change MvPowerSeries.constantCoeff
      (PowerSeries.subst l (PowerSeries.exp A)) = 1
    rw [PowerSeries.constantCoeff_subst_of_constantCoeff_zero hl0]
    exact PowerSeries.constantCoeff_exp
  exact
    eq_one_add_X_of_derivative_mul_one_add_X_eq_self
      A hD hc

/-- Substituting `exp - 1` into Mathlib's formal logarithm yields `X`. -/
theorem log_subst_exp_sub_one_eq_X
    (A : Type*) [CommRing A] [Algebra ℚ A] [IsAddTorsionFree A] :
    PowerSeries.subst ((PowerSeries.exp A) - 1) (PowerSeries.log A) =
      (PowerSeries.X : PowerSeries A) := by
  let e : PowerSeries A := PowerSeries.exp A - 1
  have he0 : PowerSeries.constantCoeff e = 0 := by
    simp [e]
  have he : PowerSeries.HasSubst e :=
    PowerSeries.HasSubst.of_constantCoeff_zero' he0
  let l : PowerSeries A := PowerSeries.log A
  let f : PowerSeries A := PowerSeries.subst e l
  have hde : PowerSeries.derivative e = PowerSeries.exp A := by
    simp [e, PowerSeries.derivative_exp]
  have hsubst_deriv_mul_exp :
      PowerSeries.subst e (PowerSeries.derivative l) *
          PowerSeries.exp A = 1 := by
    have hlog :
        PowerSeries.derivative l *
            (1 + PowerSeries.X : PowerSeries A) = 1 := by
      simpa [l] using
        PowerSeries.derivative_log_mul_one_add_X (A := A)
    have hsubst :=
      congrArg (fun q : PowerSeries A => PowerSeries.subst e q) hlog
    have hone : PowerSeries.subst e (1 : PowerSeries A) = 1 := by
      rw [← PowerSeries.coe_substAlgHom he]
      simp
    change PowerSeries.subst e
        (PowerSeries.derivative l * (1 + PowerSeries.X : PowerSeries A)) =
      PowerSeries.subst e (1 : PowerSeries A) at hsubst
    rw [PowerSeries.subst_mul he, PowerSeries.subst_add he,
      PowerSeries.subst_X he, hone] at hsubst
    have hone_add_e : (1 : PowerSeries A) + e = PowerSeries.exp A := by
      dsimp [e]
      ring
    simpa [hone_add_e] using hsubst
  have hD : PowerSeries.derivative f = 1 := by
    dsimp [f]
    calc
      PowerSeries.derivative (PowerSeries.subst e l) =
          PowerSeries.subst e (PowerSeries.derivative l) *
            PowerSeries.derivative e := by
        rw [PowerSeries.derivative_subst he]
      _ = PowerSeries.subst e (PowerSeries.derivative l) *
            PowerSeries.exp A := by
        rw [hde]
      _ = 1 := hsubst_deriv_mul_exp
  have hc : PowerSeries.constantCoeff f = 0 := by
    dsimp [f]
    change MvPowerSeries.constantCoeff (PowerSeries.subst e l) = 0
    rw [PowerSeries.constantCoeff_subst_of_constantCoeff_zero he0]
    exact PowerSeries.constantCoeff_log
  exact eq_X_of_derivative_eq_one A hD hc


end PowerSeries

end
