/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import Mathlib.Tactic
public import LeanPool.Stafford38.AlgebraicAnalysis.Commutator


/-!
# Inverse-Euler/Riccati commutator identities

This module contains the purely ring-theoretic identities behind the
inverse-Euler calculation.  No Weyl presentation, filtration, module, or
application-specific hypothesis is assumed.
-/

@[expose] public section

namespace AlgebraicAnalysis.InverseEulerRiccati

variable {A : Type*} [Ring A]

/-- Historical local name for the shared ring commutator. -/
def commutator (a b : A) : A := AlgebraicAnalysis.ringCommutator a b

@[simp]
theorem commutator_eq_shared (a b : A) :
    commutator a b = AlgebraicAnalysis.ringCommutator a b := rfl

/-- Iterated commutation by a fixed element. -/
def adIterate (p : A) : ℕ → A → A
  | 0, z => z
  | n + 1, z => commutator p (adIterate p n z)

/-- Inverting the relation `P*X-X*P=-1` produces the Riccati identity. -/
theorem inverse_riccati
    (P X T : A)
    (hPX : P * X - X * P = -1)
    (hXT : X * T = 1)
    (hTX : T * X = 1) :
    P * T - T * P = T * T := by
  have hright : P - X * P * T = -T := by
    have h := congrArg (fun z : A => z * T) hPX
    simpa [sub_mul, mul_assoc, hXT] using h
  have hleft : T * P - P * T = -(T * T) := by
    have htxpt : T * (X * P * T) = P * T := by
      calc
        T * (X * P * T) = (T * X) * P * T := by noncomm_ring
        _ = P * T := by rw [hTX]; simp
    calc
      T * P - P * T = T * P - T * (X * P * T) := by rw [htxpt]
      _ = T * (P - X * P * T) := by rw [mul_sub]
      _ = T * (-T) := by rw [hright]
      _ = -(T * T) := by simp
  calc
    P * T - T * P = -(T * P - P * T) := by noncomm_ring
    _ = -(-(T * T)) := by rw [hleft]
    _ = T * T := by simp

/-- The Euler element `H = P*X` has commutator `T`. -/
theorem euler_commutator
    (P X T : A)
    (hPX : P * X - X * P = -1)
    (hXT : X * T = 1)
    (hTX : T * X = 1) :
    (P * X) * T - T * (P * X) = T := by
  have htxp : T * (X * P) = P := by
    calc
      T * (X * P) = (T * X) * P := by rw [mul_assoc]
      _ = P := by rw [hTX]; simp
  have hleft : T * (P * X) - P = -T := by
    calc
      T * (P * X) - P = T * (P * X) - T * (X * P) := by rw [htxp]
      _ = T * (P * X - X * P) := by rw [mul_sub]
      _ = T * (-1) := by rw [hPX]
      _ = -T := by simp
  have htp : T * (P * X) = P - T := by
    calc
      T * (P * X) = (T * (P * X) - P) + P := by noncomm_ring
      _ = (-T) + P := by rw [hleft]
      _ = P - T := by noncomm_ring
  calc
    (P * X) * T - T * (P * X) = P - T * (P * X) := by
      simp [mul_assoc, hXT]
    _ = T := by rw [htp]; noncomm_ring

private theorem commutator_nat_mul (P Z : A) (m : ℕ) :
    commutator P ((m : A) * Z) = (m : A) * commutator P Z := by
  have hcentral : ∀ z : A, (m : A) * z = z * (m : A) := by
    intro z
    exact Nat.cast_comm m z
  unfold commutator
  calc
    P * ((m : A) * Z) - ((m : A) * Z) * P =
        ((m : A) * (P * Z)) - ((m : A) * (Z * P)) := by
          calc
            P * ((m : A) * Z) - ((m : A) * Z) * P =
                ((P * (m : A)) * Z) - ((m : A) * Z) * P := by
                  exact congrArg (fun q : A => q - ((m : A) * Z) * P)
                    (mul_assoc P (m : A) Z).symm
            _ = (((m : A) * P) * Z) - ((m : A) * Z) * P := by
                  rw [hcentral P]
            _ = (((m : A) * P) * Z) - (m : A) * (Z * P) := by
                  exact congrArg (fun q : A => (((m : A) * P) * Z) - q)
                    (mul_assoc (m : A) Z P)
            _ = (m : A) * (P * Z) - (m : A) * (Z * P) := by
                  rw [mul_assoc]
    _ = (m : A) * (P * Z - Z * P) := by rw [mul_sub]

private theorem commutator_pow
    (P T : A)
    (hPT : P * T - T * P = T * T) :
    ∀ n : ℕ, commutator P (T ^ n) = (n : A) * T ^ (n + 1) := by
  intro n
  induction n with
  | zero => simp [commutator]
  | succ n ih =>
      calc
        commutator P (T ^ (n + 1)) =
            commutator P (T ^ n) * T + T ^ n * commutator P T := by
                simp only [commutator, AlgebraicAnalysis.ringCommutator, pow_succ]
                noncomm_ring
        _ = (n : A) * T ^ (n + 1) * T +
              T ^ n * (P * T - T * P) := by
              rw [ih]
              rfl
        _ = (n : A) * T ^ (n + 1) * T + T ^ n * (T * T) := by
              rw [hPT]
        _ = ((n + 1 : ℕ) : A) * T ^ ((n + 1) + 1) := by
              rw [Nat.cast_succ]
              simp only [pow_succ]
              noncomm_ring

/-- The iterated commutator is the factorial Riccati tower. -/
theorem iterated_commutator
    (P X T : A)
    (hPX : P * X - X * P = -1)
    (hXT : X * T = 1)
    (hTX : T * X = 1) :
    ∀ n : ℕ, adIterate P n T = (n.factorial : A) * T ^ (n + 1) := by
  have hPT : P * T - T * P = T * T :=
    inverse_riccati P X T hPX hXT hTX
  intro n
  induction n with
  | zero => simp [adIterate]
  | succ n ih =>
      calc
        adIterate P (n + 1) T = commutator P (adIterate P n T) := by rfl
        _ = commutator P ((n.factorial : A) * T ^ (n + 1)) := by rw [ih]
        _ = (n.factorial : A) * commutator P (T ^ (n + 1)) := by
              exact commutator_nat_mul P (T ^ (n + 1)) n.factorial
        _ = (n.factorial : A) * (((n + 1 : ℕ) : A) *
              T ^ ((n + 1) + 1)) := by
              rw [commutator_pow P T hPT (n + 1)]
        _ = ((n + 1).factorial : A) * T ^ ((n + 1) + 1) := by
              simp [Nat.factorial_succ, Nat.cast_succ, Nat.cast_mul,
                mul_assoc, Nat.cast_comm]


end AlgebraicAnalysis.InverseEulerRiccati
