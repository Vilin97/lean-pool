/-
Copyright (c) 2026 M1ngXU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Max Obreiter, Tobias Steinbrecher, Robert Foerster
-/

import LeanPool.PLAcceleratedNesterovLean.Core.NesterovScheme

/-!
# Generalized Nesterov Sequence and State-Based Definitions

Extends the Nesterov scheme with:
- `nesterovSeqGen`: sequence with arbitrary initial state (not just v=0)
- State-based Lyapunov, auxVar, and related definitions
- Equivalence with the original `nesterovSeq` definitions

These are needed for the Nesterov algorithm with arbitrary initial state
(nonzero velocity).
-/

noncomputable section

namespace PLAcceleratedNesterovLean

open scoped Topology NNReal
open Manifold

variable {d : ℕ}

/-! ## Generalized Nesterov sequence -/

/-- Generalized Nesterov sequence starting from an arbitrary initial state s₀.
    Generalization of `nesterovSeq` supporting nonzero initial velocity. -/
def nesterovSeqGen (f : E d → ℝ) (η ρ : ℝ) (s₀ : NesterovState d) :
    ℕ → NesterovState d
  | 0     => s₀
  | n + 1 => nesterovStep f η ρ (nesterovSeqGen f η ρ s₀ n)

/-- `nesterovSeq` is `nesterovSeqGen` with zero initial velocity. -/
theorem nesterovSeqGen_zero_vel (f : E d → ℝ) (η ρ : ℝ) (x₁ : E d) (n : ℕ) :
    nesterovSeqGen f η ρ ⟨x₁, 0⟩ n = nesterovSeq f η ρ x₁ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [nesterovSeqGen, nesterovSeq, ih]

theorem nesterovSeqGen_succ (f : E d → ℝ) (η ρ : ℝ) (s₀ : NesterovState d) (n : ℕ) :
    nesterovSeqGen f η ρ s₀ (n + 1) = nesterovStep f η ρ (nesterovSeqGen f η ρ s₀ n) :=
  rfl

/-! ## State-based auxiliary definitions -/

/-- Normal displacement for a given state: e = x' − π(x'). -/
def normalDispOfState (π : E d → E d) (η : ℝ) (s : NesterovState d) : E d :=
  let x' := s.lookahead η
  x' - π x'

/-- Auxiliary variable for a given state: u = P⊥v + √μ'·e. -/
def auxVarOfState (P : E d →L[ℝ] E d) (μ' : ℝ) (π : E d → E d) (η : ℝ)
    (s : NesterovState d) : E d :=
  let e := normalDispOfState π η s
  (s.v - P s.v) + Real.sqrt μ' • e

/-- Curvature error for a step: ξ = e' − e − P⊥h. -/
def curvatureErrorOfState (P : E d → E d) (π : E d → E d) (f : E d → ℝ)
    (η ρ : ℝ) (s : NesterovState d) : E d :=
  let s' := nesterovStep f η ρ s
  let e  := normalDispOfState π η s
  let e' := normalDispOfState π η s'
  let h  := s'.lookahead η - s.lookahead η
  e' - e - (h - P h)

/-- Step displacement h = x'_{n+1} − x'_n for a given state. -/
def stepDispOfState (f : E d → ℝ) (η ρ : ℝ) (s : NesterovState d) : E d :=
  let s' := nesterovStep f η ρ s
  s'.lookahead η - s.lookahead η

/-- Gradient at the lookahead point for a given state. -/
def gradOfState (f : E d → ℝ) (η : ℝ) (s : NesterovState d) : E d :=
  gradient f (s.lookahead η)

/-- State-based Lyapunov function:
    L(s) = (f(x) − f⋆) + ½‖u‖² + λ‖Pv‖²
    where u = P⊥v + √μ'·e, λ = (1+a)²/(2(1−a)), a = √(μ'·η). -/
def lyapunovOfState (P : E d →L[ℝ] E d) (μ' : ℝ) (π : E d → E d)
    (f : E d → ℝ) (η : ℝ) (s : NesterovState d) : ℝ :=
  let u := auxVarOfState P μ' π η s
  let a := Real.sqrt (μ' * η)
  let lam := (1 + a) ^ 2 / (2 * (1 - a))
  (f s.x - fStar f) + ‖u‖ ^ 2 / 2 + lam * ‖P s.v‖ ^ 2

/-! ## Equivalence with `nesterovSeq`-based definitions -/

theorem normalDispOfState_eq_normalDisp (π : E d → E d) (f : E d → ℝ) (η ρ : ℝ)
    (x₁ : E d) (n : ℕ) :
    normalDispOfState π η (nesterovSeq f η ρ x₁ n) = normalDisp π f η ρ x₁ n := rfl

theorem auxVarOfState_eq_auxVar (P : E d →L[ℝ] E d) (μ' : ℝ) (π : E d → E d)
    (f : E d → ℝ) (η ρ : ℝ) (x₁ : E d) (n : ℕ) :
    auxVarOfState P μ' π η (nesterovSeq f η ρ x₁ n) = auxVar P μ' π f η ρ x₁ n := rfl

theorem stepDispOfState_eq_nesterovH (f : E d → ℝ) (η ρ : ℝ) (x₁ : E d) (n : ℕ) :
    stepDispOfState f η ρ (nesterovSeq f η ρ x₁ n) = nesterovH f η ρ x₁ n := rfl

theorem gradOfState_eq_nesterovGrad (f : E d → ℝ) (η ρ : ℝ) (x₁ : E d) (n : ℕ) :
    gradOfState f η (nesterovSeq f η ρ x₁ n) = nesterovGrad f η ρ x₁ n := rfl

theorem curvatureErrorOfState_eq_curvatureError (P π : E d → E d) (f : E d → ℝ)
    (η ρ : ℝ) (x₁ : E d) (n : ℕ) :
    curvatureErrorOfState P π f η ρ (nesterovSeq f η ρ x₁ n) =
    curvatureError P π f η ρ x₁ n := rfl

theorem lyapunovOfState_eq_lyapunov (P : E d →L[ℝ] E d) (μ' : ℝ) (π : E d → E d)
    (f : E d → ℝ) (η ρ : ℝ) (x₁ : E d) (n : ℕ) :
    lyapunovOfState P μ' π f η (nesterovSeq f η ρ x₁ n) =
    lyapunov P μ' π f η ρ x₁ n := by
  simp only [lyapunovOfState, lyapunov, auxVarOfState, auxVar,
    normalDispOfState, normalDisp, NesterovState.lookahead]

/-! ## Basic properties -/

theorem lyapunovOfState_nonneg (P : E d →L[ℝ] E d) (μ' : ℝ) (π : E d → E d)
    (f : E d → ℝ) (η : ℝ) (s : NesterovState d)
    (hμ' : 0 < μ') (hη : 0 < η) (hμη : μ' * η < 1)
    (hbdd : BddBelow (Set.range f)) :
    0 ≤ lyapunovOfState P μ' π f η s := by
  simp only [lyapunovOfState]
  have ha : 0 < Real.sqrt (μ' * η) := Real.sqrt_pos_of_pos (mul_pos hμ' hη)
  have ha_lt1 : Real.sqrt (μ' * η) < 1 := by
    calc Real.sqrt (μ' * η) < Real.sqrt 1 :=
        Real.sqrt_lt_sqrt (le_of_lt (mul_pos hμ' hη)) (by linarith)
      _ = 1 := Real.sqrt_one
  have hlam : 0 ≤ (1 + Real.sqrt (μ' * η)) ^ 2 / (2 * (1 - Real.sqrt (μ' * η))) :=
    le_of_lt (div_pos (sq_pos_of_pos (by linarith)) (by linarith))
  have hgap : 0 ≤ f s.x - fStar f := sub_nonneg.mpr (ciInf_le hbdd s.x)
  have h1 := sq_nonneg ‖auxVarOfState P μ' π η s‖
  have h2 := mul_nonneg hlam (sq_nonneg ‖P s.v‖)
  linarith

end PLAcceleratedNesterovLean
