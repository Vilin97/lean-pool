/-
Copyright (c) 2026 M1ngXU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Max Obreiter, Tobias Steinbrecher, Robert Foerster
-/

import LeanPool.PLAcceleratedNesterovLean.Core.Defs
import Mathlib.Geometry.Manifold.MFDeriv.Basic

/-!
# Modified Nesterov Scheme and Supporting Definitions

Shared definitions for the proof of local accelerated convergence:
- Modified Nesterov iteration (state, step, sequence)
- Hessian quadratic form
- Lyapunov function and auxiliary quantities
- Fiber-saturated sets
- Tangent/normal space of an embedded manifold
-/

noncomputable section

namespace PLAcceleratedNesterovLean

open scoped Topology NNReal
open Manifold

variable {d : ℕ}

/-! ## Hessian quadratic form -/

/-- The Hessian quadratic form: ξᵀ D²f(x) ξ = ⟨(D(∇f)(x)) ξ, ξ⟩. -/
def hessianQuadForm (f : E d → ℝ) (x ξ : E d) : ℝ :=
  @inner ℝ _ _ (fderiv ℝ (gradient f) x ξ) ξ

/-! ## Modified Nesterov scheme -/

/-- State of the modified Nesterov scheme: position x and velocity v. -/
structure NesterovState (d : ℕ) where
  /-- The current position. -/
  x : E d
  /-- The current velocity. -/
  v : E d

/-- The look-ahead point x' = x + √η · v. -/
def NesterovState.lookahead (s : NesterovState d) (η : ℝ) : E d :=
  s.x + Real.sqrt η • s.v

/-- One step of the modified Nesterov scheme:
    x' = x + √η · v       (look-ahead)
    g  = ∇f(x')            (gradient at look-ahead)
    x₊ = x' - η · g       (gradient step)
    v₊ = ρ(v - √η · g)    (momentum update)
-/
def nesterovStep (f : E d → ℝ) (η ρ : ℝ) (s : NesterovState d) : NesterovState d :=
  let x' := s.lookahead η
  let g := gradient f x'
  { x := x' - η • g
    v := ρ • (s.v - Real.sqrt η • g) }

/-- The Nesterov sequence starting from x₁ with v₁ = 0.
    Index 0 corresponds to iteration 1 in the paper. -/
def nesterovSeq (f : E d → ℝ) (η ρ : ℝ) (x₁ : E d) : ℕ → NesterovState d
  | 0     => { x := x₁, v := 0 }
  | n + 1 => nesterovStep f η ρ (nesterovSeq f η ρ x₁ n)

/-- The gradient computed at the look-ahead point at step n. -/
def nesterovGrad (f : E d → ℝ) (η ρ : ℝ) (x₁ : E d) (n : ℕ) : E d :=
  gradient f ((nesterovSeq f η ρ x₁ n).lookahead η)

/-- Step between consecutive look-ahead points: h_n = x'_{n+1} - x'_n. -/
def nesterovH (f : E d → ℝ) (η ρ : ℝ) (x₁ : E d) (n : ℕ) : E d :=
  (nesterovSeq f η ρ x₁ (n + 1)).lookahead η - (nesterovSeq f η ρ x₁ n).lookahead η

/-! ## Geometric quantities -/

/-- Normal displacement: e_n = x'_n - π(x'_n), the error from the manifold.
    Here π is the nearest-point projection. -/
def normalDisp (π : E d → E d) (f : E d → ℝ) (η ρ : ℝ) (x₁ : E d) (n : ℕ) : E d :=
  let x' := (nesterovSeq f η ρ x₁ n).lookahead η
  x' - π x'

/-- Auxiliary variable: u_n = P⊥ v_n + √μ' · e_n,
    where P⊥ = Id - P is the normal projector (P projects onto tangent space). -/
def auxVar (P : E d →L[ℝ] E d) (μ' : ℝ) (π : E d → E d)
    (f : E d → ℝ) (η ρ : ℝ) (x₁ : E d) (n : ℕ) : E d :=
  let s := nesterovSeq f η ρ x₁ n
  let perpV := s.v - P s.v
  let e := normalDisp π f η ρ x₁ n
  perpV + Real.sqrt μ' • e

/-- Curvature error: ξ_n = e_{n+1} - e_n - P⊥ h_n.
    Measures the deviation from the affine-case recursion. -/
def curvatureError (P π : E d → E d) (f : E d → ℝ) (η ρ : ℝ) (x₁ : E d) (n : ℕ) : E d :=
  let e_next := normalDisp π f η ρ x₁ (n + 1)
  let e_curr := normalDisp π f η ρ x₁ n
  let h := nesterovH f η ρ x₁ n
  e_next - e_curr - (h - P h)

/-! ## Potential and Lyapunov functions -/

/-- The potential Ψ(x) = f(x) - f⋆ + (μ'/2) · dist(x, S)².
    Combines the optimality gap with a quadratic distance penalty. -/
def psi (f : E d → ℝ) (μ' : ℝ) (S : Set (E d)) (x : E d) : ℝ :=
  (f x - fStar f) + μ' / 2 * (Metric.infDist x S) ^ 2

/-- The Lyapunov function:
    L_n = (f(x_n) - f⋆) + ½‖u_n‖² + lam‖P v_n‖²
    where lam = (1+a)²/(2(1-a)) and a = √(μ'·η). -/
def lyapunov (P : E d →L[ℝ] E d) (μ' : ℝ) (π : E d → E d)
    (f : E d → ℝ) (η ρ : ℝ) (x₁ : E d) (n : ℕ) : ℝ :=
  let s := nesterovSeq f η ρ x₁ n
  let u := auxVar P μ' π f η ρ x₁ n
  let a := Real.sqrt (μ' * η)
  let lam := (1 + a) ^ 2 / (2 * (1 - a))
  (f s.x - fStar f) + ‖u‖ ^ 2 / 2 + lam * ‖P s.v‖ ^ 2

/-! ## Fiber saturation -/

/-- A set A is fiber-saturated with respect to a projection π if for every x ∈ A,
    the segment from π(x) to x lies entirely in A. -/
def IsFiberSaturated (π : E d → E d) (A : Set (E d)) : Prop :=
  ∀ x ∈ A, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → (1 - t) • π x + t • x ∈ A

/-! ## Tangent space of an embedded manifold -/

/-- The tangent subspace of the embedded manifold at a point m,
    defined as the range of the manifold derivative of ι at m. -/
def tangentSubspace {n : ℕ} (ι : M → E d)
    [TopologicalSpace M] [ChartedSpace (ManifoldModel n) M] (m : M) :
    Submodule ℝ (E d) :=
  (mfderiv (modelI n) (modelWithCornersSelf ℝ (E d)) ι m).range

end PLAcceleratedNesterovLean
