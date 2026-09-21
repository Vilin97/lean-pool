/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import Mathlib.Analysis.Calculus.FDeriv.Basic
import LeanPool.ParameterFreeGradient.O3.Geometry

/-!
# Primitive objects for the O3 probe

This file fixes the finite-dimensional real model, genuine-real `ℓ_p`
functional, exact pair oracle, and an explicit deterministic interaction
machine.  In particular, a method can obtain objective information only by a
`query` transition; the smoothness constant, solution radius, optimum value,
and an optimizer are not fields of `MethodInput`.
-/

namespace O3

/-- The finite-dimensional real vector space used by the oracle and algorithms. -/
abbrev Vec (d : ℕ) := Point d

/-- A supplied exact local first-order oracle. -/
structure PairOracle (d : ℕ) where
  /-- The scalar objective value returned at a query point. -/
  value : Vec d → ℝ
  /-- The gradient vector returned at a query point. -/
  gradient : Vec d → Vec d

/-- One counted exact pair-oracle response. -/
structure Observation (d : ℕ) where
  /-- The point at which this oracle response was obtained. -/
  point : Vec d
  /-- The objective value returned by this query. -/
  value : ℝ
  /-- The gradient vector returned by this query. -/
  gradient : Vec d

/-- Package a query point with its exact objective value and gradient. -/
def PairOracle.observe {d : ℕ} (oracle : PairOracle d) (x : Vec d) : Observation d :=
  ⟨x, oracle.value x, oracle.gradient x⟩

/-- The only numerical/problem data supplied to the O3 state machine. -/
structure MethodInput (d : ℕ) where
  /-- The exponent specifying the primal norm geometry. -/
  p : ℝ
  /-- The target bound on the dual norm of the returned gradient. -/
  eps : ℝ
  /-- The initial optimization point. -/
  x0 : Vec d
  /-- The second point supplied for secant initialization. -/
  z0 : Vec d
  /-- The observable initial scale obtained from the supplied secant data. -/
  M0 : ℝ

/-- One deterministic machine action.  A continuation receives exactly the
pair returned at the point named by `query`. -/
inductive Action (d : ℕ) (State : Type) where
  | done (point : Vec d)
  | query (point : Vec d) (next : Observation d → State)

/-- An explicit deterministic first-order method.  Its transition function is
fixed before the oracle is supplied and can inspect the objective only through
the observations delivered to `Action.query`. -/
structure FirstOrderMethod (d : ℕ) where
  /-- The internal states of the deterministic first-order method. -/
  State : Type
  /-- Construct the initial internal state from the permitted method inputs. -/
  initial : MethodInput d → State
  /-- Select the next oracle query or terminal action from an internal state. -/
  action : State → Action d State

/-- Result of a fuel-bounded execution.  `queries` contains every counted
post-initialization pair-oracle call, including rejected and terminal calls. -/
structure RunResult (d : ℕ) where
  /-- The point returned when the bounded execution succeeds. -/
  returned : Vec d
  /-- Every counted oracle response in the completed execution. -/
  queries : List (Observation d)

/-- Execute at most the given number of machine steps while accumulating query responses. -/
def FirstOrderMethod.runFuel {d : ℕ} (method : FirstOrderMethod d)
    (oracle : PairOracle d) : ℕ → method.State → List (Observation d) → Option (RunResult d)
  | 0, _, _ => none
  | fuel + 1, state, history =>
      match method.action state with
      | .done x => some ⟨x, history⟩
      | .query x next =>
          let obs := oracle.observe x
          method.runFuel oracle fuel (next obs) (history ++ [obs])

/-- Run a first-order method from its initial state with an empty query history. -/
def FirstOrderMethod.run {d : ℕ} (method : FirstOrderMethod d)
    (oracle : PairOracle d) (input : MethodInput d) (fuel : ℕ) : Option (RunResult d) :=
  method.runFuel oracle fuel (method.initial input) []

/-- The number of oracle responses in a completed run. -/
def RunResult.callCount {d : ℕ} (result : RunResult d) : ℕ := result.queries.length

/-- The returned point really was queried; a bare unobserved terminal point is
not enough for the frozen theorem. -/
def RunResult.returnedWasQueried {d : ℕ} (result : RunResult d) : Prop :=
  result.returned ∈ result.queries.map Observation.point

/-- The coordinate gradient represents the Frechet derivative.  The ambient
norm used by Mathlib for differentiability is immaterial in finite dimension. -/
def IsCoordinateGradient {d : ℕ} (f : Vec d → ℝ) (grad : Vec d → Vec d) : Prop :=
  ∀ x, DifferentiableAt ℝ f x ∧ ∀ h, fderiv ℝ f x h = pairing (grad x) h

/-- The set of global minimizers of the objective function. -/
def MinimizerSet {d : ℕ} (f : Vec d → ℝ) : Set (Vec d) :=
  {x | ∀ y, f x ≤ f y}

/-- The exact source-level `ℓ_p` distance to the nonempty minimizer set. -/
noncomputable def minimizerDistance {d : ℕ} (p : ℝ) (f : Vec d → ℝ) (x0 : Vec d) : ℝ :=
  sInf ((fun x => lpNorm p (x - x0)) '' MinimizerSet f)

/-- The gradient is Lipschitz from the primal `ℓ_p` norm to the specified dual norm. -/
def IsLpSmooth {d : ℕ} (p q L : ℝ) (grad : Vec d → Vec d) : Prop :=
  ∀ x y, lpNorm q (grad x - grad y) ≤ L * lpNorm p (x - y)

/-- Exact nondegenerate secant initialization and its observable scale. -/
def SecantWitness {d : ℕ} (p q M0 : ℝ) (grad : Vec d → Vec d)
    (x0 z0 : Vec d) : Prop :=
  z0 ≠ x0 ∧ grad z0 ≠ grad x0 ∧
    M0 = lpNorm q (grad z0 - grad x0) / lpNorm p (z0 - x0) ∧ 0 < M0

/-- Exact convexity hypothesis from the frozen source. -/
def IsConvexObjective {d : ℕ} (f : Vec d → ℝ) : Prop := ConvexOn ℝ Set.univ f

/-- One complete admissible instance.  The algorithm never receives this
structure; it is used only by the correctness theorem. -/
structure AdmissibleInstance (d : ℕ) (p : ℝ) where
  /-- The objective function of the admissible optimization instance. -/
  f : Vec d → ℝ
  /-- The coordinate gradient of the objective. -/
  grad : Vec d → Vec d
  /-- The positive smoothness bound used in the instance's analytic certificate. -/
  L : ℝ
  /-- The requested terminal gradient tolerance. -/
  eps : ℝ
  /-- The point from which the method starts. -/
  x0 : Vec d
  /-- The second point in the nondegenerate secant initialization. -/
  z0 : Vec d
  /-- The initial scale witnessed by the secant data. -/
  M0 : ℝ
  p_gt_one : 1 < p
  L_pos : 0 < L
  eps_pos : 0 < eps
  gradient_spec : IsCoordinateGradient f grad
  convex : IsConvexObjective f
  minimizer_nonempty : (MinimizerSet f).Nonempty
  smooth : IsLpSmooth p (conjugateExponent p) L grad
  secant : SecantWitness p (conjugateExponent p) M0 grad x0 z0

/-- The exact value-gradient oracle associated with an admissible instance. -/
def AdmissibleInstance.oracle {d : ℕ} {p : ℝ} (P : AdmissibleInstance d p) : PairOracle d :=
  ⟨P.f, P.grad⟩

/-- Extract the observable numerical inputs supplied to the method. -/
def AdmissibleInstance.methodInput {d : ℕ} {p : ℝ} (P : AdmissibleInstance d p) : MethodInput d :=
  ⟨p, P.eps, P.x0, P.z0, P.M0⟩

/-- The primal-norm distance from the initial point to the minimizer set. -/
noncomputable def AdmissibleInstance.radius {d : ℕ} {p : ℝ} (P : AdmissibleInstance d p) : ℝ :=
  minimizerDistance p P.f P.x0

/-- The dimensionless quantity `L R / ε` governing the complexity bounds. -/
noncomputable def AdmissibleInstance.condition {d : ℕ} {p : ℝ}
    (P : AdmissibleInstance d p) : ℝ := P.L * P.radius / P.eps

/-- The condition quantity truncated below at one. -/
noncomputable def AdmissibleInstance.conditionBar {d : ℕ} {p : ℝ}
    (P : AdmissibleInstance d p) : ℝ := max 1 P.condition

/-- The returned point's gradient satisfies the prescribed dual-norm tolerance. -/
def RunResult.hasTargetGradient {d : ℕ} {p : ℝ} (P : AdmissibleInstance d p)
    (result : RunResult d) : Prop := lpNorm (conjugateExponent p) (P.grad result.returned) ≤ P.eps

end O3
