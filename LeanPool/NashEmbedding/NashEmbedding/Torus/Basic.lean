/-
Copyright (c) 2026 David Wiygul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wiygul
-/
module


/-
Copyright (c) 2026 David Wiygul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Claude Fable 5 (Anthropic), Claude Opus 4.7 (Anthropic)
  — at the request of David Wiygul
-/
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Tactic
public import LeanPool.NashEmbedding.NashEmbedding.Sobolev.Periodicity

/-!
# NashEmbedding: Basic Definitions

Periodicity, smooth periodic functions, smooth metrics, realizable metrics,
injective embeddings, flat torus embedding.
-/

@[expose] public section

open scoped BigOperators ContDiff
open Matrix NashEmbedding.Sobolev

noncomputable
section

-- Matrix needs norm instances for ContDiff to work. `fast_instance%` rebuilds each
-- structure so its parent projections reuse Mathlib's existing `Matrix` instances
-- (topology, uniformity, scalar actions); without it, TC cannot reconcile the
-- norm-derived chain with e.g. `instTopologicalSpaceMatrix` or synthesize
-- `IsScalarTower ℝ ℝ (Matrix _ _ ℝ)` through this instance.
instance NashEmbedding.matrixNormedAddCommGroup (n : ℕ) : NormedAddCommGroup (Matrix (Fin n)
    (Fin n) ℝ) :=
  fast_instance% Pi.normedAddCommGroup
instance NashEmbedding.matrixNormedSpace (n : ℕ) : NormedSpace ℝ (Matrix (Fin n) (Fin n) ℝ) :=
  fast_instance% Pi.normedSpace

namespace NashEmbedding

/-! ## Smooth periodic functions (periodicity primitives in NashEmbedding.Sobolev) -/

/-- A function is smooth and `2πℤⁿ`-periodic. -/
structure SmoothPeriodic {n : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : (Fin n → ℝ) → V) : Prop where
  smooth : ContDiff ℝ ∞ f
  periodic : IsPeriodic2Pi f

/-! ## Smooth metrics -/

/-- A smooth metric: a smooth 2πℤⁿ-periodic `Sym_n(ℝ)`-valued function that is
  pointwise positive semi-definite. (Positive semi-definiteness includes symmetry.) -/
structure IsSmoothMetric {n : ℕ} (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) : Prop where
  smoothPeriodic : SmoothPeriodic g
  posSemidef : ∀ x, (g x).PosSemidef

/-- A positive-definite smooth metric: a smooth 2πℤⁿ-periodic `Sym_n(ℝ)`-valued function
  that is pointwise positive definite. -/
structure IsPosDefSmoothMetric {n : ℕ}
    (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) : Prop where
  smoothPeriodic : SmoothPeriodic g
  posDef : ∀ x, (g x).PosDef

/-- Every positive-definite smooth metric is a smooth metric. -/
lemma IsPosDefSmoothMetric.toIsSmoothMetric {n : ℕ}
    {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ}
    (hg : IsPosDefSmoothMetric g) : IsSmoothMetric g :=
  ⟨hg.smoothPeriodic, fun x => (hg.posDef x).posSemidef⟩

/-! ## Partial derivatives and realizable metrics -/

/-- The partial derivative of `u : ℝⁿ → ℝᴺ` with respect to the `i`-th coordinate,
  defined as the Fréchet derivative applied to the `i`-th standard basis vector. -/
def partialDeriv {n N : ℕ} (i : Fin n) (u : (Fin n → ℝ) → (Fin N → ℝ))
    (x : Fin n → ℝ) : Fin N → ℝ :=
  fderiv ℝ u x (Pi.single i 1)

/-- `u` realizes `g` if `∂ᵢu(x) · ∂ⱼu(x) = g(x)ᵢⱼ` for all `x, i, j`. -/
def Realizes {n N : ℕ} (u : (Fin n → ℝ) → (Fin N → ℝ))
    (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ (x : Fin n → ℝ) (i j : Fin n),
    dotProduct (partialDeriv i u x) (partialDeriv j u x) = g x i j

/-- A smooth metric `g` is realizable if there exist `N` and a smooth periodic
  `u : ℝⁿ → ℝᴺ` realizing it. -/
def IsRealizable {n : ℕ} (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ (N : ℕ) (u : (Fin n → ℝ) → (Fin N → ℝ)),
    SmoothPeriodic u ∧ Realizes u g

/-- Concatenation of two functions `u₁ : ℝⁿ → ℝᴺ¹` and `u₂ : ℝⁿ → ℝᴺ²`
  into `(u₁, u₂) : ℝⁿ → ℝᴺ¹⁺ᴺ²`. -/
def concat {n N₁ N₂ : ℕ} (u₁ : (Fin n → ℝ) → (Fin N₁ → ℝ))
    (u₂ : (Fin n → ℝ) → (Fin N₂ → ℝ)) :
    (Fin n → ℝ) → (Fin (N₁ + N₂) → ℝ) :=
  fun x => Fin.append (u₁ x) (u₂ x)

/-- Translation of a function: `(τ_y f)(x) = f(x - y)`. -/
def translate {n : ℕ} {V : Type*} (y : Fin n → ℝ) (f : (Fin n → ℝ) → V) :
    (Fin n → ℝ) → V :=
  fun x => f (x - y)

/-! ## Injective embeddings -/

/-- Injectivity modulo `2πℤⁿ`: `u(x) = u(y)` implies `x - y ∈ 2πℤⁿ`. -/
def IsInjectiveMod2Pi {n N : ℕ} (u : (Fin n → ℝ) → (Fin N → ℝ)) : Prop :=
  ∀ (x y : Fin n → ℝ), u x = u y → ∃ k : Fin n → ℤ, x - y = periodicShift n k

/-- Full-rank derivative: the partial derivatives `{∂ᵢu(x)}` are linearly independent
  in `ℝᴺ` at every `x`. -/
def HasFullRankDeriv {n N : ℕ} (u : (Fin n → ℝ) → (Fin N → ℝ)) : Prop :=
  ∀ (x : Fin n → ℝ), LinearIndependent ℝ (fun i : Fin n => partialDeriv i u x)

/-- An injective embedding: smooth periodic, injective modulo `2πℤⁿ`,
  and has full-rank derivative. -/
structure IsInjectiveEmbedding {n N : ℕ}
    (u : (Fin n → ℝ) → (Fin N → ℝ)) : Prop where
  smoothPeriodic : SmoothPeriodic u
  injective : IsInjectiveMod2Pi u
  fullRank : HasFullRankDeriv u

/-- A smooth metric `g` is injectively realizable if there exist `N` and an
  injective embedding `u` realizing it. -/
def IsInjRealizable {n : ℕ}
    (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ (N : ℕ) (u : (Fin n → ℝ) → (Fin N → ℝ)),
    IsInjectiveEmbedding u ∧ Realizes u g

/-- Every injectively realizable metric is realizable. -/
lemma IsInjRealizable.toIsRealizable {n : ℕ}
    {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ}
    (hg : IsInjRealizable g) : IsRealizable g :=
  let ⟨N, u, hue, hreal⟩ := hg
  ⟨N, u, hue.smoothPeriodic, hreal⟩

/-! ## Flat-torus embedding -/

/-- The flat-torus embedding `u_flat : ℝⁿ → ℝ²ⁿ` defined by
  `u_flat(x) = (cos x₁, sin x₁, cos x₂, sin x₂, …, cos xₙ, sin xₙ)`.
  For `k : Fin (2n)`, the component is `cos(x_{k/2})` if `k` is even,
  and `sin(x_{k/2})` if `k` is odd. -/
def flatTorusEmb (n : ℕ) : (Fin n → ℝ) → (Fin (2 * n) → ℝ) :=
  fun x k =>
    let i : Fin n := ⟨k.val / 2, by omega⟩
    if k.val % 2 = 0 then Real.cos (x i) else Real.sin (x i)

/-- The flat metric `g_flat = Iₙ` (the identity matrix). -/
def flatMetric (n : ℕ) : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ :=
  fun _ => 1

/-- The operator norm of a matrix, defined as the norm of the associated
  continuous linear map on `ℝⁿ` (with the sup norm on `Fin n → ℝ`). -/
def matOpNorm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ‖A.toLin'.toContinuousLinearMap‖

end NashEmbedding

end
