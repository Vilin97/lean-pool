/-
Copyright (c) 2026 Makoto Yamashita. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Makoto Yamashita
-/

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Primal-dual LP data and HSDE notation

This file is intended to be a stable foundation.  It contains the LP data,
homogeneous self-dual variables, complementarity/gap notation, and the
neighborhood definitions used later in the proof.

Lean-reading hints for beginners:
* `structure` is a record type.  Its fields become named assumptions/data.
* `def` introduces a definition; `theorem` introduces a proved proposition.
* `namespace HSDInteriorPointLP` prevents names from clashing with Mathlib.
* `simp only [...]` rewrites only by the listed rules.  It is safer than bare
  `simp` in a long proof because the simplification set does not change silently.
-/

noncomputable section

open scoped BigOperators

/-!
# HSDE-LP proof skeleton with separated `(x, τ)` and `(s, κ)` variables

This version keeps the homogenizing variables explicit:

* primal-side variables: `x : Vec n` and `tau : ℝ`;
* dual/complementarity-side variables: `s : Vec n` and `kappa : ℝ`.

This is closer to the Ye--Todd--Mizuno HLP notation and is easier to compare with
Clarabel-style homogeneous embedding variables.  It is mathematically equivalent to
bundling `(x,τ)` and `(s,κ)` into vectors of dimension `n+1`, but the separated form
makes the special scalar complementarity term `τκ` visible.

The remaining YTM predictor/corrector neighborhood estimates are kept only in the
fixed-parameter YTM form: tight neighborhood `1/4`, wide neighborhood `1/2`,
and predictor step constant `8^{-2.5}`.
-/

namespace HSDInteriorPointLP

/-!
## Short Lean proof-command guide

The file is written for readers who know the interior-point algebra but may be new
to Lean.

* `intro` introduces an assumption or quantified variable from the current goal.
* `have h : P := by ...` proves and names an intermediate claim.
* `rcases h with ⟨...⟩` unpacks conjunctions, existentials, and structures.
* `simp only [...]` performs controlled rewriting using only the listed facts.
* `simpa [defs] using h` simplifies the goal and the type of `h`, then applies `h`.
* `linarith` closes linear real-arithmetic goals from the available hypotheses.
* `nlinarith` is the same idea for nonlinear arithmetic such as products/squares.
* `ring` proves polynomial identities over rings such as `ℝ`.
-/

/-- Real coordinate vectors indexed by `Fin n`. -/
abbrev Vec (n : Nat) := Fin n → ℝ

/-- Standard-form LP data for the Ye--Todd--Mizuno HLP construction:
`min cᵀx` subject to `Ax = b`, `x ≥ 0`. -/
structure LPData (m n : Nat) where
  /-- Constraint matrix. -/
  A : Matrix (Fin m) (Fin n) ℝ
  /-- Right-hand side vector. -/
  b : Vec m
  /-- Objective vector. -/
  c : Vec n

/-- Full row rank of `A`, written without importing a separate linear-independence API.
This says that the only linear combination of the rows of `A` equal to zero is the
trivial one.  This is the standard full-row-rank assumption used in primal-dual IPM
analyses. -/
def FullRowRank {m n : Nat} (P : LPData m n) : Prop :=
  ∀ y : Vec m, (∀ j : Fin n, ∑ i : Fin m, y i * P.A i j = 0) → ∀ i : Fin m, y i = 0

/-- Standard assumptions for the LP-level HLP skeleton.
For the current LP proof skeleton we only record full row rank explicitly.
Interior/nonemptiness assumptions belong to the neighborhood and local-theory
statements below. -/
structure LPStandardAssumptions {m n : Nat} (P : LPData m n) : Prop where
  full_row_rank : FullRowRank P

/-- Homogeneous complementarity dimension `n + 1`. -/
def hdim (n : Nat) : ℝ := (n : ℝ) + 1

/-- Euclidean dot product on finite real vectors. -/
def dot {n : Nat} (u v : Vec n) : ℝ :=
  ∑ i, u i * v i

/-- Pairing of `(x,τ)` and `(s,κ)`: `xᵀs + τκ`. -/
def hdot {n : Nat} (x : Vec n) (tau : ℝ) (s : Vec n) (kappa : ℝ) : ℝ :=
  dot x s + tau * kappa

/-- Squared centrality deviation for `(xᵢsᵢ, τκ)` from `μe`. -/
def centerSq {n : Nat} (x : Vec n) (tau : ℝ) (s : Vec n) (kappa : ℝ) (μ : ℝ) : ℝ :=
  (∑ i, (x i * s i - μ) ^ 2) + (tau * kappa - μ) ^ 2

/-- Homogeneous self-dual state with primal and dual/complementarity variables. -/
structure HSState (n : Nat) where
  /-- Primal vector. -/
  x : Vec n
  /-- Primal homogenizing scalar. -/
  tau : ℝ
  /-- Dual slack vector. -/
  s : Vec n
  /-- Dual homogenizing scalar. -/
  kappa : ℝ

/-- Homogeneous self-dual search direction. -/
structure HSDirection (n : Nat) where
  /-- Primal-vector direction. -/
  dx : Vec n
  /-- Primal homogenizing scalar direction. -/
  dtau : ℝ
  /-- Dual-slack direction. -/
  ds : Vec n
  /-- Dual homogenizing scalar direction. -/
  dkappa : ℝ

/-- Strict positivity of every HSD state component. -/
def Interior {n : Nat} (w : HSState n) : Prop :=
  (∀ i, 0 < w.x i) ∧ 0 < w.tau ∧ (∀ i, 0 < w.s i) ∧ 0 < w.kappa

/-- Complementarity gap of an HSD state. -/
def gap {n : Nat} (w : HSState n) : ℝ :=
  hdot w.x w.tau w.s w.kappa

/-- Average complementarity measure. -/
def mu {n : Nat} (w : HSState n) : ℝ :=
  gap w / hdim n

/-- HSDE central neighborhood corresponding to the YTM neighborhood
`‖(Xs, τκ) - μe‖ ≤ β μ`, written with squared Euclidean norm. -/
def HSDNeighborhood {n : Nat} (β : ℝ) (w : HSState n) : Prop :=
  Interior w ∧ 0 < β ∧ β < 1 ∧
  centerSq w.x w.tau w.s w.kappa (mu w) ≤ (β * mu w) ^ 2

/-- Apply a scalar step along an HSD search direction. -/
def addStep {n : Nat} (w : HSState n) (d : HSDirection n) (α : ℝ) : HSState n :=
  { x := fun i => w.x i + α * d.dx i
    tau := w.tau + α * d.dtau
    s := fun i => w.s i + α * d.ds i
    kappa := w.kappa + α * d.dkappa }

/-- Direction lies in the HLP nullspace, recorded through the skew-symmetry
consequence used in the complementarity-gap calculation.

In the full HLP formulation this identity is obtained by multiplying the four
linearized HLP equality equations by the corresponding direction components and
adding them.  See `HLPNullDirection_from_full_nullspace` below for the concrete
calculation from the separated full equations. -/
structure HLPNullDirection {n : Nat} (d : HSDirection n) : Prop where
  cross_zero : hdot d.dx d.dtau d.ds d.dkappa = 0

/-- Skew-symmetry of the HLP constraint matrix gives this orthogonality. -/
structure HSDSkewOrthogonal {n : Nat} (d : HSDirection n) : Prop where
  cross_zero : hdot d.dx d.dtau d.ds d.dkappa = 0

/-- Complementarity equation used in the predictor/corrector system.
For `γ = 0` this is the predictor equation.  For `γ = 1` this is the corrector equation. -/
structure HSDComplementarityDirection {n : Nat}
    (w : HSState n) (d : HSDirection n) (γ : ℝ) : Prop where
  component_eq : ∀ i,
    w.x i * d.ds i + w.s i * d.dx i = γ * mu w - w.x i * w.s i
  scalar_eq :
    w.tau * d.dkappa + w.kappa * d.dtau = γ * mu w - w.tau * w.kappa
  aggregate_eq :
    hdot w.x w.tau d.ds d.dkappa + hdot d.dx d.dtau w.s w.kappa
      = -(1 - γ) * gap w

/-- A single YTM-type linearized step direction for the HLP. -/
structure HSDStepDirection {n : Nat}
    (w : HSState n) (d : HSDirection n) (γ : ℝ) : Prop where
  null_dir : HLPNullDirection d
  skew : HSDSkewOrthogonal d
  compl : HSDComplementarityDirection w d γ



/-- The linear system that defines a YTM-type search direction.

The first field represents membership in the HLP nullspace, i.e., the linearized
HLP equalities.  The last two fields are the linearized complementarity equations
for `(x,s)` and `(τ,κ)`.  The parameter `γ` distinguishes the predictor (`γ = 0`)
from the corrector (`γ = 1`). -/
structure HSDDirectionEquation {n : Nat}
    (w : HSState n) (d : HSDirection n) (γ : ℝ) : Prop where
  null_dir : HLPNullDirection d
  component_eq : ∀ i,
    w.x i * d.ds i + w.s i * d.dx i = γ * mu w - w.x i * w.s i
  scalar_eq :
    w.tau * d.dkappa + w.kappa * d.dtau = γ * mu w - w.tau * w.kappa


/-! ## Concrete YTM/HLP full-direction layer

The earlier `HSDirectionEquation` works only with the reduced variables
`(dx,dτ,ds,dκ)`.  The actual Ye--Todd--Mizuno HLP Newton system also contains
`dy` and `dθ`.  The following definitions expose that full search-direction layer.
-/

/-- Matrix-vector multiplication for the row-indexed constraint matrix. -/
def matVec {m n : Nat} (A : Matrix (Fin m) (Fin n) ℝ) (x : Vec n) : Vec m :=
  fun i => ∑ j, A i j * x j

/-- Transposed matrix-vector multiplication. -/
def tMatVec {m n : Nat} (A : Matrix (Fin m) (Fin n) ℝ) (y : Vec m) : Vec n :=
  fun j => ∑ i, A i j * y i

/-- Finite-dimensional adjointness of `matVec` and `tMatVec`. -/
theorem dot_tMatVec_eq_dot_matVec {m n : Nat}
    (A : Matrix (Fin m) (Fin n) ℝ) (y : Vec m) (x : Vec n) :
    dot x (tMatVec A y) = dot y (matVec A x) := by
  unfold dot tMatVec matVec
  calc
    (∑ j : Fin n, x j * (∑ i : Fin m, A i j * y i))
        = ∑ j : Fin n, ∑ i : Fin m, x j * (A i j * y i) := by
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.mul_sum]
    _ = ∑ i : Fin m, ∑ j : Fin n, x j * (A i j * y i) := by
            rw [Finset.sum_comm]
    _ = ∑ i : Fin m, y i * (∑ j : Fin n, A i j * x j) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring

/-- All-ones vector. -/
def ones {n : Nat} : Vec n := fun _ => 1

/-- The YTM simplified HLP uses `bbar = b - A e`. -/
def bbar {m n : Nat} (P : LPData m n) : Vec m :=
  fun i => P.b i - matVec P.A (ones : Vec n) i

/-- The YTM simplified HLP uses `cbar = c - e`. -/
def cbar {m n : Nat} (P : LPData m n) : Vec n :=
  fun j => P.c j - 1

/-- The YTM simplified HLP uses `zbar = cᵀe + 1`. -/
def zbar {m n : Nat} (P : LPData m n) : ℝ :=
  dot P.c (ones : Vec n) + 1

/-- Full HLP direction, including the equality-multiplier direction `dy` and the
free homogenizing direction `dθ`. -/
structure HLPFullDirection (m n : Nat) where
  /-- Equality-multiplier direction. -/
  dy : Vec m
  /-- Primal-vector direction. -/
  dx : Vec n
  /-- Primal homogenizing scalar direction. -/
  dtau : ℝ
  /-- Free homogenizing direction. -/
  dtheta : ℝ
  /-- Dual-slack direction. -/
  ds : Vec n
  /-- Dual homogenizing scalar direction. -/
  dkappa : ℝ

/-- Forget the free/equality components and retain the reduced complementarity
variables. -/
def HLPFullDirection.toHSDirection {m n : Nat} (D : HLPFullDirection m n) : HSDirection n :=
  { dx := D.dx
    dtau := D.dtau
    ds := D.ds
    dkappa := D.dkappa }

/-- Linearized HLP equalities in the simplified YTM HLP form.

These equations are the full analogue of membership in the HLP nullspace.  They
correspond to the four displayed equations in Theorem 5(ii) of Ye--Todd--Mizuno,
after adding the slack directions `ds` and `dκ` and keeping the free direction `dθ`.
-/
structure HLPNullspaceEquations {m n : Nat}
    (P : LPData m n) (D : HLPFullDirection m n) : Prop where
  primal_eq : ∀ i : Fin m,
    matVec P.A D.dx i - P.b i * D.dtau + bbar P i * D.dtheta = 0
  dual_eq : ∀ j : Fin n,
    -(tMatVec P.A D.dy j) + P.c j * D.dtau - cbar P j * D.dtheta - D.ds j = 0
  gap_eq :
    dot P.b D.dy - dot P.c D.dx + zbar P * D.dtheta - D.dkappa = 0
  normalizing_eq :
    -(dot (bbar P) D.dy) + dot (cbar P) D.dx - zbar P * D.dtau = 0

/-- Full YTM search-direction equations: HLP nullspace plus the linearized
complementarity equations. -/
structure HLPFullDirectionEquation {m n : Nat}
    (P : LPData m n) (w : HSState n) (D : HLPFullDirection m n) (γ : ℝ) : Prop where
  null_eqs : HLPNullspaceEquations P D
  component_eq : ∀ i,
    w.x i * D.ds i + w.s i * D.dx i = γ * mu w - w.x i * w.s i
  scalar_eq :
    w.tau * D.dkappa + w.kappa * D.dtau = γ * mu w - w.tau * w.kappa

/-- Right-hand side of the complementarity part of the YTM Newton system. -/
def complRhs {n : Nat} (w : HSState n) (γ : ℝ) : Vec n :=
  fun i => γ * mu w - w.x i * w.s i

/-- Right-hand side of the scalar complementarity equation. -/
def scalarComplRhs {n : Nat} (w : HSState n) (γ : ℝ) : ℝ :=
  γ * mu w - w.tau * w.kappa

/-- The full HLP Newton block operator, written as equations rather than as a single
matrix.  The output consists of the four HLP nullspace residuals and the
`n+1` complementarity residuals.  Thus solving the Newton system means finding
`D` such that this operator equals the right-hand side encoded below.

For the homogeneous self-dual LP of Ye--Todd--Mizuno, the first four blocks are the
linearized HLP equalities, while the last two blocks are the linearized complementarity
equations. -/
structure HLPNewtonBlockSystem {m n : Nat}
    (P : LPData m n) (w : HSState n) (D : HLPFullDirection m n) (γ : ℝ) : Prop where
  primal_block : ∀ i : Fin m,
    matVec P.A D.dx i - P.b i * D.dtau + bbar P i * D.dtheta = 0
  dual_block : ∀ j : Fin n,
    -(tMatVec P.A D.dy j) + P.c j * D.dtau - cbar P j * D.dtheta - D.ds j = 0
  gap_block :
    dot P.b D.dy - dot P.c D.dx + zbar P * D.dtheta - D.dkappa = 0
  normalizing_block :
    -(dot (bbar P) D.dy) + dot (cbar P) D.dx - zbar P * D.dtau = 0
  complementarity_block : ∀ i : Fin n,
    w.x i * D.ds i + w.s i * D.dx i = complRhs w γ i
  scalar_complementarity_block :
    w.tau * D.dkappa + w.kappa * D.dtau = scalarComplRhs w γ

/-- The block-system formulation is equivalent to the previous bundled full
direction equation.  This direction is useful because the block system exposes the
Newton matrix whose nonsingularity must be proved from full row rank and interiority. -/
theorem full_direction_equation_iff_block_system {m n : Nat}
    (P : LPData m n) (w : HSState n) (D : HLPFullDirection m n) (γ : ℝ) :
    HLPFullDirectionEquation P w D γ ↔ HLPNewtonBlockSystem P w D γ := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact h.null_eqs.primal_eq
    · exact h.null_eqs.dual_eq
    · exact h.null_eqs.gap_eq
    · exact h.null_eqs.normalizing_eq
    · intro i
      exact h.component_eq i
    · exact h.scalar_eq
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · exact ⟨h.primal_block, h.dual_block, h.gap_block, h.normalizing_block⟩
    · intro i
      exact h.complementarity_block i
    · exact h.scalar_complementarity_block



/-- Homogeneous version of the full Newton block system.

This is the kernel system obtained by replacing the complementarity right-hand side by
zero.  Proving that its only solution is zero is the standard injectivity step in the
finite-dimensional solvability proof of the HLP Newton equations. -/
structure HLPNewtonHomogeneousBlockSystem {m n : Nat}
    (P : LPData m n) (w : HSState n) (D : HLPFullDirection m n) : Prop where
  primal_block : ∀ i : Fin m,
    matVec P.A D.dx i - P.b i * D.dtau + bbar P i * D.dtheta = 0
  dual_block : ∀ j : Fin n,
    -(tMatVec P.A D.dy j) + P.c j * D.dtau - cbar P j * D.dtheta - D.ds j = 0
  gap_block :
    dot P.b D.dy - dot P.c D.dx + zbar P * D.dtheta - D.dkappa = 0
  normalizing_block :
    -(dot (bbar P) D.dy) + dot (cbar P) D.dx - zbar P * D.dtau = 0
  complementarity_block : ∀ i : Fin n,
    w.x i * D.ds i + w.s i * D.dx i = 0
  scalar_complementarity_block :
    w.tau * D.dkappa + w.kappa * D.dtau = 0


/-! ### Finite-dimensional solvability of the full Newton block

The solvability step is a purely finite-dimensional linear-algebra argument.  We
encode the unknowns `(dy,dx,dτ,dθ,ds,dκ)` and the six residual blocks in the same
product vector space.  The concrete Newton block is then a linear self-map on this
space.  Since the homogeneous block has only the zero solution, the self-map is
injective; in finite dimension, injectivity of a self-map implies surjectivity. -/

/-- Product vector space used for the full HLP Newton unknowns and residuals. -/
abbrev HLPBlockSpace (m n : Nat) := Vec m × Vec n × ℝ × ℝ × Vec n × ℝ

/-- Encode a full HLP direction as a vector in the product block space. -/
def HLPFullDirection.toBlockVector {m n : Nat} (D : HLPFullDirection m n) :
    HLPBlockSpace m n :=
  (D.dy, D.dx, D.dtau, D.dtheta, D.ds, D.dkappa)

/-- Decode a product block vector as a full HLP direction. -/
def HLPFullDirection.ofBlockVector {m n : Nat} (u : HLPBlockSpace m n) :
    HLPFullDirection m n :=
  { dy := u.1
    dx := u.2.1
    dtau := u.2.2.1
    dtheta := u.2.2.2.1
    ds := u.2.2.2.2.1
    dkappa := u.2.2.2.2.2 }

@[simp] theorem HLPFullDirection.of_toBlockVector {m n : Nat}
    (D : HLPFullDirection m n) :
    HLPFullDirection.ofBlockVector (HLPFullDirection.toBlockVector D) = D := by
  cases D
  rfl

@[simp] theorem HLPFullDirection.to_ofBlockVector {m n : Nat}
    (u : HLPBlockSpace m n) :
    HLPFullDirection.toBlockVector (HLPFullDirection.ofBlockVector u) = u := by
  rcases u with ⟨dy, dx, dtau, dtheta, ds, dkappa⟩
  rfl

/-- Right-hand side of the full Newton block system in the same block space. -/
def HLPNewtonBlockRhs {n : Nat} (w : HSState n) (γ : ℝ) (m : Nat) :
    HLPBlockSpace m n :=
  (0, 0, 0, 0, complRhs w γ, scalarComplRhs w γ)


/-!
This file contains the stable foundation: data structures, elementary HSDE/HLP
definitions, and basic algebraic identities used by the work file.
It intentionally stops before `HLPNewtonBlockOperator`, where the current active
proof engineering is happening.
-/

end HSDInteriorPointLP
