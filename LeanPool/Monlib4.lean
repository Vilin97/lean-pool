/-
Copyright (c) 2026 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/

import LeanPool.Monlib4.Monlib

/-!
# Monlib4 Operator-Algebra and Quantum-Set Core

Source: arxiv:1810.08368, doi:10.4169/amer.math.monthly.124.10.966
Authors: Monica Omar
Status: verified
Main declarations: `Matrix.aut_mat_inner`, `QuantumSet`, `schurMul`, `QuantumGraph`
Tags: linear-algebra, operator-algebras, quantum-sets, quantum-graphs, representation-theory
MSC: 15A69, 16W20
-/

/-!
## Mathematical overview

A theorem-bearing subset of `monlib4` — a Lean 4 formalization of
non-commutative graph theory. The upstream library builds quantum-graph and
quantum-set theory on substantial matrix / inner-product-space infrastructure.

This vendored subset includes the upstream matrix-algebra automorphism theorem:
every automorphism of a finite matrix algebra over a field is inner, implemented
by conjugation with an invertible matrix (`Matrix.aut_mat_inner` and
`Matrix.aut_mat_inner'`). As a corollary, such automorphisms preserve trace
(`Matrix.aut_mat_inner_trace_preserving`).

The recovered downstream operator-algebra layer adds unitary inner
star-algebra automorphisms (`unitary.innerAutStarAlg`), their matrix
specialization as linear maps (`Matrix.innerAut`), and preservation results for
trace, spectrum, multiplication, star, inverses, and Hermitian matrices.  The
quantum-set core now includes `starAlgebra`, `InnerProductAlgebra`,
`QuantumSet`, the modular-automorphism identities, the complex quantum set
instance `Complex.quantumSet`, finite product quantum sets, delta-form quantum
sets, and the star-preserving map API `LinearMap.IsReal` / `LinearMap.real`.
The recovered quantum-graph core includes the Schur product `schurMul`, Schur
projections, and the predicates `QuantumGraph` / `QuantumGraph.Real`.

The supporting imported infrastructure also includes a `Matrix.reshape` linear
equivalence between `Mₙₓₘ(R)` and `Rⁿˣᵐ`, the entrywise conjugate `Matrix.conj`
with the `ᴴᵀ` notation, the projection `directSumFromTo` between summands of a
dependent direct sum, basic spectrum commutativity (`isUnit_comm`,
`spectrum.comm`), the `PiMat` matrix-family abbreviation, permutation-matrix
unitarity, self-adjoint/inner-product extensionality lemmas, strict
tensor-product coercions, left/right multiplication maps and bimodule maps on
tensor products, the finite-dimensional Hilbert-algebra coalgebra instance,
coalgebras on multiplicative opposites, and helper lemmas for finite sums,
ites/dites, digit-sum divisibility in arbitrary bases, and `RCLike`-valued
order relations.

## Provenance

Imported from <https://github.com/themathqueen/monlib4> (originally Lean
`v4.21.0-rc3`) and ported to Lean Pool's `v4.30.0-rc2` / Mathlib `v4.30.0-rc2`.
The successor of <https://github.com/themathqueen/monlib> (the Lean 3 version).
Large parts of the upstream quantum-graph and Schur-product theorem stack are
not yet vendored. In particular, upstream modules such as
`QuantumGraph.OfClassicalGraph` and the deeper theorem sections of
`QuantumSet.SchurMul` / `QuantumGraph.Basic` depend on the older
`PiLp`/normed-ring scaffold and upstream heartbeat or linter overrides that
Lean Pool does not permit.
-/
