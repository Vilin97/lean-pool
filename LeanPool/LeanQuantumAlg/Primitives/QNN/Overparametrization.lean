/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import LeanPool.LeanQuantumAlg.Init
public import Mathlib.Order.Monotone.Basic

/-!
# Overparametrization of quantum neural networks

A quantum neural network (QNN) becomes **overparametrized** once it has enough
parameters that the achievable quantum-Fisher-information rank saturates its
dynamical-Lie-algebra (DLA) bound: the maximal rank is bounded by `dim g_S`, so
beyond the critical parameter count `M_c ≤ dim g_S` no new directions of the state
space are explored (Larocca et al. 2021, *Theory of overparametrization in QNNs*).

This module records that structural relationship abstractly, in the
`GroverModel`/`ParamShiftModel` style: the hard analytic input — the Fisher rank is
bounded by the DLA dimension and is monotone in the parameter count — is bundled as
the hypotheses of `QNNOverparametrization`, and the structural consequences (the
capacity bound and the persistence of overparametrization, i.e. the trainability
"phase transition") are derived. Here `dlaDim` is an abstract natural number
standing for `dim g_S`; its
formal identification with the `Module.finrank` of the formalized
`LeanPool.LeanQuantumAlg.dynamicalLieAlgebra` is **not yet wired in** (deferred — `dlaDim` is an
opaque parameter, not connected in Lean to the DLA construction).

Source: Larocca, Ju, García-Martín, Coles, Cerezo (2021), arXiv:2109.11676.

## Main results

- `LeanPool.LeanQuantumAlg.QNNOverparametrization` — the abstract overparametrization data.
- `LeanPool.LeanQuantumAlg.QNNOverparametrization.fisherRank_le` — capacity bound: the rank
  never exceeds `dim g_S`.
- `LeanPool.LeanQuantumAlg.QNNOverparametrization.isOverparametrized_stays` — once
  overparametrized, adding parameters keeps the QNN overparametrized.
-/

@[expose] public section

namespace QuantumAlg

/-- Abstract overparametrization data for a QNN: a number of parameters, the
dimension of its dynamical Lie algebra, and the achievable quantum-Fisher-information
rank as a (monotone) function of the parameter count, bounded by the DLA dimension. -/
structure QNNOverparametrization where
  /-- Abstract stand-in for the dimension of the dynamical Lie algebra `g_S` (an
  opaque `ℕ`; not yet identified in Lean with `finrank` of `dynamicalLieAlgebra`). -/
  dlaDim : ℕ
  /-- Achievable quantum-Fisher-information-matrix rank as a function of the number
  of parameters. -/
  fisherRank : ℕ → ℕ
  /-- Capacity bound (Larocca et al. 2021): the rank never exceeds `dim g_S`. -/
  rank_le_dlaDim : ∀ M, fisherRank M ≤ dlaDim
  /-- More parameters cannot decrease the achievable rank. -/
  rank_mono : Monotone fisherRank

namespace QNNOverparametrization

variable (Q : QNNOverparametrization)

/-- The QNN is **overparametrized** at `M` parameters when the achievable Fisher
rank has saturated its dynamical-Lie-algebra bound. -/
def IsOverparametrized (M : ℕ) : Prop := Q.fisherRank M = Q.dlaDim

/-- Capacity bound: the achievable rank never exceeds the DLA dimension. -/
theorem fisherRank_le (M : ℕ) : Q.fisherRank M ≤ Q.dlaDim := Q.rank_le_dlaDim M

/-- Since the rank is always bounded by `dlaDim`, overparametrization is exactly
saturation of that bound from below. -/
theorem isOverparametrized_iff (M : ℕ) :
    Q.IsOverparametrized M ↔ Q.dlaDim ≤ Q.fisherRank M := by
  unfold IsOverparametrized
  constructor
  · intro h; rw [h]
  · intro h; exact le_antisymm (Q.rank_le_dlaDim M) h

/-- **Persistence of overparametrization.** Once overparametrized at `M`, the QNN
stays overparametrized for any `M' ≥ M` — the trainability "phase transition" is
monotone in the parameter count. -/
theorem isOverparametrized_stays {M M' : ℕ} (h : M ≤ M')
    (hover : Q.IsOverparametrized M) : Q.IsOverparametrized M' := by
  rw [isOverparametrized_iff] at hover ⊢
  exact hover.trans (Q.rank_mono h)

end QNNOverparametrization

end QuantumAlg
