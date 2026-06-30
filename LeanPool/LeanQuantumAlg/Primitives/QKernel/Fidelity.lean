/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import LeanPool.LeanQuantumAlg.Init
public import LeanPool.LeanQuantumAlg.Core.State
public import LeanPool.LeanQuantumAlg.Core.Tensor
public import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Quantum kernel methods: the fidelity kernel and its Gram-matrix positive semidefiniteness

A data-encoding *quantum feature map* sends a classical input `x` to a quantum
state `|φ(x)⟩`. The induced *fidelity quantum kernel* is
`k(x, y) = |⟨φ(x) | φ(y)⟩|²` (for pure states this equals `tr[ρ(x) ρ(y)]`,
the Hilbert–Schmidt inner product of the density operators). The core fact that
makes such a `k` a legitimate kernel for classical kernel methods (SVMs, etc.)
is that every Gram matrix `K_{ij} = k(xᵢ, xⱼ)` is positive semidefinite.

The proof realizes the fidelity kernel as a genuine inner-product Gram matrix:
with the feature vector `w(x) := φ(x) ⊗ conj φ(x)` one has
`⟨w(x), w(y)⟩ = ⟨φ(x), φ(y)⟩ · conj⟨φ(x), φ(y)⟩ = |⟨φ(x), φ(y)⟩|²`
(via `PureState.inner_tensor_tensor`), so the kernel Gram matrix factors as
`K = Bᴴ B` and is positive semidefinite by
`Matrix.posSemidef_conjTranspose_mul_self`.

Sources: Schuld & Killoran (2019), *Quantum machine learning in feature Hilbert
spaces*; Schuld (2021), *Supervised quantum machine learning models are kernel
methods*.

## Main definitions / results

- `LeanPool.LeanQuantumAlg.PureState.conjState` — elementwise complex conjugate of a state.
- `LeanPool.LeanQuantumAlg.quantumKernel` — the fidelity quantum kernel `|⟨φ(x), φ(y)⟩|²`.
- `LeanPool.LeanQuantumAlg.quantumKernel_eq_inner_featureTensor` — the kernel as an inner
  product of feature vectors `φ(x) ⊗ conj φ(x)`.
- `LeanPool.LeanQuantumAlg.quantumKernel_gram_posSemidef` — the kernel Gram matrix is
  positive semidefinite (the validity-of-the-kernel theorem). Being
  positive semidefinite it is in particular Hermitian, i.e. symmetric.
- `LeanPool.LeanQuantumAlg.quantumKernel_self` — the diagonal value on a pure state.
-/

@[expose] public section

namespace QuantumAlg

namespace PureState

section

variable {n : ℕ}

/-- Elementwise complex conjugate of a pure state. -/
noncomputable def conjState (ψ : PureState n) : PureState n :=
  ofVec (WithLp.toLp 2 fun i => starRingEnd ℂ (ψ i)) (by
    calc
      ‖WithLp.toLp 2 (fun i => starRingEnd ℂ (ψ i))‖
          = ‖(ψ : StateVector n)‖ := by
            rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
            congr 1
            exact Finset.sum_congr rfl fun i _ => by simp
      _ = 1 := ψ.norm_eq_one)

@[simp]
theorem conjState_apply (ψ : PureState n) (i : Fin (2 ^ n)) :
    conjState ψ i = starRingEnd ℂ (ψ i) := rfl

/-- Conjugating both arguments conjugates the inner product. -/
theorem inner_conjState (a b : PureState n) :
    inner ℂ (conjState a) (conjState b) = starRingEnd ℂ (inner ℂ a b) := by
  change inner ℂ ((conjState a : PureState n) : StateVector n)
      ((conjState b : PureState n) : StateVector n)
    = starRingEnd ℂ (inner ℂ (a : StateVector n) (b : StateVector n))
  simp only [PiLp.inner_apply, RCLike.inner_apply, conjState_apply, map_sum, map_mul]

end

end PureState

noncomputable section

variable {n : ℕ} {X : Type*}

/-- The feature vector `φ(x) ⊗ conj φ(x)` whose inner products realize the
fidelity kernel as a Gram matrix. -/
def featureTensor (φ : X → PureState n) (x : X) : PureState (n + n) :=
  (φ x).tensor (PureState.conjState (φ x))

/-- The fidelity quantum kernel `k(x, y) = |⟨φ(x), φ(y)⟩|²`, written as the
complex product `⟨φ(x), φ(y)⟩ · conj⟨φ(x), φ(y)⟩` (a nonnegative real). -/
def quantumKernel (φ : X → PureState n) (x y : X) : ℂ :=
  inner ℂ (φ x) (φ y) * starRingEnd ℂ (inner ℂ (φ x) (φ y))

/-- The fidelity kernel is the inner product of the feature vectors
`φ(·) ⊗ conj φ(·)`. -/
theorem quantumKernel_eq_inner_featureTensor (φ : X → PureState n) (x y : X) :
    quantumKernel φ x y = inner ℂ (featureTensor φ x) (featureTensor φ y) := by
  rw [featureTensor, featureTensor, PureState.inner_tensor_tensor,
    PureState.inner_conjState, quantumKernel]

/-- The diagonal kernel value is `1`. -/
theorem quantumKernel_self (φ : X → PureState n) (x : X) :
    quantumKernel φ x x = 1 := by
  have hself : inner ℂ (φ x) (φ x) = (1 : ℂ) := by
    change inner ℂ ((φ x : PureState n) : StateVector n) ((φ x : PureState n) : StateVector n)
      = (1 : ℂ)
    rw [inner_self_eq_norm_sq_to_K, (φ x).norm_eq_one]
    norm_num
  rw [quantumKernel, hself, map_one, mul_one]

open scoped ComplexOrder

/-- **Validity of the quantum kernel.** For any finite family of inputs, the
fidelity-kernel Gram matrix `K_{ij} = k(xᵢ, xⱼ)` is positive semidefinite, hence
`k` is a legitimate (positive-semidefinite) kernel. -/
theorem quantumKernel_gram_posSemidef {ι : Type*} [Finite ι]
    (φ : X → PureState n) (x : ι → X) :
    (Matrix.of fun i j => quantumKernel φ (x i) (x j)).PosSemidef := by
  letI := Fintype.ofFinite ι
  have hK : (Matrix.of fun i j => quantumKernel φ (x i) (x j))
      = (Matrix.of fun (k : Fin (2 ^ (n + n))) (i : ι) => featureTensor φ (x i) k).conjTranspose
        * Matrix.of fun (k : Fin (2 ^ (n + n))) (i : ι) => featureTensor φ (x i) k := by
    ext i j
    rw [Matrix.of_apply, quantumKernel_eq_inner_featureTensor, Matrix.mul_apply]
    change inner ℂ ((featureTensor φ (x i) : PureState (n + n)) : StateVector (n + n))
        ((featureTensor φ (x j) : PureState (n + n)) : StateVector (n + n))
      = ∑ x_1, (Matrix.of fun k i => featureTensor φ (x i) k).conjTranspose i x_1 *
          (Matrix.of fun k i => featureTensor φ (x i) k) x_1 j
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [RCLike.inner_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.of_apply,
      starRingEnd_apply]
    ring
  rw [hK]
  exact Matrix.posSemidef_conjTranspose_mul_self _

namespace QuantumKernel

/-- Main theorem: fidelity quantum-kernel Gram matrices are positive semidefinite. -/
theorem main {ι : Type*} [Finite ι] (φ : X → PureState n) (x : ι → X) :
    (Matrix.of fun i j => quantumKernel φ (x i) (x j)).PosSemidef :=
  quantumKernel_gram_posSemidef φ x

/-- Public supporting theorem: the fidelity kernel is an inner product after tensor lifting. -/
theorem main_feature_tensor (φ : X → PureState n) (x y : X) :
    quantumKernel φ x y = inner ℂ (featureTensor φ x) (featureTensor φ y) :=
  quantumKernel_eq_inner_featureTensor φ x y

/-- Public supporting theorem: the diagonal fidelity-kernel value of a pure state is one. -/
theorem main_self (φ : X → PureState n) (x : X) :
    quantumKernel φ x x = 1 :=
  quantumKernel_self φ x

end QuantumKernel

end

end QuantumAlg
