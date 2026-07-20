/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import LeanPool.LeanQuantumAlg.Init
public import LeanPool.LeanQuantumAlg.Primitives.QKernel.Fidelity
public import LeanPool.LeanQuantumAlg.Primitives.QKernel.Fourier
public import LeanPool.LeanQuantumAlg.Primitives.QKernel.Concentration
public import LeanPool.LeanQuantumAlg.Primitives.QKernel.DiscreteLogConcept
public import LeanPool.LeanQuantumAlg.Primitives.QKernel.Advantage
public import LeanPool.LeanQuantumAlg.Primitives.QKernel.Expressivity

/-!
# Quantum kernels

Umbrella module for the quantum-kernel development; re-exports the genuine results.

- `QKernel.Fidelity` — the fidelity quantum kernel and its Gram-matrix positive
  semidefiniteness (`quantumKernel_gram_posSemidef`).
- `QKernel.Fourier` — the Fourier representation of quantum kernels
  (`fourier_representation`, Schuld 2021).
- `QKernel.Concentration` — exponential concentration of the tensor-product RY kernel
  (`ryKernel_concentrates`, Thanasilp 2022).
- `QKernel.DiscreteLogConcept` / `QKernel.Advantage` — the discrete-log concept class
  (secret-homogeneity `acc_shift`) and the conditional learning-advantage separation
  (`QuantumKernelAdvantage.separation`, Liu 2021).
- `QKernel.Expressivity` — density-matrix realization of feature-map kernels
  (`eqk_realizes`, Gil-Fuster 2023).
-/

@[expose] public section
