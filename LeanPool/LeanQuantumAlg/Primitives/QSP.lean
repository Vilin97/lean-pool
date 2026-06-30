/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import LeanPool.LeanQuantumAlg.Init
public import LeanPool.LeanQuantumAlg.Primitives.QSP.Chebyshev
public import LeanPool.LeanQuantumAlg.Primitives.QSP.Fourier

/-!
# Quantum signal processing (single qubit)

Quantum signal processing (QSP) interleaves a fixed one-parameter *signal*
rotation with tunable *processing* phase rotations and characterizes exactly
which `SU(2)`-valued polynomial transforms of the signal are achievable.

This is the umbrella module for the single-qubit QSP development. It splits by
polynomial basis and re-exports both halves:

- `LeanPool.LeanQuantumAlg.Primitives.QSP.Chebyshev` — the Chebyshev-basis
  forms: the reflection-derived **O-convention** (`qsp_reflection_iff`) and the
  **Wx-convention / XZX form** (`qsp_wx_iff`), characterized by `IsQSPPair`.
- `LeanPool.LeanQuantumAlg.Primitives.QSP.Fourier` — the Fourier-basis (trigonometric)
  forms: the **YZY** (`qsp_yzy_iff`) and **YZZYZ / W-Z-W** (`qsp_yzzyz_iff`)
  quantum-neural-network forms, characterized by `IsYZYPair`/`IsYZPair` through
  the Laurent encoding `lEval`.

The two families are genuinely different transforms with different inputs
(Chebyshev polynomials in `x ∈ [-1,1]` vs. Laurent/Fourier polynomials in
`e^{ix/2}`); a cross-convention bridge (`x = cos θ`) is left as future work.

## Main results (registered targets)

- `LeanPool.LeanQuantumAlg.ReflectionBasedQuantumSignalProcessing.main`,
  `LeanPool.LeanQuantumAlg.ReflectionBasedQuantumSignalProcessing.main_wx` —
  Chebyshev basis.
- `LeanPool.LeanQuantumAlg.qsp_yzy_iff`, `LeanPool.LeanQuantumAlg.qsp_yzzyz_iff` — Fourier basis.
-/

@[expose] public section
