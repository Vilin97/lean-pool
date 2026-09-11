/-
Copyright (c) 2024 Sidharth Hariharan and 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Sidharth Hariharan, Gareth Ma, Dean Cureton
-/

import LeanPool.SpherePacking.Conclusion

/-!
# Sharp asymptotic upper bounds for sphere packing

Source: url:https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6
Authors: OpenAI, Sidharth Hariharan, Gareth Ma, Dean Cureton
Status: verified
Main declarations: `PackingBounds.sharpFullCohnElkiesManuscriptConclusions`
Tags: sphere-packing, discrete-geometry, harmonic-analysis, linear-programming-bounds
MSC: 52C17, 41A60, 42A38
-/

/-!
## Provenance

OpenAI developed the main proof and its supporting analysis. The sphere-packing foundations adapt
work by Sidharth Hariharan and Gareth Ma from the Sphere Packing in Lean project, whose broader
contributors include Christopher Birkbeck, Seewoo Lee, Bhavik Mehta, and Maryna Viazovska. Dean
Cureton subsequently optimized the formalization at revision
`30c21d72a2ee3308d66c945387729d736e0cb305` of his `ten-proofs` fork before its migration into
Lean Pool; the canonical OpenAI source revision remains recorded separately in the project card.
-/
