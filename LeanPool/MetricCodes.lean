/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

import LeanPool.MetricCodes.Conclusion

/-!
# Improved asymptotic bounds for binary and spherical codes

Source: url:https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6
Authors: OpenAI, Dean Cureton
Status: verified
Main declarations: `MetricCodes.Johnson.main_binary_theorem`
Tags: coding-theory, spherical-codes, kissing-number, harmonic-analysis, asymptotic-bounds
MSC: 94B65, 52C17, 41A60
-/

/-!
## Provenance

OpenAI developed the formalization. Dean Cureton subsequently optimized it at revision
`30c21d72a2ee3308d66c945387729d736e0cb305` of his `ten-proofs` fork; those optimizations are
incorporated here, while the canonical OpenAI revision remains recorded in the project card.
-/
