/-
Copyright (c) 2026 Yash Kanoria. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yash Kanoria
-/
module


public import LeanPool.FullyDynamicMatching.FD1D.V5.CompleteFormalizationAudit

/-!
# Palomar solution

The imported development proves
`FD1D.V5.Palomar.optimalDynamicMatchingUpperBound`. Its local
`CompleteFormalizationAudit` checks proof closure and the permitted axioms.

The independent Mathlib-only statement is retained in the
[upstream Challenge.lean](https://github.com/ykanoria/fd1d-lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/Challenge.lean).
The [upstream verification instructions](https://github.com/ykanoria/fd1d-lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/README.md#verification)
describe its comparator check. Those comparison artifacts are not included in
this Lean Pool import; the local proof-closure audit does not perform that comparison.
-/
