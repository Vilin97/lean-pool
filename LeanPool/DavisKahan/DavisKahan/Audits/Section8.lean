/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section8.Presentation
public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section8.Theorem81MajorizationReal

/-!
# Dependency audit for Davis--Kahan 1970 Section 8

This is the audit leaf for the **actual final capstones** of Section 8.  It
lives downstream of the analytic layer because that is where Section 8's
analytic content lives; the upstream leaf
`DavisKahan/Sources/DavisKahan1970/Audits/Section8.lean` continues to audit the
internal infrastructure, which is no longer evidence about the printed
theorems.

Every target below should report exactly

```
[propext, Classical.choice, Quot.sound]
```

and nothing project-local.
-/

@[expose] public section

namespace TauCeti
namespace DavisKahan1970
namespace Section8

/-! ## Theorem 8.1: the branch, its characterization, its uniqueness -/

/-! ## Theorem 8.1(i), both blocks -/

/-! ## Theorem 8.1(ii), both blocks

The shared Weyl step, the dimension-free approximation-number statements, and
the printed angle form. -/

/-! ## Theorem 8.1(iii), both blocks

The weak-majorization cores, the every-symmetric-gauge forms, the printed angle
forms, and the paper's increasing index order. -/

/-! ## Theorem 8.1(ii) and 8.1(iii) over a REAL Hilbert space, both blocks

The real branch, its sharp form bounds, the dimension-free part (ii) endpoints
and the finite-dimensional part (iii) endpoints. -/

/-! ## The eigenvalue/angle source dictionary -/

/-! ## The generic sandwich majorization behind part (iii) -/

/-! ## Theorem 8.2

Both alternatives from the printed hypotheses, the inherited `sin 2Θ`
estimates, the Krein completion, equation (1.5), and the printed `Θ < π/4`. -/

end Section8
end DavisKahan1970
end TauCeti
