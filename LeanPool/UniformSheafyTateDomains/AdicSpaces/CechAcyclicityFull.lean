/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornCechAcyclicity

/-!
# All-degree Čech acyclicity of rational covers (campaign C)

Wedhorn's Lemmas 8.33 and 8.34 are **all-degree** statements: for a 2-cover the
augmented alternating complex `0 → O(X) → O(U₁) × O(U₂) → O(U₁∩U₂) → 0` is exact
([Wedhorn] l.4151), and `O_X`-acyclicity of the ideal-generated covers follows by
the Prop A.3 product/refinement calculus.

**C-L1 is proven**: the missing degree for the 2-cover — surjectivity of the
difference map onto the overlap value — is `unitCover_delta_surjective`
(WedhornCechAcyclicity.lean, beside `unitCover_isOXAcyclic`; it lives there because
it is assembled from that file's private Example 6.38/6.39 bridges and the
axiom-clean `LaurentCover.row3_exact` δ-surjectivity). Together the two theorems
give the full exactness of the augmented 2-cover complex.

The remaining campaign-C layers (the API gap C-AG1, `decomposition.md`):
multi-intersection data and the Čech complex on `RationalCoveringData` in all
degrees (note: `CechCohomology.lean`'s `CechCochain` is the **unnormalized**
complex — a comparison with the alternating complex, or a degeneracy contraction,
is a required layer per the validation addendum), the A.3 product/refinement
calculus in all degrees, and the per-example headlines (`JetA` via the Milnor LES
of augmented algebraic complexes in `ModuleCat`; `WPA` via coefficientwise
`c₀`-primitives with per-degree open-mapping bounds,
`ContinuousLinearMap.exists_preimage_norm_le`).
-/
