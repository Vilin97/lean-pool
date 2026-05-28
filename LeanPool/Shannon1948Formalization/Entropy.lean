/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import LeanPool.Shannon1948Formalization.Entropy.Properties
import LeanPool.Shannon1948Formalization.Entropy.Converse

/-!
# Shannon.Entropy

Facade module for the Shannon entropy formalization.

Import this file to access the full development:
- Characterization theorems (Appendix 2): `entropyNat_unique`, `entropyBase_unique`
- Converse: `entropyNat_shannonAxioms` (entropy satisfies the formal conditions)
- Section 6 properties: nonnegativity, maximum at uniform, subadditivity,
  conditioning reduces entropy, chain rule, product additivity

## Module chain

`Core → Uniform → Rational → Approx → Final → Gibbs → Joint → Properties`
                                                    ↘ Converse
-/
