/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.AdicMorphismsCore
import LeanPool.UniformSheafyTateDomains.AdicSpaces.AdicSpaceMorphisms

/-!
# Adic morphisms — aggregator

`import «Adic spaces».AdicMorphisms` exposes both the ring-level adicness API
(`IsAdicHom`, `isAdicHom_iff_preserves_analytic`, … — `AdicMorphismsCore.lean`) and
the space-level provisional layer (`PresentationIsAdicMorphism` — NOT Definition 8.38, see its docstring;
`PresentationAffinoidNeighborhood`, … — `AdicSpaceMorphisms.lean`, downstream of the genuine
structure-presheaf space definitions). The split exists because the space layer
consumes `AffinoidAdicPresentation`, which lives downstream of the sheaf-condition
equivalences, while `SpaCompactNoHArch.lean` (upstream) needs the ring-level part.
-/
