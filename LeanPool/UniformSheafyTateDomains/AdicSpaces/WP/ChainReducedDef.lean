/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/
module


/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.Presheaf

/-!
# Rational stable reducedness — the definition ([WP] def:rationally-stably-reduced)

The chain recursion `ChainReduced` formalizing "every finite iterated rational
localization is reduced". Split out of `WP/Reduced.lean` so the definition is
importable without that file's proofs (definition layer / proving layer hygiene,
as for the rest of the weighted-parity example).
-/

@[expose] public section

@[expose] public section

namespace WeightedParity

open ValuationSpectrum

/-- Finite chains of rational localizations, and reducedness all the way down
([WP] def:rationally-stably-reduced: "every finite iterated rational localization is
reduced").  `ChainReduced A n` says: `A` itself and every iterated rational
localization of depth `≤ n` is reduced (cumulative successor form per the 2026-07-28
ChatGPT-5.6 plan review, so each level records all shallower depths too). -/
def ChainReduced : (A : Type _) → [inst : CommRing A] → [inst : TopologicalSpace A] →
    [inst : IsTopologicalRing A] → ℕ → Prop
  | A, _, _, _, 0 => IsReduced A
  | A, _, _, _, (n + 1) => IsReduced A ∧ ∀ D : RationalLocData A, D.IsRational →
      ChainReduced (presheafValue D) n

end WeightedParity
