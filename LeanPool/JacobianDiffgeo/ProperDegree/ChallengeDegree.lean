/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.MappingDegree

/-!
# The challenge-signature mapping degree (proper-map-degree, file 1 of 3)

Unit: proper-map-degree (`docs/design/proper-map-degree.md` §3.1). Root-level wrapper of
`RS.degree` (`Jacobian/MappingDegree/Degree.lean`) matching the EXACT signature the challenge
file (`docs/Jacobian_challenge.lean:147`) demands.

* `_root_.ContMDiff.degree (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) : ℕ` — the degree of a
  holomorphic map between compact Riemann surfaces; `0` for constant maps, else `RS.degree f`.
* `ContMDiff.degree_eq`, `ContMDiff.degree_of_forall_eq`, `ContMDiff.degree_comp` — restated
  corollaries in wrapper form (statement bank, API parity with `RS.degree`/`RS.degree_comp`).

**Deviation from the design doc** (`proper-map-degree.md` §3.1): the design's sketch declared
`variable {f : X → Y}` (implicit). The challenge file's own preamble
(`docs/Jacobian_challenge.lean:104`, `variable (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)`)
declares `f` **explicit** — confirmed load-bearing by its own call site
`pushforward_pullback`'s RHS `(ContMDiff.degree f hf) • P`, which applies `f` positionally. To
match "the exact challenge signature" this file declares `f` explicit throughout; `hf.degree`
(dot notation) still works since `f` is fully determined by unification against `hf`'s type.
-/

open scoped ContDiff Manifold

namespace RS.ProperDegree

variable {X Y : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]

/-- The degree of a holomorphic map between compact Riemann surfaces (challenge signature,
`docs/Jacobian_challenge.lean:147`). Equal to `0` for constant maps (`RS.degree_of_forall_eq`),
otherwise the usual mapping degree (`RS.degree`). One-line wrapper — `RS.degree` already has the
right junk-`0` convention definitionally, no case split needed. `[Nonempty Y]` (needed by
`RS.degree`) is discharged for free by `ConnectedSpace.toNonempty`
(`Mathlib.Topology.Connected.Basic:636`). -/
noncomputable def _root_.ContMDiff.degree (f : X → Y) (_hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) : ℕ :=
  RS.degree f

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ, ℂ) ω X] [T2Space Y]
    [CompactSpace Y] [IsManifold 𝓘(ℂ, ℂ) ω Y] in
@[simp] theorem _root_.ContMDiff.degree_eq (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    hf.degree = RS.degree f := rfl

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ, ℂ) ω X] [T2Space Y]
    [CompactSpace Y] [IsManifold 𝓘(ℂ, ℂ) ω Y] in
/-- Restated junk convention in wrapper form (`RS.degree_of_forall_eq`, unfolded). -/
theorem _root_.ContMDiff.degree_of_forall_eq {c : Y}
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun _ : X => c)) : hf.degree = 0 := by
  rw [ContMDiff.degree_eq]; exact RS.degree_of_forall_eq c

/-- Functoriality, restated in wrapper form (statement bank; no critical consumer identified,
kept for API parity with `RS.degree_comp`). -/
theorem _root_.ContMDiff.degree_comp {Z : Type*} [TopologicalSpace Z] [T2Space Z]
    [ConnectedSpace Z] [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ) ω Z]
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g)
    (hneG : ¬ ∃ c, ∀ y, g y = c) (hneF : ¬ ∃ c, ∀ x, f x = c) :
    (hg.comp hf).degree = hg.degree * hf.degree := by
  simp only [ContMDiff.degree_eq]; exact RS.degree_comp hg hf hneG hneF

end RS.ProperDegree
