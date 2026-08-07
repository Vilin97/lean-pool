/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.Abel.Loops
import LeanPool.JacobianDiffgeo.TailDuality
import LeanPool.JacobianDiffgeo.LaurentTail
import LeanPool.JacobianDiffgeo.DolbeaultComparison
import LeanPool.JacobianDiffgeo.CanonicalForms

/-!
# abel-theorem: the Dolbeault-upgrade bridge, RESTATED at the tail level (design §4.3 D3)

Unit: abel-theorem. Namespace `RS.Abel`.

## Status: the abstract bridge is now PROVEN (gated on `serre-duality-tails`'s own one remaining
external blocker), replacing the ORIGINAL design's blocked statement

The design (`docs/design/abel-theorem.md` §4.3) planned this bridge as a composite of
`holomorphicMFormsEquiv` (canonical-forms) + `resEquiv 0` composed with `H1Tail.equiv`
(serre-duality-tails' FULL, unconditional Čech comparison `H1Tail 0 ≃ₗ Cech.H1 0`) +
`dolbeaultEquiv` (dolbeault-comparison). By the time `serre-duality-tails` (`Jacobian/TailDuality/`)
actually landed, its own root docstring flagged that `H1Tail.equiv` does **not exist**: the
Čech-comparison direction `H1Tail D ≃ₗ Cech.H1 D` needs `LaurentTail.tailToH1`'s **surjectivity**,
which is a genuine, out-of-scope Mittag-Leffler/Cousin-I-style existence theorem (`laurent-tails`'
own `Comparison.lean` file-end note), *not* a bookkeeping gap — only the UNCONDITIONAL injectivity
(`H1Tail.toH1_injective`) and the conditional `LaurentTail.H1Tail.equivOfSurjective` (taking
surjectivity as an explicit hypothesis, per that unit's own `CONVENTIONS.md`-rule-3-compliant
fallback) are available.

Per `Jacobian/TailDuality.lean`'s own consumer note for this exact file: "the Abel fixer's bridge
needs restating at the tail level (through `H1Tail`, not `Cech.H1`) or needs to accept the
conditional equivalence as a hypothesis." This file takes the second option, literally: the bridge
below is **fully proved, zero admitted steps**, gated on the ONE hypothesis
`Function.Surjective (RS.LaurentTail.tailToH1 (0 : RS.Divisor X))` — an honest, independently
meaningful, non-vacuous external fact (mirroring the project's established gating idiom, e.g.
`Jacobian.ofCurve_inj'`'s `[DiscreteTopology (RS.periodSubgroup X)]` gate), NOT a restatement of
this file's own conclusion.

## The composite

* `formDualEquiv : Form1 X ≃ₗ[ℂ] Module.Dual ℂ (H1Tail 0)`: `holomorphicMFormsEquiv`
  (`Form1 X ≃ₗ MForm.OmegaSpace 0`, canonical-forms, unconditional) composed with a `neg_zero`
  cast and `RS.TailDuality.resEquiv 0` (`MForm.OmegaSpace (-0) ≃ₗ Dual (H1Tail 0)`,
  serre-duality-tails, unconditional — Miranda Thm 3.3 itself, not merely a dimension count).
* Given `hsurj`, `RS.LaurentTail.H1Tail.equivOfSurjective 0 hsurj : H1Tail 0 ≃ₗ Cech.H1 0` and
  `RS.dolbeaultEquiv : Cech.H1 0 ≃ₗ H01 X` (dolbeault-comparison, unconditional) let us pull
  `H01.mk η` (the Dolbeault class of a candidate `(0,1)`-form `η`) BACK to an `H1Tail 0` element
  `e`. If `e` pairs to zero (via `formDualEquiv`) against a full basis of `Form1 X`, then — since
  `formDualEquiv` maps that basis to a basis of the DUAL of `H1Tail 0` (a perfect pairing, no
  dimension-count needed) — `e` pairs to zero against literally EVERY functional on `H1Tail 0`
  (`Module.forall_dual_apply_eq_zero_iff`, valid for any vector space over a field, no finiteness
  hypothesis needed), hence `e = 0`, hence `H01.mk η = 0` (chasing the two equivalences forward),
  hence (`RS.H01.mk_eq_zero_iff`) `η` is `d''`-exact. This is a genuine finite-dimensional-linear-
  algebra argument (Miranda Thm 3.3's own content), exactly as routing decision #3 (no Hodge
  theory) demands — no new analytic input beyond what `serre-duality-tails`/`dolbeault-comparison`
  already ship.

## What remains open (NOT this file — see `Sufficiency.lean`'s own docstring)

Packaging a weak solution `f`'s chart-local `d''f/f` data into a concrete `η : Form01 X` with a
PROVEN vanishing pairing against a basis (design §4.3's own "step 5", `abel-weak-solutions`
explicitly does not build this global object) is independent, substantial new analytic content,
not an external blocker — flagged precisely in `Sufficiency.lean`.
-/

open scoped ContDiff Manifold

noncomputable section

namespace RS.Abel

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [T1Space X] [DecidableEq X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- The perfect pairing `Form1 X ≃ₗ[ℂ] Dual (H1Tail 0)` (Miranda Thm 3.3, tail-level): composes
`RS.holomorphicMFormsEquiv` (canonical-forms) with `RS.TailDuality.resEquiv 0`
(serre-duality-tails), after a `neg_zero` cast identifying `MForm.OmegaSpace (-0)` with
`MForm.OmegaSpace 0`. Fully unconditional — no gate. -/
noncomputable def formDualEquiv :
    RS.Form1 X ≃ₗ[ℂ] Module.Dual ℂ (RS.LaurentTail.H1Tail (0 : RS.Divisor X)) :=
  RS.holomorphicMFormsEquiv.trans
    ((LinearEquiv.ofEq _ _ (congrArg RS.MForm.OmegaSpace (neg_zero (G := RS.Divisor X)).symm)).trans
      (RS.TailDuality.resEquiv (0 : RS.Divisor X)))

/-- **The Forster-19.10 substitute, restated at the tail level** (design §4.3, routing decision #3
honored: no harmonic theory, no Hodge `*`-operator). Gated on `hsurj`, `serre-duality-tails`'s own
one remaining external blocker (Mittag-Leffler/Cousin-I surjectivity, out of scope for this
challenge) — see the file docstring. If a smooth global `(0,1)`-form `η` pairs to zero (via
`formDualEquiv`, the residue/Serre pairing) against a full basis of `Form1 X` — after pulling
`η`'s Dolbeault class back to `H1Tail 0` through `dolbeaultEquiv`/`H1Tail.equivOfSurjective` —
then `η` is `d''`-exact. -/
theorem exists_dbar_eq_zero_of_forall_basis_pairing_eq_zero
    (hsurj : Function.Surjective (RS.LaurentTail.tailToH1 (0 : RS.Divisor X)))
    {η : RS.Form01 X}
    (h : ∀ i : Fin (genus X),
      formDualEquiv (RS.basis X i)
        ((RS.LaurentTail.H1Tail.equivOfSurjective (0 : RS.Divisor X) hsurj).symm
          ((RS.dolbeaultEquiv (X := X)).symm (RS.H01.mk η))) = 0) :
    ∃ u : RS.SmoothC X, RS.dbar u = η := by
  apply RS.H01.mk_eq_zero_iff.1
  have hzero :
      (RS.LaurentTail.H1Tail.equivOfSurjective (0 : RS.Divisor X) hsurj).symm
        ((RS.dolbeaultEquiv (X := X)).symm (RS.H01.mk η)) = 0 := by
    rw [← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro φ
    obtain ⟨g, rfl⟩ := formDualEquiv.surjective φ
    have hL : ((LinearMap.applyₗ
          ((RS.LaurentTail.H1Tail.equivOfSurjective (0 : RS.Divisor X) hsurj).symm
            ((RS.dolbeaultEquiv (X := X)).symm (RS.H01.mk η)))).comp formDualEquiv.toLinearMap
        : RS.Form1 X →ₗ[ℂ] ℂ) = 0 := by
      apply (RS.basis X).ext
      intro i
      simpa using h i
    have := congrArg (fun L => L g) hL
    simpa using this
  have hde : (RS.dolbeaultEquiv (X := X)).symm (RS.H01.mk η) = 0 := by
    have h2 := congrArg (RS.LaurentTail.H1Tail.equivOfSurjective (0 : RS.Divisor X) hsurj) hzero
    rwa [LinearEquiv.apply_symm_apply, map_zero] at h2
  have h3 := congrArg (RS.dolbeaultEquiv (X := X)) hde
  rwa [LinearEquiv.apply_symm_apply, map_zero] at h3

end RS.Abel

end
