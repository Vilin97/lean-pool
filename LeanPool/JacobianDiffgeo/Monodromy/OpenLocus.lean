/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.Path
import Mathlib.Geometry.Manifold.IsManifold.Basic

/-!
# `monodromy`: the open pole/zero-free locus as a Riemann surface

Unit: monodromy (`docs/design/monodromy.md` §4.1). Relativizes `Jacobian/Path/`'s per-path
machinery (`IsPrimitiveAlongMap`, chain continuation, homotopy invariance) to an open subset
`s : Opens X` of a Riemann surface `X`, at zero proof cost: mathlib gives an open submanifold of
a charted space / `IsManifold` the same instances *for free*
(`TopologicalSpace.Opens.instChartedSpace`, and the derived `IsManifold` instance for opens), so
`Path`'s declarations — stated for a fully generic `X` satisfying only `[TopologicalSpace X]
[ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]`, no `T2Space`/`CompactSpace`/`ConnectedSpace` — apply to
`s` by direct instantiation, term for term (spike-verified, `scratch_mono.lean`, project root).

Main declarations:
* `RS.Monodromy.openLocus`/`openLocusOfFinite` — the open locus determined by a closed/finite
  "bad set" (in practice a divisor support).
* `RS.Monodromy.Path.liftOpenLocus` — lift a path of `X` whose range avoids the bad set to a path
  in the open locus; `RS.Monodromy.Path.liftOpenLocus_extend` recovers `γ.extend` pointwise.
-/

open scoped ContDiff Manifold
open TopologicalSpace Set

noncomputable section

namespace RS.Monodromy

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- The open locus determined by a closed "bad set" (in practice a divisor support). -/
def openLocus {S : Set X} (hS : IsClosed S) : Opens X := ⟨Sᶜ, hS.isOpen_compl⟩

/-- Finite bad sets are closed in a `T2Space` (`Set.Finite.isClosed`), hence give an open locus.
The standing surface is compact, so this is the case actually used in `LogContinuation.lean`
(`(divisor f).support` is finite by `finite_support_divisor`). -/
def openLocusOfFinite {S : Set X} (hS : S.Finite) : Opens X := openLocus hS.isClosed

omit [T2Space X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] in
@[simp] theorem mem_openLocus {S : Set X} (hS : IsClosed S) {x : X} :
    x ∈ openLocus hS ↔ x ∉ S := Set.mem_compl_iff S x

omit [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] in
@[simp] theorem mem_openLocusOfFinite {S : Set X} (hS : S.Finite) {x : X} :
    x ∈ openLocusOfFinite hS ↔ x ∉ S := mem_openLocus hS.isClosed

/-- `ChartedSpace ℂ (openLocus hS)`: automatic (`TopologicalSpace.Opens.instChartedSpace`,
mathlib) — no proof needed, `inferInstance` resolves it (spike-verified). Recorded as an
`example`, not a declaration, since no proof obligation exists. -/
example {S : Set X} (hS : IsClosed S) : ChartedSpace ℂ (openLocus hS) := inferInstance

/-- `IsManifold 𝓘(ℂ) ω (openLocus hS)`: automatic (mathlib's derived `IsManifold` instance for
opens of an `IsManifold`) — no proof needed, `inferInstance` resolves it (spike-verified). -/
example {S : Set X} (hS : IsClosed S) : IsManifold 𝓘(ℂ) ω (openLocus hS) := inferInstance

/-- Lift a path of `X` whose whole range avoids `S` to a path in the open locus. -/
def Path.liftOpenLocus {S : Set X} (hS : IsClosed S) {x y : X} (γ : Path x y)
    (hγ : ∀ t : ↥unitInterval, γ t ∉ S) :
    Path (⟨x, γ.source ▸ hγ 0⟩ : openLocus hS) (⟨y, γ.target ▸ hγ 1⟩ : openLocus hS) where
  toFun t := ⟨γ t, hγ t⟩
  continuous_toFun := by fun_prop
  source' := by simp [γ.source]
  target' := by simp [γ.target]

omit [T2Space X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] in
/-- The lift's `extend` recovers `γ.extend` pointwise (needed to translate `IsPrimitiveAlong`
facts about the lift back into statements about `γ.extend`, `f.holoRepr`, etc.).

NB: called with the fully-qualified name `Path.liftOpenLocus`, not dot notation — `Path` is a
mathlib root-namespace type, so a declaration named `Path.foo` nested inside `RS.Monodromy` is
*not* found by the dot-notation mechanism (only by ordinary name resolution, which does see it
since we are inside the `RS.Monodromy` namespace). -/
theorem Path.liftOpenLocus_extend {S : Set X} (hS : IsClosed S) {x y : X} (γ : Path x y)
    (hγ : ∀ t : ↥unitInterval, γ t ∉ S) (t : ℝ) :
    ((Path.liftOpenLocus hS γ hγ).extend t : X) = γ.extend t := by
  by_cases ht : t ≤ 0
  · rw [(Path.liftOpenLocus hS γ hγ).extend_of_le_zero ht, γ.extend_of_le_zero ht]
  · rw [not_le] at ht
    by_cases ht1 : t ≤ 1
    · rw [(Path.liftOpenLocus hS γ hγ).extend_apply ⟨ht.le, ht1⟩, γ.extend_apply ⟨ht.le, ht1⟩]
      rfl
    · rw [not_le] at ht1
      rw [(Path.liftOpenLocus hS γ hγ).extend_of_one_le ht1.le, γ.extend_of_one_le ht1.le]

end RS.Monodromy

end
