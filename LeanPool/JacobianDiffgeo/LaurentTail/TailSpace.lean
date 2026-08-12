/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.Cech
import Mathlib.Data.DFinsupp.Module

/-!
# Laurent tail spaces `TailAt p D` / `T D` (laurent-tails, design §2 D1/D2/D4, §4.1)

Unit: laurent-tails (`docs/design/laurent-tails.md`).

* `TailAt p D`: the tail space at a point `p` — germs at the chart source of `p`, modulo those
  of order `≥ -(D p)` (D1). A **direct quotient**, no colimit: every germ has some finite order,
  so the "growing window" colimit Miranda's definition literally describes collapses to a single
  quotient (verified by the spike, `scratch_ltails.lean`).
* `windowAtToTailAt`: Cech's finite `WindowAt p (D p) d'` embeds into `TailAt p D` for every
  finite `d'` (the two defining submodules are literally equal, not just comparable).
* `T D := Π₀ p : X, TailAt p D` (D2): a `DFinsupp` (dependent on `p` via `chartAt ℂ p`/`D p`).
  **`abbrev`, not `def`** — matching `Cech.C0/C1/Window/H1`'s own convention (a plain `def` breaks
  `DFunLike`/`AddCommGroup`/`Module ℂ` instance search here, confirmed by the spike).
* `T.mk`/`windowToT` (D4): the finite skyscraper `Window D D'` embeds in `T D`, the bridge that
  will let a future bridge derive the tail-level six-term sequence from Cech's own.

Deviation from the design doc: `mulTailAt`/`mulTail`/`mulTailEquiv` (§2 D5) are **not built here**.
serre-duality-tails (`docs/requests/laurent-tails.md`, item 4) explicitly de-scopes them: their
own `mulInto` (built directly on `T D`/`TailAt p D` from this file) supersedes `mulTail`, so this
is a genuine scope relief, not a shortfall.
-/

open scoped ContDiff Manifold
open Set TopologicalSpace

namespace RS.LaurentTail

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### `TailAt p D` (D1) -/

/-- The tail space at `p`: germs at the chart source of `p`, modulo those of order `≥ -(D p)`.
No colimit over `d'` is needed: every germ has *some* finite order, so it already lies in some
`Cech.ordGe p (-d')`. **`abbrev`, not `def`** — matching `T D`'s own convention (D2): a plain
`def` here is opaque enough to break `Submodule.liftQ`'s instance/type matching against
`TailAt p D` downstream (`Comparison.lean`'s `tailAtToH1`, confirmed by that build); `abbrev`
lets the ambient `Submodule.Quotient` `AddCommGroup`/`Module ℂ` instances be found directly,
so the two instances previously declared here by hand are no longer needed. -/
noncomputable abbrev TailAt (p : X) (D : RS.Divisor X) : Type _ :=
  RS.MeroGermOn X (chartAt ℂ p).source ⧸ RS.Cech.ordGe p (-(D p))

/-- The quotient map onto `TailAt p D`. -/
noncomputable def TailAt.mk (p : X) (D : RS.Divisor X) :
    RS.MeroGermOn X (chartAt ℂ p).source →ₗ[ℂ] TailAt p D := Submodule.mkQ _

omit [T2Space X] [IsManifold 𝓘(ℂ, ℂ) ω X] in
@[simp] theorem TailAt.mk_eq_zero_iff {p : X} {D : RS.Divisor X}
    (ψ : RS.MeroGermOn X (chartAt ℂ p).source) :
    TailAt.mk p D ψ = 0 ↔ (-(D p) : WithTop ℤ) ≤ ψ.ord p := by
  change Submodule.Quotient.mk ψ =
    (0 : RS.MeroGermOn X (chartAt ℂ p).source ⧸ RS.Cech.ordGe p (-(D p))) ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  exact RS.Cech.mem_ordGe_iff

omit [T2Space X] [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem TailAt.mk_surjective (p : X) (D : RS.Divisor X) :
    Function.Surjective (TailAt.mk p D) := Submodule.mkQ_surjective _

/-! ### `windowAtToTailAt` (D1 continued) -/

/-- Cech's finite Laurent window at `p` (between orders `-d'` and `-(D p)`) embeds into the full
tail space: `WindowAt p (D p) d'`'s defining submodule, viewed inside `ordGe p (-d')`, is exactly
the restriction of `ordGe p (-(D p))` there. -/
noncomputable def windowAtToTailAt (p : X) (D : RS.Divisor X) (d' : ℤ) :
    RS.Cech.WindowAt p (D p) d' →ₗ[ℂ] TailAt p D :=
  Submodule.mapQ _ _ (RS.Cech.ordGe p (-d')).subtype le_rfl

omit [T2Space X] [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem windowAtToTailAt_mk (p : X) (D : RS.Divisor X) (d' : ℤ) (ψ : RS.Cech.ordGe p (-d')) :
    windowAtToTailAt p D d' (RS.Cech.WindowAt.mk p (D p) d' ψ) = TailAt.mk p D ψ := rfl

omit [T2Space X] [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- Every tail class is *represented* by some finite window (the union-of-`ordGe` fact): every
germ has an honest `WithTop ℤ`-order, hence lies in `ordGe p (-d')` for `d'` large enough. -/
theorem exists_windowAt_repr (p : X) (D : RS.Divisor X) (z : TailAt p D) :
    ∃ (d' : ℤ) (ψ : RS.Cech.ordGe p (-d')),
      windowAtToTailAt p D d' (RS.Cech.WindowAt.mk p (D p) d' ψ) = z := by
  obtain ⟨ψ₀, rfl⟩ := TailAt.mk_surjective p D z
  by_cases htop : ψ₀.ord p = ⊤
  · refine ⟨0, ⟨ψ₀, ?_⟩, windowAtToTailAt_mk p D 0 ⟨ψ₀, ?_⟩⟩ <;>
      · rw [RS.Cech.mem_ordGe_iff]; rw [htop]; exact le_top
  · obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp htop
    refine ⟨-n, ⟨ψ₀, ?_⟩, windowAtToTailAt_mk p D (-n) ⟨ψ₀, ?_⟩⟩ <;>
      · rw [RS.Cech.mem_ordGe_iff]; simp only [neg_neg]; rw [← hn]

/-! ### `T D` (D2) -/

variable [DecidableEq X]

/-- Miranda's `T[D]`: finitely-supported tail data (D2). **`abbrev`, not `def`** — a plain `def`
breaks `DFunLike`/`AddCommGroup`/`Module ℂ` instance search for the assembled `DFinsupp` (confirmed
by the spike, `scratch_ltails.lean`). -/
noncomputable abbrev T (D : RS.Divisor X) : Type _ := Π₀ p : X, TailAt p D

noncomputable instance instAddCommGroupT (D : RS.Divisor X) : AddCommGroup (T D) :=
  inferInstanceAs (AddCommGroup (Π₀ p : X, TailAt p D))

noncomputable instance instModuleT (D : RS.Divisor X) : Module ℂ (T D) :=
  inferInstanceAs (Module ℂ (Π₀ p : X, TailAt p D))

/-- A single finitely-supported tail element, built from a `Finset` witness (mirrors
`Cech.Window.diffSupp`'s own pattern). -/
noncomputable def T.mk (D : RS.Divisor X) (S : Finset X)
    (x : ∀ p : (S : Set X), TailAt (p : X) D) : T D := DFinsupp.mk S x

omit [T2Space X] [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem T.mk_apply_mem {D : RS.Divisor X} {S : Finset X} {x : ∀ p : (S : Set X), TailAt (p : X) D}
    {p : X} (hp : p ∈ S) : T.mk D S x p = x ⟨p, hp⟩ := by
  unfold T.mk
  rw [DFinsupp.mk_apply, dite_eq_left hp]

omit [T2Space X] [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem T.mk_apply_not_mem {D : RS.Divisor X} {S : Finset X}
    {x : ∀ p : (S : Set X), TailAt (p : X) D} {p : X} (hp : p ∉ S) : T.mk D S x p = 0 := by
  unfold T.mk
  rw [DFinsupp.mk_apply, dite_eq_right hp]

/-! ### `windowToT` (D4): the finite skyscraper embeds in the tail space -/

variable [CompactSpace X]

/-- The finite skyscraper `Window D D'` embeds in the full tail space `T D` — the bridge that
lets a future bridge file derive the tail-level six-term sequence from Cech's own (instead of
re-proving it). -/
noncomputable def windowToT (D D' : RS.Divisor X) (_h : D ≤ D') :
    RS.Cech.Window D D' →ₗ[ℂ] T D where
  toFun w := T.mk D (RS.Cech.diffSupp D D')
    (fun q => windowAtToTailAt (q : X) D (D' q) (w q))
  map_add' w w' := by
    apply DFinsupp.ext
    intro p
    by_cases hp : p ∈ RS.Cech.diffSupp D D'
    · rw [DFinsupp.add_apply, T.mk_apply_mem hp, T.mk_apply_mem hp, T.mk_apply_mem hp,
        Pi.add_apply, map_add]
    · rw [DFinsupp.add_apply, T.mk_apply_not_mem hp, T.mk_apply_not_mem hp, T.mk_apply_not_mem hp,
        add_zero]
  map_smul' a w := by
    apply DFinsupp.ext
    intro p
    by_cases hp : p ∈ RS.Cech.diffSupp D D'
    · rw [DFinsupp.smul_apply, T.mk_apply_mem hp, T.mk_apply_mem hp, Pi.smul_apply, map_smul]
      rfl
    · rw [DFinsupp.smul_apply, T.mk_apply_not_mem hp, T.mk_apply_not_mem hp, smul_zero]

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem windowToT_apply (D D' : RS.Divisor X) (h : D ≤ D') (w : RS.Cech.Window D D')
    (q : RS.Cech.diffSupp D D') :
    windowToT D D' h w (q : X) = windowAtToTailAt (q : X) D (D' q) (w q) := by
  change T.mk D (RS.Cech.diffSupp D D') (fun q => windowAtToTailAt (q : X) D (D' q) (w q))
    (q : X) = _
  exact T.mk_apply_mem q.2

end RS.LaurentTail
