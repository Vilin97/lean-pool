/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.AbelWeak
import LeanPool.JacobianDiffgeo.JacobianConstruction

/-!
# abel-theorem: loop-cancellation algebra (`docs/design/abel-theorem.md` §4.2, D2, §2.1 steps 1-3)

Unit: abel-theorem. Namespace `RS.Abel`. Two deliverables:

* `mem_periodSubgroup_iff_exists_loop` — `RS.periodSubgroup X`'s generating set (based-loop period
  vectors) is already closed under `+`/`neg`/`0` (`RS.periodVector_trans/_symm/_refl`, BUILT), so
  `AddSubgroup.closure` of it adds nothing new: every element of the closure is already the
  `periodVector` of a SINGLE based loop. Proved via `AddSubgroup.closure_induction`, mirroring
  exactly how `RS.periodVector_mem_periodSubgroup` (BUILT, `OfCurve.lean`) proves the reverse
  inclusion via conjugation.
* `exists_zeroPeriod_path` — the loop-cancellation construction itself (§2.1 steps 1-3): given a
  path `δ : Path Q P` whose basis-period vector lies in `RS.periodSubgroup X`, produce ANOTHER
  path `δ' : Path Q P` (differing from `δ` by a based loop, conjugated to be based at `Q`) with
  **exactly** zero integral against every `ω ∈ RS.Form1 X`, not merely against the basis (Forster's
  own Remark: "only needs to be checked for a basis" — extended to all of `Form1 X` via linearity
  of `RS.pathIntegralₗ` and `Module.Basis.ext`).
-/

open scoped ContDiff Manifold

noncomputable section

namespace RS.Abel

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **Compat** (request filed to `jacobian-construction`'s `Periods.lean`, built here as this
unit's own D2 since it is small and self-contained): `RS.periodSubgroup X`'s generating set is
already closed under the loop operations, so the closure adds nothing — every element is the
`periodVector` of a single based loop at the fixed basepoint `Classical.arbitrary X`. -/
theorem mem_periodSubgroup_iff_exists_loop {v : Fin (genus X) → ℂ} :
    v ∈ RS.periodSubgroup X ↔
      ∃ α : Path (Classical.arbitrary X) (Classical.arbitrary X),
        RS.periodVector (RS.basis X) α = v := by
  constructor
  · intro hv
    have hv' : ∃ _ : v ∈ RS.periodSubgroup X,
        ∃ α : Path (Classical.arbitrary X) (Classical.arbitrary X),
          RS.periodVector (RS.basis X) α = v := by
      induction hv using AddSubgroup.closure_induction with
      | mem x hx => exact ⟨AddSubgroup.subset_closure hx, hx.choose, hx.choose_spec⟩
      | zero => exact ⟨(RS.periodSubgroup X).zero_mem, Path.refl _, RS.periodVector_refl _⟩
      | add x y hx hy ihx ihy =>
        obtain ⟨_, α, hα⟩ := ihx
        obtain ⟨_, β, hβ⟩ := ihy
        exact ⟨AddSubgroup.add_mem _ hx hy, α.trans β, by
          rw [RS.periodVector_trans, hα, hβ]⟩
      | neg x hx ihx =>
        obtain ⟨_, α, hα⟩ := ihx
        exact ⟨AddSubgroup.neg_mem _ hx, α.symm, by rw [RS.periodVector_symm, hα]⟩
    exact hv'.2
  · rintro ⟨α, hα⟩
    exact hα ▸ RS.periodVector_mem_periodSubgroup α

/-- **The loop-cancellation construction** (§2.1 steps 1-3): if `δ`'s basis-period vector lies in
`RS.periodSubgroup X`, there is another path `δ' : Path Q P` with EXACTLY zero integral against
every `ω ∈ RS.Form1 X`. -/
theorem exists_zeroPeriod_path {Q P : X} (δ : Path Q P)
    (hmem : (fun i => RS.pathIntegral δ (RS.basis X i)) ∈ RS.periodSubgroup X) :
    ∃ δ' : Path Q P, ∀ η : RS.Form1 X, RS.pathIntegral δ' η = 0 := by
  obtain ⟨α, hα⟩ := mem_periodSubgroup_iff_exists_loop.mp hmem
  set σ : Path Q (Classical.arbitrary X) := PathConnectedSpace.somePath Q (Classical.arbitrary X)
  set β : Path Q Q := (σ.trans α).trans σ.symm with hβ_def
  have hβ_period : ∀ k, RS.period β (RS.basis X k) = RS.period α (RS.basis X k) :=
    fun k => RS.period_conj σ α (RS.basis X k)
  refine ⟨β.symm.trans δ, ?_⟩
  -- First, the basis vanishing (the exact content step 3 needs), then extend by linearity.
  have hbasis : ∀ k, RS.pathIntegral (β.symm.trans δ) (RS.basis X k) = 0 := by
    intro k
    rw [RS.pathIntegral_trans, RS.pathIntegral_symm]
    change -(RS.period β (RS.basis X k)) + RS.pathIntegral δ (RS.basis X k) = 0
    rw [hβ_period k]
    change -(RS.periodVector (RS.basis X) α k) + RS.pathIntegral δ (RS.basis X k) = 0
    rw [hα]
    change -(RS.pathIntegral δ (RS.basis X k)) + RS.pathIntegral δ (RS.basis X k) = 0
    ring
  intro η
  have hlin : RS.pathIntegralₗ (β.symm.trans δ) = 0 := by
    apply (RS.basis X).ext
    intro k
    change RS.pathIntegral (β.symm.trans δ) (RS.basis X k) = 0
    exact hbasis k
  change RS.pathIntegralₗ (β.symm.trans δ) η = 0
  rw [hlin]
  rfl

end RS.Abel

end
