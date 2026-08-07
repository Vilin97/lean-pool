/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

/-
Blueprint unit: form-trace-tower. `traceZkForm`: the Jacobian-weighted planar trace atom (D3).
-/
import LeanPool.JacobianDiffgeo.MeromorphicTrace.PlanarTrace
import LeanPool.JacobianDiffgeo.ResidueCalculus.LaurentCoeff
import LeanPool.JacobianDiffgeo.ResidueCalculus.Residue

/-!
# The Jacobian-weighted planar trace atom (`form-trace-tower`, file 2/6)

Unit: form-trace-tower (`docs/design/form-trace-tower.md` §2 D3, §4.2, §5). `RS.MTrace.traceZk`
(`Jacobian/MeromorphicTrace/PlanarTrace.lean`) is fully proved, zero sorries, including its
Laurent-coefficient formula `laurentCoeffAt_traceZk` (P6 — CLOSED, see `docs/build-log.md`'s
`[mtrace]` entries) and its residue corollary `resAt_traceZk`. This file builds the "divide out
the Jacobian factor" atom on top.

* `traceZkForm h k w` — divides the `k · v^(k-1)` Jacobian factor (that `F^*(dz) = d(v^k) =
  k v^{k-1} dv` produces in an adapted chart) back out of `h`'s coefficient before applying
  `traceZk`. Junk-inherits `traceZk`'s own convention at `w = 0` (never used there).
* `traceZkForm_hAdapted_eq_apply` (the cancellation identity, task item 2's core step):
  applying `traceZkForm` to a coefficient that ALREADY carries the Jacobian factor recovers the
  bare `traceZk` of the un-weighted function, for every `w ≠ 0` — this is why "the trace of the
  pair-form `h·F^*dz`" needs no new global object: its coefficient function IS `RS.MTrace.trace`.
  **Deviation from the design**: stated for `w ≠ 0` (not as a full function equality) — the
  design's own proof sketch claims an unconditional (`∀ w`, no `w ≠ 0` guard) function equality,
  but this is FALSE at `w = 0` for `k > 1` whenever `g 0 ≠ 0` (the Jacobian factor `k·v^{k-1}`
  literally vanishes at `v = 0` for `k > 1`, so dividing it back out at the branch point does not
  recover `g 0`) — a genuine gap in the design's claim, corrected here to the provable, and
  equally useful (all downstream uses are `𝓝[≠]0`-germ notions), `w ≠ 0` form.
* `meromorphicAt_traceZkForm` — existence of meromorphy, UNCONDITIONAL in `k` (needs only
  `k ≠ 0`), built only from `RS.MTrace.meromorphicAt_traceZk` (P5).
* `laurentCoeffAt_traceZkForm` / `resAt_traceZkForm` — the Laurent-coefficient / residue
  identities, now UNCONDITIONALLY PROVABLE (mtrace's P6 landed, see `docs/build-log.md`).
-/

open Filter Topology

namespace RS.FormTrace

variable {h g : ℂ → ℂ} {k : ℕ}

/-- The Jacobian-weighted planar trace atom: divides the `k·v^{k-1}` Jacobian factor of
`F^*(dz)` back out before applying `RS.MTrace.traceZk`. -/
noncomputable def traceZkForm (h : ℂ → ℂ) (k : ℕ) (w : ℂ) : ℂ :=
  RS.MTrace.traceZk (fun v => h v * ((k : ℂ) * v ^ ((k : ℤ) - 1))⁻¹) k w

theorem traceZkForm_def (h : ℂ → ℂ) (k : ℕ) (w : ℂ) :
    traceZkForm h k w = RS.MTrace.traceZk (fun v => h v * ((k : ℂ) * v ^ ((k : ℤ) - 1))⁻¹) k w :=
  rfl

/-- The cancellation identity (task item 2's core step), `w ≠ 0` form (see the module docstring
for why the design's unconditional claim is false at `w = 0`). -/
theorem traceZkForm_hAdapted_eq_apply (hk : k ≠ 0) {w : ℂ} (hw : w ≠ 0) :
    traceZkForm (fun v => g v * (k : ℂ) * v ^ ((k : ℤ) - 1)) k w = RS.MTrace.traceZk g k w := by
  unfold traceZkForm
  rw [RS.MTrace.traceZk_def, RS.MTrace.traceZk_def]
  apply finsum_mem_congr rfl
  intro v hv
  have hvpow : v ^ k = w := hv
  have hv0 : v ≠ 0 := by
    rintro rfl
    rw [zero_pow hk] at hvpow
    exact hw hvpow.symm
  have hkC : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk
  have hvz : v ^ ((k : ℤ) - 1) ≠ 0 := zpow_ne_zero _ hv0
  field_simp

/-- Existence of meromorphy: builds ONLY on `RS.MTrace.meromorphicAt_traceZk` (P5, zero sorries)
— NOT gated on P6. -/
theorem meromorphicAt_traceZkForm (hh : MeromorphicAt h 0) (hk : k ≠ 0) :
    MeromorphicAt (traceZkForm h k) 0 := by
  unfold traceZkForm
  apply RS.MTrace.meromorphicAt_traceZk _ hk
  have hzp : MeromorphicAt (fun v : ℂ => v ^ ((k : ℤ) - 1)) 0 := by
    simpa using (MeromorphicAt.id (0 : ℂ)).fun_zpow ((k : ℤ) - 1)
  exact hh.mul ((MeromorphicAt.const (k : ℂ) 0).mul hzp).inv

/-- The Laurent-coefficient formula (design §4.2, ⚠ was gated on mtrace's P6 — now UNCONDITIONAL,
P6 having landed with zero admitted goals). -/
theorem laurentCoeffAt_traceZkForm (hh : MeromorphicAt h 0) (hk : k ≠ 0) (j : ℤ) :
    RS.laurentCoeffAt (traceZkForm h k) 0 j = RS.laurentCoeffAt h 0 ((k : ℤ) * j + ((k : ℤ) - 1)) :=
        by
  unfold traceZkForm
  have hkC : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk
  have hzp : MeromorphicAt (fun v : ℂ => v ^ ((k : ℤ) - 1)) 0 := by
    simpa using (MeromorphicAt.id (0 : ℂ)).fun_zpow ((k : ℤ) - 1)
  have hH : MeromorphicAt (fun v => h v * ((k : ℂ) * v ^ ((k : ℤ) - 1))⁻¹) 0 :=
    hh.mul ((MeromorphicAt.const (k : ℂ) 0).mul hzp).inv
  rw [RS.MTrace.laurentCoeffAt_traceZk hH hk j]
  have heq : (fun v : ℂ => h v * ((k : ℂ) * v ^ ((k : ℤ) - 1))⁻¹)
      = fun v => (k : ℂ)⁻¹ * ((v - 0) ^ (-((k : ℤ) - 1)) * h v) := by
    funext v; rw [mul_inv, ← zpow_neg]; ring_nf
  rw [heq, RS.laurentCoeffAt_const_mul, RS.laurentCoeffAt_zpow_mul hh]
  have hidx : (k : ℤ) * j - -((k : ℤ) - 1) = (k : ℤ) * j + ((k : ℤ) - 1) := by ring
  rw [hidx, mul_inv_cancel_left₀ hkC]

/-- Miranda Lemma 3.2, LOCAL case (single preimage): the residue is preserved EXACTLY (no factor
of `k` — the Jacobian factor exactly cancels mtrace's `k`-multiplier at the residue index
`j = -1`). -/
theorem resAt_traceZkForm (hh : MeromorphicAt h 0) (hk : k ≠ 0) :
    RS.resAt (traceZkForm h k) 0 = RS.resAt h 0 := by
  have hL := laurentCoeffAt_traceZkForm hh hk (-1)
  have hidx : (k : ℤ) * (-1) + ((k : ℤ) - 1) = -1 := by ring
  rw [hidx] at hL
  exact hL

end RS.FormTrace
