/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/

import LeanPool.DomainTheory.Neighborhood.Approximable
import LeanPool.DomainTheory.Neighborhood.Example12
import LeanPool.DomainTheory.Neighborhood.ExampleB

/-!
# Example 2.3 (Scott 1981, PRG-19, §2) — the parity map `f : B → T`

Scott's first approximable mapping. Reading a binary sequence left to right, count
the number `n`
of `0`'s seen *before the first* `1`; the output is `true` if `n` is even, `false`
if `n` is odd,
and `⊥` while the input is still an unbroken string of `0`'s (which has consistent
extensions of
both parities). Concretely

`f(0ⁿ1⊥) = true` if `n` even, `false` if `n` odd; `f(0^∞) = ⊥`.

Here `B` is the binary system (`ExampleB`) and `T` is the two-token domain of
Example 1.2, whose two
total elements we use as `true`/`false` and whose unique partial element is `⊥`.

We model the relation by a parity scanner `scan : Σ* → Option Bool`:
`scan` returns `none` while no `1` has appeared and `some b` (with `b` the
parity-of-leading-zeros)
once the first `1` is found. The neighbourhood relation is

`X f Y ↔ ∃ σ, X = σΣ* ∧ Y ∈ valElt (scan σ)`,

where `valElt none = ⊥`, `valElt (some true) = true`, `valElt (some false) =
false`. The cone `σΣ*`
has a unique generating prefix (`cone_injective`), so this is well defined, and
`scan` is *stable*
under extension (`scan_append`), which is exactly the monotonicity (Def 2.1(iii)).

Definition 2.1(i)–(iii) all check out, giving `parityMap : ApproximableMap B T`.
(The `B`-side
reasoning is choice-free; `parityMap` nonetheless pulls `Classical.choice` through
the concrete
codomain `T` of Example 1.2, whose `simp`/`fin_cases` proofs already do —
pre-existing and harmless.)
-/

namespace Domain.Neighborhood.Example23

open Domain.Neighborhood NeighborhoodSystem ExampleB

/-- The two-token codomain `T` of Example 1.2. -/
abbrev T : NeighborhoodSystem Example12.Token := Example12.neighborhoodSystem

/-- Scott's `true`: the total element `{Δ, {0}}` of `T`. -/
def trueElt : T.Element := Example12.neighborhoodSystem.elemZero

/-- Scott's `false`: the total element `{Δ, {1}}` of `T`. -/
def falseElt : T.Element := Example12.neighborhoodSystem.elemOne

/-- Scott's `⊥`: the unique partial element `{Δ}` of `T`. -/
def botElt : T.Element := Example12.neighborhoodSystem.bot

/-- The codomain element selected by a parity reading: `none ↦ ⊥`, `some true ↦
true`,
`some false ↦ false`. -/
def valElt : Option Bool → T.Element
  | none => botElt
  | some true => trueElt
  | some false => falseElt

/-- `⊥` approximates every element of `T` (the local `{Δ}` form, proved directly). -/
theorem botElt_le (x : T.Element) : botElt ≤ x := by
  intro Z hZ
  have : Z = Example12.master := hZ
  subst this
  exact x.master_mem

/-- **The parity scanner.** `scan σ = none` while `σ` is an unbroken run of `0`'s;
once a `1`
appears, `scan σ = some b` with `b = true` iff an even number of `0`'s preceded
it. A leading `0`
flips the parity of the rest; a leading `1` fixes parity `true` (zero preceding
zeros). -/
def scan : Str → Option Bool
  | [] => none
  | true :: _ => some true
  | false :: t => (scan t).map (!·)

@[simp] theorem scan_nil : scan [] = none := rfl
@[simp] theorem scan_true (t : Str) : scan (true :: t) = some true := rfl
@[simp] theorem scan_false (t : Str) : scan (false :: t) = (scan t).map (!·) := rfl

/-- **Stability of the scan under extension.** Once `scan σ` has committed to a
parity `some b`,
every extension `σ ++ t` keeps that value. This is the engine of monotonicity for
`parityMap`. -/
theorem scan_append {σ : Str} {b : Bool} (h : scan σ = some b) (t : Str) :
    scan (σ ++ t) = some b := by
  induction σ generalizing b with
  | nil => simp at h
  | cons c σ₀ ih =>
    cases c with
    | true => simp only [scan_true] at h ⊢; exact h
    | false =>
      simp only [List.cons_append, scan_false] at h ⊢
      rw [Option.map_eq_some_iff] at h
      obtain ⟨a, ha, rfl⟩ := h
      rw [ih ha]
      rfl

/-- **Monotonicity of the parity value.** A longer prefix `σ <+: σ'` yields a
(weakly) more defined
value: `valElt (scan σ) ⊑ valElt (scan σ')`. If `scan σ = none` then `valElt = ⊥ ⊑
_`; otherwise the
value is fixed by `scan_append`. -/
theorem valElt_scan_mono {σ σ' : Str} (h : σ <+: σ') :
    valElt (scan σ) ≤ valElt (scan σ') := by
  obtain ⟨t, rfl⟩ := h
  cases hσ : scan σ with
  | none => simpa [valElt, hσ] using botElt_le _
  | some b => rw [scan_append hσ t]

/-- **Example 2.3 — the parity mapping `f : B → T`.** `X f Y` iff `X` is the cone
`σΣ*` of some
prefix `σ` and `Y` is approximated by the parity verdict `valElt (scan σ)`.
Definition 2.1:
(i) the empty prefix scans to `none = ⊥`, and `⊥` contains `Δ_T`; (ii) for a fixed
cone the verdict
is a *single* filter (cones have a unique prefix), closed under `∩`; (iii)
extending the prefix only
sharpens the verdict (`valElt_scan_mono`). -/
def parityMap : ApproximableMap B T where
  rel X Y := ∃ σ, X = cone σ ∧ (valElt (scan σ)).mem Y
  rel_dom := fun ⟨σ, hX, _⟩ => ⟨σ, hX⟩
  rel_cod := fun ⟨_, _, hY⟩ => (valElt _).sub hY
  master_rel := by
    refine ⟨[], cone_nil.symm, ?_⟩
    change (botElt).mem Example12.master
    rfl
  inter_right := by
    rintro X Y Y' ⟨σ, hX, hY⟩ ⟨σ', hX', hY'⟩
    have hσ : σ = σ' := cone_injective (hX ▸ hX')
    subst hσ
    exact ⟨σ, hX, (valElt (scan σ)).inter_mem hY hY'⟩
  mono := by
    rintro X X' Y Y' ⟨σ, hX, hY⟩ hX'X hYY' hX'mem hY'mem
    obtain ⟨σ', hX'cone⟩ := hX'mem
    have hpre : σ <+: σ' := by
      apply cone_subset_cone.mp
      rw [← hX'cone, ← hX]; exact hX'X
    have hYmem' : (valElt (scan σ)).mem Y' := (valElt (scan σ)).up_mem hY hY'mem hYY'
    exact ⟨σ', hX'cone, valElt_scan_mono hpre Y' hYmem'⟩

end Domain.Neighborhood.Example23
