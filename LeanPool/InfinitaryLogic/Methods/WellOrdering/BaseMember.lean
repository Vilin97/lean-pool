/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.WellOrdering.MarkExtension
/-!
# The initial member: `Bφ ∈ P` (issue #12, the mathematical starting gate)

**The only point where `HasWellOrderedChains` enters the consistency-property construction**:
the base diagram itself is a member.  The proof exposes the intended normalization —

* finite remainder: `Bφ \ Bφ = ∅`;
* remainder support and realization: vacuous;
* marking enumeration: `Fin 0`;
* for each `α < ω₁`, the source chain is requested at `γ = α + 1`;
* `lt_gamma` is discharged by `α < α + 1`;
* every mark and gap field reduces from the empty domain.

This separately certifies that the strengthened terminal/bottom-margin invariant (D6 and the
`lt_gamma` addition) has **not** accidentally strengthened the theorem's hypothesis: an
`(α+1)`-chain per level — exactly Marker's hypothesis, off by the harmless successor — is all
that is consumed.
-/

namespace FirstOrder.Language

open FirstOrder Structure

variable {L : Language.{0, 0}} {φ : L.Sentenceω} {lt : L.Relations 2}

/-- **The initial member**: the base diagram satisfies the member predicate, from
`HasWellOrderedChains` alone. -/
theorem baseDiagram_mem (h : HasWellOrderedChains φ lt) :
    WOMem φ lt (baseDiagram φ lt) := by
  refine ⟨subset_rfl, ?_, ?_, ?_, ?_⟩
  · -- finite remainder: `Bφ \ Bφ = ∅`
    rw [Set.sdiff_self]
    exact Set.finite_empty
  · -- remainder support: vacuous
    rw [Set.sdiff_self]
    simp
  · -- universe: the root is the seed root, the atoms are seed relation instances
    rintro χ hχ
    rcases mem_baseDiagram_elim hχ with rfl | ⟨q, r, _, rfl⟩
    · exact root₁_mem
    · exact relInst_mem lt _
  · -- (*): request the source chain at `γ = α + 1`
    intro α hα
    obtain ⟨M, inst, ne, hφreal, w, hchain⟩ := h (α + 1) (add_one_lt_omega1 hα)
    refine ⟨{
      M := M
      inst := inst
      ne := ne
      h := fun _ => ne.some
      base_realize := hφreal
      rem_realize := fun _ hχ => absurd hχ.1 hχ.2
      m := 0
      mark := Fin.elim0
      mark_mono := fun i => i.elim0
      mark_cover := ?_
      witness := {
        γ := α + 1
        w := w
        chain := hchain
        rank := Fin.elim0
        rank_lt := fun i => i.elim0
        initial := fun i => i.elim0
        gaps := fun i => i.elim0
        terminal := fun i => i.elim0
        lt_gamma := lt_add_one α
        marks := fun i => i.elim0 } }⟩
    rintro q ⟨χ, hχ, -⟩
    exact absurd hχ.1 hχ.2

end FirstOrder.Language
