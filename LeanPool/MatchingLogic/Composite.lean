/-
Copyright (c) 2026 Aurélien Eveil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Eveil, Anthropic, OpenAI
-/

/-
Corollary 12 and Theorem 13 of arXiv:2608.13306v1, Sections 4-5.

Theorem 13 is the semantic half of global completeness: it is where Lemma 8
supplies `C ⊆ ⟦Γ⟧` and the double cover of Definition 10 turns a *local*
countermodel into a *global* one.

Statements pinned before any proof was attempted.
-/
import LeanPool.MatchingLogic.DoubleCover
import LeanPool.MatchingLogic.Localization

/-!
# MatchingLogic.Composite
-/

namespace MatchingLogic

variable {S : Signature} {Var : Type} [DecidableEq Var]

section Cover

variable (M : Model S) (C : Set M.carrier)

/-- **Corollary 12.**  For closed `ψ`, `⟦ψ⟧_N = (⟦ψ⟧_M ∩ C) × {0,1}`.
The `∩ C` and the `× {0,1}` are both absorbed by the carrier `↥C × Bool`: the
statement says a point of `N` lies in `⟦ψ⟧_N` exactly when its underlying
point of `C` lies in `⟦ψ⟧_M`, whichever copy it is in. -/
theorem cover_denote_closed (hC : M.BackwardClosed C) (hne : C.Nonempty)
    (star : M.carrier) (hstar : star ∉ C)
    {ψ : Pattern S Var} (hψ : Closed ψ)
    (ν : Var → (C × Bool)) (ρ : Var → M.carrier) (p : C × Bool) :
    p ∈ (cover M C hne).denote ν ψ ↔ (p.1 : M.carrier) ∈ M.denote ρ ψ := by
  rw [two_copies M C hC hne star hstar ψ ν p]
  rw [denote_closed M hψ (fun x => proj M C star p.2 (ν x)) ρ]

/-- **Corollary 12**, second half: `N ⊨ ψ` iff `C ⊆ ⟦ψ⟧_M`.

Note that `star` and `hstar` appear nowhere in the statement, only in the proof
(Lemma 11 consumes them).  They are not vestigial: requiring a point outside `C`
is how this theorem carries Definition 10's standing assumption `C ≠ M`.  A
caller must exhibit one, so Corollary 12 does NOT apply when `C = M` -- which is
exactly why Theorem 13 handles that case separately. -/
theorem cover_sat_iff (hC : M.BackwardClosed C) (hne : C.Nonempty)
    (star : M.carrier) (hstar : star ∉ C)
    {ψ : Pattern S Var} (hψ : Closed ψ) (ρ : Var → M.carrier) :
    (cover M C hne).Sat ψ ↔ C ⊆ M.denote ρ ψ := by
  constructor
  · intro h q hq
    let p : C × Bool := (⟨q, hq⟩, false)
    let ν : Var → (C × Bool) := fun _ => p
    apply (cover_denote_closed M C hC hne star hstar hψ ν ρ p).mp
    have htotal := h ν
    rw [htotal]
    exact Set.mem_univ p
  · intro h ν
    apply Set.eq_univ_iff_forall.mpr
    intro p
    apply (cover_denote_closed M C hC hne star hstar hψ ν ρ p).mpr
    exact h p.1.property

end Cover

/-- **Theorem 13 (semantic localization).**  `Γ ⊨ φ ↔ Δ_Γ ⊨loc φ`.

`(⇐)` is Lemma 7.  `(⇒)` is contrapositive: a local countermodel gives a point
`w` with `w ∈ ⟦Δ_Γ⟧` and `w ∉ ⟦φ⟧`; take `C := ⇝*[w]`, which is backward
closed, contains `w`, and satisfies `C ⊆ ⟦Γ⟧` by Lemma 8.  If `C = M` we are
done; otherwise the double cover `N` of Definition 10 satisfies `Γ` and refutes
`φ`, by Corollary 12. -/
theorem semantic_localization_of_closed_Γ {Γ : Set (Pattern S Var)}
    {φ : Pattern S Var} (hΓ : ∀ γ ∈ Γ, Closed γ) :
    GlobalCons Γ φ ↔ LocalCons (localize Γ) φ := by
  classical
  constructor
  · intro hglobal M ρ w hw
    by_contra hwφ
    let C : Set M.carrier := M.denoteSet ρ (localize Γ)
    have hwC : w ∈ C := hw
    have hCdata := backwardClosed_denoteSet_localize M ρ Γ
    have hC : M.BackwardClosed C := hCdata.1
    have hCΓ : C ⊆ M.denoteSet ρ Γ := hCdata.2
    by_cases hfull : C = Set.univ
    · have hsatΓ : M.SatSet Γ := by
        intro γ hγ ρ'
        unfold Model.Total
        rw [denote_closed M (hΓ γ hγ) ρ' ρ]
        apply Set.eq_univ_iff_forall.mpr
        intro u
        have huC : u ∈ C := by
          rw [hfull]
          exact Set.mem_univ u
        have huΓ := hCΓ huC
        have huΓ' : ∀ δ, δ ∈ Γ → u ∈ M.denote ρ δ := by
          simpa only [Model.denoteSet, Set.mem_iInter] using huΓ
        exact huΓ' γ hγ
      have hsatφ := hglobal M hsatΓ ρ
      apply hwφ
      rw [hsatφ]
      exact Set.mem_univ w
    · have hne : C.Nonempty := ⟨w, hwC⟩
      obtain ⟨star, hstar⟩ := (Set.ne_univ_iff_exists_notMem C).mp hfull
      let N : Model S := cover M C hne
      have hsatΓ : N.SatSet Γ := by
        intro γ hγ
        apply (cover_sat_iff M C hC hne star hstar (hΓ γ hγ) ρ).mpr
        intro u huC
        have huΓ := hCΓ huC
        have huΓ' : ∀ δ, δ ∈ Γ → u ∈ M.denote ρ δ := by
          simpa only [Model.denoteSet, Set.mem_iInter] using huΓ
        exact huΓ' γ hγ
      let ν : Var → C × Bool := fun x =>
        if hx : ρ x ∈ C then (⟨ρ x, hx⟩, false) else (⟨w, hwC⟩, true)
      let ρ' : Var → M.carrier := fun x => proj M C star false (ν x)
      have hagree : AgreeOn C ρ ρ' := by
        intro x
        by_cases hx : ρ x ∈ C
        · exact Or.inl ⟨by simp [ρ', ν, hx, proj], hx⟩
        · exact Or.inr ⟨hx, by simp [ρ', ν, hx, proj, hstar]⟩
      have hloc := locality M hC φ ρ ρ' hagree
      have hwφ' : w ∉ M.denote ρ' φ := by
        intro hw'
        have hm : w ∈ M.denote ρ' φ ∩ C := ⟨hw', hwC⟩
        rw [← hloc] at hm
        exact hwφ hm.1
      let q : C × Bool := (⟨w, hwC⟩, false)
      have hqφ : q ∉ N.denote ν φ := by
        intro hq
        have hproj := (two_copies M C hC hne star hstar φ ν q).mp hq
        apply hwφ'
        simpa [N, q, ρ'] using hproj
      apply hqφ
      have hsatφ := hglobal N hsatΓ ν
      rw [hsatφ]
      exact Set.mem_univ q
  · exact globalCons_of_localCons_localize

/-- **Theorem 13 (paper-facing statement).**  The paper assumes the conclusion
closed globally; the mechanized proof above shows that assumption is unused. -/
theorem semantic_localization {Γ : Set (Pattern S Var)} {φ : Pattern S Var}
    (hΓ : ∀ γ ∈ Γ, Closed γ) (_hφ : Closed φ) :
    GlobalCons Γ φ ↔ LocalCons (localize Γ) φ :=
  semantic_localization_of_closed_Γ hΓ

end MatchingLogic
