/-
Copyright (c) 2026 Aurélien Eveil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Eveil, Anthropic, OpenAI
-/

/-
Localization: Definition 6, Lemma 7 and Lemma 8 of arXiv:2608.13306v1,
Section 3.

Definitions are written by the coordinating session from the paper; the statements below were pinned
before any proof was attempted.

Note on Lemma 7.  The paper obtains `M ⊨ Γ iff M ⊨ Δ_Γ` proof-theoretically:
every member of `Δ_Γ` is derivable from `Γ` by Lemma 5 (necessitation), and
soundness (S) transfers this to models.  The same equivalence is available
semantically, directly from Lemma 4, and that is the route taken here -- so
this file needs no proof system.  Lemma 5 itself belongs with the proof system
and is not in this file.
-/
import LeanPool.MatchingLogic.Boxes

/-!
# MatchingLogic.Localization
-/

namespace MatchingLogic

variable {S : Signature} {Var : Type} [DecidableEq Var]

/-- **Definition 6 (localization).**  `Δ_Γ := {[p]γ | γ ∈ Γ, p ∈ E*}`. -/
def localize (Γ : Set (Pattern S Var)) : Set (Pattern S Var) :=
  {ψ | ∃ γ ∈ Γ, ∃ p : List (Coord S), ψ = boxes p γ}

omit [DecidableEq Var] in
/-- `Γ ⊆ Δ_Γ`, by taking `p = ε`. -/
theorem subset_localize (Γ : Set (Pattern S Var)) : Γ ⊆ localize Γ := by
  intro γ hγ
  exact ⟨γ, hγ, [], rfl⟩

omit [DecidableEq Var] in
/-- Every member of `Δ_Γ` is closed when every member of `Γ` is, so `⟦Δ_Γ⟧` is
well defined. -/
theorem closed_of_mem_localize {Γ : Set (Pattern S Var)}
    (hΓ : ∀ γ ∈ Γ, Closed γ) : ∀ ψ ∈ localize Γ, Closed ψ := by
  rintro ψ ⟨γ, hγ, p, rfl⟩
  exact (closed_boxes p γ).2 (hΓ γ hγ)

/-- **Lemma 8.**  `⟦Δ_Γ⟧ = {u | ⇝*[u] ⊆ ⟦Γ⟧}`. -/
theorem denoteSet_localize (M : Model S) (ρ : Var → M.carrier)
    (Γ : Set (Pattern S Var)) :
    M.denoteSet ρ (localize Γ) =
      {u | ∀ v, Relation.ReflTransGen M.Step u v → v ∈ M.denoteSet ρ Γ} := by
  ext u
  simp only [Model.denoteSet, Set.mem_iInter, Set.mem_ofPred_eq]
  constructor
  · intro hu v huv γ hγ
    obtain ⟨p, hp⟩ := (M.reflTransGen_step_iff_exists_word u v).mp huv
    have hbox : u ∈ M.denote ρ (boxes p γ) :=
      hu (boxes p γ) ⟨γ, hγ, p, rfl⟩
    rw [denote_boxes] at hbox
    exact hbox v hp
  · rintro hu ψ ⟨γ, hγ, p, rfl⟩
    rw [denote_boxes]
    intro v hp
    exact hu v ((M.reflTransGen_step_iff_exists_word u v).mpr ⟨p, hp⟩) γ hγ

/-- **Lemma 8**, second half: `⟦Δ_Γ⟧` is backward closed and contained in
`⟦Γ⟧`. -/
theorem backwardClosed_denoteSet_localize (M : Model S) (ρ : Var → M.carrier)
    (Γ : Set (Pattern S Var)) :
    M.BackwardClosed (M.denoteSet ρ (localize Γ)) ∧
      M.denoteSet ρ (localize Γ) ⊆ M.denoteSet ρ Γ := by
  constructor
  · rw [denoteSet_localize]
    intro u hu v huv w hvw
    exact hu w (Relation.ReflTransGen.head huv hvw)
  · rw [denoteSet_localize]
    intro u hu
    exact hu u Relation.ReflTransGen.refl

/-- **Lemma 8**, third half: it is the *largest* such set. -/
theorem denoteSet_localize_greatest (M : Model S) (ρ : Var → M.carrier)
    (Γ : Set (Pattern S Var)) {U : Set M.carrier}
    (hU : M.BackwardClosed U) (hUΓ : U ⊆ M.denoteSet ρ Γ) :
    U ⊆ M.denoteSet ρ (localize Γ) := by
  rw [denoteSet_localize]
  intro u hu v huv
  apply hUΓ
  induction huv with
  | refl => exact hu
  | tail _ hyz ih => exact hU ih hyz

/-- `M ⊨ Γ` and `M ⊨ Δ_Γ` are equivalent: localizing does not change the
models.  Proved here from Lemma 4 rather than from necessitation. -/
theorem satSet_localize_iff (M : Model S) {Γ : Set (Pattern S Var)}
    : M.SatSet (localize Γ) ↔ M.SatSet Γ := by
  constructor
  · intro hloc γ hγ
    exact hloc γ (subset_localize Γ hγ)
  · rintro hsat ψ ⟨γ, hγ, p, rfl⟩ ρ
    change M.denote ρ (boxes p γ) = Set.univ
    rw [denote_boxes]
    ext u
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    intro v _
    rw [hsat γ hγ ρ]
    exact Set.mem_univ v

/-- **Lemma 7.**  If `Δ_Γ ⊨loc φ` then `Γ ⊨ φ`. -/
theorem globalCons_of_localCons_localize {Γ : Set (Pattern S Var)}
    {φ : Pattern S Var} (h : LocalCons (localize Γ) φ) : GlobalCons Γ φ := by
  intro M hM ρ
  have hloc : M.SatSet (localize Γ) := (satSet_localize_iff M).2 hM
  apply Set.eq_univ_of_forall
  intro u
  apply h M ρ
  simp only [Model.denoteSet, Set.mem_iInter]
  intro ψ hψ
  rw [hloc ψ hψ ρ]
  exact Set.mem_univ u

end MatchingLogic
