/-
Copyright (c) 2026 Aurélien Eveil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Eveil, Anthropic, OpenAI
-/

/-
Lemma 9 (locality) of arXiv:2608.13306v1, Section 4.

  "Let ρ, ρ' : Var → M satisfy, for every x: either ρ(x) = ρ'(x) ∈ C, or
   ρ(x) ∉ C and ρ'(x) ∉ C.  Then ρ(ψ) ∩ C = ρ'(ψ) ∩ C for every pattern ψ."

Throughout, C is backward closed (Definition 2).

The statement was pinned before any proof was attempted, and was proved
independently by two lanes in different model families against that same pinned
statement.  The proof below is the in-house one.  `locality` is byte-identical
to the pinned form; only the proof body was supplied.
-/
import LeanPool.MatchingLogic.Core

/-!
# MatchingLogic.Locality
-/

namespace MatchingLogic

variable {S : Signature} {Var : Type} [DecidableEq Var]

/-- The agreement condition of Lemma 9: on `C` the two valuations coincide, and
off `C` they are both off `C`. -/
def AgreeOn {M : Model S} (C : Set M.carrier) (ρ ρ' : Var → M.carrier) : Prop :=
  ∀ x, (ρ x = ρ' x ∧ ρ x ∈ C) ∨ (ρ x ∉ C ∧ ρ' x ∉ C)

/-- The concrete identity behind the `app`/symbol case of the paper's proof:
`σ_M(A₁,…,Aₙ) ∩ C = σ_M(A₁∩C,…,Aₙ∩C) ∩ C`.  Backward closure of `C` is used to
pull each witnessing tuple entry into `C` once the produced point already lies
in `C`. -/
theorem Model.app_inter_backwardClosed {M : Model S} {C : Set M.carrier}
    (hC : M.BackwardClosed C) (σ : S.Sym) (A : Fin (S.arity σ) → Set M.carrier) :
    M.app σ A ∩ C = M.app σ (fun i => A i ∩ C) ∩ C := by
  ext u
  simp only [Model.app, Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨a, ha, hu⟩, huC⟩
    exact ⟨⟨a, fun i => ⟨ha i, Model.BackwardClosed.mem_of_interp M hC huC hu i⟩, hu⟩, huC⟩
  · rintro ⟨⟨a, ha, hu⟩, huC⟩
    exact ⟨⟨a, fun i => (ha i).1, hu⟩, huC⟩

/-- `AgreeOn` is preserved by matched updates: updating both valuations at the
same variable to the same value keeps them agreeing, whether or not that value
lies in `C`. -/
theorem AgreeOn.update {M : Model S} {C : Set M.carrier} {ρ ρ' : Var → M.carrier}
    (h : AgreeOn C ρ ρ') (x : Var) (a : M.carrier) :
    AgreeOn C (Function.update ρ x a) (Function.update ρ' x a) := by
  intro y
  rcases eq_or_ne y x with hy | hy
  · subst hy
    simp only [Function.update_apply]
    rcases Classical.em (a ∈ C) with ha | ha
    · exact Or.inl ⟨rfl, ha⟩
    · exact Or.inr ⟨ha, ha⟩
  · simp only [Function.update_apply, ite_eq_right hy]
    exact h y

/-- **Lemma 9 (locality).**  A backward-closed `C` together with one bit per
variable -- whether that variable's value lies in `C` -- determines truth on `C`. -/
theorem locality (M : Model S) {C : Set M.carrier} (hC : M.BackwardClosed C)
    (ψ : Pattern S Var) (ρ ρ' : Var → M.carrier) (h : AgreeOn C ρ ρ') :
    M.denote ρ ψ ∩ C = M.denote ρ' ψ ∩ C := by
  induction ψ generalizing ρ ρ' with
  | var x =>
    simp only [denote_var]
    rcases h x with ⟨heq, _⟩ | ⟨hxC, hxC'⟩
    · rw [heq]
    · ext u
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨rfl, hu⟩; exact absurd hu hxC
      · rintro ⟨rfl, hu⟩; exact absurd hu hxC'
  | bot => simp
  | app σ f ih =>
    simp only [denote_app]
    rw [Model.app_inter_backwardClosed hC σ (fun i => M.denote ρ (f i)),
        Model.app_inter_backwardClosed hC σ (fun i => M.denote ρ' (f i))]
    congr 2
    funext i
    exact ih i ρ ρ' h
  | imp φ ψ ihφ ihψ =>
    ext u
    simp only [denote_imp, Set.mem_inter_iff, Set.mem_union, Set.mem_compl_iff]
    constructor
    · rintro ⟨hu, huC⟩
      refine ⟨?_, huC⟩
      rcases hu with hu | hu
      · left
        intro hφ'
        apply hu
        have hmem : u ∈ M.denote ρ' φ ∩ C := ⟨hφ', huC⟩
        rw [← ihφ ρ ρ' h] at hmem
        exact hmem.1
      · right
        have hmem : u ∈ M.denote ρ ψ ∩ C := ⟨hu, huC⟩
        rw [ihψ ρ ρ' h] at hmem
        exact hmem.1
    · rintro ⟨hu, huC⟩
      refine ⟨?_, huC⟩
      rcases hu with hu | hu
      · left
        intro hφ
        apply hu
        have hmem : u ∈ M.denote ρ φ ∩ C := ⟨hφ, huC⟩
        rw [ihφ ρ ρ' h] at hmem
        exact hmem.1
      · right
        have hmem : u ∈ M.denote ρ' ψ ∩ C := ⟨hu, huC⟩
        rw [← ihψ ρ ρ' h] at hmem
        exact hmem.1
  | ex x φ ih =>
    ext u
    simp only [denote_ex, Set.mem_inter_iff, Set.mem_iUnion]
    constructor
    · rintro ⟨⟨a, ha⟩, huC⟩
      refine ⟨⟨a, ?_⟩, huC⟩
      have hmem : u ∈ M.denote (Function.update ρ x a) φ ∩ C := ⟨ha, huC⟩
      rw [ih (Function.update ρ x a) (Function.update ρ' x a) (h.update x a)] at hmem
      exact hmem.1
    · rintro ⟨⟨a, ha⟩, huC⟩
      refine ⟨⟨a, ?_⟩, huC⟩
      have hmem : u ∈ M.denote (Function.update ρ' x a) φ ∩ C := ⟨ha, huC⟩
      rw [← ih (Function.update ρ x a) (Function.update ρ' x a) (h.update x a)] at hmem
      exact hmem.1

end MatchingLogic
