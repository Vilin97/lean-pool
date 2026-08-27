/-
Copyright (c) 2026 Aurélien Eveil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Eveil, Anthropic, OpenAI
-/

/-
What the paper's hypotheses are actually doing.

The paper states Theorem 13 and Lemma 7 for closed `Γ` and closed `φ`, having
assumed at the top of Section 2 that both are closed without loss of generality.
That is a perfectly good convention for a paper. Mechanization makes it worth
asking, for each hypothesis separately, whether it is doing work.

The answers are not uniform, and that is the point of this file:

* `Closed φ` is NOT needed, in Theorem 13 or in Lemma 7. Both hold for an
  arbitrary, possibly open conclusion.
* `Closed γ` for `γ ∈ Γ` IS needed in Theorem 13, and the countermodel is small.
* Localizing is NOT a convenience: replacing `Δ_Γ` by `Γ` makes Theorem 13
  false.

The third is the sharpest. `semantic_localization` says
`Γ ⊨ φ ↔ Δ_Γ ⊨loc φ`, and a reader may reasonably wonder how much distance
there is between `⊨` and `⊨loc` once `Γ` has been localized. The answer is that
the localization is exactly what closes the gap, and without it the two sides
come apart.

Statements pinned before any proof was attempted.
-/
import LeanPool.MatchingLogic.Composite

/-!
# MatchingLogic.Independence
-/

namespace MatchingLogic

variable {S : Signature} {Var : Type} [DecidableEq Var]

/-! ### Hypotheses that cannot be dropped -/

/-- **Theorem 13 DOES need every member of `Γ` closed.**

An open `Γ` constrains the model through the valuation quantifier hidden inside
totality, and localization cannot see that. -/
theorem semantic_localization_needs_closed_Γ :
    ¬ (∀ (S : Signature) (Var : Type) (_ : DecidableEq Var)
         (Γ : Set (Pattern S Var)) (φ : Pattern S Var), Closed φ →
         (GlobalCons Γ φ ↔ LocalCons (localize Γ) φ)) := by
  intro hall
  let S₀ : Signature := ⟨Empty, fun e => Empty.elim e⟩
  let Γ : Set (Pattern S₀ Bool) := {Pattern.var false}
  let φ : Pattern S₀ Bool :=
    Pattern.al false (Pattern.al true (.imp (.var false) (.var true)))
  have hφ : Closed φ := by
    simp [φ, Closed]
  have hglobal : GlobalCons Γ φ := by
    intro M hM ρ
    have hone : ∀ a b : M.carrier, a = b := by
      intro a b
      have htotal := hM (.var false) (by simp [Γ]) (fun _ => a)
      have hb : b ∈ M.denote (fun _ : Bool => a) (.var false) := by
        rw [htotal]
        exact Set.mem_univ b
      have hba : b = a := by simpa using hb
      exact hba.symm
    unfold Model.Total
    apply Set.eq_univ_iff_forall.mpr
    intro u
    change u ∈ M.denote ρ
      (Pattern.al false (Pattern.al true (.imp (.var false) (.var true))))
    rw [denote_al]
    simp only [Set.mem_iInter]
    intro a
    rw [denote_al]
    simp only [Set.mem_iInter]
    intro b
    simp only [denote_imp, Set.mem_union, Set.mem_compl_iff, denote_var,
      Set.mem_singleton_iff]
    right
    simpa using hone u b
  have hnotlocal : ¬LocalCons (localize Γ) φ := by
    intro hlocal
    let M₀ : Model S₀ :=
      { carrier := Bool
        nonempty := ⟨false⟩
        interp := fun e => Empty.elim e }
    let ρ₀ : Bool → Bool := fun _ => false
    have hwΓ : false ∈ M₀.denoteSet ρ₀ (localize Γ) := by
      simp only [Model.denoteSet, Set.mem_iInter]
      rintro ψ ⟨γ, hγ, p, rfl⟩
      have hγ' : γ = Pattern.var false := by simpa [Γ] using hγ
      subst γ
      cases p with
      | nil => rfl
      | cons e p => exact Empty.elim e.1
    have hwφ := hlocal M₀ ρ₀ hwΓ
    change false ∈ M₀.denote ρ₀
      (Pattern.al false (Pattern.al true (.imp (.var false) (.var true)))) at hwφ
    rw [denote_al] at hwφ
    simp only [Set.mem_iInter] at hwφ
    have h₁ := hwφ false
    rw [denote_al] at h₁
    simp only [Set.mem_iInter] at h₁
    have h₂ := h₁ true
    simp [M₀, ρ₀] at h₂
  exact hnotlocal ((hall S₀ Bool inferInstance Γ φ hφ).mp hglobal)

/-! ### Localization is not decoration -/

/-- **Replacing `Δ_Γ` by `Γ` makes Theorem 13 false**, even for closed `Γ` and
closed `φ`.  So the localization in `semantic_localization` is load-bearing and
the theorem forbids something. -/
theorem localize_not_redundant :
    ¬ (∀ (S : Signature) (Var : Type) (_ : DecidableEq Var)
         (Γ : Set (Pattern S Var)) (φ : Pattern S Var),
         (∀ γ ∈ Γ, Closed γ) → Closed φ →
         (GlobalCons Γ φ ↔ LocalCons Γ φ)) := by
  intro hall
  let S₁ : Signature := ⟨Bool, fun _ => 1⟩
  let γ : Pattern S₁ Bool := .ex false (.app false (fun _ => .var false))
  let e : Coord S₁ := ⟨true, 0⟩
  let φ : Pattern S₁ Bool := box e γ
  let Γ : Set (Pattern S₁ Bool) := {γ}
  have hγ : Closed γ := by
    simp [γ, Closed]
  have hΓ : ∀ δ ∈ Γ, Closed δ := by
    intro δ hδ
    have : δ = γ := by simpa [Γ] using hδ
    simpa [this] using hγ
  have hφ : Closed φ := by
    unfold Closed at hγ ⊢
    simpa [φ] using hγ
  have hglobal : GlobalCons Γ φ := by
    intro M hM ρ
    have hγtotal := hM γ (by simp [Γ]) ρ
    unfold Model.Total
    change M.denote ρ (box e γ) = Set.univ
    rw [denote_box]
    ext u
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    intro v _
    rw [hγtotal]
    exact Set.mem_univ v
  have hsatisfiable : ∃ M : Model S₁, M.SatSet Γ := by
    let T : Model S₁ :=
      { carrier := Bool
        nonempty := ⟨false⟩
        interp := fun _ _ => Set.univ }
    refine ⟨T, ?_⟩
    intro δ hδ ρ
    have hδ' : δ = γ := by simpa [Γ] using hδ
    subst δ
    unfold Model.Total
    apply Set.eq_univ_iff_forall.mpr
    intro u
    rw [show γ = .ex false (.app false (fun _ => .var false)) by rfl,
      denote_ex]
    apply Set.mem_iUnion.mpr
    refine ⟨u, ?_⟩
    rw [denote_app]
    refine ⟨fun _ => u, ?_, ?_⟩
    · intro i
      simp
    · exact Set.mem_univ u
  have hglobal_nonvacuous : GlobalCons Γ φ ∧ ∃ M : Model S₁, M.SatSet Γ :=
    ⟨hglobal, hsatisfiable⟩
  have hnotlocal : ¬LocalCons Γ φ := by
    intro hlocal
    let M₁ : Model S₁ :=
      { carrier := Bool
        nonempty := ⟨false⟩
        interp := fun σ a => match σ with
          | false => {false}
          | true => if a 0 = true then {false} else ∅ }
    let ρ₁ : Bool → Bool := fun _ => false
    have hwΓ : false ∈ M₁.denoteSet ρ₁ Γ := by
      simp only [Model.denoteSet, Set.mem_iInter]
      intro δ hδ
      have hδ' : δ = γ := by simpa [Γ] using hδ
      subst δ
      rw [show γ = .ex false (.app false (fun _ => .var false)) by rfl,
        denote_ex]
      apply Set.mem_iUnion.mpr
      refine ⟨false, ?_⟩
      rw [denote_app]
      refine ⟨fun _ => false, ?_, ?_⟩
      · intro i
        simp
      · rfl
    have hwφ := hlocal M₁ ρ₁ hwΓ
    change false ∈ M₁.denote ρ₁ (box e γ) at hwφ
    rw [denote_box] at hwφ
    have hstep : M₁.stepAt e false true := by
      refine ⟨fun _ => true, ?_, rfl⟩
      rfl
    have hvγ := hwφ true hstep
    rw [show γ = .ex false (.app false (fun _ => .var false)) by rfl,
      denote_ex] at hvγ
    obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hvγ
    rw [denote_app] at ha
    obtain ⟨A, _, hout⟩ := ha
    exact Bool.noConfusion hout
  exact hnotlocal ((hall S₁ Bool inferInstance Γ φ hΓ hφ).mp hglobal_nonvacuous.1)

end MatchingLogic
