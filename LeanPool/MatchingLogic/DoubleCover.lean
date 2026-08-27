/-
Copyright (c) 2026 Aurélien Eveil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Eveil, Anthropic, OpenAI
-/

/-
Definition 10 (the double cover) and Lemma 11 (two copies) of
arXiv:2608.13306v1, Section 4.

Definition 10 and the statements of Lemma 11 were pinned before any proof was
attempted, and two lanes in different model families proved them independently
against that same pinned form.  The proofs below are the codex lane's.  `cover`,
`coverInterp`, `proj` and both theorem statements are byte-identical to the
pinned form, checked against the kernel's own printing of their types and
bodies.

Note on the constant case.  Definition 10 gives constants `σ_N := (σ_M ∩ C) × {0,1}`,
i.e. the SAME subset in both copies; the paper warns that assigning it to one
copy only would break Lemma 11 at `ψ = σ`.  The uniform clause below reproduces
this automatically: the unmixedness condition `∀ j, (A j).2 = p.2` is vacuous
when the arity is `0`, so both copies are populated.
-/
import LeanPool.MatchingLogic.Locality

/-!
# MatchingLogic.DoubleCover
-/

namespace MatchingLogic

variable {S : Signature} {Var : Type} [DecidableEq Var]

section Cover

variable (M : Model S) (C : Set M.carrier)

/-- The interpretation of Definition 10: a tuple contributes only when it is
unmixed, and then it contributes `σ_M(ā) ∩ C` in its own copy. -/
def coverInterp (σ : S.Sym) (A : Fin (S.arity σ) → (C × Bool)) : Set (C × Bool) :=
  {p | (∀ j, (A j).2 = p.2) ∧
       ((p.1 : M.carrier) ∈ M.interp σ (fun j => ((A j).1 : M.carrier)))}

/-- **Definition 10.**  The double cover `N := C × {0,1}`.

Definition 10 sits under the standing assumptions `∅ ≠ C ≠ M` and `C` backward
closed, and picks `star ∈ M \ C`.  `cover` and `proj` below do NOT carry those
assumptions in their own signatures -- only `C.Nonempty`, which the carrier
needs.  Backward closure, and `star ∉ C`, are hypotheses of Lemma 11 instead.
So `cover` and `proj` are well formed outside the paper's domain, where they
mean nothing; every theorem about them restores the assumptions. -/
def cover (hne : C.Nonempty) : Model S where
  carrier := C × Bool
  nonempty := ⟨(⟨hne.choose, hne.choose_spec⟩, false)⟩
  interp := coverInterp M C

/-- The projections `π_i : N → M` of Definition 10: keep copy `i`, and send the
other copy to a fixed `star ∈ M \ C`. -/
def proj (star : M.carrier) (i : Bool) (p : C × Bool) : M.carrier :=
  if p.2 = i then (p.1 : M.carrier) else star

private theorem proj_update (star : M.carrier) (i : Bool)
    (ν : Var → (C × Bool)) (x : Var) (n : C × Bool) :
    (fun y => proj M C star i (Function.update ν x n y)) =
      Function.update (fun y => proj M C star i (ν y)) x (proj M C star i n) := by
  funext y
  by_cases h : y = x
  · subst y
    simp
  · simp [Function.update, h]

/-- **Lemma 11 (two copies)**, in membership form.  Equivalent to the display in
the paper (see `two_copies_set`); this form is the one to prove by induction. -/
theorem two_copies (hC : M.BackwardClosed C) (hne : C.Nonempty)
    (star : M.carrier) (hstar : star ∉ C)
    (ψ : Pattern S Var) (ν : Var → (C × Bool)) (p : C × Bool) :
    p ∈ (cover M C hne).denote ν ψ ↔
      (p.1 : M.carrier) ∈ M.denote (fun x => proj M C star p.2 (ν x)) ψ := by
  classical
  simp only [cover]
  induction ψ generalizing ν p with
  | var x =>
      simp only [Model.denote, Set.mem_singleton_iff]
      constructor
      · intro hp
        subst p
        simp [proj]
      · intro hp
        by_cases hb : (ν x).2 = p.2
        · apply Prod.ext
          · apply Subtype.ext
            simpa [proj, hb] using hp
          · exact hb.symm
        · exfalso
          have hpstar : (p.1 : M.carrier) = star := by
            simpa [proj, hb] using hp
          apply hstar
          rw [← hpstar]
          exact p.1.property
  | app σ f ih =>
      simp only [denote_app, Model.app, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨A, hA, hmix, hinterp⟩
        refine ⟨fun j => ((A j).1 : M.carrier), ?_, hinterp⟩
        intro j
        have hj := (ih j (ν := ν) (p := A j)).mp (hA j)
        simpa [proj, hmix j] using hj
      · rintro ⟨a, ha, hinterp⟩
        have haC : ∀ j, a j ∈ C := fun j =>
          Model.BackwardClosed.mem_of_interp M hC p.1.property hinterp j
        let A : Fin (S.arity σ) → (C × Bool) :=
          fun j => (⟨a j, haC j⟩, p.2)
        refine ⟨A, ?_, ?_, ?_⟩
        · intro j
          apply (ih j (ν := ν) (p := A j)).mpr
          simpa [A, proj] using ha j
        · intro j
          rfl
        · simpa [A] using hinterp
  | imp φ χ ihφ ihχ =>
      simp only [denote_imp, Set.mem_union, Set.mem_compl_iff]
      constructor
      · rintro (hφ | hχ)
        · left
          intro hpφ
          exact hφ ((ihφ (ν := ν) (p := p)).mpr hpφ)
        · right
          exact (ihχ (ν := ν) (p := p)).mp hχ
      · rintro (hφ | hχ)
        · left
          intro hpφ
          exact hφ ((ihφ (ν := ν) (p := p)).mp hpφ)
        · right
          exact (ihχ (ν := ν) (p := p)).mpr hχ
  | bot =>
      exact ⟨id, id⟩
  | ex x φ ih =>
      rw [denote_ex, denote_ex]
      constructor
      · intro hp
        obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hp
        apply Set.mem_iUnion.mpr
        refine ⟨proj M C star p.2 n, ?_⟩
        rw [← proj_update (M := M) (C := C) star p.2 ν x n]
        exact (ih (ν := Function.update ν x n) (p := p)).mp hn
      · intro hp
        obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hp
        by_cases haC : a ∈ C
        · let n : C × Bool := (⟨a, haC⟩, p.2)
          apply Set.mem_iUnion.mpr
          refine ⟨n, (ih (ν := Function.update ν x n) (p := p)).mpr ?_⟩
          rw [proj_update (M := M) (C := C) star p.2 ν x n]
          simpa [n, proj] using ha
        · let ρ : Var → M.carrier := fun y => proj M C star p.2 (ν y)
          have hagree : AgreeOn C (Function.update ρ x a)
              (Function.update ρ x star) := by
            intro y
            by_cases hy : y = x
            · subst y
              simp [haC, hstar]
            · simp only [Function.update, hy]
              by_cases hyC : ρ y ∈ C
              · exact Or.inl ⟨rfl, hyC⟩
              · exact Or.inr ⟨hyC, hyC⟩
          have hloc := locality M hC φ (Function.update ρ x a)
            (Function.update ρ x star) hagree
          have hstarDen : (p.1 : M.carrier) ∈
              M.denote (Function.update ρ x star) φ := by
            have hpC : (p.1 : M.carrier) ∈
                M.denote (Function.update ρ x a) φ ∩ C := ⟨ha, p.1.property⟩
            rw [hloc] at hpC
            exact hpC.1
          let n : C × Bool := (⟨hne.choose, hne.choose_spec⟩, !p.2)
          apply Set.mem_iUnion.mpr
          refine ⟨n, (ih (ν := Function.update ν x n) (p := p)).mpr ?_⟩
          rw [proj_update (M := M) (C := C) star p.2 ν x n]
          simpa [ρ, n, proj] using hstarDen

/-- **Lemma 11 (two copies)**, in the paper's displayed set form:
`ν(ψ)_N = (π₀(ν)(ψ)_M ∩ C) × {0} ∪ (π₁(ν)(ψ)_M ∩ C) × {1}`.
The `∩ C` is absorbed by the subtype `↥C`. -/
theorem two_copies_set (hC : M.BackwardClosed C) (hne : C.Nonempty)
    (star : M.carrier) (hstar : star ∉ C)
    (ψ : Pattern S Var) (ν : Var → (C × Bool)) :
    (cover M C hne).denote ν ψ =
      {p : C × Bool | p.2 = false ∧
        (p.1 : M.carrier) ∈ M.denote (fun x => proj M C star false (ν x)) ψ} ∪
      {p : C × Bool | p.2 = true ∧
        (p.1 : M.carrier) ∈ M.denote (fun x => proj M C star true (ν x)) ψ} := by
  apply Set.ext
  intro p
  change p ∈ (cover M C hne).denote ν ψ ↔
    (p.2 = false ∧
      (p.1 : M.carrier) ∈ M.denote (fun x => proj M C star false (ν x)) ψ) ∨
    (p.2 = true ∧
      (p.1 : M.carrier) ∈ M.denote (fun x => proj M C star true (ν x)) ψ)
  rcases p with ⟨q, b⟩
  cases b with
  | false =>
      constructor
      · intro hp
        exact Or.inl ⟨rfl,
          (two_copies M C hC hne star hstar ψ ν (q, false)).mp hp⟩
      · rintro (⟨_, hp⟩ | ⟨hbad, _⟩)
        · exact (two_copies M C hC hne star hstar ψ ν (q, false)).mpr hp
        · cases hbad
  | true =>
      constructor
      · intro hp
        exact Or.inr ⟨rfl,
          (two_copies M C hC hne star hstar ψ ν (q, true)).mp hp⟩
      · rintro (⟨hbad, _⟩ | ⟨_, hp⟩)
        · cases hbad
        · exact (two_copies M C hC hne star hstar ψ ν (q, true)).mpr hp

end Cover

end MatchingLogic
