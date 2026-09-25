/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Skein.Composition

/-!
# Isomorphism theory of fragments

An equivalence of fragments `Fragment.Equiv W₁ W₂` (defined in
`RS/Definitions.lean`) is a pair of type equivalences on flags and
vertices commuting with attachment, pairing, and boundary-flag
data, preserving the circle count.  This module proves the
equivalences form a groupoid (refl, symm, trans) and are
congruences for the fragment operations: relabelling, disjoint
union, and single-pair gluing.
-/

@[expose] public section

namespace RS

namespace Fragment

variable {α β : Type}

namespace Equiv

variable {W₁ W₂ W₃ : Fragment α}

/-- The flag equivalence sends boundary flags to boundary flags. -/
theorem boundaryFlag_comm (e : Equiv W₁ W₂) (ℓ : α) :
    e.flagEquiv (W₁.boundaryFlag ℓ) = W₂.boundaryFlag ℓ := by
  apply W₂.eq_boundaryFlag ℓ
  rw [e.attach_comm]
  simp [W₁.attach_boundaryFlag]

/-- The identity equivalence. -/
def refl (W : Fragment α) : Equiv W W where
  flagEquiv := _root_.Equiv.refl _
  vertexEquiv := _root_.Equiv.refl _
  attach_comm := fun f => by
    change W.attach f = (W.attach f).map (_root_.Equiv.refl _) id
    rcases W.attach f with v | ℓ <;> simp
  pairing_comm := fun _ => rfl
  circles_eq := rfl

/-- The inverse equivalence. -/
def symm (e : Equiv W₁ W₂) : Equiv W₂ W₁ where
  flagEquiv := e.flagEquiv.symm
  vertexEquiv := e.vertexEquiv.symm
  attach_comm := fun f => by
    have h := e.attach_comm (e.flagEquiv.symm f)
    simp? at h
    rw [h]
    rcases W₁.attach (e.flagEquiv.symm f) with v | ℓ <;> simp
  pairing_comm := fun f => by
    have h := e.pairing_comm (e.flagEquiv.symm f)
    simp? at h
    rw [← h]
    simp
  circles_eq := e.circles_eq.symm

/-- The composite equivalence. -/
def trans (e₁ : Equiv W₁ W₂) (e₂ : Equiv W₂ W₃) : Equiv W₁ W₃ where
  flagEquiv := e₁.flagEquiv.trans e₂.flagEquiv
  vertexEquiv := e₁.vertexEquiv.trans e₂.vertexEquiv
  attach_comm := fun f => by
    simp? [_root_.Equiv.trans_apply]
    rw [e₂.attach_comm, e₁.attach_comm]
    rcases W₁.attach f with v | ℓ <;> simp
  pairing_comm := fun f => by
    simp? [_root_.Equiv.trans_apply]
    rw [e₁.pairing_comm, e₂.pairing_comm]
  circles_eq := e₁.circles_eq.trans e₂.circles_eq

/-! ### Congruences -/

/-- Relabelling commutes with fragment equivalence. -/
def relabelCongr (e : Equiv W₁ W₂) (σ : α ≃ β) :
    Equiv (W₁.relabel σ) (W₂.relabel σ) where
  flagEquiv := e.flagEquiv
  vertexEquiv := e.vertexEquiv
  attach_comm := fun f => by
    -- The goal involves `(W.relabel σ).attach` which unfolds to
    -- `(W.attach f).map id σ`.  Abstracting over the Sum value
    -- avoids type-level transparency mismatches with `rw`.
    have h := e.attach_comm f
    suffices key : ∀ (a : W₂.Vertex ⊕ α) (b : W₁.Vertex ⊕ α),
        a = b.map e.vertexEquiv id →
        a.map id σ = (b.map id σ).map e.vertexEquiv id from
      key _ _ h
    intro a b hab
    subst hab
    rcases b with v | ℓ <;> rfl
  pairing_comm := fun f => e.pairing_comm f
  circles_eq := e.circles_eq

variable {V₁ V₂ : Fragment β}

/-- Disjoint union commutes with fragment equivalence. -/
def disjUnionCongr (e₁ : Equiv W₁ W₂) (e₂ : Equiv V₁ V₂) :
    Equiv (W₁.disjUnion V₁) (W₂.disjUnion V₂) where
  flagEquiv := _root_.Equiv.sumCongr e₁.flagEquiv e₂.flagEquiv
  vertexEquiv := _root_.Equiv.sumCongr e₁.vertexEquiv e₂.vertexEquiv
  attach_comm := fun f => by
    cases f with
    | inl g =>
      have h := e₁.attach_comm g
      suffices key : ∀ (a : W₂.Vertex ⊕ α) (b : W₁.Vertex ⊕ α),
          a = b.map e₁.vertexEquiv id →
          a.map Sum.inl Sum.inl =
            (b.map Sum.inl Sum.inl).map
              (_root_.Equiv.sumCongr e₁.vertexEquiv e₂.vertexEquiv)
              id from
        key _ _ h
      intro a b hab
      subst hab
      rcases b with v | ℓ <;> rfl
    | inr g =>
      have h := e₂.attach_comm g
      suffices key : ∀ (a : V₂.Vertex ⊕ β) (b : V₁.Vertex ⊕ β),
          a = b.map e₂.vertexEquiv id →
          a.map Sum.inr Sum.inr =
            (b.map Sum.inr Sum.inr).map
              (_root_.Equiv.sumCongr e₁.vertexEquiv e₂.vertexEquiv)
              id from
        key _ _ h
      intro a b hab
      subst hab
      rcases b with v | ℓ <;> rfl
  pairing_comm := fun f => by
    cases f with
    | inl g =>
      change Sum.inl (e₁.flagEquiv (W₁.pairing g)) =
        Sum.inl (W₂.pairing (e₁.flagEquiv g))
      rw [e₁.pairing_comm]
    | inr g =>
      change Sum.inr (e₂.flagEquiv (V₁.pairing g)) =
        Sum.inr (V₂.pairing (e₂.flagEquiv g))
      rw [e₂.pairing_comm]
  circles_eq := by
    change W₁.circles + V₁.circles = W₂.circles + V₂.circles
    rw [e₁.circles_eq, e₂.circles_eq]

/-! ### Glue-pair congruence -/

section GluePairCongr

variable {i j : α} (e : Equiv W₁ W₂)

/-- The flag equivalence restricts to surviving flags. -/
def survivingFlagEquiv (e : Equiv W₁ W₂) (i j : α) :
    SurvivingFlag W₁ i j ≃ SurvivingFlag W₂ i j where
  toFun f := ⟨e.flagEquiv f.val, by
    refine ⟨fun h => f.prop.1 ?_, fun h => f.prop.2 ?_⟩
    · exact e.flagEquiv.injective (h.trans (e.boundaryFlag_comm i).symm)
    · exact e.flagEquiv.injective (h.trans (e.boundaryFlag_comm j).symm)⟩
  invFun f := ⟨e.flagEquiv.symm f.val, by
    refine ⟨fun h => f.prop.1 ?_, fun h => f.prop.2 ?_⟩
    · have h1 := congrArg e.flagEquiv h
      simp? at h1
      rw [e.boundaryFlag_comm i] at h1
      exact h1
    · have h1 := congrArg e.flagEquiv h
      simp? at h1
      rw [e.boundaryFlag_comm j] at h1
      exact h1⟩
  left_inv f := Subtype.ext (by simp)
  right_inv f := Subtype.ext (by simp)

/-- The glue case (closed vs open) is preserved by the equivalence. -/
theorem gluePair_case_preserved (e : Equiv W₁ W₂) (i j : α) :
    W₁.pairing (W₁.boundaryFlag i) = W₁.boundaryFlag j ↔
    W₂.pairing (W₂.boundaryFlag i) = W₂.boundaryFlag j := by
  constructor
  · intro h
    have h1 := e.pairing_comm (W₁.boundaryFlag i)
    rw [h, e.boundaryFlag_comm i, e.boundaryFlag_comm j] at h1
    exact h1.symm
  · intro h
    have h1 := e.pairing_comm (W₁.boundaryFlag i)
    rw [e.boundaryFlag_comm i, h, ← e.boundaryFlag_comm j] at h1
    exact e.flagEquiv.injective h1

/-- The surviving-flag equivalence commutes with `glueAttachOn`.  Both
scrutinees are variables, so each of the four cases reduces. -/
private theorem survivingFlagEquiv_glueAttachOn (e : Equiv W₁ W₂)
    (i j : α) (f : SurvivingFlag W₁ i j)
    (s₁ : W₁.Vertex ⊕ α) (h₁ : W₁.attach f.val = s₁)
    (s₂ : W₂.Vertex ⊕ α)
    (h₂ : W₂.attach (e.survivingFlagEquiv i j f).val = s₂) :
    glueAttachOn W₂ i j (e.survivingFlagEquiv i j f) s₂ h₂ =
      (glueAttachOn W₁ i j f s₁ h₁).map e.vertexEquiv id := by
  have hatt := e.attach_comm f.val
  change W₂.attach (e.flagEquiv f.val) = s₂ at h₂
  rw [h₁] at hatt
  rw [h₂] at hatt
  cases s₁ <;> cases s₂ <;> simp_all [glueAttachOn]

/-- The surviving-flag equivalence commutes with glueAttach. -/
private theorem survivingFlagEquiv_glueAttach (e : Equiv W₁ W₂)
    (i j : α) (f : SurvivingFlag W₁ i j) :
    glueAttach W₂ i j (e.survivingFlagEquiv i j f) =
    (glueAttach W₁ i j f).map e.vertexEquiv id :=
  e.survivingFlagEquiv_glueAttachOn i j f _ rfl _ rfl

/-- The closed case: the flag equivalence restricts to a
`gluePairClosed` congruence. -/
def gluePairClosedCongr
    (h₁ : W₁.pairing (W₁.boundaryFlag i) = W₁.boundaryFlag j)
    (h₂ : W₂.pairing (W₂.boundaryFlag i) = W₂.boundaryFlag j) :
    Equiv (W₁.gluePairClosed i j h₁) (W₂.gluePairClosed i j h₂) where
  flagEquiv := e.survivingFlagEquiv i j
  vertexEquiv := e.vertexEquiv
  attach_comm := fun f => e.survivingFlagEquiv_glueAttach i j f
  pairing_comm := fun f => by
    apply Subtype.ext
    change e.flagEquiv (W₁.pairing f.val) = W₂.pairing (e.flagEquiv f.val)
    exact e.pairing_comm f.val
  circles_eq := by
    change W₁.circles + 1 = W₂.circles + 1
    rw [e.circles_eq]

/-! #### Rewire commutation -/

/-- The `.val` of a `rewire` in the first branch (partner is `i`'s
boundary flag). -/
private theorem rewire_val_of_eq_left {W : Fragment α} {i j : α}
    {hopen : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag j}
    {f : SurvivingFlag W i j}
    (hfi : W.pairing f.val = W.boundaryFlag i) :
    (rewire hopen f).val = W.pairing (W.boundaryFlag j) := by
  unfold rewire; simp [dite_eq_left hfi]

/-- The `.val` of a `rewire` in the second branch (partner is `j`'s
boundary flag). -/
private theorem rewire_val_of_eq_right {W : Fragment α} {i j : α}
    {hopen : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag j}
    {f : SurvivingFlag W i j}
    (hfi : W.pairing f.val ≠ W.boundaryFlag i)
    (hfj : W.pairing f.val = W.boundaryFlag j) :
    (rewire hopen f).val = W.pairing (W.boundaryFlag i) := by
  unfold rewire; simp [dite_eq_right hfi, dite_eq_left hfj]

/-- The `.val` of a `rewire` in the third branch (partner is
neither boundary flag). -/
private theorem rewire_val_of_ne {W : Fragment α} {i j : α}
    {hopen : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag j}
    {f : SurvivingFlag W i j}
    (hfi : W.pairing f.val ≠ W.boundaryFlag i)
    (hfj : W.pairing f.val ≠ W.boundaryFlag j) :
    (rewire hopen f).val = W.pairing f.val := by
  unfold rewire; simp [dite_eq_right hfi, dite_eq_right hfj]

/-- The open case: the flag equivalence commutes with rewiring. -/
private theorem survivingFlagEquiv_rewire
    (hopen₁ : W₁.pairing (W₁.boundaryFlag i) ≠ W₁.boundaryFlag j)
    (hopen₂ : W₂.pairing (W₂.boundaryFlag i) ≠ W₂.boundaryFlag j)
    (f : SurvivingFlag W₁ i j) :
    e.survivingFlagEquiv i j (rewire hopen₁ f) =
    rewire hopen₂ (e.survivingFlagEquiv i j f) := by
  apply Subtype.ext
  set g := e.survivingFlagEquiv i j f
  have hgval : g.val = e.flagEquiv f.val := rfl
  -- ═══════ CASE: f's partner is the boundary flag of i ═══════
  by_cases hfi : W₁.pairing f.val = W₁.boundaryFlag i
  · have hfi₂ : W₂.pairing g.val = W₂.boundaryFlag i := by
      rw [hgval, ← e.pairing_comm, hfi, e.boundaryFlag_comm]
    change e.flagEquiv (rewire hopen₁ f).val = (rewire hopen₂ g).val
    rw [rewire_val_of_eq_left hfi, rewire_val_of_eq_left hfi₂]
    rw [e.pairing_comm, e.boundaryFlag_comm]
  -- ═══════ CASE: f's partner is the boundary flag of j ═══════
  · by_cases hfj : W₁.pairing f.val = W₁.boundaryFlag j
    · have hfi₂ : W₂.pairing g.val ≠ W₂.boundaryFlag i := by
        rw [hgval]; intro h
        apply hfi
        rw [← e.boundaryFlag_comm i, ← e.pairing_comm] at h
        exact e.flagEquiv.injective h
      have hfj₂ : W₂.pairing g.val = W₂.boundaryFlag j := by
        rw [hgval, ← e.pairing_comm, hfj, e.boundaryFlag_comm]
      change e.flagEquiv (rewire hopen₁ f).val = (rewire hopen₂ g).val
      rw [rewire_val_of_eq_right hfi hfj,
          rewire_val_of_eq_right hfi₂ hfj₂]
      rw [e.pairing_comm, e.boundaryFlag_comm]
    -- ═══════ CASE: f's partner is neither boundary flag ═══════
    · have hfi₂ : W₂.pairing g.val ≠ W₂.boundaryFlag i := by
        rw [hgval]; intro h
        apply hfi
        rw [← e.boundaryFlag_comm i, ← e.pairing_comm] at h
        exact e.flagEquiv.injective h
      have hfj₂ : W₂.pairing g.val ≠ W₂.boundaryFlag j := by
        rw [hgval]; intro h
        apply hfj
        rw [← e.boundaryFlag_comm j, ← e.pairing_comm] at h
        exact e.flagEquiv.injective h
      change e.flagEquiv (rewire hopen₁ f).val = (rewire hopen₂ g).val
      rw [rewire_val_of_ne hfi hfj, rewire_val_of_ne hfi₂ hfj₂,
          hgval, e.pairing_comm]

/-- The open case: the flag equivalence restricts to a
`gluePairOpen` congruence. -/
def gluePairOpenCongr
    (hopen₁ : W₁.pairing (W₁.boundaryFlag i) ≠ W₁.boundaryFlag j)
    (hopen₂ : W₂.pairing (W₂.boundaryFlag i) ≠ W₂.boundaryFlag j)
    (hij : i ≠ j) :
    Equiv (W₁.gluePairOpen i j hij hopen₁)
      (W₂.gluePairOpen i j hij hopen₂) where
  flagEquiv := e.survivingFlagEquiv i j
  vertexEquiv := e.vertexEquiv
  attach_comm := fun f => e.survivingFlagEquiv_glueAttach i j f
  pairing_comm := fun f =>
    e.survivingFlagEquiv_rewire hopen₁ hopen₂ f
  circles_eq := e.circles_eq

/-- Single-pair gluing commutes with fragment equivalence. -/
def gluePairCongr (hij : i ≠ j) :
    Equiv (W₁.gluePair i j hij) (W₂.gluePair i j hij) := by
  unfold gluePair
  split
  · rename_i h₁
    rw [dite_eq_left ((e.gluePair_case_preserved i j).mp h₁)]
    exact e.gluePairClosedCongr h₁
      ((e.gluePair_case_preserved i j).mp h₁)
  · rename_i h₁
    rw [dite_eq_right (mt (e.gluePair_case_preserved i j).mpr h₁)]
    exact e.gluePairOpenCongr h₁
      (mt (e.gluePair_case_preserved i j).mpr h₁) hij

end GluePairCongr

/-! ### Relabel algebra -/

/-- Helper: the identity map commutes with `Sum.map id (Equiv.refl α)`
composed with `Sum.map (Equiv.refl _) id`. -/
private theorem relabel_refl_attach_aux (W : Fragment α)
    (f : W.Flag) :
    W.attach f = ((W.attach f).map id (_root_.Equiv.refl α)).map
      (_root_.Equiv.refl _) id := by
  rcases W.attach f with v | ℓ <;> simp

/-- Relabelling by the identity is the identity on fragments,
up to equivalence. -/
def relabelRefl (W : Fragment α) :
    Equiv (W.relabel (_root_.Equiv.refl α)) W where
  flagEquiv := _root_.Equiv.refl _
  vertexEquiv := _root_.Equiv.refl _
  attach_comm f := relabel_refl_attach_aux W f
  pairing_comm := fun _ => rfl
  circles_eq := rfl

/-- Helper: double relabelling commutes with single transitive
relabelling, as a `Sum` equation. -/
private theorem relabel_trans_attach_aux (W : Fragment α)
    (e₁ : α ≃ β) {γ : Type} (e₂ : β ≃ γ) (f : W.Flag) :
    (W.attach f).map id (e₁.trans e₂) =
    (((W.attach f).map id e₁).map id e₂).map
      (_root_.Equiv.refl _) id := by
  rcases W.attach f with v | ℓ <;> simp

/-- Relabelling twice composes, up to equivalence. -/
def relabelTrans (W : Fragment α) (e₁ : α ≃ β) {γ : Type}
    (e₂ : β ≃ γ) :
    Equiv ((W.relabel e₁).relabel e₂) (W.relabel (e₁.trans e₂)) where
  flagEquiv := _root_.Equiv.refl _
  vertexEquiv := _root_.Equiv.refl _
  attach_comm f := relabel_trans_attach_aux W e₁ e₂ f
  pairing_comm := fun _ => rfl
  circles_eq := rfl

/-! ### Sanity checks -/

/-- The identity equivalence on the strand. -/
example : Equiv strand strand := refl strand

/-- Symmetry of an equivalence round-trips. -/
example (e : Equiv W₁ W₂) : Equiv W₂ W₁ := e.symm

end Equiv

end Fragment

end RS
