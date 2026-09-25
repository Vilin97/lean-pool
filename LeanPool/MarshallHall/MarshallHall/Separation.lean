/-
Copyright (c) 2026 Arthur F. Ramos, David Barros Hulak, Ruy J.G.B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/
module

public import LeanPool.MarshallHall.MarshallHall.FiniteCore
public import Mathlib.GroupTheory.Finiteness


/-! The finite state set used in the separation argument. -/

@[expose] public section

open Set Function

noncomputable section

namespace MarshallHall

universe u

variable {α : Type u}



/-- The finite-core points viewed as states in the subgroup's left-coset space. -/
def coreStateSet [DecidableEq α] (H : Subgroup (FreeGroup α))
    (S : Finset (FreeGroup α)) (g : FreeGroup α) :
    Set (LeftCosetQuotient H) :=
  (fun x : FreeGroup α => (Quotient.mk'' x : LeftCosetQuotient H)) ''
    (corePoints S g : Set (FreeGroup α))

theorem coreStateSet_finite [DecidableEq α]
    (H : Subgroup (FreeGroup α)) (S : Finset (FreeGroup α)) (g : FreeGroup α) :
    (coreStateSet H S g).Finite := by
  exact (Finset.finite_toSet (corePoints S g)).image _

theorem mem_coreStateSet [DecidableEq α]
    {H : Subgroup (FreeGroup α)} {S : Finset (FreeGroup α)} {g x : FreeGroup α}
    (hx : x ∈ corePoints S g) :
    (Quotient.mk'' x : LeftCosetQuotient H) ∈ coreStateSet H S g := by
  exact ⟨x, hx, rfl⟩

theorem one_mem_coreStateSet [DecidableEq α]
    (H : Subgroup (FreeGroup α)) (S : Finset (FreeGroup α)) (g : FreeGroup α) :
    (Quotient.mk'' (1 : FreeGroup α) : LeftCosetQuotient H) ∈ coreStateSet H S g := by
  apply mem_coreStateSet
  exact mem_corePoints_of_separating (one_mem_allActionStates g.toWord)

/-! A finite based permutation representation separates an element from a
finitely generated subgroup when the subgroup acts trivially on the chosen
base state but the element does not.  This is the explicit finite quotient
surface behind subgroup separability; the older existential finite-index
subgroup statement is derived from its basepoint stabilizer below. -/

/-- A finite permutation representation fixing the subgroup at a base state and moving that state
by `g`. -/
structure FinitePermutationSeparator
    (H : Subgroup (FreeGroup α)) (g : FreeGroup α) where
  /-- The finite state type of the separating permutation representation. -/
  State : Type u
  /-- The finite enumeration of the representation's states. -/
  [stateFintype : Fintype State]
  /-- The free-group action on states as a homomorphism into their permutation group. -/
  representation : FreeGroup α →* Equiv.Perm State
  /-- The state fixed by the subgroup and moved by the element being separated. -/
  base : State
  fixes_subgroup : ∀ h : H, representation (h : FreeGroup α) base = base
  separates : representation g base ≠ base

/-- A permutation representation agrees with left multiplication along every word staying in
its finite core, provided its generator permutations extend the corresponding partial actions. -/
theorem word_action_of_generator_extensions {α : Type*}
    (H : Subgroup (FreeGroup α)) (A : Set (LeftCosetQuotient H)) (base : A)
    (hbase : base.1 = Quotient.mk'' (1 : FreeGroup α))
    (genPerm : α → Equiv.Perm A) (rho : FreeGroup α →* Equiv.Perm A)
    (genPerm_apply : ∀ {a : α} {z : A}
      (hz : leftMulEquiv H (FreeGroup.of a) z.1 ∈ A),
      genPerm a z = ⟨leftMulEquiv H (FreeGroup.of a) z.1, hz⟩)
    (genPerm_inv_apply : ∀ {a : α} {z : A}
      (hz : leftMulEquiv H (FreeGroup.of a)⁻¹ z.1 ∈ A),
      (genPerm a).symm z = ⟨leftMulEquiv H (FreeGroup.of a)⁻¹ z.1, hz⟩)
    (rho_singleton : ∀ x : α × Bool, rho (FreeGroup.mk [x]) =
      if x.2 then genPerm x.1 else (genPerm x.1).symm) :
    ∀ w : List (α × Bool),
      (∀ u ∈ List.tails w, ∀ x ∈ actionStates u,
        (Quotient.mk'' x : LeftCosetQuotient H) ∈ A) →
      ((rho (FreeGroup.mk w)) base : A).1 =
        (Quotient.mk'' (wordValue w) : LeftCosetQuotient H) := by
  classical
  intro w
  induction w with
  | nil =>
      intro hcore
      change ((rho 1) base : A).1 = Quotient.mk'' 1
      rw [map_one]
      exact hbase
  | cons x w ih =>
      rcases x with ⟨a, b⟩
      cases b with
      | false =>
          intro hcore
          have htail : ∀ u ∈ List.tails w, ∀ x ∈ actionStates u,
              (Quotient.mk'' x : LeftCosetQuotient H) ∈ A := by
            intro u hu x hx
            apply hcore u (by
              simp only [List.tails, List.mem_cons]
              exact Or.inr hu) x hx
          have hi := ih htail
          have hwfinal :
              (Quotient.mk'' (wordValue w) : LeftCosetQuotient H) ∈ A := by
            exact hcore w (by simp [List.tails]) _ (wordValue_mem_actionStates w)
          have hi' : rho (FreeGroup.mk w) base =
              ⟨Quotient.mk'' (wordValue w), hwfinal⟩ := by
            apply Subtype.ext
            exact hi
          have hfinal :
              (Quotient.mk'' (wordValue ((a, false) :: w)) :
                LeftCosetQuotient H) ∈ A := by
            exact hcore ((a, false) :: w) (by simp [List.tails]) _
              (wordValue_mem_actionStates ((a, false) :: w))
          have htarget :
              leftMulEquiv H (FreeGroup.of a)⁻¹
                  (Quotient.mk'' (wordValue w) : LeftCosetQuotient H) ∈ A := by
            rw [leftMulEquiv_mk]
            simpa [wordValue, signedLetter] using hfinal
          calc
            ((rho (FreeGroup.mk ((a, false) :: w))) base : A).1 =
                ((rho (FreeGroup.mk [(a, false)]))
                  (rho (FreeGroup.mk w) base) : A).1 := by
              rw [show FreeGroup.mk ((a, false) :: w) =
                  FreeGroup.mk [(a, false)] * FreeGroup.mk w by
                rw [FreeGroup.mul_mk]
                rfl, rho.map_mul, Equiv.Perm.mul_apply]
            _ = ((genPerm a).symm
                  ⟨Quotient.mk'' (wordValue w), hwfinal⟩ : A).1 := by
              rw [hi', rho_singleton]
              rfl
            _ = (leftMulEquiv H (FreeGroup.of a)⁻¹
                  (Quotient.mk'' (wordValue w) : LeftCosetQuotient H)) := by
              rw [genPerm_inv_apply htarget]
            _ = (Quotient.mk'' (wordValue ((a, false) :: w)) :
                  LeftCosetQuotient H) := by
              rw [leftMulEquiv_mk]
              simp [wordValue, signedLetter]
      | true =>
          intro hcore
          have htail : ∀ u ∈ List.tails w, ∀ x ∈ actionStates u,
              (Quotient.mk'' x : LeftCosetQuotient H) ∈ A := by
            intro u hu x hx
            apply hcore u (by
              simp only [List.tails, List.mem_cons]
              exact Or.inr hu) x hx
          have hi := ih htail
          have hwfinal :
              (Quotient.mk'' (wordValue w) : LeftCosetQuotient H) ∈ A := by
            exact hcore w (by simp [List.tails]) _ (wordValue_mem_actionStates w)
          have hi' : rho (FreeGroup.mk w) base =
              ⟨Quotient.mk'' (wordValue w), hwfinal⟩ := by
            apply Subtype.ext
            exact hi
          have hfinal :
              (Quotient.mk'' (wordValue ((a, true) :: w)) :
                LeftCosetQuotient H) ∈ A := by
            exact hcore ((a, true) :: w) (by simp [List.tails]) _
              (wordValue_mem_actionStates ((a, true) :: w))
          have htarget :
              leftMulEquiv H (FreeGroup.of a)
                  (Quotient.mk'' (wordValue w) : LeftCosetQuotient H) ∈ A := by
            rw [leftMulEquiv_mk]
            simpa [wordValue, signedLetter] using hfinal
          calc
            ((rho (FreeGroup.mk ((a, true) :: w))) base : A).1 =
                ((rho (FreeGroup.mk [(a, true)]))
                  (rho (FreeGroup.mk w) base) : A).1 := by
              rw [show FreeGroup.mk ((a, true) :: w) =
                  FreeGroup.mk [(a, true)] * FreeGroup.mk w by
                rw [FreeGroup.mul_mk]
                rfl, rho.map_mul, Equiv.Perm.mul_apply]
            _ = (genPerm a
                  ⟨Quotient.mk'' (wordValue w), hwfinal⟩ : A).1 := by
              rw [hi', rho_singleton]
              rfl
            _ = (leftMulEquiv H (FreeGroup.of a)
                  (Quotient.mk'' (wordValue w) : LeftCosetQuotient H)) := by
              rw [genPerm_apply htarget]
            _ = (Quotient.mk'' (wordValue ((a, true) :: w)) :
                  LeftCosetQuotient H) := by
              rw [leftMulEquiv_mk]
              simp [wordValue, signedLetter]

theorem freeGroup_finite_permutation_separator_proved
    {α : Type*} (H : Subgroup (FreeGroup α))
    [Group.FG H]
    (g : FreeGroup α)
    (hg : g ∉ H) :
    Nonempty (FinitePermutationSeparator H g) := by
  classical
  let : DecidableEq α := Classical.decEq α
  obtain ⟨S, hS⟩ := (Group.fg_iff_subgroup_fg H).mp (inferInstance : Group.FG H)
  let A : Set (LeftCosetQuotient H) := coreStateSet H S g
  have hAfin : A.Finite := by
    exact coreStateSet_finite H S g
  let : Fintype A := hAfin.fintype
  let q0 : LeftCosetQuotient H := Quotient.mk'' (1 : FreeGroup α)
  have hq0 : q0 ∈ A := by
    exact one_mem_coreStateSet H S g
  let base : A := ⟨q0, hq0⟩
  let genPerm : α → Equiv.Perm A := fun a =>
    Equiv.extendSubtype (restrictedEquiv A (leftMulEquiv H (FreeGroup.of a)))
  let rho : FreeGroup α →* Equiv.Perm A := FreeGroup.lift genPerm
  let : MulAction (FreeGroup α) A := MulAction.compHom A rho
  have genPerm_apply {a : α} {z : A}
      (hz : leftMulEquiv H (FreeGroup.of a) z.1 ∈ A) :
      genPerm a z = ⟨leftMulEquiv H (FreeGroup.of a) z.1, hz⟩ := by
    apply Subtype.ext
    dsimp [genPerm]
    have h := Equiv.extendSubtype_apply_of_mem
      (restrictedEquiv A (leftMulEquiv H (FreeGroup.of a))) z hz
    simpa [restrictedEquiv] using congrArg Subtype.val h
  have genPerm_inv_apply {a : α} {z : A}
      (hz : leftMulEquiv H (FreeGroup.of a)⁻¹ z.1 ∈ A) :
      (genPerm a).symm z =
        ⟨leftMulEquiv H (FreeGroup.of a)⁻¹ z.1, hz⟩ := by
    let y : A := ⟨leftMulEquiv H (FreeGroup.of a)⁻¹ z.1, hz⟩
    have hy : leftMulEquiv H (FreeGroup.of a) y.1 ∈ A := by
      have he : leftMulEquiv H (FreeGroup.of a)
          (leftMulEquiv H (FreeGroup.of a)⁻¹ z.1) = z.1 := by
        exact (leftMulEquiv H (FreeGroup.of a)).apply_symm_apply z.1
      rw [show y.1 = leftMulEquiv H (FreeGroup.of a)⁻¹ z.1 by rfl, he]
      exact z.2
    have hforward : genPerm a y = z := by
      rw [genPerm_apply hy]
      exact Subtype.ext (by
        exact (leftMulEquiv H (FreeGroup.of a)).apply_symm_apply z.1)
    have hback := congrArg (genPerm a).symm hforward
    simpa [y] using hback.symm
  have rho_singleton (x : α × Bool) :
      rho (FreeGroup.mk [x]) =
        if x.2 then genPerm x.1 else (genPerm x.1).symm := by
    cases x with
    | mk a b =>
        cases b <;> simp [rho, FreeGroup.lift_mk, Equiv.Perm.inv_def]
  have word_action : ∀ (w : List (α × Bool)),
      (∀ u ∈ List.tails w, ∀ x ∈ actionStates u,
        (Quotient.mk'' x : LeftCosetQuotient H) ∈ A) →
      ((rho (FreeGroup.mk w)) base : A).1 =
        (Quotient.mk'' (wordValue w) : LeftCosetQuotient H) :=
    word_action_of_generator_extensions H A base rfl genPerm rho
      genPerm_apply genPerm_inv_apply rho_singleton
  let K : Subgroup (FreeGroup α) := MulAction.stabilizer (FreeGroup α) base
  have gen_mem : ∀ s ∈ S, s ∈ K := by
    intro s hs
    have hcore_s : ∀ u ∈ List.tails s.toWord, ∀ x ∈ actionStates u,
        (Quotient.mk'' x : LeftCosetQuotient H) ∈ A := by
      intro u hu x hx
      change (Quotient.mk'' x : LeftCosetQuotient H) ∈ coreStateSet H S g
      exact mem_coreStateSet (mem_corePoints_of_generator_suffix hs hu hx)
    have hs_action : ((rho s) base : A).1 =
        (Quotient.mk'' s : LeftCosetQuotient H) := by
      have h := word_action s.toWord hcore_s
      simpa [wordValue_eq_freeGroup_mk, FreeGroup.mk_toWord] using h
    have hsH : s ∈ H := by
      rw [← hS]
      exact Subgroup.subset_closure hs
    have hs_quotient : (Quotient.mk'' s : LeftCosetQuotient H) = q0 := by
      dsimp [q0]
      exact (leftCoset_mk_eq_one_iff H s).2 hsH
    apply (MulAction.mem_stabilizer_iff).2
    apply Subtype.ext
    change ((rho s) base : A).1 = q0
    rw [hs_action, hs_quotient]
  have hHK : H ≤ K := by
    rw [← hS]
    exact (Subgroup.closure_le K).2 gen_mem
  have hKindex : K.index ≠ 0 := by
    dsimp [K]
    rw [MulAction.index_stabilizer]
    exact Nat.ne_of_gt ((Set.ncard_pos (s := MulAction.orbit (FreeGroup α) base)).2
      (MulAction.nonempty_orbit base))
  have hcore_g : ∀ u ∈ List.tails g.toWord, ∀ x ∈ actionStates u,
      (Quotient.mk'' x : LeftCosetQuotient H) ∈ A := by
    intro u hu x hx
    change (Quotient.mk'' x : LeftCosetQuotient H) ∈ coreStateSet H S g
    exact mem_coreStateSet (mem_corePoints_of_separating_suffix hu hx)
  have hg_action : ((rho g) base : A).1 =
      (Quotient.mk'' g : LeftCosetQuotient H) := by
    have h := word_action g.toWord hcore_g
    simpa [wordValue_eq_freeGroup_mk, FreeGroup.mk_toWord] using h
  have hHfix : ∀ h : H, rho (h : FreeGroup α) base = base := by
    intro h
    have hmem : (h : FreeGroup α) ∈ K := hHK h.property
    have hfix := (MulAction.mem_stabilizer_iff.mp hmem)
    change rho (h : FreeGroup α) base = base at hfix
    exact hfix
  have hg_notfix : rho g base ≠ base := by
    intro hfix
    apply hg
    have hfix' : ((rho g) base : A).1 = q0 := by
      change (rho g) base = base at hfix
      exact congrArg Subtype.val hfix
    have hquot : (Quotient.mk'' g : LeftCosetQuotient H) = q0 :=
      hg_action.symm.trans hfix'
    have hquot' : (Quotient.mk'' g : LeftCosetQuotient H) =
        Quotient.mk'' (1 : FreeGroup α) := by
      simpa [q0] using hquot
    exact (leftCoset_mk_eq_one_iff H g).1 hquot'
  exact ⟨{
    State := A
    representation := rho
    base := base
    fixes_subgroup := hHfix
    separates := hg_notfix
  }⟩

/-! The original LERF statement is a direct corollary of the explicit
separator.  Its subgroup is the stabilizer of the displayed finite action's
base state, so the finite-index witness is still tied to the actual
permutation representation. -/

theorem freeGroup_subgroup_separable_proved
    {α : Type*} (H : Subgroup (FreeGroup α))
    [Group.FG H]
    (g : FreeGroup α)
    (hg : g ∉ H) :
    ∃ K : Subgroup (FreeGroup α),
      H ≤ K ∧ K.index ≠ 0 ∧ g ∉ K := by
  obtain ⟨s⟩ := freeGroup_finite_permutation_separator_proved H g hg
  let : Fintype s.State := s.stateFintype
  let : MulAction (FreeGroup α) s.State :=
    MulAction.compHom s.State s.representation
  let K : Subgroup (FreeGroup α) :=
    MulAction.stabilizer (FreeGroup α) s.base
  have hHK : H ≤ K := by
    intro h hmem
    apply (MulAction.mem_stabilizer_iff).2
    change s.representation (h : FreeGroup α) s.base = s.base
    exact s.fixes_subgroup ⟨h, hmem⟩
  have hKindex : K.index ≠ 0 := by
    dsimp [K]
    rw [MulAction.index_stabilizer]
    exact Nat.ne_of_gt ((Set.ncard_pos (s := MulAction.orbit
      (FreeGroup α) s.base)).2 (MulAction.nonempty_orbit s.base))
  refine ⟨K, hHK, hKindex, ?_⟩
  intro hgK
  have hfix := (MulAction.mem_stabilizer_iff.mp hgK)
  change s.representation g s.base = s.base at hfix
  exact s.separates hfix

end MarshallHall
