/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Coordinates.CircuitCount

/-!
# The orbit count is the number of orbits

`orbitCount` is defined as the number of cycles plus the number of
fixed points, which is convenient for computing signs but says
nothing directly about orbits.  This file identifies it with the
cardinality of the quotient by "lies on the same cycle": an orbit is
either the support of one of the permutation's cycles or a single
fixed point, and those two possibilities are exclusive and
exhaustive.

That identification is what lets two orbit counts be compared when
their underlying sets are different — a walk on flags against a
rotation on labels, say — since a bijection of quotients is then
enough.
-/

namespace RS

open Equiv Equiv.Perm

variable {β : Type}

/-- **The orbits of a permutation**, as a quotient of its ground
set. -/
abbrev Orbits (π : Perm β) : Type := Quotient (SameCycle.setoid π)

/-- The orbit space of a permutation of a finite type is finite. -/
instance [Fintype β] (π : Perm β) : Finite (Orbits π) := Quotient.finite _

/-- Hence it carries a fintype structure. -/
noncomputable instance [Fintype β] (π : Perm β) : Fintype (Orbits π) :=
  Fintype.ofFinite _

/-- And orbits can be compared, classically. -/
noncomputable instance (π : Perm β) : DecidableEq (Orbits π) :=
  Classical.decEq _

/-- Two points give the same orbit exactly when they lie on a common
cycle. -/
theorem orbit_eq_iff {π : Perm β} {x y : β} :
    (Quotient.mk (SameCycle.setoid π) x
      = Quotient.mk (SameCycle.setoid π) y) ↔ π.SameCycle x y :=
  Quotient.eq

/-! ### A fixed point's orbit is a singleton -/

/-- Nothing else lies on a fixed point's cycle. -/
theorem eq_of_sameCycle_of_fixed {π : Perm β} {x y : β}
    (hx : π x = x) (h : π.SameCycle x y) : y = x := by
  obtain ⟨i, hi⟩ := h
  rw [← hi, zpow_apply_eq_self_of_apply_eq_self hx i]

/-- A point on the same cycle as a moved point is moved. -/
theorem apply_ne_of_sameCycle {π : Perm β} {x y : β}
    (hx : π x ≠ x) (h : π.SameCycle x y) : π y ≠ y := by
  intro hy
  exact hx (eq_of_sameCycle_of_fixed hy h.symm ▸ hy)

/-! ### The orbit map -/

/-- The orbit of a point, named by its cycle when the point moves
and by the point itself when it does not. -/
noncomputable def orbitName [Fintype β] [DecidableEq β] (π : Perm β)
    (x : β) :
    π.cycleFactorsFinset ⊕ (Function.fixedPoints π) :=
  if h : π x = x then Sum.inr ⟨x, h⟩
  else Sum.inl ⟨π.cycleOf x,
    cycleOf_mem_cycleFactorsFinset_iff.mpr (mem_support.mpr h)⟩

/-- Points on the same cycle get the same name, so the naming
descends to orbits. -/
theorem orbitName_congr [Fintype β] [DecidableEq β] {π : Perm β} {x y : β}
    (h : π.SameCycle x y) : orbitName π x = orbitName π y := by
  unfold orbitName
  by_cases hx : π x = x
  · rw [dif_pos hx, dif_pos (eq_of_sameCycle_of_fixed hx h ▸ hx)]
    exact congrArg Sum.inr
      (Subtype.ext (eq_of_sameCycle_of_fixed hx h).symm)
  · rw [dif_neg hx, dif_neg (apply_ne_of_sameCycle hx h)]
    exact congrArg Sum.inl (Subtype.ext h.cycleOf_eq)

/-- A chosen point on one of the permutation's cycles. -/
noncomputable def cycleRep [Fintype β] [DecidableEq β] {π : Perm β}
    (c : π.cycleFactorsFinset) : β :=
  ((mem_cycleFactorsFinset_iff.mp c.prop).1.nonempty_support).choose

/-- The chosen point of a cycle lies on it. -/
theorem cycleRep_mem [Fintype β] [DecidableEq β] {π : Perm β}
    (c : π.cycleFactorsFinset) :
    cycleRep c ∈ c.val.support :=
  ((mem_cycleFactorsFinset_iff.mp c.prop).1.nonempty_support).choose_spec

/-- **The orbits are the cycles together with the fixed points.** -/
noncomputable def orbitsEquiv [Fintype β] [DecidableEq β] (π : Perm β) :
    Orbits π ≃ π.cycleFactorsFinset ⊕ (Function.fixedPoints π) where
  toFun := Quotient.lift (orbitName π) (fun _ _ h => orbitName_congr h)
  invFun := fun
    | Sum.inl c => Quotient.mk (SameCycle.setoid π)
        (cycleRep c)
    | Sum.inr x => Quotient.mk (SameCycle.setoid π) x.val
  left_inv := by
    refine Quotient.ind (fun x => ?_)
    show (match orbitName π x with
      | Sum.inl c => Quotient.mk (SameCycle.setoid π) _
      | Sum.inr y => Quotient.mk (SameCycle.setoid π) y.val)
      = Quotient.mk (SameCycle.setoid π) x
    unfold orbitName
    by_cases hx : π x = x
    · rw [dif_pos hx]
    · rw [dif_neg hx]
      refine Quotient.sound ?_
      have hmem := cycleRep_mem
        (⟨π.cycleOf x, cycleOf_mem_cycleFactorsFinset_iff.mpr
          (mem_support.mpr hx)⟩ : π.cycleFactorsFinset)
      rw [mem_support_cycleOf_iff] at hmem
      exact hmem.1.symm
  right_inv := by
    rintro (⟨c, hc⟩ | ⟨x, hx⟩)
    · have hcyc : c.IsCycle := (mem_cycleFactorsFinset_iff.mp hc).1
      have hmem := cycleRep_mem (⟨c, hc⟩ : π.cycleFactorsFinset)
      set y := cycleRep (⟨c, hc⟩ : π.cycleFactorsFinset) with hy
      have hyc : π.cycleOf y = c :=
        (cycle_is_cycleOf hmem hc).symm
      have hyne : π y ≠ y := by
        have : y ∈ π.support := by
          rw [← cycleOf_mem_cycleFactorsFinset_iff, hyc]
          exact hc
        exact mem_support.mp this
      show orbitName π y = Sum.inl ⟨c, hc⟩
      unfold orbitName
      rw [dif_neg hyne]
      exact congrArg Sum.inl (Subtype.ext hyc)
    · have hx' : π x = x := hx
      show orbitName π x = Sum.inr ⟨x, hx⟩
      unfold orbitName
      rw [dif_pos hx']

/-- **The orbit count is the number of orbits.** -/
theorem orbitCount_eq_card_orbits [Fintype β] [DecidableEq β]
    (π : Perm β) :
    orbitCount π = Fintype.card (Orbits π) := by
  rw [Fintype.card_congr (orbitsEquiv π), Fintype.card_sum]
  unfold orbitCount
  congr 1
  · rw [Equiv.Perm.cycleType, Multiset.card_map]
    exact (Fintype.card_coe _).symm

/-! ### Transporting orbits along a step-wise map

A map that moves each point within a single orbit of the target
permutation carries orbits to orbits, whatever it does inside them.
This is how a contracted matching's rotation is compared with the
original's: one step of the contracted rotation is several steps of
the original.
-/

/-- A map whose one-step images stay in one orbit respects the orbit
relation. -/
theorem sameCycle_of_step {γ : Type} {π : Perm β} {ρ : Perm γ}
    (f : γ → β) (hstep : ∀ x, π.SameCycle (f x) (f (ρ x)))
    {x y : γ} (h : ρ.SameCycle x y) : π.SameCycle (f x) (f y) := by
  have hnat : ∀ (z : γ) (m : ℕ), π.SameCycle (f z) (f ((ρ ^ m) z)) := by
    intro z m
    induction m with
    | zero => exact Equiv.Perm.SameCycle.refl π (f z)
    | succ m ih =>
      refine ih.trans ?_
      have hs := hstep ((ρ ^ m) z)
      rwa [show ρ ((ρ ^ m) z) = (ρ ^ (m + 1)) z from by
        rw [pow_succ']; rfl] at hs
  obtain ⟨n, hn⟩ := h
  subst hn
  obtain ⟨m, hm | hm⟩ := Int.eq_nat_or_neg n
  · subst hm
    rw [zpow_natCast]
    exact hnat x m
  · subst hm
    have h1 := hnat ((ρ ^ (-(m : ℤ))) x) m
    rw [show (ρ ^ (m : ℕ)) ((ρ ^ (-(m : ℤ))) x) = x from by
      rw [← zpow_natCast, ← Equiv.Perm.mul_apply, ← zpow_add]
      simp] at h1
    exact h1.symm

/-! ### The orbits partition the ground set

Grouping the ground set by orbit is what lets a construction be
carried out one orbit at a time — gluing an interface component by
component, say, rather than label by label.
-/

/-- **The orbit count does not read the decidability instance.** -/
theorem orbitCount_congr_decEq [Fintype β] (d₁ d₂ : DecidableEq β)
    (π : Perm β) :
    @orbitCount β _ d₁ π = @orbitCount β _ d₂ π := by
  rw [@orbitCount_eq_card_orbits β _ d₁ π,
    @orbitCount_eq_card_orbits β _ d₂ π]

/-- **Orbit counts agree along a bijection of orbit sets.** -/
theorem orbitCount_eq_of_orbitsEquiv [Fintype β] [DecidableEq β]
    {γ : Type} [Fintype γ] [DecidableEq γ] {π : Perm β} {ρ : Perm γ}
    (e : Orbits π ≃ Orbits ρ) : orbitCount π = orbitCount ρ := by
  rw [orbitCount_eq_card_orbits, orbitCount_eq_card_orbits,
    Fintype.card_congr e]

end RS
