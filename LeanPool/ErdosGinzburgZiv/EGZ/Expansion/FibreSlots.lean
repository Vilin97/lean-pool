/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/
module


public import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.Subweights

/-!
# Remaining multiset positions in each fibre

Deletion is performed on labelled positions, so coincident vectors retain
their separate multiplicities. The remaining fibres reconstruct exactly
the remaining natural-valued weight.
-/

@[expose] public section

open scoped BigOperators

namespace EGZ.Expansion.FibreSlots

variable {G H S : Type*} [Fintype G]

/-- A labelled copy of a group element, with one copy for each unit of its multiplicity. -/
abbrev Atom (w : G → ℕ) := Σ v, Fin (w v)

/-- The multiplicity function remaining after the selected atoms are removed. -/
noncomputable def remaining (w : G → ℕ) (U : Finset (Atom w)) : G → ℕ := by
  classical
  exact pushWeight Sigma.fst (fun a : Atom w ↦ if a ∉ U then 1 else 0)

/-- The retained atoms whose group elements project to the specified fibre label. -/
abbrev Fibre (w : G → ℕ) (U : Finset (Atom w)) (π : G → H) (q : H) :=
  {a : Atom w // π a.1 = q ∧ a ∉ U}

noncomputable instance fibreFintype (w : G → ℕ) (U : Finset (Atom w))
    (π : G → H) (q : H) : Fintype (Fibre w U π q) := Fintype.ofFinite _

/-- The subtype of atoms that have not been removed. -/
abbrev Retained (w : G → ℕ) (U : Finset (Atom w)) := {a : Atom w // a ∉ U}

noncomputable instance retainedFintype (w : G → ℕ) (U : Finset (Atom w)) :
    Fintype (Retained w U) := Fintype.ofFinite _

theorem pushWeight_atoms (w : G → ℕ) :
    pushWeight Sigma.fst (fun _ : Atom w ↦ 1) = w := by
  classical
  funext v
  change (∑ a : Σ z, Fin (w z), if a.1 = v then 1 else 0) = w v
  rw [Fintype.sum_sigma]
  calc
    _ = ∑ z, if z = v then w z else 0 := by
      apply Finset.sum_congr rfl
      intro z _
      by_cases hz : z = v <;> simp [hz]
    _ = w v := by simp

theorem card_atoms (w : G → ℕ) : Fintype.card (Atom w) = natMass w := by
  simp [natMass, Fintype.card_sigma]

theorem remaining_le (w : G → ℕ) (U : Finset (Atom w)) : remaining w U ≤ w := by
  classical
  calc
    remaining w U ≤ pushWeight Sigma.fst (fun _ : Atom w ↦ 1) := by
      apply pushWeight_mono
      intro a
      dsimp
      split_ifs <;> omega
    _ = w := pushWeight_atoms w

theorem mass_remaining_add_card (w : G → ℕ) (U : Finset (Atom w)) :
    natMass (remaining w U) + U.card = natMass w := by
  classical
  rw [remaining, natMass_pushWeight, ← card_atoms w]
  have hnot : natMass (fun a : Atom w ↦ if a ∉ U then 1 else 0) =
      ((Finset.univ : Finset (Atom w)) \ U).card := by
    have hfilter : (Finset.univ.filter (fun a : Atom w ↦ a ∉ U)) = Finset.univ \ U := by
      ext a
      simp
    change (∑ a : Atom w, if a ∉ U then 1 else 0) = _
    rw [Finset.sum_boole, hfilter]
    simp
  rw [hnot, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ]
  exact Nat.sub_add_cancel (Finset.card_le_univ U)

theorem mass_loss (w : G → ℕ) (U : Finset (Atom w)) :
    natMass w - natMass (remaining w U) = U.card := by
  have h := mass_remaining_add_card w U
  omega

theorem card_fibre_eq (w : G → ℕ) (U : Finset (Atom w))
    (π : G → H) (q : H) :
    Fintype.card (Fibre w U π q) = pushWeight π (remaining w U) q := by
  classical
  rw [remaining, pushWeight_comp]
  change Fintype.card {a : Atom w // π a.1 = q ∧ a ∉ U} = _
  rw [Fintype.card_subtype]
  simp only [pushWeight, Function.comp_apply]
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hq : π a.1 = q <;> by_cases hU : a ∈ U <;> simp [hq, hU]

/-- The number of removed atoms lying over a specified fibre label. -/
noncomputable def removedInFibre (w : G → ℕ) (U : Finset (Atom w))
    (π : G → H) (q : H) : ℕ := by
  classical
  exact (U.filter (fun a ↦ π a.1 = q)).card

theorem card_fibre_eq_sub_removed (w : G → ℕ) (U : Finset (Atom w))
    (π : G → H) (q : H) :
    Fintype.card (Fibre w U π q) = pushWeight π w q - removedInFibre w U π q := by
  classical
  have hall : pushWeight π w q =
      (Finset.univ.filter (fun a : Atom w ↦ π a.1 = q)).card := by
    have h := congrFun (congrArg (pushWeight π) (pushWeight_atoms w)) q
    rw [pushWeight_comp] at h
    rw [← h]
    simp only [pushWeight, Function.comp_apply, Finset.sum_boole, Nat.cast_id]
  change Fintype.card {a : Atom w // π a.1 = q ∧ a ∉ U} = _
  rw [Fintype.card_subtype]
  have hfilter : (Finset.univ.filter (fun a : Atom w ↦ π a.1 = q ∧ a ∉ U)) =
      (Finset.univ.filter (fun a : Atom w ↦ π a.1 = q)) \ U := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
  have hinter : U ∩ Finset.univ.filter (fun a : Atom w ↦ π a.1 = q) =
      U.filter (fun a ↦ π a.1 = q) := by ext a; simp
  rw [hfilter, Finset.card_sdiff, hinter, ← hall]
  rfl

theorem card_fibre_lower (w : G → ℕ) (U : Finset (Atom w))
    (π : G → H) (q : H) :
    pushWeight π w q - U.card ≤ Fintype.card (Fibre w U π q) := by
  classical
  rw [card_fibre_eq_sub_removed]
  have h : removedInFibre w U π q ≤ U.card := Finset.card_filter_le _ _
  omega

theorem sum_retained [DecidableEq G] {M : Type*} [AddCommMonoid M]
    (w : G → ℕ) (U : Finset (Atom w)) (f : Atom w → M) :
    (∑ a : Retained w U, f a.val) = ∑ a, if a ∉ U then f a else 0 := by
  classical
  rw [← Finset.sum_filter]
  symm
  exact Finset.sum_subtype _ (by simp) f

/-- The equivalence reassembling disjoint labelled fibres into all retained atoms. -/
noncomputable def labelledEquiv
    (w : G → ℕ) (U : Finset (Atom w)) (π : G → H) (label : S → H)
    (hinj : Function.Injective label)
    (hcover : ∀ v, w v ≠ 0 → ∃ s, π v = label s) :
    (Σ s, Fibre w U π (label s)) ≃ Retained w U := by
  classical
  let f : (Σ s, Fibre w U π (label s)) → Retained w U :=
    fun z ↦ ⟨z.2.val, z.2.property.2⟩
  apply Equiv.ofBijective f
  constructor
  · rintro ⟨s, a, ha⟩ ⟨t, b, hb⟩ heq
    have hab : a = b := congrArg Subtype.val heq
    have hst : s = t := hinj (ha.1.symm.trans (by rw [hab]; exact hb.1))
    subst t
    have hsub : (⟨a, ha⟩ : Fibre w U π (label s)) = ⟨b, hb⟩ := Subtype.ext hab
    exact congrArg (Sigma.mk s) hsub
  · rintro ⟨a, haU⟩
    have haW : w a.1 ≠ 0 := by have h := a.2.isLt; omega
    obtain ⟨s, hs⟩ := hcover a.1 haW
    exact ⟨⟨s, ⟨a, hs, haU⟩⟩, rfl⟩

/-- Reassembling all surviving labelled fibres recovers exactly the
remaining multiplicities, without identifying coincident positions. -/
theorem reassemble_remaining [Fintype S]
    (w : G → ℕ) (U : Finset (Atom w)) (π : G → H) (label : S → H)
    (hinj : Function.Injective label)
    (hcover : ∀ v, w v ≠ 0 → ∃ s, π v = label s) :
    pushWeight (fun z : Σ s, Fibre w U π (label s) ↦ z.2.val.1) (fun _ ↦ 1) =
      remaining w U := by
  classical
  funext v
  let e := labelledEquiv w U π label hinj hcover
  calc
    _ = ∑ a : Retained w U, if a.val.1 = v then 1 else 0 := by
      exact e.sum_comp (fun a ↦ if a.val.1 = v then 1 else 0)
    _ = ∑ a : Atom w, if a ∉ U then (if a.1 = v then 1 else 0) else 0 :=
      sum_retained w U (fun a ↦ if a.1 = v then 1 else 0)
    _ = remaining w U v := by
      unfold remaining pushWeight
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : a ∈ U <;> by_cases hv : a.1 = v <;> simp [ha, hv]

theorem remaining_isThickRelative {p d r T : ℕ} [NeZero p]
    (w : FpCoord p d → ℕ) (U : Finset (Atom w))
    (π : FpCoord p d → FpCoord p r) {δ : ℝ}
    (hδ : 0 ≤ δ) (hmass : p ≤ natMass w)
    (hU : (U.card : ℝ) ≤ δ * p / 2)
    (hthick : IsThickRelative w π T δ) :
    IsThickRelative (remaining w U) π T (δ / 2) := by
  intro ξ hξ
  have hloss : (natMass w : ℝ) - natMass (remaining w U) ≤ (δ / 2) * p := by
    have hcast : (natMass (remaining w U) : ℝ) + U.card = natMass w := by
      exact_mod_cast mass_remaining_add_card w U
    nlinarith
  have h := (hthick ξ hξ).of_pruning (remaining_le w U) (ε := 1) (M := p)
    (by norm_num) (by positivity : 0 ≤ δ / 2)
    (by simpa using (show (p : ℝ) ≤ natMass w by exact_mod_cast hmass)) hloss
    (by simpa using (show 0 ≤ δ - δ / 2 by linarith))
  convert h using 1
  ring

end EGZ.Expansion.FibreSlots
