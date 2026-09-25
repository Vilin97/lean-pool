/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Skein.TransitionExists

/-!
# Circuit count decomposition via orientations

The orbit count of the walk permutation decomposes into the orbit
counts of its restrictions to out-flags and in-flags (invariant
predicates under the walk).  Pairing-conjugation shows these two
restrictions have the same orbit count, whence the circuit count
(half the total orbit count) equals the orbit count of the
out-restriction.
-/

@[expose] public section

namespace RS

open Equiv

/-! ### Orbit count of a permutation -/

section OrbitCount

variable {β : Type}

/-- The orbit count of a permutation: number of non-trivial cycles
plus number of fixed points. -/
noncomputable def orbitCount [Fintype β] [DecidableEq β]
    (π : Perm β) : ℕ :=
  π.cycleType.card + Fintype.card (Function.fixedPoints π)

/-- Decomposition of a permutation into ofSubtype parts for an
invariant predicate and its complement. -/
theorem perm_eq_ofSubtype_mul (π : Perm β) (p : β → Prop) [DecidablePred p]
    (hp : ∀ x, p (π x) ↔ p x) :
    π = Perm.ofSubtype (π.subtypePerm hp) *
        Perm.ofSubtype (π.subtypePerm (p := fun x => ¬p x) (fun x =>
          (hp x).not)) := by
  ext x
  simp only [Perm.mul_apply]
  by_cases hpx : p x
  · have h1 : (Perm.ofSubtype (π.subtypePerm (p := fun x => ¬p x)
        (fun x => (hp x).not))) x = x :=
      Perm.ofSubtype_apply_of_not_mem _ (not_not.mpr hpx)
    have h2 : (Perm.ofSubtype (π.subtypePerm hp)) x = π x :=
      Perm.ofSubtype_subtypePerm_of_mem hp hpx
    simp [h1, h2]
  · have h1 : (Perm.ofSubtype (π.subtypePerm (p := fun x => ¬p x)
        (fun x => (hp x).not))) x = π x :=
      Perm.ofSubtype_subtypePerm_of_mem (p := fun x => ¬p x) (fun x =>
        (hp x).not) hpx
    have h2 : (Perm.ofSubtype (π.subtypePerm hp)) (π x) = π x :=
      Perm.ofSubtype_subtypePerm_of_not_mem hp ((hp x).not.mpr hpx)
    simp [h1, h2]

/-- The ofSubtype lifts of the p-restriction and not-p-restriction
are disjoint. -/
theorem disjoint_ofSubtype_subtypePerm (π : Perm β) (p : β → Prop)
  [DecidablePred p]
    (hp : ∀ x, p (π x) ↔ p x) :
    Perm.Disjoint
      (Perm.ofSubtype (π.subtypePerm hp))
      (Perm.ofSubtype (π.subtypePerm (p := fun x => ¬p x) (fun x =>
        (hp x).not))) := by
  intro x
  by_cases hpx : p x
  · right
    exact Perm.ofSubtype_apply_of_not_mem _ (not_not.mpr hpx)
  · left
    exact Perm.ofSubtype_subtypePerm_of_not_mem hp hpx

/-- The orbit count of a permutation splits additively over an
invariant predicate. -/
theorem orbitCount_eq_add [Fintype β] [DecidableEq β]
    (π : Perm β) (p : β → Prop) [DecidablePred p]
    (hp : ∀ x, p (π x) ↔ p x) :
    orbitCount π = orbitCount (π.subtypePerm hp) +
      orbitCount (π.subtypePerm (p := fun x => ¬p x) (fun x =>
        (hp x).not)) := by
  unfold orbitCount
  have hdecomp := perm_eq_ofSubtype_mul π p hp
  have hdisj := disjoint_ofSubtype_subtypePerm π p hp
  have hct : π.cycleType =
      (π.subtypePerm hp).cycleType +
      (π.subtypePerm (p := fun x => ¬p x) (fun x => (hp x).not)).cycleType := by
    conv_lhs => rw [hdecomp]
    rw [hdisj.cycleType_mul, Perm.cycleType_ofSubtype, Perm.cycleType_ofSubtype]
  rw [Perm.card_fixedPoints π, Perm.card_fixedPoints (π.subtypePerm hp),
      Perm.card_fixedPoints (π.subtypePerm (p := fun x => ¬p x) (fun x =>
        (hp x).not)),
      hct, Multiset.card_add, Multiset.sum_add]
  have hle_p := Perm.sum_cycleType_le (π.subtypePerm hp)
  have hle_np := Perm.sum_cycleType_le
    (π.subtypePerm (p := fun x => ¬p x) (fun x => (hp x).not))
  have h1 := Fintype.card_subtype_compl p
  have h2 := Fintype.card_subtype_le (fun x : β => p x)
  omega

/-- Orbit count is invariant under inversion. -/
theorem orbitCount_inv [Fintype β] [DecidableEq β]
    (π : Perm β) :
    orbitCount π⁻¹ = orbitCount π := by
  unfold orbitCount
  rw [Perm.cycleType_inv, Perm.card_fixedPoints π⁻¹,
      Perm.card_fixedPoints π, Perm.cycleType_inv]

/-- Orbit count is invariant under transport along an
equivalence. -/
theorem orbitCount_permCongr [Fintype β] [DecidableEq β]
    {γ : Type} [Fintype γ] [DecidableEq γ]
    (e : β ≃ γ) (π : Perm β) :
    orbitCount (e.permCongr π) = orbitCount π := by
  unfold orbitCount
  rw [cycleType_permCongr, card_fixedPoints_permCongr]

/-- `(-1)^(a - b) = (-1)^a * (-1)^b` when `b le a`, since
`(-1)^b` is its own inverse. -/
private theorem neg_one_pow_sub {a b : ℕ} (h : b ≤ a) :
    (-1 : ℂ) ^ (a - b) = (-1 : ℂ) ^ a * (-1 : ℂ) ^ b := by
  have h1 : (-1 : ℂ) ^ (a - b) * (-1) ^ b = (-1) ^ a := by
    rw [← pow_add]; congr 1; omega
  have h2 : (-1 : ℂ) ^ b * (-1) ^ b = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  calc (-1 : ℂ) ^ (a - b)
      = (-1) ^ (a - b) * ((-1) ^ b * (-1) ^ b) := by rw [h2, mul_one]
    _ = ((-1) ^ (a - b) * (-1) ^ b) * (-1) ^ b := by ring
    _ = (-1) ^ a * (-1) ^ b := by rw [h1]

/-- The sign identity: `(-1)^(orbitCount pi) = (-1)^(card beta) * sign pi`. -/
theorem neg_one_pow_orbitCount [Fintype β] [DecidableEq β]
    (π : Perm β) :
    (-1 : ℂ) ^ orbitCount π =
      (-1 : ℂ) ^ Fintype.card β * ((Perm.sign π : ℤ) : ℂ) := by
  have hsign : ((Perm.sign π : ℤ) : ℂ) =
      (-1 : ℂ) ^ (π.cycleType.sum + π.cycleType.card) := by
    have h := Perm.sign_of_cycleType π
    have hint : (Perm.sign π : ℤ) =
        (-1 : ℤ) ^ (π.cycleType.sum + π.cycleType.card) := by
      have := congr_arg Units.val h
      simp only [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one] at this
      exact this
    simp only [hint, Int.cast_pow, Int.cast_neg, Int.cast_one]
  unfold orbitCount
  rw [Perm.card_fixedPoints, pow_add,
      neg_one_pow_sub π.sum_cycleType_le, hsign, pow_add]
  ring

end OrbitCount

/-! ### Walk-orientation interaction -/

variable {α : Type} {W : Fragment α} {F : EdgeSubset W}

namespace EdgeSubset.TransitionSystem

/-- The walk preserves the orientation bit: pairing flips it once,
the matching flips it back. -/
theorem walk_isOut (κ : F.TransitionSystem) (o : κ.Orientation)
    (f : W.Flag) (hf : f ∈ F.flags) :
    o.isOut (κ.walk f) = o.isOut f := by
  unfold TransitionSystem.walk
  rw [o.match_flip (W.pairing f) (F.pairing_mem f hf),
      o.pairing_flip f hf, Bool.not_not]

/-- The walk permutation preserves the out-flag predicate. -/
theorem walkPerm_isOut_iff (κ : F.TransitionSystem) (o : κ.Orientation)
    (x : {f : W.Flag // f ∈ F.flags}) :
    (o.isOut (κ.walkPerm x).val = true) ↔ (o.isOut x.val = true) := by
  rw [κ.walkPerm_val, κ.walk_isOut o x.val x.prop]

/-- The out-flag restriction of the walk permutation. -/
noncomputable def outPerm (κ : F.TransitionSystem) (o : κ.Orientation) :
    Perm {f : {g : W.Flag // g ∈ F.flags} // o.isOut f.val = true} :=
  κ.walkPerm.subtypePerm (fun x => κ.walkPerm_isOut_iff o x)

/-! ### In/out orbit equivalence -/

/-- The pairing permutation maps out-flags to in-flags. -/
private theorem pairingPerm_isOut_flip (κ : F.TransitionSystem) (o :
  κ.Orientation)
    (a : {f : W.Flag // f ∈ F.flags}) :
    (o.isOut a.val = true) ↔ ¬(o.isOut (F.pairingPerm a).val = true) := by
  simp only [EdgeSubset.pairingPerm_val, o.pairing_flip a.val a.prop]
  cases o.isOut a.val <;> simp

/-- The equivalence between out-flags and in-flags induced by the
edge pairing. -/
noncomputable def outToIn (κ : F.TransitionSystem) (o : κ.Orientation) :
    {x : {g : W.Flag // g ∈ F.flags} // o.isOut x.val = true} ≃
    {x : {g : W.Flag // g ∈ F.flags} // ¬(o.isOut x.val = true)} :=
  F.pairingPerm.subtypeEquiv (fun a => κ.pairingPerm_isOut_flip o a)

/-- The reverse conjugation identity: sigma * walk^{-1} * sigma = walk. -/
private theorem conj_eq_walkPerm (κ : F.TransitionSystem) :
    F.pairingPerm * κ.walkPerm⁻¹ * F.pairingPerm = κ.walkPerm := by
  have h := κ.conj_zpow (-1)
  simp only [zpow_neg_one, neg_neg, zpow_one] at h
  exact h

/-- Key computation: sigma(walk^{-1}(sigma x)) = walk x. -/
private theorem pairing_walkInv_pairing (κ : F.TransitionSystem)
    (x : {f : W.Flag // f ∈ F.flags}) :
    F.pairingPerm (κ.walkPerm⁻¹ (F.pairingPerm x)) = κ.walkPerm x := by
  have h := congr_fun (congr_arg DFunLike.coe (κ.conj_eq_walkPerm)) x
  simpa [Perm.mul_apply] using h

/-- The in-restriction of the walk permutation equals the
outToIn-transport of the inverse out-restriction. -/
theorem inPerm_eq_permCongr_outPerm_inv (κ : F.TransitionSystem) (o :
  κ.Orientation) :
    κ.walkPerm.subtypePerm (p := fun x => ¬(o.isOut x.val = true))
      (fun x => (κ.walkPerm_isOut_iff o x).not) =
      (κ.outToIn o).permCongr (κ.outPerm o)⁻¹ := by
  apply Perm.ext
  intro ⟨y, hy⟩
  apply Subtype.ext
  -- After Subtype.ext, goal is definitionally:
  --   walkPerm y = pairingPerm (walkPerm^{-1} (pairingPerm^{-1} y))
  -- We convert to this form, rewrite pairingPerm^{-1} to pairingPerm, then use
  --   the key lemma
  change κ.walkPerm y = F.pairingPerm (κ.walkPerm⁻¹ (F.pairingPerm⁻¹ y))
  rw [EdgeSubset.pairingPerm_inv]
  exact (κ.pairing_walkInv_pairing y).symm

/-- The in-restriction and out-restriction of the walk permutation
have the same orbit count. -/
theorem orbitCount_inPerm_eq (κ : F.TransitionSystem) (o : κ.Orientation) :
    orbitCount (κ.walkPerm.subtypePerm (p := fun x => ¬(o.isOut x.val = true))
      (fun x => (κ.walkPerm_isOut_iff o x).not)) =
      orbitCount (κ.outPerm o) := by
  rw [κ.inPerm_eq_permCongr_outPerm_inv o, orbitCount_permCongr, orbitCount_inv]

/-! ### Main theorems -/

/-- The circuit count of a transition system equals the orbit count
of its out-flag restriction. -/
theorem circuitCount_eq_orbitCount_outPerm (κ : F.TransitionSystem)
    (o : κ.Orientation) :
    κ.circuitCount = orbitCount (κ.outPerm o) := by
  have hsplit := orbitCount_eq_add κ.walkPerm
    (fun x => o.isOut x.val = true) (fun x => κ.walkPerm_isOut_iff o x)
  have heq := κ.orbitCount_inPerm_eq o
  -- The out-part of the split is definitionally outPerm
  have hout : orbitCount (κ.walkPerm.subtypePerm
    (fun x => κ.walkPerm_isOut_iff o x)) = orbitCount (κ.outPerm o) := rfl
  have hdouble : orbitCount κ.walkPerm = 2 * orbitCount (κ.outPerm o) := by
    rw [hsplit, heq, hout]; ring
  unfold TransitionSystem.circuitCount orbitCount at hdouble ⊢
  omega

/-- The circuit sign decomposes as `(-1)^(card out-flags) * sign(outPerm)`. -/
theorem neg_one_pow_circuitCount (κ : F.TransitionSystem)
    (o : κ.Orientation) :
    ((-1 : ℂ) ^ κ.circuitCount) =
      (-1 : ℂ) ^ (Fintype.card
        {f : {g : W.Flag // g ∈ F.flags} // o.isOut f.val = true}) *
        ((Perm.sign (κ.outPerm o) : ℤ) : ℂ) := by
  rw [κ.circuitCount_eq_orbitCount_outPerm o, neg_one_pow_orbitCount]

end EdgeSubset.TransitionSystem

end RS
