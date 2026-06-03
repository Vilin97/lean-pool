/-
Copyright (c) 2026 ruplet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ruplet
-/

-- import Mathlib.Algebra.Ring.Defs

import LeanPool.FormalizationOfBoundedArithmetic.DisplayedVariables
import LeanPool.FormalizationOfBoundedArithmetic.Complexity
import LeanPool.FormalizationOfBoundedArithmetic.IsEnum
import LeanPool.FormalizationOfBoundedArithmetic.IOPEN

/-!
# LeanPool.FormalizationOfBoundedArithmetic.IDelta0
-/

open FirstOrder Language BoundedFormula

/-- Models of open induction extended with induction for delta-zero formulas. -/
class IDelta0Model (num : Type*) extends IOPENModel num where
  delta0_induction {n1} {a} [IsEnum a]
    (phi : peano.BoundedFormula ((Vars1 n1) ⊕ a) 0) :
    phi.IsDelta0 -> (mkInductionSentence phi).Realize num

namespace IDelta0Model

universe u
variable {M : Type*} [idelta0 : IDelta0Model M]

-- Example 3.9 Theorems of IΔ0
open Formula BoundedFormula

open BASICModel IOPENModel

-- D1. x ≠ 0 → ∃ y ≤ x, x = y + 1  (Predecessor)
-- proof: induction on x
theorem pred_exists :
  ∀ {x : M}, x ≠ 0 → ∃ y ≤ x, x = y + 1 :=
by
  let ind1 : peano.Formula (Vars2 .y .x) := x =' (y + 1)
  let ind2 : peano.Formula (Vars1 .x) :=
    (Formula.iBdEx' x (display2 .y ind1).flip)
  let ind := idelta0.delta0_induction <| display1 <| (x ≠' 0) ⟹ ind2
  unfold ind2 ind1 at ind
  specialize ind (by
    rw [IsDelta0.display1]
    -- TODO: this lemma can't be in @[delta0_simps],
    -- as it creates a goal 'φ.IsOpen' - which might be not true!
    rw [IsDelta0.of_open.imp]
    · constructor
      · unfold Term.neq
        rw [IsDelta0.of_open.not]
        constructor; constructor; constructor
        constructor; constructor
      · constructor
        rw [IsDelta0.flip]
        rw [IsDelta0.display2]
        constructor; constructor; constructor
    · unfold Term.neq
      rw [IsOpen.not]
      constructor; constructor
  )
  simpInduction at ind
  apply ind ?base ?step <;> clear ind ind1 ind2
  · simp only [IsEmpty.forall_iff]
  · intro a hind h
    exists a
    constructor
    · exact B8
    · rfl

theorem ex_of_bdEx {a} [LE a] {t} {P : a -> Prop} : (∃ x ≤ t, P x) -> ∃ x, P x := by
  intro h
  obtain ⟨x, ⟨hx1, hx2⟩⟩ := h
  exists x

lemma zero_add :
  ∀ x : M, 0 + x = x :=
by
  intro x
  rw [idelta0.add_comm]
  exact B3 x

instance : AddZeroClass M where
  zero_add := zero_add
  add_zero := B3

open IOPENModel BASICModel

-- D2. ∃ z, (x + z = y ∨ y + z = x)
-- original proof: Induction on x. Base case: B2, O2. Induction step: B3, B4, D1
-- our proof is different
theorem add_diff_exists :
  ∀ x y : M, ∃ z, x + z = y ∨ y + z = x :=
by
  let ind1 : peano.Formula (Vars3 .z .x .y) :=
    ((x + z) =' y) ⊔ ((y + z) =' x)
  let ind2 : peano.Formula (Vars2 .x .y) := iBdEx' (x + y) (display3 .z ind1).flip
  let ind3 : peano.Formula (Vars1 .x ⊕ Vars1 .y) := display2 .x ind2
  let ind := idelta0.delta0_induction ind3
  unfold ind3 ind2 ind1 at ind
  specialize ind (by
    rw [IsDelta0.display2]
    constructor
    rw [IsDelta0.flip]
    rw [IsDelta0.display3]
    constructor
    · constructor
      · constructor; constructor; constructor
      · constructor; constructor
    · constructor; constructor; constructor
  )
  simpInduction at ind
  intro x y
  apply ex_of_bdEx
  apply ind ?base ?step <;> clear ind1 ind2 ind3 ind
  · intro z
    exists z
    constructor
    · calc
        z ≤ z := le_refl z
        _ = 0 + z := (zero_add z).symm
    · rw [idelta0.add_comm]
      left
      change z + 0 = z
      exact B3 z
  · intro L hind R
    by_cases h_R_zero : R = 0
    · exists (L + 1)
      constructor
      · exact B8
      · right
        rw [h_R_zero]
        change 0 + (L + 1) = L + 1
        exact zero_add (L + 1)
    · obtain ⟨pred_R, h_pred_R_le, h_pred_R_eq⟩ := pred_exists h_R_zero
      specialize hind pred_R
      obtain ⟨symdiff_pred, h_symdiff_pred_le, h_symdiff_pred_eq⟩ := hind
      change symdiff_pred ≤ L + pred_R at h_symdiff_pred_le
      exists symdiff_pred
      cases h_symdiff_pred_eq with
      | inl h_LR =>
        change L + symdiff_pred = pred_R at h_LR
        constructor
        · change symdiff_pred ≤ (L + 1) + R
          rw [h_pred_R_eq, <- h_LR]
          conv =>
            rhs;
            rw [idelta0.add_comm]
            rw [idelta0.add_assoc]
            lhs
            rw [idelta0.add_comm]
          rw [idelta0.add_assoc]
          apply B8
        · left
          change (L + 1) + symdiff_pred = R
          rw [h_pred_R_eq]
          rw [idelta0.add_assoc]
          conv => lhs; rhs; rw [idelta0.add_comm]
          rw [<- idelta0.add_assoc]
          congr
      | inr h_RL =>
        change pred_R + symdiff_pred = L at h_RL
        constructor
        · change symdiff_pred ≤ (L + 1) + R
          rw [<- h_RL]
          conv => rhs; left; left; rw [idelta0.add_comm]
          conv =>
            rhs
            left
            rw [idelta0.add_comm]
            rw [<- idelta0.add_assoc]
            left
            rw [idelta0.add_comm]
          conv => rhs; rw [idelta0.add_assoc]; rw [idelta0.add_assoc]
          apply B8
        · right
          change R + symdiff_pred = L + 1
          rw [<- h_RL]
          rw [h_pred_R_eq]
          conv => lhs; rw [idelta0.add_assoc]; rhs; rw [idelta0.add_comm]
          rw [idelta0.add_assoc]

-- D3. x ≤ y ↔ ∃ z, x + z = y
theorem le_iff_exists_add :
  ∀ x y : M, x ≤ y ↔ ∃ z, x + z = y :=
by
  intro x y
  constructor
  · intro h_xy
    obtain ⟨diff, hdiff⟩ := add_diff_exists x y
    cases hdiff with
    | inl heq => exists diff
    | inr heq =>
      exists 0
      calc
        x + 0 = x := B3 x
        _ = y := by
          apply B7
          · exact h_xy
          · exact heq ▸ B8
  · intro h
    obtain ⟨z, hz⟩ := h
    rw [<- hz]
    apply B8

-- D4. (x ≤ y ∧ y ≤ z) → x ≤ z  (Transitivity)
theorem le_trans :
  ∀ {x y z : M}, x ≤ y -> y ≤ z -> x ≤ z :=
by
  intro x y z hxy hyz
  rw [le_iff_exists_add] at hxy hyz ⊢
  obtain ⟨diff_x_y, hdiff_x_y⟩ := hxy
  obtain ⟨diff_y_z, hdiff_y_z⟩ := hyz
  exists (diff_x_y + diff_y_z)
  rw [<- idelta0.add_assoc]
  rw [hdiff_x_y]
  rw [hdiff_y_z]


instance : Preorder M where
  le_refl := by apply @BASICModel.le_refl
  le_trans := by apply le_trans
  lt_iff_le_not_ge := by
    intro a b
    constructor
    · intro h
      constructor
      · exact h.1
      · intro contr
        apply h.2
        exact contr
    · intro h
      exact h


-- D5. x ≤ y ∨ y ≤ x  (Total order)
theorem le_total :
  ∀ x y : M, x ≤ y ∨ y ≤ x :=
by
  intro x y
  obtain ⟨diff, hdiff⟩ := add_diff_exists x y
  cases hdiff with
  | inl h =>
    left
    rw [le_iff_exists_add]
    exists diff
  | inr h =>
    right
    rw [le_iff_exists_add]
    exists diff

theorem add_rotate
  : ∀ {a b c : M}, a + b + c = b + c + a :=
by
  intro a b c
  rw [idelta0.add_assoc]
  rw [idelta0.add_comm]

-- D6. x ≤ y ↔ x + z ≤ y + z
theorem add_le_add_right :
  ∀ {x y z : M}, x ≤ y ↔ x + z ≤ y + z :=
by
  intro x y z
  constructor
  · intro hxy
    rw [le_iff_exists_add] at hxy ⊢
    obtain ⟨diff, hdiff⟩ := hxy
    exists diff
    rw [<- add_rotate]
    rw [idelta0.add_comm] at ⊢ hdiff
    rw [hdiff]
    rw [idelta0.add_comm]
  · rw [le_iff_exists_add]
    rw [le_iff_exists_add]
    intro h
    obtain ⟨a, ha⟩ := h
    exists a
    apply add_cancel_right.mp
    conv at ha => rw [idelta0.add_assoc]; lhs; rhs; rw [idelta0.add_comm]
    rw [idelta0.add_assoc]
    exact ha

theorem le_cancel_left :
  ∀ {x y z : M}, x <= y -> z + x <= z + y :=
by
  conv =>
    rhs
    rhs
    rhs
    rhs
    rw [idelta0.add_comm]
    rhs
    rw [idelta0.add_comm]
  intro x y z h
  apply add_le_add_right.mp h

-- D7. x ≤ y → x * z ≤ y * z
theorem le_mul_right :
  ∀ {x y z : M}, x ≤ y → x * z ≤ y * z :=
by
  intro x y z hxy
  rw [le_iff_exists_add] at hxy ⊢
  obtain ⟨diff, hdiff⟩ := hxy
  rw [<- hdiff]
  rw [idelta0.add_mul]
  exists (diff * z)

-- D8. x ≤ y + 1 ↔ (x ≤ y ∨ x = y + 1)  (Discreteness 1)
theorem le_succ_iff :
  ∀ {x y : M}, x ≤ y + 1 ↔ (x ≤ y ∨ x = y + 1) :=
by
  intro x y
  constructor
  · intro hxy
    rw [le_iff_exists_add] at hxy
    obtain ⟨diff, hdiff⟩ := hxy
    by_cases h : diff = 0
    · rw [h] at hdiff
      right
      exact (B3 x).symm.trans hdiff
    · obtain ⟨pred_diff, hpred_diff_le, hpred_diff_eq⟩
        := pred_exists h
      left
      rw [hpred_diff_eq] at hdiff
      rw [<- idelta0.add_assoc] at hdiff
      rw [le_iff_exists_add]
      exists pred_diff
      apply B2
      exact hdiff
  · intro h
    cases h with
    | inl h =>
      rw [le_iff_exists_add] at h ⊢
      rcases h with ⟨diff, hdiff⟩
      refine ⟨diff + 1, ?_⟩
      rw [<- idelta0.add_assoc]
      rw [hdiff]
    | inr h =>
      rw [h]

-- D4 used
instance : PartialOrder M where
  le_refl := idelta0.le_refl
  le_trans := @idelta0.le_trans
  le_antisymm := by apply B7

instance : CanonicallyOrderedAdd M where
  exists_add_of_le := by
    intro a b hab
    have diff := idelta0.add_diff_exists a b
    obtain ⟨diff, hdiff⟩ := diff
    cases hdiff with
    | inl h => rw [<- h]; exists diff
    | inr h =>
      exists 0
      calc
        b = a := by
          apply B7
          · exact h ▸ B8
          · exact hab
        _ = a + 0 := (B3 a).symm
  le_self_add := by apply B8
  le_add_self := by
    intro a b
    rw [idelta0.add_comm]
    apply B8

noncomputable instance : LinearOrder M where
  le_refl := idelta0.le_refl
  le_trans := by apply le_trans
  le_antisymm := by apply B7
  le_total := idelta0.le_total
  min_def := by simp only [implies_true]
  max_def := by exact fun a b ↦ rfl
  compare_eq_compareOfLessAndEq := by
    simp only [implies_true]

  toDecidableLE := by
    unfold DecidableLE DecidableRel
    intro a b
    if ha : a = 0 then
      apply Decidable.isTrue
      rw [ha]
      apply IOPENModel.zero_le b
    else
      if hb : b = 0 then
        apply Decidable.isFalse
        rw [hb]
        intro ha'
        apply ha
        exact (@nonpos_iff_eq_zero M).mp ha'
      else
        -- HERE, WE SHOULD TAKE PREDECESSOR OF
        -- BOTH AND RECURSE!
        exact Classical.propDecidable (a ≤ b)

theorem le_of_eq :
  ∀ {x y : M}, x = y -> x ≤ y :=
by
  intro x y hxy
  rw [hxy]

-- theorem lt_of_not_ge :
--   ∀ {x y : M}, ¬ x <= y -> y < x :=
-- by
--   intro x y h
--   constructor
--   · cases le_total x y with
--     | inl x_le =>
--       contradiction
--     | inr y_le =>
--       exact y_le
--   · intro h_eq
--     apply h
--     apply le_of_eq
--     apply Eq.symm
--     exact h_eq

theorem zero_if_sum_zero :
  ∀ {x y : M}, x + y = 0 -> x = 0 ∧ y = 0 :=
by
  intro x y h
  constructor
  · apply le_zero_eq
    have t := @B8 _ _ x y
    rw [h] at t
    exact t
  · apply le_zero_eq
    have t := @B8 _ _ y x
    rw [idelta0.add_comm] at t
    rw [h] at t
    exact t

theorem lt_one_eq_zero :
  ∀ {x : M}, x < 1 -> x = 0 :=
by
  intro x hx
  rcases hx with ⟨h_x_le, h_x_neq⟩
  rw [le_iff_exists_add] at h_x_le
  rcases h_x_le with ⟨diff, hdiff⟩
  by_cases h : x = 0
  · trivial
  · obtain ⟨pred, hp1, hp2⟩ := pred_exists h
    rw [hp2] at hdiff
    rw [idelta0.add_assoc] at hdiff
    conv at hdiff => lhs; rhs; rw [idelta0.add_comm]
    rw [<- idelta0.add_assoc] at hdiff
    conv at hdiff => rhs; rw [<- idelta0.zero_add 1]
    have hdiff := B2 _ _ hdiff
    have pred_zero := (zero_if_sum_zero hdiff).left
    rw [pred_zero, idelta0.zero_add] at hp2
    exfalso
    apply h_x_neq
    rw [hp2]

-- D9. x < y ↔ x + 1 ≤ y  (Discreteness 2)
-- recall: x < y means x ≤ y ∧ x ≠ y
theorem lt_iff_succ_le :
  ∀ {x y : M}, (x < y) ↔ x + 1 ≤ y :=
by
  intro x y
  constructor
  · intro h
    rcases h with ⟨h1, h2⟩
    rw [le_iff_exists_add] at h1
    obtain ⟨diff, hdiff⟩ := h1
    rw [<- hdiff]
    apply le_cancel_left
    by_contra not_one_le_diff
    apply h2
    rw [<- hdiff]
    conv => lhs; rw [<- B3 x]
    have diff_lt_one := lt_of_not_ge not_one_le_diff
    rw [lt_one_eq_zero diff_lt_one]
    rw [@B3]
    exact (B3 x).symm ▸ BASICModel.le_refl x
  · intro h
    rw [le_iff_exists_add] at h
    rcases h with ⟨diff, hdiff⟩
    constructor
    · rw [le_iff_exists_add]
      exists (1 + diff)
      rw [<- idelta0.add_assoc]
      exact hdiff
    · intro absurd
      rw [<- hdiff] at absurd
      have aux : x + 1 + diff = x := by
        have aux : x ≤ x + 1 + diff := by
          refine le_add_of_le_left ?_
          exact le_self_add
        apply le_antisymm <;> assumption
      conv at aux => lhs; rw [idelta0.add_assoc]
      conv at aux => rhs; rw [<- B3 x]
      rw [add_cancel_left] at aux
      rw [idelta0.add_comm] at aux
      exact (B1 (x := diff)) aux

theorem mul_eq_zero_iff_left :
  ∀ {x y : M}, x ≠ 0 -> (x * y = 0 ↔ y = 0) :=
by
  intro x y hx
  constructor
  · intro hxy
    rcases pred_exists hx with ⟨xp, _, hxp_eq⟩
    rw [hxp_eq] at hxy
    rw [idelta0.add_mul] at hxy
    by_contra hy
    rcases pred_exists hy with ⟨yp, _, hyp_eq⟩
    rw [hyp_eq] at hxy
    conv at hxy => lhs; rhs; rw [idelta0.mul_add]
    rw [idelta0.mul_one] at hxy
    rw [<- idelta0.add_assoc] at hxy
    apply B1 (num := M)
    exact hxy
  · intro hy
    rw [hy]
    apply B5

-- D10. x * z = y * z ∧ z ≠ 0 → x = y  (Cancellation law for ·)
theorem mul_cancel_right :
  ∀ x y z : M, (x * z = y * z ∧ z ≠ 0) → x = y :=
by
  let ind1 : peano.Formula (Vars3 .x .y .z)
    := ((x * z) =' (y * z) ⊓ (z ≠' 0)) ⟹ (x =' y)
  let ind := idelta0.delta0_induction <| display3 .x ind1
  specialize ind (by
    rw [IsDelta0.display3]
    unfold ind1
    constructor
    · apply IsDelta0.of_isQF
      apply IsQF.inf
      · constructor; constructor
      · apply IsQF.not; constructor; constructor
    · constructor; constructor; constructor
  )
  unfold ind1 at ind
  simpInduction at ind
  apply ind ?base ?step <;> clear ind ind1
  · intro y z hyz_z
    obtain ⟨hyz, hz⟩ := hyz_z
    by_cases hy : y = 0
    · exact hy.symm
    · rcases pred_exists hy with ⟨yp, _, hyp_eq⟩
      change 0 * z = y * z at hyz
      change z ≠ 0 at hz
      rcases pred_exists hz with ⟨zp, _, hzp_eq⟩
      rw [hyp_eq, hzp_eq] at hyz
      exfalso
      have hyz_zero : 0 = (yp + 1) * (zp + 1) := by
        exact (zero_mul (zp + 1)).symm.trans hyz
      have rhs_succ :
          (yp + 1) * (zp + 1) = ((yp + 1) * zp + yp) + 1 := by
        calc
          (yp + 1) * (zp + 1) = (yp + 1) * zp + (yp + 1) := B6
          _ = ((yp + 1) * zp + yp) + 1 := B4
      exact (B1 (x := (yp + 1) * zp + yp)) (rhs_succ.symm.trans hyz_zero.symm)
  · intro y hind x z hass_hz
    obtain ⟨hass, hz⟩ := hass_hz
    change (y + 1) * z = x * z at hass
    change z ≠ 0 at hz
    change ∀ x z : M, (y * z = x * z ∧ z ≠ 0) → y = x at hind
    -- hind tells us that we can right-cancel
    -- multiplication by `a_1` if the other factor at RHS is `a`

    -- right-cancel multiplication by `z` in `hass`
    have hx : x ≠ 0 := by
      by_contra hx
      rw [hx] at hass
      rw [idelta0.zero_mul] at hass
      rw [mul_eq_zero_iff_left] at hass
      · apply hz
        exact hass
      · apply @B1 M
    rcases pred_exists hx with ⟨xp, _, hxp_eq⟩
    rw [hxp_eq] at hass
    rw [idelta0.add_mul] at hass
    rw [idelta0.add_mul] at hass
    have hass_cancel : y * z = xp * z := by
      apply add_cancel_right.mp
      calc
        y * z + z = y * z + 1 * z := by rw [one_mul z]
        _ = xp * z + 1 * z := hass
        _ = xp * z + z := by rw [one_mul z]
    change y + 1 = x
    rw [hxp_eq]
    rw [hind xp z ⟨hass_cancel, hz⟩]


end IDelta0Model
