/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie and Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.PolygonCellRadial
import Mathlib.Topology.Instances.AddCircle.Real

/-!
# Weighted subdivisions of the circle

A positive list of integral weights determines the orientation-preserving piecewise-linear map
which sends the `i`th unit interval to an interval of length equal to the `i`th weight.  This file
packages that map as a homeomorphism of intervals and, after identifying endpoints, as a
homeomorphism of circles.  It is the geometric core of Gallier--Xu P1 edge subdivision.
-/

namespace LeanEval.Topology.ClassificationOfSurfaces

namespace WeightedCircle

/-- Piecewise-linear cumulative stretching by a list of integral weights. -/
noncomputable def stretch : List ℕ → ℝ → ℝ
  | [], _ => 0
  | w :: weights, x =>
      if x ≤ 1 then w * x else w + stretch weights (x - 1)

/-- The inverse piecewise-linear cumulative stretching. -/
noncomputable def unstretch : List ℕ → ℝ → ℝ
  | [], _ => 0
  | w :: weights, y =>
      if y ≤ w then y / w else 1 + unstretch weights (y - w)

/-- Every weight is strictly positive. -/
def Positive (weights : List ℕ) : Prop :=
  ∀ w ∈ weights, 0 < w

theorem Positive.head {w : ℕ} {weights : List ℕ}
    (h : Positive (w :: weights)) : 0 < w :=
  h w (by simp)

theorem Positive.tail {w : ℕ} {weights : List ℕ}
    (h : Positive (w :: weights)) : Positive weights := by
  intro v hv
  exact h v (by simp [hv])

theorem sum_take_lt_sum {weights : List ℕ} (h : Positive weights)
    (i : Fin weights.length) :
    (weights.take i).sum < weights.sum := by
  induction weights with
  | nil => exact Fin.elim0 i
  | cons w weights ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [List.length_cons, Fin.coe_ofNat_eq_mod, Nat.zero_mod, List.take_zero,
          List.sum_nil, List.sum_cons, add_pos_iff]
        exact Or.inl h.head
      · simpa [List.take_succ_cons] using Nat.add_lt_add_left (ih h.tail j) w

@[simp]
theorem stretch_nil (x : ℝ) : stretch [] x = 0 :=
  rfl

@[simp]
theorem unstretch_nil (y : ℝ) : unstretch [] y = 0 :=
  rfl

@[simp]
theorem stretch_zero (weights : List ℕ) : stretch weights 0 = 0 := by
  induction weights with
  | nil => rfl
  | cons w weights _ =>
      simp [stretch]

@[simp]
theorem unstretch_zero (weights : List ℕ) : unstretch weights 0 = 0 := by
  induction weights with
  | nil => rfl
  | cons w weights _ =>
      by_cases hw : w = 0
      · subst w
        simp [unstretch]
      · have hwpos : (0 : ℝ) < w := by exact_mod_cast Nat.pos_of_ne_zero hw
        simp [unstretch, hwpos.le]

@[simp]
theorem stretch_length (weights : List ℕ) :
    stretch weights weights.length = weights.sum := by
  induction weights with
  | nil => simp
  | cons w weights ih =>
      cases weights with
      | nil => simp [stretch]
      | cons v weights =>
          have hnot :
              ¬((↑((w :: v :: weights).length) : ℝ) ≤ 1) := by
            simp only [List.length_cons, Nat.cast_add, Nat.cast_one, add_le_iff_nonpos_left,
              not_le]
            positivity
          calc
            stretch (w :: v :: weights) (w :: v :: weights).length =
                (w : ℝ) +
                  stretch (v :: weights)
                    ((w :: v :: weights).length - 1) := by
              rw [stretch, if_neg hnot]
            _ = (w : ℝ) +
                  stretch (v :: weights) (v :: weights).length := by
              congr 2
              simp
            _ = (w : ℝ) + (v :: weights).sum := by rw [ih]
            _ = (w :: v :: weights).sum := by
              push_cast
              simp

theorem unstretch_sum (weights : List ℕ) (h : Positive weights) :
    unstretch weights weights.sum = weights.length := by
  induction weights with
  | nil => simp
  | cons w weights ih =>
      by_cases htail : weights = []
      · subst weights
        have hw := h.head
        simp [unstretch, hw.ne']
      · have hsumpos : 0 < weights.sum :=
          List.sum_pos weights h.tail htail
        have hnot : ¬((↑(w + weights.sum) : ℝ) ≤ w) := by
          intro hle
          have hlt : (w : ℝ) < (w + weights.sum : ℕ) := by
            exact_mod_cast Nat.lt_add_of_pos_right hsumpos
          linarith
        simp only [List.sum_cons, List.length_cons, unstretch, hnot, if_false]
        rw [show (↑(w + weights.sum) : ℝ) - w = weights.sum by
          push_cast
          ring]
        rw [ih h.tail]
        push_cast
        ring

/-- Stretching is continuous; adjacent affine pieces agree at every breakpoint. -/
theorem continuous_stretch (weights : List ℕ) :
    Continuous (stretch weights) := by
  induction weights with
  | nil => exact continuous_const
  | cons w weights ih =>
      change Continuous (fun x : ℝ =>
        if x ≤ 1 then (w : ℝ) * x
        else (w : ℝ) + stretch weights (x - 1))
      apply Continuous.if_le
        (continuous_const.mul continuous_id)
        (continuous_const.add (ih.comp (continuous_id.sub continuous_const)))
        continuous_id continuous_const
      intro x hx
      simp only [id_eq] at hx
      subst x
      simp

/-- Inverse stretching is continuous when every weight is positive. -/
theorem continuous_unstretch (weights : List ℕ) (h : Positive weights) :
    Continuous (unstretch weights) := by
  induction weights with
  | nil => exact continuous_const
  | cons w weights ih =>
      change Continuous (fun y : ℝ =>
        if y ≤ w then y / (w : ℝ)
        else 1 + unstretch weights (y - w))
      apply Continuous.if_le
        (continuous_id.div_const _)
        (continuous_const.add
          ((ih h.tail).comp (continuous_id.sub continuous_const)))
        continuous_id continuous_const
      intro y hy
      simp only [id_eq] at hy
      subst y
      have hw : (w : ℝ) ≠ 0 := by exact_mod_cast h.head.ne'
      change (w : ℝ) / w = 1 + unstretch weights ((w : ℝ) - w)
      rw [div_self hw, sub_self, unstretch_zero]
      norm_num

theorem stretch_nonneg {weights : List ℕ} (h : Positive weights)
    {x : ℝ} (hx0 : 0 ≤ x) (hxlen : x ≤ weights.length) :
    0 ≤ stretch weights x := by
  induction weights generalizing x with
  | nil => simp
  | cons w weights ih =>
      by_cases hx : x ≤ 1
      · rw [stretch, if_pos hx]
        exact mul_nonneg (by exact_mod_cast h.head.le) hx0
      · rw [stretch, if_neg hx]
        have hx0' : 0 ≤ x - 1 := by linarith
        have hxlen' : x - 1 ≤ weights.length := by
          rw [sub_le_iff_le_add]
          simpa only [List.length_cons, Nat.cast_add, Nat.cast_one] using hxlen
        exact add_nonneg (by positivity)
          (ih h.tail hx0' hxlen')

theorem stretch_le_sum {weights : List ℕ} (h : Positive weights)
    {x : ℝ} (hx0 : 0 ≤ x) (hxlen : x ≤ weights.length) :
    stretch weights x ≤ weights.sum := by
  induction weights generalizing x with
  | nil => simp
  | cons w weights ih =>
      by_cases hx : x ≤ 1
      · rw [stretch, if_pos hx]
        have hw0 : (0 : ℝ) ≤ w := by positivity
        have hmul : (w : ℝ) * x ≤ w := by nlinarith
        rw [List.sum_cons, Nat.cast_add]
        exact hmul.trans
          (le_add_of_nonneg_right (Nat.cast_nonneg _))
      · rw [stretch, if_neg hx]
        have hx0' : 0 ≤ x - 1 := by linarith
        have hxlen' : x - 1 ≤ weights.length := by
          rw [sub_le_iff_le_add]
          simpa only [List.length_cons, Nat.cast_add, Nat.cast_one] using hxlen
        have htail := ih h.tail hx0' hxlen'
        rw [List.sum_cons, Nat.cast_add]
        linarith

theorem stretch_pos {weights : List ℕ} (h : Positive weights)
    {x : ℝ} (hx0 : 0 < x) (hxlen : x ≤ weights.length) :
    0 < stretch weights x := by
  cases weights with
  | nil =>
      simp at hxlen
      linarith
  | cons w weights =>
      by_cases hx : x ≤ 1
      · rw [stretch, if_pos hx]
        exact mul_pos (by exact_mod_cast h.head) hx0
      · rw [stretch, if_neg hx]
        have hx0' : 0 ≤ x - 1 := by linarith
        have hxlen' : x - 1 ≤ weights.length := by
          rw [sub_le_iff_le_add]
          simpa only [List.length_cons, Nat.cast_add, Nat.cast_one] using hxlen
        have htail :=
          stretch_nonneg h.tail hx0' hxlen'
        have hw : (0 : ℝ) < w := by exact_mod_cast h.head
        linarith

theorem unstretch_nonneg {weights : List ℕ} (h : Positive weights)
    {y : ℝ} (hy0 : 0 ≤ y) (hysum : y ≤ weights.sum) :
    0 ≤ unstretch weights y := by
  induction weights generalizing y with
  | nil => simp
  | cons w weights ih =>
      by_cases hy : y ≤ w
      · rw [unstretch, if_pos hy]
        exact div_nonneg hy0 (by exact_mod_cast h.head.le)
      · rw [unstretch, if_neg hy]
        have hy0' : 0 ≤ y - w := by linarith
        have hysum' : y - w ≤ weights.sum := by
          rw [sub_le_iff_le_add]
          simpa only [List.sum_cons, Nat.cast_add, add_comm] using hysum
        exact add_nonneg (by norm_num) (ih h.tail hy0' hysum')

theorem unstretch_le_length {weights : List ℕ} (h : Positive weights)
    {y : ℝ} (hy0 : 0 ≤ y) (hysum : y ≤ weights.sum) :
    unstretch weights y ≤ weights.length := by
  induction weights generalizing y with
  | nil => simp
  | cons w weights ih =>
      by_cases hy : y ≤ w
      · rw [unstretch, if_pos hy]
        have hw : (0 : ℝ) < w := by exact_mod_cast h.head
        have hdiv : y / (w : ℝ) ≤ 1 := (div_le_one hw).2 hy
        rw [List.length_cons]
        push_cast
        exact hdiv.trans (by
          have : (0 : ℝ) ≤ weights.length := by positivity
          linarith)
      · rw [unstretch, if_neg hy]
        have hy0' : 0 ≤ y - w := by linarith
        have hysum' : y - w ≤ weights.sum := by
          rw [sub_le_iff_le_add]
          simpa only [List.sum_cons, Nat.cast_add, add_comm] using hysum
        have htail := ih h.tail hy0' hysum'
        rw [List.length_cons]
        push_cast
        linarith

theorem unstretch_pos {weights : List ℕ} (h : Positive weights)
    {y : ℝ} (hy0 : 0 < y) (hysum : y ≤ weights.sum) :
    0 < unstretch weights y := by
  cases weights with
  | nil =>
      simp at hysum
      linarith
  | cons w weights =>
      by_cases hy : y ≤ w
      · rw [unstretch, if_pos hy]
        exact div_pos hy0 (by exact_mod_cast h.head)
      · rw [unstretch, if_neg hy]
        have hy0' : 0 ≤ y - w := by linarith
        have hysum' : y - w ≤ weights.sum := by
          rw [sub_le_iff_le_add]
          simpa only [List.sum_cons, Nat.cast_add, add_comm] using hysum
        have htail :=
          unstretch_nonneg h.tail hy0' hysum'
        linarith

theorem unstretch_stretch {weights : List ℕ} (h : Positive weights)
    {x : ℝ} (hx0 : 0 ≤ x) (hxlen : x ≤ weights.length) :
    unstretch weights (stretch weights x) = x := by
  induction weights generalizing x with
  | nil =>
      simp at hxlen
      simp [show x = 0 by linarith]
  | cons w weights ih =>
      by_cases hx : x ≤ 1
      · rw [stretch, if_pos hx]
        have hw : (0 : ℝ) < w := by exact_mod_cast h.head
        have hselect : (w : ℝ) * x ≤ w := by nlinarith
        rw [unstretch, if_pos hselect]
        exact (div_eq_iff hw.ne').2 (by ring)
      · rw [stretch, if_neg hx]
        have hx0' : 0 < x - 1 := by linarith
        have hxlen' : x - 1 ≤ weights.length := by
          rw [sub_le_iff_le_add]
          simpa only [List.length_cons, Nat.cast_add, Nat.cast_one] using hxlen
        have hstretchPos : 0 < stretch weights (x - 1) :=
          stretch_pos h.tail hx0' hxlen'
        have hselect :
            ¬((w : ℝ) + stretch weights (x - 1) ≤ w) := by
          linarith
        rw [unstretch, if_neg hselect]
        have ih' := ih h.tail hx0'.le hxlen'
        rw [show (w : ℝ) + stretch weights (x - 1) - w =
          stretch weights (x - 1) by ring]
        rw [ih']
        ring

theorem stretch_unstretch {weights : List ℕ} (h : Positive weights)
    {y : ℝ} (hy0 : 0 ≤ y) (hysum : y ≤ weights.sum) :
    stretch weights (unstretch weights y) = y := by
  induction weights generalizing y with
  | nil =>
      simp at hysum
      simp [show y = 0 by linarith]
  | cons w weights ih =>
      by_cases hy : y ≤ w
      · rw [unstretch, if_pos hy]
        have hw : (0 : ℝ) < w := by exact_mod_cast h.head
        have hselect : y / (w : ℝ) ≤ 1 := (div_le_one hw).2 hy
        rw [stretch, if_pos hselect]
        exact (mul_div_cancel₀ y hw.ne')
      · rw [unstretch, if_neg hy]
        have hy0' : 0 < y - w := by linarith
        have hysum' : y - w ≤ weights.sum := by
          rw [sub_le_iff_le_add]
          simpa only [List.sum_cons, Nat.cast_add, add_comm] using hysum
        have hunstretchPos : 0 < unstretch weights (y - w) :=
          unstretch_pos h.tail hy0' hysum'
        have hselect :
            ¬(1 + unstretch weights (y - w) ≤ 1) := by
          linarith
        rw [stretch, if_neg hselect]
        have ih' := ih h.tail hy0'.le hysum'
        rw [show 1 + unstretch weights (y - w) - 1 =
          unstretch weights (y - w) by ring]
        rw [ih']
        ring

/-- Positive weights give a homeomorphism from the interval of positions to the interval of
expanded positions. -/
noncomputable def intervalHomeomorph (weights : List ℕ) (h : Positive weights) :
    Set.Icc (0 : ℝ) (0 + weights.length) ≃ₜ
      Set.Icc (0 : ℝ) (0 + weights.sum) where
  toFun x :=
    ⟨stretch weights x,
      stretch_nonneg h x.property.1 (by simpa using x.property.2),
      by
        simpa using
          stretch_le_sum h x.property.1 (by simpa using x.property.2)⟩
  invFun y :=
    ⟨unstretch weights y,
      unstretch_nonneg h y.property.1 (by simpa using y.property.2),
      by
        simpa using
          unstretch_le_length h y.property.1 (by simpa using y.property.2)⟩
  left_inv := by
    intro x
    apply Subtype.ext
    exact unstretch_stretch h x.property.1 (by simpa using x.property.2)
  right_inv := by
    intro y
    apply Subtype.ext
    exact stretch_unstretch h y.property.1 (by simpa using y.property.2)
  continuous_toFun := by
    apply continuous_induced_rng.2
    exact (continuous_stretch weights).comp continuous_subtype_val
  continuous_invFun := by
    apply continuous_induced_rng.2
    exact (continuous_unstretch weights h).comp continuous_subtype_val

@[simp]
theorem intervalHomeomorph_apply_val (weights : List ℕ) (h : Positive weights)
    (x : Set.Icc (0 : ℝ) (0 + weights.length)) :
    (intervalHomeomorph weights h x).val = stretch weights x :=
  rfl

@[simp]
theorem intervalHomeomorph_zero (weights : List ℕ) (h : Positive weights) :
    intervalHomeomorph weights h
        ⟨0, by simp⟩ =
      (⟨0, by constructor <;> positivity⟩ :
        Set.Icc (0 : ℝ) (0 + weights.sum)) := by
  apply Subtype.ext
  exact stretch_zero weights

theorem intervalHomeomorph_length (weights : List ℕ) (h : Positive weights) :
    intervalHomeomorph weights h
        ⟨0 + weights.length, by simp⟩ =
      (⟨0 + weights.sum, ⟨by positivity, le_rfl⟩⟩ :
        Set.Icc (0 : ℝ) (0 + weights.sum)) := by
  apply Subtype.ext
  rw [intervalHomeomorph_apply_val]
  simpa only [zero_add] using stretch_length weights

theorem intervalHomeomorph_endpointIdent_iff
    (weights : List ℕ) (h : Positive weights)
    [Fact (0 < (weights.length : ℝ))]
    [Fact (0 < (weights.sum : ℝ))]
    (x y : Set.Icc (0 : ℝ) (0 + weights.length)) :
    AddCircle.EndpointIdent (weights.length : ℝ) 0 x y ↔
      AddCircle.EndpointIdent (weights.sum : ℝ) 0
        (intervalHomeomorph weights h x)
        (intervalHomeomorph weights h y) := by
  constructor
  · intro hxy
    cases hxy
    rw [intervalHomeomorph_zero, intervalHomeomorph_length]
    exact AddCircle.EndpointIdent.mk
  · intro hxy
    generalize hximage :
      intervalHomeomorph weights h x = ximage at hxy
    generalize hyimage :
      intervalHomeomorph weights h y = yimage at hxy
    cases hxy
    have hx :
        x = (⟨0, by simp⟩ :
          Set.Icc (0 : ℝ) (0 + weights.length)) := by
      apply (intervalHomeomorph weights h).injective
      rw [hximage, intervalHomeomorph_zero]
    have hy :
        y = (⟨0 + weights.length, by simp⟩ :
          Set.Icc (0 : ℝ) (0 + weights.length)) := by
      apply (intervalHomeomorph weights h).injective
      rw [hyimage, intervalHomeomorph_length]
    subst x
    subst y
    exact AddCircle.EndpointIdent.mk

/-- The interval homeomorphism descends after identifying both pairs of endpoints. -/
noncomputable def endpointQuotHomeomorph
    (weights : List ℕ) (h : Positive weights)
    [Fact (0 < (weights.length : ℝ))]
    [Fact (0 < (weights.sum : ℝ))] :
    Quot (AddCircle.EndpointIdent (weights.length : ℝ) 0) ≃ₜ
      Quot (AddCircle.EndpointIdent (weights.sum : ℝ) 0) where
  toFun :=
    Quot.lift
      (fun x => Quot.mk _ (intervalHomeomorph weights h x))
      fun x y hxy =>
        Quot.sound ((intervalHomeomorph_endpointIdent_iff weights h x y).mp hxy)
  invFun :=
    Quot.lift
      (fun y => Quot.mk _ ((intervalHomeomorph weights h).symm y))
      fun x y hxy => by
        apply Quot.sound
        apply (intervalHomeomorph_endpointIdent_iff weights h _ _).mpr
        simpa only [Homeomorph.apply_symm_apply] using hxy
  left_inv := by
    intro q
    induction q using Quot.inductionOn
    simp
  right_inv := by
    intro q
    induction q using Quot.inductionOn
    simp
  continuous_toFun :=
    continuous_quot_lift
      (fun x y hxy =>
        Quot.sound ((intervalHomeomorph_endpointIdent_iff weights h x y).mp hxy))
      (continuous_quot_mk.comp (intervalHomeomorph weights h).continuous)
  continuous_invFun :=
    continuous_quot_lift
      (fun x y hxy => by
        apply Quot.sound
        apply (intervalHomeomorph_endpointIdent_iff weights h _ _).mpr
        simpa only [Homeomorph.apply_symm_apply] using hxy)
      (continuous_quot_mk.comp (intervalHomeomorph weights h).symm.continuous)

/-- The weighted interval map with endpoints identified, as a homeomorphism of additive
circles. -/
noncomputable def addCircleHomeomorph
    (weights : List ℕ) (h : Positive weights) (hne : weights ≠ []) :
    AddCircle (weights.length : ℝ) ≃ₜ AddCircle (weights.sum : ℝ) := by
  letI : Fact (0 < (weights.length : ℝ)) :=
    ⟨by exact_mod_cast List.length_pos_of_ne_nil hne⟩
  letI : Fact (0 < (weights.sum : ℝ)) :=
    ⟨by exact_mod_cast List.sum_pos weights h hne⟩
  exact
    (AddCircle.homeoIccQuot (weights.length : ℝ) 0).trans
      ((endpointQuotHomeomorph weights h).trans
        (AddCircle.homeoIccQuot (weights.sum : ℝ) 0).symm)

/-- The weighted subdivision homeomorphism transported to the complex unit circle. -/
noncomputable def circleHomeomorph
    (weights : List ℕ) (h : Positive weights) (hne : weights ≠ []) :
    Circle ≃ₜ Circle := by
  have hlength : (weights.length : ℝ) ≠ 0 := by
    exact_mod_cast (List.length_pos_of_ne_nil hne).ne'
  have hsum : (weights.sum : ℝ) ≠ 0 := by
    exact_mod_cast (List.sum_pos weights h hne).ne'
  exact
    (AddCircle.homeomorphCircle hlength).symm |>.trans
      ((addCircleHomeomorph weights h hne).trans
        (AddCircle.homeomorphCircle hsum))

theorem addCircleHomeomorph_apply_of_mem_Ico
    (weights : List ℕ) (h : Positive weights) (hne : weights ≠ [])
    (x : ℝ) (hx : x ∈ Set.Ico 0 (weights.length : ℝ)) :
    addCircleHomeomorph weights h hne
        (x : AddCircle (weights.length : ℝ)) =
      (stretch weights x : AddCircle (weights.sum : ℝ)) := by
  letI : Fact (0 < (weights.length : ℝ)) :=
    ⟨by exact_mod_cast List.length_pos_of_ne_nil hne⟩
  letI : Fact (0 < (weights.sum : ℝ)) :=
    ⟨by exact_mod_cast List.sum_pos weights h hne⟩
  unfold addCircleHomeomorph
  simp only [Homeomorph.trans_apply]
  have hsource :
      (AddCircle.homeoIccQuot (weights.length : ℝ) 0)
          (x : AddCircle (weights.length : ℝ)) =
        Quot.mk _ ⟨x, hx.1, by simpa using hx.2.le⟩ := by
    change Quot.mk _
      (Set.inclusion Set.Ico_subset_Icc_self
        (AddCircle.equivIco (weights.length : ℝ) 0
          (x : AddCircle (weights.length : ℝ)))) = _
    rw [AddCircle.equivIco, QuotientAddGroup.equivIcoMod_coe]
    apply congrArg (Quot.mk _)
    apply Subtype.ext
    exact (toIcoMod_eq_self (Fact.out : 0 < (weights.length : ℝ))).2
      (by simpa only [zero_add] using hx)
  rw [hsource]
  rfl

/-- On the fundamental interval, the circle homeomorphism is exactly the weighted
piecewise-linear angular map. -/
theorem circleHomeomorph_exp_of_mem_Ico
    (weights : List ℕ) (h : Positive weights) (hne : weights ≠ [])
    (x : ℝ) (hx : x ∈ Set.Ico 0 (weights.length : ℝ)) :
    circleHomeomorph weights h hne
        (Circle.exp (2 * Real.pi / weights.length * x)) =
      Circle.exp (2 * Real.pi / weights.sum * stretch weights x) := by
  have hlength : (weights.length : ℝ) ≠ 0 := by
    exact_mod_cast (List.length_pos_of_ne_nil hne).ne'
  have hsum : (weights.sum : ℝ) ≠ 0 := by
    exact_mod_cast (List.sum_pos weights h hne).ne'
  rw [show Circle.exp (2 * Real.pi / weights.length * x) =
      AddCircle.homeomorphCircle hlength
        (x : AddCircle (weights.length : ℝ)) by
    rw [AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk]]
  unfold circleHomeomorph
  simp only [Homeomorph.trans_apply, Homeomorph.symm_apply_apply]
  rw [addCircleHomeomorph_apply_of_mem_Ico weights h hne x hx]
  rw [AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk]

/-- On the `i`th unit interval, stretching is affine with slope equal to the `i`th weight. -/
theorem stretch_index_add
    (weights : List ℕ) (i : Fin weights.length) (t : unitInterval) :
    stretch weights ((i : ℝ) + t) =
      (weights.take i).sum + weights.get i * (t : ℝ) := by
  induction weights with
  | nil => exact Fin.elim0 i
  | cons w weights ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [Fin.val_zero, Nat.cast_zero, zero_add, List.take_zero,
          List.sum_nil, List.get_cons_zero]
        rw [stretch, if_pos t.property.2]
      · by_cases hboundary :
          ((Fin.succ j : ℕ) : ℝ) + (t : ℝ) ≤ 1
        · have hjval : j.val = 0 := by
            have ht : (0 : ℝ) ≤ t := t.property.1
            have hjle : (j : ℝ) ≤ 0 := by
              change ((j.val + 1 : ℕ) : ℝ) + (t : ℝ) ≤ 1 at hboundary
              push_cast at hboundary
              linarith
            have hjleNat : j.val ≤ 0 := by exact_mod_cast hjle
            omega
          have ht0 : (t : ℝ) = 0 := by
            apply le_antisymm
            · simpa [Fin.succ, hjval] using hboundary
            · exact t.property.1
          rw [stretch, if_pos hboundary]
          simp [List.take_succ_cons, hjval, ht0]
        · rw [stretch, if_neg hboundary]
          have harg :
              (((Fin.succ j : ℕ) : ℝ) + (t : ℝ) - 1) =
                (j : ℝ) + t := by
            change ((j.val + 1 : ℕ) : ℝ) + (t : ℝ) - 1 =
              (j.val : ℝ) + t
            push_cast
            ring
          rw [harg, ih]
          simp [List.take_succ_cons]
          ring

/-- The weighted circle homeomorphism sends a point of side `i` to the boundary coordinate
obtained by adding the weighted prefix and the affine local parameter. -/
theorem circleHomeomorph_exp_index_add
    (weights : List ℕ) (h : Positive weights) (hne : weights ≠ [])
    (i : Fin weights.length) (t : unitInterval)
    (hnotLastEndpoint :
      ((i : ℝ) + (t : ℝ)) < weights.length) :
    circleHomeomorph weights h hne
        (Circle.exp
          (2 * Real.pi / weights.length * ((i : ℝ) + (t : ℝ)))) =
      Circle.exp
        (2 * Real.pi / weights.sum *
          ((weights.take i).sum + weights.get i * (t : ℝ))) := by
  rw [circleHomeomorph_exp_of_mem_Ico weights h hne]
  · rw [stretch_index_add]
  · exact
      ⟨add_nonneg (Nat.cast_nonneg _) t.property.1,
        hnotLastEndpoint⟩

/-- Endpoint-inclusive form of `circleHomeomorph_exp_index_add`.  The only additional case is
the terminal endpoint of the last source interval; both displayed angles then represent the
basepoint of their respective circles. -/
theorem circleHomeomorph_exp_index_add'
    (weights : List ℕ) (h : Positive weights) (hne : weights ≠ [])
    (i : Fin weights.length) (t : unitInterval) :
    circleHomeomorph weights h hne
        (Circle.exp
          (2 * Real.pi / weights.length * ((i : ℝ) + (t : ℝ)))) =
      Circle.exp
        (2 * Real.pi / weights.sum *
          ((weights.take i).sum + weights.get i * (t : ℝ))) := by
  by_cases hnotLastEndpoint :
      ((i : ℝ) + (t : ℝ)) < weights.length
  · exact circleHomeomorph_exp_index_add weights h hne i t hnotLastEndpoint
  · have hle :
        ((i : ℝ) + (t : ℝ)) ≤ weights.length := by
      have hi : ((i : ℝ) + 1) ≤ weights.length := by
        exact_mod_cast i.isLt
      linarith [t.property.2]
    have hend :
        ((i : ℝ) + (t : ℝ)) = weights.length :=
      le_antisymm hle (le_of_not_gt hnotLastEndpoint)
    have hpref :
        ((weights.take i).sum : ℝ) +
            weights.get i * (t : ℝ) = weights.sum := by
      rw [← stretch_index_add weights i t, hend, stretch_length]
    have hsource :
        Circle.exp
            (2 * Real.pi / weights.length * (weights.length : ℝ)) =
          Circle.exp 0 := by
      apply Circle.exp_eq_exp.mpr
      refine ⟨1, ?_⟩
      have hlength : (weights.length : ℝ) ≠ 0 := by
        exact_mod_cast (List.length_pos_of_ne_nil hne).ne'
      field_simp [hlength]
      all_goals ring
    have htarget :
        Circle.exp
            (2 * Real.pi / weights.sum * (weights.sum : ℝ)) =
          Circle.exp 0 := by
      apply Circle.exp_eq_exp.mpr
      refine ⟨1, ?_⟩
      have hsum : (weights.sum : ℝ) ≠ 0 := by
        exact_mod_cast (List.sum_pos weights h hne).ne'
      field_simp [hsum]
      all_goals ring
    have hzero :
        circleHomeomorph weights h hne (Circle.exp 0) =
          Circle.exp 0 := by
      simpa only [mul_zero, stretch_zero] using
        circleHomeomorph_exp_of_mem_Ico weights h hne 0
          ⟨le_rfl, by
            exact_mod_cast List.length_pos_of_ne_nil hne⟩
    rw [hend, hpref, hsource, htarget, hzero]

end WeightedCircle

end LeanEval.Topology.ClassificationOfSurfaces
