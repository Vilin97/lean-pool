/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.HighlyOrderTransitive
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Linear ordered fields are highly order-transitive (issue #11 unit 6a)

Every linear ordered field is a highly order-transitive linear order
(`HighlyOrderTransitive.of_field`): a finite increasing tuple is moved onto another one point at
a time, left to right — the first point by translation, and each subsequent point by a **cut
dilation** (`dilateAbove`): the order automorphism that is the identity on `(-∞, a]` and the
positive affine dilation `z ↦ a + ((y-a)/(x-a)) * (z-a)` above the last already-placed target
`a`, carrying the current point `x` to its target `y` while fixing everything already placed.

The automorphism is built as a piecewise strictly monotone surjection
(`StrictMono.orderIsoOfSurjective`) — no order-sum gluing needed.
-/

namespace FirstOrder

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The cut-dilation function: identity up to `a`, positive dilation with factor `c` above. -/
private def dilateFun (a c : K) (z : K) : K :=
  if z ≤ a then z else a + c * (z - a)

private theorem dilateFun_strictMono {a c : K} (hc : 0 < c) : StrictMono (dilateFun a c) := by
  intro z w hzw
  unfold dilateFun
  rcases le_or_gt w a with hw | hw
  · rw [ite_eq_left (hzw.le.trans hw), ite_eq_left hw]
    exact hzw
  · rw [ite_eq_right (not_le.mpr hw)]
    rcases le_or_gt z a with hz | hz
    · rw [ite_eq_left hz]
      calc z ≤ a := hz
        _ < a + c * (w - a) := lt_add_of_pos_right a (mul_pos hc (sub_pos.mpr hw))
    · rw [ite_eq_right (not_le.mpr hz)]
      have := mul_lt_mul_of_pos_left (sub_lt_sub_right hzw a) hc
      linarith

private theorem dilateFun_surjective {a c : K} (hc : 0 < c) : Function.Surjective (dilateFun a c) := by
  intro w
  rcases le_or_gt w a with hw | hw
  · exact ⟨w, by rw [dilateFun, ite_eq_left hw]⟩
  · refine ⟨a + (w - a) / c, ?_⟩
    have hz : a < a + (w - a) / c :=
      lt_add_of_pos_right a (div_pos (sub_pos.mpr hw) hc)
    rw [dilateFun, ite_eq_right (not_le.mpr hz)]
    field_simp
    ring

/-- **The cut dilation**: the order automorphism that is the identity on `(-∞, a]` and carries
`x` to `y` above `a`. -/
private noncomputable def dilateAbove (a x y : K) (hx : a < x) (hy : a < y) : K ≃o K :=
  StrictMono.orderIsoOfSurjective (dilateFun a ((y - a) / (x - a)))
    (dilateFun_strictMono (div_pos (sub_pos.mpr hy) (sub_pos.mpr hx)))
    (dilateFun_surjective (div_pos (sub_pos.mpr hy) (sub_pos.mpr hx)))

private theorem dilateAbove_apply_of_le {a x y : K} (hx : a < x) (hy : a < y) {z : K} (hz : z ≤ a) :
    dilateAbove a x y hx hy z = z := by
  show dilateFun a _ z = z
  rw [dilateFun, ite_eq_left hz]

private theorem dilateAbove_apply_point {a x y : K} (hx : a < x) (hy : a < y) :
    dilateAbove a x y hx hy x = y := by
  show dilateFun a _ x = y
  rw [dilateFun, ite_eq_right (not_le.mpr hx), div_mul_cancel₀ _ (sub_ne_zero.mpr hx.ne')]
  ring

/-- **Every linear ordered field is highly order-transitive** — the left-to-right point-moving
induction: translation for the first point, cut dilations for the rest. -/
theorem HighlyOrderTransitive.of_field (K : Type*) [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] : HighlyOrderTransitive K := by
  intro n
  induction n with
  | zero => exact fun s t => ⟨OrderIso.refl K, fun i => i.elim0⟩
  | succ n IH =>
    intro s t
    obtain ⟨e', he'⟩ := IH (Fin.castSuccOrderEmb.trans s) (Fin.castSuccOrderEmb.trans t)
    have he'' : ∀ i : Fin n, e' (s (Fin.castSucc i)) = t (Fin.castSucc i) := he'
    rcases n with _ | m
    · refine ⟨OrderIso.addRight (t 0 - s 0), fun i => ?_⟩
      have h0 : i = 0 := Fin.ext (by omega)
      subst h0
      show s 0 + (t 0 - s 0) = t 0
      ring
    · have hax : t (Fin.castSucc (Fin.last m)) < e' (s (Fin.last (m + 1))) := by
        rw [← he'' (Fin.last m)]
        exact e'.lt_iff_lt.mpr (s.lt_iff_lt.mpr (Fin.castSucc_lt_last _))
      have hay : t (Fin.castSucc (Fin.last m)) < t (Fin.last (m + 1)) :=
        t.lt_iff_lt.mpr (Fin.castSucc_lt_last _)
      refine ⟨e'.trans (dilateAbove _ _ _ hax hay), fun i => ?_⟩
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · show dilateAbove _ _ _ hax hay (e' (s (Fin.castSucc j))) = t (Fin.castSucc j)
        rw [he'' j]
        exact dilateAbove_apply_of_le hax hay
          (t.le_iff_le.mpr (Fin.castSucc_le_castSucc_iff.mpr (Fin.le_last j)))
      · show dilateAbove _ _ _ hax hay (e' (s (Fin.last (m + 1)))) = t (Fin.last (m + 1))
        exact dilateAbove_apply_point hax hay

end FirstOrder
