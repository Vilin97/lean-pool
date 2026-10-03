/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JD Jones
-/
module

public import LeanPool.NaslundCounterexample.Code
public import LeanPool.NaslundCounterexample.Polynomials
public import LeanPool.NaslundCounterexample.Below

/-!
# The lift

Given an even `m` and a square-difference-free set `B` of polynomials of degree below `m`, the
lift is

`L_m(B) = { V_s + P·R_r + Q·(b + s_∞ T^m + u T^{m+1}) : s ∈ S, r ∈ F_3^3, u ∈ F_3, b ∈ B }`,

a set of polynomials of degree below `m + 8` with exactly `810 · |B|` elements, again
square-difference-free.

Three features of the formula do the work. The values of a lifted polynomial at `0, 1, 2` are
`s_0, s_1, s_2`, because `P` and `Q` vanish there; its coefficient at `T^{m+6}` is `s_∞`, because
`Q` has degree `6` and no `T^5` term; and the remaining freedom `(r, u, b)` is recovered from the
polynomial itself, which is what makes the parameter map injective. A square difference of two
lifted polynomials therefore has all four coordinates of `s' - s` in `{0, 1}`, so the code
property gives `s = s'`; what is left is a square difference inside `B`, which `B` does not have.
-/

public section

namespace NaslundCounterexample

open Polynomial

/-- A parameter tuple `(s, r, u, b)`: a word of the code, the coefficient vector of `R`, a scalar,
and an element of the base. -/
abbrev Parameters := (Fin 4 → ZMod 3) × (Fin 3 → ZMod 3) × ZMod 3 × (ZMod 3)[X]

/-- The tail of a lifted polynomial, `b + s_∞ T^m + u T^{m+1}`: what the multiplier `Q` acts on. -/
noncomputable def tail (m : ℕ) (p : Parameters) : (ZMod 3)[X] :=
  p.2.2.2 + C (p.1 3) * X ^ m + C p.2.2.1 * X ^ (m + 1)

/-- The lift of one parameter tuple, `V_s + P·R_r + Q·(b + s_∞ T^m + u T^{m+1})`. -/
noncomputable def liftMap (m : ℕ) (p : Parameters) : (ZMod 3)[X] :=
  V p.1 + P * R p.2.1 + Q * tail m p

/-- The parameter set `S × F_3^3 × F_3 × B`. -/
noncomputable def parameters (B : Finset (ZMod 3)[X]) : Finset Parameters :=
  code ×ˢ ((Finset.univ : Finset (Fin 3 → ZMod 3)) ×ˢ
    ((Finset.univ : Finset (ZMod 3)) ×ˢ B))

/-- The lifted set `L_m(B)`, the image of the parameter set under the lift. -/
noncomputable def lift (m : ℕ) (B : Finset (ZMod 3)[X]) : Finset (ZMod 3)[X] :=
  open scoped Classical in (parameters B).image (liftMap m)

/-- A tuple is a parameter exactly when its code word and its base element are. -/
theorem mem_params {B : Finset (ZMod 3)[X]} {p : Parameters} :
    p ∈ parameters B ↔ p.1 ∈ code ∧ p.2.2.2 ∈ B := by
  simp [parameters, Finset.mem_product]

/-- There are `810 · |B|` parameter tuples: `10 · 27 · 3` choices besides the base element. -/
theorem parameters_card (B : Finset (ZMod 3)[X]) : (parameters B).card = 810 * B.card := by
  rw [parameters, Finset.card_product, Finset.card_product, Finset.card_product, code_card,
    Finset.card_univ, Finset.card_univ, Fintype.card_fun]
  simp [ZMod.card]
  ring

/-- Membership in the lifted set: the elements of `L_m(B)` are the lifts of parameter tuples. -/
theorem mem_lift {m : ℕ} {B : Finset (ZMod 3)[X]} {f : (ZMod 3)[X]} :
    f ∈ lift m B ↔ ∃ p ∈ parameters B, liftMap m p = f := by
  classical
  simp [lift, Finset.mem_image]

/-- The tail has degree below `m + 2` when its base element has degree below `m`. -/
theorem tail_below (m : ℕ) {p : Parameters} (hb : Below m p.2.2.2) : Below (m + 2) (tail m p) := by
  unfold tail
  exact ((hb.mono (by omega)).add (below_C_mul_X_pow _ m (m + 2) (by omega))).add
    (below_C_mul_X_pow _ (m + 1) (m + 2) (by omega))

/-- The degree bound: a lift of a tuple whose base element has degree below `m` has degree below
`m + 8`. -/
theorem liftMap_below (m : ℕ) {p : Parameters} (hb : Below m p.2.2.2) :
    Below (m + 8) (liftMap m p) := by
  have h1 : Below (m + 8) (V p.1 + P * R p.2.1) :=
    Below.mono (by omega) (below_of_degree_le (m := 5) (degree_V_add_P_mul_R_le p.1 p.2.1))
  have h3 : Below (m + 8) (Q * tail m p) := by
    have h4 := (tail_below m hb).Q_mul
    rwa [show m + 2 + 6 = m + 8 from by omega] at h4
  exact h1.add h3

/-- The value of a lifted polynomial at `0` is the code coordinate `s_0`. -/
theorem eval_liftMap_zero (m : ℕ) (p : Parameters) : (liftMap m p).eval 0 = p.1 0 := by
  simp [liftMap, eval_P, eval_Q, eval_V_zero]

/-- The value of a lifted polynomial at `1` is the code coordinate `s_1`. -/
theorem eval_liftMap_one (m : ℕ) (p : Parameters) : (liftMap m p).eval 1 = p.1 1 := by
  simp [liftMap, eval_P, eval_Q, eval_V_one]

/-- The value of a lifted polynomial at `2` is the code coordinate `s_2`. -/
theorem eval_liftMap_two (m : ℕ) (p : Parameters) : (liftMap m p).eval 2 = p.1 2 := by
  simp [liftMap, eval_P, eval_Q, eval_V_two]

/-- The coefficient of the tail at `T^m` is the code coordinate `s_∞`: the base element does not
reach `T^m` and the term `u T^{m+1}` lies above it. -/
theorem coeff_tail_self (m : ℕ) {p : Parameters} (hb : Below m p.2.2.2) :
    (tail m p).coeff m = p.1 3 := by
  have h : p.2.2.2.coeff m = 0 := hb.coeff_eq_zero (le_refl m)
  simp [tail, h]

/-- The coefficient of the tail at `T^{m+1}` is the scalar `u`: the base element does not reach
`T^{m+1}` and the term `s_∞ T^m` lies below it. -/
theorem coeff_tail_succ (m : ℕ) {p : Parameters} (hb : Below m p.2.2.2) :
    (tail m p).coeff (m + 1) = p.2.2.1 := by
  have h : p.2.2.2.coeff (m + 1) = 0 := hb.coeff_eq_zero (by omega)
  simp [tail, h]

/-- A difference `P · (R_r - R_{r'})` has degree below `6`: this is the part of a difference of
two lifted polynomials that lies below the multiplier `Q`, and it is what forces `r = r'`. -/
theorem degree_P_mul_R_sub_lt (r r' : Fin 3 → ZMod 3) : (P * (R r - R r')).degree < 6 := by
  have h3 : Below 3 (R r - R r') :=
    (below_of_degree_le (m := 2) (degree_R_le r)).sub (below_of_degree_le (m := 2) (degree_R_le r'))
  have h6 : Below 6 (P * (R r - R r')) := h3.P_mul
  simpa [Below] using h6

/-- **The top coordinate.** When the base element has degree below `m`, the coefficient of a
lifted polynomial at `T^{m+6}` is the code coordinate `s_∞`: the part `V_s + P·R_r` has degree at
most `5 < m + 6`; `Q · b` has degree below `m + 6`; `Q · s_∞ T^m` contributes `s_∞` times the
leading coefficient of `Q`; and `Q · u T^{m+1}` would contribute `u` times the vanishing
coefficient `[T^5] Q`. -/
theorem coeff_liftMap_top (m : ℕ) {p : Parameters} (hb : Below m p.2.2.2) :
    (liftMap m p).coeff (m + 6) = p.1 3 := by
  have hlow : (V p.1 + P * R p.2.1).coeff (m + 6) = 0 :=
    (Below.mono (by omega)
      (below_of_degree_le (m := 5) (degree_V_add_P_mul_R_le p.1 p.2.1))).coeff_eq_zero
      (le_refl (m + 6))
  have hQb : (Q * p.2.2.2).coeff (m + 6) = 0 := hb.Q_mul.coeff_eq_zero (le_refl (m + 6))
  have hs : (Q * (C (p.1 3) * X ^ m)).coeff (m + 6) = p.1 3 := by
    have h : Q * (C (p.1 3) * X ^ m) = Q * C (p.1 3) * X ^ m := by ring
    rw [h, show m + 6 = 6 + m from by omega, coeff_mul_X_pow, coeff_mul_C, coeff_Q_six, one_mul]
  have hu : (Q * (C p.2.2.1 * X ^ (m + 1))).coeff (m + 6) = 0 := by
    have h : Q * (C p.2.2.1 * X ^ (m + 1)) = Q * C p.2.2.1 * X ^ (m + 1) := by ring
    rw [h, show m + 6 = 5 + (m + 1) from by omega, coeff_mul_X_pow, coeff_mul_C, coeff_Q_five,
      zero_mul]
  simp only [liftMap, tail, mul_add, coeff_add, hlow, hQb, hs, hu, zero_add, add_zero]

/-- Evaluations and the top coefficient recover the code word from a lifted polynomial. -/
theorem code_eq_of_liftMap_eq (m : ℕ) {p p' : Parameters}
    (hb : Below m p.2.2.2) (hb' : Below m p'.2.2.2) (h : liftMap m p = liftMap m p') :
    p.1 = p'.1 := by
  have h0 : p.1 0 = p'.1 0 := by
    rw [← eval_liftMap_zero m p, ← eval_liftMap_zero m p', h]
  have h1 : p.1 1 = p'.1 1 := by
    rw [← eval_liftMap_one m p, ← eval_liftMap_one m p', h]
  have h2 : p.1 2 = p'.1 2 := by
    rw [← eval_liftMap_two m p, ← eval_liftMap_two m p', h]
  have h3 : p.1 3 = p'.1 3 := by
    rw [← coeff_liftMap_top m hb, ← coeff_liftMap_top m hb', h]
  funext i
  fin_cases i
  exacts [h0, h1, h2, h3]

/-- Equal lifts with equal code words have equal low-degree vectors and equal tails. -/
theorem remainder_and_tail_eq (m : ℕ) {p p' : Parameters}
    (h : liftMap m p = liftMap m p') (hs : p.1 = p'.1) :
    p.2.1 = p'.2.1 ∧ tail m p' = tail m p := by
  have hV : V p.1 = V p'.1 := by rw [hs]
  have key : P * (R p.2.1 - R p'.2.1) = Q * (tail m p' - tail m p) := by
    have h' := h
    simp only [liftMap] at h'
    rw [hV] at h'
    linear_combination h'
  have hzero : P * (R p.2.1 - R p'.2.1) = 0 :=
    eq_zero_of_Q_dvd_of_degree_lt _ (degree_P_mul_R_sub_lt p.2.1 p'.2.1) ⟨_, key⟩
  have hr : p.2.1 = p'.2.1 := by
    rcases mul_eq_zero.mp hzero with hP | hR
    · exact absurd hP P_ne_zero
    · exact R_injective (sub_eq_zero.mp hR)
  -- cancelling `Q` identifies the tails, hence `u` and `b`
  have htail : tail m p' = tail m p := by
    have hQ : Q * (tail m p' - tail m p) = 0 := by rw [← key, hzero]
    rcases mul_eq_zero.mp hQ with hQ0 | ht
    · exact absurd hQ0 Q_ne_zero
    · exact sub_eq_zero.mp ht
  exact ⟨hr, htail⟩

/-- **Injectivity of the lift on parameters.** Two tuples with base elements of degree below `m`
that lift to the same polynomial are equal. No division algorithm is needed: equal outputs give
`(V_s + P·R_r) - (V_s' + P·R_r') = Q · (tail' - tail)`, whose left side has degree below `6`, so
both sides vanish; evaluating at `0, 1, 2` identifies the code words, cancelling `P` identifies
`r`, and comparing the coefficients at `T^m` and `T^{m+1}` identifies `u` and `b`. -/
theorem liftMap_injOn (m : ℕ) (B : Finset (ZMod 3)[X]) (hB : AllBelow m B) :
    Set.InjOn (liftMap m) (parameters B) := by
  intro p hp p' hp' h
  have hpm : p ∈ parameters B := Finset.mem_coe.mp hp
  have hpm' : p' ∈ parameters B := Finset.mem_coe.mp hp'
  have hb : Below m p.2.2.2 := hB _ (mem_params.mp hpm).2
  have hb' : Below m p'.2.2.2 := hB _ (mem_params.mp hpm').2
  have hs := code_eq_of_liftMap_eq m hb hb' h
  have h3 : p.1 3 = p'.1 3 := by rw [hs]
  obtain ⟨hr, htail⟩ := remainder_and_tail_eq m h hs
  have hu : p.2.2.1 = p'.2.2.1 := by
    rw [← coeff_tail_succ m hb, ← coeff_tail_succ m hb', htail]
  have hbb : p.2.2.2 = p'.2.2.2 := by
    have ht := htail
    simp only [tail, h3, hu] at ht
    exact (add_right_cancel (add_right_cancel ht)).symm
  obtain ⟨s, r, u, b⟩ := p
  obtain ⟨s', r', u', b'⟩ := p'
  simp only [Prod.mk.injEq]
  exact ⟨hs, hr, hu, hbb⟩

/-- The lift multiplies cardinality by `810`. -/
theorem lift_card (m : ℕ) (B : Finset (ZMod 3)[X]) (hB : AllBelow m B) :
    (lift m B).card = 810 * B.card := by
  classical
  rw [lift, Finset.card_image_of_injOn (liftMap_injOn m B hB), parameters_card]

/-- The lift of a set of polynomials of degree below `m` has degree below `m + 8`. -/
theorem lift_allBelow (m : ℕ) (B : Finset (ZMod 3)[X]) (hB : AllBelow m B) :
    AllBelow (m + 8) (lift m B) := by
  intro f hf
  obtain ⟨p, hp, rfl⟩ := mem_lift.mp hf
  exact liftMap_below m (hB _ (mem_params.mp hp).2)

/-- A square difference of lifts from an even degree bound has a bounded-degree square root. -/
theorem square_difference_root_degree (t : ℕ) {p p' : Parameters} {z : (ZMod 3)[X]}
    (hb : Below (t + t) p.2.2.2) (hb' : Below (t + t) p'.2.2.2)
    (hz : liftMap (t + t) p' - liftMap (t + t) p = z ^ 2) :
    z.natDegree ≤ t + 3 := by
  have hdiff : Below (t + t + 7 + 1) (z ^ 2) := by
    have h8 : Below (t + t + 8) (z ^ 2) := by
      rw [← hz]
      exact (liftMap_below _ hb').sub (liftMap_below _ hb)
    rwa [show t + t + 8 = t + t + 7 + 1 from by omega] at h8
  have h1 := hdiff.natDegree_le
  rw [Polynomial.natDegree_pow] at h1
  omega

/-- All four code coordinates of a square difference are squares, so the code words agree. -/
theorem code_eq_of_square_difference (t : ℕ) {p p' : Parameters} {z : (ZMod 3)[X]}
    (hp : p.1 ∈ code) (hp' : p'.1 ∈ code)
    (hb : Below (t + t) p.2.2.2) (hb' : Below (t + t) p'.2.2.2)
    (hz : liftMap (t + t) p' - liftMap (t + t) p = z ^ 2) : p.1 = p'.1 := by
  have hzdeg := square_difference_root_degree t hb hb' hz
  have htop : p'.1 3 - p.1 3 = z.coeff (t + 3) ^ 2 := by
    have hc := congrArg (fun f => Polynomial.coeff f (t + t + 6)) hz
    simp only [coeff_sub, coeff_liftMap_top _ hb, coeff_liftMap_top _ hb'] at hc
    rw [show t + t + 6 = 2 * (t + 3) from by omega,
      Polynomial.coeff_pow_of_natDegree_le hzdeg] at hc
    exact hc
  have hev0 : p'.1 0 - p.1 0 = z.eval 0 ^ 2 := by
    have hc := congrArg (fun f => Polynomial.eval 0 f) hz
    simpa [eval_liftMap_zero] using hc
  have hev1 : p'.1 1 - p.1 1 = z.eval 1 ^ 2 := by
    have hc := congrArg (fun f => Polynomial.eval 1 f) hz
    simpa [eval_liftMap_one] using hc
  have hev2 : p'.1 2 - p.1 2 = z.eval 2 ^ 2 := by
    have hc := congrArg (fun f => Polynomial.eval 2 f) hz
    simpa [eval_liftMap_two] using hc
  have hsq : ∀ i : Fin 4, ∃ w : ZMod 3, p'.1 i - p.1 i = w ^ 2 := by
    intro i
    fin_cases i
    exacts [⟨_, hev0⟩, ⟨_, hev1⟩, ⟨_, hev2⟩, ⟨_, htop⟩]
  exact code_property p.1 hp p'.1 hp' fun i => by
    obtain ⟨w, hw⟩ := hsq i
    rw [hw]
    exact sq_eq_zero_or_one w

/-- Equal code coordinates force the square root to vanish at every element of `F_3`. -/
theorem P_dvd_of_square_difference (m : ℕ) {p p' : Parameters} {z : (ZMod 3)[X]}
    (hcode : p.1 = p'.1) (hz : liftMap m p' - liftMap m p = z ^ 2) : P ∣ z := by
  apply P_dvd_of_eval
  · have h := congrArg (fun f => Polynomial.eval 0 f) hz
    have hzero : z.eval 0 ^ 2 = 0 := by simpa [eval_liftMap_zero, hcode] using h.symm
    exact eq_zero_of_sq_eq_zero _ hzero
  · have h := congrArg (fun f => Polynomial.eval 1 f) hz
    have hzero : z.eval 1 ^ 2 = 0 := by simpa [eval_liftMap_one, hcode] using h.symm
    exact eq_zero_of_sq_eq_zero _ hzero
  · have h := congrArg (fun f => Polynomial.eval 2 f) hz
    have hzero : z.eval 2 ^ 2 = 0 := by simpa [eval_liftMap_two, hcode] using h.symm
    exact eq_zero_of_sq_eq_zero _ hzero

/-- The low-degree part vanishes, allowing cancellation of `Q` from a square difference. -/
theorem square_eq_tail_difference (m : ℕ) {p p' : Parameters} {z w : (ZMod 3)[X]}
    (hcode : p.1 = p'.1) (hz : liftMap m p' - liftMap m p = z ^ 2) (hw : z = P * w) :
    w ^ 2 = tail m p' - tail m p := by
  have hQw : z ^ 2 = Q * w ^ 2 := by simp only [Q, hw, mul_pow]
  have hV : V p'.1 = V p.1 := by rw [hcode]
  have key : P * (R p'.2.1 - R p.2.1) = Q * (w ^ 2 - (tail m p' - tail m p)) := by
    have h' := hz
    simp only [liftMap] at h'
    rw [hV, hQw] at h'
    linear_combination h'
  have hzero : P * (R p'.2.1 - R p.2.1) = 0 :=
    eq_zero_of_Q_dvd_of_degree_lt _ (degree_P_mul_R_sub_lt p'.2.1 p.2.1) ⟨_, key⟩
  have hQ : Q * (w ^ 2 - (tail m p' - tail m p)) = 0 := by rw [← key, hzero]
  rcases mul_eq_zero.mp hQ with hQ0 | ht
  · exact absurd hQ0 Q_ne_zero
  · exact sub_eq_zero.mp ht

/-- A tail difference has odd degree unless its scalar coordinates agree. -/
theorem scalar_eq_of_square_tail (t : ℕ) {p p' : Parameters} {w : (ZMod 3)[X]}
    (hb : Below (t + t) p.2.2.2) (hb' : Below (t + t) p'.2.2.2)
    (hcode : p.1 = p'.1) (hw2 : w ^ 2 = tail (t + t) p' - tail (t + t) p) :
    p'.2.2.1 = p.2.2.1 := by
  have htaildiff : tail (t + t) p' - tail (t + t) p
      = (p'.2.2.2 - p.2.2.2) + C (p'.2.2.1 - p.2.2.1) * X ^ (t + t + 1) := by
    simp only [tail, hcode, map_sub]
    ring
  by_contra hne
  have hsub : Below (t + t) (p'.2.2.2 - p.2.2.2) := hb'.sub hb
  have hlt : (p'.2.2.2 - p.2.2.2).natDegree
      < (C (p'.2.2.1 - p.2.2.1) * X ^ (t + t + 1)).natDegree := by
    rw [natDegree_C_mul_X_pow _ _ (sub_ne_zero.mpr hne)]
    have hle : (p'.2.2.2 - p.2.2.2).natDegree ≤ t + t :=
      Below.natDegree_le (hsub.mono (by omega))
    omega
  have hdeg : (w ^ 2).natDegree = t + t + 1 := by
    rw [hw2, htaildiff, natDegree_add_eq_right_of_natDegree_lt hlt,
      natDegree_C_mul_X_pow _ _ (sub_ne_zero.mpr hne)]
  rw [Polynomial.natDegree_pow] at hdeg
  omega

/-- **The lift preserves square-difference-freeness** for even `m`. If two lifted polynomials
differ by `z^2`, then the four coordinates of `s' - s` are squares in `F_3`, hence in `{0, 1}`,
so the code property gives `s = s'`; then `z` vanishes on `F_3`, so `z = P·w`, the parts below
`Q` cancel, and `w^2 = (b' - b) + (u' - u) T^{m+1}`. A nonzero square has even natural degree,
while `m + 1` is odd, so `u' = u`; and `w^2 = b' - b` forces `w = 0` because `B` is
square-difference-free. -/
theorem lift_sdf (m : ℕ) (B : Finset (ZMod 3)[X]) (hm : Even m) (hB : AllBelow m B)
    (hS : SquareDifferenceFree B) : SquareDifferenceFree (lift m B) := by
  obtain ⟨t, rfl⟩ := hm
  intro f hf g hg z hz
  obtain ⟨p, hp, rfl⟩ := mem_lift.mp hf
  obtain ⟨p', hp', rfl⟩ := mem_lift.mp hg
  have hb := hB _ (mem_params.mp hp).2
  have hb' := hB _ (mem_params.mp hp').2
  have hcode := code_eq_of_square_difference t (mem_params.mp hp).1 (mem_params.mp hp').1 hb hb' hz
  obtain ⟨w, hw⟩ := P_dvd_of_square_difference (t + t) hcode hz
  have hw2 := square_eq_tail_difference (t + t) hcode hz hw
  have hu := scalar_eq_of_square_tail t hb hb' hcode hw2
  have hbeq : p'.2.2.2 - p.2.2.2 = w ^ 2 := by
    rw [hw2]
    simp only [tail, hcode, hu]
    ring
  have hw0 := hS _ (mem_params.mp hp).2 _ (mem_params.mp hp').2 w hbeq
  rw [hw, hw0, mul_zero]

end NaslundCounterexample
