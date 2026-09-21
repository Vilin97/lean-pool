/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.GramRank
import LeanPool.RegtsSevenster.RS.Novel.Skein.SuperSpace

/-!
# The super form on boundary states, and the rank it bounds

A boundary state at arity `t` is a coordinate of the `t`-fold tensor
power of `V_k ⊕ V_{2ℓ}`, so a vector in that power is a function on
boundary states.  The ambient bilinear form is the `t`-fold product
of the super form on one leg: the identity on the even colours and
the symplectic form on the odd ones, zero across the two.  That one
leg's form is the through-edge state factor the mixed partition
function already uses.

Writing the connection pairing as this form evaluated at vectors
attached to the two fragments bounds the edge-rank by `(k + 2ℓ)^t`,
because that is how many boundary states there are.
-/

namespace RS

open Classical

/-- **The super form on boundary states at arity `t`**: the product
over the legs of the one-leg form of RS21 (11) — the identity on the
even colours and the symplectic form on the odd ones, zero across
the two. -/
noncomputable def superForm {k ℓ : ℕ} (t : ℕ)
    (x y : GenBoundaryState k ℓ (Fin t)) : ℂ :=
  ∏ i : Fin t, superLeg (x i) (y i)

/-- **A super-Gram factorization bounds the edge-rank by
`k + 2ℓ`.** -/
theorem edgeRankBounded_of_superGram {k ℓ : ℕ}
    {f : ClosedFragment → ℂ}
    (T : ∀ t : ℕ, Fragment (Fin t) → GenBoundaryState k ℓ (Fin t) → ℂ)
    (hgram : ∀ (t : ℕ) (F G : Fragment (Fin t)),
      connectionPairing f t F G
        = ∑ x : GenBoundaryState k ℓ (Fin t),
            ∑ y : GenBoundaryState k ℓ (Fin t),
              superForm t x y * T t F x * T t G y) :
    EdgeRankBounded f (k + 2 * ℓ) :=
  edgeRankBounded_of_gram (fun t => GenBoundaryState k ℓ (Fin t))
    (fun t => by
      rw [card_genBoundaryState k ℓ (Fin t), Fintype.card_fin])
    (fun t => superForm t) T hgram

/-! ### The fragment tensor's normalisation

The super form pairs an odd leg's two colours antisymmetrically, so
across the legs a matched pair of fragments picks up `(-1)` once for
each of the half of the used legs where the first fragment's arc
enters.  The fragment tensor carries a fourth root of unity per two
used legs, and the two fragments' roots multiply to exactly that
sign.  Since a leg is used exactly when its colour is odd, the
factor depends on the boundary state alone.
-/

/-- The number of legs a boundary state colours oddly. -/
noncomputable def oddCount {k ℓ t : ℕ}
    (x : GenBoundaryState k ℓ (Fin t)) : ℕ :=
  (Finset.univ.filter (fun i => ∃ c, x i = Sum.inr c)).card

/-- **The fragment tensor's normalising root**: a fourth root of
unity, one quarter turn for every two odd legs. -/
noncomputable def stateTwist {k ℓ t : ℕ}
    (x : GenBoundaryState k ℓ (Fin t)) : ℂ :=
  Complex.I ^ (oddCount x / 2)

/-- **The two fragments' roots multiply to the form's sign.**  On a
matched pair of states the product is `(-1)` to half the number of
odd legs — exactly the sign the antisymmetric legs contribute. -/
theorem stateTwist_mul_stateTwist {k ℓ t : ℕ}
    {x y : GenBoundaryState k ℓ (Fin t)}
    (hxy : oddCount x = oddCount y) :
    stateTwist x * stateTwist y = (-1 : ℂ) ^ (oddCount x / 2) := by
  unfold stateTwist
  rw [← hxy, ← pow_add, ← two_mul, pow_mul, Complex.I_sq]

/-- **The roots cancel the legs' sign** — RS21's "these
contributions cancel with `(-1)^{|S(H₁)|/4} (-1)^{|S(H₂)|/4}`".  At
half the used legs the first fragment's arc enters and the form is
`⟨f_c, g_c⟩ = -1`; at the other half it leaves and the form is
`⟨g_c, f_c⟩ = 1`.  So the legs contribute `(-1)` to half the number
of used legs, and the two fragments' fourth roots multiply to the
same thing. -/
theorem stateTwist_mul_stateTwist_mul_half {k ℓ t : ℕ}
    {x y : GenBoundaryState k ℓ (Fin t)}
    (hxy : oddCount x = oddCount y) {m : ℕ} (hm : oddCount x = 2 * m) :
    (stateTwist x * stateTwist y) * (-1 : ℂ) ^ m = 1 := by
  rw [stateTwist_mul_stateTwist hxy, hm,
    show 2 * m / 2 = m from by omega, ← pow_add, ← two_mul, pow_mul]
  norm_num

/-! ### The form vanishes across a parity mismatch

The one-leg form is zero between an even colour and an odd one, so
two states differing in parity at any leg pair to zero.  This is
what makes two fragments' tensors orthogonal when their subsets use
different label sets.
-/

/-- **An even leg against an odd one kills the form.** -/
theorem superForm_eq_zero_of_left_right {k ℓ t : ℕ}
    (x y : GenBoundaryState k ℓ (Fin t)) (i : Fin t) {a : Fin k}
    {c : Fin (2 * ℓ)} (hx : x i = Sum.inl a) (hy : y i = Sum.inr c) :
    superForm t x y = 0 := by
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  rw [hx, hy]
  rfl

/-- **And an odd leg against an even one.** -/
theorem superForm_eq_zero_of_right_left {k ℓ t : ℕ}
    (x y : GenBoundaryState k ℓ (Fin t)) (i : Fin t)
    {c : Fin (2 * ℓ)} {a : Fin k} (hx : x i = Sum.inr c)
    (hy : y i = Sum.inl a) : superForm t x y = 0 := by
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  rw [hx, hy]
  rfl

/-- A colour that is not odd is even. -/
theorem exists_left_of_not_right {k ℓ : ℕ}
    {v : Fin k ⊕ Fin (2 * ℓ)} (h : ¬ ∃ c, v = Sum.inr c) :
    ∃ a, v = Sum.inl a := by
  rcases v with a | c
  · exact ⟨a, rfl⟩
  · exact absurd ⟨c, rfl⟩ h

/-! ### The form is diagonal in the partner pairing

RS21 pairs two fragments' tensors coordinate by coordinate and
observes that the pairing vanishes unless the two coordinates agree
— the even colours outright, and the odd ones because the two
orientations are opposite at a used leg, so the same colour appears
against its dual basis vector.

Written in one basis the second coordinate is not equal to the
first but *dual* to it: the same colour on an even leg, the partner
colour on an odd one.  So the form has exactly one nonzero
coordinate for each state, and the double sum over coordinates
collapses to a single one.
-/

/-- **The dual of one leg's colour**: itself on an even colour, the
partner on an odd one. -/
noncomputable def dualLeg {k ℓ : ℕ} :
    (Fin k ⊕ Fin (2 * ℓ)) → (Fin k ⊕ Fin (2 * ℓ))
  | Sum.inl a => Sum.inl a
  | Sum.inr c => Sum.inr (oddPartner ℓ c)

/-- **The dual state**: the dual colour at every leg. -/
noncomputable def dualState {k ℓ : ℕ} {α : Type}
    (x : GenBoundaryState k ℓ α) : GenBoundaryState k ℓ α :=
  fun i => dualLeg (x i)

/-- **One leg's form vanishes off the dual colour.** -/
theorem superLeg_eq_zero_of_ne_dualLeg {k ℓ : ℕ}
    (u v : Fin k ⊕ Fin (2 * ℓ)) (h : v ≠ dualLeg u) :
    superLeg u v = 0 := by
  rcases u with a | c
  · rcases v with b | d
    · exact if_neg (fun hb => h (by rw [hb]; rfl))
    · rfl
  · rcases v with b | d
    · rfl
    · show symplecticJ ℓ c d = 0
      have hd : d ≠ oddPartner ℓ c := fun hx => h (by rw [hx]; rfl)
      have hc := c.isLt
      have hd' := d.isLt
      have hpart := eq_oddPartner_iff c d
      unfold symplecticJ
      by_cases hlt : c.val < ℓ
      · rw [if_pos hlt] at hpart
        rw [if_neg (fun hx => hd (hpart.mpr hx)),
          if_neg (by omega)]
      · rw [if_neg hlt] at hpart
        rw [if_neg (by omega),
          if_neg (fun hx => hd (hpart.mpr (by omega)))]

/-- **The form vanishes off the dual state.** -/
theorem superForm_eq_zero_of_ne_dualState {k ℓ t : ℕ}
    (x y : GenBoundaryState k ℓ (Fin t)) (h : y ≠ dualState x) :
    superForm t x y = 0 := by
  obtain ⟨i, hi⟩ : ∃ i, y i ≠ dualLeg (x i) := by
    by_contra hx
    push Not at hx
    exact h (funext hx)
  exact Finset.prod_eq_zero (Finset.mem_univ i)
    (superLeg_eq_zero_of_ne_dualLeg (x i) (y i) hi)

/-- **One leg's form against its own dual**: `1` on an even colour,
and on an odd one the negated dual sign — RS21's `⟨f_c, g_c⟩`. -/
noncomputable def legSelf {k ℓ : ℕ} :
    (Fin k ⊕ Fin (2 * ℓ)) → ℂ
  | Sum.inl _ => 1
  | Sum.inr c => -dualSign ℓ c

/-- The one-leg form at the dual colour. -/
theorem superLeg_dualLeg {k ℓ : ℕ} (u : Fin k ⊕ Fin (2 * ℓ)) :
    superLeg u (dualLeg u) = legSelf u := by
  rcases u with a | c
  · exact if_pos rfl
  · show symplecticJ ℓ c (oddPartner ℓ c) = -dualSign ℓ c
    have hfg := superLeg_f_g ℓ c
    have hsq := dualSign_sq ℓ c
    linear_combination dualSign ℓ c * hfg
      - symplecticJ ℓ c (oddPartner ℓ c) * hsq

/-- **The form at the dual state** is the product of the legs' own
values. -/
theorem superForm_dualState {k ℓ t : ℕ}
    (x : GenBoundaryState k ℓ (Fin t)) :
    superForm t x (dualState x) = ∏ i : Fin t, legSelf (x i) :=
  Finset.prod_congr rfl (fun i _ => superLeg_dualLeg (x i))

/-- **The Gram double sum collapses.**  Only the dual coordinate
contributes, so a pairing written against the form is a single sum
over boundary states. -/
theorem sum_sum_superForm {k ℓ t : ℕ}
    (T₁ T₂ : GenBoundaryState k ℓ (Fin t) → ℂ) :
    (∑ x : GenBoundaryState k ℓ (Fin t),
        ∑ y : GenBoundaryState k ℓ (Fin t),
          superForm t x y * T₁ x * T₂ y)
      = ∑ x : GenBoundaryState k ℓ (Fin t),
          (∏ i : Fin t, legSelf (x i)) * T₁ x * T₂ (dualState x) := by
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.sum_eq_single (dualState x)]
  · rw [superForm_dualState]
  · intro y _ hy
    rw [superForm_eq_zero_of_ne_dualState x y hy, zero_mul,
      zero_mul]
  · intro hx
    exact absurd (Finset.mem_univ _) hx

/-! ### The leg bracket

At a used leg the two fragments each contribute a dual-basis weight
and the form contributes its entry.  Their product is RS21's leg
value: `-1` where the first fragment's arc leaves the leg and `1`
where it enters — provided the two arcs point oppositely, which is
what the Eulerian condition on the union of the two matchings says.
-/

/-- **The leg bracket on an odd leg** — RS21's `⟨f_c, g_c⟩ = -1` and
`⟨g_c, f_c⟩ = 1`, read in the coordinates the tensor uses. -/
theorem legBracket_odd {k ℓ : ℕ} (u : Fin (2 * ℓ)) (t₁ : Bool) :
    ((if t₁ then dualSign ℓ u else 1)
        * (if !t₁ then dualSign ℓ (oddPartner ℓ u) else 1))
      * (superLeg (k := k) (ℓ := ℓ) (Sum.inr u)
          (Sum.inr (oddPartner ℓ u)))
      = if t₁ then -1 else 1 := by
  have hJ : (superLeg (k := k) (ℓ := ℓ) (Sum.inr u)
      (Sum.inr (oddPartner ℓ u))) = -dualSign ℓ u := by
    have hfg := superLeg_f_g ℓ u
    have hsq := dualSign_sq ℓ u
    show symplecticJ ℓ u (oddPartner ℓ u) = -dualSign ℓ u
    linear_combination dualSign ℓ u * hfg
      - symplecticJ ℓ u (oddPartner ℓ u) * hsq
  have hsq := dualSign_sq ℓ u
  have hpart := dualSign_oddPartner ℓ u
  cases t₁
  · rw [if_neg (by simp), Bool.not_false, if_pos rfl, hJ, hpart,
      if_neg (by simp)]
    linear_combination hsq
  · rw [if_pos rfl, Bool.not_true, if_neg (by simp), hJ,
      if_pos rfl]
    linear_combination -hsq

/-- **The leg bracket on an even leg** is trivial. -/
theorem legBracket_even {k ℓ : ℕ} (a : Fin k) :
    (superLeg (k := k) (ℓ := ℓ) (Sum.inl a) (Sum.inl a)) = 1 :=
  if_pos rfl

/-! ### The legs, multiplied out

Each fragment's dual-basis weight is a product over the legs, so the
whole leg contribution is a product of brackets.  With the two
matchings' arcs opposite at every leg, each bracket is `-1` exactly
where the first fragment's arc leaves, so the product is `(-1)` to
the number of such legs — half the used ones, which is RS21's
count.
-/

/-- One leg's dual-basis weight, as it occurs in `dualWeight`. -/
noncomputable def legWeight {k ℓ : ℕ} (b : Bool)
    (v : Fin k ⊕ Fin (2 * ℓ)) : ℂ :=
  match v with
  | Sum.inl _ => 1
  | Sum.inr u => if b then dualSign ℓ u else 1

/-- **The leg weights only see the used legs.**  At an even colour
the weight is one whichever way the arc points, so two direction
assignments agreeing on the odd legs give the same product.  This is
what lets the two fragments' directions be compared only where both
subsets are used. -/
theorem prod_legWeight_congr {k ℓ t : ℕ} (b b' : Fin t → Bool)
    (x : GenBoundaryState k ℓ (Fin t))
    (h : ∀ i, (∃ c, x i = Sum.inr c) → b i = b' i) :
    (∏ i : Fin t, legWeight (b i) (x i))
      = ∏ i : Fin t, legWeight (b' i) (x i) := by
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rcases hx : x i with a | c
  · rfl
  · rw [h i ⟨c, hx⟩]

/-- **The bracket at one leg.** -/
theorem legWeight_mul {k ℓ : ℕ} (b : Bool)
    (v : Fin k ⊕ Fin (2 * ℓ)) :
    legWeight b v * legWeight (!b) (dualLeg v) * superLeg v (dualLeg v)
      = if (∃ c, v = Sum.inr c) ∧ b = true then -1 else 1 := by
  rcases v with a | u
  · rw [if_neg (by
      rintro ⟨⟨c, hcc⟩, -⟩
      exact Sum.inl_ne_inr hcc)]
    show (1 : ℂ) * 1 * superLeg (Sum.inl a) (Sum.inl a) = 1
    rw [legBracket_even a]
    ring
  · have hb := legBracket_odd (k := k) u b
    by_cases hbt : b = true
    · rw [if_pos ⟨⟨u, rfl⟩, hbt⟩, hbt]
      rw [hbt] at hb
      simpa [legWeight, dualLeg] using hb
    · have hbf : b = false := by
        cases b
        · rfl
        · exact absurd rfl hbt
      rw [if_neg (fun hc => hbt hc.2), hbf]
      rw [hbf] at hb
      simpa [legWeight, dualLeg] using hb

/-! ### Undoing the dual basis is a bijection of states

Summing a tensor's coordinates and summing the partition function's
states are the same sum: the dual basis relabels the colour at the
legs whose arc leaves, and that relabelling is an involution.
-/

/-- The dual colour is an involution. -/
theorem dualLeg_involutive {k ℓ : ℕ} :
    Function.Involutive (dualLeg (k := k) (ℓ := ℓ)) := by
  rintro (a | c)
  · rfl
  · show Sum.inr (oddPartner ℓ (oddPartner ℓ c)) = Sum.inr c
    rw [oddPartner_invol]

/-- **Undoing the dual basis at the legs whose arc leaves.** -/
noncomputable def untwistState {k ℓ t : ℕ} (b : Fin t → Bool)
    (x : GenBoundaryState k ℓ (Fin t)) :
    GenBoundaryState k ℓ (Fin t) :=
  fun i => if b i then dualLeg (x i) else x i

/-- Untwisting a state at a fixed sign pattern is an involution. -/
theorem untwistState_involutive {k ℓ t : ℕ} (b : Fin t → Bool) :
    Function.Involutive (untwistState (k := k) (ℓ := ℓ) b) := by
  intro x
  funext i
  show (if b i then dualLeg (untwistState b x i)
      else untwistState b x i) = x i
  by_cases hb : b i = true
  · rw [if_pos hb]
    show dualLeg (if b i then dualLeg (x i) else x i) = x i
    rw [if_pos hb, dualLeg_involutive (x i)]
  · rw [if_neg hb]
    show (if b i then dualLeg (x i) else x i) = x i
    rw [if_neg hb]

/-- **The two sums agree.** -/
theorem sum_untwistState {k ℓ t : ℕ} (b : Fin t → Bool)
    (V : GenBoundaryState k ℓ (Fin t) → ℂ) :
    (∑ x : GenBoundaryState k ℓ (Fin t), V (untwistState b x))
      = ∑ st : GenBoundaryState k ℓ (Fin t), V st :=
  Fintype.sum_equiv
    ((untwistState_involutive (k := k) (ℓ := ℓ) b).toPerm) _ _
    (fun _ => rfl)

/-- The dual state colours the same legs oddly, pointwise. -/
theorem dualState_isInr {k ℓ t : ℕ}
    (x : GenBoundaryState k ℓ (Fin t)) (i : Fin t) :
    (∃ c, dualState x i = Sum.inr c) ↔ (∃ c, x i = Sum.inr c) := by
  show (∃ c, dualLeg (x i) = Sum.inr c) ↔ (∃ c, x i = Sum.inr c)
  rcases x i with a | c
  · constructor
    · rintro ⟨d, hd⟩
      exact (Sum.inl_ne_inr hd).elim
    · rintro ⟨d, hd⟩
      exact (Sum.inl_ne_inr hd).elim
  · exact ⟨fun _ => ⟨c, rfl⟩, fun _ => ⟨oddPartner ℓ c, rfl⟩⟩

/-- **RS21's `χ = χ′`, needing the directions opposite only where
both subsets are used.**  At an even leg the dual colour is the
colour, so the two sides agree there whatever the directions say. -/
theorem untwistState_dualState' {k ℓ t : ℕ} (b₁ b₂ : Fin t → Bool)
    (x : GenBoundaryState k ℓ (Fin t))
    (hb : ∀ i, (∃ c, x i = Sum.inr c) → b₂ i = !(b₁ i)) :
    untwistState b₂ (dualState x) = untwistState b₁ x := by
  funext i
  show (if b₂ i then dualLeg (dualLeg (x i)) else dualLeg (x i))
    = if b₁ i then dualLeg (x i) else x i
  rcases hx : x i with a | c
  · have he : dualLeg (Sum.inl a : Fin k ⊕ Fin (2 * ℓ))
        = Sum.inl a := rfl
    rw [he, he]
    by_cases h₂ : b₂ i = true
    · rw [if_pos h₂]
      by_cases h₁ : b₁ i = true
      · rw [if_pos h₁]
      · rw [if_neg h₁]
    · rw [if_neg h₂]
      by_cases h₁ : b₁ i = true
      · rw [if_pos h₁]
      · rw [if_neg h₁]
  · rw [hb i ⟨c, hx⟩]
    by_cases h₁ : b₁ i = true
    · rw [h₁, Bool.not_true, if_neg (by simp), if_pos rfl]
    · have hf : b₁ i = false := by
        cases hbb : b₁ i
        · rfl
        · exact absurd hbb h₁
      rw [hf, Bool.not_false, if_pos rfl, if_neg (by simp)]
      exact dualLeg_involutive _

/-! ### Contracting one leg

Summing a fragment tensor's coordinate at a used leg against the
form is the same as summing the partition function's own colour
there.  The two differ by the partner relabelling the dual basis
performs, which is a bijection of the odd colours, and by RS21's leg
value.
-/

/-- **The legs' product**: `(-1)` to the number of legs at which the
first fragment's arc leaves. -/
theorem prod_legBracket {k ℓ t : ℕ}
    (x : GenBoundaryState k ℓ (Fin t)) (b : Fin t → Bool) :
    ((∏ i : Fin t, legWeight (b i) (x i))
        * (∏ i : Fin t, legWeight (!(b i)) (dualLeg (x i))))
      * superForm t x (dualState x)
      = (-1 : ℂ) ^ (Finset.univ.filter
          (fun i => (∃ c, x i = Sum.inr c) ∧ b i = true)).card := by
  classical
  rw [superForm, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  rw [Finset.prod_congr rfl (fun i _ => by
    show legWeight (b i) (x i) * legWeight (!(b i)) (dualLeg (x i))
        * superLeg (x i) (dualState x i) = _
    exact legWeight_mul (b i) (x i))]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one,
    mul_one]

/-- The dual state colours the same legs oddly. -/
theorem oddCount_dualState {k ℓ t : ℕ}
    (x : GenBoundaryState k ℓ (Fin t)) :
    oddCount (dualState x) = oddCount x := by
  classical
  unfold oddCount
  refine congrArg Finset.card (Finset.filter_congr (fun i _ => ?_))
  constructor
  · rintro ⟨c, hc⟩
    rcases hx : x i with a | u
    · exact absurd (hx ▸ hc : dualLeg (Sum.inl a) = Sum.inr c)
        (fun h => Sum.inl_ne_inr h)
    · exact ⟨u, rfl⟩
  · rintro ⟨u, hu⟩
    exact ⟨oddPartner ℓ u, by
      show dualLeg (x i) = Sum.inr (oddPartner ℓ u)
      rw [hu]
      rfl⟩

/-- **RS21's cancellation, assembled**: the two fragments' fourth
roots and the legs' product cancel, provided the first fragment's
arc leaves at half the used legs — which is what the Eulerian
condition on the union gives. -/
theorem legs_cancel_twists {k ℓ t : ℕ}
    (x : GenBoundaryState k ℓ (Fin t)) (b : Fin t → Bool)
    (hcount : oddCount x = 2 * (Finset.univ.filter
      (fun i => (∃ c, x i = Sum.inr c) ∧ b i = true)).card) :
    (stateTwist x * stateTwist (dualState x))
        * (((∏ i : Fin t, legWeight (b i) (x i))
            * (∏ i : Fin t, legWeight (!(b i)) (dualLeg (x i))))
          * superForm t x (dualState x))
      = 1 := by
  rw [prod_legBracket x b]
  exact stateTwist_mul_stateTwist_mul_half (oddCount_dualState x).symm
    hcount

/-! ### The legs contracted, all at once

Putting the two together: the bracket product is `(-1)` to the
number of legs the first fragment's arc leaves, and undoing the dual
basis is a bijection of states.  So the Gram sum in the tensor's
coordinates is the partition function's sum over states, times
RS21's leg sign — provided the tensors are supported where the used
legs are the same, which is what (16) already says.
-/

/-- **RS21's step 5, complete.**  With the two fragments' fourth
roots included, the Gram sum in the tensor's coordinates is the
partition function's own sum over states, with no residual sign:
the legs' `(-1)` per entering arc is exactly cancelled by the
roots. -/
theorem sum_legBracket_with_twists {k ℓ t : ℕ} (b : Fin t → Bool)
    (V : GenBoundaryState k ℓ (Fin t) → ℂ) (m : ℕ)
    (hodd : ∀ x : GenBoundaryState k ℓ (Fin t),
      V (untwistState b x) ≠ 0 →
      (Finset.univ.filter (fun i =>
        (∃ c, x i = Sum.inr c) ∧ b i = true)).card = m)
    (hcnt : ∀ x : GenBoundaryState k ℓ (Fin t),
      V (untwistState b x) ≠ 0 → oddCount x = 2 * m) :
    (∑ x : GenBoundaryState k ℓ (Fin t),
        ((stateTwist x * stateTwist (dualState x))
          * (((∏ i : Fin t, legWeight (b i) (x i))
              * (∏ i : Fin t, legWeight (!(b i)) (dualLeg (x i))))
            * superForm t x (dualState x)))
          * V (untwistState b x))
      = ∑ st : GenBoundaryState k ℓ (Fin t), V st := by
  classical
  have hterm : ∀ x : GenBoundaryState k ℓ (Fin t),
      ((stateTwist x * stateTwist (dualState x))
        * (((∏ i : Fin t, legWeight (b i) (x i))
            * (∏ i : Fin t, legWeight (!(b i)) (dualLeg (x i))))
          * superForm t x (dualState x)))
        * V (untwistState b x)
      = V (untwistState b x) := by
    intro x
    by_cases hV : V (untwistState b x) = 0
    · rw [hV, mul_zero]
    · rw [legs_cancel_twists x b (by rw [hcnt x hV, hodd x hV]),
        one_mul]
  rw [Finset.sum_congr rfl (fun x _ => hterm x), sum_untwistState b V]

/-- **RS21's step 5, with the second fragment's own directions.**
The two fragments each carry their own arc directions; they need
only be opposite at the legs both subsets use, since an even leg's
weight is one either way. -/
theorem sum_legBracket_with_twists' {k ℓ t : ℕ}
    (b₁ b₂ : Fin t → Bool)
    (V : GenBoundaryState k ℓ (Fin t) → ℂ) (m : ℕ)
    (hodd : ∀ x : GenBoundaryState k ℓ (Fin t),
      V (untwistState b₁ x) ≠ 0 →
      (Finset.univ.filter (fun i =>
        (∃ c, x i = Sum.inr c) ∧ b₁ i = true)).card = m)
    (hcnt : ∀ x : GenBoundaryState k ℓ (Fin t),
      V (untwistState b₁ x) ≠ 0 → oddCount x = 2 * m)
    (hb : ∀ x : GenBoundaryState k ℓ (Fin t),
      V (untwistState b₁ x) ≠ 0 →
      ∀ i, (∃ c, x i = Sum.inr c) → b₂ i = !(b₁ i)) :
    (∑ x : GenBoundaryState k ℓ (Fin t),
        ((stateTwist x * stateTwist (dualState x))
          * (((∏ i : Fin t, legWeight (b₁ i) (x i))
              * (∏ i : Fin t, legWeight (b₂ i) (dualLeg (x i))))
            * superForm t x (dualState x)))
          * V (untwistState b₁ x))
      = ∑ st : GenBoundaryState k ℓ (Fin t), V st := by
  classical
  have hodd' : ∀ (x : GenBoundaryState k ℓ (Fin t)) (i : Fin t),
      (∃ c, dualState x i = Sum.inr c) ↔ (∃ c, x i = Sum.inr c) := by
    intro x i
    show (∃ c, dualLeg (x i) = Sum.inr c) ↔ (∃ c, x i = Sum.inr c)
    rcases x i with a | c
    · constructor
      · rintro ⟨d, hd⟩
        exact (Sum.inl_ne_inr hd).elim
      · rintro ⟨d, hd⟩
        exact (Sum.inl_ne_inr hd).elim
    · exact ⟨fun _ => ⟨c, rfl⟩, fun _ => ⟨oddPartner ℓ c, rfl⟩⟩
  refine (Finset.sum_congr rfl (fun x _ => ?_)).trans
    (sum_legBracket_with_twists b₁ V m hodd hcnt)
  by_cases hV : V (untwistState b₁ x) = 0
  · rw [hV, mul_zero, mul_zero]
  · refine congrArg (fun z : ℂ => z * V (untwistState b₁ x)) ?_
    refine congrArg (fun z : ℂ =>
      (stateTwist x * stateTwist (dualState x))
        * (((∏ i : Fin t, legWeight (b₁ i) (x i)) * z)
          * superForm t x (dualState x))) ?_
    exact prod_legWeight_congr b₂ (fun i => !(b₁ i)) (dualState x)
      (fun i hi => hb x hV i ((hodd' x i).mp hi))

end RS
