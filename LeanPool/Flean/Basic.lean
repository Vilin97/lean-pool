/-
Copyright (c) 2026 Joseph McKinsey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph McKinsey
-/
import LeanPool.Flean.FloatCfg
import LeanPool.Flean.Subnorm
import LeanPool.Flean.FloatRep
import LeanPool.Flean.Rounding

/-!
# Floating-Point Numbers

This module assembles the full `Flean.Float` type (combining normal and
subnormal representations with infinities and NaN), the conversions `toFloat`
and `toRat` between rationals and floats, and the round-trip and rounding-error
correctness results such as `to_float_to_rat`.
-/

variable {C : FloatCfg}

/-- Round a rational to a subnormal representation using the mode in scope. -/
def roundsub [R : Rounding] (q : ℚ) : SubnormRep C :=
  subnormalRound (roundFunction R) q

lemma subnormal_roundsub_valid [R : Rounding] :
  ValidSubnormalRounding (roundsub : ℚ → SubnormRep C) :=
  subnormal_round_valid (roundFunction R)

lemma subnormal_roundsub_coe [R : Rounding] (s : SubnormRep C) (h : s.nonzero) :
  roundsub (subnormalToQ s) = s :=
  subnormal_round_coe (roundFunction R) h

/-- A floating-point number of the format `C`: a signed infinity, `NaN`, a valid
normal representation, or a valid subnormal representation. -/
inductive Flean.Float (C : FloatCfg) where
  /-- A signed infinity (`true` for negative). -/
  | inf : Bool → Float C
  /-- Not-a-number. -/
  | nan : Float C
  /-- A normal float, given by a representation with valid exponent and mantissa. -/
  | normal : (f : FloatRep C) → f.validE → f.validM → Float C
  /-- A subnormal float, given by a representation with mantissa below precision. -/
  | subnormal : (sm : SubnormRep C) → sm.m < C.prec → Float C


/-- Round a rational to the nearest representable float under the mode in scope. -/
def toFloat [R : Rounding] (q : ℚ) : Flean.Float C :=
  if q_nonneg : q = 0 then
    Flean.Float.subnormal ⟨false, 0⟩ C.prec_pos
  else if h : Int.log 2 |q| < C.emin then
    let sp := roundsub q
    if h_eq_prec : sp.2 = C.prec then by
      refine Flean.Float.normal ⟨q < 0, C.emin, 0⟩ ?_ ?_
      <;> simp only [FloatRep.validE, FloatRep.validM]
      · refine ⟨by linarith, by linarith [C.emin_lt_emax]⟩
      linarith [C.prec_pos]
    else by
      refine Flean.Float.subnormal ⟨sp.1, sp.2⟩ ?_
      · refine lt_of_le_of_ne ?_ h_eq_prec
        apply subnormal_roundsub_valid q q_nonneg
        exact h
  else match sem_def : roundRep q with
  | (⟨s, e, m⟩ : FloatRep C) => if h': e > C.emax then
      Flean.Float.inf (q < 0)
    else by
      refine Flean.Float.normal ⟨s, e, m⟩ ?_ ?_
      <;> simp only [FloatRep.validE, FloatRep.validM]
      · refine ⟨?_, by linarith [h', C.emin_lt_emax]⟩
        have := round_min_e (r := roundFunction R) (C := C) q_nonneg
        rw [<-roundRep] at this
        rw [sem_def] at this
        linarith
      have := round_valid_m (C := C) q q_nonneg
      rw [sem_def] at this
      exact this

/-- The exact rational value of a float (`0` for infinities and `NaN`). -/
def toRat : Flean.Float C → ℚ
| Flean.Float.inf _ => 0
| Flean.Float.nan => 0
| Flean.Float.normal f _ _ => coeQ f
| Flean.Float.subnormal sm _ => subnormalToQ sm

/-- Whether a float is finite (not an infinity or `NaN`). -/
def Flean.Float.IsFinite : Flean.Float C → Prop
| Flean.Float.inf _ => false
| Flean.Float.nan => false
| _ => true

/-- Whether a float is (a) zero. -/
def Flean.Float.IsZero : Flean.Float C → Prop
| Flean.Float.subnormal ⟨_, 0⟩ _ => true
| _ => false

lemma subnorm_eq_0_iff_to_q (sm : SubnormRep C) :
  subnormalToQ sm = 0 ↔ sm.m = 0 := by
  symm
  constructor
  · intro h
    rw [subnormalToQ, h]
    simp
  contrapose!
  intro h
  have : sm.m > 0 := Nat.zero_lt_of_ne_zero h
  rw [subnormalToQ]
  have hprec := C.prec_pos
  cases hs : sm.s
  · simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
    positivity
  · simp only [↓reduceIte, neg_mul, one_mul, neg_ne_zero]
    positivity


lemma is_zero_iff_subnormal_to_q (sm : SubnormRep C) (h : sm.m < C.prec) :
  subnormalToQ sm = 0 ↔ (Flean.Float.subnormal sm h).IsZero := by
  rw [subnorm_eq_0_iff_to_q]
  constructor
  · intro h'
    simp only [Flean.Float.IsZero, Bool.false_eq_true]
    rcases sm with ⟨s, m⟩
    split
    · simp at *
    simp only [C.prec_pos, Flean.Float.subnormal.injEq, SubnormRep.mk.injEq, imp_false,
      not_and, forall_const, forall_eq'] at *
    contradiction
  intro h'
  rcases sm with ⟨s, m⟩
  simp only [Flean.Float.IsZero] at h'
  split at h'
  next s m h_again sm_def =>
    rw [Flean.Float.subnormal.injEq] at sm_def
    rw [sm_def]
  simp at h'

lemma subnormal_range (f : SubnormRep C) (vm : f.m < C.prec) (ne_zero : f.nonzero) :
  Int.log 2 |subnormalToQ f| < C.emin := by
  rw [subnormalToQ]
  rw [SubnormRep.nonzero] at ne_zero
  rcases f with ⟨s, m⟩
  cases s <;> {
    simp only [Bool.false_eq_true, ↓reduceIte, neg_mul, one_mul, abs_neg]
    have man_ge_0 : 0 < (m : ℚ) / C.prec := by
      have := C.prec_pos
      positivity
    have man_lt_1 : (m : ℚ) / C.prec < 1 := by
      rw [div_lt_one (by norm_cast; exact C.prec_pos)]
      norm_cast
    exact log_zero_to_one_lt ((m : ℚ) / C.prec) C.emin man_ge_0 man_lt_1
  }

/-- The largest finite float of the format `C`. -/
def maxFloat (C : FloatCfg) : Flean.Float C := by
  refine Flean.Float.normal (maxFloatRep C) ?_ ?_
  · simp [maxFloatRep, FloatRep.validE, le_of_lt C.emin_lt_emax]
  simp [maxFloatRep, FloatRep.validM, C.prec_pos]

lemma to_rat_max_float :
  toRat (maxFloat C) = maxFloatQ C := by
  simp only [toRat, maxFloat, coe_q_max_float_rep]

lemma log_lt_emax_of_max_float {q : ℚ} (q_nonneg : q ≠ 0) (h : |q| ≤ maxFloatQ C) :
  Int.log 2 |q| ≤ C.emax := by
  suffices Int.log 2 |q| < C.emax + 1 by linarith
  rw [<-Int.lt_zpow_iff_log_lt (by norm_num) (by positivity)]
  unfold maxFloatQ at h
  apply lt_of_le_of_lt h
  rw [zpow_add₀ (by norm_num)]
  rw [mul_comm]
  apply mul_lt_mul' ?_ ?_ (by linarith [max_mantissa_q C]) (by positivity)
  · rfl
  linarith [max_mantissa_q C]


lemma float_range (f : Flean.Float C) :
  |toRat f| ≤ maxFloatQ C := by
  unfold toRat
  unfold maxFloatQ
  have : (1 : ℚ) / C.prec ≤ 1 := by
    rw [one_div_le]
    · simp only [ne_eq, one_ne_zero, not_false_eq_true, div_self, Nat.one_le_cast]
      exact C.prec_pos
    · exact Nat.cast_pos'.mpr C.prec_pos
    norm_num
  have : 0 < (2 - (1 : ℚ) / C.prec) := by linarith
  have := C.prec_pos
  rcases f with _ | _ | ⟨f, ve, vm⟩ | ⟨sm, vm⟩
  · simp only [abs_zero]; positivity
  · positivity
  · dsimp
    rw [coeQ]
    cases f.s
    <;> {
      simp only [Bool.false_eq_true, ↓reduceIte, one_mul, ge_iff_le,
      neg_mul, abs_neg
      ]
      apply normal_range'
      · exact vm
      exact ve.2
    }
  dsimp
  apply le_of_lt
  calc
    |subnormalToQ sm| < (2 : ℚ)^C.emin := by
      by_cases h : 0 < |subnormalToQ sm|
      · suffices Int.log 2 |subnormalToQ sm| < C.emin by
          rw [<-Int.lt_zpow_iff_log_lt] at this
          · norm_cast at this
          · norm_num
          exact h
        apply subnormal_range
        · exact vm
        contrapose h
        simp only [abs_pos, ne_eq, Decidable.not_not]
        simp only [SubnormRep.nonzero, ne_eq, Decidable.not_not] at h
        exact (subnorm_eq_0_iff_to_q sm).mpr h
      simp only [abs_pos, ne_eq, Decidable.not_not] at h
      rw [h]
      positivity
    _ < (2 - 1 / ↑C.prec) * 2 ^ C.emax := by
      rw [<-one_mul (2 ^ _)]
      apply mul_lt_mul' ?_ ?_ (by positivity) (by positivity)
      · linarith
      apply zpow_lt_zpow_right₀ (by norm_num) C.emin_lt_emax


lemma to_float_to_rat [R : Rounding] (f : Flean.Float C) (finite : f.IsFinite)
    (nonzero : ¬f.IsZero) :
  toFloat (toRat f) = f := by
  simp only [Flean.Float.IsFinite, Bool.false_eq_true] at finite
  rcases f with _ | _ | ⟨f, ve, vm⟩ | ⟨sm, vm⟩
  <;> simp only at finite nonzero
  · have : coeQ f ≠ 0 := by
      rcases f with ⟨s, e, m⟩
      cases s
      · linarith [coe_q_false_pos (C := C) (e := e) (m := m)]
      linarith [coe_q_true_neg (C := C) (e := e) (m := m)]
    simp only [toRat]
    unfold toFloat
    split_ifs
    · contradiction
    · linarith [(normal_range f ve vm).1]
    have : roundRep (coeQ f) = f := round_rep_coe f vm
    dsimp
    split_ifs
    · rw [this] at *
      linarith [ve.2]
    simp [this]
  have sm_nonzero : sm.m ≠ 0 := by
    rw [<-is_zero_iff_subnormal_to_q _ vm] at nonzero
    rw [subnorm_eq_0_iff_to_q] at nonzero
    exact nonzero
  have := subnormal_range sm vm sm_nonzero
  simp only [toRat]
  unfold toFloat
  have snormal_eq := subnormal_roundsub_coe sm sm_nonzero
  if mzero : subnormalToQ sm = 0 then
    rw [is_zero_iff_subnormal_to_q _ vm] at mzero
    contradiction
  else
    if h_eq_pres : sm.2 = C.prec then
      rw [<-snormal_eq] at h_eq_pres
      simp only [mzero, this, h_eq_pres, ↓reduceDIte, reduceCtorEq]
      rw [snormal_eq] at h_eq_pres
      linarith
    else
      rw [<-snormal_eq] at h_eq_pres
      simp only [mzero, this, h_eq_pres, ↓reduceDIte, Flean.Float.subnormal.injEq]
      rw [snormal_eq]


/-
I would like to prove that rounding preserves order
for finite values
First we split into 4 cases:
- q1 and q2 are both normal
- q1 and q2 are both subnormal
- q1 rounds to a subnormal number and q2 to a normal
- vice versa

We've already proved the first two cases.
For the third case, we can use
the fact that the rounding exactly overlaps
at the subnormal / normal boundary in a
transitive ordering proof.

Of course, this requires it's own case work
to identify that boundary, but it only
depends on the sign of the normal number.

I should also note that we are really splitting
the rational numbers not the floats.
So we need to know how rounding behaves
on different sets. i.e. which sets of ℚ
give us something equivalent to subnormal rounding
or normal rounding (conditioned on rounding giving us finite).

Finally, we need to prove that rounding
preserves the overlapping boundary of those sets.
-/

-- Alternative
-- |q| ≤ 2^C.emin → toRat (toFloat q : Flean.Float C) = subnormalToQ (roundsub q)
-- 2^C.emin ≤ |q| → toRat (toFloat q : Flean.Float C) = coeQ (roundRep q)
lemma splitIsFinite [R : Rounding] {q : ℚ}
  (h : (toFloat q : Flean.Float C).IsFinite) :
  ((|q| ≤ 2^C.emin) ∧
    toRat (toFloat q : Flean.Float C)
  = subnormalToQ (roundsub (C := C) q))
  ∨ (2^C.emin ≤ |q| ∧ toRat (toFloat q : Flean.Float C) = coeQ (roundRep (C := C) q)) := by
  set f := toFloat q with f_def
  unfold toFloat at f_def
  split_ifs at f_def with i1 i2
  · left
    constructor
    · rw [i1, abs_zero]
      positivity
    rw [f_def, i1, roundsub, roundsub_zero]
    simp [toRat, subnormalToQ]
  · left
    constructor
    · apply le_of_lt
      exact (Int.lt_zpow_iff_log_lt (b := 2) (by norm_num) (by positivity)).2 i2
    dsimp at f_def
    split_ifs at f_def with h'
    · --simp only [i1, ↓reduceDIte, i2, h']
      rw [f_def, toRat, coeQ, subnormalToQ, h']
      rw [roundsub, subnormalRound]
      dsimp
      rw [mul_assoc, mul_assoc]
      congr 1
      rw [div_self]
      · simp
      norm_cast
      exact ne_of_gt C.prec_pos
    rw [f_def, toRat]
  match sem_def : roundRep q with
  | { s := s, e := e, m := m } => {
    dsimp at f_def
    simp_rw [sem_def] at f_def
    split_ifs at f_def with i3
    · exfalso
      rw [f_def] at h
      simp [Flean.Float.IsFinite] at h
    right
    constructor
    · apply (Int.zpow_le_iff_le_log (b := 2) (by norm_num) (by positivity)).2
      exact not_lt.mp i2
    rw [f_def, toRat]
  }

lemma subnormal_to_q_emin :
  subnormalToQ (C := C) ⟨false, C.prec⟩ = 2^C.emin := by
  rw [subnormalToQ, div_self]
  · simp
  exact_mod_cast ne_of_gt C.prec_pos

lemma subnormal_to_q_neg_emin :
  subnormalToQ (C := C) ⟨true, C.prec⟩ = -2^C.emin := by
  rw [<-subnormal_to_q_emin]
  simp [subnormalToQ]

lemma coe_q_emin : coeQ (C := C) ⟨false, C.emin, 0⟩ = 2^C.emin := by
  rw [coeQ]
  simp

lemma coe_q_neg_emin : coeQ (C := C) ⟨true, C.emin, 0⟩ = -2^C.emin := by
  rw [<-coe_q_emin]
  simp [coeQ]

lemma roundsub_emin [R : Rounding] : roundsub (C := C) (2^C.emin) = ⟨false, C.prec⟩ := by
  rw [roundsub, <-subnormal_to_q_emin, subnormal_round_coe]
  simp [SubnormRep.nonzero, ne_of_gt, C.prec_pos]

lemma roundsub_neg_emin [R : Rounding] : roundsub (C := C) (-2^C.emin) = ⟨true, C.prec⟩ := by
  rw [roundsub, <-subnormal_to_q_neg_emin, subnormal_round_coe]
  simp [SubnormRep.nonzero, ne_of_gt, C.prec_pos]

lemma roundrep_emin [R : Rounding] : roundRep (C := C) (2^C.emin) = ⟨false, C.emin, 0⟩ := by
  rw [<-coe_q_emin]
  apply round_rep_coe
  simp [FloatRep.validM, C.prec_pos]

lemma roundrep_neg_emin [R : Rounding] : roundRep (C := C) (-2^C.emin) = ⟨true, C.emin, 0⟩ := by
  rw [<-coe_q_neg_emin]
  apply round_rep_coe
  simp [FloatRep.validM, C.prec_pos]

/-- Negate a float by flipping the sign of each case. -/
def Flean.Float.neg : Flean.Float C → Flean.Float C
| Flean.Float.inf s => Flean.Float.inf (¬s)
| Flean.Float.nan => Flean.Float.nan
| Flean.Float.normal f ve vm => Flean.Float.normal f.neg ve vm
| Flean.Float.subnormal sm vm => Flean.Float.subnormal sm.neg vm

lemma to_float_neg (f : Flean.Float C) (h : f.IsFinite) :
  toRat (Flean.Float.neg f) = -toRat f := by
  unfold toRat
  rcases f with _ | _ | ⟨f, ve, vm⟩ | ⟨sm, vm⟩
  · simp [Flean.Float.neg]
  · simp [Flean.Float.neg]
  · simp [Flean.Float.neg, coe_q_of_neg]
  simp [Flean.Float.neg, subnormal_to_q_neg]

lemma float_le_float_of [R : Rounding] (q1 q2 : ℚ)
  (h1 : (toFloat (C := C) q1).IsFinite)
  (h2 : (toFloat (C := C) q2).IsFinite) (h : q1 ≤ q2) :
  toRat (toFloat (C := C) q1) ≤ toRat (toFloat (C := C) q2) := by
  by_cases h' : q1 = q2
  · rw [h']
  rcases splitIsFinite (h := h1) with ⟨q1_small, h1⟩ | ⟨q1_large, h1⟩
  · rw [h1]
    rcases splitIsFinite (h := h2) with ⟨q2_small, h2⟩ | ⟨q2_large, h2⟩
    · rw [h2]
      apply subnormal_round_le_of_le (C := C) (r := roundFunction R) q1 q2 h
    · rw [h2]
      have : q2 > 0 := by
        contrapose! h'
        rw [abs_of_nonpos h'] at q2_large
        rw [abs_of_nonpos (le_trans h h')] at q1_small
        apply le_antisymm h
        have := le_trans q1_small q2_large
        linarith
      apply le_trans (b := 2^C.emin)
      · rw [<-subnormal_to_q_emin, <-roundsub_emin]
        apply subnormal_round_le_of_le (C := C) (r := roundFunction R) q1 (2^C.emin)
        exact (abs_le.mp q1_small).2
      rw [<-abs_of_pos this, <-coe_q_emin, <-roundrep_emin]
      apply le_roundf_of_le
      · positivity
      · positivity
      exact q2_large
  rw [h1]
  rcases splitIsFinite (h := h2) with ⟨q2_small, h2⟩ | ⟨q2_large, h2⟩
  · rw [h2]
    have : q1 < 0 := by
      contrapose! h'
      rw [abs_of_nonneg h'] at q1_large
      apply le_antisymm h
      apply le_trans _ q1_large
      exact (abs_le.mp q2_small).2
    apply le_trans (b := -2^C.emin)
    · rw [<-coe_q_neg_emin, <-roundrep_neg_emin]
      apply le_roundf_of_le
      · exact ne_of_lt this
      · rw [<-neg_ne_zero, neg_neg]
        positivity
      rw [abs_of_neg this] at q1_large
      exact le_neg_of_le_neg q1_large
    rw [<-subnormal_to_q_neg_emin, <-roundsub_neg_emin]
    apply subnormal_round_le_of_le (C := C) (r := roundFunction R)
    exact (abs_le.mp q2_small).1
  rw [h2]
  apply le_roundf_of_le (C := C) (r := roundFunction R) q1 q2
  · exact abs_pos.mp (lt_of_lt_of_le (zpow_pos rfl C.emin) q1_large)
  · exact abs_pos.mp (lt_of_lt_of_le (zpow_pos rfl C.emin) q2_large)
  exact h

/-- Round a rational toward negative infinity to a float. -/
def toFloatDown : ℚ → Flean.Float C := toFloat (R := .mk (.down))

/-- Round a rational toward positive infinity to a float. -/
def toFloatUp : ℚ → Flean.Float C := toFloat (R := .mk (.up))

/-- Round a rational to the nearest float (ties to even). -/
def toFloatNearest : ℚ → Flean.Float C := toFloat (R := .mk (.nearest))

lemma float_down_le (q : ℚ) (h : (toFloatDown (C := C) q).IsFinite) :
  toRat (toFloatDown (C := C) q) ≤ q := by
  unfold toFloatDown at h ⊢
  rcases splitIsFinite (R := .mk (.down)) (h := h) with ⟨q_small, h⟩ | ⟨q_large, h⟩
  · rw [h]
    apply rounddownsub_le
  rw [h]
  apply roundf_down_le
  apply abs_pos.mp
  linarith [show 0 < (2:ℚ) ^ C.emin by positivity]

lemma le_float_up (q : ℚ) (h : (toFloatUp (C := C) q).IsFinite) :
  q ≤ toRat (toFloatUp (C := C) q) := by
  unfold toFloatUp at h ⊢
  rcases splitIsFinite (R := .mk (.up)) (h := h) with ⟨q_small, h⟩ | ⟨q_large, h⟩
  · rw [h]
    apply le_roundupsub
  rw [h]
  apply le_roundf_up
  apply abs_pos.mp
  linarith [show 0 < (2:ℚ) ^ C.emin by positivity]

lemma to_float_boundary (R : Rounding) {q : ℚ} (h : |q| = 2 ^ C.emin) :
  toRat (toFloat (C := C) q) = q := by
  rw [abs_eq (by positivity)] at h
  have ne0 : (2 : ℚ)^C.emin ≠ 0 := by positivity
  have logemin : Int.log 2 |(2 : ℚ)^C.emin| = C.emin := by
    rw [abs_of_pos (by positivity)]
    exact Int.log_zpow (b := 2) (by norm_num) C.emin
  rcases h with h | h
  · rw [h, toFloat]
    simp_rw [logemin]
    simp only [ne0, ↓reduceDIte, lt_self_iff_false, gt_iff_lt]
    simp_rw [roundrep_emin]
    simp [C.emin_lt_emax.not_gt, toRat, coeQ]
  rw [h, toFloat]
  simp_rw [neg_eq_zero, abs_neg]
  simp_rw [logemin]
  simp_rw [roundrep_neg_emin]
  simp [ne0, C.emin_lt_emax.not_gt, toRat, coeQ]

lemma float_up_minus_down (q : ℚ) (h : (toFloatDown (C := C) q).IsFinite)
  (h' : (toFloatUp (C := C) q).IsFinite) :
  toRat (toFloatUp (C := C) q) - toRat (toFloatDown (C := C) q)
    ≤ max ((2 : ℚ)^C.emin / (C.prec : ℚ)) (2 ^ (Int.log 2 |q|) / C.prec) := by
  unfold toFloatDown toFloatUp at *
  by_cases q_is_boundary : |q| = 2^C.emin
  · rw [to_float_boundary (R := .mk (.down)) q_is_boundary]
    rw [to_float_boundary (R := .mk (.up)) q_is_boundary]
    simp only [sub_self]
    positivity
  rcases splitIsFinite (R := .mk (.down)) (h := h) with ⟨q_small, h⟩ | ⟨q_large, h⟩
  <;> rcases splitIsFinite (R := .mk (.up)) (h := h') with ⟨q_small', h'⟩ | ⟨q_large', h'⟩
  · rw [h, h']
    apply le_max_of_le_left
    unfold roundsub
    simp only [roundFunction]
    apply subnormal_up_minus_down (C := C)
  · exfalso
    apply q_is_boundary
    apply le_antisymm q_small q_large'
  · exfalso
    apply q_is_boundary
    apply le_antisymm q_small' q_large
  rw [h, h']
  apply le_max_of_le_right
  apply roundf_up_minus_down
  apply abs_pos.mp
  linarith [show 0 < (2:ℚ) ^ C.emin by positivity]

lemma float_eq_up_or_down [R : Rounding] (q : ℚ) :
  (toFloat (C := C) q) = (toFloatDown (C := C) q) ∨
  (toFloat (C := C) q) = (toFloatUp (C := C) q) := by
  by_cases q_nezero : q = 0
  · left
    rw [q_nezero]
    simp [toFloat, toFloatDown]
  unfold toFloatDown toFloatUp toFloat roundsub roundRep
  split_ifs with h1
  · simp only
    set x := |q| * 2 ^ (-C.emin) * ↑C.prec with x_def
    have := round_eq_or' (r := roundFunction R) (b := q < 0)
        (q := x) (h := by positivity)
    simp_rw [subnormalRound]
    rcases this with h' | h'
    · left
      simp_rw [<-x_def, h']
      simp [x_def, roundFunction]
    right
    simp_rw [<-x_def, h']
    simp [x_def, roundFunction]
  simp only
  set x := ((|q| * (2 ^ Int.log 2 |q|)⁻¹ - 1) * ↑C.prec) with x_def
  have := by
    refine round_eq_or' (r := roundFunction R) (b := q < 0)
      (q := x) (h := ?_)
    apply mantissa_nonneg (q_nezero := q_nezero)
  simp_rw [roundf]
  rcases this with h' | h'
  · left
    simp_rw [<-x_def, h']
    simp [x_def, roundFunction]
  right
  simp_rw [<-x_def, h']
  simp [x_def, roundFunction]

lemma float_error_old [R : Rounding] (q : ℚ) (h : (toFloatDown (C := C) q).IsFinite)
    (h' : (toFloatUp (C := C) q).IsFinite) :
  |toRat (toFloat (C := C) q) - q|
    ≤ max ((2 : ℚ)^C.emin / C.prec) (2 ^ (Int.log 2 |q|) / C.prec) := by
  apply le_trans (b := toRat (toFloatUp (C := C) q) - toRat (toFloatDown (C := C) q))
  · rcases float_eq_up_or_down q with h'' | h'' <;> rw [h'']
    · rw [abs_sub_comm, abs_of_nonneg]
      · rw [sub_le_sub_iff_right]
        apply le_float_up (C := C)
        rwa [toFloatUp]
      rw [sub_nonneg]
      apply float_down_le (C := C) (h := h)
    rw [abs_of_nonneg]
    · rw [sub_le_sub_iff_left]
      apply float_down_le (C := C) (h := h)
    rw [sub_nonneg]
    apply le_float_up (C := C) (h := h')
  apply float_up_minus_down (C := C) q h h'

lemma float_error [R : Rounding] (q : ℚ) (h : (toFloat (C := C) q).IsFinite) :
  |toRat (toFloat (C := C) q) - q|
    ≤ max ((2 : ℚ)^C.emin / C.prec) (2 ^ (Int.log 2 |q|) / C.prec) := by
  rw [abs_sub_comm]
  rcases splitIsFinite (h := h) with ⟨q_small, h⟩ | ⟨q_large, h⟩
  · rw [h]
    apply le_sup_of_le_left
    apply subnormal_round_close (roundFunction R) q
  rw [h]
  apply le_sup_of_le_right
  apply roundf_close (roundFunction R)
  apply abs_pos.mp
  linarith [show 0 < (2:ℚ) ^ C.emin by positivity]

lemma to_float_in_range [R : Rounding] {q : ℚ} (h : |q| ≤ maxFloatQ C) :
  (toFloat q : Flean.Float C).IsFinite := by
  by_cases q_nezero : q = 0
  · rw [q_nezero]
    simp [toFloat, Flean.Float.IsFinite]
  have := log_lt_emax_of_max_float q_nezero h
  rw [Flean.Float.IsFinite]
  · rw [toFloat]
    simp only [q_nezero, ↓reduceDIte, gt_iff_lt, imp_false, Bool.forall_bool]
    split_ifs with h1 h2 h3
    · simp
    · simp
    · simp only [Flean.Float.inf.injEq, decide_eq_false_iff_not, not_lt, not_le, decide_eq_true_eq]
      have := round_min_e' (C := C) q q_nezero
      exfalso
      suffices (roundRep q).e ≤ C.emax by
        linarith
      exact roundf_in_range _ q_nezero h
    · simp
  simp [toFloat]
  split_ifs <;> simp

lemma float_error' [R : Rounding] (q : ℚ) (h : |q| ≤ maxFloatQ C) :
  |toRat (toFloat (C := C) q) - q|
    ≤ max ((2 : ℚ)^C.emin / C.prec) (2 ^ (Int.log 2 |q|) / C.prec) :=
  float_error q (to_float_in_range h)

lemma float_nearest_error (q : ℚ) (h : (toFloatNearest (C := C) q).IsFinite) :
  |q - toRat (toFloatNearest (C := C) q)|
    ≤ max ((2 : ℚ) ^ (Int.log 2 |q| - 1) / C.prec) (2 ^ (C.emin - 1) / C.prec) := by
  unfold toFloatNearest at h ⊢
  rcases splitIsFinite (R := .mk (.nearest)) (h := h) with ⟨q_small, h⟩ | ⟨q_large, h⟩
  · rw [h]
    apply le_sup_of_le_right
    apply subnormal_near_close
  rw [h]
  apply le_sup_of_le_left
  apply roundf_near_close
  apply abs_pos.mp
  linarith [show 0 < (2:ℚ) ^ C.emin by positivity]
