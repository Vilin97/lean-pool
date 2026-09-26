/-
Copyright (c) 2026 Wouter Cames van Batenburg, Samuel Korsky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Cames van Batenburg, Samuel Korsky
-/

module

public import LeanPool.MooreBound.DegreeDiameter.AsymptoticsLimits
public import LeanPool.MooreBound.DegreeDiameter.Proposition31Full
public import LeanPool.MooreBound.PrimeNumberTheoremAnd.Consequences
public import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Theorem 1.1 directly from Proposition 3.1

This module follows the dependency route in the paper.  For every large
ambient degree `d`, the prime-number theorem supplies a prime `p` just below
the `(2k)`-th root of `d`.  The concrete graph `Proposition31Graph` over the
field of order `p` has degree at most its displayed cap, and that cap is at
most `d`.  Its exact order-to-cap asymptotic then gives the lower bound.  The
Moore bound gives the matching upper bound.

Lean Pool port of wewantmoore commit d59bd80ea93fabb9faf769e790ab47692645e022.
The port adds a namespace and adapts proofs to the current Mathlib APIs and repository style.
-/

public section

namespace MooreBound

open Filter _root_.Set

namespace DegreeDiameter

noncomputable section

/-- A prime, viewed as one of the prime-power field orders used in
Proposition 3.1. -/
def proposition31PrimePowerIndexOfPrime (p : ℕ) (hp : p.Prime) :
    PrimePowerIndex :=
  ⟨p, hp.isPrimePow⟩

@[simp]
theorem proposition31PrimePowerIndexOfPrime_val (p : ℕ) (hp : p.Prime) :
    (proposition31PrimePowerIndexOfPrime p hp).1 = p :=
  rfl

instance proposition31PrimePowerIndex_nonempty : Nonempty PrimePowerIndex :=
  ⟨proposition31PrimePowerIndexOfPrime 2 Nat.prime_two⟩

/-- The cap is bounded above by the power used to fit the construction below
an ambient degree. -/
theorem proposition31_cap_le_succ_pow_two_mul
    (q : PrimePowerIndex) (k : ℕ) :
    proposition31DegreeCap q.1 k ≤ (q.1 + 1) ^ (2 * k) := by
  have hsub : (q.1 + 1) ^ k - 1 ≤ (q.1 + 1) ^ k := Nat.sub_le _ _
  calc
    proposition31DegreeCap q.1 k =
        (q.1 + 1) ^ k * ((q.1 + 1) ^ k - 1) := rfl
    _ ≤ (q.1 + 1) ^ k * (q.1 + 1) ^ k :=
      Nat.mul_le_mul_left _ hsub
    _ = (q.1 + 1) ^ (2 * k) := by
      rw [← pow_add]
      congr 1
      omega

/-- For positive `k`, the cap also dominates `q^(2k)`.  This is the scale
comparison needed after choosing a prime close to the relevant root. -/
theorem proposition31_pow_two_mul_le_cap
    (q : PrimePowerIndex) (k : ℕ) (hk : 0 < k) :
    q.1 ^ (2 * k) ≤ proposition31DegreeCap q.1 k := by
  have hpowlt : q.1 ^ k < (q.1 + 1) ^ k :=
    Nat.pow_lt_pow_left (Nat.lt_succ_self q.1) hk.ne'
  have hleft : q.1 ^ k ≤ (q.1 + 1) ^ k := hpowlt.le
  have hright : q.1 ^ k ≤ (q.1 + 1) ^ k - 1 := by omega
  calc
    q.1 ^ (2 * k) = q.1 ^ k * q.1 ^ k := by
      rw [← pow_add]
      congr 1
      omega
    _ ≤ (q.1 + 1) ^ k * ((q.1 + 1) ^ k - 1) :=
      Nat.mul_le_mul hleft hright
    _ = proposition31DegreeCap q.1 k := rfl

/-- The concrete graph in Proposition 3.1 is admissible whenever its
displayed cap is at most the ambient maximum degree.  In particular, this
lemma uses the actual common degree and the exact diameter of that graph. -/
theorem proposition31_orderAdmissible
    (q : PrimePowerIndex) (k : ℕ) (hk : 0 < k) {d : ℕ}
    (hcap : proposition31DegreeCap q.1 k ≤ d) :
    OrderAdmissible k d (proposition31PrimePowerOrder k q) := by
  let V := Proposition31Vertex (PrimePowerField q) k
  let G := Proposition31Graph (PrimePowerField q) k
  have hP31 := proposition_3_1 k hk
  have hp : Proposition31FiniteClaims q k := hP31.1 q
  refine ⟨V, G, inferInstance, rfl, ?_, ?_⟩
  · intro P
    have hregular :
        (G.neighborSet P).ncard =
          proposition31Degree (PrimePowerField q) k := by
      simpa only [G, Nat.card_coe_set_eq] using hp.regularity P
    calc
      (G.neighborSet P).ncard =
          proposition31Degree (PrimePowerField q) k := hregular
      _ ≤ proposition31DegreeCap q.1 k := by
        exact hp.degree_le_cap
      _ ≤ d := hcap
  · exact hp.ediam_eq.le

/-! ## Prime interpolation -/

/-- Taking a fixed positive integral root preserves divergence to infinity. -/
theorem proposition31_tendsto_nthRoot_comp_atTop
    {D : ℕ → ℕ} (hD : Tendsto D atTop atTop)
    {m : ℕ} (hm : 0 < m) :
    Tendsto (fun d ↦ Nat.nthRoot m (D d)) atTop atTop :=
  tendsto_nthRoot_comp_atTop hD hm

/-- The small root-normalization factor which occurs in the interpolation
argument tends to one. -/
theorem proposition31_tendsto_nthRoot_div_add_one
    {D : ℕ → ℕ} (hD : Tendsto D atTop atTop)
    {m : ℕ} (hm : 0 < m) :
    Tendsto
      (fun d ↦ (Nat.nthRoot m (D d) : ℝ) /
        ((Nat.nthRoot m (D d) : ℝ) + 1))
      atTop (nhds 1) :=
  tendsto_nthRoot_div_add_one hD hm

/-- A positive multiplicative prime gap can be made small enough for any
fixed power. -/
theorem proposition31_exists_pos_inv_one_add_pow_gt
    {M : ℕ} {y : ℝ} (hy : y < 1) :
    ∃ η : ℝ, 0 < η ∧ y < ((1 + η)⁻¹) ^ M :=
  exists_pos_inv_one_add_pow_gt hy

/-- The PNT prime interval pulled back along a growing integral root. -/
theorem proposition31_eventually_prime_near_nthRoot
    {D : ℕ → ℕ} (hD : Tendsto D atTop atTop)
    {m : ℕ} (hm : 0 < m) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ d : ℕ in atTop, ∃ p : ℕ, p.Prime ∧
      (Nat.nthRoot m (D d) : ℝ) / (1 + η) < p ∧
      p + 1 ≤ Nat.nthRoot m (D d) :=
  eventually_prime_near_nthRoot (fun hη => prime_between hη) hD hm hη

/-- The root comparison factor used in the lower bound. -/
@[expose] def proposition31RootComparison
    (D : ℕ → ℕ) (m t : ℕ) (η : ℝ) (d : ℕ) : ℝ :=
  ((Nat.nthRoot m (D d) : ℝ) /
    ((Nat.nthRoot m (D d) : ℝ) + 1) / (1 + η)) ^ (m * t)

theorem proposition31_tendsto_rootComparison
    {D : ℕ → ℕ} (hD : Tendsto D atTop atTop)
    {m : ℕ} (hm : 0 < m) (t : ℕ) {η : ℝ} (_hη : 0 < η) :
    Tendsto (proposition31RootComparison D m t η) atTop
      (nhds (((1 + η)⁻¹) ^ (m * t))) :=
  tendsto_rootComparison hD hm t _hη

/-! ## The lower and upper extremal comparisons -/

/-- The pointwise multiplication step combining the exact order/cap ratio
with the PNT scale comparison. -/
theorem proposition31_mul_rootComparison_lt_order_ratio
    (q : PrimePowerIndex) {k r d : ℕ} (hk : 0 < k)
    {η s : ℝ} (hη : 0 < η) (hs : 0 < s)
    (hqLower : (r : ℝ) / (1 + η) < q.1)
    (hrPos : 0 < r) (hdUpper : d ≤ (r + 1) ^ (2 * k))
    (hdPos : 0 < d)
    (horder : s <
      (proposition31PrimePowerOrder k q : ℝ) /
        (proposition31DegreeCap q.1 k : ℝ) ^ k) :
    s * ((r : ℝ) / ((r : ℝ) + 1) / (1 + η)) ^ ((2 * k) * k) <
      (proposition31PrimePowerOrder k q : ℝ) / (d : ℝ) ^ k := by
  let m := 2 * k
  have hm : 0 < m := Nat.mul_pos (by norm_num) hk
  have hM : m * k ≠ 0 := Nat.mul_ne_zero hm.ne' hk.ne'
  have hnum : ((r : ℝ) / (1 + η)) ^ (m * k) <
      (q.1 : ℝ) ^ (m * k) := by
    exact pow_lt_pow_left₀ hqLower (by positivity) hM
  have hcapNat : q.1 ^ m ≤ proposition31DegreeCap q.1 k := by
    simpa only [m] using proposition31_pow_two_mul_le_cap q k hk
  have hcapPowNat : q.1 ^ (m * k) ≤
      proposition31DegreeCap q.1 k ^ k := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left hcapNat k
  have hcapPow : (q.1 : ℝ) ^ (m * k) ≤
      (proposition31DegreeCap q.1 k : ℝ) ^ k := by
    exact_mod_cast hcapPowNat
  have hden : (0 : ℝ) < (d : ℝ) ^ k := by positivity
  have hupperden : (d : ℝ) ^ k ≤
      (((r : ℝ) + 1) ^ m) ^ k := by
    apply pow_le_pow_left₀ (by positivity)
    exact_mod_cast hdUpper
  have hid :
      ((r : ℝ) / ((r : ℝ) + 1) / (1 + η)) ^ (m * k) =
        ((r : ℝ) / (1 + η)) ^ (m * k) /
          (((r : ℝ) + 1) ^ m) ^ k := by
    have hpow : (((r : ℝ) + 1) ^ m) ^ k =
        ((r : ℝ) + 1) ^ (m * k) := by
      rw [← pow_mul]
    rw [hpow, div_pow, div_pow]
    ring
  have hrootCap :
      ((r : ℝ) / ((r : ℝ) + 1) / (1 + η)) ^ (m * k) <
        (proposition31DegreeCap q.1 k : ℝ) ^ k / (d : ℝ) ^ k := by
    rw [hid]
    calc
      ((r : ℝ) / (1 + η)) ^ (m * k) /
            (((r : ℝ) + 1) ^ m) ^ k <
          (q.1 : ℝ) ^ (m * k) /
            (((r : ℝ) + 1) ^ m) ^ k :=
        (div_lt_div_iff_of_pos_right (by positivity)).2 hnum
      _ ≤ (proposition31DegreeCap q.1 k : ℝ) ^ k /
            (((r : ℝ) + 1) ^ m) ^ k :=
        div_le_div_of_nonneg_right hcapPow (by positivity)
      _ ≤ (proposition31DegreeCap q.1 k : ℝ) ^ k / (d : ℝ) ^ k :=
        div_le_div_of_nonneg_left (by positivity) hden hupperden
  have hrootPos : 0 <
      ((r : ℝ) / ((r : ℝ) + 1) / (1 + η)) ^ (m * k) := by
    positivity
  have horderPos : 0 <
      (proposition31PrimePowerOrder k q : ℝ) /
        (proposition31DegreeCap q.1 k : ℝ) ^ k :=
    hs.trans horder
  have hqPosNat : 0 < q.1 := Nat.zero_lt_of_lt q.2.two_le
  have hcapPosNat : 0 < proposition31DegreeCap q.1 k :=
    (Nat.pow_pos hqPosNat).trans_le hcapNat
  have hcapNe : (proposition31DegreeCap q.1 k : ℝ) ≠ 0 := by
    exact_mod_cast hcapPosNat.ne'
  have hdNe : (d : ℝ) ≠ 0 := by exact_mod_cast hdPos.ne'
  change s *
      ((r : ℝ) / ((r : ℝ) + 1) / (1 + η)) ^ (m * k) < _
  calc
    s * ((r : ℝ) / ((r : ℝ) + 1) / (1 + η)) ^ (m * k) <
        ((proposition31PrimePowerOrder k q : ℝ) /
          (proposition31DegreeCap q.1 k : ℝ) ^ k) *
        ((r : ℝ) / ((r : ℝ) + 1) / (1 + η)) ^ (m * k) :=
      mul_lt_mul_of_pos_right horder hrootPos
    _ < ((proposition31PrimePowerOrder k q : ℝ) /
          (proposition31DegreeCap q.1 k : ℝ) ^ k) *
        ((proposition31DegreeCap q.1 k : ℝ) ^ k / (d : ℝ) ^ k) :=
      mul_lt_mul_of_pos_left hrootCap horderPos
    _ = (proposition31PrimePowerOrder k q : ℝ) / (d : ℝ) ^ k := by
      field_simp [hcapNe, hdNe]

theorem proposition31_tendsto_orderRatio_upper (k : ℕ) :
    Tendsto (fun d : ℕ ↦ (1 + (d : ℝ)⁻¹) ^ k) atTop (nhds 1) :=
  tendsto_orderRatio_upper k

/-- **Theorem 1.1, directly from Proposition 3.1.** -/
theorem theorem_1_1_from_proposition_3_1
    {k : ℕ} (hk : 0 < k) :
    Tendsto (fun d : ℕ ↦ (nKD k d : ℝ) / (d : ℝ) ^ k)
      atTop (nhds 1) := by
  rw [tendsto_order]
  constructor
  · intro y hy
    by_cases hyNeg : y < 0
    · exact Eventually.of_forall fun d ↦
        hyNeg.trans_le (div_nonneg (by positivity) (by positivity))
    · have hyNonneg : 0 ≤ y := le_of_not_gt hyNeg
      let s : ℝ := (y + 1) / 2
      have hsPos : 0 < s := by dsimp only [s]; linarith
      have hsOne : s < 1 := by dsimp only [s]; linarith
      have hyss : y < s * s := by
        dsimp only [s]
        nlinarith [sq_pos_of_pos (sub_pos.mpr hy)]
      let m := 2 * k
      have hm : 0 < m := Nat.mul_pos (by norm_num) hk
      obtain ⟨η, hη, hsη⟩ :=
        proposition31_exists_pos_inv_one_add_pow_gt (M := m * k) hsOne
      have hcomparison :=
        (proposition31_tendsto_rootComparison tendsto_id hm k hη).eventually
          (Ioi_mem_nhds hsη)
      have hprime :=
        proposition31_eventually_prime_near_nthRoot tendsto_id hm hη
      have horderEventually :=
        (proposition31_order_div_cap_pow_tendsto_one_from_proposition_3_1
          k hk).eventually
          (Ioi_mem_nhds hsOne)
      rw [eventually_atTop] at horderEventually
      obtain ⟨q₀, hq₀⟩ := horderEventually
      have hrootNat :=
        proposition31_tendsto_nthRoot_comp_atTop tendsto_id hm
      have hrootReal :
          Tendsto (fun d ↦ (Nat.nthRoot m d : ℝ)) atTop atTop :=
        tendsto_natCast_atTop_atTop.comp hrootNat
      have hx :
          Tendsto (fun d ↦ (Nat.nthRoot m d : ℝ) / (1 + η))
            atTop atTop :=
        hrootReal.atTop_div_const (by linarith)
      have hlarge := hx.eventually_gt_atTop (q₀.1 : ℝ)
      filter_upwards [hcomparison, hprime, hlarge] with d hdcomp hdprime hdlarge
      obtain ⟨p, hp, hpLower, hpUpper⟩ := hdprime
      let q : PrimePowerIndex := proposition31PrimePowerIndexOfPrime p hp
      have hq₀q : q₀ ≤ q := by
        change q₀.1 ≤ p
        have hlt : (q₀.1 : ℝ) < p := hdlarge.trans hpLower
        have hltNat : q₀.1 < p := by exact_mod_cast hlt
        exact hltNat.le
      have horderq :
          s < (proposition31PrimePowerOrder k q : ℝ) /
            (proposition31DegreeCap q.1 k : ℝ) ^ k :=
        hq₀ q hq₀q
      let r := Nat.nthRoot m d
      have hsucPow : (p + 1) ^ m ≤ d :=
        (Nat.pow_le_pow_left hpUpper m).trans
          (Nat.pow_nthRoot_le (Or.inl hm.ne'))
      have hcap : proposition31DegreeCap q.1 k ≤ d := by
        calc
          proposition31DegreeCap q.1 k ≤ (q.1 + 1) ^ (2 * k) :=
            proposition31_cap_le_succ_pow_two_mul q k
          _ = (p + 1) ^ m := by rfl
          _ ≤ d := hsucPow
      have hadmissible := proposition31_orderAdmissible q k hk hcap
      have horderLe : proposition31PrimePowerOrder k q ≤ nKD k d :=
        le_nKD hadmissible
      have hdUpper : d ≤ (r + 1) ^ (2 * k) :=
        (Nat.lt_pow_nthRoot_add_one hm.ne' d).le
      have hrPos : 0 < r := (Nat.succ_pos p).trans_le hpUpper
      have hdPos : 0 < d := by
        have : 0 < (p + 1) ^ m := Nat.pow_pos (Nat.succ_pos p)
        exact this.trans_le hsucPow
      have hpoint := proposition31_mul_rootComparison_lt_order_ratio
        q hk hη hsPos hpLower hrPos hdUpper hdPos horderq
      have hratioLe :
          (proposition31PrimePowerOrder k q : ℝ) / (d : ℝ) ^ k ≤
            (nKD k d : ℝ) / (d : ℝ) ^ k := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact_mod_cast horderLe
      calc
        y < s * s := hyss
        _ < s * proposition31RootComparison id m k η d :=
          mul_lt_mul_of_pos_left hdcomp hsPos
        _ < (proposition31PrimePowerOrder k q : ℝ) / (d : ℝ) ^ k := by
          simpa only [proposition31RootComparison, id_eq, m, r] using hpoint
        _ ≤ (nKD k d : ℝ) / (d : ℝ) ^ k := hratioLe
  · intro z hz
    have hupper : ∀ᶠ d : ℕ in atTop, (1 + (d : ℝ)⁻¹) ^ k < z :=
      (proposition31_tendsto_orderRatio_upper k).eventually (Iio_mem_nhds hz)
    filter_upwards [hupper, eventually_gt_atTop 0] with d hupp hd
    have hdegree : (nKD k d : ℝ) ≤ ((d + 1 : ℕ) : ℝ) ^ k := by
      exact_mod_cast
        (nKD_le_mooreBound k d).trans (mooreBound_le_add_one_pow k d)
    have hratioUpper :
        (nKD k d : ℝ) / (d : ℝ) ^ k ≤
          (1 + (d : ℝ)⁻¹) ^ k := by
      calc
        (nKD k d : ℝ) / (d : ℝ) ^ k ≤
            (((d + 1 : ℕ) : ℝ) ^ k) / (d : ℝ) ^ k :=
          div_le_div_of_nonneg_right hdegree (by positivity)
        _ = (1 + (d : ℝ)⁻¹) ^ k := by
          rw [← div_pow]
          congr 1
          norm_num
          field_simp
    exact hratioUpper.trans_lt hupp

end

end DegreeDiameter

end MooreBound
