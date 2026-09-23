/-
Copyright (c) 2026 Wouter Cames van Batenburg, Samuel Korsky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Cames van Batenburg, Samuel Korsky
-/

module

public import LeanPool.MooreBound.DegreeDiameter.EdgeReduction
public import LeanPool.MooreBound.DegreeDiameter.Proposition31Full
public import LeanPool.MooreBound.DegreeDiameter.Theorem11FromProposition31
public import Mathlib.Topology.Order.LiminfLimsup

/-!
# Corollary 1.2 directly from Proposition 3.1

This module follows Section 4 of the write-up.  For `k = ell - 1` it applies
the bipartite expansion to the concrete graph in Proposition 3.1.  The exact
edge count is

`|V(H)| * (proposition31PrimePowerDegree k q + 1)`,

Lemma 4.1 supplies line-graph diameter at most `k + 1`, and the two limits in
equation (9) give the normalized lower bound.  The proof records the paper's
convention literally: the displayed edge count is first bounded by
`h ell d - 1`, and only then by `h ell d`.

Lean Pool port of wewantmoore commit d59bd80ea93fabb9faf769e790ab47692645e022.
The port adds a namespace and adapts proofs to the current Mathlib APIs and repository style.
-/

@[expose] public section

namespace MooreBound

open Filter _root_.Set

namespace DegreeDiameter

noncomputable section

/-- The product of the two equation-(9) ratios needed after applying
Lemma 4.1.  The exponent `k + 1` is the line-graph diameter parameter. -/
private def proposition31EdgeFactor (k : ℕ) (q : PrimePowerIndex) : ℝ :=
  (proposition31PrimePowerOrder k q : ℝ) /
      (proposition31PrimePowerDegree k q : ℝ) ^ k *
    ((proposition31PrimePowerDegree k q : ℝ) /
      (proposition31DegreeCap q.1 k : ℝ)) ^ (k + 1)

/-- The two limits in equation (9), combined in exactly the form consumed by
the edge construction. -/
private theorem proposition31_edgeFactor_tendsto_one
    (k : ℕ) (hk : 0 < k) :
    Tendsto (proposition31EdgeFactor k) atTop (nhds 1) := by
  have hP31 := proposition_3_1 k hk
  have hdegree := hP31.2.1
  have horder := hP31.2.2
  change Tendsto
    (fun q : PrimePowerIndex ↦
      (proposition31PrimePowerOrder k q : ℝ) /
          (proposition31PrimePowerDegree k q : ℝ) ^ k *
        ((proposition31PrimePowerDegree k q : ℝ) /
          (proposition31DegreeCap q.1 k : ℝ)) ^ (k + 1))
    atTop (nhds 1)
  simpa only [one_pow, one_mul] using
    horder.mul (hdegree.pow (k + 1))

private theorem proposition31_tendsto_nat_sub_one_atTop :
    Tendsto (fun d : ℕ ↦ d - 1) atTop atTop :=
  tendsto_nat_sub_one_atTop

/-- The cap-scale comparison used for Corollary 1.2.  This is the edge
analogue of the pointwise interpolation step for Theorem 1.1, with exponent
`t = k + 1`. -/
private theorem proposition31_rootComparison_lt_capRatio
    (q : PrimePowerIndex) {k r d t : ℕ} (hk : 0 < k) (ht : 0 < t)
    {η : ℝ} (hη : 0 < η)
    (hqLower : (r : ℝ) / (1 + η) < q.1)
    (hdUpper : d ≤ (r + 1) ^ (2 * k)) (hdPos : 0 < d) :
    ((r : ℝ) / ((r : ℝ) + 1) / (1 + η)) ^ ((2 * k) * t) <
      (proposition31DegreeCap q.1 k : ℝ) ^ t / (d : ℝ) ^ t := by
  let m := 2 * k
  have hm : 0 < m := Nat.mul_pos (by norm_num) hk
  have hmt : m * t ≠ 0 := Nat.mul_ne_zero hm.ne' ht.ne'
  have hnum :
      ((r : ℝ) / (1 + η)) ^ (m * t) < (q.1 : ℝ) ^ (m * t) :=
    pow_lt_pow_left₀ hqLower (by positivity) hmt
  have hcapNat : q.1 ^ m ≤ proposition31DegreeCap q.1 k := by
    simpa only [m] using proposition31_pow_two_mul_le_cap q k hk
  have hcapPowNat :
      q.1 ^ (m * t) ≤ proposition31DegreeCap q.1 k ^ t := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left hcapNat t
  have hcapPow :
      (q.1 : ℝ) ^ (m * t) ≤
        (proposition31DegreeCap q.1 k : ℝ) ^ t := by
    exact_mod_cast hcapPowNat
  have hden : 0 < (d : ℝ) ^ t := by positivity
  have hupperDen :
      (d : ℝ) ^ t ≤ (((r : ℝ) + 1) ^ m) ^ t := by
    apply pow_le_pow_left₀ (by positivity)
    exact_mod_cast hdUpper
  have hid :
      ((r : ℝ) / ((r : ℝ) + 1) / (1 + η)) ^ (m * t) =
        ((r : ℝ) / (1 + η)) ^ (m * t) /
          (((r : ℝ) + 1) ^ m) ^ t := by
    have hpow : (((r : ℝ) + 1) ^ m) ^ t =
        ((r : ℝ) + 1) ^ (m * t) := by rw [← pow_mul]
    rw [hpow, div_pow, div_pow]
    ring
  change
    ((r : ℝ) / ((r : ℝ) + 1) / (1 + η)) ^ (m * t) < _
  rw [hid]
  calc
    ((r : ℝ) / (1 + η)) ^ (m * t) /
          (((r : ℝ) + 1) ^ m) ^ t <
        (q.1 : ℝ) ^ (m * t) /
          (((r : ℝ) + 1) ^ m) ^ t :=
      (div_lt_div_iff_of_pos_right (by positivity)).2 hnum
    _ ≤ (proposition31DegreeCap q.1 k : ℝ) ^ t /
          (((r : ℝ) + 1) ^ m) ^ t :=
      div_le_div_of_nonneg_right hcapPow (by positivity)
    _ ≤ (proposition31DegreeCap q.1 k : ℝ) ^ t /
          (d : ℝ) ^ t :=
      div_le_div_of_nonneg_left (by positivity) hden hupperDen

/-- A neutral coarse bound needed only to invoke the order-theoretic
characterization of `liminf`. -/
private theorem proposition31_edgeRatio_isBoundedUnder_le (ell : ℕ) :
    atTop.IsBoundedUnder (· ≤ ·)
      (fun d : ℕ ↦ (h ell d : ℝ) / (d : ℝ) ^ ell) :=
  edgeRatio_isBoundedUnder_le ell

/-- Applying `bipartiteExpansion` to the actual Proposition 3.1 graph gives
an admissible edge graph whenever the actual degree plus one fits below the
ambient degree.  This records regularity, the exact edge count, and Lemma 4.1
in one finite step. -/
private theorem proposition31_bipartiteExpansion_edgeAdmissible
    (q : PrimePowerIndex) (k : ℕ) (hk : 0 < k)
    {ell d : ℕ} (hkell : k + 1 = ell)
    (hcap : proposition31DegreeCap q.1 k + 1 ≤ d) :
    EdgeAdmissible ell d
      (proposition31PrimePowerOrder k q *
        (proposition31PrimePowerDegree k q + 1)) := by
  let G := Proposition31Graph (PrimePowerField q) k
  have hP31 := proposition_3_1 k hk
  have hp : Proposition31FiniteClaims q k := hP31.1 q
  have hregular : ∀ P,
      (G.neighborSet P).ncard = proposition31PrimePowerDegree k q := by
    intro P
    simpa only [G, Nat.card_coe_set_eq] using hp.regularity P
  have hdegreeCap :
      proposition31PrimePowerDegree k q ≤
        proposition31DegreeCap q.1 k := by
    exact hp.degree_le_cap
  have hdegree : MaxDegreeLE (bipartiteExpansion G) d :=
    maxDegreeLE_mono
      ((Nat.add_le_add_right hdegreeCap 1).trans hcap)
      (maxDegreeLE_bipartiteExpansion
        (fun P ↦ (hregular P).le))
  have hedges :
      (bipartiteExpansion G).edgeSet.ncard =
        proposition31PrimePowerOrder k q *
          (proposition31PrimePowerDegree k q + 1) := by
    simpa only [G] using
      ncard_edgeSet_bipartiteExpansion_of_regular G
        (proposition31PrimePowerDegree k q) hregular
  have hdiamG : G.ediam ≤ (k : ℕ∞) := by
    simpa only [G] using hp.ediam_eq.le
  have hline :
      (bipartiteExpansion G).lineGraph.ediam ≤ (ell : ℕ∞) := by
    simpa only [hkell] using lemma_4_1_le G k hdiamG
  exact ⟨_, bipartiteExpansion G, inferInstance, hedges, hdegree, hline⟩

/-- The exact Proposition 3.1 family gives every lower estimate below one
eventually for the edge ratio.  Prime interpolation is performed against the
displayed cap, not against a weaker order estimate. -/
private theorem proposition31_eventually_lt_edgeRatio
    {k : ℕ} (hk : 0 < k) {y : ℝ} (hy : y < 1) :
    ∀ᶠ d : ℕ in atTop,
      y < (h (k + 1) d : ℝ) / (d : ℝ) ^ (k + 1) := by
  by_cases hy0 : y < 0
  · exact Eventually.of_forall fun d ↦
      hy0.trans_le (div_nonneg (Nat.cast_nonneg _)
        (pow_nonneg (Nat.cast_nonneg _) _))
  have hyNonneg : 0 ≤ y := le_of_not_gt hy0
  let m := 2 * k
  let t := k + 1
  have hm : 0 < m := Nat.mul_pos (by norm_num) hk
  have ht : 0 < t := Nat.succ_pos k
  obtain ⟨η, hη, hyLimit⟩ :=
    proposition31_exists_pos_inv_one_add_pow_gt (M := m * t) hy
  let L : ℝ := ((1 + η)⁻¹) ^ (m * t)
  have hLpos : 0 < L := by
    dsimp only [L]
    positivity
  have hyDiv : y / L < 1 := (div_lt_one hLpos).2 (by
    simpa only [L] using hyLimit)
  have hyDivNonneg : 0 ≤ y / L := div_nonneg hyNonneg hLpos.le
  obtain ⟨a, hya, haOne⟩ := exists_between hyDiv
  have haPos : 0 < a := hyDivNonneg.trans_lt hya
  have hyaLimit : y / a < L := by
    apply (div_lt_iff₀ haPos).2
    have hy_aL : y < a * L := (div_lt_iff₀ hLpos).1 hya
    simpa only [mul_comm] using hy_aL
  have hfactorEventually :
      ∀ᶠ q : PrimePowerIndex in atTop,
        a < proposition31EdgeFactor k q :=
    (proposition31_edgeFactor_tendsto_one k hk).eventually
      (Ioi_mem_nhds haOne)
  obtain ⟨q₀, hq₀⟩ := (eventually_atTop.1 hfactorEventually)
  have hcomparisonEventually :
      ∀ᶠ d : ℕ in atTop,
        y / a < proposition31RootComparison (fun d : ℕ ↦ d - 1) m t η d := by
    have hlim := proposition31_tendsto_rootComparison
      proposition31_tendsto_nat_sub_one_atTop hm t hη
    exact hlim.eventually (Ioi_mem_nhds (by
      simpa only [L] using hyaLimit))
  have hprimeEventually := proposition31_eventually_prime_near_nthRoot
    proposition31_tendsto_nat_sub_one_atTop hm hη
  have hrootNat := proposition31_tendsto_nthRoot_comp_atTop
    proposition31_tendsto_nat_sub_one_atTop hm
  have hrootReal : Tendsto
      (fun d : ℕ ↦
        (Nat.nthRoot m (d - 1) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hrootNat
  have hrootDiv : Tendsto
      (fun d : ℕ ↦
        (Nat.nthRoot m (d - 1) : ℝ) / (1 + η))
      atTop atTop :=
    hrootReal.atTop_div_const (by linarith)
  have hrootLarge :
      ∀ᶠ d : ℕ in atTop,
        (q₀.1 : ℝ) <
          (Nat.nthRoot m (d - 1) : ℝ) / (1 + η) :=
    hrootDiv.eventually_gt_atTop (q₀.1 : ℝ)
  filter_upwards [hcomparisonEventually, hprimeEventually, hrootLarge]
    with d hcomparison hdprime hlarge
  obtain ⟨p, hp, hpLower, hpUpper⟩ := hdprime
  let q : PrimePowerIndex := proposition31PrimePowerIndexOfPrime p hp
  let r := Nat.nthRoot m (d - 1)
  let C := proposition31DegreeCap q.1 k
  let Δ := proposition31PrimePowerDegree k q
  let N := proposition31PrimePowerOrder k q
  have hq₀q : q₀ ≤ q := by
    change q₀.1 ≤ p
    have : (q₀.1 : ℝ) < p := hlarge.trans hpLower
    exact Nat.le_of_lt (by exact_mod_cast this)
  have hfactor : a < proposition31EdgeFactor k q := hq₀ q hq₀q
  have hfactorPos : 0 < proposition31EdgeFactor k q := haPos.trans hfactor
  have hsuccPow : (p + 1) ^ m ≤ d - 1 :=
    (Nat.pow_le_pow_left hpUpper m).trans
      (Nat.pow_nthRoot_le (Or.inl hm.ne'))
  have hcapUpper : C ≤ (p + 1) ^ m := by
    simpa only [C, q, m, proposition31PrimePowerIndexOfPrime_val] using
      proposition31_cap_le_succ_pow_two_mul q k
  have hsuccPos : 0 < (p + 1) ^ m := Nat.pow_pos (Nat.succ_pos p)
  have hcapAmbient : C + 1 ≤ d := by omega
  have hpCap : p ^ m ≤ C := by
    simpa only [C, q, m, proposition31PrimePowerIndexOfPrime_val] using
      proposition31_pow_two_mul_le_cap q k hk
  have hpPos : 0 < p := hp.pos
  have hCpos : 0 < C := (Nat.pow_pos hpPos).trans_le hpCap
  have hdPos : 0 < d := by omega
  have hdupper : d ≤ (r + 1) ^ m := by
    dsimp only [r]
    have := Nat.lt_pow_nthRoot_add_one hm.ne' (d - 1)
    omega
  have hrootCap :
      proposition31RootComparison (fun d : ℕ ↦ d - 1) m t η d <
        (C ^ t : ℕ) / (d : ℝ) ^ t := by
    simpa only [proposition31RootComparison, r, m, C, q, Nat.cast_pow,
      proposition31PrimePowerIndexOfPrime_val] using
      proposition31_rootComparison_lt_capRatio
        q hk ht hη hpLower hdupper hdPos
  have hcomparisonPos :
      0 < proposition31RootComparison (fun d : ℕ ↦ d - 1) m t η d :=
    (div_nonneg hyNonneg haPos.le).trans_lt hcomparison
  have hyProduct :
      y < proposition31EdgeFactor k q *
        proposition31RootComparison (fun d : ℕ ↦ d - 1) m t η d := by
    calc
      y = a * (y / a) := by field_simp
      _ < a * proposition31RootComparison
          (fun d : ℕ ↦ d - 1) m t η d :=
        mul_lt_mul_of_pos_left hcomparison haPos
      _ < proposition31EdgeFactor k q *
          proposition31RootComparison
            (fun d : ℕ ↦ d - 1) m t η d :=
        mul_lt_mul_of_pos_right hfactor hcomparisonPos
  have hΔne : (Δ : ℝ) ≠ 0 := by
    intro hzero
    have hfactorZero : proposition31EdgeFactor k q = 0 := by
      change (proposition31PrimePowerDegree k q : ℝ) = 0 at hzero
      simp [proposition31EdgeFactor, hzero, hk.ne']
    rw [hfactorZero] at hfactorPos
    exact lt_irrefl 0 hfactorPos
  have hCne : (C : ℝ) ≠ 0 := by exact_mod_cast hCpos.ne'
  have hdne : (d : ℝ) ≠ 0 := by exact_mod_cast hdPos.ne'
  have hfactorCapIdentity :
      proposition31EdgeFactor k q *
          ((C ^ t : ℕ) / (d : ℝ) ^ t) =
        (N * Δ : ℕ) / (d : ℝ) ^ t := by
    have hΔactual :
        (proposition31PrimePowerDegree k q : ℝ) ≠ 0 := by
      simpa only [Δ] using hΔne
    have hCactual :
        (proposition31DegreeCap q.1 k : ℝ) ≠ 0 := by
      simpa only [C] using hCne
    simp only [proposition31EdgeFactor, N, Δ, C, t,
      Nat.cast_mul, Nat.cast_pow, div_pow, pow_succ]
    field_simp [hΔactual, hCactual, hdne]
  have hadmissible : EdgeAdmissible (k + 1) d (N * (Δ + 1)) := by
    simpa only [N, Δ] using
      proposition31_bipartiteExpansion_edgeAdmissible
        q k hk rfl hcapAmbient
  have hedgeSubOne : N * (Δ + 1) ≤ h (k + 1) d - 1 :=
    le_h_sub_one hadmissible
  have hedgeH : N * (Δ + 1) ≤ h (k + 1) d :=
    hedgeSubOne.trans (Nat.sub_le _ _)
  have hdenPos : 0 < (d : ℝ) ^ t := pow_pos (by exact_mod_cast hdPos) t
  calc
    y < proposition31EdgeFactor k q *
        proposition31RootComparison
          (fun d : ℕ ↦ d - 1) m t η d := hyProduct
    _ < proposition31EdgeFactor k q *
        ((C ^ t : ℕ) / (d : ℝ) ^ t) :=
      mul_lt_mul_of_pos_left hrootCap hfactorPos
    _ = (N * Δ : ℕ) / (d : ℝ) ^ t := hfactorCapIdentity
    _ ≤ (N * (Δ + 1) : ℕ) / (d : ℝ) ^ t := by
      apply div_le_div_of_nonneg_right _ hdenPos.le
      exact_mod_cast Nat.mul_le_mul_left N (Nat.le_succ Δ)
    _ ≤ (h (k + 1) d : ℝ) / (d : ℝ) ^ t := by
      apply div_le_div_of_nonneg_right _ hdenPos.le
      exact_mod_cast hedgeH
    _ = (h (k + 1) d : ℝ) / (d : ℝ) ^ (k + 1) := rfl

/-- **Corollary 1.2, directly from Proposition 3.1 and equation (9).** -/
theorem corollary_1_2_from_proposition_3_1
    {ell : ℕ} (hell : 2 ≤ ell) :
    1 ≤ liminf
      (fun d : ℕ ↦ (h ell d : ℝ) / (d : ℝ) ^ ell)
      atTop := by
  let k := ell - 1
  have hk : 0 < k := by omega
  have hkell : k + 1 = ell := by omega
  have hnonneg : atTop.IsBoundedUnder (· ≥ ·)
      (fun d : ℕ ↦ (h ell d : ℝ) / (d : ℝ) ^ ell) := by
    refine ⟨0, ?_⟩
    change ∀ᶠ d : ℕ in atTop,
      (0 : ℝ) ≤ (h ell d : ℝ) / (d : ℝ) ^ ell
    exact .of_forall fun d ↦
      div_nonneg (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg _) ell)
  have hbounded := proposition31_edgeRatio_isBoundedUnder_le ell
  rw [le_liminf_iff hbounded.isCoboundedUnder_ge hnonneg]
  intro y hy
  simpa only [hkell] using proposition31_eventually_lt_edgeRatio hk hy

end

end DegreeDiameter

end MooreBound
