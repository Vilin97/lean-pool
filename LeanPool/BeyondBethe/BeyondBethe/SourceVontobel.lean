/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.Bethe
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Convex.Deriv

/-! # Source Vontobel -/

open scoped BigOperators Topology

namespace BeyondBethe

/-!
# Vontobel's simplex-concavity theorem

This file formalizes the source theorem used to prove concavity of the Bethe
objective.  The algebraic core is the Hessian inequality

`sum v_i^2 / (1 - p_i) <= sum v_i^2 / p_i`

for a strictly positive probability vector `p` and a tangent vector `v` whose
coordinates sum to zero.  This is the finite-dimensional form of the argument
in Vontobel's Theorem 20.  The proof below uses weighted Cauchy--Schwarz and
also supplies the boundary control that is only sketched in the source.
-/

/-- Weighted Cauchy--Schwarz on the complement of one coordinate. -/
private theorem tangent_coordinate_sq_div_complement_le
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (p v : ι → ℝ) (hp : ∀ i ∈ s, 0 < p i)
    (hpsum : ∑ i ∈ s, p i = 1) (hvsum : ∑ i ∈ s, v i = 0)
    (i : ι) (hi : i ∈ s) (hpi : p i < 1) :
    v i ^ 2 / (1 - p i) ≤
      ∑ j ∈ s.erase i, v j ^ 2 / p j := by
  have hpsumErase : ∑ j ∈ s.erase i, p j = 1 - p i := by
    have h := Finset.sum_erase_add s p hi
    rw [hpsum] at h
    linarith
  have hpc : 0 < ∑ j ∈ s.erase i, p j := by
    rw [hpsumErase]
    exact sub_pos.mpr hpi
  have hvsumErase : ∑ j ∈ s.erase i, v j = -v i := by
    have h := Finset.sum_erase_add s v hi
    rw [hvsum] at h
    linarith
  have hcs := Finset.sq_sum_div_le_sum_sq_div
    (R := ℝ) (s.erase i) v
    (fun j hj ↦ hp j (Finset.mem_of_mem_erase hj))
  rw [hpsumErase, hvsumErase, neg_sq] at hcs
  exact hcs

/-- The Hessian inequality behind concavity of Vontobel's simplex entropy. -/
theorem vontobel_tangent_hessian_nonpos
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (p v : ι → ℝ) (hp : ∀ i ∈ s, 0 < p i)
    (hplt : ∀ i ∈ s, p i < 1)
    (hpsum : ∑ i ∈ s, p i = 1) (hvsum : ∑ i ∈ s, v i = 0) :
    (∑ i ∈ s, v i ^ 2 / (1 - p i)) -
        ∑ i ∈ s, v i ^ 2 / p i ≤ 0 := by
  have hcoord : ∀ i ∈ s,
      p i * (v i ^ 2 / (1 - p i)) ≤
        p i * ∑ j ∈ s.erase i, v j ^ 2 / p j := by
    intro i hi
    exact mul_le_mul_of_nonneg_left
      (tangent_coordinate_sq_div_complement_le s p v hp hpsum hvsum i hi (hplt i hi))
      (hp i hi).le
  have hsum := Finset.sum_le_sum fun i hi ↦ hcoord i hi
  have hdouble :
      ∑ i ∈ s, p i * ∑ j ∈ s.erase i, v j ^ 2 / p j =
        ∑ j ∈ s, (1 - p j) * (v j ^ 2 / p j) := by
    classical
    let a : ι → ℝ := fun j ↦ v j ^ 2 / p j
    have herase : ∀ i ∈ s, ∑ j ∈ s.erase i, a j = (∑ j ∈ s, a j) - a i := by
      intro i hi
      have h := Finset.sum_erase_add s a hi
      linarith
    change (∑ i ∈ s, p i * ∑ j ∈ s.erase i, a j) =
      ∑ j ∈ s, (1 - p j) * a j
    calc
      ∑ i ∈ s, p i * ∑ j ∈ s.erase i, a j
          = ∑ i ∈ s, p i * ((∑ j ∈ s, a j) - a i) := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [herase i hi]
      _
          = (∑ i ∈ s, p i) * (∑ j ∈ s, a j) - ∑ i ∈ s, p i * a i := by
              simp_rw [mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]
      _ = (∑ j ∈ s, a j) - ∑ i ∈ s, p i * a i := by rw [hpsum, one_mul]
      _ = ∑ j ∈ s, (1 - p j) * a j := by
              simp_rw [sub_mul, one_mul, Finset.sum_sub_distrib]
  rw [hdouble] at hsum
  have hleft :
      ∑ i ∈ s, v i ^ 2 / (1 - p i) =
        ∑ i ∈ s, (v i ^ 2 + p i * (v i ^ 2 / (1 - p i))) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hne : 1 - p i ≠ 0 := (sub_pos.mpr (hplt i hi)).ne'
    field_simp
    ring
  have hright :
      ∑ i ∈ s, v i ^ 2 / p i =
        ∑ i ∈ s, (v i ^ 2 + (1 - p i) * (v i ^ 2 / p i)) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hne : p i ≠ 0 := (hp i hi).ne'
    field_simp
    ring
  rw [hleft, hright, Finset.sum_add_distrib, Finset.sum_add_distrib]
  linarith

/-- Vontobel's scalar entropy contribution
`-x log x + (1-x) log (1-x)`, written in a boundary-continuous form. -/
noncomputable def vontobelEntropyTerm (x : ℝ) : ℝ :=
  Real.negMulLog x - Real.negMulLog (1 - x)

/-- The entropy `S` in Vontobel's Theorem 20. -/
noncomputable def vontobelSimplexEntropy
    {ι : Type*} [Fintype ι] (p : ι → ℝ) : ℝ :=
  ∑ i, vontobelEntropyTerm (p i)

/-- Affine segment between two finite vectors. -/
def probabilitySegment
    {ι : Type*} (p q : ι → ℝ) (t : ℝ) (i : ι) : ℝ :=
  (1 - t) * p i + t * q i

theorem probabilitySegment_sum
    {ι : Type*} [Fintype ι] {p q : ι → ℝ}
    (hp : ∑ i, p i = 1) (hq : ∑ i, q i = 1) (t : ℝ) :
    ∑ i, probabilitySegment p q t i = 1 := by
  simp_rw [probabilitySegment, Finset.sum_add_distrib, ← Finset.mul_sum,
    hp, hq]
  ring

theorem IsStrictProbabilityVector.lt_one_of_one_lt_card
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ι → ℝ} (hp : IsStrictProbabilityVector p)
    (hcard : 1 < Fintype.card ι) (i : ι) :
    p i < 1 := by
  obtain ⟨j, hji⟩ := Fintype.exists_ne_of_one_lt_card hcard i
  rw [← hp.1.sum_eq_one]
  calc
    p i < p i + p j := lt_add_of_pos_right _ (hp.2 j)
    _ = ∑ k ∈ ({i, j} : Finset ι), p k := by
      rw [Finset.sum_pair hji.symm]
    _ ≤ ∑ k, p k := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) (fun k _ _ ↦ hp.1.nonnegative k)

theorem probabilitySegment_strictProbability
    {ι : Type*} [Fintype ι]
    {p q : ι → ℝ} (hp : IsProbabilityVector p)
    (hq : IsStrictProbabilityVector q) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) :
    IsStrictProbabilityVector (probabilitySegment p q t) := by
  refine ⟨⟨?_, probabilitySegment_sum hp.sum_eq_one hq.1.sum_eq_one t⟩, ?_⟩
  · intro i
    exact add_nonneg
      (mul_nonneg (sub_nonneg.mpr ht1.le) (hp.nonnegative i))
      (mul_nonneg ht0.le (hq.1.nonnegative i))
  · intro i
    exact add_pos_of_nonneg_of_pos
      (mul_nonneg (sub_nonneg.mpr ht1.le) (hp.nonnegative i))
      (mul_pos ht0 (hq.2 i))

theorem hasDerivAt_probabilitySegment
    {ι : Type*} (p q : ι → ℝ) (i : ι) (t : ℝ) :
    HasDerivAt (fun u ↦ probabilitySegment p q u i) (q i - p i) t := by
  convert! ((hasDerivAt_const t 1).sub (hasDerivAt_id t)).mul_const (p i) |>.add
    ((hasDerivAt_id t).mul_const (q i)) using 1 <;>
    simp [probabilitySegment] <;> ring

private theorem hasDerivAt_vontobelEntropyTerm_segment
    {ι : Type*} (p q : ι → ℝ) (i : ι) {t : ℝ}
    (hpos : 0 < probabilitySegment p q t i)
    (hlt : probabilitySegment p q t i < 1) :
    HasDerivAt
      (fun u ↦ vontobelEntropyTerm (probabilitySegment p q u i))
      ((q i - p i) *
        (-Real.log (probabilitySegment p q t i) -
          Real.log (1 - probabilitySegment p q t i) - 2)) t := by
  let r := probabilitySegment p q t i
  let v := q i - p i
  have hr := hasDerivAt_probabilitySegment p q i t
  have hneg : HasDerivAt
      (fun u ↦ Real.negMulLog (probabilitySegment p q u i))
      ((-Real.log r - 1) * v) t := by
    exact (Real.hasDerivAt_negMulLog hpos.ne').comp t hr
  have hinner : HasDerivAt
      (fun u ↦ 1 - probabilitySegment p q u i) (-v) t := by
    convert! (hasDerivAt_const t 1).sub hr using 1 <;> simp [v]
  have hcomp : HasDerivAt
      (fun u ↦ Real.negMulLog (1 - probabilitySegment p q u i))
      ((-Real.log (1 - r) - 1) * (-v)) t := by
    exact (Real.hasDerivAt_negMulLog (sub_pos.mpr hlt).ne').comp t hinner
  change HasDerivAt
    (fun u ↦ Real.negMulLog (probabilitySegment p q u i) -
      Real.negMulLog (1 - probabilitySegment p q u i)) _ t
  convert! hneg.sub hcomp using 1 <;> dsimp [r, v] <;> ring

private theorem hasDerivAt_vontobelEntropyTerm_segment_deriv
    {ι : Type*} (p q : ι → ℝ) (i : ι) {t : ℝ}
    (hpos : 0 < probabilitySegment p q t i)
    (hlt : probabilitySegment p q t i < 1) :
    HasDerivAt
      (fun u ↦ (q i - p i) *
        (-Real.log (probabilitySegment p q u i) -
          Real.log (1 - probabilitySegment p q u i) - 2))
      ((q i - p i) ^ 2 / (1 - probabilitySegment p q t i) -
        (q i - p i) ^ 2 / probabilitySegment p q t i) t := by
  let r := probabilitySegment p q t i
  let v := q i - p i
  have hr := hasDerivAt_probabilitySegment p q i t
  have hlogr : HasDerivAt
      (fun u ↦ Real.log (probabilitySegment p q u i)) (v / r) t := by
    exact hr.log hpos.ne'
  have hinner : HasDerivAt
      (fun u ↦ 1 - probabilitySegment p q u i) (-v) t := by
    convert! (hasDerivAt_const t 1).sub hr using 1 <;> simp [v]
  have hlogc : HasDerivAt
      (fun u ↦ Real.log (1 - probabilitySegment p q u i))
      ((-v) / (1 - r)) t := by
    exact hinner.log (sub_pos.mpr hlt).ne'
  have hsum := ((hlogr.neg.sub hlogc).sub_const 2).const_mul v
  convert! hsum using 1 <;> dsimp [r, v] <;> field_simp <;> ring

/-- Concavity along a segment whose second endpoint has full support.  This
is the exact form first needed in the regularized-optimizer argument. -/
theorem vontobelSimplexEntropy_segment_concave
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p q : ι → ℝ} (hp : IsProbabilityVector p)
    (hq : IsStrictProbabilityVector q)
    (hcard : 1 < Fintype.card ι) :
    ConcaveOn ℝ (Set.Icc (0 : ℝ) 1)
      (fun t ↦ vontobelSimplexEntropy (probabilitySegment p q t)) := by
  let f : ℝ → ℝ := fun t ↦
    vontobelSimplexEntropy (probabilitySegment p q t)
  let f' : ℝ → ℝ := fun t ↦ ∑ i,
    (q i - p i) *
      (-Real.log (probabilitySegment p q t i) -
        Real.log (1 - probabilitySegment p q t i) - 2)
  let f'' : ℝ → ℝ := fun t ↦ ∑ i,
    ((q i - p i) ^ 2 / (1 - probabilitySegment p q t i) -
      (q i - p i) ^ 2 / probabilitySegment p q t i)
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc 0 1)
  · dsimp only [f, vontobelSimplexEntropy, vontobelEntropyTerm,
      probabilitySegment]
    fun_prop
  · intro t ht
    have ht' : t ∈ Set.Ioo (0 : ℝ) 1 := by simpa using ht
    have hr := probabilitySegment_strictProbability hp hq ht'.1 ht'.2
    have hlt := hr.lt_one_of_one_lt_card hcard
    apply (HasDerivAt.fun_sum fun i _ ↦
      hasDerivAt_vontobelEntropyTerm_segment p q i (hr.2 i) (hlt i)).hasDerivWithinAt
  · intro t ht
    have ht' : t ∈ Set.Ioo (0 : ℝ) 1 := by simpa using ht
    have hr := probabilitySegment_strictProbability hp hq ht'.1 ht'.2
    have hlt := hr.lt_one_of_one_lt_card hcard
    apply (HasDerivAt.fun_sum fun i _ ↦
      hasDerivAt_vontobelEntropyTerm_segment_deriv p q i (hr.2 i) (hlt i)).hasDerivWithinAt
  · intro t ht
    have ht' : t ∈ Set.Ioo (0 : ℝ) 1 := by simpa using ht
    have hr := probabilitySegment_strictProbability hp hq ht'.1 ht'.2
    have hlt := hr.lt_one_of_one_lt_card hcard
    have hsumv : ∑ i, (q i - p i) = 0 := by
      rw [Finset.sum_sub_distrib, hq.1.sum_eq_one, hp.sum_eq_one]
      ring
    simpa [f'', Finset.sum_sub_distrib] using
      vontobel_tangent_hessian_nonpos Finset.univ
        (probabilitySegment p q t) (fun i ↦ q i - p i)
        (fun i _ ↦ hr.2 i) (fun i _ ↦ hlt i)
        (by simpa using hr.1.sum_eq_one) (by simpa using hsumv)

@[simp] theorem probabilitySegment_zero
    {ι : Type*} (p q : ι → ℝ) :
    probabilitySegment p q 0 = p := by
  funext i
  simp [probabilitySegment]

@[simp] theorem probabilitySegment_one
    {ι : Type*} (p q : ι → ℝ) :
    probabilitySegment p q 1 = q := by
  funext i
  simp [probabilitySegment]

/-- Jensen form of Vontobel's entropy concavity when one endpoint has full
support. -/
theorem vontobelSimplexEntropy_segment_lower_of_right_strict
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p q : ι → ℝ} (hp : IsProbabilityVector p)
    (hq : IsStrictProbabilityVector q)
    (hcard : 1 < Fintype.card ι)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - t) * vontobelSimplexEntropy p +
        t * vontobelSimplexEntropy q ≤
      vontobelSimplexEntropy (probabilitySegment p q t) := by
  have hc := (vontobelSimplexEntropy_segment_concave hp hq hcard).2
    (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by simp)
    (show (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by simp)
    (sub_nonneg.mpr ht1) ht0 (by ring : (1 - t) + t = 1)
  simpa [probabilitySegment, smul_eq_mul] using hc

/-- The simplex entropy is continuous on the whole ambient finite-dimensional
space.  In particular, its boundary convention agrees with limits from the
relative interior of the simplex. -/
theorem continuous_vontobelSimplexEntropy
    {ι : Type*} [Fintype ι] :
    Continuous (vontobelSimplexEntropy : (ι → ℝ) → ℝ) := by
  unfold vontobelSimplexEntropy vontobelEntropyTerm
  apply continuous_finsetSum
  intro i _
  fun_prop

/-- Uniform probability vector on a nonempty finite type. -/
noncomputable def uniformProbabilityVector
    (ι : Type*) [Fintype ι] : ι → ℝ :=
  fun _ ↦ 1 / Fintype.card ι

theorem uniformProbabilityVector_strict
    {ι : Type*} [Fintype ι] [Nonempty ι] :
    IsStrictProbabilityVector (uniformProbabilityVector ι) := by
  have hcard : 0 < Fintype.card ι := Fintype.card_pos
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i
    exact div_nonneg zero_le_one (Nat.cast_nonneg _)
  · simp [uniformProbabilityVector, hcard.ne']
  · intro i
    exact div_pos zero_lt_one (by exact_mod_cast hcard)

/-- Full Jensen form of Vontobel's simplex-concavity theorem.  The proof
approximates the second endpoint by a full-support probability vector and
passes to the boundary using continuity. -/
theorem vontobelSimplexEntropy_segment_lower
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p q : ι → ℝ} (hp : IsProbabilityVector p)
    (hq : IsProbabilityVector q)
    (hcard : 1 < Fintype.card ι)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - t) * vontobelSimplexEntropy p +
        t * vontobelSimplexEntropy q ≤
      vontobelSimplexEntropy (probabilitySegment p q t) := by
  letI : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  let u : ι → ℝ := uniformProbabilityVector ι
  let qs : ℝ → ι → ℝ := fun δ ↦ probabilitySegment q u δ
  let lhs : ℝ → ℝ := fun δ ↦
    (1 - t) * vontobelSimplexEntropy p +
      t * vontobelSimplexEntropy (qs δ)
  let rhs : ℝ → ℝ := fun δ ↦
    vontobelSimplexEntropy (probabilitySegment p (qs δ) t)
  have hu : IsStrictProbabilityVector u := by
    simpa [u] using (uniformProbabilityVector_strict (ι := ι))
  have hlhs : Continuous lhs := by
    have hqs : Continuous qs := by
      apply continuous_pi
      intro i
      dsimp [qs, probabilitySegment]
      fun_prop
    exact continuous_const.add
      (continuous_const.mul (continuous_vontobelSimplexEntropy.comp hqs))
  have hrhs : Continuous rhs := by
    have hsegment : Continuous
        (fun δ ↦ probabilitySegment p (qs δ) t) := by
      apply continuous_pi
      intro i
      dsimp [qs, probabilitySegment]
      fun_prop
    exact continuous_vontobelSimplexEntropy.comp hsegment
  have hlhs0 : lhs 0 =
      (1 - t) * vontobelSimplexEntropy p +
        t * vontobelSimplexEntropy q := by
    simp [lhs, qs]
  have hrhs0 : rhs 0 =
      vontobelSimplexEntropy (probabilitySegment p q t) := by
    simp [rhs, qs]
  rw [← hlhs0, ← hrhs0]
  letI : Filter.NeBot (nhdsWithin (0 : ℝ) (Set.Ioi 0)) :=
    nhdsGT_neBot (0 : ℝ)
  refine le_of_tendsto_of_tendsto (b := nhdsWithin (0 : ℝ) (Set.Ioi 0))
    (hlhs.tendsto 0 |>.mono_left nhdsWithin_le_nhds)
    (hrhs.tendsto 0 |>.mono_left nhdsWithin_le_nhds) ?_
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono
      nhdsWithin_le_nhds] with δ hδpos hδone
  have hqs : IsStrictProbabilityVector (qs δ) := by
    exact probabilitySegment_strictProbability hq hu hδpos hδone
  exact vontobelSimplexEntropy_segment_lower_of_right_strict
    hp hqs hcard ht0 ht1

theorem betheRowObjective_eq_linear_add_vontobelEntropy
    {ι : Type*} [Fintype ι]
    (A X : Matrix ι ι ℝ) (i : ι) :
    betheRowObjective A X i =
      (∑ j, X i j * Real.log (A i j)) +
        vontobelSimplexEntropy (X i) := by
  classical
  simp only [betheRowObjective, vontobelSimplexEntropy,
    vontobelEntropyTerm, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Real.negMulLog]
  have hneg :
      (∑ j, -(1 - X i j) * Real.log (1 - X i j)) =
        -(∑ j, (1 - X i j) * Real.log (1 - X i j)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hneg]
  ring

/-- Matrix segment written rowwise. -/
def betheMatrixSegment
    {ι : Type*} (t : ℝ) (X Y : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  fun i ↦ probabilitySegment (X i) (Y i) t

/-- Jensen inequality for the Bethe objective on the Birkhoff polytope. -/
theorem betheObjective_segment_lower
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hcard : 1 < Fintype.card ι)
    (A X Y : Matrix ι ι ℝ)
    (hX : IsDoublyStochastic X) (hY : IsDoublyStochastic Y)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - t) * betheObjective A X + t * betheObjective A Y ≤
      betheObjective A (betheMatrixSegment t X Y) := by
  classical
  simp_rw [betheObjective, betheRowObjective_eq_linear_add_vontobelEntropy,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  have hentropy := vontobelSimplexEntropy_segment_lower
    (hX.row_probability i)
    (hY.row_probability i) hcard ht0 ht1
  have hentropy' :
      (1 - t) * vontobelSimplexEntropy (X i) +
          t * vontobelSimplexEntropy (Y i) ≤
        vontobelSimplexEntropy (betheMatrixSegment t X Y i) := by
    simpa only [betheMatrixSegment] using hentropy
  have hlinear :
      (1 - t) * (∑ j, X i j * Real.log (A i j)) +
          t * (∑ j, Y i j * Real.log (A i j)) =
        ∑ j, betheMatrixSegment t X Y i j * Real.log (A i j) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    simp only [betheMatrixSegment, probabilitySegment]
    ring
  rw [← hlinear]
  linarith

/-- The Birkhoff polytope is convex. -/
theorem convex_doublyStochastic
    {ι : Type*} [Fintype ι] :
    Convex ℝ {X : Matrix ι ι ℝ | IsDoublyStochastic X} := by
  rw [convex_iff_add_mem]
  intro X hX Y hY a b ha hb hab
  change IsDoublyStochastic
    (fun i j ↦ a * X i j + b * Y i j)
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    exact add_nonneg
      (mul_nonneg ha (hX.nonnegative i j))
      (mul_nonneg hb (hY.nonnegative i j))
  · intro i
    simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum,
      hX.row_sum, hY.row_sum]
    simpa using hab
  · intro j
    simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum,
      hX.col_sum, hY.col_sum]
    simpa using hab

/-- Vontobel's full Bethe-concavity theorem, including boundary points of the
Birkhoff polytope. -/
theorem vontobelBetheConcavity : VontobelBetheConcavity := by
  intro ι _ A _hA
  classical
  refine ⟨convex_doublyStochastic, ?_⟩
  intro X hX Y hY a b ha hb hab
  by_cases hcard : 1 < Fintype.card ι
  · have hble : b ≤ 1 := by linarith
    have hjensen := betheObjective_segment_lower hcard A X Y hX hY hb hble
    have haeq : a = 1 - b := by linarith
    rw [haeq]
    have hmatrix :
        (1 - b) • X + b • Y = betheMatrixSegment b X Y := by
      funext i j
      change (1 - b) * X i j + b * Y i j =
        (1 - b) * X i j + b * Y i j
      rfl
    simpa [smul_eq_mul, hmatrix] using hjensen
  · have hsmall : Fintype.card ι ≤ 1 := Nat.le_of_not_gt hcard
    letI : Subsingleton ι := Fintype.card_le_one_iff_subsingleton.mp hsmall
    have hXY : X = Y := by
      ext i j
      have hx := hX.row_sum i
      have hy := hY.row_sum i
      have huniv : (Finset.univ : Finset ι) = {j} := by
        ext k
        simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
        exact Subsingleton.elim k j
      rw [huniv] at hx hy
      simpa using hx.trans hy.symm
    subst Y
    rw [Convex.combo_self hab, Convex.combo_self hab]

end BeyondBethe
