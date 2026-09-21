/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.V7.Proofs.Stage5AboveTwoLowerS5A2Envelope.SymmetryLinearization

namespace V7.Stage5AboveTwoLowerS5A2Envelope

open scoped BigOperators
open Stage5AboveTwoLower.S5ARepair

lemma signedLpSymmetry_lpPower {p : ℝ} (hp : 2 < p)
    {Q Qdual : Point d → Point d} (hsym : SignedLpSymmetry p Q Qdual)
    (x : Point d) : O3.lpPower p (Q x) = O3.lpPower p x := by
  rw [← O3.Stage2RouteB.lpNorm_rpow_eq_lpPower (by linarith : p ≠ 0),
    ← O3.Stage2RouteB.lpNorm_rpow_eq_lpPower (by linarith : p ≠ 0)]
  have hn := hsym.1 x
  change O3.lpNorm p (Q x) = O3.lpNorm p x at hn
  rw [hn]

lemma hasDerivAt_lpPower_line {p : ℝ} (hp : 2 < p)
    (x h : Point d) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ O3.lpPower p (x + s • h))
      (p * O3.Stage2RouteA.linePowerPair p x h t) t := by
  have hline : HasDerivAt (fun s : ℝ ↦ x + s • h) h t := by
    simpa using ((hasDerivAt_id t).smul_const h).const_add x
  have hc := (hasFDerivAt_lpPower (by linarith : 1 < p) (x + t • h)).comp
    t hline.hasFDerivAt
  simpa [lpPowerFDeriv, pairingCLM_apply,
    O3.Stage2RouteA.linePowerPair, Function.comp_def] using hc.hasDerivAt

lemma signedLpSymmetry_linePowerPair {p : ℝ} (hp : 2 < p)
    {Q Qdual : Point d → Point d} (hsym : SignedLpSymmetry p Q Qdual)
    (x h : Point d) :
    O3.Stage2RouteA.linePowerPair p (Q x) (Q h) =
      O3.Stage2RouteA.linePowerPair p x h := by
  funext t
  have hfun : (fun s : ℝ ↦ O3.lpPower p (Q x + s • Q h)) =
      (fun s : ℝ ↦ O3.lpPower p (x + s • h)) := by
    funext s
    have hQs : Q (x + s • h) = Q x + s • Q h := by
      rw [signedLpSymmetry_Q_add hsym, signedLpSymmetry_Q_smul hsym]
    rw [← hQs]
    exact signedLpSymmetry_lpPower hp hsym (x + s • h)
  have hleft := hasDerivAt_lpPower_line hp (Q x) (Q h) t
  have hright := hasDerivAt_lpPower_line hp x h t
  rw [hfun] at hleft
  have heq := hleft.unique hright
  exact (mul_left_cancel₀ (by linarith : p ≠ 0)) heq

/-- Distinct columns of a frozen signed `ell_p` symmetry have disjoint
coordinate support.  The proof differentiates the preserved `p`-power twice
at a coordinate vector; this avoids importing a packaged Lamperti theorem. -/
lemma signedLpSymmetry_columns_disjoint {p : ℝ} (hp : 2 < p)
    {Q Qdual : Point d → Point d} (hsym : SignedLpSymmetry p Q Qdual)
    {i j : Fin d} (hij : i ≠ j) (k : Fin d) :
    Q (coordinateUnit i) k = 0 ∨ Q (coordinateUnit j) k = 0 := by
  let ui := Q (coordinateUnit i)
  let uj := Q (coordinateUnit j)
  have hpairfun := signedLpSymmetry_linePowerPair hp hsym
    (coordinateUnit i) (coordinateUnit j)
  have hleft := O3.Stage2RouteA.hasDerivAt_linePowerPair_above_two hp ui uj 0
  have hright := O3.Stage2RouteA.hasDerivAt_linePowerPair_above_two hp
    (coordinateUnit i) (coordinateUnit j) 0
  have hfun : O3.Stage2RouteA.linePowerPair p ui uj =
      O3.Stage2RouteA.linePowerPair p (coordinateUnit i) (coordinateUnit j) := by
    simpa [ui, uj] using hpairfun
  rw [hfun] at hleft
  have heq := hleft.unique hright
  have hrightZero : O3.Stage2RouteA.weightedSquareSum p
      (coordinateUnit i) (coordinateUnit j) 0 = 0 := by
    unfold O3.Stage2RouteA.weightedSquareSum
    apply Finset.sum_eq_zero
    intro m _
    by_cases hmi : m = i
    · subst m
      simp [coordinateUnit, hij]
    · simp [coordinateUnit, hmi, Real.zero_rpow (by linarith : p - 2 ≠ 0)]
  rw [hrightZero, mul_zero] at heq
  have hsum : O3.Stage2RouteA.weightedSquareSum p ui uj 0 = 0 := by
    exact (mul_eq_zero.mp heq).resolve_left (by linarith : p - 1 ≠ 0)
  have hterm : |ui k| ^ (p - 2) * (uj k) ^ (2 : ℕ) = 0 := by
    have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun m _ ↦
      mul_nonneg (Real.rpow_nonneg (abs_nonneg (ui m)) _)
        (sq_nonneg (uj m)))).mp (by simpa [O3.Stage2RouteA.weightedSquareSum] using hsum)
    exact hall k (Finset.mem_univ k)
  rcases mul_eq_zero.mp hterm with hui | huj
  · left
    exact abs_eq_zero.mp ((Real.rpow_eq_zero (abs_nonneg (ui k))
      (by linarith : p - 2 ≠ 0)).mp hui)
  · right
    exact sq_eq_zero_iff.mp huj

lemma lpPower_coordinateUnit (p : ℝ) (hp : p ≠ 0) (i : Fin d) :
    O3.lpPower p (coordinateUnit i) = 1 := by
  unfold O3.lpPower
  rw [Finset.sum_eq_single i]
  · simp [coordinateUnit, Real.one_rpow]
  · intro j _ hji
    simp [coordinateUnit, hji, Real.zero_rpow hp]
  · intro hi
    exact (hi (Finset.mem_univ _)).elim

lemma lpNorm_coordinateUnit {p : ℝ} (hp : 0 < p) (i : Fin d) :
    O3.lpNorm p (coordinateUnit i) = 1 := by
  unfold O3.lpNorm
  rw [lpPower_coordinateUnit p hp.ne' i]
  exact Real.one_rpow _

lemma signedLpSymmetry_column_ne_zero {p : ℝ} (hp : 2 < p)
    {Q Qdual : Point d → Point d} (hsym : SignedLpSymmetry p Q Qdual)
    (i : Fin d) : Q (coordinateUnit i) ≠ 0 := by
  intro hz
  have hn := hsym.1 (coordinateUnit i)
  change O3.lpNorm p (Q (coordinateUnit i)) =
    O3.lpNorm p (coordinateUnit i) at hn
  rw [hz, O3.lpNorm_zero (by linarith), lpNorm_coordinateUnit (by linarith) i] at hn
  norm_num at hn

noncomputable def signedLpColumnIndex {p : ℝ} (hp : 2 < p)
    (Q Qdual : Point d → Point d) (hsym : SignedLpSymmetry p Q Qdual)
    (i : Fin d) : Fin d :=
  Classical.choose (Function.ne_iff.mp
    (signedLpSymmetry_column_ne_zero hp hsym i))

lemma signedLpColumnIndex_spec {p : ℝ} (hp : 2 < p)
    {Q Qdual : Point d → Point d} (hsym : SignedLpSymmetry p Q Qdual)
    (i : Fin d) :
    Q (coordinateUnit i) (signedLpColumnIndex hp Q Qdual hsym i) ≠ 0 :=
  Classical.choose_spec (Function.ne_iff.mp
    (signedLpSymmetry_column_ne_zero hp hsym i))

lemma signedLpColumnIndex_injective {p : ℝ} (hp : 2 < p)
    {Q Qdual : Point d → Point d} (hsym : SignedLpSymmetry p Q Qdual) :
    Function.Injective (signedLpColumnIndex hp Q Qdual hsym) := by
  intro i j hijIndex
  by_contra hij
  have hdis := signedLpSymmetry_columns_disjoint hp hsym hij
    (signedLpColumnIndex hp Q Qdual hsym i)
  rcases hdis with hi | hj
  · exact (signedLpColumnIndex_spec hp hsym i) hi
  · have hjs := signedLpColumnIndex_spec hp hsym j
    rw [← hijIndex] at hjs
    exact hjs hj

lemma signedLpColumnIndex_surjective {p : ℝ} (hp : 2 < p)
    {Q Qdual : Point d → Point d} (hsym : SignedLpSymmetry p Q Qdual) :
    Function.Surjective (signedLpColumnIndex hp Q Qdual hsym) :=
  Finite.surjective_of_injective (signedLpColumnIndex_injective hp hsym)

lemma signedLpSymmetry_column_off_index {p : ℝ} (hp : 2 < p)
    {Q Qdual : Point d → Point d} (hsym : SignedLpSymmetry p Q Qdual)
    {i : Fin d} {k : Fin d}
    (hk : k ≠ signedLpColumnIndex hp Q Qdual hsym i) :
    Q (coordinateUnit i) k = 0 := by
  obtain ⟨j, rfl⟩ := signedLpColumnIndex_surjective hp hsym k
  by_contra hnon
  have hij : i ≠ j := by
    intro hij
    subst j
    exact hk rfl
  have hdis := signedLpSymmetry_columns_disjoint hp hsym hij
    (signedLpColumnIndex hp Q Qdual hsym j)
  exact hdis.elim (fun hi ↦ hnon hi)
    (fun hj ↦ (signedLpColumnIndex_spec hp hsym j) hj)

lemma signedLpSymmetry_column_abs_at_index {p : ℝ} (hp : 2 < p)
    {Q Qdual : Point d → Point d} (hsym : SignedLpSymmetry p Q Qdual)
    (i : Fin d) :
    |Q (coordinateUnit i) (signedLpColumnIndex hp Q Qdual hsym i)| = 1 := by
  have hpower := signedLpSymmetry_lpPower hp hsym (coordinateUnit i)
  have hsum : ∑ k, |Q (coordinateUnit i) k| ^ p = 1 := by
    change (∑ k, |Q (coordinateUnit i) k| ^ p) =
      O3.lpPower p (coordinateUnit i) at hpower
    rw [lpPower_coordinateUnit p (by linarith) i] at hpower
    exact hpower
  have hsingle : |Q (coordinateUnit i)
      (signedLpColumnIndex hp Q Qdual hsym i)| ^ p = 1 := by
    rw [← hsum]
    symm
    apply Finset.sum_eq_single (signedLpColumnIndex hp Q Qdual hsym i)
    · intro k _ hk
      rw [signedLpSymmetry_column_off_index hp hsym hk]
      simp [Real.zero_rpow (by linarith : p ≠ 0)]
    · intro hnot
      exact (hnot (Finset.mem_univ _)).elim
  have honepow : (1 : ℝ) ^ p = 1 := Real.one_rpow _
  exact (Real.rpow_left_inj (abs_nonneg _) zero_le_one
    (by linarith : p ≠ 0)).mp (by simpa [honepow] using hsingle)

def signedLpLinearMap {p : ℝ}
    (Q Qdual : Point d → Point d) (hsym : SignedLpSymmetry p Q Qdual) :
    Point d →ₗ[ℝ] Point d where
  toFun := Q
  map_add' := signedLpSymmetry_Q_add hsym
  map_smul' := signedLpSymmetry_Q_smul hsym

lemma point_eq_sum_coordinateUnit (x : Point d) :
    x = ∑ i, x i • coordinateUnit i := by
  funext k
  simp [coordinateUnit]

/-- Every frozen signed `ell_p` symmetry preserves every coordinate `r`-power,
not only the physical `p`-power. -/
theorem signedLpSymmetry_lpPower_all {p r : ℝ} (hp : 2 < p)
    {Q Qdual : Point d → Point d} (hsym : SignedLpSymmetry p Q Qdual)
    (x : Point d) : O3.lpPower r (Q x) = O3.lpPower r x := by
  let σ := signedLpColumnIndex hp Q Qdual hsym
  have hσinj : Function.Injective σ := signedLpColumnIndex_injective hp hsym
  have hQsum : Q x = ∑ i, x i • Q (coordinateUnit i) := by
    have hm := congrArg (signedLpLinearMap Q Qdual hsym) (point_eq_sum_coordinateUnit x)
    simpa [signedLpLinearMap] using hm
  unfold O3.lpPower
  rw [hQsum]
  symm
  apply Finset.sum_bij (fun i _ ↦ σ i)
  · intro i _
    exact Finset.mem_univ _
  · intro i _ j _ hij
    exact hσinj hij
  · intro k _
    obtain ⟨i, hi⟩ := signedLpColumnIndex_surjective hp hsym k
    exact ⟨i, Finset.mem_univ _, hi⟩
  · intro i _
    have hoff : ∀ j ≠ i, Q (coordinateUnit j) (σ i) = 0 := by
      intro j hji
      apply signedLpSymmetry_column_off_index hp hsym
      intro heq
      exact hji (hσinj heq).symm
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single i]
    · rw [abs_mul, signedLpSymmetry_column_abs_at_index hp hsym i, mul_one]
    · intro j _ hji
      rw [hoff j hji]
      simp
    · intro hi
      exact (hi (Finset.mem_univ _)).elim

theorem signedLpSymmetry_lpNorm_all {p r : ℝ} (hp : 2 < p)
    {Q Qdual : Point d → Point d} (hsym : SignedLpSymmetry p Q Qdual)
    (x : Point d) : O3.lpNorm r (Q x) = O3.lpNorm r x := by
  unfold O3.lpNorm
  rw [signedLpSymmetry_lpPower_all hp hsym]

end V7.Stage5AboveTwoLowerS5A2Envelope
