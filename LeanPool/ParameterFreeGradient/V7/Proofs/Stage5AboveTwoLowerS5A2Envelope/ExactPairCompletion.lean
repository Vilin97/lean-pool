/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/
module


public import LeanPool.ParameterFreeGradient.V7.Proofs.Stage5AboveTwoLowerS5A2Envelope.Construction

/-!
The completed resisting oracle preserves all earlier exact value-gradient observations.
-/

@[expose] public section

namespace V7.Stage5AboveTwoLowerS5A2Envelope

open Stage5AboveTwoLower
open Stage5AboveTwoLower.S5AFinalRepair

private def piece (data : LowerCompletionData p d T) (i : ℕ) (x : Point d) : ℝ :=
  data.xi i * x (data.sigma i) - (i : ℝ) * data.delta

lemma partialG_convex (data : LowerCompletionData p d T) {t : ℕ}
    (ht : t < T)
    (hsteps : ∀ s < T, (data.xi s = 1 ∨ data.xi s = -1) ∧
      ResistingMaximumAt data s) :
    O3.IsConvexObjective (data.partialG t) := by
  unfold O3.IsConvexObjective
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  obtain ⟨i, hit, hiz⟩ := (hsteps t ht).2 (a • x + b • y) |>.2
  have hix := ((hsteps t ht).2 x).1 i hit
  have hiy := ((hsteps t ht).2 y).1 i hit
  rw [hiz]
  dsimp [piece] at hix hiy ⊢
  have hconst := congrArg (fun c : ℝ ↦ c * ((i : ℝ) * data.delta)) hab
  nlinarith

lemma partialG_oneLipschitz (data : LowerCompletionData p d T)
    {t : ℕ} (hp : 1 ≤ p) (ht : t < T)
    (hsteps : ∀ s < T, (data.xi s = 1 ∨ data.xi s = -1) ∧
      ResistingMaximumAt data s) :
    IsOneLipschitz p (data.partialG t) := by
  intro x y
  obtain ⟨i, hit, hix⟩ := ((hsteps t ht).2 x).2
  obtain ⟨j, hjt, hjy⟩ := ((hsteps t ht).2 y).2
  have hiy := ((hsteps t ht).2 y).1 i hit
  have hjx := ((hsteps t ht).2 x).1 j hjt
  have hxi := (hsteps i (lt_of_le_of_lt hit ht)).1
  have hxj := (hsteps j (lt_of_le_of_lt hjt ht)).1
  have hcoordI := norm_apply_le_lpNorm hp (x - y) (data.sigma i)
  have hcoordJ := norm_apply_le_lpNorm hp (x - y) (data.sigma j)
  change |x (data.sigma i) - y (data.sigma i)| ≤ lpNorm p (x - y) at hcoordI
  change |x (data.sigma j) - y (data.sigma j)| ≤ lpNorm p (x - y) at hcoordJ
  have hupper : data.partialG t x - data.partialG t y ≤ lpNorm p (x - y) := by
    rw [hix]
    rcases hxi with hxi | hxi <;> rw [hxi] at hiy ⊢
    · norm_num at hiy ⊢
      linarith [le_abs_self (x (data.sigma i) - y (data.sigma i))]
    · norm_num at hiy ⊢
      linarith [neg_le_abs (x (data.sigma i) - y (data.sigma i))]
  have hlower : -(lpNorm p (x - y)) ≤
      data.partialG t x - data.partialG t y := by
    rw [hjy]
    rcases hxj with hxj | hxj <;> rw [hxj] at hjx ⊢
    · norm_num at hjx ⊢
      linarith [neg_le_abs (x (data.sigma j) - y (data.sigma j))]
    · norm_num at hjx ⊢
      linarith [le_abs_self (x (data.sigma j) - y (data.sigma j))]
  exact (abs_le.2 ⟨hlower, hupper⟩)

lemma partialH_convex_oneLipschitz (data : LowerCompletionData p d T)
    {t : ℕ} (hp : 1 ≤ p) (ht : t < T)
    (hsteps : ∀ s < T, (data.xi s = 1 ∨ data.xi s = -1) ∧
      ResistingMaximumAt data s)
    (hH : ∀ x, data.partialH t x =
      max (data.partialG t x / 2) (lpNorm p x - 3 / 2)) :
    O3.IsConvexObjective (data.partialH t) ∧
      IsOneLipschitz p (data.partialH t) := by
  have hGconv := partialG_convex data ht hsteps
  have hGlip := partialG_oneLipschitz data hp ht hsteps
  have hNconv := convexOn_lpNorm (d := d) hp
  constructor
  · unfold O3.IsConvexObjective at hGconv ⊢
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b ha hb hab
    rw [hH, hH, hH]
    apply max_le
    · have hg := hGconv.2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab
      have hxmax := le_max_left (data.partialG t x / 2) (lpNorm p x - 3 / 2)
      have hymax := le_max_left (data.partialG t y / 2) (lpNorm p y - 3 / 2)
      simp only [smul_eq_mul] at hg ⊢
      nlinarith
    · have hn := hNconv.2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab
      have hxmax := le_max_right (data.partialG t x / 2) (lpNorm p x - 3 / 2)
      have hymax := le_max_right (data.partialG t y / 2) (lpNorm p y - 3 / 2)
      have hconst := congrArg (fun c : ℝ ↦ c * (3 / 2 : ℝ)) hab
      simp only [smul_eq_mul] at hn ⊢
      nlinarith
  · intro x y
    rw [hH, hH]
    refine (abs_max_sub_max_le_max _ _ _ _).trans (max_le ?_ ?_)
    · have hg := hGlip x y
      have hn := O3.lpNorm_nonneg p (x - y)
      rw [show data.partialG t x / 2 - data.partialG t y / 2 =
        (data.partialG t x - data.partialG t y) / 2 by ring]
      rw [abs_div]
      norm_num
      nlinarith
    · have hxy := lpNorm_add_le hp (x - y) y
      have hyx := lpNorm_add_le hp (y - x) x
      have hneg : lpNorm p (y - x) = lpNorm p (x - y) := by
        rw [show y - x = -(x - y) by module]
        change O3.lpNorm p (-(x - y)) = O3.lpNorm p (x - y)
        simpa using O3.Stage2RouteC.lpNorm_smul hp (-1 : ℝ) (x - y)
      rw [show x - y + y = x by module] at hxy
      rw [show y - x + x = y by module, hneg] at hyx
      rw [show lpNorm p x - 3 / 2 - (lpNorm p y - 3 / 2) =
        lpNorm p x - lpNorm p y by ring]
      exact abs_le.2 ⟨by linarith, by linarith⟩

lemma future_piece_le_at_nearby_query (data : LowerCompletionData p d T)
    (hp : 1 ≤ p) (hdelta : 0 < data.delta)
    (hchi : data.delta = 2 * data.chi)
    (hsteps : ∀ s < T, (∀ r < s, data.sigma r ≠ data.sigma s) ∧
      (data.sigma s).val < T ∧
      (∀ j : Fin d, j.val < T → (∀ r < s, data.sigma r ≠ j) →
        |data.queries s j| ≤ |data.queries s (data.sigma s)|) ∧
      (data.xi s = 1 ∨ data.xi s = -1) ∧
      data.xi s * data.queries s (data.sigma s) =
        |data.queries s (data.sigma s)| ∧
      ResistingMaximumAt data s ∧
      (∀ x, data.partialH s x =
        max (data.partialG s x / 2) (lpNorm p x - 3 / 2)) ∧
      (∀ x, (data.partialOracle s).value x =
        data.beta * (data.kernel.smooth data.chi (data.partialH s)).value x) ∧
      (∀ x, (data.partialOracle s).gradient x =
        data.beta • (data.kernel.smooth data.chi (data.partialH s)).gradient x))
    {t i : ℕ} (ht : t < T) (hi : i < T) (hti : t < i)
    (v : Point d) (hv : lpNorm p v ≤ data.chi) :
    data.xi i * (data.queries t + v) (data.sigma i) - (i : ℝ) * data.delta ≤
      data.xi t * (data.queries t + v) (data.sigma t) - (t : ℝ) * data.delta := by
  obtain ⟨hdistT, hvalT, hmaxT, hxiT, hsignT, -⟩ := hsteps t ht
  obtain ⟨hdistI, hvalI, -, hxiI, -, -⟩ := hsteps i hi
  have hunused : ∀ r < t, data.sigma r ≠ data.sigma i := by
    intro r hrt
    exact hdistI r (lt_trans hrt hti)
  have habsI : |data.queries t (data.sigma i)| ≤
      |data.queries t (data.sigma t)| := hmaxT (data.sigma i) hvalI hunused
  have hcoordI := norm_apply_le_lpNorm hp v (data.sigma i)
  have hcoordT := norm_apply_le_lpNorm hp v (data.sigma t)
  have hvI : data.xi i * v (data.sigma i) ≤ data.chi := by
    rcases hxiI with hxiI | hxiI <;> rw [hxiI]
    · norm_num
      exact (le_abs_self _).trans (hcoordI.trans hv)
    · norm_num
      exact (neg_le_abs _).trans (hcoordI.trans hv)
  have hvT : -data.chi ≤ data.xi t * v (data.sigma t) := by
    rcases hxiT with hxiT | hxiT <;> rw [hxiT]
    · norm_num
      linarith [neg_le_abs (v (data.sigma t)), hcoordT.trans hv]
    · norm_num
      linarith [le_abs_self (v (data.sigma t)), hcoordT.trans hv]
  have hqI : data.xi i * data.queries t (data.sigma i) ≤
      |data.queries t (data.sigma i)| := by
    rcases hxiI with hxiI | hxiI <;> rw [hxiI]
    · norm_num; exact le_abs_self _
    · norm_num; exact neg_le_abs _
  have hcast : (t : ℝ) + 1 ≤ (i : ℝ) := by exact_mod_cast (Nat.succ_le_iff.2 hti)
  have hoffset : (t : ℝ) * data.delta + data.delta ≤
      (i : ℝ) * data.delta := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hcast) (le_of_lt hdelta)]
  simp only [Pi.add_apply]
  nlinarith

lemma partialG_final_eq_at_nearby_query (data : LowerCompletionData p d T)
    (hp : 1 ≤ p) (hT : 1 ≤ T) (hdelta : 0 < data.delta)
    (hchi : data.delta = 2 * data.chi)
    (hsteps : ∀ s < T, (∀ r < s, data.sigma r ≠ data.sigma s) ∧
      (data.sigma s).val < T ∧
      (∀ j : Fin d, j.val < T → (∀ r < s, data.sigma r ≠ j) →
        |data.queries s j| ≤ |data.queries s (data.sigma s)|) ∧
      (data.xi s = 1 ∨ data.xi s = -1) ∧
      data.xi s * data.queries s (data.sigma s) =
        |data.queries s (data.sigma s)| ∧
      ResistingMaximumAt data s ∧
      (∀ x, data.partialH s x =
        max (data.partialG s x / 2) (lpNorm p x - 3 / 2)) ∧
      (∀ x, (data.partialOracle s).value x =
        data.beta * (data.kernel.smooth data.chi (data.partialH s)).value x) ∧
      (∀ x, (data.partialOracle s).gradient x =
        data.beta • (data.kernel.smooth data.chi (data.partialH s)).gradient x))
    {t : ℕ} (ht : t < T) (v : Point d) (hv : lpNorm p v ≤ data.chi) :
    data.partialG (T - 1) (data.queries t + v) =
      data.partialG t (data.queries t + v) := by
  have hlast : T - 1 < T := by omega
  have htlast : t ≤ T - 1 := by omega
  let y := data.queries t + v
  have hresT := (hsteps t ht).2.2.2.2.2.1 y
  have hresLast := (hsteps (T - 1) hlast).2.2.2.2.2.1 y
  apply le_antisymm
  · obtain ⟨i, hiLast, hiEq⟩ := hresLast.2
    rw [hiEq]
    by_cases hit : i ≤ t
    · exact hresT.1 i hit
    · have hti : t < i := Nat.lt_of_not_ge hit
      exact (future_piece_le_at_nearby_query data hp hdelta hchi hsteps
        ht (lt_of_le_of_lt hiLast hlast) hti v hv).trans (hresT.1 t le_rfl)
  · obtain ⟨i, hit, hiEq⟩ := hresT.2
    rw [hiEq]
    exact hresLast.1 i (hit.trans htlast)

lemma partialH_final_eq_at_nearby_query (data : LowerCompletionData p d T)
    (hp : 1 ≤ p) (hT : 1 ≤ T) (hdelta : 0 < data.delta)
    (hchi : data.delta = 2 * data.chi)
    (hsteps : ∀ s < T, (∀ r < s, data.sigma r ≠ data.sigma s) ∧
      (data.sigma s).val < T ∧
      (∀ j : Fin d, j.val < T → (∀ r < s, data.sigma r ≠ j) →
        |data.queries s j| ≤ |data.queries s (data.sigma s)|) ∧
      (data.xi s = 1 ∨ data.xi s = -1) ∧
      data.xi s * data.queries s (data.sigma s) =
        |data.queries s (data.sigma s)| ∧
      ResistingMaximumAt data s ∧
      (∀ x, data.partialH s x =
        max (data.partialG s x / 2) (lpNorm p x - 3 / 2)) ∧
      (∀ x, (data.partialOracle s).value x =
        data.beta * (data.kernel.smooth data.chi (data.partialH s)).value x) ∧
      (∀ x, (data.partialOracle s).gradient x =
        data.beta • (data.kernel.smooth data.chi (data.partialH s)).gradient x))
    {t : ℕ} (ht : t < T) (v : Point d) (hv : lpNorm p v ≤ data.chi) :
    data.partialH (T - 1) (data.queries t + v) =
      data.partialH t (data.queries t + v) := by
  have hlast : T - 1 < T := by omega
  rw [(hsteps (T - 1) hlast).2.2.2.2.2.2.1,
    (hsteps t ht).2.2.2.2.2.2.1]
  rw [partialG_final_eq_at_nearby_query data hp hT hdelta hchi hsteps ht v hv]

/-- Frozen S5-B: the completed oracle returns exactly the same value-gradient
pair as the chronological partial oracle at every counted query. -/
theorem _root_.V7.aboveLowerExactPairCompletion : AboveLowerExactPairCompletionStatement := by
  intro p hp d T data hassum t ht
  rcases hassum with
    ⟨hp', hd, hT, hTd, hx0, hkernel, hDelta, hdelta, hchi, hbeta,
      hqueries, hsteps, hcompletedValue, hcompletedGradient⟩
  have hpOne : 1 ≤ p := by linarith
  have hTreal : 0 < (T : ℝ) := by exact_mod_cast hT
  have hDeltaPos : 0 < data.Delta := by
    rw [hDelta]
    exact Real.rpow_pos_of_pos hTreal _
  have hdeltaPos : 0 < data.delta := by
    rw [hdelta]
    positivity
  have hchiPos : 0 < data.chi := by
    rw [hchi]
    positivity
  have hdeltachi : data.delta = 2 * data.chi := by
    rw [hchi]
    ring
  have hlast : T - 1 < T := by omega
  let shortSteps : ∀ s < T,
      (data.xi s = 1 ∨ data.xi s = -1) ∧ ResistingMaximumAt data s :=
    fun s hs => ⟨(hsteps s hs).2.2.2.1, (hsteps s hs).2.2.2.2.2.1⟩
  have hpartialLast := partialH_convex_oneLipschitz data hpOne hlast shortSteps
    (hsteps (T - 1) hlast).2.2.2.2.2.2.1
  have hpartialT := partialH_convex_oneLipschitz data hpOne ht shortSteps
    (hsteps t ht).2.2.2.2.2.2.1
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hlocal, -⟩ := hkernel
  have hsmoothObserve := hlocal data.chi hchiPos
    (data.partialH (T - 1)) (data.partialH t)
    hpartialLast.1 hpartialLast.2 hpartialT.1 hpartialT.2 (data.queries t)
    (fun v hv => partialH_final_eq_at_nearby_query data hpOne hT hdeltaPos
      hdeltachi hsteps ht v hv)
  have hsmoothValue := congrArg O3.Observation.value hsmoothObserve
  have hsmoothGradient := congrArg O3.Observation.gradient hsmoothObserve
  change (data.kernel.smooth data.chi (data.partialH (T - 1))).value
      (data.queries t) =
    (data.kernel.smooth data.chi (data.partialH t)).value
      (data.queries t) at hsmoothValue
  change (data.kernel.smooth data.chi (data.partialH (T - 1))).gradient
      (data.queries t) =
    (data.kernel.smooth data.chi (data.partialH t)).gradient
      (data.queries t) at hsmoothGradient
  change (⟨data.queries t, data.completedOracle.value (data.queries t),
      data.completedOracle.gradient (data.queries t)⟩ : O3.Observation d) =
    ⟨data.queries t, (data.partialOracle t).value (data.queries t),
      (data.partialOracle t).gradient (data.queries t)⟩
  rw [O3.Observation.mk.injEq]
  refine ⟨rfl, ?_, ?_⟩
  · rw [hcompletedValue, (hsteps t ht).2.2.2.2.2.2.2.1]
    exact congrArg (fun z : ℝ => data.beta * z) hsmoothValue
  · rw [hcompletedGradient, (hsteps t ht).2.2.2.2.2.2.2.2]
    exact congrArg (fun z : Point d => data.beta • z) hsmoothGradient

end V7.Stage5AboveTwoLowerS5A2Envelope
