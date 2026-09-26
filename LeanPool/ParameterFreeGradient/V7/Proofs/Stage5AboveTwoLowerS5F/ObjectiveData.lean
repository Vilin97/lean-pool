/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/
module


public import LeanPool.ParameterFreeGradient.V7.Proofs.Stage5AboveTwoLowerS5F.CompletionData

/-!
The normalized completion is a convex objective with the stated coordinate gradient.
-/

@[expose] public section

namespace V7.Stage5AboveTwoLowerS5F

open Stage5AboveTwoLower
open Stage5AboveTwoLower.S5ARepair
open Stage5AboveTwoLowerS5A2Envelope

/-- The normalized separation scale `T ^ (-1 / p)`. -/
noncomputable def unitDelta (p : ℝ) (T : ℕ) : ℝ := (T : ℝ) ^ (-1 / p)
/-- The affine-piece offset used in the normalized resisting construction. -/
noncomputable def unitDeltaStep (p : ℝ) (T : ℕ) : ℝ := unitDelta p T / (2 * T)
/-- The smoothing scale, equal to half the normalized affine-piece offset. -/
noncomputable def unitChi (p : ℝ) (T : ℕ) : ℝ := unitDeltaStep p T / 2

/-- The explicit kernel and scales initializing the normalized resisting construction. -/
noncomputable def unitParameters (p : ℝ) (d T : ℕ)
    (algorithm : DeterministicExactPairAlgorithm d) (hT : 1 ≤ T) (hTd : T ≤ d) :
    PrefixParameters p d T :=
  { algorithm := algorithm
    kernel := repairKernel p d
    delta := unitDeltaStep p T
    chi := unitChi p T
    beta := unitChi p T / repairMpd p d
    T_pos := hT
    T_le_d := hTd }

lemma unitDelta_pos {p : ℝ} {T : ℕ} (hT : 1 ≤ T) : 0 < unitDelta p T := by
  unfold unitDelta
  positivity

lemma unitDeltaStep_pos {p : ℝ} {T : ℕ} (hT : 1 ≤ T) :
    0 < unitDeltaStep p T := by
  unfold unitDeltaStep
  have hTr : 0 < (T : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hT)
  exact div_pos (unitDelta_pos hT) (mul_pos (by norm_num) hTr)

lemma unitChi_pos {p : ℝ} {T : ℕ} (hT : 1 ≤ T) : 0 < unitChi p T := by
  unfold unitChi
  exact half_pos (unitDeltaStep_pos hT)

lemma unitBeta_pos {p : ℝ} {d T : ℕ} (hp : 2 < p) (hd : 2 ≤ d) (hT : 1 ≤ T) :
    0 < unitChi p T / repairMpd p d :=
  div_pos (unitChi_pos hT) (repairMpd_pos hp hd)

/-- The complete normalized resisting data for a deterministic algorithm. -/
noncomputable def unitCompletionData (p : ℝ) (d T : ℕ)
    (algorithm : DeterministicExactPairAlgorithm d) (hT : 1 ≤ T) (hTd : T ≤ d) :
    LowerCompletionData p d T :=
  completionData (unitParameters p d T algorithm hT hTd) (unitDelta p T)

theorem unitCompletionData_assumptions {p : ℝ} {d T : ℕ}
    (algorithm : DeterministicExactPairAlgorithm d)
    (hp : 2 < p) (hd : 2 ≤ d) (hT : 1 ≤ T) (hTd : T ≤ d) :
    LowerCompletionAssumptions (unitCompletionData p d T algorithm hT hTd) := by
  apply completionData_assumptions
  · exact hp
  · exact hd
  · exact repairKernel_assumptions hp hd
  · rfl
  · rfl
  · rfl
  · rfl

/-- A global supporting field implies convexity; this local wheel avoids any
packaged convex-envelope dependency. -/
lemma convexObjective_of_global_support (f : Point d → ℝ) (g : Point d → Point d)
    (hsupport : ∀ x y, f x + pairing (g x) (y - x) ≤ f y) :
    O3.IsConvexObjective f := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  let z : Point d := a • x + b • y
  have hx := hsupport z x
  have hy := hsupport z y
  have hcombine := add_le_add (mul_le_mul_of_nonneg_left hx ha)
    (mul_le_mul_of_nonneg_left hy hb)
  have hpair : a * pairing (g z) (x - z) + b * pairing (g z) (y - z) = 0 := by
    rw [← O3.Stage2RouteD.pairing_smul_right,
      ← O3.Stage2RouteD.pairing_smul_right,
      ← O3.Stage2RouteD.pairing_add_right]
    have hvec : a • (x - z) + b • (y - z) = 0 := by
      dsimp [z]
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply,
        Pi.zero_apply]
      have hx := congrArg (fun c : ℝ => c * x i) hab
      have hy := congrArg (fun c : ℝ => c * y i) hab
      nlinarith
    rw [hvec]
    change (∑ i, g z i * (0 : Point d) i) = 0
    simp
  dsimp [z] at hcombine ⊢
  rw [show a * (f (a • x + b • y) + pairing (g (a • x + b • y))
      (x - (a • x + b • y))) +
      b * (f (a • x + b • y) + pairing (g (a • x + b • y))
        (y - (a • x + b • y))) =
      (a + b) * f (a • x + b • y) +
        (a * pairing (g z) (x - z) + b * pairing (g z) (y - z)) by
      dsimp [z]; ring] at hcombine
  rw [hab, one_mul, hpair, add_zero] at hcombine
  exact hcombine

lemma coordinateGradient_const_mul (f : Point d → ℝ) (g : Point d → Point d)
    (c : ℝ) (hgrad : O3.IsCoordinateGradient f g) :
    O3.IsCoordinateGradient (fun x => c * f x) (fun x => c • g x) := by
  intro x
  obtain ⟨hdiff, hderiv⟩ := hgrad x
  refine ⟨hdiff.const_mul c, ?_⟩
  intro h
  rw [fderiv_const_mul hdiff]
  change c * fderiv ℝ f x h = pairing (c • g x) h
  rw [hderiv]
  exact (O3.Stage2RouteD.pairing_smul_left c (g x) h).symm

/-- The normalized completed resisting data viewed as objective data. -/
noncomputable def unitObjectiveData (p : ℝ) (d T : ℕ)
    (algorithm : DeterministicExactPairAlgorithm d) (hT : 1 ≤ T) (hTd : T ≤ d) :
    LowerObjectiveData p d T :=
  { toLowerCompletionData := unitCompletionData p d T algorithm hT hTd }

theorem unitObjectiveData_assumptions {p : ℝ} {d T : ℕ}
    (algorithm : DeterministicExactPairAlgorithm d)
    (hp : 2 < p) (hd : 2 ≤ d) (hT : 1 ≤ T) (hTd : T ≤ d) :
    LowerObjectiveAssumptions (unitObjectiveData p d T algorithm hT hTd) := by
  let P := unitParameters p d T algorithm hT hTd
  let data := unitCompletionData p d T algorithm hT hTd
  have hcompletion : LowerCompletionAssumptions data :=
    unitCompletionData_assumptions algorithm hp hd hT hTd
  rcases hcompletion with ⟨hp', hd', hT', hTd', hx0, hkernel, hDelta,
    hdelta, hchi, hbeta, hqueries, hsteps, hcompletedValue, hcompletedGradient⟩
  let t0 := T - 1
  have ht0 : t0 < T := by dsimp [t0]; omega
  have hbasic : ∀ s < T, (data.xi s = 1 ∨ data.xi s = -1) ∧
      ResistingMaximumAt data s := by
    intro s hs
    rcases hsteps s hs with ⟨-, -, -, hxi, -, hresist, -⟩
    exact ⟨hxi, hresist⟩
  have hH : ∀ x, data.partialH t0 x =
      max (data.partialG t0 x / 2) (lpNorm p x - 3 / 2) := by
    rcases hsteps t0 ht0 with ⟨-, -, -, -, -, -, hH, -⟩
    exact hH
  have hHcert := partialH_convex_oneLipschitz data (by linarith) ht0 hbasic hH
  have hchiPos : 0 < P.chi := unitChi_pos hT
  have hsupport : ∀ x y,
      (repairSelectedOracle p d P.chi (data.partialH t0)).value x +
        pairing ((repairSelectedOracle p d P.chi (data.partialH t0)).gradient x)
          (y - x) ≤
      (repairSelectedOracle p d P.chi (data.partialH t0)).value y := by
    intro x y
    exact repairSelectedGradient_support hp hd hchiPos (data.partialH t0)
      hHcert.1 hHcert.2 x y
  have hbaseConv := convexObjective_of_global_support _ _ hsupport
  have hbaseGrad := repairSelectedOracle_coordinateGradient hp hd hchiPos
    (data.partialH t0) hHcert.1 hHcert.2
  have hbetaNonneg : 0 ≤ P.beta := (unitBeta_pos hp hd hT).le
  refine ⟨?_, ?_, ?_⟩
  · exact unitCompletionData_assumptions algorithm hp hd hT hTd
  · unfold O3.IsConvexObjective at hbaseConv ⊢
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b ha hb hab
    have hc := hbaseConv.2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab
    change P.beta *
        (repairSelectedOracle p d P.chi (data.partialH t0)).value (a • x + b • y) ≤
      a * (P.beta * (repairSelectedOracle p d P.chi (data.partialH t0)).value x) +
        b * (P.beta * (repairSelectedOracle p d P.chi (data.partialH t0)).value y)
    have hmul := mul_le_mul_of_nonneg_left hc hbetaNonneg
    calc
      _ ≤ P.beta *
          (a * (repairSelectedOracle p d P.chi (data.partialH t0)).value x +
            b * (repairSelectedOracle p d P.chi (data.partialH t0)).value y) := by
        simpa [smul_eq_mul] using hmul
      _ = _ := by ring
  · change O3.IsCoordinateGradient data.completedOracle.value data.completedOracle.gradient
    have hscaled := coordinateGradient_const_mul
        (repairSelectedOracle p d P.chi (data.partialH t0)).value
        (repairSelectedOracle p d P.chi (data.partialH t0)).gradient P.beta hbaseGrad
    have hvalue : data.completedOracle.value = fun x =>
        P.beta * (repairSelectedOracle p d P.chi (data.partialH t0)).value x := by
      funext x
      rw [hcompletedValue]
      rfl
    have hgradient : data.completedOracle.gradient = fun x =>
        P.beta • (repairSelectedOracle p d P.chi (data.partialH t0)).gradient x := by
      funext x
      rw [hcompletedGradient]
      rfl
    rw [hvalue, hgradient]
    exact hscaled

end V7.Stage5AboveTwoLowerS5F
