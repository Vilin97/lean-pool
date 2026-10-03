/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Terms
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Terms.TinyDivergence

/-! The exact algebraic split and HDot⁻¹ estimate for `tiny`.

The component L² bounds and the mean-zero condition for the nondivergence component are
hypotheses here; the mean-zero condition is proved in `Contracts/MeanZero.lean`.
-/

@[expose] public section

noncomputable section
open MeasureTheory Homogenization
namespace AVenhance.Infra.Section5

open AVenhance

variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

/-- The nondivergence summand in the definition of `tiny`. -/
def tinyNondivergencePart (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ)
    (e : ℝ → Vec 2 → Vec 2) (t : ℝ) (x : Vec 2) : ℝ :=
  ∑' k : ℤ,
    I.xiMK m k t *
      vecDot (I.chiTilde hΦ m κm k t x)
        ((flowGradK I hΦ m k t x).mulVec (gradDiv e t x))

/-- `tiny` is its divergence part plus the scalar nondivergence remainder. -/
theorem tiny_eq_divergence_add_nondivergence (hΦ : IsStreamSeq I Φ)
    (m : ℕ) (κm : ℝ) (d e : ℝ → Vec 2 → Vec 2) (t : ℝ) :
    tiny I hΦ m κm d e t =
      fun x => vecDiv (fun y => d t y + e t y) x +
        tinyNondivergencePart I hΦ m κm e t x := by
  funext x
  have hEven (k : ℤ) (hk : ¬ Odd k) :
      I.chiTilde hΦ m κm k t = fun _ => 0 := by
    have h1 : k % 4 ≠ 1 := by
      intro hmod
      rcases Int.even_or_odd k with he | ho
      · rcases he with ⟨z, hz⟩
        omega
      · exact hk ho
    have h3 : k % 4 ≠ 3 := by
      intro hmod
      rcases Int.even_or_odd k with he | ho
      · rcases he with ⟨z, hz⟩
        omega
      · exact hk ho
    have hu : uShear β I.Λ m k = fun _ => 0 := by
      funext y
      simp [uShear, h1, h3]
    funext y
    simp [Ingredients.chiTilde, Ingredients.chiMK, hu]
  let f : ℤ → ℝ := fun k =>
    I.xiMK m k t *
      vecDot (I.chiTilde hΦ m κm k t x)
        ((flowGradK I hΦ m k t x).mulVec (gradDiv e t x))
  have hzero (k : ℤ) (hk : ¬ Odd k) : f k = 0 := by
    simp [f, hEven k hk, vecDot]
  have hTsum : (∑' k : ℤ, f k) =
      ∑' k : {k : ℤ // Odd k}, f k.1 := by
    have hindicator : Set.indicator {k : ℤ | Odd k} f = f := by
      funext k
      by_cases hk : Odd k
      · simp [Set.indicator, hk]
      · simp [Set.indicator, hk, hzero k hk]
    calc
      (∑' k : ℤ, f k) =
          ∑' k : ℤ, Set.indicator {k : ℤ | Odd k} f k := by
        exact congrArg (fun g : ℤ → ℝ => ∑' k : ℤ, g k) hindicator.symm
      _ = ∑' k : {k : ℤ // Odd k}, f k.1 := (tsum_subtype _ _).symm
  simp only [tiny, tinyNondivergencePart]
  rw [← hTsum]

/-- Conditional HDot⁻¹ estimate for the complete `tiny` term. The two
component L² premises are the analytic estimates proved from `e.dm.bounds`
and `e.Em-1.thetam`; the mean-zero premise is a hypothesis here and is proved in
`Contracts/MeanZero.lean`. -/
theorem hMinusOneNorm_tiny_le_of_components
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ)
    (d e : ℝ → Vec 2 → Vec 2) (t : ℝ)
    (hdivL2 : MemL2On unitCube
      (fun x => vecDiv (fun y => d t y + e t y) x))
    (hN_L2 : MemL2On unitCube (tinyNondivergencePart I hΦ m κm e t))
    (hN_mean : MeanZeroOn unitCube (tinyNondivergencePart I hΦ m κm e t))
    (hF : ContDiff ℝ (⊤ : ℕ∞) (fun x => d t x + e t x))
    (hFper : IsZ2Periodic (fun x => d t x + e t x)) :
    hMinusOneNorm (tiny I hΦ m κm d e t) ≤
      ENNReal.ofReal
          (Real.sqrt (gradNormSq (fun x => d t x + e t x))) +
        ENNReal.ofReal ((2 * Real.pi)⁻¹ *
          Real.sqrt (l2NormSq (tinyNondivergencePart I hΦ m κm e t))) := by
  rw [tiny_eq_divergence_add_nondivergence I hΦ m κm d e t]
  calc
    _ ≤ hMinusOneNorm (fun x => vecDiv (fun y => d t y + e t y) x) +
        hMinusOneNorm (tinyNondivergencePart I hΦ m κm e t) :=
      hMinusOneNorm_add_le hdivL2 hN_L2
    _ ≤ _ := add_le_add
      (hMinusOneNorm_tiny_divergencePart_le d e t hF hFper)
      (hMinusOneNorm_le_L2 hN_L2 hN_mean)

end AVenhance.Infra.Section5
end
