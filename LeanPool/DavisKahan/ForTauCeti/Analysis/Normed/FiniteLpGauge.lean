/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-5.6 Thinking
-/
module

public import Mathlib.Analysis.MeanInequalities
public import LeanPool.DavisKahan.ForTauCeti.Analysis.Convex.Majorization
public import Mathlib.Data.Fintype.Order


/-!
# The finite `ℓᵖ` gauges

The `ℓᵖ` family of `FiniteSymmetricGauge`s, `1 ≤ p ≤ ∞`, and their monotonicity under weak
majorization.

* `FiniteVector.lpGauge p x = (∑ i, |xᵢ|ᵖ)^(1/p)` for `1 ≤ p < ∞`, with the finite Minkowski
  inequality, and `FiniteVector.linftyGauge`, the coordinatewise supremum;
* `FiniteVector.lpSymmetricGauge` and `FiniteVector.linftySymmetricGauge`, the corresponding
  bundled gauges;
* their monotonicity under `FiniteVector.WeaklyMajorized`, which is
  `FiniteSymmetricGauge.mono_weaklyMajorized` specialized;
* the zero-padding bridges used to compare gauges across index lengths.

The majorization theory these consume — `FiniteVector.prefixSum`,
`FiniteVector.WeaklyMajorized`, `FiniteVector.zeroPadRight`, `FiniteSymmetricGauge` itself,
and the Hardy--Littlewood--Pólya transfer descent that makes every symmetric gauge monotone —
lives in `ForTauCeti.Analysis.Convex.Majorization`.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `ForMathlib.Analysis.Normed.FiniteLpGauge`, moved to
  `ForTauCeti` in the Wave-1 staging migration; introduced at Davis--Kahan
  commit `a8d4ea3`.  The majorization layer was split out to
  `ForTauCeti.Analysis.Convex.Majorization` on 2026-07-28, when the T-transform descent it
  contained was found to be one of three copies in this library.
* Extraction class: **moved**.  The Wave-1 migration renamed the namespace
  `ForMathlib` to `TauCeti`; declaration names and proofs are unchanged.
* Original authors / copyright: Jon Crall, GPT-5.6 Thinking; Copyright (c) 2026 Kitware, Inc.;
  Apache 2.0.
* Spectra influence: **none** — this module imports only Mathlib and sibling
  `ForTauCeti` staging modules.
-/

public section

namespace TauCeti

open scoped BigOperators

namespace FiniteVector

variable {n m : ℕ}

/-- The finite real `ℓᵖ` gauge. -/
@[expose]
noncomputable def lpGauge (p : ℝ) (x : Fin n → ℝ) : ℝ :=
  (∑ i, |x i| ^ p) ^ (1 / p)

/-- The `ℓᵖ` gauge is nonnegative. -/
theorem lpGauge_nonneg (p : ℝ) (x : Fin n → ℝ) :
    0 ≤ lpGauge p x := by
  exact Real.rpow_nonneg (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (abs_nonneg _) _) _

/-- The `ℓᵖ` gauge of zero is zero. -/
@[simp] theorem lpGauge_zero {p : ℝ} (hp : 0 < p) :
    lpGauge p (0 : Fin n → ℝ) = 0 := by
  simp [lpGauge, Real.zero_rpow hp.ne', Real.zero_rpow (inv_ne_zero hp.ne')]

/-- The finite `ℓᵖ` gauge vanishes exactly on the zero vector. -/
theorem lpGauge_eq_zero_iff {p : ℝ} (hp : 0 < p) (x : Fin n → ℝ) :
    lpGauge p x = 0 ↔ x = 0 := by
  have hsum0 : 0 ≤ ∑ i, |x i| ^ p :=
    Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (abs_nonneg _) _
  rw [lpGauge, Real.rpow_eq_zero_iff_of_nonneg hsum0]
  constructor
  · rintro ⟨hsum, -⟩
    funext i
    have hi : |x i| ^ p = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => Real.rpow_nonneg (abs_nonneg (x j)) _)).mp hsum
          i (Finset.mem_univ i)
    have habs : |x i| = 0 :=
      ((Real.rpow_eq_zero_iff_of_nonneg (abs_nonneg (x i))).mp hi).1
    exact abs_eq_zero.mp habs
  · rintro rfl
    constructor
    · simp [Real.zero_rpow hp.ne']
    · exact one_div_ne_zero hp.ne'

/-- Positive homogeneity of the finite `ℓᵖ` gauge. -/
theorem lpGauge_smul {p : ℝ} (hp : 0 < p) (c : ℝ) (x : Fin n → ℝ) :
    lpGauge p (c • x) = |c| * lpGauge p x := by
  by_cases hc : c = 0
  · subst c
    simp [lpGauge_zero (n := n) hp]
  have habspos : 0 < |c| := abs_pos.mpr hc
  have hsum : (∑ i, |(c • x) i| ^ p) =
      |c| ^ p * ∑ i, |x i| ^ p := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Pi.smul_apply, smul_eq_mul, abs_mul, Real.mul_rpow]
    exacts [abs_nonneg c, abs_nonneg (x i)]
  unfold lpGauge
  rw [hsum, Real.mul_rpow]
  · rw [← Real.rpow_mul (abs_nonneg c)]
    have hpinv : p * (1 / p) = 1 := by
      field_simp
    rw [hpinv, Real.rpow_one]
  · exact Real.rpow_nonneg (abs_nonneg c) p
  · exact Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (abs_nonneg _) _

/-- Permutation invariance of the finite `ℓᵖ` gauge. -/
theorem lpGauge_perm (p : ℝ) (x : Fin n → ℝ) (π : Equiv.Perm (Fin n)) :
    lpGauge p (x ∘ π) = lpGauge p x := by
  unfold lpGauge
  congr 1
  exact Equiv.sum_comp π (fun i => |x i| ^ p)

/-- A single coordinate sign flip does not change the finite `ℓᵖ` gauge. -/
theorem lpGauge_neg_single (p : ℝ) (x : Fin n → ℝ) (j : Fin n) :
    lpGauge p (Function.update x j (-(x j))) = lpGauge p x := by
  unfold lpGauge
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rcases eq_or_ne i j with rfl | hij
  · simp
  · rw [Function.update_of_ne hij]

/-- Finite-dimensional Minkowski inequality. -/
theorem lpGauge_add_le {p : ℝ} (hp : 1 ≤ p) (x y : Fin n → ℝ) :
    lpGauge p (x + y) ≤ lpGauge p x + lpGauge p y := by
  simpa [lpGauge] using Real.Lp_add_le Finset.univ x y hp

/-- The `ℓᵖ` gauge as a finite symmetric gauge. -/
noncomputable def lpSymmetricGauge (p : ℝ) (hp : 1 ≤ p) :
    FiniteSymmetricGauge n where
  toFun := lpGauge p
  add_le' := lpGauge_add_le hp
  real_smul' := lpGauge_smul (zero_lt_one.trans_le hp)
  perm' := lpGauge_perm p
  neg_single' := lpGauge_neg_single p

/-- `ℓᵖ` gauge monotonicity under weak majorization. -/
theorem lpGauge_mono_weaklyMajorized {p : ℝ} (hp : 1 ≤ p)
    {x y : Fin n → ℝ} (h : WeaklyMajorized x y) :
    lpGauge p x ≤ lpGauge p y :=
  (lpSymmetricGauge (n := n) p hp).mono_weaklyMajorized h

/-- Coordinatewise monotonicity of the `ℓᵖ` gauge on nonnegative vectors. -/
theorem lpGauge_mono {p : ℝ} (hp : 1 ≤ p) {x y : Fin n → ℝ}
    (hx0 : ∀ i, 0 ≤ x i) (hxy : ∀ i, x i ≤ y i) :
    lpGauge p x ≤ lpGauge p y :=
  (lpSymmetricGauge (n := n) p hp).mono hx0 hxy

/-- Right zero-padding does not change the finite `ℓᵖ` gauge. -/
theorem lpGauge_zeroPadRight (p : ℝ) (x : Fin n → ℝ) :
    lpGauge p (zeroPadRight (m := m) x) = lpGauge p x := by
  rcases eq_or_ne p 0 with rfl | hp
  · -- the outer exponent `1 / 0` is zero, so both gauges collapse to `1`
    simp [lpGauge]
  · unfold lpGauge zeroPadRight
    rw [Fin.sum_univ_add]
    simp [Real.zero_rpow hp]

/-- The finite `ℓ∞` gauge. -/
noncomputable def linftyGauge (x : Fin n → ℝ) : ℝ :=
  ⨆ i, |x i|

/-- The `ℓ∞` gauge is nonnegative. -/
theorem linftyGauge_nonneg (x : Fin n → ℝ) : 0 ≤ linftyGauge x := by
  rcases n with _ | n
  · simp [linftyGauge]
  · exact (abs_nonneg (x 0)).trans
      (le_ciSup (Finite.bddAbove_range (fun j : Fin (n + 1) => |x j|)) 0)

/-- The `ℓ∞` gauge of zero is zero. -/
@[simp] theorem linftyGauge_zero :
    linftyGauge (0 : Fin n → ℝ) = 0 := by
  simp [linftyGauge]

/-- Coordinatewise domination of absolute values implies `ℓ∞` domination. -/
theorem linftyGauge_mono {x y : Fin n → ℝ}
    (hxy : ∀ i, |x i| ≤ |y i|) : linftyGauge x ≤ linftyGauge y := by
  unfold linftyGauge
  exact ciSup_mono (Finite.bddAbove_range (fun i => |y i|)) hxy

/-- Triangle inequality for the finite `ℓ∞` gauge. -/
theorem linftyGauge_add_le (x y : Fin n → ℝ) :
    linftyGauge (x + y) ≤ linftyGauge x + linftyGauge y := by
  -- `ciSup_le` needs a nonempty index type; the empty gauge is zero
  rcases n with _ | n
  · simp [linftyGauge]
  unfold linftyGauge
  refine ciSup_le fun i => ?_
  exact (abs_add_le (x i) (y i)).trans
    (add_le_add (le_ciSup (Finite.bddAbove_range (fun j => |x j|)) i)
      (le_ciSup (Finite.bddAbove_range (fun j => |y j|)) i))

/-- Positive homogeneity of the finite `ℓ∞` gauge. -/
theorem linftyGauge_smul (c : ℝ) (x : Fin n → ℝ) :
    linftyGauge (c • x) = |c| * linftyGauge x := by
  unfold linftyGauge
  -- `Real.mul_iSup_of_nonneg` is already total in `c`, including `c = 0`
  rw [Real.mul_iSup_of_nonneg (abs_nonneg c)]
  apply congrArg iSup
  funext i
  simp [abs_mul, Pi.smul_apply, smul_eq_mul]

/-- Permutation invariance of the finite `ℓ∞` gauge. -/
theorem linftyGauge_perm (x : Fin n → ℝ) (π : Equiv.Perm (Fin n)) :
    linftyGauge (x ∘ π) = linftyGauge x := by
  rcases n with _ | n
  · simp [linftyGauge]
  unfold linftyGauge
  apply le_antisymm
  · refine ciSup_le fun i => ?_
    exact le_ciSup (Finite.bddAbove_range (fun j => |x j|)) (π i)
  · refine ciSup_le fun i => ?_
    simpa using le_ciSup (Finite.bddAbove_range (fun j => |x (π j)|)) (π.symm i)

/-- A single sign flip does not change the finite `ℓ∞` gauge. -/
theorem linftyGauge_neg_single (x : Fin n → ℝ) (j : Fin n) :
    linftyGauge (Function.update x j (-(x j))) = linftyGauge x := by
  unfold linftyGauge
  congr 1
  funext i
  rcases eq_or_ne i j with rfl | hij
  · simp
  · simp [Function.update_of_ne hij]

/-- The `ℓ∞` gauge as a finite symmetric gauge. -/
noncomputable def linftySymmetricGauge : FiniteSymmetricGauge n where
  toFun := linftyGauge
  add_le' := linftyGauge_add_le
  real_smul' := linftyGauge_smul
  perm' := linftyGauge_perm
  neg_single' := linftyGauge_neg_single

/-- `ℓ∞` gauge monotonicity under weak majorization. -/
theorem linftyGauge_mono_weaklyMajorized {x y : Fin n → ℝ}
    (h : WeaklyMajorized x y) : linftyGauge x ≤ linftyGauge y :=
  (linftySymmetricGauge (n := n)).mono_weaklyMajorized h

/-- Right zero-padding does not change the finite `ℓ∞` gauge. -/
theorem linftyGauge_zeroPadRight (x : Fin n → ℝ) :
    linftyGauge (zeroPadRight (m := m) x) = linftyGauge x := by
  rcases n with _ | n
  · -- nothing to pad: the padded vector is identically zero
    have hz : zeroPadRight (m := m) x = 0 := by
      funext i
      simp [zeroPadRight]
    rw [hz]
    simp [linftyGauge]
  have : Nonempty (Fin (n + 1 + m)) := ⟨⟨0, by omega⟩⟩
  apply le_antisymm
  · unfold linftyGauge
    refine ciSup_le fun i => ?_
    refine Fin.addCases (motive := fun i =>
      |zeroPadRight (m := m) x i| ≤ ⨆ q, |x q|) ?_ ?_ i
    · intro j
      rw [zeroPadRight_left]
      exact le_ciSup (Finite.bddAbove_range (fun q => |x q|)) j
    · intro j
      rw [zeroPadRight_right, abs_zero]
      exact linftyGauge_nonneg x
  · unfold linftyGauge
    refine ciSup_le fun i => ?_
    simpa using le_ciSup
      (Finite.bddAbove_range (fun q => |zeroPadRight (m := m) x q|))
      (Fin.castAdd m i)

end FiniteVector
end TauCeti
