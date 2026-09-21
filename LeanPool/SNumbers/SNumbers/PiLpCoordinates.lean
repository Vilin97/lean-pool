/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Coordinate embedding and projection between `ℓ^p_n` and `ℓ^p_m`

Elementary facts about the finite-dimensional sequence spaces `ℓ^p_k`, and two
coordinate maps relating `ℓ^p_m` to the lower-dimensional `ℓ^p_n` along the
inclusion `Fin.castLE : Fin n → Fin m` (for `n ≤ m`):

* `piLp_norm_mono` — the `L^p` norm is monotone under coordinatewise domination
  of the norms;
* `finrank_piLp` — the dimension of `ℓ^p_k` is `k`;
* `projFin` keeps the first `n` coordinates;
* `padFin` extends a vector by zeros in the remaining coordinates.

Both maps are contractions (`norm_projFin_clm_le`, `norm_padFin_clm_le`;
`padFin` is in fact an isometry), and `projFin ∘ padFin = id`. They are used
to build finite-rank approximants and compressions: in the diagonal-operator
example (`SNumbers.Examples.DiagonalMatrices`) and in the determinant
quantities `Δₖ(S)` (`SNumbers.MaxDifference`).

This is generic `PiLp` material (no s-number content); it is a candidate for
upstreaming to `Mathlib.Analysis.Normed.Lp.PiLp`.
-/

universe u

open scoped ENNReal
open ContinuousLinearMap

namespace SNumbers

variable {𝕜 : Type u} [RCLike 𝕜] {m : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-! ## Norm monotonicity and the dimension of `ℓ^p_k` -/

/-- If `‖x i‖ ≤ ‖y i‖` for every coordinate `i`, then `‖x‖ ≤ ‖y‖` in `PiLp p`.
Proved by the `p = ∞` (suprema) and `1 ≤ p.toReal` (sums of `p`-th powers)
cases of the explicit norm formula. -/
lemma piLp_norm_mono {ι : Type*} [Fintype ι] {β : ι → Type*}
    [∀ i, SeminormedAddCommGroup (β i)] {x y : PiLp p β}
    (h : ∀ i, ‖x i‖ ≤ ‖y i‖) : ‖x‖ ≤ ‖y‖ := by
  rcases p.dichotomy with (rfl | hp)
  · rw [PiLp.norm_eq_ciSup, PiLp.norm_eq_ciSup]
    exact ciSup_mono (Finite.bddAbove_range _) h
  · have hp0 : 0 < p.toReal := zero_lt_one.trans_le hp
    rw [PiLp.norm_eq_sum hp0, PiLp.norm_eq_sum hp0]
    have hsum : (∑ i, ‖x i‖ ^ p.toReal) ≤ ∑ i, ‖y i‖ ^ p.toReal :=
      Finset.sum_le_sum fun i _ => Real.rpow_le_rpow (norm_nonneg _) (h i) hp0.le
    exact Real.rpow_le_rpow (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg _) _)
      hsum (one_div_nonneg.mpr hp0.le)

omit [Fact (1 ≤ p)] in
/-- The dimension of `ℓ^p_k = PiLp p (Fin k → 𝕜)` is `k`. -/
lemma finrank_piLp (k : ℕ) :
    Module.finrank 𝕜 (PiLp p (fun _ : Fin k => 𝕜)) = k := by
  rw [(WithLp.linearEquiv p 𝕜 (Fin k → 𝕜)).finrank_eq, Module.finrank_pi 𝕜, Fintype.card_fin]

/-! ## The coordinate maps -/

/-- The **coordinate projection** `ℓ^p_m → ℓ^p_n` keeping the first `n`
coordinates (along `Fin.castLE h`). -/
noncomputable def projFin (h : n ≤ m) :
    PiLp p (fun _ : Fin m => 𝕜) →L[𝕜] PiLp p (fun _ : Fin n => 𝕜) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp p (fun j => x (Fin.castLE h j))
      map_add' := fun x y => by ext j; simp
      map_smul' := fun c x => by ext j; simp }

@[simp] lemma projFin_apply (h : n ≤ m) (x : PiLp p (fun _ : Fin m => 𝕜)) (j : Fin n) :
    (projFin (p := p) h x) j = x (Fin.castLE h j) := rfl

/-- The **coordinate embedding** `ℓ^p_n → ℓ^p_m` extending by zeros past the
first `n` coordinates. -/
noncomputable def padFin :
    PiLp p (fun _ : Fin n => 𝕜) →L[𝕜] PiLp p (fun _ : Fin m => 𝕜) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => WithLp.toLp p (fun i => if hi : (i : ℕ) < n then y ⟨i, hi⟩ else 0)
      map_add' := fun y z => by ext i; by_cases hi : (i : ℕ) < n <;> simp [hi]
      map_smul' := fun c y => by ext i; by_cases hi : (i : ℕ) < n <;> simp [hi] }

@[simp] lemma padFin_apply (y : PiLp p (fun _ : Fin n => 𝕜)) (i : Fin m) :
    (padFin (p := p) (m := m) y) i = if hi : (i : ℕ) < n then y ⟨i, hi⟩ else 0 := rfl

/-- Embedding the first `n` coordinates back gives the **coordinate truncation**
`Pₙ = padFin ∘ projFin` on `ℓ^p_m`: it keeps the first `n` coordinates and zeros
the rest. -/
lemma padFin_projFin_apply (h : n ≤ m) (x : PiLp p (fun _ : Fin m => 𝕜)) (i : Fin m) :
    (padFin (projFin (p := p) h x)) i = if (i : ℕ) < n then x i else 0 := by
  by_cases hi : (i : ℕ) < n
  · rw [padFin_apply, dite_eq_left hi, projFin_apply, ite_eq_left hi]
    congr 1
  · rw [padFin_apply, dite_eq_right hi, ite_eq_right hi]

/-- The coordinate projection is a contraction: `‖projFin h x‖ ≤ ‖x‖`. -/
lemma norm_projFin_le (h : n ≤ m) (x : PiLp p (fun _ : Fin m => 𝕜)) :
    ‖projFin (p := p) h x‖ ≤ ‖x‖ := by
  rcases p.dichotomy with (rfl | hp)
  · rw [PiLp.norm_eq_ciSup, PiLp.norm_eq_ciSup]
    rcases isEmpty_or_nonempty (Fin n) with _ | _
    · rw [Real.iSup_of_isEmpty]
      exact Real.iSup_nonneg fun i => norm_nonneg _
    · refine ciSup_le fun j => ?_
      simpa [projFin_apply] using le_ciSup (Finite.bddAbove_range fun i => ‖x i‖) (Fin.castLE h j)
  · have hp0 : 0 < p.toReal := zero_lt_one.trans_le hp
    rw [PiLp.norm_eq_sum hp0, PiLp.norm_eq_sum hp0]
    apply Real.rpow_le_rpow (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg _) _) _
      (one_div_nonneg.mpr hp0.le)
    simp only [projFin_apply]
    have himg : ∑ j : Fin n, ‖x (Fin.castLE h j)‖ ^ p.toReal
        = ∑ i ∈ Finset.univ.image (Fin.castLE h), ‖x i‖ ^ p.toReal := by
      rw [Finset.sum_image fun a _ b _ hab => Fin.castLE_injective h hab]
    rw [himg]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun i _ _ => Real.rpow_nonneg (norm_nonneg _) _)

/-- The coordinate projection has operator norm `≤ 1`. -/
lemma norm_projFin_clm_le (h : n ≤ m) : ‖projFin (𝕜 := 𝕜) (p := p) h‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    rw [one_mul]; exact norm_projFin_le h x

/-- The coordinate embedding agrees with the original on the embedded indices. -/
lemma padFin_castLE (h : n ≤ m) (y : PiLp p (fun _ : Fin n => 𝕜)) (j : Fin n) :
    (padFin (p := p) (m := m) y) (Fin.castLE h j) = y j := by
  rw [padFin_apply, dite_eq_left (by simp only [Fin.val_castLE]; exact j.isLt)]
  congr 1

/-- The coordinate embedding is an isometry, in particular a contraction:
`‖padFin y‖ ≤ ‖y‖`. The extra coordinates are zero, so they contribute nothing
to the `L^p` norm. -/
lemma norm_padFin_le (h : n ≤ m) (y : PiLp p (fun _ : Fin n => 𝕜)) :
    ‖padFin (p := p) (m := m) y‖ ≤ ‖y‖ := by
  rcases p.dichotomy with (rfl | hp)
  · rw [PiLp.norm_eq_ciSup, PiLp.norm_eq_ciSup]
    rcases isEmpty_or_nonempty (Fin m) with _ | _
    · rw [Real.iSup_of_isEmpty]
      exact Real.iSup_nonneg fun j => norm_nonneg _
    · refine ciSup_le fun i => ?_
      by_cases hi : (i : ℕ) < n
      · simpa [padFin_apply, hi] using
          le_ciSup (Finite.bddAbove_range fun j => ‖y j‖) (⟨(i : ℕ), hi⟩ : Fin n)
      · simp only [padFin_apply, dite_eq_right hi, norm_zero]
        exact Real.iSup_nonneg fun j => norm_nonneg _
  · have hp0 : 0 < p.toReal := zero_lt_one.trans_le hp
    rw [PiLp.norm_eq_sum hp0, PiLp.norm_eq_sum hp0]
    apply le_of_eq
    congr 1
    have hoff : ∑ i : Fin m, ‖(padFin (p := p) (m := m) y) i‖ ^ p.toReal
        = ∑ i ∈ Finset.univ.image (Fin.castLE h),
            ‖(padFin (p := p) (m := m) y) i‖ ^ p.toReal := by
      refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
      intro i _ hi
      have hni : ¬ (i : ℕ) < n := fun hlt =>
        hi (Finset.mem_image.mpr ⟨⟨(i : ℕ), hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩)
      rw [padFin_apply, dite_eq_right hni, norm_zero, Real.zero_rpow hp0.ne']
    rw [hoff, Finset.sum_image fun a _ b _ hab => Fin.castLE_injective h hab]
    exact Finset.sum_congr rfl fun j _ => by rw [padFin_castLE]

/-- The coordinate embedding has operator norm `≤ 1`. -/
lemma norm_padFin_clm_le (h : n ≤ m) :
    ‖(padFin (𝕜 := 𝕜) (p := p) (n := n) (m := m))‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => by
    rw [one_mul]; exact norm_padFin_le h y

end SNumbers

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
