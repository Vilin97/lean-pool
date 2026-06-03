/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/

import LeanPool.OSforGFF.GaussianField.SchwartzNuclear.ParametricCalculus
import LeanPool.OSforGFF.GaussianField.SchwartzNuclear.SchwartzHermiteExpansion

/-!
# Schwartz Function Slicing and Partial Hermite Coefficients

Defines the slicing of a multi-dimensional Schwartz function along one coordinate
and the partial Hermite coefficient map. These are the "A1" and "A2" analytical
constructions used in the multi-dimensional Hermite expansion proof.

## Main definitions

- `euclideanSnoc d y t` : embed `(y, t)` into `EuclideanSpace ℝ (Fin (d+1))`
- `euclideanInit d x` : project to the first `d` coordinates
- `schwartzSlice d f y` : fix first `d+1` coordinates of `f ∈ S(ℝ^{d+2})`, get `S(ℝ)`
- `schwartzPartialHermiteCoeff d f n` : integrate out last coordinate against
  the `n`-th Hermite function, get `S(ℝ^{d+1})`

## Sorry inventory

**0 sorrys.** All lemmas fully proved. <!-- count_axioms:skip -->

## Proved lemmas

- `euclideanSnoc_norm_sq` — `‖euclideanSnoc y t‖² = ‖y‖² + t²`
- `euclideanSnoc_norm_ge_left` — `‖y‖ ≤ ‖euclideanSnoc y t‖`
- `integral_euclidean_snoc` — Fubini for EuclideanSpace slicing
- `contDiff_parametric_hermiteCoeff` — parametric Hermite coefficient is C^∞
- `schwartz_slice_partial_pointwise_bound` — pointwise bound via chain rule + CLM norms
- `schwartz_slice_partial_seminorm_bound` — seminorm bound for scalarized slices
-/

open MeasureTheory Real SchwartzMap Measure
open scoped ContDiff

/-- In `WithTop ℕ∞`, `∞ + ↑n = ∞` so `∞ + ↑n ≤ ∞`. -/
private lemma le_infty_add (n : ℕ) : (∞ : WithTop ℕ∞) + ↑n ≤ ∞ := by
  change (↑(⊤ : ℕ∞) : WithTop ℕ∞) + ↑(↑n : ℕ∞) ≤ ↑(⊤ : ℕ∞)
  rw [← WithTop.coe_add, WithTop.coe_le_coe]; exact le_of_eq (top_add _)

/-- In `WithTop ℕ∞`, `↑n ≤ ∞`. -/
private lemma nat_le_infty (n : ℕ) : (↑n : WithTop ℕ∞) ≤ ∞ :=
  (show (↑(↑n : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞) from WithTop.coe_le_coe.mpr le_top)

noncomputable section

namespace GaussianField

/-- Embed `EuclideanSpace ℝ (Fin d) × ℝ` into `EuclideanSpace ℝ (Fin (d + 1))`
by appending the real value as the last coordinate.
-/
def euclideanSnoc (d : ℕ) (y : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    EuclideanSpace ℝ (Fin (d + 1)) :=
  (WithLp.equiv 2 _).symm (Fin.snoc (fun i => y i) t)

/-- Project `EuclideanSpace ℝ (Fin (d + 1))` to its first `d` coordinates. -/
def euclideanInit (d : ℕ) (x : EuclideanSpace ℝ (Fin (d + 1))) :
    EuclideanSpace ℝ (Fin d) :=
  (WithLp.equiv 2 _).symm (fun i => x (Fin.castSucc i))

/-- Snoc of init and last coordinate recovers the original point. -/
lemma euclideanSnoc_init_last (d : ℕ) (x : EuclideanSpace ℝ (Fin (d + 1))) :
    euclideanSnoc d (euclideanInit d x) (x (Fin.last d)) = x := by
  simp only [euclideanSnoc, euclideanInit]
  apply (WithLp.equiv 2 _).injective
  simp only [Equiv.apply_symm_apply]
  funext i
  refine Fin.lastCases ?_ ?_ i
  · simp [Fin.snoc_last]
  · intro j; simp [Fin.snoc_castSucc]

/-- `euclideanSnoc d y` has temperate growth as a function of `t`. -/
private lemma euclideanSnoc_hasTemperateGrowth (d : ℕ)
    (y : EuclideanSpace ℝ (Fin (d + 1))) :
    Function.HasTemperateGrowth (euclideanSnoc (d + 1) y) := by
  -- The linear part: embed ℝ as the last coordinate in EuclideanSpace
  set L : ℝ →L[ℝ] EuclideanSpace ℝ (Fin (d + 2)) :=
    (EuclideanSpace.equiv (Fin (d+2)) ℝ).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.single (R := ℝ) (φ := fun (_ : Fin (d + 2)) => ℝ)
        (Fin.last (d + 1)))
  -- The constant part
  set c := euclideanSnoc (d + 1) y 0
  have h_snoc_decomp : ∀ t,
      Fin.snoc (α := fun _ => ℝ) (fun i => y.ofLp i) t =
      Fin.snoc (α := fun _ => ℝ) (fun i => y.ofLp i) 0 +
        Pi.single (Fin.last (d + 1)) t := by
    intro t
    ext i
    rw [Pi.add_apply]
    refine Fin.lastCases ?_ ?_ i
    · simp [Fin.snoc_last]
    · intro j; simp [Fin.snoc_castSucc]
  have h_eq : euclideanSnoc (d+1) y = (fun t => c + L t) := by
    funext t
    simp only [c, L, euclideanSnoc, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.single_apply, ContinuousLinearEquiv.coe_coe]
    change (WithLp.equiv 2 _).symm (Fin.snoc (fun i => y.ofLp i) t) =
      (WithLp.equiv 2 _).symm (Fin.snoc (fun i => y.ofLp i) 0) +
      (EuclideanSpace.equiv (Fin (d+2)) ℝ).symm (Pi.single (Fin.last (d+1)) t)
    rw [h_snoc_decomp]
    simp [EuclideanSpace.equiv]
  rw [h_eq]
  exact Function.HasTemperateGrowth.add (Function.HasTemperateGrowth.const _)
    L.hasTemperateGrowth

/-- `euclideanSnoc d y` is antilipschitz (in fact isometric) in `t`. -/
private lemma euclideanSnoc_antilipschitz (d : ℕ)
    (y : EuclideanSpace ℝ (Fin (d + 1))) :
    AntilipschitzWith 1 (euclideanSnoc (d + 1) y) := by
  refine AntilipschitzWith.of_le_mul_dist (fun s t => ?_)
  simp only [NNReal.coe_one, one_mul]
  have hcoord : ∀ i : Fin (d+2),
    ‖(euclideanSnoc (d+1) y s - euclideanSnoc (d+1) y t) i‖ =
    if i = Fin.last (d+1) then ‖s - t‖ else 0 := by
    intro i
    simp only [euclideanSnoc, WithLp.equiv_symm_apply, WithLp.ofLp_sub, Pi.sub_apply]
    refine Fin.lastCases ?_ ?_ i
    · simp [Fin.snoc_last]
    · intro j; simp [Fin.snoc_castSucc]
  have hsum : ∑ i, ‖(euclideanSnoc (d+1) y s - euclideanSnoc (d+1) y t) i‖ ^ 2
    = ‖s - t‖ ^ 2 := by
    conv_lhs => arg 2; ext i; rw [hcoord]
    simp [Finset.sum_ite_eq', Finset.mem_univ]
  change dist s t ≤ dist (euclideanSnoc (d + 1) y s) (euclideanSnoc (d + 1) y t)
  rw [dist_eq_norm, dist_eq_norm (E := EuclideanSpace ℝ _), EuclideanSpace.norm_eq,
    hsum, Real.sqrt_sq (norm_nonneg _)]

/-- The norm of `euclideanSnoc y t` satisfies `‖y‖² + t² = ‖euclideanSnoc y t‖²`.
This is because snoc just appends one coordinate.
-/
private lemma euclideanSnoc_norm_sq (d : ℕ)
    (y : EuclideanSpace ℝ (Fin (d + 1))) (t : ℝ) :
    ‖euclideanSnoc (d + 1) y t‖ ^ 2 = ‖y‖ ^ 2 + t ^ 2 := by
  have hlast : (euclideanSnoc (d + 1) y t) (Fin.last (d + 1)) = t := by
    simp [euclideanSnoc, Fin.snoc_last]
  have hcast : ∀ j : Fin (d + 1),
      (euclideanSnoc (d + 1) y t) (Fin.castSucc j) = y j := by
    intro j; simp [euclideanSnoc, Fin.snoc_castSucc]
  simp only [EuclideanSpace.norm_eq]
  rw [Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _)),
    Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
  rw [show ∑ i : Fin (d + 2), ‖(euclideanSnoc (d + 1) y t) i‖ ^ 2 =
    (∑ j : Fin (d + 1), ‖(euclideanSnoc (d + 1) y t) (Fin.castSucc j)‖ ^ 2) +
    ‖(euclideanSnoc (d + 1) y t) (Fin.last (d + 1))‖ ^ 2 from
    Fin.sum_univ_castSucc _]
  rw [hlast, norm_eq_abs, sq_abs]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [hcast]

/-- The first `d+1` coordinates contribute to the norm:
`‖y‖ ≤ ‖euclideanSnoc (d+1) y t‖`.
-/
private lemma euclideanSnoc_norm_ge_left (d : ℕ)
    (y : EuclideanSpace ℝ (Fin (d + 1))) (t : ℝ) :
    ‖y‖ ≤ ‖euclideanSnoc (d + 1) y t‖ := by
  rw [← Real.sqrt_sq (norm_nonneg y),
    ← Real.sqrt_sq (norm_nonneg (euclideanSnoc (d + 1) y t))]
  apply Real.sqrt_le_sqrt
  rw [euclideanSnoc_norm_sq]
  linarith [sq_nonneg t]

/-- The last coordinate contributes to the norm:
`|t| ≤ ‖euclideanSnoc (d+1) y t‖`.
-/
private lemma euclideanSnoc_norm_ge_right (d : ℕ)
    (y : EuclideanSpace ℝ (Fin (d + 1))) (t : ℝ) :
    ‖t‖ ≤ ‖euclideanSnoc (d + 1) y t‖ := by
  rw [← Real.sqrt_sq (norm_nonneg t),
    ← Real.sqrt_sq (norm_nonneg (euclideanSnoc (d + 1) y t))]
  apply Real.sqrt_le_sqrt
  rw [euclideanSnoc_norm_sq, Real.norm_eq_abs, sq_abs]
  linarith [sq_nonneg ‖y‖]

-- A1: Slicing a Schwartz function along the last coordinate
/-- Restrict `f ∈ S(ℝ^{d+2})` to the hyperplane `{x | x_rest = y}`,
giving a Schwartz function of the last coordinate.
-/
noncomputable def schwartzSlice (d : ℕ)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin (d + 2))) ℝ)
    (y : EuclideanSpace ℝ (Fin (d + 1))) :
    SchwartzMap ℝ ℝ where
  toFun t := f (euclideanSnoc (d + 1) y t)
  smooth' :=
    (compCLMOfAntilipschitz ℝ (euclideanSnoc_hasTemperateGrowth d y)
      (euclideanSnoc_antilipschitz d y) f).smooth'
  decay' :=
    (compCLMOfAntilipschitz ℝ (euclideanSnoc_hasTemperateGrowth d y)
      (euclideanSnoc_antilipschitz d y) f).decay'

/-! ## A2: Partial Hermite coefficient is Schwartz

The function `g(y) = ∫ f(euclideanSnoc y t) · ψ_n(t) dt` is Schwartz in y.

**Proof strategy** (following the parametric integral approach):

### Smoothness (`smooth'`)
Prove `ContDiff ℝ m` for all `m` by induction on `m`:
- Base (`m = 0`): continuity via `continuous_of_dominated`
- Step: `hasFDerivAt_integral_of_dominated_of_fderiv_le` gives the derivative
  as `∫ (∂_y f)(euclideanSnoc y t) · ψ_n(t) dt`, which has the same form with `∂_y f`
  (still Schwartz) replacing `f`, so the IH applies.

### Decay (`decay'`)
Use the key norm bound `‖y‖ ≤ ‖euclideanSnoc y t‖` (`euclideanSnoc_norm_ge_left`):
1. Commute `iteratedFDeriv` and the integral (via `smooth'`)
2. Bound `‖y‖^k * |integrand| ≤ ‖euclideanSnoc y t‖^k * |integrand|`
3. Apply Schwartz decay of `f` at the point `euclideanSnoc y t`
4. The resulting `t`-integral is finite since `hermiteFunction n` is integrable.
-/

/-- The integrand `f(euclideanSnoc y t) * hermiteFunction n t` is dominated
by `(seminorm ℝ 0 0 f) * |hermiteFunction n t|`, which is `y`-independent.
-/
private lemma hermiteCoeff_integrand_bound (d : ℕ)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin (d + 2))) ℝ) (n : ℕ)
    (y : EuclideanSpace ℝ (Fin (d + 1))) (t : ℝ) :
    ‖f (euclideanSnoc (d + 1) y t) * hermiteFunction n t‖ ≤
      SchwartzMap.seminorm ℝ 0 0 f * ‖hermiteFunction n t‖ := by
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (norm_le_seminorm ℝ f _) (norm_nonneg _)

/-- The dominating function `C * |hermiteFunction n t|` is integrable in `t`. -/
private lemma hermiteCoeff_bound_integrable (n : ℕ) (C : ℝ) :
    Integrable (fun t : ℝ => C * ‖hermiteFunction n t‖) := by
  apply Integrable.const_mul
  rw [show (fun t => ‖hermiteFunction n t‖) =
    (fun t => ‖(schwartzHermiteBasis1D n) t‖) from
    by ext t; rw [schwartzHermiteBasis1D_apply]]
  exact (schwartzHermiteBasis1D n).integrable.norm

/-- For fixed `t`, the map `y ↦ euclideanSnoc y t` is continuous.
Proved via 1-Lipschitz: changing `y` by `δ` changes `euclideanSnoc y t` by at most `δ`
since only the first `d+1` coordinates change.
-/
private lemma continuous_euclideanSnoc_y (d : ℕ) (t : ℝ) :
    Continuous (fun y : EuclideanSpace ℝ (Fin (d + 1)) =>
      euclideanSnoc (d + 1) y t) := by
  apply LipschitzWith.continuous (K := 1)
  intro y₁ y₂
  simp only [ENNReal.coe_one, one_mul, edist_dist, dist_eq_norm]
  apply ENNReal.ofReal_le_ofReal
  -- ‖euclideanSnoc y₁ t - euclideanSnoc y₂ t‖ ≤ ‖y₁ - y₂‖
  rw [show euclideanSnoc (d + 1) y₁ t - euclideanSnoc (d + 1) y₂ t =
    euclideanSnoc (d + 1) (y₁ - y₂) 0 from by
    ext i
    simp only [euclideanSnoc, WithLp.equiv_symm_apply, WithLp.ofLp_sub, Pi.sub_apply]
    refine Fin.lastCases ?_ ?_ i
    · simp [Fin.snoc_last]
    · intro j; simp [Fin.snoc_castSucc]]
  have h : ‖euclideanSnoc (d + 1) (y₁ - y₂) 0‖ ^ 2 = ‖y₁ - y₂‖ ^ 2 := by
    rw [euclideanSnoc_norm_sq]; ring
  nlinarith [norm_nonneg (euclideanSnoc (d + 1) (y₁ - y₂) 0), norm_nonneg (y₁ - y₂),
    sq_nonneg (‖euclideanSnoc (d + 1) (y₁ - y₂) 0‖ - ‖y₁ - y₂‖)]

/-- For fixed `t`, the map `y ↦ euclideanSnoc y t` has temperate growth.
This is because the map is affine: `euclideanSnoc y t = c + L(y)` where
`L` is the castSucc isometric embedding and `c = euclideanSnoc 0 t = (0,...,0,t)`.
-/
private lemma euclideanSnoc_y_hasTemperateGrowth (d : ℕ) (t : ℝ) :
    Function.HasTemperateGrowth (fun y : EuclideanSpace ℝ (Fin (d + 1)) =>
      euclideanSnoc (d + 1) y t) := by
  -- Constant part
  set c := euclideanSnoc (d + 1) (0 : EuclideanSpace ℝ (Fin (d + 1))) t
  -- Linear part: y ↦ euclideanSnoc y 0 (embeds y into first d+1 coordinates)
  set L_fun : EuclideanSpace ℝ (Fin (d + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (d + 2)) :=
    { toFun := fun y => euclideanSnoc (d + 1) y 0
      map_add' := fun y₁ y₂ => by
        ext i
        simp only [euclideanSnoc, WithLp.equiv_symm_apply, WithLp.ofLp_add, Pi.add_apply]
        refine Fin.lastCases ?_ ?_ i
        · simp [Fin.snoc_last]
        · intro j; simp [Fin.snoc_castSucc]
      map_smul' := fun a y => by
        ext i
        simp only [euclideanSnoc, WithLp.equiv_symm_apply, WithLp.ofLp_smul,
          Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        refine Fin.lastCases ?_ ?_ i
        · simp [Fin.snoc_last]
        · intro j; simp [Fin.snoc_castSucc] }
  have hL_bound : ∀ y, ‖L_fun y‖ ≤ 1 * ‖y‖ := fun y => by
    rw [one_mul]
    have hdef : ‖L_fun y‖ = ‖euclideanSnoc (d + 1) y 0‖ := rfl
    have h : ‖euclideanSnoc (d + 1) y 0‖ ^ 2 = ‖y‖ ^ 2 := by
      rw [euclideanSnoc_norm_sq]; ring
    nlinarith [norm_nonneg (euclideanSnoc (d + 1) y 0), norm_nonneg y,
      sq_nonneg (‖euclideanSnoc (d + 1) y 0‖ - ‖y‖)]
  set L := L_fun.mkContinuous 1 hL_bound
  have h_eq : (fun y => euclideanSnoc (d + 1) y t) = fun y => c + L y := by
    funext y
    change euclideanSnoc (d + 1) y t =
      euclideanSnoc (d + 1) 0 t + euclideanSnoc (d + 1) y 0
    ext i
    simp only [euclideanSnoc, WithLp.equiv_symm_apply, WithLp.ofLp_add, Pi.add_apply]
    refine Fin.lastCases ?_ ?_ i
    · simp [Fin.snoc_last]
    · intro j; simp [Fin.snoc_castSucc]
  rw [h_eq]
  exact Function.HasTemperateGrowth.add (Function.HasTemperateGrowth.const _)
    L.hasTemperateGrowth

/-- For fixed `t`, the map `y ↦ euclideanSnoc y t` is antilipschitz with constant 1.
This is because only the first d+1 coordinates change while the last stays fixed at `t`.
-/
private lemma euclideanSnoc_y_antilipschitz (d : ℕ) (t : ℝ) :
    AntilipschitzWith 1 (fun y : EuclideanSpace ℝ (Fin (d + 1)) =>
      euclideanSnoc (d + 1) y t) := by
  refine AntilipschitzWith.of_le_mul_dist (fun y₁ y₂ => ?_)
  simp only [NNReal.coe_one, one_mul]
  rw [dist_eq_norm, dist_eq_norm]
  -- ‖y₁ - y₂‖ ≤ ‖euclideanSnoc y₁ t - euclideanSnoc y₂ t‖
  -- because the difference in euclideanSnoc only has the y-components
  have h : ‖euclideanSnoc (d + 1) y₁ t - euclideanSnoc (d + 1) y₂ t‖ ^ 2 =
      ‖y₁ - y₂‖ ^ 2 := by
    rw [show euclideanSnoc (d + 1) y₁ t - euclideanSnoc (d + 1) y₂ t =
      euclideanSnoc (d + 1) (y₁ - y₂) 0 from by
      ext i
      simp only [euclideanSnoc, WithLp.equiv_symm_apply, WithLp.ofLp_sub, Pi.sub_apply]
      refine Fin.lastCases ?_ ?_ i
      · simp [Fin.snoc_last]
      · intro j; simp [Fin.snoc_castSucc]]
    rw [euclideanSnoc_norm_sq]; ring
  nlinarith [norm_nonneg (euclideanSnoc (d + 1) y₁ t - euclideanSnoc (d + 1) y₂ t),
    norm_nonneg (y₁ - y₂),
    sq_nonneg (‖euclideanSnoc (d + 1) y₁ t - euclideanSnoc (d + 1) y₂ t‖ - ‖y₁ - y₂‖)]

/-- For fixed `t`, the composition `f ∘ euclideanSnoc · t` is a Schwartz function of `y`. -/
private noncomputable def schwartz_slice_y (d : ℕ)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin (d + 2))) ℝ)
    (t : ℝ) : SchwartzMap (EuclideanSpace ℝ (Fin (d + 1))) ℝ :=
  compCLMOfAntilipschitz ℝ (euclideanSnoc_y_hasTemperateGrowth d t)
    (euclideanSnoc_y_antilipschitz d t) f

/-- The linear part of `y ↦ euclideanSnoc y t`: the CLM `y ↦ euclideanSnoc y 0`
that isometrically embeds the first d+1 coordinates.
-/
private noncomputable def euclideanSnoc_linearCLM (d : ℕ) :
    EuclideanSpace ℝ (Fin (d + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (d + 2)) :=
  LinearMap.mkContinuous
    { toFun := fun y => euclideanSnoc (d + 1) y 0
      map_add' := fun y₁ y₂ => by
        ext i
        simp only [euclideanSnoc, WithLp.equiv_symm_apply, WithLp.ofLp_add, Pi.add_apply]
        refine Fin.lastCases ?_ ?_ i
        · simp [Fin.snoc_last]
        · intro j; simp [Fin.snoc_castSucc]
      map_smul' := fun a y => by
        ext i
        simp only [euclideanSnoc, WithLp.equiv_symm_apply, WithLp.ofLp_smul,
          Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        refine Fin.lastCases ?_ ?_ i
        · simp [Fin.snoc_last]
        · intro j; simp [Fin.snoc_castSucc] }
    1 (fun y => by
      rw [one_mul]
      change ‖euclideanSnoc (d + 1) y 0‖ ≤ _
      have h : ‖euclideanSnoc (d + 1) y 0‖ ^ 2 = ‖y‖ ^ 2 := by
        rw [euclideanSnoc_norm_sq]; ring
      nlinarith [norm_nonneg (euclideanSnoc (d + 1) y 0), norm_nonneg y,
        sq_nonneg (‖euclideanSnoc (d + 1) y 0‖ - ‖y‖)])

private lemma euclideanSnoc_linearCLM_apply (d : ℕ)
    (y : EuclideanSpace ℝ (Fin (d + 1))) :
    euclideanSnoc_linearCLM d y = euclideanSnoc (d + 1) y 0 := rfl

private lemma euclideanSnoc_decomp (d : ℕ) (y : EuclideanSpace ℝ (Fin (d + 1))) (t : ℝ) :
    euclideanSnoc (d + 1) y t =
      euclideanSnoc (d + 1) 0 t + euclideanSnoc_linearCLM d y := by
  ext i
  simp only [euclideanSnoc, euclideanSnoc_linearCLM_apply,
    WithLp.equiv_symm_apply, WithLp.ofLp_add, Pi.add_apply]
  refine Fin.lastCases ?_ ?_ i
  · simp [Fin.snoc_last]
  · intro j; simp [Fin.snoc_castSucc]

private lemma euclideanSnoc_linearCLM_norm_le (d : ℕ) :
    ‖euclideanSnoc_linearCLM d‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- Pointwise bound: the y-seminorm of the slice `f ∘ euclideanSnoc · t` is
bounded by the seminorm of `f`, uniformly in `t`. This uses the chain rule
for the affine isometric embedding `y ↦ euclideanSnoc y t` together with
`euclideanSnoc_norm_ge_left` to transfer the polynomial weight.
-/
private lemma schwartz_slice_y_le_seminorm (d : ℕ)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin (d + 2))) ℝ)
    (t : ℝ) (k m : ℕ) (y : EuclideanSpace ℝ (Fin (d + 1))) :
    ‖y‖ ^ k * ‖iteratedFDeriv ℝ m (schwartz_slice_y d f t) y‖ ≤
      f.seminorm ℝ k m := by
  -- Step 1: schwartz_slice_y agrees with f ∘ euclideanSnoc · t pointwise
  -- and therefore has the same iteratedFDeriv
  set c := euclideanSnoc (d + 1) (0 : EuclideanSpace ℝ (Fin (d + 1))) t
  set L := euclideanSnoc_linearCLM d
  -- The slice function equals (f ∘ (c + ·)) ∘ L
  set f' : EuclideanSpace ℝ (Fin (d + 2)) → ℝ := fun z => f (c + z)
  -- Step 2: Chain rule for composition with L
  have hf'_smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) f' := by
    exact f.smooth'.comp (contDiff_const.add contDiff_id)
  have h_chain : iteratedFDeriv ℝ m (f' ∘ ⇑L) y =
      (iteratedFDeriv ℝ m f' (L y)).compContinuousLinearMap (fun _ => L) :=
    L.iteratedFDeriv_comp_right hf'_smooth y
      (WithTop.coe_le_coe.mpr le_top)
  -- Step 3: Translation invariance: iteratedFDeriv m f' z = iteratedFDeriv m f (c + z)
  have h_trans : ∀ z, iteratedFDeriv ℝ m f' z =
      iteratedFDeriv ℝ m (f : EuclideanSpace ℝ (Fin (d + 2)) → ℝ) (c + z) :=
    fun z => iteratedFDeriv_comp_add_left m c z
  -- Step 4: The slice function equals f' ∘ L
  have h_fun_eq : (schwartz_slice_y d f t : EuclideanSpace ℝ (Fin (d + 1)) → ℝ) =
      f' ∘ ⇑L := by
    ext y'
    simp only [schwartz_slice_y, compCLMOfAntilipschitz_apply, Function.comp_apply, f']
    congr 1
    exact euclideanSnoc_decomp d y' t
  -- Step 5: Norm bound on the iterated derivative
  have h_norm : ‖iteratedFDeriv ℝ m (schwartz_slice_y d f t) y‖ ≤
      ‖iteratedFDeriv ℝ m f (euclideanSnoc (d + 1) y t)‖ := by
    rw [show (schwartz_slice_y d f t : EuclideanSpace ℝ (Fin (d + 1)) → ℝ) = f' ∘ ⇑L
        from h_fun_eq]
    rw [h_chain]
    calc ‖(iteratedFDeriv ℝ m f' (L y)).compContinuousLinearMap (fun _ => L)‖
        ≤ ‖iteratedFDeriv ℝ m f' (L y)‖ * ∏ _ : Fin m, ‖L‖ :=
          ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
      _ ≤ ‖iteratedFDeriv ℝ m f' (L y)‖ * 1 := by
          gcongr
          calc ∏ _ : Fin m, ‖L‖ ≤ ∏ _ : Fin m, (1 : ℝ) :=
                Finset.prod_le_prod (fun _ _ => norm_nonneg _)
                  (fun _ _ => euclideanSnoc_linearCLM_norm_le d)
            _ = 1 := by simp
      _ = ‖iteratedFDeriv ℝ m f (c + L y)‖ := by rw [mul_one, h_trans]
      _ = ‖iteratedFDeriv ℝ m f (euclideanSnoc (d + 1) y t)‖ := by
          rw [euclideanSnoc_decomp d y t]
  -- Step 6: Combine with Schwartz decay
  calc ‖y‖ ^ k * ‖iteratedFDeriv ℝ m (schwartz_slice_y d f t) y‖
      ≤ ‖y‖ ^ k * ‖iteratedFDeriv ℝ m f (euclideanSnoc (d + 1) y t)‖ :=
        mul_le_mul_of_nonneg_left h_norm (pow_nonneg (norm_nonneg _) _)
    _ ≤ ‖euclideanSnoc (d + 1) y t‖ ^ k *
        ‖iteratedFDeriv ℝ m f (euclideanSnoc (d + 1) y t)‖ := by
        gcongr; exact euclideanSnoc_norm_ge_left d y t
    _ ≤ f.seminorm ℝ k m := SchwartzMap.le_seminorm ℝ k m f _

private lemma contDiff_parametric_hermiteCoeff (d : ℕ)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin (d + 2))) ℝ) (n : ℕ) :
    ContDiff ℝ ∞
      (fun y => ∫ t, f (euclideanSnoc (d + 1) y t) * hermiteFunction n t) ∧
    ∀ (m : ℕ) (y : EuclideanSpace ℝ (Fin (d + 1))),
      iteratedFDeriv ℝ m
        (fun y' => ∫ t, f (euclideanSnoc (d + 1) y' t) * hermiteFunction n t) y =
      ∫ t, iteratedFDeriv ℝ m
        (fun y' => f (euclideanSnoc (d + 1) y' t) * hermiteFunction n t) y := by
  -- Rewrite hermiteFunction n to ⇑(schwartzHermiteBasis1D n) so the textbook lemma applies
  simp_rw [show ∀ t, hermiteFunction n t = (schwartzHermiteBasis1D n) t from
    fun t => (schwartzHermiteBasis1D_apply n t).symm]
  exact contDiff_schwartz_parametric_integral f (schwartzHermiteBasis1D n)
    (euclideanSnoc (d + 1))
    (fun t => by -- hι_smooth: y ↦ euclideanSnoc y t is C^∞ (affine in y)
      rw [show (fun y => euclideanSnoc (d + 1) y t) =
        (fun y => euclideanSnoc (d + 1) 0 t + euclideanSnoc_linearCLM d y) from
        funext (fun y => euclideanSnoc_decomp d y t)]
      exact contDiff_const.add (euclideanSnoc_linearCLM d).contDiff)
    (fun m y => by -- hι_meas: t ↦ D^m_y[f(euclideanSnoc · t)] y is ae-measurable
      -- CLM chain rule: equals (iteratedFDeriv m f (euclideanSnoc y t)).compCLM (fun _ => L)
      set L := euclideanSnoc_linearCLM d
      have h_chain : ∀ t, iteratedFDeriv ℝ m (fun y' => f (euclideanSnoc (d + 1) y' t)) y =
          (iteratedFDeriv ℝ m (↑f : _ → ℝ) (euclideanSnoc (d + 1) y t)).compContinuousLinearMap
            (fun _ => L) := by
        intro t
        set c := euclideanSnoc (d + 1) (0 : EuclideanSpace ℝ (Fin (d + 1))) t
        have hf' : ContDiff ℝ (↑(⊤ : ℕ∞)) ((↑f : _ → ℝ) ∘ (c + ·)) :=
          f.smooth'.comp (contDiff_const.add contDiff_id)
        have h_eq : (fun y' => (↑f : _ → ℝ) (euclideanSnoc (d + 1) y' t)) =
            ((↑f : _ → ℝ) ∘ (c + ·)) ∘ ⇑L := by
          ext y'; simp only [Function.comp_apply]; congr 1
          exact euclideanSnoc_decomp d y' t
        rw [h_eq, L.iteratedFDeriv_comp_right hf' y (WithTop.coe_le_coe.mpr le_top)]
        congr 1
        change iteratedFDeriv ℝ m (fun z => (↑f : _ → ℝ) (c + z)) (L y) =
          iteratedFDeriv ℝ m (↑f : _ → ℝ) (euclideanSnoc (d + 1) y t)
        rw [iteratedFDeriv_comp_add_left]; congr 1
        exact (euclideanSnoc_decomp d y t).symm
      simp_rw [h_chain]
      have h_snoc_cont : Continuous (fun t : ℝ => euclideanSnoc (d + 1) y t) := by
        set L_t : ℝ →L[ℝ] EuclideanSpace ℝ (Fin (d + 2)) :=
          (EuclideanSpace.equiv (Fin (d + 2)) ℝ).symm.toContinuousLinearMap.comp
            (ContinuousLinearMap.single (R := ℝ) (φ := fun (_ : Fin (d + 2)) => ℝ)
              (Fin.last (d + 1)))
        have h_decomp : (fun t => euclideanSnoc (d + 1) y t) =
            (fun t => euclideanSnoc (d + 1) y 0 + L_t t) := by
          funext t
          simp only [L_t, euclideanSnoc, ContinuousLinearMap.comp_apply,
            ContinuousLinearMap.single_apply, ContinuousLinearEquiv.coe_coe]
          change (WithLp.equiv 2 _).symm (Fin.snoc (fun i => y.ofLp i) t) =
            (WithLp.equiv 2 _).symm (Fin.snoc (fun i => y.ofLp i) 0) +
            (EuclideanSpace.equiv (Fin (d + 2)) ℝ).symm (Pi.single (Fin.last (d + 1)) t)
          have : ∀ (s : ℝ), Fin.snoc (α := fun _ => ℝ) (fun i => y.ofLp i) s =
              Fin.snoc (α := fun _ => ℝ) (fun i => y.ofLp i) 0 +
                Pi.single (Fin.last (d + 1)) s := by
            intro s; ext i; rw [Pi.add_apply]
            refine Fin.lastCases ?_ ?_ i
            · simp [Fin.snoc_last]
            · intro j; simp [Fin.snoc_castSucc]
          rw [this t]; simp [EuclideanSpace.equiv]
        rw [h_decomp]; exact continuous_const.add L_t.continuous
      exact ((ContinuousMultilinearMap.compContinuousLinearMapL (fun _ => L)).continuous.comp
        ((f.smooth'.of_le (WithTop.coe_le_coe.mpr le_top)).continuous_iteratedFDeriv'.comp
          h_snoc_cont)).aestronglyMeasurable)
    (fun m => by -- hι_bound: ‖D^m_y[f(ι(·,t))](y)‖ ≤ C uniformly in y,t
      exact ⟨f.seminorm ℝ 0 m, fun y t => by
        have := schwartz_slice_y_le_seminorm d f t 0 m y
        simpa only [pow_zero, one_mul, schwartz_slice_y, compCLMOfAntilipschitz_apply,
          Function.comp_def] using this⟩)

/-- Smoothness of the partial Hermite coefficient: the function
`y ↦ ∫ f(y,t) ψ_n(t) dt` is `C^∞` in `y`.
-/
private lemma schwartz_partial_hermiteCoeff_smooth (d : ℕ)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin (d + 2))) ℝ)
    (n : ℕ) :
    ContDiff ℝ ∞ (fun y => hermiteCoeff1D n (schwartzSlice d f y)) :=
  (contDiff_parametric_hermiteCoeff d f n).1

/-- Schwartz decay of the partial Hermite coefficient: for all `k, m`,
`sup_y ‖y‖^k · ‖∂^m_y g(y)‖ < ∞` where `g(y) = ∫ f(y,t) ψ_n(t) dt`.

Uses `contDiff_parametric_hermiteCoeff` to commute derivatives with the integral,
then `schwartz_slice_y_le_seminorm` for the pointwise bound on each slice,
and integrates against `|ψ_n(t)| dt`.
-/
private lemma schwartz_partial_hermiteCoeff_decay (d : ℕ)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin (d + 2))) ℝ)
    (n : ℕ) (k m : ℕ) :
    ∃ C : ℝ, ∀ y : EuclideanSpace ℝ (Fin (d + 1)),
      ‖y‖ ^ k * ‖iteratedFDeriv ℝ m
        (fun y' => hermiteCoeff1D n (schwartzSlice d f y')) y‖ ≤ C := by
  -- The proof uses:
  -- 1. contDiff_parametric_hermiteCoeff to commute iteratedFDeriv with the integral
  -- 2. The constant hermiteFunction n t factors out of iteratedFDeriv in y
  -- 3. schwartz_slice_y_le_seminorm gives ‖y‖^k * ‖D^m(f∘snoc·t)(y)‖ ≤ seminorm f
  -- 4. Integrate against |ψ_n(t)| dt (finite since ψ_n is Schwartz)
  exact ⟨f.seminorm ℝ k m * ∫ t, ‖hermiteFunction n t‖, fun y => by
    obtain ⟨_, h_comm⟩ := contDiff_parametric_hermiteCoeff d f n
    change ‖y‖ ^ k * ‖iteratedFDeriv ℝ m
      (fun y' => ∫ t, f (euclideanSnoc (d + 1) y' t) * hermiteFunction n t) y‖ ≤ _
    rw [h_comm]
    -- Factor hermiteFunction n t out of iteratedFDeriv using const_smul
    have h_factor : ∀ t, iteratedFDeriv ℝ m
        (fun y' => f (euclideanSnoc (d + 1) y' t) * hermiteFunction n t) y =
        hermiteFunction n t • iteratedFDeriv ℝ m (schwartz_slice_y d f t) y := by
      intro t
      have h_eq : (fun y' => f (euclideanSnoc (d + 1) y' t) * hermiteFunction n t) =
          (fun y' => hermiteFunction n t • (schwartz_slice_y d f t) y') := by
        ext y'; simp [schwartz_slice_y, compCLMOfAntilipschitz_apply, smul_eq_mul, mul_comm]
      rw [h_eq]
      exact iteratedFDeriv_const_smul_apply'
        (((schwartz_slice_y d f t).smooth'.of_le
          (WithTop.coe_le_coe.mpr le_top)).contDiffAt)
    simp_rw [h_factor]
    -- Bound: ‖y‖^k * ‖∫ ψ(t) • D^m(slice)(y)‖ ≤ seminorm * ∫ ‖ψ‖
    calc ‖y‖ ^ k * ‖∫ t, hermiteFunction n t •
          iteratedFDeriv ℝ m (↑(schwartz_slice_y d f t)) y‖
        ≤ ‖y‖ ^ k * ∫ t, ‖hermiteFunction n t •
          iteratedFDeriv ℝ m (↑(schwartz_slice_y d f t)) y‖ := by
          gcongr; exact norm_integral_le_integral_norm _
      _ = ‖y‖ ^ k * ∫ t, ‖hermiteFunction n t‖ *
          ‖iteratedFDeriv ℝ m (↑(schwartz_slice_y d f t)) y‖ := by
          simp_rw [norm_smul]
      _ = ∫ t, ‖hermiteFunction n t‖ *
          (‖y‖ ^ k * ‖iteratedFDeriv ℝ m (↑(schwartz_slice_y d f t)) y‖) := by
          rw [← integral_const_mul]; congr 1; ext t; ring
      _ ≤ ∫ t, ‖hermiteFunction n t‖ * (f.seminorm ℝ k m) := by
          apply integral_mono_of_nonneg
          · exact Filter.Eventually.of_forall (fun t => mul_nonneg (norm_nonneg _)
              (mul_nonneg (pow_nonneg (norm_nonneg _) _) (norm_nonneg _)))
          · exact (hermiteCoeff_bound_integrable n (f.seminorm ℝ k m)).congr
              (Filter.Eventually.of_forall (fun t => by ring))
          · exact Filter.Eventually.of_forall (fun t =>
              mul_le_mul_of_nonneg_left
                (schwartz_slice_y_le_seminorm d f t k m y) (norm_nonneg _))
      _ = f.seminorm ℝ k m * ∫ t, ‖hermiteFunction n t‖ := by
          rw [← integral_const_mul]; congr 1; ext t; ring⟩

-- A2: Partial Hermite coefficient is Schwartz in remaining coordinates
/-- Integrate out the last coordinate of `f` against the `n`-th Hermite
function, giving a Schwartz function of the remaining `d + 1` coordinates.
-/
noncomputable def schwartzPartialHermiteCoeff (d : ℕ)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin (d + 2))) ℝ)
    (n : ℕ) :
    SchwartzMap (EuclideanSpace ℝ (Fin (d + 1))) ℝ where
  toFun y := hermiteCoeff1D n (schwartzSlice d f y)
  smooth' := schwartz_partial_hermiteCoeff_smooth d f n
  decay' := schwartz_partial_hermiteCoeff_decay d f n

-- A3b: Partial coefficient relates to 1D slice (definitionally true)
lemma schwartz_partial_hermiteCoeff_eq_1D (d : ℕ)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin (d + 2))) ℝ)
    (n : ℕ) (y : EuclideanSpace ℝ (Fin (d + 1))) :
    schwartzPartialHermiteCoeff d f n y =
      hermiteCoeff1D n (schwartzSlice d f y) := rfl

-- A3c: Slice evaluation (definitionally true)
lemma schwartz_slice_eq (d : ℕ)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin (d + 2))) ℝ)
    (y : EuclideanSpace ℝ (Fin (d + 1))) (t : ℝ) :
    schwartzSlice d f y t = f (euclideanSnoc (d + 1) y t) := rfl

/-- Fubini theorem for EuclideanSpace slicing.
Isolates the measure equivalence between ℝ^{d+2} and ℝ^{d+1} × ℝ.
-/
lemma integral_euclidean_snoc (d : ℕ) (g : EuclideanSpace ℝ (Fin (d + 2)) → ℝ)
    (hg : Integrable g) :
    ∫ x, g x = ∫ y : EuclideanSpace ℝ (Fin (d + 1)), ∫ t : ℝ, g (euclideanSnoc (d + 1) y t) := by
  -- Step 1: Transfer from EuclideanSpace to Fin (d+2) → ℝ via volume-preserving equiv
  have hv := PiLp.volume_preserving_toLp (ι := Fin (d + 2))
  rw [← hv.integral_comp' (f := MeasurableEquiv.toLp 2 _)]
  -- Step 2: Split Fin (d+2) → ℝ into ℝ × (Fin (d+1) → ℝ) via piFinSuccAbove at Fin.last
  set e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 2) => ℝ) (Fin.last (d + 1))).symm
  have hem : MeasurePreserving e :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (d + 2) => ℝ) (Fin.last (d + 1))).symm _
  rw [← hem.integral_comp' (f := e)]
  -- Step 3: Apply Fubini and swap integral order
  set F : ℝ × (Fin (d + 1) → ℝ) → ℝ :=
    fun p => g ((MeasurableEquiv.toLp 2 _) (e p))
  have hint : Integrable F :=
    (hem.integrable_comp_emb e.measurableEmbedding).mpr
      ((hv.integrable_comp_emb (MeasurableEquiv.toLp 2 _).measurableEmbedding).mpr hg)
  rw [volume_eq_prod] at hint ⊢
  rw [integral_prod _ hint, integral_integral_swap hint]
  -- Step 4: Transfer outer integral from Fin (d+1) → ℝ to EuclideanSpace
  have hv' := PiLp.volume_preserving_toLp (ι := Fin (d + 1))
  rw [← hv'.integral_comp' (f := MeasurableEquiv.toLp 2 _)]
  congr 1; funext y'
  congr 1; funext t
  -- Show the composed function equals g (euclideanSnoc ...)
  change F (t, y') = g (euclideanSnoc (d + 1) ((MeasurableEquiv.toLp 2 _) y') t)
  simp only [F, e, MeasurableEquiv.piFinSuccAbove_symm_apply, MeasurableEquiv.toLp,
    MeasurableEquiv.coe_mk]
  congr 1
  ext i
  simp only [euclideanSnoc, WithLp.equiv_symm_apply]
  refine Fin.lastCases ?_ ?_ i
  · simp [Fin.snoc_last]
  · intro j; simp [Fin.snoc_castSucc]

/-! ### Scalarization helpers for seminorm control

These helpers reduce the multi-dimensional seminorm control problem to 1D
by evaluating the multilinear map `D^{l'}_y[g_n]` along arbitrary vectors `v`,
reducing to a 1D problem solvable by `hermiteCoeff1D_decay`.
-/

/-- Chain rule: the `l'`-th derivative in `y` of `f(euclideanSnoc y t)` evaluated at vectors
`v` equals the `l'`-th derivative of `f` at `euclideanSnoc y t` evaluated at `L(v_i)` where
`L = euclideanSnoc_linearCLM d`.
-/
private lemma schwartz_slice_partial_chain_rule (d : ℕ)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin (d + 2))) ℝ) (l' : ℕ)
    (y : EuclideanSpace ℝ (Fin (d + 1)))
    (v : Fin l' → EuclideanSpace ℝ (Fin (d + 1))) (t : ℝ) :
    iteratedFDeriv ℝ l' (fun y' => f (euclideanSnoc (d + 1) y' t)) y v =
      (iteratedFDeriv ℝ l' (↑f : _ → ℝ) (euclideanSnoc (d + 1) y t))
        (fun i => euclideanSnoc_linearCLM d (v i)) := by
  set c := euclideanSnoc (d + 1) (0 : EuclideanSpace ℝ (Fin (d + 1))) t
  set L := euclideanSnoc_linearCLM d
  set f' : EuclideanSpace ℝ (Fin (d + 2)) → ℝ := fun z => f (c + z)
  have hf'_smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) f' :=
    f.smooth'.comp (contDiff_const.add contDiff_id)
  have h_fun_eq : (fun y' => f (euclideanSnoc (d + 1) y' t)) = f' ∘ ⇑L := by
    ext y'
    simp only [Function.comp_apply, f']
    congr 1
    exact euclideanSnoc_decomp d y' t
  rw [h_fun_eq]
  rw [L.iteratedFDeriv_comp_right hf'_smooth y (WithTop.coe_le_coe.mpr le_top)]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1
  ext u
  rw [iteratedFDeriv_comp_add_left,
    show c + L y = euclideanSnoc (d + 1) y t from (euclideanSnoc_decomp d y t).symm]

/-- The norm of `Pi.single (Fin.last (d+1)) t` embedded into EuclideanSpace is `‖t‖`.
Used for the `L_t` norm bound in several places.
-/
private lemma euclideanSnoc_Pi_single_norm_le (d : ℕ) (t : ℝ) :
    ‖(EuclideanSpace.equiv (Fin (d + 2)) ℝ).symm
      (Pi.single (Fin.last (d + 1)) t)‖ ≤ ‖t‖ := by
  rw [EuclideanSpace.norm_eq]
  rw [show ∑ i : Fin (d + 2),
      ‖((EuclideanSpace.equiv (Fin (d + 2)) ℝ).symm
        (Pi.single (Fin.last (d + 1)) t)) i‖ ^ 2 = ‖t‖ ^ 2 from by
    have : ∀ i : Fin (d + 2),
        ‖((EuclideanSpace.equiv (Fin (d + 2)) ℝ).symm
          (Pi.single (Fin.last (d + 1)) t)) i‖ ^ 2 =
        if i = Fin.last (d + 1) then ‖t‖ ^ 2 else 0 := by
      intro i
      simp only [EuclideanSpace.equiv, PiLp.continuousLinearEquiv_symm_apply,
        PiLp.toLp_apply, Pi.single_apply]
      by_cases hi : i = Fin.last (d + 1) <;> simp [hi]
    simp_rw [this, Finset.sum_ite_eq', Finset.mem_univ, if_true]]
  exact le_of_eq (Real.sqrt_sq (norm_nonneg t))

/-- The map `t ↦ euclideanSnoc y t` is smooth (affine in `t`). -/
private lemma euclideanSnoc_t_contDiff (d : ℕ)
    (y : EuclideanSpace ℝ (Fin (d + 1))) :
    ContDiff ℝ ∞ (fun t : ℝ => euclideanSnoc (d + 1) y t) := by
  unfold euclideanSnoc
  change ContDiff ℝ ∞ (⇑(PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : Fin (d + 2) => ℝ)).symm ∘ (fun t => Fin.snoc (fun i => y.ofLp i) t))
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (d + 2) => ℝ)).symm.contDiff.comp
    (contDiff_pi.mpr (fun i => by
      refine Fin.lastCases ?_ ?_ i
      · simp only [Fin.snoc_last]; exact contDiff_id
      · intro j; simp only [Fin.snoc_castSucc]; exact contDiff_const))

/-- The 1D Schwartz function obtained by evaluating the `l'`-th iterated Fréchet derivative
of a slice along vectors `v`. Used for the "scalarization" step: reduce the operator norm
of `D^{l'} g_n(y)` to pointwise evaluations that can be bounded via 1D Hermite decay.
-/
noncomputable def schwartzSlicePartial (d : ℕ)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin (d + 2))) ℝ) (l' : ℕ)
    (y : EuclideanSpace ℝ (Fin (d + 1)))
    (v : Fin l' → EuclideanSpace ℝ (Fin (d + 1))) :
    SchwartzMap ℝ ℝ where
  toFun t := iteratedFDeriv ℝ l' (fun y' => f (euclideanSnoc (d + 1) y' t)) y v
  smooth' := by
    set w := fun i => euclideanSnoc_linearCLM d (v i)
    set G : EuclideanSpace ℝ (Fin (d + 2)) → ℝ := fun z =>
      (iteratedFDeriv ℝ l' (↑f : _ → ℝ) z) w
    have h_eq : (fun t => iteratedFDeriv ℝ l' (fun y' =>
        f (euclideanSnoc (d + 1) y' t)) y v) =
        fun t => G (euclideanSnoc (d + 1) y t) := by
      ext t; exact schwartz_slice_partial_chain_rule d f l' y v t
    rw [h_eq]
    exact ((ContinuousMultilinearMap.apply ℝ _ ℝ w).contDiff.comp
      (f.smooth'.iteratedFDeriv_right (le_infty_add l'))).comp
      (euclideanSnoc_t_contDiff d y)
  decay' := by
    -- The function equals G ∘ (euclideanSnoc y) where
    -- G z = (iteratedFDeriv ℝ l' f z) w, w = L(v_i)
    set L := euclideanSnoc_linearCLM d
    set w : Fin l' → EuclideanSpace ℝ (Fin (d + 2)) := fun i => L (v i)
    set G : EuclideanSpace ℝ (Fin (d + 2)) → ℝ := fun z =>
      (iteratedFDeriv ℝ l' (↑f : _ → ℝ) z) w
    intro k b
    -- The bound: ‖t‖^k * ‖D^b toFun(t)‖ ≤ C_w * f.seminorm(k, b+l')
    -- where C_w = ‖apply w‖
    set C_w := ‖ContinuousMultilinearMap.apply ℝ
      (fun _ : Fin l' => EuclideanSpace ℝ (Fin (d + 2))) ℝ w‖
    refine ⟨C_w * f.seminorm ℝ k (b + l'), fun t => ?_⟩
    -- The same proof as schwartz_slice_partial_pointwise_bound with k_y = 0
    -- First, toFun t = G(euclideanSnoc y t) by chain rule
    have h_val : iteratedFDeriv ℝ l' (fun y' =>
        f (euclideanSnoc (d + 1) y' t)) y v = G (euclideanSnoc (d + 1) y t) :=
      schwartz_slice_partial_chain_rule d f l' y v t
    -- D^b toFun is the b-th t-derivative, bounded via chain rule for G ∘ (euclideanSnoc y ·)
    -- Key: toFun = G ∘ (euclideanSnoc y ·) as functions
    have h_fun_eq : (fun t => iteratedFDeriv ℝ l' (fun y' =>
        f (euclideanSnoc (d + 1) y' t)) y v) =
        fun t => G (euclideanSnoc (d + 1) y t) := by
      ext s; exact schwartz_slice_partial_chain_rule d f l' y v s
    -- Rewrite iteratedFDeriv using the functional equality
    rw [h_fun_eq]
    -- Now bound using the t-chain rule (same approach as h_deriv in pointwise_bound)
    set L_t : ℝ →L[ℝ] EuclideanSpace ℝ (Fin (d + 2)) :=
      (EuclideanSpace.equiv (Fin (d + 2)) ℝ).symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.single (R := ℝ) (φ := fun (_ : Fin (d + 2)) => ℝ)
          (Fin.last (d + 1)))
    set c₀ := euclideanSnoc (d + 1) y 0
    have h_snoc_eq : (fun t => euclideanSnoc (d + 1) y t) = (fun t => c₀ + L_t t) := by
      funext s
      simp only [c₀, L_t, euclideanSnoc, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.single_apply, ContinuousLinearEquiv.coe_coe]
      change (WithLp.equiv 2 _).symm (Fin.snoc (fun i => y.ofLp i) s) =
        (WithLp.equiv 2 _).symm (Fin.snoc (fun i => y.ofLp i) 0) +
        (EuclideanSpace.equiv (Fin (d + 2)) ℝ).symm (Pi.single (Fin.last (d + 1)) s)
      have : ∀ (u : ℝ), Fin.snoc (α := fun _ => ℝ) (fun i => y.ofLp i) u =
          Fin.snoc (α := fun _ => ℝ) (fun i => y.ofLp i) 0 +
            Pi.single (Fin.last (d + 1)) u := by
        intro u; ext i; rw [Pi.add_apply]
        refine Fin.lastCases ?_ ?_ i
        · simp [Fin.snoc_last]
        · intro j; simp [Fin.snoc_castSucc]
      rw [this s]; simp [EuclideanSpace.equiv]
    have h_Lt_norm : ‖L_t‖ ≤ 1 := by
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro s; rw [one_mul]
      exact euclideanSnoc_Pi_single_norm_le d s
    have h_G_smooth : ContDiff ℝ ∞ G :=
      (ContinuousMultilinearMap.apply ℝ _ ℝ w).contDiff.comp
        (f.smooth'.iteratedFDeriv_right (le_infty_add l'))
    -- Bound ‖D^b_t[G ∘ snoc](t)‖ ≤ ‖D^b G(snoc y t)‖ (chain rule + ‖L_t‖ ≤ 1)
    set G' := fun z => G (c₀ + z)
    have hG'_smooth : ContDiff ℝ ∞ G' := h_G_smooth.comp (contDiff_const.add contDiff_id)
    have h_fun_eq2 : (fun t => G (euclideanSnoc (d + 1) y t)) = G' ∘ ⇑L_t := by
      funext s; exact congr_arg G (congr_fun h_snoc_eq s)
    have h_deriv_bound : ‖iteratedFDeriv ℝ b (fun t => G (euclideanSnoc (d + 1) y t)) t‖ ≤
        ‖iteratedFDeriv ℝ b G (euclideanSnoc (d + 1) y t)‖ := by
      rw [h_fun_eq2,
          L_t.iteratedFDeriv_comp_right hG'_smooth t (WithTop.coe_le_coe.mpr le_top)]
      calc ‖(iteratedFDeriv ℝ b G' (L_t t)).compContinuousLinearMap fun _ => L_t‖
          ≤ ‖iteratedFDeriv ℝ b G' (L_t t)‖ * ∏ _ : Fin b, ‖L_t‖ :=
            ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
        _ ≤ ‖iteratedFDeriv ℝ b G' (L_t t)‖ * 1 := by
            gcongr; calc ∏ _ : Fin b, ‖L_t‖ ≤ ∏ _ : Fin b, (1 : ℝ) :=
                  Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun _ _ => h_Lt_norm)
              _ = 1 := by simp
        _ = ‖iteratedFDeriv ℝ b G (c₀ + L_t t)‖ := by
            rw [mul_one]; congr 1; exact iteratedFDeriv_comp_add_left b c₀ (L_t t)
        _ = ‖iteratedFDeriv ℝ b G (euclideanSnoc (d + 1) y t)‖ := by
            rw [show c₀ + L_t t = euclideanSnoc (d + 1) y t from
              (congr_fun h_snoc_eq t).symm]
    -- Bound ‖D^b G(z)‖ ≤ C_w * ‖D^(b+l') f(z)‖
    set L_apply := ContinuousMultilinearMap.apply ℝ
      (fun _ : Fin l' => EuclideanSpace ℝ (Fin (d + 2))) ℝ w
    have hf_smooth_l' : ContDiff ℝ ∞ (iteratedFDeriv ℝ l' (↑f : _ → ℝ)) :=
      f.smooth'.iteratedFDeriv_right (le_infty_add l')
    have h_G_bound : ‖iteratedFDeriv ℝ b G (euclideanSnoc (d + 1) y t)‖ ≤
        C_w * ‖iteratedFDeriv ℝ (b + l') (↑f : _ → ℝ) (euclideanSnoc (d + 1) y t)‖ := by
      calc ‖iteratedFDeriv ℝ b G (euclideanSnoc (d + 1) y t)‖
          = ‖L_apply.compContinuousMultilinearMap
              (iteratedFDeriv ℝ b (iteratedFDeriv ℝ l' (↑f : _ → ℝ))
                (euclideanSnoc (d + 1) y t))‖ := by
            rw [show G = ⇑L_apply ∘ (iteratedFDeriv ℝ l' (↑f : _ → ℝ)) from rfl,
                L_apply.iteratedFDeriv_comp_left
                  hf_smooth_l'.contDiffAt (nat_le_infty b)]
        _ ≤ ‖L_apply‖ *
            ‖iteratedFDeriv ℝ b (iteratedFDeriv ℝ l' (↑f : _ → ℝ))
              (euclideanSnoc (d + 1) y t)‖ :=
            L_apply.norm_compContinuousMultilinearMap_le _
        _ = _ := by rw [norm_iteratedFDeriv_iteratedFDeriv]
    -- Combine: ‖t‖^k * ‖D^b(toFun)(t)‖ ≤ C_w * f.seminorm(k, b+l')
    calc ‖t‖ ^ k * ‖iteratedFDeriv ℝ b (fun t => G (euclideanSnoc (d + 1) y t)) t‖
        ≤ ‖t‖ ^ k * ‖iteratedFDeriv ℝ b G (euclideanSnoc (d + 1) y t)‖ :=
          mul_le_mul_of_nonneg_left h_deriv_bound (pow_nonneg (norm_nonneg _) _)
      _ ≤ ‖t‖ ^ k * (C_w * ‖iteratedFDeriv ℝ (b + l') (↑f : _ → ℝ)
            (euclideanSnoc (d + 1) y t)‖) :=
          mul_le_mul_of_nonneg_left h_G_bound (pow_nonneg (norm_nonneg _) _)
      _ = C_w * (‖t‖ ^ k *
            ‖iteratedFDeriv ℝ (b + l') (↑f : _ → ℝ) (euclideanSnoc (d + 1) y t)‖) := by
          ring
      _ ≤ C_w * (‖euclideanSnoc (d + 1) y t‖ ^ k *
            ‖iteratedFDeriv ℝ (b + l') (↑f : _ → ℝ) (euclideanSnoc (d + 1) y t)‖) := by
          gcongr; exact euclideanSnoc_norm_ge_right d y t
      _ ≤ C_w * f.seminorm ℝ k (b + l') := by
          gcongr; exact SchwartzMap.le_seminorm ℝ k (b + l') f _

/-- The iterated Fréchet derivative of `schwartzPartialHermiteCoeff d f n` evaluated
at `y` along vectors `v` equals the 1D Hermite coefficient of the corresponding
slice partial function. This is the key "commutation" lemma that connects the
multi-d seminorm to a 1D quantity.
-/
lemma schwartz_partial_hermiteCoeff_iteratedFDeriv (d : ℕ)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin (d + 2))) ℝ) (n l' : ℕ)
    (y : EuclideanSpace ℝ (Fin (d + 1)))
    (v : Fin l' → EuclideanSpace ℝ (Fin (d + 1))) :
    iteratedFDeriv ℝ l' (schwartzPartialHermiteCoeff d f n) y v =
      hermiteCoeff1D n (schwartzSlicePartial d f l' y v) := by
  -- Step 1: Commute iteratedFDeriv with the integral
  obtain ⟨_, h_comm⟩ := contDiff_parametric_hermiteCoeff d f n
  change (iteratedFDeriv ℝ l' (fun y' =>
    ∫ t, f (euclideanSnoc (d + 1) y' t) * hermiteFunction n t) y) v = _
  rw [h_comm]
  -- Step 2: Factor hermiteFunction n t out of iteratedFDeriv and evaluate at v
  have h_factor_v : ∀ t, (iteratedFDeriv ℝ l'
      (fun y' => f (euclideanSnoc (d + 1) y' t) * hermiteFunction n t) y) v =
      schwartzSlicePartial d f l' y v t * hermiteFunction n t := by
    intro t
    have h_eq : (fun y' => f (euclideanSnoc (d + 1) y' t) * hermiteFunction n t) =
        (fun y' => hermiteFunction n t • (schwartz_slice_y d f t) y') := by
      ext y'; simp [schwartz_slice_y, compCLMOfAntilipschitz_apply, smul_eq_mul, mul_comm]
    rw [h_eq]
    have h_smul : iteratedFDeriv ℝ l'
        (fun y' => hermiteFunction n t • (schwartz_slice_y d f t) y') y =
        hermiteFunction n t • iteratedFDeriv ℝ l' (↑(schwartz_slice_y d f t)) y :=
      iteratedFDeriv_const_smul_apply'
        (((schwartz_slice_y d f t).smooth'.of_le
          (WithTop.coe_le_coe.mpr le_top)).contDiffAt)
    rw [h_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul, mul_comm]
    -- schwartz_slice_y d f t = f ∘ euclideanSnoc · t (definitional)
    rfl
  -- Step 3: Pull evaluation at v inside the integral using integral_apply
  have h_int : Integrable (fun t => iteratedFDeriv ℝ l'
      (fun y' => f (euclideanSnoc (d + 1) y' t) * hermiteFunction n t) y) := by
    apply (hermiteCoeff_bound_integrable n (f.seminorm ℝ 0 l')).mono'
    · -- AEStronglyMeasurable: show the CLM-valued integrand is continuous
      apply Continuous.aestronglyMeasurable
      set L := euclideanSnoc_linearCLM d
      -- CLM-level chain rule: iteratedFDeriv l' (f ∘ euclideanSnoc · t) y =
      --   (iteratedFDeriv l' f (euclideanSnoc y t)).compCLM (fun _ => L)
      have h_chain : ∀ t, iteratedFDeriv ℝ l'
            (fun y' => (↑f : _ → ℝ) (euclideanSnoc (d + 1) y' t)) y =
          (iteratedFDeriv ℝ l' (↑f : _ → ℝ) (euclideanSnoc (d + 1) y t)).compContinuousLinearMap
            (fun _ => L) := by
        intro t
        set c := euclideanSnoc (d + 1) (0 : EuclideanSpace ℝ (Fin (d + 1))) t
        have hf' : ContDiff ℝ (↑(⊤ : ℕ∞)) ((↑f : _ → ℝ) ∘ (c + ·)) :=
          f.smooth'.comp (contDiff_const.add contDiff_id)
        have h_eq : (fun y' => (↑f : _ → ℝ) (euclideanSnoc (d + 1) y' t)) =
            ((↑f : _ → ℝ) ∘ (c + ·)) ∘ ⇑L := by
          ext y'; simp only [Function.comp_apply]; congr 1
          exact euclideanSnoc_decomp d y' t
        rw [h_eq, L.iteratedFDeriv_comp_right hf' y (WithTop.coe_le_coe.mpr le_top)]
        congr 1
        change iteratedFDeriv ℝ l' (fun z => (↑f : _ → ℝ) (c + z)) (L y) =
          iteratedFDeriv ℝ l' (↑f : _ → ℝ) (euclideanSnoc (d + 1) y t)
        rw [iteratedFDeriv_comp_add_left]; congr 1
        exact (euclideanSnoc_decomp d y t).symm
      -- Factor out hermiteFunction and combine with chain rule
      have h_fn_eq : (fun t => iteratedFDeriv ℝ l'
            (fun y' => f (euclideanSnoc (d + 1) y' t) * hermiteFunction n t) y) =
          (fun t => hermiteFunction n t •
            (iteratedFDeriv ℝ l' (↑f : _ → ℝ)
              (euclideanSnoc (d + 1) y t)).compContinuousLinearMap
              (fun _ => L)) := by
        ext t
        have h_mul : (fun y' => f (euclideanSnoc (d + 1) y' t) * hermiteFunction n t) =
            (fun y' => hermiteFunction n t • (schwartz_slice_y d f t) y') := by
          ext y'; simp [schwartz_slice_y, compCLMOfAntilipschitz_apply, smul_eq_mul, mul_comm]
        rw [h_mul]
        have h_smul : iteratedFDeriv ℝ l'
            (fun y' => hermiteFunction n t • (schwartz_slice_y d f t) y') y =
            hermiteFunction n t • iteratedFDeriv ℝ l' (↑(schwartz_slice_y d f t)) y :=
          iteratedFDeriv_const_smul_apply'
            (((schwartz_slice_y d f t).smooth'.of_le
              (WithTop.coe_le_coe.mpr le_top)).contDiffAt)
        rw [h_smul]
        have h_inner : iteratedFDeriv ℝ l' (↑(schwartz_slice_y d f t)) y =
            (iteratedFDeriv ℝ l' (↑f : _ → ℝ)
              (euclideanSnoc (d + 1) y t)).compContinuousLinearMap (fun _ => L) := by
          have h_sw : (↑(schwartz_slice_y d f t) : _ → ℝ) =
              fun y' => (↑f : _ → ℝ) (euclideanSnoc (d + 1) y' t) := by
            ext y'; simp [schwartz_slice_y, compCLMOfAntilipschitz_apply]
          rw [h_sw]; exact h_chain t
        rw [h_inner]
      rw [h_fn_eq]
      -- Continuity of fun t => euclideanSnoc y t via CLM decomposition
      have h_snoc_cont : Continuous (fun t : ℝ => euclideanSnoc (d + 1) y t) := by
        set L_t : ℝ →L[ℝ] EuclideanSpace ℝ (Fin (d + 2)) :=
          (EuclideanSpace.equiv (Fin (d + 2)) ℝ).symm.toContinuousLinearMap.comp
            (ContinuousLinearMap.single (R := ℝ) (φ := fun (_ : Fin (d + 2)) => ℝ)
              (Fin.last (d + 1)))
        have h_decomp : (fun t => euclideanSnoc (d + 1) y t) =
            (fun t => euclideanSnoc (d + 1) y 0 + L_t t) := by
          funext t
          simp only [L_t, euclideanSnoc, ContinuousLinearMap.comp_apply,
            ContinuousLinearMap.single_apply, ContinuousLinearEquiv.coe_coe]
          change (WithLp.equiv 2 _).symm (Fin.snoc (fun i => y.ofLp i) t) =
            (WithLp.equiv 2 _).symm (Fin.snoc (fun i => y.ofLp i) 0) +
            (EuclideanSpace.equiv (Fin (d + 2)) ℝ).symm (Pi.single (Fin.last (d + 1)) t)
          have : ∀ (s : ℝ), Fin.snoc (α := fun _ => ℝ) (fun i => y.ofLp i) s =
              Fin.snoc (fun i => y.ofLp i) 0 + Pi.single (Fin.last (d + 1)) s := by
            intro s; ext i; rw [Pi.add_apply]
            refine Fin.lastCases ?_ ?_ i
            · simp [Fin.snoc_last]
            · intro j; simp [Fin.snoc_castSucc]
          rw [this t]; simp [EuclideanSpace.equiv]
        rw [h_decomp]; exact continuous_const.add L_t.continuous
      exact Continuous.smul (hermiteFunction_contDiff n 0).continuous
        ((ContinuousMultilinearMap.compContinuousLinearMapL (fun _ => L)).continuous.comp
          ((f.smooth'.of_le (WithTop.coe_le_coe.mpr le_top)).continuous_iteratedFDeriv'.comp
            h_snoc_cont))
    · exact Filter.Eventually.of_forall (fun t => by
        have h_eq' : (fun y' => f (euclideanSnoc (d + 1) y' t) * hermiteFunction n t) =
            (fun y' => hermiteFunction n t • (schwartz_slice_y d f t) y') := by
          ext y'; simp [schwartz_slice_y, compCLMOfAntilipschitz_apply, smul_eq_mul, mul_comm]
        rw [h_eq']
        have h_smul' : iteratedFDeriv ℝ l'
            (fun y' => hermiteFunction n t • (schwartz_slice_y d f t) y') y =
            hermiteFunction n t • iteratedFDeriv ℝ l' (↑(schwartz_slice_y d f t)) y :=
          iteratedFDeriv_const_smul_apply'
            (((schwartz_slice_y d f t).smooth'.of_le
              (WithTop.coe_le_coe.mpr le_top)).contDiffAt)
        rw [h_smul', norm_smul]
        calc ‖hermiteFunction n t‖ * ‖iteratedFDeriv ℝ l' (↑(schwartz_slice_y d f t)) y‖
            ≤ ‖hermiteFunction n t‖ * f.seminorm ℝ 0 l' := by
              gcongr; simpa using schwartz_slice_y_le_seminorm d f t 0 l' y
          _ = f.seminorm ℝ 0 l' * ‖hermiteFunction n t‖ := mul_comm _ _)
  rw [ContinuousMultilinearMap.integral_apply h_int v]
  congr 1; ext t
  exact h_factor_v t

/-- Pointwise bound for the scalarized slice: for each `t`,
`‖y‖^k * ‖t‖^a * ‖D^b_t[slice_partial](t)‖ ≤ ‖apply w‖ * f.seminorm (k+a) (b+l')`.
Combines the chain rule, CLM norm bounds, and Schwartz decay.
-/
private lemma schwartz_slice_partial_pointwise_bound (d : ℕ)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin (d + 2))) ℝ) (l' : ℕ)
    (y : EuclideanSpace ℝ (Fin (d + 1)))
    (v : Fin l' → EuclideanSpace ℝ (Fin (d + 1))) (k a b : ℕ) (t : ℝ) :
    ‖y‖ ^ k * (‖t‖ ^ a * ‖iteratedFDeriv ℝ b
      (↑(schwartzSlicePartial d f l' y v)) t‖) ≤
      ‖ContinuousMultilinearMap.apply ℝ
        (fun _ : Fin l' => EuclideanSpace ℝ (Fin (d + 2))) ℝ
        (fun i => euclideanSnoc_linearCLM d (v i))‖ *
      f.seminorm ℝ (k + a) (b + l') := by
  set L := euclideanSnoc_linearCLM d
  set w : Fin l' → EuclideanSpace ℝ (Fin (d + 2)) := fun i => L (v i)
  set g := schwartzSlicePartial d f l' y v
  set G : EuclideanSpace ℝ (Fin (d + 2)) → ℝ := fun z =>
    (iteratedFDeriv ℝ l' (↑f : _ → ℝ) z) w
  -- Step 1: Chain rule bound on b-th t-derivative
  set L_t : ℝ →L[ℝ] EuclideanSpace ℝ (Fin (d + 2)) :=
    (EuclideanSpace.equiv (Fin (d + 2)) ℝ).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.single (R := ℝ) (φ := fun (_ : Fin (d + 2)) => ℝ)
        (Fin.last (d + 1)))
  set c₀ := euclideanSnoc (d + 1) y 0
  have h_snoc_eq : (fun t => euclideanSnoc (d + 1) y t) = (fun t => c₀ + L_t t) := by
    funext t
    simp only [c₀, L_t, euclideanSnoc, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.single_apply, ContinuousLinearEquiv.coe_coe]
    change (WithLp.equiv 2 _).symm (Fin.snoc (fun i => y.ofLp i) t) =
      (WithLp.equiv 2 _).symm (Fin.snoc (fun i => y.ofLp i) 0) +
      (EuclideanSpace.equiv (Fin (d + 2)) ℝ).symm (Pi.single (Fin.last (d + 1)) t)
    have : ∀ (s : ℝ), Fin.snoc (α := fun _ => ℝ) (fun i => y.ofLp i) s =
        Fin.snoc (α := fun _ => ℝ) (fun i => y.ofLp i) 0 +
          Pi.single (Fin.last (d + 1)) s := by
      intro s; ext i; rw [Pi.add_apply]
      refine Fin.lastCases ?_ ?_ i
      · simp [Fin.snoc_last]
      · intro j; simp [Fin.snoc_castSucc]
    rw [this t]; simp [EuclideanSpace.equiv]
  have h_Lt_norm : ‖L_t‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro t; rw [one_mul]
    exact euclideanSnoc_Pi_single_norm_le d t
  have h_G_smooth : ContDiff ℝ ∞ G :=
    (ContinuousMultilinearMap.apply ℝ _ ℝ w).contDiff.comp
      (f.smooth'.iteratedFDeriv_right (le_infty_add l'))
  -- Bound: ‖D^b_t[g](t)‖ ≤ ‖D^b G(euclideanSnoc y t)‖
  set G' := fun z => G (c₀ + z)
  have hG'_smooth : ContDiff ℝ ∞ G' := h_G_smooth.comp (contDiff_const.add contDiff_id)
  -- Key functional equality: g = G' ∘ L_t (avoids rw under iteratedFDeriv)
  have h_fun_eq : (↑g : ℝ → ℝ) = G' ∘ ⇑L_t := by
    ext s
    change g s = G (c₀ + L_t s)
    rw [show c₀ + L_t s = euclideanSnoc (d + 1) y s from (congr_fun h_snoc_eq s).symm]
    exact schwartz_slice_partial_chain_rule d f l' y v s
  have h_deriv : ‖iteratedFDeriv ℝ b (↑g) t‖ ≤
      ‖iteratedFDeriv ℝ b G (euclideanSnoc (d + 1) y t)‖ := by
    rw [h_fun_eq,
        L_t.iteratedFDeriv_comp_right hG'_smooth t (WithTop.coe_le_coe.mpr le_top)]
    calc ‖(iteratedFDeriv ℝ b G' (L_t t)).compContinuousLinearMap fun _ => L_t‖
        ≤ ‖iteratedFDeriv ℝ b G' (L_t t)‖ * ∏ _ : Fin b, ‖L_t‖ :=
          ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
      _ ≤ ‖iteratedFDeriv ℝ b G' (L_t t)‖ * 1 := by
          gcongr; calc ∏ _ : Fin b, ‖L_t‖ ≤ ∏ _ : Fin b, (1 : ℝ) :=
                Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun _ _ => h_Lt_norm)
            _ = 1 := by simp
      _ = ‖iteratedFDeriv ℝ b G (c₀ + L_t t)‖ := by
          rw [mul_one]; congr 1; exact iteratedFDeriv_comp_add_left b c₀ (L_t t)
      _ = ‖iteratedFDeriv ℝ b G (euclideanSnoc (d + 1) y t)‖ := by
          rw [show c₀ + L_t t = euclideanSnoc (d + 1) y t from (congr_fun h_snoc_eq t).symm]
  -- Step 2: ‖D^b G z‖ ≤ ‖apply w‖ * ‖D^(b+l') f z‖
  have h_G_bound : ‖iteratedFDeriv ℝ b G (euclideanSnoc (d + 1) y t)‖ ≤
      ‖ContinuousMultilinearMap.apply ℝ _ ℝ w‖ *
        ‖iteratedFDeriv ℝ (b + l') (↑f : _ → ℝ) (euclideanSnoc (d + 1) y t)‖ := by
    set L_apply := ContinuousMultilinearMap.apply ℝ
      (fun _ : Fin l' => EuclideanSpace ℝ (Fin (d + 2))) ℝ w
    have hf_smooth_l' : ContDiff ℝ ∞ (iteratedFDeriv ℝ l' (↑f : _ → ℝ)) :=
      f.smooth'.iteratedFDeriv_right (le_infty_add l')
    have h_G_eq : G = ⇑L_apply ∘ (iteratedFDeriv ℝ l' (↑f : _ → ℝ)) := rfl
    calc ‖iteratedFDeriv ℝ b G (euclideanSnoc (d + 1) y t)‖
        = ‖L_apply.compContinuousMultilinearMap
            (iteratedFDeriv ℝ b (iteratedFDeriv ℝ l' (↑f : _ → ℝ))
              (euclideanSnoc (d + 1) y t))‖ := by
          rw [h_G_eq, L_apply.iteratedFDeriv_comp_left
            hf_smooth_l'.contDiffAt (nat_le_infty b)]
      _ ≤ ‖L_apply‖ *
          ‖iteratedFDeriv ℝ b (iteratedFDeriv ℝ l' (↑f : _ → ℝ))
            (euclideanSnoc (d + 1) y t)‖ :=
          L_apply.norm_compContinuousMultilinearMap_le _
      _ = _ := by rw [norm_iteratedFDeriv_iteratedFDeriv]
  -- Step 3: Combine with polynomial weights
  set C_w := ‖ContinuousMultilinearMap.apply ℝ
    (fun _ : Fin l' => EuclideanSpace ℝ (Fin (d + 2))) ℝ w‖
  calc ‖y‖ ^ k * (‖t‖ ^ a * ‖iteratedFDeriv ℝ b (↑g) t‖)
      ≤ ‖y‖ ^ k * (‖t‖ ^ a * ‖iteratedFDeriv ℝ b G (euclideanSnoc (d + 1) y t)‖) := by
        gcongr
    _ ≤ ‖y‖ ^ k * (‖t‖ ^ a * (C_w *
          ‖iteratedFDeriv ℝ (b + l') (↑f : _ → ℝ) (euclideanSnoc (d + 1) y t)‖)) := by
        gcongr
    _ = C_w * (‖y‖ ^ k * ‖t‖ ^ a *
          ‖iteratedFDeriv ℝ (b + l') (↑f : _ → ℝ) (euclideanSnoc (d + 1) y t)‖) := by ring
    _ ≤ C_w * (‖euclideanSnoc (d + 1) y t‖ ^ (k + a) *
          ‖iteratedFDeriv ℝ (b + l') (↑f : _ → ℝ) (euclideanSnoc (d + 1) y t)‖) := by
        gcongr
        calc ‖y‖ ^ k * ‖t‖ ^ a
            ≤ ‖euclideanSnoc (d + 1) y t‖ ^ k * ‖euclideanSnoc (d + 1) y t‖ ^ a := by
              gcongr
              · exact euclideanSnoc_norm_ge_left d y t
              · exact euclideanSnoc_norm_ge_right d y t
          _ = ‖euclideanSnoc (d + 1) y t‖ ^ (k + a) := (pow_add _ k a).symm
    _ ≤ C_w * f.seminorm ℝ (k + a) (b + l') := by
        gcongr; exact SchwartzMap.le_seminorm ℝ (k + a) (b + l') f _

/-- Seminorm bound for the slice partial function: the 1D Schwartz seminorm of
`schwartzSlicePartial d f l' y v`, weighted by `‖y‖^k'`, is bounded by a product
of `∏ ‖v_i‖` and finitely many higher-dimensional seminorms of `f`.
-/
lemma schwartz_slice_partial_seminorm_bound (d : ℕ) (k' l' a b : ℕ) :
    ∃ (C : ℝ) (q' : Finset (ℕ × ℕ)), 0 < C ∧
      ∀ (f : SchwartzMap (EuclideanSpace ℝ (Fin (d + 2))) ℝ)
        (y : EuclideanSpace ℝ (Fin (d + 1)))
        (v : Fin l' → EuclideanSpace ℝ (Fin (d + 1))),
        ‖y‖ ^ k' * schwartzSeminormFamily ℝ ℝ ℝ (a, b)
          (schwartzSlicePartial d f l' y v) ≤
          C * (∏ i, ‖v i‖) *
            q'.sup (schwartzSeminormFamily ℝ (EuclideanSpace ℝ (Fin (d + 2))) ℝ) f
    := by
  refine ⟨1, {(k' + a, b + l')}, one_pos, fun f y v => ?_⟩
  simp only [Finset.sup_singleton, one_mul]
  set g := schwartzSlicePartial d f l' y v
  set L := euclideanSnoc_linearCLM d
  set w : Fin l' → EuclideanSpace ℝ (Fin (d + 2)) := fun i => L (v i)
  -- The apply norm is bounded by ∏ ‖w_i‖ ≤ ∏ ‖v_i‖
  have h_apply_le : ‖ContinuousMultilinearMap.apply ℝ
      (fun _ : Fin l' => EuclideanSpace ℝ (Fin (d + 2))) ℝ w‖ ≤ ∏ i : Fin l', ‖v i‖ := by
    calc ‖ContinuousMultilinearMap.apply ℝ _ ℝ w‖
        ≤ ∏ i, ‖w i‖ := by
          apply ContinuousLinearMap.opNorm_le_bound
          · exact Finset.prod_nonneg (fun _ _ => norm_nonneg _)
          · intro A
            calc ‖A w‖ ≤ ‖A‖ * ∏ i, ‖w i‖ := A.le_opNorm w
              _ = (∏ i, ‖w i‖) * ‖A‖ := mul_comm _ _
      _ ≤ ∏ i, ‖v i‖ := by
          apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
          intro i _
          calc ‖w i‖ = ‖L (v i)‖ := rfl
            _ ≤ ‖L‖ * ‖v i‖ := ContinuousLinearMap.le_opNorm L (v i)
            _ ≤ 1 * ‖v i‖ := by gcongr; exact euclideanSnoc_linearCLM_norm_le d
            _ = ‖v i‖ := one_mul _
  -- From pointwise bound to seminorm bound
  by_cases hy : ‖y‖ ^ k' = 0
  · simp only [hy, zero_mul]
    positivity
  · have hy_pos : 0 < ‖y‖ ^ k' := lt_of_le_of_ne (pow_nonneg (norm_nonneg _) _) (Ne.symm hy)
    have h_sem : SchwartzMap.seminorm ℝ a b g ≤
        ((∏ i : Fin l', ‖v i‖) * f.seminorm ℝ (k' + a) (b + l')) / ‖y‖ ^ k' := by
      apply SchwartzMap.seminorm_le_bound ℝ a b g (by positivity)
      intro t
      rw [le_div_iff₀ hy_pos]
      calc ‖t‖ ^ a * ‖iteratedFDeriv ℝ b (↑g) t‖ * ‖y‖ ^ k'
          = ‖y‖ ^ k' * (‖t‖ ^ a * ‖iteratedFDeriv ℝ b (↑g) t‖) := by ring
        _ ≤ ‖ContinuousMultilinearMap.apply ℝ _ ℝ w‖ * f.seminorm ℝ (k' + a) (b + l') :=
            schwartz_slice_partial_pointwise_bound d f l' y v k' a b t
        _ ≤ (∏ i : Fin l', ‖v i‖) * f.seminorm ℝ (k' + a) (b + l') := by
            gcongr
    calc ‖y‖ ^ k' * SchwartzMap.seminorm ℝ a b g
        ≤ ‖y‖ ^ k' * (((∏ i, ‖v i‖) * f.seminorm ℝ (k' + a) (b + l')) / ‖y‖ ^ k') :=
          mul_le_mul_of_nonneg_left h_sem (le_of_lt hy_pos)
      _ = (∏ i, ‖v i‖) * f.seminorm ℝ (k' + a) (b + l') :=
          mul_div_cancel₀ _ (ne_of_gt hy_pos)

end GaussianField
