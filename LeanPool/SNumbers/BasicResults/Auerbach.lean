/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Instances.Matrix

/-!
# Auerbach's Lemma

Every `n`-dimensional normed space over `ℝ` admits a basis `{eᵢ}` with `‖eᵢ‖ = 1`
whose dual coordinate functionals also satisfy `‖eⁱ‖ = 1`.

The proof maximizes `|det|` on the product of unit balls, then reads off the basis
and dual functionals from the maximizer.
-/

@[expose] public section

noncomputable section

open Module FiniteDimensional Metric

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- An **Auerbach basis**: all basis vectors and dual coordinate functionals have norm 1. -/
structure IsAuerbachBasis (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {ι : Type*} [Fintype ι] (b : Basis ι ℝ V) : Prop where
  norm_basis : ∀ i, ‖b i‖ = 1
  norm_coord : ∀ i, ‖(b.coord i).toContinuousLinearMap‖ = 1

-- ============================================================================
-- § 1. Continuity and compactness
-- ============================================================================

private theorem basis_det_continuous {n : ℕ} (b₀ : Basis (Fin n) ℝ V) :
    Continuous (b₀.det : (Fin n → V) → ℝ) := by
  have : (b₀.det : (Fin n → V) → ℝ) = fun v => Matrix.det (b₀.toMatrix v) :=
    funext b₀.det_apply
  rw [this]
  exact (continuous_matrix fun i j =>
    ((Finsupp.lapply i |>.comp b₀.repr.toLinearMap).continuous_of_finiteDimensional).comp
      (continuous_apply j)).matrix_det

-- ============================================================================
-- § 2. Existence and positivity of the maximum of |det|
-- ============================================================================

private theorem exists_max_abs_det {n : ℕ} (b₀ : Basis (Fin n) ℝ V) :
    ∃ e ∈ Set.pi Set.univ (fun _ : Fin n => closedBall (0 : V) 1),
      ∀ w ∈ Set.pi Set.univ (fun _ : Fin n => closedBall (0 : V) 1),
        |b₀.det w| ≤ |b₀.det e| := by
  obtain ⟨e, he, hmax⟩ := (isCompact_univ_pi fun _ => isCompact_closedBall 0 1).exists_isMaxOn
    ⟨0, by simp⟩ (continuous_abs.comp (basis_det_continuous b₀)).continuousOn
  exact ⟨e, he, isMaxOn_iff.mp hmax⟩

omit [FiniteDimensional ℝ V] in
private theorem det_normalized_pos {n : ℕ} (b₀ : Basis (Fin n) ℝ V) :
    0 < |b₀.det (fun i => ‖b₀ i‖⁻¹ • b₀ i)| := by
  have hpos : ∀ i : Fin n, 0 < ‖b₀ i‖ := fun i => norm_pos_iff.mpr (b₀.ne_zero i)
  have hprod : 0 < ∏ i : Fin n, ‖b₀ i‖⁻¹ :=
    Finset.prod_pos fun i _ => inv_pos.mpr (hpos i)
  have h : b₀.det (fun i => ‖b₀ i‖⁻¹ • b₀ i) = (∏ i : Fin n, ‖b₀ i‖⁻¹) * 1 := by
    have := b₀.det.toMultilinearMap.map_smul_univ (fun i => ‖b₀ i‖⁻¹) b₀
    simp only [smul_eq_mul, AlternatingMap.coe_multilinearMap, b₀.det_self] at this
    exact this
  rw [h, mul_one, abs_of_pos hprod]; exact hprod

omit [FiniteDimensional ℝ V] in
private theorem normalized_mem {n : ℕ} (b₀ : Basis (Fin n) ℝ V) :
    (fun i => ‖b₀ i‖⁻¹ • b₀ i) ∈
      Set.pi Set.univ (fun _ : Fin n => closedBall (0 : V) 1) := by
  simp only [Set.mem_pi, Set.mem_univ, mem_closedBall, dist_zero_right, true_implies]
  intro i
  by_cases h : b₀ i = 0
  · simp [h]
  · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr h)]

private theorem exists_max_pos {n : ℕ} (b₀ : Basis (Fin n) ℝ V) :
    ∃ e ∈ Set.pi Set.univ (fun _ : Fin n => closedBall (0 : V) 1),
      0 < |b₀.det e| ∧
      ∀ w ∈ Set.pi Set.univ (fun _ : Fin n => closedBall (0 : V) 1),
        |b₀.det w| ≤ |b₀.det e| := by
  obtain ⟨e, he_mem, he_max⟩ := exists_max_abs_det b₀
  exact ⟨e, he_mem,
    lt_of_lt_of_le (det_normalized_pos b₀) (he_max _ (normalized_mem b₀)), he_max⟩

-- ============================================================================
-- § 3. The maximizer has unit-norm entries
-- ============================================================================

omit [FiniteDimensional ℝ V] in
private theorem norm_maximizer_eq_one {n : ℕ} (b₀ : Basis (Fin n) ℝ V)
    (e : Fin n → V)
    (he_mem : e ∈ Set.pi Set.univ (fun _ : Fin n => closedBall (0 : V) 1))
    (he_pos : 0 < |b₀.det e|)
    (he_max : ∀ w ∈ Set.pi Set.univ (fun _ : Fin n => closedBall (0 : V) 1),
        |b₀.det w| ≤ |b₀.det e|)
    (i : Fin n) : ‖e i‖ = 1 := by
  have hi_le : ‖e i‖ ≤ 1 := by
    simpa [Set.mem_pi, mem_closedBall, dist_zero_right] using he_mem i trivial
  have hei_ne : e i ≠ 0 := by
    intro h; simp [AlternatingMap.map_coord_zero b₀.det i h] at he_pos
  have hei_pos : 0 < ‖e i‖ := norm_pos_iff.mpr hei_ne
  by_contra h_ne
  have hi_lt : ‖e i‖ < 1 := lt_of_le_of_ne hi_le h_ne
  set w := Function.update e i (‖e i‖⁻¹ • e i)
  have hw_mem : w ∈ Set.pi Set.univ (fun _ : Fin n => closedBall (0 : V) 1) := by
    simp only [Set.mem_pi, Set.mem_univ, mem_closedBall, dist_zero_right, true_implies,
               w, Function.update_apply]
    intro j; split_ifs with h
    · subst h; rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (ne_of_gt hei_pos)]
    · simpa [Set.mem_pi, mem_closedBall, dist_zero_right] using he_mem j trivial
  have hw_det : b₀.det w = ‖e i‖⁻¹ • b₀.det e := by
    have := b₀.det.toMultilinearMap.map_update_smul' e i ‖e i‖⁻¹ (e i)
    simp only [Function.update_eq_self] at this; exact this
  have : |b₀.det e| < |b₀.det w| := by
    rw [hw_det, smul_eq_mul, abs_mul, abs_of_pos (inv_pos.mpr hei_pos)]
    exact lt_mul_of_one_lt_left he_pos ((one_lt_inv₀ hei_pos).mpr hi_lt)
  linarith [he_max w hw_mem]

-- ============================================================================
-- § 4. The dual coordinate functionals
-- ============================================================================

/-- The `i`-th coordinate functional: `v ↦ det(e₁,…,v,…,eₙ) / det(e)`.

Linearity is Mathlib's: fixing all but the `i`-th argument of the multilinear
`b₀.det` gives a linear map (`MultilinearMap.toLinearMap`), which is then scaled
by `(det e)⁻¹` and continuous because `V` is finite-dimensional. -/
noncomputable def coordFunOfDet {n : ℕ} (b₀ : Basis (Fin n) ℝ V)
    (e : Fin n → V) (_h_det : b₀.det e ≠ 0) (i : Fin n) : V →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ((b₀.det e)⁻¹ • b₀.det.toMultilinearMap.toLinearMap e i)

/-- The defining value of `coordFunOfDet`, in the `div` form of the definition. -/
theorem coordFunOfDet_apply_eq {n : ℕ} (b₀ : Basis (Fin n) ℝ V)
    (e : Fin n → V) (h_det : b₀.det e ≠ 0) (i : Fin n) (v : V) :
    coordFunOfDet b₀ e h_det i v = b₀.det (Function.update e i v) / b₀.det e := by
  simp [coordFunOfDet, div_eq_inv_mul]

theorem coordFunOfDet_apply {n : ℕ} (b₀ : Basis (Fin n) ℝ V)
    (e : Fin n → V) (h_det : b₀.det e ≠ 0) (i j : Fin n) :
    coordFunOfDet b₀ e h_det i (e j) = if i = j then 1 else 0 := by
  rw [coordFunOfDet_apply_eq]
  split_ifs with h
  · subst h; rw [Function.update_eq_self, div_self h_det]
  · rw [div_eq_zero_iff]; left
    exact b₀.det.map_eq_zero_of_eq _
      (by rw [Function.update_self, Function.update_of_ne (Ne.symm h)]) h

-- ============================================================================
-- § 5. Norm bounds for the coordinate functionals
-- ============================================================================

private theorem norm_coordFunOfDet_le_one {n : ℕ} (b₀ : Basis (Fin n) ℝ V)
    (e : Fin n → V) (h_det : b₀.det e ≠ 0)
    (he_max : ∀ w ∈ Set.pi Set.univ (fun _ : Fin n => closedBall (0 : V) 1),
        |b₀.det w| ≤ |b₀.det e|)
    (he_norm : ∀ k, ‖e k‖ = 1) (i : Fin n) :
    ‖coordFunOfDet b₀ e h_det i‖ ≤ 1 := by
  have hbound : ∀ v : V, ‖coordFunOfDet b₀ e h_det i v‖ ≤ 1 * ‖v‖ := by
    intro v; rw [one_mul]
    rw [coordFunOfDet_apply_eq, Real.norm_eq_abs, abs_div]
    rcases eq_or_ne v 0 with rfl | hv
    · simp
    · rw [div_le_iff₀ (abs_pos.mpr h_det)]
      have hv_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv
      have hresc : b₀.det (Function.update e i v) =
          ‖v‖ * b₀.det (Function.update e i (‖v‖⁻¹ • v)) := by
        have hscale : b₀.det (Function.update e i (‖v‖ • ‖v‖⁻¹ • v)) =
            ‖v‖ * b₀.det (Function.update e i (‖v‖⁻¹ • v)) := by
          have := b₀.det.toMultilinearMap.map_update_smul' e i ‖v‖ (‖v‖⁻¹ • v)
          rwa [smul_eq_mul] at this
        conv_lhs => rw [show v = ‖v‖ • ‖v‖⁻¹ • v by
          rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hv_pos), one_smul]]
        exact hscale
      rw [hresc, abs_mul, abs_norm]
      apply mul_le_mul_of_nonneg_left _ (le_of_lt hv_pos)
      apply he_max
      simp only [Set.mem_pi, Set.mem_univ, mem_closedBall, dist_zero_right, true_implies,
                 Function.update_apply]
      intro k; split_ifs with h
      · subst h; rw [norm_smul, norm_inv, norm_norm]
        exact le_of_eq (inv_mul_cancel₀ (ne_of_gt hv_pos))
      · exact le_of_eq (he_norm k)
  exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one hbound

private theorem one_le_norm_coordFunOfDet {n : ℕ} (b₀ : Basis (Fin n) ℝ V)
    (e : Fin n → V) (h_det : b₀.det e ≠ 0)
    (he_norm : ∀ k, ‖e k‖ = 1) (i : Fin n) :
    1 ≤ ‖coordFunOfDet b₀ e h_det i‖ := by
  calc 1 = ‖coordFunOfDet b₀ e h_det i (e i)‖ := by
        simp [coordFunOfDet_apply]
    _ ≤ ‖coordFunOfDet b₀ e h_det i‖ * ‖e i‖ :=
        (coordFunOfDet b₀ e h_det i).le_opNorm (e i)
    _ = ‖coordFunOfDet b₀ e h_det i‖ := by rw [he_norm i, mul_one]

-- ============================================================================
-- § 6. Linear independence and basis construction
-- ============================================================================

omit [FiniteDimensional ℝ V] in
/-- If `b₀.det e ≠ 0`, the vectors `e` form a basis of `V`: they are linearly
    independent and span the whole space.  This packages Mathlib's
    `Basis.is_basis_iff_det`, using that over the field `ℝ` a determinant is a
    unit iff it is nonzero (`isUnit_iff_ne_zero`). -/
private theorem isBasis_of_det_ne_zero {n : ℕ} (b₀ : Basis (Fin n) ℝ V)
    (e : Fin n → V) (h_det : b₀.det e ≠ 0) :
    LinearIndependent ℝ e ∧ Submodule.span ℝ (Set.range e) = ⊤ :=
  (b₀.is_basis_iff_det).mpr (isUnit_iff_ne_zero.mpr h_det)

omit [FiniteDimensional ℝ V] in
/-- If `b₀.det e ≠ 0`, the vectors `e` are linearly independent. -/
private theorem linearIndependent_of_det_ne_zero {n : ℕ} (b₀ : Basis (Fin n) ℝ V)
    (e : Fin n → V) (h_det : b₀.det e ≠ 0) : LinearIndependent ℝ e :=
  (isBasis_of_det_ne_zero b₀ e h_det).1

/-- The basis of `V` obtained from a family `e` with nonzero determinant.
    Built directly from independence and spanning via `Basis.mk`, so it needs
    neither a dimension hypothesis nor nonemptiness of the index type. -/
private def basisOfMaximizer {n : ℕ} (b₀ : Basis (Fin n) ℝ V)
    (e : Fin n → V) (h_det : b₀.det e ≠ 0) : Basis (Fin n) ℝ V :=
  Basis.mk (isBasis_of_det_ne_zero b₀ e h_det).1
    (isBasis_of_det_ne_zero b₀ e h_det).2.ge

omit [FiniteDimensional ℝ V] in
@[simp] private theorem basisOfMaximizer_apply {n : ℕ} (b₀ : Basis (Fin n) ℝ V)
    (e : Fin n → V) (h_det : b₀.det e ≠ 0) (i : Fin n) :
    basisOfMaximizer b₀ e h_det i = e i := by
  simp only [basisOfMaximizer, Basis.mk_apply]

private theorem basisOfMaximizer_coord_eq {n : ℕ} (b₀ : Basis (Fin n) ℝ V)
    (e : Fin n → V) (h_det : b₀.det e ≠ 0) (i : Fin n) :
    ((basisOfMaximizer b₀ e h_det).coord i).toContinuousLinearMap =
      coordFunOfDet b₀ e h_det i := by
  set b := basisOfMaximizer b₀ e h_det
  apply ContinuousLinearMap.ext; intro v
  conv_lhs => rw [← b.sum_repr v]
  conv_rhs => rw [← b.sum_repr v]
  simp only [map_sum, map_smul, smul_eq_mul]
  congr 1; ext j; congr 1
  have lhs : (b.coord i).toContinuousLinearMap (b j) = if i = j then 1 else 0 := by
    change b.coord i (b j) = _
    rw [Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]
    exact if_congr eq_comm rfl rfl
  rw [lhs, basisOfMaximizer_apply, coordFunOfDet_apply]

-- ============================================================================
-- § 7. Main theorem
-- ============================================================================

/-- **Auerbach's Lemma.** Every finite-dimensional normed space over `ℝ`
    admits an Auerbach basis.  (For the zero space this is the empty basis, for
    which the norm conditions hold vacuously.) -/
theorem exists_isAuerbachBasis
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] :
    ∃ b : Basis (Fin (finrank ℝ V)) ℝ V, IsAuerbachBasis V b := by
  set b₀ := Module.finBasis ℝ V
  obtain ⟨e, he_mem, he_pos, he_max⟩ := exists_max_pos b₀
  have he_norm := fun i => norm_maximizer_eq_one b₀ e he_mem he_pos he_max i
  have h_det : b₀.det e ≠ 0 := abs_pos.mp he_pos
  set b := basisOfMaximizer b₀ e h_det
  exact ⟨b, {
    norm_basis := fun i => by rw [basisOfMaximizer_apply]; exact he_norm i
    norm_coord := fun i => by
      rw [basisOfMaximizer_coord_eq]
      exact le_antisymm
        (norm_coordFunOfDet_le_one b₀ e h_det he_max he_norm i)
        (one_le_norm_coordFunOfDet b₀ e h_det he_norm i) }⟩

end

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
