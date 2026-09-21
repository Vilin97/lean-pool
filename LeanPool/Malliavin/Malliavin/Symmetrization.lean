/-
Copyright (c) 2026 The lean-malliavin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-malliavin contributors
-/
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.Recall

/-!
# Rung 1 (`symm`): the symmetrization operator

For a function `f : (Fin n → T) → E` of `n` variables, its *symmetrization* is

  `symmetrize n f t = (n!)⁻¹ • ∑ σ : Equiv.Perm (Fin n), f (t ∘ σ)`.

This is the operator `f ↦ f̃` of Nualart, *The Malliavin Calculus and Related Topics*, §1.1.2:
the multiple Wiener–Itô integral satisfies `Iₙ(f) = Iₙ(f̃)` and `E[Iₙ(f)²] = n! ‖f̃‖²`, so
symmetrization is the first ingredient of the Wiener chaos decomposition.

On the function side the "`n`-fold tensor product" `L²(T)^{⊗n} ≅ L²(Tⁿ)` is the product measure
space `Fin n → T` with `Measure.pi (fun _ ↦ μ)`; the symmetric tensors are the symmetric
functions, and `symmetrize` is the projection onto them.

## Main results

* `Malliavin.symmetrize`, `Malliavin.symmetrizeₗ` — the operator on functions (as a function,
  and as an `ℝ`-linear map).
* `Malliavin.isSymmetric_symmetrize` — `symmetrize n f` is a symmetric function;
  `Malliavin.isSymmetric_of_swap` — symmetry can be checked on transpositions.
* `Malliavin.symmetrize_of_isSymmetric` — symmetric functions are fixed points.
* `Malliavin.symmetrize_symmetrize` — idempotence; `Malliavin.symmetrizeₗ_isProj` — `symmetrizeₗ`
  is a projection onto the submodule `Malliavin.symmetricSubmodule` of symmetric functions.
* `Malliavin.measurePreserving_comp_perm` — permuting coordinates preserves `μ^{⊗n}`.
* `Malliavin.eLpNorm_symmetrize_le` — contraction: `‖f̃‖_p ≤ ‖f‖_p` for `1 ≤ p`.
* `Malliavin.memLp_symmetrize` — `f ∈ Lᵖ(μ^{⊗n}) → f̃ ∈ Lᵖ(μ^{⊗n})`.
* `Malliavin.permL` — the coordinate-permutation isometries of `Lp E p μ^{⊗n}`.
* `Malliavin.symmetrizeL` — the operator as a continuous linear map
  `Lp E p μ^{⊗n} →L[ℝ] Lp E p μ^{⊗n}`, with `‖symmetrizeL‖ ≤ 1` (`norm_symmetrizeL_le`),
  idempotent (`symmetrizeL_comp_symmetrizeL`), with fixed points exactly the a.e.-symmetric
  functions (`symmetrizeL_eq_self_iff`).
-/

open MeasureTheory Finset
open scoped ENNReal

noncomputable section

namespace Malliavin

variable {T : Type*} {E : Type*}

/-- A function of `n` variables is *symmetric* if it is invariant under every permutation of
its arguments. -/
def IsSymmetric (n : ℕ) (f : (Fin n → T) → E) : Prop :=
  ∀ (σ : Equiv.Perm (Fin n)) (t : Fin n → T), f (t ∘ σ) = f t

/-- Symmetry only needs to be checked on transpositions (they generate `Equiv.Perm (Fin n)`). -/
theorem isSymmetric_of_swap {n : ℕ} {f : (Fin n → T) → E}
    (h : ∀ x y : Fin n, x ≠ y → ∀ t : Fin n → T, f (t ∘ Equiv.swap x y) = f t) :
    IsSymmetric n f := by
  intro σ
  induction σ using Equiv.Perm.swap_induction_on with
  | one => intro t; rfl
  | swap_mul τ x y hxy ih =>
    intro t
    calc f (t ∘ ⇑(Equiv.swap x y * τ)) = f ((t ∘ Equiv.swap x y) ∘ τ) := rfl
      _ = f (t ∘ Equiv.swap x y) := ih _
      _ = f t := h x y hxy t

theorem isSymmetric_iff_swap {n : ℕ} {f : (Fin n → T) → E} :
    IsSymmetric n f ↔ ∀ x y : Fin n, x ≠ y → ∀ t : Fin n → T, f (t ∘ Equiv.swap x y) = f t :=
  ⟨fun hf _ _ _ t => hf _ t, isSymmetric_of_swap⟩

/-! ### The algebraic part: `symmetrize` is a linear projection onto symmetric functions -/

section Algebra

variable [AddCommGroup E] [Module ℝ E]

/-- The symmetrization of a function of `n` variables:
`symmetrize n f t = (n!)⁻¹ • ∑ σ, f (t ∘ σ)`. -/
def symmetrize (n : ℕ) (f : (Fin n → T) → E) : (Fin n → T) → E :=
  fun t => ((n.factorial : ℝ)⁻¹) • ∑ σ : Equiv.Perm (Fin n), f (t ∘ σ)

theorem symmetrize_apply (n : ℕ) (f : (Fin n → T) → E) (t : Fin n → T) :
    symmetrize n f t = ((n.factorial : ℝ)⁻¹) • ∑ σ : Equiv.Perm (Fin n), f (t ∘ σ) :=
  rfl

/-- `symmetrize n f` as a scalar multiple of a sum of coordinate-permuted copies of `f`
(the form used for the `Lᵖ` estimates). -/
theorem symmetrize_eq_smul_sum (n : ℕ) (f : (Fin n → T) → E) :
    symmetrize n f =
      ((n.factorial : ℝ)⁻¹) • ∑ σ : Equiv.Perm (Fin n), f ∘ (fun t : Fin n → T => t ∘ σ) := by
  ext t
  simp only [symmetrize_apply, Pi.smul_apply, Finset.sum_apply, Function.comp_apply]

theorem symmetrize_add (n : ℕ) (f g : (Fin n → T) → E) :
    symmetrize n (f + g) = symmetrize n f + symmetrize n g := by
  ext t
  simp only [symmetrize_apply, Pi.add_apply, sum_add_distrib, smul_add]

theorem symmetrize_smul (n : ℕ) (c : ℝ) (f : (Fin n → T) → E) :
    symmetrize n (c • f) = c • symmetrize n f := by
  ext t
  simp only [symmetrize_apply, Pi.smul_apply, smul_sum, smul_comm c]

@[simp]
theorem symmetrize_zero (n : ℕ) : symmetrize n (0 : (Fin n → T) → E) = 0 := by
  ext t
  simp only [symmetrize_apply, Pi.zero_apply, sum_const_zero, smul_zero]

/-- `symmetrize` as an `ℝ`-linear map on functions of `n` variables. -/
def symmetrizeₗ (n : ℕ) : ((Fin n → T) → E) →ₗ[ℝ] ((Fin n → T) → E) where
  toFun := symmetrize n
  map_add' := symmetrize_add n
  map_smul' := symmetrize_smul n

@[simp]
theorem symmetrizeₗ_apply (n : ℕ) (f : (Fin n → T) → E) : symmetrizeₗ n f = symmetrize n f :=
  rfl

recall Fintype.card_perm {α : Type*} [DecidableEq α] [Fintype α] :
    Fintype.card (Equiv.Perm α) = (Fintype.card α).factorial

/-- Precomposition with a permutation leaves `symmetrize n f` unchanged: reindex the sum over
`Equiv.Perm (Fin n)` by the bijection `σ ↦ τ * σ`. -/
theorem symmetrize_comp_perm (n : ℕ) (f : (Fin n → T) → E) (τ : Equiv.Perm (Fin n))
    (t : Fin n → T) : symmetrize n f (t ∘ τ) = symmetrize n f t := by
  simp only [symmetrize_apply]
  congr 1
  exact Equiv.sum_comp (Equiv.mulLeft τ) (fun σ : Equiv.Perm (Fin n) => f (t ∘ σ))

theorem isSymmetric_symmetrize (n : ℕ) (f : (Fin n → T) → E) : IsSymmetric n (symmetrize n f) :=
  fun τ t => symmetrize_comp_perm n f τ t

/-- Pointwise version of `symmetrize_of_isSymmetric`: at a point `t` where all permuted values
agree, the average is just `f t`. -/
theorem symmetrize_apply_of_forall {n : ℕ} {f : (Fin n → T) → E} {t : Fin n → T}
    (h : ∀ σ : Equiv.Perm (Fin n), f (t ∘ σ) = f t) : symmetrize n f t = f t := by
  rw [symmetrize_apply, Finset.sum_congr rfl (fun σ _ => h σ), Finset.sum_const, Finset.card_univ,
    Fintype.card_perm, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
    inv_mul_cancel₀ (by exact_mod_cast n.factorial_ne_zero), one_smul]

theorem symmetrize_of_isSymmetric {n : ℕ} {f : (Fin n → T) → E} (hf : IsSymmetric n f) :
    symmetrize n f = f :=
  funext fun t => symmetrize_apply_of_forall fun σ => hf σ t

/-- Symmetrization is idempotent. -/
theorem symmetrize_symmetrize (n : ℕ) (f : (Fin n → T) → E) :
    symmetrize n (symmetrize n f) = symmetrize n f :=
  symmetrize_of_isSymmetric (isSymmetric_symmetrize n f)

theorem isSymmetric_iff_symmetrize_eq {n : ℕ} {f : (Fin n → T) → E} :
    IsSymmetric n f ↔ symmetrize n f = f :=
  ⟨symmetrize_of_isSymmetric, fun h => h ▸ isSymmetric_symmetrize n f⟩

theorem symmetrizeₗ_comp_symmetrizeₗ (n : ℕ) :
    (symmetrizeₗ n : ((Fin n → T) → E) →ₗ[ℝ] ((Fin n → T) → E)).comp (symmetrizeₗ n) =
      symmetrizeₗ n :=
  LinearMap.ext fun f => symmetrize_symmetrize n f

/-- The submodule of symmetric functions of `n` variables. -/
def symmetricSubmodule (T : Type*) (E : Type*) [AddCommGroup E] [Module ℝ E] (n : ℕ) :
    Submodule ℝ ((Fin n → T) → E) where
  carrier := {f | IsSymmetric n f}
  zero_mem' := fun _ _ => rfl
  add_mem' := fun hf hg σ t => by simp only [Pi.add_apply, hf σ t, hg σ t]
  smul_mem' := fun c _ hf σ t => by simp only [Pi.smul_apply, hf σ t]

@[simp]
theorem mem_symmetricSubmodule {n : ℕ} {f : (Fin n → T) → E} :
    f ∈ symmetricSubmodule T E n ↔ IsSymmetric n f :=
  Iff.rfl

/-- `symmetrizeₗ` is a linear projection onto the symmetric functions. -/
theorem symmetrizeₗ_isProj (n : ℕ) :
    LinearMap.IsProj (symmetricSubmodule T E n) (symmetrizeₗ n) where
  map_mem f := isSymmetric_symmetrize n f
  map_id _ hf := symmetrize_of_isSymmetric hf

end Algebra

/-! ### The measure-theoretic part: `symmetrize` is an `Lᵖ`-contraction -/

section Measure

variable [MeasurableSpace T] (μ : Measure T) [SigmaFinite μ]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Permuting the coordinates of `Fin n → T` preserves the product measure `μ^{⊗n}`. -/
theorem measurePreserving_comp_perm (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    MeasurePreserving (fun t : Fin n → T => t ∘ σ)
      (Measure.pi fun _ : Fin n => μ) (Measure.pi fun _ : Fin n => μ) :=
  measurePreserving_arrowCongr' (fun _ : Fin n => μ) (fun _ : Fin n => μ) σ.symm
    (MeasurableEquiv.refl T) (fun _ => MeasurePreserving.id μ)

variable {μ}

omit [NormedSpace ℝ E] in
theorem aestronglyMeasurable_comp_perm {n : ℕ} {f : (Fin n → T) → E}
    (hf : AEStronglyMeasurable f (Measure.pi fun _ : Fin n => μ)) (σ : Equiv.Perm (Fin n)) :
    AEStronglyMeasurable (f ∘ fun t : Fin n → T => t ∘ σ) (Measure.pi fun _ : Fin n => μ) :=
  hf.comp_quasiMeasurePreserving (measurePreserving_comp_perm μ n σ).quasiMeasurePreserving

theorem aestronglyMeasurable_symmetrize {n : ℕ} {f : (Fin n → T) → E}
    (hf : AEStronglyMeasurable f (Measure.pi fun _ : Fin n => μ)) :
    AEStronglyMeasurable (symmetrize n f) (Measure.pi fun _ : Fin n => μ) := by
  rw [symmetrize_eq_smul_sum]
  refine AEStronglyMeasurable.const_smul ?_ _
  exact Finset.sum_induction _ (fun g => AEStronglyMeasurable g (Measure.pi fun _ : Fin n => μ))
    (fun _ _ hg hg' => hg.add hg') aestronglyMeasurable_const
    fun σ _ => aestronglyMeasurable_comp_perm hf σ

recall MeasureTheory.eLpNorm_comp_measurePreserving {α : Type*} {m0 : MeasurableSpace α}
    {p : ℝ≥0∞} {μ : Measure α} {ε : Type*} [TopologicalSpace ε] [ContinuousENorm ε] {β : Type*}
    {mβ : MeasurableSpace β} {f : α → β} {g : β → ε} {ν : Measure β}
    (hg : AEStronglyMeasurable g ν) (hf : MeasurePreserving f μ ν) :
    eLpNorm (g ∘ f) p μ = eLpNorm g p ν

recall ENNReal.inv_mul_cancel {a : ℝ≥0∞} (h0 : a ≠ 0) (ht : a ≠ ∞) : a⁻¹ * a = 1

/-- Symmetrization is an `Lᵖ`-contraction: `‖f̃‖_p ≤ ‖f‖_p` for `1 ≤ p`. -/
theorem eLpNorm_symmetrize_le {n : ℕ} {f : (Fin n → T) → E}
    (hf : AEStronglyMeasurable f (Measure.pi fun _ : Fin n => μ)) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    eLpNorm (symmetrize n f) p (Measure.pi fun _ : Fin n => μ) ≤
      eLpNorm f p (Measure.pi fun _ : Fin n => μ) := by
  set ν : Measure (Fin n → T) := Measure.pi fun _ : Fin n => μ with hν
  have hfac : (n.factorial : ℝ≥0∞) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  rw [symmetrize_eq_smul_sum, eLpNorm_const_smul]
  calc ‖(n.factorial : ℝ)⁻¹‖ₑ *
        eLpNorm (∑ σ : Equiv.Perm (Fin n), f ∘ fun t : Fin n → T => t ∘ σ) p ν
      ≤ ‖(n.factorial : ℝ)⁻¹‖ₑ *
        ∑ σ : Equiv.Perm (Fin n), eLpNorm (f ∘ fun t : Fin n → T => t ∘ σ) p ν := by
        gcongr
        exact eLpNorm_sum_le (fun σ _ => aestronglyMeasurable_comp_perm hf σ) hp
    _ = ‖(n.factorial : ℝ)⁻¹‖ₑ * ∑ _σ : Equiv.Perm (Fin n), eLpNorm f p ν := by
        congr 1
        exact Finset.sum_congr rfl fun σ _ =>
          eLpNorm_comp_measurePreserving hf (measurePreserving_comp_perm μ n σ)
    _ = ‖(n.factorial : ℝ)⁻¹‖ₑ * ((n.factorial : ℝ≥0∞) * eLpNorm f p ν) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
    _ = eLpNorm f p ν := by
        rw [enorm_inv (by exact_mod_cast n.factorial_ne_zero), Real.enorm_natCast, ← mul_assoc,
          ENNReal.inv_mul_cancel hfac (ENNReal.natCast_ne_top _), one_mul]

theorem memLp_symmetrize {n : ℕ} {f : (Fin n → T) → E} {p : ℝ≥0∞}
    (hf : MemLp f p (Measure.pi fun _ : Fin n => μ)) :
    MemLp (symmetrize n f) p (Measure.pi fun _ : Fin n => μ) := by
  rw [symmetrize_eq_smul_sum]
  exact (memLp_finsetSum' _ fun σ _ =>
    hf.comp_measurePreserving (measurePreserving_comp_perm μ n σ)).const_smul _

/-- Symmetrization respects a.e.-equality (so it descends to `Lp`). -/
theorem symmetrize_congr_ae {n : ℕ} {f g : (Fin n → T) → E}
    (h : f =ᵐ[Measure.pi fun _ : Fin n => μ] g) :
    symmetrize n f =ᵐ[Measure.pi fun _ : Fin n => μ] symmetrize n g := by
  have hσ : ∀ σ : Equiv.Perm (Fin n),
      (f ∘ fun t : Fin n → T => t ∘ σ) =ᵐ[Measure.pi fun _ : Fin n => μ]
        (g ∘ fun t : Fin n → T => t ∘ σ) :=
    fun σ => (measurePreserving_comp_perm μ n σ).quasiMeasurePreserving.ae_eq_comp h
  filter_upwards [Filter.eventually_all.2 hσ] with t ht
  simp only [symmetrize_apply]
  congr 1
  exact Finset.sum_congr rfl fun σ _ => ht σ

/-! ### The operator on `Lp` -/

omit [NormedSpace ℝ E] in
/-- Coercion of a finite sum in `Lp` is a.e. the sum of the coercions. -/
theorem _root_.MeasureTheory.Lp.coeFn_finset_sum {α : Type*} [MeasurableSpace α]
    {ν : Measure α} {p : ℝ≥0∞} {ι : Type*} (s : Finset ι) (g : ι → Lp E p ν) :
    ⇑(∑ i ∈ s, g i) =ᵐ[ν] ∑ i ∈ s, ⇑(g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using Lp.coeFn_zero (E := E) (p := p) (μ := ν)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    filter_upwards [Lp.coeFn_add (g a) (∑ i ∈ s, g i), ih] with t h1 h2
    rw [h1, Pi.add_apply, Pi.add_apply, h2]

variable (E) in
/-- The coordinate-permutation operator `f ↦ f ∘ (· ∘ σ)` on `Lp E p μ^{⊗n}`, as a continuous
linear map (it is in fact an isometry, being `Lp.compMeasurePreservingₗᵢ`). -/
def permL (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (σ : Equiv.Perm (Fin n)) :
    Lp E p (Measure.pi fun _ : Fin n => μ) →L[ℝ] Lp E p (Measure.pi fun _ : Fin n => μ) :=
  (Lp.compMeasurePreservingₗᵢ ℝ (fun t : Fin n → T => t ∘ σ)
    (measurePreserving_comp_perm μ n σ)).toContinuousLinearMap

theorem coeFn_permL (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (σ : Equiv.Perm (Fin n))
    (f : Lp E p (Measure.pi fun _ : Fin n => μ)) :
    ⇑(permL E (μ := μ) n p σ f) =ᵐ[Measure.pi fun _ : Fin n => μ]
      ⇑f ∘ fun t : Fin n → T => t ∘ σ :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_comp_perm μ n σ)

theorem norm_permL_le (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (σ : Equiv.Perm (Fin n)) :
    ‖permL E (μ := μ) n p σ‖ ≤ 1 :=
  LinearIsometry.norm_toContinuousLinearMap_le _

variable (E) in
/-- The symmetrization operator on `Lp E p μ^{⊗n}`, as a continuous linear map: the average of
the (isometric) coordinate-permutation operators `permL`. -/
def symmetrizeL (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Lp E p (Measure.pi fun _ : Fin n => μ) →L[ℝ] Lp E p (Measure.pi fun _ : Fin n => μ) :=
  ((n.factorial : ℝ)⁻¹) • ∑ σ : Equiv.Perm (Fin n), permL E (μ := μ) n p σ

theorem symmetrizeL_apply (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : Lp E p (Measure.pi fun _ : Fin n => μ)) :
    symmetrizeL E (μ := μ) n p f =
      ((n.factorial : ℝ)⁻¹) • ∑ σ : Equiv.Perm (Fin n), permL E (μ := μ) n p σ f := by
  simp only [symmetrizeL, smul_apply, _root_.sum_apply]

/-- `symmetrizeL` is a.e. the pointwise symmetrization of a representative. -/
theorem coeFn_symmetrizeL (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : Lp E p (Measure.pi fun _ : Fin n => μ)) :
    ⇑(symmetrizeL E (μ := μ) n p f) =ᵐ[Measure.pi fun _ : Fin n => μ] symmetrize n ⇑f := by
  rw [symmetrizeL_apply]
  filter_upwards [Lp.coeFn_smul ((n.factorial : ℝ)⁻¹)
      (∑ σ : Equiv.Perm (Fin n), permL E (μ := μ) n p σ f),
    Lp.coeFn_finset_sum Finset.univ (fun σ : Equiv.Perm (Fin n) => permL E (μ := μ) n p σ f),
    Filter.eventually_all.2 (fun σ => coeFn_permL (E := E) (μ := μ) n p σ f)] with t h1t h2t h3t
  rw [h1t, Pi.smul_apply, h2t, Finset.sum_apply, symmetrize_apply]
  congr 1
  exact Finset.sum_congr rfl fun σ _ => h3t σ

/-- The operator norm of symmetrization is at most `1`. -/
theorem norm_symmetrizeL_le (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    ‖symmetrizeL E (μ := μ) n p‖ ≤ 1 := by
  have hsum : ‖∑ σ : Equiv.Perm (Fin n), permL E (μ := μ) n p σ‖ ≤ (n.factorial : ℝ) := by
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun σ _ => norm_permL_le (E := E) (μ := μ) n p σ).trans ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul,
      mul_one]
  calc ‖symmetrizeL E (μ := μ) n p‖
      = ‖(n.factorial : ℝ)⁻¹‖ * ‖∑ σ : Equiv.Perm (Fin n), permL E (μ := μ) n p σ‖ :=
        norm_smul _ _
    _ ≤ ‖(n.factorial : ℝ)⁻¹‖ * (n.factorial : ℝ) := by gcongr
    _ = 1 := by
        rw [norm_inv, Real.norm_natCast, inv_mul_cancel₀ (by exact_mod_cast n.factorial_ne_zero)]

theorem norm_symmetrizeL_apply_le (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : Lp E p (Measure.pi fun _ : Fin n => μ)) :
    ‖symmetrizeL E (μ := μ) n p f‖ ≤ ‖f‖ := by
  have h := (symmetrizeL E (μ := μ) n p).le_of_opNorm_le
    (norm_symmetrizeL_le (E := E) (μ := μ) n p) f
  simpa only [one_mul] using h

/-- `symmetrizeL` is idempotent. -/
theorem symmetrizeL_symmetrizeL (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : Lp E p (Measure.pi fun _ : Fin n => μ)) :
    symmetrizeL E (μ := μ) n p (symmetrizeL E (μ := μ) n p f) = symmetrizeL E (μ := μ) n p f := by
  apply Lp.ext
  have h1 := coeFn_symmetrizeL n p (symmetrizeL E (μ := μ) n p f)
  have h2 := symmetrize_congr_ae (μ := μ) (coeFn_symmetrizeL n p f)
  rw [symmetrize_symmetrize] at h2
  exact h1.trans (h2.trans (coeFn_symmetrizeL n p f).symm)

theorem symmetrizeL_comp_symmetrizeL (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    (symmetrizeL E (μ := μ) n p).comp (symmetrizeL E (μ := μ) n p) = symmetrizeL E (μ := μ) n p :=
  ContinuousLinearMap.ext fun f => symmetrizeL_symmetrizeL n p f

/-- An a.e.-symmetric `Lp` function is fixed by `symmetrizeL`. -/
theorem symmetrizeL_eq_self_of_ae_symmetric (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : Lp E p (Measure.pi fun _ : Fin n => μ))
    (hf : ∀ σ : Equiv.Perm (Fin n),
      (⇑f ∘ fun t : Fin n → T => t ∘ σ) =ᵐ[Measure.pi fun _ : Fin n => μ] ⇑f) :
    symmetrizeL E (μ := μ) n p f = f := by
  apply Lp.ext
  refine (coeFn_symmetrizeL n p f).trans ?_
  filter_upwards [Filter.eventually_all.2 hf] with t ht
  exact symmetrize_apply_of_forall fun σ => ht σ

/-- Conversely, a fixed point of `symmetrizeL` is a.e.-symmetric. -/
theorem ae_symmetric_of_symmetrizeL_eq_self (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : Lp E p (Measure.pi fun _ : Fin n => μ)) (hf : symmetrizeL E (μ := μ) n p f = f)
    (σ : Equiv.Perm (Fin n)) :
    (⇑f ∘ fun t : Fin n → T => t ∘ σ) =ᵐ[Measure.pi fun _ : Fin n => μ] ⇑f := by
  have h1 : ⇑f =ᵐ[Measure.pi fun _ : Fin n => μ] symmetrize n ⇑f := by
    have := coeFn_symmetrizeL (E := E) (μ := μ) n p f
    rwa [hf] at this
  have h2 : (⇑f ∘ fun t : Fin n → T => t ∘ σ) =ᵐ[Measure.pi fun _ : Fin n => μ]
      (symmetrize n ⇑f ∘ fun t : Fin n → T => t ∘ σ) :=
    (measurePreserving_comp_perm μ n σ).quasiMeasurePreserving.ae_eq_comp h1
  have h3 : (symmetrize n ⇑f ∘ fun t : Fin n → T => t ∘ σ) = symmetrize n ⇑f :=
    funext fun t => symmetrize_comp_perm n ⇑f σ t
  rw [h3] at h2
  exact h2.trans h1.symm

/-- The fixed points of `symmetrizeL` are exactly the a.e.-symmetric functions. -/
theorem symmetrizeL_eq_self_iff (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : Lp E p (Measure.pi fun _ : Fin n => μ)) :
    symmetrizeL E (μ := μ) n p f = f ↔ ∀ σ : Equiv.Perm (Fin n),
      (⇑f ∘ fun t : Fin n → T => t ∘ σ) =ᵐ[Measure.pi fun _ : Fin n => μ] ⇑f :=
  ⟨ae_symmetric_of_symmetrizeL_eq_self n p f, symmetrizeL_eq_self_of_ae_symmetric n p f⟩

end Measure

/-! ### `symmetrizeL` is self-adjoint on `L²`, hence an orthogonal projection -/

section InnerProduct

variable [MeasurableSpace T] {μ : Measure T} [SigmaFinite μ]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem inner_permL_left (n : ℕ) (σ : Equiv.Perm (Fin n))
    (f g : Lp E 2 (Measure.pi fun _ : Fin n => μ)) :
    inner ℝ (permL E (μ := μ) n 2 σ f) g = inner ℝ f (permL E (μ := μ) n 2 σ⁻¹ g) := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  have hemb : MeasurableEmbedding (fun t : Fin n → T => t ∘ ⇑(σ⁻¹)) :=
    (MeasurableEquiv.arrowCongr' (σ⁻¹).symm (MeasurableEquiv.refl T)).measurableEmbedding
  have hcov := (measurePreserving_comp_perm μ n σ⁻¹).integral_comp hemb
    (fun t : Fin n → T => inner ℝ (f (t ∘ σ)) (g t))
  calc ∫ t, inner ℝ ((permL E (μ := μ) n 2 σ f) t) (g t) ∂(Measure.pi fun _ : Fin n => μ)
      = ∫ t, inner ℝ (f (t ∘ σ)) (g t) ∂(Measure.pi fun _ : Fin n => μ) := by
        refine integral_congr_ae ?_
        filter_upwards [coeFn_permL (E := E) (μ := μ) n 2 σ f] with t ht
        rw [ht]
        rfl
    _ = ∫ u, inner ℝ (f ((u ∘ ⇑(σ⁻¹)) ∘ σ)) (g (u ∘ ⇑(σ⁻¹)))
          ∂(Measure.pi fun _ : Fin n => μ) := hcov.symm
    _ = ∫ u, inner ℝ (f u) ((permL E (μ := μ) n 2 σ⁻¹ g) u) ∂(Measure.pi fun _ : Fin n => μ) := by
        refine integral_congr_ae ?_
        filter_upwards [coeFn_permL (E := E) (μ := μ) n 2 σ⁻¹ g] with u hu
        have hu' : (u ∘ ⇑(σ⁻¹)) ∘ ⇑σ = u := by
          ext i
          simp only [Function.comp_apply, Equiv.Perm.coe_inv, Equiv.symm_apply_apply]
        rw [hu, hu']
        rfl

/-- `symmetrizeL` is self-adjoint on `L²`: together with idempotence this makes it the orthogonal
projection onto the a.e.-symmetric functions. -/
theorem inner_symmetrizeL_left (n : ℕ) (f g : Lp E 2 (Measure.pi fun _ : Fin n => μ)) :
    inner ℝ (symmetrizeL E (μ := μ) n 2 f) g = inner ℝ f (symmetrizeL E (μ := μ) n 2 g) := by
  simp only [symmetrizeL_apply, real_inner_smul_left, real_inner_smul_right, sum_inner, inner_sum]
  congr 1
  rw [← Equiv.sum_comp (Equiv.inv (Equiv.Perm (Fin n)))
    (fun σ => inner ℝ f (permL E (μ := μ) n 2 σ g))]
  exact Finset.sum_congr rfl fun σ _ => inner_permL_left n σ f g

/-- `f - symmetrizeL f` is orthogonal to `symmetrizeL f`. -/
theorem inner_symmetrizeL_sub_symmetrizeL (n : ℕ) (f : Lp E 2 (Measure.pi fun _ : Fin n => μ)) :
    inner ℝ (symmetrizeL E (μ := μ) n 2 f) (f - symmetrizeL E (μ := μ) n 2 f) = 0 := by
  rw [inner_sub_right, inner_symmetrizeL_left n f (symmetrizeL E (μ := μ) n 2 f),
    symmetrizeL_symmetrizeL, inner_symmetrizeL_left, sub_self]

/-- Orthogonal decomposition: `‖f‖² = ‖f̃‖² + ‖f - f̃‖²` on `L²`. -/
theorem norm_sq_eq_norm_sq_symmetrizeL_add (n : ℕ)
    (f : Lp E 2 (Measure.pi fun _ : Fin n => μ)) :
    ‖f‖ ^ 2 = ‖symmetrizeL E (μ := μ) n 2 f‖ ^ 2 + ‖f - symmetrizeL E (μ := μ) n 2 f‖ ^ 2 := by
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (symmetrizeL E (μ := μ) n 2 f)
    (f - symmetrizeL E (μ := μ) n 2 f) (inner_symmetrizeL_sub_symmetrizeL n f)
  rw [add_sub_cancel] at h
  simpa only [sq] using h

end InnerProduct

end Malliavin

end

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
