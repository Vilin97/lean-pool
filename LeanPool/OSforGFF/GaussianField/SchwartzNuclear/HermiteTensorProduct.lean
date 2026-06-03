/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/

import LeanPool.OSforGFF.GaussianField.SchwartzNuclear.Basis1D
import LeanPool.OSforGFF.GaussianField.Nuclear.NuclearTensorProduct
import LeanPool.OSforGFF.GaussianField.SchwartzNuclear.SchwartzSlicing
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Nuclear Space Instance for Schwartz Space via Sequence Space Isomorphism

Proves `DyninMityaginSpace (SchwartzMap D ℝ)` for any finite-dimensional `D`.
**0 sorrys, 0 axioms.** <!-- count_axioms:skip -->

## Strategy

The Schwartz space `S(D, ℝ)` is topologically isomorphic to the space `s(ℕ)`
of rapidly decreasing sequences (Dynin-Mityagin). The isomorphism is:
- For D = ℝ: the Hermite expansion (proved in `SchwartzNuclear.Basis1D`)
- For general D = ℝ^d: multi-index Hermite expansion using tensorized 1D
  Hermite functions indexed by `Fin d → ℕ`, flattened via a polynomially-bounded
  bijection `ℕ^d → ℕ`.

The `DyninMityaginSpace` instance is derived from this isomorphism by transferring
the basis, coefficients, expansion, growth, and decay properties through
the continuous linear equivalence.

## References

- Dynin, Mityagin, "Criterion for nuclearity in terms of approximative dimension"
- Gel'fand-Vilenkin, "Generalized Functions" Vol. 4, Ch. 3-4
- Thangavelu, "Lectures on Hermite and Laguerre Expansions", Ch. 1
-/

noncomputable section

open GaussianField MeasureTheory Real SchwartzMap
open scoped ContDiff

namespace GaussianField

/-! ## The Sequence Space Isomorphism

The key mathematical fact: Schwartz space on any finite-dimensional real
normed space is topologically linearly isomorphic to the space of rapidly
decreasing sequences `s(ℕ)`.

For D = ℝ, this is the Hermite expansion:
  f ↦ (∫ f(x)ψₙ(x)dx)ₙ
where ψₙ are the Hermite functions. This is proved in `SchwartzNuclear.Basis1D`.

For D = ℝ^d with d > 1, the proof uses multi-index Hermite expansion:
  f ↦ (∫ f(x) · ∏ᵢ ψ_{αᵢ}(xᵢ) dx)_α
flattened via a polynomially-bounded bijection `ℕ^d → ℕ`.
-/

/-! ## Domain Transfer

`schwartzDomCongr` transfers Schwartz maps along a continuous linear equivalence
of domains. This is the key ingredient for reducing `SchwartzMap D ℝ` to
`SchwartzMap (EuclideanSpace ℝ (Fin d)) ℝ` and then to `SchwartzMap ℝ ℝ`.
-/

/-- Composition with a continuous linear equivalence gives a topological isomorphism
of Schwartz spaces. Forward: `f ↦ f ∘ g`, backward: `f ↦ f ∘ g⁻¹`.
-/
noncomputable def schwartzDomCongr {D E F : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : D ≃L[ℝ] E) :
    SchwartzMap E F ≃L[ℝ] SchwartzMap D F :=
  ContinuousLinearEquiv.equivOfInverse
    (compCLMOfContinuousLinearEquiv ℝ g)
    (compCLMOfContinuousLinearEquiv ℝ g.symm)
    (fun f => SchwartzMap.ext fun x => by
      simp only [compCLMOfContinuousLinearEquiv_apply, Function.comp_def]
      exact congr_arg f (g.apply_symm_apply x))
    (fun f => SchwartzMap.ext fun x => by
      simp only [compCLMOfContinuousLinearEquiv_apply, Function.comp_def]
      exact congr_arg f (g.symm_apply_apply x))

/-- `EuclideanSpace ℝ (Fin 1)` is continuously linearly equivalent to `ℝ`. -/
noncomputable def euclideanFin1Equiv : EuclideanSpace ℝ (Fin 1) ≃L[ℝ] ℝ :=
  (EuclideanSpace.equiv (Fin 1) ℝ).trans (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ)

/-- Measurable equivalence `EuclideanSpace ℝ (Fin 1) ≃ᵐ ℝ`, composing the `WithLp`
unwrapping with the `Fin 1 → ℝ ≃ᵐ ℝ` unique-function equivalence.
-/
noncomputable def euclideanFin1MeasEquiv : EuclideanSpace ℝ (Fin 1) ≃ᵐ ℝ :=
  (MeasurableEquiv.toLp 2 (Fin 1 → ℝ)).symm.trans (MeasurableEquiv.funUnique (Fin 1) ℝ)

/-- `euclideanFin1MeasEquiv` preserves the volume measure. -/
lemma euclideanFin1MeasEquiv_mp :
    MeasureTheory.MeasurePreserving euclideanFin1MeasEquiv volume volume :=
  (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 1)).trans
    (MeasureTheory.volume_preserving_funUnique (Fin 1) ℝ)

/-- `euclideanFin1MeasEquiv x` extracts the unique coordinate. -/
lemma euclideanFin1MeasEquiv_apply (x : EuclideanSpace ℝ (Fin 1)) :
    euclideanFin1MeasEquiv x = x 0 := by
  simp [euclideanFin1MeasEquiv, MeasurableEquiv.funUnique, MeasurableEquiv.toLp, WithLp.equiv]

/-! ## 1D Hermite Isomorphism

The Hermite expansion gives a topological isomorphism `SchwartzMap ℝ ℝ ≃L[ℝ] RapidDecaySeq`.
Forward: `f ↦ (cₙ(f))ₙ` where `cₙ(f) = ∫ f ψₙ`.
Backward: `a ↦ ∑' n, aₙ ψₙ` (tsum in Schwartz topology).
-/

/-- Kronecker property: the Hermite coefficient of a basis function is δₙₘ. -/
theorem hermiteCoeff1D_basis_kronecker (n m : ℕ) :
    hermiteCoeff1D n (schwartzHermiteBasis1D m) = if n = m then 1 else 0 := by
  change ∫ x, schwartzHermiteBasis1D m x * hermiteFunction n x = _
  simp_rw [schwartzHermiteBasis1D_apply]
  convert hermiteFunction_orthonormal m n using 1
  exact ite_congr (propext eq_comm) (fun _ => rfl) (fun _ => rfl)

/-- Hermite coefficients of a Schwartz function form a rapidly decreasing sequence.
From `hermiteCoeff1D_decay` at exponent `k + 2`:
  `|cₙ(f)| · (1+n)^(k+2) ≤ C · ‖f‖`, so `|cₙ(f)| · (1+n)^k ≤ C · ‖f‖ · (1+n)⁻²`,
which is summable.
-/
private theorem hermiteCoeff_rapid_decay (f : SchwartzMap ℝ ℝ) (k : ℕ) :
    Summable (fun m => |hermiteCoeff1D m f| * (1 + (m : ℝ)) ^ k) := by
  -- Get decay bound at k+2 (real exponent)
  obtain ⟨C, q, hC, hbound⟩ := hermiteCoeff1D_decay ((k : ℝ) + 2)
  set S := (Finset.Iic q).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f
  -- Each term bounded by C * S * (1+m)^{-2}
  have h_le : ∀ m : ℕ, |hermiteCoeff1D m f| * (1 + (m : ℝ)) ^ k ≤
      C * S * (1 + (m : ℝ)) ^ ((-2) : ℝ) := by
    intro m
    have h1m : (0 : ℝ) < 1 + ↑m := by positivity
    have h_bd := hbound f m
    -- h_bd : |c_m| * (1+m)^((k:ℝ)+2) ≤ C * S
    -- Convert: (1+m)^((k:ℝ)+2) = (1+m)^k * (1+m)^2
    have h_split : (1 + (m : ℝ)) ^ ((k : ℝ) + 2) =
        (1 + (m : ℝ)) ^ (k : ℕ) * (1 + (m : ℝ)) ^ (2 : ℝ) := by
      rw [← rpow_natCast (1 + ↑m) k, ← rpow_add h1m]
    rw [h_split] at h_bd
    have h2_pos : (0 : ℝ) < (1 + ↑m) ^ (2 : ℝ) := rpow_pos_of_pos h1m 2
    have hle : |hermiteCoeff1D m f| * (1 + ↑m) ^ k ≤ C * S / (1 + ↑m) ^ (2 : ℝ) := by
      rw [le_div_iff₀ h2_pos]
      calc |hermiteCoeff1D m f| * (1 + ↑m) ^ k * (1 + ↑m) ^ (2 : ℝ)
          = |hermiteCoeff1D m f| * ((1 + ↑m) ^ (k : ℕ) * (1 + ↑m) ^ (2 : ℝ)) := by ring
        _ ≤ C * S := h_bd
    rwa [div_eq_mul_inv, ← rpow_neg h1m.le] at hle
  -- ∑ C * S * (1+m)^{-2} converges
  have h_sum : Summable (fun m : ℕ => C * S * (1 + (m : ℝ)) ^ ((-2) : ℝ)) := by
    have h_base : Summable (fun n : ℕ => ((n : ℝ)) ^ ((-2) : ℝ)) :=
      summable_nat_rpow.mpr (by norm_num)
    have h_shifted := h_base.comp_injective
      (show Function.Injective (· + 1 : ℕ → ℕ) from fun a b h => Nat.succ_injective h)
    have h1 : Summable (fun n : ℕ => (1 + (n : ℝ)) ^ ((-2) : ℝ)) :=
      h_shifted.congr (fun n => by change ((↑(n + 1) : ℝ)) ^ ((-2) : ℝ) = _; simp [add_comm])
    exact h1.const_smul (C * S)
  exact .of_nonneg_of_le (fun m => mul_nonneg (abs_nonneg _)
    (pow_nonneg (by positivity) k)) h_le h_sum

/-- The forward linear map of the 1D Hermite isomorphism:
`f ↦ (hermiteCoeff1D n f)ₙ` as a rapid decay sequence.
-/
private def toRapidDecay1DLM : SchwartzMap ℝ ℝ →ₗ[ℝ] RapidDecaySeq where
  toFun f := ⟨fun n => hermiteCoeff1D n f, hermiteCoeff_rapid_decay f⟩
  map_add' f g := RapidDecaySeq.ext fun n => (hermiteCoeff1D_linear n).map_add f g
  map_smul' r f := RapidDecaySeq.ext fun n => by
    simp only [RapidDecaySeq.smul_val, RingHom.id_apply]
    exact (hermiteCoeff1D_linear n).map_smul r f

/-- The forward CLM: Schwartz → RapidDecaySeq via Hermite coefficients. -/
private noncomputable def toRapidDecay1DCLM : SchwartzMap ℝ ℝ →L[ℝ] RapidDecaySeq where
  toLinearMap := toRapidDecay1DLM
  cont := by
    -- Each rapidDecaySeminorm k on the output is bounded by Schwartz seminorms on the input
    apply WithSeminorms.continuous_of_isBounded
      (schwartz_withSeminorms ℝ ℝ ℝ) RapidDecaySeq.rapidDecay_withSeminorms
    intro k
    -- rapidDecaySeminorm k (toRapidDecay1DLM f) = ∑' n, |cₙ(f)| * (1+n)^k
    -- From hermiteCoeff1D_decay ((k:ℝ)+2), each |cₙ(f)| * (1+n)^k ≤ C * S * (1+n)^{-2}
    -- So the sum ≤ C * S * ∑ (1+n)^{-2} = C' * S where S is a sup of Schwartz seminorms
    obtain ⟨C, q, hC, hbound⟩ := hermiteCoeff1D_decay ((k : ℝ) + 2)
    -- Sum of (1+n)^{-2}
    have h_base : Summable (fun n : ℕ => ((n : ℝ)) ^ ((-2) : ℝ)) :=
      summable_nat_rpow.mpr (by norm_num)
    have h_shifted := h_base.comp_injective
      (show Function.Injective (· + 1 : ℕ → ℕ) from fun a b h => Nat.succ_injective h)
    have h_rpow_sum : Summable (fun n : ℕ => (1 + (n : ℝ)) ^ ((-2) : ℝ)) :=
      h_shifted.congr (fun n => by change ((↑(n + 1) : ℝ)) ^ ((-2) : ℝ) = _; simp [add_comm])
    set L := ∑' n : ℕ, (1 + (n : ℝ)) ^ ((-2) : ℝ)
    -- Total bound: C * L
    refine ⟨Finset.Iic q, ⟨C * L, by positivity⟩, fun f => ?_⟩
    -- Show: rapidDecaySeminorm k (toRapidDecay1DLM f) ≤ (C * L) • (sup seminorms) f
    simp only [Seminorm.comp_apply]
    set S := (Finset.Iic q).sup (schwartzSeminormFamily ℝ ℝ ℝ) f
    -- Each term bounded by C * S * (1+n)^{-2}
    have h_le : ∀ n : ℕ, |hermiteCoeff1D n f| * (1 + (n : ℝ)) ^ k ≤
        C * S * (1 + (n : ℝ)) ^ ((-2) : ℝ) := by
      intro n
      have h1n : (0 : ℝ) < 1 + ↑n := by positivity
      have h_bd := hbound f n
      have h_split : (1 + (n : ℝ)) ^ ((k : ℝ) + 2) =
          (1 + (n : ℝ)) ^ (k : ℕ) * (1 + (n : ℝ)) ^ (2 : ℝ) := by
        rw [← rpow_natCast (1 + ↑n) k, ← rpow_add h1n]
      rw [h_split] at h_bd
      have h2_pos : (0 : ℝ) < (1 + ↑n) ^ (2 : ℝ) := rpow_pos_of_pos h1n 2
      have hle : |hermiteCoeff1D n f| * (1 + ↑n) ^ k ≤ C * S / (1 + ↑n) ^ (2 : ℝ) := by
        rw [le_div_iff₀ h2_pos]
        calc |hermiteCoeff1D n f| * (1 + ↑n) ^ k * (1 + ↑n) ^ (2 : ℝ)
            = |hermiteCoeff1D n f| * ((1 + ↑n) ^ (k : ℕ) * (1 + ↑n) ^ (2 : ℝ)) := by ring
          _ ≤ C * S := h_bd
      rwa [div_eq_mul_inv, ← rpow_neg h1n.le] at hle
    have h_tsum := (hermiteCoeff_rapid_decay f k).tsum_le_tsum h_le (h_rpow_sum.const_smul (C * S))
    calc ∑' n, |hermiteCoeff1D n f| * (1 + ↑n) ^ k
        ≤ ∑' (n : ℕ), C * S * (1 + (n : ℝ)) ^ ((-2) : ℝ) := h_tsum
      _ = C * S * L := by rw [tsum_mul_left]
      _ = C * L * S := by ring

/-- T2Space instance for Schwartz maps.
Derived from T1Space via topological group structure.
-/
noncomputable instance schwartzMapT2Space : T2Space (SchwartzMap ℝ ℝ) := by
  haveI : T1Space (SchwartzMap ℝ ℝ) :=
    WithSeminorms.T1_of_separating (schwartz_withSeminorms ℝ ℝ ℝ) fun f hf =>
      by
        -- If f ≠ 0, then seminorm(0,0) is nonzero since ‖f x‖ ≤ seminorm(0,0)(f)
        exact ⟨⟨0, 0⟩, fun h => hf (SchwartzMap.ext fun x =>
          norm_le_zero_iff.mp ((SchwartzMap.norm_le_seminorm ℝ f x).trans (le_of_eq h)))⟩
  exact inferInstance

/-! ### Constructing the Schwartz limit of `∑ aₙ ψₙ`

For a rapid-decay sequence `a`, the pointwise series `g(x) = ∑' n, aₙ · ψₙ(x)` converges
(in ℝ, which is complete) and defines a Schwartz function. We construct it explicitly,
avoiding the need for `CompleteSpace (SchwartzMap ℝ ℝ)` (not yet in Mathlib).
-/

/-- Bound on iterated derivative of `c * ψₙ`: `‖D^k(c·ψₙ)(x)‖ ≤ |c| · p_{0,k}(ψₙ)`. -/
private lemma scalar_hermite_iteratedFDeriv_bound (c : ℝ) (n k : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ k (fun y => c * hermiteFunction n y) x‖ ≤
    |c| * SchwartzMap.seminorm ℝ 0 k (schwartzHermiteBasis1D n) := by
  rw [show (fun y => c * hermiteFunction n y) =
    (fun y => c • hermiteFunction n y) from by ext; simp [smul_eq_mul]]
  rw [iteratedFDeriv_const_smul_apply' ((hermiteFunction_contDiff n k).contDiffAt),
    norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (by
    have h := SchwartzMap.le_seminorm ℝ 0 k (schwartzHermiteBasis1D n) x
    simp only [pow_zero, one_mul] at h
    rwa [show iteratedFDeriv ℝ k (⇑(schwartzHermiteBasis1D n)) x =
      iteratedFDeriv ℝ k (hermiteFunction n) x from
      congr_arg (iteratedFDeriv ℝ k · x) (schwartzHermiteBasis1D_coe n)] at h)
    (abs_nonneg _)

/-- Summability of `∑ |aₙ| · p_{k,l}(ψₙ)` for rapid-decay sequences.
Uses basis growth `p_{k,l}(ψₙ) ≤ C(1+n)^s` and rapid decay `∑ |aₙ|(1+n)^s < ∞`.
-/
private lemma rapidDecay_seminorm_summable (a : RapidDecaySeq) (k l : ℕ) :
    Summable (fun n => |a.val n| * SchwartzMap.seminorm ℝ k l (schwartzHermiteBasis1D n)) := by
  obtain ⟨C, hC, s, hbasis⟩ := schwartzHermiteBasis1D_growth k l
  exact .of_nonneg_of_le
    (fun n => mul_nonneg (abs_nonneg _) (apply_nonneg _ _))
    (fun n => by
      calc |a.val n| * SchwartzMap.seminorm ℝ k l (schwartzHermiteBasis1D n)
          ≤ |a.val n| * (C * (1 + ↑n) ^ s) :=
            mul_le_mul_of_nonneg_left (hbasis n) (abs_nonneg _)
        _ = C * (|a.val n| * (1 + ↑n) ^ s) := by ring)
    (Summable.mul_left C (a.rapid_decay s))

/-- The pointwise tsum is smooth. -/
private lemma rapidDecay_hermite_contDiff (a : RapidDecaySeq) :
    ContDiff ℝ ∞ (fun x => ∑' n, a.val n * hermiteFunction n x) := by
  apply contDiff_tsum
    (v := fun j n => |a.val n| * SchwartzMap.seminorm ℝ 0 j (schwartzHermiteBasis1D n))
  · intro n
    exact contDiff_infty.mpr (fun m => contDiff_const.mul (hermiteFunction_contDiff n m))
  · intro j _; exact rapidDecay_seminorm_summable a 0 j
  · intro j n x _; exact scalar_hermite_iteratedFDeriv_bound (a.val n) n j x

/-- Pointwise bound: `‖x‖^k · ‖D^l(∑' aₙψₙ)(x)‖ ≤ ∑' |aₙ| · p_{k,l}(ψₙ)`. -/
private lemma rapidDecay_pointwise_seminorm_le (a : RapidDecaySeq) (k l : ℕ) (x : ℝ) :
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ l (fun y => ∑' n, a.val n * hermiteFunction n y) x‖ ≤
    ∑' n, |a.val n| * SchwartzMap.seminorm ℝ k l (schwartzHermiteBasis1D n) := by
  -- Interchange iteratedFDeriv and tsum
  have h_iFD : iteratedFDeriv ℝ l (fun y => ∑' n, a.val n * hermiteFunction n y) x =
      ∑' n, iteratedFDeriv ℝ l (fun y => a.val n * hermiteFunction n y) x := by
    apply iteratedFDeriv_tsum_apply (N := ⊤)
      (v := fun j n => |a.val n| * SchwartzMap.seminorm ℝ 0 j (schwartzHermiteBasis1D n))
    · intro n
      exact contDiff_infty.mpr (fun m => contDiff_const.mul (hermiteFunction_contDiff n m))
    · intro j _; exact rapidDecay_seminorm_summable a 0 j
    · intro j n y _; exact scalar_hermite_iteratedFDeriv_bound (a.val n) n j y
    · exact le_top
  rw [h_iFD]
  -- Summability of norms
  have h_norm_summ : Summable (fun n =>
      ‖iteratedFDeriv ℝ l (fun y => a.val n * hermiteFunction n y) x‖) :=
    .of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun n => scalar_hermite_iteratedFDeriv_bound (a.val n) n l x)
      (rapidDecay_seminorm_summable a 0 l)
  -- Pointwise bound: ‖x‖^k * ‖iteratedFDeriv(c*ψ_n)‖ ≤ |c| * p_{k,l}(ψ_n)
  have h_ptwise : ∀ n, ‖x‖ ^ k *
      ‖iteratedFDeriv ℝ l (fun y => a.val n * hermiteFunction n y) x‖ ≤
      |a.val n| * SchwartzMap.seminorm ℝ k l (schwartzHermiteBasis1D n) := by
    intro n
    have hfun_eq : (fun y => a.val n * hermiteFunction n y) =
        ⇑(a.val n • schwartzHermiteBasis1D n) := by
      ext y; simp [smul_eq_mul, schwartzHermiteBasis1D_apply]
    rw [hfun_eq]
    calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ l (⇑(a.val n • schwartzHermiteBasis1D n)) x‖
        ≤ SchwartzMap.seminorm ℝ k l (a.val n • schwartzHermiteBasis1D n) :=
          SchwartzMap.le_seminorm ℝ k l _ x
      _ = |a.val n| * SchwartzMap.seminorm ℝ k l (schwartzHermiteBasis1D n) := by
          rw [map_smul_eq_mul, Real.norm_eq_abs]
  -- Chain: ‖x‖^k * ‖tsum‖ ≤ tsum of bounds
  calc ‖x‖ ^ k * ‖∑' n, iteratedFDeriv ℝ l (fun y => a.val n * hermiteFunction n y) x‖
      ≤ ‖x‖ ^ k * ∑' n, ‖iteratedFDeriv ℝ l (fun y => a.val n * hermiteFunction n y) x‖ :=
        mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm h_norm_summ)
          (pow_nonneg (norm_nonneg _) k)
    _ = ∑' n, ‖x‖ ^ k * ‖iteratedFDeriv ℝ l (fun y => a.val n * hermiteFunction n y) x‖ :=
        tsum_mul_left.symm
    _ ≤ ∑' n, |a.val n| * SchwartzMap.seminorm ℝ k l (schwartzHermiteBasis1D n) :=
        (Summable.of_nonneg_of_le
          (fun _ => mul_nonneg (pow_nonneg (norm_nonneg _) k) (norm_nonneg _))
          h_ptwise (rapidDecay_seminorm_summable a k l)).tsum_le_tsum
          h_ptwise (rapidDecay_seminorm_summable a k l)

/-- The pointwise tsum has Schwartz decay: `‖x‖^k · ‖D^l g(x)‖ ≤ C` uniformly. -/
private lemma rapidDecay_hermite_decay (a : RapidDecaySeq) (k l : ℕ) :
    ∃ C : ℝ, ∀ x : ℝ, ‖x‖ ^ k *
      ‖iteratedFDeriv ℝ l (fun y => ∑' n, a.val n * hermiteFunction n y) x‖ ≤ C :=
  ⟨_, rapidDecay_pointwise_seminorm_le a k l⟩

/-- The Schwartz function defined by a rapid-decay Hermite expansion. -/
private noncomputable def rapidDecay_schwartzMap (a : RapidDecaySeq) : SchwartzMap ℝ ℝ where
  toFun := fun x => ∑' n, a.val n * hermiteFunction n x
  smooth' := rapidDecay_hermite_contDiff a
  decay' := rapidDecay_hermite_decay a

/-- Coercion: `rapidDecay_schwartzMap a` evaluates to the pointwise tsum. -/
private lemma rapidDecay_schwartzMap_apply (a : RapidDecaySeq) (x : ℝ) :
    rapidDecay_schwartzMap a x = ∑' n, a.val n * hermiteFunction n x := rfl

/-- The Hermite expansion converges to `rapidDecay_schwartzMap a` in Schwartz topology. -/
private theorem rapidDecay_hermite_hasSum (a : RapidDecaySeq) :
    HasSum (fun n => a.val n • schwartzHermiteBasis1D n) (rapidDecay_schwartzMap a) := by
  rw [HasSum]
  change Filter.Tendsto _ Filter.atTop _
  rw [(schwartz_withSeminorms ℝ ℝ ℝ).tendsto_nhds _ (rapidDecay_schwartzMap a)]
  intro ⟨k, l⟩ ε hε
  -- Get vanishing condition from summability of ∑ |aₙ| * p_{k,l}(ψₙ)
  have h_sem := rapidDecay_seminorm_summable a k l
  obtain ⟨s₀, hs₀⟩ := summable_iff_vanishing_norm.mp h_sem (ε / 2) (half_pos hε)
  rw [Filter.eventually_atTop]
  refine ⟨s₀, fun s hs => ?_⟩
  -- Flip subtraction order: (∑ - limit) = -(limit - ∑)
  rw [show (∑ i ∈ s, a.val i • schwartzHermiteBasis1D i) - rapidDecay_schwartzMap a =
    -(rapidDecay_schwartzMap a - ∑ i ∈ s, a.val i • schwartzHermiteBasis1D i) from by abel,
    map_neg_eq_map]
  -- Suffices to show seminorm(limit - partial sum) ≤ ε/2 < ε
  calc SchwartzMap.seminorm ℝ k l
        (rapidDecay_schwartzMap a - ∑ i ∈ s, a.val i • schwartzHermiteBasis1D i)
      ≤ ε / 2 := by
        -- Reduce to pointwise bound via seminorm_le_bound
        apply SchwartzMap.seminorm_le_bound ℝ k l _ (half_pos hε).le
        intro x
        -- Set up notation
        set r := rapidDecay_schwartzMap a -
          ∑ i ∈ s, a.val i • schwartzHermiteBasis1D i with hr_def
        let g : ℕ → ℝ → ℝ := fun n y => a.val n * hermiteFunction n y
        -- Summability of iteratedFDeriv values
        have h_summ_iFD : Summable (fun n => iteratedFDeriv ℝ l (g n) x) := by
          apply Summable.of_norm_bounded
            (g := fun n => |a.val n| *
              SchwartzMap.seminorm ℝ 0 l (schwartzHermiteBasis1D n))
          · exact rapidDecay_seminorm_summable a 0 l
          · intro n; exact scalar_hermite_iteratedFDeriv_bound (a.val n) n l x
        -- Step 1: iteratedFDeriv of the limit = ∑' iteratedFDeriv(gₙ)
        have h_iFD_limit : iteratedFDeriv ℝ l
            (fun y => ∑' n, a.val n * hermiteFunction n y) x =
            ∑' n, iteratedFDeriv ℝ l (g n) x := by
          apply iteratedFDeriv_tsum_apply (N := ⊤)
            (v := fun j n => |a.val n| *
              SchwartzMap.seminorm ℝ 0 j (schwartzHermiteBasis1D n))
          · intro n
            exact contDiff_infty.mpr (fun m =>
              contDiff_const.mul (hermiteFunction_contDiff n m))
          · intro j _; exact rapidDecay_seminorm_summable a 0 j
          · intro j n y _; exact scalar_hermite_iteratedFDeriv_bound (a.val n) n j y
          · exact le_top
        -- Step 2: coercion of finite Schwartz sum = pointwise finite sum
        have hsum_coe : ∀ y,
            (∑ i ∈ s, a.val i • schwartzHermiteBasis1D i : SchwartzMap ℝ ℝ) y =
            ∑ i ∈ s, g i y := by
          intro y
          have : ∀ (t : Finset ℕ),
              (∑ i ∈ t, a.val i • schwartzHermiteBasis1D i : SchwartzMap ℝ ℝ) y =
              ∑ i ∈ t, g i y := by
            intro t; induction t using Finset.cons_induction with
            | empty => simp
            | cons a' t' ha' ih =>
              simp [SchwartzMap.smul_apply, smul_eq_mul, schwartzHermiteBasis1D_apply, g]
          exact this s
        -- Step 3: iteratedFDeriv of the finite sum
        have h_iFD_sum : iteratedFDeriv ℝ l
            (⇑(∑ i ∈ s, a.val i • schwartzHermiteBasis1D i : SchwartzMap ℝ ℝ)) x =
            ∑ i ∈ s, iteratedFDeriv ℝ l (g i) x := by
          have hcoe : ⇑(∑ i ∈ s, a.val i • schwartzHermiteBasis1D i : SchwartzMap ℝ ℝ) =
              fun y => ∑ i ∈ s, g i y := funext hsum_coe
          rw [hcoe]
          have h_eq := iteratedFDeriv_sum (𝕜 := ℝ) (f := g) (u := s) (i := l)
            (fun i _ => (contDiff_const.mul (hermiteFunction_contDiff i l)).of_le le_rfl)
          exact congr_fun h_eq x |>.trans (Finset.sum_apply x s _)
        -- Step 4: iteratedFDeriv of r = ∑'_{i∉s} iteratedFDeriv(gₙ)
        have h_iFD_r : iteratedFDeriv ℝ l (⇑r) x =
            ∑' (i : ↥(↑s : Set ℕ)ᶜ), iteratedFDeriv ℝ l (g ↑i) x := by
          have hf_cd : ContDiff ℝ l (fun y => ∑' n, a.val n * hermiteFunction n y) :=
            (rapidDecay_hermite_contDiff a).of_le (mod_cast le_top)
          have hg_cd : ContDiff ℝ l (fun y => ∑ i ∈ s, g i y) :=
            ContDiff.sum (fun i _ =>
              (contDiff_const.mul (hermiteFunction_contDiff i l)).of_le le_rfl)
          have hcoe_r : (⇑r : ℝ → ℝ) = fun y =>
              (∑' n, a.val n * hermiteFunction n y) - ∑ i ∈ s, g i y := by
            ext y; simp only [hr_def, SchwartzMap.sub_apply, rapidDecay_schwartzMap_apply]
            exact congrArg ((∑' n, a.val n * hermiteFunction n y) - ·) (hsum_coe y)
          rw [hcoe_r]
          set h_sum := fun y => ∑ i ∈ s, g i y with h_sum_def
          have h_neg_cd : ContDiff ℝ l (-h_sum) := hg_cd.neg
          have h_rw : (fun y => (∑' n, a.val n * hermiteFunction n y) - h_sum y) =
              (fun y => ∑' n, a.val n * hermiteFunction n y) + (-h_sum) := by
            ext; simp [sub_eq_add_neg]
          rw [h_rw, iteratedFDeriv_add hf_cd h_neg_cd, Pi.add_apply,
            iteratedFDeriv_neg, Pi.neg_apply, h_iFD_limit]
          have h_iFD_h : iteratedFDeriv ℝ l h_sum x =
              ∑ i ∈ s, iteratedFDeriv ℝ l (g i) x := by
            rw [h_sum_def]
            have h_eq := iteratedFDeriv_sum (𝕜 := ℝ) (f := g) (u := s) (i := l)
              (fun i _ =>
                (contDiff_const.mul (hermiteFunction_contDiff i l)).of_le le_rfl)
            calc iteratedFDeriv ℝ l (fun y => ∑ i ∈ s, g i y) x
                = (∑ j ∈ s, iteratedFDeriv ℝ l (g j)) x := congr_fun h_eq x
              _ = ∑ i ∈ s, iteratedFDeriv ℝ l (g i) x := Finset.sum_apply x s _
          rw [h_iFD_h]
          rw [← h_summ_iFD.sum_add_tsum_compl (s := s)]
          abel
        -- Summability on complement
        have h_norm_summ : Summable (fun (i : ↥(↑s : Set ℕ)ᶜ) =>
            ‖iteratedFDeriv ℝ l (g ↑i) x‖) :=
          (Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
            (fun n => scalar_hermite_iteratedFDeriv_bound (a.val n) n l x)
            (rapidDecay_seminorm_summable a 0 l)).subtype _
        have h_sem_summ : Summable (fun (i : ↥(↑s : Set ℕ)ᶜ) =>
            |a.val ↑i| *
            SchwartzMap.seminorm ℝ k l (schwartzHermiteBasis1D ↑i)) :=
          (rapidDecay_seminorm_summable a k l).subtype _
        -- Key pointwise bound
        have h_ptwise : ∀ (i : ↥(↑s : Set ℕ)ᶜ),
            ‖x‖ ^ k * ‖iteratedFDeriv ℝ l (g ↑i) x‖ ≤
            |a.val ↑i| * SchwartzMap.seminorm ℝ k l (schwartzHermiteBasis1D ↑i) := by
          intro ⟨n, _⟩
          have hg_eq : g n = ⇑(a.val n • schwartzHermiteBasis1D n) := by
            ext y; simp [g, smul_eq_mul, schwartzHermiteBasis1D_apply]
          rw [hg_eq]
          calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ l (⇑(a.val n • schwartzHermiteBasis1D n)) x‖
              ≤ SchwartzMap.seminorm ℝ k l (a.val n • schwartzHermiteBasis1D n) :=
                SchwartzMap.le_seminorm ℝ k l _ x
            _ = |a.val n| * SchwartzMap.seminorm ℝ k l (schwartzHermiteBasis1D n) := by
                rw [map_smul_eq_mul, Real.norm_eq_abs]
        -- Chain the bounds
        rw [h_iFD_r]
        calc ‖x‖ ^ k * ‖∑' (i : ↥(↑s : Set ℕ)ᶜ), iteratedFDeriv ℝ l (g ↑i) x‖
            ≤ ‖x‖ ^ k * ∑' (i : ↥(↑s : Set ℕ)ᶜ),
                ‖iteratedFDeriv ℝ l (g ↑i) x‖ :=
              mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm h_norm_summ)
                (pow_nonneg (norm_nonneg _) k)
          _ = ∑' (i : ↥(↑s : Set ℕ)ᶜ),
                (‖x‖ ^ k * ‖iteratedFDeriv ℝ l (g ↑i) x‖) := by
              rw [tsum_mul_left]
          _ ≤ ∑' (i : ↥(↑s : Set ℕ)ᶜ),
                (|a.val ↑i| *
                  SchwartzMap.seminorm ℝ k l (schwartzHermiteBasis1D ↑i)) :=
              (h_norm_summ.mul_left _).tsum_le_tsum h_ptwise h_sem_summ
          _ ≤ ε / 2 := by
              apply h_sem_summ.tsum_le_of_sum_le
              intro t
              set t' := t.map ⟨Subtype.val, Subtype.val_injective⟩ with ht'_def
              have h_disj : Disjoint t' s := by
                rw [Finset.disjoint_left]
                intro n hn hn_s
                rw [Finset.mem_map] at hn
                obtain ⟨⟨m, hm⟩, _, rfl⟩ := hn
                exact hm hn_s
              have h_disj₀ : Disjoint t' s₀ := Disjoint.mono_right hs h_disj
              have h_lt := hs₀ t' h_disj₀
              rw [Real.norm_of_nonneg (Finset.sum_nonneg fun i _ =>
                mul_nonneg (abs_nonneg _) (apply_nonneg _ _))] at h_lt
              rw [ht'_def, Finset.sum_map] at h_lt
              exact le_of_lt h_lt
    _ < ε := half_lt_self hε

/-- **Summability of Hermite expansion for rapid-decay coefficients.** -/
private theorem rapidDecay_hermite_summable (a : RapidDecaySeq) :
    Summable (fun n => a.val n • schwartzHermiteBasis1D n) :=
  ⟨_, rapidDecay_hermite_hasSum a⟩

/-- The backward linear map (underlying `LinearMap`). -/
private noncomputable def fromRapidDecay1DLM : RapidDecaySeq →ₗ[ℝ] SchwartzMap ℝ ℝ where
  toFun := fun a => ∑' n, a.val n • schwartzHermiteBasis1D n
  map_add' := fun a b => by
    simp only [RapidDecaySeq.add_val]
    rw [show (fun n => (a.val n + b.val n) • schwartzHermiteBasis1D n) =
      (fun n => a.val n • schwartzHermiteBasis1D n + b.val n • schwartzHermiteBasis1D n) from by
      ext n; rw [add_smul]]
    exact (rapidDecay_hermite_summable a).tsum_add (rapidDecay_hermite_summable b)
  map_smul' := fun r a => by
    simp only [RapidDecaySeq.smul_val, RingHom.id_apply]
    rw [show (fun n => (r * a.val n) • schwartzHermiteBasis1D n) =
      (fun n => r • (a.val n • schwartzHermiteBasis1D n)) from by
      ext n; rw [mul_smul]]
    exact (rapidDecay_hermite_summable a).tsum_const_smul r

/-- `fromRapidDecay1DLM a` equals `rapidDecay_schwartzMap a`. -/
private lemma fromRapidDecay1DLM_eq (a : RapidDecaySeq) :
    fromRapidDecay1DLM a = rapidDecay_schwartzMap a :=
  (rapidDecay_hermite_hasSum a).tsum_eq

/-- Seminorm bound: `p_{k,l}(fromRapidDecay1DLM a) ≤ ∑' n, |aₙ| * p_{k,l}(ψₙ)`. -/
private lemma fromRapidDecay1DLM_seminorm_le (a : RapidDecaySeq) (k l : ℕ) :
    SchwartzMap.seminorm ℝ k l (fromRapidDecay1DLM a) ≤
      ∑' n, |a.val n| * SchwartzMap.seminorm ℝ k l (schwartzHermiteBasis1D n) := by
  rw [fromRapidDecay1DLM_eq]
  exact SchwartzMap.seminorm_le_bound ℝ k l _ (tsum_nonneg fun n =>
    mul_nonneg (abs_nonneg _) (apply_nonneg _ _)) (rapidDecay_pointwise_seminorm_le a k l)

/-- Seminorm bound with rapid-decay seminorm: `p_{k,l}(Φ(a)) ≤ C * ρ_s(a)`. -/
private lemma fromRapidDecay1DLM_bound (k l : ℕ) :
    ∃ (C : ℝ), 0 < C ∧ ∃ (s : ℕ), ∀ (a : RapidDecaySeq),
      SchwartzMap.seminorm ℝ k l (fromRapidDecay1DLM a) ≤
        C * RapidDecaySeq.rapidDecaySeminorm s a := by
  obtain ⟨C, hC, s, hbasis⟩ := schwartzHermiteBasis1D_growth k l
  exact ⟨C, hC, s, fun a => by
    calc (SchwartzMap.seminorm ℝ k l) (fromRapidDecay1DLM a)
        ≤ ∑' n, |a.val n| * SchwartzMap.seminorm ℝ k l (schwartzHermiteBasis1D n) :=
          fromRapidDecay1DLM_seminorm_le a k l
      _ ≤ ∑' n, |a.val n| * (C * (1 + (n : ℝ)) ^ s) :=
          (rapidDecay_seminorm_summable a k l).tsum_le_tsum
            (fun n => mul_le_mul_of_nonneg_left (hbasis n) (abs_nonneg _))
            ((a.rapid_decay s).mul_left C |>.congr fun n => by ring)
      _ = C * ∑' n, |a.val n| * (1 + (n : ℝ)) ^ s := by
          rw [← tsum_mul_left]; congr 1; ext n; ring⟩

/-- The `IsBounded` property for `fromRapidDecay1DLM`: each Schwartz seminorm of the
output is bounded by a rapid-decay seminorm of the input.
-/
private lemma fromRapidDecay1DLM_isBounded :
    Seminorm.IsBounded RapidDecaySeq.rapidDecaySeminorm
      (schwartzSeminormFamily ℝ ℝ ℝ) fromRapidDecay1DLM := by
  intro ⟨k, l⟩
  obtain ⟨C, hC, s, hbound⟩ := fromRapidDecay1DLM_bound k l
  exact ⟨{s}, ⟨C, hC.le⟩, fun a => by
    simp only [Seminorm.comp_apply, schwartzSeminormFamily, Finset.sup_singleton,
      Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul]
    exact hbound a⟩

/-- The backward CLM: `RapidDecaySeq → SchwartzMap ℝ ℝ` via Hermite expansion. -/
private noncomputable def fromRapidDecay1DCLM : RapidDecaySeq →L[ℝ] SchwartzMap ℝ ℝ where
  toLinearMap := fromRapidDecay1DLM
  cont :=
    WithSeminorms.continuous_of_isBounded RapidDecaySeq.rapidDecay_withSeminorms
      (schwartz_withSeminorms ℝ ℝ ℝ) fromRapidDecay1DLM fromRapidDecay1DLM_isBounded

/-- The 1D Hermite isomorphism: `SchwartzMap ℝ ℝ ≃L[ℝ] RapidDecaySeq`. -/
noncomputable def schwartzRapidDecayEquiv1D :
    SchwartzMap ℝ ℝ ≃L[ℝ] RapidDecaySeq :=
  ContinuousLinearEquiv.equivOfInverse
    toRapidDecay1DCLM
    fromRapidDecay1DCLM
    -- Left inverse: fromRapidDecay1DCLM ∘ toRapidDecay1DCLM = id
    (fun f => by
      -- fromRapidDecay1DCLM (toRapidDecay1DCLM f) = ∑' n, cₙ(f) • ψₙ = f
      change ∑' n, hermiteCoeff1D n f • schwartzHermiteBasis1D n = f
      exact ((schwartz_hermite_hasSum f).unique
        (schwartz_hermite_hasSum f).summable.hasSum).symm)
    -- Right inverse: toRapidDecay1DCLM ∘ fromRapidDecay1DCLM = id
    (fun a => by
      -- Need: hermiteCoeff1D n (∑' m, aₘ ψₘ) = aₙ for all n
      apply RapidDecaySeq.ext; intro n
      -- Apply continuous hermiteCoeff1DCLM to interchange with tsum
      change hermiteCoeff1D n (∑' m, a.val m • schwartzHermiteBasis1D m) = a.val n
      -- Interchange hermiteCoeff1DCLM (continuous) with tsum
      rw [show hermiteCoeff1D n (∑' m, a.val m • schwartzHermiteBasis1D m) =
        hermiteCoeff1DCLM n (∑' m, a.val m • schwartzHermiteBasis1D m) from rfl,
        (hermiteCoeff1DCLM n).map_tsum (rapidDecay_hermite_summable a)]
      -- Now: ∑' m, hermiteCoeff1DCLM n (aₘ • ψₘ) = ∑' m, aₘ * δₙₘ = aₙ
      simp only [hermiteCoeff1DCLM_apply, map_smul, smul_eq_mul,
        hermiteCoeff1D_basis_kronecker]
      -- ∑' m, a.val m * if n = m then 1 else 0 = a.val n
      -- Convert `if n = m` to `if m = n` for tsum_ite_eq
      simp_rw [show ∀ m, (if n = m then (1 : ℝ) else 0) = if m = n then 1 else 0 from
        fun m => by split_ifs <;> simp_all]
      simp [mul_ite, mul_one, mul_zero, tsum_ite_eq])

/-- The inverse of `schwartzRapidDecayEquiv1D` evaluates pointwise as the 1D Hermite series
reconstruction: `(equiv.symm a) t = ∑' n, a_n * ψ_n(t)`.
-/
theorem schwartzRapidDecayEquiv1D_symm_apply (a : RapidDecaySeq) (t : ℝ) :
    (schwartzRapidDecayEquiv1D.symm a) t =
      ∑' n, a.val n * hermiteFunction n t := by
  simp only [schwartzRapidDecayEquiv1D, ContinuousLinearEquiv.symm_equivOfInverse,
    ContinuousLinearEquiv.equivOfInverse_apply]
  show fromRapidDecay1DCLM a t = _
  change fromRapidDecay1DLM a t = _
  rw [fromRapidDecay1DLM_eq]
  show rapidDecay_schwartzMap a t = _
  rfl

/-! ## Multi-Dimensional Sequence Space and Flattening -/

/-- A multi-index is a function `Fin d → ℕ`. -/
abbrev MultiIndex (d : ℕ) := Fin d → ℕ

/-- The magnitude (L1 norm) of a multi-index. -/
def _root_.GaussianField.MultiIndex.abs {d : ℕ} (α : MultiIndex d) : ℕ :=
  ∑ i, α i

/-- To flatten s(ℕ^d) to s(ℕ), we need a bijection that is polynomially bounded
in both directions. We use iterated Cantor pairing: peel off the last coordinate
via `Fin.succFunEquiv`, recurse, then pair with `Nat.pairEquiv`.

The domain is `MultiIndex (d + 1)` (i.e., `Fin (d + 1) → ℕ`) since `Fin 0 → ℕ`
is a singleton and cannot biject with `ℕ`. All downstream consumers have `d ≥ 1`.
-/
noncomputable def multiIndexEquiv : (d : ℕ) → MultiIndex (d + 1) ≃ ℕ
  | 0 => Equiv.funUnique (Fin 1) ℕ
  | (d + 1) => (Fin.succFunEquiv ℕ (d + 1)).trans
      ((Equiv.prodCongr (multiIndexEquiv d) (Equiv.refl ℕ)).trans Nat.pairEquiv)

/-- Auxiliary: `multiIndexEquiv (d+1)` unfolds to pairing. -/
private lemma multiIndexEquiv_succ_apply (d : ℕ) (α : MultiIndex (d + 2)) :
    multiIndexEquiv (d + 1) α =
      Nat.pair (multiIndexEquiv d ((Fin.succFunEquiv ℕ (d + 1) α).1))
        ((Fin.succFunEquiv ℕ (d + 1) α).2) := by
  simp [multiIndexEquiv, Equiv.trans_apply, Equiv.prodCongr_apply, Nat.pairEquiv]

/-- Auxiliary: `(multiIndexEquiv (d+1)).symm` unfolds through unpairing. -/
private lemma multiIndexEquiv_succ_symm (d : ℕ) (n : ℕ) :
    (multiIndexEquiv (d + 1)).symm n =
      (Fin.succFunEquiv ℕ (d + 1)).symm
        ((multiIndexEquiv d).symm (Nat.unpair n).1, (Nat.unpair n).2) := by
  apply (multiIndexEquiv (d + 1)).injective
  simp only [Equiv.apply_symm_apply]
  rw [multiIndexEquiv_succ_apply]
  simp only [Equiv.apply_symm_apply, Nat.pair_unpair]

/-- Auxiliary: `MultiIndex.abs` decomposes along `Fin.succFunEquiv` for `d + 2`. -/
private lemma multiIndex_abs_succ (d : ℕ) (α : MultiIndex (d + 2)) :
    (MultiIndex.abs α : ℝ) =
      (MultiIndex.abs ((Fin.succFunEquiv ℕ (d + 1) α).1) : ℝ) +
        ((Fin.succFunEquiv ℕ (d + 1) α).2 : ℝ) := by
  simp only [MultiIndex.abs]
  push_cast
  rw [Fin.sum_univ_castSucc (n := d + 1)]
  congr 1

/-- Auxiliary: `MultiIndex.abs` of the inverse at `d+1` decomposes through unpairing. -/
private lemma multiIndex_abs_succ_symm (d : ℕ) (n : ℕ) :
    (MultiIndex.abs ((multiIndexEquiv (d + 1)).symm n) : ℝ) =
      (MultiIndex.abs ((multiIndexEquiv d).symm (Nat.unpair n).1) : ℝ) +
        ((Nat.unpair n).2 : ℝ) := by
  rw [multiIndexEquiv_succ_symm]
  have h := multiIndex_abs_succ d
    ((Fin.succFunEquiv ℕ (d + 1)).symm
      ((multiIndexEquiv d).symm (Nat.unpair n).1, (Nat.unpair n).2))
  simp only [Equiv.apply_symm_apply] at h
  exact h

/-- The multi-index enumeration has polynomial growth.
Stated for `MultiIndex (d + 1)` since `multiIndexEquiv d : MultiIndex (d + 1) ≃ ℕ`.
-/
lemma multiIndexEquiv_growth (d : ℕ) :
    ∃ C > 0, ∃ k : ℕ, ∀ α : MultiIndex (d + 1),
      (1 + (multiIndexEquiv d α : ℝ)) ≤ C * (1 + (MultiIndex.abs α : ℝ)) ^ k := by
  induction d with
  | zero =>
    -- d = 0: multiIndexEquiv 0 = Equiv.funUnique (Fin 1) ℕ
    refine ⟨1, one_pos, 1, fun α => ?_⟩
    simp only [multiIndexEquiv, Equiv.funUnique_apply, one_mul, pow_one]
    suffices h : (α default : ℝ) ≤ (MultiIndex.abs α : ℝ) by linarith
    gcongr
    change α default ≤ ∑ i, α i
    rw [Fin.default_eq_zero]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0)
  | succ d ih =>
    -- d + 1: Cantor pairing with IH
    obtain ⟨C₁, hC₁, k₁, hbound₁⟩ := ih
    refine ⟨(C₁ + 1) ^ 2, by positivity, 2 * (k₁ + 1), fun α => ?_⟩
    rw [multiIndexEquiv_succ_apply]
    set β := (Fin.succFunEquiv ℕ (d + 1) α).1
    set a := (Fin.succFunEquiv ℕ (d + 1) α).2
    set m := multiIndexEquiv d β
    have h_abs := multiIndex_abs_succ d α
    have h_pair_bound : (1 : ℝ) + ↑(Nat.pair m a) ≤ ((1 + ↑m) + ↑a) ^ 2 := by
      have h1 : Nat.pair m a < (max m a + 1) ^ 2 := Nat.pair_lt_max_add_one_sq m a
      have h2 : max m a + 1 ≤ m + a + 1 := by omega
      have h3 : (max m a + 1) ^ 2 ≤ (m + a + 1) ^ 2 := Nat.pow_le_pow_left h2 2
      have h4 : Nat.pair m a + 1 ≤ (m + a + 1) ^ 2 := by omega
      have h5 : ((Nat.pair m a + 1 : ℕ) : ℝ) ≤ (((m + a + 1) ^ 2 : ℕ) : ℝ) :=
        Nat.cast_le.mpr h4
      simp only [Nat.cast_add, Nat.cast_one, Nat.cast_pow] at h5
      linarith
    have h_ih := hbound₁ β
    have h_one_abs : (1 : ℝ) ≤ 1 + (MultiIndex.abs α : ℝ) :=
      le_add_of_nonneg_right (Nat.cast_nonneg _)
    have h_β_le : (1 + (MultiIndex.abs β : ℝ)) ≤ (1 + (MultiIndex.abs α : ℝ)) := by
      linarith [h_abs, (show (0 : ℝ) ≤ ↑a from Nat.cast_nonneg a)]
    have h_a_le : (a : ℝ) ≤ (1 + (MultiIndex.abs α : ℝ)) := by
      linarith [h_abs, (show (0 : ℝ) ≤ (MultiIndex.abs β : ℝ) from Nat.cast_nonneg _)]
    have h_sum : (1 + (m : ℝ)) + ↑a ≤ (C₁ + 1) * (1 + (MultiIndex.abs α : ℝ)) ^ (k₁ + 1) := by
      have hm : (1 : ℝ) + ↑m ≤ C₁ * (1 + (MultiIndex.abs α : ℝ)) ^ (k₁ + 1) := by
        calc (1 : ℝ) + ↑m ≤ C₁ * (1 + (MultiIndex.abs β : ℝ)) ^ k₁ := h_ih
          _ ≤ C₁ * (1 + (MultiIndex.abs α : ℝ)) ^ k₁ := by
              apply mul_le_mul_of_nonneg_left _ hC₁.le
              exact pow_le_pow_left₀ (by positivity) h_β_le k₁
          _ ≤ C₁ * (1 + (MultiIndex.abs α : ℝ)) ^ (k₁ + 1) := by
              apply mul_le_mul_of_nonneg_left _ hC₁.le
              exact pow_le_pow_right₀ h_one_abs (Nat.le_succ k₁)
      have ha : (a : ℝ) ≤ 1 * (1 + (MultiIndex.abs α : ℝ)) ^ (k₁ + 1) := by
        rw [one_mul]
        calc (a : ℝ) ≤ (1 + (MultiIndex.abs α : ℝ)) ^ 1 := by rw [pow_one]; exact h_a_le
          _ ≤ (1 + (MultiIndex.abs α : ℝ)) ^ (k₁ + 1) :=
              pow_le_pow_right₀ h_one_abs (by omega)
      linarith
    calc (1 : ℝ) + ↑(Nat.pair m a)
        ≤ ((1 + ↑m) + ↑a) ^ 2 := h_pair_bound
      _ ≤ ((C₁ + 1) * (1 + (MultiIndex.abs α : ℝ)) ^ (k₁ + 1)) ^ 2 := by
          apply pow_le_pow_left₀ (by positivity) h_sum
      _ = (C₁ + 1) ^ 2 * (1 + (MultiIndex.abs α : ℝ)) ^ (2 * (k₁ + 1)) := by
          rw [mul_pow]; ring_nf

/-- The inverse of the multi-index enumeration has polynomial growth.
Stated for `multiIndexEquiv d : MultiIndex (d + 1) ≃ ℕ`.
-/
lemma multiIndexEquiv_symm_growth (d : ℕ) :
    ∃ C > 0, ∃ k : ℕ, ∀ n : ℕ,
      (1 + (MultiIndex.abs ((multiIndexEquiv d).symm n) : ℝ)) ≤ C * (1 + (n : ℝ)) ^ k := by
  induction d with
  | zero =>
    -- d = 0: multiIndexEquiv 0 = Equiv.funUnique (Fin 1) ℕ
    refine ⟨1, one_pos, 1, fun n => ?_⟩
    simp only [multiIndexEquiv, one_mul, pow_one, MultiIndex.abs]
    change (1 : ℝ) + ↑((Equiv.funUnique (Fin 1) ℕ).symm n 0) ≤ 1 + ↑n
    simp [Equiv.funUnique]
  | succ d ih =>
    -- d + 1: unpairing with IH
    obtain ⟨C₁, hC₁, k₁, hbound₁⟩ := ih
    refine ⟨C₁ + 1, by linarith, k₁ + 1, fun n => ?_⟩
    rw [multiIndex_abs_succ_symm]
    set p := (Nat.unpair n).1
    set q := (Nat.unpair n).2
    have h_unpair : (p : ℝ) + ↑q ≤ ↑n := by
      exact_mod_cast Nat.unpair_add_le n
    have h_p_le : (p : ℝ) ≤ ↑n := by linarith [show (0 : ℝ) ≤ ↑q from Nat.cast_nonneg q]
    have h_q_le : (q : ℝ) ≤ ↑n := by linarith [show (0 : ℝ) ≤ ↑p from Nat.cast_nonneg p]
    have h_one_n : (1 : ℝ) ≤ 1 + (n : ℝ) := le_add_of_nonneg_right (Nat.cast_nonneg n)
    have h_ih := hbound₁ p
    have h_1p : (1 : ℝ) + ↑p ≤ 1 + ↑n := by linarith
    have h_beta : (1 : ℝ) + ↑(MultiIndex.abs ((multiIndexEquiv d).symm p)) ≤
        C₁ * (1 + ↑n) ^ k₁ := by
      calc _ ≤ C₁ * (1 + ↑p) ^ k₁ := h_ih
        _ ≤ C₁ * (1 + ↑n) ^ k₁ := by
            apply mul_le_mul_of_nonneg_left _ hC₁.le
            exact pow_le_pow_left₀ (by positivity) h_1p k₁
    calc (1 : ℝ) + (↑(MultiIndex.abs ((multiIndexEquiv d).symm p)) + ↑q)
        ≤ C₁ * (1 + ↑n) ^ k₁ + ↑n := by linarith [h_beta, h_q_le]
      _ ≤ C₁ * (1 + ↑n) ^ (k₁ + 1) + (1 + ↑n) ^ (k₁ + 1) := by
          have hk : C₁ * (1 + ↑n) ^ k₁ ≤ C₁ * (1 + ↑n) ^ (k₁ + 1) := by
            apply mul_le_mul_of_nonneg_left _ hC₁.le
            exact pow_le_pow_right₀ h_one_n (Nat.le_succ k₁)
          have hn : (n : ℝ) ≤ (1 + ↑n) ^ (k₁ + 1) := by
            calc (n : ℝ) ≤ (1 + ↑n) ^ 1 := by rw [pow_one]; linarith
              _ ≤ (1 + ↑n) ^ (k₁ + 1) := pow_le_pow_right₀ h_one_n (by omega)
          linarith
      _ = (C₁ + 1) * (1 + ↑n) ^ (k₁ + 1) := by ring

/-! ## Multi-Dimensional Hermite Analysis -/

/-- The multidimensional Hermite function is the tensor product of 1D Hermite functions. -/
noncomputable def hermiteFunctionNd (d : ℕ) (α : MultiIndex d) :
    EuclideanSpace ℝ (Fin d) → ℝ :=
  fun x => ∏ i : Fin d, hermiteFunction (α i) (x i)

/-- Each factor `fun x => hermiteFunction (α i) (x i)` is smooth on `EuclideanSpace ℝ (Fin d)`. -/
private lemma hermiteFunctionNd_factor_contDiff (d : ℕ) (α : MultiIndex d) (i : Fin d) (m : ℕ) :
    ContDiff ℝ m (fun x : EuclideanSpace ℝ (Fin d) => hermiteFunction (α i) (x i)) :=
  (hermiteFunction_contDiff (α i) m).comp (contDiff_piLp_apply (p := 2))

/-- The multidimensional Hermite function is smooth. -/
private lemma hermiteFunctionNd_contDiff (d : ℕ) (α : MultiIndex d) :
    ContDiff ℝ ∞ (hermiteFunctionNd d α) := by
  apply contDiff_infty.mpr
  intro m
  exact contDiff_prod (fun i _ => hermiteFunctionNd_factor_contDiff d α i m)

/-- The multidimensional Hermite function has Schwartz decay.

The proof uses the product structure: each 1D factor `hermiteFunction (α i)` is Schwartz,
so for any `k`, the factor at coordinate `i` satisfies `|x_i|^k * |D^m ψ_{α_i}(x_i)| ≤ C`.
The `iteratedFDeriv` of the product decomposes via the multilinear Leibniz rule into sums of
products of individual derivatives. Each term has at most one "active" coordinate that absorbs
the `‖x‖^k` factor through Schwartz decay, while all other coordinates contribute bounded
derivative values.
-/
-- 1D Schwartz seminorm bound: |t|^k * ‖iteratedFDeriv ℝ m (hermiteFunction n) t‖ ≤ C
private lemma hermiteFunction_schwartz_seminorm_bound (n k m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      |t| ^ k * ‖iteratedFDeriv ℝ m (hermiteFunction n) t‖ ≤ C := by
  obtain ⟨φ, hφ⟩ := hermiteFunction_schwartz n
  have hcoe : (fun t => hermiteFunction n t) = ⇑φ := (funext hφ).symm
  refine ⟨SchwartzMap.seminorm ℝ k m φ, apply_nonneg _ _, fun t => ?_⟩
  have hle := SchwartzMap.le_seminorm ℝ k m φ t
  rw [Real.norm_eq_abs] at hle
  rwa [show iteratedFDeriv ℝ m (⇑φ) t = iteratedFDeriv ℝ m (hermiteFunction n) t from
    congr_arg (iteratedFDeriv ℝ m · t) hcoe.symm] at hle

-- The projection ‖EuclideanSpace.proj i‖ ≤ 1.
private lemma euclidean_proj_norm_le_one (d : ℕ) (i : Fin d) :
    ‖(EuclideanSpace.proj (𝕜 := ℝ) i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    (fun x => by simp only [one_mul]; exact PiLp.norm_apply_le (p := 2) x i)

-- The norm of the iterated derivative of (hermiteFunction n ∘ proj_i) at x is bounded
-- by the norm of the 1D iterated derivative at x i.
-- This follows from the chain rule and ‖proj_i‖ ≤ 1.
private lemma norm_iteratedFDeriv_hermite_comp_proj_le (d : ℕ) (n : ℕ) (i : Fin d) (m : ℕ)
    (x : EuclideanSpace ℝ (Fin d)) :
    ‖iteratedFDeriv ℝ m
      (fun x : EuclideanSpace ℝ (Fin d) => hermiteFunction n (x i)) x‖ ≤
    ‖iteratedFDeriv ℝ m (hermiteFunction n) (x i)‖ := by
  have hf_smooth : ContDiff ℝ ∞ (hermiteFunction n) :=
    contDiff_infty.mpr (hermiteFunction_contDiff n)
  set L : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := EuclideanSpace.proj (𝕜 := ℝ) i
  have hL_le : ‖L‖ ≤ 1 := euclidean_proj_norm_le_one d i
  have hcomp : (fun x : EuclideanSpace ℝ (Fin d) => hermiteFunction n (x i)) =
      (hermiteFunction n) ∘ L := rfl
  have hiFD : iteratedFDeriv ℝ m ((hermiteFunction n) ∘ L) x =
      (iteratedFDeriv ℝ m (hermiteFunction n) (L x)).compContinuousLinearMap (fun _ => L) :=
    L.iteratedFDeriv_comp_right hf_smooth x (i := m) (mod_cast le_top)
  have h_prod_le : ∏ _j : Fin m, ‖L‖ ≤ 1 := by
    calc ∏ _j : Fin m, ‖L‖ ≤ ∏ _j : Fin m, (1 : ℝ) :=
        Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun _ _ => hL_le)
      _ = 1 := by simp
  rw [hcomp, hiFD]
  calc ‖(iteratedFDeriv ℝ m (hermiteFunction n) (L x)).compContinuousLinearMap
        (fun _ => L)‖
      ≤ ‖iteratedFDeriv ℝ m (hermiteFunction n) (L x)‖ * ∏ _j : Fin m, ‖L‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ ‖iteratedFDeriv ℝ m (hermiteFunction n) (x i)‖ * 1 :=
        mul_le_mul_of_nonneg_left h_prod_le (norm_nonneg _)
    _ = ‖iteratedFDeriv ℝ m (hermiteFunction n) (x i)‖ := mul_one _

-- Bound on ‖iteratedFDeriv ℝ m (hermiteFunction n ∘ proj i) x‖ using 1D Schwartz decay.
-- Key: iteratedFDeriv of (f ∘ L) = (iteratedFDeriv f (L x)).comp L, and ‖L‖ ≤ 1.
private lemma iteratedFDeriv_hermite_comp_proj_bound (d : ℕ) (n : ℕ) (i : Fin d) (k m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : EuclideanSpace ℝ (Fin d),
      |x i| ^ k * ‖iteratedFDeriv ℝ m
        (fun x : EuclideanSpace ℝ (Fin d) => hermiteFunction n (x i)) x‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := hermiteFunction_schwartz_seminorm_bound n k m
  refine ⟨C, hC, fun x => ?_⟩
  calc |x i| ^ k * ‖iteratedFDeriv ℝ m
        (fun x : EuclideanSpace ℝ (Fin d) => hermiteFunction n (x i)) x‖
      ≤ |x i| ^ k * ‖iteratedFDeriv ℝ m (hermiteFunction n) (x i)‖ :=
        mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_hermite_comp_proj_le d n i m x)
          (pow_nonneg (abs_nonneg _) _)
    _ ≤ C := hbound (x i)

private lemma hermiteFunctionNd_decay (d : ℕ) (α : MultiIndex d) (k n : ℕ) :
    ∃ C : ℝ, ∀ x : EuclideanSpace ℝ (Fin d),
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (hermiteFunctionNd d α) x‖ ≤ C := by
  -- Strategy: Use the multinomial Leibniz rule (norm_iteratedFDeriv_prod_le) to decompose
  -- the derivative of the product ∏ f_j into a sum of products of individual derivatives.
  -- Then bound each term using Schwartz decay of individual 1D factors.
  --
  -- Step 1: Set up individual factor bounds from iteratedFDeriv_hermite_comp_proj_bound.
  -- For each j : Fin d and m : ℕ, we have:
  --   ‖iteratedFDeriv ℝ m (fun x => hermiteFunction (α j) (x j)) x‖ ≤ M(j,m) (bounded, k=0)
  --   |x j|^k * ‖iteratedFDeriv ℝ m (fun x => hermiteFunction (α j) (x j)) x‖ ≤ C(j,k,m)
  --
  -- Step 2: Apply norm_iteratedFDeriv_prod_le to get
  --   ‖D^n f x‖ ≤ ∑_{p ∈ sym n} mult(p) * ∏_j ‖D^{count j p} f_j x‖
  --
  -- Step 3: For each term, bound ‖x‖^k * ∏_j ‖D^{count j p} f_j x‖ ≤ C(p)
  --   using: ‖x‖ ≤ ∑ |x_j| (ℓ²≤ℓ¹) and distributing |x_j|^k to factor j.
  --
  -- For d = 0, the function is constant 1, so the bound is trivial.
  -- For d ≥ 1, we use the decomposition.
  --
  -- We use a simpler bound: the product of temperate growth functions has temperate growth,
  -- giving ‖D^n f x‖ ≤ A(1+‖x‖)^p. Combined with the pointwise bound
  -- |f(x)| ≤ ∏ M_j and the rapid decay |x_j|^k |f_j(x_j)| ≤ C_j for each coordinate,
  -- we get the result.
  --
  -- Actually, we prove this by showing each term in the Leibniz expansion is bounded
  -- by a product of 1D Schwartz bounds.
  rcases d with _ | d
  · -- d = 0: EuclideanSpace ℝ (Fin 0) is a point
    refine ⟨1, fun x => ?_⟩
    have hx : x = 0 := Subsingleton.eq_zero x
    subst hx
    simp only [norm_zero]
    rcases k with _ | k
    · simp only [pow_zero, one_mul]
      -- Need ‖iteratedFDeriv ℝ n (hermiteFunctionNd 0 α) 0‖ ≤ 1
      -- hermiteFunctionNd 0 α = fun x => ∏ i : Fin 0, ... = fun _ => 1
      have hf : hermiteFunctionNd 0 α = fun _ => 1 := by
        ext x; simp [hermiteFunctionNd, Finset.prod_empty]
      rw [hf]
      rcases n with _ | n
      · simp
      · simp [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero n)]
    · simp [zero_pow (Nat.succ_ne_zero k), zero_mul]
  -- d + 1 ≥ 1
  -- For each j and m, get the bounds from 1D Schwartz decay
  -- Use the abstract product bound
  -- First, get smooth factors
  set fac : Fin (d + 1) → EuclideanSpace ℝ (Fin (d + 1)) → ℝ :=
    fun j x => hermiteFunction (α j) (x j)
  have hfac_smooth : ∀ j, ContDiff ℝ ∞ (fac j) := fun j =>
    contDiff_infty.mpr (hermiteFunctionNd_factor_contDiff (d + 1) α j)
  -- The product equals hermiteFunctionNd
  have hprod_eq : (fun x => ∏ j : Fin (d + 1), fac j x) = hermiteFunctionNd (d + 1) α := by
    ext x; simp [hermiteFunctionNd, fac]
  -- Get uniform bounds for each factor
  -- M(j,m) = bound on ‖D^m f_j x‖ (k=0 case)
  -- C(j,k,m) = bound on |x j|^k * ‖D^m f_j x‖
  have hfac_bound : ∀ j : Fin (d + 1), ∀ m : ℕ,
      ∃ M : ℝ, 0 ≤ M ∧ ∀ x : EuclideanSpace ℝ (Fin (d + 1)),
        ‖iteratedFDeriv ℝ m (fac j) x‖ ≤ M := by
    intro j m
    obtain ⟨C, hC, hbound⟩ := iteratedFDeriv_hermite_comp_proj_bound (d + 1) (α j) j 0 m
    exact ⟨C, hC, fun x => by simpa using hbound x⟩
  have hfac_decay : ∀ j : Fin (d + 1), ∀ m : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x : EuclideanSpace ℝ (Fin (d + 1)),
        |x j| ^ k * ‖iteratedFDeriv ℝ m (fac j) x‖ ≤ C := by
    intro j m
    exact iteratedFDeriv_hermite_comp_proj_bound (d + 1) (α j) j k m
  -- Step A: Prove ‖x‖ ≤ ∑ |x j| (ℓ² ≤ ℓ¹ norm inequality)
  have h_l2_le_l1 : ∀ x : EuclideanSpace ℝ (Fin (d + 1)),
      ‖x‖ ≤ ∑ j : Fin (d + 1), |x j| := by
    intro x
    rw [EuclideanSpace.norm_eq]
    -- ‖x‖² = ∑ |x j|² ≤ (∑ |x j|)² by sum_sq_le_sq_sum_of_nonneg
    have hsq : ∑ j : Fin (d + 1), ‖x j‖ ^ 2 ≤
        (∑ j : Fin (d + 1), |x j|) ^ 2 := by
      convert Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
        (fun j _ => abs_nonneg (x j)) using 2
    calc √(∑ j, ‖x j‖ ^ 2) ≤ √((∑ j, |x j|) ^ 2) :=
          Real.sqrt_le_sqrt hsq
      _ = ∑ j, |x j| := by
          rw [Real.sqrt_sq_eq_abs, abs_of_nonneg
            (Finset.sum_nonneg (fun j _ => abs_nonneg _))]
  -- Step B: ‖x‖^k ≤ (d+1)^(k-1) * ∑ |x j|^k (from power mean inequality)
  -- Combined: ‖x‖^k ≤ (d+1)^k * ∑ |x j|^k
  have h_norm_pow_le : ∀ x : EuclideanSpace ℝ (Fin (d + 1)),
      ‖x‖ ^ k ≤ ((d + 1 : ℝ) ^ k) * ∑ j : Fin (d + 1), |x j| ^ k := by
    intro x
    rcases k with _ | k
    · -- k = 0: ‖x‖^0 = 1 ≤ (d+1)^0 * ∑ |x j|^0 = 1 * (d+1)
      simp only [pow_zero, one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_one]
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le d)
    -- k + 1 ≥ 1
    -- ‖x‖^(k+1) ≤ (∑ |x j|)^(k+1) ≤ (d+1)^k * ∑ |x j|^(k+1)
    have h1 : (1 : ℝ) ≤ (d + 1 : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le d)
    calc ‖x‖ ^ (k + 1) ≤ (∑ j : Fin (d + 1), |x j|) ^ (k + 1) :=
          pow_le_pow_left₀ (norm_nonneg _) (h_l2_le_l1 x) _
      _ ≤ ((Finset.univ : Finset (Fin (d + 1))).card : ℝ) ^ k *
            ∑ j ∈ Finset.univ, |x j| ^ (k + 1) :=
          _root_.pow_sum_le_card_mul_sum_pow (fun j _ => abs_nonneg (x j)) k
      _ = (d + 1 : ℝ) ^ k * ∑ j : Fin (d + 1), |x j| ^ (k + 1) := by
          simp [Finset.card_univ, Fintype.card_fin]
      _ ≤ (d + 1 : ℝ) ^ (k + 1) * ∑ j : Fin (d + 1), |x j| ^ (k + 1) := by
          apply mul_le_mul_of_nonneg_right
          · exact pow_le_pow_right₀ h1 (Nat.le_succ k)
          · exact Finset.sum_nonneg (fun j _ => pow_nonneg (abs_nonneg _) _)
  -- Step C: Apply the multinomial Leibniz rule and bound each term
  -- First get the Leibniz bound
  have hprod_bound : ∀ y : EuclideanSpace ℝ (Fin (d + 1)),
      ‖iteratedFDeriv ℝ n (fun z => ∏ j : Fin (d + 1), fac j z) y‖ ≤
      ∑ p ∈ (Finset.univ : Finset (Fin (d + 1))).sym n,
        (p : Multiset (Fin (d + 1))).countPerms *
          ∏ j ∈ (Finset.univ : Finset (Fin (d + 1))),
            ‖iteratedFDeriv ℝ ((p : Multiset (Fin (d + 1))).count j) (fac j) y‖ := by
    intro y
    exact norm_iteratedFDeriv_prod_le
      (fun j _ => hfac_smooth j) (mod_cast le_top)
  -- Rewrite using hprod_eq
  have hprod_eq' : ∀ y : EuclideanSpace ℝ (Fin (d + 1)),
      iteratedFDeriv ℝ n (hermiteFunctionNd (d + 1) α) y =
      iteratedFDeriv ℝ n (fun z => ∏ j : Fin (d + 1), fac j z) y := by
    intro y; rw [hprod_eq]
  -- Step D: Use choose to extract uniform bounding functions M(j,m) and C(j,m)
  -- from the existential bounds, then construct the total bounding constant.
  choose M hM using hfac_bound
  choose C_dec hC_dec using hfac_decay
  -- For each partition p and active coordinate j₀, bound the product term
  -- by isolating the j₀ factor using Finset.mul_prod_erase.
  have h_term : ∀ (x : EuclideanSpace ℝ (Fin (d + 1)))
      (j₀ : Fin (d + 1)) (p : Sym (Fin (d + 1)) n),
      |x j₀| ^ k *
        ∏ j ∈ (Finset.univ : Finset (Fin (d + 1))),
          ‖iteratedFDeriv ℝ ((p : Multiset (Fin (d + 1))).count j) (fac j) x‖ ≤
        C_dec j₀ ((p : Multiset (Fin (d + 1))).count j₀) *
          ∏ j ∈ (Finset.univ : Finset (Fin (d + 1))).erase j₀,
            M j ((p : Multiset (Fin (d + 1))).count j) := by
    intro x j₀ p
    rw [(Finset.mul_prod_erase (Finset.univ : Finset (Fin (d + 1)))
      (fun j => ‖iteratedFDeriv ℝ ((p : Multiset (Fin (d + 1))).count j) (fac j) x‖)
      (Finset.mem_univ j₀)).symm, ← mul_assoc]
    exact mul_le_mul
      ((hC_dec j₀ ((p : Multiset (Fin (d + 1))).count j₀)).2 x)
      (Finset.prod_le_prod (fun j _ => norm_nonneg _)
        (fun j _ => (hM j ((p : Multiset (Fin (d + 1))).count j)).2 x))
      (Finset.prod_nonneg fun j _ => norm_nonneg _)
      ((hC_dec j₀ ((p : Multiset (Fin (d + 1))).count j₀)).1)
  -- For each partition p, bound ‖x‖^k * ∏ ‖D^{count j} fac_j x‖
  -- by distributing the norm power via h_norm_pow_le and summing over active coordinates.
  have h_full : ∀ (x : EuclideanSpace ℝ (Fin (d + 1)))
      (p : Sym (Fin (d + 1)) n),
      ‖x‖ ^ k *
        ∏ j ∈ (Finset.univ : Finset (Fin (d + 1))),
          ‖iteratedFDeriv ℝ ((p : Multiset (Fin (d + 1))).count j) (fac j) x‖ ≤
        (d + 1 : ℝ) ^ k *
          ∑ j₀ : Fin (d + 1),
            C_dec j₀ ((p : Multiset (Fin (d + 1))).count j₀) *
              ∏ j ∈ (Finset.univ : Finset (Fin (d + 1))).erase j₀,
                M j ((p : Multiset (Fin (d + 1))).count j) := by
    intro x p
    calc ‖x‖ ^ k *
          ∏ j ∈ (Finset.univ : Finset (Fin (d + 1))),
            ‖iteratedFDeriv ℝ ((p : Multiset (Fin (d + 1))).count j) (fac j) x‖
        ≤ ((d + 1 : ℝ) ^ k * ∑ j₀ : Fin (d + 1), |x j₀| ^ k) *
            ∏ j ∈ (Finset.univ : Finset (Fin (d + 1))),
              ‖iteratedFDeriv ℝ ((p : Multiset (Fin (d + 1))).count j) (fac j) x‖ :=
          mul_le_mul_of_nonneg_right (h_norm_pow_le x)
            (Finset.prod_nonneg fun j _ => norm_nonneg _)
      _ = (d + 1 : ℝ) ^ k *
            ∑ j₀ : Fin (d + 1), |x j₀| ^ k *
              ∏ j ∈ (Finset.univ : Finset (Fin (d + 1))),
                ‖iteratedFDeriv ℝ ((p : Multiset (Fin (d + 1))).count j) (fac j) x‖ := by
          rw [mul_assoc, Finset.sum_mul]
      _ ≤ (d + 1 : ℝ) ^ k *
            ∑ j₀ : Fin (d + 1),
              C_dec j₀ ((p : Multiset (Fin (d + 1))).count j₀) *
                ∏ j ∈ (Finset.univ : Finset (Fin (d + 1))).erase j₀,
                  M j ((p : Multiset (Fin (d + 1))).count j) := by
          apply mul_le_mul_of_nonneg_left
          · exact Finset.sum_le_sum fun j₀ _ => h_term x j₀ p
          · positivity
  -- Define total bound and prove it
  refine ⟨∑ p ∈ (Finset.univ : Finset (Fin (d + 1))).sym n,
      (p : Multiset (Fin (d + 1))).countPerms *
        ((d + 1 : ℝ) ^ k *
          ∑ j₀ : Fin (d + 1),
            C_dec j₀ ((p : Multiset (Fin (d + 1))).count j₀) *
              ∏ j ∈ (Finset.univ : Finset (Fin (d + 1))).erase j₀,
                M j ((p : Multiset (Fin (d + 1))).count j)),
    fun x => ?_⟩
  rw [hprod_eq' x]
  calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun z => ∏ j : Fin (d + 1), fac j z) x‖
      -- Step 1: Apply multinomial Leibniz bound
      ≤ ‖x‖ ^ k *
          ∑ p ∈ (Finset.univ : Finset (Fin (d + 1))).sym n,
            (p : Multiset (Fin (d + 1))).countPerms *
              ∏ j ∈ (Finset.univ : Finset (Fin (d + 1))),
                ‖iteratedFDeriv ℝ ((p : Multiset (Fin (d + 1))).count j) (fac j) x‖ :=
        mul_le_mul_of_nonneg_left (hprod_bound x) (pow_nonneg (norm_nonneg _) _)
    -- Step 2: Distribute ‖x‖^k and apply coordinate-wise bounds
    _ ≤ ∑ p ∈ (Finset.univ : Finset (Fin (d + 1))).sym n,
          (p : Multiset (Fin (d + 1))).countPerms *
            ((d + 1 : ℝ) ^ k *
              ∑ j₀ : Fin (d + 1),
                C_dec j₀ ((p : Multiset (Fin (d + 1))).count j₀) *
                  ∏ j ∈ (Finset.univ : Finset (Fin (d + 1))).erase j₀,
                    M j ((p : Multiset (Fin (d + 1))).count j)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro p _
        rw [mul_left_comm (‖x‖ ^ k)]
        exact mul_le_mul_of_nonneg_left (h_full x p) (by positivity)

/-- The multidimensional Hermite function as a Schwartz map. -/
noncomputable def schwartzHermiteBasisNd (d : ℕ) (α : MultiIndex d) :
    SchwartzMap (EuclideanSpace ℝ (Fin d)) ℝ where
  toFun := hermiteFunctionNd d α
  smooth' := hermiteFunctionNd_contDiff d α
  decay' := hermiteFunctionNd_decay d α

/-- The coefficient of a Schwartz function against a multidimensional Hermite function. -/
noncomputable def hermiteCoeffNd (d : ℕ) (α : MultiIndex d)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℝ) : ℝ :=
  ∫ x, f x * hermiteFunctionNd d α x

/-- For `d = 1`, the multi-dimensional Hermite coefficient reduces to the 1D coefficient
transferred through `euclideanFin1Equiv`. Uses `euclideanFin1MeasEquiv` for the
measure-preserving change of variables.
-/
lemma hermiteCoeffNd_eq_hermiteCoeff1D
    (f : SchwartzMap (EuclideanSpace ℝ (Fin 1)) ℝ) (n : ℕ) :
    hermiteCoeffNd 1 (fun _ : Fin 1 => n) f =
    hermiteCoeff1D n ((schwartzDomCongr euclideanFin1Equiv).symm f) := by
  unfold hermiteCoeffNd hermiteCoeff1D hermiteFunctionNd
  simp only [Fin.prod_univ_one]
  symm
  rw [← euclideanFin1MeasEquiv_mp.integral_comp']
  congr 1; ext x
  simp only [euclideanFin1MeasEquiv_apply]
  congr 1
  change f (euclideanFin1Equiv.symm (x 0)) = f x
  congr 1; simp only [Fin.isValue]; ext i; fin_cases i; rfl

/-! ### Analytical Axioms for Multi-Dimensional Hermite Analysis

The definitions `schwartzSlice`, `schwartzPartialHermiteCoeff`,
`euclideanSnoc`, `euclideanInit` and associated lemmas live in
`SchwartzSlicing.lean` (imported above).

The remaining axioms are:

**A3a. Fubini factorization** (`hermiteCoeffNd_fubini`) — needs `hermiteCoeffNd`

**A4. Seminorm control of partial coefficients**
(`schwartz_partial_hermiteCoeff_seminorm_bound`): 1D-type seminorms of the
partial Hermite coefficient (as a Schwartz function of d+1 variables) are
controlled by finitely many (d+2)-variable Schwartz seminorms. Combined with
1D decay and Fubini, this gives multi-dimensional decay by induction.
-/

private lemma schwartz_mul_hermiteBasisNd_integrable (d : ℕ)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℝ) (α : MultiIndex d) :
    Integrable (fun x => f x * hermiteFunctionNd d α x) :=
  (f.memLp 2 volume).integrable_mul ((schwartzHermiteBasisNd d α).memLp 2 volume)

/-! ### Explicit Fubini Slicing Proof for Axiom A3a -/

/-- Helper: `euclideanSnoc` on castSucc evaluates to the base vector `y`. -/
private lemma euclideanSnoc_castSucc (d : ℕ) (y : EuclideanSpace ℝ (Fin d)) (t : ℝ) (i : Fin d) :
    euclideanSnoc d y t (Fin.castSucc i) = y i := by
  unfold euclideanSnoc
  simp [Fin.snoc_castSucc]

/-- Helper: `euclideanSnoc` on the last coordinate evaluates to `t`. -/
private lemma euclideanSnoc_last (d : ℕ) (y : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    euclideanSnoc d y t (Fin.last d) = t := by
  unfold euclideanSnoc
  simp [Fin.snoc_last]

/-- The multi-dimensional Hermite function splits algebraically under `snoc`. -/
private lemma hermiteFunctionNd_snoc (d : ℕ) (α : MultiIndex (d + 2))
    (y : EuclideanSpace ℝ (Fin (d + 1))) (t : ℝ) :
    hermiteFunctionNd (d + 2) α (euclideanSnoc (d + 1) y t) =
    hermiteFunctionNd (d + 1) (fun i => α (Fin.castSucc i)) y *
    hermiteFunction (α (Fin.last (d + 1))) t := by
  unfold hermiteFunctionNd
  rw [Fin.prod_univ_castSucc]
  congr 1
  · apply Finset.prod_congr rfl
    intro i _
    rw [euclideanSnoc_castSucc]
  · rw [euclideanSnoc_last]

-- A3a: Fubini factorization of multi-dimensional Hermite coefficients
/-- `c_α(f) = c_{α_rest}(partial_coeff_{α_last} f)` by Fubini. -/
private lemma hermiteCoeffNd_fubini (d : ℕ)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin (d + 2))) ℝ)
    (α : MultiIndex (d + 2)) :
    hermiteCoeffNd (d + 2) α f =
      hermiteCoeffNd (d + 1) (fun i => α (Fin.castSucc i))
        (schwartzPartialHermiteCoeff d f (α (Fin.last (d + 1)))) := by
  unfold hermiteCoeffNd
  rw [integral_euclidean_snoc d _ (schwartz_mul_hermiteBasisNd_integrable (d + 2) f α)]
  congr 1
  ext y
  rw [schwartz_partial_hermiteCoeff_eq_1D]
  unfold hermiteCoeff1D
  have h_factor : ∀ t, f (euclideanSnoc (d + 1) y t) * hermiteFunctionNd (d + 2) α (euclideanSnoc
    (d + 1) y t) =
      (f (euclideanSnoc (d + 1) y t) * hermiteFunction (α (Fin.last (d + 1))) t) *
      hermiteFunctionNd (d + 1) (fun i => α (Fin.castSucc i)) y := by
    intro t
    rw [hermiteFunctionNd_snoc]
    ring
  simp_rw [h_factor]
  -- Pull constant factor out of the integral: ∫ t, g(t) * C = (∫ t, g(t)) * C
  have h_pull := @integral_smul_const ℝ ℝ _ volume _ _ ℝ _ _ _
    (fun t => f (euclideanSnoc (d + 1) y t) * hermiteFunction (α (Fin.last (d + 1))) t)
    (hermiteFunctionNd (d + 1) (fun i => α (Fin.castSucc i)) y)
  simp only [smul_eq_mul] at h_pull
  rw [h_pull]
  congr 1

-- Seminorm control of partial Hermite coefficients with 1D decay (was axiom A4).
-- Each Schwartz seminorm of schwartzPartialHermiteCoeff d f n (as a function of d+1
-- variables) decays rapidly in n: multiplied by (1+n)^k for any k, it is controlled
-- by finitely many (d+2)-variable Schwartz seminorms of f.
--
-- Proved by "scalarization": evaluate the multilinear map D^{l'}_y[g_n] along arbitrary
-- vectors v, reducing to a 1D problem solvable by `hermiteCoeff1D_decay`.
private lemma schwartz_partial_hermiteCoeff_seminorm_bound (d : ℕ) (k' l' : ℕ) (k : ℝ) :
    ∃ (C : ℝ) (q' : Finset (ℕ × ℕ)), 0 < C ∧
      ∀ (f : SchwartzMap (EuclideanSpace ℝ (Fin (d + 2))) ℝ) (n : ℕ),
        SchwartzMap.seminorm ℝ k' l'
          (schwartzPartialHermiteCoeff d f n) * (1 + (n : ℝ)) ^ k ≤
          C * q'.sup (schwartzSeminormFamily ℝ (EuclideanSpace ℝ (Fin (d + 2))) ℝ) f := by
  -- Step 1: Get 1D Hermite coefficient decay bound
  obtain ⟨C₁, q₁_raw, hC₁, h1decay⟩ := hermiteCoeff1D_decay k
  set q₁ := Finset.Iic q₁_raw with hq₁_def
  have hne : q₁.Nonempty := ⟨⊥, Finset.mem_Iic.mpr bot_le⟩
  -- Step 2: For each 1D seminorm index, get the slice partial bound
  have h_single : ∀ idx : ℕ × ℕ, ∃ (C_i : ℝ) (q_i : Finset (ℕ × ℕ)), 0 < C_i ∧
      ∀ (f : SchwartzMap (EuclideanSpace ℝ (Fin (d + 2))) ℝ)
        (y : EuclideanSpace ℝ (Fin (d + 1)))
        (v : Fin l' → EuclideanSpace ℝ (Fin (d + 1))),
        ‖y‖ ^ k' * schwartzSeminormFamily ℝ ℝ ℝ idx
          (schwartzSlicePartial d f l' y v) ≤
          C_i * (∏ i, ‖v i‖) *
            q_i.sup (schwartzSeminormFamily ℝ (EuclideanSpace ℝ (Fin (d + 2))) ℝ) f := by
    intro ⟨a, b⟩
    exact schwartz_slice_partial_seminorm_bound d k' l' a b
  choose C_fn q_fn hC_pos h_bnd using h_single
  -- Step 3: Take maximum constants over the finite set q₁
  set C_max := q₁.sup' hne C_fn
  set q₂ := q₁.biUnion q_fn
  set C₂ := C₁ * C_max
  have hC_max_pos : 0 < C_max :=
    lt_of_lt_of_le (hC_pos hne.choose) (Finset.le_sup' C_fn hne.choose_spec)
  have hC₂_pos : 0 < C₂ := mul_pos hC₁ hC_max_pos
  refine ⟨C₂, q₂, hC₂_pos, fun f n => ?_⟩
  set g := schwartzPartialHermiteCoeff d f n
  set S_f := q₂.sup (schwartzSeminormFamily ℝ (EuclideanSpace ℝ (Fin (d + 2))) ℝ) f
  have hSf_nonneg : 0 ≤ S_f := apply_nonneg _ _
  have hc : 0 < (1 + (n : ℝ)) ^ k := by positivity
  -- Reduce to: seminorm ≤ C₂ * S_f / (1+n)^k
  rw [← le_div_iff₀ hc]
  -- Reduce Schwartz seminorm to pointwise bound
  apply SchwartzMap.seminorm_le_bound ℝ k' l' _
    (div_nonneg (mul_nonneg hC₂_pos.le hSf_nonneg) hc.le)
  intro y
  -- Need: ‖y‖^k' * ‖iteratedFDeriv ℝ l' g y‖ ≤ C₂ * S_f / (1+n)^k
  set c := ‖y‖ ^ k'
  have hc_nonneg : 0 ≤ c := by positivity
  -- Reduce via operator norm: ‖D^l' g(y)‖ ≤ bound / c (when c > 0)
  -- We bound c * ‖D^l' g(y)‖ directly using the multilinear op-norm
  change c * ‖iteratedFDeriv ℝ l' g y‖ ≤ C₂ * S_f / (1 + (n : ℝ)) ^ k
  rw [le_div_iff₀ hc]
  -- Need: c * ‖D^l' g(y)‖ * (1+n)^k ≤ C₂ * S_f
  -- Use op-norm: ‖f‖ ≤ B iff ∀ v, ‖f v‖ ≤ B * ∏ ‖vᵢ‖
  -- Apply to c • D^l' g(y) to absorb the c factor
  have hrw : c * ‖iteratedFDeriv ℝ l' g y‖ * (1 + (n : ℝ)) ^ k =
      ‖c • iteratedFDeriv ℝ l' g y‖ * (1 + (n : ℝ)) ^ k := by
    rw [norm_smul, Real.norm_of_nonneg hc_nonneg]
  rw [hrw]
  -- Bound ‖c • D^l' g(y)‖ ≤ C₂ * S_f / (1+n)^k via op-norm
  have h_op : ‖c • iteratedFDeriv ℝ l' g y‖ ≤ C₂ * S_f / (1 + (n : ℝ)) ^ k := by
    apply ContinuousMultilinearMap.opNorm_le_bound
      (div_nonneg (mul_nonneg hC₂_pos.le hSf_nonneg) hc.le)
    intro v
    rw [div_mul_eq_mul_div, le_div_iff₀ hc]
    -- Evaluate: (c • D^l' g(y)) v = c * (D^l' g(y) v)
    have heval : ‖(c • iteratedFDeriv ℝ l' g y) v‖ =
        c * ‖iteratedFDeriv ℝ l' g y v‖ := by
      rw [ContinuousMultilinearMap.smul_apply, norm_smul, Real.norm_of_nonneg hc_nonneg]
    rw [heval]
    -- Connect to 1D via schwartz_partial_hermiteCoeff_iteratedFDeriv
    have h_comm := schwartz_partial_hermiteCoeff_iteratedFDeriv d f n l' y v
    rw [h_comm]
    set slice := schwartzSlicePartial d f l' y v
    -- Apply 1D decay bound
    have h_decay := h1decay slice n
    -- Chain: c * |hermiteCoeff1D n slice| * (1+n)^k
    --   ≤ c * (C₁ * sup-seminorm(slice))
    --   ≤ C₁ * C_max * (∏ ‖vᵢ‖) * S_f
    calc c * ‖hermiteCoeff1D n slice‖ * (1 + (n : ℝ)) ^ k
        = c * (|hermiteCoeff1D n slice| * (1 + (n : ℝ)) ^ k) := by
          rw [Real.norm_eq_abs]; ring
      _ ≤ c * (C₁ * q₁.sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) slice) :=
          mul_le_mul_of_nonneg_left h_decay hc_nonneg
      _ = C₁ * (c * q₁.sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) slice) := by ring
      _ ≤ C₁ * (C_max * (∏ i, ‖v i‖) * S_f) := by
          apply mul_le_mul_of_nonneg_left _ hC₁.le
          -- Bound c * sup-seminorm(slice) ≤ C_max * (∏ ‖vᵢ‖) * S_f
          -- by bounding each seminorm individually via h_bnd
          rcases eq_or_ne c 0 with hc0 | hcne
          · rw [hc0, zero_mul]
            exact mul_nonneg (mul_nonneg hC_max_pos.le
              (Finset.prod_nonneg fun _ _ => norm_nonneg _)) hSf_nonneg
          · have hc_pos : 0 < c := lt_of_le_of_ne hc_nonneg hcne.symm
            rw [← le_div_iff₀' hc_pos]
            apply Seminorm.finset_sup_apply_le
              (div_nonneg (mul_nonneg (mul_nonneg hC_max_pos.le
                (Finset.prod_nonneg fun _ _ => norm_nonneg _)) hSf_nonneg) hc_pos.le)
            intro idx hidx
            rw [le_div_iff₀' hc_pos]
            calc c * (fun m => SchwartzMap.seminorm ℝ m.1 m.2) idx slice
                = c * schwartzSeminormFamily ℝ ℝ ℝ idx slice := rfl
              _ ≤ C_fn idx * (∏ i, ‖v i‖) *
                  (q_fn idx).sup (schwartzSeminormFamily ℝ _ ℝ) f :=
                h_bnd idx f y v
              _ ≤ C_max * (∏ i, ‖v i‖) *
                  (q_fn idx).sup (schwartzSeminormFamily ℝ _ ℝ) f := by
                  apply mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_right (Finset.le_sup' C_fn hidx)
                      (Finset.prod_nonneg fun _ _ => norm_nonneg _))
                    (apply_nonneg _ _)
              _ ≤ C_max * (∏ i, ‖v i‖) * S_f := by
                  apply mul_le_mul_of_nonneg_left
                  · exact (Finset.sup_mono
                      (f := schwartzSeminormFamily ℝ (EuclideanSpace ℝ (Fin (d + 2))) ℝ)
                      (Finset.subset_biUnion_of_mem q_fn hidx)) f
                  · exact mul_nonneg hC_max_pos.le
                      (Finset.prod_nonneg fun _ _ => norm_nonneg _)
      _ = C₁ * C_max * S_f * ∏ i, ‖v i‖ := by ring
      _ = C₂ * S_f * ∏ i, ‖v i‖ := rfl
  calc ‖c • iteratedFDeriv ℝ l' g y‖ * (1 + (n : ℝ)) ^ k
      ≤ (C₂ * S_f / (1 + (n : ℝ)) ^ k) * (1 + (n : ℝ)) ^ k :=
        mul_le_mul_of_nonneg_right h_op hc.le
    _ = C₂ * S_f := div_mul_cancel₀ _ hc.ne.symm

/-- Packages `schwartz_partial_hermiteCoeff_seminorm_bound` for `schwartzSeminormFamily`-indexed
seminorms over a finite set `q`, with `(1+n)^k` decay.
-/
private lemma schwartz_partial_hermiteCoeff_seminorm_bound'
    (d : ℕ) (q : Finset (ℕ × ℕ)) (k : ℝ) :
    ∃ (C : ℝ) (q' : Finset (ℕ × ℕ)), 0 < C ∧
      ∀ (f : SchwartzMap (EuclideanSpace ℝ (Fin (d + 2))) ℝ) (n : ℕ),
        q.sup (schwartzSeminormFamily ℝ (EuclideanSpace ℝ (Fin (d + 1))) ℝ)
          (schwartzPartialHermiteCoeff d f n) * (1 + (n : ℝ)) ^ k ≤
          C * q'.sup (schwartzSeminormFamily ℝ (EuclideanSpace ℝ (Fin (d + 2))) ℝ) f := by
  by_cases hq : q = ∅
  · exact ⟨1, ∅, one_pos, fun f n => by simp [hq, zero_mul]⟩
  · -- For each idx ∈ q, apply the axiom to get a per-seminorm bound
    have h_single : ∀ idx : ℕ × ℕ, ∃ (C : ℝ) (q' : Finset (ℕ × ℕ)), 0 < C ∧
        ∀ (f : SchwartzMap (EuclideanSpace ℝ (Fin (d + 2))) ℝ) (n : ℕ),
          schwartzSeminormFamily ℝ (EuclideanSpace ℝ (Fin (d + 1))) ℝ idx
            (schwartzPartialHermiteCoeff d f n) * (1 + (n : ℝ)) ^ k ≤
            C * q'.sup (schwartzSeminormFamily ℝ (EuclideanSpace ℝ (Fin (d + 2))) ℝ) f := by
      intro ⟨k', l'⟩
      exact schwartz_partial_hermiteCoeff_seminorm_bound d k' l' k
    choose C_fn q'_fn hC_pos h_bnd using h_single
    have hne := Finset.nonempty_of_ne_empty hq
    have hCM : 0 < q.sup' hne C_fn :=
      lt_of_lt_of_le (hC_pos hne.choose) (Finset.le_sup' C_fn hne.choose_spec)
    refine ⟨q.sup' hne C_fn, q.biUnion q'_fn, hCM, fun f n => ?_⟩
    -- Strategy: bound sup(p_i)(g_n) via bound on each p_i(g_n), then multiply by (1+n)^k
    set B := q.sup' hne C_fn * (q.biUnion q'_fn).sup
      (schwartzSeminormFamily ℝ (EuclideanSpace ℝ (Fin (d + 2))) ℝ) f
    have hc : (0 : ℝ) < (1 + (n : ℝ)) ^ k := by positivity
    -- Each p_i(g_n) ≤ B / (1+n)^k (by dividing the per-seminorm bound)
    have h_each : ∀ idx ∈ q,
        schwartzSeminormFamily ℝ (EuclideanSpace ℝ (Fin (d + 1))) ℝ idx
          (schwartzPartialHermiteCoeff d f n) ≤ B / (1 + (n : ℝ)) ^ k := by
      intro idx hidx
      rw [le_div_iff₀ hc]
      calc schwartzSeminormFamily ℝ (EuclideanSpace ℝ (Fin (d + 1))) ℝ idx
              (schwartzPartialHermiteCoeff d f n) * (1 + (n : ℝ)) ^ k
          ≤ C_fn idx * (q'_fn idx).sup
              (schwartzSeminormFamily ℝ (EuclideanSpace ℝ (Fin (d + 2))) ℝ) f :=
            h_bnd idx f n
        _ ≤ B := by
            apply mul_le_mul
            · exact Finset.le_sup' C_fn hidx
            · exact (Finset.sup_mono
                (f := schwartzSeminormFamily ℝ (EuclideanSpace ℝ (Fin (d + 2))) ℝ)
                (Finset.subset_biUnion_of_mem q'_fn hidx)) f
            · exact apply_nonneg _ _
            · exact hCM.le
    -- Take the sup, then multiply by (1+n)^k
    have h_sup := Seminorm.finset_sup_apply_le
      (div_nonneg (mul_nonneg hCM.le (apply_nonneg _ _)) hc.le) h_each
    calc q.sup (schwartzSeminormFamily ℝ (EuclideanSpace ℝ (Fin (d + 1))) ℝ)
            (schwartzPartialHermiteCoeff d f n) * (1 + (n : ℝ)) ^ k
        ≤ B / (1 + (n : ℝ)) ^ k * (1 + (n : ℝ)) ^ k :=
          mul_le_mul_of_nonneg_right h_sup hc.le
      _ = B := div_mul_cancel₀ B (ne_of_gt hc)

/-! ### Proofs from Analytical Lemmas

The following lemmas are proved from the analytical lemmas above
(Fubini slicing and seminorm control) together with 1D
decay (`hermiteCoeff1D_decay`), 1D completeness (`schwartz_hermite_hasSum`),
and standard Mathlib seminorm API.
-/

/-- Inductive step for injectivity: reduces d' + 2 to d' + 1.
Proved by Fubini: c_α(f) = ∫ c_{α_d}^{1D}(slice f x_{rest}) Ψ_{α_{rest}} dx_{rest}.
If all coefficients vanish, then for each fixed x_{rest}, all 1D coefficients of
the slice vanish → slice = 0 by 1D injectivity → by IH the function is zero.
-/
private lemma hermiteCoeffNd_injective_succ (d' : ℕ)
    (ih : ∀ f : SchwartzMap (EuclideanSpace ℝ (Fin (d' + 1))) ℝ,
      (∀ α : MultiIndex (d' + 1), hermiteCoeffNd (d' + 1) α f = 0) → f = 0)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin (d' + 2))) ℝ)
    (h : ∀ α : MultiIndex (d' + 2), hermiteCoeffNd (d' + 2) α f = 0) : f = 0 := by
  -- Step 1: Fubini shows all partial coefficients vanish
  have h_partial : ∀ n, schwartzPartialHermiteCoeff d' f n = 0 := by
    intro n
    apply ih
    intro β
    have := hermiteCoeffNd_fubini d' f (Fin.snoc β n)
    simp only [Fin.snoc_last] at this
    rw [h] at this
    convert this.symm using 1
    congr 1; funext i; simp [Fin.snoc_castSucc]
  -- Step 2: All 1D slices are zero (by 1D completeness)
  have h_slice : ∀ y, schwartzSlice d' f y = 0 := by
    intro y
    have h_coeff : ∀ n, hermiteCoeff1D n (schwartzSlice d' f y) = 0 := by
      intro n
      rw [← schwartz_partial_hermiteCoeff_eq_1D]
      exact congr_fun (congrArg SchwartzMap.toFun (h_partial n)) y
    have hs' := schwartz_hermite_hasSum (schwartzSlice d' f y)
    have heq : (fun n => hermiteCoeff1D n (schwartzSlice d' f y) •
        schwartzHermiteBasis1D n) = fun _ => 0 := by
      ext n; simp [h_coeff n]
    rw [heq] at hs'
    exact hs'.unique hasSum_zero
  -- Step 3: f is zero everywhere
  ext x
  have h_zero : ∀ y t, (schwartzSlice d' f y) t = 0 := by
    intro y t
    exact congr_fun (congrArg SchwartzMap.toFun (h_slice y)) t
  have h_val := h_zero (euclideanInit (d' + 1) x) (x (Fin.last (d' + 1)))
  rw [schwartz_slice_eq] at h_val
  convert h_val using 1
  congr 1
  exact (euclideanSnoc_init_last (d' + 1) x).symm

/-- If all multi-dimensional Hermite coefficients are zero, the Schwartz function is zero.
For `d = d' + 1 ≥ 1`, proved by induction on `d'`:
- **Base case** (`d' = 0`, i.e. d = 1): from 1D completeness (`schwartz_hermite_hasSum`)
  transferred through `euclideanFin1Equiv`.
- **Inductive step** (`d' + 1`, i.e. d = d'+2 from d'+1):
  `hermiteCoeffNd_injective_succ` via Fubini slicing.
-/
private lemma hermiteCoeffNd_injective (d' : ℕ)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin (d' + 1))) ℝ)
    (h : ∀ α : MultiIndex (d' + 1), hermiteCoeffNd (d' + 1) α f = 0) : f = 0 := by
  induction d' with
  | zero =>
    -- d = 1: transfer through euclideanFin1Equiv to use schwartz_hermite_hasSum
    let g := (schwartzDomCongr euclideanFin1Equiv).symm f
    have h_coeff : ∀ n : ℕ, hermiteCoeff1D n g = 0 := by
      intro n
      rw [← hermiteCoeffNd_eq_hermiteCoeff1D]
      exact h (fun _ => n)
    have hg : g = 0 := by
      have hs := schwartz_hermite_hasSum g
      have heq : (fun n => hermiteCoeff1D n g • schwartzHermiteBasis1D n) = fun _ => 0 := by
        ext n; simp [h_coeff n]
      rw [heq] at hs
      exact hs.unique hasSum_zero
    change (schwartzDomCongr euclideanFin1Equiv).symm f = 0 at hg
    exact (ContinuousLinearEquiv.injective _) (by rw [hg, map_zero])
  | succ d'' ih =>
    exact hermiteCoeffNd_injective_succ d''
      (fun g hg => ih g hg) f h

/-- Multidimensional Hermite coefficients decay rapidly (for `d = d' + 1 ≥ 1`).
This is the multivariate generalization of `hermiteCoeff1D_decay`.

Proved by induction on `d'`:
- **Base case** (`d' = 0`, i.e. d = 1): Transfer through `euclideanFin1Equiv` to use
  `hermiteCoeff1D_decay`, converting `Finset.Iic` seminorms to `schwartzSeminormFamily`.
- **Inductive step** (`d' = d'' + 1`, i.e. d = d''+2 from d''+1):
  For `k ≥ 0`: Factor `(1+|α|)^k ≤ (1+|α_rest|)^k · (1+n)^k`, apply IH for first factor
  and weighted axiom for second. For `k < 0`: directly use `(1+|α|)^k ≤ (1+|α_rest|)^k`
  since the base is ≥ 1 and the exponent is negative.
-/
private lemma hermiteCoeffNd_decay (d' : ℕ) (k : ℝ) :
    ∃ (C : ℝ) (q : Finset (ℕ × ℕ)), 0 < C ∧
      ∀ (f : SchwartzMap (EuclideanSpace ℝ (Fin (d' + 1))) ℝ)
        (α : MultiIndex (d' + 1)),
        |hermiteCoeffNd (d' + 1) α f| * (1 + (MultiIndex.abs α : ℝ)) ^ k ≤
          C * q.sup (schwartzSeminormFamily ℝ (EuclideanSpace ℝ (Fin (d' + 1))) ℝ) f := by
  induction d' with
  | zero =>
    -- d = 1: transfer through euclideanFin1Equiv to use hermiteCoeff1D_decay
    obtain ⟨C₁, q₁, hC₁, h1d⟩ := hermiteCoeff1D_decay k
    -- Get CLE seminorm bound: seminorms of g = T f are bounded by seminorms of f
    set T : SchwartzMap (EuclideanSpace ℝ (Fin 1)) ℝ →L[ℝ] SchwartzMap ℝ ℝ :=
      (schwartzDomCongr euclideanFin1Equiv).symm.toContinuousLinearMap with hT_def
    -- For each 1D seminorm, compose with T to get a continuous seminorm on the source space
    have hw_src := schwartz_withSeminorms ℝ (EuclideanSpace ℝ (Fin 1)) ℝ
    have h_per_idx : ∀ idx : ℕ × ℕ, ∃ (s : Finset (ℕ × ℕ)) (Ci : ℝ), 0 < Ci ∧
        ∀ f, SchwartzMap.seminorm ℝ idx.1 idx.2 (T f) ≤
          Ci * s.sup (schwartzSeminormFamily ℝ (EuclideanSpace ℝ (Fin 1)) ℝ) f := by
      intro ⟨k', l'⟩
      let p : Seminorm ℝ _ :=
        (SchwartzMap.seminorm ℝ k' l').comp T.toLinearMap
      have hp : Continuous p :=
        ((schwartz_withSeminorms ℝ ℝ ℝ).continuous_seminorm ⟨k', l'⟩).comp T.continuous
      obtain ⟨s, C, hCne, hle⟩ := Seminorm.bound_of_continuous hw_src p hp
      exact ⟨s, ↑C, by exact_mod_cast pos_iff_ne_zero.mpr hCne, fun f => by
        have := hle f; simp only [Seminorm.smul_apply] at this; exact this⟩
    -- Package the per-index bounds into a finset bound
    have h_clm : ∃ (C₂ : ℝ) (q₂ : Finset (ℕ × ℕ)), 0 < C₂ ∧
        ∀ f, (Finset.Iic q₁).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) (T f) ≤
          C₂ * q₂.sup (schwartzSeminormFamily ℝ (EuclideanSpace ℝ (Fin 1)) ℝ) f := by
      by_cases hq : (Finset.Iic q₁) = ∅
      · exact ⟨1, ∅, one_pos, fun f => by simp [hq]⟩
      · choose s_fn C_fn hC_pos h_bnd using h_per_idx
        have hne := Finset.nonempty_of_ne_empty hq
        have hCM : 0 < (Finset.Iic q₁).sup' hne (C_fn ·) :=
          lt_of_lt_of_le (hC_pos hne.choose) (Finset.le_sup' _ hne.choose_spec)
        refine ⟨(Finset.Iic q₁).sup' hne (C_fn ·),
               (Finset.Iic q₁).biUnion (s_fn ·), hCM, fun f => ?_⟩
        apply Seminorm.finset_sup_apply_le (mul_nonneg hCM.le (apply_nonneg _ _))
        intro idx hidx
        calc SchwartzMap.seminorm ℝ idx.1 idx.2 (T f)
            ≤ C_fn idx * (s_fn idx).sup
                (schwartzSeminormFamily ℝ (EuclideanSpace ℝ (Fin 1)) ℝ) f := h_bnd idx f
          _ ≤ (Finset.Iic q₁).sup' hne (C_fn ·) *
                ((Finset.Iic q₁).biUnion (s_fn ·)).sup
                  (schwartzSeminormFamily ℝ (EuclideanSpace ℝ (Fin 1)) ℝ) f := by
              apply mul_le_mul
              · exact Finset.le_sup' _ hidx
              · exact (Finset.sup_mono
                  (f := schwartzSeminormFamily ℝ (EuclideanSpace ℝ (Fin 1)) ℝ)
                  (Finset.subset_biUnion_of_mem (s_fn ·) hidx)) f
              · exact apply_nonneg _ _
              · exact hCM.le
    obtain ⟨C₂, q₂, hC₂, h_clm_bound⟩ := h_clm
    refine ⟨C₁ * C₂, q₂, mul_pos hC₁ hC₂, fun f α => ?_⟩
    have h_abs : MultiIndex.abs α = α 0 := by
      simp [MultiIndex.abs]
    rw [h_abs]
    set g := T f
    have h_coeff : hermiteCoeffNd 1 α f = hermiteCoeff1D (α 0) g := by
      have : α = fun _ => α 0 := by ext i; exact congr_arg α (Fin.eq_zero i)
      rw [this]
      exact hermiteCoeffNd_eq_hermiteCoeff1D f (α 0)
    rw [h_coeff]
    calc |hermiteCoeff1D (α 0) g| * (1 + (α 0 : ℝ)) ^ k
        ≤ C₁ * (Finset.Iic q₁).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) g := h1d g (α 0)
      _ ≤ C₁ * (C₂ * q₂.sup (schwartzSeminormFamily ℝ (EuclideanSpace ℝ (Fin 1)) ℝ) f) :=
          mul_le_mul_of_nonneg_left (h_clm_bound f) hC₁.le
      _ = (C₁ * C₂) * q₂.sup (schwartzSeminormFamily ℝ (EuclideanSpace ℝ (Fin 1)) ℝ) f := by
          ring
  | succ d'' ih =>
    -- Inductive step: d' = d'' + 1, dimension d = d'' + 2
    obtain ⟨C_ih, q_ih, hC_ih, h_ih⟩ := ih
    -- For k < 0: use (1+|α|)^k ≤ (1+|α_rest|)^k directly, then unweighted axiom
    -- For k ≥ 0: use (1+|α|)^k ≤ (1+|α_rest|)^k * (1+n)^k, then weighted axiom
    by_cases hk : k < 0
    · -- k < 0 case: use unweighted bound (axiom at k=0)
      obtain ⟨C_ax, q_ax, hC_ax, h_ax⟩ :=
        schwartz_partial_hermiteCoeff_seminorm_bound' d'' q_ih 0
      refine ⟨C_ih * C_ax, q_ax, mul_pos hC_ih hC_ax, fun f α => ?_⟩
      rw [hermiteCoeffNd_fubini d'' f α]
      set α_rest : MultiIndex (d'' + 1) := fun i => α (Fin.castSucc i)
      set n := α (Fin.last (d'' + 1))
      set g := schwartzPartialHermiteCoeff d'' f n
      -- |α| ≥ |α_rest|, and k < 0, so (1+|α|)^k ≤ (1+|α_rest|)^k
      have h_abs_rest_le : (MultiIndex.abs α_rest : ℝ) ≤ MultiIndex.abs α := by
        exact_mod_cast show MultiIndex.abs α_rest ≤ MultiIndex.abs α from by
          have : MultiIndex.abs α = MultiIndex.abs α_rest + n := by
            simp only [MultiIndex.abs, α_rest, n]; exact Fin.sum_univ_castSucc α
          omega
      have h1α : (1 : ℝ) ≤ 1 + (MultiIndex.abs α_rest : ℝ) :=
        le_add_of_nonneg_right (Nat.cast_nonneg _)
      have h_weight : (1 + (MultiIndex.abs α : ℝ)) ^ k ≤
          (1 + (MultiIndex.abs α_rest : ℝ)) ^ k := by
        apply rpow_le_rpow_of_nonpos (by linarith) (by linarith) hk.le
      -- Unweighted axiom at k=0 gives seminorm bound
      have h_ax0 := h_ax f n
      simp only [rpow_zero, mul_one] at h_ax0
      calc |hermiteCoeffNd (d'' + 1) α_rest g| *
              (1 + (MultiIndex.abs α : ℝ)) ^ k
          ≤ |hermiteCoeffNd (d'' + 1) α_rest g| *
              (1 + (MultiIndex.abs α_rest : ℝ)) ^ k :=
            mul_le_mul_of_nonneg_left h_weight (abs_nonneg _)
        _ ≤ C_ih * q_ih.sup (schwartzSeminormFamily ℝ
              (EuclideanSpace ℝ (Fin (d'' + 1))) ℝ) g := h_ih g α_rest
        _ ≤ C_ih * (C_ax * q_ax.sup (schwartzSeminormFamily ℝ
              (EuclideanSpace ℝ (Fin (d'' + 2))) ℝ) f) :=
            mul_le_mul_of_nonneg_left h_ax0 hC_ih.le
        _ = (C_ih * C_ax) * q_ax.sup (schwartzSeminormFamily ℝ
              (EuclideanSpace ℝ (Fin (d'' + 2))) ℝ) f := by ring
    · -- k ≥ 0 case: factor (1+|α|)^k ≤ (1+|α_rest|)^k * (1+n)^k
      push Not at hk
      obtain ⟨C_ax, q_ax, hC_ax, h_ax⟩ :=
        schwartz_partial_hermiteCoeff_seminorm_bound' d'' q_ih k
      refine ⟨C_ih * C_ax, q_ax, mul_pos hC_ih hC_ax, fun f α => ?_⟩
      rw [hermiteCoeffNd_fubini d'' f α]
      set α_rest : MultiIndex (d'' + 1) := fun i => α (Fin.castSucc i)
      set n := α (Fin.last (d'' + 1))
      set g := schwartzPartialHermiteCoeff d'' f n
      -- Key: |α| = |α_rest| + n, and (1+a+b)^k ≤ ((1+a)(1+b))^k for k ≥ 0
      have h_abs_eq : (MultiIndex.abs α : ℕ) =
          MultiIndex.abs α_rest + n := by
        simp only [MultiIndex.abs, α_rest, n]
        exact Fin.sum_univ_castSucc α
      have h_product_bound : (1 + (MultiIndex.abs α : ℝ)) ^ k ≤
          (1 + (MultiIndex.abs α_rest : ℝ)) ^ k * (1 + (n : ℝ)) ^ k := by
        rw [← mul_rpow (by positivity) (by positivity)]
        apply rpow_le_rpow (by positivity) _ hk
        calc (1 + (MultiIndex.abs α : ℝ))
            = 1 + (↑(MultiIndex.abs α_rest) + ↑n) := by push_cast [h_abs_eq]; ring
          _ ≤ (1 + ↑(MultiIndex.abs α_rest)) * (1 + ↑n) := by
              have : (1 + ↑(MultiIndex.abs α_rest)) * (1 + (↑n : ℝ)) =
                  1 + ↑(MultiIndex.abs α_rest) + ↑n + ↑(MultiIndex.abs α_rest) * ↑n := by ring
              linarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) (MultiIndex.abs α_rest))
                (Nat.cast_nonneg (α := ℝ) n)]
      calc |hermiteCoeffNd (d'' + 1) α_rest g| *
              (1 + (MultiIndex.abs α : ℝ)) ^ k
          ≤ |hermiteCoeffNd (d'' + 1) α_rest g| *
              ((1 + (MultiIndex.abs α_rest : ℝ)) ^ k * (1 + (n : ℝ)) ^ k) :=
            mul_le_mul_of_nonneg_left h_product_bound (abs_nonneg _)
        _ = (|hermiteCoeffNd (d'' + 1) α_rest g| *
              (1 + (MultiIndex.abs α_rest : ℝ)) ^ k) * (1 + (n : ℝ)) ^ k := by ring
        _ ≤ (C_ih * q_ih.sup (schwartzSeminormFamily ℝ
              (EuclideanSpace ℝ (Fin (d'' + 1))) ℝ) g) * (1 + (n : ℝ)) ^ k :=
            mul_le_mul_of_nonneg_right (h_ih g α_rest) (by positivity)
        _ = C_ih * (q_ih.sup (schwartzSeminormFamily ℝ
              (EuclideanSpace ℝ (Fin (d'' + 1))) ℝ) g * (1 + (n : ℝ)) ^ k) := by ring
        _ ≤ C_ih * (C_ax * q_ax.sup (schwartzSeminormFamily ℝ
              (EuclideanSpace ℝ (Fin (d'' + 2))) ℝ) f) :=
            mul_le_mul_of_nonneg_left (h_ax f n) hC_ih.le
        _ = (C_ih * C_ax) * q_ax.sup (schwartzSeminormFamily ℝ
              (EuclideanSpace ℝ (Fin (d'' + 2))) ℝ) f := by ring

private lemma schwartzHermiteBasisNd_weighted_product_bound (d k l : ℕ)
    (C₁ : ℝ) (s₁ : ℕ) (hC₁_pos : 0 < C₁)
    (fac : MultiIndex (d + 1) → Fin (d + 1) → EuclideanSpace ℝ (Fin (d + 1)) → ℝ)
    (hM_poly : ∀ (α : MultiIndex (d + 1)) (j : Fin (d + 1)) (m : ℕ) (_ : m ≤ l)
      (x : EuclideanSpace ℝ (Fin (d + 1))),
      ‖iteratedFDeriv ℝ m (fac α j) x‖ ≤ C₁ * (1 + (MultiIndex.abs α : ℝ)) ^ s₁)
    (hC_poly : ∀ (α : MultiIndex (d + 1)) (j : Fin (d + 1)) (m : ℕ) (_ : m ≤ l)
      (x : EuclideanSpace ℝ (Fin (d + 1))),
      |x j| ^ k * ‖iteratedFDeriv ℝ m (fac α j) x‖ ≤
        C₁ * (1 + (MultiIndex.abs α : ℝ)) ^ s₁) :
    ∀ (α : MultiIndex (d + 1)) (x : EuclideanSpace ℝ (Fin (d + 1)))
      (p : Sym (Fin (d + 1)) l),
      ‖x‖ ^ k *
        ∏ j ∈ (Finset.univ : Finset (Fin (d + 1))),
          ‖iteratedFDeriv ℝ ((p : Multiset (Fin (d + 1))).count j) (fac α j) x‖ ≤
        (d + 1 : ℝ) ^ (k + 1) *
          (C₁ * (1 + (MultiIndex.abs α : ℝ)) ^ s₁) ^ (d + 1) := by
  have h_count_le : ∀ (p : Sym (Fin (d + 1)) l) (j : Fin (d + 1)),
      (p : Multiset (Fin (d + 1))).count j ≤ l :=
    fun p j => (Multiset.count_le_card j ↑p).trans (le_of_eq p.prop)
  have h_l2_le_l1 : ∀ x : EuclideanSpace ℝ (Fin (d + 1)),
      ‖x‖ ≤ ∑ j : Fin (d + 1), |x j| := by
    intro x
    rw [EuclideanSpace.norm_eq]
    have hsq : ∑ j : Fin (d + 1), ‖x j‖ ^ 2 ≤
        (∑ j : Fin (d + 1), |x j|) ^ 2 := by
      convert Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
        (fun j _ => abs_nonneg (x j)) using 2
    calc √(∑ j, ‖x j‖ ^ 2) ≤ √((∑ j, |x j|) ^ 2) :=
          Real.sqrt_le_sqrt hsq
      _ = ∑ j, |x j| := by
          rw [Real.sqrt_sq_eq_abs, abs_of_nonneg
            (Finset.sum_nonneg (fun j _ => abs_nonneg _))]
  have h_norm_pow_le : ∀ x : EuclideanSpace ℝ (Fin (d + 1)),
      ‖x‖ ^ k ≤ ((d + 1 : ℝ) ^ k) * ∑ j : Fin (d + 1), |x j| ^ k := by
    intro x
    rcases k with _ | k_
    · simp only [pow_zero, one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_one]
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le d)
    have h1 : (1 : ℝ) ≤ (d + 1 : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le d)
    calc ‖x‖ ^ (k_ + 1) ≤ (∑ j : Fin (d + 1), |x j|) ^ (k_ + 1) :=
          pow_le_pow_left₀ (norm_nonneg _) (h_l2_le_l1 x) _
      _ ≤ ((Finset.univ : Finset (Fin (d + 1))).card : ℝ) ^ k_ *
            ∑ j ∈ Finset.univ, |x j| ^ (k_ + 1) :=
          _root_.pow_sum_le_card_mul_sum_pow (fun j _ => abs_nonneg (x j)) k_
      _ = (d + 1 : ℝ) ^ k_ * ∑ j : Fin (d + 1), |x j| ^ (k_ + 1) := by
          simp [Finset.card_univ, Fintype.card_fin]
      _ ≤ (d + 1 : ℝ) ^ (k_ + 1) * ∑ j : Fin (d + 1), |x j| ^ (k_ + 1) := by
          apply mul_le_mul_of_nonneg_right
          · exact pow_le_pow_right₀ h1 (Nat.le_succ k_)
          · exact Finset.sum_nonneg (fun j _ => pow_nonneg (abs_nonneg _) _)
  have h_term : ∀ (α : MultiIndex (d + 1)) (x : EuclideanSpace ℝ (Fin (d + 1)))
      (j₀ : Fin (d + 1)) (p : Sym (Fin (d + 1)) l),
      |x j₀| ^ k *
        ∏ j ∈ (Finset.univ : Finset (Fin (d + 1))),
          ‖iteratedFDeriv ℝ ((p : Multiset (Fin (d + 1))).count j) (fac α j) x‖ ≤
        (C₁ * (1 + (MultiIndex.abs α : ℝ)) ^ s₁) ^ (d + 1) := by
    intro α x j₀ p
    rw [(Finset.mul_prod_erase (Finset.univ : Finset (Fin (d + 1)))
      (fun j => ‖iteratedFDeriv ℝ ((p : Multiset (Fin (d + 1))).count j) (fac α j) x‖)
      (Finset.mem_univ j₀)).symm, ← mul_assoc]
    calc |x j₀| ^ k * ‖iteratedFDeriv ℝ ((p : Multiset (Fin (d + 1))).count j₀) (fac α j₀) x‖ *
          ∏ j ∈ (Finset.univ : Finset (Fin (d + 1))).erase j₀,
            ‖iteratedFDeriv ℝ ((p : Multiset (Fin (d + 1))).count j) (fac α j) x‖
        ≤ (C₁ * (1 + (MultiIndex.abs α : ℝ)) ^ s₁) *
            ∏ _j ∈ (Finset.univ : Finset (Fin (d + 1))).erase j₀,
              (C₁ * (1 + (MultiIndex.abs α : ℝ)) ^ s₁) := by
          apply mul_le_mul
          · exact hC_poly α j₀ _ (h_count_le p j₀) x
          · exact Finset.prod_le_prod (fun j _ => norm_nonneg _)
              (fun j _ => hM_poly α j _ (h_count_le p j) x)
          · exact Finset.prod_nonneg fun j _ => norm_nonneg _
          · positivity
      _ = (C₁ * (1 + (MultiIndex.abs α : ℝ)) ^ s₁) *
            (C₁ * (1 + (MultiIndex.abs α : ℝ)) ^ s₁) ^
              ((Finset.univ : Finset (Fin (d + 1))).erase j₀).card := by
          rw [Finset.prod_const]
      _ ≤ (C₁ * (1 + (MultiIndex.abs α : ℝ)) ^ s₁) ^ (d + 1) := by
          have hcard : ((Finset.univ : Finset (Fin (d + 1))).erase j₀).card = d := by
            rw [Finset.card_erase_of_mem (Finset.mem_univ j₀),
              Finset.card_univ, Fintype.card_fin]; omega
          rw [hcard, pow_succ']
  intro α x p
  calc ‖x‖ ^ k *
        ∏ j ∈ (Finset.univ : Finset (Fin (d + 1))),
          ‖iteratedFDeriv ℝ ((p : Multiset (Fin (d + 1))).count j) (fac α j) x‖
      ≤ ((d + 1 : ℝ) ^ k * ∑ j₀ : Fin (d + 1), |x j₀| ^ k) *
          ∏ j ∈ (Finset.univ : Finset (Fin (d + 1))),
            ‖iteratedFDeriv ℝ ((p : Multiset (Fin (d + 1))).count j) (fac α j) x‖ :=
        mul_le_mul_of_nonneg_right (h_norm_pow_le x)
          (Finset.prod_nonneg fun j _ => norm_nonneg _)
    _ = (d + 1 : ℝ) ^ k *
          ∑ j₀ : Fin (d + 1), |x j₀| ^ k *
            ∏ j ∈ (Finset.univ : Finset (Fin (d + 1))),
              ‖iteratedFDeriv ℝ ((p : Multiset (Fin (d + 1))).count j) (fac α j) x‖ := by
        rw [mul_assoc, Finset.sum_mul]
    _ ≤ (d + 1 : ℝ) ^ k *
          ∑ _j₀ : Fin (d + 1),
            (C₁ * (1 + (MultiIndex.abs α : ℝ)) ^ s₁) ^ (d + 1) := by
        apply mul_le_mul_of_nonneg_left
        · exact Finset.sum_le_sum fun j₀ _ => h_term α x j₀ p
        · positivity
    _ = (d + 1 : ℝ) ^ (k + 1) *
          (C₁ * (1 + (MultiIndex.abs α : ℝ)) ^ s₁) ^ (d + 1) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast; ring

/-- The multidimensional Hermite basis functions have polynomial growth in seminorms.

The proof tracks the α-dependence through the Leibniz expansion: each 1D factor
`ψ_{α_j}` has seminorm `≤ C * (1 + α_j)^s` from `schwartzHermiteBasis1D_growth`,
and `(1 + α_j) ≤ (1 + |α|)`, so the product bound grows polynomially in `|α|`.
-/
private lemma schwartzHermiteBasisNd_growth (d : ℕ) (k l : ℕ) :
    ∃ (C : ℝ) (_ : 0 < C) (s : ℕ), ∀ (α : MultiIndex d),
      SchwartzMap.seminorm ℝ k l (schwartzHermiteBasisNd d α) ≤
        C * (1 + (MultiIndex.abs α : ℝ)) ^ s := by
  -- Suffices to show a pointwise bound with polynomial α-dependence,
  -- then apply seminorm_le_bound.
  -- For d = 0: hermiteFunctionNd 0 α = fun _ => 1 (constant)
  rcases d with _ | d
  · refine ⟨1, one_pos, 0, fun α => ?_⟩
    simp only [pow_zero, mul_one]
    apply SchwartzMap.seminorm_le_bound ℝ k l _ zero_le_one
    intro x
    have hx : x = 0 := Subsingleton.eq_zero x; subst hx
    simp only [norm_zero]
    rcases k with _ | k'
    · simp only [pow_zero, one_mul]
      have hf : ⇑(schwartzHermiteBasisNd 0 α) =
          fun (_ : EuclideanSpace ℝ (Fin 0)) => (1 : ℝ) := by
        ext y; change hermiteFunctionNd 0 α y = 1; simp [hermiteFunctionNd]
      rw [hf]
      rcases l with _ | l'
      · simp
      · simp [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero l')]
    · simp [zero_pow (Nat.succ_ne_zero k'), zero_mul]
  -- d + 1 ≥ 1
  -- Step 1: Get uniform 1D growth bounds.
  -- For each (k', m'), schwartzHermiteBasis1D_growth gives C, s with
  --   seminorm(ψ_n, k', m') ≤ C * (1+n)^s
  -- We need this for k' ∈ {0, k} and m' ∈ {0, ..., l}.
  -- Take the max C and s over these finitely many pairs.
  choose C_0 hC_0_rest using fun m' => schwartzHermiteBasis1D_growth 0 m'
  choose s_0 hbound_0 using fun m' => (hC_0_rest m').2
  choose C_k hC_k_rest using fun m' => schwartzHermiteBasis1D_growth k m'
  choose s_k hbound_k using fun m' => (hC_k_rest m').2
  -- Max over m' ∈ {0, ..., l}
  set C₁ := (Finset.range (l + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ l)⟩
    (fun m' => max (C_0 m') (C_k m') + 1) with hC₁_def
  set s₁ := (Finset.range (l + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ l)⟩
    (fun m' => max (s_0 m') (s_k m')) with hs₁_def
  have hC₁_pos : 0 < C₁ := by
    have : 0 < max (C_0 0) (C_k 0) + 1 := by linarith [le_max_left (C_0 0) (C_k 0), (hC_0_rest 0).1]
    exact lt_of_lt_of_le this
      (Finset.le_sup' (fun m' => max (C_0 m') (C_k m') + 1)
        (Finset.mem_range.mpr (Nat.zero_lt_succ l)))
  have h_unif_0 : ∀ m' ≤ l, ∀ n : ℕ,
      SchwartzMap.seminorm ℝ 0 m' (schwartzHermiteBasis1D n) ≤
        C₁ * (1 + (n : ℝ)) ^ s₁ := by
    intro m' hm' n
    have hmem : m' ∈ Finset.range (l + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hm')
    have hC : C_0 m' ≤ C₁ :=
      le_trans (le_trans (le_max_left (C_0 m') (C_k m'))
        (le_add_of_nonneg_right zero_le_one))
        (Finset.le_sup' (fun m' => max (C_0 m') (C_k m') + 1) hmem)
    have hs : s_0 m' ≤ s₁ :=
      le_trans (le_max_left (s_0 m') (s_k m'))
        (Finset.le_sup' (fun m' => max (s_0 m') (s_k m')) hmem)
    calc SchwartzMap.seminorm ℝ 0 m' (schwartzHermiteBasis1D n)
        ≤ C_0 m' * (1 + (n : ℝ)) ^ s_0 m' := hbound_0 m' n
      _ ≤ C₁ * (1 + (n : ℝ)) ^ s₁ :=
          mul_le_mul hC (pow_le_pow_right₀ (le_add_of_nonneg_right (Nat.cast_nonneg n)) hs)
            (by positivity) hC₁_pos.le
  have h_unif_k : ∀ m' ≤ l, ∀ n : ℕ,
      SchwartzMap.seminorm ℝ k m' (schwartzHermiteBasis1D n) ≤
        C₁ * (1 + (n : ℝ)) ^ s₁ := by
    intro m' hm' n
    have hmem : m' ∈ Finset.range (l + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hm')
    have hC : C_k m' ≤ C₁ :=
      le_trans (le_trans (le_max_right (C_0 m') (C_k m'))
        (le_add_of_nonneg_right zero_le_one))
        (Finset.le_sup' (fun m' => max (C_0 m') (C_k m') + 1) hmem)
    have hs : s_k m' ≤ s₁ :=
      le_trans (le_max_right (s_0 m') (s_k m'))
        (Finset.le_sup' (fun m' => max (s_0 m') (s_k m')) hmem)
    calc SchwartzMap.seminorm ℝ k m' (schwartzHermiteBasis1D n)
        ≤ C_k m' * (1 + (n : ℝ)) ^ s_k m' := hbound_k m' n
      _ ≤ C₁ * (1 + (n : ℝ)) ^ s₁ :=
          mul_le_mul hC (pow_le_pow_right₀ (le_add_of_nonneg_right (Nat.cast_nonneg n)) hs)
            (by positivity) hC₁_pos.le
  -- α-tracking: (1 + α j) ≤ (1 + |α|) for each j
  have h_alpha_le : ∀ (α : MultiIndex (d + 1)) (j : Fin (d + 1)),
      (1 + (α j : ℝ)) ≤ (1 + (MultiIndex.abs α : ℝ)) := by
    intro α j; gcongr; change α j ≤ ∑ i, α i
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  -- Reduce to pointwise bound
  suffices h_poly : ∃ (C : ℝ) (s : ℕ), 0 < C ∧
      ∀ (α : MultiIndex (d + 1)) (x : EuclideanSpace ℝ (Fin (d + 1))),
        ‖x‖ ^ k * ‖iteratedFDeriv ℝ l (hermiteFunctionNd (d + 1) α) x‖ ≤
          C * (1 + (MultiIndex.abs α : ℝ)) ^ s by
    obtain ⟨C, s, hC, hbound⟩ := h_poly
    exact ⟨C, hC, s, fun α =>
      SchwartzMap.seminorm_le_bound ℝ k l (schwartzHermiteBasisNd (d + 1) α) (by positivity)
        (hbound α)⟩
  -- Step 2: Factor bounds with α-tracking
  -- Using le_seminorm and composition with projection (as in
  -- iteratedFDeriv_hermite_comp_proj_bound):
  -- ‖D^m (fun x => ψ_n(x j)) x‖ ≤ ‖D^m ψ_n (x j)‖ ≤ seminorm(ψ_n, 0, m)
  -- |x j|^k * ‖D^m (fun x => ψ_n(x j)) x‖ ≤ |x j|^k * ‖D^m ψ_n (x j)‖ ≤ seminorm(ψ_n, k, m)
  set fac : MultiIndex (d + 1) → Fin (d + 1) → EuclideanSpace ℝ (Fin (d + 1)) → ℝ :=
    fun α j x => hermiteFunction (α j) (x j)
  have hfac_smooth : ∀ α j, ContDiff ℝ ∞ (fac α j) := fun α j =>
    contDiff_infty.mpr (hermiteFunctionNd_factor_contDiff (d + 1) α j)
  -- Factor bound (k'=0): ‖D^m (fac α j) x‖ ≤ C₁ * (1+|α|)^s₁
  -- Chain: comp_proj_le → le_seminorm (k=0) → h_unif_0 → h_alpha_le
  have hM_poly : ∀ (α : MultiIndex (d + 1)) (j : Fin (d + 1)) (m : ℕ) (_ : m ≤ l)
      (x : EuclideanSpace ℝ (Fin (d + 1))),
      ‖iteratedFDeriv ℝ m (fac α j) x‖ ≤ C₁ * (1 + (MultiIndex.abs α : ℝ)) ^ s₁ := by
    intro α j m hm x
    have h_le_sem : ‖iteratedFDeriv ℝ m (hermiteFunction (α j)) (x j)‖ ≤
        SchwartzMap.seminorm ℝ 0 m (schwartzHermiteBasis1D (α j)) := by
      have h := SchwartzMap.le_seminorm ℝ 0 m (schwartzHermiteBasis1D (α j)) (x j)
      simp only [pow_zero, one_mul] at h
      rwa [show iteratedFDeriv ℝ m (⇑(schwartzHermiteBasis1D (α j))) (x j) =
        iteratedFDeriv ℝ m (hermiteFunction (α j)) (x j) from
        congr_arg (iteratedFDeriv ℝ m · (x j)) (schwartzHermiteBasis1D_coe (α j))] at h
    calc ‖iteratedFDeriv ℝ m (fac α j) x‖
        ≤ ‖iteratedFDeriv ℝ m (hermiteFunction (α j)) (x j)‖ :=
          norm_iteratedFDeriv_hermite_comp_proj_le (d + 1) (α j) j m x
      _ ≤ SchwartzMap.seminorm ℝ 0 m (schwartzHermiteBasis1D (α j)) := h_le_sem
      _ ≤ C₁ * (1 + (α j : ℝ)) ^ s₁ := h_unif_0 m hm (α j)
      _ ≤ C₁ * (1 + (MultiIndex.abs α : ℝ)) ^ s₁ :=
          mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (by positivity) (h_alpha_le α j) s₁) hC₁_pos.le
  -- Factor bound (k'=k): |x j|^k * ‖D^m (fac α j) x‖ ≤ C₁ * (1+|α|)^s₁
  have hC_poly : ∀ (α : MultiIndex (d + 1)) (j : Fin (d + 1)) (m : ℕ) (_ : m ≤ l)
      (x : EuclideanSpace ℝ (Fin (d + 1))),
      |x j| ^ k * ‖iteratedFDeriv ℝ m (fac α j) x‖ ≤
        C₁ * (1 + (MultiIndex.abs α : ℝ)) ^ s₁ := by
    intro α j m hm x
    have h_le_sem : |x j| ^ k * ‖iteratedFDeriv ℝ m (hermiteFunction (α j)) (x j)‖ ≤
        SchwartzMap.seminorm ℝ k m (schwartzHermiteBasis1D (α j)) := by
      have h := SchwartzMap.le_seminorm ℝ k m (schwartzHermiteBasis1D (α j)) (x j)
      rw [Real.norm_eq_abs] at h
      rwa [show iteratedFDeriv ℝ m (⇑(schwartzHermiteBasis1D (α j))) (x j) =
        iteratedFDeriv ℝ m (hermiteFunction (α j)) (x j) from
        congr_arg (iteratedFDeriv ℝ m · (x j)) (schwartzHermiteBasis1D_coe (α j))] at h
    calc |x j| ^ k * ‖iteratedFDeriv ℝ m (fac α j) x‖
        ≤ |x j| ^ k * ‖iteratedFDeriv ℝ m (hermiteFunction (α j)) (x j)‖ :=
          mul_le_mul_of_nonneg_left
            (norm_iteratedFDeriv_hermite_comp_proj_le (d + 1) (α j) j m x)
            (pow_nonneg (abs_nonneg _) _)
      _ ≤ SchwartzMap.seminorm ℝ k m (schwartzHermiteBasis1D (α j)) := h_le_sem
      _ ≤ C₁ * (1 + (α j : ℝ)) ^ s₁ := h_unif_k m hm (α j)
      _ ≤ C₁ * (1 + (MultiIndex.abs α : ℝ)) ^ s₁ :=
          mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (by positivity) (h_alpha_le α j) s₁) hC₁_pos.le
  -- Step C: Product equation
  have hprod_eq : ∀ (α : MultiIndex (d + 1)),
      (fun x => ∏ j : Fin (d + 1), fac α j x) = hermiteFunctionNd (d + 1) α := by
    intro α; ext x; simp [hermiteFunctionNd, fac]
  -- Step D: Leibniz bound
  have hprod_bound : ∀ (α : MultiIndex (d + 1)) (y : EuclideanSpace ℝ (Fin (d + 1))),
      ‖iteratedFDeriv ℝ l (fun z => ∏ j : Fin (d + 1), fac α j z) y‖ ≤
      ∑ p ∈ (Finset.univ : Finset (Fin (d + 1))).sym l,
        (p : Multiset (Fin (d + 1))).countPerms *
          ∏ j ∈ (Finset.univ : Finset (Fin (d + 1))),
            ‖iteratedFDeriv ℝ ((p : Multiset (Fin (d + 1))).count j) (fac α j) y‖ := by
    intro α y
    exact norm_iteratedFDeriv_prod_le
      (fun j _ => hfac_smooth α j) (mod_cast le_top)
  have h_full := schwartzHermiteBasisNd_weighted_product_bound d k l C₁ s₁ hC₁_pos fac
    hM_poly hC_poly
  -- Step G: Final assembly
  -- Define total constant (independent of α)
  set K := (d + 1 : ℝ) ^ (k + 1) * C₁ ^ (d + 1) *
    (∑ p ∈ (Finset.univ : Finset (Fin (d + 1))).sym l,
      ((p : Multiset (Fin (d + 1))).countPerms : ℝ)) with hK_def
  refine ⟨K + 1, (d + 1) * s₁, by positivity, fun α x => ?_⟩
  have hprod_eq' : iteratedFDeriv ℝ l (hermiteFunctionNd (d + 1) α) x =
      iteratedFDeriv ℝ l (fun z => ∏ j : Fin (d + 1), fac α j z) x :=
    congrArg (iteratedFDeriv ℝ l · x) (hprod_eq α).symm
  rw [hprod_eq']
  calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ l (fun z => ∏ j : Fin (d + 1), fac α j z) x‖
      ≤ ‖x‖ ^ k *
          ∑ p ∈ (Finset.univ : Finset (Fin (d + 1))).sym l,
            (p : Multiset (Fin (d + 1))).countPerms *
              ∏ j ∈ (Finset.univ : Finset (Fin (d + 1))),
                ‖iteratedFDeriv ℝ ((p : Multiset (Fin (d + 1))).count j) (fac α j) x‖ :=
        mul_le_mul_of_nonneg_left (hprod_bound α x) (pow_nonneg (norm_nonneg _) _)
    _ = ∑ p ∈ (Finset.univ : Finset (Fin (d + 1))).sym l,
          (p : Multiset (Fin (d + 1))).countPerms *
            (‖x‖ ^ k *
              ∏ j ∈ (Finset.univ : Finset (Fin (d + 1))),
                ‖iteratedFDeriv ℝ ((p : Multiset (Fin (d + 1))).count j) (fac α j) x‖) := by
        rw [Finset.mul_sum]; ring_nf
    _ ≤ ∑ p ∈ (Finset.univ : Finset (Fin (d + 1))).sym l,
          (p : Multiset (Fin (d + 1))).countPerms *
            ((d + 1 : ℝ) ^ (k + 1) *
              (C₁ * (1 + (MultiIndex.abs α : ℝ)) ^ s₁) ^ (d + 1)) := by
        apply Finset.sum_le_sum; intro p _
        apply mul_le_mul_of_nonneg_left (h_full α x p) (by positivity)
    _ = K * (1 + (MultiIndex.abs α : ℝ)) ^ ((d + 1) * s₁) := by
        simp only [hK_def, mul_pow, ← Finset.sum_mul]; ring
    _ ≤ (K + 1) * (1 + (MultiIndex.abs α : ℝ)) ^ ((d + 1) * s₁) := by
        apply mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one)
        positivity

/-! ## Multi-Dimensional Isomorphism -/

/-- Fubini for EuclideanSpace: factors a product integral into individual integrals.
Bridges the MeasurableSpace instance diamond between EuclideanSpace (inner product
based Haar measure) and Pi (product measure) via the volume-preserving equivalence.
-/
private lemma integral_euclidean_prod_eq_prod (d : ℕ)
    (f : Fin d → ℝ → ℝ) :
    ∫ x : EuclideanSpace ℝ (Fin d), ∏ i, f i (x i) =
      ∏ i : Fin d, ∫ t : ℝ, f i t := by
  have h_pi := integral_fintype_prod_volume_eq_prod f
  convert h_pi using 1
  exact (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin d)).integral_comp'
    (fun y : Fin d → ℝ => ∏ i, f i (y i))

/-- Multi-dimensional Hermite orthonormality:
  `∫ Ψ_α(x) Ψ_β(x) dx = δ_{α,β}`.
Uses product structure `Ψ_α(x) = ∏ᵢ ψ_{αᵢ}(xᵢ)` and Fubini
(`integral_fintype_prod_volume_eq_prod`) to reduce to 1D orthonormality.
-/
private lemma hermiteFunctionNd_orthonormal (d : ℕ) (α β : MultiIndex d) :
    ∫ x : EuclideanSpace ℝ (Fin d),
      hermiteFunctionNd d α x * hermiteFunctionNd d β x =
      if α = β then 1 else 0 := by
  -- Unfold to product: Ψ_α · Ψ_β = ∏ i, (ψ_{αᵢ} · ψ_{βᵢ})
  simp only [hermiteFunctionNd, ← Finset.prod_mul_distrib]
  -- Apply Fubini via the EuclideanSpace → Pi bridge
  rw [integral_euclidean_prod_eq_prod d
    (fun i t => hermiteFunction (α i) t * hermiteFunction (β i) t)]
  -- Each 1D factor: ∫ ψ_{αᵢ} · ψ_{βᵢ} = δ_{αᵢ, βᵢ}
  simp_rw [hermiteFunction_orthonormal]
  -- Collapse: ∏ᵢ δ_{αᵢ, βᵢ} = δ_{α, β}
  by_cases h : α = β
  · subst h; simp
  · simp only [h, ite_false]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)
/-- Kronecker property for multi-d Hermite coefficients:
  `hermiteCoeffNd d α (schwartzHermiteBasisNd d β) = δ_{α,β}`.
Follows directly from orthonormality of `hermiteFunctionNd`.
-/
private lemma hermiteCoeffNd_basisNd_kronecker (d : ℕ) (α β : MultiIndex d) :
    hermiteCoeffNd d α (schwartzHermiteBasisNd d β) = if α = β then 1 else 0 := by
  change ∫ x, schwartzHermiteBasisNd d β x * hermiteFunctionNd d α x = _
  simp_rw [show ∀ x, schwartzHermiteBasisNd d β x = hermiteFunctionNd d β x from fun _ => rfl]
  convert hermiteFunctionNd_orthonormal d β α using 1
  exact ite_congr (propext eq_comm) (fun _ => rfl) (fun _ => rfl)

/-- Hermite coefficients are linear in f (multi-d). -/
private lemma hermiteCoeffNd_linear (d : ℕ) (α : MultiIndex d) :
    IsLinearMap ℝ (hermiteCoeffNd d α) where
  map_add f g := by
    simp only [hermiteCoeffNd]
    rw [show (fun x => (f + g) x * hermiteFunctionNd d α x) =
      fun x => f x * hermiteFunctionNd d α x + g x * hermiteFunctionNd d α x from by
        ext x; simp [add_mul]]
    exact integral_add
      (schwartz_mul_hermiteBasisNd_integrable d f α)
      (schwartz_mul_hermiteBasisNd_integrable d g α)
  map_smul c f := by
    simp only [hermiteCoeffNd]
    rw [show (fun x => (c • f) x * hermiteFunctionNd d α x) =
      fun x => c * (f x * hermiteFunctionNd d α x) from by
        ext x; simp [smul_eq_mul, mul_assoc]]
    exact MeasureTheory.integral_const_mul c _

/-- Multi-d Hermite coefficient as a continuous linear map (for fixed α).
Continuity follows from `|∫ f · Ψ_α| ≤ ‖Ψ_α‖_{L¹} · seminorm(0,0)(f)`.
-/
private noncomputable def hermiteCoeffNdCLM (d : ℕ) (α : MultiIndex d) :
    SchwartzMap (EuclideanSpace ℝ (Fin d)) ℝ →L[ℝ] ℝ where
  toLinearMap := {
    toFun := hermiteCoeffNd d α
    map_add' := (hermiteCoeffNd_linear d α).map_add
    map_smul' := (hermiteCoeffNd_linear d α).map_smul
  }
  cont := by
    -- Bound: |∫ f Ψ_α| ≤ sup|f| · ∫|Ψ_α| ≤ seminorm(0,0)(f) · ‖Ψ_α‖_{L¹}
    set Ψ := schwartzHermiteBasisNd d α
    set M := ∫ x : EuclideanSpace ℝ (Fin d), ‖Ψ x‖
    have hΨ_int : Integrable (⇑Ψ) volume := Ψ.integrable
    let lm : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℝ →ₗ[ℝ] ℝ := {
      toFun := hermiteCoeffNd d α
      map_add' := (hermiteCoeffNd_linear d α).map_add
      map_smul' := (hermiteCoeffNd_linear d α).map_smul
    }
    apply WithSeminorms.continuous_of_isBounded
      (schwartz_withSeminorms ℝ _ ℝ) (norm_withSeminorms ℝ ℝ) lm
    intro _
    refine ⟨{(0, 0)}, ⟨M, integral_nonneg (fun _ => norm_nonneg _)⟩, fun f => ?_⟩
    simp only [Seminorm.comp_apply, Finset.sup_singleton, lm]
    change ‖hermiteCoeffNd d α f‖ ≤
      M * SchwartzMap.seminorm ℝ 0 0 f
    calc ‖hermiteCoeffNd d α f‖
        = ‖∫ x, f x * hermiteFunctionNd d α x‖ := rfl
      _ ≤ ∫ x, ‖f x * hermiteFunctionNd d α x‖ :=
          norm_integral_le_integral_norm _
      _ = ∫ x, ‖f x‖ * ‖Ψ x‖ := by
          congr 1; ext x; exact norm_mul _ _
      _ ≤ ∫ x, SchwartzMap.seminorm ℝ 0 0 f * ‖Ψ x‖ := by
          apply integral_mono_of_nonneg
          · exact Filter.Eventually.of_forall fun _ =>
              mul_nonneg (norm_nonneg _) (norm_nonneg _)
          · exact hΨ_int.norm.const_mul _
          · exact Filter.Eventually.of_forall fun x =>
              mul_le_mul_of_nonneg_right
                (SchwartzMap.norm_le_seminorm ℝ f x) (norm_nonneg _)
      _ = SchwartzMap.seminorm ℝ 0 0 f * M := integral_const_mul _ _
      _ = M * SchwartzMap.seminorm ℝ 0 0 f := mul_comm _ _

@[simp] private theorem hermiteCoeffNdCLM_apply (d : ℕ) (α : MultiIndex d)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℝ) :
    hermiteCoeffNdCLM d α f = hermiteCoeffNd d α f := rfl

/-- Flattened multi-d Hermite coefficients form a rapid-decay sequence.
Uses `hermiteCoeffNd_decay` and `multiIndexEquiv_growth`.
-/
private theorem hermiteCoeffNd_rapid_decayFlat (d' : ℕ)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin (d' + 1))) ℝ) (k : ℕ) :
    Summable (fun n => |hermiteCoeffNd (d' + 1) ((multiIndexEquiv d').symm n) f| *
      (1 + (n : ℝ)) ^ k) := by
  obtain ⟨C₁, hC₁, k₁, hgrowth⟩ := multiIndexEquiv_growth d'
  obtain ⟨D, q, hD, hdecay⟩ := hermiteCoeffNd_decay d' (↑(k₁ * (k + 2)) : ℝ)
  set S := q.sup (schwartzSeminormFamily ℝ (EuclideanSpace ℝ (Fin (d' + 1))) ℝ) f
  -- Bound each term
  have h_le : ∀ n : ℕ,
      |hermiteCoeffNd (d' + 1) ((multiIndexEquiv d').symm n) f| * (1 + (n : ℝ)) ^ k ≤
      D * S * C₁ ^ (k + 2) * (1 + (n : ℝ)) ^ ((-2) : ℝ) := by
    intro n
    set α := (multiIndexEquiv d').symm n
    have h1n : (0 : ℝ) < 1 + ↑n := by positivity
    have hn_le : (1 + (n : ℝ)) ≤ C₁ * (1 + ↑(MultiIndex.abs α)) ^ k₁ := by
      have := hgrowth α; simp only [α, Equiv.apply_symm_apply] at this; exact this
    have h_bd : |hermiteCoeffNd (d' + 1) α f| *
        (1 + ↑(MultiIndex.abs α)) ^ (k₁ * (k + 2)) ≤ D * S := by
      have := hdecay f α; rwa [rpow_natCast] at this
    have h_combined : |hermiteCoeffNd (d' + 1) α f| * (1 + ↑n) ^ (k + 2) ≤
        C₁ ^ (k + 2) * (D * S) := by
      calc |hermiteCoeffNd (d' + 1) α f| * (1 + ↑n) ^ (k + 2)
          ≤ |hermiteCoeffNd (d' + 1) α f| *
            (C₁ ^ (k + 2) * (1 + ↑(MultiIndex.abs α)) ^ (k₁ * (k + 2))) := by
            apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
            calc (1 + ↑n) ^ (k + 2)
                ≤ (C₁ * (1 + ↑(MultiIndex.abs α)) ^ k₁) ^ (k + 2) :=
                  pow_le_pow_left₀ (by positivity) hn_le _
              _ = C₁ ^ (k + 2) * (1 + ↑(MultiIndex.abs α)) ^ (k₁ * (k + 2)) := by
                  rw [mul_pow, ← pow_mul]
        _ = C₁ ^ (k + 2) * (|hermiteCoeffNd (d' + 1) α f| *
              (1 + ↑(MultiIndex.abs α)) ^ (k₁ * (k + 2))) := by ring
        _ ≤ C₁ ^ (k + 2) * (D * S) :=
            mul_le_mul_of_nonneg_left h_bd (pow_nonneg hC₁.le _)
    rw [pow_add, ← mul_assoc] at h_combined
    calc |hermiteCoeffNd (d' + 1) α f| * (1 + ↑n) ^ k
        ≤ C₁ ^ (k + 2) * (D * S) / (1 + ↑n) ^ 2 :=
          (le_div_iff₀ (by positivity : (0 : ℝ) < (1 + ↑n) ^ 2)).mpr h_combined
      _ = D * S * C₁ ^ (k + 2) * ((1 + ↑n) ^ (2 : ℕ))⁻¹ := by rw [div_eq_mul_inv]; ring
      _ = D * S * C₁ ^ (k + 2) * (1 + ↑n) ^ ((-2) : ℝ) := by
          congr 1
          rw [show ((-2 : ℝ) : ℝ) = -(↑2 : ℕ) from by norm_num]
          rw [rpow_neg h1n.le, rpow_natCast]
  -- Summable upper bound
  have h_sum : Summable (fun n : ℕ => D * S * C₁ ^ (k + 2) * (1 + (n : ℝ)) ^ ((-2) : ℝ)) :=
    (((summable_nat_rpow.mpr (by norm_num : (-2 : ℝ) < -1)).comp_injective
      (fun a b h => Nat.succ_injective h)).congr
      (fun n => by change ((↑(n + 1) : ℝ)) ^ ((-2) : ℝ) = _; simp [add_comm]))
    |>.const_smul (D * S * C₁ ^ (k + 2))
  exact .of_nonneg_of_le
    (fun n => mul_nonneg (abs_nonneg _) (pow_nonneg (by positivity) _))
    h_le h_sum

/-- The forward linear map for the multi-d Hermite expansion.
Maps `S(ℝ^{d'+1})` to `s(ℕ)` via flattened Hermite coefficients.
-/
private noncomputable def toRapidDecayNdLM (d' : ℕ) :
    SchwartzMap (EuclideanSpace ℝ (Fin (d' + 1))) ℝ →ₗ[ℝ] RapidDecaySeq where
  toFun f := ⟨fun n => hermiteCoeffNd (d' + 1) ((multiIndexEquiv d').symm n) f,
    hermiteCoeffNd_rapid_decayFlat d' f⟩
  map_add' f g := RapidDecaySeq.ext fun n =>
    (hermiteCoeffNd_linear (d' + 1) _).map_add f g
  map_smul' r f := RapidDecaySeq.ext fun n => by
    simp only [RapidDecaySeq.smul_val, RingHom.id_apply]
    exact (hermiteCoeffNd_linear (d' + 1) _).map_smul r f

/-- The `IsBounded` property for `toRapidDecayNdLM`. -/
private lemma toRapidDecayNdLM_isBounded (d' : ℕ) :
    Seminorm.IsBounded
      (schwartzSeminormFamily ℝ (EuclideanSpace ℝ (Fin (d' + 1))) ℝ)
      RapidDecaySeq.rapidDecaySeminorm
      (toRapidDecayNdLM d') := by
  intro k
  obtain ⟨C₁, hC₁, k₁, hgrowth⟩ := multiIndexEquiv_growth d'
  obtain ⟨D, q, hD, hdecay⟩ := hermiteCoeffNd_decay d' (↑(k₁ * (k + 2)) : ℝ)
  have h_rpow_sum : Summable (fun n : ℕ => (1 + (n : ℝ)) ^ ((-2) : ℝ)) :=
    ((summable_nat_rpow.mpr (by norm_num : (-2 : ℝ) < -1)).comp_injective
      (fun a b h => Nat.succ_injective h)).congr
      (fun n => by change ((↑(n + 1) : ℝ)) ^ ((-2) : ℝ) = _; simp [add_comm])
  set L := ∑' n : ℕ, (1 + (n : ℝ)) ^ ((-2) : ℝ)
  refine ⟨q, ⟨D * C₁ ^ (k + 2) * L, by positivity⟩, fun f => ?_⟩
  simp only [Seminorm.comp_apply, Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul]
  set S := q.sup (schwartzSeminormFamily ℝ (EuclideanSpace ℝ (Fin (d' + 1))) ℝ) f
  change ∑' n, |hermiteCoeffNd (d' + 1) ((multiIndexEquiv d').symm n) f| * (1 + ↑n) ^ k ≤
    D * C₁ ^ (k + 2) * L * S
  have h_le : ∀ n : ℕ,
      |hermiteCoeffNd (d' + 1) ((multiIndexEquiv d').symm n) f| * (1 + (n : ℝ)) ^ k ≤
      D * S * C₁ ^ (k + 2) * (1 + (n : ℝ)) ^ ((-2) : ℝ) := by
    intro n
    set α := (multiIndexEquiv d').symm n
    have h1n : (0 : ℝ) < 1 + ↑n := by positivity
    have hn_le : (1 + (n : ℝ)) ≤ C₁ * (1 + ↑(MultiIndex.abs α)) ^ k₁ := by
      have := hgrowth α; simp only [α, Equiv.apply_symm_apply] at this; exact this
    have h_bd : |hermiteCoeffNd (d' + 1) α f| *
        (1 + ↑(MultiIndex.abs α)) ^ (k₁ * (k + 2)) ≤ D * S := by
      have := hdecay f α; rwa [rpow_natCast] at this
    have h_combined : |hermiteCoeffNd (d' + 1) α f| * (1 + ↑n) ^ (k + 2) ≤
        C₁ ^ (k + 2) * (D * S) := by
      calc |hermiteCoeffNd (d' + 1) α f| * (1 + ↑n) ^ (k + 2)
          ≤ |hermiteCoeffNd (d' + 1) α f| *
            (C₁ ^ (k + 2) * (1 + ↑(MultiIndex.abs α)) ^ (k₁ * (k + 2))) := by
            apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
            calc (1 + ↑n) ^ (k + 2)
                ≤ (C₁ * (1 + ↑(MultiIndex.abs α)) ^ k₁) ^ (k + 2) :=
                  pow_le_pow_left₀ (by positivity) hn_le _
              _ = C₁ ^ (k + 2) * (1 + ↑(MultiIndex.abs α)) ^ (k₁ * (k + 2)) := by
                  rw [mul_pow, ← pow_mul]
        _ = C₁ ^ (k + 2) * (|hermiteCoeffNd (d' + 1) α f| *
              (1 + ↑(MultiIndex.abs α)) ^ (k₁ * (k + 2))) := by ring
        _ ≤ C₁ ^ (k + 2) * (D * S) :=
            mul_le_mul_of_nonneg_left h_bd (pow_nonneg hC₁.le _)
    rw [pow_add, ← mul_assoc] at h_combined
    have hle : |hermiteCoeffNd (d' + 1) α f| * (1 + ↑n) ^ k ≤
        D * S * C₁ ^ (k + 2) * (1 + ↑n) ^ ((-2) : ℝ) := by
      calc |hermiteCoeffNd (d' + 1) α f| * (1 + ↑n) ^ k
          ≤ C₁ ^ (k + 2) * (D * S) / (1 + ↑n) ^ 2 :=
            (le_div_iff₀ (by positivity : (0 : ℝ) < (1 + ↑n) ^ 2)).mpr h_combined
        _ = D * S * C₁ ^ (k + 2) * ((1 + ↑n) ^ (2 : ℕ))⁻¹ := by rw [div_eq_mul_inv]; ring
        _ = D * S * C₁ ^ (k + 2) * (1 + ↑n) ^ ((-2) : ℝ) := by
            congr 1
            rw [show ((-2 : ℝ) : ℝ) = -(↑2 : ℕ) from by norm_num]
            rw [rpow_neg h1n.le, rpow_natCast]
    exact hle
  calc ∑' n, |hermiteCoeffNd (d' + 1) ((multiIndexEquiv d').symm n) f| * (1 + ↑n) ^ k
      ≤ ∑' (n : ℕ), D * S * C₁ ^ (k + 2) * (1 + (n : ℝ)) ^ ((-2) : ℝ) :=
        (hermiteCoeffNd_rapid_decayFlat d' f k).tsum_le_tsum h_le
          (h_rpow_sum.const_smul (D * S * C₁ ^ (k + 2)))
    _ = D * S * C₁ ^ (k + 2) * L := tsum_mul_left
    _ = D * C₁ ^ (k + 2) * L * S := by ring

/-- The forward continuous linear map for the d-dimensional Hermite expansion.
Maps `S(ℝ^d)` to `s(ℕ)` using the flattened multi-index.
-/
noncomputable def toRapidDecayNdCLM (d : ℕ) :
    SchwartzMap (EuclideanSpace ℝ (Fin d)) ℝ →L[ℝ] RapidDecaySeq :=
  match d with
  | 0 => 0
  | d' + 1 => {
      toLinearMap := toRapidDecayNdLM d'
      cont := WithSeminorms.continuous_of_isBounded
        (schwartz_withSeminorms ℝ (EuclideanSpace ℝ (Fin (d' + 1))) ℝ)
        RapidDecaySeq.rapidDecay_withSeminorms
        _ (toRapidDecayNdLM_isBounded d')
    }

/-! ### Multi-Dimensional Backward Map Construction -/

/-- The flattened multi-d Hermite basis: the n-th basis function via `multiIndexEquiv`. -/
private noncomputable def flatBasisNd (d : ℕ) (n : ℕ) :
    SchwartzMap (EuclideanSpace ℝ (Fin (d + 1))) ℝ :=
  schwartzHermiteBasisNd (d + 1) ((multiIndexEquiv d).symm n)

/-- Bound on iterated derivative of `c * flatBasisNd d n`:
`‖D^l(c · Φₙ)(x)‖ ≤ |c| · p_{0,l}(Φₙ)`.
-/
private lemma scalar_flatBasisNd_iFDeriv_bound (d : ℕ) (c : ℝ) (n l : ℕ)
    (x : EuclideanSpace ℝ (Fin (d + 1))) :
    ‖iteratedFDeriv ℝ l (fun y => c * flatBasisNd d n y) x‖ ≤
      |c| * SchwartzMap.seminorm ℝ 0 l (flatBasisNd d n) := by
  have hcoe : (fun y => c * flatBasisNd d n y) = ⇑(c • flatBasisNd d n) := by
    ext y; simp [smul_eq_mul]
  rw [hcoe]
  calc ‖iteratedFDeriv ℝ l (⇑(c • flatBasisNd d n)) x‖
      ≤ (SchwartzMap.seminorm ℝ 0 l) (c • flatBasisNd d n) := by
          have h := SchwartzMap.le_seminorm ℝ 0 l (c • flatBasisNd d n) x
          simp only [pow_zero, one_mul] at h; exact h
    _ = |c| * (SchwartzMap.seminorm ℝ 0 l) (flatBasisNd d n) := by
          rw [map_smul_eq_mul, Real.norm_eq_abs]

/-- Summability of `∑ₙ |aₙ| · p_{k,l}(Φₙ)` for the flattened multi-d basis.
Uses `schwartzHermiteBasisNd_growth` and `multiIndexEquiv_symm_growth`.
-/
private lemma rapidDecay_seminorm_summableNd (d : ℕ) (a : RapidDecaySeq) (k l : ℕ) :
    Summable (fun n => |a.val n| * SchwartzMap.seminorm ℝ k l (flatBasisNd d n)) := by
  obtain ⟨C₁, hC₁, s₁, hbasis⟩ := schwartzHermiteBasisNd_growth (d + 1) k l
  obtain ⟨C₂, hC₂, k₂, hsymm⟩ := multiIndexEquiv_symm_growth d
  exact .of_nonneg_of_le
    (fun n => mul_nonneg (abs_nonneg _) (apply_nonneg _ _))
    (fun n => by
      set α := (multiIndexEquiv d).symm n
      calc |a.val n| * SchwartzMap.seminorm ℝ k l (flatBasisNd d n)
          ≤ |a.val n| * (C₁ * (1 + (MultiIndex.abs α : ℝ)) ^ s₁) :=
            mul_le_mul_of_nonneg_left (hbasis α) (abs_nonneg _)
        _ ≤ |a.val n| * (C₁ * (C₂ * (1 + (n : ℝ)) ^ k₂) ^ s₁) := by
            gcongr; exact hsymm n
        _ = (C₁ * C₂ ^ s₁) * (|a.val n| * (1 + (n : ℝ)) ^ (k₂ * s₁)) := by
            rw [mul_pow]; ring)
    ((a.rapid_decay (k₂ * s₁)).mul_left (C₁ * C₂ ^ s₁))

/-- Pointwise summability of the multi-d Hermite expansion. -/
private lemma rapidDecay_pointwise_summableNd (d : ℕ) (a : RapidDecaySeq)
    (x : EuclideanSpace ℝ (Fin (d + 1))) :
    Summable (fun n => a.val n * flatBasisNd d n x) := by
  apply Summable.of_norm_bounded
    (g := fun n => |a.val n| * SchwartzMap.seminorm ℝ 0 0 (flatBasisNd d n))
  · exact rapidDecay_seminorm_summableNd d a 0 0
  · intro n
    simp only [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left
      (by rw [← Real.norm_eq_abs]; exact SchwartzMap.norm_le_seminorm ℝ _ x)
      (abs_nonneg _)

/-- The pointwise tsum of the multi-d Hermite expansion is smooth. -/
private lemma rapidDecay_hermite_contDiffNd (d : ℕ) (a : RapidDecaySeq) :
    ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin (d + 1)) =>
      ∑' n, a.val n * flatBasisNd d n x) := by
  apply contDiff_tsum
    (v := fun j n => |a.val n| * SchwartzMap.seminorm ℝ 0 j (flatBasisNd d n))
  · intro n
    exact contDiff_const.mul (flatBasisNd d n).smooth'
  · intro j _; exact rapidDecay_seminorm_summableNd d a 0 j
  · intro j n x _; exact scalar_flatBasisNd_iFDeriv_bound d (a.val n) n j x

/-- Pointwise bound: `‖x‖^k · ‖D^l(∑' aₙΦₙ)(x)‖ ≤ ∑' |aₙ| · p_{k,l}(Φₙ)`. -/
private lemma rapidDecay_pointwise_seminorm_leNd (d : ℕ) (a : RapidDecaySeq) (k l : ℕ)
    (x : EuclideanSpace ℝ (Fin (d + 1))) :
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ l
      (fun y => ∑' n, a.val n * flatBasisNd d n y) x‖ ≤
    ∑' n, |a.val n| * SchwartzMap.seminorm ℝ k l (flatBasisNd d n) := by
  have h_iFD : iteratedFDeriv ℝ l (fun y => ∑' n, a.val n * flatBasisNd d n y) x =
      ∑' n, iteratedFDeriv ℝ l (fun y => a.val n * flatBasisNd d n y) x := by
    apply iteratedFDeriv_tsum_apply (N := ⊤)
      (v := fun j n => |a.val n| * SchwartzMap.seminorm ℝ 0 j (flatBasisNd d n))
    · intro n; exact contDiff_const.mul (flatBasisNd d n).smooth'
    · intro j _; exact rapidDecay_seminorm_summableNd d a 0 j
    · intro j n y _; exact scalar_flatBasisNd_iFDeriv_bound d (a.val n) n j y
    · exact le_top
  rw [h_iFD]
  have h_norm_summ : Summable (fun n =>
      ‖iteratedFDeriv ℝ l (fun y => a.val n * flatBasisNd d n y) x‖) :=
    .of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun n => scalar_flatBasisNd_iFDeriv_bound d (a.val n) n l x)
      (rapidDecay_seminorm_summableNd d a 0 l)
  have h_ptwise : ∀ n, ‖x‖ ^ k *
      ‖iteratedFDeriv ℝ l (fun y => a.val n * flatBasisNd d n y) x‖ ≤
      |a.val n| * SchwartzMap.seminorm ℝ k l (flatBasisNd d n) := by
    intro n
    have hfun_eq : (fun y => a.val n * flatBasisNd d n y) =
        ⇑(a.val n • flatBasisNd d n) := by
      ext y; simp [smul_eq_mul]
    rw [hfun_eq]
    calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ l (⇑(a.val n • flatBasisNd d n)) x‖
        ≤ SchwartzMap.seminorm ℝ k l (a.val n • flatBasisNd d n) :=
          SchwartzMap.le_seminorm ℝ k l _ x
      _ = |a.val n| * SchwartzMap.seminorm ℝ k l (flatBasisNd d n) := by
          rw [map_smul_eq_mul, Real.norm_eq_abs]
  calc ‖x‖ ^ k * ‖∑' n, iteratedFDeriv ℝ l (fun y => a.val n * flatBasisNd d n y) x‖
      ≤ ‖x‖ ^ k * ∑' n, ‖iteratedFDeriv ℝ l (fun y => a.val n * flatBasisNd d n y) x‖ :=
        mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm h_norm_summ)
          (pow_nonneg (norm_nonneg _) k)
    _ = ∑' n, ‖x‖ ^ k * ‖iteratedFDeriv ℝ l (fun y => a.val n * flatBasisNd d n y) x‖ :=
        tsum_mul_left.symm
    _ ≤ ∑' n, |a.val n| * SchwartzMap.seminorm ℝ k l (flatBasisNd d n) :=
        (Summable.of_nonneg_of_le
          (fun _ => mul_nonneg (pow_nonneg (norm_nonneg _) k) (norm_nonneg _))
          h_ptwise (rapidDecay_seminorm_summableNd d a k l)).tsum_le_tsum
          h_ptwise (rapidDecay_seminorm_summableNd d a k l)

/-- The Schwartz function from a rapid-decay multi-d Hermite expansion. -/
private noncomputable def rapidDecay_schwartzMapNd (d : ℕ) (a : RapidDecaySeq) :
    SchwartzMap (EuclideanSpace ℝ (Fin (d + 1))) ℝ where
  toFun x := ∑' n, a.val n * flatBasisNd d n x
  smooth' := rapidDecay_hermite_contDiffNd d a
  decay' k l := ⟨_, rapidDecay_pointwise_seminorm_leNd d a k l⟩

private lemma rapidDecay_schwartzMapNd_apply (d : ℕ) (a : RapidDecaySeq)
    (x : EuclideanSpace ℝ (Fin (d + 1))) :
    rapidDecay_schwartzMapNd d a x = ∑' n, a.val n * flatBasisNd d n x := rfl

private noncomputable instance schwartzMapNd_T2Space (d : ℕ) :
    T2Space (SchwartzMap (EuclideanSpace ℝ (Fin d)) ℝ) := by
  haveI : T1Space (SchwartzMap (EuclideanSpace ℝ (Fin d)) ℝ) :=
    WithSeminorms.T1_of_separating (schwartz_withSeminorms ℝ _ ℝ) fun f hf =>
      ⟨⟨0, 0⟩, fun h => hf (SchwartzMap.ext fun x =>
        norm_le_zero_iff.mp ((SchwartzMap.norm_le_seminorm ℝ f x).trans (le_of_eq h)))⟩
  exact inferInstance

/-- The multi-d Hermite expansion converges to `rapidDecay_schwartzMapNd d a`
in the Schwartz topology.
-/
private theorem rapidDecay_hermite_hasSumNd (d : ℕ) (a : RapidDecaySeq) :
    HasSum (fun n => a.val n • flatBasisNd d n) (rapidDecay_schwartzMapNd d a) := by
  rw [HasSum]
  change Filter.Tendsto _ Filter.atTop _
  rw [(schwartz_withSeminorms ℝ (EuclideanSpace ℝ (Fin (d + 1))) ℝ).tendsto_nhds _
    (rapidDecay_schwartzMapNd d a)]
  intro ⟨k, l⟩ ε hε
  have h_sem := rapidDecay_seminorm_summableNd d a k l
  obtain ⟨s₀, hs₀⟩ := summable_iff_vanishing_norm.mp h_sem (ε / 2) (half_pos hε)
  rw [Filter.eventually_atTop]
  refine ⟨s₀, fun s hs => ?_⟩
  rw [show (∑ i ∈ s, a.val i • flatBasisNd d i) - rapidDecay_schwartzMapNd d a =
    -(rapidDecay_schwartzMapNd d a - ∑ i ∈ s, a.val i • flatBasisNd d i) from by abel,
    map_neg_eq_map]
  calc SchwartzMap.seminorm ℝ k l
        (rapidDecay_schwartzMapNd d a - ∑ i ∈ s, a.val i • flatBasisNd d i)
      ≤ ε / 2 := by
        apply SchwartzMap.seminorm_le_bound ℝ k l _ (half_pos hε).le
        intro x
        set r := rapidDecay_schwartzMapNd d a -
          ∑ i ∈ s, a.val i • flatBasisNd d i with hr_def
        let g : ℕ → EuclideanSpace ℝ (Fin (d + 1)) → ℝ :=
          fun n y => a.val n * flatBasisNd d n y
        have h_summ_iFD : Summable (fun n => iteratedFDeriv ℝ l (g n) x) := by
          apply Summable.of_norm_bounded
            (g := fun n => |a.val n| * SchwartzMap.seminorm ℝ 0 l (flatBasisNd d n))
          · exact rapidDecay_seminorm_summableNd d a 0 l
          · intro n; exact scalar_flatBasisNd_iFDeriv_bound d (a.val n) n l x
        have h_iFD_limit : iteratedFDeriv ℝ l
            (fun y => ∑' n, a.val n * flatBasisNd d n y) x =
            ∑' n, iteratedFDeriv ℝ l (g n) x := by
          apply iteratedFDeriv_tsum_apply (N := ⊤)
            (v := fun j n => |a.val n| * SchwartzMap.seminorm ℝ 0 j (flatBasisNd d n))
          · intro n; exact contDiff_const.mul (flatBasisNd d n).smooth'
          · intro j _; exact rapidDecay_seminorm_summableNd d a 0 j
          · intro j n y _; exact scalar_flatBasisNd_iFDeriv_bound d (a.val n) n j y
          · exact le_top
        have hsum_coe : ∀ y,
            (∑ i ∈ s, a.val i • flatBasisNd d i :
              SchwartzMap (EuclideanSpace ℝ (Fin (d + 1))) ℝ) y =
            ∑ i ∈ s, g i y := by
          intro y
          have : ∀ (t : Finset ℕ),
              (∑ i ∈ t, a.val i • flatBasisNd d i :
                SchwartzMap (EuclideanSpace ℝ (Fin (d + 1))) ℝ) y =
              ∑ i ∈ t, g i y := by
            intro t; induction t using Finset.cons_induction with
            | empty => simp
            | cons a' t' ha' ih =>
              simp [SchwartzMap.smul_apply, smul_eq_mul, g]
          exact this s
        have h_iFD_sum : iteratedFDeriv ℝ l
            (⇑(∑ i ∈ s, a.val i • flatBasisNd d i :
              SchwartzMap (EuclideanSpace ℝ (Fin (d + 1))) ℝ)) x =
            ∑ i ∈ s, iteratedFDeriv ℝ l (g i) x := by
          have hcoe : ⇑(∑ i ∈ s, a.val i • flatBasisNd d i :
              SchwartzMap (EuclideanSpace ℝ (Fin (d + 1))) ℝ) =
              fun y => ∑ i ∈ s, g i y := funext hsum_coe
          rw [hcoe]
          have h_eq := iteratedFDeriv_sum (𝕜 := ℝ) (f := g) (u := s) (i := l)
            (fun i _ => (contDiff_const.mul (flatBasisNd d i).smooth').of_le (mod_cast le_top))
          exact congr_fun h_eq x |>.trans (Finset.sum_apply x s _)
        have h_iFD_r : iteratedFDeriv ℝ l (⇑r) x =
            ∑' (i : ↥(↑s : Set ℕ)ᶜ), iteratedFDeriv ℝ l (g ↑i) x := by
          have hf_cd : ContDiff ℝ l
              (fun y => ∑' n, a.val n * flatBasisNd d n y) :=
            (rapidDecay_hermite_contDiffNd d a).of_le (mod_cast le_top)
          have hg_cd : ContDiff ℝ l (fun y => ∑ i ∈ s, g i y) :=
            ContDiff.sum (fun i _ =>
              (contDiff_const.mul (flatBasisNd d i).smooth').of_le (mod_cast le_top))
          have hcoe_r : (⇑r : EuclideanSpace ℝ (Fin (d + 1)) → ℝ) = fun y =>
              (∑' n, a.val n * flatBasisNd d n y) - ∑ i ∈ s, g i y := by
            ext y; simp only [hr_def, SchwartzMap.sub_apply,
              rapidDecay_schwartzMapNd_apply]
            exact congrArg
              ((∑' n, a.val n * flatBasisNd d n y) - ·) (hsum_coe y)
          rw [hcoe_r]
          set h_sum := fun y => ∑ i ∈ s, g i y with h_sum_def
          have h_neg_cd : ContDiff ℝ l (-h_sum) := hg_cd.neg
          have h_rw : (fun y =>
              (∑' n, a.val n * flatBasisNd d n y) - h_sum y) =
              (fun y => ∑' n, a.val n * flatBasisNd d n y) + (-h_sum) := by
            ext; simp [sub_eq_add_neg]
          rw [h_rw, iteratedFDeriv_add hf_cd h_neg_cd, Pi.add_apply,
            iteratedFDeriv_neg, Pi.neg_apply, h_iFD_limit]
          have h_iFD_h : iteratedFDeriv ℝ l h_sum x =
              ∑ i ∈ s, iteratedFDeriv ℝ l (g i) x := by
            rw [h_sum_def]
            have h_eq := iteratedFDeriv_sum (𝕜 := ℝ) (f := g) (u := s) (i := l)
              (fun i _ =>
                (contDiff_const.mul (flatBasisNd d i).smooth').of_le (mod_cast le_top))
            calc iteratedFDeriv ℝ l (fun y => ∑ i ∈ s, g i y) x
                = (∑ j ∈ s, iteratedFDeriv ℝ l (g j)) x := congr_fun h_eq x
              _ = ∑ i ∈ s, iteratedFDeriv ℝ l (g i) x := Finset.sum_apply x s _
          rw [h_iFD_h]
          rw [← h_summ_iFD.sum_add_tsum_compl (s := s)]
          abel
        have h_norm_summ : Summable (fun (i : ↥(↑s : Set ℕ)ᶜ) =>
            ‖iteratedFDeriv ℝ l (g ↑i) x‖) :=
          (Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
            (fun n => scalar_flatBasisNd_iFDeriv_bound d (a.val n) n l x)
            (rapidDecay_seminorm_summableNd d a 0 l)).subtype _
        have h_sem_summ : Summable (fun (i : ↥(↑s : Set ℕ)ᶜ) =>
            |a.val ↑i| * SchwartzMap.seminorm ℝ k l (flatBasisNd d ↑i)) :=
          (rapidDecay_seminorm_summableNd d a k l).subtype _
        have h_ptwise : ∀ (i : ↥(↑s : Set ℕ)ᶜ),
            ‖x‖ ^ k * ‖iteratedFDeriv ℝ l (g ↑i) x‖ ≤
            |a.val ↑i| * SchwartzMap.seminorm ℝ k l (flatBasisNd d ↑i) := by
          intro ⟨n, _⟩
          have hg_eq : g n = ⇑(a.val n • flatBasisNd d n) := by
            ext y; simp [g, smul_eq_mul]
          rw [hg_eq]
          calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ l
                (⇑(a.val n • flatBasisNd d n)) x‖
              ≤ SchwartzMap.seminorm ℝ k l (a.val n • flatBasisNd d n) :=
                SchwartzMap.le_seminorm ℝ k l _ x
            _ = |a.val n| * SchwartzMap.seminorm ℝ k l (flatBasisNd d n) := by
                rw [map_smul_eq_mul, Real.norm_eq_abs]
        rw [h_iFD_r]
        calc ‖x‖ ^ k * ‖∑' (i : ↥(↑s : Set ℕ)ᶜ),
                iteratedFDeriv ℝ l (g ↑i) x‖
            ≤ ‖x‖ ^ k * ∑' (i : ↥(↑s : Set ℕ)ᶜ),
                ‖iteratedFDeriv ℝ l (g ↑i) x‖ :=
              mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm h_norm_summ)
                (pow_nonneg (norm_nonneg _) k)
          _ = ∑' (i : ↥(↑s : Set ℕ)ᶜ),
                (‖x‖ ^ k * ‖iteratedFDeriv ℝ l (g ↑i) x‖) := by
              rw [tsum_mul_left]
          _ ≤ ∑' (i : ↥(↑s : Set ℕ)ᶜ),
                (|a.val ↑i| * SchwartzMap.seminorm ℝ k l (flatBasisNd d ↑i)) :=
              (h_norm_summ.mul_left _).tsum_le_tsum h_ptwise h_sem_summ
          _ ≤ ε / 2 := by
              apply h_sem_summ.tsum_le_of_sum_le
              intro t
              set t' := t.map ⟨Subtype.val, Subtype.val_injective⟩ with ht'_def
              have h_disj : Disjoint t' s := by
                rw [Finset.disjoint_left]
                intro n hn hn_s
                rw [Finset.mem_map] at hn
                obtain ⟨⟨m, hm⟩, _, rfl⟩ := hn
                exact hm hn_s
              have h_disj₀ : Disjoint t' s₀ := Disjoint.mono_right hs h_disj
              have h_lt := hs₀ t' h_disj₀
              rw [Real.norm_of_nonneg (Finset.sum_nonneg fun i _ =>
                mul_nonneg (abs_nonneg _) (apply_nonneg _ _))] at h_lt
              rw [ht'_def, Finset.sum_map] at h_lt
              exact le_of_lt h_lt
    _ < ε := half_lt_self hε

/-- Summability of multi-d Hermite expansion for rapid-decay coefficients. -/
private theorem rapidDecay_hermite_summableNd (d : ℕ) (a : RapidDecaySeq) :
    Summable (fun n => a.val n • flatBasisNd d n) :=
  ⟨_, rapidDecay_hermite_hasSumNd d a⟩

private noncomputable def fromRapidDecayNdLM (d : ℕ) :
    RapidDecaySeq →ₗ[ℝ] SchwartzMap (EuclideanSpace ℝ (Fin (d + 1))) ℝ where
  toFun := rapidDecay_schwartzMapNd d
  map_add' a b := SchwartzMap.ext fun x => by
    change ∑' n, (a + b).val n * flatBasisNd d n x =
      (∑' n, a.val n * flatBasisNd d n x) + (∑' n, b.val n * flatBasisNd d n x)
    simp only [RapidDecaySeq.add_val, add_mul]
    exact (rapidDecay_pointwise_summableNd d a x).tsum_add
      (rapidDecay_pointwise_summableNd d b x)
  map_smul' r a := SchwartzMap.ext fun x => by
    change ∑' n, (r • a).val n * flatBasisNd d n x =
      r • (∑' n, a.val n * flatBasisNd d n x)
    simp only [RapidDecaySeq.smul_val, smul_eq_mul, mul_assoc]
    exact tsum_mul_left

/-- `fromRapidDecayNdLM d a` equals the tsum of scaled Hermite basis elements. -/
private lemma fromRapidDecayNdLM_eq (d : ℕ) (a : RapidDecaySeq) :
    fromRapidDecayNdLM d a = ∑' n, a.val n • flatBasisNd d n :=
  (rapidDecay_hermite_hasSumNd d a).tsum_eq.symm

/-- Seminorm bound: `p_{k,l}(fromRapidDecayNdLM d a) ≤ ∑' |aₙ| · p_{k,l}(Φₙ)`. -/
private lemma fromRapidDecayNdLM_seminorm_le (d : ℕ) (a : RapidDecaySeq) (k l : ℕ) :
    SchwartzMap.seminorm ℝ k l (fromRapidDecayNdLM d a) ≤
      ∑' n, |a.val n| * SchwartzMap.seminorm ℝ k l (flatBasisNd d n) :=
  SchwartzMap.seminorm_le_bound ℝ k l _ (tsum_nonneg fun _ =>
    mul_nonneg (abs_nonneg _) (apply_nonneg _ _)) (rapidDecay_pointwise_seminorm_leNd d a k l)

/-- Bound using rapid-decay seminorm: `p_{k,l}(Φ(a)) ≤ C · ρ_s(a)`. -/
private lemma fromRapidDecayNdLM_bound (d : ℕ) (k l : ℕ) :
    ∃ (C : ℝ), 0 < C ∧ ∃ (s : ℕ), ∀ (a : RapidDecaySeq),
      SchwartzMap.seminorm ℝ k l (fromRapidDecayNdLM d a) ≤
        C * RapidDecaySeq.rapidDecaySeminorm s a := by
  obtain ⟨C₁, hC₁, s₁, hbasis⟩ := schwartzHermiteBasisNd_growth (d + 1) k l
  obtain ⟨C₂, hC₂, k₂, hsymm⟩ := multiIndexEquiv_symm_growth d
  refine ⟨C₁ * C₂ ^ s₁, by positivity, k₂ * s₁, fun a => ?_⟩
  calc SchwartzMap.seminorm ℝ k l (fromRapidDecayNdLM d a)
      ≤ ∑' n, |a.val n| * SchwartzMap.seminorm ℝ k l (flatBasisNd d n) :=
        fromRapidDecayNdLM_seminorm_le d a k l
    _ ≤ ∑' n, |a.val n| * (C₁ * (C₂ * (1 + (n : ℝ)) ^ k₂) ^ s₁) := by
        apply (rapidDecay_seminorm_summableNd d a k l).tsum_le_tsum _
          ((a.rapid_decay (k₂ * s₁)).mul_left (C₁ * C₂ ^ s₁) |>.congr fun n => by
            rw [mul_pow]; ring)
        intro n
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        calc SchwartzMap.seminorm ℝ k l (flatBasisNd d n)
            ≤ C₁ * (1 + (MultiIndex.abs ((multiIndexEquiv d).symm n) : ℝ)) ^ s₁ := hbasis _
          _ ≤ C₁ * (C₂ * (1 + (n : ℝ)) ^ k₂) ^ s₁ := by
              gcongr; exact hsymm n
    _ = C₁ * C₂ ^ s₁ * ∑' n, |a.val n| * (1 + (n : ℝ)) ^ (k₂ * s₁) := by
        rw [← tsum_mul_left]; congr 1; ext n; rw [mul_pow]; ring

/-- The `IsBounded` property for `fromRapidDecayNdLM`. -/
private lemma fromRapidDecayNdLM_isBounded (d : ℕ) :
    Seminorm.IsBounded RapidDecaySeq.rapidDecaySeminorm
      (schwartzSeminormFamily ℝ (EuclideanSpace ℝ (Fin (d + 1))) ℝ)
      (fromRapidDecayNdLM d) := by
  intro ⟨k, l⟩
  obtain ⟨C, hC, s, hbound⟩ := fromRapidDecayNdLM_bound d k l
  exact ⟨{s}, ⟨C, hC.le⟩, fun a => by
    simp only [Seminorm.comp_apply, schwartzSeminormFamily, Finset.sup_singleton,
      Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul]
    exact hbound a⟩

/-- The backward continuous linear map for the d-dimensional Hermite expansion.
Maps `s(ℕ)` to `S(ℝ^d)`.
-/
noncomputable def fromRapidDecayNdCLM (d : ℕ) :
    RapidDecaySeq →L[ℝ] SchwartzMap (EuclideanSpace ℝ (Fin d)) ℝ :=
  match d with
  | 0 => 0
  | d' + 1 => {
      toLinearMap := fromRapidDecayNdLM d'
      cont := WithSeminorms.continuous_of_isBounded
        RapidDecaySeq.rapidDecay_withSeminorms
        (schwartz_withSeminorms ℝ (EuclideanSpace ℝ (Fin (d' + 1))) ℝ)
        _ (fromRapidDecayNdLM_isBounded d')
    }

/-! ### Left Inverse and Completeness via Injectivity -/

/-- Right inverse property extracted as a lemma: the Hermite coefficients of the reconstructed
Schwartz function exactly match the input sequence.
-/
private lemma hermiteCoeffNd_rapidDecay_schwartzMapNd (d' : ℕ) (a : RapidDecaySeq) (n : ℕ) :
    hermiteCoeffNd (d' + 1) ((multiIndexEquiv d').symm n)
      (rapidDecay_schwartzMapNd d' a) = a.val n := by
  -- Rewrite the pointwise-tsum Schwartz map to the module-level tsum
  rw [show (rapidDecay_schwartzMapNd d' a : SchwartzMap _ _) =
      ∑' m, a.val m • flatBasisNd d' m from
    (rapidDecay_hermite_hasSumNd d' a).tsum_eq.symm]
  -- Push hermiteCoeffNd (as CLM) through the tsum
  rw [show hermiteCoeffNd (d' + 1) ((multiIndexEquiv d').symm n)
        (∑' m, a.val m • flatBasisNd d' m) =
      hermiteCoeffNdCLM (d' + 1) ((multiIndexEquiv d').symm n)
        (∑' m, a.val m • flatBasisNd d' m) from rfl,
    (hermiteCoeffNdCLM (d' + 1) ((multiIndexEquiv d').symm n)).map_tsum
      (rapidDecay_hermite_summableNd d' a)]
  -- Simplify: push CLM through smul, unfold flatBasisNd, apply Kronecker
  simp only [hermiteCoeffNdCLM_apply, map_smul, smul_eq_mul,
    flatBasisNd, hermiteCoeffNd_basisNd_kronecker]
  -- Use injectivity of multiIndexEquiv.symm to simplify the if-condition
  simp_rw [(multiIndexEquiv d').symm.injective.eq_iff]
  -- Flip `if n = m` to `if m = n` for tsum_ite_eq
  simp_rw [show ∀ m, (if n = m then (1 : ℝ) else 0) = if m = n then 1 else 0 from
    fun m => by split_ifs <;> simp_all]
  simp [mul_ite, mul_one, mul_zero, tsum_ite_eq]

/-- **Completeness of the multi-d Hermite expansion in Schwartz topology.**
Proved purely algebraically! The series converges to `S_f := from(to(f))`.
By the right inverse (Kronecker), `c_α(S_f) = c_α(f)` for all `α`.
By `hermiteCoeffNd_injective`, `S_f - f = 0`, so `S_f = f`.
-/
private lemma schwartz_hermite_completeness_nd (d' : ℕ)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin (d' + 1))) ℝ) :
    HasSum (fun n => hermiteCoeffNd (d' + 1) ((multiIndexEquiv d').symm n) f •
      flatBasisNd d' n) f := by
  set a := toRapidDecayNdLM d' f
  set S_f := fromRapidDecayNdLM d' a
  -- The expansion converges to S_f in Schwartz topology
  have h_sum : HasSum (fun n => a.val n • flatBasisNd d' n) S_f :=
    rapidDecay_hermite_hasSumNd d' a
  -- S_f = f because their Hermite coefficients agree (right inverse + injectivity)
  have h_eq : S_f = f := by
    have h_sub : S_f - f = 0 := by
      apply hermiteCoeffNd_injective d'
      intro α
      rw [(hermiteCoeffNd_linear (d' + 1) α).map_sub, sub_eq_zero]
      set n := multiIndexEquiv d' α
      have h_alpha : α = (multiIndexEquiv d').symm n :=
        ((multiIndexEquiv d').symm_apply_apply α).symm
      rw [h_alpha]
      have h_Sf := hermiteCoeffNd_rapidDecay_schwartzMapNd d' a n
      have h_a : a.val n = hermiteCoeffNd (d' + 1) ((multiIndexEquiv d').symm n) f := rfl
      rw [h_a] at h_Sf
      exact h_Sf
    exact sub_eq_zero.mp h_sub
  rwa [h_eq] at h_sum

/-- The d-dimensional Hermite topological isomorphism (for d = d' + 1 ≥ 1).
The `d' + 1` signature avoids the d=0 branch entirely —
`EuclideanSpace ℝ (Fin 0)` is topologically degenerate and never reached
because `Nontrivial D` forces `finrank ℝ D ≥ 1`.
-/
noncomputable def schwartzRapidDecayEquivNd (d' : ℕ) :
    SchwartzMap (EuclideanSpace ℝ (Fin (d' + 1))) ℝ ≃L[ℝ] RapidDecaySeq :=
  ContinuousLinearEquiv.equivOfInverse
    (toRapidDecayNdCLM (d' + 1))
    (fromRapidDecayNdCLM (d' + 1))
    -- Left inverse: from(to(f)) = f
    (fun f => by
      have h_f := schwartz_hermite_completeness_nd d' f
      have h_recon := rapidDecay_hermite_hasSumNd d' (toRapidDecayNdLM d' f)
      exact h_recon.unique h_f)
    -- Right inverse: to(from(a)) = a
    (fun a => by
      apply RapidDecaySeq.ext; intro n
      exact hermiteCoeffNd_rapidDecay_schwartzMapNd d' a n)

/-- The inverse of `schwartzRapidDecayEquivNd` evaluates pointwise as the Hermite series
reconstruction: `(equiv.symm a) x = ∑' n, a_n * Ψ_n(x)`.
-/
theorem schwartzRapidDecayEquivNd_symm_apply (d' : ℕ) (a : RapidDecaySeq)
    (x : EuclideanSpace ℝ (Fin (d' + 1))) :
    ((schwartzRapidDecayEquivNd d').symm a) x =
      ∑' n, a.val n * hermiteFunctionNd (d' + 1) ((multiIndexEquiv d').symm n) x := by
  -- The symm of equivOfInverse f₁ f₂ h₁ h₂ applies f₂
  simp only [schwartzRapidDecayEquivNd, ContinuousLinearEquiv.symm_equivOfInverse,
    ContinuousLinearEquiv.equivOfInverse_apply]
  -- Now the goal is fromRapidDecayNdCLM (d'+1) a x = tsum
  -- fromRapidDecayNdCLM (d'+1) for d'+1 ≥ 1 gives fromRapidDecayNdLM d' a
  -- which is rapidDecay_schwartzMapNd d' a
  show fromRapidDecayNdCLM (d' + 1) a x = _
  -- Unfold fromRapidDecayNdCLM to fromRapidDecayNdLM, then to rapidDecay_schwartzMapNd
  change rapidDecay_schwartzMapNd d' a x = _
  -- By definition, this is ∑' n, a.val n * flatBasisNd d' n x
  change ∑' n, a.val n * flatBasisNd d' n x = _
  -- flatBasisNd d' n = schwartzHermiteBasisNd (d'+1) ((multiIndexEquiv d').symm n)
  -- and schwartzHermiteBasisNd (d'+1) α x = hermiteFunctionNd (d'+1) α x
  rfl

/-- Pointwise summability of the multi-d Hermite series. -/
theorem schwartzRapidDecayEquivNd_summable (d' : ℕ) (a : RapidDecaySeq)
    (x : EuclideanSpace ℝ (Fin (d' + 1))) :
    Summable (fun n => a.val n * hermiteFunctionNd (d' + 1) ((multiIndexEquiv d').symm n) x) :=
  rapidDecay_pointwise_summableNd d' a x

/-- Pointwise norm summability of the multi-d Hermite series. -/
theorem schwartzRapidDecayEquivNd_norm_summable (d' : ℕ) (a : RapidDecaySeq)
    (x : EuclideanSpace ℝ (Fin (d' + 1))) :
    Summable (fun n => ‖a.val n * hermiteFunctionNd (d' + 1) ((multiIndexEquiv d').symm n) x‖) :=
  (schwartzRapidDecayEquivNd_summable d' a x).norm

/-- Pointwise summability of the 1D Hermite series. -/
theorem schwartzRapidDecayEquiv1D_summable (a : RapidDecaySeq) (t : ℝ) :
    Summable (fun n => a.val n * hermiteFunction n t) := by
  apply Summable.of_norm_bounded
    (g := fun n => |a.val n| * SchwartzMap.seminorm ℝ 0 0 (schwartzHermiteBasis1D n))
  · exact rapidDecay_seminorm_summable a 0 0
  · intro n
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left
      (by rw [← Real.norm_eq_abs, ← schwartzHermiteBasis1D_apply]
          exact SchwartzMap.norm_le_seminorm ℝ _ t)
      (abs_nonneg _)

/-- Pointwise norm summability of the 1D Hermite series. -/
theorem schwartzRapidDecayEquiv1D_norm_summable (a : RapidDecaySeq) (t : ℝ) :
    Summable (fun n => ‖a.val n * hermiteFunction n t‖) :=
  (schwartzRapidDecayEquiv1D_summable a t).norm

/-- The (d+2)-dimensional Hermite basis function, indexed via `multiIndexEquiv (d+1)`, factors
into a product along `euclideanInit` and `Fin.last` coordinates.

This is the key identity for proving that the inverse of `schwartzPeelOff` sends pure tensors
to pointwise products. It uses the decomposition of `multiIndexEquiv (d+1)` via Cantor
unpairing and the product structure of `hermiteFunctionNd`.
-/
theorem hermiteFunctionNd_unpair (d : ℕ) (n : ℕ)
    (x : EuclideanSpace ℝ (Fin (d + 2))) :
    hermiteFunctionNd (d + 2) ((multiIndexEquiv (d + 1)).symm n) x =
      hermiteFunctionNd (d + 1) ((multiIndexEquiv d).symm (Nat.unpair n).1)
        (euclideanInit (d + 1) x) *
      hermiteFunction (Nat.unpair n).2 (x (Fin.last (d + 1))) := by
  -- Use euclideanSnoc_init_last to decompose x, then apply hermiteFunctionNd_snoc
  -- and the multiIndexEquiv decomposition
  set α := (multiIndexEquiv (d + 1)).symm n
  -- Step 1: Rewrite x = euclideanSnoc (init x) (last x)
  conv_lhs => rw [← euclideanSnoc_init_last (d + 1) x]
  -- Step 2: Use hermiteFunctionNd_snoc to split the product
  rw [hermiteFunctionNd_snoc d α (euclideanInit (d + 1) x) (x (Fin.last (d + 1)))]
  -- Goal now: hermiteFunctionNd (d+1) (fun i => α (castSucc i)) (init x) *
  --           hermiteFunction (α (last (d+1))) (x (last (d+1)))
  --         = hermiteFunctionNd (d+1) (β) (init x) * hermiteFunction k (x (last (d+1)))
  -- Step 3: Show the multi-indices match using multiIndexEquiv_succ_symm
  have h_alpha := multiIndexEquiv_succ_symm d n
  congr 1
  · -- fun i => α (castSucc i) = (multiIndexEquiv d).symm (unpair n).1
    simp only [hermiteFunctionNd]
    apply Finset.prod_congr rfl
    intro j _
    congr 1
    -- α (castSucc j) = ((multiIndexEquiv d).symm (unpair n).1) j
    change ((multiIndexEquiv (d + 1)).symm n) (Fin.castSucc j) =
        ((multiIndexEquiv d).symm (Nat.unpair n).1) j
    conv_lhs => rw [h_alpha]
    -- succFunEquiv.symm (β, k) at castSucc j: this is β j
    simp only [Fin.succFunEquiv, Equiv.symm_trans_apply, Equiv.prodCongrRight_symm,
      Equiv.prodCongrRight_apply]
    -- Goal should now involve Fin.appendEquiv or Fin.append with castAdd
    rw [show Fin.castSucc j = Fin.castAdd 1 j from rfl]
    simp [Fin.append_left]
  · -- α (last (d+1)) = (unpair n).2
    congr 1
    change ((multiIndexEquiv (d + 1)).symm n) (Fin.last (d + 1)) = (Nat.unpair n).2
    conv_lhs => rw [h_alpha]
    -- Need: (succFunEquiv.symm (β, k)) (Fin.last (d+1)) = k
    -- Key: succFunEquiv applied to the inverse gives back (β, k)
    set f := (Fin.succFunEquiv ℕ (d + 1)).symm
      ((multiIndexEquiv d).symm (Nat.unpair n).1, (Nat.unpair n).2)
    -- f is the function whose succFunEquiv image is (β, k)
    have hf : (Fin.succFunEquiv ℕ (d + 1) f).2 = (Nat.unpair n).2 :=
      congr_arg Prod.snd (Equiv.apply_symm_apply _ _)
    -- But (succFunEquiv f).2 involves f applied via funUnique, which extracts f (Fin.last)
    -- succFunEquiv = (appendEquiv n 1).symm.trans (prodCongrRight ...) so
    -- (succFunEquiv f).2 = Equiv.funUnique (Fin 1) ℕ (appendEquiv n 1 f).2
    -- = (appendEquiv n 1 f).2 0 = f (natAdd n 0) = f (last n)
    -- We just use simp to resolve the computed form
    simp only [Fin.succFunEquiv, Equiv.trans_apply] at hf
    exact hf

/-- Schwartz space isomorphism for `EuclideanSpace ℝ (Fin d)` with `d ≥ 1`.
- For `d = 1`: reduces to `SchwartzMap ℝ ℝ` via `euclideanFin1Equiv`,
  then uses `schwartzRapidDecayEquiv1D`.
- For `d ≥ 2`: uses the generalized `schwartzRapidDecayEquivNd`.
-/
noncomputable def schwartzRapidDecayEquivFin (d : ℕ) (hd : 0 < d) :
    SchwartzMap (EuclideanSpace ℝ (Fin d)) ℝ ≃L[ℝ] RapidDecaySeq :=
  match d, hd with
  | 1, _ => (schwartzDomCongr euclideanFin1Equiv).symm.trans schwartzRapidDecayEquiv1D
  | d' + 2, _ => schwartzRapidDecayEquivNd (d' + 1)

/-- The Schwartz space on any nontrivial finite-dimensional real normed space is
topologically linearly isomorphic to the space of rapidly decreasing sequences.

The proof decomposes as:
  `SchwartzMap D ℝ ≃L SchwartzMap (EuclideanSpace ℝ (Fin d)) ℝ ≃L RapidDecaySeq`
where `d = finrank ℝ D ≥ 1` (from `Nontrivial D`).

**Sorry**: sorrys for `d ≥ 2` are decomposed into multi-index Hermite analysis components.
count_axioms:skip
The 1D forward and backward maps and all structural components are fully proved.
-/
noncomputable def schwartzRapidDecayEquiv (D : Type*)
    [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D] [Nontrivial D] :
    SchwartzMap D ℝ ≃L[ℝ] RapidDecaySeq :=
  have hd : 0 < Module.finrank ℝ D := Module.finrank_pos
  (schwartzDomCongr (toEuclidean (E := D))).symm.trans
    (schwartzRapidDecayEquivFin (Module.finrank ℝ D) hd)

end GaussianField
