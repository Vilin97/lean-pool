/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.Potentials
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.ExtensionNormTransport
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.CZInputs

/-! # Weak gradients selected from the actual indexed extension

The completed L^(6/5) operator supplies its own membership and numerical
bound. Its positive pairing with the first potential selects the negatively
signed weak gradient, without any classical representative identification.
-/

@[expose] public section

section

/-! # Weak pressure gradients from indexed extension bounds

The negatively signed extension supplies a weak gradient of the first
Newtonian derivative potential. Only distributional pairings and Lp bounds
are used; no classical derivative of a rough representative is identified.
-/

open MeasureTheory Filter
open scoped ENNReal BigOperators
open CKN.Foundation.Parabolic

noncomputable section
namespace CKN.Core.Endgame

private theorem norm_le_sum_abs (v : Vec3) : ‖v‖ ≤ ∑ i : Fin 3, |v i| := by
  rw [Pi.norm_def]
  have hs : Finset.univ.sup (fun i : Fin 3 => ‖v i‖₊) ≤ ∑ i : Fin 3, ‖v i‖₊ := by
    apply Finset.sup_le
    intro i _
    exact Finset.single_le_sum (fun j _ => (‖v j‖₊).2) (Finset.mem_univ i)
  exact_mod_cast hs

private theorem eLpNorm_le_sum_components {D : Vec3 → Vec3} {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hD : AEStronglyMeasurable D volume) :
    eLpNorm D p volume ≤ ∑ j : Fin 3, eLpNorm (fun x => D x j) p volume := by
  calc
    _ ≤ eLpNorm (fun x => ∑ j : Fin 3, |D x j|) p volume := by
      apply eLpNorm_mono_ae_real hD
      exact Eventually.of_forall fun x => norm_le_sum_abs (D x)
    _ ≤ ∑ j : Fin 3, eLpNorm (fun x => |D x j|) p volume := by
      change eLpNorm (∑ j : Fin 3, fun x => |D x j|) p volume ≤ _
      exact eLpNorm_sum_le hp
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      have hj := (ContinuousLinearMap.proj (R := ℝ) j).continuous.comp_aestronglyMeasurable hD
      simpa only [Real.norm_eq_abs] using (eLpNorm_norm (fun x => D x j) hj)

/-- Actual component membership, bounds, and positive extension pairings
give the weak gradient with the negative sign and a uniform vector bound. -/
theorem exists_weak_pressure_gradient_of_extension
    (Ccomp C_CZ : ℝ) (hCcomp : 0 ≤ Ccomp) (hconst : 3 * Ccomp ≤ C_CZ)
    (T : Fin 3 → Fin 3 → (Vec3 → ℝ) → Vec3 → ℝ)
    (hmem : ∀ i j (G : Vec3 → ℝ),
      MemLp G (ENNReal.ofReal (6 / 5 : ℝ)) volume → HasCompactSupport G →
      MemLp (T i j G) (ENNReal.ofReal (6 / 5 : ℝ)) volume)
    (hbound : ∀ i j (G : Vec3 → ℝ),
      MemLp G (ENNReal.ofReal (6 / 5 : ℝ)) volume → HasCompactSupport G →
      eLpNorm (T i j G) (ENNReal.ofReal (6 / 5 : ℝ)) volume ≤
        ENNReal.ofReal Ccomp * eLpNorm G (ENNReal.ofReal (6 / 5 : ℝ)) volume)
    (hpair : ∀ i j (G : Vec3 → ℝ),
      MemLp G (ENNReal.ofReal (6 / 5 : ℝ)) volume → HasCompactSupport G →
      ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      (∫ x, pressureNewtonianDerivativePotential i G x * spatialDeriv ψ j x) =
        ∫ x, T i j G x * ψ x) :
    ∀ (i : Fin 3) (G : Vec3 → ℝ),
      MemLp G (ENNReal.ofReal (6 / 5 : ℝ)) volume → HasCompactSupport G →
      ∃ D : Vec3 → Vec3,
        MemLp D (ENNReal.ofReal (6 / 5 : ℝ)) volume ∧
        (∀ (j : Fin 3) (ψ : Vec3 → ℝ),
          ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
          (∫ x, pressureNewtonianDerivativePotential i G x * spatialDeriv ψ j x) =
            -(∫ x, D x j * ψ x)) ∧
        eLpNorm D (ENNReal.ofReal (6 / 5 : ℝ)) volume ≤
          ENNReal.ofReal C_CZ * eLpNorm G (ENNReal.ofReal (6 / 5 : ℝ)) volume := by
  intro i G hG hGc
  let D : Vec3 → Vec3 := fun x j => -T i j G x
  have hDmeas : AEStronglyMeasurable D volume := by
    apply AEMeasurable.aestronglyMeasurable
    apply AEMeasurable.of_eval
    intro j
    exact (hmem i j G hG hGc).aestronglyMeasurable.neg.aemeasurable
  have hDN : eLpNorm D (ENNReal.ofReal (6 / 5 : ℝ)) volume ≤
      ENNReal.ofReal C_CZ * eLpNorm G (ENNReal.ofReal (6 / 5 : ℝ)) volume := by
    calc
      _ ≤ ∑ j : Fin 3, eLpNorm (fun x => D x j) (ENNReal.ofReal (6 / 5 : ℝ)) volume :=
        eLpNorm_le_sum_components (by norm_num) hDmeas
      _ ≤ ∑ _j : Fin 3, ENNReal.ofReal Ccomp * eLpNorm G
          (ENNReal.ofReal (6 / 5 : ℝ)) volume := by
        apply Finset.sum_le_sum
        intro j _
        change eLpNorm (-T i j G) _ _ ≤ _
        rw [eLpNorm_neg]
        exact hbound i j G hG hGc
      _ = ENNReal.ofReal (3 * Ccomp) * eLpNorm G (ENNReal.ofReal (6 / 5 : ℝ)) volume := by
        rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul,
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
        norm_num only [ENNReal.ofReal_ofNat]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hconst) (by positivity)
  have hCCZ : 0 ≤ C_CZ := (mul_nonneg (by norm_num) hCcomp).trans hconst
  have hDmem : MemLp D (ENNReal.ofReal (6 / 5 : ℝ)) volume :=
    hDN.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hG.eLpNorm_lt_top)
  refine ⟨D, hDmem, ?_, hDN⟩
  intro j ψ hψ hψc
  rw [hpair i j G hG hGc ψ hψ hψc]
  change (∫ x, T i j G x * ψ x) = -(∫ x, (-T i j G x) * ψ x)
  simp only [neg_mul, integral_neg, neg_neg]


end CKN.Core.Endgame
end

end

open MeasureTheory Filter
open scoped ENNReal
open CKN.Foundation.Parabolic CKN.Foundation.Euclidean

noncomputable section
namespace CKN.Core.Endgame

/-- The actual indexed extension produces the required weak-gradient
output once its distributional pairing is supplied. -/
theorem exists_weak_pressure_gradient_of_riesz_extension
    (C_CZ : ℝ)
    (hconst : 3 * czGradientComponentConstant rieszSecondWeakTypeConstant 1 ≤ C_CZ)
    (hL2 : ∀ i j : Fin 3, RieszSecondL2Input i j)
    (hWeak11 : ∀ i j f, Measurable f → Integrable f volume → MemLp f 2 volume →
      ∀ l : ℝ, 0 < l →
        volume {x | l < |rieszSecondL2RawOperator (hL2 i j) f x|} ≤
          ENNReal.ofReal rieszSecondWeakTypeConstant *
            (∫⁻ x, absE f x) / ENNReal.ofReal l)
    (hpair : ∀ i j (G : Vec3 → ℝ),
      MemLp G (ENNReal.ofReal (6 / 5 : ℝ)) volume → HasCompactSupport G →
      ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      (∫ x, pressureNewtonianDerivativePotential i G x * spatialDeriv ψ j x) =
        ∫ x, rieszSecondGradientExtensionOperator (hL2 i j) (hWeak11 i j) G x * ψ x) :
    ∀ (i : Fin 3) (G : Vec3 → ℝ),
      MemLp G (ENNReal.ofReal (6 / 5 : ℝ)) volume → HasCompactSupport G →
      ∃ D : Vec3 → Vec3,
        MemLp D (ENNReal.ofReal (6 / 5 : ℝ)) volume ∧
        (∀ (j : Fin 3) (ψ : Vec3 → ℝ),
          ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
          (∫ x, pressureNewtonianDerivativePotential i G x * spatialDeriv ψ j x) =
            -(∫ x, D x j * ψ x)) ∧
        eLpNorm D (ENNReal.ofReal (6 / 5 : ℝ)) volume ≤
          ENNReal.ofReal C_CZ * eLpNorm G (ENNReal.ofReal (6 / 5 : ℝ)) volume := by
  have hC : 0 ≤ czGradientComponentConstant rieszSecondWeakTypeConstant 1 :=
    ENNReal.toReal_nonneg
  apply exists_weak_pressure_gradient_of_extension
    (czGradientComponentConstant rieszSecondWeakTypeConstant 1) C_CZ hC hconst
    (fun i j => rieszSecondGradientExtensionOperator (hL2 i j) (hWeak11 i j))
    (fun i j G hG hGc => rieszSecondGradientExtension_memLp (hL2 i j) (hWeak11 i j) hG hGc)
    ?_ hpair
  intro i j G hG hGc
  exact eLpNorm_le_of_toLp_norm_le hG
    (rieszSecondGradientExtension_memLp (hL2 i j) (hWeak11 i j) hG hGc) hC
    (rieszSecondGradientExtension_toLp_bound (hL2 i j) (hWeak11 i j) hG hGc)

end CKN.Core.Endgame
