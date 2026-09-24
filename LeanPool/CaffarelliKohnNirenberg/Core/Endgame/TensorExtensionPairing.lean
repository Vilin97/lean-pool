/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.ExtensionPairing

/-! # Distributional pairing for the tensor-indexed pressure extension

The nine completed scalar identities sum to the pressure identity. Hölder
integrability justifies the finite-sum interchanges without compact support
of the tensor inputs or any condition on chosen Lp representatives.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal Topology BigOperators
open CKN.Foundation.Parabolic CKN.Foundation.Euclidean

noncomputable section
namespace CKN.Core.Endgame

private theorem derivative_compact {f : Vec3 → ℝ}
    (hf : HasCompactSupport f) (i : Fin 3) : HasCompactSupport (spatialDeriv f i) := by
  exact hf.fderiv_apply (𝕜 := ℝ) (basisVec i)

/-- The tensor sum of the actual completed operators satisfies the
distributional pressure identity for arbitrary L^(3/2) component inputs. -/
theorem rieszSecondP1ExtensionTensor_distributional_identity
    (hL2 : ∀ i j : Fin 3, RieszSecondL2Input i j)
    (hWeak11 : ∀ i j : Fin 3, ∀ f, Measurable f → Integrable f volume →
      MemLp f 2 volume → ∀ l : ℝ, 0 < l →
        volume {x | l < |rieszSecondL2RawOperator (hL2 i j) f x|} ≤
          ENNReal.ofReal rieszSecondWeakTypeConstant *
            (∫⁻ x, absE f x) / ENNReal.ofReal l)
    {G : Fin 3 → Fin 3 → Vec3 → ℝ}
    (hG : ∀ i j, MemLp (G i j) (ENNReal.ofReal (3 / 2 : ℝ)) volume)
    {ψ : Vec3 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    (∫ x, (∑ i, ∑ j, rieszSecondP1ExtensionOperator (hL2 i j) (hWeak11 i j)
      (G i j) x) * spatialLaplacian ψ x) =
        ∫ x, ∑ i, ∑ j, G i j x * mixedSecond ψ i j x := by
  let : Fact (1 ≤ ENNReal.ofReal (3 / 2 : ℝ)) := ⟨by norm_num⟩
  let : Fact (1 ≤ ENNReal.ofReal (3 : ℝ)) := ⟨by norm_num⟩
  let : ENNReal.HolderConjugate (ENNReal.ofReal (3 / 2 : ℝ)) (ENNReal.ofReal 3) :=
    (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩ :
      Real.HolderConjugate (3 / 2 : ℝ) 3).ennrealOfReal
  have hlapc : HasCompactSupport (spatialLaplacian ψ) := by
    change HasCompactSupport (fun x => ∑ k : Fin 3, spatialDeriv (spatialDeriv ψ k) k x)
    convert
      ((derivative_compact (derivative_compact hψc 0) 0).add
        ((derivative_compact (derivative_compact hψc 1) 1).add
          (derivative_compact (derivative_compact hψc 2) 2))) using 1
    funext x
    simp [Fin.sum_univ_succ, Pi.add_apply]
  have hlap : MemLp (spatialLaplacian ψ) (ENNReal.ofReal (3 : ℝ)) volume :=
    (contDiff_spatialLaplacian_smooth hψ).continuous.memLp_of_hasCompactSupport hlapc
  have hrhs (i j : Fin 3) : MemLp (mixedSecond ψ i j) (ENNReal.ofReal (3 : ℝ)) volume :=
    (contDiff_mixedSecond_smooth hψ i j).continuous.memLp_of_hasCompactSupport
      (derivative_compact (derivative_compact hψc j) i)
  let T (i j : Fin 3) := rieszSecondP1ExtensionOperator (hL2 i j) (hWeak11 i j) (G i j)
  have hT (i j : Fin 3) : MemLp (T i j) (ENNReal.ofReal (3 / 2 : ℝ)) volume :=
    lpExtensionRepresentative_memLp (by norm_num)
      (rieszSecondP1ExtensionInput (hL2 i j) (hWeak11 i j)) (hG i j)
  have hleft (i j : Fin 3) : Integrable (fun x => T i j x * spatialLaplacian ψ x) volume :=
    (hT i j).integrable_mul hlap
  have hright (i j : Fin 3) : Integrable (fun x => G i j x * mixedSecond ψ i j x) volume :=
    (hG i j).integrable_mul (hrhs i j)
  change (∫ x, (∑ i, ∑ j, T i j x) * spatialLaplacian ψ x) = _
  simp_rw [Finset.sum_mul]
  rw [integral_finsetSum Finset.univ
    (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hleft i j)),
    integral_finsetSum Finset.univ
      (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hright i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum Finset.univ (fun j _ => hleft i j),
    integral_finsetSum Finset.univ (fun j _ => hright i j)]
  apply Finset.sum_congr rfl
  intro j _
  exact rieszSecondP1Extension_distributional_identity (hL2 i j) (hWeak11 i j) (hG i j) hψ hψc

end CKN.Core.Endgame
