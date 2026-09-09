/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.LpFiniteTensorReconstruction
public import LeanPool.NavierStokesAndEuler.Euler.LpSmoothField
public import LeanPool.NavierStokesAndEuler.Euler.MeanCutoffCurlBound
public import LeanPool.NavierStokesAndEuler.Euler.MeanHarmonicDerivatives
import LeanPool.NavierStokesAndEuler.Euler.DivCurlRecovery
import LeanPool.NavierStokesAndEuler.Euler.LpBochnerRealization
import LeanPool.NavierStokesAndEuler.Euler.TensorCoordinateEnergyBound
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-! Recover the actual all-order L² Fréchet tensors from scalar coordinate
derivatives. The derivative hypotheses used here are consequences of compact
vorticity, ordinary smoothness, and finite velocity energy. -/

@[expose] public section


noncomputable section


namespace EulerComparatorRecovery

open MeasureTheory EulerSmoothLimit EulerVectorCalculus EulerMeanHarmonic
  EulerLpTranslation EulerLpFiniteTensor EulerMeanCutoffCurl
open scoped ContDiff Topology

/-- List coordinate derivatives agree with the ordinary Fréchet tensor
evaluated on the corresponding sequence of coordinate directions. -/
theorem iteratedFDeriv_coordinate_word (n : ℕ) (w : Fin n → Fin 3)
    (h : Space → ℝ) (hh : ContDiff ℝ ∞ h) (x : Space) :
    iteratedFDeriv ℝ n h x (fun i => direction (w i)) =
      wordDerivative (List.ofFn w) h x := by
  induction n generalizing x with
  | zero => simp [wordDerivative]
  | succ n ih =>
    have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ n h) x :=
      ((hh.iteratedFDeriv_right (m := ∞) (by simp)).differentiable (by simp)).differentiableAt
    rw [hd.iteratedFDeriv_succ_apply_left']
    have he : (fun y => iteratedFDeriv ℝ n h y
        (Fin.tail (fun i => direction (w i)))) = wordDerivative (List.ofFn (Fin.tail w)) h := by
      funext y
      exact ih (Fin.tail w) y
    rw [he, List.ofFn_succ]
    rfl

/-- Coordinate projection commutes with the actual iterated Fréchet derivative. -/
theorem iteratedFDeriv_component (n : ℕ) (u : Space → Space)
    (hu : ContDiff ℝ ∞ u) (x : Space) (m : Fin n → Space) (j : Fin 3) :
    iteratedFDeriv ℝ n (fun y => u y j) x m = (iteratedFDeriv ℝ n u x m) j := by
  have he := (EuclideanSpace.proj j : Space →L[ℝ] ℝ).iteratedFDeriv_comp_left
    (hu.contDiffAt (x := x)) (i := n) (by simp)
  exact congrArg (fun A : Space [×n]→L[ℝ] ℝ => A m) he

/-- Every coordinate evaluation of the Fréchet tensor is in L². -/
theorem iteratedFDeriv_coordinate_memLp (u : Space → Space)
    (hu : ContDiff ℝ ∞ u) (hL2 : MemLp u 2 volume)
    (hdiv : ∀ x, divergence u x = 0) (hc : HasCompactSupport (vectorCurl u))
    (n : ℕ) (w : Fin n → Fin 3) :
    MemLp (fun x => iteratedFDeriv ℝ n u x (fun i => direction (w i))) 2 volume := by
  apply MemLp.of_eval_piLp
  intro j
  have he : (fun x => (iteratedFDeriv ℝ n u x (fun i => direction (w i))) j) =
      wordDerivative (List.ofFn w) (fun x => u x j) := by
    funext x
    rw [← iteratedFDeriv_component n u hu x _ j]
    exact iteratedFDeriv_coordinate_word n w _ ((contDiff_piLp 2).mp hu j) x
  rw [he]
  exact component_wordDerivative_memLp u hu hL2 hdiv hc j (List.ofFn w)

/-- Smooth finite-energy divergence-free velocity with compact vorticity
has all its actual Fréchet derivatives in L². -/
theorem iteratedFDeriv_memLp_of_curl_compact (u : Space → Space)
    (hu : ContDiff ℝ ∞ u) (hL2 : MemLp u 2 volume)
    (hdiv : ∀ x, divergence u x = 0) (hc : HasCompactSupport (vectorCurl u))
    (n : ℕ) : MemLp (iteratedFDeriv ℝ n u) 2 volume := by
  have ht : MemLp (fun x => tensorCoordinates n (iteratedFDeriv ℝ n u x)) 2 volume := by
    apply MemLp.of_eval
    intro w
    exact iteratedFDeriv_coordinate_memLp u hu hL2 hdiv hc n w
  have hr := (tensorReassembly (V := Space) n).comp_memLp' ht
  simpa only [Function.comp_def, tensorReassembly_coordinates] using hr

/-- The derivative class used by the development follows from ordinary
smoothness, finite energy, solenoidality, and compact vorticity. -/
def smoothL2FieldOfCurlCompact (u : Space → Space)
    (hu : ContDiff ℝ ∞ u) (hL2 : MemLp u 2 volume)
    (hdiv : ∀ x, divergence u x = 0) (hc : HasCompactSupport (vectorCurl u)) :
    SmoothL2Field Space where
  field := u
  smooth := hu
  integrable := iteratedFDeriv_memLp_of_curl_compact u hu hL2 hdiv hc

/-- The literal tensor energy is controlled by finitely many scalar coordinate
energies. The constant is fixed by the derivative order alone. -/
theorem tensor_integral_norm_sq_le_coordinate_energy (n : ℕ)
    (F : Space → (Space [×n]→L[ℝ] Space)) (hF : MemLp F 2 volume) :
    (∫ x, ‖F x‖ ^ 2) ≤ ‖tensorReassembly (V := Space) n‖ ^ 2 *
      ∑ w : Fin n → Fin 3, ∑ j : Fin 3,
        ∫ x, (F x (fun i => direction (w i)) j) ^ 2 := by
  have hcoord (w : Fin n → Fin 3) (j : Fin 3) :
      Integrable (fun x => (F x (fun i => direction (w i)) j) ^ 2) := by
    have ht := ((tensorCoordinates (V := Space) n).comp_memLp' hF).eval w
    exact (ht.eval_piLp j).integrable_sq
  have hsum (w : Fin n → Fin 3) : Integrable
      (fun x => ∑ j : Fin 3, (F x (fun i => direction (w i)) j) ^ 2) :=
    integrable_finsetSum Finset.univ (fun j _ => hcoord w j)
  calc
    (∫ x, ‖F x‖ ^ 2) ≤ ∫ x, ‖tensorReassembly (V := Space) n‖ ^ 2 *
        ∑ w : Fin n → Fin 3, ∑ j : Fin 3,
          (F x (fun i => direction (w i)) j) ^ 2 :=
      integral_mono ((memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).mp hF)
        ((integrable_finsetSum Finset.univ (fun w _ => hsum w)).const_mul _)
        (fun x => tensor_norm_sq_le_coordinate_energy n (F x))
    _ = _ := by
      rw [integral_const_mul, integral_finsetSum Finset.univ (fun w _ => hsum w)]
      congr 1
      apply Finset.sum_congr rfl
      intro w _
      exact integral_finsetSum Finset.univ (fun j _ => hcoord w j)

/-- The L² class of a smooth field's tensor has exactly its ordinary integral
energy, so quantitative recovery applies to the development's norm. -/
theorem jetLp_norm_sq_eq_integral (A : SmoothL2Field Space) (n : ℕ) :
    ‖A.jetLp n‖ ^ 2 = ∫ x, ‖iteratedFDeriv ℝ n A.field x‖ ^ 2 := by
  rw [EulerLpBochnerRealization.norm_sq_eq_integral]
  apply integral_congr_ae
  filter_upwards [(A.integrable n).coeFn_toLp] with x hx
  exact congrArg (fun v : Space [×n]→L[ℝ] Space => ‖v‖ ^ 2) hx

/-- Uniform bounds for scalar coordinate-word energies yield uniform L²
norms of the actual Fréchet tensors over an arbitrary parameter set. -/
theorem jetLp_norm_uniform_of_coordinate_energy {ι : Type*}
    (A : ι → SmoothL2Field Space)
    (henergy : ∀ (j : Fin 3) (word : List (Fin 3)), ∃ B : ℝ,
      ∀ t, (∫ x, wordDerivative word (fun y => (A t).field y j) x ^ 2) ≤ B)
    (n : ℕ) : ∃ M : ℝ, ∀ t, ‖(A t).jetLp n‖ ≤ M := by
  classical
  choose B hB using fun (w : Fin n → Fin 3) (j : Fin 3) => henergy j (List.ofFn w)
  let C : ℝ := ‖tensorReassembly (V := Space) n‖ ^ 2 *
    ∑ w : Fin n → Fin 3, ∑ j : Fin 3, B w j
  refine ⟨Real.sqrt (max C 0), fun t => ?_⟩
  apply (Real.le_sqrt (norm_nonneg _) (le_max_right C 0)).mpr
  apply le_trans _ (le_max_left C 0)
  rw [jetLp_norm_sq_eq_integral]
  apply (tensor_integral_norm_sq_le_coordinate_energy n _ ((A t).integrable n)).trans
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  apply Finset.sum_le_sum
  intro w _
  apply Finset.sum_le_sum
  intro j _
  have he : (fun x => (iteratedFDeriv ℝ n (A t).field x
      (fun i => direction (w i)) j) ^ 2) =
      (fun x => wordDerivative (List.ofFn w) (fun y => (A t).field y j) x ^ 2) := by
    funext x
    rw [← iteratedFDeriv_component n (A t).field (A t).smooth x _ j,
      iteratedFDeriv_coordinate_word n w _ ((contDiff_piLp 2).mp (A t).smooth j) x]
  rw [he]
  exact hB w j t

end EulerComparatorRecovery
