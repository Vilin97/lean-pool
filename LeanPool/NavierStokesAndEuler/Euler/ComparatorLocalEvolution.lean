/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.ComparatorEvolutionIdentification
public import LeanPool.NavierStokesAndEuler.Euler.ClassicalBridge
import LeanPool.NavierStokesAndEuler.Euler.CompactProjectedEulerLaw
import LeanPool.NavierStokesAndEuler.Euler.CompactVorticityTimeUpgrade
import LeanPool.NavierStokesAndEuler.Euler.ComparatorLocalCompactVorticity
import LeanPool.NavierStokesAndEuler.Euler.ScalarEulerVorticity
public import LeanPool.NavierStokesAndEuler.Euler.MeanCutoffCurlBound
public import LeanPool.NavierStokesAndEuler.Euler.MeanHarmonicDerivatives
public import LeanPool.NavierStokesAndEuler.Euler.SolutionDefinitions
import LeanPool.NavierStokesAndEuler.Euler.DivCurlRecovery
import LeanPool.NavierStokesAndEuler.Euler.MeanVectorIdentities
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import LeanPool.NavierStokesAndEuler.Euler.MeanHarmonicLaplacian
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
public import LeanPool.NavierStokesAndEuler.Euler.LpFiniteTensorReconstruction
public import LeanPool.NavierStokesAndEuler.Euler.LpSmoothField
import LeanPool.NavierStokesAndEuler.Euler.LpBochnerRealization
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-!
# The concrete local Comparator-to-development conversion

Compact initial vorticity remains in one compact set for a positive time.
Elliptic recovery gives all spatial L² derivatives on that interval, and
the genuine Euler pairings against dense compact solenoidal tests provide
the time regularity needed for an ordinary Euler evolution.
-/

section

/-! Recover the actual all-order L² Fréchet tensors from scalar coordinate
derivatives. The derivative hypotheses used here are consequences of compact
vorticity, ordinary smoothness, and finite velocity energy. -/

section

/-!
# Bounding a tensor by the energies of its coordinate evaluations

The reconstruction map is fixed in each derivative order.  Its operator norm
therefore gives a finite constant converting the sum of the scalar coordinate
energies into a bound for the literal tensor norm.
-/

@[expose] public section

noncomputable section

namespace EulerComparatorRecovery

open EulerSmoothLimit EulerLpFiniteTensor

/-- The product norm of finitely many Euclidean vectors is bounded by their
combined scalar coordinate energy. -/
theorem tuple_norm_sq_le_coordinate_energy {ι : Type*} [Fintype ι]
    (v : ι → Space) :
    ‖v‖ ^ 2 ≤ ∑ i : ι, ∑ j : Fin 3, (v i j) ^ 2 := by
  classical
  let S : ℝ := ∑ i : ι, ∑ j : Fin 3, (v i j) ^ 2
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hnorm : ‖v‖ ≤ Real.sqrt S := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg S)).mpr
    intro i
    apply (Real.le_sqrt (norm_nonneg _) hS).mpr
    rw [EuclideanSpace.real_norm_sq_eq]
    exact Finset.single_le_sum
      (fun k _ => Finset.sum_nonneg fun j _ => sq_nonneg (v k j))
      (Finset.mem_univ i)
  calc
    ‖v‖ ^ 2 ≤ (Real.sqrt S) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg S)).mpr hnorm
    _ = S := Real.sq_sqrt hS

/-- A tensor's squared operator norm is bounded by the sum of the squared
scalar coordinate evaluations, with a constant depending only on its order. -/
theorem tensor_norm_sq_le_coordinate_energy (n : ℕ)
    (A : Space [×n]→L[ℝ] Space) :
    ‖A‖ ^ 2 ≤ ‖tensorReassembly (V := Space) n‖ ^ 2 *
      ∑ w : Fin n → Fin 3, ∑ j : Fin 3,
        (A (fun i => direction (w i)) j) ^ 2 := by
  have hnorm : ‖A‖ ≤ ‖tensorReassembly (V := Space) n‖ *
      ‖tensorCoordinates n A‖ := by
    simpa only [tensorReassembly_coordinates] using
      (tensorReassembly (V := Space) n).le_opNorm (tensorCoordinates n A)
  have hsq : ‖A‖ ^ 2 ≤ ‖tensorReassembly (V := Space) n‖ ^ 2 *
      ‖tensorCoordinates n A‖ ^ 2 := by
    simpa only [mul_pow] using
      (sq_le_sq₀ (norm_nonneg A)
        (mul_nonneg (norm_nonneg (tensorReassembly (V := Space) n))
          (norm_nonneg (tensorCoordinates n A)))).mpr hnorm
  exact hsq.trans (mul_le_mul_of_nonneg_left
    (tuple_norm_sq_le_coordinate_energy (tensorCoordinates n A)) (sq_nonneg _))

end EulerComparatorRecovery

end
end

end

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

end
end

end

section

/-! Joint spatial coordinate derivatives and uniform energy bounds for
families supported in a fixed compact set. -/

@[expose] public section

noncomputable section

open Set MeasureTheory Laplacian EulerSmoothLimit EulerVectorCalculus EulerMeanHarmonic
open scoped ContDiff Topology

namespace EulerComparatorRecovery

theorem joint_scalar_partialDerivative_contDiffOn
    {u : ℝ × Space → ℝ} {S : Set ℝ}
    (hu : ContDiffOn ℝ ∞ u (S ×ˢ (univ : Set Space))) (i : Fin 3) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Space =>
      partialDerivative (fun y => u (z.1, y)) i z.2) (S ×ˢ (univ : Set Space)) := by
  have hd : ContDiffOn ℝ ∞ (fun z : ℝ × Space =>
      fderiv ℝ (fun y => u (z.1, y)) z.2) (S ×ˢ (univ : Set Space)) := by
    intro z hz
    have hf : ContDiffWithinAt ℝ ∞
        (fun q : (ℝ × Space) × Space => u (q.1.1, q.2))
        ((S ×ˢ (univ : Set Space)) ×ˢ (univ : Set Space)) (z, z.2) := by
      apply (hu z hz).comp (z, z.2)
        (contDiffWithinAt_fst.fst.prodMk contDiffWithinAt_snd)
      intro q hq
      exact ⟨hq.1.1, mem_univ _⟩
    have hf' := ContDiffWithinAt.fderivWithin
      (𝕜 := ℝ) (n := ∞) (m := ∞)
      (f := fun (z : ℝ × Space) (y : Space) => u (z.1, y))
      (s := S ×ˢ (univ : Set Space)) (t := (univ : Set Space))
      (g := fun z : ℝ × Space => z.2)
      hf contDiffWithinAt_snd uniqueDiffOn_univ (by simp) hz
      (by intro z hz; exact mem_univ _)
    simpa only [fderivWithin_univ] using hf'
  exact hd.clm_apply contDiffOn_const

theorem joint_wordDerivative_contDiffOn
    {u : ℝ × Space → ℝ} {S : Set ℝ}
    (hu : ContDiffOn ℝ ∞ u (S ×ˢ (univ : Set Space))) (word : List (Fin 3)) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Space =>
      wordDerivative word (fun y => u (z.1, y)) z.2) (S ×ˢ (univ : Set Space)) := by
  induction word with
  | nil => exact hu
  | cons i word ih => exact joint_scalar_partialDerivative_contDiffOn ih i

theorem joint_scalar_laplacian_contDiffOn
    {u : ℝ × Space → ℝ} {S : Set ℝ}
    (hu : ContDiffOn ℝ ∞ u (S ×ˢ (univ : Set Space))) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Space => Δ (fun y => u (z.1, y)) z.2)
      (S ×ˢ (univ : Set Space)) := by
  have hd : ContDiffOn ℝ ∞ (fun z : ℝ × Space => ∑ i : Fin 3,
      partialDerivative (partialDerivative (fun y => u (z.1, y)) i) i z.2)
      (S ×ˢ (univ : Set Space)) :=
    ContDiffOn.sum (fun i _ => joint_scalar_partialDerivative_contDiffOn
      (joint_scalar_partialDerivative_contDiffOn hu i) i)
  apply hd.congr
  intro z hz
  have hs : ContDiff ℝ ∞ (fun y => u (z.1, y)) :=
    hu.comp_contDiff (contDiff_const.prodMk contDiff_id) (fun y => ⟨hz.1, mem_univ _⟩)
  exact laplacian_eq_coordinate_sum _ hs z.2

theorem tsupport_wordDerivative_subset (word : List (Fin 3)) (f : Space → ℝ) :
    tsupport (wordDerivative word f) ⊆ tsupport f := by
  induction word with
  | nil => exact Subset.rfl
  | cons i word ih =>
    exact (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1)).trans ih

theorem uniform_energy_of_compact_support
    {E : Type*} [NormedAddCommGroup E]
    (f : ℝ × Space → E) (T : ℝ) (K : Set Space) (hK : IsCompact K)
    (hf : ContinuousOn f (Icc (0 : ℝ) T ×ˢ K))
    (hsupport : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∉ K, f (t, x) = 0) :
    ∃ B : ℝ, ∀ t ∈ Icc (0 : ℝ) T, (∫ x, ‖f (t, x)‖ ^ 2) ≤ B := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn hf
  refine ⟨(max C 0) ^ 2 * volume.real K, ?_⟩
  intro t ht
  have hind : (fun x => ‖f (t, x)‖ ^ 2) =
      K.indicator (fun x => ‖f (t, x)‖ ^ 2) := by
    funext x
    by_cases hx : x ∈ K
    · simp only [indicator_of_mem hx]
    · simp [indicator_of_notMem hx, hsupport t ht x hx]
  rw [hind, integral_indicator hK.measurableSet]
  apply (le_abs_self _).trans
  rw [← Real.norm_eq_abs]
  apply norm_setIntegral_le_of_norm_le_const hK.measure_lt_top
  intro x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) ((hC (t, x) ⟨ht, hx⟩).trans (le_max_left _ _)) 2

theorem wordDerivative_energy_uniform_of_compact_support
    (f : ℝ × Space → ℝ) (T : ℝ) (K : Set Space) (hK : IsCompact K)
    (hf : ContDiffOn ℝ ∞ f (Icc (0 : ℝ) T ×ˢ (univ : Set Space)))
    (hsupport : ∀ t ∈ Icc (0 : ℝ) T, tsupport (fun x => f (t, x)) ⊆ K)
    (word : List (Fin 3)) :
    ∃ B : ℝ, ∀ t ∈ Icc (0 : ℝ) T,
      (∫ x, wordDerivative word (fun y => f (t, y)) x ^ 2) ≤ B := by
  obtain ⟨B, hB⟩ := uniform_energy_of_compact_support
    (fun z : ℝ × Space => wordDerivative word (fun y => f (z.1, y)) z.2)
    T K hK
    ((joint_wordDerivative_contDiffOn hf word).continuousOn.mono
      (by intro z hz; exact ⟨hz.1, mem_univ _⟩))
    (by
      intro t ht x hx
      exact image_eq_zero_of_notMem_tsupport (fun hn =>
        hx (hsupport t ht (tsupport_wordDerivative_subset word _ hn))))
  refine ⟨B, fun t ht => ?_⟩
  simpa only [Real.norm_eq_abs, sq_abs] using hB t ht

end EulerComparatorRecovery

end
end

end

section

/-! Uniform spatial derivative energies for a Comparator solution whose
vorticity stays in one compact set on a finite time interval. Ordinary joint
smoothness supplies the compact source bounds, and elliptic recovery supplies
the velocity derivative bounds. -/

@[expose] public section

noncomputable section

open Set MeasureTheory InnerProductSpace Laplacian EulerSmoothLimit EulerVectorCalculus
  EulerMeanHarmonic EulerMeanVectorIdentities EulerMeanCutoffCurl EulerComparatorRecovery
open scoped ContDiff Topology

namespace Euler.EulerExistenceAndSmoothnessR3

variable {u₀ : Space → Space} {v : Space → ℝ → Space} {p : Space → ℝ → ℝ}
  (h : EulerExistenceAndSmoothnessR3 u₀ v p)

include h

/-- The literal Laplacian of the velocity is the negative curl of its
vorticity, by solenoidality and the ordinary curl-curl identity. -/
theorem velocity_laplacian_eq_neg_curl_curl (t : ℝ) (ht : 0 ≤ t) :
    Δ (v · t) = -vectorCurl (vectorCurl (v · t)) := by
  have hi := vectorCurl_vectorCurl (v · t) (h.velocity_contDiff t ht)
  have hg : gradient (EulerSmoothLimit.divergence (v · t)) = 0 := by
    rw [show EulerSmoothLimit.divergence (v · t) = (fun _ : Space => (0 : ℝ)) from
      funext (fun x => h.div_free x t ht)]
    funext x
    exact gradient_fun_const x 0
  rw [hg, zero_sub] at hi
  rw [hi, neg_neg]

/-- Locality of curl places the Laplacian support inside the vorticity support. -/
theorem velocity_laplacian_tsupport_subset (t : ℝ) (ht : 0 ≤ t) :
    tsupport (Δ (v · t)) ⊆ tsupport (vectorCurl (v · t)) := by
  rw [h.velocity_laplacian_eq_neg_curl_curl t ht, tsupport_neg]
  exact vectorCurl_support _

/-- Every scalar component of the actual velocity Laplacian remains jointly
smooth through time zero. -/
theorem velocity_laplacian_component_joint_contDiffOn (j : Fin 3) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Space => Δ (v · z.1) z.2 j)
      (Ici 0 ×ˢ (univ : Set Space)) := by
  have hs : ContDiffOn ℝ ∞ (fun z : ℝ × Space => v z.2 z.1 j)
      (Ici 0 ×ˢ (univ : Set Space)) :=
    (EuclideanSpace.proj j : Space →L[ℝ] ℝ).contDiff.comp_contDiffOn h.velocity_joint_contDiffOn
  apply (joint_scalar_laplacian_contDiffOn hs).congr
  intro z hz
  exact vector_laplacian_coordinate (v · z.1) (h.velocity_contDiff z.1 hz.1) z.2 j

/-- Common compact support of vorticity and Comparator joint smoothness
uniformly control every scalar coordinate derivative of the Laplacian. -/
theorem laplacian_component_word_energy_uniform_of_commonCompactCurl
    (T : ℝ) (K : Set Space) (hK : IsCompact K)
    (hsupport : ∀ t ∈ Icc (0 : ℝ) T, tsupport (vectorCurl (v · t)) ⊆ K)
    (j : Fin 3) (word : List (Fin 3)) :
    ∃ B : ℝ, ∀ t ∈ Icc (0 : ℝ) T,
      (∫ x, wordDerivative word (fun y => Δ (v · t) y j) x ^ 2) ≤ B := by
  apply wordDerivative_energy_uniform_of_compact_support
    (fun z : ℝ × Space => Δ (v · z.1) z.2 j) T K hK
  · exact (h.velocity_laplacian_component_joint_contDiffOn j).mono
      (by intro z hz; exact ⟨hz.1.1, hz.2⟩)
  · intro t ht
    exact (tsupport_comp_subset (g := fun q : Space => q j) rfl (Δ (v · t))).trans
      ((h.velocity_laplacian_tsupport_subset t ht.1).trans (hsupport t ht))

/-- A Comparator solution with common compact vorticity support has uniform
energies for all genuine scalar coordinate derivatives of its velocity. -/
theorem component_word_energy_uniform_of_commonCompactCurl
    (T : ℝ) (K : Set Space) (hK : IsCompact K)
    (hsupport : ∀ t ∈ Icc (0 : ℝ) T, tsupport (vectorCurl (v · t)) ⊆ K)
    (j : Fin 3) (word : List (Fin 3)) :
    ∃ B : ℝ, ∀ t ∈ Icc (0 : ℝ) T,
      (∫ x, wordDerivative word (fun y => v y t j) x ^ 2) ≤ B := by
  let u (t : Icc (0 : ℝ) T) : Space → Space := fun x => v x (t : ℝ)
  have hsource (a : Fin 3) (w : List (Fin 3)) : ∃ B : ℝ,
      ∀ t : Icc (0 : ℝ) T,
        (∫ x, wordDerivative w (fun y => Δ (u t) y a) x ^ 2) ≤ B := by
    obtain ⟨B, hB⟩ := h.laplacian_component_word_energy_uniform_of_commonCompactCurl
      T K hK hsupport a w
    exact ⟨B, fun t => hB t t.property⟩
  have henergy : ∃ B : ℝ, ∀ t : Icc (0 : ℝ) T, (∫ x, ‖u t x‖ ^ 2) ≤ B := by
    obtain ⟨B, hB⟩ := h.globally_bounded_energy
    exact ⟨B, fun t => (hB t t.property.1).le⟩
  obtain ⟨B, hB⟩ := component_wordDerivative_energy_uniform u
    (fun t => h.velocity_contDiff t t.property.1)
    (fun t => h.velocity_memLp t t.property.1)
    (fun t x => h.div_free x t t.property.1)
    (fun t => hK.of_isClosed_subset (isClosed_tsupport _) (hsupport t t.property))
    henergy hsource j word
  exact ⟨B, fun t ht => hB ⟨t, ht⟩⟩

end Euler.EulerExistenceAndSmoothnessR3

end
end

end

@[expose] public section

noncomputable section

namespace Euler.ComparatorBridge

open Set MeasureTheory EulerSmoothLimit EulerLpTranslation EulerOrdinarySobolev
  EulerMeanSolenoidal EulerMeanHarmonic EulerMeanCutoffCurl EulerComparatorRecovery
open scoped ContDiff Topology

variable {u₀ : Space → Space} {v : Space → ℝ → Space} {p : Space → ℝ → ℝ}

/-- Actual ordinary smooth-L² velocity slices recovered from a common compact
vorticity support. The fields are definitionally the Comparator velocity. -/
def recoveredVelocity (h : EulerExistenceAndSmoothnessR3 u₀ v p)
    (T : ℝ) (K : Set Space) (hK : IsCompact K)
    (hsupport : ∀ t ∈ Icc (0 : ℝ) T, tsupport (vectorCurl (v · t)) ⊆ K) :
    Icc (0 : ℝ) T → SmoothL2Field Space := fun t =>
  smoothL2FieldOfCurlCompact (v · (t : ℝ))
    (h.velocity_contDiff t t.property.1)
    (h.velocity_memLp t t.property.1)
    (fun x => h.div_free x t t.property.1)
    (hK.of_isClosed_subset (isClosed_tsupport _) (hsupport t t.property))

@[simp] theorem recoveredVelocity_field (h : EulerExistenceAndSmoothnessR3 u₀ v p)
    (T : ℝ) (K : Set Space) (hK : IsCompact K)
    (hsupport : ∀ t ∈ Icc (0 : ℝ) T, tsupport (vectorCurl (v · t)) ⊆ K)
    (t : Icc (0 : ℝ) T) :
    (recoveredVelocity h T K hK hsupport t).field = (v · (t : ℝ)) := rfl

/-- All genuine spatial L² tensor norms are uniformly bounded on the common
compact-vorticity interval. No time regularity of these norms is assumed. -/
theorem recoveredVelocity_jetLp_uniform (h : EulerExistenceAndSmoothnessR3 u₀ v p)
    (T : ℝ) (K : Set Space) (hK : IsCompact K)
    (hsupport : ∀ t ∈ Icc (0 : ℝ) T, tsupport (vectorCurl (v · t)) ⊆ K) :
    ∀ n : ℕ, ∃ M : ℝ, ∀ t,
      ‖(recoveredVelocity h T K hK hsupport t).jetLp n‖ ≤ M := by
  intro n
  refine jetLp_norm_uniform_of_coordinate_energy
    (recoveredVelocity h T K hK hsupport) ?_ n
  intro j word
  obtain ⟨B, hB⟩ := h.component_word_energy_uniform_of_commonCompactCurl
    T K hK hsupport j word
  exact ⟨B, fun t => hB t t.property⟩

/-- A Comparator Euler solution with a common compact vorticity support is
represented by an actual ordinary evolution throughout that interval. -/
theorem exists_evolution_of_commonCompactCurl
    (h : EulerExistenceAndSmoothnessR3 u₀ v p)
    (T : ℝ) (hT : 0 < T) (K : Set Space) (hK : IsCompact K)
    (hsupport : ∀ t ∈ Icc (0 : ℝ) T, tsupport (vectorCurl (v · t)) ⊆ K) :
    ∃ U : Evolution T hT.le,
      ∀ t : Icc (0 : ℝ) T, (U.velocity t).field = (v · (t : ℝ)) := by
  let A := recoveredVelocity h T K hK hsupport
  have hA (t : Icc (0 : ℝ) T) : (A t).field = (v · (t : ℝ)) := rfl
  have hscalar : IsSmoothScalarEuler (hT := hT.le) A := by
    apply isSmoothScalarEuler_of_weak_projectedEquation hT A
      (comparator_velocity_mem_solenoidal h A hA)
      (tensorNorm_uniform_of_jetLp_uniform A
        (recoveredVelocity_jetLp_uniform h T K hK hsupport))
      compactSolenoidalTests compactSolenoidalTests_dense
    · intro φ _
      exact comparator_weak_pairings_continuous h A hA φ
    · intro φ hφ t ht
      exact comparator_projected_pairing_hasDerivAt h hT A hA φ hφ t ht
  obtain ⟨U, hU⟩ := (exists_evolution_iff_scalar (hT := hT.le) hT A).mpr hscalar
  refine ⟨U, ?_⟩
  intro t
  rw [hU]
  exact hA t

/-- Compact initial vorticity alone supplies the complete local conversion:
the truncations, support propagation, spatial recovery, and time regularity
are all obtained from the actual Comparator solution assumptions. -/
theorem compactCurlLocalUpgrade : CompactCurlLocalUpgrade := by
  intro u₀ v p h hc
  obtain ⟨δ, B, hδ, hsupport⟩ :=
    h.local_compact_vorticity_of_truncationFamily h.finiteEnergyTruncationFamily hc
  obtain ⟨U, hU⟩ := exists_evolution_of_commonCompactCurl h δ hδ
    (Metric.closedBall (0 : Space) B) (isCompact_closedBall _ _) hsupport
  exact ⟨δ, hδ, U, hU⟩

end Euler.ComparatorBridge
