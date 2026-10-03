/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesStreamFlux
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWordEnergy

/-! Skew integration by parts for the first coefficient derivative in the drift error. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open AVenhance

/-- The actual matrix-gradient flux is smooth. -/
theorem iterate_matrix_gradient_smooth
    {A : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {v : Vec 2 → ℝ}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hv : ContDiff ℝ (⊤ : ℕ∞) v) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => (A x).mulVec (spaceGrad v x)) := by
  apply contDiff_pi.mpr
  intro i
  change ContDiff ℝ (⊤ : ℕ∞) (fun x => ∑ j : Fin 2, A x i j * spaceGrad v x j)
  exact ContDiff.sum (fun j _ => (contDiff_pi.mp (contDiff_pi.mp hA i) j).mul
    (contDiff_pi.mp (iterate_gradient_smooth hv) j))

/-- Periodicity of the actual coefficient and scalar supplies flux periodicity. -/
theorem iterate_matrix_gradient_periodic
    {A : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {v : Vec 2 → ℝ}
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (hA : IsZ2Periodic A) (hvp : IsZ2Periodic v) :
    IsZ2Periodic (fun x => (A x).mulVec (spaceGrad v x)) := by
  have hg := iterate_gradient_periodic (hv.of_le (by simp)) hvp
  intro k x
  dsimp only
  rw [hA k x, hg k x]

/-- The first stream-coefficient derivative can be transferred to the
coefficient once more, avoiding Young's inequality on the large first jet. -/
theorem iterate_stream_pairing_transfer {ψ u v : Vec 2 → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hψp : IsZ2Periodic ψ) (hup : IsZ2Periodic u) (hvp : IsZ2Periodic v) :
    (∫ x in unitCube, vecDot (spaceGrad u x)
      ((ψ x • sigmaMat).mulVec (spaceGrad v x))) =
    ∫ x in unitCube, u x * vecDot (sigmaMat.mulVec (spaceGrad ψ x)) (spaceGrad v x) := by
  have hp : IsZ2Periodic (fun x => ψ x • sigmaMat) := by
    intro k x
    dsimp only
    rw [hψp k x]
  have he := iterate_divergence_pairing hu hup
    (iterate_matrix_gradient_smooth (iterate_stream_matrix_smooth hψ) hv)
    (iterate_matrix_gradient_periodic hv hp hvp)
  have heq : (fun x => u x * vecDiv
      (fun y => (ψ y • sigmaMat).mulVec (spaceGrad v y)) x) =
      fun x => -(u x * vecDot (sigmaMat.mulVec (spaceGrad ψ x)) (spaceGrad v x)) := by
    funext x
    rw [iterate_stream_flux_divergence hψ hv]
    ring
  rw [heq, integral_neg] at he
  linarith only [he]

/-- Pointwise bilinear bound after the skew transfer. The scalar norm is
undifferentiated; both factors can then be controlled by lower-order energy. -/
theorem iterate_scalar_transport_abs_bound {H a : ℝ} (hH : 0 < H)
    (b v : Vec 2) (hb : ∀ j, |b j| ≤ H) :
    |a * vecDot b v| ≤ H * (a ^ 2 + vecNormSq v) := by
  have hA : ∀ i j : Fin 2, |(!![b 0, b 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ H := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [hb, hH.le]
  have h := iterate_matrix_pairing_abs_bound hH
    (!![b 0, b 1; 0, 0]) (![a, 0]) v hA
  have hratio : H ^ 2 / H = H := by field_simp
  rw [hratio] at h
  simpa [vecDot, vecNormSq, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    mul_add, pow_two] using h

/-- Continuous cell integrands are integrable; this discharges the spatial
integrability in the forcing estimates. -/
theorem iterate_continuous_cell_integrable {f : Vec 2 → ℝ} (hf : Continuous f) :
    IntegrableOn f unitCube := by
  let C : Set (Vec 2) := Set.pi Set.univ (fun _ => Set.Icc (0 : ℝ) 1)
  have hc : IsCompact C := isCompact_univ_pi (fun _ : Fin 2 => isCompact_Icc)
  have hsub : unitCube ⊆ C := by
    intro x hx i hi
    exact ⟨(hx i hi).1.le, (hx i hi).2.le⟩
  exact (hf.continuousOn.integrableOn_compact hc).mono_set hsub

/-- Any nonempty ordered scalar word is a component of a lower-order gradient. -/
theorem iterateSpatialWord_sq_le_tail_gradient (f : Vec 2 → ℝ)
    (i : Fin 2) (w : List (Fin 2)) (x : Vec 2) :
    iterateSpatialWord (i :: w) f x ^ 2 ≤
      vecNormSq (spaceGrad (iterateSpatialWord w f) x) := by
  simp only [iterateSpatialWord]
  unfold vecNormSq vecDot
  change spaceGrad (iterateSpatialWord w f) x i ^ 2 ≤
    ∑ j : Fin 2, spaceGrad (iterateSpatialWord w f) x j *
      spaceGrad (iterateSpatialWord w f) x j
  simpa only [pow_two] using Finset.single_le_sum
    (fun j _ => mul_self_nonneg (spaceGrad (iterateSpatialWord w f) x j))
    (Finset.mem_univ i)

end AVenhance.Infra.Section4
