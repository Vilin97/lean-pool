/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.KernelAllOrdersBounds
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.KernelAllOrdersPotential
public import LeanPool.CaffarelliKohnNirenberg.Pressure.Potentials
public import LeanPool.CaffarelliKohnNirenberg.Pressure.PkBoundsBasic

/-!
# Kernel All Orders

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open scoped BigOperators Topology
open MeasureTheory
open CKN.Foundation.Parabolic


/-!
# All-order estimates for the Newtonian potentials of an annular density

The Newtonian kernel and each of its first derivatives are of every finite
differentiability order away from the origin, with

  `‖D^k N x‖ ≤ c_k ‖x‖₂^{-(1 + k)}`,   `‖D^k ∂_j N x‖ ≤ c_k ‖x‖₂^{-(2 + k)}`,

the kernel estimates behind `cor:CZ-harmonic`.  Consequently, if the density `g`
vanishes outside a set `A` separated from an open set `U` by `δ > 0`, then the
potentials `N * g` and `∂_j N * g` are of every finite differentiability order
on `U` and obey

  `‖D^k (N * g) x‖ ≤ c_k δ^{-(1 + k)} ‖g‖₁`,
  `‖D^k (∂_j N * g) x‖ ≤ c_k δ^{-(2 + k)} ‖g‖₁`   for `x ∈ U`,

with constants depending on the order `k` alone; this is the display
`eq:har-Ck`.  Specialising to the pressure geometry `U = B(x₀, ρ/2)` and
`A = B(x₀, 3ρ/4) \ B(x₀, 13ρ/20)`, the separation is `δ = 3ρ/20` (lem:cutoff).
-/

noncomputable section

namespace CKN.Foundation.Heat

/-! ### Smoothness of the first-order kernels -/

/-- Each first-order Newtonian kernel `∂_j N` has every finite differentiability order
away from the origin. -/
theorem contDiffAt_newtonianKernel_spatialDeriv (j : Fin 3) (i : ℕ) (z : Vec3) (hz : z ≠ 0) :
    ContDiffAt ℝ i (CKN.spatialDeriv newtonianKernel j) z := by
  have hfd : ContDiffAt ℝ (i : ℕ) (fderiv ℝ newtonianKernel) z :=
    contDiffAt_fderiv_of_kernelSmooth
      (fun n w hw => contDiffAt_newtonianKernel n hw) i z hz
  exact hfd.clm_apply contDiffAt_const

/-! ### The potentials of the Newtonian kernel and its first derivatives -/

/-- The pressure potential is the negative of the potential of the Newtonian kernel. -/
theorem pressureNewtonianPotential_eq_neg_kernelPotential (g : Vec3 → ℝ) (x : Vec3) :
    CKN.pressureNewtonianPotential g x = -kernelPotential newtonianKernel g x := by
  rw [kernelPotential_real_eq]
  change (∫ y : Vec3, (-newtonianKernel (x - y)) * g y) = _
  rw [← integral_neg]
  congr 1
  funext y
  ring

/-- The pressure derivative potential is the potential of the kernel `∂_j N`. -/
theorem pressureNewtonianDerivativePotential_eq_kernelPotential (j : Fin 3) (g : Vec3 → ℝ)
    (x : Vec3) :
    CKN.pressureNewtonianDerivativePotential j g x =
      kernelPotential (CKN.spatialDeriv newtonianKernel j) g x :=
  (kernelPotential_real_eq _ _ _).symm

/-- Smoothness of the Newtonian potential off the support of its density (`eq:har-Ck`). -/
theorem contDiffOn_pressureNewtonianPotential {g : Vec3 → ℝ} {A U : Set Vec3} {δ : ℝ}
    (hg : Integrable g volume) (hU : IsOpen U) (hg0 : ∀ y : Vec3, y ∉ A → g y = 0)
    (hδ : 0 < δ) (hsep : ∀ x ∈ U, ∀ y ∈ A, δ ≤ vec3EuclideanNorm (x - y)) (n : ℕ) :
    ContDiffOn ℝ (n : ℕ) (CKN.pressureNewtonianPotential g) U := by
  obtain ⟨C, hC0, hC⟩ : ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧ ∀ (j : ℕ) (z : Vec3), z ≠ 0 →
      ‖iteratedFDeriv ℝ j newtonianKernel z‖ ≤
        C j * (vec3EuclideanNorm z ^ (1 + j))⁻¹ := by
    choose C hC0 hC using exists_norm_iteratedFDeriv_newtonianKernel_le
    exact ⟨C, hC0, hC⟩
  have hmain : ContDiffOn ℝ (n : ℕ) (kernelPotential newtonianKernel g) U :=
    contDiffOn_kernelPotential hC0 (fun i z hz => contDiffAt_newtonianKernel i hz) hC
      hg hU hg0 hδ hsep n
  exact hmain.neg.congr fun z _ => pressureNewtonianPotential_eq_neg_kernelPotential g z

/-- Smoothness of the first-order Newtonian potential off the support of its density. -/
theorem contDiffOn_pressureNewtonianDerivativePotential (j : Fin 3) {g : Vec3 → ℝ}
    {A U : Set Vec3} {δ : ℝ} (hg : Integrable g volume) (hU : IsOpen U)
    (hg0 : ∀ y : Vec3, y ∉ A → g y = 0) (hδ : 0 < δ)
    (hsep : ∀ x ∈ U, ∀ y ∈ A, δ ≤ vec3EuclideanNorm (x - y)) (n : ℕ) :
    ContDiffOn ℝ (n : ℕ) (CKN.pressureNewtonianDerivativePotential j g) U := by
  obtain ⟨C, hC0, hC⟩ : ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧ ∀ (i : ℕ) (z : Vec3), z ≠ 0 →
      ‖iteratedFDeriv ℝ i (CKN.spatialDeriv newtonianKernel j) z‖ ≤
        C i * (vec3EuclideanNorm z ^ (2 + i))⁻¹ := by
    choose C hC0 hC using exists_norm_iteratedFDeriv_newtonianKernel_spatialDeriv_le j
    exact ⟨C, hC0, hC⟩
  have hmain : ContDiffOn ℝ (n : ℕ)
      (kernelPotential (CKN.spatialDeriv newtonianKernel j) g) U :=
    contDiffOn_kernelPotential hC0 (contDiffAt_newtonianKernel_spatialDeriv j) hC
      hg hU hg0 hδ hsep n
  exact hmain.congr fun z _ =>
    pressureNewtonianDerivativePotential_eq_kernelPotential j g z

/-- All-order size of the Newtonian potential off the support of its density (`eq:har-Ck`);
the constant depends on the order alone. -/
theorem exists_norm_iteratedFDeriv_pressureNewtonianPotential_le (k : ℕ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (g : Vec3 → ℝ), Integrable g volume → ∀ (A U : Set Vec3), IsOpen U →
      (∀ y : Vec3, y ∉ A → g y = 0) → ∀ δ : ℝ, 0 < δ →
      (∀ x ∈ U, ∀ y ∈ A, δ ≤ vec3EuclideanNorm (x - y)) → ∀ x ∈ U,
        ‖iteratedFDeriv ℝ k (CKN.pressureNewtonianPotential g) x‖ ≤
          c * (δ ^ (1 + k))⁻¹ * ∫ y : Vec3, ‖g y‖ := by
  choose C hC0 hC using exists_norm_iteratedFDeriv_newtonianKernel_le
  refine ⟨C k, hC0 k, fun g hg A U hU hg0 δ hδ hsep x hx => ?_⟩
  have hfun : Set.EqOn (CKN.pressureNewtonianPotential g)
      (-kernelPotential newtonianKernel g) U := fun z _ => by
    simpa using pressureNewtonianPotential_eq_neg_kernelPotential g z
  rw [iteratedFDeriv_eq_of_eqOn_isOpen hU hfun k hx, iteratedFDeriv_neg, Pi.neg_apply,
    norm_neg]
  exact norm_iteratedFDeriv_kernelPotential_le hC0
    (fun i z hz => contDiffAt_newtonianKernel i hz) hC hg hU hg0 hδ hsep k hx

/-- All-order size of the first-order Newtonian potential off the support of its density;
the constant depends on the order alone. -/
theorem exists_norm_iteratedFDeriv_pressureNewtonianDerivativePotential_le
    (j : Fin 3) (k : ℕ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (g : Vec3 → ℝ), Integrable g volume → ∀ (A U : Set Vec3), IsOpen U →
      (∀ y : Vec3, y ∉ A → g y = 0) → ∀ δ : ℝ, 0 < δ →
      (∀ x ∈ U, ∀ y ∈ A, δ ≤ vec3EuclideanNorm (x - y)) → ∀ x ∈ U,
        ‖iteratedFDeriv ℝ k (CKN.pressureNewtonianDerivativePotential j g) x‖ ≤
          c * (δ ^ (2 + k))⁻¹ * ∫ y : Vec3, ‖g y‖ := by
  choose C hC0 hC using exists_norm_iteratedFDeriv_newtonianKernel_spatialDeriv_le j
  refine ⟨C k, hC0 k, fun g hg A U hU hg0 δ hδ hsep x hx => ?_⟩
  have hfun : Set.EqOn (CKN.pressureNewtonianDerivativePotential j g)
      (kernelPotential (CKN.spatialDeriv newtonianKernel j) g) U := fun z _ =>
    pressureNewtonianDerivativePotential_eq_kernelPotential j g z
  rw [iteratedFDeriv_eq_of_eqOn_isOpen hU hfun k hx]
  exact norm_iteratedFDeriv_kernelPotential_le hC0
    (contDiffAt_newtonianKernel_spatialDeriv j) hC hg hU hg0 hδ hsep k hx

/-! ### The pressure geometry: inner ball against the cutoff annulus -/

/-- On the inner ball `B(x₀, ρ/2)` the cutoff annulus `B(x₀, 3ρ/4) \ B(x₀, 13ρ/20)` is at
Euclidean distance at least `3ρ/20` (lem:cutoff). -/
theorem annulus_separation {x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ) :
    ∀ x ∈ vec3Ball x₀ (ρ / 2), ∀ y ∈ CKN.pressureAnnulus x₀ ρ,
      3 * ρ / 20 ≤ vec3EuclideanNorm (x - y) := fun _x hx _y hy =>
  CKN.cutoff_annulus_separation hρ (by positivity) le_rfl hx hy

/-- Smoothness of the annular Newtonian potential on the inner ball (`eq:har-Ck`). -/
theorem contDiffOn_pressureNewtonianPotential_annulus {x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ)
    {g : Vec3 → ℝ} (hg : Integrable g volume)
    (hg0 : ∀ y : Vec3, y ∉ CKN.pressureAnnulus x₀ ρ → g y = 0) (n : ℕ) :
    ContDiffOn ℝ (n : ℕ) (CKN.pressureNewtonianPotential g) (vec3Ball x₀ (ρ / 2)) :=
  contDiffOn_pressureNewtonianPotential hg (isOpen_vec3Ball x₀ (ρ / 2)) hg0
    (by positivity) (annulus_separation hρ) n

/-- Smoothness of the annular first-order Newtonian potential on the inner ball. -/
theorem contDiffOn_pressureNewtonianDerivativePotential_annulus (j : Fin 3) {x₀ : Vec3}
    {ρ : ℝ} (hρ : 0 < ρ) {g : Vec3 → ℝ} (hg : Integrable g volume)
    (hg0 : ∀ y : Vec3, y ∉ CKN.pressureAnnulus x₀ ρ → g y = 0) (n : ℕ) :
    ContDiffOn ℝ (n : ℕ) (CKN.pressureNewtonianDerivativePotential j g)
      (vec3Ball x₀ (ρ / 2)) :=
  contDiffOn_pressureNewtonianDerivativePotential j hg (isOpen_vec3Ball x₀ (ρ / 2)) hg0
    (by positivity) (annulus_separation hρ) n

/-- All-order size of the annular Newtonian potential on the inner ball, with the separation
`3ρ/20` of lem:cutoff and a constant depending on the order alone (`eq:har-Ck`). -/
theorem exists_norm_iteratedFDeriv_pressureNewtonianPotential_annulus_le (k : ℕ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (x₀ : Vec3) (ρ : ℝ), 0 < ρ → ∀ g : Vec3 → ℝ, Integrable g volume →
      (∀ y : Vec3, y ∉ CKN.pressureAnnulus x₀ ρ → g y = 0) →
      ∀ x ∈ vec3Ball x₀ (ρ / 2),
        ‖iteratedFDeriv ℝ k (CKN.pressureNewtonianPotential g) x‖ ≤
          c * ((3 * ρ / 20) ^ (1 + k))⁻¹ * ∫ y : Vec3, ‖g y‖ := by
  obtain ⟨c, hc0, hc⟩ := exists_norm_iteratedFDeriv_pressureNewtonianPotential_le k
  refine ⟨c, hc0, fun x₀ ρ hρ g hg hg0 x hx => ?_⟩
  exact hc g hg (CKN.pressureAnnulus x₀ ρ) (vec3Ball x₀ (ρ / 2))
    (isOpen_vec3Ball x₀ (ρ / 2)) hg0 (3 * ρ / 20) (by positivity)
    (annulus_separation hρ) x hx

/-- All-order size of the annular first-order Newtonian potential on the inner ball, with the
separation `3ρ/20` of lem:cutoff and a constant depending on the order alone. -/
theorem exists_norm_iteratedFDeriv_pressureNewtonianDerivativePotential_annulus_le
    (j : Fin 3) (k : ℕ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (x₀ : Vec3) (ρ : ℝ), 0 < ρ → ∀ g : Vec3 → ℝ, Integrable g volume →
      (∀ y : Vec3, y ∉ CKN.pressureAnnulus x₀ ρ → g y = 0) →
      ∀ x ∈ vec3Ball x₀ (ρ / 2),
        ‖iteratedFDeriv ℝ k (CKN.pressureNewtonianDerivativePotential j g) x‖ ≤
          c * ((3 * ρ / 20) ^ (2 + k))⁻¹ * ∫ y : Vec3, ‖g y‖ := by
  obtain ⟨c, hc0, hc⟩ :=
    exists_norm_iteratedFDeriv_pressureNewtonianDerivativePotential_le j k
  refine ⟨c, hc0, fun x₀ ρ hρ g hg hg0 x hx => ?_⟩
  exact hc g hg (CKN.pressureAnnulus x₀ ρ) (vec3Ball x₀ (ρ / 2))
    (isOpen_vec3Ball x₀ (ρ / 2)) hg0 (3 * ρ / 20) (by positivity)
    (annulus_separation hρ) x hx

/-- The inverse integer power used in the potential bounds is the negative real power of
the paper's displays. -/
theorem inv_pow_eq_rpow_neg {t : ℝ} (ht : 0 < t) (n : ℕ) :
    (t ^ n)⁻¹ = t ^ (-(n : ℝ)) := by
  rw [Real.rpow_neg ht.le, Real.rpow_natCast]

end CKN.Foundation.Heat
