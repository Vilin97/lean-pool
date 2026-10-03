/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermCenteredDefs

/-! # Product rule for matrix-vector fluxes

Pointwise calculus for the integration by parts in `e.monster.twistie4.split`: for
differentiable `D`, `g`,
`div (D g) = D : ∇g + g · Div D`, and the divergence of a finite weighted sum is the weighted sum
of the divergences. -/

@[expose] public section

open Homogenization

noncomputable section

namespace AVenhance.Infra.Section5.Contracts

open AVenhance AVenhance.Infra.Section5

theorem sd_spaceGrad_add {f g : Vec 2 → ℝ} {x : Vec 2} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (i : Fin 2) :
    spaceGrad (fun y => f y + g y) x i = spaceGrad f x i + spaceGrad g x i := by
  simp only [spaceGrad]
  rw [fderiv_fun_add hf hg]
  rfl

theorem sd_spaceGrad_mul {f g : Vec 2 → ℝ} {x : Vec 2} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (i : Fin 2) :
    spaceGrad (fun y => f y * g y) x i = f x * spaceGrad g x i + g x * spaceGrad f x i := by
  simp only [spaceGrad]
  rw [fderiv_fun_mul hf hg]
  simp

theorem sd_spaceGrad_const_mul {f : Vec 2 → ℝ} {x : Vec 2} (c : ℝ)
    (hf : DifferentiableAt ℝ f x) (i : Fin 2) :
    spaceGrad (fun y => c * f y) x i = c * spaceGrad f x i := by
  simp only [spaceGrad]
  rw [fderiv_const_mul hf]
  simp

theorem sd_spaceGrad_sum {ι : Type*} (S : Finset ι) {f : ι → Vec 2 → ℝ} {x : Vec 2}
    (hf : ∀ k ∈ S, DifferentiableAt ℝ (f k) x) (i : Fin 2) :
    spaceGrad (fun y => ∑ k ∈ S, f k y) x i = ∑ k ∈ S, spaceGrad (f k) x i := by
  simp only [spaceGrad]
  rw [fderiv_fun_sum hf]
  simp

/-- Product rule for `div (D g)`. -/
theorem sd_vecDiv_mulVec {D : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {g : Vec 2 → Vec 2} {x : Vec 2}
    (hD : ∀ i j, DifferentiableAt ℝ (fun y => D y i j) x)
    (hg : ∀ j, DifferentiableAt ℝ (fun y => g y j) x) :
    vecDiv (fun y => (D y).mulVec (g y)) x =
      frob (D x) (Matrix.of fun i j => spaceGrad (fun y => g y j) x i) +
        vecDot (g x) (matDiv D x) := by
  have hrow : ∀ i : Fin 2, (fun y => (D y).mulVec (g y) i) =
      fun y => D y i 0 * g y 0 + D y i 1 * g y 1 := by
    intro i
    funext y
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hterm : ∀ i : Fin 2, spaceGrad (fun y => (D y).mulVec (g y) i) x i =
      (D x i 0 * spaceGrad (fun y => g y 0) x i + g x 0 * spaceGrad (fun y => D y i 0) x i) +
        (D x i 1 * spaceGrad (fun y => g y 1) x i + g x 1 * spaceGrad (fun y => D y i 1) x i) := by
    intro i
    have h0 : DifferentiableAt ℝ (fun y => D y i 0 * g y 0) x := (hD i 0).mul (hg 0)
    have h1 : DifferentiableAt ℝ (fun y => D y i 1 * g y 1) x := (hD i 1).mul (hg 1)
    rw [hrow i, sd_spaceGrad_add h0 h1,
      sd_spaceGrad_mul (hD i 0) (hg 0), sd_spaceGrad_mul (hD i 1) (hg 1)]
  unfold vecDiv
  simp only [hterm]
  simp only [frob, vecDot, matDiv, Matrix.of_apply, Fin.sum_univ_two]
  ring

/-- The divergence of a finite weighted sum of fluxes. -/
theorem sd_vecDiv_finset_sum {ι : Type*} (S : Finset ι) (c : ι → ℝ) {V : ι → Vec 2 → Vec 2}
    {x : Vec 2} (hV : ∀ k ∈ S, ∀ j, DifferentiableAt ℝ (fun y => V k y j) x) :
    vecDiv (fun y => ∑ k ∈ S, c k • V k y) x = ∑ k ∈ S, c k * vecDiv (V k) x := by
  unfold vecDiv
  have hcomp : ∀ i : Fin 2, spaceGrad (fun y => (∑ k ∈ S, c k • V k y) i) x i =
      ∑ k ∈ S, c k * spaceGrad (fun y => V k y i) x i := by
    intro i
    have h1 : (fun y => (∑ k ∈ S, c k • V k y) i) = fun y => ∑ k ∈ S, c k * V k y i := by
      funext y
      simp [Finset.sum_apply]
    rw [h1, sd_spaceGrad_sum S (fun k hk => (hV k hk i).const_mul (c k))]
    exact Finset.sum_congr rfl fun k hk => sd_spaceGrad_const_mul (c k) (hV k hk i) i
  simp only [hcomp]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]

/-- The finite-sum form of the split. -/
theorem sd_split_finset {ι : Type*} (S : Finset ι) (c : ι → ℝ)
    (D : ι → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (g : ι → Vec 2 → Vec 2) (x : Vec 2)
    (hD : ∀ k ∈ S, ∀ i j, DifferentiableAt ℝ (fun y => D k y i j) x)
    (hg : ∀ k ∈ S, ∀ j, DifferentiableAt ℝ (fun y => g k y j) x) :
    -∑ k ∈ S, c k * vecDot (g k x) (matDiv (D k) x) =
      ∑ k ∈ S, c k * frob (D k x) (Matrix.of fun i j => spaceGrad (fun y => g k y j) x i) -
        vecDiv (fun y => ∑ k ∈ S, c k • (D k y).mulVec (g k y)) x := by
  rw [sd_vecDiv_finset_sum S c (V := fun k y => (D k y).mulVec (g k y)) (x := x)
    (fun k hk j => by
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      exact ((hD k hk j 0).mul (hg k hk 0)).add ((hD k hk j 1).mul (hg k hk 1)))]
  have : ∀ k ∈ S, c k * vecDiv (fun y => (D k y).mulVec (g k y)) x =
      c k * frob (D k x) (Matrix.of fun i j => spaceGrad (fun y => g k y j) x i) +
        c k * vecDot (g k x) (matDiv (D k) x) := by
    intro k hk
    rw [sd_vecDiv_mulVec (hD k hk) (hg k hk), mul_add]
  rw [Finset.sum_congr rfl this, Finset.sum_add_distrib]
  ring

end AVenhance.Infra.Section5.Contracts
end
