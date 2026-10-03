/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Terms
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ingredients.Parameters

/-! The exact transport equation for the final T-iterate. -/

@[expose] public section

open Homogenization

noncomputable section

namespace AVenhance.Infra.Section5

variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

/-- The source error `e_{m-1}` from the difference between the last two
T-iterates. -/
def iterateError (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm κprev : ℝ)
    (T : ℕ → ℝ → Vec 2 → ℝ) (t : ℝ) (x : Vec 2) : Vec 2 :=
  (I.Kmat κm m t - κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
      I.sMat hΦ m κm t x).mulVec
    (spaceGrad (T (Nstar β - 1) t) x - spaceGrad (T (Nstar β) t) x)

/-- The last iterate satisfies the source's exact `T_{m-1}` equation, with
the finite-iteration error retained as `e_{m-1}`. -/
theorem final_iterate_transport_eq
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm κprev : ℝ)
    (θ₀ : Vec 2 → ℝ) (θprev : ℝ → Vec 2 → ℝ)
    (T : ℕ → ℝ → Vec 2 → ℝ)
    (hT : Ingredients.IsTIterates I hΦ m κm κprev θ₀ θprev T)
    {t : ℝ} {x : Vec 2}
    (hA : ∀ i : Fin 2, DifferentiableAt ℝ
      (fun y => (I.Kmat κm m t - κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        I.sMat hΦ m κm t y).mulVec (spaceGrad (T (Nstar β - 1) t) y) i) x)
    (hgrad : ∀ i : Fin 2, DifferentiableAt ℝ
      (fun y => spaceGrad (T (Nstar β) t) y i) x)
    (ht : 0 < t) :
    deriv (fun s => T (Nstar β) s x) t +
      vecDot (streamVel (Φ (m - 1)) t x)
        (spaceGrad (T (Nstar β) t) x) =
      vecDiv (fun y =>
        (I.Kmat κm m t + I.sMat hΦ m κm t y).mulVec
          (spaceGrad (T (Nstar β) t) y) +
        iterateError I hΦ m κm κprev T t y) x := by
  have hN : 1 ≤ Nstar β := by
    have h := AVenhance.Infra.Ingredients.Nstar_ge_256 I.one_lt_beta I.beta_lt
    omega
  rcases hT with ⟨hzero, hstep⟩
  have hclass : IsClassicalSol (streamVel (Φ (m - 1))) κprev
      (I.TForcing hΦ m κm κprev (T (Nstar β - 1))) θ₀ (T (Nstar β)) :=
    hstep (Nstar β) hN le_rfl
  rcases hclass with ⟨_, _, _, hpde⟩
  have hpde' := hpde t ht x
  let U : Vec 2 → Vec 2 := fun y =>
    (I.Kmat κm m t - κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
      I.sMat hΦ m κm t y).mulVec (spaceGrad (T (Nstar β - 1) t) y)
  let V : Vec 2 → Vec 2 := fun y => κprev • spaceGrad (T (Nstar β) t) y
  have hvec (y : Vec 2) :
      (I.Kmat κm m t + I.sMat hΦ m κm t y).mulVec
          (spaceGrad (T (Nstar β) t) y) +
        iterateError I hΦ m κm κprev T t y =
      U y + V y := by
    have hmat : I.Kmat κm m t + I.sMat hΦ m κm t y =
        (I.Kmat κm m t - κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
          I.sMat hΦ m κm t y) + κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
      ext i j
      simp
      ring
    simp only [U, V, iterateError, hmat, Matrix.add_mulVec,
      Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      Matrix.mulVec_sub]
    abel
  have hsumdiv : vecDiv (fun y => U y + V y) x = vecDiv U x + vecDiv V x := by
    change (∑ i : Fin 2, spaceGrad (fun y => U y i + V y i) x i) = _
    calc
      (∑ i : Fin 2, spaceGrad (fun y => U y i + V y i) x i) =
          ∑ i : Fin 2, (spaceGrad (fun y => U y i) x i +
            spaceGrad (fun y => V y i) x i) := by
        apply Finset.sum_congr rfl
        intro i _
        change fderiv ℝ ((fun y => U y i) + (fun y => V y i))
          x (basisVec i) = _
        have hVi : DifferentiableAt ℝ (fun y => V y i) x := by
          simpa [V, Pi.smul_apply, smul_eq_mul] using
            (hgrad i).const_mul κprev
        rw [fderiv_add (hA i) hVi]
        rfl
      _ = vecDiv U x + vecDiv V x := by
        simp only [vecDiv]
        rw [Finset.sum_add_distrib]
  have hlap : vecDiv V x = κprev * spaceLap (T (Nstar β) t) x := by
    change (∑ i : Fin 2,
        spaceGrad (fun y => κprev * spaceGrad (T (Nstar β) t) y i) x i) =
      κprev * ∑ i : Fin 2,
        spaceGrad (fun y => spaceGrad (T (Nstar β) t) y i) x i
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    change fderiv ℝ (fun y => κprev * spaceGrad (T (Nstar β) t) y i)
        x (basisVec i) = κprev * spaceGrad
          (fun y => spaceGrad (T (Nstar β) t) y i) x i
    rw [fderiv_const_mul (hgrad i) κprev]
    rfl
  have hdiv :
      vecDiv (fun y =>
        (I.Kmat κm m t + I.sMat hΦ m κm t y).mulVec
          (spaceGrad (T (Nstar β) t) y) +
        iterateError I hΦ m κm κprev T t y) x =
      I.TForcing hΦ m κm κprev (T (Nstar β - 1)) t x +
        κprev * spaceLap (T (Nstar β) t) x := by
    have hfield : (fun y =>
        (I.Kmat κm m t + I.sMat hΦ m κm t y).mulVec
          (spaceGrad (T (Nstar β) t) y) +
        iterateError I hΦ m κm κprev T t y) = fun y => U y + V y := by
      funext y
      exact hvec y
    rw [hfield, hsumdiv]
    have hforce :
        vecDiv (fun y =>
          (I.Kmat κm m t - κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
              I.sMat hΦ m κm t y).mulVec
              (spaceGrad (T (Nstar β - 1) t) y)) x =
          I.TForcing hΦ m κm κprev (T (Nstar β - 1)) t x := rfl
    rw [hforce, hlap]
  have hpde'' :
      deriv (fun s => T (Nstar β) s x) t -
        κprev * spaceLap (T (Nstar β) t) x +
        vecDot (streamVel (Φ (m - 1)) t x)
          (spaceGrad (T (Nstar β) t) x) =
      I.TForcing hΦ m κm κprev (T (Nstar β - 1)) t x := by
    simpa [advDiffOp] using hpde'
  rw [hdiv]
  linarith [hpde'']

end AVenhance.Infra.Section5

end
