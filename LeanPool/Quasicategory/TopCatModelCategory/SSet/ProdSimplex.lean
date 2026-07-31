/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import LeanPool.Quasicategory.TopCatModelCategory.SSet.NonDegenerateProdSimplex

universe u

open CategoryTheory MonoidalCategory Simplicial Opposite

namespace SSet

section

variable {X Y : SSet.{u}} (app : ∀ d, X _⦋d⦌ → Y _⦋d⦌)
  (naturality : ∀ ⦃d₁ d₂ : ℕ⦄ (f : ⦋d₁⦌ ⟶ ⦋d₂⦌), app d₁ ∘ X.map f.op = Y.map f.op ∘ app d₂)

def homMk : X ⟶ Y where
  app := fun ⟨d⟩ ↦ by
    induction d using SimplexCategory.rec with
    | h n => exact app n
  naturality := by
    rintro ⟨d₁⟩ ⟨d₂⟩ ⟨f⟩
    induction' d₁ using SimplexCategory.rec with d₁
    induction' d₂ using SimplexCategory.rec with d₂
    exact naturality f

@[simp]
lemma homMk_app (d : ℕ) : (homMk app naturality).app (op ⦋d⦌) = app d := rfl

end

namespace prodStdSimplex

def obj₁Mk {p q : ℕ} {x y : Fin (p + 1) × Fin (q + 1)} (h : x ≤ y) :
    (Δ[p] ⊗ Δ[q] : SSet.{u}) _⦋1⦌ :=
  objEquiv.symm (Fin.orderHomMk₂ h)

def homEquiv {p q n : ℕ} :
    (Δ[p] ⊗ Δ[q] ⟶ Δ[n]) ≃ (Fin (p + 1) × Fin (q + 1) →o Fin (n + 1)) where
  toFun φ :=
    { toFun x := stdSimplex.obj₀Equiv (φ.app (op ⦋0⦌) (prodStdSimplex.obj₀Equiv.symm x))
      monotone' := by
        intro x y h
        convert (stdSimplex.objEquiv
          (φ.app _ (obj₁Mk h))).toOrderHom.monotone (show 0 ≤ 1 by simp) using 1
        · exact DFunLike.congr_fun
            (congr_fun (φ.naturality (SimplexCategory.const ⦋0⦌ ⦋1⦌ 0).op) (obj₁Mk h)) 0
        · exact DFunLike.congr_fun
            (congr_fun (φ.naturality (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1).op) (obj₁Mk h)) 0 }
  invFun f := homMk (fun d x ↦ stdSimplex.objMk (f.comp (prodStdSimplex.objEquiv x)))
    (fun _ _ _ ↦ rfl)
  left_inv φ := by
    ext ⟨d⟩ x : 2
    induction' d using SimplexCategory.rec with d
    ext i : 1
    exact DFunLike.congr_fun (congr_fun (φ.naturality (SimplexCategory.const ⦋0⦌ ⦋d⦌ i).op) x) 0
  right_inv _ := rfl

end prodStdSimplex

end SSet
