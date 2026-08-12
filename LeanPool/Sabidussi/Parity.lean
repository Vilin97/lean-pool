/-
Copyright (c) 2026 Nikolay Ulyanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nikolay Ulyanov
-/
import LeanPool.Sabidussi.Color

/-!
# Parity algebra for the four-colour argument

This file records the two finite characteristic-two calculations used after the local choices
have been balanced: polarization of the quadratic form along an ordered word, and recovery of
the parity of all four colour classes from its linear and quadratic moments.
-/

namespace Sabidussi

open scoped BigOperators

/-- The sum of the bracket over all ordered pairs of positions, each pair occurring with its
smaller position second. -/
def orderedPairBracket {n : ℕ} (f : Fin n → Color) : F₂ :=
  ∑ i, ∑ j, if j < i then bracket (f i) (f j) else 0

private theorem orderedPairBracket_inner_castSucc {n : ℕ} (f : Fin (n + 1) → Color)
    (i : Fin n) :
    (∑ j : Fin (n + 1),
        if j < i.castSucc then bracket (f i.castSucc) (f j) else 0) =
      ∑ j : Fin n, if j < i then bracket (f i.castSucc) (f j.castSucc) else 0 := by
  rw [Fin.sum_univ_castSucc]
  have hnlt : ¬ Fin.last n < i.castSucc := (Fin.castSucc_lt_last i).asymm
  rw [ite_eq_right hnlt, add_zero]
  simp

private theorem orderedPairBracket_inner_last {n : ℕ} (f : Fin (n + 1) → Color) :
    (∑ j : Fin (n + 1),
        if j < Fin.last n then bracket (f (Fin.last n)) (f j) else 0) =
      ∑ j : Fin n, bracket (f j.castSucc) (f (Fin.last n)) := by
  calc
    _ = ∑ j : Fin n, bracket (f (Fin.last n)) (f j.castSucc) := by
      rw [Fin.sum_univ_castSucc]
      simp
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      exact bracket_comm _ _

/-- Adding the last position adds precisely its brackets with all earlier positions. -/
theorem orderedPairBracket_succ {n : ℕ} (f : Fin (n + 1) → Color) :
    orderedPairBracket f =
      orderedPairBracket (fun i : Fin n ↦ f i.castSucc) +
        bracket (∑ i : Fin n, f i.castSucc) (f (Fin.last n)) := by
  unfold orderedPairBracket
  rw [Fin.sum_univ_castSucc]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    exact orderedPairBracket_inner_castSucc f i
  · rw [orderedPairBracket_inner_last]
    let g : Color →+ F₂ :=
      { toFun := fun x ↦ bracket x (f (Fin.last n))
        map_zero' := bracket_zero_left _
        map_add' := fun x y ↦ bracket_add_left x y _ }
    change (∑ i : Fin n, g (f i.castSucc)) = g (∑ i : Fin n, f i.castSucc)
    exact (map_sum g (fun i : Fin n ↦ f i.castSucc) Finset.univ).symm

/-- Polarization of `quadratic` along a finite linearly ordered word. -/
theorem quadratic_sum_fin : ∀ {n : ℕ} (f : Fin n → Color),
    quadratic (∑ i, f i) = (∑ i, quadratic (f i)) + orderedPairBracket f
  | 0, f => by simp [orderedPairBracket, quadratic]
  | n + 1, f => by
    rw [Fin.sum_univ_castSucc, quadratic_add,
      quadratic_sum_fin (fun i : Fin n ↦ f i.castSucc), orderedPairBracket_succ,
      Fin.sum_univ_castSucc]
    abel

/-- The positions carrying a specified colour. -/
def colorFiber {I : Type*} [Fintype I] (f : I → Color) (c : Color) :
    Finset I :=
  Finset.univ.filter fun i ↦ f i = c

theorem cast_colorFiber_card {I : Type*} [Fintype I]
    (f : I → Color) (c : Color) :
    ((colorFiber f c).card : F₂) = ∑ i, if f i = c then 1 else 0 := by
  symm
  simp [colorFiber]

private theorem colorIndicator_eq_product (x c : Color) :
    (if x = c then 1 else 0 : F₂) =
      (1 + x.1 + c.1) * (1 + x.2 + c.2) := by
  rcases x with ⟨a, b⟩
  rcases c with ⟨u, v⟩
  fin_cases a <;> fin_cases b <;> fin_cases u <;> fin_cases v <;> decide

private theorem colorIndicator_eq_moments (x c : Color) :
    (if x = c then 1 else 0 : F₂) =
      (1 + c.1) * (1 + c.2) + (1 + c.2) * x.1 +
        (1 + c.1) * x.2 + quadratic x := by
  rw [colorIndicator_eq_product]
  simp only [quadratic]
  ring

private def colorFstHom : Color →+ F₂ where
  toFun := Prod.fst
  map_zero' := rfl
  map_add' := fun _ _ ↦ rfl

private def colorSndHom : Color →+ F₂ where
  toFun := Prod.snd
  map_zero' := rfl
  map_add' := fun _ _ ↦ rfl

/-- In an even finite family of four colours, vanishing of the two linear moments and of the
quadratic moment is equivalent to every colour occurring evenly.  This is the forward direction
needed in the Sabidussi argument. -/
theorem colorFiber_card_even_of_moments {I : Type*} [Fintype I]
    (f : I → Color) (hcard : Even (Fintype.card I))
    (hsum : ∑ i, f i = 0) (hquadratic : ∑ i, quadratic (f i) = 0) (c : Color) :
    Even (colorFiber f c).card := by
  have hfst : ∑ i, (f i).1 = 0 := by
    calc
      ∑ i, (f i).1 = colorFstHom (∑ i, f i) := by
        simp [colorFstHom]
      _ = 0 := by rw [hsum]; rfl
  have hsnd : ∑ i, (f i).2 = 0 := by
    calc
      ∑ i, (f i).2 = colorSndHom (∑ i, f i) := by
        simp [colorSndHom]
      _ = 0 := by rw [hsum]; rfl
  have hcardF₂ : (Fintype.card I : F₂) = 0 :=
    ZMod.natCast_eq_zero_iff_even.mpr hcard
  change ∑ i, (f i).1 * (f i).2 = 0 at hquadratic
  apply ZMod.natCast_eq_zero_iff_even.mp
  rw [cast_colorFiber_card]
  simp_rw [colorIndicator_eq_moments]
  simp only [Finset.sum_add_distrib]
  rw [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum, ← Finset.mul_sum]
  simp [hcardF₂, hfst, hsnd, hquadratic]

end Sabidussi
