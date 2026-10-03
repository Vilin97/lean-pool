/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.ThetaIntegratedEnergy

/-! # Torus calculus for the separation estimates

Integral helpers over the unit cube, a coordinate integration by parts for smooth periodic functions
(deduced from `theta_divergence_pairing`), and the integration-by-parts identity that removes the
second derivative of the drift from the second-order commutator pairing. -/

@[expose] public section

open Homogenization MeasureTheory
open AVenhance.Infra.Section4

noncomputable section

namespace AVenhance.Infra.FullTheorem.Separation

open AVenhance

/-- `∫_{cell} (∂^w f)²`. -/
def en (w : List (Fin 2)) (f : Vec 2 → ℝ) : ℝ :=
  ∫ x in unitCube, (classicalWordDerivative w f x) ^ 2

theorem intOn {f : Vec 2 → ℝ} (hf : Continuous f) : IntegrableOn f unitCube :=
  thetaTime_integrableOn_unitCube hf

theorem abs_integral_le_of {F q : Vec 2 → ℝ} (hF : Continuous F) (hq : Continuous q)
    (h : ∀ x, |F x| ≤ q x) : |∫ x in unitCube, F x| ≤ ∫ x in unitCube, q x :=
  (abs_integral_le_integral_abs).trans
    (integral_mono (intOn hF.abs) (intOn hq) h)

theorem int_sum2 {φ : Fin 2 → Vec 2 → ℝ} (h : ∀ i, Continuous (φ i)) :
    ∫ x in unitCube, ∑ i : Fin 2, φ i x = ∑ i : Fin 2, ∫ x in unitCube, φ i x :=
  integral_finsetSum _ (fun i _ => intOn (h i))

theorem int_sum_sum {φ : Fin 2 → Fin 2 → Vec 2 → ℝ} (h : ∀ i j, Continuous (φ i j)) :
    ∫ x in unitCube, ∑ i : Fin 2, ∑ j : Fin 2, φ i j x =
      ∑ i : Fin 2, ∑ j : Fin 2, ∫ x in unitCube, φ i j x := by
  rw [int_sum2 (fun i => continuous_finsetSum _ (fun j _ => h i j))]
  exact Finset.sum_congr rfl (fun i _ => int_sum2 (h i))

theorem int_sum_sum_sum {φ : Fin 2 → Fin 2 → Fin 2 → Vec 2 → ℝ}
    (h : ∀ i j k, Continuous (φ i j k)) :
    ∫ x in unitCube, ∑ i : Fin 2, ∑ j : Fin 2, ∑ k : Fin 2, φ i j k x =
      ∑ i : Fin 2, ∑ j : Fin 2, ∑ k : Fin 2, ∫ x in unitCube, φ i j k x := by
  rw [int_sum2 (fun i => continuous_finsetSum _
    (fun j _ => continuous_finsetSum _ (fun k _ => h i j k)))]
  exact Finset.sum_congr rfl (fun i _ => int_sum_sum (h i))

theorem contDiff_word (w : List (Fin 2)) {f : Vec 2 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (classicalWordDerivative w f) :=
  classicalWordDerivative_contDiff w f hf

theorem cont_word (w : List (Fin 2)) {f : Vec 2 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    Continuous (classicalWordDerivative w f) :=
  (contDiff_word w hf).continuous

/-- Coordinate integration by parts for smooth periodic functions. -/
theorem ibp_coord {g h : Vec 2 → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hgp : IsZ2Periodic g) (hhp : IsZ2Periodic h) (j : Fin 2) :
    (∫ x in unitCube, g x * spaceGrad h x j) =
      -∫ x in unitCube, spaceGrad g x j * h x := by
  let F : Vec 2 → Vec 2 := fun x l => if l = j then h x else 0
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := by
    apply contDiff_pi.2
    intro l
    by_cases hl : l = j
    · simpa [F, hl] using hh
    · simpa [F, hl] using (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) fun _ : Vec 2 => (0 : ℝ))
  have hFp : IsZ2Periodic F := by
    intro k x
    funext l
    by_cases hl : l = j
    · simpa [F, hl] using hhp k x
    · simp [F, hl]
  have hdiv : ∀ x, vecDiv F x = spaceGrad h x j := by
    intro x
    unfold vecDiv
    rw [Fin.sum_univ_two]
    have h0 : spaceGrad (fun y => F y 0) x 0 =
        if (0 : Fin 2) = j then spaceGrad h x 0 else 0 := by
      by_cases hj : (0 : Fin 2) = j
      · subst hj; simp [F]
      · simp only [F, hj, ite_false]
        simp [spaceGrad]
    have h1 : spaceGrad (fun y => F y 1) x 1 =
        if (1 : Fin 2) = j then spaceGrad h x 1 else 0 := by
      by_cases hj : (1 : Fin 2) = j
      · subst hj; simp [F]
      · simp only [F, hj, ite_false]
        simp [spaceGrad]
    rw [h0, h1]
    fin_cases j <;> simp
  have hdot : ∀ x, vecDot (spaceGrad g x) (F x) = spaceGrad g x j * h x := by
    intro x
    simp [vecDot, F]
  have := theta_divergence_pairing hg hgp hF hFp
  simp only [hdiv, hdot] at this
  exact this

/-- The integration-by-parts identity of the second-order commutator pairing: only first
derivatives of the drift survive. -/
theorem triple_identity {F2 Fk mik mjk Fik : Vec 2 → ℝ}
    (hF2 : ContDiff ℝ (⊤ : ℕ∞) F2) (hFk : ContDiff ℝ (⊤ : ℕ∞) Fk)
    (hm : ContDiff ℝ (⊤ : ℕ∞) mik) (hF2p : IsZ2Periodic F2) (hFkp : IsZ2Periodic Fk)
    (hmp : IsZ2Periodic mik) (hmjk : Continuous mjk) (hFik : Continuous Fik) (j : Fin 2) :
    (∫ x in unitCube, F2 x * (spaceGrad mik x j * Fk x + mjk x * Fik x +
        mik x * spaceGrad Fk x j)) =
      ∫ x in unitCube, (-(mik x * spaceGrad F2 x j * Fk x) + F2 x * mjk x * Fik x) := by
  have cF2 := hF2.continuous
  have cFk := hFk.continuous
  have cm := hm.continuous
  have dF2 : Continuous (fun x => spaceGrad F2 x j) :=
    (cont_word [j] hF2)
  have dFk : Continuous (fun x => spaceGrad Fk x j) := cont_word [j] hFk
  have dm : Continuous (fun x => spaceGrad mik x j) := cont_word [j] hm
  have hprod : ContDiff ℝ (⊤ : ℕ∞) (fun x => F2 x * Fk x) := hF2.mul hFk
  have hprodp : IsZ2Periodic (fun x => F2 x * Fk x) := by
    intro k x
    simp only [hF2p k x, hFkp k x]
  have hibp := ibp_coord hprod hm hprodp hmp j
  have hgrad : ∀ x, spaceGrad (fun y => F2 y * Fk y) x j =
      F2 x * spaceGrad Fk x j + spaceGrad F2 x j * Fk x :=
    fun x => classicalProduct_firstDerivative F2 Fk hF2 hFk j x
  have iA : IntegrableOn (fun x => F2 x * Fk x * spaceGrad mik x j) unitCube :=
    intOn ((cF2.mul cFk).mul dm)
  have iB : IntegrableOn (fun x => F2 x * (mjk x * Fik x)) unitCube :=
    intOn (cF2.mul (hmjk.mul hFik))
  have iC : IntegrableOn (fun x => F2 x * (mik x * spaceGrad Fk x j)) unitCube :=
    intOn (cF2.mul (cm.mul dFk))
  have iD : IntegrableOn (fun x => F2 x * (spaceGrad Fk x j * mik x)) unitCube :=
    intOn (cF2.mul (dFk.mul cm))
  have iE : IntegrableOn (fun x => spaceGrad F2 x j * Fk x * mik x) unitCube :=
    intOn ((dF2.mul cFk).mul cm)
  have e1 : (∫ x in unitCube, F2 x * (spaceGrad mik x j * Fk x + mjk x * Fik x +
        mik x * spaceGrad Fk x j)) =
      (∫ x in unitCube, (F2 x * Fk x) * spaceGrad mik x j) +
      (∫ x in unitCube, F2 x * (mjk x * Fik x)) +
      (∫ x in unitCube, F2 x * (mik x * spaceGrad Fk x j)) := by
    have : (fun x => F2 x * (spaceGrad mik x j * Fk x + mjk x * Fik x +
        mik x * spaceGrad Fk x j)) = fun x =>
        (F2 x * Fk x * spaceGrad mik x j + F2 x * (mjk x * Fik x)) +
          F2 x * (mik x * spaceGrad Fk x j) := by
      funext x; ring
    have iAB : IntegrableOn (fun x => F2 x * Fk x * spaceGrad mik x j +
        F2 x * (mjk x * Fik x)) unitCube := iA.add iB
    rw [this, integral_add iAB iC, integral_add iA iB]
  have e2 : (∫ x in unitCube, spaceGrad (fun y => F2 y * Fk y) x j * mik x) =
      (∫ x in unitCube, F2 x * (spaceGrad Fk x j * mik x)) +
      (∫ x in unitCube, spaceGrad F2 x j * Fk x * mik x) := by
    have : (fun x => spaceGrad (fun y => F2 y * Fk y) x j * mik x) = fun x =>
        F2 x * (spaceGrad Fk x j * mik x) + spaceGrad F2 x j * Fk x * mik x := by
      funext x; rw [hgrad x]; ring
    rw [this, integral_add iD iE]
  have e3 : (∫ x in unitCube, (-(mik x * spaceGrad F2 x j * Fk x) + F2 x * mjk x * Fik x)) =
      -(∫ x in unitCube, spaceGrad F2 x j * Fk x * mik x) +
      (∫ x in unitCube, F2 x * (mjk x * Fik x)) := by
    have : (fun x => -(mik x * spaceGrad F2 x j * Fk x) + F2 x * mjk x * Fik x) = fun x =>
        -(spaceGrad F2 x j * Fk x * mik x) + F2 x * (mjk x * Fik x) := by
      funext x; ring
    have iE' : IntegrableOn (fun x => -(spaceGrad F2 x j * Fk x * mik x)) unitCube := iE.neg
    rw [this, integral_add iE' iB, integral_neg]
  have e4 : (∫ x in unitCube, F2 x * (mik x * spaceGrad Fk x j)) =
      ∫ x in unitCube, F2 x * (spaceGrad Fk x j * mik x) := by
    congr 1
    funext x
    ring
  have hibp' : (∫ x in unitCube, (F2 x * Fk x) * spaceGrad mik x j) =
      -((∫ x in unitCube, F2 x * (spaceGrad Fk x j * mik x)) +
      (∫ x in unitCube, spaceGrad F2 x j * Fk x * mik x)) := by
    rw [← e2]
    exact hibp
  rw [e1, e3, hibp', e4]
  ring

end AVenhance.Infra.FullTheorem.Separation
