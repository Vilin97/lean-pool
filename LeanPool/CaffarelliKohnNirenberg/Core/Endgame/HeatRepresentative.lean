/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.HeatPotential.SubordinatedCampanato
public import LeanPool.CaffarelliKohnNirenberg.Statements.ParabolicHolderVecNormLE

/-! # Quantitative vector representatives of heat potentials

The scalar heat estimate is applied to each coordinate. Both the local value
bound and the global Hölder constant remain explicit functions of the source
norms and the local averages of the potential.
-/

@[expose] public section

open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory Set
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Core.HeatPotential

noncomputable section
namespace CKN.Core.Endgame

/-- The explicit scalar Hölder coefficient in the heat-potential estimate. -/
def heatHolderCoefficient (F : ParabolicPoint → ℝ)
    (G : Fin 3 → ParabolicPoint → ℝ) (γ θ₀ θ₁ P : ℝ) : ℝ :=
  let V : ℝ := (volume (parabolicCylinder 0 0 1)).toReal
  let BF : ℝ := V ^ (1 - 1 / P) * (morreyNorm P θ₀ F).toReal
  let BG : Fin 3 → ℝ := fun i =>
    V ^ (1 - 1 / P) * (morreyNorm P θ₁ (G i)).toReal
  let Cnear : ℝ :=
    2 * 1000 * (2 : ℝ) ^ (8 - 5 / θ₀) *
        (1 - (2 : ℝ) ^ (-γ))⁻¹ * (256 : ℝ) ^ γ * BF +
      ∑ i, 2 * 300000 * (2 : ℝ) ^ (10 - 1 - 5 / θ₁) *
        (1 - (2 : ℝ) ^ (-γ))⁻¹ * (256 : ℝ) ^ γ * BG i
  let C : ℝ :=
    (1800000 * (2 : ℝ) ^ (8 * (5 * (1 - 1 / θ₀)) - 16) +
      40000000 * (2 : ℝ) ^ (8 * (5 * (1 - 1 / θ₀)) - 20)) * BF +
      ∑ i, (120000000 * (2 : ℝ) ^ (8 * (5 * (1 - 1 / θ₁)) - 20) +
        120000000000 * (2 : ℝ) ^ (8 * (5 * (1 - 1 / θ₁)) - 24)) * BG i
  parabolicCampanatoHolderConstant γ P *
    (Cnear + C * (1 - (2 : ℝ) ^ (γ - 1))⁻¹)

/-- The sum of the absolute scalar Hölder coefficients. -/
def vectorHeatHolderCoefficient (F : ParabolicPoint → Vec3)
    (G : Fin 3 → ParabolicPoint → Vec3) (γ θ₀ θ₁ P : ℝ) : ℝ :=
  ∑ i, |heatHolderCoefficient (fun x => F x i) (fun j x => G j x i) γ θ₀ θ₁ P|

/-- An explicit bound for the vector potential on a ball. -/
def vectorHeatValueBound (F : ParabolicPoint → Vec3)
    (G : Fin 3 → ParabolicPoint → Vec3) (γ θ₀ θ₁ P : ℝ)
    (z : ParabolicPoint) (R : ℝ) : ℝ :=
  ∑ i : Fin 3, |(2 : ℝ) ^ γ *
    heatHolderCoefficient (fun x => F x i) (fun j x => G j x i) γ θ₀ θ₁ P *
      R ^ γ +
        (⨍ x in Metric.ball z R,
          |heatPotential (fun y => F y i) (fun j y => G j y i) x| ^ P) ^ (1 / P)|

private lemma vec3EuclideanNorm_le_sum_abs (v : Vec3) :
    vec3EuclideanNorm v ≤ ∑ i, |v i| := by
  rw [vec3EuclideanNorm]
  apply Real.sqrt_le_iff.mpr
  constructor
  · exact Finset.sum_nonneg fun i _ => abs_nonneg _
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change v 0 ^ 2 + (v 1 ^ 2 + v 2 ^ 2) ≤
      (|v 0| + (|v 1| + |v 2|)) ^ 2
    have h0 := sq_abs (v 0)
    have h1 := sq_abs (v 1)
    have h2 := sq_abs (v 2)
    have h01 := mul_nonneg (abs_nonneg (v 0)) (abs_nonneg (v 1))
    have h02 := mul_nonneg (abs_nonneg (v 0)) (abs_nonneg (v 2))
    have h12 := mul_nonneg (abs_nonneg (v 1)) (abs_nonneg (v 2))
    nlinarith only [h0, h1, h2, h01, h02, h12]

/-- Compactly supported Morrey sources have a common vector representative,
with an explicit local norm on every parabolic ball. -/
theorem vector_heat_representative_and_seminorm_of_morrey
    {F : ParabolicPoint → Vec3} {G : Fin 3 → ParabolicPoint → Vec3}
    {γ θ₀ θ₁ P : ℝ}
    (hγ : 0 < γ) (hγ1 : γ < 1)
    (hθ₀ : 1 / θ₀ = (2 - γ) / 5)
    (hθ₁ : 1 / θ₁ = (1 - γ) / 5)
    (hP : 1 ≤ P) (hPθ₀ : P ≤ θ₀) (hPθ₁ : P ≤ θ₁)
    (hF : ∀ i, AEMeasurable (fun x => F x i) volume)
    (hG : ∀ j i, AEMeasurable (fun x => G j x i) volume)
    (hNF : ∀ i, morreyNorm P θ₀ (fun x => F x i) < ∞)
    (hNG : ∀ j i, morreyNorm P θ₁ (fun x => G j x i) < ∞)
    (hSupportF : ∀ i, HasCompactSupport (fun x => F x i))
    (hSupportG : ∀ j i, HasCompactSupport (fun x => G j x i)) :
    ∃ v : ParabolicPoint → Vec3,
      v =ᵐ[volume] (fun x i => heatPotential (fun y => F y i)
        (fun j y => G j y i) x) ∧
      (∀ x y, vec3EuclideanNorm (v x - v y) ≤
        vectorHeatHolderCoefficient F G γ θ₀ θ₁ P * parabolicDist x y ^ γ) ∧
      ∀ z R, 0 < R →
        ParabolicHolderVecNormLE (Metric.ball z R) v γ
          (vectorHeatValueBound F G γ θ₀ θ₁ P z R +
            vectorHeatHolderCoefficient F G γ θ₀ θ₁ P) := by
  have hscalar := fun i : Fin 3 => prop_heat_morrey_hoelder
    hγ hγ1 hθ₀ hθ₁ hP hPθ₀ hPθ₁ (hF i) (fun j => hG j i)
      (hNF i) (fun j => hNG j i) (hSupportF i) (fun j => hSupportG j i)
  change ∀ i : Fin 3, ∃ v : ParabolicPoint → ℝ,
    v =ᵐ[volume] heatPotential (fun x => F x i) (fun j x => G j x i) ∧
    ParabolicHolderSeminormLE univ v γ
      (heatHolderCoefficient (fun x => F x i) (fun j x => G j x i) γ θ₀ θ₁ P) ∧
    (∀ z R, 0 < R → ∀ w ∈ Metric.ball z R,
      |v w| ≤ (2 : ℝ) ^ γ *
        heatHolderCoefficient (fun x => F x i) (fun j x => G j x i) γ θ₀ θ₁ P *
          R ^ γ + (⨍ x in Metric.ball z R,
            |heatPotential (fun y => F y i) (fun j y => G j y i) x| ^ P) ^ (1 / P))
    at hscalar
  choose v hv hholder hvalue using hscalar
  have hglobal : ∀ x y, vec3EuclideanNorm ((fun i => v i x) - (fun i => v i y)) ≤
      vectorHeatHolderCoefficient F G γ θ₀ θ₁ P * parabolicDist x y ^ γ := by
    intro x y
    refine (vec3EuclideanNorm_le_sum_abs _).trans ?_
    rw [vectorHeatHolderCoefficient, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    exact (hholder i x (mem_univ _) y (mem_univ _)).trans
      (mul_le_mul_of_nonneg_right (le_abs_self _)
        (Real.rpow_nonneg (parabolicDist_nonneg x y) γ))
  refine ⟨fun x i => v i x, ?_, hglobal, ?_⟩
  · filter_upwards [ae_all_iff.mpr hv] with x hx
    exact funext hx
  · intro z R _hR
    refine ⟨vectorHeatValueBound F G γ θ₀ θ₁ P z R,
      vectorHeatHolderCoefficient F G γ θ₀ θ₁ P,
      Finset.sum_nonneg (fun i _ => abs_nonneg _),
      Finset.sum_nonneg (fun i _ => abs_nonneg _), le_rfl, ?_, ?_⟩
    · intro x hx
      refine (vec3EuclideanNorm_le_sum_abs _).trans (Finset.sum_le_sum fun i _ => ?_)
      exact (hvalue i z R _hR x hx).trans (le_abs_self _)
    · intro x _hx y _hy
      exact hglobal x y

/-- The local norm estimate, without separately retaining the global seminorm. -/
theorem vector_heat_representative_of_morrey
    {F : ParabolicPoint → Vec3} {G : Fin 3 → ParabolicPoint → Vec3}
    {γ θ₀ θ₁ P : ℝ}
    (hγ : 0 < γ) (hγ1 : γ < 1)
    (hθ₀ : 1 / θ₀ = (2 - γ) / 5)
    (hθ₁ : 1 / θ₁ = (1 - γ) / 5)
    (hP : 1 ≤ P) (hPθ₀ : P ≤ θ₀) (hPθ₁ : P ≤ θ₁)
    (hF : ∀ i, AEMeasurable (fun x => F x i) volume)
    (hG : ∀ j i, AEMeasurable (fun x => G j x i) volume)
    (hNF : ∀ i, morreyNorm P θ₀ (fun x => F x i) < ∞)
    (hNG : ∀ j i, morreyNorm P θ₁ (fun x => G j x i) < ∞)
    (hSupportF : ∀ i, HasCompactSupport (fun x => F x i))
    (hSupportG : ∀ j i, HasCompactSupport (fun x => G j x i)) :
    ∃ v : ParabolicPoint → Vec3,
      v =ᵐ[volume] (fun x i => heatPotential (fun y => F y i)
        (fun j y => G j y i) x) ∧
      ∀ z R, 0 < R →
        ParabolicHolderVecNormLE (Metric.ball z R) v γ
          (vectorHeatValueBound F G γ θ₀ θ₁ P z R +
            vectorHeatHolderCoefficient F G γ θ₀ θ₁ P) := by
  obtain ⟨v, hv, _hsemi, hlocal⟩ := vector_heat_representative_and_seminorm_of_morrey
    hγ hγ1 hθ₀ hθ₁ hP hPθ₀ hPθ₁ hF hG hNF hNG hSupportF hSupportG
  exact ⟨v, hv, hlocal⟩

end CKN.Core.Endgame
