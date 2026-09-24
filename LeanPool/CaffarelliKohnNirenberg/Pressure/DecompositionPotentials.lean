/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.Decomposition
public import LeanPool.CaffarelliKohnNirenberg.Pressure.DerivativeAdjoint

/-!
# Decomposition Potentials

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat

noncomputable section

namespace CKN

/-! The eight explicit potentials in the local pressure decomposition. -/

def pressureP2 (η : Vec3 → ℝ) (u : ParabolicPoint → Vec3) (c : ℝ → Vec3)
    (s : ℝ) : Vec3 → ℝ := fun x =>
  ∑ i, ∑ j, pressureNewtonianPotential
    (fun y => mixedSecond η i j y * pressureUTensor u c (y, s) i j) x

def pressureP3 (η : Vec3 → ℝ) (u : ParabolicPoint → Vec3) (c : ℝ → Vec3)
    (s : ℝ) : Vec3 → ℝ := fun x =>
  ∑ i, ∑ j, pressureNewtonianDerivativePotential j
    (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η i y) x

def pressureP4 (η : Vec3 → ℝ) (u : ParabolicPoint → Vec3) (c : ℝ → Vec3)
    (s : ℝ) : Vec3 → ℝ := fun x =>
  ∑ i, ∑ j, pressureNewtonianDerivativePotential i
    (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η j y) x

def pressureP5 (η : Vec3 → ℝ) (p : ParabolicPoint → ℝ) (s : ℝ) : Vec3 → ℝ := fun x =>
  -pressureNewtonianPotential (fun y => p (y, s) * spatialLaplacian η y) x

def pressureP6 (η : Vec3 → ℝ) (p : ParabolicPoint → ℝ) (s : ℝ) : Vec3 → ℝ := fun x =>
  -2 * ∑ j, pressureNewtonianDerivativePotential j
    (fun y => spatialDeriv η j y * p (y, s)) x

def pressureP7 (η : Vec3 → ℝ) (f : ParabolicPoint → Vec3) (s : ℝ) : Vec3 → ℝ := fun x =>
  -∑ j, pressureNewtonianDerivativePotential j
    (fun y => η y * f (y, s) j) x

def pressureP8 (η : Vec3 → ℝ) (f : ParabolicPoint → Vec3) (s : ℝ) : Vec3 → ℝ := fun x =>
  -∑ j, pressureNewtonianPotential
    (fun y => spatialDeriv η j y * f (y, s) j) x

def pressureP1 (η : Vec3 → ℝ) (u : ParabolicPoint → Vec3) (c : ℝ → Vec3)
    (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3) (s : ℝ) : Vec3 → ℝ := fun x =>
  η x * p (x, s) - (pressureP2 η u c s x + pressureP3 η u c s x +
    pressureP4 η u c s x + pressureP5 η p s x + pressureP6 η p s x +
    pressureP7 η f s x + pressureP8 η f s x)

theorem pressure_decomposition_pointwise (η : Vec3 → ℝ)
    (u : ParabolicPoint → Vec3) (c : ℝ → Vec3) (p : ParabolicPoint → ℝ)
    (f : ParabolicPoint → Vec3) (s : ℝ) (x : Vec3) :
    η x * p (x, s) = pressureP1 η u c p f s x + pressureP2 η u c s x +
      pressureP3 η u c s x + pressureP4 η u c s x + pressureP5 η p s x +
      pressureP6 η p s x + pressureP7 η f s x + pressureP8 η f s x := by
  simp only [pressureP1]
  ring

private theorem pressure_locallyIntegrable_sum₂
    {F : Fin 3 → Fin 3 → Vec3 → ℝ}
    (hF : ∀ i j, LocallyIntegrable (F i j) volume) :
    LocallyIntegrable (fun x => ∑ i, ∑ j, F i j x) volume := by
  classical
  have hsum (i : Fin 3) : LocallyIntegrable (fun x => ∑ j, F i j x) volume := by
    simpa only [Finset.sum_apply] using
      (locallyIntegrable_finsetSum (Finset.univ : Finset (Fin 3))
        (fun j _hj => hF i j))
  simpa only [Finset.sum_apply] using
    (locallyIntegrable_finsetSum (Finset.univ : Finset (Fin 3))
      (fun i _hi => hsum i))

theorem pressureP2_locallyIntegrable {η : Vec3 → ℝ}
    {u : ParabolicPoint → Vec3} {c : ℝ → Vec3} {s : ℝ}
    (hInt : ∀ i j, Integrable
      (fun y => mixedSecond η i j y * pressureUTensor u c (y, s) i j) volume)
    (hSupp : ∀ i j, HasCompactSupport
      (fun y => mixedSecond η i j y * pressureUTensor u c (y, s) i j)) :
    LocallyIntegrable (pressureP2 η u c s) volume := by
  apply pressure_locallyIntegrable_sum₂
  intro i j
  exact pressureNewtonianPotential_locallyIntegrable (hInt i j) (hSupp i j)

theorem pressureP3_locallyIntegrable {η : Vec3 → ℝ}
    {u : ParabolicPoint → Vec3} {c : ℝ → Vec3} {s : ℝ}
    (hInt : ∀ i j, Integrable
      (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η i y) volume)
    (hSupp : ∀ i j, HasCompactSupport
      (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η i y)) :
    LocallyIntegrable (pressureP3 η u c s) volume := by
  apply pressure_locallyIntegrable_sum₂
  intro i j
  exact pressureNewtonianDerivativePotential_locallyIntegrable j (hInt i j) (hSupp i j)

theorem pressureP4_locallyIntegrable {η : Vec3 → ℝ}
    {u : ParabolicPoint → Vec3} {c : ℝ → Vec3} {s : ℝ}
    (hInt : ∀ i j, Integrable
      (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η j y) volume)
    (hSupp : ∀ i j, HasCompactSupport
      (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η j y)) :
    LocallyIntegrable (pressureP4 η u c s) volume := by
  apply pressure_locallyIntegrable_sum₂
  intro i j
  exact pressureNewtonianDerivativePotential_locallyIntegrable i (hInt i j) (hSupp i j)

theorem pressureP5_locallyIntegrable {η : Vec3 → ℝ} {p : ParabolicPoint → ℝ} {s : ℝ}
    (hInt : Integrable (fun y => p (y, s) * spatialLaplacian η y) volume)
    (hSupp : HasCompactSupport (fun y => p (y, s) * spatialLaplacian η y)) :
    LocallyIntegrable (pressureP5 η p s) volume := by
  change LocallyIntegrable
    (fun x => -pressureNewtonianPotential
      (fun y => p (y, s) * spatialLaplacian η y) x) volume
  exact (pressureNewtonianPotential_locallyIntegrable hInt hSupp).neg

theorem pressureP6_locallyIntegrable {η : Vec3 → ℝ} {p : ParabolicPoint → ℝ} {s : ℝ}
    (hInt : ∀ j, Integrable (fun y => spatialDeriv η j y * p (y, s)) volume)
    (hSupp : ∀ j, HasCompactSupport (fun y => spatialDeriv η j y * p (y, s))) :
    LocallyIntegrable (pressureP6 η p s) volume := by
  have hsum : LocallyIntegrable
      (fun x => ∑ j, pressureNewtonianDerivativePotential j
        (fun y => spatialDeriv η j y * p (y, s)) x) volume := by
    simpa only [Finset.sum_apply] using
      (locallyIntegrable_finsetSum (Finset.univ : Finset (Fin 3))
        (fun j _hj => pressureNewtonianDerivativePotential_locallyIntegrable j
          (hInt j) (hSupp j)))
  have heq : pressureP6 η p s =
      (-2 : ℝ) • (fun x => ∑ j, pressureNewtonianDerivativePotential j
        (fun y => spatialDeriv η j y * p (y, s)) x) := by
    funext x
    simp [pressureP6]
  rw [heq]
  exact hsum.smul (-2 : ℝ)

theorem pressureP7_locallyIntegrable {η : Vec3 → ℝ}
    {f : ParabolicPoint → Vec3} {s : ℝ}
    (hInt : ∀ j, Integrable (fun y => η y * f (y, s) j) volume)
    (hSupp : ∀ j, HasCompactSupport (fun y => η y * f (y, s) j)) :
    LocallyIntegrable (pressureP7 η f s) volume := by
  change LocallyIntegrable
    (fun x => -(∑ j, pressureNewtonianDerivativePotential j
      (fun y => η y * f (y, s) j) x)) volume
  have hsum : LocallyIntegrable
      (fun x => ∑ j, pressureNewtonianDerivativePotential j
        (fun y => η y * f (y, s) j) x) volume := by
    simpa only [Finset.sum_apply] using
      (locallyIntegrable_finsetSum (Finset.univ : Finset (Fin 3))
        (fun j _hj => pressureNewtonianDerivativePotential_locallyIntegrable j
          (hInt j) (hSupp j)))
  exact hsum.neg

theorem pressureP8_locallyIntegrable {η : Vec3 → ℝ}
    {f : ParabolicPoint → Vec3} {s : ℝ}
    (hInt : ∀ j, Integrable (fun y => spatialDeriv η j y * f (y, s) j) volume)
    (hSupp : ∀ j, HasCompactSupport (fun y => spatialDeriv η j y * f (y, s) j)) :
    LocallyIntegrable (pressureP8 η f s) volume := by
  have hsum : LocallyIntegrable
      (fun x => ∑ j, pressureNewtonianPotential
        (fun y => spatialDeriv η j y * f (y, s) j) x) volume := by
    simpa only [Finset.sum_apply] using
      (locallyIntegrable_finsetSum (Finset.univ : Finset (Fin 3))
        (fun j _hj => pressureNewtonianPotential_locallyIntegrable (hInt j) (hSupp j)))
  change LocallyIntegrable
    (fun x => -(∑ j, pressureNewtonianPotential
      (fun y => spatialDeriv η j y * f (y, s) j) x)) volume
  exact hsum.neg

private theorem decomposition_laplacian_hasCompactSupport {ψ : Vec3 → ℝ}
    (hψc : HasCompactSupport ψ) : HasCompactSupport (spatialLaplacian ψ) := by
  have hdiag (i : Fin 3) : HasCompactSupport
      (spatialDeriv (spatialDeriv ψ i) i) :=
    (hψc.fderiv_apply (𝕜 := ℝ) (basisVec i)).fderiv_apply
      (𝕜 := ℝ) (basisVec i)
  have h01 : HasCompactSupport (fun y : Vec3 =>
      spatialDeriv (spatialDeriv ψ (0 : Fin 3)) 0 y +
        spatialDeriv (spatialDeriv ψ (1 : Fin 3)) 1 y) := by
    convert (hdiag (0 : Fin 3)).add (hdiag (1 : Fin 3)) using 1
  have hsum : HasCompactSupport (fun y : Vec3 =>
      spatialDeriv (spatialDeriv ψ (0 : Fin 3)) 0 y +
        spatialDeriv (spatialDeriv ψ (1 : Fin 3)) 1 y +
          spatialDeriv (spatialDeriv ψ (2 : Fin 3)) 2 y) := by
    convert h01.add (hdiag (2 : Fin 3)) using 1
  change HasCompactSupport (fun y : Vec3 =>
    ∑ i : Fin 3, spatialDeriv (spatialDeriv ψ i) i y)
  simpa only [Fin.sum_univ_three] using hsum

private theorem pressure_derivative_sum_distributional_pairing
    {G : Fin 3 → Vec3 → ℝ} {ψ : Vec3 → ℝ}
    (hInt : ∀ j, Integrable (G j) volume)
    (hSupp : ∀ j, HasCompactSupport (G j))
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    ∫ x, (∑ j, pressureNewtonianDerivativePotential j (G j) x) *
        spatialLaplacian ψ x =
      ∑ j, ∫ y, G j y * CKN.spatialDeriv ψ j y := by
  have hφ : ContDiff ℝ (⊤ : ℕ∞) (spatialLaplacian ψ) :=
    contDiff_spatialLaplacian_smooth hψ
  have hφc : HasCompactSupport (spatialLaplacian ψ) :=
    decomposition_laplacian_hasCompactSupport hψc
  have hterm (j : Fin 3) : Integrable
      (fun x => pressureNewtonianDerivativePotential j (G j) x *
        spatialLaplacian ψ x) volume :=
    pressureNewtonianDerivativePotential_mul_smooth_integrable
      (hInt j) (hSupp j) hφ hφc
  have hpair (j : Fin 3) :
      ∫ x, pressureNewtonianDerivativePotential j (G j) x *
        spatialLaplacian ψ x = ∫ y, G j y * CKN.spatialDeriv ψ j y :=
    pressureNewtonianDerivativePotential_distributional_pairing_smooth
      (hInt j) (hSupp j) hψ hψc
  calc
    ∫ x, (∑ j, pressureNewtonianDerivativePotential j (G j) x) *
        spatialLaplacian ψ x =
        ∫ x, ∑ j, pressureNewtonianDerivativePotential j (G j) x *
          spatialLaplacian ψ x := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [Finset.sum_mul]
    _ = ∑ j, ∫ x, pressureNewtonianDerivativePotential j (G j) x *
        spatialLaplacian ψ x := by
      rw [integral_finsetSum (s := Finset.univ)]
      intro j hj
      exact hterm j
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      exact hpair j

theorem pressureP2_distributional_pairing {η : Vec3 → ℝ}
    {u : ParabolicPoint → Vec3} {c : ℝ → Vec3} {s : ℝ}
    {ψ : Vec3 → ℝ}
    (hInt : ∀ i j, Integrable
      (fun y => mixedSecond η i j y * pressureUTensor u c (y, s) i j) volume)
    (hSupp : ∀ i j, HasCompactSupport
      (fun y => mixedSecond η i j y * pressureUTensor u c (y, s) i j))
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    ∫ x, pressureP2 η u c s x * spatialLaplacian ψ x =
      ∑ i, ∑ j, ∫ y, mixedSecond η i j y *
        pressureUTensor u c (y, s) i j * ψ y := by
  have hφ : ContDiff ℝ (⊤ : ℕ∞) (spatialLaplacian ψ) :=
    contDiff_spatialLaplacian_smooth hψ
  have hφc : HasCompactSupport (spatialLaplacian ψ) :=
    decomposition_laplacian_hasCompactSupport hψc
  have hterm (i j : Fin 3) : Integrable
      (fun x => pressureNewtonianPotential
        (fun y => mixedSecond η i j y * pressureUTensor u c (y, s) i j) x *
          spatialLaplacian ψ x) volume :=
    pressureNewtonianPotential_mul_smooth_integrable (hInt i j) (hSupp i j) hφ hφc
  have hpair (i j : Fin 3) :
      ∫ x, pressureNewtonianPotential
        (fun y => mixedSecond η i j y * pressureUTensor u c (y, s) i j) x *
          spatialLaplacian ψ x =
        ∫ y, mixedSecond η i j y * pressureUTensor u c (y, s) i j * ψ y := by
    exact pressureNewtonianPotential_distributional_pairing
      (hInt i j) (hSupp i j) hψ hψc
  change ∫ x, (∑ i, ∑ j, pressureNewtonianPotential
      (fun y => mixedSecond η i j y * pressureUTensor u c (y, s) i j) x) *
        spatialLaplacian ψ x = _
  calc
    _ = ∫ x, ∑ i, ∑ j, pressureNewtonianPotential
        (fun y => mixedSecond η i j y * pressureUTensor u c (y, s) i j) x *
          spatialLaplacian ψ x := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [Finset.sum_mul]
    _ = ∑ i, ∑ j, ∫ x, pressureNewtonianPotential
        (fun y => mixedSecond η i j y * pressureUTensor u c (y, s) i j) x *
          spatialLaplacian ψ x := by
      rw [integral_finsetSum (s := Finset.univ)]
      · apply Finset.sum_congr rfl
        intro i hi
        rw [integral_finsetSum (s := Finset.univ)]
        intro j hj
        exact hterm i j
      · intro i hi
        exact integrable_finsetSum (Finset.univ : Finset (Fin 3))
          (fun j hj => hterm i j)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact hpair i j

theorem pressureP5_distributional_pairing {η : Vec3 → ℝ}
    {p : ParabolicPoint → ℝ} {s : ℝ} {ψ : Vec3 → ℝ}
    (hInt : Integrable (fun y => p (y, s) * spatialLaplacian η y) volume)
    (hSupp : HasCompactSupport
      (fun y => p (y, s) * spatialLaplacian η y))
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    ∫ x, pressureP5 η p s x * spatialLaplacian ψ x =
      -∫ y, p (y, s) * spatialLaplacian η y * ψ y := by
  change ∫ x, -pressureNewtonianPotential
      (fun y => p ((y, s) : ParabolicPoint) * spatialLaplacian η y) x *
        spatialLaplacian ψ x = _
  rw [show (fun x => -pressureNewtonianPotential
      (fun y => p ((y, s) : ParabolicPoint) * spatialLaplacian η y) x *
        spatialLaplacian ψ x) =
      fun x => -(pressureNewtonianPotential
        (fun y => p ((y, s) : ParabolicPoint) * spatialLaplacian η y) x *
          spatialLaplacian ψ x) by
        funext x
        ring]
  rw [MeasureTheory.integral_neg]
  rw [pressureNewtonianPotential_distributional_pairing hInt hSupp hψ hψc]

theorem pressureP8_distributional_pairing {η : Vec3 → ℝ}
    {f : ParabolicPoint → Vec3} {s : ℝ} {ψ : Vec3 → ℝ}
    (hInt : ∀ j, Integrable
      (fun y => spatialDeriv η j y * f (y, s) j) volume)
    (hSupp : ∀ j, HasCompactSupport
      (fun y => spatialDeriv η j y * f (y, s) j))
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    ∫ x, pressureP8 η f s x * spatialLaplacian ψ x =
      -∑ j, ∫ y, spatialDeriv η j y * f (y, s) j * ψ y := by
  have hφ : ContDiff ℝ (⊤ : ℕ∞) (spatialLaplacian ψ) :=
    contDiff_spatialLaplacian_smooth hψ
  have hφc : HasCompactSupport (spatialLaplacian ψ) :=
    decomposition_laplacian_hasCompactSupport hψc
  have hterm (j : Fin 3) : Integrable
      (fun x => pressureNewtonianPotential
        (fun y => spatialDeriv η j y * f (y, s) j) x *
          spatialLaplacian ψ x) volume :=
    pressureNewtonianPotential_mul_smooth_integrable (hInt j) (hSupp j) hφ hφc
  have hpair (j : Fin 3) :
      ∫ x, pressureNewtonianPotential
        (fun y => spatialDeriv η j y * f (y, s) j) x *
          spatialLaplacian ψ x =
        ∫ y, spatialDeriv η j y * f (y, s) j * ψ y :=
    pressureNewtonianPotential_distributional_pairing
      (hInt j) (hSupp j) hψ hψc
  change ∫ x, -(∑ j, pressureNewtonianPotential
      (fun y => spatialDeriv η j y * f (y, s) j) x) *
        spatialLaplacian ψ x = _
  have hsum : (fun x => -(∑ j, pressureNewtonianPotential
      (fun y => spatialDeriv η j y * f (y, s) j) x) *
        spatialLaplacian ψ x) =
      (fun x => -∑ j, pressureNewtonianPotential
        (fun y => spatialDeriv η j y * f (y, s) j) x *
          spatialLaplacian ψ x) := by
    funext x
    rw [show -(∑ j, pressureNewtonianPotential
        (fun y => spatialDeriv η j y * f ((y, s) : ParabolicPoint) j) x) =
        ∑ j, -pressureNewtonianPotential
          (fun y => spatialDeriv η j y * f ((y, s) : ParabolicPoint) j) x by
      rw [← Finset.sum_neg_distrib]]
    simp only [Finset.sum_mul, neg_mul]
    rw [Finset.sum_neg_distrib]
  rw [hsum, MeasureTheory.integral_neg]
  rw [integral_finsetSum (s := Finset.univ)]
  · apply congrArg Neg.neg
    apply Finset.sum_congr rfl
    intro j hj
    exact hpair j
  · intro j hj
    exact hterm j

theorem pressureP6_distributional_pairing {η : Vec3 → ℝ}
    {p : ParabolicPoint → ℝ} {s : ℝ} {ψ : Vec3 → ℝ}
    (hInt : ∀ j, Integrable
      (fun y => spatialDeriv η j y * p (y, s)) volume)
    (hSupp : ∀ j, HasCompactSupport
      (fun y => spatialDeriv η j y * p (y, s)))
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    ∫ x, pressureP6 η p s x * spatialLaplacian ψ x =
      -2 * ∑ j, ∫ y, spatialDeriv η j y * p (y, s) *
        CKN.spatialDeriv ψ j y := by
  let G : Fin 3 → Vec3 → ℝ := fun j y => spatialDeriv η j y * p (y, s)
  have hsum := pressure_derivative_sum_distributional_pairing
    (fun j => hInt j) (fun j => hSupp j) hψ hψc
  change ∫ x, (-2 : ℝ) * (∑ j,
      pressureNewtonianDerivativePotential j (G j) x) *
        spatialLaplacian ψ x = _
  have heq : (fun x => (-2 : ℝ) * (∑ j,
      pressureNewtonianDerivativePotential j (G j) x) *
        spatialLaplacian ψ x) =
      (fun x => (-2 : ℝ) * ((∑ j,
        pressureNewtonianDerivativePotential j (G j) x) *
          spatialLaplacian ψ x)) := by
    funext x
    ring
  rw [heq, integral_const_mul, hsum]

theorem pressureP7_distributional_pairing {η : Vec3 → ℝ}
    {f : ParabolicPoint → Vec3} {s : ℝ} {ψ : Vec3 → ℝ}
    (hInt : ∀ j, Integrable
      (fun y => η y * f (y, s) j) volume)
    (hSupp : ∀ j, HasCompactSupport
      (fun y => η y * f (y, s) j))
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    ∫ x, pressureP7 η f s x * spatialLaplacian ψ x =
      -∑ j, ∫ y, η y * f (y, s) j * CKN.spatialDeriv ψ j y := by
  let G : Fin 3 → Vec3 → ℝ := fun j y => η y * f (y, s) j
  have hsum := pressure_derivative_sum_distributional_pairing
    (fun j => hInt j) (fun j => hSupp j) hψ hψc
  change ∫ x, -(∑ j,
      pressureNewtonianDerivativePotential j (G j) x) *
        spatialLaplacian ψ x = _
  have heq : (fun x => -(∑ j,
      pressureNewtonianDerivativePotential j (G j) x) *
        spatialLaplacian ψ x) =
      (fun x => -((∑ j, pressureNewtonianDerivativePotential j (G j) x) *
        spatialLaplacian ψ x)) := by
    funext x
    ring
  rw [heq, MeasureTheory.integral_neg, hsum]

theorem pressureP3_distributional_pairing {η : Vec3 → ℝ}
    {u : ParabolicPoint → Vec3} {c : ℝ → Vec3} {s : ℝ}
    {ψ : Vec3 → ℝ}
    (hInt : ∀ i j, Integrable
      (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η i y) volume)
    (hSupp : ∀ i j, HasCompactSupport
      (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η i y))
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    ∫ x, pressureP3 η u c s x * spatialLaplacian ψ x =
      ∑ i, ∑ j, ∫ y, pressureUTensor u c (y, s) i j *
        spatialDeriv η i y * CKN.spatialDeriv ψ j y := by
  have hφ : ContDiff ℝ (⊤ : ℕ∞) (spatialLaplacian ψ) :=
    contDiff_spatialLaplacian_smooth hψ
  have hφc : HasCompactSupport (spatialLaplacian ψ) :=
    decomposition_laplacian_hasCompactSupport hψc
  have hterm (i j : Fin 3) : Integrable
      (fun x => pressureNewtonianDerivativePotential j
        (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η i y) x *
          spatialLaplacian ψ x) volume :=
    pressureNewtonianDerivativePotential_mul_smooth_integrable
      (hInt i j) (hSupp i j) hφ hφc
  have hpair (i j : Fin 3) :
      ∫ x, pressureNewtonianDerivativePotential j
        (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η i y) x *
          spatialLaplacian ψ x =
        ∫ y, pressureUTensor u c (y, s) i j * spatialDeriv η i y *
          CKN.spatialDeriv ψ j y :=
    pressureNewtonianDerivativePotential_distributional_pairing_smooth
      (hInt i j) (hSupp i j) hψ hψc
  change ∫ x, (∑ i, ∑ j, pressureNewtonianDerivativePotential j
      (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η i y) x) *
        spatialLaplacian ψ x = _
  calc
    _ = ∫ x, ∑ i, ∑ j, pressureNewtonianDerivativePotential j
        (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η i y) x *
          spatialLaplacian ψ x := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [Finset.sum_mul]
    _ = ∑ i, ∑ j, ∫ x, pressureNewtonianDerivativePotential j
        (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η i y) x *
          spatialLaplacian ψ x := by
      rw [integral_finsetSum (s := Finset.univ)]
      · apply Finset.sum_congr rfl
        intro i hi
        rw [integral_finsetSum (s := Finset.univ)]
        intro j hj
        exact hterm i j
      · intro i hi
        exact integrable_finsetSum (Finset.univ : Finset (Fin 3))
          (fun j hj => hterm i j)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact hpair i j

theorem pressureP4_distributional_pairing {η : Vec3 → ℝ}
    {u : ParabolicPoint → Vec3} {c : ℝ → Vec3} {s : ℝ}
    {ψ : Vec3 → ℝ}
    (hInt : ∀ i j, Integrable
      (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η j y) volume)
    (hSupp : ∀ i j, HasCompactSupport
      (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η j y))
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    ∫ x, pressureP4 η u c s x * spatialLaplacian ψ x =
      ∑ i, ∑ j, ∫ y, pressureUTensor u c (y, s) i j *
        spatialDeriv η j y * CKN.spatialDeriv ψ i y := by
  have hφ : ContDiff ℝ (⊤ : ℕ∞) (spatialLaplacian ψ) :=
    contDiff_spatialLaplacian_smooth hψ
  have hφc : HasCompactSupport (spatialLaplacian ψ) :=
    decomposition_laplacian_hasCompactSupport hψc
  have hterm (i j : Fin 3) : Integrable
      (fun x => pressureNewtonianDerivativePotential i
        (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η j y) x *
          spatialLaplacian ψ x) volume :=
    pressureNewtonianDerivativePotential_mul_smooth_integrable
      (hInt i j) (hSupp i j) hφ hφc
  have hpair (i j : Fin 3) :
      ∫ x, pressureNewtonianDerivativePotential i
        (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η j y) x *
          spatialLaplacian ψ x =
        ∫ y, pressureUTensor u c (y, s) i j * spatialDeriv η j y *
          CKN.spatialDeriv ψ i y :=
    pressureNewtonianDerivativePotential_distributional_pairing_smooth
      (hInt i j) (hSupp i j) hψ hψc
  change ∫ x, (∑ i, ∑ j, pressureNewtonianDerivativePotential i
      (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η j y) x) *
        spatialLaplacian ψ x = _
  calc
    _ = ∫ x, ∑ i, ∑ j, pressureNewtonianDerivativePotential i
        (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η j y) x *
          spatialLaplacian ψ x := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [Finset.sum_mul]
    _ = ∑ i, ∑ j, ∫ x, pressureNewtonianDerivativePotential i
        (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η j y) x *
          spatialLaplacian ψ x := by
      rw [integral_finsetSum (s := Finset.univ)]
      · apply Finset.sum_congr rfl
        intro i hi
        rw [integral_finsetSum (s := Finset.univ)]
        intro j hj
        exact hterm i j
      · intro i hi
        exact integrable_finsetSum (Finset.univ : Finset (Fin 3))
          (fun j hj => hterm i j)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact hpair i j

end CKN
