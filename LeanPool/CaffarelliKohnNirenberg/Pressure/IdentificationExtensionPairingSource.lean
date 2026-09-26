/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.DecompositionPotentials

/-!
# Identification Extension Pairing Source

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
noncomputable section
namespace CKN

/-!
# Support and integrability of the eight cut-off pressure sources

The paper's pressure representation `prop:pressure-decomposition` writes the
localized pressure `η p` as a remainder `p₁` plus the eight source potentials
`p₂, …, p₈` (`eq:p1-bound`, `eq:p234-bound`, `eq:p56-bound`, `eq:p78-bound`).
Each of those potentials is a Newtonian or Newtonian-derivative potential of an
integrand built from the cut-off `η`, the velocity `u`, the pressure `p` and the
force `f`, evaluated on the time slice `t = s`.

This file records the bookkeeping needed to feed those potentials into the
potential calculus: that the spatial derivatives and the spatial Laplacian of a
cut-off are again supported in the cut-off's support (and hence compactly
supported), a general criterion turning an integrability hypothesis on a set
`K` into global integrability of a product with a smooth function supported in
`K`, and the resulting integrability and compact-support statements for the
eight source integrands.

The eight source integrands are, in the order used below,

* `η · p` (remainder/`p₁` slot, `eq:p1-bound`),
* `∂ᵢ∂ⱼη · Uᵢⱼ`, `Uᵢⱼ · ∂ᵢη`, `Uᵢⱼ · ∂ⱼη` (`p₂`, `p₃`, `p₄`, `eq:p234-bound`),
* `p · Δη`, `∂ⱼη · p` (`p₅`, `p₆`, `eq:p56-bound`),
* `η · fⱼ`, `∂ⱼη · fⱼ` (`p₇`, `p₈`, `eq:p78-bound`),

where `Uᵢⱼ = pressureUTensor u c (·, s) i j`.
-/

/-! ## Support of the spatial derivatives of a cut-off -/

/-- The first spatial derivative `∂ᵢη` of a cut-off is supported in the support
of `η` (`prop:pressure-decomposition`). -/
theorem pressureCutoff_tsupport_spatialDeriv_subset (η : Vec3 → ℝ) (i : Fin 3) :
    tsupport (spatialDeriv η i) ⊆ tsupport η :=
  tsupport_fderiv_apply_subset (𝕜 := ℝ) (f := η) (basisVec i)

/-- The mixed second derivative `∂ᵢ∂ⱼη` of a cut-off is supported in the support
of `η` (`prop:pressure-decomposition`). -/
theorem pressureCutoff_tsupport_mixedSecond_subset (η : Vec3 → ℝ) (i j : Fin 3) :
    tsupport (mixedSecond η i j) ⊆ tsupport η :=
  (pressureCutoff_tsupport_spatialDeriv_subset (spatialDeriv η j) i).trans
    (pressureCutoff_tsupport_spatialDeriv_subset η j)

/-- The spatial Laplacian `Δη` of a cut-off is supported in the support of `η`
(`prop:pressure-decomposition`). -/
theorem pressureCutoff_tsupport_spatialLaplacian_subset (η : Vec3 → ℝ) :
    tsupport (spatialLaplacian η) ⊆ tsupport η := by
  refine closure_minimal ?_ (isClosed_tsupport η)
  intro x hx
  by_contra hxt
  apply hx
  simp only [spatialLaplacian]
  refine Finset.sum_eq_zero fun i _ => ?_
  have hxi : x ∉ tsupport (spatialDeriv η i) :=
    fun h => hxt (pressureCutoff_tsupport_spatialDeriv_subset η i h)
  exact image_eq_zero_of_notMem_tsupport fun h =>
    hxi (pressureCutoff_tsupport_spatialDeriv_subset (spatialDeriv η i) i h)

/-- The first spatial derivative of a compactly supported cut-off is compactly
supported (`prop:pressure-decomposition`). -/
theorem pressureCutoff_hasCompactSupport_spatialDeriv {η : Vec3 → ℝ}
    (hηc : HasCompactSupport η) (i : Fin 3) : HasCompactSupport (spatialDeriv η i) :=
  hηc.fderiv_apply (𝕜 := ℝ) (basisVec i)

/-- The mixed second derivative of a compactly supported cut-off is compactly
supported (`prop:pressure-decomposition`). -/
theorem pressureCutoff_hasCompactSupport_mixedSecond {η : Vec3 → ℝ}
    (hηc : HasCompactSupport η) (i j : Fin 3) : HasCompactSupport (mixedSecond η i j) :=
  (hηc.fderiv_apply (𝕜 := ℝ) (basisVec j)).fderiv_apply (𝕜 := ℝ) (basisVec i)

/-- The spatial Laplacian of a compactly supported cut-off is compactly
supported (`prop:pressure-decomposition`). -/
theorem pressureCutoff_hasCompactSupport_spatialLaplacian {η : Vec3 → ℝ}
    (hηc : HasCompactSupport η) : HasCompactSupport (spatialLaplacian η) :=
  HasCompactSupport.of_support_subset_isCompact hηc.isCompact
    (subset_closure.trans (pressureCutoff_tsupport_spatialLaplacian_subset η))

/-! ## Integrability against a locally bounded source -/

/-- If `θ` is a continuous compactly supported function whose support lies in a
set `K`, and `g` is integrable on `K`, then `θ · g` is integrable on all of
`ℝ³` (`prop:pressure-decomposition`).  This is the criterion used to turn the
slice-integrability hypotheses on the eight sources into global integrability of
the potentials' integrands. -/
theorem pressureCutoff_integrable_mul_of_tsupport_subset {θ g : Vec3 → ℝ} {K : Set Vec3}
    (hθ : Continuous θ) (hθc : HasCompactSupport θ) (hθK : tsupport θ ⊆ K)
    (hg : IntegrableOn g K volume) :
    Integrable (fun y => θ y * g y) volume := by
  obtain ⟨C, hC⟩ := hθc.exists_bound_of_continuous hθ
  have h1 : Integrable (fun y => g y * θ y) (volume.restrict K) :=
    hg.mul_bdd hθ.aestronglyMeasurable (Eventually.of_forall fun y => hC y)
  have h2 : IntegrableOn (fun y => θ y * g y) K volume :=
    h1.congr (Eventually.of_forall fun y => mul_comm (g y) (θ y))
  refine h2.integrable_of_forall_notMem_eq_zero fun x hx => ?_
  rw [image_eq_zero_of_notMem_tsupport (f := θ) fun h => hx (hθK h), zero_mul]

/-! ## The eight cut-off pressure sources: integrability -/

/-- The localized pressure integrand `η · p(·, s)` is integrable
(`eq:p1-bound`). -/
theorem pressureCutoff_cutoffPressure_integrable {η : Vec3 → ℝ}
    {p : ParabolicPoint → ℝ} {s : ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hp : IntegrableOn (fun y : Vec3 => p (y, s)) (tsupport η) volume) :
    Integrable (fun y => η y * p (y, s)) volume :=
  pressureCutoff_integrable_mul_of_tsupport_subset hη.continuous hηc subset_rfl hp

/-- The `p₂` integrand `∂ᵢ∂ⱼη · Uᵢⱼ` is integrable (`eq:p234-bound`). -/
theorem pressureCutoff_hessianTensor_integrable {η : Vec3 → ℝ}
    {u : ParabolicPoint → Vec3} {c : ℝ → Vec3} {s : ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hU : ∀ i j : Fin 3,
      IntegrableOn (fun y : Vec3 => pressureUTensor u c (y, s) i j) (tsupport η) volume) :
    ∀ i j : Fin 3,
      Integrable (fun y => mixedSecond η i j y * pressureUTensor u c (y, s) i j) volume := by
  intro i j
  exact pressureCutoff_integrable_mul_of_tsupport_subset
    (contDiff_mixedSecond_smooth hη i j).continuous
    (pressureCutoff_hasCompactSupport_mixedSecond hηc i j)
    (pressureCutoff_tsupport_mixedSecond_subset η i j) (hU i j)

/-- The `p₃` integrand `Uᵢⱼ · ∂ᵢη` is integrable (`eq:p234-bound`). -/
theorem pressureCutoff_tensorGradientFirst_integrable {η : Vec3 → ℝ}
    {u : ParabolicPoint → Vec3} {c : ℝ → Vec3} {s : ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hU : ∀ i j : Fin 3,
      IntegrableOn (fun y : Vec3 => pressureUTensor u c (y, s) i j) (tsupport η) volume) :
    ∀ i j : Fin 3,
      Integrable (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η i y) volume := by
  intro i j
  simpa only [mul_comm] using
    pressureCutoff_integrable_mul_of_tsupport_subset
      (contDiff_spatialDeriv_smooth hη i).continuous
      (pressureCutoff_hasCompactSupport_spatialDeriv hηc i)
      (pressureCutoff_tsupport_spatialDeriv_subset η i) (hU i j)

/-- The `p₄` integrand `Uᵢⱼ · ∂ⱼη` is integrable (`eq:p234-bound`). -/
theorem pressureCutoff_tensorGradientSecond_integrable {η : Vec3 → ℝ}
    {u : ParabolicPoint → Vec3} {c : ℝ → Vec3} {s : ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hU : ∀ i j : Fin 3,
      IntegrableOn (fun y : Vec3 => pressureUTensor u c (y, s) i j) (tsupport η) volume) :
    ∀ i j : Fin 3,
      Integrable (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η j y) volume := by
  intro i j
  simpa only [mul_comm] using
    pressureCutoff_integrable_mul_of_tsupport_subset
      (contDiff_spatialDeriv_smooth hη j).continuous
      (pressureCutoff_hasCompactSupport_spatialDeriv hηc j)
      (pressureCutoff_tsupport_spatialDeriv_subset η j) (hU i j)

/-- The `p₅` integrand `p(·, s) · Δη` is integrable (`eq:p56-bound`). -/
theorem pressureCutoff_pressureLaplacian_integrable {η : Vec3 → ℝ}
    {p : ParabolicPoint → ℝ} {s : ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hp : IntegrableOn (fun y : Vec3 => p (y, s)) (tsupport η) volume) :
    Integrable (fun y => p (y, s) * spatialLaplacian η y) volume := by
  simpa only [mul_comm] using
    pressureCutoff_integrable_mul_of_tsupport_subset
      (contDiff_spatialLaplacian_smooth hη).continuous
      (pressureCutoff_hasCompactSupport_spatialLaplacian hηc)
      (pressureCutoff_tsupport_spatialLaplacian_subset η) hp

/-- The `p₆` integrand `∂ⱼη · p(·, s)` is integrable (`eq:p56-bound`). -/
theorem pressureCutoff_pressureGradient_integrable {η : Vec3 → ℝ}
    {p : ParabolicPoint → ℝ} {s : ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hp : IntegrableOn (fun y : Vec3 => p (y, s)) (tsupport η) volume) :
    ∀ j : Fin 3, Integrable (fun y => spatialDeriv η j y * p (y, s)) volume := by
  intro j
  exact pressureCutoff_integrable_mul_of_tsupport_subset
    (contDiff_spatialDeriv_smooth hη j).continuous
    (pressureCutoff_hasCompactSupport_spatialDeriv hηc j)
    (pressureCutoff_tsupport_spatialDeriv_subset η j) hp

/-- The `p₇` integrand `η · fⱼ(·, s)` is integrable (`eq:p78-bound`). -/
theorem pressureCutoff_forceCutoff_integrable {η : Vec3 → ℝ}
    {f : ParabolicPoint → Vec3} {s : ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hf : ∀ j : Fin 3,
      IntegrableOn (fun y : Vec3 => f (y, s) j) (tsupport η) volume) :
    ∀ j : Fin 3, Integrable (fun y => η y * f (y, s) j) volume := by
  intro j
  exact pressureCutoff_integrable_mul_of_tsupport_subset
    hη.continuous hηc subset_rfl (hf j)

/-- The `p₈` integrand `∂ⱼη · fⱼ(·, s)` is integrable (`eq:p78-bound`). -/
theorem pressureCutoff_forceGradient_integrable {η : Vec3 → ℝ}
    {f : ParabolicPoint → Vec3} {s : ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hf : ∀ j : Fin 3,
      IntegrableOn (fun y : Vec3 => f (y, s) j) (tsupport η) volume) :
    ∀ j : Fin 3, Integrable (fun y => spatialDeriv η j y * f (y, s) j) volume := by
  intro j
  exact pressureCutoff_integrable_mul_of_tsupport_subset
    (contDiff_spatialDeriv_smooth hη j).continuous
    (pressureCutoff_hasCompactSupport_spatialDeriv hηc j)
    (pressureCutoff_tsupport_spatialDeriv_subset η j) (hf j)

/-! ## The eight cut-off pressure sources: compact support -/

/-- The `p₂` integrand `∂ᵢ∂ⱼη · Uᵢⱼ` has compact support (`eq:p234-bound`). -/
theorem pressureCutoff_hessianTensor_hasCompactSupport {η : Vec3 → ℝ}
    {u : ParabolicPoint → Vec3} {c : ℝ → Vec3} {s : ℝ}
    (hηc : HasCompactSupport η) :
    ∀ i j : Fin 3,
      HasCompactSupport (fun y => mixedSecond η i j y * pressureUTensor u c (y, s) i j) :=
  fun i _ => (pressureCutoff_hasCompactSupport_mixedSecond hηc i _).mul_right

/-- The `p₃` integrand `Uᵢⱼ · ∂ᵢη` has compact support (`eq:p234-bound`). -/
theorem pressureCutoff_tensorGradientFirst_hasCompactSupport {η : Vec3 → ℝ}
    {u : ParabolicPoint → Vec3} {c : ℝ → Vec3} {s : ℝ}
    (hηc : HasCompactSupport η) :
    ∀ i j : Fin 3,
      HasCompactSupport (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η i y) :=
  fun i _ => (pressureCutoff_hasCompactSupport_spatialDeriv hηc i).mul_left

/-- The `p₄` integrand `Uᵢⱼ · ∂ⱼη` has compact support (`eq:p234-bound`). -/
theorem pressureCutoff_tensorGradientSecond_hasCompactSupport {η : Vec3 → ℝ}
    {u : ParabolicPoint → Vec3} {c : ℝ → Vec3} {s : ℝ}
    (hηc : HasCompactSupport η) :
    ∀ i j : Fin 3,
      HasCompactSupport (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η j y) :=
  fun _ j => (pressureCutoff_hasCompactSupport_spatialDeriv hηc j).mul_left

/-- The `p₅` integrand `p(·, s) · Δη` has compact support (`eq:p56-bound`). -/
theorem pressureCutoff_pressureLaplacian_hasCompactSupport {η : Vec3 → ℝ}
    {p : ParabolicPoint → ℝ} {s : ℝ} (hηc : HasCompactSupport η) :
    HasCompactSupport (fun y => p (y, s) * spatialLaplacian η y) :=
  (pressureCutoff_hasCompactSupport_spatialLaplacian hηc).mul_left

/-- The `p₆` integrand `∂ⱼη · p(·, s)` has compact support (`eq:p56-bound`). -/
theorem pressureCutoff_pressureGradient_hasCompactSupport {η : Vec3 → ℝ}
    {p : ParabolicPoint → ℝ} {s : ℝ} (hηc : HasCompactSupport η) :
    ∀ j : Fin 3, HasCompactSupport (fun y => spatialDeriv η j y * p (y, s)) :=
  fun j => (pressureCutoff_hasCompactSupport_spatialDeriv hηc j).mul_right

/-- The `p₇` integrand `η · fⱼ(·, s)` has compact support (`eq:p78-bound`). -/
theorem pressureCutoff_forceCutoff_hasCompactSupport {η : Vec3 → ℝ}
    {f : ParabolicPoint → Vec3} {s : ℝ} (hηc : HasCompactSupport η) :
    ∀ j : Fin 3, HasCompactSupport (fun y => η y * f (y, s) j) :=
  fun _ => hηc.mul_right

/-- The `p₈` integrand `∂ⱼη · fⱼ(·, s)` has compact support (`eq:p78-bound`). -/
theorem pressureCutoff_forceGradient_hasCompactSupport {η : Vec3 → ℝ}
    {f : ParabolicPoint → Vec3} {s : ℝ} (hηc : HasCompactSupport η) :
    ∀ j : Fin 3, HasCompactSupport (fun y => spatialDeriv η j y * f (y, s) j) :=
  fun j => (pressureCutoff_hasCompactSupport_spatialDeriv hηc j).mul_right

end CKN
end
