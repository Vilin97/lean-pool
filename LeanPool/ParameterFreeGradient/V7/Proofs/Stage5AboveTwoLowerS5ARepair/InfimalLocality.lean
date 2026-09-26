/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/
module


public import LeanPool.ParameterFreeGradient.V7.Proofs.Stage5AboveTwoLower.LocalityBridge
public import LeanPool.ParameterFreeGradient.O3.Stage2RouteC

/-!
Stable interior minimizing displacements imply locality of the infimal-convolution value.
-/

@[expose] public section

namespace V7.Stage5AboveTwoLower.S5ARepair

private lemma lpNorm_add_le {p : ℝ} (hp : 1 ≤ p) (u v : Point d) :
    lpNorm p (u + v) ≤ lpNorm p u + lpNorm p v := by
  let e : ENNReal := ENNReal.ofReal p
  let _ : Fact (1 ≤ e) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  have h := norm_add_le (WithLp.toLp e u : PiLp e (fun _ : Fin d ↦ ℝ))
    (WithLp.toLp e v)
  change O3.lpNorm p (u + v) ≤ O3.lpNorm p u + O3.lpNorm p v
  rw [O3.Stage2RouteC.lpNorm_eq_piLpNorm hp,
    O3.Stage2RouteC.lpNorm_eq_piLpNorm hp,
    O3.Stage2RouteC.lpNorm_eq_piLpNorm hp]
  simpa using h

private lemma continuous_lpNorm {p : ℝ} (hp : 1 ≤ p) :
    Continuous (fun z : Point d ↦ lpNorm p z) := by
  let e : ENNReal := ENNReal.ofReal p
  let _ : Fact (1 ≤ e) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  have hto : Continuous
      (fun z : Point d ↦ (WithLp.toLp e z : PiLp e (fun _ : Fin d ↦ ℝ))) :=
    PiLp.continuous_toLp e (fun _ : Fin d ↦ ℝ)
  have hn := continuous_norm.comp hto
  apply hn.congr
  intro z
  exact (O3.Stage2RouteC.lpNorm_eq_piLpNorm hp z).symm

lemma eventually_lpNorm_sub_lt {p eta : ℝ} (hp : 1 ≤ p)
    (heta : 0 < eta) (x : Point d) :
    ∀ᶠ y in nhds x, lpNorm p (y - x) < eta := by
  have hc : ContinuousAt (fun y : Point d ↦ lpNorm p (y - x)) x :=
    (continuous_lpNorm hp).continuousAt.comp'
      (continuousAt_id.sub continuousAt_const)
  have hzero : lpNorm p (x - x) = 0 := by
    rw [sub_self]
    change O3.lpNorm p (0 : Point d) = 0
    exact O3.lpNorm_zero (by linarith : 0 < p)
  have hmem : Set.Iio eta ∈ nhds (lpNorm p (x - x)) := by
    rw [hzero]
    exact Iio_mem_nhds heta
  exact hc hmem

/-- The objective value plus the rescaled kernel penalty at a displacement. -/
noncomputable def smoothingCost (kernel : SmoothingKernelData p d)
    (chi : ℝ) (ell : Point d → ℝ) (x v : Point d) : ℝ :=
  ell (x + v) + chi * kernel.phi ((1 / chi) • v)

/-- The displacement globally minimizes the infimal-convolution cost. -/
def IsInfimalMinimizer (kernel : SmoothingKernelData p d)
    (chi : ℝ) (ell : Point d → ℝ) (x v : Point d) : Prop :=
  ∀ w, smoothingCost kernel chi ell x v ≤ smoothingCost kernel chi ell x w

lemma localSmoothingValue_eq_of_minimizer
    (kernel : SmoothingKernelData p d) (chi : ℝ) (ell : Point d → ℝ)
    (x v : Point d) (hv : IsInfimalMinimizer kernel chi ell x v) :
    localSmoothingValue kernel chi ell x = smoothingCost kernel chi ell x v := by
  unfold localSmoothingValue
  let values : Set ℝ := {a : ℝ | ∃ w : Point d,
    a = ell (x + w) + chi * kernel.phi ((1 / chi) • w)}
  have hleast : IsLeast values (smoothingCost kernel chi ell x v) := by
    constructor
    · exact ⟨v, rfl⟩
    · intro a ha
      rcases ha with ⟨w, rfl⟩
      exact hv w
  change sInf values = smoothingCost kernel chi ell x v
  exact hleast.csInf_eq

/-- The exact logical core of value locality. Once minimizers at nearby
centres stay inside the original closed smoothing ball, equality of the two
objectives on that ball forces equality of the two infimal values. -/
lemma localSmoothingValue_eventually_eq_of_stable_minimizers
    (kernel : SmoothingKernelData p d) {chi : ℝ} {ell₁ ell₂ : Point d → ℝ}
    {x : Point d}
    (heq : ∀ u, lpNorm p u ≤ chi → ell₁ (x + u) = ell₂ (x + u))
    (hstable : ∀ᶠ y in nhds x, ∃ v₁ v₂ : Point d,
      IsInfimalMinimizer kernel chi ell₁ y v₁ ∧
      IsInfimalMinimizer kernel chi ell₂ y v₂ ∧
      lpNorm p (y + v₁ - x) ≤ chi ∧
      lpNorm p (y + v₂ - x) ≤ chi) :
    localSmoothingValue kernel chi ell₁ =ᶠ[nhds x]
      localSmoothingValue kernel chi ell₂ := by
  filter_upwards [hstable] with y hy
  rcases hy with ⟨v₁, v₂, hmin₁, hmin₂, hv₁, hv₂⟩
  have heq₁ : ell₁ (y + v₁) = ell₂ (y + v₁) := by
    convert heq (y + v₁ - x) hv₁ using 1 <;> abel
  have heq₂ : ell₁ (y + v₂) = ell₂ (y + v₂) := by
    convert heq (y + v₂ - x) hv₂ using 1 <;> abel
  have hcost₁ : smoothingCost kernel chi ell₁ y v₁ =
      smoothingCost kernel chi ell₂ y v₁ := by
    unfold smoothingCost
    rw [heq₁]
  have hcost₂ : smoothingCost kernel chi ell₁ y v₂ =
      smoothingCost kernel chi ell₂ y v₂ := by
    unfold smoothingCost
    rw [heq₂]
  rw [localSmoothingValue_eq_of_minimizer kernel chi ell₁ y v₁ hmin₁,
    localSmoothingValue_eq_of_minimizer kernel chi ell₂ y v₂ hmin₂]
  apply le_antisymm
  · calc
      smoothingCost kernel chi ell₁ y v₁ ≤
          smoothingCost kernel chi ell₁ y v₂ := hmin₁ v₂
      _ = smoothingCost kernel chi ell₂ y v₂ := hcost₂
  · calc
      smoothingCost kernel chi ell₂ y v₂ ≤
          smoothingCost kernel chi ell₂ y v₁ := hmin₂ v₁
      _ = smoothingCost kernel chi ell₁ y v₁ := hcost₁.symm

/-- A uniform interior margin is sufficient for the nearby-centre stability
hypothesis above. This isolates the remaining compactness task: produce one
positive `eta` that works for every minimizer in a neighbourhood. -/
lemma stable_minimizers_of_uniform_interior_margin
    (kernel : SmoothingKernelData p d) {chi eta : ℝ}
    {ell₁ ell₂ : Point d → ℝ} {x : Point d}
    (hp : 1 ≤ p) (_heta : 0 < eta)
    (hnear : ∀ᶠ y in nhds x, lpNorm p (y - x) < eta)
    (hmargin : ∀ᶠ y in nhds x, ∃ v₁ v₂ : Point d,
      IsInfimalMinimizer kernel chi ell₁ y v₁ ∧
      IsInfimalMinimizer kernel chi ell₂ y v₂ ∧
      lpNorm p v₁ ≤ chi - eta ∧ lpNorm p v₂ ≤ chi - eta) :
    ∀ᶠ y in nhds x, ∃ v₁ v₂ : Point d,
      IsInfimalMinimizer kernel chi ell₁ y v₁ ∧
      IsInfimalMinimizer kernel chi ell₂ y v₂ ∧
      lpNorm p (y + v₁ - x) ≤ chi ∧
      lpNorm p (y + v₂ - x) ≤ chi := by
  filter_upwards [hnear, hmargin] with y hy hmins
  rcases hmins with ⟨v₁, v₂, hmin₁, hmin₂, hv₁, hv₂⟩
  refine ⟨v₁, v₂, hmin₁, hmin₂, ?_, ?_⟩
  · have htri := lpNorm_add_le hp (y - x) v₁
    have hid : y + v₁ - x = (y - x) + v₁ := by abel
    rw [hid]
    linarith
  · have htri := lpNorm_add_le hp (y - x) v₂
    have hid : y + v₂ - x = (y - x) + v₂ := by abel
    rw [hid]
    linarith

end V7.Stage5AboveTwoLower.S5ARepair
