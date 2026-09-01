/-
Copyright (c) 2026 BochaoKong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BochaoKong
-/

import LeanPool.LocalComplexGeometry.Germs.Coordinates
import Mathlib.Analysis.Analytic.Order
import Mathlib.Order.Filter.Finite

/-!
# The local analytic Nullstellensatz in one complex variable

The proof uses the isolated-zero factorization of a nonzero one-variable
analytic germ.  A generator which is nonzero at the origin is a unit.  If all
generators vanish at the origin but one is a nonzero germ, its finite order of
vanishing bounds a power of every germ vanishing at the origin.  Finally, if
all generators are zero germs, the common-zero hypothesis forces the target
to be the zero germ.
-/

open Filter
open scoped BigOperators Topology


namespace LocalComplexGeometry

noncomputable section

/-! ## The standard coordinate on `ComplexEuclidean 1` -/

/-- Evaluation at the unique coordinate, as a complex-linear equivalence. -/
def oneCoordinateLinearEquiv : ComplexEuclidean 1 ≃ₗ[ℂ] ℂ where
  toFun x := x 0
  invFun z := fun _ ↦ z
  left_inv x := by
    funext i
    simp [Fin.eq_zero i]
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The continuous complex-linear identification `ℂ¹ ≃ ℂ`. -/
def oneCoordinateEquiv : ComplexEuclidean 1 ≃L[ℂ] ℂ :=
  oneCoordinateLinearEquiv.toContinuousLinearEquiv

@[simp]
theorem oneCoordinateEquiv_apply (x : ComplexEuclidean 1) :
    oneCoordinateEquiv x = x 0 :=
  rfl

@[simp]
theorem oneCoordinateEquiv_symm_apply (z : ℂ) :
    oneCoordinateEquiv.symm z = fun _ ↦ z :=
  rfl

/-! ## A principal one-variable power certificate -/

/--
If `f` is a nonzero one-variable analytic germ and both `f` and `g` vanish at
the origin, then a positive power of `g` is an analytic multiple of `f`.

The exponent produced by the proof is the order of vanishing of `f`.
-/
theorem exists_power_eq_mul_of_analyticAt_oneVariable
    {f g : ComplexEuclidean 1 → ℂ}
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0)
    (hf0 : f 0 = 0) (hg0 : g 0 = 0)
    (hf_ne : ¬ f =ᶠ[𝓝 (0 : ComplexEuclidean 1)] (fun _ ↦ 0)) :
    ∃ N : ℕ, 0 < N ∧
      ∃ h : ComplexEuclidean 1 → ℂ,
        AnalyticAt ℂ h 0 ∧
        (fun x ↦ g x ^ N) =ᶠ[𝓝 0] fun x ↦ h x * f x := by
  let F : ℂ → ℂ := f ∘ oneCoordinateEquiv.symm
  let G : ℂ → ℂ := g ∘ oneCoordinateEquiv.symm
  have hF : AnalyticAt ℂ F 0 := by
    have hf' : AnalyticAt ℂ f (oneCoordinateEquiv.symm 0) := by
      rw [map_zero]
      exact hf
    simpa [F] using hf'.compContinuousLinearMap
      (u := oneCoordinateEquiv.symm.toContinuousLinearMap) (x := 0)
  have hG : AnalyticAt ℂ G 0 := by
    have hg' : AnalyticAt ℂ g (oneCoordinateEquiv.symm 0) := by
      rw [map_zero]
      exact hg
    simpa [G] using hg'.compContinuousLinearMap
      (u := oneCoordinateEquiv.symm.toContinuousLinearMap) (x := 0)
  have hF0 : F 0 = 0 := by
    change f (oneCoordinateEquiv.symm 0) = 0
    rw [map_zero]
    exact hf0
  have hG0 : G 0 = 0 := by
    change g (oneCoordinateEquiv.symm 0) = 0
    rw [map_zero]
    exact hg0
  have hF_ne : ¬ F =ᶠ[𝓝 (0 : ℂ)] (fun _ ↦ 0) := by
    intro hzero
    have ht : Tendsto oneCoordinateEquiv
        (𝓝 (0 : ComplexEuclidean 1)) (𝓝 (0 : ℂ)) := by
      have ht' : Tendsto oneCoordinateEquiv
          (𝓝 (0 : ComplexEuclidean 1))
          (𝓝 (oneCoordinateEquiv (0 : ComplexEuclidean 1))) :=
        oneCoordinateEquiv.continuous.continuousAt
      rw [map_zero] at ht'
      exact ht'
    apply hf_ne
    filter_upwards [hzero.comp_tendsto ht] with x hx
    change f (oneCoordinateEquiv.symm (oneCoordinateEquiv x)) = 0 at hx
    rw [oneCoordinateEquiv.symm_apply_apply] at hx
    exact hx
  obtain ⟨m, u, hu, hu0, hfactor⟩ :=
    hF.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hF_ne
  have hm : 0 < m := by
    by_contra hm
    have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
    have hfactor0 := hfactor.self_of_nhds
    have hFu : F 0 = u 0 := by
      simpa [hm0] using hfactor0
    exact hu0 (by rw [← hFu, hF0])
  obtain ⟨p, hp⟩ := hG
  let q : ℂ → ℂ := dslope G 0
  have hq : AnalyticAt ℂ q 0 :=
    ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩
  have hGfactor : ∀ z : ℂ, G z = z * q z := by
    intro z
    simpa [q] using (sub_smul_dslope_of_zero hG0 z).symm
  let H : ℂ → ℂ := fun z ↦ q z ^ m * (u z)⁻¹
  have hH : AnalyticAt ℂ H 0 :=
    (hq.pow m).mul (hu.inv hu0)
  have hu_ne : ∀ᶠ z in 𝓝 (0 : ℂ), u z ≠ 0 :=
    hu.continuousAt.eventually_ne hu0
  have hscalar : (fun z ↦ G z ^ m) =ᶠ[𝓝 (0 : ℂ)]
      fun z ↦ H z * F z := by
    filter_upwards [hfactor, hu_ne] with z hFz huz
    rw [hGfactor z, hFz]
    change (z * q z) ^ m =
      (q z ^ m * (u z)⁻¹) * ((z - 0) ^ m * u z)
    simp only [sub_zero, mul_pow]
    field_simp
  let h : ComplexEuclidean 1 → ℂ := H ∘ oneCoordinateEquiv
  have hh : AnalyticAt ℂ h 0 := by
    have hH' : AnalyticAt ℂ H (oneCoordinateEquiv 0) := by
      simpa using hH
    simpa [h] using hH'.compContinuousLinearMap
      (u := oneCoordinateEquiv.toContinuousLinearMap) (x := 0)
  have ht : Tendsto oneCoordinateEquiv
      (𝓝 (0 : ComplexEuclidean 1)) (𝓝 (0 : ℂ)) := by
    have ht' : Tendsto oneCoordinateEquiv
        (𝓝 (0 : ComplexEuclidean 1))
        (𝓝 (oneCoordinateEquiv (0 : ComplexEuclidean 1))) :=
      oneCoordinateEquiv.continuous.continuousAt
    rw [map_zero] at ht'
    exact ht'
  have hcertificate : (fun x ↦ g x ^ m) =ᶠ[𝓝 0]
      fun x ↦ h x * f x := by
    filter_upwards [hscalar.comp_tendsto ht] with x hx
    change g (oneCoordinateEquiv.symm (oneCoordinateEquiv x)) ^ m =
      H (oneCoordinateEquiv x) *
        f (oneCoordinateEquiv.symm (oneCoordinateEquiv x)) at hx
    change g x ^ m = H (oneCoordinateEquiv x) * f x
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hx
  exact ⟨m, hm, h, hh, hcertificate⟩

/-! ## The finite-family Nullstellensatz -/

/--
The audited finite-family local analytic Nullstellensatz in one complex
variable.  The hypothesis is the genuine eventual common-zero implication,
and the conclusion is a positive-power certificate with analytic
coefficients.
-/
theorem localAnalyticNullstellensatz_oneVariable
    {s : ℕ}
    {f : Fin s → ComplexEuclidean 1 → ℂ}
    {g : ComplexEuclidean 1 → ℂ}
    (hf : ∀ i, AnalyticAt ℂ (f i) 0)
    (hg : AnalyticAt ℂ g 0)
    (hzero : ∀ᶠ x in 𝓝 (0 : ComplexEuclidean 1),
      (∀ i, f i x = 0) → g x = 0) :
    ∃ N : ℕ, 0 < N ∧
      ∃ h : Fin s → ComplexEuclidean 1 → ℂ,
        (∀ i, AnalyticAt ℂ (h i) 0) ∧
        (fun x ↦ g x ^ N) =ᶠ[𝓝 0]
          fun x ↦ ∑ i, h i x * f i x := by
  classical
  by_cases hunit : ∃ i, f i 0 ≠ 0
  · obtain ⟨j, hj⟩ := hunit
    let q : ComplexEuclidean 1 → ℂ := fun x ↦ g x * (f j x)⁻¹
    have hq : AnalyticAt ℂ q 0 :=
      hg.mul ((hf j).inv hj)
    let h : Fin s → ComplexEuclidean 1 → ℂ :=
      fun i x ↦ if i = j then q x else 0
    have hh : ∀ i, AnalyticAt ℂ (h i) 0 := by
      intro i
      by_cases hij : i = j
      · simpa [h, hij] using hq
      · simpa [h, hij] using (analyticAt_const :
          AnalyticAt ℂ (fun _ : ComplexEuclidean 1 ↦ (0 : ℂ)) 0)
    have hj_ne : ∀ᶠ x in 𝓝 (0 : ComplexEuclidean 1), f j x ≠ 0 :=
      (hf j).continuousAt.eventually_ne hj
    refine ⟨1, Nat.zero_lt_succ 0, h, hh, ?_⟩
    filter_upwards [hj_ne] with x hx
    have hsum : ∑ i, h i x * f i x = q x * f j x := by
      calc
        ∑ i, h i x * f i x = h j x * f j x := by
          apply Fintype.sum_eq_single j
          intro i hij
          simp [h, hij]
        _ = q x * f j x := by simp [h]
    rw [hsum]
    simp [q, hx]
  · have hvanish : ∀ i, f i 0 = 0 := by
      simpa only [not_exists, not_ne_iff] using hunit
    by_cases hall : ∀ i, (f i) =ᶠ[𝓝 (0 : ComplexEuclidean 1)] (fun _ ↦ 0)
    · have hall_eventually : ∀ᶠ x in 𝓝 (0 : ComplexEuclidean 1),
          ∀ i, f i x = 0 :=
        Filter.eventually_all.mpr hall
      have hgzero : g =ᶠ[𝓝 (0 : ComplexEuclidean 1)] (fun _ ↦ 0) := by
        filter_upwards [hzero, hall_eventually] with x hx hallx
        exact hx hallx
      refine ⟨1, Nat.zero_lt_succ 0, fun _ _ ↦ 0, ?_, ?_⟩
      · intro i
        exact analyticAt_const
      · filter_upwards [hgzero] with x hx
        simp [hx]
    · push Not at hall
      obtain ⟨j, hj⟩ := hall
      have hzero0 : (∀ i, f i 0 = 0) → g 0 = 0 :=
        Filter.Eventually.self_of_nhds hzero
      have hg0 : g 0 = 0 := hzero0 hvanish
      obtain ⟨N, hN, q, hq, hqcert⟩ :=
        exists_power_eq_mul_of_analyticAt_oneVariable
          (hf j) hg (hvanish j) hg0 hj
      let h : Fin s → ComplexEuclidean 1 → ℂ :=
        fun i x ↦ if i = j then q x else 0
      have hh : ∀ i, AnalyticAt ℂ (h i) 0 := by
        intro i
        by_cases hij : i = j
        · simpa [h, hij] using hq
        · simpa [h, hij] using (analyticAt_const :
            AnalyticAt ℂ (fun _ : ComplexEuclidean 1 ↦ (0 : ℂ)) 0)
      refine ⟨N, hN, h, hh, ?_⟩
      filter_upwards [hqcert] with x hx
      have hsum : ∑ i, h i x * f i x = q x * f j x := by
        calc
          ∑ i, h i x * f i x = h j x * f j x := by
            apply Fintype.sum_eq_single j
            intro i hij
            simp [h, hij]
          _ = q x * f j x := by simp [h]
      rw [hsum]
      exact hx

end

end LocalComplexGeometry
