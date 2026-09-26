/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
module


public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section9.FreeBeamCharacteristic
public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Tactic

/-!
# Every solution of the free-beam ODE is a classical mode

The classification half of the free-beam eigenmode analysis: a real function with a full
fourth-order derivative chain satisfying `u'''' = β⁴ u` agrees on `[0,1]` with a member of the
four-parameter family `mode β a b c d` — together with its whole derivative chain.

The proof is the standard first-order reduction.  The four-tuple `(u, u', u'', u''')` solves a
linear system with Lipschitz right-hand side `(p₂, p₃, p₄, β⁴ p₁)`; the mode family realizes
every jet at `0` (this is where `β ≠ 0` enters); and `ODE_solution_unique` collapses the
difference.

Combined with `characteristic_eq_zero_of_freeBoundary`, this is exactly the input the
free-beam spectral realization needs: any eigenfunction of the fourth-derivative operator,
once bootstrapped to a classical solution with free boundary conditions, has `cos β cosh β = 1`
— so its eigenvalue `β⁴` exceeds `500` by the root exclusion already in the build.
-/

@[expose] public section

namespace TauCeti
namespace DavisKahan
namespace FreeBeam

open Set

/-- The first-order system vector field for the free-beam ODE `u'''' = β⁴ u`. -/
def modeVectorField (beta : ℝ) (p : ℝ × ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ × ℝ :=
  (p.2.1, p.2.2.1, p.2.2.2, beta ^ 4 * p.1)

/-- The free-beam vector field is Lipschitz with constant `max 1 β⁴`. -/
theorem lipschitzWith_modeVectorField (beta : ℝ) :
    LipschitzWith ⟨max 1 (beta ^ 4), le_trans zero_le_one (le_max_left _ _)⟩
      (modeVectorField beta) := by
  refine LipschitzWith.of_dist_le_mul fun p q => ?_
  have hKD : (max 1 (beta ^ 4)) * dist p q = max 1 (beta ^ 4) * dist p q := rfl
  have h1 : dist p.1 q.1 ≤ dist p q := by
    rw [Prod.dist_eq]
    exact le_max_left _ _
  have h2 : dist p.2.1 q.2.1 ≤ dist p q := by
    rw [Prod.dist_eq, Prod.dist_eq]
    exact le_max_of_le_right (le_max_left _ _)
  have h3 : dist p.2.2.1 q.2.2.1 ≤ dist p q := by
    rw [Prod.dist_eq, Prod.dist_eq, Prod.dist_eq]
    exact le_max_of_le_right (le_max_of_le_right (le_max_left _ _))
  have h4 : dist p.2.2.2 q.2.2.2 ≤ dist p q := by
    rw [Prod.dist_eq, Prod.dist_eq, Prod.dist_eq]
    exact le_max_of_le_right (le_max_of_le_right (le_max_right _ _))
  have hone : ∀ r : ℝ, r ≤ dist p q → r ≤ max 1 (beta ^ 4) * dist p q := by
    intro r hr
    calc r ≤ dist p q := hr
      _ = 1 * dist p q := (one_mul _).symm
      _ ≤ max 1 (beta ^ 4) * dist p q :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) dist_nonneg
  have hscaled : dist (beta ^ 4 * p.1) (beta ^ 4 * q.1)
      ≤ max 1 (beta ^ 4) * dist p q := by
    rw [Real.dist_eq, ← mul_sub, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ beta ^ 4)]
    calc beta ^ 4 * |p.1 - q.1| = beta ^ 4 * dist p.1 q.1 := by rw [Real.dist_eq]
      _ ≤ beta ^ 4 * dist p q := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ max 1 (beta ^ 4) * dist p q :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) dist_nonneg
  change dist (modeVectorField beta p) (modeVectorField beta q)
      ≤ max 1 (beta ^ 4) * dist p q
  unfold modeVectorField
  rw [Prod.dist_eq, Prod.dist_eq, Prod.dist_eq]
  exact max_le (hone _ h2) (max_le (hone _ h3) (max_le (hone _ h4) hscaled))

/-- The value of a mode at `0`. -/
theorem mode_eval_zero (beta a b c d : ℝ) : mode beta a b c d 0 = a + c := by
  simp [mode]

/-- The value of the mode derivative at `0`. -/
theorem modeD1_eval_zero (beta a b c d : ℝ) :
    modeD1 beta a b c d 0 = beta * (b + d) := by
  simp only [modeD1, mul_zero, Real.cos_zero, Real.sin_zero, Real.cosh_zero,
    Real.sinh_zero, mul_one]
  ring

/-- The value of the second mode derivative at `0`. -/
theorem modeD2_eval_zero (beta a b c d : ℝ) :
    modeD2 beta a b c d 0 = beta ^ 2 * (c - a) := by
  simp only [modeD2, mul_zero, Real.cos_zero, Real.sin_zero, Real.cosh_zero,
    Real.sinh_zero, mul_one]
  ring

/-- The value of the third mode derivative at `0`. -/
theorem modeD3_eval_zero (beta a b c d : ℝ) :
    modeD3 beta a b c d 0 = beta ^ 3 * (d - b) := by
  simp only [modeD3, mul_zero, Real.cos_zero, Real.sin_zero, Real.cosh_zero,
    Real.sinh_zero, mul_one]
  ring

/-- At nonzero frequency the mode family realizes every jet at `0`. -/
theorem exists_mode_jet (beta : ℝ) (hbeta : beta ≠ 0) (j0 j1 j2 j3 : ℝ) :
    ∃ a b c d : ℝ,
      mode beta a b c d 0 = j0 ∧ modeD1 beta a b c d 0 = j1 ∧
      modeD2 beta a b c d 0 = j2 ∧ modeD3 beta a b c d 0 = j3 := by
  refine ⟨(j0 - j2 / beta ^ 2) / 2, (j1 / beta - j3 / beta ^ 3) / 2,
    (j0 + j2 / beta ^ 2) / 2, (j1 / beta + j3 / beta ^ 3) / 2, ?_, ?_, ?_, ?_⟩
  · rw [mode_eval_zero]
    ring
  · rw [modeD1_eval_zero]
    field_simp
    ring
  · rw [modeD2_eval_zero]
    field_simp
    ring
  · rw [modeD3_eval_zero]
    field_simp
    ring

/-- **Uniqueness for the free-beam ODE with a full derivative chain**: two solutions of
`u'''' = β⁴ u` with the same jet at `0` agree on `[0,1]`, chain and all. -/
theorem eqOn_of_fourth_deriv_eq_of_jet_eq (beta : ℝ)
    {u u1 u2 u3 v v1 v2 v3 : ℝ → ℝ}
    (hdu : ∀ x, HasDerivAt u (u1 x) x) (hdu1 : ∀ x, HasDerivAt u1 (u2 x) x)
    (hdu2 : ∀ x, HasDerivAt u2 (u3 x) x)
    (hdu3 : ∀ x, HasDerivAt u3 (beta ^ 4 * u x) x)
    (hdv : ∀ x, HasDerivAt v (v1 x) x) (hdv1 : ∀ x, HasDerivAt v1 (v2 x) x)
    (hdv2 : ∀ x, HasDerivAt v2 (v3 x) x)
    (hdv3 : ∀ x, HasDerivAt v3 (beta ^ 4 * v x) x)
    (h0 : u 0 = v 0) (h1 : u1 0 = v1 0) (h2 : u2 0 = v2 0) (h3 : u3 0 = v3 0) :
    EqOn u v (Icc 0 1) ∧ EqOn u1 v1 (Icc 0 1) ∧
      EqOn u2 v2 (Icc 0 1) ∧ EqOn u3 v3 (Icc 0 1) := by
  set F : ℝ → ℝ × ℝ × ℝ × ℝ := fun x => (u x, u1 x, u2 x, u3 x) with hFdef
  set G : ℝ → ℝ × ℝ × ℝ × ℝ := fun x => (v x, v1 x, v2 x, v3 x) with hGdef
  have hF' : ∀ x, HasDerivAt F (modeVectorField beta (F x)) x := fun x =>
    (hdu x).prodMk ((hdu1 x).prodMk ((hdu2 x).prodMk (hdu3 x)))
  have hG' : ∀ x, HasDerivAt G (modeVectorField beta (G x)) x := fun x =>
    (hdv x).prodMk ((hdv1 x).prodMk ((hdv2 x).prodMk (hdv3 x)))
  have hFcont : ContinuousOn F (Icc 0 1) :=
    (Differentiable.continuous fun x => (hF' x).differentiableAt).continuousOn
  have hGcont : ContinuousOn G (Icc 0 1) :=
    (Differentiable.continuous fun x => (hG' x).differentiableAt).continuousOn
  have hFG : EqOn F G (Icc 0 1) := by
    refine ODE_solution_unique (v := fun _ => modeVectorField beta)
      (fun _ => lipschitzWith_modeVectorField beta) hFcont
      (fun x _ => (hF' x).hasDerivWithinAt) hGcont
      (fun x _ => (hG' x).hasDerivWithinAt) ?_
    simp only [hFdef, hGdef, h0, h1, h2, h3]
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩ <;>
    have := hFG hx
  · exact congrArg (fun p => p.1) this
  · exact congrArg (fun p => p.2.1) this
  · exact congrArg (fun p => p.2.2.1) this
  · exact congrArg (fun p => p.2.2.2) this

/-- **Every classical solution of the free-beam ODE is a mode on `[0,1]`**, together with its
entire derivative chain.  This is the classification half of the eigenmode analysis: it turns
an analytically bootstrapped eigenfunction into a member of the closed four-parameter family,
whose boundary behaviour is governed by the characteristic equation. -/
theorem exists_mode_eqOn_of_fourth_deriv (beta : ℝ) (hbeta : beta ≠ 0)
    {u u1 u2 u3 : ℝ → ℝ}
    (hdu : ∀ x, HasDerivAt u (u1 x) x) (hdu1 : ∀ x, HasDerivAt u1 (u2 x) x)
    (hdu2 : ∀ x, HasDerivAt u2 (u3 x) x)
    (hdu3 : ∀ x, HasDerivAt u3 (beta ^ 4 * u x) x) :
    ∃ a b c d : ℝ,
      EqOn u (mode beta a b c d) (Icc 0 1) ∧
      EqOn u1 (modeD1 beta a b c d) (Icc 0 1) ∧
      EqOn u2 (modeD2 beta a b c d) (Icc 0 1) ∧
      EqOn u3 (modeD3 beta a b c d) (Icc 0 1) := by
  obtain ⟨a, b, c, d, hj0, hj1, hj2, hj3⟩ :=
    exists_mode_jet beta hbeta (u 0) (u1 0) (u2 0) (u3 0)
  have hm3 : ∀ x, HasDerivAt (modeD3 beta a b c d) (beta ^ 4 * mode beta a b c d x) x :=
    fun x => hasDerivAt_modeD3 beta a b c d x
  exact ⟨a, b, c, d,
    eqOn_of_fourth_deriv_eq_of_jet_eq beta hdu hdu1 hdu2 hdu3
      (hasDerivAt_mode beta a b c d) (hasDerivAt_modeD1 beta a b c d)
      (hasDerivAt_modeD2 beta a b c d) hm3
      hj0.symm hj1.symm hj2.symm hj3.symm⟩

/-- Interval version of the uniqueness theorem: derivative chains within `[0,1]` suffice.
This is the form the eigenfunction bootstrap produces — at the two endpoints only one-sided
derivatives exist. -/
theorem eqOn_of_fourth_deriv_eq_of_jet_eq_within (beta : ℝ)
    {u u1 u2 u3 v v1 v2 v3 : ℝ → ℝ}
    (hdu : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt u (u1 x) (Icc 0 1) x)
    (hdu1 : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt u1 (u2 x) (Icc 0 1) x)
    (hdu2 : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt u2 (u3 x) (Icc 0 1) x)
    (hdu3 : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt u3 (beta ^ 4 * u x) (Icc 0 1) x)
    (hdv : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt v (v1 x) (Icc 0 1) x)
    (hdv1 : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt v1 (v2 x) (Icc 0 1) x)
    (hdv2 : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt v2 (v3 x) (Icc 0 1) x)
    (hdv3 : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt v3 (beta ^ 4 * v x) (Icc 0 1) x)
    (h0 : u 0 = v 0) (h1 : u1 0 = v1 0) (h2 : u2 0 = v2 0) (h3 : u3 0 = v3 0) :
    EqOn u v (Icc 0 1) ∧ EqOn u1 v1 (Icc 0 1) ∧
      EqOn u2 v2 (Icc 0 1) ∧ EqOn u3 v3 (Icc 0 1) := by
  set F : ℝ → ℝ × ℝ × ℝ × ℝ := fun x => (u x, u1 x, u2 x, u3 x) with hFdef
  set G : ℝ → ℝ × ℝ × ℝ × ℝ := fun x => (v x, v1 x, v2 x, v3 x) with hGdef
  have hF' : ∀ x ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt F (modeVectorField beta (F x)) (Icc 0 1) x := fun x hx =>
    ((hdu x hx).prodMk ((hdu1 x hx).prodMk ((hdu2 x hx).prodMk (hdu3 x hx))))
  have hG' : ∀ x ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt G (modeVectorField beta (G x)) (Icc 0 1) x := fun x hx =>
    ((hdv x hx).prodMk ((hdv1 x hx).prodMk ((hdv2 x hx).prodMk (hdv3 x hx))))
  have hFcont : ContinuousOn F (Icc 0 1) := fun x hx => (hF' x hx).continuousWithinAt
  have hGcont : ContinuousOn G (Icc 0 1) := fun x hx => (hG' x hx).continuousWithinAt
  have hFG : EqOn F G (Icc 0 1) := by
    refine ODE_solution_unique (v := fun _ => modeVectorField beta)
      (fun _ => lipschitzWith_modeVectorField beta) hFcont ?_ hGcont ?_ ?_
    · intro t ht
      exact (hF' t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem ht)
    · intro t ht
      exact (hG' t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem ht)
    · simp only [hFdef, hGdef, h0, h1, h2, h3]
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩ <;>
    have := hFG hx
  · exact congrArg (fun p => p.1) this
  · exact congrArg (fun p => p.2.1) this
  · exact congrArg (fun p => p.2.2.1) this
  · exact congrArg (fun p => p.2.2.2) this

/-- **Interval classification**: a function with a fourth-order derivative chain within
`[0,1]` solving `u'''' = β⁴ u` there is a mode on `[0,1]`, chain and all. -/
theorem exists_mode_eqOn_of_fourth_deriv_within (beta : ℝ) (hbeta : beta ≠ 0)
    {u u1 u2 u3 : ℝ → ℝ}
    (hdu : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt u (u1 x) (Icc 0 1) x)
    (hdu1 : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt u1 (u2 x) (Icc 0 1) x)
    (hdu2 : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt u2 (u3 x) (Icc 0 1) x)
    (hdu3 : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt u3 (beta ^ 4 * u x) (Icc 0 1) x) :
    ∃ a b c d : ℝ,
      EqOn u (mode beta a b c d) (Icc 0 1) ∧
      EqOn u1 (modeD1 beta a b c d) (Icc 0 1) ∧
      EqOn u2 (modeD2 beta a b c d) (Icc 0 1) ∧
      EqOn u3 (modeD3 beta a b c d) (Icc 0 1) := by
  obtain ⟨a, b, c, d, hj0, hj1, hj2, hj3⟩ :=
    exists_mode_jet beta hbeta (u 0) (u1 0) (u2 0) (u3 0)
  have hm3 : ∀ x ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (modeD3 beta a b c d) (beta ^ 4 * mode beta a b c d x)
        (Icc 0 1) x :=
    fun x _ => (hasDerivAt_modeD3 beta a b c d x).hasDerivWithinAt
  exact ⟨a, b, c, d,
    eqOn_of_fourth_deriv_eq_of_jet_eq_within beta hdu hdu1 hdu2 hdu3
      (fun x _ => (hasDerivAt_mode beta a b c d x).hasDerivWithinAt)
      (fun x _ => (hasDerivAt_modeD1 beta a b c d x).hasDerivWithinAt)
      (fun x _ => (hasDerivAt_modeD2 beta a b c d x).hasDerivWithinAt)
      hm3 hj0.symm hj1.symm hj2.symm hj3.symm⟩

end FreeBeam
end DavisKahan
end TauCeti
