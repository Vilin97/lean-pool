/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.H1

/-! # Potential Solenoidal -/

@[expose] public section

namespace Homogenization

def IsPotentialOn {d : ℕ} (U : Set (Vec d)) (f : Vec d → Vec d) : Prop :=
  ∃ u : H1Function U, u.grad = f

def IsPotentialZeroTraceOn {d : ℕ} (U : Set (Vec d)) (f : Vec d → Vec d) : Prop :=
  ∃ u : H10Function U, u.toH1Function.grad = f

noncomputable def IsSolenoidalOn {d : ℕ} (U : Set (Vec d)) (g : Vec d → Vec d) : Prop :=
  ∀ φ : H10Function U,
    ∫ x in U, vecDot (g x) (φ.toH1Function.grad x) ∂MeasureTheory.volume = 0

noncomputable def IsSolenoidalZeroNormalTraceOn {d : ℕ} (U : Set (Vec d))
    (g : Vec d → Vec d) : Prop :=
  ∀ φ : H1Function U,
    ∫ x in U, vecDot (g x) (φ.grad x) ∂MeasureTheory.volume = 0

theorem H1Function.isPotentialOn {d : ℕ} {U : Set (Vec d)} (u : H1Function U) :
    IsPotentialOn U u.grad :=
  ⟨u, rfl⟩

theorem H10Function.isPotentialZeroTraceOn {d : ℕ} {U : Set (Vec d)} (u : H10Function U) :
    IsPotentialZeroTraceOn U u.toH1Function.grad :=
  ⟨u, rfl⟩

/-- The zero-trace potential predicate is insensitive to changing the vector
field on a null set. This is the representative bridge needed when moving from
closed `L²` subspaces back to witness-based Sobolev predicates. -/
theorem IsPotentialZeroTraceOn.congr_ae {d : ℕ} {U : Set (Vec d)}
    {f g : Vec d → Vec d}
    (hfg : f =ᵐ[MeasureTheory.volume.restrict U] g)
    (hf : IsPotentialZeroTraceOn U f) :
    IsPotentialZeroTraceOn U g := by
  rcases hf with ⟨u, hgrad⟩
  have hug : u.toH1Function.grad =ᵐ[MeasureTheory.volume.restrict U] g := by
    simpa [hgrad] using hfg
  let vH1 : H1Function U :=
    { toFun := u.toH1Function.toFun
      grad := g
      memL2 := u.toH1Function.memL2
      gradMemL2 := by
        intro i
        have hcoord :
            (fun x => u.toH1Function.grad x i) =ᵐ[MeasureTheory.volume.restrict U]
              fun x => g x i :=
          hug.mono fun x hx => congrArg (fun y : Vec d => y i) hx
        exact (u.toH1Function.gradMemL2 i).ae_eq hcoord
      hasWeakGradient := by
        intro i φ hφ hφ_supp hφ_sub
        have hcoord :
            (fun x => u.toH1Function.grad x i) =ᵐ[MeasureTheory.volume.restrict U]
              fun x => g x i :=
          hug.mono fun x hx => congrArg (fun y : Vec d => y i) hx
        have hright :
            ∫ x in U, g x i * φ x ∂MeasureTheory.volume =
              ∫ x in U, u.toH1Function.grad x i * φ x ∂MeasureTheory.volume := by
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards [hcoord] with x hx
          rw [← hx]
        calc
          ∫ x in U, u.toH1Function.toFun x * (fderiv ℝ φ x) (basisVec i)
              ∂MeasureTheory.volume
              = -∫ x in U, u.toH1Function.grad x i * φ x ∂MeasureTheory.volume := by
                exact u.toH1Function.hasWeakGradient i φ hφ hφ_supp hφ_sub
          _ = -∫ x in U, g x i * φ x ∂MeasureTheory.volume := by rw [hright] }
  let v : H10Function U :=
    { toH1Function := vH1
      approx := u.approx
      approx_smooth := u.approx_smooth
      approx_hasCompactSupport := u.approx_hasCompactSupport
      approx_support_subset := u.approx_support_subset
      tendsto_approx := by
        simpa [vH1] using u.tendsto_approx
      tendsto_approx_grad := by
        intro i
        have hcoord :
            (fun x => u.toH1Function.grad x i) =ᵐ[MeasureTheory.volume.restrict U]
              fun x => g x i :=
          hug.mono fun x hx => congrArg (fun y : Vec d => y i) hx
        have hnorm :
            (fun n =>
              MeasureTheory.eLpNorm
                (fun x => (fderiv ℝ (u.approx n) x) (basisVec i) - g x i) 2
                (MeasureTheory.volume.restrict U)) =
            fun n =>
              MeasureTheory.eLpNorm
                (fun x =>
                  (fderiv ℝ (u.approx n) x) (basisVec i) - u.toH1Function.grad x i) 2
                (MeasureTheory.volume.restrict U) := by
          funext n
          exact MeasureTheory.eLpNorm_congr_ae <|
            hcoord.mono fun x hx => by
              change
                (fderiv ℝ (u.approx n) x) (basisVec i) - g x i =
                  (fderiv ℝ (u.approx n) x) (basisVec i) - u.toH1Function.grad x i
              have hx' : u.toH1Function.grad x i = g x i := hx
              rw [← hx']
        rw [hnorm]
        exact u.tendsto_approx_grad i }
  exact ⟨v, rfl⟩

theorem IsPotentialZeroTraceOn.isPotentialOn {d : ℕ} {U : Set (Vec d)} {f : Vec d → Vec d}
    (hf : IsPotentialZeroTraceOn U f) : IsPotentialOn U f := by
  rcases hf with ⟨u, rfl⟩
  exact u.toH1Function.isPotentialOn

theorem isPotentialOn_zero {d : ℕ} {U : Set (Vec d)} :
    IsPotentialOn U (0 : Vec d → Vec d) :=
  (0 : H1Function U).isPotentialOn

theorem isPotentialOn_add {d : ℕ} {U : Set (Vec d)} {f g : Vec d → Vec d}
    (hf : IsPotentialOn U f) (hg : IsPotentialOn U g) :
    IsPotentialOn U (f + g) := by
  rcases hf with ⟨u, rfl⟩
  rcases hg with ⟨v, rfl⟩
  exact (u + v).isPotentialOn

theorem isPotentialOn_smul {d : ℕ} {U : Set (Vec d)} {f : Vec d → Vec d}
    (hf : IsPotentialOn U f) (c : ℝ) :
    IsPotentialOn U (c • f) := by
  rcases hf with ⟨u, rfl⟩
  exact (c • u).isPotentialOn

theorem isPotentialZeroTraceOn_zero {d : ℕ} {U : Set (Vec d)} :
    IsPotentialZeroTraceOn U (0 : Vec d → Vec d) :=
  (0 : H10Function U).isPotentialZeroTraceOn

theorem isPotentialZeroTraceOn_add {d : ℕ} {U : Set (Vec d)} {f g : Vec d → Vec d}
    (hf : IsPotentialZeroTraceOn U f) (hg : IsPotentialZeroTraceOn U g) :
    IsPotentialZeroTraceOn U (f + g) := by
  rcases hf with ⟨u, rfl⟩
  rcases hg with ⟨v, rfl⟩
  exact (u + v).isPotentialZeroTraceOn

theorem isPotentialZeroTraceOn_smul {d : ℕ} {U : Set (Vec d)} {f : Vec d → Vec d}
    (hf : IsPotentialZeroTraceOn U f) (c : ℝ) :
    IsPotentialZeroTraceOn U (c • f) := by
  rcases hf with ⟨u, rfl⟩
  exact (c • u).isPotentialZeroTraceOn

theorem isPotentialOn_of_contDiff {d : ℕ} {U : Set (Vec d)} (hU : IsOpen U)
    {u : Vec d → ℝ} (hu : ContDiff ℝ 1 u) (hu_supp : HasCompactSupport u) :
    IsPotentialOn U (fun x i => (fderiv ℝ u x) (basisVec i)) :=
  (H1Function.ofContDiff hU hu hu_supp).isPotentialOn

theorem isPotentialZeroTraceOn_of_contDiff {d : ℕ} {U : Set (Vec d)} (hU : IsOpen U)
    {u : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hu_supp : HasCompactSupport u) (hu_sub : tsupport u ⊆ U) :
    IsPotentialZeroTraceOn U (fun x i => (fderiv ℝ u x) (basisVec i)) :=
  (H10Function.ofContDiff hU hu hu_supp hu_sub).isPotentialZeroTraceOn

theorem isSolenoidalOn_zero {d : ℕ} {U : Set (Vec d)} :
    IsSolenoidalOn U (0 : Vec d → Vec d) := by
  intro φ
  simp [vecDot]

theorem isSolenoidalOn_add {d : ℕ} {U : Set (Vec d)} {f g : Vec d → Vec d}
    (hf : IsSolenoidalOn U f) (hg : IsSolenoidalOn U g)
    (hf_int : ∀ φ : H10Function U,
      MeasureTheory.IntegrableOn (fun x => vecDot (f x) (φ.toH1Function.grad x)) U)
    (hg_int : ∀ φ : H10Function U,
      MeasureTheory.IntegrableOn (fun x => vecDot (g x) (φ.toH1Function.grad x)) U) :
    IsSolenoidalOn U (f + g) := by
  intro φ
  rw [show (fun x => vecDot ((f + g) x) (φ.toH1Function.grad x)) =
      fun x => vecDot (f x) (φ.toH1Function.grad x) + vecDot (g x) (φ.toH1Function.grad x) by
        funext x
        simp [vecDot, Finset.sum_add_distrib, add_mul]]
  rw [MeasureTheory.integral_add (hf_int φ) (hg_int φ), hf φ, hg φ]
  simp

theorem isSolenoidalOn_smul {d : ℕ} {U : Set (Vec d)} {g : Vec d → Vec d}
    (hg : IsSolenoidalOn U g) (c : ℝ) :
    IsSolenoidalOn U (c • g) := by
  intro φ
  rw [show (fun x => vecDot ((c • g) x) (φ.toH1Function.grad x)) =
      fun x => c * vecDot (g x) (φ.toH1Function.grad x) by
        funext x
        simp [vecDot, Finset.mul_sum, mul_assoc]]
  rw [MeasureTheory.integral_const_mul]
  simp [hg φ]

theorem isSolenoidalZeroNormalTraceOn_zero {d : ℕ} {U : Set (Vec d)} :
    IsSolenoidalZeroNormalTraceOn U (0 : Vec d → Vec d) := by
  intro φ
  simp [vecDot]

theorem isSolenoidalZeroNormalTraceOn_add {d : ℕ} {U : Set (Vec d)} {f g : Vec d → Vec d}
    (hf : IsSolenoidalZeroNormalTraceOn U f) (hg : IsSolenoidalZeroNormalTraceOn U g)
    (hf_int : ∀ φ : H1Function U,
      MeasureTheory.IntegrableOn (fun x => vecDot (f x) (φ.grad x)) U)
    (hg_int : ∀ φ : H1Function U,
      MeasureTheory.IntegrableOn (fun x => vecDot (g x) (φ.grad x)) U) :
    IsSolenoidalZeroNormalTraceOn U (f + g) := by
  intro φ
  rw [show (fun x => vecDot ((f + g) x) (φ.grad x)) =
      fun x => vecDot (f x) (φ.grad x) + vecDot (g x) (φ.grad x) by
        funext x
        simp [vecDot, Finset.sum_add_distrib, add_mul]]
  rw [MeasureTheory.integral_add (hf_int φ) (hg_int φ), hf φ, hg φ]
  simp

theorem isSolenoidalZeroNormalTraceOn_smul {d : ℕ} {U : Set (Vec d)} {g : Vec d → Vec d}
    (hg : IsSolenoidalZeroNormalTraceOn U g) (c : ℝ) :
    IsSolenoidalZeroNormalTraceOn U (c • g) := by
  intro φ
  rw [show (fun x => vecDot ((c • g) x) (φ.grad x)) =
      fun x => c * vecDot (g x) (φ.grad x) by
        funext x
        simp [vecDot, Finset.mul_sum, mul_assoc]]
  rw [MeasureTheory.integral_const_mul]
  simp [hg φ]

theorem IsSolenoidalOn.test_of_contDiff {d : ℕ} {U : Set (Vec d)} {g : Vec d → Vec d}
    (hg : IsSolenoidalOn U g) (hU : IsOpen U)
    {u : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hu_supp : HasCompactSupport u) (hu_sub : tsupport u ⊆ U) :
    ∫ x in U, vecDot (g x) (fun i => (fderiv ℝ u x) (basisVec i)) ∂MeasureTheory.volume = 0 := by
  simpa [H10Function.ofContDiff, H1Function.ofContDiff] using
    hg (H10Function.ofContDiff hU hu hu_supp hu_sub)

theorem IsSolenoidalZeroNormalTraceOn.test_of_contDiff {d : ℕ} {U : Set (Vec d)}
    {g : Vec d → Vec d} (hg : IsSolenoidalZeroNormalTraceOn U g) (hU : IsOpen U)
    {u : Vec d → ℝ} (hu : ContDiff ℝ 1 u) (hu_supp : HasCompactSupport u) :
    ∫ x in U, vecDot (g x) (fun i => (fderiv ℝ u x) (basisVec i)) ∂MeasureTheory.volume = 0 := by
  simpa [H1Function.ofContDiff] using hg (H1Function.ofContDiff hU hu hu_supp)

end Homogenization
