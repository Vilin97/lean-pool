/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.H6Pressure

@[expose] public section

/-!
Uniform finite-order product and pressure constants from bounds on the
actual coefficient derivative tree. At each fixed Sobolev order these
costs are finite polynomials in the coefficient bound and inverse coercivity.
-/

noncomputable section

namespace EulerCoefficientJetPressureBounds

open Finset EulerLiftedGradientSpace EulerSpatialSobolevInverse EulerJetProductBounds

def productCost (B : ℝ) : ℕ → ℝ
  | 0 => B
  | q+1 => B+8*productCost B q

def pressureCost (c B : ℝ) : ℕ → ℝ
  | 0 => c⁻¹
  | q+1 => c⁻¹+4*(pressureCost c B q*(1+productCost B q*pressureCost c B q))

theorem productCost_nonneg (B : ℝ) (hB : 0 ≤ B) (q : ℕ) : 0 ≤ productCost B q := by
  induction q with
  | zero => exact hB
  | succ q ih => simp only [productCost]; positivity

theorem pressureCost_nonneg (c B : ℝ) (hc : 0 < c) (hB : 0 ≤ B) (q : ℕ) :
    0 ≤ pressureCost c B q := by
  induction q with
  | zero => exact inv_nonneg.mpr hc.le
  | succ q ih =>
      have hp := productCost_nonneg B hB q
      simp only [pressureCost]
      positivity

variable {P : ℝ} [Fact (0 < P)] {dirs : Fin 4 → LiftTangent}

def TreeBound {s : ℕ} {A : SmoothCoefficient P} (K : CoefficientJet P dirs s A) (B : ℝ) : Prop :=
  match K with
  | .zero A => (A.bound : ℝ) ≤ B
  | .succ _ lower _ => (A.bound : ℝ) ≤ B ∧ ∀ i, TreeBound (lower i) B

omit [Fact (0 < P)] in
theorem TreeBound.root {s : ℕ} {A : SmoothCoefficient P} {K : CoefficientJet P dirs s A}
    {B : ℝ} (hK : TreeBound K B) : (A.bound : ℝ) ≤ B := by
  cases K with
  | zero => exact hK
  | succ => exact hK.1

omit [Fact (0 < P)] in
theorem treeBound_of_levels {s : ℕ} {A : SmoothCoefficient P} (K : CoefficientJet P dirs s A)
    (B : ℝ) (hb : ∀ n, n ≤ s → boundLevel P K n ≤ B) : TreeBound K B := by
  induction K with
  | zero A => simpa only [boundLevel,TreeBound] using hb 0 le_rfl
  | @succ s A dA lower hd ih =>
      refine ⟨?_,?_⟩
      · simpa only [boundLevel] using hb 0 (Nat.zero_le _)
      intro i
      apply ih i
      intro n hn
      have hs : boundLevel P (lower i) n ≤ ∑ j : Fin 4, boundLevel P (lower j) n :=
        single_le_sum (fun j _ => boundLevel_nonneg (lower j)) (mem_univ i)
      have hh := hb (n+1) (by omega)
      rw [boundLevel] at hh
      exact hs.trans hh

omit [Fact (0 < P)] in
theorem TreeBound.truncate {s : ℕ} {A : SmoothCoefficient P}
    {K : CoefficientJet P dirs (s+1) A} {B : ℝ} (hK : TreeBound K B) :
    TreeBound K.truncate B := by
  induction s generalizing A with
  | zero => cases K; exact hK.1
  | succ s ih =>
      cases K with
      | succ dA lower hd =>
          exact ⟨hK.1,fun i => ih (hK.2 i)⟩

omit [Fact (0 < P)] in
theorem TreeBound.restrict {s : ℕ} {A : SmoothCoefficient P}
    {K : CoefficientJet P dirs s A} {B : ℝ} (hK : TreeBound K B)
    (q : ℕ) (hq : q ≤ s) : TreeBound (EulerH6Pressure.CoefficientJet.restrict K q hq) B := by
  induction q generalizing s A with
  | zero =>
      rw [EulerH6Pressure.CoefficientJet.restrict,TreeBound]
      exact hK.root
  | succ q ih =>
      cases K with
      | zero => omega
      | succ dA lower hd =>
          rw [EulerH6Pressure.CoefficientJet.restrict,TreeBound]
          exact ⟨hK.1,fun i => ih (hK.2 i) (by omega)⟩

omit [Fact (0 < P)] in
theorem TreeBound.productConstant_le {s : ℕ} {A : SmoothCoefficient P}
    {K : CoefficientJet P dirs s A} {B : ℝ} (hK : TreeBound K B) :
    K.productConstant ≤ productCost B s := by
  induction s generalizing A with
  | zero => cases K; simpa only [CoefficientJet.productConstant,productCost,TreeBound] using hK
  | succ s ih =>
      cases K with
      | succ dA lower hd =>
          rw [CoefficientJet.productConstant,productCost]
          calc
            _ ≤ B+∑ _i : Fin 4, (productCost B s+productCost B s) :=
              add_le_add hK.1 (sum_le_sum (fun i _ =>
                add_le_add (ih hK.truncate) (ih (hK.2 i))))
            _ = _ := by norm_num only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

omit [Fact (0 < P)] in
theorem TreeBound.pressureConstant_le {s : ℕ} {A : SmoothCoefficient P}
    {K : CoefficientJet P dirs s A} {B : ℝ} (hK : TreeBound K B)
    (c : ℝ) (hc : 0 < c) (hB : 0 ≤ B) : K.pressureConstant c ≤ pressureCost c B s := by
  induction s generalizing A with
  | zero => cases K; rw [CoefficientJet.pressureConstant,pressureCost]
  | succ s ih =>
      cases K with
      | succ dA lower hd =>
          rw [CoefficientJet.pressureConstant,pressureCost]
          let K₀ := (CoefficientJet.succ dA lower hd).truncate
          have hp := ih hK.truncate
          have hp0 : 0 ≤ K₀.pressureConstant c := K₀.pressureConstant_nonneg c hc
          have hP0 := pressureCost_nonneg c B hc hB s
          have hC0 := productCost_nonneg B hB s
          have ht (i : Fin 4) : K₀.pressureConstant c*(1+(lower
            i).productConstant*K₀.pressureConstant c) ≤
              pressureCost c B s*(1+productCost B s*pressureCost c B s) := by
            have hi := (hK.2 i).productConstant_le
            have hc0 := (lower i).productConstant_nonneg
            exact mul_le_mul hp (add_le_add le_rfl (mul_le_mul hi hp hp0 hC0))
              (by positivity) hP0
          calc
            _ ≤ c⁻¹+∑ _i : Fin 4, pressureCost c B s*(1+productCost B s*pressureCost c B s) :=
              add_le_add le_rfl (sum_le_sum (fun i _ => ht i))
            _ = _ := by norm_num only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]

end EulerCoefficientJetPressureBounds
