/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.RealModes.Modes

/-! # Projection

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open MeasureTheory
attribute [local instance] realModesMeasureSpace realModesMeasureIsAddHaar realModesProbability
namespace AVenhance.Infra.Parabolic.FourierGalerkin

theorem Projection.complexFourierPartialSumComplex_sum {ι : Type*}
    {N : ℕ} (s : Finset ι) (F : ι → Torus → ℂ)
    (hF : ∀ i ∈ s, Continuous (F i)) (x : Torus) :
    complexFourierPartialSumComplex N (fun y => ∑ i ∈ s, F i y) x =
      ∑ i ∈ s, complexFourierPartialSumComplex N (F i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [complexFourierPartialSumComplex, UnitAddTorus.mFourierCoeff]
  | @insert i s hi ih =>
    have htail : Continuous (fun y => ∑ j ∈ s, F j y) :=
      continuous_finsetSum s (fun j hj => hF j (Finset.mem_insert_of_mem hj))
    have hhead : Continuous (F i) := hF i (Finset.mem_insert_self i s)
    have hdecomp : (fun y => ∑ j ∈ insert i s, F j y) =
        fun y => F i y + ∑ j ∈ s, F j y := by
      funext y
      rw [Finset.sum_insert hi]
    rw [hdecomp, complexFourierPartialSumComplex_add hhead htail x]
    rw [ih (fun j hj => hF j (Finset.mem_insert_of_mem hj))]
    simp [Finset.sum_insert, hi]

theorem Projection.complexFourierPartialSumComplex_linearCombination {N : ℕ}
    {k l : Fin 2 → ℤ} (hk : frequencyPair k ∈ symmetricFrequencyBox N)
    (hl : frequencyPair l ∈ symmetricFrequencyBox N) (c d : ℂ) (x : Torus) :
    complexFourierPartialSumComplex N
      (fun y => c * UnitAddTorus.mFourier k y + d * UnitAddTorus.mFourier l y) x =
      c * UnitAddTorus.mFourier k x + d * UnitAddTorus.mFourier l x := by
  have hcharK : Continuous (UnitAddTorus.mFourier k) :=
    (UnitAddTorus.mFourier k).continuous
  have hcharL : Continuous (UnitAddTorus.mFourier l) :=
    (UnitAddTorus.mFourier l).continuous
  calc
    _ = complexFourierPartialSumComplex N
        (fun y => c * UnitAddTorus.mFourier k y) x +
          complexFourierPartialSumComplex N
            (fun y => d * UnitAddTorus.mFourier l y) x :=
      complexFourierPartialSumComplex_add
        (continuous_const.mul hcharK) (continuous_const.mul hcharL) x
    _ = c * UnitAddTorus.mFourier k x + d * UnitAddTorus.mFourier l x := by
      rw [complexFourierPartialSumComplex_const_mul c x,
        complexFourierPartialSumComplex_const_mul d x,
        complexFourierPartialSumComplex_mFourier k hk x,
        complexFourierPartialSumComplex_mFourier l hl x]

theorem Projection.frequencyPair_neg (k : Fin 2 → ℤ) :
    frequencyPair (-k) = -frequencyPair k := by
  apply Prod.ext <;> simp [frequencyPair]

theorem Projection.neg_frequency_mem_box {N : ℕ} {k : Fin 2 → ℤ}
    (hk : frequencyPair k ∈ symmetricFrequencyBox N) :
    frequencyPair (-k) ∈ symmetricFrequencyBox N := by
  rw [Projection.frequencyPair_neg]
  exact neg_mem_symmetricFrequencyBox hk

/-- Every real sine/cosine mode in the cutoff is fixed by the corresponding complex Fourier sum. -/
theorem complexFourierPartialSumComplex_realFourierMode {N : ℕ}
    (a : RealFourierIndex N) (x : Torus) :
    complexFourierPartialSumComplex N (fun y => (realFourierMode N a y : ℂ)) x =
      (realFourierMode N a x : ℂ) := by
  classical
  cases a with
  | none =>
    have hzero : frequencyPair (0 : Fin 2 → ℤ) ∈ symmetricFrequencyBox N := by
      simp [frequencyPair, symmetricFrequencyBox]
    have hchar := complexFourierPartialSumComplex_mFourier
      (0 : Fin 2 → ℤ) hzero x
    have hconst : (fun y : Torus => (1 : ℂ)) =
        UnitAddTorus.mFourier (0 : Fin 2 → ℤ) := by
      funext y
      have h0 := congrArg (fun f : C(Torus, ℂ) => f y)
        UnitAddTorus.mFourier_zero
      simpa using h0.symm
    change complexFourierPartialSumComplex N (fun y : Torus => (1 : ℂ)) x = 1
    rw [hconst]
    exact hchar.trans
      (congrArg (fun f : C(Torus, ℂ) => f x) UnitAddTorus.mFourier_zero)
  | some q =>
    rcases q with ⟨p, isSine⟩
    let k := representativeFrequency p
    have hk : frequencyPair k ∈ symmetricFrequencyBox N := by
      exact representativeFrequency_mem_box p
    have hneg := Projection.neg_frequency_mem_box hk
    cases isSine
    · have hfun : (fun y => (realFourierMode N (some (p, false)) y : ℂ)) =
          fun y => (Real.sqrt 2 / 2 : ℝ) * UnitAddTorus.mFourier k y +
            (Real.sqrt 2 / 2 : ℝ) * UnitAddTorus.mFourier (-k) y := by
        funext y
        calc
          _ = (Real.sqrt 2 / 2 : ℝ) *
              (UnitAddTorus.mFourier (representativeFrequency p) y +
                UnitAddTorus.mFourier (-representativeFrequency p) y) :=
            realFourierMode_cos_complexExpansion N p y
          _ = _ := by simp [k, mul_add]
      calc
        _ = complexFourierPartialSumComplex N
            (fun y => (Real.sqrt 2 / 2 : ℝ) * UnitAddTorus.mFourier k y +
              (Real.sqrt 2 / 2 : ℝ) * UnitAddTorus.mFourier (-k) y) x := by
          rw [hfun]
        _ = (Real.sqrt 2 / 2 : ℝ) * UnitAddTorus.mFourier k x +
              (Real.sqrt 2 / 2 : ℝ) * UnitAddTorus.mFourier (-k) x :=
          Projection.complexFourierPartialSumComplex_linearCombination hk hneg
            (Real.sqrt 2 / 2 : ℝ) (Real.sqrt 2 / 2 : ℝ) x
        _ = (realFourierMode N (some (p, false)) x : ℂ) := (congrFun hfun x).symm
    · have hfun : (fun y => (realFourierMode N (some (p, true)) y : ℂ)) =
          fun y => ((Real.sqrt 2 / 2 : ℝ) * (-Complex.I)) *
              UnitAddTorus.mFourier k y +
            (-((Real.sqrt 2 / 2 : ℝ) * (-Complex.I))) *
              UnitAddTorus.mFourier (-k) y := by
        funext y
        calc
          _ = (Real.sqrt 2 / 2 : ℝ) * (-Complex.I) *
              (UnitAddTorus.mFourier (representativeFrequency p) y -
                UnitAddTorus.mFourier (-representativeFrequency p) y) :=
            realFourierMode_sin_complexExpansion N p y
          _ = _ := by ring
      calc
        _ = complexFourierPartialSumComplex N
            (fun y => ((Real.sqrt 2 / 2 : ℝ) * (-Complex.I)) *
                UnitAddTorus.mFourier k y +
              (-((Real.sqrt 2 / 2 : ℝ) * (-Complex.I))) *
                UnitAddTorus.mFourier (-k) y) x := by
          rw [hfun]
        _ = ((Real.sqrt 2 / 2 : ℝ) * (-Complex.I)) *
              UnitAddTorus.mFourier k x +
            (-((Real.sqrt 2 / 2 : ℝ) * (-Complex.I))) *
              UnitAddTorus.mFourier (-k) x :=
          Projection.complexFourierPartialSumComplex_linearCombination hk hneg
            ((Real.sqrt 2 / 2 : ℝ) * (-Complex.I))
            (-((Real.sqrt 2 / 2 : ℝ) * (-Complex.I))) x
        _ = (realFourierMode N (some (p, true)) x : ℂ) := (congrFun hfun x).symm

/-- The finite real-mode dimension at cutoff `N`. -/
@[irreducible]
def RealFourierDimension (N : ℕ) := Fintype.card (RealFourierIndex N)

/-- Reindex the concrete real Fourier family by the standard finite type used by the ODE layer. -/
noncomputable def realFourierIndexEquivFin (N : ℕ) :
    RealFourierIndex N ≃ Fin (RealFourierDimension N) := by
  unfold RealFourierDimension
  exact Fintype.equivFin _

/-- Lift a real Fourier index into a larger symmetric cutoff. -/
def positiveRepresentativeLift {M N : ℕ} (hMN : M ≤ N)
    (p : {p : ℤ × ℤ // p ∈ positiveFrequencyRepresentatives M}) :
    {p : ℤ × ℤ // p ∈ positiveFrequencyRepresentatives N} :=
  ⟨p.1, positiveFrequencyRepresentatives_subset hMN p.2⟩

/-- The representative frequency is unchanged by lifting a positive representative. -/
theorem representativeFrequency_lift {M N : ℕ} (hMN : M ≤ N)
    (p : {p : ℤ × ℤ // p ∈ positiveFrequencyRepresentatives M}) :
    representativeFrequency (positiveRepresentativeLift hMN p) = representativeFrequency p := rfl

/-- Lift a real Fourier index into a larger symmetric cutoff. -/
noncomputable def realFourierIndexLift {M N : ℕ} (hMN : M ≤ N) :
    RealFourierIndex M → RealFourierIndex N := by
  classical
  intro a
  cases a with
  | none => exact none
  | some q =>
    rcases q with ⟨p, isSine⟩
    exact some (positiveRepresentativeLift hMN p, isSine)

/-- Lifting real indices to a larger cutoff is injective. -/
theorem realFourierIndexLift_injective {M N : ℕ} (hMN : M ≤ N) :
    Function.Injective (realFourierIndexLift hMN) := by
  classical
  intro a b hab
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some q => cases hab
  | some q =>
    cases b with
    | none => cases hab
    | some r =>
      rcases q with ⟨p, bp⟩
      rcases r with ⟨q, bq⟩
      have hpair := Option.some.inj hab
      have hsub : positiveRepresentativeLift hMN p = positiveRepresentativeLift hMN q :=
        congrArg Prod.fst hpair
      have hval : p.val = q.val := congrArg
        (fun z : {p : ℤ × ℤ // p ∈ positiveFrequencyRepresentatives N} => z.val) hsub
      have hpq : p = q := Subtype.ext hval
      have hb : bp = bq := congrArg Prod.snd hpair
      cases hpq
      cases hb
      rfl

/-- The lift preserves every real mode. -/
theorem realFourierMode_lift {M N : ℕ} (hMN : M ≤ N)
    (a : RealFourierIndex M) :
    realFourierMode N (realFourierIndexLift hMN a) = realFourierMode M a := by
  funext x
  cases a with
  | none => rfl
  | some q =>
    rcases q with ⟨p, isSine⟩
    change realFourierMode N (some (positiveRepresentativeLift hMN p, isSine)) x = _
    have hfreq := representativeFrequency_lift hMN p
    cases isSine <;>
      simp only [realFourierMode, Bool.false_eq_true, ↓reduceIte] <;> rw [hfreq]

/-- The lift preserves the smooth ambient real mode. -/
theorem realFourierModeAmbient_lift {M N : ℕ} (hMN : M ≤ N)
    (a : RealFourierIndex M) :
    realFourierModeAmbient N (realFourierIndexLift hMN a) = realFourierModeAmbient M a := by
  funext x
  cases a with
  | none => rfl
  | some q =>
    rcases q with ⟨p, isSine⟩
    change realFourierModeAmbient N (some (positiveRepresentativeLift hMN p, isSine)) x = _
    have hfreq := representativeFrequency_lift hMN p
    cases isSine <;>
      simp only [realFourierModeAmbient, Bool.false_eq_true, ↓reduceIte] <;> rw [hfreq]

/-- The lift also preserves the ambient periodic gradient mode. -/
theorem realFourierModeAmbientGrad_lift {M N : ℕ} (hMN : M ≤ N)
    (a : RealFourierIndex M) :
    realFourierModeAmbientGrad N (realFourierIndexLift hMN a) =
      realFourierModeAmbientGrad M a := by
  unfold realFourierModeAmbientGrad
  rw [realFourierModeAmbient_lift hMN a]

/-- The scalar Fourier mode family with `Fin` indices. -/
noncomputable def realFourierModeFin (N : ℕ) :
    Fin (RealFourierDimension N) → Torus → ℝ :=
  fun i => realFourierMode N ((realFourierIndexEquivFin N).symm i)

/-- The gradient family with the matching `Fin` indices. -/
noncomputable def realFourierModeGradFin (N : ℕ) :
    Fin (RealFourierDimension N) → Torus → Homogenization.Vec 2 :=
  fun i => realFourierModeGrad N ((realFourierIndexEquivFin N).symm i)

/-- The `Fin`-indexed injection induced by a nested real Fourier cutoff. -/
noncomputable def realFourierIndexLiftFin {M N : ℕ} (hMN : M ≤ N) :
    Fin (RealFourierDimension M) → Fin (RealFourierDimension N) :=
  fun i => realFourierIndexEquivFin N
    (realFourierIndexLift hMN ((realFourierIndexEquivFin M).symm i))

/-- The scalar mode is unchanged by the `Fin`-indexed cutoff injection. -/
theorem realFourierModeFin_lift {M N : ℕ} (hMN : M ≤ N)
    (i : Fin (RealFourierDimension M)) :
    realFourierModeFin N (realFourierIndexLiftFin hMN i) = realFourierModeFin M i := by
  simp only [realFourierModeFin, realFourierIndexLiftFin, Equiv.symm_apply_apply]
  exact realFourierMode_lift hMN _

theorem realFourierModeFin_orthonormal (N : ℕ)
    (i j : Fin (RealFourierDimension N)) :
    ∫ x : Torus, realFourierModeFin N i x * realFourierModeFin N j x =
      if i = j then 1 else 0 := by
  simpa [realFourierModeFin, realFourierIndexEquivFin] using
    realFourierMode_orthonormal N
      ((realFourierIndexEquivFin N).symm i) ((realFourierIndexEquivFin N).symm j)

theorem realFourierModeFin_continuous (N : ℕ)
    (i : Fin (RealFourierDimension N)) : Continuous (realFourierModeFin N i) := by
  simpa [realFourierModeFin] using
    realFourierMode_continuous N ((realFourierIndexEquivFin N).symm i)

theorem realFourierModeFin_eq_periodicToTorus (N : ℕ)
    (i : Fin (RealFourierDimension N)) :
    realFourierModeFin N i = AVenhance.Infra.Torus.periodicToTorus
      (realFourierModeAmbient N ((realFourierIndexEquivFin N).symm i)) := by
  exact realFourierMode_eq_periodicToTorus N ((realFourierIndexEquivFin N).symm i)

theorem realFourierModeGradFin_eq_periodicToTorus (N : ℕ)
    (i : Fin (RealFourierDimension N)) :
    realFourierModeGradFin N i = AVenhance.Infra.Torus.periodicToTorus
      (realFourierModeAmbientGrad N ((realFourierIndexEquivFin N).symm i)) := rfl

/-- The gradient mode is unchanged by the `Fin`-indexed cutoff injection. -/
theorem realFourierModeGradFin_lift {M N : ℕ} (hMN : M ≤ N)
    (i : Fin (RealFourierDimension M)) :
    realFourierModeGradFin N (realFourierIndexLiftFin hMN i) =
      realFourierModeGradFin M i := by
  rw [realFourierModeGradFin_eq_periodicToTorus,
    realFourierModeGradFin_eq_periodicToTorus]
  simpa [realFourierIndexLiftFin] using congrArg AVenhance.Infra.Torus.periodicToTorus
    (realFourierModeAmbientGrad_lift hMN ((realFourierIndexEquivFin M).symm i))

theorem complexFourierPartialSumComplex_modeExpansion {N : ℕ}
    (c : Coefficients (RealFourierDimension N)) (x : Torus) :
    complexFourierPartialSumComplex N
      (fun y => (modeExpansion (RealFourierDimension N) (realFourierModeFin N) c y : ℂ)) x =
      (modeExpansion (RealFourierDimension N) (realFourierModeFin N) c x : ℂ) := by
  classical
  let F : Fin (RealFourierDimension N) → Torus → ℂ := fun i y =>
    (c i : ℂ) * (realFourierModeFin N i y : ℂ)
  have hcast : (fun y =>
      (modeExpansion (RealFourierDimension N) (realFourierModeFin N) c y : ℂ)) =
      fun y => ∑ i : Fin (RealFourierDimension N), F i y := by
    funext y
    simp [F, modeExpansion]
  have hcont : ∀ i, Continuous (F i) := by
    intro i
    exact continuous_const.mul (Complex.continuous_ofReal.comp
      (realFourierModeFin_continuous N i))
  have hterm (i : Fin (RealFourierDimension N)) (x : Torus) :
      complexFourierPartialSumComplex N (F i) x = F i x := by
    dsimp [F]
    rw [complexFourierPartialSumComplex_const_mul]
    simpa [realFourierModeFin] using
      congrArg (fun z : ℂ => (c i : ℂ) * z)
        (complexFourierPartialSumComplex_realFourierMode
          ((realFourierIndexEquivFin N).symm i) x)
  calc
    _ = complexFourierPartialSumComplex N (fun y => ∑ i ∈ Finset.univ, F i y) x := by
      rw [hcast]
    _ = ∑ i ∈ Finset.univ, complexFourierPartialSumComplex N (F i) x :=
      Projection.complexFourierPartialSumComplex_sum Finset.univ F
        (fun i _ => hcont i) x
    _ = ∑ i ∈ Finset.univ, F i x := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hterm i x
    _ = (modeExpansion (RealFourierDimension N) (realFourierModeFin N) c x : ℂ) := by
      symm
      exact congrFun hcast x

/-- Every finite coefficient expansion of the cutoff's real modes is fixed by its real projection.
-/
theorem realFourierProjection_modeExpansion (N : ℕ)
    (c : Coefficients (RealFourierDimension N)) :
    realFourierProjection N
        (modeExpansion (RealFourierDimension N) (realFourierModeFin N) c) =
      modeExpansion (RealFourierDimension N) (realFourierModeFin N) c := by
  funext x
  have hproj := congrFun (realFourierProjection_complexification N
    (modeExpansion (RealFourierDimension N) (realFourierModeFin N) c)) x
  change (realFourierProjection N
      (modeExpansion (RealFourierDimension N) (realFourierModeFin N) c) x : ℂ) =
    complexFourierPartialSumComplex N
      (fun y => (modeExpansion (RealFourierDimension N) (realFourierModeFin N) c y : ℂ)) x
    at hproj
  have hsum := complexFourierPartialSumComplex_modeExpansion c x
  have h := hproj.trans hsum
  simpa using congrArg Complex.re h

end AVenhance.Infra.Parabolic.FourierGalerkin

end
