/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section52.PositiveExcessUpper
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section52.PositiveExcessLowerAndIntegrability.PowIntegrable

/-! # Unit Descendant Sup -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section52

open MeasureTheory
open scoped Matrix.Norms.Elementwise

noncomputable section

theorem section52_annealedMomentRoot_le_const_mul_of_ae_le
    {d : ℕ} {P : Ch04.RestrictionCoeffLaw d} {ξ : ℕ} {c : ℝ}
    {X Y : RegCoeffField d → ℝ}
    (hξ : 1 ≤ ξ) (hc : 0 ≤ c)
    (hX_nonneg : ∀ a, 0 ≤ X a) (hY_nonneg : ∀ a, 0 ≤ Y a)
    (hX_aemeas : AEMeasurable X P)
    (hY_abs_int : Integrable (fun a => |Y a| ^ ξ) P)
    (hXY : X ≤ᵐ[P] fun a => c * Y a) :
    Ch04.annealedMomentRoot P ξ X ≤ c * Ch04.annealedMomentRoot P ξ Y := by
  have hCY_nonneg : ∀ a, 0 ≤ c * Y a := fun a => mul_nonneg hc (hY_nonneg a)
  have hY_pow_int : Integrable (fun a => Y a ^ ξ) P := by
    refine hY_abs_int.congr ?_
    filter_upwards with a
    rw [abs_of_nonneg (hY_nonneg a)]
  have hCY_pow_int : Integrable (fun a => (c * Y a) ^ ξ) P := by
    refine (hY_pow_int.const_mul (c ^ ξ)).congr ?_
    filter_upwards with a
    rw [mul_pow]
  have hCY_abs_int : Integrable (fun a => |c * Y a| ^ ξ) P := by
    refine hCY_pow_int.congr ?_
    filter_upwards with a
    rw [abs_of_nonneg (hCY_nonneg a)]
  have hX_abs_le :
      ∀ᵐ a ∂P, |X a| ≤ c * Y a := by
    filter_upwards [hXY] with a ha
    simpa [abs_of_nonneg (hX_nonneg a)] using ha
  have hX_abs_int : Integrable (fun a => |X a| ^ ξ) P :=
    section52_integrable_abs_pow_of_ae_abs_le_nonneg
      (P := P) (ξ := ξ) (X := X) (Y := fun a => c * Y a)
      hX_aemeas hCY_nonneg hX_abs_le hCY_abs_int
  have hX_pow_int : Integrable (fun a => X a ^ ξ) P := by
    refine hX_abs_int.congr ?_
    filter_upwards with a
    rw [abs_of_nonneg (hX_nonneg a)]
  have hmono :
      Ch04.annealedMomentRoot P ξ X ≤
        Ch04.annealedMomentRoot P ξ (fun a => c * Y a) :=
    Ch04.annealedMomentRoot_le_of_ae_nonneg_le
      (P := P) (ξ := ξ) (X := X) (Y := fun a => c * Y a)
      hξ hX_nonneg hX_pow_int hCY_pow_int hXY
  calc
    Ch04.annealedMomentRoot P ξ X ≤
        Ch04.annealedMomentRoot P ξ (fun a => c * Y a) := hmono
    _ = c * Ch04.annealedMomentRoot P ξ Y :=
        section52_annealedMomentRoot_const_mul_of_nonneg hξ hc hY_nonneg

theorem upper_unitDescendantSup_integrable_abs_pow
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    {s : ℝ} {ξ m : ℕ} (hs : 0 < s) (hξ_one : 1 ≤ ξ)
    (hSourceInt :
      Integrable
        (fun a : RegCoeffField d =>
          (Ch04.LambdaSqCoeffField (originCube d 0) s (.finite 1) a) ^ ξ) P) :
    let D := descendantsAtScale (originCube d (m : ℤ)) 0
    let hD : D.Nonempty :=
      descendantsAtScale_nonempty (originCube d (m : ℤ)) (by simp [originCube])
    Integrable
      (fun a : RegCoeffField d =>
        |D.sup' hD (fun U => Ch04.LambdaSqCoeffField U s (.finite 1) a)| ^ ξ) P := by
  classical
  intro D hD
  let X : TriadicCube d → RegCoeffField d → ℝ :=
    fun U a => Ch04.LambdaSqCoeffField U s (.finite 1) a
  have hX_nonneg : ∀ U ∈ D, ∀ a, 0 ≤ X U a := by
    intro U _hU a
    exact Ch04.LambdaSqCoeffField_finite_nonneg U a hs
      (by norm_num : (1 : ℝ) ≤ 1)
  have hX_aemeas : ∀ U ∈ D, AEMeasurable (X U) P := by
    intro U _hU
    exact hP.aemeasurable_LambdaSqCoeffField_finite_one U hs
  have hX_int : ∀ U ∈ D, Integrable (fun a : RegCoeffField d => |X U a| ^ ξ) P := by
    intro U hU
    exact upper_unitDescendant_Lambda_integrable_abs_pow
      hP hStruct hs hSourceInt hU
  have hsum_int :
      Integrable (fun a : RegCoeffField d => |∑ U ∈ D, X U a| ^ ξ) P :=
    section52_integrable_abs_finset_sum_pow_of_integrable_abs_pow
      (P := P) (ξ := ξ) (s := D) (G := X)
      hξ_one hX_aemeas hX_int
  have hsum_nonneg : ∀ a, 0 ≤ ∑ U ∈ D, X U a := by
    intro a
    exact Finset.sum_nonneg fun U hU => hX_nonneg U hU a
  have hS_aemeas :
      AEMeasurable
        (fun a : RegCoeffField d => D.sup' hD (fun U => X U a)) P := by
    have h :
        AEMeasurable (D.sup' hD (fun U (a : RegCoeffField d) => X U a)) P := by
      refine Finset.sup'_induction (s := D) (H := hD)
        (f := fun U (a : RegCoeffField d) => X U a)
        (p := fun f => AEMeasurable f P) ?_ ?_
      · intro _f hf _g hg
        exact hf.sup hg
      · intro U hU
        exact hX_aemeas U hU
    convert h using 1
    ext a
    exact (Finset.sup'_apply (C := fun _ : RegCoeffField d => ℝ) hD
      (fun U (a : RegCoeffField d) => X U a) a).symm
  have hS_le_sum :
      ∀ᵐ a ∂P,
        |D.sup' hD (fun U => X U a)| ≤ ∑ U ∈ D, X U a := by
    filter_upwards with a
    have hS_nonneg : 0 ≤ D.sup' hD (fun U => X U a) := by
      rcases hD with ⟨U0, hU0⟩
      exact (hX_nonneg U0 hU0 a).trans
        (Finset.le_sup' (f := fun U => X U a) hU0)
    rw [abs_of_nonneg hS_nonneg]
    refine Finset.sup'_le hD _ ?_
    intro U hU
    exact Finset.single_le_sum
      (f := fun V => X V a) (fun V hV => hX_nonneg V hV a) hU
  exact
    section52_integrable_abs_pow_of_ae_abs_le_nonneg
      (P := P) (ξ := ξ)
      (X := fun a : RegCoeffField d => D.sup' hD (fun U => X U a))
      (Y := fun a : RegCoeffField d => ∑ U ∈ D, X U a)
      hS_aemeas hsum_nonneg hS_le_sum hsum_int

theorem upper_unitDescendantSup_aemeasurable
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) {s : ℝ} {m : ℕ} (hs : 0 < s) :
    let D := descendantsAtScale (originCube d (m : ℤ)) 0
    let hD : D.Nonempty :=
      descendantsAtScale_nonempty (originCube d (m : ℤ)) (by simp [originCube])
    AEMeasurable
      (fun a : RegCoeffField d =>
        D.sup' hD (fun U => Ch04.LambdaSqCoeffField U s (.finite 1) a)) P := by
  classical
  intro D hD
  let X : TriadicCube d → RegCoeffField d → ℝ :=
    fun U a => Ch04.LambdaSqCoeffField U s (.finite 1) a
  have h :
      AEMeasurable (D.sup' hD (fun U (a : RegCoeffField d) => X U a)) P := by
    refine Finset.sup'_induction (s := D) (H := hD)
      (f := fun U (a : RegCoeffField d) => X U a)
      (p := fun f => AEMeasurable f P) ?_ ?_
    · intro _f hf _g hg
      exact hf.sup hg
    · intro U _hU
      exact hP.aemeasurable_LambdaSqCoeffField_finite_one U hs
  convert h using 1
  ext a
  exact (Finset.sup'_apply (C := fun _ : RegCoeffField d => ℝ) hD
    (fun U (a : RegCoeffField d) => X U a) a).symm

theorem upper_unitDescendantSup_nonneg
    {d : ℕ} [NeZero d] {s : ℝ} {m : ℕ} (hs : 0 < s) (a : RegCoeffField d) :
    let D := descendantsAtScale (originCube d (m : ℤ)) 0
    let hD : D.Nonempty :=
      descendantsAtScale_nonempty (originCube d (m : ℤ)) (by simp [originCube])
    0 ≤ D.sup' hD (fun U => Ch04.LambdaSqCoeffField U s (.finite 1) a) := by
  intro D hD
  rcases hD with ⟨U0, hU0⟩
  exact
    (Ch04.LambdaSqCoeffField_finite_nonneg U0 a hs
      (by norm_num : (1 : ℝ) ≤ 1)).trans
      (Finset.le_sup'
        (f := fun U => Ch04.LambdaSqCoeffField U s (.finite 1) a) hU0)

theorem lower_unitDescendant_lambdaInv_integrable_abs_pow
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    {s : ℝ} {ξ m : ℕ} (hs : 0 < s)
    (hSourceInt :
      Integrable
        (fun a : RegCoeffField d =>
          ((Ch04.lambdaSqCoeffField (originCube d 0) s (.finite 1) a)⁻¹) ^ ξ) P)
    {U : TriadicCube d}
    (hU : U ∈ descendantsAtScale (originCube d (m : ℤ)) 0) :
    Integrable
      (fun a : RegCoeffField d => |(Ch04.lambdaSqCoeffField U s (.finite 1) a)⁻¹| ^ ξ) P := by
  classical
  let X0 : RegCoeffField d → ℝ :=
    fun a => (Ch04.lambdaSqCoeffField (originCube d 0) s (.finite 1) a)⁻¹
  have hX0_aemeas : AEMeasurable X0 P :=
    hP.aemeasurable_lambdaSqCoeffField_finite_one_inv (originCube d 0) hs
  have hX0_abs_int : Integrable (fun a : RegCoeffField d => |X0 a| ^ ξ) P := by
    refine hSourceInt.congr ?_
    filter_upwards with a
    rw [abs_of_nonneg]
    exact inv_nonneg.mpr
      (Ch04.lambdaSqCoeffField_finite_nonneg (originCube d 0) a hs
        (by norm_num : (1 : ℝ) ≤ 1))
  have hscale : U.scale = 0 := scale_eq_of_mem_descendantsAtScale hU
  let z : Fin d → ℤ := Book.Ch04.scaleTranslationShift 0 U
  have hUeq : U = translateCube z (originCube d 0) := by
    simpa [z] using (translateCube_originCube_zero_eq_of_scale_zero U hscale).symm
  have hae :
      (fun a : RegCoeffField d => (Ch04.lambdaSqCoeffField U s (.finite 1) a)⁻¹) =ᵐ[P]
        fun a => X0 (translateReg (intVecToRealVec z) a) := by
    have hcov :=
      Ch04.lambdaSqCoeffField_originCube_zero_translateByInt_ae
        hP hStruct.stationary z s (.finite 1)
    filter_upwards [by simpa [X0, hUeq] using! hcov] with a ha
    simpa [X0, hUeq] using congrArg Inv.inv ha
  have hmap :
      Measure.map (fun a : RegCoeffField d => (Ch04.lambdaSqCoeffField U s (.finite 1) a)⁻¹) P =
        Measure.map X0 P := by
    calc
      Measure.map (fun a : RegCoeffField d => (Ch04.lambdaSqCoeffField U s (.finite 1) a)⁻¹) P =
          Measure.map (fun a : RegCoeffField d => X0 (translateReg (intVecToRealVec z) a)) P :=
            Measure.map_congr hae
      _ = Measure.map X0 (Measure.map (translateReg (intVecToRealVec z)) P) := by
            symm
            exact AEMeasurable.map_map_of_aemeasurable
              (by simpa [hStruct.stationary z] using hX0_aemeas)
              (measurable_translateReg (intVecToRealVec z)).aemeasurable
      _ = Measure.map X0 P := by
            rw [hStruct.stationary z]
  exact integrable_abs_pow_of_map_eq_map_aemeasurable
    (hP.aemeasurable_lambdaSqCoeffField_finite_one_inv U hs) hX0_aemeas hmap hX0_abs_int

theorem lower_unitDescendantSup_integrable_abs_pow
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    {s : ℝ} {ξ m : ℕ} (hs : 0 < s) (hξ_one : 1 ≤ ξ)
    (hSourceInt :
      Integrable
        (fun a : RegCoeffField d =>
          ((Ch04.lambdaSqCoeffField (originCube d 0) s (.finite 1) a)⁻¹) ^ ξ) P) :
    let D := descendantsAtScale (originCube d (m : ℤ)) 0
    let hD : D.Nonempty :=
      descendantsAtScale_nonempty (originCube d (m : ℤ)) (by simp [originCube])
    Integrable
      (fun a : RegCoeffField d =>
        |D.sup' hD (fun U => (Ch04.lambdaSqCoeffField U s (.finite 1) a)⁻¹)| ^ ξ) P := by
  classical
  intro D hD
  let X : TriadicCube d → RegCoeffField d → ℝ :=
    fun U a => (Ch04.lambdaSqCoeffField U s (.finite 1) a)⁻¹
  have hX_nonneg : ∀ U ∈ D, ∀ a, 0 ≤ X U a := by
    intro U _hU a
    exact inv_nonneg.mpr
      (Ch04.lambdaSqCoeffField_finite_nonneg U a hs
        (by norm_num : (1 : ℝ) ≤ 1))
  have hX_aemeas : ∀ U ∈ D, AEMeasurable (X U) P := by
    intro U _hU
    exact hP.aemeasurable_lambdaSqCoeffField_finite_one_inv U hs
  have hX_int : ∀ U ∈ D, Integrable (fun a : RegCoeffField d => |X U a| ^ ξ) P := by
    intro U hU
    exact lower_unitDescendant_lambdaInv_integrable_abs_pow
      hP hStruct hs hSourceInt hU
  have hsum_int :
      Integrable (fun a : RegCoeffField d => |∑ U ∈ D, X U a| ^ ξ) P :=
    section52_integrable_abs_finset_sum_pow_of_integrable_abs_pow
      (P := P) (ξ := ξ) (s := D) (G := X)
      hξ_one hX_aemeas hX_int
  have hsum_nonneg : ∀ a, 0 ≤ ∑ U ∈ D, X U a := by
    intro a
    exact Finset.sum_nonneg fun U hU => hX_nonneg U hU a
  have hS_aemeas :
      AEMeasurable
        (fun a : RegCoeffField d => D.sup' hD (fun U => X U a)) P := by
    have h :
        AEMeasurable (D.sup' hD (fun U (a : RegCoeffField d) => X U a)) P := by
      refine Finset.sup'_induction (s := D) (H := hD)
        (f := fun U (a : RegCoeffField d) => X U a)
        (p := fun f => AEMeasurable f P) ?_ ?_
      · intro _f hf _g hg
        exact hf.sup hg
      · intro U hU
        exact hX_aemeas U hU
    convert h using 1
    ext a
    exact (Finset.sup'_apply (C := fun _ : RegCoeffField d => ℝ) hD
      (fun U (a : RegCoeffField d) => X U a) a).symm
  have hS_le_sum :
      ∀ᵐ a ∂P,
        |D.sup' hD (fun U => X U a)| ≤ ∑ U ∈ D, X U a := by
    filter_upwards with a
    have hS_nonneg : 0 ≤ D.sup' hD (fun U => X U a) := by
      rcases hD with ⟨U0, hU0⟩
      exact (hX_nonneg U0 hU0 a).trans
        (Finset.le_sup' (f := fun U => X U a) hU0)
    rw [abs_of_nonneg hS_nonneg]
    refine Finset.sup'_le hD _ ?_
    intro U hU
    exact Finset.single_le_sum
      (f := fun V => X V a) (fun V hV => hX_nonneg V hV a) hU
  exact
    section52_integrable_abs_pow_of_ae_abs_le_nonneg
      (P := P) (ξ := ξ)
      (X := fun a : RegCoeffField d => D.sup' hD (fun U => X U a))
      (Y := fun a : RegCoeffField d => ∑ U ∈ D, X U a)
      hS_aemeas hsum_nonneg hS_le_sum hsum_int

theorem lower_unitDescendantSup_aemeasurable
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) {s : ℝ} {m : ℕ} (hs : 0 < s) :
    let D := descendantsAtScale (originCube d (m : ℤ)) 0
    let hD : D.Nonempty :=
      descendantsAtScale_nonempty (originCube d (m : ℤ)) (by simp [originCube])
    AEMeasurable
      (fun a : RegCoeffField d =>
        D.sup' hD (fun U => (Ch04.lambdaSqCoeffField U s (.finite 1) a)⁻¹)) P := by
  classical
  intro D hD
  let X : TriadicCube d → RegCoeffField d → ℝ :=
    fun U a => (Ch04.lambdaSqCoeffField U s (.finite 1) a)⁻¹
  have h :
      AEMeasurable (D.sup' hD (fun U (a : RegCoeffField d) => X U a)) P := by
    refine Finset.sup'_induction (s := D) (H := hD)
      (f := fun U (a : RegCoeffField d) => X U a)
      (p := fun f => AEMeasurable f P) ?_ ?_
    · intro _f hf _g hg
      exact hf.sup hg
    · intro U _hU
      exact hP.aemeasurable_lambdaSqCoeffField_finite_one_inv U hs
  convert h using 1
  ext a
  exact (Finset.sup'_apply (C := fun _ : RegCoeffField d => ℝ) hD
    (fun U (a : RegCoeffField d) => X U a) a).symm

theorem lower_unitDescendantSup_nonneg
    {d : ℕ} [NeZero d] {s : ℝ} {m : ℕ} (hs : 0 < s) (a : RegCoeffField d) :
    let D := descendantsAtScale (originCube d (m : ℤ)) 0
    let hD : D.Nonempty :=
      descendantsAtScale_nonempty (originCube d (m : ℤ)) (by simp [originCube])
    0 ≤ D.sup' hD
      (fun U => (Ch04.lambdaSqCoeffField U s (.finite 1) a)⁻¹) := by
  intro D hD
  rcases hD with ⟨U0, hU0⟩
  exact
    (inv_nonneg.mpr
      (Ch04.lambdaSqCoeffField_finite_nonneg U0 a hs
        (by norm_num : (1 : ℝ) ≤ 1))).trans
      (Finset.le_sup'
        (f := fun U => (Ch04.lambdaSqCoeffField U s (.finite 1) a)⁻¹) hU0)

theorem lowerFactorPowerIntegrableAtScale_from_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (m : ℕ) :
    Integrable
      (fun a : RegCoeffField d =>
        ((Ch04.lambdaSqCoeffField (originCube d (m : ℤ)) hP4.sLower (.finite 1) a)⁻¹) ^
          hP4.xi) P := by
  classical
  let : IsProbabilityMeasure P := hP.isProbability
  let s : ℝ := hP4.sLower
  let ξ : ℕ := hP4.xi
  let D : Finset (TriadicCube d) := descendantsAtScale (originCube d (m : ℤ)) 0
  let V : ℝ := section52SmallTailWeight s m
  let scalarization := Ch04.Internal.annealedScalarizationTheory_of_structuralLaw hP hStruct
  let base : ℝ := (scalarization.barSigmaStar 0)⁻¹
  let cSmall : ℝ :=
    Real.rpow (3 : ℝ) (-s * (m : ℝ)) ^ 2 * (D.card : ℝ) / V
  let small : RegCoeffField d → ℝ :=
    fun a => cSmall *
      ∑ U ∈ D, (Ch04.lambdaSqCoeffField U s (.finite 1) a)⁻¹
  let large : ℤ → RegCoeffField d → ℝ := fun n a =>
    if hn : n ∈ section52LargeScaleSet m then
      section52LargeScaleWeight s m n *
        (let parents := descendantsAtScale (originCube d (m : ℤ)) n
         let hparents : parents.Nonempty :=
          descendantsAtScale_nonempty (originCube d (m : ℤ))
            (section52LargeScaleSet_mem_le_m hn)
         parents.sup' hparents
          (fun Q =>
            max
              (Ch02.matrixNorm (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight -
                Ch02.matrixNorm (base • (1 : Mat d)))
              0))
    else 0
  let I : Finset (Option ℤ) := insert none ((section52LargeScaleSet m).image some)
  let G : Option ℤ → RegCoeffField d → ℝ := fun o a =>
    match o with
    | none => small a + base
    | some n => large n a
  have hξ_one : 1 ≤ ξ := by
    simpa [ξ] using Nat.succ_le_of_lt hP4.xi_pos
  have hξ_two : 2 ≤ ξ := by
    simpa [ξ] using hP4.two_le_xi
  have hs : 0 < s := by simpa [s] using hP4.sLower_pos
  have hs_nonneg : 0 ≤ s := hs.le
  have hBlock0 :
      Integrable (Ch04.coarseFullBlockMatrixAtCube (originCube d (0 : ℤ))) P :=
    hP.integrable_coarseFullBlockMatrixAtCube_origin_of_integrable_factor_observables
      hP4.sUpper_pos hP4.sLower_pos hξ_one
      hP4.upper_moment_integrable hP4.lower_inv_moment_integrable
  have hbase_nonneg : 0 ≤ base := by
    let primitive0 := Ch04.Internal.annealedPrimitiveScalarizationData_of_structuralLaw hP hStruct (0 : ℤ)
    have hBarSigmaStar0_inv_eq :
        base = Ch04.Internal.barSigmaStarInvAtScaleOfPrimitive primitive0 := by
      have hstar :
          scalarization.barSigmaStar 0 =
            (Ch04.Internal.barSigmaStarInvAtScaleOfPrimitive primitive0)⁻¹ := by
        simpa [base, scalarization, primitive0] using
          Ch04.Internal.AnnealedPrimitiveScalarizationData.barSigmaStar_eq_inv_barSigmaStarInv
            (Ch04.Internal.annealedScalarizationTheory_of_structuralLaw hP hStruct)
            (Ch04.Internal.annealedPrimitiveScalarizationData_of_structuralLaw hP hStruct (0 : ℤ))
      simp [base, hstar]
    have hStar0 :
        0 < Ch04.Internal.barSigmaStarInvAtScaleOfPrimitive primitive0 := by
      simpa [primitive0] using
        Ch04.RestrictionLawCarrier.Internal.barSigmaStarInv_pos_of_integrable_coarseFullBlockMatrixAtCube hP
          (Ch04.Internal.annealedPrimitiveScalarizationData_of_structuralLaw hP hStruct (0 : ℤ))
          hBlock0
    simpa [hBarSigmaStar0_inv_eq] using hStar0.le
  have hcSmall_nonneg : 0 ≤ cSmall := by
    have hVpos : 0 < V := by
      simpa [V, s] using section52SmallTailWeight_pos hP4.sLower_pos m
    exact div_nonneg
      (mul_nonneg (sq_nonneg _) (by exact_mod_cast Nat.zero_le D.card))
      hVpos.le
  have hsmall_nonneg : ∀ a, 0 ≤ small a := by
    intro a
    exact mul_nonneg hcSmall_nonneg
      (Finset.sum_nonneg fun U _hU =>
        inv_nonneg.mpr
          (Ch04.lambdaSqCoeffField_finite_nonneg U a hs (by norm_num : (1 : ℝ) ≤ 1)))
  have hlarge_nonneg :
      ∀ n ∈ section52LargeScaleSet m, ∀ a, 0 ≤ large n a := by
    intro n hn a
    simpa [large, s, scalarization, base, hn] using!
      lowerLargeScalePositiveExcess_nonneg_source
        hP hStruct hs_nonneg hn a
  have hG_nonneg : ∀ o ∈ I, ∀ a, 0 ≤ G o a := by
    intro o ho a
    cases o with
    | none =>
        exact add_nonneg (hsmall_nonneg a) hbase_nonneg
    | some n =>
        have hn : n ∈ section52LargeScaleSet m :=
          section52_mem_of_some_mem_insert_image_some ho
        exact hlarge_nonneg n hn a
  have hsmall_aemeas : AEMeasurable small P :=
    aemeasurable_const.mul (Finset.aemeasurable_fun_sum D fun U _ =>
      hP.aemeasurable_lambdaSqCoeffField_finite_one_inv U hs)
  have hG_aemeas : ∀ o ∈ I, AEMeasurable (G o) P := by
    intro o ho
    cases o with
    | none =>
        exact hsmall_aemeas.add aemeasurable_const
    | some n =>
        have hn : n ∈ section52LargeScaleSet m :=
          section52_mem_of_some_mem_insert_image_some ho
        simpa [G, large, s, scalarization, base, hn] using!
          lowerLargeScalePositiveExcess_aemeasurable_source
            hP hStruct (r := s) hn
  have hsmall_int : Integrable (fun a : RegCoeffField d => |small a| ^ ξ) P := by
    have hsum_int :
        Integrable
          (fun a : RegCoeffField d =>
            |∑ U ∈ D, (Ch04.lambdaSqCoeffField U s (.finite 1) a)⁻¹| ^ ξ) P :=
      section52_integrable_abs_finset_sum_pow_of_integrable_abs_pow
        (P := P) (ξ := ξ) (s := D)
        (G := fun U a => (Ch04.lambdaSqCoeffField U s (.finite 1) a)⁻¹)
        hξ_one
        (fun U _hU => hP.aemeasurable_lambdaSqCoeffField_finite_one_inv U hs)
        (fun U hU => lower_unitDescendant_lambdaInv_integrable_abs_pow
          hP hStruct hs hP4.lower_inv_moment_integrable hU)
    refine (hsum_int.const_mul (|cSmall| ^ ξ)).congr ?_
    filter_upwards with a
    simp [small, abs_mul, mul_pow]
  have hnone_int : Integrable (fun a : RegCoeffField d => |small a + base| ^ ξ) P := by
    have hξ_ne : ξ ≠ 0 := by omega
    have hsmall_mem : MemLp small (ξ : ENNReal) P := by
      rw [← MeasureTheory.integrable_norm_rpow_iff
        hsmall_aemeas.aestronglyMeasurable
        (by exact_mod_cast hξ_ne) (by simp)]
      simpa [Real.norm_eq_abs] using hsmall_int
    have hbase_mem : MemLp (fun _ : RegCoeffField d => base) (ξ : ENNReal) P :=
      memLp_const base
    have hadd := hsmall_mem.add hbase_mem
    have hint := hadd.integrable_norm_pow hξ_ne
    simpa [Real.norm_eq_abs] using hint
  have hG_int : ∀ o ∈ I, Integrable (fun a : RegCoeffField d => |G o a| ^ ξ) P := by
    intro o ho
    cases o with
    | none =>
        simpa [G] using hnone_int
    | some n =>
        have hn : n ∈ section52LargeScaleSet m :=
          section52_mem_of_some_mem_insert_image_some ho
        have hInt :=
          lowerLargeScalePositiveExcess_integrable_abs_pow_source
            hP hStruct (sSource := s) (r := s) (ξ := ξ)
            hs hξ_one hξ_two hP4.lower_inv_moment_integrable hn
        simpa [G, large, s, scalarization, base, Real.norm_eq_abs, hn] using! hInt
  let X : RegCoeffField d → ℝ :=
    fun a => (Ch04.lambdaSqCoeffField (originCube d (m : ℤ)) s (.finite 1) a)⁻¹
  have hX_aemeas : AEMeasurable X P :=
    hP.aemeasurable_lambdaSqCoeffField_finite_one_inv (originCube d (m : ℤ)) hs
  have hPoint :
      ∀ᵐ a ∂P, max (X a - 0) 0 ≤ ∑ o ∈ I, G o a := by
    filter_upwards with a
    have hsplit :=
      lambdaSqCoeffField_originCube_finite_one_inv_le_lowerSmallSqrtTail_sq_div_add_largeScale_sum
        (d := d) m hs a
    have hsmall := lowerSmallTailTerm_le_sameExponent_unitDescendantSum (d := d) m hs a
    have hlarge := lowerLargeScaleRaw_sum_le_base_add_positiveExcess_sum
      (d := d) m hs hbase_nonneg a
    have hX_nonneg : 0 ≤ X a :=
      inv_nonneg.mpr
        (Ch04.lambdaSqCoeffField_finite_nonneg (originCube d (m : ℤ)) a hs
          (by norm_num : (1 : ℝ) ≤ 1))
    have hsmall_le :
        lowerSmallSqrtTailCoeffField (d := d) m s a ^ 2 /
          section52SmallTailWeight s m ≤ small a := by
      simpa [small, cSmall, D, V, s] using hsmall
    have hlarge_sum :
        (∑ n ∈ section52LargeScaleSet m,
          section52LargeScaleWeight s m n *
            Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale
              (originCube d (m : ℤ)) n a) ≤
          base + ∑ n ∈ section52LargeScaleSet m, large n a := by
      refine section52_le_add_finsetSum_of_le_add_attachSum
        (G := fun n => large n a) hlarge le_rfl ?_
      intro n
      simp [large, n.2]
    calc
      max (X a - 0) 0 = X a := by simp [X, hX_nonneg]
      _ ≤ small a + (base + ∑ n ∈ section52LargeScaleSet m, large n a) :=
        hsplit.trans (add_le_add hsmall_le hlarge_sum)
      _ = ∑ o ∈ I, G o a := by simp [I, G, add_assoc]
  have hAbsInt :
      Integrable (fun a : RegCoeffField d => |max (X a - 0) 0| ^ ξ) P :=
    section52_integrable_abs_positiveExcess_pow_of_ae_finset_sum_bound
      (P := P) (ξ := ξ) (s := I) (X := X) (base := 0) (G := G)
      hξ_one hX_aemeas hG_nonneg hG_aemeas hG_int hPoint
  have hPowInt : Integrable (fun a : RegCoeffField d => X a ^ ξ) P := by
    refine hAbsInt.congr ?_
    filter_upwards with a
    have hX_nonneg : 0 ≤ X a :=
      inv_nonneg.mpr
        (Ch04.lambdaSqCoeffField_finite_nonneg (originCube d (m : ℤ)) a hs
          (by norm_num : (1 : ℝ) ≤ 1))
    simp [abs_of_nonneg hX_nonneg, max_eq_left hX_nonneg]
  simpa [X, s, ξ] using hPowInt

end

end Section52
end Ch05
end Book
end Homogenization
