/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section52.PositiveExcessUpper
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section52.PositiveExcessLowerAndIntegrability.LowerVariants

/-! # Pow Integrable -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section52

open MeasureTheory
open scoped Matrix.Norms.Elementwise

noncomputable section

theorem section52_integrable_abs_pow_of_ae_abs_le_nonneg
    {d : ℕ} {P : Ch04.RestrictionCoeffLaw d} {ξ : ℕ}
    {X Y : RegCoeffField d → ℝ}
    (hX_aemeas : AEMeasurable X P)
    (hY_nonneg : ∀ a, 0 ≤ Y a)
    (hXY : ∀ᵐ a ∂P, |X a| ≤ Y a)
    (hY_int : Integrable (fun a => |Y a| ^ ξ) P) :
    Integrable (fun a => |X a| ^ ξ) P := by
  refine Integrable.mono' hY_int
    ((hX_aemeas.norm.pow_const ξ).aestronglyMeasurable) ?_
  filter_upwards [hXY] with a ha
  have hpow : |X a| ^ ξ ≤ Y a ^ ξ :=
    pow_le_pow_left₀ (abs_nonneg (X a)) ha ξ
  have hleft : ‖|X a| ^ ξ‖ = |X a| ^ ξ := by
    simp [Real.norm_eq_abs]
  have hright : |Y a| ^ ξ = Y a ^ ξ := by
    rw [abs_of_nonneg (hY_nonneg a)]
  simpa [hleft, hright] using hpow

theorem section52_integrable_abs_finset_sum_pow_of_integrable_abs_pow
    {d : ℕ} {P : Ch04.RestrictionCoeffLaw d} {ι : Type*} {ξ : ℕ}
    {s : Finset ι} {G : ι → RegCoeffField d → ℝ}
    (hξ : 1 ≤ ξ)
    (hG_aemeas : ∀ i ∈ s, AEMeasurable (G i) P)
    (hG_int : ∀ i ∈ s, Integrable (fun a => |G i a| ^ ξ) P) :
    Integrable (fun a => |∑ i ∈ s, G i a| ^ ξ) P := by
  have hξ_ne : ξ ≠ 0 := by omega
  have hG_memLp :
      ∀ i ∈ s, MemLp (G i) (ξ : ENNReal) P := by
    intro i hi
    rw [← MeasureTheory.integrable_norm_rpow_iff
      (hG_aemeas i hi).aestronglyMeasurable
      (by exact_mod_cast hξ_ne) (by simp)]
    simpa [Real.norm_eq_abs] using hG_int i hi
  have hsum_memLp :
      MemLp (fun a => ∑ i ∈ s, G i a) (ξ : ENNReal) P :=
    memLp_finsetSum s hG_memLp
  simpa [Real.norm_eq_abs] using
    hsum_memLp.integrable_norm_pow
      (Nat.pos_iff_ne_zero.mp (lt_of_lt_of_le zero_lt_one hξ))

theorem section52_integrable_abs_positiveExcess_pow_of_ae_finset_sum_bound
    {d : ℕ} {P : Ch04.RestrictionCoeffLaw d} {ι : Type*} {ξ : ℕ}
    {s : Finset ι} {X : RegCoeffField d → ℝ} {base : ℝ}
    {G : ι → RegCoeffField d → ℝ}
    (hξ : 1 ≤ ξ)
    (hX_aemeas : AEMeasurable X P)
    (hG_nonneg : ∀ i ∈ s, ∀ a, 0 ≤ G i a)
    (hG_aemeas : ∀ i ∈ s, AEMeasurable (G i) P)
    (hG_int : ∀ i ∈ s, Integrable (fun a => |G i a| ^ ξ) P)
    (hPoint : ∀ᵐ a ∂P, max (X a - base) 0 ≤ ∑ i ∈ s, G i a) :
    Integrable (fun a => |max (X a - base) 0| ^ ξ) P := by
  let Y : RegCoeffField d → ℝ := fun a => ∑ i ∈ s, G i a
  have hY_nonneg : ∀ a, 0 ≤ Y a := by
    intro a
    exact Finset.sum_nonneg (fun i hi => hG_nonneg i hi a)
  have hY_int : Integrable (fun a => |Y a| ^ ξ) P := by
    simpa [Y] using
      section52_integrable_abs_finset_sum_pow_of_integrable_abs_pow
        (P := P) (ξ := ξ) (s := s) (G := G)
        hξ hG_aemeas hG_int
  have hExcess_aemeas : AEMeasurable (fun a => max (X a - base) 0) P :=
    (hX_aemeas.sub aemeasurable_const).max aemeasurable_const
  have hPoint_abs :
      ∀ᵐ a ∂P, |max (X a - base) 0| ≤ Y a := by
    filter_upwards [hPoint] with a ha
    simpa [Y, abs_of_nonneg (le_max_right (X a - base) 0)] using ha
  exact
    section52_integrable_abs_pow_of_ae_abs_le_nonneg
      (P := P) (ξ := ξ)
      (X := fun a => max (X a - base) 0) (Y := Y)
      hExcess_aemeas hY_nonneg hPoint_abs hY_int

theorem upper_unitDescendant_Lambda_integrable_abs_pow
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    {s : ℝ} {ξ m : ℕ} (hs : 0 < s)
    (hSourceInt :
      Integrable
        (fun a : RegCoeffField d =>
          (Ch04.LambdaSqCoeffField (originCube d 0) s (.finite 1) a) ^ ξ) P)
    {U : TriadicCube d}
    (hU : U ∈ descendantsAtScale (originCube d (m : ℤ)) 0) :
    Integrable
      (fun a : RegCoeffField d => |Ch04.LambdaSqCoeffField U s (.finite 1) a| ^ ξ) P := by
  classical
  let X0 : RegCoeffField d → ℝ :=
    fun a => Ch04.LambdaSqCoeffField (originCube d 0) s (.finite 1) a
  have hX0_aemeas : AEMeasurable X0 P :=
    hP.aemeasurable_LambdaSqCoeffField_finite_one (originCube d 0) hs
  have hX0_abs_int : Integrable (fun a : RegCoeffField d => |X0 a| ^ ξ) P := by
    refine hSourceInt.congr ?_
    filter_upwards with a
    rw [abs_of_nonneg]
    exact Ch04.LambdaSqCoeffField_finite_nonneg (originCube d 0) a hs
      (by norm_num : (1 : ℝ) ≤ 1)
  have hscale : U.scale = 0 := scale_eq_of_mem_descendantsAtScale hU
  let z : Fin d → ℤ := Book.Ch04.scaleTranslationShift 0 U
  have hUeq : U = translateCube z (originCube d 0) := by
    simpa [z] using (translateCube_originCube_zero_eq_of_scale_zero U hscale).symm
  have hae :
      (fun a : RegCoeffField d => Ch04.LambdaSqCoeffField U s (.finite 1) a) =ᵐ[P]
        fun a => X0 (translateReg (intVecToRealVec z) a) := by
    have hcov :=
      Ch04.LambdaSqCoeffField_originCube_zero_translateByInt_ae
        hP hStruct.stationary z s (.finite 1)
    simpa [X0, hUeq] using hcov
  have hmap :
      Measure.map (fun a : RegCoeffField d => Ch04.LambdaSqCoeffField U s (.finite 1) a) P =
        Measure.map X0 P := by
    calc
      Measure.map (fun a : RegCoeffField d => Ch04.LambdaSqCoeffField U s (.finite 1) a) P =
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
    (hP.aemeasurable_LambdaSqCoeffField_finite_one U hs) hX0_aemeas hmap hX0_abs_int

/-- Membership of a `some` index in a finite family with an extra `none`
entry is membership of the original index in the original family. -/
theorem section52_mem_of_some_mem_insert_image_some
    {ι : Type*} [DecidableEq ι] {s : Finset ι} {i : ι}
    (hi : some i ∈ insert none (s.image some)) :
    i ∈ s := by
  classical
  have hsome : some i ∈ s.image some := by
    rcases Finset.mem_insert.mp hi with hnone | hsome
    · cases hnone
    · exact hsome
  rcases Finset.mem_image.mp hsome with ⟨j, hj, hji⟩
  exact (Option.some.inj hji) ▸ hj

/-- An attached-sum upper bound transfers to the corresponding ordinary finite
sum while replacing its initial summand by a larger one. -/
theorem section52_le_add_finsetSum_of_le_add_attachSum
    {ι : Type*} {s : Finset ι} {F : {i // i ∈ s} → ℝ} {G : ι → ℝ}
    {x a b : ℝ}
    (hsplit : x ≤ a + ∑ i ∈ s.attach, F i)
    (hsmall : a ≤ b) (hFG : ∀ i, F i = G i.1) :
    x ≤ b + ∑ i ∈ s, G i := by
  have hsum : ∑ i ∈ s.attach, F i = ∑ i ∈ s, G i := by
    calc
      ∑ i ∈ s.attach, F i = ∑ i ∈ s.attach, G i.1 :=
        Finset.sum_congr rfl (fun i _ => hFG i)
      _ = ∑ i ∈ s, G i := Finset.sum_attach s G
  calc
    x ≤ b + ∑ i ∈ s.attach, F i := hsplit.trans (add_le_add_right hsmall _)
    _ = b + ∑ i ∈ s, G i := congrArg (b + ·) hsum

theorem upperFactorPowerIntegrableAtScale_from_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (m : ℕ) :
    Integrable
      (fun a : RegCoeffField d =>
        (Ch04.LambdaSqCoeffField (originCube d (m : ℤ)) hP4.sUpper (.finite 1) a) ^
          hP4.xi) P := by
  classical
  let : IsProbabilityMeasure P := hP.isProbability
  let s : ℝ := hP4.sUpper
  let ξ : ℕ := hP4.xi
  let D : Finset (TriadicCube d) := descendantsAtScale (originCube d (m : ℤ)) 0
  let V : ℝ := section52SmallTailWeight s m
  let scalarization := Ch04.Internal.annealedScalarizationTheory_of_structuralLaw hP hStruct
  let base : ℝ := scalarization.barSigma 0
  let cSmall : ℝ :=
    Real.rpow (3 : ℝ) (-s * (m : ℝ)) ^ 2 * (D.card : ℝ) / V
  let small : RegCoeffField d → ℝ :=
    fun a => cSmall *
      ∑ U ∈ D, Ch04.LambdaSqCoeffField U s (.finite 1) a
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
              (Ch02.matrixNorm (coarseBlockMatrix (cubeSet Q) a.toFun).upperLeft -
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
  have hs : 0 < s := by simpa [s] using hP4.sUpper_pos
  have hs_nonneg : 0 ≤ s := hs.le
  have hBlock0 :
      Integrable (Ch04.coarseFullBlockMatrixAtCube (originCube d (0 : ℤ))) P :=
    hP.integrable_coarseFullBlockMatrixAtCube_origin_of_integrable_factor_observables
      hP4.sUpper_pos hP4.sLower_pos hξ_one
      hP4.upper_moment_integrable hP4.lower_inv_moment_integrable
  have hbase_nonneg : 0 ≤ base := by
    let primitive0 := Ch04.Internal.annealedPrimitiveScalarizationData_of_structuralLaw hP hStruct (0 : ℤ)
    have hBarSigma0_eq :
        base = Ch04.Internal.barBAtScaleOfPrimitive primitive0 := by
      simpa [base, scalarization, primitive0] using
        Ch04.Internal.AnnealedPrimitiveScalarizationData.barSigma_eq_barB
          (Ch04.Internal.annealedScalarizationTheory_of_structuralLaw hP hStruct)
          (Ch04.Internal.annealedPrimitiveScalarizationData_of_structuralLaw hP hStruct (0 : ℤ))
    have hB0 :
        0 ≤ Ch04.Internal.barBAtScaleOfPrimitive primitive0 := by
      simpa [primitive0] using
        Ch04.RestrictionLawCarrier.Internal.barB_nonneg_of_integrable_coarseFullBlockMatrixAtCube hP
          (Ch04.Internal.annealedPrimitiveScalarizationData_of_structuralLaw hP hStruct (0 : ℤ))
          hBlock0
    simpa [hBarSigma0_eq] using hB0
  have hcSmall_nonneg : 0 ≤ cSmall := by
    have hVpos : 0 < V := by
      simpa [V, s] using section52SmallTailWeight_pos hP4.sUpper_pos m
    exact div_nonneg
      (mul_nonneg (sq_nonneg _) (by exact_mod_cast Nat.zero_le D.card))
      hVpos.le
  have hsmall_nonneg : ∀ a, 0 ≤ small a := by
    intro a
    exact mul_nonneg hcSmall_nonneg
      (Finset.sum_nonneg fun U _hU =>
        Ch04.LambdaSqCoeffField_finite_nonneg U a hs (by norm_num : (1 : ℝ) ≤ 1))
  have hlarge_nonneg :
      ∀ n ∈ section52LargeScaleSet m, ∀ a, 0 ≤ large n a := by
    intro n hn a
    simpa [large, s, scalarization, base, hn] using!
      upperLargeScalePositiveExcess_nonneg_source
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
      hP.aemeasurable_LambdaSqCoeffField_finite_one U hs)
  have hG_aemeas : ∀ o ∈ I, AEMeasurable (G o) P := by
    intro o ho
    cases o with
    | none =>
        exact hsmall_aemeas.add aemeasurable_const
    | some n =>
        have hn : n ∈ section52LargeScaleSet m :=
          section52_mem_of_some_mem_insert_image_some ho
        simpa [G, large, s, scalarization, base, hn] using!
          upperLargeScalePositiveExcess_aemeasurable_source
            hP hStruct (r := s) hn
  have hsmall_int : Integrable (fun a : RegCoeffField d => |small a| ^ ξ) P := by
    have hunit_int :
        ∀ U ∈ D,
          Integrable
            (fun a : RegCoeffField d =>
              |Ch04.LambdaSqCoeffField U s (.finite 1) a| ^ ξ) P := by
      intro U hU
      exact upper_unitDescendant_Lambda_integrable_abs_pow
        hP hStruct hs hP4.upper_moment_integrable hU
    have hsum_int :
        Integrable
          (fun a : RegCoeffField d =>
            |∑ U ∈ D, Ch04.LambdaSqCoeffField U s (.finite 1) a| ^ ξ) P :=
      section52_integrable_abs_finset_sum_pow_of_integrable_abs_pow
        (P := P) (ξ := ξ) (s := D)
        (G := fun U a => Ch04.LambdaSqCoeffField U s (.finite 1) a)
        hξ_one
        (fun U _hU => hP.aemeasurable_LambdaSqCoeffField_finite_one U hs)
        hunit_int
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
          upperLargeScalePositiveExcess_integrable_abs_pow_source
            hP hStruct (sSource := s) (r := s) (ξ := ξ)
            hs hξ_one hξ_two hP4.upper_moment_integrable hn
        simpa [G, large, s, scalarization, base, Real.norm_eq_abs, hn] using! hInt
  let X : RegCoeffField d → ℝ :=
    fun a => Ch04.LambdaSqCoeffField (originCube d (m : ℤ)) s (.finite 1) a
  have hX_aemeas : AEMeasurable X P :=
    hP.aemeasurable_LambdaSqCoeffField_finite_one (originCube d (m : ℤ)) hs
  have hPoint :
      ∀ᵐ a ∂P, max (X a - 0) 0 ≤ ∑ o ∈ I, G o a := by
    filter_upwards with a
    have hsplit :=
      LambdaSqCoeffField_originCube_finite_one_le_upperSmallSqrtTail_sq_div_add_largeScale_sum
        (d := d) m hs a
    have hsmall := upperSmallTailTerm_le_sameExponent_unitDescendantSum (d := d) m hs a
    have hlarge := upperLargeScaleRaw_sum_le_base_add_positiveExcess_sum
      (d := d) m hs hbase_nonneg a
    have hX_nonneg : 0 ≤ X a :=
      Ch04.LambdaSqCoeffField_finite_nonneg (originCube d (m : ℤ)) a hs
        (by norm_num : (1 : ℝ) ≤ 1)
    have hsmall_le :
        upperSmallSqrtTailCoeffField (d := d) m s a ^ 2 /
          section52SmallTailWeight s m ≤ small a := by
      simpa [small, cSmall, D, V, s] using hsmall
    have hlarge_sum :
        (∑ n ∈ section52LargeScaleSet m,
          section52LargeScaleWeight s m n *
            Ch04.maxDescendantBMatrixNormCoeffFieldAtScale
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
      Ch04.LambdaSqCoeffField_finite_nonneg (originCube d (m : ℤ)) a hs
        (by norm_num : (1 : ℝ) ≤ 1)
    simp [abs_of_nonneg hX_nonneg, max_eq_left hX_nonneg]
  simpa [X, s, ξ] using hPowInt

end

end Section52
end Ch05
end Book
end Homogenization
