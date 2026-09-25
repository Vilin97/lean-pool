/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section52.P4Integrability

/-! # Moment Bounds -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section52

open MeasureTheory
open scoped Matrix.Norms.Elementwise

noncomputable section
/-!
# Section 5.2 internals: MomentBounds

Final positive-excess and multiscale ellipticity moment bounds.
-/

private theorem section52_mem_of_some_mem_insert_image_some
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

private theorem section52_sum_insert_image_some
    {ι α : Type*} [DecidableEq ι] [AddCommMonoid α]
    (s : Finset ι) (x0 : α) (f : ι → α) :
    (∑ o ∈ insert none (s.image some),
        match o with
        | none => x0
        | some i => f i) =
      x0 + ∑ i ∈ s, f i := by
  classical
  simp

private theorem section52_sum_insert_image_some_apply
    {ι α β : Type*} [DecidableEq ι] [AddCommMonoid β]
    (s : Finset ι) (x0 : α → β) (f : ι → α → β) (a : α) :
    (∑ o ∈ insert none (s.image some),
        (match o with
        | none => x0
        | some i => f i) a) =
      x0 a + ∑ i ∈ s, f i a := by
  classical
  simp

theorem section52_annealedMomentRoot_positiveExcess_le_finset_sum
    {d : ℕ} {P : Ch04.RestrictionCoeffLaw d} {ι : Type*} {ξ : ℕ}
    {s : Finset ι} {X : RegCoeffField d → ℝ} {base : ℝ}
    {G : ι → RegCoeffField d → ℝ}
    (hξ : 1 ≤ ξ)
    (hG_nonneg : ∀ i ∈ s, ∀ a, 0 ≤ G i a)
    (hG_aemeas : ∀ i ∈ s, AEMeasurable (G i) P)
    (hG_int : ∀ i ∈ s, Integrable (fun a => |G i a| ^ ξ) P)
    (hExcess_int :
      Integrable (fun a => |max (X a - base) 0| ^ ξ) P)
    (hPoint : ∀ᵐ a ∂P, max (X a - base) 0 ≤ ∑ i ∈ s, G i a) :
    Ch04.annealedMomentRoot P ξ (fun a => max (X a - base) 0) ≤
      ∑ i ∈ s, Ch04.annealedMomentRoot P ξ (G i) := by
  let Y : RegCoeffField d → ℝ := fun a => ∑ i ∈ s, G i a
  have hY_nonneg : ∀ a, 0 ≤ Y a := by
    intro a
    exact Finset.sum_nonneg (fun i hi => hG_nonneg i hi a)
  have hY_abs_int : Integrable (fun a => |Y a| ^ ξ) P := by
    simpa [Y] using
      section52_integrable_abs_finset_sum_pow_of_integrable_abs_pow
        (P := P) (ξ := ξ) (s := s) (G := G)
        hξ hG_aemeas hG_int
  have hY_int : Integrable (fun a => Y a ^ ξ) P := by
    refine hY_abs_int.congr ?_
    filter_upwards with a
    simp [abs_of_nonneg (hY_nonneg a)]
  have hPointY : (fun a => max (X a - base) 0) ≤ᵐ[P] Y := by
    filter_upwards [hPoint] with a ha
    simpa [Y] using ha
  have hExcess_pow_int :
      Integrable (fun a => (max (X a - base) 0) ^ ξ) P := by
    refine hExcess_int.congr ?_
    filter_upwards with a
    simp [abs_of_nonneg (le_max_right (X a - base) 0)]
  have hmono :
      Ch04.annealedMomentRoot P ξ (fun a => max (X a - base) 0) ≤
        Ch04.annealedMomentRoot P ξ Y :=
    Ch04.annealedMomentRoot_le_of_ae_nonneg_le
      (P := P) (ξ := ξ)
      (X := fun a => max (X a - base) 0) (Y := Y)
      hξ
      (fun a => le_max_right (X a - base) 0)
      hExcess_pow_int hY_int hPointY
  have htriangle :
      Ch04.annealedMomentRoot P ξ Y ≤
        ∑ i ∈ s, Ch04.annealedMomentRoot P ξ (G i) := by
    have hsum :=
      integral_abs_finsetSum_pow_rpow_inv_le_sum_aemeasurable
        (μ := P) (s := s) (p := ξ) hξ hG_aemeas hG_int
    calc
      Ch04.annealedMomentRoot P ξ Y =
          (∫ a, |∑ i ∈ s, G i a| ^ ξ ∂P) ^ (1 / (ξ : ℝ)) := by
            unfold Ch04.annealedMomentRoot
            congr 1
            exact integral_congr_ae
              (Filter.Eventually.of_forall fun a => by
                simp [Y, abs_of_nonneg (hY_nonneg a)])
      _ ≤ ∑ i ∈ s, (∫ a, |G i a| ^ ξ ∂P) ^ (1 / (ξ : ℝ)) := hsum
      _ = ∑ i ∈ s, Ch04.annealedMomentRoot P ξ (G i) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            unfold Ch04.annealedMomentRoot
            congr 1
            exact integral_congr_ae
              (Filter.Eventually.of_forall fun a => by
                simp [abs_of_nonneg (hG_nonneg i hi a)])
  exact hmono.trans htriangle

theorem section52_annealedMomentRoot_positiveExcess_le_scaled_initial
    {d : ℕ} {P : Ch04.RestrictionCoeffLaw d} {ι : Type*} {ξ : ℕ}
    {s : Finset ι} {X : RegCoeffField d → ℝ} {base initial finalCoeff : ℝ}
    {G : ι → RegCoeffField d → ℝ} {coeff : ι → ℝ}
    (hξ : 1 ≤ ξ)
    (hInitial_nonneg : 0 ≤ initial)
    (hG_nonneg : ∀ i ∈ s, ∀ a, 0 ≤ G i a)
    (hG_aemeas : ∀ i ∈ s, AEMeasurable (G i) P)
    (hG_int : ∀ i ∈ s, Integrable (fun a => |G i a| ^ ξ) P)
    (hExcess_int :
      Integrable (fun a => |max (X a - base) 0| ^ ξ) P)
    (hPoint : ∀ᵐ a ∂P, max (X a - base) 0 ≤ ∑ i ∈ s, G i a)
    (hRoot : ∀ i ∈ s, Ch04.annealedMomentRoot P ξ (G i) ≤ coeff i * initial)
    (hCoeffSum : ∑ i ∈ s, coeff i ≤ finalCoeff) :
    Ch04.annealedMomentRoot P ξ (fun a => max (X a - base) 0) ≤
      finalCoeff * initial := by
  calc
    Ch04.annealedMomentRoot P ξ (fun a => max (X a - base) 0)
        ≤ ∑ i ∈ s, Ch04.annealedMomentRoot P ξ (G i) :=
          section52_annealedMomentRoot_positiveExcess_le_finset_sum
            (P := P) (ξ := ξ) (s := s) (X := X) (base := base) (G := G)
            hξ hG_nonneg hG_aemeas hG_int hExcess_int hPoint
    _ ≤ ∑ i ∈ s, coeff i * initial :=
          Finset.sum_le_sum hRoot
    _ = (∑ i ∈ s, coeff i) * initial := by
          rw [Finset.sum_mul]
    _ ≤ finalCoeff * initial :=
          mul_le_mul_of_nonneg_right hCoeffSum hInitial_nonneg

theorem section52_integrable_positiveExcess_pow_of_one_add_finset_bound
    {d : ℕ} {P : Ch04.RestrictionCoeffLaw d} {ι : Type*} [DecidableEq ι] {ξ : ℕ}
    {s : Finset ι} {X : RegCoeffField d → ℝ} {base : ℝ}
    {G0 : RegCoeffField d → ℝ} {G : ι → RegCoeffField d → ℝ}
    (hξ : 1 ≤ ξ)
    (hG0_nonneg : ∀ a, 0 ≤ G0 a)
    (hG_nonneg : ∀ i ∈ s, ∀ a, 0 ≤ G i a)
    (hG0_aemeas : AEMeasurable G0 P)
    (hG_aemeas : ∀ i ∈ s, AEMeasurable (G i) P)
    (hG0_int : Integrable (fun a => |G0 a| ^ ξ) P)
    (hG_int : ∀ i ∈ s, Integrable (fun a => |G i a| ^ ξ) P)
    (hX_aemeas : AEMeasurable X P)
    (hPoint : ∀ᵐ a ∂P, max (X a - base) 0 ≤ G0 a + ∑ i ∈ s, G i a) :
    Integrable (fun a => (max (X a - base) 0) ^ ξ) P := by
  classical
  let I : Finset (Option ι) := insert none (s.image some)
  let H : Option ι → RegCoeffField d → ℝ := fun o =>
    match o with
    | none => G0
    | some i => G i
  have hH_nonneg : ∀ o ∈ I, ∀ a, 0 ≤ H o a := by
    intro o ho a
    cases o with
    | none =>
        exact hG0_nonneg a
    | some i =>
        have hi : i ∈ s := by
          exact section52_mem_of_some_mem_insert_image_some (s := s) ho
        exact hG_nonneg i hi a
  have hH_aemeas : ∀ o ∈ I, AEMeasurable (H o) P := by
    intro o ho
    cases o with
    | none =>
        exact hG0_aemeas
    | some i =>
        have hi : i ∈ s := by
          exact section52_mem_of_some_mem_insert_image_some (s := s) ho
        exact hG_aemeas i hi
  have hH_int : ∀ o ∈ I, Integrable (fun a => |H o a| ^ ξ) P := by
    intro o ho
    cases o with
    | none =>
        exact hG0_int
    | some i =>
        have hi : i ∈ s := by
          exact section52_mem_of_some_mem_insert_image_some (s := s) ho
        exact hG_int i hi
  have hPointI :
      ∀ᵐ a ∂P, max (X a - base) 0 ≤ ∑ o ∈ I, H o a := by
    filter_upwards [hPoint] with a ha
    calc
      max (X a - base) 0 ≤ G0 a + ∑ i ∈ s, G i a := ha
      _ = ∑ o ∈ I, H o a := by
          dsimp [I, H]
          exact (section52_sum_insert_image_some_apply (s := s) (x0 := G0)
            (f := G) a).symm
  have hAbsInt :
      Integrable (fun a => |max (X a - base) 0| ^ ξ) P :=
    section52_integrable_abs_positiveExcess_pow_of_ae_finset_sum_bound
      (P := P) (ξ := ξ) (s := I) (X := X) (base := base) (G := H)
      hξ hX_aemeas hH_nonneg hH_aemeas hH_int hPointI
  refine hAbsInt.congr ?_
  filter_upwards with a
  simp [abs_of_nonneg (le_max_right (X a - base) 0)]

theorem section52_annealedMomentRoot_positiveExcess_le_one_add_finset_scaled
    {d : ℕ} {P : Ch04.RestrictionCoeffLaw d} {ι : Type*} [DecidableEq ι] {ξ : ℕ}
    {s : Finset ι} {X : RegCoeffField d → ℝ} {base initial finalCoeff coeff0 : ℝ}
    {G0 : RegCoeffField d → ℝ} {G : ι → RegCoeffField d → ℝ} {coeff : ι → ℝ}
    (hξ : 1 ≤ ξ)
    (hInitial_nonneg : 0 ≤ initial)
    (hG0_nonneg : ∀ a, 0 ≤ G0 a)
    (hG_nonneg : ∀ i ∈ s, ∀ a, 0 ≤ G i a)
    (hG0_aemeas : AEMeasurable G0 P)
    (hG_aemeas : ∀ i ∈ s, AEMeasurable (G i) P)
    (hG0_int : Integrable (fun a => |G0 a| ^ ξ) P)
    (hG_int : ∀ i ∈ s, Integrable (fun a => |G i a| ^ ξ) P)
    (hX_aemeas : AEMeasurable X P)
    (hPoint : ∀ᵐ a ∂P, max (X a - base) 0 ≤ G0 a + ∑ i ∈ s, G i a)
    (hRoot0 : Ch04.annealedMomentRoot P ξ G0 ≤ coeff0 * initial)
    (hRoot : ∀ i ∈ s, Ch04.annealedMomentRoot P ξ (G i) ≤ coeff i * initial)
    (hCoeffSum : coeff0 + ∑ i ∈ s, coeff i ≤ finalCoeff) :
    Ch04.annealedMomentRoot P ξ (fun a => max (X a - base) 0) ≤
      finalCoeff * initial := by
  classical
  let I : Finset (Option ι) := insert none (s.image some)
  let H : Option ι → RegCoeffField d → ℝ := fun o =>
    match o with
    | none => G0
    | some i => G i
  let C : Option ι → ℝ := fun o =>
    match o with
    | none => coeff0
    | some i => coeff i
  have hH_nonneg : ∀ o ∈ I, ∀ a, 0 ≤ H o a := by
    intro o ho a
    cases o with
    | none =>
        exact hG0_nonneg a
    | some i =>
        have hi : i ∈ s := by
          exact section52_mem_of_some_mem_insert_image_some (s := s) ho
        exact hG_nonneg i hi a
  have hH_aemeas : ∀ o ∈ I, AEMeasurable (H o) P := by
    intro o ho
    cases o with
    | none =>
        exact hG0_aemeas
    | some i =>
        have hi : i ∈ s := by
          exact section52_mem_of_some_mem_insert_image_some (s := s) ho
        exact hG_aemeas i hi
  have hH_int : ∀ o ∈ I, Integrable (fun a => |H o a| ^ ξ) P := by
    intro o ho
    cases o with
    | none =>
        exact hG0_int
    | some i =>
        have hi : i ∈ s := by
          exact section52_mem_of_some_mem_insert_image_some (s := s) ho
        exact hG_int i hi
  have hPointI :
      ∀ᵐ a ∂P, max (X a - base) 0 ≤ ∑ o ∈ I, H o a := by
    filter_upwards [hPoint] with a ha
    calc
      max (X a - base) 0 ≤ G0 a + ∑ i ∈ s, G i a := ha
      _ = ∑ o ∈ I, H o a := by
          dsimp [I, H]
          exact (section52_sum_insert_image_some_apply (s := s) (x0 := G0)
            (f := G) a).symm
  have hRootI :
      ∀ o ∈ I, Ch04.annealedMomentRoot P ξ (H o) ≤ C o * initial := by
    intro o ho
    cases o with
    | none =>
        exact hRoot0
    | some i =>
        have hi : i ∈ s := by
          exact section52_mem_of_some_mem_insert_image_some (s := s) ho
        exact hRoot i hi
  have hCoeffI : ∑ o ∈ I, C o ≤ finalCoeff := by
    calc
      ∑ o ∈ I, C o = coeff0 + ∑ i ∈ s, coeff i := by
        dsimp [I, C]
        exact section52_sum_insert_image_some (s := s) (x0 := coeff0) (f := coeff)
      _ ≤ finalCoeff := hCoeffSum
  have hExcess_int :
      Integrable (fun a => |max (X a - base) 0| ^ ξ) P :=
    section52_integrable_abs_positiveExcess_pow_of_ae_finset_sum_bound
      (P := P) (ξ := ξ) (s := I) (X := X) (base := base) (G := H)
      hξ hX_aemeas hH_nonneg hH_aemeas hH_int hPointI
  exact
    section52_annealedMomentRoot_positiveExcess_le_scaled_initial
      (P := P) (ξ := ξ) (s := I) (X := X) (base := base)
      (initial := initial) (finalCoeff := finalCoeff) (G := H) (coeff := C)
      hξ hInitial_nonneg hH_nonneg hH_aemeas hH_int hExcess_int
      hPointI hRootI hCoeffI

theorem upperPositiveExcessMomentAtScale_integrable_and_le_raw_twoExponentCoeff
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    {s r : ℝ} {ξ m : ℕ}
    (hs : 0 < s) (hsr : s < r) (hr_lt_one : r < 1)
    (hξ_one : 1 ≤ ξ) (hξ_two : 2 ≤ ξ)
    (hBlock0 :
      Integrable (Ch04.coarseFullBlockMatrixAtCube (originCube d (0 : ℤ))) P)
    (hUpperSourceInt :
      Integrable
        (fun a : RegCoeffField d =>
          (Ch04.LambdaSqCoeffField (originCube d 0) s (.finite 1) a) ^ ξ) P) :
    let D := descendantsAtScale (originCube d (m : ℤ)) 0
    Integrable
        (fun a : RegCoeffField d =>
          (max
            (Ch04.LambdaSqCoeffField (originCube d (m : ℤ)) r (.finite 1) a -
              hP.barSigmaAtScale hStruct 0)
            0) ^ ξ) P ∧
      LambdaPositiveExcessMomentAtScale P (m : ℤ) r ξ
          hP hStruct ≤
        ((((25 * s⁻¹ * (r - s)⁻¹ *
              Real.rpow (3 : ℝ) (-r * (m : ℝ))) ^ 2 /
            section52SmallTailWeight r m) *
            (D.card : ℝ) ^ (1 / (ξ : ℝ))) +
          ((Fintype.card (Fin d) : ℝ) * (Fintype.card (Fin d) : ℝ)) *
            (∑ n ∈ section52LargeScaleSet m,
              section52LargeScaleRootCoeff d ξ r m n)) *
          Ch04.LambdaMomentAtScale P 0 s ξ := by
  classical
  intro D
  let hD : D.Nonempty :=
    descendantsAtScale_nonempty (originCube d (m : ℤ)) (by simp [originCube])
  let : IsProbabilityMeasure P := hP.isProbability
  let scalarization := Ch04.Internal.annealedScalarizationTheory_of_structuralLaw hP hStruct
  let initial : ℝ := Ch04.LambdaMomentAtScale P 0 s ξ
  let c0 : ℝ :=
    (25 * s⁻¹ * (r - s)⁻¹ *
        Real.rpow (3 : ℝ) (-r * (m : ℝ))) ^ 2 /
      section52SmallTailWeight r m
  let S : RegCoeffField d → ℝ :=
    fun a => D.sup' hD (fun U => Ch04.LambdaSqCoeffField U s (.finite 1) a)
  let G0 : RegCoeffField d → ℝ := fun a => c0 * S a
  let G : ℤ → RegCoeffField d → ℝ := fun n a =>
    if hn : n ∈ section52LargeScaleSet m then
      section52LargeScaleWeight r m n *
        (let parents := descendantsAtScale (originCube d (m : ℤ)) n
         let hparents : parents.Nonempty :=
          descendantsAtScale_nonempty (originCube d (m : ℤ))
            (section52LargeScaleSet_mem_le_m hn)
         parents.sup' hparents
          (fun Q =>
            max
              (Ch02.matrixNorm (coarseBlockMatrix (cubeSet Q) a.toFun).upperLeft -
                Ch02.matrixNorm
                  (scalarization.barSigma 0 • (1 : Mat d)))
              0))
    else 0
  let coeff0 : ℝ := c0 * (D.card : ℝ) ^ (1 / (ξ : ℝ))
  let coeff : ℤ → ℝ := fun n =>
    ((Fintype.card (Fin d) : ℝ) * (Fintype.card (Fin d) : ℝ)) *
      section52LargeScaleRootCoeff d ξ r m n
  have hr_pos : 0 < r := hs.trans hsr
  have hr_nonneg : 0 ≤ r := hr_pos.le
  have hgap_pos : 0 < r - s := sub_pos.mpr hsr
  have hVpos : 0 < section52SmallTailWeight r m :=
    section52SmallTailWeight_pos hr_pos m
  have hc0_nonneg : 0 ≤ c0 := by
    dsimp [c0]
    exact div_nonneg (sq_nonneg _) hVpos.le
  have hInitial_nonneg : 0 ≤ initial := by
    exact Ch04.LambdaMomentAtScale_nonneg P 0 ξ hs
  have hbase_nonneg : 0 ≤ scalarization.barSigma 0 := by
    let primitive0 := Ch04.Internal.annealedPrimitiveScalarizationData_of_structuralLaw hP hStruct (0 : ℤ)
    have hBarSigma0_eq :
        scalarization.barSigma 0 =
          Ch04.Internal.barBAtScaleOfPrimitive primitive0 := by
      simpa [scalarization, primitive0] using
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
  have hS_nonneg : ∀ a, 0 ≤ S a := by
    intro a
    exact upper_unitDescendantSup_nonneg (d := d) (s := s) (m := m) hs a
  have hG0_nonneg : ∀ a, 0 ≤ G0 a := by
    intro a
    exact mul_nonneg hc0_nonneg (hS_nonneg a)
  have hG_nonneg :
      ∀ n ∈ section52LargeScaleSet m, ∀ a, 0 ≤ G n a := by
    intro n hn a
    simpa only [G, scalarization, hn, dif_pos] using!
      upperLargeScalePositiveExcess_nonneg_source
        hP hStruct hr_nonneg hn a
  have hS_aemeas : AEMeasurable S P := by
    exact upper_unitDescendantSup_aemeasurable
      (d := d) (P := P) hP (s := s) (m := m) hs
  have hG0_aemeas : AEMeasurable G0 P := by
    exact aemeasurable_const.mul hS_aemeas
  have hG_aemeas :
      ∀ n ∈ section52LargeScaleSet m, AEMeasurable (G n) P := by
    intro n hn
    simpa only [G, scalarization, hn, dif_pos] using!
      upperLargeScalePositiveExcess_aemeasurable_source
        hP hStruct (r := r) hn
  have hS_int : Integrable (fun a : RegCoeffField d => |S a| ^ ξ) P := by
    exact upper_unitDescendantSup_integrable_abs_pow
      (d := d) (P := P) hP hStruct (s := s) (ξ := ξ) (m := m)
      hs hξ_one hUpperSourceInt
  have hG0_int : Integrable (fun a : RegCoeffField d => |G0 a| ^ ξ) P := by
    refine (hS_int.const_mul (|c0| ^ ξ)).congr ?_
    filter_upwards with a
    simp only [G0, abs_mul, mul_pow]
  have hG_int :
      ∀ n ∈ section52LargeScaleSet m,
        Integrable (fun a : RegCoeffField d => |G n a| ^ ξ) P := by
    intro n hn
    have hInt :=
      upperLargeScalePositiveExcess_integrable_abs_pow_source
        hP hStruct (sSource := s) (r := r) (ξ := ξ)
        hs hξ_one hξ_two hUpperSourceInt hn
    simpa only [G, scalarization, Real.norm_eq_abs, hn, dif_pos] using! hInt
  have hX_aemeas :
      AEMeasurable
        (fun a : RegCoeffField d =>
          Ch04.LambdaSqCoeffField (originCube d (m : ℤ)) r (.finite 1) a) P :=
    hP.aemeasurable_LambdaSqCoeffField_finite_one (originCube d (m : ℤ)) hr_pos
  have hPoint :
      ∀ᵐ a ∂P,
        max
          (Ch04.LambdaSqCoeffField (originCube d (m : ℤ)) r (.finite 1) a -
            scalarization.barSigma 0)
          0 ≤ G0 a + ∑ n ∈ section52LargeScaleSet m, G n a := by
    filter_upwards with a
    have hsplit :=
      upperPositiveExcess_pointwise_le_smallTail_add_largeScalePositiveExcess
        (d := d) m (s := r) (base := scalarization.barSigma 0)
        hr_pos hbase_nonneg a
    have hsmall :=
      upperSmallTailTerm_le_raw_unitDescendantSup
        (d := d) m (s := s) (r := r) hs hsr hr_lt_one a
    calc
      max
          (Ch04.LambdaSqCoeffField (originCube d (m : ℤ)) r (.finite 1) a -
            scalarization.barSigma 0)
          0 ≤
        upperSmallSqrtTailCoeffField (d := d) m r a ^ 2 /
            section52SmallTailWeight r m +
          ((section52LargeScaleSet m).attach.sum fun n =>
            section52LargeScaleWeight r m n.1 *
              (let parents := descendantsAtScale (originCube d (m : ℤ)) n.1
               let hparents : parents.Nonempty :=
                descendantsAtScale_nonempty (originCube d (m : ℤ))
                  (section52LargeScaleSet_mem_le_m n.2)
               parents.sup' hparents
                (fun Q =>
                  max
                    (Ch02.matrixNorm (coarseBlockMatrix (cubeSet Q) a.toFun).upperLeft -
                      Ch02.matrixNorm (scalarization.barSigma 0 • (1 : Mat d)))
                    0))) := by
              exact hsplit
      _ ≤ G0 a +
          ((section52LargeScaleSet m).attach.sum fun n =>
            section52LargeScaleWeight r m n.1 *
              (let parents := descendantsAtScale (originCube d (m : ℤ)) n.1
               let hparents : parents.Nonempty :=
                descendantsAtScale_nonempty (originCube d (m : ℤ))
                  (section52LargeScaleSet_mem_le_m n.2)
               parents.sup' hparents
                (fun Q =>
                  max
                    (Ch02.matrixNorm (coarseBlockMatrix (cubeSet Q) a.toFun).upperLeft -
                      Ch02.matrixNorm (scalarization.barSigma 0 • (1 : Mat d)))
                    0))) := by
              exact
                add_le_add_left hsmall
                  (((section52LargeScaleSet m).attach.sum fun n =>
                    section52LargeScaleWeight r m n.1 *
                      (let parents := descendantsAtScale (originCube d (m : ℤ)) n.1
                       let hparents : parents.Nonempty :=
                        descendantsAtScale_nonempty (originCube d (m : ℤ))
                          (section52LargeScaleSet_mem_le_m n.2)
                       parents.sup' hparents
                        (fun Q =>
                          max
                            (Ch02.matrixNorm (coarseBlockMatrix (cubeSet Q) a.toFun).upperLeft -
                              Ch02.matrixNorm (scalarization.barSigma 0 • (1 : Mat d)))
                            0))))
      _ = G0 a + ∑ n ∈ section52LargeScaleSet m, G n a := by
              have hsum_eq :
                  ((section52LargeScaleSet m).attach.sum fun n =>
                    section52LargeScaleWeight r m n.1 *
                      (let parents := descendantsAtScale (originCube d (m : ℤ)) n.1
                       let hparents : parents.Nonempty :=
                        descendantsAtScale_nonempty (originCube d (m : ℤ))
                          (section52LargeScaleSet_mem_le_m n.2)
                       parents.sup' hparents
                        (fun Q =>
                          max
                            (Ch02.matrixNorm (coarseBlockMatrix (cubeSet Q) a.toFun).upperLeft -
                              Ch02.matrixNorm (scalarization.barSigma 0 • (1 : Mat d)))
                            0))) =
                    ∑ n ∈ section52LargeScaleSet m, G n a := by
                have hattach :
                    ((section52LargeScaleSet m).attach.sum fun n =>
                      section52LargeScaleWeight r m n.1 *
                        (let parents := descendantsAtScale (originCube d (m : ℤ)) n.1
                         let hparents : parents.Nonempty :=
                          descendantsAtScale_nonempty (originCube d (m : ℤ))
                            (section52LargeScaleSet_mem_le_m n.2)
                         parents.sup' hparents
                          (fun Q =>
                            max
                              (Ch02.matrixNorm (coarseBlockMatrix (cubeSet Q) a.toFun).upperLeft -
                                Ch02.matrixNorm (scalarization.barSigma 0 • (1 : Mat d)))
                              0))) =
                      ∑ n ∈ (section52LargeScaleSet m).attach, G n.1 a := by
                  refine Finset.sum_congr rfl ?_
                  intro n hn
                  dsimp [G]
                  rw [dif_pos n.2]
                exact hattach.trans
                  (Finset.sum_attach (section52LargeScaleSet m)
                    (fun n => G n a))
              rw [hsum_eq]
  have hRoot0 :
      Ch04.annealedMomentRoot P ξ G0 ≤ coeff0 * initial := by
    have hSRoot :
        Ch04.annealedMomentRoot P ξ S ≤
          (D.card : ℝ) ^ (1 / (ξ : ℝ)) * initial := by
      change
        Ch04.annealedMomentRoot P ξ
            (fun a : RegCoeffField d =>
              D.sup' hD (fun U => Ch04.LambdaSqCoeffField U s (.finite 1) a)) ≤
          (D.card : ℝ) ^ (1 / (ξ : ℝ)) *
            Ch04.LambdaMomentAtScale P 0 s ξ
      exact
        upper_unitDescendantSup_momentRoot_le_card_mul_origin
          (d := d) (P := P) hP hStruct (s := s) (ξ := ξ) (m := m)
          hs hξ_one hUpperSourceInt
    calc
      Ch04.annealedMomentRoot P ξ G0 =
          c0 * Ch04.annealedMomentRoot P ξ S := by
            exact
              section52_annealedMomentRoot_const_mul_of_nonneg
                (P := P) (ξ := ξ) (c := c0) (X := S)
                hξ_one hc0_nonneg hS_nonneg
      _ ≤ c0 * ((D.card : ℝ) ^ (1 / (ξ : ℝ)) * initial) :=
            mul_le_mul_of_nonneg_left hSRoot hc0_nonneg
      _ = coeff0 * initial := by
            dsimp [coeff0]
            ring
  have hRoot :
      ∀ n ∈ section52LargeScaleSet m,
        Ch04.annealedMomentRoot P ξ (G n) ≤ coeff n * initial := by
    intro n hn
    simpa only [G, coeff, scalarization, initial, hn, dif_pos, mul_assoc] using!
      upperLargeScalePositiveExcessRoot_le_largeScaleRootCoeff_source
        hP hStruct (sSource := s) (r := r) (ξ := ξ)
        hs hr_nonneg hξ_one hξ_two hUpperSourceInt hn
  have hCoeffSum :
      coeff0 + ∑ n ∈ section52LargeScaleSet m, coeff n ≤
        ((c0 * (D.card : ℝ) ^ (1 / (ξ : ℝ))) +
          ((Fintype.card (Fin d) : ℝ) * (Fintype.card (Fin d) : ℝ)) *
            (∑ n ∈ section52LargeScaleSet m,
              section52LargeScaleRootCoeff d ξ r m n)) := by
    dsimp [coeff0, coeff]
    rw [Finset.mul_sum]
  have hmain :=
    section52_annealedMomentRoot_positiveExcess_le_one_add_finset_scaled
      (P := P) (ξ := ξ) (s := section52LargeScaleSet m)
      (X := fun a : RegCoeffField d =>
        Ch04.LambdaSqCoeffField (originCube d (m : ℤ)) r (.finite 1) a)
      (base := scalarization.barSigma 0) (initial := initial)
      (finalCoeff :=
        (c0 * (D.card : ℝ) ^ (1 / (ξ : ℝ))) +
          ((Fintype.card (Fin d) : ℝ) * (Fintype.card (Fin d) : ℝ)) *
            (∑ n ∈ section52LargeScaleSet m,
              section52LargeScaleRootCoeff d ξ r m n))
      (coeff0 := coeff0) (G0 := G0) (G := G) (coeff := coeff)
      hξ_one hInitial_nonneg hG0_nonneg hG_nonneg hG0_aemeas hG_aemeas
      hG0_int hG_int hX_aemeas hPoint hRoot0 hRoot hCoeffSum
  have hPowIntScalar :
      Integrable
        (fun a : RegCoeffField d =>
          (max
            (Ch04.LambdaSqCoeffField (originCube d (m : ℤ)) r (.finite 1) a -
              scalarization.barSigma 0)
            0) ^ ξ) P :=
    section52_integrable_positiveExcess_pow_of_one_add_finset_bound
      (P := P) (ξ := ξ) (s := section52LargeScaleSet m)
      (X := fun a : RegCoeffField d =>
        Ch04.LambdaSqCoeffField (originCube d (m : ℤ)) r (.finite 1) a)
      (base := scalarization.barSigma 0) (G0 := G0) (G := G)
      hξ_one hG0_nonneg hG_nonneg hG0_aemeas hG_aemeas
      hG0_int hG_int hX_aemeas hPoint
  have hPowInt :
      Integrable
        (fun a : RegCoeffField d =>
          (max
            (Ch04.LambdaSqCoeffField (originCube d (m : ℤ)) r (.finite 1) a -
              hP.barSigmaAtScale hStruct 0)
            0) ^ ξ) P := by
    change
      Integrable
        (fun a : RegCoeffField d =>
          (max
            (Ch04.LambdaSqCoeffField (originCube d (m : ℤ)) r (.finite 1) a -
              scalarization.barSigma 0)
            0) ^ ξ) P
    exact hPowIntScalar
  have hBound :
      LambdaPositiveExcessMomentAtScale P (m : ℤ) r ξ
          hP hStruct ≤
        ((((25 * s⁻¹ * (r - s)⁻¹ *
              Real.rpow (3 : ℝ) (-r * (m : ℝ))) ^ 2 /
            section52SmallTailWeight r m) *
            (D.card : ℝ) ^ (1 / (ξ : ℝ))) +
          ((Fintype.card (Fin d) : ℝ) * (Fintype.card (Fin d) : ℝ)) *
            (∑ n ∈ section52LargeScaleSet m,
              section52LargeScaleRootCoeff d ξ r m n)) *
          Ch04.LambdaMomentAtScale P 0 s ξ := by
    change
      Ch04.annealedMomentRoot P ξ
          (fun a : RegCoeffField d =>
            max
              (Ch04.LambdaSqCoeffField (originCube d (m : ℤ)) r (.finite 1) a -
                scalarization.barSigma 0)
              0) ≤
        ((c0 * (D.card : ℝ) ^ (1 / (ξ : ℝ))) +
          ((Fintype.card (Fin d) : ℝ) * (Fintype.card (Fin d) : ℝ)) *
            (∑ n ∈ section52LargeScaleSet m,
              section52LargeScaleRootCoeff d ξ r m n)) *
          initial
    exact hmain
  exact ⟨hPowInt, hBound⟩

theorem upperPositiveExcessMomentAtScale_le_raw_twoExponentCoeff
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    {s r : ℝ} {ξ m : ℕ}
    (hs : 0 < s) (hsr : s < r) (hr_lt_one : r < 1)
    (hξ_one : 1 ≤ ξ) (hξ_two : 2 ≤ ξ)
    (hBlock0 :
      Integrable (Ch04.coarseFullBlockMatrixAtCube (originCube d (0 : ℤ))) P)
    (hUpperSourceInt :
      Integrable
        (fun a : RegCoeffField d =>
          (Ch04.LambdaSqCoeffField (originCube d 0) s (.finite 1) a) ^ ξ) P) :
    let D := descendantsAtScale (originCube d (m : ℤ)) 0
    LambdaPositiveExcessMomentAtScale P (m : ℤ) r ξ
        hP hStruct ≤
      ((((25 * s⁻¹ * (r - s)⁻¹ *
            Real.rpow (3 : ℝ) (-r * (m : ℝ))) ^ 2 /
          section52SmallTailWeight r m) *
          (D.card : ℝ) ^ (1 / (ξ : ℝ))) +
        ((Fintype.card (Fin d) : ℝ) * (Fintype.card (Fin d) : ℝ)) *
          (∑ n ∈ section52LargeScaleSet m,
            section52LargeScaleRootCoeff d ξ r m n)) *
        Ch04.LambdaMomentAtScale P 0 s ξ := by
  classical
  intro D
  have h :=
    upperPositiveExcessMomentAtScale_integrable_and_le_raw_twoExponentCoeff
      (d := d) (P := P) hP hStruct (s := s) (r := r) (ξ := ξ) (m := m)
      hs hsr hr_lt_one hξ_one hξ_two hBlock0 hUpperSourceInt
  exact h.2

theorem lowerPositiveExcessMomentAtScale_integrable_and_le_raw_twoExponentCoeff
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    {s r : ℝ} {ξ m : ℕ}
    (hs : 0 < s) (hsr : s < r) (hr_lt_one : r < 1)
    (hξ_one : 1 ≤ ξ) (hξ_two : 2 ≤ ξ)
    (hBlock0 :
      Integrable (Ch04.coarseFullBlockMatrixAtCube (originCube d (0 : ℤ))) P)
    (hLowerSourceInt :
      Integrable
        (fun a : RegCoeffField d =>
          ((Ch04.lambdaSqCoeffField (originCube d 0) s (.finite 1) a)⁻¹) ^ ξ) P) :
    let D := descendantsAtScale (originCube d (m : ℤ)) 0
    Integrable
        (fun a : RegCoeffField d =>
          (max
            ((Ch04.lambdaSqCoeffField (originCube d (m : ℤ)) r (.finite 1) a)⁻¹ -
              (hP.barSigmaStarAtScale hStruct 0)⁻¹)
            0) ^ ξ) P ∧
      lambdaInvPositiveExcessMomentAtScale P (m : ℤ) r ξ
          hP hStruct ≤
        ((((25 * s⁻¹ * (r - s)⁻¹ *
              Real.rpow (3 : ℝ) (-r * (m : ℝ))) ^ 2 /
            section52SmallTailWeight r m) *
            (D.card : ℝ) ^ (1 / (ξ : ℝ))) +
          ((Fintype.card (Fin d) : ℝ) * (Fintype.card (Fin d) : ℝ)) *
            (∑ n ∈ section52LargeScaleSet m,
              section52LargeScaleRootCoeff d ξ r m n)) *
          Ch04.lambdaInvMomentAtScale P 0 s ξ := by
  classical
  intro D
  let hD : D.Nonempty :=
    descendantsAtScale_nonempty (originCube d (m : ℤ)) (by simp [originCube])
  let : IsProbabilityMeasure P := hP.isProbability
  let scalarization := Ch04.Internal.annealedScalarizationTheory_of_structuralLaw hP hStruct
  let initial : ℝ := Ch04.lambdaInvMomentAtScale P 0 s ξ
  let c0 : ℝ :=
    (25 * s⁻¹ * (r - s)⁻¹ *
        Real.rpow (3 : ℝ) (-r * (m : ℝ))) ^ 2 /
      section52SmallTailWeight r m
  let S : RegCoeffField d → ℝ :=
    fun a => D.sup' hD (fun U => (Ch04.lambdaSqCoeffField U s (.finite 1) a)⁻¹)
  let G0 : RegCoeffField d → ℝ := fun a => c0 * S a
  let G : ℤ → RegCoeffField d → ℝ := fun n a =>
    if hn : n ∈ section52LargeScaleSet m then
      section52LargeScaleWeight r m n *
        (let parents := descendantsAtScale (originCube d (m : ℤ)) n
         let hparents : parents.Nonempty :=
          descendantsAtScale_nonempty (originCube d (m : ℤ))
            (section52LargeScaleSet_mem_le_m hn)
         parents.sup' hparents
          (fun Q =>
            max
              (Ch02.matrixNorm (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight -
                Ch02.matrixNorm
                  ((scalarization.barSigmaStar 0)⁻¹ • (1 : Mat d)))
              0))
    else 0
  let coeff0 : ℝ := c0 * (D.card : ℝ) ^ (1 / (ξ : ℝ))
  let coeff : ℤ → ℝ := fun n =>
    ((Fintype.card (Fin d) : ℝ) * (Fintype.card (Fin d) : ℝ)) *
      section52LargeScaleRootCoeff d ξ r m n
  have hr_pos : 0 < r := hs.trans hsr
  have hr_nonneg : 0 ≤ r := hr_pos.le
  have hVpos : 0 < section52SmallTailWeight r m :=
    section52SmallTailWeight_pos hr_pos m
  have hc0_nonneg : 0 ≤ c0 := by
    dsimp [c0]
    exact div_nonneg (sq_nonneg _) hVpos.le
  have hInitial_nonneg : 0 ≤ initial := by
    exact Ch04.lambdaInvMomentAtScale_nonneg P 0 ξ hs
  have hbase_nonneg : 0 ≤ (scalarization.barSigmaStar 0)⁻¹ := by
    let primitive0 := Ch04.Internal.annealedPrimitiveScalarizationData_of_structuralLaw hP hStruct (0 : ℤ)
    have hBarSigmaStar0_inv_eq :
        (scalarization.barSigmaStar 0)⁻¹ =
          Ch04.Internal.barSigmaStarInvAtScaleOfPrimitive primitive0 := by
      have hstar :
          scalarization.barSigmaStar 0 =
            (Ch04.Internal.barSigmaStarInvAtScaleOfPrimitive primitive0)⁻¹ := by
        simpa [scalarization, primitive0] using
          Ch04.Internal.AnnealedPrimitiveScalarizationData.barSigmaStar_eq_inv_barSigmaStarInv
            (Ch04.Internal.annealedScalarizationTheory_of_structuralLaw hP hStruct)
            (Ch04.Internal.annealedPrimitiveScalarizationData_of_structuralLaw hP hStruct (0 : ℤ))
      rw [hstar, inv_inv]
    have hStar0 :
        0 < Ch04.Internal.barSigmaStarInvAtScaleOfPrimitive primitive0 := by
      simpa [primitive0] using
        Ch04.RestrictionLawCarrier.Internal.barSigmaStarInv_pos_of_integrable_coarseFullBlockMatrixAtCube hP
          (Ch04.Internal.annealedPrimitiveScalarizationData_of_structuralLaw hP hStruct (0 : ℤ))
          hBlock0
    simpa [hBarSigmaStar0_inv_eq] using hStar0.le
  have hS_nonneg : ∀ a, 0 ≤ S a := by
    intro a
    exact lower_unitDescendantSup_nonneg (d := d) (s := s) (m := m) hs a
  have hG0_nonneg : ∀ a, 0 ≤ G0 a := by
    intro a
    exact mul_nonneg hc0_nonneg (hS_nonneg a)
  have hG_nonneg :
      ∀ n ∈ section52LargeScaleSet m, ∀ a, 0 ≤ G n a := by
    intro n hn a
    simpa only [G, scalarization, hn, dif_pos] using!
      lowerLargeScalePositiveExcess_nonneg_source
        hP hStruct hr_nonneg hn a
  have hS_aemeas : AEMeasurable S P := by
    exact lower_unitDescendantSup_aemeasurable
      (d := d) (P := P) hP (s := s) (m := m) hs
  have hG0_aemeas : AEMeasurable G0 P := by
    exact aemeasurable_const.mul hS_aemeas
  have hG_aemeas :
      ∀ n ∈ section52LargeScaleSet m, AEMeasurable (G n) P := by
    intro n hn
    simpa only [G, scalarization, hn, dif_pos] using!
      lowerLargeScalePositiveExcess_aemeasurable_source
        hP hStruct (r := r) hn
  have hS_int : Integrable (fun a : RegCoeffField d => |S a| ^ ξ) P := by
    exact lower_unitDescendantSup_integrable_abs_pow
      (d := d) (P := P) hP hStruct (s := s) (ξ := ξ) (m := m)
      hs hξ_one hLowerSourceInt
  have hG0_int : Integrable (fun a : RegCoeffField d => |G0 a| ^ ξ) P := by
    refine (hS_int.const_mul (|c0| ^ ξ)).congr ?_
    filter_upwards with a
    simp only [G0, abs_mul, mul_pow]
  have hG_int :
      ∀ n ∈ section52LargeScaleSet m,
        Integrable (fun a : RegCoeffField d => |G n a| ^ ξ) P := by
    intro n hn
    have hInt :=
      lowerLargeScalePositiveExcess_integrable_abs_pow_source
        hP hStruct (sSource := s) (r := r) (ξ := ξ)
        hs hξ_one hξ_two hLowerSourceInt hn
    simpa only [G, scalarization, Real.norm_eq_abs, hn, dif_pos] using! hInt
  have hX_aemeas :
      AEMeasurable
        (fun a : RegCoeffField d =>
          (Ch04.lambdaSqCoeffField (originCube d (m : ℤ)) r (.finite 1) a)⁻¹) P :=
    hP.aemeasurable_lambdaSqCoeffField_finite_one_inv (originCube d (m : ℤ)) hr_pos
  have hPoint :
      ∀ᵐ a ∂P,
        max
          ((Ch04.lambdaSqCoeffField (originCube d (m : ℤ)) r (.finite 1) a)⁻¹ -
            (scalarization.barSigmaStar 0)⁻¹)
          0 ≤ G0 a + ∑ n ∈ section52LargeScaleSet m, G n a := by
    filter_upwards with a
    have hsplit :=
      lowerPositiveExcess_pointwise_le_smallTail_add_largeScalePositiveExcess
        (d := d) m (s := r) (base := (scalarization.barSigmaStar 0)⁻¹)
        hr_pos hbase_nonneg a
    have hsmall :=
      lowerSmallTailTerm_le_raw_unitDescendantSup
        (d := d) m (s := s) (r := r) hs hsr hr_lt_one a
    calc
      max
          ((Ch04.lambdaSqCoeffField (originCube d (m : ℤ)) r (.finite 1) a)⁻¹ -
            (scalarization.barSigmaStar 0)⁻¹)
          0 ≤
        lowerSmallSqrtTailCoeffField (d := d) m r a ^ 2 /
            section52SmallTailWeight r m +
          ((section52LargeScaleSet m).attach.sum fun n =>
            section52LargeScaleWeight r m n.1 *
              (let parents := descendantsAtScale (originCube d (m : ℤ)) n.1
               let hparents : parents.Nonempty :=
                descendantsAtScale_nonempty (originCube d (m : ℤ))
                  (section52LargeScaleSet_mem_le_m n.2)
               parents.sup' hparents
                (fun Q =>
                  max
                    (Ch02.matrixNorm (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight -
                      Ch02.matrixNorm ((scalarization.barSigmaStar 0)⁻¹ • (1 : Mat d)))
                    0))) := by
              exact hsplit
      _ ≤ G0 a +
          ((section52LargeScaleSet m).attach.sum fun n =>
            section52LargeScaleWeight r m n.1 *
              (let parents := descendantsAtScale (originCube d (m : ℤ)) n.1
               let hparents : parents.Nonempty :=
                descendantsAtScale_nonempty (originCube d (m : ℤ))
                  (section52LargeScaleSet_mem_le_m n.2)
               parents.sup' hparents
                (fun Q =>
                  max
                    (Ch02.matrixNorm (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight -
                      Ch02.matrixNorm ((scalarization.barSigmaStar 0)⁻¹ • (1 : Mat d)))
                    0))) := by
              exact
                add_le_add_left hsmall
                  (((section52LargeScaleSet m).attach.sum fun n =>
                    section52LargeScaleWeight r m n.1 *
                      (let parents := descendantsAtScale (originCube d (m : ℤ)) n.1
                       let hparents : parents.Nonempty :=
                        descendantsAtScale_nonempty (originCube d (m : ℤ))
                          (section52LargeScaleSet_mem_le_m n.2)
                       parents.sup' hparents
                        (fun Q =>
                          max
                            (Ch02.matrixNorm (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight -
                              Ch02.matrixNorm ((scalarization.barSigmaStar 0)⁻¹ • (1 : Mat d)))
                            0))))
      _ = G0 a + ∑ n ∈ section52LargeScaleSet m, G n a := by
              have hsum_eq :
                  ((section52LargeScaleSet m).attach.sum fun n =>
                    section52LargeScaleWeight r m n.1 *
                      (let parents := descendantsAtScale (originCube d (m : ℤ)) n.1
                       let hparents : parents.Nonempty :=
                        descendantsAtScale_nonempty (originCube d (m : ℤ))
                          (section52LargeScaleSet_mem_le_m n.2)
                       parents.sup' hparents
                        (fun Q =>
                          max
                            (Ch02.matrixNorm (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight -
                              Ch02.matrixNorm ((scalarization.barSigmaStar 0)⁻¹ • (1 : Mat d)))
                            0))) =
                    ∑ n ∈ section52LargeScaleSet m, G n a := by
                have hattach :
                    ((section52LargeScaleSet m).attach.sum fun n =>
                      section52LargeScaleWeight r m n.1 *
                        (let parents := descendantsAtScale (originCube d (m : ℤ)) n.1
                         let hparents : parents.Nonempty :=
                          descendantsAtScale_nonempty (originCube d (m : ℤ))
                            (section52LargeScaleSet_mem_le_m n.2)
                         parents.sup' hparents
                          (fun Q =>
                            max
                              (Ch02.matrixNorm (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight -
                                Ch02.matrixNorm ((scalarization.barSigmaStar 0)⁻¹ • (1 : Mat d)))
                              0))) =
                      ∑ n ∈ (section52LargeScaleSet m).attach, G n.1 a := by
                  refine Finset.sum_congr rfl ?_
                  intro n hn
                  dsimp [G]
                  rw [dif_pos n.2]
                exact hattach.trans
                  (Finset.sum_attach (section52LargeScaleSet m)
                    (fun n => G n a))
              rw [hsum_eq]
  have hRoot0 :
      Ch04.annealedMomentRoot P ξ G0 ≤ coeff0 * initial := by
    have hSRoot :
        Ch04.annealedMomentRoot P ξ S ≤
          (D.card : ℝ) ^ (1 / (ξ : ℝ)) * initial := by
      change
        Ch04.annealedMomentRoot P ξ
            (fun a : RegCoeffField d =>
              D.sup' hD (fun U => (Ch04.lambdaSqCoeffField U s (.finite 1) a)⁻¹)) ≤
          (D.card : ℝ) ^ (1 / (ξ : ℝ)) *
            Ch04.lambdaInvMomentAtScale P 0 s ξ
      exact
        lower_unitDescendantSup_momentRoot_le_card_mul_origin
          (d := d) (P := P) hP hStruct (s := s) (ξ := ξ) (m := m)
          hs hξ_one hLowerSourceInt
    calc
      Ch04.annealedMomentRoot P ξ G0 =
          c0 * Ch04.annealedMomentRoot P ξ S := by
            exact
              section52_annealedMomentRoot_const_mul_of_nonneg
                (P := P) (ξ := ξ) (c := c0) (X := S)
                hξ_one hc0_nonneg hS_nonneg
      _ ≤ c0 * ((D.card : ℝ) ^ (1 / (ξ : ℝ)) * initial) :=
            mul_le_mul_of_nonneg_left hSRoot hc0_nonneg
      _ = coeff0 * initial := by
            dsimp [coeff0]
            ring
  have hRoot :
      ∀ n ∈ section52LargeScaleSet m,
        Ch04.annealedMomentRoot P ξ (G n) ≤ coeff n * initial := by
    intro n hn
    simpa only [G, coeff, scalarization, initial, hn, dif_pos, mul_assoc] using!
      lowerLargeScalePositiveExcessRoot_le_largeScaleRootCoeff_source
        hP hStruct (sSource := s) (r := r) (ξ := ξ)
        hs hr_nonneg hξ_one hξ_two hLowerSourceInt hn
  have hCoeffSum :
      coeff0 + ∑ n ∈ section52LargeScaleSet m, coeff n ≤
        ((c0 * (D.card : ℝ) ^ (1 / (ξ : ℝ))) +
          ((Fintype.card (Fin d) : ℝ) * (Fintype.card (Fin d) : ℝ)) *
            (∑ n ∈ section52LargeScaleSet m,
              section52LargeScaleRootCoeff d ξ r m n)) := by
    dsimp [coeff0, coeff]
    rw [Finset.mul_sum]
  have hmain :=
    section52_annealedMomentRoot_positiveExcess_le_one_add_finset_scaled
      (P := P) (ξ := ξ) (s := section52LargeScaleSet m)
      (X := fun a : RegCoeffField d =>
        (Ch04.lambdaSqCoeffField (originCube d (m : ℤ)) r (.finite 1) a)⁻¹)
      (base := (scalarization.barSigmaStar 0)⁻¹) (initial := initial)
      (finalCoeff :=
        (c0 * (D.card : ℝ) ^ (1 / (ξ : ℝ))) +
          ((Fintype.card (Fin d) : ℝ) * (Fintype.card (Fin d) : ℝ)) *
            (∑ n ∈ section52LargeScaleSet m,
              section52LargeScaleRootCoeff d ξ r m n))
      (coeff0 := coeff0) (G0 := G0) (G := G) (coeff := coeff)
      hξ_one hInitial_nonneg hG0_nonneg hG_nonneg hG0_aemeas hG_aemeas
      hG0_int hG_int hX_aemeas hPoint hRoot0 hRoot hCoeffSum
  have hPowIntScalar :
      Integrable
        (fun a : RegCoeffField d =>
          (max
            ((Ch04.lambdaSqCoeffField (originCube d (m : ℤ)) r (.finite 1) a)⁻¹ -
              (scalarization.barSigmaStar 0)⁻¹)
            0) ^ ξ) P :=
    section52_integrable_positiveExcess_pow_of_one_add_finset_bound
      (P := P) (ξ := ξ) (s := section52LargeScaleSet m)
      (X := fun a : RegCoeffField d =>
        (Ch04.lambdaSqCoeffField (originCube d (m : ℤ)) r (.finite 1) a)⁻¹)
      (base := (scalarization.barSigmaStar 0)⁻¹) (G0 := G0) (G := G)
      hξ_one hG0_nonneg hG_nonneg hG0_aemeas hG_aemeas
      hG0_int hG_int hX_aemeas hPoint
  have hPowInt :
      Integrable
        (fun a : RegCoeffField d =>
          (max
            ((Ch04.lambdaSqCoeffField (originCube d (m : ℤ)) r (.finite 1) a)⁻¹ -
              (hP.barSigmaStarAtScale hStruct 0)⁻¹)
            0) ^ ξ) P := by
    change
      Integrable
        (fun a : RegCoeffField d =>
          (max
            ((Ch04.lambdaSqCoeffField (originCube d (m : ℤ)) r (.finite 1) a)⁻¹ -
              (scalarization.barSigmaStar 0)⁻¹)
            0) ^ ξ) P
    exact hPowIntScalar
  have hBound :
      lambdaInvPositiveExcessMomentAtScale P (m : ℤ) r ξ
          hP hStruct ≤
        ((((25 * s⁻¹ * (r - s)⁻¹ *
              Real.rpow (3 : ℝ) (-r * (m : ℝ))) ^ 2 /
            section52SmallTailWeight r m) *
            (D.card : ℝ) ^ (1 / (ξ : ℝ))) +
          ((Fintype.card (Fin d) : ℝ) * (Fintype.card (Fin d) : ℝ)) *
            (∑ n ∈ section52LargeScaleSet m,
              section52LargeScaleRootCoeff d ξ r m n)) *
          Ch04.lambdaInvMomentAtScale P 0 s ξ := by
    change
      Ch04.annealedMomentRoot P ξ
          (fun a : RegCoeffField d =>
            max
              ((Ch04.lambdaSqCoeffField (originCube d (m : ℤ)) r (.finite 1) a)⁻¹ -
                (scalarization.barSigmaStar 0)⁻¹)
              0) ≤
        ((c0 * (D.card : ℝ) ^ (1 / (ξ : ℝ))) +
          ((Fintype.card (Fin d) : ℝ) * (Fintype.card (Fin d) : ℝ)) *
            (∑ n ∈ section52LargeScaleSet m,
              section52LargeScaleRootCoeff d ξ r m n)) *
          initial
    exact hmain
  exact ⟨hPowInt, hBound⟩

theorem lowerPositiveExcessMomentAtScale_le_raw_twoExponentCoeff
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    {s r : ℝ} {ξ m : ℕ}
    (hs : 0 < s) (hsr : s < r) (hr_lt_one : r < 1)
    (hξ_one : 1 ≤ ξ) (hξ_two : 2 ≤ ξ)
    (hBlock0 :
      Integrable (Ch04.coarseFullBlockMatrixAtCube (originCube d (0 : ℤ))) P)
    (hLowerSourceInt :
      Integrable
        (fun a : RegCoeffField d =>
          ((Ch04.lambdaSqCoeffField (originCube d 0) s (.finite 1) a)⁻¹) ^ ξ) P) :
    let D := descendantsAtScale (originCube d (m : ℤ)) 0
    lambdaInvPositiveExcessMomentAtScale P (m : ℤ) r ξ
        hP hStruct ≤
      ((((25 * s⁻¹ * (r - s)⁻¹ *
            Real.rpow (3 : ℝ) (-r * (m : ℝ))) ^ 2 /
          section52SmallTailWeight r m) *
          (D.card : ℝ) ^ (1 / (ξ : ℝ))) +
        ((Fintype.card (Fin d) : ℝ) * (Fintype.card (Fin d) : ℝ)) *
          (∑ n ∈ section52LargeScaleSet m,
            section52LargeScaleRootCoeff d ξ r m n)) *
        Ch04.lambdaInvMomentAtScale P 0 s ξ := by
  classical
  intro D
  have h :=
    lowerPositiveExcessMomentAtScale_integrable_and_le_raw_twoExponentCoeff
      (d := d) (P := P) hP hStruct (s := s) (r := r) (ξ := ξ) (m := m)
      hs hsr hr_lt_one hξ_one hξ_two hBlock0 hLowerSourceInt
  exact h.2

/-- Upper positive-excess estimate in the corrected two-exponent Section 5.2
moment lemma.  The source exponent is `s`; the scale-`m` target exponent is
`r`. -/
theorem LambdaPositiveExcessMomentAtScale_le_twoExponentMomentBoundCoeff
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    {s r : ℝ} {ξ m : ℕ}
    (hs : 0 < s) (hsr : s < r) (hr_lt_one : r < 1)
    (hξ_one : 1 ≤ ξ) (hξ_two : 2 ≤ ξ)
    (hlargeGap : 0 < ((d : ℝ) / 2) + (d : ℝ) / (ξ : ℝ) - r)
    (hBlock0 :
      Integrable (Ch04.coarseFullBlockMatrixAtCube (originCube d (0 : ℤ))) P)
    (hUpperSourceInt :
      Integrable
        (fun a : RegCoeffField d =>
          (Ch04.LambdaSqCoeffField (originCube d 0) s (.finite 1) a) ^ ξ) P) :
    LambdaPositiveExcessMomentAtScale P (m : ℤ) r ξ
        hP hStruct ≤
      section52TwoExponentMomentBoundCoeff d ξ
        (625 + section52LargeScalarAbsorptionConst d) s r m *
        Ch04.LambdaMomentAtScale P 0 s ξ := by
  let D := descendantsAtScale (originCube d (m : ℤ)) 0
  have hraw :=
    upperPositiveExcessMomentAtScale_le_raw_twoExponentCoeff
      (d := d) (P := P) hP hStruct (s := s) (r := r) (ξ := ξ) (m := m)
      hs hsr hr_lt_one hξ_one hξ_two hBlock0 hUpperSourceInt
  have hcoeff :=
    section52RawTwoExponentCoeff_le_twoExponentMomentBoundCoeff
      (d := d) (ξ := ξ) (m := m) (s := s) (r := r)
      hξ_one hξ_two hs hsr hr_lt_one hlargeGap
  have hinitial_nonneg : 0 ≤ Ch04.LambdaMomentAtScale P 0 s ξ :=
    Ch04.LambdaMomentAtScale_nonneg P 0 ξ hs
  calc
    LambdaPositiveExcessMomentAtScale P (m : ℤ) r ξ
        hP hStruct
        ≤ ((((25 * s⁻¹ * (r - s)⁻¹ *
              Real.rpow (3 : ℝ) (-r * (m : ℝ))) ^ 2 /
            section52SmallTailWeight r m) *
            (D.card : ℝ) ^ (1 / (ξ : ℝ))) +
          ((Fintype.card (Fin d) : ℝ) * (Fintype.card (Fin d) : ℝ)) *
            (∑ n ∈ section52LargeScaleSet m,
              section52LargeScaleRootCoeff d ξ r m n)) *
          Ch04.LambdaMomentAtScale P 0 s ξ := by
            exact hraw
    _ ≤ section52TwoExponentMomentBoundCoeff d ξ
          (625 + section52LargeScalarAbsorptionConst d) s r m *
          Ch04.LambdaMomentAtScale P 0 s ξ :=
        mul_le_mul_of_nonneg_right
          (by
            change
              ((((25 * s⁻¹ * (r - s)⁻¹ *
                    Real.rpow (3 : ℝ) (-r * (m : ℝ))) ^ 2 /
                  section52SmallTailWeight r m) *
                  (D.card : ℝ) ^ (1 / (ξ : ℝ))) +
                ((Fintype.card (Fin d) : ℝ) * (Fintype.card (Fin d) : ℝ)) *
                  (∑ n ∈ section52LargeScaleSet m,
                    section52LargeScaleRootCoeff d ξ r m n)) ≤
                section52TwoExponentMomentBoundCoeff d ξ
                  (625 + section52LargeScalarAbsorptionConst d) s r m
            exact hcoeff)
          hinitial_nonneg

/-- Lower inverse positive-excess estimate in the corrected two-exponent
Section 5.2 moment lemma. -/
theorem lambdaInvPositiveExcessMomentAtScale_le_twoExponentMomentBoundCoeff
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    {s r : ℝ} {ξ m : ℕ}
    (hs : 0 < s) (hsr : s < r) (hr_lt_one : r < 1)
    (hξ_one : 1 ≤ ξ) (hξ_two : 2 ≤ ξ)
    (hlargeGap : 0 < ((d : ℝ) / 2) + (d : ℝ) / (ξ : ℝ) - r)
    (hBlock0 :
      Integrable (Ch04.coarseFullBlockMatrixAtCube (originCube d (0 : ℤ))) P)
    (hLowerSourceInt :
      Integrable
        (fun a : RegCoeffField d =>
          ((Ch04.lambdaSqCoeffField (originCube d 0) s (.finite 1) a)⁻¹) ^ ξ) P) :
    lambdaInvPositiveExcessMomentAtScale P (m : ℤ) r ξ
        hP hStruct ≤
      section52TwoExponentMomentBoundCoeff d ξ
        (625 + section52LargeScalarAbsorptionConst d) s r m *
        Ch04.lambdaInvMomentAtScale P 0 s ξ := by
  let D := descendantsAtScale (originCube d (m : ℤ)) 0
  have hraw :=
    lowerPositiveExcessMomentAtScale_le_raw_twoExponentCoeff
      (d := d) (P := P) hP hStruct (s := s) (r := r) (ξ := ξ) (m := m)
      hs hsr hr_lt_one hξ_one hξ_two hBlock0 hLowerSourceInt
  have hcoeff :=
    section52RawTwoExponentCoeff_le_twoExponentMomentBoundCoeff
      (d := d) (ξ := ξ) (m := m) (s := s) (r := r)
      hξ_one hξ_two hs hsr hr_lt_one hlargeGap
  have hinitial_nonneg : 0 ≤ Ch04.lambdaInvMomentAtScale P 0 s ξ :=
    Ch04.lambdaInvMomentAtScale_nonneg P 0 ξ hs
  calc
    lambdaInvPositiveExcessMomentAtScale P (m : ℤ) r ξ
        hP hStruct
        ≤ ((((25 * s⁻¹ * (r - s)⁻¹ *
              Real.rpow (3 : ℝ) (-r * (m : ℝ))) ^ 2 /
            section52SmallTailWeight r m) *
            (D.card : ℝ) ^ (1 / (ξ : ℝ))) +
          ((Fintype.card (Fin d) : ℝ) * (Fintype.card (Fin d) : ℝ)) *
            (∑ n ∈ section52LargeScaleSet m,
              section52LargeScaleRootCoeff d ξ r m n)) *
          Ch04.lambdaInvMomentAtScale P 0 s ξ := by
            exact hraw
    _ ≤ section52TwoExponentMomentBoundCoeff d ξ
          (625 + section52LargeScalarAbsorptionConst d) s r m *
          Ch04.lambdaInvMomentAtScale P 0 s ξ :=
        mul_le_mul_of_nonneg_right
          (by
            change
              ((((25 * s⁻¹ * (r - s)⁻¹ *
                    Real.rpow (3 : ℝ) (-r * (m : ℝ))) ^ 2 /
                  section52SmallTailWeight r m) *
                  (D.card : ℝ) ^ (1 / (ξ : ℝ))) +
                ((Fintype.card (Fin d) : ℝ) * (Fintype.card (Fin d) : ℝ)) *
                  (∑ n ∈ section52LargeScaleSet m,
                    section52LargeScaleRootCoeff d ξ r m n)) ≤
                section52TwoExponentMomentBoundCoeff d ξ
                  (625 + section52LargeScalarAbsorptionConst d) s r m
            exact hcoeff)
          hinitial_nonneg

/-- The shifted upper positive excess appearing in Section 5.3 is integrable
under `(P4)`.  This extracts the integrability already used inside the
Section 5.2 two-exponent moment estimate. -/
theorem upperPositiveExcessPowIntegrableAtScale_from_P4_twoExponent
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {rUpper : ℝ} (hrUpper_gt : hP4.sUpper < rUpper)
    (hrUpper_lt_one : rUpper < 1) (m : ℕ) :
    Integrable
      (fun a : RegCoeffField d =>
        (max
          (Ch04.LambdaSqCoeffField (originCube d (m : ℤ)) rUpper (.finite 1) a -
            hP.barSigmaAtScale hStruct 0)
          0) ^ hP4.xi) P := by
  have hξ_one : 1 ≤ hP4.xi := Nat.succ_le_of_lt hP4.xi_pos
  have hξ_two : 2 ≤ hP4.xi := hP4.two_le_xi
  have hBlock0 :
      Integrable (Ch04.coarseFullBlockMatrixAtCube (originCube d (0 : ℤ))) P :=
    hP.integrable_coarseFullBlockMatrixAtCube_origin_of_integrable_factor_observables
      hP4.sUpper_pos hP4.sLower_pos hξ_one
      hP4.upper_moment_integrable hP4.lower_inv_moment_integrable
  simpa using
    (upperPositiveExcessMomentAtScale_integrable_and_le_raw_twoExponentCoeff
      (d := d) (P := P) hP hStruct
      (s := hP4.sUpper) (r := rUpper) (ξ := hP4.xi) (m := m)
      hP4.sUpper_pos hrUpper_gt hrUpper_lt_one hξ_one hξ_two
      hBlock0 hP4.upper_moment_integrable).1

/-- The shifted lower inverse positive excess appearing in Section 5.3 is
integrable under `(P4)`. -/
theorem lowerPositiveExcessPowIntegrableAtScale_from_P4_twoExponent
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {rLower : ℝ} (hrLower_gt : hP4.sLower < rLower)
    (hrLower_lt_one : rLower < 1) (m : ℕ) :
    Integrable
      (fun a : RegCoeffField d =>
        (max
          ((Ch04.lambdaSqCoeffField (originCube d (m : ℤ)) rLower (.finite 1) a)⁻¹ -
            (hP.barSigmaStarAtScale hStruct 0)⁻¹)
          0) ^ hP4.xi) P := by
  have hξ_one : 1 ≤ hP4.xi := Nat.succ_le_of_lt hP4.xi_pos
  have hξ_two : 2 ≤ hP4.xi := hP4.two_le_xi
  have hBlock0 :
      Integrable (Ch04.coarseFullBlockMatrixAtCube (originCube d (0 : ℤ))) P :=
    hP.integrable_coarseFullBlockMatrixAtCube_origin_of_integrable_factor_observables
      hP4.sUpper_pos hP4.sLower_pos hξ_one
      hP4.upper_moment_integrable hP4.lower_inv_moment_integrable
  simpa using
    (lowerPositiveExcessMomentAtScale_integrable_and_le_raw_twoExponentCoeff
      (d := d) (P := P) hP hStruct
      (s := hP4.sLower) (r := rLower) (ξ := hP4.xi) (m := m)
      hP4.sLower_pos hrLower_gt hrLower_lt_one hξ_one hξ_two
      hBlock0 hP4.lower_inv_moment_integrable).1

/-- Manuscript Lemma `l.multiscale.ellipticity.moments.homogenization.scale`,
in its corrected two-exponent form.

The single constant is explicit in Lean and depends only on `d`; the public
statement exposes it existentially, matching the manuscript's `C(d)`. -/
theorem multiscaleEllipticityMomentBounds_homogenizationScale
    {d : ℕ} [NeZero d] :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {P : Ch04.RestrictionCoeffLaw d}
        (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
        (hP4 : QuantitativeCoarseGrainedEllipticity P),
        ∀ (rUpper rLower : ℝ) (m : ℕ),
          hP4.sUpper < rUpper → rUpper < 1 →
          hP4.sLower < rLower → rLower < 1 →
            LambdaPositiveExcessMomentAtScale P (m : ℤ) rUpper hP4.xi
                hP hStruct ≤
              section52TwoExponentMomentBoundCoeff d hP4.xi C hP4.sUpper rUpper m *
                Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi ∧
            lambdaInvPositiveExcessMomentAtScale P (m : ℤ) rLower hP4.xi
                hP hStruct ≤
              section52TwoExponentMomentBoundCoeff d hP4.xi C hP4.sLower rLower m *
                Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi := by
  refine ⟨625 + section52LargeScalarAbsorptionConst d,
    add_nonneg (by norm_num) (section52LargeScalarAbsorptionConst_nonneg d), ?_⟩
  intro P hP hStruct hP4 rUpper rLower m hsrUpper hrUpper hsrLower hrLower
  have hξ_one : 1 ≤ hP4.xi := Nat.succ_le_of_lt hP4.xi_pos
  have hξ_two : 2 ≤ hP4.xi := hP4.two_le_xi
  have hBlock0 :
      Integrable (Ch04.coarseFullBlockMatrixAtCube (originCube d (0 : ℤ))) P :=
    hP.integrable_coarseFullBlockMatrixAtCube_origin_of_integrable_factor_observables
      hP4.sUpper_pos hP4.sLower_pos hξ_one
      hP4.upper_moment_integrable hP4.lower_inv_moment_integrable
  have hUpperGap :
      0 < ((d : ℝ) / 2) + (d : ℝ) / (hP4.xi : ℝ) - rUpper := by
    have hd_two : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hP4.two_le_dim
    have hd_half : (1 : ℝ) ≤ (d : ℝ) / 2 := by
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
      simpa using hd_two
    have hd_nonneg : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
    have hxi_nonneg : (0 : ℝ) ≤ (hP4.xi : ℝ) := by
      exact_mod_cast Nat.zero_le hP4.xi
    have hdiv_nonneg : 0 ≤ (d : ℝ) / (hP4.xi : ℝ) :=
      div_nonneg hd_nonneg hxi_nonneg
    have hr_lt :
        rUpper < (d : ℝ) / 2 + (d : ℝ) / (hP4.xi : ℝ) := by
      calc
        rUpper < 1 := hrUpper
        _ ≤ (d : ℝ) / 2 := hd_half
        _ ≤ (d : ℝ) / 2 + (d : ℝ) / (hP4.xi : ℝ) :=
          le_add_of_nonneg_right hdiv_nonneg
    exact sub_pos.mpr hr_lt
  have hLowerGap :
      0 < ((d : ℝ) / 2) + (d : ℝ) / (hP4.xi : ℝ) - rLower := by
    have hd_two : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hP4.two_le_dim
    have hd_half : (1 : ℝ) ≤ (d : ℝ) / 2 := by
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
      simpa using hd_two
    have hd_nonneg : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
    have hxi_nonneg : (0 : ℝ) ≤ (hP4.xi : ℝ) := by
      exact_mod_cast Nat.zero_le hP4.xi
    have hdiv_nonneg : 0 ≤ (d : ℝ) / (hP4.xi : ℝ) :=
      div_nonneg hd_nonneg hxi_nonneg
    have hr_lt :
        rLower < (d : ℝ) / 2 + (d : ℝ) / (hP4.xi : ℝ) := by
      calc
        rLower < 1 := hrLower
        _ ≤ (d : ℝ) / 2 := hd_half
        _ ≤ (d : ℝ) / 2 + (d : ℝ) / (hP4.xi : ℝ) :=
          le_add_of_nonneg_right hdiv_nonneg
    exact sub_pos.mpr hr_lt
  constructor
  · exact
      LambdaPositiveExcessMomentAtScale_le_twoExponentMomentBoundCoeff
        hP hStruct hP4.sUpper_pos hsrUpper hrUpper hξ_one hξ_two
        hUpperGap hBlock0 hP4.upper_moment_integrable
  · exact
      lambdaInvPositiveExcessMomentAtScale_le_twoExponentMomentBoundCoeff
        hP hStruct hP4.sLower_pos hsrLower hrLower hξ_one hξ_two
        hLowerGap hBlock0 hP4.lower_inv_moment_integrable

end

end Section52
end Ch05
end Book
end Homogenization
