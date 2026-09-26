/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module



public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import LeanPool.CarlsonFunctions.StdSimplexMeasure.CoordinateRealization

public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Measure.Dirac.Def
public import LeanPool.CarlsonFunctions.StdSimplexMeasure.PositiveSimplex.Basic

/-! # The ambient affine-hyperplane coordinate measure -/

@[expose] public noncomputable section StdSimplexCoordinateMeasure

namespace MeasureTheory.Measure

variable {ι : Type*} [Fintype ι]


/-- The coordinate map is measurable. -/
theorem measurable_stdSimplexCoordMap (i : ι) :
    Measurable (stdSimplexCoordMap (R := ℝ) i) :=
  (continuous_stdSimplexCoordMap i).measurable

/-- Lebesgue measure pushed forward from the free coordinates omitting i. -/
def stdSimplexMeasureAt (i : ι) : Measure (ι → ℝ) := by
  classical
  exact Measure.map (stdSimplexCoordMap (R := ℝ) i) volume

open scoped Classical in
/-- The Lebesgue measure is homogeneous of degree `(Fintype.card ι - 1)` in the free coordinates. -/
theorem volume_map_smul_free_coords (i : ι) (c : ℝ) (hc : 0 < c) :
    Measure.map (c • · : ({j : ι // j ≠ i} → ℝ) → ({j : ι // j ≠ i} → ℝ)) volume =
      ENNReal.ofReal (c ^ (Fintype.card ι - 1))⁻¹ • volume := by
  let f : ({j : ι // j ≠ i} → ℝ) →ₗ[ℝ] ({j : ι // j ≠ i} → ℝ) :=
    c • LinearMap.id
  have hf : LinearMap.det f ≠ 0 := by
    simp [f, hc.ne']
  have hmap := Real.map_linearMap_volume_pi_eq_smul_volume_pi hf
  change Measure.map f volume = _
  simpa [f, abs_of_pos hc, Fintype.card_subtype_compl,
    ENNReal.ofReal_inv_of_pos (pow_pos hc _)] using hmap

open scoped Classical in
/-- Coordinate explicit form of `stdSimplexMeasureAt`. -/
theorem stdSimplexMeasureAt_eq_map_piSplitAt_symm (i : ι) :
    stdSimplexMeasureAt i =
      Measure.map (Homeomorph.piSplitAt i (fun _ => ℝ)).symm
        (Measure.map (fun x : {j : ι // j ≠ i} → ℝ => (1 - ∑ q, x q, x)) volume) := by
  unfold stdSimplexMeasureAt stdSimplexCoordMap
  rw [Measure.map_map]
  · rfl
  · exact (Homeomorph.piSplitAt i (fun _ => ℝ)).symm.measurable
  · fun_prop

open scoped Classical in
/-- The absolute determinant of uniform scaling on the free-coordinate space. -/
private lemma stdSimplexScaleMap_det (t : ℝ) (i : ι) :
    abs (LinearMap.det ((1 - t) • (LinearMap.id : ({j // j ≠ i} → ℝ) →ₗ[ℝ] _)))
      = abs (1 - t) ^ (Fintype.card ι - 1) := by
  simp [LinearMap.det_smul, Fintype.card_subtype_compl, abs_pow]

open scoped Classical in
/-- Pushing `stdSimplexMeasureAt (σ i)` forward along `σ` gives `stdSimplexMeasureAt i`. -/
theorem stdSimplexMeasureAt_map_perm (i : ι) (σ : Equiv.Perm ι) :
  Measure.map (fun u => u ∘ σ)
    (stdSimplexMeasureAt (σ i)) = stdSimplexMeasureAt i := by
  let e : {j : ι // j ≠ i} ≃ {j : ι // j ≠ σ i} := {
    toFun j := ⟨σ j, fun h => j.property (σ.injective h)⟩
    invFun j := ⟨σ.symm j, fun h => j.property (by simpa using congrArg σ h)⟩
    left_inv j := by ext; simp
    right_inv j := by ext; simp
  }
  let T := MeasurableEquiv.piCongrLeft
    (fun _ : {j : ι // j ≠ i} => ℝ) e.symm
  have hT : Measure.map T volume = volume :=
    (volume_measurePreserving_piCongrLeft
      (fun _ : {j : ι // j ≠ i} => ℝ) e.symm).map_eq
  unfold stdSimplexMeasureAt
  calc
    Measure.map (fun u => u ∘ σ) (Measure.map (stdSimplexCoordMap (σ i)) volume) =
        Measure.map ((fun u => u ∘ σ) ∘ stdSimplexCoordMap (σ i)) volume := by
          exact Measure.map_map
            (continuous_pi (fun j => continuous_apply (σ j)) |>.measurable)
            (measurable_stdSimplexCoordMap (σ i))
    _ = Measure.map (stdSimplexCoordMap i ∘ T) volume := by
      congr 1
      funext x
      have hTx : T x = fun ⟨j, hj⟩ => x ⟨σ j, fun h => hj (σ.injective h)⟩ := by
        funext j
        change T x j = x (e j)
        rw [show j = e.symm (e j) by simp]
        rw [MeasurableEquiv.piCongrLeft_apply_apply]
        exact congrArg x (e.apply_symm_apply (e j)).symm
      change stdSimplexCoordMap (σ i) x ∘ σ = stdSimplexCoordMap i (T x)
      rw [hTx]
      exact stdSimplexCoordMap_comp_perm i σ x
    _ = Measure.map (stdSimplexCoordMap i) (Measure.map T volume) := by
      exact (Measure.map_map (measurable_stdSimplexCoordMap i) T.measurable).symm
    _ = Measure.map (stdSimplexCoordMap i) volume := by rw [hT]

open scoped Classical in
/-- Pushing `stdSimplexMeasureAt i` forward along the transposition `swap i j` gives
`stdSimplexMeasureAt j`. -/
theorem stdSimplexMeasureAt_swap (i j : ι) :
    Measure.map (fun x => x ∘ Equiv.swap i j) (stdSimplexMeasureAt i) =
      stdSimplexMeasureAt j := by
  simpa [Equiv.swap_apply_def] using
    (stdSimplexMeasureAt_map_perm j (Equiv.swap i j))

open scoped Classical in
/-- The affine free-coordinate change induced by swapping two ambient coordinates preserves
Lebesgue measure. -/
private theorem map_stdSimplexFreeCoordSwap_volume (i j : ι) (hij : i ≠ j) :
    Measure.map (stdSimplexFreeCoordSwap (R := ℝ) i j hij) volume = volume := by
  let α := {q : ι // q ≠ i}
  let ji : α := ⟨j, Ne.symm hij⟩
  let L := stdSimplexFreeCoordSwapLinear (R := ℝ) i j hij
  have hLinv : L.comp L = LinearMap.id := by
    apply LinearMap.ext
    intro x
    funext q
    by_cases hq : q = ji
    · subst q
      rw [LinearMap.comp_apply, LinearMap.id_apply]
      change (if ji = ji then -∑ q, L x q else L x ji) = x ji
      rw [ite_eq_left rfl, sum_stdSimplexFreeCoordSwapLinear]
      simp only [neg_neg]
      congr 1
    · simp [L, stdSimplexFreeCoordSwapLinear, ji, hq]
  have hdet_sq : LinearMap.det L * LinearMap.det L = 1 := by
    rw [← LinearMap.det_comp, hLinv, LinearMap.det_id]
  have hdet_abs : |LinearMap.det L| = 1 := by
    have ha : |LinearMap.det L| ^ 2 = 1 := by
      rw [sq_abs]
      nlinarith
    nlinarith [abs_nonneg (LinearMap.det L)]
  have hmapL : Measure.map L volume = volume := by
    have hdet_ne : LinearMap.det L ≠ 0 := by
      intro h
      simp [h] at hdet_abs
    rw [Real.map_linearMap_volume_pi_eq_smul_volume_pi hdet_ne]
    simp [abs_inv, hdet_abs]
  let c : α → ℝ := fun q => if q = ji then 1 else 0
  rw [show stdSimplexFreeCoordSwap i j hij = (fun y => c + y) ∘ L by rfl]
  rw [← Measure.map_map (by fun_prop) (by fun_prop), hmapL]
  exact Measure.IsAddLeftInvariant.map_add_left_eq_self c

open scoped Classical in
/-- The coordinate measure is independent of the chosen special coordinate. -/
theorem stdSimplexMeasureAt_eq (i j : ι) :
    stdSimplexMeasureAt i = stdSimplexMeasureAt j := by
  by_cases hij : i = j
  · subst j
    rfl
  have hswap : Measure.map (fun u : ι → ℝ => u ∘ Equiv.swap i j)
      (stdSimplexMeasureAt i) = stdSimplexMeasureAt i := by
    unfold stdSimplexMeasureAt
    calc
      Measure.map (fun u : ι → ℝ => u ∘ Equiv.swap i j)
          (Measure.map (stdSimplexCoordMap i) volume) =
          Measure.map ((fun u : ι → ℝ => u ∘ Equiv.swap i j) ∘
            stdSimplexCoordMap i) volume :=
        Measure.map_map (by fun_prop) (measurable_stdSimplexCoordMap i)
      _ = Measure.map (stdSimplexCoordMap i ∘ stdSimplexFreeCoordSwap i j hij) volume := by
        rw [stdSimplexCoordMap_comp_freeCoordSwap i j hij]
      _ = Measure.map (stdSimplexCoordMap i)
          (Measure.map (stdSimplexFreeCoordSwap i j hij) volume) :=
        (Measure.map_map (measurable_stdSimplexCoordMap i)
          (continuous_stdSimplexFreeCoordSwap i j hij).measurable).symm
      _ = Measure.map (stdSimplexCoordMap i) volume := by
        rw [map_stdSimplexFreeCoordSwap_volume i j hij]
  exact hswap.symm.trans (stdSimplexMeasureAt_swap i j)

/-- The coordinate Lebesgue measure on `stdSimplexAffineSet`. When `ι` is empty the measure
is zero; otherwise it is the push-forward of Lebesgue measure from any set of free
coordinates. -/
def stdSimplexMeasure :
    Measure (ι → ℝ) := by
  by_cases h : Nonempty ι
  · exact stdSimplexMeasureAt (Classical.choice h)
  · exact 0

/-- `stdSimplexMeasure` equals `stdSimplexMeasureAt i`, for any `i`. -/
theorem stdSimplexMeasure_eq_at [Nonempty ι] (i : ι) :
    stdSimplexMeasure (ι := ι) = stdSimplexMeasureAt i := by
  unfold stdSimplexMeasure
  rw [dite_eq_left (inferInstance : Nonempty ι)]
  exact stdSimplexMeasureAt_eq _ i

open scoped Classical in
/-- The coordinate map pushes the restricted volume on the free coordinates to the restricted
simplex measure. -/
theorem stdSimplexMeasure_restrict_stdSimplex
    [Nonempty ι] (i : ι) :
    (stdSimplexMeasure (ι := ι)).restrict (Convexity.StdSimplex.coordinateSet ℝ ι) =
      Measure.map (stdSimplexCoordMap i)
        (volume.restrict (stdSimplexFreeCoords i)) := by
  rw [stdSimplexMeasure_eq_at i]
  unfold stdSimplexMeasureAt
  rw [Measure.restrict_map
    (measurable_stdSimplexCoordMap i)
    (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet]
  rw [preimage_stdSimplexCoordMap]

/-- `stdSimplexMeasure` is zero when `ι` is empty. -/
@[simp] theorem stdSimplexMeasure_empty [IsEmpty ι] :
    stdSimplexMeasure (ι := ι) = 0 := by
  unfold stdSimplexMeasure
  exact dite_eq_right (not_nonempty_iff.mpr inferInstance)

/-- `stdSimplexMeasure` is a `SigmaFinite` measure. -/
instance sigmaFinite_stdSimplexMeasure :
    SigmaFinite (stdSimplexMeasure (ι := ι)) := by
  cases isEmpty_or_nonempty ι with
  | inl h =>
      let : IsEmpty ι := h
      rw [stdSimplexMeasure_empty]
      infer_instance
  | inr h =>
      let : Nonempty ι := h
      let i : ι := Classical.choice h
      rw [stdSimplexMeasure_eq_at i]
      unfold stdSimplexMeasureAt
      exact (isClosedEmbedding_stdSimplexCoordMap i).measurableEmbedding.sigmaFinite_map

open scoped Classical in
/-- For a type with a unique element, the pushforward measure at that element is a Dirac mass
at the all-ones point. -/
@[simp] theorem stdSimplexMeasureAt_of_unique [Unique ι] (i : ι) :
    stdSimplexMeasureAt i = dirac (fun _ ↦ (1 : ℝ)) := by
  let : IsEmpty {j : ι // j ≠ i} :=
    ⟨fun j => j.property (Subsingleton.elim _ _)⟩
  unfold stdSimplexMeasureAt
  rw [Measure.volume_pi_eq_dirac]
  rw [Measure.map_dirac' (measurable_stdSimplexCoordMap i)]
  congr 1
  funext j
  have hji : j = i := Subsingleton.elim _ _
  subst j
  simp

/-- Restating `stdSimplexMeasureAt_of_unique` in terms of `stdSimplexMeasure`. -/
theorem stdSimplexMeasure_unique [Unique ι] :
    stdSimplexMeasure (ι := ι) = dirac (fun _ ↦ (1 : ℝ)) := by
  rw [stdSimplexMeasure_eq_at default, stdSimplexMeasureAt_of_unique]

/-- The coordinate Lebesgue measure is supported on `stdSimplexAffineSet`. -/
theorem stdSimplexMeasure_restrict_stdSimplexAffineSet :
  stdSimplexMeasure (ι := ι) =
    stdSimplexMeasure.restrict stdSimplexAffineSet := by
  cases isEmpty_or_nonempty ι with
  | inl h =>
      let : IsEmpty ι := h
      simp
  | inr h =>
      let : Nonempty ι := h
      let i : ι := Classical.choice h
      rw [stdSimplexMeasure_eq_at i]
      unfold stdSimplexMeasureAt
      symm
      rw [Measure.restrict_map (measurable_stdSimplexCoordMap i)
        isClosed_stdSimplexAffineSet.measurableSet]
      have hp : stdSimplexCoordMap (R := ℝ) i ⁻¹'
          stdSimplexAffineSet (R := ℝ) = Set.univ := by
        ext x
        simp only [Set.mem_preimage, Set.mem_univ, iff_true]
        exact mem_fintypeAffineCoords_iff_sum.mpr (sum_stdSimplexCoordMap i x)
      rw [hp, Measure.restrict_univ]

/-- The coordinate Lebesgue measure is finite on the standard simplex. -/
instance : IsFiniteMeasure (stdSimplexMeasure.restrict (Convexity.StdSimplex.coordinateSet ℝ ι))
  := by
  refine ⟨?_⟩
  cases isEmpty_or_nonempty ι with
  | inl h =>
      let : IsEmpty ι := h
      simp
  | inr h =>
      let : Nonempty ι := h
      let i : ι := Classical.choice h
      rw [stdSimplexMeasure_restrict_stdSimplex i]
      rw [Measure.map_apply (measurable_stdSimplexCoordMap i) MeasurableSet.univ]
      rw [Set.preimage_univ, Measure.restrict_apply_univ]
      have hc : IsCompact (stdSimplexFreeCoords (R := ℝ) i) := by
        rw [← preimage_stdSimplexCoordMap i]
        exact (isClosedEmbedding_stdSimplexCoordMap i).isCompact_preimage
          (Convexity.StdSimplex.isCompact_coordinateSet ℝ ι)
      exact hc.measure_lt_top

/-- Permuting coordinates is a measure-preserving transformation of `stdSimplexMeasure`:
the map `x ↦ x ∘ σ` is measurable, and it pushes `stdSimplexMeasure` forward to itself. -/
theorem measurePreserving_stdSimplexMeasure_perm (σ : Equiv.Perm ι) :
  MeasurePreserving (fun x => x ∘ σ)
    stdSimplexMeasure stdSimplexMeasure := by
  refine ⟨continuous_pi (fun j => continuous_apply (σ j)) |>.measurable, ?_⟩
  cases isEmpty_or_nonempty ι with
  | inl h =>
      rw [stdSimplexMeasure_empty, Measure.map_zero]
  | inr h =>
      rw [stdSimplexMeasure_eq_at (σ (Classical.choice h)),
        stdSimplexMeasureAt_map_perm]
      exact stdSimplexMeasureAt_eq _ _

/-- The pushforward of `stdSimplexMeasure` under a coordinate permutation is
`stdSimplexMeasure` itself — the `Measure.map` equation extracted from
`measurePreserving_stdSimplexMeasure_perm`. -/
theorem stdSimplexMeasure_map_perm (σ : Equiv.Perm ι) :
  Measure.map (fun x ↦ x ∘ σ) stdSimplexMeasure = stdSimplexMeasure :=
  (measurePreserving_stdSimplexMeasure_perm σ).map_eq

open scoped Classical in
/-- Extended real evaluation of the measure of the standard simplex. The value is
$1/(k-1)!$ where `k = Fintype.card ι`. -/
@[simp] theorem stdSimplexMeasure_stdSimplex [Nonempty ι] :
  stdSimplexMeasure (Convexity.StdSimplex.coordinateSet ℝ ι) =
    1 / (Nat.factorial (Fintype.card ι - 1) : ENNReal) := by
  let i : ι := Classical.choice (inferInstance : Nonempty ι)
  rw [← Measure.restrict_apply_univ]
  rw [stdSimplexMeasure_restrict_stdSimplex i]
  rw [Measure.map_apply (measurable_stdSimplexCoordMap i) MeasurableSet.univ]
  rw [Set.preimage_univ, Measure.restrict_apply_univ]
  change volume (posSimplex {j : ι // j ≠ i} 1) = _
  rw [volume_posSimplex _ 1 (by positivity)]
  simp

/-- Real-valued form of the coordinate-volume formula for the standard simplex. -/
theorem stdSimplexMeasure_stdSimplex_toReal [Nonempty ι] :
  (stdSimplexMeasure (Convexity.StdSimplex.coordinateSet ℝ ι)).toReal =
    1 / (Nat.factorial (Fintype.card ι - 1) : ℝ) := by
  rw [stdSimplexMeasure_stdSimplex]
  simp

/-- The measure of the standard simplex is finite. -/
theorem stdSimplexMeasure_stdSimplex_ne_top [Nonempty ι] :
    stdSimplexMeasure (Convexity.StdSimplex.coordinateSet ℝ ι) ≠ ⊤ := by
  rw [stdSimplexMeasure_stdSimplex]
  exact ENNReal.div_ne_top ENNReal.one_ne_top (by positivity)

open scoped Classical in
/-- The projected measure of a measurable set: `stdSimplexMeasureAt i s` equals the volume
of the preimage of `s` under `stdSimplexCoordMap i`. -/
theorem stdSimplexMeasureAt_apply
    (i : ι) {s : Set (ι → ℝ)} (hs : MeasurableSet s) :
    stdSimplexMeasureAt i s =
      volume (stdSimplexCoordMap i ⁻¹' s) := by
  unfold stdSimplexMeasureAt
  exact Measure.map_apply (continuous_stdSimplexCoordMap i).measurable hs

open scoped Classical in
/-- The coordinate faces have measure 0. -/
theorem stdSimplexMeasure_coord_eq_zero [Nonempty ι] (i : ι) :
  stdSimplexMeasure {u : ι → ℝ | u i = 0} = 0 := by
  cases subsingleton_or_nontrivial ι with
  | inl hι =>
      let : Unique ι :=
        ⟨⟨Classical.choice (inferInstance : Nonempty ι)⟩, fun a => hι.elim _ _⟩
      rw [stdSimplexMeasure_unique]
      simp
  | inr hι =>
      obtain ⟨j, hji⟩ := exists_ne i
      rw [stdSimplexMeasure_eq_at j,
        stdSimplexMeasureAt_apply j
          (isClosed_eq (continuous_apply i) continuous_const).measurableSet]
      rw [volume_pi]
      have hs : stdSimplexCoordMap j ⁻¹' {u : ι → ℝ | u i = 0} =
          {x : {q : ι // q ≠ j} → ℝ | x ⟨i, hji.symm⟩ = 0} := by
        ext x
        change stdSimplexCoordMap j x i = 0 ↔ x ⟨i, hji.symm⟩ = 0
        rw [stdSimplexCoordMap_apply_of_ne j i hji.symm]
      rw [hs]
      exact Measure.pi_hyperplane (fun _ : {q : ι // q ≠ j} => volume) ⟨i, hji.symm⟩ 0

/-- Almost every point of the simplex has every coordinate strictly positive, with respect to
`stdSimplexMeasure` restricted to the simplex. -/
theorem ae_zero_lt_of_mem_stdSimplex [Nonempty ι] :
  ∀ᵐ u ∂stdSimplexMeasure.restrict (Convexity.StdSimplex.coordinateSet ℝ ι),
    ∀ i, 0 < u i := by
  rw [ae_all_iff]
  intro i
  have hne_full : ∀ᵐ u ∂stdSimplexMeasure, u i ≠ 0 := by
    rw [ae_iff]
    simpa only [not_ne_iff] using stdSimplexMeasure_coord_eq_zero i
  have hne : ∀ᵐ u ∂stdSimplexMeasure.restrict (Convexity.StdSimplex.coordinateSet ℝ ι), u i ≠ 0 :=
    (ae_mono Measure.restrict_le_self) hne_full
  filter_upwards
    [self_mem_ae_restrict
      (μ := stdSimplexMeasure)
      (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet, hne] with u hu hne
  exact lt_of_le_of_ne (hu.1 i) (Ne.symm hne)

/-- Coordinates belong to every `Lᵖ` space for a finite measure supported on the simplex. -/
theorem memLp_coordinate_of_restrict_stdSimplex
    {μ : Measure (ι → ℝ)} [IsFiniteMeasure μ]
    (hμ : μ.restrict (Convexity.StdSimplex.coordinateSet ℝ ι) = μ) (i : ι) (p : ENNReal) :
    MemLp (fun u : ι → ℝ => u i) p μ := by
  apply MemLp.of_bound (measurable_pi_apply i).aestronglyMeasurable 1
  have hmem : ∀ᵐ u ∂μ, u ∈ Convexity.StdSimplex.coordinateSet ℝ ι := by
    rw [← hμ]
    exact ae_restrict_mem (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet
  filter_upwards [hmem] with u hu
  rw [Real.norm_eq_abs, abs_of_nonneg (hu.1 i)]
  exact (Convexity.StdSimplex.mem_Icc_of_mem_coordinateSet hu i).2

end MeasureTheory.Measure

end StdSimplexCoordinateMeasure
