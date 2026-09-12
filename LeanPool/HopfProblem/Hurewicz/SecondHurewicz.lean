/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.Foundations.InvariantSubsetQuotient
import all LeanPool.HopfProblem.HomologyTheory.SingularMayerVietoris
import all LeanPool.HopfProblem.Foundations.TriangleRegularBaseFundamentalGroup
import all LeanPool.HopfProblem.HomologyTheory.FirstHurewicz1
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology4
import all LeanPool.HopfProblem.HomologyTheory.FirstHurewicz2
import all LeanPool.HopfProblem.Foundations.InvariantSubsetQuotient

/-!
# Hopf problem: hurewicz · second hurewicz

Supporting definitions and proofs for this stage of the six-sphere construction.
-/


open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

noncomputable section

namespace Mathoverflow1973

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

private def
    SecondHurewicz.SimplyConnected.simplexBoundary (n : ℕ) : Set (FirstHurewicz.Simplex n) :=
  {s | ∃ i : Fin (n + 1), s i = 0}

private abbrev SecondHurewicz.SimplyConnected.SimplexBoundary (n : ℕ) :=
  ↥(simplexBoundary n)

private def SecondHurewicz.SimplyConnected.bottomOrSide (n : ℕ) :
    Set (unitInterval × FirstHurewicz.Simplex n) :=
  {u | u.1 = 0 ∨ u.2 ∈ simplexBoundary n}

private theorem SecondHurewicz.SimplyConnected.isClosed_simplexBoundary (n : ℕ) :
    IsClosed (simplexBoundary n) := by
  have h : IsClosed (⋃ i : Fin (n + 1), {s : FirstHurewicz.Simplex n | s i = 0}) :=
    isClosed_iUnion_of_finite fun i =>
      isClosed_eq ((continuous_apply i).comp continuous_subtype_val) continuous_const
  simpa only [simplexBoundary, Set.ofPred_exists] using h

private theorem SecondHurewicz.SimplyConnected.simplexFace_mem_boundary (n : ℕ) (i : Fin (n + 2))
    (s : FirstHurewicz.Simplex n) : FirstHurewicz.simplexFace n i s ∈ simplexBoundary (n + 1) :=
  ⟨i, FirstHurewicz.simplexFace_apply_self n i s⟩

private def SecondHurewicz.SimplyConnected.bottomInclusion (n : ℕ) :
    C(FirstHurewicz.Simplex n, ↥(bottomOrSide n))
    where
  toFun s := ⟨(0, s), Or.inl rfl⟩
  continuous_toFun := (continuous_const.prodMk continuous_id).subtype_mk _

private def SecondHurewicz.SimplyConnected.sideInclusion (n : ℕ) :
    C(unitInterval × SimplexBoundary n, ↥(bottomOrSide n))
    where
  toFun u := ⟨(u.1, u.2.val), Or.inr u.2.property⟩
  continuous_toFun :=
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).subtype_mk _

private def HigherHurewicz.flatSimplexSet (n : ℕ) : Set (Fin n → ℝ) :=
  {v | (∀ i, 0 ≤ v i) ∧ ∑ i, v i ≤ 1}

private def HigherHurewicz.realCubeSet (n : ℕ) : Set (Fin n → ℝ) :=
  Set.Icc 0 1

private def HigherHurewicz.BasedSimplex (n : ℕ) {X : Type} [TopologicalSpace X] (x : X) :=
  { τ : C(FirstHurewicz.Simplex n, X) //
    ∀ s ∈ SecondHurewicz.SimplyConnected.simplexBoundary n, τ s = x }

private def HigherHurewicz.constantBasedSimplex (n : ℕ) {X : Type} [TopologicalSpace X] (x : X) :
    BasedSimplex n x :=
  ⟨ContinuousMap.const (FirstHurewicz.Simplex n) x, fun _ _ => rfl⟩

private theorem HigherHurewicz.convex_realCubeSet (n : ℕ) : Convex ℝ (realCubeSet n) :=
  convex_Icc 0 1

private theorem HigherHurewicz.isClosed_realCubeSet (n : ℕ) : IsClosed (realCubeSet n) :=
  isClosed_Icc

private theorem HigherHurewicz.isCompact_realCubeSet (n : ℕ) : IsCompact (realCubeSet n) :=
  CompactIccSpace.isCompact_Icc

private theorem HigherHurewicz.mem_interior_realCubeSet (n : ℕ) (v : Fin n → ℝ) :
    v ∈ interior (realCubeSet n) ↔ ∀ i, 0 < v i ∧ v i < 1 := by
  rw [realCubeSet, ← Set.pi_univ_Icc, interior_pi_set (Set.finite_univ)]
  simp only [Set.mem_pi, Set.mem_univ, forall_const, interior_Icc, Pi.zero_apply, Pi.one_apply,
    Set.mem_Ioo]

private theorem HigherHurewicz.interior_realCubeSet_nonempty (n : ℕ) :
    (interior (realCubeSet n)).Nonempty := by
  refine ⟨fun _ => 1 / 2, (mem_interior_realCubeSet n _).mpr ?_⟩
  intro i
  norm_num

private theorem HigherHurewicz.realCubeSet_mem_frontier_iff (n : ℕ) (v : ↥(realCubeSet n)) :
    v.val ∈ frontier (realCubeSet n) ↔ ∃ i, v.val i = 0 ∨ v.val i = 1 := by
  classical
  rw [frontier, (isClosed_realCubeSet n).closure_eq]
  simp only [Set.mem_sdiff, v.property, true_and, mem_interior_realCubeSet]
  constructor
  · intro h
    simp only [Classical.not_forall, not_and_or, not_lt] at h
    obtain ⟨i, h | h⟩ := h
    · exact ⟨i, Or.inl (le_antisymm h (v.property.1 i))⟩
    · exact ⟨i, Or.inr (le_antisymm (v.property.2 i) h)⟩
  · rintro ⟨i, h | h⟩ hi
    · have h0 := (hi i).1
      rw [h] at h0
      exact lt_irrefl _ h0
    · have h1 := (hi i).2
      rw [h] at h1
      exact lt_irrefl _ h1

private def HigherHurewicz.realCubeHomeomorph (n : ℕ) : ↥(realCubeSet n) ≃ₜ (Fin n → (unitInterval))
    where
  toFun v i := ⟨v.val i, v.property.1 i, v.property.2 i⟩
  invFun u := ⟨fun i => (u i : ℝ), fun i => (u i).property.1, fun i => (u i).property.2⟩
  left_inv v := Subtype.ext rfl
  right_inv
    u := by
    funext i
    apply Subtype.ext
    rfl
  continuous_toFun := by
    apply continuous_pi
    intro i
    exact ((continuous_apply i).comp continuous_subtype_val).subtype_mk _
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_pi fun i => continuous_subtype_val.comp (continuous_apply i)

private theorem HigherHurewicz.realCubeHomeomorph_mem_boundary_iff (n : ℕ) (v : ↥(realCubeSet n)) :
    realCubeHomeomorph n v ∈ Cube.boundary (Fin n) ↔ v.val ∈ frontier (realCubeSet n) := by
  rw [realCubeSet_mem_frontier_iff]
  constructor
  · rintro ⟨i, hi | hi⟩
    · exact ⟨i, Or.inl (congrArg (fun t : (unitInterval) => (t : ℝ)) hi)⟩
    · exact ⟨i, Or.inr (congrArg (fun t : (unitInterval) => (t : ℝ)) hi)⟩
  · rintro ⟨i, hi | hi⟩
    · exact ⟨i, Or.inl (Subtype.ext hi)⟩
    · exact ⟨i, Or.inr (Subtype.ext hi)⟩

private def
    HigherHurewicz.simplexFlat (n : ℕ) (s : FirstHurewicz.Simplex n) : ↥(flatSimplexSet n) :=
  ⟨fun i => s i.succ, by
    refine ⟨fun i => stdSimplex.zero_le s i.succ, ?_⟩
    have hs := stdSimplex.sum_eq_one s
    rw [Fin.sum_univ_succ] at hs
    have h0 := stdSimplex.zero_le s 0
    linarith⟩

private def
    HigherHurewicz.flatSimplex (n : ℕ) (v : ↥(flatSimplexSet n)) : FirstHurewicz.Simplex n :=
  ⟨Fin.cons (1 - ∑ i, v.val i) v.val, by
    constructor
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact sub_nonneg.mpr v.property.2
      · exact v.property.1 j
    · simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
      exact sub_add_cancel 1 _⟩

private theorem HigherHurewicz.continuous_simplexFlat (n : ℕ) : Continuous (simplexFlat n) := by
  apply Continuous.subtype_mk
  exact continuous_pi fun i => (continuous_apply i.succ).comp continuous_subtype_val

private theorem HigherHurewicz.continuous_flatSimplex (n : ℕ) : Continuous (flatSimplex n) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact
      continuous_const.sub <|
        continuous_finsetSum _ fun j _ => (continuous_apply j).comp continuous_subtype_val
  · exact (continuous_apply j).comp continuous_subtype_val

@[simp]
private theorem HigherHurewicz.flatSimplex_simplexFlat (n : ℕ) (s : FirstHurewicz.Simplex n) :
    flatSimplex n (simplexFlat n s) = s := by
  apply Subtype.ext
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · change 1 - ∑ j : Fin n, s j.succ = s 0
    have hs := stdSimplex.sum_eq_one s
    rw [Fin.sum_univ_succ] at hs
    linarith
  · rfl

@[simp]
private theorem HigherHurewicz.simplexFlat_flatSimplex (n : ℕ) (v : ↥(flatSimplexSet n)) :
    simplexFlat n (flatSimplex n v) = v := by
  apply Subtype.ext
  rfl

private def
    HigherHurewicz.simplexFlatHomeomorph (n : ℕ) : FirstHurewicz.Simplex n ≃ₜ ↥(flatSimplexSet n)
    where
  toFun := simplexFlat n
  invFun := flatSimplex n
  left_inv := flatSimplex_simplexFlat n
  right_inv := simplexFlat_flatSimplex n
  continuous_toFun := continuous_simplexFlat n
  continuous_invFun := continuous_flatSimplex n

private theorem HigherHurewicz.convex_flatSimplexSet (n : ℕ) : Convex ℝ (flatSimplexSet n) := by
  intro x hx y hy a b ha hb hab
  constructor
  · intro i
    exact add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i))
  · change ∑ i, (a * x i + b * y i) ≤ 1
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    calc
      a * ∑ i, x i + b * ∑ i, y i ≤ a * 1 + b * 1 :=
        add_le_add (mul_le_mul_of_nonneg_left hx.2 ha) (mul_le_mul_of_nonneg_left hy.2 hb)
      _ = 1 := by simpa only [mul_one] using hab

private theorem HigherHurewicz.isClosed_flatSimplexSet (n : ℕ) : IsClosed (flatSimplexSet n) := by
  have he : flatSimplexSet n = (⋂ i : Fin n, {v : Fin n → ℝ | 0 ≤ v i}) ∩ {v | ∑ i, v i ≤ 1} := by
    ext v
    simp only [flatSimplexSet, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [he]
  exact
    (isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)).inter
      (isClosed_le (by fun_prop) continuous_const)

private theorem HigherHurewicz.flatSimplexSet_subset_Icc (n : ℕ) :
    flatSimplexSet n ⊆ Set.Icc (0 : Fin n → ℝ) 1 := by
  intro v hv
  refine ⟨hv.1, fun i => ?_⟩
  exact (Finset.single_le_sum (fun j _ => hv.1 j) (Finset.mem_univ i)).trans hv.2

private theorem HigherHurewicz.isCompact_flatSimplexSet (n : ℕ) : IsCompact (flatSimplexSet n) :=
  CompactIccSpace.isCompact_Icc.of_isClosed_subset (isClosed_flatSimplexSet n)
    (flatSimplexSet_subset_Icc n)

private def HigherHurewicz.flatCoordinateSum_mo1973_5884 (n : ℕ) : (Fin n → ℝ) →L[ℝ] ℝ
    where
  toFun v := ∑ i, v i
  map_add' v w := Finset.sum_add_distrib
  map_smul' a v := by simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
  cont := by fun_prop

private theorem HigherHurewicz.flatCoordinateSum_succ_ne_zero_mo1973_5885 (n : ℕ) :
    flatCoordinateSum_mo1973_5884 (n + 1) ≠ 0 := by
  intro h
  have he := congrArg (fun f : (Fin (n + 1) → ℝ) →L[ℝ] ℝ => f 1) h
  have hn : (n : ℝ) + 1 = 0 := by simpa [flatCoordinateSum_mo1973_5884] using he
  exact (ne_of_gt (Nat.cast_add_one_pos n)) hn

private theorem HigherHurewicz.isOpen_flatSimplexStrict_mo1973_5886 (n : ℕ) :
    IsOpen {v : Fin n → ℝ | (∀ i, 0 < v i) ∧ ∑ i, v i < 1} := by
  have he :
    {v : Fin n → ℝ | (∀ i, 0 < v i) ∧ ∑ i, v i < 1} =
      (⋂ i : Fin n, {v : Fin n → ℝ | 0 < v i}) ∩ {v | ∑ i, v i < 1} := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [he]
  exact
    (isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_apply i)).inter
      (isOpen_lt (by fun_prop) continuous_const)

private theorem HigherHurewicz.interior_flatSimplexSet (n : ℕ) :
    interior (flatSimplexSet n) = {v : Fin n → ℝ | (∀ i, 0 < v i) ∧ ∑ i, v i < 1} := by
  apply Set.Subset.antisymm
  · intro v hv
    constructor
    · intro i
      have hi : v ∈ interior ((fun w : Fin n → ℝ => w i) ⁻¹' Set.Ici 0) :=
        interior_mono (fun w hw => hw.1 i) hv
      have h := (isOpenMap_eval i).interior_preimage_subset_preimage_interior hi
      simpa only [Set.mem_preimage, interior_Ici, Set.mem_Ioi] using h
    · cases n with
      | zero => simp
      | succ
        n =>
        have hs : v ∈ interior (flatCoordinateSum_mo1973_5884 (n + 1) ⁻¹' Set.Iic 1) :=
          interior_mono (fun w hw => hw.2) hv
        have h :=
          ((flatCoordinateSum_mo1973_5884 (n + 1)).isOpenMap_of_ne_zero
                (flatCoordinateSum_succ_ne_zero_mo1973_5885
                  n)).interior_preimage_subset_preimage_interior
            hs
        simpa only [Set.mem_preimage, interior_Iic, Set.mem_Iio, flatCoordinateSum_mo1973_5884,
          ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk] using h
  · exact
      (isOpen_flatSimplexStrict_mo1973_5886 n).subset_interior_iff.mpr
        (fun _ hv => ⟨fun i => (hv.1 i).le, hv.2.le⟩)

private theorem HigherHurewicz.interior_flatSimplexSet_nonempty (n : ℕ) :
    (interior (flatSimplexSet n)).Nonempty := by
  rw [interior_flatSimplexSet]
  have hn : 0 < (n : ℝ) + 1 := Nat.cast_add_one_pos n
  refine ⟨fun _ => 1 / ((n : ℝ) + 1), fun _ => one_div_pos.mpr hn, ?_⟩
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one_div] using (div_lt_one hn).mpr (lt_add_one (n : ℝ))

private theorem HigherHurewicz.simplexFlatHomeomorph_mem_interior_iff (n : ℕ)
    (s : FirstHurewicz.Simplex n) :
    (simplexFlatHomeomorph n s).val ∈ interior (flatSimplexSet n) ↔ ∀ i, 0 < s i := by
  rw [interior_flatSimplexSet]
  change ((∀ i : Fin n, 0 < s i.succ) ∧ ∑ i : Fin n, s i.succ < 1) ↔ _
  have hs := stdSimplex.sum_eq_one s
  rw [Fin.sum_univ_succ] at hs
  constructor
  · rintro ⟨hpos, hsum⟩ i
    refine Fin.cases ?_ (fun j => hpos j) i
    linarith
  · intro hpos
    exact ⟨fun i => hpos i.succ, by linarith [hpos 0]⟩

private theorem HigherHurewicz.simplexFlatHomeomorph_mem_frontier_iff (n : ℕ)
    (s : FirstHurewicz.Simplex n) :
    (simplexFlatHomeomorph n s).val ∈ frontier (flatSimplexSet n) ↔
      s ∈ SecondHurewicz.SimplyConnected.simplexBoundary n := by
  rw [frontier, (isClosed_flatSimplexSet n).closure_eq]
  change (_ ∧ _) ↔ ∃ i : Fin (n + 1), s i = 0
  rw [simplexFlatHomeomorph_mem_interior_iff]
  constructor
  · rintro ⟨_, hnot⟩
    classical
    push Not at hnot
    obtain ⟨i, hi⟩ := hnot
    exact ⟨i, le_antisymm hi (stdSimplex.zero_le s i)⟩
  · rintro ⟨i, hi⟩
    refine ⟨(simplexFlatHomeomorph n s).property, ?_⟩
    intro hpos
    have := hpos i
    rw [hi] at this
    exact (lt_irrefl 0) this

private theorem HigherHurewicz.exists_ambientSimplexCubeHomeomorph (n : ℕ) :
    ∃ e : (Fin n → ℝ) ≃ₜ (Fin n → ℝ),
      e '' flatSimplexSet n = realCubeSet n ∧
        e '' frontier (flatSimplexSet n) = frontier (realCubeSet n) := by
  obtain ⟨e, _, hclosed, hfrontier⟩ :=
    exists_homeomorph_image_eq (convex_flatSimplexSet n) (interior_flatSimplexSet_nonempty n)
      ((isCompact_flatSimplexSet n).isVonNBounded ℝ) (convex_realCubeSet n)
      (interior_realCubeSet_nonempty n) ((isCompact_realCubeSet n).isVonNBounded ℝ)
  refine ⟨e, ?_, hfrontier⟩
  simpa only [(isClosed_flatSimplexSet n).closure_eq, (isClosed_realCubeSet n).closure_eq] using
    hclosed

private def HigherHurewicz.ambientSimplexCubeHomeomorph (n : ℕ) : (Fin n → ℝ) ≃ₜ (Fin n → ℝ) :=
  Classical.choose (exists_ambientSimplexCubeHomeomorph n)

private theorem HigherHurewicz.ambientSimplexCubeHomeomorph_image (n : ℕ) :
    ambientSimplexCubeHomeomorph n '' flatSimplexSet n = realCubeSet n :=
  (Classical.choose_spec (exists_ambientSimplexCubeHomeomorph n)).1

private theorem HigherHurewicz.ambientSimplexCubeHomeomorph_image_frontier (n : ℕ) :
    ambientSimplexCubeHomeomorph n '' frontier (flatSimplexSet n) = frontier (realCubeSet n) :=
  (Classical.choose_spec (exists_ambientSimplexCubeHomeomorph n)).2

private theorem HigherHurewicz.ambientSimplexCubeHomeomorph_mem_iff (n : ℕ) (v : Fin n → ℝ) :
    v ∈ flatSimplexSet n ↔ ambientSimplexCubeHomeomorph n v ∈ realCubeSet n := by
  constructor
  · intro hv
    rw [← ambientSimplexCubeHomeomorph_image]
    exact ⟨v, hv, rfl⟩
  · intro hv
    rw [← ambientSimplexCubeHomeomorph_image] at hv
    obtain ⟨w, hw, he⟩ := hv
    exact (ambientSimplexCubeHomeomorph n).injective he ▸ hw

private theorem
    HigherHurewicz.ambientSimplexCubeHomeomorph_mem_frontier_iff (n : ℕ) (v : Fin n → ℝ) :
    v ∈ frontier (flatSimplexSet n) ↔
      ambientSimplexCubeHomeomorph n v ∈ frontier (realCubeSet n) := by
  constructor
  · intro hv
    rw [← ambientSimplexCubeHomeomorph_image_frontier]
    exact ⟨v, hv, rfl⟩
  · intro hv
    rw [← ambientSimplexCubeHomeomorph_image_frontier] at hv
    obtain ⟨w, hw, he⟩ := hv
    exact (ambientSimplexCubeHomeomorph n).injective he ▸ hw

private def HigherHurewicz.flatCubeHomeomorph (n : ℕ) : ↥(flatSimplexSet n) ≃ₜ ↥(realCubeSet n) :=
  (ambientSimplexCubeHomeomorph n).subtype (ambientSimplexCubeHomeomorph_mem_iff n)

private def HigherHurewicz.simplexCubeHomeomorph (n : ℕ) :
    FirstHurewicz.Simplex n ≃ₜ (Fin n → (unitInterval)) :=
  (simplexFlatHomeomorph n).trans ((flatCubeHomeomorph n).trans (realCubeHomeomorph n))

private theorem
    HigherHurewicz.simplexCubeHomeomorph_boundary_iff (n : ℕ) (s : FirstHurewicz.Simplex n) :
    simplexCubeHomeomorph n s ∈ Cube.boundary (Fin n) ↔
      s ∈ SecondHurewicz.SimplyConnected.simplexBoundary n := by
  change
    realCubeHomeomorph n (flatCubeHomeomorph n (simplexFlatHomeomorph n s)) ∈
        Cube.boundary (Fin n) ↔
      _
  rw [realCubeHomeomorph_mem_boundary_iff]
  change
    ambientSimplexCubeHomeomorph n (simplexFlatHomeomorph n s).val ∈ frontier (realCubeSet n) ↔ _
  rw [← ambientSimplexCubeHomeomorph_mem_frontier_iff, simplexFlatHomeomorph_mem_frontier_iff]

private theorem HigherHurewicz.simplexCubeHomeomorph_symm_boundary_iff (n : ℕ)
    (u : Fin n → (unitInterval)) :
    (simplexCubeHomeomorph n).symm u ∈ SecondHurewicz.SimplyConnected.simplexBoundary n ↔
      u ∈ Cube.boundary (Fin n) := by
  rw [← simplexCubeHomeomorph_boundary_iff, Homeomorph.apply_symm_apply]

private def
    SecondHurewicz.SimplyConnected.VerticesBased {X : Type} [TopologicalSpace X] (x : X) (n : ℕ)
    (smp : C(FirstHurewicz.Simplex n, X)) : Prop :=
  ∀ i : Fin (n + 1), smp (stdSimplex.vertex (S := ℝ) i) = x

private theorem
    SecondHurewicz.SimplyConnected.VerticesBased.face {X : Type} [TopologicalSpace X] {x : X}
    {n : ℕ} {smp : C(FirstHurewicz.Simplex (n + 1), X)}
    (h : SecondHurewicz.SimplyConnected.VerticesBased x (n + 1) smp) (i : Fin (n + 2)) :
    SecondHurewicz.SimplyConnected.VerticesBased x n (smp.comp (FirstHurewicz.simplexFace n i)) :=
  by
  intro j
  change smp (FirstHurewicz.simplexFace n i (stdSimplex.vertex (S := ℝ) j)) = x
  rw [FirstHurewicz.simplexFace_vertex]
  exact h (i.succAbove j)

@[simp]
private theorem
    SecondHurewicz.SimplyConnected.verticesBased_const {X : Type} [TopologicalSpace X] (x : X)
    (n : ℕ) : VerticesBased x n (ContinuousMap.const (FirstHurewicz.Simplex n) x) := fun _ => rfl

private theorem
    SecondHurewicz.SimplyConnected.verticesBased_zero_iff {X : Type} [TopologicalSpace X]
    {x : X} {smp : C(FirstHurewicz.Simplex 0, X)} :
    VerticesBased x 0 smp ↔ smp = ContinuousMap.const (FirstHurewicz.Simplex 0) x := by
  constructor
  · intro h
    apply ContinuousMap.ext
    intro s
    change smp s = x
    rw [FirstHurewicz.simplexZero_eq_vertex s]
    exact h 0
  · rintro rfl
    exact verticesBased_const x 0

private theorem SecondHurewicz.SimplyConnected.simplexVertex_exists_face (n : ℕ) (k : Fin (n + 2)) :
    ∃ i : Fin (n + 2),
      ∃ j : Fin (n + 1),
        FirstHurewicz.simplexFace n i (stdSimplex.vertex (S := ℝ) j) =
          stdSimplex.vertex (S := ℝ) k := by
  obtain ⟨i, hi⟩ := exists_ne k
  obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hi.symm
  refine ⟨i, j, ?_⟩
  rw [FirstHurewicz.simplexFace_vertex, hj]

private def SecondHurewicz.SimplyConnected.simplexFaceInverse (n : ℕ) (i : Fin (n + 2)) :
    C({ s : FirstHurewicz.Simplex (n + 1) // s i = 0 }, FirstHurewicz.Simplex n)
    where
  toFun
    s :=
    ⟨fun k => s.val (i.succAbove k),
      ⟨fun k => stdSimplex.zero_le s.val (i.succAbove k),
        by
        have hs := stdSimplex.sum_eq_one s.val
        rw [Fin.sum_univ_succAbove _ i, s.property, zero_add] at hs
        exact hs⟩⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro k
    have hc : Continuous (fun s : FirstHurewicz.Simplex (n + 1) => s (i.succAbove k)) :=
      (continuous_apply (i.succAbove k)).comp continuous_subtype_val
    exact hc.comp continuous_subtype_val

@[simp]
private theorem SecondHurewicz.SimplyConnected.simplexFace_inverse (n : ℕ) (i : Fin (n + 2))
    (s : { s : FirstHurewicz.Simplex (n + 1) // s i = 0 }) :
    FirstHurewicz.simplexFace n i (simplexFaceInverse n i s) = s.val := by
  apply Subtype.ext
  funext k
  change FirstHurewicz.simplexFace n i (simplexFaceInverse n i s) k = s.val k
  by_cases hk : k = i
  · subst k
    exact (FirstHurewicz.simplexFace_apply_self n i _).trans s.property.symm
  · obtain ⟨l, rfl⟩ := Fin.exists_succAbove_eq hk
    exact FirstHurewicz.simplexFace_apply_succAbove n i _ l

private theorem SecondHurewicz.SimplyConnected.simplexFace_range (n : ℕ) (i : Fin (n + 2)) :
    Set.range (FirstHurewicz.simplexFace n i) = {s : FirstHurewicz.Simplex (n + 1) | s i = 0} := by
  ext s
  constructor
  · rintro ⟨t, rfl⟩
    exact FirstHurewicz.simplexFace_apply_self n i t
  · intro hs
    exact ⟨simplexFaceInverse n i ⟨s, hs⟩, simplexFace_inverse n i ⟨s, hs⟩⟩

private theorem SecondHurewicz.SimplyConnected.simplexFace_injective (n : ℕ) (i : Fin (n + 2)) :
    Function.Injective (FirstHurewicz.simplexFace n i) := by
  intro s t h
  apply Subtype.ext
  funext k
  change s k = t k
  have hk := congrArg (fun u : FirstHurewicz.Simplex (n + 1) => u (i.succAbove k)) h
  simpa only [FirstHurewicz.simplexFace_apply_succAbove] using hk

private def SecondHurewicz.SimplyConnected.simplexFaceBoundary (n : ℕ) (i : Fin (n + 2)) :
    C(FirstHurewicz.Simplex n, SimplexBoundary (n + 1))
    where
  toFun s := ⟨FirstHurewicz.simplexFace n i s, simplexFace_mem_boundary n i s⟩
  continuous_toFun := (FirstHurewicz.simplexFace n i).continuous.subtype_mk _

private theorem SecondHurewicz.SimplyConnected.simplexBoundary_exists_face (n : ℕ)
    (s : SimplexBoundary (n + 1)) :
    ∃ i : Fin (n + 2), ∃ t : FirstHurewicz.Simplex n, simplexFaceBoundary n i t = s := by
  obtain ⟨i, hi⟩ := s.property
  have hmem : s.val ∈ Set.range (FirstHurewicz.simplexFace n i) := by
    rw [simplexFace_range]
    exact hi
  obtain ⟨t, ht⟩ := hmem
  exact ⟨i, t, Subtype.ext ht⟩

private def SecondHurewicz.SimplyConnected.simplexFaceCylinder (n : ℕ) (i : Fin (n + 2)) :
    C((unitInterval) × FirstHurewicz.Simplex n, (unitInterval) × SimplexBoundary (n + 1)) :=
  (ContinuousMap.id (unitInterval)).prodMap (simplexFaceBoundary n i)

private def SecondHurewicz.SimplyConnected.simplexFaceCover (n : ℕ) :
    C((Σ _i : Fin (n + 2), (unitInterval) × FirstHurewicz.Simplex n),
      (unitInterval) × SimplexBoundary (n + 1))
    where
  toFun a := simplexFaceCylinder n a.fst a.snd
  continuous_toFun := continuous_sigma fun i => (simplexFaceCylinder n i).continuous

private theorem SecondHurewicz.SimplyConnected.simplexFaceCover_surjective (n : ℕ) :
    Function.Surjective (simplexFaceCover n) := by
  rintro ⟨r, s⟩
  obtain ⟨i, t, rfl⟩ := simplexBoundary_exists_face n s
  exact ⟨⟨i, (r, t)⟩, rfl⟩

private theorem SecondHurewicz.SimplyConnected.simplexFaceCover_isQuotientMap (n : ℕ) :
    Topology.IsQuotientMap (simplexFaceCover n) :=
  Topology.IsQuotientMap.of_surjective_continuous (simplexFaceCover_surjective n)
    (simplexFaceCover n).continuous

private def SecondHurewicz.SimplyConnected.FaceCompatible {X : Type} [TopologicalSpace X] {n : ℕ}
    (F : Fin (n + 2) → C((unitInterval) × FirstHurewicz.Simplex n, X)) : Prop :=
  ∀ (i j : Fin (n + 2)) (s t : FirstHurewicz.Simplex n),
    FirstHurewicz.simplexFace n i s = FirstHurewicz.simplexFace n j t →
      ∀ r : (unitInterval), F i (r, s) = F j (r, t)

private def SecondHurewicz.SimplyConnected.faceFamilyMap {X : Type} [TopologicalSpace X] {n : ℕ}
    (F : Fin (n + 2) → C((unitInterval) × FirstHurewicz.Simplex n, X)) :
    C((Σ _i : Fin (n + 2), (unitInterval) × FirstHurewicz.Simplex n), X)
    where
  toFun a := F a.fst a.snd
  continuous_toFun := continuous_sigma fun i => (F i).continuous

private theorem SecondHurewicz.SimplyConnected.faceFamilyMap_factorsThrough {X : Type}
    [TopologicalSpace X] {n : ℕ}
    (F : Fin (n + 2) → C((unitInterval) × FirstHurewicz.Simplex n, X)) (hF : FaceCompatible F) :
    Function.FactorsThrough (faceFamilyMap F) (simplexFaceCover n) := by
  rintro ⟨i, r, s⟩ ⟨j, q, t⟩ h
  have hr : r = q := congrArg Prod.fst h
  have hs : FirstHurewicz.simplexFace n i s = FirstHurewicz.simplexFace n j t :=
    congrArg (fun u : (unitInterval) × SimplexBoundary (n + 1) => u.2.val) h
  subst q
  exact hF i j s t hs r

private def
    SecondHurewicz.SimplyConnected.glueFaceHomotopies {X : Type} [TopologicalSpace X] {n : ℕ}
    (F : Fin (n + 2) → C((unitInterval) × FirstHurewicz.Simplex n, X)) (hF : FaceCompatible F) :
    C((unitInterval) × SimplexBoundary (n + 1), X) :=
  (simplexFaceCover_isQuotientMap n).lift (faceFamilyMap F) (faceFamilyMap_factorsThrough F hF)

@[simp]
private theorem
    SecondHurewicz.SimplyConnected.glueFaceHomotopies_face {X : Type} [TopologicalSpace X]
    {n : ℕ} (F : Fin (n + 2) → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (hF : FaceCompatible F) (i : Fin (n + 2)) (r : (unitInterval)) (s : FirstHurewicz.Simplex n) :
    glueFaceHomotopies F hF (r, simplexFaceBoundary n i s) = F i (r, s) := by
  exact
    congrArg (fun f => f ⟨i, (r, s)⟩)
      ((simplexFaceCover_isQuotientMap n).lift_comp (faceFamilyMap F)
        (faceFamilyMap_factorsThrough F hF))

private theorem
    SecondHurewicz.SimplyConnected.glueFaceHomotopies_time {X : Type} [TopologicalSpace X]
    {n : ℕ} (F : Fin (n + 2) → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (hF : FaceCompatible F) (r : (unitInterval)) (g : FirstHurewicz.Simplex (n + 1) → X)
    (h :
      ∀ (i : Fin (n + 2)) (s : FirstHurewicz.Simplex n),
        F i (r, s) = g (FirstHurewicz.simplexFace n i s))
    (b : SimplexBoundary (n + 1)) : glueFaceHomotopies F hF (r, b) = g b.val := by
  obtain ⟨i, s, rfl⟩ := simplexBoundary_exists_face n b
  exact (glueFaceHomotopies_face F hF i r s).trans (h i s)

private theorem
    SecondHurewicz.SimplyConnected.glueFaceHomotopies_zero {X : Type} [TopologicalSpace X]
    {n : ℕ} (F : Fin (n + 2) → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (hF : FaceCompatible F) (g : C(FirstHurewicz.Simplex (n + 1), X))
    (h :
      ∀ (i : Fin (n + 2)) (s : FirstHurewicz.Simplex n),
        F i (0, s) = g (FirstHurewicz.simplexFace n i s))
    (b : SimplexBoundary (n + 1)) : glueFaceHomotopies F hF (0, b) = g b.val :=
  glueFaceHomotopies_time F hF 0 g h b

private theorem
    SecondHurewicz.SimplyConnected.glueFaceHomotopies_unique {X : Type} [TopologicalSpace X]
    {n : ℕ} (F : Fin (n + 2) → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (hF : FaceCompatible F) (G : C((unitInterval) × SimplexBoundary (n + 1), X))
    (hG :
      ∀ (i : Fin (n + 2)) (r : (unitInterval)) (s : FirstHurewicz.Simplex n),
        G (r, simplexFaceBoundary n i s) = F i (r, s)) :
    G = glueFaceHomotopies F hF := by
  ext u
  rcases u with ⟨r, b⟩
  obtain ⟨i, s, rfl⟩ := simplexBoundary_exists_face n b
  exact (hG i r s).trans (glueFaceHomotopies_face F hF i r s).symm

private theorem SecondHurewicz.SimplyConnected.simplexFace_intersection {n : ℕ} {i j : Fin (n + 2)}
    (hij : i ≤ j) {s t : FirstHurewicz.Simplex (n + 1)}
    (h :
      FirstHurewicz.simplexFace (n + 1) j.succ s =
        FirstHurewicz.simplexFace (n + 1) i.castSucc t) :
    ∃ u : FirstHurewicz.Simplex n,
      FirstHurewicz.simplexFace n i u = s ∧ FirstHurewicz.simplexFace n j u = t := by
  have hs : s i = 0 := by
    calc
      s i = FirstHurewicz.simplexFace (n + 1) j.succ s (j.succ.succAbove i) :=
        (FirstHurewicz.simplexFace_apply_succAbove (n + 1) j.succ s i).symm
      _ = FirstHurewicz.simplexFace (n + 1) j.succ s i.castSucc := by
        rw [Fin.succAbove_succ_of_le j i hij]
      _ = FirstHurewicz.simplexFace (n + 1) i.castSucc t i.castSucc :=
        (congrArg (fun v : FirstHurewicz.Simplex (n + 2) => v i.castSucc) h)
      _ = 0 := FirstHurewicz.simplexFace_apply_self (n + 1) i.castSucc t
  let u := simplexFaceInverse n i ⟨s, hs⟩
  have hu : FirstHurewicz.simplexFace n i u = s := simplexFace_inverse n i ⟨s, hs⟩
  refine ⟨u, hu, simplexFace_injective (n + 1) i.castSucc ?_⟩
  calc
    FirstHurewicz.simplexFace (n + 1) i.castSucc (FirstHurewicz.simplexFace n j u) =
        FirstHurewicz.simplexFace (n + 1) j.succ (FirstHurewicz.simplexFace n i u) :=
      (congrArg (fun f : C(FirstHurewicz.Simplex n, FirstHurewicz.Simplex (n + 2)) => f u)
          (PeriodTorusLineBundle.ChernCocycle.simplexFace_comp hij)).symm
    _ = FirstHurewicz.simplexFace (n + 1) j.succ s :=
      (congrArg (FirstHurewicz.simplexFace (n + 1) j.succ) hu)
    _ = FirstHurewicz.simplexFace (n + 1) i.castSucc t := h

private def SecondHurewicz.SimplyConnected.CofaceCompatible {X : Type} [TopologicalSpace X] {n : ℕ}
    (F : Fin (n + 3) → C((unitInterval) × FirstHurewicz.Simplex (n + 1), X)) : Prop :=
  ∀ (i j : Fin (n + 2)),
    i ≤ j →
      ∀ (r : (unitInterval)) (u : FirstHurewicz.Simplex n),
        F j.succ (r, FirstHurewicz.simplexFace n i u) =
          F i.castSucc (r, FirstHurewicz.simplexFace n j u)

private theorem SecondHurewicz.SimplyConnected.faceCompatible_of_cofaceCompatible_lt_mo1973_6084
    {X : Type} [TopologicalSpace X] {n : ℕ}
    (F : Fin (n + 3) → C((unitInterval) × FirstHurewicz.Simplex (n + 1), X))
    (hF : CofaceCompatible F) {a b : Fin (n + 3)} (hab : a < b)
    {s t : FirstHurewicz.Simplex (n + 1)}
    (hst : FirstHurewicz.simplexFace (n + 1) a s = FirstHurewicz.simplexFace (n + 1) b t)
    (r : (unitInterval)) : F a (r, s) = F b (r, t) := by
  obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.mpr (Fin.ne_last_of_lt hab)
  obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.mpr (Fin.ne_zero_of_lt hab)
  have hij : i ≤ j := Fin.castSucc_lt_succ_iff.mp hab
  obtain ⟨u, hu, hv⟩ := simplexFace_intersection hij hst.symm
  rw [← hu, ← hv]
  exact (hF i j hij r u).symm

private theorem SecondHurewicz.SimplyConnected.faceCompatible_of_cofaceCompatible {X : Type}
    [TopologicalSpace X] {n : ℕ}
    (F : Fin (n + 3) → C((unitInterval) × FirstHurewicz.Simplex (n + 1), X))
    (hF : CofaceCompatible F) : FaceCompatible F := by
  intro a b s t hst r
  rcases lt_trichotomy a b with hab | hab | hba
  · exact faceCompatible_of_cofaceCompatible_lt_mo1973_6084 F hF hab hst r
  · subst b
    exact congrArg (fun u => F a (r, u)) (simplexFace_injective (n + 1) a hst)
  · exact (faceCompatible_of_cofaceCompatible_lt_mo1973_6084 F hF hba hst.symm r).symm

private theorem SecondHurewicz.SimplyConnected.faceCompatible_zero {X : Type} [TopologicalSpace X]
    (F : Fin 2 → C((unitInterval) × FirstHurewicz.Simplex 0, X)) : FaceCompatible F := by
  intro i j s t hst r
  have hs : s = t := by
    rw [FirstHurewicz.simplexZero_eq_vertex s, FirstHurewicz.simplexZero_eq_vertex t]
  subst t
  fin_cases i <;> fin_cases j
  · rfl
  · have h : (1 : Fin 2) = 0 :=
      stdSimplex.vertex_injective
        ((FirstHurewicz.simplexFace_zero_zero s).symm.trans
          (hst.trans (FirstHurewicz.simplexFace_zero_one s)))
    exact False.elim ((by decide : (1 : Fin 2) ≠ 0) h)
  · have h : (0 : Fin 2) = 1 :=
      stdSimplex.vertex_injective
        ((FirstHurewicz.simplexFace_zero_one s).symm.trans
          (hst.trans (FirstHurewicz.simplexFace_zero_zero s)))
    exact False.elim ((by decide : (0 : Fin 2) ≠ 1) h)
  · rfl

private def
    SecondHurewicz.SimplyConnected.minimumCoordinate {n : ℕ} (s : FirstHurewicz.Simplex n) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun i => s i)

private theorem SecondHurewicz.SimplyConnected.minimumCoordinate_nonneg {n : ℕ}
    (s : FirstHurewicz.Simplex n) : 0 ≤ minimumCoordinate s :=
  Finset.le_inf' _ _ fun i _ => stdSimplex.zero_le s i

private theorem
    SecondHurewicz.SimplyConnected.minimumCoordinate_le {n : ℕ} (s : FirstHurewicz.Simplex n)
    (i : Fin (n + 1)) : minimumCoordinate s ≤ s i :=
  Finset.inf'_le _ (Finset.mem_univ i)

private theorem SecondHurewicz.SimplyConnected.exists_coordinate_eq_minimum {n : ℕ}
    (s : FirstHurewicz.Simplex n) : ∃ i : Fin (n + 1), s i = minimumCoordinate s := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (fun i => s i)
  exact ⟨i, hi.symm⟩

private theorem SecondHurewicz.SimplyConnected.continuous_minimumCoordinate (n : ℕ) :
    Continuous (minimumCoordinate (n := n)) :=
  Continuous.finset_inf'_apply _ fun i _ => (continuous_apply i).comp continuous_subtype_val

private theorem SecondHurewicz.SimplyConnected.minimumCoordinate_eq_zero_of_mem_boundary {n : ℕ}
    {s : FirstHurewicz.Simplex n} (hs : s ∈ simplexBoundary n) : minimumCoordinate s = 0 := by
  obtain ⟨i, hi⟩ := hs
  exact le_antisymm (hi ▸ minimumCoordinate_le s i) (minimumCoordinate_nonneg s)

private def SecondHurewicz.SimplyConnected.barycenterCoordinate (n : ℕ) : ℝ :=
  ((n : ℝ) + 1)⁻¹

private theorem
    SecondHurewicz.SimplyConnected.simplexCard_pos (n : ℕ) : 0 < (n : ℝ) + 1 := by positivity

private theorem SecondHurewicz.SimplyConnected.barycenterCoordinate_pos (n : ℕ) :
    0 < barycenterCoordinate n :=
  inv_pos.mpr (simplexCard_pos n)

private theorem SecondHurewicz.SimplyConnected.card_mul_barycenterCoordinate (n : ℕ) :
    ((n : ℝ) + 1) * barycenterCoordinate n = 1 :=
  mul_inv_cancel₀ (ne_of_gt (simplexCard_pos n))

private def SecondHurewicz.SimplyConnected.cylinderDenominator {n : ℕ}
    (u : unitInterval × FirstHurewicz.Simplex n) : ℝ :=
  Max.max (1 - (u.1 : ℝ) / 2) (1 - ((n : ℝ) + 1) * minimumCoordinate u.2)

private theorem SecondHurewicz.SimplyConnected.cylinderDenominator_half_le {n : ℕ}
    (u : unitInterval × FirstHurewicz.Simplex n) : 1 / 2 ≤ cylinderDenominator u := by
  have ht := u.1.property.2
  exact (show 1 / 2 ≤ 1 - (u.1 : ℝ) / 2 by linarith).trans (le_max_left _ _)

private theorem SecondHurewicz.SimplyConnected.cylinderDenominator_pos {n : ℕ}
    (u : unitInterval × FirstHurewicz.Simplex n) : 0 < cylinderDenominator u :=
  lt_of_lt_of_le (by norm_num) (cylinderDenominator_half_le u)

private theorem SecondHurewicz.SimplyConnected.cylinderDenominator_ne_zero {n : ℕ}
    (u : unitInterval × FirstHurewicz.Simplex n) : cylinderDenominator u ≠ 0 :=
  ne_of_gt (cylinderDenominator_pos u)

private theorem SecondHurewicz.SimplyConnected.cylinderDenominator_le_one {n : ℕ}
    (u : unitInterval × FirstHurewicz.Simplex n) : cylinderDenominator u ≤ 1 := by
  apply max_le
  · have ht := u.1.property.1
    linarith
  · have hm := mul_nonneg (le_of_lt (simplexCard_pos n)) (minimumCoordinate_nonneg u.2)
    linarith

private theorem SecondHurewicz.SimplyConnected.bottomDenominator_le {n : ℕ}
    (u : unitInterval × FirstHurewicz.Simplex n) : 1 - (u.1 : ℝ) / 2 ≤ cylinderDenominator u :=
  le_max_left _ _

private theorem SecondHurewicz.SimplyConnected.sideDenominator_le {n : ℕ}
    (u : unitInterval × FirstHurewicz.Simplex n) :
    1 - ((n : ℝ) + 1) * minimumCoordinate u.2 ≤ cylinderDenominator u :=
  le_max_right _ _

private theorem SecondHurewicz.SimplyConnected.coordinateDenominator_le {n : ℕ}
    (u : unitInterval × FirstHurewicz.Simplex n) (i : Fin (n + 1)) :
    1 - ((n : ℝ) + 1) * u.2 i ≤ cylinderDenominator u := by
  have hm := mul_le_mul_of_nonneg_left (minimumCoordinate_le u.2 i) (le_of_lt (simplexCard_pos n))
  exact (sub_le_sub_left hm 1).trans (sideDenominator_le u)

private theorem SecondHurewicz.SimplyConnected.continuous_cylinderDenominator (n : ℕ) :
    Continuous (cylinderDenominator (n := n)) :=
  (continuous_const.sub ((continuous_subtype_val.comp continuous_fst).div_const 2)).max
    (continuous_const.sub
      (continuous_const.mul ((continuous_minimumCoordinate n).comp continuous_snd)))

private theorem SecondHurewicz.SimplyConnected.cylinderDenominator_eq_one_of_mem {n : ℕ}
    {u : unitInterval × FirstHurewicz.Simplex n} (hu : u ∈ bottomOrSide n) :
    cylinderDenominator u = 1 := by
  apply le_antisymm (cylinderDenominator_le_one u)
  rcases hu with ht | hs
  · have h := bottomDenominator_le u
    rw [ht] at h
    change 1 - (0 : ℝ) / 2 ≤ cylinderDenominator u at h
    simpa only [zero_div, sub_zero] using h
  · have h := sideDenominator_le u
    simpa only [minimumCoordinate_eq_zero_of_mem_boundary hs, MulZeroClass.mul_zero,
      sub_zero] using h

private theorem SecondHurewicz.SimplyConnected.retractedTime_nonneg {n : ℕ}
    (u : unitInterval × FirstHurewicz.Simplex n) :
    0 ≤ ((u.1 : ℝ) + 2 * cylinderDenominator u - 2) / cylinderDenominator u := by
  apply div_nonneg _ (le_of_lt (cylinderDenominator_pos u))
  have h := bottomDenominator_le u
  linarith

private theorem SecondHurewicz.SimplyConnected.retractedTime_le_one {n : ℕ}
    (u : unitInterval × FirstHurewicz.Simplex n) :
    ((u.1 : ℝ) + 2 * cylinderDenominator u - 2) / cylinderDenominator u ≤ 1 := by
  apply (div_le_one (cylinderDenominator_pos u)).mpr
  have ht := u.1.property.2
  have hd := cylinderDenominator_le_one u
  linarith

private def SecondHurewicz.SimplyConnected.retractedTime {n : ℕ}
    (u : unitInterval × FirstHurewicz.Simplex n) : unitInterval :=
  ⟨((u.1 : ℝ) + 2 * cylinderDenominator u - 2) / cylinderDenominator u, retractedTime_nonneg u,
    retractedTime_le_one u⟩

private theorem SecondHurewicz.SimplyConnected.continuous_retractedTime (n : ℕ) :
    Continuous (retractedTime (n := n)) := by
  apply Continuous.subtype_mk
  exact
    (((continuous_subtype_val.comp continuous_fst).add
              (continuous_const.mul (continuous_cylinderDenominator n))).sub
          continuous_const).div
      (continuous_cylinderDenominator n) cylinderDenominator_ne_zero

private theorem SecondHurewicz.SimplyConnected.retractedCoordinate_numerator_nonneg {n : ℕ}
    (u : unitInterval × FirstHurewicz.Simplex n) (i : Fin (n + 1)) :
    0 ≤ u.2 i + (cylinderDenominator u - 1) * barycenterCoordinate n := by
  have h :=
    mul_nonneg (sub_nonneg.mpr (coordinateDenominator_le u i))
      (le_of_lt (barycenterCoordinate_pos n))
  have he :
    (cylinderDenominator u - (1 - ((n : ℝ) + 1) * u.2 i)) * barycenterCoordinate n =
      u.2 i + (cylinderDenominator u - 1) * barycenterCoordinate n := by
    calc
      _ =
          (cylinderDenominator u - 1) * barycenterCoordinate n +
            u.2 i * (((n : ℝ) + 1) * barycenterCoordinate n) := by ring
      _ = _ := by rw [card_mul_barycenterCoordinate]; ring
  exact he ▸ h

private theorem SecondHurewicz.SimplyConnected.retractedCoordinate_nonneg {n : ℕ}
    (u : unitInterval × FirstHurewicz.Simplex n) (i : Fin (n + 1)) :
    0 ≤ (u.2 i + (cylinderDenominator u - 1) * barycenterCoordinate n) / cylinderDenominator u :=
  div_nonneg (retractedCoordinate_numerator_nonneg u i) (le_of_lt (cylinderDenominator_pos u))

private theorem SecondHurewicz.SimplyConnected.retractedCoordinates_sum {n : ℕ}
    (u : unitInterval × FirstHurewicz.Simplex n) :
    ∑ i : Fin (n + 1),
        (u.2 i + (cylinderDenominator u - 1) * barycenterCoordinate n) / cylinderDenominator u =
      1 := by
  have hsum :
    (∑ _i : Fin (n + 1), (cylinderDenominator u - 1) * barycenterCoordinate n) =
      cylinderDenominator u - 1 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add,
      Nat.cast_one]
    calc
      _ = (cylinderDenominator u - 1) * (((n : ℝ) + 1) * barycenterCoordinate n) := by ring
      _ = _ := by rw [card_mul_barycenterCoordinate, mul_one]
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul, Finset.sum_add_distrib, stdSimplex.sum_eq_one, hsum]
  rw [show 1 + (cylinderDenominator u - 1) = cylinderDenominator u by ring,
    mul_inv_cancel₀ (cylinderDenominator_ne_zero u)]

private def SecondHurewicz.SimplyConnected.retractedSimplex {n : ℕ}
    (u : unitInterval × FirstHurewicz.Simplex n) : FirstHurewicz.Simplex n :=
  ⟨fun i =>
    (u.2 i + (cylinderDenominator u - 1) * barycenterCoordinate n) / cylinderDenominator u,
    retractedCoordinate_nonneg u, retractedCoordinates_sum u⟩

private theorem SecondHurewicz.SimplyConnected.continuous_retractedSimplex (n : ℕ) :
    Continuous (retractedSimplex (n := n)) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  exact
    (((continuous_apply i).comp (continuous_subtype_val.comp continuous_snd)).add
          (((continuous_cylinderDenominator n).sub continuous_const).mul continuous_const)).div
      (continuous_cylinderDenominator n) cylinderDenominator_ne_zero

private theorem SecondHurewicz.SimplyConnected.retractedTime_eq_of_mem {n : ℕ}
    {u : unitInterval × FirstHurewicz.Simplex n} (hu : u ∈ bottomOrSide n) :
    retractedTime u = u.1 := by
  apply Subtype.ext
  change ((u.1 : ℝ) + 2 * cylinderDenominator u - 2) / cylinderDenominator u = (u.1 : ℝ)
  rw [cylinderDenominator_eq_one_of_mem hu]
  ring

private theorem SecondHurewicz.SimplyConnected.retractedSimplex_eq_of_mem {n : ℕ}
    {u : unitInterval × FirstHurewicz.Simplex n} (hu : u ∈ bottomOrSide n) :
    retractedSimplex u = u.2 := by
  apply Subtype.ext
  funext i
  change
    (u.2 i + (cylinderDenominator u - 1) * barycenterCoordinate n) / cylinderDenominator u = u.2 i
  rw [cylinderDenominator_eq_one_of_mem hu]
  simp

private theorem SecondHurewicz.SimplyConnected.retracted_mem_bottomOrSide {n : ℕ}
    (u : unitInterval × FirstHurewicz.Simplex n) :
    (retractedTime u, retractedSimplex u) ∈ bottomOrSide n := by
  rcases le_total (1 - ((n : ℝ) + 1) * minimumCoordinate u.2) (1 - (u.1 : ℝ) / 2) with h | h
  · have hd : cylinderDenominator u = 1 - (u.1 : ℝ) / 2 := max_eq_left h
    left
    apply Subtype.ext
    change ((u.1 : ℝ) + 2 * cylinderDenominator u - 2) / cylinderDenominator u = 0
    have hn : (u.1 : ℝ) + 2 * cylinderDenominator u - 2 = 0 := by rw [hd]; ring
    rw [hn, zero_div]
  · have hd : cylinderDenominator u = 1 - ((n : ℝ) + 1) * minimumCoordinate u.2 := max_eq_right h
    right
    obtain ⟨i, hi⟩ := exists_coordinate_eq_minimum u.2
    refine ⟨i, ?_⟩
    change
      (u.2 i + (cylinderDenominator u - 1) * barycenterCoordinate n) / cylinderDenominator u = 0
    have hn : u.2 i + (cylinderDenominator u - 1) * barycenterCoordinate n = 0 := by
      rw [hi, hd]
      calc
        _ =
            minimumCoordinate u.2 -
              minimumCoordinate u.2 * (((n : ℝ) + 1) * barycenterCoordinate n) := by ring
        _ = 0 := by rw [card_mul_barycenterCoordinate]; ring
    rw [hn, zero_div]

private def SecondHurewicz.SimplyConnected.cylinderRetraction (n : ℕ) :
    C(unitInterval × FirstHurewicz.Simplex n, ↥(bottomOrSide n))
    where
  toFun u := ⟨(retractedTime u, retractedSimplex u), retracted_mem_bottomOrSide u⟩
  continuous_toFun :=
    ((continuous_retractedTime n).prodMk (continuous_retractedSimplex n)).subtype_mk _

private theorem SecondHurewicz.SimplyConnected.cylinderRetraction_val_of_mem {n : ℕ}
    {u : unitInterval × FirstHurewicz.Simplex n} (hu : u ∈ bottomOrSide n) :
    (cylinderRetraction n u).val = u :=
  Prod.ext (retractedTime_eq_of_mem hu) (retractedSimplex_eq_of_mem hu)

@[simp]
private theorem
    SecondHurewicz.SimplyConnected.cylinderRetraction_fix {n : ℕ} (u : ↥(bottomOrSide n)) :
    cylinderRetraction n u.val = u :=
  Subtype.ext (cylinderRetraction_val_of_mem u.property)

@[simp]
private theorem SecondHurewicz.SimplyConnected.cylinderRetraction_bottom (n : ℕ)
    (s : FirstHurewicz.Simplex n) : cylinderRetraction n (0, s) = bottomInclusion n s :=
  cylinderRetraction_fix (bottomInclusion n s)

@[simp]
private theorem SecondHurewicz.SimplyConnected.cylinderRetraction_side (n : ℕ) (t : unitInterval)
    (s : SimplexBoundary n) : cylinderRetraction n (t, s.val) = sideInclusion n (t, s) :=
  cylinderRetraction_fix (sideInclusion n (t, s))

private def SecondHurewicz.SimplyConnected.gluedBoundaryFunction_mo1973_6129 {n : ℕ} {X : Type*}
    [TopologicalSpace X] (f : C(FirstHurewicz.Simplex n, X))
    (h : C(unitInterval × SimplexBoundary n, X)) (u : ↥(bottomOrSide n)) : X :=
  if hu : u.val.1 = 0 then f u.val.2 else h (u.val.1, ⟨u.val.2, u.property.resolve_left hu⟩)

private theorem SecondHurewicz.SimplyConnected.gluedBoundaryFunction_bottom_mo1973_6130 {n : ℕ}
    {X : Type*} [TopologicalSpace X] (f : C(FirstHurewicz.Simplex n, X))
    (h : C(unitInterval × SimplexBoundary n, X)) (u : ↥(bottomOrSide n)) (hu : u.val.1 = 0) :
    gluedBoundaryFunction_mo1973_6129 f h u = f u.val.2 := by classical exact dite_eq_left hu

private theorem SecondHurewicz.SimplyConnected.gluedBoundaryFunction_side_mo1973_6131 {n : ℕ}
    {X : Type*} [TopologicalSpace X] (f : C(FirstHurewicz.Simplex n, X))
    (h : C(unitInterval × SimplexBoundary n, X)) (h0 : ∀ s, h (0, s) = f s.val)
    (u : ↥(bottomOrSide n)) (hu : u.val.2 ∈ simplexBoundary n) :
    gluedBoundaryFunction_mo1973_6129 f h u = h (u.val.1, ⟨u.val.2, hu⟩) := by
  classical
  by_cases ht : u.val.1 = 0
  · rw [gluedBoundaryFunction_bottom_mo1973_6130 f h u ht]
    simpa only [ht] using (h0 ⟨u.val.2, hu⟩).symm
  · exact dite_eq_right ht

private theorem SecondHurewicz.SimplyConnected.continuous_gluedBoundaryFunction_mo1973_6132
    {n : ℕ} {X : Type*} [TopologicalSpace X] (f : C(FirstHurewicz.Simplex n, X))
    (h : C(unitInterval × SimplexBoundary n, X)) (h0 : ∀ s, h (0, s) = f s.val) :
    Continuous (gluedBoundaryFunction_mo1973_6129 f h) := by
  let B : Set (↥(bottomOrSide n)) := {u | u.val.1 = 0}
  let S : Set (↥(bottomOrSide n)) := {u | u.val.2 ∈ simplexBoundary n}
  have hB : IsClosed B :=
    isClosed_eq (continuous_fst.comp continuous_subtype_val) continuous_const
  have hS : IsClosed S :=
    (isClosed_simplexBoundary n).preimage (continuous_snd.comp continuous_subtype_val)
  have hcover : B ∪ S = Set.univ := by
    apply Set.eq_univ_of_forall
    intro u
    exact u.property
  have hbottom : ContinuousOn (gluedBoundaryFunction_mo1973_6129 f h) B :=
    (f.continuous.comp (continuous_snd.comp continuous_subtype_val)).continuousOn.congr
      (fun u hu => gluedBoundaryFunction_bottom_mo1973_6130 f h u hu)
  have hside : ContinuousOn (gluedBoundaryFunction_mo1973_6129 f h) S := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have hc : Continuous (fun u : S => h (u.val.val.1, ⟨u.val.val.2, u.property⟩)) :=
      h.continuous.comp
        ((continuous_fst.comp (continuous_subtype_val.comp continuous_subtype_val)).prodMk
          ((continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk
            _))
    exact hc.congr fun u => (gluedBoundaryFunction_side_mo1973_6131 f h h0 u.val u.property).symm
  apply continuousOn_univ.mp
  rw [← hcover]
  exact hbottom.union_of_isClosed hside hB hS

private def SecondHurewicz.SimplyConnected.gluedBoundaryMap {n : ℕ} {X : Type*} [TopologicalSpace X]
    (f : C(FirstHurewicz.Simplex n, X)) (h : C(unitInterval × SimplexBoundary n, X))
    (h0 : ∀ s, h (0, s) = f s.val) : C(↥(bottomOrSide n), X)
    where
  toFun := gluedBoundaryFunction_mo1973_6129 f h
  continuous_toFun := continuous_gluedBoundaryFunction_mo1973_6132 f h h0

@[simp]
private theorem SecondHurewicz.SimplyConnected.gluedBoundaryMap_bottomInclusion {n : ℕ} {X : Type*}
    [TopologicalSpace X] (f : C(FirstHurewicz.Simplex n, X))
    (h : C(unitInterval × SimplexBoundary n, X)) (h0 : ∀ s, h (0, s) = f s.val)
    (s : FirstHurewicz.Simplex n) : gluedBoundaryMap f h h0 (bottomInclusion n s) = f s :=
  gluedBoundaryFunction_bottom_mo1973_6130 f h (bottomInclusion n s) rfl

@[simp]
private theorem SecondHurewicz.SimplyConnected.gluedBoundaryMap_sideInclusion {n : ℕ} {X : Type*}
    [TopologicalSpace X] (f : C(FirstHurewicz.Simplex n, X))
    (h : C(unitInterval × SimplexBoundary n, X)) (h0 : ∀ s, h (0, s) = f s.val)
    (u : unitInterval × SimplexBoundary n) : gluedBoundaryMap f h h0 (sideInclusion n u) = h u :=
  gluedBoundaryFunction_side_mo1973_6131 f h h0 (sideInclusion n u) u.2.property

private def
    SecondHurewicz.SimplyConnected.extendBoundaryHomotopy {n : ℕ} {X : Type*} [TopologicalSpace X]
    (f : C(FirstHurewicz.Simplex n, X)) (h : C(unitInterval × SimplexBoundary n, X))
    (h0 : ∀ s, h (0, s) = f s.val) : C(unitInterval × FirstHurewicz.Simplex n, X) :=
  (gluedBoundaryMap f h h0).comp (cylinderRetraction n)

@[simp]
private theorem SecondHurewicz.SimplyConnected.extendBoundaryHomotopy_bottom {n : ℕ} {X : Type*}
    [TopologicalSpace X] (f : C(FirstHurewicz.Simplex n, X))
    (h : C(unitInterval × SimplexBoundary n, X)) (h0 : ∀ s, h (0, s) = f s.val)
    (s : FirstHurewicz.Simplex n) : extendBoundaryHomotopy f h h0 (0, s) = f s := by
  change gluedBoundaryMap f h h0 (cylinderRetraction n (0, s)) = f s
  rw [cylinderRetraction_bottom, gluedBoundaryMap_bottomInclusion]

@[simp]
private theorem SecondHurewicz.SimplyConnected.extendBoundaryHomotopy_side {n : ℕ} {X : Type*}
    [TopologicalSpace X] (f : C(FirstHurewicz.Simplex n, X))
    (h : C(unitInterval × SimplexBoundary n, X)) (h0 : ∀ s, h (0, s) = f s.val) (t : unitInterval)
    (s : SimplexBoundary n) : extendBoundaryHomotopy f h h0 (t, s.val) = h (t, s) := by
  change gluedBoundaryMap f h h0 (cylinderRetraction n (t, s.val)) = h (t, s)
  rw [cylinderRetraction_side, gluedBoundaryMap_sideInclusion]

private theorem SecondHurewicz.SimplyConnected.extendBoundaryHomotopy_boundary {n : ℕ} {X : Type*}
    [TopologicalSpace X] (f : C(FirstHurewicz.Simplex n, X))
    (h : C(unitInterval × SimplexBoundary n, X)) (h0 : ∀ s, h (0, s) = f s.val) (t : unitInterval)
    (s : FirstHurewicz.Simplex n) (hs : s ∈ simplexBoundary n) :
    extendBoundaryHomotopy f h h0 (t, s) = h (t, ⟨s, hs⟩) :=
  extendBoundaryHomotopy_side f h h0 t ⟨s, hs⟩

private theorem SecondHurewicz.SimplyConnected.extendBoundaryHomotopy_face {n : ℕ} {X : Type*}
    [TopologicalSpace X] (f : C(FirstHurewicz.Simplex (n + 1), X))
    (h : C(unitInterval × SimplexBoundary (n + 1), X)) (h0 : ∀ s, h (0, s) = f s.val)
    (t : unitInterval) (i : Fin (n + 2)) (s : FirstHurewicz.Simplex n) :
    extendBoundaryHomotopy f h h0 (t, FirstHurewicz.simplexFace n i s) =
      h (t, ⟨FirstHurewicz.simplexFace n i s, simplexFace_mem_boundary n i s⟩) :=
  extendBoundaryHomotopy_boundary f h h0 t _ (simplexFace_mem_boundary n i s)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem
    SecondHurewicz.crossProductTriangle_zero_eq_zeroRight (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] :
    PeriodTorusHigherHomology.crossProductTriangle X Y 0 =
      PeriodTorusHigherHomology.crossProductZeroRight X Y 2 := by
  apply PeriodTorusHigherHomology.chainBilinearMap_ext X Y 2 0
  intro σ τ
  rw [PeriodTorusHigherHomology.crossProductTriangle_simplex,
    PeriodTorusHigherHomology.formalTriangleCrossProduct_zero_simplex_right,
    SingularMayerVietoris.formalMap_simplex,
    PeriodTorusHigherHomology.productAffineChainMap_simplex, FirstHurewicz.inducedChain_simplex,
    PeriodTorusHigherHomology.crossProductZeroRight_simplex]
  apply congrArg (FirstHurewicz.simplexChain (X × Y) 2)
  change
    (σ.prodMap τ).comp
        (PeriodTorusHigherHomology.productAffineSimplex
          (fun i =>
            (SingularMayerVietoris.stdVertices 2 i, SingularMayerVietoris.stdVertices 0 0))) =
      (PeriodTorusHigherHomology.crossInsertRight
            (PeriodTorusHigherHomology.zeroSimplexValue τ)).comp
        σ
  rw [PeriodTorusHigherHomology.productAffineSimplex_point_right,
    SingularMayerVietoris.affineSimplex_stdVertices, ContinuousMap.comp_id]
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem SecondHurewicz.crossProductTriangle_point_right (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] (a : FirstHurewicz.Chains X 2) (y : Y) :
    PeriodTorusHigherHomology.crossProductTriangle X Y 0 a (FirstHurewicz.pointChain y) =
      FirstHurewicz.inducedChain (PeriodTorusHigherHomology.crossInsertRight y) 2 a := by
  rw [crossProductTriangle_zero_eq_zeroRight, FirstHurewicz.pointChain,
    PeriodTorusHigherHomology.crossProductZeroRight_simplex_right]
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem SecondHurewicz.crossProductEdge_point_right (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] (a : FirstHurewicz.Chains X 1) (y : Y) :
    PeriodTorusHigherHomology.crossProductEdge X Y 0 a (FirstHurewicz.pointChain y) =
      FirstHurewicz.inducedChain (PeriodTorusHigherHomology.crossInsertRight y) 1 a := by
  rw [FirstHurewicz.pointChain, PeriodTorusHigherHomology.crossProductEdge_zero_simplex_right]
  rfl

private abbrev SecondHurewicz.Remaining :=
  { j : Fin 2 // j ≠ 0 }

private abbrev SecondHurewicz.BasedLoopSpace {X : Type} [TopologicalSpace X] (x : X) :=
  GenLoop Remaining X x

private def SecondHurewicz.evaluation {X : Type} [TopologicalSpace X] (x : X) :
    C(BasedLoopSpace x × (unitInterval), X)
    where
  toFun z := z.1 (fun _ => z.2)
  continuous_toFun := by fun_prop

@[simp]
private theorem SecondHurewicz.evaluation_zero {X : Type} [TopologicalSpace X] (x : X)
    (p : BasedLoopSpace x) : evaluation x (p, 0) = x :=
  GenLoop.boundary p _ ⟨⟨1, by decide⟩, Or.inl rfl⟩

@[simp]
private theorem SecondHurewicz.evaluation_one {X : Type} [TopologicalSpace X] (x : X)
    (p : BasedLoopSpace x) : evaluation x (p, 1) = x :=
  GenLoop.boundary p _ ⟨⟨1, by decide⟩, Or.inr rfl⟩

@[simp]
private theorem SecondHurewicz.evaluation_comp_right_zero {X : Type} [TopologicalSpace X] (x : X) :
    (evaluation x).comp (PeriodTorusHigherHomology.crossInsertRight (0 : (unitInterval))) =
      ContinuousMap.const (BasedLoopSpace x) x := by
  ext p
  exact evaluation_zero x p

@[simp]
private theorem SecondHurewicz.evaluation_comp_right_one {X : Type} [TopologicalSpace X] (x : X) :
    (evaluation x).comp (PeriodTorusHigherHomology.crossInsertRight (1 : (unitInterval))) =
      ContinuousMap.const (BasedLoopSpace x) x := by
  ext p
  exact evaluation_one x p

private def
    SecondHurewicz.squareCoordinates : C((unitInterval) × (unitInterval), Fin 2 → (unitInterval))
    where
  toFun z := Cube.insertAt (0 : Fin 2) (z.1, fun _ => z.2)
  continuous_toFun := by fun_prop

@[simp]
private theorem SecondHurewicz.squareCoordinates_zero (z : (unitInterval) × (unitInterval)) :
    squareCoordinates z 0 = z.1 := by
  simp [squareCoordinates, Cube.insertAt, Homeomorph.funSplitAt_symm_apply]

@[simp]
private theorem SecondHurewicz.squareCoordinates_one (z : (unitInterval) × (unitInterval)) :
    squareCoordinates z 1 = z.2 := by
  simp [squareCoordinates, Cube.insertAt, Homeomorph.funSplitAt_symm_apply]

private def
    SecondHurewicz.squareMap {X : Type} [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x) :
    C((unitInterval) × (unitInterval), X) :=
  p.val.comp squareCoordinates

private theorem SecondHurewicz.evaluation_comp_toLoop {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 2) X x) :
    (evaluation x).comp
        ((GenLoop.toLoop (0 : Fin 2) p).toContinuousMap.prodMap
          (ContinuousMap.id (unitInterval))) =
      squareMap p := by
  ext z
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def SecondHurewicz.intervalChain : FirstHurewicz.Chains (unitInterval) 1 :=
  FirstHurewicz.pathChain Path.id

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem SecondHurewicz.intervalChain_boundary :
    FirstHurewicz.boundaryOne (unitInterval) intervalChain =
      FirstHurewicz.pointChain (1 : (unitInterval)) -
        FirstHurewicz.pointChain (0 : (unitInterval)) :=
  FirstHurewicz.boundaryOne_pathChain Path.id

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem
    SecondHurewicz.evaluation_right_zero_chain {X : Type} [TopologicalSpace X] (x : X) (n : ℕ)
    (a : FirstHurewicz.Chains (BasedLoopSpace x) n) :
    FirstHurewicz.inducedChain (evaluation x) n
        (FirstHurewicz.inducedChain
          (PeriodTorusHigherHomology.crossInsertRight (0 : (unitInterval))) n a) =
      FirstHurewicz.inducedChain (ContinuousMap.const (BasedLoopSpace x) x) n a := by
  change
    ((FirstHurewicz.inducedChain (evaluation x) n).comp
          (FirstHurewicz.inducedChain
            (PeriodTorusHigherHomology.crossInsertRight (0 : (unitInterval))) n))
        a =
      _
  rw [← FirstHurewicz.inducedChain_comp, evaluation_comp_right_zero]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem
    SecondHurewicz.evaluation_right_one_chain {X : Type} [TopologicalSpace X] (x : X) (n : ℕ)
    (a : FirstHurewicz.Chains (BasedLoopSpace x) n) :
    FirstHurewicz.inducedChain (evaluation x) n
        (FirstHurewicz.inducedChain
          (PeriodTorusHigherHomology.crossInsertRight (1 : (unitInterval))) n a) =
      FirstHurewicz.inducedChain (ContinuousMap.const (BasedLoopSpace x) x) n a := by
  change
    ((FirstHurewicz.inducedChain (evaluation x) n).comp
          (FirstHurewicz.inducedChain
            (PeriodTorusHigherHomology.crossInsertRight (1 : (unitInterval))) n))
        a =
      _
  rw [← FirstHurewicz.inducedChain_comp, evaluation_comp_right_one]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem
    SecondHurewicz.evaluated_edge_endpoint_cancel {X : Type} [TopologicalSpace X] (x : X)
    (a : FirstHurewicz.Chains (BasedLoopSpace x) 1) :
    FirstHurewicz.inducedChain (evaluation x) 1
        (PeriodTorusHigherHomology.crossProductEdge (BasedLoopSpace x) (unitInterval) 0 a
          (FirstHurewicz.boundaryOne (unitInterval) intervalChain)) =
      0 := by
  simp only [intervalChain_boundary, map_sub, crossProductEdge_point_right,
    evaluation_right_one_chain, evaluation_right_zero_chain, sub_self]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem
    SecondHurewicz.evaluated_triangle_endpoint_cancel {X : Type} [TopologicalSpace X] (x : X)
    (a : FirstHurewicz.Chains (BasedLoopSpace x) 2) :
    FirstHurewicz.inducedChain (evaluation x) 2
        (PeriodTorusHigherHomology.crossProductTriangle (BasedLoopSpace x) (unitInterval) 0 a
          (FirstHurewicz.boundaryOne (unitInterval) intervalChain)) =
      0 := by
  simp only [intervalChain_boundary, map_sub, crossProductTriangle_point_right,
    evaluation_right_one_chain, evaluation_right_zero_chain, sub_self]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def SecondHurewicz.suspensionOne {X : Type} [TopologicalSpace X] (x : X) :
    FirstHurewicz.Chains (BasedLoopSpace x) 1 →ₗ[ℤ] FirstHurewicz.Chains X 2 :=
  (FirstHurewicz.inducedChain (evaluation x) 2).comp
    (PeriodTorusHigherHomology.integerBilinearRightApply
      (PeriodTorusHigherHomology.crossProductEdge (BasedLoopSpace x) (unitInterval) 1)
      intervalChain)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
private theorem SecondHurewicz.suspensionOne_apply {X : Type} [TopologicalSpace X] (x : X)
    (a : FirstHurewicz.Chains (BasedLoopSpace x) 1) :
    suspensionOne x a =
      FirstHurewicz.inducedChain (evaluation x) 2
        (PeriodTorusHigherHomology.crossProductEdge (BasedLoopSpace x) (unitInterval) 1 a
          intervalChain) :=
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def SecondHurewicz.suspensionTwo {X : Type} [TopologicalSpace X] (x : X) :
    FirstHurewicz.Chains (BasedLoopSpace x) 2 →ₗ[ℤ] FirstHurewicz.Chains X 3 :=
  (FirstHurewicz.inducedChain (evaluation x) 3).comp
    (PeriodTorusHigherHomology.integerBilinearRightApply
      (PeriodTorusHigherHomology.crossProductTriangle (BasedLoopSpace x) (unitInterval) 1)
      intervalChain)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
private theorem SecondHurewicz.suspensionTwo_apply {X : Type} [TopologicalSpace X] (x : X)
    (a : FirstHurewicz.Chains (BasedLoopSpace x) 2) :
    suspensionTwo x a =
      FirstHurewicz.inducedChain (evaluation x) 3
        (PeriodTorusHigherHomology.crossProductTriangle (BasedLoopSpace x) (unitInterval) 1 a
          intervalChain) :=
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem
    SecondHurewicz.boundaryTwo_suspensionOne_of_cycle {X : Type} [TopologicalSpace X] (x : X)
    (a : FirstHurewicz.Chains (BasedLoopSpace x) 1)
    (ha : FirstHurewicz.boundaryOne (BasedLoopSpace x) a = 0) :
    FirstHurewicz.boundaryTwo X (suspensionOne x a) = 0 := by
  change ((FirstHurewicz.singularComplex X).d 2 1).hom (suspensionOne x a) = 0
  rw [suspensionOne_apply, ← FirstHurewicz.inducedChain_boundary,
    PeriodTorusHigherHomology.crossProductEdge_boundary 0]
  change
    FirstHurewicz.inducedChain (evaluation x) 1
        (PeriodTorusHigherHomology.crossProductZeroLeft (BasedLoopSpace x) (unitInterval) 1
            (FirstHurewicz.boundaryOne (BasedLoopSpace x) a) intervalChain -
          PeriodTorusHigherHomology.crossProductEdge (BasedLoopSpace x) (unitInterval) 0 a
            (FirstHurewicz.boundaryOne (unitInterval) intervalChain)) =
      0
  rw [ha, map_zero, LinearMap.zero_apply, zero_sub, map_neg, evaluated_edge_endpoint_cancel,
    neg_zero]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem SecondHurewicz.boundaryThree_suspensionTwo {X : Type} [TopologicalSpace X] (x : X)
    (a : FirstHurewicz.Chains (BasedLoopSpace x) 2) :
    ((FirstHurewicz.singularComplex X).d 3 2).hom (suspensionTwo x a) =
      suspensionOne x (FirstHurewicz.boundaryTwo (BasedLoopSpace x) a) := by
  rw [suspensionTwo_apply, ← FirstHurewicz.inducedChain_boundary,
    PeriodTorusHigherHomology.crossProductTriangle_boundary 0]
  change
    FirstHurewicz.inducedChain (evaluation x) 2
        (PeriodTorusHigherHomology.crossProductEdge (BasedLoopSpace x) (unitInterval) 1
            (FirstHurewicz.boundaryTwo (BasedLoopSpace x) a) intervalChain +
          PeriodTorusHigherHomology.crossProductTriangle (BasedLoopSpace x) (unitInterval) 0 a
            (FirstHurewicz.boundaryOne (unitInterval) intervalChain)) =
      _
  rw [map_add, evaluated_triangle_endpoint_cancel, add_zero]
  rfl

private def SecondHurewicz.pathSquareCycle {X : Type} [TopologicalSpace X] (x : X)
    (p : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const) :
    SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 2 :=
  SingularMayerVietoris.ModuleHomology.mkCycle (FirstHurewicz.singularComplex X) 2
    (suspensionOne x (FirstHurewicz.pathChain p))
    (boundaryTwo_suspensionOne_of_cycle x (FirstHurewicz.pathChain p)
      (FirstHurewicz.boundaryOne_loop p))

@[simp]
private theorem SecondHurewicz.pathSquareCycle_val {X : Type} [TopologicalSpace X] (x : X)
    (p : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const) :
    (pathSquareCycle x p).1 = suspensionOne x (FirstHurewicz.pathChain p) :=
  rfl

private def SecondHurewicz.pathSquareClass {X : Type} [TopologicalSpace X] (x : X)
    (p : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const) :
    SingularMayerVietoris.SingularHomology X 2 :=
  SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 2
    (pathSquareCycle x p)

private theorem SecondHurewicz.pathSquare_homotopy_boundary {X : Type} [TopologicalSpace X] (x : X)
    {p q : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const} (H : p.Homotopy q) :
    ((FirstHurewicz.singularComplex X).d 3 2).hom
        (suspensionTwo x (FirstHurewicz.homotopyChain H)) =
      (pathSquareCycle x p).1 - (pathSquareCycle x q).1 := by
  rw [boundaryThree_suspensionTwo, FirstHurewicz.boundaryTwo_loopHomotopy, map_sub]
  rfl

private theorem SecondHurewicz.pathSquareClass_homotopy {X : Type} [TopologicalSpace X] (x : X)
    {p q : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const} (H : p.Homotopy q) :
    pathSquareClass x p = pathSquareClass x q :=
  (SingularMayerVietoris.ModuleHomology.cycleClass_eq_iff (FirstHurewicz.singularComplex X) 2 _
        _).mpr
    ⟨suspensionTwo x (FirstHurewicz.homotopyChain H), pathSquare_homotopy_boundary x H⟩

private theorem SecondHurewicz.pathSquareClass_homotopic {X : Type} [TopologicalSpace X] (x : X)
    {p q : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const} (h : p.Homotopic q) :
    pathSquareClass x p = pathSquareClass x q := by
  obtain ⟨H⟩ := h
  exact pathSquareClass_homotopy x H

@[simp]
private theorem SecondHurewicz.pathSquareClass_refl {X : Type} [TopologicalSpace X] (x : X) :
    pathSquareClass x (Path.refl (GenLoop.const : BasedLoopSpace x)) = 0 := by
  apply
    (SingularMayerVietoris.ModuleHomology.cycleClass_eq_zero_iff (FirstHurewicz.singularComplex X)
        2 _).mpr
  refine
    ⟨suspensionTwo x (FirstHurewicz.constantTriangleChain (GenLoop.const : BasedLoopSpace x)), ?_⟩
  rw [boundaryThree_suspensionTwo, FirstHurewicz.boundaryTwo_constantTriangleChain]
  rfl

private theorem SecondHurewicz.pathSquare_concat_boundary {X : Type} [TopologicalSpace X] (x : X)
    (p q : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const) :
    ((FirstHurewicz.singularComplex X).d 3 2).hom
        (-suspensionTwo x (FirstHurewicz.concatChain p q)) =
      (pathSquareCycle x (p.trans q)).1 - ((pathSquareCycle x p).1 + (pathSquareCycle x q).1) := by
  rw [map_neg, boundaryThree_suspensionTwo, FirstHurewicz.boundaryTwo_concatChain, map_add,
    map_sub]
  simp only [pathSquareCycle_val]
  abel

private theorem SecondHurewicz.pathSquareClass_trans {X : Type} [TopologicalSpace X] (x : X)
    (p q : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const) :
    pathSquareClass x (p.trans q) = pathSquareClass x p + pathSquareClass x q := by
  unfold pathSquareClass
  rw [← map_add]
  apply
    (SingularMayerVietoris.ModuleHomology.cycleClass_eq_iff (FirstHurewicz.singularComplex X) 2 _
        _).mpr
  exact ⟨-suspensionTwo x (FirstHurewicz.concatChain p q), pathSquare_concat_boundary x p q⟩

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def SecondHurewicz.productSquareChain :
    FirstHurewicz.Chains ((unitInterval) × (unitInterval)) 2 :=
  PeriodTorusHigherHomology.crossProductEdge (unitInterval) (unitInterval) 1 intervalChain
    intervalChain

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem SecondHurewicz.productSquareChain_boundary :
    FirstHurewicz.boundaryTwo ((unitInterval) × (unitInterval)) productSquareChain =
      FirstHurewicz.inducedChain (PeriodTorusHigherHomology.crossInsertLeft (1 : (unitInterval)))
            1 intervalChain -
          FirstHurewicz.inducedChain
            (PeriodTorusHigherHomology.crossInsertLeft (0 : (unitInterval))) 1 intervalChain -
        (FirstHurewicz.inducedChain
            (PeriodTorusHigherHomology.crossInsertRight (1 : (unitInterval))) 1 intervalChain -
          FirstHurewicz.inducedChain
            (PeriodTorusHigherHomology.crossInsertRight (0 : (unitInterval))) 1 intervalChain) := by
  change
    ((FirstHurewicz.singularComplex ((unitInterval) × (unitInterval))).d 2 1).hom
        (PeriodTorusHigherHomology.crossProductEdge (unitInterval) (unitInterval) 1 intervalChain
          intervalChain) =
      _
  rw [PeriodTorusHigherHomology.crossProductEdge_boundary 0]
  change
    PeriodTorusHigherHomology.crossProductZeroLeft (unitInterval) (unitInterval) 1
          (FirstHurewicz.boundaryOne (unitInterval) intervalChain) intervalChain -
        PeriodTorusHigherHomology.crossProductEdge (unitInterval) (unitInterval) 0 intervalChain
          (FirstHurewicz.boundaryOne (unitInterval) intervalChain) =
      _
  simp only [intervalChain_boundary, map_sub, LinearMap.sub_apply, crossProductEdge_point_right]
  simp only [FirstHurewicz.pointChain,
    PeriodTorusHigherHomology.crossProductZeroLeft_simplex_left]
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def
    SecondHurewicz.fundamentalSquareChain : FirstHurewicz.Chains (Fin 2 → (unitInterval)) 2 :=
  FirstHurewicz.inducedChain squareCoordinates 2 productSquareChain

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem SecondHurewicz.induced_intervalChain {X : Type} [TopologicalSpace X] {a b : X}
    (p : Path a b) :
    FirstHurewicz.inducedChain p.toContinuousMap 1 intervalChain = FirstHurewicz.pathChain p := by
  rw [intervalChain, FirstHurewicz.pathChain, FirstHurewicz.inducedChain_simplex]
  apply congrArg (FirstHurewicz.simplexChain X 1)
  ext s
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem SecondHurewicz.suspensionOne_toLoop {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 2) X x) :
    suspensionOne x (FirstHurewicz.pathChain (GenLoop.toLoop (0 : Fin 2) p)) =
      FirstHurewicz.inducedChain (squareMap p) 2 productSquareChain := by
  have h :=
    PeriodTorusHigherHomology.crossProductEdge_natural
      (GenLoop.toLoop (0 : Fin 2) p).toContinuousMap (ContinuousMap.id (unitInterval)) 1
      intervalChain intervalChain
  rw [induced_intervalChain, FirstHurewicz.inducedChain_id, LinearMap.id_apply] at h
  rw [suspensionOne_apply, ← h]
  change
    ((FirstHurewicz.inducedChain (evaluation x) 2).comp
          (FirstHurewicz.inducedChain
            ((GenLoop.toLoop (0 : Fin 2) p).toContinuousMap.prodMap
              (ContinuousMap.id (unitInterval)))
            2))
        productSquareChain =
      _
  rw [← FirstHurewicz.inducedChain_comp, evaluation_comp_toLoop]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def
    SecondHurewicz.squareChain {X : Type} [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x) :
    FirstHurewicz.Chains X 2 :=
  suspensionOne x (FirstHurewicz.pathChain (GenLoop.toLoop (0 : Fin 2) p))

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem SecondHurewicz.squareChain_boundary {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 2) X x) : FirstHurewicz.boundaryTwo X (squareChain p) = 0 :=
  boundaryTwo_suspensionOne_of_cycle x _ (FirstHurewicz.boundaryOne_loop (GenLoop.toLoop 0 p))

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def
    SecondHurewicz.squareCycle {X : Type} [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x) :
    SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 2 :=
  pathSquareCycle x (GenLoop.toLoop (0 : Fin 2) p)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def SecondHurewicz.squareHomologyClass {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 2) X x) : SingularMayerVietoris.SingularHomology X 2 :=
  SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 2
    (squareCycle p)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem
    SecondHurewicz.squareHomologyClass_eq_pathSquareClass {X : Type} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) :
    squareHomologyClass p = pathSquareClass x (GenLoop.toLoop (0 : Fin 2) p) :=
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem SecondHurewicz.squareHomologyClass_homotopic {X : Type} [TopologicalSpace X] {x : X}
    {p q : GenLoop (Fin 2) X x} (h : GenLoop.Homotopic p q) :
    squareHomologyClass p = squareHomologyClass q :=
  pathSquareClass_homotopic x (GenLoop.homotopicTo (0 : Fin 2) h)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem SecondHurewicz.toLoop_const {X : Type} [TopologicalSpace X] {x : X} :
    GenLoop.toLoop (0 : Fin 2) (GenLoop.const : GenLoop (Fin 2) X x) =
      Path.refl (GenLoop.const : BasedLoopSpace x) := by
  apply Path.ext
  funext t
  apply GenLoop.ext
  intro u
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
private theorem SecondHurewicz.squareHomologyClass_const {X : Type} [TopologicalSpace X] {x : X} :
    squareHomologyClass (GenLoop.const : GenLoop (Fin 2) X x) = 0 := by
  rw [squareHomologyClass_eq_pathSquareClass, toLoop_const, pathSquareClass_refl]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem SecondHurewicz.toLoop_transAt {X : Type} [TopologicalSpace X] {x : X}
    (p q : GenLoop (Fin 2) X x) :
    GenLoop.toLoop (0 : Fin 2) (GenLoop.transAt (0 : Fin 2) p q) =
      (GenLoop.toLoop (0 : Fin 2) p).trans (GenLoop.toLoop (0 : Fin 2) q) := by
  have h :=
    congrArg (GenLoop.toLoop (0 : Fin 2))
      (GenLoop.fromLoop_trans_toLoop (i := (0 : Fin 2)) (p := p) (q := q))
  rw [GenLoop.to_from] at h
  exact h.symm

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem SecondHurewicz.squareHomologyClass_transAt {X : Type} [TopologicalSpace X] {x : X}
    (p q : GenLoop (Fin 2) X x) :
    squareHomologyClass (GenLoop.transAt (0 : Fin 2) p q) =
      squareHomologyClass p + squareHomologyClass q := by
  simp only [squareHomologyClass_eq_pathSquareClass, toLoop_transAt, pathSquareClass_trans]

private def SecondHurewicz.mapGenLoop {N X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) : C(GenLoop N X x, GenLoop N Y (f x))
    where
  toFun p := ⟨f.comp p.val, fun t ht => congrArg f (p.property t ht)⟩
  continuous_toFun :=
    ((ContinuousMap.continuous_postcomp f).comp continuous_subtype_val).subtype_mk _

@[simp]
private theorem
    SecondHurewicz.mapGenLoop_val {N X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) (p : GenLoop N X x) : (mapGenLoop f x p).val = f.comp p.val :=
  rfl

@[simp]
private theorem
    SecondHurewicz.mapGenLoop_const {N X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) : mapGenLoop (N := N) f x GenLoop.const = GenLoop.const :=
  rfl

private theorem SecondHurewicz.mapGenLoop_homotopic {N X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (x : X) {p q : GenLoop N X x} (h : GenLoop.Homotopic p q) :
    GenLoop.Homotopic (mapGenLoop f x p) (mapGenLoop f x q) :=
  h.comp_continuousMap f

@[simp]
private theorem
    SecondHurewicz.mapGenLoop_transAt {N X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [DecidableEq N] (f : C(X, Y)) (x : X) (i : N) (p q : GenLoop N X x) :
    mapGenLoop f x (GenLoop.transAt i p q) =
      GenLoop.transAt i (mapGenLoop f x p) (mapGenLoop f x q) := by
  apply GenLoop.ext
  intro t
  change f (if (t i : ℝ) ≤ 1 / 2 then _ else _) = if (t i : ℝ) ≤ 1 / 2 then _ else _
  split_ifs <;> rfl

private def SecondHurewicz.hurewiczFunction {X : Type} [TopologicalSpace X] (x : X) :
    π_ 2 X x → SingularMayerVietoris.SingularHomology X 2 :=
  Quotient.lift squareHomologyClass (fun _ _ h => squareHomologyClass_homotopic h)

private def SecondHurewicz.hurewiczPi2 {X : Type} [TopologicalSpace X] (x : X) :
    π_ 2 X x →* Multiplicative (SingularMayerVietoris.SingularHomology X 2)
    where
  toFun a := Multiplicative.ofAdd (hurewiczFunction x a)
  map_one' := congrArg Multiplicative.ofAdd (squareHomologyClass_const (x := x))
  map_mul' a
    b := by
    refine Quotient.inductionOn₂ a b fun p q => ?_
    refine
      (congrArg (fun c : π_ 2 X x => Multiplicative.ofAdd (hurewiczFunction x c))
            (HomotopyGroup.mul_spec (i := (0 : Fin 2)) (p := p) (q := q))).trans
        ?_
    change
      Multiplicative.ofAdd (squareHomologyClass (GenLoop.transAt (0 : Fin 2) q p)) =
        Multiplicative.ofAdd (squareHomologyClass p + squareHomologyClass q)
    rw [squareHomologyClass_transAt, add_comm]

private def SecondHurewicz.hurewiczMap {X : Type} [TopologicalSpace X] (x : X) :
    Additive (π_ 2 X x) →ₗ[ℤ] SingularMayerVietoris.SingularHomology X 2
    where
  toFun := (hurewiczPi2 x).toAdditiveLeft
  map_add' := (hurewiczPi2 x).toAdditiveLeft.map_add
  map_smul' n a := by simpa using map_intCast_smul (hurewiczPi2 x).toAdditiveLeft ℤ ℤ n a

private theorem SecondHurewicz.hurewiczMap_representative {X : Type} [TopologicalSpace X] (x : X)
    (p : GenLoop (Fin 2) X x) :
    hurewiczMap x (Additive.ofMul (⟦p⟧ : π_ 2 X x)) =
      SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 2
        (squareCycle p) :=
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def SecondHurewicz.SimplyConnected.timeSlice {A X : Type} [TopologicalSpace A]
    [TopologicalSpace X] (H : C((unitInterval) × A, X)) (t : (unitInterval)) : C(A, X) :=
  H.comp (PeriodTorusHigherHomology.crossInsertLeft t)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem
    SecondHurewicz.SimplyConnected.crossPoint_left {A : Type} [TopologicalSpace A] (n : ℕ)
    (t : (unitInterval)) (c : FirstHurewicz.Chains A n) :
    PeriodTorusHigherHomology.crossProductZeroLeft (unitInterval) A n (FirstHurewicz.pointChain t)
        c =
      FirstHurewicz.inducedChain (PeriodTorusHigherHomology.crossInsertLeft t) n c := by
  rw [FirstHurewicz.pointChain, PeriodTorusHigherHomology.crossProductZeroLeft_simplex_left]
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem
    SecondHurewicz.SimplyConnected.inducedChain_timeSlice {A X : Type} [TopologicalSpace A]
    [TopologicalSpace X] (H : C((unitInterval) × A, X)) (t : (unitInterval)) (n : ℕ)
    (c : FirstHurewicz.Chains A n) :
    FirstHurewicz.inducedChain H n
        (FirstHurewicz.inducedChain (PeriodTorusHigherHomology.crossInsertLeft t) n c) =
      FirstHurewicz.inducedChain (timeSlice H t) n c := by
  change
    ((FirstHurewicz.inducedChain H n).comp
          (FirstHurewicz.inducedChain (PeriodTorusHigherHomology.crossInsertLeft t) n))
        c =
      _
  rw [← FirstHurewicz.inducedChain_comp]
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def SecondHurewicz.SimplyConnected.prismOperator {A X : Type} [TopologicalSpace A]
    [TopologicalSpace X] (n : ℕ) (H : C((unitInterval) × A, X)) :
    FirstHurewicz.Chains A n →ₗ[ℤ] FirstHurewicz.Chains X (n + 1) :=
  (FirstHurewicz.inducedChain H (n + 1)).comp
    (PeriodTorusHigherHomology.crossProductEdge (unitInterval) A n SecondHurewicz.intervalChain)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
private theorem SecondHurewicz.SimplyConnected.prismOperator_apply {A X : Type} [TopologicalSpace A]
    [TopologicalSpace X] (n : ℕ) (H : C((unitInterval) × A, X)) (c : FirstHurewicz.Chains A n) :
    prismOperator n H c =
      FirstHurewicz.inducedChain H (n + 1)
        (PeriodTorusHigherHomology.crossProductEdge (unitInterval) A n
          SecondHurewicz.intervalChain c) :=
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem
    SecondHurewicz.SimplyConnected.prismOperator_boundary {A X : Type} [TopologicalSpace A]
    [TopologicalSpace X] (n : ℕ) (H : C((unitInterval) × A, X))
    (c : FirstHurewicz.Chains A (n + 1)) :
    ((FirstHurewicz.singularComplex X).d (n + 2) (n + 1)).hom (prismOperator (n + 1) H c) =
      FirstHurewicz.inducedChain (timeSlice H 1) (n + 1) c -
          FirstHurewicz.inducedChain (timeSlice H 0) (n + 1) c -
        prismOperator n H (((FirstHurewicz.singularComplex A).d (n + 1) n).hom c) := by
  rw [prismOperator_apply, ← FirstHurewicz.inducedChain_boundary,
    PeriodTorusHigherHomology.crossProductEdge_boundary n]
  change
    FirstHurewicz.inducedChain H (n + 1)
        (PeriodTorusHigherHomology.crossProductZeroLeft (unitInterval) A (n + 1)
            (FirstHurewicz.boundaryOne (unitInterval) SecondHurewicz.intervalChain) c -
          PeriodTorusHigherHomology.crossProductEdge (unitInterval) A n
            SecondHurewicz.intervalChain
            (((FirstHurewicz.singularComplex A).d (n + 1) n).hom c)) =
      _
  simp only [SecondHurewicz.intervalChain_boundary, map_sub, LinearMap.sub_apply, crossPoint_left,
    inducedChain_timeSlice, prismOperator_apply]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem
    SecondHurewicz.SimplyConnected.prismOperator_domain {A B X : Type} [TopologicalSpace A]
    [TopologicalSpace B] [TopologicalSpace X] (n : ℕ) (f : C(A, B)) (H : C((unitInterval) × B, X))
    (c : FirstHurewicz.Chains A n) :
    prismOperator n (H.comp ((ContinuousMap.id (unitInterval)).prodMap f)) c =
      prismOperator n H (FirstHurewicz.inducedChain f n c) := by
  have h :=
    PeriodTorusHigherHomology.crossProductEdge_natural (ContinuousMap.id (unitInterval)) f n
      SecondHurewicz.intervalChain c
  rw [FirstHurewicz.inducedChain_id, LinearMap.id_apply] at h
  simp only [prismOperator_apply, FirstHurewicz.inducedChain_comp, LinearMap.comp_apply]
  exact congrArg (FirstHurewicz.inducedChain H (n + 1)) h

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def SecondHurewicz.SimplyConnected.simplexPrism {X : Type} [TopologicalSpace X] (n : ℕ)
    (H : C((unitInterval) × FirstHurewicz.Simplex n, X)) : FirstHurewicz.Chains X (n + 1) :=
  prismOperator n H
    (FirstHurewicz.simplexChain (FirstHurewicz.Simplex n) n
      (ContinuousMap.id (FirstHurewicz.Simplex n)))

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem
    SecondHurewicz.SimplyConnected.prismOperator_simplex {A X : Type} [TopologicalSpace A]
    [TopologicalSpace X] (n : ℕ) (H : C((unitInterval) × A, X))
    (smp : FirstHurewicz.SingularSimplex A n) :
    prismOperator n H (FirstHurewicz.simplexChain A n smp) =
      simplexPrism n (H.comp ((ContinuousMap.id (unitInterval)).prodMap smp)) := by
  have h :=
    prismOperator_domain n smp H
      (FirstHurewicz.simplexChain (FirstHurewicz.Simplex n) n
        (ContinuousMap.id (FirstHurewicz.Simplex n)))
  rw [FirstHurewicz.inducedChain_simplex, ContinuousMap.comp_id] at h
  exact h.symm

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem SecondHurewicz.SimplyConnected.simplexPrism_boundary {X : Type} [TopologicalSpace X]
    (n : ℕ) (H : C((unitInterval) × FirstHurewicz.Simplex (n + 1), X)) :
    ((FirstHurewicz.singularComplex X).d (n + 2) (n + 1)).hom (simplexPrism (n + 1) H) =
      FirstHurewicz.simplexChain X (n + 1) (timeSlice H 1) -
          FirstHurewicz.simplexChain X (n + 1) (timeSlice H 0) -
        ∑ i : Fin (n + 2),
          (-1 : ℤ) ^ i.val •
            simplexPrism n
              (H.comp
                ((ContinuousMap.id (unitInterval)).prodMap (FirstHurewicz.simplexFace n i))) := by
  rw [simplexPrism, prismOperator_boundary, FirstHurewicz.inducedChain_simplex,
    FirstHurewicz.inducedChain_simplex, ContinuousMap.comp_id, ContinuousMap.comp_id]
  rw [FirstHurewicz.boundary_simplex, map_sum]
  simp only [map_zsmul, ContinuousMap.id_comp, prismOperator_simplex]

private def
    SecondHurewicz.SimplyConnected.simplexEndpointOperator {X : Type} [TopologicalSpace X] (n : ℕ)
    (H : FirstHurewicz.SingularSimplex X n → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (t : (unitInterval)) : FirstHurewicz.Chains X n →ₗ[ℤ] FirstHurewicz.Chains X n :=
  FirstHurewicz.chainLift X n fun smp => FirstHurewicz.simplexChain X n (timeSlice (H smp) t)

@[simp]
private theorem SecondHurewicz.SimplyConnected.simplexEndpointOperator_simplex {X : Type}
    [TopologicalSpace X] (n : ℕ)
    (H : FirstHurewicz.SingularSimplex X n → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (t : (unitInterval)) (smp : FirstHurewicz.SingularSimplex X n) :
    simplexEndpointOperator n H t (FirstHurewicz.simplexChain X n smp) =
      FirstHurewicz.simplexChain X n (timeSlice (H smp) t) :=
  FirstHurewicz.chainLift_simplex X n _ smp

private def
    SecondHurewicz.SimplyConnected.simplexPrismOperator {X : Type} [TopologicalSpace X] (n : ℕ)
    (H : FirstHurewicz.SingularSimplex X n → C((unitInterval) × FirstHurewicz.Simplex n, X)) :
    FirstHurewicz.Chains X n →ₗ[ℤ] FirstHurewicz.Chains X (n + 1) :=
  FirstHurewicz.chainLift X n fun smp => simplexPrism n (H smp)

@[simp]
private theorem SecondHurewicz.SimplyConnected.simplexPrismOperator_simplex {X : Type}
    [TopologicalSpace X] (n : ℕ)
    (H : FirstHurewicz.SingularSimplex X n → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (smp : FirstHurewicz.SingularSimplex X n) :
    simplexPrismOperator n H (FirstHurewicz.simplexChain X n smp) = simplexPrism n (H smp) :=
  FirstHurewicz.chainLift_simplex X n _ smp

private def SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies {X : Type} [TopologicalSpace X]
    (n : ℕ)
    (H : FirstHurewicz.SingularSimplex X n → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (H' :
      FirstHurewicz.SingularSimplex X (n + 1) →
        C((unitInterval) × FirstHurewicz.Simplex (n + 1), X)) :
    Prop :=
  ∀ smp i,
    (H' smp).comp ((ContinuousMap.id (unitInterval)).prodMap (FirstHurewicz.simplexFace n i)) =
      H (smp.comp (FirstHurewicz.simplexFace n i))

private theorem
    SecondHurewicz.SimplyConnected.timeSlice_face {X : Type} [TopologicalSpace X] {n : ℕ}
    {H : FirstHurewicz.SingularSimplex X n → C((unitInterval) × FirstHurewicz.Simplex n, X)}
    {H' :
      FirstHurewicz.SingularSimplex X (n + 1) →
        C((unitInterval) × FirstHurewicz.Simplex (n + 1), X)}
    (h : FaceCompatibleHomotopies n H H') (smp : FirstHurewicz.SingularSimplex X (n + 1))
    (i : Fin (n + 2)) (t : (unitInterval)) :
    (timeSlice (H' smp) t).comp (FirstHurewicz.simplexFace n i) =
      timeSlice (H (smp.comp (FirstHurewicz.simplexFace n i))) t :=
  congrArg (fun F => timeSlice F t) (h smp i)

private theorem SecondHurewicz.SimplyConnected.simplexEndpointOperator_boundary {X : Type}
    [TopologicalSpace X] (n : ℕ)
    (H : FirstHurewicz.SingularSimplex X n → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (H' :
      FirstHurewicz.SingularSimplex X (n + 1) →
        C((unitInterval) × FirstHurewicz.Simplex (n + 1), X))
    (h : FaceCompatibleHomotopies n H H') (t : (unitInterval))
    (c : FirstHurewicz.Chains X (n + 1)) :
    ((FirstHurewicz.singularComplex X).d (n + 1) n).hom (simplexEndpointOperator (n + 1) H' t c) =
      simplexEndpointOperator n H t (((FirstHurewicz.singularComplex X).d (n + 1) n).hom c) := by
  have hc :
    (((FirstHurewicz.singularComplex X).d (n + 1) n).hom).comp
        (simplexEndpointOperator (n + 1) H' t) =
      (simplexEndpointOperator n H t).comp ((FirstHurewicz.singularComplex X).d (n + 1) n).hom := by
    apply FirstHurewicz.chainMap_ext X (n + 1)
    intro smp
    simp only [LinearMap.comp_apply, simplexEndpointOperator_simplex,
      FirstHurewicz.boundary_simplex, map_sum, map_zsmul, timeSlice_face h]
  exact LinearMap.congr_fun hc c

private theorem SecondHurewicz.SimplyConnected.simplexPrismOperator_boundary {X : Type}
    [TopologicalSpace X] (n : ℕ)
    (H : FirstHurewicz.SingularSimplex X n → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (H' :
      FirstHurewicz.SingularSimplex X (n + 1) →
        C((unitInterval) × FirstHurewicz.Simplex (n + 1), X))
    (h : FaceCompatibleHomotopies n H H') (c : FirstHurewicz.Chains X (n + 1)) :
    ((FirstHurewicz.singularComplex X).d (n + 2) (n + 1)).hom
        (simplexPrismOperator (n + 1) H' c) =
      simplexEndpointOperator (n + 1) H' 1 c - simplexEndpointOperator (n + 1) H' 0 c -
        simplexPrismOperator n H (((FirstHurewicz.singularComplex X).d (n + 1) n).hom c) := by
  have hc :
    (((FirstHurewicz.singularComplex X).d (n + 2) (n + 1)).hom).comp
        (simplexPrismOperator (n + 1) H') =
      simplexEndpointOperator (n + 1) H' 1 - simplexEndpointOperator (n + 1) H' 0 -
        (simplexPrismOperator n H).comp ((FirstHurewicz.singularComplex X).d (n + 1) n).hom := by
    apply FirstHurewicz.chainMap_ext X (n + 1)
    intro smp
    have hface := h smp
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, simplexPrismOperator_simplex,
      simplexPrism_boundary, simplexEndpointOperator_simplex, FirstHurewicz.boundary_simplex,
      map_sum, map_zsmul, hface]
  exact LinearMap.congr_fun hc c

private theorem SecondHurewicz.SimplyConnected.simplexEndpointOperator_zero {X : Type}
    [TopologicalSpace X] (n : ℕ)
    (H : FirstHurewicz.SingularSimplex X n → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (h₀ : ∀ smp, timeSlice (H smp) 0 = smp) : simplexEndpointOperator n H 0 = LinearMap.id := by
  apply FirstHurewicz.chainMap_ext X n
  intro smp
  rw [simplexEndpointOperator_simplex, h₀]
  rfl

private def SecondHurewicz.SimplyConnected.straightenedTwoCycle {X : Type} [TopologicalSpace X]
    (H₁ : FirstHurewicz.SingularSimplex X 1 → C((unitInterval) × FirstHurewicz.Simplex 1, X))
    (H₂ : FirstHurewicz.SingularSimplex X 2 → C((unitInterval) × FirstHurewicz.Simplex 2, X))
    (h : FaceCompatibleHomotopies 1 H₁ H₂)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 2) :
    SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 2 :=
  SingularMayerVietoris.ModuleHomology.mkCycle (FirstHurewicz.singularComplex X) 2
    (simplexEndpointOperator 2 H₂ 1 c.1)
    (by
      rw [simplexEndpointOperator_boundary 1 H₁ H₂ h,
        SingularMayerVietoris.ModuleHomology.cycle_condition (FirstHurewicz.singularComplex X) 2
          c,
        map_zero])

private theorem
    SecondHurewicz.SimplyConnected.straightenedTwoCycle_class {X : Type} [TopologicalSpace X]
    (H₁ : FirstHurewicz.SingularSimplex X 1 → C((unitInterval) × FirstHurewicz.Simplex 1, X))
    (H₂ : FirstHurewicz.SingularSimplex X 2 → C((unitInterval) × FirstHurewicz.Simplex 2, X))
    (h : FaceCompatibleHomotopies 1 H₁ H₂) (h₀ : ∀ smp, timeSlice (H₂ smp) 0 = smp)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 2) :
    SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 2
        (straightenedTwoCycle H₁ H₂ h c) =
      SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 2 c := by
  apply
    (SingularMayerVietoris.ModuleHomology.cycleClass_eq_iff (FirstHurewicz.singularComplex X) 2 _
        _).mpr
  refine ⟨simplexPrismOperator 2 H₂ c.1, ?_⟩
  rw [simplexPrismOperator_boundary 1 H₁ H₂ h, simplexEndpointOperator_zero 2 H₂ h₀,
    SingularMayerVietoris.ModuleHomology.cycle_condition (FirstHurewicz.singularComplex X) 2 c,
    map_zero, sub_zero]
  rfl

private structure SecondHurewicz.SimplyConnected.VertexHomotopyData {X : Type} [TopologicalSpace X]
    (x : X) (n : ℕ) where
  homotopy : C(FirstHurewicz.Simplex n, X) → C((unitInterval) × FirstHurewicz.Simplex n, X)
  zero :
    ∀ (smp : C(FirstHurewicz.Simplex n, X)) (s : FirstHurewicz.Simplex n),
      homotopy smp (0, s) = smp s
  one_verticesBased : ∀ smp, VerticesBased x n (timeSlice (homotopy smp) 1)
  of_verticesBased :
    ∀ smp,
      VerticesBased x n smp →
        homotopy smp =
          smp.comp
            (ContinuousMap.snd :
              C((unitInterval) × FirstHurewicz.Simplex n, FirstHurewicz.Simplex n))
  face_compatible :
    ∀ smp : C(FirstHurewicz.Simplex (n + 1), X),
      FaceCompatible (fun i => homotopy (smp.comp (FirstHurewicz.simplexFace n i)))

private def
    SecondHurewicz.SimplyConnected.vertexBoundaryHomotopy {X : Type} [TopologicalSpace X] {x : X}
    {n : ℕ} (D : VertexHomotopyData x n) (smp : C(FirstHurewicz.Simplex (n + 1), X)) :
    C((unitInterval) × SimplexBoundary (n + 1), X) :=
  glueFaceHomotopies (fun i => D.homotopy (smp.comp (FirstHurewicz.simplexFace n i)))
    (D.face_compatible smp)

@[simp]
private theorem
    SecondHurewicz.SimplyConnected.vertexBoundaryHomotopy_face {X : Type} [TopologicalSpace X]
    {x : X} {n : ℕ} (D : VertexHomotopyData x n) (smp : C(FirstHurewicz.Simplex (n + 1), X))
    (i : Fin (n + 2)) (r : (unitInterval)) (s : FirstHurewicz.Simplex n) :
    vertexBoundaryHomotopy D smp (r, simplexFaceBoundary n i s) =
      D.homotopy (smp.comp (FirstHurewicz.simplexFace n i)) (r, s) :=
  glueFaceHomotopies_face _ _ i r s

@[simp]
private theorem
    SecondHurewicz.SimplyConnected.vertexBoundaryHomotopy_zero {X : Type} [TopologicalSpace X]
    {x : X} {n : ℕ} (D : VertexHomotopyData x n) (smp : C(FirstHurewicz.Simplex (n + 1), X))
    (s : SimplexBoundary (n + 1)) : vertexBoundaryHomotopy D smp (0, s) = smp s.val :=
  glueFaceHomotopies_zero _ _ smp (fun i t => D.zero (smp.comp (FirstHurewicz.simplexFace n i)) t)
    s

private def
    SecondHurewicz.SimplyConnected.vertexStepHomotopy {X : Type} [TopologicalSpace X] {x : X}
    {n : ℕ} (D : VertexHomotopyData x n) (smp : C(FirstHurewicz.Simplex (n + 1), X)) :
    C((unitInterval) × FirstHurewicz.Simplex (n + 1), X) := by
  classical
    exact
    if VerticesBased x (n + 1) smp then
      smp.comp
        (ContinuousMap.snd :
          C((unitInterval) × FirstHurewicz.Simplex (n + 1), FirstHurewicz.Simplex (n + 1)))
    else
      extendBoundaryHomotopy smp (vertexBoundaryHomotopy D smp)
        (vertexBoundaryHomotopy_zero D smp)

private theorem SecondHurewicz.SimplyConnected.vertexStepHomotopy_of_verticesBased {X : Type}
    [TopologicalSpace X] {x : X} {n : ℕ} (D : VertexHomotopyData x n)
    (smp : C(FirstHurewicz.Simplex (n + 1), X)) (h : VerticesBased x (n + 1) smp) :
    vertexStepHomotopy D smp =
      smp.comp
        (ContinuousMap.snd :
          C((unitInterval) × FirstHurewicz.Simplex (n + 1), FirstHurewicz.Simplex (n + 1))) := by
  classical simp only [vertexStepHomotopy, ite_eq_left h]

private theorem SecondHurewicz.SimplyConnected.vertexStepHomotopy_of_not_verticesBased {X : Type}
    [TopologicalSpace X] {x : X} {n : ℕ} (D : VertexHomotopyData x n)
    (smp : C(FirstHurewicz.Simplex (n + 1), X)) (h : ¬VerticesBased x (n + 1) smp) :
    vertexStepHomotopy D smp =
      extendBoundaryHomotopy smp (vertexBoundaryHomotopy D smp)
        (vertexBoundaryHomotopy_zero D smp) := by
  classical simp only [vertexStepHomotopy, ite_eq_right h]

@[simp]
private theorem
    SecondHurewicz.SimplyConnected.vertexStepHomotopy_zero {X : Type} [TopologicalSpace X]
    {x : X} {n : ℕ} (D : VertexHomotopyData x n) (smp : C(FirstHurewicz.Simplex (n + 1), X))
    (s : FirstHurewicz.Simplex (n + 1)) : vertexStepHomotopy D smp (0, s) = smp s := by
  classical
  by_cases h : VerticesBased x (n + 1) smp
  · rw [vertexStepHomotopy_of_verticesBased D smp h]
    rfl
  · rw [vertexStepHomotopy_of_not_verticesBased D smp h]
    exact extendBoundaryHomotopy_bottom _ _ _ s

private theorem SecondHurewicz.SimplyConnected.vertexStepHomotopy_face_apply {X : Type}
    [TopologicalSpace X] {x : X} {n : ℕ} (D : VertexHomotopyData x n)
    (smp : C(FirstHurewicz.Simplex (n + 1), X)) (i : Fin (n + 2)) (r : (unitInterval))
    (s : FirstHurewicz.Simplex n) :
    vertexStepHomotopy D smp (r, FirstHurewicz.simplexFace n i s) =
      D.homotopy (smp.comp (FirstHurewicz.simplexFace n i)) (r, s) := by
  classical
  by_cases h : VerticesBased x (n + 1) smp
  · rw [vertexStepHomotopy_of_verticesBased D smp h, D.of_verticesBased _ (h.face i)]
    rfl
  · rw [vertexStepHomotopy_of_not_verticesBased D smp h, extendBoundaryHomotopy_face]
    exact vertexBoundaryHomotopy_face D smp i r s

private theorem
    SecondHurewicz.SimplyConnected.vertexStepHomotopy_face {X : Type} [TopologicalSpace X]
    {x : X} {n : ℕ} (D : VertexHomotopyData x n) :
    FaceCompatibleHomotopies n D.homotopy (vertexStepHomotopy D) := by
  intro smp i
  ext u
  exact vertexStepHomotopy_face_apply D smp i u.1 u.2

private theorem SecondHurewicz.SimplyConnected.vertexStepHomotopy_one_verticesBased {X : Type}
    [TopologicalSpace X] {x : X} {n : ℕ} (D : VertexHomotopyData x n)
    (smp : C(FirstHurewicz.Simplex (n + 1), X)) :
    VerticesBased x (n + 1) (timeSlice (vertexStepHomotopy D smp) 1) := by
  intro k
  obtain ⟨i, j, hij⟩ := simplexVertex_exists_face n k
  change vertexStepHomotopy D smp (1, stdSimplex.vertex k) = x
  rw [← hij, vertexStepHomotopy_face_apply]
  exact D.one_verticesBased (smp.comp (FirstHurewicz.simplexFace n i)) j

private theorem SecondHurewicz.SimplyConnected.vertexStepHomotopy_faceCompatible {X : Type}
    [TopologicalSpace X] {x : X} {n : ℕ} (D : VertexHomotopyData x n)
    (smp : C(FirstHurewicz.Simplex (n + 2), X)) :
    FaceCompatible
      (fun i => vertexStepHomotopy D (smp.comp (FirstHurewicz.simplexFace (n + 1) i))) := by
  apply faceCompatible_of_cofaceCompatible
  intro i j hij r u
  rw [vertexStepHomotopy_face_apply, vertexStepHomotopy_face_apply,
    PeriodTorusLineBundle.ChernCocycle.singularSimplex_face_face smp hij]

private def
    SecondHurewicz.SimplyConnected.VertexHomotopyData.next {X : Type} [TopologicalSpace X] {x : X}
    {n : ℕ} (D : SecondHurewicz.SimplyConnected.VertexHomotopyData x n) :
    SecondHurewicz.SimplyConnected.VertexHomotopyData x (n + 1)
    where
  homotopy := SecondHurewicz.SimplyConnected.vertexStepHomotopy D
  zero := SecondHurewicz.SimplyConnected.vertexStepHomotopy_zero D
  one_verticesBased := SecondHurewicz.SimplyConnected.vertexStepHomotopy_one_verticesBased D
  of_verticesBased := SecondHurewicz.SimplyConnected.vertexStepHomotopy_of_verticesBased D
  face_compatible := SecondHurewicz.SimplyConnected.vertexStepHomotopy_faceCompatible D

private def SecondHurewicz.SimplyConnected.basedEdgePath {X : Type} [TopologicalSpace X] (x : X)
    (smp : C(FirstHurewicz.Simplex 1, X)) (h₀ : smp (stdSimplex.vertex (S := ℝ) (0 : Fin 2)) = x)
    (h₁ : smp (stdSimplex.vertex (S := ℝ) (1 : Fin 2)) = x) : Path x x :=
  (FirstHurewicz.simplexPath smp).cast h₀.symm h₁.symm

@[simp]
private theorem SecondHurewicz.SimplyConnected.basedEdgePath_const {X : Type} [TopologicalSpace X]
    (x : X) :
    basedEdgePath x (ContinuousMap.const (FirstHurewicz.Simplex 1) x) rfl rfl = Path.refl x := by
  apply Path.ext
  funext t
  rfl

private def SecondHurewicz.SimplyConnected.chosenBasePath {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x y : X) : Path y x := by
  classical exact if h : y = x then (Path.refl x).cast h rfl else PathConnectedSpace.somePath y x

@[simp]
private theorem SecondHurewicz.SimplyConnected.chosenBasePath_self {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) : chosenBasePath x x = Path.refl x := by
  simp [chosenBasePath]

private def SecondHurewicz.SimplyConnected.chosenNullHomotopy {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (p : Path x x) : p.Homotopy (Path.refl x) := by
  classical
    exact
    if h : p = Path.refl x then (Path.Homotopy.refl (Path.refl x)).cast h.symm rfl
    else Classical.choice (SimplyConnectedSpace.paths_homotopic p (Path.refl x))

@[simp]
private theorem
    SecondHurewicz.SimplyConnected.chosenNullHomotopy_refl {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) :
    chosenNullHomotopy x (Path.refl x) = Path.Homotopy.refl (Path.refl x) := by
  simp [chosenNullHomotopy]
  rfl

private def SecondHurewicz.SimplyConnected.vertexHomotopy {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (smp : C(FirstHurewicz.Simplex 0, X)) :
    C((unitInterval) × FirstHurewicz.Simplex 0, X) :=
  (chosenBasePath x (smp (stdSimplex.vertex (S := ℝ) (0 : Fin 1)))).toContinuousMap.comp
    (ContinuousMap.fst : C((unitInterval) × FirstHurewicz.Simplex 0, (unitInterval)))

@[simp]
private theorem SecondHurewicz.SimplyConnected.vertexHomotopy_zero {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (smp : C(FirstHurewicz.Simplex 0, X))
    (s : FirstHurewicz.Simplex 0) : vertexHomotopy x smp (0, s) = smp s := by
  change chosenBasePath x (smp (stdSimplex.vertex (S := ℝ) (0 : Fin 1))) 0 = smp s
  rw [Path.source, FirstHurewicz.simplexZero_eq_vertex s]

@[simp]
private theorem SecondHurewicz.SimplyConnected.vertexHomotopy_one {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (smp : C(FirstHurewicz.Simplex 0, X))
    (s : FirstHurewicz.Simplex 0) : vertexHomotopy x smp (1, s) = x :=
  (chosenBasePath x (smp (stdSimplex.vertex (S := ℝ) (0 : Fin 1)))).target

@[simp]
private theorem SecondHurewicz.SimplyConnected.vertexHomotopy_const {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) :
    vertexHomotopy x (ContinuousMap.const (FirstHurewicz.Simplex 0) x) =
      ContinuousMap.const ((unitInterval) × FirstHurewicz.Simplex 0) x := by
  ext t
  change chosenBasePath x x t.1 = x
  rw [chosenBasePath_self]
  rfl

private def SecondHurewicz.SimplyConnected.edgeNullHomotopy {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (smp : C(FirstHurewicz.Simplex 1, X))
    (h₀ : smp (stdSimplex.vertex (S := ℝ) (0 : Fin 2)) = x)
    (h₁ : smp (stdSimplex.vertex (S := ℝ) (1 : Fin 2)) = x) :
    C((unitInterval) × FirstHurewicz.Simplex 1, X) :=
  (chosenNullHomotopy x (basedEdgePath x smp h₀ h₁)).toContinuousMap.comp
    ((ContinuousMap.id (unitInterval)).prodMap
      ⟨stdSimplexHomeomorphUnitInterval, stdSimplexHomeomorphUnitInterval.continuous⟩)

@[simp]
private theorem SecondHurewicz.SimplyConnected.edgeNullHomotopy_zero {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (smp : C(FirstHurewicz.Simplex 1, X)) (h₀ h₁)
    (s : FirstHurewicz.Simplex 1) : edgeNullHomotopy x smp h₀ h₁ (0, s) = smp s := by
  change
    chosenNullHomotopy x (basedEdgePath x smp h₀ h₁) (0, stdSimplexHomeomorphUnitInterval s) =
      smp s
  rw [ContinuousMap.HomotopyWith.apply_zero]
  change smp (stdSimplexHomeomorphUnitInterval.symm (stdSimplexHomeomorphUnitInterval s)) = smp s
  rw [stdSimplexHomeomorphUnitInterval.symm_apply_apply]

@[simp]
private theorem SecondHurewicz.SimplyConnected.edgeNullHomotopy_one {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (smp : C(FirstHurewicz.Simplex 1, X)) (h₀ h₁)
    (s : FirstHurewicz.Simplex 1) : edgeNullHomotopy x smp h₀ h₁ (1, s) = x := by
  change
    chosenNullHomotopy x (basedEdgePath x smp h₀ h₁) (1, stdSimplexHomeomorphUnitInterval s) = x
  rw [ContinuousMap.HomotopyWith.apply_one]
  rfl

@[simp]
private theorem SecondHurewicz.SimplyConnected.edgeNullHomotopy_vertex_zero {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) (smp : C(FirstHurewicz.Simplex 1, X))
    (h₀ h₁) (t : (unitInterval)) :
    edgeNullHomotopy x smp h₀ h₁ (t, stdSimplex.vertex (S := ℝ) (0 : Fin 2)) = x := by
  change
    chosenNullHomotopy x (basedEdgePath x smp h₀ h₁) (t, stdSimplexHomeomorphUnitInterval _) = x
  rw [stdSimplexHomeomorphUnitInterval_zero]
  exact Path.Homotopy.source _ t

@[simp]
private theorem
    SecondHurewicz.SimplyConnected.edgeNullHomotopy_vertex_one {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (smp : C(FirstHurewicz.Simplex 1, X)) (h₀ h₁)
    (t : (unitInterval)) :
    edgeNullHomotopy x smp h₀ h₁ (t, stdSimplex.vertex (S := ℝ) (1 : Fin 2)) = x := by
  change
    chosenNullHomotopy x (basedEdgePath x smp h₀ h₁) (t, stdSimplexHomeomorphUnitInterval _) = x
  rw [stdSimplexHomeomorphUnitInterval_one]
  exact Path.Homotopy.target _ t

@[simp]
private theorem
    SecondHurewicz.SimplyConnected.edgeNullHomotopy_const {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) :
    edgeNullHomotopy x (ContinuousMap.const (FirstHurewicz.Simplex 1) x) rfl rfl =
      ContinuousMap.const ((unitInterval) × FirstHurewicz.Simplex 1) x := by
  ext t
  change
    chosenNullHomotopy x
        (basedEdgePath x (ContinuousMap.const (FirstHurewicz.Simplex 1) x) rfl rfl)
        (t.1, stdSimplexHomeomorphUnitInterval t.2) =
      x
  rw [basedEdgePath_const, chosenNullHomotopy_refl]
  rfl

private def SecondHurewicz.SimplyConnected.vertexInitialData {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) : VertexHomotopyData x 0
    where
  homotopy := vertexHomotopy x
  zero := vertexHomotopy_zero x
  one_verticesBased smp i := vertexHomotopy_one x smp (stdSimplex.vertex i)
  of_verticesBased smp
    h := by
    have hs : smp = ContinuousMap.const (FirstHurewicz.Simplex 0) x := verticesBased_zero_iff.mp h
    rw [hs, vertexHomotopy_const]
    rfl
  face_compatible
    smp :=
    faceCompatible_zero (fun i => vertexHomotopy x (smp.comp (FirstHurewicz.simplexFace 0 i)))

private def SecondHurewicz.SimplyConnected.vertexStraighteningData {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) : (n : ℕ) → VertexHomotopyData x n
  | 0 => vertexInitialData x
  | n + 1 => (vertexStraighteningData x n).next

private def
    SecondHurewicz.SimplyConnected.vertexStraighteningHomotopy {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (n : ℕ) (smp : C(FirstHurewicz.Simplex n, X)) :
    C((unitInterval) × FirstHurewicz.Simplex n, X) :=
  (vertexStraighteningData x n).homotopy smp

@[simp]
private theorem SecondHurewicz.SimplyConnected.vertexStraighteningHomotopy_zero {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) (n : ℕ)
    (smp : C(FirstHurewicz.Simplex n, X)) (s : FirstHurewicz.Simplex n) :
    vertexStraighteningHomotopy x n smp (0, s) = smp s :=
  (vertexStraighteningData x n).zero smp s

@[simp]
private theorem SecondHurewicz.SimplyConnected.vertexStraighteningHomotopy_timeSlice_zero {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) (n : ℕ)
    (smp : C(FirstHurewicz.Simplex n, X)) :
    timeSlice (vertexStraighteningHomotopy x n smp) 0 = smp := by
  ext s
  exact vertexStraighteningHomotopy_zero x n smp s

private theorem SecondHurewicz.SimplyConnected.vertexStraighteningHomotopy_face {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) (n : ℕ) :
    FaceCompatibleHomotopies n (vertexStraighteningHomotopy x n)
      (vertexStraighteningHomotopy x (n + 1)) :=
  vertexStepHomotopy_face (vertexStraighteningData x n)

private theorem SecondHurewicz.SimplyConnected.vertexStraighteningHomotopy_timeSlice_face {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) (n : ℕ)
    (smp : C(FirstHurewicz.Simplex (n + 1), X)) (i : Fin (n + 2)) (r : (unitInterval)) :
    (timeSlice (vertexStraighteningHomotopy x (n + 1) smp) r).comp
        (FirstHurewicz.simplexFace n i) =
      timeSlice (vertexStraighteningHomotopy x n (smp.comp (FirstHurewicz.simplexFace n i))) r :=
  timeSlice_face (vertexStraighteningHomotopy_face x n) smp i r

private theorem
    SecondHurewicz.SimplyConnected.vertexStraighteningHomotopy_one_verticesBased {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) (n : ℕ)
    (smp : C(FirstHurewicz.Simplex n, X)) :
    VerticesBased x n (timeSlice (vertexStraighteningHomotopy x n smp) 1) :=
  (vertexStraighteningData x n).one_verticesBased smp

private theorem
    SecondHurewicz.SimplyConnected.vertexStraighteningHomotopy_of_verticesBased {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) (n : ℕ)
    (smp : C(FirstHurewicz.Simplex n, X)) (h : VerticesBased x n smp) :
    vertexStraighteningHomotopy x n smp =
      smp.comp
        (ContinuousMap.snd :
          C((unitInterval) × FirstHurewicz.Simplex n, FirstHurewicz.Simplex n)) :=
  (vertexStraighteningData x n).of_verticesBased smp h

private theorem
    SecondHurewicz.SimplyConnected.vertexStraighteningHomotopy_timeSlice_of_verticesBased
    {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) (n : ℕ)
    (smp : C(FirstHurewicz.Simplex n, X)) (h : VerticesBased x n smp) (r : (unitInterval)) :
    timeSlice (vertexStraighteningHomotopy x n smp) r = smp := by
  rw [vertexStraighteningHomotopy_of_verticesBased x n smp h]
  rfl

@[simp]
private theorem SecondHurewicz.SimplyConnected.vertexStraighteningHomotopy_const {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) (n : ℕ) :
    vertexStraighteningHomotopy x n (ContinuousMap.const (FirstHurewicz.Simplex n) x) =
      ContinuousMap.const ((unitInterval) × FirstHurewicz.Simplex n) x := by
  rw [vertexStraighteningHomotopy_of_verticesBased x n _ (verticesBased_const x n)]
  rfl

private def SecondHurewicz.SimplyConnected.stationarySimplexHomotopy {X : Type} [TopologicalSpace X]
    (n : ℕ) (smp : C(FirstHurewicz.Simplex n, X)) :
    C((unitInterval) × FirstHurewicz.Simplex n, X) :=
  smp.comp
    (ContinuousMap.snd : C((unitInterval) × FirstHurewicz.Simplex n, FirstHurewicz.Simplex n))

private def SecondHurewicz.SimplyConnected.edgeStraighteningHomotopy {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (smp : C(FirstHurewicz.Simplex 1, X)) :
    C((unitInterval) × FirstHurewicz.Simplex 1, X) := by
  classical
    exact
    if h :
        smp (stdSimplex.vertex (S := ℝ) (0 : Fin 2)) = x ∧
          smp (stdSimplex.vertex (S := ℝ) (1 : Fin 2)) = x then
      edgeNullHomotopy x smp h.1 h.2
    else stationarySimplexHomotopy 1 smp

@[simp]
private theorem SecondHurewicz.SimplyConnected.edgeStraighteningHomotopy_zero {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) (smp : C(FirstHurewicz.Simplex 1, X))
    (s : FirstHurewicz.Simplex 1) : edgeStraighteningHomotopy x smp (0, s) = smp s := by
  classical
  unfold edgeStraighteningHomotopy
  split
  · exact edgeNullHomotopy_zero x smp _ _ s
  · rfl

private theorem SecondHurewicz.SimplyConnected.edgeStraighteningHomotopy_one {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) (smp : C(FirstHurewicz.Simplex 1, X))
    (h₀ : smp (stdSimplex.vertex (S := ℝ) (0 : Fin 2)) = x)
    (h₁ : smp (stdSimplex.vertex (S := ℝ) (1 : Fin 2)) = x) (s : FirstHurewicz.Simplex 1) :
    edgeStraighteningHomotopy x smp (1, s) = x := by
  classical
  have h :
    smp (stdSimplex.vertex (S := ℝ) (0 : Fin 2)) = x ∧
      smp (stdSimplex.vertex (S := ℝ) (1 : Fin 2)) = x :=
    ⟨h₀, h₁⟩
  rw [edgeStraighteningHomotopy, dite_eq_left h]
  exact edgeNullHomotopy_one x smp _ _ s

private theorem SecondHurewicz.SimplyConnected.edgeStraighteningHomotopy_vertex {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) (smp : C(FirstHurewicz.Simplex 1, X))
    (i : Fin 2) (t : (unitInterval)) :
    edgeStraighteningHomotopy x smp (t, stdSimplex.vertex (S := ℝ) i) =
      smp (stdSimplex.vertex (S := ℝ) i) := by
  classical
  unfold edgeStraighteningHomotopy
  split
  · rename_i h
    fin_cases i
    · exact (edgeNullHomotopy_vertex_zero x smp h.1 h.2 t).trans h.1.symm
    · exact (edgeNullHomotopy_vertex_one x smp h.1 h.2 t).trans h.2.symm
  · rfl

@[simp]
private theorem SecondHurewicz.SimplyConnected.edgeStraighteningHomotopy_const {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) :
    edgeStraighteningHomotopy x (ContinuousMap.const (FirstHurewicz.Simplex 1) x) =
      ContinuousMap.const ((unitInterval) × FirstHurewicz.Simplex 1) x := by
  classical
  simp only [edgeStraighteningHomotopy, ContinuousMap.const_apply]
  exact edgeNullHomotopy_const x

private theorem SecondHurewicz.SimplyConnected.edgeStraighteningHomotopy_face {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) :
    FaceCompatibleHomotopies 0 (stationarySimplexHomotopy 0) (edgeStraighteningHomotopy x) := by
  intro smp i
  ext u
  rcases u with ⟨t, s⟩
  change
    edgeStraighteningHomotopy x smp (t, FirstHurewicz.simplexFace 0 i s) =
      smp (FirstHurewicz.simplexFace 0 i s)
  rw [FirstHurewicz.simplexZero_eq_vertex s, FirstHurewicz.simplexFace_vertex]
  exact edgeStraighteningHomotopy_vertex x smp _ t

private theorem SecondHurewicz.SimplyConnected.nextFaceHomotopies_compatible {X : Type}
    [TopologicalSpace X] {n : ℕ}
    (H : FirstHurewicz.SingularSimplex X n → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (H' :
      FirstHurewicz.SingularSimplex X (n + 1) →
        C((unitInterval) × FirstHurewicz.Simplex (n + 1), X))
    (h : FaceCompatibleHomotopies n H H') (smp : FirstHurewicz.SingularSimplex X (n + 2)) :
    FaceCompatible (fun i => H' (smp.comp (FirstHurewicz.simplexFace (n + 1) i))) := by
  apply faceCompatible_of_cofaceCompatible
  intro i j hij t s
  have hi :=
    congrArg (fun F : C((unitInterval) × FirstHurewicz.Simplex n, X) => F (t, s))
      (h (smp.comp (FirstHurewicz.simplexFace (n + 1) j.succ)) i)
  have hj :=
    congrArg (fun F : C((unitInterval) × FirstHurewicz.Simplex n, X) => F (t, s))
      (h (smp.comp (FirstHurewicz.simplexFace (n + 1) i.castSucc)) j)
  change
    H' (smp.comp (FirstHurewicz.simplexFace (n + 1) j.succ))
        (t, FirstHurewicz.simplexFace n i s) =
      H
        ((smp.comp (FirstHurewicz.simplexFace (n + 1) j.succ)).comp
          (FirstHurewicz.simplexFace n i))
        (t, s) at hi
  change
    H' (smp.comp (FirstHurewicz.simplexFace (n + 1) i.castSucc))
        (t, FirstHurewicz.simplexFace n j s) =
      H
        ((smp.comp (FirstHurewicz.simplexFace (n + 1) i.castSucc)).comp
          (FirstHurewicz.simplexFace n j))
        (t, s) at hj
  rw [hi, hj]
  change
    H (smp.comp ((FirstHurewicz.simplexFace (n + 1) j.succ).comp (FirstHurewicz.simplexFace n i)))
        (t, s) =
      H
        (smp.comp
          ((FirstHurewicz.simplexFace (n + 1) i.castSucc).comp (FirstHurewicz.simplexFace n j)))
        (t, s)
  rw [PeriodTorusLineBundle.ChernCocycle.simplexFace_comp hij]

private def
    SecondHurewicz.SimplyConnected.coherentFaceBoundaryHomotopy {X : Type} [TopologicalSpace X]
    {n : ℕ}
    (H : FirstHurewicz.SingularSimplex X n → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (H' :
      FirstHurewicz.SingularSimplex X (n + 1) →
        C((unitInterval) × FirstHurewicz.Simplex (n + 1), X))
    (h : FaceCompatibleHomotopies n H H') (smp : FirstHurewicz.SingularSimplex X (n + 2)) :
    C((unitInterval) × SimplexBoundary (n + 2), X) :=
  glueFaceHomotopies (fun i => H' (smp.comp (FirstHurewicz.simplexFace (n + 1) i)))
    (nextFaceHomotopies_compatible H H' h smp)

@[simp]
private theorem SecondHurewicz.SimplyConnected.coherentFaceBoundaryHomotopy_face {X : Type}
    [TopologicalSpace X] {n : ℕ}
    (H : FirstHurewicz.SingularSimplex X n → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (H' :
      FirstHurewicz.SingularSimplex X (n + 1) →
        C((unitInterval) × FirstHurewicz.Simplex (n + 1), X))
    (h : FaceCompatibleHomotopies n H H') (smp : FirstHurewicz.SingularSimplex X (n + 2))
    (i : Fin (n + 3)) (t : (unitInterval)) (s : FirstHurewicz.Simplex (n + 1)) :
    coherentFaceBoundaryHomotopy H H' h smp (t, simplexFaceBoundary (n + 1) i s) =
      H' (smp.comp (FirstHurewicz.simplexFace (n + 1) i)) (t, s) :=
  glueFaceHomotopies_face _ _ i t s

private theorem SecondHurewicz.SimplyConnected.coherentFaceBoundaryHomotopy_zero {X : Type}
    [TopologicalSpace X] {n : ℕ}
    (H : FirstHurewicz.SingularSimplex X n → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (H' :
      FirstHurewicz.SingularSimplex X (n + 1) →
        C((unitInterval) × FirstHurewicz.Simplex (n + 1), X))
    (h : FaceCompatibleHomotopies n H H') (h₀ : ∀ smp s, H' smp (0, s) = smp s)
    (smp : FirstHurewicz.SingularSimplex X (n + 2)) (b : SimplexBoundary (n + 2)) :
    coherentFaceBoundaryHomotopy H H' h smp (0, b) = smp b.val :=
  glueFaceHomotopies_zero _ _ smp
    (fun i s => h₀ (smp.comp (FirstHurewicz.simplexFace (n + 1) i)) s) b

private def
    SecondHurewicz.SimplyConnected.extendCoherentSimplexHomotopy {X : Type} [TopologicalSpace X]
    {n : ℕ}
    (H : FirstHurewicz.SingularSimplex X n → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (H' :
      FirstHurewicz.SingularSimplex X (n + 1) →
        C((unitInterval) × FirstHurewicz.Simplex (n + 1), X))
    (h : FaceCompatibleHomotopies n H H') (h₀ : ∀ smp s, H' smp (0, s) = smp s)
    (smp : FirstHurewicz.SingularSimplex X (n + 2)) :
    C((unitInterval) × FirstHurewicz.Simplex (n + 2), X) :=
  extendBoundaryHomotopy smp (coherentFaceBoundaryHomotopy H H' h smp)
    (coherentFaceBoundaryHomotopy_zero H H' h h₀ smp)

@[simp]
private theorem SecondHurewicz.SimplyConnected.extendCoherentSimplexHomotopy_zero {X : Type}
    [TopologicalSpace X] {n : ℕ}
    (H : FirstHurewicz.SingularSimplex X n → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (H' :
      FirstHurewicz.SingularSimplex X (n + 1) →
        C((unitInterval) × FirstHurewicz.Simplex (n + 1), X))
    (h : FaceCompatibleHomotopies n H H') (h₀ : ∀ smp s, H' smp (0, s) = smp s)
    (smp : FirstHurewicz.SingularSimplex X (n + 2)) (s : FirstHurewicz.Simplex (n + 2)) :
    extendCoherentSimplexHomotopy H H' h h₀ smp (0, s) = smp s :=
  extendBoundaryHomotopy_bottom _ _ _ s

private theorem SecondHurewicz.SimplyConnected.extendCoherentSimplexHomotopy_face {X : Type}
    [TopologicalSpace X] {n : ℕ}
    (H : FirstHurewicz.SingularSimplex X n → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (H' :
      FirstHurewicz.SingularSimplex X (n + 1) →
        C((unitInterval) × FirstHurewicz.Simplex (n + 1), X))
    (h : FaceCompatibleHomotopies n H H') (h₀ : ∀ smp s, H' smp (0, s) = smp s) :
    FaceCompatibleHomotopies (n + 1) H' (extendCoherentSimplexHomotopy H H' h h₀) := by
  intro smp i
  ext u
  rcases u with ⟨t, s⟩
  change
    extendBoundaryHomotopy smp (coherentFaceBoundaryHomotopy H H' h smp)
        (coherentFaceBoundaryHomotopy_zero H H' h h₀ smp)
        (t, FirstHurewicz.simplexFace (n + 1) i s) =
      _
  rw [extendBoundaryHomotopy_face]
  exact coherentFaceBoundaryHomotopy_face H H' h smp i t s

private def SecondHurewicz.SimplyConnected.triangleBoundary : Set (FirstHurewicz.Simplex 2) :=
  {s | ∃ i, s i = 0}

private def SecondHurewicz.SimplyConnected.BasedTriangle {X : Type} [TopologicalSpace X] (x : X) :=
  { τ : C(FirstHurewicz.Simplex 2, X) // ∀ s ∈ triangleBoundary, τ s = x }

private def SecondHurewicz.SimplyConnected.triangleQuotient :
    C((unitInterval) × (unitInterval), FirstHurewicz.Simplex 2)
    where
  toFun
    z :=
    ⟨![1 - (z.1 : ℝ), (z.1 : ℝ) - Min.min (z.1 : ℝ) (z.2 : ℝ), Min.min (z.1 : ℝ) (z.2 : ℝ)],
      by
      constructor
      · intro i
        fin_cases i
        · exact sub_nonneg.mpr z.1.property.2
        · exact sub_nonneg.mpr (min_le_left _ _)
        · exact le_min z.1.property.1 z.2.property.1
      · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Matrix.cons_val_zero,
          Matrix.cons_val_succ, Matrix.cons_val_fin_one]
        ring⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp <;> fun_prop

@[simp]
private theorem SecondHurewicz.SimplyConnected.triangleQuotient_zero
    (z : (unitInterval) × (unitInterval)) : triangleQuotient z 0 = 1 - (z.1 : ℝ) :=
  rfl

@[simp]
private theorem SecondHurewicz.SimplyConnected.triangleQuotient_one
    (z : (unitInterval) × (unitInterval)) :
    triangleQuotient z 1 = (z.1 : ℝ) - Min.min (z.1 : ℝ) (z.2 : ℝ) :=
  rfl

@[simp]
private theorem SecondHurewicz.SimplyConnected.triangleQuotient_two
    (z : (unitInterval) × (unitInterval)) : triangleQuotient z 2 = Min.min (z.1 : ℝ) (z.2 : ℝ) :=
  rfl

private def SecondHurewicz.SimplyConnected.triangleCubeQuotient :
    C(Fin 2 → (unitInterval), FirstHurewicz.Simplex 2) :=
  triangleQuotient.comp ⟨fun t => (t 0, t 1), by fun_prop⟩

private theorem
    SecondHurewicz.SimplyConnected.triangleCubeQuotient_boundary (t : Fin 2 → (unitInterval))
    (ht : t ∈ Cube.boundary (Fin 2)) : triangleCubeQuotient t ∈ triangleBoundary := by
  rcases ht with ⟨i, hi | hi⟩
  · fin_cases i
    · refine ⟨2, ?_⟩
      change t 0 = 0 at hi
      change Min.min (t 0 : ℝ) (t 1 : ℝ) = 0
      simp [hi, min_eq_left (t 1).property.1]
    · refine ⟨2, ?_⟩
      change t 1 = 0 at hi
      change Min.min (t 0 : ℝ) (t 1 : ℝ) = 0
      simp [hi, min_eq_right (t 0).property.1]
  · fin_cases i
    · refine ⟨0, ?_⟩
      change t 0 = 1 at hi
      change 1 - (t 0 : ℝ) = 0
      simp [hi]
    · refine ⟨1, ?_⟩
      change t 1 = 1 at hi
      change (t 0 : ℝ) - Min.min (t 0 : ℝ) (t 1 : ℝ) = 0
      simp [hi, min_eq_left (t 0).property.2]

private def SecondHurewicz.SimplyConnected.basedTriangleLoop {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedTriangle x) : GenLoop (Fin 2) X x :=
  ⟨τ.val.comp triangleCubeQuotient, fun t ht => τ.property _ (triangleCubeQuotient_boundary t ht)⟩

private theorem
    SecondHurewicz.SimplyConnected.squareMap_basedTriangleLoop {X : Type} [TopologicalSpace X]
    {x : X} (τ : BasedTriangle x) :
    SecondHurewicz.squareMap (basedTriangleLoop τ) = τ.val.comp triangleQuotient := by
  ext z
  change
    τ.val
        (triangleQuotient
          (SecondHurewicz.squareCoordinates z 0, SecondHurewicz.squareCoordinates z 1)) =
      _
  rw [SecondHurewicz.squareCoordinates_zero, SecondHurewicz.squareCoordinates_one]
  rfl

private def
    SecondHurewicz.SimplyConnected.basedTriangleClass {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedTriangle x) : Additive (π_ 2 X x) :=
  Additive.ofMul (⟦basedTriangleLoop τ⟧ : π_ 2 X x)

private def
    SecondHurewicz.SimplyConnected.constantBasedTriangle {X : Type} [TopologicalSpace X] (x : X) :
    BasedTriangle x :=
  ⟨ContinuousMap.const (FirstHurewicz.Simplex 2) x, fun _ _ => rfl⟩

private def SecondHurewicz.SimplyConnected.triangleEdgeStraighteningHomotopy {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    (smp : FirstHurewicz.SingularSimplex X 2) : C((unitInterval) × FirstHurewicz.Simplex 2, X) :=
  extendCoherentSimplexHomotopy (stationarySimplexHomotopy 0) (edgeStraighteningHomotopy x)
    (edgeStraighteningHomotopy_face x) (edgeStraighteningHomotopy_zero x) smp

@[simp]
private theorem SecondHurewicz.SimplyConnected.triangleEdgeStraighteningHomotopy_zero {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    (smp : FirstHurewicz.SingularSimplex X 2) (s : FirstHurewicz.Simplex 2) :
    triangleEdgeStraighteningHomotopy x smp (0, s) = smp s :=
  extendCoherentSimplexHomotopy_zero _ _ _ _ smp s

private theorem SecondHurewicz.SimplyConnected.triangleEdgeStraighteningHomotopy_face {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) :
    FaceCompatibleHomotopies 1 (edgeStraighteningHomotopy x)
      (triangleEdgeStraighteningHomotopy x) :=
  extendCoherentSimplexHomotopy_face (stationarySimplexHomotopy 0) (edgeStraighteningHomotopy x)
    (edgeStraighteningHomotopy_face x) (edgeStraighteningHomotopy_zero x)

private def SecondHurewicz.SimplyConnected.tetrahedronEdgeStraighteningHomotopy {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    (smp : FirstHurewicz.SingularSimplex X 3) : C((unitInterval) × FirstHurewicz.Simplex 3, X) :=
  extendCoherentSimplexHomotopy (edgeStraighteningHomotopy x)
    (triangleEdgeStraighteningHomotopy x) (triangleEdgeStraighteningHomotopy_face x)
    (triangleEdgeStraighteningHomotopy_zero x) smp

@[simp]
private theorem SecondHurewicz.SimplyConnected.tetrahedronEdgeStraighteningHomotopy_zero {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    (smp : FirstHurewicz.SingularSimplex X 3) (s : FirstHurewicz.Simplex 3) :
    tetrahedronEdgeStraighteningHomotopy x smp (0, s) = smp s :=
  extendCoherentSimplexHomotopy_zero _ _ _ _ smp s

private theorem SecondHurewicz.SimplyConnected.tetrahedronEdgeStraighteningHomotopy_face {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) :
    FaceCompatibleHomotopies 2 (triangleEdgeStraighteningHomotopy x)
      (tetrahedronEdgeStraighteningHomotopy x) :=
  extendCoherentSimplexHomotopy_face (edgeStraighteningHomotopy x)
    (triangleEdgeStraighteningHomotopy x) (triangleEdgeStraighteningHomotopy_face x)
    (triangleEdgeStraighteningHomotopy_zero x)

private theorem SecondHurewicz.SimplyConnected.triangleEdgeStraighteningHomotopy_one_face {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    (smp : FirstHurewicz.SingularSimplex X 2) (h : VerticesBased x 2 smp) (i : Fin 3) :
    (timeSlice (triangleEdgeStraighteningHomotopy x smp) 1).comp (FirstHurewicz.simplexFace 1 i) =
      ContinuousMap.const (FirstHurewicz.Simplex 1) x := by
  rw [timeSlice_face (triangleEdgeStraighteningHomotopy_face x)]
  ext s
  exact
    edgeStraighteningHomotopy_one x (smp.comp (FirstHurewicz.simplexFace 1 i)) (h.face i 0)
      (h.face i 1) s

private theorem
    SecondHurewicz.SimplyConnected.triangleEdgeStraighteningHomotopy_one_boundary {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    (smp : FirstHurewicz.SingularSimplex X 2) (h : VerticesBased x 2 smp)
    (s : FirstHurewicz.Simplex 2) (hs : s ∈ triangleBoundary) :
    timeSlice (triangleEdgeStraighteningHomotopy x smp) 1 s = x := by
  obtain ⟨i, t, ht⟩ := simplexBoundary_exists_face 1 (⟨s, hs⟩ : SimplexBoundary 2)
  have he : FirstHurewicz.simplexFace 1 i t = s := congrArg Subtype.val ht
  rw [← he]
  exact
    congrArg (fun f : C(FirstHurewicz.Simplex 1, X) => f t)
      (triangleEdgeStraighteningHomotopy_one_face x smp h i)

private def SecondHurewicz.SimplyConnected.edgeStraightenedTriangle {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (smp : FirstHurewicz.SingularSimplex X 2)
    (h : VerticesBased x 2 smp) : BasedTriangle x :=
  ⟨timeSlice (triangleEdgeStraighteningHomotopy x smp) 1,
    triangleEdgeStraighteningHomotopy_one_boundary x smp h⟩

private def SecondHurewicz.SimplyConnected.vertexNormalizedSimplex {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (n : ℕ) (smp : FirstHurewicz.SingularSimplex X n) :
    FirstHurewicz.SingularSimplex X n :=
  timeSlice (vertexStraighteningHomotopy x n smp) 1

private theorem SecondHurewicz.SimplyConnected.vertexNormalizedSimplex_verticesBased {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) (n : ℕ)
    (smp : FirstHurewicz.SingularSimplex X n) :
    VerticesBased x n (vertexNormalizedSimplex x n smp) :=
  vertexStraighteningHomotopy_one_verticesBased x n smp

private theorem SecondHurewicz.SimplyConnected.vertexNormalizedSimplex_face {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) (n : ℕ)
    (smp : FirstHurewicz.SingularSimplex X (n + 1)) (i : Fin (n + 2)) :
    (vertexNormalizedSimplex x (n + 1) smp).comp (FirstHurewicz.simplexFace n i) =
      vertexNormalizedSimplex x n (smp.comp (FirstHurewicz.simplexFace n i)) :=
  vertexStraighteningHomotopy_timeSlice_face x n smp i 1

private theorem SecondHurewicz.SimplyConnected.vertexNormalizedSimplex_of_verticesBased {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) (n : ℕ)
    (smp : FirstHurewicz.SingularSimplex X n) (h : VerticesBased x n smp) :
    vertexNormalizedSimplex x n smp = smp :=
  vertexStraighteningHomotopy_timeSlice_of_verticesBased x n smp h 1

private def SecondHurewicz.SimplyConnected.normalizedTriangle {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (smp : FirstHurewicz.SingularSimplex X 2) :
    BasedTriangle x :=
  edgeStraightenedTriangle x (vertexNormalizedSimplex x 2 smp)
    (vertexNormalizedSimplex_verticesBased x 2 smp)

private theorem SecondHurewicz.SimplyConnected.normalizedTriangle_of_verticesBased {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    (smp : FirstHurewicz.SingularSimplex X 2) (h : VerticesBased x 2 smp) :
    normalizedTriangle x smp = edgeStraightenedTriangle x smp h := by
  apply Subtype.ext
  change
    timeSlice (triangleEdgeStraighteningHomotopy x (vertexNormalizedSimplex x 2 smp)) 1 =
      timeSlice (triangleEdgeStraighteningHomotopy x smp) 1
  rw [vertexNormalizedSimplex_of_verticesBased x 2 smp h]

private def SecondHurewicz.SimplyConnected.normalizedTetrahedronMap {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (smp : FirstHurewicz.SingularSimplex X 3) :
    FirstHurewicz.SingularSimplex X 3 :=
  timeSlice (tetrahedronEdgeStraighteningHomotopy x (vertexNormalizedSimplex x 3 smp)) 1

private theorem SecondHurewicz.SimplyConnected.normalizedTetrahedronMap_face {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    (smp : FirstHurewicz.SingularSimplex X 3) (i : Fin 4) :
    (normalizedTetrahedronMap x smp).comp (FirstHurewicz.simplexFace 2 i) =
      (normalizedTriangle x (smp.comp (FirstHurewicz.simplexFace 2 i))).val := by
  change
    (timeSlice (tetrahedronEdgeStraighteningHomotopy x (vertexNormalizedSimplex x 3 smp)) 1).comp
        (FirstHurewicz.simplexFace 2 i) =
      _
  rw [timeSlice_face (tetrahedronEdgeStraighteningHomotopy_face x), vertexNormalizedSimplex_face]
  rfl

private theorem SecondHurewicz.SimplyConnected.normalizedTetrahedronMap_face_boundary {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    (smp : FirstHurewicz.SingularSimplex X 3) (i : Fin 4) (s : FirstHurewicz.Simplex 2)
    (hs : s ∈ triangleBoundary) :
    normalizedTetrahedronMap x smp (FirstHurewicz.simplexFace 2 i s) = x := by
  have hf :=
    congrArg (fun f : C(FirstHurewicz.Simplex 2, X) => f s)
      (normalizedTetrahedronMap_face x smp i)
  exact hf.trans ((normalizedTriangle x (smp.comp (FirstHurewicz.simplexFace 2 i))).property s hs)

private def SecondHurewicz.SimplyConnected.normalizedTwoChain {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) : FirstHurewicz.Chains X 2 →ₗ[ℤ] FirstHurewicz.Chains X 2 :=
  FirstHurewicz.chainLift X 2 fun smp =>
    FirstHurewicz.simplexChain X 2 (normalizedTriangle x smp).val

@[simp]
private theorem
    SecondHurewicz.SimplyConnected.normalizedTwoChain_simplex {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (smp : FirstHurewicz.SingularSimplex X 2) :
    normalizedTwoChain x (FirstHurewicz.simplexChain X 2 smp) =
      FirstHurewicz.simplexChain X 2 (normalizedTriangle x smp).val :=
  FirstHurewicz.chainLift_simplex X 2 _ smp

private theorem SecondHurewicz.SimplyConnected.normalizedTwoChain_eq {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) :
    normalizedTwoChain x =
      (simplexEndpointOperator 2 (triangleEdgeStraighteningHomotopy x) 1).comp
        (simplexEndpointOperator 2 (vertexStraighteningHomotopy x 2) 1) := by
  apply FirstHurewicz.chainMap_ext X 2
  intro smp
  simp only [normalizedTwoChain_simplex, LinearMap.comp_apply, simplexEndpointOperator_simplex]
  rfl

private def SecondHurewicz.SimplyConnected.vertexNormalizedTwoCycle {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 2) :
    SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 2 :=
  straightenedTwoCycle (vertexStraighteningHomotopy x 1) (vertexStraighteningHomotopy x 2)
    (vertexStraighteningHomotopy_face x 1) c

private theorem SecondHurewicz.SimplyConnected.vertexNormalizedTwoCycle_class {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 2) :
    SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 2
        (vertexNormalizedTwoCycle x c) =
      SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 2 c :=
  straightenedTwoCycle_class _ _ (vertexStraighteningHomotopy_face x 1)
    (vertexStraighteningHomotopy_timeSlice_zero x 2) c

private def SecondHurewicz.SimplyConnected.normalizedTwoCycle {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 2) :
    SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 2 :=
  straightenedTwoCycle (edgeStraighteningHomotopy x) (triangleEdgeStraighteningHomotopy x)
    (triangleEdgeStraighteningHomotopy_face x) (vertexNormalizedTwoCycle x c)

@[simp]
private theorem
    SecondHurewicz.SimplyConnected.normalizedTwoCycle_val {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 2) :
    (normalizedTwoCycle x c).val = normalizedTwoChain x c.val := by
  rw [normalizedTwoChain_eq]
  rfl

private theorem
    SecondHurewicz.SimplyConnected.normalizedTwoCycle_class {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 2) :
    SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 2
        (normalizedTwoCycle x c) =
      SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 2 c := by
  have h₀ : ∀ smp, timeSlice (triangleEdgeStraighteningHomotopy x smp) 0 = smp := by
    intro smp
    ext s
    exact triangleEdgeStraighteningHomotopy_zero x smp s
  exact
    (straightenedTwoCycle_class _ _ (triangleEdgeStraighteningHomotopy_face x) h₀
          (vertexNormalizedTwoCycle x c)).trans
      (vertexNormalizedTwoCycle_class x c)

private def SecondHurewicz.SimplyConnected.tetrahedronOneSkeleton : Set (FirstHurewicz.Simplex 3) :=
  {s | ∃ i j : Fin 4, i ≠ j ∧ s i = 0 ∧ s j = 0}

private def
    SecondHurewicz.SimplyConnected.BasedTetrahedron {X : Type} [TopologicalSpace X] (x : X) :=
  { τ : C(FirstHurewicz.Simplex 3, X) // ∀ s ∈ tetrahedronOneSkeleton, τ s = x }

private theorem SecondHurewicz.SimplyConnected.simplexFace_triangleBoundary (i : Fin 4)
    (s : FirstHurewicz.Simplex 2) (hs : s ∈ triangleBoundary) :
    FirstHurewicz.simplexFace 2 i s ∈ tetrahedronOneSkeleton := by
  obtain ⟨j, hj⟩ := hs
  exact
    ⟨i, i.succAbove j, (Fin.succAbove_ne i j).symm, FirstHurewicz.simplexFace_apply_self 2 i s,
      (FirstHurewicz.simplexFace_apply_succAbove 2 i s j).trans hj⟩

private def
    SecondHurewicz.SimplyConnected.basedTetrahedronFace {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedTetrahedron x) (i : Fin 4) : BasedTriangle x :=
  ⟨τ.val.comp (FirstHurewicz.simplexFace 2 i), fun s hs =>
    τ.property _ (simplexFace_triangleBoundary i s hs)⟩

private def SecondHurewicz.SimplyConnected.tetrahedronSimplexBlend {n : ℕ} (t : (unitInterval))
    (a b : FirstHurewicz.Simplex n) : FirstHurewicz.Simplex n :=
  ⟨(1 - (t : ℝ)) • (a : Fin (n + 1) → ℝ) + (t : ℝ) • (b : Fin (n + 1) → ℝ),
    convex_stdSimplex ℝ _ a.property b.property (sub_nonneg.mpr t.property.2) t.property.1
      (by ring)⟩

@[simp]
private theorem SecondHurewicz.SimplyConnected.tetrahedronSimplexBlend_zero {n : ℕ}
    (a b : FirstHurewicz.Simplex n) : tetrahedronSimplexBlend 0 a b = a := by
  apply Subtype.ext
  funext i
  change (1 - (0 : ℝ)) * a i + (0 : ℝ) * b i = a i
  simp

@[simp]
private theorem SecondHurewicz.SimplyConnected.tetrahedronSimplexBlend_one {n : ℕ}
    (a b : FirstHurewicz.Simplex n) : tetrahedronSimplexBlend 1 a b = b := by
  apply Subtype.ext
  funext i
  change (1 - (1 : ℝ)) * a i + (1 : ℝ) * b i = b i
  simp

@[simp]
private theorem
    SecondHurewicz.SimplyConnected.tetrahedronSimplexBlend_self {n : ℕ} (t : (unitInterval))
    (a : FirstHurewicz.Simplex n) : tetrahedronSimplexBlend t a a = a := by
  apply Subtype.ext
  funext i
  change (1 - (t : ℝ)) * a i + (t : ℝ) * a i = a i
  ring

private def SecondHurewicz.SimplyConnected.tetrahedronSimplexBlendMap {n : ℕ} {Y : Type}
    [TopologicalSpace Y] (f g : C(Y, FirstHurewicz.Simplex n)) :
    C((unitInterval) × Y, FirstHurewicz.Simplex n)
    where
  toFun p := tetrahedronSimplexBlend p.1 (f p.2) (g p.2)
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    change
      Continuous fun p : (unitInterval) × Y => (1 - (p.1 : ℝ)) * f p.2 i + (p.1 : ℝ) * g p.2 i
    have hf : Continuous fun p : (unitInterval) × Y => f p.2 i :=
      (continuous_apply i).comp (continuous_subtype_val.comp (f.continuous.comp continuous_snd))
    have hg : Continuous fun p : (unitInterval) × Y => g p.2 i :=
      (continuous_apply i).comp (continuous_subtype_val.comp (g.continuous.comp continuous_snd))
    exact
      ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul hf).add
        ((continuous_subtype_val.comp continuous_fst).mul hg)

private theorem SecondHurewicz.SimplyConnected.tetrahedronSimplexBlend_zero_coordinate {n : ℕ}
    (t : (unitInterval)) (a b : FirstHurewicz.Simplex n) (i : Fin (n + 1)) (ha : a i = 0)
    (hb : b i = 0) : tetrahedronSimplexBlend t a b i = 0 := by
  change (1 - (t : ℝ)) * a i + (t : ℝ) * b i = 0
  simp [ha, hb]

private theorem SecondHurewicz.SimplyConnected.simplexFace_two_zero (s : FirstHurewicz.Simplex 2) :
    (FirstHurewicz.simplexFace 2 0 s : Fin 4 → ℝ) = ![0, s 0, s 1, s 2] := by
  funext i
  fin_cases i
  · exact FirstHurewicz.simplexFace_apply_self 2 0 s
  · exact FirstHurewicz.simplexFace_apply_succAbove 2 0 s 0
  · exact FirstHurewicz.simplexFace_apply_succAbove 2 0 s 1
  · exact FirstHurewicz.simplexFace_apply_succAbove 2 0 s 2

private theorem SecondHurewicz.SimplyConnected.simplexFace_two_one (s : FirstHurewicz.Simplex 2) :
    (FirstHurewicz.simplexFace 2 1 s : Fin 4 → ℝ) = ![s 0, 0, s 1, s 2] := by
  funext i
  fin_cases i
  · exact FirstHurewicz.simplexFace_apply_succAbove 2 1 s 0
  · exact FirstHurewicz.simplexFace_apply_self 2 1 s
  · exact FirstHurewicz.simplexFace_apply_succAbove 2 1 s 1
  · exact FirstHurewicz.simplexFace_apply_succAbove 2 1 s 2

private theorem SecondHurewicz.SimplyConnected.simplexFace_two_two (s : FirstHurewicz.Simplex 2) :
    (FirstHurewicz.simplexFace 2 2 s : Fin 4 → ℝ) = ![s 0, s 1, 0, s 2] := by
  funext i
  fin_cases i
  · exact FirstHurewicz.simplexFace_apply_succAbove 2 2 s 0
  · exact FirstHurewicz.simplexFace_apply_succAbove 2 2 s 1
  · exact FirstHurewicz.simplexFace_apply_self 2 2 s
  · exact FirstHurewicz.simplexFace_apply_succAbove 2 2 s 2

private theorem SecondHurewicz.SimplyConnected.simplexFace_two_three (s : FirstHurewicz.Simplex 2) :
    (FirstHurewicz.simplexFace 2 3 s : Fin 4 → ℝ) = ![s 0, s 1, s 2, 0] := by
  funext i
  fin_cases i
  · exact FirstHurewicz.simplexFace_apply_succAbove 2 3 s 0
  · exact FirstHurewicz.simplexFace_apply_succAbove 2 3 s 1
  · exact FirstHurewicz.simplexFace_apply_succAbove 2 3 s 2
  · exact FirstHurewicz.simplexFace_apply_self 2 3 s

private def SecondHurewicz.SimplyConnected.BasedTetrahedron.ofFaces {X : Type} [TopologicalSpace X]
    {x : X} (τ : C(FirstHurewicz.Simplex 3, X))
    (h :
      ∀ i : Fin 4,
        ∀ s ∈ SecondHurewicz.SimplyConnected.triangleBoundary,
          (τ.comp (FirstHurewicz.simplexFace 2 i)) s = x) :
    SecondHurewicz.SimplyConnected.BasedTetrahedron x :=
  ⟨τ, by
    intro s hs
    obtain ⟨i, j, hij, hi, hj⟩ := hs
    obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hij.symm
    let t := SecondHurewicz.SimplyConnected.simplexFaceInverse 2 i ⟨s, hi⟩
    have ht : t ∈ SecondHurewicz.SimplyConnected.triangleBoundary := by
      refine ⟨k, ?_⟩
      change s (i.succAbove k) = 0
      rw [hk]
      exact hj
    have he := h i t ht
    change τ (FirstHurewicz.simplexFace 2 i t) = x at he
    rw [show FirstHurewicz.simplexFace 2 i t = s from
        SecondHurewicz.SimplyConnected.simplexFace_inverse 2 i ⟨s, hi⟩] at he
    exact he⟩

private def SecondHurewicz.SimplyConnected.tetrahedronQuadrilateralA :
    C(Fin 2 → (unitInterval), FirstHurewicz.Simplex 3)
    where
  toFun
    u :=
    ⟨![1 - Max.max (u 0 : ℝ) (u 1 : ℝ), (u 0 : ℝ) - Min.min (u 0 : ℝ) (u 1 : ℝ),
        Min.min (u 0 : ℝ) (u 1 : ℝ), (u 1 : ℝ) - Min.min (u 0 : ℝ) (u 1 : ℝ)],
      by
      constructor
      · intro i
        fin_cases i
        · exact sub_nonneg.mpr (max_le (u 0).property.2 (u 1).property.2)
        · exact sub_nonneg.mpr (min_le_left _ _)
        · exact le_min (u 0).property.1 (u 1).property.1
        · exact sub_nonneg.mpr (min_le_right _ _)
      · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Matrix.cons_val_zero,
          Matrix.cons_val_succ, Matrix.cons_val_fin_one]
        rcases le_total (u 0 : ℝ) (u 1 : ℝ) with h | h
        · rw [min_eq_left h, max_eq_right h]
          ring
        · rw [min_eq_right h, max_eq_left h]
          ring⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp <;> fun_prop

private theorem SecondHurewicz.SimplyConnected.tetrahedronQuadrilateralA_boundary
    (u : Fin 2 → (unitInterval)) (hu : u ∈ Cube.boundary (Fin 2)) :
    tetrahedronQuadrilateralA u ∈ tetrahedronOneSkeleton := by
  rcases hu with ⟨i, hi | hi⟩
  · fin_cases i
    · change u 0 = 0 at hi
      refine ⟨1, 2, by decide, ?_, ?_⟩ <;>
        simp [DFunLike.coe, tetrahedronQuadrilateralA, hi, min_eq_left (u 1).property.1]
    · change u 1 = 0 at hi
      refine ⟨2, 3, by decide, ?_, ?_⟩ <;>
        simp [DFunLike.coe, tetrahedronQuadrilateralA, hi, min_eq_right (u 0).property.1]
  · fin_cases i
    · change u 0 = 1 at hi
      refine ⟨0, 3, by decide, ?_, ?_⟩ <;>
        simp [DFunLike.coe, tetrahedronQuadrilateralA, hi, min_eq_right (u 1).property.2,
          max_eq_left (u 1).property.2]
    · change u 1 = 1 at hi
      refine ⟨0, 1, by decide, ?_, ?_⟩ <;>
        simp [DFunLike.coe, tetrahedronQuadrilateralA, hi, min_eq_left (u 0).property.2,
          max_eq_right (u 0).property.2]

private theorem
    SecondHurewicz.SimplyConnected.tetrahedronQuadrilateralA_diagonal (t : (unitInterval)) :
    tetrahedronQuadrilateralA ![t, t] ∈ tetrahedronOneSkeleton := by
  refine ⟨1, 3, by decide, ?_, ?_⟩ <;> simp [DFunLike.coe, tetrahedronQuadrilateralA]

private def SecondHurewicz.SimplyConnected.tetrahedronQuarterShift :
    C(FirstHurewicz.Simplex 3, FirstHurewicz.Simplex 3)
    where
  toFun
    s :=
    ⟨![s 3, s 0, s 1, s 2], by
      constructor
      · intro i
        fin_cases i <;> exact stdSimplex.zero_le s _
      · have hs := stdSimplex.sum_eq_one s
        simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Matrix.cons_val_zero,
          Matrix.cons_val_succ, Matrix.cons_val_fin_one] at hs ⊢
        change s 0 + (s 1 + (s 2 + s 3)) = 1 at hs
        linarith⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    fin_cases i
    · exact (continuous_apply 3).comp continuous_subtype_val
    · exact (continuous_apply 0).comp continuous_subtype_val
    · exact (continuous_apply 1).comp continuous_subtype_val
    · exact (continuous_apply 2).comp continuous_subtype_val

private def SecondHurewicz.SimplyConnected.tetrahedronQuarterIndex : Fin 4 ≃ Fin 4
    where
  toFun i := ![1, 2, 3, 0] i
  invFun i := ![3, 0, 1, 2] i
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

@[simp]
private theorem
    SecondHurewicz.SimplyConnected.tetrahedronQuarterShift_index (s : FirstHurewicz.Simplex 3)
    (i : Fin 4) : tetrahedronQuarterShift s (tetrahedronQuarterIndex i) = s i := by
  fin_cases i <;> rfl

private theorem SecondHurewicz.SimplyConnected.tetrahedronQuarterShift_oneSkeleton
    (s : FirstHurewicz.Simplex 3) (hs : s ∈ tetrahedronOneSkeleton) :
    tetrahedronQuarterShift s ∈ tetrahedronOneSkeleton := by
  obtain ⟨i, j, hij, hi, hj⟩ := hs
  exact
    ⟨tetrahedronQuarterIndex i, tetrahedronQuarterIndex j, fun h =>
      hij (tetrahedronQuarterIndex.injective h), by simpa, by simpa⟩

private def
    SecondHurewicz.SimplyConnected.tetrahedronQuadrilateralLoop {X : Type} [TopologicalSpace X]
    {x : X} (τ : BasedTetrahedron x) : GenLoop (Fin 2) X x :=
  ⟨τ.val.comp tetrahedronQuadrilateralA, fun u hu =>
    τ.property _ (tetrahedronQuadrilateralA_boundary u hu)⟩

private theorem SecondHurewicz.SimplyConnected.tetrahedronQuadrilateralLoop_diagonal {X : Type}
    [TopologicalSpace X] {x : X} (τ : BasedTetrahedron x) (t : (unitInterval)) :
    tetrahedronQuadrilateralLoop τ ![t, t] = x :=
  τ.property _ (tetrahedronQuadrilateralA_diagonal t)

private def SecondHurewicz.SimplyConnected.tetrahedronShiftedQuadrilateralLoop {X : Type}
    [TopologicalSpace X] {x : X} (τ : BasedTetrahedron x) : GenLoop (Fin 2) X x :=
  ⟨τ.val.comp (tetrahedronQuarterShift.comp tetrahedronQuadrilateralA), fun u hu =>
    τ.property _
      (tetrahedronQuarterShift_oneSkeleton _ (tetrahedronQuadrilateralA_boundary u hu))⟩

private theorem
    SecondHurewicz.SimplyConnected.tetrahedronShiftedQuadrilateralLoop_diagonal {X : Type}
    [TopologicalSpace X] {x : X} (τ : BasedTetrahedron x) (t : (unitInterval)) :
    tetrahedronShiftedQuadrilateralLoop τ ![t, t] = x :=
  τ.property _ (tetrahedronQuarterShift_oneSkeleton _ (tetrahedronQuadrilateralA_diagonal t))

private def
    SecondHurewicz.SimplyConnected.quarterTurn : C(Fin 2 → (unitInterval), Fin 2 → (unitInterval))
    where
  toFun u := ![u 1, (unitInterval.symm) (u 0)]
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp <;> fun_prop

@[simp]
private theorem SecondHurewicz.SimplyConnected.quarterTurn_apply (u : Fin 2 → (unitInterval)) :
    quarterTurn u = ![u 1, (unitInterval.symm) (u 0)] :=
  rfl

private theorem SecondHurewicz.SimplyConnected.quarterTurn_boundary (u : Fin 2 → (unitInterval))
    (hu : u ∈ Cube.boundary (Fin 2)) : quarterTurn u ∈ Cube.boundary (Fin 2) := by
  rcases hu with ⟨i, hi | hi⟩
  · fin_cases i
    · change u 0 = 0 at hi
      exact ⟨1, Or.inr (by simp [hi])⟩
    · exact ⟨0, Or.inl (by simpa using hi)⟩
  · fin_cases i
    · change u 0 = 1 at hi
      exact ⟨1, Or.inl (by simp [hi])⟩
    · exact ⟨0, Or.inr (by simpa using hi)⟩

private def
    SecondHurewicz.SimplyConnected.rotatedSquareLoop {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 2) X x) : GenLoop (Fin 2) X x :=
  ⟨p.val.comp quarterTurn, fun u hu => p.property _ (quarterTurn_boundary u hu)⟩

private def SecondHurewicz.SimplyConnected.rotationVector (v : ℝ × ℝ) : ℝ × ℝ :=
  (v.2, -v.1)

@[simp]
private theorem SecondHurewicz.SimplyConnected.rotationVector_norm (v : ℝ × ℝ) :
    ‖rotationVector v‖ = ‖v‖ := by simp [rotationVector, Prod.norm_def, max_comm]

private def SecondHurewicz.SimplyConnected.rotationBlend (t : ℝ) (v : ℝ × ℝ) : ℝ × ℝ :=
  ((1 - t) * v.1 + t * v.2, (1 - t) * v.2 - t * v.1)

@[simp]
private theorem
    SecondHurewicz.SimplyConnected.rotationBlend_zero (v : ℝ × ℝ) : rotationBlend 0 v = v := by
  ext <;> simp [rotationBlend]

@[simp]
private theorem SecondHurewicz.SimplyConnected.rotationBlend_one (v : ℝ × ℝ) :
    rotationBlend 1 v = rotationVector v := by ext <;> simp [rotationBlend, rotationVector]

@[simp]
private theorem SecondHurewicz.SimplyConnected.rotationBlend_zero_vector (t : ℝ) :
    rotationBlend t 0 = 0 := by ext <;> simp [rotationBlend]

private theorem
    SecondHurewicz.SimplyConnected.rotationBlend_ne_zero (t : ℝ) {v : ℝ × ℝ} (hv : v ≠ 0) :
    rotationBlend t v ≠ 0 := by
  intro h
  have h₁ : (1 - t) * v.1 + t * v.2 = 0 := congrArg Prod.fst h
  have h₂ : (1 - t) * v.2 - t * v.1 = 0 := congrArg Prod.snd h
  have hd : (1 - t) ^ 2 + t ^ 2 ≠ 0 := by
    have hp : 0 < (1 - t) ^ 2 + t ^ 2 := by nlinarith [sq_nonneg (t - 1 / 2)]
    exact ne_of_gt hp
  have ha : ((1 - t) ^ 2 + t ^ 2) * v.1 = 0 := by linear_combination (1 - t) * h₁ - t * h₂
  have hb : ((1 - t) ^ 2 + t ^ 2) * v.2 = 0 := by linear_combination t * h₁ + (1 - t) * h₂
  apply hv
  exact Prod.ext (mul_eq_zero.mp ha |>.resolve_left hd) (mul_eq_zero.mp hb |>.resolve_left hd)

private theorem SecondHurewicz.SimplyConnected.rotationBlend_continuous :
    Continuous (fun z : ℝ × (ℝ × ℝ) => rotationBlend z.1 z.2) := by
  unfold rotationBlend
  fun_prop

private def SecondHurewicz.SimplyConnected.rotationCentered (u : Fin 2 → (unitInterval)) : ℝ × ℝ :=
  (2 * (u 0 : ℝ) - 1, 2 * (u 1 : ℝ) - 1)

private theorem SecondHurewicz.SimplyConnected.rotationCentered_continuous :
    Continuous rotationCentered := by
  unfold rotationCentered
  fun_prop

private theorem
    SecondHurewicz.SimplyConnected.rotationCentered_norm_le (u : Fin 2 → (unitInterval)) :
    ‖rotationCentered u‖ ≤ 1 := by
  rw [norm_prod_le_iff]
  constructor <;> rw [Real.norm_eq_abs, abs_le]
  · constructor <;> dsimp [rotationCentered] <;> linarith [(u 0).property.1, (u 0).property.2]
  · constructor <;> dsimp [rotationCentered] <;> linarith [(u 1).property.1, (u 1).property.2]

private theorem
    SecondHurewicz.SimplyConnected.rotationCentered_norm_boundary (u : Fin 2 → (unitInterval))
    (hu : u ∈ Cube.boundary (Fin 2)) : ‖rotationCentered u‖ = 1 := by
  apply le_antisymm (rotationCentered_norm_le u)
  rcases hu with ⟨i, hi | hi⟩
  · fin_cases i
    · change u 0 = 0 at hi
      have hc : ‖(rotationCentered u).1‖ = 1 := by norm_num [rotationCentered, hi]
      exact hc ▸ norm_fst_le (rotationCentered u)
    · change u 1 = 0 at hi
      have hc : ‖(rotationCentered u).2‖ = 1 := by norm_num [rotationCentered, hi]
      exact hc ▸ norm_snd_le (rotationCentered u)
  · fin_cases i
    · change u 0 = 1 at hi
      have hc : ‖(rotationCentered u).1‖ = 1 := by norm_num [rotationCentered, hi]
      exact hc ▸ norm_fst_le (rotationCentered u)
    · change u 1 = 1 at hi
      have hc : ‖(rotationCentered u).2‖ = 1 := by norm_num [rotationCentered, hi]
      exact hc ▸ norm_snd_le (rotationCentered u)

private def SecondHurewicz.SimplyConnected.rotationDenominator (t : (unitInterval))
    (u : Fin 2 → (unitInterval)) : ℝ :=
  1 - ‖rotationCentered u‖ + ‖rotationBlend t (rotationCentered u)‖

private theorem SecondHurewicz.SimplyConnected.rotationDenominator_pos (t : (unitInterval))
    (u : Fin 2 → (unitInterval)) : 0 < rotationDenominator t u := by
  by_cases hv : rotationCentered u = 0
  · simp [rotationDenominator, hv]
  · have hnorm : 0 < ‖rotationBlend t (rotationCentered u)‖ :=
      norm_pos_iff.mpr (rotationBlend_ne_zero t hv)
    have hle := rotationCentered_norm_le u
    unfold rotationDenominator
    linarith

private theorem SecondHurewicz.SimplyConnected.rotationDenominator_continuous :
    Continuous
      (fun z : (unitInterval) × (Fin 2 → (unitInterval)) => rotationDenominator z.1 z.2) := by
  unfold rotationDenominator
  apply Continuous.add
  · exact continuous_const.sub (rotationCentered_continuous.comp continuous_snd).norm
  · apply Continuous.norm
    exact
      rotationBlend_continuous.comp
        ((continuous_subtype_val.comp continuous_fst).prodMk
          (rotationCentered_continuous.comp continuous_snd))

private def SecondHurewicz.SimplyConnected.rotationNormalized (t : (unitInterval))
    (u : Fin 2 → (unitInterval)) : ℝ × ℝ :=
  (rotationDenominator t u)⁻¹ • rotationBlend t (rotationCentered u)

private theorem SecondHurewicz.SimplyConnected.rotationNormalized_continuous :
    Continuous
      (fun z : (unitInterval) × (Fin 2 → (unitInterval)) => rotationNormalized z.1 z.2) := by
  unfold rotationNormalized
  apply
    Continuous.smul (f := fun z : (unitInterval) × (Fin 2 → (unitInterval)) =>
      (rotationDenominator z.1 z.2)⁻¹) (g := fun z : (unitInterval) × (Fin 2 → (unitInterval)) =>
      rotationBlend z.1 (rotationCentered z.2))
  · exact
      rotationDenominator_continuous.inv₀ (fun z => ne_of_gt (rotationDenominator_pos z.1 z.2))
  · exact
      rotationBlend_continuous.comp
        ((continuous_subtype_val.comp continuous_fst).prodMk
          (rotationCentered_continuous.comp continuous_snd))

private theorem SecondHurewicz.SimplyConnected.rotationNormalized_norm_le (t : (unitInterval))
    (u : Fin 2 → (unitInterval)) : ‖rotationNormalized t u‖ ≤ 1 := by
  have hd := rotationDenominator_pos t u
  rw [rotationNormalized, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hd.le)]
  rw [inv_mul_le_iff₀ hd, mul_one]
  unfold rotationDenominator
  linarith [rotationCentered_norm_le u]

private theorem SecondHurewicz.SimplyConnected.rotationNormalized_norm_boundary (t : (unitInterval))
    (u : Fin 2 → (unitInterval)) (hu : u ∈ Cube.boundary (Fin 2)) :
    ‖rotationNormalized t u‖ = 1 := by
  have hd := rotationDenominator_pos t u
  have he : rotationDenominator t u = ‖rotationBlend t (rotationCentered u)‖ := by
    simp [rotationDenominator, rotationCentered_norm_boundary u hu]
  rw [rotationNormalized, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hd.le)]
  rw [← he, inv_mul_cancel₀ (ne_of_gt hd)]

@[simp]
private theorem
    SecondHurewicz.SimplyConnected.rotationNormalized_zero (u : Fin 2 → (unitInterval)) :
    rotationNormalized 0 u = rotationCentered u := by
  simp [rotationNormalized, rotationDenominator]

@[simp]
private theorem SecondHurewicz.SimplyConnected.rotationNormalized_one (u : Fin 2 → (unitInterval)) :
    rotationNormalized 1 u = rotationVector (rotationCentered u) := by
  simp [rotationNormalized, rotationDenominator]

private def SecondHurewicz.SimplyConnected.rotationUncenter (v : ℝ × ℝ) (hv : ‖v‖ ≤ 1) :
    Fin 2 → (unitInterval) :=
  ![⟨(v.1 + 1) / 2,
      by
      have h := abs_le.mp (show |v.1| ≤ 1 from (norm_fst_le v).trans hv)
      constructor <;> linarith⟩,
    ⟨(v.2 + 1) / 2,
      by
      have h := abs_le.mp (show |v.2| ≤ 1 from (norm_snd_le v).trans hv)
      constructor <;> linarith⟩]

private theorem SecondHurewicz.SimplyConnected.rotationUncenter_congr {v w : ℝ × ℝ} {hv : ‖v‖ ≤ 1}
    {hw : ‖w‖ ≤ 1} (h : v = w) : rotationUncenter v hv = rotationUncenter w hw := by
  subst w
  rfl

private theorem
    SecondHurewicz.SimplyConnected.rotationUncenter_centered (u : Fin 2 → (unitInterval)) :
    rotationUncenter (rotationCentered u) (rotationCentered_norm_le u) = u := by
  funext i
  fin_cases i <;> apply Subtype.ext <;> dsimp [rotationUncenter, rotationCentered] <;> ring

private theorem
    SecondHurewicz.SimplyConnected.rotationUncenter_vector (u : Fin 2 → (unitInterval)) :
    rotationUncenter (rotationVector (rotationCentered u))
        (by simpa using rotationCentered_norm_le u) =
      quarterTurn u := by
  rw [quarterTurn_apply]
  funext i
  fin_cases i <;> apply Subtype.ext <;>
      dsimp [rotationUncenter, rotationVector, rotationCentered, unitInterval.symm] <;>
    ring

private theorem SecondHurewicz.SimplyConnected.rotationUncenter_boundary (v : ℝ × ℝ) (hv : ‖v‖ ≤ 1)
    (he : ‖v‖ = 1) : rotationUncenter v hv ∈ Cube.boundary (Fin 2) := by
  have hm : 1 ≤ Max.max |v.1| |v.2| := by simpa [Prod.norm_def, Real.norm_eq_abs] using he.ge
  rcases le_max_iff.mp hm with ha | hb
  · have hn : |v.1| = 1 := le_antisymm ((norm_fst_le v).trans hv) ha
    by_cases hp : 0 ≤ v.1
    · have h : v.1 = 1 := by simpa [abs_of_nonneg hp] using hn
      refine ⟨0, Or.inr ?_⟩
      apply Subtype.ext
      dsimp [rotationUncenter]
      linarith
    · have h : v.1 = -1 := by
        rw [abs_of_neg (lt_of_not_ge hp)] at hn
        linarith
      refine ⟨0, Or.inl ?_⟩
      apply Subtype.ext
      dsimp [rotationUncenter]
      linarith
  · have hn : |v.2| = 1 := le_antisymm ((norm_snd_le v).trans hv) hb
    by_cases hp : 0 ≤ v.2
    · have h : v.2 = 1 := by simpa [abs_of_nonneg hp] using hn
      refine ⟨1, Or.inr ?_⟩
      apply Subtype.ext
      dsimp [rotationUncenter]
      linarith
    · have h : v.2 = -1 := by
        rw [abs_of_neg (lt_of_not_ge hp)] at hn
        linarith
      refine ⟨1, Or.inl ?_⟩
      apply Subtype.ext
      dsimp [rotationUncenter]
      linarith

private def SecondHurewicz.SimplyConnected.quarterTurnHomotopyMap :
    C((unitInterval) × (Fin 2 → (unitInterval)), Fin 2 → (unitInterval))
    where
  toFun z := rotationUncenter (rotationNormalized z.1 z.2) (rotationNormalized_norm_le z.1 z.2)
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i
    · apply Continuous.subtype_mk
      change
        Continuous
          (fun z : (unitInterval) × (Fin 2 → (unitInterval)) =>
            ((rotationNormalized z.1 z.2).1 + 1) / 2)
      exact (rotationNormalized_continuous.fst.add continuous_const).div_const 2
    · apply Continuous.subtype_mk
      change
        Continuous
          (fun z : (unitInterval) × (Fin 2 → (unitInterval)) =>
            ((rotationNormalized z.1 z.2).2 + 1) / 2)
      exact (rotationNormalized_continuous.snd.add continuous_const).div_const 2

@[simp]
private theorem
    SecondHurewicz.SimplyConnected.quarterTurnHomotopyMap_zero (u : Fin 2 → (unitInterval)) :
    quarterTurnHomotopyMap (0, u) = u := by
  exact
    (rotationUncenter_congr (hv := rotationNormalized_norm_le 0 u)
          (rotationNormalized_zero u)).trans
      (rotationUncenter_centered u)

@[simp]
private theorem
    SecondHurewicz.SimplyConnected.quarterTurnHomotopyMap_one (u : Fin 2 → (unitInterval)) :
    quarterTurnHomotopyMap (1, u) = quarterTurn u := by
  exact
    (rotationUncenter_congr (hv := rotationNormalized_norm_le 1 u)
          (rotationNormalized_one u)).trans
      (rotationUncenter_vector u)

private theorem SecondHurewicz.SimplyConnected.quarterTurnHomotopyMap_boundary (t : (unitInterval))
    (u : Fin 2 → (unitInterval)) (hu : u ∈ Cube.boundary (Fin 2)) :
    quarterTurnHomotopyMap (t, u) ∈ Cube.boundary (Fin 2) :=
  rotationUncenter_boundary (rotationNormalized t u) (rotationNormalized_norm_le t u)
    (rotationNormalized_norm_boundary t u hu)

private def
    SecondHurewicz.SimplyConnected.rotatedSquareLoop_homotopy {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) :
    p.val.HomotopyRel (rotatedSquareLoop p).val (Cube.boundary (Fin 2))
    where
  toFun z := p (quarterTurnHomotopyMap z)
  continuous_toFun := p.val.continuous.comp quarterTurnHomotopyMap.continuous
  map_zero_left u := congrArg p (quarterTurnHomotopyMap_zero u)
  map_one_left u := congrArg p (quarterTurnHomotopyMap_one u)
  prop' t u
    hu := (p.property _ (quarterTurnHomotopyMap_boundary t u hu)).trans (p.property u hu).symm

private theorem
    SecondHurewicz.SimplyConnected.rotatedSquareLoop_class {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) : (⟦rotatedSquareLoop p⟧ : π_ 2 X x) = ⟦p⟧ := by
  have h : (⟦p⟧ : π_ 2 X x) = ⟦rotatedSquareLoop p⟧ :=
    Quotient.sound
      (show GenLoop.Homotopic p (rotatedSquareLoop p) from ⟨rotatedSquareLoop_homotopy p⟩)
  exact h.symm

private def SecondHurewicz.SimplyConnected.tetrahedronQuadrilateralB :
    C(Fin 2 → (unitInterval), FirstHurewicz.Simplex 3) :=
  (tetrahedronQuarterShift.comp tetrahedronQuadrilateralA).comp quarterTurn

private theorem SecondHurewicz.SimplyConnected.tetrahedronQuadrilateral_perimeter
    (u : Fin 2 → (unitInterval)) (hu : u ∈ Cube.boundary (Fin 2)) :
    tetrahedronQuadrilateralA u = tetrahedronQuadrilateralB u := by
  have tetrahedronQuadrilateralA_zero (u : Fin 2 → (unitInterval)) :
    tetrahedronQuadrilateralA u 0 = 1 - Max.max (u 0 : ℝ) (u 1 : ℝ) := rfl
  have tetrahedronQuadrilateralA_one (u : Fin 2 → (unitInterval)) :
    tetrahedronQuadrilateralA u 1 = (u 0 : ℝ) - Min.min (u 0 : ℝ) (u 1 : ℝ) := rfl
  have tetrahedronQuadrilateralA_two (u : Fin 2 → (unitInterval)) :
    tetrahedronQuadrilateralA u 2 = Min.min (u 0 : ℝ) (u 1 : ℝ) := rfl
  have tetrahedronQuadrilateralA_three (u : Fin 2 → (unitInterval)) :
    tetrahedronQuadrilateralA u 3 = (u 1 : ℝ) - Min.min (u 0 : ℝ) (u 1 : ℝ) := rfl
  have tetrahedronQuarterShift_zero (s : FirstHurewicz.Simplex 3) :
    tetrahedronQuarterShift s 0 = s 3 := rfl
  have tetrahedronQuarterShift_one (s : FirstHurewicz.Simplex 3) :
    tetrahedronQuarterShift s 1 = s 0 := rfl
  have tetrahedronQuarterShift_two (s : FirstHurewicz.Simplex 3) :
    tetrahedronQuarterShift s 2 = s 1 := rfl
  have tetrahedronQuarterShift_three (s : FirstHurewicz.Simplex 3) :
    tetrahedronQuarterShift s 3 = s 2 := rfl
  have tetrahedronQuadrilateralB_apply (u : Fin 2 → (unitInterval)) :
    tetrahedronQuadrilateralB u =
      tetrahedronQuarterShift (tetrahedronQuadrilateralA ![u 1, (unitInterval.symm) (u 0)]) :=
    rfl
  apply Subtype.ext
  funext j
  change tetrahedronQuadrilateralA u j = tetrahedronQuadrilateralB u j
  rcases hu with ⟨i, hi | hi⟩
  · fin_cases i
    · change u 0 = 0 at hi
      fin_cases j <;>
        simp [tetrahedronQuadrilateralA_zero, tetrahedronQuadrilateralA_one,
          tetrahedronQuadrilateralA_two, tetrahedronQuadrilateralA_three,
          tetrahedronQuarterShift_zero, tetrahedronQuarterShift_one, tetrahedronQuarterShift_two,
          tetrahedronQuarterShift_three, tetrahedronQuadrilateralB_apply, hi,
          min_eq_left (u 1).property.2, max_eq_right (u 1).property.2,
          min_eq_left (u 1).property.1, max_eq_right (u 1).property.1]
    · change u 1 = 0 at hi
      fin_cases j <;>
        simp [tetrahedronQuadrilateralA_zero, tetrahedronQuadrilateralA_one,
          tetrahedronQuadrilateralA_two, tetrahedronQuadrilateralA_three,
          tetrahedronQuarterShift_zero, tetrahedronQuarterShift_one, tetrahedronQuarterShift_two,
          tetrahedronQuarterShift_three, tetrahedronQuadrilateralB_apply, hi,
          min_eq_right (u 0).property.1, max_eq_left (u 0).property.1, (u 0).property.2]
  · fin_cases i
    · change u 0 = 1 at hi
      fin_cases j <;>
        simp [tetrahedronQuadrilateralA_zero, tetrahedronQuadrilateralA_one,
          tetrahedronQuadrilateralA_two, tetrahedronQuadrilateralA_three,
          tetrahedronQuarterShift_zero, tetrahedronQuarterShift_one, tetrahedronQuarterShift_two,
          tetrahedronQuarterShift_three, tetrahedronQuadrilateralB_apply, hi,
          min_eq_right (u 1).property.2, max_eq_left (u 1).property.2,
          min_eq_right (u 1).property.1, max_eq_left (u 1).property.1]
    · change u 1 = 1 at hi
      fin_cases j <;>
        simp [tetrahedronQuadrilateralA_zero, tetrahedronQuadrilateralA_one,
          tetrahedronQuadrilateralA_two, tetrahedronQuadrilateralA_three,
          tetrahedronQuarterShift_zero, tetrahedronQuarterShift_one, tetrahedronQuarterShift_two,
          tetrahedronQuarterShift_three, tetrahedronQuadrilateralB_apply, hi,
          min_eq_left (u 0).property.2, max_eq_right (u 0).property.2, (u 0).property.1]

private def
    SecondHurewicz.SimplyConnected.tetrahedronFillingsHomotopy {X : Type} [TopologicalSpace X]
    {x : X} (τ : BasedTetrahedron x) :
    (tetrahedronQuadrilateralLoop τ).val.HomotopyRel
      (rotatedSquareLoop (tetrahedronShiftedQuadrilateralLoop τ)).val (Cube.boundary (Fin 2))
    where
  toFun
    p :=
    τ.val
      (tetrahedronSimplexBlend p.1 (tetrahedronQuadrilateralA p.2)
        (tetrahedronQuadrilateralB p.2))
  continuous_toFun :=
    τ.val.continuous.comp
      (tetrahedronSimplexBlendMap tetrahedronQuadrilateralA tetrahedronQuadrilateralB).continuous
  map_zero_left
    u := by
    change τ.val (tetrahedronSimplexBlend 0 _ _) = τ.val (tetrahedronQuadrilateralA u)
    rw [tetrahedronSimplexBlend_zero]
  map_one_left
    u := by
    change τ.val (tetrahedronSimplexBlend 1 _ _) = τ.val (tetrahedronQuadrilateralB u)
    rw [tetrahedronSimplexBlend_one]
  prop' t u
    hu := by
    change τ.val (tetrahedronSimplexBlend t _ _) = τ.val (tetrahedronQuadrilateralA u)
    rw [← tetrahedronQuadrilateral_perimeter u hu, tetrahedronSimplexBlend_self]

private theorem SecondHurewicz.SimplyConnected.tetrahedronFillings_homotopic {X : Type}
    [TopologicalSpace X] {x : X} (τ : BasedTetrahedron x) :
    GenLoop.Homotopic (tetrahedronQuadrilateralLoop τ)
      (rotatedSquareLoop (tetrahedronShiftedQuadrilateralLoop τ)) :=
  ⟨tetrahedronFillingsHomotopy τ⟩

private theorem
    SecondHurewicz.SimplyConnected.tetrahedronFillings_class {X : Type} [TopologicalSpace X]
    {x : X} (τ : BasedTetrahedron x) :
    (⟦tetrahedronQuadrilateralLoop τ⟧ : π_ 2 X x) = ⟦tetrahedronShiftedQuadrilateralLoop τ⟧ :=
  (Quotient.sound (tetrahedronFillings_homotopic τ)).trans
    (rotatedSquareLoop_class (tetrahedronShiftedQuadrilateralLoop τ))

private def SecondHurewicz.SimplyConnected.triangleCyclicPermutation :
    C(FirstHurewicz.Simplex 2, FirstHurewicz.Simplex 2)
    where
  toFun
    s :=
    ⟨![s 1, s 2, s 0], by
      constructor
      · intro i
        fin_cases i <;> exact stdSimplex.zero_le s _
      · have hs := stdSimplex.sum_eq_one s
        simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Matrix.cons_val_zero,
          Matrix.cons_val_succ, Matrix.cons_val_fin_one] at hs ⊢
        change s 0 + (s 1 + s 2) = 1 at hs
        linarith⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    fin_cases i
    · exact (continuous_apply 1).comp continuous_subtype_val
    · exact (continuous_apply 2).comp continuous_subtype_val
    · exact (continuous_apply 0).comp continuous_subtype_val

private theorem SecondHurewicz.SimplyConnected.triangleCyclicPermutation_boundary
    (s : FirstHurewicz.Simplex 2) (hs : s ∈ triangleBoundary) :
    triangleCyclicPermutation s ∈ triangleBoundary := by
  obtain ⟨i, hi⟩ := hs
  fin_cases i
  · exact ⟨2, hi⟩
  · exact ⟨0, hi⟩
  · exact ⟨1, hi⟩

private def
    SecondHurewicz.SimplyConnected.cyclicBasedTriangle {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedTriangle x) : BasedTriangle x :=
  ⟨τ.val.comp triangleCyclicPermutation, fun s hs =>
    τ.property _ (triangleCyclicPermutation_boundary s hs)⟩

private theorem SecondHurewicz.SimplyConnected.cyclicTriangleQuotient_commonZero
    (u : Fin 2 → (unitInterval)) (hu : u ∈ Cube.boundary (Fin 2)) :
    ∃ i : Fin 3,
      triangleCyclicPermutation (triangleCubeQuotient u) i = 0 ∧
        triangleCubeQuotient (quarterTurn u) i = 0 := by
  have triangleCubeQuotient_apply (t : Fin 2 → (unitInterval)) :
    triangleCubeQuotient t = triangleQuotient (t 0, t 1) := rfl
  have triangleCyclicPermutation_zero (s : FirstHurewicz.Simplex 2) :
    triangleCyclicPermutation s 0 = s 1 := rfl
  have triangleCyclicPermutation_one (s : FirstHurewicz.Simplex 2) :
    triangleCyclicPermutation s 1 = s 2 := rfl
  have triangleCyclicPermutation_two (s : FirstHurewicz.Simplex 2) :
    triangleCyclicPermutation s 2 = s 0 := rfl
  rcases hu with ⟨i, hi | hi⟩
  · fin_cases i
    · change u 0 = 0 at hi
      refine ⟨1, ?_, ?_⟩ <;>
        simp [triangleCubeQuotient_apply, triangleCyclicPermutation_one, hi,
          min_eq_left (u 1).property.1, min_eq_left (u 1).property.2]
    · change u 1 = 0 at hi
      refine ⟨1, ?_, ?_⟩
      · simp [triangleCubeQuotient_apply, triangleCyclicPermutation_one, hi,
          min_eq_right (u 0).property.1]
      · simp [triangleCubeQuotient_apply, hi, (u 0).property.2]
  · fin_cases i
    · change u 0 = 1 at hi
      refine ⟨2, ?_, ?_⟩ <;>
        simp [triangleCubeQuotient_apply, triangleCyclicPermutation_two, hi,
          min_eq_right (u 1).property.1]
    · change u 1 = 1 at hi
      refine ⟨0, ?_, ?_⟩ <;>
        simp [triangleCubeQuotient_apply, triangleCyclicPermutation_zero, hi,
          min_eq_left (u 0).property.2]

private theorem
    SecondHurewicz.SimplyConnected.cyclicTriangleQuotient_blend_boundary (t : (unitInterval))
    (u : Fin 2 → (unitInterval)) (hu : u ∈ Cube.boundary (Fin 2)) :
    tetrahedronSimplexBlend t (triangleCyclicPermutation (triangleCubeQuotient u))
        (triangleCubeQuotient (quarterTurn u)) ∈
      triangleBoundary := by
  obtain ⟨i, hi, hj⟩ := cyclicTriangleQuotient_commonZero u hu
  exact ⟨i, tetrahedronSimplexBlend_zero_coordinate t _ _ i hi hj⟩

private def
    SecondHurewicz.SimplyConnected.cyclicTriangleLoopHomotopy {X : Type} [TopologicalSpace X]
    {x : X} (τ : BasedTriangle x) :
    (basedTriangleLoop (cyclicBasedTriangle τ)).val.HomotopyRel
      (rotatedSquareLoop (basedTriangleLoop τ)).val (Cube.boundary (Fin 2))
    where
  toFun
    p :=
    τ.val
      (tetrahedronSimplexBlend p.1 (triangleCyclicPermutation (triangleCubeQuotient p.2))
        (triangleCubeQuotient (quarterTurn p.2)))
  continuous_toFun :=
    τ.val.continuous.comp
      (tetrahedronSimplexBlendMap (triangleCyclicPermutation.comp triangleCubeQuotient)
          (triangleCubeQuotient.comp quarterTurn)).continuous
  map_zero_left
    u := by
    change
      τ.val (tetrahedronSimplexBlend 0 _ _) =
        τ.val (triangleCyclicPermutation (triangleCubeQuotient u))
    rw [tetrahedronSimplexBlend_zero]
  map_one_left
    u := by
    change τ.val (tetrahedronSimplexBlend 1 _ _) = τ.val (triangleCubeQuotient (quarterTurn u))
    rw [tetrahedronSimplexBlend_one]
  prop' t u
    hu :=
    (τ.property _ (cyclicTriangleQuotient_blend_boundary t u hu)).trans
      ((basedTriangleLoop (cyclicBasedTriangle τ)).property u hu).symm

@[simp]
private theorem
    SecondHurewicz.SimplyConnected.basedTriangleClass_cyclic {X : Type} [TopologicalSpace X]
    {x : X} (τ : BasedTriangle x) :
    basedTriangleClass (cyclicBasedTriangle τ) = basedTriangleClass τ := by
  have h :
    GenLoop.Homotopic (basedTriangleLoop (cyclicBasedTriangle τ))
      (rotatedSquareLoop (basedTriangleLoop τ)) :=
    ⟨cyclicTriangleLoopHomotopy τ⟩
  have he :
    (⟦basedTriangleLoop (cyclicBasedTriangle τ)⟧ : π_ 2 X x) =
      ⟦rotatedSquareLoop (basedTriangleLoop τ)⟧ :=
    Quotient.sound h
  exact congrArg Additive.ofMul (he.trans (rotatedSquareLoop_class (basedTriangleLoop τ)))

private abbrev SecondHurewicz.SimplyConnected.SubdivisionSquare :=
  Fin 2 → (unitInterval)

private theorem
    SecondHurewicz.SimplyConnected.subdivisionSquare_boundary_cases (u : SubdivisionSquare)
    (hu : u ∈ Cube.boundary (Fin 2)) : u 0 = 0 ∨ u 0 = 1 ∨ u 1 = 0 ∨ u 1 = 1 := by
  rcases hu with ⟨i, hi⟩
  fin_cases i
  · rcases hi with hi | hi
    · exact Or.inl hi
    · exact Or.inr (Or.inl hi)
  · rcases hi with hi | hi
    · exact Or.inr (Or.inr (Or.inl hi))
    · exact Or.inr (Or.inr (Or.inr hi))

private inductive
    SecondHurewicz.SimplyConnected.SubdivisionSameSide (a b : SubdivisionSquare) : Prop
  | zero (i : Fin 2) (ha : a i = 0) (hb : b i = 0)
  | one (i : Fin 2) (ha : a i = 1) (hb : b i = 1)
  | diagonal (ha : a 0 = a 1) (hb : b 0 = b 1)

private def SecondHurewicz.SimplyConnected.subdivisionBlend (t : (unitInterval))
    (a b : SubdivisionSquare) : SubdivisionSquare := fun i => Set.Icc.convexComb (a i) (b i) t

@[simp]
private theorem SecondHurewicz.SimplyConnected.subdivisionBlend_zero (a b : SubdivisionSquare) :
    subdivisionBlend 0 a b = a := by
  funext i
  exact Set.Icc.convexComb_zero _ _

@[simp]
private theorem SecondHurewicz.SimplyConnected.subdivisionBlend_one (a b : SubdivisionSquare) :
    subdivisionBlend 1 a b = b := by
  funext i
  exact Set.Icc.convexComb_one _ _

private def SecondHurewicz.SimplyConnected.subdivisionBlendMap
    (f g : C(SubdivisionSquare, SubdivisionSquare)) :
    C((unitInterval) × SubdivisionSquare, SubdivisionSquare)
    where
  toFun u := subdivisionBlend u.1 (f u.2) (g u.2)
  continuous_toFun := by
    apply continuous_pi
    intro i
    exact
      Set.Icc.continuous_convexComb_prod.comp
        (((continuous_apply i).comp (f.continuous.comp continuous_snd)).prodMk
          (((continuous_apply i).comp (g.continuous.comp continuous_snd)).prodMk continuous_fst))

private theorem
    SecondHurewicz.SimplyConnected.subdivisionOnDiagonal {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) (hd : ∀ t : (unitInterval), p ![t, t] = x)
    (a : SubdivisionSquare) (ha : a 0 = a 1) : p a = x := by
  have h : a = ![a 0, a 0] := by
    funext i
    fin_cases i
    · rfl
    · exact ha.symm
  exact (congrArg p h).trans (hd _)

private theorem
    SecondHurewicz.SimplyConnected.subdivisionBlend_based {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) (hd : ∀ t : (unitInterval), p ![t, t] = x)
    {a b : SubdivisionSquare} (h : SubdivisionSameSide a b) (t : (unitInterval)) :
    p (subdivisionBlend t a b) = x := by
  cases h with
  | zero i ha hb =>
    apply p.property
    exact ⟨i, Or.inl (by simp [subdivisionBlend, ha, hb])⟩
  | one i ha hb =>
    apply p.property
    exact ⟨i, Or.inr (by simp [subdivisionBlend, ha, hb])⟩
  | diagonal ha hb =>
    apply subdivisionOnDiagonal p hd
    simp only [subdivisionBlend, ha, hb]

private def SecondHurewicz.SimplyConnected.subdivisionPullbackLoop {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) (f : C(SubdivisionSquare, SubdivisionSquare))
    (hf : ∀ u ∈ Cube.boundary (Fin 2), p (f u) = x) : GenLoop (Fin 2) X x :=
  ⟨p.val.comp f, hf⟩

private def
    SecondHurewicz.SimplyConnected.subdivisionLinearHomotopy {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) (hd : ∀ t : (unitInterval), p ![t, t] = x)
    (f g : C(SubdivisionSquare, SubdivisionSquare))
    (hf : ∀ u ∈ Cube.boundary (Fin 2), p (f u) = x)
    (hg : ∀ u ∈ Cube.boundary (Fin 2), p (g u) = x)
    (hfg : ∀ u ∈ Cube.boundary (Fin 2), SubdivisionSameSide (f u) (g u)) :
    (subdivisionPullbackLoop p f hf).val.HomotopyRel (subdivisionPullbackLoop p g hg).val
      (Cube.boundary (Fin 2))
    where
  toFun u := p (subdivisionBlend u.1 (f u.2) (g u.2))
  continuous_toFun := p.val.continuous.comp (subdivisionBlendMap f g).continuous
  map_zero_left
    u := by
    change p (subdivisionBlend 0 (f u) (g u)) = p (f u)
    rw [subdivisionBlend_zero]
  map_one_left
    u := by
    change p (subdivisionBlend 1 (f u) (g u)) = p (g u)
    rw [subdivisionBlend_one]
  prop' t u hu := (subdivisionBlend_based p hd (hfg u hu) t).trans (hf u hu).symm

private def
    SecondHurewicz.SimplyConnected.subdivisionSubMin (u v : (unitInterval)) : (unitInterval) :=
  ⟨(u : ℝ) - Min.min (u : ℝ) (v : ℝ), sub_nonneg.mpr (min_le_left _ _),
    (sub_le_self _ (le_min u.property.1 v.property.1)).trans u.property.2⟩

@[simp]
private theorem SecondHurewicz.SimplyConnected.subdivisionSubMin_zero_left (v : (unitInterval)) :
    subdivisionSubMin 0 v = 0 := by
  apply Subtype.ext
  simp [subdivisionSubMin, v.property.1]

@[simp]
private theorem SecondHurewicz.SimplyConnected.subdivisionSubMin_zero_right (u : (unitInterval)) :
    subdivisionSubMin u 0 = u := by
  apply Subtype.ext
  simp [subdivisionSubMin, u.property.1]

@[simp]
private theorem SecondHurewicz.SimplyConnected.subdivisionSubMin_one_left (v : (unitInterval)) :
    subdivisionSubMin 1 v = (unitInterval.symm) v := by
  apply Subtype.ext
  simp [subdivisionSubMin, v.property.2]

@[simp]
private theorem SecondHurewicz.SimplyConnected.subdivisionSubMin_one_right (u : (unitInterval)) :
    subdivisionSubMin u 1 = 0 := by
  apply Subtype.ext
  simp [subdivisionSubMin, u.property.2]

private def SecondHurewicz.SimplyConnected.subdivisionLowerProductMap :
    C(SubdivisionSquare, SubdivisionSquare)
    where
  toFun u := ![u 0, u 0 * u 1]
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_apply 0
    · change Continuous fun u : SubdivisionSquare => u 0 * u 1
      apply Continuous.subtype_mk
      exact
        (continuous_subtype_val.comp (continuous_apply 0)).mul
          (continuous_subtype_val.comp (continuous_apply 1))

private def SecondHurewicz.SimplyConnected.subdivisionUpperProductMap :
    C(SubdivisionSquare, SubdivisionSquare)
    where
  toFun u := ![u 0, Set.Icc.convexComb (u 0) 1 (u 1)]
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_apply 0
    · change Continuous fun u : SubdivisionSquare => Set.Icc.convexComb (u 0) 1 (u 1)
      unfold Set.Icc.convexComb
      fun_prop

private def SecondHurewicz.SimplyConnected.subdivisionUpperConeMap :
    C(SubdivisionSquare, SubdivisionSquare)
    where
  toFun u := ![u 0 * (unitInterval.symm) (u 1), Set.Icc.convexComb (u 0) 1 (u 1)]
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i
    · change Continuous fun u : SubdivisionSquare => u 0 * (unitInterval.symm) (u 1)
      apply Continuous.subtype_mk
      change Continuous fun u : SubdivisionSquare => (u 0 : ℝ) * (1 - (u 1 : ℝ))
      fun_prop
    · change Continuous fun u : SubdivisionSquare => Set.Icc.convexComb (u 0) 1 (u 1)
      unfold Set.Icc.convexComb
      fun_prop

private def SecondHurewicz.SimplyConnected.subdivisionLowerTriangleMap :
    C(SubdivisionSquare, SubdivisionSquare)
    where
  toFun u := ![u 0, Min.min (u 0) (u 1)]
  continuous_toFun := by fun_prop

private def SecondHurewicz.SimplyConnected.subdivisionUpperTriangleMap :
    C(SubdivisionSquare, SubdivisionSquare)
    where
  toFun u := ![subdivisionSubMin (u 0) (u 1), u 0]
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i
    · change Continuous fun u : SubdivisionSquare => subdivisionSubMin (u 0) (u 1)
      unfold subdivisionSubMin
      fun_prop
    · exact continuous_apply 0

private theorem SecondHurewicz.SimplyConnected.subdivisionLowerProductMap_based {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) (u : SubdivisionSquare)
    (hu : u ∈ Cube.boundary (Fin 2)) : p (subdivisionLowerProductMap u) = x := by
  rcases subdivisionSquare_boundary_cases u hu with h | h | h | h
  · exact p.property _ ⟨0, Or.inl (by simp [subdivisionLowerProductMap, h])⟩
  · exact p.property _ ⟨0, Or.inr (by simp [subdivisionLowerProductMap, h])⟩
  · exact p.property _ ⟨1, Or.inl (by simp [subdivisionLowerProductMap, h])⟩
  · exact subdivisionOnDiagonal p hd _ (by simp [subdivisionLowerProductMap, h])

private theorem SecondHurewicz.SimplyConnected.subdivisionUpperProductMap_based {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) (u : SubdivisionSquare)
    (hu : u ∈ Cube.boundary (Fin 2)) : p (subdivisionUpperProductMap u) = x := by
  rcases subdivisionSquare_boundary_cases u hu with h | h | h | h
  · exact p.property _ ⟨0, Or.inl (by simp [subdivisionUpperProductMap, h])⟩
  · exact p.property _ ⟨0, Or.inr (by simp [subdivisionUpperProductMap, h])⟩
  · exact subdivisionOnDiagonal p hd _ (by simp [subdivisionUpperProductMap, h])
  · exact p.property _ ⟨1, Or.inr (by simp [subdivisionUpperProductMap, h])⟩

private theorem SecondHurewicz.SimplyConnected.subdivisionUpperConeMap_based {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) (u : SubdivisionSquare)
    (hu : u ∈ Cube.boundary (Fin 2)) : p (subdivisionUpperConeMap u) = x := by
  rcases subdivisionSquare_boundary_cases u hu with h | h | h | h
  · exact p.property _ ⟨0, Or.inl (by simp [subdivisionUpperConeMap, h])⟩
  · exact p.property _ ⟨1, Or.inr (by simp [subdivisionUpperConeMap, h])⟩
  · exact subdivisionOnDiagonal p hd _ (by simp [subdivisionUpperConeMap, h])
  · exact p.property _ ⟨0, Or.inl (by simp [subdivisionUpperConeMap, h])⟩

private theorem SecondHurewicz.SimplyConnected.subdivisionLowerTriangleMap_based {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) (u : SubdivisionSquare)
    (hu : u ∈ Cube.boundary (Fin 2)) : p (subdivisionLowerTriangleMap u) = x := by
  rcases subdivisionSquare_boundary_cases u hu with h | h | h | h
  · exact p.property _ ⟨0, Or.inl (by simp [subdivisionLowerTriangleMap, h])⟩
  · exact p.property _ ⟨0, Or.inr (by simp [subdivisionLowerTriangleMap, h])⟩
  · exact p.property _ ⟨1, Or.inl (by simp [subdivisionLowerTriangleMap, h])⟩
  · exact
      subdivisionOnDiagonal p hd _
        (by
          simp [subdivisionLowerTriangleMap, h,
            min_eq_left (show u 0 ≤ (1 : (unitInterval)) from (u 0).property.2)])

private theorem SecondHurewicz.SimplyConnected.subdivisionUpperTriangleMap_based {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) (u : SubdivisionSquare)
    (hu : u ∈ Cube.boundary (Fin 2)) : p (subdivisionUpperTriangleMap u) = x := by
  rcases subdivisionSquare_boundary_cases u hu with h | h | h | h
  · exact p.property _ ⟨1, Or.inl (by simp [subdivisionUpperTriangleMap, h])⟩
  · exact p.property _ ⟨1, Or.inr (by simp [subdivisionUpperTriangleMap, h])⟩
  · exact subdivisionOnDiagonal p hd _ (by simp [subdivisionUpperTriangleMap, h])
  · exact p.property _ ⟨0, Or.inl (by simp [subdivisionUpperTriangleMap, h])⟩

private def
    SecondHurewicz.SimplyConnected.subdivisionLowerProductLoop {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    GenLoop (Fin 2) X x :=
  subdivisionPullbackLoop p subdivisionLowerProductMap (subdivisionLowerProductMap_based p hd)

private def
    SecondHurewicz.SimplyConnected.subdivisionUpperProductLoop {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    GenLoop (Fin 2) X x :=
  subdivisionPullbackLoop p subdivisionUpperProductMap (subdivisionUpperProductMap_based p hd)

private def SecondHurewicz.SimplyConnected.subdivisionUpperConeLoop {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    GenLoop (Fin 2) X x :=
  subdivisionPullbackLoop p subdivisionUpperConeMap (subdivisionUpperConeMap_based p hd)

private def
    SecondHurewicz.SimplyConnected.subdivisionLowerTriangleLoop {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    GenLoop (Fin 2) X x :=
  subdivisionPullbackLoop p subdivisionLowerTriangleMap (subdivisionLowerTriangleMap_based p hd)

private def
    SecondHurewicz.SimplyConnected.subdivisionUpperTriangleLoop {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    GenLoop (Fin 2) X x :=
  subdivisionPullbackLoop p subdivisionUpperTriangleMap (subdivisionUpperTriangleMap_based p hd)

private theorem SecondHurewicz.SimplyConnected.subdivisionLowerProductTriangle_sides
    (u : SubdivisionSquare) (hu : u ∈ Cube.boundary (Fin 2)) :
    SubdivisionSameSide (subdivisionLowerProductMap u) (subdivisionLowerTriangleMap u) := by
  rcases subdivisionSquare_boundary_cases u hu with h | h | h | h
  · exact
      .zero 0 (by simp [subdivisionLowerProductMap, h]) (by simp [subdivisionLowerTriangleMap, h])
  · exact
      .one 0 (by simp [subdivisionLowerProductMap, h]) (by simp [subdivisionLowerTriangleMap, h])
  · exact
      .zero 1 (by simp [subdivisionLowerProductMap, h]) (by simp [subdivisionLowerTriangleMap, h])
  · exact
      .diagonal (by simp [subdivisionLowerProductMap, h])
        (by
          simp [subdivisionLowerTriangleMap, h,
            min_eq_left (show u 0 ≤ (1 : (unitInterval)) from (u 0).property.2)])

private theorem
    SecondHurewicz.SimplyConnected.subdivisionUpperProductCone_sides (u : SubdivisionSquare)
    (hu : u ∈ Cube.boundary (Fin 2)) :
    SubdivisionSameSide (subdivisionUpperProductMap u) (subdivisionUpperConeMap u) := by
  rcases subdivisionSquare_boundary_cases u hu with h | h | h | h
  · exact .zero 0 (by simp [subdivisionUpperProductMap, h]) (by simp [subdivisionUpperConeMap, h])
  · exact .one 1 (by simp [subdivisionUpperProductMap, h]) (by simp [subdivisionUpperConeMap, h])
  · exact
      .diagonal (by simp [subdivisionUpperProductMap, h]) (by simp [subdivisionUpperConeMap, h])
  · exact .one 1 (by simp [subdivisionUpperProductMap, h]) (by simp [subdivisionUpperConeMap, h])

private theorem
    SecondHurewicz.SimplyConnected.subdivisionUpperConeTriangle_sides (u : SubdivisionSquare)
    (hu : u ∈ Cube.boundary (Fin 2)) :
    SubdivisionSameSide (subdivisionUpperConeMap u) (subdivisionUpperTriangleMap u) := by
  rcases subdivisionSquare_boundary_cases u hu with h | h | h | h
  · exact
      .zero 0 (by simp [subdivisionUpperConeMap, h]) (by simp [subdivisionUpperTriangleMap, h])
  · exact .one 1 (by simp [subdivisionUpperConeMap, h]) (by simp [subdivisionUpperTriangleMap, h])
  · exact
      .diagonal (by simp [subdivisionUpperConeMap, h]) (by simp [subdivisionUpperTriangleMap, h])
  · exact
      .zero 0 (by simp [subdivisionUpperConeMap, h]) (by simp [subdivisionUpperTriangleMap, h])

private def SecondHurewicz.SimplyConnected.subdivisionLowerTriangleHomotopy {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    (subdivisionLowerProductLoop p hd).val.HomotopyRel (subdivisionLowerTriangleLoop p hd).val
      (Cube.boundary (Fin 2)) :=
  subdivisionLinearHomotopy p hd _ _ (subdivisionLowerProductMap_based p hd)
    (subdivisionLowerTriangleMap_based p hd) subdivisionLowerProductTriangle_sides

private def
    SecondHurewicz.SimplyConnected.subdivisionUpperConeHomotopy {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    (subdivisionUpperProductLoop p hd).val.HomotopyRel (subdivisionUpperConeLoop p hd).val
      (Cube.boundary (Fin 2)) :=
  subdivisionLinearHomotopy p hd _ _ (subdivisionUpperProductMap_based p hd)
    (subdivisionUpperConeMap_based p hd) subdivisionUpperProductCone_sides

private def SecondHurewicz.SimplyConnected.subdivisionUpperTriangleHomotopy {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    (subdivisionUpperConeLoop p hd).val.HomotopyRel (subdivisionUpperTriangleLoop p hd).val
      (Cube.boundary (Fin 2)) :=
  subdivisionLinearHomotopy p hd _ _ (subdivisionUpperConeMap_based p hd)
    (subdivisionUpperTriangleMap_based p hd) subdivisionUpperConeTriangle_sides

private theorem
    SecondHurewicz.SimplyConnected.subdivision_toLoop_transAt {X : Type*} [TopologicalSpace X]
    {x : X} (i : Fin 2) (a b : GenLoop (Fin 2) X x) :
    GenLoop.toLoop i (GenLoop.transAt i a b) = (GenLoop.toLoop i a).trans (GenLoop.toLoop i b) := by
  rw [← GenLoop.fromLoop_trans_toLoop, GenLoop.to_from]

private theorem SecondHurewicz.SimplyConnected.subdivision_transAt_homotopic {X : Type*}
    [TopologicalSpace X] {x : X} (i : Fin 2) {a b c d : GenLoop (Fin 2) X x}
    (ha : GenLoop.Homotopic a c) (hb : GenLoop.Homotopic b d) :
    GenLoop.Homotopic (GenLoop.transAt i a b) (GenLoop.transAt i c d) := by
  apply GenLoop.homotopicFrom i
  rw [subdivision_toLoop_transAt, subdivision_toLoop_transAt]
  rcases GenLoop.homotopicTo i ha with ⟨Ha⟩
  rcases GenLoop.homotopicTo i hb with ⟨Hb⟩
  exact ⟨Ha.hcomp Hb⟩

private noncomputable def SecondHurewicz.SimplyConnected.subdivisionWarpCoordinate :
    C((unitInterval) × (unitInterval), (unitInterval))
    where
  toFun
    p :=
    Set.Icc.convexComb (Set.projIcc 0 1 zero_le_one (2 * (p.2 : ℝ) - 1))
      (Set.projIcc 0 1 zero_le_one (2 * (p.2 : ℝ))) p.1
  continuous_toFun := by
    unfold Set.Icc.convexComb
    fun_prop

private theorem
    SecondHurewicz.SimplyConnected.subdivisionWarpCoordinate_apply (u v : (unitInterval)) :
    subdivisionWarpCoordinate (u, v) =
      Set.Icc.convexComb (Set.projIcc 0 1 zero_le_one (2 * (v : ℝ) - 1))
        (Set.projIcc 0 1 zero_le_one (2 * (v : ℝ))) u :=
  rfl

@[simp]
private theorem SecondHurewicz.SimplyConnected.subdivisionWarpCoordinate_zero (u : (unitInterval)) :
    subdivisionWarpCoordinate (u, 0) = 0 := by
  simp [subdivisionWarpCoordinate, Set.projIcc, Set.Icc.convexComb]

@[simp]
private theorem SecondHurewicz.SimplyConnected.subdivisionWarpCoordinate_one (u : (unitInterval)) :
    subdivisionWarpCoordinate (u, 1) = 1 := by
  norm_num [subdivisionWarpCoordinate, Set.projIcc, Set.Icc.convexComb]

private theorem
    SecondHurewicz.SimplyConnected.subdivisionWarpCoordinate_of_le_half (u v : (unitInterval))
    (hv : (v : ℝ) ≤ 1 / 2) :
    subdivisionWarpCoordinate (u, v) = u * Set.projIcc 0 1 zero_le_one (2 * (v : ℝ)) := by
  have hzero : Set.projIcc 0 1 zero_le_one (2 * (v : ℝ) - 1) = (0 : (unitInterval)) :=
    Set.projIcc_of_le_left zero_le_one (by linarith)
  rw [subdivisionWarpCoordinate_apply, hzero]
  apply Subtype.ext
  simp

private theorem
    SecondHurewicz.SimplyConnected.subdivisionWarpCoordinate_of_half_le (u v : (unitInterval))
    (hv : 1 / 2 ≤ (v : ℝ)) :
    subdivisionWarpCoordinate (u, v) =
      Set.Icc.convexComb u 1 (Set.projIcc 0 1 zero_le_one (2 * (v : ℝ) - 1)) := by
  have hone : Set.projIcc 0 1 zero_le_one (2 * (v : ℝ)) = (1 : (unitInterval)) :=
    Set.projIcc_of_right_le zero_le_one (by linarith)
  rw [subdivisionWarpCoordinate_apply, hone]
  apply Subtype.ext
  simp only [Set.Icc.coe_convexComb]
  change (1 - (u : ℝ)) * _ + (u : ℝ) * 1 = (1 - _) * (u : ℝ) + _ * 1
  ring

private theorem
    SecondHurewicz.SimplyConnected.subdivisionWarpCoordinate_of_half_lt (u v : (unitInterval))
    (hv : 1 / 2 < (v : ℝ)) :
    subdivisionWarpCoordinate (u, v) =
      Set.Icc.convexComb u 1 (Set.projIcc 0 1 zero_le_one (2 * (v : ℝ) - 1)) :=
  subdivisionWarpCoordinate_of_half_le u v hv.le

private def
    SecondHurewicz.SimplyConnected.subdivisionWarpMap : C(SubdivisionSquare, SubdivisionSquare)
    where
  toFun u := ![u 0, subdivisionWarpCoordinate (u 0, u 1)]
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_apply 0
    · change Continuous fun u : SubdivisionSquare => subdivisionWarpCoordinate (u 0, u 1)
      exact
        subdivisionWarpCoordinate.continuous.comp
          (show Continuous (fun u : SubdivisionSquare => (u 0, u 1)) from
            (continuous_apply 0).prodMk (continuous_apply 1))

private theorem SecondHurewicz.SimplyConnected.subdivisionWarpMap_sides (u : SubdivisionSquare)
    (hu : u ∈ Cube.boundary (Fin 2)) : SubdivisionSameSide u (subdivisionWarpMap u) := by
  rcases subdivisionSquare_boundary_cases u hu with h | h | h | h
  · exact .zero 0 h (by simp [subdivisionWarpMap, h])
  · exact .one 0 h (by simp [subdivisionWarpMap, h])
  · exact .zero 1 h (by simp [subdivisionWarpMap, h])
  · exact .one 1 h (by simp [subdivisionWarpMap, h])

private theorem
    SecondHurewicz.SimplyConnected.subdivisionWarpMap_based {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) (u : SubdivisionSquare) (hu : u ∈ Cube.boundary (Fin 2)) :
    p (subdivisionWarpMap u) = x := by
  rcases subdivisionSquare_boundary_cases u hu with h | h | h | h
  · exact p.property _ ⟨0, Or.inl (by simp [subdivisionWarpMap, h])⟩
  · exact p.property _ ⟨0, Or.inr (by simp [subdivisionWarpMap, h])⟩
  · exact p.property _ ⟨1, Or.inl (by simp [subdivisionWarpMap, h])⟩
  · exact p.property _ ⟨1, Or.inr (by simp [subdivisionWarpMap, h])⟩

private def
    SecondHurewicz.SimplyConnected.subdivisionWarpLoop {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 2) X x) : GenLoop (Fin 2) X x :=
  subdivisionPullbackLoop p subdivisionWarpMap (subdivisionWarpMap_based p)

private def SecondHurewicz.SimplyConnected.subdivisionWarpHomotopy {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    p.val.HomotopyRel (subdivisionWarpLoop p).val (Cube.boundary (Fin 2)) :=
  subdivisionLinearHomotopy p hd (ContinuousMap.id _) subdivisionWarpMap p.property
    (subdivisionWarpMap_based p) subdivisionWarpMap_sides

private theorem SecondHurewicz.SimplyConnected.subdivisionWarpLoop_eq_transAt {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    subdivisionWarpLoop p =
      GenLoop.transAt (1 : Fin 2) (subdivisionLowerProductLoop p hd)
        (subdivisionUpperProductLoop p hd) := by
  apply GenLoop.ext
  intro u
  change
    p ![u 0, subdivisionWarpCoordinate (u 0, u 1)] =
      if (u 1 : ℝ) ≤ 1 / 2 then
        subdivisionLowerProductLoop p hd
          (Function.update u 1 (Set.projIcc 0 1 zero_le_one (2 * (u 1 : ℝ))))
      else
        subdivisionUpperProductLoop p hd
          (Function.update u 1 (Set.projIcc 0 1 zero_le_one (2 * (u 1 : ℝ) - 1)))
  split_ifs with h
  · simpa [subdivisionLowerProductLoop, subdivisionPullbackLoop, subdivisionLowerProductMap] using
      congrArg (fun v : (unitInterval) => p ![u 0, v])
        (subdivisionWarpCoordinate_of_le_half (u 0) (u 1) h)
  · simpa [subdivisionUpperProductLoop, subdivisionPullbackLoop, subdivisionUpperProductMap] using
      congrArg (fun v : (unitInterval) => p ![u 0, v])
        (subdivisionWarpCoordinate_of_half_lt (u 0) (u 1) (lt_of_not_ge h))

private theorem
    SecondHurewicz.SimplyConnected.subdivision_homotopic {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    GenLoop.Homotopic p
      (GenLoop.transAt (1 : Fin 2) (subdivisionLowerTriangleLoop p hd)
        (subdivisionUpperTriangleLoop p hd)) := by
  have hw : GenLoop.Homotopic p (subdivisionWarpLoop p) := ⟨subdivisionWarpHomotopy p hd⟩
  rw [subdivisionWarpLoop_eq_transAt p hd] at hw
  apply hw.trans
  apply subdivision_transAt_homotopic
  · exact ⟨subdivisionLowerTriangleHomotopy p hd⟩
  · exact ⟨(subdivisionUpperConeHomotopy p hd).trans (subdivisionUpperTriangleHomotopy p hd)⟩

private theorem
    SecondHurewicz.SimplyConnected.subdivision_class {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 2) X x) (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    (⟦p⟧ : π_ 2 X x) =
      ((· * ·) : π_ 2 X x → π_ 2 X x → π_ 2 X x) ⟦subdivisionLowerTriangleLoop p hd⟧
        ⟦subdivisionUpperTriangleLoop p hd⟧ := by
  have h :
    (⟦p⟧ : π_ 2 X x) =
      (⟦GenLoop.transAt (1 : Fin 2) (subdivisionLowerTriangleLoop p hd)
            (subdivisionUpperTriangleLoop p hd)⟧ :
        π_ 2 X x) :=
    Quotient.sound (subdivision_homotopic p hd)
  exact
    h.trans
      ((HomotopyGroup.mul_spec (i := (1 : Fin 2)) (p := subdivisionUpperTriangleLoop p hd) (q :=
            subdivisionLowerTriangleLoop p hd)).symm.trans
        (mul_comm _ _))

private theorem
    SecondHurewicz.SimplyConnected.subdivision_additiveClass {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    Additive.ofMul (⟦p⟧ : π_ 2 X x) =
      ((· + ·) : Additive (π_ 2 X x) → Additive (π_ 2 X x) → Additive (π_ 2 X x))
        (Additive.ofMul (⟦subdivisionLowerTriangleLoop p hd⟧ : π_ 2 X x))
        (Additive.ofMul (⟦subdivisionUpperTriangleLoop p hd⟧ : π_ 2 X x)) :=
  congrArg Additive.ofMul (subdivision_class p hd)

private theorem SecondHurewicz.SimplyConnected.tetrahedronQuadrilateralA_lower
    (u : Fin 2 → (unitInterval)) :
    tetrahedronQuadrilateralA (subdivisionLowerTriangleMap u) =
      FirstHurewicz.simplexFace 2 3 (triangleCubeQuotient u) := by
  have tetrahedronQuadrilateralA_zero (u : Fin 2 → (unitInterval)) :
    tetrahedronQuadrilateralA u 0 = 1 - Max.max (u 0 : ℝ) (u 1 : ℝ) := rfl
  have tetrahedronQuadrilateralA_one (u : Fin 2 → (unitInterval)) :
    tetrahedronQuadrilateralA u 1 = (u 0 : ℝ) - Min.min (u 0 : ℝ) (u 1 : ℝ) := rfl
  have tetrahedronQuadrilateralA_two (u : Fin 2 → (unitInterval)) :
    tetrahedronQuadrilateralA u 2 = Min.min (u 0 : ℝ) (u 1 : ℝ) := rfl
  have tetrahedronQuadrilateralA_three (u : Fin 2 → (unitInterval)) :
    tetrahedronQuadrilateralA u 3 = (u 1 : ℝ) - Min.min (u 0 : ℝ) (u 1 : ℝ) := rfl
  have triangleCubeQuotient_apply (t : Fin 2 → (unitInterval)) :
    triangleCubeQuotient t = triangleQuotient (t 0, t 1) := rfl
  apply Subtype.ext
  funext j
  change
    tetrahedronQuadrilateralA ![u 0, Min.min (u 0) (u 1)] j =
      (FirstHurewicz.simplexFace 2 3 (triangleCubeQuotient u) : Fin 4 → ℝ) j
  rw [simplexFace_two_three]
  fin_cases j <;>
    simp [tetrahedronQuadrilateralA_zero, tetrahedronQuadrilateralA_one,
      tetrahedronQuadrilateralA_two, tetrahedronQuadrilateralA_three, triangleCubeQuotient_apply]

private theorem SecondHurewicz.SimplyConnected.tetrahedronQuadrilateralA_upper
    (u : Fin 2 → (unitInterval)) :
    tetrahedronQuadrilateralA (subdivisionUpperTriangleMap u) =
      FirstHurewicz.simplexFace 2 1 (triangleCubeQuotient u) := by
  have tetrahedronQuadrilateralA_zero (u : Fin 2 → (unitInterval)) :
    tetrahedronQuadrilateralA u 0 = 1 - Max.max (u 0 : ℝ) (u 1 : ℝ) := rfl
  have tetrahedronQuadrilateralA_one (u : Fin 2 → (unitInterval)) :
    tetrahedronQuadrilateralA u 1 = (u 0 : ℝ) - Min.min (u 0 : ℝ) (u 1 : ℝ) := rfl
  have tetrahedronQuadrilateralA_two (u : Fin 2 → (unitInterval)) :
    tetrahedronQuadrilateralA u 2 = Min.min (u 0 : ℝ) (u 1 : ℝ) := rfl
  have tetrahedronQuadrilateralA_three (u : Fin 2 → (unitInterval)) :
    tetrahedronQuadrilateralA u 3 = (u 1 : ℝ) - Min.min (u 0 : ℝ) (u 1 : ℝ) := rfl
  have triangleCubeQuotient_apply (t : Fin 2 → (unitInterval)) :
    triangleCubeQuotient t = triangleQuotient (t 0, t 1) := rfl
  have subdivisionSubMin_coe (u v : (unitInterval)) :
    (subdivisionSubMin u v : ℝ) = (u : ℝ) - Min.min (u : ℝ) (v : ℝ) := rfl
  have hm : (u 0 : ℝ) - Min.min (u 0 : ℝ) (u 1 : ℝ) ≤ (u 0 : ℝ) :=
    sub_le_self _ (le_min (u 0).property.1 (u 1).property.1)
  apply Subtype.ext
  funext j
  change
    tetrahedronQuadrilateralA ![subdivisionSubMin (u 0) (u 1), u 0] j =
      (FirstHurewicz.simplexFace 2 1 (triangleCubeQuotient u) : Fin 4 → ℝ) j
  rw [simplexFace_two_one]
  fin_cases j <;>
    simp [tetrahedronQuadrilateralA_zero, tetrahedronQuadrilateralA_one,
      tetrahedronQuadrilateralA_two, tetrahedronQuadrilateralA_three, triangleCubeQuotient_apply,
      subdivisionSubMin_coe, min_eq_left hm, max_eq_right hm]

private theorem SecondHurewicz.SimplyConnected.tetrahedronQuarterShift_face_three
    (s : FirstHurewicz.Simplex 2) :
    tetrahedronQuarterShift (FirstHurewicz.simplexFace 2 3 s) = FirstHurewicz.simplexFace 2 0 s :=
  by
  apply Subtype.ext
  funext j
  change
    tetrahedronQuarterShift (FirstHurewicz.simplexFace 2 3 s) j =
      (FirstHurewicz.simplexFace 2 0 s : Fin 4 → ℝ) j
  rw [simplexFace_two_zero]
  fin_cases j
  · exact FirstHurewicz.simplexFace_apply_self 2 3 s
  · exact FirstHurewicz.simplexFace_apply_succAbove 2 3 s 0
  · exact FirstHurewicz.simplexFace_apply_succAbove 2 3 s 1
  · exact FirstHurewicz.simplexFace_apply_succAbove 2 3 s 2

private theorem SecondHurewicz.SimplyConnected.tetrahedronQuarterShift_face_one
    (s : FirstHurewicz.Simplex 2) :
    tetrahedronQuarterShift (FirstHurewicz.simplexFace 2 1 s) =
      FirstHurewicz.simplexFace 2 2 (triangleCyclicPermutation (triangleCyclicPermutation s)) := by
  apply Subtype.ext
  funext j
  change
    tetrahedronQuarterShift (FirstHurewicz.simplexFace 2 1 s) j =
      (FirstHurewicz.simplexFace 2 2 (triangleCyclicPermutation (triangleCyclicPermutation s)) :
          Fin 4 → ℝ)
        j
  rw [simplexFace_two_two]
  fin_cases j
  · exact FirstHurewicz.simplexFace_apply_succAbove 2 1 s 2
  · exact FirstHurewicz.simplexFace_apply_succAbove 2 1 s 0
  · exact FirstHurewicz.simplexFace_apply_self 2 1 s
  · exact FirstHurewicz.simplexFace_apply_succAbove 2 1 s 1

private theorem SecondHurewicz.SimplyConnected.tetrahedronLowerLoop_eq_face {X : Type}
    [TopologicalSpace X] {x : X} (τ : BasedTetrahedron x) :
    subdivisionLowerTriangleLoop (tetrahedronQuadrilateralLoop τ)
        (tetrahedronQuadrilateralLoop_diagonal τ) =
      basedTriangleLoop (basedTetrahedronFace τ 3) := by
  apply GenLoop.ext
  intro u
  change
    τ.val (tetrahedronQuadrilateralA (subdivisionLowerTriangleMap u)) =
      τ.val (FirstHurewicz.simplexFace 2 3 (triangleCubeQuotient u))
  rw [tetrahedronQuadrilateralA_lower]

private theorem SecondHurewicz.SimplyConnected.tetrahedronUpperLoop_eq_face {X : Type}
    [TopologicalSpace X] {x : X} (τ : BasedTetrahedron x) :
    subdivisionUpperTriangleLoop (tetrahedronQuadrilateralLoop τ)
        (tetrahedronQuadrilateralLoop_diagonal τ) =
      basedTriangleLoop (basedTetrahedronFace τ 1) := by
  apply GenLoop.ext
  intro u
  change
    τ.val (tetrahedronQuadrilateralA (subdivisionUpperTriangleMap u)) =
      τ.val (FirstHurewicz.simplexFace 2 1 (triangleCubeQuotient u))
  rw [tetrahedronQuadrilateralA_upper]

private theorem SecondHurewicz.SimplyConnected.tetrahedronShiftedLowerLoop_eq_face {X : Type}
    [TopologicalSpace X] {x : X} (τ : BasedTetrahedron x) :
    subdivisionLowerTriangleLoop (tetrahedronShiftedQuadrilateralLoop τ)
        (tetrahedronShiftedQuadrilateralLoop_diagonal τ) =
      basedTriangleLoop (basedTetrahedronFace τ 0) := by
  apply GenLoop.ext
  intro u
  change
    τ.val (tetrahedronQuarterShift (tetrahedronQuadrilateralA (subdivisionLowerTriangleMap u))) =
      τ.val (FirstHurewicz.simplexFace 2 0 (triangleCubeQuotient u))
  rw [tetrahedronQuadrilateralA_lower, tetrahedronQuarterShift_face_three]

private theorem SecondHurewicz.SimplyConnected.tetrahedronShiftedUpperLoop_eq_face {X : Type}
    [TopologicalSpace X] {x : X} (τ : BasedTetrahedron x) :
    subdivisionUpperTriangleLoop (tetrahedronShiftedQuadrilateralLoop τ)
        (tetrahedronShiftedQuadrilateralLoop_diagonal τ) =
      basedTriangleLoop (cyclicBasedTriangle (cyclicBasedTriangle (basedTetrahedronFace τ 2))) := by
  apply GenLoop.ext
  intro u
  change
    τ.val (tetrahedronQuarterShift (tetrahedronQuadrilateralA (subdivisionUpperTriangleMap u))) =
      τ.val
        (FirstHurewicz.simplexFace 2 2
          (triangleCyclicPermutation (triangleCyclicPermutation (triangleCubeQuotient u))))
  rw [tetrahedronQuadrilateralA_upper, tetrahedronQuarterShift_face_one]

private theorem SecondHurewicz.SimplyConnected.basedTetrahedron_pair_relation {X : Type}
    [TopologicalSpace X] {x : X} (τ : BasedTetrahedron x) :
    basedTriangleClass (basedTetrahedronFace τ 3) +
        basedTriangleClass (basedTetrahedronFace τ 1) =
      basedTriangleClass (basedTetrahedronFace τ 0) +
        basedTriangleClass (basedTetrahedronFace τ 2) := by
  have hA :=
    subdivision_additiveClass (tetrahedronQuadrilateralLoop τ)
      (tetrahedronQuadrilateralLoop_diagonal τ)
  rw [tetrahedronLowerLoop_eq_face, tetrahedronUpperLoop_eq_face] at hA
  have hB :=
    subdivision_additiveClass (tetrahedronShiftedQuadrilateralLoop τ)
      (tetrahedronShiftedQuadrilateralLoop_diagonal τ)
  rw [tetrahedronShiftedLowerLoop_eq_face, tetrahedronShiftedUpperLoop_eq_face] at hB
  change
    Additive.ofMul (⟦tetrahedronShiftedQuadrilateralLoop τ⟧ : π_ 2 X x) =
      basedTriangleClass (basedTetrahedronFace τ 0) +
        basedTriangleClass
          (cyclicBasedTriangle (cyclicBasedTriangle (basedTetrahedronFace τ 2))) at hB
  simp only [basedTriangleClass_cyclic] at hB
  exact hA.symm.trans ((congrArg Additive.ofMul (tetrahedronFillings_class τ)).trans hB)

private theorem SecondHurewicz.SimplyConnected.basedTetrahedron_boundary_relation {X : Type}
    [TopologicalSpace X] {x : X} (τ : BasedTetrahedron x) :
    basedTriangleClass (basedTetrahedronFace τ 0) -
            basedTriangleClass (basedTetrahedronFace τ 1) +
          basedTriangleClass (basedTetrahedronFace τ 2) -
        basedTriangleClass (basedTetrahedronFace τ 3) =
      0 := by
  calc
    _ =
        (basedTriangleClass (basedTetrahedronFace τ 0) +
            basedTriangleClass (basedTetrahedronFace τ 2)) -
          (basedTriangleClass (basedTetrahedronFace τ 3) +
            basedTriangleClass (basedTetrahedronFace τ 1)) := by abel
    _ = 0 := sub_eq_zero.mpr (basedTetrahedron_pair_relation τ).symm

private theorem SecondHurewicz.SimplyConnected.basedTetrahedron_signed_relation {X : Type}
    [TopologicalSpace X] {x : X} (τ : BasedTetrahedron x) :
    ∑ i : Fin 4, (-1 : ℤ) ^ i.val • basedTriangleClass (basedTetrahedronFace τ i) = 0 := by
  have h := basedTetrahedron_boundary_relation τ
  simpa [Fin.sum_univ_succ, sub_eq_add_neg, add_assoc] using h

private def SecondHurewicz.SimplyConnected.normalizedTetrahedron {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (smp : FirstHurewicz.SingularSimplex X 3) :
    BasedTetrahedron x :=
  BasedTetrahedron.ofFaces (normalizedTetrahedronMap x smp)
    (normalizedTetrahedronMap_face_boundary x smp)

@[simp]
private theorem
    SecondHurewicz.SimplyConnected.normalizedTetrahedron_face {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (smp : FirstHurewicz.SingularSimplex X 3) (i : Fin 4) :
    basedTetrahedronFace (normalizedTetrahedron x smp) i =
      normalizedTriangle x (smp.comp (FirstHurewicz.simplexFace 2 i)) := by
  apply Subtype.ext
  exact normalizedTetrahedronMap_face x smp i

private theorem SecondHurewicz.SimplyConnected.normalizedTriangle_boundary_relation {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    (smp : FirstHurewicz.SingularSimplex X 3) :
    ∑ i : Fin 4,
        (-1 : ℤ) ^ i.val •
          basedTriangleClass (normalizedTriangle x (smp.comp (FirstHurewicz.simplexFace 2 i))) =
      0 := by
  simpa only [normalizedTetrahedron_face] using
    basedTetrahedron_signed_relation (normalizedTetrahedron x smp)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def SecondHurewicz.SimplyConnected.squareAffineTriangle (v : Fin 3 → Fin 2 × Fin 2) :
    C(FirstHurewicz.Simplex 2, (unitInterval) × (unitInterval)) :=
  ((FirstHurewicz.pathSimplex Path.id).prodMap (FirstHurewicz.pathSimplex Path.id)).comp
    (PeriodTorusHigherHomology.productAffineSimplex
      (fun i =>
        (SingularMayerVietoris.stdVertices 1 (v i).1,
          SingularMayerVietoris.stdVertices 1 (v i).2)))

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem
    SecondHurewicz.SimplyConnected.squareAffineTriangle_fst_coe (v : Fin 3 → Fin 2 × Fin 2)
    (s : FirstHurewicz.Simplex 2) :
    ((squareAffineTriangle v s).1 : ℝ) =
      ∑ i, s i * SingularMayerVietoris.stdVertices 1 (v i).1 1 := by
  change
    SingularMayerVietoris.affineSimplex (fun i => SingularMayerVietoris.stdVertices 1 (v i).1) s
        1 =
      _
  exact SingularMayerVietoris.affineSimplex_coordinate _ _ _

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem
    SecondHurewicz.SimplyConnected.squareAffineTriangle_snd_coe (v : Fin 3 → Fin 2 × Fin 2)
    (s : FirstHurewicz.Simplex 2) :
    ((squareAffineTriangle v s).2 : ℝ) =
      ∑ i, s i * SingularMayerVietoris.stdVertices 1 (v i).2 1 := by
  change
    SingularMayerVietoris.affineSimplex (fun i => SingularMayerVietoris.stdVertices 1 (v i).2) s
        1 =
      _
  exact SingularMayerVietoris.affineSimplex_coordinate _ _ _

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def SecondHurewicz.SimplyConnected.lowerProductTriangle :
    C(FirstHurewicz.Simplex 2, (unitInterval) × (unitInterval)) :=
  squareAffineTriangle ![(0, 0), (1, 0), (1, 1)]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def SecondHurewicz.SimplyConnected.upperProductTriangle :
    C(FirstHurewicz.Simplex 2, (unitInterval) × (unitInterval)) :=
  squareAffineTriangle ![(0, 0), (0, 1), (1, 1)]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def SecondHurewicz.SimplyConnected.leftProductDegenerate :
    C(FirstHurewicz.Simplex 2, (unitInterval) × (unitInterval)) :=
  squareAffineTriangle ![(0, 0), (0, 0), (0, 1)]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def SecondHurewicz.SimplyConnected.bottomProductDegenerate :
    C(FirstHurewicz.Simplex 2, (unitInterval) × (unitInterval)) :=
  squareAffineTriangle ![(0, 0), (0, 0), (1, 0)]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
private theorem
    SecondHurewicz.SimplyConnected.lowerProductTriangle_fst (s : FirstHurewicz.Simplex 2) :
    ((lowerProductTriangle s).1 : ℝ) = s 1 + s 2 := by
  simp [lowerProductTriangle, squareAffineTriangle_fst_coe, SingularMayerVietoris.stdVertices,
    stdSimplex.vertex, Fin.sum_univ_succ, Pi.single_apply]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
private theorem
    SecondHurewicz.SimplyConnected.lowerProductTriangle_snd (s : FirstHurewicz.Simplex 2) :
    ((lowerProductTriangle s).2 : ℝ) = s 2 := by
  simp [lowerProductTriangle, squareAffineTriangle_snd_coe, SingularMayerVietoris.stdVertices,
    stdSimplex.vertex, Fin.sum_univ_succ, Pi.single_apply]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
private theorem
    SecondHurewicz.SimplyConnected.upperProductTriangle_fst (s : FirstHurewicz.Simplex 2) :
    ((upperProductTriangle s).1 : ℝ) = s 2 := by
  simp [upperProductTriangle, squareAffineTriangle_fst_coe, SingularMayerVietoris.stdVertices,
    stdSimplex.vertex, Fin.sum_univ_succ, Pi.single_apply]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
private theorem
    SecondHurewicz.SimplyConnected.upperProductTriangle_snd (s : FirstHurewicz.Simplex 2) :
    ((upperProductTriangle s).2 : ℝ) = s 1 + s 2 := by
  simp [upperProductTriangle, squareAffineTriangle_snd_coe, SingularMayerVietoris.stdVertices,
    stdSimplex.vertex, Fin.sum_univ_succ, Pi.single_apply]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
private theorem
    SecondHurewicz.SimplyConnected.leftProductDegenerate_fst (s : FirstHurewicz.Simplex 2) :
    (leftProductDegenerate s).1 = 0 := by
  apply Subtype.ext
  simp [leftProductDegenerate, squareAffineTriangle_fst_coe, SingularMayerVietoris.stdVertices,
    stdSimplex.vertex, Fin.sum_univ_succ, Pi.single_apply]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
private theorem
    SecondHurewicz.SimplyConnected.bottomProductDegenerate_snd (s : FirstHurewicz.Simplex 2) :
    (bottomProductDegenerate s).2 = 0 := by
  apply Subtype.ext
  simp [bottomProductDegenerate, squareAffineTriangle_snd_coe, SingularMayerVietoris.stdVertices,
    stdSimplex.vertex, Fin.sum_univ_succ, Pi.single_apply]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def SecondHurewicz.SimplyConnected.lowerSquareTriangle :
    C(FirstHurewicz.Simplex 2, Fin 2 → (unitInterval)) :=
  SecondHurewicz.squareCoordinates.comp lowerProductTriangle

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def SecondHurewicz.SimplyConnected.upperSquareTriangle :
    C(FirstHurewicz.Simplex 2, Fin 2 → (unitInterval)) :=
  SecondHurewicz.squareCoordinates.comp upperProductTriangle

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
private theorem
    SecondHurewicz.SimplyConnected.lowerSquareTriangle_zero (s : FirstHurewicz.Simplex 2) :
    (lowerSquareTriangle s 0 : ℝ) = s 1 + s 2 := by simp [lowerSquareTriangle]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
private theorem
    SecondHurewicz.SimplyConnected.lowerSquareTriangle_one (s : FirstHurewicz.Simplex 2) :
    (lowerSquareTriangle s 1 : ℝ) = s 2 := by simp [lowerSquareTriangle]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
private theorem
    SecondHurewicz.SimplyConnected.upperSquareTriangle_zero (s : FirstHurewicz.Simplex 2) :
    (upperSquareTriangle s 0 : ℝ) = s 2 := by simp [upperSquareTriangle]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
private theorem
    SecondHurewicz.SimplyConnected.upperSquareTriangle_one (s : FirstHurewicz.Simplex 2) :
    (upperSquareTriangle s 1 : ℝ) = s 1 + s 2 := by simp [upperSquareTriangle]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem SecondHurewicz.SimplyConnected.productSquareChain_four_triangles :
    SecondHurewicz.productSquareChain =
      FirstHurewicz.simplexChain ((unitInterval) × (unitInterval)) 2 lowerProductTriangle -
            FirstHurewicz.simplexChain ((unitInterval) × (unitInterval)) 2 leftProductDegenerate -
          FirstHurewicz.simplexChain ((unitInterval) × (unitInterval)) 2 upperProductTriangle +
        FirstHurewicz.simplexChain ((unitInterval) × (unitInterval)) 2 bottomProductDegenerate := by
  rw [SecondHurewicz.productSquareChain, SecondHurewicz.intervalChain, FirstHurewicz.pathChain,
    PeriodTorusHigherHomology.crossProductEdge_simplex,
    PeriodTorusHigherHomology.formalEdgeCrossProduct_simplex_succ,
    PeriodTorusHigherHomology.formalPointCrossProduct_edge_boundary,
    PeriodTorusHigherHomology.formalBoundary_edge_simplex]
  simp only [map_sub, PeriodTorusHigherHomology.formalEdgeCrossProduct_zero_simplex_right,
    SingularMayerVietoris.formalMap_simplex, SingularMayerVietoris.formalCone_simplex,
    PeriodTorusHigherHomology.productAffineChainMap_simplex, FirstHurewicz.inducedChain_simplex]
  change
    (FirstHurewicz.simplexChain ((unitInterval) × (unitInterval)) 2 lowerProductTriangle -
          FirstHurewicz.simplexChain ((unitInterval) × (unitInterval)) 2 leftProductDegenerate) -
        (FirstHurewicz.simplexChain ((unitInterval) × (unitInterval)) 2 upperProductTriangle -
          FirstHurewicz.simplexChain ((unitInterval) × (unitInterval)) 2
            bottomProductDegenerate) =
      _
  abel

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem SecondHurewicz.SimplyConnected.squareMap_leftProductDegenerate {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x) :
    (SecondHurewicz.squareMap p).comp leftProductDegenerate =
      ContinuousMap.const (FirstHurewicz.Simplex 2) x := by
  ext s
  apply GenLoop.boundary p
  refine ⟨0, Or.inl ?_⟩
  rw [SecondHurewicz.squareCoordinates_zero, leftProductDegenerate_fst]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem SecondHurewicz.SimplyConnected.squareMap_bottomProductDegenerate {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x) :
    (SecondHurewicz.squareMap p).comp bottomProductDegenerate =
      ContinuousMap.const (FirstHurewicz.Simplex 2) x := by
  ext s
  apply GenLoop.boundary p
  refine ⟨1, Or.inl ?_⟩
  rw [SecondHurewicz.squareCoordinates_one, bottomProductDegenerate_snd]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem
    SecondHurewicz.SimplyConnected.squareChain_two_triangles {X : Type} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) :
    SecondHurewicz.squareChain p =
      FirstHurewicz.simplexChain X 2 (p.val.comp lowerSquareTriangle) -
        FirstHurewicz.simplexChain X 2 (p.val.comp upperSquareTriangle) := by
  rw [SecondHurewicz.squareChain, SecondHurewicz.suspensionOne_toLoop,
    productSquareChain_four_triangles]
  simp only [map_add, map_sub, FirstHurewicz.inducedChain_simplex,
    squareMap_leftProductDegenerate, squareMap_bottomProductDegenerate]
  change
    (FirstHurewicz.simplexChain X 2 (p.val.comp lowerSquareTriangle) -
            FirstHurewicz.simplexChain X 2 (ContinuousMap.const (FirstHurewicz.Simplex 2) x)) -
          FirstHurewicz.simplexChain X 2 (p.val.comp upperSquareTriangle) +
        FirstHurewicz.simplexChain X 2 (ContinuousMap.const (FirstHurewicz.Simplex 2) x) =
      _
  abel

private theorem SecondHurewicz.SimplyConnected.triangleQuotient_lowerProductTriangle :
    triangleQuotient.comp lowerProductTriangle = ContinuousMap.id (FirstHurewicz.Simplex 2) := by
  apply ContinuousMap.ext
  intro s
  apply Subtype.ext
  funext i
  have hs := stdSimplex.sum_eq_one s
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hs
  change s 0 + (s 1 + s 2) = 1 at hs
  have hle : s 2 ≤ s 1 + s 2 := le_add_of_nonneg_left (stdSimplex.zero_le s 1)
  fin_cases i
  · change 1 - ((lowerProductTriangle s).1 : ℝ) = s 0
    rw [lowerProductTriangle_fst]
    linarith
  · change
      ((lowerProductTriangle s).1 : ℝ) -
          Min.min ((lowerProductTriangle s).1 : ℝ) ((lowerProductTriangle s).2 : ℝ) =
        s 1
    rw [lowerProductTriangle_fst, lowerProductTriangle_snd, min_eq_right hle]
    ring
  · change Min.min ((lowerProductTriangle s).1 : ℝ) ((lowerProductTriangle s).2 : ℝ) = s 2
    rw [lowerProductTriangle_fst, lowerProductTriangle_snd, min_eq_right hle]

private theorem SecondHurewicz.SimplyConnected.triangleQuotient_upperProductTriangle_boundary
    (s : FirstHurewicz.Simplex 2) :
    triangleQuotient (upperProductTriangle s) ∈ triangleBoundary := by
  refine ⟨1, ?_⟩
  rw [triangleQuotient_one, upperProductTriangle_fst, upperProductTriangle_snd,
    min_eq_left (le_add_of_nonneg_left (stdSimplex.zero_le s 1)), sub_self]

private theorem
    SecondHurewicz.SimplyConnected.basedTriangleLoop_lower {X : Type} [TopologicalSpace X]
    {x : X} (τ : BasedTriangle x) : (basedTriangleLoop τ).val.comp lowerSquareTriangle = τ.val := by
  change (SecondHurewicz.squareMap (basedTriangleLoop τ)).comp lowerProductTriangle = _
  rw [squareMap_basedTriangleLoop, ContinuousMap.comp_assoc,
    triangleQuotient_lowerProductTriangle, ContinuousMap.comp_id]

private theorem
    SecondHurewicz.SimplyConnected.basedTriangleLoop_upper {X : Type} [TopologicalSpace X]
    {x : X} (τ : BasedTriangle x) :
    (basedTriangleLoop τ).val.comp upperSquareTriangle =
      ContinuousMap.const (FirstHurewicz.Simplex 2) x := by
  change (SecondHurewicz.squareMap (basedTriangleLoop τ)).comp upperProductTriangle = _
  rw [squareMap_basedTriangleLoop]
  ext s
  exact τ.property _ (triangleQuotient_upperProductTriangle_boundary s)

private theorem SecondHurewicz.SimplyConnected.squareChain_basedTriangleLoop {X : Type}
    [TopologicalSpace X] {x : X} (τ : BasedTriangle x) :
    SecondHurewicz.squareChain (basedTriangleLoop τ) =
      FirstHurewicz.simplexChain X 2 τ.val -
        FirstHurewicz.simplexChain X 2 (ContinuousMap.const (FirstHurewicz.Simplex 2) x) := by
  rw [squareChain_two_triangles, basedTriangleLoop_lower, basedTriangleLoop_upper]

private def
    SecondHurewicz.SimplyConnected.basedTriangleCycle {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedTriangle x) :
    SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 2 :=
  SingularMayerVietoris.ModuleHomology.mkCycle (FirstHurewicz.singularComplex X) 2
    (FirstHurewicz.simplexChain X 2 τ.val -
      FirstHurewicz.simplexChain X 2 (ContinuousMap.const (FirstHurewicz.Simplex 2) x))
    (by
      rw [← squareChain_basedTriangleLoop]
      exact SecondHurewicz.squareChain_boundary (basedTriangleLoop τ))

@[simp]
private theorem
    SecondHurewicz.SimplyConnected.basedTriangleCycle_val {X : Type} [TopologicalSpace X]
    {x : X} (τ : BasedTriangle x) :
    (basedTriangleCycle τ).val =
      FirstHurewicz.simplexChain X 2 τ.val -
        FirstHurewicz.simplexChain X 2 (ContinuousMap.const (FirstHurewicz.Simplex 2) x) :=
  rfl

private theorem
    SecondHurewicz.SimplyConnected.hurewicz_basedTriangleClass {X : Type} [TopologicalSpace X]
    {x : X} (τ : BasedTriangle x) :
    SecondHurewicz.hurewiczMap x (basedTriangleClass τ) =
      SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 2
        (basedTriangleCycle τ) := by
  change
    SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 2
        (SecondHurewicz.squareCycle (basedTriangleLoop τ)) =
      _
  congr 1
  apply Subtype.ext
  exact squareChain_basedTriangleLoop τ

private def
    SecondHurewicz.SimplyConnected.secondHomologyDesc {X : Type} [TopologicalSpace X] {M : Type*}
    [AddCommGroup M] [Module ℤ M] (F : FirstHurewicz.Chains X 2 →ₗ[ℤ] M)
    (hF :
      ∀ b : FirstHurewicz.Chains X 3, F (((FirstHurewicz.singularComplex X).d 3 2).hom b) = 0) :
    SingularMayerVietoris.SingularHomology X 2 →ₗ[ℤ] M :=
  PeriodTorusHigherHomology.homologyDesc (FirstHurewicz.singularComplex X) 2
    (F.comp
      (SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 2).subtype)
    (fun b => hF b)

@[simp]
private theorem SecondHurewicz.SimplyConnected.secondHomologyDesc_cycleClass {X : Type}
    [TopologicalSpace X] {M : Type*} [AddCommGroup M] [Module ℤ M]
    (F : FirstHurewicz.Chains X 2 →ₗ[ℤ] M)
    (hF : ∀ b : FirstHurewicz.Chains X 3, F (((FirstHurewicz.singularComplex X).d 3 2).hom b) = 0)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 2) :
    secondHomologyDesc F hF
        (SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 2 c) =
      F c.1 :=
  PeriodTorusHigherHomology.homologyDesc_cycleClass (FirstHurewicz.singularComplex X) 2 _ _ c

private theorem SecondHurewicz.SimplyConnected.comp_secondHomologyDesc_eq_id {X : Type}
    [TopologicalSpace X] {M : Type*} [AddCommGroup M] [Module ℤ M]
    (F : FirstHurewicz.Chains X 2 →ₗ[ℤ] M)
    (hF : ∀ b : FirstHurewicz.Chains X 3, F (((FirstHurewicz.singularComplex X).d 3 2).hom b) = 0)
    (g : M →ₗ[ℤ] SingularMayerVietoris.SingularHomology X 2)
    (hg :
      ∀ c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 2,
        g (F c.1) =
          SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 2 c) :
    g.comp (secondHomologyDesc F hF) = LinearMap.id := by
  apply PeriodTorusHigherHomology.homologyLinearMap_ext (FirstHurewicz.singularComplex X) 2
  intro c
  simpa only [LinearMap.comp_apply, secondHomologyDesc_cycleClass, LinearMap.id_apply] using hg c

private def
    SecondHurewicz.SimplyConnected.chainAugmentation (X : Type) [TopologicalSpace X] (n : ℕ) :
    FirstHurewicz.Chains X n →ₗ[ℤ] ℤ :=
  FirstHurewicz.chainLift X n fun _ => 1

@[simp]
private theorem
    SecondHurewicz.SimplyConnected.chainAugmentation_simplex (X : Type) [TopologicalSpace X]
    (n : ℕ) (smp : FirstHurewicz.SingularSimplex X n) :
    chainAugmentation X n (FirstHurewicz.simplexChain X n smp) = 1 :=
  FirstHurewicz.chainLift_simplex X n _ smp

private theorem SecondHurewicz.SimplyConnected.chainAugmentation_boundaryTwo (X : Type)
    [TopologicalSpace X] (c : FirstHurewicz.Chains X 2) :
    chainAugmentation X 1 (FirstHurewicz.boundaryTwo X c) = chainAugmentation X 2 c := by
  have h : (chainAugmentation X 1).comp (FirstHurewicz.boundaryTwo X) = chainAugmentation X 2 := by
    apply FirstHurewicz.chainMap_ext X 2
    intro smp
    simp only [LinearMap.comp_apply, FirstHurewicz.boundaryTwo_simplex, map_add, map_sub,
      chainAugmentation_simplex, sub_self, zero_add]
  exact LinearMap.congr_fun h c

@[simp]
private theorem
    SecondHurewicz.SimplyConnected.chainAugmentation_twoCycle (X : Type) [TopologicalSpace X]
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 2) :
    chainAugmentation X 2 c.1 = 0 := by
  rw [← chainAugmentation_boundaryTwo]
  have hc :=
    SingularMayerVietoris.ModuleHomology.cycle_condition (FirstHurewicz.singularComplex X) 2 c
  change FirstHurewicz.boundaryTwo X c.1 = 0 at hc
  rw [hc, map_zero]

private theorem
    SecondHurewicz.SimplyConnected.chainLift_sub_constant (X : Type) [TopologicalSpace X]
    {M : Type} [AddCommGroup M] [Module ℤ M] (n : ℕ) (f : FirstHurewicz.SingularSimplex X n → M)
    (m : M) (c : FirstHurewicz.Chains X n) :
    FirstHurewicz.chainLift X n (fun smp => f smp - m) c =
      FirstHurewicz.chainLift X n f c - chainAugmentation X n c • m := by
  have h :
    FirstHurewicz.chainLift X n (fun smp => f smp - m) =
      FirstHurewicz.chainLift X n f -
        (LinearMap.toSpanSingleton ℤ M m).comp (chainAugmentation X n) := by
    apply FirstHurewicz.chainMap_ext X n
    intro smp
    simp only [FirstHurewicz.chainLift_simplex, LinearMap.sub_apply, LinearMap.comp_apply,
      chainAugmentation_simplex, LinearMap.toSpanSingleton_apply_one]
  exact
    (LinearMap.congr_fun h c).trans
      (congrArg (fun z : M => FirstHurewicz.chainLift X n f c - z)
        (int_smul_eq_zsmul (inferInstance : Module ℤ M) (chainAugmentation X n c) m))

private theorem SecondHurewicz.SimplyConnected.chainLift_sub_constant_twoCycle (X : Type)
    [TopologicalSpace X] {M : Type} [AddCommGroup M] [Module ℤ M]
    (f : FirstHurewicz.SingularSimplex X 2 → M) (m : M)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 2) :
    FirstHurewicz.chainLift X 2 (fun smp => f smp - m) c.1 = FirstHurewicz.chainLift X 2 f c.1 := by
  rw [chainLift_sub_constant, chainAugmentation_twoCycle, zero_smul, sub_zero]

private def SecondHurewicz.SimplyConnected.triangleClassOperator {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) : FirstHurewicz.Chains X 2 →ₗ[ℤ] Additive (π_ 2 X x) :=
  FirstHurewicz.chainLift X 2 fun smp => basedTriangleClass (normalizedTriangle x smp)

@[simp]
private theorem SecondHurewicz.SimplyConnected.triangleClassOperator_simplex {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    (smp : FirstHurewicz.SingularSimplex X 2) :
    triangleClassOperator x (FirstHurewicz.simplexChain X 2 smp) =
      basedTriangleClass (normalizedTriangle x smp) :=
  FirstHurewicz.chainLift_simplex X 2 _ smp

private theorem SecondHurewicz.SimplyConnected.triangleClassOperator_boundary {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) (b : FirstHurewicz.Chains X 3) :
    triangleClassOperator x (((FirstHurewicz.singularComplex X).d 3 2).hom b) = 0 := by
  have h : (triangleClassOperator x).comp ((FirstHurewicz.singularComplex X).d 3 2).hom = 0 := by
    apply FirstHurewicz.chainMap_ext X 3
    intro smp
    simp only [LinearMap.comp_apply, FirstHurewicz.boundary_simplex, map_sum, map_zsmul,
      triangleClassOperator_simplex, LinearMap.zero_apply]
    exact normalizedTriangle_boundary_relation x smp
  exact LinearMap.congr_fun h b

private def
    SecondHurewicz.SimplyConnected.normalizedTriangleCycleOperator {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) :
    FirstHurewicz.Chains X 2 →ₗ[ℤ]
      SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 2 :=
  FirstHurewicz.chainLift X 2 fun smp => basedTriangleCycle (normalizedTriangle x smp)

@[simp]
private theorem SecondHurewicz.SimplyConnected.normalizedTriangleCycleOperator_simplex {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    (smp : FirstHurewicz.SingularSimplex X 2) :
    normalizedTriangleCycleOperator x (FirstHurewicz.simplexChain X 2 smp) =
      basedTriangleCycle (normalizedTriangle x smp) :=
  FirstHurewicz.chainLift_simplex X 2 _ smp

private theorem SecondHurewicz.SimplyConnected.normalizedTriangleCycleOperator_val {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) (c : FirstHurewicz.Chains X 2) :
    (normalizedTriangleCycleOperator x c).val =
      FirstHurewicz.chainLift X 2
        (fun smp =>
          FirstHurewicz.simplexChain X 2 (normalizedTriangle x smp).val -
            FirstHurewicz.simplexChain X 2 (ContinuousMap.const (FirstHurewicz.Simplex 2) x))
        c := by
  have h :
    (SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 2).subtype.comp
        (normalizedTriangleCycleOperator x) =
      FirstHurewicz.chainLift X 2
        (fun smp =>
          FirstHurewicz.simplexChain X 2 (normalizedTriangle x smp).val -
            FirstHurewicz.simplexChain X 2 (ContinuousMap.const (FirstHurewicz.Simplex 2) x)) := by
    apply FirstHurewicz.chainMap_ext X 2
    intro smp
    simp only [LinearMap.comp_apply, normalizedTriangleCycleOperator_simplex,
      Submodule.subtype_apply, basedTriangleCycle_val, FirstHurewicz.chainLift_simplex]
  exact LinearMap.congr_fun h c

private theorem SecondHurewicz.SimplyConnected.normalizedTriangleCycleOperator_twoCycle {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 2) :
    normalizedTriangleCycleOperator x c.val = normalizedTwoCycle x c := by
  apply Subtype.ext
  rw [normalizedTriangleCycleOperator_val, chainLift_sub_constant_twoCycle,
    normalizedTwoCycle_val]
  rfl

private theorem SecondHurewicz.SimplyConnected.hurewiczMap_comp_triangleClassOperator {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) :
    (SecondHurewicz.hurewiczMap x).comp (triangleClassOperator x) =
      (SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 2).comp
        (normalizedTriangleCycleOperator x) := by
  apply FirstHurewicz.chainMap_ext X 2
  intro smp
  simp only [LinearMap.comp_apply, triangleClassOperator_simplex,
    normalizedTriangleCycleOperator_simplex]
  exact hurewicz_basedTriangleClass (normalizedTriangle x smp)

private theorem SecondHurewicz.SimplyConnected.hurewiczMap_triangleClassOperator_twoCycle {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 2) :
    SecondHurewicz.hurewiczMap x (triangleClassOperator x c.val) =
      SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 2 c := by
  have h := LinearMap.congr_fun (hurewiczMap_comp_triangleClassOperator x) c.val
  change
    SecondHurewicz.hurewiczMap x (triangleClassOperator x c.val) =
      SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 2
        (normalizedTriangleCycleOperator x c.val) at h
  rw [normalizedTriangleCycleOperator_twoCycle] at h
  exact h.trans (normalizedTwoCycle_class x c)

private def SecondHurewicz.SimplyConnected.hurewiczInverse {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) :
    SingularMayerVietoris.SingularHomology X 2 →ₗ[ℤ] Additive (π_ 2 X x) :=
  secondHomologyDesc (triangleClassOperator x) (triangleClassOperator_boundary x)

@[simp]
private theorem
    SecondHurewicz.SimplyConnected.hurewiczInverse_cycleClass {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 2) :
    hurewiczInverse x
        (SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 2 c) =
      triangleClassOperator x c.val :=
  secondHomologyDesc_cycleClass _ _ c

private theorem SecondHurewicz.SimplyConnected.hurewiczMap_comp_hurewiczInverse {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) :
    (SecondHurewicz.hurewiczMap x).comp (hurewiczInverse x) = LinearMap.id :=
  comp_secondHomologyDesc_eq_id (triangleClassOperator x) (triangleClassOperator_boundary x)
    (SecondHurewicz.hurewiczMap x) (hurewiczMap_triangleClassOperator_twoCycle x)

@[simp]
private theorem
    SecondHurewicz.SimplyConnected.hurewiczMap_hurewiczInverse {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (c : SingularMayerVietoris.SingularHomology X 2) :
    SecondHurewicz.hurewiczMap x (hurewiczInverse x c) = c :=
  LinearMap.congr_fun (hurewiczMap_comp_hurewiczInverse x) c

private theorem SecondHurewicz.SimplyConnected.lowerSquareTriangle_verticesBased {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x) :
    VerticesBased x 2 (p.val.comp lowerSquareTriangle) := by
  intro i
  change p (lowerSquareTriangle (stdSimplex.vertex (S := ℝ) i)) = x
  apply GenLoop.boundary p
  refine ⟨1, ?_⟩
  by_cases hi : i = 2
  · right
    apply Subtype.ext
    change (lowerSquareTriangle (stdSimplex.vertex (S := ℝ) i) 1 : ℝ) = 1
    simp [hi, stdSimplex.vertex]
  · left
    apply Subtype.ext
    change (lowerSquareTriangle (stdSimplex.vertex (S := ℝ) i) 1 : ℝ) = 0
    simp [hi, stdSimplex.vertex]

private theorem SecondHurewicz.SimplyConnected.upperSquareTriangle_verticesBased {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x) :
    VerticesBased x 2 (p.val.comp upperSquareTriangle) := by
  intro i
  change p (upperSquareTriangle (stdSimplex.vertex (S := ℝ) i)) = x
  apply GenLoop.boundary p
  refine ⟨0, ?_⟩
  by_cases hi : i = 2
  · right
    apply Subtype.ext
    change (upperSquareTriangle (stdSimplex.vertex (S := ℝ) i) 0 : ℝ) = 1
    simp [hi, stdSimplex.vertex]
  · left
    apply Subtype.ext
    change (upperSquareTriangle (stdSimplex.vertex (S := ℝ) i) 0 : ℝ) = 0
    simp [hi, stdSimplex.vertex]

private theorem
    SecondHurewicz.SimplyConnected.squareTriangles_diagonal {X : Type} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) :
    (p.val.comp lowerSquareTriangle).comp (FirstHurewicz.simplexFace 1 1) =
      (p.val.comp upperSquareTriangle).comp (FirstHurewicz.simplexFace 1 1) := by
  apply ContinuousMap.ext
  intro s
  change
    p.val (lowerSquareTriangle (FirstHurewicz.simplexFace 1 1 s)) =
      p.val (upperSquareTriangle (FirstHurewicz.simplexFace 1 1 s))
  apply congrArg p.val
  funext i
  apply Subtype.ext
  fin_cases i
  · change
      (lowerSquareTriangle (FirstHurewicz.simplexFace 1 1 s) 0 : ℝ) =
        (upperSquareTriangle (FirstHurewicz.simplexFace 1 1 s) 0 : ℝ)
    rw [lowerSquareTriangle_zero, upperSquareTriangle_zero, FirstHurewicz.simplexFace_apply_self,
      zero_add]
  · change
      (lowerSquareTriangle (FirstHurewicz.simplexFace 1 1 s) 1 : ℝ) =
        (upperSquareTriangle (FirstHurewicz.simplexFace 1 1 s) 1 : ℝ)
    rw [lowerSquareTriangle_one, upperSquareTriangle_one, FirstHurewicz.simplexFace_apply_self,
      zero_add]

private theorem SecondHurewicz.SimplyConnected.lowerSquareTriangle_outerFace {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x) (i : Fin 3) (hi : i ≠ 1) :
    (p.val.comp lowerSquareTriangle).comp (FirstHurewicz.simplexFace 1 i) =
      ContinuousMap.const (FirstHurewicz.Simplex 1) x := by
  fin_cases i
  · apply ContinuousMap.ext
    intro s
    change p (lowerSquareTriangle (FirstHurewicz.simplexFace 1 0 s)) = x
    apply GenLoop.boundary p
    refine ⟨0, Or.inr ?_⟩
    apply Subtype.ext
    change (lowerSquareTriangle (FirstHurewicz.simplexFace 1 0 s) 0 : ℝ) = 1
    rw [lowerSquareTriangle_zero]
    have h1 : FirstHurewicz.simplexFace 1 0 s 1 = s 0 :=
      FirstHurewicz.simplexFace_apply_succAbove 1 0 s 0
    have h2 : FirstHurewicz.simplexFace 1 0 s 2 = s 1 :=
      FirstHurewicz.simplexFace_apply_succAbove 1 0 s 1
    rw [h1, h2]
    exact stdSimplex.add_eq_one s
  · exact (hi rfl).elim
  · apply ContinuousMap.ext
    intro s
    change p (lowerSquareTriangle (FirstHurewicz.simplexFace 1 2 s)) = x
    apply GenLoop.boundary p
    refine ⟨1, Or.inl ?_⟩
    apply Subtype.ext
    change (lowerSquareTriangle (FirstHurewicz.simplexFace 1 2 s) 1 : ℝ) = 0
    rw [lowerSquareTriangle_one, FirstHurewicz.simplexFace_apply_self]

private theorem SecondHurewicz.SimplyConnected.upperSquareTriangle_outerFace {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x) (i : Fin 3) (hi : i ≠ 1) :
    (p.val.comp upperSquareTriangle).comp (FirstHurewicz.simplexFace 1 i) =
      ContinuousMap.const (FirstHurewicz.Simplex 1) x := by
  fin_cases i
  · apply ContinuousMap.ext
    intro s
    change p (upperSquareTriangle (FirstHurewicz.simplexFace 1 0 s)) = x
    apply GenLoop.boundary p
    refine ⟨1, Or.inr ?_⟩
    apply Subtype.ext
    change (upperSquareTriangle (FirstHurewicz.simplexFace 1 0 s) 1 : ℝ) = 1
    rw [upperSquareTriangle_one]
    have h1 : FirstHurewicz.simplexFace 1 0 s 1 = s 0 :=
      FirstHurewicz.simplexFace_apply_succAbove 1 0 s 0
    have h2 : FirstHurewicz.simplexFace 1 0 s 2 = s 1 :=
      FirstHurewicz.simplexFace_apply_succAbove 1 0 s 1
    rw [h1, h2]
    exact stdSimplex.add_eq_one s
  · exact (hi rfl).elim
  · apply ContinuousMap.ext
    intro s
    change p (upperSquareTriangle (FirstHurewicz.simplexFace 1 2 s)) = x
    apply GenLoop.boundary p
    refine ⟨0, Or.inl ?_⟩
    apply Subtype.ext
    change (upperSquareTriangle (FirstHurewicz.simplexFace 1 2 s) 0 : ℝ) = 0
    rw [upperSquareTriangle_zero, FirstHurewicz.simplexFace_apply_self]

private theorem
    SecondHurewicz.SimplyConnected.lowerSquareTriangle_quotient (t : Fin 2 → (unitInterval))
    (h : (t 1 : ℝ) ≤ t 0) : lowerSquareTriangle (triangleQuotient (t 0, t 1)) = t := by
  funext i
  apply Subtype.ext
  fin_cases i
  · change (lowerSquareTriangle (triangleQuotient (t 0, t 1)) 0 : ℝ) = (t 0 : ℝ)
    rw [lowerSquareTriangle_zero, triangleQuotient_one, triangleQuotient_two]
    ring
  · change (lowerSquareTriangle (triangleQuotient (t 0, t 1)) 1 : ℝ) = (t 1 : ℝ)
    rw [lowerSquareTriangle_one, triangleQuotient_two, min_eq_right h]

private theorem
    SecondHurewicz.SimplyConnected.upperSquareTriangle_quotient (t : Fin 2 → (unitInterval))
    (h : (t 0 : ℝ) ≤ t 1) : upperSquareTriangle (triangleQuotient (t 1, t 0)) = t := by
  funext i
  apply Subtype.ext
  fin_cases i
  · change (upperSquareTriangle (triangleQuotient (t 1, t 0)) 0 : ℝ) = (t 0 : ℝ)
    rw [upperSquareTriangle_zero, triangleQuotient_two, min_eq_right h]
  · change (upperSquareTriangle (triangleQuotient (t 1, t 0)) 1 : ℝ) = (t 1 : ℝ)
    rw [upperSquareTriangle_one, triangleQuotient_one, triangleQuotient_two]
    ring

private theorem SecondHurewicz.SimplyConnected.triangleQuotient_perimeter_of_le
    (z : (unitInterval) × (unitInterval)) (hper : z.1 = 0 ∨ z.1 = 1 ∨ z.2 = 0 ∨ z.2 = 1)
    (hle : (z.2 : ℝ) ≤ z.1) : triangleQuotient z 0 = 0 ∨ triangleQuotient z 2 = 0 := by
  rcases hper with h | h | h | h
  · right
    rw [triangleQuotient_two, h]
    exact min_eq_left z.2.property.1
  · left
    rw [triangleQuotient_zero, h]
    norm_num
  · right
    rw [triangleQuotient_two, h]
    exact min_eq_right z.1.property.1
  · have hu : z.1 = 1 := Subtype.ext (le_antisymm z.1.property.2 (by simpa only [h] using hle))
    left
    rw [triangleQuotient_zero, hu]
    norm_num

private theorem
    SecondHurewicz.SimplyConnected.cubeBoundary_productBoundary (t : Fin 2 → (unitInterval))
    (ht : t ∈ Cube.boundary (Fin 2)) : t 0 = 0 ∨ t 0 = 1 ∨ t 1 = 0 ∨ t 1 = 1 := by
  rcases ht with ⟨i, hi | hi⟩
  · fin_cases i
    · exact Or.inl hi
    · exact Or.inr (Or.inr (Or.inl hi))
  · fin_cases i
    · exact Or.inr (Or.inl hi)
    · exact Or.inr (Or.inr (Or.inr hi))

private def SecondHurewicz.SimplyConnected.gluedTriangleHomotopyMap {X : Type} [TopologicalSpace X]
    (L U : C((unitInterval) × FirstHurewicz.Simplex 2, X))
    (hdiag : ∀ r s, s 1 = 0 → L (r, s) = U (r, s)) :
    C((unitInterval) × (Fin 2 → (unitInterval)), X)
    where
  toFun
    z :=
    if (z.2 1 : ℝ) ≤ z.2 0 then L (z.1, triangleQuotient (z.2 0, z.2 1))
    else U (z.1, triangleQuotient (z.2 1, z.2 0))
  continuous_toFun := by
    apply Continuous.if_le (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    intro z h
    have he : z.2 1 = z.2 0 := Subtype.ext h
    have hq : triangleQuotient (z.2 0, z.2 1) 1 = 0 := by
      simp only [triangleQuotient_one, he, min_self, sub_self]
    simpa only [he] using hdiag z.1 (triangleQuotient (z.2 0, z.2 1)) hq

private theorem SecondHurewicz.SimplyConnected.gluedTriangleHomotopyMap_boundary {X : Type}
    [TopologicalSpace X] (L U : C((unitInterval) × FirstHurewicz.Simplex 2, X))
    (hdiag : ∀ r s, s 1 = 0 → L (r, s) = U (r, s)) (x : X)
    (hL : ∀ r s, s 0 = 0 ∨ s 2 = 0 → L (r, s) = x) (hU : ∀ r s, s 0 = 0 ∨ s 2 = 0 → U (r, s) = x)
    (r : (unitInterval)) (t : Fin 2 → (unitInterval)) (ht : t ∈ Cube.boundary (Fin 2)) :
    gluedTriangleHomotopyMap L U hdiag (r, t) = x := by
  have hp := cubeBoundary_productBoundary t ht
  change (if (t 1 : ℝ) ≤ t 0 then _ else _) = x
  split_ifs with h
  · exact hL r _ (triangleQuotient_perimeter_of_le (t 0, t 1) hp h)
  · have hp' : t 1 = 0 ∨ t 1 = 1 ∨ t 0 = 0 ∨ t 0 = 1 := by
      rcases hp with hp | hp | hp | hp
      · exact Or.inr (Or.inr (Or.inl hp))
      · exact Or.inr (Or.inr (Or.inr hp))
      · exact Or.inl hp
      · exact Or.inr (Or.inl hp)
    exact hU r _ (triangleQuotient_perimeter_of_le (t 1, t 0) hp' (le_of_not_ge h))

private def
    SecondHurewicz.SimplyConnected.gluedTriangleHomotopy {X : Type} [TopologicalSpace X] {x : X}
    {p q : GenLoop (Fin 2) X x}
    (L : (p.val.comp lowerSquareTriangle).Homotopy (q.val.comp lowerSquareTriangle))
    (U : (p.val.comp upperSquareTriangle).Homotopy (q.val.comp upperSquareTriangle))
    (hdiag : ∀ r s, s 1 = 0 → L (r, s) = U (r, s)) (hL : ∀ r s, s 0 = 0 ∨ s 2 = 0 → L (r, s) = x)
    (hU : ∀ r s, s 0 = 0 ∨ s 2 = 0 → U (r, s) = x) :
    p.val.HomotopyRel q.val (Cube.boundary (Fin 2))
    where
  toContinuousMap := gluedTriangleHomotopyMap L.toContinuousMap U.toContinuousMap hdiag
  map_zero_left
    t := by
    change (if (t 1 : ℝ) ≤ t 0 then _ else _) = p.val t
    split_ifs with h
    · change L (0, triangleQuotient (t 0, t 1)) = p.val t
      rw [L.apply_zero]
      change p.val (lowerSquareTriangle (triangleQuotient (t 0, t 1))) = p.val t
      rw [lowerSquareTriangle_quotient t h]
    · change U (0, triangleQuotient (t 1, t 0)) = p.val t
      rw [U.apply_zero]
      change p.val (upperSquareTriangle (triangleQuotient (t 1, t 0))) = p.val t
      rw [upperSquareTriangle_quotient t (le_of_not_ge h)]
  map_one_left
    t := by
    change (if (t 1 : ℝ) ≤ t 0 then _ else _) = q.val t
    split_ifs with h
    · change L (1, triangleQuotient (t 0, t 1)) = q.val t
      rw [L.apply_one]
      change q.val (lowerSquareTriangle (triangleQuotient (t 0, t 1))) = q.val t
      rw [lowerSquareTriangle_quotient t h]
    · change U (1, triangleQuotient (t 1, t 0)) = q.val t
      rw [U.apply_one]
      change q.val (upperSquareTriangle (triangleQuotient (t 1, t 0))) = q.val t
      rw [upperSquareTriangle_quotient t (le_of_not_ge h)]
  prop' r t
    ht :=
    (gluedTriangleHomotopyMap_boundary L.toContinuousMap U.toContinuousMap hdiag x hL hU r t
          ht).trans
      (GenLoop.boundary p t ht).symm

private theorem SecondHurewicz.SimplyConnected.basedTriangles_diagonal_mo1973_6743 {X : Type}
    [TopologicalSpace X] {x : X} (τ υ : BasedTriangle x) (s : FirstHurewicz.Simplex 2)
    (hs : s 1 = 0) : τ.val s = υ.val s :=
  (τ.property s ⟨1, hs⟩).trans (υ.property s ⟨1, hs⟩).symm

private def
    SecondHurewicz.SimplyConnected.basedTrianglesLoop {X : Type} [TopologicalSpace X] {x : X}
    (τ υ : BasedTriangle x) : GenLoop (Fin 2) X x :=
  ⟨(gluedTriangleHomotopyMap (τ.val.comp ContinuousMap.snd) (υ.val.comp ContinuousMap.snd)
          (fun _ => basedTriangles_diagonal_mo1973_6743 τ υ)).comp
      ⟨fun t => ((0 : (unitInterval)), t), by fun_prop⟩,
    by
    intro t ht
    exact
      gluedTriangleHomotopyMap_boundary _ _ (fun _ => basedTriangles_diagonal_mo1973_6743 τ υ) x
        (fun _ s hs => τ.property s (hs.elim (fun h => ⟨0, h⟩) (fun h => ⟨2, h⟩)))
        (fun _ s hs => υ.property s (hs.elim (fun h => ⟨0, h⟩) (fun h => ⟨2, h⟩))) 0 t ht⟩

@[simp]
private theorem
    SecondHurewicz.SimplyConnected.basedTrianglesLoop_apply {X : Type} [TopologicalSpace X]
    {x : X} (τ υ : BasedTriangle x) (t : Fin 2 → (unitInterval)) :
    basedTrianglesLoop τ υ t =
      if (t 1 : ℝ) ≤ t 0 then τ.val (triangleQuotient (t 0, t 1))
      else υ.val (triangleQuotient (t 1, t 0)) :=
  rfl

private theorem
    SecondHurewicz.SimplyConnected.basedTrianglesLoop_diagonal {X : Type} [TopologicalSpace X]
    {x : X} (τ υ : BasedTriangle x) (u : (unitInterval)) :
    basedTrianglesLoop τ υ (fun _ => u) = x := by
  rw [basedTrianglesLoop_apply, ite_eq_left le_rfl]
  apply τ.property
  exact ⟨1, by simp only [triangleQuotient_one, min_self, sub_self]⟩

private theorem
    SecondHurewicz.SimplyConnected.basedTrianglesLoop_lower {X : Type} [TopologicalSpace X]
    {x : X} (τ υ : BasedTriangle x) :
    (basedTrianglesLoop τ υ).val.comp lowerSquareTriangle = τ.val := by
  apply ContinuousMap.ext
  intro s
  change basedTrianglesLoop τ υ (lowerSquareTriangle s) = τ.val s
  rw [basedTrianglesLoop_apply]
  have hle : (lowerSquareTriangle s 1 : ℝ) ≤ lowerSquareTriangle s 0 := by
    rw [lowerSquareTriangle_zero, lowerSquareTriangle_one]
    exact le_add_of_nonneg_left (stdSimplex.zero_le s 1)
  rw [ite_eq_left hle]
  change
    τ.val (triangleQuotient ((lowerProductTriangle s).1, (lowerProductTriangle s).2)) = τ.val s
  exact congrArg τ.val (ContinuousMap.congr_fun triangleQuotient_lowerProductTriangle s)

private theorem SecondHurewicz.SimplyConnected.triangleQuotient_swapped_upper_mo1973_6748
    (s : FirstHurewicz.Simplex 2) :
    triangleQuotient (upperSquareTriangle s 1, upperSquareTriangle s 0) = s := by
  have hpair : (upperSquareTriangle s 1, upperSquareTriangle s 0) = lowerProductTriangle s := by
    apply Prod.ext <;> apply Subtype.ext
    · rw [upperSquareTriangle_one, lowerProductTriangle_fst]
    · rw [upperSquareTriangle_zero, lowerProductTriangle_snd]
  rw [hpair]
  exact ContinuousMap.congr_fun triangleQuotient_lowerProductTriangle s

private theorem
    SecondHurewicz.SimplyConnected.basedTrianglesLoop_upper {X : Type} [TopologicalSpace X]
    {x : X} (τ υ : BasedTriangle x) :
    (basedTrianglesLoop τ υ).val.comp upperSquareTriangle = υ.val := by
  apply ContinuousMap.ext
  intro s
  change basedTrianglesLoop τ υ (upperSquareTriangle s) = υ.val s
  rw [basedTrianglesLoop_apply]
  split_ifs with h
  · have hs : s 1 = 0 := by
      rw [upperSquareTriangle_zero, upperSquareTriangle_one] at h
      exact le_antisymm (by linarith) (stdSimplex.zero_le s 1)
    have he : upperSquareTriangle s 0 = upperSquareTriangle s 1 := by
      apply Subtype.ext
      rw [upperSquareTriangle_zero, upperSquareTriangle_one, hs, zero_add]
    have hq : triangleQuotient (upperSquareTriangle s 0, upperSquareTriangle s 1) = s := by
      simpa only [he] using triangleQuotient_swapped_upper_mo1973_6748 s
    rw [hq]
    exact basedTriangles_diagonal_mo1973_6743 τ υ s hs
  · rw [triangleQuotient_swapped_upper_mo1973_6748]

private def
    SecondHurewicz.SimplyConnected.basedTrianglesHomotopy {X : Type} [TopologicalSpace X] {x : X}
    {p : GenLoop (Fin 2) X x} (τ υ : BasedTriangle x)
    (L : (p.val.comp lowerSquareTriangle).Homotopy τ.val)
    (U : (p.val.comp upperSquareTriangle).Homotopy υ.val)
    (hdiag : ∀ r s, s 1 = 0 → L (r, s) = U (r, s)) (hL : ∀ r s, s 0 = 0 ∨ s 2 = 0 → L (r, s) = x)
    (hU : ∀ r s, s 0 = 0 ∨ s 2 = 0 → U (r, s) = x) :
    p.val.HomotopyRel (basedTrianglesLoop τ υ).val (Cube.boundary (Fin 2)) :=
  gluedTriangleHomotopy (L.cast rfl (basedTrianglesLoop_lower τ υ).symm)
    (U.cast rfl (basedTrianglesLoop_upper τ υ).symm) hdiag hL hU

private theorem SecondHurewicz.SimplyConnected.triangleProperty_of_face
    {P : FirstHurewicz.Simplex 2 → Prop} (i : Fin 3)
    (h : ∀ u, P (FirstHurewicz.simplexFace 1 i u)) (s : FirstHurewicz.Simplex 2) (hs : s i = 0) :
    P s := by simpa only [simplexFace_inverse] using h (simplexFaceInverse 1 i ⟨s, hs⟩)

private def
    SecondHurewicz.SimplyConnected.basedTrianglesHomotopy_of_faces {X : Type} [TopologicalSpace X]
    {x : X} {p : GenLoop (Fin 2) X x} (τ υ : BasedTriangle x)
    (L : (p.val.comp lowerSquareTriangle).Homotopy τ.val)
    (U : (p.val.comp upperSquareTriangle).Homotopy υ.val)
    (hdiag :
      ∀ r s, L (r, FirstHurewicz.simplexFace 1 1 s) = U (r, FirstHurewicz.simplexFace 1 1 s))
    (hL : ∀ r (i : Fin 3), i ≠ 1 → ∀ s, L (r, FirstHurewicz.simplexFace 1 i s) = x)
    (hU : ∀ r (i : Fin 3), i ≠ 1 → ∀ s, U (r, FirstHurewicz.simplexFace 1 i s) = x) :
    p.val.HomotopyRel (basedTrianglesLoop τ υ).val (Cube.boundary (Fin 2)) :=
  basedTrianglesHomotopy τ υ L U
    (fun r s hs => triangleProperty_of_face (P := fun s => L (r, s) = U (r, s)) 1 (hdiag r) s hs)
    (fun r s hs =>
      hs.elim (triangleProperty_of_face (P := fun s => L (r, s) = x) 0 (hL r 0 (by decide)) s)
        (triangleProperty_of_face (P := fun s => L (r, s) = x) 2 (hL r 2 (by decide)) s))
    (fun r s hs =>
      hs.elim (triangleProperty_of_face (P := fun s => U (r, s) = x) 0 (hU r 0 (by decide)) s)
        (triangleProperty_of_face (P := fun s => U (r, s) = x) 2 (hU r 2 (by decide)) s))

private def
    SecondHurewicz.SimplyConnected.squareNormalizedLowerTriangle {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] {x : X} (p : GenLoop (Fin 2) X x) : BasedTriangle x :=
  edgeStraightenedTriangle x (p.val.comp lowerSquareTriangle)
    (lowerSquareTriangle_verticesBased p)

private def
    SecondHurewicz.SimplyConnected.squareNormalizedUpperTriangle {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] {x : X} (p : GenLoop (Fin 2) X x) : BasedTriangle x :=
  edgeStraightenedTriangle x (p.val.comp upperSquareTriangle)
    (upperSquareTriangle_verticesBased p)

private def SecondHurewicz.SimplyConnected.squareNormalizationTriangleHomotopy {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] {x : X} (smp : C(FirstHurewicz.Simplex 2, X))
    (h : VerticesBased x 2 smp) : smp.Homotopy (edgeStraightenedTriangle x smp h).val
    where
  toContinuousMap := triangleEdgeStraighteningHomotopy x smp
  map_zero_left := triangleEdgeStraighteningHomotopy_zero x smp
  map_one_left _ := rfl

private def SecondHurewicz.SimplyConnected.squareLowerNormalizationHomotopy {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] {x : X} (p : GenLoop (Fin 2) X x) :
    (p.val.comp lowerSquareTriangle).Homotopy (squareNormalizedLowerTriangle p).val :=
  squareNormalizationTriangleHomotopy _ (lowerSquareTriangle_verticesBased p)

private def SecondHurewicz.SimplyConnected.squareUpperNormalizationHomotopy {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] {x : X} (p : GenLoop (Fin 2) X x) :
    (p.val.comp upperSquareTriangle).Homotopy (squareNormalizedUpperTriangle p).val :=
  squareNormalizationTriangleHomotopy _ (upperSquareTriangle_verticesBased p)

private theorem SecondHurewicz.SimplyConnected.squareNormalization_edge_face {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] {x : X} (smp : C(FirstHurewicz.Simplex 2, X))
    (i : Fin 3) (r : (unitInterval)) (s : FirstHurewicz.Simplex 1) :
    triangleEdgeStraighteningHomotopy x smp (r, FirstHurewicz.simplexFace 1 i s) =
      edgeStraighteningHomotopy x (smp.comp (FirstHurewicz.simplexFace 1 i)) (r, s) :=
  DFunLike.congr_fun (triangleEdgeStraighteningHomotopy_face x smp i) (r, s)

private theorem SecondHurewicz.SimplyConnected.squareNormalization_diagonal {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (r : (unitInterval)) (s : FirstHurewicz.Simplex 1) :
    squareLowerNormalizationHomotopy p (r, FirstHurewicz.simplexFace 1 1 s) =
      squareUpperNormalizationHomotopy p (r, FirstHurewicz.simplexFace 1 1 s) := by
  change
    triangleEdgeStraighteningHomotopy x (p.val.comp lowerSquareTriangle)
        (r, FirstHurewicz.simplexFace 1 1 s) =
      triangleEdgeStraighteningHomotopy x (p.val.comp upperSquareTriangle)
        (r, FirstHurewicz.simplexFace 1 1 s)
  rw [squareNormalization_edge_face, squareNormalization_edge_face, squareTriangles_diagonal]

private theorem SecondHurewicz.SimplyConnected.squareLowerNormalization_outerFace {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (r : (unitInterval)) (i : Fin 3) (hi : i ≠ 1) (s : FirstHurewicz.Simplex 1) :
    squareLowerNormalizationHomotopy p (r, FirstHurewicz.simplexFace 1 i s) = x := by
  change
    triangleEdgeStraighteningHomotopy x (p.val.comp lowerSquareTriangle)
        (r, FirstHurewicz.simplexFace 1 i s) =
      x
  rw [squareNormalization_edge_face, lowerSquareTriangle_outerFace p i hi,
    edgeStraighteningHomotopy_const]
  rfl

private theorem SecondHurewicz.SimplyConnected.squareUpperNormalization_outerFace {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (r : (unitInterval)) (i : Fin 3) (hi : i ≠ 1) (s : FirstHurewicz.Simplex 1) :
    squareUpperNormalizationHomotopy p (r, FirstHurewicz.simplexFace 1 i s) = x := by
  change
    triangleEdgeStraighteningHomotopy x (p.val.comp upperSquareTriangle)
        (r, FirstHurewicz.simplexFace 1 i s) =
      x
  rw [squareNormalization_edge_face, upperSquareTriangle_outerFace p i hi,
    edgeStraighteningHomotopy_const]
  rfl

private def
    SecondHurewicz.SimplyConnected.squareNormalizationHomotopy {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] {x : X} (p : GenLoop (Fin 2) X x) :
    p.val.HomotopyRel
      (basedTrianglesLoop (squareNormalizedLowerTriangle p) (squareNormalizedUpperTriangle p)).val
      (Cube.boundary (Fin 2)) :=
  basedTrianglesHomotopy_of_faces (squareNormalizedLowerTriangle p)
    (squareNormalizedUpperTriangle p) (squareLowerNormalizationHomotopy p)
    (squareUpperNormalizationHomotopy p) (squareNormalization_diagonal p)
    (squareLowerNormalization_outerFace p) (squareUpperNormalization_outerFace p)

private theorem SecondHurewicz.SimplyConnected.squareNormalization_homotopic {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] {x : X} (p : GenLoop (Fin 2) X x) :
    GenLoop.Homotopic p
      (basedTrianglesLoop (squareNormalizedLowerTriangle p) (squareNormalizedUpperTriangle p)) :=
  ⟨squareNormalizationHomotopy p⟩

private def SecondHurewicz.SimplyConnected.subdivisionUpperPositiveSquareTriangle :
    C(FirstHurewicz.Simplex 2, Fin 2 → (unitInterval)) :=
  SecondHurewicz.squareCoordinates.comp (squareAffineTriangle ![(0, 0), (1, 1), (0, 1)])

@[simp]
private theorem SecondHurewicz.SimplyConnected.subdivisionUpperPositiveSquareTriangle_zero
    (s : FirstHurewicz.Simplex 2) : (subdivisionUpperPositiveSquareTriangle s 0 : ℝ) = s 1 := by
  simp [subdivisionUpperPositiveSquareTriangle, squareAffineTriangle_fst_coe,
    SingularMayerVietoris.stdVertices, stdSimplex.vertex, Fin.sum_univ_succ, Pi.single_apply]

@[simp]
private theorem SecondHurewicz.SimplyConnected.subdivisionUpperPositiveSquareTriangle_one
    (s : FirstHurewicz.Simplex 2) :
    (subdivisionUpperPositiveSquareTriangle s 1 : ℝ) = s 1 + s 2 := by
  simp [subdivisionUpperPositiveSquareTriangle, squareAffineTriangle_snd_coe,
    SingularMayerVietoris.stdVertices, stdSimplex.vertex, Fin.sum_univ_succ, Pi.single_apply]

private theorem SecondHurewicz.SimplyConnected.subdivisionTriangle_coordinate_sum
    (s : FirstHurewicz.Simplex 2) : s 0 + s 1 + s 2 = 1 := by
  have hsum := stdSimplex.sum_eq_one s
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hsum
  change s 0 + (s 1 + s 2) = 1 at hsum
  linarith

private theorem SecondHurewicz.SimplyConnected.subdivisionLowerSquareTriangle_based {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) (s : FirstHurewicz.Simplex 2)
    (hs : s ∈ triangleBoundary) : p (lowerSquareTriangle s) = x := by
  rcases hs with ⟨i, hi⟩
  fin_cases i
  · change s 0 = 0 at hi
    apply p.property
    refine ⟨0, Or.inr ?_⟩
    apply Subtype.ext
    change (lowerSquareTriangle s 0 : ℝ) = 1
    rw [lowerSquareTriangle_zero]
    linarith [subdivisionTriangle_coordinate_sum s]
  · change s 1 = 0 at hi
    apply subdivisionOnDiagonal p hd
    apply Subtype.ext
    simp [hi]
  · change s 2 = 0 at hi
    apply p.property
    refine ⟨1, Or.inl ?_⟩
    apply Subtype.ext
    simpa using hi

private theorem
    SecondHurewicz.SimplyConnected.subdivisionUpperNegativeSquareTriangle_based {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) (s : FirstHurewicz.Simplex 2)
    (hs : s ∈ triangleBoundary) : p (upperSquareTriangle s) = x := by
  rcases hs with ⟨i, hi⟩
  fin_cases i
  · change s 0 = 0 at hi
    apply p.property
    refine ⟨1, Or.inr ?_⟩
    apply Subtype.ext
    change (upperSquareTriangle s 1 : ℝ) = 1
    rw [upperSquareTriangle_one]
    linarith [subdivisionTriangle_coordinate_sum s]
  · change s 1 = 0 at hi
    apply subdivisionOnDiagonal p hd
    apply Subtype.ext
    simp [hi]
  · change s 2 = 0 at hi
    apply p.property
    refine ⟨0, Or.inl ?_⟩
    apply Subtype.ext
    simpa using hi

private theorem
    SecondHurewicz.SimplyConnected.subdivisionUpperPositiveSquareTriangle_based {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) (s : FirstHurewicz.Simplex 2)
    (hs : s ∈ triangleBoundary) : p (subdivisionUpperPositiveSquareTriangle s) = x := by
  rcases hs with ⟨i, hi⟩
  fin_cases i
  · change s 0 = 0 at hi
    apply p.property
    refine ⟨1, Or.inr ?_⟩
    apply Subtype.ext
    change (subdivisionUpperPositiveSquareTriangle s 1 : ℝ) = 1
    rw [subdivisionUpperPositiveSquareTriangle_one]
    linarith [subdivisionTriangle_coordinate_sum s]
  · change s 1 = 0 at hi
    apply p.property
    refine ⟨0, Or.inl ?_⟩
    apply Subtype.ext
    simpa using hi
  · change s 2 = 0 at hi
    apply subdivisionOnDiagonal p hd
    apply Subtype.ext
    simp [hi]

private def
    SecondHurewicz.SimplyConnected.subdivisionLowerBasedTriangle {X : Type} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    BasedTriangle x :=
  ⟨p.val.comp lowerSquareTriangle, subdivisionLowerSquareTriangle_based p hd⟩

private def SecondHurewicz.SimplyConnected.subdivisionUpperNegativeBasedTriangle {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) : BasedTriangle x :=
  ⟨p.val.comp upperSquareTriangle, subdivisionUpperNegativeSquareTriangle_based p hd⟩

private def SecondHurewicz.SimplyConnected.subdivisionUpperPositiveBasedTriangle {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) : BasedTriangle x :=
  ⟨p.val.comp subdivisionUpperPositiveSquareTriangle,
    subdivisionUpperPositiveSquareTriangle_based p hd⟩

private theorem SecondHurewicz.SimplyConnected.subdivisionLowerTriangleLoop_eq_basedTriangleLoop
    {X : Type} [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    subdivisionLowerTriangleLoop p hd = basedTriangleLoop (subdivisionLowerBasedTriangle p hd) := by
  apply GenLoop.ext
  intro u
  change p ![u 0, Min.min (u 0) (u 1)] = p (lowerSquareTriangle (triangleQuotient (u 0, u 1)))
  congr 1
  funext i
  fin_cases i <;> apply Subtype.ext <;> simp

private theorem SecondHurewicz.SimplyConnected.subdivisionUpperTriangleLoop_eq_basedTriangleLoop
    {X : Type} [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    subdivisionUpperTriangleLoop p hd =
      basedTriangleLoop (subdivisionUpperPositiveBasedTriangle p hd) := by
  apply GenLoop.ext
  intro u
  change
    p ![subdivisionSubMin (u 0) (u 1), u 0] =
      p (subdivisionUpperPositiveSquareTriangle (triangleQuotient (u 0, u 1)))
  congr 1
  funext i
  fin_cases i <;> apply Subtype.ext <;> simp [subdivisionSubMin]

private theorem
    SecondHurewicz.SimplyConnected.subdivisionUpperNegativeBasedTriangle_loop_apply {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) (u : Fin 2 → (unitInterval)) :
    basedTriangleLoop (subdivisionUpperNegativeBasedTriangle p hd) u =
      p ![Min.min (u 0) (u 1), u 0] := by
  change p (upperSquareTriangle (triangleQuotient (u 0, u 1))) = p ![Min.min (u 0) (u 1), u 0]
  congr 1
  funext i
  fin_cases i <;> apply Subtype.ext <;> simp

private theorem SecondHurewicz.SimplyConnected.subdivision_basedTriangleClass_sum {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    Additive.ofMul (⟦p⟧ : π_ 2 X x) =
      basedTriangleClass (subdivisionLowerBasedTriangle p hd) +
        basedTriangleClass (subdivisionUpperPositiveBasedTriangle p hd) := by
  simpa only [subdivisionLowerTriangleLoop_eq_basedTriangleLoop,
    subdivisionUpperTriangleLoop_eq_basedTriangleLoop, basedTriangleClass] using
    subdivision_additiveClass p hd

private def SecondHurewicz.SimplyConnected.subdivisionUpperNegativeMap :
    C(SubdivisionSquare, SubdivisionSquare)
    where
  toFun u := ![Min.min (u 0) (u 1), u 0]
  continuous_toFun := by fun_prop

private def SecondHurewicz.SimplyConnected.subdivisionUpperNegativeReversedMap :
    C(SubdivisionSquare, SubdivisionSquare)
    where
  toFun u := ![Min.min (u 0) ((unitInterval.symm) (u 1)), u 0]
  continuous_toFun := by fun_prop

private theorem SecondHurewicz.SimplyConnected.subdivisionUpperNegativeMap_based {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) (u : SubdivisionSquare)
    (hu : u ∈ Cube.boundary (Fin 2)) : p (subdivisionUpperNegativeMap u) = x := by
  rcases subdivisionSquare_boundary_cases u hu with h | h | h | h
  · exact p.property _ ⟨1, Or.inl (by simp [subdivisionUpperNegativeMap, h])⟩
  · exact p.property _ ⟨1, Or.inr (by simp [subdivisionUpperNegativeMap, h])⟩
  · exact p.property _ ⟨0, Or.inl (by simp [subdivisionUpperNegativeMap, h])⟩
  · exact
      subdivisionOnDiagonal p hd _
        (by
          simp [subdivisionUpperNegativeMap, h,
            min_eq_left (show u 0 ≤ (1 : (unitInterval)) from (u 0).property.2)])

private theorem SecondHurewicz.SimplyConnected.subdivisionUpperNegativeReversedMap_based {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) (u : SubdivisionSquare)
    (hu : u ∈ Cube.boundary (Fin 2)) : p (subdivisionUpperNegativeReversedMap u) = x := by
  rcases subdivisionSquare_boundary_cases u hu with h | h | h | h
  · exact p.property _ ⟨1, Or.inl (by simp [subdivisionUpperNegativeReversedMap, h])⟩
  · exact p.property _ ⟨1, Or.inr (by simp [subdivisionUpperNegativeReversedMap, h])⟩
  · exact
      subdivisionOnDiagonal p hd _
        (by
          simp [subdivisionUpperNegativeReversedMap, h,
            min_eq_left (show u 0 ≤ (1 : (unitInterval)) from (u 0).property.2)])
  · exact p.property _ ⟨0, Or.inl (by simp [subdivisionUpperNegativeReversedMap, h])⟩

private def
    SecondHurewicz.SimplyConnected.subdivisionUpperNegativeLoop {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    GenLoop (Fin 2) X x :=
  subdivisionPullbackLoop p subdivisionUpperNegativeMap (subdivisionUpperNegativeMap_based p hd)

private def SecondHurewicz.SimplyConnected.subdivisionUpperNegativeReversedLoop {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) : GenLoop (Fin 2) X x :=
  subdivisionPullbackLoop p subdivisionUpperNegativeReversedMap
    (subdivisionUpperNegativeReversedMap_based p hd)

private theorem
    SecondHurewicz.SimplyConnected.subdivisionUpperOrientation_sides (u : SubdivisionSquare)
    (hu : u ∈ Cube.boundary (Fin 2)) :
    SubdivisionSameSide (subdivisionUpperTriangleMap u) (subdivisionUpperNegativeReversedMap u) :=
  by
  rcases subdivisionSquare_boundary_cases u hu with h | h | h | h
  · exact
      .zero 1 (by simp [subdivisionUpperTriangleMap, h])
        (by simp [subdivisionUpperNegativeReversedMap, h])
  · exact
      .one 1 (by simp [subdivisionUpperTriangleMap, h])
        (by simp [subdivisionUpperNegativeReversedMap, h])
  · exact
      .diagonal (by simp [subdivisionUpperTriangleMap, h])
        (by
          simp [subdivisionUpperNegativeReversedMap, h,
            min_eq_left (show u 0 ≤ (1 : (unitInterval)) from (u 0).property.2)])
  · exact
      .zero 0 (by simp [subdivisionUpperTriangleMap, h])
        (by simp [subdivisionUpperNegativeReversedMap, h])

private def SecondHurewicz.SimplyConnected.subdivisionUpperOrientationHomotopy {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    (subdivisionUpperTriangleLoop p hd).val.HomotopyRel
      (subdivisionUpperNegativeReversedLoop p hd).val (Cube.boundary (Fin 2)) :=
  subdivisionLinearHomotopy p hd _ _ (subdivisionUpperTriangleMap_based p hd)
    (subdivisionUpperNegativeReversedMap_based p hd) subdivisionUpperOrientation_sides

private theorem
    SecondHurewicz.SimplyConnected.subdivisionUpperNegativeReversedLoop_eq_symmAt {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    subdivisionUpperNegativeReversedLoop p hd =
      GenLoop.symmAt (1 : Fin 2) (subdivisionUpperNegativeLoop p hd) := by
  apply GenLoop.ext
  intro u
  change
    p ![Min.min (u 0) ((unitInterval.symm) (u 1)), u 0] =
      subdivisionUpperNegativeLoop p hd
        (fun j => if j = 1 then (unitInterval.symm) (u 1) else u j)
  simp [subdivisionUpperNegativeLoop, subdivisionPullbackLoop, subdivisionUpperNegativeMap]

private theorem SecondHurewicz.SimplyConnected.subdivisionUpperOrientation_homotopic {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    GenLoop.Homotopic (subdivisionUpperTriangleLoop p hd)
      (GenLoop.symmAt (1 : Fin 2) (subdivisionUpperNegativeLoop p hd)) := by
  rw [← subdivisionUpperNegativeReversedLoop_eq_symmAt]
  exact ⟨subdivisionUpperOrientationHomotopy p hd⟩

private theorem SecondHurewicz.SimplyConnected.subdivisionUpperOrientation_class {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    (⟦subdivisionUpperTriangleLoop p hd⟧ : π_ 2 X x) =
      ((·⁻¹) : π_ 2 X x → π_ 2 X x) ⟦subdivisionUpperNegativeLoop p hd⟧ := by
  have h :
    (⟦subdivisionUpperTriangleLoop p hd⟧ : π_ 2 X x) =
      (⟦GenLoop.symmAt (1 : Fin 2) (subdivisionUpperNegativeLoop p hd)⟧ : π_ 2 X x) :=
    Quotient.sound (subdivisionUpperOrientation_homotopic p hd)
  exact
    h.trans
      (HomotopyGroup.inv_spec (i := (1 : Fin 2)) (p := subdivisionUpperNegativeLoop p hd)).symm

private theorem SecondHurewicz.SimplyConnected.subdivisionUpperOrientation_additiveClass {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    Additive.ofMul (⟦subdivisionUpperTriangleLoop p hd⟧ : π_ 2 X x) =
      ((-·) : Additive (π_ 2 X x) → Additive (π_ 2 X x))
        (Additive.ofMul (⟦subdivisionUpperNegativeLoop p hd⟧ : π_ 2 X x)) :=
  congrArg Additive.ofMul (subdivisionUpperOrientation_class p hd)

public
theorem SecondHurewicz.SimplyConnected.subdivision_eq_sub_of_eq_add {A : Type*} [AddGroup A]
    {a b c d : A} (h : a = b + c) (hc : c = -d) : a = b - d :=
  h.trans ((congrArg (fun z => b + z) hc).trans (sub_eq_add_neg b d).symm)

private theorem SecondHurewicz.SimplyConnected.subdivisionUpperNegativeLoop_eq_basedTriangleLoop
    {X : Type} [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    subdivisionUpperNegativeLoop p hd =
      basedTriangleLoop (subdivisionUpperNegativeBasedTriangle p hd) := by
  apply GenLoop.ext
  intro u
  exact (subdivisionUpperNegativeBasedTriangle_loop_apply p hd u).symm

private theorem SecondHurewicz.SimplyConnected.subdivisionUpperPositiveBasedTriangle_class_eq_neg
    {X : Type} [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    basedTriangleClass (subdivisionUpperPositiveBasedTriangle p hd) =
      -basedTriangleClass (subdivisionUpperNegativeBasedTriangle p hd) := by
  unfold basedTriangleClass
  rw [← subdivisionUpperTriangleLoop_eq_basedTriangleLoop, ←
    subdivisionUpperNegativeLoop_eq_basedTriangleLoop]
  exact subdivisionUpperOrientation_additiveClass p hd

private theorem SecondHurewicz.SimplyConnected.subdivision_basedTriangleClass_sub {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    Additive.ofMul (⟦p⟧ : π_ 2 X x) =
      basedTriangleClass (subdivisionLowerBasedTriangle p hd) -
        basedTriangleClass (subdivisionUpperNegativeBasedTriangle p hd) :=
  subdivision_eq_sub_of_eq_add (A := Additive (π_ 2 X x))
    (subdivision_basedTriangleClass_sum p hd)
    (subdivisionUpperPositiveBasedTriangle_class_eq_neg p hd)

private theorem
    SecondHurewicz.SimplyConnected.basedTrianglesLoop_class {X : Type} [TopologicalSpace X]
    {x : X} (τ υ : BasedTriangle x) :
    Additive.ofMul (⟦basedTrianglesLoop τ υ⟧ : π_ 2 X x) =
      basedTriangleClass τ - basedTriangleClass υ := by
  have hd : ∀ t : (unitInterval), basedTrianglesLoop τ υ ![t, t] = x := by
    intro t
    have he : (![t, t] : Fin 2 → (unitInterval)) = fun _ => t := by
      funext i
      fin_cases i <;> rfl
    rw [he, basedTrianglesLoop_diagonal]
  have hl : subdivisionLowerBasedTriangle (basedTrianglesLoop τ υ) hd = τ :=
    Subtype.ext (basedTrianglesLoop_lower τ υ)
  have hu : subdivisionUpperNegativeBasedTriangle (basedTrianglesLoop τ υ) hd = υ :=
    Subtype.ext (basedTrianglesLoop_upper τ υ)
  simpa only [hl, hu] using subdivision_basedTriangleClass_sub (basedTrianglesLoop τ υ) hd

private theorem SecondHurewicz.SimplyConnected.squareNormalization_quotient {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] {x : X} (p : GenLoop (Fin 2) X x) :
    (⟦p⟧ : π_ 2 X x) =
      ⟦basedTrianglesLoop (squareNormalizedLowerTriangle p) (squareNormalizedUpperTriangle p)⟧ :=
  Quotient.sound (squareNormalization_homotopic p)

private theorem
    SecondHurewicz.SimplyConnected.squareNormalization_class {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] {x : X} (p : GenLoop (Fin 2) X x) :
    basedTriangleClass (squareNormalizedLowerTriangle p) -
        basedTriangleClass (squareNormalizedUpperTriangle p) =
      Additive.ofMul (⟦p⟧ : π_ 2 X x) := by
  have h := congrArg Additive.ofMul (squareNormalization_quotient p)
  exact
    (basedTrianglesLoop_class (squareNormalizedLowerTriangle p)
          (squareNormalizedUpperTriangle p)).symm.trans
      h.symm

private theorem SecondHurewicz.SimplyConnected.triangleClassOperator_squareChain {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) (p : GenLoop (Fin 2) X x) :
    triangleClassOperator x (SecondHurewicz.squareChain p) = Additive.ofMul (⟦p⟧ : π_ 2 X x) := by
  rw [squareChain_two_triangles, map_sub, triangleClassOperator_simplex,
    triangleClassOperator_simplex,
    normalizedTriangle_of_verticesBased x _ (lowerSquareTriangle_verticesBased p),
    normalizedTriangle_of_verticesBased x _ (upperSquareTriangle_verticesBased p)]
  exact squareNormalization_class p

private theorem SecondHurewicz.SimplyConnected.hurewiczInverse_hurewiczMap_mk {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) (p : GenLoop (Fin 2) X x) :
    hurewiczInverse x (SecondHurewicz.hurewiczMap x (Additive.ofMul (⟦p⟧ : π_ 2 X x))) =
      Additive.ofMul (⟦p⟧ : π_ 2 X x) := by
  rw [SecondHurewicz.hurewiczMap_representative, hurewiczInverse_cycleClass]
  exact triangleClassOperator_squareChain x p

@[simp]
private theorem
    SecondHurewicz.SimplyConnected.hurewiczInverse_hurewiczMap {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (a : Additive (π_ 2 X x)) :
    hurewiczInverse x (SecondHurewicz.hurewiczMap x a) = a := by
  change
    hurewiczInverse x (SecondHurewicz.hurewiczMap x (Additive.ofMul (Additive.toMul a))) =
      Additive.ofMul (Additive.toMul a)
  refine Quotient.inductionOn (Additive.toMul a) ?_
  intro p
  exact hurewiczInverse_hurewiczMap_mk x p

private theorem SecondHurewicz.SimplyConnected.hurewiczInverse_comp_hurewiczMap {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) :
    (hurewiczInverse x).comp (SecondHurewicz.hurewiczMap x) = LinearMap.id := by
  ext a
  exact hurewiczInverse_hurewiczMap x a


private def SecondHurewicz.SimplyConnected.hurewiczPi2Equiv {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) :
    π_ 2 X x ≃* Multiplicative (SingularMayerVietoris.SingularHomology X 2)
    where
  __ := SecondHurewicz.hurewiczPi2 x
  invFun c := Additive.toMul (hurewiczInverse x (Multiplicative.toAdd c))
  left_inv a := congrArg Additive.toMul (hurewiczInverse_hurewiczMap x (Additive.ofMul a))
  right_inv
    c := congrArg Multiplicative.ofAdd (hurewiczMap_hurewiczInverse x (Multiplicative.toAdd c))

private theorem
    ThirdHurewicz.gluedBoundaryMap_constant_value {X : Type} [TopologicalSpace X] {n : ℕ}
    (f : C(FirstHurewicz.Simplex n, X))
    (g : C((unitInterval) × SecondHurewicz.SimplyConnected.SimplexBoundary n, X))
    (h₀ : ∀ s, g (0, s) = f s.val) (x : X) (hf : ∀ s, f s = x) (hg : ∀ u, g u = x)
    (u : ↥(SecondHurewicz.SimplyConnected.bottomOrSide n)) :
    SecondHurewicz.SimplyConnected.gluedBoundaryMap f g h₀ u = x := by
  rcases u.property with hb | hs
  · have hu : u = SecondHurewicz.SimplyConnected.bottomInclusion n u.val.2 := by
      apply Subtype.ext
      exact Prod.ext hb rfl
    exact
      (congrArg (SecondHurewicz.SimplyConnected.gluedBoundaryMap f g h₀) hu).trans
        ((SecondHurewicz.SimplyConnected.gluedBoundaryMap_bottomInclusion f g h₀ _).trans (hf _))
  · have hu : u = SecondHurewicz.SimplyConnected.sideInclusion n (u.val.1, ⟨u.val.2, hs⟩) := by
      apply Subtype.ext
      rfl
    exact
      (congrArg (SecondHurewicz.SimplyConnected.gluedBoundaryMap f g h₀) hu).trans
        ((SecondHurewicz.SimplyConnected.gluedBoundaryMap_sideInclusion f g h₀ _).trans (hg _))

private theorem
    ThirdHurewicz.coherentFaceBoundaryHomotopy_const {X : Type} [TopologicalSpace X] {n : ℕ}
    (H : FirstHurewicz.SingularSimplex X n → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (H' :
      FirstHurewicz.SingularSimplex X (n + 1) →
        C((unitInterval) × FirstHurewicz.Simplex (n + 1), X))
    (h : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies n H H') (x : X)
    (hc :
      H' (ContinuousMap.const (FirstHurewicz.Simplex (n + 1)) x) =
        ContinuousMap.const ((unitInterval) × FirstHurewicz.Simplex (n + 1)) x) :
    SecondHurewicz.SimplyConnected.coherentFaceBoundaryHomotopy H H' h
        (ContinuousMap.const (FirstHurewicz.Simplex (n + 2)) x) =
      ContinuousMap.const
        ((unitInterval) × SecondHurewicz.SimplyConnected.SimplexBoundary (n + 2)) x := by
  unfold SecondHurewicz.SimplyConnected.coherentFaceBoundaryHomotopy
  apply
    (SecondHurewicz.SimplyConnected.glueFaceHomotopies_unique _ _ (ContinuousMap.const _ x)
        ?_).symm
  intro i r s
  change x = H' (ContinuousMap.const (FirstHurewicz.Simplex (n + 1)) x) (r, s)
  rw [hc]
  rfl

private theorem
    ThirdHurewicz.extendCoherentSimplexHomotopy_const {X : Type} [TopologicalSpace X] {n : ℕ}
    (H : FirstHurewicz.SingularSimplex X n → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (H' :
      FirstHurewicz.SingularSimplex X (n + 1) →
        C((unitInterval) × FirstHurewicz.Simplex (n + 1), X))
    (h : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies n H H')
    (h₀ : ∀ smp s, H' smp (0, s) = smp s) (x : X)
    (hc :
      H' (ContinuousMap.const (FirstHurewicz.Simplex (n + 1)) x) =
        ContinuousMap.const ((unitInterval) × FirstHurewicz.Simplex (n + 1)) x) :
    SecondHurewicz.SimplyConnected.extendCoherentSimplexHomotopy H H' h h₀
        (ContinuousMap.const (FirstHurewicz.Simplex (n + 2)) x) =
      ContinuousMap.const ((unitInterval) × FirstHurewicz.Simplex (n + 2)) x := by
  unfold SecondHurewicz.SimplyConnected.extendCoherentSimplexHomotopy
  ext u
  change
    SecondHurewicz.SimplyConnected.gluedBoundaryMap
        (ContinuousMap.const (FirstHurewicz.Simplex (n + 2)) x)
        (SecondHurewicz.SimplyConnected.coherentFaceBoundaryHomotopy H H' h
          (ContinuousMap.const (FirstHurewicz.Simplex (n + 2)) x))
        (SecondHurewicz.SimplyConnected.coherentFaceBoundaryHomotopy_zero H H' h h₀
          (ContinuousMap.const (FirstHurewicz.Simplex (n + 2)) x))
        (SecondHurewicz.SimplyConnected.cylinderRetraction (n + 2) u) =
      x
  apply gluedBoundaryMap_constant_value _ _ _ x (fun _ => rfl)
  intro v
  exact
    congrArg
      (fun F : C((unitInterval) × SecondHurewicz.SimplyConnected.SimplexBoundary (n + 2), X) =>
        F v)
      (coherentFaceBoundaryHomotopy_const H H' h x hc)

end Mathoverflow1973

end
