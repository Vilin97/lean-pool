/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.Hurewicz.HigherHurewicz1
import all LeanPool.HopfProblem.HomologyTheory.SingularMayerVietoris
import all LeanPool.HopfProblem.HomologyTheory.FirstHurewicz1
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology4
import all LeanPool.HopfProblem.Hurewicz.SecondHurewicz
import all LeanPool.HopfProblem.Hurewicz.ThirdHurewicz
import all LeanPool.HopfProblem.Hurewicz.HigherHurewicz1

/-!
# Hopf problem: hurewicz · higher hurewicz 2

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

private theorem HigherHurewicz.CubicalBoundary.whiskerFacet_transAt_zero_apply {n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} (p q : GenLoop (Fin (n + 1)) X x)
    (u : Fin (n + 1) → (unitInterval)) :
    GenLoop.transAt 0 p q u =
      if (u 0 : ℝ) ≤ 1 / 2 then
        p (Function.update u 0 (Set.projIcc 0 1 zero_le_one (2 * (u 0 : ℝ))))
      else q (Function.update u 0 (Set.projIcc 0 1 zero_le_one (2 * (u 0 : ℝ) - 1))) :=
  rfl

private theorem HigherHurewicz.CubicalBoundary.whiskeredCell_face_last_upper {n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} (F : BasedCubicalCell (n + 2) x) :
    uncurryLoop (cubicalUpperFace (whiskeredCell F) (Fin.last n)) =
      GenLoop.transAt 0
        (HigherHurewicz.NativeSubdivision.permuteCubeLoop (cubicalLowerFace F 0)
          (finRotate (n + 1)))
        (GenLoop.transAt 0 (cubicalUpperFace F (Fin.last (n + 1)))
          (GenLoop.symmAt 0
            (HigherHurewicz.NativeSubdivision.permuteCubeLoop (cubicalUpperFace F 0)
              (finRotate (n + 1))))) := by
  apply GenLoop.ext
  intro u
  rw [whiskerFacet_last_upper_uncurry_apply, whiskerTrack_concat, whiskerFacet_transAt_zero_apply]
  by_cases h₀ : (u 0 : ℝ) ≤ 1 / 2
  · simp only [ite_eq_left h₀, whiskerFacet_rotated_face_apply, Fin.tail_update_zero,
      Function.update_self]
  · simp only [ite_eq_right h₀]
    rw [whiskerFacet_transAt_zero_apply]
    simp only [Function.update_self]
    split_ifs
    · rw [whiskerFacet_last_upper_apply]
      simp only [Fin.tail_update_zero, Function.update_self]
    · rw [whiskerFacet_reflected_rotated_face_apply]
      simp only [Fin.tail_update_zero, Function.update_self]

private theorem HigherHurewicz.CubicalBoundary.uncurryTail_update_succ {n : ℕ}
    (u : Fin (n + 1) → (unitInterval)) (i : Fin n) (t : (unitInterval)) :
    (fun j : Fin n => Function.update u i.succ t j.succ) =
      Function.update (fun j : Fin n => u j.succ) i t := by
  funext j
  simp only [Function.update_apply, Fin.succ_inj]

@[simp]
private theorem HigherHurewicz.CubicalBoundary.uncurryHead_update_succ {n : ℕ}
    (u : Fin (n + 1) → (unitInterval)) (i : Fin n) (t : (unitInterval)) :
    Function.update u i.succ t 0 = u 0 := by
  simp only [Function.update_apply, (Fin.succ_ne_zero i).symm, ite_false]

private theorem HigherHurewicz.CubicalBoundary.uncurryLoop_transAt {n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} (i : Fin n)
    (p q : GenLoop (Fin n) (GenLoop (Fin 1) X x) GenLoop.const) :
    uncurryLoop (GenLoop.transAt i p q) =
      GenLoop.transAt i.succ (uncurryLoop p) (uncurryLoop q) := by
  apply GenLoop.ext
  intro u
  change
    ((if (u i.succ : ℝ) ≤ 1 / 2 then _ else _) : GenLoop (Fin 1) X x) (fun _ => u 0) =
      if (u i.succ : ℝ) ≤ 1 / 2 then _ else _
  split_ifs <;> simp only [uncurryLoop_apply, uncurryTail_update_succ, uncurryHead_update_succ]

private theorem
    HigherHurewicz.CubicalBoundary.uncurryLoop_symmAt {n : ℕ} {X : Type*} [TopologicalSpace X]
    {x : X} (i : Fin n) (p : GenLoop (Fin n) (GenLoop (Fin 1) X x) GenLoop.const) :
    uncurryLoop (GenLoop.symmAt i p) = GenLoop.symmAt i.succ (uncurryLoop p) := by
  apply GenLoop.ext
  intro u
  change
    p (fun j => if j = i then (unitInterval.symm) (u i.succ) else u j.succ) (fun _ => u 0) =
      p (fun j => if j.succ = i.succ then (unitInterval.symm) (u i.succ) else u j.succ)
        (fun _ => if (0 : Fin (n + 1)) = i.succ then (unitInterval.symm) (u i.succ) else u 0)
  simp only [Fin.succ_inj, (Fin.succ_ne_zero i).symm, ite_false]

private theorem
    HigherHurewicz.CubicalBoundary.uncurryLoop_swap {X : Type*} [TopologicalSpace X] {x : X}
    {n : ℕ} (p : GenLoop (Fin n) (GenLoop (Fin 1) X x) GenLoop.const) (i j : Fin n) :
    uncurryLoop (HigherHurewicz.NativeSubdivision.permuteCubeLoop p (Equiv.swap i j)) =
      HigherHurewicz.NativeSubdivision.permuteCubeLoop (uncurryLoop p)
        (Equiv.swap i.succ j.succ) := by
  have hzero : Equiv.swap i.succ j.succ (0 : Fin (n + 1)) = 0 :=
    Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero i).symm (Fin.succ_ne_zero j).symm
  have hsucc (k : Fin n) : Equiv.swap i.succ j.succ k.succ = (Equiv.swap i j k).succ := by
    by_cases hki : k = i
    · subst k
      simp
    by_cases hkj : k = j
    · subst k
      simp
    have hki' : k.succ ≠ i.succ := fun h => hki (Fin.succ_inj.mp h)
    have hkj' : k.succ ≠ j.succ := fun h => hkj (Fin.succ_inj.mp h)
    rw [Equiv.swap_apply_of_ne_of_ne hki' hkj', Equiv.swap_apply_of_ne_of_ne hki hkj]
  apply GenLoop.ext
  intro u
  change
    p (fun k => u (Equiv.swap i j k).succ) (fun _ => u 0) =
      p (fun k => u (Equiv.swap i.succ j.succ k.succ)) (fun _ => u (Equiv.swap i.succ j.succ 0))
  simp only [hsucc, hzero]

private def HigherHurewicz.CubicalBoundary.CubicalEvaluator.uncurry {n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} {A : Type*} [AddCommGroup A]
    (E : HigherHurewicz.CubicalBoundary.CubicalEvaluator (n + 1) x A) :
    HigherHurewicz.CubicalBoundary.CubicalEvaluator n (GenLoop.const : GenLoop (Fin 1) X x) A
    where
  evaluate p := E (HigherHurewicz.CubicalBoundary.uncurryLoop p)
  map_const := by rw [HigherHurewicz.CubicalBoundary.uncurryLoop_const]; exact E.map_const
  map_homotopic h := E.map_homotopic (HigherHurewicz.CubicalBoundary.uncurryLoop_homotopic h)
  map_transAt i p
    q := by
    rw [HigherHurewicz.CubicalBoundary.uncurryLoop_transAt]
    exact E.map_transAt i.succ _ _
  map_symmAt i
    p := by
    rw [HigherHurewicz.CubicalBoundary.uncurryLoop_symmAt]
    exact E.map_symmAt i.succ _
  map_swap p i j
    hij := by
    rw [HigherHurewicz.CubicalBoundary.uncurryLoop_swap]
    exact E.map_swap _ i.succ j.succ (fun h => hij (Fin.succ_inj.mp h))

@[simp]
private theorem HigherHurewicz.CubicalBoundary.CubicalEvaluator.uncurry_apply {n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} {A : Type*} [AddCommGroup A]
    (E : HigherHurewicz.CubicalBoundary.CubicalEvaluator (n + 1) x A)
    (p : GenLoop (Fin n) (GenLoop (Fin 1) X x) GenLoop.const) :
    E.uncurry p = E (HigherHurewicz.CubicalBoundary.uncurryLoop p) :=
  rfl

private theorem HigherHurewicz.CubicalBoundary.CubicalEvaluator.map_constantClosingPaths {n : ℕ}
    {X : Type*} [TopologicalSpace X] {x : X} {A : Type*} [AddCommGroup A]
    (E : HigherHurewicz.CubicalBoundary.CubicalEvaluator (n + 1) x A)
    (p : GenLoop (Fin (n + 1)) X x) :
    E (GenLoop.transAt 0 GenLoop.const (GenLoop.transAt 0 p GenLoop.const)) = E p := by
  rw [E.map_transAt, E.map_transAt, E.map_const, zero_add, add_zero]

private theorem
    HigherHurewicz.CubicalBoundary.CubicalEvaluator.map_cyclicClosingPaths {n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} {A : Type*} [AddCommGroup A]
    (E : HigherHurewicz.CubicalBoundary.CubicalEvaluator (n + 1) x A)
    (l p r : GenLoop (Fin (n + 1)) X x) :
    E
        (GenLoop.transAt 0
          (HigherHurewicz.NativeSubdivision.permuteCubeLoop l (finRotate (n + 1)))
          (GenLoop.transAt 0 p
            (GenLoop.symmAt 0
              (HigherHurewicz.NativeSubdivision.permuteCubeLoop r (finRotate (n + 1)))))) =
      E p - (-1 : ℤ) ^ n • (E r - E l) := by
  rw [E.map_transAt, E.map_transAt, E.map_symmAt, E.map_finRotate, E.map_finRotate]
  simp only [Nat.add_sub_cancel, smul_sub]
  abel

private theorem HigherHurewicz.CubicalBoundary.alternatingSign_smul_involution {A : Type*}
    [AddCommGroup A] (n : ℕ) (a : A) : (-1 : ℤ) ^ n • ((-1 : ℤ) ^ n • a) = a := by
  rw [smul_smul, ← mul_pow]
  simp

private theorem
    HigherHurewicz.CubicalBoundary.alternatingSum_head {A : Type*} [AddCommGroup A] (n : ℕ)
    (a : Fin (n + 2) → A) :
    (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • a i) =
      a 0 - ∑ i : Fin (n + 1), (-1 : ℤ) ^ i.val • a i.succ := by
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_succ, pow_succ', neg_mul, one_mul,
    neg_smul, Finset.sum_neg_distrib, sub_eq_add_neg]

private theorem HigherHurewicz.CubicalBoundary.alternatingSum_dimension_reduction {A : Type*}
    [AddCommGroup A] (n : ℕ) (a : Fin (n + 2) → A) (b : Fin (n + 1) → A)
    (hmid : ∀ i : Fin n, b i.castSucc = a i.castSucc.succ)
    (hlast : b (Fin.last n) = a (Fin.last (n + 1)) - (-1 : ℤ) ^ n • a 0) :
    (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • a i) = -(∑ i : Fin (n + 1), (-1 : ℤ) ^ i.val • b i) := by
  have htail :
    (∑ i : Fin (n + 1), (-1 : ℤ) ^ i.val • b i) =
      (∑ i : Fin (n + 1), (-1 : ℤ) ^ i.val • a i.succ) - a 0 := by
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    simp only [hmid, hlast, Fin.val_castSucc, Fin.val_last, Fin.succ_last, smul_sub,
      alternatingSign_smul_involution]
    abel
  rw [alternatingSum_head, htail]
  abel

private theorem HigherHurewicz.CubicalBoundary.whiskeredCell_lower_value {n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} {A : Type*} [AddCommGroup A] (E : CubicalEvaluator (n + 1) x A)
    (F : BasedCubicalCell (n + 2) x) (i : Fin (n + 1)) :
    E.uncurry (cubicalLowerFace (whiskeredCell F) i) = E (cubicalLowerFace F i.succ) := by
  rw [CubicalEvaluator.uncurry_apply, whiskeredCell_face_normal F i 0 (Or.inl rfl) (Or.inr rfl)]
  exact E.map_constantClosingPaths _

private theorem HigherHurewicz.CubicalBoundary.whiskeredCell_upper_value {n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} {A : Type*} [AddCommGroup A] (E : CubicalEvaluator (n + 1) x A)
    (F : BasedCubicalCell (n + 2) x) (i : Fin n) :
    E.uncurry (cubicalUpperFace (whiskeredCell F) i.castSucc) =
      E (cubicalUpperFace F i.castSucc.succ) := by
  rw [CubicalEvaluator.uncurry_apply,
    whiskeredCell_face_normal F i.castSucc 1 (Or.inr rfl) (Or.inl (Fin.castSucc_ne_last i))]
  exact E.map_constantClosingPaths _

private theorem HigherHurewicz.CubicalBoundary.whiskeredCell_last_upper_value {n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} {A : Type*} [AddCommGroup A] (E : CubicalEvaluator (n + 1) x A)
    (F : BasedCubicalCell (n + 2) x) :
    E.uncurry (cubicalUpperFace (whiskeredCell F) (Fin.last n)) =
      E (cubicalUpperFace F (Fin.last (n + 1))) -
        (-1 : ℤ) ^ n • (E (cubicalUpperFace F 0) - E (cubicalLowerFace F 0)) := by
  rw [CubicalEvaluator.uncurry_apply, whiskeredCell_face_last_upper]
  exact E.map_cyclicClosingPaths _ _ _

private theorem HigherHurewicz.CubicalBoundary.cubicalBoundaryValue_dimension_reduction {n : ℕ}
    {X : Type*} [TopologicalSpace X] {x : X} {A : Type*} [AddCommGroup A]
    (E : CubicalEvaluator (n + 1) x A) (F : BasedCubicalCell (n + 2) x) :
    cubicalBoundaryValue E F = -cubicalBoundaryValue E.uncurry (whiskeredCell F) := by
  unfold cubicalBoundaryValue
  apply alternatingSum_dimension_reduction n
  · intro i
    rw [whiskeredCell_upper_value, whiskeredCell_lower_value]
  · rw [whiskeredCell_last_upper_value, whiskeredCell_lower_value, Fin.succ_last]
    abel

private def HigherHurewicz.CubicalBoundary.squareLowerRoute :
    C(Fin 1 → (unitInterval), Fin 2 → (unitInterval))
    where
  toFun
    u :=
    ![Set.projIcc 0 1 zero_le_one (2 * (u 0 : ℝ)),
      Set.projIcc 0 1 zero_le_one (2 * (u 0 : ℝ) - 1)]
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp
    · exact continuous_projIcc.comp (by fun_prop)
    · exact continuous_projIcc.comp (by fun_prop)

private def HigherHurewicz.CubicalBoundary.squareUpperRoute :
    C(Fin 1 → (unitInterval), Fin 2 → (unitInterval))
    where
  toFun
    u :=
    ![Set.projIcc 0 1 zero_le_one (2 * (u 0 : ℝ) - 1),
      Set.projIcc 0 1 zero_le_one (2 * (u 0 : ℝ))]
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp
    · exact continuous_projIcc.comp (by fun_prop)
    · exact continuous_projIcc.comp (by fun_prop)

@[simp]
private theorem HigherHurewicz.CubicalBoundary.squareLowerRoute_zero (u : Fin 1 → (unitInterval))
    (hu : u 0 = 0) : squareLowerRoute u = fun _ => 0 := by
  funext i
  fin_cases i <;> apply Subtype.ext <;> norm_num [squareLowerRoute, hu, Set.projIcc]

@[simp]
private theorem HigherHurewicz.CubicalBoundary.squareLowerRoute_one (u : Fin 1 → (unitInterval))
    (hu : u 0 = 1) : squareLowerRoute u = fun _ => 1 := by
  funext i
  fin_cases i <;> apply Subtype.ext <;> norm_num [squareLowerRoute, hu, Set.projIcc]

@[simp]
private theorem HigherHurewicz.CubicalBoundary.squareUpperRoute_zero (u : Fin 1 → (unitInterval))
    (hu : u 0 = 0) : squareUpperRoute u = fun _ => 0 := by
  funext i
  fin_cases i <;> apply Subtype.ext <;> norm_num [squareUpperRoute, hu, Set.projIcc]

@[simp]
private theorem HigherHurewicz.CubicalBoundary.squareUpperRoute_one (u : Fin 1 → (unitInterval))
    (hu : u 0 = 1) : squareUpperRoute u = fun _ => 1 := by
  funext i
  fin_cases i <;> apply Subtype.ext <;> norm_num [squareUpperRoute, hu, Set.projIcc]

private theorem HigherHurewicz.CubicalBoundary.squareLowerRoute_of_le (u : Fin 1 → (unitInterval))
    (hu : (u 0 : ℝ) ≤ 1 / 2) :
    squareLowerRoute u = ![Set.projIcc 0 1 zero_le_one (2 * (u 0 : ℝ)), 0] := by
  funext i
  fin_cases i
  · rfl
  · exact Set.projIcc_of_le_left zero_le_one (by linarith)

private theorem
    HigherHurewicz.CubicalBoundary.squareLowerRoute_of_not_le (u : Fin 1 → (unitInterval))
    (hu : ¬(u 0 : ℝ) ≤ 1 / 2) :
    squareLowerRoute u = ![1, Set.projIcc 0 1 zero_le_one (2 * (u 0 : ℝ) - 1)] := by
  funext i
  fin_cases i
  · exact Set.projIcc_of_right_le zero_le_one (by linarith)
  · rfl

private theorem HigherHurewicz.CubicalBoundary.squareUpperRoute_of_le (u : Fin 1 → (unitInterval))
    (hu : (u 0 : ℝ) ≤ 1 / 2) :
    squareUpperRoute u = ![0, Set.projIcc 0 1 zero_le_one (2 * (u 0 : ℝ))] := by
  funext i
  fin_cases i
  · exact Set.projIcc_of_le_left zero_le_one (by linarith)
  · rfl

private theorem
    HigherHurewicz.CubicalBoundary.squareUpperRoute_of_not_le (u : Fin 1 → (unitInterval))
    (hu : ¬(u 0 : ℝ) ≤ 1 / 2) :
    squareUpperRoute u = ![Set.projIcc 0 1 zero_le_one (2 * (u 0 : ℝ) - 1), 1] := by
  funext i
  fin_cases i
  · rfl
  · exact Set.projIcc_of_right_le zero_le_one (by linarith)

private def HigherHurewicz.CubicalBoundary.squareRoutesBlend :
    C((unitInterval) × (Fin 1 → (unitInterval)), Fin 2 → (unitInterval))
    where
  toFun
    u :=
    HigherHurewicz.NativeSubdivision.nativeCubeBlend u.1 (squareLowerRoute u.2)
      (squareUpperRoute u.2)
  continuous_toFun := by
    apply continuous_pi
    intro i
    exact
      Set.Icc.continuous_convexComb_prod.comp
        (((continuous_apply i).comp (squareLowerRoute.continuous.comp continuous_snd)).prodMk
          (((continuous_apply i).comp (squareUpperRoute.continuous.comp continuous_snd)).prodMk
            continuous_fst))

@[simp]
private theorem HigherHurewicz.CubicalBoundary.squareRoutesBlend_zero (u : Fin 1 → (unitInterval)) :
    squareRoutesBlend (0, u) = squareLowerRoute u :=
  HigherHurewicz.NativeSubdivision.nativeCubeBlend_zero _ _

@[simp]
private theorem HigherHurewicz.CubicalBoundary.squareRoutesBlend_one (u : Fin 1 → (unitInterval)) :
    squareRoutesBlend (1, u) = squareUpperRoute u :=
  HigherHurewicz.NativeSubdivision.nativeCubeBlend_one _ _

private theorem HigherHurewicz.CubicalBoundary.squareRoutesBlend_endpoint_zero (t : (unitInterval))
    (u : Fin 1 → (unitInterval)) (hu : u 0 = 0) : squareRoutesBlend (t, u) = fun _ => 0 := by
  funext i
  simp [squareRoutesBlend, HigherHurewicz.NativeSubdivision.nativeCubeBlend,
    squareLowerRoute_zero u hu, squareUpperRoute_zero u hu]

private theorem HigherHurewicz.CubicalBoundary.squareRoutesBlend_endpoint_one (t : (unitInterval))
    (u : Fin 1 → (unitInterval)) (hu : u 0 = 1) : squareRoutesBlend (t, u) = fun _ => 1 := by
  funext i
  simp [squareRoutesBlend, HigherHurewicz.NativeSubdivision.nativeCubeBlend,
    squareLowerRoute_one u hu, squareUpperRoute_one u hu]

private theorem HigherHurewicz.CubicalBoundary.squareFacet_zero (ε : (unitInterval))
    (u : Fin 1 → (unitInterval)) : cubeFacet 1 0 ε u = ![ε, u 0] := by
  funext i
  fin_cases i
  · exact cubeFacet_apply_self 1 0 ε u
  · change cubeFacet 1 0 ε u ((0 : Fin 2).succAbove 0) = u 0
    exact cubeFacet_apply_succAbove 1 0 ε u 0

private theorem HigherHurewicz.CubicalBoundary.squareFacet_one (ε : (unitInterval))
    (u : Fin 1 → (unitInterval)) : cubeFacet 1 1 ε u = ![u 0, ε] := by
  funext i
  fin_cases i
  · change cubeFacet 1 1 ε u ((1 : Fin 2).succAbove 0) = u 0
    exact cubeFacet_apply_succAbove 1 1 ε u 0
  · exact cubeFacet_apply_self 1 1 ε u

private theorem HigherHurewicz.CubicalBoundary.squareLowerRoute_transAt_apply {X : Type*}
    [TopologicalSpace X] {x : X} (F : BasedCubicalCell 2 x) (u : Fin 1 → (unitInterval)) :
    GenLoop.transAt 0 (cubicalLowerFace F 1) (cubicalUpperFace F 0) u =
      F.val (squareLowerRoute u) := by
  change
    (if (u 0 : ℝ) ≤ 1 / 2 then
        F.val
          (cubeFacet 1 1 0 (Function.update u 0 (Set.projIcc 0 1 zero_le_one (2 * (u 0 : ℝ)))))
      else
        F.val
          (cubeFacet 1 0 1
            (Function.update u 0 (Set.projIcc 0 1 zero_le_one (2 * (u 0 : ℝ) - 1))))) =
      _
  by_cases hu : (u 0 : ℝ) ≤ 1 / 2
  · rw [ite_eq_left hu, squareLowerRoute_of_le u hu]
    simp only [squareFacet_one, Function.update_self]
  · rw [ite_eq_right hu, squareLowerRoute_of_not_le u hu]
    simp only [squareFacet_zero, Function.update_self]

private theorem HigherHurewicz.CubicalBoundary.squareUpperRoute_transAt_apply {X : Type*}
    [TopologicalSpace X] {x : X} (F : BasedCubicalCell 2 x) (u : Fin 1 → (unitInterval)) :
    GenLoop.transAt 0 (cubicalLowerFace F 0) (cubicalUpperFace F 1) u =
      F.val (squareUpperRoute u) := by
  change
    (if (u 0 : ℝ) ≤ 1 / 2 then
        F.val
          (cubeFacet 1 0 0 (Function.update u 0 (Set.projIcc 0 1 zero_le_one (2 * (u 0 : ℝ)))))
      else
        F.val
          (cubeFacet 1 1 1
            (Function.update u 0 (Set.projIcc 0 1 zero_le_one (2 * (u 0 : ℝ) - 1))))) =
      _
  by_cases hu : (u 0 : ℝ) ≤ 1 / 2
  · rw [ite_eq_left hu, squareUpperRoute_of_le u hu]
    simp only [squareFacet_zero, Function.update_self]
  · rw [ite_eq_right hu, squareUpperRoute_of_not_le u hu]
    simp only [squareFacet_one, Function.update_self]

private def
    HigherHurewicz.CubicalBoundary.squareCubicalFacesHomotopy {X : Type*} [TopologicalSpace X]
    {x : X} (F : BasedCubicalCell 2 x) :
    (GenLoop.transAt 0 (cubicalLowerFace F 1) (cubicalUpperFace F 0)).val.HomotopyRel
      (GenLoop.transAt 0 (cubicalLowerFace F 0) (cubicalUpperFace F 1)).val
      (Cube.boundary (Fin 1))
    where
  toFun z := F.val (squareRoutesBlend z)
  continuous_toFun := F.val.continuous.comp squareRoutesBlend.continuous
  map_zero_left
    u := by
    rw [squareRoutesBlend_zero]
    exact (squareLowerRoute_transAt_apply F u).symm
  map_one_left
    u := by
    rw [squareRoutesBlend_one]
    exact (squareUpperRoute_transAt_apply F u).symm
  prop' t u
    hu := by
    change
      F.val (squareRoutesBlend (t, u)) =
        GenLoop.transAt 0 (cubicalLowerFace F 1) (cubicalUpperFace F 0) u
    refine
      Eq.trans (b := x) ?_
        ((GenLoop.transAt 0 (cubicalLowerFace F 1) (cubicalUpperFace F 0)).property u hu).symm
    obtain ⟨i, hi⟩ := hu
    have hi0 : u 0 = 0 ∨ u 0 = 1 := by simpa only [Fin.fin_one_eq_zero] using hi
    rcases hi0 with hi0 | hi0
    · exact
        (congrArg F.val (squareRoutesBlend_endpoint_zero t u hi0)).trans
          (F.property (fun _ => 0) 0 1 (by decide) (Or.inl rfl) (Or.inl rfl))
    · exact
        (congrArg F.val (squareRoutesBlend_endpoint_one t u hi0)).trans
          (F.property (fun _ => 1) 0 1 (by decide) (Or.inr rfl) (Or.inr rfl))

private theorem HigherHurewicz.CubicalBoundary.squareCubicalFaces_homotopic {X : Type*}
    [TopologicalSpace X] {x : X} (F : BasedCubicalCell 2 x) :
    GenLoop.Homotopic (GenLoop.transAt 0 (cubicalLowerFace F 1) (cubicalUpperFace F 0))
      (GenLoop.transAt 0 (cubicalLowerFace F 0) (cubicalUpperFace F 1)) :=
  ⟨squareCubicalFacesHomotopy F⟩

private theorem HigherHurewicz.CubicalBoundary.cubicalBoundaryValue_square {X : Type*}
    [TopologicalSpace X] {x : X} {A : Type*} [AddCommGroup A] (E : CubicalEvaluator 1 x A)
    (F : BasedCubicalCell 2 x) : cubicalBoundaryValue E F = 0 := by
  have h := E.map_homotopic (squareCubicalFaces_homotopic F)
  rw [E.map_transAt, E.map_transAt] at h
  unfold cubicalBoundaryValue
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Fin.val_zero, Fin.val_succ,
    Nat.zero_add, pow_zero, pow_one, one_zsmul, neg_one_zsmul, ← sub_eq_add_neg]
  change
    (E (cubicalUpperFace F 0) - E (cubicalLowerFace F 0)) -
        (E (cubicalUpperFace F 1) - E (cubicalLowerFace F 1)) =
      0
  apply sub_eq_zero.mpr
  apply sub_eq_sub_iff_add_eq_add.mpr
  simpa only [add_comm] using h

private theorem HigherHurewicz.CubicalBoundary.cubicalBoundaryValue_eq_zero (n : ℕ) :
    ∀ {X : Type u} [TopologicalSpace X] {x : X} {A : Type v} [AddCommGroup A]
      (E : CubicalEvaluator (n + 1) x A) (F : BasedCubicalCell (n + 2) x),
      cubicalBoundaryValue E F = 0 := by
  induction n with
  | zero =>
    intro X _ x A _ E F
    exact cubicalBoundaryValue_square E F
  | succ n ih =>
    intro X _ x A _ E F
    rw [cubicalBoundaryValue_dimension_reduction, ih E.uncurry (whiskeredCell F), neg_zero]

private theorem HigherHurewicz.SimplexGeometry.basedSimplexBoundary_evaluation {X : Type*}
    [TopologicalSpace X] {x : X} {A : Type*} [AddCommGroup A] {n : ℕ}
    (E : HigherHurewicz.CubicalBoundary.CubicalEvaluator (n + 1) x A)
    (τ : BasedSimplexBoundary (n + 2) x) :
    (∑ i : Fin (n + 3), (-1 : ℤ) ^ i.val • E (basedSimplexLoop (basedSimplexBoundaryFace τ i))) =
      0 := by
  rw [← simplexBoundaryCube_boundaryValue]
  exact HigherHurewicz.CubicalBoundary.cubicalBoundaryValue_eq_zero n E (simplexBoundaryCube τ)

private theorem HigherHurewicz.SimplexGeometry.basedSimplexBoundary_signed_relation {X : Type*}
    [TopologicalSpace X] {x : X} {n : ℕ} (τ : BasedSimplexBoundary (n + 3) x) :
    (∑ i : Fin (n + 4), (-1 : ℤ) ^ i.val • basedSimplexClass (basedSimplexBoundaryFace τ i)) =
      0 :=
  basedSimplexBoundary_evaluation (HigherHurewicz.CubicalBoundary.nativeCubicalEvaluator n x) τ

private theorem
    FourthHurewicz.basedFiveSimplex_signed_relation {X : Type*} [TopologicalSpace X] {x : X}
    (τ : BasedFiveSimplex x) :
    (∑ i : Fin 6, (-1 : ℤ) ^ i.val • basedFourSimplexClass (basedFiveSimplexFace τ i)) = 0 :=
  HigherHurewicz.SimplexGeometry.basedSimplexBoundary_signed_relation (n := 2) τ

private theorem
    FourthHurewicz.normalizedFourSimplex_boundary_relation {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    (smp : FirstHurewicz.SingularSimplex X 5) :
    ∑ i : Fin 6,
        (-1 : ℤ) ^ i.val •
          basedFourSimplexClass
            (normalizedFourSimplex x (smp.comp (FirstHurewicz.simplexFace 4 i))) =
      0 := by
  simpa only [normalizedFiveSimplex_face] using
    basedFiveSimplex_signed_relation (normalizedFiveSimplex x smp)

private theorem FourthHurewicz.fourSimplexClassOperator_boundary {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    (b : FirstHurewicz.Chains X 5) :
    fourSimplexClassOperator x (((FirstHurewicz.singularComplex X).d 5 4).hom b) = 0 := by
  have h : (fourSimplexClassOperator x).comp ((FirstHurewicz.singularComplex X).d 5 4).hom = 0 := by
    apply FirstHurewicz.chainMap_ext X 5
    intro smp
    simp only [LinearMap.comp_apply, FirstHurewicz.boundary_simplex, map_sum, map_zsmul,
      fourSimplexClassOperator_simplex, LinearMap.zero_apply]
    exact normalizedFourSimplex_boundary_relation x smp
  exact LinearMap.congr_fun h b

private theorem HigherHurewicz.CubeTriangulation.exists_cubeSimplex {n : ℕ} (u : CubeN n) :
    ∃ e : Equiv.Perm (Fin n), ∃ s : FirstHurewicz.Simplex n, cubeSimplex e s = u := by
  obtain ⟨e, he⟩ := exists_sortedPermutation u
  exact ⟨e, cubeSimplexInverse e ⟨u, he⟩, cubeSimplex_inverse e ⟨u, he⟩⟩

private def HigherHurewicz.CubeTriangulation.cubeSimplexCylinder {n : ℕ} (e : Equiv.Perm (Fin n)) :
    C((unitInterval) × FirstHurewicz.Simplex n, (unitInterval) × CubeN n) :=
  (ContinuousMap.id (unitInterval)).prodMap (cubeSimplex e)

private def HigherHurewicz.CubeTriangulation.cubeCylinderCover (n : ℕ) :
    C((Σ _e : Equiv.Perm (Fin n), (unitInterval) × FirstHurewicz.Simplex n),
      (unitInterval) × CubeN n)
    where
  toFun a := cubeSimplexCylinder a.fst a.snd
  continuous_toFun := continuous_sigma fun e => (cubeSimplexCylinder e).continuous

private theorem HigherHurewicz.CubeTriangulation.cubeCylinderCover_surjective (n : ℕ) :
    Function.Surjective (cubeCylinderCover n) := by
  rintro ⟨r, u⟩
  obtain ⟨e, s, rfl⟩ := exists_cubeSimplex u
  exact ⟨⟨e, (r, s)⟩, rfl⟩

private theorem HigherHurewicz.CubeTriangulation.cubeCylinderCover_isQuotientMap (n : ℕ) :
    Topology.IsQuotientMap (cubeCylinderCover n) :=
  Topology.IsQuotientMap.of_surjective_continuous (cubeCylinderCover_surjective n)
    (cubeCylinderCover n).continuous

private def HigherHurewicz.CubeGluing.CubeCompatible {n : ℕ} {X : Type} [TopologicalSpace X]
    (F : Equiv.Perm (Fin n) → C((unitInterval) × FirstHurewicz.Simplex n, X)) : Prop :=
  ∀ (e f : Equiv.Perm (Fin n)) (s t : FirstHurewicz.Simplex n),
    HigherHurewicz.CubeTriangulation.cubeSimplex e s =
        HigherHurewicz.CubeTriangulation.cubeSimplex f t →
      ∀ r : (unitInterval), F e (r, s) = F f (r, t)

private def HigherHurewicz.CubeGluing.cubeFamilyMap {n : ℕ} {X : Type} [TopologicalSpace X]
    (F : Equiv.Perm (Fin n) → C((unitInterval) × FirstHurewicz.Simplex n, X)) :
    C((Σ _e : Equiv.Perm (Fin n), (unitInterval) × FirstHurewicz.Simplex n), X)
    where
  toFun a := F a.fst a.snd
  continuous_toFun := continuous_sigma fun e => (F e).continuous

private theorem HigherHurewicz.CubeGluing.cubeFamilyMap_factorsThrough {n : ℕ} {X : Type}
    [TopologicalSpace X] (F : Equiv.Perm (Fin n) → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (hF : CubeCompatible F) :
    Function.FactorsThrough (cubeFamilyMap F)
      (HigherHurewicz.CubeTriangulation.cubeCylinderCover n) := by
  rintro ⟨e, r, s⟩ ⟨f, q, t⟩ h
  have hr : r = q := congrArg Prod.fst h
  have hs :
    HigherHurewicz.CubeTriangulation.cubeSimplex e s =
      HigherHurewicz.CubeTriangulation.cubeSimplex f t :=
    congrArg Prod.snd h
  subst q
  exact hF e f s t hs r

private def HigherHurewicz.CubeGluing.glueCubeHomotopies {n : ℕ} {X : Type} [TopologicalSpace X]
    (F : Equiv.Perm (Fin n) → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (hF : CubeCompatible F) : C((unitInterval) × HigherHurewicz.CubeTriangulation.CubeN n, X) :=
  (HigherHurewicz.CubeTriangulation.cubeCylinderCover_isQuotientMap n).lift (cubeFamilyMap F)
    (cubeFamilyMap_factorsThrough F hF)

@[simp]
private theorem
    HigherHurewicz.CubeGluing.glueCubeHomotopies_cell {n : ℕ} {X : Type} [TopologicalSpace X]
    (F : Equiv.Perm (Fin n) → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (hF : CubeCompatible F) (e : Equiv.Perm (Fin n)) (r : (unitInterval))
    (s : FirstHurewicz.Simplex n) :
    glueCubeHomotopies F hF (r, HigherHurewicz.CubeTriangulation.cubeSimplex e s) = F e (r, s) :=
  DFunLike.congr_fun
    ((HigherHurewicz.CubeTriangulation.cubeCylinderCover_isQuotientMap n).lift_comp
      (cubeFamilyMap F) (cubeFamilyMap_factorsThrough F hF))
    ⟨e, (r, s)⟩

private theorem
    HigherHurewicz.CubeGluing.glueCubeHomotopies_time {n : ℕ} {X : Type} [TopologicalSpace X]
    (F : Equiv.Perm (Fin n) → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (hF : CubeCompatible F) (r : (unitInterval))
    (g : HigherHurewicz.CubeTriangulation.CubeN n → X)
    (h :
      ∀ (e : Equiv.Perm (Fin n)) (s : FirstHurewicz.Simplex n),
        F e (r, s) = g (HigherHurewicz.CubeTriangulation.cubeSimplex e s))
    (u : HigherHurewicz.CubeTriangulation.CubeN n) : glueCubeHomotopies F hF (r, u) = g u := by
  obtain ⟨e, s, rfl⟩ := HigherHurewicz.CubeTriangulation.exists_cubeSimplex u
  exact (glueCubeHomotopies_cell F hF e r s).trans (h e s)

private theorem
    HigherHurewicz.CubeGluing.glueCubeHomotopies_zero {n : ℕ} {X : Type} [TopologicalSpace X]
    (F : Equiv.Perm (Fin n) → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (hF : CubeCompatible F) (g : C(HigherHurewicz.CubeTriangulation.CubeN n, X))
    (h :
      ∀ (e : Equiv.Perm (Fin n)) (s : FirstHurewicz.Simplex n),
        F e (0, s) = g (HigherHurewicz.CubeTriangulation.cubeSimplex e s))
    (u : HigherHurewicz.CubeTriangulation.CubeN n) : glueCubeHomotopies F hF (0, u) = g u :=
  glueCubeHomotopies_time F hF 0 g h u

private theorem HigherHurewicz.CubeTriangulation.cubeSimplex_mem_boundary_iff {n : ℕ}
    (e : Equiv.Perm (Fin (n + 1))) (s : FirstHurewicz.Simplex (n + 1)) :
    cubeSimplex e s ∈ Cube.boundary (Fin (n + 1)) ↔ s 0 = 0 ∨ s (Fin.last (n + 1)) = 0 := by
  constructor
  · rintro ⟨i, hi⟩
    obtain ⟨j, rfl⟩ := e.surjective i
    rcases hi with hi | hi
    · right
      have hlast : (cubeSimplex e s (e (Fin.last n)) : ℝ) ≤ (cubeSimplex e s (e j) : ℝ) :=
        cubeSimplex_antitone e s (Fin.le_last j)
      have hr := congrArg (fun t : (unitInterval) => (t : ℝ)) hi
      change (cubeSimplex e s (e j) : ℝ) = 0 at hr
      rw [cubeSimplex_coordinate_last, hr] at hlast
      exact le_antisymm hlast (stdSimplex.zero_le s (Fin.last (n + 1)))
    · left
      have hfirst : (cubeSimplex e s (e j) : ℝ) ≤ (cubeSimplex e s (e 0) : ℝ) :=
        cubeSimplex_antitone e s (Fin.zero_le j)
      have hr := congrArg (fun t : (unitInterval) => (t : ℝ)) hi
      change (cubeSimplex e s (e j) : ℝ) = 1 at hr
      rw [cubeSimplex_coordinate_zero, hr] at hfirst
      linarith [stdSimplex.zero_le s 0]
  · rintro (hs | hs)
    · refine ⟨e 0, Or.inr ?_⟩
      apply Subtype.ext
      change (cubeSimplex e s (e 0) : ℝ) = 1
      rw [cubeSimplex_coordinate_zero, hs, sub_zero]
    · refine ⟨e (Fin.last n), Or.inl ?_⟩
      apply Subtype.ext
      change (cubeSimplex e s (e (Fin.last n)) : ℝ) = 0
      rw [cubeSimplex_coordinate_last, hs]

private theorem
    HigherHurewicz.CubeTriangulation.cubeSimplex_tie {n : ℕ} (e : Equiv.Perm (Fin (n + 1)))
    (s : FirstHurewicz.Simplex (n + 1)) (i : Fin n)
    (h : cubeSimplex e s (e i.castSucc) = cubeSimplex e s (e i.succ)) : s i.succ.castSucc = 0 := by
  have hd := cubeSimplex_adjacent_difference e s i
  rw [h, sub_self] at hd
  exact hd.symm

private theorem HigherHurewicz.CubeTriangulation.cubeSimplex_tie_iff {n : ℕ}
    (e : Equiv.Perm (Fin (n + 1))) (s : FirstHurewicz.Simplex (n + 1)) (i : Fin n) :
    cubeSimplex e s (e i.castSucc) = cubeSimplex e s (e i.succ) ↔ s i.succ.castSucc = 0 := by
  refine ⟨cubeSimplex_tie e s i, ?_⟩
  intro hs
  apply Subtype.ext
  have hd := cubeSimplex_adjacent_difference e s i
  rw [hs] at hd
  exact sub_eq_zero.mp hd

private theorem
    HigherHurewicz.CubeGluing.cubeOriginal_face_zero {n : ℕ} {X : Type} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin (n + 1)) X x) (e : Equiv.Perm (Fin (n + 1))) :
    (p.val.comp (HigherHurewicz.CubeTriangulation.cubeSimplex e)).comp
        (FirstHurewicz.simplexFace n 0) =
      ContinuousMap.const (FirstHurewicz.Simplex n) x := by
  ext s
  exact GenLoop.boundary p _ (HigherHurewicz.CubeTriangulation.cubeSimplex_face_zero_boundary e s)

private theorem
    HigherHurewicz.CubeGluing.cubeOriginal_face_last {n : ℕ} {X : Type} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin (n + 1)) X x) (e : Equiv.Perm (Fin (n + 1))) :
    (p.val.comp (HigherHurewicz.CubeTriangulation.cubeSimplex e)).comp
        (FirstHurewicz.simplexFace n (Fin.last (n + 1))) =
      ContinuousMap.const (FirstHurewicz.Simplex n) x := by
  ext s
  exact GenLoop.boundary p _ (HigherHurewicz.CubeTriangulation.cubeSimplex_face_last_boundary e s)

private theorem
    HigherHurewicz.CubeGluing.cubeOriginal_face_swap {n : ℕ} {X : Type} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin (n + 1)) X x) (e : Equiv.Perm (Fin (n + 1))) (i : Fin n) :
    (p.val.comp (HigherHurewicz.CubeTriangulation.cubeSimplex e)).comp
        (FirstHurewicz.simplexFace n i.succ.castSucc) =
      (p.val.comp
            (HigherHurewicz.CubeTriangulation.cubeSimplex
              ((Equiv.swap i.castSucc i.succ).trans e))).comp
        (FirstHurewicz.simplexFace n i.succ.castSucc) := by
  simpa only [ContinuousMap.comp_assoc] using
    congrArg
      (fun f : C(FirstHurewicz.Simplex n, HigherHurewicz.CubeTriangulation.CubeN (n + 1)) =>
        p.val.comp f)
      (HigherHurewicz.CubeTriangulation.cubeSimplex_face_swap e i)

private theorem
    HigherHurewicz.CubeGluing.coherentCubeCell_face {n : ℕ} {X : Type} [TopologicalSpace X]
    {x : X} (H₀ : C(FirstHurewicz.Simplex n, X) → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (H₁ :
      C(FirstHurewicz.Simplex (n + 1), X) → C((unitInterval) × FirstHurewicz.Simplex (n + 1), X))
    (hface : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies n H₀ H₁)
    (p : GenLoop (Fin (n + 1)) X x) (e : Equiv.Perm (Fin (n + 1))) (i : Fin (n + 2))
    (r : (unitInterval)) (s : FirstHurewicz.Simplex n) :
    H₁ (p.val.comp (HigherHurewicz.CubeTriangulation.cubeSimplex e))
        (r, FirstHurewicz.simplexFace n i s) =
      H₀
        ((p.val.comp (HigherHurewicz.CubeTriangulation.cubeSimplex e)).comp
          (FirstHurewicz.simplexFace n i))
        (r, s) :=
  DFunLike.congr_fun (hface (p.val.comp (HigherHurewicz.CubeTriangulation.cubeSimplex e)) i)
    (r, s)

private theorem
    HigherHurewicz.CubeGluing.coherentCubeCell_swap {n : ℕ} {X : Type} [TopologicalSpace X]
    {x : X} (H₀ : C(FirstHurewicz.Simplex n, X) → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (H₁ :
      C(FirstHurewicz.Simplex (n + 1), X) → C((unitInterval) × FirstHurewicz.Simplex (n + 1), X))
    (hface : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies n H₀ H₁)
    (p : GenLoop (Fin (n + 1)) X x) (e : Equiv.Perm (Fin (n + 1))) (i : Fin n)
    (r : (unitInterval)) (s : FirstHurewicz.Simplex (n + 1)) (hs : s i.succ.castSucc = 0) :
    H₁ (p.val.comp (HigherHurewicz.CubeTriangulation.cubeSimplex e)) (r, s) =
      H₁
        (p.val.comp
          (HigherHurewicz.CubeTriangulation.cubeSimplex ((Equiv.swap i.castSucc i.succ).trans e)))
        (r, s) := by
  let t := SecondHurewicz.SimplyConnected.simplexFaceInverse n i.succ.castSucc ⟨s, hs⟩
  have ht : FirstHurewicz.simplexFace n i.succ.castSucc t = s :=
    SecondHurewicz.SimplyConnected.simplexFace_inverse n i.succ.castSucc ⟨s, hs⟩
  rw [← ht, coherentCubeCell_face H₀ H₁ hface, coherentCubeCell_face H₀ H₁ hface,
    cubeOriginal_face_swap]

private theorem HigherHurewicz.CubeGluing.coherentCubeCell_boundary {n : ℕ} {X : Type}
    [TopologicalSpace X] {x : X}
    (H₀ : C(FirstHurewicz.Simplex n, X) → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (H₁ :
      C(FirstHurewicz.Simplex (n + 1), X) → C((unitInterval) × FirstHurewicz.Simplex (n + 1), X))
    (hface : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies n H₀ H₁)
    (hconst :
      H₀ (ContinuousMap.const (FirstHurewicz.Simplex n) x) =
        ContinuousMap.const ((unitInterval) × FirstHurewicz.Simplex n) x)
    (p : GenLoop (Fin (n + 1)) X x) (e : Equiv.Perm (Fin (n + 1))) (r : (unitInterval))
    (s : FirstHurewicz.Simplex (n + 1))
    (hs : HigherHurewicz.CubeTriangulation.cubeSimplex e s ∈ Cube.boundary (Fin (n + 1))) :
    H₁ (p.val.comp (HigherHurewicz.CubeTriangulation.cubeSimplex e)) (r, s) = x := by
  rcases (HigherHurewicz.CubeTriangulation.cubeSimplex_mem_boundary_iff e s).mp hs with hs | hs
  · let t := SecondHurewicz.SimplyConnected.simplexFaceInverse n 0 ⟨s, hs⟩
    have ht : FirstHurewicz.simplexFace n 0 t = s :=
      SecondHurewicz.SimplyConnected.simplexFace_inverse n 0 ⟨s, hs⟩
    rw [← ht, coherentCubeCell_face H₀ H₁ hface, cubeOriginal_face_zero, hconst]
    rfl
  · let t := SecondHurewicz.SimplyConnected.simplexFaceInverse n (Fin.last (n + 1)) ⟨s, hs⟩
    have ht : FirstHurewicz.simplexFace n (Fin.last (n + 1)) t = s :=
      SecondHurewicz.SimplyConnected.simplexFace_inverse n (Fin.last (n + 1)) ⟨s, hs⟩
    rw [← ht, coherentCubeCell_face H₀ H₁ hface, cubeOriginal_face_last, hconst]
    rfl

private theorem HigherHurewicz.CubeTriangulation.cubeSimplex_eq_of_sorted {n : ℕ}
    (e f : Equiv.Perm (Fin n)) (s : FirstHurewicz.Simplex n)
    (hf : SortedCoordinates (cubeSimplex e s) f) : cubeSimplex f s = cubeSimplex e s := by
  funext k
  obtain ⟨i, rfl⟩ := f.surjective k
  apply Subtype.ext
  calc
    (cubeSimplex f s (f i) : ℝ) = ∑ k : Fin (n + 1), if i.val < k.val then s k else 0 :=
      cubeSimplex_coordinate f s i
    _ = (cubeSimplex e s (e i) : ℝ) := (cubeSimplex_coordinate e s i).symm
    _ = (cubeSimplex e s (f i) : ℝ) :=
      congrArg Subtype.val (sorted_values_eq (cubeSimplex e s) (cubeSimplex_sorted e s) hf i)

private theorem HigherHurewicz.CubeTriangulation.cubeSimplex_overlap_preimage {n : ℕ}
    (e f : Equiv.Perm (Fin n)) (s t : FirstHurewicz.Simplex n)
    (h : cubeSimplex e s = cubeSimplex f t) : s = t := by
  have hf : SortedCoordinates (cubeSimplex e s) f := by
    rw [h]
    exact cubeSimplex_sorted f t
  exact cubeSimplex_injective f ((cubeSimplex_eq_of_sorted e f s hf).trans h)

private theorem HigherHurewicz.CubeTriangulation.coordinate_swap_of_tie {n : ℕ} {α : Type*}
    {u : Fin n → α} {e : Equiv.Perm (Fin n)} {a b : Fin n} (hab : u (e a) = u (e b)) (i : Fin n) :
    u (((Equiv.swap a b).trans e) i) = u (e i) :=
  Equiv.apply_swap_eq_self (v := fun j => u (e j)) hab i

private theorem HigherHurewicz.CubeTriangulation.sortedCoordinates_swap_of_tie {n : ℕ} {α : Type*}
    [LinearOrder α] {u : Fin n → α} {e : Equiv.Perm (Fin n)} (he : SortedCoordinates u e)
    {a b : Fin n} (hab : u (e a) = u (e b)) : SortedCoordinates u ((Equiv.swap a b).trans e) := by
  intro i j hij
  simpa only [coordinate_swap_of_tie hab] using he hij

private theorem HigherHurewicz.CubeTriangulation.swap_trans_swap_trans_swap_mo1973_8327 {n : ℕ}
    {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c) :
    ((Equiv.swap b c).trans (Equiv.swap a b)).trans (Equiv.swap b c) = Equiv.swap a c := by
  simpa only [Equiv.symm_swap, Equiv.swap_apply_of_ne_of_ne hab hac, Equiv.swap_apply_left] using
    Equiv.symm_trans_swap_trans a b (Equiv.swap b c)

private theorem HigherHurewicz.CubeTriangulation.eq_swap_of_sorted_tie_of_lt_mo1973_8328 {n : ℕ}
    {α : Type*} [LinearOrder α] (u : Fin (n + 1) → α) {A : Type*}
    (F : Equiv.Perm (Fin (n + 1)) → A)
    (hswap :
      ∀ e,
        SortedCoordinates u e →
          ∀ i : Fin n,
            u (e i.castSucc) = u (e i.succ) → F e = F ((Equiv.swap i.castSucc i.succ).trans e))
    (b : Fin (n + 1)) :
    ∀ (a : Fin (n + 1)) (e : Equiv.Perm (Fin (n + 1))),
      a < b → SortedCoordinates u e → u (e a) = u (e b) → F e = F ((Equiv.swap a b).trans e) := by
  induction b using Fin.induction with
  | zero =>
    intro a e hab
    exact (Fin.not_lt_zero a hab).elim
  | succ b ih =>
    intro a e hab he ht
    obtain rfl | hlt := (Fin.le_castSucc_iff.mpr hab).eq_or_lt
    · exact hswap e he b ht
    have hmid : u (e b.castSucc) = u (e b.succ) :=
      le_antisymm ((he hlt.le).trans ht.le) (he Fin.castSucc_lt_succ.le)
    have hleft : u (e a) = u (e b.castSucc) := ht.trans hmid.symm
    let e₁ := (Equiv.swap b.castSucc b.succ).trans e
    have h₁ : SortedCoordinates u e₁ := sortedCoordinates_swap_of_tie he hmid
    have hv₁ (i : Fin (n + 1)) : u (e₁ i) = u (e i) := coordinate_swap_of_tie hmid i
    have ht₁ : u (e₁ a) = u (e₁ b.castSucc) := by
      rw [hv₁, hv₁]
      exact hleft
    let e₂ := (Equiv.swap a b.castSucc).trans e₁
    have h₂ : SortedCoordinates u e₂ := sortedCoordinates_swap_of_tie h₁ ht₁
    have hv₂ (i : Fin (n + 1)) : u (e₂ i) = u (e₁ i) := coordinate_swap_of_tie ht₁ i
    have ht₂ : u (e₂ b.castSucc) = u (e₂ b.succ) := by
      rw [hv₂, hv₂, hv₁, hv₁]
      exact hmid
    calc
      F e = F e₁ := hswap e he b hmid
      _ = F e₂ := (ih a e₁ hlt h₁ ht₁)
      _ = F ((Equiv.swap b.castSucc b.succ).trans e₂) := (hswap e₂ h₂ b ht₂)
      _ = F ((Equiv.swap a b.succ).trans e) := by
        apply congrArg F
        dsimp only [e₂, e₁]
        rw [← Equiv.trans_assoc, ← Equiv.trans_assoc,
          swap_trans_swap_trans_swap_mo1973_8327 hlt.ne hab.ne]

private theorem
    HigherHurewicz.CubeTriangulation.eq_swap_of_sorted_tie {n : ℕ} {α : Type*} [LinearOrder α]
    (u : Fin (n + 1) → α) {A : Type*} (F : Equiv.Perm (Fin (n + 1)) → A)
    (hswap :
      ∀ e,
        SortedCoordinates u e →
          ∀ i : Fin n,
            u (e i.castSucc) = u (e i.succ) → F e = F ((Equiv.swap i.castSucc i.succ).trans e))
    {e : Equiv.Perm (Fin (n + 1))} (he : SortedCoordinates u e) (a b : Fin (n + 1))
    (hab : u (e a) = u (e b)) : F e = F ((Equiv.swap a b).trans e) := by
  rcases lt_trichotomy a b with hlt | rfl | hgt
  · exact eq_swap_of_sorted_tie_of_lt_mo1973_8328 u F hswap b a e hlt he hab
  · simp
  · simpa only [Equiv.swap_comm b a] using
      eq_swap_of_sorted_tie_of_lt_mo1973_8328 u F hswap a b e hgt he hab.symm

private theorem HigherHurewicz.CubeTriangulation.label_swap_apply_mo1973_8330 {ι β : Type*}
    [DecidableEq ι] (v : ι → β) {a b : ι} (hab : v a = v b) (z : ι) :
    v (Equiv.swap a b z) = v z := by
  by_cases hza : z = a
  · subst z
    simpa only [Equiv.swap_apply_left] using hab.symm
  by_cases hzb : z = b
  · subst z
    simpa only [Equiv.swap_apply_right] using hab
  rw [Equiv.swap_apply_of_ne_of_ne hza hzb]

private theorem HigherHurewicz.CubeTriangulation.valuePreservingPermutation_induction {ι β : Type*}
    [DecidableEq ι] [Finite ι] (v : ι → β) {P : Equiv.Perm ι → Prop} (hone : P 1)
    (hswap :
      ∀ (r : Equiv.Perm ι) (a b : ι),
        v a = v b → (∀ i, v (r i) = v i) → P r → P (Equiv.swap a b * r))
    (r : Equiv.Perm ι) (hr : ∀ i, v (r i) = v i) : P r := by
  classical
  let _ := Fintype.ofFinite ι
  suffices h : ∀ k : ℕ, ∀ q : Equiv.Perm ι, q.support.card = k → (∀ i, v (q i) = v i) → P q from
    h _ r rfl hr
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro q hq hvalues
    by_cases hqone : q = 1
    · simpa only [hqone] using hone
    have hmoved : ∃ a, q a ≠ a := by
      by_contra! hn
      exact hqone (Equiv.ext hn)
    obtain ⟨a, ha⟩ := hmoved
    let q' := Equiv.swap a (q a) * q
    have hlt : q'.support.card < k := by
      rw [← hq]
      exact Equiv.Perm.card_support_swap_mul ha
    have hvalues' : ∀ i, v (q' i) = v i := by
      intro i
      change v (Equiv.swap a (q a) (q i)) = v i
      exact (label_swap_apply_mo1973_8330 v (hvalues a).symm (q i)).trans (hvalues i)
    have hstep :=
      hswap q' a (q a) (hvalues a).symm hvalues' (ih q'.support.card hlt q' rfl hvalues')
    simpa only [q', Equiv.swap_mul_self_mul] using hstep

private theorem HigherHurewicz.CubeTriangulation.eq_of_value_preserving_swaps {ι β : Type*}
    [DecidableEq ι] [Finite ι] (v : ι → β) {A : Type*} (G : Equiv.Perm ι → A)
    (hswap :
      ∀ (r : Equiv.Perm ι),
        (∀ i, v (r i) = v i) → ∀ a b, v a = v b → G r = G (Equiv.swap a b * r))
    (r : Equiv.Perm ι) (hr : ∀ i, v (r i) = v i) : G 1 = G r :=
  valuePreservingPermutation_induction v (P := fun q => G 1 = G q) rfl
    (fun q a b hab hq ih => ih.trans (hswap q hq a b hab)) r hr

private theorem
    HigherHurewicz.CubeTriangulation.eq_of_sorted_adjacent {n : ℕ} {α : Type*} [LinearOrder α]
    (u : Fin (n + 1) → α) {A : Type*} (F : Equiv.Perm (Fin (n + 1)) → A)
    (hswap :
      ∀ e,
        SortedCoordinates u e →
          ∀ i : Fin n,
            u (e i.castSucc) = u (e i.succ) → F e = F ((Equiv.swap i.castSucc i.succ).trans e))
    {e f : Equiv.Perm (Fin (n + 1))} (he : SortedCoordinates u e) (hf : SortedCoordinates u f) :
    F e = F f := by
  have hr : ∀ i, u (e ((f.trans e.symm) i)) = u (e i) := by
    intro i
    simpa only [Equiv.trans_apply, Equiv.apply_symm_apply] using (sorted_values_eq u he hf i).symm
  have hG : F ((1 : Equiv.Perm (Fin (n + 1))).trans e) = F ((f.trans e.symm).trans e) :=
    eq_of_value_preserving_swaps (fun i => u (e i)) (fun r => F (r.trans e))
      (by
        intro r hvalues a b hab
        have hsorted : SortedCoordinates u (r.trans e) := by
          intro i j hij
          change u (e (r j)) ≤ u (e (r i))
          rw [hvalues, hvalues]
          exact he hij
        have ht : u ((r.trans e) (r.symm a)) = u ((r.trans e) (r.symm b)) := by
          simpa only [Equiv.trans_apply, Equiv.apply_symm_apply] using hab
        have hh := eq_swap_of_sorted_tie u F hswap hsorted (r.symm a) (r.symm b) ht
        refine hh.trans (congrArg F ?_)
        apply Equiv.ext
        intro i
        change e ((r * Equiv.swap (r.symm a) (r.symm b)) i) = e ((Equiv.swap a b * r) i)
        exact
          congrArg (fun q : Equiv.Perm (Fin (n + 1)) => e (q i))
            (Equiv.swap_mul_eq_mul_swap r a b).symm)
      (f.trans e.symm) hr
  simpa only [Equiv.Perm.one_def, Equiv.refl_trans, Equiv.trans_assoc, Equiv.symm_trans_self,
    Equiv.trans_refl] using hG

private theorem HigherHurewicz.CubeGluing.coherentCubeFamily_compatible {n : ℕ} {X : Type}
    [TopologicalSpace X] {x : X}
    (H₀ : C(FirstHurewicz.Simplex n, X) → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (H₁ :
      C(FirstHurewicz.Simplex (n + 1), X) → C((unitInterval) × FirstHurewicz.Simplex (n + 1), X))
    (hface : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies n H₀ H₁)
    (p : GenLoop (Fin (n + 1)) X x) :
    CubeCompatible (fun e => H₁ (p.val.comp (HigherHurewicz.CubeTriangulation.cubeSimplex e))) := by
  intro e f s t h r
  have hst := HigherHurewicz.CubeTriangulation.cubeSimplex_overlap_preimage e f s t h
  subst t
  have hf :
    HigherHurewicz.CubeTriangulation.SortedCoordinates
      (HigherHurewicz.CubeTriangulation.cubeSimplex e s) f := by
    rw [h]
    exact HigherHurewicz.CubeTriangulation.cubeSimplex_sorted f s
  apply
    HigherHurewicz.CubeTriangulation.eq_of_sorted_adjacent
      (HigherHurewicz.CubeTriangulation.cubeSimplex e s)
      (fun g => H₁ (p.val.comp (HigherHurewicz.CubeTriangulation.cubeSimplex g)) (r, s)) ?_
      (HigherHurewicz.CubeTriangulation.cubeSimplex_sorted e s) hf
  intro g hg i ht
  apply coherentCubeCell_swap H₀ H₁ hface p g i r s
  apply HigherHurewicz.CubeTriangulation.cubeSimplex_tie g s i
  simpa only [HigherHurewicz.CubeTriangulation.cubeSimplex_eq_of_sorted e g s hg] using ht

private def
    HigherHurewicz.CubeGluing.coherentCubeHomotopyMap {n : ℕ} {X : Type} [TopologicalSpace X]
    {x : X} (H₀ : C(FirstHurewicz.Simplex n, X) → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (H₁ :
      C(FirstHurewicz.Simplex (n + 1), X) → C((unitInterval) × FirstHurewicz.Simplex (n + 1), X))
    (hface : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies n H₀ H₁)
    (p : GenLoop (Fin (n + 1)) X x) :
    C((unitInterval) × HigherHurewicz.CubeTriangulation.CubeN (n + 1), X) :=
  glueCubeHomotopies (fun e => H₁ (p.val.comp (HigherHurewicz.CubeTriangulation.cubeSimplex e)))
    (coherentCubeFamily_compatible H₀ H₁ hface p)

@[simp]
private theorem HigherHurewicz.CubeGluing.coherentCubeHomotopyMap_cell {n : ℕ} {X : Type}
    [TopologicalSpace X] {x : X}
    (H₀ : C(FirstHurewicz.Simplex n, X) → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (H₁ :
      C(FirstHurewicz.Simplex (n + 1), X) → C((unitInterval) × FirstHurewicz.Simplex (n + 1), X))
    (hface : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies n H₀ H₁)
    (p : GenLoop (Fin (n + 1)) X x) (e : Equiv.Perm (Fin (n + 1))) (r : (unitInterval))
    (s : FirstHurewicz.Simplex (n + 1)) :
    coherentCubeHomotopyMap H₀ H₁ hface p (r, HigherHurewicz.CubeTriangulation.cubeSimplex e s) =
      H₁ (p.val.comp (HigherHurewicz.CubeTriangulation.cubeSimplex e)) (r, s) :=
  glueCubeHomotopies_cell _ _ e r s

private theorem HigherHurewicz.CubeGluing.coherentCubeHomotopyMap_zero {n : ℕ} {X : Type}
    [TopologicalSpace X] {x : X}
    (H₀ : C(FirstHurewicz.Simplex n, X) → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (H₁ :
      C(FirstHurewicz.Simplex (n + 1), X) → C((unitInterval) × FirstHurewicz.Simplex (n + 1), X))
    (hface : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies n H₀ H₁)
    (hzero :
      ∀ (smp : C(FirstHurewicz.Simplex (n + 1), X)) (s : FirstHurewicz.Simplex (n + 1)),
        H₁ smp (0, s) = smp s)
    (p : GenLoop (Fin (n + 1)) X x) (u : HigherHurewicz.CubeTriangulation.CubeN (n + 1)) :
    coherentCubeHomotopyMap H₀ H₁ hface p (0, u) = p u :=
  glueCubeHomotopies_zero _ _ p.val
    (fun e s => hzero (p.val.comp (HigherHurewicz.CubeTriangulation.cubeSimplex e)) s) u

private theorem HigherHurewicz.CubeGluing.coherentCubeHomotopyMap_boundary {n : ℕ} {X : Type}
    [TopologicalSpace X] {x : X}
    (H₀ : C(FirstHurewicz.Simplex n, X) → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (H₁ :
      C(FirstHurewicz.Simplex (n + 1), X) → C((unitInterval) × FirstHurewicz.Simplex (n + 1), X))
    (hface : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies n H₀ H₁)
    (hconst :
      H₀ (ContinuousMap.const (FirstHurewicz.Simplex n) x) =
        ContinuousMap.const ((unitInterval) × FirstHurewicz.Simplex n) x)
    (p : GenLoop (Fin (n + 1)) X x) (r : (unitInterval))
    (u : HigherHurewicz.CubeTriangulation.CubeN (n + 1)) (hu : u ∈ Cube.boundary (Fin (n + 1))) :
    coherentCubeHomotopyMap H₀ H₁ hface p (r, u) = x := by
  obtain ⟨e, s, rfl⟩ := HigherHurewicz.CubeTriangulation.exists_cubeSimplex u
  rw [coherentCubeHomotopyMap_cell]
  exact coherentCubeCell_boundary H₀ H₁ hface hconst p e r s hu

private def
    HigherHurewicz.CubeGluing.coherentCubeEndpoint {n : ℕ} {X : Type} [TopologicalSpace X] {x : X}
    (H₀ : C(FirstHurewicz.Simplex n, X) → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (H₁ :
      C(FirstHurewicz.Simplex (n + 1), X) → C((unitInterval) × FirstHurewicz.Simplex (n + 1), X))
    (hface : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies n H₀ H₁)
    (hconst :
      H₀ (ContinuousMap.const (FirstHurewicz.Simplex n) x) =
        ContinuousMap.const ((unitInterval) × FirstHurewicz.Simplex n) x)
    (p : GenLoop (Fin (n + 1)) X x) : GenLoop (Fin (n + 1)) X x :=
  ⟨SecondHurewicz.SimplyConnected.timeSlice (coherentCubeHomotopyMap H₀ H₁ hface p) 1, fun u hu =>
    coherentCubeHomotopyMap_boundary H₀ H₁ hface hconst p 1 u hu⟩

private theorem HigherHurewicz.CubeGluing.coherentCubeEndpoint_cell {n : ℕ} {X : Type}
    [TopologicalSpace X] {x : X}
    (H₀ : C(FirstHurewicz.Simplex n, X) → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (H₁ :
      C(FirstHurewicz.Simplex (n + 1), X) → C((unitInterval) × FirstHurewicz.Simplex (n + 1), X))
    (hface : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies n H₀ H₁)
    (hconst :
      H₀ (ContinuousMap.const (FirstHurewicz.Simplex n) x) =
        ContinuousMap.const ((unitInterval) × FirstHurewicz.Simplex n) x)
    (p : GenLoop (Fin (n + 1)) X x) (e : Equiv.Perm (Fin (n + 1))) :
    (coherentCubeEndpoint H₀ H₁ hface hconst p).val.comp
        (HigherHurewicz.CubeTriangulation.cubeSimplex e) =
      SecondHurewicz.SimplyConnected.timeSlice
        (H₁ (p.val.comp (HigherHurewicz.CubeTriangulation.cubeSimplex e))) 1 := by
  ext s
  exact coherentCubeHomotopyMap_cell H₀ H₁ hface p e 1 s

private def
    HigherHurewicz.CubeGluing.coherentCubeHomotopy {n : ℕ} {X : Type} [TopologicalSpace X] {x : X}
    (H₀ : C(FirstHurewicz.Simplex n, X) → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (H₁ :
      C(FirstHurewicz.Simplex (n + 1), X) → C((unitInterval) × FirstHurewicz.Simplex (n + 1), X))
    (hface : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies n H₀ H₁)
    (hconst :
      H₀ (ContinuousMap.const (FirstHurewicz.Simplex n) x) =
        ContinuousMap.const ((unitInterval) × FirstHurewicz.Simplex n) x)
    (hzero :
      ∀ (smp : C(FirstHurewicz.Simplex (n + 1), X)) (s : FirstHurewicz.Simplex (n + 1)),
        H₁ smp (0, s) = smp s)
    (p : GenLoop (Fin (n + 1)) X x) :
    p.val.HomotopyRel (coherentCubeEndpoint H₀ H₁ hface hconst p).val
      (Cube.boundary (Fin (n + 1)))
    where
  toHomotopy :=
    { toContinuousMap := coherentCubeHomotopyMap H₀ H₁ hface p
      map_zero_left := coherentCubeHomotopyMap_zero H₀ H₁ hface hzero p
      map_one_left _ := rfl }
  prop' r u
    hu :=
    (coherentCubeHomotopyMap_boundary H₀ H₁ hface hconst p r u hu).trans
      (GenLoop.boundary p u hu).symm

private theorem
    HigherHurewicz.simplex_coordinate_zero_of_tail_eq {n : ℕ} (s : FirstHurewicz.Simplex n)
    {i j : Fin n} (hij : i < j)
    (h :
      (∑ k : Fin (n + 1), if i.val < k.val then s k else 0) =
        ∑ k : Fin (n + 1), if j.val < k.val then s k else 0) :
    s i.succ = 0 := by
  classical
  let A := Finset.univ.filter (fun k : Fin (n + 1) => i.val < k.val)
  let B := Finset.univ.filter (fun k : Fin (n + 1) => j.val < k.val)
  have hAB : (∑ k ∈ A, s k) = ∑ k ∈ B, s k := by simpa only [A, B, Finset.sum_filter] using h
  have hiB : i.succ ∉ B := by
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_succ, not_lt]
    exact hij
  have hsub : Insert.insert i.succ B ⊆ A := by
    intro k hk
    rcases Finset.mem_insert.mp hk with hk | hk
    · subst k
      simp [A]
    · have hjk : j.val < k.val := (Finset.mem_filter.mp hk).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_trans hij hjk⟩
  have hle : s i.succ + ∑ k ∈ B, s k ≤ ∑ k ∈ A, s k := by
    calc
      s i.succ + ∑ k ∈ B, s k = ∑ k ∈ Insert.insert i.succ B, s k := (Finset.sum_insert hiB).symm
      _ ≤ ∑ k ∈ A, s k :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => stdSimplex.zero_le s k)
  exact le_antisymm (by linarith) (stdSimplex.zero_le s i.succ)

private theorem HigherHurewicz.cubeSimplex_ordered_coordinate_equality_boundary {n : ℕ}
    (e : Equiv.Perm (Fin n)) (s : FirstHurewicz.Simplex n) {i j : Fin n} (hij : i ≠ j)
    (h : CubeTriangulation.cubeSimplex e s (e i) = CubeTriangulation.cubeSimplex e s (e j)) :
    s ∈ SecondHurewicz.SimplyConnected.simplexBoundary n := by
  have hreal := congrArg (fun t : (unitInterval) => (t : ℝ)) h
  rw [CubeTriangulation.cubeSimplex_coordinate, CubeTriangulation.cubeSimplex_coordinate] at hreal
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact ⟨i.succ, simplex_coordinate_zero_of_tail_eq s hlt hreal⟩
  · exact ⟨j.succ, simplex_coordinate_zero_of_tail_eq s hgt hreal.symm⟩

private theorem
    HigherHurewicz.cubeSimplex_coordinate_equality_boundary {n : ℕ} (e : Equiv.Perm (Fin n))
    (s : FirstHurewicz.Simplex n) {i j : Fin n} (hij : i ≠ j)
    (h : CubeTriangulation.cubeSimplex e s i = CubeTriangulation.cubeSimplex e s j) :
    s ∈ SecondHurewicz.SimplyConnected.simplexBoundary n := by
  apply cubeSimplex_ordered_coordinate_equality_boundary e s (e.symm.injective.ne hij)
  simpa only [Equiv.apply_symm_apply] using h

private theorem
    HigherHurewicz.coherentCubeEndpoint_cell_boundary {n : ℕ} {X : Type} [TopologicalSpace X]
    {x : X}
    (H : FirstHurewicz.SingularSimplex X n → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (H' :
      FirstHurewicz.SingularSimplex X (n + 1) →
        C((unitInterval) × FirstHurewicz.Simplex (n + 1), X))
    (hface : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies n H H')
    (hconst :
      H (ContinuousMap.const (FirstHurewicz.Simplex n) x) =
        ContinuousMap.const ((unitInterval) × FirstHurewicz.Simplex n) x)
    (hone :
      ∀ smp,
        SecondHurewicz.SimplyConnected.timeSlice (H smp) 1 =
          ContinuousMap.const (FirstHurewicz.Simplex n) x)
    (p : GenLoop (Fin (n + 1)) X x) (e : Equiv.Perm (Fin (n + 1)))
    (s : FirstHurewicz.Simplex (n + 1))
    (hs : s ∈ SecondHurewicz.SimplyConnected.simplexBoundary (n + 1)) :
    CubeGluing.coherentCubeEndpoint H H' hface hconst p (CubeTriangulation.cubeSimplex e s) = x :=
  by
  have he :=
    congrArg (fun f : C(FirstHurewicz.Simplex (n + 1), X) => f s)
      (CubeGluing.coherentCubeEndpoint_cell H H' hface hconst p e)
  exact he.trans (simplexEndpoint_boundary H H' hface x hone _ s hs)

private theorem
    HigherHurewicz.coherentCubeEndpoint_internalBased {n : ℕ} {X : Type} [TopologicalSpace X]
    {x : X}
    (H : FirstHurewicz.SingularSimplex X n → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (H' :
      FirstHurewicz.SingularSimplex X (n + 1) →
        C((unitInterval) × FirstHurewicz.Simplex (n + 1), X))
    (hface : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies n H H')
    (hconst :
      H (ContinuousMap.const (FirstHurewicz.Simplex n) x) =
        ContinuousMap.const ((unitInterval) × FirstHurewicz.Simplex n) x)
    (hone :
      ∀ smp,
        SecondHurewicz.SimplyConnected.timeSlice (H smp) 1 =
          ContinuousMap.const (FirstHurewicz.Simplex n) x)
    (p : GenLoop (Fin (n + 1)) X x) (u : Fin (n + 1) → (unitInterval)) (i j : Fin (n + 1))
    (hij : i ≠ j) (hu : u i = u j) : CubeGluing.coherentCubeEndpoint H H' hface hconst p u = x := by
  obtain ⟨e, s, rfl⟩ := CubeTriangulation.exists_cubeSimplex u
  exact
    coherentCubeEndpoint_cell_boundary H H' hface hconst hone p e s
      (cubeSimplex_coordinate_equality_boundary e s hij hu)

private def
    FourthHurewicz.normalizedCube {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)] (p : GenLoop (Fin 4) X x) :
    GenLoop (Fin 4) X x :=
  HigherHurewicz.CubeGluing.coherentCubeEndpoint (normalizationThreeSimplexHomotopy x)
    (normalizationFourSimplexHomotopy x) (normalizationHomotopy_face x)
    (normalizationThreeSimplexHomotopy_const x) p

private theorem FourthHurewicz.normalizedCube_cell {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    (p : GenLoop (Fin 4) X x) (e : Equiv.Perm (Fin 4)) :
    (normalizedCube x p).val.comp (HigherHurewicz.CubeTriangulation.cubeSimplex e) =
      (normalizedFourSimplex x
          (p.val.comp (HigherHurewicz.CubeTriangulation.cubeSimplex e))).val :=
  HigherHurewicz.CubeGluing.coherentCubeEndpoint_cell (normalizationThreeSimplexHomotopy x)
    (normalizationFourSimplexHomotopy x) (normalizationHomotopy_face x)
    (normalizationThreeSimplexHomotopy_const x) p e

private def FourthHurewicz.normalizationCubeHomotopy {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    (p : GenLoop (Fin 4) X x) :
    p.val.HomotopyRel (normalizedCube x p).val (Cube.boundary (Fin 4)) :=
  HigherHurewicz.CubeGluing.coherentCubeHomotopy (normalizationThreeSimplexHomotopy x)
    (normalizationFourSimplexHomotopy x) (normalizationHomotopy_face x)
    (normalizationThreeSimplexHomotopy_const x) (normalizationFourSimplexHomotopy_zero x) p

private theorem FourthHurewicz.normalizedCube_internalBased {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    (p : GenLoop (Fin 4) X x) (u : Fin 4 → (unitInterval)) (i j : Fin 4) (hij : i ≠ j)
    (hu : u i = u j) : normalizedCube x p u = x :=
  HigherHurewicz.coherentCubeEndpoint_internalBased (normalizationThreeSimplexHomotopy x)
    (normalizationFourSimplexHomotopy x) (normalizationHomotopy_face x)
    (normalizationThreeSimplexHomotopy_const x) (normalizationThreeSimplexHomotopy_endpoint x) p u
    i j hij hu

private theorem HigherHurewicz.CubeTriangulation.cubeSimplex_simplexBoundary {n : ℕ}
    (e : Equiv.Perm (Fin (n + 1))) (s : FirstHurewicz.Simplex (n + 1))
    (hs : s ∈ SecondHurewicz.SimplyConnected.simplexBoundary (n + 1)) :
    cubeSimplex e s ∈ Cube.boundary (Fin (n + 1)) ∨
      ∃ i j : Fin (n + 1), i ≠ j ∧ cubeSimplex e s i = cubeSimplex e s j := by
  obtain ⟨k, hk⟩ := hs
  cases k using Fin.cases with
  | zero => exact Or.inl ((cubeSimplex_mem_boundary_iff e s).mpr (Or.inl hk))
  | succ k =>
    cases k using Fin.lastCases with
    | last =>
      apply Or.inl
      apply (cubeSimplex_mem_boundary_iff e s).mpr
      exact Or.inr (by simpa only [Fin.succ_last] using hk)
    | cast i =>
      apply Or.inr
      refine ⟨e i.castSucc, e i.succ, ?_, ?_⟩
      · intro h
        have hval := congrArg Fin.val (e.injective h)
        simp only [Fin.val_castSucc, Fin.val_succ] at hval
        omega
      · apply (cubeSimplex_tie_iff e s i).mpr
        simpa only [Fin.castSucc_succ] using hk

private def
    HigherHurewicz.NativeSubdivision.nativeCubeSimplexQuotient {n : ℕ} (e : Equiv.Perm (Fin n)) :
    C(NativeCube (Fin n), NativeCube (Fin n)) :=
  (HigherHurewicz.CubeTriangulation.cubeSimplex e).comp
    (HigherHurewicz.SimplexGeometry.simplexQuotient n)

private theorem
    HigherHurewicz.NativeSubdivision.nativeCubeSimplex_based {X : Type*} [TopologicalSpace X]
    {x : X} {n : ℕ} (p : GenLoop (Fin n) X x) (hp : NativeCubeInternalBased p)
    (e : Equiv.Perm (Fin n)) (s : FirstHurewicz.Simplex n)
    (hs : s ∈ SecondHurewicz.SimplyConnected.simplexBoundary n) :
    p (HigherHurewicz.CubeTriangulation.cubeSimplex e s) = x := by
  cases n with
  | zero =>
    obtain ⟨i, hi⟩ := hs
    have hi0 : i = 0 := Fin.ext (by omega)
    subst i
    have hsum : s 0 = 1 := by
      simpa only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] using stdSimplex.sum_eq_one s
    exact False.elim (by linarith)
  | succ
    n =>
    rcases HigherHurewicz.CubeTriangulation.cubeSimplex_simplexBoundary e s hs with h |
      ⟨i, j, hij, h⟩
    · exact p.property _ h
    · exact hp _ i j hij h

private def HigherHurewicz.NativeSubdivision.nativeBasedCubeSimplex {X : Type*} [TopologicalSpace X]
    {x : X} {n : ℕ} (p : GenLoop (Fin n) X x) (hp : NativeCubeInternalBased p)
    (e : Equiv.Perm (Fin n)) : HigherHurewicz.SimplexGeometry.BasedSimplex n x :=
  ⟨p.val.comp (HigherHurewicz.CubeTriangulation.cubeSimplex e), nativeCubeSimplex_based p hp e⟩

private theorem HigherHurewicz.NativeSubdivision.nativeCubeSimplexQuotient_based {X : Type*}
    [TopologicalSpace X] {x : X} {n : ℕ} (p : GenLoop (Fin n) X x)
    (hp : NativeCubeInternalBased p) (e : Equiv.Perm (Fin n)) (u : NativeCube (Fin n))
    (hu : u ∈ Cube.boundary (Fin n)) : p (nativeCubeSimplexQuotient e u) = x :=
  nativeCubeSimplex_based p hp e _ (HigherHurewicz.SimplexGeometry.simplexQuotient_boundary u hu)

private theorem FourthHurewicz.normalizedCube_simplex {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    (p : GenLoop (Fin 4) X x) (e : Equiv.Perm (Fin 4)) :
    HigherHurewicz.NativeSubdivision.nativeBasedCubeSimplex (normalizedCube x p)
        (normalizedCube_internalBased x p) e =
      normalizedFourSimplex x (p.val.comp (HigherHurewicz.CubeTriangulation.cubeSimplex e)) := by
  apply Subtype.ext
  exact normalizedCube_cell x p e

private theorem
    FourthHurewicz.fourSimplexClassOperator_cubeChain_sum {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    (p : GenLoop (Fin 4) X x) :
    fourSimplexClassOperator x (cubeChain p) =
      ∑ e : Equiv.Perm (Fin 4),
        HigherHurewicz.CubeTriangulation.cubeOrientation e •
          basedFourSimplexClass
            (normalizedFourSimplex x
              (p.val.comp (HigherHurewicz.CubeTriangulation.cubeSimplex e))) := by
  rw [CubeSubdivision.cubeChain_eq_sum_simplices, map_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [map_zsmul, fourSimplexClassOperator_simplex]

private def HigherHurewicz.NativeSubdivision.insertPermutation {n : ℕ} (e : Equiv.Perm (Fin n))
    (r : Fin (n + 1)) : Equiv.Perm (Fin (n + 1)) :=
  (finSuccEquiv' r).trans (e.optionCongr.trans finSuccEquivLast.symm)

@[simp]
private theorem HigherHurewicz.NativeSubdivision.insertPermutation_apply_at {n : ℕ}
    (e : Equiv.Perm (Fin n)) (r : Fin (n + 1)) : insertPermutation e r r = Fin.last n := by
  simp [insertPermutation]

@[simp]
private theorem HigherHurewicz.NativeSubdivision.insertPermutation_apply_succAbove {n : ℕ}
    (e : Equiv.Perm (Fin n)) (r : Fin (n + 1)) (j : Fin n) :
    insertPermutation e r (r.succAbove j) = (e j).castSucc := by simp [insertPermutation]

@[simp]
private theorem HigherHurewicz.NativeSubdivision.insertPermutation_symm_last {n : ℕ}
    (e : Equiv.Perm (Fin n)) (r : Fin (n + 1)) : (insertPermutation e r).symm (Fin.last n) = r := by
  apply (insertPermutation e r).injective
  simp

private theorem HigherHurewicz.NativeSubdivision.insertPermutation_pair_injective {n : ℕ} :
    Function.Injective
      (fun er : Equiv.Perm (Fin n) × Fin (n + 1) => insertPermutation er.1 er.2) := by
  rintro ⟨e, r⟩ ⟨f, s⟩ h
  have hrs : r = s := by
    simpa using congrArg (fun E : Equiv.Perm (Fin (n + 1)) => E.symm (Fin.last n)) h
  subst s
  have hef : e = f := by
    apply Equiv.ext
    intro j
    apply Fin.castSucc_injective n
    simpa using congrArg (fun E : Equiv.Perm (Fin (n + 1)) => E (r.succAbove j)) h
  exact congrArg (fun e : Equiv.Perm (Fin n) => (e, r)) hef

private theorem HigherHurewicz.NativeSubdivision.optionCongr_removeNone_of_none {α β : Type*}
    (e : Option α ≃ Option β) (h : e Option.none = Option.none) : e.removeNone.optionCongr = e := by
  apply Equiv.ext
  intro a
  cases a with
  | none => simpa using h.symm
  | some a =>
    change Option.some (e.removeNone a) = e (Option.some a)
    cases ha : e (Option.some a) with
    | none =>
      have : Option.some a = Option.none := e.injective (ha.trans h.symm)
      cases this
    | some b => simpa only [ha] using e.removeNone_some ⟨b, ha⟩

private def HigherHurewicz.NativeSubdivision.deletePermutationOption {n : ℕ}
    (E : Equiv.Perm (Fin (n + 1))) : Equiv.Perm (Option (Fin n)) :=
  (finSuccEquiv' (E.symm (Fin.last n))).symm.trans (E.trans finSuccEquivLast)

@[simp]
private theorem HigherHurewicz.NativeSubdivision.deletePermutationOption_none {n : ℕ}
    (E : Equiv.Perm (Fin (n + 1))) : deletePermutationOption E Option.none = Option.none := by
  simp [deletePermutationOption]

private def
    HigherHurewicz.NativeSubdivision.deletePermutation {n : ℕ} (E : Equiv.Perm (Fin (n + 1))) :
    Equiv.Perm (Fin n) :=
  (deletePermutationOption E).removeNone

private theorem HigherHurewicz.NativeSubdivision.deletePermutation_castSucc {n : ℕ}
    (E : Equiv.Perm (Fin (n + 1))) (j : Fin n) :
    (deletePermutation E j).castSucc = E ((E.symm (Fin.last n)).succAbove j) := by
  have h :=
    congrArg (fun e : Equiv.Perm (Option (Fin n)) => e (Option.some j))
      (optionCongr_removeNone_of_none (deletePermutationOption E)
        (deletePermutationOption_none E))
  have h' := congrArg finSuccEquivLast.symm h
  simpa only [deletePermutation, Equiv.optionCongr_apply, Option.map_some,
    finSuccEquivLast_symm_some, deletePermutationOption, Equiv.trans_apply,
    finSuccEquiv'_symm_some, Equiv.symm_apply_apply] using h'

@[simp]
private theorem HigherHurewicz.NativeSubdivision.insertPermutation_deletePermutation {n : ℕ}
    (E : Equiv.Perm (Fin (n + 1))) :
    insertPermutation (deletePermutation E) (E.symm (Fin.last n)) = E := by
  ext i
  refine Fin.succAboveCases (E.symm (Fin.last n)) ?_ (fun j => ?_) i
  · simp
  · rw [insertPermutation_apply_succAbove, deletePermutation_castSucc]

private def HigherHurewicz.NativeSubdivision.insertPermutationEquiv (n : ℕ) :
    (Equiv.Perm (Fin n) × Fin (n + 1)) ≃ Equiv.Perm (Fin (n + 1))
    where
  toFun er := insertPermutation er.1 er.2
  invFun E := (deletePermutation E, E.symm (Fin.last n))
  left_inv
    er :=
    insertPermutation_pair_injective
      (insertPermutation_deletePermutation (insertPermutation er.1 er.2))
  right_inv := insertPermutation_deletePermutation

private theorem HigherHurewicz.NativeSubdivision.sum_insertPermutation {n : ℕ} {A : Type*}
    [AddCommMonoid A] (F : Equiv.Perm (Fin (n + 1)) → A) :
    ∑ E, F E = ∑ e : Equiv.Perm (Fin n), ∑ r : Fin (n + 1), F (insertPermutation e r) := by
  rw [← (insertPermutationEquiv n).sum_comp F, Fintype.sum_prod_type]
  rfl

private structure HigherHurewicz.NativeSubdivision.NativeChamberChart {n : ℕ}
    (e : Equiv.Perm (Fin n)) where
  toContinuousMap : C(NativeCube (Fin n), NativeCube (Fin n))
  zero_last : ∀ u i, i.val + 1 = n → u (e i) = 0 → toContinuousMap u (e i) = 0
  zero_adjacent :
    ∀ u i j, i.val + 1 = j.val → u (e i) = 0 → toContinuousMap u (e i) = toContinuousMap u (e j)
  one_first : ∀ u i, i.val = 0 → u (e i) = 1 → toContinuousMap u (e i) = 1
  one_adjacent :
    ∀ u i j, j.val + 1 = i.val → u (e i) = 1 → toContinuousMap u (e i) = toContinuousMap u (e j)

private def HigherHurewicz.NativeSubdivision.chamberLower {n : ℕ} (e : Equiv.Perm (Fin n))
    (r : Fin (n + 1)) (chart : NativeChamberChart e) : C(NativeCube (Fin n), (unitInterval)) :=
  if h : r.val < n then (ContinuousMap.eval (e ⟨r.val, h⟩)).comp chart.toContinuousMap
  else ContinuousMap.const _ 0

private def HigherHurewicz.NativeSubdivision.chamberUpper {n : ℕ} (e : Equiv.Perm (Fin n))
    (r : Fin (n + 1)) (chart : NativeChamberChart e) : C(NativeCube (Fin n), (unitInterval)) :=
  if h : 0 < r.val then (ContinuousMap.eval (e ⟨r.val - 1, by omega⟩)).comp chart.toContinuousMap
  else ContinuousMap.const _ 1

private theorem
    HigherHurewicz.NativeSubdivision.chamberLower_of_rank {n : ℕ} (e : Equiv.Perm (Fin n))
    (r : Fin (n + 1)) (chart : NativeChamberChart e) (u : NativeCube (Fin n)) (k : Fin n)
    (h : r.val = k.val) : chamberLower e r chart u = chart.toContinuousMap u (e k) := by
  have hr : r.val < n := h ▸ k.isLt
  have hk : (⟨r.val, hr⟩ : Fin n) = k := Fin.ext h
  simp [chamberLower, hr, hk]

private theorem HigherHurewicz.NativeSubdivision.chamberLower_last {n : ℕ} (e : Equiv.Perm (Fin n))
    (r : Fin (n + 1)) (chart : NativeChamberChart e) (u : NativeCube (Fin n)) (h : r.val = n) :
    chamberLower e r chart u = 0 := by simp [chamberLower, h]

private theorem
    HigherHurewicz.NativeSubdivision.chamberUpper_of_rank {n : ℕ} (e : Equiv.Perm (Fin n))
    (r : Fin (n + 1)) (chart : NativeChamberChart e) (u : NativeCube (Fin n)) (k : Fin n)
    (h : r.val = k.val + 1) : chamberUpper e r chart u = chart.toContinuousMap u (e k) := by
  have hr : 0 < r.val := by omega
  have hk : (⟨r.val - 1, by omega⟩ : Fin n) = k := Fin.ext (by dsimp; omega)
  simp [chamberUpper, hr, hk]

private theorem HigherHurewicz.NativeSubdivision.chamberUpper_first {n : ℕ} (e : Equiv.Perm (Fin n))
    (r : Fin (n + 1)) (chart : NativeChamberChart e) (u : NativeCube (Fin n)) (h : r.val = 0) :
    chamberUpper e r chart u = 1 := by simp [chamberUpper, h]

private theorem
    HigherHurewicz.NativeSubdivision.chamberLower_zero_face {n : ℕ} (e : Equiv.Perm (Fin n))
    (r : Fin (n + 1)) (chart : NativeChamberChart e) (u : NativeCube (Fin n)) (k : Fin n)
    (h : r.val = k.val + 1) (hu : u (e k) = 0) :
    chamberLower e r chart u = chart.toContinuousMap u (e k) := by
  by_cases hr : r.val < n
  · let j : Fin n := ⟨r.val, hr⟩
    rw [chamberLower_of_rank e r chart u j rfl]
    exact (chart.zero_adjacent u k j (by simpa [j] using h.symm) hu).symm
  · have hn : r.val = n := by omega
    rw [chamberLower_last e r chart u hn]
    exact (chart.zero_last u k (by omega) hu).symm

private theorem
    HigherHurewicz.NativeSubdivision.chamberUpper_one_face {n : ℕ} (e : Equiv.Perm (Fin n))
    (r : Fin (n + 1)) (chart : NativeChamberChart e) (u : NativeCube (Fin n)) (k : Fin n)
    (h : r.val = k.val) (hu : u (e k) = 1) :
    chamberUpper e r chart u = chart.toContinuousMap u (e k) := by
  by_cases hr : 0 < r.val
  · let j : Fin n := ⟨r.val - 1, by omega⟩
    rw [chamberUpper_of_rank e r chart u j (by dsimp [j]; omega)]
    exact (chart.one_adjacent u k j (by dsimp [j]; omega) hu).symm
  · have hz : r.val = 0 := by omega
    rw [chamberUpper_first e r chart u hz]
    exact (chart.one_first u k (by omega) hu).symm

private def HigherHurewicz.NativeSubdivision.chamberOldCoordinates {n : ℕ} :
    C(NativeCube (Fin (n + 1)), NativeCube (Fin n))
    where
  toFun u k := u k.castSucc
  continuous_toFun := continuous_pi fun _ => continuous_apply _

private def HigherHurewicz.NativeSubdivision.insertChamberMap {n : ℕ} (e : Equiv.Perm (Fin n))
    (r : Fin (n + 1)) (chart : NativeChamberChart e) :
    C(NativeCube (Fin (n + 1)), NativeCube (Fin (n + 1)))
    where
  toFun
    u :=
    Fin.lastCases
      (Set.Icc.convexComb (chamberLower e r chart (chamberOldCoordinates u))
        (chamberUpper e r chart (chamberOldCoordinates u)) (u (Fin.last n)))
      (chart.toContinuousMap (chamberOldCoordinates u))
  continuous_toFun := by
    apply continuous_pi
    intro k
    refine Fin.lastCases ?_ (fun j => ?_) k
    · simp only [Fin.lastCases_last]
      exact
        Set.Icc.continuous_convexComb_prod.comp
          (((chamberLower e r chart).continuous.comp chamberOldCoordinates.continuous).prodMk
            (((chamberUpper e r chart).continuous.comp chamberOldCoordinates.continuous).prodMk
              (continuous_apply (Fin.last n))))
    · simp only [Fin.lastCases_castSucc]
      exact
        (continuous_apply j).comp
          (chart.toContinuousMap.continuous.comp chamberOldCoordinates.continuous)

@[simp]
private theorem HigherHurewicz.NativeSubdivision.insertChamberMap_apply_castSucc {n : ℕ}
    (e : Equiv.Perm (Fin n)) (r : Fin (n + 1)) (chart : NativeChamberChart e)
    (u : NativeCube (Fin (n + 1))) (k : Fin n) :
    insertChamberMap e r chart u k.castSucc = chart.toContinuousMap (chamberOldCoordinates u) k :=
  by simp [insertChamberMap]

@[simp]
private theorem HigherHurewicz.NativeSubdivision.insertChamberMap_apply_last {n : ℕ}
    (e : Equiv.Perm (Fin n)) (r : Fin (n + 1)) (chart : NativeChamberChart e)
    (u : NativeCube (Fin (n + 1))) :
    insertChamberMap e r chart u (Fin.last n) =
      Set.Icc.convexComb (chamberLower e r chart (chamberOldCoordinates u))
        (chamberUpper e r chart (chamberOldCoordinates u)) (u (Fin.last n)) := by
  simp [insertChamberMap]

private theorem
    HigherHurewicz.NativeSubdivision.chamberSuccAbove_val_cases {n : ℕ} (r : Fin (n + 1))
    (i : Fin n) :
    ((r.succAbove i).val = i.val ∧ i.val < r.val) ∨
      ((r.succAbove i).val = i.val + 1 ∧ r.val ≤ i.val) := by
  by_cases h : i.castSucc < r
  · exact Or.inl ⟨congrArg Fin.val (Fin.succAbove_of_castSucc_lt r i h), h⟩
  · exact
      Or.inr
        ⟨congrArg Fin.val (Fin.succAbove_of_le_castSucc r i (le_of_not_gt h)), le_of_not_gt h⟩

private theorem HigherHurewicz.NativeSubdivision.chamberUpper_succ_eq_lower_castSucc {m : ℕ}
    (e : Equiv.Perm (Fin m)) (chart : NativeChamberChart e) (j : Fin m) (u : NativeCube (Fin m)) :
    chamberUpper e j.succ chart u = chamberLower e j.castSucc chart u := by
  rw [chamberUpper_of_rank e j.succ chart u j rfl,
    chamberLower_of_rank e j.castSucc chart u j rfl]

private def HigherHurewicz.NativeSubdivision.chamberCutSequence {m : ℕ} (e : Equiv.Perm (Fin m))
    (chart : NativeChamberChart e) : Fin (m + 2) → C(NativeCube (Fin m), (unitInterval)) :=
  Fin.cons (ContinuousMap.const _ 0) (fun j : Fin (m + 1) => chamberUpper e j.rev chart)

private theorem
    HigherHurewicz.NativeSubdivision.chamberCutSequence_succ {m : ℕ} (e : Equiv.Perm (Fin m))
    (chart : NativeChamberChart e) (j : Fin (m + 1)) (u : NativeCube (Fin m)) :
    chamberCutSequence e chart j.succ u = chamberUpper e j.rev chart u := by
  simp [chamberCutSequence]

@[simp]
private theorem
    HigherHurewicz.NativeSubdivision.chamberCutSequence_last {m : ℕ} (e : Equiv.Perm (Fin m))
    (chart : NativeChamberChart e) (u : NativeCube (Fin m)) :
    chamberCutSequence e chart (Fin.last (m + 1)) u = 1 := by
  change chamberUpper e (Fin.last m).rev chart u = 1
  rw [Fin.rev_last]
  exact chamberUpper_first e 0 chart u rfl

private theorem HigherHurewicz.NativeSubdivision.chamberCutSequence_castSucc {m : ℕ}
    (e : Equiv.Perm (Fin m)) (chart : NativeChamberChart e) (j : Fin (m + 1))
    (u : NativeCube (Fin m)) :
    chamberCutSequence e chart j.castSucc u = chamberLower e j.rev chart u := by
  refine Fin.cases ?_ (fun k => ?_) j
  · change 0 = chamberLower e (0 : Fin (m + 1)).rev chart u
    rw [Fin.rev_zero]
    exact (chamberLower_last e (Fin.last m) chart u rfl).symm
  · change chamberUpper e k.castSucc.rev chart u = chamberLower e k.succ.rev chart u
    rw [Fin.rev_castSucc, Fin.rev_succ]
    exact chamberUpper_succ_eq_lower_castSucc e chart k.rev u

private theorem
    HigherHurewicz.NativeSubdivision.chamberCuts_sum_rev {m : ℕ} {A : Type*} [AddCommMonoid A]
    (f : Fin (m + 1) → A) : ∑ j : Fin (m + 1), f j.rev = ∑ j : Fin (m + 1), f j :=
  Equiv.sum_comp Fin.revPerm f

private def HigherHurewicz.NativeSubdivision.cubeRestriction {m n : ℕ} (h : m ≤ n) :
    C(NativeCube (Fin n), NativeCube (Fin m))
    where
  toFun u i := u (Fin.castLE h i)
  continuous_toFun := continuous_pi fun i => continuous_apply (Fin.castLE h i)

@[simp]
private theorem HigherHurewicz.NativeSubdivision.cubeRestriction_apply {m n : ℕ} (h : m ≤ n)
    (u : NativeCube (Fin n)) (i : Fin m) : cubeRestriction h u i = u (Fin.castLE h i) :=
  rfl

private def HigherHurewicz.NativeSubdivision.extendCubeMap {m n : ℕ} (h : m ≤ n)
    (f : C(NativeCube (Fin m), NativeCube (Fin m))) : C(NativeCube (Fin n), NativeCube (Fin n))
    where
  toFun u i := if hi : i.val < m then f (cubeRestriction h u) ⟨i.val, hi⟩ else u i
  continuous_toFun := by
    apply continuous_pi
    intro i
    by_cases hi : i.val < m
    · simp only [dite_eq_left hi]
      exact (continuous_apply ⟨i.val, hi⟩).comp (f.continuous.comp (cubeRestriction h).continuous)
    · simpa only [dite_eq_right hi] using
        (continuous_apply i : Continuous fun u : NativeCube (Fin n) => u i)

@[simp]
private theorem HigherHurewicz.NativeSubdivision.extendCubeMap_castLE {m n : ℕ} (h : m ≤ n)
    (f : C(NativeCube (Fin m), NativeCube (Fin m))) (u : NativeCube (Fin n)) (i : Fin m) :
    extendCubeMap h f u (Fin.castLE h i) = f (cubeRestriction h u) i := by simp [extendCubeMap]

private theorem HigherHurewicz.NativeSubdivision.extendCubeMap_outside {m n : ℕ} (h : m ≤ n)
    (f : C(NativeCube (Fin m), NativeCube (Fin m))) (u : NativeCube (Fin n)) (i : Fin n)
    (hi : m ≤ i.val) : extendCubeMap h f u i = u i := by simp [extendCubeMap, Nat.not_lt.mpr hi]

private theorem
    HigherHurewicz.NativeSubdivision.cubeRestriction_update_outside {m n : ℕ} (h : m ≤ n)
    (u : NativeCube (Fin n)) (i : Fin n) (hi : m ≤ i.val) (v : (unitInterval)) :
    cubeRestriction h (Function.update u i v) = cubeRestriction h u := by
  funext j
  apply Function.update_of_ne
  intro heq
  have hv := congrArg Fin.val heq
  exact (Nat.not_lt.mpr hi) (hv ▸ j.isLt)

private theorem HigherHurewicz.NativeSubdivision.extendCubeMap_update_outside {m n : ℕ} (h : m ≤ n)
    (f : C(NativeCube (Fin m), NativeCube (Fin m))) (u : NativeCube (Fin n)) (i : Fin n)
    (hi : m ≤ i.val) (v : (unitInterval)) :
    extendCubeMap h f (Function.update u i v) = Function.update (extendCubeMap h f u) i v := by
  funext j
  by_cases hj : j = i
  · subst j
    simp [extendCubeMap_outside h f _ i hi]
  · rw [Function.update_of_ne hj]
    by_cases hjm : j.val < m
    · simp only [extendCubeMap, ContinuousMap.coe_mk, dite_eq_left hjm]
      rw [cubeRestriction_update_outside h u i hi v]
    · rw [extendCubeMap_outside h f _ j (Nat.le_of_not_gt hjm),
        extendCubeMap_outside h f _ j (Nat.le_of_not_gt hjm), Function.update_of_ne hj]

@[simp]
private theorem HigherHurewicz.NativeSubdivision.extendCubeMap_refl {n : ℕ}
    (f : C(NativeCube (Fin n), NativeCube (Fin n))) : extendCubeMap (le_refl n) f = f := by
  ext u i
  simp [cubeRestriction, extendCubeMap]

@[simp]
private theorem HigherHurewicz.NativeSubdivision.extendCubeMap_zero {n : ℕ} (h : 0 ≤ n)
    (f : C(NativeCube (Fin 0), NativeCube (Fin 0))) : extendCubeMap h f = ContinuousMap.id _ := by
  apply ContinuousMap.ext
  intro u
  funext i
  exact extendCubeMap_outside h f u i (Nat.zero_le _)

private theorem HigherHurewicz.NativeSubdivision.extendCubeMap_sameFlat {m n : ℕ} (h : m ≤ n)
    (f g : C(NativeCube (Fin m), NativeCube (Fin m))) (u : NativeCube (Fin n))
    (hfg : NativeCubeSameFlat (f (cubeRestriction h u)) (g (cubeRestriction h u))) :
    NativeCubeSameFlat (extendCubeMap h f u) (extendCubeMap h g u) := by
  cases hfg with
  | zero i hf hg => exact .zero (Fin.castLE h i) (by simpa using hf) (by simpa using hg)
  | one i hf hg => exact .one (Fin.castLE h i) (by simpa using hf) (by simpa using hg)
  | equal i j hij hf hg =>
    exact
      .equal (Fin.castLE h i) (Fin.castLE h j)
        (fun heq => hij (Fin.ext (congrArg (fun k : Fin n => k.val) heq))) (by simpa using hf)
        (by simpa using hg)

private theorem HigherHurewicz.NativeSubdivision.insertChamberMap_zero_last {n : ℕ}
    (e : Equiv.Perm (Fin n)) (r : Fin (n + 1)) (chart : NativeChamberChart e)
    (u : NativeCube (Fin (n + 1))) (i : Fin (n + 1)) (hi : i.val + 1 = n + 1)
    (hu : u (insertPermutation e r i) = 0) :
    insertChamberMap e r chart u (insertPermutation e r i) = 0 := by
  revert hi hu
  refine Fin.succAboveCases r ?_ (fun k => ?_) i
  · intro hi hu
    simp only [insertPermutation_apply_at] at hu ⊢
    rw [insertChamberMap_apply_last, hu, Set.Icc.convexComb_zero]
    exact chamberLower_last e r chart (chamberOldCoordinates u) (by omega)
  · intro hi hu
    have hk := chamberSuccAbove_val_cases r k
    simp only [insertPermutation_apply_succAbove, insertChamberMap_apply_castSucc] at hu ⊢
    exact chart.zero_last (chamberOldCoordinates u) k (by omega) hu

private theorem HigherHurewicz.NativeSubdivision.insertChamberMap_zero_adjacent {n : ℕ}
    (e : Equiv.Perm (Fin n)) (r : Fin (n + 1)) (chart : NativeChamberChart e)
    (u : NativeCube (Fin (n + 1))) (i j : Fin (n + 1)) (hij : i.val + 1 = j.val)
    (hu : u (insertPermutation e r i) = 0) :
    insertChamberMap e r chart u (insertPermutation e r i) =
      insertChamberMap e r chart u (insertPermutation e r j) := by
  revert hij hu
  refine Fin.succAboveCases r ?_ (fun k => ?_) i
  · refine Fin.succAboveCases r ?_ (fun l => ?_) j
    · intro hij
      omega
    · intro hij hu
      have hl := chamberSuccAbove_val_cases r l
      have hr : r.val = l.val := by omega
      simp only [insertPermutation_apply_at, insertPermutation_apply_succAbove,
        insertChamberMap_apply_last, insertChamberMap_apply_castSucc] at hu ⊢
      rw [hu, Set.Icc.convexComb_zero]
      exact chamberLower_of_rank e r chart (chamberOldCoordinates u) l hr
  · refine Fin.succAboveCases r ?_ (fun l => ?_) j
    · intro hij hu
      have hk := chamberSuccAbove_val_cases r k
      have hr : r.val = k.val + 1 := by omega
      simp only [insertPermutation_apply_at, insertPermutation_apply_succAbove,
        insertChamberMap_apply_last, insertChamberMap_apply_castSucc] at hu ⊢
      rw [chamberLower_zero_face e r chart (chamberOldCoordinates u) k hr hu,
        chamberUpper_of_rank e r chart (chamberOldCoordinates u) k hr]
      simp
    · intro hij hu
      have hk := chamberSuccAbove_val_cases r k
      have hl := chamberSuccAbove_val_cases r l
      have hkl : k.val + 1 = l.val := by omega
      simp only [insertPermutation_apply_succAbove, insertChamberMap_apply_castSucc] at hu ⊢
      exact chart.zero_adjacent (chamberOldCoordinates u) k l hkl hu

private theorem HigherHurewicz.NativeSubdivision.insertChamberMap_one_first {n : ℕ}
    (e : Equiv.Perm (Fin n)) (r : Fin (n + 1)) (chart : NativeChamberChart e)
    (u : NativeCube (Fin (n + 1))) (i : Fin (n + 1)) (hi : i.val = 0)
    (hu : u (insertPermutation e r i) = 1) :
    insertChamberMap e r chart u (insertPermutation e r i) = 1 := by
  revert hi hu
  refine Fin.succAboveCases r ?_ (fun k => ?_) i
  · intro hi hu
    simp only [insertPermutation_apply_at] at hu ⊢
    rw [insertChamberMap_apply_last, hu, Set.Icc.convexComb_one]
    exact chamberUpper_first e r chart (chamberOldCoordinates u) hi
  · intro hi hu
    have hk := chamberSuccAbove_val_cases r k
    simp only [insertPermutation_apply_succAbove, insertChamberMap_apply_castSucc] at hu ⊢
    exact chart.one_first (chamberOldCoordinates u) k (by omega) hu

private theorem HigherHurewicz.NativeSubdivision.insertChamberMap_one_adjacent {n : ℕ}
    (e : Equiv.Perm (Fin n)) (r : Fin (n + 1)) (chart : NativeChamberChart e)
    (u : NativeCube (Fin (n + 1))) (i j : Fin (n + 1)) (hij : j.val + 1 = i.val)
    (hu : u (insertPermutation e r i) = 1) :
    insertChamberMap e r chart u (insertPermutation e r i) =
      insertChamberMap e r chart u (insertPermutation e r j) := by
  revert hij hu
  refine Fin.succAboveCases r ?_ (fun k => ?_) i
  · refine Fin.succAboveCases r ?_ (fun l => ?_) j
    · intro hij
      omega
    · intro hij hu
      have hl := chamberSuccAbove_val_cases r l
      have hr : r.val = l.val + 1 := by omega
      simp only [insertPermutation_apply_at, insertPermutation_apply_succAbove,
        insertChamberMap_apply_last, insertChamberMap_apply_castSucc] at hu ⊢
      rw [hu, Set.Icc.convexComb_one]
      exact chamberUpper_of_rank e r chart (chamberOldCoordinates u) l hr
  · refine Fin.succAboveCases r ?_ (fun l => ?_) j
    · intro hij hu
      have hk := chamberSuccAbove_val_cases r k
      have hr : r.val = k.val := by omega
      simp only [insertPermutation_apply_at, insertPermutation_apply_succAbove,
        insertChamberMap_apply_last, insertChamberMap_apply_castSucc] at hu ⊢
      rw [chamberLower_of_rank e r chart (chamberOldCoordinates u) k hr,
        chamberUpper_one_face e r chart (chamberOldCoordinates u) k hr hu]
      simp
    · intro hij hu
      have hk := chamberSuccAbove_val_cases r k
      have hl := chamberSuccAbove_val_cases r l
      have hkl : l.val + 1 = k.val := by omega
      simp only [insertPermutation_apply_succAbove, insertChamberMap_apply_castSucc] at hu ⊢
      exact chart.one_adjacent (chamberOldCoordinates u) k l hkl hu

private def HigherHurewicz.NativeSubdivision.insertChamberChart {n : ℕ} (e : Equiv.Perm (Fin n))
    (r : Fin (n + 1)) (chart : NativeChamberChart e) : NativeChamberChart (insertPermutation e r)
    where
  toContinuousMap := insertChamberMap e r chart
  zero_last := insertChamberMap_zero_last e r chart
  zero_adjacent := insertChamberMap_zero_adjacent e r chart
  one_first := insertChamberMap_one_first e r chart
  one_adjacent := insertChamberMap_one_adjacent e r chart

@[ext]
private theorem
    HigherHurewicz.NativeSubdivision.NativeChamberChart.ext {n : ℕ} {e : Equiv.Perm (Fin n)}
    {f g : HigherHurewicz.NativeSubdivision.NativeChamberChart e}
    (h : f.toContinuousMap = g.toContinuousMap) : f = g := by
  cases f
  cases g
  cases h
  rfl

private def HigherHurewicz.NativeSubdivision.chamberCutIndex {m n : ℕ} (h : m + 1 ≤ n) : Fin n :=
  Fin.castLE h (Fin.last m)

private theorem HigherHurewicz.NativeSubdivision.chamberCutIndex_ne_castLE {m n : ℕ} (h : m + 1 ≤ n)
    (j : Fin m) : Fin.castLE (Nat.le_of_succ_le h) j ≠ chamberCutIndex h := by
  intro he
  have hv := congrArg Fin.val he
  exact (Nat.ne_of_lt j.isLt) hv

@[simp]
private theorem HigherHurewicz.NativeSubdivision.chamberOldCoordinates_cubeRestriction {m n : ℕ}
    (h : m + 1 ≤ n) (u : NativeCube (Fin n)) :
    chamberOldCoordinates (cubeRestriction h u) = cubeRestriction (Nat.le_of_succ_le h) u :=
  rfl

private theorem HigherHurewicz.NativeSubdivision.extend_insertChamberMap {m n : ℕ} (h : m + 1 ≤ n)
    (e : Equiv.Perm (Fin m)) (r : Fin (m + 1)) (chart : NativeChamberChart e)
    (u : NativeCube (Fin n)) :
    extendCubeMap h (insertChamberMap e r chart) u =
      Function.update (extendCubeMap (Nat.le_of_succ_le h) chart.toContinuousMap u)
        (chamberCutIndex h)
        (Set.Icc.convexComb (chamberLower e r chart (cubeRestriction (Nat.le_of_succ_le h) u))
          (chamberUpper e r chart (cubeRestriction (Nat.le_of_succ_le h) u))
          (u (chamberCutIndex h))) := by
  funext j
  by_cases hjm : j.val < m
  · let k : Fin m := ⟨j.val, hjm⟩
    have hk : Fin.castLE h k.castSucc = j := Fin.ext rfl
    have hk' : Fin.castLE h k.castSucc = Fin.castLE (Nat.le_of_succ_le h) k := Fin.ext rfl
    have hji : j ≠ chamberCutIndex h := by
      rw [← hk, hk']
      exact chamberCutIndex_ne_castLE h k
    rw [Function.update_of_ne hji, ← hk, extendCubeMap_castLE, insertChamberMap_apply_castSucc,
      chamberOldCoordinates_cubeRestriction, hk', extendCubeMap_castLE]
  · by_cases hji : j = chamberCutIndex h
    · subst j
      rw [Function.update_self]
      change extendCubeMap h (insertChamberMap e r chart) u (Fin.castLE h (Fin.last m)) = _
      rw [extendCubeMap_castLE, insertChamberMap_apply_last,
        chamberOldCoordinates_cubeRestriction]
      rfl
    · have hjval : j.val ≠ m := fun he => hji (Fin.ext he)
      have hmj : m + 1 ≤ j.val := by omega
      rw [extendCubeMap_outside h _ u j hmj, Function.update_of_ne hji,
        extendCubeMap_outside (Nat.le_of_succ_le h) _ u j (Nat.le_of_succ_le hmj)]

private def HigherHurewicz.NativeSubdivision.extendedChamberCutSequence {m n : ℕ} (h : m + 1 ≤ n)
    (e : Equiv.Perm (Fin m)) (chart : NativeChamberChart e) :
    Fin (m + 2) → C(NativeCube (Fin n), (unitInterval)) := fun j =>
  (chamberCutSequence e chart j).comp (cubeRestriction (Nat.le_of_succ_le h))

@[simp]
private theorem
    HigherHurewicz.NativeSubdivision.extendedChamberCutSequence_zero {m n : ℕ} (h : m + 1 ≤ n)
    (e : Equiv.Perm (Fin m)) (chart : NativeChamberChart e) (u : NativeCube (Fin n)) :
    extendedChamberCutSequence h e chart 0 u = 0 :=
  rfl

@[simp]
private theorem
    HigherHurewicz.NativeSubdivision.extendedChamberCutSequence_last {m n : ℕ} (h : m + 1 ≤ n)
    (e : Equiv.Perm (Fin m)) (chart : NativeChamberChart e) (u : NativeCube (Fin n)) :
    extendedChamberCutSequence h e chart (Fin.last (m + 1)) u = 1 :=
  chamberCutSequence_last e chart _

private theorem HigherHurewicz.NativeSubdivision.extendedChamberCutSequence_castSucc {m n : ℕ}
    (h : m + 1 ≤ n) (e : Equiv.Perm (Fin m)) (chart : NativeChamberChart e) (j : Fin (m + 1))
    (u : NativeCube (Fin n)) :
    extendedChamberCutSequence h e chart j.castSucc u =
      chamberLower e j.rev chart (cubeRestriction (Nat.le_of_succ_le h) u) :=
  chamberCutSequence_castSucc e chart j _

private theorem
    HigherHurewicz.NativeSubdivision.extendedChamberCutSequence_succ {m n : ℕ} (h : m + 1 ≤ n)
    (e : Equiv.Perm (Fin m)) (chart : NativeChamberChart e) (j : Fin (m + 1))
    (u : NativeCube (Fin n)) :
    extendedChamberCutSequence h e chart j.succ u =
      chamberUpper e j.rev chart (cubeRestriction (Nat.le_of_succ_le h) u) :=
  chamberCutSequence_succ e chart j _

private theorem HigherHurewicz.NativeSubdivision.NativeChamberChart.sameFlat {m : ℕ}
    {e : Equiv.Perm (Fin m)} (chart other : HigherHurewicz.NativeSubdivision.NativeChamberChart e)
    (u : HigherHurewicz.NativeSubdivision.NativeCube (Fin m)) (hu : u ∈ Cube.boundary (Fin m)) :
    HigherHurewicz.NativeSubdivision.NativeCubeSameFlat (chart.toContinuousMap u)
      (other.toContinuousMap u) := by
  obtain ⟨j, hj⟩ := hu
  let i := e.symm j
  have hei : e i = j := e.apply_symm_apply j
  rcases hj with hj | hj
  · have hi : u (e i) = 0 := hei ▸ hj
    by_cases hilast : i.val + 1 = m
    · exact .zero (e i) (chart.zero_last u i hilast hi) (other.zero_last u i hilast hi)
    · let k : Fin m := ⟨i.val + 1, by have := i.isLt; omega⟩
      have hik : i.val + 1 = k.val := rfl
      have hne : e i ≠ e k := by
        intro h
        have hv := congrArg Fin.val (e.injective h)
        dsimp [k] at hv
        omega
      exact
        .equal (e i) (e k) hne (chart.zero_adjacent u i k hik hi)
          (other.zero_adjacent u i k hik hi)
  · have hi : u (e i) = 1 := hei ▸ hj
    by_cases hifirst : i.val = 0
    · exact .one (e i) (chart.one_first u i hifirst hi) (other.one_first u i hifirst hi)
    · let k : Fin m := ⟨i.val - 1, by have := i.isLt; omega⟩
      have hki : k.val + 1 = i.val := by dsimp [k]; omega
      have hne : e i ≠ e k := by
        intro h
        have hv := congrArg Fin.val (e.injective h)
        dsimp [k] at hv
        omega
      exact
        .equal (e i) (e k) hne (chart.one_adjacent u i k hki hi) (other.one_adjacent u i k hki hi)

private theorem HigherHurewicz.NativeSubdivision.extendedChamberMap_sameFlat {m n : ℕ} (h : m ≤ n)
    {e : Equiv.Perm (Fin m)} (chart other : NativeChamberChart e) (u : NativeCube (Fin n))
    (hu : u ∈ Cube.boundary (Fin n)) :
    NativeCubeSameFlat (extendCubeMap h chart.toContinuousMap u)
      (extendCubeMap h other.toContinuousMap u) := by
  obtain ⟨j, hj⟩ := hu
  by_cases hjm : j.val < m
  · let k : Fin m := ⟨j.val, hjm⟩
    have hk : Fin.castLE h k = j := Fin.ext rfl
    apply extendCubeMap_sameFlat
    apply chart.sameFlat other
    refine ⟨k, ?_⟩
    simpa only [cubeRestriction_apply, hk] using hj
  · rcases hj with hj | hj
    · exact
        .zero j ((extendCubeMap_outside h _ u j (Nat.le_of_not_gt hjm)).trans hj)
          ((extendCubeMap_outside h _ u j (Nat.le_of_not_gt hjm)).trans hj)
    · exact
        .one j ((extendCubeMap_outside h _ u j (Nat.le_of_not_gt hjm)).trans hj)
          ((extendCubeMap_outside h _ u j (Nat.le_of_not_gt hjm)).trans hj)

private theorem HigherHurewicz.NativeSubdivision.extendedChamberMap_based {m n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin n) X x) (hp : NativeCubeInternalBased p)
    (h : m ≤ n) {e : Equiv.Perm (Fin m)} (chart : NativeChamberChart e) (u : NativeCube (Fin n))
    (hu : u ∈ Cube.boundary (Fin n)) : p (extendCubeMap h chart.toContinuousMap u) = x := by
  simpa only [nativeCubeBlend_zero] using
    nativeCubeBlend_based p hp (extendedChamberMap_sameFlat h chart chart u hu) 0

private def HigherHurewicz.NativeSubdivision.extendedChamberLoop {m n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin n) X x) (hp : NativeCubeInternalBased p)
    (h : m ≤ n) {e : Equiv.Perm (Fin m)} (chart : NativeChamberChart e) : GenLoop (Fin n) X x :=
  nativeCubePullbackLoop p (extendCubeMap h chart.toContinuousMap)
    (extendedChamberMap_based p hp h chart)

@[simp]
private theorem HigherHurewicz.NativeSubdivision.extendedChamberLoop_apply {m n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin n) X x) (hp : NativeCubeInternalBased p)
    (h : m ≤ n) {e : Equiv.Perm (Fin m)} (chart : NativeChamberChart e) (u : NativeCube (Fin n)) :
    extendedChamberLoop p hp h chart u = p (extendCubeMap h chart.toContinuousMap u) :=
  rfl

@[simp]
private theorem HigherHurewicz.NativeSubdivision.extendedChamberLoop_zero {n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin n) X x) (hp : NativeCubeInternalBased p)
    (h : 0 ≤ n) {e : Equiv.Perm (Fin 0)} (chart : NativeChamberChart e) :
    extendedChamberLoop p hp h chart = p := by
  apply GenLoop.ext
  intro u
  simp

private def HigherHurewicz.NativeSubdivision.extendedChamberHomotopy {m n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin n) X x) (hp : NativeCubeInternalBased p)
    (h : m ≤ n) {e : Equiv.Perm (Fin m)} (chart other : NativeChamberChart e) :
    (extendedChamberLoop p hp h chart).val.HomotopyRel (extendedChamberLoop p hp h other).val
      (Cube.boundary (Fin n)) :=
  nativeCubeLinearHomotopy p hp (extendCubeMap h chart.toContinuousMap)
    (extendCubeMap h other.toContinuousMap) (extendedChamberMap_based p hp h chart)
    (extendedChamberMap_based p hp h other) (extendedChamberMap_sameFlat h chart other)

private theorem
    HigherHurewicz.NativeSubdivision.nativeClass_extendedChamber_eq {m n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin n) X x) (hp : NativeCubeInternalBased p)
    (h : m ≤ n) {e : Equiv.Perm (Fin m)} (chart other : NativeChamberChart e) :
    nativeClass (extendedChamberLoop p hp h chart) =
      nativeClass (extendedChamberLoop p hp h other) :=
  nativeClass_homotopic ⟨extendedChamberHomotopy p hp h chart other⟩

private def HigherHurewicz.NativeSubdivision.CutIndependent {N : Type*} [DecidableEq N] (i : N)
    (a : C(NativeCube N, (unitInterval))) : Prop :=
  ∀ u v, a (Function.update u i v) = a u

private def HigherHurewicz.NativeSubdivision.CutBased {N : Type*} [DecidableEq N] {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop N X x) (i : N)
    (a : C(NativeCube N, (unitInterval))) : Prop :=
  ∀ u, p (Function.update u i (a u)) = x

private def HigherHurewicz.NativeSubdivision.sliceMap {N : Type*} [DecidableEq N] (i : N)
    (a b : C(NativeCube N, (unitInterval))) : C(NativeCube N, NativeCube N)
    where
  toFun u := Function.update u i (Set.Icc.convexComb (a u) (b u) (u i))
  continuous_toFun :=
    continuous_id.update i
      (Set.Icc.continuous_convexComb_prod.comp
        (a.continuous.prodMk (b.continuous.prodMk (continuous_apply i))))

private theorem
    HigherHurewicz.NativeSubdivision.sliceMap_based {N : Type*} [DecidableEq N] {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop N X x) (i : N)
    (a b : C(NativeCube N, (unitInterval))) (ha : CutBased p i a) (hb : CutBased p i b)
    (u : NativeCube N) (hu : u ∈ Cube.boundary N) : p (sliceMap i a b u) = x := by
  rcases hu with ⟨j, hj⟩
  by_cases hji : j = i
  · subst j
    rcases hj with hj | hj
    · simpa [sliceMap, hj] using ha u
    · simpa [sliceMap, hj] using hb u
  · exact p.property _ ⟨j, by simpa [sliceMap, hji] using hj⟩

private def HigherHurewicz.NativeSubdivision.sliceLoop {N : Type*} [DecidableEq N] {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop N X x) (i : N)
    (a b : C(NativeCube N, (unitInterval))) (ha : CutBased p i a) (hb : CutBased p i b) :
    GenLoop N X x :=
  ⟨p.val.comp (sliceMap i a b), sliceMap_based p i a b ha hb⟩

@[simp]
private theorem
    HigherHurewicz.NativeSubdivision.sliceLoop_apply {N : Type*} [DecidableEq N] {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop N X x) (i : N)
    (a b : C(NativeCube N, (unitInterval))) (ha : CutBased p i a) (hb : CutBased p i b)
    (u : NativeCube N) :
    sliceLoop p i a b ha hb u = p (Function.update u i (Set.Icc.convexComb (a u) (b u) (u i))) :=
  rfl

private theorem
    HigherHurewicz.NativeSubdivision.sliceLoop_self {N : Type*} [DecidableEq N] {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop N X x) (i : N) (a : C(NativeCube N, (unitInterval)))
    (ha : CutBased p i a) : sliceLoop p i a a ha ha = GenLoop.const := by
  apply GenLoop.ext
  intro u
  simpa only [sliceLoop_apply, Set.Icc.convexComb_eq, GenLoop.const_apply] using ha u

private theorem
    HigherHurewicz.NativeSubdivision.sliceLoop_full {N : Type*} [DecidableEq N] {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop N X x) (i : N)
    (a b : C(NativeCube N, (unitInterval))) (ha : CutBased p i a) (hb : CutBased p i b)
    (ha0 : ∀ u, a u = 0) (hb1 : ∀ u, b u = 1) : sliceLoop p i a b ha hb = p := by
  apply GenLoop.ext
  intro u
  simp [ha0 u, hb1 u]

private def HigherHurewicz.NativeSubdivision.sliceHomotopyOfCoordinate {N : Type*} [DecidableEq N]
    {X : Type*} [TopologicalSpace X] {x : X} (p : GenLoop N X x) (i : N)
    (a b : C(NativeCube N, (unitInterval))) (ha : CutBased p i a) (hb : CutBased p i b)
    (q : GenLoop N X x) (w : C(NativeCube N, (unitInterval)))
    (hq : ∀ u, q u = p (Function.update u i (w u))) (hw0 : ∀ u, u i = 0 → w u = a u)
    (hw1 : ∀ u, u i = 1 → w u = b u) :
    (sliceLoop p i a b ha hb).val.HomotopyRel q.val (Cube.boundary N)
    where
  toFun
    v :=
    p
      (Function.update v.2 i
        (Set.Icc.convexComb (Set.Icc.convexComb (a v.2) (b v.2) (v.2 i)) (w v.2) v.1))
  continuous_toFun :=
    p.val.continuous.comp
      (continuous_snd.update i
        (Set.Icc.continuous_convexComb_prod.comp
          ((Set.Icc.continuous_convexComb_prod.comp
                ((a.continuous.comp continuous_snd).prodMk
                  ((b.continuous.comp continuous_snd).prodMk
                    ((continuous_apply i).comp continuous_snd)))).prodMk
            ((w.continuous.comp continuous_snd).prodMk continuous_fst))))
  map_zero_left
    u := by
    change
      p
          (Function.update u i
            (Set.Icc.convexComb (Set.Icc.convexComb (a u) (b u) (u i)) (w u) 0)) =
        _
    rw [Set.Icc.convexComb_zero]
    rfl
  map_one_left
    u := by
    change
      p
          (Function.update u i
            (Set.Icc.convexComb (Set.Icc.convexComb (a u) (b u) (u i)) (w u) 1)) =
        q u
    rw [Set.Icc.convexComb_one]
    exact (hq u).symm
  prop' t u
    hu := by
    change
      p
          (Function.update u i
            (Set.Icc.convexComb (Set.Icc.convexComb (a u) (b u) (u i)) (w u) t)) =
        sliceLoop p i a b ha hb u
    have hs : sliceLoop p i a b ha hb u = x := (sliceLoop p i a b ha hb).property u hu
    rw [hs]
    rcases hu with ⟨j, hj⟩
    by_cases hji : j = i
    · subst j
      rcases hj with hj | hj
      · simpa [hj, hw0 u hj] using ha u
      · simpa [hj, hw1 u hj] using hb u
    · exact p.property _ ⟨j, by simpa [hji] using hj⟩

private theorem HigherHurewicz.NativeSubdivision.extendedChamberCutSequence_independent {m n : ℕ}
    (h : m + 1 ≤ n) (e : Equiv.Perm (Fin m)) (chart : NativeChamberChart e) (j : Fin (m + 2)) :
    CutIndependent (chamberCutIndex h) (extendedChamberCutSequence h e chart j) := by
  intro u v
  change
    chamberCutSequence e chart j
        (cubeRestriction (Nat.le_of_succ_le h) (Function.update u (chamberCutIndex h) v)) =
      chamberCutSequence e chart j (cubeRestriction (Nat.le_of_succ_le h) u)
  rw [cubeRestriction_update_outside (Nat.le_of_succ_le h) u (chamberCutIndex h) (le_refl m) v]

private theorem
    HigherHurewicz.NativeSubdivision.extendedChamberCutSequence_based {m n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin n) X x) (hp : NativeCubeInternalBased p)
    (h : m + 1 ≤ n) (e : Equiv.Perm (Fin m)) (chart : NativeChamberChart e) (j : Fin (m + 2)) :
    CutBased (extendedChamberLoop p hp (Nat.le_of_succ_le h) chart) (chamberCutIndex h)
      (extendedChamberCutSequence h e chart j) := by
  intro u
  rw [extendedChamberLoop_apply,
    extendCubeMap_update_outside (Nat.le_of_succ_le h) chart.toContinuousMap u (chamberCutIndex h)
      (le_refl m)]
  refine Fin.cases ?_ (fun r => ?_) j
  · rw [extendedChamberCutSequence_zero]
    exact p.property _ ⟨chamberCutIndex h, Or.inl (Function.update_self _ _ _)⟩
  · rw [extendedChamberCutSequence_succ]
    by_cases hr : 0 < r.rev.val
    · let k : Fin m := ⟨r.rev.val - 1, by have := r.rev.isLt; omega⟩
      have hk : r.rev.val = k.val + 1 := by
        change r.rev.val = (r.rev.val - 1) + 1
        omega
      rw [chamberUpper_of_rank e r.rev chart (cubeRestriction (Nat.le_of_succ_le h) u) k hk]
      apply
        hp _ (chamberCutIndex h) (Fin.castLE (Nat.le_of_succ_le h) (e k))
          (chamberCutIndex_ne_castLE h (e k)).symm
      rw [Function.update_self, Function.update_of_ne (chamberCutIndex_ne_castLE h (e k)),
        extendCubeMap_castLE]
    · have hr0 : r.rev.val = 0 := by omega
      rw [chamberUpper_first e r.rev chart (cubeRestriction (Nat.le_of_succ_le h) u) hr0]
      exact p.property _ ⟨chamberCutIndex h, Or.inr (Function.update_self _ _ _)⟩

private def HigherHurewicz.NativeSubdivision.cutBinaryWarp :
    C(((unitInterval) × (unitInterval) × (unitInterval)) × (unitInterval), (unitInterval))
    where
  toFun
    p :=
    Set.Icc.convexComb
      (Set.Icc.convexComb p.1.1 p.1.2.1 (Set.projIcc 0 1 zero_le_one (2 * (p.2 : ℝ)))) p.1.2.2
      (Set.projIcc 0 1 zero_le_one (2 * (p.2 : ℝ) - 1))
  continuous_toFun := by
    unfold Set.Icc.convexComb
    fun_prop

private theorem HigherHurewicz.NativeSubdivision.cutBinaryWarp_apply (a b c t : (unitInterval)) :
    cutBinaryWarp ((a, b, c), t) =
      Set.Icc.convexComb (Set.Icc.convexComb a b (Set.projIcc 0 1 zero_le_one (2 * (t : ℝ)))) c
        (Set.projIcc 0 1 zero_le_one (2 * (t : ℝ) - 1)) :=
  rfl

@[simp]
private theorem HigherHurewicz.NativeSubdivision.cutBinaryWarp_zero (a b c : (unitInterval)) :
    cutBinaryWarp ((a, b, c), 0) = a := by
  norm_num [cutBinaryWarp, Set.projIcc, Set.Icc.convexComb]

@[simp]
private theorem HigherHurewicz.NativeSubdivision.cutBinaryWarp_one (a b c : (unitInterval)) :
    cutBinaryWarp ((a, b, c), 1) = c := by
  norm_num [cutBinaryWarp, Set.projIcc, Set.Icc.convexComb]

private theorem HigherHurewicz.NativeSubdivision.cutBinaryWarp_of_le_half (a b c t : (unitInterval))
    (ht : (t : ℝ) ≤ 1 / 2) :
    cutBinaryWarp ((a, b, c), t) =
      Set.Icc.convexComb a b (Set.projIcc 0 1 zero_le_one (2 * (t : ℝ))) := by
  have hz : Set.projIcc 0 1 zero_le_one (2 * (t : ℝ) - 1) = (0 : (unitInterval)) :=
    Set.projIcc_of_le_left zero_le_one (by linarith)
  rw [cutBinaryWarp_apply, hz, Set.Icc.convexComb_zero]

private theorem HigherHurewicz.NativeSubdivision.cutBinaryWarp_of_half_le (a b c t : (unitInterval))
    (ht : 1 / 2 ≤ (t : ℝ)) :
    cutBinaryWarp ((a, b, c), t) =
      Set.Icc.convexComb b c (Set.projIcc 0 1 zero_le_one (2 * (t : ℝ) - 1)) := by
  have ho : Set.projIcc 0 1 zero_le_one (2 * (t : ℝ)) = (1 : (unitInterval)) :=
    Set.projIcc_of_right_le zero_le_one (by linarith)
  rw [cutBinaryWarp_apply, ho, Set.Icc.convexComb_one]

private theorem HigherHurewicz.NativeSubdivision.cutBinaryWarp_of_half_lt (a b c t : (unitInterval))
    (ht : 1 / 2 < (t : ℝ)) :
    cutBinaryWarp ((a, b, c), t) =
      Set.Icc.convexComb b c (Set.projIcc 0 1 zero_le_one (2 * (t : ℝ) - 1)) :=
  cutBinaryWarp_of_half_le a b c t ht.le

private def HigherHurewicz.NativeSubdivision.sliceBinaryCoordinate {N : Type*} (i : N)
    (a b c : C(NativeCube N, (unitInterval))) : C(NativeCube N, (unitInterval))
    where
  toFun u := cutBinaryWarp ((a u, b u, c u), u i)
  continuous_toFun :=
    cutBinaryWarp.continuous.comp
      ((a.continuous.prodMk (b.continuous.prodMk c.continuous)).prodMk (continuous_apply i))

private theorem HigherHurewicz.NativeSubdivision.sliceBinaryCoordinate_zero {N : Type*} (i : N)
    (a b c : C(NativeCube N, (unitInterval))) (u : NativeCube N) (hu : u i = 0) :
    sliceBinaryCoordinate i a b c u = a u := by simp [sliceBinaryCoordinate, hu]

private theorem HigherHurewicz.NativeSubdivision.sliceBinaryCoordinate_one {N : Type*} (i : N)
    (a b c : C(NativeCube N, (unitInterval))) (u : NativeCube N) (hu : u i = 1) :
    sliceBinaryCoordinate i a b c u = c u := by simp [sliceBinaryCoordinate, hu]

private theorem HigherHurewicz.NativeSubdivision.sliceTrans_apply {N : Type*} {X : Type*}
    [TopologicalSpace X] {x : X} [DecidableEq N] (p : GenLoop N X x) (i : N)
    (a b c : C(NativeCube N, (unitInterval))) (ha : CutBased p i a) (hb : CutBased p i b)
    (hc : CutBased p i c) (haInd : CutIndependent i a) (hbInd : CutIndependent i b)
    (hcInd : CutIndependent i c) (u : NativeCube N) :
    GenLoop.transAt i (sliceLoop p i a b ha hb) (sliceLoop p i b c hb hc) u =
      p (Function.update u i (sliceBinaryCoordinate i a b c u)) := by
  change
    (if (u i : ℝ) ≤ 1 / 2 then
        sliceLoop p i a b ha hb
          (Function.update u i (Set.projIcc 0 1 zero_le_one (2 * (u i : ℝ))))
      else
        sliceLoop p i b c hb hc
          (Function.update u i (Set.projIcc 0 1 zero_le_one (2 * (u i : ℝ) - 1)))) =
      p (Function.update u i (cutBinaryWarp ((a u, b u, c u), u i)))
  split_ifs with h
  · rw [sliceLoop_apply, haInd u _, hbInd u _, Function.update_self, Function.update_idem]
    exact
      congrArg (fun v => p (Function.update u i v))
        (cutBinaryWarp_of_le_half (a u) (b u) (c u) (u i) h).symm
  · rw [sliceLoop_apply, hbInd u _, hcInd u _, Function.update_self, Function.update_idem]
    exact
      congrArg (fun v => p (Function.update u i v))
        (cutBinaryWarp_of_half_lt (a u) (b u) (c u) (u i) (lt_of_not_ge h)).symm

private theorem HigherHurewicz.NativeSubdivision.slice_homotopic_trans {N : Type*} {X : Type*}
    [TopologicalSpace X] {x : X} [DecidableEq N] (p : GenLoop N X x) (i : N)
    (a b c : C(NativeCube N, (unitInterval))) (ha : CutBased p i a) (hb : CutBased p i b)
    (hc : CutBased p i c) (haInd : CutIndependent i a) (hbInd : CutIndependent i b)
    (hcInd : CutIndependent i c) :
    GenLoop.Homotopic (sliceLoop p i a c ha hc)
      (GenLoop.transAt i (sliceLoop p i a b ha hb) (sliceLoop p i b c hb hc)) :=
  ⟨sliceHomotopyOfCoordinate p i a c ha hc
      (GenLoop.transAt i (sliceLoop p i a b ha hb) (sliceLoop p i b c hb hc))
      (sliceBinaryCoordinate i a b c) (sliceTrans_apply p i a b c ha hb hc haInd hbInd hcInd)
      (sliceBinaryCoordinate_zero i a b c) (sliceBinaryCoordinate_one i a b c)⟩

private theorem HigherHurewicz.NativeSubdivision.slice_toLoop_transAt {N : Type*} {X : Type*}
    [TopologicalSpace X] {x : X} [DecidableEq N] (i : N) (a b : GenLoop N X x) :
    GenLoop.toLoop i (GenLoop.transAt i a b) = (GenLoop.toLoop i a).trans (GenLoop.toLoop i b) := by
  rw [← GenLoop.fromLoop_trans_toLoop, GenLoop.to_from]

private theorem HigherHurewicz.NativeSubdivision.slice_transAt_homotopic {N : Type*} {X : Type*}
    [TopologicalSpace X] {x : X} [DecidableEq N] (i : N) {a b c d : GenLoop N X x}
    (ha : GenLoop.Homotopic a c) (hb : GenLoop.Homotopic b d) :
    GenLoop.Homotopic (GenLoop.transAt i a b) (GenLoop.transAt i c d) := by
  apply GenLoop.homotopicFrom i
  rw [slice_toLoop_transAt, slice_toLoop_transAt]
  rcases GenLoop.homotopicTo i ha with ⟨Ha⟩
  rcases GenLoop.homotopicTo i hb with ⟨Hb⟩
  exact ⟨Ha.hcomp Hb⟩

private def HigherHurewicz.NativeSubdivision.sliceConcat {N : Type*} [DecidableEq N] {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop N X x) (i : N) :
    (k : ℕ) →
      (a : Fin (k + 1) → C(NativeCube N, (unitInterval))) →
        (∀ j, CutBased p i (a j)) → GenLoop N X x
  | 0, _, _ => GenLoop.const
  | k + 1, a, ha =>
    GenLoop.transAt i
      (sliceLoop p i (a 0) (a (0 : Fin (k + 1)).succ) (ha 0) (ha (0 : Fin (k + 1)).succ))
      (sliceConcat p i k (fun j => a j.succ) (fun j => ha j.succ))

private theorem HigherHurewicz.NativeSubdivision.slice_homotopic_concat {N : Type*} [DecidableEq N]
    {X : Type*} [TopologicalSpace X] {x : X} (p : GenLoop N X x) (i : N) (k : ℕ)
    (a : Fin (k + 1) → C(NativeCube N, (unitInterval))) (ha : ∀ j, CutBased p i (a j))
    (hInd : ∀ j, CutIndependent i (a j)) :
    GenLoop.Homotopic (sliceLoop p i (a 0) (a (Fin.last k)) (ha 0) (ha (Fin.last k)))
      (sliceConcat p i k a ha) := by
  induction k with
  | zero =>
    change GenLoop.Homotopic (sliceLoop p i (a 0) (a 0) (ha 0) (ha 0)) GenLoop.const
    rw [sliceLoop_self]
  | succ k
    ih =>
    have ht := ih (fun j => a j.succ) (fun j => ha j.succ) (fun j => hInd j.succ)
    have hs :=
      slice_homotopic_trans p i (a 0) (a (0 : Fin (k + 1)).succ) (a (Fin.last (k + 1))) (ha 0)
        (ha (0 : Fin (k + 1)).succ) (ha (Fin.last (k + 1))) (hInd 0) (hInd (0 : Fin (k + 1)).succ)
        (hInd (Fin.last (k + 1)))
    apply hs.trans
    apply slice_transAt_homotopic
    · exact GenLoop.Homotopic.refl _
    · exact ht

private theorem
    HigherHurewicz.NativeSubdivision.sliceConcat_class {N : Type*} [DecidableEq N] {X : Type*}
    [TopologicalSpace X] {x : X} [Nontrivial N] (p : GenLoop N X x) (i : N) (k : ℕ)
    (a : Fin (k + 1) → C(NativeCube N, (unitInterval))) (ha : ∀ j, CutBased p i (a j)) :
    nativeClass (sliceConcat p i k a ha) =
      ∑ j : Fin k,
        nativeClass (sliceLoop p i (a j.castSucc) (a j.succ) (ha j.castSucc) (ha j.succ)) := by
  induction k with
  | zero => simp [sliceConcat]
  | succ k ih =>
    rw [sliceConcat, nativeClass_transAt, ih, Fin.sum_univ_succ]
    rfl

private theorem HigherHurewicz.NativeSubdivision.finiteCuts_homotopic {N : Type*} [DecidableEq N]
    {X : Type*} [TopologicalSpace X] {x : X} (p : GenLoop N X x) (i : N) (k : ℕ)
    (a : Fin (k + 1) → C(NativeCube N, (unitInterval))) (ha : ∀ j, CutBased p i (a j))
    (hInd : ∀ j, CutIndependent i (a j)) (hzero : ∀ u, a 0 u = 0)
    (hone : ∀ u, a (Fin.last k) u = 1) : GenLoop.Homotopic p (sliceConcat p i k a ha) := by
  have h := slice_homotopic_concat p i k a ha hInd
  rwa [sliceLoop_full p i (a 0) (a (Fin.last k)) (ha 0) (ha (Fin.last k)) hzero hone] at h

private theorem
    HigherHurewicz.NativeSubdivision.finiteCuts_class {N : Type*} [DecidableEq N] {X : Type*}
    [TopologicalSpace X] {x : X} [Nontrivial N] (p : GenLoop N X x) (i : N) (k : ℕ)
    (a : Fin (k + 1) → C(NativeCube N, (unitInterval))) (ha : ∀ j, CutBased p i (a j))
    (hInd : ∀ j, CutIndependent i (a j)) (hzero : ∀ u, a 0 u = 0)
    (hone : ∀ u, a (Fin.last k) u = 1) :
    nativeClass p =
      ∑ j : Fin k,
        nativeClass (sliceLoop p i (a j.castSucc) (a j.succ) (ha j.castSucc) (ha j.succ)) :=
  (nativeClass_homotopic (finiteCuts_homotopic p i k a ha hInd hzero hone)).trans
    (sliceConcat_class p i k a ha)

private theorem HigherHurewicz.NativeSubdivision.extendedChamberCut_slice_eq {m n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin n) X x) (hp : NativeCubeInternalBased p)
    (h : m + 1 ≤ n) (e : Equiv.Perm (Fin m)) (chart : NativeChamberChart e) (j : Fin (m + 1)) :
    sliceLoop (extendedChamberLoop p hp (Nat.le_of_succ_le h) chart) (chamberCutIndex h)
        (extendedChamberCutSequence h e chart j.castSucc)
        (extendedChamberCutSequence h e chart j.succ)
        (extendedChamberCutSequence_based p hp h e chart j.castSucc)
        (extendedChamberCutSequence_based p hp h e chart j.succ) =
      extendedChamberLoop p hp h (insertChamberChart e j.rev chart) := by
  apply GenLoop.ext
  intro u
  rw [sliceLoop_apply, extendedChamberLoop_apply, extendedChamberCutSequence_castSucc,
    extendedChamberCutSequence_succ,
    extendCubeMap_update_outside (Nat.le_of_succ_le h) chart.toContinuousMap u (chamberCutIndex h)
      (le_refl m)]
  exact congrArg p (extend_insertChamberMap h e j.rev chart u).symm

private theorem
    HigherHurewicz.NativeSubdivision.nativeClass_extendedChamber_eq_sum_insertions {m n : ℕ}
    {X : Type*} [TopologicalSpace X] {x : X} [Nontrivial (Fin n)] (p : GenLoop (Fin n) X x)
    (hp : NativeCubeInternalBased p) (h : m + 1 ≤ n) {e : Equiv.Perm (Fin m)}
    (chart : NativeChamberChart e) :
    nativeClass (extendedChamberLoop p hp (Nat.le_of_succ_le h) chart) =
      ∑ r : Fin (m + 1),
        nativeClass (extendedChamberLoop p hp h (insertChamberChart e r chart)) := by
  have hcut :=
    finiteCuts_class (extendedChamberLoop p hp (Nat.le_of_succ_le h) chart) (chamberCutIndex h)
      (m + 1) (extendedChamberCutSequence h e chart)
      (extendedChamberCutSequence_based p hp h e chart)
      (extendedChamberCutSequence_independent h e chart)
      (extendedChamberCutSequence_zero h e chart) (extendedChamberCutSequence_last h e chart)
  have hrev :
    nativeClass (extendedChamberLoop p hp (Nat.le_of_succ_le h) chart) =
      ∑ j : Fin (m + 1),
        nativeClass (extendedChamberLoop p hp h (insertChamberChart e j.rev chart)) := by
    simpa only [extendedChamberCut_slice_eq p hp h e chart] using hcut
  exact
    hrev.trans
      (chamberCuts_sum_rev
        (fun r => nativeClass (extendedChamberLoop p hp h (insertChamberChart e r chart))))

private def
    HigherHurewicz.NativeSubdivision.prefixProduct {n : ℕ} (u : NativeCube (Fin n)) (k : ℕ) :
    (unitInterval) :=
  ∏ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k), u i

@[simp]
private theorem
    HigherHurewicz.NativeSubdivision.prefixProduct_zero {n : ℕ} (u : NativeCube (Fin n)) :
    prefixProduct u 0 = 1 := by simp [prefixProduct]

private theorem HigherHurewicz.NativeSubdivision.prefixProduct_succ {n : ℕ} (u : NativeCube (Fin n))
    (k : ℕ) (hk : k < n) : prefixProduct u (k + 1) = prefixProduct u k * u ⟨k, hk⟩ := by
  have hs :
    (Finset.univ.filter fun i : Fin n => i.val < k + 1) =
      Insert.insert ⟨k, hk⟩ (Finset.univ.filter fun i : Fin n => i.val < k) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  unfold prefixProduct
  rw [hs, Finset.prod_insert (by simp)]
  exact mul_comm _ _

private theorem HigherHurewicz.NativeSubdivision.prefixProduct_eq_zero_of_coordinate {n : ℕ}
    (u : NativeCube (Fin n)) (k : ℕ) (i : Fin n) (hik : i.val < k) (hi : u i = 0) :
    prefixProduct u k = 0 :=
  Finset.prod_eq_zero (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hik⟩) hi

private theorem HigherHurewicz.NativeSubdivision.prefixProduct_succ_of_one {n : ℕ}
    (u : NativeCube (Fin n)) (i : Fin n) (hi : u i = 1) :
    prefixProduct u (i.val + 1) = prefixProduct u i.val := by
  rw [prefixProduct_succ u i.val i.isLt, hi, mul_one]

private theorem HigherHurewicz.NativeSubdivision.continuous_prefixProduct (n k : ℕ) :
    Continuous (fun u : NativeCube (Fin n) => prefixProduct u k) := by
  unfold prefixProduct
  generalize Finset.univ.filter (fun i : Fin n => i.val < k) = s
  induction s using Finset.induction_on with
  | empty =>
    simpa only [Finset.prod_empty] using
      (continuous_const : Continuous (fun _ : NativeCube (Fin n) => (1 : (unitInterval))))
  | @insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    exact
      ((continuous_subtype_val.comp (continuous_apply i)).mul
            (continuous_subtype_val.comp ih)).subtype_mk
        _

private def HigherHurewicz.NativeSubdivision.nativeDuffyCubeCanonical (n : ℕ) :
    C(NativeCube (Fin n), NativeCube (Fin n))
    where
  toFun u i := prefixProduct u (i.val + 1)
  continuous_toFun := continuous_pi fun i => continuous_prefixProduct n (i.val + 1)

private def HigherHurewicz.NativeSubdivision.nativeDuffyCube {n : ℕ} (e : Equiv.Perm (Fin n)) :
    C(NativeCube (Fin n), NativeCube (Fin n))
    where
  toFun u i := nativeDuffyCubeCanonical n u (e.symm i)
  continuous_toFun :=
    continuous_pi fun i =>
      (continuous_apply (e.symm i)).comp (nativeDuffyCubeCanonical n).continuous

private theorem
    HigherHurewicz.NativeSubdivision.nativeDuffyCube_apply {n : ℕ} (e : Equiv.Perm (Fin n))
    (u : NativeCube (Fin n)) (i : Fin n) :
    nativeDuffyCube e u i = prefixProduct u ((e.symm i).val + 1) :=
  rfl

@[simp]
private theorem HigherHurewicz.NativeSubdivision.nativeDuffyCube_coordinate {n : ℕ}
    (e : Equiv.Perm (Fin n)) (u : NativeCube (Fin n)) (i : Fin n) :
    nativeDuffyCube e u (e i) = prefixProduct u (i.val + 1) := by simp [nativeDuffyCube_apply]

private theorem HigherHurewicz.NativeSubdivision.nativeDuffyCube_coordinate_eq_zero {n : ℕ}
    (e : Equiv.Perm (Fin n)) (u : NativeCube (Fin n)) (i j : Fin n) (hij : i ≤ j) (hi : u i = 0) :
    nativeDuffyCube e u (e j) = 0 := by
  rw [nativeDuffyCube_coordinate]
  exact prefixProduct_eq_zero_of_coordinate u _ i (by omega) hi

private theorem HigherHurewicz.NativeSubdivision.nativeDuffyCube_coordinate_zero_of_one {n : ℕ}
    (e : Equiv.Perm (Fin (n + 1))) (u : NativeCube (Fin (n + 1))) (hu : u 0 = 1) :
    nativeDuffyCube e u (e 0) = 1 := by
  rw [nativeDuffyCube_coordinate, prefixProduct_succ_of_one u 0 hu]
  exact prefixProduct_zero u

private theorem HigherHurewicz.NativeSubdivision.nativeDuffyCube_adjacent_of_one {n : ℕ}
    (e : Equiv.Perm (Fin (n + 1))) (u : NativeCube (Fin (n + 1))) (i : Fin n)
    (hi : u i.succ = 1) : nativeDuffyCube e u (e i.castSucc) = nativeDuffyCube e u (e i.succ) := by
  rw [nativeDuffyCube_coordinate, nativeDuffyCube_coordinate,
    prefixProduct_succ_of_one u i.succ hi]
  rfl

private theorem
    HigherHurewicz.NativeSubdivision.nativeDuffyCube_boundary {n : ℕ} (e : Equiv.Perm (Fin n))
    (u : NativeCube (Fin n)) (hu : u ∈ Cube.boundary (Fin n)) :
    nativeDuffyCube e u ∈ Cube.boundary (Fin n) ∨
      ∃ i j : Fin n, i ≠ j ∧ nativeDuffyCube e u i = nativeDuffyCube e u j := by
  obtain ⟨i, hi | hi⟩ := hu
  · exact Or.inl ⟨e i, Or.inl (nativeDuffyCube_coordinate_eq_zero e u i i le_rfl hi)⟩
  · cases n with
    | zero => exact Fin.elim0 i
    | succ n =>
      cases i using Fin.cases with
      | zero => exact Or.inl ⟨e 0, Or.inr (nativeDuffyCube_coordinate_zero_of_one e u hi)⟩
      | succ i =>
        exact
          Or.inr
            ⟨e i.castSucc, e i.succ,
              e.injective.ne (by intro h; have := congrArg Fin.val h; simp at this),
              nativeDuffyCube_adjacent_of_one e u i hi⟩

private theorem
    HigherHurewicz.NativeSubdivision.nativeDuffyCube_based {X : Type*} [TopologicalSpace X]
    {x : X} {n : ℕ} (p : GenLoop (Fin n) X x) (hp : NativeCubeInternalBased p)
    (e : Equiv.Perm (Fin n)) (u : NativeCube (Fin n)) (hu : u ∈ Cube.boundary (Fin n)) :
    p (nativeDuffyCube e u) = x := by
  rcases nativeDuffyCube_boundary e u hu with h | ⟨i, j, hij, h⟩
  · exact p.property _ h
  · exact hp _ i j hij h

private def
    HigherHurewicz.NativeSubdivision.nativeDuffyCubeLoop {X : Type*} [TopologicalSpace X] {x : X}
    {n : ℕ} (p : GenLoop (Fin n) X x) (hp : NativeCubeInternalBased p) (e : Equiv.Perm (Fin n)) :
    GenLoop (Fin n) X x :=
  nativeCubePullbackLoop p (nativeDuffyCube e) (nativeDuffyCube_based p hp e)

private def
    HigherHurewicz.NativeSubdivision.nativeOrderedDuffyMap {n : ℕ} (e : Equiv.Perm (Fin n)) :
    C(NativeCube (Fin n), NativeCube (Fin n)) :=
  (nativeDuffyCube e).comp (permuteCubeCoordinates e)

@[simp]
private theorem HigherHurewicz.NativeSubdivision.nativeOrderedDuffyMap_coordinate {n : ℕ}
    (e : Equiv.Perm (Fin n)) (u : NativeCube (Fin n)) (i : Fin n) :
    nativeOrderedDuffyMap e u (e i) = prefixProduct (fun k => u (e k)) (i.val + 1) := by
  exact nativeDuffyCube_coordinate e (permuteCubeCoordinates e u) i

private theorem HigherHurewicz.NativeSubdivision.nativeOrderedDuffyMap_coordinate_eq_zero {n : ℕ}
    (e : Equiv.Perm (Fin n)) (u : NativeCube (Fin n)) (i j : Fin n) (hij : i ≤ j)
    (hi : u (e i) = 0) : nativeOrderedDuffyMap e u (e j) = 0 :=
  nativeDuffyCube_coordinate_eq_zero e (permuteCubeCoordinates e u) i j hij hi

private theorem HigherHurewicz.NativeSubdivision.nativeOrderedDuffyMap_zero_last {n : ℕ}
    (e : Equiv.Perm (Fin n)) (u : NativeCube (Fin n)) (i : Fin n) (_hi : i.val + 1 = n)
    (hu : u (e i) = 0) : nativeOrderedDuffyMap e u (e i) = 0 :=
  nativeOrderedDuffyMap_coordinate_eq_zero e u i i le_rfl hu

private theorem HigherHurewicz.NativeSubdivision.nativeOrderedDuffyMap_zero_adjacent {n : ℕ}
    (e : Equiv.Perm (Fin n)) (u : NativeCube (Fin n)) (i j : Fin n) (hij : i.val + 1 = j.val)
    (hu : u (e i) = 0) : nativeOrderedDuffyMap e u (e i) = nativeOrderedDuffyMap e u (e j) := by
  rw [nativeOrderedDuffyMap_coordinate_eq_zero e u i i le_rfl hu,
    nativeOrderedDuffyMap_coordinate_eq_zero e u i j (by omega) hu]

private theorem HigherHurewicz.NativeSubdivision.nativeOrderedDuffyMap_one_first {n : ℕ}
    (e : Equiv.Perm (Fin n)) (u : NativeCube (Fin n)) (i : Fin n) (hi : i.val = 0)
    (hu : u (e i) = 1) : nativeOrderedDuffyMap e u (e i) = 1 := by
  rw [nativeOrderedDuffyMap_coordinate, prefixProduct_succ_of_one (fun k => u (e k)) i hu, hi,
    prefixProduct_zero]

private theorem HigherHurewicz.NativeSubdivision.nativeOrderedDuffyMap_one_adjacent {n : ℕ}
    (e : Equiv.Perm (Fin n)) (u : NativeCube (Fin n)) (i j : Fin n) (hji : j.val + 1 = i.val)
    (hu : u (e i) = 1) : nativeOrderedDuffyMap e u (e i) = nativeOrderedDuffyMap e u (e j) := by
  rw [nativeOrderedDuffyMap_coordinate, nativeOrderedDuffyMap_coordinate,
    prefixProduct_succ_of_one (fun k => u (e k)) i hu, hji]

private theorem HigherHurewicz.NativeSubdivision.nativeOrderedDuffyMap_based {X : Type*}
    [TopologicalSpace X] {x : X} {n : ℕ} (p : GenLoop (Fin n) X x)
    (hp : NativeCubeInternalBased p) (e : Equiv.Perm (Fin n)) (u : NativeCube (Fin n))
    (hu : u ∈ Cube.boundary (Fin n)) : p (nativeOrderedDuffyMap e u) = x :=
  nativeDuffyCube_based p hp e _ (permuteCubeCoordinates_boundary e u hu)

private def HigherHurewicz.NativeSubdivision.nativeCubeOrderedDuffyHomotopy {X : Type*}
    [TopologicalSpace X] {x : X} {n : ℕ} (p : GenLoop (Fin n) X x)
    (hp : NativeCubeInternalBased p) (e : Equiv.Perm (Fin n))
    (f : C(NativeCube (Fin n), NativeCube (Fin n)))
    (hf : ∀ u ∈ Cube.boundary (Fin n), p (f u) = x)
    (hfg : ∀ u ∈ Cube.boundary (Fin n), NativeCubeSameFlat (f u) (nativeOrderedDuffyMap e u)) :
    (nativeCubePullbackLoop p f hf).val.HomotopyRel
      (permuteCubeLoop (nativeDuffyCubeLoop p hp e) e).val (Cube.boundary (Fin n)) :=
  nativeCubeLinearHomotopy p hp f (nativeOrderedDuffyMap e) hf
    (nativeOrderedDuffyMap_based p hp e) hfg

private theorem HigherHurewicz.NativeSubdivision.nativeClass_commonOrderedDuffy {X : Type*}
    [TopologicalSpace X] {x : X} {n : ℕ} [Nontrivial (Fin n)] (p : GenLoop (Fin n) X x)
    (hp : NativeCubeInternalBased p) (e : Equiv.Perm (Fin n))
    (f : C(NativeCube (Fin n), NativeCube (Fin n)))
    (hf : ∀ u ∈ Cube.boundary (Fin n), p (f u) = x)
    (hfg : ∀ u ∈ Cube.boundary (Fin n), NativeCubeSameFlat (f u) (nativeOrderedDuffyMap e u)) :
    nativeClass (nativeCubePullbackLoop p f hf) =
      ((Equiv.Perm.sign e : ℤˣ) : ℤ) • nativeClass (nativeDuffyCubeLoop p hp e) := by
  calc
    nativeClass (nativeCubePullbackLoop p f hf) =
        nativeClass (permuteCubeLoop (nativeDuffyCubeLoop p hp e) e) :=
      nativeClass_homotopic ⟨nativeCubeOrderedDuffyHomotopy p hp e f hf hfg⟩
    _ = _ := permuteCubeLoop_additiveClass _ e

private def HigherHurewicz.NativeSubdivision.orderedDuffyChart {n : ℕ} (e : Equiv.Perm (Fin n)) :
    NativeChamberChart e
    where
  toContinuousMap := nativeOrderedDuffyMap e
  zero_last := nativeOrderedDuffyMap_zero_last e
  zero_adjacent := nativeOrderedDuffyMap_zero_adjacent e
  one_first := nativeOrderedDuffyMap_one_first e
  one_adjacent := nativeOrderedDuffyMap_one_adjacent e

private theorem HigherHurewicz.NativeSubdivision.NativeChamberChart.commonOrderedDuffy {n : ℕ}
    {e : Equiv.Perm (Fin n)} (chart : HigherHurewicz.NativeSubdivision.NativeChamberChart e)
    (u : HigherHurewicz.NativeSubdivision.NativeCube (Fin n)) (hu : u ∈ Cube.boundary (Fin n)) :
    HigherHurewicz.NativeSubdivision.NativeCubeSameFlat (chart.toContinuousMap u)
      (HigherHurewicz.NativeSubdivision.nativeOrderedDuffyMap e u) :=
  chart.sameFlat (HigherHurewicz.NativeSubdivision.orderedDuffyChart e) u hu

private theorem HigherHurewicz.NativeSubdivision.nativeClass_eq_sum_partialChambers {n : ℕ}
    [Nontrivial (Fin n)] {X : Type*} [TopologicalSpace X] {x : X} (p : GenLoop (Fin n) X x)
    (hp : NativeCubeInternalBased p) (m : ℕ) (h : m ≤ n) :
    nativeClass p =
      ∑ e : Equiv.Perm (Fin m), nativeClass (extendedChamberLoop p hp h (orderedDuffyChart e)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_insertPermutation]
    calc
      nativeClass p =
          ∑ e : Equiv.Perm (Fin m),
            nativeClass (extendedChamberLoop p hp (Nat.le_of_succ_le h) (orderedDuffyChart e)) :=
        ih (Nat.le_of_succ_le h)
      _ =
          ∑ e : Equiv.Perm (Fin m),
            ∑ r : Fin (m + 1),
              nativeClass
                (extendedChamberLoop p hp h (orderedDuffyChart (insertPermutation e r))) := by
        apply Finset.sum_congr rfl
        intro e _
        rw [nativeClass_extendedChamber_eq_sum_insertions p hp h (orderedDuffyChart e)]
        apply Finset.sum_congr rfl
        intro r _
        exact
          nativeClass_extendedChamber_eq p hp h (insertChamberChart e r (orderedDuffyChart e))
            (orderedDuffyChart (insertPermutation e r))

@[simp]
private theorem HigherHurewicz.NativeSubdivision.nativeCubeSimplexQuotient_coordinate {n : ℕ}
    (e : Equiv.Perm (Fin n)) (u : NativeCube (Fin n)) (i : Fin n) :
    nativeCubeSimplexQuotient e u (e i) =
      HigherHurewicz.SimplexGeometry.prefixMinimum u (i.val + 1) :=
  Subtype.ext (HigherHurewicz.SimplexGeometry.cubeSimplex_quotient_coordinate e u i)

private theorem
    HigherHurewicz.NativeSubdivision.nativeCubeSimplexQuotient_coordinate_eq_zero {n : ℕ}
    (e : Equiv.Perm (Fin n)) (u : NativeCube (Fin n)) (i j : Fin n) (hij : i ≤ j) (hi : u i = 0) :
    nativeCubeSimplexQuotient e u (e j) = 0 := by
  rw [nativeCubeSimplexQuotient_coordinate]
  exact
    le_antisymm (hi ▸ HigherHurewicz.SimplexGeometry.prefixMinimum_le_coordinate u _ i (by omega))
      bot_le

private theorem
    HigherHurewicz.NativeSubdivision.nativeCubeSimplexQuotient_coordinate_zero_of_one {n : ℕ}
    (e : Equiv.Perm (Fin (n + 1))) (u : NativeCube (Fin (n + 1))) (hu : u 0 = 1) :
    nativeCubeSimplexQuotient e u (e 0) = 1 := by
  rw [nativeCubeSimplexQuotient_coordinate]
  change HigherHurewicz.SimplexGeometry.prefixMinimum u (0 + 1) = 1
  rw [HigherHurewicz.SimplexGeometry.prefixMinimum_succ u 0 (Nat.zero_lt_succ n),
    HigherHurewicz.SimplexGeometry.prefixMinimum_zero]
  simp [hu]

private theorem HigherHurewicz.NativeSubdivision.nativeCubeSimplexQuotient_adjacent_of_one {n : ℕ}
    (e : Equiv.Perm (Fin (n + 1))) (u : NativeCube (Fin (n + 1))) (i : Fin n)
    (hi : u i.succ = 1) :
    nativeCubeSimplexQuotient e u (e i.castSucc) = nativeCubeSimplexQuotient e u (e i.succ) := by
  rw [nativeCubeSimplexQuotient_coordinate, nativeCubeSimplexQuotient_coordinate,
    HigherHurewicz.SimplexGeometry.prefixMinimum_succ u i.succ.val i.succ.isLt]
  change
    HigherHurewicz.SimplexGeometry.prefixMinimum u (i.val + 1) =
      Min.min (HigherHurewicz.SimplexGeometry.prefixMinimum u (i.val + 1)) (u i.succ)
  rw [hi,
    min_eq_left
      (show HigherHurewicz.SimplexGeometry.prefixMinimum u (i.val + 1) ≤ 1 from
        (HigherHurewicz.SimplexGeometry.prefixMinimum u (i.val + 1)).property.2)]

private theorem HigherHurewicz.NativeSubdivision.nativeDuffyCube_simplex_sameFlat {n : ℕ}
    (e : Equiv.Perm (Fin n)) (u : NativeCube (Fin n)) (hu : u ∈ Cube.boundary (Fin n)) :
    NativeCubeSameFlat (nativeDuffyCube e u) (nativeCubeSimplexQuotient e u) := by
  obtain ⟨i, hi | hi⟩ := hu
  · exact
      .zero (e i) (nativeDuffyCube_coordinate_eq_zero e u i i le_rfl hi)
        (nativeCubeSimplexQuotient_coordinate_eq_zero e u i i le_rfl hi)
  · cases n with
    | zero => exact Fin.elim0 i
    | succ n =>
      cases i using Fin.cases with
      | zero =>
        exact
          .one (e 0) (nativeDuffyCube_coordinate_zero_of_one e u hi)
            (nativeCubeSimplexQuotient_coordinate_zero_of_one e u hi)
      | succ i =>
        exact
          .equal (e i.castSucc) (e i.succ)
            (e.injective.ne (by intro h; have := congrArg Fin.val h; simp at this))
            (nativeDuffyCube_adjacent_of_one e u i hi)
            (nativeCubeSimplexQuotient_adjacent_of_one e u i hi)

private def HigherHurewicz.NativeSubdivision.nativeDuffyCubeSimplexHomotopy {X : Type*}
    [TopologicalSpace X] {x : X} {n : ℕ} (p : GenLoop (Fin n) X x)
    (hp : NativeCubeInternalBased p) (e : Equiv.Perm (Fin n)) :
    (nativeDuffyCubeLoop p hp e).val.HomotopyRel
      (HigherHurewicz.SimplexGeometry.basedSimplexLoop (nativeBasedCubeSimplex p hp e)).val
      (Cube.boundary (Fin n)) :=
  nativeCubeLinearHomotopy p hp (nativeDuffyCube e) (nativeCubeSimplexQuotient e)
    (nativeDuffyCube_based p hp e) (nativeCubeSimplexQuotient_based p hp e)
    (nativeDuffyCube_simplex_sameFlat e)

private theorem
    HigherHurewicz.NativeSubdivision.nativeDuffyCube_homotopic_basedSimplexLoop {X : Type*}
    [TopologicalSpace X] {x : X} {n : ℕ} (p : GenLoop (Fin n) X x)
    (hp : NativeCubeInternalBased p) (e : Equiv.Perm (Fin n)) :
    GenLoop.Homotopic (nativeDuffyCubeLoop p hp e)
      (HigherHurewicz.SimplexGeometry.basedSimplexLoop (nativeBasedCubeSimplex p hp e)) :=
  ⟨nativeDuffyCubeSimplexHomotopy p hp e⟩

private theorem
    HigherHurewicz.NativeSubdivision.nativeDuffyCubeClass_eq_basedSimplexClass {X : Type*}
    [TopologicalSpace X] {x : X} {n : ℕ} (p : GenLoop (Fin n) X x)
    (hp : NativeCubeInternalBased p) (e : Equiv.Perm (Fin n)) :
    nativeClass (nativeDuffyCubeLoop p hp e) =
      HigherHurewicz.SimplexGeometry.basedSimplexClass (nativeBasedCubeSimplex p hp e) :=
  nativeClass_homotopic (nativeDuffyCube_homotopic_basedSimplexLoop p hp e)

private theorem HigherHurewicz.NativeSubdivision.nativeClass_commonOrderedSimplex {X : Type*}
    [TopologicalSpace X] {x : X} {n : ℕ} [Nontrivial (Fin n)] (p : GenLoop (Fin n) X x)
    (hp : NativeCubeInternalBased p) (e : Equiv.Perm (Fin n))
    (f : C(NativeCube (Fin n), NativeCube (Fin n)))
    (hf : ∀ u ∈ Cube.boundary (Fin n), p (f u) = x)
    (hfg : ∀ u ∈ Cube.boundary (Fin n), NativeCubeSameFlat (f u) (nativeOrderedDuffyMap e u)) :
    nativeClass (nativeCubePullbackLoop p f hf) =
      HigherHurewicz.CubeTriangulation.cubeOrientation e •
        HigherHurewicz.SimplexGeometry.basedSimplexClass (nativeBasedCubeSimplex p hp e) := by
  rw [nativeClass_commonOrderedDuffy p hp e f hf hfg, nativeDuffyCubeClass_eq_basedSimplexClass]
  rfl

private theorem HigherHurewicz.NativeSubdivision.nativeClass_chamber_eq_orientedSimplex {n : ℕ}
    [Nontrivial (Fin n)] {X : Type*} [TopologicalSpace X] {x : X} (p : GenLoop (Fin n) X x)
    (hp : NativeCubeInternalBased p) (e : Equiv.Perm (Fin n)) (chart : NativeChamberChart e) :
    nativeClass (extendedChamberLoop p hp (le_refl n) chart) =
      HigherHurewicz.CubeTriangulation.cubeOrientation e •
        HigherHurewicz.SimplexGeometry.basedSimplexClass (nativeBasedCubeSimplex p hp e) := by
  apply
    nativeClass_commonOrderedSimplex p hp e (extendCubeMap (le_refl n) chart.toContinuousMap)
      (extendedChamberMap_based p hp (le_refl n) chart)
  intro u hu
  rw [extendCubeMap_refl]
  exact chart.commonOrderedDuffy u hu

private theorem
    HigherHurewicz.NativeSubdivision.nativeClass_eq_sum_simplices {n : ℕ} [Nontrivial (Fin n)]
    {X : Type*} [TopologicalSpace X] {x : X} (p : GenLoop (Fin n) X x)
    (hp : NativeCubeInternalBased p) :
    nativeClass p =
      ∑ e : Equiv.Perm (Fin n),
        HigherHurewicz.CubeTriangulation.cubeOrientation e •
          HigherHurewicz.SimplexGeometry.basedSimplexClass (nativeBasedCubeSimplex p hp e) := by
  calc
    nativeClass p =
        ∑ e : Equiv.Perm (Fin n),
          nativeClass (extendedChamberLoop p hp (le_refl n) (orderedDuffyChart e)) :=
      nativeClass_eq_sum_partialChambers p hp n (le_refl n)
    _ = _ :=
      Finset.sum_congr rfl fun e _ =>
        nativeClass_chamber_eq_orientedSimplex p hp e (orderedDuffyChart e)

private theorem
    HigherHurewicz.NativeSubdivision.nativeCubeSubdivision_class {n : ℕ} [Nontrivial (Fin n)]
    {X : Type*} [TopologicalSpace X] {x : X} (p : GenLoop (Fin n) X x)
    (hp : NativeCubeInternalBased p) :
    Additive.ofMul (⟦p⟧ : π_ n X x) =
      ∑ e : Equiv.Perm (Fin n),
        HigherHurewicz.CubeTriangulation.cubeOrientation e •
          HigherHurewicz.SimplexGeometry.basedSimplexClass (nativeBasedCubeSimplex p hp e) :=
  nativeClass_eq_sum_simplices p hp

private theorem FourthHurewicz.fourSimplexClassOperator_cubeChain {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    (p : GenLoop (Fin 4) X x) :
    fourSimplexClassOperator x (cubeChain p) = Additive.ofMul (⟦p⟧ : π_ 4 X x) := by
  rw [fourSimplexClassOperator_cubeChain_sum]
  calc
    _ = Additive.ofMul (⟦normalizedCube x p⟧ : π_ 4 X x) := by
      simpa only [normalizedCube_simplex, basedFourSimplexClass] using
        (HigherHurewicz.NativeSubdivision.nativeCubeSubdivision_class (normalizedCube x p)
            (normalizedCube_internalBased x p)).symm
    _ = _ :=
      congrArg Additive.ofMul
        (Quotient.sound
          (show GenLoop.Homotopic (normalizedCube x p) p from
            ⟨(normalizationCubeHomotopy x p).symm⟩))

private def FourthHurewicz.hurewiczInverse {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)] :
    SingularMayerVietoris.SingularHomology X 4 →ₗ[ℤ] Additive (π_ 4 X x) :=
  HigherHurewicz.singularHomologyDesc 4 (fourSimplexClassOperator x)
    (fourSimplexClassOperator_boundary x)

@[simp]
private theorem FourthHurewicz.hurewiczInverse_cycleClass {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 4) :
    hurewiczInverse x
        (SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 4 c) =
      fourSimplexClassOperator x c.val :=
  HigherHurewicz.singularHomologyDesc_cycleClass 4 _ _ c

private theorem FourthHurewicz.hurewiczMap_comp_hurewiczInverse {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)] :
    (hurewiczMap x).comp (hurewiczInverse x) = LinearMap.id :=
  HigherHurewicz.comp_singularHomologyDesc_eq_id 4 (fourSimplexClassOperator x)
    (fourSimplexClassOperator_boundary x) (hurewiczMap x)
    (hurewiczMap_fourSimplexClassOperator_cycle x)

@[simp]
private theorem FourthHurewicz.hurewiczMap_hurewiczInverse {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    (c : SingularMayerVietoris.SingularHomology X 4) : hurewiczMap x (hurewiczInverse x c) = c :=
  LinearMap.congr_fun (hurewiczMap_comp_hurewiczInverse x) c

private theorem FourthHurewicz.hurewiczInverse_hurewiczMap_mk {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    (p : GenLoop (Fin 4) X x) :
    hurewiczInverse x (hurewiczMap x (Additive.ofMul (⟦p⟧ : π_ 4 X x))) =
      Additive.ofMul (⟦p⟧ : π_ 4 X x) := by
  rw [hurewiczMap_representative, hurewiczInverse_cycleClass]
  exact fourSimplexClassOperator_cubeChain x p

@[simp]
private theorem FourthHurewicz.hurewiczInverse_hurewiczMap {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    (a : Additive (π_ 4 X x)) : hurewiczInverse x (hurewiczMap x a) = a := by
  change
    hurewiczInverse x (hurewiczMap x (Additive.ofMul (Additive.toMul a))) =
      Additive.ofMul (Additive.toMul a)
  refine Quotient.inductionOn (Additive.toMul a) ?_
  intro p
  exact hurewiczInverse_hurewiczMap_mk x p

private theorem FourthHurewicz.hurewiczInverse_comp_hurewiczMap {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)] :
    (hurewiczInverse x).comp (hurewiczMap x) = LinearMap.id := by
  ext a
  exact hurewiczInverse_hurewiczMap x a


private def FourthHurewicz.hurewiczPi4Equiv {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)] :
    π_ 4 X x ≃* Multiplicative (SingularMayerVietoris.SingularHomology X 4)
    where
  __ := hurewiczPi4 x
  invFun c := Additive.toMul (hurewiczInverse x (Multiplicative.toAdd c))
  left_inv a := congrArg Additive.toMul (hurewiczInverse_hurewiczMap x (Additive.ofMul a))
  right_inv
    c := congrArg Multiplicative.ofAdd (hurewiczMap_hurewiczInverse x (Multiplicative.toAdd c))

private def
    FifthHurewicz.lowerSixSimplexHomotopy {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    (smp : FirstHurewicz.SingularSimplex X 6) : C((unitInterval) × FirstHurewicz.Simplex 6, X) :=
  SecondHurewicz.SimplyConnected.extendCoherentSimplexHomotopy
    (FourthHurewicz.normalizationFourSimplexHomotopy x)
    (FourthHurewicz.normalizationFiveSimplexHomotopy x)
    (FourthHurewicz.normalizationFiveHomotopy_face x)
    (FourthHurewicz.normalizationFiveSimplexHomotopy_zero x) smp

@[simp]
private theorem FifthHurewicz.lowerSixSimplexHomotopy_zero {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    (smp : FirstHurewicz.SingularSimplex X 6) (s : FirstHurewicz.Simplex 6) :
    lowerSixSimplexHomotopy x smp (0, s) = smp s :=
  SecondHurewicz.SimplyConnected.extendCoherentSimplexHomotopy_zero _ _ _ _ smp s

private theorem FifthHurewicz.lowerSixSimplexHomotopy_face {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)] :
    SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies 5
      (FourthHurewicz.normalizationFiveSimplexHomotopy x) (lowerSixSimplexHomotopy x) :=
  SecondHurewicz.SimplyConnected.extendCoherentSimplexHomotopy_face
    (FourthHurewicz.normalizationFourSimplexHomotopy x)
    (FourthHurewicz.normalizationFiveSimplexHomotopy x)
    (FourthHurewicz.normalizationFiveHomotopy_face x)
    (FourthHurewicz.normalizationFiveSimplexHomotopy_zero x)

private def FifthHurewicz.fourFiveSimplexHomotopy {X : Type} [TopologicalSpace X] (x : X)
    [Subsingleton (π_ 4 X x)] (smp : FirstHurewicz.SingularSimplex X 5) :
    C((unitInterval) × FirstHurewicz.Simplex 5, X) :=
  SecondHurewicz.SimplyConnected.extendCoherentSimplexHomotopy
    (SecondHurewicz.SimplyConnected.stationarySimplexHomotopy 3)
    (HigherHurewicz.simplexStraighteningHomotopy 4 x)
    (HigherHurewicz.simplexStraighteningHomotopy_face 3 x)
    (HigherHurewicz.simplexStraighteningHomotopy_zero 4 x) smp

@[simp]
private theorem FifthHurewicz.fourFiveSimplexHomotopy_zero {X : Type} [TopologicalSpace X] (x : X)
    [Subsingleton (π_ 4 X x)] (smp : FirstHurewicz.SingularSimplex X 5)
    (s : FirstHurewicz.Simplex 5) : fourFiveSimplexHomotopy x smp (0, s) = smp s :=
  SecondHurewicz.SimplyConnected.extendCoherentSimplexHomotopy_zero _ _ _ _ smp s

private theorem FifthHurewicz.fourFiveSimplexHomotopy_face {X : Type} [TopologicalSpace X] (x : X)
    [Subsingleton (π_ 4 X x)] :
    SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies 4
      (HigherHurewicz.simplexStraighteningHomotopy 4 x) (fourFiveSimplexHomotopy x) :=
  SecondHurewicz.SimplyConnected.extendCoherentSimplexHomotopy_face
    (SecondHurewicz.SimplyConnected.stationarySimplexHomotopy 3)
    (HigherHurewicz.simplexStraighteningHomotopy 4 x)
    (HigherHurewicz.simplexStraighteningHomotopy_face 3 x)
    (HigherHurewicz.simplexStraighteningHomotopy_zero 4 x)

@[simp]
private theorem FifthHurewicz.fourFiveSimplexHomotopy_const {X : Type} [TopologicalSpace X] (x : X)
    [Subsingleton (π_ 4 X x)] :
    fourFiveSimplexHomotopy x (ContinuousMap.const (FirstHurewicz.Simplex 5) x) =
      ContinuousMap.const ((unitInterval) × FirstHurewicz.Simplex 5) x :=
  ThirdHurewicz.extendCoherentSimplexHomotopy_const
    (SecondHurewicz.SimplyConnected.stationarySimplexHomotopy 3)
    (HigherHurewicz.simplexStraighteningHomotopy 4 x)
    (HigherHurewicz.simplexStraighteningHomotopy_face 3 x)
    (HigherHurewicz.simplexStraighteningHomotopy_zero 4 x) x
    (HigherHurewicz.simplexStraighteningHomotopy_const 4 x)

private def FifthHurewicz.fourSixSimplexHomotopy {X : Type} [TopologicalSpace X] (x : X)
    [Subsingleton (π_ 4 X x)] (smp : FirstHurewicz.SingularSimplex X 6) :
    C((unitInterval) × FirstHurewicz.Simplex 6, X) :=
  SecondHurewicz.SimplyConnected.extendCoherentSimplexHomotopy
    (HigherHurewicz.simplexStraighteningHomotopy 4 x) (fourFiveSimplexHomotopy x)
    (fourFiveSimplexHomotopy_face x) (fourFiveSimplexHomotopy_zero x) smp

@[simp]
private theorem FifthHurewicz.fourSixSimplexHomotopy_zero {X : Type} [TopologicalSpace X] (x : X)
    [Subsingleton (π_ 4 X x)] (smp : FirstHurewicz.SingularSimplex X 6)
    (s : FirstHurewicz.Simplex 6) : fourSixSimplexHomotopy x smp (0, s) = smp s :=
  SecondHurewicz.SimplyConnected.extendCoherentSimplexHomotopy_zero _ _ _ _ smp s

private theorem FifthHurewicz.fourSixSimplexHomotopy_face {X : Type} [TopologicalSpace X] (x : X)
    [Subsingleton (π_ 4 X x)] :
    SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies 5 (fourFiveSimplexHomotopy x)
      (fourSixSimplexHomotopy x) :=
  SecondHurewicz.SimplyConnected.extendCoherentSimplexHomotopy_face
    (HigherHurewicz.simplexStraighteningHomotopy 4 x) (fourFiveSimplexHomotopy x)
    (fourFiveSimplexHomotopy_face x) (fourFiveSimplexHomotopy_zero x)

private def FifthHurewicz.normalizationFourSimplexHomotopy {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] :
    FirstHurewicz.SingularSimplex X 4 → C((unitInterval) × FirstHurewicz.Simplex 4, X) :=
  ThirdHurewicz.composeSimplexHomotopies (FourthHurewicz.normalizationFourSimplexHomotopy x)
    (HigherHurewicz.simplexStraighteningHomotopy 4 x)
    (FourthHurewicz.normalizationFourSimplexHomotopy_zero x)
    (HigherHurewicz.simplexStraighteningHomotopy_zero 4 x)

private def FifthHurewicz.normalizationFiveSimplexHomotopy {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] :
    FirstHurewicz.SingularSimplex X 5 → C((unitInterval) × FirstHurewicz.Simplex 5, X) :=
  ThirdHurewicz.composeSimplexHomotopies (FourthHurewicz.normalizationFiveSimplexHomotopy x)
    (fourFiveSimplexHomotopy x) (FourthHurewicz.normalizationFiveSimplexHomotopy_zero x)
    (fourFiveSimplexHomotopy_zero x)

private def FifthHurewicz.normalizationSixSimplexHomotopy {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] :
    FirstHurewicz.SingularSimplex X 6 → C((unitInterval) × FirstHurewicz.Simplex 6, X) :=
  ThirdHurewicz.composeSimplexHomotopies (lowerSixSimplexHomotopy x) (fourSixSimplexHomotopy x)
    (lowerSixSimplexHomotopy_zero x) (fourSixSimplexHomotopy_zero x)

@[simp]
private theorem FifthHurewicz.normalizationFiveSimplexHomotopy_zero {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] (smp : FirstHurewicz.SingularSimplex X 5)
    (s : FirstHurewicz.Simplex 5) : normalizationFiveSimplexHomotopy x smp (0, s) = smp s :=
  ThirdHurewicz.composeSimplexHomotopies_zero _ _ _ _ smp s

@[simp]
private theorem FifthHurewicz.normalizationSixSimplexHomotopy_zero {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] (smp : FirstHurewicz.SingularSimplex X 6)
    (s : FirstHurewicz.Simplex 6) : normalizationSixSimplexHomotopy x smp (0, s) = smp s :=
  ThirdHurewicz.composeSimplexHomotopies_zero _ _ _ _ smp s

private theorem FifthHurewicz.normalizationHomotopy_face {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] :
    SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies 4 (normalizationFourSimplexHomotopy x)
      (normalizationFiveSimplexHomotopy x) :=
  ThirdHurewicz.composeSimplexHomotopies_face (FourthHurewicz.normalizationFourSimplexHomotopy x)
    (HigherHurewicz.simplexStraighteningHomotopy 4 x)
    (FourthHurewicz.normalizationFiveSimplexHomotopy x) (fourFiveSimplexHomotopy x)
    (FourthHurewicz.normalizationFourSimplexHomotopy_zero x)
    (HigherHurewicz.simplexStraighteningHomotopy_zero 4 x)
    (FourthHurewicz.normalizationFiveSimplexHomotopy_zero x) (fourFiveSimplexHomotopy_zero x)
    (FourthHurewicz.normalizationFiveHomotopy_face x) (fourFiveSimplexHomotopy_face x)

private theorem FifthHurewicz.normalizationSixHomotopy_face {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] :
    SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies 5 (normalizationFiveSimplexHomotopy x)
      (normalizationSixSimplexHomotopy x) :=
  ThirdHurewicz.composeSimplexHomotopies_face (FourthHurewicz.normalizationFiveSimplexHomotopy x)
    (fourFiveSimplexHomotopy x) (lowerSixSimplexHomotopy x) (fourSixSimplexHomotopy x)
    (FourthHurewicz.normalizationFiveSimplexHomotopy_zero x) (fourFiveSimplexHomotopy_zero x)
    (lowerSixSimplexHomotopy_zero x) (fourSixSimplexHomotopy_zero x)
    (lowerSixSimplexHomotopy_face x) (fourSixSimplexHomotopy_face x)

@[simp]
private theorem FifthHurewicz.normalizationFourSimplexHomotopy_const {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] :
    normalizationFourSimplexHomotopy x (ContinuousMap.const (FirstHurewicz.Simplex 4) x) =
      ContinuousMap.const ((unitInterval) × FirstHurewicz.Simplex 4) x :=
  ThirdHurewicz.composeSimplexHomotopies_const (FourthHurewicz.normalizationFourSimplexHomotopy x)
    (HigherHurewicz.simplexStraighteningHomotopy 4 x)
    (FourthHurewicz.normalizationFourSimplexHomotopy_zero x)
    (HigherHurewicz.simplexStraighteningHomotopy_zero 4 x) x
    (FourthHurewicz.normalizationFourSimplexHomotopy_const x)
    (HigherHurewicz.simplexStraighteningHomotopy_const 4 x)

@[simp]
private theorem FifthHurewicz.normalizationFiveSimplexHomotopy_const {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] :
    normalizationFiveSimplexHomotopy x (ContinuousMap.const (FirstHurewicz.Simplex 5) x) =
      ContinuousMap.const ((unitInterval) × FirstHurewicz.Simplex 5) x :=
  ThirdHurewicz.composeSimplexHomotopies_const (FourthHurewicz.normalizationFiveSimplexHomotopy x)
    (fourFiveSimplexHomotopy x) (FourthHurewicz.normalizationFiveSimplexHomotopy_zero x)
    (fourFiveSimplexHomotopy_zero x) x (FourthHurewicz.normalizationFiveSimplexHomotopy_const x)
    (fourFiveSimplexHomotopy_const x)

@[simp]
private theorem
    FifthHurewicz.normalizationFourSimplexHomotopy_endpoint {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] (smp : FirstHurewicz.SingularSimplex X 4) :
    SecondHurewicz.SimplyConnected.timeSlice (normalizationFourSimplexHomotopy x smp) 1 =
      ContinuousMap.const (FirstHurewicz.Simplex 4) x := by
  rw [normalizationFourSimplexHomotopy, ThirdHurewicz.timeSlice_composeSimplexHomotopies_one,
    FourthHurewicz.normalizationFourSimplexHomotopy_endpoint]
  ext s
  exact
    HigherHurewicz.simplexStraighteningHomotopy_one 4 x
      (FourthHurewicz.normalizedFourSimplex x smp).val
      (FourthHurewicz.normalizedFourSimplex x smp).property s

private abbrev FifthHurewicz.fiveSimplexBoundary : Set (FirstHurewicz.Simplex 5) :=
  SecondHurewicz.SimplyConnected.simplexBoundary 5

private abbrev FifthHurewicz.BasedFiveSimplex {X : Type*} [TopologicalSpace X] (x : X) :=
  HigherHurewicz.SimplexGeometry.BasedSimplex 5 x

private abbrev FifthHurewicz.basedFiveSimplexLoop {X : Type*} [TopologicalSpace X] {x : X}
    (τ : BasedFiveSimplex x) : GenLoop (Fin 5) X x :=
  HigherHurewicz.SimplexGeometry.basedSimplexLoop τ

private abbrev FifthHurewicz.basedFiveSimplexClass {X : Type*} [TopologicalSpace X] {x : X}
    (τ : BasedFiveSimplex x) : Additive (π_ 5 X x) :=
  HigherHurewicz.SimplexGeometry.basedSimplexClass τ

private theorem FifthHurewicz.basedFiveSimplex_face {X : Type*} [TopologicalSpace X] {x : X}
    (τ : BasedFiveSimplex x) (i : Fin 6) :
    τ.val.comp (FirstHurewicz.simplexFace 4 i) =
      ContinuousMap.const (FirstHurewicz.Simplex 4) x :=
  HigherHurewicz.SimplexGeometry.basedSimplex_face τ i

private def
    FifthHurewicz.normalizedFiveSimplex {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)] [Subsingleton (π_ 4 X x)]
    (smp : FirstHurewicz.SingularSimplex X 5) : BasedFiveSimplex x :=
  ⟨SecondHurewicz.SimplyConnected.timeSlice (normalizationFiveSimplexHomotopy x smp) 1,
    HigherHurewicz.simplexEndpoint_boundary (normalizationFourSimplexHomotopy x)
      (normalizationFiveSimplexHomotopy x) (normalizationHomotopy_face x) x
      (normalizationFourSimplexHomotopy_endpoint x) smp⟩

private theorem
    FifthHurewicz.normalizationFiveSimplexHomotopy_endpoint {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] (smp : FirstHurewicz.SingularSimplex X 5) :
    SecondHurewicz.SimplyConnected.timeSlice (normalizationFiveSimplexHomotopy x smp) 1 =
      (normalizedFiveSimplex x smp).val :=
  rfl

private def
    FifthHurewicz.normalizedSixSimplexMap {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)] [Subsingleton (π_ 4 X x)]
    (smp : FirstHurewicz.SingularSimplex X 6) : FirstHurewicz.SingularSimplex X 6 :=
  SecondHurewicz.SimplyConnected.timeSlice (normalizationSixSimplexHomotopy x smp) 1

private theorem FifthHurewicz.normalizedSixSimplexMap_face {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] (smp : FirstHurewicz.SingularSimplex X 6) (i : Fin 7) :
    (normalizedSixSimplexMap x smp).comp (FirstHurewicz.simplexFace 5 i) =
      (normalizedFiveSimplex x (smp.comp (FirstHurewicz.simplexFace 5 i))).val :=
  SecondHurewicz.SimplyConnected.timeSlice_face (normalizationSixHomotopy_face x) smp i 1

private theorem FifthHurewicz.normalizedSixSimplexMap_face_boundary {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] (smp : FirstHurewicz.SingularSimplex X 6) (i : Fin 7)
    (s : FirstHurewicz.Simplex 5) (hs : s ∈ fiveSimplexBoundary) :
    normalizedSixSimplexMap x smp (FirstHurewicz.simplexFace 5 i s) = x := by
  have hf :=
    congrArg (fun f : C(FirstHurewicz.Simplex 5, X) => f s) (normalizedSixSimplexMap_face x smp i)
  exact
    hf.trans ((normalizedFiveSimplex x (smp.comp (FirstHurewicz.simplexFace 5 i))).property s hs)

private def FifthHurewicz.fiveSimplexClassOperator {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] : FirstHurewicz.Chains X 5 →ₗ[ℤ] Additive (π_ 5 X x) :=
  FirstHurewicz.chainLift X 5 fun smp => basedFiveSimplexClass (normalizedFiveSimplex x smp)

@[simp]
private theorem FifthHurewicz.fiveSimplexClassOperator_simplex {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] (smp : FirstHurewicz.SingularSimplex X 5) :
    fiveSimplexClassOperator x (FirstHurewicz.simplexChain X 5 smp) =
      basedFiveSimplexClass (normalizedFiveSimplex x smp) :=
  FirstHurewicz.chainLift_simplex X 5 _ smp

private abbrev FifthHurewicz.BasedSixSimplex {X : Type*} [TopologicalSpace X] (x : X) :=
  HigherHurewicz.SimplexGeometry.BasedSimplexBoundary 6 x

private abbrev FifthHurewicz.basedSixSimplexFace {X : Type*} [TopologicalSpace X] {x : X}
    (τ : BasedSixSimplex x) (i : Fin 7) : BasedFiveSimplex x :=
  HigherHurewicz.SimplexGeometry.basedSimplexBoundaryFace τ i

private def FifthHurewicz.BasedSixSimplex.ofFaces {X : Type*} [TopologicalSpace X] {x : X}
    (τ : C(FirstHurewicz.Simplex 6, X))
    (h :
      ∀ i : Fin 7,
        ∀ s ∈ FifthHurewicz.fiveSimplexBoundary, (τ.comp (FirstHurewicz.simplexFace 5 i)) s = x) :
    FifthHurewicz.BasedSixSimplex x :=
  HigherHurewicz.SimplexGeometry.BasedSimplexBoundary.ofFaces τ h

private theorem
    FifthHurewicz.basedSixSimplex_signed_relation {X : Type*} [TopologicalSpace X] {x : X}
    (τ : BasedSixSimplex x) :
    (∑ i : Fin 7, (-1 : ℤ) ^ i.val • basedFiveSimplexClass (basedSixSimplexFace τ i)) = 0 :=
  HigherHurewicz.SimplexGeometry.basedSimplexBoundary_signed_relation (n := 3) τ

private def
    FifthHurewicz.normalizedSixSimplex {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)] [Subsingleton (π_ 4 X x)]
    (smp : FirstHurewicz.SingularSimplex X 6) : BasedSixSimplex x :=
  BasedSixSimplex.ofFaces (normalizedSixSimplexMap x smp)
    (normalizedSixSimplexMap_face_boundary x smp)

@[simp]
private theorem FifthHurewicz.normalizedSixSimplex_face {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] (smp : FirstHurewicz.SingularSimplex X 6) (i : Fin 7) :
    basedSixSimplexFace (normalizedSixSimplex x smp) i =
      normalizedFiveSimplex x (smp.comp (FirstHurewicz.simplexFace 5 i)) := by
  apply Subtype.ext
  exact normalizedSixSimplexMap_face x smp i

private theorem
    FifthHurewicz.normalizedFiveSimplex_boundary_relation {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] (smp : FirstHurewicz.SingularSimplex X 6) :
    ∑ i : Fin 7,
        (-1 : ℤ) ^ i.val •
          basedFiveSimplexClass
            (normalizedFiveSimplex x (smp.comp (FirstHurewicz.simplexFace 5 i))) =
      0 := by
  simpa only [normalizedSixSimplex_face] using
    basedSixSimplex_signed_relation (normalizedSixSimplex x smp)

private theorem FifthHurewicz.fiveSimplexClassOperator_boundary {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] (b : FirstHurewicz.Chains X 6) :
    fiveSimplexClassOperator x (((FirstHurewicz.singularComplex X).d 6 5).hom b) = 0 := by
  have h : (fiveSimplexClassOperator x).comp ((FirstHurewicz.singularComplex X).d 6 5).hom = 0 := by
    apply FirstHurewicz.chainMap_ext X 6
    intro smp
    simp only [LinearMap.comp_apply, FirstHurewicz.boundary_simplex, map_sum, map_zsmul,
      fiveSimplexClassOperator_simplex, LinearMap.zero_apply]
    exact normalizedFiveSimplex_boundary_relation x smp
  exact LinearMap.congr_fun h b

private def
    FifthHurewicz.normalizedCube {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)] [Subsingleton (π_ 4 X x)]
    (p : GenLoop (Fin 5) X x) : GenLoop (Fin 5) X x :=
  HigherHurewicz.CubeGluing.coherentCubeEndpoint (normalizationFourSimplexHomotopy x)
    (normalizationFiveSimplexHomotopy x) (normalizationHomotopy_face x)
    (normalizationFourSimplexHomotopy_const x) p

private theorem
    FifthHurewicz.normalizedCube_cell {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)] [Subsingleton (π_ 4 X x)]
    (p : GenLoop (Fin 5) X x) (e : Equiv.Perm (Fin 5)) :
    (normalizedCube x p).val.comp (HigherHurewicz.CubeTriangulation.cubeSimplex e) =
      (normalizedFiveSimplex x
          (p.val.comp (HigherHurewicz.CubeTriangulation.cubeSimplex e))).val :=
  HigherHurewicz.CubeGluing.coherentCubeEndpoint_cell (normalizationFourSimplexHomotopy x)
    (normalizationFiveSimplexHomotopy x) (normalizationHomotopy_face x)
    (normalizationFourSimplexHomotopy_const x) p e

private def FifthHurewicz.normalizationCubeHomotopy {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] (p : GenLoop (Fin 5) X x) :
    p.val.HomotopyRel (normalizedCube x p).val (Cube.boundary (Fin 5)) :=
  HigherHurewicz.CubeGluing.coherentCubeHomotopy (normalizationFourSimplexHomotopy x)
    (normalizationFiveSimplexHomotopy x) (normalizationHomotopy_face x)
    (normalizationFourSimplexHomotopy_const x) (normalizationFiveSimplexHomotopy_zero x) p

private theorem FifthHurewicz.normalizedCube_internalBased {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] (p : GenLoop (Fin 5) X x) (u : Fin 5 → (unitInterval)) (i j : Fin 5)
    (hij : i ≠ j) (hu : u i = u j) : normalizedCube x p u = x :=
  HigherHurewicz.coherentCubeEndpoint_internalBased (normalizationFourSimplexHomotopy x)
    (normalizationFiveSimplexHomotopy x) (normalizationHomotopy_face x)
    (normalizationFourSimplexHomotopy_const x) (normalizationFourSimplexHomotopy_endpoint x) p u i
    j hij hu

private theorem FifthHurewicz.normalizedCube_simplex {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] (p : GenLoop (Fin 5) X x) (e : Equiv.Perm (Fin 5)) :
    HigherHurewicz.NativeSubdivision.nativeBasedCubeSimplex (normalizedCube x p)
        (normalizedCube_internalBased x p) e =
      normalizedFiveSimplex x (p.val.comp (HigherHurewicz.CubeTriangulation.cubeSimplex e)) := by
  apply Subtype.ext
  exact normalizedCube_cell x p e

private abbrev FifthHurewicz.Remaining :=
  { j : Fin 5 // j ≠ 0 }

private def
    FifthHurewicz.remainingCoordinates : C(Fin 4 → (unitInterval), Remaining → (unitInterval))
    where
  toFun u j := u (j.val.pred j.property)
  continuous_toFun := by fun_prop

@[simp]
private theorem FifthHurewicz.remainingCoordinates_succ (u : Fin 4 → (unitInterval)) (i : Fin 4) :
    remainingCoordinates u ⟨i.succ, Fin.succ_ne_zero i⟩ = u i := by simp [remainingCoordinates]

private theorem FifthHurewicz.remainingCoordinates_boundary {u : Fin 4 → (unitInterval)}
    (h : u ∈ Cube.boundary (Fin 4)) : remainingCoordinates u ∈ Cube.boundary Remaining := by
  obtain ⟨i, hi⟩ := h
  exact ⟨⟨i.succ, Fin.succ_ne_zero i⟩, by simpa using hi⟩

private abbrev FifthHurewicz.BasedLoopSpace {X : Type} [TopologicalSpace X] (x : X) :=
  GenLoop Remaining X x

private def FifthHurewicz.evaluation {X : Type} [TopologicalSpace X] (x : X) :
    C(BasedLoopSpace x × (Fin 4 → (unitInterval)), X)
    where
  toFun z := z.1 (remainingCoordinates z.2)
  continuous_toFun := by fun_prop

private theorem FifthHurewicz.evaluation_boundary {X : Type} [TopologicalSpace X] (x : X)
    (p : BasedLoopSpace x) (u : Fin 4 → (unitInterval)) (hu : u ∈ Cube.boundary (Fin 4)) :
    evaluation x (p, u) = x :=
  GenLoop.boundary p _ (remainingCoordinates_boundary hu)

private theorem FifthHurewicz.evaluation_comp_boundary {X : Type} [TopologicalSpace X] {A : Type}
    [TopologicalSpace A] (x : X) (f : C(A, Fin 4 → (unitInterval)))
    (hf : ∀ a, f a ∈ Cube.boundary (Fin 4)) :
    (evaluation x).comp ((ContinuousMap.id (BasedLoopSpace x)).prodMap f) =
      ContinuousMap.const (BasedLoopSpace x × A) x := by
  ext z
  exact evaluation_boundary x z.1 (f z.2) (hf z.2)

private def FifthHurewicz.cubeCoordinates :
    C((unitInterval) × (Fin 4 → (unitInterval)), Fin 5 → (unitInterval))
    where
  toFun z := Cube.insertAt (0 : Fin 5) (z.1, remainingCoordinates z.2)
  continuous_toFun := by fun_prop

@[simp]
private theorem FifthHurewicz.cubeCoordinates_zero (z : (unitInterval) × (Fin 4 → (unitInterval))) :
    cubeCoordinates z 0 = z.1 := by
  simp [cubeCoordinates, Cube.insertAt, Homeomorph.funSplitAt_symm_apply]

@[simp]
private theorem FifthHurewicz.cubeCoordinates_succ (z : (unitInterval) × (Fin 4 → (unitInterval)))
    (i : Fin 4) : cubeCoordinates z i.succ = z.2 i := by
  simp [cubeCoordinates, Cube.insertAt, Homeomorph.funSplitAt_symm_apply, remainingCoordinates]

private def
    FifthHurewicz.cubeMap {X : Type} [TopologicalSpace X] {x : X} (p : GenLoop (Fin 5) X x) :
    C((unitInterval) × (Fin 4 → (unitInterval)), X) :=
  p.val.comp cubeCoordinates

private theorem FifthHurewicz.evaluation_comp_toLoop {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 5) X x) :
    (evaluation x).comp
        ((GenLoop.toLoop (0 : Fin 5) p).toContinuousMap.prodMap
          (ContinuousMap.id (Fin 4 → (unitInterval)))) =
      cubeMap p := by
  ext z
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def FifthHurewicz.remainingCubeSideFirst (t : (unitInterval)) :
    C(Fin 3 → (unitInterval), Fin 4 → (unitInterval)) :=
  FourthHurewicz.cubeCoordinates.comp (PeriodTorusHigherHomology.crossInsertLeft t)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def FifthHurewicz.remainingCubeSide {A : Type} [TopologicalSpace A]
    (f : C(A, Fin 3 → (unitInterval))) : C((unitInterval) × A, Fin 4 → (unitInterval)) :=
  FourthHurewicz.cubeCoordinates.comp ((ContinuousMap.id (unitInterval)).prodMap f)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem
    FifthHurewicz.remainingCubeSideFirst_boundary (t : (unitInterval)) (ht : t = 0 ∨ t = 1)
    (u : Fin 3 → (unitInterval)) : remainingCubeSideFirst t u ∈ Cube.boundary (Fin 4) := by
  refine ⟨0, ?_⟩
  change FourthHurewicz.cubeCoordinates (t, u) 0 = 0 ∨ FourthHurewicz.cubeCoordinates (t, u) 0 = 1
  simpa only [FourthHurewicz.cubeCoordinates_zero] using ht

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem FifthHurewicz.remainingCubeSide_boundary {A : Type} [TopologicalSpace A]
    (f : C(A, Fin 3 → (unitInterval))) (hf : ∀ a, f a ∈ Cube.boundary (Fin 3))
    (z : (unitInterval) × A) : remainingCubeSide f z ∈ Cube.boundary (Fin 4) := by
  obtain ⟨i, hi⟩ := hf z.2
  refine ⟨i.succ, ?_⟩
  change
    FourthHurewicz.cubeCoordinates (z.1, f z.2) i.succ = 0 ∨
      FourthHurewicz.cubeCoordinates (z.1, f z.2) i.succ = 1
  simpa only [FourthHurewicz.cubeCoordinates_succ] using hi

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem FifthHurewicz.remainingCubeSide_chain {A : Type} [TopologicalSpace A] (k : ℕ)
    (f : C(A, Fin 3 → (unitInterval))) (b : FirstHurewicz.Chains A k) :
    FirstHurewicz.inducedChain FourthHurewicz.cubeCoordinates (k + 1)
        (PeriodTorusHigherHomology.crossProductEdge (unitInterval) (Fin 3 → (unitInterval)) k
          SecondHurewicz.intervalChain (FirstHurewicz.inducedChain f k b)) =
      FirstHurewicz.inducedChain (remainingCubeSide f) (k + 1)
        (PeriodTorusHigherHomology.crossProductEdge (unitInterval) A k
          SecondHurewicz.intervalChain b) := by
  have h :=
    PeriodTorusHigherHomology.crossProductEdge_natural (ContinuousMap.id (unitInterval)) f k
      SecondHurewicz.intervalChain b
  rw [FirstHurewicz.inducedChain_id, LinearMap.id_apply] at h
  rw [← h]
  change
    ((FirstHurewicz.inducedChain FourthHurewicz.cubeCoordinates (k + 1)).comp
          (FirstHurewicz.inducedChain ((ContinuousMap.id (unitInterval)).prodMap f) (k + 1)))
        _ =
      _
  rw [← FirstHurewicz.inducedChain_comp]
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def FifthHurewicz.productThreeIntervalChain :
    FirstHurewicz.Chains ((unitInterval) × ((unitInterval) × (unitInterval))) 3 :=
  PeriodTorusHigherHomology.crossProductEdge (unitInterval) ((unitInterval) × (unitInterval)) 2
    SecondHurewicz.intervalChain SecondHurewicz.productSquareChain

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem FifthHurewicz.remainingCubeChain_boundary :
    ((FirstHurewicz.singularComplex (Fin 4 → (unitInterval))).d 4 3).hom
        FourthHurewicz.fundamentalCubeChain =
      FirstHurewicz.inducedChain (remainingCubeSideFirst 1) 3 ThirdHurewicz.fundamentalCubeChain -
          FirstHurewicz.inducedChain (remainingCubeSideFirst 0) 3
            ThirdHurewicz.fundamentalCubeChain -
        (FirstHurewicz.inducedChain (remainingCubeSide (FourthHurewicz.remainingCubeSideFirst 1))
              3 ThirdHurewicz.productCubeChain -
            FirstHurewicz.inducedChain
              (remainingCubeSide (FourthHurewicz.remainingCubeSideFirst 0)) 3
              ThirdHurewicz.productCubeChain -
          (FirstHurewicz.inducedChain
                (remainingCubeSide
                  (FourthHurewicz.remainingCubeSide (ThirdHurewicz.squareSideLeft 1)))
                3 productThreeIntervalChain -
              FirstHurewicz.inducedChain
                (remainingCubeSide
                  (FourthHurewicz.remainingCubeSide (ThirdHurewicz.squareSideLeft 0)))
                3 productThreeIntervalChain -
            (FirstHurewicz.inducedChain
                (remainingCubeSide
                  (FourthHurewicz.remainingCubeSide (ThirdHurewicz.squareSideRight 1)))
                3 productThreeIntervalChain -
              FirstHurewicz.inducedChain
                (remainingCubeSide
                  (FourthHurewicz.remainingCubeSide (ThirdHurewicz.squareSideRight 0)))
                3 productThreeIntervalChain))) := by
  have hpoint (t : (unitInterval)) :
    PeriodTorusHigherHomology.crossProductZeroLeft (unitInterval) (Fin 3 → (unitInterval)) 3
        (FirstHurewicz.pointChain t) ThirdHurewicz.fundamentalCubeChain =
      FirstHurewicz.inducedChain (PeriodTorusHigherHomology.crossInsertLeft t) 3
        ThirdHurewicz.fundamentalCubeChain := by
    rw [FirstHurewicz.pointChain, PeriodTorusHigherHomology.crossProductZeroLeft_simplex_left]
    rfl
  have hfirst (t : (unitInterval)) :
    FirstHurewicz.inducedChain FourthHurewicz.cubeCoordinates 3
        (FirstHurewicz.inducedChain (PeriodTorusHigherHomology.crossInsertLeft t) 3
          ThirdHurewicz.fundamentalCubeChain) =
      FirstHurewicz.inducedChain (remainingCubeSideFirst t) 3
        ThirdHurewicz.fundamentalCubeChain := by
    rw [remainingCubeSideFirst, FirstHurewicz.inducedChain_comp]
    rfl
  rw [FourthHurewicz.fundamentalCubeChain, ← FirstHurewicz.inducedChain_boundary]
  change
    FirstHurewicz.inducedChain FourthHurewicz.cubeCoordinates 3
        (((FirstHurewicz.singularComplex ((unitInterval) × (Fin 3 → (unitInterval)))).d 4 3).hom
          (PeriodTorusHigherHomology.crossProductEdge (unitInterval) (Fin 3 → (unitInterval)) 3
            SecondHurewicz.intervalChain ThirdHurewicz.fundamentalCubeChain)) =
      _
  rw [PeriodTorusHigherHomology.crossProductEdge_boundary 2]
  change
    FirstHurewicz.inducedChain FourthHurewicz.cubeCoordinates 3
        (PeriodTorusHigherHomology.crossProductZeroLeft (unitInterval) (Fin 3 → (unitInterval)) 3
            (FirstHurewicz.boundaryOne (unitInterval) SecondHurewicz.intervalChain)
            ThirdHurewicz.fundamentalCubeChain -
          PeriodTorusHigherHomology.crossProductEdge (unitInterval) (Fin 3 → (unitInterval)) 2
            SecondHurewicz.intervalChain
            (((FirstHurewicz.singularComplex (Fin 3 → (unitInterval))).d 3 2).hom
              ThirdHurewicz.fundamentalCubeChain)) =
      _
  rw [SecondHurewicz.intervalChain_boundary, FourthHurewicz.remainingCubeChain_boundary]
  simp only [map_sub, LinearMap.sub_apply, hpoint, hfirst, remainingCubeSide_chain]
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem FifthHurewicz.evaluated_edge_boundaryMap {X A : Type} [TopologicalSpace X]
    [TopologicalSpace A] (x : X) (a : FirstHurewicz.Chains (BasedLoopSpace x) 1) (k : ℕ)
    (b : FirstHurewicz.Chains A k) (f : C(A, Fin 4 → (unitInterval)))
    (hf : ∀ t, f t ∈ Cube.boundary (Fin 4)) :
    FirstHurewicz.inducedChain (evaluation x) (k + 1)
        (PeriodTorusHigherHomology.crossProductEdge (BasedLoopSpace x) (Fin 4 → (unitInterval)) k
          a (FirstHurewicz.inducedChain f k b)) =
      FirstHurewicz.inducedChain (ContinuousMap.const (BasedLoopSpace x × A) x) (k + 1)
        (PeriodTorusHigherHomology.crossProductEdge (BasedLoopSpace x) A k a b) := by
  have h :=
    PeriodTorusHigherHomology.crossProductEdge_natural (ContinuousMap.id (BasedLoopSpace x)) f k a
      b
  rw [FirstHurewicz.inducedChain_id, LinearMap.id_apply] at h
  rw [← h]
  change
    ((FirstHurewicz.inducedChain (evaluation x) (k + 1)).comp
          (FirstHurewicz.inducedChain ((ContinuousMap.id (BasedLoopSpace x)).prodMap f) (k + 1)))
        _ =
      _
  rw [← FirstHurewicz.inducedChain_comp, evaluation_comp_boundary x f hf]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem FifthHurewicz.evaluated_triangle_boundaryMap {X A : Type} [TopologicalSpace X]
    [TopologicalSpace A] (x : X) (a : FirstHurewicz.Chains (BasedLoopSpace x) 2) (k : ℕ)
    (b : FirstHurewicz.Chains A k) (f : C(A, Fin 4 → (unitInterval)))
    (hf : ∀ t, f t ∈ Cube.boundary (Fin 4)) :
    FirstHurewicz.inducedChain (evaluation x) (k + 2)
        (PeriodTorusHigherHomology.crossProductTriangle (BasedLoopSpace x)
          (Fin 4 → (unitInterval)) k a (FirstHurewicz.inducedChain f k b)) =
      FirstHurewicz.inducedChain (ContinuousMap.const (BasedLoopSpace x × A) x) (k + 2)
        (PeriodTorusHigherHomology.crossProductTriangle (BasedLoopSpace x) A k a b) := by
  have h :=
    PeriodTorusHigherHomology.crossProductTriangle_natural (ContinuousMap.id (BasedLoopSpace x)) f
      k a b
  rw [FirstHurewicz.inducedChain_id, LinearMap.id_apply] at h
  rw [← h]
  change
    ((FirstHurewicz.inducedChain (evaluation x) (k + 2)).comp
          (FirstHurewicz.inducedChain ((ContinuousMap.id (BasedLoopSpace x)).prodMap f) (k + 2)))
        _ =
      _
  rw [← FirstHurewicz.inducedChain_comp, evaluation_comp_boundary x f hf]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem
    FifthHurewicz.evaluated_edge_cubeBoundary_cancel {X : Type} [TopologicalSpace X] (x : X)
    (a : FirstHurewicz.Chains (BasedLoopSpace x) 1) :
    FirstHurewicz.inducedChain (evaluation x) 4
        (PeriodTorusHigherHomology.crossProductEdge (BasedLoopSpace x) (Fin 4 → (unitInterval)) 3
          a
          (((FirstHurewicz.singularComplex (Fin 4 → (unitInterval))).d 4 3).hom
            FourthHurewicz.fundamentalCubeChain)) =
      0 := by
  have hF (t : (unitInterval)) (ht : t = 0 ∨ t = 1) :=
    evaluated_edge_boundaryMap x a 3 ThirdHurewicz.fundamentalCubeChain (remainingCubeSideFirst t)
      (remainingCubeSideFirst_boundary t ht)
  have hS (t : (unitInterval)) (ht : t = 0 ∨ t = 1) :=
    evaluated_edge_boundaryMap x a 3 ThirdHurewicz.productCubeChain
      (remainingCubeSide (FourthHurewicz.remainingCubeSideFirst t))
      (remainingCubeSide_boundary _ (FourthHurewicz.remainingCubeSideFirst_boundary t ht))
  have hL (t : (unitInterval)) (ht : t = 0 ∨ t = 1) :=
    evaluated_edge_boundaryMap x a 3 productThreeIntervalChain
      (remainingCubeSide (FourthHurewicz.remainingCubeSide (ThirdHurewicz.squareSideLeft t)))
      (remainingCubeSide_boundary _
        (FourthHurewicz.remainingCubeSide_boundary _
          (ThirdHurewicz.squareSideLeft_boundary t ht)))
  have hR (t : (unitInterval)) (ht : t = 0 ∨ t = 1) :=
    evaluated_edge_boundaryMap x a 3 productThreeIntervalChain
      (remainingCubeSide (FourthHurewicz.remainingCubeSide (ThirdHurewicz.squareSideRight t)))
      (remainingCubeSide_boundary _
        (FourthHurewicz.remainingCubeSide_boundary _
          (ThirdHurewicz.squareSideRight_boundary t ht)))
  simp only [remainingCubeChain_boundary, map_sub, hF 1 (Or.inr rfl), hF 0 (Or.inl rfl),
    hS 1 (Or.inr rfl), hS 0 (Or.inl rfl), hL 1 (Or.inr rfl), hL 0 (Or.inl rfl), hR 1 (Or.inr rfl),
    hR 0 (Or.inl rfl), sub_self]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem FifthHurewicz.evaluated_triangle_cubeBoundary_cancel {X : Type} [TopologicalSpace X]
    (x : X) (a : FirstHurewicz.Chains (BasedLoopSpace x) 2) :
    FirstHurewicz.inducedChain (evaluation x) 5
        (PeriodTorusHigherHomology.crossProductTriangle (BasedLoopSpace x)
          (Fin 4 → (unitInterval)) 3 a
          (((FirstHurewicz.singularComplex (Fin 4 → (unitInterval))).d 4 3).hom
            FourthHurewicz.fundamentalCubeChain)) =
      0 := by
  have hF (t : (unitInterval)) (ht : t = 0 ∨ t = 1) :=
    evaluated_triangle_boundaryMap x a 3 ThirdHurewicz.fundamentalCubeChain
      (remainingCubeSideFirst t) (remainingCubeSideFirst_boundary t ht)
  have hS (t : (unitInterval)) (ht : t = 0 ∨ t = 1) :=
    evaluated_triangle_boundaryMap x a 3 ThirdHurewicz.productCubeChain
      (remainingCubeSide (FourthHurewicz.remainingCubeSideFirst t))
      (remainingCubeSide_boundary _ (FourthHurewicz.remainingCubeSideFirst_boundary t ht))
  have hL (t : (unitInterval)) (ht : t = 0 ∨ t = 1) :=
    evaluated_triangle_boundaryMap x a 3 productThreeIntervalChain
      (remainingCubeSide (FourthHurewicz.remainingCubeSide (ThirdHurewicz.squareSideLeft t)))
      (remainingCubeSide_boundary _
        (FourthHurewicz.remainingCubeSide_boundary _
          (ThirdHurewicz.squareSideLeft_boundary t ht)))
  have hR (t : (unitInterval)) (ht : t = 0 ∨ t = 1) :=
    evaluated_triangle_boundaryMap x a 3 productThreeIntervalChain
      (remainingCubeSide (FourthHurewicz.remainingCubeSide (ThirdHurewicz.squareSideRight t)))
      (remainingCubeSide_boundary _
        (FourthHurewicz.remainingCubeSide_boundary _
          (ThirdHurewicz.squareSideRight_boundary t ht)))
  simp only [remainingCubeChain_boundary, map_sub, hF 1 (Or.inr rfl), hF 0 (Or.inl rfl),
    hS 1 (Or.inr rfl), hS 0 (Or.inl rfl), hL 1 (Or.inr rfl), hL 0 (Or.inl rfl), hR 1 (Or.inr rfl),
    hR 0 (Or.inl rfl), sub_self]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def FifthHurewicz.suspensionOne {X : Type} [TopologicalSpace X] (x : X) :
    FirstHurewicz.Chains (BasedLoopSpace x) 1 →ₗ[ℤ] FirstHurewicz.Chains X 5 :=
  (FirstHurewicz.inducedChain (evaluation x) 5).comp
    (PeriodTorusHigherHomology.integerBilinearRightApply
      (PeriodTorusHigherHomology.crossProductEdge (BasedLoopSpace x) (Fin 4 → (unitInterval)) 4)
      FourthHurewicz.fundamentalCubeChain)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
private theorem FifthHurewicz.suspensionOne_apply {X : Type} [TopologicalSpace X] (x : X)
    (a : FirstHurewicz.Chains (BasedLoopSpace x) 1) :
    suspensionOne x a =
      FirstHurewicz.inducedChain (evaluation x) 5
        (PeriodTorusHigherHomology.crossProductEdge (BasedLoopSpace x) (Fin 4 → (unitInterval)) 4
          a FourthHurewicz.fundamentalCubeChain) :=
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def FifthHurewicz.suspensionTwo {X : Type} [TopologicalSpace X] (x : X) :
    FirstHurewicz.Chains (BasedLoopSpace x) 2 →ₗ[ℤ] FirstHurewicz.Chains X 6 :=
  (FirstHurewicz.inducedChain (evaluation x) 6).comp
    (PeriodTorusHigherHomology.integerBilinearRightApply
      (PeriodTorusHigherHomology.crossProductTriangle (BasedLoopSpace x) (Fin 4 → (unitInterval))
        4)
      FourthHurewicz.fundamentalCubeChain)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
private theorem FifthHurewicz.suspensionTwo_apply {X : Type} [TopologicalSpace X] (x : X)
    (a : FirstHurewicz.Chains (BasedLoopSpace x) 2) :
    suspensionTwo x a =
      FirstHurewicz.inducedChain (evaluation x) 6
        (PeriodTorusHigherHomology.crossProductTriangle (BasedLoopSpace x)
          (Fin 4 → (unitInterval)) 4 a FourthHurewicz.fundamentalCubeChain) :=
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem
    FifthHurewicz.boundaryFive_suspensionOne_of_cycle {X : Type} [TopologicalSpace X] (x : X)
    (a : FirstHurewicz.Chains (BasedLoopSpace x) 1)
    (ha : FirstHurewicz.boundaryOne (BasedLoopSpace x) a = 0) :
    ((FirstHurewicz.singularComplex X).d 5 4).hom (suspensionOne x a) = 0 := by
  rw [suspensionOne_apply, ← FirstHurewicz.inducedChain_boundary,
    PeriodTorusHigherHomology.crossProductEdge_boundary 3]
  change
    FirstHurewicz.inducedChain (evaluation x) 4
        (PeriodTorusHigherHomology.crossProductZeroLeft (BasedLoopSpace x)
            (Fin 4 → (unitInterval)) 4 (FirstHurewicz.boundaryOne (BasedLoopSpace x) a)
            FourthHurewicz.fundamentalCubeChain -
          PeriodTorusHigherHomology.crossProductEdge (BasedLoopSpace x) (Fin 4 → (unitInterval)) 3
            a
            (((FirstHurewicz.singularComplex (Fin 4 → (unitInterval))).d 4 3).hom
              FourthHurewicz.fundamentalCubeChain)) =
      0
  rw [ha, map_zero, LinearMap.zero_apply, zero_sub, map_neg, evaluated_edge_cubeBoundary_cancel,
    neg_zero]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem FifthHurewicz.boundarySix_suspensionTwo {X : Type} [TopologicalSpace X] (x : X)
    (a : FirstHurewicz.Chains (BasedLoopSpace x) 2) :
    ((FirstHurewicz.singularComplex X).d 6 5).hom (suspensionTwo x a) =
      suspensionOne x (FirstHurewicz.boundaryTwo (BasedLoopSpace x) a) := by
  rw [suspensionTwo_apply, ← FirstHurewicz.inducedChain_boundary,
    PeriodTorusHigherHomology.crossProductTriangle_boundary 3]
  change
    FirstHurewicz.inducedChain (evaluation x) 5
        (PeriodTorusHigherHomology.crossProductEdge (BasedLoopSpace x) (Fin 4 → (unitInterval)) 4
            (FirstHurewicz.boundaryTwo (BasedLoopSpace x) a) FourthHurewicz.fundamentalCubeChain +
          PeriodTorusHigherHomology.crossProductTriangle (BasedLoopSpace x)
            (Fin 4 → (unitInterval)) 3 a
            (((FirstHurewicz.singularComplex (Fin 4 → (unitInterval))).d 4 3).hom
              FourthHurewicz.fundamentalCubeChain)) =
      _
  rw [map_add, evaluated_triangle_cubeBoundary_cancel, add_zero]
  rfl

private def FifthHurewicz.pathCubeCycle {X : Type} [TopologicalSpace X] (x : X)
    (p : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const) :
    SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 5 :=
  SingularMayerVietoris.ModuleHomology.mkCycle (FirstHurewicz.singularComplex X) 5
    (suspensionOne x (FirstHurewicz.pathChain p))
    (boundaryFive_suspensionOne_of_cycle x (FirstHurewicz.pathChain p)
      (FirstHurewicz.boundaryOne_loop p))

@[simp]
private theorem FifthHurewicz.pathCubeCycle_val {X : Type} [TopologicalSpace X] (x : X)
    (p : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const) :
    (pathCubeCycle x p).1 = suspensionOne x (FirstHurewicz.pathChain p) :=
  rfl

private def FifthHurewicz.pathCubeClass {X : Type} [TopologicalSpace X] (x : X)
    (p : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const) :
    SingularMayerVietoris.SingularHomology X 5 :=
  SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 5
    (pathCubeCycle x p)

private theorem FifthHurewicz.pathCube_homotopy_boundary {X : Type} [TopologicalSpace X] (x : X)
    {p q : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const} (H : p.Homotopy q) :
    ((FirstHurewicz.singularComplex X).d 6 5).hom
        (suspensionTwo x (FirstHurewicz.homotopyChain H)) =
      (pathCubeCycle x p).1 - (pathCubeCycle x q).1 := by
  rw [boundarySix_suspensionTwo, FirstHurewicz.boundaryTwo_loopHomotopy, map_sub]
  rfl

private theorem FifthHurewicz.pathCubeClass_homotopy {X : Type} [TopologicalSpace X] (x : X)
    {p q : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const} (H : p.Homotopy q) :
    pathCubeClass x p = pathCubeClass x q :=
  (SingularMayerVietoris.ModuleHomology.cycleClass_eq_iff (FirstHurewicz.singularComplex X) 5 _
        _).mpr
    ⟨suspensionTwo x (FirstHurewicz.homotopyChain H), pathCube_homotopy_boundary x H⟩

private theorem FifthHurewicz.pathCubeClass_homotopic {X : Type} [TopologicalSpace X] (x : X)
    {p q : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const} (h : p.Homotopic q) :
    pathCubeClass x p = pathCubeClass x q := by
  obtain ⟨H⟩ := h
  exact pathCubeClass_homotopy x H

@[simp]
private theorem FifthHurewicz.pathCubeClass_refl {X : Type} [TopologicalSpace X] (x : X) :
    pathCubeClass x (Path.refl (GenLoop.const : BasedLoopSpace x)) = 0 := by
  apply
    (SingularMayerVietoris.ModuleHomology.cycleClass_eq_zero_iff (FirstHurewicz.singularComplex X)
        5 _).mpr
  refine
    ⟨suspensionTwo x (FirstHurewicz.constantTriangleChain (GenLoop.const : BasedLoopSpace x)), ?_⟩
  rw [boundarySix_suspensionTwo, FirstHurewicz.boundaryTwo_constantTriangleChain]
  rfl

private theorem FifthHurewicz.pathCube_concat_boundary {X : Type} [TopologicalSpace X] (x : X)
    (p q : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const) :
    ((FirstHurewicz.singularComplex X).d 6 5).hom
        (-suspensionTwo x (FirstHurewicz.concatChain p q)) =
      (pathCubeCycle x (p.trans q)).1 - ((pathCubeCycle x p).1 + (pathCubeCycle x q).1) := by
  rw [map_neg, boundarySix_suspensionTwo, FirstHurewicz.boundaryTwo_concatChain, map_add, map_sub]
  simp only [pathCubeCycle_val]
  abel

private theorem FifthHurewicz.pathCubeClass_trans {X : Type} [TopologicalSpace X] (x : X)
    (p q : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const) :
    pathCubeClass x (p.trans q) = pathCubeClass x p + pathCubeClass x q := by
  unfold pathCubeClass
  rw [← map_add]
  apply
    (SingularMayerVietoris.ModuleHomology.cycleClass_eq_iff (FirstHurewicz.singularComplex X) 5 _
        _).mpr
  exact ⟨-suspensionTwo x (FirstHurewicz.concatChain p q), pathCube_concat_boundary x p q⟩

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def FifthHurewicz.productCubeChain :
    FirstHurewicz.Chains ((unitInterval) × (Fin 4 → (unitInterval))) 5 :=
  PeriodTorusHigherHomology.crossProductEdge (unitInterval) (Fin 4 → (unitInterval)) 4
    SecondHurewicz.intervalChain FourthHurewicz.fundamentalCubeChain

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def FifthHurewicz.fundamentalCubeChain : FirstHurewicz.Chains (Fin 5 → (unitInterval)) 5 :=
  FirstHurewicz.inducedChain cubeCoordinates 5 productCubeChain

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem FifthHurewicz.suspensionOne_toLoop {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 5) X x) :
    suspensionOne x (FirstHurewicz.pathChain (GenLoop.toLoop (0 : Fin 5) p)) =
      FirstHurewicz.inducedChain (cubeMap p) 5 productCubeChain := by
  have h :=
    PeriodTorusHigherHomology.crossProductEdge_natural
      (GenLoop.toLoop (0 : Fin 5) p).toContinuousMap (ContinuousMap.id (Fin 4 → (unitInterval))) 4
      SecondHurewicz.intervalChain FourthHurewicz.fundamentalCubeChain
  rw [SecondHurewicz.induced_intervalChain, FirstHurewicz.inducedChain_id,
    LinearMap.id_apply] at h
  rw [suspensionOne_apply, ← h]
  change
    ((FirstHurewicz.inducedChain (evaluation x) 5).comp
          (FirstHurewicz.inducedChain
            ((GenLoop.toLoop (0 : Fin 5) p).toContinuousMap.prodMap
              (ContinuousMap.id (Fin 4 → (unitInterval))))
            5))
        productCubeChain =
      _
  rw [← FirstHurewicz.inducedChain_comp, evaluation_comp_toLoop]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def
    FifthHurewicz.cubeChain {X : Type} [TopologicalSpace X] {x : X} (p : GenLoop (Fin 5) X x) :
    FirstHurewicz.Chains X 5 :=
  suspensionOne x (FirstHurewicz.pathChain (GenLoop.toLoop (0 : Fin 5) p))

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem FifthHurewicz.cubeChain_eq_induced {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 5) X x) :
    cubeChain p = FirstHurewicz.inducedChain p.val 5 fundamentalCubeChain := by
  rw [cubeChain, suspensionOne_toLoop]
  change
    FirstHurewicz.inducedChain (p.val.comp cubeCoordinates) 5 productCubeChain =
      ((FirstHurewicz.inducedChain p.val 5).comp (FirstHurewicz.inducedChain cubeCoordinates 5))
        productCubeChain
  rw [FirstHurewicz.inducedChain_comp]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def
    FifthHurewicz.cubeCycle {X : Type} [TopologicalSpace X] {x : X} (p : GenLoop (Fin 5) X x) :
    SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 5 :=
  pathCubeCycle x (GenLoop.toLoop (0 : Fin 5) p)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def FifthHurewicz.cubeHomologyClass {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 5) X x) : SingularMayerVietoris.SingularHomology X 5 :=
  SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 5
    (cubeCycle p)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem
    FifthHurewicz.cubeHomologyClass_eq_pathCubeClass {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 5) X x) :
    cubeHomologyClass p = pathCubeClass x (GenLoop.toLoop (0 : Fin 5) p) :=
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem FifthHurewicz.cubeHomologyClass_homotopic {X : Type} [TopologicalSpace X] {x : X}
    {p q : GenLoop (Fin 5) X x} (h : GenLoop.Homotopic p q) :
    cubeHomologyClass p = cubeHomologyClass q :=
  pathCubeClass_homotopic x (GenLoop.homotopicTo (0 : Fin 5) h)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem FifthHurewicz.toLoop_const {X : Type} [TopologicalSpace X] {x : X} :
    GenLoop.toLoop (0 : Fin 5) (GenLoop.const : GenLoop (Fin 5) X x) =
      Path.refl (GenLoop.const : BasedLoopSpace x) := by
  apply Path.ext
  funext t
  apply GenLoop.ext
  intro u
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
private theorem FifthHurewicz.cubeHomologyClass_const {X : Type} [TopologicalSpace X] {x : X} :
    cubeHomologyClass (GenLoop.const : GenLoop (Fin 5) X x) = 0 := by
  rw [cubeHomologyClass_eq_pathCubeClass, toLoop_const, pathCubeClass_refl]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
public
theorem FifthHurewicz.toLoop_transAt {X : Type} [TopologicalSpace X] {x : X}
    (p q : GenLoop (Fin 5) X x) :
    GenLoop.toLoop (0 : Fin 5) (GenLoop.transAt (0 : Fin 5) p q) =
      (GenLoop.toLoop (0 : Fin 5) p).trans (GenLoop.toLoop (0 : Fin 5) q) := by
  have h :=
    congrArg (GenLoop.toLoop (0 : Fin 5))
      (GenLoop.fromLoop_trans_toLoop (i := (0 : Fin 5)) (p := p) (q := q))
  rw [GenLoop.to_from] at h
  exact h.symm

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem FifthHurewicz.cubeHomologyClass_transAt {X : Type} [TopologicalSpace X] {x : X}
    (p q : GenLoop (Fin 5) X x) :
    cubeHomologyClass (GenLoop.transAt (0 : Fin 5) p q) =
      cubeHomologyClass p + cubeHomologyClass q := by
  simp only [cubeHomologyClass_eq_pathCubeClass, toLoop_transAt, pathCubeClass_trans]

private theorem FifthHurewicz.CubeSubdivision.cubeCoordinates_boundary_right (s : (unitInterval))
    {u : Fin 4 → (unitInterval)} (hu : u ∈ Cube.boundary (Fin 4)) :
    FifthHurewicz.cubeCoordinates (s, u) ∈ Cube.boundary (Fin 5) := by
  obtain ⟨i, hi⟩ := hu
  exact ⟨i.succ, by simpa only [FifthHurewicz.cubeCoordinates_succ] using hi⟩

private def FifthHurewicz.CubeSubdivision.curryLoop {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 5) X x) :
    GenLoop (Fin 4) C((unitInterval), X) (ContinuousMap.const (unitInterval) x) :=
  ⟨((FifthHurewicz.cubeMap p).comp ContinuousMap.prodSwap).curry,
    by
    intro u hu
    apply ContinuousMap.ext
    intro s
    exact GenLoop.boundary p _ (cubeCoordinates_boundary_right s hu)⟩

private theorem
    FifthHurewicz.CubeSubdivision.evalLeft_comp_curryLoop {X : Type} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 5) X x) :
    (FourthHurewicz.CubeSubdivision.evalLeft X).comp
        ((ContinuousMap.id (unitInterval)).prodMap (curryLoop p).val) =
      FifthHurewicz.cubeMap p := by
  ext z
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem FifthHurewicz.CubeSubdivision.evalLeft_crossProductEdge_curryLoop {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 5) X x) (n : ℕ)
    (b : FirstHurewicz.Chains (Fin 4 → (unitInterval)) n) :
    FirstHurewicz.inducedChain (FourthHurewicz.CubeSubdivision.evalLeft X) (n + 1)
        (PeriodTorusHigherHomology.crossProductEdge (unitInterval) C((unitInterval), X) n
          SecondHurewicz.intervalChain (FirstHurewicz.inducedChain (curryLoop p).val n b)) =
      FirstHurewicz.inducedChain (FifthHurewicz.cubeMap p) (n + 1)
        (PeriodTorusHigherHomology.crossProductEdge (unitInterval) (Fin 4 → (unitInterval)) n
          SecondHurewicz.intervalChain b) := by
  have h :=
    PeriodTorusHigherHomology.crossProductEdge_natural (ContinuousMap.id (unitInterval))
      (curryLoop p).val n SecondHurewicz.intervalChain b
  rw [FirstHurewicz.inducedChain_id, LinearMap.id_apply] at h
  rw [← h]
  change
    ((FirstHurewicz.inducedChain (FourthHurewicz.CubeSubdivision.evalLeft X) (n + 1)).comp
          (FirstHurewicz.inducedChain
            ((ContinuousMap.id (unitInterval)).prodMap (curryLoop p).val) (n + 1)))
        _ =
      _
  rw [← FirstHurewicz.inducedChain_comp, evalLeft_comp_curryLoop]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem FifthHurewicz.CubeSubdivision.cubeChain_eq_curriedCrossProduct {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 5) X x) :
    FifthHurewicz.cubeChain p =
      FirstHurewicz.inducedChain (FourthHurewicz.CubeSubdivision.evalLeft X) 5
        (PeriodTorusHigherHomology.crossProductEdge (unitInterval) C((unitInterval), X) 4
          SecondHurewicz.intervalChain (FourthHurewicz.cubeChain (curryLoop p))) := by
  rw [FourthHurewicz.cubeChain_eq_induced, evalLeft_crossProductEdge_curryLoop,
    FifthHurewicz.cubeChain_eq_induced, FifthHurewicz.fundamentalCubeChain]
  change
    (FirstHurewicz.inducedChain p.val 5)
        ((FirstHurewicz.inducedChain FifthHurewicz.cubeCoordinates 5)
          FifthHurewicz.productCubeChain) =
      (FirstHurewicz.inducedChain (p.val.comp FifthHurewicz.cubeCoordinates) 5)
        FifthHurewicz.productCubeChain
  rw [FirstHurewicz.inducedChain_comp]
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def
    FifthHurewicz.CubeSubdivision.intervalFourSimplexChain {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 5) X x) (e : Equiv.Perm (Fin 4)) : FirstHurewicz.Chains X 5 :=
  FirstHurewicz.inducedChain (FourthHurewicz.CubeSubdivision.evalLeft X) 5
    (PeriodTorusHigherHomology.crossProductEdge (unitInterval) C((unitInterval), X) 4
      SecondHurewicz.intervalChain
      (FirstHurewicz.simplexChain C((unitInterval), X) 4
        ((curryLoop p).val.comp (HigherHurewicz.CubeTriangulation.cubeSimplex e))))

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem FifthHurewicz.CubeSubdivision.intervalFourSimplexChain_eq_original {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 5) X x) (e : Equiv.Perm (Fin 4)) :
    intervalFourSimplexChain p e =
      FirstHurewicz.inducedChain (FifthHurewicz.cubeMap p) 5
        (PeriodTorusHigherHomology.crossProductEdge (unitInterval) (Fin 4 → (unitInterval)) 4
          SecondHurewicz.intervalChain
          (FirstHurewicz.simplexChain (Fin 4 → (unitInterval)) 4
            (HigherHurewicz.CubeTriangulation.cubeSimplex e))) := by
  rw [intervalFourSimplexChain, ← FirstHurewicz.inducedChain_simplex,
    evalLeft_crossProductEdge_curryLoop]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem
    FifthHurewicz.CubeSubdivision.cubeChain_eq_sum_prisms {X : Type} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 5) X x) :
    FifthHurewicz.cubeChain p =
      ∑ e : Equiv.Perm (Fin 4),
        HigherHurewicz.CubeTriangulation.cubeOrientation e • intervalFourSimplexChain p e := by
  rw [cubeChain_eq_curriedCrossProduct, FourthHurewicz.CubeSubdivision.cubeChain_eq_sum_simplices]
  simp only [map_sum, map_zsmul, intervalFourSimplexChain]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem FifthHurewicz.CubeSubdivision.prismCubeMap_four (e : Equiv.Perm (Fin 4)) :
    FifthHurewicz.cubeCoordinates.comp
        ((FirstHurewicz.pathSimplex Path.id).prodMap
          (HigherHurewicz.CubeTriangulation.cubeSimplex e)) =
      FourthHurewicz.CubeSubdivision.prismCubeMap e := by
  apply ContinuousMap.ext
  intro z
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact FifthHurewicz.cubeCoordinates_zero _
  · change
      FifthHurewicz.cubeCoordinates
          (FirstHurewicz.pathSimplex Path.id z.1,
            HigherHurewicz.CubeTriangulation.cubeSimplex e z.2)
          j.succ =
        _
    rw [FifthHurewicz.cubeCoordinates_succ]
    rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem
    FifthHurewicz.CubeSubdivision.intervalFourSimplexChain_eq_prismCubeRealization {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 5) X x) (e : Equiv.Perm (Fin 4)) :
    intervalFourSimplexChain p e =
      FourthHurewicz.CubeSubdivision.prismCubeRealization p.val e 5
        (PeriodTorusHigherHomology.formalEdgeCrossProduct 4
          (SingularMayerVietoris.formalSimplex (fun i : Fin 2 => i))
          (SingularMayerVietoris.formalSimplex (fun j : Fin 5 => j))) := by
  rw [intervalFourSimplexChain_eq_original, SecondHurewicz.intervalChain, FirstHurewicz.pathChain,
    PeriodTorusHigherHomology.crossProductEdge_simplex,
    FourthHurewicz.CubeSubdivision.prismCubeRealization_edgeCrossProduct]
  change
    ((FirstHurewicz.inducedChain (FifthHurewicz.cubeMap p) 5).comp
          (FirstHurewicz.inducedChain
            ((FirstHurewicz.pathSimplex Path.id).prodMap
              (HigherHurewicz.CubeTriangulation.cubeSimplex e))
            5))
        _ =
      _
  rw [← FirstHurewicz.inducedChain_comp]
  change
    FirstHurewicz.inducedChain
        (p.val.comp
          (FifthHurewicz.cubeCoordinates.comp
            ((FirstHurewicz.pathSimplex Path.id).prodMap
              (HigherHurewicz.CubeTriangulation.cubeSimplex e))))
        5 _ =
      _
  rw [prismCubeMap_four]

private theorem FifthHurewicz.CubeSubdivision.cubeChain_eq_orientedPrismRealization {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 5) X x) :
    FifthHurewicz.cubeChain p =
      FourthHurewicz.CubeSubdivision.orientedPrismRealization p.val 5
        (PeriodTorusHigherHomology.formalEdgeCrossProduct 4
          (SingularMayerVietoris.formalSimplex (fun i : Fin 2 => i))
          (SingularMayerVietoris.formalSimplex (fun j : Fin 5 => j))) := by
  rw [cubeChain_eq_sum_prisms, FourthHurewicz.CubeSubdivision.orientedPrismRealization_eq_sum]
  simp only [intervalFourSimplexChain_eq_prismCubeRealization]

private theorem
    FifthHurewicz.CubeSubdivision.cubeChain_eq_sum_simplices {X : Type} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 5) X x) :
    FifthHurewicz.cubeChain p =
      ∑ e : Equiv.Perm (Fin 5),
        HigherHurewicz.CubeTriangulation.cubeOrientation e •
          FirstHurewicz.simplexChain X 5
            (p.val.comp (HigherHurewicz.CubeTriangulation.cubeSimplex e)) := by
  rw [cubeChain_eq_orientedPrismRealization,
    FourthHurewicz.CubeSubdivision.orientedPrismRealization_edge_eq_standard (n := 2) p,
    FourthHurewicz.CubeSubdivision.orientedPrismRealization_standardPrism]

private theorem FifthHurewicz.fiveSimplexClassOperator_cubeChain_sum {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] (p : GenLoop (Fin 5) X x) :
    fiveSimplexClassOperator x (cubeChain p) =
      ∑ e : Equiv.Perm (Fin 5),
        HigherHurewicz.CubeTriangulation.cubeOrientation e •
          basedFiveSimplexClass
            (normalizedFiveSimplex x
              (p.val.comp (HigherHurewicz.CubeTriangulation.cubeSimplex e))) := by
  rw [CubeSubdivision.cubeChain_eq_sum_simplices, map_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [map_zsmul, fiveSimplexClassOperator_simplex]

private theorem FifthHurewicz.fiveSimplexClassOperator_cubeChain {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] (p : GenLoop (Fin 5) X x) :
    fiveSimplexClassOperator x (cubeChain p) = Additive.ofMul (⟦p⟧ : π_ 5 X x) := by
  rw [fiveSimplexClassOperator_cubeChain_sum]
  calc
    _ = Additive.ofMul (⟦normalizedCube x p⟧ : π_ 5 X x) := by
      simpa only [normalizedCube_simplex, basedFiveSimplexClass] using
        (HigherHurewicz.NativeSubdivision.nativeCubeSubdivision_class (normalizedCube x p)
            (normalizedCube_internalBased x p)).symm
    _ = _ :=
      congrArg Additive.ofMul
        (Quotient.sound
          (show GenLoop.Homotopic (normalizedCube x p) p from
            ⟨(normalizationCubeHomotopy x p).symm⟩))

private def FifthHurewicz.basedFiveSimplexChain {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedFiveSimplex x) : FirstHurewicz.Chains X 5 :=
  HigherHurewicz.correctedSimplexChain 5 x τ.val

private def FifthHurewicz.basedFiveSimplexCycle {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedFiveSimplex x) :
    SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 5 :=
  HigherHurewicz.correctedSimplexCycle 4 x τ.val (basedFiveSimplex_face τ)

private theorem
    FifthHurewicz.basedFiveSimplex_simplexChain_sum {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedFiveSimplex x) :
    (∑ e : Equiv.Perm (Fin 5),
        HigherHurewicz.CubeTriangulation.cubeOrientation e •
          FirstHurewicz.simplexChain X 5
            ((basedFiveSimplexLoop τ).val.comp
              (HigherHurewicz.CubeTriangulation.cubeSimplex e))) =
      basedFiveSimplexChain τ :=
  HigherHurewicz.SimplexGeometry.basedSimplex_simplexChain_sum (n := 3) τ

private def HigherHurewicz.normalizedCycleAssignment {X : Type} [TopologicalSpace X] (n : ℕ) (x : X)
    (f : FirstHurewicz.SingularSimplex X (n + 1) → SimplexGeometry.BasedSimplex (n + 1) x) :
    FirstHurewicz.Chains X (n + 1) →ₗ[ℤ]
      SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) (n + 1) :=
  FirstHurewicz.chainLift X (n + 1) fun smp =>
    correctedSimplexCycle n x (f smp).val (SimplexGeometry.basedSimplex_face (f smp))

@[simp]
private theorem
    HigherHurewicz.normalizedCycleAssignment_simplex {X : Type} [TopologicalSpace X] (n : ℕ)
    (x : X) (f : FirstHurewicz.SingularSimplex X (n + 1) → SimplexGeometry.BasedSimplex (n + 1) x)
    (smp : FirstHurewicz.SingularSimplex X (n + 1)) :
    normalizedCycleAssignment n x f (FirstHurewicz.simplexChain X (n + 1) smp) =
      correctedSimplexCycle n x (f smp).val (SimplexGeometry.basedSimplex_face (f smp)) :=
  FirstHurewicz.chainLift_simplex X (n + 1) _ smp

private theorem HigherHurewicz.normalizedCycleAssignment_val {X : Type} [TopologicalSpace X] (n : ℕ)
    (x : X) (f : FirstHurewicz.SingularSimplex X (n + 1) → SimplexGeometry.BasedSimplex (n + 1) x)
    (c : FirstHurewicz.Chains X (n + 1)) :
    (normalizedCycleAssignment n x f c).val =
      FirstHurewicz.chainLift X (n + 1)
        (fun smp =>
          FirstHurewicz.simplexChain X (n + 1) (f smp).val - constantSimplexChain (n + 1) x)
        c := by
  have h :
    (SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X)
            (n + 1)).subtype.comp
        (normalizedCycleAssignment n x f) =
      FirstHurewicz.chainLift X (n + 1)
        (fun smp =>
          FirstHurewicz.simplexChain X (n + 1) (f smp).val - constantSimplexChain (n + 1) x) := by
    apply FirstHurewicz.chainMap_ext X (n + 1)
    intro smp
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, normalizedCycleAssignment_simplex,
      correctedSimplexCycle_val, FirstHurewicz.chainLift_simplex]
  exact LinearMap.congr_fun h c

private theorem
    HigherHurewicz.normalizedCycleAssignment_val_endpoint {X : Type} [TopologicalSpace X]
    (n : ℕ) (x : X)
    (f : FirstHurewicz.SingularSimplex X (n + 1) → SimplexGeometry.BasedSimplex (n + 1) x)
    (H' :
      FirstHurewicz.SingularSimplex X (n + 1) →
        C((unitInterval) × FirstHurewicz.Simplex (n + 1), X))
    (hf : ∀ smp, (f smp).val = SecondHurewicz.SimplyConnected.timeSlice (H' smp) 1)
    (c : FirstHurewicz.Chains X (n + 1)) :
    (normalizedCycleAssignment n x f c).val =
      SecondHurewicz.SimplyConnected.simplexEndpointOperator (n + 1) H' 1 c -
        SecondHurewicz.SimplyConnected.chainAugmentation X (n + 1) c •
          constantSimplexChain (n + 1) x := by
  rw [normalizedCycleAssignment_val, SecondHurewicz.SimplyConnected.chainLift_sub_constant]
  have hmap :
    FirstHurewicz.chainLift X (n + 1)
        (fun smp => FirstHurewicz.simplexChain X (n + 1) (f smp).val) =
      SecondHurewicz.SimplyConnected.simplexEndpointOperator (n + 1) H' 1 := by
    apply FirstHurewicz.chainMap_ext X (n + 1)
    intro smp
    rw [FirstHurewicz.chainLift_simplex,
      SecondHurewicz.SimplyConnected.simplexEndpointOperator_simplex, hf]
  rw [hmap]

private theorem
    HigherHurewicz.normalizedCycleAssignment_evenCycle {X : Type} [TopologicalSpace X] (n : ℕ)
    (x : X) (f : FirstHurewicz.SingularSimplex X (n + 1) → SimplexGeometry.BasedSimplex (n + 1) x)
    (H : FirstHurewicz.SingularSimplex X n → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (H' :
      FirstHurewicz.SingularSimplex X (n + 1) →
        C((unitInterval) × FirstHurewicz.Simplex (n + 1), X))
    (hface : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies n H H')
    (hf : ∀ smp, (f smp).val = SecondHurewicz.SimplyConnected.timeSlice (H' smp) 1)
    (heven : Even (n + 1))
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) (n + 1)) :
    normalizedCycleAssignment n x f c.val = straightenedCycle n H H' hface c := by
  apply Subtype.ext
  rw [normalizedCycleAssignment_val_endpoint n x f H' hf,
    chainAugmentation_evenCycle X (n + 1) heven (Nat.zero_lt_succ n), zero_smul, sub_zero,
    straightenedCycle_val]

private theorem
    HigherHurewicz.normalizedCycleAssignment_oddCycle {X : Type} [TopologicalSpace X] (n : ℕ)
    (x : X) (f : FirstHurewicz.SingularSimplex X (n + 1) → SimplexGeometry.BasedSimplex (n + 1) x)
    (H : FirstHurewicz.SingularSimplex X n → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (H' :
      FirstHurewicz.SingularSimplex X (n + 1) →
        C((unitInterval) × FirstHurewicz.Simplex (n + 1), X))
    (hface : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies n H H')
    (hf : ∀ smp, (f smp).val = SecondHurewicz.SimplyConnected.timeSlice (H' smp) 1)
    (hodd : Odd (n + 1))
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) (n + 1)) :
    normalizedCycleAssignment n x f c.val =
      straightenedCycle n H H' hface c -
        SecondHurewicz.SimplyConnected.chainAugmentation X (n + 1) c.val •
          constantSimplexCycle (n + 1) x hodd := by
  apply Subtype.ext
  change
    (normalizedCycleAssignment n x f c.val).val =
      (straightenedCycle n H H' hface c).val -
        SecondHurewicz.SimplyConnected.chainAugmentation X (n + 1) c.val •
          (constantSimplexCycle (n + 1) x hodd).val
  rw [normalizedCycleAssignment_val_endpoint n x f H' hf, straightenedCycle_val,
    constantSimplexCycle_val]

private theorem
    HigherHurewicz.normalizedCycleAssignment_class {X : Type} [TopologicalSpace X] (n : ℕ)
    (x : X) (f : FirstHurewicz.SingularSimplex X (n + 1) → SimplexGeometry.BasedSimplex (n + 1) x)
    (H : FirstHurewicz.SingularSimplex X n → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (H' :
      FirstHurewicz.SingularSimplex X (n + 1) →
        C((unitInterval) × FirstHurewicz.Simplex (n + 1), X))
    (hface : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies n H H')
    (h₀ : ∀ smp, SecondHurewicz.SimplyConnected.timeSlice (H' smp) 0 = smp)
    (hf : ∀ smp, (f smp).val = SecondHurewicz.SimplyConnected.timeSlice (H' smp) 1)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) (n + 1)) :
    SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) (n + 1)
        (normalizedCycleAssignment n x f c.val) =
      SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) (n + 1)
        c := by
  by_cases heven : Even (n + 1)
  · rw [normalizedCycleAssignment_evenCycle n x f H H' hface hf heven]
    exact straightenedCycle_class n H H' hface h₀ c
  · have hodd : Odd (n + 1) := Nat.not_even_iff_odd.mp heven
    rw [normalizedCycleAssignment_oddCycle n x f H H' hface hf hodd, map_sub, map_zsmul,
      constantSimplexCycle_class, zsmul_zero, sub_zero]
    exact straightenedCycle_class n H H' hface h₀ c

private def FifthHurewicz.normalizedFiveSimplexCycleOperator {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] :
    FirstHurewicz.Chains X 5 →ₗ[ℤ]
      SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 5 :=
  HigherHurewicz.normalizedCycleAssignment 4 x (normalizedFiveSimplex x)

@[simp]
private theorem
    FifthHurewicz.normalizedFiveSimplexCycleOperator_simplex {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] (smp : FirstHurewicz.SingularSimplex X 5) :
    normalizedFiveSimplexCycleOperator x (FirstHurewicz.simplexChain X 5 smp) =
      basedFiveSimplexCycle (normalizedFiveSimplex x smp) :=
  HigherHurewicz.normalizedCycleAssignment_simplex 4 x (normalizedFiveSimplex x) smp

private theorem
    FifthHurewicz.normalizedFiveSimplexCycleOperator_class {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)]
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 5) :
    SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 5
        (normalizedFiveSimplexCycleOperator x c.val) =
      SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 5 c := by
  apply
    HigherHurewicz.normalizedCycleAssignment_class 4 x (normalizedFiveSimplex x)
      (normalizationFourSimplexHomotopy x) (normalizationFiveSimplexHomotopy x)
      (normalizationHomotopy_face x) _ (fun _ => rfl) c
  intro smp
  ext s
  exact normalizationFiveSimplexHomotopy_zero x smp s

private def FifthHurewicz.hurewiczFunction {X : Type} [TopologicalSpace X] (x : X) :
    π_ 5 X x → SingularMayerVietoris.SingularHomology X 5 :=
  Quotient.lift cubeHomologyClass (fun _ _ h => cubeHomologyClass_homotopic h)

private def FifthHurewicz.hurewiczPi5 {X : Type} [TopologicalSpace X] (x : X) :
    π_ 5 X x →* Multiplicative (SingularMayerVietoris.SingularHomology X 5)
    where
  toFun a := Multiplicative.ofAdd (hurewiczFunction x a)
  map_one' := congrArg Multiplicative.ofAdd (cubeHomologyClass_const (x := x))
  map_mul' a
    b := by
    refine Quotient.inductionOn₂ a b fun p q => ?_
    refine
      (congrArg (fun c : π_ 5 X x => Multiplicative.ofAdd (hurewiczFunction x c))
            (HomotopyGroup.mul_spec (i := (0 : Fin 5)) (p := p) (q := q))).trans
        ?_
    change
      Multiplicative.ofAdd (cubeHomologyClass (GenLoop.transAt (0 : Fin 5) q p)) =
        Multiplicative.ofAdd (cubeHomologyClass p + cubeHomologyClass q)
    rw [cubeHomologyClass_transAt, add_comm]

private def FifthHurewicz.hurewiczMap {X : Type} [TopologicalSpace X] (x : X) :
    Additive (π_ 5 X x) →ₗ[ℤ] SingularMayerVietoris.SingularHomology X 5
    where
  toFun := (hurewiczPi5 x).toAdditiveLeft
  map_add' := (hurewiczPi5 x).toAdditiveLeft.map_add
  map_smul' n a := by simpa using map_intCast_smul (hurewiczPi5 x).toAdditiveLeft ℤ ℤ n a

private theorem FifthHurewicz.hurewiczMap_representative {X : Type} [TopologicalSpace X] (x : X)
    (p : GenLoop (Fin 5) X x) :
    hurewiczMap x (Additive.ofMul (⟦p⟧ : π_ 5 X x)) =
      SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 5
        (cubeCycle p) :=
  rfl

private theorem FifthHurewicz.cubeChain_basedFiveSimplexLoop {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedFiveSimplex x) : cubeChain (basedFiveSimplexLoop τ) = basedFiveSimplexChain τ := by
  rw [CubeSubdivision.cubeChain_eq_sum_simplices, basedFiveSimplex_simplexChain_sum]

private theorem FifthHurewicz.cubeCycle_basedFiveSimplexLoop {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedFiveSimplex x) : cubeCycle (basedFiveSimplexLoop τ) = basedFiveSimplexCycle τ := by
  apply Subtype.ext
  exact cubeChain_basedFiveSimplexLoop τ

private theorem FifthHurewicz.hurewicz_basedFiveSimplexClass {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedFiveSimplex x) :
    hurewiczMap x (basedFiveSimplexClass τ) =
      SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 5
        (basedFiveSimplexCycle τ) := by
  change
    SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 5
        (cubeCycle (basedFiveSimplexLoop τ)) =
      _
  rw [cubeCycle_basedFiveSimplexLoop]

private theorem
    FifthHurewicz.hurewiczMap_comp_fiveSimplexClassOperator {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] :
    (hurewiczMap x).comp (fiveSimplexClassOperator x) =
      (SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 5).comp
        (normalizedFiveSimplexCycleOperator x) := by
  apply FirstHurewicz.chainMap_ext X 5
  intro smp
  simp only [LinearMap.comp_apply, fiveSimplexClassOperator_simplex,
    normalizedFiveSimplexCycleOperator_simplex]
  exact hurewicz_basedFiveSimplexClass (normalizedFiveSimplex x smp)

private theorem
    FifthHurewicz.hurewiczMap_fiveSimplexClassOperator_cycle {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)]
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 5) :
    hurewiczMap x (fiveSimplexClassOperator x c.val) =
      SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 5 c := by
  have h := LinearMap.congr_fun (hurewiczMap_comp_fiveSimplexClassOperator x) c.val
  change
    hurewiczMap x (fiveSimplexClassOperator x c.val) =
      SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 5
        (normalizedFiveSimplexCycleOperator x c.val) at h
  exact h.trans (normalizedFiveSimplexCycleOperator_class x c)

private def
    FifthHurewicz.hurewiczInverse {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)] [Subsingleton (π_ 4 X x)] :
    SingularMayerVietoris.SingularHomology X 5 →ₗ[ℤ] Additive (π_ 5 X x) :=
  HigherHurewicz.singularHomologyDesc 5 (fiveSimplexClassOperator x)
    (fiveSimplexClassOperator_boundary x)

@[simp]
private theorem FifthHurewicz.hurewiczInverse_cycleClass {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)]
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 5) :
    hurewiczInverse x
        (SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 5 c) =
      fiveSimplexClassOperator x c.val :=
  HigherHurewicz.singularHomologyDesc_cycleClass 5 _ _ c

private theorem FifthHurewicz.hurewiczMap_comp_hurewiczInverse {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] : (hurewiczMap x).comp (hurewiczInverse x) = LinearMap.id :=
  HigherHurewicz.comp_singularHomologyDesc_eq_id 5 (fiveSimplexClassOperator x)
    (fiveSimplexClassOperator_boundary x) (hurewiczMap x)
    (hurewiczMap_fiveSimplexClassOperator_cycle x)

@[simp]
private theorem FifthHurewicz.hurewiczMap_hurewiczInverse {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] (c : SingularMayerVietoris.SingularHomology X 5) :
    hurewiczMap x (hurewiczInverse x c) = c :=
  LinearMap.congr_fun (hurewiczMap_comp_hurewiczInverse x) c

private theorem FifthHurewicz.hurewiczInverse_hurewiczMap_mk {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] (p : GenLoop (Fin 5) X x) :
    hurewiczInverse x (hurewiczMap x (Additive.ofMul (⟦p⟧ : π_ 5 X x))) =
      Additive.ofMul (⟦p⟧ : π_ 5 X x) := by
  rw [hurewiczMap_representative, hurewiczInverse_cycleClass]
  exact fiveSimplexClassOperator_cubeChain x p

@[simp]
private theorem FifthHurewicz.hurewiczInverse_hurewiczMap {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] (a : Additive (π_ 5 X x)) :
    hurewiczInverse x (hurewiczMap x a) = a := by
  change
    hurewiczInverse x (hurewiczMap x (Additive.ofMul (Additive.toMul a))) =
      Additive.ofMul (Additive.toMul a)
  refine Quotient.inductionOn (Additive.toMul a) ?_
  intro p
  exact hurewiczInverse_hurewiczMap_mk x p

private theorem FifthHurewicz.hurewiczInverse_comp_hurewiczMap {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] : (hurewiczInverse x).comp (hurewiczMap x) = LinearMap.id := by
  ext a
  exact hurewiczInverse_hurewiczMap x a


private def FifthHurewicz.hurewiczPi5Equiv {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)] [Subsingleton (π_ 4 X x)] :
    π_ 5 X x ≃* Multiplicative (SingularMayerVietoris.SingularHomology X 5)
    where
  __ := hurewiczPi5 x
  invFun c := Additive.toMul (hurewiczInverse x (Multiplicative.toAdd c))
  left_inv a := congrArg Additive.toMul (hurewiczInverse_hurewiczMap x (Additive.ofMul a))
  right_inv
    c := congrArg Multiplicative.ofAdd (hurewiczMap_hurewiczInverse x (Multiplicative.toAdd c))

end Mathoverflow1973

end
