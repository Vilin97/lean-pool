/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

module

import Mathlib.Algebra.Polynomial.Basis
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
public import LeanPool.InfiniteConnesRigidity.SpectralAndPropertyT

/-!
# Concrete group construction and ICC certificates
-/

noncomputable section

namespace ConnesRigidity
section

open ConnesRigidity

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem cornulierK₁_hasUniformRelativeKazhdanDisplacement
    (hroot : ShalomIntegralPolynomialRelativePair) :
    HasUniformRelativeKazhdanDisplacement
      integralElementaryGroup cornulierK₁ := by
  rw [← cornulierColumnPlanes_sup_eq_K₁]
  have huniform := shalom_uniformPolynomialTranslationDisplacement hroot
  exact (huniform.map integralRankTwoColumnEmbedding).sup_of_elementwise_commute
      (huniform.map integralRankTwoColumnEmbedding12)
      cornulierColumnPlanes_commute

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem cornulierK₂_hasUniformRelativeKazhdanDisplacement
    (hroot : ShalomIntegralPolynomialRelativePair) :
    HasUniformRelativeKazhdanDisplacement
      integralElementaryGroup cornulierK₂ := by
  rw [← cornulierRowPlanes_sup_eq_K₂]
  have huniform := shalom_uniformPolynomialTranslationDisplacement hroot
  exact (huniform.map integralRankTwoRowEmbedding01).sup_of_elementwise_commute
      (huniform.map integralRankTwoRowEmbedding12)
      cornulierRowPlanes_commute

end

section

open ConnesRigidity

universe u

section AffineLengths

variable {G : Type u} [Group G]
variable {V : Type u} [NormedAddCommGroup V]
  [InnerProductSpace ℂ V] [CompleteSpace V]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def cornulierHilbertLength (α : AffineHilbertAction G V)
    (x : V) (g : G) : ℝ :=
  ‖α g x - x‖



omit [CompleteSpace V] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem cornulierHilbertLength_mul_le
    (α : AffineHilbertAction G V) (x : V) (g h : G) :
    cornulierHilbertLength α x (g * h) ≤
      cornulierHilbertLength α x g + cornulierHilbertLength α x h := by
  change ‖α (g * h) x - x‖ ≤ ‖α g x - x‖ + ‖α h x - x‖
  rw [← dist_eq_norm, ← dist_eq_norm, ← dist_eq_norm]
  calc
    dist (α (g * h) x) x ≤
        dist (α (g * h) x) (α g x) + dist (α g x) x :=
      dist_triangle _ _ _
    _ = dist (α h x) x + dist (α g x) x := by
      rw [map_mul]
      change dist (α g (α h x)) (α g x) + dist (α g x) x = _
      rw [(α g).isometry.dist_eq]
    _ = dist (α g x) x + dist (α h x) x := add_comm _ _

omit [CompleteSpace V] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem cornulierHilbertLength_le_of_fixed
    (α : AffineHilbertAction G V) (N : Subgroup G)
    (x y : V) (hy : IsAffineFixed α N y) (g : N) :
    cornulierHilbertLength α x (g : G) ≤ 2 * ‖x - y‖ := by
  change ‖α (g : G) x - x‖ ≤ 2 * ‖x - y‖
  rw [← dist_eq_norm]
  calc
    dist (α (g : G) x) x ≤
        dist (α (g : G) x) y + dist y x := dist_triangle _ _ _
    _ = dist x y + dist y x := by
      have hdist := (α (g : G)).isometry.dist_eq x y
      rw [hy g] at hdist
      rw [hdist]
    _ = 2 * ‖x - y‖ := by
      rw [dist_eq_norm, dist_eq_norm, norm_sub_rev]
      ring

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def CornulierHilbertLengthBoundedOn
    (α : AffineHilbertAction G V) (x : V) (N : Subgroup G) : Prop :=
  ∃ C : ℝ, ∀ g : N, cornulierHilbertLength α x (g : G) ≤ C

end AffineLengths

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def HasCornulierCorelativePropertyFH
    (G : CountableDiscreteGroup.{u}) (N : Subgroup G) : Prop :=
  ∀ (V : Type u)
    (_ : NormedAddCommGroup V)
    (_ : InnerProductSpace ℂ V)
    (_ : CompleteSpace V)
    (α : AffineHilbertAction G V) (x : V),
    CornulierHilbertLengthBoundedOn α x N →
      CornulierHilbertLengthBoundedOn α x ⊤

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def HasCornulierRelativeAffineFixedPoint
    (G : CountableDiscreteGroup.{u}) (N : Subgroup G) : Prop :=
  ∀ (V : Type u)
    (_ : NormedAddCommGroup V)
    (_ : InnerProductSpace ℂ V)
    (_ : CompleteSpace V)
    (α : AffineHilbertAction G V),
      ∃ x : V, IsAffineFixed α N x

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem cornulier_corelative_iff_affineOrbitBound
    (G : CountableDiscreteGroup.{u}) (N : Subgroup G) :
    HasCornulierCorelativePropertyFH G N ↔
      HasCorelativeAffineOrbitBound N := by
  constructor
  · intro h V _ _ _ α x hN
    obtain ⟨C, hC⟩ := h V inferInstance inferInstance inferInstance α x
      (by simpa only [CornulierHilbertLengthBoundedOn, cornulierHilbertLength, Subtype.forall]
        using hN)
    exact ⟨C, fun g => hC ⟨g, Subgroup.mem_top g⟩⟩
  · intro h V _ _ _ α x hN
    obtain ⟨C, hC⟩ := h V inferInstance inferInstance inferInstance α x
      (by simpa only [Subtype.forall, CornulierHilbertLengthBoundedOn, cornulierHilbertLength]
        using hN)
    exact ⟨C, fun g => hC (g : G)⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem cornulier_elementary_isPerfect :
    Group.IsPerfect integralElementaryGroup :=
  integralElementaryGroup_isPerfect

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem cornulier_hom_commGroup_eq_one
    {A : Type*} [CommGroup A]
    (f : integralElementaryGroup →* A) :
    ∀ g : integralElementaryGroup, f g = 1 := by
  let : Group.IsPerfect integralElementaryGroup :=
    cornulier_elementary_isPerfect
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  let : Subsingleton f.range :=
    Group.IsPerfect.subsingleton_of_isMulCommutative
  intro g
  have h : (⟨f g, ⟨g, rfl⟩⟩ : f.range) = 1 :=
    Subsingleton.elim _ _
  exact congrArg Subtype.val h

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem cornulier_realCharacter_eq_zero
    (f : integralElementaryGroup →* Multiplicative ℝ)
    (g : integralElementaryGroup) :
    Multiplicative.toAdd (f g) = 0 := by
  have h := cornulier_hom_commGroup_eq_one f g
  exact congrArg Multiplicative.toAdd h

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private noncomputable def cornulierFiniteOppositeRoots :
    Finset integralElementaryGroup := by
  classical
  exact
  (Finset.univ.biUnion fun i : Index =>
    if h : i ≠ cornulierLast then
      ({(1 : IntegralPolynomial), Polynomial.X} :
        Finset IntegralPolynomial).image
          (cornulierRoot i cornulierLast h)
    else ∅) ∪
  (Finset.univ.biUnion fun j : Index =>
    if h : cornulierLast ≠ j then
      ({(1 : IntegralPolynomial), Polynomial.X} :
        Finset IntegralPolynomial).image
          (cornulierRoot cornulierLast j h)
    else ∅)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem cornulier_lastColumnRoot_mem_finiteOppositeRoots
    (i : Index) (hi : i ≠ cornulierLast) (a : IntegralPolynomial)
    (ha : a = 1 ∨ a = Polynomial.X) :
    cornulierRoot i cornulierLast hi a ∈ cornulierFiniteOppositeRoots := by
  classical
  unfold cornulierFiniteOppositeRoots
  apply Finset.mem_union_left
  apply Finset.mem_biUnion.mpr
  refine ⟨i, Finset.mem_univ i, ?_⟩
  rw [dite_eq_left hi]
  exact Finset.mem_image.mpr ⟨a, by simpa only [Finset.mem_insert,
                                      Finset.mem_singleton] using ha, rfl⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem cornulier_lastRowRoot_mem_finiteOppositeRoots
    (j : Index) (hj : cornulierLast ≠ j) (a : IntegralPolynomial)
    (ha : a = 1 ∨ a = Polynomial.X) :
    cornulierRoot cornulierLast j hj a ∈ cornulierFiniteOppositeRoots := by
  classical
  unfold cornulierFiniteOppositeRoots
  apply Finset.mem_union_right
  apply Finset.mem_biUnion.mpr
  refine ⟨j, Finset.mem_univ j, ?_⟩
  rw [dite_eq_left hj]
  exact Finset.mem_image.mpr ⟨a, by simpa only [Finset.mem_insert,
                                      Finset.mem_singleton] using ha, rfl⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem cornulier_finiteOppositeRoots_subset
    (g : integralElementaryGroup)
    (hg : g ∈ cornulierFiniteOppositeRoots) :
    g ∈ cornulierK₁ ∨ g ∈ cornulierK₂ := by
  classical
  unfold cornulierFiniteOppositeRoots at hg
  rcases Finset.mem_union.mp hg with hleft | hright
  · obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hleft
    by_cases h : i ≠ cornulierLast
    · rw [dite_eq_left h] at hi
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hi
      exact Or.inl (cornulierRoot_mem_K₁ i h a)
    · rw [dite_eq_right h] at hi
      simp only [Finset.notMem_empty] at hi
  · obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hright
    by_cases h : cornulierLast ≠ j
    · rw [dite_eq_left h] at hj
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hj
      exact Or.inr (cornulierRoot_mem_K₂ j h a)
    · rw [dite_eq_right h] at hj
      simp only [Finset.notMem_empty] at hj

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem cornulierRoot_mem_finiteOppositeRoots_closure
    (i j : Index) (hij : i ≠ j) (a : IntegralPolynomial)
    (ha : a = 1 ∨ a = Polynomial.X) :
    cornulierRoot i j hij a ∈
      Subgroup.closure
        (cornulierFiniteOppositeRoots : Set integralElementaryGroup) := by
  by_cases hi : i = cornulierLast
  · subst i
    apply Subgroup.subset_closure
    exact cornulier_lastRowRoot_mem_finiteOppositeRoots j hij a ha
  by_cases hj : j = cornulierLast
  · subst j
    apply Subgroup.subset_closure
    exact cornulier_lastColumnRoot_mem_finiteOppositeRoots i hij a ha
  let x : integralElementaryGroup := cornulierRoot i cornulierLast hi a
  let y : integralElementaryGroup :=
    cornulierRoot cornulierLast j (Ne.symm hj) (1 : IntegralPolynomial)
  let S : Subgroup integralElementaryGroup :=
    Subgroup.closure
      (cornulierFiniteOppositeRoots : Set integralElementaryGroup)
  have hx : x ∈ S := Subgroup.subset_closure
    (cornulier_lastColumnRoot_mem_finiteOppositeRoots i hi a ha)
  have hy : y ∈ S := Subgroup.subset_closure
    (cornulier_lastRowRoot_mem_finiteOppositeRoots j (Ne.symm hj) 1 (Or.inl rfl))
  have hcomm : x * y * x⁻¹ * y⁻¹ ∈ S :=
    S.mul_mem (S.mul_mem (S.mul_mem hx hy) (S.inv_mem hx)) (S.inv_mem hy)
  have heq : x * y * x⁻¹ * y⁻¹ = cornulierRoot i j hij a := by
    apply Subtype.ext
    change
      Matrix.SpecialLinearGroup.transvection hi a *
        Matrix.SpecialLinearGroup.transvection (Ne.symm hj) 1 *
        (Matrix.SpecialLinearGroup.transvection hi a)⁻¹ *
        (Matrix.SpecialLinearGroup.transvection (Ne.symm hj) 1)⁻¹ =
        Matrix.SpecialLinearGroup.transvection hij a
    simpa only [mul_one] using specialLinear_transvection_commutator
      i cornulierLast j hi (Ne.symm hj) hij a 1
  exact heq ▸ hcomm

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem cornulier_finiteOppositeRoots_closure_eq_top :
    Subgroup.closure
      (cornulierFiniteOppositeRoots : Set integralElementaryGroup) = ⊤ := by
  let S : Subgroup integralElementaryGroup :=
    Subgroup.closure
      (cornulierFiniteOppositeRoots : Set integralElementaryGroup)
  let H : Subgroup IntegralSpecialLinearGroup :=
    S.map integralElementarySubgroup.subtype
  have hone : ∀ (i j : Index) (h : i ≠ j),
      Matrix.SpecialLinearGroup.transvection h
        (1 : IntegralPolynomial) ∈ H := by
    intro i j h
    exact ⟨cornulierRoot i j h 1,
      cornulierRoot_mem_finiteOppositeRoots_closure i j h 1
        (Or.inl rfl), rfl⟩
  have hX : ∀ (i j : Index) (h : i ≠ j),
      Matrix.SpecialLinearGroup.transvection h
        (Polynomial.X : IntegralPolynomial) ∈ H := by
    intro i j h
    exact ⟨cornulierRoot i j h Polynomial.X,
      cornulierRoot_mem_finiteOppositeRoots_closure i j h Polynomial.X
        (Or.inr rfl), rfl⟩
  have hcover : integralElementarySubgroup ≤ H := by
    change Subgroup.closure _ ≤ H
    rw [Subgroup.closure_le]
    rintro _ ⟨i, j, h, a, rfl⟩
    exact integral_transvection_mem_of_one_and_X H hone hX i j h a
  apply top_unique
  intro g _
  change g ∈ S
  obtain ⟨z, hz, hzg⟩ := hcover g.property
  have heq : z = g := Subtype.ext hzg
  exact heq ▸ hz

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem cornulier_oppositeRoots_generate :
    cornulierK₁ ⊔ cornulierK₂ = ⊤ :=
  cornulierK₁_sup_cornulierK₂_eq_top

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem cornulier_proposition4_corelativeFH
    (hfactor : CornulierBoundedFactorization)
    (hleft : HasCornulierRelativeAffineFixedPoint
      integralElementaryGroup cornulierK₁)
    (hright : HasCornulierRelativeAffineFixedPoint
      integralElementaryGroup cornulierK₂) :
    HasCornulierCorelativePropertyFH integralElementaryGroup cornulierH := by
  intro V _ _ _ α x hH
  obtain ⟨x₁, hx₁⟩ := hleft V inferInstance inferInstance inferInstance α
  obtain ⟨x₂, hx₂⟩ := hright V inferInstance inferInstance inferInstance α
  obtain ⟨C, hC⟩ := hH
  refine ⟨2 * ‖x - x₁‖ + 2 * ‖x - x₂‖ +
      2 * ‖x - x₁‖ + C + 2 * ‖x - x₂‖, ?_⟩
  intro g
  obtain ⟨a₁, ha₁, a₂, ha₂, b₁, hb₁, h, hh, b₂, hb₂, heq⟩ :=
    hfactor (g : integralElementaryGroup)
  have ha₁' := cornulierHilbertLength_le_of_fixed α cornulierK₁ x x₁ hx₁
    ⟨a₁, ha₁⟩
  have ha₂' := cornulierHilbertLength_le_of_fixed α cornulierK₂ x x₂ hx₂
    ⟨a₂, ha₂⟩
  have hb₁' := cornulierHilbertLength_le_of_fixed α cornulierK₁ x x₁ hx₁
    ⟨b₁, hb₁⟩
  have hh' := hC ⟨h, hh⟩
  have hb₂' := cornulierHilbertLength_le_of_fixed α cornulierK₂ x x₂ hx₂
    ⟨b₂, hb₂⟩
  change cornulierHilbertLength α x (g : integralElementaryGroup) ≤ _
  rw [heq]
  calc
    cornulierHilbertLength α x (a₁ * a₂ * b₁ * h * b₂) ≤
        cornulierHilbertLength α x (a₁ * a₂ * b₁ * h) +
          cornulierHilbertLength α x b₂ :=
      cornulierHilbertLength_mul_le α x (a₁ * a₂ * b₁ * h) b₂
    _ ≤ (cornulierHilbertLength α x (a₁ * a₂ * b₁) +
          cornulierHilbertLength α x h) +
          cornulierHilbertLength α x b₂ := by
      gcongr
      exact cornulierHilbertLength_mul_le α x (a₁ * a₂ * b₁) h
    _ ≤ ((cornulierHilbertLength α x (a₁ * a₂) +
          cornulierHilbertLength α x b₁) +
          cornulierHilbertLength α x h) +
          cornulierHilbertLength α x b₂ := by
      gcongr
      exact cornulierHilbertLength_mul_le α x (a₁ * a₂) b₁
    _ ≤ (((cornulierHilbertLength α x a₁ +
          cornulierHilbertLength α x a₂) +
          cornulierHilbertLength α x b₁) +
          cornulierHilbertLength α x h) +
          cornulierHilbertLength α x b₂ := by
      gcongr
      exact cornulierHilbertLength_mul_le α x a₁ a₂
    _ ≤ 2 * ‖x - x₁‖ + 2 * ‖x - x₂‖ +
          2 * ‖x - x₁‖ + C + 2 * ‖x - x₂‖ := by
      linarith

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem cornulier_relativeAffineFixedPoints_of_shalom_gaussian
    (hShalomPair : ShalomIntegralPolynomialRelativePair) :
    HasCornulierRelativeAffineFixedPoint integralElementaryGroup cornulierK₁ ∧
      HasCornulierRelativeAffineFixedPoint integralElementaryGroup cornulierK₂ := by
  constructor
  · exact cornulierRelativeAffineFixed_of_uniform
      integralElementaryGroup cornulierK₁
      (cornulierK₁_hasUniformRelativeKazhdanDisplacement hShalomPair)
  · exact cornulierRelativeAffineFixed_of_uniform
      integralElementaryGroup cornulierK₂
      (cornulierK₂_hasUniformRelativeKazhdanDisplacement hShalomPair)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem cornulier_proposition4_of_shalom_gaussian
    (hShalomPair : ShalomIntegralPolynomialRelativePair) :
    HasCornulierCorelativePropertyFH integralElementaryGroup cornulierH := by
  obtain ⟨hleft, hright⟩ :=
    cornulier_relativeAffineFixedPoints_of_shalom_gaussian hShalomPair
  exact cornulier_proposition4_corelativeFH
    cornulierBoundedFactorization hleft hright

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem cornulier_fullLatticePropertyT_of_relativeSuslin
    (hSuslinRelative : SuslinRelativeElementaryGeneration)
    (hElementary : HasKazhdanPropertyT integralElementaryGroup) :
    ErshovJaikinUniversalLatticePropertyT :=
  universalLatticePropertyT_of_elementary
    (suslinElementaryGeneration_iff_relative.mpr hSuslinRelative)
    hElementary

end

section

open ConnesRigidity

universe u

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private inductive AffineGeneratorWord
    {G : Type u} [Group G] (S : Set G) : G → ℕ → Prop
  | one : AffineGeneratorWord S 1 0
  | generator {g : G} (hg : g ∈ S) : AffineGeneratorWord S g 1
  | mul {g h : G} {m n : ℕ}
      (hg : AffineGeneratorWord S g m)
      (hh : AffineGeneratorWord S h n) :
      AffineGeneratorWord S (g * h) (m + n)
  | inv {g : G} {n : ℕ}
      (hg : AffineGeneratorWord S g n) :
      AffineGeneratorWord S g⁻¹ n

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem exists_affineGeneratorWord_of_mem_closure
    {G : Type u} [Group G] (S : Set G)
    {g : G} (hg : g ∈ Subgroup.closure S) :
    ∃ n : ℕ, AffineGeneratorWord S g n := by
  induction hg using Subgroup.closure_induction with
  | mem g hg => exact ⟨1, AffineGeneratorWord.generator hg⟩
  | one => exact ⟨0, AffineGeneratorWord.one⟩
  | @mul g h hg hh ihg ihh =>
      obtain ⟨m, hm⟩ := ihg
      obtain ⟨n, hn⟩ := ihh
      exact ⟨m + n, AffineGeneratorWord.mul hm hn⟩
  | @inv g hg ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n, AffineGeneratorWord.inv hn⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def affineGeneratorWordLength
    {G : Type u} [Group G] (S : Finset G)
    (hgen : Subgroup.closure (S : Set G) = ⊤) (g : G) : ℕ := by
  classical
  exact Nat.find (exists_affineGeneratorWord_of_mem_closure
    (S : Set G) (g := g) (by rw [hgen]; trivial))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem affineGeneratorWordLength_spec
    {G : Type u} [Group G] (S : Finset G)
    (hgen : Subgroup.closure (S : Set G) = ⊤) (g : G) :
    AffineGeneratorWord (S : Set G) g
      (affineGeneratorWordLength S hgen g) := by
  classical
  exact Nat.find_spec (exists_affineGeneratorWord_of_mem_closure
    (S : Set G) (g := g) (by rw [hgen]; trivial))

variable {G : Type u} [Group G]
variable {V : Type u} [NormedAddCommGroup V]
  [InnerProductSpace ℂ V] [CompleteSpace V]

omit [CompleteSpace V] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem affineHilbert_displacement_inv
    (α : AffineHilbertAction G V) (x : V) (g : G) :
    ‖α g⁻¹ x - x‖ = ‖α g x - x‖ := by
  rw [← dist_eq_norm, ← dist_eq_norm]
  calc
    dist (α g⁻¹ x) x = dist (α g (α g⁻¹ x)) (α g x) :=
      ((α g).isometry.dist_eq _ _).symm
    _ = dist x (α g x) := by
      congr 1
      calc
        α g (α g⁻¹ x) = α (g * g⁻¹) x := by
          rw [map_mul]
          rfl
        _ = x := by simp only [mul_inv_cancel, map_one, AffineIsometryEquiv.coe_one, id_eq]
    _ = dist (α g x) x := dist_comm _ _

omit [CompleteSpace V] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem affine_displacement_le_of_generatorWord
    (α : AffineHilbertAction G V) (x : V)
    (S : Set G) (D : ℝ)
    (hS : ∀ g ∈ S, ‖α g x - x‖ ≤ D)
    {g : G} {n : ℕ} (hword : AffineGeneratorWord S g n) :
    ‖α g x - x‖ ≤ (n : ℝ) * D := by
  induction hword with
  | one => simp only [map_one, AffineIsometryEquiv.coe_one, id_eq, sub_self, norm_zero,
             CharP.cast_eq_zero, zero_mul, Std.le_refl]
  | generator hg => simpa only [Nat.cast_one, one_mul] using hS _ hg
  | @mul g h m n hg hh ihg ihh =>
      calc
        ‖α (g * h) x - x‖ ≤
            ‖α g x - x‖ + ‖α h x - x‖ :=
          cornulierHilbertLength_mul_le α x g h
        _ ≤ (m : ℝ) * D + (n : ℝ) * D := add_le_add ihg ihh
        _ = ((m + n : ℕ) : ℝ) * D := by
          push_cast
          ring
  | @inv g n hg ih =>
      rw [affineHilbert_displacement_inv]
      exact ih

omit [CompleteSpace V] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem affine_oppositeGenerator_displacement_left
    (α : AffineHilbertAction G V) (K₁ K₂ : Subgroup G)
    (x y : V)
    (hx : IsAffineFixed α K₁ x)
    (hy : IsAffineFixed α K₂ y)
    (g : G) (hg : g ∈ K₁ ∨ g ∈ K₂) :
    ‖α g x - x‖ ≤ 2 * ‖x - y‖ := by
  rcases hg with hg | hg
  · have hfixed : α g x = x := hx ⟨g, hg⟩
    simp only [hfixed, sub_self, norm_zero, Nat.ofNat_pos, mul_nonneg_iff_of_pos_left, norm_nonneg]
  · exact cornulierHilbertLength_le_of_fixed
      α K₂ x y hy ⟨g, hg⟩

omit [CompleteSpace V] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem affine_oppositeGenerator_displacement_right
    (α : AffineHilbertAction G V) (K₁ K₂ : Subgroup G)
    (x y : V)
    (hx : IsAffineFixed α K₁ x)
    (hy : IsAffineFixed α K₂ y)
    (g : G) (hg : g ∈ K₁ ∨ g ∈ K₂) :
    ‖α g y - y‖ ≤ 2 * ‖x - y‖ := by
  rcases hg with hg | hg
  · have hbound :=
      cornulierHilbertLength_le_of_fixed α K₁ y x hx ⟨g, hg⟩
    change ‖α g y - y‖ ≤ 2 * ‖y - x‖ at hbound
    rwa [norm_sub_rev y x] at hbound
  · have hfixed : α g y = y := hy ⟨g, hg⟩
    simp only [hfixed, sub_self, norm_zero, Nat.ofNat_pos, mul_nonneg_iff_of_pos_left, norm_nonneg]

omit [CompleteSpace V] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem affine_oppositeWord_displacement_left
    (α : AffineHilbertAction G V) (K₁ K₂ : Subgroup G)
    (S : Finset G) (hgen : Subgroup.closure (S : Set G) = ⊤)
    (hS : ∀ g ∈ S, g ∈ K₁ ∨ g ∈ K₂)
    (x y : V)
    (hx : IsAffineFixed α K₁ x)
    (hy : IsAffineFixed α K₂ y)
    (C : ℝ) (hC : ‖x - y‖ ≤ C) (g : G) :
    ‖α g x - x‖ ≤
      (affineGeneratorWordLength S hgen g : ℝ) * (2 * C) := by
  apply affine_displacement_le_of_generatorWord
    α x (S : Set G) (2 * C) ?_
    (affineGeneratorWordLength_spec S hgen g)
  intro s hs
  calc
    ‖α s x - x‖ ≤ 2 * ‖x - y‖ :=
      affine_oppositeGenerator_displacement_left α K₁ K₂ x y hx hy s
        (hS s hs)
    _ ≤ 2 * C := by gcongr

omit [CompleteSpace V] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem affine_oppositeWord_displacement_right
    (α : AffineHilbertAction G V) (K₁ K₂ : Subgroup G)
    (S : Finset G) (hgen : Subgroup.closure (S : Set G) = ⊤)
    (hS : ∀ g ∈ S, g ∈ K₁ ∨ g ∈ K₂)
    (x y : V)
    (hx : IsAffineFixed α K₁ x)
    (hy : IsAffineFixed α K₂ y)
    (C : ℝ) (hC : ‖x - y‖ ≤ C) (g : G) :
    ‖α g y - y‖ ≤
      (affineGeneratorWordLength S hgen g : ℝ) * (2 * C) := by
  apply affine_displacement_le_of_generatorWord
    α y (S : Set G) (2 * C) ?_
    (affineGeneratorWordLength_spec S hgen g)
  intro s hs
  calc
    ‖α s y - y‖ ≤ 2 * ‖x - y‖ :=
      affine_oppositeGenerator_displacement_right α K₁ K₂ x y hx hy s
        (hS s hs)
    _ ≤ 2 * C := by gcongr

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def affineMarkedPointWordBound
    (S : Finset G) (hgen : Subgroup.closure (S : Set G) = ⊤)
    (C : ℝ) (i : G × Bool) : ℝ :=
  ((affineGeneratorWordLength S hgen i.1 : ℝ) * 2 + 1) * C

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def affineMarkedPairWordBound
    (S : Finset G) (hgen : Subgroup.closure (S : Set G) = ⊤)
    (C : ℝ) (q : (G × Bool) × (G × Bool)) : ℝ :=
  affineMarkedPointWordBound S hgen C q.1 +
    affineMarkedPointWordBound S hgen C q.2

omit [CompleteSpace V] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem markedAffineOrbitPoint_le_wordBound
    (α : AffineHilbertAction G V) (K₁ K₂ : Subgroup G)
    (S : Finset G) (hgen : Subgroup.closure (S : Set G) = ⊤)
    (hS : ∀ g ∈ S, g ∈ K₁ ∨ g ∈ K₂)
    (x y : V)
    (hx : IsAffineFixed α K₁ x)
    (hy : IsAffineFixed α K₂ y)
    (C : ℝ) (hC : ‖x - y‖ ≤ C) (i : G × Bool) :
    ‖CornulierUltralimit.markedAffineOrbitPoint α x y i - x‖ ≤
      affineMarkedPointWordBound S hgen C i := by
  have hCnonneg : 0 ≤ C := (norm_nonneg _).trans hC
  rcases i with ⟨g, b⟩
  cases b with
  | false =>
      change ‖α g y - x‖ ≤ _
      calc
        ‖α g y - x‖ = ‖(α g y - y) + (y - x)‖ := by
          congr 1
          abel
        _ ≤ ‖α g y - y‖ + ‖y - x‖ := norm_add_le _ _
        _ ≤ (affineGeneratorWordLength S hgen g : ℝ) * (2 * C) + C := by
          exact add_le_add
            (affine_oppositeWord_displacement_right
              α K₁ K₂ S hgen hS x y hx hy C hC g)
            (by simpa only [norm_sub_rev] using hC)
        _ = affineMarkedPointWordBound S hgen C (g, false) := by
          unfold affineMarkedPointWordBound
          ring
  | true =>
      change ‖α g x - x‖ ≤ _
      calc
        ‖α g x - x‖ ≤
            (affineGeneratorWordLength S hgen g : ℝ) * (2 * C) :=
          affine_oppositeWord_displacement_left
            α K₁ K₂ S hgen hS x y hx hy C hC g
        _ ≤ affineMarkedPointWordBound S hgen C (g, true) := by
          unfold affineMarkedPointWordBound
          linarith

omit [CompleteSpace V] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem markedAffinePairDisplacement_le_wordBound
    (α : AffineHilbertAction G V) (K₁ K₂ : Subgroup G)
    (S : Finset G) (hgen : Subgroup.closure (S : Set G) = ⊤)
    (hS : ∀ g ∈ S, g ∈ K₁ ∨ g ∈ K₂)
    (x y : V)
    (hx : IsAffineFixed α K₁ x)
    (hy : IsAffineFixed α K₂ y)
    (C : ℝ) (hC : ‖x - y‖ ≤ C)
    (q : (G × Bool) × (G × Bool)) :
    ‖CornulierUltralimit.markedAffinePairDisplacement α x y q‖ ≤
      affineMarkedPairWordBound S hgen C q := by
  unfold CornulierUltralimit.markedAffinePairDisplacement
  calc
    ‖CornulierUltralimit.markedAffineOrbitPoint α x y q.1 -
        CornulierUltralimit.markedAffineOrbitPoint α x y q.2‖ =
      ‖(CornulierUltralimit.markedAffineOrbitPoint α x y q.1 - x) -
        (CornulierUltralimit.markedAffineOrbitPoint α x y q.2 - x)‖ := by
          congr 1
          abel
    _ ≤ ‖CornulierUltralimit.markedAffineOrbitPoint α x y q.1 - x‖ +
        ‖CornulierUltralimit.markedAffineOrbitPoint α x y q.2 - x‖ :=
      norm_sub_le _ _
    _ ≤ affineMarkedPointWordBound S hgen C q.1 +
        affineMarkedPointWordBound S hgen C q.2 :=
      add_le_add
        (markedAffineOrbitPoint_le_wordBound
          α K₁ K₂ S hgen hS x y hx hy C hC q.1)
        (markedAffineOrbitPoint_le_wordBound
          α K₁ K₂ S hgen hS x y hx hy C hC q.2)
    _ = affineMarkedPairWordBound S hgen C q := rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem exists_markedAffinePairDisplacement_uniform_bound
    (K₁ K₂ : Subgroup G) (S : Finset G)
    (hgen : Subgroup.closure (S : Set G) = ⊤)
    (hS : ∀ g ∈ S, g ∈ K₁ ∨ g ∈ K₂)
    (C : ℝ)
    {W : ℕ → Type u}
    [∀ n, NormedAddCommGroup (W n)]
    [∀ n, InnerProductSpace ℂ (W n)]
    (α : ∀ n, AffineHilbertAction G (W n))
    (x y : ∀ n, W n)
    (hx : ∀ n, IsAffineFixed (α n) K₁ (x n))
    (hy : ∀ n, IsAffineFixed (α n) K₂ (y n))
    (hC : ∀ n, ‖x n - y n‖ ≤ C) :
    ∃ B : ((G × Bool) × (G × Bool)) → ℝ,
      ∀ n q,
        ‖CornulierUltralimit.markedAffinePairDisplacement
          (α n) (x n) (y n) q‖ ≤ B q := by
  refine ⟨affineMarkedPairWordBound S hgen C, ?_⟩
  intro n q
  exact markedAffinePairDisplacement_le_wordBound
    (α n) K₁ K₂ S hgen hS (x n) (y n)
    (hx n) (hy n) C (hC n) q

end

section

open ConnesRigidity

section

universe u

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def HasAffineFixedPointProperty (G : CountableDiscreteGroup.{u}) : Prop :=
  ∀ (V : Type u)
    (_ : NormedAddCommGroup V)
    (_ : InnerProductSpace ℂ V)
    (_ : CompleteSpace V)
    (α : AffineHilbertAction G V),
      ∃ x : V, ∀ g : G, α g x = x

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem hasKazhdanPropertyT_of_affine_fixed_points
    (G : CountableDiscreteGroup.{u})
    (hfixed : HasAffineFixedPointProperty G) :
    HasKazhdanPropertyT G := by
  intro V _ _ _ π hπ
  obtain ⟨v, hv, hsum⟩ := exists_almostInvariantUnitSequence_summable π hπ
  let α : AffineHilbertAction G (lp (fun _ : ℕ => V) 2) :=
    diagonalAffineAction π v hsum
  obtain ⟨x, hx⟩ := hfixed (lp (fun _ : ℕ => V) 2)
    inferInstance inferInstance inferInstance α
  exact affineDiagonal_nonzero_invariant_of_fixed π v hv α
    (diagonalAffineAction_apply π v hsum) x hx

end

end

section

open CornulierUltralimit Filter
open scoped Topology

universe u

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private structure CornulierNormalizedMarkedAction
    (G : Type u) [Group G]
    (K₁ K₂ : Subgroup G) (S : Finset G) where
  carrier : Type u
  [normed : NormedAddCommGroup carrier]
  [inner : InnerProductSpace ℂ carrier]
  [complete : CompleteSpace carrier]
  action : G →* (carrier ≃ᵃⁱ[ℂ] carrier)
  leftPoint : carrier
  rightPoint : carrier
  left_fixed : IsAffineFixed action K₁ leftPoint
  right_fixed : IsAffineFixed action K₂ rightPoint
  normalized : AffineUniformGeneratorDisplacement action S

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private instance cornulierNormalizedMarkedActionNormed
    {G : Type u} [Group G] {K₁ K₂ : Subgroup G} {S : Finset G}
    (a : CornulierNormalizedMarkedAction G K₁ K₂ S) :
    NormedAddCommGroup a.carrier := a.normed

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private instance cornulierNormalizedMarkedActionInner
    {G : Type u} [Group G] {K₁ K₂ : Subgroup G} {S : Finset G}
    (a : CornulierNormalizedMarkedAction G K₁ K₂ S) :
    InnerProductSpace ℂ a.carrier := a.inner

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private instance cornulierNormalizedMarkedActionComplete
    {G : Type u} [Group G] {K₁ K₂ : Subgroup G} {S : Finset G}
    (a : CornulierNormalizedMarkedAction G K₁ K₂ S) :
    CompleteSpace a.carrier := a.complete

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def CornulierNormalizedMarkedAction.distance
    {G : Type u} [Group G] {K₁ K₂ : Subgroup G} {S : Finset G}
    (a : CornulierNormalizedMarkedAction G K₁ K₂ S) : ℝ :=
  ‖a.leftPoint - a.rightPoint‖

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def cornulierNormalizedDistanceSpectrum
    (G : Type u) [Group G] (K₁ K₂ : Subgroup G) (S : Finset G) : Set ℝ :=
  Set.range
    (CornulierNormalizedMarkedAction.distance
      (G := G) (K₁ := K₁) (K₂ := K₂) (S := S))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem cornulierNormalizedDistanceSpectrum_bddBelow
    {G : Type u} [Group G]
    (K₁ K₂ : Subgroup G) (S : Finset G) :
    BddBelow (cornulierNormalizedDistanceSpectrum G K₁ K₂ S) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨a, rfl⟩
  exact norm_nonneg _

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def cornulierNormalizedDistanceInfimum
    (G : Type u) [Group G] (K₁ K₂ : Subgroup G) (S : Finset G) : ℝ :=
  sInf (cornulierNormalizedDistanceSpectrum G K₁ K₂ S)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem cornulierNormalizedDistanceInfimum_le
    {G : Type u} [Group G] {K₁ K₂ : Subgroup G} {S : Finset G}
    (a : CornulierNormalizedMarkedAction G K₁ K₂ S) :
    cornulierNormalizedDistanceInfimum G K₁ K₂ S ≤ a.distance :=
  csInf_le (cornulierNormalizedDistanceSpectrum_bddBelow K₁ K₂ S)
    ⟨a, rfl⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem cornulierNormalizedDistanceInfimum_le_of_fixed
    {G H : Type u} [Group G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {K₁ K₂ : Subgroup G} {S : Finset G}
    (α : G →* (H ≃ᵃⁱ[ℂ] H))
    (hnormalized : AffineUniformGeneratorDisplacement α S)
    {x y : H}
    (hx : IsAffineFixed α K₁ x)
    (hy : IsAffineFixed α K₂ y) :
    cornulierNormalizedDistanceInfimum G K₁ K₂ S ≤ ‖x - y‖ := by
  let a : CornulierNormalizedMarkedAction G K₁ K₂ S :=
    { carrier := H
      action := α
      leftPoint := x
      rightPoint := y
      left_fixed := hx
      right_fixed := hy
      normalized := hnormalized }
  exact cornulierNormalizedDistanceInfimum_le a

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem exists_cornulierNormalizedMinimizingSequence
    {G : Type u} [Group G]
    (K₁ K₂ : Subgroup G) (S : Finset G)
    (hne : Nonempty (CornulierNormalizedMarkedAction G K₁ K₂ S)) :
    ∃ a : ℕ → CornulierNormalizedMarkedAction G K₁ K₂ S,
      Antitone (fun n ↦ (a n).distance) ∧
      Tendsto (fun n ↦ (a n).distance) atTop
        (𝓝 (cornulierNormalizedDistanceInfimum G K₁ K₂ S)) := by
  have hspectrum :
      (cornulierNormalizedDistanceSpectrum G K₁ K₂ S).Nonempty := by
    obtain ⟨a⟩ := hne
    exact ⟨a.distance, ⟨a, rfl⟩⟩
  obtain ⟨d, hanti, hd, hmem⟩ := exists_seq_tendsto_sInf hspectrum
    (cornulierNormalizedDistanceSpectrum_bddBelow K₁ K₂ S)
  choose a ha using hmem
  refine ⟨a, ?_, ?_⟩
  · intro i j hij
    simpa only [ha] using hanti hij
  have heq : (fun n ↦ (a n).distance) = d := by
    funext n
    exact ha n
  rw [heq]
  simpa only [cornulierNormalizedDistanceInfimum] using hd

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem cornulierNormalizedMinimizingSequence_bounded
    {G : Type u} [Group G] {K₁ K₂ : Subgroup G} {S : Finset G}
    (a : ℕ → CornulierNormalizedMarkedAction G K₁ K₂ S)
    (hanti : Antitone (fun n ↦ (a n).distance)) :
    ∀ n : ℕ, (a n).distance ≤ (a 0).distance := fun n ↦
  hanti (Nat.zero_le n)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem cornulierNormalizedMarkedAction_nonempty_of_fixed
    {G H : Type u} [Group G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (K₁ K₂ : Subgroup G) (S : Finset G)
    (α : G →* (H ≃ᵃⁱ[ℂ] H))
    (hnormalized : AffineUniformGeneratorDisplacement α S)
    (hleft : ∃ x : H, IsAffineFixed α K₁ x)
    (hright : ∃ y : H, IsAffineFixed α K₂ y) :
    Nonempty (CornulierNormalizedMarkedAction G K₁ K₂ S) := by
  obtain ⟨x, hx⟩ := hleft
  obtain ⟨y, hy⟩ := hright
  exact ⟨{
    carrier := H
    action := α
    leftPoint := x
    rightPoint := y
    left_fixed := hx
    right_fixed := hy
    normalized := hnormalized }⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem isMinimizingAffinePair_of_normalized_infimum
    {G H : Type u} [Group G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (K₁ K₂ : Subgroup G) (S : Finset G)
    (α : G →* (H ≃ᵃⁱ[ℂ] H))
    (hnormalized : AffineUniformGeneratorDisplacement α S)
    (x y : H)
    (hx : IsAffineFixed α K₁ x)
    (hy : IsAffineFixed α K₂ y)
    (hdistance : ‖x - y‖ =
      cornulierNormalizedDistanceInfimum G K₁ K₂ S) :
    IsMinimizingAffinePair α K₁ K₂ x y where
  fixed_left := hx
  fixed_right := hy
  minimal z w hz hw := by
    rw [hdistance]
    exact cornulierNormalizedDistanceInfimum_le_of_fixed
      α hnormalized hz hw

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem exists_cornulierNormalizedExtremalAction_with_infimum
    {G : Type u} [Group G]
    (K₁ K₂ : Subgroup G) (S : Finset G)
    (hgen : Subgroup.closure (S : Set G) = ⊤)
    (hS : ∀ g ∈ S, g ∈ K₁ ∨ g ∈ K₂)
    (hne : Nonempty (CornulierNormalizedMarkedAction G K₁ K₂ S)) :
    ∃ a : CornulierNormalizedMarkedAction G K₁ K₂ S,
      a.distance = cornulierNormalizedDistanceInfimum G K₁ K₂ S ∧
        IsMinimizingAffinePair a.action K₁ K₂ a.leftPoint a.rightPoint := by
  obtain ⟨a, hanti, hdist⟩ :=
    exists_cornulierNormalizedMinimizingSequence K₁ K₂ S hne
  let H : ℕ → Type u := fun n => (a n).carrier
  let (n : ℕ) : NormedAddCommGroup (H n) := (a n).normed
  let (n : ℕ) : InnerProductSpace ℂ (H n) := (a n).inner
  let (n : ℕ) : CompleteSpace (H n) := (a n).complete
  let α : ∀ n, G →* (H n ≃ᵃⁱ[ℂ] H n) := fun n => (a n).action
  let x : ∀ n, H n := fun n => (a n).leftPoint
  let y : ∀ n, H n := fun n => (a n).rightPoint
  have hx : ∀ n, IsAffineFixed (α n) K₁ (x n) :=
    fun n => (a n).left_fixed
  have hy : ∀ n, IsAffineFixed (α n) K₂ (y n) :=
    fun n => (a n).right_fixed
  have hC : ∀ n, ‖x n - y n‖ ≤ (a 0).distance :=
    fun n => cornulierNormalizedMinimizingSequence_bounded a hanti n
  obtain ⟨B, hB⟩ := exists_markedAffinePairDisplacement_uniform_bound
    K₁ K₂ S hgen hS (a 0).distance α x y hx hy hC
  have hnormalized : ∀ n,
      AffineUniformGeneratorDisplacement (α n) S :=
    fun n => (a n).normalized
  obtain ⟨L, R, hadd, _, _, _, hleft, hright, hlimit,
      hlimitNormalized, _⟩ :=
    exists_marked_affine_ultralimit_normalized α x y K₁ K₂ hx hy B hB
      (cornulierNormalizedDistanceInfimum G K₁ K₂ S) hdist S hnormalized
  let β := markedPairAffineAction L R hadd ((1 : G), false)
  let x' := markedPairPoint R ((1 : G), false) ((1 : G), true)
  let y' := markedPairPoint R ((1 : G), false) ((1 : G), false)
  let extremal : CornulierNormalizedMarkedAction G K₁ K₂ S :=
    { carrier := R.realization.carrier
      action := β
      leftPoint := x'
      rightPoint := y'
      left_fixed := hleft
      right_fixed := hright
      normalized := hlimitNormalized }
  refine ⟨extremal, hlimit, ?_⟩
  exact isMinimizingAffinePair_of_normalized_infimum K₁ K₂ S β
    hlimitNormalized x' y' hleft hright hlimit

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem isMinimizingAffinePair_of_normalized_nonexpansive_image
    {G H W : Type u} [Group G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
    (K₁ K₂ : Subgroup G) (S : Finset G)
    (α : G →* (H ≃ᵃⁱ[ℂ] H))
    (β : G →* (W ≃ᵃⁱ[ℂ] W))
    (hnormalized : AffineUniformGeneratorDisplacement β S)
    (P : H → W)
    (hequivariant : ∀ (g : G) (z : H), P (α g z) = β g (P z))
    (hnonexpansive : ∀ z w : H, ‖P z - P w‖ ≤ ‖z - w‖)
    (x y : H)
    (hx : IsAffineFixed α K₁ x)
    (hy : IsAffineFixed α K₂ y)
    (hdistance : ‖x - y‖ =
      cornulierNormalizedDistanceInfimum G K₁ K₂ S) :
    IsMinimizingAffinePair β K₁ K₂ (P x) (P y) := by
  have hPx : IsAffineFixed β K₁ (P x) := by
    intro k
    rw [← hequivariant (k : G) x, hx k]
  have hPy : IsAffineFixed β K₂ (P y) := by
    intro k
    rw [← hequivariant (k : G) y, hy k]
  have hlower := cornulierNormalizedDistanceInfimum_le_of_fixed
    β hnormalized hPx hPy
  have hupper : ‖P x - P y‖ ≤
      cornulierNormalizedDistanceInfimum G K₁ K₂ S := by
    rw [← hdistance]
    exact hnonexpansive x y
  exact isMinimizingAffinePair_of_normalized_infimum
    K₁ K₂ S β hnormalized (P x) (P y) hPx hPy
    (le_antisymm hupper hlower)

end

section

open ConnesRigidity

universe u

variable {G H : Type u} [Group G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def gromovCenteredCocycle
    (α : AffineHilbertAction G H) (x : H) (r : ℝ) (g : G) : H :=
  (r⁻¹ : ℝ) • (α g x - x)

omit [CompleteSpace H] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem gromovCenteredCocycle_mul
    (α : AffineHilbertAction G H) (x : H) (r : ℝ) (g h : G) :
    gromovCenteredCocycle α x r (g * h) =
      gromovCenteredCocycle α x r g +
        affineLinearIsometryHom α g (gromovCenteredCocycle α x r h) := by
  unfold gromovCenteredCocycle
  rw [map_mul]
  change
    (r⁻¹ : ℝ) • (α g (α h x) - x) =
      (r⁻¹ : ℝ) • (α g x - x) +
        (α g).linearIsometryEquiv ((r⁻¹ : ℝ) • (α h x - x))
  rw [map_real_smul (α g).linearIsometryEquiv
    (α g).linearIsometryEquiv.continuous]
  have hsub := (α g).map_vsub (α h x) x
  change (α g).linearIsometryEquiv (α h x - x) =
    α g (α h x) - α g x at hsub
  rw [hsub, ← smul_add]
  congr 1
  abel

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def gromovRescaledAffineAction
    (α : AffineHilbertAction G H) (x : H) (r : ℝ) :
    AffineHilbertAction G H :=
  CornulierUltralimit.unitaryCocycleAffineAction
    (affineLinearIsometryHom α)
    (gromovCenteredCocycle α x r)
    (gromovCenteredCocycle_mul α x r)

omit [CompleteSpace H] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem gromovRescaledAffineAction_apply
    (α : AffineHilbertAction G H) (x : H) (r : ℝ)
    (g : G) (z : H) :
    gromovRescaledAffineAction α x r g z =
      (α g).linearIsometryEquiv z + (r⁻¹ : ℝ) • (α g x - x) := rfl

omit [CompleteSpace H] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem gromovRescaledAffineAction_displacement_norm
    (α : AffineHilbertAction G H) (x : H) (r : ℝ) (hr : 0 < r)
    (g : G) (z : H) :
    ‖gromovRescaledAffineAction α x r g z - z‖ =
      r⁻¹ * ‖α g (x + r • z) - (x + r • z)‖ := by
  have hscaled :
      α g (x + r • z) - (x + r • z) =
        r • (gromovRescaledAffineAction α x r g z - z) := by
    rw [gromovRescaledAffineAction_apply]
    have hmap := (α g).map_vadd x (r • z)
    change α g (r • z + x) =
      (α g).linearIsometryEquiv (r • z) + α g x at hmap
    have hreal := map_real_smul (α g).linearIsometryEquiv
      (α g).linearIsometryEquiv.continuous r z
    rw [add_comm x (r • z), hmap, hreal]
    rw [smul_sub, smul_add, smul_smul]
    have hscale : r * r⁻¹ = (1 : ℝ) := mul_inv_cancel₀ (ne_of_gt hr)
    rw [hscale, one_smul]
    abel
  rw [hscaled, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
  field_simp

end

section

namespace CornulierUltralimit

open Filter
open scoped ComplexOrder InnerProductSpace Topology

universe u

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem affineUniformGeneratorDisplacement_marked_limit_of_local
    {G : Type u} [Group G] {H : ℕ → Type u}
    [∀ n, NormedAddCommGroup (H n)]
    [∀ n, InnerProductSpace ℂ (H n)]
    (α : ∀ n, G →* (H n ≃ᵃⁱ[ℂ] H n))
    (S : Finset G)
    (hnormalized : ∀ (n : ℕ) (z : H n),
      ‖z‖ ≤ (n : ℝ) →
        ∃ s ∈ S, (1 : ℝ) ≤ ‖α n s z - z‖)
    (K : Matrix ((G × Bool) × (G × Bool))
      ((G × Bool) × (G × Bool)) ℂ)
    (R : EquivariantMarkedHilbertKernelRealization
      (markedOrbitAction G) K)
    (hadd : ∀ i j k : G × Bool, ∀ q,
      K (i, j) q + K (j, k) q = K (i, k) q)
    (hdense : Dense (Submodule.span ℂ
      (Set.range R.realization.vector) : Set R.realization.carrier))
    (hgram : ∀ q r,
      Tendsto
        (fun n =>
          ⟪markedAffinePairDisplacement (α n) 0 0 q,
            markedAffinePairDisplacement (α n) 0 0 r⟫_ℂ)
        (Filter.hyperfilter ℕ)
        (𝓝 ⟪R.realization.vector q,
          R.realization.vector r⟫_ℂ)) :
    AffineUniformGeneratorDisplacement
      (markedPairAffineAction K R hadd ((1 : G), false)) S := by
  apply affineUniformGeneratorDisplacement_of_dense
    (markedPairAffineAction K R hadd ((1 : G), false)) S hdense
  intro z hz
  obtain ⟨c, rfl⟩ :=
    Finsupp.mem_span_range_iff_exists_finsupp.mp hz
  let zₙ : ∀ n, H n := fun n =>
    c.sum (fun q a =>
      a • markedAffinePairDisplacement (α n) 0 0 q)
  let zlim : R.realization.carrier :=
    c.sum (fun q a => a • R.realization.vector q)
  have hznorm : Tendsto (fun n => ‖zₙ n‖)
      (Filter.hyperfilter ℕ) (𝓝 ‖zlim‖) := by
    exact tendsto_norm_finsupp_sum_of_gram
      (Filter.hyperfilter ℕ)
      (fun n => markedAffinePairDisplacement (α n) 0 0)
      R.realization.vector hgram c
  have hbounded : ∀ᶠ n in (Filter.hyperfilter ℕ : Filter ℕ),
      ‖zₙ n‖ ≤ ‖zlim‖ + 1 := by
    have hopen : Set.Iio (‖zlim‖ + 1) ∈ 𝓝 ‖zlim‖ :=
      Iio_mem_nhds (lt_add_one _)
    exact (hznorm.eventually hopen).mono fun n hn => le_of_lt hn
  obtain ⟨N, hN⟩ := exists_nat_ge (‖zlim‖ + 1)
  have hlarge : ∀ᶠ n in (Filter.hyperfilter ℕ : Filter ℕ), N ≤ n :=
    (eventually_ge_atTop N).filter_mono Nat.hyperfilter_le_atTop
  have hlocal : ∀ᶠ n in (Filter.hyperfilter ℕ : Filter ℕ),
      ‖zₙ n‖ ≤ (n : ℝ) := by
    filter_upwards [hbounded, hlarge] with n hb hn
    exact hb.trans (hN.trans (by exact_mod_cast hn))
  have hevent : ∀ᶠ n in (Filter.hyperfilter ℕ : Filter ℕ),
      ∃ s ∈ S, (1 : ℝ) ≤ ‖α n s (zₙ n) - zₙ n‖ :=
    hlocal.mono fun n hn => hnormalized n (zₙ n) hn
  obtain ⟨s, hs, hmove⟩ :=
    ultrafilter_eventually_exists_finset (Filter.hyperfilter ℕ)
      S (fun n s => (1 : ℝ) ≤ ‖α n s (zₙ n) - zₙ n‖) hevent
  refine ⟨s, hs, ?_⟩
  have hlimit :=
    tendsto_norm_finsupp_sum_of_gram
      (Filter.hyperfilter ℕ)
      (fun n => markedAffinePairDisplacement (α n) 0 0)
      R.realization.vector hgram
      (markedDisplacementCoefficients (markedOrbitAction G)
        ((1 : G), false) s c)
  rw [markedPairAffineAction_finsupp_action
    K R hadd ((1 : G), false) s c] at hlimit
  have hlimit' :
      Tendsto (fun n => ‖α n s (zₙ n) - zₙ n‖)
        (Filter.hyperfilter ℕ)
        (𝓝 ‖markedPairAffineAction K R hadd
          ((1 : G), false) s
            (c.sum (fun q a => a • R.realization.vector q)) -
          c.sum (fun q a => a • R.realization.vector q)‖) := by
    simpa only [markedAffinePairDisplacement_finsupp_action,
      zero_add, zₙ] using hlimit
  exact ge_of_tendsto hlimit' hmove

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem exists_affineUniformGeneratorDisplacement_of_local_sequence
    {G : Type u} [Group G] {H : ℕ → Type u}
    [∀ n, NormedAddCommGroup (H n)]
    [∀ n, InnerProductSpace ℂ (H n)]
    (α : ∀ n, G →* (H n ≃ᵃⁱ[ℂ] H n))
    (S : Finset G)
    (hgen : Subgroup.closure (S : Set G) = ⊤)
    (hupper : ∀ (n : ℕ) (s : G), s ∈ S →
      ‖α n s (0 : H n) - (0 : H n)‖ ≤ 2)
    (hlocal : ∀ (n : ℕ) (z : H n),
      ‖z‖ ≤ (n : ℝ) →
        ∃ s ∈ S, (1 : ℝ) ≤ ‖α n s z - z‖) :
    ∃ (W : Type u)
      (_ : NormedAddCommGroup W)
      (_ : InnerProductSpace ℂ W)
      (_ : CompleteSpace W)
      (β : G →* (W ≃ᵃⁱ[ℂ] W)),
      AffineUniformGeneratorDisplacement β S := by
  let x : ∀ n, H n := fun _ => 0
  let ℓ : G → ℕ :=
    fun g => ConnesRigidity.affineGeneratorWordLength S hgen g
  let B : (G × Bool) × (G × Bool) → ℝ :=
    fun q => (ℓ q.1.1 : ℝ) * 2 + (ℓ q.2.1 : ℝ) * 2
  have hword (n : ℕ) (g : G) :
      ‖α n g (0 : H n) - (0 : H n)‖ ≤ (ℓ g : ℝ) * 2 := by
    exact ConnesRigidity.affine_displacement_le_of_generatorWord
      (α n) 0 (S : Set G) 2 (fun s hs => hupper n s hs)
      (ConnesRigidity.affineGeneratorWordLength_spec S hgen g)
  have hbound : ∀ (n : ℕ)
      (q : (G × Bool) × (G × Bool)),
      ‖markedAffinePairDisplacement (α n) (x n) (x n) q‖ ≤ B q := by
    intro n q
    simp only [markedAffinePairDisplacement, markedAffineOrbitPoint, ite_self]
    change ‖α n q.1.1 (0 : H n) - α n q.2.1 (0 : H n)‖ ≤
      (ℓ q.1.1 : ℝ) * 2 + (ℓ q.2.1 : ℝ) * 2
    calc
      ‖α n q.1.1 (0 : H n) - α n q.2.1 (0 : H n)‖ ≤
          ‖α n q.1.1 (0 : H n)‖ +
            ‖α n q.2.1 (0 : H n)‖ := norm_sub_le _ _
      _ ≤ (ℓ q.1.1 : ℝ) * 2 + (ℓ q.2.1 : ℝ) * 2 := by
        simpa only [sub_zero] using add_le_add (hword n q.1.1) (hword n q.2.1)
  have hx : ∀ n,
      ConnesRigidity.IsAffineFixed (α n) (⊥ : Subgroup G) (x n) := by
    intro n g
    have hg : (g : G) = 1 := Subgroup.mem_bot.mp g.property
    simp only [hg, map_one, AffineIsometryEquiv.coe_one, id_eq, x]
  have hdist : Tendsto (fun n => ‖x n - x n‖)
      Filter.atTop (𝓝 (0 : ℝ)) := by
    simp only [sub_self, norm_zero, tendsto_const_nhds_iff]
  obtain ⟨L, R, hadd, _, hdense, _, _, _, _, hgram⟩ :=
    exists_marked_affine_ultralimit α x x
      (⊥ : Subgroup G) (⊥ : Subgroup G)
      hx hx B hbound 0 hdist
  refine ⟨R.realization.carrier, inferInstance, inferInstance,
    inferInstance, markedPairAffineAction L R hadd ((1 : G), false), ?_⟩
  apply affineUniformGeneratorDisplacement_marked_limit_of_local
    α S hlocal L R hadd hdense
  simpa only [Prod.forall, Bool.forall_bool] using hgram

end CornulierUltralimit

namespace CornulierUltralimit

open Filter Topology
open scoped BigOperators ComplexOrder InnerProductSpace Topology

universe u

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem exists_local_half_minimizer
    {X : Type*} [PseudoMetricSpace X] [CompleteSpace X] [Nonempty X]
    (D : X → ℝ) (hcont : Continuous D) (hpositive : ∀ x, 0 < D x)
    (N : ℕ) :
    ∃ x : X, ∀ y : X,
      dist x y ≤ (N : ℝ) * D x → D x / 2 ≤ D y := by
  classical
  by_contra hnot
  push Not at hnot
  choose f hdist hdrop using hnot
  let x₀ : X := Classical.choice (inferInstance : Nonempty X)
  let x : ℕ → X := fun n => Nat.rec x₀ (fun _ y => f y) n
  have hxzero : x 0 = x₀ := rfl
  have hxsucc (n : ℕ) : x (n + 1) = f (x n) := by
    simp only [x]
  have hdecay : ∀ n : ℕ,
      D (x n) ≤ D x₀ * ((1 / 2 : ℝ) ^ n) := by
    intro n
    induction n with
    | zero => simp only [hxzero, one_div, pow_zero, mul_one, Std.le_refl]
    | succ n ih =>
      calc
        D (x (n + 1)) ≤ D (x n) / 2 := by
          rw [hxsucc]
          exact le_of_lt (hdrop (x n))
        _ ≤ (D x₀ * ((1 / 2 : ℝ) ^ n)) / 2 := by
          gcongr
        _ = D x₀ * ((1 / 2 : ℝ) ^ (n + 1)) := by
          rw [pow_succ]
          ring
  have hstep : ∀ n : ℕ,
      dist (x n) (x (n + 1)) ≤
        ((N : ℝ) * D x₀) * ((1 / 2 : ℝ) ^ n) := by
    intro n
    calc
      dist (x n) (x (n + 1)) ≤ (N : ℝ) * D (x n) := by
        rw [hxsucc]
        exact hdist (x n)
      _ ≤ (N : ℝ) * (D x₀ * ((1 / 2 : ℝ) ^ n)) := by
        exact mul_le_mul_of_nonneg_left (hdecay n) (Nat.cast_nonneg N)
      _ = ((N : ℝ) * D x₀) * ((1 / 2 : ℝ) ^ n) := by
        ring
  have hcauchy : CauchySeq x :=
    cauchySeq_of_le_geometric (r := (1 / 2 : ℝ))
      (C := (N : ℝ) * D x₀) (by norm_num) hstep
  obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hzero : Tendsto (fun n => D (x n)) atTop (𝓝 (0 : ℝ)) := by
    apply squeeze_zero
      (fun n => (hpositive (x n)).le)
      hdecay
    simpa only [one_div, inv_pow, mul_zero] using
      (tendsto_const_nhds.mul
        (tendsto_pow_atTop_nhds_zero_of_lt_one
          (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (by norm_num : (1 / 2 : ℝ) < 1)))
  have hDz : D z = 0 :=
    tendsto_nhds_unique (hcont.tendsto z |>.comp hz) hzero
  exact (hpositive z).ne' hDz

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def generatorMaxDisplacement
    {G H : Type u} [Group G] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H]
    (α : G →* (H ≃ᵃⁱ[ℂ] H)) (S : Finset G) (x : H) : ℝ :=
  ((S.sup fun s => ‖α s x - x‖₊ : NNReal) : ℝ)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem continuous_generatorMaxDisplacement
    {G H : Type u} [Group G] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H]
    (α : G →* (H ≃ᵃⁱ[ℂ] H)) (S : Finset G) :
    Continuous (generatorMaxDisplacement α S) := by
  classical
  change Continuous (fun x : H => ((S.sup fun s => ‖α s x - x‖₊ : NNReal) : ℝ))
  apply NNReal.continuous_coe.comp
  induction S using Finset.induction_on with
  | empty => simpa only [Finset.sup_empty,
               bot_eq_zero'] using (continuous_const : Continuous fun _ : H => (0 : NNReal))
  | @insert a S ha ih =>
      simpa only [Finset.sup_insert, Pi.sub_apply, id_eq] using
        (((α a).continuous.sub continuous_id).nnnorm.sup ih)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem generator_displacement_le_max
    {G H : Type u} [Group G] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H]
    (α : G →* (H ≃ᵃⁱ[ℂ] H)) (S : Finset G) (x : H)
    {s : G} (hs : s ∈ S) :
    ‖α s x - x‖ ≤ generatorMaxDisplacement α S x := by
  change (‖α s x - x‖₊ : ℝ) ≤
    ((S.sup fun s => ‖α s x - x‖₊ : NNReal) : ℝ)
  exact_mod_cast (Finset.le_sup (f := fun s => ‖α s x - x‖₊) hs)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def affinePointStabilizer
    {G H : Type u} [Group G] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H]
    (α : G →* (H ≃ᵃⁱ[ℂ] H)) (x : H) : Subgroup G where
  carrier := {g : G | α g x = x}
  one_mem' := by simp only [Set.mem_ofPred_eq, map_one, AffineIsometryEquiv.coe_one, id_eq]
  mul_mem' := by
    intro a b ha hb
    change α (a * b) x = x
    rw [map_mul]
    change α a (α b x) = x
    rw [hb, ha]
  inv_mem' := by
    intro a ha
    change α a⁻¹ x = x
    apply (α a).injective
    calc
      α a (α a⁻¹ x) = α (a * a⁻¹) x := by
        rw [map_mul]
        rfl
      _ = x := by simp only [mul_inv_cancel, map_one, AffineIsometryEquiv.coe_one, id_eq]
      _ = α a x := ha.symm

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem generatorMaxDisplacement_pos_of_no_fixed
    {G H : Type u} [Group G] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H]
    (α : G →* (H ≃ᵃⁱ[ℂ] H)) (S : Finset G)
    (hgen : Subgroup.closure (S : Set G) = ⊤)
    (hfixed : ¬ ∃ x : H, ∀ g : G, α g x = x)
    (x : H) :
    0 < generatorMaxDisplacement α S x := by
  by_contra hnot
  have hzero : generatorMaxDisplacement α S x = 0 := by
    apply le_antisymm (le_of_not_gt hnot)
    exact_mod_cast (bot_le : (0 : NNReal) ≤
      S.sup (fun s => ‖α s x - x‖₊))
  have hgenerator : ∀ s ∈ S, α s x = x := by
    intro s hs
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    apply le_antisymm
    · simpa only [norm_le_zero_iff, hzero] using generator_displacement_le_max α S x hs
    · exact norm_nonneg _
  have hstabilizer :
      Subgroup.closure (S : Set G) ≤ affinePointStabilizer α x := by
    apply (Subgroup.closure_le (affinePointStabilizer α x)).2
    intro s hs
    exact hgenerator s hs
  apply hfixed
  refine ⟨x, fun g => ?_⟩
  have hg : g ∈ Subgroup.closure (S : Set G) := by
    rw [hgen]
    trivial
  exact hstabilizer hg

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem exists_generator_eq_max
    {G H : Type u} [Group G] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H]
    (α : G →* (H ≃ᵃⁱ[ℂ] H)) (S : Finset G) (x : H)
    (hpositive : 0 < generatorMaxDisplacement α S x) :
    ∃ s ∈ S, ‖α s x - x‖ = generatorMaxDisplacement α S x := by
  classical
  have hnonempty : S.Nonempty := by
    by_contra hempty
    have heq : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
    simp only [generatorMaxDisplacement, heq, Finset.sup_empty, bot_eq_zero', NNReal.coe_zero,
      lt_self_iff_false] at hpositive
  obtain ⟨s, hs, heq⟩ :=
    Finset.exists_mem_eq_sup S hnonempty (fun s => ‖α s x - x‖₊)
  refine ⟨s, hs, ?_⟩
  change (‖α s x - x‖₊ : ℝ) =
    ((S.sup fun s => ‖α s x - x‖₊ : NNReal) : ℝ)
  exact_mod_cast heq.symm

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem gromov_rescaled_generator_displacement_at_zero_le_two
    {G H : Type u} [Group G] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H]
    (α : G →* (H ≃ᵃⁱ[ℂ] H)) (S : Finset G) (x : H)
    (hpositive : 0 < generatorMaxDisplacement α S x)
    (s : G) (hs : s ∈ S) :
    ‖gromovRescaledAffineAction α x
      (generatorMaxDisplacement α S x / 2) s 0‖ ≤ 2 := by
  let D : ℝ := generatorMaxDisplacement α S x
  have hr : 0 < D / 2 := by
    dsimp [D]
    linarith
  calc
    ‖gromovRescaledAffineAction α x (D / 2) s 0‖ =
        (D / 2)⁻¹ * ‖α s x - x‖ := by
      simpa only [gromovRescaledAffineAction_apply, map_zero, inv_div, zero_add, sub_zero,
        smul_zero, add_zero] using
        gromovRescaledAffineAction_displacement_norm α x (D / 2) hr s 0
    _ ≤ (D / 2)⁻¹ * D := by
      apply mul_le_mul_of_nonneg_left
        (generator_displacement_le_max α S x hs)
      exact inv_nonneg.mpr hr.le
    _ = 2 := by
      field_simp [show D ≠ 0 by linarith]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem gromov_rescaled_generator_displacement_ge_one_on_ball
    {G H : Type u} [Group G] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H]
    (α : G →* (H ≃ᵃⁱ[ℂ] H)) (S : Finset G) (x : H) (N : ℕ)
    (hpositive : ∀ y : H, 0 < generatorMaxDisplacement α S y)
    (hlocal : ∀ y : H,
      dist x y ≤ (N : ℝ) * generatorMaxDisplacement α S x →
        generatorMaxDisplacement α S x / 2 ≤
          generatorMaxDisplacement α S y)
    (z : H) (hz : ‖z‖ ≤ (N : ℝ)) :
    ∃ s ∈ S, (1 : ℝ) ≤
      ‖gromovRescaledAffineAction α x
        (generatorMaxDisplacement α S x / 2) s z - z‖ := by
  let D : H → ℝ := generatorMaxDisplacement α S
  have hr : 0 < D x / 2 := by
    dsimp [D]
    linarith [hpositive x]
  let y : H := x + (D x / 2) • z
  have hdist : dist x y ≤ (N : ℝ) * D x := by
    calc
      dist x y = ‖(D x / 2) • z‖ := by
        dsimp [y]
        rw [dist_eq_norm]
        simp only [sub_add_cancel_left, norm_neg]
      _ = (D x / 2) * ‖z‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
      _ ≤ (D x / 2) * (N : ℝ) := by
        exact mul_le_mul_of_nonneg_left hz hr.le
      _ ≤ (N : ℝ) * D x := by
        have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
        nlinarith
  obtain ⟨s, hs, heq⟩ :=
    exists_generator_eq_max α S y (hpositive y)
  refine ⟨s, hs, ?_⟩
  rw [gromovRescaledAffineAction_displacement_norm α x (D x / 2) hr]
  have hlow : D x / 2 ≤ ‖α s y - y‖ := by
    rw [heq]
    exact hlocal y hdist
  calc
    (1 : ℝ) = (D x / 2)⁻¹ * (D x / 2) := by
      field_simp [show D x ≠ 0 by linarith]
    _ ≤ (D x / 2)⁻¹ * ‖α s y - y‖ := by
      exact mul_le_mul_of_nonneg_left hlow (inv_nonneg.mpr hr.le)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem exists_affineUniformGeneratorDisplacement_of_no_fixed
    {G H : Type u} [Group G] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (α : G →* (H ≃ᵃⁱ[ℂ] H)) (S : Finset G)
    (hgen : Subgroup.closure (S : Set G) = ⊤)
    (hfixed : ¬ ∃ x : H, ∀ g : G, α g x = x) :
    ∃ (W : Type u)
      (_ : NormedAddCommGroup W)
      (_ : InnerProductSpace ℂ W)
      (_ : CompleteSpace W)
      (β : G →* (W ≃ᵃⁱ[ℂ] W)),
      AffineUniformGeneratorDisplacement β S := by
  classical
  let D : H → ℝ := generatorMaxDisplacement α S
  have hcont : Continuous D := continuous_generatorMaxDisplacement α S
  have hpositive : ∀ x : H, 0 < D x :=
    generatorMaxDisplacement_pos_of_no_fixed α S hgen hfixed
  have hcenters : ∀ n : ℕ, ∃ x : H,
      ∀ y : H, dist x y ≤ (n : ℝ) * D x → D x / 2 ≤ D y := by
    intro n
    exact exists_local_half_minimizer D hcont hpositive n
  choose x hx using hcenters
  let γ : ℕ → G →* (H ≃ᵃⁱ[ℂ] H) := fun n =>
    gromovRescaledAffineAction α (x n) (D (x n) / 2)
  apply exists_affineUniformGeneratorDisplacement_of_local_sequence γ S hgen
  · intro n s hs
    simpa [γ, D] using
      gromov_rescaled_generator_displacement_at_zero_le_two
        α S (x n) (hpositive (x n)) s hs
  · intro n z hz
    exact gromov_rescaled_generator_displacement_ge_one_on_ball
      α S (x n) n hpositive (hx n) z hz

end CornulierUltralimit

end

section

open ConnesRigidity
open ConnesRigidity.CornulierUltralimit

universe u

variable {G V : Type u} [Group G]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def affineInvariantOrthogonalProjection
    (α : AffineHilbertAction G V) (x : V) :
    affineOrthogonalComplement α :=
  ⟨x - (normalFixedSubmodule (⊤ : Subgroup G)
      (affineLinearRepresentation α)).starProjection x,
    Submodule.sub_starProjection_mem_orthogonal x⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem affineInvariantOrthogonalProjection_coe
    (α : AffineHilbertAction G V) (x : V) :
    (affineInvariantOrthogonalProjection α x : V) =
      x - (normalFixedSubmodule (⊤ : Subgroup G)
        (affineLinearRepresentation α)).starProjection x := rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem affineAction_apply_eq_linear_add_zero
    (α : AffineHilbertAction G V) (g : G) (x : V) :
    α g x = (affineLinearRepresentation α g : V →L[ℂ] V) x + α g 0 := by
  have h := (α g).map_vsub x 0
  change (affineLinearRepresentation α g : V →L[ℂ] V) (x - 0) =
    α g x - α g 0 at h
  simpa only [sub_zero] using (eq_sub_iff_add_eq.mp h).symm

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem affineInvariantLinearProjection_action
    (hreal : ∀ φ : G →* Multiplicative ℝ,
      ∀ g : G, Multiplicative.toAdd (φ g) = 0)
    (α : AffineHilbertAction G V) (g : G) (x : V) :
    (normalFixedSubmodule (⊤ : Subgroup G)
        (affineLinearRepresentation α)).starProjection (α g x) =
      (normalFixedSubmodule (⊤ : Subgroup G)
        (affineLinearRepresentation α)).starProjection x := by
  let M := normalFixedSubmodule (⊤ : Subgroup G)
    (affineLinearRepresentation α)
  rw [affineAction_apply_eq_linear_add_zero, map_add,
    normalFixed_starProjection_commute
      (⊤ : Subgroup G) (affineLinearRepresentation α) g x,
    affineInvariantProjection_zero_of_no_real_characters hreal α g,
    add_zero]
  exact (Submodule.starProjection_apply_mem M x)
    ⟨g, Subgroup.mem_top g⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem affineInvariantOrthogonalProjection_equivariant
    (hreal : ∀ φ : G →* Multiplicative ℝ,
      ∀ g : G, Multiplicative.toAdd (φ g) = 0)
    (α : AffineHilbertAction G V) (g : G) (x : V) :
    affineInvariantOrthogonalProjection α (α g x) =
      affineOrthogonalAction hreal α g
        (affineInvariantOrthogonalProjection α x) := by
  apply Subtype.ext
  rw [affineOrthogonalAction_apply_coe,
    affineInvariantOrthogonalProjection_coe,
    affineInvariantOrthogonalProjection_coe,
    affineInvariantLinearProjection_action hreal α g x]
  have hfixed := (Submodule.starProjection_apply_mem
    (normalFixedSubmodule (⊤ : Subgroup G)
      (affineLinearRepresentation α)) x)
        (⟨g, Subgroup.mem_top g⟩ : (⊤ : Subgroup G))
  rw [affineAction_apply_eq_linear_add_zero α g x,
    affineAction_apply_eq_linear_add_zero α g
      (x - (normalFixedSubmodule (⊤ : Subgroup G)
        (affineLinearRepresentation α)).starProjection x),
    map_sub]
  rw [hfixed]
  abel

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem affineInvariantOrthogonalProjection_nonexpansive
    (α : AffineHilbertAction G V) (x y : V) :
    ‖affineInvariantOrthogonalProjection α x -
        affineInvariantOrthogonalProjection α y‖ ≤ ‖x - y‖ := by
  let M := normalFixedSubmodule (⊤ : Subgroup G)
    (affineLinearRepresentation α)
  change ‖(x - M.starProjection x) -
      (y - M.starProjection y)‖ ≤ ‖x - y‖
  rw [← Submodule.starProjection_orthogonal_val x,
    ← Submodule.starProjection_orthogonal_val y, ← map_sub]
  exact Mᗮ.norm_starProjection_apply_le _

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem affineOrthogonalAction_normalized
    (hreal : ∀ φ : G →* Multiplicative ℝ,
      ∀ g : G, Multiplicative.toAdd (φ g) = 0)
    (α : AffineHilbertAction G V) (S : Finset G)
    (hα : AffineUniformGeneratorDisplacement α S) :
    AffineUniformGeneratorDisplacement (affineOrthogonalAction hreal α) S := by
  intro z
  obtain ⟨s, hs, hbound⟩ := hα (z : V)
  refine ⟨s, hs, ?_⟩
  change 1 ≤ ‖(affineOrthogonalAction hreal α s z : V) - (z : V)‖
  rwa [affineOrthogonalAction_apply_coe]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem IsAffineFixed.affineInvariantOrthogonalProjection
    (hreal : ∀ φ : G →* Multiplicative ℝ,
      ∀ g : G, Multiplicative.toAdd (φ g) = 0)
    {α : AffineHilbertAction G V} {K : Subgroup G}
    {x : V} (hx : IsAffineFixed α K x) :
    IsAffineFixed (affineOrthogonalAction hreal α) K
      (affineInvariantOrthogonalProjection α x) := by
  intro k
  rw [← affineInvariantOrthogonalProjection_equivariant hreal α (k : G) x,
    hx k]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem affineOrthogonalAction_isMinimizingAffinePair
    (hreal : ∀ φ : G →* Multiplicative ℝ,
      ∀ g : G, Multiplicative.toAdd (φ g) = 0)
    (K₁ K₂ : Subgroup G) (S : Finset G)
    (α : AffineHilbertAction G V)
    (hα : AffineUniformGeneratorDisplacement α S)
    (x y : V)
    (hx : IsAffineFixed α K₁ x)
    (hy : IsAffineFixed α K₂ y)
    (hdist : ‖x - y‖ =
      cornulierNormalizedDistanceInfimum G K₁ K₂ S) :
    IsMinimizingAffinePair (affineOrthogonalAction hreal α) K₁ K₂
      (affineInvariantOrthogonalProjection α x)
      (affineInvariantOrthogonalProjection α y) := by
  exact isMinimizingAffinePair_of_normalized_nonexpansive_image
    K₁ K₂ S α (affineOrthogonalAction hreal α)
    (affineOrthogonalAction_normalized hreal α S hα)
    (affineInvariantOrthogonalProjection α)
    (affineInvariantOrthogonalProjection_equivariant hreal α)
    (affineInvariantOrthogonalProjection_nonexpansive α)
    x y hx hy hdist

end

section

open ConnesRigidity
open CornulierUltralimit

universe u

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem cornulier_normalizedMarkedAction_false
    (G : CountableDiscreteGroup.{u})
    (H K₁ K₂ : Subgroup G) (S : Finset G)
    (hSgen : Subgroup.closure (S : Set G) = ⊤)
    (hSroot : ∀ g ∈ S, g ∈ K₁ ∨ g ∈ K₂)
    (hgen : K₁ ⊔ K₂ = ⊤)
    (hH₁ : H ≤ Subgroup.normalizer (K₁ : Set G))
    (hH₂ : H ≤ Subgroup.normalizer (K₂ : Set G))
    (hreal : ∀ φ : G →* Multiplicative ℝ,
      ∀ g : G, Multiplicative.toAdd (φ g) = 0)
    (hcorel : HasCorelativeAffineOrbitBound H) :
    ¬ Nonempty (CornulierNormalizedMarkedAction G K₁ K₂ S) := by
  intro hnonempty
  obtain ⟨a, hdist, _⟩ :=
    exists_cornulierNormalizedExtremalAction_with_infimum
      K₁ K₂ S hSgen hSroot hnonempty
  let β := affineOrthogonalAction hreal a.action
  let x := affineInvariantOrthogonalProjection a.action a.leftPoint
  let y := affineInvariantOrthogonalProjection a.action a.rightPoint
  have hβ : AffineUniformGeneratorDisplacement β S :=
    affineOrthogonalAction_normalized hreal a.action S a.normalized
  have hmin : IsMinimizingAffinePair β K₁ K₂ x y :=
    affineOrthogonalAction_isMinimizingAffinePair hreal K₁ K₂ S
      a.action a.normalized a.leftPoint a.rightPoint
      a.left_fixed a.right_fixed hdist
  exact cornulier_normalized_minimizing_action_false
    H K₁ K₂ S hgen hH₁ hH₂ hcorel β hβ x y hmin
      (affineOrthogonalAction_no_linear_invariants hreal a.action)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem cornulier_theorem7_of_normalization
    (G : CountableDiscreteGroup.{u})
    (H K₁ K₂ : Subgroup G) (S : Finset G)
    (hSgen : Subgroup.closure (S : Set G) = ⊤)
    (hSroot : ∀ g ∈ S, g ∈ K₁ ∨ g ∈ K₂)
    (hgen : K₁ ⊔ K₂ = ⊤)
    (hH₁ : H ≤ Subgroup.normalizer (K₁ : Set G))
    (hH₂ : H ≤ Subgroup.normalizer (K₂ : Set G))
    (hreal : ∀ φ : G →* Multiplicative ℝ,
      ∀ g : G, Multiplicative.toAdd (φ g) = 0)
    (hcorel : HasCorelativeAffineOrbitBound H)
    (hleft : ∀ (V : Type u)
      (_ : NormedAddCommGroup V)
      (_ : InnerProductSpace ℂ V)
      (_ : CompleteSpace V)
      (α : AffineHilbertAction G V),
        ∃ x : V, IsAffineFixed α K₁ x)
    (hright : ∀ (V : Type u)
      (_ : NormedAddCommGroup V)
      (_ : InnerProductSpace ℂ V)
      (_ : CompleteSpace V)
      (α : AffineHilbertAction G V),
        ∃ x : V, IsAffineFixed α K₂ x)
    (hnormalize : ∀ (V : Type u)
      (_ : NormedAddCommGroup V)
      (_ : InnerProductSpace ℂ V)
      (_ : CompleteSpace V)
      (α : AffineHilbertAction G V),
        (¬ ∃ x : V, ∀ g : G, α g x = x) →
          ∃ (W : Type u)
            (_ : NormedAddCommGroup W)
            (_ : InnerProductSpace ℂ W)
            (_ : CompleteSpace W)
            (β : AffineHilbertAction G W),
              AffineUniformGeneratorDisplacement β S) :
    HasKazhdanPropertyT G := by
  apply hasKazhdanPropertyT_of_affine_fixed_points G
  intro V _ _ _ α
  by_contra hfixed
  obtain ⟨W, hnormed, hinner, hcomplete, β, hβ⟩ :=
    hnormalize V inferInstance inferInstance inferInstance α hfixed
  let : NormedAddCommGroup W := hnormed
  let : InnerProductSpace ℂ W := hinner
  let : CompleteSpace W := hcomplete
  obtain ⟨x, hx⟩ := hleft W inferInstance inferInstance inferInstance β
  obtain ⟨y, hy⟩ := hright W inferInstance inferInstance inferInstance β
  have hmarked :
      Nonempty (CornulierNormalizedMarkedAction G K₁ K₂ S) :=
    cornulierNormalizedMarkedAction_nonempty_of_fixed
      K₁ K₂ S β hβ ⟨x, hx⟩ ⟨y, hy⟩
  exact cornulier_normalizedMarkedAction_false
    G H K₁ K₂ S hSgen hSroot hgen hH₁ hH₂ hreal hcorel hmarked

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem cornulier_theorem7
    (G : CountableDiscreteGroup.{u})
    (H K₁ K₂ : Subgroup G) (S : Finset G)
    (hSgen : Subgroup.closure (S : Set G) = ⊤)
    (hSroot : ∀ g ∈ S, g ∈ K₁ ∨ g ∈ K₂)
    (hgen : K₁ ⊔ K₂ = ⊤)
    (hH₁ : H ≤ Subgroup.normalizer (K₁ : Set G))
    (hH₂ : H ≤ Subgroup.normalizer (K₂ : Set G))
    (hreal : ∀ φ : G →* Multiplicative ℝ,
      ∀ g : G, Multiplicative.toAdd (φ g) = 0)
    (hcorel : HasCorelativeAffineOrbitBound H)
    (hleft : ∀ (V : Type u)
      (_ : NormedAddCommGroup V)
      (_ : InnerProductSpace ℂ V)
      (_ : CompleteSpace V)
      (α : AffineHilbertAction G V),
        ∃ x : V, IsAffineFixed α K₁ x)
    (hright : ∀ (V : Type u)
      (_ : NormedAddCommGroup V)
      (_ : InnerProductSpace ℂ V)
      (_ : CompleteSpace V)
      (α : AffineHilbertAction G V),
        ∃ x : V, IsAffineFixed α K₂ x) :
    HasKazhdanPropertyT G := by
  apply cornulier_theorem7_of_normalization
    G H K₁ K₂ S hSgen hSroot hgen hH₁ hH₂ hreal hcorel hleft hright
  intro V _ _ _ α hno
  exact exists_affineUniformGeneratorDisplacement_of_no_fixed
    α S hSgen hno

end

section

open ConnesRigidity MeasureTheory Set
open scoped BigOperators ENNReal NNReal

universe u

variable {A : Type u} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
variable [MeasurableSpace (DiscreteCharacterSpace A)]
  [BorelSpace (DiscreteCharacterSpace A)]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem shalom_normalized_restriction_variation_bound
    {ε : ℝ} (hε : 0 ≤ ε) (hsmall : ε ≤ (1 / 10 : ℝ)) :
    (2 * ε + ε ^ 2) / (1 - ε ^ 2) ≤ (7 / 33 : ℝ) := by
  have hden : 0 < 1 - ε ^ 2 := by nlinarith
  apply (div_le_iff₀ hden).2
  nlinarith

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem shalom_normalized_restriction_variation_lt_one_fourth
    {ε : ℝ} (hε : 0 ≤ ε) (hsmall : ε ≤ (1 / 10 : ℝ)) :
    (2 * ε + ε ^ 2) / (1 - ε ^ 2) < (1 / 4 : ℝ) := by
  calc
    (2 * ε + ε ^ 2) / (1 - ε ^ 2) ≤ 7 / 33 :=
      shalom_normalized_restriction_variation_bound hε hsmall
    _ < 1 / 4 := by norm_num

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem circle_nonpositive_real_energy (z : Circle)
    (hz : (z : ℂ).re ≤ 0) :
    (2 : ℝ) ≤ ‖(z : ℂ) - 1‖ ^ 2 := by
  have hnorm : Complex.normSq (z : ℂ) = 1 := Circle.normSq_coe z
  rw [Complex.sq_norm, Complex.normSq_apply]
  rw [Complex.normSq_apply] at hnorm
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero, ge_iff_le]
  linarith

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def spectralNonpositiveRealSet (a : A) : Set (DiscreteCharacterSpace A) :=
  {χ | (((χ (Multiplicative.ofAdd a) : Circle) : ℂ).re) ≤ 0}

omit [DiscreteTopology A] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem spectralNonpositiveRealSet_measurable (a : A) :
    MeasurableSet (spectralNonpositiveRealSet a) := by
  exact (Complex.continuous_re.comp
    (continuous_character_evaluation a)).measurable
      (measurableSet_Iic)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem spectralNonpositiveRealSet_measureReal_mul_two_le_energy
    (μ : ProbabilityMeasure (DiscreteCharacterSpace A)) (a : A) :
    2 * (μ : Measure (DiscreteCharacterSpace A)).real
        (spectralNonpositiveRealSet a) ≤
      spectralDetectionEnergy μ a := by
  have hsubset : spectralNonpositiveRealSet a ⊆
      spectralLargeDisplacementSet a (Real.sqrt 2) := by
    intro χ hχ
    change Real.sqrt 2 ≤
      ‖((χ (Multiplicative.ofAdd a) : Circle) : ℂ) - 1‖
    have henergy := circle_nonpositive_real_energy
      (χ (Multiplicative.ofAdd a)) hχ
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
      Real.sqrt_nonneg (2 : ℝ),
      norm_nonneg (((χ (Multiplicative.ofAdd a) : Circle) : ℂ) - 1)]
  calc
    2 * (μ : Measure (DiscreteCharacterSpace A)).real
        (spectralNonpositiveRealSet a) ≤
      2 * (μ : Measure (DiscreteCharacterSpace A)).real
        (spectralLargeDisplacementSet a (Real.sqrt 2)) := by
      exact mul_le_mul_of_nonneg_left
        (measureReal_mono
          (μ := (μ : Measure (DiscreteCharacterSpace A))) hsubset)
        (by norm_num)
    _ = (Real.sqrt 2) ^ 2 *
        (μ : Measure (DiscreteCharacterSpace A)).real
          (spectralLargeDisplacementSet a (Real.sqrt 2)) := by
      rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    _ ≤ spectralDetectionEnergy μ a :=
      spectralLargeDisplacement_measureReal_mul_sq_le_energy μ a
        (Real.sqrt 2) (Real.sqrt_nonneg _)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def spectralTorusWindow (a b : A) : Set (DiscreteCharacterSpace A) :=
  (spectralNonpositiveRealSet a ∪ spectralNonpositiveRealSet b)ᶜ

omit [DiscreteTopology A] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem spectralTorusWindow_measurable (a b : A) :
    MeasurableSet (spectralTorusWindow a b) :=
  ((spectralNonpositiveRealSet_measurable a).union
    (spectralNonpositiveRealSet_measurable b)).compl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem spectralTorusWindow_compl_measureReal_mul_two_le_energy_sum
    (μ : ProbabilityMeasure (DiscreteCharacterSpace A)) (a b : A) :
    2 * (μ : Measure (DiscreteCharacterSpace A)).real
        (spectralTorusWindow a b)ᶜ ≤
      spectralDetectionEnergy μ a + spectralDetectionEnergy μ b := by
  have ha := spectralNonpositiveRealSet_measureReal_mul_two_le_energy μ a
  have hb := spectralNonpositiveRealSet_measureReal_mul_two_le_energy μ b
  have hunion := measureReal_union_le
    (μ := (μ : Measure (DiscreteCharacterSpace A)))
    (spectralNonpositiveRealSet a) (spectralNonpositiveRealSet b)
  have hbad : 2 * (μ : Measure (DiscreteCharacterSpace A)).real
      (spectralNonpositiveRealSet a ∪ spectralNonpositiveRealSet b) ≤
      spectralDetectionEnergy μ a + spectralDetectionEnergy μ b := by
    linarith
  simpa only [spectralTorusWindow, compl_compl] using hbad

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem spectralTorusWindow_compl_measureReal_le_sq
    (μ : ProbabilityMeasure (DiscreteCharacterSpace A)) (a b : A)
    {ε : ℝ}
    (ha : spectralDetectionEnergy μ a ≤ ε ^ 2)
    (hb : spectralDetectionEnergy μ b ≤ ε ^ 2) :
    (μ : Measure (DiscreteCharacterSpace A)).real
      (spectralTorusWindow a b)ᶜ ≤ ε ^ 2 := by
  have hwindow :=
    spectralTorusWindow_compl_measureReal_mul_two_le_energy_sum μ a b
  linarith

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem spectralTorusWindow_measureReal_ge_one_sub_sq
    (μ : ProbabilityMeasure (DiscreteCharacterSpace A)) (a b : A)
    {ε : ℝ}
    (ha : spectralDetectionEnergy μ a ≤ ε ^ 2)
    (hb : spectralDetectionEnergy μ b ≤ ε ^ 2) :
    1 - ε ^ 2 ≤ (μ : Measure (DiscreteCharacterSpace A)).real
      (spectralTorusWindow a b) := by
  have hsum := measureReal_add_measureReal_compl
    (μ := (μ : Measure (DiscreteCharacterSpace A)))
    (spectralTorusWindow_measurable a b)
  rw [probReal_univ] at hsum
  have hbad := spectralTorusWindow_compl_measureReal_le_sq μ a b ha hb
  linarith

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem spectralTorusWindow_measureReal_pos
    (μ : ProbabilityMeasure (DiscreteCharacterSpace A)) (a b : A)
    {ε : ℝ} (hsmall : ε ≤ (1 / 10 : ℝ))
    (hε : 0 ≤ ε)
    (ha : spectralDetectionEnergy μ a ≤ ε ^ 2)
    (hb : spectralDetectionEnergy μ b ≤ ε ^ 2) :
    0 < (μ : Measure (DiscreteCharacterSpace A)).real
      (spectralTorusWindow a b) := by
  have hden : 0 < 1 - ε ^ 2 := by nlinarith
  exact lt_of_lt_of_le hden
    (spectralTorusWindow_measureReal_ge_one_sub_sq μ a b ha hb)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem shalom_conditioned_variation_lt_one_fourth
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : ProbabilityMeasure Ω) {U : Set Ω}
    (hU : 0 < (μ : Measure Ω).real U)
    (hUmeas : MeasurableSet U)
    {ε : ℝ} (hε : 0 ≤ ε) (hsmall : ε ≤ (1 / 10 : ℝ))
    (hdiscard : (μ : Measure Ω).real Uᶜ ≤ ε ^ 2)
    (s t : Set Ω)
    (hvariation : |(μ : Measure Ω).real s -
      (μ : Measure Ω).real t| ≤ 2 * ε) :
    |(conditionedProbability μ U hU : Measure Ω).real s -
      (conditionedProbability μ U hU : Measure Ω).real t| <
        (1 / 4 : ℝ) := by
  have hden : 0 < 1 - ε ^ 2 := by nlinarith
  have hsurvive : 1 - ε ^ 2 ≤ (μ : Measure Ω).real U := by
    have htotal := measureReal_add_measureReal_compl
      (μ := (μ : Measure Ω)) hUmeas
    rw [probReal_univ] at htotal
    linarith
  have hnum : 0 ≤ 2 * ε + ε ^ 2 := by positivity
  calc
    |(conditionedProbability μ U hU : Measure Ω).real s -
      (conditionedProbability μ U hU : Measure Ω).real t| ≤
        (|(μ : Measure Ω).real s - (μ : Measure Ω).real t| +
          (μ : Measure Ω).real Uᶜ) / (μ : Measure Ω).real U :=
      abs_conditionedProbability_measureReal_sub_le μ hU hUmeas s t
    _ ≤ (2 * ε + ε ^ 2) / (μ : Measure Ω).real U := by
      gcongr
    _ ≤ (2 * ε + ε ^ 2) / (1 - ε ^ 2) :=
      div_le_div_of_nonneg_left hnum hden hsurvive
    _ < 1 / 4 :=
      shalom_normalized_restriction_variation_lt_one_fourth hε hsmall

end

section

open ConnesRigidity MeasureTheory Set

universe u





/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem circle_re_pos_iff_arg_mem_Ioo (z : Circle) :
    0 < (z : ℂ).re ↔
      -(Real.pi / 2) < Complex.arg (z : ℂ) ∧
        Complex.arg (z : ℂ) < Real.pi / 2 := by
  simpa only [z.coe_ne_zero, or_false, abs_lt] using
    (Complex.abs_arg_lt_pi_div_two_iff (z := (z : ℂ))).symm

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem circle_arg_mul_of_no_wrap_le (z w : Circle)
    (hlower : -Real.pi < Complex.arg (z : ℂ) + Complex.arg (w : ℂ))
    (hupper : Complex.arg (z : ℂ) + Complex.arg (w : ℂ) ≤ Real.pi) :
    Complex.arg ((z * w : Circle) : ℂ) =
      Complex.arg (z : ℂ) + Complex.arg (w : ℂ) := by
  change Complex.arg ((z : ℂ) * (w : ℂ)) = _
  exact Complex.arg_mul z.coe_ne_zero w.coe_ne_zero ⟨hlower, hupper⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem circle_arg_mul_of_no_wrap (z w : Circle)
    (hlower : -Real.pi < Complex.arg (z : ℂ) + Complex.arg (w : ℂ))
    (hupper : Complex.arg (z : ℂ) + Complex.arg (w : ℂ) < Real.pi) :
    Complex.arg ((z * w : Circle) : ℂ) =
      Complex.arg (z : ℂ) + Complex.arg (w : ℂ) :=
  circle_arg_mul_of_no_wrap_le z w hlower hupper.le

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem circle_arg_inv_of_lt_pi (z : Circle)
    (hz : Complex.arg (z : ℂ) < Real.pi) :
    Complex.arg ((z⁻¹ : Circle) : ℂ) = -Complex.arg (z : ℂ) := by
  change Complex.arg ((z : ℂ)⁻¹) = -Complex.arg (z : ℂ)
  rw [Complex.arg_inv, ite_eq_right (ne_of_lt hz)]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem circle_arg_div_of_no_wrap (z w : Circle)
    (hw : Complex.arg (w : ℂ) < Real.pi)
    (hlower : -Real.pi < Complex.arg (z : ℂ) - Complex.arg (w : ℂ))
    (hupper : Complex.arg (z : ℂ) - Complex.arg (w : ℂ) < Real.pi) :
    Complex.arg ((z / w : Circle) : ℂ) =
      Complex.arg (z : ℂ) - Complex.arg (w : ℂ) := by
  rw [div_eq_mul_inv]
  rw [circle_arg_mul_of_no_wrap]
  · rw [circle_arg_inv_of_lt_pi w hw]
    exact sub_eq_add_neg _ _
  · rw [circle_arg_inv_of_lt_pi w hw]
    exact hlower
  · rw [circle_arg_inv_of_lt_pi w hw]
    exact hupper

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem circle_arg_mul_of_re_pos (z w : Circle)
    (hz : 0 < (z : ℂ).re) (hw : 0 < (w : ℂ).re) :
    Complex.arg ((z * w : Circle) : ℂ) =
      Complex.arg (z : ℂ) + Complex.arg (w : ℂ) := by
  obtain ⟨hzlo, hzhi⟩ := (circle_re_pos_iff_arg_mem_Ioo z).mp hz
  obtain ⟨hwlo, hwhi⟩ := (circle_re_pos_iff_arg_mem_Ioo w).mp hw
  exact circle_arg_mul_of_no_wrap z w (by linarith) (by linarith)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem circle_arg_div_of_re_pos (z w : Circle)
    (hz : 0 < (z : ℂ).re) (hw : 0 < (w : ℂ).re) :
    Complex.arg ((z / w : Circle) : ℂ) =
      Complex.arg (z : ℂ) - Complex.arg (w : ℂ) := by
  obtain ⟨hzlo, hzhi⟩ := (circle_re_pos_iff_arg_mem_Ioo z).mp hz
  obtain ⟨hwlo, hwhi⟩ := (circle_re_pos_iff_arg_mem_Ioo w).mp hw
  apply circle_arg_div_of_no_wrap z w
  · linarith [Real.pi_pos]
  · linarith
  · linarith

variable {A : Type u} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
variable [MeasurableSpace (DiscreteCharacterSpace A)]
  [BorelSpace (DiscreteCharacterSpace A)]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def spectralArgCoordinates (a b : A)
    (χ : DiscreteCharacterSpace A) : ℝ × ℝ :=
  (Complex.arg (((χ (Multiplicative.ofAdd a) : Circle) : ℂ)),
    Complex.arg (((χ (Multiplicative.ofAdd b) : Circle) : ℂ)))

omit [DiscreteTopology A] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem measurable_spectralArgCoordinates (a b : A) :
    Measurable (spectralArgCoordinates a b) :=
  (Complex.measurable_arg.comp
    (continuous_character_evaluation a).measurable).prodMk
    (Complex.measurable_arg.comp
      (continuous_character_evaluation b).measurable)

omit [DiscreteTopology A] [MeasurableSpace (DiscreteCharacterSpace A)]
  [BorelSpace (DiscreteCharacterSpace A)] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem spectralTorusWindow_mem_iff_re_pos (a b : A)
    (χ : DiscreteCharacterSpace A) :
    χ ∈ spectralTorusWindow a b ↔
      0 < (((χ (Multiplicative.ofAdd a) : Circle) : ℂ).re) ∧
        0 < (((χ (Multiplicative.ofAdd b) : Circle) : ℂ).re) := by
  simp only [spectralTorusWindow, spectralNonpositiveRealSet, compl_union, mem_inter_iff,
    mem_compl_iff, mem_ofPred_eq, not_le]

omit [DiscreteTopology A] [MeasurableSpace (DiscreteCharacterSpace A)]
  [BorelSpace (DiscreteCharacterSpace A)] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem spectralArg_add_of_window (a b : A)
    (χ : DiscreteCharacterSpace A) (hχ : χ ∈ spectralTorusWindow a b) :
    Complex.arg (((χ (Multiplicative.ofAdd (a + b)) : Circle) : ℂ)) =
      (spectralArgCoordinates a b χ).1 +
        (spectralArgCoordinates a b χ).2 := by
  obtain ⟨ha, hb⟩ := (spectralTorusWindow_mem_iff_re_pos a b χ).mp hχ
  rw [ofAdd_add, map_mul]
  exact circle_arg_mul_of_re_pos
    (χ (Multiplicative.ofAdd a)) (χ (Multiplicative.ofAdd b)) ha hb

omit [DiscreteTopology A] [MeasurableSpace (DiscreteCharacterSpace A)]
  [BorelSpace (DiscreteCharacterSpace A)] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem spectralArg_sub_of_window (a b : A)
    (χ : DiscreteCharacterSpace A) (hχ : χ ∈ spectralTorusWindow a b) :
    Complex.arg (((χ (Multiplicative.ofAdd (a - b)) : Circle) : ℂ)) =
      (spectralArgCoordinates a b χ).1 -
        (spectralArgCoordinates a b χ).2 := by
  obtain ⟨ha, hb⟩ := (spectralTorusWindow_mem_iff_re_pos a b χ).mp hχ
  rw [ofAdd_sub, map_div]
  exact circle_arg_div_of_re_pos
    (χ (Multiplicative.ofAdd a)) (χ (Multiplicative.ofAdd b)) ha hb

omit [DiscreteTopology A] [MeasurableSpace (DiscreteCharacterSpace A)]
  [BorelSpace (DiscreteCharacterSpace A)] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem spectralArgCoordinates_tpos (a b : A)
    (χ : DiscreteCharacterSpace A) (hχ : χ ∈ spectralTorusWindow a b) :
    spectralArgCoordinates a (b - a) χ =
      ((spectralArgCoordinates a b χ).1,
        (spectralArgCoordinates a b χ).2 -
          (spectralArgCoordinates a b χ).1) := by
  apply Prod.ext
  · rfl
  · exact spectralArg_sub_of_window b a χ (by
      simpa only [spectralTorusWindow, union_comm, compl_union, mem_inter_iff,
        mem_compl_iff] using hχ)

omit [DiscreteTopology A] [MeasurableSpace (DiscreteCharacterSpace A)]
  [BorelSpace (DiscreteCharacterSpace A)] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem spectralArgCoordinates_spos (a b : A)
    (χ : DiscreteCharacterSpace A) (hχ : χ ∈ spectralTorusWindow a b) :
    spectralArgCoordinates (a - b) b χ =
      ((spectralArgCoordinates a b χ).1 -
        (spectralArgCoordinates a b χ).2,
        (spectralArgCoordinates a b χ).2) := by
  apply Prod.ext
  · exact spectralArg_sub_of_window a b χ hχ
  · rfl

omit [DiscreteTopology A] [MeasurableSpace (DiscreteCharacterSpace A)]
  [BorelSpace (DiscreteCharacterSpace A)] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem spectralArgCoordinates_tneg (a b : A)
    (χ : DiscreteCharacterSpace A) (hχ : χ ∈ spectralTorusWindow a b) :
    spectralArgCoordinates a (b + a) χ =
      ((spectralArgCoordinates a b χ).1,
        (spectralArgCoordinates a b χ).2 +
          (spectralArgCoordinates a b χ).1) := by
  apply Prod.ext
  · rfl
  · exact spectralArg_add_of_window b a χ (by
      simpa only [spectralTorusWindow, union_comm, compl_union, mem_inter_iff,
        mem_compl_iff] using hχ)

omit [DiscreteTopology A] [MeasurableSpace (DiscreteCharacterSpace A)]
  [BorelSpace (DiscreteCharacterSpace A)] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem spectralArgCoordinates_sneg (a b : A)
    (χ : DiscreteCharacterSpace A) (hχ : χ ∈ spectralTorusWindow a b) :
    spectralArgCoordinates (a + b) b χ =
      ((spectralArgCoordinates a b χ).1 +
        (spectralArgCoordinates a b χ).2,
        (spectralArgCoordinates a b χ).2) := by
  apply Prod.ext
  · exact spectralArg_add_of_window a b χ hχ
  · rfl

end

section

open ConnesRigidity MeasureTheory

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private abbrev IntegerRankTwo := Fin 2 → ℤ

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem integerRankTwo_basis_decomposition (v : IntegerRankTwo) :
    v = v 0 • (Pi.single 0 1) +
      v 1 • (Pi.single 1 1) := by
  funext i
  fin_cases i <;>
    simp

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem integerDual_eq_one_iff_coordinate_values
    (χ : DiscreteCharacterSpace IntegerRankTwo) :
    χ = 1 ↔
      χ (Multiplicative.ofAdd (Pi.single 0 1)) = 1 ∧
        χ (Multiplicative.ofAdd (Pi.single 1 1)) = 1 := by
  constructor
  · rintro rfl
    simp only [PontryaginDual.one_apply, and_self]
  · rintro ⟨hzero, hone⟩
    apply PontryaginDual.ext
    intro z
    let v : IntegerRankTwo := Multiplicative.toAdd z
    change χ (Multiplicative.ofAdd v) = 1
    rw [integerRankTwo_basis_decomposition v]
    change
      χ ((Multiplicative.ofAdd (Pi.single 0 1)) ^ (v 0) *
        (Multiplicative.ofAdd (Pi.single 1 1)) ^ (v 1)) = 1
    simp only [Fin.isValue, map_mul, map_zpow, hzero, one_zpow, hone, mul_one]





/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem integerDual_spectralArgCoordinates_eq_zero_iff
    (χ : DiscreteCharacterSpace IntegerRankTwo) :
    spectralArgCoordinates (Pi.single 0 1)
      (Pi.single 1 1) χ = (0, 0) ↔ χ = 1 := by
  rw [Prod.ext_iff]
  change
    (Complex.arg ((χ (Multiplicative.ofAdd (Pi.single 0 1)) : Circle) : ℂ)
        = 0 ∧
      Complex.arg ((χ (Multiplicative.ofAdd (Pi.single 1 1)) : Circle) : ℂ)
        = 0) ↔ χ = 1
  rw [Circle.arg_eq_zero, Circle.arg_eq_zero]
  exact (integerDual_eq_one_iff_coordinate_values χ).symm

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem integerDual_spectralArgCoordinates_origin_preimage :
    spectralArgCoordinates (Pi.single 0 1)
      (Pi.single 1 1) ⁻¹' {(0, 0)} =
        ({1} : Set (DiscreteCharacterSpace IntegerRankTwo)) := by
  ext χ
  simp only [Set.mem_preimage, Set.mem_singleton_iff,
    integerDual_spectralArgCoordinates_eq_zero_iff]

end

section

open MeasureTheory Set

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem shalom_four_sector_mass_gap
    (a b c d u v w z : ℝ)
    (hmass : a + b + c + d = 1)
    (hu : u ≤ a) (hv : v ≤ b) (hw : w ≤ d) (hz : z ≤ c) :
    (1 / 4 : ℝ) ≤ |u - (a + b)| ∨
      (1 / 4 : ℝ) ≤ |v - (a + b)| ∨
      (1 / 4 : ℝ) ≤ |w - (d + c)| ∨
      (1 / 4 : ℝ) ≤ |z - (d + c)| := by
  by_contra h
  push Not at h
  rcases h with ⟨hu', hv', hw', hz'⟩
  have ha : a ≤ |v - (a + b)| := by
    linarith [neg_le_abs (v - (a + b))]
  have hb : b ≤ |u - (a + b)| := by
    linarith [neg_le_abs (u - (a + b))]
  have hc : c ≤ |w - (d + c)| := by
    linarith [neg_le_abs (w - (d + c))]
  have hd : d ≤ |z - (d + c)| := by
    linarith [neg_le_abs (z - (d + c))]
  norm_num at hu' hv' hw' hz'
  linarith

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem shalom_three_sector_mass_gap
    (a b c u v w : ℝ)
    (hmass : a + b + c = 1)
    (hu : u ≤ c) (hv : v ≤ a) (hw : w ≤ b) :
    (1 / 5 : ℝ) ≤ |u - (a + b)| ∨
      (1 / 5 : ℝ) ≤ |v - (c + b)| ∨
      (1 / 5 : ℝ) ≤ |w - a| := by
  by_contra h
  push Not at h
  rcases h with ⟨hu', hv', hw'⟩
  have hAB : a + b ≤ c + |u - (a + b)| := by
    linarith [neg_le_abs (u - (a + b))]
  have hCB : c + b ≤ a + |v - (c + b)| := by
    linarith [neg_le_abs (v - (c + b))]
  have hA : a ≤ b + |w - a| := by
    linarith [neg_le_abs (w - a)]
  norm_num at hu' hv' hw'
  linarith

end

section
open ConnesRigidity MeasureTheory Set
open scoped BigOperators ENNReal NNReal CompactlySupported

section RegularSpectralMeasure

variable {Ω : Type*} [TopologicalSpace Ω] [CompactSpace Ω] [T2Space Ω]
  [MeasurableSpace Ω] [BorelSpace Ω]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem regular_measureReal_le_add_of_testFunctions
    (μ ν : Measure Ω) [μ.Regular] [ν.Regular]
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (c : ℝ) (hc : 0 ≤ c)
    (htest : ∀ f : C_c(Ω, ℝ),
      (∀ x : Ω, 0 ≤ f x ∧ f x ≤ 1) →
        (∫ x, f x ∂μ) ≤ (∫ x, f x ∂ν) + c)
    {s : Set Ω} (hs : MeasurableSet s) :
    μ.real s ≤ ν.real s + c := by
  by_contra hnot
  have hstrict : ν.real s + c < μ.real s := lt_of_not_ge hnot
  have hrnonneg : 0 ≤ ν.real s + c :=
    add_nonneg measureReal_nonneg hc
  have hENN : ENNReal.ofReal (ν.real s + c) < μ s :=
    (ENNReal.ofReal_lt_iff_lt_toReal hrnonneg (measure_ne_top μ s)).mpr hstrict
  obtain ⟨K, hKs, hK, hKmass⟩ := hs.exists_lt_isCompact hENN
  have hKreal : ν.real s + c < μ.real K :=
    (ENNReal.ofReal_lt_iff_lt_toReal hrnonneg
      (measure_ne_top μ K)).mp hKmass
  let ε : ℝ := μ.real K - (ν.real s + c)
  have hε : 0 < ε := sub_pos.mpr hKreal
  obtain ⟨U, hKU, hUopen, hUmeasure⟩ :=
    K.exists_isOpen_lt_add (μ := ν) (measure_ne_top ν K)
      (ENNReal.ofReal_pos.mpr hε).ne'
  have hUreal : ν.real U < ν.real K + ε := by
    have hfinite : ν K + ENNReal.ofReal ε ≠ ∞ :=
      ENNReal.add_ne_top.mpr ⟨measure_ne_top ν K, ENNReal.ofReal_ne_top⟩
    have hreal := (ENNReal.toReal_lt_toReal
      (measure_ne_top ν U) hfinite).mpr hUmeasure
    simpa only [measureReal_def, gt_iff_lt, ne_eq, measure_ne_top, not_false_eq_true,
      ENNReal.ofReal_ne_top, ENNReal.toReal_add, ENNReal.toReal_ofReal hε.le] using hreal
  obtain ⟨f, hfK, hfcompact, hfsupport, hfbounds⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hK hUopen hKU
  let fc : C_c(Ω, ℝ) := ⟨f, hfcompact⟩
  have hleft : μ.real K ≤ ∫ x, fc x ∂μ := by
    rw [← integral_indicator_one hK.measurableSet]
    apply integral_mono
    · exact (continuousOn_const.integrableOn_compact hK).integrable_indicator
        hK.measurableSet
    · exact fc.integrable
    · intro x
      by_cases hx : x ∈ K
      · simp only [hx, indicator_of_mem, Pi.one_apply]
        change 1 ≤ f x
        have hvalue : f x = 1 := by simpa only [Pi.one_apply] using hfK hx
        simp only [hvalue, Std.le_refl]
      · simp only [hx, not_false_eq_true, indicator_of_notMem]
        change 0 ≤ f x
        exact (hfbounds x).1
  have hright : (∫ x, fc x ∂ν) ≤ ν.real U := by
    rw [← integral_indicator_one hUopen.measurableSet]
    apply integral_mono
    · exact fc.integrable
    · exact IntegrableOn.integrable_indicator integrableOn_const
        hUopen.measurableSet
    · intro x
      by_cases hx : x ∈ U
      · simp only [hx, indicator_of_mem, Pi.one_apply]
        change f x ≤ 1
        exact (hfbounds x).2
      · have hzero : f x = 0 :=
          image_eq_zero_of_notMem_tsupport
            (fun hxsupport => hx (hfsupport hxsupport))
        simp only [hx, not_false_eq_true, indicator_of_notMem, ge_iff_le]
        change f x ≤ 0
        simp only [hzero, Std.le_refl]
  have hKν : ν.real K ≤ ν.real s :=
    measureReal_mono (μ := ν) hKs
  have htest' := htest fc hfbounds
  dsimp [ε] at hUreal
  linarith

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem abs_regular_measureReal_sub_le_of_testFunctions
    (μ ν : Measure Ω) [μ.Regular] [ν.Regular]
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (c : ℝ) (hc : 0 ≤ c)
    (htest : ∀ f : C_c(Ω, ℝ),
      (∀ x : Ω, 0 ≤ f x ∧ f x ≤ 1) →
        |(∫ x, f x ∂μ) - (∫ x, f x ∂ν)| ≤ c)
    {s : Set Ω} (hs : MeasurableSet s) :
    |μ.real s - ν.real s| ≤ c := by
  apply abs_le.mpr
  constructor
  · have h := regular_measureReal_le_add_of_testFunctions ν μ c hc
      (fun f hf => by
        have hbound := (abs_le.mp (htest f hf)).1
        linarith)
      hs
    linarith
  · have h := regular_measureReal_le_add_of_testFunctions μ ν c hc
      (fun f hf => by
        have hbound := (abs_le.mp (htest f hf)).2
        linarith)
      hs
    linarith

end RegularSpectralMeasure

universe u

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem bounded_vector_state_lipschitz
    {W : Type u} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (T : W →L[ℂ] W) (x y : W)
    (hT : ‖T‖ ≤ 1) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    |(inner ℂ x (T x)).re - (inner ℂ y (T y)).re| ≤
      2 * ‖x - y‖ := by
  have hidentity :
      inner ℂ x (T x) - inner ℂ y (T y) =
        inner ℂ (x - y) (T x) + inner ℂ y (T (x - y)) := by
    rw [inner_sub_left, map_sub, inner_sub_right]
    ring
  have hTx : ‖T x‖ ≤ 1 := by
    calc
      ‖T x‖ ≤ ‖T‖ * ‖x‖ := T.le_opNorm x
      _ ≤ 1 := by simpa only [hx, mul_one] using hT
  have hTsub : ‖T (x - y)‖ ≤ ‖x - y‖ := by
    calc
      ‖T (x - y)‖ ≤ ‖T‖ * ‖x - y‖ := T.le_opNorm (x - y)
      _ ≤ 1 * ‖x - y‖ :=
        mul_le_mul_of_nonneg_right hT (norm_nonneg _)
      _ = ‖x - y‖ := one_mul _
  calc
    |(inner ℂ x (T x)).re - (inner ℂ y (T y)).re| =
        |(inner ℂ x (T x) - inner ℂ y (T y)).re| := by
          exact congrArg abs (Complex.sub_re _ _).symm
    _ ≤ ‖inner ℂ x (T x) - inner ℂ y (T y)‖ :=
      Complex.abs_re_le_norm _
    _ = ‖inner ℂ (x - y) (T x) + inner ℂ y (T (x - y))‖ := by
      rw [hidentity]
    _ ≤ ‖inner ℂ (x - y) (T x)‖ +
          ‖inner ℂ y (T (x - y))‖ := norm_add_le _ _
    _ ≤ ‖x - y‖ * ‖T x‖ + ‖y‖ * ‖T (x - y)‖ :=
      add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
    _ ≤ ‖x - y‖ * 1 + 1 * ‖x - y‖ := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left hTx (norm_nonneg _)
      · rw [hy]
        exact mul_le_mul_of_nonneg_left hTsub zero_le_one
    _ = 2 * ‖x - y‖ := by ring

variable {A : Type u} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
variable {G H : CountableDiscreteGroup.{u}}
variable [MeasurableSpace (DiscreteCharacterSpace A)]
  [BorelSpace (DiscreteCharacterSpace A)]
variable {W : Type u} [NormedAddCommGroup W]
  [InnerProductSpace ℂ W] [CompleteSpace W]

omit [MeasurableSpace (DiscreteCharacterSpace A)] [BorelSpace (DiscreteCharacterSpace A)]
  in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem jointFunctionalCalculusOperator_positive_contraction
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G W)
    (f : C_c(DiscreteCharacterSpace A, ℝ))
    (hf : ∀ χ : DiscreteCharacterSpace A, 0 ≤ f χ ∧ f χ ≤ 1) :
    ‖jointFunctionalCalculusOperator E π
      (characterRealComplexification f)‖ ≤ 1 := by
  have hnorm : ‖characterRealComplexification f‖ ≤ 1 := by
    apply (ContinuousMap.norm_le _ (by positivity)).2
    intro χ
    rw [characterRealComplexification_apply, Complex.norm_real,
      Real.norm_of_nonneg (hf χ).1]
    exact (hf χ).2
  exact (NonUnitalStarAlgHom.norm_apply_le
    (jointFunctionalCalculusOperator E π)
    (characterRealComplexification f)).trans hnorm

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem abs_jointScalarMeasure_measureReal_sub_le
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G W)
    (x y : W) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    {s : Set (DiscreteCharacterSpace A)} (hs : MeasurableSet s) :
    |((jointPositiveSpectralFunctional E π).measure x).real s -
      ((jointPositiveSpectralFunctional E π).measure y).real s| ≤
        2 * ‖x - y‖ := by
  let Φ := jointPositiveSpectralFunctional E π
  apply abs_regular_measureReal_sub_le_of_testFunctions
    (Φ.measure x) (Φ.measure y) (2 * ‖x - y‖) (by positivity)
  · intro f hf
    rw [Φ.integral_measure x f, Φ.integral_measure y f]
    change
      |(inner ℂ x
          ((jointFunctionalCalculusOperator E π
            (characterRealComplexification f)) x)).re -
        (inner ℂ y
          ((jointFunctionalCalculusOperator E π
            (characterRealComplexification f)) y)).re| ≤ _
    exact bounded_vector_state_lipschitz
      (jointFunctionalCalculusOperator E π
        (characterRealComplexification f)) x y
      (jointFunctionalCalculusOperator_positive_contraction E π f hf) hx hy
  · exact hs

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem abs_jointScalarMeasure_map_measureReal_sub_le
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G W)
    (x : W) (hx : ‖x‖ = 1) (h : H)
    {s : Set (DiscreteCharacterSpace A)} (hs : MeasurableSet s) :
    |(((jointPositiveSpectralFunctional E π).measure x).map
          (dualCharacterAction E.action h)).real s -
        ((jointPositiveSpectralFunctional E π).measure x).real s| ≤
      2 * ‖(π (E.splitting h) : W →L[ℂ] W) x - x‖ := by
  change
    |((RealRMK.rieszMeasure
          ((jointPositiveSpectralFunctional E π).functional x)).map
          (dualCharacterAction E.action h)).real s -
        (RealRMK.rieszMeasure
          ((jointPositiveSpectralFunctional E π).functional x)).real s| ≤ _
  rw [(jointPositiveSpectralFunctional E π).covariance h x]
  exact abs_jointScalarMeasure_measureReal_sub_le E π
    ((π (E.splitting h) : W →L[ℂ] W) x) x
    ((Unitary.norm_map (π (E.splitting h)) x).trans hx) hx hs

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem trivialCharacterProjection_ne_zero_of_joint_atom_pos
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G W)
    (x : W) (hxnorm : ‖x‖ = 1)
    (hx : 0 < spectralTrivialAtom
      ((jointPositiveSpectralFunctional E π).probabilityMeasure x hxnorm)) :
    trivialCharacterProjection E π x ≠ 0 := by
  intro hprojection
  let Φ := jointPositiveSpectralFunctional E π
  change 0 < (Φ.measure x).real {1} at hx
  let ε : ℝ := min 1 ((Φ.measure x).real {1})
  have hε : 0 < ε := lt_min (by norm_num) hx
  obtain ⟨s, w, hw, hsmall⟩ :=
    kernelOrbitAffineApproximation E π x hprojection ε hε
  have hbound := Φ.trivial_atom_le_kernel_orbit_norm_sq
    x s (fun a : A ↦ a) w hw
  let z : W := ∑ a ∈ s, w a •
    ((π (E.inclusion (Multiplicative.ofAdd a)) : W →L[ℂ] W) x)
  change (Φ.measure x).real {1} ≤ ‖z‖ ^ 2 at hbound
  change ‖z‖ < ε at hsmall
  have hzone : ‖z‖ < 1 := lt_of_lt_of_le hsmall (min_le_left _ _)
  have hzatom : ‖z‖ < (Φ.measure x).real {1} :=
    lt_of_lt_of_le hsmall (min_le_right _ _)
  have hznorm : 0 ≤ ‖z‖ := norm_nonneg _
  linarith [mul_nonneg hznorm (sub_nonneg.mpr (le_of_lt hzone))]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem exists_kernel_fixed_of_joint_atom_pos
    (E : SplitAbelianExtension A G H)
    (π : UnitaryRepresentation G W)
    (x : W) (hxnorm : ‖x‖ = 1)
    (hx : 0 < spectralTrivialAtom
      ((jointPositiveSpectralFunctional E π).probabilityMeasure x hxnorm)) :
    ∃ y : W, y ≠ 0 ∧
      ∀ a : A,
        (π (E.inclusion (Multiplicative.ofAdd a)) : W →L[ℂ] W) y = y := by
  refine ⟨trivialCharacterProjection E π x,
    trivialCharacterProjection_ne_zero_of_joint_atom_pos
      E π x hxnorm hx, ?_⟩
  exact trivialCharacterProjection_kernel_fixed E π x

end

section

open ConnesRigidity MeasureTheory

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def integerElementaryRankTwoGroup : CountableDiscreteGroup where
  Carrier := ElementaryRankTwoSemidirect ℤ
  group := inferInstance
  countable := inferInstance

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def integerElementaryRankTwoActingGroup : CountableDiscreteGroup where
  Carrier := elementaryRankTwo ℤ
  group := inferInstance
  countable := inferInstance

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private abbrev integerElementaryRankTwoTranslationSubgroup :
    Subgroup integerElementaryRankTwoGroup :=
  elementaryRankTwoTranslationSubgroup ℤ

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private abbrev integerElementaryRankTwoInl :
    Multiplicative (Fin 2 → ℤ) →* integerElementaryRankTwoGroup :=
  SemidirectProduct.inl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private abbrev integerElementaryRankTwoInr :
    integerElementaryRankTwoActingGroup →*
      integerElementaryRankTwoGroup :=
  SemidirectProduct.inr

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private abbrev integerElementaryRankTwoProjection :
    integerElementaryRankTwoGroup →*
      integerElementaryRankTwoActingGroup :=
  SemidirectProduct.rightHom

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def integerElementaryRankTwoSplitAbelianExtension :
    SplitAbelianExtension (Fin 2 → ℤ)
      integerElementaryRankTwoGroup
      integerElementaryRankTwoActingGroup where
  inclusion := integerElementaryRankTwoInl
  quotient := integerElementaryRankTwoProjection
  splitting := integerElementaryRankTwoInr
  quotient_splitting := SemidirectProduct.rightHom_comp_inr
  exact := SemidirectProduct.range_inl_eq_ker_rightHom.symm
  action := (MulAutMultiplicative (Fin 2 → ℤ)).toMonoidHom.comp
    (elementaryRankTwoAction ℤ)
  conjugation g v := by
    change
      (⟨1, (g : elementaryRankTwo ℤ)⟩ : ElementaryRankTwoSemidirect ℤ) *
        (⟨Multiplicative.ofAdd v, 1⟩ : ElementaryRankTwoSemidirect ℤ) *
        (⟨1, (g : elementaryRankTwo ℤ)⟩ : ElementaryRankTwoSemidirect ℤ)⁻¹ =
      (⟨(elementaryRankTwoAction ℤ) g (Multiplicative.ofAdd v), 1⟩ :
        ElementaryRankTwoSemidirect ℤ)
    refine SemidirectProduct.ext ?_ ?_
    · simp
    · change (g : elementaryRankTwo ℤ) * 1 * g⁻¹ = 1
      rw [mul_one, mul_inv_cancel]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem integerElementaryRankTwoSplitAbelianExtension_range :
    integerElementaryRankTwoSplitAbelianExtension.inclusion.range =
      integerElementaryRankTwoTranslationSubgroup := rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def integerTranslationZero : Fin 2 → ℤ :=
  Pi.single 0 1

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def integerTranslationOne : Fin 2 → ℤ :=
  Pi.single 1 1

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def integerUpperShear : integerElementaryRankTwoActingGroup :=
  elementaryRankTwoRoot (show (0 : Fin 2) ≠ 1 by decide) (1 : ℤ)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def integerLowerShear : integerElementaryRankTwoActingGroup :=
  elementaryRankTwoRoot (show (1 : Fin 2) ≠ 0 by decide) (1 : ℤ)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def integerShalomShears : Finset integerElementaryRankTwoActingGroup := by
  classical
  exact {integerUpperShear, integerLowerShear,
    integerUpperShear⁻¹, integerLowerShear⁻¹}

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def integerShalomTranslations : Finset (Fin 2 → ℤ) := by
  classical
  exact {integerTranslationZero, integerTranslationOne}

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def integerShalomTranslation (i : Fin 2) (a : ℤ) :
    integerElementaryRankTwoGroup :=
  integerElementaryRankTwoInl
    (Multiplicative.ofAdd (Pi.single i a : Fin 2 → ℤ))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def integerShalomTranslationGenerators :
    Finset integerElementaryRankTwoGroup := by
  classical
  exact
    {integerShalomTranslation 0 1,
      integerShalomTranslation 0 (-1),
      integerShalomTranslation 1 1,
      integerShalomTranslation 1 (-1)}

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def integerShalomShearGenerators :
    Finset integerElementaryRankTwoGroup := by
  classical
  exact integerShalomShears.image integerElementaryRankTwoInr

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def integerShalomGenerators : Finset integerElementaryRankTwoGroup := by
  classical
  exact integerShalomTranslationGenerators ∪ integerShalomShearGenerators





/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem integerShalomTranslations_in_generators
    {a : Fin 2 → ℤ} (ha : a ∈ integerShalomTranslations) :
    integerElementaryRankTwoInl (Multiplicative.ofAdd a) ∈
      integerShalomGenerators := by
  classical
  simp only [integerShalomTranslations, Finset.mem_insert,
    Finset.mem_singleton] at ha
  rcases ha with rfl | rfl
  · simp only [integerShalomGenerators, integerShalomTranslationGenerators,
      integerShalomTranslation, Fin.isValue, Int.reduceNeg, Finset.insert_union,
      Finset.singleton_union, integerTranslationZero, Finset.mem_insert, true_or]
  · simp only [integerShalomGenerators, integerShalomTranslationGenerators,
      integerShalomTranslation, Fin.isValue, Int.reduceNeg, Finset.insert_union,
      Finset.singleton_union, integerTranslationOne, Finset.mem_insert, true_or, or_true]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem integerShalomShears_in_generators
    {h : integerElementaryRankTwoActingGroup}
    (hh : h ∈ integerShalomShears) :
    integerElementaryRankTwoInr h ∈ integerShalomGenerators := by
  classical
  simp only [integerShalomGenerators, Finset.mem_union,
    integerShalomShearGenerators, Finset.mem_image]
  exact Or.inr ⟨h, hh, rfl⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def ShalomIntegerRelativePair : Prop :=
  IsRelativeKazhdanPair integerElementaryRankTwoGroup
    integerElementaryRankTwoTranslationSubgroup
    integerShalomGenerators
    (shalomPolynomialKazhdanConstant 0)

section IntegerScalarFourier

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
local instance integerDualMeasurableSpace :
    MeasurableSpace (DiscreteCharacterSpace (Fin 2 → ℤ)) :=
  borel _

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
local instance integerDualBorelSpace :
    BorelSpace (DiscreteCharacterSpace (Fin 2 → ℤ)) :=
  ⟨rfl⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def IntegerShalomFourierAtomGap : Prop :=
  ∀ μ : ProbabilityMeasure (DiscreteCharacterSpace (Fin 2 → ℤ)),
    (∀ h ∈ integerShalomShears,
      ∀ s : Set (DiscreteCharacterSpace (Fin 2 → ℤ)),
        MeasurableSet s →
          |((μ : Measure (DiscreteCharacterSpace (Fin 2 → ℤ))).map
              (dualCharacterAction
                integerElementaryRankTwoSplitAbelianExtension.action h)).real s -
            (μ : Measure (DiscreteCharacterSpace (Fin 2 → ℤ))).real s| <
              2 * shalomPolynomialKazhdanConstant 0) →
    (∀ a ∈ integerShalomTranslations,
      spectralDetectionEnergy μ a <
        (shalomPolynomialKazhdanConstant 0) ^ 2) →
      0 < spectralTrivialAtom μ

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem integerShalomRelativeKazhdanPair_of_fourierAtomGap
    (hatom : IntegerShalomFourierAtomGap) :
    ShalomIntegerRelativePair := by
  classical
  refine ⟨shalomPolynomialKazhdanConstant_pos 0, ?_⟩
  intro W _ _ _ π ξ hξ hsmall
  let E := integerElementaryRankTwoSplitAbelianExtension
  let Φ := jointPositiveSpectralFunctional E π
  let μ := Φ.probabilityMeasure ξ hξ
  have hshears :
      ∀ h ∈ integerShalomShears,
        ∀ s : Set (DiscreteCharacterSpace (Fin 2 → ℤ)),
          MeasurableSet s →
            |((μ : Measure (DiscreteCharacterSpace (Fin 2 → ℤ))).map
                (dualCharacterAction E.action h)).real s -
              (μ : Measure (DiscreteCharacterSpace (Fin 2 → ℤ))).real s| <
                2 * shalomPolynomialKazhdanConstant 0 := by
    intro h hh s hs
    have hbound :=
      abs_jointScalarMeasure_map_measureReal_sub_le E π ξ hξ h hs
    have hdisplacement := hsmall (integerElementaryRankTwoInr h)
      (integerShalomShears_in_generators hh)
    change
      |((Φ.measure ξ).map (dualCharacterAction E.action h)).real s -
        (Φ.measure ξ).real s| <
          2 * shalomPolynomialKazhdanConstant 0
    change
      ‖(π (E.splitting h) : W →L[ℂ] W) ξ - ξ‖ <
        shalomPolynomialKazhdanConstant 0 at hdisplacement
    linarith
  have htranslations :
      ∀ a ∈ integerShalomTranslations,
        spectralDetectionEnergy μ a <
          (shalomPolynomialKazhdanConstant 0) ^ 2 := by
    intro a ha
    have hdisplacement :=
      hsmall (integerElementaryRankTwoInl (Multiplicative.ofAdd a))
        (integerShalomTranslations_in_generators ha)
    change
      (∫ χ : DiscreteCharacterSpace (Fin 2 → ℤ),
        ‖((χ (Multiplicative.ofAdd a) : Circle) : ℂ) - 1‖ ^ 2
          ∂(Φ.measure ξ)) <
            (shalomPolynomialKazhdanConstant 0) ^ 2
    rw [Φ.measure_energy ξ a]
    change
      ‖(π (E.inclusion (Multiplicative.ofAdd a)) : W →L[ℂ] W) ξ - ξ‖ <
        shalomPolynomialKazhdanConstant 0 at hdisplacement
    nlinarith [norm_nonneg
      ((π (E.inclusion (Multiplicative.ofAdd a)) : W →L[ℂ] W) ξ - ξ),
      shalomPolynomialKazhdanConstant_pos 0]
  have hpositive : 0 < spectralTrivialAtom μ :=
    hatom μ hshears htranslations
  obtain ⟨η, hη, hfixed⟩ :=
    exists_kernel_fixed_of_joint_atom_pos E π ξ hξ hpositive
  refine ⟨η, hη, ?_⟩
  intro n
  obtain ⟨a, ha⟩ := n.property
  rw [← ha]
  exact hfixed (Multiplicative.toAdd a)

end IntegerScalarFourier

end

section

open Set MeasureTheory

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private abbrev ShalomPuncturedPlane := {p : ℝ × ℝ // p ≠ 0}

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def shalomSectorA : Set (ℝ × ℝ) :=
  {p | p.1 * p.2 ≤ 0 ∧ |p.1| < |p.2|}

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def shalomSectorB : Set (ℝ × ℝ) :=
  {p | p.1 * p.2 < 0 ∧ |p.2| ≤ |p.1|}

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def shalomSectorC : Set (ℝ × ℝ) :=
  {p | 0 ≤ p.1 * p.2 ∧ |p.2| < |p.1|}

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def shalomSectorD : Set (ℝ × ℝ) :=
  {p | 0 < p.1 * p.2 ∧ |p.1| ≤ |p.2|}

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def shalomPuncturedA : Set ShalomPuncturedPlane :=
  Subtype.val ⁻¹' shalomSectorA

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def shalomPuncturedB : Set ShalomPuncturedPlane :=
  Subtype.val ⁻¹' shalomSectorB

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def shalomPuncturedC : Set ShalomPuncturedPlane :=
  Subtype.val ⁻¹' shalomSectorC

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def shalomPuncturedD : Set ShalomPuncturedPlane :=
  Subtype.val ⁻¹' shalomSectorD

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem shalomSectorA_measurable : MeasurableSet shalomSectorA := by
  exact (isClosed_le (continuous_fst.mul continuous_snd)
    continuous_const).measurableSet.inter
    (isOpen_lt continuous_fst.abs continuous_snd.abs).measurableSet

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem shalomSectorB_measurable : MeasurableSet shalomSectorB := by
  exact (isOpen_lt (continuous_fst.mul continuous_snd)
    continuous_const).measurableSet.inter
    (isClosed_le continuous_snd.abs continuous_fst.abs).measurableSet

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem shalomSectorC_measurable : MeasurableSet shalomSectorC := by
  exact (isClosed_le continuous_const
    (continuous_fst.mul continuous_snd)).measurableSet.inter
    (isOpen_lt continuous_snd.abs continuous_fst.abs).measurableSet

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem shalomSectorD_measurable : MeasurableSet shalomSectorD := by
  exact (isOpen_lt continuous_const
    (continuous_fst.mul continuous_snd)).measurableSet.inter
    (isClosed_le continuous_fst.abs continuous_snd.abs).measurableSet

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem shalomPunctured_cover :
    shalomPuncturedA ∪ shalomPuncturedB ∪ shalomPuncturedC ∪
      shalomPuncturedD = Set.univ := by
  ext ⟨⟨x, y⟩, hne⟩
  simp only [Set.mem_union, Set.mem_univ, iff_true, shalomPuncturedA,
    shalomPuncturedB, shalomPuncturedC, shalomPuncturedD, Set.mem_preimage,
    shalomSectorA, shalomSectorB, shalomSectorC, shalomSectorD, Set.mem_ofPred_eq]
  by_cases hneg : x * y < 0
  · by_cases hlt : |x| < |y|
    · exact Or.inl (Or.inl (Or.inl ⟨hneg.le, hlt⟩))
    · exact Or.inl (Or.inl (Or.inr ⟨hneg, le_of_not_gt hlt⟩))
  by_cases hpos : 0 < x * y
  · by_cases hlt : |y| < |x|
    · exact Or.inl (Or.inr ⟨hpos.le, hlt⟩)
    · exact Or.inr ⟨hpos, le_of_not_gt hlt⟩
  have hzero : x * y = 0 := le_antisymm (le_of_not_gt hpos) (le_of_not_gt hneg)
  rcases mul_eq_zero.mp hzero with hx | hy
  · have hyne : y ≠ 0 := by
      intro hy
      apply hne
      exact Prod.ext hx hy
    exact Or.inl (Or.inl (Or.inl
      ⟨by simp only [hx, zero_mul, Std.le_refl], by simp only [hx, abs_zero, abs_pos.mpr hyne]⟩))
  · have hxne : x ≠ 0 := by
      intro hx
      apply hne
      exact Prod.ext hx hy
    exact Or.inl (Or.inr
      ⟨by simp only [hy, mul_zero, Std.le_refl], by simp only [hy, abs_zero, abs_pos.mpr hxne]⟩)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem abs_sub_of_mul_nonpos {x y : ℝ} (h : x * y ≤ 0) :
    |y - x| = |y| + |x| := by
  rcases (mul_nonpos_iff.mp h) with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · rw [abs_of_nonpos hy, abs_of_nonneg hx, abs_of_nonpos (by linarith)]
    linarith
  · rw [abs_of_nonneg hy, abs_of_nonpos hx, abs_of_nonneg (by linarith)]
    linarith

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem abs_add_of_mul_nonneg {x y : ℝ} (h : 0 ≤ x * y) :
    |x + y| = |x| + |y| := by
  rcases (mul_nonneg_iff.mp h) with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · rw [abs_of_nonneg hx, abs_of_nonneg hy, abs_of_nonneg (by linarith)]
  · rw [abs_of_nonpos hx, abs_of_nonpos hy, abs_of_nonpos (by linarith)]
    ring

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem shalomTpos_sector_inclusion :
    (fun p : ℝ × ℝ => (p.1, p.2 - p.1)) '' (shalomSectorA ∪ shalomSectorB) ⊆ shalomSectorA := by
  rintro _ ⟨⟨x, y⟩, hxy, rfl⟩
  have hnonpos : x * y ≤ 0 := by
    rcases hxy with h | h
    · exact h.1
    · exact h.1.le
  have hy : y ≠ 0 := by
    intro hy
    rcases hxy with h | h
    · exact (not_lt_of_ge (abs_nonneg x)) (by simpa only [hy, abs_zero] using h.2)
    · simpa only [hy, mul_zero, lt_self_iff_false] using h.1
  change x * (y - x) ≤ 0 ∧ |x| < |y - x|
  constructor
  · linarith [sq_nonneg x]
  · rw [abs_sub_of_mul_nonpos hnonpos]
    linarith [abs_pos.mpr hy]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem shalomSpos_sector_inclusion :
    (fun p : ℝ × ℝ => (p.1 - p.2, p.2)) '' (shalomSectorA ∪ shalomSectorB) ⊆ shalomSectorB := by
  rintro _ ⟨⟨x, y⟩, hxy, rfl⟩
  have hnonpos : x * y ≤ 0 := by
    rcases hxy with h | h
    · exact h.1
    · exact h.1.le
  have hy : y ≠ 0 := by
    intro hy
    rcases hxy with h | h
    · exact (not_lt_of_ge (abs_nonneg x)) (by simpa only [hy, abs_zero] using h.2)
    · simpa only [hy, mul_zero, lt_self_iff_false] using h.1
  change (x - y) * y < 0 ∧ |y| ≤ |x - y|
  constructor
  · linarith [sq_pos_of_ne_zero hy]
  · rw [abs_sub_comm, abs_sub_of_mul_nonpos hnonpos]
    linarith [abs_nonneg x]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem shalomTneg_sector_inclusion :
    (fun p : ℝ × ℝ => (p.1, p.2 + p.1)) '' (shalomSectorD ∪ shalomSectorC) ⊆ shalomSectorD := by
  rintro _ ⟨⟨x, y⟩, hxy, rfl⟩
  have hnonneg : 0 ≤ x * y := by
    rcases hxy with h | h
    · exact h.1.le
    · exact h.1
  have hx : x ≠ 0 := by
    intro hx
    rcases hxy with h | h
    · simpa only [hx, zero_mul, lt_self_iff_false] using h.1
    · exact (not_lt_of_ge (abs_nonneg y)) (by simpa only [hx, abs_zero] using h.2)
  change 0 < x * (y + x) ∧ |x| ≤ |y + x|
  constructor
  · linarith [sq_pos_of_ne_zero hx]
  · rw [add_comm y x, abs_add_of_mul_nonneg hnonneg]
    linarith [abs_nonneg y]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem shalomSneg_sector_inclusion :
    (fun p : ℝ × ℝ => (p.1 + p.2, p.2)) '' (shalomSectorD ∪ shalomSectorC) ⊆ shalomSectorC := by
  rintro _ ⟨⟨x, y⟩, hxy, rfl⟩
  have hnonneg : 0 ≤ x * y := by
    rcases hxy with h | h
    · exact h.1.le
    · exact h.1
  have hx : x ≠ 0 := by
    intro hx
    rcases hxy with h | h
    · simpa only [hx, zero_mul, lt_self_iff_false] using h.1
    · exact (not_lt_of_ge (abs_nonneg y)) (by simpa only [hx, abs_zero] using h.2)
  change 0 ≤ (x + y) * y ∧ |y| < |x + y|
  constructor
  · linarith [sq_nonneg y]
  · rw [abs_add_of_mul_nonneg hnonneg]
    linarith [abs_pos.mpr hx]

end

section

open ConnesRigidity MeasureTheory Set

universe u

variable {A : Type u} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
variable {H : CountableDiscreteGroup.{u}}
variable [MeasurableSpace (DiscreteCharacterSpace A)]
  [BorelSpace (DiscreteCharacterSpace A)]

omit [MeasurableSpace (DiscreteCharacterSpace A)] [BorelSpace (DiscreteCharacterSpace A)]
  in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem spectralArgCoordinates_dualCharacterAction
    (action : H →* Multiplicative (AddAut A)) (h : H)
    (a b : A) (χ : DiscreteCharacterSpace A) :
    spectralArgCoordinates a b (dualCharacterAction action h χ) =
      (Complex.arg
        (((χ (Multiplicative.ofAdd
          ((Multiplicative.toAdd (action h⁻¹)) a)) : Circle) : ℂ)),
       Complex.arg
        (((χ (Multiplicative.ofAdd
          ((Multiplicative.toAdd (action h⁻¹)) b)) : Circle) : ℂ))) := rfl

omit [MeasurableSpace (DiscreteCharacterSpace A)] [BorelSpace (DiscreteCharacterSpace A)]
  in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem spectralArgCoordinates_dualCharacterAction_tpos
    (action : H →* Multiplicative (AddAut A)) (h : H)
    (a b : A)
    (ha : (Multiplicative.toAdd (action h⁻¹)) a = a)
    (hb : (Multiplicative.toAdd (action h⁻¹)) b = b - a)
    (χ : DiscreteCharacterSpace A)
    (hχ : χ ∈ spectralTorusWindow a b) :
    spectralArgCoordinates a b (dualCharacterAction action h χ) =
      ((spectralArgCoordinates a b χ).1,
        (spectralArgCoordinates a b χ).2 -
          (spectralArgCoordinates a b χ).1) := by
  calc
    spectralArgCoordinates a b (dualCharacterAction action h χ) =
        spectralArgCoordinates a (b - a) χ := by
      rw [spectralArgCoordinates_dualCharacterAction, ha, hb]
      rfl
    _ = ((spectralArgCoordinates a b χ).1,
        (spectralArgCoordinates a b χ).2 -
          (spectralArgCoordinates a b χ).1) := by
      exact spectralArgCoordinates_tpos a b χ hχ

omit [MeasurableSpace (DiscreteCharacterSpace A)] [BorelSpace (DiscreteCharacterSpace A)]
  in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem spectralArgCoordinates_dualCharacterAction_spos
    (action : H →* Multiplicative (AddAut A)) (h : H)
    (a b : A)
    (ha : (Multiplicative.toAdd (action h⁻¹)) a = a - b)
    (hb : (Multiplicative.toAdd (action h⁻¹)) b = b)
    (χ : DiscreteCharacterSpace A)
    (hχ : χ ∈ spectralTorusWindow a b) :
    spectralArgCoordinates a b (dualCharacterAction action h χ) =
      ((spectralArgCoordinates a b χ).1 -
          (spectralArgCoordinates a b χ).2,
        (spectralArgCoordinates a b χ).2) := by
  calc
    spectralArgCoordinates a b (dualCharacterAction action h χ) =
        spectralArgCoordinates (a - b) b χ := by
      rw [spectralArgCoordinates_dualCharacterAction, ha, hb]
      rfl
    _ = ((spectralArgCoordinates a b χ).1 -
          (spectralArgCoordinates a b χ).2,
        (spectralArgCoordinates a b χ).2) := by
      exact spectralArgCoordinates_spos a b χ hχ

omit [MeasurableSpace (DiscreteCharacterSpace A)] [BorelSpace (DiscreteCharacterSpace A)]
  in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem spectralArgCoordinates_dualCharacterAction_tneg
    (action : H →* Multiplicative (AddAut A)) (h : H)
    (a b : A)
    (ha : (Multiplicative.toAdd (action h⁻¹)) a = a)
    (hb : (Multiplicative.toAdd (action h⁻¹)) b = b + a)
    (χ : DiscreteCharacterSpace A)
    (hχ : χ ∈ spectralTorusWindow a b) :
    spectralArgCoordinates a b (dualCharacterAction action h χ) =
      ((spectralArgCoordinates a b χ).1,
        (spectralArgCoordinates a b χ).2 +
          (spectralArgCoordinates a b χ).1) := by
  calc
    spectralArgCoordinates a b (dualCharacterAction action h χ) =
        spectralArgCoordinates a (b + a) χ := by
      rw [spectralArgCoordinates_dualCharacterAction, ha, hb]
      rfl
    _ = ((spectralArgCoordinates a b χ).1,
        (spectralArgCoordinates a b χ).2 +
          (spectralArgCoordinates a b χ).1) := by
      exact spectralArgCoordinates_tneg a b χ hχ

omit [MeasurableSpace (DiscreteCharacterSpace A)] [BorelSpace (DiscreteCharacterSpace A)]
  in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem spectralArgCoordinates_dualCharacterAction_sneg
    (action : H →* Multiplicative (AddAut A)) (h : H)
    (a b : A)
    (ha : (Multiplicative.toAdd (action h⁻¹)) a = a + b)
    (hb : (Multiplicative.toAdd (action h⁻¹)) b = b)
    (χ : DiscreteCharacterSpace A)
    (hχ : χ ∈ spectralTorusWindow a b) :
    spectralArgCoordinates a b (dualCharacterAction action h χ) =
      ((spectralArgCoordinates a b χ).1 +
          (spectralArgCoordinates a b χ).2,
        (spectralArgCoordinates a b χ).2) := by
  calc
    spectralArgCoordinates a b (dualCharacterAction action h χ) =
        spectralArgCoordinates (a + b) b χ := by
      rw [spectralArgCoordinates_dualCharacterAction, ha, hb]
      rfl
    _ = ((spectralArgCoordinates a b χ).1 +
          (spectralArgCoordinates a b χ).2,
        (spectralArgCoordinates a b χ).2) := by
      exact spectralArgCoordinates_sneg a b χ hχ

end

section

open ConnesRigidity Matrix MeasureTheory





/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem integerUpperShear_inv_action_zero :
    (Multiplicative.toAdd
      (integerElementaryRankTwoSplitAbelianExtension.action
        integerUpperShear⁻¹)) integerTranslationZero =
      integerTranslationZero := by
  change
    (Matrix.SpecialLinearGroup.transvection
      (show (0 : Fin 2) ≠ 1 by decide) (1 : ℤ))⁻¹ •
      (Pi.single (0 : Fin 2) 1 : Fin 2 → ℤ) =
      Pi.single (0 : Fin 2) 1
  rw [Matrix.SpecialLinearGroup.transvection_inv,
    Matrix.SpecialLinearGroup.transvection_smul_single_fst]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem integerUpperShear_inv_action_one :
    (Multiplicative.toAdd
      (integerElementaryRankTwoSplitAbelianExtension.action
        integerUpperShear⁻¹)) integerTranslationOne =
      integerTranslationOne - integerTranslationZero := by
  change
    (Matrix.SpecialLinearGroup.transvection
      (show (0 : Fin 2) ≠ 1 by decide) (1 : ℤ))⁻¹ •
      (Pi.single (1 : Fin 2) 1 : Fin 2 → ℤ) =
      Pi.single (1 : Fin 2) 1 - Pi.single (0 : Fin 2) 1
  rw [Matrix.SpecialLinearGroup.transvection_inv,
    Matrix.SpecialLinearGroup.transvection_smul_single_snd]
  simp only [Fin.isValue, Int.reduceNeg, neg_smul, one_smul, sub_eq_add_neg]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem integerLowerShear_inv_action_zero :
    (Multiplicative.toAdd
      (integerElementaryRankTwoSplitAbelianExtension.action
        integerLowerShear⁻¹)) integerTranslationZero =
      integerTranslationZero - integerTranslationOne := by
  change
    (Matrix.SpecialLinearGroup.transvection
      (show (1 : Fin 2) ≠ 0 by decide) (1 : ℤ))⁻¹ •
      (Pi.single (0 : Fin 2) 1 : Fin 2 → ℤ) =
      Pi.single (0 : Fin 2) 1 - Pi.single (1 : Fin 2) 1
  rw [Matrix.SpecialLinearGroup.transvection_inv,
    Matrix.SpecialLinearGroup.transvection_smul_single_snd]
  simp only [Fin.isValue, Int.reduceNeg, neg_smul, one_smul, sub_eq_add_neg]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem integerLowerShear_inv_action_one :
    (Multiplicative.toAdd
      (integerElementaryRankTwoSplitAbelianExtension.action
        integerLowerShear⁻¹)) integerTranslationOne =
      integerTranslationOne := by
  change
    (Matrix.SpecialLinearGroup.transvection
      (show (1 : Fin 2) ≠ 0 by decide) (1 : ℤ))⁻¹ •
      (Pi.single (1 : Fin 2) 1 : Fin 2 → ℤ) =
      Pi.single (1 : Fin 2) 1
  rw [Matrix.SpecialLinearGroup.transvection_inv,
    Matrix.SpecialLinearGroup.transvection_smul_single_fst]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem integerUpperShear_action_zero :
    (Multiplicative.toAdd
      (integerElementaryRankTwoSplitAbelianExtension.action
        integerUpperShear)) integerTranslationZero =
      integerTranslationZero := by
  change
    (Matrix.SpecialLinearGroup.transvection
      (show (0 : Fin 2) ≠ 1 by decide) (1 : ℤ)) •
      (Pi.single (0 : Fin 2) 1 : Fin 2 → ℤ) =
      Pi.single (0 : Fin 2) 1
  rw [Matrix.SpecialLinearGroup.transvection_smul_single_fst]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem integerUpperShear_action_one :
    (Multiplicative.toAdd
      (integerElementaryRankTwoSplitAbelianExtension.action
        integerUpperShear)) integerTranslationOne =
      integerTranslationOne + integerTranslationZero := by
  change
    (Matrix.SpecialLinearGroup.transvection
      (show (0 : Fin 2) ≠ 1 by decide) (1 : ℤ)) •
      (Pi.single (1 : Fin 2) 1 : Fin 2 → ℤ) =
      Pi.single (1 : Fin 2) 1 + Pi.single (0 : Fin 2) 1
  rw [Matrix.SpecialLinearGroup.transvection_smul_single_snd]
  simp only [Fin.isValue, one_smul]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem integerLowerShear_action_zero :
    (Multiplicative.toAdd
      (integerElementaryRankTwoSplitAbelianExtension.action
        integerLowerShear)) integerTranslationZero =
      integerTranslationZero + integerTranslationOne := by
  change
    (Matrix.SpecialLinearGroup.transvection
      (show (1 : Fin 2) ≠ 0 by decide) (1 : ℤ)) •
      (Pi.single (0 : Fin 2) 1 : Fin 2 → ℤ) =
      Pi.single (0 : Fin 2) 1 + Pi.single (1 : Fin 2) 1
  rw [Matrix.SpecialLinearGroup.transvection_smul_single_snd]
  simp only [Fin.isValue, one_smul]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem integerLowerShear_action_one :
    (Multiplicative.toAdd
      (integerElementaryRankTwoSplitAbelianExtension.action
        integerLowerShear)) integerTranslationOne =
      integerTranslationOne := by
  change
    (Matrix.SpecialLinearGroup.transvection
      (show (1 : Fin 2) ≠ 0 by decide) (1 : ℤ)) •
      (Pi.single (1 : Fin 2) 1 : Fin 2 → ℤ) =
      Pi.single (1 : Fin 2) 1
  rw [Matrix.SpecialLinearGroup.transvection_smul_single_fst]

end

section

open ConnesRigidity MeasureTheory Set

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem shalom_conditioned_image_variation_lt_one_fourth
    (μ : ProbabilityMeasure Ω) {U : Set Ω}
    (hU : 0 < (μ : Measure Ω).real U)
    (hUmeas : MeasurableSet U)
    {ε : ℝ} (hε : 0 ≤ ε) (hsmall : ε ≤ (1 / 10 : ℝ))
    (hdiscard : (μ : Measure Ω).real Uᶜ ≤ ε ^ 2)
    (f : Ω ≃ᵐ Ω) (s : Set Ω)
    (hvariation : |(μ : Measure Ω).real (f.symm ⁻¹' s) -
      (μ : Measure Ω).real s| ≤ 2 * ε) :
    |(conditionedProbability μ U hU : Measure Ω).real (f '' s) -
      (conditionedProbability μ U hU : Measure Ω).real s| <
        (1 / 4 : ℝ) := by
  have himage : f '' s = f.symm ⁻¹' s := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa only [mem_preimage, MeasurableEquiv.symm_apply_apply] using hy
    · intro hx
      exact ⟨f.symm x, hx, f.apply_symm_apply x⟩
  rw [himage]
  exact shalom_conditioned_variation_lt_one_fourth μ hU hUmeas
    hε hsmall hdiscard (f.symm ⁻¹' s) s hvariation

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem shalom_conditioned_image_variation_of_map_lt_one_fourth
    (μ : ProbabilityMeasure Ω) {U : Set Ω}
    (hU : 0 < (μ : Measure Ω).real U)
    (hUmeas : MeasurableSet U)
    {ε : ℝ} (hε : 0 ≤ ε) (hsmall : ε ≤ (1 / 10 : ℝ))
    (hdiscard : (μ : Measure Ω).real Uᶜ ≤ ε ^ 2)
    (f : Ω ≃ᵐ Ω) (s : Set Ω) (hs : MeasurableSet s)
    (hvariation : |((μ : Measure Ω).map f.symm).real s -
      (μ : Measure Ω).real s| ≤ 2 * ε) :
    |(conditionedProbability μ U hU : Measure Ω).real (f '' s) -
      (conditionedProbability μ U hU : Measure Ω).real s| <
        (1 / 4 : ℝ) := by
  apply shalom_conditioned_image_variation_lt_one_fourth μ hU
    hUmeas hε hsmall hdiscard f s
  simpa only [ProbabilityMeasure.measureReal_eq_coe_coeFn,
    map_measureReal_apply f.symm.measurable hs] using hvariation

universe u

variable {A : Type u} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
variable [MeasurableSpace (DiscreteCharacterSpace A)]
  [BorelSpace (DiscreteCharacterSpace A)]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem spectralTorusWindow_conditioned_image_variation_lt_one_fourth
    (μ : ProbabilityMeasure (DiscreteCharacterSpace A)) (a b : A)
    {ε : ℝ} (hε : 0 ≤ ε) (hsmall : ε ≤ (1 / 10 : ℝ))
    (ha : spectralDetectionEnergy μ a ≤ ε ^ 2)
    (hb : spectralDetectionEnergy μ b ≤ ε ^ 2)
    (f : DiscreteCharacterSpace A ≃ᵐ DiscreteCharacterSpace A)
    (s : Set (DiscreteCharacterSpace A)) (hs : MeasurableSet s)
    (hvariation :
      |((μ : Measure (DiscreteCharacterSpace A)).map f.symm).real s -
        (μ : Measure (DiscreteCharacterSpace A)).real s| ≤ 2 * ε) :
    let hU := spectralTorusWindow_measureReal_pos μ a b hsmall hε ha hb
    |(conditionedProbability μ (spectralTorusWindow a b) hU :
        Measure (DiscreteCharacterSpace A)).real (f '' s) -
      (conditionedProbability μ (spectralTorusWindow a b) hU :
        Measure (DiscreteCharacterSpace A)).real s| <
          (1 / 4 : ℝ) := by
  dsimp
  exact shalom_conditioned_image_variation_of_map_lt_one_fourth μ
    (spectralTorusWindow_measureReal_pos μ a b hsmall hε ha hb)
    (spectralTorusWindow_measurable a b) hε hsmall
    (spectralTorusWindow_compl_measureReal_le_sq μ a b ha hb)
    f s hs hvariation

end

section

open MeasureTheory Set

section

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem shalom_measureReal_inter_support_eq
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {support : Set Ω} (hsupport : MeasurableSet support)
    (hmass : μ.real support = 1) (s : Set Ω) :
    μ.real (s ∩ support) = μ.real s := by
  have hcompl : μ.real supportᶜ = 0 := by
    have htotal := measureReal_add_measureReal_compl
      (μ := μ) hsupport
    rw [probReal_univ, hmass] at htotal
    linarith
  have hdiff : μ.real (s \ support) = 0 := by
    have hle := measureReal_mono (μ := μ)
      (Set.sdiff_subset_compl s support)
    have hnonneg := measureReal_nonneg (μ := μ) (s := s \ support)
    linarith
  have hdecomp := measureReal_inter_add_sdiff
    (μ := μ) (s := s) hsupport
  linarith

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem shalom_three_sector_supported_probability_gap
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (support A B C U V W : Set Ω)
    (hsupport : MeasurableSet support)
    (hmass : μ.real support = 1)
    (_hA : MeasurableSet A) (hB : MeasurableSet B)
    (hC : MeasurableSet C)
    (hAB : Disjoint A B) (hAC : Disjoint A C)
    (hBC : Disjoint B C)
    (hcover : A ∪ B ∪ C = support)
    (hU : U ∩ support ⊆ C)
    (hV : V ∩ support ⊆ A)
    (hW : W ∩ support ⊆ B) :
    (1 / 5 : ℝ) ≤ |μ.real U - μ.real (A ∪ B)| ∨
      (1 / 5 : ℝ) ≤ |μ.real V - μ.real (C ∪ B)| ∨
      (1 / 5 : ℝ) ≤ |μ.real W - μ.real A| := by
  have hAB_C : Disjoint (A ∪ B) C :=
    disjoint_union_left.mpr ⟨hAC, hBC⟩
  have hsector_mass : μ.real A + μ.real B + μ.real C = 1 := by
    calc
      μ.real A + μ.real B + μ.real C = μ.real (A ∪ B ∪ C) := by
        rw [measureReal_union hAB_C hC, measureReal_union hAB hB]
      _ = 1 := by rw [hcover, hmass]
  have hABmass : μ.real (A ∪ B) = μ.real A + μ.real B :=
    measureReal_union hAB hB
  have hCBmass : μ.real (C ∪ B) = μ.real C + μ.real B :=
    measureReal_union hBC.symm hB
  have hUmass : μ.real U ≤ μ.real C := by
    rw [← shalom_measureReal_inter_support_eq μ hsupport hmass U]
    exact measureReal_mono hU
  have hVmass : μ.real V ≤ μ.real A := by
    rw [← shalom_measureReal_inter_support_eq μ hsupport hmass V]
    exact measureReal_mono hV
  have hWmass : μ.real W ≤ μ.real B := by
    rw [← shalom_measureReal_inter_support_eq μ hsupport hmass W]
    exact measureReal_mono hW
  rw [hABmass, hCBmass]
  exact shalom_three_sector_mass_gap
    (μ.real A) (μ.real B) (μ.real C)
    (μ.real U) (μ.real V) (μ.real W)
    hsector_mass hUmass hVmass hWmass

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem shalom_three_sector_supported_action_gap
    {Ω G : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (act : G → Ω → Ω) (t s n : G)
    (support A B C : Set Ω)
    (hsupport : MeasurableSet support)
    (hmass : μ.real support = 1)
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hC : MeasurableSet C)
    (hAB : Disjoint A B) (hAC : Disjoint A C)
    (hBC : Disjoint B C)
    (hcover : A ∪ B ∪ C = support)
    (ht : (act t '' (A ∪ B)) ∩ support ⊆ C)
    (hs : (act s '' (C ∪ B)) ∩ support ⊆ A)
    (hn : (act n '' A) ∩ support ⊆ B) :
    ∃ g ∈ ({t, s, n} : Set G),
      ∃ U : Set Ω, MeasurableSet U ∧
        (1 / 5 : ℝ) ≤ |μ.real (act g '' U) - μ.real U| := by
  rcases shalom_three_sector_supported_probability_gap μ
      support A B C
      (act t '' (A ∪ B))
      (act s '' (C ∪ B))
      (act n '' A)
      hsupport hmass hA hB hC hAB hAC hBC hcover ht hs hn
      with h | h | h
  · exact ⟨t, by simp only [mem_insert_iff, mem_singleton_iff, true_or], A ∪ B, hA.union hB, h⟩
  · exact ⟨s, by simp only [mem_insert_iff, mem_singleton_iff, true_or,
                   or_true], C ∪ B, hC.union hB, h⟩
  · exact ⟨n, by simp only [mem_insert_iff, mem_singleton_iff, or_true], A, hA, h⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem shalom_four_sector_supported_probability_gap
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (support A B C D U V W Z : Set Ω)
    (hsupport : MeasurableSet support)
    (hmass : μ.real support = 1)
    (_hA : MeasurableSet A) (hB : MeasurableSet B)
    (hC : MeasurableSet C) (hD : MeasurableSet D)
    (hAB : Disjoint A B) (hAC : Disjoint A C)
    (hAD : Disjoint A D) (hBC : Disjoint B C)
    (hBD : Disjoint B D) (hCD : Disjoint C D)
    (hcover : A ∪ B ∪ C ∪ D = support)
    (hU : U ∩ support ⊆ A) (hV : V ∩ support ⊆ B)
    (hW : W ∩ support ⊆ D) (hZ : Z ∩ support ⊆ C) :
    (1 / 4 : ℝ) ≤ |μ.real U - μ.real (A ∪ B)| ∨
      (1 / 4 : ℝ) ≤ |μ.real V - μ.real (A ∪ B)| ∨
      (1 / 4 : ℝ) ≤ |μ.real W - μ.real (D ∪ C)| ∨
      (1 / 4 : ℝ) ≤ |μ.real Z - μ.real (D ∪ C)| := by
  have hAB_C : Disjoint (A ∪ B) C :=
    disjoint_union_left.mpr ⟨hAC, hBC⟩
  have hABC_D : Disjoint (A ∪ B ∪ C) D :=
    disjoint_union_left.mpr
      ⟨disjoint_union_left.mpr ⟨hAD, hBD⟩, hCD⟩
  have hsector_mass :
      μ.real A + μ.real B + μ.real C + μ.real D = 1 := by
    calc
      μ.real A + μ.real B + μ.real C + μ.real D =
          μ.real (A ∪ B ∪ C ∪ D) := by
            rw [measureReal_union hABC_D hD,
              measureReal_union hAB_C hC,
              measureReal_union hAB hB]
      _ = 1 := by rw [hcover, hmass]
  have hABmass : μ.real (A ∪ B) = μ.real A + μ.real B :=
    measureReal_union hAB hB
  have hDCmass : μ.real (D ∪ C) = μ.real D + μ.real C :=
    measureReal_union hCD.symm hC
  have hUmass : μ.real U ≤ μ.real A := by
    rw [← shalom_measureReal_inter_support_eq μ hsupport hmass U]
    exact measureReal_mono hU
  have hVmass : μ.real V ≤ μ.real B := by
    rw [← shalom_measureReal_inter_support_eq μ hsupport hmass V]
    exact measureReal_mono hV
  have hWmass : μ.real W ≤ μ.real D := by
    rw [← shalom_measureReal_inter_support_eq μ hsupport hmass W]
    exact measureReal_mono hW
  have hZmass : μ.real Z ≤ μ.real C := by
    rw [← shalom_measureReal_inter_support_eq μ hsupport hmass Z]
    exact measureReal_mono hZ
  rw [hABmass, hDCmass]
  exact shalom_four_sector_mass_gap
    (μ.real A) (μ.real B) (μ.real C) (μ.real D)
    (μ.real U) (μ.real V) (μ.real W) (μ.real Z)
    hsector_mass hUmass hVmass hWmass hZmass

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem shalom_four_sector_supported_action_gap
    {Ω G : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (act : G → Ω → Ω) (tpos spos tneg sneg : G)
    (support A B C D : Set Ω)
    (hsupport : MeasurableSet support)
    (hmass : μ.real support = 1)
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hC : MeasurableSet C) (hD : MeasurableSet D)
    (hAB : Disjoint A B) (hAC : Disjoint A C)
    (hAD : Disjoint A D) (hBC : Disjoint B C)
    (hBD : Disjoint B D) (hCD : Disjoint C D)
    (hcover : A ∪ B ∪ C ∪ D = support)
    (htpos : (act tpos '' (A ∪ B)) ∩ support ⊆ A)
    (hspos : (act spos '' (A ∪ B)) ∩ support ⊆ B)
    (htneg : (act tneg '' (D ∪ C)) ∩ support ⊆ D)
    (hsneg : (act sneg '' (D ∪ C)) ∩ support ⊆ C) :
    ∃ g ∈ ({tpos, spos, tneg, sneg} : Set G),
      ∃ U : Set Ω, MeasurableSet U ∧
        (1 / 4 : ℝ) ≤ |μ.real (act g '' U) - μ.real U| := by
  rcases shalom_four_sector_supported_probability_gap μ
      support A B C D
      (act tpos '' (A ∪ B))
      (act spos '' (A ∪ B))
      (act tneg '' (D ∪ C))
      (act sneg '' (D ∪ C))
      hsupport hmass hA hB hC hD
      hAB hAC hAD hBC hBD hCD hcover
      htpos hspos htneg hsneg with h | h | h | h
  · exact ⟨tpos, by simp only [mem_insert_iff, mem_singleton_iff, true_or], A ∪ B, hA.union hB, h⟩
  · exact ⟨spos, by simp only [mem_insert_iff, mem_singleton_iff, true_or,
                      or_true], A ∪ B, hA.union hB, h⟩
  · exact ⟨tneg, by simp only [mem_insert_iff, mem_singleton_iff, true_or,
                      or_true], D ∪ C, hD.union hC, h⟩
  · exact ⟨sneg, by simp only [mem_insert_iff, mem_singleton_iff, or_true], D ∪ C, hD.union hC, h⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem shalom_punctured_support_measureReal_eq_one
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {support : Set Ω}
    (hmass : μ.real support = 1)
    (origin : Ω) (horigin : MeasurableSet ({origin} : Set Ω))
    (hzero : μ.real ({origin} : Set Ω) = 0) :
    μ.real (support \ {origin}) = 1 := by
  have hnull : μ.real (support ∩ {origin}) = 0 := by
    exact measureReal_mono_null (Set.inter_subset_right :
      support ∩ {origin} ⊆ ({origin} : Set Ω)) hzero
  have hinter := measureReal_inter_add_sdiff
    (μ := μ) (s := support) horigin
  rw [hnull, hmass] at hinter
  simpa only [zero_add] using hinter

end

end

section

open Set MeasureTheory































universe u

variable {A : Type u} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
variable [MeasurableSpace (DiscreteCharacterSpace A)]
  [BorelSpace (DiscreteCharacterSpace A)]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def shalomSpectralSectorA (a b : A) : Set (DiscreteCharacterSpace A) :=
  spectralTorusWindow a b ∩ spectralArgCoordinates a b ⁻¹' shalomSectorA

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def shalomSpectralSectorB (a b : A) : Set (DiscreteCharacterSpace A) :=
  spectralTorusWindow a b ∩ spectralArgCoordinates a b ⁻¹' shalomSectorB

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def shalomSpectralSectorC (a b : A) : Set (DiscreteCharacterSpace A) :=
  spectralTorusWindow a b ∩ spectralArgCoordinates a b ⁻¹' shalomSectorC

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def shalomSpectralSectorD (a b : A) : Set (DiscreteCharacterSpace A) :=
  spectralTorusWindow a b ∩ spectralArgCoordinates a b ⁻¹' shalomSectorD

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def shalomSpectralPuncturedWindow (a b : A) : Set (DiscreteCharacterSpace A) :=
  spectralTorusWindow a b \ spectralArgCoordinates a b ⁻¹' {(0, 0)}

omit [DiscreteTopology A] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem shalomSpectralSectorA_measurable (a b : A) :
    MeasurableSet (shalomSpectralSectorA a b) :=
  (spectralTorusWindow_measurable a b).inter
    (shalomSectorA_measurable.preimage (measurable_spectralArgCoordinates a b))

omit [DiscreteTopology A] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem shalomSpectralSectorB_measurable (a b : A) :
    MeasurableSet (shalomSpectralSectorB a b) :=
  (spectralTorusWindow_measurable a b).inter
    (shalomSectorB_measurable.preimage (measurable_spectralArgCoordinates a b))

omit [DiscreteTopology A] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem shalomSpectralSectorC_measurable (a b : A) :
    MeasurableSet (shalomSpectralSectorC a b) :=
  (spectralTorusWindow_measurable a b).inter
    (shalomSectorC_measurable.preimage (measurable_spectralArgCoordinates a b))

omit [DiscreteTopology A] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem shalomSpectralSectorD_measurable (a b : A) :
    MeasurableSet (shalomSpectralSectorD a b) :=
  (spectralTorusWindow_measurable a b).inter
    (shalomSectorD_measurable.preimage (measurable_spectralArgCoordinates a b))

omit [DiscreteTopology A] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem shalomSpectralPuncturedWindow_measurable (a b : A) :
    MeasurableSet (shalomSpectralPuncturedWindow a b) :=
  (spectralTorusWindow_measurable a b).diff
    ((measurable_spectralArgCoordinates a b)
      (measurableSet_singleton (0, 0)))

omit [DiscreteTopology A] [MeasurableSpace (DiscreteCharacterSpace A)]
  [BorelSpace (DiscreteCharacterSpace A)] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem shalomSpectralSectorA_B_disjoint (a b : A) :
    Disjoint (shalomSpectralSectorA a b) (shalomSpectralSectorB a b) := by
  rw [Set.disjoint_left]
  intro χ hA hB
  exact not_lt_of_ge hB.2.2 hA.2.2

omit [DiscreteTopology A] [MeasurableSpace (DiscreteCharacterSpace A)]
  [BorelSpace (DiscreteCharacterSpace A)] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem shalomSpectralSectorA_C_disjoint (a b : A) :
    Disjoint (shalomSpectralSectorA a b) (shalomSpectralSectorC a b) := by
  rw [Set.disjoint_left]
  intro χ hA hC
  exact not_lt_of_ge hA.2.2.le hC.2.2

omit [DiscreteTopology A] [MeasurableSpace (DiscreteCharacterSpace A)]
  [BorelSpace (DiscreteCharacterSpace A)] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem shalomSpectralSectorA_D_disjoint (a b : A) :
    Disjoint (shalomSpectralSectorA a b) (shalomSpectralSectorD a b) := by
  rw [Set.disjoint_left]
  intro χ hA hD
  exact not_lt_of_ge hA.2.1 hD.2.1

omit [DiscreteTopology A] [MeasurableSpace (DiscreteCharacterSpace A)]
  [BorelSpace (DiscreteCharacterSpace A)] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem shalomSpectralSectorB_C_disjoint (a b : A) :
    Disjoint (shalomSpectralSectorB a b) (shalomSpectralSectorC a b) := by
  rw [Set.disjoint_left]
  intro χ hB hC
  exact not_lt_of_ge hC.2.1 hB.2.1

omit [DiscreteTopology A] [MeasurableSpace (DiscreteCharacterSpace A)]
  [BorelSpace (DiscreteCharacterSpace A)] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem shalomSpectralSectorB_D_disjoint (a b : A) :
    Disjoint (shalomSpectralSectorB a b) (shalomSpectralSectorD a b) := by
  rw [Set.disjoint_left]
  intro χ hB hD
  linarith [hB.2.1, hD.2.1]

omit [DiscreteTopology A] [MeasurableSpace (DiscreteCharacterSpace A)]
  [BorelSpace (DiscreteCharacterSpace A)] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem shalomSpectralSectorC_D_disjoint (a b : A) :
    Disjoint (shalomSpectralSectorC a b) (shalomSpectralSectorD a b) := by
  rw [Set.disjoint_left]
  intro χ hC hD
  exact not_lt_of_ge hD.2.2 hC.2.2

omit [DiscreteTopology A] [MeasurableSpace (DiscreteCharacterSpace A)]
  [BorelSpace (DiscreteCharacterSpace A)] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem shalomSpectralSector_cover (a b : A) :
    shalomSpectralSectorA a b ∪ shalomSpectralSectorB a b ∪
      shalomSpectralSectorC a b ∪ shalomSpectralSectorD a b =
        shalomSpectralPuncturedWindow a b := by
  ext χ
  constructor
  · intro hχ
    rcases hχ with ((hA | hB) | hC) | hD
    · refine ⟨hA.1, ?_⟩
      intro hzero
      have hcoord : spectralArgCoordinates a b χ = (0, 0) := by
        simpa only [mem_preimage, mem_singleton_iff] using hzero
      have hsector := hA.2
      simp only [shalomSectorA, preimage_ofPred_eq, mem_ofPred_eq, hcoord, mul_zero, Std.le_refl,
        abs_zero, lt_self_iff_false, and_false] at hsector
    · refine ⟨hB.1, ?_⟩
      intro hzero
      have hcoord : spectralArgCoordinates a b χ = (0, 0) := by
        simpa only [mem_preimage, mem_singleton_iff] using hzero
      have hsector := hB.2
      simp only [shalomSectorB, preimage_ofPred_eq, mem_ofPred_eq, hcoord, mul_zero,
        lt_self_iff_false, abs_zero, Std.le_refl, and_true] at hsector
    · refine ⟨hC.1, ?_⟩
      intro hzero
      have hcoord : spectralArgCoordinates a b χ = (0, 0) := by
        simpa only [mem_preimage, mem_singleton_iff] using hzero
      have hsector := hC.2
      simp only [shalomSectorC, preimage_ofPred_eq, mem_ofPred_eq, hcoord, mul_zero, Std.le_refl,
        abs_zero, lt_self_iff_false, and_false] at hsector
    · refine ⟨hD.1, ?_⟩
      intro hzero
      have hcoord : spectralArgCoordinates a b χ = (0, 0) := by
        simpa only [mem_preimage, mem_singleton_iff] using hzero
      have hsector := hD.2
      simp only [shalomSectorD, preimage_ofPred_eq, mem_ofPred_eq, hcoord, mul_zero,
        lt_self_iff_false, abs_zero, Std.le_refl, and_true] at hsector
  · rintro ⟨hwindow, hnonzero⟩
    have hcoord : spectralArgCoordinates a b χ ≠ (0, 0) := by
      intro hzero
      exact hnonzero (by simpa only [mem_preimage, mem_singleton_iff] using hzero)
    let p : ShalomPuncturedPlane := ⟨spectralArgCoordinates a b χ, hcoord⟩
    have hp : p ∈ shalomPuncturedA ∪ shalomPuncturedB ∪
        shalomPuncturedC ∪ shalomPuncturedD := by
      rw [shalomPunctured_cover]
      trivial
    rcases hp with ((hA | hB) | hC) | hD
    · exact Or.inl (Or.inl (Or.inl ⟨hwindow, hA⟩))
    · exact Or.inl (Or.inl (Or.inr ⟨hwindow, hB⟩))
    · exact Or.inl (Or.inr ⟨hwindow, hC⟩)
    · exact Or.inr ⟨hwindow, hD⟩

end

section

open ConnesRigidity MeasureTheory Set

universe u

variable {A : Type u} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
variable {H : CountableDiscreteGroup.{u}}
variable [MeasurableSpace (DiscreteCharacterSpace A)]
  [BorelSpace (DiscreteCharacterSpace A)]

omit [MeasurableSpace (DiscreteCharacterSpace A)] [BorelSpace (DiscreteCharacterSpace A)]
  in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem shalomSpectralSector_tpos_inclusion
    (action : H →* Multiplicative (AddAut A)) (h : H)
    (a b : A)
    (ha : (Multiplicative.toAdd (action h⁻¹)) a = a)
    (hb : (Multiplicative.toAdd (action h⁻¹)) b = b - a) :
    ((dualCharacterAction action h) ''
        (shalomSpectralSectorA a b ∪ shalomSpectralSectorB a b)) ∩
      shalomSpectralPuncturedWindow a b ⊆
        shalomSpectralSectorA a b := by
  rintro _ ⟨⟨χ, hsector, rfl⟩, hpunctured⟩
  have hwindow : χ ∈ spectralTorusWindow a b := by
    rcases hsector with hsector | hsector
    · exact hsector.1
    · exact hsector.1
  have hreal : spectralArgCoordinates a b χ ∈
      shalomSectorA ∪ shalomSectorB := by
    rcases hsector with hsector | hsector
    · exact Or.inl hsector.2
    · exact Or.inr hsector.2
  refine ⟨hpunctured.1, ?_⟩
  change spectralArgCoordinates a b (dualCharacterAction action h χ) ∈
    shalomSectorA
  rw [spectralArgCoordinates_dualCharacterAction_tpos
    action h a b ha hb χ hwindow]
  exact shalomTpos_sector_inclusion
    ⟨spectralArgCoordinates a b χ, hreal, rfl⟩

omit [MeasurableSpace (DiscreteCharacterSpace A)] [BorelSpace (DiscreteCharacterSpace A)]
  in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem shalomSpectralSector_spos_inclusion
    (action : H →* Multiplicative (AddAut A)) (h : H)
    (a b : A)
    (ha : (Multiplicative.toAdd (action h⁻¹)) a = a - b)
    (hb : (Multiplicative.toAdd (action h⁻¹)) b = b) :
    ((dualCharacterAction action h) ''
        (shalomSpectralSectorA a b ∪ shalomSpectralSectorB a b)) ∩
      shalomSpectralPuncturedWindow a b ⊆
        shalomSpectralSectorB a b := by
  rintro _ ⟨⟨χ, hsector, rfl⟩, hpunctured⟩
  have hwindow : χ ∈ spectralTorusWindow a b := by
    rcases hsector with hsector | hsector
    · exact hsector.1
    · exact hsector.1
  have hreal : spectralArgCoordinates a b χ ∈
      shalomSectorA ∪ shalomSectorB := by
    rcases hsector with hsector | hsector
    · exact Or.inl hsector.2
    · exact Or.inr hsector.2
  refine ⟨hpunctured.1, ?_⟩
  change spectralArgCoordinates a b (dualCharacterAction action h χ) ∈
    shalomSectorB
  rw [spectralArgCoordinates_dualCharacterAction_spos
    action h a b ha hb χ hwindow]
  exact shalomSpos_sector_inclusion
    ⟨spectralArgCoordinates a b χ, hreal, rfl⟩

omit [MeasurableSpace (DiscreteCharacterSpace A)] [BorelSpace (DiscreteCharacterSpace A)]
  in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem shalomSpectralSector_tneg_inclusion
    (action : H →* Multiplicative (AddAut A)) (h : H)
    (a b : A)
    (ha : (Multiplicative.toAdd (action h⁻¹)) a = a)
    (hb : (Multiplicative.toAdd (action h⁻¹)) b = b + a) :
    ((dualCharacterAction action h) ''
        (shalomSpectralSectorD a b ∪ shalomSpectralSectorC a b)) ∩
      shalomSpectralPuncturedWindow a b ⊆
        shalomSpectralSectorD a b := by
  rintro _ ⟨⟨χ, hsector, rfl⟩, hpunctured⟩
  have hwindow : χ ∈ spectralTorusWindow a b := by
    rcases hsector with hsector | hsector
    · exact hsector.1
    · exact hsector.1
  have hreal : spectralArgCoordinates a b χ ∈
      shalomSectorD ∪ shalomSectorC := by
    rcases hsector with hsector | hsector
    · exact Or.inl hsector.2
    · exact Or.inr hsector.2
  refine ⟨hpunctured.1, ?_⟩
  change spectralArgCoordinates a b (dualCharacterAction action h χ) ∈
    shalomSectorD
  rw [spectralArgCoordinates_dualCharacterAction_tneg
    action h a b ha hb χ hwindow]
  exact shalomTneg_sector_inclusion
    ⟨spectralArgCoordinates a b χ, hreal, rfl⟩

omit [MeasurableSpace (DiscreteCharacterSpace A)] [BorelSpace (DiscreteCharacterSpace A)]
  in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem shalomSpectralSector_sneg_inclusion
    (action : H →* Multiplicative (AddAut A)) (h : H)
    (a b : A)
    (ha : (Multiplicative.toAdd (action h⁻¹)) a = a + b)
    (hb : (Multiplicative.toAdd (action h⁻¹)) b = b) :
    ((dualCharacterAction action h) ''
        (shalomSpectralSectorD a b ∪ shalomSpectralSectorC a b)) ∩
      shalomSpectralPuncturedWindow a b ⊆
        shalomSpectralSectorC a b := by
  rintro _ ⟨⟨χ, hsector, rfl⟩, hpunctured⟩
  have hwindow : χ ∈ spectralTorusWindow a b := by
    rcases hsector with hsector | hsector
    · exact hsector.1
    · exact hsector.1
  have hreal : spectralArgCoordinates a b χ ∈
      shalomSectorD ∪ shalomSectorC := by
    rcases hsector with hsector | hsector
    · exact Or.inl hsector.2
    · exact Or.inr hsector.2
  refine ⟨hpunctured.1, ?_⟩
  change spectralArgCoordinates a b (dualCharacterAction action h χ) ∈
    shalomSectorC
  rw [spectralArgCoordinates_dualCharacterAction_sneg
    action h a b ha hb χ hwindow]
  exact shalomSneg_sector_inclusion
    ⟨spectralArgCoordinates a b χ, hreal, rfl⟩

end

section

open ConnesRigidity MeasureTheory Set

universe u

variable {A : Type u} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
variable {H : CountableDiscreteGroup.{u}}
variable [MeasurableSpace (DiscreteCharacterSpace A)]
  [BorelSpace (DiscreteCharacterSpace A)]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem shalomSpectral_four_sector_action_gap
    (action : H →* Multiplicative (AddAut A)) (a b : A)
    (tpos spos tneg sneg : H)
    (htpos_a : (Multiplicative.toAdd (action tpos⁻¹)) a = a)
    (htpos_b : (Multiplicative.toAdd (action tpos⁻¹)) b = b - a)
    (hspos_a : (Multiplicative.toAdd (action spos⁻¹)) a = a - b)
    (hspos_b : (Multiplicative.toAdd (action spos⁻¹)) b = b)
    (htneg_a : (Multiplicative.toAdd (action tneg⁻¹)) a = a)
    (htneg_b : (Multiplicative.toAdd (action tneg⁻¹)) b = b + a)
    (hsneg_a : (Multiplicative.toAdd (action sneg⁻¹)) a = a + b)
    (hsneg_b : (Multiplicative.toAdd (action sneg⁻¹)) b = b)
    (ν : ProbabilityMeasure (DiscreteCharacterSpace A))
    (hmass : (ν : Measure (DiscreteCharacterSpace A)).real
      (shalomSpectralPuncturedWindow a b) = 1) :
    ∃ h ∈ ({tpos, spos, tneg, sneg} : Set H),
      ∃ s : Set (DiscreteCharacterSpace A), MeasurableSet s ∧
        (1 / 4 : ℝ) ≤
          |(ν : Measure (DiscreteCharacterSpace A)).real
              (dualCharacterAction action h '' s) -
            (ν : Measure (DiscreteCharacterSpace A)).real s| := by
  apply shalom_four_sector_supported_action_gap
    (ν : Measure (DiscreteCharacterSpace A))
    (dualCharacterAction action) tpos spos tneg sneg
    (shalomSpectralPuncturedWindow a b)
    (shalomSpectralSectorA a b)
    (shalomSpectralSectorB a b)
    (shalomSpectralSectorC a b)
    (shalomSpectralSectorD a b)
    (shalomSpectralPuncturedWindow_measurable a b)
    hmass
    (shalomSpectralSectorA_measurable a b)
    (shalomSpectralSectorB_measurable a b)
    (shalomSpectralSectorC_measurable a b)
    (shalomSpectralSectorD_measurable a b)
    (shalomSpectralSectorA_B_disjoint a b)
    (shalomSpectralSectorA_C_disjoint a b)
    (shalomSpectralSectorA_D_disjoint a b)
    (shalomSpectralSectorB_C_disjoint a b)
    (shalomSpectralSectorB_D_disjoint a b)
    (shalomSpectralSectorC_D_disjoint a b)
    (shalomSpectralSector_cover a b)
  · exact shalomSpectralSector_tpos_inclusion
      action tpos a b htpos_a htpos_b
  · exact shalomSpectralSector_spos_inclusion
      action spos a b hspos_a hspos_b
  · exact shalomSpectralSector_tneg_inclusion
      action tneg a b htneg_a htneg_b
  · exact shalomSpectralSector_sneg_inclusion
      action sneg a b hsneg_a hsneg_b

end

section

open ConnesRigidity MeasureTheory Set

variable {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem conditionedProbability_punctured_window_measureReal_one
    (μ : ProbabilityMeasure Ω) {U s : Set Ω}
    (hU : 0 < (μ : Measure Ω).real U)
    (hUmeas : MeasurableSet U)
    (hs : (μ : Measure Ω).real s = 0) :
    (conditionedProbability μ U hU : Measure Ω).real (U \ s) = 1 := by
  rw [conditionedProbability_measureReal μ hU hUmeas (U \ s)]
  rw [Set.inter_eq_left.mpr sdiff_subset]
  rw [measureReal_sdiff_null hs]
  exact div_self (ne_of_gt hU)

universe u

variable {A : Type u} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
variable [MeasurableSpace (DiscreteCharacterSpace A)]
  [BorelSpace (DiscreteCharacterSpace A)]





end

section

open ConnesRigidity MeasureTheory Set

universe u

variable {A : Type u} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
variable {H : CountableDiscreteGroup.{u}}
variable [MeasurableSpace (DiscreteCharacterSpace A)]
  [BorelSpace (DiscreteCharacterSpace A)]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem shalomSpectral_zeroFiber_positive_of_variation
    (action : H →* Multiplicative (AddAut A)) (a b : A)
    (tpos spos tneg sneg : H)
    (htposa : (Multiplicative.toAdd (action tpos⁻¹)) a = a)
    (htposb : (Multiplicative.toAdd (action tpos⁻¹)) b = b - a)
    (hsposa : (Multiplicative.toAdd (action spos⁻¹)) a = a - b)
    (hsposb : (Multiplicative.toAdd (action spos⁻¹)) b = b)
    (htnega : (Multiplicative.toAdd (action tneg⁻¹)) a = a)
    (htnegb : (Multiplicative.toAdd (action tneg⁻¹)) b = b + a)
    (hsnega : (Multiplicative.toAdd (action sneg⁻¹)) a = a + b)
    (hsnegb : (Multiplicative.toAdd (action sneg⁻¹)) b = b)
    (μ : ProbabilityMeasure (DiscreteCharacterSpace A))
    {ε : ℝ} (hε : 0 ≤ ε) (hsmall : ε ≤ (1 / 10 : ℝ))
    (ha : spectralDetectionEnergy μ a ≤ ε ^ 2)
    (hb : spectralDetectionEnergy μ b ≤ ε ^ 2)
    (hvariation :
      ∀ h ∈ ({tpos, spos, tneg, sneg} : Set H),
        ∀ s : Set (DiscreteCharacterSpace A), MeasurableSet s →
          |((μ : Measure (DiscreteCharacterSpace A)).map
              (dualCharacterAction action h⁻¹)).real s -
            (μ : Measure (DiscreteCharacterSpace A)).real s| ≤
              2 * ε) :
    0 < (μ : Measure (DiscreteCharacterSpace A)).real
      (spectralArgCoordinates a b ⁻¹' {(0, 0)}) := by
  by_contra hpositive
  have hzero : (μ : Measure (DiscreteCharacterSpace A)).real
      (spectralArgCoordinates a b ⁻¹' {(0, 0)}) = 0 :=
    le_antisymm (not_lt.mp hpositive) measureReal_nonneg
  let hU : 0 < (μ : Measure (DiscreteCharacterSpace A)).real
      (spectralTorusWindow a b) :=
    spectralTorusWindow_measureReal_pos μ a b hsmall hε ha hb
  let ν : ProbabilityMeasure (DiscreteCharacterSpace A) :=
    conditionedProbability μ (spectralTorusWindow a b) hU
  have hsupport : (ν : Measure (DiscreteCharacterSpace A)).real
      (shalomSpectralPuncturedWindow a b) = 1 := by
    change (conditionedProbability μ (spectralTorusWindow a b) hU :
      Measure (DiscreteCharacterSpace A)).real
        (spectralTorusWindow a b \
          spectralArgCoordinates a b ⁻¹' {(0, 0)}) = 1
    exact conditionedProbability_punctured_window_measureReal_one μ hU
      (spectralTorusWindow_measurable a b) hzero
  obtain ⟨h, hh, s, hs, hgap⟩ :=
    shalomSpectral_four_sector_action_gap action a b
      tpos spos tneg sneg
      htposa htposb hsposa hsposb htnega htnegb hsnega hsnegb ν hsupport
  have hstrict :
      |(ν : Measure (DiscreteCharacterSpace A)).real
          (dualCharacterAction action h '' s) -
        (ν : Measure (DiscreteCharacterSpace A)).real s| <
          (1 / 4 : ℝ) := by
    change
      |(conditionedProbability μ (spectralTorusWindow a b) hU :
        Measure (DiscreteCharacterSpace A)).real
          (dualCharacterAction action h '' s) -
        (conditionedProbability μ (spectralTorusWindow a b) hU :
          Measure (DiscreteCharacterSpace A)).real s| < (1 / 4 : ℝ)
    let f : DiscreteCharacterSpace A ≃ᵐ DiscreteCharacterSpace A :=
      (dualCharacterHomeomorph action h).toMeasurableEquiv
    have hvar :
        |((μ : Measure (DiscreteCharacterSpace A)).map f.symm).real s -
          (μ : Measure (DiscreteCharacterSpace A)).real s| ≤ 2 * ε := by
      exact hvariation h hh s hs
    exact spectralTorusWindow_conditioned_image_variation_lt_one_fourth
      μ a b hε hsmall ha hb f s hs hvar
  linarith

end

section

open ConnesRigidity MeasureTheory

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
local instance integerAtomDualMeasurable :
    MeasurableSpace (DiscreteCharacterSpace (Fin 2 → ℤ)) := borel _

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
local instance integerAtomDualBorel :
    BorelSpace (DiscreteCharacterSpace (Fin 2 → ℤ)) := ⟨rfl⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem integerShalomShears_inv_mem
    {g : integerElementaryRankTwoActingGroup}
    (hg : g ∈ integerShalomShears) :
    g⁻¹ ∈ integerShalomShears := by
  classical
  simp only [integerShalomShears, Finset.mem_insert,
    Finset.mem_singleton] at hg ⊢
  rcases hg with rfl | rfl | rfl | rfl <;> simp

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem integerTranslationZero_eq_dualCoordinate :
    integerTranslationZero = (Pi.single 0 1) := rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem integerTranslationOne_eq_dualCoordinate :
    integerTranslationOne = (Pi.single 1 1) := rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem integerShalom_spectralArgCoordinates_zero_preimage :
    spectralArgCoordinates integerTranslationZero integerTranslationOne ⁻¹'
      {(0, 0)} =
        ({1} : Set (DiscreteCharacterSpace (Fin 2 → ℤ))) :=
  integerDual_spectralArgCoordinates_origin_preimage

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem integerShalomKazhdanConstant_le_one_tenth :
    shalomPolynomialKazhdanConstant 0 ≤ (1 / 10 : ℝ) := by
  rw [shalomPolynomialKazhdanConstant_zero]
  norm_num

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem integerShalomFourierAtomGap : IntegerShalomFourierAtomGap := by
  intro μ hshears htranslations
  have hzero : spectralDetectionEnergy μ integerTranslationZero ≤
      (shalomPolynomialKazhdanConstant 0) ^ 2 := by
    apply le_of_lt
    apply htranslations integerTranslationZero
    simp only [integerShalomTranslations, integerTranslationZero_eq_dualCoordinate,
      integerTranslationOne_eq_dualCoordinate, Finset.mem_insert, Finset.mem_singleton, true_or]
  have hone : spectralDetectionEnergy μ integerTranslationOne ≤
      (shalomPolynomialKazhdanConstant 0) ^ 2 := by
    apply le_of_lt
    apply htranslations integerTranslationOne
    simp only [integerShalomTranslations, integerTranslationZero_eq_dualCoordinate,
      integerTranslationOne_eq_dualCoordinate, Finset.mem_insert, Finset.mem_singleton, or_true]
  have hvariation :
      ∀ h ∈ ({integerUpperShear, integerLowerShear,
          integerUpperShear⁻¹, integerLowerShear⁻¹} :
            Set integerElementaryRankTwoActingGroup),
        ∀ s : Set (DiscreteCharacterSpace (Fin 2 → ℤ)),
          MeasurableSet s →
            |((μ : Measure (DiscreteCharacterSpace (Fin 2 → ℤ))).map
                (dualCharacterAction
                  integerElementaryRankTwoSplitAbelianExtension.action h⁻¹)).real s -
              (μ : Measure (DiscreteCharacterSpace (Fin 2 → ℤ))).real s| ≤
                2 * shalomPolynomialKazhdanConstant 0 := by
    intro h hh s hs
    have hmem : h ∈ integerShalomShears := by
      simpa only [integerShalomShears, Finset.mem_insert, Finset.mem_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] using hh
    exact le_of_lt
      (hshears h⁻¹ (integerShalomShears_inv_mem hmem) s hs)
  have hpositive := shalomSpectral_zeroFiber_positive_of_variation
    integerElementaryRankTwoSplitAbelianExtension.action
    integerTranslationZero integerTranslationOne
    integerUpperShear integerLowerShear
    integerUpperShear⁻¹ integerLowerShear⁻¹
    integerUpperShear_inv_action_zero
    integerUpperShear_inv_action_one
    integerLowerShear_inv_action_zero
    integerLowerShear_inv_action_one
    (by simpa only [inv_inv,
          integerTranslationZero_eq_dualCoordinate] using integerUpperShear_action_zero)
    (by simpa only [inv_inv, integerTranslationOne_eq_dualCoordinate,
          integerTranslationZero_eq_dualCoordinate] using integerUpperShear_action_one)
    (by simpa only [inv_inv, integerTranslationZero_eq_dualCoordinate,
          integerTranslationOne_eq_dualCoordinate] using integerLowerShear_action_zero)
    (by simpa only [inv_inv,
          integerTranslationOne_eq_dualCoordinate] using integerLowerShear_action_one)
    μ (le_of_lt (shalomPolynomialKazhdanConstant_pos 0))
    integerShalomKazhdanConstant_le_one_tenth hzero hone hvariation
  rw [integerShalom_spectralArgCoordinates_zero_preimage] at hpositive
  exact hpositive

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem integerShalomRelativeKazhdanPair : ShalomIntegerRelativePair :=
  integerShalomRelativeKazhdanPair_of_fourierAtomGap
    integerShalomFourierAtomGap

end

section

open ConnesRigidity MeasureTheory

universe u

variable {A : Type u} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
variable {H : CountableDiscreteGroup.{u}}

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem dualCharacterAction_preimage_eq_image_inv
    (action : H →* Multiplicative (AddAut A)) (h : H)
    (s : Set (DiscreteCharacterSpace A)) :
    dualCharacterAction action h ⁻¹' s =
      dualCharacterAction action h⁻¹ '' s := by
  ext χ
  constructor
  · intro hχ
    refine ⟨dualCharacterAction action h χ, hχ, ?_⟩
    rw [← dualCharacterAction_mul, inv_mul_cancel,
      dualCharacterAction_one]
  · rintro ⟨ψ, hψ, rfl⟩
    change dualCharacterAction action h
      (dualCharacterAction action h⁻¹ ψ) ∈ s
    rw [← dualCharacterAction_mul, mul_inv_cancel,
      dualCharacterAction_one]
    exact hψ

section Borel

variable [MeasurableSpace (DiscreteCharacterSpace A)]
  [BorelSpace (DiscreteCharacterSpace A)]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem dualCharacterAction_measurable
    (action : H →* Multiplicative (AddAut A)) (h : H) :
    Measurable (dualCharacterAction action h) :=
  (dualCharacterAction_continuous action h).measurable

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem dualCharacterAction_map_measureReal
    (action : H →* Multiplicative (AddAut A)) (h : H)
    (μ : Measure (DiscreteCharacterSpace A))
    {s : Set (DiscreteCharacterSpace A)} (hs : MeasurableSet s) :
    (μ.map (dualCharacterAction action h)).real s =
      μ.real (dualCharacterAction action h⁻¹ '' s) := by
  rw [map_measureReal_apply (dualCharacterAction_measurable action h) hs,
    dualCharacterAction_preimage_eq_image_inv]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem dualCharacterAction_image_measureReal_eq_map_inv
    (action : H →* Multiplicative (AddAut A)) (h : H)
    (μ : Measure (DiscreteCharacterSpace A))
    {s : Set (DiscreteCharacterSpace A)} (hs : MeasurableSet s) :
    μ.real (dualCharacterAction action h '' s) =
      (μ.map (dualCharacterAction action h⁻¹)).real s := by
  simpa only [inv_inv] using (dualCharacterAction_map_measureReal action h⁻¹ μ hs).symm

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem dualCharacterAction_image_variation_eq_map_inv
    (action : H →* Multiplicative (AddAut A)) (h : H)
    (μ : Measure (DiscreteCharacterSpace A))
    {s : Set (DiscreteCharacterSpace A)} (hs : MeasurableSet s) :
    |μ.real (dualCharacterAction action h '' s) - μ.real s| =
      |(μ.map (dualCharacterAction action h⁻¹)).real s - μ.real s| := by
  rw [dualCharacterAction_image_measureReal_eq_map_inv action h μ hs]

end Borel

end

section

open Set MeasureTheory

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private instance polynomialCircleMeasurable : MeasurableSpace Circle := borel Circle

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private instance polynomialCircleBorel : BorelSpace Circle := ⟨rfl⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private abbrev PolynomialCircleSequence := ℕ → Circle

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private abbrev PolynomialCirclePair := PolynomialCircleSequence × PolynomialCircleSequence

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private noncomputable def polynomialFirstNontrivial
    (x : PolynomialCircleSequence) : ℕ∞ := by
  classical
  exact if h : ∃ n : ℕ, x n ≠ 1 then (Nat.find h : ℕ∞) else ⊤

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem polynomialFirstNontrivial_eq_top_iff (x : PolynomialCircleSequence) :
    polynomialFirstNontrivial x = ⊤ ↔ ∀ n : ℕ, x n = 1 := by
  classical
  by_cases h : ∃ n : ℕ, x n ≠ 1
  · simp only [polynomialFirstNontrivial, ne_eq, h, ↓reduceDIte, ENat.natCast_ne_top, false_iff,
      not_forall]
  · simp only [polynomialFirstNontrivial, ne_eq, h, ↓reduceDIte, true_iff]
    exact fun n => Classical.byContradiction fun hn => h ⟨n, hn⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem polynomialFirstNontrivial_eq_coe_iff
    (x : PolynomialCircleSequence) (n : ℕ) :
    polynomialFirstNontrivial x = (n : ℕ∞) ↔
      x n ≠ 1 ∧ ∀ m < n, x m = 1 := by
  classical
  constructor
  · intro hval
    by_cases hex : ∃ k : ℕ, x k ≠ 1
    · have hfind : Nat.find hex = n := by
        exact_mod_cast (show (Nat.find hex : ℕ∞) = (n : ℕ∞) by
          simpa only [ne_eq, Nat.cast_inj, polynomialFirstNontrivial, hex, ↓reduceDIte] using hval)
      constructor
      · rw [← hfind]
        exact Nat.find_spec hex
      · intro m hm
        apply Classical.byContradiction
        intro hne
        have hle := Nat.find_min' hex hne
        omega
    · simp only [polynomialFirstNontrivial, ne_eq, hex, ↓reduceDIte, ENat.top_ne_natCast] at hval
  · rintro ⟨hn, hmin⟩
    have hex : ∃ k : ℕ, x k ≠ 1 := ⟨n, hn⟩
    simp only [polynomialFirstNontrivial, dite_eq_left hex]
    apply congrArg ((↑) : ℕ → ℕ∞)
    apply le_antisymm (Nat.find_min' hex hn)
    by_contra hnot
    have hlt : Nat.find hex < n := Nat.lt_of_not_ge hnot
    exact (Nat.find_spec hex) (hmin (Nat.find hex) hlt)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem polynomialFirstNontrivial_le_coe_iff
    (x : PolynomialCircleSequence) (n : ℕ) :
    polynomialFirstNontrivial x ≤ (n : ℕ∞) ↔
      ∃ k ≤ n, x k ≠ 1 := by
  classical
  by_cases hex : ∃ k : ℕ, x k ≠ 1
  · rw [polynomialFirstNontrivial, dite_eq_left hex]
    rw [ENat.natCast_le_natCast]
    constructor
    · intro h
      exact ⟨Nat.find hex, h, Nat.find_spec hex⟩
    · rintro ⟨k, hk, hkn⟩
      exact (Nat.find_min' hex hkn).trans hk
  · constructor
    · intro h
      simp only [polynomialFirstNontrivial, ne_eq, hex, ↓reduceDIte, top_le_iff,
        ENat.natCast_ne_top] at h
    · rintro ⟨k, _, hk⟩
      exact (hex ⟨k, hk⟩).elim

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def polynomialSequenceMul
    (x y : PolynomialCircleSequence) : PolynomialCircleSequence :=
  fun n => x n * y n

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem polynomialSequenceMul_apply
    (x y : PolynomialCircleSequence) (n : ℕ) :
    polynomialSequenceMul x y n = x n * y n := rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def polynomialSequenceTail (x : PolynomialCircleSequence) : PolynomialCircleSequence :=
  fun n => x (n + 1)



/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem polynomialFirstNontrivial_tail_succ
    (x : PolynomialCircleSequence)
    {n : ℕ} (hval : polynomialFirstNontrivial x = (n + 1 : ℕ∞)) :
    polynomialFirstNontrivial (polynomialSequenceTail x) = (n : ℕ∞) := by
  apply (polynomialFirstNontrivial_eq_coe_iff _ n).mpr
  have hcoeff := (polynomialFirstNontrivial_eq_coe_iff x (n + 1)).mp hval
  exact ⟨hcoeff.1, fun m hm => hcoeff.2 (m + 1) (by omega)⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem polynomialFirstNontrivial_mul_eq_left_of_lt
    (x y : PolynomialCircleSequence)
    (hxy : polynomialFirstNontrivial x < polynomialFirstNontrivial y) :
    polynomialFirstNontrivial (polynomialSequenceMul x y) =
      polynomialFirstNontrivial x := by
  classical
  have hxne : polynomialFirstNontrivial x ≠ ⊤ :=
    fun htop => by simp only [htop, not_top_lt] at hxy
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hxne
  have hxval : polynomialFirstNontrivial x = (n : ℕ∞) := hn.symm
  have hx := (polynomialFirstNontrivial_eq_coe_iff x n).mp hxval
  have hyn : y n = 1 := by
    by_contra hne
    have hle := (polynomialFirstNontrivial_le_coe_iff y n).mpr ⟨n, le_rfl, hne⟩
    rw [hxval] at hxy
    exact (not_lt_of_ge hle) hxy
  have hmin : ∀ m < n, polynomialSequenceMul x y m = 1 := by
    intro m hm
    rw [polynomialSequenceMul_apply, hx.2 m hm]
    have hym : y m = 1 := by
      by_contra hne
      have hle :=
        (polynomialFirstNontrivial_le_coe_iff y m).mpr ⟨m, le_rfl, hne⟩
      rw [hxval] at hxy
      have hm' : (m : ℕ∞) < (n : ℕ∞) := ENat.natCast_lt_natCast.mpr hm
      exact (not_lt_of_ge hle) (hm'.trans hxy)
    simp only [hym, mul_one]
  rw [hxval]
  apply (polynomialFirstNontrivial_eq_coe_iff _ n).mpr
  exact ⟨by simpa only [polynomialSequenceMul_apply, hyn, mul_one, ne_eq] using hx.1, hmin⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem polynomialFirstNontrivial_eq_top_iff_eq_one
    (x : PolynomialCircleSequence) :
    polynomialFirstNontrivial x = ⊤ ↔ x = 1 := by
  rw [polynomialFirstNontrivial_eq_top_iff]
  constructor
  · intro h
    funext n
    exact h n
  · intro h n
    simp only [h, Pi.one_apply]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem polynomialFirstNontrivial_tail_lt_of_head
    (x : PolynomialCircleSequence) (hx0 : x 0 = 1) (hx : x ≠ 1) :
    polynomialFirstNontrivial (polynomialSequenceTail x) <
      polynomialFirstNontrivial x := by
  have hxtop : polynomialFirstNontrivial x ≠ ⊤ :=
    fun h => hx ((polynomialFirstNontrivial_eq_top_iff_eq_one x).mp h)
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hxtop
  have hval : polynomialFirstNontrivial x = (n : ℕ∞) := hn.symm
  have hn0 : n ≠ 0 := by
    intro hnzero
    subst n
    exact ((polynomialFirstNontrivial_eq_coe_iff x 0).mp hval).1 hx0
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  rw [polynomialFirstNontrivial_tail_succ x hval, hval]
  exact ENat.natCast_lt_natCast.mpr (Nat.lt_succ_self m)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem polynomialFirstNontrivial_mul_eq_right_of_gt
    (x y : PolynomialCircleSequence)
    (hxy : polynomialFirstNontrivial y < polynomialFirstNontrivial x) :
    polynomialFirstNontrivial (polynomialSequenceMul x y) =
      polynomialFirstNontrivial y := by
  have h := polynomialFirstNontrivial_mul_eq_left_of_lt y x hxy
  have hcomm : polynomialSequenceMul x y = polynomialSequenceMul y x := by
    funext n
    exact mul_comm _ _
  rw [hcomm]
  exact h

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def polynomialRawSectorA : Set PolynomialCirclePair :=
  {z | polynomialFirstNontrivial z.2 < polynomialFirstNontrivial z.1}

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def polynomialRawSectorB : Set PolynomialCirclePair :=
  {z | polynomialFirstNontrivial z.1 = polynomialFirstNontrivial z.2}

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def polynomialRawSectorC : Set PolynomialCirclePair :=
  {z | polynomialFirstNontrivial z.1 < polynomialFirstNontrivial z.2}

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def polynomialNoFree : Set PolynomialCirclePair :=
  {z | z.1 0 = 1 ∧ z.2 0 = 1}

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def polynomialPunctured : Set PolynomialCirclePair :=
  {z | z.1 ≠ 1 ∨ z.2 ≠ 1}

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def polynomialSectorSupport : Set PolynomialCirclePair :=
  polynomialNoFree ∩ polynomialPunctured

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def polynomialSectorA : Set PolynomialCirclePair :=
  polynomialRawSectorA ∩ polynomialSectorSupport

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def polynomialSectorB : Set PolynomialCirclePair :=
  polynomialRawSectorB ∩ polynomialSectorSupport

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def polynomialSectorC : Set PolynomialCirclePair :=
  polynomialRawSectorC ∩ polynomialSectorSupport

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem measurableSet_polynomialFirstNontrivial_lt :
    MeasurableSet {p : PolynomialCirclePair |
      polynomialFirstNontrivial p.1 < polynomialFirstNontrivial p.2} := by
  classical
  have hrepr :
      {p : PolynomialCirclePair |
        polynomialFirstNontrivial p.1 < polynomialFirstNontrivial p.2} =
        ⋃ n : ℕ,
          ({p : PolynomialCirclePair | p.1 n ≠ 1} ∩
            ⋂ m : {m : ℕ // m < n}, {p : PolynomialCirclePair | p.1 m = 1}) ∩
            ⋂ m : {m : ℕ // m ≤ n}, {p : PolynomialCirclePair | p.2 m = 1} := by
    ext p
    simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff, mem_iInter]
    constructor
    · intro h
      have hxne : polynomialFirstNontrivial p.1 ≠ ⊤ :=
        fun htop => by simp only [htop, not_top_lt] at h
      obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hxne
      have hxval : polynomialFirstNontrivial p.1 = (n : ℕ∞) := hn.symm
      have hx := (polynomialFirstNontrivial_eq_coe_iff p.1 n).mp hxval
      refine ⟨n, ⟨hx.1, fun m => hx.2 m.1 m.2⟩, ?_⟩
      intro m
      by_contra hm
      have hle : polynomialFirstNontrivial p.2 ≤ (n : ℕ∞) :=
        (polynomialFirstNontrivial_le_coe_iff p.2 n).mpr ⟨m.1, m.2, hm⟩
      rw [hxval] at h
      exact (not_lt_of_ge hle) h
    · rintro ⟨n, ⟨hxn, hxmin⟩, hymin⟩
      have hxval : polynomialFirstNontrivial p.1 = (n : ℕ∞) :=
        (polynomialFirstNontrivial_eq_coe_iff p.1 n).mpr
          ⟨hxn, fun m hm => hxmin ⟨m, hm⟩⟩
      rw [hxval]
      apply lt_of_not_ge
      intro hy
      obtain ⟨m, hmn, hm⟩ :=
        (polynomialFirstNontrivial_le_coe_iff p.2 n).mp hy
      exact hm (hymin ⟨m, hmn⟩)
  rw [hrepr]
  apply MeasurableSet.iUnion
  intro n
  refine ((measurableSet_eq_fun
    ((measurable_pi_apply n).comp measurable_fst) measurable_const).compl.inter
      (MeasurableSet.iInter fun m : {m : ℕ // m < n} =>
        measurableSet_eq_fun ((measurable_pi_apply m.1).comp measurable_fst)
          measurable_const)).inter ?_
  exact MeasurableSet.iInter fun m : {m : ℕ // m ≤ n} =>
    measurableSet_eq_fun ((measurable_pi_apply m.1).comp measurable_snd)
      measurable_const

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem measurableSet_polynomialNoFree : MeasurableSet polynomialNoFree := by
  exact
    (measurableSet_eq_fun
      ((measurable_pi_apply 0).comp measurable_fst) measurable_const).inter
      (measurableSet_eq_fun
        ((measurable_pi_apply 0).comp measurable_snd) measurable_const)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem measurableSet_polynomialPunctured :
    MeasurableSet polynomialPunctured := by
  have hone : MeasurableSet {x : PolynomialCircleSequence | x = 1} := by
    have hrepr :
        {x : PolynomialCircleSequence | x = 1} =
          ⋂ n : ℕ, {x : PolynomialCircleSequence | x n = 1} := by
      ext x
      simp only [mem_ofPred_eq, mem_iInter]
      constructor
      · intro h n
        simp only [h, Pi.one_apply]
      · intro h
        funext n
        exact h n
    rw [hrepr]
    exact MeasurableSet.iInter fun n =>
      measurableSet_eq_fun (measurable_pi_apply n) measurable_const
  change MeasurableSet
    (({z : PolynomialCirclePair | z.1 = 1})ᶜ ∪
      ({z : PolynomialCirclePair | z.2 = 1})ᶜ)
  exact (hone.preimage measurable_fst).compl.union
    (hone.preimage measurable_snd).compl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem measurableSet_polynomialSectorSupport :
    MeasurableSet polynomialSectorSupport :=
  measurableSet_polynomialNoFree.inter measurableSet_polynomialPunctured

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem measurableSet_polynomialRawSectorC :
    MeasurableSet polynomialRawSectorC :=
  measurableSet_polynomialFirstNontrivial_lt

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem measurableSet_polynomialRawSectorA :
    MeasurableSet polynomialRawSectorA := by
  change MeasurableSet
    ((fun z : PolynomialCirclePair => (z.2, z.1)) ⁻¹'
      {z : PolynomialCirclePair |
        polynomialFirstNontrivial z.1 < polynomialFirstNontrivial z.2})
  exact measurableSet_polynomialFirstNontrivial_lt.preimage
    (measurable_snd.prodMk measurable_fst)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem measurableSet_polynomialRawSectorB :
    MeasurableSet polynomialRawSectorB := by
  have hrepr :
      polynomialRawSectorB =
        (polynomialRawSectorA ∪ polynomialRawSectorC)ᶜ := by
    ext z
    change
      (polynomialFirstNontrivial z.1 = polynomialFirstNontrivial z.2) ↔
        ¬ (polynomialFirstNontrivial z.2 < polynomialFirstNontrivial z.1 ∨
          polynomialFirstNontrivial z.1 < polynomialFirstNontrivial z.2)
    constructor
    · intro h
      rw [h]
      simp only [lt_self_iff_false, or_self, not_false_eq_true]
    · intro h
      exact le_antisymm
        (le_of_not_gt fun hlt => h (Or.inl hlt))
        (le_of_not_gt fun hlt => h (Or.inr hlt))
  rw [hrepr]
  exact (measurableSet_polynomialRawSectorA.union
    measurableSet_polynomialRawSectorC).compl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem measurableSet_polynomialSectorA : MeasurableSet polynomialSectorA :=
  measurableSet_polynomialRawSectorA.inter measurableSet_polynomialSectorSupport

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem measurableSet_polynomialSectorB : MeasurableSet polynomialSectorB :=
  measurableSet_polynomialRawSectorB.inter measurableSet_polynomialSectorSupport

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem measurableSet_polynomialSectorC : MeasurableSet polynomialSectorC :=
  measurableSet_polynomialRawSectorC.inter measurableSet_polynomialSectorSupport

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def polynomialShearT (z : PolynomialCirclePair) : PolynomialCirclePair :=
  (polynomialSequenceMul z.1 (polynomialSequenceTail z.2), z.2)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def polynomialShearS (z : PolynomialCirclePair) : PolynomialCirclePair :=
  (z.1, polynomialSequenceMul z.2 (polynomialSequenceTail z.1))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def polynomialShearN (z : PolynomialCirclePair) : PolynomialCirclePair :=
  (polynomialSequenceMul z.1 z.2, z.2)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem polynomialShearT_mem_rawSectorC
    {z : PolynomialCirclePair}
    (hfree : z ∈ polynomialNoFree)
    (hpunctured : z ∈ polynomialPunctured)
    (hsector : z ∈ polynomialRawSectorA ∪ polynomialRawSectorB) :
    polynomialShearT z ∈ polynomialRawSectorC := by
  change z.1 0 = 1 ∧ z.2 0 = 1 at hfree
  change z.1 ≠ 1 ∨ z.2 ≠ 1 at hpunctured
  have hle : polynomialFirstNontrivial z.2 ≤ polynomialFirstNontrivial z.1 := by
    rcases hsector with h | h
    · exact le_of_lt h
    · exact le_of_eq h.symm
  have hy : z.2 ≠ 1 := by
    intro hyone
    have hyval : polynomialFirstNontrivial z.2 = ⊤ :=
      (polynomialFirstNontrivial_eq_top_iff_eq_one _).mpr hyone
    have hxval : polynomialFirstNontrivial z.1 = ⊤ :=
      top_unique (hyval ▸ hle)
    exact hpunctured.elim
      (fun hx => hx ((polynomialFirstNontrivial_eq_top_iff_eq_one _).mp hxval))
      (fun hy => hy hyone)
  have htail := polynomialFirstNontrivial_tail_lt_of_head z.2 hfree.2 hy
  have hdominates := htail.trans_le hle
  change polynomialFirstNontrivial
      (polynomialSequenceMul z.1 (polynomialSequenceTail z.2)) <
      polynomialFirstNontrivial z.2
  rw [polynomialFirstNontrivial_mul_eq_right_of_gt _ _ hdominates]
  exact htail

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem polynomialShearS_mem_rawSectorA
    {z : PolynomialCirclePair}
    (hfree : z ∈ polynomialNoFree)
    (hpunctured : z ∈ polynomialPunctured)
    (hsector : z ∈ polynomialRawSectorC ∪ polynomialRawSectorB) :
    polynomialShearS z ∈ polynomialRawSectorA := by
  change z.1 0 = 1 ∧ z.2 0 = 1 at hfree
  change z.1 ≠ 1 ∨ z.2 ≠ 1 at hpunctured
  have hle : polynomialFirstNontrivial z.1 ≤ polynomialFirstNontrivial z.2 := by
    rcases hsector with h | h
    · exact le_of_lt h
    · exact le_of_eq h
  have hx : z.1 ≠ 1 := by
    intro hxone
    have hxval : polynomialFirstNontrivial z.1 = ⊤ :=
      (polynomialFirstNontrivial_eq_top_iff_eq_one _).mpr hxone
    have hyval : polynomialFirstNontrivial z.2 = ⊤ :=
      top_unique (hxval ▸ hle)
    exact hpunctured.elim
      (fun hx => hx hxone)
      (fun hy => hy ((polynomialFirstNontrivial_eq_top_iff_eq_one _).mp hyval))
  have htail := polynomialFirstNontrivial_tail_lt_of_head z.1 hfree.1 hx
  have hdominates := htail.trans_le hle
  change polynomialFirstNontrivial
      (polynomialSequenceMul z.2 (polynomialSequenceTail z.1)) <
      polynomialFirstNontrivial z.1
  rw [polynomialFirstNontrivial_mul_eq_right_of_gt _ _ hdominates]
  exact htail

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem polynomialShearN_mem_rawSectorB
    {z : PolynomialCirclePair} (hsector : z ∈ polynomialRawSectorA) :
    polynomialShearN z ∈ polynomialRawSectorB := by
  change polynomialFirstNontrivial
      (polynomialSequenceMul z.1 z.2) = polynomialFirstNontrivial z.2
  exact polynomialFirstNontrivial_mul_eq_right_of_gt z.1 z.2 hsector

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem polynomialShearT_image_sector_inter_support :
    (polynomialShearT '' (polynomialSectorA ∪ polynomialSectorB)) ∩
      polynomialSectorSupport ⊆ polynomialSectorC := by
  rintro w ⟨⟨z, hz, rfl⟩, hw⟩
  rcases hz with ⟨hz, hsupport⟩ | ⟨hz, hsupport⟩
  · exact ⟨polynomialShearT_mem_rawSectorC hsupport.1 hsupport.2 (Or.inl hz), hw⟩
  · exact ⟨polynomialShearT_mem_rawSectorC hsupport.1 hsupport.2 (Or.inr hz), hw⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem polynomialShearS_image_sector_inter_support :
    (polynomialShearS '' (polynomialSectorC ∪ polynomialSectorB)) ∩
      polynomialSectorSupport ⊆ polynomialSectorA := by
  rintro w ⟨⟨z, hz, rfl⟩, hw⟩
  rcases hz with ⟨hz, hsupport⟩ | ⟨hz, hsupport⟩
  · exact ⟨polynomialShearS_mem_rawSectorA hsupport.1 hsupport.2 (Or.inl hz), hw⟩
  · exact ⟨polynomialShearS_mem_rawSectorA hsupport.1 hsupport.2 (Or.inr hz), hw⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem polynomialShearN_image_sector_inter_support :
    (polynomialShearN '' polynomialSectorA) ∩
      polynomialSectorSupport ⊆ polynomialSectorB := by
  rintro w ⟨⟨z, ⟨hz, _⟩, rfl⟩, hw⟩
  exact ⟨polynomialShearN_mem_rawSectorB hz, hw⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem polynomialSector_cover :
    polynomialSectorA ∪ polynomialSectorB ∪ polynomialSectorC =
      polynomialSectorSupport := by
  ext z
  constructor
  · intro hz
    rcases hz with (⟨_, h⟩ | ⟨_, h⟩) | ⟨_, h⟩
    · exact h
    · exact h
    · exact h
  · intro hsupport
    rcases lt_trichotomy
      (polynomialFirstNontrivial z.1)
      (polynomialFirstNontrivial z.2) with hlt | heq | hgt
    · exact Or.inr ⟨hlt, hsupport⟩
    · exact Or.inl (Or.inr ⟨heq, hsupport⟩)
    · exact Or.inl (Or.inl ⟨hgt, hsupport⟩)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem polynomialSector_disjoint_AB :
    Disjoint polynomialSectorA polynomialSectorB := by
  rw [Set.disjoint_left]
  rintro z ⟨hA, _⟩ ⟨hB, _⟩
  exact (ne_of_lt hA) hB.symm

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem polynomialSector_disjoint_AC :
    Disjoint polynomialSectorA polynomialSectorC := by
  rw [Set.disjoint_left]
  rintro z ⟨hA, _⟩ ⟨hC, _⟩
  change polynomialFirstNontrivial z.2 < polynomialFirstNontrivial z.1 at hA
  change polynomialFirstNontrivial z.1 < polynomialFirstNontrivial z.2 at hC
  exact (not_lt_of_ge hA.le) hC

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem polynomialSector_disjoint_BC :
    Disjoint polynomialSectorB polynomialSectorC := by
  rw [Set.disjoint_left]
  rintro z ⟨hB, _⟩ ⟨hC, _⟩
  exact (ne_of_lt hC) hB

end

section

open ConnesRigidity MeasureTheory Set

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private instance integralPolynomialPairTopologicalSpace :
    TopologicalSpace (Fin 2 → IntegralPolynomial) := ⊥

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private instance integralPolynomialPairDiscreteTopology :
    DiscreteTopology (Fin 2 → IntegralPolynomial) := ⟨rfl⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private abbrev PolynomialRankTwoCharacter :=
  DiscreteCharacterSpace (Fin 2 → IntegralPolynomial)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private instance integralPolynomialPairDualMeasurable :
    MeasurableSpace PolynomialRankTwoCharacter := borel _

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private instance integralPolynomialPairDualBorel :
    BorelSpace PolynomialRankTwoCharacter := ⟨rfl⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def polynomialCharacterCoefficient
    (χ : PolynomialRankTwoCharacter) (i : Fin 2) (n : ℕ) : Circle :=
  χ (Multiplicative.ofAdd
    (Pi.single i ((Polynomial.X : IntegralPolynomial) ^ n) :
      Fin 2 → IntegralPolynomial))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def polynomialCharacterCoefficients
    (χ : PolynomialRankTwoCharacter) (i : Fin 2) :
    PolynomialCircleSequence :=
  fun n => polynomialCharacterCoefficient χ i n



/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def polynomialCharacterCoefficientPair
    (χ : PolynomialRankTwoCharacter) : PolynomialCirclePair :=
  (polynomialCharacterCoefficients χ 0,
    polynomialCharacterCoefficients χ 1)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem polynomialCharacterCoefficient_one (i : Fin 2) (n : ℕ) :
    polynomialCharacterCoefficient (1 : PolynomialRankTwoCharacter) i n = 1 := by
  simp only [polynomialCharacterCoefficient, PontryaginDual.one_apply]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem polynomialCharacterCoefficientPair_one :
    polynomialCharacterCoefficientPair (1 : PolynomialRankTwoCharacter) = 1 := by
  apply Prod.ext
  · funext n
    exact polynomialCharacterCoefficient_one 0 n
  · funext n
    exact polynomialCharacterCoefficient_one 1 n

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem continuous_polynomialCharacterCoefficient
    (i : Fin 2) (n : ℕ) :
    Continuous (fun χ : PolynomialRankTwoCharacter =>
      polynomialCharacterCoefficient χ i n) := by
  apply continuous_induced_rng.mpr
  exact continuous_character_evaluation
    (Pi.single i ((Polynomial.X : IntegralPolynomial) ^ n) :
      Fin 2 → IntegralPolynomial)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem measurable_polynomialCharacterCoefficient
    (i : Fin 2) (n : ℕ) :
    Measurable (fun χ : PolynomialRankTwoCharacter =>
      polynomialCharacterCoefficient χ i n) :=
  (continuous_polynomialCharacterCoefficient i n).measurable

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem measurable_polynomialCharacterCoefficients (i : Fin 2) :
    Measurable (fun χ : PolynomialRankTwoCharacter =>
      polynomialCharacterCoefficients χ i) := by
  exact measurable_pi_lambda _ fun n =>
    measurable_polynomialCharacterCoefficient i n

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem measurable_polynomialCharacterCoefficientPair :
    Measurable polynomialCharacterCoefficientPair := by
  exact (measurable_polynomialCharacterCoefficients 0).prodMk
    (measurable_polynomialCharacterCoefficients 1)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem polynomialCharacter_monomial
    (χ : PolynomialRankTwoCharacter) (i : Fin 2)
    (n : ℕ) (z : ℤ) :
    χ (Multiplicative.ofAdd
      (Pi.single i (Polynomial.monomial n z) :
        Fin 2 → IntegralPolynomial)) =
      (polynomialCharacterCoefficient χ i n) ^ z := by
  have hmono : Polynomial.monomial n z =
      z • ((Polynomial.X : IntegralPolynomial) ^ n) := by
    rw [← Polynomial.C_mul_X_pow_eq_monomial,
      Polynomial.smul_eq_C_mul]
  rw [hmono]
  have hsingle :
      (Pi.single i (z • ((Polynomial.X : IntegralPolynomial) ^ n)) :
        Fin 2 → IntegralPolynomial) =
          z • (Pi.single i ((Polynomial.X : IntegralPolynomial) ^ n) :
            Fin 2 → IntegralPolynomial) := by
    ext j
    by_cases hji : j = i <;> simp [hji]
  rw [hsingle]
  change χ ((Multiplicative.ofAdd
    (Pi.single i ((Polynomial.X : IntegralPolynomial) ^ n) :
      Fin 2 → IntegralPolynomial)) ^ z) = _
  exact map_zpow χ _ _

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem polynomialCharacter_ext
    {χ ψ : PolynomialRankTwoCharacter}
    (h : ∀ i : Fin 2, ∀ n : ℕ,
      polynomialCharacterCoefficient χ i n =
        polynomialCharacterCoefficient ψ i n) : χ = ψ := by
  have hcoord : ∀ (i : Fin 2) (p : IntegralPolynomial),
      χ (Multiplicative.ofAdd
        (Pi.single i p : Fin 2 → IntegralPolynomial)) =
      ψ (Multiplicative.ofAdd
        (Pi.single i p : Fin 2 → IntegralPolynomial)) := by
    intro i p
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
        have hsingle :
            (Pi.single i (p + q) : Fin 2 → IntegralPolynomial) =
              Pi.single i p + Pi.single i q := by
          ext j
          by_cases hji : j = i <;> simp [hji]
        rw [hsingle]
        have hsplit :
            Multiplicative.ofAdd
              ((Pi.single i p : Fin 2 → IntegralPolynomial) +
                Pi.single i q) =
              Multiplicative.ofAdd
                (Pi.single i p : Fin 2 → IntegralPolynomial) *
              Multiplicative.ofAdd
                (Pi.single i q : Fin 2 → IntegralPolynomial) := rfl
        rw [hsplit, map_mul, map_mul, hp, hq]
    | monomial n z =>
        rw [polynomialCharacter_monomial χ i n z,
          polynomialCharacter_monomial ψ i n z, h i n]
  apply ContinuousMonoidHom.ext
  intro v
  let w : Fin 2 → IntegralPolynomial := Multiplicative.toAdd v
  have hw : w = Pi.single (0 : Fin 2) (w 0) +
      Pi.single (1 : Fin 2) (w 1) := by
    ext i
    fin_cases i <;> simp
  change χ (Multiplicative.ofAdd w) =
    ψ (Multiplicative.ofAdd w)
  rw [hw]
  have hsplit :
      Multiplicative.ofAdd
        ((Pi.single (0 : Fin 2) (w 0) : Fin 2 → IntegralPolynomial) +
          Pi.single (1 : Fin 2) (w 1)) =
        Multiplicative.ofAdd
          (Pi.single (0 : Fin 2) (w 0) : Fin 2 → IntegralPolynomial) *
        Multiplicative.ofAdd
          (Pi.single (1 : Fin 2) (w 1) : Fin 2 → IntegralPolynomial) := rfl
  rw [hsplit, map_mul, map_mul, hcoord, hcoord]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem polynomialCharacterCoefficientPair_injective :
    Function.Injective polynomialCharacterCoefficientPair := by
  intro χ ψ hpair
  apply polynomialCharacter_ext
  intro i n
  fin_cases i
  · exact congrFun (congrArg Prod.fst hpair) n
  · exact congrFun (congrArg Prod.snd hpair) n

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def polynomialCharacterNoFree : Set PolynomialRankTwoCharacter :=
  {χ | ∀ i : Fin 2, polynomialCharacterCoefficient χ i 0 = 1}

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem polynomialCharacterNoFree_measurable :
    MeasurableSet polynomialCharacterNoFree := by
  have hset : polynomialCharacterNoFree =
    (⋂ i : Fin 2,
      {χ : PolynomialRankTwoCharacter |
        polynomialCharacterCoefficient χ i 0 = 1}) := by
    ext χ
    simp only [polynomialCharacterNoFree, Fin.forall_fin_two,
      Fin.isValue, mem_ofPred_eq, mem_iInter]
  rw [hset]
  exact MeasurableSet.iInter fun i =>
    measurableSet_eq_fun (measurable_polynomialCharacterCoefficient i 0)
      measurable_const



/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem polynomialCharacterNoFree_eq_preimage :
    polynomialCharacterNoFree =
      polynomialCharacterCoefficientPair ⁻¹' polynomialNoFree := by
  ext χ
  change
    (∀ i : Fin 2, polynomialCharacterCoefficient χ i 0 = 1) ↔
      polynomialCharacterCoefficient χ 0 0 = 1 ∧
        polynomialCharacterCoefficient χ 1 0 = 1
  constructor
  · intro h
    exact ⟨h 0, h 1⟩
  · rintro ⟨h0, h1⟩ i
    fin_cases i
    · exact h0
    · exact h1

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem polynomialCharacterCoefficientPair_eq_one_iff
    (χ : PolynomialRankTwoCharacter) :
    polynomialCharacterCoefficientPair χ = 1 ↔ χ = 1 := by
  constructor
  · intro h
    exact polynomialCharacterCoefficientPair_injective
      (h.trans polynomialCharacterCoefficientPair_one.symm)
  · intro h
    rw [h, polynomialCharacterCoefficientPair_one]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem polynomialCharacterCoefficientPair_mem_punctured
    (χ : PolynomialRankTwoCharacter) :
    polynomialCharacterCoefficientPair χ ∈ polynomialPunctured ↔ χ ≠ 1 := by
  calc
    polynomialCharacterCoefficientPair χ ∈ polynomialPunctured ↔
        polynomialCharacterCoefficientPair χ ≠ 1 := by
      change
        polynomialCharacterCoefficients χ 0 ≠ 1 ∨
          polynomialCharacterCoefficients χ 1 ≠ 1 ↔
          (polynomialCharacterCoefficients χ 0,
            polynomialCharacterCoefficients χ 1) ≠ (1, 1)
      constructor
      · rintro (h0 | h1) hpair
        · exact h0 (congrArg Prod.fst hpair)
        · exact h1 (congrArg Prod.snd hpair)
      · intro hpair
        by_contra hnot
        push Not at hnot
        exact hpair (Prod.ext hnot.1 hnot.2)
    _ ↔ χ ≠ 1 :=
      not_congr (polynomialCharacterCoefficientPair_eq_one_iff χ)

end

section

open ConnesRigidity MeasureTheory Set
open scoped BigOperators ENNReal NNReal

section IntegralPolynomialSpectralMeasure

variable {V : Type} [NormedAddCommGroup V]
  [InnerProductSpace ℂ V] [CompleteSpace V]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def integralElementaryJointSpectralProbability
    (π : UnitaryRepresentation integralElementaryRankTwoGroup V)
    (x : V) (hx : ‖x‖ = 1) :
    ProbabilityMeasure
      (DiscreteCharacterSpace (Fin 2 → IntegralPolynomial)) :=
  (jointPositiveSpectralFunctional
    integralElementaryRankTwoSplitAbelianExtension π).probabilityMeasure x hx

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem integralElementaryJointSpectralProbability_energy
    (π : UnitaryRepresentation integralElementaryRankTwoGroup V)
    (x : V) (hx : ‖x‖ = 1) (a : Fin 2 → IntegralPolynomial) :
    spectralDetectionEnergy
        (integralElementaryJointSpectralProbability π x hx) a =
      ‖(π (integralElementaryRankTwoInl (Multiplicative.ofAdd a)) :
          V →L[ℂ] V) x - x‖ ^ 2 := by
  exact (jointPositiveSpectralFunctional
    integralElementaryRankTwoSplitAbelianExtension π).measure_energy x a

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem integralElementaryJointSpectralProbability_shear_map_variation
    (π : UnitaryRepresentation integralElementaryRankTwoGroup V)
    (x : V) (hx : ‖x‖ = 1)
    (h : integralElementaryRankTwoActingGroup)
    {s : Set (DiscreteCharacterSpace (Fin 2 → IntegralPolynomial))}
    (hs : MeasurableSet s) :
    |((integralElementaryJointSpectralProbability π x hx :
          Measure (DiscreteCharacterSpace (Fin 2 → IntegralPolynomial))).map
            (dualCharacterAction
              integralElementaryRankTwoSplitAbelianExtension.action h)).real s -
      (integralElementaryJointSpectralProbability π x hx :
          Measure (DiscreteCharacterSpace (Fin 2 → IntegralPolynomial))).real s| ≤
      2 * ‖(π (integralElementaryRankTwoInr h) : V →L[ℂ] V) x - x‖ := by
  exact abs_jointScalarMeasure_map_measureReal_sub_le
    integralElementaryRankTwoSplitAbelianExtension π x hx h hs

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem integralElementaryJointSpectralProbability_ae_character_eq_one
    (π : UnitaryRepresentation integralElementaryRankTwoGroup V)
    (x : V) (hx : ‖x‖ = 1) (a : Fin 2 → IntegralPolynomial)
    (hfixed : (π (integralElementaryRankTwoInl (Multiplicative.ofAdd a)) :
      V →L[ℂ] V) x = x) :
    ∀ᵐ χ ∂(integralElementaryJointSpectralProbability π x hx :
      Measure (DiscreteCharacterSpace (Fin 2 → IntegralPolynomial))),
        χ (Multiplicative.ofAdd a) = 1 := by
  let μ := integralElementaryJointSpectralProbability π x hx
  have henergy : spectralDetectionEnergy μ a = 0 := by
    rw [integralElementaryJointSpectralProbability_energy, hfixed]
    simp only [sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
  have hintegral :
      (∫ χ : DiscreteCharacterSpace (Fin 2 → IntegralPolynomial),
        ‖((χ (Multiplicative.ofAdd a) : Circle) : ℂ) - 1‖ ^ 2
          ∂(μ : Measure (DiscreteCharacterSpace
            (Fin 2 → IntegralPolynomial)))) = 0 := henergy
  have hae :
      (fun χ : DiscreteCharacterSpace (Fin 2 → IntegralPolynomial) ↦
        ‖((χ (Multiplicative.ofAdd a) : Circle) : ℂ) - 1‖ ^ 2)
          =ᵐ[(μ : Measure (DiscreteCharacterSpace
            (Fin 2 → IntegralPolynomial)))] 0 :=
    (integral_eq_zero_iff_of_nonneg
      (fun χ ↦ sq_nonneg _) (spectralDetection_integrable μ a)).mp hintegral
  filter_upwards [hae] with χ hχ
  have hnorm : ‖((χ (Multiplicative.ofAdd a) : Circle) : ℂ) - 1‖ = 0 := by
    have hsq : ‖((χ (Multiplicative.ofAdd a) : Circle) : ℂ) - 1‖ ^ 2 = 0 := by
      simpa only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, norm_eq_zero,
        Pi.zero_apply] using hχ
    exact (sq_eq_zero_iff).mp hsq
  apply Circle.coe_injective
  simpa only [Circle.coe_one, OneMemClass.coe_eq_one] using (sub_eq_zero.mp (norm_eq_zero.mp hnorm))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem integralElementaryJointSpectralProbability_ae_polynomialCharacterNoFree
    (π : UnitaryRepresentation integralElementaryRankTwoGroup V)
    (x : V) (hx : ‖x‖ = 1)
    (hfixed : ∀ i : Fin 2,
      (π (integralElementaryRankTwoInl (Multiplicative.ofAdd
        (Pi.single i (1 : IntegralPolynomial) :
          Fin 2 → IntegralPolynomial))) : V →L[ℂ] V) x = x) :
    ∀ᵐ χ ∂(integralElementaryJointSpectralProbability π x hx :
      Measure PolynomialRankTwoCharacter),
        χ ∈ polynomialCharacterNoFree := by
  have hzero := integralElementaryJointSpectralProbability_ae_character_eq_one
    π x hx (Pi.single (0 : Fin 2) (1 : IntegralPolynomial)) (hfixed 0)
  have hone := integralElementaryJointSpectralProbability_ae_character_eq_one
    π x hx (Pi.single (1 : Fin 2) (1 : IntegralPolynomial)) (hfixed 1)
  filter_upwards [hzero, hone] with χ hχzero hχone
  change ∀ i : Fin 2, polynomialCharacterCoefficient χ i 0 = 1
  intro i
  fin_cases i
  · simpa only [polynomialCharacterCoefficient, Nat.reduceAdd, Fin.zero_eta, Fin.isValue,
      pow_zero] using hχzero
  · simpa only [polynomialCharacterCoefficient, Nat.reduceAdd, Fin.mk_one, Fin.isValue,
      pow_zero] using hχone

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem integralElementaryJointSpectralProbability_polynomialCharacterNoFree
    (π : UnitaryRepresentation integralElementaryRankTwoGroup V)
    (x : V) (hx : ‖x‖ = 1)
    (hfixed : ∀ i : Fin 2,
      (π (integralElementaryRankTwoInl (Multiplicative.ofAdd
        (Pi.single i (1 : IntegralPolynomial) :
          Fin 2 → IntegralPolynomial))) : V →L[ℂ] V) x = x) :
    (integralElementaryJointSpectralProbability π x hx :
      Measure PolynomialRankTwoCharacter).real polynomialCharacterNoFree = 1 := by
  have hae :=
    integralElementaryJointSpectralProbability_ae_polynomialCharacterNoFree
      π x hx hfixed
  have hmass :
      (integralElementaryJointSpectralProbability π x hx :
        Measure PolynomialRankTwoCharacter) polynomialCharacterNoFree = 1 :=
    (mem_ae_iff_prob_eq_one polynomialCharacterNoFree_measurable).mp hae
  simp only [measureReal_def, hmass, ENNReal.toReal_one]

end IntegralPolynomialSpectralMeasure

end

section

open ConnesRigidity Matrix

variable {A : Type} [CommRing A]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem elementaryRankTwoRoot_inv
    {i j : Fin 2} (hij : i ≠ j) (a : A) :
    (elementaryRankTwoRoot hij a)⁻¹ =
      elementaryRankTwoRoot hij (-a) := by
  apply Subtype.ext
  exact Matrix.SpecialLinearGroup.transvection_inv hij a

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem elementaryRankTwoRoot_smul_single_target
    {i j : Fin 2} (hij : i ≠ j) (a b : A) :
    ((elementaryRankTwoRoot hij a : elementaryRankTwo A) :
      Matrix.SpecialLinearGroup (Fin 2) A) •
        (Pi.single i b : Fin 2 → A) = Pi.single i b := by
  change
    Matrix.SpecialLinearGroup.transvection hij a •
      (Pi.single i b : Fin 2 → A) = Pi.single i b
  ext k
  simp only [Matrix.SpecialLinearGroup.smul_def, SpecialLinearGroup.transvection_coe,
    smul_eq_mulVec, mulVec_single, Pi.smul_apply, col_apply, Matrix.add_apply, Matrix.one_apply,
    hij.symm, and_false, not_false_eq_true, single_apply_of_ne, add_zero, smul_ite,
    MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, one_mul, smul_zero, Pi.single_apply]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem elementaryRankTwoRoot_smul_single_source
    {i j : Fin 2} (hij : i ≠ j) (a b : A) :
    ((elementaryRankTwoRoot hij a : elementaryRankTwo A) :
      Matrix.SpecialLinearGroup (Fin 2) A) •
        (Pi.single j b : Fin 2 → A) =
      Pi.single j b + Pi.single i (a * b) :=
  rankTwo_transvection_smul_single hij a b

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem elementaryRankTwoRoot_inv_smul_single_target
    {i j : Fin 2} (hij : i ≠ j) (a b : A) :
    (((elementaryRankTwoRoot hij a)⁻¹ : elementaryRankTwo A) :
      Matrix.SpecialLinearGroup (Fin 2) A) •
        (Pi.single i b : Fin 2 → A) = Pi.single i b := by
  rw [elementaryRankTwoRoot_inv]
  exact elementaryRankTwoRoot_smul_single_target hij (-a) b

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem elementaryRankTwoRoot_inv_smul_single_source
    {i j : Fin 2} (hij : i ≠ j) (a b : A) :
    (((elementaryRankTwoRoot hij a)⁻¹ : elementaryRankTwo A) :
      Matrix.SpecialLinearGroup (Fin 2) A) •
        (Pi.single j b : Fin 2 → A) =
      Pi.single j b + Pi.single i ((-a) * b) := by
  rw [elementaryRankTwoRoot_inv]
  exact elementaryRankTwoRoot_smul_single_source hij (-a) b

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem shalomPolynomial_X_mul_X_pow (n : ℕ) :
    (Polynomial.X : IntegralPolynomial) * Polynomial.X ^ n =
      Polynomial.X ^ (n + 1) := by
  rw [mul_comm, ← pow_succ]



end

section

open ConnesRigidity Matrix

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def polynomialShearTActing : integralElementaryRankTwoActingGroup :=
  elementaryRankTwoRoot (show (1 : Fin 2) ≠ 0 by decide)
    (-(Polynomial.X : IntegralPolynomial))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def polynomialShearSActing : integralElementaryRankTwoActingGroup :=
  elementaryRankTwoRoot (show (0 : Fin 2) ≠ 1 by decide)
    (-(Polynomial.X : IntegralPolynomial))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def polynomialShearNActing : integralElementaryRankTwoActingGroup :=
  elementaryRankTwoRoot (show (1 : Fin 2) ≠ 0 by decide)
    (-1 : IntegralPolynomial)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def polynomialDualShearT
    (χ : PolynomialRankTwoCharacter) : PolynomialRankTwoCharacter :=
  dualCharacterAction integralElementaryRankTwoSplitAbelianExtension.action
    polynomialShearTActing χ

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def polynomialDualShearS
    (χ : PolynomialRankTwoCharacter) : PolynomialRankTwoCharacter :=
  dualCharacterAction integralElementaryRankTwoSplitAbelianExtension.action
    polynomialShearSActing χ

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def polynomialDualShearN
    (χ : PolynomialRankTwoCharacter) : PolynomialRankTwoCharacter :=
  dualCharacterAction integralElementaryRankTwoSplitAbelianExtension.action
    polynomialShearNActing χ

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem polynomialCharacterCoefficient_dual_root_source
    {i j : Fin 2} (hij : i ≠ j) (a : IntegralPolynomial)
    (χ : PolynomialRankTwoCharacter) (n : ℕ) :
    polynomialCharacterCoefficient
        (dualCharacterAction
          integralElementaryRankTwoSplitAbelianExtension.action
          (elementaryRankTwoRoot hij a) χ) j n =
      polynomialCharacterCoefficient χ j n *
        χ (Multiplicative.ofAdd
          (Pi.single i ((-a) * (Polynomial.X : IntegralPolynomial) ^ n) :
            Fin 2 → IntegralPolynomial)) := by
  change
    χ (Multiplicative.ofAdd
      ((((elementaryRankTwoRoot hij a)⁻¹ :
        elementaryRankTwo IntegralPolynomial) :
        Matrix.SpecialLinearGroup (Fin 2) IntegralPolynomial) •
          (Pi.single j ((Polynomial.X : IntegralPolynomial) ^ n) :
            Fin 2 → IntegralPolynomial))) = _
  rw [elementaryRankTwoRoot_inv_smul_single_source]
  change
    χ (Multiplicative.ofAdd
      ((Pi.single j ((Polynomial.X : IntegralPolynomial) ^ n) :
          Fin 2 → IntegralPolynomial) +
        Pi.single i ((-a) * (Polynomial.X : IntegralPolynomial) ^ n))) = _
  exact map_mul χ _ _

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem polynomialCharacterCoefficient_dual_root_target
    {i j : Fin 2} (hij : i ≠ j) (a : IntegralPolynomial)
    (χ : PolynomialRankTwoCharacter) (n : ℕ) :
    polynomialCharacterCoefficient
        (dualCharacterAction
          integralElementaryRankTwoSplitAbelianExtension.action
          (elementaryRankTwoRoot hij a) χ) i n =
      polynomialCharacterCoefficient χ i n := by
  change
    χ (Multiplicative.ofAdd
      ((((elementaryRankTwoRoot hij a)⁻¹ :
        elementaryRankTwo IntegralPolynomial) :
        Matrix.SpecialLinearGroup (Fin 2) IntegralPolynomial) •
          (Pi.single i ((Polynomial.X : IntegralPolynomial) ^ n) :
            Fin 2 → IntegralPolynomial))) = _
  rw [elementaryRankTwoRoot_inv_smul_single_target]
  rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem polynomialCharacterCoefficientPair_polynomialDualShearT
    (χ : PolynomialRankTwoCharacter) :
    polynomialCharacterCoefficientPair (polynomialDualShearT χ) =
      polynomialShearT (polynomialCharacterCoefficientPair χ) := by
  apply Prod.ext
  · funext n
    change
      polynomialCharacterCoefficient
        (dualCharacterAction
          integralElementaryRankTwoSplitAbelianExtension.action
          (elementaryRankTwoRoot
            (show (1 : Fin 2) ≠ 0 by decide)
            (-(Polynomial.X : IntegralPolynomial))) χ) 0 n =
        polynomialCharacterCoefficient χ 0 n *
          polynomialCharacterCoefficient χ 1 (n + 1)
    rw [polynomialCharacterCoefficient_dual_root_source]
    simp only [neg_neg, shalomPolynomial_X_mul_X_pow]
    rfl
  · funext n
    exact polynomialCharacterCoefficient_dual_root_target
      (show (1 : Fin 2) ≠ 0 by decide)
      (-(Polynomial.X : IntegralPolynomial)) χ n

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem polynomialCharacterCoefficientPair_polynomialDualShearS
    (χ : PolynomialRankTwoCharacter) :
    polynomialCharacterCoefficientPair (polynomialDualShearS χ) =
      polynomialShearS (polynomialCharacterCoefficientPair χ) := by
  apply Prod.ext
  · funext n
    exact polynomialCharacterCoefficient_dual_root_target
      (show (0 : Fin 2) ≠ 1 by decide)
      (-(Polynomial.X : IntegralPolynomial)) χ n
  · funext n
    change
      polynomialCharacterCoefficient
        (dualCharacterAction
          integralElementaryRankTwoSplitAbelianExtension.action
          (elementaryRankTwoRoot
            (show (0 : Fin 2) ≠ 1 by decide)
            (-(Polynomial.X : IntegralPolynomial))) χ) 1 n =
        polynomialCharacterCoefficient χ 1 n *
          polynomialCharacterCoefficient χ 0 (n + 1)
    rw [polynomialCharacterCoefficient_dual_root_source]
    simp only [neg_neg, shalomPolynomial_X_mul_X_pow]
    rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem polynomialCharacterCoefficientPair_polynomialDualShearN
    (χ : PolynomialRankTwoCharacter) :
    polynomialCharacterCoefficientPair (polynomialDualShearN χ) =
      polynomialShearN (polynomialCharacterCoefficientPair χ) := by
  apply Prod.ext
  · funext n
    change
      polynomialCharacterCoefficient
        (dualCharacterAction
          integralElementaryRankTwoSplitAbelianExtension.action
          (elementaryRankTwoRoot
            (show (1 : Fin 2) ≠ 0 by decide)
            (-1 : IntegralPolynomial)) χ) 0 n =
        polynomialCharacterCoefficient χ 0 n *
          polynomialCharacterCoefficient χ 1 n
    rw [polynomialCharacterCoefficient_dual_root_source]
    simp only [neg_neg, one_mul]
    rfl
  · funext n
    exact polynomialCharacterCoefficient_dual_root_target
      (show (1 : Fin 2) ≠ 0 by decide)
      (-1 : IntegralPolynomial) χ n

end

section

open Set MeasureTheory

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def polynomialCharacterSectorSupport : Set PolynomialRankTwoCharacter :=
  polynomialCharacterNoFree \ ({1} : Set PolynomialRankTwoCharacter)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem polynomialCharacterCoefficientPair_preimage_sectorSupport :
    polynomialCharacterCoefficientPair ⁻¹' polynomialSectorSupport =
      polynomialCharacterSectorSupport := by
  ext χ
  change
    (polynomialCharacterCoefficientPair χ ∈ polynomialNoFree ∧
      polynomialCharacterCoefficientPair χ ∈ polynomialPunctured) ↔
      χ ∈ polynomialCharacterNoFree ∧ χ ∉ ({1} : Set PolynomialRankTwoCharacter)
  rw [polynomialCharacterNoFree_eq_preimage,
    polynomialCharacterCoefficientPair_mem_punctured]
  simp only [ne_eq, mem_preimage, mem_singleton_iff]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem measurableSet_polynomialCharacterSectorSupport :
    MeasurableSet polynomialCharacterSectorSupport := by
  rw [← polynomialCharacterCoefficientPair_preimage_sectorSupport]
  exact measurableSet_polynomialSectorSupport.preimage
    measurable_polynomialCharacterCoefficientPair

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def polynomialCharacterSectorA : Set PolynomialRankTwoCharacter :=
  (polynomialCharacterCoefficientPair ⁻¹' polynomialSectorA ∩
    polynomialCharacterNoFree) ∩
    ({1} : Set PolynomialRankTwoCharacter)ᶜ

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def polynomialCharacterSectorB : Set PolynomialRankTwoCharacter :=
  (polynomialCharacterCoefficientPair ⁻¹' polynomialSectorB ∩
    polynomialCharacterNoFree) ∩
    ({1} : Set PolynomialRankTwoCharacter)ᶜ

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def polynomialCharacterSectorC : Set PolynomialRankTwoCharacter :=
  (polynomialCharacterCoefficientPair ⁻¹' polynomialSectorC ∩
    polynomialCharacterNoFree) ∩
    ({1} : Set PolynomialRankTwoCharacter)ᶜ

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem polynomialCharacterSector_preimage_redundant
    (S : Set PolynomialCirclePair) (hS : S ⊆ polynomialSectorSupport) :
    (polynomialCharacterCoefficientPair ⁻¹' S ∩
        polynomialCharacterNoFree) ∩
      ({1} : Set PolynomialRankTwoCharacter)ᶜ =
      polynomialCharacterCoefficientPair ⁻¹' S := by
  ext χ
  constructor
  · exact fun h => h.1.1
  · intro h
    have hs := hS h
    refine ⟨⟨h, ?_⟩, ?_⟩
    · rw [polynomialCharacterNoFree_eq_preimage]
      exact hs.1
    · exact (polynomialCharacterCoefficientPair_mem_punctured χ).mp hs.2

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem polynomialCharacterSectorA_eq_preimage :
    polynomialCharacterSectorA =
      polynomialCharacterCoefficientPair ⁻¹' polynomialSectorA := by
  apply polynomialCharacterSector_preimage_redundant
  exact fun _ h => h.2

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem polynomialCharacterSectorB_eq_preimage :
    polynomialCharacterSectorB =
      polynomialCharacterCoefficientPair ⁻¹' polynomialSectorB := by
  apply polynomialCharacterSector_preimage_redundant
  exact fun _ h => h.2

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem polynomialCharacterSectorC_eq_preimage :
    polynomialCharacterSectorC =
      polynomialCharacterCoefficientPair ⁻¹' polynomialSectorC := by
  apply polynomialCharacterSector_preimage_redundant
  exact fun _ h => h.2

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem measurableSet_polynomialCharacterSectorA :
    MeasurableSet polynomialCharacterSectorA := by
  rw [polynomialCharacterSectorA_eq_preimage]
  exact measurableSet_polynomialSectorA.preimage
    measurable_polynomialCharacterCoefficientPair

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem measurableSet_polynomialCharacterSectorB :
    MeasurableSet polynomialCharacterSectorB := by
  rw [polynomialCharacterSectorB_eq_preimage]
  exact measurableSet_polynomialSectorB.preimage
    measurable_polynomialCharacterCoefficientPair

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem measurableSet_polynomialCharacterSectorC :
    MeasurableSet polynomialCharacterSectorC := by
  rw [polynomialCharacterSectorC_eq_preimage]
  exact measurableSet_polynomialSectorC.preimage
    measurable_polynomialCharacterCoefficientPair

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem polynomialCharacterSector_disjoint_AB :
    Disjoint polynomialCharacterSectorA polynomialCharacterSectorB := by
  rw [polynomialCharacterSectorA_eq_preimage,
    polynomialCharacterSectorB_eq_preimage, Set.disjoint_left]
  exact fun _ hA hB =>
    Set.disjoint_left.mp polynomialSector_disjoint_AB hA hB

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem polynomialCharacterSector_disjoint_AC :
    Disjoint polynomialCharacterSectorA polynomialCharacterSectorC := by
  rw [polynomialCharacterSectorA_eq_preimage,
    polynomialCharacterSectorC_eq_preimage, Set.disjoint_left]
  exact fun _ hA hC =>
    Set.disjoint_left.mp polynomialSector_disjoint_AC hA hC

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem polynomialCharacterSector_disjoint_BC :
    Disjoint polynomialCharacterSectorB polynomialCharacterSectorC := by
  rw [polynomialCharacterSectorB_eq_preimage,
    polynomialCharacterSectorC_eq_preimage, Set.disjoint_left]
  exact fun _ hB hC =>
    Set.disjoint_left.mp polynomialSector_disjoint_BC hB hC

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem polynomialCharacterSector_cover :
    polynomialCharacterSectorA ∪ polynomialCharacterSectorB ∪
        polynomialCharacterSectorC = polynomialCharacterSectorSupport := by
  rw [polynomialCharacterSectorA_eq_preimage,
    polynomialCharacterSectorB_eq_preimage,
    polynomialCharacterSectorC_eq_preimage,
    ← Set.preimage_union, ← Set.preimage_union, polynomialSector_cover,
    polynomialCharacterCoefficientPair_preimage_sectorSupport]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem polynomialCharacterSector_shearT_supported
    (T : PolynomialRankTwoCharacter → PolynomialRankTwoCharacter)
    (hT : ∀ χ, polynomialCharacterCoefficientPair (T χ) =
      polynomialShearT (polynomialCharacterCoefficientPair χ)) :
    (T '' (polynomialCharacterSectorA ∪ polynomialCharacterSectorB)) ∩
      polynomialCharacterSectorSupport ⊆ polynomialCharacterSectorC := by
  rw [polynomialCharacterSectorA_eq_preimage,
    polynomialCharacterSectorB_eq_preimage,
    polynomialCharacterSectorC_eq_preimage,
    ← polynomialCharacterCoefficientPair_preimage_sectorSupport]
  rintro y ⟨⟨x, hx, rfl⟩, hy⟩
  have hfx : polynomialCharacterCoefficientPair x ∈
      polynomialSectorA ∪ polynomialSectorB := hx
  have hfy : polynomialCharacterCoefficientPair (T x) ∈
      polynomialSectorSupport := hy
  have himage : polynomialShearT (polynomialCharacterCoefficientPair x) ∈
      polynomialSectorC := polynomialShearT_image_sector_inter_support
        ⟨⟨polynomialCharacterCoefficientPair x, hfx, rfl⟩, hT x ▸ hfy⟩
  change polynomialCharacterCoefficientPair (T x) ∈ polynomialSectorC
  rw [hT x]
  exact himage

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem polynomialCharacterSector_shearS_supported
    (S : PolynomialRankTwoCharacter → PolynomialRankTwoCharacter)
    (hS : ∀ χ, polynomialCharacterCoefficientPair (S χ) =
      polynomialShearS (polynomialCharacterCoefficientPair χ)) :
    (S '' (polynomialCharacterSectorC ∪ polynomialCharacterSectorB)) ∩
      polynomialCharacterSectorSupport ⊆ polynomialCharacterSectorA := by
  rw [polynomialCharacterSectorA_eq_preimage,
    polynomialCharacterSectorB_eq_preimage,
    polynomialCharacterSectorC_eq_preimage,
    ← polynomialCharacterCoefficientPair_preimage_sectorSupport]
  rintro y ⟨⟨x, hx, rfl⟩, hy⟩
  have hfx : polynomialCharacterCoefficientPair x ∈
      polynomialSectorC ∪ polynomialSectorB := hx
  have hfy : polynomialCharacterCoefficientPair (S x) ∈
      polynomialSectorSupport := hy
  have himage : polynomialShearS (polynomialCharacterCoefficientPair x) ∈
      polynomialSectorA := polynomialShearS_image_sector_inter_support
        ⟨⟨polynomialCharacterCoefficientPair x, hfx, rfl⟩, hS x ▸ hfy⟩
  change polynomialCharacterCoefficientPair (S x) ∈ polynomialSectorA
  rw [hS x]
  exact himage

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem polynomialCharacterSector_shearN_supported
    (N : PolynomialRankTwoCharacter → PolynomialRankTwoCharacter)
    (hN : ∀ χ, polynomialCharacterCoefficientPair (N χ) =
      polynomialShearN (polynomialCharacterCoefficientPair χ)) :
    (N '' polynomialCharacterSectorA) ∩
      polynomialCharacterSectorSupport ⊆ polynomialCharacterSectorB := by
  rw [polynomialCharacterSectorA_eq_preimage,
    polynomialCharacterSectorB_eq_preimage,
    ← polynomialCharacterCoefficientPair_preimage_sectorSupport]
  rintro y ⟨⟨x, hx, rfl⟩, hy⟩
  have hfy : polynomialCharacterCoefficientPair (N x) ∈
      polynomialSectorSupport := hy
  have himage : polynomialShearN (polynomialCharacterCoefficientPair x) ∈
      polynomialSectorB := polynomialShearN_image_sector_inter_support
        ⟨⟨polynomialCharacterCoefficientPair x, hx, rfl⟩, hN x ▸ hfy⟩
  change polynomialCharacterCoefficientPair (N x) ∈ polynomialSectorB
  rw [hN x]
  exact himage

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem polynomialCharacterSectorSupport_measureReal_eq_one
    (μ : Measure PolynomialRankTwoCharacter) [IsProbabilityMeasure μ]
    (hfree : μ.real polynomialCharacterNoFree = 1)
    (hatom : μ.real ({1} : Set PolynomialRankTwoCharacter) = 0) :
    μ.real polynomialCharacterSectorSupport = 1 := by
  exact shalom_punctured_support_measureReal_eq_one μ
    hfree 1 (measurableSet_singleton 1) hatom

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem polynomialCharacterSector_action_gap
    (μ : Measure PolynomialRankTwoCharacter) [IsProbabilityMeasure μ]
    (hfree : μ.real polynomialCharacterNoFree = 1)
    (hatom : μ.real ({1} : Set PolynomialRankTwoCharacter) = 0)
    (T S N : PolynomialRankTwoCharacter → PolynomialRankTwoCharacter)
    (hT : ∀ χ, polynomialCharacterCoefficientPair (T χ) =
      polynomialShearT (polynomialCharacterCoefficientPair χ))
    (hS : ∀ χ, polynomialCharacterCoefficientPair (S χ) =
      polynomialShearS (polynomialCharacterCoefficientPair χ))
    (hN : ∀ χ, polynomialCharacterCoefficientPair (N χ) =
      polynomialShearN (polynomialCharacterCoefficientPair χ)) :
    ∃ shear ∈ ({T, S, N} :
        Set (PolynomialRankTwoCharacter → PolynomialRankTwoCharacter)),
      ∃ U : Set PolynomialRankTwoCharacter, MeasurableSet U ∧
        (1 / 5 : ℝ) ≤ |μ.real (shear '' U) - μ.real U| := by
  have hgap := shalom_three_sector_supported_action_gap μ
    (fun shear χ => shear χ) T S N
    polynomialCharacterSectorSupport
    polynomialCharacterSectorA polynomialCharacterSectorB
    polynomialCharacterSectorC
    measurableSet_polynomialCharacterSectorSupport
    (polynomialCharacterSectorSupport_measureReal_eq_one μ hfree hatom)
    measurableSet_polynomialCharacterSectorA
    measurableSet_polynomialCharacterSectorB
    measurableSet_polynomialCharacterSectorC
    polynomialCharacterSector_disjoint_AB
    polynomialCharacterSector_disjoint_AC
    polynomialCharacterSector_disjoint_BC
    polynomialCharacterSector_cover
    (polynomialCharacterSector_shearT_supported T hT)
    (polynomialCharacterSector_shearS_supported S hS)
    (polynomialCharacterSector_shearN_supported N hN)
  exact hgap

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem polynomialCharacter_atom_pos_of_actual_sector_variation
    (μ : Measure PolynomialRankTwoCharacter) [IsProbabilityMeasure μ]
    (hfree : μ.real polynomialCharacterNoFree = 1)
    (T S N : PolynomialRankTwoCharacter → PolynomialRankTwoCharacter)
    (hT : ∀ χ, polynomialCharacterCoefficientPair (T χ) =
      polynomialShearT (polynomialCharacterCoefficientPair χ))
    (hS : ∀ χ, polynomialCharacterCoefficientPair (S χ) =
      polynomialShearS (polynomialCharacterCoefficientPair χ))
    (hN : ∀ χ, polynomialCharacterCoefficientPair (N χ) =
      polynomialShearN (polynomialCharacterCoefficientPair χ))
    (hvariation : ∀ shear ∈ ({T, S, N} :
        Set (PolynomialRankTwoCharacter → PolynomialRankTwoCharacter)),
      ∀ U : Set PolynomialRankTwoCharacter, MeasurableSet U →
        |μ.real (shear '' U) - μ.real U| < (1 / 5 : ℝ)) :
    0 < μ.real ({1} : Set PolynomialRankTwoCharacter) := by
  by_contra hnot
  have hatom : μ.real ({1} : Set PolynomialRankTwoCharacter) = 0 :=
    le_antisymm (le_of_not_gt hnot) measureReal_nonneg
  obtain ⟨shear, hshear, U, hU, hgap⟩ :=
    polynomialCharacterSector_action_gap μ hfree hatom T S N hT hS hN
  exact (not_lt_of_ge hgap) (hvariation shear hshear U hU)

end

section

open ConnesRigidity



/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem shalomPolynomialUpperShear_inv (a : IntegralPolynomial) :
    (shalomPolynomialUpperShear a)⁻¹ = shalomPolynomialUpperShear (-a) := by
  let x : integralElementaryRankTwoActingGroup :=
    elementaryRankTwoRoot (show (0 : Fin 2) ≠ 1 by decide) a
  let y : integralElementaryRankTwoActingGroup :=
    elementaryRankTwoRoot (show (0 : Fin 2) ≠ 1 by decide) (-a)
  change (integralElementaryRankTwoInr x)⁻¹ = integralElementaryRankTwoInr y
  rw [← map_inv]
  congr 1
  apply Subtype.ext
  exact Matrix.SpecialLinearGroup.transvection_inv
    (show (0 : Fin 2) ≠ 1 by decide) a

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem shalomPolynomialLowerShear_inv (a : IntegralPolynomial) :
    (shalomPolynomialLowerShear a)⁻¹ = shalomPolynomialLowerShear (-a) := by
  let x : integralElementaryRankTwoActingGroup :=
    elementaryRankTwoRoot (show (1 : Fin 2) ≠ 0 by decide) a
  let y : integralElementaryRankTwoActingGroup :=
    elementaryRankTwoRoot (show (1 : Fin 2) ≠ 0 by decide) (-a)
  change (integralElementaryRankTwoInr x)⁻¹ = integralElementaryRankTwoInr y
  rw [← map_inv]
  congr 1
  apply Subtype.ext
  exact Matrix.SpecialLinearGroup.transvection_inv
    (show (1 : Fin 2) ≠ 0 by decide) a

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem shalomPolynomialUpperShear_X_mem :
    shalomPolynomialUpperShear Polynomial.X ∈
      shalomPolynomialKazhdanGenerators := by
  classical
  simp only [shalomPolynomialKazhdanGenerators, shalomPolynomialShearGenerators,
    Finset.union_insert, Finset.union_singleton, Finset.mem_insert, true_or, or_true]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem shalomPolynomialLowerShear_one_mem :
    shalomPolynomialLowerShear 1 ∈ shalomPolynomialKazhdanGenerators := by
  classical
  simp only [shalomPolynomialKazhdanGenerators, shalomPolynomialShearGenerators,
    Finset.union_insert, Finset.union_singleton, Finset.mem_insert, true_or, or_true]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem shalomPolynomialLowerShear_X_mem :
    shalomPolynomialLowerShear Polynomial.X ∈
      shalomPolynomialKazhdanGenerators := by
  classical
  simp only [shalomPolynomialKazhdanGenerators, shalomPolynomialShearGenerators,
    Finset.union_insert, Finset.union_singleton, Finset.mem_insert, true_or, or_true]

end

section

open ConnesRigidity

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem polynomialShearTActing_inv_mem_kazhdanGenerators :
    integralElementaryRankTwoInr (polynomialShearTActing⁻¹) ∈
      shalomPolynomialKazhdanGenerators := by
  rw [map_inv]
  change (shalomPolynomialLowerShear (-Polynomial.X))⁻¹ ∈ _
  rw [shalomPolynomialLowerShear_inv]
  simpa only [neg_neg] using shalomPolynomialLowerShear_X_mem

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem polynomialShearSActing_inv_mem_kazhdanGenerators :
    integralElementaryRankTwoInr (polynomialShearSActing⁻¹) ∈
      shalomPolynomialKazhdanGenerators := by
  rw [map_inv]
  change (shalomPolynomialUpperShear (-Polynomial.X))⁻¹ ∈ _
  rw [shalomPolynomialUpperShear_inv]
  simpa only [neg_neg] using shalomPolynomialUpperShear_X_mem

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem polynomialShearNActing_inv_mem_kazhdanGenerators :
    integralElementaryRankTwoInr (polynomialShearNActing⁻¹) ∈
      shalomPolynomialKazhdanGenerators := by
  rw [map_inv]
  change (shalomPolynomialLowerShear (-1))⁻¹ ∈ _
  rw [shalomPolynomialLowerShear_inv]
  simpa only [neg_neg] using shalomPolynomialLowerShear_one_mem

end

section

open ConnesRigidity MeasureTheory Set

variable {W : Type} [NormedAddCommGroup W]
  [InnerProductSpace ℂ W] [CompleteSpace W]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem polynomialTrivialAtom_pos_of_constantFixed_smallShears_of_covariance
    (π : UnitaryRepresentation integralElementaryRankTwoGroup W)
    (η : W) (hη : ‖η‖ = 1)
    (hfixed : ∀ i : Fin 2,
      (π (integralElementaryRankTwoInl (Multiplicative.ofAdd
        (Pi.single i (1 : IntegralPolynomial) :
          Fin 2 → IntegralPolynomial))) : W →L[ℂ] W) η = η)
    (hsmall : ∀ g ∈ shalomPolynomialKazhdanGenerators,
      ‖(π g : W →L[ℂ] W) η - η‖ < (1 / 10 : ℝ))
    (hT : ∀ χ : PolynomialRankTwoCharacter,
      polynomialCharacterCoefficientPair (polynomialDualShearT χ) =
        polynomialShearT (polynomialCharacterCoefficientPair χ))
    (hS : ∀ χ : PolynomialRankTwoCharacter,
      polynomialCharacterCoefficientPair (polynomialDualShearS χ) =
        polynomialShearS (polynomialCharacterCoefficientPair χ))
    (hN : ∀ χ : PolynomialRankTwoCharacter,
      polynomialCharacterCoefficientPair (polynomialDualShearN χ) =
        polynomialShearN (polynomialCharacterCoefficientPair χ)) :
    0 < spectralTrivialAtom
      (integralElementaryJointSpectralProbability π η hη) := by
  let μ := integralElementaryJointSpectralProbability π η hη
  let action := integralElementaryRankTwoSplitAbelianExtension.action
  have hfree : (μ : Measure PolynomialRankTwoCharacter).real
      polynomialCharacterNoFree = 1 :=
    integralElementaryJointSpectralProbability_polynomialCharacterNoFree
      π η hη hfixed
  apply polynomialCharacter_atom_pos_of_actual_sector_variation
    (μ : Measure PolynomialRankTwoCharacter) hfree
    polynomialDualShearT polynomialDualShearS polynomialDualShearN hT hS hN
  intro shear hshear U hU
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hshear
  rcases hshear with rfl | rfl | rfl
  · change
      |(μ : Measure PolynomialRankTwoCharacter).real
          (dualCharacterAction action polynomialShearTActing '' U) -
        (μ : Measure PolynomialRankTwoCharacter).real U| < (1 / 5 : ℝ)
    rw [dualCharacterAction_image_variation_eq_map_inv
      action polynomialShearTActing (μ : Measure PolynomialRankTwoCharacter) hU]
    have hbound := integralElementaryJointSpectralProbability_shear_map_variation
      π η hη (polynomialShearTActing⁻¹) hU
    have hdisplacement := hsmall _
      polynomialShearTActing_inv_mem_kazhdanGenerators
    linarith
  · change
      |(μ : Measure PolynomialRankTwoCharacter).real
          (dualCharacterAction action polynomialShearSActing '' U) -
        (μ : Measure PolynomialRankTwoCharacter).real U| < (1 / 5 : ℝ)
    rw [dualCharacterAction_image_variation_eq_map_inv
      action polynomialShearSActing (μ : Measure PolynomialRankTwoCharacter) hU]
    have hbound := integralElementaryJointSpectralProbability_shear_map_variation
      π η hη (polynomialShearSActing⁻¹) hU
    have hdisplacement := hsmall _
      polynomialShearSActing_inv_mem_kazhdanGenerators
    linarith
  · change
      |(μ : Measure PolynomialRankTwoCharacter).real
          (dualCharacterAction action polynomialShearNActing '' U) -
        (μ : Measure PolynomialRankTwoCharacter).real U| < (1 / 5 : ℝ)
    rw [dualCharacterAction_image_variation_eq_map_inv
      action polynomialShearNActing (μ : Measure PolynomialRankTwoCharacter) hU]
    have hbound := integralElementaryJointSpectralProbability_shear_map_variation
      π η hη (polynomialShearNActing⁻¹) hU
    have hdisplacement := hsmall _
      polynomialShearNActing_inv_mem_kazhdanGenerators
    linarith

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem polynomialKernelFixed_of_constantFixed_smallShears_of_covariance
    (π : UnitaryRepresentation integralElementaryRankTwoGroup W)
    (η : W) (hη : ‖η‖ = 1)
    (hfixed : ∀ i : Fin 2,
      (π (integralElementaryRankTwoInl (Multiplicative.ofAdd
        (Pi.single i (1 : IntegralPolynomial) :
          Fin 2 → IntegralPolynomial))) : W →L[ℂ] W) η = η)
    (hsmall : ∀ g ∈ shalomPolynomialKazhdanGenerators,
      ‖(π g : W →L[ℂ] W) η - η‖ < (1 / 10 : ℝ))
    (hT : ∀ χ : PolynomialRankTwoCharacter,
      polynomialCharacterCoefficientPair (polynomialDualShearT χ) =
        polynomialShearT (polynomialCharacterCoefficientPair χ))
    (hS : ∀ χ : PolynomialRankTwoCharacter,
      polynomialCharacterCoefficientPair (polynomialDualShearS χ) =
        polynomialShearS (polynomialCharacterCoefficientPair χ))
    (hN : ∀ χ : PolynomialRankTwoCharacter,
      polynomialCharacterCoefficientPair (polynomialDualShearN χ) =
        polynomialShearN (polynomialCharacterCoefficientPair χ)) :
    ∃ ζ : W, ζ ≠ 0 ∧
      ∀ n : integralElementaryRankTwoTranslationSubgroup,
        (π (n : integralElementaryRankTwoGroup) : W →L[ℂ] W) ζ = ζ := by
  have hatom :=
    polynomialTrivialAtom_pos_of_constantFixed_smallShears_of_covariance
      π η hη hfixed hsmall hT hS hN
  obtain ⟨ζ, hζ, hζfixed⟩ := exists_kernel_fixed_of_joint_atom_pos
    integralElementaryRankTwoSplitAbelianExtension π η hη hatom
  refine ⟨ζ, hζ, ?_⟩
  intro n
  obtain ⟨a, ha⟩ := n.property
  rw [← ha]
  exact hζfixed (Multiplicative.toAdd a)

end

section

open ConnesRigidity Matrix

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def shalomConstantVector : (Fin 2 → ℤ) →+ (Fin 2 → IntegralPolynomial) where
  toFun v i := Polynomial.C (v i)
  map_zero' := by
    ext i
    simp only [Pi.zero_apply, eq_intCast, Int.cast_zero, Polynomial.coeff_zero]
  map_add' v w := by
    ext i
    simp only [Pi.add_apply, eq_intCast, Int.cast_add, Polynomial.coeff_add]



/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem shalomConstantVector_single
    (i : Fin 2) (a : ℤ) :
    shalomConstantVector (Pi.single i a) =
      (Pi.single i (Polynomial.C a) : Fin 2 → IntegralPolynomial) := by
  ext j
  by_cases h : i = j <;> simp [shalomConstantVector, h]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def shalomConstantSpecialLinear :
    Matrix.SpecialLinearGroup (Fin 2) ℤ →*
      Matrix.SpecialLinearGroup (Fin 2) IntegralPolynomial :=
  Matrix.SpecialLinearGroup.map (Polynomial.C : ℤ →+* IntegralPolynomial)



/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem shalomConstantSpecialLinear_transvection
    {i j : Fin 2} (hij : i ≠ j) (a : ℤ) :
    shalomConstantSpecialLinear
      (Matrix.SpecialLinearGroup.transvection hij a) =
      Matrix.SpecialLinearGroup.transvection hij (Polynomial.C a) :=
  specialLinear_map_transvection_baseChange Polynomial.C hij a

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem shalomConstantSpecialLinear_map_elementary_le :
    (elementaryRankTwo ℤ).map shalomConstantSpecialLinear ≤
      elementaryRankTwo IntegralPolynomial := by
  change
    (Subgroup.closure
      {g : Matrix.SpecialLinearGroup (Fin 2) ℤ |
        ∃ (i j : Fin 2) (hij : i ≠ j) (a : ℤ),
          Matrix.SpecialLinearGroup.transvection hij a = g}).map
            shalomConstantSpecialLinear ≤ _
  rw [MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨_, ⟨i, j, hij, a, rfl⟩, rfl⟩
  rw [shalomConstantSpecialLinear_transvection]
  exact Subgroup.subset_closure
    ⟨i, j, hij, Polynomial.C a, rfl⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def shalomConstantActing :
    elementaryRankTwo ℤ →* elementaryRankTwo IntegralPolynomial where
  toFun g :=
    ⟨shalomConstantSpecialLinear g,
      shalomConstantSpecialLinear_map_elementary_le
        ⟨g, g.property, rfl⟩⟩
  map_one' := Subtype.ext (map_one shalomConstantSpecialLinear)
  map_mul' g h := Subtype.ext
    (map_mul shalomConstantSpecialLinear
      (g : Matrix.SpecialLinearGroup (Fin 2) ℤ)
      (h : Matrix.SpecialLinearGroup (Fin 2) ℤ))



/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem shalomConstantActing_root
    {i j : Fin 2} (hij : i ≠ j) (a : ℤ) :
    shalomConstantActing (elementaryRankTwoRoot hij a) =
      elementaryRankTwoRoot hij (Polynomial.C a) := by
  apply Subtype.ext
  exact shalomConstantSpecialLinear_transvection hij a

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem shalomConstantVector_action
    (g : elementaryRankTwo ℤ) (v : Fin 2 → ℤ) :
    shalomConstantVector
      ((g : Matrix.SpecialLinearGroup (Fin 2) ℤ) • v) =
      (shalomConstantActing g :
        Matrix.SpecialLinearGroup (Fin 2) IntegralPolynomial) •
          shalomConstantVector v := by
  funext i
  change
    Polynomial.C
        (∑ j : Fin 2,
          (g : Matrix.SpecialLinearGroup (Fin 2) ℤ) i j * v j) =
      ∑ j : Fin 2,
        Polynomial.C
          ((g : Matrix.SpecialLinearGroup (Fin 2) ℤ) i j) *
            Polynomial.C (v j)
  simp only [Fin.sum_univ_two, Fin.isValue, eq_intCast, Int.cast_add, Int.cast_mul]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def shalomConstantMultiplicative :
    Multiplicative (Fin 2 → ℤ) →*
      Multiplicative (Fin 2 → IntegralPolynomial) :=
  shalomConstantVector.toMultiplicative

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem shalomConstantAction_natural (g : elementaryRankTwo ℤ) :
    shalomConstantMultiplicative.comp
        (elementaryRankTwoAction ℤ g).toMonoidHom =
      (elementaryRankTwoAction IntegralPolynomial
        (shalomConstantActing g)).toMonoidHom.comp
          shalomConstantMultiplicative := by
  apply MonoidHom.ext
  intro v
  apply Multiplicative.toAdd.injective
  exact shalomConstantVector_action g (Multiplicative.toAdd v)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def shalomConstantEmbedding :
    integerElementaryRankTwoGroup →*
      integralElementaryRankTwoGroup :=
  SemidirectProduct.map shalomConstantMultiplicative
    shalomConstantActing shalomConstantAction_natural

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem shalomConstantEmbedding_inl (v : Fin 2 → ℤ) :
    shalomConstantEmbedding
        (integerElementaryRankTwoInl (Multiplicative.ofAdd v)) =
      integralElementaryRankTwoInl
        (Multiplicative.ofAdd (shalomConstantVector v)) := by
  exact SemidirectProduct.map_inl shalomConstantMultiplicative
    shalomConstantActing shalomConstantAction_natural
      (Multiplicative.ofAdd v)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem shalomConstantEmbedding_inr (g : elementaryRankTwo ℤ) :
    shalomConstantEmbedding (integerElementaryRankTwoInr g) =
      integralElementaryRankTwoInr (shalomConstantActing g) := by
  exact SemidirectProduct.map_inr shalomConstantMultiplicative
    shalomConstantActing shalomConstantAction_natural g

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem shalomConstantEmbedding_translation
    (i : Fin 2) (a : ℤ) :
    shalomConstantEmbedding
        (integerElementaryRankTwoInl
          (Multiplicative.ofAdd (Pi.single i a))) =
      shalomPolynomialTranslation i (Polynomial.C a) := by
  rw [shalomConstantEmbedding_inl, shalomConstantVector_single]
  rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem shalomConstantEmbedding_integerTranslation
    (i : Fin 2) (a : ℤ) :
    shalomConstantEmbedding (integerShalomTranslation i a) =
      shalomPolynomialTranslation i (Polynomial.C a) :=
  shalomConstantEmbedding_translation i a

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem shalomConstantEmbedding_upperShear (a : ℤ) :
    shalomConstantEmbedding
        (integerElementaryRankTwoInr
          (elementaryRankTwoRoot
            (show (0 : Fin 2) ≠ 1 by decide) a)) =
      shalomPolynomialUpperShear (Polynomial.C a) := by
  rw [shalomConstantEmbedding_inr, shalomConstantActing_root]
  rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem shalomConstantEmbedding_lowerShear (a : ℤ) :
    shalomConstantEmbedding
        (integerElementaryRankTwoInr
          (elementaryRankTwoRoot
            (show (1 : Fin 2) ≠ 0 by decide) a)) =
      shalomPolynomialLowerShear (Polynomial.C a) := by
  rw [shalomConstantEmbedding_inr, shalomConstantActing_root]
  rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem shalomConstantEmbedding_integerUpperShear :
    shalomConstantEmbedding
        (integerElementaryRankTwoInr integerUpperShear) =
      shalomPolynomialUpperShear 1 := by
  simpa only [integerUpperShear, Fin.isValue, shalomConstantEmbedding_inr,
    shalomConstantActing_root, eq_intCast, Int.cast_one] using shalomConstantEmbedding_upperShear 1

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem shalomConstantEmbedding_integerLowerShear :
    shalomConstantEmbedding
        (integerElementaryRankTwoInr integerLowerShear) =
      shalomPolynomialLowerShear 1 := by
  simpa only [integerLowerShear, Fin.isValue, shalomConstantEmbedding_inr,
    shalomConstantActing_root, eq_intCast, Int.cast_one] using shalomConstantEmbedding_lowerShear 1

end

section

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem shalomPolynomialUpperShear_one_inv :
    (shalomPolynomialUpperShear 1)⁻¹ =
      shalomPolynomialUpperShear (-1) :=
  shalomPolynomialUpperShear_inv 1

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem shalomPolynomialLowerShear_one_inv :
    (shalomPolynomialLowerShear 1)⁻¹ =
      shalomPolynomialLowerShear (-1) :=
  shalomPolynomialLowerShear_inv 1

open Classical in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem shalomConstantEmbedding_translationGenerators_image :
    integerShalomTranslationGenerators.image shalomConstantEmbedding =
      shalomPolynomialTranslationGenerators := by
  classical
  simp only [integerShalomTranslationGenerators,
    shalomPolynomialTranslationGenerators, Finset.image_insert,
    Finset.image_singleton, shalomConstantEmbedding_integerTranslation]
  simp only [Fin.isValue, eq_intCast, Int.cast_one, Int.reduceNeg, Int.cast_neg]

open Classical in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem shalomConstantEmbedding_shearGenerators_image_subset :
    integerShalomShearGenerators.image shalomConstantEmbedding ⊆
      shalomPolynomialShearGenerators := by
  classical
  intro g hg
  simp only [integerShalomShearGenerators, Finset.mem_image] at hg
  obtain ⟨_, ⟨h, hh, rfl⟩, rfl⟩ := hg
  simp only [integerShalomShears, Finset.mem_insert,
    Finset.mem_singleton] at hh
  rcases hh with rfl | rfl | rfl | rfl
  · rw [shalomConstantEmbedding_integerUpperShear]
    simp only [shalomPolynomialShearGenerators, Finset.mem_insert, Finset.mem_singleton, true_or]
  · rw [shalomConstantEmbedding_integerLowerShear]
    simp only [shalomPolynomialShearGenerators, Finset.mem_insert, Finset.mem_singleton, true_or,
      or_true]
  · have hinv :
        integerElementaryRankTwoInr (integerUpperShear⁻¹) =
          (integerElementaryRankTwoInr integerUpperShear)⁻¹ :=
        map_inv integerElementaryRankTwoInr integerUpperShear
    rw [hinv, map_inv, shalomConstantEmbedding_integerUpperShear]
    rw [shalomPolynomialUpperShear_one_inv]
    simp only [shalomPolynomialShearGenerators, Finset.mem_insert, Finset.mem_singleton, true_or,
      or_true]
  · have hinv :
        integerElementaryRankTwoInr (integerLowerShear⁻¹) =
          (integerElementaryRankTwoInr integerLowerShear)⁻¹ :=
        map_inv integerElementaryRankTwoInr integerLowerShear
    rw [hinv, map_inv, shalomConstantEmbedding_integerLowerShear]
    rw [shalomPolynomialLowerShear_one_inv]
    simp only [shalomPolynomialShearGenerators, Finset.mem_insert, Finset.mem_singleton, true_or,
      or_true]

open Classical in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem shalomConstantEmbedding_generators_image_subset :
    integerShalomGenerators.image shalomConstantEmbedding ⊆
      shalomPolynomialKazhdanGenerators := by
  classical
  intro g hg
  simp only [integerShalomGenerators, Finset.mem_image,
    Finset.mem_union] at hg
  obtain ⟨h, hh, rfl⟩ := hg
  rcases hh with htranslation | hshear
  · simp only [shalomPolynomialKazhdanGenerators, Finset.mem_union]
    left
    rw [← shalomConstantEmbedding_translationGenerators_image]
    exact Finset.mem_image.mpr ⟨h, htranslation, rfl⟩
  · simp only [shalomPolynomialKazhdanGenerators, Finset.mem_union]
    right
    apply shalomConstantEmbedding_shearGenerators_image_subset
    exact Finset.mem_image.mpr ⟨h, hshear, rfl⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem shalomConstantEmbedding_mem_polynomialGenerators
    {g : integerElementaryRankTwoGroup}
    (hg : g ∈ integerShalomGenerators) :
    shalomConstantEmbedding g ∈ shalomPolynomialKazhdanGenerators := by
  classical
  exact shalomConstantEmbedding_generators_image_subset
    (Finset.mem_image.mpr ⟨g, hg, rfl⟩)

end

section

open ConnesRigidity

universe u

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem shalom_projectionResidual_norm_lt_of_relativePair
    {G₀ G : CountableDiscreteGroup.{u}}
    (N₀ : Subgroup G₀) [N₀.Normal]
    (f : G₀ →* G) {F₀ : Finset G₀} {κ δ : ℝ}
    (hpair : IsRelativeKazhdanPair G₀ N₀ F₀ κ)
    (hδ : 0 < δ)
    (W : Type u) [NormedAddCommGroup W]
      [InnerProductSpace ℂ W] [CompleteSpace W]
    (π : UnitaryRepresentation G W) (ξ : W)
    (hsmall : ∀ g ∈ F₀,
      ‖(π (f g) : W →L[ℂ] W) ξ - ξ‖ < δ) :
    ‖ξ - (normalFixedSubmodule N₀ (π.comp f)).starProjection ξ‖ <
      δ / κ := by
  let ρ : UnitaryRepresentation G₀ W := π.comp f
  let M : Submodule ℂ W := normalFixedSubmodule N₀ ρ
  let z : W := ξ - M.starProjection ξ
  have hκ : 0 < κ := hpair.1
  change ‖z‖ < δ / κ
  by_contra hnot
  have hzlower : δ / κ ≤ ‖z‖ := le_of_not_gt hnot
  have hz : z ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hzlower
    exact (not_le_of_gt (div_pos hδ hκ)) hzlower
  have hzmem : z ∈ Mᗮ :=
    Submodule.sub_starProjection_mem_orthogonal ξ
  let w : Mᗮ :=
    ⟨((‖z‖ : ℂ)⁻¹) • z, (Mᗮ).smul_mem _ hzmem⟩
  have hwnorm : ‖w‖ = 1 := norm_smul_inv_norm hz
  have hwsmall :
      ∀ g ∈ F₀,
        ‖(normalFixedOrthogonalRepresentation N₀ ρ g :
          Mᗮ →L[ℂ] Mᗮ) w - w‖ < κ := by
    intro g hg
    have hcontract :
        ‖(ρ g : W →L[ℂ] W) z - z‖ ≤
          ‖(ρ g : W →L[ℂ] W) ξ - ξ‖ :=
      normalFixed_orthogonalResidual_displacement_le N₀ ρ g ξ
    have hwformula :
        ‖(normalFixedOrthogonalRepresentation N₀ ρ g :
            Mᗮ →L[ℂ] Mᗮ) w - w‖ =
          ‖(ρ g : W →L[ℂ] W) z - z‖ / ‖z‖ := by
      change ‖(ρ g : W →L[ℂ] W)
        (((‖z‖ : ℂ)⁻¹) • z) - ((‖z‖ : ℂ)⁻¹) • z‖ = _
      rw [map_smul, ← smul_sub, norm_smul, norm_inv,
        Complex.norm_real, Real.norm_of_nonneg (norm_nonneg z)]
      simp only [div_eq_mul_inv, mul_comm]
    rw [hwformula]
    apply (div_lt_iff₀ (norm_pos_iff.mpr hz)).2
    have hgsmall : ‖(ρ g : W →L[ℂ] W) ξ - ξ‖ < δ := by
      exact hsmall g hg
    have hδbound : δ ≤ κ * ‖z‖ :=
      by simpa only [mul_comm] using (div_le_iff₀ hκ).mp hzlower
    exact lt_of_lt_of_le (lt_of_le_of_lt hcontract hgsmall) hδbound
  obtain ⟨η, hη, hηfixed⟩ := hpair.2
    Mᗮ inferInstance inferInstance inferInstance
    (normalFixedOrthogonalRepresentation N₀ ρ) w hwnorm hwsmall
  exact hη (normalFixedOrthogonalRepresentation_no_fixed N₀ ρ η hηfixed)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem shalom_normalizedFixedVector_of_relativePair
    {G₀ G : CountableDiscreteGroup.{u}}
    (N₀ : Subgroup G₀) [N₀.Normal]
    (f : G₀ →* G) {F₀ : Finset G₀} {κ δ : ℝ}
    (hpair : IsRelativeKazhdanPair G₀ N₀ F₀ κ)
    (hδ : 0 < δ) (hδκ : δ < κ)
    (W : Type u) [NormedAddCommGroup W]
      [InnerProductSpace ℂ W] [CompleteSpace W]
    (π : UnitaryRepresentation G W) (ξ : W)
    (hξ : ‖ξ‖ = 1)
    (hsmall : ∀ g ∈ F₀,
      ‖(π (f g) : W →L[ℂ] W) ξ - ξ‖ < δ) :
    ∃ η : W, ‖η‖ = 1 ∧
      (∀ n : N₀, (π (f (n : G₀)) : W →L[ℂ] W) η = η) ∧
      ∀ g : G,
        ‖(π g : W →L[ℂ] W) ξ - ξ‖ < δ →
          ‖(π g : W →L[ℂ] W) η - η‖ <
            (δ + 2 * (δ / κ)) / (1 - δ / κ) := by
  let ρ : UnitaryRepresentation G₀ W := π.comp f
  let M : Submodule ℂ W := normalFixedSubmodule N₀ ρ
  let z : W := ξ - M.starProjection ξ
  let p : M := ⟨M.starProjection ξ,
    Submodule.starProjection_apply_mem M ξ⟩
  have hκ : 0 < κ := hpair.1
  have hzsmall : ‖z‖ < δ / κ :=
    shalom_projectionResidual_norm_lt_of_relativePair
      N₀ f hpair hδ W π ξ hsmall
  have hden : 0 < 1 - δ / κ := by
    have hratio : δ / κ < 1 := (div_lt_one hκ).mpr hδκ
    linarith
  have hpbig : 1 - δ / κ < ‖p‖ := by
    have htriangle : ‖ξ‖ ≤ ‖(p : W)‖ + ‖z‖ := by
      calc
        ‖ξ‖ = ‖(p : W) + z‖ := by
          congr 1
          dsimp [p, z]
          abel
        _ ≤ ‖(p : W)‖ + ‖z‖ := norm_add_le _ _
    change 1 - δ / κ < ‖(p : W)‖
    rw [hξ] at htriangle
    linarith
  have hppos : 0 < ‖p‖ := lt_trans hden hpbig
  have hpzero : p ≠ 0 := norm_pos_iff.mp hppos
  let η : W := ((‖p‖ : ℂ)⁻¹) • (p : W)
  refine ⟨η, norm_smul_inv_norm ?_, ?_, ?_⟩
  · exact fun hp => hpzero (Subtype.ext hp)
  · intro n
    change (ρ (n : G₀) : W →L[ℂ] W) η = η
    dsimp [η]
    rw [map_smul, p.property n]
  · intro g hg
    have hzdisp :
        ‖(π g : W →L[ℂ] W) z - z‖ ≤ 2 * ‖z‖ := by
      calc
        ‖(π g : W →L[ℂ] W) z - z‖ ≤
          ‖(π g : W →L[ℂ] W) z‖ + ‖z‖ := norm_sub_le _ _
        _ = 2 * ‖z‖ := by rw [Unitary.norm_map]; ring
    have hpdisp :
        ‖(π g : W →L[ℂ] W) (p : W) - (p : W)‖ ≤
          ‖(π g : W →L[ℂ] W) ξ - ξ‖ + 2 * ‖z‖ := by
      calc
        ‖(π g : W →L[ℂ] W) (p : W) - (p : W)‖ =
            ‖((π g : W →L[ℂ] W) ξ - ξ) -
              ((π g : W →L[ℂ] W) z - z)‖ := by
              congr 1
              dsimp [p, z]
              rw [map_sub]
              abel
        _ ≤ ‖(π g : W →L[ℂ] W) ξ - ξ‖ +
              ‖(π g : W →L[ℂ] W) z - z‖ := norm_sub_le _ _
        _ ≤ ‖(π g : W →L[ℂ] W) ξ - ξ‖ +
              2 * ‖z‖ := add_le_add (le_refl _) hzdisp
    have hpdisplt :
        ‖(π g : W →L[ℂ] W) (p : W) - (p : W)‖ <
          δ + 2 * (δ / κ) := by
      linarith
    have hnumpos : 0 < δ + 2 * (δ / κ) := by
      have hratio : 0 < δ / κ := div_pos hδ hκ
      linarith
    have hfrac :
        ‖(π g : W →L[ℂ] W) (p : W) - (p : W)‖ / ‖(p : W)‖ <
          (δ + 2 * (δ / κ)) / (1 - δ / κ) := by
      apply (div_lt_div_iff₀ hppos hden).mpr
      exact lt_trans
        (mul_lt_mul_of_pos_right hpdisplt hden)
        (mul_lt_mul_of_pos_left hpbig hnumpos)
    change ‖(π g : W →L[ℂ] W)
      (((‖p‖ : ℂ)⁻¹) • (p : W)) -
        ((‖p‖ : ℂ)⁻¹) • (p : W)‖ < _
    rw [map_smul, ← smul_sub, norm_smul, norm_inv,
      Complex.norm_real, Real.norm_of_nonneg (norm_nonneg p)]
    simpa only [Submodule.coe_norm, div_eq_mul_inv, mul_comm] using hfrac

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem shalom_normalizedConstantFixedVector_of_integerPair
    (hbase : ShalomIntegerRelativePair)
    (W : Type) [NormedAddCommGroup W]
      [InnerProductSpace ℂ W] [CompleteSpace W]
    (π : UnitaryRepresentation integralElementaryRankTwoGroup W)
    (ξ : W) (hξ : ‖ξ‖ = 1)
    (hsmall : ∀ g ∈ shalomPolynomialKazhdanGenerators,
      ‖(π g : W →L[ℂ] W) ξ - ξ‖ <
        shalomPolynomialKazhdanConstant 1) :
    ∃ η : W, ‖η‖ = 1 ∧
      (∀ n : integerElementaryRankTwoTranslationSubgroup,
        (π (shalomConstantEmbedding (n : integerElementaryRankTwoGroup)) :
          W →L[ℂ] W) η = η) ∧
      ∀ g ∈ shalomPolynomialKazhdanGenerators,
        ‖(π g : W →L[ℂ] W) η - η‖ < (1 / 10 : ℝ) := by
  let : integerElementaryRankTwoTranslationSubgroup.Normal := by
    rw [← integerElementaryRankTwoSplitAbelianExtension_range,
      ← integerElementaryRankTwoSplitAbelianExtension.exact]
    infer_instance
  have hδ : 0 < shalomPolynomialKazhdanConstant 1 :=
    shalomPolynomialKazhdanConstant_pos 1
  have hδκ : shalomPolynomialKazhdanConstant 1 <
      shalomPolynomialKazhdanConstant 0 := by
    rw [shalomPolynomialKazhdanConstant_one,
      shalomPolynomialKazhdanConstant_zero]
    norm_num
  have hsmallconst : ∀ g ∈ integerShalomGenerators,
      ‖(π (shalomConstantEmbedding g) : W →L[ℂ] W) ξ - ξ‖ <
        shalomPolynomialKazhdanConstant 1 := by
    intro g hg
    exact hsmall (shalomConstantEmbedding g)
      (shalomConstantEmbedding_mem_polynomialGenerators hg)
  obtain ⟨η, hηnorm, hηfixed, hηdisp⟩ :=
    shalom_normalizedFixedVector_of_relativePair
      integerElementaryRankTwoTranslationSubgroup
      shalomConstantEmbedding hbase hδ hδκ W π ξ hξ hsmallconst
  refine ⟨η, hηnorm, hηfixed, ?_⟩
  intro g hg
  refine lt_trans (hηdisp g (hsmall g hg)) ?_
  rw [shalomPolynomialKazhdanConstant_one,
    shalomPolynomialKazhdanConstant_zero]
  norm_num

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem shalom_constantCoordinate_fixed_of_constantTranslation_fixed
    (W : Type) [NormedAddCommGroup W]
      [InnerProductSpace ℂ W] [CompleteSpace W]
    (π : UnitaryRepresentation integralElementaryRankTwoGroup W)
    (η : W)
    (hfixed : ∀ n : integerElementaryRankTwoTranslationSubgroup,
      (π (shalomConstantEmbedding (n : integerElementaryRankTwoGroup)) :
        W →L[ℂ] W) η = η) :
    ∀ i : Fin 2,
      (π (integralElementaryRankTwoInl
        (Multiplicative.ofAdd
          (Pi.single i (1 : IntegralPolynomial)))) : W →L[ℂ] W) η = η := by
  intro i
  let n : integerElementaryRankTwoTranslationSubgroup :=
    ⟨integerElementaryRankTwoInl
      (Multiplicative.ofAdd (Pi.single i (1 : ℤ))),
      ⟨Multiplicative.ofAdd (Pi.single i (1 : ℤ)), rfl⟩⟩
  have hn := hfixed n
  simpa [n] using hn

end

section

open ConnesRigidity MeasureTheory Set

section

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem shalom_normalizedConstantFixedVector
    (W : Type) [NormedAddCommGroup W]
      [InnerProductSpace ℂ W] [CompleteSpace W]
    (π : UnitaryRepresentation integralElementaryRankTwoGroup W)
    (ξ : W) (hξ : ‖ξ‖ = 1)
    (hsmall : ∀ g ∈ shalomPolynomialKazhdanGenerators,
      ‖(π g : W →L[ℂ] W) ξ - ξ‖ <
        shalomPolynomialKazhdanConstant 1) :
    ∃ η : W, ‖η‖ = 1 ∧
      (∀ n : integerElementaryRankTwoTranslationSubgroup,
        (π (shalomConstantEmbedding
          (n : integerElementaryRankTwoGroup)) : W →L[ℂ] W) η = η) ∧
      ∀ g ∈ shalomPolynomialKazhdanGenerators,
        ‖(π g : W →L[ℂ] W) η - η‖ < (1 / 10 : ℝ) :=
  shalom_normalizedConstantFixedVector_of_integerPair
    integerShalomRelativeKazhdanPair W π ξ hξ hsmall

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem shalomIntegralPolynomialRelativePair_of_constantFixed
    (hkernel : ∀ (W : Type)
      (_ : NormedAddCommGroup W)
      (_ : InnerProductSpace ℂ W)
      (_ : CompleteSpace W)
      (π : UnitaryRepresentation integralElementaryRankTwoGroup W)
      (η : W),
      ‖η‖ = 1 →
      (∀ i : Fin 2,
        (π (integralElementaryRankTwoInl (Multiplicative.ofAdd
          (Pi.single i (1 : IntegralPolynomial) :
            Fin 2 → IntegralPolynomial))) : W →L[ℂ] W) η = η) →
      (∀ g ∈ shalomPolynomialKazhdanGenerators,
        ‖(π g : W →L[ℂ] W) η - η‖ < (1 / 10 : ℝ)) →
      ∃ ζ : W, ζ ≠ 0 ∧
        ∀ n : integralElementaryRankTwoTranslationSubgroup,
          (π (n : integralElementaryRankTwoGroup) : W →L[ℂ] W) ζ = ζ) :
    ShalomIntegralPolynomialRelativePair := by
  refine ⟨shalomPolynomialKazhdanConstant_pos 1, ?_⟩
  intro W _ _ _ π ξ hξ hsmall
  obtain ⟨η, hη, hfixed, hηsmall⟩ :=
    shalom_normalizedConstantFixedVector W π ξ hξ hsmall
  exact hkernel W inferInstance inferInstance inferInstance π η hη
    (shalom_constantCoordinate_fixed_of_constantTranslation_fixed
      W π η hfixed) hηsmall

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem shalomIntegralPolynomialRelativePair :
    ShalomIntegralPolynomialRelativePair := by
  apply shalomIntegralPolynomialRelativePair_of_constantFixed
  intro W _ _ _ π η hη hfixed hsmall
  exact polynomialKernelFixed_of_constantFixed_smallShears_of_covariance
    π η hη hfixed hsmall
    polynomialCharacterCoefficientPair_polynomialDualShearT
    polynomialCharacterCoefficientPair_polynomialDualShearS
    polynomialCharacterCoefficientPair_polynomialDualShearN

end

end

section

open ConnesRigidity

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem integralElementaryGroup_propertyT_of_shalomPair
    (hShalomPair : ShalomIntegralPolynomialRelativePair) :
    HasKazhdanPropertyT integralElementaryGroup := by
  obtain ⟨hleft, hright⟩ :=
    cornulier_relativeAffineFixedPoints_of_shalom_gaussian hShalomPair
  exact cornulier_theorem7
    integralElementaryGroup cornulierH cornulierK₁ cornulierK₂
    cornulierFiniteOppositeRoots
    cornulier_finiteOppositeRoots_closure_eq_top
    cornulier_finiteOppositeRoots_subset
    cornulier_oppositeRoots_generate
    cornulierH_le_normalizer_K₁
    cornulierH_le_normalizer_K₂
    (fun φ g => cornulier_realCharacter_eq_zero φ g)
    ((cornulier_corelative_iff_affineOrbitBound
      integralElementaryGroup cornulierH).mp
      (cornulier_proposition4_of_shalom_gaussian hShalomPair))
    hleft hright

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem integralElementaryGroup_propertyT :
    HasKazhdanPropertyT integralElementaryGroup :=
  integralElementaryGroup_propertyT_of_shalomPair
    shalomIntegralPolynomialRelativePair

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem universalLatticePropertyT_of_suslinRelative
    (hSuslinRelative : SuslinRelativeElementaryGeneration) :
    ErshovJaikinUniversalLatticePropertyT :=
  cornulier_fullLatticePropertyT_of_relativeSuslin hSuslinRelative
    integralElementaryGroup_propertyT

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem suslinRelativeElementaryGeneration :
    SuslinRelativeElementaryGeneration := by
  apply suslinRelativeElementaryGeneration_of_maximal_local_elementary
  intro g _ m _
  exact suslin_atPrime_polynomial_elementary m
    (Matrix.SpecialLinearGroup.map
      (Polynomial.mapRingHom
        (algebraMap ℤ (Localization.AtPrime m))) g)

end

section

open ConnesRigidity

section

universe u v

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem conj_mem_centralizer_image_iff
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (e : H ≃ₗᵢ[ℂ] K)
    (S : Set (H →L[ℂ] H)) (T : H →L[ℂ] H) :
    e.conjStarAlgEquiv T ∈
        StarSubalgebra.centralizer ℂ (e.conjStarAlgEquiv '' S) ↔
      T ∈ StarSubalgebra.centralizer ℂ S := by
  rw [StarSubalgebra.mem_centralizer_iff,
    StarSubalgebra.mem_centralizer_iff]
  constructor
  · intro h x hx
    have hx' := h (e.conjStarAlgEquiv x) ⟨x, hx, rfl⟩
    constructor
    · have heq :
          e.conjStarAlgEquiv (x * T) =
            e.conjStarAlgEquiv (T * x) := by
        rw [map_mul, map_mul]
        exact hx'.1
      exact e.conjStarAlgEquiv.injective heq
    · have heq :
          e.conjStarAlgEquiv (star x * T) =
            e.conjStarAlgEquiv (T * star x) := by
        rw [map_mul, map_mul]
        simpa only [map_star] using hx'.2
      exact e.conjStarAlgEquiv.injective heq
  · intro h y hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hx' := h x hx
    constructor
    · have heq := congrArg e.conjStarAlgEquiv hx'.1
      rw [map_mul, map_mul] at heq
      exact heq
    · have heq := congrArg e.conjStarAlgEquiv hx'.2
      rw [map_mul, map_mul] at heq
      rw [map_star] at heq
      exact heq

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem conj_image_centralizer
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (e : H ≃ₗᵢ[ℂ] K)
    (S : Set (H →L[ℂ] H)) :
    (StarSubalgebra.centralizer ℂ
        (e.conjStarAlgEquiv '' S) : Set (K →L[ℂ] K)) =
      e.conjStarAlgEquiv ''
        (StarSubalgebra.centralizer ℂ S : Set (H →L[ℂ] H)) := by
  ext y
  constructor
  · intro hy
    refine ⟨e.conjStarAlgEquiv.symm y, ?_, ?_⟩
    · apply (conj_mem_centralizer_image_iff
        e S (e.conjStarAlgEquiv.symm y)).mp
      rw [e.conjStarAlgEquiv.apply_symm_apply]
      exact hy
    · exact e.conjStarAlgEquiv.apply_symm_apply y
  · rintro ⟨x, hx, rfl⟩
    exact (conj_mem_centralizer_image_iff e S x).mpr hx

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem conj_mem_vonNeumannClosure_image_iff
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (e : H ≃ₗᵢ[ℂ] K)
    (S : Set (H →L[ℂ] H)) (T : H →L[ℂ] H) :
    e.conjStarAlgEquiv T ∈
        vonNeumannClosure (e.conjStarAlgEquiv '' S) ↔
      T ∈ vonNeumannClosure S := by
  change
    e.conjStarAlgEquiv T ∈ StarSubalgebra.centralizer ℂ
        (StarSubalgebra.centralizer ℂ
          (e.conjStarAlgEquiv '' S) : Set (K →L[ℂ] K)) ↔
      T ∈ StarSubalgebra.centralizer ℂ
        (StarSubalgebra.centralizer ℂ S : Set (H →L[ℂ] H))
  rw [conj_image_centralizer e S]
  exact conj_mem_centralizer_image_iff e
    (StarSubalgebra.centralizer ℂ S : Set (H →L[ℂ] H)) T

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem isProjectionSupremum_image_starAlgEquiv
    {A : Type u} {B : Type v}
    [Semiring A] [StarRing A] [Algebra ℂ A]
    [Semiring B] [StarRing B] [Algebra ℂ B]
    (e : A ≃⋆ₐ[ℂ] B) (S : Set A) (p : A)
    (hp : IsProjectionSupremum S p) :
    IsProjectionSupremum (e '' S) (e p) := by
  refine ⟨hp.1.map e, ?_, ?_⟩
  · rintro q ⟨r, hrS, rfl⟩
    exact ⟨(hp.2.1 r hrS).1.map e,
      by
        simpa only [ProjectionLE, map_mul] using
          congrArg e (hp.2.1 r hrS).2⟩
  · intro r hr hupper
    have hr' : IsStarProjection (e.symm r) := hr.map e.symm
    have hbound : ∀ q ∈ S, ProjectionLE q (e.symm r) := by
      intro q hq
      have himage : e q ∈ e '' S := ⟨q, hq, rfl⟩
      have h := hupper (e q) himage
      simpa only [ProjectionLE, map_mul, StarAlgEquiv.symm_apply_apply] using congrArg e.symm h
    have hleast := hp.2.2 (e.symm r) hr' hbound
    simpa only [ProjectionLE, map_mul, StarAlgEquiv.apply_symm_apply] using congrArg e hleast

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem starAlgEquiv_isNormal
    {A : Type u} {B : Type v}
    [Semiring A] [StarRing A] [Algebra ℂ A]
    [Semiring B] [StarRing B] [Algebra ℂ B]
    (e : A ≃⋆ₐ[ℂ] B) :
    IsNormalStarAlgEquiv e :=
  ⟨isProjectionSupremum_image_starAlgEquiv e,
    isProjectionSupremum_image_starAlgEquiv e.symm⟩

open MeasureTheory

variable {Γ : Type*} [Group Γ]
variable {Ω : Type*} [AddCommGroup Ω] [TopologicalSpace Ω] [MeasurableSpace Ω]
variable {Ξ : Type*} [AddCommGroup Ξ] [TopologicalSpace Ξ] [MeasurableSpace Ξ]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem crossedHaarHilbertEquiv_multiplier_conj
    {X : HaarProbabilityAction Γ Ω}
    {Y : HaarProbabilityAction Γ Ξ}
    (e : EquivariantHaarEquiv X Y)
    (f : crossedCoefficient X) :
    (crossedHaarHilbertEquiv e).conjStarAlgEquiv
        (crossedMultiplier X f) =
      crossedMultiplier Y
        (Lp.compMeasurePreserving e.toMeasurableEquiv.symm
          (EquivariantHaarEquiv.symm e).measure_preserving f) := by
  apply ContinuousLinearMap.ext
  intro η
  obtain ⟨ξ, rfl⟩ := (crossedHaarHilbertEquiv e).surjective η
  apply lp.ext
  funext k
  change
    crossedHaarHilbertEquiv e
      (crossedMultiplier X f
        ((crossedHaarHilbertEquiv e).symm
          ((crossedHaarHilbertEquiv e) ξ))) k =
      crossedBaseMultiplier Y
        (Lp.compMeasurePreserving e.toMeasurableEquiv.symm
          (EquivariantHaarEquiv.symm e).measure_preserving f)
        (crossedBaseHaarEquiv e (ξ k))
  rw [LinearIsometryEquiv.symm_apply_apply]
  change
    crossedBaseHaarEquiv e (crossedBaseMultiplier X f (ξ k)) =
      crossedBaseMultiplier Y
        (Lp.compMeasurePreserving e.toMeasurableEquiv.symm
          (EquivariantHaarEquiv.symm e).measure_preserving f)
        (crossedBaseHaarEquiv e (ξ k))
  exact crossedBaseHaarEquiv_multiplier_apply e f (ξ k)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem crossedCoefficient_pullback_symm_apply
    {X : HaarProbabilityAction Γ Ω}
    {Y : HaarProbabilityAction Γ Ξ}
    (e : EquivariantHaarEquiv X Y)
    (f : crossedCoefficient Y) :
    Lp.compMeasurePreserving e.toMeasurableEquiv.symm
      (EquivariantHaarEquiv.symm e).measure_preserving
      (Lp.compMeasurePreserving e.toMeasurableEquiv
        e.measure_preserving f) = f := by
  let hs : MeasurePreserving
      (e.toMeasurableEquiv.symm : Ξ → Ω) Y.measure X.measure :=
    (EquivariantHaarEquiv.symm e).measure_preserving
  have h := Lp.compMeasurePreserving_comp_apply f e.measure_preserving hs
  simpa only [Function.comp_def, MeasurableEquiv.apply_symm_apply,
    show (fun z : Ξ ↦ z) = id from rfl, Lp.compMeasurePreserving_id,
    AddMonoidHom.id_apply] using h.symm

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem crossedGeneratorSet_image
    {X : HaarProbabilityAction Γ Ω}
    {Y : HaarProbabilityAction Γ Ξ}
    (e : EquivariantHaarEquiv X Y) :
    (crossedHaarHilbertEquiv e).conjStarAlgEquiv '' crossedGeneratorSet X =
      crossedGeneratorSet Y := by
  ext T
  constructor
  · rintro ⟨S, hS, rfl⟩
    rcases hS with ⟨f, rfl⟩ | ⟨k, rfl⟩
    · exact Or.inl ⟨_, (crossedHaarHilbertEquiv_multiplier_conj e f).symm⟩
    · exact Or.inr ⟨k, (crossedHaarHilbertEquiv_group_conj e k).symm⟩
  · rintro (⟨f, rfl⟩ | ⟨k, rfl⟩)
    · let g : crossedCoefficient X :=
        Lp.compMeasurePreserving e.toMeasurableEquiv
          e.measure_preserving f
      refine ⟨crossedMultiplier X g, Or.inl ⟨g, rfl⟩, ?_⟩
      rw [crossedHaarHilbertEquiv_multiplier_conj]
      congr 1
      exact crossedCoefficient_pullback_symm_apply e f
    · exact ⟨(crossedGroupUnitary X k).toContinuousLinearEquiv.toContinuousLinearMap,
        Or.inr ⟨k, rfl⟩,
        crossedHaarHilbertEquiv_group_conj e k⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem crossedHaarHilbertEquiv_mem_algebra_iff
    {X : HaarProbabilityAction Γ Ω}
    {Y : HaarProbabilityAction Γ Ξ}
    (e : EquivariantHaarEquiv X Y)
    (T : crossedHilbert X →L[ℂ] crossedHilbert X) :
    T ∈ (crossedProductModel X).algebra ↔
      (crossedHaarHilbertEquiv e).conjStarAlgEquiv T ∈
        (crossedProductModel Y).algebra := by
  change
    T ∈ vonNeumannClosure (crossedGeneratorSet X) ↔
      (crossedHaarHilbertEquiv e).conjStarAlgEquiv T ∈
        vonNeumannClosure (crossedGeneratorSet Y)
  rw [← crossedGeneratorSet_image e]
  exact (conj_mem_vonNeumannClosure_image_iff
    (crossedHaarHilbertEquiv e) (crossedGeneratorSet X) T).symm

end

end

section

namespace DetectionGap

open scoped BigOperators

open ConnesRigidity.FeedbackBooleanPolynomial

variable {α ι ζ : Type*}

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem nonprimitive_card
    [DecidableEq α]
    (ambient primitive : Finset α) (k : ℕ)
    (hprimitive_subset : primitive ⊆ ambient)
    (hambient : ambient.card = 8 * k)
    (hprimitive : primitive.card = 7 * k + 1) :
    (ambient \ primitive).card + 1 = k := by
  have hpartition :=
    Finset.card_sdiff_add_card_eq_card hprimitive_subset
  omega

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem primitive_detecting_card
    [DecidableEq α]
    (ambient primitive detecting : Finset α) (k : ℕ)
    (hprimitive_subset : primitive ⊆ ambient)
    (hdetecting_subset : detecting ⊆ ambient)
    (hambient : ambient.card = 8 * k)
    (hprimitive : primitive.card = 7 * k + 1)
    (hquarter : ambient.card ≤ 4 * detecting.card) :
    k + 1 ≤ (detecting ∩ primitive).card := by
  have hnonprimitive :=
    nonprimitive_card ambient primitive k
      hprimitive_subset hambient hprimitive
  have haway_subset : detecting \ primitive ⊆ ambient \ primitive := by
    intro x hx
    exact Finset.mem_sdiff.mpr
      ⟨hdetecting_subset (Finset.mem_sdiff.mp hx).1,
        (Finset.mem_sdiff.mp hx).2⟩
  have haway_card := Finset.card_le_card haway_subset
  have hdetecting_partition :=
    Finset.card_sdiff_add_card_inter detecting primitive
  omega

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem primitive_detecting_seventh
    [DecidableEq α]
    (ambient primitive detecting : Finset α) (k : ℕ)
    (hprimitive_subset : primitive ⊆ ambient)
    (hdetecting_subset : detecting ⊆ ambient)
    (hambient : ambient.card = 8 * k)
    (hprimitive : primitive.card = 7 * k + 1)
    (hquarter : ambient.card ≤ 4 * detecting.card) :
    primitive.card ≤ 7 * (detecting ∩ primitive).card := by
  have hexact := primitive_detecting_card ambient primitive detecting k
    hprimitive_subset hdetecting_subset hambient hprimitive hquarter
  omega

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem cube_card_eq_eight_mul_scale
    (N : ℕ) (hN : 0 < N) :
    2 ^ (4 * N) = 8 * 2 ^ (4 * N - 3) := by
  have hexponent : 4 * N = (4 * N - 3) + 3 := by omega
  rw [hexponent, pow_add]
  norm_num
  omega

end DetectionGap

end

section

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
local instance sourceDiscreteTopology : TopologicalSpace D := ⊥

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
local instance sourceDiscrete : DiscreteTopology D := ⟨rfl⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
noncomputable def binaryRootEquiv : F ≃ rootsOfUnity 2 Circle :=
  Equiv.ofBijective (ZMod.rootsOfUnityAddChar 2)
    (bijective_rootsOfUnityAddChar 2)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
noncomputable def circleBit (z : Circle) (hz : z ^ 2 = 1) : F :=
  binaryRootEquiv.symm (rootsOfUnity.mkOfPowEq z hz)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem circleBit_spec (z : Circle) (hz : z ^ 2 = 1) :
    ZMod.toCircle (circleBit z hz) = z := by
  have h := binaryRootEquiv.apply_symm_apply (rootsOfUnity.mkOfPowEq z hz)
  have h' := congrArg (fun w : rootsOfUnity 2 Circle => (w.val : Circle)) h
  exact h'

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem dualCharacter_square (χ : DiscreteCharacterSpace D) (d : D) :
    χ (Multiplicative.ofAdd d) ^ 2 = 1 := by
  rw [← map_pow, pow_two]
  change χ (Multiplicative.ofAdd (d + d)) = 1
  rw [D_add_self]
  exact map_one χ

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
noncomputable def characterBit
    (χ : DiscreteCharacterSpace D) (d : D) : F :=
  circleBit (χ (Multiplicative.ofAdd d)) (dualCharacter_square χ d)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem characterBit_spec (χ : DiscreteCharacterSpace D) (d : D) :
    ZMod.toCircle (characterBit χ d) = χ (Multiplicative.ofAdd d) :=
  circleBit_spec _ _

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem characterBit_zero (χ : DiscreteCharacterSpace D) :
    characterBit χ 0 = 0 := by
  apply ZMod.injective_toCircle
  rw [characterBit_spec]
  simp only [ofAdd_zero, map_one, AddChar.map_zero_eq_one]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem characterBit_add (χ : DiscreteCharacterSpace D) (d₁ d₂ : D) :
    characterBit χ (d₁ + d₂) = characterBit χ d₁ + characterBit χ d₂ := by
  apply ZMod.injective_toCircle
  calc
    ZMod.toCircle (characterBit χ (d₁ + d₂)) =
        χ (Multiplicative.ofAdd (d₁ + d₂)) := characterBit_spec χ _
    _ = χ (Multiplicative.ofAdd d₁) * χ (Multiplicative.ofAdd d₂) :=
      map_mul χ _ _
    _ = ZMod.toCircle (characterBit χ d₁) *
        ZMod.toCircle (characterBit χ d₂) := by
      rw [characterBit_spec, characterBit_spec]
    _ = ZMod.toCircle (characterBit χ d₁ + characterBit χ d₂) :=
      (ZMod.toCircle.map_add_eq_mul _ _).symm

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
noncomputable def characterBitLinear (χ : DiscreteCharacterSpace D) : D →ₗ[F] F where
  toFun := characterBit χ
  map_add' := characterBit_add χ
  map_smul' a d := by
    have ha : a = 0 ∨ a = 1 := by
      fin_cases a
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases ha with rfl | rfl <;> simp



/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
noncomputable def dualToPair (χ : DiscreteCharacterSpace D) : X × Y :=
  ((characterBitLinear χ).comp (LinearMap.inl F V B),
    (characterBitLinear χ).comp (LinearMap.inr F V B))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
public
theorem dualToPair_linear_apply
    (χ : DiscreteCharacterSpace D) (v : V) :
    (dualToPair χ).1 v = characterBit χ (v, 0) := rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
public
theorem dualToPair_quadratic_apply
    (χ : DiscreteCharacterSpace D) (b : B) :
    (dualToPair χ).2 b = characterBit χ (0, b) := rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
noncomputable def pairToDual (z : X × Y) : DiscreteCharacterSpace D where
  toFun d := ZMod.toCircle
    (z.1 (Multiplicative.toAdd d).1 + z.2 (Multiplicative.toAdd d).2)
  map_one' := by simp only [toAdd_one, Prod.fst_zero, map_zero, Prod.snd_zero, add_zero,
                   AddChar.map_zero_eq_one]
  map_mul' d₁ d₂ := by
    change ZMod.toCircle
      (z.1 ((Multiplicative.toAdd d₁).1 + (Multiplicative.toAdd d₂).1) +
       z.2 ((Multiplicative.toAdd d₁).2 + (Multiplicative.toAdd d₂).2)) = _
    rw [← ZMod.toCircle.map_add_eq_mul]
    congr 1
    simp only [map_add]
    abel
  continuous_toFun := continuous_of_discreteTopology



/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem pairToDual_linear_eq_one_iff (z : X × Y) (v : V) :
    pairToDual z (Multiplicative.ofAdd (v, 0)) = 1 ↔ z.1 v = 0 := by
  change ZMod.toCircle (z.1 v + z.2 0) = 1 ↔ z.1 v = 0
  simp only [map_zero, add_zero]
  constructor
  · intro h
    apply ZMod.injective_toCircle
    simpa only [AddChar.map_zero_eq_one] using h
  · intro h
    rw [h]
    exact ZMod.toCircle.map_zero_eq_one

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem pairToDual_quadratic_eq_one_iff (z : X × Y) (b : B) :
    pairToDual z (Multiplicative.ofAdd (0, b)) = 1 ↔ z.2 b = 0 := by
  change ZMod.toCircle (z.1 0 + z.2 b) = 1 ↔ z.2 b = 0
  simp only [map_zero, zero_add]
  constructor
  · intro h
    apply ZMod.injective_toCircle
    simpa only [AddChar.map_zero_eq_one] using h
  · intro h
    rw [h]
    exact ZMod.toCircle.map_zero_eq_one

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem pairToDual_linear_ne_one_iff (z : X × Y) (v : V) :
    pairToDual z (Multiplicative.ofAdd (v, 0)) ≠ 1 ↔ z.1 v ≠ 0 :=
  not_congr (pairToDual_linear_eq_one_iff z v)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem pairToDual_quadratic_ne_one_iff (z : X × Y) (b : B) :
    pairToDual z (Multiplicative.ofAdd (0, b)) ≠ 1 ↔ z.2 b ≠ 0 :=
  not_congr (pairToDual_quadratic_eq_one_iff z b)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
public
theorem dualToPair_pairToDual (z : X × Y) :
    dualToPair (pairToDual z) = z := by
  apply Prod.ext
  · apply LinearMap.ext
    intro v
    apply ZMod.injective_toCircle
    change ZMod.toCircle (characterBit (pairToDual z) (v, 0)) =
      ZMod.toCircle (z.1 v)
    rw [characterBit_spec]
    change ZMod.toCircle (z.1 v + z.2 0) = ZMod.toCircle (z.1 v)
    simp only [map_zero, add_zero]
  · apply LinearMap.ext
    intro b
    apply ZMod.injective_toCircle
    change ZMod.toCircle (characterBit (pairToDual z) (0, b)) =
      ZMod.toCircle (z.2 b)
    rw [characterBit_spec]
    change ZMod.toCircle (z.1 0 + z.2 b) = ZMod.toCircle (z.2 b)
    simp only [map_zero, zero_add]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
public
theorem pairToDual_dualToPair (χ : DiscreteCharacterSpace D) :
    pairToDual (dualToPair χ) = χ := by
  apply PontryaginDual.ext
  rintro ⟨v, b⟩
  change ZMod.toCircle
    (characterBit χ (v, 0) + characterBit χ (0, b)) =
      χ (Multiplicative.ofAdd (v, b))
  rw [ZMod.toCircle.map_add_eq_mul, characterBit_spec, characterBit_spec]
  have hproduct :
      Multiplicative.ofAdd (v, (0 : B)) *
        Multiplicative.ofAdd ((0 : V), b) =
          Multiplicative.ofAdd (v, b) := by
    apply Multiplicative.toAdd.injective
    change (v, (0 : B)) + ((0 : V), b) = (v, b)
    simp only [Prod.mk_add_mk, add_zero, zero_add]
  calc
    χ (Multiplicative.ofAdd (v, (0 : B))) *
        χ (Multiplicative.ofAdd ((0 : V), b)) =
          χ (Multiplicative.ofAdd (v, (0 : B)) *
            Multiplicative.ofAdd ((0 : V), b)) := (map_mul χ _ _).symm
    _ = χ (Multiplicative.ofAdd (v, b)) := congrArg χ hproduct

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
noncomputable def pairDualEquiv : X × Y ≃ DiscreteCharacterSpace D where
  toFun := pairToDual
  invFun := dualToPair
  left_inv := dualToPair_pairToDual
  right_inv := pairToDual_dualToPair

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem pairToDual_continuous : Continuous pairToDual := by
  change Continuous
    (fun z : X × Y ↦ (pairToDual z : ((Multiplicative D) →ₜ* Circle)))
  apply ContinuousMonoidHom.continuous_of_continuous_uncurry
  apply continuous_prod_of_discrete_right.mpr
  intro d
  change Continuous (fun z : X × Y ↦
    ZMod.toCircle
      (z.1 (Multiplicative.toAdd d).1 + z.2 (Multiplicative.toAdd d).2))
  exact
    (continuous_of_discreteTopology : Continuous (fun a : F ↦ ZMod.toCircle a)).comp
      (((continuous_X_eval (Multiplicative.toAdd d).1).comp continuous_fst).add
        ((continuous_Y_eval (Multiplicative.toAdd d).2).comp continuous_snd))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
noncomputable def pairDualHomeomorph : X × Y ≃ₜ DiscreteCharacterSpace D :=
  pairToDual_continuous.homeoOfEquivCompactToT2 (f := pairDualEquiv)





/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
noncomputable def dualPairAction (k : K) (z : X × Y) : X × Y :=
  (z.1.comp (kLinear k⁻¹).toLinearMap,
    z.2.comp (kDividedSquareLinear k⁻¹).toLinearMap)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
noncomputable def moduleAddAction :
    actingGroup →* Multiplicative (AddAut D) :=
  (MulAutMultiplicative D).toMonoidHom.comp kDAction

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem pairDualHomeomorph_equivariant (k : K) (z : X × Y) :
    pairDualHomeomorph (dualPairAction k z) =
      dualCharacterAction (A := D) (H := actingGroup)
        moduleAddAction k (pairDualHomeomorph z) := by
  apply PontryaginDual.ext
  intro d
  rfl

end

section

namespace ElementaryGenerationProof

open Matrix
open scoped BigOperators

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private abbrev elementarySubgroup : Subgroup Q :=
  Subgroup.closure elementaryTransvections

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem transvection_mem (i j : Index) (h : i ≠ j) (c : R) :
    Matrix.SpecialLinearGroup.transvection h c ∈ elementarySubgroup :=
  Subgroup.subset_closure ⟨i, j, h, c, rfl⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem transvection_smul_same (i j : Index) (h : i ≠ j) (c : R)
    (v : V) :
    (Matrix.SpecialLinearGroup.transvection h c • v) i = v i + c * v j := by
  change ((Matrix.SpecialLinearGroup.transvection h c).val *ᵥ v) i = _
  rw [Matrix.SpecialLinearGroup.transvection_coe, Matrix.add_mulVec,
      Matrix.one_mulVec, Matrix.single_mulVec]
  simp only [Pi.add_apply, Function.update_self]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem transvection_smul_other (i j k : Index) (h : i ≠ j)
    (hk : k ≠ i) (c : R) (v : V) :
    (Matrix.SpecialLinearGroup.transvection h c • v) k = v k := by
  change ((Matrix.SpecialLinearGroup.transvection h c).val *ᵥ v) k = _
  rw [Matrix.SpecialLinearGroup.transvection_coe, Matrix.add_mulVec,
      Matrix.one_mulVec, Matrix.single_mulVec]
  simp only [Pi.add_apply, ne_eq, hk, not_false_eq_true, Function.update_of_ne, Pi.zero_apply,
    add_zero]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def coordinateSwap (i j : Index) (h : i ≠ j) : Q :=
  Matrix.SpecialLinearGroup.transvection h 1 *
    Matrix.SpecialLinearGroup.transvection h.symm 1 *
    Matrix.SpecialLinearGroup.transvection h 1

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem coordinateSwap_mem (i j : Index) (h : i ≠ j) :
    coordinateSwap i j h ∈ elementarySubgroup :=
  elementarySubgroup.mul_mem
    (elementarySubgroup.mul_mem (transvection_mem i j h 1)
      (transvection_mem j i h.symm 1))
    (transvection_mem i j h 1)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem coordinateSwap_smul_left (i j : Index) (h : i ≠ j) (v : V) :
    (coordinateSwap i j h • v) i = v j := by
  simp only [coordinateSwap, mul_smul]
  rw [transvection_smul_same]
  rw [transvection_smul_other j i i h.symm h]
  rw [transvection_smul_same j i]
  rw [transvection_smul_same i j]
  rw [transvection_smul_other i j j h h.symm]
  simp only [one_mul]
  calc
    v i + v j + (v j + (v i + v j)) =
      (v i + v i) + (v j + v j) + v j := by ac_rfl
    _ = v j := by simp only [CharTwo.add_self_eq_zero, zero_add]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem coordinateSwap_smul_right (i j : Index) (h : i ≠ j) (v : V) :
    (coordinateSwap i j h • v) j = v i := by
  simp only [coordinateSwap, mul_smul]
  rw [transvection_smul_other i j j h h.symm]
  rw [transvection_smul_same j i]
  rw [transvection_smul_same i j]
  rw [transvection_smul_other i j j h h.symm]
  simp only [one_mul]
  calc
    v j + (v i + v j) = (v j + v j) + v i := by ac_rfl
    _ = v i := by simp only [CharTwo.add_self_eq_zero, zero_add]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem coordinateSwap_smul_other (i j k : Index) (h : i ≠ j)
    (hki : k ≠ i) (hkj : k ≠ j) (v : V) :
    (coordinateSwap i j h • v) k = v k := by
  simp only [coordinateSwap, mul_smul]
  rw [transvection_smul_other i j k h hki]
  rw [transvection_smul_other j i k h.symm hkj]
  rw [transvection_smul_other i j k h hki]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def euclideanStep (i j : Index) (h : i ≠ j) (a b : R) : Q :=
  coordinateSwap i j h *
    Matrix.SpecialLinearGroup.transvection h.symm (b / a)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem euclideanStep_mem (i j : Index) (h : i ≠ j) (a b : R) :
    euclideanStep i j h a b ∈ elementarySubgroup :=
  elementarySubgroup.mul_mem (coordinateSwap_mem i j h)
    (transvection_mem j i h.symm (b / a))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem euclideanStep_smul_left (i j : Index) (h : i ≠ j) (v : V) :
    (euclideanStep i j h (v i) (v j) • v) i = v j % v i := by
  rw [euclideanStep, mul_smul, coordinateSwap_smul_left,
    transvection_smul_same]
  have hd := EuclideanDomain.div_add_mod (v j) (v i)
  calc
    v j + (v j / v i) * v i =
        (v i * (v j / v i) + v j % v i) + (v j / v i) * v i := by rw [hd]
    _ = (v i * (v j / v i) + v i * (v j / v i)) + v j % v i := by ac_rfl
    _ = v j % v i := by simp only [CharTwo.add_self_eq_zero, zero_add]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem euclideanStep_smul_right (i j : Index) (h : i ≠ j) (v : V) :
    (euclideanStep i j h (v i) (v j) • v) j = v i := by
  rw [euclideanStep, mul_smul, coordinateSwap_smul_right,
    transvection_smul_other _ _ _ h.symm h]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem euclideanStep_smul_other (i j k : Index) (h : i ≠ j)
    (hki : k ≠ i) (hkj : k ≠ j) (v : V) :
    (euclideanStep i j h (v i) (v j) • v) k = v k := by
  rw [euclideanStep, mul_smul,
    coordinateSwap_smul_other i j k h hki hkj,
    transvection_smul_other _ _ _ h.symm hkj]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem pair_reduce (i j : Index) (h : i ≠ j) (v : V) :
    ∃ g : Q, g ∈ elementarySubgroup ∧
      (g • v) i = EuclideanDomain.gcd (v i) (v j) ∧
      (g • v) j = 0 ∧
      ∀ k : Index, k ≠ i → k ≠ j → (g • v) k = v k := by
  let P : R → R → Prop := fun a b =>
    ∀ w : V, w i = a → w j = b →
      ∃ g : Q, g ∈ elementarySubgroup ∧
        (g • w) i = EuclideanDomain.gcd a b ∧
        (g • w) j = 0 ∧
        ∀ k : Index, k ≠ i → k ≠ j → (g • w) k = w k
  have hp : P (v i) (v j) := by
    apply EuclideanDomain.GCD.induction (P := P) (v i) (v j)
    · intro b w hwi hwj
      refine ⟨coordinateSwap i j h, coordinateSwap_mem i j h, ?_, ?_, ?_⟩
      · rw [coordinateSwap_smul_left, hwj, EuclideanDomain.gcd_zero_left]
      · rw [coordinateSwap_smul_right, hwi]
      · intro k hki hkj
        exact coordinateSwap_smul_other i j k h hki hkj w
    · intro a b _ ih w hwi hwj
      let s : Q := euclideanStep i j h a b
      have hs : s ∈ elementarySubgroup := euclideanStep_mem i j h a b
      have hsi : (s • w) i = b % a := by
        dsimp [s]
        subst a
        subst b
        exact euclideanStep_smul_left i j h w
      have hsj : (s • w) j = a := by
        dsimp [s]
        subst a
        subst b
        exact euclideanStep_smul_right i j h w
      obtain ⟨g, hg, hgi, hgj, hgother⟩ := ih (s • w) hsi hsj
      refine ⟨g * s, elementarySubgroup.mul_mem hg hs, ?_, ?_, ?_⟩
      · rw [mul_smul, hgi, EuclideanDomain.gcd_val a b]
      · rw [mul_smul, hgj]
      · intro k hki hkj
        rw [mul_smul, hgother k hki hkj]
        dsimp [s]
        subst a
        subst b
        exact euclideanStep_smul_other i j k h hki hkj w
  exact hp v rfl rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem binaryPolynomial_eq_one_of_isUnit (p : R) (hp : IsUnit p) :
    p = 1 := by
  obtain ⟨a, ha, hpa⟩ := Polynomial.isUnit_iff.mp hp
  have ha' : a = 1 :=
    FeedbackBooleanPolynomial.eq_one_of_ne_zero_zmod_two a ha.ne_zero
  simpa only [ha', map_one] using hpa.symm

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem matrix_mul_apply_as_smul (g A : Q) (i j : Index) :
    (g * A) i j = (g • (fun k : Index => A k j)) i := by
  rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem first_column_reduce (A : Q) :
    ∃ g : Q, g ∈ elementarySubgroup ∧
      (g * A) 0 0 = 1 ∧
      (g * A) 1 0 = 0 ∧
      (g * A) 2 0 = 0 ∧
      (g * A) 3 0 = 0 := by
  let v : V := fun i => A i 0
  obtain ⟨g₁, hg₁, _, hg₁1, hg₁other⟩ :=
    pair_reduce (0 : Index) 1 (by decide) v
  obtain ⟨g₂, hg₂, _, hg₂2, hg₂other⟩ :=
    pair_reduce (0 : Index) 2 (by decide) (g₁ • v)
  obtain ⟨g₃, hg₃, _, hg₃3, hg₃other⟩ :=
    pair_reduce (0 : Index) 3 (by decide) (g₂ • (g₁ • v))
  let g := g₃ * g₂ * g₁
  have hg : g ∈ elementarySubgroup :=
    elementarySubgroup.mul_mem (elementarySubgroup.mul_mem hg₃ hg₂) hg₁
  have h1 : (g • v) (1 : Index) = 0 := by
    dsimp [g]
    rw [mul_smul, mul_smul,
      hg₃other 1 (by decide) (by decide),
      hg₂other 1 (by decide) (by decide), hg₁1]
  have h2 : (g • v) (2 : Index) = 0 := by
    dsimp [g]
    rw [mul_smul, mul_smul,
      hg₃other 2 (by decide) (by decide), hg₂2]
  have h3 : (g • v) (3 : Index) = 0 := by
    dsimp [g]
    rw [mul_smul, mul_smul, hg₃3]
  have hentry (i : Index) : (g * A) i 0 = (g • v) i :=
    matrix_mul_apply_as_smul g A i 0
  have hz1 : (g * A) (1 : Index) 0 = 0 := (hentry 1).trans h1
  have hz2 : (g * A) (2 : Index) 0 = 0 := (hentry 2).trans h2
  have hz3 : (g * A) (3 : Index) 0 = 0 := (hentry 3).trans h3
  have hdet : ((g * A : Q).val).det = 1 := (g * A).property
  rw [Matrix.det_succ_column_zero] at hdet
  change ((g.val * A.val) 1 0) = 0 at hz1
  change ((g.val * A.val) 2 0) = 0 at hz2
  change ((g.val * A.val) 3 0) = 0 at hz3
  have hproduct :
      (g * A) 0 0 *
          (((g * A : Q).val).submatrix Fin.succ Fin.succ).det = 1 := by
    simpa only [Fin.isValue, Matrix.SpecialLinearGroup.coe_mul, Nat.succ_eq_add_one, Nat.reduceAdd,
      Fin.sum_univ_succ, Fin.coe_ofNat_eq_mod, Nat.zero_mod, pow_zero, one_mul, Fin.succAbove_zero,
      Fin.val_succ, zero_add, pow_one, Fin.succ_zero_eq_one, hz1, mul_zero, zero_mul, even_two,
      Even.neg_pow, one_pow, Fin.succ_one_eq_two, hz2, Finset.univ_unique, Fin.default_eq_zero,
      Fin.val_eq_zero, Finset.sum_singleton, Fin.reduceSucc, hz3, add_zero] using hdet
  have hunit : IsUnit ((g * A) 0 0) :=
    IsUnit.of_mul_eq_one _ hproduct
  exact ⟨g, hg, binaryPolynomial_eq_one_of_isUnit _ hunit, hz1, hz2, hz3⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem transvection_fix_of_source_zero (i j : Index) (h : i ≠ j) (c : R)
    (w : V) (hw : w j = 0) :
    Matrix.SpecialLinearGroup.transvection h c • w = w := by
  funext k
  by_cases hk : k = i
  · subst k
    rw [transvection_smul_same i j h c w, hw]
    simp only [mul_zero, add_zero]
  · exact transvection_smul_other i j k h hk c w

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem coordinateSwap_fix_of_pair_zero (i j : Index) (h : i ≠ j) (w : V)
    (hi : w i = 0) (hj : w j = 0) :
    coordinateSwap i j h • w = w := by
  rw [coordinateSwap, mul_smul, mul_smul,
    transvection_fix_of_source_zero i j h 1 w hj,
    transvection_fix_of_source_zero j i h.symm 1 w hi,
    transvection_fix_of_source_zero i j h 1 w hj]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem euclideanStep_fix_of_pair_zero (i j : Index) (h : i ≠ j)
    (a b : R) (w : V) (hi : w i = 0) (hj : w j = 0) :
    euclideanStep i j h a b • w = w := by
  rw [euclideanStep, mul_smul,
    transvection_fix_of_source_zero j i h.symm (b / a) w hi,
    coordinateSwap_fix_of_pair_zero i j h w hi hj]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem pair_reduce_strong (i j : Index) (h : i ≠ j) (v : V) :
    ∃ g : Q, g ∈ elementarySubgroup ∧
      (g • v) i = EuclideanDomain.gcd (v i) (v j) ∧
      (g • v) j = 0 ∧
      (∀ k : Index, k ≠ i → k ≠ j → (g • v) k = v k) ∧
      (∀ w : V, w i = 0 → w j = 0 → g • w = w) := by
  let P : R → R → Prop := fun a b =>
    ∀ w : V, w i = a → w j = b →
      ∃ g : Q, g ∈ elementarySubgroup ∧
        (g • w) i = EuclideanDomain.gcd a b ∧
        (g • w) j = 0 ∧
        (∀ k : Index, k ≠ i → k ≠ j → (g • w) k = w k) ∧
        (∀ z : V, z i = 0 → z j = 0 → g • z = z)
  have hp : P (v i) (v j) := by
    apply EuclideanDomain.GCD.induction (P := P) (v i) (v j)
    · intro b w hwi hwj
      refine ⟨coordinateSwap i j h, coordinateSwap_mem i j h, ?_, ?_, ?_, ?_⟩
      · rw [coordinateSwap_smul_left, hwj, EuclideanDomain.gcd_zero_left]
      · rw [coordinateSwap_smul_right, hwi]
      · intro k hki hkj
        exact coordinateSwap_smul_other i j k h hki hkj w
      · exact coordinateSwap_fix_of_pair_zero i j h
    · intro a b _ ih w hwi hwj
      let s : Q := euclideanStep i j h a b
      have hs : s ∈ elementarySubgroup := euclideanStep_mem i j h a b
      have hsi : (s • w) i = b % a := by
        dsimp [s]
        subst a
        subst b
        exact euclideanStep_smul_left i j h w
      have hsj : (s • w) j = a := by
        dsimp [s]
        subst a
        subst b
        exact euclideanStep_smul_right i j h w
      obtain ⟨g, hg, hgi, hgj, hgother, hgfix⟩ := ih (s • w) hsi hsj
      refine ⟨g * s, elementarySubgroup.mul_mem hg hs, ?_, ?_, ?_, ?_⟩
      · rw [mul_smul, hgi, EuclideanDomain.gcd_val a b]
      · rw [mul_smul, hgj]
      · intro k hki hkj
        rw [mul_smul, hgother k hki hkj]
        dsimp [s]
        subst a
        subst b
        exact euclideanStep_smul_other i j k h hki hkj w
      · intro z hzi hzj
        rw [mul_smul]
        have hsz : s • z = z :=
          euclideanStep_fix_of_pair_zero i j h a b z hzi hzj
        rw [hsz, hgfix z hzi hzj]
  exact hp v rfl rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem second_column_reduce (A : Q)
    (h₁₀ : A (1 : Index) 0 = 0)
    (h₂₀ : A (2 : Index) 0 = 0)
    (h₃₀ : A (3 : Index) 0 = 0) :
    ∃ p : Q, p ∈ elementarySubgroup ∧
      (p * A) 1 0 = 0 ∧
      (p * A) 2 0 = 0 ∧
      (p * A) 3 0 = 0 ∧
      (p * A) 2 1 = 0 ∧
      (p * A) 3 1 = 0 := by
  let v₁ : V := fun k => A k 1
  obtain ⟨p₁₂, hp₁₂, _, hz₂₁, _, hfix₁₂⟩ :=
    pair_reduce_strong (1 : Index) 2 (by decide) v₁
  obtain ⟨p₁₃, hp₁₃, _, hz₃₁, hother₁₃, hfix₁₃⟩ :=
    pair_reduce_strong (1 : Index) 3 (by decide) (p₁₂ • v₁)
  let p : Q := p₁₃ * p₁₂
  have hp : p ∈ elementarySubgroup :=
    elementarySubgroup.mul_mem hp₁₃ hp₁₂
  have h21 : (p * A) (2 : Index) 1 = 0 := by
    change (p • v₁) (2 : Index) = 0
    dsimp [p]
    rw [mul_smul, hother₁₃ 2 (by decide) (by decide), hz₂₁]
  have h31 : (p * A) (3 : Index) 1 = 0 := by
    change (p • v₁) (3 : Index) = 0
    dsimp [p]
    rw [mul_smul, hz₃₁]
  let v₀ : V := fun k => A k 0
  have hv₀1 : v₀ (1 : Index) = 0 := h₁₀
  have hv₀2 : v₀ (2 : Index) = 0 := h₂₀
  have hv₀3 : v₀ (3 : Index) = 0 := h₃₀
  have hfix₀ : p • v₀ = v₀ := by
    dsimp [p]
    rw [mul_smul, hfix₁₂ v₀ hv₀1 hv₀2, hfix₁₃ v₀ hv₀1 hv₀3]
  have h10 : (p * A) (1 : Index) 0 = 0 := by
    change (p • v₀) (1 : Index) = 0
    rw [hfix₀]
    exact h₁₀
  have h20 : (p * A) (2 : Index) 0 = 0 := by
    change (p • v₀) (2 : Index) = 0
    rw [hfix₀]
    exact h₂₀
  have h30 : (p * A) (3 : Index) 0 = 0 := by
    change (p • v₀) (3 : Index) = 0
    rw [hfix₀]
    exact h₃₀
  exact ⟨p, hp, h10, h20, h30, h21, h31⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem third_column_reduce (A : Q)
    (h10 : A 1 0 = 0) (h20 : A 2 0 = 0) (h30 : A 3 0 = 0)
    (h21 : A 2 1 = 0) (h31 : A 3 1 = 0) :
    ∃ p : Q, p ∈ elementarySubgroup ∧
      (p * A) 1 0 = 0 ∧ (p * A) 2 0 = 0 ∧ (p * A) 3 0 = 0 ∧
      (p * A) 2 1 = 0 ∧ (p * A) 3 1 = 0 ∧ (p * A) 3 2 = 0 := by
  let v₂ : V := fun k => A k 2
  obtain ⟨p, hp, _, hz32, _, hfix⟩ :=
    pair_reduce_strong (2 : Index) 3 (by decide) v₂
  let col₀ : V := fun k => A k 0
  let col₁ : V := fun k => A k 1
  have hfix₀ : p • col₀ = col₀ := hfix col₀ h20 h30
  have hfix₁ : p • col₁ = col₁ := hfix col₁ h21 h31
  refine ⟨p, hp, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change (p • col₀) (1 : Index) = 0
    rw [hfix₀]
    exact h10
  · change (p • col₀) (2 : Index) = 0
    rw [hfix₀]
    exact h20
  · change (p • col₀) (3 : Index) = 0
    rw [hfix₀]
    exact h30
  · change (p • col₁) (2 : Index) = 0
    rw [hfix₁]
    exact h21
  · change (p • col₁) (3 : Index) = 0
    rw [hfix₁]
    exact h31
  · exact hz32

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem fin_four_upperTriangular_of_six (A : Q)
    (h10 : A (1 : Index) 0 = 0)
    (h20 : A (2 : Index) 0 = 0)
    (h30 : A (3 : Index) 0 = 0)
    (h21 : A (2 : Index) 1 = 0)
    (h31 : A (3 : Index) 1 = 0)
    (h32 : A (3 : Index) 2 = 0) :
    ∀ i j : Index, j < i → A i j = 0 := by
  intro i j hji
  have hval : j.val < i.val := hji
  fin_cases i
  · change j.val < 0 at hval
    omega
  · change j.val < 1 at hval
    have hj : j = 0 := Fin.ext (by omega)
    simpa only [Nat.reduceAdd, Fin.mk_one, Fin.isValue, hj] using h10
  · change j.val < 2 at hval
    have hj : j = 0 ∨ j = 1 := by
      by_cases hzero : j.val = 0
      · exact Or.inl (Fin.ext hzero)
      · exact Or.inr (Fin.ext (by omega))
    rcases hj with rfl | rfl
    · exact h20
    · exact h21
  · change j.val < 3 at hval
    have hj : j = 0 ∨ j = 1 ∨ j = 2 := by
      by_cases hzero : j.val = 0
      · exact Or.inl (Fin.ext hzero)
      · by_cases hone : j.val = 1
        · exact Or.inr (Or.inl (Fin.ext hone))
        · exact Or.inr (Or.inr (Fin.ext (by omega)))
    rcases hj with rfl | rfl | rfl
    · exact h30
    · exact h31
    · exact h32

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem upper_triangularize (A : Q) :
    ∃ g : Q, g ∈ elementarySubgroup ∧
      ∀ i j : Index, j < i → (g * A) i j = 0 := by
  obtain ⟨p₀, hp₀, _, h10, h20, h30⟩ := first_column_reduce A
  obtain ⟨p₁, hp₁, h10', h20', h30', h21, h31⟩ :=
    second_column_reduce (p₀ * A) h10 h20 h30
  obtain ⟨p₂, hp₂, h10'', h20'', h30'', h21', h31', h32⟩ :=
    third_column_reduce (p₁ * (p₀ * A)) h10' h20' h30' h21 h31
  let p : Q := p₂ * p₁ * p₀
  have hp : p ∈ elementarySubgroup :=
    elementarySubgroup.mul_mem
      (elementarySubgroup.mul_mem hp₂ hp₁) hp₀
  have hprod : p * A = p₂ * (p₁ * (p₀ * A)) := by
    simp only [mul_assoc, p]
  refine ⟨p, hp, ?_⟩
  rw [hprod]
  exact fin_four_upperTriangular_of_six _
    h10'' h20'' h30'' h21' h31' h32

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem upperTriangular_diag_one (g : Q)
    (htri : ∀ i j : Index, j < i → g i j = 0) (i : Index) :
    g i i = 1 := by
  have hblock : (g : Matrix Index Index R).BlockTriangular id := by
    intro k l hkl
    exact htri k l hkl
  have hprod : (∏ j : Index, g j j) = 1 := by
    calc
      (∏ j : Index, g j j) = (g : Matrix Index Index R).det :=
        (Matrix.det_of_isUpperTriangular hblock).symm
      _ = 1 := g.property
  have hdvd : g i i ∣ (∏ j : Index, g j j) :=
    Finset.dvd_prod_of_mem (fun j : Index => g j j) (Finset.mem_univ i)
  rw [hprod] at hdvd
  exact binaryPolynomial_eq_one_of_isUnit _ (isUnit_of_dvd_one hdvd)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem upperUnitriangular_factorization (g : Q)
    (hu : ∀ i j : Index, j < i → g i j = 0)
    (hd : ∀ i : Index, g i i = 1) :
    g =
      Matrix.SpecialLinearGroup.transvection (show (2 : Index) ≠ 3 by decide)
        (g 2 3) *
      Matrix.SpecialLinearGroup.transvection (show (1 : Index) ≠ 3 by decide)
        (g 1 3) *
      Matrix.SpecialLinearGroup.transvection (show (1 : Index) ≠ 2 by decide)
        (g 1 2) *
      Matrix.SpecialLinearGroup.transvection (show (0 : Index) ≠ 3 by decide)
        (g 0 3) *
      Matrix.SpecialLinearGroup.transvection (show (0 : Index) ≠ 2 by decide)
        (g 0 2) *
      Matrix.SpecialLinearGroup.transvection (show (0 : Index) ≠ 1 by decide)
        (g 0 1) := by
  have h00 := hd 0
  have h11 := hd 1
  have h22 := hd 2
  have h33 := hd 3
  have h10 := hu 1 0 (by decide)
  have h20 := hu 2 0 (by decide)
  have h21 := hu 2 1 (by decide)
  have h30 := hu 3 0 (by decide)
  have h31 := hu 3 1 (by decide)
  have h32 := hu 3 2 (by decide)
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [Nat.reduceAdd, Fin.zero_eta, Fin.isValue, Fin.mk_one,
      Fin.reduceFinMk, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.transvection_coe, Matrix.mul_apply,
      Matrix.add_apply, Matrix.one_apply, Fin.reduceEq, false_and,
      not_false_eq_true, Matrix.single_apply_of_ne, add_zero,
      Matrix.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, ↓reduceIte, one_ne_zero, true_and,
      Fin.sum_univ_four, zero_ne_one, mul_ite, mul_one, mul_zero,
      ite_self, zero_add, and_false, Finset.sum_ite_eq', and_true,
      h00, h11, h22, h33, h10, h20, h21, h30, h31, h32]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem upperUnitriangular_mem (g : Q)
    (hu : ∀ i j : Index, j < i → g i j = 0)
    (hd : ∀ i : Index, g i i = 1) :
    g ∈ elementarySubgroup := by
  rw [upperUnitriangular_factorization g hu hd]
  exact elementarySubgroup.mul_mem
    (elementarySubgroup.mul_mem
      (elementarySubgroup.mul_mem
        (elementarySubgroup.mul_mem
          (elementarySubgroup.mul_mem
            (transvection_mem 2 3 (by decide) (g 2 3))
            (transvection_mem 1 3 (by decide) (g 1 3)))
          (transvection_mem 1 2 (by decide) (g 1 2)))
        (transvection_mem 0 3 (by decide) (g 0 3)))
      (transvection_mem 0 2 (by decide) (g 0 2)))
    (transvection_mem 0 1 (by decide) (g 0 1))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem elementarySubgroup_eq_top : elementarySubgroup = ⊤ := by
  apply top_unique
  intro A _
  obtain ⟨p, hp, hupper⟩ := upper_triangularize A
  have hunit : p * A ∈ elementarySubgroup :=
    upperUnitriangular_mem (p * A) hupper
      (upperTriangular_diag_one (p * A) hupper)
  have hA := elementarySubgroup.mul_mem
    (elementarySubgroup.inv_mem hp) hunit
  simpa only [inv_mul_cancel_left] using hA

end ElementaryGenerationProof

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem elementaryGeneration : ElementaryGeneration :=
  ElementaryGenerationProof.elementarySubgroup_eq_top

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem pi₂_surjective : Function.Surjective pi₂ :=
  pi₂_surjective_of_elementaryGeneration elementaryGeneration

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private instance instShiftKernelFinite (n : ℕ) : Finite (shiftKernel n) := by
  let e : shiftKernel n ≃ (Fin 4 → Fin n → F) :=
    ((shiftKernelEquivQuotient n).trans
      (shiftedQuotientCoeffEquiv n)).toEquiv
  exact Finite.of_injective e e.injective

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private instance instShiftKernelDiscreteTopology (n : ℕ) :
    DiscreteTopology (shiftKernel n) :=
  Finite.instDiscreteTopology

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def pontryaginDualEquivMonoidHom
    (A : Type*) [CommGroup A] [TopologicalSpace A] [DiscreteTopology A] :
    PontryaginDual A ≃* (A →* Circle) where
  toFun χ := χ.toMonoidHom
  invFun χ :=
    { toMonoidHom := χ
      continuous_toFun := continuous_of_discreteTopology }
  left_inv χ := by
    apply PontryaginDual.ext
    intro a
    rfl
  right_inv χ := by
    apply MonoidHom.ext
    intro a
    rfl
  map_mul' χ ψ := rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem finitePontryaginDual_card
    (A : Type*) [CommGroup A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A] :
    Nat.card (PontryaginDual A) = Nat.card A := by
  rw [Nat.card_congr (pontryaginDualEquivMonoidHom A).toEquiv]
  rw [Nat.card_congr (MonoidHom.toHomUnitsMulEquiv :
    (A →* Circle) ≃* (A →* Circleˣ)).toEquiv]
  exact CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity A Circle

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem shiftKernelPontryaginDual_card_eq_shiftKernel_card (n : ℕ) :
    Nat.card (PontryaginDual (Multiplicative (shiftKernel n))) =
      Nat.card (shiftKernel n) := by
  rw [finitePontryaginDual_card (Multiplicative (shiftKernel n))]
  change Nat.card (shiftKernel n) = Nat.card (shiftKernel n)
  rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem shiftKernelPontryaginDual_card (n : ℕ) :
    Nat.card (PontryaginDual (Multiplicative (shiftKernel n))) =
      2 ^ (4 * n) := by
  rw [shiftKernelPontryaginDual_card_eq_shiftKernel_card]
  exact shiftKernel_card n

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private abbrev ShiftKernelDual (n : ℕ) :=
  Additive (PontryaginDual (Multiplicative (shiftKernel n)))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def dualCarryPullback (n : ℕ) : E 0 →+ E n :=
  (PontryaginDual.map (carryPullbackContinuous n)).toMonoidHom.toAdditive



/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def dualCarrySection (n : ℕ) : E n →+ E 0 :=
  (PontryaginDual.map (carryPullbackSectionContinuous n)).toMonoidHom.toAdditive

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem dualCarrySection_dualCarryPullback (n : ℕ) (η : E 0) :
    dualCarrySection n (dualCarryPullback n η) = η := by
  apply Additive.toMul.injective
  apply PontryaginDual.ext
  intro z
  change Additive.toMul η
      (Multiplicative.ofAdd
        (carryPullback n (carryPullbackSection n (Multiplicative.toAdd z)))) =
    Additive.toMul η z
  rw [carryPullback_carryPullbackSection]
  rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem dualCarryPullback_injective (n : ℕ) :
    Function.Injective (dualCarryPullback n) :=
  Function.LeftInverse.injective (dualCarrySection_dualCarryPullback n)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def shiftKernelRestriction (n : ℕ) : E n →+ ShiftKernelDual n :=
  (PontryaginDual.map (shiftKernelInclusionContinuous n)).toMonoidHom.toAdditive



/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def extendShiftKernelCharacter (n : ℕ) : ShiftKernelDual n →+ E n :=
  (PontryaginDual.map (kernelProjectionContinuous n)).toMonoidHom.toAdditive

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem shiftKernelRestriction_extend (n : ℕ)
    (χ : ShiftKernelDual n) :
    shiftKernelRestriction n (extendShiftKernelCharacter n χ) = χ := by
  apply Additive.toMul.injective
  apply PontryaginDual.ext
  intro ℓ
  change Additive.toMul χ
      (Multiplicative.ofAdd
        (kernelProjection n
          (shiftKernelInclusion n (Multiplicative.toAdd ℓ)))) =
    Additive.toMul χ ℓ
  rw [kernelProjection_shiftKernelInclusion]
  rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem shiftKernelRestriction_surjective (n : ℕ) :
    Function.Surjective (shiftKernelRestriction n) :=
  Function.RightInverse.surjective (shiftKernelRestriction_extend n)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem dualCarryPullback_range_eq_shiftKernelRestriction_ker (n : ℕ) :
    (dualCarryPullback n).range = (shiftKernelRestriction n).ker := by
  ext η
  constructor
  · rintro ⟨χ, rfl⟩
    change shiftKernelRestriction n (dualCarryPullback n χ) = 0
    apply Additive.toMul.injective
    apply PontryaginDual.ext
    intro ℓ
    change Additive.toMul χ
      (Multiplicative.ofAdd (carryPullback n (shiftKernelInclusion n
        (Multiplicative.toAdd ℓ)))) = 1
    have hzero : carryPullback n
        (shiftKernelInclusion n (Multiplicative.toAdd ℓ)) = 0 := by
      apply CarryGroup.ext
      · exact (Multiplicative.toAdd ℓ).property
      · rfl
    simp only [hzero, ofAdd_zero, map_one]
  · intro hη
    refine ⟨dualCarrySection n η, ?_⟩
    apply Additive.toMul.injective
    apply PontryaginDual.ext
    intro z
    change Additive.toMul η
      (Multiplicative.ofAdd (carryPullbackSection n
        (carryPullback n (Multiplicative.toAdd z)))) =
      Additive.toMul η z
    have htrivial :
        Additive.toMul η (Multiplicative.ofAdd
          (shiftKernelInclusion n (kernelProjection n (Multiplicative.toAdd z))))
          = 1 := by
      exact DFunLike.congr_fun (congrArg Additive.toMul hη)
        (Multiplicative.ofAdd (kernelProjection n (Multiplicative.toAdd z)))
    have hsplit := (carryGroupSplitEquiv n).left_inv (Multiplicative.toAdd z)
    change carryPullbackSection n (carryPullback n
      (Multiplicative.toAdd z)) +
        shiftKernelInclusion n (kernelProjection n (Multiplicative.toAdd z)) =
        Multiplicative.toAdd z at hsplit
    calc
      Additive.toMul η
          (Multiplicative.ofAdd (carryPullbackSection n
            (carryPullback n (Multiplicative.toAdd z)))) =
          Additive.toMul η
            (Multiplicative.ofAdd (carryPullbackSection n
              (carryPullback n (Multiplicative.toAdd z)))) *
          Additive.toMul η
            (Multiplicative.ofAdd (shiftKernelInclusion n
              (kernelProjection n (Multiplicative.toAdd z)))) := by
              rw [htrivial, mul_one]
      _ = Additive.toMul η
          (Multiplicative.ofAdd (carryPullbackSection n
            (carryPullback n (Multiplicative.toAdd z)) +
            shiftKernelInclusion n
              (kernelProjection n (Multiplicative.toAdd z)))) := by
              simp only [ofAdd_add, map_mul]
      _ = Additive.toMul η z := by
              simpa only [ofAdd_add, map_mul, ofAdd_toAdd] using congrArg
                (fun w : CarryGroup n => Additive.toMul η (Multiplicative.ofAdd w))
                hsplit

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem dualCarryPullback_range_index_eq_kernelDual_card (n : ℕ) :
    (dualCarryPullback n).range.index = Nat.card (ShiftKernelDual n) := by
  rw [dualCarryPullback_range_eq_shiftKernelRestriction_ker]
  rw [AddSubgroup.index_ker]
  rw [AddMonoidHom.range_eq_top.mpr (shiftKernelRestriction_surjective n)]
  exact Nat.card_congr (Equiv.Set.univ (ShiftKernelDual n))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem shiftKernelDual_card (n : ℕ) :
    Nat.card (ShiftKernelDual n) = 2 ^ (4 * n) := by
  change Nat.card (PontryaginDual (Multiplicative (shiftKernel n))) = _
  exact shiftKernelPontryaginDual_card n

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem dualCarryPullback_range_index (n : ℕ) :
    (dualCarryPullback n).range.index = 2 ^ (4 * n) := by
  rw [dualCarryPullback_range_index_eq_kernelDual_card, shiftKernelDual_card]

section SemidirectIndex

variable {N₁ N₂ H : Type*} [Group N₁] [Group N₂] [Group H]
variable {φ₁ : H →* MulAut N₁} {φ₂ : H →* MulAut N₂}

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem semidirectMap_range_index
    (f : N₁ →* N₂)
    (hequiv : ∀ h : H,
      f.comp (φ₁ h).toMonoidHom =
        (φ₂ ((MonoidHom.id H) h)).toMonoidHom.comp f) :
    (SemidirectProduct.map f (MonoidHom.id H) hequiv).range.index =
      f.range.index := by
  let F : (N₁ ⋊[φ₁] H) →* (N₂ ⋊[φ₂] H) :=
    SemidirectProduct.map f (MonoidHom.id H) hequiv
  let j : N₂ →* (N₂ ⋊[φ₂] H) := SemidirectProduct.inl
  have hcomap : F.range.comap j = f.range := by
    ext x
    constructor
    · rintro ⟨z, hz⟩
      exact ⟨z.left, congrArg SemidirectProduct.left hz⟩
    · rintro ⟨z, hz⟩
      refine ⟨SemidirectProduct.inl z, ?_⟩
      apply SemidirectProduct.ext
      · exact hz
      · rfl
  have hrelation : ∀ x y : N₂,
      QuotientGroup.leftRel f.range x y ↔
        QuotientGroup.leftRel F.range (j x) (j y) := by
    intro x y
    rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply]
    rw [← map_inv, ← map_mul]
    change (x⁻¹ * y ∈ f.range) ↔ j (x⁻¹ * y) ∈ F.range
    rw [← hcomap]
    rfl
  let quotientMap : (N₂ ⧸ f.range) → ((N₂ ⋊[φ₂] H) ⧸ F.range) :=
    Quotient.map' j fun x y hxy => (hrelation x y).mp hxy
  have hbijective : Function.Bijective quotientMap := by
    constructor
    · simp_rw [← Quotient.eq''] at hrelation
      refine Quotient.ind' fun x => ?_
      refine Quotient.ind' fun y => ?_
      exact (hrelation x y).mpr
    · refine Quotient.ind' fun z => ?_
      refine ⟨Quotient.mk'' z.left, ?_⟩
      apply Quotient.sound'
      rw [QuotientGroup.leftRel_apply]
      refine ⟨SemidirectProduct.inr z.right, ?_⟩
      apply SemidirectProduct.ext <;> simp [F, j]
  change F.range.index = f.range.index
  exact (Nat.card_congr (Equiv.ofBijective quotientMap hbijective)).symm

end SemidirectIndex

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem carryPullback_kCarryAddAut (n : ℕ) (k : K)
    (z : CarryGroup n) :
    carryPullback n (kCarryAddAut n k z) =
      kCarryAddAut 0 k (carryPullback n z) := by
  apply CarryGroup.ext
  · exact kXLinear_shift k n z.linear
  · rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem dualCarryPullback_equivariant
    (n : ℕ) (k : K) (η : E 0) :
    dualCarryPullback n
        (Multiplicative.toAdd (kEAction 0 k (Multiplicative.ofAdd η))) =
      Multiplicative.toAdd
        (kEAction n k (Multiplicative.ofAdd (dualCarryPullback n η))) := by
  apply Additive.toMul.injective
  apply PontryaginDual.ext
  intro z
  change Additive.toMul η
      ((kCarryAction 0 k)⁻¹ (carryPullbackContinuous n z)) =
    Additive.toMul η
      (carryPullbackContinuous n ((kCarryAction n k)⁻¹ z))
  have hzero : (kCarryAction 0 k)⁻¹ = kCarryAction 0 k⁻¹ :=
    (map_inv (kCarryAction 0) k).symm
  have hn : (kCarryAction n k)⁻¹ = kCarryAction n k⁻¹ :=
    (map_inv (kCarryAction n) k).symm
  rw [hzero, hn]
  congr 1
  apply Multiplicative.toAdd.injective
  exact (carryPullback_kCarryAddAut n k⁻¹ (Multiplicative.toAdd z)).symm

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def gammaEmbedding (n : ℕ) : Gamma 0 →* Gamma n :=
  SemidirectProduct.map (dualCarryPullback n).toMultiplicative
    (MonoidHom.id K) (by
      intro k
      apply MonoidHom.ext
      intro η
      exact congrArg Multiplicative.ofAdd
        (dualCarryPullback_equivariant n k (Multiplicative.toAdd η)))





/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem gammaEmbedding_injective (n : ℕ) :
    Function.Injective (gammaEmbedding n) := by
  intro g h heq
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    apply dualCarryPullback_injective n
    exact congrArg (fun z : Gamma n => Multiplicative.toAdd z.left) heq
  · exact congrArg (fun z : Gamma n => z.right) heq

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem gammaEmbedding_range_index (n : ℕ) :
    (gammaEmbedding n).range.index = 2 ^ (4 * n) := by
  unfold gammaEmbedding
  rw [semidirectMap_range_index]
  change (dualCarryPullback n).range.index = 2 ^ (4 * n)
  exact dualCarryPullback_range_index n

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def gammaExactIndexEmbedding (n : ℕ) :
    ExactIndexEmbedding (gammaGroup 0) (gammaGroup n) (2 ^ (4 * n)) where
  hom := gammaEmbedding n
  injective := gammaEmbedding_injective n
  index_eq := gammaEmbedding_range_index n

end

section

open ConnesRigidity MeasureTheory

section

universe u v

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem additiveLeftRegularUnitary_single
    {A : Type u} [AddCommGroup A] [DecidableEq A]
    (a b : A) (c : ℂ) :
    (leftRegularUnitary (Multiplicative.ofAdd a) :
      GroupL2 (Multiplicative A) →L[ℂ] GroupL2 (Multiplicative A))
      (lp.single 2 (Multiplicative.ofAdd b) c) =
      lp.single 2 (Multiplicative.ofAdd (a + b)) c := by
  ext k
  simp only [leftRegularUnitary_apply, lp.single_apply, Pi.single_apply, inv_mul_eq_iff_eq_mul,
    ofAdd_add]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem fourierUnitary_single_smul
    {A : Type u} [DecidableEq A]
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (U : GroupL2 (Multiplicative A) ≃ₗᵢ[ℂ] H)
    (χ : A → H)
    (hU : ∀ b : A,
      U (lp.single 2 (Multiplicative.ofAdd b) 1) = χ b)
    (b : A) (c : ℂ) :
    U (lp.single 2 (Multiplicative.ofAdd b) c) = c • χ b := by
  have hs : lp.single (E := fun _ : Multiplicative A => ℂ)
      2 (Multiplicative.ofAdd b) c =
      c • lp.single (E := fun _ : Multiplicative A => ℂ)
        2 (Multiplicative.ofAdd b) (1 : ℂ) := by
    simpa only [smul_eq_mul, mul_one] using (lp.single_smul (E := fun _ : Multiplicative A => ℂ)
      2 (Multiplicative.ofAdd b) c (1 : ℂ))
  rw [hs, map_smul, hU]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem fourier_conjugates_regular_of_character_basis
    {A : Type u} [AddCommGroup A] [DecidableEq A]
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    (U : GroupL2 (Multiplicative A) ≃ₗᵢ[ℂ] H)
    (χ : A → H)
    (hU : ∀ b : A,
      U (lp.single 2 (Multiplicative.ofAdd b) 1) = χ b)
    (a : A) (T : H →L[ℂ] H)
    (hT : ∀ b : A, T (χ b) = χ (a + b)) :
    U.conjStarAlgEquiv
      (leftRegularUnitary (Multiplicative.ofAdd a) :
        GroupL2 (Multiplicative A) →L[ℂ]
          GroupL2 (Multiplicative A)) = T := by
  let F : GroupL2 (Multiplicative A) →L[ℂ] H :=
    U.toContinuousLinearEquiv.toContinuousLinearMap
  have hcomp :
      F.comp (leftRegularUnitary (Multiplicative.ofAdd a) :
        GroupL2 (Multiplicative A) →L[ℂ]
          GroupL2 (Multiplicative A)) = T.comp F := by
    apply lp.ext_continuousLinearMap (by simp only [ne_eq, ENNReal.ofNat_ne_top, not_false_eq_true])
    intro b
    apply ContinuousLinearMap.ext
    intro c
    change U
      ((leftRegularUnitary (Multiplicative.ofAdd a) :
        GroupL2 (Multiplicative A) →L[ℂ]
          GroupL2 (Multiplicative A))
        (lp.single 2 (Multiplicative.ofAdd (Multiplicative.toAdd b)) c)) =
      T (U (lp.single 2
        (Multiplicative.ofAdd (Multiplicative.toAdd b)) c))
    rw [additiveLeftRegularUnitary_single
      a (Multiplicative.toAdd b) c,
      fourierUnitary_single_smul U χ hU,
      fourierUnitary_single_smul U χ hU,
      map_smul, hT]
  apply ContinuousLinearMap.ext
  intro ξ
  obtain ⟨η, rfl⟩ := U.surjective ξ
  change U
    ((leftRegularUnitary (Multiplicative.ofAdd a) :
      GroupL2 (Multiplicative A) →L[ℂ]
        GroupL2 (Multiplicative A))
      (U.symm (U η))) = T (U η)
  rw [U.symm_apply_apply]
  exact DFunLike.congr_fun hcomp η

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem carryFourier_conjugates_regular_of_character_basis
    (n : ℕ) (η : E n)
    (T : Lp ℂ 2 (carryHaar n) →L[ℂ] Lp ℂ 2 (carryHaar n))
    (hT : ∀ θ : E n,
      T (carryCharacterL2 n θ) = carryCharacterL2 n (η + θ)) :
    (carryFourierEquiv n).conjStarAlgEquiv
      (leftRegularUnitary (Multiplicative.ofAdd η) :
        GroupL2 (Multiplicative (E n)) →L[ℂ]
          GroupL2 (Multiplicative (E n))) = T := by
  classical
  let U : GroupL2 (Multiplicative (E n)) ≃ₗᵢ[ℂ]
      Lp ℂ 2 (carryHaar n) := carryFourierEquiv n
  have hU : ∀ θ : E n,
      U (lp.single 2 (Multiplicative.ofAdd θ) 1) =
        carryCharacterL2 n θ := by
    intro θ
    exact carryFourierEquiv_single n θ
  exact fourier_conjugates_regular_of_character_basis
    (A := E n) (H := Lp ℂ 2 (carryHaar n))
    U (carryCharacterL2 n) hU η T hT

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem splitFourier_conjugates_regular_of_character_basis
    (d : D)
    (T : Lp ℂ 2 productHaar →L[ℂ] Lp ℂ 2 productHaar)
    (hT : ∀ e : D,
      T (splitCharacterL2 e) = splitCharacterL2 (d + e)) :
    splitFourierEquiv.conjStarAlgEquiv
      (leftRegularUnitary (Multiplicative.ofAdd d) :
        GroupL2 (Multiplicative D) →L[ℂ]
          GroupL2 (Multiplicative D)) = T := by
  classical
  let U : GroupL2 (Multiplicative D) ≃ₗᵢ[ℂ]
      Lp ℂ 2 productHaar := splitFourierEquiv
  have hU : ∀ e : D,
      U (lp.single 2 (Multiplicative.ofAdd e) 1) =
        splitCharacterL2 e := by
    intro e
    exact splitFourierEquiv_single e
  exact fourier_conjugates_regular_of_character_basis
    (A := D) (H := Lp ℂ 2 productHaar)
    U splitCharacterL2 hU d T hT

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem carryFourier_conjugates_normal_generator
    (n : ℕ) (η : E n) :
    (carryFourierEquiv n).conjStarAlgEquiv
      (leftRegularUnitary (Multiplicative.ofAdd η) :
        GroupL2 (Multiplicative (E n)) →L[ℂ]
          GroupL2 (Multiplicative (E n))) =
      crossedBaseMultiplier (paperCarryHaarAction n)
        (carryCharacterCoefficient n η) := by
  apply carryFourier_conjugates_regular_of_character_basis
  exact carryCharacterMultiplier_character n η

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem splitFourier_conjugates_normal_generator
    (d : D) :
    splitFourierEquiv.conjStarAlgEquiv
      (leftRegularUnitary (Multiplicative.ofAdd d) :
        GroupL2 (Multiplicative D) →L[ℂ]
          GroupL2 (Multiplicative D)) =
      crossedBaseMultiplier paperSplitHaarAction
        (splitCharacterCoefficient d) := by
  apply splitFourier_conjugates_regular_of_character_basis
  exact splitCharacterMultiplier_character d

end

end

section

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def tensorCoords : T ≃ₗ[F] Fin 4 → Fin 4 → TensorProduct F R R :=
  (TensorProduct.piLeft F V (fun _ : Fin 4 ↦ R)).trans
    (LinearEquiv.piCongrRight fun _ : Fin 4 ↦
      TensorProduct.piRight F F R (fun _ : Fin 4 ↦ R))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem tensorCoords_tmul (u v : V) (i j : Fin 4) :
    tensorCoords (u ⊗ₜ[F] v) i j = u i ⊗ₜ[F] v j := by
  change
    (TensorProduct.piRight F F R (fun _ : Fin 4 ↦ R)
      (u i ⊗ₜ[F] v)) j = u i ⊗ₜ[F] v j
  rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def blockCoefficients : TensorProduct F R R ≃ₗ[F] ℕ →₀ R :=
  TensorProduct.equivFinsuppOfBasisRight (Polynomial.basisMonomials F)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem blockCoefficients_tmul (u v : R) (n : ℕ) :
    blockCoefficients (u ⊗ₜ[F] v) n = v.coeff n • u := by
  rw [blockCoefficients,
    TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply]
  rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem exists_blockCoefficient_ne_zero {w : TensorProduct F R R} (hw : w ≠ 0) :
    ∃ n : ℕ, blockCoefficients w n ≠ 0 := by
  have h : blockCoefficients w ≠ 0 := by
    intro hzero
    apply hw
    exact blockCoefficients.injective (by simpa only [map_zero,
                                            EmbeddingLike.map_eq_zero_iff] using hzero)
  by_contra hnot
  apply h
  apply Finsupp.ext
  intro n
  by_contra hn
  exact hnot ⟨n, hn⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem blockCoefficients_map_mulLeft (f : R) (w : TensorProduct F R R)
    (n : ℕ) :
    blockCoefficients
        ((TensorProduct.map (LinearMap.mulLeft F f) LinearMap.id) w) n =
      f * blockCoefficients w n := by
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply, mul_zero]
  | tmul u v =>
      simp only [TensorProduct.map_tmul, LinearMap.mulLeft_apply, LinearMap.id_coe, id_eq,
        blockCoefficients_tmul, Algebra.mul_smul_comm]
  | add u v hu hv =>
      simp only [map_add, Finsupp.add_apply]
      rw [hu, hv, mul_add]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem exists_tensor_blockCoefficient_ne_zero {w : T} (hw : w ≠ 0) :
    ∃ (i j : Fin 4) (n : ℕ), blockCoefficients (tensorCoords w i j) n ≠ 0 := by
  have hcoords : tensorCoords w ≠ 0 := by
    intro hzero
    apply hw
    exact tensorCoords.injective (by simpa only [map_zero,
                                       EmbeddingLike.map_eq_zero_iff] using hzero)
  simp only [ne_eq, funext_iff, Pi.zero_apply, not_forall] at hcoords
  obtain ⟨i, j, hij⟩ := hcoords
  obtain ⟨n, hn⟩ := exists_blockCoefficient_ne_zero hij
  exact ⟨i, j, n, hn⟩

end

section

open Matrix

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem specialLinear_map_transvection
    {A C : Type*} [CommRing A] [CommRing C]
    (f : A →+* C) {i j : Index} (hij : i ≠ j) (a : A) :
    Matrix.SpecialLinearGroup.map f
      (Matrix.SpecialLinearGroup.transvection hij a) =
      Matrix.SpecialLinearGroup.transvection hij (f a) := by
  apply Matrix.SpecialLinearGroup.ext
  intro k l
  change f ((1 + Matrix.single i j a) k l) =
    (1 + Matrix.single i j (f a)) k l
  simp only [Matrix.add_apply, Matrix.one_apply, single_apply, map_add,
    MonoidWithZeroHom.map_ite_one_zero, add_right_inj]
  split_ifs <;> simp_all

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def binaryTransvection {i j : Index} (hij : i ≠ j) (n : ℕ) : Q :=
  Matrix.SpecialLinearGroup.transvection hij
    ((Polynomial.X : R) ^ n)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def integralOrbitTransvection {i j : Index} (hij : i ≠ j) (n : ℕ) :
    IntegralSpecialLinearGroup :=
  Matrix.SpecialLinearGroup.transvection hij
    (Polynomial.C (3 : ℤ) * (Polynomial.X : IntegralPolynomial) ^ n)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem integralOrbitTransvection_mem_K {i j : Index} (hij : i ≠ j) (n : ℕ) :
    integralOrbitTransvection hij n ∈ modThreeGroupHom.ker := by
  change modThreeGroupHom (integralOrbitTransvection hij n) = 1
  rw [integralOrbitTransvection, modThreeGroupHom,
    specialLinear_map_transvection]
  have hthree : (3 : ZMod 3) = 0 := by decide
  simp only [modThreeAtZero, eq_intCast, Int.cast_ofNat, RingHom.coe_comp, Int.coe_castRingHom,
    Polynomial.coe_evalRingHom, Function.comp_apply, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_pow, Polynomial.eval_X, Int.cast_mul, hthree, Int.cast_pow, Int.cast_zero,
    zero_mul, SpecialLinearGroup.transvection_coeff_zero]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def actingTransvection {i j : Index} (hij : i ≠ j) (n : ℕ) : K :=
  ⟨integralOrbitTransvection hij n, integralOrbitTransvection_mem_K hij n⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem pi₂_actingTransvection {i j : Index} (hij : i ≠ j) (n : ℕ) :
    pi₂ (actingTransvection hij n) = binaryTransvection hij n := by
  change Matrix.SpecialLinearGroup.map modTwoPolynomial
    (integralOrbitTransvection hij n) = binaryTransvection hij n
  rw [integralOrbitTransvection, specialLinear_map_transvection]
  apply congrArg (Matrix.SpecialLinearGroup.transvection hij)
  have hthree : (3 : ZMod 2) = 1 := by decide
  simp only [modTwoPolynomial, eq_intCast, Int.cast_ofNat, Polynomial.coe_mapRingHom,
    Polynomial.map_mul, Polynomial.map_ofNat, Polynomial.map_pow, Polynomial.map_X, ne_eq,
    pow_eq_zero_iff', Polynomial.X_ne_zero, false_and, not_false_eq_true, mul_eq_right₀]
  change Polynomial.C (3 : ZMod 2) = Polynomial.C 1
  exact congrArg (Polynomial.C : ZMod 2 →+* R) hthree

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem transvection_smul_apply
    {i j : Index} (hij : i ≠ j) (f : R) (v : V) :
    (Matrix.SpecialLinearGroup.transvection hij f • v) i =
      v i + f * v j := by
  simp only [Matrix.SpecialLinearGroup.smul_def, SpecialLinearGroup.transvection_coe,
    smul_eq_mulVec, add_mulVec, one_mulVec, single_mulVec_eq, Pi.add_apply, Pi.smul_apply,
    Pi.single_eq_same, smul_eq_mul, mul_one]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem x_pow_mul_injective (p : R) (hp : p ≠ 0) :
    Function.Injective (fun n : ℕ ↦ (Polynomial.X : R) ^ n * p) := by
  intro m n h
  have hpowers : (Polynomial.X : R) ^ m = (Polynomial.X : R) ^ n :=
    mul_right_cancel₀ hp h
  simpa only [Polynomial.natDegree_pow, Polynomial.natDegree_X,
    mul_one] using congrArg Polynomial.natDegree hpowers

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem binaryTransvection_smul_injective
    {i j : Index} (hij : i ≠ j) (v : V) (hvj : v j ≠ 0) :
    Function.Injective (fun n : ℕ ↦ binaryTransvection hij n • v) := by
  intro m n h
  have hcoordinate := congrFun h i
  simp only [binaryTransvection, transvection_smul_apply] at hcoordinate
  exact x_pow_mul_injective (v j) hvj (add_left_cancel hcoordinate)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem k_vector_orbit_infinite (v : V) (hv : v ≠ 0) :
    (Set.range fun k : K ↦ kLinear k v).Infinite := by
  obtain ⟨j, hj⟩ : ∃ j : Index, v j ≠ 0 := by
    by_contra h
    push Not at h
    apply hv
    funext j
    exact h j
  obtain ⟨i, hij, _⟩ :=
    Fin.exists_ne_and_ne_of_two_lt j j (by decide : 2 < 4)
  have hcompare (n : ℕ) :
      kLinear (actingTransvection hij n) v = binaryTransvection hij n • v := by
    change Matrix.SpecialLinearGroup.toLin'
      (pi₂ (actingTransvection hij n)) v = binaryTransvection hij n • v
    rw [pi₂_actingTransvection]
    rfl
  have hinjective : Function.Injective
      (fun n : ℕ ↦ kLinear (actingTransvection hij n) v) := by
    simpa only [hcompare] using binaryTransvection_smul_injective hij v hj
  exact (Set.infinite_range_of_injective hinjective).mono (by
    rintro _ ⟨n, rfl⟩
    exact ⟨actingTransvection hij n, rfl⟩)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem transvection_linear_apply_coordinate
    {i j : Index} (hij : i ≠ j) (f : R) (v : V) (k : Index) :
    (Matrix.SpecialLinearGroup.toLin'
      (Matrix.SpecialLinearGroup.transvection hij f) v) k =
      v k + if k = i then f * v j else 0 := by
  simp only [SpecialLinearGroup.toLin', Matrix.SpecialLinearGroup.coe_inv, MonoidHom.coe_mk,
    OneHom.coe_mk, SpecialLinearGroup.transvection_coe, map_add, toLin'_one,
    LinearEquiv.coe_ofLinearMap, LinearMap.add_apply, LinearMap.id_coe, id_eq, toLin'_apply,
    single_mulVec_eq, Pi.add_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one,
    mul_zero]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def transvectionTensor {i j : Index} (hij : i ≠ j) (f : R) : T ≃ₗ[F] T :=
  TensorProduct.congr
    ((Matrix.SpecialLinearGroup.toLin'
      (Matrix.SpecialLinearGroup.transvection hij f)).restrictScalars F)
    ((Matrix.SpecialLinearGroup.toLin'
      (Matrix.SpecialLinearGroup.transvection hij f)).restrictScalars F)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem tensorCoords_transvection
    {i j k : Index} (hij : i ≠ j) (hik : i ≠ k) (f : R) (w : T) :
    tensorCoords (transvectionTensor hij f w) i k =
      tensorCoords w i k +
        (TensorProduct.map (LinearMap.mulLeft F f) LinearMap.id)
          (tensorCoords w j k) := by
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero, Pi.zero_apply, add_zero]
  | tmul u v =>
      simp only [transvectionTensor, TensorProduct.congr_tmul, LinearEquiv.restrictScalars_apply,
        tensorCoords_tmul, transvection_linear_apply_coordinate, ↓reduceIte, hik.symm, add_zero,
        TensorProduct.add_tmul, TensorProduct.map_tmul, LinearMap.mulLeft_apply, LinearMap.id_coe,
        id_eq]
  | add u v hu hv =>
      simp only [map_add, Pi.add_apply]
      rw [hu, hv]
      ac_rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem kTensorLinear_actingTransvection
    {i j : Index} (hij : i ≠ j) (n : ℕ) :
    kTensorLinear (actingTransvection hij n) =
      transvectionTensor hij ((Polynomial.X : R) ^ n) := by
  change TensorProduct.congr
    ((Matrix.SpecialLinearGroup.toLin'
      (pi₂ (actingTransvection hij n))).restrictScalars F)
    ((Matrix.SpecialLinearGroup.toLin'
      (pi₂ (actingTransvection hij n))).restrictScalars F) = _
  rw [pi₂_actingTransvection]
  rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem firstTensorPowerAction_injective
    (z : TensorProduct F R R) (hz : z ≠ 0) :
    Function.Injective (fun n : ℕ ↦
      (TensorProduct.map
        (LinearMap.mulLeft F ((Polynomial.X : R) ^ n)) LinearMap.id) z) := by
  obtain ⟨r, hr⟩ := exists_blockCoefficient_ne_zero hz
  intro m n h
  have hpoly :
      (Polynomial.X : R) ^ m * blockCoefficients z r =
        (Polynomial.X : R) ^ n * blockCoefficients z r := by
    simpa only [blockCoefficients_map_mulLeft] using
      congrArg (fun w : TensorProduct F R R ↦ blockCoefficients w r) h
  exact x_pow_mul_injective (blockCoefficients z r) hr hpoly

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem k_tensor_orbit_infinite (w : T) (hw : w ≠ 0) :
    (Set.range fun k : K ↦ kTensorLinear k w).Infinite := by
  obtain ⟨j, k, r, hr⟩ := exists_tensor_blockCoefficient_ne_zero hw
  have hz : tensorCoords w j k ≠ 0 := by
    intro hzero
    simp only [hzero, map_zero, Finsupp.coe_zero, Pi.zero_apply, ne_eq, not_true_eq_false] at hr
  obtain ⟨i, hij, hik⟩ :=
    Fin.exists_ne_and_ne_of_two_lt j k (by decide : 2 < 4)
  have hinjective :
      Function.Injective (fun n : ℕ ↦
        kTensorLinear (actingTransvection hij n) w) := by
    intro m n h
    have hblock := congrArg (fun z : T ↦ tensorCoords z i k) h
    change tensorCoords (kTensorLinear (actingTransvection hij m) w) i k =
      tensorCoords (kTensorLinear (actingTransvection hij n) w) i k at hblock
    rw [kTensorLinear_actingTransvection hij m,
      kTensorLinear_actingTransvection hij n,
      tensorCoords_transvection hij hik,
      tensorCoords_transvection hij hik] at hblock
    exact firstTensorPowerAction_injective
      (tensorCoords w j k) hz (add_left_cancel hblock)
  exact (Set.infinite_range_of_injective hinjective).mono (by
    rintro _ ⟨n, rfl⟩
    exact ⟨actingTransvection hij n, rfl⟩)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem k_dividedSquare_orbit_infinite (b : B) (hb : b ≠ 0) :
    (Set.range fun k : K ↦ kDividedSquareLinear k b).Infinite := by
  have hval : (b : T) ≠ 0 := by
    intro hzero
    apply hb
    apply Subtype.ext
    exact hzero
  apply Set.Infinite.of_image (fun x : B ↦ (x : T))
  apply (k_tensor_orbit_infinite (b : T) hval).mono
  rintro _ ⟨k, rfl⟩
  exact ⟨kDividedSquareLinear k b, ⟨k, rfl⟩,
    kDividedSquareLinear_val k b⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem k_D_orbit_infinite (x : D) (hx : x ≠ 0) :
    (Set.range fun k : K ↦ kDLinear k x).Infinite := by
  by_cases hv : x.1 = 0
  · have hb : x.2 ≠ 0 := by
      intro hzero
      apply hx
      exact Prod.ext hv hzero
    apply Set.Infinite.of_image (fun y : D ↦ y.2)
    apply (k_dividedSquare_orbit_infinite x.2 hb).mono
    rintro _ ⟨k, rfl⟩
    exact ⟨kDLinear k x, ⟨k, rfl⟩, rfl⟩
  · apply Set.Infinite.of_image (fun y : D ↦ y.1)
    apply (k_vector_orbit_infinite x.1 hv).mono
    rintro _ ⟨k, rfl⟩
    exact ⟨kDLinear k x, ⟨k, rfl⟩, rfl⟩

end

section

open ConnesRigidity

universe u

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def splitConjugationOrbit
    (G H : CountableDiscreteGroup.{u}) (section_ : H →* G) (x : G) : Set G :=
  Set.range fun h : H ↦ section_ h * x * (section_ h)⁻¹

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem isICC_of_split_quotient
    (G H : CountableDiscreteGroup.{u})
    (projection : G →* H) (section_ : H →* G)
    (hsection : ∀ h : H, projection (section_ h) = h)
    (hH : IsICC H)
    (hkernel : ∀ x : G, projection x = 1 → x ≠ 1 →
      (splitConjugationOrbit G H section_ x).Infinite) :
    IsICC G := by
  rcases hH with ⟨hH_infinite, hH_conjugacy⟩
  have : Infinite H := hH_infinite
  have hsection_injective : Function.Injective section_ := by
    intro a b hab
    simpa only [hsection] using congrArg projection hab
  refine ⟨Infinite.of_injective section_ hsection_injective, ?_⟩
  intro x hx
  by_cases hprojection : projection x = 1
  · exact (hkernel x hprojection hx).mono (by
      rintro y ⟨h, rfl⟩
      exact ⟨section_ h, rfl⟩)
  · apply Set.Infinite.of_image projection
    apply (hH_conjugacy (projection x) hprojection).mono
    rintro y ⟨h, rfl⟩
    refine ⟨section_ h * x * (section_ h)⁻¹, ⟨section_ h, rfl⟩, ?_⟩
    simp only [map_mul, hsection, map_inv]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def semidirectCountableGroup
    (A H : CountableDiscreteGroup.{u}) (action : H →* MulAut A) :
    CountableDiscreteGroup.{u} where
  Carrier := SemidirectProduct A H action
  group := inferInstance
  countable := SemidirectProduct.equivProd.injective.countable

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem semidirect_isICC
    (A H : CountableDiscreteGroup.{u}) (action : H →* MulAut A)
    (hH : IsICC H)
    (horbit : ∀ a : A, a ≠ 1 →
      (Set.range fun h : H ↦ action h a).Infinite) :
    IsICC (semidirectCountableGroup A H action) := by
  apply isICC_of_split_quotient
    (semidirectCountableGroup A H action) H
    SemidirectProduct.rightHom SemidirectProduct.inr
    (fun h ↦ SemidirectProduct.rightHom_inr h) hH
  intro x hright hx
  change x.right = 1 at hright
  have hleft : x.left ≠ 1 := by
    intro hleft
    apply hx
    apply SemidirectProduct.ext
    · exact hleft
    · exact hright
  have hinfinite :
      ((SemidirectProduct.inl (φ := action) : A →* SemidirectProduct A H action) ''
        (Set.range fun h : H ↦ action h x.left)).Infinite :=
    (horbit x.left hleft).image
      (SemidirectProduct.inl_injective (φ := action)).injOn
  apply hinfinite.mono
  rintro y ⟨a, ⟨h, rfl⟩, rfl⟩
  refine ⟨h, ?_⟩
  have hxkernel : x = SemidirectProduct.inl x.left := by
    apply SemidirectProduct.ext
    · rfl
    · simpa only [SemidirectProduct.right_inl] using hright
  rw [hxkernel]
  apply SemidirectProduct.ext
  · change
      (1 * action h x.left) * action (h * 1) (action h⁻¹ 1⁻¹) =
        action h x.left
    simp only [one_mul, mul_one, map_inv, inv_one, map_one]
  · change (h * 1) * h⁻¹ = 1
    simp only [mul_one, mul_inv_cancel]

end

section

open ConnesRigidity

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def eKernelGroup (n : ℕ) : CountableDiscreteGroup where
  Carrier := Multiplicative (E n)
  group := inferInstance
  countable := inferInstance

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem kEAction_iota (n : ℕ) (k : K) (v : V) :
    kEAction n k (Multiplicative.ofAdd (iota n v)) =
      Multiplicative.ofAdd (iota n (kLinear k v)) := by
  apply PontryaginDual.ext
  intro z
  change
    ZMod.toCircle
      ((Multiplicative.toAdd ((kCarryAction n k)⁻¹ z)).linear v) =
      ZMod.toCircle ((Multiplicative.toAdd z).linear (kLinear k v))
  change
    ZMod.toCircle
      (kXLinear k⁻¹ (Multiplicative.toAdd z).linear v) =
      ZMod.toCircle ((Multiplicative.toAdd z).linear (kLinear k v))
  rw [kXLinear_apply, inv_inv]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def kEAddAction (n : ℕ) (k : K) : E n ≃+ E n :=
  MulEquiv.toAdditive (kEAction n k)



/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem kEAddAction_iota (n : ℕ) (k : K) (v : V) :
    kEAddAction n k (iota n v) = iota n (kLinear k v) := by
  exact congrArg Multiplicative.toAdd (kEAction_iota n k v)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem kEAddAction_iota_orbit_infinite
    (n : ℕ) (v : V) (hv : v ≠ 0) :
    (Set.range fun k : K => kEAddAction n k (iota n v)).Infinite := by
  have hinfinite :
      ((iota n) '' (Set.range fun k : K => kLinear k v)).Infinite :=
    (k_vector_orbit_infinite v hv).image (iota_injective n).injOn
  apply hinfinite.mono
  rintro _ ⟨w, ⟨k, rfl⟩, rfl⟩
  rw [← kEAddAction_iota n k v]
  exact Set.mem_range_self k

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem kEAddAction_orbit_infinite_of_exact
    (n : ℕ) (sigma : E n →+ B)
    (hsigma_ker : sigma.ker = (iota n).range)
    (hsigma_equivariant : ∀ (k : K) (η : E n),
      sigma (kEAddAction n k η) = kDividedSquareLinear k (sigma η))
    (η : E n) (hη : η ≠ 0) :
    (Set.range fun k : K => kEAddAction n k η).Infinite := by
  by_cases hquadratic : sigma η = 0
  · have hkernel : η ∈ sigma.ker := hquadratic
    rw [hsigma_ker] at hkernel
    obtain ⟨v, hv⟩ := hkernel
    have hvzero : v ≠ 0 := by
      intro hzero
      apply hη
      simpa only [hzero, map_zero] using hv.symm
    rw [← hv]
    exact kEAddAction_iota_orbit_infinite n v hvzero
  · apply Set.Infinite.of_image sigma
    apply (k_dividedSquare_orbit_infinite (sigma η) hquadratic).mono
    rintro _ ⟨k, rfl⟩
    exact ⟨kEAddAction n k η, ⟨k, rfl⟩,
      hsigma_equivariant k η⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem gamma_isICC_of_infinite_orbits
    (n : ℕ)
    (horbit : ∀ η : Multiplicative (E n), η ≠ 1 →
      (Set.range fun k : K => kEAction n k η).Infinite) :
    IsICC (gammaGroup n) := by
  exact semidirect_isICC (eKernelGroup n) actingGroup (kEAction n)
    actingGroup_isICC horbit

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem gamma_isICC_of_additive_infinite_orbits
    (n : ℕ)
    (horbit : ∀ η : E n, η ≠ 0 →
      (Set.range fun k : K => kEAddAction n k η).Infinite) :
    IsICC (gammaGroup n) := by
  apply gamma_isICC_of_infinite_orbits n
  intro η hη
  have hzero : Multiplicative.toAdd η ≠ 0 := by
    intro h
    apply hη
    exact congrArg Multiplicative.ofAdd h
  apply Set.Infinite.of_image Multiplicative.toAdd
  exact (horbit (Multiplicative.toAdd η) hzero).mono (by
    rintro _ ⟨k, rfl⟩
    exact ⟨kEAction n k η, ⟨k, rfl⟩, rfl⟩)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem gamma_isICC_of_exact
    (n : ℕ) (sigma : E n →+ B)
    (hsigma_ker : sigma.ker = (iota n).range)
    (hsigma_equivariant : ∀ (k : K) (η : E n),
      sigma (kEAddAction n k η) = kDividedSquareLinear k (sigma η)) :
    IsICC (gammaGroup n) :=
  gamma_isICC_of_additive_infinite_orbits n
    (kEAddAction_orbit_infinite_of_exact n sigma hsigma_ker
      hsigma_equivariant)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem kEAddAction_quadratic_value (n : ℕ) (k : K)
    (η : E n) (q : Y) :
    Additive.toMul (kEAddAction n k η)
      (Multiplicative.ofAdd (⟨0, q⟩ : CarryGroup n)) =
      Additive.toMul η
        (Multiplicative.ofAdd
          (⟨0, kYLinear k⁻¹ q⟩ : CarryGroup n)) := by
  change
    (kEAction n k (Multiplicative.ofAdd η) :
      PontryaginDual (Multiplicative (CarryGroup n)))
      (Multiplicative.ofAdd (⟨0, q⟩ : CarryGroup n)) =
    (Additive.toMul η)
      (Multiplicative.ofAdd
        (⟨0, kYLinear k⁻¹ q⟩ : CarryGroup n))
  rw [kEAction_apply]
  congr 1

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem sigma_equivariant_of_characterization
    (n : ℕ) (s : E n →+ B)
    (hs : ∀ (η : E n) (q : Y),
      ZMod.toCircle (q (s η)) =
        Additive.toMul η
          (Multiplicative.ofAdd (⟨0, q⟩ : CarryGroup n)))
    (k : K) (η : E n) :
    s (kEAddAction n k η) = kDividedSquareLinear k (s η) := by
  apply Module.eval_apply_injective F
  apply LinearMap.ext
  intro q
  apply ZMod.injective_toCircle
  calc
    ZMod.toCircle (q (s (kEAddAction n k η))) =
        Additive.toMul (kEAddAction n k η)
          (Multiplicative.ofAdd (⟨0, q⟩ : CarryGroup n)) :=
      hs (kEAddAction n k η) q
    _ = Additive.toMul η
          (Multiplicative.ofAdd
            (⟨0, kYLinear k⁻¹ q⟩ : CarryGroup n)) :=
      kEAddAction_quadratic_value n k η q
    _ = ZMod.toCircle ((kYLinear k⁻¹ q) (s η)) :=
      (hs η (kYLinear k⁻¹ q)).symm
    _ = ZMod.toCircle (q (kDividedSquareLinear k (s η))) := by
      rw [kYLinear_apply, inv_inv]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem gamma_isICC_of_characterized_exact
    (n : ℕ) (s : E n →+ B)
    (hs_ker : s.ker = (iota n).range)
    (hs_characterization : ∀ (η : E n) (q : Y),
      ZMod.toCircle (q (s η)) =
        Additive.toMul η
          (Multiplicative.ofAdd (⟨0, q⟩ : CarryGroup n))) :
    IsICC (gammaGroup n) :=
  gamma_isICC_of_exact n s hs_ker
    (sigma_equivariant_of_characterization n s hs_characterization)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem sigma_equivariant (n : ℕ) (k : K) (η : E n) :
    sigma n (kEAddAction n k η) =
      kDividedSquareLinear k (sigma n η) :=
  sigma_equivariant_of_characterization n (sigma n)
    (sigma_characterization n) k η

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem sigma_equivariant_raw (n : ℕ) (k : K) (η : E n) :
    sigma n
        (Multiplicative.toAdd
          (kEAction n k (Multiplicative.ofAdd η))) =
      kDividedSquareLinear k (sigma n η) :=
  sigma_equivariant n k η

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem gamma_isICC (n : ℕ) : IsICC (gammaGroup n) :=
  gamma_isICC_of_characterized_exact n (sigma n) (sigma_ker n)
    (sigma_characterization n)

end

end ConnesRigidity

end
