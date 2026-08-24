/-
Copyright (c) 2026 Utensil Song, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song, OpenAI
-/
/-

Derived in part from Apache-2.0 `openai/ten-proofs`, `ConnesRigidity.lean` at
94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6, lines 31153-31229.
Modifications: specialized the generic Fourier conjugacy block to Zhou's
kernel and local Fourier unitary. Paper: §3. See the upstream PORT_MAP.md.
-/
import Mathlib.MeasureTheory.Function.Holder
import LeanPool.ConnesRigidity.Porting.CoreTransfer
import LeanPool.ConnesRigidity.Paper.Section3.Fourier

/-!
The fourier action component of the Connes rigidity formalization.
-/

namespace Connes
namespace PaperFourierAction

open MeasureTheory
open Construction
open Construction.PaperKernel
open PaperDualHaar
open PaperFourier

noncomputable section

/--
The `D` construction used in the Connes rigidity formalization.
-/
abbrev D := PaperKernel.D
/--
The `CharacterSpace` construction used in the Connes rigidity formalization.
-/
abbrev CharacterSpace := PaperDualHaar.PaperCharacterSpace
/--
The `FourierSpace` construction used in the Connes rigidity formalization.
-/
abbrev FourierSpace := Lp ℂ 2 paperCharacterHaar

/--
The `paperDDecidableEq` construction used in the Connes rigidity formalization.
-/
local instance paperDDecidableEq : DecidableEq D := Classical.decEq D
/--
The `paperMultiplicativeDDecidableEq` construction used in the Connes rigidity formalization.
-/
local instance paperMultiplicativeDDecidableEq :
    DecidableEq (Multiplicative D) := Classical.decEq _

/- Multiplication by a bounded continuous coefficient on the compact dual.
Paper: §3.
-/
/--
The `characterMultiplier` construction used in the Connes rigidity formalization.
-/
def characterMultiplier :
    C(CharacterSpace, ℂ) →L[ℂ] (FourierSpace →L[ℂ] FourierSpace) :=
  ((ContinuousLinearMap.mul ℂ ℂ).holderL paperCharacterHaar ⊤ 2 2).comp
    (ContinuousMap.toLp ⊤ paperCharacterHaar ℂ)

/-- The multiplier has the expected pointwise representative. Paper: §3. -/
theorem characterMultiplier_coeFn
    (q : C(CharacterSpace, ℂ)) (f : FourierSpace) :
    characterMultiplier q f =ᵐ[paperCharacterHaar]
      fun χ => q χ * f χ := by
  exact (ContinuousLinearMap.coeFn_holder (ContinuousLinearMap.mul ℂ ℂ)
    ((ContinuousMap.toLp ⊤ paperCharacterHaar ℂ) q) f).trans <| by
      filter_upwards [ContinuousMap.coeFn_toLp (p := ⊤) (𝕜 := ℂ)
        paperCharacterHaar q] with χ hχ
      change ((ContinuousMap.toLp ⊤ paperCharacterHaar ℂ) q) χ * f χ =
        q χ * f χ
      rw [hχ]

/- Character multiplication shifts the Fourier basis by its index. Paper: §3. -/
theorem characterMultiplier_character (d e : D) :
    characterMultiplier (complexCharacter d) (characterL2 e) =
      characterL2 (d + e) := by
  apply Lp.ext
  filter_upwards [
    characterMultiplier_coeFn (complexCharacter d) (characterL2 e),
    ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2)
      paperCharacterHaar (complexCharacter e),
    ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2)
      paperCharacterHaar (complexCharacter (d + e))]
    with χ hmul he hsum
  change (characterL2 e : CharacterSpace → ℂ) χ =
    complexCharacter e χ at he
  change (characterL2 (d + e) : CharacterSpace → ℂ) χ =
    complexCharacter (d + e) χ at hsum
  change
    (characterMultiplier (complexCharacter d) (characterL2 e) :
      CharacterSpace → ℂ) χ =
      (characterL2 (d + e) : CharacterSpace → ℂ) χ
  calc
    (characterMultiplier (complexCharacter d) (characterL2 e) :
        CharacterSpace → ℂ) χ =
      (complexCharacter d χ) * (characterL2 e : CharacterSpace → ℂ) χ := hmul
    _ = complexCharacter d χ * complexCharacter e χ :=
      congrArg (fun z => complexCharacter d χ * z) he
    _ = complexCharacter (d + e) χ := by
      simp only [complexCharacter, ofAdd_add, map_mul, Circle.coe_mul]
      rfl
    _ = (characterL2 (d + e) : CharacterSpace → ℂ) χ := hsum.symm

/- Reindex the Fourier transform onto the multiplicative kernel carrier.
Paper: §3.
-/
/--
The `paperFourierUnitary` construction used in the Connes rigidity formalization.
-/
def paperFourierUnitary :
    GroupL2 (Multiplicative D) ≃ₗᵢ[ℂ] FourierSpace :=
  (l2Reindex (Multiplicative.toAdd : Multiplicative D ≃ D)).trans
    FourierTransform

/- Reindexing sends a point mass to the corresponding additive index. Paper: §3. -/
private theorem l2Reindex_single
    {α β : Type*} (e : α ≃ β) [DecidableEq α] [DecidableEq β]
    (i : α) (c : ℂ) :
    l2Reindex e (lp.single 2 i c) = lp.single 2 (e i) c := by
  ext j
  simp only [OpenAIPort.l2Reindex_apply, lp.single_apply]
  by_cases h : e.symm j = i
  · have hj : j = e i := by
      simpa only [Equiv.apply_symm_apply] using congrArg e h
    simp only [hj, Equiv.symm_apply_apply, Pi.single_eq_same]
  · have hj : j ≠ e i := by
      intro hj
      apply h
      simp only [hj, Equiv.symm_apply_apply]
    simp only [ne_eq, h, not_false_eq_true, Pi.single_eq_of_ne, hj]

/- Additive kernel translations move point masses by addition. Paper: §3. -/
private theorem additiveLeftRegularUnitary_single
    {A : Type*} [AddCommGroup A] [DecidableEq A]
    (a b : A) (c : ℂ) :
    (leftRegularUnitary (Multiplicative.ofAdd a) :
      GroupL2 (Multiplicative A) →L[ℂ] GroupL2 (Multiplicative A))
        (lp.single 2 (Multiplicative.ofAdd b) c) =
      lp.single 2 (Multiplicative.ofAdd (a + b)) c := by
  ext k
  simp only [OpenAIPort.leftRegularUnitary_apply, lp.single_apply,
    Pi.single_apply, inv_mul_eq_iff_eq_mul, ofAdd_add]

/- The reindexed Fourier transform sends kernel point masses to characters.
Paper: §3. -/
theorem paperFourierUnitary_single (d : D) :
    paperFourierUnitary
        (lp.single 2 (Multiplicative.ofAdd d) (1 : ℂ)) =
      characterL2 d := by
  classical
  change FourierTransform
    (l2Reindex (Multiplicative.toAdd : Multiplicative D ≃ D)
      (lp.single 2 (Multiplicative.ofAdd d) (1 : ℂ))) = characterL2 d
  rw [l2Reindex_single]
  exact Orthonormal.linearIsometryEquiv_symm_apply_single_one
    characterL2_orthonormal characterL2_span_closure_eq_top.ge d

/- Scalar multiples of Fourier point masses are transported linearly. Paper: §3. -/
private theorem fourierUnitary_single_smul
    {A : Type*} [DecidableEq A]
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (U : GroupL2 (Multiplicative A) ≃ₗᵢ[ℂ] K)
    (χ : A → K)
    (hU : ∀ b : A,
      U (lp.single 2 (Multiplicative.ofAdd b) (1 : ℂ)) = χ b)
    (b : A) (c : ℂ) :
    U (lp.single 2 (Multiplicative.ofAdd b) c) = c • χ b := by
  have hs : lp.single (E := fun _ : Multiplicative A => ℂ)
      2 (Multiplicative.ofAdd b) c =
      c • lp.single (E := fun _ : Multiplicative A => ℂ)
        2 (Multiplicative.ofAdd b) (1 : ℂ) := by
    simpa only [smul_eq_mul, mul_one] using
      (lp.single_smul (E := fun _ : Multiplicative A => ℂ)
        2 (Multiplicative.ofAdd b) c (1 : ℂ))
  rw [hs, map_smul, hU]

/- A Fourier unitary conjugates a kernel regular operator when it shifts the
character basis in the corresponding way. Paper: §3. -/
theorem fourier_conjugates_regular_of_character_basis
    {A : Type*} [AddCommGroup A] [DecidableEq A]
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K]
    (U : GroupL2 (Multiplicative A) ≃ₗᵢ[ℂ] K)
    (χ : A → K)
    (hU : ∀ b : A,
      U (lp.single 2 (Multiplicative.ofAdd b) (1 : ℂ)) = χ b)
    (a : A) (T : K →L[ℂ] K)
    (hT : ∀ b : A, T (χ b) = χ (a + b)) :
    U.conjStarAlgEquiv
        (leftRegularUnitary (Multiplicative.ofAdd a) :
          GroupL2 (Multiplicative A) →L[ℂ]
            GroupL2 (Multiplicative A)) = T := by
  let F : GroupL2 (Multiplicative A) →L[ℂ] K :=
    U.toContinuousLinearEquiv.toContinuousLinearMap
  have hcomp :
      F.comp (leftRegularUnitary (Multiplicative.ofAdd a) :
        GroupL2 (Multiplicative A) →L[ℂ]
          GroupL2 (Multiplicative A)) = T.comp F := by
    apply lp.ext_continuousLinearMap
      (by simp only [ne_eq, ENNReal.ofNat_ne_top, not_false_eq_true])
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
    rw [additiveLeftRegularUnitary_single a (Multiplicative.toAdd b) c,
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

/- The actual paper Fourier unitary conjugates every kernel regular operator
to its character multiplier. Paper: §3. -/
theorem paperFourier_conjugates_regular (d : D) :
    paperFourierUnitary.conjStarAlgEquiv
        (leftRegularUnitary (Multiplicative.ofAdd d) :
          GroupL2 (Multiplicative D) →L[ℂ]
            GroupL2 (Multiplicative D)) =
      characterMultiplier (complexCharacter d) := by
  apply fourier_conjugates_regular_of_character_basis
    (U := paperFourierUnitary) (χ := characterL2)
  · exact paperFourierUnitary_single
  · intro b
    exact characterMultiplier_character d b

end
end PaperFourierAction
end Connes
