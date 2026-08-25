/-
Copyright (c) 2026 Utensil Song, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song, OpenAI
-/
/-

Derived in part from Apache-2.0 `openai/ten-proofs`, `ConnesRigidity.lean` at
94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6, lines 295-655.
Modifications: extracted finite-index induction into a small namespace and
adapted imports and local group vocabulary. See the upstream PORT_MAP.md.
-/
import LeanPool.ConnesRigidity.Core

/-!
The finite index component of the Connes rigidity formalization.
-/

namespace Connes
namespace OpenAIPort

universe u v

open scoped ENNReal

/-- Countable discrete subgroup wrapper. Paper: §4. -/
def CountableDiscreteGroup.subgroup
    (G : CountableDiscreteGroup.{u}) (S : Subgroup G) :
    CountableDiscreteGroup.{u} where
  Carrier := S
  group := inferInstance
  countable := inferInstance

namespace FiniteIndex

variable {G : Type u} [Group G] (S : Subgroup G)

/-- Correction element for the finite-index induced representation. Paper: §4. -/
noncomputable def correction (g : G) (q : G ⧸ S) : S :=
  ⟨(Quotient.out (g • q))⁻¹ * g * Quotient.out q, by
    have hrel : QuotientGroup.leftRel S
        (Quotient.out (g • q)) (g * Quotient.out q) := by
      apply Quotient.exact'
      calc
        QuotientGroup.mk (Quotient.out (g • q)) = g • q :=
          Quotient.out_eq _
        _ = g • QuotientGroup.mk (Quotient.out q) := by
          exact congrArg (fun r : G ⧸ S ↦ g • r) (Quotient.out_eq q).symm
        _ = QuotientGroup.mk (g * Quotient.out q) := rfl
    exact (by
      simpa only [mul_assoc] using
        (QuotientGroup.leftRel_apply (s := S)).mp hrel)⟩

/-- Pointwise formula for the correction element. Paper: §4. -/
@[simp] theorem correction_coe (g : G) (q : G ⧸ S) :
    (correction S g q : G) =
      (Quotient.out (g • q))⁻¹ * g * Quotient.out q :=
  rfl

/-- Multiplicativity of the correction cocycle. Paper: §4. -/
theorem correction_mul (g h : G) (q : G ⧸ S) :
    correction S (g * h) q =
      correction S g (h • q) * correction S h q := by
  apply Subtype.ext
  simp only [correction, mul_smul, mul_assoc, MulMemClass.mk_mul_mk, mul_inv_cancel_left]

/-- Unit value of the correction cocycle. Paper: §4. -/
@[simp] theorem correction_one (q : G ⧸ S) :
    correction S 1 q = 1 := by
  apply Subtype.ext
  simp only [correction, one_smul, mul_one, inv_mul_cancel, OneMemClass.coe_one]

/-- The subgroup fixes the base coset. Paper: §4. -/
theorem subgroup_smul_baseCoset (s : S) :
    (s : G) • (QuotientGroup.mk 1 : G ⧸ S) =
      QuotientGroup.mk 1 := by
  apply Quotient.sound
  change QuotientGroup.leftRel S ((s : G) * 1) 1
  rw [QuotientGroup.leftRel_apply]
  simp only [mul_one, inv_mem_iff, SetLike.coe_mem]

/-- The chosen representative of the base coset lies in the subgroup. Paper: §4. -/
theorem quotientOut_baseCoset_mem :
    Quotient.out (QuotientGroup.mk 1 : G ⧸ S) ∈ S := by
  let q₀ : G ⧸ S := QuotientGroup.mk 1
  have hrel : QuotientGroup.leftRel S (Quotient.out q₀) 1 := by
    apply Quotient.exact'
    exact Quotient.out_eq q₀
  have hinv : (Quotient.out q₀)⁻¹ ∈ S := by
    simpa only [inv_mem_iff, QuotientGroup.leftRel_apply, mul_one] using hrel
  exact S.inv_mem_iff.mp hinv

section Induced

variable [S.FiniteIndex]
variable {H : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/--
The `finiteIndexQuotientFintype` construction used in the Connes rigidity formalization.
-/
noncomputable local instance finiteIndexQuotientFintype : Fintype (G ⧸ S) :=
  S.fintypeQuotientOfFiniteIndex

/-- Hilbert space induced from a finite-index subgroup. Paper: §4. -/
abbrev InducedSpace :=
  PiLp 2 (fun _ : G ⧸ S ↦ H)

/-- Linear-isometric action on the induced Hilbert space. Paper: §4. -/
noncomputable def inducedLinearIsometryEquiv
    (π : UnitaryRepresentation S H) (g : G) :
    InducedSpace (H := H) S ≃ₗᵢ[ℂ] InducedSpace (H := H) S := by
  exact
    (LinearIsometryEquiv.piLpCongrLeft 2 ℂ H (MulAction.toPerm g)).trans
      (LinearIsometryEquiv.piLpCongrRight 2
        (fun q ↦ Unitary.linearIsometryEquiv
          (π (correction S g (g⁻¹ • q)))))

/-- Pointwise formula for the induced linear isometry. Paper: §4. -/
@[simp] theorem inducedLinearIsometryEquiv_apply
    (π : UnitaryRepresentation S H) (g : G)
    (ξ : InducedSpace (H := H) S) (q : G ⧸ S) :
    inducedLinearIsometryEquiv S π g ξ q =
      (π (correction S g (g⁻¹ • q)) : H →L[ℂ] H)
        (ξ (g⁻¹ • q)) := by
  rfl

/-- Unitary wrapper for the induced linear isometry. Paper: §4. -/
noncomputable def inducedUnitary
    (π : UnitaryRepresentation S H) (g : G) :
    unitary (InducedSpace (H := H) S →L[ℂ] InducedSpace (H := H) S) :=
  Unitary.linearIsometryEquiv.symm (inducedLinearIsometryEquiv S π g)

/-- Pointwise formula for the induced unitary. Paper: §4. -/
@[simp] theorem inducedUnitary_apply
    (π : UnitaryRepresentation S H) (g : G)
    (ξ : InducedSpace (H := H) S) (q : G ⧸ S) :
    (inducedUnitary S π g :
      InducedSpace (H := H) S →L[ℂ] InducedSpace (H := H) S) ξ q =
      (π (correction S g (g⁻¹ • q)) : H →L[ℂ] H)
        (ξ (g⁻¹ • q)) := by
  rfl

/-- Induced unitary representation of the ambient group. Paper: §4. -/
noncomputable def inducedRepresentation
    (π : UnitaryRepresentation S H) :
    UnitaryRepresentation G (InducedSpace (H := H) S) where
  toFun := inducedUnitary S π
  map_one' := by
    apply Subtype.ext
    ext ξ q
    simp only [inducedUnitary_apply, inv_one, one_smul, correction_one, map_one,
      OneMemClass.coe_one, one_apply_eq_self]
  map_mul' g h := by
    apply Subtype.ext
    ext ξ q
    simp only [inducedUnitary_apply, Submonoid.coe_mul, mul_apply_eq_comp]
    rw [correction_mul]
    simp only [mul_inv_rev, mul_smul, smul_inv_smul, map_mul, Submonoid.coe_mul, mul_apply_eq_comp]

/-- Pointwise formula for the induced representation. Paper: §4. -/
@[simp] theorem inducedRepresentation_apply
    (π : UnitaryRepresentation S H) (g : G)
    (ξ : InducedSpace (H := H) S) (q : G ⧸ S) :
    (inducedRepresentation S π g :
      InducedSpace (H := H) S →L[ℂ] InducedSpace (H := H) S) ξ q =
      (π (correction S g (g⁻¹ • q)) : H →L[ℂ] H)
        (ξ (g⁻¹ • q)) :=
  rfl

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
/-- Sum-of-coordinate norm bound for the induced space. Paper: §4. -/
theorem inducedSpace_norm_le_sum_norm_apply
    (ξ : InducedSpace (H := H) S) :
    ‖ξ‖ ≤ ∑ q : G ⧸ S, ‖ξ q‖ := by
  classical
  have hξ :
      ξ = ∑ q : G ⧸ S, PiLp.single 2 q (ξ q) := by
    ext q
    simp only [WithLp.ofLp_sum, PiLp.ofLp_single, Finset.sum_apply, Finset.sum_pi_single,
      Finset.mem_univ, ↓reduceIte]
  calc
    ‖ξ‖ = ‖∑ q : G ⧸ S, PiLp.single 2 q (ξ q)‖ :=
      congrArg norm hξ
    _ ≤ ∑ q : G ⧸ S, ‖ξ q‖ := by
      simpa only [PiLp.norm_single] using
        (norm_sum_le Finset.univ
          (fun q : G ⧸ S ↦ PiLp.single 2 q (ξ q)))

/-- Almost-invariant vectors lift through finite-index induction. Paper: §4. -/
theorem inducedRepresentation_hasAlmostInvariantUnitVectors
    (π : UnitaryRepresentation S H)
    (hπ : π.HasAlmostInvariantUnitVectors) :
    (inducedRepresentation S π).HasAlmostInvariantUnitVectors := by
  classical
  intro K ε hε
  let n : ℝ := Fintype.card (G ⧸ S)
  let δ : ℝ := ε / (n + 1)
  have hn : 0 ≤ n := by
    dsimp [n]
    positivity
  have hden : 0 < n + 1 := by positivity
  have hδ : 0 < δ := div_pos hε hden
  let T : Finset S :=
    K.biUnion fun g ↦
      Finset.univ.image fun q : G ⧸ S ↦
        correction S g (g⁻¹ • q)
  obtain ⟨v, hvnorm, hvclose⟩ := hπ T δ hδ
  let raw : InducedSpace (H := H) S :=
    WithLp.toLp 2 (fun _ : G ⧸ S ↦ v)
  let q₀ : G ⧸ S := QuotientGroup.mk 1
  have hraw_lower : 1 ≤ ‖raw‖ := by
    have hcoord := PiLp.norm_apply_le raw q₀
    simpa [raw, q₀, hvnorm] using hcoord
  have hraw_pos : 0 < ‖raw‖ := zero_lt_one.trans_le hraw_lower
  let a : ℂ := ((‖raw‖⁻¹ : ℝ) : ℂ)
  let ξ : InducedSpace (H := H) S := a • raw
  have ha_norm : ‖a‖ = ‖raw‖⁻¹ := by
    simp [a]
  have ha_le_one : ‖a‖ ≤ 1 := by
    rw [ha_norm]
    exact inv_le_one_of_one_le₀ hraw_lower
  have hξnorm : ‖ξ‖ = 1 := by
    rw [show ξ = a • raw by rfl, norm_smul, ha_norm]
    exact inv_mul_cancel₀ hraw_pos.ne'
  refine ⟨ξ, hξnorm, ?_⟩
  intro g hg
  have hcoordinate :
      ∀ q : G ⧸ S,
        ‖((inducedRepresentation S π g :
            InducedSpace (H := H) S →L[ℂ] InducedSpace (H := H) S) ξ - ξ) q‖ < δ := by
    intro q
    have hmem : correction S g (g⁻¹ • q) ∈ T := by
      apply Finset.mem_biUnion.mpr
      refine ⟨g, hg, ?_⟩
      apply Finset.mem_image.mpr
      exact ⟨q, Finset.mem_univ q, rfl⟩
    have hclose := hvclose (correction S g (g⁻¹ • q)) hmem
    have hformula :
        ((inducedRepresentation S π g :
            InducedSpace (H := H) S →L[ℂ] InducedSpace (H := H) S) ξ - ξ) q =
          a •
            ((π (correction S g (g⁻¹ • q)) : H →L[ℂ] H) v - v) := by
      simp [ξ, raw, map_smul, smul_sub]
    rw [hformula, norm_smul]
    calc
      ‖a‖ * ‖(π (correction S g (g⁻¹ • q)) : H →L[ℂ] H) v - v‖ ≤
          1 * ‖(π (correction S g (g⁻¹ • q)) : H →L[ℂ] H) v - v‖ :=
        mul_le_mul_of_nonneg_right ha_le_one (norm_nonneg _)
      _ < δ := by simpa using hclose
  calc
    ‖(inducedRepresentation S π g :
        InducedSpace (H := H) S →L[ℂ] InducedSpace (H := H) S) ξ - ξ‖ ≤
        ∑ q : G ⧸ S,
          ‖((inducedRepresentation S π g :
              InducedSpace (H := H) S →L[ℂ] InducedSpace (H := H) S) ξ - ξ) q‖ :=
      inducedSpace_norm_le_sum_norm_apply S _
    _ < ∑ _q : G ⧸ S, δ :=
      Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
        (fun q _ ↦ hcoordinate q)
    _ = n * δ := by
      simp [n]
    _ < ε := by
      dsimp [δ]
      rw [show n * (ε / (n + 1)) = (n * ε) / (n + 1) by ring]
      exact (div_lt_iff₀ hden).2 (by linarith)

/-- A nonzero invariant induced vector is nonzero at the base coset. Paper: §4. -/
theorem inducedInvariant_baseCoset_ne_zero
    (π : UnitaryRepresentation S H)
    (η : InducedSpace (H := H) S)
    (hη : η ≠ 0)
    (hinv : (inducedRepresentation S π).IsInvariant η) :
    η (QuotientGroup.mk 1 : G ⧸ S) ≠ 0 := by
  classical
  let q₀ : G ⧸ S := QuotientGroup.mk 1
  obtain ⟨q, hq⟩ : ∃ q : G ⧸ S, η q ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hη
    ext q
    exact hall q
  have hgq : Quotient.out q • q₀ = q := by
    calc
      Quotient.out q • q₀ =
          QuotientGroup.mk (Quotient.out q * 1) := rfl
      _ = QuotientGroup.mk (Quotient.out q) := by rw [mul_one]
      _ = q := Quotient.out_eq q
  have hinvq : (Quotient.out q)⁻¹ • q = q₀ := by
    calc
      (Quotient.out q)⁻¹ • q =
          (Quotient.out q)⁻¹ • (Quotient.out q • q₀) :=
        congrArg (fun r : G ⧸ S ↦ (Quotient.out q)⁻¹ • r) hgq.symm
      _ = q₀ := inv_smul_smul (Quotient.out q) q₀
  have heval :=
    congrArg (fun ζ : InducedSpace (H := H) S ↦
      ζ (Quotient.out q • q₀)) (hinv (Quotient.out q))
  have heval' :
      (π (correction S (Quotient.out q) q₀) : H →L[ℂ] H) (η q₀) =
        η q := by
    simpa only [inducedRepresentation_apply, hinvq, hgq] using heval
  intro hzero
  apply hq
  rw [← heval', hzero, map_zero]

omit [S.FiniteIndex] in
/-- Correction conjugacy at the base coset. Paper: §4. -/
theorem correction_conjugate_at_baseCoset
    (s : S) :
    let r : S :=
      ⟨Quotient.out (QuotientGroup.mk 1 : G ⧸ S),
        quotientOut_baseCoset_mem S⟩
    correction S ((r * s * r⁻¹ : S) : G)
      (QuotientGroup.mk 1 : G ⧸ S) = s := by
  dsimp only
  apply Subtype.ext
  rw [correction_coe]
  rw [subgroup_smul_baseCoset]
  simp only [mul_assoc, Subgroup.coe_mul, InvMemClass.coe_inv, inv_mul_cancel_left, inv_mul_cancel,
    mul_one]

/-- Invariant induced vectors restrict to invariant subgroup vectors. Paper: §4. -/
theorem inducedInvariant_baseCoset_isInvariant
    (π : UnitaryRepresentation S H)
    (η : InducedSpace (H := H) S)
    (hinv : (inducedRepresentation S π).IsInvariant η) :
    π.IsInvariant (η (QuotientGroup.mk 1 : G ⧸ S)) := by
  intro s
  let q₀ : G ⧸ S := QuotientGroup.mk 1
  let r : S :=
    ⟨Quotient.out q₀, quotientOut_baseCoset_mem S⟩
  let t : S := r * s * r⁻¹
  have heval :=
    congrArg (fun ζ : InducedSpace (H := H) S ↦ ζ q₀)
      (hinv (t : G))
  have htfix : ((t : G)⁻¹) • q₀ = q₀ := by
    rw [← Subgroup.coe_inv]
    exact subgroup_smul_baseCoset S t⁻¹
  have hcorr : correction S (t : G) q₀ = s := by
    simpa [t, r, q₀] using correction_conjugate_at_baseCoset S s
  simpa only [inducedRepresentation_apply, htfix, hcorr] using heval

end Induced

end FiniteIndex

/-- Property-(T) descends to a finite-index subgroup. Paper: §4. -/
theorem hasKazhdanPropertyT_subgroup_of_finiteIndex
    (G : CountableDiscreteGroup.{u}) (S : Subgroup G)
    [S.FiniteIndex]
    (hG : HasKazhdanPropertyT.{u, max u v} G) :
    HasKazhdanPropertyT.{u, v} (CountableDiscreteGroup.subgroup G S) := by
  intro H _ _ _ π hπ
  let quotientFintype : Fintype (G ⧸ S) := S.fintypeQuotientOfFiniteIndex
  obtain ⟨η, hη, hinv⟩ :=
    hG (FiniteIndex.InducedSpace (H := H) S)
      inferInstance inferInstance inferInstance
      (FiniteIndex.inducedRepresentation S π)
      (FiniteIndex.inducedRepresentation_hasAlmostInvariantUnitVectors S π hπ)
  exact
    ⟨η (QuotientGroup.mk 1 : G ⧸ S),
      FiniteIndex.inducedInvariant_baseCoset_ne_zero S π η hη hinv,
      FiniteIndex.inducedInvariant_baseCoset_isInvariant S π η hinv⟩

end OpenAIPort
end Connes
