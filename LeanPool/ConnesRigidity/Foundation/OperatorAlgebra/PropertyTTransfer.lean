/-
Copyright (c) 2026 Utensil Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song
-/
/-

Property-(T) extension interfaces for Zhou §4. The finite-index extension
data records the subgroup, normality, finite index, and the two quotient
identifications used in Proposition 4.8. It does not encode the conclusion
as an implication field.
-/
import LeanPool.ConnesRigidity.Core
import LeanPool.ConnesRigidity.Porting.CoreTransfer
import LeanPool.ConnesRigidity.Foundation.OperatorAlgebra.FiniteIndex
import LeanPool.ConnesRigidity.Foundation.OperatorAlgebra.NormalFixed

/-!
The property t transfer component of the Connes rigidity formalization.
-/

namespace Connes

universe u

namespace CountableDiscreteGroup

/- The quotient wrapper is the group appearing in Zhou's Lemma 4.7.
-/
/--
The `quotient` construction used in the Connes rigidity formalization.
-/
noncomputable def quotient
    (G : CountableDiscreteGroup.{u}) (N : Subgroup G) (hN : N.Normal) :
    CountableDiscreteGroup.{u} := by
  let normalInstance : N.Normal := hN
  exact {
    Carrier := G ⧸ N
    group := inferInstance
    countable := @Quotient.countable _ (inferInstance : Countable G) _ }

end CountableDiscreteGroup

namespace PropertyTTransfer

/-- The finite extension in Zhou Proposition 4.8, before applying Lemma 4.7. -/
structure FiniteExtensionData
    (L G Q : CountableDiscreteGroup.{u}) where
  /--
  The `subgroup` component of `FiniteExtensionData`.
  -/
  subgroup : Subgroup G
  normal : subgroup.Normal
  finiteIndex : subgroup.FiniteIndex
  /--
  The `subgroupEquiv` component of `FiniteExtensionData`.
  -/
  subgroupEquiv : L ≃* OpenAIPort.CountableDiscreteGroup.subgroup G subgroup
  /--
  The `quotientEquiv` component of `FiniteExtensionData`.
  -/
  quotientEquiv : CountableDiscreteGroup.quotient G subgroup normal ≃* Q

/- A property-(T) subgroup supplies the relative part after an explicit
equivalence to the subgroup. -/
theorem relativePropertyT_of_subgroupEquiv
    (L G : CountableDiscreteGroup.{u}) (N : Subgroup G)
    (e : L ≃* OpenAIPort.CountableDiscreteGroup.subgroup G N)
    (hL : HasKazhdanPropertyT L) :
    HasRelativePropertyT G N := by
  classical
  intro K _ _ _ π hπ
  let f : (L : Type u) →* G := N.subtype.comp e.toMonoidHom
  obtain ⟨ξ, hξ, hinv⟩ :=
    hL K inferInstance inferInstance inferInstance (π.comp f) (by
      intro S ε hε
      obtain ⟨η, hη, hclose⟩ := hπ (S.image f) ε hε
      refine ⟨η, hη, ?_⟩
      intro l hl
      exact hclose (f l) (Finset.mem_image.mpr ⟨l, hl, rfl⟩))
  refine ⟨ξ, hξ, ?_⟩
  intro n
  obtain ⟨l, rfl⟩ := e.surjective n
  exact hinv l

/- The quotient representation inherits almost-invariant vectors from a
representation with relative property-(T). This is the quantitative bridge
behind Zhou's Lemma 4.7. -/
theorem normalFixedQuotient_hasAlmostInvariantUnitVectors
    (G : CountableDiscreteGroup.{u}) (N : Subgroup G) [N.Normal]
    (hrelative : HasRelativePropertyT G N)
    {K : Type u} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K]
    (π : UnitaryRepresentation G K)
    (hπ : π.HasAlmostInvariantUnitVectors) :
    (normalFixedQuotientRepresentation N π).HasAlmostInvariantUnitVectors := by
  classical
  intro F ε hε
  have hno :
      ¬(normalFixedOrthogonalRepresentation N π).HasAlmostInvariantUnitVectors := by
    intro horth
    obtain ⟨ξ, hξ, hinv⟩ :=
      hrelative ((normalFixedSubmodule N π)ᗮ)
        inferInstance inferInstance inferInstance
        (normalFixedOrthogonalRepresentation N π) horth
    have hzero := normalFixedOrthogonalRepresentation_no_fixed N π ξ hinv
    exact hξ hzero
  have hgap : ∃ S : Finset G, ∃ κ : ℝ, 0 < κ ∧
      ∀ z : (normalFixedSubmodule N π)ᗮ, ‖z‖ = 1 →
        ∃ g ∈ S,
          κ ≤ ‖(normalFixedOrthogonalRepresentation N π g :
            (normalFixedSubmodule N π)ᗮ →L[ℂ]
              (normalFixedSubmodule N π)ᗮ) z - z‖ := by
    by_contra h
    push Not at h
    exact hno h
  obtain ⟨S, κ, hκ, hgap⟩ := hgap
  let α : ℝ := min (κ / 4) (min (ε * κ / 16) (ε / 16))
  have hα : 0 < α := by
    dsimp [α]
    positivity
  let T : Finset G := S ∪ F.image Quotient.out
  obtain ⟨x, hx, hclose⟩ := hπ T α hα
  let z : K := x - (normalFixedSubmodule N π).starProjection x
  have hzmem : z ∈ (normalFixedSubmodule N π)ᗮ := by
    dsimp [z]
    exact Submodule.sub_starProjection_mem_orthogonal x
  have hzbound : ‖z‖ < α / κ := by
    by_contra hnot
    have hzlower : α / κ ≤ ‖z‖ := le_of_not_gt hnot
    have hz : z ≠ 0 := by
      intro hzero
      rw [hzero, norm_zero] at hzlower
      exact (not_le_of_gt (div_pos hα hκ)) hzlower
    let w : (normalFixedSubmodule N π)ᗮ :=
      ⟨((‖z‖ : ℂ)⁻¹) • z,
        (normalFixedSubmodule N π)ᗮ.smul_mem _ hzmem⟩
    have hwnorm : ‖w‖ = 1 := norm_smul_inv_norm hz
    obtain ⟨g, hg, hgκ⟩ := hgap w hwnorm
    have hcontract :
        ‖(normalFixedOrthogonalRepresentation N π g :
          (normalFixedSubmodule N π)ᗮ →L[ℂ]
            (normalFixedSubmodule N π)ᗮ) ⟨z, hzmem⟩ - ⟨z, hzmem⟩‖ ≤
          ‖(π g : K →L[ℂ] K) x - x‖ := by
      exact normalFixed_orthogonalResidual_displacement_le N π g x
    have hwformula :
        ‖(normalFixedOrthogonalRepresentation N π g :
          (normalFixedSubmodule N π)ᗮ →L[ℂ]
            (normalFixedSubmodule N π)ᗮ) w - w‖ =
          ‖(π g : K →L[ℂ] K) z - z‖ / ‖z‖ := by
      change ‖(π g : K →L[ℂ] K)
        (((‖z‖ : ℂ)⁻¹) • z) - ((‖z‖ : ℂ)⁻¹) • z‖ = _
      rw [map_smul, ← smul_sub, norm_smul, norm_inv,
        Complex.norm_real, Real.norm_of_nonneg (norm_nonneg z)]
      simp only [div_eq_mul_inv, mul_comm]
    rw [hwformula] at hgκ
    have hgsmall : ‖(π g : K →L[ℂ] K) x - x‖ < α :=
      hclose g (Finset.mem_union_left _ hg)
    have hreslt : ‖(π g : K →L[ℂ] K) z - z‖ < α :=
      lt_of_le_of_lt hcontract hgsmall
    have hresdiv :
        ‖(π g : K →L[ℂ] K) z - z‖ / ‖z‖ < α / ‖z‖ :=
      (div_lt_div_iff_of_pos_right (norm_pos_iff.mpr hz)).2 hreslt
    have halphadiv : α / ‖z‖ ≤ κ := by
      apply (div_le_iff₀ (norm_pos_iff.mpr hz)).2
      have hακ : α ≤ ‖z‖ * κ := (div_le_iff₀ hκ).mp hzlower
      simpa [mul_comm] using hακ
    linarith
  let p : normalFixedSubmodule N π :=
    ⟨(normalFixedSubmodule N π).starProjection x,
      Submodule.starProjection_apply_mem _ _⟩
  have hp_lower : 1 - α / κ < ‖p‖ := by
    by_contra hnot
    have hpupper : ‖p‖ ≤ 1 - α / κ := le_of_not_gt hnot
    have htriangle : ‖x‖ ≤ ‖(p : K)‖ + ‖z‖ := by
      calc
        ‖x‖ = ‖(p : K) + z‖ := by
          congr 1
          dsimp [p, z]
          abel
        _ ≤ ‖(p : K)‖ + ‖z‖ := norm_add_le _ _
    rw [hx] at htriangle
    have hsum : ‖p‖ + ‖z‖ < (1 - α / κ) + α / κ :=
      add_lt_add_of_le_of_lt hpupper hzbound
    have hsum' : ‖p‖ + ‖z‖ < 1 := by
      convert hsum using 1
      all_goals ring
    exact (not_lt_of_ge htriangle) hsum'
  have halpha_kappa : α / κ ≤ 1 / 4 := by
    apply (div_le_iff₀ hκ).2
    dsimp [α]
    have hmin := min_le_left (κ / 4) (min (ε * κ / 16) (ε / 16))
    nlinarith
  have hp_lower' : 3 / 4 < ‖p‖ := by
    linarith
  have hp_pos : 0 < ‖p‖ := lt_trans (by norm_num) hp_lower'
  let η : normalFixedSubmodule N π := ((‖p‖ : ℂ)⁻¹) • p
  have hηnorm : ‖η‖ = 1 := by
    dsimp [η]
    exact norm_smul_inv_norm (norm_pos_iff.mp hp_pos)
  refine ⟨η, hηnorm, ?_⟩
  intro q hq
  let g : G := Quotient.out q
  have hgmem : g ∈ T := by
    change g ∈ S ∪ F.image Quotient.out
    apply Finset.mem_union_right S
    exact Finset.mem_image.mpr ⟨q, hq, rfl⟩
  have hgsmall : ‖(π g : K →L[ℂ] K) x - x‖ < α :=
    hclose g hgmem
  have hpdisp :
      ‖(π g : K →L[ℂ] K) (p : K) - (p : K)‖ ≤
        ‖(π g : K →L[ℂ] K) x - x‖ + 2 * ‖z‖ := by
    calc
      ‖(π g : K →L[ℂ] K) (p : K) - (p : K)‖ =
          ‖((π g : K →L[ℂ] K) x - x) -
            ((π g : K →L[ℂ] K) z - z)‖ := by
        congr 1
        dsimp [p, z]
        rw [map_sub]
        abel
      _ ≤ ‖(π g : K →L[ℂ] K) x - x‖ +
            ‖(π g : K →L[ℂ] K) z - z‖ := norm_sub_le _ _
      _ ≤ ‖(π g : K →L[ℂ] K) x - x‖ + 2 * ‖z‖ := by
        calc
          _ ≤ ‖(π g : K →L[ℂ] K) x - x‖ +
              (‖(π g : K →L[ℂ] K) z‖ + ‖z‖) :=
            add_le_add_right (norm_sub_le _ _) _
          _ = ‖(π g : K →L[ℂ] K) x - x‖ + 2 * ‖z‖ := by
            rw [Unitary.norm_map]
            ring
  have hzsmall : ‖z‖ < α / κ := hzbound
  have hnum : α + 2 * (α / κ) ≤ 3 * ε / 16 := by
    have ha : α ≤ ε / 16 := by
      dsimp [α]
      exact le_trans (min_le_right _ _) (min_le_right _ _)
    have har : α / κ ≤ ε / 16 := by
      apply (div_le_iff₀ hκ).2
      have hα2 : α ≤ ε * κ / 16 := by
        dsimp [α]
        exact le_trans (min_le_right _ _) (min_le_left _ _)
      calc
        α ≤ ε * κ / 16 := hα2
        _ = (ε / 16) * κ := by ring
    nlinarith
  have hpdisplt :
      ‖(π g : K →L[ℂ] K) (p : K) - (p : K)‖ < 3 * ε / 16 := by
    exact lt_of_le_of_lt hpdisp (by nlinarith [hgsmall, hzsmall, hnum])
  have hfrac :
      ‖(π g : K →L[ℂ] K) (p : K) - (p : K)‖ / ‖p‖ < ε := by
    apply (div_lt_iff₀ hp_pos).2
    have hpbound : 3 / 4 ≤ ‖p‖ := by linarith
    nlinarith
  have hqg : QuotientGroup.mk' N g = q := by
    exact QuotientGroup.out_eq' q
  have hηdisp : ‖(π g : K →L[ℂ] K) (η : K) - (η : K)‖ < ε := by
    dsimp [η]
    rw [map_smul, ← smul_sub, norm_smul]
    have hscalar :
        ‖((‖(p : K)‖ : ℂ)⁻¹)‖ = (‖(p : K)‖ : ℝ)⁻¹ := by
      simp [norm_inv, Complex.norm_real]
    rw [hscalar]
    simpa only [Submodule.coe_norm, div_eq_mul_inv, mul_comm] using hfrac
  have hrep :
      ((normalFixedQuotientRepresentation N π (QuotientGroup.mk' N g) :
        normalFixedSubmodule N π →L[ℂ] normalFixedSubmodule N π) η : K) =
        (π g : K →L[ℂ] K) (η : K) :=
    normalFixedQuotientRepresentation_apply_mk N π g η
  have htarget :
      ‖((normalFixedQuotientRepresentation N π (QuotientGroup.mk' N g) :
        normalFixedSubmodule N π →L[ℂ] normalFixedSubmodule N π) η : K) -
        (η : K)‖ < ε := by
    rw [hrep]
    exact hηdisp
  rw [← hqg]
  change ‖((normalFixedQuotientRepresentation N π (QuotientGroup.mk' N g) :
    normalFixedSubmodule N π →L[ℂ] normalFixedSubmodule N π) η : K) -
    (η : K)‖ < ε
  exact htarget

/- This is the representation-theoretic extension lemma used as Zhou's
Lemma 4.7. The local relative-property API records the qualitative
representation boundary, so its quantitative transfer proof remains an
explicit project obligation rather than being hidden in a data structure. -/
theorem hasKazhdanPropertyT_of_relative_and_quotient
    (G : CountableDiscreteGroup.{u}) (N : Subgroup G)
    (hN : N.Normal) (hrelative : HasRelativePropertyT G N)
    (hquotient : HasKazhdanPropertyT (CountableDiscreteGroup.quotient G N hN)) :
    HasKazhdanPropertyT G := by
  classical
  let normalInstance : N.Normal := hN
  intro K _ _ _ π hπ
  have hq := normalFixedQuotient_hasAlmostInvariantUnitVectors
    G N hrelative π hπ
  obtain ⟨η, hη, hinv⟩ :=
    hquotient (normalFixedSubmodule N π)
      inferInstance inferInstance inferInstance
      (normalFixedQuotientRepresentation N π) hq
  refine ⟨(η : K), ?_, ?_⟩
  · intro hzero
    apply hη
    exact Subtype.ext hzero
  · intro g
    have hg := congrArg
      (fun v : normalFixedSubmodule N π => (v : K))
      (hinv (QuotientGroup.mk' N g))
    calc
      (π g : K →L[ℂ] K) (η : K) =
          ((normalFixedQuotientRepresentation N π (QuotientGroup.mk' N g) :
            normalFixedSubmodule N π →L[ℂ] normalFixedSubmodule N π) η : K) :=
        (normalFixedQuotientRepresentation_apply_mk N π g η).symm
      _ = (η : K) := hg

/- Apply the preceding lemma to a finite-index extension with an explicit
quotient identification. -/
theorem hasKazhdanPropertyT_of_finiteExtension
    (data : FiniteExtensionData L G Q)
    (hL : HasKazhdanPropertyT L)
    (hQ : HasKazhdanPropertyT Q) :
    HasKazhdanPropertyT G := by
  let hrelative : HasRelativePropertyT G data.subgroup :=
    relativePropertyT_of_subgroupEquiv L G data.subgroup
      data.subgroupEquiv hL
  let hquotient : HasKazhdanPropertyT
    (CountableDiscreteGroup.quotient G data.subgroup data.normal) :=
    (OpenAIPort.hasKazhdanPropertyT_iff_of_mulEquiv
      (CountableDiscreteGroup.quotient G data.subgroup data.normal) Q
      data.quotientEquiv).mpr hQ
  exact hasKazhdanPropertyT_of_relative_and_quotient G data.subgroup
    data.normal hrelative hquotient

end PropertyTTransfer
end Connes
