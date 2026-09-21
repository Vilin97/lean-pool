/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WP.HeadTResidue

/-!
# The residue field of the head at a maximal ideal

([hrw-decomposition] BETA brick (ii) prep.)  Maximal residues of the head
itself are `K`-finite (the `T_N`-tower at level zero: contract along the
even inclusion, apply the even Nullstellensatz through `evenSupportEquiv`,
climb the finite extension), and the constant embedding of `K` into the
head is norm-nonincreasing, giving the continuous `K`-scalar action.
-/

@[expose] public section

namespace WeightedParity

open FiniteJetOver FiniteJet.GraphKoszul

open scoped NormedField Valued

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [CompleteSpace K]
variable (w : ℕ → ℕ) (N : ℕ)

/-- The constant embedding of the head is norm-nonincreasing. -/
theorem norm_constHead_le (c : K) : ‖constHead K w N c‖ ≤ ‖c‖ := by
  show ‖((constHead K w N c : WPHead K w N) : Amb K)‖ ≤ ‖c‖
  rw [MvRestricted.norm_eq, MvPowerSeries.gaussNorm]
  refine ciSup_le fun t => ?_
  rw [show (t.prod ((fun _ : ℕ => (1 : ℝ)) · ^ ·)) = 1 from by
    simp [Finsupp.prod], mul_one]
  show ‖MvPowerSeries.coeff t (MvPowerSeries.C (σ := ℕ) c)‖ ≤ ‖c‖
  classical
  rw [MvPowerSeries.coeff_C]
  by_cases ht : t = 0
  · rw [if_pos ht]
  · rw [if_neg ht, norm_zero]
    exact norm_nonneg c

/-- Maximal residues of the even part are `K`-finite (Nullstellensatz along
`evenSupportEquiv`). -/
theorem module_finite_residue_even (ϖ : Uniformizer K)
    [hdvr : IsDiscreteValuationRing 𝒪[K]]
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (𝔪ₑ : Ideal ↥(wpEvenSupport K w N)) [h𝔪 : 𝔪ₑ.IsMaximal] :
    letI : Algebra K (↥(wpEvenSupport K w N) ⧸ 𝔪ₑ) :=
      ((Ideal.Quotient.mk 𝔪ₑ).comp (evenConst w N)).toAlgebra
    Module.Finite K (↥(wpEvenSupport K w N) ⧸ 𝔪ₑ) := by
  letI : Algebra K (↥(wpEvenSupport K w N) ⧸ 𝔪ₑ) :=
    ((Ideal.Quotient.mk 𝔪ₑ).comp (evenConst w N)).toAlgebra
  classical
  set 𝔪' : Ideal (P K (N + 1)) :=
    𝔪ₑ.map (((evenSupportEquiv K w N) :
      ↥(wpEvenSupport K w N) ≃+* P K (N + 1)) :
      ↥(wpEvenSupport K w N) →+* P K (N + 1)) with h𝔪'def
  haveI h𝔪'max : 𝔪'.IsMaximal := by
    rw [h𝔪'def, Ideal.map_comap_of_equiv]
    exact Ideal.comap_isMaximal_of_surjective _
      ((evenSupportEquiv K w N).symm.surjective)
  letI : Algebra K (P K (N + 1) ⧸ 𝔪') :=
    (FiniteJet.GraphKoszul.constantsToResidue (m := N + 1) 𝔪').toAlgebra
  haveI hbig : Module.Finite K (P K (N + 1) ⧸ 𝔪') :=
    FiniteJet.GraphKoszul.module_finite_residue (m := N + 1) ϖ 𝔪' hK₀
  have hle : 𝔪ₑ ≤ Ideal.comap (((evenSupportEquiv K w N) :
      ↥(wpEvenSupport K w N) ≃+* P K (N + 1)) :
      ↥(wpEvenSupport K w N) →+* P K (N + 1)) 𝔪' :=
    Ideal.le_comap_map
  set e : (↥(wpEvenSupport K w N) ⧸ 𝔪ₑ) →+* (P K (N + 1) ⧸ 𝔪') :=
    Ideal.quotientMap 𝔪' (((evenSupportEquiv K w N) :
      ↥(wpEvenSupport K w N) ≃+* P K (N + 1)) :
      ↥(wpEvenSupport K w N) →+* P K (N + 1)) hle with hedef
  have hinj : Function.Injective e := by
    rw [hedef]
    refine Ideal.quotientMap_injective' ?_
    rw [h𝔪'def]
    have hcm : Ideal.comap (((evenSupportEquiv K w N) :
        ↥(wpEvenSupport K w N) ≃+* P K (N + 1)) :
        ↥(wpEvenSupport K w N) →+* P K (N + 1))
        (Ideal.map (((evenSupportEquiv K w N) :
          ↥(wpEvenSupport K w N) ≃+* P K (N + 1)) :
          ↥(wpEvenSupport K w N) →+* P K (N + 1)) 𝔪ₑ) = 𝔪ₑ :=
      Ideal.comap_map_of_bijective _ (evenSupportEquiv K w N).bijective
    rw [hcm]
  have hcomm : ∀ c : K, e (algebraMap K
      (↥(wpEvenSupport K w N) ⧸ 𝔪ₑ) c) =
      algebraMap K (P K (N + 1) ⧸ 𝔪') c := by
    intro c
    show e (Ideal.Quotient.mk 𝔪ₑ (evenConst w N c)) =
      Ideal.Quotient.mk 𝔪'
        (FiniteJet.GraphKoszul.polyToP (MvPolynomial.C c))
    rw [hedef, Ideal.quotientMap_mk]
    have h6 : (((evenSupportEquiv K w N) :
        ↥(wpEvenSupport K w N) ≃+* P K (N + 1)) :
        ↥(wpEvenSupport K w N) →+* P K (N + 1)) (evenConst w N c) =
        constPE (N + 1) c := evenSupportEquiv_evenConst w N c
    rw [h6]
    congr 1
    refine Subtype.ext ?_
    show MvPowerSeries.C c =
      ((MvPolynomial.C c : MvPolynomial (Fin (N + 1)) K) :
        MvPowerSeries (Fin (N + 1)) K)
    exact (MvPolynomial.coe_C c).symm
  have hlin : ∀ (c : K) (x : ↥(wpEvenSupport K w N) ⧸ 𝔪ₑ),
      e (c • x) = c • e x := by
    intro c x
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, hcomm]
  exact Module.Finite.of_injective
    ({ toFun := ⇑e,
       map_add' := fun a b => map_add e a b,
       map_smul' := fun c x => by
         rw [RingHom.id_apply]
         exact hlin c x } :
      (↥(wpEvenSupport K w N) ⧸ 𝔪ₑ) →ₗ[K] (P K (N + 1) ⧸ 𝔪')) hinj

/-- The even-into-head inclusion sends constants to constants. -/
theorem inclusion_evenConst (c : K) :
    Subring.inclusion (wpEvenSupport_le_wpHeadSupport K w N)
      (evenConst w N c) = constHead K w N c :=
  Subtype.ext rfl

/-- **Maximal residues of the head are `K`-finite** (the tower at level
zero). -/
theorem module_finite_residue_head (ϖ : Uniformizer K)
    [hdvr : IsDiscreteValuationRing 𝒪[K]]
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (𝔭 : Ideal (WPHead K w N)) [h𝔭 : 𝔭.IsMaximal] :
    letI : Algebra K (WPHead K w N ⧸ 𝔭) :=
      ((Ideal.Quotient.mk 𝔭).comp (constHead K w N)).toAlgebra
    Module.Finite K (WPHead K w N ⧸ 𝔭) := by
  letI : Algebra K (WPHead K w N ⧸ 𝔭) :=
    ((Ideal.Quotient.mk 𝔭).comp (constHead K w N)).toAlgebra
  classical
  letI : Algebra ↥(wpEvenSupport K w N) (WPHead K w N) :=
    (Subring.inclusion (wpEvenSupport_le_wpHeadSupport K w N)).toAlgebra
  haveI hfin : Module.Finite ↥(wpEvenSupport K w N) (WPHead K w N) :=
    moduleFinite_head_over_even (K := K) (w := w) (N := N)
  haveI hint : Algebra.IsIntegral ↥(wpEvenSupport K w N) (WPHead K w N) :=
    Algebra.IsIntegral.of_finite _ _
  set 𝔪ₑ : Ideal ↥(wpEvenSupport K w N) :=
    𝔭.comap (Subring.inclusion (wpEvenSupport_le_wpHeadSupport K w N))
    with h𝔪ₑdef
  haveI h𝔪ₑmax : 𝔪ₑ.IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal 𝔭
  letI : Algebra K (↥(wpEvenSupport K w N) ⧸ 𝔪ₑ) :=
    ((Ideal.Quotient.mk 𝔪ₑ).comp (evenConst w N)).toAlgebra
  haveI heven : Module.Finite K (↥(wpEvenSupport K w N) ⧸ 𝔪ₑ) :=
    module_finite_residue_even w N ϖ hK₀ 𝔪ₑ
  letI : Algebra (↥(wpEvenSupport K w N) ⧸ 𝔪ₑ) (WPHead K w N ⧸ 𝔭) :=
    (Ideal.quotientMap 𝔭
      (Subring.inclusion (wpEvenSupport_le_wpHeadSupport K w N))
      (le_of_eq h𝔪ₑdef)).toAlgebra
  haveI hfin2 : Module.Finite (↥(wpEvenSupport K w N) ⧸ 𝔪ₑ)
      (WPHead K w N ⧸ 𝔭) := by
    obtain ⟨T, hT⟩ := hfin.fg_top
    refine ⟨⟨T.image (Ideal.Quotient.mk 𝔭), ?_⟩⟩
    rw [eq_top_iff]
    intro z _
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
    have hb : b ∈ Submodule.span ↥(wpEvenSupport K w N) (T : Set _) := by
      rw [hT]
      exact Submodule.mem_top
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hb
    · intro t ht
      exact Submodule.subset_span (Finset.mem_coe.mpr
        (Finset.mem_image_of_mem _ ht))
    · rw [_root_.map_zero]
      exact Submodule.zero_mem _
    · intro u v _ _ hu hv
      rw [_root_.map_add]
      exact Submodule.add_mem _ hu hv
    · intro a x _ hx
      have h5 : Ideal.Quotient.mk 𝔭 (a • x) =
          (Ideal.Quotient.mk 𝔪ₑ a) • (Ideal.Quotient.mk 𝔭 x) := by
        show Ideal.Quotient.mk 𝔭
          (Subring.inclusion (wpEvenSupport_le_wpHeadSupport K w N) a
            * x) = _
        rw [map_mul]
        rfl
      rw [h5]
      exact Submodule.smul_mem _ _ hx
  haveI htower : IsScalarTower K (↥(wpEvenSupport K w N) ⧸ 𝔪ₑ)
      (WPHead K w N ⧸ 𝔭) := by
    refine IsScalarTower.of_algebraMap_eq fun c => ?_
    show Ideal.Quotient.mk 𝔭 (constHead K w N c) =
      Ideal.quotientMap 𝔭
        (Subring.inclusion (wpEvenSupport_le_wpHeadSupport K w N))
        (le_of_eq h𝔪ₑdef)
        (Ideal.Quotient.mk 𝔪ₑ (evenConst w N c))
    rw [Ideal.quotientMap_mk, inclusion_evenConst]
  exact Module.Finite.trans (↥(wpEvenSupport K w N) ⧸ 𝔪ₑ)
    (WPHead K w N ⧸ 𝔭)

section KappaAlias

variable (𝔭 : Ideal (WPHead K w N))

/-- The residue field of the head at `𝔭`, as a type alias carrying the
SPECTRAL structures only (the raw quotient keeps the quotient-topology
instances; the alias is instance-isolated). -/
def KappaP : Type _ := WPHead K w N ⧸ 𝔭

variable [h𝔭 : 𝔭.IsMaximal]

noncomputable instance : Field (KappaP w N 𝔭) :=
  Ideal.Quotient.field 𝔭
/-- The residue map onto the alias. -/
noncomputable def mkKappaP : WPHead K w N →+* KappaP w N 𝔭 :=
  Ideal.Quotient.mk 𝔭

/-- The constants of the head, viewed in the alias. -/
noncomputable def constKappaP : K →+* KappaP w N 𝔭 :=
  (mkKappaP w N 𝔭).comp (constHead K w N)

noncomputable instance : Algebra K (KappaP w N 𝔭) :=
  (constKappaP w N 𝔭).toAlgebra

/-- The `K`-module structure of the residue field, in the shape the
finite-dimensionality API expects (an `AddCommGroup`-derived scalar
action).  Without it the `Module` search inside `FiniteDimensional K
(KappaP w N 𝔭)` cannot reconcile the two routes through the alias's
`Field` instance. -/
noncomputable instance :
    @Module K (KappaP w N 𝔭) _ (@AddCommGroup.toAddCommMonoid _ inferInstance) :=
  Algebra.toModule

@[simp]
theorem algebraMap_kappaP (c : K) :
    algebraMap K (KappaP w N 𝔭) c = mkKappaP w N 𝔭 (constHead K w N c) :=
  rfl

end KappaAlias

end WeightedParity
