/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module


public import LeanPool.Nikodym.Nikodym.LowerBound.Algebra.PolynomialDegree
public import LeanPool.Nikodym.Nikodym.LowerBound.Algebra.CoefficientProjection
public import LeanPool.Nikodym.Nikodym.LowerBound.Hilbert.Defs
public import LeanPool.Nikodym.Nikodym.LowerBound.Jets.Defs

/-!
# Base change of polynomial ideals along a field extension

This file implements the items **TR0**, **TR1**, **TR2** and **TR6** of the base-change node
**TR** of `docs/algebra_backend_design.md`.

For a field extension `K ⊆ K'` (an arbitrary `[Algebra K K']` between fields) we write
`P := MvPolynomial (Fin d) K`, `P' := MvPolynomial (Fin d) K'` and
`ι := MvPolynomial.map (algebraMap K K') : P →+* P'`.

* **TR0** `coeffProj π : P' →ₗ[K] P`, the coefficientwise application of a `K`-linear functional
  `π : K' →ₗ[K] K`, with `coeffProj_map`, `coeffProj_map_mul`, `coeffProj_mem_of_mem_map`,
  `totalDegree_coeffProj_le` and the decomposition `exists_sum_smul_map_coeffProj` of an element
  of `P'` along a `K`-basis of `K'`.
* **TR1** `comap_map_eq_self : (I.map ι).comap ι = I`, and the consequences `mem_map_iff`,
  `map_le_map_iff`, `map_injective`, `map_eq_top_iff`, `map_ne_top_iff`, together with
  `totalDegree_map`.
* **TR2** `hilbert_map : hilbert (I.map ι) t = hilbert I t`, `affineHilbertPoly_map` and
  `degree_map`, via the rank–nullity identity `hilbert_add_finrank_inf` and the base change of
  bases `finrank_map_inf_restrictTotalDegree`.
* **TR6** `map_pointIdeal`, `map_jetIdeal`, `jetDim_eq_hilbert` and `jetDim_map`.

All statements are generic in `[Algebra K K']`; they are applied with `K' = RatFunc K` in TR7.
-/

@[expose] public section

namespace Nikodym.LowerBound

open MvPolynomial

variable {K K' : Type*} [Field K] [Field K'] [Algebra K K'] {d : ℕ}

/-- The base-change ring homomorphism `ι : P → P'`, `MvPolynomial.map (algebraMap K K')`. -/
local notation "ι" => (MvPolynomial.map (algebraMap K K') :
  MvPolynomial (Fin d) K →+* MvPolynomial (Fin d) K')

/-! ### TR0: coefficient projection along a `K`-linear functional -/



/-! ### TR1: the extension of ideals is injective -/

section Comap

/-- Blueprint TR1: `(I.map ι).comap ι = I`. -/
theorem comap_map_eq_self (I : Ideal (MvPolynomial (Fin d) K)) : (I.map ι).comap ι = I := by
  obtain ⟨π, hπ⟩ := Module.Projective.exists_dual_eq_one K (one_ne_zero : (1 : K') ≠ 0)
  refine le_antisymm (fun f hf ↦ ?_) Ideal.le_comap_map
  rw [Ideal.mem_comap] at hf
  have h := coeffProj_mem_of_mem_map π I hf
  rwa [coeffProj_map hπ] at h

/-- Blueprint TR1: `ι f ∈ I.map ι ↔ f ∈ I`. -/
theorem mem_map_iff (I : Ideal (MvPolynomial (Fin d) K)) (f : MvPolynomial (Fin d) K) :
    ι f ∈ I.map ι ↔ f ∈ I := by
  rw [← Ideal.mem_comap, comap_map_eq_self]

/-- Blueprint TR1: `I.map ι ≤ J.map ι ↔ I ≤ J`. -/
theorem map_le_map_iff (I J : Ideal (MvPolynomial (Fin d) K)) : I.map ι ≤ J.map ι ↔ I ≤ J := by
  refine ⟨fun h ↦ ?_, Ideal.map_mono⟩
  have h' := Ideal.comap_mono (f := ι) h
  rwa [comap_map_eq_self, comap_map_eq_self] at h'

/-- Blueprint TR1: `I ↦ I.map ι` is injective. -/
theorem map_injective :
    Function.Injective
      (Ideal.map ι : Ideal (MvPolynomial (Fin d) K) → Ideal (MvPolynomial (Fin d) K')) :=
  fun I J h ↦ le_antisymm ((map_le_map_iff I J).mp h.le) ((map_le_map_iff J I).mp h.ge)

/-- Blueprint TR1: `I.map ι = ⊤ ↔ I = ⊤`. -/
theorem map_eq_top_iff (I : Ideal (MvPolynomial (Fin d) K)) : I.map ι = ⊤ ↔ I = ⊤ := by
  rw [← Ideal.map_top ι]
  exact map_injective.eq_iff

/-- Blueprint TR1: `I.map ι ≠ ⊤ ↔ I ≠ ⊤`. -/
theorem map_ne_top_iff (I : Ideal (MvPolynomial (Fin d) K)) : I.map ι ≠ ⊤ ↔ I ≠ ⊤ :=
  (map_eq_top_iff I).not

/-- Blueprint TR1: `ι` preserves the total degree. -/
theorem totalDegree_map (f : MvPolynomial (Fin d) K) : (ι f).totalDegree = f.totalDegree := by
  rw [totalDegree, totalDegree, support_map_of_injective _ (algebraMap K K').injective]

end Comap

/-! ### TR2: the Hilbert function is invariant under base change -/

section Hilbert

/-- Blueprint TR2: rank–nullity for the restriction of `P → P ⧸ I` to `P_{≤t}`:
`hilbert I t + dim_K (I ⊓ P_{≤t}) = (t + d).choose d`. -/
theorem hilbert_add_finrank_inf (I : Ideal (MvPolynomial (Fin d) K)) (t : ℕ) :
    hilbert I t + Module.finrank K (I.restrictScalars K ⊓ restrictTotalDegree (Fin d) K t :
      Submodule K (MvPolynomial (Fin d) K)) = (t + d).choose d := by
  set W := restrictTotalDegree (Fin d) K t with hW
  set φ := (Ideal.Quotient.mkₐ K I).toLinearMap.domRestrict W with hφ
  have h := LinearMap.finrank_range_add_finrank_ker φ
  rw [hφ, LinearMap.range_domRestrict, hW, finrank_restrictTotalDegree] at h
  have hker : LinearMap.ker φ = (I.restrictScalars K ⊓ W).comap W.subtype := by
    ext ⟨f, hf⟩
    simp only [hφ, LinearMap.mem_ker, LinearMap.domRestrict_apply, AlgHom.toLinearMap_apply,
      Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem, Submodule.mem_comap,
      Submodule.subtype_apply, Submodule.mem_inf, Submodule.restrictScalars_mem]
    exact ⟨fun h ↦ ⟨h, hf⟩, fun h ↦ h.1⟩
  rw [hker, (Submodule.comapSubtypeEquivOfLe inf_le_right).finrank_eq] at h
  rw [hilbert, restrictionSpace]
  exact h

/-- Blueprint TR2: the `K'`-dimension of `(I.map ι) ⊓ P'_{≤t}` equals the `K`-dimension of
`I ⊓ P_{≤t}`: the base change of a `K`-basis of the latter is a `K'`-basis of the former. -/
theorem finrank_map_inf_restrictTotalDegree (I : Ideal (MvPolynomial (Fin d) K)) (t : ℕ) :
    Module.finrank K' ((I.map ι).restrictScalars K' ⊓ restrictTotalDegree (Fin d) K' t :
        Submodule K' (MvPolynomial (Fin d) K')) =
      Module.finrank K (I.restrictScalars K ⊓ restrictTotalDegree (Fin d) K t :
        Submodule K (MvPolynomial (Fin d) K)) := by
  classical
  set V : Submodule K (MvPolynomial (Fin d) K) :=
    I.restrictScalars K ⊓ restrictTotalDegree (Fin d) K t with hV
  set V' : Submodule K' (MvPolynomial (Fin d) K') :=
    (I.map ι).restrictScalars K' ⊓ restrictTotalDegree (Fin d) K' t with hV'
  have : FiniteDimensional K V := Submodule.finiteDimensional_of_le inf_le_right
  let b := Module.Free.chooseBasis K V
  let v : Module.Free.ChooseBasisIndex K V → MvPolynomial (Fin d) K' := fun j ↦ ι (b j : _)
  have hv : ∀ j, v j = ι (b j : MvPolynomial (Fin d) K) := fun j ↦ rfl
  -- linear independence of the base-changed basis
  have hli : LinearIndependent K' v := by
    rw [linearIndependent_iff']
    intro s g hg i hi
    rw [← Module.forall_dual_apply_eq_zero_iff K (g i)]
    intro π
    have h1 : coeffProj π (∑ j ∈ s, g j • v j) =
        ∑ j ∈ s, π (g j) • (b j : MvPolynomial (Fin d) K) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [smul_eq_C_mul, mul_comm (C (g j)), hv, coeffProj_map_mul, coeffProj_C, mul_comm,
        ← smul_eq_C_mul]
    rw [hg, map_zero] at h1
    have h2 : ∑ j ∈ s, π (g j) • b j = (0 : V) := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      simp only [Submodule.coe_smul]
      exact h1.symm
    exact linearIndependent_iff'.mp b.linearIndependent s (fun j ↦ π (g j)) h2 i hi
  -- the base-changed basis lies in `V'`
  have hmem : ∀ j, v j ∈ V' := fun j ↦ by
    have hj := Submodule.mem_inf.mp (b j).2
    refine Submodule.mem_inf.mpr ⟨Ideal.mem_map_of_mem ι hj.1, ?_⟩
    rw [mem_restrictTotalDegree_iff, totalDegree_map]
    exact mem_restrictTotalDegree_iff.mp hj.2
  -- `ι` maps `V` into the `K'`-span of the base-changed basis
  have hιV : ∀ w : V, ι (w : MvPolynomial (Fin d) K) ∈ Submodule.span K' (Set.range v) := by
    intro w
    have hw : (w : MvPolynomial (Fin d) K) = ∑ j, b.repr w j • (b j : MvPolynomial (Fin d) K) := by
      conv_lhs => rw [← b.sum_repr w]
      rw [Submodule.coe_sum]
      simp only [Submodule.coe_smul]
    rw [hw, map_sum]
    refine Submodule.sum_mem _ fun j _ ↦ ?_
    rw [smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  -- the base-changed basis spans `V'`
  have hspan : Submodule.span K' (Set.range v) = V' := by
    refine le_antisymm (Submodule.span_le.mpr (Set.range_subset_iff.mpr hmem)) fun g' hg' ↦ ?_
    obtain ⟨hgI, hgt⟩ := Submodule.mem_inf.mp hg'
    obtain ⟨s, hs⟩ := exists_sum_smul_map_coeffProj (Module.Free.chooseBasis K K') g'
    rw [hs]
    refine Submodule.sum_mem _ fun j _ ↦ Submodule.smul_mem _ _ ?_
    have hw : coeffProj ((Module.Free.chooseBasis K K').coord j) g' ∈ V :=
      Submodule.mem_inf.mpr ⟨coeffProj_mem_of_mem_map _ I hgI,
        mem_restrictTotalDegree_iff.mpr
          ((totalDegree_coeffProj_le _ g').trans (mem_restrictTotalDegree_iff.mp hgt))⟩
    exact hιV ⟨_, hw⟩
  rw [← hspan, finrank_span_eq_card hli, Module.finrank_eq_card_basis b]

/-- Blueprint TR2: the Hilbert function is invariant under base change,
`hilbert (I.map ι) t = hilbert I t`. -/
theorem hilbert_map (I : Ideal (MvPolynomial (Fin d) K)) (t : ℕ) :
    hilbert (I.map ι) t = hilbert I t := by
  have h1 := hilbert_add_finrank_inf (I.map ι) t
  have h2 := hilbert_add_finrank_inf I t
  rw [finrank_map_inf_restrictTotalDegree] at h1
  omega

/-- Blueprint TR2: the affine Hilbert polynomial is invariant under base change. -/
theorem affineHilbertPoly_map (I : Ideal (MvPolynomial (Fin d) K)) :
    affineHilbertPoly (I.map ι) = affineHilbertPoly I := by
  have h : hilbert (I.map ι) = hilbert I := funext (hilbert_map I)
  unfold affineHilbertPoly
  rw [h]

/-- Blueprint TR2: the degree is invariant under base change. -/
theorem degree_map (I : Ideal (MvPolynomial (Fin d) K)) : degree (I.map ι) = degree I := by
  unfold degree
  rw [affineHilbertPoly_map]

end Hilbert

/-! ### TR6: point ideals, jet ideals and jet dimensions under base change -/

section Jets

/-- Blueprint TR6: the base change of the point ideal of `x` is the point ideal of the image
point `fun i ↦ algebraMap K K' (x i)`. -/
theorem map_pointIdeal (x : Fin d → K) :
    (pointIdeal x).map ι = pointIdeal (fun i ↦ algebraMap K K' (x i)) := by
  rw [pointIdeal_eq_span, pointIdeal_eq_span, Ideal.map_span, ← Set.range_comp]
  congr 2
  funext i
  simp only [Function.comp_apply, map_sub, map_X, map_C]

/-- Blueprint TR6: base change of jet ideals. -/
theorem map_jetIdeal (I : Ideal (MvPolynomial (Fin d) K)) (x : Fin d → K) (r : ℕ) :
    (jetIdeal I x r).map ι = jetIdeal (I.map ι) (fun i ↦ algebraMap K K' (x i)) r := by
  rw [jetIdeal, jetIdeal, Ideal.map_sup, Ideal.map_pow, map_pointIdeal]

/-- Blueprint TR6 (auxiliary): translation does not increase the total degree. -/
theorem totalDegree_translate_le (x : Fin d → K) (g : MvPolynomial (Fin d) K) :
    (translate x g).totalDegree ≤ g.totalDegree := by
  rw [translate_apply]
  exact totalDegree_aeval_le_of_totalDegree_le_one
    (fun i ↦ (totalDegree_sub_C_le _ _).trans (totalDegree_X i).le) g

/-- Blueprint TR6: if `𝔪ₓ ^ r ≤ J`, then `P ⧸ J` is spanned by the classes of the polynomials of
total degree at most `r - 1`, i.e. `V_J(r - 1) = ⊤`. -/
theorem restrictionSpace_eq_top_of_pointIdeal_pow_le {J : Ideal (MvPolynomial (Fin d) K)}
    {x : Fin d → K} {r : ℕ} (hJ : pointIdeal x ^ r ≤ J) :
    restrictionSpace J (r - 1) = ⊤ := by
  rw [eq_top_iff]
  rintro v -
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective v
  set J' := J.comap (translate x : MvPolynomial (Fin d) K →+* MvPolynomial (Fin d) K) with hJ'
  have hJ'r : idealOfVars (Fin d) K ^ r ≤ J' := by
    rw [hJ', ← Ideal.map_le_iff_le_comap, ← pointIdeal_pow_eq_map]
    exact hJ
  have hmem : Ideal.Quotient.mk J' ((translate x).symm f) ∈
      (restrictTotalDegree (Fin d) K (r - 1)).map (Ideal.Quotient.mkₐ K J').toLinearMap := by
    rw [map_restrictTotalDegree_eq_top_of_pow_idealOfVars_le hJ'r]
    trivial
  obtain ⟨g, hg, hgf⟩ := Submodule.mem_map.mp hmem
  have h1 : Ideal.Quotient.mk J' ((translate x).symm f) = Ideal.Quotient.mk J' g := hgf.symm
  have h2 : (translate x).symm f - g ∈ J' := Ideal.Quotient.eq.mp h1
  rw [hJ', Ideal.mem_comap, RingHom.coe_coe, map_sub, AlgEquiv.apply_symm_apply] at h2
  rw [Ideal.Quotient.eq.mpr h2]
  exact mem_restrictionSpace_mk
    ((totalDegree_translate_le x g).trans (mem_restrictTotalDegree_iff.mp hg))

/-- Blueprint TR6: the jet dimension is the Hilbert function of the jet ideal at `r - 1`,
`jetDim I x r = hilbert (jetIdeal I x r) (r - 1)`. (The hypothesis `1 ≤ r` is part of the
blueprint statement; it is not needed for the proof.) -/
theorem jetDim_eq_hilbert (I : Ideal (MvPolynomial (Fin d) K)) (x : Fin d → K) {r : ℕ}
    (_hr : 1 ≤ r) : jetDim I x r = hilbert (jetIdeal I x r) (r - 1) := by
  rw [jetDim, hilbert,
    restrictionSpace_eq_top_of_pointIdeal_pow_le (pointIdeal_pow_le_jetIdeal I x r), finrank_top]

/-- Blueprint TR6: the jet dimension is invariant under base change. -/
theorem jetDim_map (I : Ideal (MvPolynomial (Fin d) K)) (x : Fin d → K) {r : ℕ} (hr : 1 ≤ r) :
    jetDim (I.map ι) (fun i ↦ algebraMap K K' (x i)) r = jetDim I x r := by
  rw [jetDim_eq_hilbert _ _ hr, jetDim_eq_hilbert _ _ hr, ← map_jetIdeal, hilbert_map]

end Jets

end Nikodym.LowerBound

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
