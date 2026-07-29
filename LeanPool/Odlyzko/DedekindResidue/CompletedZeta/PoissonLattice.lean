/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib
public import LeanPool.Odlyzko.DedekindResidue.CompletedZeta.DualLattice
public import LeanPool.Odlyzko.DedekindResidue.CompletedZeta.PoissonSummation

/-!
# Poisson summation over a general `ℤ`-lattice  (SP1-AGP, leaf P.3)

Transport of the `ℤ^ι` Poisson formula (`tsum_eq_tsum_fourier_zpoint`) to an arbitrary
`ℤ`-lattice `L ⊂ EuclideanSpace ℝ ι`: conjugate by the linear equivalence sending the standard
lattice to `L`. The Fourier side transforms by the **`GL` change-of-variables law**
(`fourier_comp_linearEquiv`, new to this development: mathlib only has the isometry case
`Real.fourier_comp_linearIsometry`), the dual lattice appears via `dualZLattice_eq_span`
(P.1), and the covolume factor via `ZLattice.covolume_eq_det_mul_measureReal`.

## Main results (this file)
* `DedekindResidue.fourier_comp_linearEquiv` —
  `𝓕(g ∘ T) w = |det T|⁻¹ • 𝓕 g ((T⁻¹)^* w)` for `T ∈ GL(EuclideanSpace ℝ ι)`.
* `DedekindResidue.tsum_eq_tsum_fourier_zlattice` — **Poisson summation over a `ℤ`-lattice**:
  `∑'_{v ∈ L} g(v) = covol(L)⁻¹ • ∑'_{w ∈ L♯} 𝓕g(w)`.
-/

namespace DedekindResidue

@[expose] public section

open MeasureTheory Complex TopologicalSpace
open scoped FourierTransform

variable {ι : Type*} [Fintype ι]

/-- **Fourier transform under a linear change of variables** (`GL` version; mathlib has only
the isometry case). For an invertible linear `T` on Euclidean space,
`𝓕(g ∘ T) w = |det T|⁻¹ · 𝓕 g ((T⁻¹)^* w)`, by the substitution `v ↦ T⁻¹ v` (Haar scaling
`|det T|⁻¹`) and moving `T⁻¹` across the pairing to its adjoint. -/
theorem fourier_comp_linearEquiv
    (T : EuclideanSpace ℝ ι ≃ₗ[ℝ] EuclideanSpace ℝ ι) (g : EuclideanSpace ℝ ι → ℂ)
    (w : EuclideanSpace ℝ ι) :
    𝓕 (fun v => g (T v)) w
      = |LinearMap.det (T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι)|⁻¹
        • 𝓕 g (LinearMap.adjoint (T.symm : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι) w) := by
  classical
  have hdet : LinearMap.det (T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι) ≠ 0 :=
    (LinearEquiv.isUnit_det' T).ne_zero
  set eT : EuclideanSpace ℝ ι ≃ᵐ EuclideanSpace ℝ ι :=
    T.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv with heT
  have hfun : (⇑eT : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
      = ⇑(T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι) := rfl
  have hmap : Measure.map (⇑eT) (volume : Measure (EuclideanSpace ℝ ι))
      = ENNReal.ofReal |(LinearMap.det (T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι))⁻¹|
        • volume := by
    rw [hfun]
    exact Measure.map_linearMap_addHaar_eq_smul_addHaar volume hdet
  have hsub : ∀ F : EuclideanSpace ℝ ι → ℂ,
      ∫ v, F (T v) = |LinearMap.det (T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι)|⁻¹
        • ∫ y, F y := by
    intro F
    have h1 : ∫ v, F (T v) = ∫ y, F y ∂(Measure.map (⇑eT) volume) :=
      (integral_map_equiv eT F).symm
    rw [h1, hmap, integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _), abs_inv]
  rw [Real.fourier_eq', Real.fourier_eq']
  have key := hsub (fun y => Complex.exp
    ((↑(-2 * Real.pi * inner ℝ (T.symm y) w) : ℂ) * Complex.I) • g y)
  simp only [LinearEquiv.symm_apply_apply] at key
  rw [key]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
  dsimp only
  have hadj : inner ℝ y ((LinearMap.adjoint
        (T.symm : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι)) w)
      = inner ℝ (T.symm y) w := by
    rw [LinearMap.adjoint_inner_right]
    rfl
  rw [hadj]

open LinearMap.BilinForm
open scoped RealInnerProductSpace

/-- Two vectors agreeing against every element of a basis (via the inner product) are equal —
separation through `innerₗ_nondegenerate`. -/
theorem eq_of_inner_basis_eq {x y : EuclideanSpace ℝ ι}
    (c : Module.Basis ι ℝ (EuclideanSpace ℝ ι)) (h : ∀ j, ⟪x, c j⟫ = ⟪y, c j⟫) : x = y := by
  have hz : x - y = 0 := by
    refine (innerₗ_nondegenerate (V := EuclideanSpace ℝ ι)).1 _ (fun z => ?_)
    have hzexp : z = ∑ i, c.repr z i • c i := (c.sum_repr z).symm
    rw [innerₗ_apply_apply, hzexp, inner_sum]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [real_inner_smul_right, inner_sub_left, h i, sub_self, mul_zero]
  exact sub_eq_zero.mp hz

/-- **P3b.** The lattice-basis change of variables sends the integer point `n` to the lattice
element of `L` with `b`-coordinates `n`. -/
theorem latticeEquiv_zpoint (L : Submodule ℤ (EuclideanSpace ℝ ι)) [DiscreteTopology L]
    [IsZLattice ℝ L] (b : Module.Basis ι ℤ L) (n : ι → ℤ) :
    ((EuclideanSpace.basisFun ι ℝ).toBasis.equiv (b.ofZLatticeBasis ℝ) (Equiv.refl ι))
        (zpoint n)
      = ((b.equivFun.symm n : L) : EuclideanSpace ℝ ι) := by
  classical
  set b₀ := (EuclideanSpace.basisFun ι ℝ) with hb₀
  set c := b.ofZLatticeBasis ℝ with hc
  set T := (b₀.toBasis.equiv c (Equiv.refl ι)) with hT
  have hTb : ∀ i, T (b₀.toBasis i) = c i := fun i => by
    rw [hT, Module.Basis.equiv_apply, Equiv.refl_apply]
  have hz : zpoint n = ∑ i, (n i : ℝ) • b₀.toBasis i := by
    ext j
    simp [zpoint, Finset.sum_apply, WithLp.equiv_symm_apply,
      hb₀, EuclideanSpace.basisFun_apply, Pi.single_apply, mul_ite,
      mul_one, mul_zero, Finset.sum_ite_eq]
  have hRHS : ((b.equivFun.symm n : L) : EuclideanSpace ℝ ι) = ∑ i, (n i : ℝ) • c i := by
    rw [Module.Basis.equivFun_symm_apply, Submodule.coe_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [AddSubgroupClass.coe_zsmul, Int.cast_smul_eq_zsmul ℝ,
      ← Module.Basis.ofZLatticeBasis_apply ℝ L b]
  rw [hz, map_sum, hRHS]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_smul, hTb]

/-- **P3c.** The inverse-adjoint of the lattice-basis change of variables sends the integer
point `m` to the element of the dual lattice with dual-basis coordinates `m`. -/
theorem adjoint_symm_latticeEquiv_zpoint [DecidableEq ι]
    (L : Submodule ℤ (EuclideanSpace ℝ ι)) [DiscreteTopology L]
    [IsZLattice ℝ L] (b : Module.Basis ι ℤ L) (m : ι → ℤ) :
    LinearMap.adjoint
        ((((EuclideanSpace.basisFun ι ℝ).toBasis.equiv (b.ofZLatticeBasis ℝ)
          (Equiv.refl ι)).symm : EuclideanSpace ℝ ι ≃ₗ[ℝ] EuclideanSpace ℝ ι) :
          EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι) (zpoint m)
      = ∑ i, (m i : ℝ) • dualBasis (innerₗ (EuclideanSpace ℝ ι)) innerₗ_nondegenerate
          (b.ofZLatticeBasis ℝ) i := by
  classical
  set b₀ := (EuclideanSpace.basisFun ι ℝ) with hb₀
  set c := b.ofZLatticeBasis ℝ with hc
  set T := (b₀.toBasis.equiv c (Equiv.refl ι)) with hT
  set d := dualBasis (innerₗ (EuclideanSpace ℝ ι)) innerₗ_nondegenerate c with hd
  have hTb : ∀ i, T (b₀.toBasis i) = c i := fun i => by
    rw [hT, Module.Basis.equiv_apply, Equiv.refl_apply]
  have hTsymm : ∀ j, T.symm (c j) = b₀.toBasis j := fun j => by
    rw [← hTb j, T.symm_apply_apply]
  refine eq_of_inner_basis_eq c (fun j => ?_)
  have hLHS : ⟪LinearMap.adjoint ((T.symm : EuclideanSpace ℝ ι ≃ₗ[ℝ] EuclideanSpace ℝ ι) :
      EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι) (zpoint m), c j⟫ = (m j : ℝ) := by
    rw [LinearMap.adjoint_inner_left]
    have : ((T.symm : EuclideanSpace ℝ ι ≃ₗ[ℝ] EuclideanSpace ℝ ι) :
        EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι) (c j) = b₀.toBasis j := hTsymm j
    rw [this]
    show ⟪zpoint m, b₀.toBasis j⟫ = (m j : ℝ)
    simp [zpoint, PiLp.inner_apply, WithLp.equiv_symm_apply, hb₀,
      EuclideanSpace.basisFun_apply]
  have hRHS : ⟪∑ i, (m i : ℝ) • d i, c j⟫ = (m j : ℝ) := by
    rw [sum_inner]
    have : ∀ i, ⟪(m i : ℝ) • d i, c j⟫ = (m i : ℝ) * if j = i then 1 else 0 := fun i => by
      rw [real_inner_smul_left]
      congr 1
      have := apply_dualBasis_left (B := innerₗ (EuclideanSpace ℝ ι))
        innerₗ_nondegenerate c i j
      rw [← innerₗ_apply_apply]
      exact this
    simp only [this, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [hLHS, hRHS]

/-- **P3d.** The determinant of the lattice-basis change of variables is (up to sign) the
covolume of the lattice. -/
theorem abs_det_latticeEquiv (L : Submodule ℤ (EuclideanSpace ℝ ι)) [DiscreteTopology L]
    [IsZLattice ℝ L] (b : Module.Basis ι ℤ L) :
    |LinearMap.det (((EuclideanSpace.basisFun ι ℝ).toBasis.equiv
        (b.ofZLatticeBasis ℝ) (Equiv.refl ι) :
        EuclideanSpace ℝ ι ≃ₗ[ℝ] EuclideanSpace ℝ ι) :
        EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι)|
      = ZLattice.covolume L volume := by
  classical
  set b₀ := (EuclideanSpace.basisFun ι ℝ) with hb₀
  set c := b.ofZLatticeBasis ℝ with hc
  set T := (b₀.toBasis.equiv c (Equiv.refl ι)) with hT
  have hTc : ⇑(T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι) ∘ ⇑b₀.toBasis = ⇑c := by
    funext i
    show (b₀.toBasis.equiv c (Equiv.refl ι)) (b₀.toBasis i) = c i
    rw [Module.Basis.equiv_apply, Equiv.refl_apply]
  have hdet : LinearMap.det (T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι)
      = b₀.toBasis.det ⇑c := by
    have := Module.Basis.det_comp b₀.toBasis
      (T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι) ⇑b₀.toBasis
    rw [hTc, Module.Basis.det_self, mul_one] at this
    exact this.symm
  have hcb : (Subtype.val ∘ ⇑b) = ⇑c := by ext i; simp [hc]
  rw [hdet, ZLattice.covolume_eq_det_mul_measureReal (μ := volume) (b := b)
    (b₀ := b₀.toBasis), volumeReal_fundamentalDomain_orthonormal, mul_one, hcb]

/-- **Sup-norm transport.** Restriction norms of translates conjugate cleanly under an
invertible linear map: the translate of `g ∘ T` by `T⁻¹v` on `K` has the same sup-norm as the
translate of `g` by `v` on `T(K)`. -/
theorem norm_restrict_comp_linearEquiv (g : C(EuclideanSpace ℝ ι, ℂ))
    (T : EuclideanSpace ℝ ι ≃ₗ[ℝ] EuclideanSpace ℝ ι) (hTcont : Continuous ⇑T)
    (K : Compacts (EuclideanSpace ℝ ι)) (v : EuclideanSpace ℝ ι) :
    ‖((g.comp ⟨⇑T, hTcont⟩).comp (ContinuousMap.addRight (T.symm v))).restrict (K : Set _)‖
      = ‖(g.comp (ContinuousMap.addRight v)).restrict
          ((K.map ⇑T hTcont : Compacts _) : Set _)‖ := by
  refine le_antisymm ?_ ?_
  · refine (ContinuousMap.norm_le _ (norm_nonneg _)).mpr (fun x => ?_)
    have hmem : T x ∈ (K.map ⇑T hTcont : Compacts (EuclideanSpace ℝ ι)) := ⟨x, x.2, rfl⟩
    have h2 := ContinuousMap.norm_coe_le_norm
      ((g.comp (ContinuousMap.addRight v)).restrict
        ((K.map ⇑T hTcont : Compacts (EuclideanSpace ℝ ι)) : Set _)) ⟨T x, hmem⟩
    have hTx : T (x + T.symm v) = T x + v := by rw [map_add, T.apply_symm_apply]
    calc ‖g (T (x + T.symm v))‖ = ‖g (T x + v)‖ := by rw [hTx]
      _ ≤ _ := h2
  · refine (ContinuousMap.norm_le _ (norm_nonneg _)).mpr (fun y => ?_)
    obtain ⟨x, hxK, hxy⟩ := y.2
    have h2 := ContinuousMap.norm_coe_le_norm
      (((g.comp ⟨⇑T, hTcont⟩).comp (ContinuousMap.addRight (T.symm v))).restrict
        (K : Set _)) ⟨x, hxK⟩
    have hTx : T (x + T.symm v) = T x + v := by rw [map_add, T.apply_symm_apply]
    calc ‖g ((y : EuclideanSpace ℝ ι) + v)‖ = ‖g (T (x + T.symm v))‖ := by rw [hTx, hxy]
      _ ≤ _ := h2

/-- Transport of the local-summability hypothesis through the lattice change of variables:
`ℤ^ι`-translates of `g ∘ T` on `K` are the `L`-translates of `g` on `T(K)`. -/
theorem summable_norm_comp_addRight_zpoint {L : Submodule ℤ (EuclideanSpace ℝ ι)}
    (T : EuclideanSpace ℝ ι ≃ₗ[ℝ] EuclideanSpace ℝ ι) (hTcont : Continuous ⇑T)
    (eL : (ι → ℤ) ≃ L)
    (hTz : ∀ n, T (zpoint n) = ((eL n : L) : EuclideanSpace ℝ ι))
    {g : C(EuclideanSpace ℝ ι, ℂ)}
    (h_norm : ∀ K : Compacts (EuclideanSpace ℝ ι), Summable fun v : L =>
      ‖(g.comp (ContinuousMap.addRight (v : EuclideanSpace ℝ ι))).restrict (K : Set _)‖)
    (K : Compacts (EuclideanSpace ℝ ι)) :
    Summable fun n : ι → ℤ =>
      ‖((g.comp ⟨⇑T, hTcont⟩).comp (ContinuousMap.addRight (zpoint n))).restrict
        (K : Set _)‖ := by
  have hTsz : ∀ n, T.symm ((eL n : L) : EuclideanSpace ℝ ι) = zpoint n :=
    fun n => by rw [← hTz n, T.symm_apply_apply]
  have heq : ∀ n : ι → ℤ,
      ‖((g.comp ⟨⇑T, hTcont⟩).comp (ContinuousMap.addRight (zpoint n))).restrict (K : Set _)‖
      = ‖(g.comp (ContinuousMap.addRight ((eL n : L) : EuclideanSpace ℝ ι))).restrict
          ((K.map ⇑T hTcont : Compacts _) : Set _)‖ := fun n => by
    rw [← hTsz n]
    exact norm_restrict_comp_linearEquiv g T hTcont K _
  have hsummable := (h_norm (K.map ⇑T hTcont)).comp_injective eL.injective
  exact hsummable.congr (fun n => (heq n).symm)

/-- Transport of the Fourier-side summability through the lattice change of variables,
via `fourier_comp_linearEquiv`. -/
theorem summable_fourier_zpoint_of_equiv {L : Submodule ℤ (EuclideanSpace ℝ ι)}
    [DiscreteTopology L] [IsZLattice ℝ L]
    (T : EuclideanSpace ℝ ι ≃ₗ[ℝ] EuclideanSpace ℝ ι) (hTcont : Continuous ⇑T)
    (eD : (ι → ℤ) ≃ dualZLattice L)
    (hadj : ∀ m : ι → ℤ, LinearMap.adjoint
        ((T.symm : EuclideanSpace ℝ ι ≃ₗ[ℝ] EuclideanSpace ℝ ι) :
          EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι) (zpoint m)
      = ((eD m : dualZLattice L) : EuclideanSpace ℝ ι))
    {g : C(EuclideanSpace ℝ ι, ℂ)}
    (h_sum : Summable fun w : dualZLattice L => 𝓕 (⇑g) (w : EuclideanSpace ℝ ι)) :
    Summable fun m : ι → ℤ => 𝓕 (⇑(g.comp ⟨⇑T, hTcont⟩)) (zpoint m) := by
  have h𝓕 : ∀ m : ι → ℤ, 𝓕 (⇑(g.comp ⟨⇑T, hTcont⟩)) (zpoint m)
      = |LinearMap.det (T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι)|⁻¹
        • 𝓕 (⇑g) ((eD m : dualZLattice L) : EuclideanSpace ℝ ι) := by
    intro m
    have hcoe : (⇑(g.comp ⟨⇑T, hTcont⟩) : EuclideanSpace ℝ ι → ℂ) = fun v => g (T v) := rfl
    rw [hcoe, fourier_comp_linearEquiv T (⇑g) (zpoint m), hadj m]
  have h1 := (h_sum.comp_injective eD.injective).const_smul
    |LinearMap.det (T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι)|⁻¹
  exact h1.congr (fun m => (h𝓕 m).symm)

omit [Fintype ι] in
theorem tsum_comp_zpoint_of_equiv {L : Submodule ℤ (EuclideanSpace ℝ ι)}
    (T : EuclideanSpace ℝ ι ≃ₗ[ℝ] EuclideanSpace ℝ ι) (hTcont : Continuous ⇑T)
    (eL : (ι → ℤ) ≃ L)
    (hTz : ∀ n : ι → ℤ, T (zpoint n) = ((eL n : L) : EuclideanSpace ℝ ι))
    (g : C(EuclideanSpace ℝ ι, ℂ)) :
    ∑' n : ι → ℤ, (g.comp ⟨⇑T, hTcont⟩) (zpoint n)
      = ∑' v : L, g (v : EuclideanSpace ℝ ι) := by
  rw [← eL.tsum_eq (f := fun v : L => g (v : EuclideanSpace ℝ ι))]
  exact tsum_congr (fun n => by
    show g (T (zpoint n)) = _
    rw [hTz n])

theorem tsum_fourier_zpoint_of_equiv {L : Submodule ℤ (EuclideanSpace ℝ ι)}
    [DiscreteTopology L] [IsZLattice ℝ L]
    (T : EuclideanSpace ℝ ι ≃ₗ[ℝ] EuclideanSpace ℝ ι) (hTcont : Continuous ⇑T)
    (eD : (ι → ℤ) ≃ dualZLattice L)
    (hadj : ∀ m : ι → ℤ, LinearMap.adjoint
        ((T.symm : EuclideanSpace ℝ ι ≃ₗ[ℝ] EuclideanSpace ℝ ι) :
          EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι) (zpoint m)
      = ((eD m : dualZLattice L) : EuclideanSpace ℝ ι))
    (g : C(EuclideanSpace ℝ ι, ℂ)) :
    ∑' m : ι → ℤ, 𝓕 (⇑(g.comp ⟨⇑T, hTcont⟩)) (zpoint m)
      = |LinearMap.det (T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι)|⁻¹
        • ∑' w : dualZLattice L, 𝓕 (⇑g) (w : EuclideanSpace ℝ ι) := by
  have h𝓕 : ∀ m : ι → ℤ, 𝓕 (⇑(g.comp ⟨⇑T, hTcont⟩)) (zpoint m)
      = |LinearMap.det (T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι)|⁻¹
        • 𝓕 (⇑g) ((eD m : dualZLattice L) : EuclideanSpace ℝ ι) := by
    intro m
    have hcoe : (⇑(g.comp ⟨⇑T, hTcont⟩) : EuclideanSpace ℝ ι → ℂ) = fun v => g (T v) := rfl
    rw [hcoe, fourier_comp_linearEquiv T (⇑g) (zpoint m), hadj m]
  rw [tsum_congr h𝓕, tsum_const_smul'',
    eD.tsum_eq (f := fun w : dualZLattice L => 𝓕 (⇑g) (w : EuclideanSpace ℝ ι))]

open LinearMap.BilinForm in
/-- **Poisson summation over a `ℤ`-lattice** (SP1-AGP P.3). For a `ℤ`-lattice
`L ⊂ EuclideanSpace ℝ ι` and continuous `g` whose `L`-translates are locally summable and
whose Fourier transform is summable over the dual lattice `L♯`,

`∑'_{v ∈ L} g(v) = covol(L)⁻¹ · ∑'_{w ∈ L♯} 𝓕g(w)`.

Proof: conjugate the `ℤ^ι` formula by the lattice-basis change of variables `T`; the sum side
reindexes by `latticeEquiv_zpoint`, the Fourier side by `fourier_comp_linearEquiv` +
`adjoint_symm_latticeEquiv_zpoint` (the inverse-adjoint carries `ℤ^ι` onto `L♯`), and
`|det T| = covol(L)` by `abs_det_latticeEquiv`. -/
theorem tsum_eq_tsum_fourier_zlattice (L : Submodule ℤ (EuclideanSpace ℝ ι))
    [DiscreteTopology L] [IsZLattice ℝ L] {g : C(EuclideanSpace ℝ ι, ℂ)}
    (h_norm : ∀ K : Compacts (EuclideanSpace ℝ ι),
        Summable fun v : L =>
          ‖(g.comp (ContinuousMap.addRight (v : EuclideanSpace ℝ ι))).restrict (K : Set _)‖)
    (h_sum : Summable fun w : dualZLattice L => 𝓕 (⇑g) (w : EuclideanSpace ℝ ι)) :
    ∑' v : L, g (v : EuclideanSpace ℝ ι)
      = (ZLattice.covolume L volume)⁻¹
        • ∑' w : dualZLattice L, 𝓕 (⇑g) (w : EuclideanSpace ℝ ι) := by
  classical
  have := ZLattice.module_finite ℝ L
  have := ZLattice.module_free ℝ L
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ ↥L) = Fintype.card ι := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ L, finrank_euclideanSpace]
  set b : Module.Basis ι ℤ ↥L :=
    (Module.Free.chooseBasis ℤ L).reindex (Fintype.equivOfCardEq hcard) with hb
  set c : Module.Basis ι ℝ (EuclideanSpace ℝ ι) := b.ofZLatticeBasis ℝ with hc
  set d := dualBasis (innerₗ (EuclideanSpace ℝ ι)) innerₗ_nondegenerate c with hd
  set T := ((EuclideanSpace.basisFun ι ℝ).toBasis.equiv c (Equiv.refl ι)) with hT
  have hTcont : Continuous ⇑T :=
    LinearMap.continuous_of_finiteDimensional (T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι)
  set eL : (ι → ℤ) ≃ L := b.equivFun.symm.toEquiv with heL
  have hTz : ∀ n : ι → ℤ, T (zpoint n) = ((eL n : L) : EuclideanSpace ℝ ι) :=
    fun n => latticeEquiv_zpoint L b n
  have hlinind : LinearIndependent ℤ ⇑d :=
    d.linearIndependent.restrict_scalars (by simpa using Int.cast_injective)
  have hspan : Submodule.span ℤ (Set.range ⇑d) = dualZLattice L :=
    (dualZLattice_eq_span L b).symm
  set bs : Module.Basis ι ℤ (Submodule.span ℤ (Set.range ⇑d)) :=
    Module.Basis.span hlinind with hbs
  set eD : (ι → ℤ) ≃ dualZLattice L :=
    (bs.equivFun.symm.toEquiv).trans (LinearEquiv.ofEq _ _ hspan).toEquiv with heD
  have hadj : ∀ m : ι → ℤ, LinearMap.adjoint
      ((T.symm : EuclideanSpace ℝ ι ≃ₗ[ℝ] EuclideanSpace ℝ ι) :
        EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι) (zpoint m)
      = ((eD m : dualZLattice L) : EuclideanSpace ℝ ι) := by
    intro m
    rw [adjoint_symm_latticeEquiv_zpoint L b m]
    show _ = ((LinearEquiv.ofEq _ _ hspan) (bs.equivFun.symm m) : EuclideanSpace ℝ ι)
    rw [LinearEquiv.coe_ofEq_apply, Module.Basis.equivFun_symm_apply, Submodule.coe_sum]
    refine (Finset.sum_congr rfl (fun i _ => ?_)).symm
    rw [AddSubgroupClass.coe_zsmul, hbs, Module.Basis.span_apply, Int.cast_smul_eq_zsmul ℝ]
  have h_norm' := fun K => summable_norm_comp_addRight_zpoint T hTcont eL hTz h_norm K
  have h_sum' := summable_fourier_zpoint_of_equiv T hTcont eD hadj h_sum
  have hmain := tsum_eq_tsum_fourier_zpoint (g := g.comp ⟨⇑T, hTcont⟩) h_norm' h_sum'
  rw [tsum_comp_zpoint_of_equiv T hTcont eL hTz g,
    tsum_fourier_zpoint_of_equiv T hTcont eD hadj g, abs_det_latticeEquiv L b] at hmain
  exact hmain

end

end DedekindResidue
