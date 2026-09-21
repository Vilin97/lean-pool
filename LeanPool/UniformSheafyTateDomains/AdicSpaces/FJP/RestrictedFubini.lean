/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.RestrictedGaussAdic
import LeanPool.UniformSheafyTateDomains.AdicSpaces.Vendored.XiaMvPowerSeriesEquiv
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WP.ZeroHeadTate
import Mathlib.RingTheory.MvPowerSeries.Rename

/-!
# The restricted Fubini: `K⟨X₁..X_{k+m}⟩ ≅ (K⟨X₁..X_m⟩)⟨T₁..T_k⟩`

([hrw-decomposition] the T_N⟨T⟩-tower leaf for `comap_headToQ_isMaximal`.)
Radius-one restricted power series in a sum of variables are restricted
power series with restricted coefficients: Xia's `sumAlgEquiv` at the
underlying series level, with the Gauss decay transported through the
sup-norm identity in both directions.  Composed with the `Fin`-sum rename,
this identifies the `k`-th Tate extension of a Tate algebra with a Tate
algebra, funneling the tower Nullstellensatz into `module_finite_residue`.

Both Gauss-transport legs (`isRestrictedGauss_sumToRestrictedFun`,
`isRestrictedGauss_iterToSum`) are proven; the file is sorry-free and axiom-clean.
-/

@[expose] public section

namespace FiniteJet.GraphKoszul

open MvPowerSeries

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [CompleteSpace K]

/-- Double embedding along an equivalence and its inverse is the identity. -/
theorem embDomain_symm_embDomain {σ τ : Type*} (e : σ ≃ τ) (t : τ →₀ ℕ) :
    Finsupp.embDomain e.toEmbedding
      (Finsupp.embDomain e.symm.toEmbedding t) = t := by
  rw [Finsupp.embDomain_eq_mapDomain, Finsupp.embDomain_eq_mapDomain,
    ← Finsupp.mapDomain_comp]
  refine (Finsupp.mapDomain_congr ?_).trans Finsupp.mapDomain_id
  intro a _
  exact e.apply_symm_apply a

/-- Coefficients of a rename along an equivalence. -/
theorem coeff_rename_equiv {σ τ : Type*} (e : σ ≃ τ)
    (F : MvPowerSeries σ K) (t : τ →₀ ℕ) :
    MvPowerSeries.coeff t (MvPowerSeries.rename (⇑e) F) =
      MvPowerSeries.coeff (Finsupp.embDomain e.symm.toEmbedding t) F := by
  conv_lhs => rw [← embDomain_symm_embDomain e t]
  exact MvPowerSeries.coeff_embDomain_rename e.toEmbedding F _

/-- Renaming along an equivalence preserves radius-one restrictedness. -/
theorem isRestrictedGauss_rename_equiv {σ τ : Type*} (e : σ ≃ τ)
    (F : MvPowerSeries σ K)
    (hF : MvPowerSeries.IsRestrictedGauss (fun _ : σ => (1 : ℝ)) F) :
    MvPowerSeries.IsRestrictedGauss (fun _ : τ => (1 : ℝ))
      (MvPowerSeries.rename e F) := by
  rw [WeightedParity.isRestrictedGauss_one_iff] at hF ⊢
  rw [funext (coeff_rename_equiv e F)]
  exact hF.comp (Finsupp.embDomain_injective _).tendsto_cofinite

/-- The restricted rename homomorphism along an equivalence. -/
noncomputable def restrictedRenameHom {σ τ : Type*} (e : σ ≃ τ) :
    MvPowerSeries.Restricted K (fun _ : σ => (1 : ℝ)) →+*
      MvPowerSeries.Restricted K (fun _ : τ => (1 : ℝ)) where
  toFun F := ⟨MvPowerSeries.rename e F.1,
    isRestrictedGauss_rename_equiv e F.1 F.2⟩
  map_one' := Subtype.ext
    (map_one (MvPowerSeries.rename (R := K) (⇑e)))
  map_mul' F G := Subtype.ext
    (map_mul (MvPowerSeries.rename (R := K) (⇑e)) F.1 G.1)
  map_zero' := Subtype.ext
    (map_zero (MvPowerSeries.rename (R := K) (⇑e)))
  map_add' F G := Subtype.ext
    (map_add (MvPowerSeries.rename (R := K) (⇑e)) F.1 G.1)

/-- Radius-one restricted series transport along an index equivalence. -/
noncomputable def restrictedRenameEquiv {σ τ : Type*} (e : σ ≃ τ) :
    MvPowerSeries.Restricted K (fun _ : σ => (1 : ℝ)) ≃+*
      MvPowerSeries.Restricted K (fun _ : τ => (1 : ℝ)) :=
  RingEquiv.ofRingHom (restrictedRenameHom e) (restrictedRenameHom e.symm)
    (RingHom.ext fun F => Subtype.ext (by
      show MvPowerSeries.rename (⇑e)
        (MvPowerSeries.rename (⇑e.symm) F.1) = F.1
      refine MvPowerSeries.ext fun t => ?_
      rw [coeff_rename_equiv e]
      exact MvPowerSeries.coeff_embDomain_rename e.symm.toEmbedding F.1 t))
    (RingHom.ext fun F => Subtype.ext (by
      show MvPowerSeries.rename (⇑e.symm)
        (MvPowerSeries.rename (⇑e) F.1) = F.1
      refine MvPowerSeries.ext fun t => ?_
      rw [coeff_rename_equiv e.symm, Equiv.symm_symm]
      exact MvPowerSeries.coeff_embDomain_rename e.toEmbedding F.1 t))

/-- Generic radius-one decay criterion (any normed coefficient ring). -/
theorem isRestrictedGauss_one_iff' {R : Type*} [NormedRing R] {σ : Type*}
    (f : MvPowerSeries σ R) :
    MvPowerSeries.IsRestrictedGauss (fun _ : σ => (1 : ℝ)) f ↔
      Filter.Tendsto (fun t : σ →₀ ℕ => MvPowerSeries.coeff t f)
        Filter.cofinite (nhds 0) := by
  have hp : (fun t : σ →₀ ℕ =>
      ‖MvPowerSeries.coeff t f‖ * t.prod ((fun _ : σ => (1 : ℝ)) · ^ ·)) =
      fun t : σ →₀ ℕ => ‖MvPowerSeries.coeff t f‖ := by
    funext t
    rw [show t.prod ((fun _ : σ => (1 : ℝ)) · ^ ·) = 1 from by
      simp [Finsupp.prod], mul_one]
  rw [MvPowerSeries.IsRestrictedGauss, hp,
    ← tendsto_zero_iff_norm_tendsto_zero]

/-- The underlying coefficient inclusion of the Tate algebra. -/
noncomputable def pValHom (m : ℕ) : P K m →+* MvPowerSeries (Fin m) K where
  toFun x := x.1
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem pValHom_injective (m : ℕ) :
    Function.Injective (pValHom (K := K) m) :=
  fun _ _ h => Subtype.ext h

/-- The forward sum transport: outer series with restricted coefficients. -/
noncomputable def sumToRestrictedFun (m k : ℕ)
    (F : MvPowerSeries.Restricted K (fun _ : Fin k ⊕ Fin m => (1 : ℝ))) :
    MvPowerSeries (Fin k) (P K m) := fun y =>
  ⟨MvPowerSeries.coeff y
    (MvPowerSeries.sumToIter (Fin k) (Fin m) K F.1), by
    show MvPowerSeries.IsRestrictedGauss _ _
    rw [isRestrictedGauss_one_iff']
    have hF := (isRestrictedGauss_one_iff' F.1).mp F.2
    have hinj : Function.Injective
        (fun x : Fin m →₀ ℕ => Finsupp.sumElim y x) := by
      intro x₁ x₂ h
      have h2 := congrArg (fun u : Fin k ⊕ Fin m →₀ ℕ =>
        Finsupp.comapDomain Sum.inr u Sum.inr_injective.injOn) h
      simpa [Finsupp.comapDomain_inr_sumElim] using h2
    have hpt : ∀ x : Fin m →₀ ℕ,
        MvPowerSeries.coeff x (MvPowerSeries.coeff y
          (MvPowerSeries.sumToIter (Fin k) (Fin m) K F.1)) =
        MvPowerSeries.coeff (Finsupp.sumElim y x) F.1 := fun x =>
      MvPowerSeries.coeff_sumToIter y x F.1
    rw [funext hpt]
    exact hF.comp hinj.tendsto_cofinite⟩

/-- The forward sum transport has restricted coefficients decaying in the
sup norm. -/
theorem isRestrictedGauss_sumToRestrictedFun (m k : ℕ)
    (F : MvPowerSeries.Restricted K (fun _ : Fin k ⊕ Fin m => (1 : ℝ))) :
    MvPowerSeries.IsRestrictedGauss (fun _ : Fin k => (1 : ℝ))
      (sumToRestrictedFun m k F) := by
  rw [isRestrictedGauss_one_iff']
  refine Filter.tendsto_def.mpr fun U hU => ?_
  rw [Filter.mem_cofinite]
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
  have hFdecay := (isRestrictedGauss_one_iff' F.1).mp F.2
  have hS : {p : Fin k ⊕ Fin m →₀ ℕ |
      ¬ ‖MvPowerSeries.coeff p F.1‖ < ε / 2}.Finite := by
    have h2 := Filter.tendsto_def.mp hFdecay (Metric.ball 0 (ε / 2))
      (Metric.ball_mem_nhds 0 (by positivity))
    rw [Filter.mem_cofinite] at h2
    refine h2.subset ?_
    intro p hp
    simp only [Set.mem_compl_iff, Set.mem_preimage, Metric.mem_ball,
      dist_zero_right] at hp ⊢
    exact hp
  refine Set.Finite.subset (Set.Finite.image
    (fun p : Fin k ⊕ Fin m →₀ ℕ =>
      Finsupp.comapDomain Sum.inl p Sum.inl_injective.injOn) hS) ?_
  intro y hy
  simp only [Set.mem_compl_iff, Set.mem_preimage] at hy
  have hnorm : ε ≤
      ‖MvPowerSeries.coeff y (sumToRestrictedFun m k F)‖ := by
    by_contra hlt
    push_neg at hlt
    refine hy (hball ?_)
    simpa [Metric.mem_ball, dist_zero_right] using hlt
  by_cases hex : ∃ x : Fin m →₀ ℕ, ε / 2 ≤
      ‖MvPowerSeries.coeff (Finsupp.sumElim y x) F.1‖
  · obtain ⟨x, hx⟩ := hex
    refine ⟨Finsupp.sumElim y x, ?_, ?_⟩
    · simp only [Set.mem_setOf_eq]
      exact not_lt.mpr hx
    · show Finsupp.comapDomain Sum.inl (Finsupp.sumElim y x)
        Sum.inl_injective.injOn = y
      exact Finsupp.comapDomain_inl_sumElim y x
  · push_neg at hex
    exfalso
    rw [MvRestricted.norm_eq] at hnorm
    have hbound : MvPowerSeries.gaussNorm (norm : K → ℝ)
        (fun _ : Fin m => (1 : ℝ))
        (MvPowerSeries.coeff y (sumToRestrictedFun m k F)).1 ≤ ε / 2 := by
      rw [MvPowerSeries.gaussNorm]
      refine Real.iSup_le (fun x => ?_) (by positivity)
      have h3 : (x.prod ((fun _ : Fin m => (1 : ℝ)) · ^ ·)) = 1 := by
        simp [Finsupp.prod]
      rw [h3, mul_one]
      have h4 : MvPowerSeries.coeff x
          (MvPowerSeries.coeff y (sumToRestrictedFun m k F)).1 =
          MvPowerSeries.coeff (Finsupp.sumElim y x) F.1 :=
        MvPowerSeries.coeff_sumToIter y x F.1
      rw [h4]
      exact (hex x).le
    linarith

theorem map_pValHom_sumToRestrictedFun (m k : ℕ)
    (F : MvPowerSeries.Restricted K (fun _ : Fin k ⊕ Fin m => (1 : ℝ))) :
    MvPowerSeries.map (pValHom m) (sumToRestrictedFun m k F) =
      MvPowerSeries.sumToIter (Fin k) (Fin m) K F.1 :=
  MvPowerSeries.ext fun y => by
    rw [MvPowerSeries.coeff_map]
    rfl

/-- The inverse transport preserves radius-one restrictedness. -/
theorem isRestrictedGauss_iterToSum (m k : ℕ)
    (G : MvPowerSeries.Restricted (P K m) (fun _ : Fin k => (1 : ℝ))) :
    MvPowerSeries.IsRestrictedGauss (fun _ : Fin k ⊕ Fin m => (1 : ℝ))
      ((MvPowerSeries.sumAlgEquiv (Fin k) (Fin m) K).symm
        (MvPowerSeries.map (pValHom m) G.1)) := by
  rw [isRestrictedGauss_one_iff']
  refine Filter.tendsto_def.mpr fun U hU => ?_
  rw [Filter.mem_cofinite]
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
  have hGdecay := (isRestrictedGauss_one_iff' G.1).mp G.2
  have hO : {y : Fin k →₀ ℕ |
      ¬ ‖MvPowerSeries.coeff y G.1‖ < ε}.Finite := by
    have h2 := Filter.tendsto_def.mp hGdecay (Metric.ball 0 ε)
      (Metric.ball_mem_nhds 0 hε)
    rw [Filter.mem_cofinite] at h2
    refine h2.subset ?_
    intro y hy
    simp only [Set.mem_compl_iff, Set.mem_preimage, Metric.mem_ball,
      dist_zero_right] at hy ⊢
    exact hy
  have hpt : ∀ p : Fin k ⊕ Fin m →₀ ℕ,
      MvPowerSeries.coeff p
        ((MvPowerSeries.sumAlgEquiv (Fin k) (Fin m) K).symm
          (MvPowerSeries.map (pValHom m) G.1)) =
      MvPowerSeries.coeff
        (Finsupp.comapDomain Sum.inr p Sum.inr_injective.injOn)
        (MvPowerSeries.coeff
          (Finsupp.comapDomain Sum.inl p Sum.inl_injective.injOn)
          G.1).1 := by
    intro p
    rw [MvPowerSeries.coeff_sumAlgEquiv_symm_apply,
      MvPowerSeries.coeff_map]
    rfl
  have hIy : ∀ y : Fin k →₀ ℕ, {x : Fin m →₀ ℕ |
      ¬ ‖MvPowerSeries.coeff x
        (MvPowerSeries.coeff y G.1).1‖ < ε}.Finite := by
    intro y
    have hres := (isRestrictedGauss_one_iff'
      ((MvPowerSeries.coeff y G.1).1)).mp (MvPowerSeries.coeff y G.1).2
    have h2 := Filter.tendsto_def.mp hres (Metric.ball 0 ε)
      (Metric.ball_mem_nhds 0 hε)
    rw [Filter.mem_cofinite] at h2
    refine h2.subset ?_
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_preimage, Metric.mem_ball,
      dist_zero_right] at hx ⊢
    exact hx
  refine Set.Finite.subset (Set.Finite.biUnion hO fun y _ =>
    Set.Finite.image (fun x : Fin m →₀ ℕ => Finsupp.sumElim y x)
      (hIy y)) ?_
  intro p hp
  simp only [Set.mem_compl_iff, Set.mem_preimage] at hp
  set y := Finsupp.comapDomain Sum.inl p Sum.inl_injective.injOn with hydef
  set x := Finsupp.comapDomain Sum.inr p Sum.inr_injective.injOn with hxdef
  have hval : ε ≤ ‖MvPowerSeries.coeff x
      (MvPowerSeries.coeff y G.1).1‖ := by
    by_contra hlt
    push_neg at hlt
    refine hp (hball ?_)
    rw [Metric.mem_ball, dist_zero_right, hpt p]
    exact hlt
  have hyO : y ∈ {y : Fin k →₀ ℕ |
      ¬ ‖MvPowerSeries.coeff y G.1‖ < ε} := by
    simp only [Set.mem_setOf_eq, not_lt]
    calc ε ≤ ‖MvPowerSeries.coeff x (MvPowerSeries.coeff y G.1).1‖ := hval
      _ ≤ ‖MvPowerSeries.coeff y G.1‖ := by
        rw [MvRestricted.norm_eq]
        have h5 := MvPowerSeries.le_gaussNorm
          (v := (norm : K → ℝ)) (c := fun _ : Fin m => (1 : ℝ))
          (f := (MvPowerSeries.coeff y G.1).1)
          (MvRestricted.hasGaussNorm _ _) x
        rw [show (x.prod ((fun _ : Fin m => (1 : ℝ)) · ^ ·)) = 1 from by
          simp [Finsupp.prod], mul_one] at h5
        exact h5
  refine Set.mem_biUnion hyO ?_
  refine ⟨x, ?_, ?_⟩
  · simp only [Set.mem_setOf_eq, not_lt]
    exact hval
  · show Finsupp.sumElim
      (Finsupp.comapDomain Sum.inl p Sum.inl_injective.injOn)
      (Finsupp.comapDomain Sum.inr p Sum.inr_injective.injOn) = p
    exact Finsupp.comapDomain_sumElim_comapDomain p

/-- **The restricted sum–iterate transport**: restricted series in a sum of
variables are restricted series with restricted coefficients. -/
noncomputable def restrictedSumEquiv (m k : ℕ) :
    MvPowerSeries.Restricted K (fun _ : Fin k ⊕ Fin m => (1 : ℝ)) ≃+*
      MvPowerSeries.Restricted (P K m) (fun _ : Fin k => (1 : ℝ)) where
  toFun F := ⟨sumToRestrictedFun m k F,
    isRestrictedGauss_sumToRestrictedFun m k F⟩
  invFun G := ⟨(MvPowerSeries.sumAlgEquiv (Fin k) (Fin m) K).symm
      (MvPowerSeries.map (pValHom m) G.1),
    isRestrictedGauss_iterToSum m k G⟩
  left_inv F := Subtype.ext (by
    show (MvPowerSeries.sumAlgEquiv (Fin k) (Fin m) K).symm
      (MvPowerSeries.map (pValHom m) (sumToRestrictedFun m k F)) = F.1
    rw [map_pValHom_sumToRestrictedFun]
    exact AlgEquiv.symm_apply_apply _ F.1)
  right_inv G := Subtype.ext (MvPowerSeries.ext fun y => Subtype.ext (by
    show MvPowerSeries.coeff y (MvPowerSeries.sumToIter (Fin k) (Fin m) K
      ((MvPowerSeries.sumAlgEquiv (Fin k) (Fin m) K).symm
        (MvPowerSeries.map (pValHom m) G.1))) =
      (MvPowerSeries.coeff y G.1).1
    have h1 : MvPowerSeries.sumToIter (Fin k) (Fin m) K
        ((MvPowerSeries.sumAlgEquiv (Fin k) (Fin m) K).symm
          (MvPowerSeries.map (pValHom m) G.1)) =
        MvPowerSeries.map (pValHom m) G.1 := by
      show (MvPowerSeries.sumAlgEquiv (Fin k) (Fin m) K)
        ((MvPowerSeries.sumAlgEquiv (Fin k) (Fin m) K).symm
          (MvPowerSeries.map (pValHom m) G.1)) =
        MvPowerSeries.map (pValHom m) G.1
      exact AlgEquiv.apply_symm_apply _ _
    rw [h1, MvPowerSeries.coeff_map]
    rfl))
  map_mul' F G := Subtype.ext (MvPowerSeries.map_injective
    (pValHom_injective m) (by
      show MvPowerSeries.map (pValHom m)
        (sumToRestrictedFun m k (F * G)) =
        MvPowerSeries.map (pValHom m)
          (sumToRestrictedFun m k F * sumToRestrictedFun m k G)
      rw [map_pValHom_sumToRestrictedFun,
        show ((F * G : MvPowerSeries.Restricted K
          (fun _ : Fin k ⊕ Fin m => (1 : ℝ)))).1 = F.1 * G.1 from rfl,
        _root_.map_mul, _root_.map_mul, map_pValHom_sumToRestrictedFun,
        map_pValHom_sumToRestrictedFun]))
  map_add' F G := Subtype.ext (MvPowerSeries.map_injective
    (pValHom_injective m) (by
      show MvPowerSeries.map (pValHom m)
        (sumToRestrictedFun m k (F + G)) =
        MvPowerSeries.map (pValHom m)
          (sumToRestrictedFun m k F + sumToRestrictedFun m k G)
      rw [map_pValHom_sumToRestrictedFun,
        show ((F + G : MvPowerSeries.Restricted K
          (fun _ : Fin k ⊕ Fin m => (1 : ℝ)))).1 = F.1 + G.1 from rfl,
        _root_.map_add, _root_.map_add, map_pValHom_sumToRestrictedFun,
        map_pValHom_sumToRestrictedFun]))

/-- **The restricted Fubini** `K⟨X₁..X_{k+m}⟩ ≅ (K⟨X₁..X_m⟩)⟨T₁..T_k⟩`. -/
noncomputable def restrictedFubini (m k : ℕ) :
    P K (k + m) ≃+* P (P K m) k :=
  (restrictedRenameEquiv (finSumFinEquiv (m := k) (n := m)).symm).trans
    (restrictedSumEquiv m k)

end FiniteJet.GraphKoszul
