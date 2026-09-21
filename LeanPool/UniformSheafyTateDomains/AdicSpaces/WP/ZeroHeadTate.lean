/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WP.Heads
import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.RestrictedGaussAdic
import Mathlib.RingTheory.MvPowerSeries.Rename

/-!
# The zero-weight head is a Tate algebra

([hrw-decomposition] endgame block B, leaf B2.)  At zero weight the parity
constraint degenerates, and the `N`-th head `𝒜_N` of the weighted-parity
algebra is exactly the restricted power series supported on the variables
`W, U_1, …, U_N` — i.e. an honest Tate algebra `K⟨T_0,…,T_N⟩`.  The
identification is `MvPowerSeries.rename` along `Fin (N+1) ↪ ℕ`, with the
Gauss restrictedness transported through the coefficient reindexing.
-/

@[expose] public section

namespace WeightedParity

open FiniteJetOver FiniteJet.GraphKoszul

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [CompleteSpace K]
variable (N : ℕ)

/-- Zero weight: every multi-index is parity-admissible. -/
theorem wpMem_zero_weight (t : ℕ →₀ ℕ) : WPMem (fun _ => 0) t := by
  show wpWeight (fun _ => 0) t ≤ t 0
  have h : wpWeight (fun _ => 0) t = 0 :=
    Finset.sum_eq_zero fun n _ => by split <;> rfl
  rw [h]
  exact Nat.zero_le _

/-- Zero-weight head membership is exactly support-boundedness. -/
theorem headMem_zero_weight_iff (t : ℕ →₀ ℕ) :
    HeadMem (fun _ => 0) N t ↔ ∀ n, N < n → t n = 0 :=
  ⟨fun h => h.2, fun h => ⟨wpMem_zero_weight t, h⟩⟩

/-- Multi-indices supported on `{0,…,N}` are exactly the embedded
`Fin (N+1)`-indices. -/
theorem exists_embDomain_eq_iff (t : ℕ →₀ ℕ) :
    (∃ s : Fin (N + 1) →₀ ℕ,
      Finsupp.embDomain (Fin.valEmbedding (n := N + 1)) s = t) ↔
      ∀ n, N < n → t n = 0 := by
  constructor
  · rintro ⟨s, rfl⟩ n hn
    refine Finsupp.embDomain_notin_range _ _ _ ?_
    rintro ⟨i, hi⟩
    have h2 : (i : ℕ) < N + 1 := i.isLt
    have h3 : (i : ℕ) = n := hi
    omega
  · intro ht
    refine ⟨Finsupp.comapDomain _ t
      ((Fin.valEmbedding (n := N + 1)).injective.injOn), ?_⟩
    refine Finsupp.embDomain_comapDomain ?_
    intro n hn
    rw [Finset.mem_coe, Finsupp.mem_support_iff] at hn
    have hlt : n < N + 1 := by
      by_contra h
      exact hn (ht n (by omega))
    exact ⟨⟨n, hlt⟩, rfl⟩

/-- Radius-one Gauss restrictedness is coefficient decay. -/
theorem isRestrictedGauss_one_iff {σ : Type*} (f : MvPowerSeries σ K) :
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

/-- **The Tate algebra maps onto the zero-weight head** by renaming the
variables along `Fin (N+1) ↪ ℕ`. -/
noncomputable def pToZeroHead :
    P K (N + 1) →+* WPHead K (fun _ => 0) N where
  toFun f := ⟨⟨MvPowerSeries.rename (Fin.valEmbedding (n := N + 1)) f.1, by
    show MvPowerSeries.IsRestrictedGauss _ _
    rw [isRestrictedGauss_one_iff]
    have hf1 : Filter.Tendsto
        (fun t : Fin (N + 1) →₀ ℕ => MvPowerSeries.coeff t f.1)
        Filter.cofinite (nhds 0) := (isRestrictedGauss_one_iff f.1).mp f.2
    refine Filter.tendsto_def.mpr fun U hU => ?_
    rw [Filter.mem_cofinite]
    have h2 : {t : Fin (N + 1) →₀ ℕ |
        MvPowerSeries.coeff t f.1 ∈ U}ᶜ.Finite := by
      have h3 := Filter.tendsto_def.mp hf1 U hU
      rwa [Filter.mem_cofinite] at h3
    refine Set.Finite.subset (Set.Finite.image
      (Finsupp.embDomain (Fin.valEmbedding (n := N + 1))) h2) ?_
    intro t ht
    simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_setOf_eq] at ht
    by_cases hr : ∀ n, N < n → t n = 0
    · obtain ⟨s, rfl⟩ := (exists_embDomain_eq_iff N t).mpr hr
      refine Set.mem_image_of_mem _ ?_
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq]
      rwa [MvPowerSeries.coeff_embDomain_rename] at ht
    · exfalso
      have hz : MvPowerSeries.coeff t
          (MvPowerSeries.rename (Fin.valEmbedding (n := N + 1)) f.1) = 0 := by
        refine MvPowerSeries.coeff_rename_eq_zero _ _ ?_
        rintro ⟨s, hs⟩
        rw [← Finsupp.embDomain_eq_mapDomain] at hs
        exact hr ((exists_embDomain_eq_iff N t).mp ⟨s, hs⟩)
      rw [hz] at ht
      exact ht (mem_of_mem_nhds hU)⟩, by
    intro t ht
    show MvPowerSeries.coeff t
      (MvPowerSeries.rename (Fin.valEmbedding (n := N + 1)) f.1) = 0
    refine MvPowerSeries.coeff_rename_eq_zero _ _ ?_
    rintro ⟨s, hs⟩
    rw [← Finsupp.embDomain_eq_mapDomain] at hs
    exact ht ((headMem_zero_weight_iff N t).mpr
      ((exists_embDomain_eq_iff N t).mp ⟨s, hs⟩))⟩
  map_one' := Subtype.ext (Subtype.ext
    (map_one (MvPowerSeries.rename (R := K) (Fin.valEmbedding (n := N + 1)))))
  map_mul' f g := Subtype.ext (Subtype.ext
    (map_mul (MvPowerSeries.rename (R := K) (Fin.valEmbedding (n := N + 1)))
      f.1 g.1))
  map_zero' := Subtype.ext (Subtype.ext
    (map_zero (MvPowerSeries.rename (R := K) (Fin.valEmbedding (n := N + 1)))))
  map_add' f g := Subtype.ext (Subtype.ext
    (map_add (MvPowerSeries.rename (R := K) (Fin.valEmbedding (n := N + 1)))
      f.1 g.1))

theorem pToZeroHead_injective :
    Function.Injective (pToZeroHead (K := K) N) := by
  intro f g h
  have h1 : MvPowerSeries.rename (Fin.valEmbedding (n := N + 1)) f.1 =
      MvPowerSeries.rename (Fin.valEmbedding (n := N + 1)) g.1 :=
    congrArg (fun x : WPHead K (fun _ => 0) N => x.1.1) h
  exact Subtype.ext (MvPowerSeries.rename_injective _ h1)

theorem pToZeroHead_surjective :
    Function.Surjective (pToZeroHead (K := K) N) := by
  intro F
  set g : MvPowerSeries (Fin (N + 1)) K := fun s =>
    MvPowerSeries.coeff
      (Finsupp.embDomain (Fin.valEmbedding (n := N + 1)) s) F.1.1 with hg
  have hgc : ∀ s : Fin (N + 1) →₀ ℕ, MvPowerSeries.coeff s g =
      MvPowerSeries.coeff
        (Finsupp.embDomain (Fin.valEmbedding (n := N + 1)) s) F.1.1 :=
    fun s => rfl
  have hgauss : MvPowerSeries.IsRestrictedGauss
      (fun _ : Fin (N + 1) => (1 : ℝ)) g := by
    rw [isRestrictedGauss_one_iff]
    have hF : Filter.Tendsto (fun t : ℕ →₀ ℕ =>
        MvPowerSeries.coeff t F.1.1) Filter.cofinite (nhds 0) :=
      (isRestrictedGauss_one_iff F.1.1).mp F.1.2
    exact hF.comp (Finsupp.embDomain_injective _).tendsto_cofinite
  have hren : MvPowerSeries.rename (Fin.valEmbedding (n := N + 1)) g =
      F.1.1 := by
    ext t
    by_cases hr : ∀ n, N < n → t n = 0
    · obtain ⟨s, rfl⟩ := (exists_embDomain_eq_iff N t).mpr hr
      rw [MvPowerSeries.coeff_embDomain_rename, hgc]
    · have hz1 : MvPowerSeries.coeff t
          (MvPowerSeries.rename (Fin.valEmbedding (n := N + 1)) g) = 0 := by
        refine MvPowerSeries.coeff_rename_eq_zero _ _ ?_
        rintro ⟨s, hs⟩
        rw [← Finsupp.embDomain_eq_mapDomain] at hs
        exact hr ((exists_embDomain_eq_iff N t).mp ⟨s, hs⟩)
      have hz2 : MvPowerSeries.coeff t F.1.1 = 0 :=
        F.2 t fun hh => hr ((headMem_zero_weight_iff N t).mp hh)
      rw [hz1, hz2]
  refine ⟨⟨g, hgauss⟩, ?_⟩
  exact Subtype.ext (Subtype.ext hren)

/-- **B2: the zero-weight head IS the Tate algebra `K⟨T_0,…,T_N⟩`.** -/
noncomputable def zeroHeadTateEquiv :
    P K (N + 1) ≃+* WPHead K (fun _ => 0) N :=
  RingEquiv.ofBijective (pToZeroHead N)
    ⟨pToZeroHead_injective N, pToZeroHead_surjective N⟩

end WeightedParity
