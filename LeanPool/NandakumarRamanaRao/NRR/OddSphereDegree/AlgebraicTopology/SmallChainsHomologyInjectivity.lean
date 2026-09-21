/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import Mathlib.Tactic
import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.SmallChainComplex
import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.IteratedSubdivisionSmallChains
import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.IteratedSubdivisionHomotopySmall
import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.BarycentricSubdivisionIter
import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.SmallChainsHomologySurjectivity

/-! # Small Chains Homology Injectivity -/

open CategoryTheory Limits AlgebraicTopology
open SphereOddDegree.AffineBarycentricSubdivision

namespace SphereOddDegree

variable {R : Type} [CommRing R] {X : TopCat.{0}}
theorem exists_d_eq_iCycles_of_homologyπ_zero
    (K : ChainComplex (ModuleCat.{0} R) ℕ) (n : ℕ) (W : K.cycles n)
    (h : (K.homologyπ n).hom W = 0) :
    ∃ b : K.X (n + 1), (K.d (n + 1) n).hom b = (K.iCycles n).hom W := by
  have hW_im : ∃ b : K.X (n + 1), (K.toCycles (n + 1) n).hom b = W := by
    have h_cok := HomologicalComplex.homologyIsCokernel K (n + 1) n (by simp [ComplexShape.prev])
    have h_range_zero : K.toCycles (n + 1) n ≫ ModuleCat.ofHom (LinearMap.range (K.toCycles (n + 1) n).hom).mkQ = 0 := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      show (LinearMap.range (K.toCycles (n + 1) n).hom).mkQ ((K.toCycles (n + 1) n).hom x) = 0
      exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨x, rfl⟩
    have hl := h_cok.fac (CokernelCofork.ofπ (ModuleCat.ofHom (LinearMap.range (K.toCycles (n + 1) n).hom).mkQ) h_range_zero) WalkingParallelPair.one
    have hl_app := congr_arg (fun (f : K.cycles n ⟶ _) => f.hom W) hl
    erw [ModuleCat.hom_comp, LinearMap.comp_apply] at hl_app
    dsimp [CokernelCofork.ofπ, Cofork.ofπ] at hl_app
    rw [h, map_zero] at hl_app
    have h_quot : Submodule.Quotient.mk W = 0 := hl_app.symm
    rw [Submodule.Quotient.mk_eq_zero] at h_quot
    exact h_quot
  obtain ⟨b, hb⟩ := hW_im
  use b
  have ht := congr_arg (fun f => f.hom b) (HomologicalComplex.toCycles_i K (n + 1) n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at ht
  rw [← ht, hb]

theorem homologyπ_zero_of_iCycles_eq_d
    (K : ChainComplex (ModuleCat.{0} R) ℕ) (n : ℕ) (W : K.cycles n) (b : K.X (n + 1))
    (h : (K.iCycles n).hom W = (K.d (n + 1) n).hom b) :
    (K.homologyπ n).hom W = 0 := by
  have hW : W = (K.toCycles (n + 1) n).hom b := by
    apply (ModuleCat.mono_iff_injective (K.iCycles n)).mp inferInstance
    have ht := congr_arg (fun f => f.hom b) (HomologicalComplex.toCycles_i K (n + 1) n)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at ht
    rw [h, ht]
  rw [hW]
  have hc := congrArg (fun m => m.hom b)
    (HomologicalComplex.toCycles_comp_homologyπ K (n + 1) n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply] at hc
  exact hc

theorem iterHomotopyBoundaryTerm_eq_zero_of_full_cycle
    (R : Type) [CommRing R] (X : TopCat.{0}) (N n : ℕ)
    (z : singularChainGroup R X n)
    (hz : ((singularChainComplex R X).d n ((ComplexShape.down ℕ).next n)).hom z = 0) :
    barycentricSubdivisionIterHomotopyBoundaryTerm R X N n z = 0 := by
  cases n with
  | zero => rfl
  | succ n =>
    rw [barycentricSubdivisionIterHomotopyBoundaryTerm_succ]
    rw [ComplexShape.next_eq' (ComplexShape.down ℕ) (j := n) rfl] at hz
    have hz' : (singularBoundary R X n).hom z = 0 := hz
    rw [hz', map_zero]

theorem exists_small_boundary_witness
    (𝒰 : OpenCoverData X) (R : Type) [CommRing R] (n : ℕ)
    (b : singularChainGroup R X (n + 1))
    (hsmall : (singularBoundary R X n).hom b ∈ smallChainSubmodule R X 𝒰 n) :
    ∃ bChain : singularChainGroup R X (n + 1),
      bChain ∈ smallChainSubmodule R X 𝒰 (n + 1) ∧
      (singularBoundary R X n).hom bChain = (singularBoundary R X n).hom b := by
  have hcyc : ((singularChainComplex R X).d n ((ComplexShape.down ℕ).next n)).hom
      ((singularBoundary R X n).hom b) = 0 := by
    have hdd := congrArg (fun m => m.hom b)
      ((singularChainComplex R X).d_comp_d (n + 1) n ((ComplexShape.down ℕ).next n))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply] at hdd
    exact hdd
  obtain ⟨N₁, hN₁⟩ := exists_iteratedSubdivision_chain_mem_smallChains 𝒰 R (n + 1) b
  obtain ⟨N₂, hN₂⟩ : ∃ N₂ : ℕ,
      barycentricSubdivisionIterHomotopyLinearMap R X N₂ n ((singularBoundary R X n).hom b)
        ∈ smallChainSubmodule R X 𝒰 (n + 1) :=
    ⟨0, iteratedSubdivisionHomotopy_preserves_smallChains R 𝒰 0 n _ hsmall⟩
  have hbN : barycentricSubdivisionIterLinearMap R X (max N₁ N₂) (n + 1) b
      ∈ smallChainSubmodule R X 𝒰 (n + 1) :=
    sdIter_mem_smallChainSubmodule_mono R 𝒰 (le_max_left N₁ N₂) hN₁
  have hHN : barycentricSubdivisionIterHomotopyLinearMap R X (max N₁ N₂) n
      ((singularBoundary R X n).hom b) ∈ smallChainSubmodule R X 𝒰 (n + 1) :=
    iteratedSubdivisionHomotopy_preserves_smallChains R 𝒰 (max N₁ N₂) n _ hsmall
  refine ⟨barycentricSubdivisionIterLinearMap R X (max N₁ N₂) (n + 1) b
      + barycentricSubdivisionIterHomotopyLinearMap R X (max N₁ N₂) n
          ((singularBoundary R X n).hom b),
      Submodule.add_mem _ hbN hHN, ?_⟩
  have hcomm := barycentricSubdivisionIterLinearMap_commutes_boundary R X (max N₁ N₂) n b
  have hbf := barycentricSubdivisionIter_boundary_formula R X (max N₁ N₂) n
    ((singularBoundary R X n).hom b)
  rw [iterHomotopyBoundaryTerm_eq_zero_of_full_cycle R X (max N₁ N₂) n _ hcyc, add_zero] at hbf
  rw [map_add, hcomm, ← hbf]
  abel

theorem smallChainsInclusion_injective_on_homology
    (R : Type) [CommRing R] (X : TopCat.{0}) (𝒰 : OpenCoverData X) (n : ℕ) :
    Function.Injective (homologyMapInDegree (smallChainsInclusion R X 𝒰) n) := by
  intro x y hxy
  obtain ⟨w, hw⟩ : ∃ w : (smallChainComplex R X 𝒰).cycles n, ((smallChainComplex R X 𝒰).homologyπ n).hom w = x - y := by
    have := SphereOddDegree.homologyπ_surjective (smallChainComplex R X 𝒰) n (x - y)
    exact this
  have hWfull : ((singularChainComplex R X).homologyπ n).hom ((HomologicalComplex.cyclesMap (smallChainsInclusion R X 𝒰) n).hom w) = 0 := by
    have hnat := HomologicalComplex.homologyπ_naturality (smallChainsInclusion R X 𝒰) n
    have hnat2 := DFunLike.congr_fun (congr_arg ModuleCat.Hom.hom hnat) w
    have h_L : ((HomologicalComplex.cyclesMap (smallChainsInclusion R X 𝒰) n ≫ (singularChainComplex R X).homologyπ n).hom) w = ((singularChainComplex R X).homologyπ n).hom ((HomologicalComplex.cyclesMap (smallChainsInclusion R X 𝒰) n).hom w) := rfl
    rw [← h_L, ← hnat2]
    have h_R : (((smallChainComplex R X 𝒰).homologyπ n ≫ HomologicalComplex.homologyMap (smallChainsInclusion R X 𝒰) n).hom) w = (HomologicalComplex.homologyMap (smallChainsInclusion R X 𝒰) n).hom (((smallChainComplex R X 𝒰).homologyπ n).hom w) := rfl
    rw [h_R]
    dsimp [homologyMapInDegree] at hxy
    rw [hw, map_sub, hxy, sub_self]
  obtain ⟨b, hb⟩ : ∃ b : singularChainGroup R X (n + 1), ((singularChainComplex R X).d (n + 1) n).hom b = ((singularChainComplex R X).iCycles n).hom ((HomologicalComplex.cyclesMap (smallChainsInclusion R X 𝒰) n).hom w) := by
    exact exists_d_eq_iCycles_of_homologyπ_zero (singularChainComplex R X) n _ hWfull
  have h_cyc_i := HomologicalComplex.cyclesMap_i (smallChainsInclusion R X 𝒰) n
  have h_cyc_i2 := congrArg (fun m => m.hom w) h_cyc_i
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h_cyc_i2
  rw [h_cyc_i2] at hb
  have hb_bound : (singularBoundary R X n).hom b = ((smallChainsInclusion R X 𝒰).f n).hom (((smallChainComplex R X 𝒰).iCycles n).hom w) := by
    exact hb
  have h_sub_mem : ((smallChainsInclusion R X 𝒰).f n).hom (((smallChainComplex R X 𝒰).iCycles n).hom w) ∈ smallChainSubmodule R X 𝒰 n := by
    exact (((smallChainComplex R X 𝒰).iCycles n).hom w).2
  obtain ⟨bChain, hbChain_mem, hbChain_eq⟩ : ∃ bChain : singularChainGroup R X (n + 1),
      bChain ∈ smallChainSubmodule R X 𝒰 (n + 1) ∧
      (singularBoundary R X n).hom bChain = (singularBoundary R X n).hom b := by
    apply exists_small_boundary_witness
    rw [hb_bound]
    exact h_sub_mem
  set bSmall : (smallChainComplex R X 𝒰).X (n + 1) := ⟨bChain, hbChain_mem⟩
  have h_eq : ((smallChainComplex R X 𝒰).iCycles n).hom w = ((smallChainComplex R X 𝒰).d (n + 1) n).hom bSmall := by
    have h_comm := (smallChainsInclusion R X 𝒰).comm (n + 1) n
    have h_comm_app := DFunLike.congr_fun (congr_arg ModuleCat.Hom.hom h_comm) bSmall
    have h_lhs : (((smallChainsInclusion R X 𝒰).f (n + 1) ≫ (singularChainComplex R X).d (n + 1) n).hom) bSmall = (singularBoundary R X n).hom bChain := rfl
    have h_rhs : (((smallChainComplex R X 𝒰).d (n + 1) n ≫ (smallChainsInclusion R X 𝒰).f n).hom) bSmall = (((smallChainComplex R X 𝒰).d (n + 1) n).hom bSmall).val := rfl
    rw [h_lhs, h_rhs, hbChain_eq, hb_bound] at h_comm_app
    exact Subtype.ext h_comm_app
  have h_zero : ((smallChainComplex R X 𝒰).homologyπ n).hom w = 0 := by
    exact homologyπ_zero_of_iCycles_eq_d (smallChainComplex R X 𝒰) n w bSmall h_eq
  rw [h_zero] at hw
  exact eq_of_sub_eq_zero hw.symm

end SphereOddDegree
