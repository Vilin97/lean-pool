/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.GalerkinHorizonSmoothnessRhs

/-! Assemble time and spatial derivatives on the closed unit slab and rescale to physical
    horizons. -/

@[expose] public section

noncomputable section

open Set Filter Topology Homogenization

namespace AVenhance.Infra.Classical

theorem GalerkinHorizonSmoothnessAssembly.classicalBoundarySpatialWord_hasFDerivAt
    (w : List (Fin 2)) (u : Vec 2 → ℝ)
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (x : Vec 2) :
    HasFDerivAt (classicalWordDerivative w u)
      (∑ i : Fin 2, classicalWordDerivative (i :: w) u x •
        (ContinuousLinearMap.proj i : Vec 2 →L[ℝ] ℝ)) x := by
  let g := classicalWordDerivative w u
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := classicalWordDerivative_contDiff w u hu
  have hbase : HasFDerivAt g (fderiv ℝ g x) x :=
    (hg.differentiable (by simp) x).hasFDerivAt
  have hmap : fderiv ℝ g x =
      ∑ i : Fin 2, classicalWordDerivative (i :: w) u x •
        (ContinuousLinearMap.proj i : Vec 2 →L[ℝ] ℝ) := by
    apply ContinuousLinearMap.ext
    intro v
    have hv : v = ∑ i : Fin 2, v i • Homogenization.basisVec i := by
      ext j
      simp [Homogenization.basisVec, Pi.single_apply]
    rw [hv]
    simp only [map_sum, map_smul]
    have hcoord (i : Fin 2) :
        fderiv ℝ g x (Homogenization.basisVec i) =
          (∑ j : Fin 2, classicalWordDerivative (j :: w) u x •
            (ContinuousLinearMap.proj j : Vec 2 →L[ℝ] ℝ))
            (Homogenization.basisVec i) := by
      fin_cases i <;>
        simp [g, classicalWordDerivative, AVenhance.spaceGrad,
          ContinuousLinearMap.proj_apply, smul_eq_mul,
          Homogenization.basisVec]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hcoord]
  exact hbase.congr_fderiv hmap

/-- Every ordered spatial derivative of the unit-slab Galerkin limit is jointly smooth up to both
time endpoints. -/
theorem classicalGalerkinUnitWordFamily_contDiffOn
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Ici (0 : ℝ) ×ˢ univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) :
    ∀ w, ContDiffOn ℝ (⊤ : ℕ∞)
      (classicalGalerkinUnitWordFamily φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per w)
      (Icc (0 : ℝ) 1 ×ˢ univ) := by
  let S : Set (ℝ × Vec 2) := Icc (0 : ℝ) 1 ×ˢ univ
  let f := classicalGalerkinUnitWordFamily φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per
  let q := classicalGalerkinUnitWordRhs φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per
  have hS : S = Icc (0 : ℝ) 1 ×ˢ univ := rfl
  have hUnique : UniqueDiffOn ℝ S := by
    rw [hS]
    exact uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1) |>.prod uniqueDiffOn_univ
  have hfcont : ∀ w, ContinuousOn (f w) S := by
    intro w
    rw [hS]
    exact (classicalGalerkinUnitWordFamily_continuous
      φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per w).continuousOn
  have hqcont : ∀ w, ContinuousOn (q w) S := by
    intro w
    rw [hS]
    exact (classicalGalerkinUnitWordRhs_continuous
      φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per w).continuousOn
  have htimeInterior (w : List (Fin 2)) (x : Vec 2) {t : ℝ}
      (ht : t ∈ Ioo (0 : ℝ) 1) :
      HasDerivAt (fun s => f w (s, x)) (q w (t, x)) t := by
    have hpoint := classicalGalerkinWordPointwise_hasDerivAt
      φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per w x ht
    have hs : classicalGalerkinUnitSlabClamp t =
        ⟨t, le_of_lt ht.1, le_of_lt ht.2⟩ := by
      apply Subtype.ext
      simp [classicalGalerkinUnitSlabClamp, max_eq_right (le_of_lt ht.1),
        min_eq_right (le_of_lt ht.2)]
    have hqval : q w (t, x) = classicalWordDerivative w
        (fun y => F t y + κ * AVenhance.spaceLap
          (classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper
            θ₀ hθ₀ hθ₀per ⟨t, le_of_lt ht.1, le_of_lt ht.2⟩) y -
          classicalTransport (AVenhance.streamVel φ t)
            (classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper
              θ₀ hθ₀ hθ₀per ⟨t, le_of_lt ht.1, le_of_lt ht.2⟩) y) x := by
      simp [q, classicalGalerkinUnitWordRhs, hs]
    have hfinal := hpoint.congr_deriv hqval.symm
    simpa only [f, classicalGalerkinUnitWordFamily] using hfinal
  have htimeZero (w : List (Fin 2)) (x : Vec 2) :
      HasDerivWithinAt (fun s => f w (s, x)) (q w (0, x)) (Ici 0) 0 := by
    have hpoint := classicalGalerkinWordPointwise_hasDerivWithinAt_zero
      φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per w x
    have hs : classicalGalerkinUnitSlabClamp 0 = ⟨0, by norm_num, by norm_num⟩ := by
      apply Subtype.ext
      simp [classicalGalerkinUnitSlabClamp]
    have hqval : q w (0, x) = classicalWordDerivative w
        (fun y => F 0 y + κ * AVenhance.spaceLap
          (classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper
            θ₀ hθ₀ hθ₀per ⟨0, by norm_num, by norm_num⟩) y -
          classicalTransport (AVenhance.streamVel φ 0)
            (classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper
              θ₀ hθ₀ hθ₀per ⟨0, by norm_num, by norm_num⟩) y) x := by
      simp [q, classicalGalerkinUnitWordRhs, hs]
    have hfinal := hpoint.congr_deriv hqval.symm
    simpa only [f, classicalGalerkinUnitWordFamily] using hfinal
  have htimeOne (w : List (Fin 2)) (x : Vec 2) :
      HasDerivWithinAt (fun s => f w (s, x)) (q w (1, x)) (Iic 1) 1 := by
    have hpoint := classicalGalerkinWordPointwise_hasDerivWithinAt_one
      φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per w x
    have hs : classicalGalerkinUnitSlabClamp 1 = ⟨1, by norm_num, by norm_num⟩ := by
      apply Subtype.ext
      simp [classicalGalerkinUnitSlabClamp]
    have hqval : q w (1, x) = classicalWordDerivative w
        (fun y => F 1 y + κ * AVenhance.spaceLap
          (classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper
            θ₀ hθ₀ hθ₀per ⟨1, by norm_num, by norm_num⟩) y -
          classicalTransport (AVenhance.streamVel φ 1)
            (classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper
              θ₀ hθ₀ hθ₀per ⟨1, by norm_num, by norm_num⟩) y) x := by
      simp [q, classicalGalerkinUnitWordRhs, hs]
    have hfinal := hpoint.congr_deriv hqval.symm
    simpa only [f, classicalGalerkinUnitWordFamily] using hfinal
  have hspaceF : ∀ w t x, HasFDerivAt (fun y => f w (t, y))
      (∑ i : Fin 2, f (i :: w) (t, x) •
        (ContinuousLinearMap.proj i : Vec 2 →L[ℝ] ℝ)) x := by
    intro w t x
    have hu := classicalGalerkinRealSmoothLift_contDiff
      φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per
      (classicalGalerkinUnitSlabClamp t)
    have hword := GalerkinHorizonSmoothnessAssembly.classicalBoundarySpatialWord_hasFDerivAt w
      (classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper
        θ₀ hθ₀ hθ₀per (classicalGalerkinUnitSlabClamp t)) hu x
    simpa [f, classicalGalerkinUnitWordFamily] using hword
  have hspaceQ : ∀ w t x, HasFDerivAt (fun y => q w (t, y))
      (∑ i : Fin 2, q (i :: w) (t, x) •
        (ContinuousLinearMap.proj i : Vec 2 →L[ℝ] ℝ)) x := by
    intro w t x
    let τ := (classicalGalerkinUnitSlabClamp t : ℝ)
    let s := classicalGalerkinUnitSlabClamp t
    let u := classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per s
    let b := AVenhance.streamVel φ τ
    have hu : ContDiff ℝ (⊤ : ℕ∞) u := by
      simpa [u, s] using classicalGalerkinRealSmoothLift_contDiff
        φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per s
    have hb : ContDiff ℝ (⊤ : ℕ∞) b := by
      have hvel := (streamVel_smoothPeriodic φ hφ).smooth
      have hslice : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec 2 => ((τ : ℝ), y)) :=
        contDiff_const.prodMk contDiff_id
      have hcomp := hvel.comp hslice
      change ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec 2 => AVenhance.streamVel φ τ y) at hcomp
      simpa [b] using hcomp
    have hFsmooth : ContDiff ℝ (⊤ : ℕ∞) (F τ) :=
      classicalSmooth_slice_nonneg hF (classicalGalerkinUnitSlabClamp t).property.1
    have hlap : ContDiff ℝ (⊤ : ℕ∞) (fun y => AVenhance.spaceLap u y) :=
      classicalBoundarySpaceLap_contDiff u hu
    have htr : ContDiff ℝ (⊤ : ℕ∞) (classicalTransport b u) :=
      classicalBoundaryTransport_contDiff b u hb hu
    have hbase : ContDiff ℝ (⊤ : ℕ∞)
        (fun y => F τ y + κ * AVenhance.spaceLap u y - classicalTransport b u y) :=
      (hFsmooth.add (contDiff_const.mul hlap)).sub htr
    have hword := GalerkinHorizonSmoothnessAssembly.classicalBoundarySpatialWord_hasFDerivAt w
      (fun y => F τ y + κ * AVenhance.spaceLap u y - classicalTransport b u y) hbase x
    change HasFDerivAt (fun y =>
      classicalWordDerivative w
        (fun z => F τ z + κ * AVenhance.spaceLap u z - classicalTransport b u z) y)
      _ x at hword
    simpa [q, classicalGalerkinUnitWordRhs, τ, s, u, b] using hword
  have hderiv : ∀ w p, p ∈ S → HasFDerivWithinAt (f w)
      (classicalSpatialWordDerivativeLinearMap f q w p) S p := by
    have hres := classicalSpatialWordFamily_hasFDerivWithinAt S hS f q
      (fun w => (classicalGalerkinUnitWordFamily_continuous
        φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per w))
      (fun w => (classicalGalerkinUnitWordRhs_continuous
        φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per w))
      htimeInterior htimeZero htimeOne hspaceF hspaceQ
    exact hres
  have hfinite := classicalSpatialWordFamily_contDiffOn S hUnique f q hfcont hderiv
    (fun k hk => classicalGalerkinUnitWordRhs_contDiffOn_of_family
      φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per S hS k hk)
  simpa [f] using hfinite

/-- The horizon-rescaled Galerkin limit is jointly smooth on its closed physical-time slab. -/
theorem classicalGalerkinHorizonLimit_contDiffOn
    (N : ℕ) (hN : 0 < N)
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Ici (0 : ℝ) ×ˢ univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (Function.uncurry (classicalGalerkinHorizonLimit N hN φ hφ κ hκ F hF hFper
        θ₀ hθ₀ hθ₀per)) (Icc (0 : ℝ) (N : ℝ) ×ˢ univ) := by
  let φN := classicalGalerkinHorizonStream N φ
  let hφN := classicalGalerkinHorizonStream_admissible N φ hφ
  let κN := (N : ℝ) * κ
  have hκN : 0 < κN := mul_pos (Nat.cast_pos.mpr hN) hκ
  let FN := classicalGalerkinHorizonForcing N F
  let hFN := classicalGalerkinHorizonForcing_smooth N F hF
  let hFNper := classicalGalerkinHorizonForcing_periodic N F hFper
  let U : ℝ × Vec 2 → ℝ := fun p =>
    classicalGalerkinUnitWordFamily φN hφN κN hκN FN hFN hFNper
      θ₀ hθ₀ hθ₀per [] p
  have hU : ContDiffOn ℝ (⊤ : ℕ∞) U (Icc (0 : ℝ) 1 ×ˢ univ) := by
    change ContDiffOn ℝ (⊤ : ℕ∞)
      (classicalGalerkinUnitWordFamily φN hφN κN hκN FN hFN hFNper
        θ₀ hθ₀ hθ₀per []) (Icc (0 : ℝ) 1 ×ˢ univ)
    exact classicalGalerkinUnitWordFamily_contDiffOn
      φN hφN κN hκN FN hFN hFNper θ₀ hθ₀ hθ₀per []
  let m : ℝ × Vec 2 → ℝ × Vec 2 := fun p => (p.1 / (N : ℝ), p.2)
  have hm : ContDiff ℝ (⊤ : ℕ∞) m := by
    dsimp [m]
    fun_prop
  have hmaps : MapsTo m (Icc (0 : ℝ) (N : ℝ) ×ˢ univ)
      (Icc (0 : ℝ) 1 ×ˢ univ) := by
    intro p hp
    rcases Set.mem_prod.mp hp with ⟨ht, hx⟩
    have hNpos : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
    have hratio : p.1 / (N : ℝ) ∈ Icc (0 : ℝ) 1 := by
      constructor
      · exact div_nonneg ht.1 (le_of_lt hNpos)
      · exact (div_le_iff₀ hNpos).2 (by simpa using ht.2)
    exact ⟨hratio, hx⟩
  have hcomp : ContDiffOn ℝ (⊤ : ℕ∞) (U ∘ m)
      (Icc (0 : ℝ) (N : ℝ) ×ˢ univ) := hU.comp hm.contDiffOn hmaps
  have hEq : ∀ p ∈ Icc (0 : ℝ) (N : ℝ) ×ˢ univ,
      Function.uncurry (classicalGalerkinHorizonLimit N hN φ hφ κ hκ F hF hFper
        θ₀ hθ₀ hθ₀per) p = (U ∘ m) p := by
    intro p hp
    rcases Set.mem_prod.mp hp with ⟨ht, hx⟩
    have hrange : p.1 / (N : ℝ) ∈ Icc (0 : ℝ) 1 := (hmaps hp).1
    have hcl : classicalGalerkinUnitSlabClamp (p.1 / (N : ℝ)) =
        ⟨p.1 / (N : ℝ), hrange.1, hrange.2⟩ := by
      apply Subtype.ext
      simp [classicalGalerkinUnitSlabClamp, hrange.1, hrange.2]
    simp [Function.uncurry, classicalGalerkinHorizonLimit, U, m, hcl,
      φN, κN, FN, classicalGalerkinUnitWordFamily, classicalWordDerivative]
  exact hcomp.congr hEq

/-- The integer-horizon family is jointly smooth on every requested closed horizon. -/
theorem classicalGalerkinIntegerHorizonFamily_contDiffOn
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Ici (0 : ℝ) ×ˢ univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) (N : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (Function.uncurry (classicalGalerkinIntegerHorizonFamily φ hφ κ hκ F hF hFper
        θ₀ hθ₀ hθ₀per N)) (Icc (0 : ℝ) (N : ℝ) ×ˢ univ) := by
  let M := Nat.succ N
  have hM : 0 < M := Nat.succ_pos N
  have hlimit := classicalGalerkinHorizonLimit_contDiffOn M hM
    φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per
  have hsubset : (Icc (0 : ℝ) (N : ℝ) ×ˢ (univ : Set (Vec 2))) ⊆
      (Icc (0 : ℝ) (M : ℝ) ×ˢ (univ : Set (Vec 2))) := by
    intro p hp
    rcases Set.mem_prod.mp hp with ⟨ht, hx⟩
    refine ⟨⟨ht.1, ht.2.trans ?_⟩, hx⟩
    exact_mod_cast Nat.le_succ N
  have hrestrict := hlimit.mono hsubset
  simpa [classicalGalerkinIntegerHorizonFamily, M] using hrestrict

end AVenhance.Infra.Classical

end
