/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.GalerkinHorizonSmoothnessProducer

/-! Finite Leibniz regularity for the word-indexed Galerkin equation. -/

@[expose] public section

noncomputable section

open Set Homogenization

namespace AVenhance.Infra.Classical

theorem GalerkinHorizonSmoothnessRhs.classicalBoundaryWordDerivative_add (w : List (Fin 2))
    (f g : Vec 2 → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    classicalWordDerivative w (fun x => f x + g x) =
      fun x => classicalWordDerivative w f x + classicalWordDerivative w g x := by
  induction w generalizing f g with
  | nil => rfl
  | cons i w ih =>
      have hfw := classicalWordDerivative_contDiff w f hf
      have hgw := classicalWordDerivative_contDiff w g hg
      funext x
      change AVenhance.spaceGrad
        (classicalWordDerivative w (fun y => f y + g y)) x i = _
      rw [ih f g hf hg]
      exact classicalSpaceGrad_add _ _ hfw hgw i x

theorem GalerkinHorizonSmoothnessRhs.classicalBoundaryWordDerivative_append (v w : List (Fin 2))
    (f : Vec 2 → ℝ) :
    classicalWordDerivative v (classicalWordDerivative w f) =
      classicalWordDerivative (v ++ w) f := by
  induction v with
  | nil => rfl
  | cons i v ih =>
      funext x
      change AVenhance.spaceGrad
        (classicalWordDerivative v (classicalWordDerivative w f)) x i = _
      rw [ih]
      rfl

theorem classicalBoundarySpaceLap_contDiff (u : Vec 2 → ℝ)
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => AVenhance.spaceLap u x) := by
  unfold AVenhance.spaceLap
  apply ContDiff.sum
  intro i hi
  have hgrad : ContDiff ℝ (⊤ : ℕ∞) (fun y => AVenhance.spaceGrad u y i) := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun y => fderiv ℝ u y
      (Homogenization.basisVec i))
    exact (hu.fderiv_right (by simp)).clm_apply contDiff_const
  change ContDiff ℝ (⊤ : ℕ∞) (fun x => fderiv ℝ
    (fun y => AVenhance.spaceGrad u y i) x (Homogenization.basisVec i))
  exact (hgrad.fderiv_right (by simp)).clm_apply contDiff_const

theorem classicalBoundaryTransport_contDiff (b : Vec 2 → Vec 2)
    (u : Vec 2 → ℝ) (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
    ContDiff ℝ (⊤ : ℕ∞) (classicalTransport b u) := by
  unfold classicalTransport
  change ContDiff ℝ (⊤ : ℕ∞)
    (fun x => ∑ j : Fin 2, b x j * AVenhance.spaceGrad u x j)
  apply ContDiff.sum
  intro j hj
  have hbcomp : ContDiff ℝ (⊤ : ℕ∞) (fun x => b x j) := (contDiff_pi.1 hb) j
  have hgrad : ContDiff ℝ (⊤ : ℕ∞)
      (fun x => AVenhance.spaceGrad u x j) := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun x => fderiv ℝ u x
      (Homogenization.basisVec j))
    exact (hu.fderiv_right (by simp)).clm_apply contDiff_const
  exact hbcomp.mul hgrad

/-- The right-hand side with the product rule fully expanded in joint space-time coordinates. -/
noncomputable def classicalGalerkinUnitWordRhsExpansion
    (φ : ℝ → Vec 2 → ℝ) (κ : ℝ) (F : ℝ → Vec 2 → ℝ)
    (f : List (Fin 2) → ℝ × Vec 2 → ℝ)
    (w : List (Fin 2)) (p : ℝ × Vec 2) : ℝ :=
  classicalJointWordDerivative w (Function.uncurry F) p +
    κ * (∑ i : Fin 2, f ([i, i] ++ w) p) -
    ∑ j : Fin 2,
      ((classicalWordSplits w).map fun r =>
        classicalJointWordDerivative r.1
          (fun z => AVenhance.streamVel φ z.1 z.2 j) p * f (r.2 ++ [j]) p).sum

theorem GalerkinHorizonSmoothnessRhs.classicalBoundaryListMapSum_contDiffOn
    {α : Type*} (k : ℕ) (S : Set (ℝ × Vec 2)) (L : List α)
    (g : α → (ℝ × Vec 2 → ℝ))
    (hg : ∀ a, a ∈ L → ContDiffOn ℝ (k : WithTop ℕ∞) (g a) S) :
    ContDiffOn ℝ (k : WithTop ℕ∞) ((L.map g).sum) S := by
  induction L with
  | nil => exact contDiffOn_const
  | cons a L ih =>
      simp only [List.map_cons, List.sum_cons]
      exact (hg a (by simp)).add (ih (by
        intro b hb
        exact hg b (by simp [hb])))

theorem GalerkinHorizonSmoothnessRhs.classicalBoundaryWordRhsExpansion_contDiffOn
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F) classicalHalfSpace)
    (f : List (Fin 2) → ℝ × Vec 2 → ℝ) (S : Set (ℝ × Vec 2))
    (hS : S = Icc (0 : ℝ) 1 ×ˢ univ)
    (k : ℕ) (hk : ∀ w, ContDiffOn ℝ (k : WithTop ℕ∞) (f w) S) :
    ∀ w, ContDiffOn ℝ (k : WithTop ℕ∞)
      (classicalGalerkinUnitWordRhsExpansion φ κ F f w) S := by
  have hSsub : S ⊆ classicalHalfSpace := by
    intro p hp
    rw [hS] at hp
    exact ⟨hp.1.1, trivial⟩
  have hstream : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry (AVenhance.streamVel φ)) :=
    (streamVel_smoothPeriodic φ hφ).smooth
  have hforcing (w : List (Fin 2)) :
      ContDiffOn ℝ (k : WithTop ℕ∞)
        (classicalJointWordDerivative w (Function.uncurry F)) S := by
    have hktop : (↑(k : ℕ∞) : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) :=
      WithTop.coe_le_coe.mpr (le_top : (k : ℕ∞) ≤ (⊤ : ℕ∞))
    exact (classicalJointWordDerivative_contDiffOn w (Function.uncurry F) hF)
      |>.mono hSsub |>.of_le hktop
  have hcoefficient (v : List (Fin 2)) (j : Fin 2) :
      ContDiffOn ℝ (⊤ : ℕ∞)
        (classicalJointWordDerivative v
          (fun z => AVenhance.streamVel φ z.1 z.2 j)) S := by
    have hcoord : ContDiff ℝ (⊤ : ℕ∞)
        (fun z : ℝ × Vec 2 => (Function.uncurry (AVenhance.streamVel φ) z) j) :=
      (contDiff_pi.1 hstream) j
    have hcoord' : ContDiff ℝ (⊤ : ℕ∞)
        (fun z : ℝ × Vec 2 => AVenhance.streamVel φ z.1 z.2 j) := by
      simpa only [Function.uncurry] using hcoord
    have hword := classicalJointWordDerivative_contDiffOn v
      (fun z => AVenhance.streamVel φ z.1 z.2 j) hcoord'.contDiffOn
    exact hword.mono hSsub
  intro w
  have hlap : ContDiffOn ℝ (k : WithTop ℕ∞)
      (fun p : ℝ × Vec 2 => ∑ i : Fin 2, f ([i, i] ++ w) p) S := by
    apply ContDiffOn.sum
    intro i hi
    exact hk ([i, i] ++ w)
  have htransport (j : Fin 2) : ContDiffOn ℝ (k : WithTop ℕ∞)
      (fun p : ℝ × Vec 2 => ((classicalWordSplits w).map fun r =>
        classicalJointWordDerivative r.1
          (fun z => AVenhance.streamVel φ z.1 z.2 j) p * f (r.2 ++ [j]) p).sum) S := by
    let G : List (Fin 2) × List (Fin 2) → ℝ × Vec 2 → ℝ := fun r p =>
      classicalJointWordDerivative r.1
        (fun z => AVenhance.streamVel φ z.1 z.2 j) p * f (r.2 ++ [j]) p
    have hG : ∀ r, r ∈ classicalWordSplits w →
        ContDiffOn ℝ (k : WithTop ℕ∞) (G r) S := by
      intro r hr
      have hktop : (↑(k : ℕ∞) : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) :=
        WithTop.coe_le_coe.mpr (le_top : (k : ℕ∞) ≤ (⊤ : ℕ∞))
      have hcoeff' := (hcoefficient r.1 j).of_le hktop
      change ContDiffOn ℝ (k : WithTop ℕ∞)
        (fun p => classicalJointWordDerivative r.1
          (fun z => AVenhance.streamVel φ z.1 z.2 j) p * f (r.2 ++ [j]) p) S
      exact hcoeff'.mul (hk (r.2 ++ [j]))
    have hmap := GalerkinHorizonSmoothnessRhs.classicalBoundaryListMapSum_contDiffOn k S
      (classicalWordSplits w) G hG
    have hEq : (fun p : ℝ × Vec 2 =>
        ((classicalWordSplits w).map fun r => G r p).sum) =
        ((classicalWordSplits w).map G).sum := by
      funext p
      induction classicalWordSplits w with
      | nil => rfl
      | cons r rs ih => simp [ih]
    rw [hEq]
    exact hmap
  have htransportSum : ContDiffOn ℝ (k : WithTop ℕ∞)
      (fun p : ℝ × Vec 2 => ∑ j : Fin 2,
        ((classicalWordSplits w).map fun r =>
          classicalJointWordDerivative r.1
            (fun z => AVenhance.streamVel φ z.1 z.2 j) p * f (r.2 ++ [j]) p).sum) S := by
    apply ContDiffOn.sum
    intro j hj
    exact htransport j
  have hκconst : ContDiffOn ℝ (k : WithTop ℕ∞)
      (fun _ : ℝ × Vec 2 => κ) S := contDiffOn_const
  change ContDiffOn ℝ (k : WithTop ℕ∞)
    (fun p => (classicalJointWordDerivative w (Function.uncurry F) p +
      κ * (∑ i : Fin 2, f ([i, i] ++ w) p)) -
      ∑ j : Fin 2, ((classicalWordSplits w).map fun r =>
        classicalJointWordDerivative r.1
          (fun z => AVenhance.streamVel φ z.1 z.2 j) p * f (r.2 ++ [j]) p).sum) S
  exact ((hforcing w).add (hκconst.mul hlap)).sub htransportSum

/-- On the closed unit slab the equation word equals its finite spatial Leibniz expansion. -/
theorem classicalGalerkinUnitWordRhs_eq_expansion_on
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Ici (0 : ℝ) ×ˢ univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀)
    (w : List (Fin 2)) (p : ℝ × Vec 2)
    (hp : p ∈ Icc (0 : ℝ) 1 ×ˢ univ) :
    classicalGalerkinUnitWordRhs φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per w p =
      classicalGalerkinUnitWordRhsExpansion φ κ F
        (classicalGalerkinUnitWordFamily φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per) w p := by
  rcases p with ⟨t, x⟩
  rcases Set.mem_prod.mp hp with ⟨ht, hx⟩
  let s : Icc (0 : ℝ) 1 := ⟨t, ht.1, ht.2⟩
  let u := classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per s
  let b := AVenhance.streamVel φ t
  have hcl : classicalGalerkinUnitSlabClamp t = s := by
    apply Subtype.ext
    simp [s, classicalGalerkinUnitSlabClamp, max_eq_right ht.1,
      min_eq_right ht.2]
  have hu : ContDiff ℝ (⊤ : ℕ∞) u := by
    simpa [u] using classicalGalerkinRealSmoothLift_contDiff
      φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per s
  have hb : ContDiff ℝ (⊤ : ℕ∞) b := by
    have hvel := (streamVel_smoothPeriodic φ hφ).smooth
    have hslice : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec 2 => ((t : ℝ), y)) :=
      contDiff_const.prodMk contDiff_id
    have hcomp := hvel.comp hslice
    change ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec 2 => AVenhance.streamVel φ t y) at hcomp
    simpa [b] using hcomp
  have hFslice : ContDiff ℝ (⊤ : ℕ∞) (F t) :=
    classicalSmooth_slice_nonneg hF ht.1
  have hlap : ContDiff ℝ (⊤ : ℕ∞) (fun y => AVenhance.spaceLap u y) :=
    classicalBoundarySpaceLap_contDiff u hu
  have htransport : ContDiff ℝ (⊤ : ℕ∞) (classicalTransport b u) :=
    classicalBoundaryTransport_contDiff b u hb hu
  have hsumSmooth : ContDiff ℝ (⊤ : ℕ∞)
      (fun y => F t y + κ * AVenhance.spaceLap u y) :=
    hFslice.add (contDiff_const.mul hlap)
  have hwhole : ContDiff ℝ (⊤ : ℕ∞)
      (fun y => F t y + κ * AVenhance.spaceLap u y - classicalTransport b u y) :=
    hsumSmooth.sub htransport
  have hlinear : classicalWordDerivative w
      (fun y => F t y + κ * AVenhance.spaceLap u y - classicalTransport b u y) =
      fun y => classicalWordDerivative w (F t) y +
        κ * classicalWordDerivative w (fun y => AVenhance.spaceLap u y) y -
        classicalWordDerivative w (classicalTransport b u) y := by
    rw [classicalWordDerivative_sub w _ _ hsumSmooth htransport,
      GalerkinHorizonSmoothnessRhs.classicalBoundaryWordDerivative_add w (F t) _ hFslice
        (contDiff_const.mul hlap),
      classicalWordDerivative_const_mul w κ (fun y => AVenhance.spaceLap u y) hlap]
  have hforcing : classicalJointWordDerivative w (Function.uncurry F) (t, x) =
      classicalWordDerivative w (F t) x :=
    classicalJointWordDerivative_eq_slice w (Function.uncurry F) (by
      simpa [classicalHalfSpace] using hF) ht.1 x
  have hlapWords : classicalWordDerivative w (fun y => AVenhance.spaceLap u y) x =
      ∑ i : Fin 2, classicalWordDerivative ([i, i] ++ w) u x := by
    rw [classicalWordDerivative_spaceLap w u hu]
    change (∑ i : Fin 2,
      classicalWordDerivative [i, i] (classicalWordDerivative w u) x) = _
    apply Finset.sum_congr rfl
    intro i hi
    rw [GalerkinHorizonSmoothnessRhs.classicalBoundaryWordDerivative_append [i, i] w u]
  have hstreamJoint : ContDiffOn ℝ (⊤ : ℕ∞)
      (Function.uncurry (AVenhance.streamVel φ)) classicalHalfSpace := by
    exact (streamVel_smoothPeriodic φ hφ).smooth.contDiffOn
  have hcoeff (v : List (Fin 2)) (j : Fin 2) :
      classicalJointWordDerivative v
        (fun z => AVenhance.streamVel φ z.1 z.2 j) (t, x) =
      classicalWordDerivative v (fun y => b y j) x := by
    have hcoord : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun z => AVenhance.streamVel φ z.1 z.2 j) classicalHalfSpace := by
      have hcoord' : ContDiffOn ℝ (⊤ : ℕ∞)
          (fun z => (Function.uncurry (AVenhance.streamVel φ) z) j) classicalHalfSpace :=
        (contDiffOn_pi.1 hstreamJoint) j
      simpa only [Function.uncurry] using hcoord'
    simpa [b] using classicalJointWordDerivative_eq_slice v
      (fun z => AVenhance.streamVel φ z.1 z.2 j) hcoord ht.1 x
  have happend (v : List (Fin 2)) (j : Fin 2) :
      classicalWordDerivative v (fun y => AVenhance.spaceGrad u y j) =
        classicalWordDerivative (v ++ [j]) u := by
    change classicalWordDerivative v (classicalWordDerivative [j] u) = _
    exact GalerkinHorizonSmoothnessRhs.classicalBoundaryWordDerivative_append v [j] u
  have htransportExpansion (j : Fin 2) :
      classicalWordProductExpansion w (fun y => b y j)
        (fun y => AVenhance.spaceGrad u y j) x =
      ((classicalWordSplits w).map fun r =>
        classicalJointWordDerivative r.1
          (fun z => AVenhance.streamVel φ z.1 z.2 j) (t, x) *
        classicalGalerkinUnitWordFamily φ hφ κ hκ F hF hFper
          θ₀ hθ₀ hθ₀per (r.2 ++ [j]) (t, x)).sum := by
    let L := classicalWordSplits w
    change ((L.map (fun r =>
        classicalWordProductTerm r (fun y => b y j)
          (fun y => AVenhance.spaceGrad u y j))).sum x) = _
    have hsum (M : List (List (Fin 2) × List (Fin 2))) :
        ((M.map fun r => classicalWordProductTerm r (fun y => b y j)
          (fun y => AVenhance.spaceGrad u y j)).sum) x =
        ((M.map fun r =>
          classicalJointWordDerivative r.1
            (fun z => AVenhance.streamVel φ z.1 z.2 j) (t, x) *
          classicalGalerkinUnitWordFamily φ hφ κ hκ F hF hFper
            θ₀ hθ₀ hθ₀per (r.2 ++ [j]) (t, x)).sum) := by
      induction M with
      | nil => rfl
      | cons r M ih =>
        simp only [List.map_cons, List.sum_cons, Pi.add_apply]
        change (classicalWordDerivative r.1 (fun y => b y j) x *
          classicalWordDerivative r.2 (fun y => AVenhance.spaceGrad u y j) x) +
          ((M.map fun r => classicalWordProductTerm r (fun y => b y j)
            (fun y => AVenhance.spaceGrad u y j)).sum x) = _
        rw [hcoeff r.1 j, happend r.2 j]
        simp [classicalGalerkinUnitWordFamily, hcl, u, s, ih]
    exact hsum L
  have htransportEq : classicalWordDerivative w (classicalTransport b u) x =
      ∑ j : Fin 2, ((classicalWordSplits w).map fun r =>
        classicalJointWordDerivative r.1
          (fun z => AVenhance.streamVel φ z.1 z.2 j) (t, x) *
        classicalGalerkinUnitWordFamily φ hφ κ hκ F hF hFper
          θ₀ hθ₀ hθ₀per (r.2 ++ [j]) (t, x)).sum := by
    rw [classicalWordDerivative_transport w b u hb hu]
    simp only [classicalWordProductExpansion]
    apply Finset.sum_congr rfl
    intro j hj
    exact htransportExpansion j
  rw [classicalGalerkinUnitWordRhs, hcl]
  change classicalWordDerivative w
      (fun y => F t y + κ * AVenhance.spaceLap u y -
        classicalTransport b u y) x =
      classicalGalerkinUnitWordRhsExpansion φ κ F
        (classicalGalerkinUnitWordFamily φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per) w (t, x)
  calc
    _ = classicalWordDerivative w (F t) x +
        κ * classicalWordDerivative w (fun y => AVenhance.spaceLap u y) x -
        classicalWordDerivative w (classicalTransport b u) x := congrFun hlinear x
    _ = _ := by
      simp only [classicalGalerkinUnitWordRhsExpansion]
      rw [← hforcing, hlapWords, htransportEq]
      simp [classicalGalerkinUnitWordFamily, hcl, u, s]

theorem classicalGalerkinUnitWordRhs_contDiffOn_of_family
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Ici (0 : ℝ) ×ˢ univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀)
    (S : Set (ℝ × Vec 2)) (hS : S = Icc (0 : ℝ) 1 ×ˢ univ)
    (k : ℕ)
    (hf : ∀ w, ContDiffOn ℝ (k : WithTop ℕ∞)
      (classicalGalerkinUnitWordFamily φ hφ κ hκ F hF hFper
        θ₀ hθ₀ hθ₀per w) S) :
    ∀ w, ContDiffOn ℝ (k : WithTop ℕ∞)
      (classicalGalerkinUnitWordRhs φ hφ κ hκ F hF hFper
        θ₀ hθ₀ hθ₀per w) S := by
  have hexp := GalerkinHorizonSmoothnessRhs.classicalBoundaryWordRhsExpansion_contDiffOn φ hφ κ F
    (by simpa [classicalHalfSpace] using hF)
    (classicalGalerkinUnitWordFamily φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per)
    S hS k hf
  intro w
  apply (hexp w).congr
  intro p hp
  exact classicalGalerkinUnitWordRhs_eq_expansion_on
    φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per w p (by simpa [hS] using hp)

end AVenhance.Infra.Classical

end
