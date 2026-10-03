/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FaaDiBruno.TransportCommutator
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FaaDiBruno.TransportSolution.Definitions
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FaaDiBruno.TransportSolution.GradientEstimates
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FaaDiBruno.TransportSolution.GradientMatrix
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FaaDiBruno.TransportSolution.Characteristics
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.Laws

/-! # Transport Characteristic Jets

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

open scoped ContDiff

noncomputable section

namespace AVenhance.FaaDiBruno
open Homogenization

theorem list_ofFn_map {α β : Type*} {n : ℕ}
    (I : Fin n → α) (f : α → β) :
    List.ofFn (fun j => f (I j)) = (List.ofFn I).map f := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.ofFn_succ', List.ofFn_succ']
      simp only [ih, List.map_concat]

/-- A list of coordinate directions is one of the ordered partials used in
the paper's seminorm. -/
theorem directionalJet_coordinateList_eq_orderedPartial
    (J : List (Fin 2)) {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Vec 2 → F) (hf : ContDiff ℝ ∞ f) (x : Vec 2) :
    directionalJet (J.map (coordinateVector 2)) f x =
      orderedPartial J.length f x (fun j => J.get j) := by
  have hdirs : List.ofFn (fun j : Fin J.length =>
      coordinateVector 2 (J.get j)) = J.map (coordinateVector 2) := by
    rw [list_ofFn_map, List.ofFn_get]
  rw [← hdirs]
  exact (orderedPartial_eq_directionalJet f hf x (fun j => J.get j)).symm

theorem directionalJet_coordinateList_norm_le
    (J : List (Fin 2)) (f : Vec 2 → Vec 2)
    (hf : ContDiff ℝ ∞ f) {C R : ℝ} (hR : 0 < R) (hC : 0 ≤ C)
    (hs : snorm f J.length R ≤ ENNReal.ofReal C) (x : Vec 2) :
    ‖directionalJet (J.map (coordinateVector 2)) f x‖ ≤
      C * J.length.factorial * R ^ J.length / (J.length + 1 : ℝ) ^ 2 := by
  have hf' : ContDiff ℝ J.length f :=
    hf.of_le (show ((J.length : ℕ∞) : ℕ∞ω) ≤ ∞ from by simp)
  have hpartial := orderedPartial_norm_le_of_snorm_le
    (m := J.length) (n := J.length) f hf' le_rfl hR hC hs x
      (fun j => J.get j)
  rw [directionalJet_coordinateList_eq_orderedPartial J f hf x]
  exact hpartial

theorem jointSpatialCoordinateComponentJet_eq_slice
    (J : List (Fin 2)) (b : ℝ × Vec 2 → Vec 2)
    (hb : ContDiff ℝ ∞ b) (t : ℝ) (x : Vec 2) (i : Fin 2) :
    directionalJet (jointSpatialDirections
      (J.map (coordinateVector 2))) (fun q => b q i) (t, x) =
      directionalJet (J.map (coordinateVector 2)) (fun y => b (t, y)) x i := by
  let P : Vec 2 →L[ℝ] ℝ := ContinuousLinearMap.proj i
  let D : List (ℝ × Vec 2) := jointSpatialDirections (J.map (coordinateVector 2))
  have hcomp := directionalJet_comp_clm D P b hb
  have hslice := jointSpatialDirectionalJet_eq_slice
    (J.map (coordinateVector 2)) b hb t x
  have hp := congrFun hcomp (t, x)
  have hcomp' : directionalJet D (fun q => b q i) (t, x) =
      directionalJet D b (t, x) i := by
    simpa [P, Function.comp_def] using hp
  calc
    _ = directionalJet D b (t, x) i := hcomp'
    _ = directionalJet (J.map (coordinateVector 2))
        (fun y => b (t, y)) x i := congrArg (fun z : Vec 2 => z i) hslice

theorem jointSpatialGradientJet_eq_slice
    (J : List (Fin 2)) (F : ℝ × Vec 2 → Vec 2)
    (hF : ContDiff ℝ ∞ F) (t : ℝ) (x : Vec 2) (i : Fin 2) :
    directionalJet (jointSpatialDirections (J.map (coordinateVector 2)))
        (fun q => fderiv ℝ F q (0, coordinateVector 2 i)) (t, x) =
    directionalJet ((J.map (coordinateVector 2)) ++ [coordinateVector 2 i])
        (fun y => F (t, y)) x := by
  have hFderivField : ContDiff ℝ ∞ (fun q => fderiv ℝ F q) :=
    hF.fderiv_right (by simp)
  have hFderivCoord : ContDiff ℝ ∞
      (fun q => fderiv ℝ F q (0, coordinateVector 2 i)) := by
    exact hFderivField.clm_apply (contDiff_const : ContDiff ℝ ∞
      (fun _ : ℝ × Vec 2 => ((0 : ℝ), coordinateVector 2 i)))
  have hslice := jointSpatialDirectionalJet_eq_slice
    (J.map (coordinateVector 2))
    (fun q => fderiv ℝ F q (0, coordinateVector 2 i)) hFderivCoord t x
  have happend := directionalJet_append
    (J.map (coordinateVector 2)) [coordinateVector 2 i] (fun y => F (t, y))
  have hsliceDeriv : directionalJet (J.map (coordinateVector 2))
      (fun y => fderiv ℝ F (t, y) (0, coordinateVector 2 i)) x =
      directionalJet (J.map (coordinateVector 2))
        (fun y => fderiv ℝ (fun z => F (t, z)) y (coordinateVector 2 i)) x := by
    congr 1
    funext y
    exact jointSpatialDirectionalDerivative_eq_slice_general F hF t y
      (coordinateVector 2 i)
  calc
    _ = directionalJet (J.map (coordinateVector 2))
        (fun y => fderiv ℝ (fun z => F (t, z)) y (coordinateVector 2 i)) x :=
          hslice.trans hsliceDeriv
    _ = directionalJet ((J.map (coordinateVector 2)) ++ [coordinateVector 2 i])
        (fun y => F (t, y)) x := by
          simpa [directionalJet] using congrFun happend.symm x

theorem TransportCharacteristicJets.list_sum_norm_le_of_forall
    {α : Type*} (L : List α) (f : α → Vec 2) (g : α → ℝ)
    (hfg : ∀ a ∈ L, ‖f a‖ ≤ g a) :
    ‖(L.map f).sum‖ ≤ (L.map g).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
      simp only [List.map_cons, List.sum_cons]
      have ha := hfg a (by simp)
      have htail : ∀ b ∈ L, ‖f b‖ ≤ g b := by
        intro b hb
        exact hfg b (by simp [hb])
      have hrest := ih htail
      calc
        ‖f a + (L.map f).sum‖ ≤ ‖f a‖ + ‖(L.map f).sum‖ := norm_add_le _ _
        _ ≤ g a + (L.map g).sum := add_le_add ha hrest

theorem TransportCharacteristicJets.list_sum_add_const {α : Type*} (L : List α)
    (g : α → ℝ) (c : ℝ) :
    (L.map fun a => c + g a).sum = (L.length : ℝ) * c + (L.map g).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add,
        Nat.cast_one]
      rw [ih]
      ring

theorem TransportCharacteristicJets.list_sum_le_of_forall {α : Type*} (L : List α)
    (f g : α → ℝ) (hfg : ∀ a ∈ L, f a ≤ g a) :
    (L.map f).sum ≤ (L.map g).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
      simp only [List.map_cons, List.sum_cons]
      have ha := hfg a (by simp)
      have htail : ∀ b ∈ L, f b ≤ g b := by
        intro b hb
        exact hfg b (by simp [hb])
      exact add_le_add ha (ih htail)

theorem TransportCharacteristicJets.list_sum_map_add {α : Type*} (L : List α)
    (f g : α → ℝ) :
    (L.map fun a => f a + g a).sum = (L.map f).sum + (L.map g).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      ring

theorem TransportCharacteristicJets.list_sum_if_count {α : Type*} (L : List α)
    (p : α → Prop) [DecidablePred p] (c : ℝ) :
    (L.map fun a => if p a then c else 0).sum =
      (L.countP (fun a => decide (p a)) : ℝ) * c := by
  induction L with
  | nil => simp
  | cons a L ih =>
      by_cases ha : p a
      · simp [ha, ih]
        ring
      · simp [ha, ih]

theorem TransportCharacteristicJets.orderedPartial_list_get_bound {n : ℕ}
    (K : List (Fin 2)) (hK : K.length = n)
    (f : Vec 2 → Vec 2) (x : Vec 2) {U : ℝ}
    (hU : ∀ I : Fin n → Fin 2, ‖orderedPartial n f x I‖ ≤ U) :
    ‖orderedPartial K.length f x (fun j => K.get j)‖ ≤ U := by
  cases hK
  exact hU (fun j => K.get j)

theorem TransportCharacteristicJets.contDiff_slice_joint
    (f : ℝ → Vec 2 → Vec 2) (hf : ContDiff ℝ ∞ (Function.uncurry f))
    (t : ℝ) : ContDiff ℝ ∞ (f t) := by
  have hpair : ContDiff ℝ ∞ (fun x : Vec 2 => (t, x)) := by fun_prop
  simpa [Function.uncurry, Function.comp_def] using hf.comp hpair

private theorem transportSourceJet_coordinate_norm_le_local_term1 :
  ∀ {n : ℕ} (I : Fin n → Fin (2 : ℕ)) {b Y : ℝ → Vec (2 : ℕ) → Vec (2 : ℕ)},
    ContDiff ℝ ∞ (Function.uncurry b) →
      ContDiff ℝ ∞ (Function.uncurry Y) →
        ∀ {C_f R U T : ℝ} (RY : ℝ → ℝ),
          (0 : ℝ) < R →
            (∀ (t : ℝ), (0 : ℝ) < RY t) →
              (0 : ℝ) ≤ C_f →
                ∀ (A : ℝ → ℕ → ℝ),
                  (∀ (t : ℝ) (k : ℕ), (0 : ℝ) ≤ A t k) →
                    (∀ (t : ℝ) (m : ℕ), (1 : ℕ) ≤ m → m ≤ n → snorm (b t) m R ≤ ENNReal.ofReal
                        C_f) →
                      (∀ (t : ℝ),
                          |t| ≤ T → ∀ (k : ℕ), (1 : ℕ) ≤ k → k < n → snorm (Y t) k (RY t) ≤
                              ENNReal.ofReal (A t k)) →
                        ∀ (t : ℝ),
                          |t| ≤ T →
                            ∀ (x : Vec (2 : ℕ)),
                              (∀ (J : Fin n → Fin (2 : ℕ)), ‖orderedPartial n (Y t) x J‖ ≤ U) →
                                let L : List (Fin (2 : ℕ)) := List.ofFn I;
                                let φ : Fin (2 : ℕ) → ℝ × Vec (2 : ℕ) := fun (i : Fin (2 : ℕ)) =>
                                  ((0 : ℝ), coordinateVector (2 : ℕ) i);
                                let baseWeight : List (Fin (2 : ℕ)) × List (Fin (2 : ℕ)) → ℝ :=
                                  fun (p : List (Fin (2 : ℕ)) × List (Fin (2 : ℕ))) =>
                                  C_f * (↑p.1.length.factorial : ℝ) * R ^ p.1.length /
                                      ((↑p.1.length : ℝ) + (1 : ℝ)) ^ (2 : ℕ) *
                                    (A t (p.2.length + (1 : ℕ)) * (↑(p.2.length + (1 :
                                        ℕ)).factorial : ℝ) *
                                        RY t ^ (p.2.length + (1 : ℕ)) /
                                      ((↑p.2.length : ℝ) + (2 : ℝ)) ^ (2 : ℕ));
                                let lowWeight : List (Fin (2 : ℕ)) × List (Fin (2 : ℕ)) → ℝ :=
                                  fun (p : List (Fin (2 : ℕ)) × List (Fin (2 : ℕ))) =>
                                  if (2 : ℕ) ≤ p.1.length then baseWeight p else (0 : ℝ);
                                let topCoefficient : ℝ := C_f * R / (4 : ℝ) * U;
                                let pointWeight : List (Fin (2 : ℕ)) × List (Fin (2 : ℕ)) → ℝ :=
                                  fun (p : List (Fin (2 : ℕ)) × List (Fin (2 : ℕ))) =>
                                  if p.1.length = (1 : ℕ) then topCoefficient else lowWeight p;
                                let alloc : List (List (Fin (2 : ℕ)) × List (Fin (2 : ℕ))) :=
                                    directionalSplitsNonempty L;
                                (∀ (s : ℝ), ContDiff ℝ ∞ (b s)) →
                                  (∀ (s : ℝ), ContDiff ℝ ∞ (Y s)) →
                                    L.length = n →
                                      ∀ p ∈ alloc,
                                        ∀ (i : Fin (2 : ℕ)),
                                          ‖directionalJet (List.map φ p.1)
                                                  (fun (q : ℝ × Vec (2 : ℕ)) => Function.uncurry b
                                                      q i) (t, x) •
                                                directionalJet (List.map φ p.2)
                                                  (fun (q : ℝ × Vec (2 : ℕ)) =>
                                                    (fderiv ℝ (Function.uncurry Y) q : ℝ × Vec (2
                                                        : ℕ) → Vec (2 : ℕ))
                                                      ((0 : ℝ), coordinateVector (2 : ℕ) i))
                                                  (t, x)‖ ≤
                                            pointWeight p
    := by
  intro n I b Y hb hY C_f R U T RY hR hRY hCf A hA hB hYbound t ht x hUjet L φ baseWeight
      lowWeight topCoefficient pointWeight alloc hbSlice hYSlice hlenI p hp i
  have hlen := directionalSplitsNonempty_length_sum L p hp
  have hmpos := directionalSplitsNonempty_left_pos L p hp
  have hlen' : p.1.length + p.2.length = n := by
    rw [← hlenI]
    exact hlen
  have hmle : p.1.length ≤ n := by omega
  have hcoeff := jointSpatialCoordinateComponentJet_eq_slice p.1
    (Function.uncurry b) hb t x i
  have hcoeff' :
      directionalJet (p.1.map φ) (fun q => Function.uncurry b q i) (t, x) =
        directionalJet (p.1.map (coordinateVector 2)) (b t) x i := by
    simpa [φ, jointSpatialDirections, Function.comp_def, Function.uncurry] using hcoeff
  have hcoeffBound :
      ‖directionalJet (p.1.map (coordinateVector 2)) (b t) x i‖ ≤
        C_f * p.1.length.factorial * R ^ p.1.length /
          (p.1.length + 1 : ℝ) ^ 2 := by
    have hseminorm := hB t p.1.length (by omega) hmle
    have hvec := directionalJet_coordinateList_norm_le p.1 (b t) (hbSlice t)
      hR hCf hseminorm x
    exact (norm_le_pi_norm _ _).trans (by simpa using hvec)
  have hgrad := jointSpatialGradientJet_eq_slice p.2
    (Function.uncurry Y) hY t x i
  have hgrad' :
      directionalJet (p.2.map φ) (fun q => fderiv ℝ (Function.uncurry Y) q
        (0, coordinateVector 2 i)) (t, x) =
      directionalJet ((p.2.map (coordinateVector 2)) ++ [coordinateVector 2 i])
        (Y t) x := by
    simpa [φ, jointSpatialDirections, Function.comp_def, Function.uncurry] using hgrad
  have hqLen : (p.2 ++ [i]).length = p.2.length + 1 := by simp
  have hqLenN : p.2.length + 1 ≤ n := by omega
  have htopCase : p.1.length = 1 ∨ 2 ≤ p.1.length := by omega
  rcases htopCase with htop | hlow
  · have hqLenEq : p.2.length + 1 = n := by omega
    have hYjet :
        ‖directionalJet ((p.2.map (coordinateVector 2)) ++ [coordinateVector 2 i])
            (Y t) x‖ ≤ U := by
      have hKLen : (p.2 ++ [i]).length = n := by
        rw [hqLen]
        exact hqLenEq
      calc
        _ = ‖directionalJet ((p.2 ++ [i]).map (coordinateVector 2))
            (Y t) x‖ := by
              congr 1
              simp [List.map_append]
        _ = ‖orderedPartial (p.2 ++ [i]).length (Y t) x
            (fun j => (p.2 ++ [i]).get j)‖ := by
              rw [directionalJet_coordinateList_eq_orderedPartial
                (p.2 ++ [i]) (Y t) (hYSlice t) x]
        _ ≤ U := TransportCharacteristicJets.orderedPartial_list_get_bound (p.2 ++ [i]) hKLen
          (Y t) x hUjet
    have hcoeffTop :
        ‖directionalJet (p.1.map (coordinateVector 2)) (b t) x i‖ ≤ C_f * R / 4 := by
      have hcoeff1 := hcoeffBound
      rw [htop] at hcoeff1
      norm_num [Nat.factorial_one] at hcoeff1 ⊢
      exact hcoeff1
    rw [norm_smul, hcoeff', hgrad']
    have hlowzero : lowWeight p = 0 := by simp [lowWeight, htop]
    have hprod :
        ‖directionalJet (p.1.map (coordinateVector 2)) (b t) x i‖ *
            ‖directionalJet ((p.2.map (coordinateVector 2)) ++ [coordinateVector 2 i])
              (Y t) x‖ ≤ topCoefficient := by
      dsimp [topCoefficient]
      exact mul_le_mul hcoeffTop hYjet (norm_nonneg _) (by positivity)
    simpa [pointWeight, htop, hlowzero] using hprod
  · have hqpos : 1 ≤ p.2.length + 1 := by omega
    have hqle : p.2.length + 1 < n := by omega
    have hYseminorm := hYbound t ht (p.2.length + 1) hqpos hqle
    have hYvec :
        ‖directionalJet ((p.2.map (coordinateVector 2)) ++ [coordinateVector 2 i])
            (Y t) x‖ ≤
          A t (p.2.length + 1) * (p.2.length + 1).factorial *
            RY t ^ (p.2.length + 1) / (p.2.length + 2 : ℝ) ^ 2 := by
      have h := directionalJet_coordinateList_norm_le (p.2 ++ [i]) (Y t)
        (hYSlice t) (hRY t) (hA t (p.2.length + 1))
        (by simpa [hqLen] using hYseminorm) x
      rw [hqLen] at h
      have hden : ((p.2.length + 1 : ℕ) : ℝ) + 1 =
          (p.2.length + 2 : ℝ) := by push_cast; ring
      rw [hden] at h
      simpa [List.map_append, List.map_cons, List.map_nil] using h
    have htermLower :
        ‖directionalJet (p.1.map (coordinateVector 2)) (b t) x i‖ *
            ‖directionalJet ((p.2.map (coordinateVector 2)) ++ [coordinateVector 2 i])
              (Y t) x‖ ≤ baseWeight p := by
      have hcoeffLow :
          ‖directionalJet (p.1.map (coordinateVector 2)) (b t) x i‖ ≤
            C_f * p.1.length.factorial * R ^ p.1.length /
              (p.1.length + 1 : ℝ) ^ 2 := hcoeffBound
      exact mul_le_mul hcoeffLow hYvec (norm_nonneg _) (by positivity)
    have hlowzero : lowWeight p = baseWeight p := by
      simp [lowWeight, hlow]
    rw [norm_smul, hcoeff', hgrad']
    have hne : p.1.length ≠ 1 := by omega
    calc
      _ ≤ baseWeight p := htermLower
      _ = pointWeight p := by simp [pointWeight, hne, hlowzero]

/-- A pointwise source estimate with the current order-`n` jet left as a
linear term. This is the a-priori finiteness estimate used before the sharp
corrected absorption. -/
theorem transportSourceJet_coordinate_norm_le_local
    {n : ℕ} (I : Fin n → Fin 2)
    {b g Y : ℝ → Vec 2 → Vec 2}
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hg : ContDiff ℝ ∞ (Function.uncurry g))
    (hY : ContDiff ℝ ∞ (Function.uncurry Y))
    {C_f C_g R U T : ℝ} (RY : ℝ → ℝ) (hR : 0 < R)
    (hRY : ∀ t, 0 < RY t)
    (hCf : 0 ≤ C_f) (hCg : 0 ≤ C_g)
    (A : ℝ → ℕ → ℝ) (hA : ∀ t k, 0 ≤ A t k)
    (hB : ∀ t m, 1 ≤ m → m ≤ n →
      snorm (b t) m R ≤ ENNReal.ofReal C_f)
    (hG : ∀ t, snorm (g t) n R ≤ ENNReal.ofReal C_g)
    (hYbound : ∀ t, |t| ≤ T → ∀ k, 1 ≤ k → k < n →
      snorm (Y t) k (RY t) ≤ ENNReal.ofReal (A t k))
    (t : ℝ) (ht : |t| ≤ T) (x : Vec 2)
    (hUjet : ∀ J : Fin n → Fin 2,
      ‖orderedPartial n (Y t) x J‖ ≤ U) :
    ‖transportSourceJet
        (List.ofFn fun j => coordinateVector 2 (I j)) b g Y (t, x)‖ ≤
      C_g * n.factorial * R ^ n / (n + 1 : ℝ) ^ 2 +
        2 * ((n : ℝ) * (C_f * R / 4 * U) +
          ((directionalSplitsNonempty (List.ofFn I)).map fun p =>
            if 2 ≤ p.1.length then
              C_f * p.1.length.factorial * R ^ p.1.length /
                  (p.1.length + 1 : ℝ) ^ 2 *
                (A t (p.2.length + 1) * (p.2.length + 1).factorial *
                  RY t ^ (p.2.length + 1) / (p.2.length + 2 : ℝ) ^ 2)
            else 0).sum) := by
  let L := List.ofFn I
  let φ : Fin 2 → ℝ × Vec 2 := fun i => ((0 : ℝ), coordinateVector 2 i)
  let V : List (Vec 2) := List.ofFn fun j => coordinateVector 2 (I j)
  let baseWeight (p : List (Fin 2) × List (Fin 2)) : ℝ :=
    C_f * p.1.length.factorial * R ^ p.1.length / (p.1.length + 1 : ℝ) ^ 2 *
      (A t (p.2.length + 1) * (p.2.length + 1).factorial *
        RY t ^ (p.2.length + 1) / (p.2.length + 2 : ℝ) ^ 2)
  let lowWeight (p : List (Fin 2) × List (Fin 2)) : ℝ :=
    if 2 ≤ p.1.length then baseWeight p else 0
  let topCoefficient : ℝ := C_f * R / 4 * U
  let pointWeight (p : List (Fin 2) × List (Fin 2)) : ℝ :=
    if p.1.length = 1 then topCoefficient else lowWeight p
  let alloc := directionalSplitsNonempty L
  have hcoords : V = L.map (coordinateVector 2) := by
    dsimp [V, L]
    exact list_ofFn_map I (coordinateVector 2)
  have hsplit : directionalSplitsNonempty (jointSpatialDirections V) =
      alloc.map fun p => (p.1.map φ, p.2.map φ) := by
    rw [hcoords]
    simpa [alloc, jointSpatialDirections, φ, Function.comp_def] using
      directionalSplitsNonempty_map φ L
  have hsource := transportSourceJet_nonempty_identity V b g Y hb hg hY
  have hsourceAt := congrFun hsource (t, x)
  rw [hsplit] at hsourceAt
  simp only [List.map_map, Function.comp_def] at hsourceAt
  have hspatial : transportSpatialJet V (Function.uncurry g) =
      directionalJet (jointSpatialDirections V) (Function.uncurry g) :=
    transportSpatialJet_eq_jointDirectionalJet V (Function.uncurry g)
  rw [hspatial] at hsourceAt
  have hbSlice : ∀ s, ContDiff ℝ ∞ (b s) := fun s =>
      TransportCharacteristicJets.contDiff_slice_joint b hb s
  have hgSlice : ∀ s, ContDiff ℝ ∞ (g s) := fun s =>
      TransportCharacteristicJets.contDiff_slice_joint g hg s
  have hYSlice : ∀ s, ContDiff ℝ ∞ (Y s) := fun s =>
      TransportCharacteristicJets.contDiff_slice_joint Y hY s
  have hlenI : L.length = n := by simp [L]
  have hfirst :
      ‖directionalJet (jointSpatialDirections V) (Function.uncurry g) (t, x)‖ ≤
        C_g * n.factorial * R ^ n / (n + 1 : ℝ) ^ 2 := by
    rw [jointSpatialDirectionalJet_eq_slice V (Function.uncurry g) hg t x]
    have hG' : snorm (g t) L.length R ≤ ENNReal.ofReal C_g := by
      rw [hlenI]
      exact hG t
    have h := directionalJet_coordinateList_norm_le L (g t) (hgSlice t)
      hR hCg hG' x
    simpa [L, hcoords, hlenI] using h
  have hterm (p : List (Fin 2) × List (Fin 2))
      (hp : p ∈ alloc) (i : Fin 2) :
      ‖directionalJet (p.1.map φ) (fun q => Function.uncurry b q i) (t, x) •
          directionalJet (p.2.map φ) (fun q => fderiv ℝ (Function.uncurry Y) q
            (0, coordinateVector 2 i)) (t, x)‖ ≤ pointWeight p := by
    exact @transportSourceJet_coordinate_norm_le_local_term1 n I b Y hb hY C_f R U T RY hR hRY hCf
        A hA hB hYbound t ht x hUjet hbSlice hYSlice hlenI p hp i
  have halloc (i : Fin 2) :
      ‖(alloc.map fun p =>
          directionalJet (p.1.map φ) (fun q => Function.uncurry b q i) (t, x) •
            directionalJet (p.2.map φ) (fun q => fderiv ℝ (Function.uncurry Y) q
              (0, coordinateVector 2 i)) (t, x)).sum‖ ≤
        (n : ℝ) * topCoefficient + (alloc.map lowWeight).sum := by
    calc
      _ ≤ (alloc.map fun p =>
          ‖directionalJet (p.1.map φ) (fun q => Function.uncurry b q i) (t, x) •
            directionalJet (p.2.map φ) (fun q => fderiv ℝ (Function.uncurry Y) q
              (0, coordinateVector 2 i)) (t, x)‖).sum :=
        TransportCharacteristicJets.list_sum_norm_le_of_forall alloc
          (fun p => directionalJet (p.1.map φ)
            (fun q => Function.uncurry b q i) (t, x) •
            directionalJet (p.2.map φ)
              (fun q => fderiv ℝ (Function.uncurry Y) q
                (0, coordinateVector 2 i)) (t, x))
          (fun p => ‖directionalJet (p.1.map φ)
              (fun q => Function.uncurry b q i) (t, x) •
            directionalJet (p.2.map φ)
              (fun q => fderiv ℝ (Function.uncurry Y) q
                (0, coordinateVector 2 i)) (t, x)‖)
          (fun p hp => le_rfl)
      _ ≤ (n : ℝ) * topCoefficient + (alloc.map lowWeight).sum := by
        have hpoint (p : List (Fin 2) × List (Fin 2)) (hp : p ∈ alloc) :
            ‖directionalJet (p.1.map φ) (fun q => Function.uncurry b q i) (t, x) •
              directionalJet (p.2.map φ) (fun q => fderiv ℝ (Function.uncurry Y) q
                (0, coordinateVector 2 i)) (t, x)‖ ≤ pointWeight p :=
          hterm p hp i
        have hweightIdentity (p : List (Fin 2) × List (Fin 2)) (hp : p ∈ alloc) :
            pointWeight p =
              (if p.1.length = 1 then topCoefficient else 0) + lowWeight p := by
          have hpos := directionalSplitsNonempty_left_pos L p hp
          by_cases htop : p.1.length = 1
          · have hlowzero : lowWeight p = 0 := by simp [lowWeight, htop]
            simp [pointWeight, htop, hlowzero]
          · have hlow : 2 ≤ p.1.length := by omega
            simp [pointWeight, htop, lowWeight, hlow]
        have hmap : alloc.map pointWeight = alloc.map
            (fun p => (if p.1.length = 1 then topCoefficient else 0) + lowWeight p) := by
          apply List.map_congr_left
          intro p hp
          exact hweightIdentity p hp
        have htopCount :
            (alloc.map fun p => if p.1.length = 1 then topCoefficient else 0).sum =
              (n : ℝ) * topCoefficient := by
          rw [TransportCharacteristicJets.list_sum_if_count]
          have hcount := directionalSplitsNonempty_count_leftLength_eq_one L
          have hcount' : alloc.countP (fun p => decide (p.1.length = 1)) = n := by
            simpa [alloc, L] using hcount
          rw [hcount']
        have hlowerSum :
            (alloc.map fun p =>
              (if p.1.length = 1 then topCoefficient else 0) + lowWeight p).sum =
                (n : ℝ) * topCoefficient + (alloc.map lowWeight).sum := by
          rw [TransportCharacteristicJets.list_sum_map_add, htopCount]
        calc
          _ ≤ (alloc.map pointWeight).sum :=
            TransportCharacteristicJets.list_sum_le_of_forall alloc
              (fun p => ‖directionalJet (p.1.map φ)
                (fun q => Function.uncurry b q i) (t, x) •
                directionalJet (p.2.map φ)
                  (fun q => fderiv ℝ (Function.uncurry Y) q
                    (0, coordinateVector 2 i)) (t, x)‖)
              pointWeight hpoint
          _ = (n : ℝ) * topCoefficient + (alloc.map lowWeight).sum := by
            rw [hmap, hlowerSum]
  have hcomm :
      ‖∑ i : Fin 2, (alloc.map fun p =>
          directionalJet (p.1.map φ) (fun q => Function.uncurry b q i) (t, x) •
            directionalJet (p.2.map φ) (fun q => fderiv ℝ (Function.uncurry Y) q
              (0, coordinateVector 2 i)) (t, x)).sum‖ ≤
        2 * ((n : ℝ) * topCoefficient + (alloc.map lowWeight).sum) := by
    calc
      _ ≤ ∑ i : Fin 2, ‖(alloc.map fun p =>
          directionalJet (p.1.map φ) (fun q => Function.uncurry b q i) (t, x) •
            directionalJet (p.2.map φ) (fun q => fderiv ℝ (Function.uncurry Y) q
              (0, coordinateVector 2 i)) (t, x)).sum‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin 2,
          ((n : ℝ) * topCoefficient + (alloc.map lowWeight).sum) :=
        Finset.sum_le_sum fun i hi => halloc i
      _ = 2 * ((n : ℝ) * topCoefficient + (alloc.map lowWeight).sum) := by
        simp
        ring
  have hfirst :
      ‖directionalJet (jointSpatialDirections V) (Function.uncurry g) (t, x)‖ ≤
        C_g * n.factorial * R ^ n / (n + 1 : ℝ) ^ 2 := by
    rw [jointSpatialDirectionalJet_eq_slice V (Function.uncurry g) hg t x]
    have hG' : snorm (g t) L.length R ≤ ENNReal.ofReal C_g := by
      rw [hlenI]
      exact hG t
    have h := directionalJet_coordinateList_norm_le L (g t) (hgSlice t)
      hR hCg hG' x
    simpa [L, hcoords, hlenI] using h
  have hsourceNorm :
      ‖transportSourceJet V b g Y (t, x)‖ ≤
        ‖directionalJet (jointSpatialDirections V) (Function.uncurry g) (t, x)‖ +
          ‖∑ i : Fin 2, (alloc.map fun p =>
            directionalJet (p.1.map φ) (fun q => Function.uncurry b q i) (t, x) •
              directionalJet (p.2.map φ) (fun q => fderiv ℝ (Function.uncurry Y) q
                (0, coordinateVector 2 i)) (t, x)).sum‖ := by
    rw [hsourceAt]
    simpa only [Pi.sub_apply] using
      (norm_sub_le
        (directionalJet (jointSpatialDirections V) (Function.uncurry g) (t, x))
        (∑ i : Fin 2, (alloc.map fun p =>
          directionalJet (p.1.map φ) (fun q => Function.uncurry b q i) (t, x) •
            directionalJet (p.2.map φ) (fun q => fderiv ℝ (Function.uncurry Y) q
              (0, coordinateVector 2 i)) (t, x)).sum))
  have hbound :
      ‖transportSourceJet V b g Y (t, x)‖ ≤
        C_g * n.factorial * R ^ n / (n + 1 : ℝ) ^ 2 +
          2 * ((n : ℝ) * topCoefficient + (alloc.map lowWeight).sum) := by
    exact (hsourceNorm.trans (add_le_add hfirst hcomm))
  simpa [L, V, alloc, baseWeight, lowWeight, topCoefficient] using hbound

/-- The joint spatial jet indexed by a coordinate tuple is the paper's
ordered coordinate partial of the time slice. -/
theorem transportSpatialJet_coordinate_eq_orderedPartial
    {n : ℕ} (I : Fin n → Fin 2) (Y : ℝ → Vec 2 → Vec 2)
    (hY : ContDiff ℝ ∞ (Function.uncurry Y)) (t : ℝ) (x : Vec 2) :
    transportSpatialJet (List.ofFn fun j => coordinateVector 2 (I j))
        (Function.uncurry Y) (t, x) = orderedPartial n (Y t) x I := by
  have hslice := transportSpatialJet_eq_directionalJet_slice
    (List.ofFn fun j => coordinateVector 2 (I j)) Y hY t
  have hsliceSmooth : ContDiff ℝ ∞ (Y t) := by
    have hpair : ContDiff ℝ ∞ (fun x : Vec 2 => (t, x)) := by fun_prop
    simpa [Function.uncurry, Function.comp_def] using hY.comp hpair
  have hpartial := orderedPartial_eq_directionalJet (Y t) hsliceSmooth x I
  have h := congrFun hslice x
  calc
    _ = directionalJet (List.ofFn fun j => coordinateVector 2 (I j)) (Y t) x := h
    _ = orderedPartial n (Y t) x I := hpartial.symm

theorem transportSpatialJet_initial_zero_of_nonempty
    (I : List (Vec 2)) (hI : I ≠ [])
    {b g Y : ℝ → Vec 2 → Vec 2}
    (hY : IsClassicalTransportSolution b g Y)
    (x : Vec 2) :
    transportSpatialJet I (Function.uncurry Y) (0, x) = 0 := by
  induction I generalizing x with
  | nil => exact (hI rfl).elim
  | cons v I ih =>
      change fderiv ℝ (transportSpatialJet I (Function.uncurry Y))
        (0, x) (0, v) = 0
      have hzero : (fun y : Vec 2 =>
          transportSpatialJet I (Function.uncurry Y) (0, y)) = fun _ => 0 := by
        cases I with
        | nil =>
            funext y
            exact hY.initial y
        | cons w J =>
            funext y
            exact ih (by simp) y
      have hslice := jointSpatialDirectionalDerivative_eq_slice_general
        (transportSpatialJet I (Function.uncurry Y))
        (transportSpatialJet_contDiff I (Function.uncurry Y) hY.smooth)
        0 x v
      rw [hzero] at hslice
      simpa using hslice

/-- Every nonempty spatial jet of a zero-initial-data transport solution is
the integral of its recursively differentiated source along a characteristic. -/
theorem transportSolution_spatialJet_intervalIntegral
    (I : List (Vec 2)) (hI : I ≠ [])
    {b g Y : ℝ → Vec 2 → Vec 2}
    (hY : IsClassicalTransportSolution b g Y)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hg : ContDiff ℝ ∞ (Function.uncurry g))
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (x : Vec 2) (t : ℝ) :
    transportSpatialJet I (Function.uncurry Y) (t, X t x 0) =
      ∫ r in 0..t, transportSourceJet I b g Y (r, X r x 0) := by
  let hbase : IsSmoothClassicalTransportSolution b g Y := ⟨hY, hg⟩
  let hjet := transportSolution_iteratedDirectionalDerivative_isSmoothSolution I hbase hb
  have hformula := transportSolution_intervalIntegral_alongFlow
    hjet.toIsClassicalTransportSolution hjet.source_smooth hX x 0 t
  have hzero := transportSpatialJet_initial_zero_of_nonempty I hI hY x
  simpa [Function.curry, hzero, hX.1] using hformula

end AVenhance.FaaDiBruno

end
