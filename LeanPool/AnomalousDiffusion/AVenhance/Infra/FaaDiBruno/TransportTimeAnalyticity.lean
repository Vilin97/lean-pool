/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FaaDiBruno.TransportSharpEstimate
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FaaDiBruno.TransportExpansion
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FaaDiBruno.DirectionalProduct

/-! # Transport Time Analyticity

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

open Homogenization MeasureTheory
open scoped ContDiff NNReal Topology

noncomputable section

namespace AVenhance.FaaDiBruno

theorem directionalSplits_append {E : Type*} (I J : List E) :
    directionalSplits (I ++ J) =
      (directionalSplits I).flatMap fun p =>
        (directionalSplits J).map fun q => (p.1 ++ q.1, p.2 ++ q.2) := by
  induction I with
  | nil => simp [directionalSplits]
  | cons v I ih =>
      simp only [List.cons_append, directionalSplits, List.flatMap_append,
        List.flatMap_map, ih]
      rw [List.map_flatMap, List.map_flatMap]
      simp [Function.comp_def]

theorem directionalSplits_weight_sum_right {E : Type*} (I : List E)
    (w : ℕ → ℝ) :
    ((directionalSplits I).map fun p => w p.2.length).sum =
      ∑ i ∈ Finset.range (I.length + 1),
        (I.length.choose i : ℝ) * w i := by
  induction I generalizing w with
  | nil => simp [directionalSplits]
  | cons v I ih =>
      simp only [directionalSplits, List.map_append, List.sum_append,
        List.map_map, Function.comp_def, List.length_cons]
      rw [ih w, ih (fun i => w (i + 1))]
      let n := I.length
      have hsum :
          ∑ i ∈ Finset.range (n + 2), ((n + 1).choose i : ℝ) * w i =
            (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * w (i + 1)) +
              ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * w i := by
        rw [Finset.sum_range_succ']
        simp only [Nat.choose_succ_succ, Nat.cast_add]
        simp_rw [add_mul]
        rw [Finset.sum_add_distrib]
        have htail :
            ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * w i =
              (∑ i ∈ Finset.range n, (n.choose (i + 1) : ℝ) * w (i + 1)) + w 0 := by
          rw [Finset.sum_range_succ']
          simp [Nat.choose_zero_right]
        have hlast :
            ∑ i ∈ Finset.range (n + 1), (n.choose (i + 1) : ℝ) * w (i + 1) =
              ∑ i ∈ Finset.range n, (n.choose (i + 1) : ℝ) * w (i + 1) := by
          rw [Finset.sum_range_succ]
          simp
        rw [htail, hlast]
        simp only [Nat.choose_zero_right, Nat.cast_one, one_mul]
        abel
      have hnrange : n + 2 = (I.length + 1) + 1 := by dsimp [n]
      rw [← hnrange]
      simpa [n, add_comm] using hsum.symm

theorem directionalSplits_double_weight_sum_right {E : Type*} (I J : List E)
    (w : ℕ → ℕ → ℝ) :
    ((directionalSplits I).map fun p =>
      ((directionalSplits J).map fun q => w p.2.length q.2.length).sum).sum =
      ∑ i ∈ Finset.range (I.length + 1),
        ∑ j ∈ Finset.range (J.length + 1),
          (I.length.choose i : ℝ) * (J.length.choose j : ℝ) * w i j := by
  have hinner (p : List E × List E) :
      ((directionalSplits J).map fun q => w p.2.length q.2.length).sum =
        ∑ j ∈ Finset.range (J.length + 1),
          (J.length.choose j : ℝ) * w p.2.length j := by
    simpa using directionalSplits_weight_sum_right J (w p.2.length)
  simp_rw [hinner]
  rw [directionalSplits_weight_sum_right I
    (fun i => ∑ j ∈ Finset.range (J.length + 1),
      (J.length.choose j : ℝ) * w i j)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem directionalSplits_replicate_parts {E : Type*} (a : E) {m : ℕ}
    (p : List E × List E)
    (hp : p ∈ directionalSplits (List.replicate m a)) :
    p.1 = List.replicate p.1.length a ∧
      p.2 = List.replicate p.2.length a := by
  induction m generalizing p with
  | zero =>
      simp only [List.replicate_zero, directionalSplits, List.mem_singleton] at hp
      subst p
      simp
  | succ m ih =>
      simp only [List.replicate_succ, directionalSplits,
        List.mem_append, List.mem_map] at hp
      rcases hp with hp | hp
      · rcases hp with ⟨q, hq, heq⟩
        subst p
        rcases ih q hq with ⟨hleft, hright⟩
        constructor
        · rw [List.length_cons, hleft]
          simp [List.replicate_succ]
        · exact hright
      · rcases hp with ⟨q, hq, heq⟩
        subst p
        rcases ih q hq with ⟨hleft, hright⟩
        constructor
        · exact hleft
        · rw [List.length_cons, hright]
          simp [List.replicate_succ]

theorem TransportTimeAnalyticity.list_sum_flatMap {α β : Type*} [AddCommMonoid β]
    (L : List α) (f : α → List β) :
    (L.flatMap f).sum = (L.map fun a => (f a).sum).sum := by
  induction L with
  | nil => rfl
  | cons a L ih => simp [ih]

theorem directionalSplits_append_sum {E : Type*} {β : Type*}
    [AddCommMonoid β] (I J : List E) (f : List E × List E → β) :
    ((directionalSplits (I ++ J)).map f).sum =
    ((directionalSplits I).map fun p =>
        ((directionalSplits J).map fun q =>
          f (p.1 ++ q.1, p.2 ++ q.2)).sum).sum := by
  rw [directionalSplits_append, List.map_flatMap, TransportTimeAnalyticity.list_sum_flatMap]
  simp only [List.map_map, Function.comp_def]

theorem TransportTimeAnalyticity.nat_descFactorial_le_of_length_le {n k l : ℕ}
    (hkl : k ≤ l) (hl : l ≤ n) :
    n.descFactorial k ≤ n.descFactorial l := by
  induction l generalizing k with
  | zero => simp_all
  | succ l ih =>
      by_cases hkl' : k ≤ l
      · have hprev := ih hkl' (by omega)
        calc
          n.descFactorial k ≤ n.descFactorial l := hprev
          _ ≤ n.descFactorial (l + 1) := by
            rw [Nat.descFactorial_succ]
            exact Nat.le_mul_of_pos_left _ (by omega)
      · have hkeq : k = l + 1 := by omega
        subst k
        exact le_rfl

/-- The factorial quotient in the two-parameter time/spatial induction is
monotone in both derivative counts. -/
theorem transportTime_factorialRatio_le {m n j k : ℕ}
    (hj : j ≤ m) (hk : k ≤ n) :
    ((k + j + 1).factorial : ℝ) / k.factorial ≤
      ((n + m + 1).factorial : ℝ) / n.factorial := by
  let a := k + j + 1
  let b := n + m + 1
  have hleftLen : j + 1 ≤ a := by dsimp [a]; omega
  have hrightLen : m + 1 ≤ b := by dsimp [b]; omega
  have htop : a ≤ b := by dsimp [a, b]; omega
  have hdf1 : a.descFactorial (j + 1) ≤ b.descFactorial (j + 1) :=
    Nat.descFactorial_le (j + 1) htop
  have hdf2 : b.descFactorial (j + 1) ≤ b.descFactorial (m + 1) :=
    TransportTimeAnalyticity.nat_descFactorial_le_of_length_le (by omega) (by omega)
  have hfactor1 : k.factorial * a.descFactorial (j + 1) = a.factorial := by
    have h := Nat.factorial_mul_descFactorial (by omega : j + 1 ≤ a)
    have hsub : a - (j + 1) = k := by dsimp [a]; omega
    simpa [hsub, a] using h
  have hfactor2 : n.factorial * b.descFactorial (m + 1) = b.factorial := by
    have h := Nat.factorial_mul_descFactorial (by omega : m + 1 ≤ b)
    have hsub : b - (m + 1) = n := by dsimp [b]; omega
    simpa [hsub, b] using h
  have hcross : a.factorial * n.factorial ≤ b.factorial * k.factorial := by
    calc
      a.factorial * n.factorial =
          (k.factorial * n.factorial) * a.descFactorial (j + 1) := by
            calc
              _ = (k.factorial * a.descFactorial (j + 1)) * n.factorial :=
                congrArg (fun q => q * n.factorial) hfactor1.symm
              _ = _ := by ac_rfl
      _ ≤ (k.factorial * n.factorial) * b.descFactorial (m + 1) :=
        Nat.mul_le_mul_left _ (hdf1.trans hdf2)
      _ = b.factorial * k.factorial := by rw [← hfactor2]; ring
  have hcrossReal :
      (a.factorial : ℝ) * n.factorial ≤
        (b.factorial : ℝ) * k.factorial := by exact_mod_cast hcross
  have hdenK : 0 < (k.factorial : ℝ) := by positivity
  have hdenN : 0 < (n.factorial : ℝ) := by positivity
  have hratio := (div_le_div_iff₀ hdenK hdenN).2 hcrossReal
  simpa [a, b, Nat.cast_mul] using hratio

/-- Repeated time derivatives of a joint field. -/
def iteratedJointTimeDerivative : ℕ → (ℝ × Vec 2 → Vec 2) → ℝ × Vec 2 → Vec 2
  | 0, F => F
  | n + 1, F => jointTimeDerivative (iteratedJointTimeDerivative n F)

/-- The `m`-th time derivative of a joint field, as a time-dependent spatial
field. -/
def transportTimeDerivative (m : ℕ) (F : ℝ × Vec 2 → Vec 2) :
    ℝ → Vec 2 → Vec 2 := Function.curry (iteratedJointTimeDerivative m F)

theorem iteratedJointTimeDerivative_smooth (m : ℕ)
    (F : ℝ × Vec 2 → Vec 2) (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (iteratedJointTimeDerivative m F) := by
  induction m with
  | zero => simpa [iteratedJointTimeDerivative] using hF
  | succ m ih =>
      rw [iteratedJointTimeDerivative]
      exact jointTimeDerivative_contDiff _ ih

theorem transportTimeDerivative_joint_smooth (m : ℕ)
    (F : ℝ × Vec 2 → Vec 2) (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (Function.uncurry (transportTimeDerivative m F)) := by
  change ContDiff ℝ ∞ (iteratedJointTimeDerivative m F)
  exact iteratedJointTimeDerivative_smooth m F hF

theorem directionalJet_spatial_commute_iteratedTime (I : List (Vec 2))
    (m : ℕ) (F : ℝ × Vec 2 → Vec 2) (hF : ContDiff ℝ ∞ F) :
    directionalJet (jointSpatialDirections I) (iteratedJointTimeDerivative m F) =
      iteratedJointTimeDerivative m (directionalJet (jointSpatialDirections I) F) := by
  induction m with
  | zero => rfl
  | succ m ih =>
      change directionalJet (jointSpatialDirections I)
          (jointTimeDerivative (iteratedJointTimeDerivative m F)) =
        jointTimeDerivative
          (iteratedJointTimeDerivative m (directionalJet (jointSpatialDirections I) F))
      rw [directionalJet_jointTime_commute I (iteratedJointTimeDerivative m F)
        (iteratedJointTimeDerivative_smooth m F hF), ih]

/-- A mixed coordinate partial of a time derivative is the joint directional
jet with the spatial directions followed by the time directions. -/
theorem orderedPartial_timeDerivative_eq_jointJet {m n : ℕ}
    (F : ℝ × Vec 2 → Vec 2) (hF : ContDiff ℝ ∞ F)
    (t : ℝ) (x : Vec 2) (I : Fin n → Fin 2) :
    orderedPartial n (transportTimeDerivative m F t) x I =
      iteratedJointTimeDerivative m
        (directionalJet (jointSpatialDirections
          (List.ofFn (fun j => coordinateVector 2 (I j)))) F) (t, x) := by
  let J : List (Vec 2) := List.ofFn (fun j => coordinateVector 2 (I j))
  have hH := iteratedJointTimeDerivative_smooth m F hF
  have hslice : ContDiff ℝ ∞ (fun y : Vec 2 =>
      iteratedJointTimeDerivative m F (t, y)) := by
    have hpair : ContDiff ℝ ∞ (fun y : Vec 2 => (t, y)) := by fun_prop
    exact hH.comp hpair
  have hpartial := orderedPartial_eq_directionalJet
    (fun y : Vec 2 => iteratedJointTimeDerivative m F (t, y)) hslice x I
  change orderedPartial n
    (fun y : Vec 2 => iteratedJointTimeDerivative m F (t, y)) x I = _
  rw [hpartial]
  have hspatial := jointSpatialDirectionalJet_eq_slice J
    (iteratedJointTimeDerivative m F) hH t x
  rw [← hspatial]
  rw [directionalJet_spatial_commute_iteratedTime J m F hF]

/-- Repeated pure time directions for an iterated joint derivative. -/
def transportTimeDirections (m : ℕ) : List (ℝ × Vec 2) :=
  List.replicate m ((1 : ℝ), (0 : Vec 2))

/-- Embed one spatial coordinate direction into joint time-space. -/
def jointCoordinateDirection (i : Fin 2) : ℝ × Vec 2 :=
  ((0 : ℝ), coordinateVector 2 i)

/-- Joint spatial directions associated with a list of coordinate indices. -/
def transportCoordinateDirections (I : List (Fin 2)) : List (ℝ × Vec 2) :=
  jointSpatialDirections (I.map (coordinateVector 2))

theorem transportCoordinateDirections_eq_map (I : List (Fin 2)) :
    transportCoordinateDirections I = I.map jointCoordinateDirection := by
  simp [transportCoordinateDirections, jointSpatialDirections, jointCoordinateDirection,
    List.map_map, Function.comp_def]

theorem directionalSplits_coordinate_preimage {I : List (Fin 2)}
    {p : List (ℝ × Vec 2) × List (ℝ × Vec 2)}
    (hp : p ∈ directionalSplits (transportCoordinateDirections I)) :
    ∃ q ∈ directionalSplits I,
      p = (q.1.map jointCoordinateDirection, q.2.map jointCoordinateDirection) := by
  rw [transportCoordinateDirections_eq_map, directionalSplits_map] at hp
  rcases List.mem_map.mp hp with ⟨q, hq, hpq⟩
  exact ⟨q, hq, hpq.symm⟩

theorem directionalJet_component_norm_le
    (J : List (ℝ × Vec 2)) (B : ℝ × Vec 2 → Vec 2)
    (hB : ContDiff ℝ ∞ B) (i : Fin 2) (p : ℝ × Vec 2) :
    ‖directionalJet J (fun q => B q i) p‖ ≤
      ‖directionalJet J B p‖ := by
  have hcomp := congrFun
    (directionalJet_comp_clm J (ContinuousLinearMap.proj i) B hB) p
  calc
    ‖directionalJet J (fun q => B q i) p‖ =
        ‖directionalJet J B p i‖ := by simpa using congrArg norm hcomp
    _ ≤ ‖directionalJet J B p‖ := by
      simpa using (norm_le_pi_norm (directionalJet J B p) i)

theorem directionalJet_transportAdvection_full_splitSum
    (J : List (ℝ × Vec 2)) (B F : ℝ × Vec 2 → Vec 2)
    (hB : ContDiff ℝ ∞ B) (hF : ContDiff ℝ ∞ F) :
    directionalJet J (transportAdvection B F) = fun p =>
      ∑ i : Fin 2,
        ((directionalSplits J).map fun split =>
          directionalJet split.1 (fun q => B q i) p •
            directionalJet split.2
              (fun q => fderiv ℝ F q (0, coordinateVector 2 i)) p).sum := by
  have hFderiv : ContDiff ℝ ∞ (fun p => fderiv ℝ F p) :=
    hF.fderiv_right (by simp)
  have hcoeff (i : Fin 2) : ContDiff ℝ ∞ (fun p : ℝ × Vec 2 => B p i) := by
    have hproj : ContDiff ℝ ∞
        (fun _ : ℝ × Vec 2 => (ContinuousLinearMap.proj i : Vec 2 →L[ℝ] ℝ)) :=
      contDiff_const
    have h := hproj.clm_apply hB
    simpa using h
  have hgrad (i : Fin 2) : ContDiff ℝ ∞
      (fun p : ℝ × Vec 2 => fderiv ℝ F p (0, coordinateVector 2 i)) :=
    hFderiv.clm_apply (contDiff_const : ContDiff ℝ ∞
      (fun _ : ℝ × Vec 2 => ((0 : ℝ), coordinateVector 2 i)))
  have hterm (i : Fin 2) : ContDiff ℝ ∞ (fun p : ℝ × Vec 2 =>
      B p i • fderiv ℝ F p (0, coordinateVector 2 i)) :=
    (hcoeff i).smul (hgrad i)
  have hsum := directionalJet_finset_sum J Finset.univ
    (fun i p => B p i • fderiv ℝ F p (0, coordinateVector 2 i))
    (by intro i hi; exact hterm i)
  change directionalJet J (fun p => ∑ i : Fin 2,
    B p i • fderiv ℝ F p (0, coordinateVector 2 i)) = _
  rw [hsum]
  funext p
  apply Finset.sum_congr rfl
  intro i hi
  exact congrFun (directionalJet_smul J (fun q => B q i)
    (fun q => fderiv ℝ F q (0, coordinateVector 2 i)) (hcoeff i) (hgrad i)) p

theorem transportTimeMixedEquation
    (m : ℕ) (I : List (Fin 2))
    {b g Y : ℝ → Vec 2 → Vec 2}
    (hY : IsClassicalTransportSolution b g Y)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hg : ContDiff ℝ ∞ (Function.uncurry g)) :
    directionalJet
        (transportTimeDirections m ++ transportCoordinateDirections I)
        (jointTimeDerivative (Function.uncurry Y)) =
      directionalJet
          (transportTimeDirections m ++ transportCoordinateDirections I)
          (Function.uncurry g) - fun p =>
        ∑ i : Fin 2,
          ((directionalSplits
              (transportTimeDirections m ++ transportCoordinateDirections I)).map
            fun split =>
              directionalJet split.1 (fun q => Function.uncurry b q i) p •
                directionalJet split.2 (fun q =>
                  fderiv ℝ (Function.uncurry Y) q (0, coordinateVector 2 i)) p).sum := by
  let B := Function.uncurry b
  let G := Function.uncurry g
  let F := Function.uncurry Y
  let J := transportTimeDirections m ++ transportCoordinateDirections I
  have hEq : jointTimeDerivative F = G - transportAdvection B F := by
    funext p
    have htransport := jointTransportDerivative_eq_time_add_advection B F p
    have hsolution : jointTransportDerivative B F p = G p := by
      change (fderiv ℝ (Function.uncurry Y) p)
          (1, Function.uncurry b p) = Function.uncurry g p
      simpa only [Function.uncurry] using hY.equation p.1 p.2
    rw [htransport] at hsolution
    exact (eq_sub_iff_add_eq).2 hsolution
  have hEqJet := congrArg (directionalJet J) hEq
  have hadvSmooth := transportAdvection_contDiff B F hb hY.smooth
  calc
    directionalJet J (jointTimeDerivative F) =
        directionalJet J (G - transportAdvection B F) := hEqJet
    _ = directionalJet J G - directionalJet J (transportAdvection B F) :=
      directionalJet_sub J G (transportAdvection B F) hg hadvSmooth
    _ = _ := by
      rw [directionalJet_transportAdvection_full_splitSum J B F hb hY.smooth]

theorem directionalJet_timeDirections (m : ℕ) (F : ℝ × Vec 2 → Vec 2) :
    directionalJet (transportTimeDirections m) F =
      iteratedJointTimeDerivative m F := by
  induction m with
  | zero => rfl
  | succ m ih =>
      change jointTimeDerivative
          (directionalJet (transportTimeDirections m) F) =
        jointTimeDerivative (iteratedJointTimeDerivative m F)
      rw [ih]

theorem directionalJet_mixedCoordinates_eq_iteratedTime_spatial
    (m : ℕ) (I : List (Fin 2)) (F : ℝ × Vec 2 → Vec 2) :
    directionalJet
        (transportTimeDirections m ++ transportCoordinateDirections I) F =
      iteratedJointTimeDerivative m
        (directionalJet (transportCoordinateDirections I) F) := by
  rw [directionalJet_append, directionalJet_timeDirections]

theorem directionalJet_mixedCoordinates_eq_spatial_iteratedTime
    (m : ℕ) (I : List (Fin 2)) (F : ℝ × Vec 2 → Vec 2)
    (hF : ContDiff ℝ ∞ F) :
    directionalJet
        (transportTimeDirections m ++ transportCoordinateDirections I) F =
      directionalJet (transportCoordinateDirections I)
        (iteratedJointTimeDerivative m F) := by
  rw [directionalJet_mixedCoordinates_eq_iteratedTime_spatial]
  simpa [transportCoordinateDirections] using
      (directionalJet_spatial_commute_iteratedTime
      (I.map (coordinateVector 2)) m F hF).symm

/-- A spatial derivative of a mixed time-space jet is represented by the
coordinate list with that derivative appended. -/
theorem directionalJet_mixedSpatialDerivative_eq_append
    (m : ℕ) (L : List (Fin 2)) (i : Fin 2)
    (F : ℝ × Vec 2 → Vec 2) (hF : ContDiff ℝ ∞ F)
    (p : ℝ × Vec 2) :
    directionalJet (transportTimeDirections m ++
      transportCoordinateDirections L)
      (fun q => fderiv ℝ F q (0, coordinateVector 2 i)) p =
    directionalJet (transportTimeDirections m ++
      transportCoordinateDirections (L ++ [i])) F p := by
  let v : ℝ × Vec 2 := (0, coordinateVector 2 i)
  let H := iteratedJointTimeDerivative m F
  have hH : ContDiff ℝ ∞ H := iteratedJointTimeDerivative_smooth m F hF
  have hG : ContDiff ℝ ∞ (fun q => fderiv ℝ F q v) := by
    exact (hF.fderiv_right (by simp)).clm_apply contDiff_const
  have hcommTime : iteratedJointTimeDerivative m
      (fun q => fderiv ℝ F q v) = fun q => fderiv ℝ H q v := by
    funext q
    have hcomm := congrFun
      (directionalJet_spatial_commute_iteratedTime [coordinateVector 2 i] m F hF) q
    simpa [H, directionalJet, jointSpatialDirections, v] using hcomm.symm
  calc
    _ = directionalJet (transportCoordinateDirections L)
        (iteratedJointTimeDerivative m
          (fun q => fderiv ℝ F q v)) p := by
            exact congrFun
              (directionalJet_mixedCoordinates_eq_spatial_iteratedTime
                m L (fun q => fderiv ℝ F q v) hG) p
    _ = directionalJet (transportCoordinateDirections L)
        (fun q => fderiv ℝ H q v) p := by rw [hcommTime]
    _ = directionalJet [v]
        (directionalJet (transportCoordinateDirections L) H) p := by
            have hcomm := directionalJet_commute_single
              (transportCoordinateDirections L) v H hH
            simpa [directionalJet] using congrFun hcomm p
    _ = directionalJet
        (transportCoordinateDirections L ++ [v]) H p := by
            have hcomm := directionalJet_commute_single
              (transportCoordinateDirections L) v H hH
            calc
              _ = directionalJet
                  (transportCoordinateDirections L)
                    (directionalJet [v] H) p := (congrFun hcomm p).symm
              _ = _ := (congrFun (directionalJet_append
                (transportCoordinateDirections L) [v] H) p).symm
    _ = directionalJet (transportTimeDirections m ++
        transportCoordinateDirections (L ++ [i])) F p := by
          rw [directionalJet_mixedCoordinates_eq_spatial_iteratedTime
            m (L ++ [i]) F hF]
          simp [H, transportCoordinateDirections, jointSpatialDirections,
            v, List.map_append]

/-- The ordered joint jet of a time derivative and any finite list of
coordinate spatial directions is the corresponding paper partial. -/
theorem orderedPartial_timeDerivative_eq_coordinateListJet
    (m : ℕ) {n : ℕ} (I : Fin n → Fin 2)
    (F : ℝ × Vec 2 → Vec 2) (hF : ContDiff ℝ ∞ F)
    (t : ℝ) (x : Vec 2) :
    orderedPartial n (transportTimeDerivative m F t) x I =
      directionalJet
        (transportTimeDirections m ++
          transportCoordinateDirections (List.ofFn I)) F (t, x) := by
  rw [directionalJet_mixedCoordinates_eq_iteratedTime_spatial]
  rw [orderedPartial_timeDerivative_eq_jointJet F hF t x I]
  have hlist : List.ofFn (fun j : Fin n => coordinateVector 2 (I j)) =
      (List.ofFn I).map (coordinateVector 2) := by
    rw [List.map_ofFn]
    rfl
  change iteratedJointTimeDerivative m
      (directionalJet (jointSpatialDirections
        (List.ofFn fun j : Fin n => coordinateVector 2 (I j))) F) (t, x) =
    iteratedJointTimeDerivative m
      (directionalJet (jointSpatialDirections
        ((List.ofFn I).map (coordinateVector 2))) F) (t, x)
  rw [← hlist]

/-- A mixed jet indexed by an arbitrary finite coordinate list obeys the
pointwise derivative bound read directly from the spatial seminorm. -/
theorem coordinateList_timeJet_norm_le_of_snorm
    {m n : ℕ} (F : ℝ × Vec 2 → Vec 2) (hF : ContDiff ℝ ∞ F)
    (t : ℝ) (L : List (Fin 2)) (hL : L.length = n)
    {C R : ℝ} (hR : 0 < R) (hC : 0 ≤ C)
    (hs : snorm (transportTimeDerivative m F t) n R ≤ ENNReal.ofReal C)
    (x : Vec 2) :
    ‖directionalJet
        (transportTimeDirections m ++ transportCoordinateDirections L) F
        (t, x)‖ ≤ C * n.factorial * R ^ n / (n + 1 : ℝ) ^ 2 := by
  subst n
  let I : Fin L.length → Fin 2 := fun j => L.get j
  have hlist : List.ofFn I = L := by simp [I]
  have hpartial := orderedPartial_norm_le_of_snorm_le
    (d := 2) (m := L.length) (n := L.length)
    (transportTimeDerivative m F t)
    (by
      have hjoint := transportTimeDerivative_joint_smooth m F hF
      have hpair : ContDiff ℝ ∞ (fun y : Vec 2 => (t, y)) := by fun_prop
      exact (hjoint.comp hpair).of_le (by simp))
    (by rfl) hR hC hs x I
  have hjet := orderedPartial_timeDerivative_eq_coordinateListJet m I F hF t x
  rw [hlist] at hjet
  simpa [hjet] using hpartial

/-- The paper's derivative seminorm decreases when its radius increases. -/
theorem snorm_le_of_radius_le
    {d n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Vec d → F) {R S C : ℝ} (hR : 0 < R) (hS : 0 < S)
    (hRS : R ≤ S) (hC : 0 ≤ C)
    (hs : snorm f n R ≤ ENNReal.ofReal C) :
    snorm f n S ≤ ENNReal.ofReal C := by
  have hD := derivativeSup_le_of_snorm_le f hR hs
  have hpow : R ^ n ≤ S ^ n := pow_le_pow_left₀ hR.le hRS n
  have hbound : C * n.factorial * R ^ n / (n + 1 : ℝ) ^ 2 ≤
      C * n.factorial * S ^ n / (n + 1 : ℝ) ^ 2 := by
    have hcoef : 0 ≤ C * n.factorial / (n + 1 : ℝ) ^ 2 := by positivity
    have h := mul_le_mul_of_nonneg_left hpow hcoef
    convert h using 1 <;> ring
  have hD' : derivativeSup n f ≤ ENNReal.ofReal
      (C * S ^ n * n.factorial / (n + 1 : ℝ) ^ 2) := by
    apply le_trans hD
    apply ENNReal.ofReal_le_ofReal
    calc
      C * n.factorial * R ^ n / (n + 1 : ℝ) ^ 2 ≤
          C * n.factorial * S ^ n / (n + 1 : ℝ) ^ 2 := hbound
      _ = C * S ^ n * n.factorial / (n + 1 : ℝ) ^ 2 := by ring
  exact snorm_le_of_derivativeSup_le f hS hD'

/-- One labeled mixed Leibniz summand is bounded by the exact two-factor
coordinate-seminorm product used in the 10698 resummation. -/
theorem transportTimeLowerProduct_pointwise_bound
    {m n : ℕ} (L : List (Fin 2)) (hL : L.length = n)
    {b g Y : ℝ → Vec 2 → Vec 2}
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hY : IsClassicalTransportSolution b g Y)
    {C_f Q_f R A Q ρ : ℝ}
    (hR : 0 < R) (hρ : 0 < ρ) (hCf : 0 ≤ C_f)
    (hQf : 0 ≤ Q_f) (hQ : 0 ≤ Q) (hA : 0 ≤ A)
    {p : List (ℝ × Vec 2) × List (ℝ × Vec 2)}
    (hp : p ∈ directionalSplits (transportTimeDirections m))
    {q : List (ℝ × Vec 2) × List (ℝ × Vec 2)}
    (hq : q ∈ directionalSplits (transportCoordinateDirections L))
    (i : Fin 2) (t : ℝ) (x : Vec 2)
    (hB : snorm
        (transportTimeDerivative (p.1.length) (Function.uncurry b) t)
        q.1.length R ≤ ENNReal.ofReal
          (C_f * Q_f ^ p.1.length * p.1.length.factorial))
    (hYbound : snorm
        (transportTimeDerivative (p.2.length) (Function.uncurry Y) t)
        (q.2.length + 1) ρ ≤ ENNReal.ofReal
          (A * (((q.2.length + p.2.length + 1).factorial : ℝ) *
            p.2.length.factorial / (q.2.length + 1).factorial) * Q ^ p.2.length))
    :
    ‖directionalJet (p.1 ++ q.1) (fun z => Function.uncurry b z i) (t, x) •
      directionalJet (p.2 ++ q.2)
        (fun z => fderiv ℝ (Function.uncurry Y) z
          (0, coordinateVector 2 i)) (t, x)‖ ≤
      (C_f * Q_f ^ p.1.length * p.1.length.factorial) *
        (q.1.length.factorial * R ^ q.1.length /
          (q.1.length + 1 : ℝ) ^ 2) *
        (A * (((q.2.length + p.2.length + 1).factorial : ℝ) *
          p.2.length.factorial / (q.2.length + 1).factorial) * Q ^ p.2.length) *
        ((q.2.length + 1).factorial * ρ ^ (q.2.length + 1) /
          (q.2.length + 2 : ℝ) ^ 2) := by
  let u := p.1.length
  let j := p.2.length
  let v := q.1.length
  let k := q.2.length
  have hpParts := directionalSplits_replicate_parts
    ((1 : ℝ), (0 : Vec 2)) p hp
  have hqParts := directionalSplits_coordinate_preimage hq
  rcases hqParts with ⟨r, hr, hrq⟩
  have huj : u + j = m := by
    have hlen := directionalSplits_length_sum
      (transportTimeDirections m) p hp
    simpa [u, j, transportTimeDirections] using hlen
  have hvk : v + k = n := by
    have hlen := directionalSplits_length_sum
      (transportCoordinateDirections L) q hq
    have hlen' : q.1.length + q.2.length = L.length := by
      simpa [transportCoordinateDirections, jointSpatialDirections] using hlen
    omega
  have hpLeft : p.1 = transportTimeDirections u := by
    simpa [u, transportTimeDirections] using hpParts.1
  have hpRight : p.2 = transportTimeDirections j := by
    simpa [j, transportTimeDirections] using hpParts.2
  have hqLeft : q.1 = transportCoordinateDirections r.1 := by
    rw [hrq, transportCoordinateDirections_eq_map]
  have hqRight : q.2 = transportCoordinateDirections r.2 := by
    rw [hrq, transportCoordinateDirections_eq_map]
  have hrv : r.1.length = v := by
    dsimp [v]
    rw [hrq]
    simp
  have hrk : r.2.length = k := by
    dsimp [k]
    rw [hrq]
    simp
  have hB' : snorm (transportTimeDerivative u (Function.uncurry b) t)
      v R ≤ ENNReal.ofReal (C_f * Q_f ^ u * u.factorial) := by
    simpa [u, v] using hB
  have hFirst := coordinateList_timeJet_norm_le_of_snorm
    (Function.uncurry b) hb t r.1 (by simpa [v] using hrv) hR
    (by positivity) hB' x
  have hComp := directionalJet_component_norm_le
    (p.1 ++ q.1) (Function.uncurry b) hb i (t, x)
  have hComp' :
      ‖directionalJet (p.1 ++ q.1)
        (fun z => Function.uncurry b z i) (t, x)‖ ≤
      ‖directionalJet (p.1 ++ q.1) (Function.uncurry b) (t, x)‖ := by
    simpa [hpLeft, hqLeft] using hComp
  have hFirst' :
      ‖directionalJet (p.1 ++ q.1)
        (fun z => Function.uncurry b z i) (t, x)‖ ≤
        C_f * Q_f ^ u * u.factorial *
          (v.factorial * R ^ v / (v + 1 : ℝ) ^ 2) := by
    calc
      _ ≤ ‖directionalJet (transportTimeDirections u ++
          transportCoordinateDirections r.1) (Function.uncurry b) (t, x)‖ := by
            simpa [hpLeft, hqLeft] using hComp'
      _ ≤ C_f * Q_f ^ u * u.factorial * v.factorial * R ^ v /
          (v + 1 : ℝ) ^ 2 := by simpa [u, v] using hFirst
      _ = _ := by ring
  have hSecondEq := directionalJet_mixedSpatialDerivative_eq_append
    j r.2 i (Function.uncurry Y) hY.smooth (t, x)
  have hSecondEq' :
      directionalJet (p.2 ++ q.2)
        (fun z => fderiv ℝ (Function.uncurry Y) z
          (0, coordinateVector 2 i)) (t, x) =
      directionalJet (transportTimeDirections j ++
        transportCoordinateDirections (r.2 ++ [i]))
        (Function.uncurry Y) (t, x) := by
    rw [hpRight, hqRight]
    simpa [j] using hSecondEq
  have hqRightLen : q.2.length = r.2.length := by
    rw [hqRight]
    simp [transportCoordinateDirections, jointSpatialDirections]
  have hSecond := coordinateList_timeJet_norm_le_of_snorm
    (Function.uncurry Y) hY.smooth t (r.2 ++ [i]) (by simp [hqRightLen]) hρ
    (by positivity) hYbound x
  have hSecond' :
      ‖directionalJet (p.2 ++ q.2)
        (fun z => fderiv ℝ (Function.uncurry Y) z
          (0, coordinateVector 2 i)) (t, x)‖ ≤
        (A * (((k + j + 1).factorial : ℝ) * j.factorial /
          (k + 1).factorial) * Q ^ j) *
          ((k + 1).factorial * ρ ^ (k + 1) / (k + 2 : ℝ) ^ 2) := by
    rw [hSecondEq']
    have hSecondBound :
        ‖directionalJet (transportTimeDirections j ++
          transportCoordinateDirections (r.2 ++ [i]))
          (Function.uncurry Y) (t, x)‖ ≤
        A * (((k + j + 1).factorial : ℝ) * j.factorial /
          (k + 1).factorial) * Q ^ j * (k + 1).factorial *
          ρ ^ (k + 1) / ((k + 1 : ℝ) + 1) ^ 2 := by
      simpa [j, k] using hSecond
    have hden : (k + 1 : ℝ) + 1 = k + 2 := by ring
    have hSecondBound' :
        ‖directionalJet (transportTimeDirections j ++
          transportCoordinateDirections (r.2 ++ [i]))
          (Function.uncurry Y) (t, x)‖ ≤
        A * (((k + j + 1).factorial : ℝ) * j.factorial /
          (k + 1).factorial) * Q ^ j * (k + 1).factorial *
          ρ ^ (k + 1) / (k + 2 : ℝ) ^ 2 := by
      have htmp := hSecondBound
      rw [hden] at htmp
      exact htmp
    calc
      _ ≤ _ := hSecondBound'
      _ = _ := by ring
  rw [norm_smul]
  calc
    _ ≤ (C_f * Q_f ^ u * u.factorial *
          (v.factorial * R ^ v / (v + 1 : ℝ) ^ 2)) *
        ((A * (((k + j + 1).factorial : ℝ) * j.factorial /
          (k + 1).factorial) * Q ^ j) *
          ((k + 1).factorial * ρ ^ (k + 1) / (k + 2 : ℝ) ^ 2)) :=
      mul_le_mul hFirst' hSecond' (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem TransportTimeAnalyticity.list_map_real_sum_mono {α : Type*} (L : List α)
    (f g : α → ℝ) (h : ∀ a ∈ L, f a ≤ g a) :
    (L.map f).sum ≤ (L.map g).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
      simp only [List.map_cons, List.sum_cons]
      apply add_le_add
      · exact h a (by simp)
      · apply ih
        intro b hb
        exact h b (by simp [hb])

theorem TransportTimeAnalyticity.list_map_norm_sum_le {α : Type*}
    (L : List α) (f : α → Vec 2) :
    ‖(L.map f).sum‖ ≤ (L.map fun a => ‖f a‖).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
      change ‖f a + (L.map f).sum‖ ≤ ‖f a‖ + (L.map fun a => ‖f a‖).sum
      calc
        ‖f a + (L.map f).sum‖ ≤ ‖f a‖ + ‖(L.map f).sum‖ := norm_add_le _ _
        _ ≤ ‖f a‖ + (L.map fun a => ‖f a‖).sum := add_le_add le_rfl ih

/-- Bound a sum of mixed transport Leibniz terms by its length-only majorant.
The two labeled split lists retain the binomial multiplicities exactly. -/
theorem directionalSplit_product_sum_bound {E : Type*}
    (I J : List E) (F : Fin 2 →
      (List E × List E) → (List E × List E) → Vec 2)
    (w : ℕ → ℕ → ℝ)
    (hF : ∀ i, ∀ p ∈ directionalSplits I, ∀ q ∈ directionalSplits J,
      ‖F i p q‖ ≤ w p.2.length q.2.length) :
    ‖∑ i : Fin 2,
      ((directionalSplits I).map fun p =>
        ((directionalSplits J).map fun q => F i p q).sum).sum‖ ≤
      2 * (∑ a ∈ Finset.range (I.length + 1),
        ∑ b ∈ Finset.range (J.length + 1),
          (I.length.choose a : ℝ) * (J.length.choose b : ℝ) * w a b) := by
  let P := directionalSplits I
  let S := directionalSplits J
  have hnorm (i : Fin 2) :
      ‖(P.map fun p => (S.map fun q => F i p q).sum).sum‖ ≤
        (P.map fun p => (S.map fun q => ‖F i p q‖).sum).sum := by
    calc
      _ ≤ (P.map fun p => ‖(S.map fun q => F i p q).sum‖).sum :=
        TransportTimeAnalyticity.list_map_norm_sum_le P _
      _ ≤ _ := TransportTimeAnalyticity.list_map_real_sum_mono P _ _ (by
        intro p hp
        exact TransportTimeAnalyticity.list_map_norm_sum_le S _)
  have hmajor (i : Fin 2) :
      (P.map fun p => (S.map fun q => ‖F i p q‖).sum).sum ≤
        (P.map fun p => (S.map fun q => w p.2.length q.2.length).sum).sum := by
    apply TransportTimeAnalyticity.list_map_real_sum_mono
    intro p hp
    apply TransportTimeAnalyticity.list_map_real_sum_mono
    intro q hq
    exact hF i p hp q hq
  have hdouble := directionalSplits_double_weight_sum_right I J w
  calc
    _ ≤ ∑ i : Fin 2,
        (P.map fun p => (S.map fun q => w p.2.length q.2.length).sum).sum := by
          calc
            _ ≤ ∑ i : Fin 2,
                ‖(P.map fun p => (S.map fun q => F i p q).sum).sum‖ := norm_sum_le _ _
            _ ≤ _ := Finset.sum_le_sum fun i hi => (hnorm i).trans (hmajor i)
    _ = 2 * (P.map fun p => (S.map fun q =>
          w p.2.length q.2.length).sum).sum := by
            simp [P, S, Finset.sum_const, nsmul_eq_mul]
    _ = _ := by simpa [P, S] using congrArg (fun z : ℝ => 2 * z) hdouble

/-- Scalar closure for one step of the 10698 time-derivative induction. The
`Q` budget leaves half of the target for the source and half for the exact
two-parameter convolution. -/
theorem transportTimeAnalytic_scalar_budget {m n : ℕ}
    {C_f C_g R ρ Q Q_g : ℝ}
    (hCf : 0 < C_f) (hCg : 0 ≤ C_g) (hR : 0 < R)
    (hRρ : R ≤ ρ) (hρ : ρ ≤ 2 * R)
    (hQg0 : 0 ≤ Q_g) (hQg : Q_g ≤ Q)
    (hQ₁ : C_f * R ≤ Q) (hQ₂ : 16 * (2 : ℝ) * C_f * R ≤ Q) :
    C_g * Q_g ^ m * m.factorial /
        ((m + 1).factorial * Q ^ (m + 1)) +
      2 * C_f * (2 * C_g / (C_f * R)) * ρ / Q *
        (∑ j ∈ Finset.range (m + 1),
          ∑ k ∈ Finset.range (n + 1),
            ((n + 1 : ℝ) ^ 2 /
              (((n - k + 1 : ℕ) : ℝ) ^ 2 * (k + 2 : ℝ) ^ 2 *
                (m + 1 : ℝ))) *
              (((k + j + 1).factorial : ℝ) / k.factorial)) ≤
      (2 * C_g / (C_f * R)) *
        (((n + m + 1).factorial : ℝ) / n.factorial) := by
  let A : ℝ := 2 * C_g / (C_f * R)
  let H : ℝ := ((n + m + 1).factorial : ℝ) / n.factorial
  let w (j k : ℕ) : ℝ := (n + 1 : ℝ) ^ 2 /
    (((n - k + 1 : ℕ) : ℝ) ^ 2 * (k + 2 : ℝ) ^ 2 *
      (m + 1 : ℝ))
  have hQ : 0 < Q := lt_of_lt_of_le (mul_pos hCf hR) hQ₁
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hH : 1 ≤ H := by
    dsimp [H]
    have hfac : n.factorial ≤ (n + m + 1).factorial := by
      exact Nat.factorial_le (by omega)
    have hfacR : (n.factorial : ℝ) ≤ ((n + m + 1).factorial : ℝ) := by
      exact_mod_cast hfac
    exact (le_div_iff₀ (by positivity : 0 < (n.factorial : ℝ))).2
      (by simpa using hfacR)
  have hconv :
      (∑ j ∈ Finset.range (m + 1),
        ∑ k ∈ Finset.range (n + 1), w j k *
          (((k + j + 1).factorial : ℝ) / k.factorial)) ≤ 4 * H := by
    have hterm (j k : ℕ)
        (hj : j ∈ Finset.range (m + 1))
        (hk : k ∈ Finset.range (n + 1)) :
        w j k * (((k + j + 1).factorial : ℝ) / k.factorial) ≤
          w j k * H := by
      have hj' : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have hratio := transportTime_factorialRatio_le hj' hk'
      have hw : 0 ≤ w j k := by dsimp [w]; positivity
      exact mul_le_mul_of_nonneg_left hratio hw
    calc
      _ ≤ ∑ j ∈ Finset.range (m + 1),
          ∑ k ∈ Finset.range (n + 1), w j k * H := by
            apply Finset.sum_le_sum
            intro j hj
            apply Finset.sum_le_sum
            intro k hk
            exact hterm j k hj hk
      _ = H * (∑ j ∈ Finset.range (m + 1),
          ∑ k ∈ Finset.range (n + 1), w j k) := by
            calc
              _ = ∑ j ∈ Finset.range (m + 1),
                  (∑ k ∈ Finset.range (n + 1), w j k) * H := by
                    apply Finset.sum_congr rfl
                    intro j hj
                    rw [← Finset.sum_mul]
              _ = (∑ j ∈ Finset.range (m + 1),
                  ∑ k ∈ Finset.range (n + 1), w j k) * H := by
                    rw [← Finset.sum_mul]
              _ = _ := by ring
      _ ≤ H * 4 := mul_le_mul_of_nonneg_left (by
            simpa [w] using transportTimeAnalyticConvolution_le_four n m) (by positivity)
      _ = 4 * H := by ring
  have hsource :
      C_g * Q_g ^ m * m.factorial /
          ((m + 1).factorial * Q ^ (m + 1)) ≤ A * H / 2 := by
    have hpow : Q_g ^ m ≤ Q ^ m := pow_le_pow_left₀ hQg0 hQg m
    have hfac : ((m + 1).factorial : ℝ) = (m + 1 : ℝ) * m.factorial := by
      exact_mod_cast Nat.factorial_succ m
    have hm : 1 ≤ (m + 1 : ℝ) := by norm_num
    have hden : C_f * R ≤ (m + 1 : ℝ) * Q := by
      calc
        C_f * R ≤ Q := hQ₁
        _ ≤ (m + 1 : ℝ) * Q := by nlinarith [hm, hQ]
    have hsmall :
        C_g * Q_g ^ m * m.factorial /
            ((m + 1).factorial * Q ^ (m + 1)) ≤ C_g / (C_f * R) := by
      have hnum : C_g * Q_g ^ m * m.factorial ≤ C_g * Q ^ m * m.factorial := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow hCg) (by positivity)
      have hleft :
          C_g * Q ^ m * m.factorial /
              ((m + 1).factorial * Q ^ (m + 1)) =
            C_g / ((m + 1 : ℝ) * Q) := by
        rw [hfac]
        have hmq : (m + 1 : ℝ) ≠ 0 := by positivity
        have hQpow : Q ^ m ≠ 0 := pow_ne_zero _ hQ.ne'
        field_simp [hmq, hQpow]
        rw [pow_succ]
        ring
      calc
        _ ≤ C_g * Q ^ m * m.factorial /
              ((m + 1).factorial * Q ^ (m + 1)) := by
                apply div_le_div_of_nonneg_right hnum
                positivity
        _ = C_g / ((m + 1 : ℝ) * Q) := hleft
        _ ≤ C_g / (C_f * R) := by
              apply div_le_div_of_nonneg_left hCg
              · positivity
              · exact hden
    have hAH : C_g / (C_f * R) ≤ A * H / 2 := by
      have hfactor : A * H / 2 = (C_g / (C_f * R)) * H := by
        dsimp [A]
        ring
      rw [hfactor]
      have hnonneg : 0 ≤ C_g / (C_f * R) := by positivity
      calc
        C_g / (C_f * R) = (C_g / (C_f * R)) * 1 := by ring
        _ ≤ (C_g / (C_f * R)) * H := mul_le_mul_of_nonneg_left hH hnonneg
    exact hsmall.trans hAH
  have hadv :
      2 * C_f * A * ρ / Q *
        (∑ j ∈ Finset.range (m + 1),
          ∑ k ∈ Finset.range (n + 1), w j k *
            (((k + j + 1).factorial : ℝ) / k.factorial)) ≤ A * H / 2 := by
    have hconv' : (∑ j ∈ Finset.range (m + 1),
        ∑ k ∈ Finset.range (n + 1), w j k *
          (((k + j + 1).factorial : ℝ) / k.factorial)) ≤ 4 * H := hconv
    have hscale : 2 * C_f * A * ρ / Q * (4 * H) =
        A * H * (8 * C_f * ρ / Q) := by
      ring
    have hRhoBound : 8 * C_f * ρ / Q ≤ 1 / 2 := by
      apply (div_le_iff₀ hQ).2
      have hnumer : 8 * C_f * ρ ≤ 16 * C_f * R := by nlinarith [hCf, hρ]
      have hhalf : 16 * C_f * R ≤ (1 / 2 : ℝ) * Q := by nlinarith [hQ₂]
      exact hnumer.trans hhalf
    calc
      _ ≤ 2 * C_f * A * ρ / Q * (4 * H) := by
              apply mul_le_mul_of_nonneg_left hconv'
              have hcoeff : 0 ≤ 2 * C_f := by positivity
              have hcoeffA : 0 ≤ (2 * C_f) * A := mul_nonneg hcoeff hA
              have hcoeffρ : 0 ≤ ((2 * C_f) * A) * ρ :=
                mul_nonneg hcoeffA (le_trans hR.le hRρ)
              exact div_nonneg hcoeffρ hQ.le
      _ = A * H * (8 * C_f * ρ / Q) := hscale
      _ ≤ A * H / 2 := by
            have hnonneg : 0 ≤ A * H := mul_nonneg hA (by positivity)
            simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
              (mul_le_mul_of_nonneg_left hRhoBound hnonneg)
  calc
    _ = C_g * Q_g ^ m * m.factorial /
          ((m + 1).factorial * Q ^ (m + 1)) +
        2 * C_f * A * ρ / Q *
          (∑ j ∈ Finset.range (m + 1),
            ∑ k ∈ Finset.range (n + 1), w j k *
              (((k + j + 1).factorial : ℝ) / k.factorial)) := by
          change C_g * Q_g ^ m * m.factorial /
              ((m + 1).factorial * Q ^ (m + 1)) +
            2 * C_f * A * ρ / Q *
              (∑ j ∈ Finset.range (m + 1),
                ∑ k ∈ Finset.range (n + 1), w j k *
                  (((k + j + 1).factorial : ℝ) / k.factorial)) = _
          ring
    _ ≤ A * H / 2 + A * H / 2 := add_le_add hsource hadv
    _ = A * H := by ring

end AVenhance.FaaDiBruno

end
