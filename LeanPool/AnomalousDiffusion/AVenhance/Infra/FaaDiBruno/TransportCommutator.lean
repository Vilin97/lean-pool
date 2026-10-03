/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FaaDiBruno.TransportExpansion
public import Mathlib.Analysis.Calculus.VectorField

/-! # Transport Commutator

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

open scoped ContDiff
noncomputable section

namespace AVenhance.FaaDiBruno
open Homogenization

/-- Allocations of an ordered direction list in which the left factor receives
at least one direction. -/
def directionalSplitsNonempty {E : Type*} : List E → List (List E × List E)
  | [] => []
  | v :: I =>
      (directionalSplits I).map (fun p => (v :: p.1, p.2)) ++
        (directionalSplitsNonempty I).map (fun p => (p.1, v :: p.2))

/-- Every ordered Leibniz allocation is either nonempty on the left or is the
single all-right allocation. -/
theorem directionalSplits_eq_nonempty_append_empty {E : Type*} (I : List E) :
    directionalSplits I = directionalSplitsNonempty I ++ [([], I)] := by
  induction I with
  | nil => simp [directionalSplits, directionalSplitsNonempty]
  | cons v I ih =>
      simp only [directionalSplits, directionalSplitsNonempty]
      rw [ih]
      simp only [List.map_append, List.map_cons, List.map_nil]
      simp [List.append_assoc]

theorem directionalSplits_length_sum {E : Type*} (I : List E)
    (p : List E × List E) (hp : p ∈ directionalSplits I) :
    p.1.length + p.2.length = I.length := by
  induction I generalizing p with
  | nil =>
      simp only [directionalSplits, List.mem_singleton] at hp
      subst p
      simp
  | cons v I ih =>
      simp only [directionalSplits, List.mem_append, List.mem_map] at hp
      rcases hp with hp | hp
      · rcases hp with ⟨q, hq, hqeq⟩
        have h := ih q hq
        subst p
        simp only [List.length_cons]
        omega
      · rcases hp with ⟨q, hq, hqeq⟩
        have h := ih q hq
        subst p
        simp only [List.length_cons]
        omega

theorem directionalSplitsNonempty_length_sum {E : Type*} (I : List E)
    (p : List E × List E) (hp : p ∈ directionalSplitsNonempty I) :
    p.1.length + p.2.length = I.length := by
  have hfull : p ∈ directionalSplits I := by
    rw [directionalSplits_eq_nonempty_append_empty]
    exact List.mem_append_left _ hp
  exact directionalSplits_length_sum I p hfull

theorem directionalSplitsNonempty_left_pos {E : Type*} (I : List E)
    (p : List E × List E) (hp : p ∈ directionalSplitsNonempty I) :
    0 < p.1.length := by
  induction I generalizing p with
  | nil => simp [directionalSplitsNonempty] at hp
  | cons v I ih =>
      simp only [directionalSplitsNonempty, List.mem_append, List.mem_map] at hp
      rcases hp with hp | hp
      · rcases hp with ⟨q, hq, hqeq⟩
        subst p
        simp
      · rcases hp with ⟨q, hq, hqeq⟩
        have hqpos := ih q hq
        subst p
        simpa using hqpos

theorem directionalSplits_count_leftLength {E : Type*} (I : List E) (m : ℕ) :
    (directionalSplits I).countP (fun p => decide (p.1.length = m)) =
      I.length.choose m := by
  induction I generalizing m with
  | nil => cases m <;> simp [directionalSplits]
  | cons v I ih =>
      cases m with
      | zero =>
          simp only [directionalSplits, List.countP_append, List.countP_map]
          change List.countP (fun p : List E × List E =>
              decide ((v :: p.1).length = 0)) (directionalSplits I) +
            List.countP (fun p : List E × List E => decide (p.1.length = 0))
              (directionalSplits I) = 1
          have hleft : List.countP (fun p : List E × List E =>
              decide ((v :: p.1).length = 0)) (directionalSplits I) = 0 := by
            simp [List.length_cons]
          rw [hleft, ih 0]
          simp
      | succ m =>
          simp only [directionalSplits, List.countP_append, List.countP_map]
          change List.countP (fun p : List E × List E =>
              decide ((v :: p.1).length = m + 1)) (directionalSplits I) +
            List.countP (fun p : List E × List E => decide (p.1.length = m + 1))
              (directionalSplits I) = I.length.choose m + I.length.choose (m + 1)
          have hleft : List.countP (fun p : List E × List E =>
              decide ((v :: p.1).length = m + 1)) (directionalSplits I) =
              List.countP (fun p : List E × List E => decide (p.1.length = m))
                (directionalSplits I) := by
            apply List.countP_congr
            intro p hp
            simp [List.length_cons]
          rw [hleft, ih m, ih (m + 1)]

theorem directionalSplitsNonempty_count_leftLength_eq_one {E : Type*}
    (I : List E) :
    (directionalSplitsNonempty I).countP
      (fun p => decide (p.1.length = 1)) = I.length := by
  have hsplit := directionalSplits_eq_nonempty_append_empty I
  have hcount :
      (directionalSplits I).countP (fun p => decide (p.1.length = 1)) =
        (directionalSplitsNonempty I).countP
            (fun p => decide (p.1.length = 1)) +
          ([([], I)] : List (List E × List E)).countP
            (fun p => decide (p.1.length = 1)) := by
    rw [hsplit, List.countP_append]
  have hfull := directionalSplits_count_leftLength I 1
  have hlast :
      ([([], I)] : List (List E × List E)).countP
        (fun p => decide (p.1.length = 1)) = 0 := by
    simp [List.countP, List.countP.go]
  rw [hfull, hlast] at hcount
  simpa using hcount.symm

theorem directionalSplits_map {E F : Type*} (φ : E → F) (I : List E) :
    directionalSplits (I.map φ) =
      (directionalSplits I).map fun p => (p.1.map φ, p.2.map φ) := by
  induction I with
  | nil => rfl
  | cons v I ih =>
      simp [directionalSplits, ih, List.map_append, List.map_map, Function.comp_def]

theorem directionalSplitsNonempty_map {E F : Type*} (φ : E → F) (I : List E) :
    directionalSplitsNonempty (I.map φ) =
      (directionalSplitsNonempty I).map fun p => (p.1.map φ, p.2.map φ) := by
  induction I with
  | nil => rfl
  | cons v I ih =>
      simp [directionalSplitsNonempty, directionalSplits_map, ih,
        List.map_append, List.map_map, Function.comp_def]

theorem directionalSplits_weight_sum {E : Type*} (I : List E) (w : ℕ → ℝ) :
    ((directionalSplits I).map fun p => w p.1.length).sum =
      ∑ m ∈ Finset.range (I.length + 1), (I.length.choose m : ℝ) * w m := by
  induction I generalizing w with
  | nil => simp [directionalSplits]
  | cons v I ih =>
      simp only [directionalSplits, List.map_append, List.sum_append,
        List.map_map, Function.comp_def, List.length_cons]
      rw [ih (fun m => w (m + 1)), ih w]
      let n := I.length
      have hsum :
          ∑ m ∈ Finset.range (n + 2), ((n + 1).choose m : ℝ) * w m =
            (∑ m ∈ Finset.range (n + 1), (n.choose m : ℝ) * w (m + 1)) +
              ∑ m ∈ Finset.range (n + 1), (n.choose m : ℝ) * w m := by
        rw [Finset.sum_range_succ']
        simp only [Nat.choose_succ_succ, Nat.cast_add]
        simp_rw [add_mul]
        rw [Finset.sum_add_distrib]
        have htail :
            ∑ m ∈ Finset.range (n + 1), (n.choose m : ℝ) * w m =
              (∑ m ∈ Finset.range n, (n.choose (m + 1) : ℝ) * w (m + 1)) + w 0 := by
          rw [Finset.sum_range_succ']
          simp [Nat.choose_zero_right]
        have hlast :
            ∑ m ∈ Finset.range (n + 1), (n.choose (m + 1) : ℝ) * w (m + 1) =
              ∑ m ∈ Finset.range n, (n.choose (m + 1) : ℝ) * w (m + 1) := by
          rw [Finset.sum_range_succ]
          simp
        rw [htail, hlast]
        simp only [Nat.choose_zero_right, Nat.cast_one, one_mul]
        abel
      simpa [n] using hsum.symm

theorem directionalSplitsNonempty_weight_sum {E : Type*} (I : List E)
    (w : ℕ → ℝ) :
    ((directionalSplitsNonempty I).map fun p => w p.1.length).sum =
      ∑ k ∈ Finset.range I.length,
        (I.length.choose (k + 1) : ℝ) * w (k + 1) := by
  let n := I.length
  let f : ℕ → ℝ := fun m => (n.choose m : ℝ) * w m
  have hsplit := directionalSplits_eq_nonempty_append_empty I
  have hsumSplit :
      ((directionalSplits I).map fun p => w p.1.length).sum =
        ((directionalSplitsNonempty I).map fun p => w p.1.length).sum + w 0 := by
    rw [hsplit, List.map_append, List.sum_append]
    simp [List.length]
  have hfull := directionalSplits_weight_sum I w
  have htail :
      (∑ m ∈ Finset.range (n + 1), f m) =
        f 0 + ∑ k ∈ Finset.range n, f (k + 1) := by
    rw [Finset.sum_range_succ']
    abel
  have hzero : f 0 = w 0 := by simp [f]
  have hfull' :
      ((directionalSplits I).map fun p => w p.1.length).sum =
        w 0 + ∑ k ∈ Finset.range n, f (k + 1) := by
    rw [hfull, htail, hzero]
  rw [hsumSplit] at hfull'
  have hresult :
      ((directionalSplitsNonempty I).map fun p => w p.1.length).sum =
        ∑ k ∈ Finset.range n, f (k + 1) := by linarith
  simpa [f, n] using hresult

theorem directionalJet_finset_sum {E ι F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
     [NormedAddCommGroup F] [NormedSpace ℝ F]
    (I : List E) (s : Finset ι) (f : ι → E → F)
    (hf : ∀ i ∈ s, ContDiff ℝ ∞ (f i)) :
    directionalJet I (fun x => ∑ i ∈ s, f i x) = fun x =>
      ∑ i ∈ s, directionalJet I (f i) x := by
  classical
  induction I with
  | nil => rfl
  | cons v I ih =>
      funext x
      change fderiv ℝ (directionalJet I (fun x => ∑ i ∈ s, f i x)) x v = _
      rw [ih]
      have hsum : fderiv ℝ
          (fun y => ∑ i ∈ s, directionalJet I (f i) y) x =
          ∑ i ∈ s, fderiv ℝ (directionalJet I (f i)) x := by
        have hdiff : ∀ i ∈ s, DifferentiableAt ℝ (directionalJet I (f i)) x := by
          intro i hi
          exact (directionalJet_contDiff I (f i) (hf i hi)).differentiable (by simp) x
        rw [fderiv_fun_sum hdiff]
      rw [hsum]
      simp only [directionalJet, sum_apply]

theorem directionalJet_commute_single {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (I : List E) (v : E) (f : E → F) (hf : ContDiff ℝ ∞ f) :
    directionalJet I (directionalJet [v] f) =
      directionalJet [v] (directionalJet I f) := by
  calc
    directionalJet I (directionalJet [v] f) =
        directionalJet (I ++ [v]) f := by
          symm
          exact directionalJet_append I [v] f
    _ = directionalJet (v :: I) f := directionalJet_rotate_last I v f hf
    _ = directionalJet [v] (directionalJet I f) := by
          symm
          exact directionalJet_append [v] I f

theorem directionalJet_add {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (I : List E) (f g : E → F)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    directionalJet I (fun x => f x + g x) =
      fun x => directionalJet I f x + directionalJet I g x := by
  induction I with
  | nil => rfl
  | cons v I ih =>
      funext x
      change fderiv ℝ (directionalJet I (fun x => f x + g x)) x v = _
      rw [ih]
      rw [fderiv_fun_add]
      · rfl
      · exact (directionalJet_contDiff I f hf).differentiable (by simp) x
      · exact (directionalJet_contDiff I g hg).differentiable (by simp) x

theorem directionalJet_sub {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (I : List E) (f g : E → F)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    directionalJet I (fun x => f x - g x) =
      fun x => directionalJet I f x - directionalJet I g x := by
  induction I with
  | nil => rfl
  | cons v I ih =>
      funext x
      change fderiv ℝ (directionalJet I (fun x => f x - g x)) x v = _
      rw [ih]
      rw [fderiv_fun_sub]
      · rfl
      · exact (directionalJet_contDiff I f hf).differentiable (by simp) x
      · exact (directionalJet_contDiff I g hg).differentiable (by simp) x

theorem directionalJet_comp_clm {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (I : List E) (L : F →L[ℝ] G) (f : E → F)
    (hf : ContDiff ℝ ∞ f) :
    directionalJet I (fun x => L (f x)) = fun x => L (directionalJet I f x) := by
  induction I with
  | nil => rfl
  | cons v I ih =>
      funext x
      change fderiv ℝ (directionalJet I (fun x => L (f x))) x v = _
      rw [ih]
      have hdiff : DifferentiableAt ℝ (directionalJet I f) x :=
        (directionalJet_contDiff I f hf).differentiable (by simp) x
      have hcomp := L.hasFDerivAt.comp x hdiff.hasFDerivAt
      have hderiv := hcomp.fderiv
      have happly := congrArg (fun A : E →L[ℝ] G => A v) hderiv
      simpa [Function.comp_def, directionalJet] using happly

/-- The spatial part of the transport derivative. -/
def transportAdvection (b F : ℝ × Vec 2 → Vec 2) : ℝ × Vec 2 → Vec 2 :=
  fun p => ∑ i : Fin 2,
    b p i • fderiv ℝ F p (0, coordinateVector 2 i)

/-- The time derivative of a joint field. -/
def jointTimeDerivative (F : ℝ × Vec 2 → Vec 2) : ℝ × Vec 2 → Vec 2 :=
  fun p => fderiv ℝ F p (1, 0)

/-- The joint directions corresponding to an ordered list of spatial
directions. -/
def jointSpatialDirections (I : List (Vec 2)) : List (ℝ × Vec 2) :=
  I.map fun v => ((0 : ℝ), v)

theorem jointSpatialDirectionalDerivative_eq_slice_general
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (G : ℝ × Vec 2 → F) (hG : ContDiff ℝ ∞ G)
    (t : ℝ) (x v : Vec 2) :
    fderiv ℝ G (t, x) (0, v) =
      fderiv ℝ (fun y => G (t, y)) x v := by
  have hdiff : DifferentiableAt ℝ G (t, x) := hG.differentiable (by simp) (t, x)
  have hcomp := hdiff.hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)
  have hslice : HasFDerivAt (fun y : Vec 2 => G (t, y))
      ((fderiv ℝ G (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ (Vec 2))) x := by
    simpa [Function.comp_def] using hcomp
  have h := congrArg (fun A : Vec 2 →L[ℝ] F => A v) hslice.fderiv
  simpa using h.symm

theorem jointSpatialDirectionalJet_eq_slice
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (I : List (Vec 2)) (G : ℝ × Vec 2 → F)
    (hG : ContDiff ℝ ∞ G) (t : ℝ) (x : Vec 2) :
    directionalJet (jointSpatialDirections I) G (t, x) =
      directionalJet I (fun y => G (t, y)) x := by
  induction I generalizing x with
  | nil => rfl
  | cons v I ih =>
      change fderiv ℝ (directionalJet (jointSpatialDirections I) G)
          (t, x) (0, v) = _
      have hjet := directionalJet_contDiff (jointSpatialDirections I) G hG
      calc
        _ = fderiv ℝ (fun y => directionalJet (jointSpatialDirections I) G (t, y))
            x v := jointSpatialDirectionalDerivative_eq_slice_general
              (directionalJet (jointSpatialDirections I) G) hjet t x v
        _ = fderiv ℝ (directionalJet I (fun y => G (t, y))) x v := by
              have hfun : (fun y => directionalJet (jointSpatialDirections I) G (t, y)) =
                  directionalJet I (fun y => G (t, y)) := by
                funext y
                exact ih y
              rw [hfun]
        _ = directionalJet (v :: I) (fun y => G (t, y)) x := rfl

theorem transportAdvection_commutator_identity
    (I : List (Vec 2)) (b F : ℝ × Vec 2 → Vec 2)
    (hb : ContDiff ℝ ∞ b) (hF : ContDiff ℝ ∞ F) :
    directionalJet (jointSpatialDirections I) (transportAdvection b F) -
        transportAdvection b (directionalJet (jointSpatialDirections I) F) =
      fun p => ∑ i : Fin 2,
        ((directionalSplitsNonempty (jointSpatialDirections I)).map fun split =>
          directionalJet split.1 (fun q => b q i) p •
            directionalJet split.2
              (fun q => fderiv ℝ F q (0, coordinateVector 2 i)) p).sum := by
  classical
  let J := jointSpatialDirections I
  have hFderiv : ContDiff ℝ ∞ (fun p => fderiv ℝ F p) := hF.fderiv_right (by simp)
  have hcoeff (i : Fin 2) : ContDiff ℝ ∞ (fun p : ℝ × Vec 2 => b p i) := by
    have hproj : ContDiff ℝ ∞ (fun _ : ℝ × Vec 2 =>
        (ContinuousLinearMap.proj i : Vec 2 →L[ℝ] ℝ)) := contDiff_const
    simpa using hproj.clm_apply hb
  have hgrad (i : Fin 2) : ContDiff ℝ ∞ (fun p : ℝ × Vec 2 =>
      fderiv ℝ F p (0, coordinateVector 2 i)) := by
    exact hFderiv.clm_apply (contDiff_const : ContDiff ℝ ∞
      (fun _ : ℝ × Vec 2 => ((0 : ℝ), coordinateVector 2 i)))
  have hterm (i : Fin 2) : ContDiff ℝ ∞ (fun p : ℝ × Vec 2 =>
      b p i • fderiv ℝ F p (0, coordinateVector 2 i)) :=
    (hcoeff i).smul (hgrad i)
  have hsum : directionalJet J (fun p => ∑ i : Fin 2,
      b p i • fderiv ℝ F p (0, coordinateVector 2 i)) = fun p =>
      ∑ i : Fin 2, directionalJet J
        (fun q => b q i • fderiv ℝ F q (0, coordinateVector 2 i)) p :=
    directionalJet_finset_sum J Finset.univ
      (fun i p => b p i • fderiv ℝ F p (0, coordinateVector 2 i))
      (by intro i hi; exact hterm i)
  have hsumJet : directionalJet J (transportAdvection b F) = fun p =>
      ∑ i : Fin 2, directionalJet J
        (fun q => b q i • fderiv ℝ F q (0, coordinateVector 2 i)) p := by
    change directionalJet J (fun p => ∑ i : Fin 2,
      b p i • fderiv ℝ F p (0, coordinateVector 2 i)) = _
    exact hsum
  have hcommute (i : Fin 2) (p : ℝ × Vec 2) :
      directionalJet J (fun q => fderiv ℝ F q (0, coordinateVector 2 i)) p =
        fderiv ℝ (directionalJet J F) p (0, coordinateVector 2 i) := by
    have h := directionalJet_commute_single J
      ((0 : ℝ), coordinateVector 2 i) F hF
    have hp := congrFun h p
    simpa [J, jointSpatialDirections, directionalJet] using hp
  have halloc (i : Fin 2) (p : ℝ × Vec 2) :
      directionalJet J (fun q => b q i • fderiv ℝ F q (0, coordinateVector 2 i)) p =
        ((directionalSplitsNonempty J).map fun split =>
          directionalJet split.1 (fun q => b q i) p •
            directionalJet split.2
              (fun q => fderiv ℝ F q (0, coordinateVector 2 i)) p).sum +
          b p i • fderiv ℝ (directionalJet J F) p (0, coordinateVector 2 i) := by
    have h := congrFun (directionalJet_smul J (fun q => b q i)
      (fun q => fderiv ℝ F q (0, coordinateVector 2 i)) (hcoeff i) (hgrad i)) p
    rw [directionalSplits_eq_nonempty_append_empty] at h
    simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_singleton, directionalJet] at h
    rw [hcommute i p] at h
    exact h
  funext p
  change directionalJet J (transportAdvection b F) p -
      transportAdvection b (directionalJet J F) p = _
  rw [hsumJet]
  simp only [transportAdvection]
  have hsumAlloc :
      (∑ i : Fin 2, directionalJet J
        (fun q => b q i • fderiv ℝ F q (0, coordinateVector 2 i)) p) =
        ∑ i : Fin 2,
          ((directionalSplitsNonempty J).map fun split =>
            directionalJet split.1 (fun q => b q i) p •
              directionalJet split.2
                (fun q => fderiv ℝ F q (0, coordinateVector 2 i)) p).sum +
          ∑ i : Fin 2,
            b p i • fderiv ℝ (directionalJet J F) p (0, coordinateVector 2 i) := by
    calc
      _ = ∑ i : Fin 2,
          (((directionalSplitsNonempty J).map fun split =>
            directionalJet split.1 (fun q => b q i) p •
              directionalJet split.2
                (fun q => fderiv ℝ F q (0, coordinateVector 2 i)) p).sum +
            b p i • fderiv ℝ (directionalJet J F) p (0, coordinateVector 2 i)) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact halloc i p
      _ = _ := Finset.sum_add_distrib
  rw [hsumAlloc]
  abel

theorem transportSpatialJet_eq_jointDirectionalJet (I : List (Vec 2))
    (F : ℝ × Vec 2 → Vec 2) :
    transportSpatialJet I F = directionalJet (jointSpatialDirections I) F := by
  induction I with
  | nil => rfl
  | cons v I ih =>
      funext p
      simp [transportSpatialJet, transportDirectionalDerivative,
        jointSpatialDirections, directionalJet, ih]

theorem jointTimeDerivative_contDiff (F : ℝ × Vec 2 → Vec 2)
    (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (jointTimeDerivative F) := by
  have hD : ContDiff ℝ ∞ (fun p => fderiv ℝ F p) := hF.fderiv_right (by simp)
  exact hD.clm_apply (contDiff_const : ContDiff ℝ ∞
    (fun _ : ℝ × Vec 2 => ((1 : ℝ), (0 : Vec 2))))

theorem directionalJet_jointTime_commute (I : List (Vec 2))
    (F : ℝ × Vec 2 → Vec 2) (hF : ContDiff ℝ ∞ F) :
    directionalJet (jointSpatialDirections I) (jointTimeDerivative F) =
      jointTimeDerivative (directionalJet (jointSpatialDirections I) F) := by
  let J := jointSpatialDirections I
  change directionalJet J (directionalJet [((1 : ℝ), (0 : Vec 2))] F) =
    directionalJet [((1 : ℝ), (0 : Vec 2))]
      (directionalJet J F)
  calc
    directionalJet J (directionalJet [((1 : ℝ), (0 : Vec 2))] F) =
        directionalJet (J ++ [((1 : ℝ), (0 : Vec 2))]) F :=
          (directionalJet_append J [((1 : ℝ), (0 : Vec 2))] F).symm
    _ = directionalJet (((1 : ℝ), (0 : Vec 2)) :: J) F :=
      directionalJet_rotate_last J ((1 : ℝ), (0 : Vec 2)) F hF
    _ = directionalJet [((1 : ℝ), (0 : Vec 2))] (directionalJet J F) := by
          symm
          exact directionalJet_append [((1 : ℝ), (0 : Vec 2))] J F

/-- The space-time transport derivative of a joint field. -/
def jointTransportDerivative (b : ℝ × Vec 2 → Vec 2)
    (F : ℝ × Vec 2 → Vec 2) : ℝ × Vec 2 → Vec 2 :=
  fun p => fderiv ℝ F p (1, b p)

theorem transportAdvection_contDiff (b F : ℝ × Vec 2 → Vec 2)
    (hb : ContDiff ℝ ∞ b) (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (transportAdvection b F) := by
  have hFderiv : ContDiff ℝ ∞ (fun p => fderiv ℝ F p) := hF.fderiv_right (by simp)
  have hterm (i : Fin 2) : ContDiff ℝ ∞ (fun p =>
    b p i • fderiv ℝ F p (0, coordinateVector 2 i)) := by
    have hbi : ContDiff ℝ ∞ (fun p : ℝ × Vec 2 => b p i) := by
      have hproj : ContDiff ℝ ∞ (fun _ : ℝ × Vec 2 =>
          (ContinuousLinearMap.proj i : Vec 2 →L[ℝ] ℝ)) := contDiff_const
      have h := hproj.clm_apply hb
      simpa using h
    have hFi := hFderiv.clm_apply (contDiff_const : ContDiff ℝ ∞
      (fun _ : ℝ × Vec 2 => ((0 : ℝ), coordinateVector 2 i)))
    exact hbi.smul hFi
  exact ContDiff.sum (s := Finset.univ) (fun i hi => hterm i)

theorem jointTransportDerivative_eq_time_add_advection
    (b F : ℝ × Vec 2 → Vec 2) (p : ℝ × Vec 2) :
    jointTransportDerivative b F p =
      jointTimeDerivative F p + transportAdvection b F p := by
  have hsplit : ((1 : ℝ), b p) = ((1 : ℝ), (0 : Vec 2)) +
      ∑ i : Fin 2, b p i • ((0 : ℝ), coordinateVector 2 i) := by
    apply Prod.ext
    · simp
    · ext k
      fin_cases k <;> simp [coordinateVector]
  simp only [jointTransportDerivative, jointTimeDerivative, transportAdvection]
  rw [hsplit]
  simp only [map_add, map_sum, map_smul]

/-- Differentiating the transport derivative in a fixed spatial direction
produces the commutator with the spatial derivative of the drift. -/
theorem jointTransportCommutator
    (b : ℝ × Vec 2 → Vec 2) (F : ℝ × Vec 2 → Vec 2)
    (hb : ContDiff ℝ ∞ b) (hF : ContDiff ℝ ∞ F)
    (t : ℝ) (x v : Vec 2) :
    fderiv ℝ (fun p => fderiv ℝ F p (0, v)) (t, x) (1, b (t, x)) =
      fderiv ℝ (jointTransportDerivative b F) (t, x) (0, v) -
        fderiv ℝ F (t, x) (0, fderiv ℝ b (t, x) (0, v)) := by
  let W : ℝ × Vec 2 → ℝ × Vec 2 := fun p => (1, b p)
  let V : ℝ × Vec 2 → ℝ × Vec 2 := fun _ => (0, v)
  let p : ℝ × Vec 2 := (t, x)
  have hW : Differentiable ℝ W := by
    have hW' : ContDiff ℝ ∞ W := by
      simpa [W] using contDiff_const.prodMk hb
    exact hW'.differentiable (by simp)
  have hV : Differentiable ℝ V := by fun_prop
  have hcomm := VectorField.fderiv_apply_lieBracket
    (𝕜 := ℝ) (f := F) (W := W) (V := V)
    (x := p) (hF.contDiffAt) (by simp) (hW p) (hV p)
  have hbracket : VectorField.lieBracket ℝ V W p = fderiv ℝ W p (V p) := by
    simp [VectorField.lieBracket, V]
  have hcomm' := hcomm
  rw [hbracket] at hcomm'
  have hWdir : fderiv ℝ W p (V p) =
      (0, fderiv ℝ b p (0, v)) := by
    have hbAt : DifferentiableAt ℝ b p := hb.differentiable (by simp) p
    have hWderiv : fderiv ℝ W p =
        (fderiv ℝ (fun _ : ℝ × Vec 2 => (1 : ℝ)) p).prod
          (fderiv ℝ b p) :=
      DifferentiableAt.fderiv_prodMk (differentiableAt_const (1 : ℝ)) hbAt
    change fderiv ℝ W p (0, v) = _
    rw [hWderiv]
    simp [fderiv_const_apply]
  rw [hWdir] at hcomm'
  have hresult :
      fderiv ℝ (fun q => fderiv ℝ F q (0, v)) p (W p) =
        fderiv ℝ (fun q => fderiv ℝ F q (W q)) p (0, v) -
          fderiv ℝ F p (0, fderiv ℝ b p (0, v)) := by
    rw [hcomm']
    abel
  change fderiv ℝ (fun q => fderiv ℝ F q (0, v)) (t, x) (1, b (t, x)) =
      fderiv ℝ (fun q => fderiv ℝ F q (1, b q)) (t, x) (0, v) -
        fderiv ℝ F (t, x) (0, fderiv ℝ b (t, x) (0, v))
  exact hresult

theorem TransportCommutator.jointDirectionalDerivative_contDiff
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (G : ℝ × Vec 2 → F) (hG : ContDiff ℝ ∞ G) (v : ℝ × Vec 2) :
    ContDiff ℝ ∞ (fun p => fderiv ℝ G p v) := by
  have hD : ContDiff ℝ ∞ (fun p => fderiv ℝ G p) :=
    hG.fderiv_right (by simp)
  exact hD.clm_apply (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ × Vec 2 => v))

/-- Smoothness of the transport derivative of a smooth field. -/
theorem jointTransportDerivative_contDiff
    (b F : ℝ × Vec 2 → Vec 2)
    (hb : ContDiff ℝ ∞ b) (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (jointTransportDerivative b F) := by
  have hD : ContDiff ℝ ∞ (fun p => fderiv ℝ F p) := hF.fderiv_right (by simp)
  have hW : ContDiff ℝ ∞ (fun p : ℝ × Vec 2 => ((1 : ℝ), b p)) := by
    simpa using (contDiff_const.prodMk hb)
  change ContDiff ℝ ∞ (fun p => fderiv ℝ F p (1, b p))
  exact hD.clm_apply hW

/-- Smoothness of the recursively generated source in the differentiated
transport equation. -/
theorem transportSourceJet_contDiff
    (I : List (Vec 2)) (b g Y : ℝ → Vec 2 → Vec 2)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hg : ContDiff ℝ ∞ (Function.uncurry g))
    (hY : ContDiff ℝ ∞ (Function.uncurry Y)) :
    ContDiff ℝ ∞ (transportSourceJet I b g Y) := by
  induction I with
  | nil => simpa [transportSourceJet] using hg
  | cons v I ih =>
      have hsource := TransportCommutator.jointDirectionalDerivative_contDiff
        (transportSourceJet I b g Y) ih (0, v)
      have hYjet := transportSpatialJet_contDiff I (Function.uncurry Y) hY
      have hYderiv : ContDiff ℝ ∞
          (fun p => fderiv ℝ (transportSpatialJet I (Function.uncurry Y)) p) :=
        hYjet.fderiv_right (by simp)
      have hbdir := TransportCommutator.jointDirectionalDerivative_contDiff
        (Function.uncurry b) hb (0, v)
      have hdir : ContDiff ℝ ∞
          (fun p : ℝ × Vec 2 => ((0 : ℝ), fderiv ℝ (Function.uncurry b) p (0, v))) := by
        simpa using (contDiff_const.prodMk hbdir)
      exact hsource.sub (hYderiv.clm_apply hdir)

/-- The recursive commutator source equals the derivative-of-source minus the
transport commutator, for every ordered spatial jet. -/
theorem transportSourceJet_commutator_identity
    (I : List (Vec 2)) (b g Y : ℝ → Vec 2 → Vec 2)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hg : ContDiff ℝ ∞ (Function.uncurry g))
    (hY : ContDiff ℝ ∞ (Function.uncurry Y)) :
    transportSourceJet I b g Y =
      transportSpatialJet I (Function.uncurry g) -
        transportSpatialJet I
          (jointTransportDerivative (Function.uncurry b) (Function.uncurry Y)) +
        jointTransportDerivative (Function.uncurry b)
          (transportSpatialJet I (Function.uncurry Y)) := by
  induction I with
  | nil =>
      funext p
      simp [transportSourceJet, transportSpatialJet, jointTransportDerivative]
  | cons v I ih =>
      funext p
      rcases p with ⟨t, x⟩
      have hprevSmooth := transportSourceJet_contDiff I b g Y hb hg hY
      have hjetSmooth := transportSpatialJet_contDiff I (Function.uncurry Y) hY
      let F : ℝ × Vec 2 → Vec 2 := transportSpatialJet I (Function.uncurry Y)
      let G : ℝ × Vec 2 → Vec 2 := transportSpatialJet I (Function.uncurry g)
      let A : ℝ × Vec 2 → Vec 2 :=
        transportSpatialJet I
          (jointTransportDerivative (Function.uncurry b) (Function.uncurry Y))
      let H : ℝ × Vec 2 → Vec 2 :=
        jointTransportDerivative (Function.uncurry b) F
      have hsourceTerm := jointTransportDerivative_contDiff
        (Function.uncurry b) (Function.uncurry Y) hb hY
      have hATerm := transportSpatialJet_contDiff I _ hsourceTerm
      have hHTerm := jointTransportDerivative_contDiff (Function.uncurry b) F hb hjetSmooth
      have hGAt := (transportSpatialJet_contDiff I (Function.uncurry g) hg).differentiable
        (by simp) (t, x)
      have hAAt := hATerm.differentiable (by simp) (t, x)
      have hHAt := hHTerm.differentiable (by simp) (t, x)
      have hsumDeriv := fderiv_fun_add (hGAt.sub hAAt) hHAt
      have hsubDeriv := fderiv_fun_sub hGAt hAAt
      change fderiv ℝ (G - A + H) (t, x) = _ at hsumDeriv
      change fderiv ℝ (G - A) (t, x) = _ at hsubDeriv
      have hprev : transportSourceJet I b g Y =
          G - A + H := by simpa [G, A, H] using ih
      have hprevDeriv := congrArg
          (fun H : ℝ × Vec 2 → Vec 2 => fderiv ℝ H (t, x) (0, v)) hprev
      change fderiv ℝ (transportSourceJet I b g Y) (t, x) (0, v) =
        fderiv ℝ (G - A + H) (t, x) (0, v) at hprevDeriv
      rw [hsumDeriv, hsubDeriv] at hprevDeriv
      have hcomm := jointTransportCommutator (Function.uncurry b) F hb hjetSmooth t x v
      dsimp [transportSourceJet, transportSpatialJet, transportDirectionalDerivative]
      change fderiv ℝ (transportSourceJet I b g Y) (t, x) (0, v) -
          fderiv ℝ (transportSpatialJet I (Function.uncurry Y)) (t, x)
            (0, fderiv ℝ (Function.uncurry b) (t, x) (0, v)) =
          fderiv ℝ (transportSpatialJet I (Function.uncurry g)) (t, x) (0, v) -
          fderiv ℝ (transportSpatialJet I
            (jointTransportDerivative (Function.uncurry b) (Function.uncurry Y)))
              (t, x) (0, v) +
          jointTransportDerivative (Function.uncurry b)
            (transportDirectionalDerivative F v) (t, x)
      change fderiv ℝ (transportSourceJet I b g Y) (t, x) (0, v) -
          fderiv ℝ F (t, x)
            (0, fderiv ℝ (Function.uncurry b) (t, x) (0, v)) =
        fderiv ℝ (transportSpatialJet I (Function.uncurry g)) (t, x) (0, v) -
          fderiv ℝ (transportSpatialJet I
            (jointTransportDerivative (Function.uncurry b) (Function.uncurry Y)))
              (t, x) (0, v) +
          jointTransportDerivative (Function.uncurry b)
            (transportDirectionalDerivative F v) (t, x)
      rw [hprevDeriv]
      simp only [add_apply, sub_apply]
      have hcommApplied :
          jointTransportDerivative (Function.uncurry b)
              (transportDirectionalDerivative F v) (t, x) =
            fderiv ℝ (jointTransportDerivative (Function.uncurry b) F)
                (t, x) (0, v) -
              fderiv ℝ F (t, x)
                (0, fderiv ℝ (Function.uncurry b) (t, x) (0, v)) := by
        change fderiv ℝ (fun p => fderiv ℝ F p (0, v)) (t, x)
            (1, Function.uncurry b (t, x)) = _
        exact hcomm
      rw [hcommApplied]
      abel

theorem transportSourceJet_nonempty_identity
    (I : List (Vec 2)) (b g Y : ℝ → Vec 2 → Vec 2)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hg : ContDiff ℝ ∞ (Function.uncurry g))
    (hY : ContDiff ℝ ∞ (Function.uncurry Y)) :
    transportSourceJet I b g Y =
      transportSpatialJet I (Function.uncurry g) - fun p =>
        ∑ i : Fin 2,
          ((directionalSplitsNonempty (jointSpatialDirections I)).map fun split =>
            directionalJet split.1 (fun q => Function.uncurry b q i) p •
              directionalJet split.2 (fun q =>
                fderiv ℝ (Function.uncurry Y) q (0, coordinateVector 2 i)) p).sum := by
  let B := Function.uncurry b
  let G := Function.uncurry g
  let F := Function.uncurry Y
  let J := jointSpatialDirections I
  have hspatial (H : ℝ × Vec 2 → Vec 2) :
      transportSpatialJet I H = directionalJet J H := by
    simpa [J] using transportSpatialJet_eq_jointDirectionalJet I H
  have htransport (H : ℝ × Vec 2 → Vec 2) :
      jointTransportDerivative B H = jointTimeDerivative H + transportAdvection B H := by
    funext p
    exact jointTransportDerivative_eq_time_add_advection B H p
  have htimeF : ContDiff ℝ ∞ (jointTimeDerivative F) :=
    jointTimeDerivative_contDiff F hY
  have hadvF : ContDiff ℝ ∞ (transportAdvection B F) :=
    transportAdvection_contDiff B F hb hY
  have hjetSmooth : ContDiff ℝ ∞ (directionalJet J F) :=
    directionalJet_contDiff J F hY
  have htimeCommute := directionalJet_jointTime_commute I F hY
  have hadvCommute := transportAdvection_commutator_identity I B F hb hY
  have hsource := transportSourceJet_commutator_identity I b g Y hb hg hY
  simp_rw [hspatial] at hsource
  rw [htransport F, htransport (directionalJet J F)] at hsource
  change transportSourceJet I b g Y =
    directionalJet J G -
      directionalJet J (fun p => jointTimeDerivative F p + transportAdvection B F p) +
      (jointTimeDerivative (directionalJet J F) +
        transportAdvection B (directionalJet J F)) at hsource
  rw [directionalJet_add J (jointTimeDerivative F) (transportAdvection B F)
    htimeF hadvF] at hsource
  have htimeCommute' :
      directionalJet J (jointTimeDerivative F) =
        jointTimeDerivative (directionalJet J F) := by
    simpa [J] using htimeCommute
  rw [htimeCommute'] at hsource
  funext p
  have hs := congrFun hsource p
  have ha := congrFun hadvCommute p
  rw [hspatial G]
  change transportSourceJet I b g Y p =
    directionalJet J G p -
      ∑ i : Fin 2,
        ((directionalSplitsNonempty J).map fun split =>
          directionalJet split.1 (fun q => B q i) p •
            directionalJet split.2
              (fun q => fderiv ℝ F q (0, coordinateVector 2 i)) p).sum
  calc
    transportSourceJet I b g Y p =
        directionalJet J G p -
          (directionalJet J (transportAdvection B F) p -
            transportAdvection B (directionalJet J F) p) := by
          rw [hs]
          simp only [Pi.sub_apply, Pi.add_apply]
          abel
    _ = _ := by
      have ha' : directionalJet J (transportAdvection B F) p -
          transportAdvection B (directionalJet J F) p =
            ∑ i : Fin 2,
              ((directionalSplitsNonempty J).map fun split =>
                directionalJet split.1 (fun q => B q i) p •
                  directionalJet split.2
                    (fun q => fderiv ℝ F q (0, coordinateVector 2 i)) p).sum := by
        simpa [J] using ha
      rw [ha']

end AVenhance.FaaDiBruno

end
