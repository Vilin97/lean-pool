/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! # Directional Product

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

open scoped ContDiff

noncomputable section

namespace AVenhance.FaaDiBruno

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Repeated differentiation in an ordered list of constant directions. -/
def directionalJet {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (I : List E) (f : E → F) : E → F :=
  match I with
  | [] => f
  | v :: J => fun x => fderiv ℝ (directionalJet J f) x v

/-- Every allocation of an ordered direction list between two factors,
retaining multiplicity when direction vectors repeat. -/
def directionalSplits : List E → List (List E × List E)
  | [] => [([], [])]
  | v :: J =>
      (directionalSplits J).map (fun p => (v :: p.1, p.2)) ++
      (directionalSplits J).map (fun p => (p.1, v :: p.2))

theorem directionalJet_contDiff {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (I : List E) (f : E → F) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (directionalJet I f) := by
  induction I with
  | nil => simpa [directionalJet] using hf
  | cons v I ih =>
      change ContDiff ℝ ∞ (fun x => fderiv ℝ (directionalJet I f) x v)
      have hderiv : ContDiff ℝ ∞ (fun x => fderiv ℝ (directionalJet I f) x) :=
        ih.fderiv_right (by simp)
      exact hderiv.clm_apply (contDiff_const : ContDiff ℝ ∞ (fun _ : E => v))

/-- Ordered directional jets concatenate without changing their order. -/
theorem directionalJet_append {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (I J : List E) (f : E → F) :
    directionalJet (I ++ J) f = directionalJet I (directionalJet J f) := by
  induction I with
  | nil => rfl
  | cons v I ih =>
      change (fun x => fderiv ℝ (directionalJet (I ++ J) f) x v) =
        (fun x => fderiv ℝ (directionalJet I (directionalJet J f)) x v)
      rw [ih]

/-- Two adjacent spatial derivatives commute for a smooth field. -/
theorem directionalJet_pair_swap {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : E → F) (hf : ContDiff ℝ ∞ f) (v w : E) :
    directionalJet [v, w] f = directionalJet [w, v] f := by
  funext x
  have hsymmetric := (hf.contDiffAt (x := x)).isSymmSndFDerivAt (by simp)
  have hderivC : ContDiff ℝ 1 (fun y => fderiv ℝ f y) :=
    hf.fderiv_right (m := 1) (by simp)
  have hderiv : DifferentiableAt ℝ (fun y => fderiv ℝ f y) x :=
    hderivC.differentiable_one x
  have hconstant (u : E) : DifferentiableAt ℝ (fun _ : E => u) x :=
    differentiableAt_const u
  have hEval (u z : E) :
    fderiv ℝ (fun y => fderiv ℝ f y z) x u =
        fderiv ℝ (fderiv ℝ f) x u z := by
    have h := fderiv_clm_apply hderiv (hconstant z)
    have happly := congrArg (fun A : E →L[ℝ] F => A u) h
    simpa [fderiv_const_apply] using happly
  change fderiv ℝ (fun y => fderiv ℝ f y w) x v =
    fderiv ℝ (fun y => fderiv ℝ f y v) x w
  rw [hEval w v, hEval v w]
  exact hsymmetric v w

/-- A swap of neighboring directions remains valid inside a longer ordered
jet; all derivatives to its left are applied to the equality of the two
second derivatives. -/
theorem directionalJet_adjacent_swap {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (P Q : List E) (f : E → F)
    (hf : ContDiff ℝ ∞ f) (v w : E) :
    directionalJet (P ++ [v, w] ++ Q) f =
      directionalJet (P ++ [w, v] ++ Q) f := by
  have hQ : ContDiff ℝ ∞ (directionalJet Q f) := directionalJet_contDiff Q f hf
  calc
    directionalJet (P ++ [v, w] ++ Q) f =
        directionalJet P (directionalJet [v, w] (directionalJet Q f)) := by
          simpa [List.append_assoc] using
            (directionalJet_append P ([v, w] ++ Q) f).trans
              (congrArg (directionalJet P)
                (directionalJet_append [v, w] Q f))
    _ = directionalJet P (directionalJet [w, v] (directionalJet Q f)) := by
      exact congrArg (directionalJet P)
        (directionalJet_pair_swap (directionalJet Q f) hQ v w)
    _ = directionalJet (P ++ [w, v] ++ Q) f := by
          symm
          simpa [List.append_assoc] using
            (directionalJet_append P ([w, v] ++ Q) f).trans
              (congrArg (directionalJet P)
                (directionalJet_append [w, v] Q f))

/-- Moving the final direction to the front of an ordered jet preserves its
value for a smooth field. -/
theorem directionalJet_rotate_last {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (I : List E) (v : E) (f : E → F)
    (hf : ContDiff ℝ ∞ f) :
    directionalJet (I ++ [v]) f = directionalJet (v :: I) f := by
  induction I with
  | nil => rfl
  | cons w I ih =>
      calc
        directionalJet ((w :: I) ++ [v]) f =
            directionalJet (w :: (I ++ [v])) f := rfl
        _ = directionalJet (w :: (v :: I)) f := by
          exact congrArg (directionalJet [w]) ih
        _ = directionalJet (v :: w :: I) f :=
          directionalJet_adjacent_swap [] I f hf w v

theorem DirectionalProduct.differentiableAt_list_sum {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F]
    (l : List (E → F)) (x : E)
    (hl : ∀ f ∈ l, DifferentiableAt ℝ f x) :
    DifferentiableAt ℝ (fun y => (l.map fun f => f y).sum) x := by
  induction l with
  | nil => simp
  | cons f l ih =>
      simp only [List.map_cons, List.sum_cons]
      exact (hl f (by simp)).add (ih (by
        intro g hg
        exact hl g (by simp [hg])))

theorem DirectionalProduct.list_sum_apply {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (l : List (E →L[ℝ] F)) (v : E) :
    l.sum v = (l.map fun A => A v).sum := by
  induction l with
  | nil => simp
  | cons A l ih =>
      simp only [List.sum_cons, List.map_cons, add_apply, ih]

theorem DirectionalProduct.fderiv_list_sum {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (l : List (E → F)) (x : E)
    (hl : ∀ f ∈ l, DifferentiableAt ℝ f x) :
    fderiv ℝ (fun y => (l.map fun f => f y).sum) x =
      (l.map fun f => fderiv ℝ f x).sum := by
  induction l with
  | nil => simp
  | cons f l ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [fderiv_fun_add]
      · congr 1
        exact ih (by
          intro g hg
          exact hl g (by simp [hg]))
      · exact hl f (by simp)
      · exact DirectionalProduct.differentiableAt_list_sum l x (by
          intro g hg
          exact hl g (by simp only [List.mem_cons]; right; exact hg))

theorem DirectionalProduct.contDiff_list_sum {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (l : List (E → F)) (hl : ∀ f ∈ l, ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun x => (l.map fun f => f x).sum) := by
  induction l with
  | nil => simpa using (contDiff_const : ContDiff ℝ ∞ (fun _ : E => (0 : F)))
  | cons f l ih =>
      simp only [List.map_cons, List.sum_cons]
      exact (hl f (by simp)).add (ih (by
        intro g hg
        exact hl g (by simp [hg])))

theorem directionalJet_mul (I : List E) (f g : E → ℝ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    directionalJet I (fun x => f x * g x) = fun x =>
      ((directionalSplits I).map fun p => directionalJet p.1 f x * directionalJet p.2 g x).sum := by
  induction I with
  | nil =>
      funext x
      simp [directionalJet, directionalSplits]
  | cons v I ih =>
      funext x
      change fderiv ℝ (directionalJet I (fun x => f x * g x)) x v = _
      rw [ih]
      let l := (directionalSplits I).map fun p => fun y => directionalJet p.1 f y * directionalJet
          p.2 g y
      have hdiff (p : List E × List E) :
          DifferentiableAt ℝ (fun y => directionalJet p.1 f y * directionalJet p.2 g y) x := by
        have h1 := (directionalJet_contDiff p.1 f hf).differentiable (by simp) x
        have h2 := (directionalJet_contDiff p.2 g hg).differentiable (by simp) x
        exact h1.mul h2
      have hsum := DirectionalProduct.fderiv_list_sum l x (by
        intro q hq
        rcases List.mem_map.mp hq with ⟨p, hp, rfl⟩
        exact hdiff p)
      have hsum' : fderiv ℝ
          (fun y => (List.map (fun p => directionalJet p.1 f y * directionalJet p.2 g y)
              (directionalSplits I)).sum) x =
          (List.map (fun p => fderiv ℝ
            (fun y => directionalJet p.1 f y * directionalJet p.2 g y) x) (directionalSplits
                I)).sum := by
        simpa [l, List.map_map, Function.comp_def] using hsum
      rw [hsum']
      rw [DirectionalProduct.list_sum_apply]
      have hterms (p : List E × List E) :
          fderiv ℝ (fun y => directionalJet p.1 f y * directionalJet p.2 g y) x v =
            directionalJet (v :: p.1) f x * directionalJet p.2 g x +
              directionalJet p.1 f x * directionalJet (v :: p.2) g x := by
        have h1 := (directionalJet_contDiff p.1 f hf).differentiable (by simp) x
        have h2 := (directionalJet_contDiff p.2 g hg).differentiable (by simp) x
        rw [fderiv_fun_mul h1 h2]
        simp [directionalJet, smul_eq_mul, mul_comm]
        ring
      simp only [List.map_map, Function.comp_def]
      simp only [directionalSplits, List.map_append, List.sum_append,
        List.map_map, Function.comp_def]
      rw [← List.sum_map_add]
      apply congrArg List.sum
      apply List.map_congr_left
      intro p hp
      exact hterms p

/-- The ordered directional Leibniz expansion for a scalar multiple of a
vector-valued field. -/
theorem directionalJet_smul {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (I : List E) (a : E → ℝ) (f : E → F)
    (ha : ContDiff ℝ ∞ a) (hf : ContDiff ℝ ∞ f) :
    directionalJet I (fun x => a x • f x) = fun x =>
      ((directionalSplits I).map fun p => directionalJet p.1 a x •
        directionalJet p.2 f x).sum := by
  induction I with
  | nil =>
      funext x
      simp [directionalJet, directionalSplits]
  | cons v I ih =>
      funext x
      change fderiv ℝ (directionalJet I (fun x => a x • f x)) x v = _
      rw [ih]
      let l := (directionalSplits I).map fun p => fun y =>
        directionalJet p.1 a y • directionalJet p.2 f y
      have hdiff (p : List E × List E) :
          DifferentiableAt ℝ (fun y => directionalJet p.1 a y • directionalJet p.2 f y) x := by
        have h1 := (directionalJet_contDiff p.1 a ha).differentiable (by simp) x
        have h2 := (directionalJet_contDiff p.2 f hf).differentiable (by simp) x
        exact h1.smul h2
      have hsum := DirectionalProduct.fderiv_list_sum l x (by
        intro q hq
        rcases List.mem_map.mp hq with ⟨p, hp, rfl⟩
        exact hdiff p)
      have hsum' : fderiv ℝ
          (fun y => (List.map (fun p => directionalJet p.1 a y •
            directionalJet p.2 f y) (directionalSplits I)).sum) x =
          (List.map (fun p => fderiv ℝ
            (fun y => directionalJet p.1 a y • directionalJet p.2 f y) x)
            (directionalSplits I)).sum := by
        simpa [l, List.map_map, Function.comp_def] using hsum
      rw [hsum']
      rw [DirectionalProduct.list_sum_apply]
      have hterms (p : List E × List E) :
          fderiv ℝ (fun y => directionalJet p.1 a y • directionalJet p.2 f y) x v =
            directionalJet (v :: p.1) a x • directionalJet p.2 f x +
              directionalJet p.1 a x • directionalJet (v :: p.2) f x := by
        have h1 := (directionalJet_contDiff p.1 a ha).differentiable (by simp) x
        have h2 := (directionalJet_contDiff p.2 f hf).differentiable (by simp) x
        rw [fderiv_fun_smul h1 h2]
        simp [directionalJet, ContinuousLinearMap.smulRight_apply]
        module
      simp only [List.map_map, Function.comp_def]
      simp only [directionalSplits, List.map_append, List.sum_append,
        List.map_map, Function.comp_def]
      rw [← List.sum_map_add]
      apply congrArg List.sum
      apply List.map_congr_left
      intro p hp
      exact hterms p

end AVenhance.FaaDiBruno

end
