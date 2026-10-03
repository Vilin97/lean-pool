/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.SpaceGrad
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Add

/-! First-order transport commutator identities for smooth Euclidean fields. -/

@[expose] public section

noncomputable section

open Homogenization

namespace AVenhance.Infra.Classical

/-- The scalar transport term associated with a vector field and a scalar function. -/
def classicalTransport (b : Vec 2 → Vec 2) (u : Vec 2 → ℝ) (x : Vec 2) : ℝ :=
  Homogenization.vecDot (b x) (AVenhance.spaceGrad u x)

/-- Coordinate derivative of a product of two smooth scalar functions. -/
theorem classicalProduct_firstDerivative (f g : Vec 2 → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (i : Fin 2) (x : Vec 2) :
    AVenhance.spaceGrad (fun y => f y * g y) x i =
      f x * AVenhance.spaceGrad g x i + AVenhance.spaceGrad f x i * g x := by
  change fderiv ℝ (fun y => f y * g y) x (Homogenization.basisVec i) = _
  rw [fderiv_fun_mul (hf.differentiable (by simp) x) (hg.differentiable (by simp) x)]
  simp only [add_apply, smul_apply, AVenhance.spaceGrad]
  ring

/-- Coordinate derivative commutes with subtraction for smooth scalar functions. -/
theorem classicalSpaceGrad_sub (f g : Vec 2 → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (i : Fin 2) (x : Vec 2) :
    AVenhance.spaceGrad (fun y => f y - g y) x i =
      AVenhance.spaceGrad f x i - AVenhance.spaceGrad g x i := by
  change fderiv ℝ (fun y => f y - g y) x (Homogenization.basisVec i) = _
  rw [fderiv_fun_sub (hf.differentiable (by simp) x) (hg.differentiable (by simp) x)]
  simp [AVenhance.spaceGrad]

theorem Commutator.classicalSpaceGrad_contDiff (f : Vec 2 → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => AVenhance.spaceGrad f x i) := by
  change ContDiff ℝ (⊤ : ℕ∞)
    (fun x => fderiv ℝ f x (Homogenization.basisVec i))
  exact (hf.fderiv_right (by simp)).clm_apply contDiff_const

theorem Commutator.classicalTransport_contDiff (b : Vec 2 → Vec 2) (u : Vec 2 → ℝ)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
    ContDiff ℝ (⊤ : ℕ∞) (classicalTransport b u) := by
  unfold classicalTransport
  change ContDiff ℝ (⊤ : ℕ∞)
    (fun x => ∑ j : Fin 2, b x j * AVenhance.spaceGrad u x j)
  apply ContDiff.sum
  intro j hj
  exact ((contDiff_pi.1 hb) j).mul (Commutator.classicalSpaceGrad_contDiff u hu j)

/-- An ordered word of coordinate derivatives applied to a scalar function. -/
def classicalWordDerivative : List (Fin 2) → (Vec 2 → ℝ) → Vec 2 → ℝ
  | [], f => f
  | i :: w, f => fun x => AVenhance.spaceGrad (classicalWordDerivative w f) x i

theorem classicalWordDerivative_contDiff (w : List (Fin 2)) (f : Vec 2 → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (classicalWordDerivative w f) := by
  induction w with
  | nil => exact hf
  | cons i w ih =>
    exact Commutator.classicalSpaceGrad_contDiff (classicalWordDerivative w f) ih i

/-- Smooth mixed coordinate derivatives commute. -/
theorem classicalSpaceGrad_commute (f : Vec 2 → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i j : Fin 2) (x : Vec 2) :
    AVenhance.spaceGrad (fun y => AVenhance.spaceGrad f y j) x i =
      AVenhance.spaceGrad (fun y => AVenhance.spaceGrad f y i) x j := by
  let g : Vec 2 → Vec 2 →L[ℝ] ℝ := fun y => fderiv ℝ f y
  have hfirst (y : Vec 2) : HasFDerivAt f (fderiv ℝ f y) y :=
    (hf.differentiable (by simp) y).hasFDerivAt
  have hsecond : ContDiff ℝ (⊤ : ℕ∞) g := by
    dsimp [g]
    exact hf.fderiv_right (by simp)
  have hsecond' (y : Vec 2) : HasFDerivAt g (fderiv ℝ g y) y :=
    (hsecond.differentiable (by simp) y).hasFDerivAt
  have hsymmetric := second_derivative_symmetric hfirst (hsecond' x)
    (Homogenization.basisVec i) (Homogenization.basisVec j)
  have hleft : AVenhance.spaceGrad
      (fun y => AVenhance.spaceGrad f y j) x i =
        fderiv ℝ g x (Homogenization.basisVec i) (Homogenization.basisVec j) := by
    change fderiv ℝ (fun y => fderiv ℝ f y (Homogenization.basisVec j)) x
      (Homogenization.basisVec i) = _
    rw [fderiv_clm_apply (hsecond.differentiable (by simp) x) (by fun_prop)]
    simp [g]
  have hright : AVenhance.spaceGrad
      (fun y => AVenhance.spaceGrad f y i) x j =
        fderiv ℝ g x (Homogenization.basisVec j) (Homogenization.basisVec i) := by
    change fderiv ℝ (fun y => fderiv ℝ f y (Homogenization.basisVec i)) x
      (Homogenization.basisVec j) = _
    rw [fderiv_clm_apply (hsecond.differentiable (by simp) x) (by fun_prop)]
    simp [g]
  rw [hleft, hright]
  exact hsymmetric

/-- A coordinate derivative can be moved through an arbitrary ordered word of smooth coordinate
derivatives. -/
theorem classicalWordDerivative_commute_gradient (w : List (Fin 2)) (f : Vec 2 → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (j : Fin 2) :
    classicalWordDerivative w (fun y => AVenhance.spaceGrad f y j) =
      fun x => AVenhance.spaceGrad (classicalWordDerivative w f) x j := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    have hrest := ih
    funext x
    change AVenhance.spaceGrad
        (classicalWordDerivative w (fun y => AVenhance.spaceGrad f y j)) x i = _
    rw [hrest]
    exact classicalSpaceGrad_commute (classicalWordDerivative w f)
      (classicalWordDerivative_contDiff w f hf) i j x

/-- Coordinate derivative of a sum of smooth scalar functions. -/
theorem classicalSpaceGrad_add (f g : Vec 2 → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (i : Fin 2) (x : Vec 2) :
    AVenhance.spaceGrad (fun y => f y + g y) x i =
      AVenhance.spaceGrad f x i + AVenhance.spaceGrad g x i := by
  change fderiv ℝ (fun y => f y + g y) x (Homogenization.basisVec i) = _
  rw [fderiv_fun_add (hf.differentiable (by simp) x) (hg.differentiable (by simp) x)]
  simp [AVenhance.spaceGrad]

theorem Commutator.classicalContDiff_listSum (L : List (Vec 2 → ℝ))
    (hL : ∀ f ∈ L, ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) L.sum := by
  induction L with
  | nil =>
    change ContDiff ℝ (⊤ : ℕ∞) (fun _ : Vec 2 => (0 : ℝ))
    exact contDiff_const
  | cons f L ih =>
    have hf := hL f (by simp)
    have htail : ∀ g ∈ L, ContDiff ℝ (⊤ : ℕ∞) g := by
      intro g hg
      exact hL g (by simp [hg])
    change ContDiff ℝ (⊤ : ℕ∞) (fun y => f y + L.sum y)
    exact hf.add (ih htail)

theorem Commutator.classicalSpaceGrad_listSum (L : List (Vec 2 → ℝ))
    (hL : ∀ f ∈ L, ContDiff ℝ (⊤ : ℕ∞) f) (i : Fin 2) (x : Vec 2) :
    AVenhance.spaceGrad L.sum x i = (L.map fun f => AVenhance.spaceGrad f x i).sum := by
  induction L with
  | nil => simp [AVenhance.spaceGrad]
  | cons f L ih =>
    have hf := hL f (by simp)
    have htail : ∀ g ∈ L, ContDiff ℝ (⊤ : ℕ∞) g := by
      intro g hg
      exact hL g (by simp [hg])
    change AVenhance.spaceGrad (fun y => f y + L.sum y) x i = _
    rw [classicalSpaceGrad_add f L.sum hf (Commutator.classicalContDiff_listSum L htail) i x,
      ih htail]
    simp

/-- All ways of distributing an ordered derivative word between two factors. -/
def classicalWordSplits : List (Fin 2) → List (List (Fin 2) × List (Fin 2))
  | [] => [([], [])]
  | i :: w =>
      (classicalWordSplits w).map (fun p => (i :: p.1, p.2)) ++
      (classicalWordSplits w).map (fun p => (p.1, i :: p.2))

/-- The product term attached to one split of a derivative word. -/
def classicalWordProductTerm (p : List (Fin 2) × List (Fin 2))
    (f g : Vec 2 → ℝ) : Vec 2 → ℝ :=
  fun x => classicalWordDerivative p.1 f x * classicalWordDerivative p.2 g x

/-- Leibniz expansion of an ordered word of coordinate derivatives. -/
def classicalWordProductExpansion (w : List (Fin 2)) (f g : Vec 2 → ℝ) : Vec 2 → ℝ :=
  ((classicalWordSplits w).map fun p => classicalWordProductTerm p f g).sum

/-- The derivative splits with at least one derivative assigned to the first factor. -/
def classicalWordCommutatorSplits : List (Fin 2) →
    List (List (Fin 2) × List (Fin 2))
  | [] => []
  | i :: w =>
      (classicalWordSplits w).map (fun p => (i :: p.1, p.2)) ++
      (classicalWordCommutatorSplits w).map (fun p => (p.1, i :: p.2))

theorem classicalWordSplits_length (w : List (Fin 2))
    {p : List (Fin 2) × List (Fin 2)} (hp : p ∈ classicalWordSplits w) :
    p.1.length + p.2.length = w.length := by
  induction w generalizing p with
  | nil =>
    simp only [classicalWordSplits, List.mem_singleton] at hp
    subst p
    simp
  | cons i w ih =>
    simp only [classicalWordSplits, List.mem_append] at hp
    rcases hp with hp | hp
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      have hlen := ih hq
      simp only [List.length_cons]
      omega
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      have hlen := ih hq
      simp only [List.length_cons]
      omega

theorem classicalWordCommutatorSplits_length (w : List (Fin 2))
    {p : List (Fin 2) × List (Fin 2)} (hp : p ∈ classicalWordCommutatorSplits w) :
    p.1.length + p.2.length = w.length := by
  induction w generalizing p with
  | nil => simp [classicalWordCommutatorSplits] at hp
  | cons i w ih =>
    simp only [classicalWordCommutatorSplits, List.mem_append] at hp
    rcases hp with hp | hp
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      have hlen := classicalWordSplits_length w hq
      simp only [List.length_cons]
      omega
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      have hlen := ih hq
      simp only [List.length_cons]
      omega

theorem classicalWordCommutatorSplits_left_ne_nil (w : List (Fin 2))
    {p : List (Fin 2) × List (Fin 2)} (hp : p ∈ classicalWordCommutatorSplits w) :
    p.1 ≠ [] := by
  induction w generalizing p with
  | nil => simp [classicalWordCommutatorSplits] at hp
  | cons i w ih =>
    simp only [classicalWordCommutatorSplits, List.mem_append] at hp
    rcases hp with hp | hp
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      simp
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact ih (p := q) hq

theorem classicalWordCommutatorSplits_right_length_lt (w : List (Fin 2))
    {p : List (Fin 2) × List (Fin 2)} (hp : p ∈ classicalWordCommutatorSplits w) :
    p.2.length < w.length := by
  have hlen := classicalWordCommutatorSplits_length w hp
  have hleft : 0 < p.1.length := by
    cases h : p.1 with
    | nil => exact (classicalWordCommutatorSplits_left_ne_nil w hp h).elim
    | cons a L => simp
  omega

/-- The finite Leibniz sum over splits with a nonempty first derivative word. -/
def classicalWordCommutatorExpansion (w : List (Fin 2))
    (f g : Vec 2 → ℝ) : Vec 2 → ℝ :=
  ((classicalWordCommutatorSplits w).map fun p => classicalWordProductTerm p f g).sum

theorem Commutator.classicalListSum_eval (L : List (Vec 2 → ℝ)) (x : Vec 2) :
    L.sum x = (L.map fun f => f x).sum := by
  induction L with
  | nil => simp
  | cons f L ih => simp [ih]

theorem Commutator.classicalListSum_map_add {α : Type} (L : List α) (f g : α → ℝ) :
    (L.map fun a => f a + g a).sum = (L.map f).sum + (L.map g).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [ih]; ring

theorem Commutator.classicalWordProductTerm_contDiff (p : List (Fin 2) × List (Fin 2))
    (f g : Vec 2 → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    ContDiff ℝ (⊤ : ℕ∞) (classicalWordProductTerm p f g) := by
  exact (classicalWordDerivative_contDiff p.1 f hf).mul
    (classicalWordDerivative_contDiff p.2 g hg)

theorem Commutator.classicalWordProductTerm_firstDerivative
    (p : List (Fin 2) × List (Fin 2)) (f g : Vec 2 → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (i : Fin 2) (x : Vec 2) :
    AVenhance.spaceGrad (classicalWordProductTerm p f g) x i =
      classicalWordProductTerm (i :: p.1, p.2) f g x +
        classicalWordProductTerm (p.1, i :: p.2) f g x := by
  rcases p with ⟨u, v⟩
  change AVenhance.spaceGrad
      (fun y => classicalWordDerivative u f y * classicalWordDerivative v g y) x i = _
  rw [classicalProduct_firstDerivative (classicalWordDerivative u f)
    (classicalWordDerivative v g)
    (classicalWordDerivative_contDiff u f hf)
    (classicalWordDerivative_contDiff v g hg) i x]
  simp [classicalWordProductTerm, classicalWordDerivative]
  ring

theorem Commutator.classicalWordCommutatorExpansion_firstDerivative
    (w : List (Fin 2)) (f g : Vec 2 → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (i : Fin 2) (x : Vec 2) :
    AVenhance.spaceGrad (classicalWordCommutatorExpansion w f g) x i =
      ((classicalWordCommutatorSplits w).map fun p =>
        classicalWordProductTerm (i :: p.1, p.2) f g x).sum +
      ((classicalWordCommutatorSplits w).map fun p =>
        classicalWordProductTerm (p.1, i :: p.2) f g x).sum := by
  let terms := (classicalWordCommutatorSplits w).map fun p =>
    classicalWordProductTerm p f g
  have hterms : ∀ F ∈ terms, ContDiff ℝ (⊤ : ℕ∞) F := by
    intro F hF
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hF
    exact Commutator.classicalWordProductTerm_contDiff p f g hf hg
  unfold classicalWordCommutatorExpansion
  change AVenhance.spaceGrad terms.sum x i = _
  rw [Commutator.classicalSpaceGrad_listSum terms hterms i x]
  simp only [terms]
  have hmap :
      (classicalWordCommutatorSplits w).map
          (fun p => AVenhance.spaceGrad (classicalWordProductTerm p f g) x i) =
        (classicalWordCommutatorSplits w).map (fun p =>
          classicalWordProductTerm (i :: p.1, p.2) f g x +
            classicalWordProductTerm (p.1, i :: p.2) f g x) := by
    apply List.map_congr_left
    intro p hp
    exact Commutator.classicalWordProductTerm_firstDerivative p f g hf hg i x
  have hmap' :
      List.map (fun F => AVenhance.spaceGrad F x i)
          (List.map (fun p => classicalWordProductTerm p f g)
            (classicalWordCommutatorSplits w)) =
        (classicalWordCommutatorSplits w).map (fun p =>
          classicalWordProductTerm (i :: p.1, p.2) f g x +
            classicalWordProductTerm (p.1, i :: p.2) f g x) := by
    rw [List.map_map]
    change (classicalWordCommutatorSplits w).map
        (fun p => AVenhance.spaceGrad (classicalWordProductTerm p f g) x i) = _
    exact hmap
  rw [hmap', Commutator.classicalListSum_map_add]

theorem Commutator.classicalWordProductTerm_left_derivative
    (p : List (Fin 2) × List (Fin 2)) (f g : Vec 2 → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : Fin 2) (x : Vec 2) :
    classicalWordProductTerm p (fun y => AVenhance.spaceGrad f y i) g x =
      classicalWordProductTerm (i :: p.1, p.2) f g x := by
  rcases p with ⟨u, v⟩
  have hcomm := congrFun (classicalWordDerivative_commute_gradient u f hf i) x
  change classicalWordDerivative u (fun y => AVenhance.spaceGrad f y i) x *
      classicalWordDerivative v g x =
    classicalWordDerivative (i :: u) f x * classicalWordDerivative v g x
  rw [hcomm]
  rfl

theorem Commutator.classicalWordProductTerm_right_derivative
    (p : List (Fin 2) × List (Fin 2)) (f g : Vec 2 → ℝ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (i : Fin 2) (x : Vec 2) :
    classicalWordProductTerm p f (fun y => AVenhance.spaceGrad g y i) x =
      classicalWordProductTerm (p.1, i :: p.2) f g x := by
  rcases p with ⟨u, v⟩
  have hcomm := congrFun (classicalWordDerivative_commute_gradient v g hg i) x
  change classicalWordDerivative u f x *
      classicalWordDerivative v (fun y => AVenhance.spaceGrad g y i) x =
    classicalWordDerivative u f x * classicalWordDerivative (i :: v) g x
  rw [hcomm]
  rfl

theorem Commutator.classicalWordProductExpansion_left_derivative
    (w : List (Fin 2)) (f g : Vec 2 → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : Fin 2) (x : Vec 2) :
    classicalWordProductExpansion w (fun y => AVenhance.spaceGrad f y i) g x =
      ((classicalWordSplits w).map fun p =>
        classicalWordProductTerm (i :: p.1, p.2) f g x).sum := by
  unfold classicalWordProductExpansion
  rw [Commutator.classicalListSum_eval]
  rw [List.map_map]
  simp only [Function.comp_def]
  apply congrArg List.sum
  change (classicalWordSplits w).map
      (fun p => classicalWordProductTerm p (fun y => AVenhance.spaceGrad f y i) g x) = _
  apply List.map_congr_left
  intro p hp
  exact Commutator.classicalWordProductTerm_left_derivative p f g hf i x

theorem Commutator.classicalWordCommutatorExpansion_left_derivative
    (w : List (Fin 2)) (f g : Vec 2 → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : Fin 2) (x : Vec 2) :
    classicalWordCommutatorExpansion w (fun y => AVenhance.spaceGrad f y i) g x =
      ((classicalWordCommutatorSplits w).map fun p =>
        classicalWordProductTerm (i :: p.1, p.2) f g x).sum := by
  unfold classicalWordCommutatorExpansion
  rw [Commutator.classicalListSum_eval]
  rw [List.map_map]
  simp only [Function.comp_def]
  apply congrArg List.sum
  change (classicalWordCommutatorSplits w).map
      (fun p => classicalWordProductTerm p (fun y => AVenhance.spaceGrad f y i) g x) = _
  apply List.map_congr_left
  intro p hp
  exact Commutator.classicalWordProductTerm_left_derivative p f g hf i x

theorem Commutator.classicalWordCommutatorExpansion_right_derivative
    (w : List (Fin 2)) (f g : Vec 2 → ℝ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (i : Fin 2) (x : Vec 2) :
    classicalWordCommutatorExpansion w f (fun y => AVenhance.spaceGrad g y i) x =
      ((classicalWordCommutatorSplits w).map fun p =>
        classicalWordProductTerm (p.1, i :: p.2) f g x).sum := by
  unfold classicalWordCommutatorExpansion
  rw [Commutator.classicalListSum_eval]
  rw [List.map_map]
  simp only [Function.comp_def]
  apply congrArg List.sum
  change (classicalWordCommutatorSplits w).map
      (fun p => classicalWordProductTerm p f (fun y => AVenhance.spaceGrad g y i) x) = _
  apply List.map_congr_left
  intro p hp
  exact Commutator.classicalWordProductTerm_right_derivative p f g hg i x

theorem Commutator.classicalWordCommutatorExpansion_cons
    (w : List (Fin 2)) (f g : Vec 2 → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (i : Fin 2) (x : Vec 2) :
    classicalWordCommutatorExpansion (i :: w) f g x =
    classicalWordProductExpansion w (fun y => AVenhance.spaceGrad f y i) g x +
      classicalWordCommutatorExpansion w f (fun y => AVenhance.spaceGrad g y i) x := by
  change ((classicalWordCommutatorSplits (i :: w)).map fun p =>
      classicalWordProductTerm p f g).sum x = _
  rw [Commutator.classicalListSum_eval]
  rw [classicalWordCommutatorSplits]
  rw [List.map_append]
  rw [List.map_append]
  rw [List.sum_append]
  simp only [List.map_map, Function.comp_def]
  rw [← Commutator.classicalWordProductExpansion_left_derivative w f g hf i x,
    ← Commutator.classicalWordCommutatorExpansion_right_derivative w f g hg i x]

theorem Commutator.classicalWordCommutatorExpansion_contDiff
    (w : List (Fin 2)) (f g : Vec 2 → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    ContDiff ℝ (⊤ : ℕ∞) (classicalWordCommutatorExpansion w f g) := by
  let terms := (classicalWordCommutatorSplits w).map fun p =>
    classicalWordProductTerm p f g
  have hterms : ∀ F ∈ terms, ContDiff ℝ (⊤ : ℕ∞) F := by
    intro F hF
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hF
    exact Commutator.classicalWordProductTerm_contDiff p f g hf hg
  exact Commutator.classicalContDiff_listSum terms hterms

theorem Commutator.classicalWordProductExpansion_firstDerivative (w : List (Fin 2))
    (f g : Vec 2 → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (i : Fin 2) (x : Vec 2) :
    AVenhance.spaceGrad (classicalWordProductExpansion w f g) x i =
      classicalWordProductExpansion (i :: w) f g x := by
  let terms := (classicalWordSplits w).map fun p => classicalWordProductTerm p f g
  have hterms : ∀ F ∈ terms, ContDiff ℝ (⊤ : ℕ∞) F := by
    intro F hF
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hF
    exact Commutator.classicalWordProductTerm_contDiff p f g hf hg
  unfold classicalWordProductExpansion
  change AVenhance.spaceGrad terms.sum x i = _
  rw [Commutator.classicalSpaceGrad_listSum terms hterms i x]
  rw [Commutator.classicalListSum_eval]
  simp only [terms]
  have hmap :
      ((classicalWordSplits w).map fun p =>
        AVenhance.spaceGrad (classicalWordProductTerm p f g) x i) =
      ((classicalWordSplits w).map fun p =>
        classicalWordProductTerm (i :: p.1, p.2) f g x +
          classicalWordProductTerm (p.1, i :: p.2) f g x) := by
    apply List.map_congr_left
    intro p hp
    exact Commutator.classicalWordProductTerm_firstDerivative p f g hf hg i x
  have hmap' :
      List.map (fun F => AVenhance.spaceGrad F x i)
          (List.map (fun p => classicalWordProductTerm p f g) (classicalWordSplits w)) =
        ((classicalWordSplits w).map fun p =>
          classicalWordProductTerm (i :: p.1, p.2) f g x +
            classicalWordProductTerm (p.1, i :: p.2) f g x) := by
    rw [List.map_map]
    change (classicalWordSplits w).map
        (fun p => AVenhance.spaceGrad (classicalWordProductTerm p f g) x i) = _
    exact hmap
  rw [hmap']
  rw [Commutator.classicalListSum_map_add]
  simp only [classicalWordSplits, List.map_append, List.sum_append, List.map_map]
  simp only [← List.map_map]
  simp only [List.map_map, Function.comp_def]

/-- An arbitrary ordered coordinate derivative of a product is the finite Leibniz sum over all
ways to distribute its derivative word between the factors. -/
theorem classicalWordDerivative_mul (w : List (Fin 2)) (f g : Vec 2 → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    classicalWordDerivative w (fun x => f x * g x) =
      classicalWordProductExpansion w f g := by
  induction w with
  | nil =>
    funext x
    simp [classicalWordDerivative, classicalWordProductExpansion,
      classicalWordSplits, classicalWordProductTerm]
  | cons i w ih =>
    funext x
    change AVenhance.spaceGrad
        (classicalWordDerivative w (fun y => f y * g y)) x i = _
    rw [ih]
    exact Commutator.classicalWordProductExpansion_firstDerivative w f g hf hg i x

/-- The order-s transport commutator is precisely the Leibniz sum over splits that differentiate
the drift at least once. -/
theorem classicalWordDerivative_mul_commutator (w : List (Fin 2))
    (f g : Vec 2 → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    classicalWordDerivative w (fun x => f x * g x) =
      fun x => f x * classicalWordDerivative w g x +
        classicalWordCommutatorExpansion w f g x := by
  induction w generalizing f g with
  | nil =>
    funext x
    simp [classicalWordDerivative, classicalWordCommutatorExpansion,
      classicalWordCommutatorSplits]
  | cons i w ih =>
    have hDg : ContDiff ℝ (⊤ : ℕ∞) (classicalWordDerivative w g) :=
      classicalWordDerivative_contDiff w g hg
    have hA : ContDiff ℝ (⊤ : ℕ∞)
        (fun y => f y * classicalWordDerivative w g y) := hf.mul hDg
    have hC : ContDiff ℝ (⊤ : ℕ∞) (classicalWordCommutatorExpansion w f g) :=
      Commutator.classicalWordCommutatorExpansion_contDiff w f g hf hg
    have hIH := ih f g hf hg
    funext x
    change AVenhance.spaceGrad
        (classicalWordDerivative w (fun y => f y * g y)) x i = _
    rw [hIH]
    rw [classicalSpaceGrad_add _ _ hA hC i x]
    rw [classicalProduct_firstDerivative f (classicalWordDerivative w g) hf hDg i x]
    rw [Commutator.classicalWordCommutatorExpansion_firstDerivative w f g hf hg i x]
    rw [Commutator.classicalWordCommutatorExpansion_cons w f g hf hg i x]
    have hdf : ContDiff ℝ (⊤ : ℕ∞) (fun y => AVenhance.spaceGrad f y i) :=
      Commutator.classicalSpaceGrad_contDiff f hf i
    have hprod := classicalWordDerivative_mul w
      (fun y => AVenhance.spaceGrad f y i) g hdf hg
    have hIH' := ih (fun y => AVenhance.spaceGrad f y i) g hdf hg
    have hsplit (x : Vec 2) :
        classicalWordProductExpansion w (fun y => AVenhance.spaceGrad f y i) g x =
          AVenhance.spaceGrad f x i * classicalWordDerivative w g x +
            classicalWordCommutatorExpansion w
              (fun y => AVenhance.spaceGrad f y i) g x := by
      calc
        _ = classicalWordDerivative w
            (fun y => AVenhance.spaceGrad f y i * g y) x := (congrFun hprod x).symm
        _ = _ := congrFun hIH' x
    rw [hsplit]
    rw [← Commutator.classicalWordCommutatorExpansion_left_derivative w f g hf i x,
      ← Commutator.classicalWordCommutatorExpansion_right_derivative w f g hg i x]
    simp only [classicalWordDerivative]
    ring

theorem Commutator.classicalWordDerivative_product_commutator_eq
    (w : List (Fin 2)) (f g : Vec 2 → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (x : Vec 2) :
    classicalWordProductExpansion w f g x -
        f x * classicalWordDerivative w g x =
      classicalWordCommutatorExpansion w f g x := by
  have hprod := congrFun (classicalWordDerivative_mul w f g hf hg) x
  have hcomm := congrFun (classicalWordDerivative_mul_commutator w f g hf hg) x
  rw [← hprod]
  linarith

theorem Commutator.classicalList_abs_sum_le (L : List ℝ) :
    |L.sum| ≤ (L.map fun a => |a|).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.sum_cons, List.map_cons]
    calc
      |a + L.sum| ≤ |a| + |L.sum| := abs_add_le _ _
      _ ≤ |a| + (List.map (fun a => |a|) L).sum := by nlinarith [ih]

theorem Commutator.classicalWordCommutatorExpansion_abs_le
    (w : List (Fin 2)) (f g : Vec 2 → ℝ) (x : Vec 2) :
    |classicalWordCommutatorExpansion w f g x| ≤
      ((classicalWordCommutatorSplits w).map fun p =>
        |classicalWordProductTerm p f g x|).sum := by
  unfold classicalWordCommutatorExpansion
  rw [Commutator.classicalListSum_eval]
  have h := Commutator.classicalList_abs_sum_le
    (List.map (fun F => F x)
      ((classicalWordCommutatorSplits w).map fun p => classicalWordProductTerm p f g))
  simpa only [List.map_map, Function.comp_def] using h

theorem Commutator.classicalWordDerivative_finSum (w : List (Fin 2))
    (f : Fin 2 → Vec 2 → ℝ) (hf : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (f j)) :
    classicalWordDerivative w (fun x => ∑ j : Fin 2, f j x) =
      fun x => ∑ j : Fin 2, classicalWordDerivative w (f j) x := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    funext x
    change AVenhance.spaceGrad
        (classicalWordDerivative w (fun y => ∑ j : Fin 2, f j y)) x i = _
    rw [ih]
    change fderiv ℝ (fun y => ∑ j : Fin 2, classicalWordDerivative w (f j) y)
      x (Homogenization.basisVec i) = _
    rw [fderiv_fun_sum (u := Finset.univ)
      (A := fun j : Fin 2 => classicalWordDerivative w (f j)) (by
        intro j hj
        exact (classicalWordDerivative_contDiff w (f j) (hf j)).differentiable
          (by simp) x)]
    rw [sum_apply]
    simp only [classicalWordDerivative, AVenhance.spaceGrad]

theorem Commutator.classicalTransport_eq_finSum (b : Vec 2 → Vec 2) (u : Vec 2 → ℝ) :
    classicalTransport b u = fun x => ∑ j : Fin 2,
      b x j * AVenhance.spaceGrad u x j := by
  funext x
  simp [classicalTransport, Homogenization.vecDot]

/-- Arbitrary ordered derivatives of the transport term are given by the finite Leibniz sum over
the drift components and all derivative splits. -/
theorem classicalWordDerivative_transport (w : List (Fin 2))
    (b : Vec 2 → Vec 2) (u : Vec 2 → ℝ)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
    classicalWordDerivative w (classicalTransport b u) =
      fun x => ∑ j : Fin 2,
        classicalWordProductExpansion w (fun y => b y j)
          (fun y => AVenhance.spaceGrad u y j) x := by
  rw [Commutator.classicalTransport_eq_finSum]
  rw [Commutator.classicalWordDerivative_finSum w
    (fun j y => b y j * AVenhance.spaceGrad u y j) (by
      intro j
      exact ((contDiff_pi.1 hb) j).mul (Commutator.classicalSpaceGrad_contDiff u hu j))]
  funext x
  apply Finset.sum_congr rfl
  intro j hj
  exact congrFun
    (classicalWordDerivative_mul w (fun y => b y j)
      (fun y => AVenhance.spaceGrad u y j)
      ((contDiff_pi.1 hb) j) (Commutator.classicalSpaceGrad_contDiff u hu j)) x

/-- The arbitrary order transport commutator is the sum of exactly the Leibniz terms in which a
derivative lands on the drift, written as the full product expansion with its principal term
removed componentwise. -/
theorem classicalWordDerivative_transport_commutator
    (w : List (Fin 2)) (b : Vec 2 → Vec 2) (u : Vec 2 → ℝ)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hu : ContDiff ℝ (⊤ : ℕ∞) u) (x : Vec 2) :
    classicalWordDerivative w (classicalTransport b u) x -
        Homogenization.vecDot (b x)
          (AVenhance.spaceGrad (classicalWordDerivative w u) x) =
      ∑ j : Fin 2,
        (classicalWordProductExpansion w (fun y => b y j)
            (fun y => AVenhance.spaceGrad u y j) x -
          b x j * classicalWordDerivative w
            (fun y => AVenhance.spaceGrad u y j) x) := by
  rw [classicalWordDerivative_transport w b u hb hu]
  have hprincipal : ∀ j : Fin 2,
      classicalWordDerivative w (fun y => AVenhance.spaceGrad u y j) x =
        AVenhance.spaceGrad (classicalWordDerivative w u) x j := by
    intro j
    exact congrFun (classicalWordDerivative_commute_gradient w u hu j) x
  simp only [Homogenization.vecDot]
  simp_rw [hprincipal]
  rw [Finset.sum_sub_distrib]

/-- After cancelling the principal transport derivative, the order-s commutator is the finite
sum of the Leibniz terms that differentiate a drift component. -/
theorem classicalWordDerivative_transport_eq_commutatorExpansion
    (w : List (Fin 2)) (b : Vec 2 → Vec 2) (u : Vec 2 → ℝ)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hu : ContDiff ℝ (⊤ : ℕ∞) u) (x : Vec 2) :
    classicalWordDerivative w (classicalTransport b u) x -
        Homogenization.vecDot (b x)
          (AVenhance.spaceGrad (classicalWordDerivative w u) x) =
      ∑ j : Fin 2,
        classicalWordCommutatorExpansion w (fun y => b y j)
          (fun y => AVenhance.spaceGrad u y j) x := by
  rw [classicalWordDerivative_transport_commutator w b u hb hu x]
  apply Finset.sum_congr rfl
  intro j hj
  exact Commutator.classicalWordDerivative_product_commutator_eq w
    (fun y => b y j) (fun y => AVenhance.spaceGrad u y j)
    ((contDiff_pi.1 hb) j) (Commutator.classicalSpaceGrad_contDiff u hu j) x

theorem Commutator.classicalList_sum_mono {α : Type} (L : List α) (f g : α → ℝ)
    (h : ∀ a ∈ L, f a ≤ g a) : (L.map f).sum ≤ (L.map g).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have htail : ∀ z ∈ L, f z ≤ g z := by
      intro z hz
      exact h z (by simp [hz])
    simp only [List.map_cons, List.sum_cons]
    exact add_le_add (h a (by simp)) (ih htail)

/-- The first derivative commutator between transport and a coordinate derivative is the
product of the differentiated drift and the gradient of the scalar. -/
theorem classicalTransport_firstCommutator
    (b : Vec 2 → Vec 2) (u : Vec 2 → ℝ)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (i : Fin 2) (x : Vec 2) :
    AVenhance.spaceGrad (classicalTransport b u) x i -
        Homogenization.vecDot (b x)
          (AVenhance.spaceGrad (fun y => AVenhance.spaceGrad u y i) x) =
      ∑ j : Fin 2,
        AVenhance.spaceGrad (fun y => b y j) x i * AVenhance.spaceGrad u x j := by
  have hcommute (j : Fin 2) :
      AVenhance.spaceGrad (fun y => AVenhance.spaceGrad u y j) x i =
        AVenhance.spaceGrad (fun y => AVenhance.spaceGrad u y i) x j :=
    classicalSpaceGrad_commute u hu i j x
  have hbcomp (j : Fin 2) : ContDiff ℝ (⊤ : ℕ∞) (fun y => b y j) :=
    (contDiff_pi.1 hb) j
  have hgradcomp (j : Fin 2) :
      ContDiff ℝ (⊤ : ℕ∞) (fun y => AVenhance.spaceGrad u y j) := by
    change ContDiff ℝ (⊤ : ℕ∞)
      (fun y => fderiv ℝ u y (Homogenization.basisVec j))
    exact (hu.fderiv_right (by simp)).clm_apply contDiff_const
  have hterm (j : Fin 2) :
      AVenhance.spaceGrad
          (fun y => b y j * AVenhance.spaceGrad u y j) x i =
        b x j * AVenhance.spaceGrad (fun y => AVenhance.spaceGrad u y j) x i +
          AVenhance.spaceGrad (fun y => b y j) x i * AVenhance.spaceGrad u x j := by
    change fderiv ℝ (fun y => b y j * AVenhance.spaceGrad u y j) x
        (Homogenization.basisVec i) = _
    rw [fderiv_fun_mul
      ((hbcomp j).differentiable (by simp) x)
      ((hgradcomp j).differentiable (by simp) x)]
    simp only [add_apply, smul_apply, AVenhance.spaceGrad]
    ring
  have htransport : classicalTransport b u =
      fun x => ∑ j : Fin 2, b x j * AVenhance.spaceGrad u x j := by
    funext y
    simp [classicalTransport, Homogenization.vecDot, AVenhance.spaceGrad]
  have hderivSum :
      AVenhance.spaceGrad (classicalTransport b u) x i =
        ∑ j : Fin 2,
          AVenhance.spaceGrad (fun y => b y j * AVenhance.spaceGrad u y j) x i := by
    rw [htransport]
    change fderiv ℝ (fun y => ∑ j : Fin 2,
        b y j * AVenhance.spaceGrad u y j) x (Homogenization.basisVec i) = _
    rw [fderiv_fun_sum (u := Finset.univ) (A := fun j : Fin 2 =>
        fun y => b y j * AVenhance.spaceGrad u y j) (by
          intro j hj
          exact ((hbcomp j).differentiable (by simp) x).mul
            ((hgradcomp j).differentiable (by simp) x))]
    rw [sum_apply]
    simp only [AVenhance.spaceGrad]
  rw [hderivSum]
  simp_rw [hterm]
  simp only [Homogenization.vecDot]
  rw [Finset.sum_add_distrib]
  have hcancel :
      (∑ j : Fin 2,
          b x j * AVenhance.spaceGrad (fun y => AVenhance.spaceGrad u y j) x i) =
        (∑ j : Fin 2,
          b x j * AVenhance.spaceGrad (fun y => AVenhance.spaceGrad u y i) x j) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [hcommute]
  rw [hcancel]
  simp [add_sub_cancel_left]

/-- The Leibniz split list has binomial multiplicities for the number of derivatives assigned
to its first factor. -/
theorem classicalWordSplits_leftLength_count (w : List (Fin 2)) (q : ℕ) :
    ((classicalWordSplits w).filter (fun p => p.1.length = q)).length =
      w.length.choose q := by
  induction w generalizing q with
  | nil =>
      cases q <;> simp [classicalWordSplits]
  | cons i w ih =>
      cases q with
      | zero =>
          simpa [classicalWordSplits, List.filter_map, Function.comp_def,
            List.length_eq_zero_iff] using (ih 0)
      | succ q =>
          simp [classicalWordSplits, List.filter_map, Function.comp_def, ih,
            Nat.choose_succ_succ]

/-- The commutator split list has the same binomial multiplicities, with the zero-derivative
on the first factor removed. -/
theorem classicalWordCommutatorSplits_leftLength_count
    (w : List (Fin 2)) (q : ℕ) :
    ((classicalWordCommutatorSplits w).filter
      (fun p => p.1.length = q)).length =
      if q = 0 then 0 else w.length.choose q := by
  induction w generalizing q with
  | nil =>
      cases q <;> simp [classicalWordCommutatorSplits]
  | cons i w ih =>
      cases q with
      | zero =>
          simpa [classicalWordCommutatorSplits, List.filter_map,
            Function.comp_def, List.length_eq_zero_iff] using (ih 0)
      | succ q =>
          simp [classicalWordCommutatorSplits, List.filter_map, Function.comp_def,
            classicalWordSplits_leftLength_count, ih,
            Nat.choose_succ_succ]

end AVenhance.Infra.Classical

end
