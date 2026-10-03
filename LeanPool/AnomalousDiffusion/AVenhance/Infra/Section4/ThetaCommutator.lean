/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.Commutator
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.ThetaEnergy
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FaaDiBruno.Product

/-! First-order transport commutator identities for smooth Euclidean fields. -/

@[expose] public section

noncomputable section

open Homogenization

namespace AVenhance.Infra.Section4

/-- The scalar transport term associated with a vector field and a scalar function. -/
def classicalTransport (b : Vec 2 → Vec 2) (u : Vec 2 → ℝ) (x : Vec 2) : ℝ :=
  Classical.classicalTransport b u x

/-- Coordinate derivative of a product of two smooth scalar functions. -/
theorem classicalProduct_firstDerivative (f g : Vec 2 → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (i : Fin 2) (x : Vec 2) :
    AVenhance.spaceGrad (fun y => f y * g y) x i =
      f x * AVenhance.spaceGrad g x i + AVenhance.spaceGrad f x i * g x := by
  exact Classical.classicalProduct_firstDerivative
    f g hf hg i x

/-- Coordinate derivative commutes with subtraction for smooth scalar functions. -/
theorem classicalSpaceGrad_sub (f g : Vec 2 → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (i : Fin 2) (x : Vec 2) :
    AVenhance.spaceGrad (fun y => f y - g y) x i =
      AVenhance.spaceGrad f x i - AVenhance.spaceGrad g x i := by
  exact Classical.classicalSpaceGrad_sub
    f g hf hg i x

theorem ThetaCommutator.classicalSpaceGrad_contDiff (f : Vec 2 → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => AVenhance.spaceGrad f x i) := by
  exact Classical.Commutator.classicalSpaceGrad_contDiff
    f hf i

theorem ThetaCommutator.classicalTransport_contDiff (b : Vec 2 → Vec 2) (u : Vec 2 → ℝ)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
    ContDiff ℝ (⊤ : ℕ∞) (classicalTransport b u) := by
  exact Classical.Commutator.classicalTransport_contDiff
    b u hb hu

/-- An ordered word of coordinate derivatives applied to a scalar function. -/
def classicalWordDerivative : List (Fin 2) → (Vec 2 → ℝ) → Vec 2 → ℝ :=
  Classical.classicalWordDerivative

theorem classicalWordDerivative_contDiff (w : List (Fin 2)) (f : Vec 2 → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (classicalWordDerivative w f) := by
  exact Classical.classicalWordDerivative_contDiff
    w f hf

/-- Coordinate directions of a spatial derivative word indexed by its length. -/
def ThetaCommutator.thetaWordDirections (w : List (Fin 2)) : Fin w.length → Fin 2 :=
  fun j => w.get j

/-- The ordered-word convention agrees with iterated Fréchet differentiation
on the corresponding ordered coordinate directions. -/
theorem thetaWordDerivative_eq_iteratedFDeriv (w : List (Fin 2))
    (f : Vec 2 → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : Vec 2) :
    classicalWordDerivative w f x =
      iteratedFDeriv ℝ w.length f x
        (fun j => Homogenization.basisVec (ThetaCommutator.thetaWordDirections w j)) := by
  induction w generalizing f hf x with
  | nil =>
      simp [classicalWordDerivative, Classical.classicalWordDerivative,
        ThetaCommutator.thetaWordDirections]
  | cons i w ih =>
      have hcont : ContDiff ℝ (w.length + 1) f := hf.of_le (by simp)
      have hn : (w.length : ℕ∞) < (w.length : ℕ∞) + 1 :=
        (ENat.lt_add_one_iff (by simp)).2 le_rfl
      have hn' : (w.length : WithTop ℕ∞) < (w.length : WithTop ℕ∞) + 1 := by
        simpa using (WithTop.coe_lt_coe.mpr hn)
      have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ w.length f) x :=
        (hcont.differentiable_iteratedFDeriv hn') x
      let I : Fin (w.length + 1) → Fin 2 := fun j => (i :: w).get j
      have hIzero : I 0 = i := by simp [I]
      have hIsucc (j : Fin w.length) : I j.succ = ThetaCommutator.thetaWordDirections w j := by
        simp [I, ThetaCommutator.thetaWordDirections]
      have htailFun : classicalWordDerivative w f =
          (fun y => iteratedFDeriv ℝ w.length f y
            (fun j => Homogenization.basisVec (ThetaCommutator.thetaWordDirections w j))) := by
        funext y
        exact ih f hf y
      have htailDirs :
          (fun j : Fin w.length => Homogenization.basisVec
            (ThetaCommutator.thetaWordDirections w j)) =
          (fun j => Homogenization.basisVec (I j.succ)) := by
        funext j
        rw [hIsucc]
      have hstep := AVenhance.Infra.Section4.ordered_derivative_eq_gradient_component
        (i := I) hdiff
      have hstep' := hstep
      rw [hIzero] at hstep'
      calc
        classicalWordDerivative (i :: w) f x =
            AVenhance.spaceGrad (classicalWordDerivative w f) x i := rfl
        _ = AVenhance.spaceGrad
            (fun y => iteratedFDeriv ℝ w.length f y
              (fun j => Homogenization.basisVec (ThetaCommutator.thetaWordDirections w j))) x i :=
                  by
              rw [htailFun]
        _ = iteratedFDeriv ℝ (w.length + 1) f x
            (fun j => Homogenization.basisVec (I j)) := by
              rw [htailDirs]
              exact hstep'.symm
        _ = iteratedFDeriv ℝ (List.length (i :: w)) f x
            (fun j => Homogenization.basisVec
              (ThetaCommutator.thetaWordDirections (i :: w) j)) := by
              simp [ThetaCommutator.thetaWordDirections, I]

/-- The ordered derivative identification with the tuple written using
`List.get`, for hypotheses quantified over all coordinate tuples. -/
theorem thetaWordDerivative_eq_iteratedFDeriv_get (w : List (Fin 2))
    (f : Vec 2 → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : Vec 2) :
    classicalWordDerivative w f x =
      iteratedFDeriv ℝ w.length f x
        (fun j => Homogenization.basisVec (w.get j)) := by
  calc
    _ = iteratedFDeriv ℝ w.length f x
        (fun j => Homogenization.basisVec (ThetaCommutator.thetaWordDirections w j)) :=
      thetaWordDerivative_eq_iteratedFDeriv w f hf x
    _ = iteratedFDeriv ℝ w.length f x
        (fun j => Homogenization.basisVec (w.get j)) := by
      congr 1

/-- Negation passes through an ordered word of spatial derivatives. -/
theorem classicalWordDerivative_neg (w : List (Fin 2)) (f : Vec 2 → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    classicalWordDerivative w (fun x => -f x) =
      fun x => -classicalWordDerivative w f x := by
  induction w with
  | nil => rfl
  | cons i w ih =>
      have htail := classicalWordDerivative_contDiff w f hf
      funext x
      change AVenhance.spaceGrad
          (classicalWordDerivative w (fun y => -f y)) x i =
        -AVenhance.spaceGrad (classicalWordDerivative w f) x i
      rw [ih]
      have h := classicalSpaceGrad_sub (fun _ : Vec 2 => (0 : ℝ))
        (classicalWordDerivative w f) contDiff_const htail i x
      simp [AVenhance.spaceGrad]

/-- Coordinate bounds for all order-`n` Fréchet derivatives immediately give
the same bound for each ordered coordinate word. -/
theorem classicalWordDerivative_abs_le_of_iteratedFDeriv
    (w : List (Fin 2)) (f : Vec 2 → ℝ) (B : ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hbound : ∀ i : Fin w.length → Fin 2, ∀ x : Vec 2,
      ‖iteratedFDeriv ℝ w.length f x
        (fun j => Homogenization.basisVec (i j))‖ ≤ B) :
    ∀ x : Vec 2, |classicalWordDerivative w f x| ≤ B := by
  intro x
  rw [thetaWordDerivative_eq_iteratedFDeriv w f hf x]
  simpa [Real.norm_eq_abs] using hbound (ThetaCommutator.thetaWordDirections w) x

/-- Smooth mixed coordinate derivatives commute. -/
theorem classicalSpaceGrad_commute (f : Vec 2 → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i j : Fin 2) (x : Vec 2) :
    AVenhance.spaceGrad (fun y => AVenhance.spaceGrad f y j) x i =
      AVenhance.spaceGrad (fun y => AVenhance.spaceGrad f y i) x j := by
  exact Classical.classicalSpaceGrad_commute
    f hf i j x

/-- Smooth ordered coordinate derivatives depend only on the multiset of
directions.  This lets a one-derivative Leibniz split be identified with one
coordinate of the gradient of the complementary word. -/
theorem classicalWordDerivative_eq_of_perm (w v : List (Fin 2))
    (f : Vec 2 → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (h : w.Perm v) :
    classicalWordDerivative w f = classicalWordDerivative v f := by
  induction h with
  | nil => rfl
  | @cons i w v h ih =>
      funext x
      change AVenhance.spaceGrad (classicalWordDerivative w f) x i =
        AVenhance.spaceGrad (classicalWordDerivative v f) x i
      rw [ih]
  | swap i j w =>
      funext x
      change AVenhance.spaceGrad
          (fun y => AVenhance.spaceGrad (classicalWordDerivative w f) y i) x j =
        AVenhance.spaceGrad
          (fun y => AVenhance.spaceGrad (classicalWordDerivative w f) y j) x i
      exact classicalSpaceGrad_commute (classicalWordDerivative w f)
        (classicalWordDerivative_contDiff w f hf) j i x
  | @trans w v z h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

/-- A coordinate derivative can be moved through an arbitrary ordered word of smooth coordinate
derivatives. -/
theorem classicalWordDerivative_commute_gradient (w : List (Fin 2)) (f : Vec 2 → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (j : Fin 2) :
    classicalWordDerivative w (fun y => AVenhance.spaceGrad f y j) =
      fun x => AVenhance.spaceGrad (classicalWordDerivative w f) x j := by
  exact Classical.classicalWordDerivative_commute_gradient
    w f hf j

/-- Coordinate derivative of a sum of smooth scalar functions. -/
theorem classicalSpaceGrad_add (f g : Vec 2 → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (i : Fin 2) (x : Vec 2) :
    AVenhance.spaceGrad (fun y => f y + g y) x i =
      AVenhance.spaceGrad f x i + AVenhance.spaceGrad g x i := by
  exact Classical.classicalSpaceGrad_add
    f g hf hg i x

theorem classicalContDiff_listSum (L : List (Vec 2 → ℝ))
    (hL : ∀ f ∈ L, ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) L.sum := by
  exact Classical.Commutator.classicalContDiff_listSum
    L hL

theorem classicalSpaceGrad_listSum (L : List (Vec 2 → ℝ))
    (hL : ∀ f ∈ L, ContDiff ℝ (⊤ : ℕ∞) f) (i : Fin 2) (x : Vec 2) :
    AVenhance.spaceGrad L.sum x i = (L.map fun f => AVenhance.spaceGrad f x i).sum := by
  exact Classical.Commutator.classicalSpaceGrad_listSum
    L hL i x

/-- All ways of distributing an ordered derivative word between two factors. -/
def classicalWordSplits : List (Fin 2) → List (List (Fin 2) × List (Fin 2)) :=
  Classical.classicalWordSplits

/-- The product term attached to one split of a derivative word. -/
def classicalWordProductTerm (p : List (Fin 2) × List (Fin 2))
    (f g : Vec 2 → ℝ) : Vec 2 → ℝ :=
  Classical.classicalWordProductTerm p f g

/-- Leibniz expansion of an ordered word of coordinate derivatives. -/
def classicalWordProductExpansion (w : List (Fin 2)) (f g : Vec 2 → ℝ) : Vec 2 → ℝ :=
  Classical.classicalWordProductExpansion w f g

/-- The derivative splits with at least one derivative assigned to the first factor. -/
def classicalWordCommutatorSplits : List (Fin 2) →
    List (List (Fin 2) × List (Fin 2)) :=
  Classical.classicalWordCommutatorSplits

theorem ThetaCommutator.classicalPerm_move_head (i : Fin 2) (u v : List (Fin 2)) :
    (i :: u ++ v).Perm (u ++ i :: v) := by
  induction u with
  | nil => simp
  | cons j u ih =>
      exact (List.Perm.swap j i (u ++ v)).trans (List.Perm.cons j ih)

/-- Every Leibniz split preserves the complete ordered derivative word up to
permutation. -/
theorem classicalWordSplits_perm_append (w : List (Fin 2))
    {p : List (Fin 2) × List (Fin 2)} (hp : p ∈ classicalWordSplits w) :
    w.Perm (p.1 ++ p.2) := by
  induction w generalizing p with
  | nil =>
      simp only [classicalWordSplits, Classical.classicalWordSplits, List.mem_singleton] at hp
      subst p
      exact List.Perm.nil
  | cons i w ih =>
      simp only [classicalWordSplits, Classical.classicalWordSplits, List.mem_append] at hp
      rcases hp with hp | hp
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
        have h := ih hq
        simpa using List.Perm.cons i h
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
        have h := ih hq
        have hc := List.Perm.cons i h
        exact hc.trans (ThetaCommutator.classicalPerm_move_head i q.1 q.2)

/-- The same shuffle invariant holds after the zero-derivative-on-drift term
is removed from the transport commutator. -/
theorem classicalWordCommutatorSplits_perm_append (w : List (Fin 2))
    {p : List (Fin 2) × List (Fin 2)}
    (hp : p ∈ classicalWordCommutatorSplits w) :
    w.Perm (p.1 ++ p.2) := by
  induction w generalizing p with
  | nil => simp [classicalWordCommutatorSplits, Classical.classicalWordCommutatorSplits] at hp
  | cons i w ih =>
      simp only [classicalWordCommutatorSplits, Classical.classicalWordCommutatorSplits,
        List.mem_append] at hp
      rcases hp with hp | hp
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
        exact (classicalWordSplits_perm_append w hq).cons i
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
        have h := ih hq
        exact (List.Perm.cons i h).trans (ThetaCommutator.classicalPerm_move_head i q.1 q.2)

/-- The order-`n` derivative in a split with one derivative on the stream
potential is itself a coordinate of the gradient of the complementary
order-`n-1` derivative. -/
theorem classicalWordDerivative_sq_le_gradient_of_perm
    (w v : List (Fin 2)) (i : Fin 2) (f : Vec 2 → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : Vec 2)
    (hperm : w.Perm (i :: v)) :
    (classicalWordDerivative w f x) ^ 2 ≤
      Homogenization.vecNormSq
        (AVenhance.spaceGrad (classicalWordDerivative v f) x) := by
  rw [classicalWordDerivative_eq_of_perm w (i :: v) f hf hperm]
  exact Homogenization.sq_apply_le_vecNormSq
    (AVenhance.spaceGrad (classicalWordDerivative v f) x) i

/-- Specialization of the coordinate estimate to a commutator split with one
derivative on its first factor. -/
theorem classicalWordDerivative_sq_le_gradient_of_first_order_split
    (w : List (Fin 2)) (p : List (Fin 2) × List (Fin 2))
    (f : Vec 2 → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : Vec 2)
    (hp : p ∈ classicalWordCommutatorSplits w)
    (hq : p.1.length = 1) :
    classicalWordDerivative w f x ^ 2 ≤
      Homogenization.vecNormSq
        (AVenhance.spaceGrad (classicalWordDerivative p.2 f) x) := by
  rcases p with ⟨left, right⟩
  cases left with
  | nil => simp at hq
  | cons i left =>
      cases left with
      | nil =>
          have hperm := classicalWordCommutatorSplits_perm_append w hp
          have hperm' : w.Perm (i :: right) := by simpa using hperm
          exact classicalWordDerivative_sq_le_gradient_of_perm
            w right i f hf x hperm'
      | cons j rest => simp at hq

/-- The full Leibniz split list contains `choose n q` occurrences with exactly
`q` derivatives on its first factor, including multiplicities for repeated
coordinate directions. -/
theorem classicalWordSplits_leftLength_count (w : List (Fin 2)) (q : ℕ) :
    ((classicalWordSplits w).filter (fun p => p.1.length = q)).length =
      w.length.choose q := by
  exact Classical.classicalWordSplits_leftLength_count
    w q

/-- The transport commutator split list has the same binomial multiplicities,
with the zero-derivative-on-drift split removed. -/
theorem classicalWordCommutatorSplits_leftLength_count
    (w : List (Fin 2)) (q : ℕ) :
    ((classicalWordCommutatorSplits w).filter
      (fun p => p.1.length = q)).length =
      if q = 0 then 0 else w.length.choose q := by
  exact Classical.classicalWordCommutatorSplits_leftLength_count
    w q

theorem classicalWordSplits_length (w : List (Fin 2))
    {p : List (Fin 2) × List (Fin 2)} (hp : p ∈ classicalWordSplits w) :
    p.1.length + p.2.length = w.length := by
  exact Classical.classicalWordSplits_length
    w hp

theorem classicalWordCommutatorSplits_length (w : List (Fin 2))
    {p : List (Fin 2) × List (Fin 2)} (hp : p ∈ classicalWordCommutatorSplits w) :
    p.1.length + p.2.length = w.length := by
  exact Classical.classicalWordCommutatorSplits_length
    w hp

theorem classicalWordCommutatorSplits_left_ne_nil (w : List (Fin 2))
    {p : List (Fin 2) × List (Fin 2)} (hp : p ∈ classicalWordCommutatorSplits w) :
    p.1 ≠ [] := by
  exact Classical.classicalWordCommutatorSplits_left_ne_nil
    w hp

theorem classicalWordCommutatorSplits_right_length_lt (w : List (Fin 2))
    {p : List (Fin 2) × List (Fin 2)} (hp : p ∈ classicalWordCommutatorSplits w) :
    p.2.length < w.length := by
  exact Classical.classicalWordCommutatorSplits_right_length_lt
    w hp

/-- The finite Leibniz sum over splits with a nonempty first derivative word. -/
def classicalWordCommutatorExpansion (w : List (Fin 2))
    (f g : Vec 2 → ℝ) : Vec 2 → ℝ :=
  Classical.classicalWordCommutatorExpansion w f g

theorem classicalListSum_eval (L : List (Vec 2 → ℝ)) (x : Vec 2) :
    L.sum x = (L.map fun f => f x).sum := by
  exact Classical.Commutator.classicalListSum_eval
    L x

theorem ThetaCommutator.classicalListSum_map_add {α : Type} (L : List α) (f g : α → ℝ) :
    (L.map fun a => f a + g a).sum = (L.map f).sum + (L.map g).sum := by
  exact Classical.Commutator.classicalListSum_map_add
    L f g

theorem ThetaCommutator.classicalWordProductTerm_contDiff (p : List (Fin 2) × List (Fin 2))
    (f g : Vec 2 → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    ContDiff ℝ (⊤ : ℕ∞) (classicalWordProductTerm p f g) := by
  exact Classical.Commutator.classicalWordProductTerm_contDiff
    p f g hf hg

theorem ThetaCommutator.classicalWordProductTerm_firstDerivative
    (p : List (Fin 2) × List (Fin 2)) (f g : Vec 2 → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (i : Fin 2) (x : Vec 2) :
    AVenhance.spaceGrad (classicalWordProductTerm p f g) x i =
      classicalWordProductTerm (i :: p.1, p.2) f g x +
        classicalWordProductTerm (p.1, i :: p.2) f g x := by
  exact Classical.Commutator.classicalWordProductTerm_firstDerivative
    p f g hf hg i x

theorem classicalWordCommutatorExpansion_firstDerivative
    (w : List (Fin 2)) (f g : Vec 2 → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (i : Fin 2) (x : Vec 2) :
    AVenhance.spaceGrad (classicalWordCommutatorExpansion w f g) x i =
      ((classicalWordCommutatorSplits w).map fun p =>
        classicalWordProductTerm (i :: p.1, p.2) f g x).sum +
      ((classicalWordCommutatorSplits w).map fun p =>
        classicalWordProductTerm (p.1, i :: p.2) f g x).sum := by
  exact Classical.Commutator.classicalWordCommutatorExpansion_firstDerivative
    w f g hf hg i x

theorem ThetaCommutator.classicalWordProductTerm_left_derivative
    (p : List (Fin 2) × List (Fin 2)) (f g : Vec 2 → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : Fin 2) (x : Vec 2) :
    classicalWordProductTerm p (fun y => AVenhance.spaceGrad f y i) g x =
      classicalWordProductTerm (i :: p.1, p.2) f g x := by
  exact Classical.Commutator.classicalWordProductTerm_left_derivative
    p f g hf i x

theorem ThetaCommutator.classicalWordProductTerm_right_derivative
    (p : List (Fin 2) × List (Fin 2)) (f g : Vec 2 → ℝ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (i : Fin 2) (x : Vec 2) :
    classicalWordProductTerm p f (fun y => AVenhance.spaceGrad g y i) x =
      classicalWordProductTerm (p.1, i :: p.2) f g x := by
  exact Classical.Commutator.classicalWordProductTerm_right_derivative
    p f g hg i x

theorem ThetaCommutator.classicalWordProductExpansion_left_derivative
    (w : List (Fin 2)) (f g : Vec 2 → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : Fin 2) (x : Vec 2) :
    classicalWordProductExpansion w (fun y => AVenhance.spaceGrad f y i) g x =
      ((classicalWordSplits w).map fun p =>
        classicalWordProductTerm (i :: p.1, p.2) f g x).sum := by
  exact Classical.Commutator.classicalWordProductExpansion_left_derivative
    w f g hf i x

theorem ThetaCommutator.classicalWordCommutatorExpansion_left_derivative
    (w : List (Fin 2)) (f g : Vec 2 → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : Fin 2) (x : Vec 2) :
    classicalWordCommutatorExpansion w (fun y => AVenhance.spaceGrad f y i) g x =
      ((classicalWordCommutatorSplits w).map fun p =>
        classicalWordProductTerm (i :: p.1, p.2) f g x).sum := by
  exact Classical.Commutator.classicalWordCommutatorExpansion_left_derivative
    w f g hf i x

theorem classicalWordCommutatorExpansion_right_derivative
    (w : List (Fin 2)) (f g : Vec 2 → ℝ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (i : Fin 2) (x : Vec 2) :
    classicalWordCommutatorExpansion w f (fun y => AVenhance.spaceGrad g y i) x =
      ((classicalWordCommutatorSplits w).map fun p =>
        classicalWordProductTerm (p.1, i :: p.2) f g x).sum := by
  exact Classical.Commutator.classicalWordCommutatorExpansion_right_derivative
    w f g hg i x

theorem ThetaCommutator.classicalWordCommutatorExpansion_cons
    (w : List (Fin 2)) (f g : Vec 2 → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (i : Fin 2) (x : Vec 2) :
    classicalWordCommutatorExpansion (i :: w) f g x =
    classicalWordProductExpansion w (fun y => AVenhance.spaceGrad f y i) g x +
      classicalWordCommutatorExpansion w f (fun y => AVenhance.spaceGrad g y i) x := by
  exact Classical.Commutator.classicalWordCommutatorExpansion_cons
    w f g hf hg i x

theorem classicalWordCommutatorExpansion_contDiff
    (w : List (Fin 2)) (f g : Vec 2 → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    ContDiff ℝ (⊤ : ℕ∞) (classicalWordCommutatorExpansion w f g) := by
  exact Classical.Commutator.classicalWordCommutatorExpansion_contDiff
    w f g hf hg

theorem ThetaCommutator.classicalWordProductExpansion_firstDerivative (w : List (Fin 2))
    (f g : Vec 2 → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (i : Fin 2) (x : Vec 2) :
    AVenhance.spaceGrad (classicalWordProductExpansion w f g) x i =
      classicalWordProductExpansion (i :: w) f g x := by
  exact Classical.Commutator.classicalWordProductExpansion_firstDerivative
    w f g hf hg i x

/-- An arbitrary ordered coordinate derivative of a product is the finite Leibniz sum over all
ways to distribute its derivative word between the factors. -/
theorem classicalWordDerivative_mul (w : List (Fin 2)) (f g : Vec 2 → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    classicalWordDerivative w (fun x => f x * g x) =
      classicalWordProductExpansion w f g := by
  exact Classical.classicalWordDerivative_mul
    w f g hf hg

/-- The order-s transport commutator is precisely the Leibniz sum over splits that differentiate
the drift at least once. -/
theorem classicalWordDerivative_mul_commutator (w : List (Fin 2))
    (f g : Vec 2 → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    classicalWordDerivative w (fun x => f x * g x) =
      fun x => f x * classicalWordDerivative w g x +
        classicalWordCommutatorExpansion w f g x := by
  exact Classical.classicalWordDerivative_mul_commutator
    w f g hf hg

theorem ThetaCommutator.classicalWordDerivative_product_commutator_eq
    (w : List (Fin 2)) (f g : Vec 2 → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (x : Vec 2) :
    classicalWordProductExpansion w f g x -
        f x * classicalWordDerivative w g x =
      classicalWordCommutatorExpansion w f g x := by
  exact Classical.Commutator.classicalWordDerivative_product_commutator_eq
    w f g hf hg x

theorem ThetaCommutator.classicalList_abs_sum_le (L : List ℝ) :
    |L.sum| ≤ (L.map fun a => |a|).sum := by
  exact Classical.Commutator.classicalList_abs_sum_le
    L

theorem ThetaCommutator.classicalWordCommutatorExpansion_abs_le
    (w : List (Fin 2)) (f g : Vec 2 → ℝ) (x : Vec 2) :
    |classicalWordCommutatorExpansion w f g x| ≤
      ((classicalWordCommutatorSplits w).map fun p =>
        |classicalWordProductTerm p f g x|).sum := by
  exact Classical.Commutator.classicalWordCommutatorExpansion_abs_le
    w f g x

theorem ThetaCommutator.classicalWordDerivative_finSum (w : List (Fin 2))
    (f : Fin 2 → Vec 2 → ℝ) (hf : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (f j)) :
    classicalWordDerivative w (fun x => ∑ j : Fin 2, f j x) =
      fun x => ∑ j : Fin 2, classicalWordDerivative w (f j) x := by
  exact Classical.Commutator.classicalWordDerivative_finSum
    w f hf

theorem ThetaCommutator.classicalTransport_eq_finSum (b : Vec 2 → Vec 2) (u : Vec 2 → ℝ) :
    classicalTransport b u = fun x => ∑ j : Fin 2,
      b x j * AVenhance.spaceGrad u x j := by
  exact Classical.Commutator.classicalTransport_eq_finSum
    b u

/-- Arbitrary ordered derivatives of the transport term are given by the finite Leibniz sum over
the drift components and all derivative splits. -/
theorem classicalWordDerivative_transport (w : List (Fin 2))
    (b : Vec 2 → Vec 2) (u : Vec 2 → ℝ)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
    classicalWordDerivative w (classicalTransport b u) =
      fun x => ∑ j : Fin 2,
        classicalWordProductExpansion w (fun y => b y j)
          (fun y => AVenhance.spaceGrad u y j) x := by
  exact Classical.classicalWordDerivative_transport
    w b u hb hu

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
  exact Classical.classicalWordDerivative_transport_commutator
    w b u hb hu x

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
  exact Classical.classicalWordDerivative_transport_eq_commutatorExpansion
    w b u hb hu x

theorem ThetaCommutator.classicalList_sum_mono {α : Type} (L : List α) (f g : α → ℝ)
    (h : ∀ a ∈ L, f a ≤ g a) : (L.map f).sum ≤ (L.map g).sum := by
  exact Classical.Commutator.classicalList_sum_mono
    L f g h

end AVenhance.Infra.Section4
