/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Comparison.MatrixInequalities
public import LeanPool.ViscositySolutionTheory.ViscositySolns.Comparison.Semiconvex

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Product-coordinate consequences of the semiconvex matrix lemma (Embeddings)

Part of the product-coordinate development connecting the semiconvex matrix
conclusion on the coordinate space `R^(n+n)` to the block-matrix notation on
`R^n × R^n`. Split from `ProductCoordinates.lean`; see the umbrella module
docstring.
-/

@[expose] public noncomputable section

open scoped MatrixOrder
open Filter

namespace ViscositySolns

variable {n : Nat}

/--
A local maximum on a set is a maximum on a smaller relative neighborhood.

In quantified mathematical form, if `a ∈ S` and `a` is a local maximum point
of `f` relative to `S`, then there is a set `P` such that `P` is a
neighborhood of `a` relative to `S`, `a ∈ P`, `P ⊆ S`, and `a` is a maximum
point of `f` on `P`.
-/
theorem exists_isMaxOn_mem_nhdsWithin_of_isLocalMaxOn
    {α β : Type*} [TopologicalSpace α] [Preorder β]
    {f : α -> β} {S : Set α} {a : α}
    (ha : a ∈ S) (hlocal : IsLocalMaxOn f S a) :
    ∃ P : Set α, P ∈ nhdsWithin a S ∧ a ∈ P ∧ P ⊆ S ∧ IsMaxOn f P a := by
  let E : Set α := {x | f x <= f a}
  have hE : E ∈ nhdsWithin a S := hlocal
  let P : Set α := S ∩ E
  refine ⟨P, Filter.inter_mem self_mem_nhdsWithin hE, ?_, ?_, ?_⟩
  · exact ⟨ha, le_rfl⟩
  · exact Set.inter_subset_left
  · intro x hx
    exact hx.2

/--
View a function on `R^n × R^n` as a function on the coordinate space
`R^(n+n)`.
-/
def blockFunctionToPointFunction (F : BlockPoint n -> Real) : Point (n + n) -> Real :=
  fun z => F (pointSumEquivBlockPoint n z)

/--
The coordinate map from `R^(n+n)` to `R^n × R^n` is continuous.
-/
theorem continuous_pointSumEquivBlockPoint :
    Continuous (pointSumEquivBlockPoint n) := by
  continuity

/-- The point `(x, 0)` in the product coordinate space `R^n × R^n`. -/
def leftBlockPoint (x : Point n) : BlockPoint n :=
  Sum.elim x 0

/-- The point `(0, y)` in the product coordinate space `R^n × R^n`. -/
def rightBlockPoint (y : Point n) : BlockPoint n :=
  Sum.elim 0 y

/-- The point `(x, 0)`, written in `R^(n+n)` coordinates. -/
def leftPointEmbedding (x : Point n) : Point (n + n) :=
  (pointSumEquivBlockPoint n).symm (leftBlockPoint x)

/-- The point `(0, y)`, written in `R^(n+n)` coordinates. -/
def rightPointEmbedding (y : Point n) : Point (n + n) :=
  (pointSumEquivBlockPoint n).symm (rightBlockPoint y)

/-- The left `R^n` coordinate of a point of `R^(n+n) = R^n × R^n`. -/
def pointLeft (z : Point (n + n)) : Point n :=
  blockPointLeft (pointSumEquivBlockPoint n z)

/-- The right `R^n` coordinate of a point of `R^(n+n) = R^n × R^n`. -/
def pointRight (z : Point (n + n)) : Point n :=
  blockPointRight (pointSumEquivBlockPoint n z)

/--
The point obtained from `z = (x0, y0)` by replacing its left coordinate with
`x`, giving `(x, y0)`.
-/
def pointWithLeft (z : Point (n + n)) (x : Point n) : Point (n + n) :=
  (pointSumEquivBlockPoint n).symm (Sum.elim x (pointRight (n := n) z))

/--
The point obtained from `z = (x0, y0)` by replacing its right coordinate with
`y`, giving `(x0, y)`.
-/
def pointWithRight (z : Point (n + n)) (y : Point n) : Point (n + n) :=
  (pointSumEquivBlockPoint n).symm (Sum.elim (pointLeft (n := n) z) y)

theorem continuous_leftPointEmbedding :
    Continuous (leftPointEmbedding (n := n)) := by
  refine continuous_pi ?_
  intro i
  cases hsplit : finSumFinEquiv.symm i with
  | inl j =>
      simpa [leftPointEmbedding, leftBlockPoint, pointSumEquivBlockPoint_symm_apply,
        hsplit] using (continuous_apply j : Continuous fun x : Point n => x j)
  | inr j =>
      simpa [leftPointEmbedding, leftBlockPoint, pointSumEquivBlockPoint_symm_apply,
        hsplit] using (continuous_const : Continuous fun _x : Point n => (0 : Real))

theorem continuous_rightPointEmbedding :
    Continuous (rightPointEmbedding (n := n)) := by
  refine continuous_pi ?_
  intro i
  cases hsplit : finSumFinEquiv.symm i with
  | inl j =>
      simpa [rightPointEmbedding, rightBlockPoint, pointSumEquivBlockPoint_symm_apply,
        hsplit] using (continuous_const : Continuous fun _y : Point n => (0 : Real))
  | inr j =>
      simpa [rightPointEmbedding, rightBlockPoint, pointSumEquivBlockPoint_symm_apply,
        hsplit] using (continuous_apply j : Continuous fun y : Point n => y j)

theorem continuous_pointLeft :
    Continuous (pointLeft (n := n)) := by
  refine continuous_pi ?_
  intro i
  simpa [pointLeft, blockPointLeft, pointSumEquivBlockPoint_apply_inl] using
    (continuous_apply (Fin.castAdd n i) : Continuous fun z : Point (n + n) => z (Fin.castAdd n i))

theorem continuous_pointRight :
    Continuous (pointRight (n := n)) := by
  refine continuous_pi ?_
  intro i
  simpa [pointRight, blockPointRight, pointSumEquivBlockPoint_apply_inr] using
    (continuous_apply (Fin.natAdd n i) : Continuous fun z : Point (n + n) => z (Fin.natAdd n i))

theorem continuous_pointWithLeft (z : Point (n + n)) :
    Continuous (pointWithLeft (n := n) z) := by
  refine continuous_pi ?_
  intro i
  cases hsplit : finSumFinEquiv.symm i with
  | inl j =>
      simpa [pointWithLeft, pointRight, blockPointRight, pointSumEquivBlockPoint_symm_apply,
        hsplit] using (continuous_apply j : Continuous fun x : Point n => x j)
  | inr j =>
      simpa [pointWithLeft, pointRight, blockPointRight, pointSumEquivBlockPoint_symm_apply,
        hsplit] using (continuous_const : Continuous fun _x : Point n => pointRight (n := n) z j)

theorem continuous_pointWithRight (z : Point (n + n)) :
    Continuous (pointWithRight (n := n) z) := by
  refine continuous_pi ?_
  intro i
  cases hsplit : finSumFinEquiv.symm i with
  | inl j =>
      simpa [pointWithRight, pointLeft, blockPointLeft, pointSumEquivBlockPoint_symm_apply,
        hsplit] using (continuous_const : Continuous fun _y : Point n => pointLeft (n := n) z j)
  | inr j =>
      simpa [pointWithRight, pointLeft, blockPointLeft, pointSumEquivBlockPoint_symm_apply,
        hsplit] using (continuous_apply j : Continuous fun y : Point n => y j)

/-- The left `R^n` component of a vector written in `R^(n+n)` coordinates. -/
def leftPointGradient (p : Point (n + n)) : Point n :=
  fun i => p (Fin.castAdd n i)

/-- The right `R^n` component of a vector written in `R^(n+n)` coordinates. -/
def rightPointGradient (p : Point (n + n)) : Point n :=
  fun i => p (Fin.natAdd n i)

@[simp]
theorem leftPointGradient_smul (a : Real) (p : Point (n + n)) :
    leftPointGradient (n := n) (a • p) = a • leftPointGradient (n := n) p := by
  ext i
  rfl

@[simp]
theorem rightPointGradient_smul (a : Real) (p : Point (n + n)) :
    rightPointGradient (n := n) (a • p) = a • rightPointGradient (n := n) p := by
  ext i
  rfl

/-- The left-left block of a Hessian written in `R^(n+n)` coordinates. -/
def leftPointHessian (X : Hessian (n + n)) : Hessian n :=
  X.submatrix (Fin.castAdd n) (Fin.castAdd n)

/-- The right-right block of a Hessian written in `R^(n+n)` coordinates. -/
def rightPointHessian (X : Hessian (n + n)) : Hessian n :=
  X.submatrix (Fin.natAdd n) (Fin.natAdd n)

/-- The left coordinate projection of a jet on `R^n × R^n`. -/
def leftPointJet (J : Jet (n + n)) : Jet n :=
  { gradient := leftPointGradient (n := n) J.gradient
    hessian := leftPointHessian (n := n) J.hessian }

/-- The right coordinate projection of a jet on `R^n × R^n`. -/
def rightPointJet (J : Jet (n + n)) : Jet n :=
  { gradient := rightPointGradient (n := n) J.gradient
    hessian := rightPointHessian (n := n) J.hessian }

theorem continuous_leftPointJet :
    Continuous (leftPointJet (n := n)) := by
  apply continuous_induced_rng.mpr
  change Continuous fun J : Jet (n + n) =>
    ((leftPointJet (n := n) J).gradient, (leftPointJet (n := n) J).hessian)
  have hgrad : Continuous fun J : Jet (n + n) => leftPointGradient (n := n) J.gradient := by
    refine continuous_pi ?_
    intro i
    exact (continuous_apply (Fin.castAdd n i)).comp
      (Jet.continuous_gradient (n := n + n))
  have hhess : Continuous fun J : Jet (n + n) => leftPointHessian (n := n) J.hessian := by
    refine continuous_pi ?_
    intro i
    refine continuous_pi ?_
    intro j
    exact (continuous_apply (Fin.castAdd n j)).comp
      ((continuous_apply (Fin.castAdd n i)).comp
        (Jet.continuous_hessian (n := n + n)))
  simpa [leftPointJet] using hgrad.prodMk hhess

theorem continuous_rightPointJet :
    Continuous (rightPointJet (n := n)) := by
  apply continuous_induced_rng.mpr
  change Continuous fun J : Jet (n + n) =>
    ((rightPointJet (n := n) J).gradient, (rightPointJet (n := n) J).hessian)
  have hgrad : Continuous fun J : Jet (n + n) => rightPointGradient (n := n) J.gradient := by
    refine continuous_pi ?_
    intro i
    exact (continuous_apply (Fin.natAdd n i)).comp
      (Jet.continuous_gradient (n := n + n))
  have hhess : Continuous fun J : Jet (n + n) => rightPointHessian (n := n) J.hessian := by
    refine continuous_pi ?_
    intro i
    refine continuous_pi ?_
    intro j
    exact (continuous_apply (Fin.natAdd n j)).comp
      ((continuous_apply (Fin.natAdd n i)).comp
        (Jet.continuous_hessian (n := n + n)))
  simpa [rightPointJet] using hgrad.prodMk hhess

/--
Convergence of block jets implies convergence of their left-coordinate
projected jets.
-/
theorem tendsto_leftPointJet_of_tendsto
    {ι : Type*} {l : Filter ι} {JSeq : ι -> Jet (n + n)} {J : Jet (n + n)}
    (hJ : Filter.Tendsto JSeq l (nhds J)) :
    Filter.Tendsto (fun i : ι => leftPointJet (n := n) (JSeq i)) l
      (nhds (leftPointJet (n := n) J)) :=
  (continuous_leftPointJet (n := n)).tendsto J |>.comp hJ

/--
Convergence of block jets implies convergence of the negated right-coordinate
projected jets.

In standard mathematical terms, if `J_i -> J` as jets on `R^n × R^n`, then
the jets obtained by taking the right coordinate component and negating both
the gradient and Hessian also converge:
`-(right J_i) -> -(right J)`.
-/
theorem tendsto_rightPointJet_neg_of_tendsto
    {ι : Type*} {l : Filter ι} {JSeq : ι -> Jet (n + n)} {J : Jet (n + n)}
    (hJ : Filter.Tendsto JSeq l (nhds J)) :
    Filter.Tendsto (fun i : ι => (rightPointJet (n := n) (JSeq i)).neg) l
      (nhds ((rightPointJet (n := n) J).neg)) := by
  have hcont : Continuous fun K : Jet (n + n) => (rightPointJet (n := n) K).neg := by
    apply continuous_induced_rng.mpr
    change Continuous fun K : Jet (n + n) =>
      (((rightPointJet (n := n) K).neg).gradient,
        ((rightPointJet (n := n) K).neg).hessian)
    have hright : Continuous fun K : Jet (n + n) => rightPointJet (n := n) K :=
      continuous_rightPointJet (n := n)
    have hgrad :
        Continuous fun K : Jet (n + n) => -((rightPointJet (n := n) K).gradient) :=
      (Jet.continuous_gradient.comp hright).neg
    have hhess :
        Continuous fun K : Jet (n + n) => -((rightPointJet (n := n) K).hessian) :=
      (Jet.continuous_hessian.comp hright).neg
    simpa [Jet.neg] using hgrad.prodMk hhess
  exact hcont.tendsto J |>.comp hJ

@[simp]
theorem pointSumEquivBlockPoint_leftPointEmbedding (x : Point n) :
    pointSumEquivBlockPoint n (leftPointEmbedding (n := n) x) = leftBlockPoint x := by
  simp [leftPointEmbedding]

@[simp]
theorem pointSumEquivBlockPoint_rightPointEmbedding (y : Point n) :
    pointSumEquivBlockPoint n (rightPointEmbedding (n := n) y) = rightBlockPoint y := by
  simp [rightPointEmbedding]

@[simp]
theorem leftBlockPoint_smul (a : Real) (x : Point n) :
    leftBlockPoint (a • x) = a • leftBlockPoint x := by
  ext i
  cases i <;> simp [leftBlockPoint]

@[simp]
theorem rightBlockPoint_smul (a : Real) (y : Point n) :
    rightBlockPoint (a • y) = a • rightBlockPoint y := by
  ext i
  cases i <;> simp [rightBlockPoint]

@[simp]
theorem leftPointEmbedding_smul (a : Real) (x : Point n) :
    leftPointEmbedding (n := n) (a • x) = a • leftPointEmbedding (n := n) x := by
  apply (pointSumEquivBlockPoint n).injective
  rw [pointSumEquivBlockPoint_leftPointEmbedding, pointSumEquivBlockPoint_smul,
    pointSumEquivBlockPoint_leftPointEmbedding, leftBlockPoint_smul]

@[simp]
theorem rightPointEmbedding_smul (a : Real) (y : Point n) :
    rightPointEmbedding (n := n) (a • y) = a • rightPointEmbedding (n := n) y := by
  apply (pointSumEquivBlockPoint n).injective
  rw [pointSumEquivBlockPoint_rightPointEmbedding, pointSumEquivBlockPoint_smul,
    pointSumEquivBlockPoint_rightPointEmbedding, rightBlockPoint_smul]

@[simp]
theorem blockPointLeft_leftBlockPoint (x : Point n) :
    blockPointLeft (leftBlockPoint x) = x := by
  rfl

@[simp]
theorem blockPointRight_leftBlockPoint (x : Point n) :
    blockPointRight (leftBlockPoint x) = 0 := by
  rfl

@[simp]
theorem blockPointLeft_rightBlockPoint (y : Point n) :
    blockPointLeft (rightBlockPoint y) = 0 := by
  rfl

@[simp]
theorem blockPointRight_rightBlockPoint (y : Point n) :
    blockPointRight (rightBlockPoint y) = y := by
  rfl

@[simp]
theorem leftBlockPoint_single (i : Fin n) :
    leftBlockPoint (Pi.single i (1 : Real)) = Pi.single (Sum.inl i) (1 : Real) := by
  ext c
  cases c with
  | inl k =>
      by_cases h : k = i
      · subst h
        simp [leftBlockPoint]
      · have hsum : Sum.inl k ≠ (Sum.inl i : Fin n ⊕ Fin n) := by
          intro hs
          exact h (Sum.inl.inj hs)
        simp [leftBlockPoint, Pi.single, h, hsum]
  | inr k =>
      simp [leftBlockPoint, Pi.single]

@[simp]
theorem rightBlockPoint_single (j : Fin n) :
    rightBlockPoint (Pi.single j (1 : Real)) = Pi.single (Sum.inr j) (1 : Real) := by
  ext c
  cases c with
  | inl k =>
      simp [rightBlockPoint, Pi.single]
  | inr k =>
      by_cases h : k = j
      · subst h
        simp [rightBlockPoint]
      · have hsum : Sum.inr k ≠ (Sum.inr j : Fin n ⊕ Fin n) := by
          intro hs
          exact h (Sum.inr.inj hs)
        simp [rightBlockPoint, Pi.single, h, hsum]

theorem finSumFinEquiv_symm_castAdd (i : Fin n) :
    finSumFinEquiv.symm (Fin.castAdd n i) = Sum.inl i := by
  exact (Equiv.symm_apply_eq finSumFinEquiv).2 rfl

theorem finSumFinEquiv_symm_natAdd (i : Fin n) :
    finSumFinEquiv.symm (Fin.natAdd n i) = Sum.inr i := by
  exact (Equiv.symm_apply_eq finSumFinEquiv).2 rfl

@[simp]
theorem finSumFinEquiv_symm_addNat (i : Fin n) :
    finSumFinEquiv.symm (i.addNat n) = Sum.inr i := by
  rw [← Fin.natAdd_eq_addNat]
  exact finSumFinEquiv_symm_natAdd (n := n) i

@[simp]
theorem pointLeft_zero :
    pointLeft (n := n) 0 = 0 := by
  simp [pointLeft, blockPointLeft, pointSumEquivBlockPoint_zero]

@[simp]
theorem pointRight_zero :
    pointRight (n := n) 0 = 0 := by
  simp [pointRight, blockPointRight, pointSumEquivBlockPoint_zero]

@[simp]
theorem pointLeft_leftPointEmbedding (x : Point n) :
    pointLeft (n := n) (leftPointEmbedding (n := n) x) = x := by
  simp [pointLeft]

@[simp]
theorem pointRight_leftPointEmbedding (x : Point n) :
    pointRight (n := n) (leftPointEmbedding (n := n) x) = 0 := by
  simp [pointRight]

@[simp]
theorem pointLeft_rightPointEmbedding (y : Point n) :
    pointLeft (n := n) (rightPointEmbedding (n := n) y) = 0 := by
  simp [pointLeft]

@[simp]
theorem pointRight_rightPointEmbedding (y : Point n) :
    pointRight (n := n) (rightPointEmbedding (n := n) y) = y := by
  simp [pointRight]

@[simp]
theorem pointLeft_add_leftPointEmbedding (z : Point (n + n)) (x : Point n) :
    pointLeft (n := n) (z + leftPointEmbedding (n := n) x) =
      pointLeft (n := n) z + x := by
  ext i
  simp [pointLeft, blockPointLeft, leftBlockPoint, pointSumEquivBlockPoint_add]

@[simp]
theorem pointRight_add_leftPointEmbedding (z : Point (n + n)) (x : Point n) :
    pointRight (n := n) (z + leftPointEmbedding (n := n) x) =
      pointRight (n := n) z := by
  ext i
  simp [pointRight, blockPointRight, leftBlockPoint, pointSumEquivBlockPoint_add]

@[simp]
theorem pointLeft_add_rightPointEmbedding (z : Point (n + n)) (y : Point n) :
    pointLeft (n := n) (z + rightPointEmbedding (n := n) y) =
      pointLeft (n := n) z := by
  ext i
  simp [pointLeft, blockPointLeft, rightBlockPoint, pointSumEquivBlockPoint_add]

@[simp]
theorem pointRight_add_rightPointEmbedding (z : Point (n + n)) (y : Point n) :
    pointRight (n := n) (z + rightPointEmbedding (n := n) y) =
      pointRight (n := n) z + y := by
  ext i
  simp [pointRight, blockPointRight, rightBlockPoint, pointSumEquivBlockPoint_add]

@[simp]
theorem pointSumEquivBlockPoint_pointWithLeft (z : Point (n + n)) (x : Point n) :
    pointSumEquivBlockPoint n (pointWithLeft (n := n) z x) =
      Sum.elim x (pointRight (n := n) z) := by
  simp [pointWithLeft]

@[simp]
theorem pointSumEquivBlockPoint_pointWithRight (z : Point (n + n)) (y : Point n) :
    pointSumEquivBlockPoint n (pointWithRight (n := n) z y) =
      Sum.elim (pointLeft (n := n) z) y := by
  simp [pointWithRight]

@[simp]
theorem pointLeft_pointWithLeft (z : Point (n + n)) (x : Point n) :
    pointLeft (n := n) (pointWithLeft (n := n) z x) = x := by
  simp [pointLeft, blockPointLeft]

@[simp]
theorem pointRight_pointWithLeft (z : Point (n + n)) (x : Point n) :
    pointRight (n := n) (pointWithLeft (n := n) z x) = pointRight (n := n) z := by
  simp [pointRight, blockPointRight]

@[simp]
theorem pointLeft_pointWithRight (z : Point (n + n)) (y : Point n) :
    pointLeft (n := n) (pointWithRight (n := n) z y) = pointLeft (n := n) z := by
  simp [pointLeft, blockPointLeft]

@[simp]
theorem pointRight_pointWithRight (z : Point (n + n)) (y : Point n) :
    pointRight (n := n) (pointWithRight (n := n) z y) = y := by
  simp [pointRight, blockPointRight]

@[simp]
theorem pointWithLeft_self (z : Point (n + n)) :
    pointWithLeft (n := n) z (pointLeft (n := n) z) = z := by
  apply (pointSumEquivBlockPoint n).injective
  have h :=
    doubledPointToBlockPoint_left_right (n := n) (pointSumEquivBlockPoint n z)
  simpa [pointWithLeft, pointLeft, pointRight, doubledPointToBlockPoint] using h

@[simp]
theorem pointWithRight_self (z : Point (n + n)) :
    pointWithRight (n := n) z (pointRight (n := n) z) = z := by
  apply (pointSumEquivBlockPoint n).injective
  have h :=
    doubledPointToBlockPoint_left_right (n := n) (pointSumEquivBlockPoint n z)
  simpa [pointWithRight, pointLeft, pointRight, doubledPointToBlockPoint] using h

theorem pointWithLeft_sub_self (z : Point (n + n)) (x : Point n) :
    pointWithLeft (n := n) z x - z =
      leftPointEmbedding (n := n) (x - pointLeft (n := n) z) := by
  ext i
  cases hsplit : finSumFinEquiv.symm i with
  | inl j =>
      have hi : i = Fin.castAdd n j := by
        calc
          i = finSumFinEquiv (finSumFinEquiv.symm i) :=
            (Equiv.apply_symm_apply finSumFinEquiv i).symm
          _ = finSumFinEquiv (Sum.inl j) := congrArg finSumFinEquiv hsplit
          _ = Fin.castAdd n j := rfl
      rw [hi]
      simp [pointWithLeft, leftPointEmbedding, leftBlockPoint, pointLeft, pointRight,
        blockPointLeft, blockPointRight, pointSumEquivBlockPoint_symm_apply]
  | inr j =>
      have hi : i = Fin.natAdd n j := by
        calc
          i = finSumFinEquiv (finSumFinEquiv.symm i) :=
            (Equiv.apply_symm_apply finSumFinEquiv i).symm
          _ = finSumFinEquiv (Sum.inr j) := congrArg finSumFinEquiv hsplit
          _ = Fin.natAdd n j := rfl
      rw [hi]
      simp [pointWithLeft, leftPointEmbedding, leftBlockPoint, pointLeft, pointRight,
        blockPointLeft, blockPointRight, pointSumEquivBlockPoint_symm_apply]

theorem pointWithRight_sub_self (z : Point (n + n)) (y : Point n) :
    pointWithRight (n := n) z y - z =
      rightPointEmbedding (n := n) (y - pointRight (n := n) z) := by
  ext i
  cases hsplit : finSumFinEquiv.symm i with
  | inl j =>
      have hi : i = Fin.castAdd n j := by
        calc
          i = finSumFinEquiv (finSumFinEquiv.symm i) :=
            (Equiv.apply_symm_apply finSumFinEquiv i).symm
          _ = finSumFinEquiv (Sum.inl j) := congrArg finSumFinEquiv hsplit
          _ = Fin.castAdd n j := rfl
      rw [hi]
      simp [pointWithRight, rightPointEmbedding, rightBlockPoint, pointLeft, pointRight,
        blockPointLeft, blockPointRight, pointSumEquivBlockPoint_symm_apply]
  | inr j =>
      have hi : i = Fin.natAdd n j := by
        calc
          i = finSumFinEquiv (finSumFinEquiv.symm i) :=
            (Equiv.apply_symm_apply finSumFinEquiv i).symm
          _ = finSumFinEquiv (Sum.inr j) := congrArg finSumFinEquiv hsplit
          _ = Fin.natAdd n j := rfl
      rw [hi]
      simp [pointWithRight, rightPointEmbedding, rightBlockPoint, pointLeft, pointRight,
        blockPointLeft, blockPointRight, pointSumEquivBlockPoint_symm_apply]

@[simp]
theorem leftPointEmbedding_zero :
    leftPointEmbedding (n := n) 0 = 0 := by
  apply (pointSumEquivBlockPoint n).injective
  simp [leftPointEmbedding, leftBlockPoint]

@[simp]
theorem rightPointEmbedding_zero :
    rightPointEmbedding (n := n) 0 = 0 := by
  apply (pointSumEquivBlockPoint n).injective
  simp [rightPointEmbedding, rightBlockPoint]

@[simp]
theorem leftPointEmbedding_apply_castAdd (x : Point n) (i : Fin n) :
    leftPointEmbedding (n := n) x (Fin.castAdd n i) = x i := by
  have h := congr_fun (pointSumEquivBlockPoint_leftPointEmbedding (n := n) x) (Sum.inl i)
  simpa [leftBlockPoint] using h

theorem leftPointEmbedding_apply_natAdd (x : Point n) (i : Fin n) :
    leftPointEmbedding (n := n) x (Fin.natAdd n i) = 0 := by
  have h := congr_fun (pointSumEquivBlockPoint_leftPointEmbedding (n := n) x) (Sum.inr i)
  simpa [leftBlockPoint] using h

@[simp]
theorem rightPointEmbedding_apply_castAdd (y : Point n) (i : Fin n) :
    rightPointEmbedding (n := n) y (Fin.castAdd n i) = 0 := by
  have h := congr_fun (pointSumEquivBlockPoint_rightPointEmbedding (n := n) y) (Sum.inl i)
  simpa [rightBlockPoint] using h

theorem rightPointEmbedding_apply_natAdd (y : Point n) (i : Fin n) :
    rightPointEmbedding (n := n) y (Fin.natAdd n i) = y i := by
  have h := congr_fun (pointSumEquivBlockPoint_rightPointEmbedding (n := n) y) (Sum.inr i)
  simpa [rightBlockPoint] using h

/-- The left embedding vanishes on the right coordinate block. -/
@[simp]
theorem leftPointEmbedding_apply_addNat (x : Point n) (i : Fin n) :
    leftPointEmbedding (n := n) x (i.addNat n) = 0 := by
  simpa only [Fin.natAdd_eq_addNat] using leftPointEmbedding_apply_natAdd x i

/-- The right embedding recovers the original right coordinate. -/
@[simp]
theorem rightPointEmbedding_apply_addNat (y : Point n) (i : Fin n) :
    rightPointEmbedding (n := n) y (i.addNat n) = y i := by
  simpa only [Fin.natAdd_eq_addNat] using rightPointEmbedding_apply_natAdd y i

@[simp]
theorem dotProduct_leftPointGradient (p : Point (n + n)) (x : Point n) :
    dotProduct p (leftPointEmbedding (n := n) x) =
      dotProduct (leftPointGradient (n := n) p) x := by
  rw [← dotProduct_pointSumEquivBlockPoint
    (n := n) p (leftPointEmbedding (n := n) x)]
  simp [leftPointGradient, leftBlockPoint, dotProduct, Fintype.sum_sum_type]

@[simp]
theorem dotProduct_rightPointGradient (p : Point (n + n)) (y : Point n) :
    dotProduct p (rightPointEmbedding (n := n) y) =
      dotProduct (rightPointGradient (n := n) p) y := by
  rw [← dotProduct_pointSumEquivBlockPoint
    (n := n) p (rightPointEmbedding (n := n) y)]
  simp [rightPointGradient, rightBlockPoint, dotProduct, Fintype.sum_sum_type]

theorem norm_leftPointEmbedding_le (x : Point n) :
    ‖leftPointEmbedding (n := n) x‖ <= ‖x‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg x)]
  intro i
  cases hsplit : finSumFinEquiv.symm i with
  | inl j =>
      have hi : i = Fin.castAdd n j := by
        calc
          i = finSumFinEquiv (finSumFinEquiv.symm i) :=
            (Equiv.apply_symm_apply finSumFinEquiv i).symm
          _ = finSumFinEquiv (Sum.inl j) := congrArg finSumFinEquiv hsplit
          _ = Fin.castAdd n j := rfl
      have hcoord : leftPointEmbedding (n := n) x i = x j := by
        rw [hi]
        exact leftPointEmbedding_apply_castAdd (n := n) x j
      rw [hcoord]
      exact norm_le_pi_norm x j
  | inr j =>
      have hi : i = Fin.natAdd n j := by
        calc
          i = finSumFinEquiv (finSumFinEquiv.symm i) :=
            (Equiv.apply_symm_apply finSumFinEquiv i).symm
          _ = finSumFinEquiv (Sum.inr j) := congrArg finSumFinEquiv hsplit
          _ = Fin.natAdd n j := rfl
      have hcoord : leftPointEmbedding (n := n) x i = 0 := by
        rw [hi]
        exact leftPointEmbedding_apply_natAdd (n := n) x j
      rw [hcoord]
      simp

theorem norm_rightPointEmbedding_le (y : Point n) :
    ‖rightPointEmbedding (n := n) y‖ <= ‖y‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg y)]
  intro i
  cases hsplit : finSumFinEquiv.symm i with
  | inl j =>
      have hi : i = Fin.castAdd n j := by
        calc
          i = finSumFinEquiv (finSumFinEquiv.symm i) :=
            (Equiv.apply_symm_apply finSumFinEquiv i).symm
          _ = finSumFinEquiv (Sum.inl j) := congrArg finSumFinEquiv hsplit
          _ = Fin.castAdd n j := rfl
      have hcoord : rightPointEmbedding (n := n) y i = 0 := by
        rw [hi]
        exact rightPointEmbedding_apply_castAdd (n := n) y j
      rw [hcoord]
      simp
  | inr j =>
      have hi : i = Fin.natAdd n j := by
        calc
          i = finSumFinEquiv (finSumFinEquiv.symm i) :=
            (Equiv.apply_symm_apply finSumFinEquiv i).symm
          _ = finSumFinEquiv (Sum.inr j) := congrArg finSumFinEquiv hsplit
          _ = Fin.natAdd n j := rfl
      have hcoord : rightPointEmbedding (n := n) y i = y j := by
        rw [hi]
        exact rightPointEmbedding_apply_natAdd (n := n) y j
      rw [hcoord]
      exact norm_le_pi_norm y j

theorem norm_pointWithLeft_sub_self_le (z : Point (n + n)) (x : Point n) :
    ‖pointWithLeft (n := n) z x - z‖ <= ‖x - pointLeft (n := n) z‖ := by
  rw [pointWithLeft_sub_self]
  exact norm_leftPointEmbedding_le (n := n) (x - pointLeft (n := n) z)

theorem norm_pointWithRight_sub_self_le (z : Point (n + n)) (y : Point n) :
    ‖pointWithRight (n := n) z y - z‖ <= ‖y - pointRight (n := n) z‖ := by
  rw [pointWithRight_sub_self]
  exact norm_rightPointEmbedding_le (n := n) (y - pointRight (n := n) z)

@[simp]
theorem quadraticModel_leftPointEmbedding
    (r : Real) (p : Point (n + n)) (X : Hessian (n + n)) (x : Point n) :
    quadraticModel 0 r p X (leftPointEmbedding (n := n) x) =
      quadraticModel 0 r (leftPointGradient (n := n) p)
        (leftPointHessian (n := n) X) x := by
  have hquad :
      dotProduct (Matrix.mulVec X (leftPointEmbedding (n := n) x))
          (leftPointEmbedding (n := n) x) =
        dotProduct (Matrix.mulVec (leftPointHessian (n := n) X) x) x := by
    have h :=
      quadraticForm_pointHessianToBlockHessian_pointSumEquivBlockPoint
        (n := n) X (leftPointEmbedding (n := n) x)
    rw [dotProduct_comm] at h
    rw [dotProduct_comm (Matrix.mulVec X (leftPointEmbedding (n := n) x))
      (leftPointEmbedding (n := n) x)]
    rw [← h]
    simp [leftPointHessian, leftBlockPoint, Matrix.mulVec, dotProduct, Finset.sum_mul]
  simp [quadraticModel, hquad]

@[simp]
theorem quadraticModel_rightPointEmbedding
    (r : Real) (p : Point (n + n)) (X : Hessian (n + n)) (y : Point n) :
    quadraticModel 0 r p X (rightPointEmbedding (n := n) y) =
      quadraticModel 0 r (rightPointGradient (n := n) p)
        (rightPointHessian (n := n) X) y := by
  have hquad :
      dotProduct (Matrix.mulVec X (rightPointEmbedding (n := n) y))
          (rightPointEmbedding (n := n) y) =
        dotProduct (Matrix.mulVec (rightPointHessian (n := n) X) y) y := by
    have h :=
      quadraticForm_pointHessianToBlockHessian_pointSumEquivBlockPoint
        (n := n) X (rightPointEmbedding (n := n) y)
    rw [dotProduct_comm] at h
    rw [dotProduct_comm (Matrix.mulVec X (rightPointEmbedding (n := n) y))
      (rightPointEmbedding (n := n) y)]
    rw [← h]
    simp [rightPointHessian, rightBlockPoint, Matrix.mulVec, dotProduct, Finset.sum_mul]
  simp [quadraticModel, hquad]

@[simp]
theorem quadraticModel_pointWithLeft
    (z : Point (n + n)) (r : Real) (p : Point (n + n)) (X : Hessian (n + n))
    (x : Point n) :
    quadraticModel z r p X (pointWithLeft (n := n) z x) =
      quadraticModel (pointLeft (n := n) z) r (leftPointGradient (n := n) p)
        (leftPointHessian (n := n) X) x := by
  let dx : Point n := x - pointLeft (n := n) z
  have hdiff :
      pointWithLeft (n := n) z x - z = leftPointEmbedding (n := n) dx := by
    simpa [dx] using pointWithLeft_sub_self (n := n) z x
  have hquad :
      dotProduct (Matrix.mulVec X (leftPointEmbedding (n := n) dx))
          (leftPointEmbedding (n := n) dx) =
        dotProduct (Matrix.mulVec (leftPointHessian (n := n) X) dx) dx := by
    have h :=
      quadraticForm_pointHessianToBlockHessian_pointSumEquivBlockPoint
        (n := n) X (leftPointEmbedding (n := n) dx)
    rw [dotProduct_comm] at h
    rw [dotProduct_comm (Matrix.mulVec X (leftPointEmbedding (n := n) dx))
      (leftPointEmbedding (n := n) dx)]
    rw [← h]
    simp [leftPointHessian, leftBlockPoint, Matrix.mulVec, dotProduct, Finset.sum_mul]
  simp [quadraticModel, hdiff, dx, hquad]

@[simp]
theorem quadraticModel_pointWithRight
    (z : Point (n + n)) (r : Real) (p : Point (n + n)) (X : Hessian (n + n))
    (y : Point n) :
    quadraticModel z r p X (pointWithRight (n := n) z y) =
      quadraticModel (pointRight (n := n) z) r (rightPointGradient (n := n) p)
        (rightPointHessian (n := n) X) y := by
  let dy : Point n := y - pointRight (n := n) z
  have hdiff :
      pointWithRight (n := n) z y - z = rightPointEmbedding (n := n) dy := by
    simpa [dy] using pointWithRight_sub_self (n := n) z y
  have hquad :
      dotProduct (Matrix.mulVec X (rightPointEmbedding (n := n) dy))
          (rightPointEmbedding (n := n) dy) =
        dotProduct (Matrix.mulVec (rightPointHessian (n := n) X) dy) dy := by
    have h :=
      quadraticForm_pointHessianToBlockHessian_pointSumEquivBlockPoint
        (n := n) X (rightPointEmbedding (n := n) dy)
    rw [dotProduct_comm] at h
    rw [dotProduct_comm (Matrix.mulVec X (rightPointEmbedding (n := n) dy))
      (rightPointEmbedding (n := n) dy)]
    rw [← h]
    simp [rightPointHessian, rightBlockPoint, Matrix.mulVec, dotProduct, Finset.sum_mul]
  simp [quadraticModel, hdiff, dy, hquad]

/--
The mixed second difference of a quadratic model in a left direction and a
right direction depends only on the mixed Hessian terms.

In standard mathematical terms, for a quadratic polynomial on `R^n × R^n`,
the expression

`q(z + (x, 0) + (0, y)) - q(z + (x, 0)) - q(z + (0, y)) + q(z)`

is

`(1 / 2) * (⟪X(x, 0), (0, y)⟫ + ⟪X(0, y), (x, 0)⟫)`.
-/
theorem quadraticModel_mixed_second_difference_left_right
    (z : Point (n + n)) (r : Real) (p : Point (n + n)) (X : Hessian (n + n))
    (x y : Point n) :
    quadraticModel z r p X
        (z + leftPointEmbedding (n := n) x + rightPointEmbedding (n := n) y) -
        quadraticModel z r p X (z + leftPointEmbedding (n := n) x) -
        quadraticModel z r p X (z + rightPointEmbedding (n := n) y) +
        quadraticModel z r p X z =
      (1 / 2 : Real) *
        (dotProduct (Matrix.mulVec X (leftPointEmbedding (n := n) x))
            (rightPointEmbedding (n := n) y) +
          dotProduct (Matrix.mulVec X (rightPointEmbedding (n := n) y))
            (leftPointEmbedding (n := n) x)) := by
  simpa [add_assoc] using
    quadraticModel_mixed_second_difference (n := n + n) z r p X
      (leftPointEmbedding (n := n) x) (rightPointEmbedding (n := n) y)

/--
The cross term between a left increment and a right increment may be computed
in block coordinates.

In standard mathematical terms, reindexing the Hessian `Z` from `R^{2n}` to
`R^n × R^n` does not change the bilinear expression
`⟪Z(x, 0), (0, y)⟫`.
-/
theorem dotProduct_mulVec_leftPointEmbedding_rightPointEmbedding
    (Z : Hessian (n + n)) (x y : Point n) :
    dotProduct (Matrix.mulVec Z (leftPointEmbedding (n := n) x))
        (rightPointEmbedding (n := n) y) =
      dotProduct
        (Matrix.mulVec (pointHessianToBlockHessian (n := n) Z) (leftBlockPoint x))
        (rightBlockPoint y) := by
  rw [← dotProduct_pointSumEquivBlockPoint]
  conv_rhs => rw [← pointSumEquivBlockPoint_leftPointEmbedding (n := n) x]
  rw [pointHessianToBlockHessian_mulVec_pointSumEquivBlockPoint]
  simp

/--
The cross term between a right increment and a left increment may be computed
in block coordinates.

In standard mathematical terms, reindexing the Hessian `Z` from `R^{2n}` to
`R^n × R^n` does not change the bilinear expression
`⟪Z(0, y), (x, 0)⟫`.
-/
theorem dotProduct_mulVec_rightPointEmbedding_leftPointEmbedding
    (Z : Hessian (n + n)) (x y : Point n) :
    dotProduct (Matrix.mulVec Z (rightPointEmbedding (n := n) y))
        (leftPointEmbedding (n := n) x) =
      dotProduct
        (Matrix.mulVec (pointHessianToBlockHessian (n := n) Z) (rightBlockPoint y))
        (leftBlockPoint x) := by
  rw [← dotProduct_pointSumEquivBlockPoint]
  conv_rhs => rw [← pointSumEquivBlockPoint_rightPointEmbedding (n := n) y]
  rw [pointHessianToBlockHessian_mulVec_pointSumEquivBlockPoint]
  simp

/--
The left-right cross term against coordinate basis vectors is the corresponding
matrix entry.

In standard mathematical terms, for a block Hessian `A`,

`⟪A e_i^L, e_j^R⟫ = A_{R_j,L_i}`.
-/
theorem dotProduct_mulVec_leftBlockPoint_single_rightBlockPoint_single
    (A : BlockHessian n) (i j : Fin n) :
    dotProduct (Matrix.mulVec A (Pi.single (Sum.inl i) (1 : Real)))
        (Pi.single (Sum.inr j) (1 : Real)) =
      A (Sum.inr j) (Sum.inl i) := by
  rw [dotProduct_single_one]
  simp [Matrix.mulVec]

/--
The right-left cross term against coordinate basis vectors is the corresponding
matrix entry.

In standard mathematical terms, for a block Hessian `A`,

`⟪A e_j^R, e_i^L⟫ = A_{L_i,R_j}`.
-/
theorem dotProduct_mulVec_rightBlockPoint_single_leftBlockPoint_single
    (A : BlockHessian n) (i j : Fin n) :
    dotProduct (Matrix.mulVec A (Pi.single (Sum.inr j) (1 : Real)))
        (Pi.single (Sum.inl i) (1 : Real)) =
      A (Sum.inl i) (Sum.inr j) := by
  rw [dotProduct_single_one]
  simp [Matrix.mulVec]

end ViscositySolns
