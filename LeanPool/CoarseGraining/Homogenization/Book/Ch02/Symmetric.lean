/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch01.FieldSpaces
import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Matrices

/-! # Symmetric -/

namespace Homogenization
namespace Book
namespace Ch02

noncomputable section

/-- Public averaged gradient of an arbitrary `H¹` function on a Chapter 2
domain. -/
noncomputable def h1AverageGradient {d : ℕ} (U : Domain d)
    (u : H1Function (U : Set (Vec d))) : Vec d :=
  averageVec U u.grad

/-- Public averaged flux of an arbitrary `H¹` function on a Chapter 2 domain. -/
noncomputable def h1AverageFlux {d : ℕ} (U : Domain d) (a : CoeffOn U)
    (u : H1Function (U : Set (Vec d))) : Vec d :=
  averageVec U fun x => matVecMul (a.toCoeffField x) (u.grad x)

/-- Public Dirichlet admissibility for the symmetric subsection:
`u ∈ p · x + H¹₀(U)`, stated by saying that `∇u - p` is a zero-trace
potential field. -/
def IsSymmetricDirichletAdmissible {d : ℕ} (U : Domain d) (p : Vec d)
    (u : H1Function (U : Set (Vec d))) : Prop :=
  Book.Ch01.PotentialZeroTraceFieldOn (U : Set (Vec d)) (fun x => u.grad x - p)

/-- Public Dirichlet energy value from
`e.def.nuD.nuN.symmetric.basic.definitions`. -/
noncomputable def symmetricDirichletEnergyValue {d : ℕ} (U : Domain d)
    (a : CoeffOn U) (u : H1Function (U : Set (Vec d))) : ℝ :=
  average U fun x =>
    (1 / 2 : ℝ) * vecDot (u.grad x) (matVecMul (a.toCoeffField x) (u.grad x))

/-- Public value set whose infimum is `ν_D(U,p;a)`. -/
noncomputable def symmetricDirichletValueSet {d : ℕ} (U : Domain d)
    (a : CoeffOn U) (p : Vec d) : Set ℝ :=
  {E | ∃ u : H1Function (U : Set (Vec d)),
      IsSymmetricDirichletAdmissible U p u ∧
        E = symmetricDirichletEnergyValue U a u}

/-- Public Dirichlet value `ν_D(U,p;a)`. -/
noncomputable def symmetricDirichletNu {d : ℕ} (U : Domain d)
    (a : CoeffOn U) (p : Vec d) : ℝ :=
  sInf (symmetricDirichletValueSet U a p)

/-- A public minimizer for `ν_D(U,p;a)`. -/
def IsSymmetricDirichletMinimizer {d : ℕ} (U : Domain d) (a : CoeffOn U)
    (p : Vec d) (u : H1Function (U : Set (Vec d))) : Prop :=
  IsSymmetricDirichletAdmissible U p u ∧
    ∀ w : H1Function (U : Set (Vec d)),
      IsSymmetricDirichletAdmissible U p w →
        symmetricDirichletEnergyValue U a u ≤ symmetricDirichletEnergyValue U a w

/-- Public Neumann value of a candidate from
`e.def.nuD.nuN.symmetric.basic.definitions`. -/
noncomputable def symmetricNeumannEnergyValue {d : ℕ} (U : Domain d)
    (a : CoeffOn U) (q : Vec d) (u : H1Function (U : Set (Vec d))) : ℝ :=
  average U fun x =>
    vecDot q (u.grad x) -
      (1 / 2 : ℝ) * vecDot (u.grad x) (matVecMul (a.toCoeffField x) (u.grad x))

/-- Public value set whose supremum is `ν_N(U,q;a)`. -/
noncomputable def symmetricNeumannValueSet {d : ℕ} (U : Domain d)
    (a : CoeffOn U) (q : Vec d) : Set ℝ :=
  {E | ∃ u : H1Function (U : Set (Vec d)),
      E = symmetricNeumannEnergyValue U a q u}

/-- Public Neumann value `ν_N(U,q;a)`. -/
noncomputable def symmetricNeumannNu {d : ℕ} (U : Domain d)
    (a : CoeffOn U) (q : Vec d) : ℝ :=
  sSup (symmetricNeumannValueSet U a q)

/-- A public maximizer for `ν_N(U,q;a)`. The note chooses the mean-zero
representative separately, so mean-zero is a theorem-field condition rather than
part of this maximizer predicate. -/
def IsSymmetricNeumannMaximizer {d : ℕ} (U : Domain d) (a : CoeffOn U)
    (q : Vec d) (u : H1Function (U : Set (Vec d))) : Prop :=
  ∀ w : H1Function (U : Set (Vec d)),
    symmetricNeumannEnergyValue U a q w ≤ symmetricNeumannEnergyValue U a q u

/-- The public Dirichlet energy depends only on the coefficient field up to
a.e. equality on the domain. -/
theorem symmetricDirichletEnergyValue_eq_ofAEEq {d : ℕ} {U : Domain d}
    {a b : CoeffOn U} (h : CoeffOn.AEEq a b)
    (u : H1Function (U : Set (Vec d))) :
    symmetricDirichletEnergyValue U a u =
      symmetricDirichletEnergyValue U b u := by
  unfold symmetricDirichletEnergyValue average
  congr 1
  exact MeasureTheory.integral_congr_ae <| h.mono fun x hx => by
    simp [hx]

/-- The public Dirichlet value set is invariant under a.e. coefficient changes. -/
theorem symmetricDirichletValueSet_eq_ofAEEq {d : ℕ} {U : Domain d}
    {a b : CoeffOn U} (h : CoeffOn.AEEq a b) (p : Vec d) :
    symmetricDirichletValueSet U a p =
      symmetricDirichletValueSet U b p := by
  ext E
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, hu, by
      simp [symmetricDirichletEnergyValue_eq_ofAEEq h u]⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, hu, by
      simp [symmetricDirichletEnergyValue_eq_ofAEEq h.symm u]⟩

/-- The public Dirichlet value is invariant under a.e. coefficient changes. -/
theorem symmetricDirichletNu_eq_ofAEEq {d : ℕ} {U : Domain d}
    {a b : CoeffOn U} (h : CoeffOn.AEEq a b) (p : Vec d) :
    symmetricDirichletNu U a p = symmetricDirichletNu U b p := by
  unfold symmetricDirichletNu
  rw [symmetricDirichletValueSet_eq_ofAEEq h p]

namespace IsSymmetricDirichletMinimizer

/-- Transport a public symmetric Dirichlet minimizer across an a.e. coefficient
change. -/
theorem ofAEEq {d : ℕ} {U : Domain d} {a b : CoeffOn U}
    (h : CoeffOn.AEEq a b) {p : Vec d}
    {u : H1Function (U : Set (Vec d))}
    (hu : IsSymmetricDirichletMinimizer U a p u) :
    IsSymmetricDirichletMinimizer U b p u := by
  refine ⟨hu.1, ?_⟩
  intro w hw
  have hmin := hu.2 w hw
  simpa [symmetricDirichletEnergyValue_eq_ofAEEq h u,
    symmetricDirichletEnergyValue_eq_ofAEEq h w] using hmin

end IsSymmetricDirichletMinimizer

/-- The public Neumann candidate value depends only on the coefficient field up
to a.e. equality on the domain. -/
theorem symmetricNeumannEnergyValue_eq_ofAEEq {d : ℕ} {U : Domain d}
    {a b : CoeffOn U} (h : CoeffOn.AEEq a b) (q : Vec d)
    (u : H1Function (U : Set (Vec d))) :
    symmetricNeumannEnergyValue U a q u =
      symmetricNeumannEnergyValue U b q u := by
  unfold symmetricNeumannEnergyValue average
  congr 1
  exact MeasureTheory.integral_congr_ae <| h.mono fun x hx => by
    simp [hx]

/-- The public Neumann value set is invariant under a.e. coefficient changes. -/
theorem symmetricNeumannValueSet_eq_ofAEEq {d : ℕ} {U : Domain d}
    {a b : CoeffOn U} (h : CoeffOn.AEEq a b) (q : Vec d) :
    symmetricNeumannValueSet U a q =
      symmetricNeumannValueSet U b q := by
  ext E
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨u, by
      simp [symmetricNeumannEnergyValue_eq_ofAEEq h q u]⟩
  · rintro ⟨u, rfl⟩
    exact ⟨u, by
      simp [symmetricNeumannEnergyValue_eq_ofAEEq h.symm q u]⟩

/-- The public Neumann value is invariant under a.e. coefficient changes. -/
theorem symmetricNeumannNu_eq_ofAEEq {d : ℕ} {U : Domain d}
    {a b : CoeffOn U} (h : CoeffOn.AEEq a b) (q : Vec d) :
    symmetricNeumannNu U a q = symmetricNeumannNu U b q := by
  unfold symmetricNeumannNu
  rw [symmetricNeumannValueSet_eq_ofAEEq h q]

namespace IsSymmetricNeumannMaximizer

/-- Transport a public symmetric Neumann maximizer across an a.e. coefficient
change. -/
theorem ofAEEq {d : ℕ} {U : Domain d} {a b : CoeffOn U}
    (h : CoeffOn.AEEq a b) {q : Vec d}
    {u : H1Function (U : Set (Vec d))}
    (hu : IsSymmetricNeumannMaximizer U a q u) :
    IsSymmetricNeumannMaximizer U b q u := by
  intro w
  have hmax := hu w
  simpa [symmetricNeumannEnergyValue_eq_ofAEEq h q u,
    symmetricNeumannEnergyValue_eq_ofAEEq h q w] using hmax

end IsSymmetricNeumannMaximizer

/-- The public averaged flux of an arbitrary `H¹` function is invariant under
a.e. coefficient changes. -/
theorem h1AverageFlux_eq_ofAEEq {d : ℕ} {U : Domain d} {a b : CoeffOn U}
    (h : CoeffOn.AEEq a b) (u : H1Function (U : Set (Vec d))) :
    h1AverageFlux U a u = h1AverageFlux U b u := by
  ext i
  unfold h1AverageFlux averageVec average
  congr 1
  exact MeasureTheory.integral_congr_ae <| h.mono fun x hx => by
    simp [hx]

/-- The raw public coefficient average is invariant under a.e. coefficient
changes. -/
theorem averageMat_toCoeffField_eq_ofAEEq {d : ℕ} {U : Domain d}
    {a b : CoeffOn U} (h : CoeffOn.AEEq a b) :
    averageMat U a.toCoeffField = averageMat U b.toCoeffField := by
  ext i j
  unfold averageMat average
  congr 1
  exact MeasureTheory.integral_congr_ae <| h.mono fun x hx => by
    simp [hx]

end

end Ch02
end Book
end Homogenization
