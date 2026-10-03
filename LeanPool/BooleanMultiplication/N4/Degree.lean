/-
Copyright (c) 2026 Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Morse
-/
module

public import LeanPool.BooleanMultiplication.N4.Normalization

/-!
# Homogeneous degree and seed predicates

The Boolean ANF multiplication lowers degree when variables repeat, so the
formal development records degree by coefficients rather than by a polynomial
quotient API.  This file supplies the high-part predicates used by the seed
and defect arguments.
-/

public section

namespace UnrestrictedBooleanMul
namespace N4

noncomputable section

/-- Keep exactly the monomials of cardinality `d`. -/
def homogeneousPart {m : Nat} (d : Nat) (p : ANF m) : ANF m :=
  MonoidAlgebra.ofCoeff
    (Finsupp.filter (fun s : Monomial m => s.vars.card = d) p.coeff)

@[simp] theorem homogeneousPart_coeff {m d : Nat} (p : ANF m) (s : Monomial m) :
    (homogeneousPart d p).coeff s = if s.vars.card = d then p.coeff s else 0 :=
  Finsupp.filter_apply _ _ _

/-- Linear projection onto the squarefree monomials of exactly the specified degree. -/
def homogeneousProjection {m : Nat} (d : Nat) : ANF m →ₗ[F₂] ANF m where
  toFun := homogeneousPart d
  map_add' p q := by
    apply MonoidAlgebra.coeff_injective
    ext s
    simp [homogeneousPart]
  map_smul' a p := by
    apply MonoidAlgebra.coeff_injective
    ext s
    simp [homogeneousPart]

/-- The ANF has no monomial above degree `d`. -/
@[expose]
def DegreeLE {m : Nat} (d : Nat) (p : ANF m) : Prop :=
  ∀ s : Monomial m, d < s.vars.card → p.coeff s = 0

/-- Boolean ANF degree is subadditive under multiplication.  This uses only
the support inclusion for monoid algebras and
`card (s ∪ t) ≤ card s + card t`; repeated Boolean variables can lower,
but never raise, the degree. -/
theorem DegreeLE.mul {m d e : Nat} {p q : ANF m}
    (hp : DegreeLE d p) (hq : DegreeLE e q) :
    DegreeLE (d + e) (p * q) := by
  let D : Monomial m → Nat := fun s => s.vars.card
  have hpSup : p.coeff.support.sup D ≤ d := by
    apply Finset.sup_le
    intro s hs
    apply le_of_not_gt
    intro hsd
    exact (Finsupp.mem_support_iff.mp hs) (hp s hsd)
  have hqSup : q.coeff.support.sup D ≤ e := by
    apply Finset.sup_le
    intro s hs
    apply le_of_not_gt
    intro hse
    exact (Finsupp.mem_support_iff.mp hs) (hq s hse)
  have hmul :
      (p * q).coeff.support.sup D ≤
        p.coeff.support.sup D + q.coeff.support.sup D := by
    apply Finset.sup_le
    intro s hs
    have hs' := MonoidAlgebra.support_coeff_mul_subset p q hs
    rw [Finset.mem_mul] at hs'
    rcases hs' with ⟨u, hu, v, hv, rfl⟩
    calc
      D (u * v) ≤ D u + D v := Finset.card_union_le u.vars v.vars
      _ ≤ p.coeff.support.sup D + q.coeff.support.sup D :=
        Nat.add_le_add (Finset.le_sup hu) (Finset.le_sup hv)
  intro s hs
  by_contra hne
  have hmem : s ∈ (p * q).coeff.support :=
    Finsupp.mem_support_iff.mpr hne
  have hsSup : D s ≤ (p * q).coeff.support.sup D :=
    Finset.le_sup hmem
  have hdegree : D s ≤ d + e :=
    hsSup.trans (hmul.trans (Nat.add_le_add hpSup hqSup))
  exact (Nat.not_le_of_lt hs) hdegree

theorem DegreeLE.mono {m d e : Nat} {p : ANF m}
    (hp : DegreeLE d p) (hde : d ≤ e) : DegreeLE e p := by
  intro s hes
  exact hp s (lt_of_le_of_lt hde hes)

/-- There is a genuinely high monomial (degree at least three). -/
@[expose]
def HasNonzeroHigh {m : Nat} (p : ANF m) : Prop :=
  ∃ s : Monomial m, 3 ≤ s.vars.card ∧ p.coeff s ≠ 0

/-- The degree-four homogeneous component vanishes. -/
def QuarticFree {m : Nat} (p : ANF m) : Prop :=
  homogeneousPart 4 p = 0

/-- A seed whose only possible nonzero high component is cubic. -/
@[expose]
def IsCubicSeed {m : Nat} (p : ANF m) : Prop :=
  HasNonzeroHigh p ∧ DegreeLE 3 p

/-- The fourth gate has a nonzero component of degree greater than two. -/
@[expose]
def SeedHighNonzero (C : Circuit 8 8) : Prop := HasNonzeroHigh (C.gate 3)
/-- The fourth gate has no degree-four homogeneous component. -/
def SeedQuarticFree (C : Circuit 8 8) : Prop := QuarticFree (C.gate 3)
/-- The fourth gate is a cubic seed. -/
@[expose]
def CubicSeedState (C : Circuit 8 8) : Prop := IsCubicSeed (C.gate 3)

/-- The linear subspace of Boolean ANFs of degree at most two. -/
@[expose]
def quadraticANFSpace (m : Nat) : Submodule F₂ (ANF m) where
  carrier := {p | DegreeLE 2 p}
  zero_mem' := by intro s hs; simp
  add_mem' := by
    intro p q hp hq s hs
    simp [hp s hs, hq s hs]
  smul_mem' := by
    intro a p hp s hs
    simp [hp s hs]

theorem mem_quadraticANFSpace_iff {m : Nat} (p : ANF m) :
    p ∈ quadraticANFSpace m ↔ ¬ HasNonzeroHigh p := by
  constructor
  · intro hp
    rintro ⟨s, hs, hne⟩
    exact hne (hp s (by omega))
  · intro hp s hs
    by_contra hne
    exact hp ⟨s, by omega, hne⟩

theorem affine_coeff_zero_of_two_le {m : Nat} {p : ANF m}
    (hp : p ∈ affine m) (s : Monomial m) (hs : 2 ≤ s.vars.card) :
    p.coeff s = 0 := by
  refine Submodule.span_induction (p := fun p _ => p.coeff s = 0) ?_ ?_ ?_ ?_ hp
  · intro q hq
    rcases hq with hq | hq
    · have hqone : q = 1 := by simpa only [Set.mem_singleton_iff] using hq
      subst q
      have hne : (1 : Monomial m) ≠ s := by
        intro h
        have hc := congrArg (fun t : Monomial m => t.vars.card) h
        simp at hc
        omega
      rw [MonoidAlgebra.one_def]
      simp [hne]
    · rcases hq with ⟨i, rfl⟩
      have hne : (⟨{i}⟩ : Monomial m) ≠ s := by
        intro h
        have hc := congrArg (fun t : Monomial m => t.vars.card) h
        simp at hc
        omega
      simp [X, monomial, hne]
  · simp
  · intro p q _hp _hq hpq hqq
    simp [hpq, hqq]
  · intro c p _hp hpq
    simp [hpq]

theorem affine_coeff_zero_of_three_le {m : Nat} {p : ANF m}
    (hp : p ∈ affine m) (s : Monomial m) (hs : 3 ≤ s.vars.card) :
    p.coeff s = 0 :=
  affine_coeff_zero_of_two_le hp s (by omega)

theorem aVar_ne_bVar_index (i j : Fin 4) :
    (⟨i.val, by omega⟩ : Fin 8) ≠ ⟨4 + j.val, by omega⟩ := by
  apply Fin.ne_of_lt
  change i.val < 4 + j.val
  omega

theorem coeff_aVar_mul_bVar_zero_of_three_le (i j : Fin 4)
    (s : Monomial 8) (hs : 3 ≤ s.vars.card) :
    (aVar 4 i * bVar 4 j).coeff s = 0 := by
  let ai : Fin 8 := ⟨i.val, by omega⟩
  let bj : Fin 8 := ⟨4 + j.val, by omega⟩
  have hij : ai ≠ bj := by
    simpa [ai, bj] using aVar_ne_bVar_index i j
  have hcard : ({ai, bj} : Finset (Fin 8)).card = 2 := by simp [hij]
  have hne : ({ai, bj} : Finset (Fin 8)) ≠ s.vars := by
    intro h
    have hc := congrArg Finset.card h
    rw [hcard] at hc
    omega
  have hne' :
      ({(⟨i.val, by omega⟩ : Fin 8), (⟨4 + j.val, by omega⟩ : Fin 8)} :
        Finset (Fin 8)) ≠ s.vars := by
    simpa [ai, bj] using hne
  simp only [aVar, bVar, X, monomial_mul, Finset.singleton_union]
  rw [coeff_monomial]
  simp [hne']

theorem Mul_four_coeff_zero_of_three_le (i : Fin 7)
    (s : Monomial 8) (hs : 3 ≤ s.vars.card) :
    (Mul 4 i).coeff s = 0 := by
  unfold Mul mulCoefficient
  simp only [MonoidAlgebra.coeff_sum]
  change (∑ x : Fin 4, ∑ y : Fin 4,
    (if x.val + y.val = i.val then aVar 4 x * bVar 4 y else 0).coeff s) = 0
  apply Finset.sum_eq_zero
  intro x _hx
  apply Finset.sum_eq_zero
  intro y _hy
  split
  · exact coeff_aVar_mul_bVar_zero_of_three_le x y s hs
  · simp

theorem mulTarget_coeff_zero_of_three_le {p : ANF 8}
    (hp : p ∈ mulTarget 4) (s : Monomial 8) (hs : 3 ≤ s.vars.card) :
    p.coeff s = 0 := by
  refine Submodule.span_induction (p := fun p _ => p.coeff s = 0) ?_ ?_ ?_ ?_ hp
  · rintro p ⟨i, rfl⟩
    exact Mul_four_coeff_zero_of_three_le i s hs
  · simp
  · intro p q _hp _hq hpq hqq
    simp [hpq, hqq]
  · intro c p _hp hpq
    simp [hpq]

theorem targetAmbient_coeff_zero_of_three_le {p : ANF 8}
    (hp : p ∈ targetAmbient 8 (mulTarget 4))
    (s : Monomial 8) (hs : 3 ≤ s.vars.card) : p.coeff s = 0 := by
  rcases Submodule.mem_sup.mp hp with ⟨a, ha, t, ht, rfl⟩
  simp [affine_coeff_zero_of_three_le ha s hs, mulTarget_coeff_zero_of_three_le ht s hs]

theorem targetAmbient_le_quadraticANFSpace :
    targetAmbient 8 (mulTarget 4) ≤ quadraticANFSpace 8 := by
  intro p hp s hs
  exact targetAmbient_coeff_zero_of_three_le hp s (by omega)

theorem affine_le_quadraticANFSpace {m : Nat} :
    affine m ≤ quadraticANFSpace m := by
  intro p hp s hs
  exact affine_coeff_zero_of_three_le hp s (by omega)

theorem wireSpace_le_quadratic_of_prefix {m r j : Nat}
    (g : Fin r → ANF m)
    (hgate : ∀ i : Fin r, i.val < j → g i ∈ quadraticANFSpace m) :
    wireSpace g j ≤ quadraticANFSpace m := by
  rw [wireSpace]
  apply sup_le affine_le_quadraticANFSpace
  rw [Submodule.span_le]
  rintro p ⟨i, hi, rfl⟩
  exact hgate i hi

/-- Adjoining a first high-degree vector to an entirely quadratic state cannot
create a new direction in a quadratic ambient target. -/
theorem inf_unchanged_of_first_high
    (V A : Submodule F₂ (ANF 8)) (g : ANF 8)
    (hV : V ≤ quadraticANFSpace 8)
    (hA : A ≤ quadraticANFSpace 8)
    (hg : g ∉ quadraticANFSpace 8) :
    (V ⊔ Submodule.span F₂ {g}) ⊓ A = V ⊓ A := by
  apply le_antisymm
  · rintro p ⟨hpVA, hpA⟩
    rcases Submodule.mem_sup.mp hpVA with ⟨v, hv, w, hw, rfl⟩
    rcases Submodule.mem_span_singleton.mp hw with ⟨a, rfl⟩
    rcases f2_eq_zero_or_one a with ha | ha
    · subst a
      have hpV : v + (0 : F₂) • g ∈ V := by
        rw [zero_smul, add_zero]
        exact hv
      exact ⟨hpV, hpA⟩
    · subst a
      exfalso
      apply hg
      have hvlow := hV hv
      have hsumlow : v + g ∈ quadraticANFSpace 8 := by
        apply hA
        have hpA' : v + g ∈ A := by
          rw [← one_smul F₂ g]
          exact hpA
        exact hpA'
      have : (v + g) + v ∈ quadraticANFSpace 8 :=
        Submodule.add_mem _ hsumlow hvlow
      have heq : (v + g) + v = g := by
        calc
          (v + g) + v = (v + v) + g := by ac_rfl
          _ = g := by simp
      rwa [heq] at this
  · exact inf_le_inf le_sup_left le_rfl

theorem first_high_gate_not_useful (C : Circuit 8 8) (j : Fin 8)
    (hprev : ∀ i : Fin 8, i.val < j.val →
      C.gate i ∈ quadraticANFSpace 8)
    (hhigh : HasNonzeroHigh (C.gate j)) :
    ¬ UsefulAt C (mulTarget 4) j := by
  intro huse
  have hV := wireSpace_le_quadratic_of_prefix C.gate hprev
  have hg : C.gate j ∉ quadraticANFSpace 8 := by
    rw [mem_quadraticANFSpace_iff]
    exact fun hn => hn hhigh
  have hinter := inf_unchanged_of_first_high
    (circuitFlag C j.val) (targetAmbient 8 (mulTarget 4)) (C.gate j)
    hV targetAmbient_le_quadraticANFSpace hg
  have hstep : circuitFlag C (j.val + 1) =
      circuitFlag C j.val ⊔ Submodule.span F₂ {C.gate j} := by
    rw [circuitFlag, wireSpace_succ C.gate j.isLt]
    congr 2
  unfold UsefulAt at huse
  rw [hstep] at huse
  unfold flagTargetRank at huse
  rw [hinter] at huse
  omega

/-- If the normalized seed were quadratic, every later gate would remain
quadratic: the first high suffix gate would be a forbidden second non-useful
gate. -/
theorem normalized_all_gates_quadratic_of_seed_not_high {C : Circuit 8 8}
    (hNorm : NormalizedEight C) (hseed : ¬ SeedHighNonzero C) :
    ∀ i : Fin 8, C.gate i ∈ quadraticANFSpace 8 := by
  have target_low (c : TargetCoeff) :
      targetANF c ∈ quadraticANFSpace 8 := by
    rw [mem_quadraticANFSpace_iff]
    rintro ⟨s, hs, hcoeff⟩
    exact hcoeff (mulTarget_coeff_zero_of_three_le
      (targetANF_mem_mulTarget c) s hs)
  have h0 : C.gate 0 ∈ quadraticANFSpace 8 := by
    rw [hNorm.gate_zero]
    exact target_low rZeroCoeff
  have h1 : C.gate 1 ∈ quadraticANFSpace 8 := by
    rw [hNorm.gate_one]
    exact target_low rOneCoeff
  have h2 : C.gate 2 ∈ quadraticANFSpace 8 := by
    rw [hNorm.gate_infinity]
    exact target_low rInfinityCoeff
  have h3 : C.gate 3 ∈ quadraticANFSpace 8 := by
    rw [mem_quadraticANFSpace_iff]
    exact hseed
  have next_low (j : Fin 8) (hj : 4 ≤ j.val)
      (hprev : ∀ i : Fin 8, i.val < j.val →
        C.gate i ∈ quadraticANFSpace 8) :
      C.gate j ∈ quadraticANFSpace 8 := by
    rw [mem_quadraticANFSpace_iff]
    intro hhigh
    exact first_high_gate_not_useful C j hprev hhigh
      (hNorm.suffix_useful j hj)
  have h4 : C.gate 4 ∈ quadraticANFSpace 8 := next_low 4 (by decide) (by
    intro i hi
    fin_cases i <;> simp_all)
  have h5 : C.gate 5 ∈ quadraticANFSpace 8 := next_low 5 (by decide) (by
    intro i hi
    fin_cases i <;> simp_all)
  have h6 : C.gate 6 ∈ quadraticANFSpace 8 := next_low 6 (by decide) (by
    intro i hi
    fin_cases i <;> simp_all)
  have h7 : C.gate 7 ∈ quadraticANFSpace 8 := next_low 7 (by decide) (by
    intro i hi
    fin_cases i <;> simp_all)
  intro i
  fin_cases i <;> assumption

theorem not_high_of_mem_targetAmbient {p : ANF 8}
    (hp : p ∈ targetAmbient 8 (mulTarget 4)) : ¬ HasNonzeroHigh p := by
  rintro ⟨s, hs, hcoeff⟩
  exact hcoeff (targetAmbient_coeff_zero_of_three_le hp s hs)

/-- Zero defect means the entire final wire space lies in `Aff + T`; in
particular every gate output has degree at most two. -/
theorem finalWire_le_targetAmbient_of_defect_zero (C : Circuit 8 8)
    (hdef : flagDefectRank C.finalWire (mulTarget 4) = 0) :
    C.finalWire ≤ targetAmbient 8 (mulTarget 4) := by
  have hdim : Module.finrank F₂ C.finalWire ≤
      Module.finrank F₂ ↥(C.finalWire ⊓ targetAmbient 8 (mulTarget 4)) := by
    unfold flagDefectRank at hdef
    exact Nat.sub_eq_zero_iff_le.mp hdef
  have heq : C.finalWire ⊓ targetAmbient 8 (mulTarget 4) = C.finalWire :=
    Submodule.eq_of_le_of_finrank_le
      (show C.finalWire ⊓ targetAmbient 8 (mulTarget 4) ≤ C.finalWire from inf_le_left)
      hdim
  intro p hp
  have : p ∈ C.finalWire ⊓ targetAmbient 8 (mulTarget 4) := by
    rw [heq]
    exact hp
  exact this.2

theorem gate_not_high_of_defect_zero (C : Circuit 8 8)
    (hdef : flagDefectRank C.finalWire (mulTarget 4) = 0) (i : Fin 8) :
    ¬ HasNonzeroHigh (C.gate i) := by
  apply not_high_of_mem_targetAmbient
  exact finalWire_le_targetAmbient_of_defect_zero C hdef (gate_mem_finalWire C i)

end

end N4
end UnrestrictedBooleanMul
