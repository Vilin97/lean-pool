/-
Copyright (c) 2026 Madeleine Gignoux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Madeleine Gignoux
-/

import Mathlib.Data.Fintype.Defs
import LeanPool.Lean4GlCoalgebras.Interpolation.Interpolants
import LeanPool.Lean4GlCoalgebras.Split.ProofTransformations

/-! # Partial Left Interpolation Proofs

All of the left and right partial interpolation proofs, split apart based on rule application. These
are split apart since otherwise the file runs very slow. -/

namespace Lean4GlCoalgebras

open Split

/-- Given a node `x`, defines what the root of the left interpolation proof should look like,
    i.e. `f(x)ˡ ∣ ιₓ` in on paper work. -/
noncomputable def leftInterpolantSequent {𝕏 : Split.Proof} [fin_X : Fintype 𝕏.X]
    (x : 𝕏.X) : SplitSequent :=
  {Sum.inr (interpolant 𝕏 (at (encodeVar x)))} ∪
    SplitSequent.filterLeft (f (r 𝕏.α x))

/-- Given a node `x`, defines what the same as above except for the equation `σ(χₓ)`,
    helpful for cases where the interpolant isn't defined by the interpolants of its premise nodes.,
    i.e. `f(x)ˡ ∣ σ(χₓ)` in on paper work. -/
noncomputable def leftEquationSequent {𝕏 : Proof} [fin_X : Fintype 𝕏.X]
    (x : 𝕏.X) : SplitSequent :=
  {Sum.inr (interpolant 𝕏 (equation x))} ∪
    SplitSequent.filterLeft (f (r 𝕏.α x))

/-- Given a node `x`, defines what the root of the right interpolation proof should look like,
    i.e. `~ιₓ ∣ f(x)ʳ ` in on paper work. -/
noncomputable def rightInterpolantSequent {𝕏 : Proof} [fin_X : Fintype 𝕏.X]
    (x : 𝕏.X) : SplitSequent :=
  {Sum.inl (~ (interpolant 𝕏 (at (encodeVar x))))} ∪
    SplitSequent.filterRight (f (r 𝕏.α x))

/-- Given a node `x`, defines what the same as above except for the equation `σ(χₓ)`,
    helpful for cases where the interpolant isn't defined by the interpolants of its premise nodes.,
    i.e. `~σ(χₓ) ∣ f(x)ʳ ` in on paper work. -/
noncomputable def rightEquationSequent {𝕏 : Proof} [fin_X : Fintype 𝕏.X]
    (x : 𝕏.X) : SplitSequent :=
  {Sum.inl (~ (interpolant 𝕏 (equation x)))} ∪
    SplitSequent.filterRight (f (r 𝕏.α x))

/- ## From split system to extended system -/
/-- Transforms rule applications in the split system into applications in the extended system. -/
def splitToExt {𝕏 : Split.Proof} {x : 𝕏.X} {τ} : Split.RuleApp → Ext.RuleApp x τ
  | .topₗ _ in_Δ => .topₗ _ in_Δ
  | .topᵣ _ in_Δ => .topᵣ _ in_Δ
  | .axₗₗ _ _ in_Δ => .axₗₗ _ _ in_Δ
  | .axₗᵣ _ _ in_Δ => .axₗᵣ _ _ in_Δ
  | .axᵣₗ _ _ in_Δ => .axᵣₗ _ _ in_Δ
  | .axᵣᵣ _ _ in_Δ => .axᵣᵣ _ _ in_Δ
  | .orₗ _ _ _ in_Δ => .orₗ _ _ _ in_Δ
  | .orᵣ _ _ _ in_Δ => .orᵣ _ _ _ in_Δ
  | .andₗ _ _ _ in_Δ => .andₗ _ _ _ in_Δ
  | .andᵣ _ _ _ in_Δ => .andᵣ _ _ _ in_Δ
  | .boxₗ _ _ in_Δ => .boxₗ _ _ in_Δ
  | .boxᵣ _ _ in_Δ => .boxᵣ _ _ in_Δ

/-- Auxiliary declaration used in the GL coalgebra development. -/
noncomputable def partialLeftTopₗ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X)
    {Δ in_Δ} (rule_def : r 𝕏.α x = RuleApp.topₗ Δ in_Δ)
  : Ext.PreProof x (@leftInterpolantSequent 𝕏 _) where
    X := Unit
    α u := ⟨Ext.RuleApp.topₗ (leftEquationSequent x) (by
      exact Finset.mem_union_right _ (by simpa [SplitSequent.filterLeft, rule_def, f]
        using in_Δ)), {}⟩
    step u := by simp [Ext.r, Ext.p]
    root := ()
    path u f := by exact False.elim (by simpa [Ext.edge, Ext.p] using f.2)

/-- Auxiliary declaration used in the GL coalgebra development. -/
noncomputable def partialLeftTopᵣ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X)
    {Δ in_Δ} (rule_def : r 𝕏.α x = RuleApp.topᵣ Δ in_Δ)
   : Ext.PreProof x (@leftInterpolantSequent 𝕏 _) where
    X := Unit
    α u := ⟨Ext.RuleApp.topᵣ (leftEquationSequent x) (by
      simp [leftEquationSequent, equation, rule_def] -- why not able to simp with rule here
      split <;> simp_all [interpolant, partial_] -- wow, do not forget about split!!!
      ), {}⟩
    step := by intro u; simp [Ext.r, Ext.p]
    root := ()
    path u f := by exact False.elim (by simpa [Ext.edge, Ext.p] using f.2)

/-- Auxiliary declaration used in the GL coalgebra development. -/
noncomputable def partialLeftAxₗₗ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X)
    {Δ n in_Δ} (rule_def : r 𝕏.α x = RuleApp.axₗₗ Δ n in_Δ)
  : Ext.PreProof x (@leftInterpolantSequent 𝕏 _) where
    X := Unit
    α u := ⟨Ext.RuleApp.axₗₗ (leftEquationSequent x) n (by
      simp [leftEquationSequent, rule_def, f, in_Δ]), {}⟩
    step := by intro u; simp [Ext.r, Ext.p]
    root := ()
    path u f := by exact False.elim (by simpa [Ext.edge, Ext.p] using f.2)

/-- Auxiliary declaration used in the GL coalgebra development. -/
noncomputable def partialLeftAxₗᵣ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X)
    {Δ n in_Δ} (rule_def : r 𝕏.α x = RuleApp.axₗᵣ Δ n in_Δ)
  : Ext.PreProof x (@leftInterpolantSequent 𝕏 _) where
    X := Unit
    α u := ⟨Ext.RuleApp.axₗᵣ (leftEquationSequent x) n (by
      simp only [leftEquationSequent, SplitSequent.filterLeft, Bool.false_eq_true, f,
        rule_def, Finset.singleton_union, Finset.mem_insert, reduceCtorEq,
        Finset.mem_filter, in_Δ, and_self, or_true, Sum.inr.injEq, and_false,
        or_false, true_and]
      simp only [interpolant, equation]
      split <;> simp_all only [RuleApp.axₗᵣ.injEq, reduceCtorEq]
      apply partial_const
      simp only [Formula.vocab, Finset.mem_singleton, Finset.mem_image, not_exists,
        not_and, forall_eq]
      intro _ _
      apply at_in_not_encodeVar
      rw [Proof.Sequent]
      apply Finset.mem_biUnion.mpr
      use x
      constructor
      · exact Fintype.complete x
      · apply Finset.mem_image.mpr
        use Sum.inl (at n)
        constructor
        · convert in_Δ.1
          simp_all [f]
        · rfl
      ), {}⟩
    step := by intro u; simp [Ext.r, Ext.p]
    root := ()
    path u f := by exact False.elim (by simpa [Ext.edge, Ext.p] using f.2)

/-- Auxiliary declaration used in the GL coalgebra development. -/
noncomputable def partialLeftAxᵣₗ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X)
    {Δ n in_Δ} (rule_def : r 𝕏.α x = RuleApp.axᵣₗ Δ n in_Δ)
  : Ext.PreProof x (@leftInterpolantSequent 𝕏 _) where
    X := Unit
    α u := ⟨Ext.RuleApp.axᵣₗ (leftEquationSequent x) n (by
      simp only [leftEquationSequent, rule_def, f, Finset.mem_union, Finset.mem_singleton,
        SplitSequent.filterLeft, Finset.mem_filter, reduceCtorEq, and_false, false_or,
        or_false, Sum.inr.injEq, in_Δ, and_true]
      simp only [interpolant, equation]
      split <;> simp_all only [RuleApp.axᵣₗ.injEq, reduceCtorEq]
      apply partial_const
      simp only [Formula.vocab, Finset.mem_singleton, Finset.mem_image, not_exists,
        not_and, forall_eq]
      intro _ _
      apply at_in_not_encodeVar
      rw [Proof.Sequent]
      apply Finset.mem_biUnion.mpr
      use x
      constructor
      · exact Fintype.complete x
      · apply Finset.mem_image.mpr
        use Sum.inr (at n)
        constructor
        · convert in_Δ.1
          simp_all [f]
        · rfl
      ), {}⟩
    step := by intro u; simp [Ext.r, Ext.p]
    root := ()
    path u f := by exact False.elim (by simpa [Ext.edge, Ext.p] using f.2)

/-- Auxiliary declaration used in the GL coalgebra development. -/
noncomputable def partialLeftAxᵣᵣ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X)
    {Δ n in_Δ} (rule_def : r 𝕏.α x = RuleApp.axᵣᵣ Δ n in_Δ)
  : Ext.PreProof x (@leftInterpolantSequent 𝕏 _) where
    X := Unit
    α u := ⟨Ext.RuleApp.topᵣ (leftEquationSequent x) (by
      simp [leftEquationSequent, rule_def, f, equation]
      split <;> simp_all [interpolant, partial_]
      ), {}⟩
    step := by intro u; simp [Ext.r, Ext.p]
    root := ()
    path u f := by exact False.elim (by simpa [Ext.edge, Ext.p] using f.2)

/-- Auxiliary declaration used in the GL coalgebra development. -/
noncomputable def partialLeftOrₗ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X)
    {Δ φ ψ in_Δ} (rule_def : r 𝕏.α x = RuleApp.orₗ Δ φ ψ in_Δ)
: Ext.PreProof x (@leftInterpolantSequent 𝕏 _) :=
    match p_def : p 𝕏.α x with
      | [y] =>
        have interpolant_eq :
            interpolant 𝕏 (equation x) = interpolant 𝕏 (at encodeVar y) := by
          rw [equation]
          split <;> simp_all
        { X := Fin 2
          α | 0 => ⟨Ext.RuleApp.orₗ (leftEquationSequent x) φ ψ (by
              simp [leftEquationSequent, rule_def, f, in_Δ]), [1]⟩
            | 1 => ⟨Ext.RuleApp.pre y (by simp [p_def]), {}⟩
          step := by
            have 𝕏_h := 𝕏.step x
            simp only [rule_def, p_def, List.map_cons, List.map_nil, List.cons.injEq,
              and_true, fₙ_alternate] at 𝕏_h
            intro n
            match n with
              | 0 =>
                simp [Ext.r, Ext.p, Ext.T, Ext.f, Ext.fₙ, Ext.fₚ,
                  leftInterpolantSequent, leftEquationSequent, rule_def, 𝕏_h,
                  interpolant_eq]
                aesop -- big aesop
              | 1 =>
                simp [Ext.r, Ext.p]
          root := 0
          path z f := by exfalso; simp [Ext.edge, Ext.p] at f; grind}
        | [] => by have := 𝕏.step x; simp [rule_def] at this; simp_all
        | y :: z :: l => by have := 𝕏.step x; simp [rule_def] at this; simp_all

/-- Auxiliary declaration used in the GL coalgebra development. -/
noncomputable def partialLeftOrᵣ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X)
    {Δ φ ψ in_Δ} (rule_def : r 𝕏.α x = RuleApp.orᵣ Δ φ ψ in_Δ)
  : Ext.PreProof x (@leftInterpolantSequent 𝕏 _) :=
  match p_def : p 𝕏.α x with
    | [y] =>
      have interpolant_eq : interpolant 𝕏 (equation x) = interpolant 𝕏 (at encodeVar y) := by
        rw [equation]
        split <;> simp_all
    { X := Unit
      α u := ⟨Ext.RuleApp.pre y (by simp [p_def]), {}⟩
      step := by simp [Ext.r, Ext.p]
      root := ()
      path z f := by exfalso; simp [Ext.edge, Ext.p] at f; grind}
    | [] => by have := 𝕏.step x; simp [rule_def] at this; simp_all
    | _ :: _ :: _ => by have := 𝕏.step x; simp [rule_def] at this; simp_all

/-- Auxiliary declaration used in the GL coalgebra development. -/
noncomputable def partialLeftAndₗ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X)
    {Δ φ ψ in_Δ} (rule_def : r 𝕏.α x = RuleApp.andₗ Δ φ ψ in_Δ)
  : Ext.PreProof x (@leftInterpolantSequent 𝕏 _) :=
  match p_def : p 𝕏.α x with
  | [y,z] =>
    have interpolant_eq :
        interpolant 𝕏 (equation x) =
          (interpolant 𝕏 (at encodeVar y) v interpolant 𝕏 (at encodeVar z)) := by
      rw [equation]
      split <;> simp_all [interpolant, partial_, encodeVar]
    if eq : interpolant 𝕏 (at encodeVar y) = interpolant 𝕏 (at encodeVar z)
    then {
    X := Fin 4
    α | 0 =>
        ⟨Ext.RuleApp.orᵣ (leftEquationSequent x)
          (interpolant 𝕏 (at encodeVar y)) (interpolant 𝕏 (at encodeVar z))
          (by simp [leftEquationSequent, rule_def, f, interpolant_eq]), [1]⟩
      | 1 =>
        ⟨Ext.RuleApp.andₗ
          (((leftEquationSequent x) \ {Sum.inr <| interpolant 𝕏 (equation x)}) ∪
            {(Sum.inr <| interpolant 𝕏 (at encodeVar y)),
              Sum.inr <| (interpolant 𝕏 (at encodeVar z))})
          φ ψ (by simp [leftEquationSequent, rule_def, f, interpolant_eq, in_Δ]),
          [2,3]⟩
      | 2 => ⟨Ext.RuleApp.pre y (by simp [p_def]), {}⟩
      | 3 => ⟨Ext.RuleApp.pre z (by simp [p_def]), {}⟩
    step
      | 0 => by
        simp [Ext.r, Ext.p, leftEquationSequent, rule_def, f, interpolant_eq, Ext.f,
          Ext.fₙ_alternate]
      | 1 => by
        have 𝕏_h := 𝕏.step x
        simp only [rule_def, p_def, List.map_cons, List.map_nil, List.cons.injEq,
          and_true, fₙ_alternate] at 𝕏_h
        simp only [Ext.r, leftEquationSequent, interpolant_eq, SplitSequent.filterLeft,
          Bool.false_eq_true, rule_def, Finset.singleton_union, Finset.union_insert,
          Finset.union_singleton, Ext.f, Ext.T, Fin.isValue, List.empty_eq,
          leftInterpolantSequent, Ext.p, List.map_cons, 𝕏_h, List.map_nil,
          Ext.fₙ_alternate, List.cons.injEq, and_true]
        constructor <;> ext <;> simp [f] <;> aesop
      | 2 => by simp [Ext.r, Ext.p]
      | 3 => by simp [Ext.r, Ext.p]
    root := 0
    path z f := by exfalso; simp [Ext.edge, Ext.p] at f; grind}
    else {
    X := Fin 6
    α | 0 =>
        ⟨Ext.RuleApp.orᵣ (leftEquationSequent x)
          (interpolant 𝕏 (at encodeVar y)) (interpolant 𝕏 (at encodeVar z))
          (by simp [leftEquationSequent, rule_def, f, interpolant_eq]), [1]⟩
      | 1 =>
        ⟨Ext.RuleApp.andₗ
          (((leftEquationSequent x) \ {Sum.inr <| interpolant 𝕏 (equation x)}) ∪
            {(Sum.inr <| interpolant 𝕏 (at encodeVar y)),
              Sum.inr <| (interpolant 𝕏 (at encodeVar z))})
          φ ψ (by simp [leftEquationSequent, rule_def, f, interpolant_eq, in_Δ]),
          [2,3]⟩
      | 2 =>
        ⟨Ext.RuleApp.wkᵣ
          (((((leftEquationSequent x) \ {Sum.inr <| interpolant 𝕏 (equation x)}) ∪
              {Sum.inr <| interpolant 𝕏 (at encodeVar y),
                Sum.inr <| (interpolant 𝕏 (at encodeVar z))}) \
            {Sum.inl (φ & ψ)}) ∪ {Sum.inl φ})
          (interpolant 𝕏 (at encodeVar z))
          (by simp [leftEquationSequent, rule_def, f, interpolant_eq]), [4]⟩
      | 3 =>
        ⟨Ext.RuleApp.wkᵣ
          (((((leftEquationSequent x) \ {Sum.inr <| interpolant 𝕏 (equation x)}) ∪
              {Sum.inr <| interpolant 𝕏 (at encodeVar y),
                Sum.inr <| (interpolant 𝕏 (at encodeVar z))}) \
            {Sum.inl (φ & ψ)}) ∪ {Sum.inl ψ})
          (interpolant 𝕏 (at encodeVar y))
          (by simp [leftEquationSequent, rule_def, f, interpolant_eq]), [5]⟩
      | 4 => ⟨Ext.RuleApp.pre y (by simp [p_def]), {}⟩
      | 5 => ⟨Ext.RuleApp.pre z (by simp [p_def]), {}⟩
    step
      | 0 => by
        simp [Ext.r, Ext.p, leftEquationSequent, rule_def, f, interpolant_eq, Ext.f,
          Ext.fₙ_alternate]
      | 1 => by
        simp [Ext.r, Ext.p, leftEquationSequent, rule_def, f, interpolant_eq, Ext.f,
          Ext.fₙ_alternate]
      | 2 => by
        have 𝕏_h := 𝕏.step x
        simp only [rule_def, p_def, List.map_cons, List.map_nil, List.cons.injEq,
          and_true, fₙ_alternate] at 𝕏_h
        simp only [Ext.r, leftEquationSequent, interpolant_eq, SplitSequent.filterLeft,
          Bool.false_eq_true, rule_def, Finset.singleton_union, Finset.union_insert,
          Finset.union_singleton, Ext.f, Ext.T, Fin.isValue, List.empty_eq,
          leftInterpolantSequent, Ext.p, List.map_cons, 𝕏_h, List.map_nil,
          Ext.fₙ_alternate, List.cons.injEq, and_true]
        ext; simp [f]; aesop
      | 3 => by
        have 𝕏_h := 𝕏.step x
        simp only [rule_def, p_def, List.map_cons, List.map_nil, List.cons.injEq,
          and_true, fₙ_alternate] at 𝕏_h
        simp only [Ext.r, leftEquationSequent, interpolant_eq, SplitSequent.filterLeft,
          Bool.false_eq_true, rule_def, Finset.singleton_union, Finset.union_insert,
          Finset.union_singleton, Ext.f, Ext.T, Fin.isValue, List.empty_eq,
          leftInterpolantSequent, Ext.p, List.map_cons, 𝕏_h, List.map_nil,
          Ext.fₙ_alternate, List.cons.injEq, and_true]
        ext; simp [f]; aesop
      | 4 => by simp [Ext.r, Ext.p]
      | 5 => by simp [Ext.r, Ext.p]
    root := 0
    path z f := by exfalso; simp [Ext.edge, Ext.p] at f; grind}
  | [] => by have := 𝕏.step x; simp [rule_def] at this; simp_all
  | [_] => by have := 𝕏.step x; simp [rule_def] at this; simp_all
  | _ :: _ :: _ :: _ => by have := 𝕏.step x; simp [rule_def] at this; simp_all

/-- Auxiliary declaration used in the GL coalgebra development. -/
noncomputable def partialLeftAndᵣ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X)
    {Δ φ ψ in_Δ} (rule_def : r 𝕏.α x = RuleApp.andᵣ Δ φ ψ in_Δ)
  : Ext.PreProof x (@leftInterpolantSequent 𝕏 _) :=
  match p_def : p 𝕏.α x with
  | [y,z] =>
    have interpolant_eq :
        interpolant 𝕏 (equation x) =
          (interpolant 𝕏 (at encodeVar y) & interpolant 𝕏 (at encodeVar z)) := by
      rw [equation]
      split <;> simp_all [interpolant, partial_, encodeVar]
    { X := Fin 3
      α | 0 =>
          ⟨Ext.RuleApp.andᵣ (leftEquationSequent x)
            (interpolant 𝕏 (at encodeVar y)) (interpolant 𝕏 (at encodeVar z))
            (by simp [leftEquationSequent, rule_def, f, interpolant_eq]), [1,2]⟩
        | 1 => ⟨Ext.RuleApp.pre y (by simp [p_def]), {}⟩
        | 2 => ⟨Ext.RuleApp.pre z (by simp [p_def]), {}⟩
      step
        | 0 => by
          have 𝕏_h := 𝕏.step x
          simp only [rule_def, p_def, List.map_cons, List.map_nil, List.cons.injEq,
            and_true, fₙ_alternate] at 𝕏_h
          simp only [Ext.r, leftEquationSequent, interpolant_eq, SplitSequent.filterLeft,
            Bool.false_eq_true, rule_def, Finset.singleton_union, Ext.f, Ext.T, Fin.isValue,
            List.empty_eq, leftInterpolantSequent, Ext.p, List.map_cons, 𝕏_h,
            Finset.union_singleton, List.map_nil, Ext.fₙ_alternate, List.cons.injEq, and_true]
          constructor <;> ext <;> simp [f] <;> aesop
        | 1 => by simp [Ext.r, Ext.p]
        | 2 => by simp [Ext.r, Ext.p]
      root := 0
      path z f := by exfalso; simp [Ext.edge, Ext.p] at f; grind}
  | [] => by have := 𝕏.step x; simp [rule_def] at this; simp_all
  | [_] => by have := 𝕏.step x; simp [rule_def] at this; simp_all
  | _ :: _ :: _ :: _ => by have := 𝕏.step x; simp [rule_def] at this; simp_all

/-- Auxiliary declaration used in the GL coalgebra development. -/
noncomputable def partialLeftBoxₗ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X)
    {Δ φ in_Δ} (rule_def : r 𝕏.α x = RuleApp.boxₗ Δ φ in_Δ)
  : Ext.PreProof x (@leftInterpolantSequent 𝕏 _) :=
  match p_def : p 𝕏.α x with
  | [y] =>
    have interpolant_eq :
        interpolant 𝕏 (equation x) = ◇ (interpolant 𝕏 (at encodeVar y)) := by
      rw [equation]
      split <;> simp_all [interpolant, partial_, encodeVar]
    { X := Fin 3
      α | 0 =>
          ⟨Ext.RuleApp.boxₗ (leftEquationSequent x) φ (by
            simp [leftEquationSequent, rule_def, f, in_Δ]), [1]⟩
        | 1 =>
          ⟨Ext.RuleApp.wkᵣ
            (((leftEquationSequent x) \ {Sum.inl <| □ φ}).D ∪ {Sum.inl φ})
            (◇ (interpolant 𝕏 (at encodeVar y)))
            (by
              simp [leftEquationSequent, rule_def, f, interpolant_eq, SplitSequent.D,
                SplitFormula.isDiamond]), [2]⟩
        | 2 => ⟨Ext.RuleApp.pre y (by simp [p_def]), {}⟩
      step
        | 0 => by
          simp [Ext.r, Ext.p, leftEquationSequent, rule_def, f, interpolant_eq, Ext.f,
            Ext.fₙ_alternate]
        | 1 => by
          have 𝕏_h := 𝕏.step x
          simp only [rule_def, p_def, List.map_cons, List.map_nil, List.cons.injEq,
            and_true, fₙ_alternate] at 𝕏_h
          simp only [Ext.r, leftEquationSequent, interpolant_eq, SplitSequent.filterLeft,
            Bool.false_eq_true, rule_def, Finset.singleton_union, Finset.union_singleton,
            Ext.f, Ext.T, Fin.isValue, List.empty_eq, leftInterpolantSequent, Ext.p,
            List.map_cons, 𝕏_h, List.map_nil, Ext.fₙ_alternate, List.cons.injEq, and_true]
          ext ψ
          simp [f, SplitSequent.D, Finset.mem_sdiff]
          cases ψ <;> simp
          simp [SplitFormula.isDiamond]
          constructor <;> try tauto
          intro mp
          subst mp
          simp
          induction interpolant 𝕏 (at encodeVar y) <;> simp_all
        | 2 => by simp [Ext.r, Ext.p]
      root := 0
      path z f := by exfalso; simp [Ext.edge, Ext.p] at f; grind}
  | [] => by have := 𝕏.step x; simp [rule_def] at this; simp_all
  | _ :: _ :: _ => by have := 𝕏.step x; simp [rule_def] at this; simp_all

/-- Auxiliary declaration used in the GL coalgebra development. -/
noncomputable def partialLeftBoxᵣ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X)
    {Δ φ in_Δ} (rule_def : r 𝕏.α x = RuleApp.boxᵣ Δ φ in_Δ)
  : Ext.PreProof x (@leftInterpolantSequent 𝕏 _) :=
  match p_def : p 𝕏.α x with
  | [y] =>
    have interpolant_eq :
        interpolant 𝕏 (equation x) = □ (interpolant 𝕏 (at encodeVar y)) := by
      rw [equation]
      split <;> simp_all [interpolant, partial_, encodeVar]
    { X := Fin 2
      α | 0 =>
          ⟨Ext.RuleApp.boxᵣ (leftEquationSequent x) (interpolant 𝕏 (at encodeVar y))
            (by simp [leftEquationSequent, interpolant_eq]), [1]⟩
        | 1 => ⟨Ext.RuleApp.pre y (by simp [p_def]), {}⟩
      step
        | 0 => by
          have 𝕏_h := 𝕏.step x
          simp only [rule_def, p_def, List.map_cons, List.map_nil, List.cons.injEq,
            and_true, fₙ_alternate] at 𝕏_h
          simp only [Ext.r, leftEquationSequent, interpolant_eq, SplitSequent.filterLeft,
            Bool.false_eq_true, rule_def, Finset.singleton_union, Ext.f, Ext.T, Fin.isValue,
            List.empty_eq, leftInterpolantSequent, Ext.p, List.map_cons, 𝕏_h,
            Finset.union_singleton, List.map_nil, Ext.fₙ_alternate, List.cons.injEq, and_true]
          ext ψ
          simp [f, SplitSequent.D, Finset.mem_sdiff]
          cases ψ <;> simp
        | 1 => by simp [Ext.r, Ext.p]
      root := 0
      path z f := by exfalso; simp [Ext.edge, Ext.p] at f; grind}
  | [] => by have := 𝕏.step x; simp [rule_def] at this; simp_all
  | _ :: _ :: _ => by have := 𝕏.step x; simp [rule_def] at this; simp_all

/-- Defines the left partial interpolation proof `Lₓ`. -/
noncomputable def partialEquationLeft {𝕏 : Proof} [fin_X : Fintype 𝕏.X]
    (x : 𝕏.X) : Ext.PreProof x (@leftInterpolantSequent 𝕏 _) :=
  match rule_def : (r 𝕏.α x) with
    | .topₗ _ _ => partialLeftTopₗ x rule_def
    | .topᵣ _ _ => partialLeftTopᵣ x rule_def
    | .axₗₗ _ _ _ => partialLeftAxₗₗ x rule_def
    | .axₗᵣ _ _ _ => partialLeftAxₗᵣ x rule_def
    | .axᵣₗ _ _ _ => partialLeftAxᵣₗ x rule_def
    | .axᵣᵣ _ _ _ => partialLeftAxᵣᵣ x rule_def
    | .orₗ _ _ _ _ => partialLeftOrₗ x rule_def
    | .orᵣ _ _ _ _ => partialLeftOrᵣ x rule_def
    | .andₗ _ _ _ _ => partialLeftAndₗ x rule_def
    | .andᵣ _ _ _ _ => partialLeftAndᵣ x rule_def
    | .boxₗ _ _ _ => partialLeftBoxₗ x rule_def
    | .boxᵣ _ _ _ => partialLeftBoxᵣ x rule_def


/-- Auxiliary declaration used in the GL coalgebra development. -/
noncomputable def partialRightTopₗ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X)
    {Δ in_Δ} (rule_def : r 𝕏.α x = RuleApp.topₗ Δ in_Δ)
  : Ext.PreProof x (@rightInterpolantSequent 𝕏 _) where
    X := Unit
    α u := ⟨Ext.RuleApp.topₗ (rightEquationSequent x) (by
      simp [rightEquationSequent, equation, rule_def]
      split <;> simp_all [interpolant, partial_]
      ), {}⟩
    step := by intro u; simp [Ext.r, Ext.p]
    root := ()
    path u f := by exact False.elim (by simpa [Ext.edge, Ext.p] using f.2)

/-- Auxiliary declaration used in the GL coalgebra development. -/
noncomputable def partialRightTopᵣ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X)
    {Δ in_Δ} (rule_def : r 𝕏.α x = RuleApp.topᵣ Δ in_Δ)
  : Ext.PreProof x (@rightInterpolantSequent 𝕏 _) where
    X := Unit
    α u := ⟨Ext.RuleApp.topᵣ (rightEquationSequent x) (by
      exact Finset.mem_union_right _ (by simpa [SplitSequent.filterRight, rule_def, f]
        using in_Δ)), {}⟩
    step u := by simp [Ext.r, Ext.p]
    root := ()
    path u f := by exact False.elim (by simpa [Ext.edge, Ext.p] using f.2)

/-- Auxiliary declaration used in the GL coalgebra development. -/
noncomputable def partialRightAxₗₗ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X)
    {Δ n in_Δ} (rule_def : r 𝕏.α x = RuleApp.axₗₗ Δ n in_Δ)
  : Ext.PreProof x (@rightInterpolantSequent 𝕏 _) where
    X := Unit
    α u := ⟨Ext.RuleApp.topₗ (rightEquationSequent x) (by
      simp [rightEquationSequent, rule_def, f]
      simp [equation]
      split <;> simp_all [interpolant, partial_]), {}⟩
    step := by intro u; simp [Ext.r, Ext.p]
    root := ()
    path u f := by exact False.elim (by simpa [Ext.edge, Ext.p] using f.2)

/-- Auxiliary declaration used in the GL coalgebra development. -/
noncomputable def partialRightAxₗᵣ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X)
    {Δ n in_Δ} (rule_def : r 𝕏.α x = RuleApp.axₗᵣ Δ n in_Δ)
  : Ext.PreProof x (@rightInterpolantSequent 𝕏 _) where
    X := Unit
    α u := ⟨Ext.RuleApp.axₗᵣ (rightEquationSequent x) n (by
      simp only [rightEquationSequent, SplitSequent.filterRight, Bool.false_eq_true, f,
        rule_def, Finset.singleton_union, Finset.mem_insert, Sum.inl.injEq,
        Finset.mem_filter, in_Δ, and_false, or_false, reduceCtorEq, and_self,
        or_true, and_true]
      simp only [interpolant, equation]
      split <;> simp_all only [RuleApp.axₗᵣ.injEq, reduceCtorEq]
      rw [←partial_const]
      · rfl
      simp only [Formula.vocab, Finset.mem_singleton, Finset.mem_image, not_exists,
        not_and, forall_eq]
      intro _ _
      apply at_in_not_encodeVar
      rw [Proof.Sequent]
      apply Finset.mem_biUnion.mpr
      use x
      constructor
      · exact Fintype.complete x
      · apply Finset.mem_image.mpr
        use Sum.inl (at n)
        constructor
        · convert in_Δ.1
          simp_all [f]
        · rfl
      ), {}⟩
    step := by intro u; simp [Ext.r, Ext.p]
    root := ()
    path u f := by exact False.elim (by simpa [Ext.edge, Ext.p] using f.2)

/-- Auxiliary declaration used in the GL coalgebra development. -/
noncomputable def partialRightAxᵣₗ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X)
    {Δ n in_Δ} (rule_def : r 𝕏.α x = RuleApp.axᵣₗ Δ n in_Δ)
  : Ext.PreProof x (@rightInterpolantSequent 𝕏 _) where
    X := Unit
    α u := ⟨Ext.RuleApp.axᵣₗ (rightEquationSequent x) n (by
      simp only [rightEquationSequent, rule_def, f, Finset.mem_union, Finset.mem_singleton,
        SplitSequent.filterRight, Finset.mem_filter, reduceCtorEq, and_false, false_or,
        or_false, Sum.inl.injEq, in_Δ, true_and]
      simp only [interpolant, equation]
      split <;> simp_all only [RuleApp.axᵣₗ.injEq, reduceCtorEq]
      rw [←partial_const]
      · rfl
      simp only [Formula.vocab, Finset.mem_singleton, Finset.mem_image, not_exists,
        not_and, forall_eq]
      intro _ _
      apply at_in_not_encodeVar
      rw [Proof.Sequent]
      apply Finset.mem_biUnion.mpr
      use x
      constructor
      · exact Fintype.complete x
      · apply Finset.mem_image.mpr
        use Sum.inr (at n)
        constructor
        · convert in_Δ.1
          simp_all [f]
        · rfl
      ), {}⟩
    step := by intro u; simp [Ext.r, Ext.p]
    root := ()
    path u f := by exact False.elim (by simpa [Ext.edge, Ext.p] using f.2)

/-- Auxiliary declaration used in the GL coalgebra development. -/
noncomputable def partialRightAxᵣᵣ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X)
    {Δ n in_Δ} (rule_def : r 𝕏.α x = RuleApp.axᵣᵣ Δ n in_Δ)
  : Ext.PreProof x (@rightInterpolantSequent 𝕏 _) where
    X := Unit
    α u := ⟨Ext.RuleApp.axᵣᵣ (rightEquationSequent x) n (by
      simp [rightEquationSequent, rule_def, f, in_Δ]), {}⟩
    step := by intro u; simp [Ext.r, Ext.p]
    root := ()
    path u f := by exact False.elim (by simpa [Ext.edge, Ext.p] using f.2)

/-- Auxiliary declaration used in the GL coalgebra development. -/
noncomputable def partialRightOrₗ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X)
    {Δ φ ψ in_Δ} (rule_def : r 𝕏.α x = RuleApp.orₗ Δ φ ψ in_Δ)
  : Ext.PreProof x (@rightInterpolantSequent 𝕏 _) :=
    match p_def : p 𝕏.α x with
      | [y] =>
        have interpolant_eq :
            interpolant 𝕏 (equation x) = interpolant 𝕏 (at encodeVar y) := by
          rw [equation]
          split <;> simp_all
        { X := Unit
          α u := ⟨Ext.RuleApp.pre y (by simp [p_def]), {}⟩
          step := by simp [Ext.r, Ext.p]
          root := ()
          path z f := by exfalso; simp [Ext.edge, Ext.p] at f; grind}
        | [] => by have := 𝕏.step x; simp [rule_def] at this; simp_all
        | y :: z :: l => by have := 𝕏.step x; simp [rule_def] at this; simp_all

/-- Auxiliary declaration used in the GL coalgebra development. -/
noncomputable def partialRightOrᵣ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X)
    {Δ φ ψ in_Δ} (rule_def : r 𝕏.α x = RuleApp.orᵣ Δ φ ψ in_Δ)
  : Ext.PreProof x (@rightInterpolantSequent 𝕏 _) :=
  match p_def : p 𝕏.α x with
    | [y] =>
      have interpolant_eq : interpolant 𝕏 (equation x) = interpolant 𝕏 (at encodeVar y) := by
        rw [equation]
        split <;> simp_all
    { X := Fin 2
      α | 0 => ⟨Ext.RuleApp.orᵣ (rightEquationSequent x) φ ψ (by
          simp [rightEquationSequent, rule_def, f, in_Δ]), [1]⟩
        | 1 => ⟨Ext.RuleApp.pre y (by simp [p_def]), {}⟩
      step := by
        have 𝕏_h := 𝕏.step x
        simp only [rule_def, p_def, List.map_cons, List.map_nil, List.cons.injEq,
          and_true, fₙ_alternate] at 𝕏_h
        intro n
        match n with
          | 0 =>
            simp [Ext.r, Ext.p, Ext.T, Ext.f, Ext.fₙ, Ext.fₚ,
              rightInterpolantSequent, rightEquationSequent, rule_def, 𝕏_h,
              interpolant_eq]
            aesop -- big aesop
          | 1 =>
            simp [Ext.r, Ext.p]
      root := 0
      path z f := by exfalso; simp [Ext.edge, Ext.p] at f; grind}
    | [] => by have := 𝕏.step x; simp [rule_def] at this; simp_all
    | _ :: _ :: _ => by have := 𝕏.step x; simp [rule_def] at this; simp_all

/-- Auxiliary declaration used in the GL coalgebra development. -/
noncomputable def partialRightAndₗ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X)
    {Δ φ ψ in_Δ} (rule_def : r 𝕏.α x = RuleApp.andₗ Δ φ ψ in_Δ)
  : Ext.PreProof x (@rightInterpolantSequent 𝕏 _) :=
  match p_def : p 𝕏.α x with
  | [y,z] =>
    have interpolant_eq :
        interpolant 𝕏 (equation x) =
          (interpolant 𝕏 (at encodeVar y) v interpolant 𝕏 (at encodeVar z)) := by
      rw [equation]
      split <;> simp_all [interpolant, partial_, encodeVar]
    { X := Fin 3
      α | 0 =>
          ⟨Ext.RuleApp.andₗ (rightEquationSequent x)
            (~ (interpolant 𝕏 (at encodeVar y))) (~ (interpolant 𝕏 (at encodeVar z)))
            (by simp [rightEquationSequent, rule_def, f, interpolant_eq]), [1,2]⟩
        | 1 => ⟨Ext.RuleApp.pre y (by simp [p_def]), {}⟩
        | 2 => ⟨Ext.RuleApp.pre z (by simp [p_def]), {}⟩
      step
        | 0 => by
          have 𝕏_h := 𝕏.step x
          simp only [rule_def, p_def, List.map_cons, List.map_nil, List.cons.injEq,
            and_true, fₙ_alternate] at 𝕏_h
          simp only [Ext.r, rightEquationSequent, interpolant_eq, Formula.neg.eq_6,
            SplitSequent.filterRight, Bool.false_eq_true, rule_def, Finset.singleton_union,
            Ext.f, Ext.T, Fin.isValue, List.empty_eq, rightInterpolantSequent, Ext.p,
            List.map_cons, 𝕏_h, Finset.union_singleton, List.map_nil, Ext.fₙ_alternate,
            List.cons.injEq, and_true]
          constructor <;> ext <;> simp [f] <;> aesop
        | 1 => by simp [Ext.r, Ext.p]
        | 2 => by simp [Ext.r, Ext.p]
      root := 0
      path z f := by exfalso; simp [Ext.edge, Ext.p] at f; grind}
  | [] => by have := 𝕏.step x; simp [rule_def] at this; simp_all
  | [_] => by have := 𝕏.step x; simp [rule_def] at this; simp_all
  | _ :: _ :: _ :: _ => by have := 𝕏.step x; simp [rule_def] at this; simp_all

/-- Auxiliary declaration used in the GL coalgebra development. -/
noncomputable def partialRightAndᵣ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X)
    {Δ φ ψ in_Δ} (rule_def : r 𝕏.α x = RuleApp.andᵣ Δ φ ψ in_Δ)
  : Ext.PreProof x (@rightInterpolantSequent 𝕏 _) :=
  match p_def : p 𝕏.α x with
  | [y,z] =>
    have interpolant_eq :
        interpolant 𝕏 (equation x) =
          (interpolant 𝕏 (at encodeVar y) & interpolant 𝕏 (at encodeVar z)) := by
      rw [equation]
      split <;> simp_all [interpolant, partial_, encodeVar]
    if eq : interpolant 𝕏 (at encodeVar y) = interpolant 𝕏 (at encodeVar z)
    then {
    X := Fin 4
    α | 0 =>
        ⟨Ext.RuleApp.orₗ (rightEquationSequent x) (~interpolant 𝕏 (at encodeVar y))
          (~interpolant 𝕏 (at encodeVar z))
          (by simp [rightEquationSequent, rule_def, f, interpolant_eq]), [1]⟩
      | 1 =>
        ⟨Ext.RuleApp.andᵣ
          (((rightEquationSequent x) \ {Sum.inl <| ~interpolant 𝕏 (equation x)}) ∪
            {(Sum.inl <| ~interpolant 𝕏 (at encodeVar y)),
              Sum.inl <| ~interpolant 𝕏 (at encodeVar z)})
          φ ψ (by simp [rightEquationSequent, rule_def, f, interpolant_eq, in_Δ]),
          [2,3]⟩
      | 2 => ⟨Ext.RuleApp.pre y (by simp [p_def]), {}⟩
      | 3 => ⟨Ext.RuleApp.pre z (by simp [p_def]), {}⟩
    step
      | 0 => by
        simp [Ext.r, Ext.p, rightEquationSequent, rule_def, f, interpolant_eq, Ext.f,
          Ext.fₙ_alternate]
      | 1 => by
        have 𝕏_h := 𝕏.step x
        simp only [rule_def, p_def, List.map_cons, List.map_nil, List.cons.injEq,
          and_true, fₙ_alternate] at 𝕏_h
        simp only [Ext.r, rightEquationSequent, interpolant_eq, eq, Formula.neg.eq_5,
          SplitSequent.filterRight, Bool.false_eq_true, rule_def, Finset.singleton_union,
          Finset.mem_singleton, Finset.insert_eq_of_mem, Finset.union_singleton, Ext.f,
          Ext.T, Fin.isValue, List.empty_eq, rightInterpolantSequent, Ext.p, List.map_cons,
          𝕏_h, List.map_nil, Ext.fₙ_alternate, List.cons.injEq, and_true]
        constructor <;> ext <;> simp [f] <;> aesop
      | 2 => by simp [Ext.r, Ext.p]
      | 3 => by simp [Ext.r, Ext.p]
    root := 0
    path z f := by exfalso; simp [Ext.edge, Ext.p] at f; grind}
    else {
    X := Fin 6
    α | 0 =>
        ⟨Ext.RuleApp.orₗ (rightEquationSequent x) (~interpolant 𝕏 (at encodeVar y))
          (~interpolant 𝕏 (at encodeVar z))
          (by simp [rightEquationSequent, rule_def, f, interpolant_eq]), [1]⟩
      | 1 =>
        ⟨Ext.RuleApp.andᵣ
          (((rightEquationSequent x) \ {Sum.inl <| ~interpolant 𝕏 (equation x)}) ∪
            {(Sum.inl <| ~interpolant 𝕏 (at encodeVar y)),
              Sum.inl <| ~interpolant 𝕏 (at encodeVar z)})
          φ ψ (by simp [rightEquationSequent, rule_def, f, interpolant_eq, in_Δ]),
          [2,3]⟩
      | 2 =>
        ⟨Ext.RuleApp.wkₗ
          (((((rightEquationSequent x) \ {Sum.inl <| ~interpolant 𝕏 (equation x)}) ∪
              {Sum.inl <| ~interpolant 𝕏 (at encodeVar y),
                Sum.inl <| ~interpolant 𝕏 (at encodeVar z)}) \
            {Sum.inr (φ & ψ)}) ∪ {Sum.inr φ})
          (~interpolant 𝕏 (at encodeVar z))
          (by simp [rightEquationSequent, rule_def, f, interpolant_eq]), [4]⟩
      | 3 =>
        ⟨Ext.RuleApp.wkₗ
          (((((rightEquationSequent x) \ {Sum.inl <| ~interpolant 𝕏 (equation x)}) ∪
              {Sum.inl <| ~interpolant 𝕏 (at encodeVar y),
                Sum.inl <| ~interpolant 𝕏 (at encodeVar z)}) \
            {Sum.inr (φ & ψ)}) ∪ {Sum.inr ψ})
          (~interpolant 𝕏 (at encodeVar y))
          (by simp [rightEquationSequent, rule_def, f, interpolant_eq]), [5]⟩
      | 4 => ⟨Ext.RuleApp.pre y (by simp [p_def]), {}⟩
      | 5 => ⟨Ext.RuleApp.pre z (by simp [p_def]), {}⟩
    step
      | 0 => by
        simp [Ext.r, Ext.p, rightEquationSequent, rule_def, f, interpolant_eq, Ext.f,
          Ext.fₙ_alternate]
      | 1 => by
        simp [Ext.r, Ext.p, rightEquationSequent, rule_def, f, interpolant_eq, Ext.f,
          Ext.fₙ_alternate]
      | 2 => by
        have 𝕏_h := 𝕏.step x
        simp only [rule_def, p_def, List.map_cons, List.map_nil, List.cons.injEq,
          and_true, fₙ_alternate] at 𝕏_h
        simp only [Ext.r, rightEquationSequent, interpolant_eq, Formula.neg.eq_5,
          SplitSequent.filterRight, Bool.false_eq_true, rule_def, Finset.singleton_union,
          Finset.union_insert, Finset.union_singleton, Ext.f, Ext.T, Fin.isValue,
          List.empty_eq, rightInterpolantSequent, Ext.p, List.map_cons, 𝕏_h, List.map_nil,
          Ext.fₙ_alternate, List.cons.injEq, and_true]
        ext ψ
        rcases ψ with ψ | ψ <;> simp [f]
        constructor <;> try tauto
        intro mp; subst mp; simp_all only [true_or, true_and]
        intro con; apply eq; apply Formula.neg_eq; exact con
      | 3 => by
        have 𝕏_h := 𝕏.step x
        simp only [rule_def, p_def, List.map_cons, List.map_nil, List.cons.injEq,
          and_true, fₙ_alternate] at 𝕏_h
        simp only [Ext.r, rightEquationSequent, interpolant_eq, Formula.neg.eq_5,
          SplitSequent.filterRight, Bool.false_eq_true, rule_def, Finset.singleton_union,
          Finset.union_insert, Finset.union_singleton, Ext.f, Ext.T, Fin.isValue,
          List.empty_eq, rightInterpolantSequent, Ext.p, List.map_cons, 𝕏_h, List.map_nil,
          Ext.fₙ_alternate, List.cons.injEq, and_true]
        ext ψ
        rcases ψ with ψ | ψ <;> simp [f]
        constructor <;> try tauto
        intro mp; subst mp; simp_all only [or_true, true_and]
        intro con; apply eq; apply Formula.neg_eq; exact Eq.symm con
      | 4 => by simp [Ext.r, Ext.p]
      | 5 => by simp [Ext.r, Ext.p]
    root := 0
    path z f := by exfalso; simp [Ext.edge, Ext.p] at f; grind}
  | [] => by have := 𝕏.step x; simp [rule_def] at this; simp_all
  | [_] => by have := 𝕏.step x; simp [rule_def] at this; simp_all
  | _ :: _ :: _ :: _ => by have := 𝕏.step x; simp [rule_def] at this; simp_all

/-- Auxiliary declaration used in the GL coalgebra development. -/
noncomputable def partialRightBoxₗ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X)
    {Δ φ in_Δ} (rule_def : r 𝕏.α x = RuleApp.boxₗ Δ φ in_Δ)
  : Ext.PreProof x (@rightInterpolantSequent 𝕏 _) :=
  match p_def : p 𝕏.α x with
  | [y] =>
    have interpolant_eq :
        interpolant 𝕏 (equation x) = ◇ (interpolant 𝕏 (at encodeVar y)) := by
      rw [equation]
      split <;> simp_all [interpolant, partial_, encodeVar]
    { X := Fin 2
      α | 0 =>
          ⟨Ext.RuleApp.boxₗ (rightEquationSequent x)
            (~(interpolant 𝕏 (at encodeVar y)))
            (by simp [rightEquationSequent, interpolant_eq]), [1]⟩
        | 1 => ⟨Ext.RuleApp.pre y (by simp [p_def]), {}⟩
      step
        | 0 => by
          have 𝕏_h := 𝕏.step x
          simp only [rule_def, p_def, List.map_cons, List.map_nil, List.cons.injEq,
            and_true, fₙ_alternate] at 𝕏_h
          simp only [Ext.r, rightEquationSequent, interpolant_eq, Formula.neg.eq_8,
            SplitSequent.filterRight, Bool.false_eq_true, rule_def, Finset.singleton_union,
            Ext.f, Ext.T, Fin.isValue, List.empty_eq, rightInterpolantSequent, Ext.p,
            List.map_cons, 𝕏_h, Finset.union_singleton, List.map_nil, Ext.fₙ_alternate,
            List.cons.injEq, and_true]
          ext ψ
          simp [f, SplitSequent.D, Finset.mem_sdiff]
          cases ψ <;> simp
        | 1 => by simp [Ext.r, Ext.p]
      root := 0
      path z f := by exfalso; simp [Ext.edge, Ext.p] at f; grind}
  | [] => by have := 𝕏.step x; simp [rule_def] at this; simp_all
  | _ :: _ :: _ => by have := 𝕏.step x; simp [rule_def] at this; simp_all

/-- Auxiliary declaration used in the GL coalgebra development. -/
noncomputable def partialRightBoxᵣ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X)
    {Δ φ in_Δ} (rule_def : r 𝕏.α x = RuleApp.boxᵣ Δ φ in_Δ)
  : Ext.PreProof x (@rightInterpolantSequent 𝕏 _) :=
  match p_def : p 𝕏.α x with
  | [y] =>
    have interpolant_eq :
        interpolant 𝕏 (equation x) = □ (interpolant 𝕏 (at encodeVar y)) := by
      rw [equation]
      split <;> simp_all [interpolant, partial_, encodeVar]
    { X := Fin 3
      α | 0 =>
          ⟨Ext.RuleApp.boxᵣ (rightEquationSequent x) φ (by
            simp [rightEquationSequent, rule_def, f, in_Δ]), [1]⟩
        | 1 =>
          ⟨Ext.RuleApp.wkₗ
            (((rightEquationSequent x) \ {Sum.inr <| □ φ}).D ∪ {Sum.inr φ})
            (◇ (~(interpolant 𝕏 (at encodeVar y))))
            (by
              simp [rightEquationSequent, rule_def, f, interpolant_eq, SplitSequent.D,
                SplitFormula.isDiamond]), [2]⟩
        | 2 => ⟨Ext.RuleApp.pre y (by simp [p_def]), {}⟩
      step
        | 0 => by
          simp [Ext.r, Ext.p, rightEquationSequent, rule_def, f, interpolant_eq, Ext.f,
            Ext.fₙ_alternate]
        | 1 => by
          have 𝕏_h := 𝕏.step x
          simp only [rule_def, p_def, List.map_cons, List.map_nil, List.cons.injEq,
            and_true, fₙ_alternate] at 𝕏_h
          simp only [Ext.r, rightEquationSequent, interpolant_eq, Formula.neg.eq_7,
            SplitSequent.filterRight, Bool.false_eq_true, rule_def, Finset.singleton_union,
            Finset.union_singleton, Ext.f, Ext.T, Fin.isValue, List.empty_eq,
            rightInterpolantSequent, Ext.p, List.map_cons, 𝕏_h, List.map_nil,
            Ext.fₙ_alternate, List.cons.injEq, and_true]
          ext ψ
          simp [f, SplitSequent.D, Finset.mem_sdiff]
          cases ψ <;> simp
          simp [SplitFormula.isDiamond]
          constructor <;> try tauto
          intro mp
          subst mp
          simp
          induction interpolant 𝕏 (at encodeVar y) <;> simp_all -- MALVIN so weird
        | 2 => by simp [Ext.r, Ext.p]
      root := 0
      path z f := by exfalso; simp [Ext.edge, Ext.p] at f; grind}
  | [] => by have := 𝕏.step x; simp [rule_def] at this; simp_all
  | _ :: _ :: _ => by have := 𝕏.step x; simp [rule_def] at this; simp_all

/-- Defines the right partial interpolation proof `Rₓ`. -/
noncomputable def partialEquationRight {𝕏 : Proof} [fin_X : Fintype 𝕏.X]
    (x : 𝕏.X) : Ext.PreProof x (@rightInterpolantSequent 𝕏 _) :=
  match rule_def : (r 𝕏.α x) with
    | .topₗ _ _ => partialRightTopₗ x rule_def
    | .topᵣ _ _ => partialRightTopᵣ x rule_def
    | .axₗₗ _ _ _ => partialRightAxₗₗ x rule_def
    | .axₗᵣ _ _ _ => partialRightAxₗᵣ x rule_def
    | .axᵣₗ _ _ _ => partialRightAxᵣₗ x rule_def
    | .axᵣᵣ _ _ _ => partialRightAxᵣᵣ x rule_def
    | .orₗ _ _ _ _ => partialRightOrₗ x rule_def
    | .orᵣ _ _ _ _ => partialRightOrᵣ x rule_def
    | .andₗ _ _ _ _ => partialRightAndₗ x rule_def
    | .andᵣ _ _ _ _ => partialRightAndᵣ x rule_def
    | .boxₗ _ _ _ => partialRightBoxₗ x rule_def
    | .boxᵣ _ _ _ => partialRightBoxᵣ x rule_def

private theorem partialEquationRight_proves_eq_aux {𝕏 : Proof} [fin_X : Fintype 𝕏.X]
    (x : 𝕏.X) :
    Ext.Proves x (partialEquationRight x) (rightEquationSequent x) := by
  have 𝕏_h := 𝕏.step x
  unfold partialEquationRight
  split <;> simp_all only [List.empty_eq, Finset.union_insert, Finset.union_singleton,
    List.map_eq_cons_iff, List.map_eq_nil_iff, exists_eq_right_right, ↓existsAndEq,
    true_and, Ext.Proves, Ext.r]
  · simp [partialRightTopₗ, Ext.f]
  · simp [partialRightTopᵣ, Ext.f]
  · simp [partialRightAxₗₗ, Ext.f]
  · simp [partialRightAxₗᵣ, Ext.f]
  · simp [partialRightAxᵣₗ, Ext.f]
  · simp [partialRightAxᵣᵣ, Ext.f]
  · rename_i rule_def
    simp only [partialRightOrₗ, List.empty_eq, Lean.Elab.WF.paramLet]
    have ⟨y, p_def, prop⟩ := 𝕏_h
    split <;> simp_all only [List.cons.injEq, and_true, exists_eq_left', Ext.f,
      List.ne_cons_self, reduceCtorEq, and_false]
    simp only [rightInterpolantSequent, SplitSequent.filterRight, Bool.false_eq_true, prop,
      Finset.singleton_union, rightEquationSequent, rule_def]
    apply congrArg₂
    · simp [equation]; split <;> simp_all
    · simp [f, fₙ, fₚ]
      aesop
  · simp [partialRightOrᵣ]
    split <;> simp_all [Ext.f]
  · simp [partialRightAndₗ]
    split <;> simp_all [Ext.f]
  · rename_i rule_def
    have ⟨y, z, p_def, prop⟩ := 𝕏_h
    simp only [partialRightAndᵣ, Ext.T, Fin.isValue, List.empty_eq, Lean.Elab.WF.paramLet]
    split <;> simp_all only [List.cons.injEq, and_true, ↓existsAndEq, Fin.isValue,
      List.nil_eq, reduceCtorEq, List.ne_cons_self, and_false]
    have ⟨eq₁, eq₂⟩ := p_def
    by_cases eq : interpolant 𝕏 (at encodeVar y) = interpolant 𝕏 (at encodeVar z) <;>
      subst eq₁ eq₂
    · rw [dif_pos eq]
      simp [Ext.f]
    · rw [dif_neg eq]
      simp [Ext.f]
  · simp [partialRightBoxₗ]
    split <;> simp_all [Ext.f]
  · simp [partialRightBoxᵣ]
    split <;> simp_all [Ext.f]

private theorem partialEquationLeft_proves_eq_aux {𝕏 : Proof} [fin_X : Fintype 𝕏.X]
    (x : 𝕏.X) :
    Ext.Proves x (partialEquationLeft x) (leftEquationSequent x) := by
  have 𝕏_h := 𝕏.step x
  unfold partialEquationLeft
  split <;> simp_all only [List.empty_eq, Finset.union_insert, Finset.union_singleton,
    List.map_eq_cons_iff, List.map_eq_nil_iff, exists_eq_right_right, ↓existsAndEq,
    true_and, Ext.Proves, Ext.r]
  · simp [partialLeftTopₗ, Ext.f]
  · simp [partialLeftTopᵣ, Ext.f]
  · simp [partialLeftAxₗₗ, Ext.f]
  · simp [partialLeftAxₗᵣ, Ext.f]
  · simp [partialLeftAxᵣₗ, Ext.f]
  · simp [partialLeftAxᵣᵣ, Ext.f]
  · simp [partialLeftOrₗ]
    split <;> simp_all only [List.cons.injEq, and_true, exists_eq_left', Ext.f,
      List.ne_cons_self, false_and, exists_false, reduceCtorEq, and_false]
  · rename_i rule_def
    simp only [partialLeftOrᵣ, List.empty_eq, Lean.Elab.WF.paramLet]
    have ⟨y, p_def, prop⟩ := 𝕏_h
    split <;> simp_all only [List.cons.injEq, and_true, exists_eq_left', Ext.f,
      List.ne_cons_self, reduceCtorEq, and_false]
    simp only [leftInterpolantSequent, SplitSequent.filterLeft, Bool.false_eq_true, prop,
      Finset.singleton_union, leftEquationSequent, rule_def]
    apply congrArg₂
    · simp [equation]; split <;> simp_all
    · simp [f, fₙ, fₚ]
      aesop
  · rename_i rule_def
    have ⟨y, z, p_def, prop⟩ := 𝕏_h
    simp only [partialLeftAndₗ, Ext.T, Fin.isValue, List.empty_eq, Lean.Elab.WF.paramLet]
    split <;> simp_all only [List.cons.injEq, and_true, ↓existsAndEq,
      exists_eq_left', Fin.isValue, List.nil_eq, reduceCtorEq, List.ne_cons_self, and_false]
    have ⟨eq₁, eq₂⟩ := p_def
    by_cases eq : interpolant 𝕏 (at encodeVar y) = interpolant 𝕏 (at encodeVar z) <;>
      subst eq₁ eq₂
    · rw [dif_pos eq]
      simp [Ext.f]
    · rw [dif_neg eq]
      simp [Ext.f]
  · simp [partialLeftAndᵣ]
    split <;> simp_all only [List.cons.injEq, and_true, ↓existsAndEq, Ext.f,
      List.nil_eq, reduceCtorEq, false_and, exists_false, List.ne_cons_self, and_false]
  · simp [partialLeftBoxₗ]
    split <;> simp_all only [List.cons.injEq, and_true, exists_eq_left', Ext.f,
      List.ne_cons_self, false_and, exists_false, reduceCtorEq, and_false]
  · simp [partialLeftBoxᵣ]
    split <;> simp_all only [List.cons.injEq, and_true, exists_eq_left', Ext.f,
      List.ne_cons_self, false_and, exists_false, reduceCtorEq, and_false]

/-- Carrier coalgebra of the cut-based left interpolation proof, abstracted over the right
interpolant proof `𝕐₂` and its root `y₂`. -/
noncomputable def partialInterpolationLeftAlpha {𝕏 : Proof} [fin_X : Fintype 𝕏.X]
    (x : 𝕏.X) (𝕐₂ : Split.Proof) (y₂ : 𝕐₂.X) :
    (Unit ⊕ (partialEquationLeft x).X ⊕ 𝕐₂.X) →
      (Ext.T x (@leftInterpolantSequent 𝕏 _)).obj (Unit ⊕ (partialEquationLeft x).X ⊕ 𝕐₂.X)
  | Sum.inl _ =>
      ⟨Ext.RuleApp.cutᵣ (leftInterpolantSequent x) (interpolant 𝕏 (equation x)),
        [Sum.inr (Sum.inl (partialEquationLeft x).root), Sum.inr (Sum.inr y₂)]⟩
  | Sum.inr (Sum.inl z₁) =>
      ⟨Ext.r (partialEquationLeft x).α z₁,
        List.map (Sum.inr ∘ Sum.inl) (Ext.p (partialEquationLeft x).α z₁)⟩
  | Sum.inr (Sum.inr z₂) =>
      ⟨splitToExt (r 𝕐₂.α z₂), List.map (Sum.inr ∘ Sum.inr) (p 𝕐₂.α z₂)⟩

/-- The `Sum.inl` (cut-node) arm of `partialInterpolationLeftPath`. -/
private lemma partialInterpolationLeftPath_inl {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X)
    (𝕐₂ : Split.Proof) (y₂ : 𝕐₂.X) (u : Unit)
    (f : {f : ℕ → (Unit ⊕ (partialEquationLeft x).X ⊕ 𝕐₂.X) //
        f 0 = Sum.inl u ∧
          ∀ (n : ℕ), Ext.edge (partialInterpolationLeftAlpha x 𝕐₂ y₂) (f n) (f (n + 1))}) :
    ∀ n, ∃ m, (Ext.r (partialInterpolationLeftAlpha x 𝕐₂ y₂) (f.1 (n + m))).isBox := by
  have split_to_ext_isBox {𝕐 : Split.Proof} {x : 𝕐.X} {τ} (r : Split.RuleApp) :
      r.isBox → (@splitToExt _ x τ r).isBox := by
    unfold splitToExt
    cases r <;> simp [RuleApp.isBox, Ext.RuleApp.isBox]
  have := f.2.2 0
  simp only [partialInterpolationLeftAlpha, Ext.edge, Ext.p, Ext.T, f.2.1, zero_add,
    List.mem_cons, List.not_mem_nil, or_false] at this
  rcases this with f1_def | f1_def
  · have isRight : ∀ n, (f.1 (n + 1)).isRight := by
      intro n
      induction n
      case zero => rw [f1_def]; simp
      case succ k ih =>
        have step := f.2.2 (k + 1)
        rcases fk_def : f.1 (k + 1) with l | r <;> simp [fk_def] at ih
        rcases r with z₁ | z₂
        · simp [partialInterpolationLeftAlpha, Ext.edge, Ext.p, fk_def] at step
          rcases next_def : f.1 (k + 1 + 1) with _ | next
          · simp [next_def] at step
          · rfl
        · simp [partialInterpolationLeftAlpha, Ext.edge, Ext.p, fk_def] at step
          rcases next_def : f.1 (k + 1 + 1) with _ | next
          · simp [next_def] at step
          · rfl
    have isLeft : ∀ n, ((f.1 (n + 1)).getRight (isRight n)).isLeft := by
      intro n
      induction n
      case zero => simp [f1_def]
      case succ k ih =>
        have step := f.2.2 (k + 1)
        rcases fk_def : f.1 (k + 1) with _ | l | r
        · have := isRight k
          simp [fk_def] at this
        · rcases (by
            simpa [partialInterpolationLeftAlpha, Ext.edge, Ext.p, fk_def] using step) with
            ⟨next_left, _next_mem, next_eq⟩
          simp [←next_eq]
        · simp [fk_def] at ih
    let g : ℕ → (partialEquationLeft x).X := fun n ↦
      Sum.getLeft (Sum.getRight (f.1 (n + 1)) (isRight n)) (isLeft n)
    have g_zero : g 0 = (partialEquationLeft x).root := by unfold g; simp [f1_def]
    have g_succ : ∀ n, Ext.edge (partialEquationLeft x).α (g n) (g (n + 1)) := by
      intro n
      have step := f.2.2 (n + 1)
      rcases fn_def : f.1 (n + 1) with _ | _ | gn_def
      · have := isRight n
        simp [fn_def] at this
      · rcases (by
          simpa [partialInterpolationLeftAlpha, Ext.edge, Ext.p, fn_def] using step) with
          ⟨next_left, next_mem, next_eq⟩
        simpa [g, fn_def, ←next_eq, partialInterpolationLeftAlpha, Ext.edge, Ext.p]
          using next_mem
      · have := isLeft n
        simp [fn_def] at this
    intro n
    have ⟨m, m_prop⟩ := (partialEquationLeft x).path
      (partialEquationLeft x).root ⟨g, g_zero, g_succ⟩ n
    use m + 1
    rcases fn_def : f.1 (n + m + 1) with _ | current_left | gn_def
    · have := isRight (n + m)
      simp [fn_def] at this
    · simpa [g, partialInterpolationLeftAlpha, Ext.r, fn_def] using m_prop
    · have := isLeft (n + m)
      simp [fn_def] at this
  · have isRight : ∀ n, (f.1 (n + 1)).isRight := by
      intro n
      induction n
      case zero => rw [f1_def]; simp
      case succ k ih =>
        have step := f.2.2 (k + 1)
        rcases fk_def : f.1 (k + 1) with l | r <;> simp [fk_def] at ih
        rcases r with z₁ | z₂
        · rcases (by
            simpa [partialInterpolationLeftAlpha, Ext.edge, Ext.p, fk_def] using step) with
            ⟨z, _z_mem, next_eq⟩
          simp [←next_eq]
        · rcases (by
            simpa [partialInterpolationLeftAlpha, Ext.edge, Ext.p, fk_def] using step) with
            ⟨z, _z_mem, next_eq⟩
          simp [←next_eq]
    have isRight' : ∀ n, ((f.1 (n + 1)).getRight (isRight n)).isRight := by
      intro n
      induction n
      case zero => simp [f1_def]
      case succ k ih =>
        have step := f.2.2 (k + 1)
        rcases fk_def : f.1 (k + 1) with _ | l | r
        · have := isRight k
          simp [fk_def] at this
        · simp [fk_def] at ih
        · rcases (by
            simpa [partialInterpolationLeftAlpha, Ext.edge, Ext.p, fk_def] using step) with
            ⟨z, _z_mem, next_eq⟩
          simp [←next_eq]
    let g : ℕ → 𝕐₂.X := fun n ↦
      Sum.getRight (Sum.getRight (f.1 (n + 1)) (isRight n)) (isRight' n)
    have g_zero : g 0 = y₂ := by unfold g; simp [f1_def]
    have g_succ : ∀ n, edge 𝕐₂.α (g n) (g (n + 1)) := by
      intro n
      have step := f.2.2 (n + 1)
      rcases fn_def : f.1 (n + 1) with _ | _ | gn_def
      · have := isRight n
        simp [fn_def] at this
      · have := isRight' n
        simp [fn_def] at this
      · rcases (by
          simpa [partialInterpolationLeftAlpha, Ext.edge, Ext.p, fn_def] using step) with
          ⟨z, z_mem, next_eq⟩
        simpa [g, fn_def, ←next_eq, edge] using z_mem
    intro n
    have ⟨m, m_prop⟩ := inf_path_has_inf_boxes g g_succ n
    use m + 1
    rcases fn_def : f.1 (n + m + 1) with _ | _ | gn_def
    · have := isRight (n + m)
      simp [fn_def] at this
    · have := isRight' (n + m)
      simp [fn_def] at this
    · simp only [partialInterpolationLeftAlpha, Ext.r]
      apply split_to_ext_isBox
      convert m_prop
      unfold g
      simp [fn_def]

/-- The `Sum.inr (Sum.inl _)` arm of `partialInterpolationLeftPath`. -/
private lemma partialInterpolationLeftPath_inlz {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X)
    (𝕐₂ : Split.Proof) (y₂ : 𝕐₂.X) (z : (partialEquationLeft x).X)
    (f : {f : ℕ → (Unit ⊕ (partialEquationLeft x).X ⊕ 𝕐₂.X) //
        f 0 = Sum.inr (Sum.inl z) ∧
          ∀ (n : ℕ), Ext.edge (partialInterpolationLeftAlpha x 𝕐₂ y₂) (f n) (f (n + 1))}) :
    ∀ n, ∃ m, (Ext.r (partialInterpolationLeftAlpha x 𝕐₂ y₂) (f.1 (n + m))).isBox := by
  have isRight : ∀ n, (f.1 n).isRight := by
    intro n
    induction n
    case zero => rw [f.2.1]; simp
    case succ k ih =>
      have step := f.2.2 k
      rcases fk_def : f.1 k with l | r <;> simp [fk_def] at ih
      rcases r with z₁ | z₂
      · rcases (by
          simpa [partialInterpolationLeftAlpha, Ext.edge, Ext.p, fk_def] using step) with
          ⟨z, _z_mem, next_eq⟩
        simp [←next_eq]
      · rcases (by
          simpa [partialInterpolationLeftAlpha, Ext.edge, Ext.p, fk_def] using step) with
          ⟨z, _z_mem, next_eq⟩
        simp [←next_eq]
  have isLeft : ∀ n, ((f.1 n).getRight (isRight n)).isLeft := by
    intro n
    induction n
    case zero => simp [f.2.1]
    case succ k ih =>
      have step := f.2.2 k
      rcases fk_def : f.1 k with _ | l | r
      · have := isRight k
        simp [fk_def] at this
      · rcases (by
          simpa [partialInterpolationLeftAlpha, Ext.edge, Ext.p, fk_def] using step) with
          ⟨z, _z_mem, next_eq⟩
        simp [←next_eq]
      · simp [fk_def] at ih
  let g : ℕ → (partialEquationLeft x).X := fun n ↦
    Sum.getLeft (Sum.getRight (f.1 n) (isRight n)) (isLeft n)
  have g_zero : g 0 = z := by unfold g; simp [f.2.1]
  have g_succ : ∀ n, Ext.edge (partialEquationLeft x).α (g n) (g (n + 1)) := by
    intro n
    have step := f.2.2 n
    rcases fn_def : f.1 n with _ | _ | gn_def
    · have := isRight n
      simp [fn_def] at this
    · rcases (by simpa [partialInterpolationLeftAlpha, Ext.edge, Ext.p, fn_def] using step) with
        ⟨z, z_mem, next_eq⟩
      simpa [g, fn_def, ←next_eq, partialInterpolationLeftAlpha, Ext.edge, Ext.p] using z_mem
    · have := isLeft n
      simp [fn_def] at this
  intro n
  have ⟨m, m_prop⟩ := (partialEquationLeft x).path z ⟨g, g_zero, g_succ⟩ n
  use m
  rcases fn_def : f.1 (n + m) with _ | _ | gn_def
  · have := isRight (n + m)
    simp [fn_def] at this
  · simpa [g, partialInterpolationLeftAlpha, Ext.r, fn_def] using m_prop
  · have := isLeft (n + m)
    simp [fn_def] at this

/-- The `Sum.inr (Sum.inr _)` arm of `partialInterpolationLeftPath`. -/
private lemma partialInterpolationLeftPath_inrz {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X)
    (𝕐₂ : Split.Proof) (y₂ : 𝕐₂.X) (z : 𝕐₂.X)
    (f : {f : ℕ → (Unit ⊕ (partialEquationLeft x).X ⊕ 𝕐₂.X) //
        f 0 = Sum.inr (Sum.inr z) ∧
          ∀ (n : ℕ), Ext.edge (partialInterpolationLeftAlpha x 𝕐₂ y₂) (f n) (f (n + 1))}) :
    ∀ n, ∃ m, (Ext.r (partialInterpolationLeftAlpha x 𝕐₂ y₂) (f.1 (n + m))).isBox := by
  have split_to_ext_isBox {𝕐 : Split.Proof} {x : 𝕐.X} {τ} (r : Split.RuleApp) :
      r.isBox → (@splitToExt _ x τ r).isBox := by
    unfold splitToExt
    cases r <;> simp [RuleApp.isBox, Ext.RuleApp.isBox]
  have isRight : ∀ n, (f.1 n).isRight := by
    intro n
    induction n
    case zero => rw [f.2.1]; simp
    case succ k ih =>
      have step := f.2.2 k
      rcases fk_def : f.1 k with l | r <;> simp [fk_def] at ih
      rcases r with z₁ | z₂
      · rcases (by
          simpa [partialInterpolationLeftAlpha, Ext.edge, Ext.p, fk_def] using step) with
          ⟨z, _z_mem, next_eq⟩
        simp [←next_eq]
      · rcases (by
          simpa [partialInterpolationLeftAlpha, Ext.edge, Ext.p, fk_def] using step) with
          ⟨z, _z_mem, next_eq⟩
        simp [←next_eq]
  have isRight' : ∀ n, ((f.1 n).getRight (isRight n)).isRight := by
    intro n
    induction n
    case zero => simp [f.2.1]
    case succ k ih =>
      have step := f.2.2 k
      rcases fk_def : f.1 k with _ | l | r
      · have := isRight k
        simp [fk_def] at this
      · simp [fk_def] at ih
      · rcases (by
          simpa [partialInterpolationLeftAlpha, Ext.edge, Ext.p, fk_def] using step) with
          ⟨z, _z_mem, next_eq⟩
        simp [←next_eq]
  let g : ℕ → 𝕐₂.X := fun n ↦
    Sum.getRight (Sum.getRight (f.1 n) (isRight n)) (isRight' n)
  have g_zero : g 0 = z := by unfold g; simp [f.2.1]
  have g_succ : ∀ n, edge 𝕐₂.α (g n) (g (n + 1)) := by
    intro n
    have step := f.2.2 n
    rcases fn_def : f.1 n with _ | _ | gn_def
    · have := isRight n
      simp [fn_def] at this
    · have := isRight' n
      simp [fn_def] at this
    · rcases (by simpa [partialInterpolationLeftAlpha, Ext.edge, Ext.p, fn_def] using step) with
        ⟨z, z_mem, next_eq⟩
      simpa [g, fn_def, ←next_eq, edge] using z_mem
  intro n
  have ⟨m, m_prop⟩ := inf_path_has_inf_boxes g g_succ n
  use m
  rcases fn_def : f.1 (n + m) with _ | _ | gn_def
  · have := isRight (n + m)
    simp [fn_def] at this
  · have := isRight' (n + m)
    simp [fn_def] at this
  · simp only [partialInterpolationLeftAlpha, Ext.r]
    apply split_to_ext_isBox
    convert m_prop
    unfold g
    simp [fn_def]

/-- The `path` field of the cut-based left interpolation proof: every infinite path through the
combined coalgebra meets a box rule infinitely often. -/
theorem partialInterpolationLeftPath {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X)
    (𝕐₂ : Split.Proof) (y₂ : 𝕐₂.X) :
    ∀ node, ∀ f : {f : ℕ → (Unit ⊕ (partialEquationLeft x).X ⊕ 𝕐₂.X) //
        f 0 = node ∧ ∀ (n : ℕ), Ext.edge (partialInterpolationLeftAlpha x 𝕐₂ y₂) (f n) (f (n + 1))},
      ∀ n, ∃ m, (Ext.r (partialInterpolationLeftAlpha x 𝕐₂ y₂) (f.1 (n + m))).isBox := by
  intro node f
  match node with
  | Sum.inl u => exact partialInterpolationLeftPath_inl x 𝕐₂ y₂ u f
  | Sum.inr (Sum.inl z) => exact partialInterpolationLeftPath_inlz x 𝕐₂ y₂ z f
  | Sum.inr (Sum.inr z) => exact partialInterpolationLeftPath_inrz x 𝕐₂ y₂ z f


/-- Auxiliary declaration used in the GL coalgebra development. -/
noncomputable def partialInterpolationLeft {𝕏 : Proof} [fin_X : Fintype 𝕏.X]
    (x : 𝕏.X) : Ext.PreProof x (@leftInterpolantSequent 𝕏 _) :=
  if eq : interpolant 𝕏 (at (encodeVar x)) = interpolant 𝕏 (equation x)
  then partialEquationLeft x
  else
    have equiv : interpolant 𝕏 (at (encodeVar x)) ≅ interpolant 𝕏 (equation x) := by
      have := (interpolant_prop x ).1
      simp_all
    let 𝕐₂ := equiv.1.choose
    let y₂ := equiv.1.choose_spec.choose
    have y₂_prop := equiv.1.choose_spec.choose_spec
    { X := Unit ⊕ (partialEquationLeft x).X ⊕ 𝕐₂.X
      α := partialInterpolationLeftAlpha x 𝕐₂ y₂
      step := by
        have split_to_ext_f {𝕐 : Split.Proof} {x : 𝕐.X} {τ} (r : Split.RuleApp) :
            Ext.f (@splitToExt _ x τ r) = f r := by
          unfold splitToExt
          cases r <;> simp [f, Ext.f]
        have split_to_ext_fₙ {𝕐 : Split.Proof} {x : 𝕐.X} {τ} (r : Split.RuleApp) :
            Ext.fₙ (@splitToExt _ x τ r) = fₙ r := by
          unfold splitToExt
          cases r <;> simp [fₙ_alternate, Ext.fₙ_alternate]
        intro node
        match node with
        | Sum.inl u =>
            simp only [partialInterpolationLeftAlpha, Ext.r, Ext.T, Ext.p, List.map_cons,
              split_to_ext_f, List.map_nil, Ext.fₙ_alternate, List.cons.injEq, and_true]
            constructor
            · convert partialEquationLeft_proves_eq_aux x
              simp only [leftEquationSequent, leftInterpolantSequent, Ext.Proves]
              have hset :
                  ({Sum.inr (interpolant 𝕏 (at encodeVar x))} ∪
                      (f (r 𝕏.α x)).filterLeft).filterLeft ∪
                    {Sum.inr (interpolant 𝕏 (equation x))} =
                  {Sum.inr (interpolant 𝕏 (equation x))} ∪ (f (r 𝕏.α x)).filterLeft := by
                ext a
                cases a <;> simp [Finset.mem_filter]
              rw [hset]
              rfl
            · convert y₂_prop using 1
              simp [leftInterpolantSequent]
              aesop
        | Sum.inr (Sum.inl z₁) =>
            have 𝕐₁_h := (partialEquationLeft x).step z₁
            simp only [partialInterpolationLeftAlpha, Ext.r, Ext.p, List.map_map,
              Function.comp_def]
            convert 𝕐₁_h using 2 <;> simp [Ext.p, Ext.r, List.map_eq_nil_iff]
        | Sum.inr (Sum.inr z₂) =>
            have 𝕐₂_h := 𝕐₂.step z₂
            simp only [partialInterpolationLeftAlpha, Ext.r]
            split
            all_goals
              rename_i eq
              cases r_def : r 𝕐₂.α z₂ <;> simp [r_def, splitToExt] at eq
              all_goals
                replace 𝕐₂_h := by simpa [r_def] using 𝕐₂_h
                simp only [partialInterpolationLeftAlpha, Ext.T, Ext.p, 𝕐₂_h, List.map_nil,
                  List.empty_eq, List.map_map, Finset.union_singleton, Finset.union_insert,
                  List.map_eq_singleton_iff, Function.comp_apply]
                all_goals
                  convert 𝕐₂_h
                  all_goals
                    try simp [split_to_ext_f, split_to_ext_fₙ]
                    try tauto
      root := Sum.inl ()
      path := by
        intro node
        exact partialInterpolationLeftPath x 𝕐₂ y₂ node }

/-! # Partial Left Interpolation Proofs

All of the left and right partial interpolation proofs, split apart based on rule application. These
are split apart since otherwise the file runs very slow. -/


/-- Carrier coalgebra of the cut-based right interpolation proof, abstracted over the right
interpolant proof `𝕐₂` and its root `y₂`. -/
noncomputable def partialInterpolationRightAlpha {𝕏 : Proof} [fin_X : Fintype 𝕏.X]
    (x : 𝕏.X) (𝕐₂ : Split.Proof) (y₂ : 𝕐₂.X) :
    (Unit ⊕ (partialEquationRight x).X ⊕ 𝕐₂.X) →
      (Ext.T x (@rightInterpolantSequent 𝕏 _)).obj (Unit ⊕ (partialEquationRight x).X ⊕ 𝕐₂.X)
  | Sum.inl _ =>
      ⟨Ext.RuleApp.cutₗ (rightInterpolantSequent x) (~interpolant 𝕏 (equation x)),
        [Sum.inr (Sum.inl (partialEquationRight x).root), Sum.inr (Sum.inr y₂)]⟩
  | Sum.inr (Sum.inl z₁) =>
      ⟨Ext.r (partialEquationRight x).α z₁,
        List.map (Sum.inr ∘ Sum.inl) (Ext.p (partialEquationRight x).α z₁)⟩
  | Sum.inr (Sum.inr z₂) =>
      ⟨splitToExt (r 𝕐₂.α z₂), List.map (Sum.inr ∘ Sum.inr) (p 𝕐₂.α z₂)⟩

/-- The `Sum.inl` (cut-node) arm of `partialInterpolationRightPath`. -/
private lemma partialInterpolationRightPath_inl {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X)
    (𝕐₂ : Split.Proof) (y₂ : 𝕐₂.X) (u : Unit)
    (f : {f : ℕ → (Unit ⊕ (partialEquationRight x).X ⊕ 𝕐₂.X) //
        f 0 = Sum.inl u ∧
          ∀ (n : ℕ),
            Ext.edge (partialInterpolationRightAlpha x 𝕐₂ y₂) (f n) (f (n + 1))}) :
    ∀ n, ∃ m, (Ext.r (partialInterpolationRightAlpha x 𝕐₂ y₂) (f.1 (n + m))).isBox := by
  have split_to_ext_isBox {𝕐 : Split.Proof} {x : 𝕐.X} {τ} (r : Split.RuleApp) :
      r.isBox → (@splitToExt _ x τ r).isBox := by
    unfold splitToExt
    cases r <;> simp [RuleApp.isBox, Ext.RuleApp.isBox]
  have := f.2.2 0
  simp only [partialInterpolationRightAlpha, Ext.edge, Ext.p, Ext.T, f.2.1, zero_add,
    List.mem_cons, List.not_mem_nil, or_false] at this
  rcases this with f1_def | f1_def
  · have isRight : ∀ n, (f.1 (n + 1)).isRight := by
      intro n
      induction n
      case zero => rw [f1_def]; simp
      case succ k ih =>
        have step := f.2.2 (k + 1)
        rcases fk_def : f.1 (k + 1) with l | r <;> simp [fk_def] at ih
        rcases r with z₁ | z₂
        · simp [partialInterpolationRightAlpha, Ext.edge, Ext.p, fk_def] at step
          rcases next_def : f.1 (k + 1 + 1) with _ | next
          · simp [next_def] at step
          · rfl
        · simp [partialInterpolationRightAlpha, Ext.edge, Ext.p, fk_def] at step
          rcases next_def : f.1 (k + 1 + 1) with _ | next
          · simp [next_def] at step
          · rfl
    have isLeft : ∀ n, ((f.1 (n + 1)).getRight (isRight n)).isLeft := by
      intro n
      induction n
      case zero => simp [f1_def]
      case succ k ih =>
        have step := f.2.2 (k + 1)
        rcases fk_def : f.1 (k + 1) with _ | l | r
        · have := isRight k
          simp [fk_def] at this
        · rcases (by
            simpa [partialInterpolationRightAlpha, Ext.edge, Ext.p, fk_def] using step) with
            ⟨next_left, _next_mem, next_eq⟩
          simp [←next_eq]
        · simp [fk_def] at ih
    let g : ℕ → (partialEquationRight x).X := fun n ↦
      Sum.getLeft (Sum.getRight (f.1 (n + 1)) (isRight n)) (isLeft n)
    have g_zero : g 0 = (partialEquationRight x).root := by unfold g; simp [f1_def]
    have g_succ : ∀ n, Ext.edge (partialEquationRight x).α (g n) (g (n + 1)) := by
      intro n
      have step := f.2.2 (n + 1)
      rcases fn_def : f.1 (n + 1) with _ | _ | gn_def
      · have := isRight n
        simp [fn_def] at this
      · rcases (by
          simpa [partialInterpolationRightAlpha, Ext.edge, Ext.p, fn_def] using step) with
          ⟨next_left, next_mem, next_eq⟩
        simpa [g, fn_def, ←next_eq, partialInterpolationRightAlpha, Ext.edge, Ext.p]
          using next_mem
      · have := isLeft n
        simp [fn_def] at this
    intro n
    have ⟨m, m_prop⟩ := (partialEquationRight x).path
      (partialEquationRight x).root ⟨g, g_zero, g_succ⟩ n
    use m + 1
    rcases fn_def : f.1 (n + m + 1) with _ | current_left | gn_def
    · have := isRight (n + m)
      simp [fn_def] at this
    · simpa [g, partialInterpolationRightAlpha, Ext.r, fn_def] using m_prop
    · have := isLeft (n + m)
      simp [fn_def] at this
  · have isRight : ∀ n, (f.1 (n + 1)).isRight := by
      intro n
      induction n
      case zero => rw [f1_def]; simp
      case succ k ih =>
        have step := f.2.2 (k + 1)
        rcases fk_def : f.1 (k + 1) with l | r <;> simp [fk_def] at ih
        rcases r with z₁ | z₂
        · rcases (by
            simpa [partialInterpolationRightAlpha, Ext.edge, Ext.p, fk_def] using step) with
            ⟨z, _z_mem, next_eq⟩
          simp [←next_eq]
        · rcases (by
            simpa [partialInterpolationRightAlpha, Ext.edge, Ext.p, fk_def] using step) with
            ⟨z, _z_mem, next_eq⟩
          simp [←next_eq]
    have isRight' : ∀ n, ((f.1 (n + 1)).getRight (isRight n)).isRight := by
      intro n
      induction n
      case zero => simp [f1_def]
      case succ k ih =>
        have step := f.2.2 (k + 1)
        rcases fk_def : f.1 (k + 1) with _ | l | r
        · have := isRight k
          simp [fk_def] at this
        · simp [fk_def] at ih
        · rcases (by
            simpa [partialInterpolationRightAlpha, Ext.edge, Ext.p, fk_def] using step) with
            ⟨z, _z_mem, next_eq⟩
          simp [←next_eq]
    let g : ℕ → 𝕐₂.X := fun n ↦
      Sum.getRight (Sum.getRight (f.1 (n + 1)) (isRight n)) (isRight' n)
    have g_zero : g 0 = y₂ := by unfold g; simp [f1_def]
    have g_succ : ∀ n, edge 𝕐₂.α (g n) (g (n + 1)) := by
      intro n
      have step := f.2.2 (n + 1)
      rcases fn_def : f.1 (n + 1) with _ | _ | gn_def
      · have := isRight n
        simp [fn_def] at this
      · have := isRight' n
        simp [fn_def] at this
      · rcases (by
          simpa [partialInterpolationRightAlpha, Ext.edge, Ext.p, fn_def] using step) with
          ⟨z, z_mem, next_eq⟩
        simpa [g, fn_def, ←next_eq, edge] using z_mem
    intro n
    have ⟨m, m_prop⟩ := inf_path_has_inf_boxes g g_succ n
    use m + 1
    rcases fn_def : f.1 (n + m + 1) with _ | _ | gn_def
    · have := isRight (n + m)
      simp [fn_def] at this
    · have := isRight' (n + m)
      simp [fn_def] at this
    · simp only [partialInterpolationRightAlpha, Ext.r]
      apply split_to_ext_isBox
      convert m_prop
      unfold g
      simp [fn_def]

/-- The `Sum.inr (Sum.inl _)` arm of `partialInterpolationRightPath`. -/
private lemma partialInterpolationRightPath_inlz {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X)
    (𝕐₂ : Split.Proof) (y₂ : 𝕐₂.X) (z : (partialEquationRight x).X)
    (f : {f : ℕ → (Unit ⊕ (partialEquationRight x).X ⊕ 𝕐₂.X) //
        f 0 = Sum.inr (Sum.inl z) ∧
          ∀ (n : ℕ),
            Ext.edge (partialInterpolationRightAlpha x 𝕐₂ y₂) (f n) (f (n + 1))}) :
    ∀ n, ∃ m, (Ext.r (partialInterpolationRightAlpha x 𝕐₂ y₂) (f.1 (n + m))).isBox := by
  have isRight : ∀ n, (f.1 n).isRight := by
    intro n
    induction n
    case zero => rw [f.2.1]; simp
    case succ k ih =>
      have step := f.2.2 k
      rcases fk_def : f.1 k with l | r <;> simp [fk_def] at ih
      rcases r with z₁ | z₂
      · rcases (by
          simpa [partialInterpolationRightAlpha, Ext.edge, Ext.p, fk_def] using step) with
          ⟨z, _z_mem, next_eq⟩
        simp [←next_eq]
      · rcases (by
          simpa [partialInterpolationRightAlpha, Ext.edge, Ext.p, fk_def] using step) with
          ⟨z, _z_mem, next_eq⟩
        simp [←next_eq]
  have isLeft : ∀ n, ((f.1 n).getRight (isRight n)).isLeft := by
    intro n
    induction n
    case zero => simp [f.2.1]
    case succ k ih =>
      have step := f.2.2 k
      rcases fk_def : f.1 k with _ | l | r
      · have := isRight k
        simp [fk_def] at this
      · rcases (by
          simpa [partialInterpolationRightAlpha, Ext.edge, Ext.p, fk_def] using step) with
          ⟨z, _z_mem, next_eq⟩
        simp [←next_eq]
      · simp [fk_def] at ih
  let g : ℕ → (partialEquationRight x).X := fun n ↦
    Sum.getLeft (Sum.getRight (f.1 n) (isRight n)) (isLeft n)
  have g_zero : g 0 = z := by unfold g; simp [f.2.1]
  have g_succ : ∀ n, Ext.edge (partialEquationRight x).α (g n) (g (n + 1)) := by
    intro n
    have step := f.2.2 n
    rcases fn_def : f.1 n with _ | _ | gn_def
    · have := isRight n
      simp [fn_def] at this
    · rcases (by
        simpa [partialInterpolationRightAlpha, Ext.edge, Ext.p, fn_def] using step) with
        ⟨z, z_mem, next_eq⟩
      simpa [g, fn_def, ←next_eq, partialInterpolationRightAlpha, Ext.edge, Ext.p] using z_mem
    · have := isLeft n
      simp [fn_def] at this
  intro n
  have ⟨m, m_prop⟩ := (partialEquationRight x).path z ⟨g, g_zero, g_succ⟩ n
  use m
  rcases fn_def : f.1 (n + m) with _ | _ | gn_def
  · have := isRight (n + m)
    simp [fn_def] at this
  · simpa [g, partialInterpolationRightAlpha, Ext.r, fn_def] using m_prop
  · have := isLeft (n + m)
    simp [fn_def] at this

/-- The `Sum.inr (Sum.inr _)` arm of `partialInterpolationRightPath`. -/
private lemma partialInterpolationRightPath_inrz {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X)
    (𝕐₂ : Split.Proof) (y₂ : 𝕐₂.X) (z : 𝕐₂.X)
    (f : {f : ℕ → (Unit ⊕ (partialEquationRight x).X ⊕ 𝕐₂.X) //
        f 0 = Sum.inr (Sum.inr z) ∧
          ∀ (n : ℕ),
            Ext.edge (partialInterpolationRightAlpha x 𝕐₂ y₂) (f n) (f (n + 1))}) :
    ∀ n, ∃ m, (Ext.r (partialInterpolationRightAlpha x 𝕐₂ y₂) (f.1 (n + m))).isBox := by
  have split_to_ext_isBox {𝕐 : Split.Proof} {x : 𝕐.X} {τ} (r : Split.RuleApp) :
      r.isBox → (@splitToExt _ x τ r).isBox := by
    unfold splitToExt
    cases r <;> simp [RuleApp.isBox, Ext.RuleApp.isBox]
  have isRight : ∀ n, (f.1 n).isRight := by
    intro n
    induction n
    case zero => rw [f.2.1]; simp
    case succ k ih =>
      have step := f.2.2 k
      rcases fk_def : f.1 k with l | r <;> simp [fk_def] at ih
      rcases r with z₁ | z₂
      · rcases (by
          simpa [partialInterpolationRightAlpha, Ext.edge, Ext.p, fk_def] using step) with
          ⟨z, _z_mem, next_eq⟩
        simp [←next_eq]
      · rcases (by
          simpa [partialInterpolationRightAlpha, Ext.edge, Ext.p, fk_def] using step) with
          ⟨z, _z_mem, next_eq⟩
        simp [←next_eq]
  have isRight' : ∀ n, ((f.1 n).getRight (isRight n)).isRight := by
    intro n
    induction n
    case zero => simp [f.2.1]
    case succ k ih =>
      have step := f.2.2 k
      rcases fk_def : f.1 k with _ | l | r
      · have := isRight k
        simp [fk_def] at this
      · simp [fk_def] at ih
      · rcases (by
          simpa [partialInterpolationRightAlpha, Ext.edge, Ext.p, fk_def] using step) with
          ⟨z, _z_mem, next_eq⟩
        simp [←next_eq]
  let g : ℕ → 𝕐₂.X := fun n ↦
    Sum.getRight (Sum.getRight (f.1 n) (isRight n)) (isRight' n)
  have g_zero : g 0 = z := by unfold g; simp [f.2.1]
  have g_succ : ∀ n, edge 𝕐₂.α (g n) (g (n + 1)) := by
    intro n
    have step := f.2.2 n
    rcases fn_def : f.1 n with _ | _ | gn_def
    · have := isRight n
      simp [fn_def] at this
    · have := isRight' n
      simp [fn_def] at this
    · rcases (by
        simpa [partialInterpolationRightAlpha, Ext.edge, Ext.p, fn_def] using step) with
        ⟨z, z_mem, next_eq⟩
      simpa [g, fn_def, ←next_eq, edge] using z_mem
  intro n
  have ⟨m, m_prop⟩ := inf_path_has_inf_boxes g g_succ n
  use m
  rcases fn_def : f.1 (n + m) with _ | _ | gn_def
  · have := isRight (n + m)
    simp [fn_def] at this
  · have := isRight' (n + m)
    simp [fn_def] at this
  · simp only [partialInterpolationRightAlpha, Ext.r]
    apply split_to_ext_isBox
    convert m_prop
    unfold g
    simp [fn_def]

/-- The `path` field of the cut-based right interpolation proof: every infinite path through the
combined coalgebra meets a box rule infinitely often. -/
theorem partialInterpolationRightPath {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X)
    (𝕐₂ : Split.Proof) (y₂ : 𝕐₂.X) :
    ∀ node, ∀ f : {f : ℕ → (Unit ⊕ (partialEquationRight x).X ⊕ 𝕐₂.X) //
        f 0 = node ∧ ∀ (n : ℕ),
          Ext.edge (partialInterpolationRightAlpha x 𝕐₂ y₂) (f n) (f (n + 1))},
      ∀ n, ∃ m, (Ext.r (partialInterpolationRightAlpha x 𝕐₂ y₂) (f.1 (n + m))).isBox := by
  intro node f
  match node with
  | Sum.inl u => exact partialInterpolationRightPath_inl x 𝕐₂ y₂ u f
  | Sum.inr (Sum.inl z) => exact partialInterpolationRightPath_inlz x 𝕐₂ y₂ z f
  | Sum.inr (Sum.inr z) => exact partialInterpolationRightPath_inrz x 𝕐₂ y₂ z f


/-- Auxiliary declaration used in the GL coalgebra development. -/
noncomputable def partialInterpolationRight {𝕏 : Proof} [fin_X : Fintype 𝕏.X]
    (x : 𝕏.X) : Ext.PreProof x (@rightInterpolantSequent 𝕏 _) :=
  if eq : interpolant 𝕏 (at (encodeVar x)) = interpolant 𝕏 (equation x)
  then partialEquationRight x
  else
    have equiv : interpolant 𝕏 (at (encodeVar x)) ≅ interpolant 𝕏 (equation x) := by
      have := (interpolant_prop x ).1
      simp_all
    let 𝕐₂ := equiv.2.choose
    let y₂ := equiv.2.choose_spec.choose
    have y₂_prop := equiv.2.choose_spec.choose_spec
    { X := Unit ⊕ (partialEquationRight x).X ⊕ 𝕐₂.X
      α := partialInterpolationRightAlpha x 𝕐₂ y₂
      step := by
        have split_to_ext_f {𝕐 : Split.Proof} {x : 𝕐.X} {τ} (r : Split.RuleApp) :
            Ext.f (@splitToExt _ x τ r) = f r := by
          unfold splitToExt
          cases r <;> simp [f, Ext.f]
        have split_to_ext_fₙ {𝕐 : Split.Proof} {x : 𝕐.X} {τ} (r : Split.RuleApp) :
            Ext.fₙ (@splitToExt _ x τ r) = fₙ r := by
          unfold splitToExt
          cases r <;> simp [fₙ_alternate, Ext.fₙ_alternate]
        intro node
        match node with
        | Sum.inl u =>
            simp only [partialInterpolationRightAlpha, Ext.r, Ext.T, Ext.p, List.map_cons,
              split_to_ext_f, List.map_nil, Ext.fₙ_alternate, List.cons.injEq, and_true]
            constructor
            · convert partialEquationRight_proves_eq_aux x
              simp only [rightEquationSequent, rightInterpolantSequent, Ext.Proves]
              have hset :
                  ({Sum.inl (~interpolant 𝕏 (at encodeVar x))} ∪
                      (f (r 𝕏.α x)).filterRight).filterRight ∪
                    {Sum.inl (~interpolant 𝕏 (equation x))} =
                  {Sum.inl (~interpolant 𝕏 (equation x))} ∪ (f (r 𝕏.α x)).filterRight := by
                ext a
                cases a <;> simp [Finset.mem_filter]
              rw [hset]
              rfl
            · convert y₂_prop using 1
              simp [rightInterpolantSequent]
              aesop
        | Sum.inr (Sum.inl z₁) =>
            have 𝕐₁_h := (partialEquationRight x).step z₁
            simp only [partialInterpolationRightAlpha, Ext.r, Ext.p, List.map_map,
              Function.comp_def]
            convert 𝕐₁_h using 2 <;> simp [Ext.p, Ext.r, List.map_eq_nil_iff]
        | Sum.inr (Sum.inr z₂) =>
            have 𝕐₂_h := 𝕐₂.step z₂
            simp only [partialInterpolationRightAlpha, Ext.r]
            split
            all_goals
              rename_i eq
              cases r_def : r 𝕐₂.α z₂ <;> simp [r_def, splitToExt] at eq
              all_goals
                replace 𝕐₂_h := by simpa [r_def] using 𝕐₂_h
                simp only [partialInterpolationRightAlpha, Ext.T, Ext.p, 𝕐₂_h, List.map_nil,
                  List.empty_eq, List.map_map, Finset.union_singleton, Finset.union_insert,
                  List.map_eq_singleton_iff, Function.comp_apply]
                all_goals
                  convert 𝕐₂_h
                  all_goals
                    try simp [split_to_ext_f, split_to_ext_fₙ]
                    try tauto
      root := Sum.inl ()
      path := by
        intro node
        exact partialInterpolationRightPath x 𝕐₂ y₂ node }

lemma Split_to_Ext_isBox {𝕏 : Split.Proof} {x : 𝕏.X} {τ} (r : Split.RuleApp) :
    r.isBox → (@splitToExt _ x τ r).isBox := by
  unfold splitToExt
  cases r <;> simp [RuleApp.isBox, Ext.RuleApp.isBox]

lemma Split_to_Ext_notNonAxLeaf {𝕏 : Split.Proof} {x : 𝕏.X} {τ} (r : Split.RuleApp) :
    ¬ (@splitToExt _ x τ r).isNonAxLeaf := by
  unfold splitToExt
  cases r <;> simp [Ext.RuleApp.isNonAxLeaf]

lemma Split_to_Ext_f {𝕏 : Split.Proof} {x : 𝕏.X} {τ} (r : Split.RuleApp) :
    Ext.f (@splitToExt _ x τ r) = f r := by
  unfold splitToExt
  cases r <;> simp [f, Ext.f]

lemma Split_to_Ext_fₚ {𝕏 : Split.Proof} {x : 𝕏.X} {τ} (r : Split.RuleApp) :
    Ext.fₚ (@splitToExt _ x τ r) = fₚ r := by
  unfold splitToExt
  cases r <;> simp [fₚ, Ext.fₚ]

lemma Split_to_Ext_fₙ {𝕏 : Split.Proof} {x : 𝕏.X} {τ} (r : Split.RuleApp) :
    Ext.fₙ (@splitToExt _ x τ r) = fₙ r := by
  unfold splitToExt
  cases r <;> simp [fₙ_alternate, Ext.fₙ_alternate]

lemma partialEquationLeft_proves_eq {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) :
  Ext.Proves x (partialEquationLeft x) (leftEquationSequent x) :=
  partialEquationLeft_proves_eq_aux x

/-- Every left partial interpolation proof `Lₓ` proves `f(x)ˡ ∣ ιₓ`. -/
lemma partialInterpolationLeft_proves_int {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) :
  Ext.Proves x (partialInterpolationLeft x) (leftInterpolantSequent x) :=
  if eq : interpolant 𝕏 (at (encodeVar x)) = interpolant 𝕏 (equation x) then (by
    convert partialEquationLeft_proves_eq x using 1
    · unfold partialInterpolationLeft
      simp [eq]
    · unfold leftInterpolantSequent leftEquationSequent
      simp [eq])
  else by
    unfold partialInterpolationLeft
    simp [eq]
    simp [Ext.Proves, partialInterpolationLeftAlpha, Ext.r, Ext.f]

open Classical in
/-- For every `x` in a finite split proof, the partial left interpolation proof associated with `x`
    has the property that on every path from the root to a non-axiomatic leaf, the box rule is
    applied on this path. -/
theorem partialInterpolationLeft_box_prop {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) :
  (r 𝕏.α x).isBox →
    ∀ (n : ℕ) (f : Fin (n + 1) → (partialInterpolationLeft x).X),
      f 0 = (partialInterpolationLeft x).root →
        (Ext.r (partialInterpolationLeft x).α (f ⟨n, by simp⟩)).isNonAxLeaf →
          (∀ (m : Fin n), Ext.edge (partialInterpolationLeft x).α (f m.castSucc) (f m.succ)) →
            ∃ m, (Ext.r (partialInterpolationLeft x).α (f m)).isBox := by
  intro isBox n
  have 𝕏_h := 𝕏.step x
  cases r_def : r 𝕏.α x <;> simp_all only [RuleApp.isBox, Bool.false_eq_true]
  case boxₗ =>
    by_cases eq : interpolant 𝕏 (at (encodeVar x)) = interpolant 𝕏 (equation x)
    · unfold partialInterpolationLeft
      rw [dif_pos eq, partialEquationLeft]
      split <;> simp_all only [RuleApp.boxₗ.injEq, reduceCtorEq]
      intro f f_zero f_last f_succ
      use 0
      simp [partialLeftBoxₗ, f_zero]
      split <;> simp_all
      simp [Ext.r, Ext.RuleApp.isBox]
    · unfold partialInterpolationLeft
      rw [dif_neg eq]
      intro f f_zero f_last f_succ
      use 1
      cases n
      case zero =>
        exfalso
        simp_all
        simp [partialInterpolationLeftAlpha, Ext.r, Ext.RuleApp.isNonAxLeaf] at f_last
      case succ n =>
        have step := f_succ 0
        simp only [partialInterpolationLeftAlpha, Ext.edge, Ext.p, Lean.Elab.WF.paramLet,
          Fin.castSucc_zero,
          f_zero, Fin.succ_zero_eq_one, List.mem_cons, List.not_mem_nil, or_false] at step
        rcases step with l | r
        · rw [l]
          simp [partialInterpolationLeftAlpha, Ext.r]
          simp [partialEquationLeft, partialLeftBoxₗ]
          split <;> simp_all
          split <;> simp_all [Ext.RuleApp.isBox]
        · exfalso
          simp only [partialInterpolationLeftAlpha, Ext.r] at f_last
          have isRight : ∀ m : Fin (n + 1), (f m.succ).isRight := by
            intro n
            induction n using Fin.induction
            case zero => simp [r]
            case succ k ih =>
              have step := f_succ k.succ
              rcases fk_def : f k.castSucc.succ with l | r
              · simp [fk_def] at ih
              · rcases r with z₁ | z₂
                · rcases (by
                    simpa [partialInterpolationLeftAlpha, Ext.edge, Ext.p, fk_def] using step) with
                    ⟨z, _z_mem, next_eq⟩
                  simp [←next_eq]
                · rcases (by
                    simpa [partialInterpolationLeftAlpha, Ext.edge, Ext.p, fk_def] using step) with
                    ⟨z, _z_mem, next_eq⟩
                  simp [←next_eq]
          have isRight' : ∀ m : Fin (n + 1), ((f m.succ).getRight (isRight m)).isRight := by
                intro n
                induction n using Fin.induction
                case zero => simp [r]
                case succ k ih =>
                  have step := f_succ k.succ
                  rcases fk_def : f k.castSucc.succ with _ | l | r
                  · have := isRight k.castSucc
                    simp [fk_def] at this
                  · simp [fk_def] at ih
                  · rcases (by
                      simpa [partialInterpolationLeftAlpha, Ext.edge, Ext.p, fk_def]
                        using step) with
                      ⟨z, _z_mem, next_eq⟩
                    simp [←next_eq]
          rcases f_last_def : f ⟨n + 1, by simp⟩ with c1 | ⟨c2 | c3⟩
          · have := isRight ⟨n, by simp⟩
            simp [f_last_def] at this
          · have := isRight' ⟨n, by simp⟩
            simp [f_last_def] at this
          · exact @Split_to_Ext_notNonAxLeaf 𝕏 x leftInterpolantSequent _
              (by simpa [f_last_def] using f_last)
  case boxᵣ =>
    by_cases eq : interpolant 𝕏 (at (encodeVar x)) = interpolant 𝕏 (equation x)
    · unfold partialInterpolationLeft
      rw [dif_pos eq, partialEquationLeft]
      split <;> simp_all only [RuleApp.boxᵣ.injEq, reduceCtorEq]
      intro f f_zero f_last f_succ
      use 0
      simp [partialLeftBoxᵣ, f_zero]
      split <;> simp_all
      simp [Ext.r, Ext.RuleApp.isBox]
    · unfold partialInterpolationLeft
      rw [dif_neg eq]
      intro f f_zero f_last f_succ
      use 1
      cases n
      case zero =>
        exfalso
        simp_all
        simp [partialInterpolationLeftAlpha, Ext.r, Ext.RuleApp.isNonAxLeaf] at f_last
      case succ n =>
        have step := f_succ 0
        simp only [partialInterpolationLeftAlpha, Ext.edge, Ext.p, Lean.Elab.WF.paramLet,
          Fin.castSucc_zero,
          f_zero, Fin.succ_zero_eq_one, List.mem_cons, List.not_mem_nil, or_false] at step
        rcases step with l | r
        · rw [l]
          simp [partialInterpolationLeftAlpha, Ext.r]
          simp [partialEquationLeft, partialLeftBoxᵣ]
          split <;> simp_all
          split <;> simp_all [Ext.RuleApp.isBox]
        · exfalso
          simp only [partialInterpolationLeftAlpha, Ext.r] at f_last
          have isRight : ∀ m : Fin (n + 1), (f m.succ).isRight := by
            intro n
            induction n using Fin.induction
            case zero => simp [r]
            case succ k ih =>
              have step := f_succ k.succ
              rcases fk_def : f k.castSucc.succ with l | r
              · simp [fk_def] at ih
              · rcases r with z₁ | z₂
                · rcases (by
                    simpa [partialInterpolationLeftAlpha, Ext.edge, Ext.p, fk_def] using step) with
                    ⟨z, _z_mem, next_eq⟩
                  simp [←next_eq]
                · rcases (by
                    simpa [partialInterpolationLeftAlpha, Ext.edge, Ext.p, fk_def] using step) with
                    ⟨z, _z_mem, next_eq⟩
                  simp [←next_eq]
          have isRight' : ∀ m : Fin (n + 1), ((f m.succ).getRight (isRight m)).isRight := by
                intro n
                induction n using Fin.induction
                case zero => simp [r]
                case succ k ih =>
                  have step := f_succ k.succ
                  rcases fk_def : f k.castSucc.succ with _ | l | r
                  · have := isRight k.castSucc
                    simp [fk_def] at this
                  · simp [fk_def] at ih
                  · rcases (by
                      simpa [partialInterpolationLeftAlpha, Ext.edge, Ext.p, fk_def]
                        using step) with
                      ⟨z, _z_mem, next_eq⟩
                    simp [←next_eq]
          rcases f_last_def : f ⟨n + 1, by simp⟩ with c1 | ⟨c2 | c3⟩
          · have := isRight ⟨n, by simp⟩
            simp [f_last_def] at this
          · have := isRight' ⟨n, by simp⟩
            simp [f_last_def] at this
          · exact @Split_to_Ext_notNonAxLeaf 𝕏 x leftInterpolantSequent _
              (by simpa [f_last_def] using f_last)

/-- Defining the left interpolation proof with all non-axiomatic nodes removed. -/
noncomputable def interpolantProofLeft {𝕏 : Proof}
    [fin_X : Fintype 𝕏.X] : ExtSkip.Proof :=
  @proofTransformation 𝕏 (@leftInterpolantSequent 𝕏 _) partialInterpolationLeft
    partialInterpolationLeft_proves_int partialInterpolationLeft_box_prop

/-- Every right partial interpolation proof `Rₓ` proves `~ιₓ ∣ f(x)ʳ`. -/
lemma partialEquationRight_proves_eq {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) :
  Ext.Proves x (partialEquationRight x) (rightEquationSequent x) :=
  partialEquationRight_proves_eq_aux x

lemma partialInterpolationRight_proves_int {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) :
  Ext.Proves x (partialInterpolationRight x) (rightInterpolantSequent x) :=
  if eq : interpolant 𝕏 (at (encodeVar x)) = interpolant 𝕏 (equation x) then (by
    convert partialEquationRight_proves_eq x using 1
    · unfold partialInterpolationRight
      simp [eq]
    · unfold rightInterpolantSequent rightEquationSequent
      simp [eq])
  else by
    unfold partialInterpolationRight
    simp [eq]
    simp [Ext.Proves, partialInterpolationRightAlpha, Ext.r, Ext.f]

open Classical in
/-- For every `x` in a finite split proof, the partial left interpolation proof associated with `x`
    has the property that on every path from the root to a non-axiomatic leaf, the box rule is
    applied on this path. -/
theorem partialInterpolationRight_box_prop {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) :
  (r 𝕏.α x).isBox →
    ∀ (n : ℕ) (f : Fin (n + 1) → (partialInterpolationRight x).X),
      f 0 = (partialInterpolationRight x).root →
        (Ext.r (partialInterpolationRight x).α (f ⟨n, by simp⟩)).isNonAxLeaf →
          (∀ (m : Fin n), Ext.edge (partialInterpolationRight x).α (f m.castSucc) (f m.succ)) →
            ∃ m, (Ext.r (partialInterpolationRight x).α (f m)).isBox := by
  intro isBox n
  have 𝕏_h := 𝕏.step x
  cases r_def : r 𝕏.α x <;> simp_all only [RuleApp.isBox, Bool.false_eq_true]
  case boxₗ =>
    by_cases eq : interpolant 𝕏 (at (encodeVar x)) = interpolant 𝕏 (equation x)
    · unfold partialInterpolationRight
      rw [dif_pos eq, partialEquationRight]
      split <;> simp_all only [RuleApp.boxₗ.injEq, reduceCtorEq]
      intro f f_zero f_last f_succ
      use 0
      simp [partialRightBoxₗ, f_zero]
      split <;> simp_all
      simp [Ext.r, Ext.RuleApp.isBox]
    · unfold partialInterpolationRight
      rw [dif_neg eq]
      intro f f_zero f_last f_succ
      use 1
      cases n
      case zero =>
        exfalso
        simp_all
        simp [partialInterpolationRightAlpha, Ext.r, Ext.RuleApp.isNonAxLeaf] at f_last
      case succ n =>
        have step := f_succ 0
        simp only [partialInterpolationRightAlpha, Ext.edge, Ext.p, Lean.Elab.WF.paramLet,
          Fin.castSucc_zero,
          f_zero, Fin.succ_zero_eq_one, List.mem_cons, List.not_mem_nil, or_false] at step
        rcases step with l | r
        · rw [l]
          simp [partialInterpolationRightAlpha, Ext.r]
          simp [partialEquationRight, partialRightBoxₗ]
          split <;> simp_all
          split <;> simp_all [Ext.RuleApp.isBox]
        · exfalso
          simp only [partialInterpolationRightAlpha, Ext.r] at f_last
          have isRight : ∀ m : Fin (n + 1), (f m.succ).isRight := by
            intro n
            induction n using Fin.induction
            case zero => simp [r]
            case succ k ih =>
              have step := f_succ k.succ
              rcases fk_def : f k.castSucc.succ with l | r
              · simp [fk_def] at ih
              · rcases r with z₁ | z₂
                · rcases (by
                    simpa [partialInterpolationRightAlpha, Ext.edge, Ext.p, fk_def] using step) with
                    ⟨z, _z_mem, next_eq⟩
                  simp [←next_eq]
                · rcases (by
                    simpa [partialInterpolationRightAlpha, Ext.edge, Ext.p, fk_def] using step) with
                    ⟨z, _z_mem, next_eq⟩
                  simp [←next_eq]
          have isRight' : ∀ m : Fin (n + 1), ((f m.succ).getRight (isRight m)).isRight := by
                intro n
                induction n using Fin.induction
                case zero => simp [r]
                case succ k ih =>
                  have step := f_succ k.succ
                  rcases fk_def : f k.castSucc.succ with _ | l | r
                  · have := isRight k.castSucc
                    simp [fk_def] at this
                  · simp [fk_def] at ih
                  · rcases (by
                      simpa [partialInterpolationRightAlpha, Ext.edge, Ext.p, fk_def]
                        using step) with
                      ⟨z, _z_mem, next_eq⟩
                    simp [←next_eq]
          rcases f_last_def : f ⟨n + 1, by simp⟩ with c1 | ⟨c2 | c3⟩
          · have := isRight ⟨n, by simp⟩
            simp [f_last_def] at this
          · have := isRight' ⟨n, by simp⟩
            simp [f_last_def] at this
          · exact @Split_to_Ext_notNonAxLeaf 𝕏 x rightInterpolantSequent _
              (by simpa [f_last_def] using f_last)
  case boxᵣ =>
    by_cases eq : interpolant 𝕏 (at (encodeVar x)) = interpolant 𝕏 (equation x)
    · unfold partialInterpolationRight
      rw [dif_pos eq, partialEquationRight]
      split <;> simp_all only [RuleApp.boxᵣ.injEq, reduceCtorEq]
      intro f f_zero f_last f_succ
      use 0
      simp [partialRightBoxᵣ, f_zero]
      split <;> simp_all
      simp [Ext.r, Ext.RuleApp.isBox]
    · unfold partialInterpolationRight
      rw [dif_neg eq]
      intro f f_zero f_last f_succ
      use 1
      cases n
      case zero =>
        exfalso
        simp_all
        simp [partialInterpolationRightAlpha, Ext.r, Ext.RuleApp.isNonAxLeaf] at f_last
      case succ n =>
        have step := f_succ 0
        simp only [partialInterpolationRightAlpha, Ext.edge, Ext.p, Lean.Elab.WF.paramLet,
          Fin.castSucc_zero,
          f_zero, Fin.succ_zero_eq_one, List.mem_cons, List.not_mem_nil, or_false] at step
        rcases step with l | r
        · rw [l]
          simp [partialInterpolationRightAlpha, Ext.r]
          simp [partialEquationRight, partialRightBoxᵣ]
          split <;> simp_all
          split <;> simp_all [Ext.RuleApp.isBox]
        · exfalso
          simp only [partialInterpolationRightAlpha, Ext.r] at f_last
          have isRight : ∀ m : Fin (n + 1), (f m.succ).isRight := by
            intro n
            induction n using Fin.induction
            case zero => simp [r]
            case succ k ih =>
              have step := f_succ k.succ
              rcases fk_def : f k.castSucc.succ with l | r
              · simp [fk_def] at ih
              · rcases r with z₁ | z₂
                · rcases (by
                    simpa [partialInterpolationRightAlpha, Ext.edge, Ext.p, fk_def] using step) with
                    ⟨z, _z_mem, next_eq⟩
                  simp [←next_eq]
                · rcases (by
                    simpa [partialInterpolationRightAlpha, Ext.edge, Ext.p, fk_def] using step) with
                    ⟨z, _z_mem, next_eq⟩
                  simp [←next_eq]
          have isRight' : ∀ m : Fin (n + 1), ((f m.succ).getRight (isRight m)).isRight := by
                intro n
                induction n using Fin.induction
                case zero => simp [r]
                case succ k ih =>
                  have step := f_succ k.succ
                  rcases fk_def : f k.castSucc.succ with _ | l | r
                  · have := isRight k.castSucc
                    simp [fk_def] at this
                  · simp [fk_def] at ih
                  · rcases (by
                      simpa [partialInterpolationRightAlpha, Ext.edge, Ext.p, fk_def]
                        using step) with
                      ⟨z, _z_mem, next_eq⟩
                    simp [←next_eq]
          rcases f_last_def : f ⟨n + 1, by simp⟩ with c1 | ⟨c2 | c3⟩
          · have := isRight ⟨n, by simp⟩
            simp [f_last_def] at this
          · have := isRight' ⟨n, by simp⟩
            simp [f_last_def] at this
          · exact @Split_to_Ext_notNonAxLeaf 𝕏 x rightInterpolantSequent _
              (by simpa [f_last_def] using f_last)

/-- Defining the right interpolation proof with all non-axiomatic nodes removed. -/
noncomputable def interpolantProofRight {𝕏 : Proof}
    [fin_X : Fintype 𝕏.X] : ExtSkip.Proof :=
  @proofTransformation 𝕏 (@rightInterpolantSequent 𝕏 _) partialInterpolationRight
    partialInterpolationRight_proves_int partialInterpolationRight_box_prop

/-- Left syntactic interpolation result! -/
theorem interpolantProofLeft_proves_interpolant {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X)
  : @interpolantProofLeft 𝕏 fin_X ⊢ leftInterpolantSequent x := by
  use ⟨x, (partialInterpolationLeft x).root⟩
  unfold interpolantProofLeft proofTransformation
  simp only [proofTransformation_f]
  exact partialInterpolationLeft_proves_int x

/-- Right syntactic interpolation result! -/
theorem interpolantProofRight_proves_interpolant {𝕏 : Proof} [fin_X : Fintype 𝕏.X]
    (x : 𝕏.X)
  : @interpolantProofRight 𝕏 fin_X ⊢ rightInterpolantSequent x := by
  use ⟨x, (partialInterpolationRight x).root⟩
  unfold interpolantProofRight proofTransformation
  simp only [proofTransformation_f]
  exact partialInterpolationRight_proves_int x


/-- Given a finite split proof, `interpolantProofLeft` proves the left interpolation correctness
statement and `interpolantProofRight` proves the right interpolation correctness statement. -/
theorem syntactic_interpolation {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) :
    (@interpolantProofLeft 𝕏 fin_X  ⊢ leftInterpolantSequent  x)
  ∧ (@interpolantProofRight 𝕏 fin_X ⊢ rightInterpolantSequent x) :=
  ⟨interpolantProofLeft_proves_interpolant x, interpolantProofRight_proves_interpolant x⟩
end Lean4GlCoalgebras
