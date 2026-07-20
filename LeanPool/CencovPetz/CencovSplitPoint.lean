/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import LeanPool.CencovPetz.SplittingInvariance
import LeanPool.CencovPetz.SplittingUniform
import LeanPool.CencovPetz.RationalPoint
import LeanPool.CencovPetz.UniformScalarConstant
import LeanPool.CencovPetz.UniformScalarMultiple


/-!
# `CencovPetz.CencovSplitPoint`

Extend the **uniform-point** scalar-multiple lemma to simplex points that become uniform after a
fiberwise split.

This isolates the “rational-point reduction” step in a finite Čencov/Chentsov uniqueness proof:
if `p` has coordinates proportional to a natural multiplicity function `m : α → ℕ`, then splitting
`α → Σ a, Fin (m a)` sends `p` to the uniform distribution, and the monotone metric at `p` is a
scalar multiple of Fisher.

## Main result

- `CencovPetz.MonotoneMetricFamily.eq_smul_fisher_of_isSplitRepresentable`
-/

namespace LeanPool.CencovPetz
open scoped BigOperators

namespace MonotoneMetricFamily

open MarkovMorphism

/-- If `p` is split-representable (so it splits to the uniform point), then the metric at `p` is a
scalar multiple of Fisher.

The scalar is the one given by the uniform-point characterization on the split target. -/
theorem eq_smul_fisher_of_isSplitRepresentable (G : MonotoneMetricFamily)
    {α : Type} [Fintype α] [Nonempty α]
    (p : Simplex α) (hp : Simplex.IsSplitRepresentable (α := α) p)
    {a0 a1 : α} (ha01 : a0 ≠ a1) :
    ∀ u v : tangentSpace (α := α),
      G.g (α := α) p u v = (uniformScalar G 2 (by decide)) * fisherBilin p u v := by
  classical
  rcases hp with ⟨m, hm, hp⟩
  -- Split target `β := Σ a, Fin (m a)`.
  let β := SplitTarget (α := α) m
  haveI : Nonempty β := ⟨⟨a0, ⟨0, hm a0⟩⟩⟩
  have h_uniform :
      (split (α := α) m hm).pushforward p = Simplex.uniform (α := β) := by
    simpa [β] using
      split_pushforward_eq_uniform_of_apply_eq_div_card (α := α) (m := m) (hm := hm) (p := p) hp
  -- Reduce the uniform point on `β` to the uniform point on `Fin n`.
  let n : ℕ := Fintype.card β
  let e : β ≃ Fin n := Fintype.equivFin β
  let b0 : β := ⟨a0, ⟨0, hm a0⟩⟩
  let b1 : β := ⟨a1, ⟨0, hm a1⟩⟩
  have hb01 : b0 ≠ b1 := by
    intro h
    exact ha01 (congrArg Sigma.fst h)
  have hn : 2 ≤ n := by
    have h : 1 < Fintype.card β :=
      (Fintype.one_lt_card_iff).2 ⟨b0, b1, hb01⟩
    have h' : 1 < n := by simpa [n] using h
    exact Nat.succ_le_iff.2 h'
  let i0 : Fin n := ⟨0, lt_of_lt_of_le Nat.zero_lt_two hn⟩
  let i1 : Fin n := ⟨1, lt_of_lt_of_le Nat.one_lt_two hn⟩
  have hi01 : i0 ≠ i1 := by
    intro h
    exact Nat.zero_ne_one (congrArg Fin.val h)
  haveI : Nonempty (Fin n) := ⟨i0⟩
  have h_equiv_uniform :
      (MarkovMorphism.deterministic
        (α := β) (β := Fin n) (g := (e : β → Fin n))
        e.surjective).pushforward
          (Simplex.uniform (α := β))
        =
        Simplex.uniform (α := Fin n) := by
    ext j
    have hj :
        ((MarkovMorphism.deterministic
            (α := β) (β := Fin n) (g := (e : β → Fin n))
            e.surjective).pushforward
              (Simplex.uniform (α := β))).p j
          =
          (Simplex.uniform (α := β)).p (e.symm j) := by
      simpa using
        (MarkovMorphism.deterministic_pushforward_apply_of_equiv (α := β) (β := Fin n) (e := e)
          (p := Simplex.uniform (α := β)) (b := j))
    -- Both sides are `1 / |β| = 1 / n`.
    rw [hj]
    simp [Simplex.uniform_apply, Fintype.card_congr e]
  -- Uniform-point scalar-multiple identity on `Fin n`.
  have hFin :
      (TangentFin.Bilin.B (G := G) (n := n))
        =
        (uniformScalar G n hn) • fisherBilin (Simplex.uniform (α := Fin n)) := by
    simpa [MonotoneMetricFamily.uniformScalar, i0, i1] using
      (TangentFin.Bilin.B_eq_smul_fisherBilin_uniform (G := G) (n := n) (i0 := i0) (i1 := i1) hi01)
  have hscalar : uniformScalar G n hn = uniformScalar G 2 (by decide) :=
    uniformScalar_eq_uniformScalar_two (G := G) (n := n) hn
  -- Use that scalar for the result at `p`.
  intro u v
  -- Split invariance for `G` and for Fisher.
  have hG_split :
      G.g (α := α) p u v
        =
        G.g (α := β) ((split (α := α) m hm).pushforward p)
            ((split (α := α) m hm).tangentPushforward u)
            ((split (α := α) m hm).tangentPushforward v) := by
    simpa [β] using
      (MonotoneMetricFamily.eq_of_split (G := G) (α := α) (m := m) (hm := hm) (p := p) u v).symm
  have hF_split :
      fisherBilin p u v
        =
        fisherBilin ((split (α := α) m hm).pushforward p)
            ((split (α := α) m hm).tangentPushforward u)
            ((split (α := α) m hm).tangentPushforward v) := by
    simpa [fisherMetricFamily] using
      (MonotoneMetricFamily.eq_of_split
        (G := fisherMetricFamily) (α := α) (m := m)
        (hm := hm) (p := p) u v).symm
  -- Reduce to the uniform point on `β`.
  rw [hG_split, hF_split, h_uniform]
  -- Rewrite `G.g` and Fisher on `β` in terms of `Fin n` using `eq_of_equiv`.
  have hG_equiv :
      G.g (α := β) (Simplex.uniform (α := β))
          ((split (α := α) m hm).tangentPushforward u)
          ((split (α := α) m hm).tangentPushforward v)
        =
        G.g (α := Fin n)
          ((MarkovMorphism.deterministic
              (α := β) (β := Fin n)
              (g := (e : β → Fin n))
              e.surjective).pushforward
              (Simplex.uniform (α := β)))
          ((MarkovMorphism.deterministic
              (α := β) (β := Fin n)
              (g := (e : β → Fin n))
              e.surjective).tangentPushforward
              ((split (α := α) m hm).tangentPushforward u))
          ((MarkovMorphism.deterministic
              (α := β) (β := Fin n)
              (g := (e : β → Fin n))
              e.surjective).tangentPushforward
              ((split (α := α) m hm).tangentPushforward v)) := by
    symm
    simpa using
      (MonotoneMetricFamily.eq_of_equiv (G := G) (α := β) (β := Fin n) (e := e)
        (p := Simplex.uniform (α := β))
        ((split (α := α) m hm).tangentPushforward u)
        ((split (α := α) m hm).tangentPushforward v))
  have hF_equiv :
      fisherBilin (Simplex.uniform (α := β))
          ((split (α := α) m hm).tangentPushforward u)
          ((split (α := α) m hm).tangentPushforward v)
        =
        fisherBilin (Simplex.uniform (α := Fin n))
          ((MarkovMorphism.deterministic
              (α := β) (β := Fin n)
              (g := (e : β → Fin n))
              e.surjective).tangentPushforward
              ((split (α := α) m hm).tangentPushforward u))
          ((MarkovMorphism.deterministic
              (α := β) (β := Fin n)
              (g := (e : β → Fin n))
              e.surjective).tangentPushforward
              ((split (α := α) m hm).tangentPushforward v)) := by
    have h :=
      (MonotoneMetricFamily.eq_of_equiv (G := fisherMetricFamily) (α := β) (β := Fin n) (e := e)
        (p := Simplex.uniform (α := β))
        ((split (α := α) m hm).tangentPushforward u)
        ((split (α := α) m hm).tangentPushforward v))
    -- `h` has Fisher on the pushed-forward uniform point; rewrite that point as `Simplex.uniform`.
    have h' :
        fisherBilin (Simplex.uniform (α := Fin n))
            ((MarkovMorphism.deterministic
                (α := β) (β := Fin n)
                (g := (e : β → Fin n))
                e.surjective).tangentPushforward
                ((split (α := α) m hm).tangentPushforward u))
            ((MarkovMorphism.deterministic
                (α := β) (β := Fin n)
                (g := (e : β → Fin n))
                e.surjective).tangentPushforward
                ((split (α := α) m hm).tangentPushforward v))
          =
          fisherBilin (Simplex.uniform (α := β))
            ((split (α := α) m hm).tangentPushforward u)
            ((split (α := α) m hm).tangentPushforward v) := by
      simpa [fisherMetricFamily, h_equiv_uniform] using h
    simpa using h'.symm
  -- Apply the scalar multiple identity on `Fin n`.
  rw [hG_equiv, h_equiv_uniform]
  have hFin_apply :=
    congrArg
      (fun B =>
        B
          ((MarkovMorphism.deterministic
              (α := β) (β := Fin n)
              (g := (e : β → Fin n))
              e.surjective).tangentPushforward
              ((split (α := α) m hm).tangentPushforward u))
          ((MarkovMorphism.deterministic
              (α := β) (β := Fin n)
              (g := (e : β → Fin n))
              e.surjective).tangentPushforward
              ((split (α := α) m hm).tangentPushforward v)))
      hFin
  -- Rewrite the Fisher term back to `β`, then apply `hFin_apply`.
  rw [hF_equiv]
  -- Convert the left-hand side to the `B` abbreviation used in `hFin_apply`.
  simp_all

theorem eq_smul_fisher_of_isRational (G : MonotoneMetricFamily)
    {α : Type} [Fintype α] [Nonempty α]
    (p : Simplex α) (hp : Simplex.IsRational (α := α) p)
    {a0 a1 : α} (ha01 : a0 ≠ a1) :
    ∀ u v : tangentSpace (α := α),
      G.g (α := α) p u v = (uniformScalar G 2 (by decide)) * fisherBilin p u v := by
  simpa using
    (eq_smul_fisher_of_isSplitRepresentable (G := G) (p := p) (hp := hp.isSplitRepresentable) ha01)

end MonotoneMetricFamily
end LeanPool.CencovPetz
