/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ClosedTranslationGraph
public import Mathlib.Topology.Algebra.Module.ClosedSubmodule

@[expose] public section

/-! A complete cylinder Sobolev space constructed from closed graphs of actual L² derivatives. -/

noncomputable section

namespace EulerCylinderSobolevSpace

open EulerLiftedGradientSpace EulerPressureSpatialRegularity EulerSpatialSobolevInverse
  EulerCylinderSobolev EulerClosedTranslationGraph
open scoped Topology

/-- A coordinate derivative word of length at most the Sobolev order. -/
abbrev SobolevWord (q : ℕ) := Σ n : Fin (q + 1), Fin n.val → Fin 4

/-- An edge joining a derivative word to one further coordinate derivative. -/
abbrev SobolevEdge (q : ℕ) := Σ n : Fin q, (Fin n.val → Fin 4) × Fin 4

/-- The empty derivative word. -/
def emptyWord (q : ℕ) : SobolevWord q := ⟨⟨0, Nat.zero_lt_succ q⟩, Fin.elim0⟩

/-- The lower endpoint of a derivative edge. -/
def edgeParent {q : ℕ} (e : SobolevEdge q) : SobolevWord q :=
  ⟨⟨e.1.val, Nat.lt_succ_of_lt e.1.isLt⟩, e.2.1⟩

/-- The upper endpoint obtained by prepending one derivative direction. -/
def edgeChild {q : ℕ} (e : SobolevEdge q) : SobolevWord q :=
  ⟨⟨e.1.val + 1, Nat.succ_lt_succ e.1.isLt⟩, Fin.cons e.2.2 e.2.1⟩

variable (period : ℝ) [Fact (0 < period)]

/-- The closed graph of the actual strong translation derivative. -/
def closedDerivativeGraph (a : LiftTangent) : ClosedSubmodule ℝ (LiftL2 period × LiftL2 period)
  where
  toSubmodule := translationDerivativeGraph period a
  isClosed' := translationDerivativeGraph_closed period a

/-- Evaluation of the two endpoints of a derivative edge is continuous linear. -/
def edgeEvaluation {q : ℕ} (e : SobolevEdge q) :
    (SobolevWord q → LiftL2 period) →L[ℝ] (LiftL2 period × LiftL2 period) :=
  (ContinuousLinearMap.proj (edgeParent e)).prod (ContinuousLinearMap.proj (edgeChild e))

/-- The closed linear space of finite arrays satisfying every genuine derivative compatibility. -/
def sobolevSubspace (q : ℕ) : ClosedSubmodule ℝ (SobolevWord q → LiftL2 period) :=
  ⨅ e : SobolevEdge q,
    (closedDerivativeGraph period (standardDirection e.2.2)).comap (edgeEvaluation period e)

/-- The actual cylinder Sobolev space, with the complete finite-array norm. -/
abbrev SobolevSpace (q : ℕ) := sobolevSubspace period q

/-- The Sobolev norm is the norm inherited from the underlying submodule of derivative arrays. -/
instance sobolevNormedAddCommGroup (q : ℕ) : NormedAddCommGroup (SobolevSpace period q) :=
  inferInstanceAs (NormedAddCommGroup (sobolevSubspace period q).toSubmodule)

/-- Scalar multiplication uses the same inherited norm as the derivative array. -/
instance sobolevNormedSpace (q : ℕ) : NormedSpace ℝ (SobolevSpace period q) :=
  inferInstanceAs (NormedSpace ℝ (sobolevSubspace period q).toSubmodule)

/-- Completeness follows from closedness of the derivative graphs in a finite product of L² spaces. -/
theorem sobolev_complete (q : ℕ) : CompleteSpace (SobolevSpace period q) := inferInstance

/-- The underlying L² field of a Sobolev derivative array. -/
def value {q : ℕ} (u : SobolevSpace period q) : LiftL2 period := u.val (emptyWord q)

/-- A valid derivative word in the array. -/
def word {q n : ℕ} (u : SobolevSpace period q) (hn : n ≤ q) (w : Fin n → Fin 4) : LiftL2 period :=
  u.val ⟨⟨n, Nat.lt_succ_of_le hn⟩, w⟩

/-- The defining compatibility is a genuine strong derivative of an L² translation orbit. -/
theorem word_hasDerivAt {q n : ℕ} (u : SobolevSpace period q) (hn : n < q)
    (w : Fin n → Fin 4) (i : Fin 4) :
    HasDerivAt (fun t => translation period (translationPath period (standardDirection i) t)
      (word period u hn.le w)) (word period u (Nat.succ_le_of_lt hn) (Fin.cons i w)) 0 := by
  have h := (ClosedSubmodule.mem_iInf.mp u.property) (⟨⟨n, hn⟩, w, i⟩ : SobolevEdge q)
  exact h

/-- Every finite strong derivative jet defines an element of the complete Sobolev space. -/
def ofJet {q : ℕ} {f : LiftL2 period} (J : SpatialJet period standardDirection q f) :
    SobolevSpace period q := by
  refine ⟨fun w => J.word w.2, ?_⟩
  apply ClosedSubmodule.mem_iInf.mpr
  intro e
  exact J.word_hasDerivAt e.1.isLt e.2.1 e.2.2

/-- The underlying field of the array constructed from a jet is unchanged. -/
@[simp]
theorem value_ofJet {q : ℕ} {f : LiftL2 period} (J : SpatialJet period standardDirection q f) :
    value period (ofJet period J) = f := by simp [value, ofJet, emptyWord]

/-- Every compatible array has a genuine jet of any remaining depth at every word. -/
theorem word_has_jet {q : ℕ} (u : SobolevSpace period q) (r n : ℕ)
    (h : n + r ≤ q) (w : Fin n → Fin 4) :
    Nonempty (SpatialJet period standardDirection r (word period u (by omega) w)) := by
  induction r generalizing n with
  | zero => exact ⟨.zero _⟩
  | succ r ih =>
    have hn : n < q := by omega
    refine ⟨.succ (fun i => word period u (by omega) (Fin.cons i w))
      (fun i => Classical.choice (ih (n + 1) (by omega) (Fin.cons i w))) ?_⟩
    intro i
    exact word_hasDerivAt period u hn w i

/-- A genuine full-depth strong derivative jet reconstructed from a Sobolev array. -/
def toJet {q : ℕ} (u : SobolevSpace period q) : SpatialJet period standardDirection q (value period
  u) :=
  Classical.choice (word_has_jet period u q 0 (by omega) Fin.elim0)

/-- Any genuine jet with the correct underlying field agrees with every array coordinate. -/
theorem jet_word_eq {q n : ℕ} (u : SobolevSpace period q)
    (J : SpatialJet period standardDirection q (value period u))
    (hn : n ≤ q) (w : Fin n → Fin 4) : J.word w = word period u hn w := by
  induction n with
  | zero =>
    rw [SpatialJet.word_zero]
    have hw : w = Fin.elim0 := Subsingleton.elim _ _
    subst w
    rfl
  | succ n ih =>
    have hJ := J.word_hasDerivAt (by omega : n < q) (Fin.tail w) (w 0)
    have hu := word_hasDerivAt period u (by omega : n < q) (Fin.tail w) (w 0)
    rw [ih (by omega) (Fin.tail w)] at hJ
    simpa only [Fin.cons_self_tail] using hJ.unique hu

/-- Reconstructing a jet preserves each genuine derivative coordinate. -/
theorem toJet_word {q n : ℕ} (u : SobolevSpace period q) (hn : n ≤ q) (w : Fin n → Fin 4) :
    (toJet period u).word w = word period u hn w := jet_word_eq period u _ hn w

/-- A Sobolev array is uniquely determined by its underlying L² field. -/
theorem value_injective {q : ℕ} : Function.Injective (value period : SobolevSpace period q → LiftL2
  period) := by
  intro u v huv
  apply Subtype.ext
  funext w
  have h := EulerPressureJetIdentities.SpatialJet.word_unique
    (toJet period u) (toJet period v) huv (Nat.le_of_lt_succ w.1.isLt)
      (Nat.le_of_lt_succ w.1.isLt) w.2
  rw [toJet_word period u (Nat.le_of_lt_succ w.1.isLt),
    toJet_word period v (Nat.le_of_lt_succ w.1.isLt)] at h
  exact h

/-- Reconstructing a jet and then its array is the identity. -/
@[simp]
theorem ofJet_toJet {q : ℕ} (u : SobolevSpace period q) : ofJet period (toJet period u) = u := by
  apply value_injective period
  exact value_ofJet period (toJet period u)

end EulerCylinderSobolevSpace
