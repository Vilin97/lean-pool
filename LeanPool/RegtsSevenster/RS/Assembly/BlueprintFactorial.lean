/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Envelope.FactorialTrace
public import LeanPool.RegtsSevenster.RS.Novel.Envelope.KaroubiSemisimple
public import LeanPool.RegtsSevenster.RS.Novel.Envelope.ObjectTower
public import LeanPool.RegtsSevenster.RS.Summit

/-!
# Audit: the factorial route to nilpotent-trace vanishing

The statements and axioms of the factorial obstruction are pinned
here. The final check traverses the types and proof bodies of the
factorial route, including opaque declarations, and rejects dependencies
on the Schur, hook-confinement, trace-zeta or Deligne engines.
Imported modules alone do not constitute a proof dependency.

The appendix proof serves as a control: the same traversal must
find an excluded dependency in that proof. This audit checks
independence of the nilpotent-trace and semisimplicity lemmas.
The summit checks require the factorial theorem in their transitive
dependencies and exclude the appendix's nilpotent-trace and
trace-zeta mechanisms. Schur theory used by Deligne and by the
colour bounds is audited separately.
-/

@[expose] public section

namespace RS

/-! ### Statements -/

/- Upstream audit output: @SinglePowerTrace : {A : Type u_1} → [inst : Ring A] → [inst_1 : Algebra ℂ A] → (A →ₗ[ℂ] ℂ) → A → Prop -/

/- Upstream audit output: @SinglePowerTrace.mk : ∀ {A : Type u_1} [inst : Ring A] [inst_1 : Algebra ℂ A] {τ : A →ₗ[ℂ] ℂ} {y : A},
  τ y ≠ 0 → (∀ (m : ℕ), 2 ≤ m → τ (y ^ m) = 0) → SinglePowerTrace τ y -/

/- Upstream audit output: CycleTraceTower : (E : ℕ → Type u_1) →
  [inst : (n : ℕ) → Ring (E n)] →
    [(n : ℕ) → Algebra ℂ (E n)] → (A : Type u_2) → [inst : Ring A] → [Algebra ℂ A] → Type (max u_1 u_2) -/

/- Upstream audit output: @CycleTraceTower.mk : {E : ℕ → Type u_1} →
  [inst : (n : ℕ) → Ring (E n)] →
    [inst_1 : (n : ℕ) → Algebra ℂ (E n)] →
      {A : Type u_2} →
        [inst_2 : Ring A] →
          [inst_3 : Algebra ℂ A] →
            (traceA : A →ₗ[ℂ] ℂ) →
              (trace : (n : ℕ) → E n →ₗ[ℂ] ℂ) →
                (rep : (n : ℕ) → Equiv.Perm (Fin n) →* E n) →
                  (pow : (n : ℕ) → A → E n) →
                    (∀ (n : ℕ) (π : Equiv.Perm (Fin n)) (g : A),
                        (trace n) ((rep n) π * pow n g) =
                          (Multiset.map (fun c => traceA (g ^ c)) π.cycleType).prod *
                            traceA g ^ (n - π.cycleType.sum)) →
                      CycleTraceTower E A -/

/- Upstream audit output: @CycleTraceTower.factorial_le_finrank : ∀ {E : ℕ → Type u_1} [inst : (n : ℕ) → Ring (E n)]
  [inst_1 : (n : ℕ) → Algebra ℂ (E n)] {A : Type u_2} [inst_2 : Ring A] [inst_3 : Algebra ℂ A] (T : CycleTraceTower E A)
  {g : A}, IsNilpotent g → T.traceA g ≠ 0 → ∀ (n : ℕ) [Module.Finite ℂ (E n)], n.factorial ≤ Module.finrank ℂ (E n) -/

/- Upstream audit output: @CycleTraceTower.traceA_eq_zero_of_finrank_lt_factorial : ∀ {E : ℕ → Type u_1} [inst : (n : ℕ) → Ring (E n)]
  [inst_1 : (n : ℕ) → Algebra ℂ (E n)] {A : Type u_2} [inst_2 : Ring A] [inst_3 : Algebra ℂ A] (T : CycleTraceTower E A)
  {n : ℕ} [Module.Finite ℂ (E n)], Module.finrank ℂ (E n) < n.factorial → ∀ {g : A}, IsNilpotent g → T.traceA g = 0 -/

/- Upstream audit output: @CycleTraceTower.traceA_eq_zero_of_exponential_bound : ∀ {E : ℕ → Type u_1} [inst : (n : ℕ) → Ring (E n)]
  [inst_1 : (n : ℕ) → Algebra ℂ (E n)] {A : Type u_2} [inst_2 : Ring A] [inst_3 : Algebra ℂ A] (T : CycleTraceTower E A)
  [∀ (n : ℕ), Module.Finite ℂ (E n)] (B : ℝ),
  (∀ (n : ℕ), ↑(Module.finrank ℂ (E n)) ≤ B ^ n) → ∀ {g : A}, IsNilpotent g → T.traceA g = 0 -/

/- Upstream audit output: @scalarTrace_eq_zero_of_finrank_lt_factorial : ∀ {A : Type u_2} [inst : CategoryTheory.Category.{u_1, u_2} A]
  [inst_1 : CategoryTheory.MonoidalCategory A] [inst_2 : CategoryTheory.SymmetricCategory A]
  [inst_3 : CategoryTheory.Preadditive A] [inst_4 : CategoryTheory.Linear ℂ A]
  [inst_5 : CategoryTheory.MonoidalPreadditive A] [inst_6 : CategoryTheory.MonoidalLinear ℂ A]
  [inst_7 : CategoryTheory.RigidCategory A] (hu : HasScalarUnit A) (X : A) {n : ℕ}
  [Module.Finite ℂ (CategoryTheory.End (tensorPow A X n))],
  Module.finrank ℂ (CategoryTheory.End (tensorPow A X n)) < n.factorial →
    ∀ {g : CategoryTheory.End X}, IsNilpotent g → (scalarTrace hu X) g = 0 -/

/- Upstream audit output: @scalarTrace_eq_zero_of_isNilpotent_factorial : ∀ {A : Type u_2} [inst : CategoryTheory.Category.{u_1, u_2} A]
  [inst_1 : CategoryTheory.MonoidalCategory A] [inst_2 : CategoryTheory.SymmetricCategory A]
  [inst_3 : CategoryTheory.Preadditive A] [inst_4 : CategoryTheory.Linear ℂ A]
  [inst_5 : CategoryTheory.MonoidalPreadditive A] [inst_6 : CategoryTheory.MonoidalLinear ℂ A]
  [inst_7 : CategoryTheory.RigidCategory A] (hu : HasScalarUnit A) (X : A)
  [∀ (n : ℕ), Module.Finite ℂ (CategoryTheory.End (tensorPow A X n))] (B : ℝ),
  (∀ (n : ℕ), ↑(Module.finrank ℂ (CategoryTheory.End (tensorPow A X n))) ≤ B ^ n) →
    ∀ {g : CategoryTheory.End X}, IsNilpotent g → (scalarTrace hu X) g = 0 -/

/- Upstream audit output: @skeinTrace_eq_zero_of_isNilpotent_factorial : ∀ {R : ℕ} (f : EdgeRankParameter R) (n : ℕ) {g : skeinEnd f n},
  IsNilpotent g → skeinTrace f n g = 0 -/

/- Upstream audit output: @skeinEnd_isSemisimpleRing_factorial : ∀ {R : ℕ} (f : EdgeRankParameter R) (n : ℕ), IsSemisimpleRing (skeinEnd f n) -/

/- Upstream audit output: @karoubiEnd_isSemisimpleRing_factorial : ∀ {R : ℕ} (f : EdgeRankParameter R)
  (X : CategoryTheory.Idempotents.Karoubi (SkeinObj f)), IsSemisimpleRing (CategoryTheory.End X) -/

/- Upstream audit output: @karoubiEnd_isSemisimpleRing : ∀ {R : ℕ} (f : EdgeRankParameter R)
  (X : CategoryTheory.Idempotents.Karoubi (SkeinObj f)), IsSemisimpleRing (CategoryTheory.End X) -/

/- Upstream audit output: @matTrace_eq_zero_of_isNilpotent' : ∀ {R : ℕ} {f : EdgeRankParameter R}
  {M : CategoryTheory.Mat_ (CategoryTheory.Idempotents.Karoubi (SkeinObj f))} {φ : CategoryTheory.End M},
  IsNilpotent φ → (matTrace f M) φ = 0 -/

/- Upstream audit output: @envEnd_isSemisimpleRing : ∀ {R : ℕ} (f : EdgeRankParameter R) (E : Env f), IsSemisimpleRing (CategoryTheory.End E) -/

/- Upstream audit output: @envAbelian : {R : ℕ} → (f : EdgeRankParameter R) → CategoryTheory.Abelian (Env f) -/

/- Upstream audit output: @env_deligneSemisimple : ∀ {R : ℕ} (f : EdgeRankParameter R), IsSemisimple (Env f) -/

/- Upstream audit output: @env_delignePackage : ∀ {R : ℕ} (f : EdgeRankParameter R), DeligneTheoremStatement → Nonempty (DelignePackage (Env f)) -/

/- Upstream audit output: @skein_delignePackage : ∀ {R : ℕ} (f : EdgeRankParameter R),
  DeligneTheoremStatement → Nonempty (DelignePackage (SkeinObj f)) -/

/-! ### Axioms -/

/- Upstream audit output: 'RS.exists_singlePowerTrace_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.linearIndependent_of_group_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.CycleTraceTower.factorial_le_finrank' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.CycleTraceTower.traceA_eq_zero_of_finrank_lt_factorial' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.CycleTraceTower.traceA_eq_zero_of_exponential_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.scalarTrace_eq_zero_of_finrank_lt_factorial' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.scalarTrace_eq_zero_of_isNilpotent_factorial' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.skeinTrace_eq_zero_of_isNilpotent_factorial' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.skeinEnd_isSemisimpleRing_factorial' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.karoubiEnd_isSemisimpleRing_factorial' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.envAbelian' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/-! ### Independence from the appendix and fibre-functor engines -/

/-
Upstream diagnostic traversal, preserved as documentation. The pool performs its
compiled declaration and axiom audits separately; this block declares no proof.

open Lean in
private partial def factorialDependencies (env : Environment) (name : Name) :
    StateT NameSet CoreM Unit := do
  if (← get).contains name then return
  modify (·.insert name)
  let some info := env.checked.get.find? name
    | throwError "Missing declaration in factorial audit: {name}"
  for dependency in info.getUsedConstantsAsSet.toList do
    factorialDependencies env dependency

open Lean in
private def factorialDependencyModule (env : Environment)
    (name : Name) : Option Name := do
  -- Equation lemmas can be generated in the module that first
  -- unfolds a definition. Attribute them to that definition;
  -- their proof bodies are still traversed without exemption.
  let origin := ((Meta.declFromEqLikeName env name).map Prod.fst).getD name
  return (← env.getModuleIdxFor? origin |>.bind
    (env.header.modules[·]?)).module

open Lean in
private def appendixModule (name : Name) : Bool :=
  [ `RS.Novel.Envelope.BlockAssembly,
    `RS.Novel.Envelope.NilpotentTrace,
    `RS.Novel.Envelope.ObjectTower,
    `RS.Novel.Envelope.TraceZeta,
    `RS.Novel.Envelope.TraceZetaSharp,
    `RS.Classical.SymFun.HookVanishing,
    `RS.Classical.SymFun.RecurrenceFromVanishing,
    `RS.Classical.SymFun.RationalityFromRecurrence,
    `RS.Classical.SymFun.ZetaRational,
    `RS.Classical.SymFun.ZetaSeries,
    `RS.Classical.SymFun.ZetaExp ].any (·.isPrefixOf name)

open Lean in
private def factorialExcludedDependency (env : Environment)
    (name : Name) : Bool :=
  let excluded := [
    `RS.Classical.Interfaces.SchurPackage,
    `RS.Classical.Interfaces.DeligneTheorem,
    `RS.Classical.SchurTheory,
    `RS.Classical.SymFun,
    `RS.Novel.Envelope.BlockBounds,
    `RS.Novel.Envelope.HookConfinement,
    `RS.Novel.Envelope.HookConfinementSharp]
  match factorialDependencyModule env name with
  | none => false
  | some source =>
    appendixModule source || excluded.any (·.isPrefixOf source) ||
      (`RS.Classical.Deligne).isPrefixOf source &&
        source != `RS.Classical.Deligne.FactorialBeats

-- Traverse the proof terms themselves; the import graph also
-- contains the appendix route and cannot establish independence.
run_elab do
  let env ← Lean.getEnv
  let roots := [
    ``CycleTraceTower.factorial_le_finrank,
    ``CycleTraceTower.traceA_eq_zero_of_finrank_lt_factorial,
    ``CycleTraceTower.traceA_eq_zero_of_exponential_bound,
    ``scalarTrace_eq_zero_of_finrank_lt_factorial,
    ``scalarTrace_eq_zero_of_isNilpotent_factorial,
    ``skeinTrace_eq_zero_of_isNilpotent_factorial,
    ``skeinEnd_isSemisimpleRing_factorial,
    ``karoubiEnd_isSemisimpleRing_factorial,
    ``envEnd_isSemisimpleRing, ``envAbelian, ``env_deligneSemisimple]
  let (_, dependencies) ←
    (roots.forM (factorialDependencies env)).run {}
  for name in dependencies.toList do
    if factorialExcludedDependency env name then
      throwError "Factorial route depends on excluded declaration: {name}"
  let (_, control) ←
    (factorialDependencies env
      ``scalarTrace_eq_zero_of_isNilpotent).run {}
  for name in [``schurPackage,
      ``powerSums_zero_of_hook_and_eventually_zero] do
    unless control.contains name && factorialExcludedDependency env name do
      throwError "Factorial audit missed an appendix dependency: {name}"

-- The summits use Deligne and colour-bound representation theory,
-- but their nilpotent-trace input must be the factorial argument.
run_elab do
  let env ← Lean.getEnv
  for root in [``regts_sevenster, ``regts_sevenster_quant,
      ``regts_sevenster_total, ``regts_sevenster_minimum,
      ``regts_sevenster_rank_growth, ``regts_sevenster_prescribed,
      ``regts_sevenster_characterisation,
      ``regts_sevenster_quant_characterisation] do
    let (_, dependencies) ← (factorialDependencies env root).run {}
    unless dependencies.contains
        ``skeinTrace_eq_zero_of_isNilpotent_factorial do
      throwError "Summit does not use the factorial trace theorem: {root}"
    for name in dependencies.toList do
      if let some source := factorialDependencyModule env name then
        if appendixModule source then
          throwError "Summit {root} depends on appendix declaration: {name}"

-/

end RS
