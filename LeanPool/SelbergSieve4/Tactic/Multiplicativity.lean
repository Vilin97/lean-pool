/-
Copyright (c) 2026 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk
-/
-- import Aesop
-- import SelbergSieve.Tactic.AesopInit
-- import Mathlib.NumberTheory.ArithmeticFunction

-- namespace Nat.ArithmeticFunction
-- open Finset

-- macro "multiplicativity" : attr =>
--   `(attr|aesop safe apply (rule_sets [$(Lean.mkIdent `IsMultiplicative):ident]))

-- macro (name := multiplicativity) "multiplicativity" c:Aesop.tactic_clause* : tactic =>
-- `(tactic|
--   { aesop $c* (options :=
--   { destructProductsTransparency := .reducible, applyHypsTransparency := .default, introsTransparency? := some .reducible, terminal := false } )
--   (simp_options := { enabled := false})
--   (rule_sets [$(Lean.mkIdent `IsMultiplicative):ident])})

-- macro (name := multiplicativity?) "multiplicativity?" c:Aesop.tactic_clause* : tactic =>
-- `(tactic|
--   { show_term { multiplicativity $c* } })

-- section attributes
-- open IsMultiplicative

-- attribute [multiplicativity] nat_cast int_cast mul
--   IsMultiplicative.pmul IsMultiplicative.pdiv isMultiplicative_zeta isMultiplicative_moebius
--   isMultiplicative_id isMultiplicative_one IsMultiplicative.ppow isMultiplicative_pow
--   isMultiplicative_sigma IsMultiplicative.prodPrimeFactors

-- attribute [multiplicativity] IsMultiplicative.map_one

-- end attributes

-- example : IsMultiplicative (ζ*ζ) := by multiplicativity

-- example {R : Type*} [Field R] (f : ArithmeticFunction R) (hf : IsMultiplicative f) :
--     IsMultiplicative ((ζ:ArithmeticFunction R).pdiv f) := by
--   exact IsMultiplicative.pdiv (IsMultiplicative.nat_cast isMultiplicative_zeta) hf
