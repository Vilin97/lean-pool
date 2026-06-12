/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Foundation.Vorspiel.Vorspiel

/-! # NotationClass -/


namespace LO

/-- Coding objects into syntactic objects (e.g. natural numbers, first-order terms) -/
class GoedelQuote (α β : Sort*) where
  /-- Imported declaration from the Incompleteness formalization. -/
  quote : α → β

/-- Imported declaration from the Incompleteness formalization. -/
notation:max "⌜" x "⌝" => GoedelQuote.quote x

/-- Coding objects into semantic objects (e.g. individuals of a model of a theory) -/
class StarQuote (α β : Sort*) where
  /-- Imported declaration from the Incompleteness formalization. -/
  quote : α → β

/-- Imported declaration from the Incompleteness formalization. -/
prefix:max "✶" => StarQuote.quote

end LO
