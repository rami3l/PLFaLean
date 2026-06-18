module
public import Mathlib.Logic.IsEmpty.Defs

/--
`is_empty` converts `IsEmpty α` to `α → False`.
-/
syntax "is_empty" : tactic
macro_rules | `(tactic| is_empty) => `(tactic| apply Function.isEmpty (β := False))
