import Mathlib.Logic.IsEmpty

/--
`is_empty` converts `IsEmpty α` to `α → False`.
-/
syntax "is_empty" : tactic
macro_rules | `(tactic| is_empty) => `(tactic| apply Function.isEmpty (β := False))

/--
`Decidable'` is like `Decidable`, but allows arbitrary sorts.
-/
abbrev Decidable' α := IsEmpty α ⊕' α

namespace Decidable'
  def toDecidable : Decidable' α → Decidable (Nonempty α) := by
    intro
    | .inr a => right; exact ⟨a⟩
    | .inl na => left; simpa
end Decidable'

instance [Repr α] : Repr (Decidable' α) where
  reprPrec da n := match da with
  | .inr a => ".inr " ++ reprPrec a n
  | .inl _ => ".inl _"

/--
`Iff'` is like `Iff`, but allows arbitrary sorts.
-/
abbrev Iff' a b := a → b × b → a

infix:20 " ↔'" => Iff'

theorem congr_arg₃
(f : α → β → γ → δ) {x x' : α} {y y' : β} {z z' : γ}
(hx : x = x') (hy : y = y') (hz : z = z')
: f x y z = f x' y' z'
:= by subst hx hy hz; rfl
