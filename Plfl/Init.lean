module

public import Mathlib.Tactic

@[expose] public section

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
  def toDecidable : Decidable' α → Decidable (Nonempty α) := by intro
  | .inr a => right; exact ⟨a⟩
  | .inl na => left; simpa
end Decidable'

instance [Repr α] : Repr (Decidable' α) where
  reprPrec da n := match da with
  | .inr a => ".inr " ++ reprPrec a n
  | .inl _ => ".inl _"

theorem congr_arg₃
(f : α → β → γ → δ) {x x' : α} {y y' : β} {z z' : γ}
(hx : x = x') (hy : y = y') (hz : z = z')
: f x y z = f x' y' z'
:= by subst hx hy hz; rfl

namespace Vector
  def dropLast (v : Vector α n) : Vector α (n - 1) := v.pop

  theorem get_dropLast (v : Vector α (n + 1)) (i : Fin n)
  -- : v.dropLast[i] = v[i.val]'(by omega)
  : v.dropLast.get i = v.get ⟨i.val, by omega⟩
  := by simp [dropLast, Vector.get, Vector.pop]
end Vector
