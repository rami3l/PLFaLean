module

public import Mathlib.Logic.IsEmpty.Defs
public import Mathlib.Logic.IsEmpty.Basic

@[expose] public section

/--
`Decidable'` is like `Decidable`, but allows arbitrary sorts.
-/
abbrev Decidable' α := IsEmpty α ⊕' α

namespace Decidable'
  def toDecidable : Decidable' α → Decidable (Nonempty α) := by intro
  | .inr a => right; exact ⟨a⟩
  | .inl na => left; simpa only [not_nonempty_iff]
end Decidable'

instance [Repr α] : Repr (Decidable' α) where
  reprPrec da n := match da with
  | .inr a => ".inr " ++ reprPrec a n
  | .inl _ => ".inl _"
