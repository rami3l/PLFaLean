module

-- https://plfa.github.io/ContextualEquivalence/

public import Plfl.Untyped.Denotational.Adequacy

@[expose] public section

namespace ContextualEquivalence

open Untyped Untyped.Notation
open Adequacy
open BigStep BigStep.Notation
open Compositional
open Denotational
open Soundness (soundness)

-- https://plfa.github.io/ContextualEquivalence/#contextual-equivalence
abbrev Terminates (m : Γ ⊢ ✶) : Prop := ∃ n, m —↠ ƛ n

/--
Two terms are contextually equivalent
if plugging them into the same holed program always produces two programs
that either terminate or diverge together.
-/
abbrev ContextualEquiv (m n : Γ ⊢ ✶) : Prop :=
  ∀ {c : Holed Γ ∅}, Terminates (c.plug m) = Terminates (c.plug n)

namespace Notation
  scoped infixl:25 "≃ₕ" => ContextualEquiv
end Notation

open Notation

-- https://plfa.github.io/ContextualEquivalence/#denotational-equivalence-implies-contextual-equivalence
lemma Terminates.of_eq_ℰ {m n : Γ ⊢ ✶} {c : Holed Γ ∅} (he : ℰ m = ℰ n) :
Terminates (c.plug m) → Terminates (c.plug n)
:= by
  intro ⟨n', rs⟩; apply Eval.reduce_iff_cbn.mpr; apply Eval.to_big_step
  calc ℰ (c.plug n)
    _ = ℰ (c.plug m) := compositionality he |>.symm
    _ = ℰ (ƛ n') := soundness rs

theorem ContextualEquiv.of_eq_ℰ {m n : Γ ⊢ ✶} (he : ℰ m = ℰ n) : m ≃ₕ n := by
  intro c; simp only [eq_iff_iff]; constructor
  · exact Terminates.of_eq_ℰ he
  · exact Terminates.of_eq_ℰ he.symm
