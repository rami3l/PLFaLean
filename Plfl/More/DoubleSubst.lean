-- https://plfa.github.io/More/#exercise-double-subst-stretch

-- Adapted from <https://github.com/kaa1el/plfa_solution/blob/c5869a34bc4cac56cf970e0fe38874b62bd2dafc/src/plfa/demo/DoubleSubstitutionDeBruijn.agda>.

import Plfl.More

import Mathlib.Tactic

set_option tactic.simp.trace true

open Term

@[simp]
lemma subst₁_shift : (t' : Γ ⊢ b) ⇴ (rename .s (t : Γ ⊢ a)) = t := by
  simp_all; cases t <;> try trivial
  · case lam n => stop {simp_all; apply congr_arg lam}

theorem double_subst
: subst₂ (v : Γ ⊢ a) (w : Γ ⊢ b) (n : Γ‚ a‚ b ⊢ c)
= v ⇴ rename .s w ⇴ n
:= by
  cases n <;> try trivial
  · case var n =>
    cases n
    · case z =>
      unfold subst₂; change w = _
      conv_rhs => arg 2; unfold subst; simp
      simp_all
    · case s n => simp_all; cases n <;> rfl
  · case lam n =>
    stop {simp_all; apply congr_arg lam}
  · case ap => sorry
  · case succ => sorry
  · case case => sorry
  · case mu => sorry
  · case mulP => sorry
  · case «let» => sorry
  · case prod => sorry
  · case fst => sorry
  · case snd => sorry
  · case left => sorry
  · case right => sorry
  · case caseSum => sorry
  · case caseVoid => sorry
  · case cons => sorry
  · case caseList => sorry
