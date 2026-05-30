module

-- https://plfa.github.io/Properties/

public meta import Plfl.Init
public meta import Plfl.Lambda
import Plfl.Lambda
import Mathlib.Tactic.Basic

@[expose] public section

open Lambda

namespace Properties

open Context Context.IsTy Term.Reduce
open Sum

-- https://plfa.github.io/Properties/#values-do-not-reduce
theorem Value.empty_reduce : Value m → ∀ {n}, IsEmpty (m —→ n) := by
  introv v; is_empty; intro r
  cases v <;> try contradiction
  · case succ v => cases r; · case succξ => apply (empty_reduce v).false; trivial

theorem Reduce.empty_value : m —→ n → IsEmpty (Value m) := by
  intro r; is_empty; intro v
  have : ∀ {n}, IsEmpty (m —→ n) := Value.empty_reduce v
  exact this.false r

-- https://plfa.github.io/Properties/#exercise-canonical--practice
inductive Canonical : Term → Ty → Type where
| canLam : ∅‚ x ⦂ t ⊢ n ⦂ u → Canonical (ƛ x : n) (t =⇒ u)
| canZero : Canonical 𝟘 ℕt
| canSucc : Canonical n ℕt → Canonical (ι n) ℕt

namespace Canonical
  def ofIsTy : ∅ ⊢ m ⦂ t → Value m → Canonical m t
  | tyLam l, Value.lam => canLam l
  | tyZero, V𝟘 => canZero
  | tySucc t, Value.succ m => canSucc <| ofIsTy t m

  def wellTyped : Canonical v t → ∅ ⊢ v ⦂ t × Value v
  | canLam h => ⟨tyLam h, Value.lam⟩
  | canZero => ⟨tyZero, Value.zero⟩
  | canSucc h => ⟨tySucc (wellTyped h).1, Value.succ (wellTyped h).2⟩

  def wellTypedInv : ∅ ⊢ v ⦂ t × Value v → Canonical v t
  | ⟨tyLam ty, Value.lam⟩ => canLam ty
  | ⟨tyZero, Value.zero⟩ => canZero
  | ⟨tySucc ty, Value.succ v⟩ => canSucc (wellTypedInv ⟨ty, v⟩)

  lemma wellTyped_left_inv (c : Canonical v t)
  : wellTypedInv (wellTyped c) = c
  := by
    induction c with
    | canLam h => rfl
    | canZero => rfl
    | canSucc c' ih =>
        unfold wellTyped
        generalize h_eq : wellTyped c' = pair
        cases pair with
        | mk ty v =>
          change canSucc (wellTypedInv ⟨ty, v⟩) = canSucc c'
          rw [h_eq] at ih
          rw [ih]

  lemma wellTyped_right_inv (c : ∅ ⊢ v ⦂ t × Value v)
  : wellTyped (wellTypedInv c) = c
  := by
    match c with
    | ⟨tyLam ty, Value.lam⟩ => obtain ⟨fst, snd⟩ := c; rfl
    | ⟨tyZero, Value.zero⟩ => obtain ⟨fst, snd⟩ := c; rfl
    | ⟨tySucc ty, Value.succ n⟩ =>
        rename_i v'; have := @wellTyped_right_inv v' ℕt ⟨ty, n⟩;
        rw [wellTypedInv, wellTyped];
        · simp_all only

  /--
  The Canonical forms are exactly the well-typed values.
  -/
  instance : Canonical v t ≃ (∅ ⊢ v ⦂ t) × Value v where
    toFun := wellTyped
    invFun := wellTypedInv
    left_inv := wellTyped_left_inv
    right_inv := wellTyped_right_inv
end Canonical

def canonical : ∅ ⊢ m ⦂ t → Value m → Canonical m t := Canonical.ofIsTy

-- https://plfa.github.io/Properties/#progress
/--
If a term `m` is not ill-typed, then it either is a value or can be reduced.
-/
inductive Progress (m : Term) where
| step : (m —→ n) → Progress m
| done : Value m → Progress m
--^ In general, the rule of thumb is to consider the easy case (`step`) before the hard case (`done`) for easier proofs.

namespace Progress
  def ofIsTy : ∅ ⊢ m ⦂ t → Progress m := by
    intro
    | tyVar _ => contradiction
    | tyLam _ => exact done Value.lam
    | tyAp jl jm => cases ofIsTy jl with
      | step => apply step; · apply apξ₁; trivial
      | done vl => cases ofIsTy jm with
        | step => apply step; apply apξ₂ <;> trivial
        | done => cases vl with
          | lam => apply step; apply lamβ; trivial
          | _ => contradiction
    | tyZero => exact done V𝟘
    | tySucc j => cases ofIsTy j with
      | step => apply step; apply succξ; trivial
      | done => apply done; apply Value.succ; trivial
    | tyCase jl jm jn => cases ofIsTy jl with
      | step => apply step; apply caseξ; trivial
      | done vl => cases vl with
        | lam => trivial
        | zero => exact step zeroβ
        | succ => apply step; apply succβ; trivial
    | tyMu _ => exact step muβ
end Progress

def progress : ∅ ⊢ m ⦂ t → Progress m := Progress.ofIsTy

-- https://plfa.github.io/Properties/#exercise-value-practice
def IsTy.isValue : ∅ ⊢ m ⦂ t → Decidable (Nonempty (Value m)) := by
  intro j; cases progress j
  · rename_i n r; have := Reduce.empty_value r
    apply isFalse; simp_all only [not_nonempty_iff]
  · exact isTrue ⟨by trivial⟩

def Progress' (m : Term) : Type := Value m ⊕ Σ n, m —→ n

namespace Progress'
  -- https://plfa.github.io/Properties/#exercise-progress-practice
  def ofIsTy : ∅ ⊢ m ⦂ t → Progress' m := by
    intro
    | tyVar _ => contradiction
    | tyLam _ => exact inl Value.lam
    | tyAp jl jm => match ofIsTy jl with
      | inr ⟨n, r⟩ => exact inr ⟨_, apξ₁ r⟩
      | inl vl => match ofIsTy jm with
        | inr ⟨n, r⟩ => apply inr; exact ⟨_, apξ₂ vl r⟩
        | inl _ => cases canonical jl vl with
          | canLam => apply inr; refine ⟨_, lamβ ?_⟩; trivial
    | tyZero => exact inl V𝟘
    | tySucc j => match ofIsTy j with
      | inl v => apply inl; exact Value.succ v
      | inr ⟨n, r⟩ => exact inr ⟨_, succξ r⟩
    | tyCase jl jm jn => match ofIsTy jl with
      | inr ⟨n, r⟩ => exact inr ⟨_, caseξ r⟩
      | inl vl => cases vl with
        | lam => trivial
        | zero => exact inr ⟨_, zeroβ⟩
        | succ v => exact inr ⟨_, succβ v⟩
    | tyMu _ => exact inr ⟨_, muβ⟩
end Progress'

namespace Progress
  -- https://plfa.github.io/Properties/#exercise-progress--practice
  @[simp] def toProgress' : Progress m → Progress' m | step r => inr ⟨_, r⟩ | done v => inl v
  @[simp] def fromProgress' : Progress' m → Progress m | inl v => done v | inr ⟨_, r⟩ => step r

  instance : Progress m ≃ Progress' m where
    toFun := toProgress'
    invFun := fromProgress'
    left_inv := by intro x; cases x <;> simp_all only [fromProgress', toProgress']
    right_inv := by intro x; cases x <;> simp_all only [toProgress', fromProgress']
end Progress

-- https://plfa.github.io/Properties/#renaming
namespace Renaming
  open Lookup

  /--
  If one context maps to another, the mapping holds after adding the same variable to both contexts.
  -/
  def ext
  : (∀ {x tx}, Γ ∋ x ⦂ tx → Δ ∋ x ⦂ tx)
  → (∀ {x y tx ty}, Γ‚ y ⦂ ty ∋ x ⦂ tx → Δ‚ y ⦂ ty ∋ x ⦂ tx)
  := by
    introv ρ; intro
    | z => exact z
    | s nxy lx => exact s nxy <| ρ lx

  def rename
  : (∀ {x t}, Γ ∋ x ⦂ t → Δ ∋ x ⦂ t)
  → (∀ {m t}, Γ ⊢ m ⦂ t → Δ ⊢ m ⦂ t)
  := by
    introv ρ; intro
    | tyVar j => apply tyVar; exact ρ j
    | tyLam j => apply tyLam; exact rename (ext ρ) j
    | tyAp jl jm =>
        apply tyAp
        · exact rename ρ jl
        · exact rename ρ jm
    | tyZero => apply tyZero
    | tySucc j => apply tySucc; exact rename ρ j
    | tyCase jl jm jn =>
        apply tyCase
        · exact rename ρ jl
        · exact rename ρ jm
        · exact rename (ext ρ) jn
    | tyMu j => apply tyMu; exact rename (ext ρ) j

  def Lookup.weaken : ∅ ∋ m ⦂ t → Γ ∋ m ⦂ t := by
    nofun

  def weaken : ∅ ⊢ m ⦂ t → Γ ⊢ m ⦂ t := by
    intro j; refine rename ?_ j; exact Lookup.weaken

  def drop
  : Γ‚ x ⦂ t'‚ x ⦂ t ⊢ y ⦂ u
  → Γ‚ x ⦂ t ⊢ y ⦂ u
  := by
    intro j; refine rename ?_ j
    intro y u j; cases j
    · exact z
    · case s j =>
      cases j
      · contradiction
      · case s j => refine s ?_ j; trivial

  def Lookup.swap
  : (x ≠ x') → (Γ‚ x' ⦂ t'‚ x ⦂ t ∋ y ⦂ u)
  → (Γ‚ x ⦂ t‚ x' ⦂ t' ∋ y ⦂ u)
  := by
    intro n j; cases j
    · exact s n z
    · case s j =>
      cases j
      · exact z
      · apply s
        · trivial
        · apply s <;> trivial

  def swap
  : x ≠ x' → Γ‚ x' ⦂ t'‚ x ⦂ t ⊢ y ⦂ u
  → Γ‚ x ⦂ t‚ x' ⦂ t' ⊢ y ⦂ u
  := by
    intro n j; refine rename ?_ j; introv; exact Lookup.swap n
end Renaming

-- https://plfa.github.io/Properties/#substitution
def subst
: ∅ ⊢ y ⦂ t → Γ‚ x ⦂ t ⊢ n ⦂ u
→ Γ ⊢ n[x := y] ⦂ u
:= open Renaming in by
  intro j; intro
  | tyVar k =>
    rename_i y; by_cases y = x <;> simp_all only [Term.subst, ite_true]
    · have := weaken (Γ := Γ) j; cases k <;> try trivial
    · cases k <;> simp_all only [not_true]; · repeat trivial
  | tyLam k =>
    rename_i y _ _ _; by_cases h : y = x <;> (
      simp_all only [Term.subst, ite_true]; apply tyLam
    )
    · subst h; apply drop; trivial
    · apply subst j; exact swap (by trivial) k
  | tyAp k l => apply tyAp <;> (apply subst j; trivial)
  | tyZero => exact tyZero
  | tySucc _ => apply tySucc; apply subst j; trivial
  | tyCase k l m =>
    rename_i y _; by_cases h : y = x <;> simp_all only [Term.subst, ite_true]
    · apply tyCase
      · apply subst j; exact k
      · apply subst j; exact l
      · subst h; exact drop m
    · apply tyCase <;> (apply subst j; try trivial)
      · exact swap (by trivial) m
  | tyMu k =>
    rename_i y _; by_cases h : y = x <;> simp_all only [Term.subst, ite_true]
    · subst h; apply tyMu; exact drop k
    · apply tyMu; apply subst j; exact swap (by trivial) k

-- https://plfa.github.io/Properties/#preservation
def preserve : ∅ ⊢ m ⦂ t → (m —→ n) → ∅ ⊢ n ⦂ t := by
  intro
  | tyAp jl jm, lamβ _ => apply subst jm; cases jl; · trivial
  | tyAp jl jm, apξ₁ _ =>
    apply tyAp <;> try trivial
    · apply preserve jl; trivial
  | tyAp jl jm, apξ₂ _ _ =>
    apply tyAp <;> try trivial
    · apply preserve jm; trivial
  | tySucc j, succξ r => apply tySucc; exact preserve j r
  | tyCase k l m, zeroβ => trivial
  | tyCase k l m, succβ _ => refine subst ?_ m; cases k; · trivial
  | tyCase k l m, caseξ _ =>
      apply tyCase <;> try trivial
      · apply preserve k; trivial
  | tyMu j, muβ => refine subst ?_ j; apply tyMu; trivial

-- https://plfa.github.io/Properties/#evaluation
inductive Result n where
| done (val : Value n)
| dnf
deriving BEq, DecidableEq, Repr

inductive Steps (l : Term) where
| steps : ∀{n : Term}, (l —↠ n) → Result n → Steps l
deriving Repr

open Result Steps

def eval (gas : ℕ) (j : ∅ ⊢ l ⦂ t) : Steps l := open Clos in
  if gas = 0 then
    ⟨nil, dnf⟩
  else
    match progress j with
    | Progress.done v => steps nil <| done v
    | Progress.step r =>
      let ⟨rs, res⟩ := eval (gas - 1) (preserve j r)
      ⟨cons r rs, res⟩

section examples
  open Term

  -- def x : ℕ := x + 1
  abbrev succμ := μ "x" : ι ‵"x"

  abbrev tySuccμ : ∅ ⊢ succμ ⦂ ℕt := by
    apply tyMu; apply tySucc; trivial

  /--
  info: Properties.Result.dnf
  -/
  #guard_msgs in #eval eval 3 tySuccμ |>.3

  abbrev add_2_2 := add □ 2 □ 2

  abbrev two_ty : ∅ ⊢ 2 ⦂ ℕt := by
    iterate 2 (apply tySucc)
    · exact tyZero

  abbrev tyAdd_2_2 : ∅ ⊢ add_2_2 ⦂ ℕt := by
    apply tyAp
    · apply tyAp
      · exact addTy
      · iterate 2 (apply tySucc)
        · exact tyZero
    · iterate 2 (apply tySucc)
      · exact tyZero

  /--
  info: Properties.Result.done
  (Lambda.Value.succ (Lambda.Value.succ (Lambda.Value.succ (Lambda.Value.succ (Lambda.Value.zero)))))
  -/
  #guard_msgs in #eval eval 100 tyAdd_2_2 |>.3
end examples

section subject_expansion
  open Term

  -- https://plfa.github.io/Properties/#exercise-subject_expansion-practice
  example : IsEmpty (∀ {n t m}, ∅ ⊢ n ⦂ t → (m —→ n) → ∅ ⊢ m ⦂ t) := by
    by_contra f
    simp_all only [isEmpty_pi, not_exists, not_isEmpty_iff]
    let illCase := 𝟘? 𝟘 [zero: 𝟘 |succ "x" : add]
    have nty_ill : ∅ ⊬ illCase := by
      intro t
      refine ⟨fun j => ?_⟩
      simp only [illCase] at j
      cases j; rename_i jz js
      cases jz
      cases js; rename_i js'
      cases js'
    have := f 𝟘 ℕt illCase tyZero zeroβ
    exact nty_ill.false this.some

example : IsEmpty (∀ {n t m}, ∅ ⊢ n ⦂ t → (m —→ n) → ∅ ⊢ m ⦂ t) := by
    by_contra f
    simp_all only [isEmpty_pi, not_exists, not_isEmpty_iff]
    let illAp := (ƛ "x" : 𝟘) □ illLam
    have nty_ill : ∅ ⊬ illAp := by
      intro tt
      refine ⟨fun j => ?_⟩
      simp only [illAp] at j
      cases j; rename_i jl jr
      exact nty_illLam.false jl  -- Use jl instead of jr
    have h_red : illAp —→ 𝟘 := by
      simp only [illAp]
      apply lamβ
      exact Value.lam
    have := f 𝟘 ℕt illAp tyZero h_red  -- Pass arguments explicitly
    exact nty_ill.false this.some
end subject_expansion

-- https://plfa.github.io/Properties/#well-typed-terms-dont-get-stuck
abbrev Normal m := ∀ {n}, IsEmpty (m —→ n)
abbrev Stuck m := Normal m ∧ IsEmpty (Value m)

example : Stuck (‵"x") := by
  unfold Stuck Normal; constructor
  · intro n; is_empty; nofun
  · is_empty; nofun

-- https://plfa.github.io/Properties/#exercise-unstuck-recommended
/--
No well-typed term can be stuck.
-/
theorem unstuck : ∅ ⊢ m ⦂ t → IsEmpty (Stuck m) := by
  intro j; is_empty; simp_all only [and_imp]
  intro n ns; cases progress j
  · case step s => exact n.false s
  · case done v => exact ns.false v

/--
After any number of steps, a well-typed term remains well typed.
-/
def preserves : ∅ ⊢ m ⦂ t → (m —↠ n) → ∅ ⊢ n ⦂ t := by
  intro j; intro
  | Clos.nil => trivial
  | Clos.cons car cdr => refine preserves ?_ cdr; exact preserve j car

/--
_Well-typed terms don't get stuck_ (WTTDGS):
starting from a well-typed term, taking any number of reduction steps leads to a term that is not stuck.
-/
theorem preserves_unstuck : ∅ ⊢ m ⦂ t → (m —↠ n) → IsEmpty (Stuck n) := by
  intro j r; have := preserves j r; exact unstuck this

-- https://plfa.github.io/Properties/#reduction-is-deterministic
def Reduce.det : (m —→ n) → (m —→ n') → n = n' := by
  intro r r'; cases r
  · case lamβ =>
    cases r' <;> try trivial
    · case apξ₂ => exfalso; rename_i v _ _ r; exact (Value.empty_reduce v).false r
  · case apξ₁ =>
    cases r' <;> try trivial
    · case apξ₁ => simp only [Term.ap.injEq, and_true]; apply det <;> trivial
    · case apξ₂ => exfalso; rename_i r _ v _; exact (Value.empty_reduce v).false r
  · case apξ₂ =>
    cases r' <;> try trivial
    · case lamβ => exfalso; rename_i r _ _ _ v; exact (Value.empty_reduce v).false r
    · case apξ₁ => exfalso; rename_i v _ _ r; exact (Value.empty_reduce v).false r
    · case apξ₂ => simp only [Term.ap.injEq, true_and]; apply det <;> trivial
  · case zeroβ => cases r' <;> try trivial
  · case succβ =>
    cases r' <;> try trivial
    · case caseξ => exfalso; rename_i v _ r; exact (Value.empty_reduce (Value.succ v)).false r
  · case succξ => cases r'; · case succξ => simp only [Term.succ.injEq]; apply det <;> trivial
  · case caseξ =>
    cases r' <;> try trivial
    · case succβ => exfalso; rename_i v r; exact (Value.empty_reduce (Value.succ v)).false r
    · case caseξ => simp only [Term.case.injEq, and_self, and_true]; apply det <;> trivial
  · case muβ => cases r'; try trivial

-- https://plfa.github.io/Properties/#quiz
/-
Suppose we add a new term zap with the following reduction rule

-------- β-zap
M —→ zap
and the following typing rule:

----------- ⊢zap
Γ ⊢ zap ⦂ A
Which of the following properties remain true in the presence of these rules? For each property, write either "remains true" or "becomes false." If a property becomes false, give a counterexample:

* Determinism

Becomes false.
The term `(ƛ x ⇒ `"x") □ 𝟘` can both be reduced via:
· apξ₁, to zap □ 𝟘
· zepβ, to zap
... and they're not equal.

* Progress/Preservation

Remains true.
-/


-- https://plfa.github.io/Properties/#quiz-1
/-
Suppose instead that we add a new term foo with the following reduction rules:

------------------ β-foo₁
(λ x ⇒ ` x) —→ foo

----------- β-foo₂
foo —→ zero
Which of the following properties remain true in the presence of this rule? For each one, write either "remains true" or else "becomes false." If a property becomes false, give a counterexample:

* Determinism

Becomes false.

The term `(ƛ x ⇒ `"x") □ 𝟘` can both be reduced via:
· apξ₁, to foo □ 𝟘
· lamβ, to `"x"
... and they're not equal.

* Progress

Becomes false.
The term `(ƛ x ⇒ `"x") □ 𝟘` can be reduced via:
· apξ₁ fooβ₁, to foo □ 𝟘
· then apξ₁ fooβ₂, to 𝟘 □ 𝟘
... and now the term get's stuck.

* Preservation

Becomes false.
The term `(ƛ x ⇒ `"x") ⦂ ℕt =⇒ ℕt` can be reduced via:
· fooβ₁, to foo
· then fooβ₂, 𝟘 ⦂ ℕt
... and (ℕt =⇒ ℕt) ≠ ℕt

-/

-- https://plfa.github.io/Properties/#quiz-2
/-
Suppose instead that we remove the rule ξ·₁ from the step relation. Which of the following properties remain true in the absence of this rule? For each one, write either "remains true" or else "becomes false." If a property becomes false, give a counterexample:

* Determinism/Preservation

Remains true.

* Progress

Becomes false.
The term `(ƛ x ⇒ `"x") □ 𝟘` is well-typed but gets stucked.
-/

-- https://plfa.github.io/Properties/#quiz-3
/-
We can enumerate all the computable function from naturals to naturals, by writing out all programs of type `ℕ ⇒ `ℕ in lexical order. Write fᵢ for the i’th function in this list.

NB: A ℕ → ℕ function can be seen as a stream of ℕ's, where the i'th ℕ stands for f(i).

Say we add a typing rule that applies the above enumeration to interpret a natural as a function from naturals to naturals:

Γ ⊢ L ⦂ `ℕ
Γ ⊢ M ⦂ `ℕ
-------------- _·ℕ_
Γ ⊢ L · M ⦂ `ℕ
And that we add the corresponding reduction rule:

fᵢ(m) —→ n
---------- δ
i · m —→ n
Which of the following properties remain true in the presence of these rules? For each one, write either "remains true" or else "becomes false." If a property becomes false, give a counterexample:

* Determinism/Preservation

Remains true.
The only change is that the terms that were once stuck now might continue to progress.

* Progress

Becomes false.
Since a computable function can be partial, the reduction might not halt.
<https://en.wikipedia.org/wiki/Computable_function>

Are all properties preserved in this case? Are there any other alterations we would wish to make to the system?
-/
