-- https://plfa.github.io/Denotational/

import Plfl.Init
import Plfl.Untyped
import Plfl.Untyped.Substitution

import Mathlib.Data.Vector.Basic
import Mathlib.Tactic

namespace Denotational

-- https://plfa.github.io/Denotational/#values
inductive Value : Type where
/-- No information is provided about the computation. -/
| bot : Value
/-- A single input-output mapping, from the first term to the second. -/
| fn : Value → Value → Value
/-- A function that maps inputs to outputs according to both terms. -/
| conj : Value → Value → Value
deriving BEq, DecidableEq, Repr

namespace Notation
  instance : Bot Value where bot := .bot
  instance : Sup Value where sup := .conj

  scoped infixr:70 " ⇾ " => Value.fn
end Notation

open Notation

/-- `Sub` adapts the familiar notion of subset to the `Value` type. -/
inductive Sub : Value → Value → Type where
| bot : Sub ⊥ v
| conjL : Sub v u → Sub w u → Sub (v ⊔ w) u
| conjR₁ : Sub u v → Sub u (v ⊔ w)
| conjR₂ : Sub u w → Sub u (v ⊔ w)
| trans : Sub u v → Sub v w → Sub u w
| fn : Sub v' v → Sub w w' → Sub (v ⇾ w) (v' ⇾ w')
| dist : Sub (v ⇾ (w ⊔ w')) ((v ⇾ w) ⊔ (v ⇾ w'))

namespace Notation
  scoped infix:40 " ⊑ " => Sub
end Notation

instance : Trans Sub Sub Sub where trans := .trans

@[refl]
def Sub.refl : v ⊑ v := match v with
| ⊥ => .bot
| _ ⇾ _ => .fn refl refl
| .conj _ _ => .conjL (.conjR₁ refl) (.conjR₂ refl)

/-- The `⊔` operation is monotonic with respect to `⊑`. -/
def sub_sub (d₁ : v ⊑ v') (d₂ : w ⊑ w') : v ⊔ w ⊑ v' ⊔ w' :=
  .conjL (.conjR₁ d₁) (.conjR₂ d₂)

def conj_fn_conj : (v ⊔ v') ⇾ (w ⊔ w') ⊑ (v ⇾ w) ⊔ (v' ⇾ w') := calc
  _ ⊑ ((v ⊔ v') ⇾ w) ⊔ ((v ⊔ v') ⇾ w') := .dist
  _ ⊑ (v ⇾ w) ⊔ (v' ⇾ w') := open Sub in by
    apply sub_sub <;> refine .fn ?_ .refl
    · apply conjR₁; rfl
    · apply conjR₂; rfl

def conj_sub₁ : u ⊔ v ⊑ w → u ⊑ w := by intro
| .conjL h _ => exact h
| .conjR₁ h => refine .conjR₁ ?_; exact conj_sub₁ h
| .conjR₂ h => refine .conjR₂ ?_; exact conj_sub₁ h
| .trans h h' => refine .trans ?_ h'; exact conj_sub₁ h

def conj_sub₂ : u ⊔ v ⊑ w → v ⊑ w := by intro
| .conjL _ h => exact h
| .conjR₁ h => refine .conjR₁ ?_; exact conj_sub₂ h
| .conjR₂ h => refine .conjR₂ ?_; exact conj_sub₂ h
| .trans h h' => refine .trans ?_ h'; exact conj_sub₂ h

open Untyped (Context)
open Untyped.Notation

-- https://plfa.github.io/Denotational/#environments
/--
An `Env` gives meaning to a term's free vars by mapping vars to values.
-/
abbrev Env (Γ : Context) : Type := ∀ (_ : Γ ∋ ✶), Value

namespace Env
  instance : EmptyCollection (Env ∅) where emptyCollection := by intro.

  abbrev snoc (γ : Env Γ) (v : Value) : Env (Γ‚ ✶)
  | .z => v
  | .s i => γ i
end Env

namespace Notation
  scoped notation "`∅" => (∅ : Env ∅)

  -- `‚` is not a comma! See: <https://www.compart.com/en/unicode/U+201A>
  scoped infixl:50 "`‚ " => Env.snoc
end Notation

namespace Env
  -- * I could have used Lisp jargons `cdr` and `car` here,
  -- * instead of the Haskell ones below...
  abbrev init (γ : Env (Γ‚ ✶)) : Env Γ := (γ ·.s)
  abbrev last (γ : Env (Γ‚ ✶)) : Value := γ .z

  theorem init_last (γ : Env (Γ‚ ✶)) : γ = (γ.init`‚ γ.last) := by
    ext x; cases x <;> rfl

  /-- We extend the `⊑` relation point-wise to `Env`s. -/
  abbrev Sub (γ δ : Env Γ) : Type := ∀ (x : Γ ∋ ✶), γ x ⊑ δ x
  abbrev conj (γ δ : Env Γ) : Env Γ | x => γ x ⊔ δ x
end Env

namespace Notation
  instance : Bot (Env Γ) where bot _ := ⊥
  instance : Sup (Env γ) where sup := Env.conj

  scoped infix:40 " `⊑ " => Env.Sub
end Notation

namespace Env.Sub
  @[refl] def refl : γ `⊑ γ | _ => .refl
  @[simp] def conjR₁ (γ δ : Env Γ) : γ `⊑ (γ ⊔ δ) | _ => .conjR₁ .refl
  @[simp] def conjR₂ (γ δ : Env Γ) : δ `⊑ (γ ⊔ δ) | _ => .conjR₂ .refl

  def ext_le (lt : v ⊑ v') : (γ`‚ v) `⊑ (γ`‚ v')
  | .z => lt
  | .s _ => .refl
end Env.Sub

-- https://plfa.github.io/Denotational/#denotational-semantics
/--
`Eval γ m v` means that evaluating the term `m` in the environment `γ` gives `v`.
-/
inductive Eval : Env Γ → (Γ ⊢ ✶) → Value → Prop where
| var : Eval γ (` i) (γ i)
| ap : Eval γ l (v ⇾ w) → Eval γ m v → Eval γ (l □ m) w
| fn : Eval (γ`‚ v) n w → Eval γ (ƛ n) (v ⇾ w)
| bot : Eval γ m ⊥
| conj : Eval γ m v → Eval γ m w → Eval γ m (v ⊔ w)
| sub : Eval γ m v → w ⊑ v → Eval γ m w

namespace Notation
  scoped notation:30 γ " ⊢ " m " ⇓ " v:51 => Eval γ m v
end Notation

/--
Relaxation of table lookup in application,
allowing an argument to match an input entry if the latter is less than the former.
-/
def Eval.ap_sub (d₁ : γ ⊢ l ⇓ v₁ ⇾ w) (d₂ : γ ⊢ m ⇓ v₂) (lt : v₁ ⊑ v₂) : γ ⊢ l □ m ⇓ w
:= d₁.ap <| d₂.sub lt

namespace Example
  open Untyped.Term (id delta omega twoC addC)
  open Eval

  -- `id` can be seen as a mapping table for both `⊥ ⇾ ⊥` and `(⊥ ⇾ ⊥) ⇾ (⊥ ⇾ ⊥)`.
  def denot_id₁ : γ ⊢ id ⇓ ⊥ ⇾ ⊥ := .fn .var
  def denot_id₂ : γ ⊢ id ⇓ (⊥ ⇾ ⊥) ⇾ (⊥ ⇾ ⊥) := .fn .var

  -- `id` also produces a table containing both of the previous tables.
  def denot_id₃ : γ ⊢ id ⇓ (⊥ ⇾ ⊥) ⊔ ((⊥ ⇾ ⊥) ⇾ (⊥ ⇾ ⊥)) := denot_id₁.conj denot_id₂

  -- Oops, self application!
  def denot_id_ap_id : `∅ ⊢ id □ id ⇓ v ⇾ v := .ap (.fn .var) (.fn .var)

  -- In `def twoC f u := f (f u)`,
  -- `f`'s table must include two entries, both `u ⇾ v` and `v ⇾ w`.
  -- `twoC` then merges those two entries into one: `u ⇾ w`.
  def denot_twoC : `∅ ⊢ twoC ⇓ (u ⇾ v ⊔ v ⇾ w) ⇾ u ⇾ w := by
    apply fn; apply fn; apply ap
    · apply sub .var; exact .conjR₂ .refl
    · apply ap
      · apply sub .var; exact .conjR₁ .refl
      · exact .var

  def denot_delta : `∅ ⊢ delta ⇓ (v ⇾ w ⊔ v) ⇾ w := by
    apply fn; apply ap (v := v) <;> apply sub .var
    · exact .conjR₁ .refl
    · exact .conjR₂ .refl

  example : `∅ ⊢ omega ⇓ ⊥ := by
    apply ap denot_delta; apply conj
    · exact fn (v := ⊥) .bot
    · exact .bot

  def denot_omega : `∅ ⊢ omega ⇓ ⊥ := .bot

  -- https://plfa.github.io/Denotational/#exercise-denot-plus%E1%B6%9C-practice

  -- For `def addC m n u v := (m u) (n u v)` we have the following mapping table:
  -- · n u v = w
  -- · m u w = x

  def denot_addC
  : let m := u ⇾ w ⇾ x
    let n := u ⇾ v ⇾ w
    `∅ ⊢ addC ⇓ m ⇾ n ⇾ u ⇾ v ⇾ x
  := by apply_rules [fn, ap, var]
end Example

-- https://plfa.github.io/Denotational/#denotations-and-denotational-equality
/--
A denotational semantics can be seen as a function from a term
to some relation between `Env`s and `Value`s.
-/
abbrev Denot (Γ : Context) : Type := Env Γ → Value → Prop

def ℰ (m : Γ ⊢ ✶) : Denot Γ | γ, v => γ ⊢ m ⇓ v

-- Denotational Equality

-- Nothing to do thanks to proof irrelevance.
-- Instead of defining a new `≃` operator to denote the equivalence of `Denot`s,
-- the regular `=` should be enough in our case.

section
  open Untyped.Subst
  open Substitution
  open Eval

  -- https://plfa.github.io/Denotational/#renaming-preserves-denotations

  variable {γ : Env Γ} {δ : Env Δ}

  def ext_sub (ρ : Rename Γ Δ) (lt : γ `⊑ δ ∘ ρ)
  : (γ`‚ v) `⊑ (δ`‚ v) ∘ ext ρ
  | .z => .refl
  | .s i => lt i

  /-- The result of evaluation is conserved after renaming. -/
  def rename_pres (ρ : Rename Γ Δ) (lt : γ `⊑ δ ∘ ρ) (d : γ ⊢ m ⇓ v)
  : δ ⊢ rename ρ m ⇓ v
  := by induction d generalizing Δ with
  | var => apply sub .var; apply lt
  | ap _ _ r r' => exact .ap (r ρ lt) (r' ρ lt)
  | fn _ r => apply fn; rename_i v _ _ _; exact r (ext ρ) (ext_sub ρ lt)
  | bot => exact .bot
  | conj _ _ r r' => exact .conj (r ρ lt) (r' ρ lt)
  | sub _ lt' r => exact (r ρ lt).sub lt'

  -- https://plfa.github.io/Denotational/#environment-strengthening-and-identity-renaming

  variable {γ δ : Env Γ}

  /-- The result of evaluation is conserved under a superset. -/
  def sub_env (d : γ ⊢ m ⇓ v) (lt : γ `⊑ δ) : δ ⊢ m ⇓ v := by
    convert rename_pres id lt d; exact rename_id.symm

  lemma up_env (d : (γ`‚ u₁) ⊢ m ⇓ v) (lt : u₁ ⊑ u₂) : (γ`‚ u₂) ⊢ m ⇓ v := by
    apply sub_env d; exact Env.Sub.ext_le lt
end

-- https://plfa.github.io/Denotational/#exercise-denot-church-recommended
/--
A path consists of `n` edges (`⇾`s) and `n + 1` vertices (`Value`s).
-/
def Value.path : (n : ℕ) → Vector Value (n + 1) → Value
| 0, _ => ⊥
| i + 1, vs => by
  refine path i ?_ ⊔ vs[i] ⇾ vs[i + 1]
  convert vs.take (i + 1) using 1; simp_arith

/--
Returns the denotation of the nth Church numeral for a given path.
-/
def Value.church (n : ℕ) (vs : Vector Value (n + 1)) : Value :=
  path n vs ⇾ vs.head ⇾ vs.last

namespace Example
  example : Value.church 0 ⟨[u], rfl⟩ = (⊥ ⇾ u ⇾ u) := rfl
  example : Value.church 1 ⟨[u, v], rfl⟩ = ((⊥ ⊔ u ⇾ v) ⇾ u ⇾ v) := rfl
  example : Value.church 2 ⟨[u, v, w], rfl⟩ = ((⊥ ⊔ u ⇾ v ⊔ v ⇾ w) ⇾ u ⇾ w) := rfl
end Example

section
  open Untyped.Term (church)
  open Eval

  def denot_church {vs} : `∅ ⊢ church n ⇓ Value.church n vs := by
    induction n with apply_rules [fn]
    | zero => let ⟨_ :: [], _⟩ := vs; exact var
    | succ n r =>
      have vsInit : Vector Value (n + 1) := by convert vs.take (n + 1) using 1; simp_arith
      have := @r vsInit
      apply ap (v := Value.path n vsInit ⇾ vs.head)
      · sorry
      · sorry
end
