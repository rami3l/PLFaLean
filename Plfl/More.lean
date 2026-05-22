-- https://plfa.github.io/More/

import Plfl.Init

-- This module was extended from the original one for <https://plfa.github.io/DeBruijn/>.
namespace More

-- https://plfa.github.io/More/#types
inductive Ty where
/-- Native natural type made of 𝟘 and ι. -/
| nat : Ty
/-- Primitive natural type, a simple wrapper around LEAN's own ℕ type. -/
| natP : Ty
/-- Product type. -/
| prod : Ty → Ty → Ty
/-- Sum type. -/
| sum : Ty → Ty → Ty
/-- Arrow type. -/
| fn : Ty → Ty → Ty
/-- Unit type. -/
| unit : Ty
/-- Void type. -/
| void : Ty
/-- List type. -/
| list : Ty → Ty
deriving BEq, DecidableEq, Repr

namespace Notation
  open Ty

  scoped notation "ℕt" => nat
  scoped notation "ℕp" => natP

  -- Operator overloadings for `prod` and `sum` types.
  instance : Mul Ty where mul := prod
  instance : Add Ty where add := sum

  scoped infixr:70 " =⇒ " => fn
  scoped notation "◯" => unit
  scoped notation "∅" => void
end Notation

open Notation

namespace Ty
  example : Ty := (ℕt =⇒ ℕt) =⇒ ℕt
  example : Ty := ℕp * ℕt

  theorem t_to_t'_ne_t (t t' : Ty) : (t =⇒ t') ≠ t := by
    by_contra h; match t with
    | nat => contradiction
    | fn ta tb => injection h; have := t_to_t'_ne_t ta tb; contradiction
end Ty

-- https://plfa.github.io/DeBruijn/#contexts
abbrev Context : Type := List Ty

namespace Context
  abbrev snoc (Γ : Context) (a : Ty) : Context := a :: Γ
  abbrev lappend (Γ : Context) (Δ : Context) : Context := Δ ++ Γ
end Context

namespace Notation
  open Context

  -- `‚` is not a comma! See: <https://www.compart.com/en/unicode/U+201A>
  scoped infixl:50 "‚ " => snoc
  scoped infixl:45 "‚‚ " => lappend
end Notation

-- https://plfa.github.io/DeBruijn/#variables-and-the-lookup-judgment
inductive Lookup : Context → Ty → Type where
| z : Lookup (Γ‚ t) t
| s : Lookup Γ t → Lookup (Γ‚ t') t
deriving DecidableEq, Repr

namespace Notation
  open Lookup

  scoped infix:40 " ∋ " => Lookup

  -- https://github.com/arthurpaulino/lean4-metaprogramming-book/blob/d6a227a63c55bf13d49d443f47c54c7a500ea27b/md/main/macros.md#simplifying-macro-declaration
  scoped syntax "get_elem" (ppSpace term) : term
  scoped macro_rules | `(term| get_elem $n) => match n.1.toNat with
  | 0 => `(term| Lookup.z)
  | n+1 => `(term| Lookup.s (get_elem $(Lean.quote n)))

  scoped macro "♯" n:term:90 : term => `(get_elem $n)
end Notation

namespace Lookup
  example : ∅‚ ℕt =⇒ ℕt‚ ℕt ∋ ℕt := .z
  example : ∅‚ ℕt =⇒ ℕt‚ ℕt ∋ ℕt := ♯0
  example : ∅‚ ℕt =⇒ ℕt‚ ℕt ∋ ℕt =⇒ ℕt := .s .z
  example : ∅‚ ℕt =⇒ ℕt‚ ℕt ∋ ℕt =⇒ ℕt := ♯1
end Lookup

-- https://plfa.github.io/DeBruijn/#terms-and-the-typing-judgment
/--
A term with typing judgement embedded in itself.
-/
inductive Term : Context → Ty → Type where
-- Lookup
| var : Γ ∋ a → Term Γ a
-- Lambda
| lam : Term (Γ‚ a) b → Term Γ (a =⇒ b)
| ap : Term Γ (a =⇒ b) → Term Γ a → Term Γ b
-- Native natural
| zero : Term Γ ℕt
| succ : Term Γ ℕt → Term Γ ℕt
| case : Term Γ ℕt → Term Γ a → Term (Γ‚ ℕt) a → Term Γ a
-- Fixpoint
| mu : Term (Γ‚ a) a → Term Γ a
-- Primitive natural
| prim : ℕ → Term Γ ℕp
| mulP : Term Γ ℕp → Term Γ ℕp → Term Γ ℕp
-- Let expression
| let : Term Γ a → Term (Γ‚ a) b → Term Γ b
-- Product
| prod : Term Γ a → Term Γ b → Term Γ (a * b)
| fst : Term Γ (a * b) → Term Γ a
| snd : Term Γ (a * b) → Term Γ b
-- Product (alternative formulation)
-- | caseProd : Term Γ (a * b) → Term (Γ‚ a‚ b) c → Term Γ c
-- Sum
| left : Term Γ a → Term Γ (a + b)
| right : Term Γ b → Term Γ (a + b)
| caseSum : Term Γ (a + b) → Term (Γ‚ a) c → Term (Γ‚ b) c → Term Γ c
-- Void
| caseVoid : Term Γ ∅ → Term Γ a
-- Unit
| unit : Term Γ ◯
-- List
| nil : Term Γ (.list a)
| cons : Term Γ a → Term Γ (.list a) → Term Γ (.list a)
| caseList : Term Γ (.list a) → Term Γ b → Term (Γ‚ a‚ .list a) b → Term Γ b
deriving DecidableEq, Repr

@[simp]
def Term.size : Term Γ a → Nat
  | .var _ => 1
  | .lam t => t.size + 1
  | .ap l m => l.size + m.size + 1
  | .zero => 1
  | .succ t => t.size + 1
  | .case l m n => l.size + m.size + n.size + 1
  | .mu t => t.size + 1
  | .prim _ => 1
  | .mulP m n => m.size + n.size + 1
  | .let m n => m.size + n.size + 1
  | .prod m n => m.size + n.size + 1
  | .fst t => t.size + 1
  | .snd t => t.size + 1
  | .left t => t.size + 1
  | .right t => t.size + 1
  | .caseSum s l r => s.size + l.size + r.size + 1
  | .caseVoid v => v.size + 1
  | .unit => 1
  | .nil => 1
  | .cons m n => m.size + n.size + 1
  | .caseList l m n => l.size + m.size + n.size + 1


namespace Notation
  open Term

  scoped infix:40 " ⊢ " => Term

  scoped prefix:50 "ƛ " => lam
  scoped prefix:50 "μ " => mu
  scoped notation "𝟘? " => case
  scoped infixr:min " $ " => ap
  scoped infixl:70 " □ " => ap
  scoped infixl:70 " ⋄ "   => mulP
  scoped prefix:80 "ι " => succ
  scoped prefix:90 "‵" => var

  scoped notation "𝟘" => zero
  scoped notation "◯" => unit

  -- https://plfa.github.io/DeBruijn/#abbreviating-de-bruijn-indices
  scoped macro "#" n:term:90 : term => `(‵♯$n)
end Notation

namespace Term
  example : ∅‚ ℕt =⇒ ℕt‚ ℕt ⊢ ℕt := #0
  example : ∅‚ ℕt =⇒ ℕt‚ ℕt ⊢ ℕt =⇒ ℕt := #1
  example : ∅‚ ℕt =⇒ ℕt‚ ℕt ⊢ ℕt := #1 $ #0
  example : ∅‚ ℕt =⇒ ℕt‚ ℕt ⊢ ℕt := #1 $ #1 $ #0
  example : ∅‚ ℕt =⇒ ℕt ⊢ ℕt =⇒ ℕt := ƛ (#1 $ #1 $ #0)

  def ofNat : ℕ → Γ ⊢ ℕt
  | 0 => .zero
  | n + 1 => .succ <| ofNat n

  instance : Coe ℕ (Γ ⊢ ℕt) where coe := ofNat
  instance : OfNat (Γ ⊢ ℕt) n where ofNat := ofNat n

  -- https://plfa.github.io/DeBruijn/#test-examples
  example : Γ ⊢ ℕt := ι ι 𝟘
  example : Γ ⊢ ℕt := 2

  @[simp] abbrev add : Γ ⊢ ℕt =⇒ ℕt =⇒ ℕt := μ ƛ ƛ (𝟘? (#1) (#0) (ι (#3 □ #0 □ #1)))
  abbrev four : Γ ⊢ ℕt := add □ 2 □ 2

  /--
  The Church numeral Ty.
  -/
  abbrev Ch (t : Ty) : Ty := (t =⇒ t) =⇒ t =⇒ t

  @[simp] abbrev succC : Γ ⊢ ℕt =⇒ ℕt := ƛ ι #0
  @[simp] abbrev twoC : Γ ⊢ Ch a := ƛ ƛ (#1 $ #1 $ #0)
  @[simp] abbrev addC : Γ ⊢ Ch a =⇒ Ch a =⇒ Ch a := ƛ ƛ ƛ ƛ (#3 □ #1 $ #2 □ #1 □ #0)
  abbrev four' : Γ ⊢ ℕt := addC □ twoC □ twoC □ succC □ 𝟘

  @[simp] abbrev mul : Γ ⊢ ℕt =⇒ ℕt =⇒ ℕt := μ ƛ ƛ (𝟘? (#1) 𝟘 (add □ #1 $ #3 □ #0 □ #1))
  abbrev four'' : Γ ⊢ ℕt := mul □ 2 □ 2

  -- https://plfa.github.io/DeBruijn/#exercise-mul-recommended
  @[simp] abbrev mulC : Γ ⊢ Ch a =⇒ Ch a =⇒ Ch a := ƛ ƛ ƛ ƛ (#3 □ (#2 □ #1) □ #0)

  -- https://plfa.github.io/More/#example
  example : ∅ ⊢ ℕp =⇒ ℕp := ƛ #0 ⋄ #0 ⋄ #0
end Term

namespace Subst
  -- https://plfa.github.io/DeBruijn/#renaming
  /--
  If one context maps to another,
  the mapping holds after adding the same variable to both contexts.
  -/
  def ext : (∀ {a}, Γ ∋ a → Δ ∋ a) → Γ‚ b ∋ a → Δ‚ b ∋ a := by
    intro ρ; intro
    | .z => exact .z
    | .s x => refine .s ?_; exact ρ x

  /--
  If one context maps to another,
  then the type judgements are the same in both contexts.
  -/
  def rename : (∀ {a}, Γ ∋ a → Δ ∋ a) → Γ ⊢ a → Δ ⊢ a := by
    intro ρ; intro
    | ‵ x => exact ‵ (ρ x)
    | ƛ n => exact ƛ (rename (ext ρ) n)
    | l □ m => exact rename ρ l □ rename ρ m
    | 𝟘 => exact 𝟘
    | ι n => exact ι (rename ρ n)
    | 𝟘? l m n => exact 𝟘? (rename ρ l) (rename ρ m) (rename (ext ρ) n)
    | μ n => exact μ (rename (ext ρ) n)
    | .prim n => exact .prim n
    | m ⋄ n => exact rename ρ m ⋄ rename ρ n
    | .let m n => exact .let (rename ρ m) (rename (ext ρ) n)
    | .prod m n => exact .prod (rename ρ m) (rename ρ n)
    | .fst n => exact .fst (rename ρ n)
    | .snd n => exact .snd (rename ρ n)
    | .left n => exact .left (rename ρ n)
    | .right n => exact .right (rename ρ n)
    | .caseSum s l r => exact .caseSum (rename ρ s) (rename (ext ρ) l) (rename (ext ρ) r)
    | .caseVoid v => exact .caseVoid (rename ρ v)
    | ◯ => exact ◯
    | .nil => exact .nil
    | .cons m n => exact .cons (rename ρ m) (rename ρ n)
    | .caseList l m n => exact .caseList (rename ρ l) (rename ρ m) (rename (ext (ext ρ)) n)

  abbrev shift : Γ ⊢ a → Γ‚ b ⊢ a := rename .s

  example
  : let m : ∅‚ ℕt =⇒ ℕt ⊢ ℕt =⇒ ℕt := ƛ (#1 $ #1 $ #0)
    let m' : ∅‚ ℕt =⇒ ℕt‚ ℕt ⊢ ℕt =⇒ ℕt := ƛ (#2 $ #2 $ #0)
    shift m = m'
  := rfl

  -- https://plfa.github.io/DeBruijn/#simultaneous-substitution
  /--
  If the variables in one context maps to some terms in another,
  the mapping holds after adding the same variable to both contexts.
  -/
  def exts : (∀ {a}, Γ ∋ a → Δ ⊢ a) → Γ‚ b ∋ a → Δ‚ b ⊢ a := by
    intro σ; intro
    | .z => exact ‵.z
    | .s x => apply shift; exact σ x

  /--
  General substitution for multiple free variables.
  If the variables in one context maps to some terms in another,
  then the type judgements are the same before and after the mapping,
  i.e. after replacing the free variables in the former with (expanded) terms.
  -/
  def subst : (∀ {a}, Γ ∋ a → Δ ⊢ a) → Γ ⊢ a → Δ ⊢ a := by
    intro σ; intro
    | ‵ i => exact σ i
    | ƛ n => exact ƛ (subst (exts σ) n)
    | l □ m => exact subst σ l □ subst σ m
    | 𝟘 => exact 𝟘
    | ι n => exact ι (subst σ n)
    | 𝟘? l m n => exact 𝟘? (subst σ l) (subst σ m) (subst (exts σ) n)
    | μ n => exact μ (subst (exts σ) n)
    | .prim n => exact .prim n
    | m ⋄ n => exact subst σ m ⋄ subst σ n
    | .let m n => exact .let (subst σ m) (subst (exts σ) n)
    | .prod m n => exact .prod (subst σ m) (subst σ n)
    | .fst n => exact .fst (subst σ n)
    | .snd n => exact .snd (subst σ n)
    | .left n => exact .left (subst σ n)
    | .right n => exact .right (subst σ n)
    | .caseSum s l r => exact .caseSum (subst σ s) (subst (exts σ) l) (subst (exts σ) r)
    | .caseVoid v => exact .caseVoid (subst σ v)
    | ◯ => exact ◯
    | .nil => exact .nil
    | .cons m n => exact .cons (subst σ m) (subst σ n)
    | .caseList l m n => exact .caseList (subst σ l) (subst σ m) (subst (exts (exts σ)) n)

  abbrev subst₁σ (v : Γ ⊢ b) : ∀ {a}, Γ‚ b ∋ a → Γ ⊢ a := by
    introv; intro
    | .z => exact v
    | .s x => exact ‵ x

  /--
  Substitution for one free variable `v` in the term `n`.
  -/
    abbrev subst₁ (v : Γ ⊢ b) (n : Γ‚ b ⊢ a) : Γ ⊢ a := by
    refine subst ?_ n; exact subst₁σ v

  /--
  Substitution for two free variables `v` and `w'` in the term `n`.
  -/
  abbrev subst₂ (v : Γ ⊢ b) (w : Γ ⊢ c) (n : Γ‚ b‚ c ⊢ a) : Γ ⊢ a := by
    refine subst ?_ n; introv; intro
    | .z => exact w
    | .s .z => exact v
    | .s (.s x) => exact ‵ x
end Subst

namespace Notation
  open Subst

  scoped notation:90 n "⟦" m "⟧" => subst₁ m n
end Notation

open Subst

namespace Subst
  example
  : let m : ∅ ⊢ ℕt =⇒ ℕt := ƛ (ι #0)
    let m' : ∅‚ ℕt =⇒ ℕt ⊢ ℕt =⇒ ℕt := ƛ (#1 $ #1 $ #0)
    let n : ∅ ⊢ ℕt =⇒ ℕt := ƛ (ƛ ι #0) □ ((ƛ ι #0) □ #0)
    m'⟦m⟧ = n
  := rfl

  example
  : let m : ∅‚ ℕt =⇒ ℕt ⊢ ℕt := #0 $ 𝟘
    let m' : ∅‚ ℕt =⇒ ℕt‚ ℕt ⊢ (ℕt =⇒ ℕt) =⇒ ℕt := ƛ (#0 $ #1)
    let n : ∅‚ ℕt =⇒ ℕt ⊢ (ℕt =⇒ ℕt) =⇒ ℕt := ƛ (#0 $ #1 $ 𝟘)
    m'⟦m⟧ = n
  := rfl
end Subst

inductive Value : Γ ⊢ a → Type where
| lam : Value (ƛ (n : Γ‚ a ⊢ b))
| zero : Value 𝟘
| succ : Value n → Value (ι n)
| prim : (n : ℕ) → Value (@Term.prim Γ n)
| prod : Value (v : Γ ⊢ a) → Value (w : Γ ⊢ b) → Value (.prod v w)
| left : Value v → Value (.left v)
| right : Value v → Value (.right v)
| unit : Value ◯
| nil : Value .nil
| cons : ∀ {v : Γ ⊢ a} {vs : Γ ⊢ .list a}, Value v → Value vs → Value (.cons v vs)
deriving DecidableEq, Repr

namespace Notation
  scoped notation "V𝟘" => Value.zero
end Notation

namespace Value
  def ofNat : (n : ℕ) → @Value Γ ℕt (Term.ofNat n)
  | 0 => V𝟘
  | n + 1 => succ <| ofNat n
end Value

-- https://plfa.github.io/DeBruijn/#reduction
/--
`Reduce t t'` says that `t` reduces to `t'` via a given step.
-/
inductive Reduce : (Γ ⊢ a) → (Γ ⊢ a) → Prop where
| lamβ : Value v → Reduce ((ƛ n) □ v) (n⟦v⟧)
| apξ₁ : Reduce l l' → Reduce (l □ m) (l' □ m)
| apξ₂ : Value v → Reduce m m' → Reduce (v □ m) (v □ m')
| zeroβ : Reduce (𝟘? 𝟘 m n) m
| succβ : Value v → Reduce (𝟘? (ι v) m n) (n⟦v⟧)
| succξ : Reduce m m' → Reduce (ι m) (ι m')
| caseξ : Reduce l l' → Reduce (𝟘? l m n) (𝟘? l' m n)
| muβ : Reduce (μ n) (n⟦μ n⟧)
-- https://plfa.github.io/More/#reduction
| mulPξ₁ : Reduce l l' → Reduce (l ⋄ m) (l' ⋄ m)
| mulPξ₂ : Reduce m m' → Reduce (l ⋄ m) (l ⋄ m')
| mulPδ : Reduce ((.prim c) ⋄ (.prim d)) (.prim (c * d))
-- https://plfa.github.io/More/#reduction-1
| letξ : Reduce m m' → Reduce (.let m n) (.let m' n)
| letβ : Value v → Reduce (.let v n) (n⟦v⟧)
-- https://plfa.github.io/More/#reduction-2
| prodξ₁ : Reduce m m' → Reduce (.prod m n) (.prod m' n)
| prodξ₂ : Reduce n n' → Reduce (.prod m n) (.prod m n')
| fstξ : Reduce l l' → Reduce (.fst l) (.fst l')
| fstβ : Value v → Value w → Reduce (.fst (.prod v w)) v
| sndξ : Reduce l l' → Reduce (.snd l) (.snd l')
| sndβ : Value v → Value w → Reduce (.snd (.prod v w)) w
-- https://plfa.github.io/More/#reduction-3
-- | caseProdξ : Reduce l l' → Reduce (.caseProd l m) (.caseProd l' m)
-- | caseProdβ
-- : Value (v : Γ ⊢ a)
-- → Value (w : Γ ⊢ b)
-- → Reduce (.caseProd (.prod v w) (m : Γ‚ a‚ b ⊢ c)) (subst₂ v w m)
-- https://plfa.github.io/More/#reduction-4
| caseSumξ : Reduce s s' → Reduce (.caseSum s l r) (.caseSum s' l r)
| leftξ : Reduce m m' → Reduce (.left m) (.left m')
| leftβ : Value v → Reduce (.caseSum (.left v) l r) (l⟦v⟧)
| rightξ : Reduce m m' → Reduce (.right m) (.right m')
| rightβ : Value v → Reduce (.caseSum (.right v) l r) (r⟦v⟧)
-- https://plfa.github.io/More/#reduction-7
| caseVoidξ : Reduce l l' → Reduce (.caseVoid l) (.caseVoid l')
-- https://plfa.github.io/More/#reduction-8
| caseListξ : Reduce l l' → Reduce (.caseList l m n) (.caseList l' m n)
| nilβ : Reduce (.caseList .nil m n) m
| consξ₁ : Reduce m m' → Reduce (.cons m n) (.cons m' n)
| consξ₂ : Reduce n n' → Reduce (.cons v n) (.cons v n')
| consβ : Reduce (.caseList (.cons v w) m n) (subst₂ v w n)

-- https://plfa.github.io/DeBruijn/#reflexive-and-transitive-closure

namespace Notation
  scoped infix:40 " —→ " => Reduce
end Notation

namespace Reduce
  /--
  A reflexive and transitive closure,
  defined as a sequence of zero or more steps of the underlying relation `—→`.
  -/
  abbrev Clos {Γ a} := Relation.ReflTransGen (α := Γ ⊢ a) Reduce
end Reduce

namespace Notation
  scoped infix:20 " —↠ " => Reduce.Clos
end Notation

namespace Reduce.Clos
  abbrev refl : m —↠ m := Relation.ReflTransGen.refl
  abbrev tail : (m —↠ n) → (n —→ n') → (m —↠ n') := Relation.ReflTransGen.tail
  abbrev head : (m —→ n) → (n —↠ n') → (m —↠ n') := Relation.ReflTransGen.head
  abbrev single : (m —→ n) → (m —↠ n) := Relation.ReflTransGen.single

  instance : Coe (m —→ n) (m —↠ n) where coe r := .single r

  instance : Trans (α := Γ ⊢ a) Clos Reduce Clos where trans c r := c.tail r
  instance : Trans (α := Γ ⊢ a) Reduce Reduce Clos where trans r r' := .tail r r'
  instance : Trans (α := Γ ⊢ a) Reduce Clos Clos where trans r c := .head r c
end Reduce.Clos

namespace Reduce
  -- https://plfa.github.io/DeBruijn/#examples
  open Term

  example : twoC □ succC □ @zero ∅ —↠ 2 := calc
    twoC □ succC □ 𝟘
    _ —→ (ƛ (succC $ succC $ #0)) □ 𝟘 := by apply apξ₁; apply lamβ; exact Value.lam
    _ —→ (succC $ succC $ 𝟘) := by apply lamβ; exact V𝟘
    _ —→ succC □ 1 := by
      apply apξ₂
      · apply Value.lam
      · unfold succC; exact lamβ V𝟘
    _ —→ 2 := by unfold succC; apply lamβ; exact Value.ofNat 1
end Reduce

-- https://plfa.github.io/DeBruijn/#values-do-not-reduce
theorem Value.not_reduce : Value m → ∀ {n}, ¬ m —→ n := by
  introv v; intro r
  cases v with try contradiction
  | succ v => cases r; · case succξ => apply not_reduce v; trivial
  | prod => cases r with
    | prodξ₁ r => rename_i v _ _; apply not_reduce v; trivial
    | prodξ₂ r => rename_i v _; apply not_reduce v; trivial
  | left v => cases r; · case leftξ => apply not_reduce v; trivial
  | right v => cases r; · case rightξ => apply not_reduce v; trivial
  | cons => cases r with
    | consξ₁ r => rename_i v _ _; apply not_reduce v; trivial
    | consξ₂ r => rename_i v _; apply not_reduce v; trivial

theorem Reduce.empty_value : m —→ n → IsEmpty (Value m) := by
  intro r; is_empty; intro v; exact Value.not_reduce v r

/--
If a term `m` is not ill-typed, then it either is a value or can be reduced.
-/
inductive Progress (m : ∅ ⊢ a) where
| step : (m —→ n) → Progress m
| done : Value m → Progress m

def Progress.progress : (m : ∅ ⊢ a) → Progress m := open Reduce in by
  intro
  | ‵ _ => contradiction
  | ƛ _ => exact .done .lam
  | l □ m => match progress l with
    | .step _ => apply step; apply apξ₁; trivial
    | .done l => match progress m with
      | .step _ => apply step; apply apξ₂ <;> trivial
      | .done _ => match l with
        | .lam => apply step; apply lamβ; trivial
  | 𝟘 => exact .done V𝟘
  | ι n => match progress n with
    | .step _ => apply step; apply succξ; trivial
    | .done _ => apply done; apply Value.succ; trivial
  | 𝟘? l m n => match progress l with
    | .step _ => apply step; apply caseξ; trivial
    | .done v => match v with
      | .zero => exact .step zeroβ
      | .succ _ => apply step; apply succβ; trivial
  | μ _ => exact .step muβ
  | .prim n => exact .done (.prim n)
  | m ⋄ n => match progress m with
    | .step _ => apply step; apply mulPξ₁; trivial
    | .done m => match progress n with
      | .step _ => apply step; apply mulPξ₂; trivial
      | .done n => match m, n with
        | .prim m, .prim n => exact .step mulPδ
  | .let m n => match progress m with
    | .step _ => apply step; apply letξ; trivial
    | .done m => apply step; apply letβ; trivial
  | .prod m n => match progress m with
    | .step _ => apply step; apply prodξ₁; trivial
    | .done m => match progress n with
      | .step _ => apply step; apply prodξ₂; trivial
      | .done n => exact .done (.prod m n)
  | .fst n => match progress n with
    | .step _ => apply step; apply fstξ; trivial
    | .done n => match n with
      | .prod v w => apply step; apply fstβ <;> trivial
  | .snd n => match progress n with
    | .step _ => apply step; apply sndξ; trivial
    | .done n => match n with
      | .prod v w => apply step; apply sndβ <;> trivial
  | .left n => match progress n with
    | .step _ => apply step; apply leftξ; trivial
    | .done n => exact .done (.left n)
  | .right n => match progress n with
    | .step _ => apply step; apply rightξ; trivial
    | .done n => exact .done (.right n)
  | .caseSum s l r => match progress s with
    | .step _ => apply step; apply caseSumξ; trivial
    | .done s => match s with
      | .left _ => apply step; apply leftβ; trivial
      | .right _ => apply step; apply rightβ; trivial
  | .caseVoid v => match progress v with
    | .step _ => apply step; apply caseVoidξ; trivial
    | .done _ => contradiction
  | ◯ => exact .done .unit
  | .nil => exact .done .nil
  | .cons m n => match progress m with
    | .step _ => apply step; apply consξ₁; trivial
    | .done _ => match progress n with
      | .step _ => apply step; apply consξ₂; trivial
      | .done _ => refine .done (.cons ?_ ?_) <;> trivial
  | .caseList l m n => match progress l with
    | .step _ => apply step; apply caseListξ; trivial
    | .done l => match l with
      | .nil => apply step; exact nilβ
      | .cons _ w => apply step; exact consβ

open Progress (progress)

inductive Result (n : Γ ⊢ a) where
| done (val : Value n)
| dnf
deriving BEq, DecidableEq, Repr

inductive Steps (l : Γ ⊢ a) where
| steps : ∀{n : Γ ⊢ a}, (l —↠ n) → Result n → Steps l

def eval (gas : ℕ) (l : ∅ ⊢ a) : Steps l :=
  if gas = 0 then
    ⟨.refl, .dnf⟩
  else
    match progress l with
    | .done v => .steps .refl <| .done v
    | .step r =>
      let ⟨rs, res⟩ := eval (gas - 1) (by trivial)
      ⟨Trans.trans r rs, res⟩

section examples
  open Term

  -- def x : ℕ := x + 1
  abbrev succμ : ∅ ⊢ ℕt := μ ι #0

  abbrev evalRes (l : ∅ ⊢ a) (gas := 100) := (eval gas l).3

  #eval evalRes (gas := 3) succμ
  #eval evalRes <| add □ 2 □ 1
  #eval evalRes <| mul □ 2 □ 2
  -- Prim
  #eval evalRes <| .prim 2 ⋄ .prim 3
  -- Let
  #eval evalRes <| .let (.prim 6) (#0 ⋄ .prim 7)
  #eval evalRes <| .let (.prim 3) <| .let (.prim 4) (.prod (#1) (#0))
  -- Prod, Unit
  #eval evalRes <| .fst <| .snd <| .prod ◯ (.prod (.prim 6) (ι ι 0))
  -- Sum
  #eval evalRes <| (.left (.prim 3) : ∅ ⊢ ℕp + ℕt)
  #eval evalRes <| (.right 4 : ∅ ⊢ ℕp + ℕt)
  #eval evalRes <| .caseSum (.right 1 : ∅ ⊢ ℕp + ℕt) 𝟘 (.succ (#0))
  -- List
  #eval evalRes <| .nil (a := ℕt)
  #eval evalRes <| .cons (ι 𝟘) <| .cons 𝟘 .nil
  #eval evalRes <| .caseList (.cons (ι 𝟘) <| .cons 𝟘 .nil) 𝟘 (#1 /- 0:cdr, 1:car -/)
end examples
