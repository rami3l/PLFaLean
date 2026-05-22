-- https://plfa.github.io/DeBruijn/

import Plfl.Init

-- Sorry, nothing is inherited from previous chapters here. We have to start over.
namespace DeBruijn

-- https://plfa.github.io/DeBruijn/#types
inductive Ty where
| nat : Ty
| fn : Ty → Ty → Ty
deriving BEq, DecidableEq, Repr

namespace Ty
  notation "ℕt" => nat
  infixr:70 " =⇒ " => fn

  example : Ty := (ℕt =⇒ ℕt) =⇒ ℕt

  theorem t_to_t'_ne_t (t t' : Ty) : (t =⇒ t') ≠ t := by
    by_contra h; match t with
    | nat => trivial
    | fn ta tb => injection h; have := t_to_t'_ne_t ta tb; contradiction
end Ty

-- https://plfa.github.io/DeBruijn/#contexts
abbrev Context : Type := List Ty

namespace Context
  abbrev snoc : Context → Ty → Context := flip (· :: ·)
  -- `‚` is not a comma! See: <https://www.compart.com/en/unicode/U+201A>
  infixl:50 " ‚ " => snoc
end Context

-- https://plfa.github.io/DeBruijn/#variables-and-the-lookup-judgment
inductive Lookup : Context → Ty → Type where
| z : Lookup (Γ‚ t) t
| s : Lookup Γ t → Lookup (Γ‚ t') t
deriving DecidableEq, Repr

namespace Lookup
  infix:40 " ∋ " => Lookup

  -- https://github.com/arthurpaulino/lean4-metaprogramming-book/blob/d6a227a63c55bf13d49d443f47c54c7a500ea27b/md/main/macros.md#simplifying-macro-declaration
  syntax "get_elem" (ppSpace term) : tactic
  macro_rules | `(tactic| get_elem $n) => match n.1.toNat with
  | 0 => `(tactic | exact Lookup.z)
  | n+1 => `(tactic| apply Lookup.s; get_elem $(Lean.quote n))

  macro "♯ " n:term:90 : term => `(by get_elem $n)

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
| var : Γ ∋ a → Term Γ a
| lam : Term (Γ‚ a) b → Term Γ (a =⇒ b)
| ap : Term Γ (a =⇒ b) → Term Γ a → Term Γ b
| zero : Term Γ ℕt
| succ : Term Γ ℕt → Term Γ ℕt
| case : Term Γ ℕt → Term Γ a → Term (Γ‚ ℕt) a → Term Γ a
| mu : Term (Γ‚ a) a → Term Γ a
deriving DecidableEq, Repr

namespace Term
  infix:40 " ⊢ " => Term

  prefix:50 "ƛ " => lam
  prefix:50 "μ " => mu
  notation "𝟘? " => case
  infixr:min " $ " => ap
  infixl:70 " □ " => ap
  prefix:80 "ι " => succ
  prefix:90 "‵" => var
  notation "𝟘" => zero

  -- https://plfa.github.io/DeBruijn/#abbreviating-de-bruijn-indices
  macro "# " n:term:90 : term => `(‵ ♯$n)

  example : ∅‚ ℕt =⇒ ℕt‚ ℕt ⊢ ℕt := #0
  example : ∅‚ ℕt =⇒ ℕt‚ ℕt ⊢ ℕt =⇒ ℕt := #1
  example : ∅‚ ℕt =⇒ ℕt‚ ℕt ⊢ ℕt := #1 $ #0
  example : ∅‚ ℕt =⇒ ℕt‚ ℕt ⊢ ℕt := #1 $ #1 $ #0
  example : ∅‚ ℕt =⇒ ℕt ⊢ ℕt =⇒ ℕt := ƛ (#1 $ #1 $ #0)
  example : ∅ ⊢ (ℕt =⇒ ℕt) =⇒ ℕt =⇒ ℕt := ƛ ƛ (#1 $ #1 $ #0)

  def ofNat : ℕ → Γ ⊢ ℕt
  | 0 => zero
  | n + 1 => succ <| ofNat n

  instance : Coe ℕ (Γ ⊢ ℕt) where coe := ofNat
  instance : OfNat (Γ ⊢ ℕt) n where ofNat := ofNat n

  -- https://plfa.github.io/DeBruijn/#test-examples
  example : Γ ⊢ ℕt := ι ι 𝟘
  example : Γ ⊢ ℕt := 2

  @[simp] abbrev add : Γ ⊢ ℕt =⇒ ℕt =⇒ ℕt := μ ƛ ƛ (𝟘? (#1) (#0) (ι (#3 □ #0 □ #1)))
  @[simp] abbrev mul : Γ ⊢ ℕt =⇒ ℕt =⇒ ℕt := μ ƛ ƛ (𝟘? (#1) 𝟘 (add □ #1 $ #3 □ #0 □ #1))

  example : Γ ⊢ ℕt := add □ 2 □ 2

  /--
  The Church numeral Ty.
  -/
  abbrev Ch (t : Ty) : Ty := (t =⇒ t) =⇒ t =⇒ t

  @[simp] abbrev succC : Γ ⊢ ℕt =⇒ ℕt := ƛ ι #0
  @[simp] abbrev twoC : Γ ⊢ Ch a := ƛ ƛ (#1 $ #1 $ #0)
  @[simp] abbrev addC : Γ ⊢ Ch a =⇒ Ch a =⇒ Ch a := ƛ ƛ ƛ ƛ (#3 □ #1 $ #2 □ #1 □ #0)
  example : Γ ⊢ ℕt := addC □ twoC □ twoC □ succC □ 𝟘

  -- https://plfa.github.io/DeBruijn/#exercise-mul-recommended
  @[simp] abbrev mulC : Γ ⊢ Ch a =⇒ Ch a =⇒ Ch a := ƛ ƛ ƛ ƛ (#3 □ (#2 □ #1) □ #0)
end Term

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
  | ƛ n => refine .lam ?_; refine rename ?_ n; exact ext ρ
  | l □ m =>
    apply Term.ap
    · exact rename ρ l
    · exact rename ρ m
  | 𝟘 => exact 𝟘
  | ι n => refine ι ?_; exact rename ρ n
  | 𝟘? l m n =>
    apply Term.case
    · exact rename ρ l
    · exact rename ρ m
    · refine rename ?_ n; exact ext ρ
  | μ n => refine .mu ?_; refine rename ?_ n; exact ext ρ

example
: let m : ∅‚ ℕt =⇒ ℕt ⊢ ℕt =⇒ ℕt := ƛ (#1 $ #1 $ #0)
  let m' : ∅‚ ℕt =⇒ ℕt‚ ℕt ⊢ ℕt =⇒ ℕt := ƛ (#2 $ #2 $ #0)
  rename .s m = m'
:= rfl

-- https://plfa.github.io/DeBruijn/#simultaneous-substitution
/--
If the variables in one context maps to some terms in another,
the mapping holds after adding the same variable to both contexts.
-/
def exts : (∀ {a}, Γ ∋ a → Δ ⊢ a) → Γ‚ b ∋ a → Δ‚ b ⊢ a := by
  intro σ; intro
  | .z => exact ‵.z
  | .s x => apply rename .s; exact σ x

/--
General substitution for multiple free variables.
If the variables in one context maps to some terms in another,
then the type judgements are the same before and after the mapping,
i.e. after replacing the free variables in the former with (expanded) terms.
-/
def subst : (∀ {a}, Γ ∋ a → Δ ⊢ a) → Γ ⊢ a → Δ ⊢ a := by
  intro σ; intro
  | ‵ x => exact σ x
  | ƛ n => refine .lam ?_; refine subst ?_ n; exact exts σ
  | l □ m =>
    apply Term.ap
    · exact subst σ l
    · exact subst σ m
  | 𝟘 => exact 𝟘
  | ι n => refine ι ?_; exact subst σ n
  | 𝟘? l m n =>
    apply Term.case
    · exact subst σ l
    · exact subst σ m
    · refine subst ?_ n; exact exts σ
  | μ n => refine .mu ?_; refine subst ?_ n; exact exts σ

/--
Substitution for one free variable `m` in the term `n`.
-/
abbrev subst₁ (m : Γ ⊢ b) (n : Γ‚ b ⊢ a) : Γ ⊢ a := by
  refine subst ?_ n; introv; intro
  | .z => exact m
  | .s x => exact ‵ x

notation:90 n "⟦" m "⟧" => subst₁ m n

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

inductive Value : Γ ⊢ a → Type where
| lam : Value (ƛ (n : Γ‚ a ⊢ b))
| zero: Value 𝟘
| succ: Value n → Value (ι n)
deriving BEq, DecidableEq, Repr

namespace Value
  notation "V𝟘" => zero

  def ofNat : (n : ℕ) → @Value Γ ℕt (Term.ofNat n)
  | 0 => V𝟘
  | n + 1 => succ <| ofNat n
end Value

-- https://plfa.github.io/DeBruijn/#reduction
/--
`Reduce t t'` says that `t` reduces to `t'`.
-/
inductive Reduce : (Γ ⊢ a) → (Γ ⊢ a) → Type where
| lamβ : Value w → Reduce ((ƛ n) □ w) (n⟦w⟧)
| apξ₁ : Reduce l l' → Reduce (l □ m) (l' □ m)
| apξ₂ : Value v → Reduce m m' → Reduce (v □ m) (v □ m')
| zeroβ : Reduce (𝟘? 𝟘 m n) m
| succβ : Value v → Reduce (𝟘? (ι v) m n) (n⟦v⟧)
| succξ : Reduce m m' → Reduce (ι m) (ι m')
| caseξ : Reduce l l' → Reduce (𝟘? l m n) (𝟘? l' m n)
| muβ : Reduce (μ n) (n⟦μ n⟧)
deriving Repr

infix:40 " —→ " => Reduce

namespace Reduce
  -- https://plfa.github.io/DeBruijn/#reflexive-and-transitive-closure
  /--
  A reflexive and transitive closure,
  defined as a sequence of zero or more steps of the underlying relation `—→`.
  -/
  inductive Clos : (Γ ⊢ a) → (Γ ⊢ a) → Type where
  | nil : Clos m m
  | cons : (l —→ m) → Clos m n → Clos l n
  deriving Repr

  infix:20 " —↠ " => Clos

  namespace Clos
    def length : (m —↠ n) → Nat
    | nil => 0
    | cons _ cdr => 1 + cdr.length

    @[simp] abbrev one (car : m —→ n) : (m —↠ n) := cons car nil
    instance : Coe (m —→ n) (m —↠ n) where coe := one

    def trans : (l —↠ m) → (m —↠ n) → (l —↠ n)
    | nil, c => c
    | cons h c, c' => cons h <| c.trans c'

    instance : Trans (α := Γ ⊢ a) Clos Clos Clos where
      trans := trans

    instance : Trans (α := Γ ⊢ a) Reduce Clos Clos where
      trans := cons

    instance : Trans (α := Γ ⊢ a) Reduce Reduce Clos where
      trans c c' := cons c <| cons c' nil

    def transOne : (l —↠ m) → (m —→ n) → (l —↠ n)
    | nil, c => c
    | cons h c, c' => cons h <| c.trans c'

    instance : Trans (α := Γ ⊢ a) Clos Reduce Clos where
      trans := transOne
  end Clos

  open Term

  -- https://plfa.github.io/DeBruijn/#examples
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
theorem Value.empty_reduce : Value m → ∀ {n}, IsEmpty (m —→ n) := by
  introv v; is_empty; intro r
  cases v <;> try contradiction
  · case succ v => cases r; · case succξ => apply (empty_reduce v).false; trivial

theorem Reduce.empty_value : m —→ n → IsEmpty (Value m) := by
  intro r; is_empty; intro v
  have : ∀ {n}, IsEmpty (m —→ n) := Value.empty_reduce v
  exact this.false r

/--
If a term `m` is not ill-typed, then it either is a value or can be reduced.
-/
inductive Progress (m : ∅ ⊢ a) where
| step : (m —→ n) → Progress m
| done : Value m → Progress m

def progress : (m : ∅ ⊢ a) → Progress m := open Progress Reduce in by
  intro
  | ‵ _ => contradiction
  | ƛ _ => exact .done Value.lam
  | jl □ jm => cases progress jl with
    | step => apply step; · apply apξ₁; trivial
    | done vl => cases progress jm with
      | step => apply step; apply apξ₂ <;> trivial
      | done => cases vl with
        | lam => apply step; apply lamβ; trivial
  | 𝟘 => exact done V𝟘
  | ι j => cases progress j with
    | step => apply step; apply succξ; trivial
    | done => apply done; apply Value.succ; trivial
  | 𝟘? jl jm jn => cases progress jl with
    | step => apply step; apply caseξ; trivial
    | done vl => cases vl with
      | zero => exact step zeroβ
      | succ => apply step; apply succβ; trivial
  | μ _ => exact step muβ

inductive Result (n : Γ ⊢ a) where
| done (val : Value n)
| dnf
deriving BEq, DecidableEq, Repr

inductive Steps (l : Γ ⊢ a) where
| steps : ∀{n : Γ ⊢ a}, (l —↠ n) → Result n → Steps l
deriving Repr

def eval (gas : ℕ) (l : ∅ ⊢ a) : Steps l :=
  if gas = 0 then
    ⟨.nil, .dnf⟩
  else
    match progress l with
    | .done v => .steps .nil <| .done v
    | .step r =>
      let ⟨rs, res⟩ := eval (gas - 1) (by trivial)
      ⟨.cons r rs, res⟩

section examples
  open Term

  -- def x : ℕ := x + 1
  abbrev succμ : ∅ ⊢ ℕt := μ ι #0

  #eval eval 3 succμ |> (·.3)
  #eval eval 100 (add □ 2 □ 2) |> (·.3)
  #eval eval 100 (mul □ 2 □ 3) |> (·.3)
end examples
