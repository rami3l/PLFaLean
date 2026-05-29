module

-- https://plfa.github.io/Lambda/

public import Plfl.Init

@[expose] public section

namespace Lambda

open String

def Sym : Type := String deriving BEq, DecidableEq, Repr

-- https://plfa.github.io/Lambda/#syntax-of-terms
inductive Term where
| var : Sym → Term
| lam : Sym → Term → Term
| ap : Term → Term → Term
| zero : Term
| succ : Term → Term
| case : Term → Term → Sym → Term → Term
| mu : Sym → Term → Term
deriving BEq, DecidableEq, Repr

namespace Term
  notation:50 "ƛ " v " : " d => lam v d
  notation:50 " μ " v " : " d => mu v d
  notation:max "𝟘? " e " [zero: " o " |succ " n " : " i " ] " => case e o n i
  infixr:min " $ " => ap
  infixl:70 " □ " => ap
  prefix:80 "ι " => succ
  prefix:90 "‵" => var
  notation "𝟘" => zero

  example : Term := ‵"foo"
  example : Term := 𝟘? ‵"bar" [zero: 𝟘 |succ "n" : ι 𝟘]

  @[simp] def ofNat | 0 => zero | n + 1 => succ <| ofNat n
  instance : Coe ℕ Term where coe := ofNat
  instance : OfNat Term n where ofNat := ofNat n

  example : Term := 1
  example : Term := 42

  abbrev add : Term := μ "+" : ƛ "m" : ƛ "n" : 𝟘? ‵"m" [zero: ‵"n" |succ "m": ι (‵"+" □ ‵"m" □ ‵"n")]
  -- https://plfa.github.io/Lambda/#exercise-mul-recommended
  abbrev mul : Term := μ "*" : ƛ "m" : ƛ "n" : 𝟘? ‵"m" [zero: 𝟘 |succ "m": add □ ‵"n" $ ‵"*" □ ‵"m" □ ‵"n"]

  -- Church encoding...
  abbrev succC : Term := ƛ "n" : ι ‵"n"
  abbrev oneC : Term := ƛ "s" : ƛ "z" : ‵"s" $ ‵"z"
  abbrev twoC : Term := ƛ "s" : ƛ "z" : ‵"s" $ ‵"s" $ ‵"z"
  abbrev addC : Term := ƛ "m" : ƛ "n" : ƛ "s" : ƛ "z" : ‵"m" □ ‵"s" $ ‵"n" □ ‵"s" □ ‵"z"
  -- https://plfa.github.io/Lambda/#exercise-mul%E1%B6%9C-practice
  abbrev mulC : Term := ƛ "m" : ƛ "n" : ƛ "s" : ƛ "z" : ‵"m" □ (‵"n" □ ‵"s") □ ‵"z"
end Term

-- https://plfa.github.io/Lambda/#values
inductive Value : Term → Type where
| lam : Value (ƛ v : d)
| zero: Value 𝟘
| succ: Value n → Value (ι n)
deriving BEq, DecidableEq, Repr

namespace Value
  notation "V𝟘" => zero

  def ofNat : (n : ℕ) → Value (Term.ofNat n)
  | 0 => V𝟘
  | n + 1 => succ <| ofNat n

  -- instance : CoeDep ℕ n (Value ↑n) where coe := ofNat n
  -- instance : OfNat (Value (Term.ofNat n)) n where ofNat := ofNat n
end Value

-- https://plfa.github.io/Lambda/#substitution
namespace Term
  /--
  `x.subst y v` substitutes term `v` for all free occurrences of variable `y` in term `x`.
  -/
  def subst : Term → Sym → Term → Term
  | ‵x, y, v => if x = y then v else ‵x
  | ƛ x : n, y, v => if x = y then ƛ x : n else ƛ x : n.subst y v
  | ap l m, y, v => l.subst y v $ m.subst y v
  | 𝟘, _, _ => 𝟘
  | ι n, y, v => ι (n.subst y v)
  | 𝟘? l [zero: m |succ x: n], y, v => if x = y
      then 𝟘? l.subst y v [zero: m.subst y v |succ x: n]
      else 𝟘? l.subst y v [zero: m.subst y v |succ x: n.subst y v]
  | μ x : n, y, v => if x = y then μ x : n else μ x : n.subst y v

  notation:90 x " [ " y " := " v " ] " => subst x y v

  -- https://plfa.github.io/Lambda/#examples
  example
  : (ƛ "z" : ‵"s" □ ‵"s" □ ‵"z")["s" := succC]
  = (ƛ "z" : succC □ succC □ ‵"z") := rfl

  example : (succC □ succC □ ‵"z")["z" := 𝟘] = succC □ succC □ 𝟘 := rfl
  example : (ƛ "x" : ‵"y")["y" := 𝟘] = (ƛ "x" : 𝟘) := rfl
  example : (ƛ "x" : ‵"x")["x" := 𝟘] = (ƛ "x" : ‵"x") := rfl
  example : (ƛ "y" : ‵"y")["x" := 𝟘] = (ƛ "y" : ‵"y") := rfl

  -- https://plfa.github.io/Lambda/#quiz
  example
  : (ƛ "y" : ‵"x" $ ƛ "x" : ‵"x")["x" := 𝟘]
  = (ƛ "y" : 𝟘 $ ƛ "x" : ‵"x")
  := rfl

  -- https://plfa.github.io/Lambda/#reduction
  /--
  `Reduce t t'` says that `t` reduces to `t'`.
  -/
  inductive Reduce : Term → Term → Type where
  | lamβ : Value v → Reduce ((ƛ x : n) □ v) (n[x := v])
  | apξ₁ : Reduce l l' → Reduce (l □ m) (l' □ m)
  | apξ₂ : Value v → Reduce m m' → Reduce (v □ m) (v □ m')
  | zeroβ : Reduce (𝟘? 𝟘 [zero: m |succ x : n]) m
  | succβ : Value v → Reduce (𝟘? ι v [zero: m |succ x : n]) (n[x := v])
  | succξ : Reduce m m' → Reduce (ι m) (ι m')
  | caseξ : Reduce l l' → Reduce (𝟘? l [zero: m |succ x : n]) (𝟘? l' [zero: m |succ x : n])
  | muβ : Reduce (μ x : m) (m[x := μ x : m])
  deriving Repr

  infix:40 " —→ " => Reduce
end Term

namespace Term.Reduce
  -- https://plfa.github.io/Lambda/#quiz-1
  example : (ƛ "x" : ‵"x") □ (ƛ "x" : ‵"x") —→ (ƛ "x" : ‵"x") := by
    apply lamβ; exact Value.lam

  example : (ƛ "x" : ‵"x") □ (ƛ "x" : ‵"x") □ (ƛ "x" : ‵"x") —→ (ƛ "x" : ‵"x") □ (ƛ "x" : ‵"x") := by
    apply apξ₁; apply lamβ; exact Value.lam

  example : twoC □ succC □ 𝟘 —→ (ƛ "z" : succC $ succC $ ‵"z") □ 𝟘 := by
    unfold twoC; apply apξ₁; apply lamβ; exact Value.lam

  -- https://plfa.github.io/Lambda/#reflexive-and-transitive-closure
  /--
  A reflexive and transitive closure,
  defined as a sequence of zero or more steps of the underlying relation `—→`.
  -/
  inductive Clos : Term → Term → Type where
  | nil : Clos m m
  | cons : (l —→ m) → Clos m n → Clos l n
  deriving Repr

  infix:20 " —↠ " => Clos

  namespace Clos
    def length : (m —↠ n) → Nat
    | nil => 0
    | cons _ cdr => 1 + cdr.length

    abbrev one (car : m —→ n) : (m —↠ n) := cons car nil
    instance : Coe (m —→ n) (m —↠ n) where coe := one

    def trans : (l —↠ m) → (m —↠ n) → (l —↠ n)
    | nil, c => c
    | cons h c, c' => cons h <| c.trans c'

    instance : Trans Clos Clos Clos where
      trans := trans

    instance : Trans Reduce Clos Clos where
      trans := cons

    instance : Trans Reduce Reduce Clos where
      trans c c' := cons c <| cons c' nil

    def transOne : (l —↠ m) → (m —→ n) → (l —↠ n)
    | nil, c => c
    | cons h c, c' => cons h <| c.trans c'

    instance : Trans Clos Reduce Clos where
      trans := transOne
  end Clos

  inductive Clos' : Term → Term → Type where
  | refl : Clos' m m
  | step : (m —→ n) → Clos' m n
  | trans : Clos' l m → Clos' m n → Clos' l n

  infix:20 " —↠' " => Clos'

  def Clos.toClos' : (m —↠ n) → (m —↠' n) := by
    intro
    | nil => exact Clos'.refl
    | cons h h' => exact Clos'.trans (Clos'.step h) h'.toClos'

  def Clos'.toClos : (m —↠' n) → (m —↠ n) := by
    intro
    | refl => exact Clos.nil
    | step h => exact ↑h
    | trans h h' => apply Clos.trans <;> (apply toClos; assumption)

  -- https://plfa.github.io/Lambda/#exercise-practice
  lemma Clos.toClos'_left_inv : ∀ {x : m —↠ n}, x.toClos'.toClos = x := by intro
  | nil => rfl
  | cons car cdr =>
    simp_all only [Clos.toClos', Clos'.toClos, Clos.trans, Clos.cons.injEq, heq_eq_eq, true_and]
    exact toClos'_left_inv (x := cdr)

  lemma Clos.toClos'_inj
  : @Function.Injective (m —↠ n) (m —↠' n) Clos.toClos'
  := by
    unfold Function.Injective
    intro a b h
    apply_fun Clos'.toClos at h
    rwa [←toClos'_left_inv (x := a), ←toClos'_left_inv (x := b)]

  instance Clos.embedsInClos' : (m —↠ n) ↪ (m —↠' n) where
    toFun := toClos'
    inj' := toClos'_inj
end Term.Reduce

-- https://plfa.github.io/Lambda/#confluence
section confluence
  open Term.Reduce Term.Reduce.Clos

  -- `Σ` is used instead of `∃` because it's a `Type` that exists, not a `Prop`.
  def Diamond : Type := ∀ ⦃l m n⦄, (l —→ m) → (l —→ n) → (Σ p, (m —↠ p) × (n —↠ p))
  def Confluence : Type := ∀ ⦃l m n⦄, (l —↠ m) → (l —↠ n) → (Σ p, (m —↠ p) × (n —↠ p))
  def Deterministic : Prop := ∀ ⦃l m n⦄, (l —→ m) → (l —→ n) → (m = n)

  def Deterministic.toDiamond : Deterministic → Diamond := by
    unfold Deterministic Diamond; intro h l m n lm ln
    have heq := h lm ln; simp_all only
    exists n; exact ⟨nil, nil⟩

  def Deterministic.toConfluence : Deterministic → Confluence
  | h, l, m, n, lm, ln => by match lm, ln with
    | nil, nil => exists n; exact ⟨ln, ln⟩
    | nil, c@(cons _ _) => exists n; exact ⟨c, nil⟩
    | c@(cons _ _), nil => exists m; exact ⟨nil, c⟩
    | cons car cdr, cons car' cdr' =>
      have := h car car'; subst this
      exact toConfluence h cdr cdr'
end confluence

-- https://plfa.github.io/Lambda/#examples-1
section examples
  open Term Term.Reduce Term.Reduce.Clos

  example : twoC □ succC □ 𝟘 —↠ 2 := calc
    twoC □ succC □ 𝟘
    _ —→ (ƛ "z" : succC $ succC $ ‵"z") □ 𝟘 := by apply apξ₁; apply lamβ; exact Value.lam
    _ —→ (succC $ succC $ 𝟘) := by apply lamβ; exact Value.zero
    _ —→ succC □ 1 := by apply apξ₂; apply Value.lam; apply lamβ; exact Value.zero
    _ —→ 2 := by apply lamβ; exact Value.ofNat 1

  -- https://plfa.github.io/Lambda/#exercise-plus-example-practice
  example : add □ 1 □ 1 —↠ 2 := calc
    add □ 1 □ 1
    _ —→ (ƛ "m" : ƛ "n" : 𝟘? ‵"m" [zero: ‵"n" |succ "m": ι (add □ ‵"m" □ ‵"n")]) □ 1 □ 1
      := by apply apξ₁; apply apξ₁; apply muβ
    _ —↠ (ƛ "n" : 𝟘? 1 [zero: ‵"n" |succ "m": ι (add □ ‵"m" □ ‵"n")]) □ 1
      := .one <| by apply apξ₁; apply lamβ; exact Value.ofNat 1
    _ —→ 𝟘? 1 [zero: 1 |succ "m": ι (add □ ‵"m" □ 1)]
      := lamβ <| Value.ofNat 1
    _ —→ ι (add □ 𝟘 □ 1)
      := succβ Value.zero
    _ —→ ι ((ƛ "m" : ƛ "n" : 𝟘? ‵"m" [zero: ‵"n" |succ "m": ι (add □ ‵"m" □ ‵"n")]) □ 𝟘 □ 1)
      := by apply succξ; apply apξ₁; apply apξ₁; apply muβ
    _ —→ ι ((ƛ "n" : 𝟘? 𝟘 [zero: ‵"n" |succ "m": ι (add □ ‵"m" □ ‵"n")]) □ 1)
      := by apply succξ; apply apξ₁; apply lamβ; exact V𝟘
    _ —→ ι (𝟘? 𝟘 [zero: 1 |succ "m": ι (add □ ‵"m" □ 1)])
      := by apply succξ; apply lamβ; exact Value.ofNat 1
    _ —→ 2 := succξ zeroβ
end examples

-- https://plfa.github.io/Lambda/#syntax-of-types
inductive Ty where
| nat
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

-- https://plfa.github.io/Lambda/#contexts
def Context : Type := List (Sym × Ty)

namespace Context
  open Term

  def nil : Context := []
  def extend : Context → Sym → Ty → Context | c, s, ts => ⟨s, ts⟩ :: c

  notation "∅" => nil

  -- The goal is to make `_‚_⦂_` work like an `infixl`.
  -- https://matklad.github.io/2020/04/13/simple-but-powerful-pratt-parsing.html#From-Precedence-to-Binding-Power
  -- `‚` is not a comma! See: <https://www.compart.com/en/unicode/U+201A>
  notation:50 c " ‚ " s:51 " ⦂ " t:51 => extend c s t

  example {Γ : Context} {s : Sym} {ts : Ty} : Context := Γ‚ s ⦂ ts

  -- https://plfa.github.io/Lambda/#lookup-judgment
  /--
  A lookup judgement.
  `Lookup c s ts` means that `s` is of type `ts` by _looking up_ the context `c`.
  -/
  @[aesop safe [constructors, cases]]
  inductive Lookup : Context → Sym → Ty → Type where
  | z : Lookup (Γ‚ x ⦂ t) x t
  | s : x ≠ y → Lookup Γ x t → Lookup (Γ‚ y ⦂ u) x t
  deriving DecidableEq

  notation:40 c " ∋ " s " ⦂ " t:51 => Lookup c s t

  example
  : ∅‚ "x" ⦂ ℕt =⇒ ℕt‚ "y" ⦂ ℕt‚ "z" ⦂ ℕt
  ∋ "x" ⦂ ℕt =⇒ ℕt
  := open Lookup in by
    apply s _; apply s _; apply z; repeat trivial

  -- https://plfa.github.io/Lambda/#lookup-is-functional
  theorem Lookup.functional : Γ ∋ x ⦂ t → Γ ∋ x ⦂ t' → t = t' := by intro
  | z, z => rfl
  | z, s _ e => trivial
  | s _ e, z => trivial
  | s _ e, s _ e' => exact functional e e'

  -- https://plfa.github.io/Lambda/#typing-judgment
  /--
  A general typing judgement.
  `IsTy c t tt` means that `t` can be inferred to be of type `tt` in the context `c`.
  -/
  inductive IsTy : Context → Term → Ty → Type where
  | tyVar : Γ ∋ x ⦂ t → IsTy Γ (‵x) t
  | tyLam : IsTy (Γ‚ x ⦂ t) n u → IsTy Γ (ƛ x : n) (t =⇒ u)
  | tyAp : IsTy Γ l (t =⇒ u) → IsTy Γ x t → IsTy Γ (l □ x) u
  | tyZero : IsTy Γ 𝟘 ℕt
  | tySucc : IsTy Γ n ℕt → IsTy Γ (ι n) ℕt
  | tyCase : IsTy Γ l ℕt → IsTy Γ m t → IsTy (Γ‚ x ⦂ ℕt) n t → IsTy Γ (𝟘? l [zero: m |succ x: n]) t
  | tyMu : IsTy (Γ‚ x ⦂ t) m t → IsTy Γ (μ x : m) t
  deriving DecidableEq

  -- set_option quotPrecheck false in
  notation:40 c " ⊢ " t " ⦂ " tt:51 => IsTy c t tt

  /--
  `NoTy c t` means that `t` cannot be inferred to be any type in the context `c`.
  -/
  abbrev NoTy (c : Context) (t : Term) : Prop := ∀ {tt}, IsEmpty (c ⊢ t ⦂ tt)

  infix:40 " ⊬ " => NoTy

  -- https://github.com/arthurpaulino/lean4-metaprogramming-book/blob/d6a227a63c55bf13d49d443f47c54c7a500ea27b/md/main/tactics.md#tactics-by-macro-expansion
  /--
  `lookup_var` validates the type of a variable by looking it up in the current context.
  This tactic fails when the lookup fails.
  -/
  syntax "lookup_var" : tactic
  macro_rules
  | `(tactic| lookup_var) =>
    `(tactic| apply IsTy.tyVar; repeat (first | apply Lookup.s (by trivial) | exact Lookup.z))

  -- Inform `trivial` of our new tactic.
  macro_rules | `(tactic| trivial) => `(tactic| lookup_var)

  open Context.IsTy

  -- https://plfa.github.io/Lambda/#quiz-2
  def twice_ty : Γ ⊢ (ƛ "s" : ‵"s" $ ‵"s" $ 𝟘) ⦂ ((ℕt =⇒ ℕt) =⇒ ℕt) := by
    apply tyLam; apply tyAp
    · trivial
    · apply tyAp
      · trivial
      · exact tyZero

  def two_ty : Γ ⊢ (ƛ "s" : ‵"s" $ ‵"s" $ 𝟘) □ succC ⦂ ℕt := by
    apply tyAp twice_ty
    · apply tyLam; apply tySucc; trivial

  -- https://plfa.github.io/Lambda/#derivation
  abbrev NatC (t : Ty) : Ty := (t =⇒ t) =⇒ t =⇒ t

  def twoC_ty : Γ ⊢ twoC ⦂ NatC t := by
    apply tyLam; apply tyLam; apply tyAp
    · trivial
    · apply tyAp <;> trivial

  def addTy : Γ ⊢ add ⦂ ℕt =⇒ ℕt =⇒ ℕt := by
    repeat apply_rules [tyAp, tyMu, tyLam, tyCase, tySucc, tyZero] <;> trivial

  def addC_ty : Γ ⊢ addC ⦂ NatC t =⇒ NatC t =⇒ NatC t := by
    repeat apply tyLam <;> try trivial
    · repeat apply tyAp <;> try trivial

  -- https://plfa.github.io/Lambda/#exercise-mul-recommended-1
  def mulTy : Γ ⊢ mul ⦂ ℕt =⇒ ℕt =⇒ ℕt := by
    repeat apply_rules [tyAp, tyMu, tyLam, tyCase, tySucc, tyZero] <;> trivial

  -- https://plfa.github.io/Lambda/#exercise-mul%E1%B6%9C-practice-1
  def mulC_ty : Γ ⊢ mulC ⦂ NatC t =⇒ NatC t =⇒ NatC t := by
    repeat apply tyLam <;> try trivial
    · repeat apply tyAp <;> try trivial
end Context

section examples
  open Term Context Lookup Context.IsTy

  -- https://plfa.github.io/Lambda/#non-examples
  example : ∅ ⊬ 𝟘 □ 1 :=
    ⟨fun | .tyAp hl _ => by cases hl⟩

  abbrev illLam := ƛ "x" : ‵"x" □ ‵"x"

  lemma nty_illLam : ∅ ⊬ illLam :=
    ⟨fun | .tyLam (.tyAp (.tyVar hx) (.tyVar hx')) => Ty.t_to_t'_ne_t _ _ (Lookup.functional hx hx')⟩

  -- https://plfa.github.io/Lambda/#quiz-3
  example : ∅‚ "y" ⦂ ℕt =⇒ ℕt‚ "x" ⦂ ℕt ⊢ ‵"y" □ ‵"x" ⦂ ℕt := by
    apply tyAp <;> trivial

  example : ∅‚ "y" ⦂ ℕt =⇒ ℕt‚ "x" ⦂ ℕt ⊬ ‵"x" □ ‵"y" :=
    ⟨fun | .tyAp (.tyVar hx) _ => by cases hx with | s _ _ => contradiction⟩

  example : ∅‚ "y" ⦂ ℕt =⇒ ℕt ⊢ ƛ "x" : ‵"y" □ ‵"x" ⦂ ℕt =⇒ ℕt := by
    apply tyLam; apply tyAp <;> trivial

  example : ∅‚ "x" ⦂ t ⊬ ‵"x" □ ‵"x" :=
    ⟨fun
    | .tyAp (.tyVar .z) (.tyVar (.s _ _)) => by contradiction
    | .tyAp (.tyVar (.s _ _)) _ => by contradiction⟩

  example
  : ∅‚ "x" ⦂ ℕt =⇒ ℕt‚ "y" ⦂ ℕt =⇒ ℕt
  ⊢ ƛ "z" : (‵"x" $ ‵"y" $ ‵"z") ⦂ ℕt =⇒ ℕt
  := by
    apply tyLam; apply tyAp <;> try trivial
    · apply tyAp <;> trivial
end examples
