module

-- https://plfa.github.io/Denotational/

public import Plfl.Init
public import Plfl.Untyped
public import Plfl.Untyped.Substitution

@[expose] public section

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

namespace Value
  instance instBot : Bot Value where bot := .bot
  instance instMax : Max Value where max := .conj
end Value

namespace Notation
  scoped infixr:70 " ⇾ " => Value.fn
end Notation

open Notation

/-- `Sub` adapts the familiar notion of subset to the `Value` type. -/
inductive Sub : Value → Value → Prop where
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

def sub_of_sub_bot (d : v ⊑ ⊥) : v ⊑ u := d.trans .bot

/-- The `⊔` operation is monotonic with respect to `⊑`. -/
def conj_sub_conj (d₁ : v ⊑ v') (d₂ : w ⊑ w') : v ⊔ w ⊑ v' ⊔ w' :=
  .conjL (.conjR₁ d₁) (.conjR₂ d₂)

def fn_conj_sub_conj_fn : (v ⊔ v') ⇾ (w ⊔ w') ⊑ (v ⇾ w) ⊔ (v' ⇾ w') := calc
  _ ⊑ ((v ⊔ v') ⇾ w) ⊔ ((v ⊔ v') ⇾ w') := .dist
  _ ⊑ (v ⇾ w) ⊔ (v' ⇾ w') := open Sub in by
    apply conj_sub_conj <;> refine .fn ?_ .refl
    · apply conjR₁; rfl
    · apply conjR₂; rfl

-- https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Termination.20of.20head.20induction.20on.20.60ReflTransGen.60/near/375468050
def conj_sub₁ (h : u ⊔ v ⊑ w) : u ⊑ w := by
  generalize hx : u ⊔ v = x at *
  induction h with (subst_vars; try cases hx)
  | conjL h _ => exact h
  | conjR₁ h ih => exact .conjR₁ (ih rfl)
  | conjR₂ h ih => exact .conjR₂ (ih rfl)
  | trans h h' ih => exact .trans (ih rfl) h'

def conj_sub₂ (h : u ⊔ v ⊑ w) : v ⊑ w := by
  generalize hx : u ⊔ v = x at *
  induction h with (subst_vars; try cases hx)
  | conjL _ h => exact h
  | conjR₁ h ih => exact .conjR₁ (ih rfl)
  | conjR₂ h ih => exact .conjR₂ (ih rfl)
  | trans h h' ih => exact .trans (ih rfl) h'

open Untyped (Context)
open Untyped.Notation

-- https://plfa.github.io/Denotational/#environments
/--
An `Env` gives meaning to a term's free vars by mapping vars to values.
-/
abbrev Env (Γ : Context) : Type := ∀ (_ : Γ ∋ ✶), Value

namespace Env
  instance : EmptyCollection (Env ∅) where emptyCollection := nofun

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
  def Sub (γ δ : Env Γ) : Prop := ∀ (x : Γ ∋ ✶), γ x ⊑ δ x
  abbrev conj (γ δ : Env Γ) : Env Γ | x => γ x ⊔ δ x
end Env

namespace Notation
  instance : Bot (Env Γ) where bot _ := ⊥
  instance : Max (Env Γ) where max := Env.conj

  scoped infix:40 " `⊑ " => Env.Sub
end Notation

namespace Env.Sub
  @[refl] def refl : γ `⊑ γ | _ => .refl
  @[simp] def conjR₁ (γ δ : Env Γ) : γ `⊑ (γ ⊔ δ) | _ => .conjR₁ .refl
  @[simp] def conjR₂ (γ δ : Env Γ) : δ `⊑ (γ ⊔ δ) | _ => .conjR₂ .refl

  def ext_le (lt : v ⊑ v') : (γ`‚ v) `⊑ (γ`‚ v')
  | .z => lt
  | .s _ => .refl

  def le_ext (lt : γ `⊑ γ') : (γ`‚ v) `⊑ (γ'`‚ v)
  | .z => .refl
  | .s _ => by apply lt
end Env.Sub

-- https://plfa.github.io/Denotational/#denotational-semantics
/--
`Eval γ m v` means that evaluating the term `m` in the environment `γ` gives `v`.
-/
inductive Eval : Env Γ → (Γ ⊢ ✶) → Value → Prop where
| var : Eval γ (‵ i) (γ i)
| ap : Eval γ l (v ⇾ w) → Eval γ m v → Eval γ (l □ m) w
| fn {v w} : Eval (γ`‚ v) n w → Eval γ (ƛ n) (v ⇾ w)
| bot : Eval γ m ⊥
| conj : Eval γ m v → Eval γ m w → Eval γ m (v ⊔ w)
| sub : Eval γ m v → w ⊑ v → Eval γ m w

namespace Notation
  scoped notation:30 γ " ⊢ " m " ￬ " v:51 => Eval γ m v
end Notation

/--
Relaxation of table lookup in application,
allowing an argument to match an input entry if the latter is less than the former.
-/
def Eval.ap_sub (d : γ ⊢ l ￬ v ⇾ w) (d' : γ ⊢ m ￬ v') (lt : v ⊑ v') : γ ⊢ l □ m ￬ w
:= d.ap <| d'.sub lt

namespace Example
  open Untyped.Term (id delta omega twoC addC)
  open Eval

  -- `id` can be seen as a mapping table for both `⊥ ⇾ ⊥` and `(⊥ ⇾ ⊥) ⇾ (⊥ ⇾ ⊥)`.
  def denot_id₁ : γ ⊢ id ￬ ⊥ ⇾ ⊥ := .fn .var
  def denot_id₂ : γ ⊢ id ￬ (⊥ ⇾ ⊥) ⇾ (⊥ ⇾ ⊥) := .fn .var

  -- `id` also produces a table containing both of the previous tables.
  def denot_id₃ : γ ⊢ id ￬ (⊥ ⇾ ⊥) ⊔ ((⊥ ⇾ ⊥) ⇾ (⊥ ⇾ ⊥)) := denot_id₁.conj denot_id₂

  -- Oops, self application!
  def denot_id_ap_id : `∅ ⊢ id □ id ￬ v ⇾ v := .ap (.fn .var) (.fn .var)

  -- In `def twoC f u := f (f u)`,
  -- `f`'s table must include two entries, both `u ⇾ v` and `v ⇾ w`.
  -- `twoC` then merges those two entries into one: `u ⇾ w`.
  def denot_twoC : `∅ ⊢ twoC ￬ (u ⇾ v ⊔ v ⇾ w) ⇾ u ⇾ w := by
    apply fn; apply fn; apply ap
    · apply sub .var; exact .conjR₂ .refl
    · apply ap
      · apply sub .var; exact .conjR₁ .refl
      · exact .var

  def denot_delta : `∅ ⊢ delta ￬ (v ⇾ w ⊔ v) ⇾ w := by
    apply fn; apply ap (v := v) <;> apply sub .var
    · exact .conjR₁ .refl
    · exact .conjR₂ .refl

  example : `∅ ⊢ omega ￬ ⊥ := by
    apply ap denot_delta; apply conj
    · exact fn (v := ⊥) .bot
    · exact .bot

  def denot_omega : `∅ ⊢ omega ￬ ⊥ := .bot

  -- https://plfa.github.io/Denotational/#exercise-denot-plus%E1%B6%9C-practice

  /-
  For `def addC m n u v := (m u) (n u v)` we have the following mapping table:
  · n u v = w
  · m u w = x
  -/
  def denot_addC
  : let m := u ⇾ w ⇾ x
    let n := u ⇾ v ⇾ w
    `∅ ⊢ addC ￬ m ⇾ n ⇾ u ⇾ v ⇾ x
  := by apply_rules [fn, ap, var]
end Example

-- https://plfa.github.io/Denotational/#denotations-and-denotational-equality
/--
A denotational semantics can be seen as a function from a term
to some relation between `Env`s and `Value`s.
-/
abbrev Denot (Γ : Context) : Type := Env Γ → Value → Prop

/--
`ℰ m` is the instance of `Denot` that corresponds to the `Eval` of `m`.
-/
abbrev ℰ : (Γ ⊢ ✶) → Denot Γ | m, γ, v => γ ⊢ m ￬ v

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

  def ext_sub' (ρ : Rename Γ Δ) (lt : δ ∘ ρ `⊑ γ)
  : (δ`‚ v) ∘ ext ρ `⊑ (γ`‚ v)
  | .z => .refl
  | .s i => lt i

  /-- The result of evaluation is conserved after renaming. -/
  def rename_pres (ρ : Rename Γ Δ) (lt : γ `⊑ δ ∘ ρ) (d : γ ⊢ m ￬ v)
  : δ ⊢ rename ρ m ￬ v
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
  def sub_env (d : γ ⊢ m ￬ v) (lt : γ `⊑ δ) : δ ⊢ m ￬ v := by
    convert rename_pres id lt d; exact rename_id.symm

  lemma up_env (d : (γ`‚ u) ⊢ m ￬ v) (lt : u ⊑ u') : (γ`‚ u') ⊢ m ￬ v := by
    apply sub_env d; exact Env.Sub.ext_le lt
end

-- https://plfa.github.io/Denotational/#exercise-denot-church-recommended
/--
A path consists of `n` edges (`⇾`s) and `n + 1` vertices (`Value`s).
-/
def Value.path : (n : ℕ) → Vector Value (n + 1) → Value
| 0, _ => ⊥
| i + 1, vs => path i vs.pop ⊔ vs[i] ⇾ vs[i + 1]

/--
Returns the denotation of the nth Church numeral for a given path.
-/
def Value.church (n : ℕ) (vs : Vector Value (n + 1)) : Value :=
  path n vs ⇾ vs[0] ⇾ vs[n]

namespace Example
  example : Value.church 0 #v[u] = (⊥ ⇾ u ⇾ u) := rfl
  example : Value.church 1 #v[u, v] = ((⊥ ⊔ u ⇾ v) ⇾ u ⇾ v) := rfl
  example : Value.church 2 #v[u, v, w] = ((⊥ ⊔ u ⇾ v ⊔ v ⇾ w) ⇾ u ⇾ w) := rfl
end Example

section
  open Untyped.Term (church)
  open Eval
  open Env.Sub

  def denot_church {vs} : `∅ ⊢ church n ￬ Value.church n vs := by
    apply_rules [fn]; induction n with
    | zero => exact var
    | succ n r =>
      unfold church.applyN; apply ap
      · apply sub var; simp only [Env.snoc, Value.path]; convert Sub.refl.conjR₂
      · convert sub_env (@r vs.pop) ?_ using 1
        · simp_all only [List.empty_eq, Vector.getElem_pop']
        · intro x; cases x with
          | z =>
            simp_all only [List.empty_eq, Vector.getElem_pop']
            rfl
          | s i =>
            cases i with
            | z => exact .conjR₁ .refl
            | s i' => cases i'
end

-- https://plfa.github.io/Denotational/#inversion-of-the-less-than-relation-for-functions
def Value.Elem (u v : Value) : Prop := match v with
| .conj v w => u.Elem v ∨ u.Elem w
| v => u = v

instance Value.membership : Membership Value Value where mem y x := Value.Elem x y

namespace Value
  def Included (v w : Value) : Prop := ∀ {u}, u ∈ v → u ∈ w

  instance instTrans : Trans Included Included Included where trans := flip (· ∘ ·)
  instance : HasSubset Value where Subset := Included
  instance : Trans Included Subset Included where trans := instTrans.trans
  instance : Trans Subset Subset Included where trans := instTrans.trans

  variable {u v w : Value}
  def Included.fst (s : Included (u ⊔ v) w) : u ⊆ w := s ∘ Or.inl
  def Included.snd (s : Included (u ⊔ v) w) : v ⊆ w := s ∘ Or.inr
end Value

theorem sub_of_elem (e : u ∈ v) : u ⊑ v := by
  induction v with
  | bot => subst e; exact .bot
  | fn v w => subst e; exact .refl
  | conj v w ih ih' =>
    rcases e with h | h
    · exact .conjR₁ (ih h)
    · exact .conjR₂ (ih' h)

theorem sub_of_included (s : u ⊆ v) : u ⊑ v := by induction u with
| bot => exact .bot
| fn => apply sub_of_elem; apply s; rfl
| conj _ _ ih ih' =>
  apply Sub.conjL
  · apply ih; intro _ e; apply s; exact Or.inl e
  · apply ih'; intro _ e; apply s; exact Or.inr e

theorem conj_included_inv {u v w : Value} (s : u ⊔ v ⊆ w) : u ⊆ w ∧ v ⊆ w := by
  constructor <;> (intro _ _; apply s; first | left; trivial | right; trivial)

lemma fn_elem (i : v ⇾ w ⊆ u) : v ⇾ w ∈ u := i rfl

-- https://plfa.github.io/Denotational/#function-values
/-- `IsFn u` means that `u` is a function value. -/
inductive IsFn (u : Value) : Prop where | isFn (h : u = v ⇾ w)

/-- `AllFn v` means that all elements of `v` are function values. -/
def AllFn (v : Value) : Prop := ∀ {u}, u ∈ v → IsFn u

namespace AllFn
  def fst (f : AllFn (u ⊔ v)) : AllFn u := f ∘ Or.inl
  def snd (f : AllFn (u ⊔ v)) : AllFn v := f ∘ Or.inr
end AllFn

lemma not_isFn_bot : ¬ IsFn ⊥ := nofun

lemma elem_of_allFn (f : AllFn u) : ∃ v w, v ⇾ w ∈ u := by induction u with
| bot => exact (not_isFn_bot <| f (u := ⊥) rfl).elim
| fn v w => exists v, w
| conj v w ih _ =>
  -- In fact, the proof is also possible on the `.snd` side.
  -- There is some information loss in this step.
  have ⟨v, w, i⟩ := ih f.fst; exists v, w; exact Or.inl i

-- https://plfa.github.io/Denotational/#domains-and-codomains
/-- Given a set `u` of functions, `u.conjDom` returns the join of their domains. -/
def Value.conjDom : Value → Value
| ⊥ => ⊥
| v ⇾ _ => v
| .conj u v => u.conjDom ⊔ v.conjDom

/-- Given a set `u` of functions, `u.conjCodom` returns the join of their codomains. -/
def Value.conjCodom : Value → Value
| ⊥ => ⊥
| _ ⇾ w => w
| .conj u v => u.conjCodom ⊔ v.conjCodom

/-- Given an element `v ⇾ w` of a set of functions `u`, we know that `v` is in `u.conjDom`. -/
theorem included_conjDom (f : AllFn u) (i : v ⇾ w ∈ u) : v ⊆ u.conjDom := by induction u with
| bot => cases i
| fn => cases i; intro _ hx; exact hx
| conj u u' ih ih' =>
  rcases i with h | h
  · calc v
      _ ⊆ u.conjDom := ih f.fst h
      _ ⊆ (u ⊔ u').conjDom := Or.inl
  · calc v
      _ ⊆ u'.conjDom := ih' f.snd h
      _ ⊆ (u ⊔ u').conjDom := Or.inr

/-- Given a set `u` of identical terms `v ⇾ w`, we know that `u.conjCodom` is included in `w`. -/
theorem conjCodom_included (s : u ⊆ v ⇾ w) : u.conjCodom ⊆ w := by induction u with
| bot =>
  cases s (u := ⊥) rfl
| fn u₁ u₂ =>
  cases s (u := u₁ ⇾ u₂) rfl; intro _ hx; exact hx
| conj _ _ ih ih' =>
  intro x h
  exact Or.elim h (ih s.fst) (ih' s.snd)

/--
We say that `v ⇾ w` factors `u` into `u`, if:
- `u'` contains only functions;
- `u` is included in `u`;
- `u'`'s domain is less than `v`;
- `u'`'s codomain is greater than `w`.
-/
def Factor (u u' v w : Value) : Prop :=
  AllFn u'
∧ u' ⊆ u
∧ u'.conjDom ⊑ v
∧ w ⊑ u'.conjCodom

-- https://plfa.github.io/Denotational/#inversion-of-less-than-for-functions
theorem sub_inv (lt : u ⊑ u') {v w} (i : v ⇾ w ∈ u) : ∃ u'', Factor u' u'' v w :=
  by induction lt generalizing v w with
  | bot => cases i
  | conjL _ _ ih ih' => exact Or.elim i ih ih'
  | conjR₁ _ ih => have ⟨u'', f, s, ss⟩ := ih i; exists u'', f, Or.inl ∘ s
  | conjR₂ _ ih => have ⟨u'', f, s, ss⟩ := ih i; exists u'', f, Or.inr ∘ s
  | fn lt lt' => cases i; rename_i v v' w' w _ _; exists v ⇾ w, (IsFn.isFn ·), id
  | dist =>
    cases i; rename_i v w w'; exists v ⇾ w ⊔ v ⇾ w'
    refine ⟨?_, id, ?_, .refl⟩
    · exact (Or.elim · .isFn .isFn)
    · exact .conjL .refl .refl
  | trans _ _ ih ih' =>
    rename_i u' v' w'; have ⟨u'', f, s, ss⟩ := ih i; have ⟨u'', f, s, ss'⟩ := trans f s ih'
    exists u'', f, s; exact ⟨ss'.1.trans ss.1, ss.2.trans ss'.2⟩
  where
    -- https://plfa.github.io/Denotational/#inversion-of-less-than-for-functions-the-case-for--trans
    trans {u u₁ u₂} (f : AllFn u₁) (s : u₁ ⊆ u) (ih : ∀ {v w}, v ⇾ w ∈ u → ∃ u₃, Factor u₂ u₃ v w)
    : ∃ u₃, Factor u₂ u₃ u₁.conjDom u₁.conjCodom
    := by induction u₁ with
    | bot => exfalso; apply not_isFn_bot; exact f (u := ⊥) rfl
    | fn => apply ih; apply fn_elem; exact s
    | conj _ _ ih ih' =>
      have ⟨s, s'⟩ := conj_included_inv s
      have ⟨u₃, f₃, s, ss⟩ := ih f.fst s; have ⟨u₃', f₃', s', ss'⟩ := ih' f.snd s'
      exists u₃ ⊔ u₃', (Or.elim · f₃ f₃'), (Or.elim · s s')
      exact ⟨conj_sub_conj ss.1 ss'.1, conj_sub_conj ss.2 ss'.2⟩

lemma sub_inv_fn (lt : v ⇾ w ⊑ u)
: ∃ u',
  AllFn u'
∧ u' ⊆ u
∧ (∀ {v' w'}, v' ⇾ w' ∈ u' → v' ⊑ v)
∧ w ⊑ u'.conjCodom
:= by
  have ⟨u', f, s, ss⟩ := sub_inv lt rfl; refine ⟨u', f, s, ?_, ss.2⟩
  introv i; refine .trans ?_ ss.1; exact sub_of_included <| included_conjDom f i

lemma fn_conj_fn_inv (lt : v ⇾ w ⊑ v' ⇾ w') : v' ⊑ v ∧ w ⊑ w' := by
  have ⟨_, f, s, ss⟩ := sub_inv_fn lt; have ⟨u, u', i⟩ := elem_of_allFn f
  cases s i; exists ss.1 i; apply ss.2.trans; exact sub_of_included <| conjCodom_included s
