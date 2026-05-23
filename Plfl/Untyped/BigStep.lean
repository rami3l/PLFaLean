module

-- https://plfa.github.io/BigStep/

public import Plfl.Init
public import Plfl.Untyped
public import Plfl.Untyped.Substitution

@[expose] public section

namespace BigStep

open Untyped (Context)
open Untyped.Notation
open Substitution (Subst ids sub_ids)

-- https://plfa.github.io/BigStep/#environments
/--
A closure in call-by-name is a term paired with its environment.
-/
inductive Clos : Type where
| clos : ∀ {Γ}, (m : Γ ⊢ ✶) → (γ : (Γ ∋ ✶) → Clos) → Clos

/--
An environment in call-by-name is a mapping from variables to closures.
-/
abbrev ClosEnv (Γ : Context) := (Γ ∋ ✶) → Clos

def ClosEnv.empty : ClosEnv ∅ := nofun

instance ClosEnv.instEmptyCollection : EmptyCollection (ClosEnv ∅) where
  emptyCollection := empty

def ClosEnv.tail (γ : ClosEnv Γ) (c : Clos) : ClosEnv (Γ‚ ✶)
| .z => c
| .s i => γ i

namespace Notation
  -- `‚` is not a comma! See: <https://www.compart.com/en/unicode/U+201A>
  scoped infixl:50 "‚' " => ClosEnv.tail
end Notation

open Notation

inductive Eval : ClosEnv Γ → (Γ ⊢ ✶) → Clos → Prop where
| var : γ i = .clos m δ → Eval δ m v → Eval γ (‵ i) v
| lam : Eval γ (ƛ m) (.clos (ƛ m) γ)
| ap : Eval γ l (.clos (ƛ n) δ) → Eval (δ‚' .clos m γ) n v → Eval γ (l □ m) v

namespace Notation
  scoped notation:40 γ " ⊢ " m " ⇓ " c:51 => Eval γ m c
end Notation

-- https://plfa.github.io/BigStep/#exercise-big-step-eg-practice
example
: γ ⊢ (ƛ ƛ #1) $ (ƛ #0 □ #0) $ (ƛ #0 □ #0)
-- (λ x y => x) ((λ f => f f) (λ f => f f)) ⇓ (λ y => ((λ f => f f) (λ f => f f)))
⇓ .clos (ƛ #1) (γ‚' .clos ((ƛ #0 □ #0) $ (ƛ #0 □ #0)) γ)
:= .ap .lam .lam

-- https://plfa.github.io/BigStep/#the-big-step-semantics-is-deterministic
theorem Eval.determ (e : γ ⊢ m ⇓ v) (e' : γ ⊢ m ⇓ v') : v = v' := by
  induction e generalizing v' with cases e'
  | lam => rfl
  | var h _ ih =>
    rename_i h' e'; injection h.symm.trans h'
    rename_i h hh hh'; subst h; rw [←hh.eq, ←hh'.eq] at e'; exact ih e'
  | ap _ _ ih ih₁ =>
    rename_i e' e₁'; apply ih₁; injection ih e'
    subst_vars; rename_i h; injection h; subst_vars; exact e₁'

-- https://plfa.github.io/BigStep/#big-step-evaluation-implies-beta-reduction-to-a-lambda
noncomputable def Clos.Equiv : Clos → (∅ ⊢ ✶) → Prop
| .clos (Γ := Γ) m γ, n =>
  ∃ (σ : Subst Γ ∅), (∀ i, Clos.Equiv (γ i) (σ i)) ∧ (n = ⟪σ⟫ m)

abbrev ClosEnv.Equiv (γ : ClosEnv Γ) (σ : Subst Γ ∅) : Prop :=
  ∀ i, Clos.Equiv (γ i) (σ i)

namespace Notation
  -- The default precedence in Agda is 20.
  -- See: <https://agda.readthedocs.io/en/v2.6.1/language/mixfix-operators.html#precedence>
  scoped infix:20 " ~~ " => Clos.Equiv
  scoped infix:20 " ~~ₑ " => ClosEnv.Equiv
end Notation

section
  open Untyped.Subst
  open Substitution

  @[simp] lemma ClosEnv.empty_equiv_ids : ∅ ~~ₑ ids := nofun

  abbrev ext_subst (σ : Subst Γ Δ) (n : Δ ⊢ ✶) : Subst (Γ‚ ✶) Δ := (·⟦n⟧) ∘ exts σ

  lemma subst₁σ_exts {σ : Subst Γ Δ} {m : Δ ⊢ b} {i : Γ ∋ ✶}
  : (ext_subst σ m) (.s i) = σ i
  := by simp only [subst₁σ_exts_cons]; simp_all only [cons]

  theorem ClosEnv.ext {γ : ClosEnv Γ} {σ : Subst Γ ∅} {n : ∅ ⊢ ✶}
  (ee : γ ~~ₑ σ) (e : v ~~ n) : (γ‚' v ~~ₑ ext_subst σ n)
  := by intro
  | .z => exact e
  | .s i => simp only [subst₁σ_exts]; exact ee i

  theorem Eval.clos_env_equiv {γ : ClosEnv Γ} {σ : Subst Γ ∅} {m : Γ ⊢ ✶}
  (ev : γ ⊢ m ⇓ v) (ee : γ ~~ₑ σ)
  : ∃ (n : ∅ ⊢ ✶), (⟪σ⟫ m —↠ n) ∧ (v ~~ n)
  := open Untyped.Reduce in by induction ev with
  | lam => rename_i n; exists ⟪σ⟫ (ƛ n), by rfl, σ, ee
  | var h _ev ih =>
    rename_i i; have := ee i; rw [h] at this; have ⟨τ, eeτ, hτ⟩ := this
    have ⟨n, rn, en⟩ := ih eeτ; rw [←hτ] at rn; exists n, rn
  | ap _ev _ev' ih ih' =>
    have ⟨n, rn, τ, eeτ, hτ⟩ := ih ee; subst hτ
    have ⟨n', rn', en'⟩ := ih' <| ClosEnv.ext eeτ ⟨σ, ee, rfl⟩
    refine ⟨n', ?_, en'⟩; simp only [sub_ap]; rename_i n _ m _
    apply (ap_congr₁ rn).trans; unfold ext_subst at rn'
    calc ⟪τ⟫ (ƛ n) □ ⟪σ⟫ m
      _ = (ƛ (⟪exts τ⟫ n)) □ ⟪σ⟫ m := rfl
      _ —→ ⟪subst₁σ (⟪σ⟫ m)⟫ (⟪exts τ⟫ n) := lamβ
      _ = ⟪⟪subst₁σ (⟪σ⟫ m)⟫ ∘ exts τ⟫ n := Substitution.sub_sub
      _ —↠ n' := rn'

  /--
  If call-by-name can produce a value,
  then the program can be reduced to a λ-abstraction via β-rules.
  -/
  theorem Eval.reduce_of_cbn {m : ∅ ⊢ ✶} {δ : ClosEnv Δ} {n' : Δ‚ ✶ ⊢ ✶}
  (ev : ∅ ⊢ m ⇓ .clos (ƛ n') δ)
  : ∃ (n : ∅‚ ✶ ⊢ ✶), m —↠ ƛ n
  := by
    have ⟨n, rn, σ, _, h⟩ := ev.clos_env_equiv ClosEnv.empty_equiv_ids
    subst h; rw [sub_ids] at rn; exists ⟪exts σ⟫ n'
end

-- https://plfa.github.io/BigStep/#exercise-big-alt-implies-multi-practice
namespace BySubst

-- https://github.com/L-TChen/ModalTypeTheory/blob/a4d3cf67236716fa324daa3e5a929f38a33c39e9/src/STLC/BigStep.agda#L96-L121
-- https://www.cs.cornell.edu/courses/cs6110/2014sp/Handouts/Sestoft.pdf
inductive Eval : (Γ ⊢ ✶) → (Γ ⊢ ✶) → Prop where
-- Hmmm, it's all ƛ's after all?
| lam : ∀ {n : ∅‚ ✶ ⊢ ✶}, Eval (ƛ n) (ƛ n)
| ap : Eval l (ƛ m) → Eval (m⟦n⟧) v → Eval (l □ n) v

namespace Notation
  scoped infix:50 " ⇓' "=> Eval
end Notation

open Notation

theorem Eval.determ : m ⇓' v → m ⇓' v' → v = v' := by intro
| .lam, .lam => rfl
| .ap mc mc₁, .ap mc' mc₁' =>
  have := mc.determ mc'; injection this; subst_vars; exact mc₁.determ mc₁'

open Untyped.Reduce
open Untyped.Subst

/--
If call-by-name can produce a value,
then the program can be reduced to a λ-abstraction via β-rules.
-/
theorem Eval.reduce_of_cbn {n : Γ‚ ✶ ⊢ ✶} (ev : m ⇓' (ƛ n)) : m —↠ ƛ n := by
  generalize hx : (ƛ n) = x, hx' : m = x' at *
  induction ev with
  | lam => rfl
  | ap _evl evmn' ih ih' => subst_vars; rename_i l m n'; calc l □ n'
      _ —↠ (ƛ m) □ n' := ap_congr₁ <| ih rfl rfl
      _ —→ m⟦n'⟧ := lamβ
      _ —↠ (ƛ n) := ih' rfl rfl
