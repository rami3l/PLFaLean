-- https://plfa.github.io/Soundness/

import Plfl.Init
import Plfl.Untyped.Denotational.Compositional

namespace Soundness

open Untyped Untyped.Notation
open Untyped.Subst
open Substitution (Rename Subst)
open Denotational Denotational.Notation
open Compositional Compositional.Notation

-- https://plfa.github.io/Soundness/#simultaneous-substitution-preserves-denotations
namespace Env
  /--
  `Eval δ σ γ` means that for every variable `i`,
  `σ i` results in the same value as the one for `i` in the original environment `γ`.
  -/
  abbrev Eval (δ : Env Δ) (σ : Subst Γ Δ) (γ : Env Γ) : Prop := ∀ (i : Γ ∋ ✶), δ ⊢ σ i ￬ γ i
end Env

namespace Notation
  scoped notation:30 δ " `⊢ " σ " ￬ " γ:51 => Env.Eval δ σ γ
end Notation

open Notation

section
  variable {γ : Env Γ} {δ : Env Δ}

  lemma subst_ext (σ : Subst Γ Δ) (d : δ `⊢ σ ￬ γ) : δ`‚ v `⊢ exts σ ￬ (γ`‚ v)
  | .z => .var
  | .s i => rename_pres .s (λ _ => .refl) (d i)

  /-- The result of evaluation is conserved after simultaneous substitution. -/
  theorem subst_pres (σ : Subst Γ Δ) (s : δ `⊢ σ ￬ γ) (d : γ ⊢ m ￬ v)
  : δ ⊢ subst σ m ￬ v
  := by induction d generalizing Δ with
  | var => apply s
  | ap _ _ ih ih'=> exact (ih σ s).ap (ih' σ s)
  | fn _ ih => refine .fn ?_; apply ih (exts σ); exact subst_ext σ s
  | bot => exact .bot
  | conj _ _ ih ih' => exact (ih σ s).conj (ih' σ s)
  | sub _ lt ih => exact (ih σ s).sub lt

  -- https://plfa.github.io/Soundness/#single-substitution-preserves-denotations
  /-- The result of evaluation is conserved after single substitution. -/
  theorem subst₁_pres (dn : γ`‚ v ⊢ n ￬ w) (dm : γ ⊢ m ￬ v) : γ ⊢ n⟦m⟧ ￬ w
  := subst_pres (σ := subst₁σ m) (γ := γ`‚ v) (δ := γ) (λ | .z => dm | .s _ => .var) dn

  -- https://plfa.github.io/Soundness/#reduction-preserves-denotations
  theorem reduce_pres (d : γ ⊢ m ￬ v) (r : m —→ n) : γ ⊢ n ￬ v := by induction d with
  | var => contradiction
  | bot => exact .bot
  | fn _ ih => cases r with | lamζ r => exact (ih r).fn
  | conj _ _ ih ih' => exact (ih r).conj (ih' r)
  | sub _ lt ih => exact (ih r).sub lt
  | ap d d' ih ih' => cases r with
    | apξ₁ r => exact (ih r).ap d'
    | apξ₂ r => exact d.ap (ih' r)
    | lamβ => exact subst₁_pres (lam_inv d) d'

  -- https://plfa.github.io/Soundness/#renaming-reflects-meaning
  theorem rename_reflect {ρ : Rename Γ Δ} (lt : δ ∘ ρ `⊑ γ) (d : δ ⊢ rename ρ m ￬ v)
  : γ ⊢ m ￬ v
  := by
    generalize hx : rename ρ m = x at *
    induction d generalizing Γ with
    | bot => exact .bot
    | var => cases m with (injection hx; try subst_vars)
      | var i => exact .sub .var <| (var_inv .var).trans (lt i)
    | ap _ _ ih ih' => cases m with injection hx
      | ap => rename_i hx hx'; exact (ih lt hx).ap (ih' lt hx')
    | fn _ ih => cases m with injection hx
      | lam => refine .fn ?_; apply ih (ρ := ext ρ) (ext_sub' ρ lt); trivial
    | conj _ _ ih ih' => exact (ih lt hx).conj (ih' lt hx)
    | sub _ lt' ih => exact (ih lt hx).sub lt'

  theorem rename_shift_reflect (d : γ`‚ u ⊢ shift m ￬ v) : γ ⊢ m ￬ v :=
    rename_reflect (by rfl) d
end

section
  -- https://plfa.github.io/Soundness/#substitution-reflects-denotations-the-variable-case
  /-- `const` is an `Env` with a single non-trivial mapping entry: from `i` to `v`. -/
  def Env.const (i : Γ ∋ ✶) (v : Value) : Env Γ | j => if i = j then v else ⊥

  variable {γ δ : Env Δ}

  lemma subst_reflect_var {i : Γ ∋ ✶} {σ : Subst Γ Δ} (d : γ ⊢ σ i ￬ v)
  : ∃ (δ : Env Γ), (γ `⊢ σ ￬ δ) ∧ (δ ⊢ ‵ i ￬ v)
  := by
    exists Env.const i v; unfold Env.const; constructor
    · intro j; by_cases h : i = j <;> simp only [h] at *
      · exact d
      · exact .bot
    · convert Eval.var; simp only [ite_true]

  variable {γ₁ γ₂ : Env Γ} {σ : Subst Γ Δ}

  -- https://plfa.github.io/Soundness/#substitutions-and-environment-construction
  lemma subst_bot : γ `⊢ σ ￬ ⊥ | _ => .bot

  lemma subst_conj (d₁ : γ `⊢ σ ￬ γ₁) (d₂ : γ `⊢ σ ￬ γ₂) : γ `⊢ σ ￬ γ₁ ⊔ γ₂
  | i => (d₁ i).conj (d₂ i)
end

-- https://plfa.github.io/Soundness/#simultaneous-substitution-reflects-denotations
/-- Simultaneous substitution reflects denotations. -/
theorem subst_reflect {σ : Subst Γ Δ} (d : δ ⊢ l ￬ v) (h : ⟪σ⟫ m = l)
: ∃ (γ : Env Γ), (δ `⊢ σ ￬ γ) ∧ (γ ⊢ m ￬ v)
:= by
  induction d generalizing Γ with
  | bot => exists ⊥; exact ⟨subst_bot, .bot⟩
  | var => cases m with try contradiction
    | var j => apply subst_reflect_var; convert Eval.var
  | ap d d' ih ih' => rename_i l' _ _ m'; cases m with try contradiction
    | var => apply subst_reflect_var; convert d.ap d'
    | ap =>
      injection h; rename_i h h'
      let ⟨γ, dγ, dm⟩ := ih h; let ⟨γ', dγ', dm'⟩ := ih' h'; exists γ ⊔ γ'; constructor
      · exact subst_conj dγ dγ'
      · exact (sub_env dm <| Env.Sub.conjR₁ γ γ').ap (sub_env dm' <| Env.Sub.conjR₂ γ γ')
  | fn d ih => cases m with try contradiction
    | var => apply subst_reflect_var; convert d.fn
    | lam =>
      injection h; rename_i h; let ⟨γ, dγ, dm⟩ := ih h; exists γ.init; constructor
      · intro i; exact rename_shift_reflect <| dγ i.s
      · rw [Env.init_last γ] at dm; refine .fn (up_env dm ?_); exact var_inv <| dγ .z
  | conj _ _ ih ih' =>
    let ⟨γ, dγ, dm⟩ := ih h; let ⟨γ', dγ', dm'⟩ := ih' h; exists γ ⊔ γ'; constructor
    · exact subst_conj dγ dγ'
    · exact (sub_env dm <| Env.Sub.conjR₁ γ γ').conj (sub_env dm' <| Env.Sub.conjR₂ γ γ')
  | sub _ lt' ih => let ⟨γ, dγ, dm⟩ := ih h; exact ⟨γ, dγ, dm.sub lt'⟩

-- https://plfa.github.io/Soundness/#single-substitution-reflects-denotations
lemma subst₁σ_reflect {δ : Env Δ} {γ : Env (Δ‚ ✶)} (d : δ `⊢ subst₁σ m ￬ γ)
: ∃ w, (γ `⊑ δ`‚ w) ∧ (δ ⊢ m ￬ w)
:= by
  exists γ.last; constructor
  · intro
    | .z => rfl
    | .s i => apply var_inv (d i.s)
  · exact d .z

/-- Single substitution reflects denotations. -/
theorem subst₁_reflect {δ : Env Δ} (d : δ ⊢ n⟦m⟧ ￬ v) : ∃ w, (δ ⊢ m ￬ w) ∧ (δ`‚ w ⊢ n ￬ v)
:= by
  have ⟨γ, dγ, dn⟩ := subst_reflect d rfl; have ⟨w, ltw, dw⟩ := subst₁σ_reflect dγ
  exists w, dw; exact sub_env dn ltw

-- https://plfa.github.io/Soundness/#reduction-reflects-denotations-1
theorem reduce_reflect {γ : Env Γ} {m n : Γ ⊢ a} (d : γ ⊢ n ￬ v) (r : m —→ n) : γ ⊢ m ￬ v := by
  induction r generalizing v with
  | lamβ =>
    rename_i n u; generalize hx : n⟦u⟧ = x at *
    induction d with
    | var => apply beta; rw [hx]; exact .var
    | ap d d' => apply beta; rw [hx]; exact d.ap d'
    | fn d => apply beta; rw [hx]; exact d.fn
    | bot => exact .bot
    | conj _ _ ih ih' => exact (ih hx).conj (ih' hx)
    | sub _ lt ih => exact (ih hx).sub lt
  | lamζ r ihᵣ =>
    rename_i _ n'; generalize hx : (ƛ n') = x at *
    induction d with try contradiction
    | fn d ih => injection hx; subst_vars; exact (ihᵣ <| lam_inv d.fn).fn
    | bot => exact .bot
    | conj _ _ ih ih' => exact (ih r ihᵣ hx).conj (ih' r ihᵣ hx)
    | sub _ lt ih => exact (ih r ihᵣ hx).sub lt
  | apξ₁ r ihᵣ =>
    rename_i l m; generalize hx : l □ m = x at *
    induction d with try contradiction
    | ap d d' _ _ => injection hx; subst_vars; exact (ihᵣ d).ap d'
    | bot => exact .bot
    | conj _ _ ih ih' => exact (ih r ihᵣ hx).conj (ih' r ihᵣ hx)
    | sub _ lt ih => exact (ih r ihᵣ hx).sub lt
  | apξ₂ r ihᵣ =>
    rename_i m l; generalize hx : l □ m = x at *
    induction d with try contradiction
    | ap d d' _ _ => injection hx; subst_vars; exact d.ap <| ihᵣ d'
    | bot => exact .bot
    | conj _ _ ih ih' => exact (ih r ihᵣ hx).conj (ih' r ihᵣ hx)
    | sub _ lt ih => exact (ih r ihᵣ hx).sub lt
  where
    beta {Γ m n v} {γ : Env Γ} (d : γ ⊢ n⟦m⟧ ￬ v) : γ ⊢ (ƛ n) □ m ￬ v := by
      let ⟨v, dm, dn⟩ := subst₁_reflect d; exact dn.fn.ap dm

-- https://plfa.github.io/Soundness/#reduction-implies-denotational-equality
theorem reduce_eq (r : m —→ n) : ℰ m = ℰ n := by
  ext; exact ⟨(reduce_pres · r), (reduce_reflect · r)⟩

theorem soundness (rs : m —↠ ƛ n) : ℰ m = ℰ (ƛ n) := by
  induction rs using Relation.ReflTransGen.head_induction_on with
  | refl => rfl
  | head r _ ih => convert ih using 1; exact reduce_eq r
