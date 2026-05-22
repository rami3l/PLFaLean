-- https://plfa.github.io/Adequacy/

import Plfl.Init
import Plfl.Untyped.BigStep
import Plfl.Untyped.Denotational.Soundness

namespace Adequacy

open Untyped Untyped.Notation
open Untyped.Subst
open BigStep (Clos ClosEnv Eval.reduce_of_cbn)
open BigStep.Notation
open Denotational Denotational.Notation
open Soundness (soundness)

-- https://plfa.github.io/Adequacy/#the-property-of-being-greater-or-equal-to-a-function
/-- `GtFn u` means that it is "greater than" a certain function value. -/
def GtFn (u : Value) : Prop := ∃ v w, v ⇾ w ⊑ u

/-- If `u` is greater than a function, then an even greater value `u'` is too. -/
lemma GtFn.sub (gt : GtFn u) (lt : u ⊑ u') : GtFn u' :=
  let ⟨v, w, lt'⟩ := gt; ⟨v, w, lt'.trans lt⟩

/-- `⊥` is never greater than a function. -/
lemma not_gtFn_bot : ¬ GtFn ⊥
| ⟨v, w, lt⟩ => by
  have ⟨_, f, s, _⟩ := sub_inv_fn lt; have ⟨_, _, i⟩ := elem_of_allFn f; cases s i

/-- If the join of two values is greater than a function, then at least one of them is too. -/
lemma GtFn.conj (gt : GtFn (u ⊔ v)) : GtFn u ∨ GtFn v := by
  have ⟨_, _, lt⟩ := gt; have ⟨_, f, s, _⟩ := sub_inv_fn lt; have ⟨v, w, i⟩ := elem_of_allFn f
  refine Or.imp ?inl ?inr <| s i <;> (intro i'; exists v, w; exact sub_of_elem i')

/-- If neither of the two values is greater than a function, then nor is their join. -/
lemma not_gtFn_conj (ngt : ¬ GtFn u) (ngt' : ¬ GtFn v) : ¬ GtFn (u ⊔ v) := by
  intro gtuv; exfalso; exact gtuv.conj |>.elim ngt ngt'

/--
If the join of two values is not greater than a function,
then neither of them is individually.
-/
lemma not_gtFn_conj_inv (ngtuv : ¬ GtFn (u ⊔ v)) : ¬ GtFn u ∧ ¬ GtFn v := by
  by_contra h; simp_all only [not_and, not_not]
  have ngtu := ngtuv ∘ (GtFn.sub · <| .conjR₁ .refl)
  have ngtv := ngtuv ∘ (GtFn.sub · <| .conjR₂ .refl)
  exact h ngtu |> ngtv

lemma not_gtFn_conj_iff : (¬ GtFn u ∧ ¬ GtFn v) ↔ ¬ GtFn (u ⊔ v) :=
  ⟨(λ nn => not_gtFn_conj nn.1 nn.2), not_gtFn_conj_inv⟩

instance GtFn.dec {v} : Decidable (GtFn v) := by match v with
| ⊥ => left; exact not_gtFn_bot
| v ⇾ w => right; exists v, w
| .conj u v => cases @dec u with
  | isTrue h => right; have ⟨v, w, lt⟩ := h; exists v, w; exact lt.conjR₁
  | isFalse h => cases @dec v with
    | isTrue h' => right; have ⟨v, w, lt⟩ := h'; exists v, w; exact lt.conjR₂
    | isFalse h' => left; exact not_gtFn_conj h h'

-- https://plfa.github.io/Adequacy/#relating-values-to-closures
mutual
  /--
  `𝕍 v c` will hold when:
  - `c` is in WHNF (i.e. is a λ-abstraction);
  - `v` is a function;
  - `c`'s body evaluates according to `v`.
  -/
  def 𝕍 : Value → Clos → Prop
  | _, .clos (‵ _) _ => ⊥
  | _, .clos (_ □ _) _ => ⊥
  | ⊥, .clos (ƛ _) _ => ⊤
  | vw@(v ⇾ w), .clos (ƛ n) γ =>
    have : sizeOf w < sizeOf vw := by subst_vars; simp
    ∀ {c}, 𝔼 v c → GtFn w → ∃ c', (γ‚' c ⊢ n ⇓ c') ∧ 𝕍 w c'
  | uv@(.conj u v), c@(.clos (ƛ _) _) =>
    have : sizeOf v < sizeOf uv := by subst_vars; simp
    𝕍 u c ∧ 𝕍 v c

  /--
  `𝔼 v c` will hold when:
  - `v` is greater than a function value;
  - `c` evaluates to a closure `c'` in WHNF;
  - `𝕍 v c` holds.
  -/
  def 𝔼 (v : Value) : Clos → Prop | .clos m γ' => GtFn v → ∃ c, (γ' ⊢ m ⇓ c) ∧ 𝕍 v c
end

/-- `𝔾` relates `γ` to `γ'` if the corresponding values and closures are related by `𝔼` -/
def 𝔾 (γ : Env Γ) (γ' : ClosEnv Γ) : Prop := ∀ {i : Γ ∋ ✶}, 𝔼 (γ i) (γ' i)

def 𝔾.empty : 𝔾 `∅ ∅ := nofun

def 𝔾.ext (g : 𝔾 γ γ') (e : 𝔼 v c) : 𝔾 (γ`‚ v) (γ'‚' c) := by unfold 𝔾; intro
| .z => exact e
| .s _ => exact g

/-- The proof of a term being in Weak-Head Normal Form. -/
def WHNF (t : Γ ⊢ a) : Prop := ∃ n : Γ‚ ✶ ⊢ ✶, t = (ƛ n)

/-- A closure in a 𝕍 relation must be in WHNF. -/
lemma WHNF.of_𝕍 (vc : 𝕍 v (.clos m γ)) : WHNF m := by
  cases m with (try simp [𝕍] at vc; try contradiction) | lam n => exists n

lemma 𝕍.conj (uc : 𝕍 u c) (vc : 𝕍 v c) : 𝕍 (u ⊔ v) c := by
  let .clos m γ := c; cases m with (try simp [𝕍] at *; try contradiction)
  | lam => unfold 𝕍; exact ⟨uc, vc⟩

lemma 𝕍.of_not_gtFn (nf : ¬ GtFn v) : 𝕍 v (.clos (ƛ n) γ') := by induction v with unfold 𝕍
| bot => trivial
| fn v w => exfalso; apply nf; exists v, w
| conj _ _ ih ih' => exact not_gtFn_conj_inv nf |>.imp ih ih'

lemma 𝕍.sub {v v'} (vvc : 𝕍 v c) (lt : v' ⊑ v) : 𝕍 v' c := by
  let .clos m γ := c; cases m with (try simp [𝕍] at *; try contradiction) | lam m =>
    rename_i Γ; induction lt generalizing Γ with
    | bot => unfold 𝕍; trivial
    | conjL _ _ ih ih' => unfold 𝕍; exact ⟨ih _ _ _ vvc, ih' _ _ _ vvc⟩
    | conjR₁ _ ih => apply ih; unfold 𝕍 at vvc; exact vvc.1
    | conjR₂ _ ih => apply ih; unfold 𝕍 at vvc; exact vvc.2
    | trans _ _ ih ih' => apply_rules [ih, ih']
    | @fn v₂ v₁ w₁ w₂ lt lt' ih ih' =>
      unfold 𝕍 at vvc ⊢; intro _ c evc gtw
      have : 𝔼 v₂ c := by
        -- HACK: Broken mutual induction with `𝔼.sub` here.
        cases c; simp only [𝔼] at *; intro gtv'
        have ⟨c, ec, vv₁c⟩ := evc <| gtv'.sub lt; exists c, ec
        cases c with | clos m γ => have ⟨m', h'⟩ := WHNF.of_𝕍 vv₁c; subst h'; exact ih _ γ _ vv₁c
      have ⟨c', ec', vw₂c'⟩ := vvc this (gtw.sub lt'); exists c', ec'
      let .clos _ _ := c'; have ⟨m', h'⟩ := WHNF.of_𝕍 vw₂c'; subst h'; exact ih' _ _ _ vw₂c'
    | @dist v₁ w₁ w₂ =>
      unfold 𝕍 at vvc ⊢; intro _ c ev₁c gt; unfold 𝕍 at vvc
      by_cases hgt₁ : GtFn w₁ <;> by_cases hgt₂ : GtFn w₂
      · have ⟨c₁, ec₁, vw₁⟩ := vvc.1 ev₁c hgt₁; have ⟨c₂, ec₂, vw₂⟩ := vvc.2 ev₁c hgt₂
        exists c₁, ec₁; cases c₁; have ⟨m', h'⟩ := WHNF.of_𝕍 vw₁; subst h'; unfold 𝕍
        exists vw₁; rwa [←ec₁.determ ec₂] at vw₂
      · have ⟨.clos l γ₁, ec₁, vw₁⟩ := vvc.1 ev₁c hgt₁; exists .clos l γ₁, ec₁
        have ⟨m', h'⟩ := WHNF.of_𝕍 vw₁; subst h'; apply vw₁.conj; exact of_not_gtFn hgt₂
      · have ⟨.clos l γ₂, ec₂, vw₂⟩ := vvc.2 ev₁c hgt₂; exists .clos l γ₂, ec₂
        have ⟨m', h'⟩ := WHNF.of_𝕍 vw₂; subst h'; apply (𝕍.conj · vw₂); exact of_not_gtFn hgt₁
      · cases gt.conj <;> contradiction

lemma 𝔼.sub (evc : 𝔼 v c) (lt : v' ⊑ v) : 𝔼 v' c := by
  let .clos m γ := c; simp only [𝔼] at *; intro gtv'
  have ⟨c, ec, vvc⟩ := evc <| gtv'.sub lt; exists c, ec; exact vvc.sub lt

-- https://plfa.github.io/Adequacy/#programs-with-function-denotation-terminate-via-call-by-name
theorem 𝔼.of_eval {Γ} {γ : Env Γ} {γ' : ClosEnv Γ} {m : Γ ⊢ ✶} (g : 𝔾 γ γ') (d : γ ⊢ m ￬ v)
: 𝔼 v (.clos m γ')
:= by
  generalize hx : v = x at *
  induction d generalizing v with (unfold 𝔼; intro gt)
  | @var _ γ i =>
    unfold 𝔾 𝔼 at g; have := @g i
    generalize h_clos : γ' i = ci at this
    cases ci with | clos m' δ' =>
      have ⟨c, em', vγi⟩ := this gt; refine ⟨c, ?_, vγi⟩
      exact BigStep.Eval.var h_clos em'
  | @ap _ _ _ _ _ m _ _ ih ih' =>
    unfold 𝔼 at ih; have ⟨.clos l' δ, e_cl', v_cl'⟩ := ih g rfl ⟨_, _, .refl⟩
    have ⟨m', h'⟩ := WHNF.of_𝕍 v_cl'; subst h'; unfold 𝕍 at v_cl'
    have ⟨c', em'c', v_c'⟩ := @v_cl' (.clos m γ') (ih' g rfl) gt; exact ⟨c', e_cl'.ap em'c', v_c'⟩
  | @fn _ _ n _ _ _ ih =>
    unfold 𝔼 at ih; exists .clos (ƛ n) γ', .lam; unfold 𝕍; intro _ c ev₁c; exact ih (g.ext ev₁c) rfl
  | bot => subst_vars; exfalso; exact not_gtFn_bot gt
  | sub _ lt ih =>
    unfold 𝔼 at ih; have ⟨c, e_c, v_c⟩ := ih g rfl <| gt.sub lt; exact ⟨c, e_c, v_c.sub lt⟩
  | @conj _ _ _ w w' _ _ ih ih' =>
    by_cases hgt : GtFn w <;> by_cases hgt' : GtFn w'
    · unfold 𝔼 at ih ih'; have ⟨c, e_c, vwc⟩ := ih g rfl hgt; exists c, e_c
      have ⟨_, e_c', vw'c⟩ := ih' g rfl hgt'; rw [←e_c.determ e_c'] at vw'c; exact vwc.conj vw'c
    · unfold 𝔼 at ih; have ⟨.clos l γ, e_cl, vw⟩ := ih g rfl hgt; exists .clos l γ, e_cl
      have ⟨m', h'⟩ := WHNF.of_𝕍 vw; subst h'; apply vw.conj; exact 𝕍.of_not_gtFn hgt'
    · unfold 𝔼 at ih'; have ⟨.clos l' γ', e_cl', vw'⟩ := ih' g rfl hgt'; exists .clos l' γ', e_cl'
      have ⟨m', h'⟩ := WHNF.of_𝕍 vw'; subst h'; apply (𝕍.conj · vw'); exact 𝕍.of_not_gtFn hgt
    · cases gt.conj <;> contradiction

section
  variable {m : ∅ ⊢ ✶} {n : ∅‚ ✶ ⊢ ✶}

  -- https://plfa.github.io/Adequacy/#proof-of-denotational-adequacy
  theorem Eval.to_big_step (he : ℰ m = ℰ (ƛ n))
  : ∃ (Γ : Context) (n' : Γ‚ ✶ ⊢ ✶) (γ : ClosEnv Γ), ClosEnv.empty ⊢ m ⇓ .clos (ƛ n') γ
  := by
    have : ℰ (ƛ n) ∅ (⊥ ⇾ ⊥) := by apply_rules [Eval.fn, Eval.bot]
    rw [←he] at this; have := 𝔼.of_eval 𝔾.empty this; unfold 𝔼 at this
    have ⟨.clos _ γ, emc, v_cl⟩ := this ⟨_, _, .refl⟩
    have ⟨m', h'⟩ := WHNF.of_𝕍 v_cl; subst h'; exists _, m', γ

  theorem adequacy (he : ℰ m = ℰ (ƛ n)) : ∃ n', m —↠ ƛ n' := by
    have ⟨_, _, _, e⟩ := Eval.to_big_step he; exact e.reduce_of_cbn

  -- https://plfa.github.io/Adequacy/#call-by-name-is-equivalent-to-beta-reduction
  /--
  If the program can be reduced to a λ-abstraction via β-rules,
  then call-by-name can produce a value.
  -/
  theorem Eval.reduce_to_cbn (rs : m —↠ ƛ n)
  : ∃ (Δ : Context) (n' : Δ‚ ✶ ⊢ ✶) (δ : ClosEnv Δ), ClosEnv.empty ⊢ m ⇓ .clos (ƛ n') δ
  := soundness rs |> to_big_step
end

theorem Eval.reduce_iff_cbn {m : ∅ ⊢ ✶}
: ∃ (n : ∅‚ ✶ ⊢ ✶), m —↠ ƛ n
↔ ∃ (Δ : Context) (n' : Δ‚ ✶ ⊢ ✶) (δ : ClosEnv Δ), ClosEnv.empty ⊢ m ⇓ .clos (ƛ n') δ
:= by
  constructor
  · intro ⟨_, r⟩; exact reduce_to_cbn r
  · intro ⟨_, _, _, e⟩; exact Eval.reduce_of_cbn e
