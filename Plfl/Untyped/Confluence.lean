module

-- https://plfa.github.io/Confluence/

public import Plfl.Init
public import Plfl.Untyped
public import Plfl.Untyped.Substitution

@[expose] public section

namespace Confluence

open Untyped.Notation

-- https://plfa.github.io/Confluence/#parallel-reduction
/--
Parallel reduction.
-/
inductive PReduce : (Γ ⊢ a) → (Γ ⊢ a) → Prop where
| var : PReduce (‵ x) (‵ x)
| lamβ : PReduce n n' → PReduce v v' → PReduce ((ƛ n) □ v) (n'⟦v'⟧)
| lamζ : PReduce n n' → PReduce (ƛ n) (ƛ n')
| apξ : PReduce l l' → PReduce m m' → PReduce (l □ m) (l' □ m')

namespace PReduce
  @[refl]
  theorem refl (m : Γ ⊢ a) : PReduce m m := by
    match m with
    | ‵ i => exact .var
    | ƛ n => apply lamζ; apply refl
    | l □ m => apply apξ <;> apply refl

  abbrev Clos {Γ a} := Relation.ReflTransGen (α := Γ ⊢ a) PReduce
end PReduce

open Relation.ReflTransGen (head_induction_on)

namespace Notation
  scoped infix:20 " ⇛ " => PReduce
  scoped infix:20 " ⇛* " => PReduce.Clos
end Notation

open Notation

namespace PReduce.Clos
  abbrev single (p : m ⇛ n) : (m ⇛* n) := .head p .refl
  abbrev tail : (m ⇛* n) → (n ⇛ n') → (m ⇛* n') := Relation.ReflTransGen.tail
  abbrev trans : (m ⇛* n) → (n ⇛* n') → (m ⇛* n') := Relation.ReflTransGen.trans

  instance : Coe (m ⇛ n) (m ⇛* n) where coe := .single
end PReduce.Clos

namespace PReduce
  instance {Γ a} : Std.Refl (@PReduce Γ a) where refl := .refl

  instance : Trans (α := Γ ⊢ a) Clos Clos Clos where trans := .trans
  instance : Trans (α := Γ ⊢ a) Clos PReduce Clos where trans c r := c.tail r
  instance : Trans (α := Γ ⊢ a) PReduce PReduce Clos where trans r r' := .tail r r'
  instance : Trans (α := Γ ⊢ a) PReduce Clos Clos where trans r c := .head r c

  -- https://plfa.github.io/Confluence/#equivalence-between-parallel-reduction-and-reduction
  def fromReduce {Γ a} {m n : Γ ⊢ a} : m —→ n → (m ⇛ n)
  | .lamβ => .lamβ (.refl _) (.refl _)
  | .lamζ rn => .lamζ (fromReduce rn)
  | .apξ₁ rl => .apξ (fromReduce rl) (.refl _)
  | .apξ₂ rm => .apξ (.refl _) (fromReduce rm)

  def toReduceClos : (m ⇛ n) → (m —↠ n)
  | .var => Untyped.Reduce.Clos.refl
  | .lamβ (n:=n) (n':=n') (v:=v) (v':=v') rn rv =>
    calc (ƛ n) □ v
      _ —↠ (ƛ n') □ v := Untyped.Reduce.ap_congr₁ (toReduceClos (.lamζ rn))
      _ —↠ (ƛ n') □ v' := Untyped.Reduce.ap_congr₂ (toReduceClos rv)
      _ —→ n'⟦v'⟧ := Untyped.Reduce.lamβ
  | .lamζ rn => Untyped.Reduce.lam_congr (toReduceClos rn)
  | .apξ (l:=l) (l':=l') (m:=m) (m':=m') rl rm =>
    calc l □ m
      _ —↠ l' □ m := Untyped.Reduce.ap_congr₁ (toReduceClos rl)
      _ —↠ l' □ m' := Untyped.Reduce.ap_congr₂ (toReduceClos rm)
end PReduce

instance instNonemptyPReduceReduceClos : (m ⇛* n) ≃ (m —↠ n) where
  toFun := toFun
  invFun := invFun
  left_inv _ := by simp only
  right_inv _ := by simp only
  where
    toFun {m n} : (m ⇛* n) → (m —↠ n) := by
      intro rs; induction rs using head_induction_on with
      | refl => rfl
      | head r _ => apply r.toReduceClos.trans; trivial

    invFun {m n} : (m —↠ n) → (m ⇛* n) := by
      intro rs; induction rs using head_induction_on with
      | refl => rfl
      | head r _ => refine .head (PReduce.fromReduce r) ?_; trivial

open Untyped.Subst
open Substitution

-- https://plfa.github.io/Confluence/#substitution-lemma-for-parallel-reduction
abbrev par_subst (σ : Subst Γ Δ) (σ' : Subst Γ Δ) := ∀ {a} {x : Γ ∋ a}, σ x ⇛ σ' x

section
  lemma par_rename {ρ : Rename Γ Δ} {m m' : Γ ⊢ a} : (m ⇛ m') → (rename ρ m ⇛ rename ρ m')
  := open PReduce in by intro
  | .var => exact .var
  | .lamζ rn => apply lamζ; apply par_rename; trivial
  | .apξ rl rm => apply apξ <;> (apply par_rename; trivial)
  | .lamβ rn rv =>
    rename_i n n' v v'; have rn' := par_rename (ρ := ext ρ) rn; have rv' := par_rename (ρ := ρ) rv
    have := lamβ rn' rv'; rwa [rename_subst_comm] at this

  theorem par_subst_exts {σ τ : Subst Γ Δ} (s : par_subst σ τ)
  : ∀ {b}, par_subst (exts (b := b) σ) (exts τ)
  := by
    intro _ _; intro
    | .z => exact .var
    | .s i => exact par_rename s

  theorem subst_par {σ τ : Subst Γ Δ} {m m' : Γ ⊢ a}
  (s : par_subst σ τ) (p : m ⇛ m') : (⟪σ⟫ m ⇛ ⟪τ⟫ m')
  := open PReduce in by
    match p with
    | .var => exact s
    | .lamβ pn pv => rw [←subst_comm]; apply_rules [lamβ, subst_par, par_subst_exts]
    | .lamζ pn => apply_rules [lamζ, subst_par, par_subst_exts]
    | .apξ pl pm => apply_rules [apξ, subst_par]

  variable {n n' : Γ‚ a ⊢ b} {m m': Γ ⊢ a}

  theorem par_subst₁σ (p : m ⇛ m') : par_subst (subst₁σ m) (subst₁σ m') := by
    intro _ i; cases i with simp only [subst₁σ]
    | z => exact p
    | s i => exact .var

  theorem sub_par (pn : n ⇛ n') (pm : m ⇛ m') : n⟦m⟧ ⇛ n'⟦m'⟧ :=
    subst_par (par_subst₁σ pm) pn
end

-- https://plfa.github.io/Confluence/#parallel-reduction-satisfies-the-diamond-property
/--
Many parallel reductions at once.
-/
abbrev PReduce.plus : (Γ ⊢ a) → (Γ ⊢ a)
| ‵ i => ‵ i
| ƛ n => ƛ (plus n)
| (ƛ n) □ m => plus n⟦plus m⟧
| l □ m => plus l □ plus m

namespace Notation
  postfix:max "⁺" => PReduce.plus
end Notation

theorem par_triangle {m n : Γ ⊢ a} : (m ⇛ n) → (n ⇛ m⁺) := open PReduce in by
intro
| .var => exact .var
| .lamβ pn pv => exact subst_par (par_subst₁σ (par_triangle pv)) (par_triangle pn)
| .lamζ pn => exact lamζ (par_triangle pn)
| .apξ pl pm => rename_i l l' m m'; match l with
  | ‵ _ => exact apξ (par_triangle pl) (par_triangle pm)
  | _ □ _ => exact apξ (par_triangle pl) (par_triangle pm)
  | ƛ _  => have .lamζ pl := pl; exact lamβ (par_triangle pl) (par_triangle pm)

theorem par_diamond {m n n' : Γ ⊢ a} (p : m ⇛ n) (p' : m ⇛ n')
: ∃ (l : Γ ⊢ a), (n ⇛ l) ∧ (n' ⇛ l)
:= by
  exists m⁺; constructor <;> (apply par_triangle; trivial)

-- https://plfa.github.io/Confluence/#proof-of-confluence-for-parallel-reduction
theorem strip {m n n' : Γ ⊢ a} (mn : m ⇛ n) (mn' : m ⇛* n')
: ∃ (l : Γ ⊢ a), (n ⇛* l) ∧ (n' ⇛ l)
:= by induction mn' using head_induction_on generalizing n with
| refl => exists n, .refl
| head mm' _ r =>
  rename_i m' f; have ⟨l, hl⟩ := r (par_triangle mm')
  exists l; refine ⟨?_, hl.2⟩; exact .trans (par_triangle mn) hl.1

theorem par_confluence {l m m' : Γ ⊢ a} (lm : l ⇛* m) (lm' : l ⇛* m')
: ∃ (n : Γ ⊢ a), (m ⇛* n) ∧ (m' ⇛* n)
:= by induction lm using head_induction_on generalizing m' with
| refl => exists m', lm'
| head lm₁ _ r =>
  have ⟨n, m₁n, m'n⟩ := strip lm₁ lm'
  have ⟨n', mn', nn'⟩ := r m₁n
  exists n', mn'; exact .trans m'n nn'

-- https://plfa.github.io/Confluence/#proof-of-confluence-for-reduction
theorem confluence {l m m' : Γ ⊢ a} (lm : l —↠ m) (lm' : l —↠ m')
: ∃ (n : Γ ⊢ a), (m —↠ n) ∧ (m' —↠ n)
:= by
  let equiv := @instNonemptyPReduceReduceClos Γ a
  have ⟨n, mn, m'n⟩:= par_confluence (equiv.invFun lm) (equiv.invFun lm')
  exists n; exact ⟨equiv.toFun mn, equiv.toFun m'n⟩
