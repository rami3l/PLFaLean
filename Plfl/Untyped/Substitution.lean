-- https://plfa.github.io/Substitution/#plfa_plfa-part2-Substitution-2341

import Plfl.Init
import Plfl.Untyped

namespace Substitution

open Untyped Notation

abbrev Rename (Γ Δ) := ∀ {a : Ty}, Γ ∋ a → Δ ∋ a
abbrev Subst (Γ Δ) := ∀ {a : Ty}, Γ ∋ a → Δ ⊢ a

-- https://plfa.github.io/Substitution/#the-%CF%83-algebra-of-substitution
abbrev ids : Subst Γ Γ := .var
abbrev shift : Subst Γ (Γ‚ a) := .var ∘ .s

@[simp] def cons (m : Δ ⊢ a) (σ : Subst Γ Δ) : Subst (Γ‚ a) Δ
| _, .z => m
| _, .s x => σ x

abbrev seq (σ : Subst Γ Δ) (τ : Subst Δ Φ) : Subst Γ Φ := ⟪τ⟫ ∘ σ

namespace Notation
  scoped infixr:60 " ⦂⦂ " => cons
  scoped infixr:50 " ⨟ " => seq
end Notation

open Notation
open Subst

-- https://plfa.github.io/Substitution/#relating-the-σ-algebra-and-substitution-functions
def ren (ρ : Rename Γ Δ) : Subst Γ Δ := ids ∘ ρ

section
  variable {m : Δ ⊢ a} {σ : Subst Γ Δ} {τ : Subst Δ Φ}

  -- https://plfa.github.io/Substitution/#proofs-of-sub-head-sub-tail-sub-η-z-shift-sub-idl-sub-dist-and-sub-app
  @[simp] theorem sub_head : ⟪m ⦂⦂ σ⟫ (‵ .z) = m := rfl
  @[simp] theorem sub_tail : (shift ⨟ m ⦂⦂ σ) = σ (a := b) := rfl
  @[simp] theorem sub_η {σ : Subst (Γ‚ a) Δ} : (⟪σ⟫ (‵ .z) ⦂⦂ (shift ⨟ σ)) = σ (a := b) := by funext i; cases i <;> rfl
  @[simp] theorem z_shift : ((‵ .z) ⦂⦂ shift) = @ids (Γ‚ a) b := by funext i; cases i <;> rfl
  @[simp] theorem ids_seq : (ids ⨟ σ) = σ (a := a) := rfl
  @[simp] theorem sub_ap {l m : Γ ⊢ ✶} : ⟪σ⟫ (l □ m) = (⟪σ⟫ l) □ (⟪σ⟫ m) := rfl
  @[simp] theorem sub_dist : @Eq (Γ‚ a ∋ b → Φ ⊢ b) ((m ⦂⦂ σ) ⨟ τ) ((⟪τ⟫ m) ⦂⦂ (σ ⨟ τ)) := by funext i; cases i <;> rfl
end

-- https://plfa.github.io/Substitution/#interlude-congruences
/-
Nothing to do.
-/

section
  variable {m : Γ ⊢ a} {σ : Subst Γ Δ} {ρ : Rename Γ Δ}

  -- https://plfa.github.io/Substitution/#relating-rename-exts-ext-and-subst-zero-to-the-%CF%83-algebra
  @[simp] theorem ren_ext : @Eq (Γ‚ b ∋ c → Δ‚ b ⊢ c) (ren (ext ρ)) (exts (ren ρ)) := by funext i; cases i <;> rfl
  @[simp] theorem ren_shift : @Eq (Γ ∋ a → Γ‚ b ⊢ a) (ren .s) shift := by congr

  theorem rename_subst_ren {Γ Δ} {ρ : Rename Γ Δ} {m : Γ ⊢ a} : rename ρ m = ⟪ren ρ⟫ m := by
    match m with
    | ‵ _ => rfl
    | ƛ n => apply congr_arg Term.lam; rw [rename_subst_ren]; congr; funext _; exact ren_ext
    | l □ m => simp only [sub_ap]; apply congr_arg₂ Term.ap <;> exact rename_subst_ren

  theorem rename_shift : @Eq (Γ‚ ✶ ⊢ a) (rename .s m) (⟪shift⟫ m) := by
    simp only [rename_subst_ren]; congr

  theorem exts_cons_shift : exts (a := a) (b := b) σ = (‵ .z ⦂⦂ (σ ⨟ shift)) := by
    funext i; cases i <;> simp [exts, seq, cons, rename_shift]

  theorem ext_cons_z_shift : @Eq (Γ‚ b ∋ a → Δ‚ b ⊢ a) (ren (ext ρ)) (‵ .z ⦂⦂ (ren ρ ⨟ shift)) := by
    funext i; cases i <;> simp only [ren_ext, exts, rename_subst_ren, ren_shift]; rfl
    simp_all only [cons, Function.comp_apply]

  theorem subst_z_cons_ids {m : Γ ⊢ a} : @Eq (Γ‚ ✶ ∋ a → Γ ⊢ a) (subst₁σ m) (m ⦂⦂ ids) := by
    funext i; cases i <;> rfl

  -- https://plfa.github.io/Substitution/#proofs-of-sub-abs-sub-id-and-rename-id
  theorem sub_lam {σ : Subst Γ Δ} {n : Γ‚ ✶ ⊢ ✶} : ⟪σ⟫ (ƛ n) = (ƛ ⟪(‵ .z) ⦂⦂ (σ ⨟ shift)⟫ n) := by
    change (ƛ ⟪exts σ⟫ n) = _; congr; funext _; exact exts_cons_shift

  @[simp] theorem exts_ids : @Eq (Γ‚ b ∋ a → _) (exts ids) ids := by ext i; cases i <;> rfl

  theorem sub_ids {Γ} {m : Γ ⊢ a} : ⟪ids (Γ := Γ)⟫ m = m := by
    match m with
    | ‵ _ => rfl
    | ƛ n => apply congr_arg Term.lam; convert sub_ids;
             simp_all only
             ext x_1 x_2 : 2
             simp_all only [exts_ids]
    | l □ m => simp only [sub_ap]; apply congr_arg₂ Term.ap <;> exact sub_ids

  theorem rename_id : rename (λ {_} x => x) m = m := by
    convert sub_ids; ext; simp only [rename_subst_ren, ren]; congr

  -- https://plfa.github.io/Substitution/#proof-of-sub-idr
  theorem seq_ids : @Eq (Γ ∋ a → Δ ⊢ a) (σ ⨟ ids) σ := by
    ext; simp only [Function.comp_apply, sub_ids]
end

section
  variable {m : Γ ⊢ a} {ρ : Rename Δ Φ} {ρ' : Rename Γ Δ}

  -- https://plfa.github.io/Substitution/#proof-of-sub-sub
  @[simp] theorem comp_ext : @Eq (Γ‚ b ∋ a → _) ((ext ρ) ∘ (ext ρ')) (ext (ρ ∘ ρ')) := by
    funext i; cases i <;> rfl

  theorem comp_rename {Γ Δ Φ} {m : Γ ⊢ a} {ρ : Rename Δ Φ} {ρ' : Rename Γ Δ}
  : rename ρ (rename ρ' m) = rename (ρ ∘ ρ') m := by
     match m with
    | ‵ _ => rfl
    | ƛ n => apply congr_arg Term.lam; convert comp_rename; exact comp_ext.symm
    | l □ m => apply congr_arg₂ Term.ap <;> exact comp_rename

  theorem comm_subst_rename {Γ Δ} {σ : Subst Γ Δ} {ρ : ∀ {Γ}, Rename Γ (Γ‚ ✶)}
  (r : ∀ {x : Γ ∋ ✶}, exts σ (ρ x) = rename ρ (σ x)) {m : Γ ⊢ ✶}
  : ⟪exts (b := ✶) σ⟫ (rename ρ m) = rename ρ (⟪σ⟫ m)
  := by
    match m with
    | ‵ _ => exact r
    | l □ m => apply congr_arg₂ Term.ap <;> exact comm_subst_rename r
    | ƛ n =>
      apply congr_arg Term.lam

      let ρ' : ∀ {Γ}, Rename Γ (Γ‚ ✶)
        | [] => λ i => by cases i
        | _ :: _ => ext ρ

      apply comm_subst_rename (Γ := Γ‚ ✶) (Δ := Δ‚ ✶) (σ := exts σ) (ρ := ρ') (m := n); intro
      | .z => rfl
      | .s x => calc exts (exts σ) (ρ' (.s x))
        _ = rename .s (exts σ (ρ x)) := rfl
        _ = rename .s (rename ρ (σ x)) := by rw [r]
        _ = rename (.s ∘ ρ) (σ x) := comp_rename
        _ = rename (ext ρ ∘ .s) (σ x) := by congr
        _ = rename (ext ρ) (rename .s (σ x)) := comp_rename.symm
        _ = rename ρ' (exts σ (.s x)) := rfl
end

section
  variable {ρ : Rename Γ Δ} {σ : Subst Γ Δ} {τ : Subst Δ Φ} {θ : Subst Φ Ψ}

  theorem exts_seq_exts : @Eq (Γ‚ ✶ ∋ a → _) (exts σ ⨟ exts τ) (exts (σ ⨟ τ)) := by
    funext i; match i with
    | .z => rfl
    | .s i =>
      change ⟪exts τ⟫ (rename .s (σ i)) = rename .s (⟪τ⟫ (σ i))
      exact comm_subst_rename (m := σ i) (ρ := .s) (λ {x} => rfl)

  theorem sub_sub {Γ Δ Φ} {σ : Subst Γ Δ} {τ : Subst Δ Φ} {m : Γ ⊢ a}
  : ⟪τ⟫ (⟪σ⟫ m) = ⟪σ ⨟ τ⟫ m
  := by match m with
  | ‵ _ => rfl
  | l □ m => apply congr_arg₂ Term.ap <;> exact sub_sub
  | ƛ n => calc ⟪τ⟫ (⟪σ⟫ (ƛ n))
    _ = (ƛ ⟪exts τ⟫ (⟪exts σ⟫ n)) := rfl
    _ = (ƛ (⟪exts σ ⨟ exts τ⟫ n)) := by apply congr_arg Term.lam; exact sub_sub
    _ = (ƛ (⟪exts (σ ⨟ τ)⟫ n)) := by apply congr_arg Term.lam; congr; funext _; exact exts_seq_exts

  theorem rename_subst : ⟪τ⟫ (rename ρ m) = ⟪τ ∘ ρ⟫ m := by
    simp only [rename_subst_ren, sub_sub]; congr

  -- https://plfa.github.io/Substitution/#proof-of-sub-assoc
  theorem sub_assoc : @Eq (Γ ∋ a → _) ((σ ⨟ τ) ⨟ θ) (σ ⨟ (τ ⨟ θ)) := by
    funext i; simp only [Function.comp_apply, sub_sub]

  -- https://plfa.github.io/Substitution/#proof-of-subst-zero-exts-cons
  theorem subst₁σ_exts_cons {m : Δ ⊢ b} : @Eq (Γ‚ ✶ ∋ a → _) (exts σ ⨟ subst₁σ m) (m ⦂⦂ σ) := by
    funext i; cases i
    · rfl
    · rename_i x
      change ⟪fun {a} => subst₁σ m⟫ (exts (fun {a} => σ) (.s x)) = σ x
      simp only [exts, Subst.shift, rename_subst]
      convert sub_ids (m := σ x) using 2

  variable {n : Γ‚ ✶ ⊢ ✶} {m : Γ ⊢ ✶}

  -- https://plfa.github.io/Substitution/#proof-of-the-substitution-lemma
  theorem subst_comm : (⟪exts σ⟫ n)⟦⟪σ⟫ m⟧ = ⟪σ⟫ (n⟦m⟧) := calc _
      _ = ⟪subst₁σ (⟪σ⟫ m)⟫ (⟪exts σ⟫ n) := rfl
      _ = ⟪⟪σ⟫ m ⦂⦂ ids⟫ (⟪exts σ⟫ n) := by congr; simp only [subst_z_cons_ids]
      _ = ⟪(exts σ) ⨟ ((⟪σ⟫ m) ⦂⦂ ids)⟫ n := sub_sub
      _ = ⟪(‵ .z ⦂⦂ (σ ⨟ shift)) ⨟ (⟪σ⟫ m ⦂⦂ ids)⟫ n := by congr; simp only [exts_cons_shift]
      _ = ⟪⟪⟪σ⟫ m ⦂⦂ ids⟫ (‵ .z) ⦂⦂ ((σ ⨟ shift) ⨟ (⟪σ⟫ m ⦂⦂ ids))⟫ n := by congr; simp only [sub_dist]
      _ = ⟪⟪σ⟫ m ⦂⦂ ((σ ⨟ shift) ⨟ (⟪σ⟫ m ⦂⦂ ids))⟫ n := rfl
      _ = ⟪⟪σ⟫ m ⦂⦂ (σ ⨟ shift ⨟ ⟪σ⟫ m ⦂⦂ ids)⟫ n := by congr; simp only [sub_assoc]
      _ = ⟪⟪σ⟫ m ⦂⦂ (σ ⨟ ids)⟫ n := by congr
      _ = ⟪⟪σ⟫ m ⦂⦂ (ids ⨟ σ)⟫ n := by congr; simp only [seq_ids, ids_seq]
      _ = ⟪m ⦂⦂ ids ⨟ σ⟫ n := by congr; simp only [sub_dist]
      _ = ⟪σ⟫ (⟪m ⦂⦂ ids⟫ n) := sub_sub.symm
      _ = ⟪σ⟫ (n⟦m⟧) := by congr; simp only [subst_z_cons_ids]

  theorem rename_subst_comm : (rename (ext ρ) n)⟦rename ρ m⟧ = rename ρ (n⟦m⟧) := calc _
      _ = (⟪ren (ext ρ)⟫ n)⟦⟪ren ρ⟫ m⟧ := by rw [rename_subst_ren, rename_subst_ren]
      _ = (⟪exts (ren ρ)⟫ n)⟦⟪ren ρ⟫ m⟧ := by simp only [ren_ext]
      _ = ⟪ren ρ⟫ (n⟦m⟧) := subst_comm
      _ = rename ρ (n⟦m⟧) := rename_subst_ren.symm
end

/--
Substitute a term `m` for `♯1` within term `n`.
-/
abbrev subst₁_under₁ (m : Γ ⊢ b) (n : Γ‚ b‚ c ⊢ a) : Γ‚ c ⊢ a := ⟪exts (subst₁σ m)⟫ n

namespace Notation
  scoped notation:90 n "⟦" m "⟧₁" => subst₁_under₁ m n
end Notation

theorem substitution {m : Γ‚ ✶‚ ✶ ⊢ ✶} {n : Γ‚ ✶ ⊢ ✶} {l : Γ ⊢ ✶} : m⟦n⟧⟦l⟧ = m⟦l⟧₁⟦n⟦l⟧⟧
:= subst_comm.symm
