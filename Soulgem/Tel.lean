import Soulgem.Main

/-! # Telescopes -/

namespace Soulgem
open ConLeche ConLeche.SetTheory Lean4Lean

universe u
variable {V : Type u} [SetTheory V]

def forallTel : List VExpr → VExpr → VExpr
  | [], R => R
  | A :: As, R => .forallE A (forallTel As R)

def lamTelE : List VExpr → VExpr → VExpr
  | [], b => b
  | A :: As, b => .lam A (lamTelE As b)

section
variable (M : CInterp V) (ls : List Nat)

noncomputable def lamTel : List VExpr → (List V → V) → List V → V
  | [], body, ρ => body ρ
  | A :: As, body, ρ => clam (interp M ls A ρ) fun x => lamTel As body (x :: ρ)

inductive Ext : List VExpr → List V → List V → Prop where
  | nil {ρ} : Ext [] ρ []
  | cons {A As ρ x xs} : x ∈ˢ interp M ls A ρ → Ext As (x :: ρ) xs → Ext (A :: As) ρ (x :: xs)

variable {M ls}

theorem lamTel_mem {R : VExpr} {body : List V → V} : ∀ {As : List VExpr} {ρ : List V},
    (∀ xs, Ext M ls As ρ xs → body (xs.reverse ++ ρ) ∈ˢ interp M ls R (xs.reverse ++ ρ)) →
    lamTel M ls As body ρ ∈ˢ interp M ls (forallTel As R) ρ
  | [], ρ, h => h [] .nil
  | A :: As, ρ, h => by
    simp only [lamTel, forallTel, interp]
    exact clam_mem_cpi fun x hx => lamTel_mem fun xs hxs => by
      have := h (x :: xs) (.cons hx hxs)
      simpa using this

theorem lamTel_congr {body body' : List V → V} : ∀ {As : List VExpr} {ρ : List V},
    (∀ xs, Ext M ls As ρ xs → body (xs.reverse ++ ρ) = body' (xs.reverse ++ ρ)) →
    lamTel M ls As body ρ = lamTel M ls As body' ρ
  | [], ρ, h => h [] .nil
  | A :: As, ρ, h => by
    simp only [lamTel]
    exact clam_congr fun x hx => lamTel_congr fun xs hxs => by
      have := h (x :: xs) (.cons hx hxs)
      simpa using this

theorem apps_lamTel {body : List V → V} : ∀ {As : List VExpr} {ρ xs : List V},
    Ext M ls As ρ xs → xs.foldl app (lamTel M ls As body ρ) = body (xs.reverse ++ ρ)
  | [], _, _, .nil => rfl
  | _ :: _, _, _ :: _, .cons hx hxs => by
    simp only [List.foldl, lamTel]
    rw [app_clam hx, apps_lamTel hxs]; simp

theorem interp_lamTelE (b : VExpr) : ∀ (As : List VExpr) (ρ : List V),
    interp M ls (lamTelE As b) ρ = lamTel M ls As (interp M ls b) ρ
  | [], _ => rfl
  | A :: As, ρ => by simp only [lamTelE, interp, lamTel, interp_lamTelE b As]

theorem lamTel_pt : ∀ {As : List VExpr} {ρ : List V}, lamTel M ls As (fun _ => pt) ρ = pt
  | [], _ => rfl
  | A :: As, ρ => by
    simp only [lamTel, lamTel_pt]; unfold clam; rw [ite_eq_left fun _ _ => rfl]

theorem lamTel_congrM {M' : CInterp V} {body : List V → V} : ∀ {As : List VExpr},
    (∀ A ∈ As, ConstsIn (fun c => M c = M' c) A) → ∀ {ρ : List V},
    lamTel M ls As body ρ = lamTel M' ls As body ρ
  | [], _, _ => rfl
  | A :: As, h, ρ => by
    simp only [lamTel]
    rw [interp_congr (h A (.head _)) ρ]
    congr 1; funext x
    exact lamTel_congrM (fun B hB => h B (.tail _ hB))

theorem Ext_nil_iff {ρ xs : List V} : Ext M ls [] ρ xs ↔ xs = [] :=
  ⟨fun | .nil => rfl, fun h => h ▸ .nil⟩

theorem Ext_cons_iff {A : VExpr} {As : List VExpr} {ρ xs : List V} :
    Ext M ls (A :: As) ρ xs ↔
      ∃ x xs', xs = x :: xs' ∧ x ∈ˢ interp M ls A ρ ∧ Ext M ls As (x :: ρ) xs' :=
  ⟨fun | .cons hx h => ⟨_, _, rfl, hx, h⟩, fun ⟨_, _, e, hx, h⟩ => e ▸ .cons hx h⟩

end

end Soulgem
