import Soulgem.Tel
import ConLeche.SetModel.TupleTower
import Soulgem.Spec.Induct

/-! # Telescopes as sets -/

namespace Soulgem
open ConLeche ConLeche.SetTheory ConLeche.SetTheory.Tower Lean4Lean Spec

universe u
variable {V : Type u} [SetTheory V] (M : CInterp V) (ls : List Nat)

noncomputable def telOf : (As : List VExpr) → List V → TeleS V As.length
  | [], _ => .nil
  | A :: As, ρ => .cons (interp M ls A ρ) fun x => telOf As (x :: ρ)

theorem fitsS_telOf : ∀ {As : List VExpr} {ρ xs : List V},
    FitsS (telOf M ls As ρ) xs ↔ Ext M ls As ρ xs
  | [], ρ, [] => by simp [telOf, FitsS, Ext_nil_iff]
  | [], ρ, _ :: _ => by simp [telOf, FitsS, Ext_nil_iff]
  | A :: As, ρ, [] => by simp only [telOf, FitsS, Ext_cons_iff]; simp
  | A :: As, ρ, x :: xs => by
    simp only [telOf, FitsS, Ext_cons_iff, fitsS_telOf]
    constructor
    · intro ⟨h1, h2⟩; exact ⟨x, xs, rfl, h1, h2⟩
    · intro ⟨_, _, e, h1, h2⟩; cases e; exact ⟨h1, h2⟩

theorem mem_towerSet_pos {w : Nat} (hw : w ≠ 0) : ∀ {n} {T : TeleS V n} {t : V},
    t ∈ˢ towerSet w T ↔ ∃ xs, FitsS T xs ∧ t = mkTower xs
  | _, .nil, t => by
    simp only [towerSet, mem_unitSet_iff]
    constructor
    · intro h; exact ⟨[], trivial, h⟩
    · intro ⟨xs, hf, h⟩
      cases xs with
      | nil => exact h
      | cons => exact absurd hf (by simp [FitsS])
  | _, .cons A B, t => by
    simp only [towerSet, sigmaSet, ite_eq_right hw, mem_sigmaPairs]
    constructor
    · intro ⟨x, hx, y, hy, e⟩
      obtain ⟨ys, hys, rfl⟩ := (mem_towerSet_pos hw).mp hy
      exact ⟨x :: ys, ⟨hx, hys⟩, by rw [e, mkTower, spair_eq_kpair]⟩
    · intro ⟨xs, hf, e⟩
      cases xs with
      | nil => exact absurd hf (by simp [FitsS])
      | cons x ys =>
        exact ⟨x, hf.1, mkTower ys, (mem_towerSet_pos hw).mpr ⟨ys, hf.2, rfl⟩,
            by rw [e, mkTower, spair_eq_kpair]⟩

noncomputable def extSet (As : List VExpr) (ρ : List V) : V := towerSet 1 (telOf M ls As ρ)

theorem mem_extSet {As : List VExpr} {ρ : List V} {t : V} :
    t ∈ˢ extSet M ls As ρ ↔ ∃ xs, Ext M ls As ρ xs ∧ t = mkTower xs := by
  unfold extSet; rw [mem_towerSet_pos Nat.one_ne_zero]
  simp only [fitsS_telOf]

theorem Ext.length_eq : ∀ {As : List VExpr} {ρ xs : List V}, Ext M ls As ρ xs →
    xs.length = As.length
  | _, _, _, .nil => rfl
  | _, _, _, .cons _ h => by simp [Ext.length_eq h]

theorem mkTower_mem_extSet {As : List VExpr} {ρ xs : List V} (h : Ext M ls As ρ xs) :
    mkTower xs ∈ˢ extSet M ls As ρ := (mem_extSet M ls).mpr ⟨xs, h, rfl⟩

noncomputable def piTel : List VExpr → (List V → V) → List V → V
  | [], body, ρ => body ρ
  | A :: As, body, ρ => cpi (interp M ls A ρ) fun x => piTel As body (x :: ρ)

theorem interp_forallTel (R : VExpr) : ∀ (As : List VExpr) (ρ : List V),
    interp M ls (Spec.forallTel As R) ρ = piTel M ls As (interp M ls R) ρ
  | [], _ => rfl
  | A :: As, ρ => by simp only [Spec.forallTel, interp, piTel, interp_forallTel R As]

theorem interp_lamTel' (b : VExpr) : ∀ (As : List VExpr) (ρ : List V),
    interp M ls (Spec.lamTel As b) ρ = Soulgem.lamTel M ls As (interp M ls b) ρ
  | [], _ => rfl
  | A :: As, ρ => by simp only [Spec.lamTel, interp, Soulgem.lamTel, interp_lamTel' b As]

variable {M ls}

theorem apps_mem_piTel {B : List V → V} : ∀ {As : List VExpr} {ρ xs : List V} {f : V},
    f ∈ˢ piTel M ls As B ρ → Ext M ls As ρ xs → xs.foldl app f ∈ˢ B (xs.reverse ++ ρ)
  | [], _, _, _, hf, .nil => hf
  | _ :: _, _, _, _, hf, .cons hx hxs => by
    simp only [List.foldl]
    have := apps_mem_piTel (app_mem_cpi hf hx) hxs
    simpa using this

theorem lamTel_eta {B : List V → V} : ∀ {As : List VExpr} {ρ : List V} {f : V} {body : List V → V},
    f ∈ˢ piTel M ls As B ρ → (∀ xs, Ext M ls As ρ xs → body (xs.reverse ++ ρ) = xs.foldl app f) →
    Soulgem.lamTel M ls As body ρ = f
  | [], _, _, _, _, h => by simpa [Soulgem.lamTel] using h [] .nil
  | _ :: _, _, _, _, hf, h => by
    simp only [Soulgem.lamTel, piTel] at hf ⊢
    rw [clam_congr (F' := fun x => app _ x) fun x hx =>
      lamTel_eta (app_mem_cpi hf hx) fun ys hys => by simpa using h (x :: ys) (.cons hx hys)]
    exact clam_app_eta hf

theorem lamTel_mem_piTel {body B : List V → V} : ∀ {As : List VExpr} {ρ : List V},
    (∀ xs, Ext M ls As ρ xs → body (xs.reverse ++ ρ) ∈ˢ B (xs.reverse ++ ρ)) →
    Soulgem.lamTel M ls As body ρ ∈ˢ piTel M ls As B ρ
  | [], ρ, h => h [] .nil
  | A :: As, ρ, h => by
    simp only [Soulgem.lamTel, piTel]
    exact clam_mem_cpi fun x hx => lamTel_mem_piTel fun xs hxs => by
      have := h (x :: xs) (.cons hx hxs)
      simpa using this

theorem mem_piTel_of_values {B B' : List V → V} : ∀ {As : List VExpr} {ρ : List V} {f : V},
    f ∈ˢ piTel M ls As B ρ →
    (∀ xs, Ext M ls As ρ xs → xs.foldl app f ∈ˢ B' (xs.reverse ++ ρ)) →
    f ∈ˢ piTel M ls As B' ρ
  | [], ρ, f, _, h => h [] .nil
  | A :: As, ρ, f, hf, h => by
    simp only [piTel] at hf ⊢
    obtain ⟨g, hg, rfl⟩ := mem_cpi.mp hf
    refine mem_cpi.mpr ⟨g, ?_, rfl⟩
    rw [← eq_graph_app_of_mem_piSet hg]
    refine graph_mem_piSet fun x hx => ?_
    have hgx := app_mem_of_mem_piSet hg hx
    refine mem_piTel_of_values hgx fun xs hxs => ?_
    have := h (x :: xs) (.cons hx hxs)
    simp only [List.foldl, List.reverse_cons, List.append_assoc, List.singleton_append] at this
    rwa [app_collapse hx] at this

theorem piTel_mono {B B' : List V → V} {As : List VExpr} {ρ : List V}
    (h : ∀ xs, Ext M ls As ρ xs → B (xs.reverse ++ ρ) ⊆ˢ B' (xs.reverse ++ ρ)) :
    piTel M ls As B ρ ⊆ˢ piTel M ls As B' ρ :=
  fun _ hf => mem_piTel_of_values hf fun xs hxs => h xs hxs _ (apps_mem_piTel hf hxs)

end Soulgem
