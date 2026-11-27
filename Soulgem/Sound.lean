import Soulgem.Collapse
import Lean4Lean.Theory.Typing.Basic

/-! # Soundness of lean4lean's typing judgment in the collapse model -/

namespace Soulgem
open ConLeche ConLeche.SetTheory Lean4Lean

universe u
variable {V : Type u} [SetTheory V]

abbrev CInterp (V : Type u) := Name → List Nat → V

noncomputable def interp (M : CInterp V) (ls : List Nat) : VExpr → List V → V
  | .bvar i, ρ => ρ.getD i pt
  | .sort l, _ => univ (l.eval ls)
  | .const c us, _ => M c (us.map (VLevel.eval ls))
  | .app f a, ρ => app (interp M ls f ρ) (interp M ls a ρ)
  | .lam A b, ρ => clam (interp M ls A ρ) (fun x => interp M ls b (x :: ρ))
  | .forallE A B, ρ => cpi (interp M ls A ρ) (fun x => interp M ls B (x :: ρ))

section
variable (M : CInterp V) (ls : List Nat)

theorem getD_append_lt {α} {l₁ l₂ : List α} {i : Nat} {d : α} (h : i < l₁.length) :
    (l₁ ++ l₂).getD i d = l₁.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_ge {α} {l₁ l₂ : List α} {i : Nat} {d : α} (h : l₁.length ≤ i) :
    (l₁ ++ l₂).getD i d = l₂.getD (i - l₁.length) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

theorem interp_liftN (n : Nat) : ∀ (e : VExpr) (k : Nat) (ρ₁ σ ρ₂ : List V),
    ρ₁.length = k → σ.length = n →
    interp M ls (e.liftN n k) (ρ₁ ++ (σ ++ ρ₂)) = interp M ls e (ρ₁ ++ ρ₂)
  | .bvar i, k, ρ₁, σ, ρ₂, h1, h2 => by
    simp only [VExpr.liftN, interp, liftVar]
    split
    · rename_i hi
      rw [getD_append_lt (h1 ▸ hi), getD_append_lt (h1 ▸ hi)]
    · rename_i hi
      rw [getD_append_ge (by omega), getD_append_ge (by omega), getD_append_ge (by omega)]
      congr 1; omega
  | .sort _, _, _, _, _, _, _ => rfl
  | .const _ _, _, _, _, _, _, _ => rfl
  | .app f a, k, ρ₁, σ, ρ₂, h1, h2 => by
    simp only [VExpr.liftN, interp]
    rw [interp_liftN n f k ρ₁ σ ρ₂ h1 h2, interp_liftN n a k ρ₁ σ ρ₂ h1 h2]
  | .lam A b, k, ρ₁, σ, ρ₂, h1, h2 => by
    simp only [VExpr.liftN, interp]
    rw [interp_liftN n A k ρ₁ σ ρ₂ h1 h2]
    congr 1; funext x
    exact interp_liftN n b (k+1) (x :: ρ₁) σ ρ₂ (by simp [h1]) h2
  | .forallE A B, k, ρ₁, σ, ρ₂, h1, h2 => by
    simp only [VExpr.liftN, interp]
    rw [interp_liftN n A k ρ₁ σ ρ₂ h1 h2]
    congr 1; funext x
    exact interp_liftN n B (k+1) (x :: ρ₁) σ ρ₂ (by simp [h1]) h2

theorem interp_lift (e : VExpr) (x : V) (ρ : List V) :
    interp M ls e.lift (x :: ρ) = interp M ls e ρ :=
  interp_liftN M ls 1 e 0 [] [x] ρ rfl rfl

theorem interp_closed {e : VExpr} (h : e.ClosedN) (ρ : List V) :
    interp M ls e ρ = interp M ls e [] := by
  have := interp_liftN M ls ρ.length e 0 [] ρ [] rfl rfl
  rwa [h.liftN_eq (Nat.zero_le _), List.nil_append, List.append_nil] at this

theorem interp_instN : ∀ (e e' : VExpr) (k : Nat) (ρ₁ ρ₂ : List V), ρ₁.length = k →
    interp M ls (e.inst e' k) (ρ₁ ++ ρ₂) = interp M ls e (ρ₁ ++ interp M ls e' ρ₂ :: ρ₂)
  | .bvar i, e', k, ρ₁, ρ₂, h1 => by
    simp only [VExpr.inst, VExpr.instVar]
    split
    · rename_i hi
      simp only [interp]
      rw [getD_append_lt (h1 ▸ hi), getD_append_lt (h1 ▸ hi)]
    · split
      · rename_i hi; subst hi
        have := interp_liftN M ls ρ₁.length e' 0 [] ρ₁ ρ₂ rfl rfl
        simp only [List.nil_append] at this
        rw [h1] at this
        rw [this]; simp only [interp]
        rw [getD_append_ge (by omega)]; simp [h1]
      · rename_i hlt hne
        simp only [interp]
        rw [getD_append_ge (by omega), getD_append_ge (by omega)]
        obtain ⟨j, hj⟩ : ∃ j, i - ρ₁.length = j + 1 := ⟨i - ρ₁.length - 1, by omega⟩
        rw [hj]; simp only [List.getD_cons_succ]; congr 1; omega
  | .sort _, _, _, _, _, _ => rfl
  | .const _ _, _, _, _, _, _ => rfl
  | .app f a, e', k, ρ₁, ρ₂, h1 => by
    simp only [VExpr.inst, interp]
    rw [interp_instN f e' k ρ₁ ρ₂ h1, interp_instN a e' k ρ₁ ρ₂ h1]
  | .lam A b, e', k, ρ₁, ρ₂, h1 => by
    simp only [VExpr.inst, interp]
    rw [interp_instN A e' k ρ₁ ρ₂ h1]
    congr 1; funext x
    exact interp_instN b e' (k+1) (x :: ρ₁) ρ₂ (by simp [h1])
  | .forallE A B, e', k, ρ₁, ρ₂, h1 => by
    simp only [VExpr.inst, interp]
    rw [interp_instN A e' k ρ₁ ρ₂ h1]
    congr 1; funext x
    exact interp_instN B e' (k+1) (x :: ρ₁) ρ₂ (by simp [h1])

theorem interp_inst (e e' : VExpr) (ρ : List V) :
    interp M ls (e.inst e') ρ = interp M ls e (interp M ls e' ρ :: ρ) :=
  interp_instN M ls e e' 0 [] ρ rfl

theorem interp_instL (us : List VLevel) : ∀ (e : VExpr) (ρ : List V),
    interp M ls (e.instL us) ρ = interp M (us.map (VLevel.eval ls)) e ρ
  | .bvar _, _ => rfl
  | .sort l, _ => by simp only [VExpr.instL, interp, VLevel.eval_inst]
  | .const c us', _ => by
    simp only [VExpr.instL, interp, List.map_map]
    congr 1; apply List.map_congr_left; intro l _; exact VLevel.eval_inst
  | .app f a, ρ => by simp only [VExpr.instL, interp, interp_instL us f, interp_instL us a]
  | .lam A b, ρ => by simp only [VExpr.instL, interp, interp_instL us A, interp_instL us b]
  | .forallE A B, ρ => by simp only [VExpr.instL, interp, interp_instL us A, interp_instL us B]

def Sat : List VExpr → List V → Prop
  | [], [] => True
  | A :: Γ, x :: ρ => Sat Γ ρ ∧ x ∈ˢ interp M ls A ρ
  | _, _ => False

theorem Sat.lookup {Γ : List VExpr} {i A} (H : Lookup Γ i A) :
    ∀ {ρ : List V}, Sat M ls Γ ρ → ρ.getD i pt ∈ˢ interp M ls A ρ := by
  induction H with
  | zero =>
    intro ρ hρ
    match ρ, hρ with
    | x :: ρ, ⟨_, hx⟩ => rw [interp_lift]; exact hx
  | succ _ ih =>
    intro ρ hρ
    match ρ, hρ with
    | x :: ρ, ⟨hρ, _⟩ => rw [interp_lift]; exact ih hρ

end

structure IsModel (M : CInterp V) (env : VEnv) : Prop where
  const : ∀ {c ci}, env.constants c = some ci → ∀ ls : List Nat, ls.length = ci.uvars →
    ∀ ρ, M c ls ∈ˢ interp M ls ci.type ρ
  defeq : ∀ {df}, env.defeqs df → ∀ ls : List Nat, ls.length = df.uvars → ∀ ρ,
    interp M ls df.lhs ρ = interp M ls df.rhs ρ ∧ interp M ls df.lhs ρ ∈ˢ interp M ls df.type ρ

theorem map_eval_of_forall₂ {ls : List Nat} : ∀ {us us' : List VLevel},
    List.Forall₂ (· ≈ ·) us us' → us.map (VLevel.eval ls) = us'.map (VLevel.eval ls)
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons h t => by
    simp only [List.map_cons, VLevel.equiv_def.mp h ls, map_eval_of_forall₂ t]

theorem IsModel.sound {M : CInterp V} {env : VEnv} (hM : IsModel M env) {U Γ e₁ e₂ A}
    (H : env.IsDefEq U Γ e₁ e₂ A) : ∀ ls ρ, Sat M ls Γ ρ →
      interp M ls e₁ ρ = interp M ls e₂ ρ ∧ interp M ls e₁ ρ ∈ˢ interp M ls A ρ := by
  induction H with
  | bvar h => intro ls ρ hρ; exact ⟨rfl, Sat.lookup M ls h hρ⟩
  | symm _ ih =>
    intro ls ρ hρ; obtain ⟨h1, h2⟩ := ih ls ρ hρ; exact ⟨h1.symm, h1 ▸ h2⟩
  | trans _ _ ih1 ih2 =>
    intro ls ρ hρ; exact ⟨(ih1 ls ρ hρ).1.trans (ih2 ls ρ hρ).1, (ih1 ls ρ hρ).2⟩
  | sortDF _ _ h =>
    intro ls ρ _
    simp only [interp]
    exact ⟨by rw [VLevel.equiv_def.mp h ls], univ_mem_univ _⟩
  | constDF h1 _ _ hlen hls =>
    intro ls ρ _
    simp only [interp]
    refine ⟨by rw [map_eval_of_forall₂ hls], ?_⟩
    rw [interp_instL]
    exact hM.const h1 _ (by simp [hlen]) ρ
  | appDF _ _ ih1 ih2 =>
    intro ls ρ hρ
    obtain ⟨hf, hfm⟩ := ih1 ls ρ hρ
    obtain ⟨ha, ham⟩ := ih2 ls ρ hρ
    simp only [interp] at hfm ⊢
    refine ⟨by rw [hf, ha], ?_⟩
    rw [interp_inst]
    exact app_mem_cpi hfm ham
  | lamDF _ _ ih1 ih2 =>
    intro ls ρ hρ
    obtain ⟨hA, -⟩ := ih1 ls ρ hρ
    have h2 := fun x (hx : x ∈ˢ interp M ls _ ρ) => ih2 ls (x :: ρ) ⟨hρ, hx⟩
    simp only [interp]
    refine ⟨?_, clam_mem_cpi fun x hx => (h2 x hx).2⟩
    rw [← hA]; exact clam_congr fun x hx => (h2 x hx).1
  | forallEDF _ _ ih1 ih2 =>
    intro ls ρ hρ
    obtain ⟨hA, hAm⟩ := ih1 ls ρ hρ
    have h2 := fun x (hx : x ∈ˢ interp M ls _ ρ) => ih2 ls (x :: ρ) ⟨hρ, hx⟩
    simp only [interp] at hAm h2 ⊢
    refine ⟨?_, cpi_mem_univ hAm fun x hx => (h2 x hx).2⟩
    rw [← hA]; exact cpi_congr fun x hx => (h2 x hx).1
  | defeqDF _ _ ih1 ih2 =>
    intro ls ρ hρ; exact ⟨(ih2 ls ρ hρ).1, (ih1 ls ρ hρ).1 ▸ (ih2 ls ρ hρ).2⟩
  | beta _ _ ih1 ih2 =>
    intro ls ρ hρ
    obtain ⟨-, he'⟩ := ih2 ls ρ hρ
    have h1 := ih1 ls (interp M ls _ ρ :: ρ) ⟨hρ, he'⟩
    simp only [interp]
    rw [app_clam he', interp_inst, interp_inst]
    exact ⟨rfl, h1.2⟩
  | eta _ ih =>
    intro ls ρ hρ
    obtain ⟨-, he⟩ := ih ls ρ hρ
    simp only [interp, interp_lift, List.getD_cons_zero] at he ⊢
    exact ⟨clam_app_eta he, (clam_app_eta he).symm ▸ he⟩
  | proofIrrel _ _ _ ih1 ih2 ih3 =>
    intro ls ρ hρ
    have hp := (ih1 ls ρ hρ).2
    simp only [interp, VLevel.eval] at hp
    exact ⟨(mem_univ_zero hp (ih2 ls ρ hρ).2).trans (mem_univ_zero hp (ih3 ls ρ hρ).2).symm,
      (ih2 ls ρ hρ).2⟩
  | extra h1 _ hlen =>
    intro ls ρ _
    rw [interp_instL, interp_instL, interp_instL]
    exact hM.defeq h1 _ (by simp [hlen]) ρ

end Soulgem
