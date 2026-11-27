import Soulgem.Sound
import Soulgem.Spec.WF

/-! # Substitution and renaming in the model -/

namespace Soulgem
open ConLeche ConLeche.SetTheory Lean4Lean Spec

universe u
variable {V : Type u} [SetTheory V] (M : CInterp V) (ls : List Nat)

theorem getD_append_left' {σ ρ : List V} {i : Nat} (h : i < σ.length) :
    (σ ++ ρ).getD i pt = σ.getD i pt := getD_append_lt h

theorem getD_append_right' {σ ρ : List V} {i : Nat} (h : σ.length ≤ i) :
    (σ ++ ρ).getD i pt = ρ.getD (i - σ.length) pt := getD_append_ge h

theorem interp_subst (f : Nat → VExpr) : ∀ (e : VExpr) (k N : Nat) (σ ρ ρ' : List V),
    e.ClosedN (k + N) → σ.length = k → (∀ i < N, ρ'.getD i pt = interp M ls (f i) ρ) →
    interp M ls (subst f e k) (σ ++ ρ) = interp M ls e (σ ++ ρ')
  | .bvar i, k, N, σ, ρ, ρ', hc, hk, hf => by
    simp only [subst]
    split
    · rename_i h; simp only [interp]; rw [getD_append_left' (hk ▸ h), getD_append_left' (hk ▸ h)]
    · rename_i h
      have h' : k ≤ i := Nat.le_of_not_lt h
      have := interp_liftN M ls k (f (i - k)) 0 [] σ ρ rfl hk
      simp only [List.nil_append] at this
      simp only [interp]
      rw [this, getD_append_right' (hk ▸ h'), hk, hf _ (by simp [VExpr.ClosedN] at hc; omega)]
  | .sort _, _, _, _, _, _, _, _, _ => rfl
  | .const _ _, _, _, _, _, _, _, _, _ => rfl
  | .app g a, k, N, σ, ρ, ρ', hc, hk, hf => by
    simp only [subst, interp, interp_subst f g k N σ ρ ρ' hc.1 hk hf,
      interp_subst f a k N σ ρ ρ' hc.2 hk hf]
  | .lam A b, k, N, σ, ρ, ρ', hc, hk, hf => by
    simp only [subst, interp, interp_subst f A k N σ ρ ρ' hc.1 hk hf]
    congr 1; funext x
    have := interp_subst f b (k + 1) N (x :: σ) ρ ρ' (by simpa [Nat.add_right_comm] using hc.2)
      (by simp [hk]) hf
    simpa using this
  | .forallE A b, k, N, σ, ρ, ρ', hc, hk, hf => by
    simp only [subst, interp, interp_subst f A k N σ ρ ρ' hc.1 hk hf]
    congr 1; funext x
    have := interp_subst f b (k + 1) N (x :: σ) ρ ρ' (by simpa [Nat.add_right_comm] using hc.2)
      (by simp [hk]) hf
    simpa using this

theorem remap_eq_subst (g : Nat → Nat) : ∀ (e : VExpr) (k : Nat),
    remap g e k = subst (fun i => .bvar (g i)) e k
  | .bvar i, k => by
    simp only [remap, subst]; split
    · rfl
    · simp [VExpr.liftN, liftVar, Nat.add_comm]
  | .sort _, _ => rfl
  | .const _ _, _ => rfl
  | .app f a, k => by simp only [remap, subst, remap_eq_subst g f k, remap_eq_subst g a k]
  | .lam A b, k => by simp only [remap, subst, remap_eq_subst g A k, remap_eq_subst g b (k + 1)]
  | .forallE A b, k => by
    simp only [remap, subst, remap_eq_subst g A k, remap_eq_subst g b (k + 1)]

theorem interp_remap (g : Nat → Nat) (e : VExpr) (N : Nat) (ρ ρ' : List V) (hc : e.ClosedN N)
    (hf : ∀ i < N, ρ'.getD i pt = ρ.getD (g i) pt) :
    interp M ls (remap g e) ρ = interp M ls e ρ' := by
  rw [remap_eq_subst]
  have := interp_subst M ls (fun i => .bvar (g i)) e 0 N [] ρ ρ' (by simpa using hc) rfl
    (fun i hi => by rw [hf i hi]; rfl)
  simpa using this

theorem getD_reverse {xs : List V} {i : Nat} (h : i < xs.length) :
    xs.reverse.getD i pt = xs.getD (xs.length - 1 - i) pt := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_reverse h]

theorem getD_reverse_var {xs : List V} {d L : Nat} (hd : xs.length = d) (hL : L < d) :
    xs.reverse.getD (d - 1 - L) pt = xs.getD L pt := by
  subst hd
  rw [getD_reverse (by omega)]
  congr 1; omega

theorem interp_place (d0 : Nat) (σ : Nat → Nat) (d : Nat) (e : VExpr) (xs : List V)
    (hc : e.ClosedN d0) (hd : xs.length = d) (hσ : ∀ L < d0, σ L < d) :
    interp M ls (place d0 σ d e) xs.reverse =
      interp M ls e ((List.range d0).map fun L => xs.getD (σ L) pt).reverse := by
  unfold place
  refine interp_remap M ls _ e d0 _ _ hc fun i hi => ?_
  rw [getD_reverse_var hd (hσ _ (by omega)), getD_reverse (by simp; omega)]
  simp only [List.length_map, List.length_range, List.getD_eq_getElem?_getD]
  rw [List.getElem?_map, List.getElem?_range (by omega)]
  rfl

theorem interp_var {xs : List V} {d L : Nat} (hd : xs.length = d) (hL : L < d) :
    interp M ls (var d L) xs.reverse = xs.getD L pt := by
  simp only [var, interp]; exact getD_reverse_var hd hL

theorem interp_appN (f : VExpr) : ∀ (as : List VExpr) (ρ : List V),
    interp M ls (appN f as) ρ = (as.map (interp M ls · ρ)).foldl app (interp M ls f ρ)
  | [], _ => rfl
  | a :: as, ρ => by
    simp only [appN, List.foldl] at *
    have := interp_appN (.app f a) as ρ
    simpa [appN, interp] using this

theorem interp_vars {xs : List V} {d L n : Nat} (hd : xs.length = d) (hL : L + n ≤ d) :
    (vars d L n).map (interp M ls · xs.reverse) = (xs.drop L).take n := by
  apply List.ext_getElem (by simp [vars]; omega)
  intro i h1 h2
  simp only [vars, List.map_map, List.getElem_map, List.getElem_range, Function.comp]
  rw [interp_var M ls hd (by simp [vars] at h1; omega)]
  simp [List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_getElem (by simp [vars] at h1; omega)]
  simp

theorem _root_.Soulgem.Spec.stripPi_eq : ∀ {n : Nat} {e : VExpr} {Ps : List VExpr}
    {body : VExpr}, stripPi n e = some (Ps, body) → Ps.length = n ∧ e = Spec.forallTel Ps body
  | 0, e, Ps, body, h => by simp only [stripPi, Option.some.injEq, Prod.mk.injEq] at h
                            obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩
  | n + 1, .forallE A b, Ps, body, h => by
    simp only [stripPi, Option.bind_eq_bind] at h
    match hs : stripPi n b, h with
    | some (As, r), h =>
      simp only [Option.bind_some] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨h1, h2⟩ := stripPi_eq hs
      exact ⟨by simp [h1], by simp [Spec.forallTel, h2]⟩
    | none, h => simp at h
  | _ + 1, .bvar _, _, _, h | _ + 1, .sort _, _, _, h | _ + 1, .const .., _, _, h
  | _ + 1, .app .., _, _, h | _ + 1, .lam .., _, _, h => by simp [stripPi] at h

end Soulgem
