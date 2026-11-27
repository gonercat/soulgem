import Soulgem.Model.NestedData

/-! # Nested blocks: an auxiliary constructor's fields read as its container constructor's -/

namespace Soulgem.Nested
open ConLeche ConLeche.SetTheory ConLeche.SetTheory.Tower Lean4Lean Spec BlockSem BlockModel

universe u
variable {V : Type u} [SetTheory V]

theorem interp_key (M₀ MJ : CInterp V) (ls : List Nat) (lv : List VLevel) (Ds : List VExpr)
    {e : VExpr} {j : Nat} (hcl : e.ClosedN (j + Ds.length))
    (hagr : ConstsIn (fun c => M₀ c = MJ c) e) (σ : List V) (hσ : σ.length = j) (ρp : List V) :
    interp M₀ ls (subst (argSubst Ds) (e.instL lv) j) (σ ++ ρp) =
      interp MJ (lv.map (VLevel.eval ls)) e (σ ++ keyArgs M₀ ls Ds ρp) := by
  rw [interp_subst M₀ ls _ _ j Ds.length σ ρp (keyArgs M₀ ls Ds ρp) hcl.instL hσ
    (fun i hi => by
        rw [keyArgs_getD M₀ ls Ds ρp hi, argSubst, dite_eq_left hi, getElem_eq_getElem!]),
    interp_instL]
  exact interp_congr hagr _

section Fields
variable {M : CInterp V} {env env₁ : VEnv} {b : SBlock} (S : Setting M env env₁ b)
  {MJ : CInterp V} {envJ envJ₁ : VEnv} {r : RBlock} (cJ : CanonR M env r MJ envJ envJ₁)
  {lv : List VLevel} {Ds : List VExpr}

include S cJ in
theorem interp_key_base {C₀ : List Nat → List V → Nat → V} {ls : List Nat} {e x : VExpr} {j : Nat}
    (hx : x.EqL (atKey lv Ds j e)) (hcl : e.ClosedN (j + Ds.length)) (hc : ConstsIn (Dom envJ) e)
    (hfree : ConstsIn (Dom env₁) x) (hm : mentions b.names x = false)
    (σ : List V) (hσ : σ.length = j) (ρp : List V) :
    interp M ls x (σ ++ ρp) =
      interp MJ (lv.map (VLevel.eval ls)) e (σ ++ keyArgs (M₁ M b C₀) ls Ds ρp) := by
  rw [← interp_congr (S.free (C := C₀) hfree hm), interp_EqL _ _ hx]
  exact interp_key _ _ ls lv Ds hcl (hc.mono fun _ h => agree_J S cJ h) σ hσ ρp

theorem forall₂_map_eq {α β γ : Type _} {R : α → β → Prop} {f : α → γ} {g : β → γ} :
    ∀ {l l'}, List.Forall₂ R l l' → (∀ a ∈ l, ∀ b ∈ l', R a b → f a = g b) → l.map f = l'.map g
  | _, _, .nil, _ => rfl
  | _, _, .cons h t, H => by
    simp only [List.map_cons, H _ (.head _) _ (.head _) h,
      forall₂_map_eq t fun a ha b hb => H a (.tail _ ha) b (.tail _ hb)]

include S cJ in
theorem fdom_rec_corr {C₀ : List Nat → List V → Nat → V} {X Y : Nat → V} {ls : List Nat}
    {f' fJ : SField} {k : Nat} {xs xs' idx idx' : List VExpr} {m' s : Nat}
    (hcJ : fJ.cert = .recursive xs m' idx) (hcb : f'.cert = .recursive xs' s idx')
    (hxs : EqLTel lv Ds k xs' xs)
    (hidx : List.Forall₂ (fun e e' => e.EqL (atKey lv Ds (k + xs.length) e')) idx' idx)
    (hXY : X s = Y m')
    (hxs_cl : ∀ i < xs.length, (xs[i]!).ClosedN (k + i + Ds.length))
    (hxs_c : ∀ i < xs.length, ConstsIn (Dom envJ) xs[i]!)
    (hidx_cl : ∀ e ∈ idx, e.ClosedN (k + xs.length + Ds.length))
    (hidx_c : ∀ e ∈ idx, ConstsIn (Dom envJ) e)
    (hxs'_d : ∀ x ∈ xs', ConstsIn (Dom env₁) x) (hxs'_m : ∀ x ∈ xs', mentions b.names x = false)
    (hidx'_d : ∀ x ∈ idx', ConstsIn (Dom env₁) x) (hidx'_m : ∀ x ∈ idx', mentions b.names x = false)
    (ys : List V) (hys : ys.length = k) (ρp : List V) :
    fdom M ls X f' (ys.reverse ++ ρp) =
      fdom MJ (lv.map (VLevel.eval ls)) Y fJ (ys.reverse ++ keyArgs (M₁ M b C₀) ls Ds ρp) := by
  obtain ⟨hlen, hget⟩ := EqLTel.get hxs
  unfold fdom
  rw [hcb, hcJ]
  simp only
  apply piTel_transfer
  · exact hlen
  · intro i h h' zs hzs
    have hzl : zs.length = i := by rw [Ext.length_eq _ _ hzs]; simp; omega
    have exs : xs[i] = xs[i]! := by
      rw [← getElem_eq_getElem! h']
    have hmem : xs'[i] ∈ xs' := List.getElem_mem h
    have hx := hget i h h'
    rw [exs] at hx ⊢
    rw [← List.append_assoc, ← List.append_assoc]
    exact interp_key_base S cJ hx (hxs_cl i h') (hxs_c i h') (hxs'_d _ hmem)
      (hxs'_m _ hmem) (zs.reverse ++ ys.reverse) (by simp [hzl, hys]; omega) ρp
  · intro zs hzs
    have hzl : zs.length = xs.length := by rw [Ext.length_eq _ _ hzs]
    rw [hXY]
    congr 2
    refine forall₂_map_eq hidx fun e he e' he' h => ?_
    rw [← List.append_assoc, ← List.append_assoc]
    exact interp_key_base S cJ h (hidx_cl e' he') (hidx_c e' he') (hidx'_d _ he) (hidx'_m _ he)
      (zs.reverse ++ ys.reverse) (by simp [hzl, hys]; omega) ρp

include S cJ in
theorem cidx_corr {C₀ : List Nat → List V → Nat → V} {ls : List Nat} {cb cJc : SCtor}
    (hidx : List.Forall₂ (fun e e' => e.EqL (atKey lv Ds cb.fields.length e')) cb.idx cJc.idx)
    (hcl : ∀ e ∈ cJc.idx, e.ClosedN (cb.fields.length + Ds.length))
    (hc : ∀ e ∈ cJc.idx, ConstsIn (Dom envJ) e)
    (hd : ∀ x ∈ cb.idx, ConstsIn (Dom env₁) x) (hm : ∀ x ∈ cb.idx, mentions b.names x = false)
    (fs : List V) (hfs : fs.length = cb.fields.length) (ρp : List V) :
    cidx M ls ρp cb fs = cidx MJ (lv.map (VLevel.eval ls)) (keyArgs (M₁ M b C₀) ls Ds ρp)
        cJc fs := by
  unfold cidx
  congr 1
  exact forall₂_map_eq hidx fun e he e' he' h => interp_key_base S cJ h (hcl e' he') (hc e' he')
    (hd _ he) (hm _ he) fs.reverse (by simp [hfs]) ρp

end Fields

end Soulgem.Nested
