import Soulgem.Model.TeleSat
import Soulgem.Model.BlockTypes

/-! # Reading the declared field types in the model -/

namespace Soulgem.BlockModel
open ConLeche ConLeche.SetTheory ConLeche.SetTheory.Tower Lean4Lean Spec BlockSem

universe u
variable {V : Type u} [SetTheory V] {M : CInterp V} {b : SBlock} {ls : List Nat}
  {C : List Nat → List V → Nat → V}

theorem ownLevels_eval (hl : ls.length = b.uvars) : (ownLevels b.uvars).map (VLevel.eval ls) = ls :=
  map_eval_params hl

theorem getElem!_types {j : Nat} (hj : j < b.ntypes) : b.types[j]! = b.types[j]'hj := by
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (show j < b.types.length from hj)]
  rfl

theorem apps_former {k : Nat} {ps is : List V} (hps : Ext M ls b.params [] ps)
    (his : Ext M ls (b.types[k]!).indices ps.reverse is) :
    (ps ++ is).foldl app (former M b C k ls) = app (C ls ps.reverse k) (mkTower is) := by
  unfold former
  rw [List.foldl_append, apps_lamTel hps]
  simp only [List.append_nil]
  rw [apps_lamTel his]
  have hlen : is.length = nidx b k := by rw [Ext.length_eq M ls his]; rfl
  rw [List.take_append_of_le_length (by simp [hlen]), List.take_of_length_le (by simp [hlen])]
  simp

theorem interp_indApp (hnd : b.names.Nodup) (hl : ls.length = b.uvars) {k d : Nat}
    (hk : k < b.ntypes) {idx : List VExpr} {zs : List V} (hzl : zs.length = d)
    (hn : b.nparams ≤ d) (hps : Ext M ls b.params [] (zs.take b.nparams))
    (his : Ext M ls (b.types[k]!).indices (zs.take b.nparams).reverse
      (idx.map (interp (M₁ M b C) ls · zs.reverse))) :
    interp (M₁ M b C) ls (b.indApp k d idx) zs.reverse =
      app (C ls (zs.take b.nparams).reverse k)
        (mkTower (idx.map (interp (M₁ M b C) ls · zs.reverse))) := by
  unfold SBlock.indApp
  rw [interp_appN, List.map_append, interp_vars _ _ hzl (by omega)]
  simp only [interp, List.drop_zero]
  rw [ownLevels_eval hl, getElem!_types hk, M₁_type hnd hk]
  exact apps_former hps his

theorem getD_append_reverse {xs ys : List V} {i : Nat} (h : i < xs.length) :
    (xs.reverse ++ ys).getD i pt = xs.getD (xs.length - 1 - i) pt := by
  rw [getD_append_left' (by simpa using h), getD_reverse h]

def idxSub (E : Nat) (idx : List VExpr) (l : Nat) (i : Nat) : VExpr :=
  if i < l then idx[l - 1 - i]! else .bvar (E + (i - l))

theorem idxType_eq (j E : Nat) (idx : List VExpr) (l : Nat) :
    b.idxType j E idx l = subst (idxSub E idx l) ((b.types[j]!).indices[l]!) := rfl

theorem idx_fit_gen {env₁ : VEnv} {M' : CInterp V} (hM' : IsModel M' env₁) {U E : Nat}
    {Γ : List VExpr} {zs : List V} (hΓ : Sat M' ls Γ zs.reverse) {n : Nat}
    (hzl : zs.length = n + E) {Is idx : List VExpr} (hil : idx.length = Is.length)
    (hty : ∀ l < idx.length, env₁.HasType U Γ idx[l]! (subst (idxSub E idx l) Is[l]!))
    (hcl : ∀ l < Is.length, (Is[l]!).ClosedN (n + l))
    (hfree : ∀ A ∈ Is, ConstsIn (fun c => M' c = M c) A) :
    Ext M ls Is (zs.take n).reverse (idx.map (interp M' ls · zs.reverse)) := by
  refine Ext.of_get (by simp [hil]) fun l h1 h2 => ?_
  have hl : l < idx.length := by simpa using h2
  have hmem := (hM'.sound (hty l hl) ls _ hΓ).2
  have e1 : (idx.map (interp M' ls · zs.reverse))[l] = interp M' ls idx[l]! zs.reverse := by
    simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hl]
  have e2 : Is[l]! = Is[l] := by
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem h1]; rfl
  rw [e1, ← interp_congr (hfree _ (List.getElem_mem h1))]
  have hsub := interp_subst M' ls (idxSub E idx l) Is[l]! 0 (n + l) [] zs.reverse
    (((idx.map (interp M' ls · zs.reverse)).take l).reverse ++ (zs.take n).reverse)
    (by simpa using hcl l h1) rfl ?_
  · simp only [List.nil_append] at hsub
    rw [hsub, e2] at hmem
    exact hmem
  intro i hi
  unfold idxSub
  by_cases hil' : i < l
  · simp only [hil', ite_true]
    have hlt : i < ((idx.map (interp M' ls · zs.reverse)).take l).length := by simp; omega
    rw [getD_append_reverse hlt]
    simp only [List.length_take, List.length_map]
    rw [Nat.min_eq_left (by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem!_eq_getElem?_getD, show l - 1 - i < l by omega, List.getElem?_eq_getElem
        (show l - 1 - i < idx.length by omega)]
  · simp only [hil', ite_false, interp]
    have hlen : ((idx.map (interp M' ls · zs.reverse)).take l).reverse.length = l := by
      simp; omega
    rw [getD_append_right' (by rw [hlen]; omega), hlen]
    have hz : zs = zs.take n ++ zs.drop n := (List.take_append_drop _ _).symm
    conv => rhs; rw [hz]
    rw [List.reverse_append, getD_append_right' (by simp; omega)]
    simp only [List.length_reverse, List.length_drop, hzl]
    congr 1; omega

end Soulgem.BlockModel
