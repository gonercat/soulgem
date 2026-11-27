import Soulgem.Model.NestedOp
import Soulgem.Model.BlockFinal

/-! # The block's semantics depends on the base model only through the environment -/

namespace Soulgem.BlockModel
open ConLeche ConLeche.SetTheory ConLeche.SetTheory.Tower Lean4Lean Spec BlockSem Nested

universe u
variable {V : Type u} [SetTheory V]

namespace Setting
variable {M : CInterp V} {env env₁ : VEnv} {b : SBlock} (S : Setting M env env₁ b)
  {M' : CInterp V} (hag : ∀ c, Dom env c → M c = M' c)
include S hag

theorem base_free {e : VExpr} (h₁ : ConstsIn (Dom env₁) e) (hm : mentions b.names e = false) :
    ConstsIn (fun c => M c = M' c) e :=
  (h₁.and (constsIn_of_mentions hm)).mono fun _ ⟨h1, h2⟩ => hag _ (S.dom_of_dom₁ h1 h2)

theorem Is_base (ls : List Nat) (ρp : List V) (m : Nat) : Is M ls b ρp m = Is M' ls b ρp m := by
  have hind : ∀ A ∈ (b.types[m]!).indices, ConstsIn (fun c => M c = M' c) A := by
    by_cases hm : m < b.ntypes
    · exact fun A hA => (S.indices_consts hm A hA).mono hag
    · rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_none (by simpa [SBlock.ntypes] using hm)]
      intro A hA; cases hA
  apply SetTheory.ext; intro t
  simp only [Is, mem_extSet, Ext.congrM (fun _ h => h) hind]

theorem fdom_base {ls : List Nat} {j : Nat} (hj : j < b.ntypes) {c : SCtor}
    (hc : c ∈ (b.types[j]!).ctors) {a : Nat} (ha : a < c.fields.length) (X : Nat → V)
    (ρ : List V) : fdom M ls X (c.fields[a]!) ρ = fdom M' ls X (c.fields[a]!) ρ := by
  have hfok := S.field_full hj hc ha
  have hctx := S.fctx_consts hj hc a (Nat.le_of_lt ha)
  unfold FieldFull at hfok
  unfold fdom
  split at hfok
  · rename_i w hcert
    rw [hcert]
    obtain ⟨⟨_, hd⟩, hm⟩ := hfok
    exact interp_congr ((S.base_free hag (IsDefEq.constsIn S.good₁.2 hd hctx).2.1 hm).mono
      fun _ h => h) ρ
  · rename_i xs k idx hcert
    rw [hcert]
    obtain ⟨-, -, ⟨_, hd⟩, hxs, hidx, -⟩ := hfok
    have hcR := (constsIn_forallTel xs _).mp (IsDefEq.constsIn S.good₁.2 hd hctx).2.1
    have hci : ∀ i ∈ idx, ConstsIn (Dom env₁) i := fun i hi =>
      ((constsIn_appN _ _).mp hcR.2).2 i (List.mem_append_right _ hi)
    simp only
    rw [piTel_congrM (fun _ h => h) fun A hA => S.base_free hag (hcR.1 A hA) (hxs A hA)]
    refine piTel_congr fun ys _ => ?_
    congr 2
    exact List.map_congr_left fun i hi => interp_congr (S.base_free hag (hci i hi) (hidx i hi)) _

theorem cidx_base {ls : List Nat} {j : Nat} (hj : j < b.ntypes) {c : SCtor}
    (hc : c ∈ (b.types[j]!).ctors) (ρp fs : List V) :
    cidx M ls ρp c fs = cidx M' ls ρp c fs := by
  have hidxm := (S.ctorSyn hj hc).idx_free
  have hidxty := (S.ctorOK j hj c hc).idx_typed
  have hctx := S.fctx_consts hj hc c.fields.length (Nat.le_refl _)
  have hfctx : fctx b c c.fields.length = (b.params ++ c.fields.map (·.ty)).reverse := by
    simp [fctx]
  have hci : ∀ i ∈ c.idx, ConstsIn (Dom env₁) i := fun i hi => by
    obtain ⟨l, hl', rfl⟩ := List.mem_iff_getElem.mp hi
    have := hidxty l hl'
    have e : c.idx[l]! = c.idx[l] := by
      rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hl']; rfl
    rw [e] at this
    exact (IsDefEq.constsIn S.good₁.2 this (by rw [← hfctx]; exact hctx)).1
  unfold cidx
  congr 1
  exact List.map_congr_left fun i hi => interp_congr (S.base_free hag (hci i hi) (hidxm i hi)) _

theorem Φ_base (ls : List Nat) (ρp : List V) (X : Nat → V) (m : Nat) :
    Φ M ls b ρp X m = Φ M' ls b ρp X m := by
  have H : CtorCorr M M' ls ls b b ρp ρp X X m m := by
    by_cases hm : m < b.ntypes
    · have hcm : ∀ q (hq : q < (ctorsOf b m).length), (ctorsOf b m)[q] ∈ (b.types[m]!).ctors :=
        fun q hq => List.getElem_mem hq
      refine ⟨rfl, fun q hq fs => ?_, fun q hq fs _ => S.cidx_base hag hm (hcm q hq) ρp fs⟩
      refine ffit_congr _ _ ρp ρp rfl (fun k hk ys _ _ _ => ?_) fs
      exact S.fdom_base hag hm (hcm q hq) hk X _
    · have hnil : ctorsOf b m = [] := by
        unfold ctorsOf
        rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_none
            (by simpa [SBlock.ntypes] using hm)]
        rfl
      exact ⟨rfl, fun q hq => absurd hq (by simp [hnil]), fun q hq => absurd hq (by simp [hnil])⟩
  unfold Φ
  rw [S.Is_base hag ls ρp m]
  congr 1
  funext i
  exact fib_congr rfl H i

theorem carrier_base (ls : List Nat) (ρp : List V) : carrier M ls b ρp = carrier M' ls b ρp := by
  unfold carrier
  have hI : Is M ls b ρp = Is M' ls b ρp := funext (S.Is_base hag ls ρp)
  have hΦ : Φ M ls b ρp = Φ M' ls b ρp := funext fun X => funext (S.Φ_base hag ls ρp X)
  rw [hI, hΦ]

theorem former_base (C : List Nat → List V → Nat → V) (j : Nat) (ls : List Nat) :
    former M b C j ls = former M' b C j ls := by
  have hind : ∀ A ∈ (b.types[j]!).indices, ConstsIn (Dom env) A := by
    by_cases hj : j < b.ntypes
    · exact S.indices_consts hj
    · rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_none (by simpa [SBlock.ntypes] using hj)]
      intro A hA; cases hA
  unfold former
  rw [lamTel_congrM' hag S.params_consts']
  congr 1; funext ρp
  exact lamTel_congrM' hag hind

theorem M₁_base (C : List Nat → List V → Nat → V) {c : Name} (hc : Dom env₁ c) :
    M₁ M b C c = M₁ M' b C c := by
  funext ls
  unfold M₁
  split
  · exact S.former_base hag C _ ls
  · rename_i hn
    have hnm : c ∉ b.names := fun hm => hn (by
      rw [← names_length]; exact findName_lt_of_mem hm)
    rw [hag c (S.dom_of_dom₁ hc hnm)]

theorem Mc_base {c : Name} (hc : Dom env₁ c) : Mc M b c = Mc M' b c := by
  have hC : (fun ls ρp => carrier M ls b ρp) = fun ls ρp => carrier M' ls b ρp :=
    funext fun ls => funext fun ρp => S.carrier_base hag ls ρp
  show M₁ M b (fun ls ρp => carrier M ls b ρp) c = M₁ M' b (fun ls ρp => carrier M' ls b ρp) c
  rw [hC]; exact S.M₁_base hag _ hc

theorem ctorVal_base {j : Nat} (hj : j < b.ntypes) {c : SCtor} (hc : c ∈ (b.types[j]!).ctors)
    (ls : List Nat) (q : Nat) : ctorVal b (Mc M b) ls q c = ctorVal b (Mc M' b) ls q c := by
  have hag₁ : ∀ x, Dom env₁ x → Mc M b x = Mc M' b x := fun x hx => S.Mc_base hag hx
  have hfs : ∀ A ∈ c.fields.map (·.ty), ConstsIn (Dom env₁) A := by
    intro A hA
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hA
    obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem hf
    have e : c.fields[a]! = c.fields[a] := by
      rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem ha]; rfl
    have := (S.field_ok hj hc ha).1
    rw [e] at this
    rw [← e] at this ⊢
    exact (IsDefEq.constsIn S.good₁.2 this (S.fctx_consts hj hc a (Nat.le_of_lt ha))).1
  unfold ctorVal
  rw [lamTel_congrM' hag₁ fun A hA => (S.params_consts' A hA).mono fun _ h => Dom.mono S.le₁ h]
  congr 1; funext ρ
  exact lamTel_congrM' hag₁ hfs

theorem M₂_base {x : Name} (hx : x ∈ b.ctors.map (·.name) ∨ Dom env₁ x) :
    M₂ M b x = M₂ M' b x := by
  funext ls
  unfold M₂
  split
  · rename_i p hp
    have hmem := List.mem_of_find?_eq_some hp
    obtain ⟨j, hj, hq⟩ : ∃ j, j < b.ntypes ∧ p.2 < (ctorsOf b p.1).length ∧ p.1 = j := by
      obtain ⟨j, hj, hpm⟩ := List.mem_flatMap.mp hmem
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hpm
      exact ⟨j, List.mem_range.mp hj, List.mem_range.mp hq, rfl⟩
    have hc : ctorAt b p ∈ (b.types[p.1]!).ctors := by
      have e : (ctorsOf b p.1)[p.2]! = (ctorsOf b p.1)[p.2] := by
        rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hq.1]; rfl
      show (ctorsOf b p.1)[p.2]! ∈ ctorsOf b p.1
      rw [e]; exact List.getElem_mem hq.1
    exact S.ctorVal_base hag (hq.2 ▸ hj) hc ls p.2
  · rename_i hp
    rcases hx with hx | hx
    · exfalso
      rw [← ctorPos_names] at hx
      obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hx
      have := List.find?_eq_none.mp hp p hp'
      simp at this
    · exact congrFun (S.Mc_base hag hx) ls

end Setting
end Soulgem.BlockModel
