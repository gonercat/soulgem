import Soulgem.Model.BlockMotive

/-! # The recursor's binders -/

namespace Soulgem
open ConLeche ConLeche.SetTheory ConLeche.SetTheory.Tower Lean4Lean Spec

universe u
variable {V : Type u} [SetTheory V]

/-! ## Constants of placed fragments -/

theorem constsIn_remap {P : Name → Prop} (g : Nat → Nat) :
    ∀ (e : VExpr) (k : Nat), ConstsIn P (remap g e k) ↔ ConstsIn P e
  | .bvar i, k => by simp only [remap]; split <;> simp [ConstsIn]
  | .sort _, _ | .const _ _, _ => by simp only [remap]
  | .app f a, k | .lam f a, k | .forallE f a, k => by
    simp only [remap, ConstsIn, constsIn_remap g f, constsIn_remap g a]

theorem constsIn_place {P : Name → Prop} (d0 : Nat) (σ : Nat → Nat) (d : Nat) (e : VExpr) :
    ConstsIn P (place d0 σ d e) ↔ ConstsIn P e := constsIn_remap _ e 0

theorem constsIn_consumeAnn {P : Name → Prop} (e : VExpr) (h : ConstsIn P e) :
    ConstsIn P (consumeAnn e) := by
  unfold consumeAnn
  split
  · exact constsIn_consumeAnn _ h.1.2
  · exact constsIn_consumeAnn _ h.1.2
  · exact constsIn_consumeAnn _ h.2
  · exact constsIn_consumeAnn _ h.2
  · exact h

theorem constsIn_binder {P : Name → Prop} (b : SBlock) {e : VExpr} (h : ConstsIn P e) :
    ConstsIn P (b.binder e) :=
  constsIn_consumeAnn _ (constsIn_instL.mpr h)

theorem constsIn_sh {P : Name → Prop} (b : SBlock) {e : VExpr} (h : ConstsIn P e) :
    ConstsIn P (b.sh e) := constsIn_instL.mpr h

theorem constsIn_vars {P : Name → Prop} (d L n : Nat) : ∀ a ∈ vars d L n, ConstsIn P a := by
  intro a ha
  simp only [vars, List.mem_map] at ha
  obtain ⟨_, _, rfl⟩ := ha
  trivial

/-! ## Positions in a concatenation over a range -/

theorem sum_range_lt {f : Nat → Nat} {j K : Nat} (hj : j < K) {q : Nat} (hq : q < f j) :
    ((List.range j).map f).sum + q < ((List.range K).map f).sum := by
  induction K with
  | zero => omega
  | succ K ih =>
    rw [List.range_succ, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    by_cases h : j < K
    · have := ih h; omega
    · have e : j = K := by omega
      subst e; omega

theorem flatMap_range_getElem? {α : Type _} (F : Nat → List α) :
    ∀ {K j q : Nat}, j < K → q < (F j).length →
      ((List.range K).flatMap F)[((List.range j).map fun i => (F i).length).sum + q]? = (F j)[q]?
  | 0, _, _, hj, _ => absurd hj (Nat.not_lt_zero _)
  | K + 1, j, q, hj, hq => by
    rw [List.range_succ, List.flatMap_append]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    have hlen : ((List.range K).flatMap F).length = ((List.range K).map fun i =>
        (F i).length).sum := by
      rw [List.length_flatMap]
    by_cases h : j < K
    · rw [List.getElem?_append_left (by rw [hlen]; exact sum_range_lt h hq)]
      exact flatMap_range_getElem? F h hq
    · have e : j = K := by omega
      subst e
      rw [List.getElem?_append_right (by rw [hlen]; omega), hlen, Nat.add_sub_cancel_left]

theorem sum_take_map {α : Type _} [Inhabited α] (l : List α) (f : α → Nat) {j : Nat}
    (hj : j ≤ l.length) :
    ((l.take j).map f).sum = ((List.range j).map fun i => f l[i]!).sum := by
  congr 1
  apply List.ext_getElem (by simp; omega)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_take, List.getElem_range]
  have hi : i < l.length := by simp at h2; omega
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl

namespace BlockModel
open BlockSem

abbrev minorList (b : SBlock) : List VExpr :=
  (List.range b.ntypes).flatMap fun j =>
    let cs := (b.types[j]!).ctors
    (List.range cs.length).map fun q => b.minorTy j cs[q]! (b.nparams + b.ntypes + b.ctorBase j + q)

theorem ctorBase_eq (b : SBlock) {j : Nat} (hj : j ≤ b.ntypes) :
    b.ctorBase j = ((List.range j).map fun i => (b.types[i]!).ctors.length).sum := by
  unfold SBlock.ctorBase
  exact sum_take_map b.types (·.ctors.length) hj

theorem minorList_length (b : SBlock) : (minorList b).length = b.nctors := by
  unfold SBlock.nctors SBlock.ctors
  rw [List.length_flatMap, List.length_flatMap]
  simp only [List.length_map, List.length_range]
  have := sum_take_map b.types (·.ctors.length) (Nat.le_refl _)
  rw [List.take_length] at this
  exact this.symm

theorem minorList_getElem? (b : SBlock) {j q : Nat} {c : SCtor} (hcq : (ctorsOf b j)[q]? = some c) :
    (minorList b)[b.ctorBase j + q]? =
      some (b.minorTy j c (b.nparams + b.ntypes + b.ctorBase j + q)) := by
  have hj := lt_of_ctor hcq
  obtain ⟨hq, hc⟩ := List.getElem?_eq_some_iff.mp hcq
  unfold minorList
  rw [ctorBase_eq b (Nat.le_of_lt hj)]
  have := flatMap_range_getElem? (fun j =>
    (List.range (b.types[j]!).ctors.length).map fun q =>
      b.minorTy j (b.types[j]!).ctors[q]! (b.nparams + b.ntypes + b.ctorBase j + q))
    (K := b.ntypes) (j := j) (q := q) hj (by
        simp only [List.length_map, List.length_range]; exact hq)
  simp only [List.length_map, List.length_range] at this
  rw [this, List.getElem?_map, List.getElem?_range (by exact hq)]
  simp only [Option.map_some]
  congr 1
  have e : (b.types[j]!).ctors[q]! = c := by
    rw [show (b.types[j]!).ctors = ctorsOf b j from rfl, List.getElem!_eq_getElem?_getD, hcq]; rfl
  rw [e, ctorBase_eq b (Nat.le_of_lt hj)]

namespace Setting
variable {M : CInterp V} {env env₁ : VEnv} {b : SBlock} (S : Setting M env env₁ b)
include S

theorem type_dom {j : Nat} (hj : j < b.ntypes) : Dom env₁ (b.types[j]!).name := by
  have h := S.hwt; rw [withTypes_eq] at h
  obtain ⟨_, _, _, _, _, hex⟩ := addFold_spec h
  obtain ⟨ci, hci⟩ := hex ((b.types[j]'hj).name, _) (List.mem_map.mpr ⟨_, List.getElem_mem hj, rfl⟩)
  rw [getElem!_types hj]
  simp [Dom, hci]

theorem motiveTy_consts {j : Nat} (hj : j < b.ntypes) : ConstsIn (Dom env₁) (b.motiveTy j) := by
  unfold SBlock.motiveTy
  simp only []
  rw [constsIn_forallTel]
  refine ⟨fun A hA => ?_, ?_⟩
  · simp only [List.mem_map, List.mem_range] at hA
    obtain ⟨a, ha, rfl⟩ := hA
    refine constsIn_binder b ((constsIn_place _ _ _ _).mpr ?_)
    have ha' : a < (b.types[j]!).indices.length := by simpa using ha
    have e : (b.types[j]!).indices[a]! = (b.types[j]!).indices[a] := by
      rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem ha']; rfl
    rw [e]
    exact (S.indices_consts hj _ (List.getElem_mem ha')).mono fun _ => Dom.mono S.le₁
  · refine ⟨?_, trivial⟩
    unfold SBlock.tconst
    rw [constsIn_appN]
    exact ⟨S.type_dom hj, fun a ha => by
      rcases List.mem_append.mp ha with h | h <;> exact constsIn_vars _ _ _ a h⟩

theorem interp_motiveTy' {M' : CInterp V} (hag : ∀ x, Dom env₁ x → M' x = Mc M b x)
    {ls' : List Nat} {ps : List V} (hps : Ext M (blev b ls') b.params [] ps)
    {j : Nat} (hj : j < b.ntypes) {mots₀ : List V} (hm0 : mots₀.length = j) :
    interp M' ls' (b.motiveTy j) (mots₀.reverse ++ ps.reverse) =
      motSp M b (blev b ls') ps (elimLev b ls') j := by
  rw [interp_congr ((S.motiveTy_consts hj).mono hag), S.interp_motiveTy hps hj hm0]

theorem ext_params {M' : CInterp V} (hag : ∀ x, Dom env₁ x → M' x = Mc M b x)
    (hM' : IsModel M' env₁) {ls' : List Nat} (ps : List V) :
    Ext M' ls' ((List.range b.nparams).map fun i => b.binder b.params[i]!) [] ps ↔
      Ext M (blev b ls') b.params [] ps := by
  have hagM : ∀ A ∈ b.params, ConstsIn (fun x => M x = M' x) A := fun A hA =>
    ((S.free₀ (C := fun ls ρp => carrier M ls b ρp) (S.params_consts' A hA)).and
      ((S.params_consts' A hA).mono fun _ => Dom.mono S.le₁)).mono fun x ⟨h1, h2⟩ =>
        (h1.symm.trans (hag x h2).symm)
  refine ext_transfer (by simp; rfl) fun i hi hi' ys hys => ?_
  have hi2 : i < b.params.length := hi'
  simp only [List.getElem_map, List.getElem_range, List.append_nil]
  obtain ⟨_, ⟨_, hdf⟩⟩ := S.hwf.params i hi2
  have hys' := (Ext.congrM (fun x h => h) fun A hA => hagM A (List.mem_of_mem_take hA)).mp hys
  have hsat := Sat.of_ext (Γ := []) (ρ := []) trivial hys'
  simp only [List.append_nil] at hsat
  unfold SBlock.binder SBlock.sh
  rw [consumeAnn_instL, interp_instL, ← ((hM'.sound (hdf.mono S.le₁) _ _ hsat).1)]
  have e : b.params[i]! = b.params[i] := by
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi2]; rfl
  rw [e, interp_congr ((hagM _ (List.getElem_mem hi2)).mono fun _ h => h.symm)]

theorem ext_indices {M' : CInterp V} (hag : ∀ x, Dom env₁ x → M' x = Mc M b x)
    (hM' : IsModel M' env₁) {ls' : List Nat} {ps : List V} (hps : Ext M (blev b ls') b.params [] ps)
    {d : Nat} (hd : d < b.ntypes) {mid : List V} {D : Nat} (hD : ps.length + mid.length = D)
    (zs : List V) :
    Ext M' ls' ((List.range (b.types[d]!).indices.length).map fun a =>
        b.binder (place (b.nparams + a) (b.σ1 D) (D + a) (b.types[d]!).indices[a]!))
      (ps ++ mid).reverse zs ↔ Ext M (blev b ls') (b.types[d]!).indices ps.reverse zs := by
  have hplen : ps.length = b.nparams := by rw [Ext.length_eq M _ hps]; rfl
  have hagM : ∀ A ∈ b.params ++ (b.types[d]!).indices, ConstsIn (fun x => M x = M' x) A :=
    fun A hA => by
      have h0 : ConstsIn (Dom env) A := by
        rcases List.mem_append.mp hA with h | h
        · exact S.params_consts' A h
        · exact S.indices_consts hd A h
      exact ((S.free₀ (C := fun ls ρp => carrier M ls b ρp) h0).and
        (h0.mono fun _ => Dom.mono S.le₁)).mono fun x ⟨h1, h2⟩ => h1.symm.trans (hag x h2).symm
  have hps' := (Ext.congrM (fun x h => h) fun A hA => hagM A (List.mem_append_left _ hA)).mp hps
  have hpsat : Sat M' (blev b ls') b.params.reverse ps.reverse := by
    simpa using Sat.of_ext (Γ := []) (ρ := []) trivial hps'
  refine ext_transfer (by simp) fun a ha ha' ys hys => ?_
  have hya : ys.length = a := by
    rw [Ext.length_eq _ _ hys, List.length_take]; exact Nat.min_eq_left (Nat.le_of_lt ha')
  have hrev : ys.reverse ++ (ps ++ mid).reverse = (ps ++ mid ++ ys).reverse := by simp
  rw [hrev]
  simp only [List.getElem_map, List.getElem_range]
  have hys' := (Ext.congrM (fun x h => h) fun A hA =>
    hagM A (List.mem_append_right _ (List.mem_of_mem_take hA))).mp hys
  have hsat0 := Sat.of_ext hpsat hys'
  have hΓ : CtxClosed (((b.types[d]!).indices.take a).reverse ++ b.params.reverse) := by
    have := tel_closed S.hG.1 S.params_ctx_closed (S.indices_ok hd) a
      (by have := ha'; rw [getElem!_types hd] at this; omega)
    rwa [← getElem!_types hd] at this
  have hΓ' : CtxClosed (((b.types[d]!).indices.take a).reverse ++ b.params.reverse) := hΓ
  rw [interp_binder_place hM' S.good₁.1 ls' b hΓ' (b.nparams + a)
    (by simp only [List.length_append, List.length_reverse, List.length_take,
      Nat.min_eq_left (Nat.le_of_lt ha')]; rw [Nat.add_comm]; rfl)
    (b.σ1 D) (D + a) _ (S.index_annOK hd ha') (ps ++ mid ++ ys)
    (by simp only [List.length_append]; omega)
    (fun L hL => by unfold SBlock.σ1; split <;> omega)
    (by rw [pull_σ1 b hplen hD a hya]; simpa using hsat0)]
  rw [pull_σ1 b hplen hD a hya, List.reverse_append]
  have e : (b.types[d]!).indices[a]! = (b.types[d]!).indices[a] := by
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem ha']; rfl
  rw [e, interp_congr ((hagM _ (List.mem_append_right _ (List.getElem_mem ha'))).mono
    fun _ h => h.symm)]

theorem interp_major {M' : CInterp V} (hag : ∀ x, Dom env₁ x → M' x = Mc M b x)
    {ls' : List Nat} {ps : List V} (hps : Ext M (blev b ls') b.params [] ps)
    {d : Nat} (hd : d < b.ntypes) {mid is : List V} {D : Nat} (hD : ps.length + mid.length = D)
    (his : Ext M (blev b ls') (b.types[d]!).indices ps.reverse is) :
    interp M' ls' (appN (b.tconst d) (vars (D + (b.types[d]!).indices.length) 0 b.nparams ++
        vars (D + (b.types[d]!).indices.length) D (b.types[d]!).indices.length))
      (ps ++ mid ++ is).reverse = app (carrier M (blev b ls') b ps.reverse d) (mkTower is) := by
  have hplen : ps.length = b.nparams := by rw [Ext.length_eq M _ hps]; rfl
  have hm : is.length = (b.types[d]!).indices.length := Ext.length_eq M _ his
  have hW : (ps ++ mid ++ is).length = D + (b.types[d]!).indices.length := by
    simp only [List.length_append]; omega
  rw [interp_appN, List.map_append, interp_vars _ _ hW (by omega), interp_vars _ _ hW (by omega)]
  simp only [SBlock.tconst, interp]
  rw [hag _ (S.type_dom hd), show Mc M b = M₁ M b (fun ls ρp => carrier M ls b ρp) from rfl,
    getElem!_types hd, M₁_type S.nodup hd, ← getElem!_types hd]
  have e1 : ((ps ++ mid ++ is).drop 0).take b.nparams = ps := by
    simp [hplen]
  have e2 : ((ps ++ mid ++ is).drop D).take (b.types[d]!).indices.length = is := by
    rw [← hm, show D = (ps ++ mid).length by simp; omega, List.drop_left, List.take_length]
  rw [e1, e2, apps_former hps his]

end Setting

end BlockModel
end Soulgem
