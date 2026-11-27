import Soulgem.Model.NestedScope
import Soulgem.Model.NestedShift
import Soulgem.Model.NestedTop

/-! # The model of a nested block -/

namespace Soulgem.Nested
open ConLeche ConLeche.SetTheory ConLeche.SetTheory.Tower Lean4Lean Spec BlockSem BlockModel

universe u
variable {V : Type u} [SetTheory V]

theorem eq_of_nodup_map {α β : Type _} (f : α → β) : ∀ {l : List α}, (l.map f).Nodup →
    ∀ {a a' : α}, a ∈ l → a' ∈ l → f a' = f a → a' = a
  | [], _, _, _, ha, _, _ => by simp at ha
  | x :: xs, hnd, a, a', ha, ha', h => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    rcases List.mem_cons.mp ha with rfl | hx <;> rcases List.mem_cons.mp ha' with rfl | hx'
    · rfl
    · exact absurd ⟨a', hx', h⟩ hnd.1
    · exact absurd ⟨a, hx, h.symm⟩ hnd.1
    · exact eq_of_nodup_map f hnd.2 hx hx' h

theorem addFold_get {env env' : VEnv} {cs : List (Name × VConstant)}
    (h : addFold env cs = some env')
    {x : Name × VConstant} (hx : x ∈ cs) : env'.constants x.1 = some x.2 := by
  obtain ⟨hfresh, _, _, hcs, hnd, hex⟩ := addFold_spec h
  obtain ⟨ci, hci⟩ := hex x hx
  rcases hcs _ _ hci with ⟨y, hy, hyx, hyc⟩ | henv
  · rw [hci, ← hyc, eq_of_nodup_map (·.1) hnd hx hy hyx]
  · rw [hfresh x hx] at henv; cases henv

theorem addFold_dom {env env' : VEnv} {cs : List (Name × VConstant)}
    (h : addFold env cs = some env') {x : Name × VConstant} (hx : x ∈ cs) : Dom env' x.1 := by
  unfold Dom; rw [addFold_get h hx]; nofun

section CtorParams
variable {M : CInterp V} {env env₁ : VEnv} {b : SBlock} (S : Setting M env env₁ b)
include S

theorem _root_.Soulgem.BlockModel.Setting.ctor_params_ext {M' : CInterp V}
    (hag : ∀ x, Dom env₁ x → M' x = Setting.Mc M b x)
    {Ps : List VExpr} (hPl : Ps.length = b.nparams)
    (hPd : ∀ i < b.nparams, DefEqTy env₁ b.uvars (b.params.take i).reverse Ps[i]! b.params[i]!)
    (ls : List Nat) {ys : List V} (hys : Ext M' ls Ps [] ys) : Ext M ls b.params [] ys := by
  have hC := carrier_tupleFn M b
  have hM₁ := S.model₁ hC
  have hM' : IsModel M' env₁ := IsModel.congr hM₁.1 hM₁.2 hag
  have h1 : Ext M' ls Ps [] ys ↔ Ext M' ls b.params [] ys :=
    ext_transfer (by rw [hPl]; rfl) fun i hi hi' zs hzs => by
      obtain ⟨_, hd⟩ := hPd i (by rw [← hPl]; exact hi)
      have hsat := Sat.of_ext (Γ := []) (ρ := []) trivial hzs
      have := (hM'.sound hd ls _ (by simpa using hsat)).1
      have e1 : Ps[i]! = Ps[i] := by
        rw [← getElem_eq_getElem! hi]
      have e2 : b.params[i]! = b.params[i] := by
        rw [← getElem_eq_getElem! hi']
      rw [e1, e2] at this
      simpa using this
  refine (Ext.congrM (fun _ h => h) fun A hA => ?_).mpr (h1.mp hys)
  exact (S.params_consts' A hA).mono fun x hx => by
    rw [hag x (Dom.mono S.le₁ hx)]; exact (S.agree hx).symm

end CtorParams

theorem scoped_tel_inv {P : Name → Prop} (lam : Bool) : ∀ {As : List VExpr} {R : VExpr} {k : Nat},
    Scoped P k (if lam then Spec.lamTel As R else Spec.forallTel As R) →
    (∀ i (h : i < As.length), Scoped P (k + i) As[i]) ∧ Scoped P (k + As.length) R
  | [], R, k, h => by cases lam <;> exact ⟨nofun, by simpa [Spec.lamTel, Spec.forallTel] using h⟩
  | A :: As, R, k, h => by
    have hA : Scoped P k A ∧ Scoped P (k + 1) (if lam then Spec.lamTel As R else
        Spec.forallTel As R) := by
      cases lam <;> exact ⟨⟨h.1.1, h.2.1⟩, ⟨h.1.2, h.2.2⟩⟩
    obtain ⟨hAs, hR⟩ := scoped_tel_inv lam hA.2
    refine ⟨fun i hi => ?_, by simpa [Nat.add_assoc, Nat.add_comm 1] using hR⟩
    cases i with
    | zero => simpa using hA.1
    | succ i => simpa [Nat.add_assoc, Nat.add_comm 1] using hAs i (by simpa using hi)

namespace ScopeHyp
variable {tr : Translated} {auxRec : List (Name × Name)} {ns ms : List Name} {n : Nat}
  {P P' : Name → Prop} {us : List VLevel} (H : ScopeHyp tr auxRec ns ms n P P')
include H

theorem scoped_restore_tel (lam : Bool) (As : List VExpr) (X : VExpr) (hn : As.length = n)
    (hs : restoreSafeTop ns ms us n (if lam then Spec.lamTel As X else Spec.forallTel As X) = true)
    (he : Scoped P 0 (if lam then Spec.lamTel As X else Spec.forallTel As X)) :
    Scoped P' 0 (tr.restore auxRec n (if lam then Spec.lamTel As X else Spec.forallTel As X)) := by
  have hs' := restoreSafeTop_tel ns ms us n lam As X 0 (by
      unfold restoreSafeTop at hs; rw [hn]; exact hs)
  obtain ⟨hAs, hX⟩ := scoped_tel_inv lam he
  rw [Nat.zero_add] at hX hs'
  have hAs' : ∀ i (h : i < As.length), Scoped P' (0 + i) As[i] := fun i hi =>
    H.free (hAs i hi) (hs'.1 _ (List.getElem_mem hi))
  have hX' := H.scoped_restoreBody X (d := As.length) (by omega) hs'.2 hX
  rw [hn] at hX'
  cases lam
  · rw [ite_eq_right (by decide), restore_forallTel tr auxRec n As X hn]
    exact Scoped.forallTel hAs' (by rw [Nat.zero_add, hn]; exact hX')
  · rw [ite_eq_left rfl, restore_lamTel As X hn]
    exact Scoped.lamTel hAs' (by rw [Nat.zero_add, hn]; exact hX')

end ScopeHyp

theorem restore_read {M₀ M₁' : CInterp V} {ls : List Nat} {tr' : Translated}
    {auxRec : List (Name × Name)} {ns ms : List Name} {us : List VLevel} {n : Nat}
    {Q : List V → Prop} {P P' : Name → Prop}
    (H : RestoreHyp M₀ M₀ ls tr' auxRec ns ms us n Q) (SH : ScopeHyp tr' auxRec ns ms n P P')
    (hag : ∀ c, P c → M₀ c = M₁' c) (lam : Bool) (As : List VExpr) (X : VExpr)
    (hn : As.length = n)
    (hs : restoreSafeTop ns ms us n (if lam then Spec.lamTel As X else Spec.forallTel As X) = true)
    (he : Scoped P 0 (if lam then Spec.lamTel As X else Spec.forallTel As X))
    (hQ : ∀ ys, Ext M₀ ls As [] ys → Q ys) :
    Scoped P' 0 (tr'.restore auxRec n (if lam then Spec.lamTel As X else Spec.forallTel As X)) ∧
      ∀ ρ, interp M₀ ls (tr'.restore auxRec n (if lam then Spec.lamTel As X else
          Spec.forallTel As X)) ρ =
        interp M₁' ls (if lam then Spec.lamTel As X else Spec.forallTel As X) ρ := by
  have hsc := SH.scoped_restore_tel lam As X hn hs he
  refine ⟨hsc, fun ρ => ?_⟩
  rw [interp_closed _ _ hsc.1 ρ, RestoreHyp.interp_restore_tel H lam As X hn hs hQ,
    interp_congr (he.2.mono hag), interp_closed _ _ he.1 ρ]

namespace NWF
variable {M : CInterp V} {env env₁ envT : VEnv} {b : SBlock} {rec : List RBlock} {tr : Translated}
  {nuser : Nat} {fams : List Fam} {MJf : RBlock → CInterp V} {envJf envJ₁f : RBlock → VEnv}
  (N : NWF M env env₁ envT b rec tr nuser fams MJf envJf envJ₁f)
  (hRN : RecNames b nuser = true)
  {e₁ e₂ e₃ : VEnv}
  (h1 : addFold env (nTypeConsts b nuser) = some e₁) (h2 : addFold e₁
      (nCtorConsts tr b nuser) = some e₂)
  (h3 : addFold e₂ (nRecConsts tr b nuser) = some e₃)
include N

include hRN h1 h2 h3 in
theorem trans_add : ∃ e₂T e₃T, addFold env₁ (ctorConsts b) = some e₂T ∧
    addFold e₂T (recConsts b) = some e₃T ∧ b.add env = some (iotaFold b e₃T) := by
  have hle₁ := (addFold_spec h1).2.2.1
  obtain ⟨e₂T, h2T⟩ := trans_ctors N.S hle₁ h2 N.fresh
  obtain ⟨e₃T, h3T⟩ := trans_recs N.S hle₁ h2 h3 N.fresh hRN h2T
  refine ⟨e₂T, e₃T, h2T, h3T, ?_⟩
  unfold SBlock.add
  have h2' : b.ctors.foldlM (fun e c => e.addConst c.name { uvars := b.uvars, type := c.type }) env₁
      =
      some e₂T := by simpa [addFold, ctorConsts, List.foldlM_map] using h2T
  have h3' : (List.range b.ntypes).foldlM
      (fun e d => e.addConst (b.recName d) { uvars := b.recUvars, type := b.recType d }) e₂T =
      some e₃T := by simpa [addFold, recConsts, List.foldlM_map] using h3T
  simp only [bind, Option.bind, N.S.hwt, h2', h3', pure]
  rfl

omit [SetTheory V] N in
theorem dom_trans {e₂T e₃T : VEnv} (h2T : addFold env₁ (ctorConsts b) = some e₂T)
    (h3T : addFold e₂T (recConsts b) = some e₃T) {c : Name} (hc : Dom (iotaFold b e₃T) c) :
    Dom env₁ c ∨ c ∈ b.ctors.map (·.name) ∨ c ∈ (List.range b.ntypes).map b.recName := by
  unfold Dom at hc; rw [constants_iotaFold] at hc
  obtain ⟨_, _, _, hcs3, _⟩ := addFold_spec h3T
  obtain ⟨_, _, _, hcs2, _⟩ := addFold_spec h2T
  cases e3 : e₃T.constants c with
  | none => exact absurd e3 hc
  | some ci =>
    rcases hcs3 c ci e3 with ⟨x, hx, rfl, -⟩ | e2
    · right; right; obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hx; exact List.mem_map.mpr ⟨d, hd, rfl⟩
    · rcases hcs2 c ci e2 with ⟨y, hy, hy1, -⟩ | e1
      all_goals first
        | (right; left; obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hy; rw [← hy1]
           exact List.mem_map_of_mem hc')
        | (left; unfold Dom; rw [e1]; nofun)

omit N in
theorem fin_not_trans (N : NWF M env env₁ envT b rec tr nuser fams MJf envJf envJ₁f)
    (hRN : RecNames b nuser = true)
    (hfin : ∀ x ∈ (auxRecTable b nuser).map (·.2), env.constants x = none)
    {e₂T e₃T : VEnv} (h2T : addFold env₁ (ctorConsts b) = some e₂T)
    (h3T : addFold e₂T (recConsts b) = some e₃T) {c : Name} (hc : Dom (iotaFold b e₃T) c) :
    c ∉ (auxRecTable b nuser).map (·.2) := fun hf => by
  have RN := RecNames.spec hRN
  rcases NWF.dom_trans h2T h3T hc with h | h | h
  · exact h (N.fin_none hRN hfin hf)
  · exact RN.fin_ctors c hf h
  · exact RN.fin_recs c hf h

theorem aux_ctor_target_dom {c : Name} {a : Aux} (hca : tr.auxOfCtor? c = some a) {Ic : Name}
    {Ils : List VLevel} {Ds' : List VExpr} (hk : headArgs a.key = (.const Ic Ils, Ds')) :
    Dom env (c.replacePrefix a.name Ic) := by
  obtain ⟨J, lv, Ds, r, m, d, q, hs, hq, hcn⟩ := N.auxCtor_pos hca
  have cJ := N.canon r hs.mem
  obtain ⟨k, hk0, he, -, -, ⟨c0, us0, as0, rfl⟩, -⟩ := hs.read cJ
  rw [atKey_appN_const] at he
  obtain ⟨us', as', hkey, -, -⟩ := EqL.appN_const he
  rw [hkey, headArgs_appN_const] at hk
  simp only [Prod.mk.injEq, VExpr.const.injEq] at hk
  obtain ⟨⟨rfl, -⟩, -⟩ := hk
  have hqJ : q < (r.b.types[m]!).ctors.length := hs.nctors ▸ hq
  have hinfo : ((r.info m).ctors[q]!).1 = ((r.b.types[m]!).ctors[q]!).name := by
    show (((r.b.types[m]!).ctors.map fun c => (c.name, r.tr.restore [] r.b.nparams
        c.type))[q]!).1 = _
    rw [← getElem_eq_getElem! (by rw [List.length_map]; exact hqJ), List.getElem_map,
      ← getElem_eq_getElem! hqJ]
  have hcJ : (ctorsOf r.b m)[q]? = some ((r.b.types[m]!).ctors[q]!) := by
    simp only [ctorsOf]; rw [List.getElem?_eq_getElem hqJ, getElem_eq_getElem! hqJ]
  have h1 := hs.ctor_restore q hq
  rw [← hcn]; rw [hs.ctor_name q hq] at h1 ⊢
  rw [replacePrefix_swap J a.name c0 _ h1, hinfo, ← hs.nameJ]
  exact (cJ.slotCtors m hs.m_lt q _ hcJ _ hk0 c0 us0 as0 (headArgs_appN_const _ _ _)).1

include h1 in
theorem dom₁_e₁
    {c : Name} (hc : Dom env₁ c) (hna : c ∉ tr.aux.map (·.name)) : Dom e₁ c := by
  have hwt := N.S.hwt
  rw [withTypes_eq] at hwt
  obtain ⟨_, _, _, hcs, _⟩ := addFold_spec hwt
  obtain ⟨_, _, hle, _, _, hex⟩ := addFold_spec h1
  unfold Dom at hc
  cases e : env₁.constants c with
  | none => exact absurd e hc
  | some ci =>
    rcases hcs c ci e with ⟨x, hx, hxc, -⟩ | e0
    · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
      have hn : c ∈ b.names := hxc ▸ List.mem_map_of_mem ht
      rw [N.names_split] at hn
      rcases List.mem_append.mp hn with hn | hn
      · obtain ⟨t', ht', he⟩ := List.mem_map.mp hn
        obtain ⟨ci', hci'⟩ := hex (t'.name, { uvars := b.uvars, type := t'.type })
          (List.mem_map.mpr ⟨t', ht', rfl⟩)
        unfold Dom; rw [← he, hci']; nofun
      · exact absurd hn hna
    · exact Dom.mono hle (by unfold Dom; rw [e0]; nofun)

include h1 h2 in
theorem scopeHyp_ctor :
    ScopeHyp tr [] (auxNs tr b nuser) (auxMs tr b nuser) b.nparams (Dom env₁) (Dom e₂) where
  ns_iff := N.ns_iff
  ms_ns := fun _ h => List.mem_append_left _ h
  ms_rec := fun _ hp => absurd hp List.not_mem_nil
  rec_ns := fun _ hp => absurd hp List.not_mem_nil
  key := fun a ha => by
    obtain ⟨J, lv, Ds, r, m, d, hs⟩ := N.aux_mem_spec ha
    refine ⟨key_closed N.S (N.canon r hs.mem) hs N.modelT.2 (N.argsTyped hs.link),
      ((N.key_consts ha hs).and (N.key_fresh hs)).mono fun c ⟨hc, hna⟩ => ?_⟩
    rcases hc with hc | hc
    · exact Dom.mono (addFold_spec h2).2.2.1 (N.dom₁_e₁ h1 hc hna)
    · obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hc
      exact addFold_dom h2 (List.mem_map.mpr ⟨c', hc', rfl⟩)
  key_head := fun a ha => by
    obtain ⟨J, lv, Ds, r, m, d, hs⟩ := N.aux_mem_spec ha
    obtain ⟨k, -, he, -, -, ⟨c, us, as, rfl⟩, -⟩ := hs.read (N.canon r hs.mem)
    rw [atKey_appN_const] at he
    obtain ⟨us', as', he', -, -⟩ := EqL.appN_const he
    exact ⟨c, us', as', by rw [he', headArgs_appN_const]⟩
  ctor := fun _ _ hca _ _ _ hk => Dom.mono (VEnv.LE.trans (addFold_spec h1).2.2.1
    (addFold_spec h2).2.2.1) (N.aux_ctor_target_dom hca hk)
  fin := fun _ hp => absurd hp List.not_mem_nil
  other := fun _ hc hns _ => Dom.mono (addFold_spec h2).2.2.1
    (N.dom₁_e₁ h1 hc fun h => hns (List.mem_append_left _ h))

omit [SetTheory V] N in
include h3 in
theorem fin_dom {p : Name × Name} (hp : p ∈ auxRecTable b nuser) : Dom e₃ p.2 := by
  obtain ⟨_, _, _, _, _, hex⟩ := addFold_spec h3
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
  have hi' : i < b.ntypes - nuser := by rw [auxRecTable_length] at hi; exact hi
  have hd : nuser + i < b.ntypes := by omega
  have hdl : nuser + i < (nestedRecs tr b nuser).length := by
    rw [nestedRecs_length]; exact hd
  have hname := nestedRecs_name tr b nuser hd
  rw [ite_eq_right (by omega), Nat.add_sub_cancel_left, ← getElem_eq_getElem! hi] at hname
  obtain ⟨ci, hci⟩ := hex (_, _) (List.mem_map.mpr ⟨_, List.getElem_mem hdl, rfl⟩)
  unfold Dom; simp only at hci; rw [← hname, hci]; nofun

include hRN h1 h2 h3 in
theorem scopeHyp_rec
    {e₂T e₃T : VEnv} (h2T : addFold env₁ (ctorConsts b) = some e₂T)
    (h3T : addFold e₂T (recConsts b) = some e₃T) :
    ScopeHyp (shiftTr tr b.blockLevels) (auxRecTable b nuser) (auxNs tr b nuser) (auxMs tr b nuser)
      b.nparams (Dom (iotaFold b e₃T)) (Dom e₃) := by
  have hle₁₃ : e₁ ≤ e₃ := VEnv.LE.trans (addFold_spec h2).2.2.1 (addFold_spec h3).2.2.1
  have hle₂₃ : e₂ ≤ e₃ := (addFold_spec h3).2.2.1
  have SC := N.scopeHyp_ctor h1 h2
  exact {
  ns_iff := fun c => by
    rw [shiftTr_find, shiftTr_auxOfCtor, Option.isSome_map]; exact N.ns_iff c
  ms_ns := fun _ h => List.mem_append_left _ h
  ms_rec := fun p hp => by
    obtain ⟨i, hi, he⟩ := mem_auxRecTable hp
    unfold auxMs; rw [he]
    exact List.mem_append_right _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
  rec_ns := fun _ hp => N.auxRec_not_ns hRN hp
  key := fun a' ha' => by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ha'
    have h := SC.key a ha
    exact ⟨h.1.instL, constsIn_instL.mpr (h.2.mono fun _ hc => Dom.mono hle₂₃ hc)⟩
  key_head := fun a' ha' => by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ha'
    obtain ⟨Ic, Ils, Ds, hh⟩ := SC.key_head a ha
    exact ⟨Ic, Ils.map (·.inst b.blockLevels), Ds.map (·.instL b.blockLevels), by
      simp only [headArgs_instL, hh, VExpr.instL]⟩
  ctor := fun c a' hca Ic Ils' Ds' hk => by
    rw [shiftTr_auxOfCtor] at hca
    cases hca0 : tr.auxOfCtor? c with
    | none => rw [hca0] at hca; cases hca
    | some a =>
      rw [hca0] at hca
      simp only [Option.map_some, Option.some.injEq] at hca
      subst hca
      obtain ⟨Ic₀, Ils, Ds, hh⟩ := SC.key_head a (List.mem_of_find?_eq_some hca0)
      have hk'' := hk
      simp only [headArgs_instL, hh, VExpr.instL, Prod.mk.injEq, VExpr.const.injEq] at hk''
      obtain ⟨⟨rfl, -⟩, -⟩ := hk''
      exact Dom.mono (VEnv.LE.trans (addFold_spec h1).2.2.1 hle₁₃) (N.aux_ctor_target_dom hca0 hh)
  fin := fun p hp => NWF.fin_dom h3 hp
  other := fun c hc hns hrec => by
    rcases NWF.dom_trans h2T h3T hc with h | h | h
    · exact Dom.mono hle₁₃ (N.dom₁_e₁ h1 h fun h' => hns (List.mem_append_left _ h'))
    · obtain ⟨c', hc', rfl⟩ := List.mem_map.mp h
      have hsplit : b.ctors = (b.types.take nuser).flatMap (·.ctors) ++
          (b.types.drop nuser).flatMap (·.ctors) := by
        rw [← List.flatMap_append, List.take_append_drop]; rfl
      rw [hsplit] at hc'
      rcases List.mem_append.mp hc' with hc' | hc'
      · exact Dom.mono hle₂₃ (addFold_dom h2 (List.mem_map.mpr ⟨c', hc', rfl⟩))
      · refine absurd (List.mem_append_right _ ?_) hns
        obtain ⟨t, ht, hct⟩ := List.mem_flatMap.mp hc'
        exact List.mem_flatMap.mpr ⟨t, ht, List.mem_map_of_mem hct⟩
    · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp h
      have hd := List.mem_range.mp hd
      by_cases hdu : d < nuser
      · have hdl : d < (nestedRecs tr b nuser).length := by rw [nestedRecs_length]; exact hd
        have hname := nestedRecs_name tr b nuser hd
        rw [ite_eq_left hdu] at hname
        rw [← hname]; exact addFold_dom h3 (List.mem_map.mpr ⟨_, List.getElem_mem hdl, rfl⟩)
      · have hi : d - nuser < (auxRecTable b nuser).length := by rw [auxRecTable_length]; omega
        refine absurd ?_ (hrec _ (List.getElem_mem hi))
        simp only [auxRecTable, List.getElem_map, List.getElem_range]
        congr 1; omega }

end NWF
end Soulgem.Nested
