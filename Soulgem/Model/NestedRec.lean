import Soulgem.Model.NestedAdd
import Soulgem.Model.NestedVal

/-! # The nested model -/

namespace Soulgem.Nested
open ConLeche ConLeche.SetTheory ConLeche.SetTheory.Tower Lean4Lean Spec BlockSem BlockModel

universe u
variable {V : Type u} [SetTheory V]

noncomputable def Mrec (M : CInterp V) (b : SBlock) (nuser : Nat) : CInterp V := fun x =>
  match (auxRecTable b nuser).find? (fun p => decide (p.2 = x)) with
  | some p => M₃ M b p.1
  | none => M₃ M b x

theorem Mrec_of_not_fin {M : CInterp V} {b : SBlock} {nuser : Nat} {x : Name}
    (hx : x ∉ (auxRecTable b nuser).map (·.2)) : Mrec M b nuser x = M₃ M b x := by
  unfold Mrec
  rw [List.find?_eq_none.mpr fun p hp h => hx (List.mem_map.mpr ⟨p, hp, by simpa using h⟩)]

theorem Mrec_fin {M : CInterp V} {b : SBlock} {nuser : Nat}
    (hnd : ((auxRecTable b nuser).map (·.2)).Nodup) {p : Name × Name}
        (hp : p ∈ auxRecTable b nuser) :
    Mrec M b nuser p.2 = M₃ M b p.1 := by
  unfold Mrec
  rw [find?_of_nodup_map (f := (·.2)) hnd hp]

theorem rename_nil (c : Name) : rename [] c = c := rfl

namespace NWF
variable {M : CInterp V} {env env₁ envT : VEnv} {b : SBlock} {rec : List RBlock} {tr : Translated}
  {nuser : Nat} {fams : List Fam} {MJf : RBlock → CInterp V} {envJf envJ₁f : RBlock → VEnv}
  (N : NWF M env env₁ envT b rec tr nuser fams MJf envJf envJ₁f)
  (hRN : RecNames b nuser = true)
  (hfin : ∀ x ∈ (auxRecTable b nuser).map (·.2), env.constants x = none)
  (hrecu : ∀ d < nuser, env.constants (b.recName d) = none)
  (hctu : ∀ c ∈ (b.types.take nuser).flatMap (·.ctors), env.constants c.name = none)
include N

theorem auxCtor_pos {c : Name} {a : Aux} (h : tr.auxOfCtor? c = some a) :
    ∃ J lv Ds r m d q, Slot rec b.nparams tr b nuser fams a J lv Ds r m d ∧
      q < (b.types[d]!).ctors.length ∧ ((b.types[d]!).ctors[q]!).name = c := by
  have ha : a ∈ tr.aux := List.mem_of_find?_eq_some h
  obtain ⟨J, lv, Ds, r, m, d, hs⟩ := N.aux_mem_spec ha
  have hp := List.find?_some h
  cases ht : tr.types.find? (·.name == a.name) with
  | none => simp [ht] at hp
  | some t =>
    simp only [ht, Option.any_some, List.any_eq_true, beq_iff_eq] at hp
    obtain ⟨p, hp, rfl⟩ := hp
    obtain ⟨htn, i, hi, rfl, _⟩ := List.find?_eq_some_iff_getElem.mp ht
    simp only [beq_iff_eq] at htn
    have hib : i < b.types.length := N.cert_length ▸ hi
    obtain ⟨hname, hctors⟩ := N.cert_get i hib
    have hid : i = d := N.slot_unique hib hs.hd (by
      rw [← getElem_eq_getElem! hib, ← hname,
        htn, hs.name])
    subst hid
    rw [hctors] at hp
    obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hp
    obtain ⟨q, hq, rfl⟩ := List.getElem_of_mem hc'
    have e : b.types[i]! = b.types[i] := by
      rw [← getElem_eq_getElem! hib]
    refine ⟨J, lv, Ds, r, m, i, q, hs, by rw [e]; exact hq, ?_⟩
    rw [e, ← getElem_eq_getElem! hq]

include hRN hfin in
theorem fin_none {x : Name} (hx : x ∈ (auxRecTable b nuser).map (·.2)) : env₁.constants x = none :=
  env₁_none N.S ((RecNames.spec hRN).fin_names x hx) (hfin x hx)

include hRN hrecu in
theorem rec_none {d : Nat} (hd : d < b.ntypes) : env₁.constants (b.recName d) = none := by
  refine env₁_none N.S ((RecNames.spec hRN).rec_names _ (recName_mem hd)) ?_
  by_cases hdu : d < nuser
  · exact hrecu d hdu
  · have h1 := List.all_eq_true.mp (of_decide_eq_true (decide_eq_true N.fresh.2)) (d - nuser)
      (List.mem_range.mpr (by omega))
    rw [show nuser + (d - nuser) = d by omega] at h1
    simpa using h1

include hctu in
theorem ctor_none {c : SCtor} (hc : c ∈ b.ctors) : env₁.constants c.name = none := by
  have hnd := N.S.hwf.syn.nodup
  have hnn : c.name ∉ b.names := fun hn =>
    (List.nodup_append.mp hnd).2.2 _ hn _ (List.mem_map.mpr ⟨c, hc, rfl⟩) rfl
  refine env₁_none N.S hnn ?_
  have hct : c ∈ (b.types.take nuser).flatMap (·.ctors) ++ (b.types.drop nuser).flatMap
      (·.ctors) := by
    rw [← List.flatMap_append, List.take_append_drop]; exact hc
  rcases List.mem_append.mp hct with hu | ha
  · exact hctu c hu
  · obtain ⟨t, ht, hct⟩ := List.mem_flatMap.mp ha
    have h1 := List.all_eq_true.mp (of_decide_eq_true (decide_eq_true N.fresh.1)) t ht
    have h2 := List.all_eq_true.mp h1 c hct
    simpa using h2

include hRN hfin hrecu hctu in
theorem Mrec_dom₁ {x : Name} (hx : Dom env₁ x) : Mrec M b nuser x = Setting.Mc M b x := by
  rw [Mrec_of_not_fin fun h => hx (N.fin_none hRN hfin h)]
  rw [M₃_other fun h => by
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp h
    exact hx (N.rec_none hRN hrecu (List.mem_range.mp hd))]
  rw [M₂_other fun h => by
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp h
    exact hx (N.ctor_none hctu hc)]

include hRN hfin hrecu hctu in
theorem Mrec_key {x : Name} (hx : Dom env₁ x ∨ x ∈ b.ctors.map (·.name)) :
    Mrec M b nuser x = Setting.Mc M b x := by
  rcases hx with hx | hx
  · exact N.Mrec_dom₁ hRN hfin hrecu hctu hx
  have RN := RecNames.spec hRN
  have hnn : x ∉ b.names := fun hn => (List.nodup_append.mp N.S.hwf.syn.nodup).2.2 _ hn _ hx rfl
  rw [Mrec_of_not_fin fun h => RN.fin_ctors x h hx, M₃_other fun h => RN.rec_ctors x h hx,
    ← N.base x hx]
  exact (M₁_other hnn).symm

theorem key_consts {a : Aux} (_ha : a ∈ tr.aux) {J : Name} {lv : List VLevel} {Ds : List VExpr}
    {r : RBlock} {m d : Nat} (hs : Slot rec b.nparams tr b nuser fams a J lv Ds r m d) :
    ConstsIn (fun c => Dom env₁ c ∨ c ∈ ((b.types.take nuser).flatMap (·.ctors)).map (·.name))
      a.key := by
  obtain ⟨k, -, he, -, hkc, -⟩ := hs.read (N.canon r hs.mem)
  refine EqL.constsIn he (constsIn_subst (constsIn_argSubst (fun D hD =>
    (N.key_dom hs D hD).mono fun _ h => h.1.imp_right fun hc => NWF.user_of_key hc h.2)) ?_)
  exact constsIn_instL.mpr (hkc.mono fun _ h => Or.inl (Dom.mono N.S.le₁ h))

include hRN hfin hrecu hctu in
theorem restoreHyp_ctor {ls : List Nat} (hl : ls.length = b.uvars) :
    RestoreHyp (Mrec M b nuser) (Mrec M b nuser) ls tr [] (auxNs tr b nuser) (auxMs tr b nuser)
      (ownLevels b.uvars) b.nparams (fun xs => Ext M ls b.params [] xs) where
  ns_iff := N.ns_iff
  ms_ns := fun _ h => List.mem_append_left _ h
  ms_rec := fun _ hp => absurd hp List.not_mem_nil
  rec_ns := fun _ hp => absurd hp List.not_mem_nil
  key_head := fun a ha => by
    obtain ⟨J, lv, Ds, r, m, d, hs⟩ := N.aux_mem_spec ha
    obtain ⟨k, -, he, -, -, ⟨c, us, as, rfl⟩, -⟩ := hs.read (N.canon r hs.mem)
    rw [atKey_appN_const] at he
    obtain ⟨us', as', he', -, -⟩ := EqL.appN_const he
    exact ⟨c, us', as', by rw [he', headArgs_appN_const]⟩
  other := fun c _ => by rw [rename_nil]
  closed := fun a ha => by
    obtain ⟨J, lv, Ds, r, m, d, hs⟩ := N.aux_mem_spec ha
    exact key_closed N.S (N.canon r hs.mem) hs N.modelT.2 (N.argsTyped hs.link)
  aux := fun a ha xs _ hQ => by
    obtain ⟨J, lv, Ds, r, m, d, hs⟩ := N.aux_mem_spec ha
    have hr := hs.mem
    rw [ownLevels_eval hl]
    have hdom : Dom env₁ a.name := by rw [← hs.name]; exact N.S.type_dom hs.hd
    rw [N.Mrec_dom₁ hRN hfin hrecu hctu hdom,
      interp_congr ((N.key_consts ha hs).mono fun c hc =>
        N.Mrec_key hRN hfin hrecu hctu (hc.imp_right NWF.ctor_of_user)) _]
    exact aux_keys N.S (N.canon r hr) hs (NWF.m_lt hs) N.S.nodup N.modelT.1 N.envT_agree
      (N.argsTyped hs.link) (N.link_fam hs.link).1 (N.key_agree hs fun _ _ _ _ _ => rfl) hQ
      (N.carrier_slot hl hQ hs)
  ctor := fun c a hca Ic Ils Ds' hk xs _ hQ => by
    obtain ⟨J, lv, Ds, r, m, d, q, hs, hq, hcn⟩ := N.auxCtor_pos hca
    have ha : a ∈ tr.aux := List.mem_of_find?_eq_some hca
    have hr := hs.mem
    have cJ := N.canon r hr
    have hm := NWF.m_lt hs
    have hlv := (N.link_fam hs.link).1
    have hkt := N.argsTyped hs.link
    obtain ⟨k, hk0, he, hkc, hkcon, ⟨c0, us0, as0, rfl⟩, -⟩ := hs.read cJ
    rw [atKey_appN_const] at he
    obtain ⟨us', as', hkey, hu, has⟩ := EqL.appN_const he
    rw [hkey, headArgs_appN_const] at hk
    simp only [Prod.mk.injEq, VExpr.const.injEq] at hk
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hk
    have RN := RecNames.spec hRN
    have hcmem : (b.types[d]!).ctors[q]! ∈ b.ctors :=
      List.mem_flatMap.mpr ⟨_, getElem!_mem' hs.hd, getElem!_mem' hq⟩
    have hcname : c ∈ b.ctors.map (·.name) := by rw [← hcn]; exact List.mem_map_of_mem hcmem
    rw [Mrec_of_not_fin fun h => RN.fin_ctors c h hcname,
      M₃_other fun h => RN.rec_ctors c h hcname, ← hcn,
      M₂_ctor (List.nodup_append.mp N.S.hwf.syn.nodup).2.1
        (j := d) (q := q) (by
            simp only [ctorsOf]; rw [List.getElem?_eq_getElem hq, getElem_eq_getElem! hq]),
      ownLevels_eval hl, N.aux_ctor_val ha hs hl hQ hq]
    have hqJ : q < (r.b.types[m]!).ctors.length := hs.nctors ▸ hq
    have hinfo : ((r.info m).ctors[q]!).1 = ((r.b.types[m]!).ctors[q]!).name := by
      show (((r.b.types[m]!).ctors.map fun c => (c.name, r.tr.restore [] r.b.nparams
          c.type))[q]!).1 = _
      rw [← getElem_eq_getElem! (by rw [List.length_map]; exact hqJ), List.getElem_map,
        ← getElem_eq_getElem! hqJ]
    have hrc : (((b.types[d]!).ctors[q]!).name).replacePrefix a.name c0 =
        ((r.b.types[m]!).ctors[q]!).name.replacePrefix (r.b.types[m]!).name c0 := by
      have h1 := hs.ctor_restore q hq
      rw [hs.ctor_name q hq] at h1 ⊢
      rw [replacePrefix_swap J a.name c0 _ h1, hinfo, hs.nameJ]
    have hcJ : (ctorsOf r.b m)[q]? = some ((r.b.types[m]!).ctors[q]!) := by
      simp only [ctorsOf]; rw [List.getElem?_eq_getElem hqJ, getElem_eq_getElem! hqJ]
    obtain ⟨hdomJ, hvalJ⟩ := cJ.slotCtors m hm q _ hcJ _ hk0 c0 us0 as0 (headArgs_appN_const _ _ _)
    have hcl : (appN (.const (((r.b.types[m]!).ctors[q]!).name.replacePrefix
        (r.b.types[m]!).name c0)
        us0) as0).ClosedN (0 + Ds.length) := by
      rw [Nat.zero_add, hs.nDs]; exact closedN_appN_of trivial (closedN_appN_inv hkc).2
    have hat := interp_atKey (Mrec M b nuser) ls lv Ds xs.reverse hcl [] rfl
    simp only [List.nil_append] at hat
    rw [hrc, interp_EqL _ _ (EqL.appN_congr
      (show (VExpr.const _ us').EqL (.const _ (us0.map (·.inst lv))) from ⟨rfl, hu⟩) has),
      ← atKey_appN_const, hat]
    have hagM : ∀ x, Dom env x → Mrec M b nuser x = M x := fun x hx =>
      (N.Mrec_dom₁ hRN hfin hrecu hctu (Dom.mono N.S.le₁ hx)).trans (M₁_other (N.S.not_name hx))
    have hka : keyArgs (Mrec M b nuser) ls Ds xs.reverse =
        keyArgs (M₁ M b (carrierFn M b)) ls Ds xs.reverse := by
      unfold keyArgs
      congr 1
      exact List.map_congr_left fun D hD₀ => interp_congr ((N.key_dom hs D hD₀).mono fun x hx =>
        N.Mrec_key hRN hfin hrecu hctu hx.1) _
    have hcon : ConstsIn (Dom env) (appN (.const (((r.b.types[m]!).ctors[q]!).name.replacePrefix
        (r.b.types[m]!).name c0) us0) as0) :=
      (constsIn_appN _ _).mpr ⟨hdomJ, ((constsIn_appN _ _).mp hkcon).2⟩
    rw [interp_congr (hcon.mono fun x hx => hagM x hx) _, hka,
      show keyArgs (M₁ M b (carrierFn M b)) ls Ds xs.reverse =
        (Ds.map (interp (M₁ M b (carrierFn M b)) ls · xs.reverse)).reverse from rfl,
      hvalJ _ _ (by simp [hlv]) (keyArgs_ext N.S cJ N.modelT.1 N.envT_agree hkt
        (N.key_agree hs fun _ _ _ _ _ => rfl) hQ),
      List.reverse_reverse]

end NWF
end Soulgem.Nested
