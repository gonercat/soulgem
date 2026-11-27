import Soulgem.Model.NestedCtor
import Soulgem.Model.NestedKeys

/-! # Nested blocks: the frame of one nested declaration -/

namespace Soulgem.Nested
open ConLeche ConLeche.SetTheory ConLeche.SetTheory.Tower Lean4Lean Spec BlockSem BlockModel

universe u
variable {V : Type u} [SetTheory V]

structure NWF (M : CInterp V) (env env₁ envT : VEnv) (b : SBlock) (rec : List RBlock)
    (tr : Translated) (nuser : Nat) (fams : List Fam) (MJf : RBlock → CInterp V)
    (envJf envJ₁f : RBlock → VEnv) : Prop where
  S : Setting M env env₁ b
  cert : b.Certifies b.uvars b.nparams tr.types
  hT : b.add env = some envT
  famsOK : FamsOK tr b nuser rec envT fams
  base : ∀ c ∈ b.ctors.map (·.name), M c = M₂ M b c
  safe : RestoreSafe tr b nuser = true
  fresh : AuxFresh b nuser env
  members : AuxMembers tr b nuser = true
  canon : ∀ r ∈ rec, CanonR M env r (MJf r) (envJf r) (envJ₁f r)

namespace NWF
variable {M : CInterp V} {env env₁ envT : VEnv} {b : SBlock} {rec : List RBlock} {tr : Translated}
  {nuser : Nat} {fams : List Fam} {MJf : RBlock → CInterp V} {envJf envJ₁f : RBlock → VEnv}
  (N : NWF M env env₁ envT b rec tr nuser fams MJf envJf envJ₁f)
include N

theorem envT_split : ∃ e₂ e₃, addFold env₁ (ctorConsts b) = some e₂ ∧
    addFold e₂ (recConsts b) = some e₃ ∧ envT = iotaFold b e₃ := by
  obtain ⟨e₁, e₂, e₃, h1, h2, h3, he⟩ := add_spec N.hT
  obtain rfl : e₁ = env₁ := Option.some.inj (h1.symm.trans N.S.hwt)
  exact ⟨e₂, e₃, h2, h3, he⟩

theorem drop_names : (b.types.drop nuser).map (·.name) = tr.aux.map (·.name) := by
  have := N.members; unfold AuxMembers at this; simpa using this

theorem names_split : b.names = (b.types.take nuser).map (·.name) ++ tr.aux.map (·.name) := by
  rw [← N.drop_names, ← List.map_append, List.take_append_drop]; rfl

theorem member_name {i : Nat} {a : Aux} (ha : tr.aux[i]? = some a) (hd : nuser + i < b.ntypes) :
    (b.types[nuser + i]!).name = a.name := by
  have h := congrArg (·[i]?) N.drop_names
  simp only [List.getElem?_map, List.getElem?_drop, ha, Option.map_some] at h
  rw [List.getElem?_eq_getElem (show nuser + i < b.types.length from hd), Option.map_some,
    Option.some.injEq] at h
  rw [← getElem_eq_getElem! hd]; exact h

theorem aux_slot_name {s : Nat} (hs : s < b.ntypes) (hsu : ¬s < nuser) :
    (b.types[s]!).name ∈ tr.aux.map (·.name) := by
  have hs' : s < b.types.length := hs
  rw [← N.drop_names, ← getElem_eq_getElem! hs']
  exact List.mem_map_of_mem (List.mem_iff_getElem.mpr ⟨s - nuser, by simp; omega,
    by rw [List.getElem_drop]; congr 1; omega⟩)

end NWF

theorem _root_.Soulgem.Spec.SBlock.ctors_split (b : SBlock) (n : Nat) :
    b.ctors = (b.types.take n).flatMap (·.ctors) ++ (b.types.drop n).flatMap (·.ctors) := by
  rw [← List.flatMap_append, List.take_append_drop]; rfl

theorem nodup_flatMap_mem {α β : Type _} {f : α → List β} :
    ∀ {l : List α}, (l.flatMap f).Nodup → ∀ x ∈ l, (f x).Nodup
  | [], _, _, h => by simp at h
  | a :: l, h, x, hx => by
    rw [List.flatMap_cons, List.nodup_append] at h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.1
    · exact nodup_flatMap_mem h.2.1 x hx

theorem nodup_flatMap_pos {α β : Type _} {f : α → List β} :
    ∀ {l : List α}, (l.flatMap f).Nodup → ∀ {i j} (hi : i < l.length) (hj : j < l.length) {x},
      x ∈ f l[i] → x ∈ f l[j] → i = j
  | [], _, _, _, hi, _, _, _, _ => absurd hi (Nat.not_lt_zero _)
  | a :: l, h, i, j, hi, hj, x, hx, hx' => by
    rw [List.flatMap_cons, List.nodup_append] at h
    obtain ⟨-, h2, h3⟩ := h
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ j =>
        exact (h3 x hx x (List.mem_flatMap.mpr ⟨_, List.getElem_mem (by simpa using hj), hx'⟩)
          rfl).elim
    | succ i =>
      cases j with
      | zero =>
        exact (h3 x hx' x (List.mem_flatMap.mpr ⟨_, List.getElem_mem (by simpa using hi), hx⟩)
          rfl).elim
      | succ j =>
        exact congrArg (· + 1) (nodup_flatMap_pos h2 (by simpa using hi) (by simpa using hj) hx hx')

open Classical in
noncomputable def slotVal (M : CInterp V) (b : SBlock) (rec : List RBlock) (nuser : Nat)
    (fams : List Fam) (MJf : RBlock → CInterp V) (ls : List Nat) (ps : List V) (g : Nat) :
    Option V :=
  if h : ∃ js : Nat × Nat, ∃ _ : js.1 < fams.length, nuser ≤ g ∧ fams[js.1].φ[js.2]? =
      some (g - nuser)
  then (rec[fams[h.choose.1]!.ri]?).map fun r => carrier (MJf r)
      (fams[h.choose.1]!.lv.map (VLevel.eval ls)) r.b
      (keyArgs (M₁ M b (carrierFn M b)) ls fams[h.choose.1]!.Ds ps.reverse) h.choose.2
  else none

noncomputable def allKeys (M : CInterp V) (b : SBlock) (rec : List RBlock) (nuser : Nat)
    (fams : List Fam) (MJf : RBlock → CInterp V) (ls : List Nat) (ps : List V) (g : Nat) : V :=
  (slotVal M b rec nuser fams MJf ls ps g).getD (carrier M ls b ps.reverse g)

namespace NWF
variable {M : CInterp V} {env env₁ envT : VEnv} {b : SBlock} {rec : List RBlock} {tr : Translated}
  {nuser : Nat} {fams : List Fam} {MJf : RBlock → CInterp V} {envJf envJ₁f : RBlock → VEnv}
  (N : NWF M env env₁ envT b rec tr nuser fams MJf envJf envJ₁f)
include N

theorem slot_unique {d g : Nat} (hd : d < b.ntypes) (hg : g < b.ntypes)
    (h : (b.types[d]!).name = (b.types[g]!).name) : d = g := by
  have hnd := N.S.nodup
  have hd' : d < b.names.length := by rw [names_length]; exact hd
  have hg' : g < b.names.length := by rw [names_length]; exact hg
  have e1 : b.names[d] = (b.types[d]!).name := by
    simp only [SBlock.names, List.getElem_map]
    exact congrArg (·.name) (getElem_eq_getElem! hd)
  have e2 : b.names[g] = (b.types[g]!).name := by
    simp only [SBlock.names, List.getElem_map]
    exact congrArg (·.name) (getElem_eq_getElem! hg)
  exact (List.Nodup.getElem_inj (hi := hd') (hj := hg') hnd).mp (by rw [e1, e2, h])

theorem slot_ge {g : Nat} (hg : g < b.ntypes) {a : Aux} (ha : a ∈ tr.aux)
    (hn : (b.types[g]!).name = a.name) : nuser ≤ g := by
  by_cases h : nuser ≤ g
  · exact h
  · exfalso
    have hnd := N.S.nodup; rw [N.names_split] at hnd
    have hd := (List.nodup_append.mp hnd).2.2
    have h1 : (b.types[g]!).name ∈ (b.types.take nuser).map (·.name) := by
      have hg' : g < b.types.length := hg
      rw [← getElem_eq_getElem! hg']
      exact List.mem_map_of_mem (List.mem_iff_getElem.mpr ⟨g, by simp; omega, by simp⟩)
    exact hd _ h1 _ (List.mem_map_of_mem ha) hn

theorem images_mem {j s g : Nat} (hj : j < fams.length) (h : fams[j].φ[s]? = some g) :
    g < tr.aux.length := by
  have : g ∈ images fams := List.mem_flatMap.mpr ⟨_, List.getElem_mem hj, List.mem_of_getElem? h⟩
  exact List.mem_range.mp (N.famsOK.2.mem_iff.mp this)

theorem slot_uniq {j j' s s' g : Nat} (hj : j < fams.length) (hj' : j' < fams.length)
    (h : fams[j].φ[s]? = some g) (h' : fams[j'].φ[s']? = some g) : j = j' ∧ s = s' := by
  have hnd : (images fams).Nodup := N.famsOK.2.nodup_iff.mpr List.nodup_range
  have hjj := nodup_flatMap_pos hnd hj hj' (List.mem_of_getElem? h) (List.mem_of_getElem? h')
  subst hjj
  refine ⟨rfl, ?_⟩
  obtain ⟨hs, e⟩ := List.getElem?_eq_some_iff.mp h
  obtain ⟨hs', e'⟩ := List.getElem?_eq_some_iff.mp h'
  exact (List.Nodup.getElem_inj (hi := hs) (hj := hs') (nodup_flatMap_mem hnd _
      (List.getElem_mem hj))).mp
    (e.trans e'.symm)

theorem allKeys_slot {j : Nat} (hj : j < fams.length) {r : RBlock}
    (hr : rec[fams[j].ri]? = some r) {s g : Nat} (hg : fams[j].φ[s]? = some g) {ls : List Nat}
    {ps : List V} :
    allKeys M b rec nuser fams MJf ls ps (nuser + g) = carrier (MJf r)
      (fams[j].lv.map (VLevel.eval ls)) r.b
      (keyArgs (M₁ M b (carrierFn M b)) ls fams[j].Ds ps.reverse) s := by
  have hex : ∃ js : Nat × Nat, ∃ _ : js.1 < fams.length,
      nuser ≤ nuser + g ∧ fams[js.1].φ[js.2]? = some (nuser + g - nuser) :=
    ⟨(j, s), hj, Nat.le_add_right _ _, by rw [Nat.add_sub_cancel_left]; exact hg⟩
  unfold allKeys slotVal
  rw [dite_eq_left hex]
  have hsp := hex.choose_spec
  generalize hex.choose = js at hsp ⊢
  obtain ⟨j0, s0⟩ := js
  obtain ⟨hj0, -, hφ0⟩ := hsp
  rw [Nat.add_sub_cancel_left] at hφ0
  obtain ⟨rfl, rfl⟩ := N.slot_uniq hj0 hj hφ0 hg
  simp only
  rw [← getElem_eq_getElem! hj, hr]
  rfl

theorem allKeys_none {g : Nat} (h : auxAt tr nuser g = none) (ls : List Nat) (ps : List V) :
    allKeys M b rec nuser fams MJf ls ps g = carrier M ls b ps.reverse g := by
  unfold allKeys slotVal
  rw [dite_eq_right]; · rfl
  rintro ⟨⟨j, s⟩, hj, hge, hφ⟩
  have hi := N.images_mem hj hφ
  unfold auxAt at h
  rw [ite_eq_right (by omega), List.getElem?_eq_getElem hi] at h
  cases h

theorem keyArgs_users {Ds : List VExpr} (hDs : ∀ D ∈ Ds, mentions (tr.aux.map (·.name)) D = false)
    {C₁ C₂ : List Nat → List V → Nat → V}
    (hC : ∀ s < b.ntypes, s < nuser → ∀ ls ρ, C₁ ls ρ s = C₂ ls ρ s) (ls : List Nat) (ρ : List V) :
    keyArgs (M₁ M b C₁) ls Ds ρ = keyArgs (M₁ M b C₂) ls Ds ρ := by
  unfold keyArgs
  congr 1
  refine List.map_congr_left fun D hD => interp_congr ?_ ρ
  refine (constsIn_of_mentions (hDs D hD)).mono fun c hc => M₁_agree fun s hs hn ls' ρ' => ?_
  by_cases hsu : s < nuser
  · exact hC s hs hsu ls' ρ'
  · exact absurd (hn ▸ N.aux_slot_name hs hsu) hc

theorem slotSpec {j : Nat} (hj : j < fams.length) {r : RBlock} (hr : rec[fams[j].ri]? = some r)
    {σ : Nat} (hσ : σ < r.b.ntypes) : ∃ a, tr.aux[fams[j].φ[σ]!]? = some a ∧
      Slot rec b.nparams tr b nuser fams a (r.b.types[σ]!).name fams[j].lv fams[j].Ds r σ
        (nuser + fams[j].φ[σ]!) := by
  obtain ⟨r', hr', ⟨hlen, hD, -, -, hdf, hkeys, hslot⟩, -⟩ := N.famsOK.1 j hj
  rw [hr, Option.some.injEq] at hr'; subst hr'
  have hσ' : σ < fams[j].φ.length := hlen ▸ hσ
  obtain ⟨a, t, tJ, ha, ht, htJ, hind, hnc, hcc⟩ := hslot σ hσ'
  obtain ⟨a', key, ha', hkey, hka⟩ := hkeys σ hσ'
  rw [ha, Option.some.injEq] at ha'; subst ha'
  have hrm : r ∈ rec := List.mem_of_getElem? hr
  have eφ : fams[j].φ[σ]! = fams[j].φ[σ] := (getElem_eq_getElem! hσ').symm
  rw [← eφ] at ha ht
  have htJ' : r.b.types[σ]! = tJ := by
    rw [← getElem_eq_getElem! (show σ < r.b.types.length from hσ)]
    exact Option.some.inj ((List.getElem?_eq_getElem _).symm.trans htJ)
  have hdl : nuser + fams[j].φ[σ]! < b.ntypes := (List.getElem?_eq_some_iff.mp ht).1
  have ht' : b.types[nuser + fams[j].φ[σ]!]! = t := by
    rw [← getElem_eq_getElem! hdl]
    exact Option.some.inj ((List.getElem?_eq_getElem _).symm.trans ht)
  refine ⟨a, ha, ⟨j, hj, rfl, rfl, hr, Nat.le_add_right _ _, by
    rw [Nat.add_sub_cancel_left, eφ, List.getElem?_eq_getElem hσ'], by
    rw [Nat.add_sub_cancel_left]; exact ha⟩, hrm, hσ, rfl, ⟨key, hkey, hka⟩,
    hdf, hdl,
    N.member_name ha hdl, hD, by rw [ht', htJ']; exact hind,
    by rw [ht', htJ']; exact hnc, ?_, ?_⟩
  all_goals
    intro q hq
    rw [ht'] at hq
    have hqJ : q < tJ.ctors.length := hnc ▸ hq
    have hc := hcc q hq hqJ
    simp only [RBlock.info]
    rw [htJ', getElem!_map' _ hqJ, ht', ← getElem_eq_getElem! hq, ← getElem_eq_getElem! hqJ]
  · exact hc.1
  · exact hc.2.1

theorem slot_of_index {i : Nat} (hi : i < tr.aux.length) :
    ∃ J lv Ds r m, Slot rec b.nparams tr b nuser fams tr.aux[i] J lv Ds r m (nuser + i) := by
  obtain ⟨F, hF, hiF⟩ := List.mem_flatMap.mp (N.famsOK.2.mem_iff.mpr (List.mem_range.mpr hi))
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hF
  obtain ⟨σ, hσ, hσi⟩ := List.getElem_of_mem hiF
  obtain ⟨r, hr, ⟨hlen, -⟩, -⟩ := N.famsOK.1 j hj
  obtain ⟨a, ha', hs⟩ := N.slotSpec hj hr (hlen ▸ hσ)
  rw [← getElem_eq_getElem! hσ, hσi, List.getElem?_eq_getElem hi, Option.some.injEq] at ha'
  rw [← getElem_eq_getElem! hσ, hσi] at hs
  subst ha'
  exact ⟨_, _, _, r, σ, hs⟩

theorem aux_mem_spec {a : Aux} (ha : a ∈ tr.aux) : ∃ J lv Ds r m d,
    Slot rec b.nparams tr b nuser fams a J lv Ds r m d := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
  obtain ⟨J, lv, Ds, r, m, hs⟩ := N.slot_of_index hi
  exact ⟨J, lv, Ds, r, m, _, hs⟩

theorem aux : AllSpec rec b.nparams tr b nuser fams := fun _ ha => N.aux_mem_spec ha

theorem auxSpec_at {g : Nat} {a : Aux} (h : auxAt tr nuser g = some a) :
    a ∈ tr.aux ∧ ∃ J lv Ds r m, Slot rec b.nparams tr b nuser fams a J lv Ds r m g := by
  unfold auxAt at h
  split at h; · cases h
  rename_i hge
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp h
  obtain ⟨J, lv, Ds, r, m, hs⟩ := N.slot_of_index hi
  rw [Nat.add_sub_cancel' (Nat.le_of_not_lt hge)] at hs
  exact ⟨List.getElem_mem hi, J, lv, Ds, r, m, hs⟩

theorem argsTyped {a : Aux} {lv : List VLevel} {Ds : List VExpr} {r : RBlock} {m d : Nat}
    (hf : FamLink rec tr nuser fams a lv Ds r m d) :
    ArgsTyped envT b.uvars b.params.reverse (r.b.params.map (·.instL lv)) Ds := by
  obtain ⟨j, hj, rfl, rfl, hr, -⟩ := hf
  obtain ⟨r', hr', -, hargs⟩ := N.famsOK.1 j hj
  rw [hr, Option.some.injEq] at hr'; subst hr'
  exact hargs

theorem modelT : IsModel (M₃ M b) envT ∧ Good envT := N.S.model_add N.hT

theorem envT_agree : ∀ c, Dom env c → M₃ M b c = M c := fun c hc => by
  obtain ⟨e₂, e₃, h2, h3, he⟩ := N.envT_split
  rw [BlockModel.Setting.hag₃₁ h2 h3 c (Dom.mono N.S.le₁ hc)]
  exact N.S.agree hc

theorem key_dom {a : Aux} {J : Name} {lv : List VLevel} {Ds : List VExpr} {r : RBlock}
    {m d : Nat} (hs : Slot rec b.nparams tr b nuser fams a J lv Ds r m d) :
    ∀ D ∈ Ds, ConstsIn (fun c => (Dom env₁ c ∨ c ∈ b.ctors.map (·.name)) ∧
      c ∉ keyHidden tr b nuser) D := by
  obtain ⟨e₂, e₃, h2, h3, he⟩ := N.envT_split
  have hdomT : ∀ c, Dom env c → Dom envT c := fun c h => by
    rw [he]; exact dom_iotaFold.mpr (Dom.mono (VEnv.LE.trans N.S.le₁
      (VEnv.LE.trans (addFold_spec h2).2.2.1 (addFold_spec h3).2.2.1)) h)
  have hkt := N.argsTyped hs.link
  intro D hD
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hD
  have hcT : ConstsIn (Dom envT) Ds[i] :=
    (IsDefEq.constsIn N.modelT.2.2 (hkt.2 i hi (by simpa [hkt.1] using hi))
      fun B hB => (N.S.params_consts' B (List.mem_reverse.mp hB)).mono hdomT).1
  refine (hcT.and (constsIn_of_mentions (hs.hidden _ hD))).mono fun c ⟨hc, hnh⟩ => ⟨?_, hnh⟩
  rw [he, dom_iotaFold] at hc
  obtain ⟨ci, hci⟩ := Option.ne_none_iff_exists'.mp hc
  rcases (addFold_spec h3).2.2.2.1 c ci hci with ⟨x, hx, hxc, -⟩ | h₂
  · exfalso; apply hnh
    obtain ⟨d', hd', rfl⟩ := List.mem_map.mp hx
    simp only [keyHidden, auxNames, List.mem_append, List.mem_map]
    exact Or.inr ⟨d', hd', hxc⟩
  rcases (addFold_spec h2).2.2.2.1 c ci h₂ with ⟨x, hx, hxc, -⟩ | h₁
  · obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hx
    exact Or.inr (hxc ▸ List.mem_map.mpr ⟨c', hc', rfl⟩)
  · exact Or.inl (by unfold Dom; rw [h₁]; simp)

omit [SetTheory V] N in
theorem ctor_of_user {c : Name} (h : c ∈ ((b.types.take nuser).flatMap (·.ctors)).map (·.name)) :
    c ∈ b.ctors.map (·.name) := by
  obtain ⟨c', hc', rfl⟩ := List.mem_map.mp h
  refine List.mem_map.mpr ⟨c', ?_, rfl⟩
  rw [b.ctors_split nuser]; exact List.mem_append_left _ hc'

omit [SetTheory V] N in
theorem user_of_key {c : Name} (hc : c ∈ b.ctors.map (·.name)) (hnh : c ∉ keyHidden tr b nuser) :
    c ∈ ((b.types.take nuser).flatMap (·.ctors)).map (·.name) := by
  obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hc
  rw [b.ctors_split nuser] at hc'
  rcases List.mem_append.mp hc' with hu | ha
  · exact List.mem_map.mpr ⟨c', hu, rfl⟩
  · exfalso; apply hnh
    obtain ⟨t, ht, hct⟩ := List.mem_flatMap.mp ha
    simp only [keyHidden, auxNames, List.mem_append, List.mem_flatMap, List.mem_map]
    exact Or.inl (Or.inr ⟨t, ht, c', hct, rfl⟩)

theorem key_agree {a : Aux} {J : Name} {lv : List VLevel} {Ds : List VExpr} {r : RBlock}
    {m d : Nat} (hs : Slot rec b.nparams tr b nuser fams a J lv Ds r m d)
    {X : List Nat → List V → Nat → V}
    (hX : ∀ s < b.ntypes, s < nuser → ∀ ls ρ, X ls ρ s = carrier M ls b ρ s) :
    ∀ D ∈ Ds, ConstsIn (fun c => M₁ M b X c = M₃ M b c) D := by
  obtain ⟨e₂, e₃, h2, h3, he⟩ := N.envT_split
  refine fun D hD => (N.key_dom hs D hD).mono fun c ⟨hc, hnh⟩ => ?_
  rcases hc with hdom₁ | hcm
  · rw [BlockModel.Setting.hag₃₁ h2 h3 c hdom₁]
    refine M₁_agree fun s hs' hsn ls ρ => ?_
    by_cases hsu : s < nuser
    · exact hX s hs' hsu ls ρ
    · exfalso; apply hnh
      simp only [keyHidden, auxNames, List.mem_append]
      exact Or.inl (Or.inl (hsn ▸ N.aux_slot_name hs' hsu))
  · have hnn : c ∉ b.names := fun hn =>
      (List.nodup_append.mp N.S.hwf.syn.nodup).2.2 _ hn _ hcm rfl
    rw [M₁_other hnn, BlockModel.Setting.hag₃ h3 c (BlockModel.Setting.ctor_dom h2 hcm)]
    exact N.base c hcm

theorem link_fam {a : Aux} {lv : List VLevel} {Ds : List VExpr} {r : RBlock} {m d : Nat}
    (hf : FamLink rec tr nuser fams a lv Ds r m d) :
    lv.length = r.b.uvars ∧ b.level ≈ r.b.level.inst lv := by
  obtain ⟨j, hj, rfl, rfl, hr, -⟩ := hf
  obtain ⟨r', hr', ⟨-, -, hlv, hlev, -⟩, -⟩ := N.famsOK.1 j hj
  rw [hr, Option.some.injEq] at hr'; subst hr'
  exact ⟨hlv, hlev⟩

theorem link_ctorCorr {a : Aux} {J : Name} {lv : List VLevel} {Ds : List VExpr} {r : RBlock}
    {m d : Nat} (hs : Slot rec b.nparams tr b nuser fams a J lv Ds r m d) {j : Nat}
    (hj : j < fams.length) (hlv : fams[j].lv = lv) (hDs : fams[j].Ds = Ds)
    (hr : rec[fams[j].ri]? = some r) (hφ : fams[j].φ[m]? = some (d - nuser)) :
    ∀ q < (b.types[d]!).ctors.length, Spec.CtorCorr tr b nuser
        { ri := fams[j].ri, lv, Ds, φ := fams[j].φ }
      (images (fams.take j)) r a (r.b.types[m]!) ((b.types[d]!).ctors[q]!)
      ((r.b.types[m]!).ctors[q]!) := by
  intro q hq
  obtain ⟨r', hr', ⟨hlen, -, -, -, -, -, hslot⟩, -⟩ := N.famsOK.1 j hj
  rw [hr, Option.some.injEq] at hr'; subst hr'
  have hm : m < fams[j].φ.length := (List.getElem?_eq_some_iff.mp hφ).1
  obtain ⟨a', t, tJ, ha', ht, htJ, -, hnc, hcc⟩ := hslot m hm
  obtain ⟨-, -, -, -, -, hge, -, haux⟩ := hs.link
  have eφm : fams[j].φ[m] = d - nuser := Option.some.inj ((List.getElem?_eq_getElem
      hm).symm.trans hφ)
  rw [eφm, haux, Option.some.injEq] at ha'
  subst ha'
  rw [eφm, Nat.add_sub_cancel' hge] at ht
  have et : b.types[d]! = t := by
    rw [← getElem_eq_getElem! hs.hd]; exact Option.some.inj ((List.getElem?_eq_getElem
        _).symm.trans ht)
  have hmr : m < r.b.ntypes := (List.getElem?_eq_some_iff.mp htJ).1
  have etJ : r.b.types[m]! = tJ := by
    rw [← getElem_eq_getElem! hmr]; exact Option.some.inj ((List.getElem?_eq_getElem
        _).symm.trans htJ)
  subst hlv hDs
  rw [et] at hq ⊢
  rw [etJ, ← getElem_eq_getElem! hq, ← getElem_eq_getElem! (hnc ▸ hq)]
  exact hcc q hq (hnc ▸ hq)

theorem lev_aux {a : Aux} {lv : List VLevel} {Ds : List VExpr} {r : RBlock} {m d : Nat}
    (hf : FamLink rec tr nuser fams a lv Ds r m d) (ls : List Nat) :
    lev ls b = lev (lv.map (VLevel.eval ls)) r.b := by
  unfold lev
  rw [congrFun (N.link_fam hf).2 ls, VLevel.eval_inst]

theorem allKeys_aux {n : Nat} {a : Aux} {J : Name} {lv : List VLevel} {Ds : List VExpr}
    {r : RBlock} {m d : Nat} (hs : Slot rec n tr b nuser fams a J lv Ds r m d)
    (ls : List Nat) (ps : List V) :
    allKeys M b rec nuser fams MJf ls ps d = carrier (MJf r) (lv.map (VLevel.eval ls)) r.b
      (keyArgs (M₁ M b (carrierFn M b)) ls Ds ps.reverse) m := by
  obtain ⟨j, hj, rfl, rfl, hr, hge, hφ, -⟩ := hs.link
  have := N.allKeys_slot hj hr hφ (ls := ls) (ps := ps)
  rwa [Nat.add_sub_cancel' hge] at this

end NWF

theorem Slot.auxAt_eq {rec : List RBlock} {n : Nat} {tr : Translated} {b : SBlock} {nuser : Nat}
    {fams : List Fam} {a : Aux} {J : Name} {lv : List VLevel} {Ds : List VExpr} {r : RBlock}
    {m d : Nat} (hs : Slot rec n tr b nuser fams a J lv Ds r m d) : auxAt tr nuser d = some a := by
  obtain ⟨-, -, -, -, -, hge, -, haux⟩ := hs.link
  unfold auxAt; rw [ite_eq_right (by omega)]; exact haux

namespace NWF
variable {M : CInterp V} {env env₁ envT : VEnv} {b : SBlock} {rec : List RBlock} {tr : Translated}
  {nuser : Nat} {fams : List Fam} {MJf : RBlock → CInterp V} {envJf envJ₁f : RBlock → VEnv}
  (N : NWF M env env₁ envT b rec tr nuser fams MJf envJf envJ₁f)
include N

omit [SetTheory V] N in
theorem m_lt {a : Aux} {J : Name} {lv : List VLevel} {Ds : List VExpr} {r : RBlock} {m d : Nat}
    (hs : Slot rec b.nparams tr b nuser fams a J lv Ds r m d) : m < r.b.ntypes := hs.m_lt

theorem allKeys_mem (ls : List Nat) (ps : List V) :
    InTupleSpace (lev ls b) b.ntypes (Is M ls b ps.reverse) (allKeys M b rec nuser fams MJf
        ls ps) := by
  intro g hg
  cases h : auxAt tr nuser g with
  | none => rw [N.allKeys_none h]; exact carrier_mem g hg
  | some a =>
    obtain ⟨-, J, lv, Ds, r, m, hs⟩ := N.auxSpec_at h
    have hr := hs.mem
    rw [N.allKeys_aux hs, N.lev_aux hs.link,
      aux_Is N.S (N.canon r hr) hs (NWF.m_lt hs) (carrierFn M b) ls ps.reverse]
    exact carrier_mem m (NWF.m_lt hs)

theorem patch_user (ls : List Nat) (ps : List V) :
    ∀ s < b.ntypes, s < nuser → ∀ ls' ρ',
      patch M b ls ps.reverse (allKeys M b rec nuser fams MJf ls ps) ls' ρ' s =
          carrier M ls' b ρ' s :=
  fun s _ hsu ls' ρ' => by
    by_cases h' : ls' = ls ∧ ρ' = ps.reverse
    · obtain ⟨rfl, rfl⟩ := h'
      rw [patch_at, N.allKeys_none (by unfold auxAt; rw [ite_eq_left hsu])]
    · simp [patch, h']

theorem keyArgs_patch {Ds : List VExpr} (hDs : ∀ D ∈ Ds, mentions (tr.aux.map (·.name)) D = false)
    (ls : List Nat) (ps : List V) (ρ : List V) :
    keyArgs (M₁ M b (patch M b ls ps.reverse (allKeys M b rec nuser fams MJf ls ps))) ls Ds ρ =
      keyArgs (M₁ M b (carrierFn M b)) ls Ds ρ :=
  N.keyArgs_users hDs (N.patch_user ls ps) ls ρ

end NWF

namespace NWF
variable {M : CInterp V} {env env₁ envT : VEnv} {b : SBlock} {rec : List RBlock} {tr : Translated}
  {nuser : Nat} {fams : List Fam} {MJf : RBlock → CInterp V} {envJf envJ₁f : RBlock → VEnv}
  (N : NWF M env env₁ envT b rec tr nuser fams MJf envJf envJ₁f)
include N

theorem cert_length : tr.types.length = b.types.length := by
  have := congrArg List.length N.cert.2.2; simpa using this.symm

theorem cert_get (i : Nat) (hi : i < b.types.length) :
    (tr.types[i]'(N.cert_length ▸ hi)).name = (b.types[i]).name ∧
      (tr.types[i]'(N.cert_length ▸ hi)).ctors = (b.types[i]).ctors.map fun c =>
          (c.name, c.type) := by
  have h := congrArg (·[i]?) N.cert.2.2
  simp only [List.getElem?_map, List.getElem?_eq_getElem hi,
    List.getElem?_eq_getElem (N.cert_length ▸ hi), Option.map_some, Option.some.injEq,
    Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2.2.symm⟩

theorem ctor_not_name {c : Name} (hc : c ∈ (b.types.drop nuser).flatMap (·.ctors.map (·.name))) :
    c ∉ b.names := by
  have hnd := N.S.hwf.syn.nodup
  have hc' : c ∈ b.ctors.map (·.name) := by
    obtain ⟨t, ht, hct⟩ := List.mem_flatMap.mp hc
    obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hct
    exact List.mem_map.mpr ⟨c', List.mem_flatMap.mpr ⟨t, List.mem_of_mem_drop ht, hc'⟩, rfl⟩
  exact fun hn => (List.nodup_append.mp hnd).2.2 _ hn _ hc' rfl

theorem auxCtor_iff (c : Name) :
    (tr.auxOfCtor? c).isSome ↔ c ∈ (b.types.drop nuser).flatMap (·.ctors.map (·.name)) := by
  unfold Translated.auxOfCtor?
  rw [List.find?_isSome]
  constructor
  · rintro ⟨a, ha, hp⟩
    cases ht : tr.types.find? (·.name == a.name) with
    | none => simp [ht] at hp
    | some t =>
      simp only [ht, Option.any_some, List.any_eq_true, beq_iff_eq] at hp
      obtain ⟨p, hp, rfl⟩ := hp
      obtain ⟨htn, i, hi, rfl, _⟩ := List.find?_eq_some_iff_getElem.mp ht
      simp only [beq_iff_eq] at htn
      have hib : i < b.types.length := N.cert_length ▸ hi
      obtain ⟨hname, hctors⟩ := N.cert_get i hib
      have hge : nuser ≤ i := N.slot_ge hib ha (by
        rw [← getElem_eq_getElem! hib, ← hname, htn])
      rw [hctors] at hp
      obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hp
      refine List.mem_flatMap.mpr ⟨b.types[i], ?_, List.mem_map_of_mem hc'⟩
      exact List.mem_iff_getElem.mpr ⟨i - nuser, by simp; omega, by
        rw [List.getElem_drop]; congr 1; omega⟩
  · intro h
    obtain ⟨t, ht, hct⟩ := List.mem_flatMap.mp h
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ht
    have hj' : nuser + j < b.types.length := by simp at hj; omega
    have et : (b.types.drop nuser)[j] = b.types[nuser + j] := List.getElem_drop ..
    have hmem : (b.types[nuser + j]).name ∈ tr.aux.map (·.name) := by
      rw [← N.drop_names, ← et]; exact List.mem_map_of_mem (List.getElem_mem _)
    obtain ⟨a, ha, han⟩ := List.mem_map.mp hmem
    refine ⟨a, ha, ?_⟩
    have hi : nuser + j < tr.types.length := N.cert_length ▸ hj'
    have hfind : tr.types.find? (·.name == a.name) = some (tr.types[nuser + j]'hi) := by
      refine List.find?_eq_some_iff_getElem.mpr ⟨?_, nuser + j, hi, rfl, fun k hk => ?_⟩
      · simp [(N.cert_get _ hj').1, han]
      · have hkb : k < b.types.length := by omega
        have hne : (b.types[k]).name ≠ (b.types[nuser + j]).name := fun e => by
          have := N.slot_unique (d := k) (g := nuser + j) hkb hj' (by
            rw [← getElem_eq_getElem! hkb,
              ← getElem_eq_getElem! hj', e])
          omega
        simp only [(N.cert_get k hkb).1, han, Bool.not_eq_true', beq_eq_false_iff_ne]
        intro e; apply hne; first | exact e | exact e.trans han.symm | exact e.trans han
    rw [hfind]
    simp only [Option.any_some, List.any_eq_true, beq_iff_eq, (N.cert_get _ hj').2]
    rw [et] at hct
    obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hct
    exact ⟨_, List.mem_map_of_mem hc', rfl⟩

end NWF

namespace NWF
variable {M : CInterp V} {env env₁ envT : VEnv} {b : SBlock} {rec : List RBlock} {tr : Translated}
  {nuser : Nat} {fams : List Fam} {MJf : RBlock → CInterp V} {envJf envJ₁f : RBlock → VEnv}
  (N : NWF M env env₁ envT b rec tr nuser fams MJf envJf envJ₁f)
include N

theorem ns_iff (c : Name) :
    c ∈ auxNs tr b nuser ↔ ((tr.aux.find? (·.name == c)).isSome ∨ (tr.auxOfCtor? c).isSome) := by
  unfold auxNs auxNames
  rw [List.mem_append, N.auxCtor_iff, List.find?_isSome]
  simp only [List.mem_map, beq_iff_eq]

theorem key_fresh {a : Aux} {J : Name} {lv : List VLevel} {Ds : List VExpr} {r : RBlock} {m d : Nat}
    (hs : Slot rec b.nparams tr b nuser fams a J lv Ds r m d) :
    ConstsIn (fun c => c ∉ tr.aux.map (·.name)) a.key := by
  obtain ⟨k, -, he, -, hkc, -⟩ := hs.read (N.canon r hs.mem)
  refine EqL.constsIn he (constsIn_subst (constsIn_argSubst fun D hD =>
    constsIn_of_mentions (hs.dsfree D hD)) (constsIn_instL.mpr (hkc.mono fun c hc hm => ?_)))
  exact N.S.not_name hc (by rw [N.names_split]; exact List.mem_append_right _ hm)

theorem aux_length : tr.aux.length = b.ntypes - nuser := by
  have := congrArg List.length N.drop_names
  simp only [List.length_map, List.length_drop] at this
  exact this.symm

theorem find_type {g : Nat} (hg : g < b.types.length) :
    tr.types.find? (·.name == (b.types[g]).name) = some (tr.types[g]'(N.cert_length ▸ hg)) := by
  refine List.find?_eq_some_iff_getElem.mpr ⟨by simp [(N.cert_get g hg).1], g, N.cert_length ▸ hg,
    rfl, fun k hk => ?_⟩
  have hkb : k < b.types.length := by omega
  have hne : (b.types[k]).name ≠ (b.types[g]).name := fun e => by
    have := N.slot_unique (d := k) (g := g) hkb hg (by
      rw [← getElem_eq_getElem! hkb, ← getElem_eq_getElem! hg, e])
    omega
  simpa [(N.cert_get k hkb).1] using hne

theorem auxCtor_not_aux {c : Name} {a : Aux} (h : tr.auxOfCtor? c = some a) :
    tr.aux.find? (·.name == c) = none := by
  have hc := (N.auxCtor_iff c).mp (by simp [h])
  rw [List.find?_eq_none]
  intro a' ha' hn
  simp only [beq_iff_eq] at hn
  apply N.ctor_not_name hc
  rw [N.names_split, ← hn]
  exact List.mem_append_right _ (List.mem_map_of_mem ha')

theorem auxCtor_none_of_dom {c : Name} (hc : Dom env₁ c) : tr.auxOfCtor? c = none := by
  cases h : tr.auxOfCtor? c with
  | none => rfl
  | some a =>
    exfalso
    have hm := (N.auxCtor_iff c).mp (by simp [h])
    have hd := N.S.dom_of_dom₁ hc (N.ctor_not_name hm)
    obtain ⟨t, ht, hct⟩ := List.mem_flatMap.mp hm
    obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hct
    have hf := List.all_eq_true.mp N.fresh.1 t ht
    have := List.all_eq_true.mp hf c' hc'
    simp only [Option.isNone_iff_eq_none] at this
    exact hd this

end NWF

namespace NWF
variable {M : CInterp V} {env env₁ envT : VEnv} {b : SBlock} {rec : List RBlock} {tr : Translated}
  {nuser : Nat} {fams : List Fam} {MJf : RBlock → CInterp V} {envJf envJ₁f : RBlock → VEnv}
  (N : NWF M env env₁ envT b rec tr nuser fams MJf envJf envJ₁f)
include N

theorem restoreHyp {ls : List Nat} {ps : List V} (hl : ls.length = b.uvars)
    (hps : Ext M ls b.params [] ps) :
    RestoreHyp (canonOverride M b (patch M b ls ps.reverse (allKeys M b rec nuser fams MJf ls
        ps)) ls tr ps)
      (M₁ M b (patch M b ls ps.reverse (allKeys M b rec nuser fams MJf ls ps))) ls tr []
      (auxNs tr b nuser) (auxMs tr b nuser) (ownLevels b.uvars) b.nparams (· = ps) := by
  refine restoreHyp_canon hl hps N.ns_iff (fun c h => List.mem_append_left _ h)
    (fun c a h => N.auxCtor_not_aux h) (fun a ha => ?_) (fun a ha => ?_) (fun a ha => ?_)
  all_goals obtain ⟨J, lv, Ds, r, m, d, hs⟩ := N.aux_mem_spec ha
  · obtain ⟨k, -, he, -, -, ⟨c, us, as, rfl⟩, -⟩ := hs.read (N.canon r hs.mem)
    rw [atKey_appN_const] at he
    obtain ⟨us', as', he', -, -⟩ := EqL.appN_const he
    exact ⟨c, us', as', by rw [he', headArgs_appN_const]⟩
  · exact key_closed N.S (N.canon r hs.mem) hs N.modelT.2 (N.argsTyped hs.link)
  · have hr := hs.mem
    refine aux_keys N.S (N.canon r hr) hs (NWF.m_lt hs) N.S.nodup N.modelT.1 N.envT_agree
      (N.argsTyped hs.link) (N.link_fam hs.link).1 (N.key_agree hs (N.patch_user ls ps)) hps ?_
    rw [patch_at, N.allKeys_aux hs, N.keyArgs_patch hs.dsfree]

theorem frame {a : Aux} (_ha : a ∈ tr.aux) {J : Name} {lv : List VLevel} {Ds : List VExpr}
    {r : RBlock} {m d : Nat} (hs : Slot rec b.nparams tr b nuser fams a J lv Ds r m d)
    {j : Nat} (hj : j < fams.length) (hlv : fams[j].lv = lv) (hDs : fams[j].Ds = Ds)
    (hr : rec[fams[j].ri]? = some r) (hφ : fams[j].φ[m]? = some (d - nuser))
    {ls : List Nat} {ps : List V} (hl : ls.length = b.uvars) (hps : Ext M ls b.params [] ps) :
    AuxFrame M env env₁ b (MJf r) (envJf r) (envJ₁f r) rec b.nparams tr a J lv Ds r m d nuser fams
      fams[j].ri fams[j].φ (images (fams.take j)) ls ps
      (allKeys M b rec nuser fams MJf ls ps)
      (canonOverride M b (patch M b ls ps.reverse (allKeys M b rec nuser fams MJf ls ps)) ls tr ps)
      (auxNs tr b nuser) (auxMs tr b nuser) (ownLevels b.uvars) := by
  have hrm : r ∈ rec := List.mem_of_getElem? hr
  have cJ := N.canon r hrm
  have SJ := cJ.setting
  have hm := NWF.m_lt hs
  have hf := hs.link
  have hdge : nuser ≤ d := by obtain ⟨_, _, _, _, _, h, _⟩ := hf; exact h
  refine ⟨N.S, cJ, N.aux, hs, rfl, hm, N.link_ctorCorr hs hj hlv hDs hr hφ, hl, hps,
    N.allKeys_mem ls ps, N.restoreHyp hl hps, fun q hq k hk => ?_, fun q hq k hk => ?_,
    by simp [(N.link_fam hf).1], ?_⟩
  · exact field_restoreSafe N.S N.safe hdge hs.hd (getElem!_mem' hq) hk
  · exact (N.S.field_scoped (P := Dom env₁) (fun _ h => h) hs.hd (getElem!_mem' hq) hk).2.mono
      fun c hc => canonOverride_of_none (N.auxCtor_none_of_dom hc)
  · have := keyArgs_ext N.S cJ N.modelT.1 N.envT_agree (N.argsTyped hf)
      (N.key_agree hs (N.patch_user ls ps)) hps
    simpa [keyArgs] using this

theorem frameOf {a : Aux} (ha : a ∈ tr.aux) {J : Name} {lv : List VLevel} {Ds : List VExpr}
    {r : RBlock} {m d : Nat} (hs : Slot rec b.nparams tr b nuser fams a J lv Ds r m d)
    {ls : List Nat} {ps : List V} (hl : ls.length = b.uvars) (hps : Ext M ls b.params [] ps) :
    ∃ ri φ earlier, AuxFrame M env env₁ b (MJf r) (envJf r) (envJ₁f r) rec b.nparams tr a J lv Ds
      r m d nuser fams ri φ earlier ls ps (allKeys M b rec nuser fams MJf ls ps)
      (canonOverride M b (patch M b ls ps.reverse (allKeys M b rec nuser fams MJf ls ps)) ls tr ps)
      (auxNs tr b nuser) (auxMs tr b nuser) (ownLevels b.uvars) :=
  let ⟨_, hj, hlv, hDs, hr, _, hφ, _⟩ := hs.link
  ⟨_, _, _, N.frame ha hs hj hlv hDs hr hφ hl hps⟩

end NWF

end Soulgem.Nested
