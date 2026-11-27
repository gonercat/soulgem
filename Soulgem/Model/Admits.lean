import Soulgem.Model.EtaProjCore
import Soulgem.Model.CertEnv
import Soulgem.Model.BlockCongr

/-!
# Every admitted environment has a model

`Admits base env rec` builds `env` from `base` by definitions, opaque constants, plain mutual
blocks, structure eta through projection functions and nested blocks; `rec` records the blocks.
-/

namespace Soulgem.Nested
open ConLeche ConLeche.SetTheory ConLeche.SetTheory.Tower Lean4Lean Spec BlockSem BlockModel

universe u

variable {V : Type u} [SetTheory V]

theorem userSlot {M MJ : CInterp V} {env : VEnv} {r : RBlock} {σ : Nat} (hσ : σ < r.nuser)
    (hnu : r.nuser ≤ r.b.ntypes) (hdom : Dom env (r.b.types[σ]!).name)
    (ht : M (r.b.types[σ]!).name = M₁ MJ r.b (carrierFn MJ r.b) (r.b.types[σ]!).name) :
    ∃ k, r.slotKey σ = some k ∧ k.ClosedN r.b.nparams ∧ ConstsIn (Dom env) k ∧
      (∃ c us as, k = appN (.const c us) as) ∧
      ∀ ls ρ, ls.length = r.b.uvars → Ext MJ ls r.b.params [] ρ →
        interp M ls k ρ.reverse = ρ.foldl app (M₁ MJ r.b (carrierFn MJ r.b)
            (r.b.types[σ]!).name ls) := by
  have hσt : σ < r.b.types.length := Nat.lt_of_lt_of_le hσ hnu
  refine ⟨appN (.const (r.b.types[σ]!).name (ownLevels r.b.uvars)) (vars r.b.nparams 0 r.b.nparams),
    by unfold RBlock.slotKey; rw [ite_eq_left hσ, List.getElem?_eq_getElem hσt, Option.map_some,
      getElem_eq_getElem! hσt], closedN_ownKey _ _ _, ?_, ⟨_, _, _, rfl⟩, fun ls ρ hl hρ => ?_⟩
  · refine (constsIn_appN _ _).mpr ⟨hdom, fun D hD => ?_⟩
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hD
    trivial
  · rw [interp_ownKey M ls hl (by rw [Ext.length_eq _ _ hρ]; rfl), ht]

theorem userSlotCtor {M MJ : CInterp V} {env : VEnv} {r : RBlock} {σ : Nat} (hσ : σ < r.nuser)
    (hnu : r.nuser ≤ r.b.ntypes) {q : Nat} {c : SCtor}
    (hc : Dom env c.name ∧ M c.name = fun ls => Setting.ctorVal r.b (Setting.Mc MJ r.b) ls q c) :
    ∀ k, r.slotKey σ = some k → ∀ Ic Ils Ds, headArgs k = (.const Ic Ils, Ds) →
      Dom env (c.name.replacePrefix (r.b.types[σ]!).name Ic) ∧
      ∀ ls ρ, ls.length = r.b.uvars → Ext MJ ls r.b.params [] ρ →
        interp M ls (appN (.const (c.name.replacePrefix (r.b.types[σ]!).name Ic) Ils)
            Ds) ρ.reverse =
          ρ.foldl app (Setting.ctorVal r.b (Setting.Mc MJ r.b) ls q c) := by
  intro k hk Ic Ils Ds hh
  have hσt : σ < r.b.types.length := Nat.lt_of_lt_of_le hσ hnu
  unfold RBlock.slotKey at hk
  rw [ite_eq_left hσ, List.getElem?_eq_getElem hσt, Option.map_some, Option.some.injEq,
    getElem_eq_getElem! hσt] at hk
  subst hk
  rw [headArgs_appN_const] at hh
  simp only [Prod.mk.injEq, VExpr.const.injEq] at hh
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hh
  rw [replacePrefix_same]
  refine ⟨hc.1, fun ls ρ hl hρ => ?_⟩
  rw [interp_ownKey M ls hl (by rw [Ext.length_eq _ _ hρ]; rfl), hc.2]

theorem CanonR.mono {M M' : CInterp V} {env env' : VEnv} {r : RBlock} {MJ : CInterp V}
    {envJ envJ₁ : VEnv} (C : CanonR M env r MJ envJ envJ₁) (hle : env ≤ env')
    (hag : ∀ c, Dom env c → M' c = M c) : CanonR M' env' r MJ envJ envJ₁ where
  setting := C.setting
  le := VEnv.LE.trans C.le hle
  agree := fun c hc => (hag c (Dom.mono C.le hc)).trans (C.agree c hc)
  slots := fun σ hσ => by
    obtain ⟨k, hk, hc, hcon, hform, hread⟩ := C.slots σ hσ
    exact ⟨k, hk, hc, hcon.mono fun _ h => Dom.mono hle h, hform, fun ls ρ hl hρ => by
      rw [interp_congr (hcon.mono fun c hc => hag c hc) _, hread ls ρ hl hρ]⟩
  slotCtors := fun σ hσ q c hc k hk Ic Ils Ds hh => by
    obtain ⟨hd, hv⟩ := C.slotCtors σ hσ q c hc k hk Ic Ils Ds hh
    obtain ⟨k', hk', -, hcon, ⟨c0, us0, as0, rfl⟩, -⟩ := C.slots σ hσ
    rw [hk, Option.some.injEq] at hk'
    subst hk'
    rw [headArgs_appN_const] at hh
    simp only [Prod.mk.injEq, VExpr.const.injEq] at hh
    obtain ⟨⟨-, -⟩, h3⟩ := hh
    have hcon' : ConstsIn (Dom env) (appN (.const (c.name.replacePrefix (r.b.types[σ]!).name
        Ic) Ils) Ds) :=
      (constsIn_appN _ _).mpr ⟨hd, h3 ▸ ((constsIn_appN _ _).mp hcon).2⟩
    exact ⟨Dom.mono hle hd, fun ls ρ hl hρ => by
      rw [interp_congr (hcon'.mono fun c hc => hag c hc) _, hv ls ρ hl hρ]⟩
  recs := fun h hd => by
    obtain ⟨e₂, e₃, h2, h3, hD, hv⟩ := C.recs h hd
    exact ⟨e₂, e₃, h2, h3, Dom.mono hle hD, (hag _ hD).trans hv⟩

structure RecInv (M : CInterp V) (env : VEnv) (rec : List RBlock) (MJf : RBlock → CInterp V)
    (envJf envJ₁f : RBlock → VEnv) : Prop where
  canon : ∀ r ∈ rec, CanonR M env r (MJf r) (envJf r) (envJ₁f r)

namespace RecInv
variable {M M' : CInterp V} {env env' : VEnv} {rec : List RBlock} {MJf : RBlock → CInterp V}
  {envJf envJ₁f : RBlock → VEnv}

theorem empty (M : CInterp V) (env : VEnv) (MJf : RBlock → CInterp V)
    (envJf envJ₁f : RBlock → VEnv) : RecInv M env [] MJf envJf envJ₁f :=
  ⟨nofun⟩

theorem mono (I : RecInv M env rec MJf envJf envJ₁f) (hle : env ≤ env')
    (hag : ∀ c, Dom env c → M' c = M c) : RecInv M' env' rec MJf envJf envJ₁f where
  canon := fun r hr => (I.canon r hr).mono hle hag

open Classical in
theorem push (I : RecInv M env rec MJf envJf envJ₁f) (hle : env ≤ env')
    (hag : ∀ c, Dom env c → M' c = M c) {rn : RBlock} {MJ : CInterp V} {envJ envJ₁ : VEnv}
    (C : CanonR M' env' rn MJ envJ envJ₁) :
    RecInv M' env' (rec ++ [rn]) (fun r => if r = rn then MJ else MJf r)
      (fun r => if r = rn then envJ else envJf r) (fun r => if r =
          rn then envJ₁ else envJ₁f r) where
  canon := fun r hr => by
    by_cases h : r = rn
    · subst h; simp only [ite_true]; exact C
    · simp only [ite_eq_right h]
      rcases List.mem_append.mp hr with hr | hr
      · exact (I.canon r hr).mono hle hag
      · exact absurd (List.mem_singleton.mp hr) h

end RecInv

theorem addConst_fresh {env env' : VEnv} {n : Name} {ci : VConstant}
    (h : env.addConst n ci = some env') : env.constants n = none := by
  unfold VEnv.addConst at h
  split at h
  · cases h
  · assumption

theorem step_plain {M : CInterp V} {env env' : VEnv} {rec : List RBlock}
    {MJf : RBlock → CInterp V} {envJf envJ₁f : RBlock → VEnv} (hM : IsModel M env) (hG : Good env)
    (I : RecInv M env rec MJf envJf envJ₁f) {b : SBlock} (hwf : b.WF env)
    (hadd : b.add env = some env') :
    ∃ (M' : CInterp V) (MJf' : RBlock → CInterp V) (envJf' envJ₁f' : RBlock → VEnv),
      IsModel M' (b.addEta env') ∧ Good (b.addEta env') ∧
        RecInv M' (b.addEta env') (rec ++ [RBlock.plain b]) MJf' envJf' envJ₁f' ∧
        env ≤ b.addEta env' ∧ ∀ c, Dom env c → M' c = M c := by
  obtain ⟨env₁, env₂, env₃, hwt, h2, h3, he⟩ := add_spec hadd
  have S : Setting M env env₁ b := ⟨hM, hG, hwf, hwt⟩
  obtain ⟨hM', hG'⟩ := S.model_add hadd
  subst he
  have hle₁ := S.le₁
  have hle₃ : env₁ ≤ iotaFold b env₃ :=
    VEnv.LE.trans (VEnv.LE.trans (addFold_spec h2).2.2.1 (addFold_spec h3).2.2.1)
        (le_iotaFold b env₃)
  have hle := VEnv.LE.trans hle₁ hle₃
  have hag : ∀ c, Dom env c → M₃ M b c = M c := fun c hc =>
    (BlockModel.Setting.hag₃₁ h2 h3 c (Dom.mono hle₁ hc)).trans (S.agree hc)
  have hct : ∀ d < b.ntypes, ∀ q (c : SCtor), (ctorsOf b d)[q]? = some c →
      Dom (iotaFold b env₃) c.name ∧ M₃ M b c.name = fun ls => Setting.ctorVal b
          (Setting.Mc M b) ls q c :=
    fun d hd q c hcq => ⟨Dom.mono (VEnv.LE.trans (addFold_spec h3).2.2.1 (le_iotaFold b env₃))
      (BlockModel.Setting.ctor_dom h2 (mem_ctors_name hcq)), BlockModel.Setting.hctor₃ h2 h3
          d hd q c hcq⟩
  have C : CanonR (M₃ M b) (iotaFold b env₃) (RBlock.plain b) M env env₁ :=
    { setting := S, le := hle, agree := hag,
      slots := fun σ hσ => userSlot (r := RBlock.plain b) hσ (Nat.le_refl _)
        (Dom.mono hle₃ (S.type_dom hσ)) (BlockModel.Setting.hag₃₁ h2 h3 _ (S.type_dom hσ)),
      slotCtors := fun σ hσ q c hc => userSlotCtor (r := RBlock.plain b) hσ (Nat.le_refl _)
        (hct σ hσ q c hc)
      recs := fun _ hd => ⟨env₂, env₃, h2, h3, Dom.mono (le_iotaFold b env₃)
        (BlockModel.Setting.rec_dom h3 (List.mem_map.mpr ⟨0, List.mem_range.mpr hd, rfl⟩)), rfl⟩ }
  obtain ⟨hMe, hGe⟩ := S.eta_model hadd hM' hG'
  exact ⟨_, _, _, _, hMe, hGe, (I.push hle hag C).mono (BlockModel.addEta_le b _) fun _ _ => rfl,
    VEnv.LE.trans hle (BlockModel.addEta_le b _), hag⟩

theorem restoreSafe_certTr {tr : Translated} {b : SBlock} {nuser : Nat} (rec : List RBlock)
    (fams : List Fam) : RestoreSafe (certTr tr rec fams) b nuser = RestoreSafe tr b nuser := by
  unfold RestoreSafe auxNames; rw [certTr_aux_names]

theorem auxMembers_certTr {tr : Translated} {b : SBlock} {nuser : Nat} (rec : List RBlock)
    (fams : List Fam) : AuxMembers (certTr tr rec fams) b nuser = AuxMembers tr b nuser := by
  unfold AuxMembers; rw [certTr_aux_names]

def SameDom (e₁ e₂ : VEnv) : Prop := ∀ n, (e₁.constants n).isNone = (e₂.constants n).isNone

theorem addConst_sameDom {e₁ e₂ e₁' : VEnv} {n : Name} {c₁ c₂ : VConstant} (hd : SameDom e₁ e₂)
    (h : e₁.addConst n c₁ = some e₁') : ∃ e₂', e₂.addConst n c₂ = some e₂' ∧ SameDom e₁' e₂' := by
  have h₁ := addConst_fresh h
  have h₂ : e₂.constants n = none := by
    have := hd n; rw [h₁] at this; simpa using this.symm
  unfold VEnv.addConst at h ⊢
  rw [h₁] at h; rw [h₂]
  cases h
  refine ⟨_, rfl, fun m => ?_⟩
  by_cases hm : n = m <;> simp [hm, hd m]

theorem foldlM_addConst_sameDom {α β : Type} (f₁ : α → Name) (g₁ : α → VConstant)
    (f₂ : β → Name) (g₂ : β → VConstant) :
    ∀ (l₁ : List α) (l₂ : List β), l₁.map f₁ = l₂.map f₂ → ∀ {e₁ e₂ e₁' : VEnv}, SameDom e₁ e₂ →
      l₁.foldlM (fun e x => e.addConst (f₁ x) (g₁ x)) e₁ = some e₁' →
      ∃ e₂', l₂.foldlM (fun e x => e.addConst (f₂ x) (g₂ x)) e₂ = some e₂' ∧ SameDom e₁' e₂'
  | [], [], _, _, _, _, hd, h => by cases h; exact ⟨_, rfl, hd⟩
  | [], _ :: _, hn, _, _, _, _, _ => by simp at hn
  | _ :: _, [], hn, _, _, _, _, _ => by simp at hn
  | x :: l₁, y :: l₂, hn, e₁, e₂, e₁', hd, h => by
    simp only [List.map_cons, List.cons.injEq] at hn
    simp only [List.foldlM_cons] at h ⊢
    obtain ⟨m, hm, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨m₂, hm₂, hd₂⟩ := addConst_sameDom (c₂ := g₂ y) hd hm
    rw [hn.1] at hm₂
    obtain ⟨e₂', h₂, hd'⟩ := foldlM_addConst_sameDom f₁ g₁ f₂ g₂ l₁ l₂ hn.2 hd₂ h
    exact ⟨e₂', by rw [hm₂]; exact h₂, hd'⟩

theorem nestedRecs_names_certTr (tr : Translated) (b : SBlock) (nuser : Nat) (rec : List RBlock)
    (fams : List Fam) :
    (nestedRecs (certTr tr rec fams) b nuser).map (·.name) = (nestedRecs tr b nuser).map
        (·.name) := by
  simp [nestedRecs]

theorem addNested_certTr {tr : Translated} {b : SBlock} {nuser : Nat} {env env' : VEnv}
    (rec : List RBlock) (fams : List Fam) (hadd : addNested tr b nuser env = some env') :
    ∃ envB, addNested (certTr tr rec fams) b nuser env = some envB := by
  unfold addNested at hadd ⊢
  have hd₀ : SameDom env env := fun _ => rfl
  obtain ⟨e₁, h₁, hadd⟩ := Option.bind_eq_some_iff.mp hadd
  obtain ⟨f₁, hf₁, hd₁⟩ := foldlM_addConst_sameDom _ _ _ _ _ _ rfl hd₀ h₁
  obtain ⟨e₂, h₂, hadd⟩ := Option.bind_eq_some_iff.mp hadd
  obtain ⟨f₂, hf₂, hd₂⟩ := foldlM_addConst_sameDom _ _ (fun c : SCtor => c.name)
    (fun c => ({ uvars := b.uvars, type := (certTr tr rec fams).restore [] b.nparams c.type }
        : VConstant))
    _ _ rfl hd₁ h₂
  obtain ⟨e₃, h₃, -⟩ := Option.bind_eq_some_iff.mp hadd
  obtain ⟨f₃, hf₃, -⟩ := foldlM_addConst_sameDom _ _ (fun r : RecOut => r.name)
    (fun r => ({ uvars := b.recUvars, type := r.type } : VConstant))
    _ _ (nestedRecs_names_certTr tr b nuser rec fams).symm hd₂ h₃
  exact ⟨_, Option.bind_eq_some_iff.mpr ⟨f₁, hf₁, Option.bind_eq_some_iff.mpr ⟨f₂, hf₂,
    Option.bind_eq_some_iff.mpr ⟨f₃, hf₃, rfl⟩⟩⟩⟩

theorem certTr_aux_length (tr : Translated) (rec : List RBlock) (fams : List Fam) :
    (certTr tr rec fams).aux.length = tr.aux.length := by
  simp [certTr]

theorem certTr_aux_name (tr : Translated) (rec : List RBlock) (fams : List Fam) {i : Nat}
    (hi : i < (certTr tr rec fams).aux.length) (hi' : i < tr.aux.length) :
    (certTr tr rec fams).aux[i].name = tr.aux[i].name := by
  simp [certTr]

theorem auxNs_certTr (tr : Translated) (rec : List RBlock) (fams : List Fam) (b : SBlock)
    (nuser : Nat) : auxNs (certTr tr rec fams) b nuser = auxNs tr b nuser :=
  auxNames_certTr tr rec fams b nuser

theorem auxMs_certTr (tr : Translated) (rec : List RBlock) (fams : List Fam) (b : SBlock)
    (nuser : Nat) : auxMs (certTr tr rec fams) b nuser = auxMs tr b nuser := by
  unfold auxMs; rw [auxNs_certTr]

theorem nRecConsts_names_certTr (tr : Translated) (b : SBlock) (nuser : Nat) (rec : List RBlock)
    (fams : List Fam) :
    (nRecConsts (certTr tr rec fams) b nuser).map (·.1) = (nRecConsts tr b nuser).map (·.1) := by
  unfold nRecConsts
  simpa [List.map_map, Function.comp_def] using nestedRecs_names_certTr tr b nuser rec fams

theorem addFold_dom_of_names {e e' e₁ e₂ : VEnv} {cs cs' : List (Name × VConstant)}
    (hb : ∀ x, Dom e x → Dom e' x) (h : addFold e cs = some e₁) (h' : addFold e' cs' = some e₂)
    (hn : cs.map (·.1) = cs'.map (·.1)) (x : Name) (hx : Dom e₁ x) : Dom e₂ x := by
  obtain ⟨ci, hci⟩ := Option.ne_none_iff_exists'.mp hx
  rcases (addFold_spec h).2.2.2.1 x ci hci with ⟨y, hy, hyx, -⟩ | he
  · have hm : x ∈ cs'.map (·.1) := hn ▸ List.mem_map.mpr ⟨y, hy, hyx⟩
    obtain ⟨y', hy', rfl⟩ := List.mem_map.mp hm
    exact addFold_dom h' hy'
  · exact Dom.mono (addFold_spec h').2.2.1 (hb x (by unfold Dom; rw [he]; nofun))

theorem SameHead.instL {a₁ a₂ : Aux} (us : List VLevel) (h : SameHead a₁ a₂) :
    SameHead { a₁ with key := a₁.key.instL us } { a₂ with key := a₂.key.instL us } := by
  obtain ⟨hn, Ic, Ils₁, Ils₂, Ds₁, Ds₂, h₁, h₂⟩ := h
  exact ⟨hn, Ic, Ils₁.map (·.inst us), Ils₂.map (·.inst us), Ds₁.map (·.instL us),
    Ds₂.map (·.instL us), by simp only [headArgs_instL, h₁, VExpr.instL],
    by simp only [headArgs_instL, h₂, VExpr.instL]⟩

theorem auxOfCtor_slot_certTr {M : CInterp V} {env env₁ envT : VEnv} {b : SBlock}
    {rec : List RBlock} {tr : Translated} {nuser : Nat} {fams : List Fam}
    {MJf : RBlock → CInterp V} {envJf envJ₁f : RBlock → VEnv}
    (N : NWF M env env₁ envT b rec (certTr tr rec fams) nuser fams MJf envJf envJ₁f)
    {i : Nat} {a : Aux} (ha : tr.aux[i]? = some a) (hd : nuser + i < b.ntypes)
    {c : SCtor} (hc : c ∈ (b.types[nuser + i]!).ctors) : tr.auxOfCtor? c.name = some a := by
  have hnd : (b.types.flatMap fun t => t.ctors.map (·.name)).Nodup := by
    have := (List.nodup_append.mp N.S.hwf.syn.nodup).2.1
    simpa [SBlock.ctors, List.map_flatMap] using this
  have hlen : tr.aux.length = b.ntypes - nuser := by
    rw [← certTr_aux_length tr rec fams]; exact N.aux_length
  have hp : ∀ j (hj : j < tr.aux.length),
      (tr.types.find? (·.name == tr.aux[j].name)).any (·.ctors.any (·.1 == c.name)) =
        (b.types[nuser + j]'(by have : b.ntypes = b.types.length := rfl; omega)).ctors.any
          (·.name == c.name) := by
    intro j hj
    have hjb : nuser + j < b.types.length := by have : b.ntypes = b.types.length := rfl; omega
    have hjc : j < (certTr tr rec fams).aux.length := by rw [certTr_aux_length]; exact hj
    have hn := N.member_name (List.getElem?_eq_getElem hjc) hjb
    rw [certTr_aux_name tr rec fams hjc hj] at hn
    rw [← hn, ← getElem_eq_getElem! hjb, show tr.types = (certTr tr rec fams).types from rfl,
      N.find_type hjb, Option.any_some, (N.cert_get _ hjb).2]
    simp [List.any_map, Function.comp_def]
  have hi : i < tr.aux.length := (List.getElem?_eq_some_iff.mp ha).1
  have hai : tr.aux[i] = a := (List.getElem?_eq_some_iff.mp ha).2
  have hib : nuser + i < b.types.length := hd
  unfold Translated.auxOfCtor?
  refine List.find?_eq_some_iff_getElem.mpr ⟨?_, i, hi, hai, fun j hj => ?_⟩
  · rw [← hai, hp i hi]
    exact List.any_eq_true.mpr ⟨c, by rw [getElem_eq_getElem! hib]; exact hc, by simp⟩
  · have hjl : j < tr.aux.length := by omega
    have hjb : nuser + j < b.types.length := by have : b.ntypes = b.types.length := rfl; omega
    rw [hp j hjl]
    simp only [Bool.not_eq_true', List.any_eq_false, beq_iff_eq]
    intro c' hc' he
    have := nodup_flatMap_pos hnd hjb hib (x := c.name) (List.mem_map.mpr ⟨c', hc', he⟩)
      (List.mem_map.mpr ⟨c, by rw [getElem_eq_getElem! hib]; exact hc, rfl⟩)
    omega

theorem step_nested_gen {M : CInterp V} {env env' envT : VEnv} {rec : List RBlock}
    {MJf : RBlock → CInterp V} {envJf envJ₁f : RBlock → VEnv} (hM : IsModel M env) (hG : Good env)
    (I : RecInv M env rec MJf envJf envJ₁f) {u : UDecl} {b : SBlock} {tr : Translated}
    {fams : List Fam} (hlen : u.types.length ≤ tr.types.length)
    (hcert : b.Certifies u.uvars u.nparams tr.types) (hwf : b.WF env)
    (hsafe : RestoreSafe tr b u.types.length = true) (hfresh : AuxFresh b u.types.length env)
    (hmem : AuxMembers tr b u.types.length = true) (hRN : RecNames b u.types.length = true)
    (hT : b.add env = some envT)
    (hfams : FamsOK (certTr tr rec fams) b u.types.length rec envT fams)
    (hok : CertsOK tr b u.types.length rec fams envT)
    (hbase : ∀ c ∈ b.ctors.map (·.name), M c = M₂ M b c)
    (hadd : addNested tr b u.types.length env = some env') :
    ∃ (MJf' : RBlock → CInterp V) (envJf' envJ₁f' : RBlock → VEnv),
      IsModel (Mrec M b u.types.length) (addCertified tr b u.types.length rec fams env') ∧
        Good (addCertified tr b u.types.length rec fams env') ∧
        RecInv (Mrec M b u.types.length) (addCertified tr b u.types.length rec fams env')
          (rec ++ [{ b, nuser := u.types.length, tr }]) MJf' envJf' envJ₁f' ∧
        env ≤ addCertified tr b u.types.length rec fams env' ∧
        ∀ c, Dom env c → Mrec M b u.types.length c = M c := by
  obtain ⟨env₁, -, -, hwt, -⟩ := add_spec hT
  have S : Setting M env env₁ b := ⟨hM, hG, hwf, hwt⟩
  have hcert' : b.Certifies b.uvars b.nparams tr.types := by
    have h := hcert; rw [← hcert.1, ← hcert.2.1] at h; exact h
  have N : NWF M env env₁ envT b rec (certTr tr rec fams) u.types.length fams MJf envJf envJ₁f :=
    { S, cert := hcert', hT, famsOK := hfams, base := hbase,
      safe := by rw [restoreSafe_certTr]; exact hsafe,
      fresh := hfresh, members := by rw [auxMembers_certTr]; exact hmem, canon := I.canon }
  have hnl : u.types.length ≤ b.ntypes := by
    have h : u.types.length ≤ (certTr tr rec fams).types.length := hlen
    rw [N.cert_length] at h; exact h
  obtain ⟨envB, hB⟩ := addNested_certTr rec fams hadd
  obtain ⟨e₁, e₂B, e₃B, e₂T, e₃T, h1, h2B, h3B, hBeq, hfin, hrecu, hctu, h2T, h3T, hT'⟩ :=
    addNested_facts N hRN hnl hB
  obtain ⟨e₁', e₂, e₃, h1', h2, h3, rfl⟩ := addNested_spec hadd
  obtain rfl : e₁ = e₁' := Option.some.inj (h1.symm.trans h1')
  have hd₂ : ∀ x, Dom e₂B x → Dom e₂ x :=
    addFold_dom_of_names (fun _ h => h) h2B h2 (by simp [nCtorConsts])
  have hd₃ : ∀ x, Dom e₃B x → Dom e₃ x :=
    addFold_dom_of_names hd₂ h3B h3 (nRecConsts_names_certTr tr b _ rec fams)
  have hle₁₂ := (addFold_spec h2).2.2.1
  have hle₂₃ := (addFold_spec h3).2.2.1
  have hle₃ : e₃ ≤ nIotaFold tr b u.types.length e₃ := le_foldl_addDefEq _ _
  have hagree := fun {ls : List Nat} (hl : ls.length = b.uvars) =>
    N.aux_agree hRN hfin hrecu hctu h1 h2B h2T h3T hT' hok hl
  have hsame : List.Forall₂ SameHead (certTr tr rec fams).aux tr.aux :=
    List.Forall₂.imp (fun _ _ h => AuxAgree.sameHead h)
      (hagree (List.length_replicate (n := b.uvars) (a := 0)))
  have hkeyS : ∀ a ∈ tr.aux, Scoped (Dom e₃) b.nparams a.key := fun a ha => by
    have hks := N.kernel_key_scoped hRN hfin hrecu hctu h1 h2B h2T h3T hT' hok ha
    refine ⟨hks.1, hks.2.mono fun c hc => ?_⟩
    rcases hc with ⟨hc, hna⟩ | hc | ⟨d, hd, rfl⟩ | ⟨p, hp, rfl⟩
    · exact Dom.mono (VEnv.LE.trans hle₁₂ hle₂₃)
        (N.dom₁_e₁ h1 hc (by rw [certTr_aux_names]; exact hna))
    · obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hc
      exact Dom.mono hle₂₃ (addFold_dom h2 (List.mem_map.mpr ⟨c', hc', rfl⟩))
    · have hdb : d < b.ntypes := by omega
      have hdl : d < (nestedRecs tr b u.types.length).length := by
        rw [nestedRecs_length]; exact hdb
      have hname := nestedRecs_name tr b u.types.length hdb
      rw [ite_eq_left hd] at hname
      rw [← hname]
      exact addFold_dom h3 (List.mem_map.mpr ⟨_, List.getElem_mem hdl, rfl⟩)
    · exact hd₃ _ (NWF.fin_dom h3B hp)
  have RC : ∀ {ls : List Nat}, ls.length = b.uvars →
      RestoreHyp (Mrec M b u.types.length) (Mrec M b u.types.length) ls tr []
        (auxNs tr b u.types.length) (auxMs tr b u.types.length) (ownLevels b.uvars) b.nparams
        (fun xs => Ext M ls b.params [] xs) := fun hl => by
    have H := (N.restoreHyp_ctor hRN hfin hrecu hctu hl).rekey (tr₂ := tr) rfl (hagree hl)
    rw [auxNs_certTr, auxMs_certTr] at H
    exact H
  have RR : ∀ ls' : List Nat,
      RestoreHyp (Mrec M b u.types.length) (Mrec M b u.types.length) ls'
        (shiftTr tr b.blockLevels) (auxRecTable b u.types.length) (auxNs tr b u.types.length)
        (auxMs tr b u.types.length) b.blockLevels b.nparams
        (fun xs => Ext M (blev b ls') b.params [] xs) := fun ls' =>
    (RC (blev_length b ls')).shift b.blockLevels rfl (blev_length b ls') (fun p hp => by
      obtain ⟨i, hi, he⟩ := mem_auxRecTable hp
      unfold auxMs; rw [he]
      exact List.mem_append_right _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩))
      (fun _ hp => by have h := N.auxRec_not_ns hRN hp; rw [auxNs_certTr] at h; exact h)
      (fun c _ => NWF.Mrec_rename hRN c)
  have SC : ScopeHyp tr [] (auxNs tr b u.types.length) (auxMs tr b u.types.length) b.nparams
      (Dom env₁) (Dom e₃) := by
    have H := ((N.scopeHyp_ctor h1 h2B).mono_target fun x hx => Dom.mono hle₂₃ (hd₂ x hx)).rekey
      (tr₂ := tr) rfl hsame hkeyS
    rw [auxNs_certTr, auxMs_certTr] at H
    exact H
  have SR : ScopeHyp (shiftTr tr b.blockLevels) (auxRecTable b u.types.length)
      (auxNs tr b u.types.length) (auxMs tr b u.types.length) b.nparams
      (Dom (iotaFold b e₃T)) (Dom e₃) := by
    have hsameS : List.Forall₂ SameHead (shiftTr (certTr tr rec fams) b.blockLevels).aux
        (shiftTr tr b.blockLevels).aux :=
      forall₂_map (fun _ _ h => SameHead.instL b.blockLevels h) hsame
    have H := ((N.scopeHyp_rec hRN h1 h2B h3B h2T h3T).mono_target fun x hx => hd₃ x hx).rekey
      (tr₂ := shiftTr tr b.blockLevels) rfl hsameS (fun a' ha' => by
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ha'
        have h := hkeyS a ha
        exact ⟨h.1.instL, constsIn_instL.mpr h.2⟩)
    rw [auxNs_certTr, auxMs_certTr] at H
    exact H
  obtain ⟨hM', hG'⟩ := N.model_addNested hRN hfin hrecu hctu h1 h2 h3 h2T h3T hT' RC RR SC SR hsafe
  have hle₁' : e₁ ≤ nIotaFold tr b u.types.length e₃ := VEnv.LE.trans
      (VEnv.LE.trans hle₁₂ hle₂₃) hle₃
  have hle₂' : e₂ ≤ nIotaFold tr b u.types.length e₃ := VEnv.LE.trans hle₂₃ hle₃
  have hle := VEnv.LE.trans (addFold_spec h1).2.2.1 hle₁'
  have hMd := fun {x} (hx : Dom env₁ x) => N.Mrec_dom₁ hRN hfin hrecu hctu hx
  have hag : ∀ c, Dom env c → Mrec M b u.types.length c = M c := fun c hc =>
    (hMd (Dom.mono S.le₁ hc)).trans (S.agree hc)
  have htake : ∀ d < u.types.length, b.types[d]! ∈ b.types.take u.types.length := fun d hd => by
    rw [getElem!_types (show d < b.ntypes by omega)]
    have hdl : d < b.types.length := show d < b.ntypes by omega
    exact List.mem_iff_getElem.mpr ⟨d, by
        simp only [List.length_take]; omega, by rw [List.getElem_take]; rfl⟩
  have hctor_user : ∀ d < u.types.length, ∀ q (c : SCtor), (ctorsOf b d)[q]? = some c →
      c ∈ (b.types.take u.types.length).flatMap (·.ctors) := fun d hd q c hcq =>
    List.mem_flatMap.mpr ⟨b.types[d]!, htake d hd, List.mem_of_getElem? hcq⟩
  have hctv : ∀ d < b.ntypes, ∀ q (c : SCtor), (ctorsOf b d)[q]? = some c →
      Mrec M b u.types.length c.name = fun ls => Setting.ctorVal b (Setting.Mc M b) ls q c :=
    fun d hd q c hcq => by
      have hdT : Dom (iotaFold b e₃T) c.name :=
        Dom.mono (VEnv.LE.trans (addFold_spec h3T).2.2.1 (le_iotaFold b e₃T))
          (BlockModel.Setting.ctor_dom h2T (mem_ctors_name hcq))
      exact (N.hagT hRN hfin h2T h3T hdT).trans (BlockModel.Setting.hctor₃ h2T h3T d hd q c hcq)
  have hct : ∀ d < u.types.length, ∀ q (c : SCtor), (ctorsOf b d)[q]? = some c →
      Dom (nIotaFold tr b u.types.length e₃) c.name ∧
        Mrec M b u.types.length c.name = fun ls => Setting.ctorVal b (Setting.Mc M b) ls q c :=
    fun d hd q c hcq => ⟨Dom.mono hle₂' (addFold_dom h2 (List.mem_map.mpr
        ⟨c, hctor_user d hd q c hcq, rfl⟩)),
      hctv d (by omega) q c hcq⟩
  have hdomU : ∀ d < u.types.length, Dom (nIotaFold tr b u.types.length e₃) (b.types[d]!).name :=
    fun d hd => Dom.mono hle₁' (addFold_dom h1 (List.mem_map.mpr ⟨_, htake d hd, rfl⟩))
  have haux : ∀ σ < b.ntypes, ¬ σ < u.types.length → ∃ a, tr.aux[σ - u.types.length]? = some a ∧
      (b.types[σ]!).name = a.name := fun σ hσ hu => by
    have hl := N.aux_length
    have hlc := certTr_aux_length tr rec fams
    have hi : σ - u.types.length < tr.aux.length := by omega
    have hic : σ - u.types.length < (certTr tr rec fams).aux.length := by omega
    have hn := N.member_name (List.getElem?_eq_getElem hic)
      (by omega : u.types.length + (σ - u.types.length) < b.ntypes)
    rw [Nat.add_sub_cancel' (by omega), certTr_aux_name tr rec fams hic hi] at hn
    exact ⟨_, List.getElem?_eq_getElem hi, hn⟩
  have hkey : ∀ σ, ¬ σ < u.types.length → ∀ a, tr.aux[σ - u.types.length]? = some a →
      ({ b, nuser := u.types.length, tr } : RBlock).slotKey σ = some a.key := fun σ hu a ha => by
    unfold RBlock.slotKey; simp only [ite_eq_right hu, ha, Option.map_some]
  have C : CanonR (Mrec M b u.types.length) (nIotaFold tr b u.types.length e₃)
      { b, nuser := u.types.length, tr } M env env₁ :=
    { setting := S, le := hle, agree := hag,
      slots := fun σ hσ => by
        by_cases hu : σ < u.types.length
        · exact userSlot (r := { b, nuser := u.types.length, tr }) hu hnl (hdomU σ hu)
            (hMd (S.type_dom hσ))
        obtain ⟨a, ha, hn⟩ := haux σ hσ hu
        have haM : a ∈ tr.aux := List.mem_of_getElem? ha
        have hks := hkeyS a haM
        obtain ⟨Ic, Ils, Ds, hh⟩ :=
          (RC (List.length_replicate (n := b.uvars) (a := 0))).key_head a haM
        have hk' := appN_headArgs a.key
        rw [hh] at hk'
        refine ⟨a.key, hkey σ hu a ha, hks.1, hks.2.mono fun c hc => Dom.mono hle₃ hc,
          ⟨_, _, _, hk'.symm⟩, fun ls ρ hl hρ => ?_⟩
        have H := RC hl
        rw [← H.aux a haM ρ (by rw [Ext.length_eq _ _ hρ]; rfl) hρ, ownLevels_eval hl]
        show ρ.foldl app (Mrec M b u.types.length a.name ls) = _
        rw [← hn]
        exact congrArg (fun F => ρ.foldl app (F ls)) (hMd (S.type_dom hσ)),
      slotCtors := fun σ hσ q c hc => by
        have hσb : σ < b.ntypes := hσ
        by_cases hu : σ < u.types.length
        · exact userSlotCtor (r := { b, nuser := u.types.length, tr }) hu hnl (hct σ hu q c hc)
        intro k hk Ic Ils Ds hh
        obtain ⟨a, ha, hn⟩ := haux σ hσ hu
        rw [hkey σ hu a ha, Option.some.injEq] at hk
        subst hk
        have hca : tr.auxOfCtor? c.name = some a := auxOfCtor_slot_certTr N ha (by omega) (by
          rw [Nat.add_sub_cancel' (by omega)]; exact List.mem_of_getElem? hc)
        show Dom _ (c.name.replacePrefix (b.types[σ]!).name Ic) ∧ _
        rw [hn]
        refine ⟨Dom.mono hle₃ (SC.ctor c.name a hca Ic Ils Ds hh), fun ls ρ hl hρ => ?_⟩
        have H := RC hl
        rw [← H.ctor c.name a hca Ic Ils Ds hh ρ (by rw [Ext.length_eq _ _ hρ]; rfl) hρ,
          ownLevels_eval hl, hctv σ hσ q c hc]
      recs := fun h hd => absurd (N.cert_length.symm.trans (congrArg List.length
          h)) (Nat.pos_iff_ne_zero.mp hd) }
  obtain ⟨hMB, hGB⟩ := exists_model_addNested N hRN hnl hB
  have hCB : ∀ x ∈ nCtorConsts (certTr tr rec fams) b u.types.length ++
      nRecConsts (certTr tr rec fams) b u.types.length, envB.constants x.1 = some x.2 := by
    intro x hx
    rw [hBeq, nIotaFold, constants_foldl_addDefEq]
    rcases List.mem_append.mp hx with hx | hx
    · exact (addFold_spec h3B).2.2.1.1 (addFold_get h2B hx)
    · exact addFold_get h3B hx
  have hdB : ∀ y, Dom envB y → Dom (nIotaFold tr b u.types.length e₃) y := fun y hy => by
    have h3 : Dom e₃B y := by
      unfold Dom at hy ⊢; rwa [hBeq, nIotaFold, constants_foldl_addDefEq] at hy
    have h := hd₃ y h3
    unfold Dom at h ⊢; rwa [nIotaFold, constants_foldl_addDefEq]
  obtain ⟨hM'', hG''⟩ := foldl_addDefEq (dfs := certTypings tr b u.types.length rec fams) hM' hG'
    fun df hdf => by
      unfold certTypings at hdf
      split at hdf
      · cases hdf
      rcases List.mem_append.mp hdf with hdf | hdf
      rotate_left
      · have hdfB : envB.defeqs df := by
          rw [hBeq, nIotaFold]; exact defeqs_foldl _ _ _ (.inr hdf)
        obtain ⟨⟨hl, ht⟩, hr, -⟩ := hGB.1.2 hdfB
        obtain ⟨⟨cl, ct⟩, cr, -⟩ := hGB.2.2 hdfB
        exact ⟨hMB.defeq hdfB, ⟨hl, cl.mono hdB⟩, ⟨hr, cr.mono hdB⟩, ⟨ht, ct.mono hdB⟩⟩
      obtain ⟨x, hx, rfl⟩ : ∃ x ∈ nCtorConsts (certTr tr rec fams) b u.types.length ++
          nRecConsts (certTr tr rec fams) b u.types.length,
          df = { uvars := x.2.uvars, lhs := .const x.1 (ownLevels x.2.uvars),
                 rhs := .const x.1 (ownLevels x.2.uvars), type := x.2.type } := by
        simp only [List.mem_append, List.mem_map] at hdf
        rcases hdf with ⟨c, hc, rfl⟩ | ⟨r, hr, rfl⟩
        · exact ⟨_, List.mem_append_left _ (List.mem_map.mpr ⟨c, hc, rfl⟩), rfl⟩
        · exact ⟨_, List.mem_append_right _ (List.mem_map.mpr ⟨r, hr, rfl⟩), rfl⟩
      have hci := hCB x hx
      obtain ⟨_, hcl, -⟩ := hGB.1.1 hci
      obtain ⟨_, hcs, -⟩ := hGB.2.1 hci
      have hdom : Dom envB x.1 := by simp [Dom, hci]
      refine ⟨fun ls hl ρ => ⟨rfl, ?_⟩, ⟨trivial, hdB _ hdom⟩, ⟨trivial, hdB _ hdom⟩,
        ⟨hcl, hcs.mono hdB⟩⟩
      have h := hMB.const hci ls hl ρ
      simp only [interp]
      rwa [show (ownLevels x.2.uvars).map (VLevel.eval ls) = ls from map_eval_params hl]
  exact ⟨_, _, _, hM'', hG'', (I.push hle hag C).mono (le_foldl_addDefEq _ _) fun _ _ => rfl,
    VEnv.LE.trans hle (le_foldl_addDefEq _ _), hag⟩

theorem step_nested {M : CInterp V} {env env' : VEnv} {rec : List RBlock}
    {MJf : RBlock → CInterp V} {envJf envJ₁f : RBlock → VEnv} (hM : IsModel M env) (hG : Good env)
    (I : RecInv M env rec MJf envJf envJ₁f) {u : UDecl} {b : SBlock} {tr : Translated}
    {fams : List Fam} (helim : elim (indOf rec) (fun c => (env.constants c).isSome) u = .ok tr)
    (hnwf : NestedWF tr b u.types.length rec env u fams)
    (hadd : addNested tr b u.types.length env = some env') :
    ∃ (M' : CInterp V) (MJf' : RBlock → CInterp V) (envJf' envJ₁f' : RBlock → VEnv),
      IsModel M' (addCertified tr b u.types.length rec fams env') ∧
          Good (addCertified tr b u.types.length rec fams env') ∧
        RecInv M' (addCertified tr b u.types.length rec fams env')
            (rec ++ [{ b, nuser := u.types.length, tr }])
          MJf' envJf' envJ₁f' ∧
        env ≤ addCertified tr b u.types.length rec fams env' ∧ ∀ c, Dom env c → M' c = M c := by
  obtain ⟨hcert, hwf, hsafe, hfresh, hmem, hRN, envT, hT, hfams, hcok⟩ := hnwf
  obtain ⟨e₁, e₂, -, h1, h2, -⟩ := add_spec hT
  have S₀ : Setting M env e₁ b := ⟨hM, hG, hwf, h1⟩
  have hag₀ : ∀ c, Dom env c → M c = M₂ M b c := fun c hc => by
    rw [M₂_other fun h => BlockModel.Setting.ctor_fresh h2 h (Dom.mono S₀.le₁ hc)]
    exact (S₀.agree hc).symm
  obtain ⟨MJf', envJf', envJ₁f', h⟩ := step_nested_gen (IsModel.congr hM hG fun c h =>
      (hag₀ c h).symm)
    hG (I.mono VEnv.LE.rfl fun c h => (hag₀ c h).symm) (elim_length _ _ helim) hcert hwf
        hsafe hfresh
    hmem hRN hT hfams hcok (fun c hc => S₀.M₂_base hag₀ (Or.inl hc)) hadd
  obtain ⟨hM', hG', I', hle, hag⟩ := h
  exact ⟨_, MJf', envJf', envJ₁f', hM', hG', I', hle, fun c hc => (hag c hc).trans (hag₀ c hc).symm⟩

/-- An admitted environment over a good modelled base has a model extending the base's. -/
theorem Admits.model {base env : VEnv} {rec : List RBlock} {M : CInterp V} (hM : IsModel M base)
    (hb : Good base) (H : Admits base env rec) :
    ∃ (M' : CInterp V) (MJf : RBlock → CInterp V) (envJf envJ₁f : RBlock → VEnv),
      IsModel M' env ∧ Good env ∧ RecInv M' env rec MJf envJf envJ₁f ∧
        base ≤ env ∧ ∀ c, Dom base c → M' c = M c := by
  induction H with
  | base => exact ⟨M, fun _ => M, fun _ => base, fun _ => base, hM, hb, RecInv.empty _ _ _ _ _,
      VEnv.LE.rfl, fun _ _ => rfl⟩
  | «opaque» _ hci hadd ih =>
    obtain ⟨M', MJf, envJf, envJ₁f, hM, hG, I, hle, hfr₀⟩ := ih
    have hfr := addConst_fresh hadd
    refine ⟨_, MJf, envJf, envJ₁f, (hM.addConst hG hci hadd).1, hG.addConst hci hadd,
      I.mono (VEnv.addConst_le hadd) fun c hc => ?_, VEnv.LE.trans hle (VEnv.addConst_le hadd),
      fun c hc => ?_⟩
    · simp only [ite_eq_right (fun h : c = _ => hc (h ▸ hfr))]
    · funext ls
      simp only [ite_eq_right (fun h : c = _ => Dom.mono hle hc (h ▸ hfr))]
      exact congrFun (hfr₀ c hc) ls
  | @«def» env env' _ ci _ hci hadd ih =>
    obtain ⟨M', MJf, envJf, envJ₁f, hM, hG, I, hle, hfr₀⟩ := ih
    have hfr := addConst_fresh hadd
    obtain ⟨hM', -, hdf⟩ := hM.addConst hG hci hadd
    have hle' : env ≤ env'.addDefEq ci.toDefEq :=
      VEnv.LE.trans (VEnv.addConst_le hadd) ⟨fun h => h, fun h => Or.inr h⟩
    refine ⟨_, MJf, envJf, envJ₁f, ⟨fun h => hM'.const h, fun {df} h ls hl ρ => ?_⟩,
      hG.addDef hci hadd, I.mono hle' fun c hc => ?_, VEnv.LE.trans hle hle', fun c hc => ?_⟩
    · rcases h with rfl | h
      · exact hdf ls hl ρ
      · exact hM'.defeq h ls hl ρ
    · simp only [ite_eq_right (fun h : c = _ => hc (h ▸ hfr))]
    · funext ls
      simp only [ite_eq_right (fun h : c = _ => Dom.mono hle hc (h ▸ hfr))]
      exact congrFun (hfr₀ c hc) ls
  | plain _ hwf hadd ih =>
    obtain ⟨M', MJf, envJf, envJ₁f, hM, hG, I, hle, hfr₀⟩ := ih
    obtain ⟨M'', MJf', envJf', envJ₁f', hM'', hG'', I'', hle', hag⟩ := step_plain hM hG I hwf hadd
    exact ⟨M'', MJf', envJf', envJ₁f', hM'', hG'', I'', VEnv.LE.trans hle hle',
      fun c hc => (hag c (Dom.mono hle hc)).trans (hfr₀ c hc)⟩
  | @etaProj env rec b c nm H hb hη hlen hk hδ ih =>
    obtain ⟨M', MJf, envJf, envJ₁f, hM, hG, I, hle, hfr₀⟩ := ih
    have hC := I.canon _ hb
    obtain ⟨t, ht, -, -, hc, -, -⟩ := etaCtor_spec hη
    have hle₁ := setting_le H hb hC.le hC.setting.hwt
    have R : ProjRec _ _ t _ _ := ⟨ht, hc, hlen, hk, hδ⟩
    obtain ⟨hlS, hrS, htS⟩ := etaRuleP_scoped hC hle₁ R
    have hle' : env ≤ env.addDefEq (b.etaRuleP (nm.getD · .anonymous) c) :=
        ⟨fun h => h, fun h => Or.inr h⟩
    exact ⟨M', MJf, envJf, envJ₁f, hM.addDefEq fun ls hl ρ => etaRuleP_law hM hC hle₁ R hη hl ρ,
      Good.addDefEq hG hlS hrS htS, I.mono hle' fun _ _ => rfl, VEnv.LE.trans hle hle', hfr₀⟩
  | nested _ helim hnwf hadd ih =>
    obtain ⟨M', MJf, envJf, envJ₁f, hM, hG, I, hle, hfr₀⟩ := ih
    obtain ⟨M'', MJf', envJf', envJ₁f', hM'', hG'', I'', hle', hag⟩ :=
        step_nested hM hG I helim hnwf hadd
    exact ⟨M'', MJf', envJf', envJ₁f', hM'', hG'', I'', VEnv.LE.trans hle hle',
      fun c hc => (hag c (Dom.mono hle hc)).trans (hfr₀ c hc)⟩

/-- **Consistency** of every admitted extension of a modelled base environment. -/
theorem consistency_admits {base env : VEnv} {rec : List RBlock} {M : CInterp V}
    (hM : IsModel M base) (hb : Good base) (H : Admits base env rec) (U : Nat) :
    ¬ ∃ e, env.HasType U [] e VExpr.false :=
  let ⟨_, _, _, _, hM', _⟩ := Admits.model hM hb H
  no_false_of_model hM'

/-- No environment admitted over `Core.coreEnv` has a closed proof of `∀ p : Prop, p`. -/
theorem Core.consistency_nested (V : Type u) [SetTheory V] {env : VEnv} {rec : List RBlock}
    (H : Admits Core.coreEnv env rec) (U : Nat) : ¬ ∃ e, env.HasType U [] e VExpr.false :=
  consistency_admits (Core.coreM_model (V := V)) Core.coreEnv_good H U

end Soulgem.Nested
