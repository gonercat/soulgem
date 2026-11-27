import Soulgem.Model.NestedAssemble
import Soulgem.Model.Rekey
import Soulgem.Spec.Cert

/-! # The certificate checking environment is sound in `Mrec` -/

namespace Soulgem.Nested
open ConLeche ConLeche.SetTheory ConLeche.SetTheory.Tower Lean4Lean Spec BlockSem BlockModel

universe u
variable {V : Type u} [SetTheory V]

theorem certTr_aux_names (tr : Translated) (rec : List RBlock) (fams : List Fam) :
    (certTr tr rec fams).aux.map (·.name) = tr.aux.map (·.name) := by
  unfold certTr
  exact List.ext_getElem (by simp) fun i _ _ => by simp

theorem auxNames_certTr (tr : Translated) (rec : List RBlock) (fams : List Fam) (b : SBlock)
    (nuser : Nat) : auxNames (certTr tr rec fams) b nuser = auxNames tr b nuser := by
  simp only [auxNames, certTr_aux_names]

theorem ScopeHyp.mono_source {tr : Translated} {auxRec : List (Name × Name)} {ns ms : List Name}
    {n : Nat} {P P₂ P' : Name → Prop} (H : ScopeHyp tr auxRec ns ms n P P')
    (h : ∀ c, P₂ c → P c ∨ c ∈ ns) : ScopeHyp tr auxRec ns ms n P₂ P' where
  ns_iff := H.ns_iff
  ms_ns := H.ms_ns
  ms_rec := H.ms_rec
  rec_ns := H.rec_ns
  key := H.key
  key_head := H.key_head
  ctor := H.ctor
  fin := H.fin
  other := fun c hc hn hr => H.other c ((h c hc).resolve_right hn) hn hr

theorem IsModel.addConst_same {M : CInterp V} {env env' : VEnv} {n : Name} {ci : VConstant}
    (hM : IsModel M env) (hadd : env.addConst n ci = some env')
    (hnew : ∀ ls : List Nat, ls.length = ci.uvars → ∀ ρ, M n ls ∈ˢ interp M ls ci.type ρ) :
    IsModel M env' :=
  IsModel.addFold_same (cs := [(n, ci)]) hM (by simpa [addFold] using hadd)
    fun x hx => by simp only [List.mem_singleton] at hx; subst hx; exact hnew

theorem mentions_eq_false_of_constsIn {P : Name → Prop} {ns : List Name}
    (h : ∀ c ∈ ns, ¬ P c) : ∀ {e : VExpr}, ConstsIn P e → mentions ns e = false
  | .bvar _, _ | .sort _, _ => rfl
  | .const c _, hc => by simpa [mentions] using fun hm => h c hm hc
  | .app _ _, hc | .lam _ _, hc | .forallE _ _, hc => by
    simp only [mentions, mentions_eq_false_of_constsIn h hc.1,
      mentions_eq_false_of_constsIn h hc.2, Bool.or_false]

theorem restoreSafe_appN_const {ns ms : List Name} {us : List VLevel} {n d : Nat} {x : Name}
    (hx : ns.contains x = true) {as : List VExpr} (hlen : n ≤ as.length)
    (htake : as.take n = vars d 0 n) (hdrop : (as.drop n).all (!mentions ms ·) = true) :
    restoreSafe ns ms us n (appN (.const x us) as) d = true := by
  rcases List.eq_nil_or_concat as with rfl | ⟨l, a, rfl⟩
  · have : n = 0 := by simpa using hlen
    subst this; simp [appN, restoreSafe]
  · have hh : headArgs (.app (appN (.const x us) l) a) = (.const x us, l ++ [a]) := by
      rw [← headArgs_appN_const x us (l ++ [a])]; simp [appN, List.foldl_append]
    have he : appN (.const x us) (l ++ [a]) = .app (appN (.const x us) l) a := by
      simp [appN, List.foldl_append]
    rw [List.concat_eq_append, he, restoreSafe, hh]
    simp only [List.concat_eq_append] at hlen htake hdrop
    simp only [hx, ite_true, htake, hdrop, decide_true, hlen, Bool.and_self]

theorem restoreSafeTop_go_lamTel {ns ms : List Name} {us : List VLevel} {n : Nat} :
    ∀ (As : List VExpr) (R : VExpr) (d : Nat), (∀ A ∈ As, mentions ms A = false) →
      restoreSafe ns ms us n R (d + As.length) = true →
      restoreSafeTop.go ns ms us n As.length (Spec.lamTel As R) d = true
  | [], R, d, _, h => by simpa [restoreSafeTop.go, Spec.lamTel] using h
  | A :: As, R, d, hA, h => by
    simp only [List.length_cons, Spec.lamTel, restoreSafeTop.go, hA A (.head _),
      Bool.not_false, Bool.true_and]
    exact restoreSafeTop_go_lamTel As R (d + 1) (fun B hB => hA B (.tail _ hB))
      (by simpa [Nat.add_assoc, Nat.add_comm 1] using h)

theorem forall₂_mapIdx {α β : Type} {R : β → α → Prop} :
    ∀ {l : List α} {f : Nat → α → β}, (∀ i (h : i < l.length), R (f i l[i]) l[i]) →
      List.Forall₂ R (l.mapIdx f) l
  | [], _, _ => by simp
  | a :: l, f, h => by
    rw [List.mapIdx_cons]
    exact .cons (h 0 (by simp)) (forall₂_mapIdx fun i hi => h (i + 1) (by simp; omega))

theorem certKey_some {rec : List RBlock} {fams : List Fam} {g : Nat} {K : VExpr}
    (hK : certKey rec fams g = some K) :
    ∃ j, ∃ hj : j < fams.length, ∃ Ks σ, ∃ _ : σ < fams[j].φ.length, ∃ r key,
      fams[j].kernelDs = some Ks ∧ fams[j].φ[σ] = g ∧ rec[fams[j].ri]? = some r ∧
      r.slotKey σ = some key ∧ K = atKey fams[j].lv fams[j].Ds 0 key := by
  obtain ⟨F, hFmem, hFK⟩ := List.exists_of_findSome?_eq_some hK
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hFmem
  obtain ⟨Ks, hKs⟩ : ∃ Ks, fams[j].kernelDs = some Ks := by
    cases h : fams[j].kernelDs with
    | none => simp [h] at hFK
    | some Ks => exact ⟨Ks, rfl⟩
  simp only [hKs, Option.isNone_some, Bool.false_eq_true, ↓reduceIte] at hFK
  obtain ⟨σ, hσ, hFK⟩ := Option.bind_eq_some_iff.mp hFK
  obtain ⟨r, hr, hFK⟩ := Option.bind_eq_some_iff.mp hFK
  obtain ⟨key, hkey, hFK⟩ := Option.bind_eq_some_iff.mp hFK
  obtain ⟨hσl, hσg, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hσ
  exact ⟨j, hj, Ks, σ, hσl, r, key, hKs, by simpa using hσg, hr, hkey, (Option.some.inj hFK).symm⟩

theorem certEnv_dom {tr : Translated} {b : SBlock} {nuser : Nat} {rec : List RBlock}
    {fams : List Fam} {envT E : VEnv} (hE : certEnv tr b nuser rec fams envT = some E) {c : Name}
    (hc : Dom E c) : Dom envT c ∨ ∃ p ∈ auxRecTable b nuser, p.2 = c := by
  unfold certEnv at hE
  obtain ⟨e, he₁, he₂⟩ := Option.bind_eq_some_iff.mp hE
  have hB : ∀ (xs : List Name) (e₀ e : VEnv),
      xs.foldlM (fun e x => do
        let ci ← envT.constants x
        pure (e.addDefEq { uvars := b.uvars, lhs := etaParams b x,
                           rhs := (certTr tr rec fams).restore [] b.nparams (etaParams b x),
                           type := ci.type })) e₀ = some e → e.constants = e₀.constants := by
    intro xs
    induction xs with
    | nil => intro e₀ e he; cases he; rfl
    | cons x xs ih =>
      intro e₀ e he
      simp only [List.foldlM_cons] at he
      obtain ⟨e', h', he'⟩ := Option.bind_eq_some_iff.mp he
      obtain ⟨ci, -, h'⟩ := Option.bind_eq_some_iff.mp h'
      cases h'
      have h := ih _ _ he'
      exact h
  have hA : ∀ (ps : List (Name × Name)) (e₀ e : VEnv),
      ps.foldlM (fun e p => do
        let ci ← envT.constants p.1
        let e ← e.addConst p.2 ci
        let lv := ownLevels ci.uvars
        pure (e.addDefEq { uvars := ci.uvars, lhs := .const p.2 lv, rhs := .const p.1 lv,
                           type := ci.type })) e₀ = some e →
      ∀ c, Dom e c → Dom e₀ c ∨ ∃ p ∈ ps, p.2 = c := by
    intro ps
    induction ps with
    | nil => intro e₀ e he c hc; cases he; exact .inl hc
    | cons p ps ih =>
      intro e₀ e he c hc
      simp only [List.foldlM_cons] at he
      obtain ⟨e', h', he'⟩ := Option.bind_eq_some_iff.mp he
      obtain ⟨ci, -, h'⟩ := Option.bind_eq_some_iff.mp h'
      obtain ⟨e₁, he₁, h'⟩ := Option.bind_eq_some_iff.mp h'
      cases h'
      rcases ih _ _ he' c hc with hc | ⟨q, hq, rfl⟩
      · have hc1 : e₁.constants c ≠ none := hc
        rw [addConst_constants he₁] at hc1
        by_cases hpc : p.2 = c
        · exact .inr ⟨p, List.mem_cons_self .., hpc⟩
        · simp only [hpc, ↓reduceIte] at hc1; exact .inl hc1
      · exact .inr ⟨q, List.mem_cons_of_mem _ hq, rfl⟩
  have hc' : Dom e c := by
    have h : E.constants c ≠ none := hc
    rw [hB _ e E he₂] at h; exact h
  exact hA _ envT e he₁ c hc'

namespace NWF
theorem interp_etaParams {M' : CInterp V} {b : SBlock} {x : Name} {ls : List Nat}
    (hl : ls.length = b.uvars) {B : List V → V} {ρ : List V}
    (hf : M' x ls ∈ˢ piTel M' ls b.params B ρ) :
    interp M' ls (etaParams b x) ρ = M' x ls := by
  unfold etaParams
  rw [interp_lamTel']
  refine lamTel_eta hf fun xs hxs => ?_
  have hlen : xs.length = b.nparams := hxs.length_eq
  have hc : (appN (.const x (ownLevels b.uvars)) (vars b.nparams 0 b.nparams)).ClosedN b.nparams :=
    closedN_appN_of trivial fun a ha => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
      simp only [List.mem_range] at hi
      simp only [var, VExpr.ClosedN]; omega
  have hcl := interp_liftN M' ls ρ.length (appN (.const x (ownLevels b.uvars))
      (vars b.nparams 0 b.nparams)) b.nparams xs.reverse ρ [] (by simp [hlen]) rfl
  rw [hc.liftN_eq (Nat.le_refl _), List.append_nil, List.append_nil] at hcl
  rw [hcl, interp_appN,
    interp_vars M' ls hlen (by omega)]
  simp only [interp, List.drop_zero, List.take_of_length_le (Nat.le_of_eq hlen)]
  rw [show (ownLevels b.uvars).map (VLevel.eval ls) = ls from map_eval_params hl]

variable {M : CInterp V} {env env₁ envT : VEnv} {b : SBlock} {rec : List RBlock} {tr : Translated}
  {nuser : Nat} {fams : List Fam} {MJf : RBlock → CInterp V} {envJf envJ₁f : RBlock → VEnv}
  (N : NWF M env env₁ envT b rec (certTr tr rec fams) nuser fams MJf envJf envJ₁f)
  (hRN : RecNames b nuser = true)
  (hfin : ∀ x ∈ (auxRecTable b nuser).map (·.2), env.constants x = none)
  (hrecu : ∀ d < nuser, env.constants (b.recName d) = none)
  (hctu : ∀ c ∈ (b.types.take nuser).flatMap (·.ctors), env.constants c.name = none)
  {e₁ e₂ : VEnv}
  (h1 : addFold env (nTypeConsts b nuser) = some e₁)
  (h2 : addFold e₁ (nCtorConsts (certTr tr rec fams) b nuser) = some e₂)
  {e₂T e₃T : VEnv} (h2T : addFold env₁ (ctorConsts b) = some e₂T)
  (h3T : addFold e₂T (recConsts b) = some e₃T) (hT : b.add env = some (iotaFold b e₃T))
include N

include hT in
theorem envT_eq : envT = iotaFold b e₃T := Option.some.inj (N.hT.symm.trans hT)

include hRN hfin h2T h3T hT in
theorem hagT' {x : Name} (hx : Dom envT x) : Mrec M b nuser x = M₃ M b x :=
  N.hagT hRN hfin h2T h3T (N.envT_eq hT ▸ hx)

include hRN hfin h2T h3T hT in
theorem model_envT_rec : IsModel (Mrec M b nuser) envT :=
  IsModel.congr N.modelT.1 N.modelT.2 fun _ hc => N.hagT' hRN hfin h2T h3T hT hc

theorem names_not_dom {c : Name} (hc : c ∈ b.names) : ¬ Dom env c := by
  have h := N.S.hwt; rw [withTypes_eq] at h
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hc
  exact fun hd => hd ((addFold_spec h).1 _ (List.mem_map.mpr ⟨t, ht, rfl⟩))

theorem auxMs_not_dom {c : Name} (hc : c ∈ auxMs (certTr tr rec fams) b nuser) : ¬ Dom env c := by
  intro hd
  rcases List.mem_append.mp hc with hc | hc
  · rcases List.mem_append.mp hc with hc | hc
    · rw [← N.drop_names] at hc
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hc
      exact N.names_not_dom (List.mem_map.mpr ⟨t, List.mem_of_mem_drop ht, rfl⟩) hd
    · obtain ⟨t, ht, hct⟩ := List.mem_flatMap.mp hc
      obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hct
      have := List.all_eq_true.mp (List.all_eq_true.mp N.fresh.1 t ht) c' hc'
      exact hd (Option.isNone_iff_eq_none.mp this)
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc
    have := List.all_eq_true.mp N.fresh.2 i hi
    exact hd (Option.isNone_iff_eq_none.mp this)

theorem params_aux_free : ∀ A ∈ b.params, mentions (auxMs (certTr tr rec fams) b nuser) A = false :=
  fun A hA => mentions_eq_false_of_constsIn (fun _ hc hd => N.auxMs_not_dom hc hd)
    (N.S.params_consts' A hA)

theorem etaParams_scoped {x : Name} (hx : x ∈ auxNames tr b nuser) :
    Scoped (fun c => Dom env₁ c ∨ c ∈ auxNs (certTr tr rec fams) b nuser) 0 (etaParams b x) := by
  have hx' : x ∈ auxNs (certTr tr rec fams) b nuser := by
    simpa [auxNs, auxNames_certTr] using hx
  refine Scoped.lamTel (fun i hi => ?_) ?_
  · have := N.S.params_scoped (P := fun c => Dom env₁ c ∨ c ∈ auxNs (certTr tr rec fams) b nuser)
      (fun _ h => .inl h) (i := i) hi
    rw [Nat.zero_add]; rwa [← getElem_eq_getElem! hi] at this
  · rw [Nat.zero_add]
    exact scoped_appN_iff.mpr ⟨⟨trivial, .inr hx'⟩, Scoped.vars (by omega)⟩

include hT h2T h3T in
theorem dom_envT_block {c : Name} (hc : c ∈ b.names ∨ c ∈ b.ctors.map (·.name)) : Dom envT c := by
  rw [N.envT_eq hT]
  rcases hc with hc | hc
  · have h := N.S.hwt; rw [withTypes_eq] at h
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hc
    obtain ⟨ci, hci⟩ := (addFold_spec h).2.2.2.2.2 _ (List.mem_map.mpr ⟨t, ht, rfl⟩)
    exact domT h2T h3T (by unfold Dom; rw [hci]; nofun)
  · obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hc
    have hcT := constT h3T (addFold_get h2T (List.mem_map.mpr ⟨c', hc', rfl⟩))
    unfold Dom; rw [hcT]; nofun

include hT h2T h3T in
theorem dom_envT_aux {c : Name} (hc : c ∈ auxNames tr b nuser) : Dom envT c := by
  refine N.dom_envT_block h2T h3T hT ?_
  rcases List.mem_append.mp hc with hc | hc
  · rw [← certTr_aux_names tr rec fams, ← N.drop_names] at hc
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hc
    exact .inl (List.mem_map.mpr ⟨t, List.mem_of_mem_drop ht, rfl⟩)
  · obtain ⟨t, ht, hct⟩ := List.mem_flatMap.mp hc
    obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hct
    exact .inr (List.mem_map.mpr ⟨c', List.mem_flatMap.mpr ⟨t, List.mem_of_mem_drop ht, hc'⟩, rfl⟩)

include h1 h2 hT h2T h3T in
theorem dom_e₂ {c : Name} (hc : Dom e₂ c) : Dom envT c := by
  obtain ⟨ci, hci⟩ := Option.ne_none_iff_exists'.mp hc
  rcases (addFold_spec h2).2.2.2.1 c ci hci with ⟨x, hx, rfl, -⟩ | h
  · obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hx
    obtain ⟨-, -, -, -, hcb⟩ := user_ctor hc'
    exact N.dom_envT_block h2T h3T hT (.inr (List.mem_map.mpr ⟨c', hcb, rfl⟩))
  rcases (addFold_spec h1).2.2.2.1 c ci h with ⟨x, hx, rfl, -⟩ | h
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
    exact N.dom_envT_block h2T h3T hT (.inl (List.mem_map.mpr ⟨t, List.mem_of_mem_take ht, rfl⟩))
  · rw [N.envT_eq hT]
    exact domT h2T h3T (Dom.mono N.S.le₁ (by unfold Dom; rw [h]; nofun))

include hRN hfin hrecu hctu in
theorem model_env₁_rec : IsModel (Mrec M b nuser) env₁ :=
  have hM₁ := N.S.model₁ (carrier_tupleFn M b)
  IsModel.congr hM₁.1 hM₁.2 fun _ hx => N.Mrec_dom₁ hRN hfin hrecu hctu hx

include hRN hfin hrecu hctu h2T h3T hT in
theorem aux_mem {x : Name} (hx : x ∈ auxNames tr b nuser) {ci : VConstant}
    (hci : envT.constants x = some ci) {ls : List Nat} (hl : ls.length = b.uvars) :
    ci.uvars = b.uvars ∧ ∃ B, Mrec M b nuser x ls ∈ˢ piTel (Mrec M b nuser) ls b.params B [] := by
  have hMT := N.model_envT_rec hRN hfin h2T h3T hT
  have hM₁ := N.model_env₁_rec hRN hfin hrecu hctu
  rw [N.envT_eq hT] at hci
  have hx₂ : x ∈ auxNames (certTr tr rec fams) b nuser := by rwa [auxNames_certTr]
  rcases List.mem_append.mp hx₂ with hx₂ | hx₂
  ·
    rw [← N.drop_names] at hx₂
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx₂
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp (List.mem_of_mem_drop ht)
    have h := N.S.hwt; rw [withTypes_eq] at h
    have hc₁ := addFold_get h (List.mem_map.mpr ⟨_, List.getElem_mem hj, rfl⟩)
    have hcT := constT h3T ((addFold_spec h2T).2.2.1.constants hc₁)
    rw [hci] at hcT; cases hcT
    refine ⟨rfl, ?_⟩
    have hmem := hMT.const (N.envT_eq hT ▸ hci) ls hl []
    obtain ⟨_, hd⟩ := N.S.types_defeq j hj
    have heq := ((Nested.IsModel.of_le hM₁ N.S.le₁).sound hd ls [] trivial).1
    simp only at hmem
    rw [heq, forallTel_append, interp_forallTel] at hmem
    exact ⟨_, hmem⟩
  ·
    obtain ⟨t, ht, hct⟩ := List.mem_flatMap.mp hx₂
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hct
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp (List.mem_of_mem_drop ht)
    have hcb : c ∈ b.ctors := List.mem_flatMap.mpr ⟨_, List.getElem_mem hj, hc⟩
    have hcT := constT h3T (addFold_get h2T (List.mem_map.mpr ⟨c, hcb, rfl⟩))
    rw [hci] at hcT; cases hcT
    refine ⟨rfl, ?_⟩
    have hmem := hMT.const (N.envT_eq hT ▸ hci) ls hl []
    rw [getElem_eq_getElem! hj] at hc
    obtain ⟨Ps, hPl, hty, hPd⟩ := N.S.ctor_shape j hj c hc
    simp only at hmem
    rw [hty, interp_forallTel] at hmem
    rw [piTel_pointwise (Bs := b.params) (by rw [hPl]; rfl) fun i hi hi' zs hzs => by
      obtain ⟨_, hd⟩ := hPd i (by rw [← hPl]; exact hi)
      have hsat := Sat.of_ext (Γ := []) (ρ := []) trivial hzs
      have := (hM₁.sound hd ls _ (by simpa using hsat)).1
      rw [← getElem_eq_getElem! hi, ← getElem_eq_getElem! hi'] at this
      simpa using this] at hmem
    exact ⟨_, hmem⟩

include hRN hfin hrecu hctu h1 h2 h2T h3T hT in
theorem aux_read {x : Name} (hx : x ∈ auxNames tr b nuser) {ls : List Nat}
    (hl : ls.length = b.uvars) :
    Scoped (Dom e₂) 0 ((certTr tr rec fams).restore [] b.nparams (etaParams b x)) ∧ ∀ ρ,
      interp (Mrec M b nuser) ls ((certTr tr rec fams).restore [] b.nparams (etaParams b x)) ρ =
        interp (Mrec M b nuser) ls (etaParams b x) ρ := by
  have hx' : x ∈ auxNs (certTr tr rec fams) b nuser := by
    simpa [auxNs, auxNames_certTr] using hx
  have SH := (N.scopeHyp_ctor h1 h2).mono_source
    (P₂ := fun c => Dom env₁ c ∨ c ∈ auxNs (certTr tr rec fams) b nuser) fun _ h => h
  have hn : b.params.length = b.nparams := rfl
  have hs : restoreSafeTop (auxNs (certTr tr rec fams) b nuser) (auxMs (certTr tr rec fams) b nuser)
      (ownLevels b.uvars) b.nparams (etaParams b x) = true := by
    show restoreSafeTop.go _ _ _ _ b.params.length (Spec.lamTel b.params _) 0 = true
    refine restoreSafeTop_go_lamTel _ _ 0 N.params_aux_free ?_
    refine restoreSafe_appN_const (List.contains_iff_mem.mpr hx') (by simp [vars]) ?_
      (by rw [List.drop_eq_nil_of_le (by simp [vars])]; rfl)
    rw [Nat.zero_add, hn, List.take_of_length_le (by simp [vars])]
  have he := N.etaParams_scoped hx
  have hQ : ∀ ys, Ext (Mrec M b nuser) ls b.params [] ys → Ext M ls b.params [] ys := fun ys h =>
    (Ext.congrM (P := Dom env) (fun c hc => by
        rw [N.hagT' hRN hfin h2T h3T hT (N.envT_eq hT ▸ domT h2T h3T (Dom.mono N.S.le₁ hc)),
          N.envT_agree c hc])
      fun A hA => N.S.params_consts' A hA).mp h
  exact restore_read_lam (N.restoreHyp_ctor hRN hfin hrecu hctu hl) SH (fun _ _ => rfl) b.params
      _ hn hs he hQ

include hRN hfin hrecu hctu h1 h2 h2T h3T hT in
theorem aux_eq {x : Name} (hx : x ∈ auxNames tr b nuser) {ls : List Nat} (hl : ls.length = b.uvars)
    (ρ : List V) :
    interp (Mrec M b nuser) ls ((certTr tr rec fams).restore [] b.nparams (etaParams b x)) ρ =
      interp (Mrec M b nuser) ls (etaParams b x) ρ :=
  (N.aux_read hRN hfin hrecu hctu h1 h2 h2T h3T hT hx hl).2 ρ

include hRN hfin hrecu hctu h1 h2 h2T h3T hT in
theorem aux_law {x : Name} (hx : x ∈ auxNames tr b nuser) {ci : VConstant}
    (hci : envT.constants x = some ci) {ls : List Nat} (hl : ls.length = b.uvars) (ρ : List V) :
    interp (Mrec M b nuser) ls (etaParams b x) ρ =
        interp (Mrec M b nuser) ls ((certTr tr rec fams).restore [] b.nparams (etaParams b x)) ρ ∧
      interp (Mrec M b nuser) ls (etaParams b x) ρ ∈ˢ interp (Mrec M b nuser) ls ci.type ρ := by
  refine ⟨(N.aux_eq hRN hfin hrecu hctu h1 h2 h2T h3T hT hx hl ρ).symm, ?_⟩
  obtain ⟨hu, B, hB⟩ := N.aux_mem hRN hfin hrecu hctu h2T h3T hT hx hci hl
  rw [interp_closed _ _ (N.etaParams_scoped hx).1 ρ, interp_etaParams hl hB]
  exact (N.model_envT_rec hRN hfin h2T h3T hT).const hci ls (hu ▸ hl) ρ

omit N in
theorem certEnv_le {E : VEnv} (hE : certEnv tr b nuser rec fams envT = some E) :
    envT ≤ E ∧ ∀ p ∈ auxRecTable b nuser, Dom E p.2 := by
  unfold certEnv at hE
  obtain ⟨e, he₁, he₂⟩ := Option.bind_eq_some_iff.mp hE
  have hB : ∀ (xs : List Name) (e₀ e : VEnv),
      xs.foldlM (fun e x => do
        let ci ← envT.constants x
        pure (e.addDefEq { uvars := b.uvars, lhs := etaParams b x,
                           rhs := (certTr tr rec fams).restore [] b.nparams (etaParams b x),
                           type := ci.type })) e₀ = some e → e₀ ≤ e := by
    intro xs
    induction xs with
    | nil => intro e₀ e he; cases he; exact .rfl
    | cons x xs ih =>
      intro e₀ e he
      simp only [List.foldlM_cons] at he
      obtain ⟨e', h', he'⟩ := Option.bind_eq_some_iff.mp he
      obtain ⟨ci, -, h'⟩ := Option.bind_eq_some_iff.mp h'
      cases h'
      exact VEnv.addDefEq_le.trans (ih _ _ he')
  have hA : ∀ (ps : List (Name × Name)) (e₀ e : VEnv),
      ps.foldlM (fun e p => do
        let ci ← envT.constants p.1
        let e ← e.addConst p.2 ci
        let lv := ownLevels ci.uvars
        pure (e.addDefEq { uvars := ci.uvars, lhs := .const p.2 lv, rhs := .const p.1 lv,
                           type := ci.type })) e₀ = some e →
      e₀ ≤ e ∧ ∀ p ∈ ps, Dom e p.2 := by
    intro ps
    induction ps with
    | nil => intro e₀ e he; cases he; exact ⟨.rfl, nofun⟩
    | cons p ps ih =>
      intro e₀ e he
      simp only [List.foldlM_cons] at he
      obtain ⟨e', h', he'⟩ := Option.bind_eq_some_iff.mp he
      obtain ⟨ci, -, h'⟩ := Option.bind_eq_some_iff.mp h'
      obtain ⟨e₁, he₁, h'⟩ := Option.bind_eq_some_iff.mp h'
      cases h'
      obtain ⟨hle, hdom⟩ := ih _ _ he'
      have hle₁ : e₁ ≤ e := VEnv.addDefEq_le.trans hle
      refine ⟨(VEnv.addConst_le he₁).trans hle₁, fun q hq => ?_⟩
      rcases List.mem_cons.mp hq with rfl | hq
      · exact Dom.mono hle₁ (by unfold Dom; rw [VEnv.addConst_self he₁]; nofun)
      · exact hdom q hq
  obtain ⟨hle, hdom⟩ := hA _ envT e he₁
  have hle₂ := hB _ e E he₂
  exact ⟨hle.trans hle₂, fun p hp => Dom.mono hle₂ (hdom p hp)⟩

include hRN hfin hrecu hctu h1 h2 h2T h3T hT in
theorem certEnv_good {E : VEnv} (hE : certEnv tr b nuser rec fams envT = some E) : Good E := by
  obtain ⟨hle, hdomE⟩ := certEnv_le hE
  have hGT := N.modelT.2
  have hTE : ∀ c, Dom envT c → Dom E c := fun _ h => Dom.mono hle h
  have hty : ∀ {c ci}, envT.constants c = some ci → Scoped (Dom E) 0 ci.type := fun hci => by
    obtain ⟨_, h1, _⟩ := hGT.1.1 hci
    obtain ⟨_, h2, _⟩ := hGT.2.1 hci
    exact ⟨h1, h2.mono hTE⟩
  unfold certEnv at hE
  obtain ⟨e, he₁, he₂⟩ := Option.bind_eq_some_iff.mp hE
  have hA : ∀ (ps : List (Name × Name)) (e₀ e : VEnv), (∀ p ∈ ps, p ∈ auxRecTable b nuser) →
      GoodIn e₀ (Dom E) →
      ps.foldlM (fun e p => do
        let ci ← envT.constants p.1
        let e ← e.addConst p.2 ci
        let lv := ownLevels ci.uvars
        pure (e.addDefEq { uvars := ci.uvars, lhs := .const p.2 lv, rhs := .const p.1 lv,
                           type := ci.type })) e₀ = some e →
      GoodIn e (Dom E) := by
    intro ps
    induction ps with
    | nil => intro e₀ e _ h he; cases he; exact h
    | cons p ps ih =>
      intro e₀ e hps h he
      simp only [List.foldlM_cons] at he
      obtain ⟨e', h', he'⟩ := Option.bind_eq_some_iff.mp he
      refine ih e' e (fun q hq => hps q (List.mem_cons_of_mem _ hq)) ?_ he'
      obtain ⟨ci, hci, h'⟩ := Option.bind_eq_some_iff.mp h'
      obtain ⟨e₁, he₁, h'⟩ := Option.bind_eq_some_iff.mp h'
      cases h'
      have hT₁ := hty hci
      have hG₁ : GoodIn e₁ (Dom E) := h.addFold (cs := [(p.2, ci)]) (by simpa [addFold] using he₁)
        fun x hx => by
          rcases List.mem_singleton.mp hx with rfl
          exact ⟨hT₁.1, hT₁.2⟩
      exact hG₁.addDefEq ⟨trivial, hdomE p (hps p List.mem_cons_self)⟩
        ⟨trivial, hTE _ (by unfold Dom; rw [hci]; nofun)⟩ hT₁
  have hB : ∀ (xs : List Name) (e₀ e : VEnv), (∀ x ∈ xs, x ∈ auxNames tr b nuser) →
      GoodIn e₀ (Dom E) →
      xs.foldlM (fun e x => do
        let ci ← envT.constants x
        pure (e.addDefEq { uvars := b.uvars, lhs := etaParams b x,
                           rhs := (certTr tr rec fams).restore [] b.nparams (etaParams b x),
                           type := ci.type })) e₀ = some e →
      GoodIn e (Dom E) := by
    intro xs
    induction xs with
    | nil => intro e₀ e _ h he; cases he; exact h
    | cons x xs ih =>
      intro e₀ e hxs h he
      simp only [List.foldlM_cons] at he
      obtain ⟨e', h', he'⟩ := Option.bind_eq_some_iff.mp he
      refine ih e' e (fun y hy => hxs y (List.mem_cons_of_mem _ hy)) ?_ he'
      obtain ⟨ci, hci, h'⟩ := Option.bind_eq_some_iff.mp h'
      cases h'
      have hx := hxs x List.mem_cons_self
      have hl := N.etaParams_scoped hx
      have hr := (N.aux_read hRN hfin hrecu hctu h1 h2 h2T h3T hT hx
        (ls := List.replicate b.uvars 0) (by simp)).1
      refine h.addDefEq ⟨hl.1, hl.2.mono fun c hc => hTE c ?_⟩
        ⟨hr.1, hr.2.mono fun c hc => hTE c (N.dom_e₂ h1 h2 h2T h3T hT hc)⟩ (hty hci)
      rcases hc with hc | hc
      · rw [N.envT_eq hT]; exact domT h2T h3T hc
      · exact N.dom_envT_aux h2T h3T hT (by simpa [auxNs, auxNames_certTr] using hc)
  exact GoodIn.good (hB _ e E (fun _ h => h)
    (hA _ envT e (fun _ h => h) (Good.goodIn hGT hTE) he₁) he₂)

include hRN hfin hrecu hctu h1 h2 h2T h3T hT in
theorem certEnv_model {E : VEnv} (hE : certEnv tr b nuser rec fams envT = some E) :
    IsModel (Mrec M b nuser) E := by
  have hMT := N.model_envT_rec hRN hfin h2T h3T hT
  unfold certEnv at hE
  obtain ⟨e, he₁, he₂⟩ := Option.bind_eq_some_iff.mp hE
  have hA : ∀ (ps : List (Name × Name)) (e₀ e : VEnv), (∀ p ∈ ps, p ∈ auxRecTable b nuser) →
      IsModel (Mrec M b nuser) e₀ →
      ps.foldlM (fun e p => do
        let ci ← envT.constants p.1
        let e ← e.addConst p.2 ci
        let lv := ownLevels ci.uvars
        pure (e.addDefEq { uvars := ci.uvars, lhs := .const p.2 lv, rhs := .const p.1 lv,
                           type := ci.type })) e₀ = some e →
      IsModel (Mrec M b nuser) e := by
    intro ps
    induction ps with
    | nil => intro e₀ e _ h he; cases he; exact h
    | cons p ps ih =>
      intro e₀ e hps h he
      simp only [List.foldlM_cons] at he
      obtain ⟨e', h', he'⟩ := Option.bind_eq_some_iff.mp he
      refine ih e' e (fun q hq => hps q (List.mem_cons_of_mem _ hq)) ?_ he'
      obtain ⟨ci, hci, h'⟩ := Option.bind_eq_some_iff.mp h'
      obtain ⟨e₁, he₁, h'⟩ := Option.bind_eq_some_iff.mp h'
      cases h'
      have hp := hps p List.mem_cons_self
      have hval : Mrec M b nuser p.2 = Mrec M b nuser p.1 := by
        rw [Mrec_fin (RecNames.spec hRN).fin_nodup hp, N.hagT' hRN hfin h2T h3T hT
            (by simp [Dom, hci])]
      have hmem : ∀ ls : List Nat, ls.length = ci.uvars → ∀ ρ,
          Mrec M b nuser p.2 ls ∈ˢ interp (Mrec M b nuser) ls ci.type ρ := fun ls hl ρ => by
        rw [hval]; exact hMT.const hci ls hl ρ
      refine IsModel.addDefEq (IsModel.addConst_same h he₁ hmem) fun ls hl ρ =>
        ⟨by simp only [interp, hval], ?_⟩
      simp only [interp]
      rw [show (ownLevels ci.uvars).map (VLevel.eval ls) = ls from map_eval_params hl]
      exact hmem ls hl ρ
  have hM₁ := hA _ envT e (fun _ h => h) hMT he₁
  have hB : ∀ (xs : List Name) (e₀ e : VEnv), (∀ x ∈ xs, x ∈ auxNames tr b nuser) →
      IsModel (Mrec M b nuser) e₀ →
      xs.foldlM (fun e x => do
        let ci ← envT.constants x
        pure (e.addDefEq { uvars := b.uvars, lhs := etaParams b x,
                           rhs := (certTr tr rec fams).restore [] b.nparams (etaParams b x),
                           type := ci.type })) e₀ = some e →
      IsModel (Mrec M b nuser) e := by
    intro xs
    induction xs with
    | nil => intro e₀ e _ h he; cases he; exact h
    | cons x xs ih =>
      intro e₀ e hxs h he
      simp only [List.foldlM_cons] at he
      obtain ⟨e', h', he'⟩ := Option.bind_eq_some_iff.mp he
      refine ih e' e (fun y hy => hxs y (List.mem_cons_of_mem _ hy)) ?_ he'
      obtain ⟨ci, hci, h'⟩ := Option.bind_eq_some_iff.mp h'
      cases h'
      exact IsModel.addDefEq h fun ls hl ρ =>
        N.aux_law hRN hfin hrecu hctu h1 h2 h2T h3T hT (hxs x List.mem_cons_self) hci hl ρ
  exact hB _ e E (fun _ h => h) hM₁ he₂

omit N in
theorem map_eq_of_forall₂ {α β γ} {R : α → β → Prop} {f : α → γ} {g : β → γ}
    (hfg : ∀ a b, R a b → f a = g b) :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → l₁.map f = l₂.map g
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons h hs => by simp [hfg _ _ h, map_eq_of_forall₂ hfg hs]

theorem certKey_data
    (hok : CertsOK tr b nuser rec fams envT)
    {g : Nat} {K : VExpr} (hK : certKey rec fams g = some K) {a : Aux}
    (ha : tr.aux[g]? = some a) :
    ∃ j, ∃ hj : j < fams.length, ∃ Ks r E key, fams[j].kernelDs = some Ks ∧
      rec[fams[j].ri]? = some r ∧ certEnv tr b nuser rec fams envT = some E ∧
      CertOK tr b nuser E fams[j] Ks r ∧ fams[j].Ds.length = r.b.nparams ∧
      K = atKey fams[j].lv fams[j].Ds 0 key ∧ a.key.EqL (atKey fams[j].lv Ks 0 key) ∧
      key.ClosedN r.b.nparams ∧ ConstsIn (Dom env) key ∧
      ∃ c us as, key = appN (.const c us) as := by
  obtain ⟨j, hj, Ks, σ, hσl, r, key, hKs, hσg, hr, hkey, rfl⟩ := certKey_some hK
  obtain ⟨E, r', hE, hr', hC⟩ := hok j hj Ks hKs
  obtain rfl : r = r' := Option.some.inj (hr.symm.trans hr')
  obtain ⟨a', key', ha', hkey', hEqL⟩ := hC.2.2.2 σ hσl
  rw [hσg, ha] at ha'; obtain rfl := Option.some.inj ha'
  rw [hkey] at hkey'; obtain rfl := Option.some.inj hkey'
  obtain ⟨r₀, hr₀, ⟨hφ, hDl, -⟩, -⟩ := N.famsOK.1 j hj
  obtain rfl : r = r₀ := Option.some.inj (hr.symm.trans hr₀)
  obtain ⟨k, hk, hkc, hkC, hshape, -⟩ := (N.canon r (List.mem_of_getElem? hr)).slots σ (hφ ▸ hσl)
  rw [hkey] at hk; obtain rfl := Option.some.inj hk
  exact ⟨j, hj, Ks, r, E, key, hKs, hr, hE, hC, hDl, rfl, hEqL, hkc, hkC, hshape⟩

include hRN hfin hrecu hctu h1 h2 h2T h3T hT in
theorem cert_key_agree
    (hok : CertsOK tr b nuser rec fams envT)
    {g : Nat} {K : VExpr} (hK : certKey rec fams g = some K) {a : Aux}
    (ha : tr.aux[g]? = some a) (ls : List Nat) :
    KeyAgree (Mrec M b nuser) ls b.nparams (Ext M ls b.params []) K a.key := by
  obtain ⟨j, hj, Ks, r, E, key, -, -, hE, ⟨hlenK, -, hconv, -⟩, hDl, rfl, hEqL, hkc, -,
    ⟨c, us, as, rfl⟩⟩ := N.certKey_data hok hK ha
  have hKl : Ks.length = r.b.nparams := by simpa [SBlock.nparams] using hlenK
  rw [atKey_appN_const] at hEqL ⊢
  obtain ⟨us', as', hak, hus, has⟩ := EqL.appN_const hEqL
  rw [hak]
  have hasc : ∀ x ∈ as, x.ClosedN r.b.nparams := (closedN_appN_inv hkc).2
  have hGE := N.certEnv_good hRN hfin hrecu hctu h1 h2 h2T h3T hT hE
  have hME := N.certEnv_model hRN hfin hrecu hctu h1 h2 h2T h3T hT hE
  have hiD : ∀ i, i < Ks.length → i < fams[j].Ds.length := fun i h => by omega
  have hconv' := fun i (h : i < Ks.length) => hconv i h (hiD i h) (hlenK ▸ h)
  have hKc : ∀ D ∈ Ks, D.ClosedN b.nparams := fun D hD => by
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hD
    have := ((hconv' i hi).closedN' hGE.1 N.S.params_ctx_closed).1
    rwa [List.length_reverse] at this
  have hc : (VExpr.const c us').EqL (.const c (us.map (·.inst fams[j].lv))) := by
    unfold VExpr.EqL; exact ⟨rfl, hus⟩
  refine ⟨EqL.closedN (EqL.appN_congr hc has) ?_, c, _, us', _, as',
    headArgs_appN_const .., headArgs_appN_const .., (levels_eval hus ls).symm, ?_⟩
  · refine closedN_appN_of trivial fun x hx => ?_
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    have := closedN_subst (f := argSubst Ks) (N := Ks.length) (n := b.nparams) (k := 0)
      (fun i hi => by
          unfold argSubst; rw [dite_eq_left hi]; exact hKc _ (List.mem_reverse.mp
              (List.getElem_mem _)))
      (e := y.instL fams[j].lv) (by rw [Nat.zero_add, hKl]; exact (hasc y hy).instL)
    simpa using this
  · intro xs hxs hQ
    have hQ' : Ext (Mrec M b nuser) ls b.params [] xs :=
      (Ext.congrM (P := Dom env) (fun c hc => by
          rw [N.hagT' hRN hfin h2T h3T hT (N.envT_eq hT ▸ domT h2T h3T (Dom.mono N.S.le₁ hc)),
            N.envT_agree c hc])
        fun A hA => N.S.params_consts' A hA).mpr hQ
    have hsat : Sat (Mrec M b nuser) ls b.params.reverse xs.reverse := by
      simpa using Sat.of_ext (Γ := []) (ρ := []) trivial hQ'
    have hargs : keyArgs (Mrec M b nuser) ls fams[j].Ds xs.reverse =
        keyArgs (Mrec M b nuser) ls Ks xs.reverse := by
      unfold keyArgs; congr 1
      refine List.ext_getElem (by simp [hKl, hDl]) fun i h₁ h₂ => ?_
      simp only [List.getElem_map]
      exact ((hME.sound (hconv' i (by simpa using h₂)) ls xs.reverse hsat).1).symm
    have hm : as'.map (interp (Mrec M b nuser) ls · xs.reverse) =
        (as.map fun x => subst (argSubst Ks) (x.instL fams[j].lv) 0).map
          (interp (Mrec M b nuser) ls · xs.reverse) :=
      map_eq_of_forall₂ (R := VExpr.EqL) (fun _ _ h => interp_EqL _ ls h xs.reverse) has
    rw [hm, List.map_map, List.map_map]
    refine List.map_congr_left fun y hy => ?_
    have hy' := (hasc y hy)
    show interp _ ls (atKey fams[j].lv fams[j].Ds 0 y) ([] ++ xs.reverse) =
      interp _ ls (atKey fams[j].lv Ks 0 y) ([] ++ xs.reverse)
    rw [interp_atKey (k := 0) _ ls _ _ _ (by rw [Nat.zero_add, hDl]; exact hy') [] rfl,
      interp_atKey (k := 0) _ ls _ _ _ (by rw [Nat.zero_add, hKl]; exact hy') [] rfl, hargs]

include hRN hfin hrecu hctu h1 h2 h2T h3T hT in
theorem aux_agree
    (hok : CertsOK tr b nuser rec fams envT)
    {ls : List Nat} (hl : ls.length = b.uvars) :
    List.Forall₂ (AuxAgree (Mrec M b nuser) ls b.nparams (Ext M ls b.params []))
      (certTr tr rec fams).aux tr.aux := by
  have H := N.restoreHyp_ctor hRN hfin hrecu hctu hl
  refine forall₂_mapIdx fun g hg => ⟨rfl, ?_⟩
  show KeyAgree _ _ _ _ ((certKey rec fams g).getD tr.aux[g].key) tr.aux[g].key
  cases hK : certKey rec fams g with
  | some K =>
    exact N.cert_key_agree hRN hfin hrecu hctu h1 h2 h2T h3T hT hok hK
      (List.getElem?_eq_getElem hg) ls
  | none =>
    have hg' : g < (certTr tr rec fams).aux.length := by simpa [certTr] using hg
    have hm := List.getElem_mem hg'
    have hk : ((certTr tr rec fams).aux[g]).key = tr.aux[g].key := by simp [certTr, hK]
    obtain ⟨Ic, Ils, Ds, hh⟩ := H.key_head _ hm
    have hc := H.closed _ hm
    rw [hk] at hh hc
    exact ⟨hc, Ic, Ils, Ils, Ds, Ds, hh, hh, rfl, fun _ _ _ => rfl⟩

include hRN hfin hrecu hctu h1 h2 h2T h3T hT in
theorem kernel_key_scoped
    (hok : CertsOK tr b nuser rec fams envT)
    {a : Aux} (ha : a ∈ tr.aux) :
    Scoped (fun c => (Dom env₁ c ∧ c ∉ tr.aux.map (·.name)) ∨
      c ∈ ((b.types.take nuser).flatMap (·.ctors)).map (·.name) ∨
      (∃ d < nuser, b.recName d = c) ∨ ∃ p ∈ auxRecTable b nuser, p.2 = c) b.nparams a.key := by
  refine ⟨?_, ?_⟩
  · obtain ⟨_, -, hA⟩ := List.Forall₂.forall_exists_r
      (N.aux_agree hRN hfin hrecu hctu h1 h2 h2T h3T hT hok (ls := List.replicate b.uvars 0)
        (by simp)) a ha
    exact hA.2.1
  obtain ⟨g, hg, rfl⟩ := List.getElem_of_mem ha
  have hfresh : ∀ {c}, Dom env c → c ∉ tr.aux.map (·.name) := fun hc hm =>
    N.S.not_name hc (by rw [N.names_split, certTr_aux_names]; exact List.mem_append_right _ hm)
  cases hK : certKey rec fams g with
  | none =>
    have hg' : g < (certTr tr rec fams).aux.length := by simpa [certTr] using hg
    have haM := List.getElem_mem hg'
    have hk : ((certTr tr rec fams).aux[g]).key = tr.aux[g].key := by simp [certTr, hK]
    obtain ⟨J, lv, Ds, r, m, d, hs⟩ := N.aux_mem_spec haM
    rw [← hk]
    exact ((N.key_consts haM hs).and (N.key_fresh hs)).mono fun c ⟨hc, hna⟩ => hc.elim
      (fun h => .inl ⟨h, by rwa [certTr_aux_names] at hna⟩) (fun h => .inr (.inl h))
  | some K =>
    obtain ⟨j, hj, Ks, r, E, key, -, -, hE, ⟨hlenK, hment, hconv, -⟩, hDl, -, hEqL, -, hkc, -⟩ :=
      N.certKey_data hok hK (List.getElem?_eq_getElem hg)
    refine EqL.constsIn hEqL (constsIn_subst (constsIn_argSubst fun D hD => ?_)
      (constsIn_instL.mpr (hkc.mono fun c hc => .inl ⟨Dom.mono N.S.le₁ hc, hfresh hc⟩)))
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hD
    have hiP : i < (r.b.params.map (·.instL fams[j].lv)).length := hlenK ▸ hi
    have hiD : i < fams[j].Ds.length := by
      rw [hDl]; simpa [SBlock.nparams] using hiP
    have hGE := N.certEnv_good hRN hfin hrecu hctu h1 h2 h2T h3T hT hE
    have hdomE : ∀ c, Dom env c → Dom E c := fun c h =>
      Dom.mono (certEnv_le hE).1 (by rw [N.envT_eq hT]; exact domT h2T h3T (Dom.mono N.S.le₁ h))
    have hcE : ConstsIn (Dom E) Ks[i] := (IsDefEq.constsIn hGE.2 (hconv i hi hiD hiP)
      fun B hB => (N.S.params_consts' B (List.mem_reverse.mp hB)).mono hdomE).1
    refine (hcE.and (constsIn_of_mentions (hment _ (List.getElem_mem hi)))).mono
      fun c ⟨hc, hn⟩ => ?_
    simp only [List.mem_append, not_or] at hn
    rcases certEnv_dom hE hc with hcT | ⟨q, hq, rfl⟩
    · rw [N.envT_eq hT, dom_iotaFold] at hcT
      obtain ⟨ci, hci⟩ := Option.ne_none_iff_exists'.mp hcT
      rcases (addFold_spec h3T).2.2.2.1 c ci hci with ⟨x, hx, hxc, -⟩ | h₂
      ·
        obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hx
        simp only at hxc; subst hxc
        rw [List.mem_range] at hd
        by_cases hdu : d < nuser
        · exact .inr (.inr (.inl ⟨d, hdu, rfl⟩))
        · exfalso; apply hn.2
          simp only [auxRecTable, List.map_map, List.mem_map, List.mem_range, Function.comp_def]
          exact ⟨d - nuser, by omega, by rw [Nat.add_sub_cancel' (by omega)]⟩
      rcases (addFold_spec h2T).2.2.2.1 c ci h₂ with ⟨x, hx, hxc, -⟩ | h₁
      ·
        obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hx
        simp only at hxc; subst hxc
        refine .inr (.inl ?_)
        rw [b.ctors_split nuser] at hc'
        rcases List.mem_append.mp hc' with hu | ha'
        · exact List.mem_map.mpr ⟨c', hu, rfl⟩
        · exfalso; apply hn.1
          obtain ⟨t, ht, hct⟩ := List.mem_flatMap.mp ha'
          simp only [auxNames, List.mem_append, List.mem_flatMap, List.mem_map]
          exact Or.inr ⟨t, ht, c', hct, rfl⟩
      · exact .inl ⟨by unfold Dom; rw [h₁]; nofun, fun hm => hn.1 (List.mem_append_left _ hm)⟩
    · exact .inr (.inr (.inr ⟨q, hq, rfl⟩))

end NWF
end Soulgem.Nested
