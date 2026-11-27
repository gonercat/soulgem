import Soulgem.Model.NestedModel

/-! # Assembling the model of a nested block -/

namespace Soulgem.Nested
open ConLeche ConLeche.SetTheory ConLeche.SetTheory.Tower Lean4Lean Spec BlockSem BlockModel

universe u

variable {V : Type u} [SetTheory V]

theorem IsModel.of_le {M : CInterp V} {e e' : VEnv} (h : IsModel M e') (hle : e ≤ e') :
    IsModel M e :=
  ⟨fun hc => h.const (hle.constants hc), fun hd => h.defeq (hle.defeqs hd)⟩

section Read
variable {M₀ M₁' : CInterp V} {ls : List Nat} {tr' : Translated} {auxRec : List (Name × Name)}
  {ns ms : List Name} {us : List VLevel} {n : Nat} {Q : List V → Prop} {P P' : Name → Prop}
  (H : RestoreHyp M₀ M₀ ls tr' auxRec ns ms us n Q) (SH : ScopeHyp tr' auxRec ns ms n P P')
  (hag : ∀ c, P c → M₀ c = M₁' c)
include H SH hag

theorem restore_read_pi (As : List VExpr) (X : VExpr) (hn : As.length = n)
    (hs : restoreSafeTop ns ms us n (Spec.forallTel As X) = true)
    (he : Scoped P 0 (Spec.forallTel As X)) (hQ : ∀ ys, Ext M₀ ls As [] ys → Q ys) :
    Scoped P' 0 (tr'.restore auxRec n (Spec.forallTel As X)) ∧
      ∀ ρ, interp M₀ ls (tr'.restore auxRec n (Spec.forallTel As X)) ρ =
        interp M₁' ls (Spec.forallTel As X) ρ :=
  restore_read H SH hag false As X hn hs he hQ

theorem restore_read_lam (As : List VExpr) (X : VExpr) (hn : As.length = n)
    (hs : restoreSafeTop ns ms us n (Spec.lamTel As X) = true)
    (he : Scoped P 0 (Spec.lamTel As X)) (hQ : ∀ ys, Ext M₀ ls As [] ys → Q ys) :
    Scoped P' 0 (tr'.restore auxRec n (Spec.lamTel As X)) ∧
      ∀ ρ, interp M₀ ls (tr'.restore auxRec n (Spec.lamTel As X)) ρ =
        interp M₁' ls (Spec.lamTel As X) ρ :=
  restore_read H SH hag true As X hn hs he hQ

end Read

theorem user_ctor {b : SBlock} {nuser : Nat} {c : SCtor}
    (hc : c ∈ (b.types.take nuser).flatMap (·.ctors)) :
    ∃ j, j < nuser ∧ j < b.ntypes ∧ c ∈ (b.types[j]!).ctors ∧ c ∈ b.ctors := by
  obtain ⟨t, ht, hct⟩ := List.mem_flatMap.mp hc
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp ht
  have hj' : j < b.types.length := by simp at hj; omega
  rw [List.getElem_take] at hct
  refine ⟨j, by simp at hj; omega, hj', ?_, List.mem_flatMap.mpr ⟨_, List.getElem_mem hj', hct⟩⟩
  rwa [← getElem_eq_getElem! hj']

theorem nestedRecs_type (tr : Translated) (b : SBlock) (nuser : Nat) {d : Nat} (hd : d < b.ntypes) :
    ((nestedRecs tr b nuser)[d]'(by rw [nestedRecs_length]; exact hd)).type =
      (shiftTr tr b.blockLevels).restore (auxRecTable b nuser) b.nparams (b.recType d) := by
  simp [nestedRecs, shiftTr, SBlock.sh]

theorem nestedRecs_iota (tr : Translated) (b : SBlock) (nuser : Nat) {d : Nat} (hd : d < b.ntypes) :
    ((nestedRecs tr b nuser)[d]'(by rw [nestedRecs_length]; exact hd)).iota =
      (List.range (b.types[d]!).ctors.length).map fun q =>
        { b.iota d q with
          lhs := (shiftTr tr b.blockLevels).restore (auxRecTable b nuser) b.nparams (b.iota d q).lhs
          rhs := (shiftTr tr b.blockLevels).restore (auxRecTable b nuser) b.nparams (b.iota d q).rhs
          type := (shiftTr tr b.blockLevels).restore (auxRecTable b nuser) b.nparams (b.iota d
              q).type } := by
  simp [nestedRecs, shiftTr, SBlock.sh]

theorem recType_split (b : SBlock) (d : Nat) : ∃ Rest Y, b.recType d =
    Spec.forallTel ((List.range b.nparams).map fun i => b.binder b.params[i]!)
        (Spec.forallTel Rest Y) :=
  ⟨_, _, by
    rw [recType_eq, preTel_eq, List.append_assoc, List.append_assoc, List.append_assoc]
    exact BlockModel.forallTel_append _ _ _⟩

theorem defeqs_foldl : ∀ (dfs : List VDefEq) (e : VEnv) (df : VDefEq),
    (e.defeqs df ∨ df ∈ dfs) → (dfs.foldl VEnv.addDefEq e).defeqs df
  | [], _, _, h => h.resolve_right List.not_mem_nil
  | x :: xs, e, df, h => defeqs_foldl xs (e.addDefEq x) df <| by
    rcases h with h | h
    · exact .inl (Or.inr h)
    · rcases List.mem_cons.mp h with rfl | h
      · exact .inl (Or.inl rfl)
      · exact .inr h

theorem iota_mem_iotaFold (b : SBlock) (e : VEnv) {d q : Nat} (hd : d < b.ntypes)
    (hq : q < (b.types[d]!).ctors.length) : (iotaFold b e).defeqs (b.iota d q) := by
  rw [iotaFold_eq]
  exact defeqs_foldl _ _ _ (.inr (List.mem_flatMap.mpr
    ⟨d, List.mem_range.mpr hd, List.mem_map.mpr ⟨q, List.mem_range.mpr hq, rfl⟩⟩))

theorem iotaΔ_split (b : SBlock) (d q : Nat) : iotaΔ b d q =
    (List.range b.nparams).map (fun i => b.binder b.params[i]!) ++
      ((List.range b.ntypes).map b.motiveTy ++ (minorList b ++ (b.rulePieces d q).1)) := by
  simp only [iotaΔ, preTel_eq, List.append_assoc]

theorem ScopeHyp.mono_target {tr : Translated} {auxRec : List (Name × Name)} {ns ms : List Name}
    {n : Nat} {P P' P'' : Name → Prop} (H : ScopeHyp tr auxRec ns ms n P P')
    (h : ∀ c, P' c → P'' c) : ScopeHyp tr auxRec ns ms n P P'' where
  ns_iff := H.ns_iff
  ms_ns := H.ms_ns
  ms_rec := H.ms_rec
  rec_ns := H.rec_ns
  key := fun a ha => ⟨(H.key a ha).1, (H.key a ha).2.mono h⟩
  key_head := H.key_head
  ctor := fun c a hc Ic Ils Ds hk => h _ (H.ctor c a hc Ic Ils Ds hk)
  fin := fun p hp => h _ (H.fin p hp)
  other := fun c hc hn hr => h _ (H.other c hc hn hr)

namespace NWF
variable {M : CInterp V} {env env₁ envT : VEnv} {b : SBlock} {rec : List RBlock}
    {tr trN : Translated}
  {nuser : Nat} {fams : List Fam} {MJf : RBlock → CInterp V} {envJf envJ₁f : RBlock → VEnv}
  (N : NWF M env env₁ envT b rec trN nuser fams MJf envJf envJ₁f)
  (hRN : RecNames b nuser = true)
  (hfin : ∀ x ∈ (auxRecTable b nuser).map (·.2), env.constants x = none)
  (hrecu : ∀ d < nuser, env.constants (b.recName d) = none)
  (hctu : ∀ c ∈ (b.types.take nuser).flatMap (·.ctors), env.constants c.name = none)
  {e₁ e₂ e₃ : VEnv}
  (h1 : addFold env (nTypeConsts b nuser) = some e₁)
  (h2 : addFold e₁ (nCtorConsts tr b nuser) = some e₂)
  (h3 : addFold e₂ (nRecConsts tr b nuser) = some e₃)
  {e₂T e₃T : VEnv} (h2T : addFold env₁ (ctorConsts b) = some e₂T)
  (h3T : addFold e₂T (recConsts b) = some e₃T) (hT : b.add env = some (iotaFold b e₃T))
  (RC : ∀ {ls : List Nat}, ls.length = b.uvars →
    RestoreHyp (Mrec M b nuser) (Mrec M b nuser) ls tr [] (auxNs tr b nuser) (auxMs tr b nuser)
      (ownLevels b.uvars) b.nparams (fun xs => Ext M ls b.params [] xs))
  (RR : ∀ ls' : List Nat,
    RestoreHyp (Mrec M b nuser) (Mrec M b nuser) ls' (shiftTr tr b.blockLevels)
        (auxRecTable b nuser)
      (auxNs tr b nuser) (auxMs tr b nuser) b.blockLevels b.nparams
      (fun xs => Ext M (blev b ls') b.params [] xs))
  (SC : ScopeHyp tr [] (auxNs tr b nuser) (auxMs tr b nuser) b.nparams (Dom env₁) (Dom e₃))
  (SR : ScopeHyp (shiftTr tr b.blockLevels) (auxRecTable b nuser) (auxNs tr b nuser)
    (auxMs tr b nuser) b.nparams (Dom (iotaFold b e₃T)) (Dom e₃))
  (hsafe : RestoreSafe tr b nuser = true)
include N

include hRN hfin h2T h3T in
theorem hagT {x : Name} (hx : Dom (iotaFold b e₃T) x) : Mrec M b nuser x = M₃ M b x :=
  Mrec_of_not_fin (N.fin_not_trans hRN hfin h2T h3T hx)

include hRN hfin hrecu hctu in
theorem model₁_rec : IsModel (Mrec M b nuser) env₁ :=
  IsModel.congr (N.S.model₁ (carrier_tupleFn M b)).1 N.S.good₁
    fun _ hx => N.Mrec_dom₁ hRN hfin hrecu hctu hx

include hRN hfin hrecu hctu h1 in
theorem model_e₁ : IsModel (Mrec M b nuser) e₁ ∧ Good e₁ := by
  have hM₁ := N.model₁_rec hRN hfin hrecu hctu
  have hle₁ := (addFold_spec h1).2.2.1
  have hmem : ∀ x ∈ nTypeConsts b nuser, ∃ t ∈ b.types,
      x = (t.name, { uvars := b.uvars, type := t.type }) := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
    exact ⟨t, List.mem_of_mem_take ht, rfl⟩
  have hwt := N.S.hwt
  rw [withTypes_eq] at hwt
  refine ⟨IsModel.addFold (IsModel.of_le hM₁ (addFold_spec hwt).2.2.1) N.S.hG h1
      (fun _ _ => rfl) ?_,
    Good.addFold N.S.hG h1 ?_⟩
  · intro x hx ls hl ρ
    obtain ⟨t, ht, rfl⟩ := hmem x hx
    exact hM₁.const (addFold_get hwt (List.mem_map.mpr ⟨t, ht, rfl⟩)) ls hl ρ
  · intro x hx
    obtain ⟨t, ht, rfl⟩ := hmem x hx
    obtain ⟨_, w, hT⟩ := N.S.hwf.types t ht
    exact ⟨(hT.closedN' N.S.hG.1 trivial).1,
      (Soulgem.IsDefEq.constsIn N.S.hG.2 hT nofun).1.mono fun _ hc => Dom.mono hle₁ hc⟩

omit N in
include hsafe in
theorem safe_user {c : SCtor} (hc : c ∈ (b.types.take nuser).flatMap (·.ctors)) :
    restoreSafeTop (auxNs tr b nuser) (auxMs tr b nuser) (ownLevels b.uvars) b.nparams c.type
      = true := by
  have h := hsafe
  unfold RestoreSafe at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨t, ht, hct⟩ := List.mem_flatMap.mp hc
  exact h.1 t (List.mem_of_mem_take ht) c hct

omit N in
include h2T h3T in
theorem domT {x : Name} (hx : Dom env₁ x) : Dom (iotaFold b e₃T) x := by
  have hle := VEnv.LE.trans (addFold_spec h2T).2.2.1 (addFold_spec h3T).2.2.1
  exact dom_iotaFold.mpr (Dom.mono hle hx)

omit N in
include h3T in
theorem constT {x : Name} {ci : VConstant} (hx : e₂T.constants x = some ci) :
    (iotaFold b e₃T).constants x = some ci := by
  rw [constants_iotaFold]; exact (addFold_spec h3T).2.2.1.constants hx

include hRN hfin hrecu hctu h1 h2 h3 h2T h3T hT RC SC hsafe in
theorem model_e₂ : IsModel (Mrec M b nuser) e₂ ∧ GoodIn e₂ (Dom e₃) := by
  obtain ⟨hM₁, hG₁⟩ := N.model_e₁ hRN hfin hrecu hctu h1
  have hMT := (N.S.model_add hT).1
  have hle₁₂ := (addFold_spec h2).2.2.1
  have hag : ∀ x, Dom env₁ x → Mrec M b nuser x = M₃ M b x := fun x hx =>
    N.hagT hRN hfin h2T h3T (domT h2T h3T hx)
  have key : ∀ c ∈ (b.types.take nuser).flatMap (·.ctors), ∀ ls : List Nat, ls.length = b.uvars →
      Scoped (Dom e₃) 0 (tr.restore [] b.nparams c.type) ∧
      ∀ ρ, Mrec M b nuser c.name ls ∈ˢ interp (Mrec M b nuser) ls
          (tr.restore [] b.nparams c.type) ρ := by
    intro c hc ls hl
    obtain ⟨j, -, hj, hcj, hcb⟩ := user_ctor hc
    obtain ⟨Ps, hPl, hty, hPd⟩ := N.S.ctor_shape j hj c hcj
    obtain ⟨q, hq, hcq⟩ := List.mem_iff_getElem.mp hcj
    have hcq' : (ctorsOf b j)[q]? = some c := by
      simp only [ctorsOf]; rw [List.getElem?_eq_getElem hq, hcq]
    have hcT : (iotaFold b e₃T).constants c.name = some { uvars := b.uvars, type := c.type } :=
      constT h3T (addFold_get h2T (List.mem_map.mpr ⟨c, hcb, rfl⟩))
    have hmem := hMT.const hcT ls hl
    have hdom : Dom (iotaFold b e₃T) c.name := by unfold Dom; rw [hcT]; nofun
    have hs := safe_user hsafe hc
    have he := N.S.ctor_type_scoped hcq'
    rw [hty] at hs he hmem
    have R := restore_read_pi (RC hl) SC hag Ps _ hPl hs he
      (fun ys hys => N.S.ctor_params_ext (fun x hx => N.Mrec_dom₁ hRN hfin hrecu hctu hx)
          hPl hPd ls hys)
    rw [hty]
    refine ⟨R.1, fun ρ => ?_⟩
    rw [R.2 ρ, N.hagT hRN hfin h2T h3T hdom]
    exact hmem ρ
  have hlen : (List.replicate b.uvars 0).length = b.uvars := List.length_replicate
  have hle₁₃ : e₁ ≤ e₃ := VEnv.LE.trans hle₁₂ (addFold_spec h3).2.2.1
  refine ⟨IsModel.addFold_same hM₁ h2 ?_, GoodIn.addFold (Good.goodIn hG₁ fun _ =>
      Dom.mono hle₁₃) h2 ?_⟩
  · intro x hx ls hl ρ
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
    simp only at hl ⊢
    exact (key c hc ls hl).2 ρ
  · intro x hx
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
    simp only
    exact (key c hc _ hlen).1

omit N in
include hsafe in
theorem safe_rec {d : Nat} (hd : d < b.ntypes) :
    restoreSafeTop (auxNs tr b nuser) (auxMs tr b nuser) b.blockLevels b.nparams
        (b.recType d) = true ∧
    ∀ q < (b.types[d]!).ctors.length,
      restoreSafeTop (auxNs tr b nuser) (auxMs tr b nuser) b.blockLevels b.nparams
          (b.iota d q).lhs = true ∧
      restoreSafeTop (auxNs tr b nuser) (auxMs tr b nuser) b.blockLevels b.nparams
          (b.iota d q).rhs = true ∧
      restoreSafeTop (auxNs tr b nuser) (auxMs tr b nuser) b.blockLevels b.nparams (b.iota d q).type
          = true := by
  have h := hsafe
  unfold RestoreSafe at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨h1, h2⟩ := h.2 d hd
  exact ⟨h1, fun q hq => ⟨(h2 q hq).1.1, (h2 q hq).1.2, (h2 q hq).2⟩⟩

include hRN hfin h2T h3T in
theorem rec_val {d : Nat} (hd : d < b.ntypes) :
    Mrec M b nuser ((nestedRecs tr b nuser)[d]'(by rw [nestedRecs_length]; exact hd)).name =
      M₃ M b (b.recName d) := by
  rw [nestedRecs_name tr b nuser hd]
  by_cases hdu : d < nuser
  · rw [ite_eq_left hdu]
    refine N.hagT hRN hfin h2T h3T ?_
    exact dom_iotaFold.mpr (addFold_dom h3T (List.mem_map.mpr ⟨d, List.mem_range.mpr hd, rfl⟩))
  · rw [ite_eq_right hdu]
    have hi : d - nuser < (auxRecTable b nuser).length := by rw [auxRecTable_length]; omega
    rw [← getElem_eq_getElem! hi, Mrec_fin (RecNames.spec hRN).fin_nodup (List.getElem_mem hi)]
    simp only [auxRecTable, List.getElem_map, List.getElem_range]
    congr 2; omega

include hRN hfin hrecu hctu h1 h2 h3 h2T h3T hT RC RR SC SR hsafe in
theorem model_e₃ : IsModel (Mrec M b nuser) e₃ ∧ GoodIn e₃ (Dom e₃) := by
  obtain ⟨hM₂, hG₂⟩ := N.model_e₂ hRN hfin hrecu hctu h1 h2 h3 h2T h3T hT RC SC hsafe
  have hMT := (N.S.model_add hT).1
  have hM₁ := N.model₁_rec hRN hfin hrecu hctu
  have SH := SR
  have hdom₂ : ∀ x, Dom e₂T x → Dom (iotaFold b e₃T) x := fun _ hx =>
    dom_iotaFold.mpr (Dom.mono (addFold_spec h3T).2.2.1 hx)
  have key : ∀ d (hd : d < b.ntypes), ∀ ls : List Nat, ls.length = b.recUvars →
      Scoped (Dom e₃) 0 ((nestedRecs tr b nuser)[d]'(by rw [nestedRecs_length]; exact hd)).type ∧
      ∀ ρ, Mrec M b nuser ((nestedRecs tr b nuser)[d]'(by rw [nestedRecs_length]; exact hd)).name ls
          ∈ˢ
        interp (Mrec M b nuser) ls ((nestedRecs tr b nuser)[d]'(by
            rw [nestedRecs_length]; exact hd)).type ρ := by
    intro d hd ls hl
    rw [nestedRecs_type tr b nuser hd, N.rec_val hRN hfin h2T h3T hd]
    have hcT : (iotaFold b e₃T).constants (b.recName d) = some
        { uvars := b.recUvars, type := b.recType d } := by
      rw [constants_iotaFold]; exact addFold_get h3T (List.mem_map.mpr
          ⟨d, List.mem_range.mpr hd, rfl⟩)
    have hmem := hMT.const hcT ls hl
    have hs := (safe_rec hsafe hd).1
    have he := N.S.rec_type_scoped h2T hdom₂ hd
    obtain ⟨Rest, Y, hsp⟩ := recType_split b d
    rw [hsp] at hs he hmem ⊢
    have R := restore_read_pi (RR ls) SH
      (fun x hx => N.hagT hRN hfin h2T h3T hx) _ _ (by simp) hs he
      (fun ys hys => (N.S.ext_params (fun x hx => N.Mrec_dom₁ hRN hfin hrecu hctu hx)
          hM₁ ys).mp hys)
    exact ⟨R.1, fun ρ => by rw [R.2 ρ]; exact hmem ρ⟩
  have hlen : (List.replicate b.recUvars 0).length = b.recUvars := List.length_replicate
  refine ⟨IsModel.addFold_same hM₂ h3 ?_, GoodIn.addFold hG₂ h3 ?_⟩
  · intro x hx ls hl ρ
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
    obtain ⟨d, hd, rfl⟩ := List.mem_iff_getElem.mp hr
    have hd' : d < b.ntypes := by rw [nestedRecs_length] at hd; exact hd
    exact (key d hd' ls hl).2 ρ
  · intro x hx
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
    obtain ⟨d, hd, rfl⟩ := List.mem_iff_getElem.mp hr
    have hd' : d < b.ntypes := by rw [nestedRecs_length] at hd; exact hd
    exact (key d hd' _ hlen).1

include hRN hfin hrecu hctu h1 h2 h3 h2T h3T hT RC RR SC SR hsafe in
theorem model_addNested : IsModel (Mrec M b nuser) (nIotaFold tr b nuser e₃) ∧
    Good (nIotaFold tr b nuser e₃) := by
  obtain ⟨hM₃, hG₃⟩ := N.model_e₃ hRN hfin hrecu hctu h1 h2 h3 h2T h3T hT RC RR SC SR hsafe
  have hMT := (N.S.model_add hT).1
  have hM₁ := N.model₁_rec hRN hfin hrecu hctu
  have SH := SR
  have hagT' : ∀ x, Dom (iotaFold b e₃T) x → Mrec M b nuser x = M₃ M b x := fun x hx =>
    N.hagT hRN hfin h2T h3T hx
  have hdom₃ : ∀ x, Dom e₃T x → Dom (iotaFold b e₃T) x := fun _ hx => dom_iotaFold.mpr hx
  have hQ : ∀ ls (ys : List V),
      Ext (Mrec M b nuser) ls ((List.range b.nparams).map fun i => b.binder b.params[i]!) [] ys →
      Ext M (blev b ls) b.params [] ys := fun _ ys hys =>
    (N.S.ext_params (fun x hx => N.Mrec_dom₁ hRN hfin hrecu hctu hx) hM₁ ys).mp hys
  unfold nIotaFold
  have hD : ∀ dfs : List VDefEq, Dom (dfs.foldl VEnv.addDefEq e₃) = Dom e₃ := fun dfs => by
    funext x; unfold Dom; rw [constants_foldl_addDefEq]
  refine (fun H => ⟨H.1, GoodIn.good (by rw [hD]; exact H.2)⟩)
      (foldl_addDefEq_in hM₃ hG₃ fun df hdf => ?_)
  obtain ⟨r, hr, hdf⟩ := List.mem_flatMap.mp hdf
  obtain ⟨d, hd, rfl⟩ := List.mem_iff_getElem.mp hr
  have hd' : d < b.ntypes := by rw [nestedRecs_length] at hd; exact hd
  rw [nestedRecs_iota tr b nuser hd'] at hdf
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hdf
  have hq' := List.mem_range.mp hq
  have hcq : (ctorsOf b d)[q]? = some ((b.types[d]!).ctors[q]!) := by
    simp only [ctorsOf]; rw [List.getElem?_eq_getElem hq', getElem_eq_getElem! hq']
  obtain ⟨hsL, hsR, hsT⟩ := (safe_rec hsafe hd').2 q hq'
  obtain ⟨heL, heR, heT⟩ := N.S.iota_scoped₃ h2T h3T hcq
  have hdfT := hMT.defeq (iota_mem_iotaFold b e₃T hd' hq')
  rw [iota_eq] at hsL hsR hsT heL heR heT hdfT ⊢
  simp only at hsL hsR hsT heL heR heT hdfT ⊢
  rw [iotaΔ_split, lamTel_append] at hsL hsR heL heR
  rw [iotaΔ_split, BlockModel.forallTel_append] at hsT heT
  rw [iotaΔ_split, lamTel_append _ _ (iotaL b d q), lamTel_append _ _ (iotaR b d q),
    BlockModel.forallTel_append _ _ (iotaT b d q)] at hdfT ⊢
  have hn : ((List.range b.nparams).map fun i => b.binder b.params[i]!).length =
      b.nparams := by simp
  have RL := fun ls => restore_read_lam (RR ls) SH hagT' _ _ hn hsL
    ⟨heL.1, heL.2.mono hdom₃⟩ (hQ ls)
  have RRh := fun ls => restore_read_lam (RR ls) SH hagT' _ _ hn hsR
    ⟨heR.1, heR.2.mono hdom₃⟩ (hQ ls)
  have RT := fun ls => restore_read_pi (RR ls) SH hagT' _ _ hn hsT
    ⟨heT.1, heT.2.mono hdom₃⟩ (hQ ls)
  refine ⟨fun ls hl ρ => ?_, (RL []).1, (RRh []).1, (RT []).1⟩
  obtain ⟨E1, E2⟩ := hdfT ls hl ρ
  rw [(RL ls).2 ρ, (RRh ls).2 ρ, (RT ls).2 ρ]
  exact ⟨E1, E2⟩

end NWF

theorem addNested_facts {M : CInterp V} {env env₁ envT : VEnv} {b : SBlock} {rec : List RBlock}
    {tr : Translated} {nuser : Nat} {fams : List Fam} {MJf : RBlock → CInterp V}
    {envJf envJ₁f : RBlock → VEnv} {env' : VEnv}
    (N : NWF M env env₁ envT b rec tr nuser fams MJf envJf envJ₁f) (hRN : RecNames b nuser = true)
    (hnl : nuser ≤ b.ntypes) (hadd : addNested tr b nuser env = some env') :
    ∃ e₁ e₂ e₃ e₂T e₃T, addFold env (nTypeConsts b nuser) = some e₁ ∧
      addFold e₁ (nCtorConsts tr b nuser) = some e₂ ∧ addFold e₂ (nRecConsts tr b nuser) = some e₃ ∧
      env' = nIotaFold tr b nuser e₃ ∧
      (∀ x ∈ (auxRecTable b nuser).map (·.2), env.constants x = none) ∧
      (∀ d < nuser, env.constants (b.recName d) = none) ∧
      (∀ c ∈ (b.types.take nuser).flatMap (·.ctors), env.constants c.name = none) ∧
      addFold env₁ (ctorConsts b) = some e₂T ∧ addFold e₂T (recConsts b) = some e₃T ∧
      b.add env = some (iotaFold b e₃T) := by
  obtain ⟨e₁, e₂, e₃, h1, h2, h3, rfl⟩ := addNested_spec hadd
  have hle₁ := (addFold_spec h1).2.2.1
  have hle₂ := VEnv.LE.trans hle₁ (addFold_spec h2).2.2.1
  have hctu : ∀ c ∈ (b.types.take nuser).flatMap (·.ctors), env.constants c.name = none :=
    fun c hc => none_of_le hle₁ ((addFold_spec h2).1 _ (List.mem_map.mpr ⟨c, hc, rfl⟩))
  have hrec : ∀ d (hd : d < b.ntypes),
      env.constants ((nestedRecs tr b nuser)[d]'(by rw [nestedRecs_length]; exact hd)).name
        = none :=
    fun d _ => none_of_le hle₂ ((addFold_spec h3).1 _ (List.mem_map.mpr
        ⟨_, List.getElem_mem _, rfl⟩))
  have hrecu : ∀ d < nuser, env.constants (b.recName d) = none := fun d hd => by
    have h := hrec d (by omega)
    rw [nestedRecs_name tr b _ (by omega), ite_eq_left hd] at h
    exact h
  have hfin : ∀ x ∈ (auxRecTable b nuser).map (·.2), env.constants x = none := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
    have hi' : i < b.ntypes - nuser := by rw [auxRecTable_length] at hi; exact hi
    have h := hrec (nuser + i) (by omega)
    rw [nestedRecs_name tr b _ (by omega), ite_eq_right (by omega), Nat.add_sub_cancel_left,
      ← getElem_eq_getElem! hi] at h
    exact h
  obtain ⟨e₂T, e₃T, h2T, h3T, hT⟩ := N.trans_add hRN h1 h2 h3
  exact ⟨e₁, e₂, e₃, e₂T, e₃T, h1, h2, h3, rfl, hfin, hrecu, hctu, h2T, h3T, hT⟩

theorem exists_model_addNested {M : CInterp V} {env env₁ envT : VEnv} {b : SBlock}
    {rec : List RBlock} {tr : Translated} {nuser : Nat} {fams : List Fam} {MJf : RBlock → CInterp V}
    {envJf envJ₁f : RBlock → VEnv} {env' : VEnv}
    (N : NWF M env env₁ envT b rec tr nuser fams MJf envJf envJ₁f) (hRN : RecNames b nuser = true)
    (hnl : nuser ≤ b.ntypes) (hadd : addNested tr b nuser env = some env') :
    IsModel (Mrec M b nuser) env' ∧ Good env' := by
  obtain ⟨e₁, e₂, e₃, e₂T, e₃T, h1, h2, h3, rfl, hfin, hrecu, hctu, h2T, h3T, hT⟩ :=
    addNested_facts N hRN hnl hadd
  exact N.model_addNested hRN hfin hrecu hctu h1 h2 h3 h2T h3T hT
    (N.restoreHyp_ctor hRN hfin hrecu hctu) (N.restoreHyp_rec hRN hfin hrecu hctu)
    ((N.scopeHyp_ctor h1 h2).mono_target fun _ => Dom.mono (addFold_spec h3).2.2.1)
    (N.scopeHyp_rec hRN h1 h2 h3 h2T h3T) N.safe

end Soulgem.Nested
