import Soulgem.Model.BlockFields

/-! # The setting of a block extension -/

namespace Soulgem.BlockModel
open ConLeche ConLeche.SetTheory ConLeche.SetTheory.Tower Lean4Lean Spec BlockSem

universe u
variable {V : Type u} [SetTheory V]

theorem tel_closed {env : VEnv} (henv : env.OnTypes fun _ e A => e.ClosedN ∧ A.ClosedN)
    {U : Nat} {Γ0 As : List VExpr} (h0 : CtxClosed Γ0)
    (h : ∀ i (hi : i < As.length), env.IsType U ((As.take i).reverse ++ Γ0) As[i]) :
    ∀ i ≤ As.length, CtxClosed ((As.take i).reverse ++ Γ0) := by
  intro i
  induction i with
  | zero => intro _; simpa using h0
  | succ i ih =>
    intro hi
    have hlt : i < As.length := by omega
    rw [List.take_add_one, List.getElem?_eq_getElem hlt]
    simp only [Option.toList_some, List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.cons_append]
    refine ⟨ih (by omega), ?_⟩
    obtain ⟨_, hT⟩ := h i hlt
    have := (hT.closedN' henv (ih (by omega))).1
    simpa using this

theorem tel_entry_closed {env : VEnv} (henv : env.OnTypes fun _ e A => e.ClosedN ∧ A.ClosedN)
    {U : Nat} {Γ0 As : List VExpr} (h0 : CtxClosed Γ0)
    (h : ∀ i (hi : i < As.length), env.IsType U ((As.take i).reverse ++ Γ0) As[i])
    {i : Nat} (hi : i < As.length) : As[i].ClosedN (Γ0.length + i) := by
  obtain ⟨_, hT⟩ := h i hi
  have := (hT.closedN' henv (tel_closed henv h0 h i (Nat.le_of_lt hi))).1
  simp only [List.length_append, List.length_reverse, List.length_take,
    Nat.min_eq_left (Nat.le_of_lt hi)] at this
  rwa [Nat.add_comm] at this

theorem tel_consts {env : VEnv}
    (henv : env.OnTypes fun _ e A => ConstsIn (Dom env) e ∧ ConstsIn (Dom env) A)
    {U : Nat} {Γ0 As : List VExpr} (h0 : ∀ B ∈ Γ0, ConstsIn (Dom env) B)
    (h : ∀ i (hi : i < As.length), env.IsType U ((As.take i).reverse ++ Γ0) As[i]) :
    ∀ A ∈ As, ConstsIn (Dom env) A := by
  have key : ∀ i ≤ As.length, ∀ B ∈ (As.take i).reverse ++ Γ0, ConstsIn (Dom env) B := by
    intro i
    induction i with
    | zero => intro _; simpa using h0
    | succ i ih =>
      intro hi B hB
      have hlt : i < As.length := by omega
      rw [List.take_add_one, List.getElem?_eq_getElem hlt] at hB
      simp only [Option.toList_some, List.reverse_append, List.reverse_cons, List.reverse_nil,
        List.nil_append, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hB
      rcases hB with (rfl | hB) | hB
      · obtain ⟨_, hT⟩ := h i hlt
        exact (IsDefEq.constsIn henv hT (ih (by omega))).1
      · exact ih (by omega) B (List.mem_append_left _ hB)
      · exact ih (by omega) B (List.mem_append_right _ hB)
  intro A hA
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hA
  obtain ⟨_, hT⟩ := h i hi
  exact (IsDefEq.constsIn henv hT (key i (Nat.le_of_lt hi))).1

theorem constsIn_forallTel {P : Name → Prop} : ∀ (As : List VExpr) (R : VExpr),
    ConstsIn P (Spec.forallTel As R) ↔ (∀ A ∈ As, ConstsIn P A) ∧ ConstsIn P R
  | [], R => by simp [Spec.forallTel]
  | A :: As, R => by
    simp only [Spec.forallTel, ConstsIn, constsIn_forallTel As R, List.mem_cons, forall_eq_or_imp]
    constructor
    · intro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩
    · intro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩

theorem constsIn_appN {P : Name → Prop} : ∀ (f : VExpr) (as : List VExpr),
    ConstsIn P (appN f as) ↔ ConstsIn P f ∧ ∀ a ∈ as, ConstsIn P a
  | f, [] => by simp [appN]
  | f, a :: as => by
    have := constsIn_appN (P := P) (.app f a) as
    simp only [appN, List.foldl] at this ⊢
    rw [this]; simp only [ConstsIn, List.mem_cons, forall_eq_or_imp]
    constructor
    · intro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩
    · intro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩

structure Setting (M : CInterp V) (env env₁ : VEnv) (b : SBlock) : Prop where
  hM : IsModel M env
  hG : Good env
  hwf : b.WF env
  hwt : b.withTypes env = some env₁

def Setting.FieldFull (b : SBlock) (env : VEnv) (Γ : List VExpr) (d : Nat) (f : SField) : Prop :=
  match f.cert with
  | .plain w => DefEqTy env b.uvars Γ f.ty w ∧ mentions b.names w = false
  | .recursive xs k idx =>
    k < b.ntypes ∧ idx.length = (b.types[k]!).indices.length ∧
    DefEqTy env b.uvars Γ f.ty (Spec.forallTel xs (b.indApp k (d + xs.length) idx)) ∧
    (∀ x ∈ xs, mentions b.names x = false) ∧ (∀ i ∈ idx, mentions b.names i = false) ∧
    (∀ e < xs.length, AnnOK env b.uvars ((xs.take e).reverse ++ Γ) xs[e]!) ∧
    (∀ l < idx.length, env.HasType b.uvars (xs.reverse ++ Γ) idx[l]!
      (b.idxType k (d - b.nparams + xs.length) idx l)) ∧
    ∀ e < xs.length, ∃ u, env.HasType b.uvars ((xs.take e).reverse ++ Γ) xs[e]! (.sort u) ∧
      ∀ ls, b.level.eval ls ≠ 0 → u.eval ls ≤ b.level.eval ls

namespace Setting
variable {M : CInterp V} {env env₁ : VEnv} {b : SBlock} (S : Setting M env env₁ b)
include S

theorem nodup : b.names.Nodup := (List.nodup_append.mp S.hwf.syn.nodup).1

theorem types_defeq : ∀ (j : Nat) (hj : j < b.ntypes), DefEqTy env b.uvars [] (b.types[j]'hj).type
    (Spec.forallTel (b.params ++ (b.types[j]'hj).indices) (.sort b.level)) :=
  fun _ hj => (S.hwf.types _ (List.getElem_mem hj)).2

theorem model₁ {C : List Nat → List V → Nat → V} (hC : TupleFn M b C) :
    IsModel (M₁ M b C) env₁ ∧ Good env₁ :=
  model_withTypes hC S.hM S.hG S.hwt S.nodup S.types_defeq

theorem good₁ : Good env₁ := (S.model₁ (carrier_tupleFn M b)).2

theorem ctorOK : ∀ j < b.ntypes, ∀ c ∈ (b.types[j]!).ctors, b.CtorOK env₁ j c := by
  obtain ⟨env₁', h1, h2⟩ := S.hwf.ctors
  rw [S.hwt] at h1; cases h1; exact h2

theorem le₁ : env ≤ env₁ := by
  have := S.hwt; rw [withTypes_eq] at this; exact (addFold_spec this).2.2.1

theorem dom_of_dom₁ {c : Name} (hc : Dom env₁ c) (hn : c ∉ b.names) : Dom env c := by
  have h := S.hwt; rw [withTypes_eq] at h
  obtain ⟨_, _, _, hcs, _, _⟩ := addFold_spec h
  intro hnone
  obtain ⟨ci, hci⟩ := Option.ne_none_iff_exists'.mp hc
  rcases hcs c ci hci with ⟨x, hx, rfl, _⟩ | h'
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
    exact hn (List.mem_map.mpr ⟨t, ht, rfl⟩)
  · rw [hnone] at h'; cases h'

theorem agree {C : List Nat → List V → Nat → V} {c : Name} (hc : Dom env c) : M₁ M b C c = M c := by
  refine M₁_other fun hm => ?_
  have h := S.hwt; rw [withTypes_eq] at h
  obtain ⟨hfr, _⟩ := addFold_spec h
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hm
  exact hc (hfr (t.name, _) (List.mem_map.mpr ⟨t, ht, rfl⟩))

theorem free {C : List Nat → List V → Nat → V} {e : VExpr} (h₁ : ConstsIn (Dom env₁) e)
    (hm : mentions b.names e = false) : ConstsIn (fun c => M₁ M b C c = M c) e :=
  ((h₁.and (constsIn_of_mentions hm)).mono fun _ ⟨h1, h2⟩ => S.agree (S.dom_of_dom₁ h1 h2))

theorem free₀ {C : List Nat → List V → Nat → V} {e : VExpr} (h : ConstsIn (Dom env) e) :
    ConstsIn (fun c => M₁ M b C c = M c) e :=
  h.mono fun _ hc => S.agree hc

theorem params_consts : ∀ i ≤ b.nparams, ∀ B ∈ (b.params.take i), ConstsIn (Dom env) B := by
  intro i
  induction i with
  | zero => intro _ B hB; simp at hB
  | succ i ih =>
    intro hi B hB
    rw [List.take_add_one] at hB
    rcases List.mem_append.mp hB with hB | hB
    · exact ih (by omega) B hB
    · have hlt : i < b.params.length := by unfold SBlock.nparams at hi; omega
      simp [List.getElem?_eq_getElem hlt] at hB; subst hB
      obtain ⟨⟨_, h⟩, _⟩ := S.hwf.params i hlt
      have e : b.params[i]! = b.params[i] := by
        rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hlt]; rfl
      rw [e] at h
      exact (IsDefEq.constsIn S.hG.2 h fun B hB =>
        ih (by omega) B (List.mem_reverse.mp hB)).1

theorem params_consts' : ∀ B ∈ b.params, ConstsIn (Dom env) B := fun B hB =>
  S.params_consts b.nparams (Nat.le_refl _) B (by
      rw [List.take_of_length_le (by unfold SBlock.nparams; omega)]; exact hB)

abbrev fctx (b : SBlock) (c : SCtor) (a : Nat) : List VExpr :=
  (b.params ++ (c.fields.take a).map (·.ty)).reverse

theorem field_ok {j : Nat} (hj : j < b.ntypes) {c : SCtor} (hc : c ∈ (b.types[j]!).ctors)
    {a : Nat} (ha : a < c.fields.length) :
    env₁.HasType b.uvars (fctx b c a) (c.fields[a]!).ty (.sort (c.fields[a]!).sort) ∧
    AnnOK env₁ b.uvars (fctx b c a) (c.fields[a]!).ty ∧
    (b.level.isAlwaysZero ∨ LevelLE (c.fields[a]!).sort b.level) ∧
    b.FieldOK env₁ (fctx b c a) (b.nparams + a) (c.fields[a]!) :=
  (S.ctorOK j hj c hc).fields a ha

theorem ctorSyn {j : Nat} (hj : j < b.ntypes) {c : SCtor} (hc : c ∈ (b.types[j]!).ctors) :
    b.CtorSyn j c := S.hwf.syn.ctors j hj c hc

theorem ctor_shape (j : Nat) (hj : j < b.ntypes) (c : SCtor) (hc : c ∈ (b.types[j]!).ctors) :
    ∃ Ps : List VExpr, Ps.length = b.nparams ∧
      c.type = Spec.forallTel Ps (Spec.forallTel (c.fields.map (·.ty))
        (b.indApp j (b.nparams + c.fields.length) c.idx)) ∧
      ∀ i < b.nparams, DefEqTy env₁ b.uvars (b.params.take i).reverse Ps[i]! b.params[i]! := by
  have hy := S.ctorSyn hj hc
  have hk := S.ctorOK j hj c hc
  obtain ⟨⟨Ps, body⟩, hs, hb⟩ := Option.map_eq_some_iff.mp hy.shape
  simp only at hb; subst hb
  obtain ⟨hPl, hty⟩ := stripPi_eq hs
  have hP : c.paramTys b.nparams = Ps := by simp [SCtor.paramTys, hs]
  exact ⟨Ps, hPl, hty, fun i hi => hP ▸ hk.params i hi⟩

theorem field_full {j : Nat} (hj : j < b.ntypes) {c : SCtor} (hc : c ∈ (b.types[j]!).ctors)
    {a : Nat} (ha : a < c.fields.length) :
    FieldFull b env₁ (fctx b c a) (b.nparams + a) (c.fields[a]!) := by
  have hok := (S.field_ok hj hc ha).2.2.2
  have hmem : c.fields[a]! ∈ c.fields := by
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem ha]; exact List.getElem_mem ha
  have hsy := (S.ctorSyn hj hc).fields _ hmem
  unfold FieldFull
  unfold SBlock.FieldOK at hok
  unfold SBlock.FieldSyn at hsy
  split
  · rename_i w h; simp only [h] at hok hsy; exact ⟨hok, hsy⟩
  · rename_i xs k idx h
    simp only [h] at hok hsy
    obtain ⟨h1, h2, h3, h4⟩ := hsy
    obtain ⟨g1, g2, g3, g4⟩ := hok
    exact ⟨h1, h2, g1, h3, h4, g2, g3, g4⟩

theorem fctx_consts {j : Nat} (hj : j < b.ntypes) {c : SCtor} (hc : c ∈ (b.types[j]!).ctors) :
    ∀ a ≤ c.fields.length, ∀ B ∈ fctx b c a, ConstsIn (Dom env₁) B := by
  intro a
  induction a with
  | zero =>
    intro _ B hB
    simp only [fctx, List.take_zero, List.map_nil, List.append_nil, List.mem_reverse] at hB
    exact (S.params_consts' B hB).mono fun _ => Dom.mono S.le₁
  | succ a ih =>
    intro ha B hB
    simp only [fctx, List.mem_reverse, List.mem_append] at hB
    rcases hB with hB | hB
    · exact (S.params_consts' B hB).mono fun _ => Dom.mono S.le₁
    · rw [List.take_add_one, List.map_append, List.mem_append] at hB
      rcases hB with hB | hB
      · exact ih (by omega) B (by
          simp only [fctx, List.mem_reverse, List.mem_append]; exact .inr hB)
      · have hlt : a < c.fields.length := by omega
        simp [List.getElem?_eq_getElem hlt] at hB; subst hB
        have h := (S.field_ok hj hc hlt).1
        have e : c.fields[a]! = c.fields[a] := by
          rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hlt]; rfl
        rw [e] at h
        exact (IsDefEq.constsIn S.good₁.2 h (ih (by omega))).1

theorem params_ok : ∀ i (hi : i < b.params.length),
    env.IsType b.uvars ((b.params.take i).reverse ++ []) b.params[i] := by
  intro i hi
  have := (S.hwf.params i hi).1
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi] at this
  simpa using this

theorem params_ctx_closed : CtxClosed b.params.reverse := by
  have := tel_closed S.hG.1 (Γ0 := []) trivial S.params_ok b.params.length (Nat.le_refl _)
  simpa using this

theorem indices_ok {k : Nat} (hk : k < b.ntypes) :
    ∀ i (hi : i < (b.types[k]'hk).indices.length),
    env.IsType b.uvars (((b.types[k]'hk).indices.take i).reverse ++ b.params.reverse)
      (b.types[k]'hk).indices[i] := by
  intro i hi
  have := ((S.hwf.types _ (List.getElem_mem hk)).1 i hi).1
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi] at this
  simpa [List.reverse_append] using this

theorem indices_closed {k : Nat} (hk : k < b.ntypes) {l : Nat}
    (hl : l < (b.types[k]!).indices.length) :
    ((b.types[k]!).indices[l]!).ClosedN (b.nparams + l) := by
  revert hl; rw [getElem!_types hk]; intro hl
  have := tel_entry_closed S.hG.1 S.params_ctx_closed (S.indices_ok hk) hl
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hl]
  simpa [SBlock.nparams] using this

theorem indices_consts {k : Nat} (hk : k < b.ntypes) :
    ∀ A ∈ (b.types[k]!).indices, ConstsIn (Dom env) A := by
  rw [getElem!_types hk]
  exact tel_consts S.hG.2 (fun B hB => S.params_consts' B (List.mem_reverse.mp hB))
      (S.indices_ok hk)

theorem interp_field {C : List Nat → List V → Nat → V} (hC : TupleFn M b C) {ls : List Nat}
    (hl : ls.length = b.uvars) {j : Nat} (hj : j < b.ntypes)
    {c : SCtor} (hc : c ∈ (b.types[j]!).ctors) {a : Nat} (ha : a < c.fields.length)
    {zs : List V} (hzl : zs.length = b.nparams + a)
    (hsat : Sat (M₁ M b C) ls (fctx b c a) zs.reverse)
    (hps : Ext M ls b.params [] (zs.take b.nparams)) :
    interp (M₁ M b C) ls (c.fields[a]!).ty zs.reverse =
      fdom M ls (C ls (zs.take b.nparams).reverse) (c.fields[a]!) zs.reverse := by
  have hfok := S.field_full hj hc ha
  have hM₁ := (S.model₁ hC).1
  have hctx := S.fctx_consts hj hc a (Nat.le_of_lt ha)
  unfold FieldFull at hfok
  unfold fdom
  split at hfok
  · rename_i w hcert
    rw [hcert]
    obtain ⟨⟨_, hd⟩, hm⟩ := hfok
    rw [(hM₁.sound hd ls _ hsat).1]
    exact interp_congr (S.free (IsDefEq.constsIn S.good₁.2 hd hctx).2.1 hm) _
  · rename_i xs k idx hcert
    rw [hcert]
    obtain ⟨hk, hil, ⟨_, hd⟩, hxs, hidx, _, hty, _⟩ := hfok
    rw [(hM₁.sound hd ls _ hsat).1, interp_forallTel]
    have hcR := (constsIn_forallTel xs _).mp (IsDefEq.constsIn S.good₁.2 hd hctx).2.1
    have hxfree : ∀ A ∈ xs, ConstsIn (fun c => M₁ M b C c = M c) A :=
      fun A hA => S.free (hcR.1 A hA) (hxs A hA)
    rw [piTel_congrM (fun _ h => h) hxfree]
    refine piTel_congr fun ys hys => ?_
    have hys₁ : Ext (M₁ M b C) ls xs zs.reverse ys :=
      (Ext.congrM (fun _ h => h) fun A hA => (hxfree A hA).mono fun _ h => h.symm).mp hys
    have hlen := Ext.length_eq M ls hys
    have hrev : ys.reverse ++ zs.reverse = (zs ++ ys).reverse := by simp
    have htake : (zs ++ ys).take b.nparams = zs.take b.nparams :=
      List.take_append_of_le_length (by omega)
    have hsat' : Sat (M₁ M b C) ls (xs.reverse ++ fctx b c a) (zs ++ ys).reverse := by
      rw [← hrev]; exact Sat.of_ext hsat hys₁
    have hfit := BlockModel.idx_fit_gen (M := M) hM₁ hsat' (n := b.nparams) (E := a + xs.length)
      (by simp [hzl, hlen]; omega) hil
      (fun l hl' => by
        have := hty l hl'
        rw [idxType_eq] at this
        simpa [Nat.add_sub_cancel_left] using this)
      (fun l hl' => S.indices_closed hk hl') (fun A hA => S.free₀ (S.indices_consts hk A hA))
    rw [htake] at hfit
    rw [hrev, interp_indApp S.nodup hl hk (by simp [hzl, hlen]) (by omega)
        (by rw [htake]; exact hps)
      (by rw [htake]; exact hfit), htake]
    congr 2
    have hci : ∀ i ∈ idx, ConstsIn (Dom env₁) i := fun i hi =>
      ((constsIn_appN _ _).mp hcR.2).2 i (List.mem_append_right _ hi)
    exact List.map_congr_left fun i hi => interp_congr (S.free (hci i hi) (hidx i hi)) _

end Setting
end Soulgem.BlockModel
