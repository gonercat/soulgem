import Soulgem.Model.BlockScope

/-! # The model of a block -/

namespace Soulgem
open ConLeche ConLeche.SetTheory ConLeche.SetTheory.Tower Lean4Lean Spec

universe u
variable {V : Type u} [SetTheory V]

/-! ## Lists -/

theorem find?_of_nodup_map {α β : Type _} [DecidableEq β] {f : α → β} :
    ∀ {l : List α}, (l.map f).Nodup → ∀ {a : α}, a ∈ l → l.find?
        (fun p => decide (f p = f a)) = some a
  | [], _, _, h => absurd h List.not_mem_nil
  | x :: xs, hnd, a, ha => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [List.find?_cons]
    by_cases hx : f x = f a
    · rw [decide_eq_true hx]
      simp only
      rcases List.mem_cons.mp ha with rfl | ha
      · rfl
      · exact absurd (hx ▸ List.mem_map_of_mem ha) hnd.1
    · rw [decide_eq_false hx]
      simp only
      rcases List.mem_cons.mp ha with rfl | ha
      · exact absurd rfl hx
      · exact find?_of_nodup_map hnd.2 ha

theorem range_map_getElem! {α : Type _} [Inhabited α] (l : List α) :
    (List.range l.length).map (fun i => l[i]!) = l := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range]
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem h2]; rfl

namespace BlockModel
open BlockSem Setting

/-! ## The declarations a block adds -/

def ctorConsts (b : SBlock) : List (Name × VConstant) :=
  b.ctors.map fun c => (c.name, { uvars := b.uvars, type := c.type })

def recConsts (b : SBlock) : List (Name × VConstant) :=
  (List.range b.ntypes).map fun d => (b.recName d, { uvars := b.recUvars, type := b.recType d })

def iotaFold (b : SBlock) (env : VEnv) : VEnv :=
  (List.range b.ntypes).foldl (fun e d =>
    (List.range (b.types[d]!).ctors.length).foldl (fun e q => e.addDefEq (b.iota d q)) e) env

theorem add_spec {b : SBlock} {env env' : VEnv} (h : b.add env = some env') :
    ∃ env₁ env₂ env₃, b.withTypes env = some env₁ ∧ addFold env₁ (ctorConsts b) = some env₂ ∧
      addFold env₂ (recConsts b) = some env₃ ∧ env' = iotaFold b env₃ := by
  unfold SBlock.add at h
  simp only [bind, Option.bind] at h
  split at h; · cases h
  rename_i env₁ h1
  simp only [] at h
  split at h; · cases h
  rename_i env₂ h2
  simp only [] at h
  split at h; · cases h
  rename_i env₃ h3
  simp only [pure] at h
  refine ⟨env₁, env₂, env₃, h1, ?_, ?_, ?_⟩
  · simpa [addFold, ctorConsts, List.foldlM_map] using h2
  · simpa [addFold, recConsts, List.foldlM_map] using h3
  · cases h; rfl

/-! ## The models -/

def ctorPos (b : SBlock) : List (Nat × Nat) :=
  (List.range b.ntypes).flatMap fun j => (List.range (ctorsOf b j).length).map fun q => (j, q)

abbrev ctorAt (b : SBlock) (p : Nat × Nat) : SCtor := (ctorsOf b p.1)[p.2]!

theorem mem_ctorPos {b : SBlock} {j q : Nat} {c : SCtor} (h : (ctorsOf b j)[q]? = some c) :
    (j, q) ∈ ctorPos b ∧ ctorAt b (j, q) = c := by
  have hj := lt_of_ctor h
  obtain ⟨hq, _⟩ := List.getElem?_eq_some_iff.mp h
  refine ⟨List.mem_flatMap.mpr ⟨j, List.mem_range.mpr hj, List.mem_map.mpr
      ⟨q, List.mem_range.mpr hq, rfl⟩⟩, ?_⟩
  simp only [ctorAt, List.getElem!_eq_getElem?_getD, h]; rfl

theorem ctorPos_names (b : SBlock) : (ctorPos b).map (fun p => (ctorAt b p).name) =
    b.ctors.map (·.name) := by
  unfold ctorPos SBlock.ctors
  rw [List.map_flatMap, List.map_flatMap]
  simp only [List.map_map]
  have e1 : ∀ j, (List.range (ctorsOf b j).length).map ((fun p => (ctorAt b p).name) ∘ fun q
      => (j, q)) =
      (ctorsOf b j).map (·.name) := by
    intro j
    rw [← range_map_getElem! (ctorsOf b j), List.map_map, List.length_map, List.length_range]
    rfl
  simp only [e1]
  rw [← range_map_getElem! b.types, List.flatMap_map]
  rfl

theorem ctorPos_nodup {b : SBlock} (hnd : (b.ctors.map (·.name)).Nodup) :
    ((ctorPos b).map fun p => (ctorAt b p).name).Nodup := by
  rw [ctorPos_names]; exact hnd

theorem mem_ctors_name {b : SBlock} {j q : Nat} {c : SCtor} (h : (ctorsOf b j)[q]? = some c) :
    c.name ∈ b.ctors.map (·.name) := by
  rw [← ctorPos_names]
  obtain ⟨hm, he⟩ := mem_ctorPos h
  exact List.mem_map.mpr ⟨_, hm, by rw [he]⟩

variable (M : CInterp V) (b : SBlock) in
noncomputable def M₂ : CInterp V := fun x ls =>
  match (ctorPos b).find? (fun p => decide ((ctorAt b p).name = x)) with
  | some p => ctorVal b (Mc M b) ls p.2 (ctorAt b p)
  | none => Mc M b x ls

variable (M : CInterp V) (b : SBlock) in
noncomputable def M₃ : CInterp V := fun x ls =>
  match (List.range b.ntypes).find? (fun d => decide (b.recName d = x)) with
  | some d => recVal M b (M₂ M b) d ls
  | none => M₂ M b x ls

theorem M₂_ctor {M : CInterp V} {b : SBlock} (hnd : (b.ctors.map (·.name)).Nodup) {j q : Nat}
    {c : SCtor} (h : (ctorsOf b j)[q]? = some c) :
    M₂ M b c.name = fun ls => ctorVal b (Mc M b) ls q c := by
  obtain ⟨hm, he⟩ := mem_ctorPos h
  have := find?_of_nodup_map (ctorPos_nodup hnd) hm
  rw [he] at this
  funext ls
  simp only [M₂, this]
  rw [he]

theorem M₂_other {M : CInterp V} {b : SBlock} {x : Name} (hx : x ∉ b.ctors.map (·.name)) :
    M₂ M b x = Mc M b x := by
  have : (ctorPos b).find? (fun p => decide ((ctorAt b p).name = x)) = none := by
    rw [List.find?_eq_none]
    intro p hp
    simp only [decide_eq_true_eq]
    intro e
    exact hx (by rw [← ctorPos_names]; exact List.mem_map.mpr ⟨p, hp, e⟩)
  funext ls
  simp only [M₂, this]

theorem M₃_rec {M : CInterp V} {b : SBlock} (hnd : ((List.range b.ntypes).map b.recName).Nodup)
    {d : Nat} (hd : d < b.ntypes) : M₃ M b (b.recName d) = fun ls => recVal M b (M₂ M b) d ls := by
  have := find?_of_nodup_map hnd (List.mem_range.mpr hd)
  funext ls
  simp only [M₃, this]

theorem M₃_other {M : CInterp V} {b : SBlock} {x : Name}
    (hx : x ∉ (List.range b.ntypes).map b.recName) : M₃ M b x = M₂ M b x := by
  have : (List.range b.ntypes).find? (fun d => decide (b.recName d = x)) = none := by
    rw [List.find?_eq_none]
    intro d hd
    simp only [decide_eq_true_eq]
    intro e
    exact hx (List.mem_map.mpr ⟨d, hd, e⟩)
  funext ls
  simp only [M₃, this]

theorem mem_ctors {b : SBlock} {c : SCtor} (h : c ∈ b.ctors) :
    ∃ (j q : Nat), (ctorsOf b j)[q]? = some c := by
  obtain ⟨t, ht, hc⟩ := List.mem_flatMap.mp h
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp ht
  obtain ⟨q, hq, rfl⟩ := List.mem_iff_getElem.mp hc
  refine ⟨j, q, ?_⟩
  have e : ctorsOf b j = (b.types[j]).ctors := by
    unfold ctorsOf; rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl
  rw [e, List.getElem?_eq_getElem hq]

theorem Good.addDefEq {env : VEnv} {df : VDefEq} (hG : Good env)
    (hl : Scoped (Dom env) 0 df.lhs) (hr : Scoped (Dom env) 0 df.rhs)
    (ht : Scoped (Dom env) 0 df.type) : Good (env.addDefEq df) := by
  have hD : Dom (env.addDefEq df) = Dom env := rfl
  refine ⟨⟨fun h => hG.1.1 h, fun {df'} h => ?_⟩, ⟨fun h => hG.2.1 h, fun {df'} h => ?_⟩⟩
  · rcases h with rfl | h
    · exact ⟨⟨hl.1, ht.1⟩, ⟨hr.1, ht.1⟩⟩
    · exact hG.1.2 h
  · rw [hD]
    rcases h with rfl | h
    · exact ⟨⟨hl.2, ht.2⟩, ⟨hr.2, ht.2⟩⟩
    · exact hG.2.2 h

theorem foldl_addDefEq {M : CInterp V} : ∀ {dfs : List VDefEq} {env : VEnv},
    IsModel M env → Good env → (∀ df ∈ dfs, (∀ ls : List Nat, ls.length = df.uvars → ∀ ρ,
      interp M ls df.lhs ρ = interp M ls df.rhs ρ ∧ interp M ls df.lhs ρ ∈ˢ interp M ls df.type ρ) ∧
      Scoped (Dom env) 0 df.lhs ∧ Scoped (Dom env) 0 df.rhs ∧ Scoped (Dom env) 0 df.type) →
    IsModel M (dfs.foldl VEnv.addDefEq env) ∧ Good (dfs.foldl VEnv.addDefEq env)
  | [], _, hM, hG, _ => ⟨hM, hG⟩
  | df :: dfs, env, hM, hG, h => by
    obtain ⟨hlaw, hl, hr, ht⟩ := h df (.head _)
    exact foldl_addDefEq (dfs := dfs) (env := env.addDefEq df) (IsModel.addDefEq hM hlaw)
      (Good.addDefEq hG hl hr ht) fun df' hdf' => h df' (List.mem_cons_of_mem _ hdf')

def GoodIn (env : VEnv) (P : Name → Prop) : Prop :=
  env.OnTypes (fun _ e A => e.ClosedN ∧ A.ClosedN) ∧
  env.OnTypes (fun _ e A => ConstsIn P e ∧ ConstsIn P A)

theorem Good.goodIn {env : VEnv} {P : Name → Prop} (hG : Good env) (hP : ∀ c, Dom env c → P c) :
    GoodIn env P :=
  ⟨hG.1, ⟨fun h => let ⟨u, h1, h2⟩ := hG.2.1 h; ⟨u, h1.mono hP, h2.mono hP⟩,
    fun h => let ⟨⟨h1, h2⟩, h3, h4⟩ := hG.2.2 h; ⟨⟨h1.mono hP, h2.mono hP⟩, h3.mono hP,
        h4.mono hP⟩⟩⟩

theorem GoodIn.good {env : VEnv} (h : GoodIn env (Dom env)) : Good env := h

theorem GoodIn.addFold {env env₁ : VEnv} {P : Name → Prop} {cs : List (Name × VConstant)}
    (hG : GoodIn env P) (hadd : addFold env cs = some env₁)
    (hnew : ∀ x ∈ cs, x.2.type.ClosedN ∧ ConstsIn P x.2.type) : GoodIn env₁ P := by
  obtain ⟨_, hdf, _, hcs, _, _⟩ := addFold_spec hadd
  refine ⟨⟨fun {c ci} h => ?_, fun {df} h => ?_⟩, ⟨fun {c ci} h => ?_, fun {df} h => ?_⟩⟩
  · rcases hcs c ci h with ⟨x, hx, rfl, rfl⟩ | h
    · exact ⟨.zero, (hnew x hx).1, trivial⟩
    · exact hG.1.1 h
  · rw [hdf] at h; exact hG.1.2 h
  · rcases hcs c ci h with ⟨x, hx, rfl, rfl⟩ | h
    · exact ⟨.zero, (hnew x hx).2, trivial⟩
    · exact hG.2.1 h
  · rw [hdf] at h; exact hG.2.2 h

theorem GoodIn.addDefEq {env : VEnv} {P : Name → Prop} {df : VDefEq} (hG : GoodIn env P)
    (hl : Scoped P 0 df.lhs) (hr : Scoped P 0 df.rhs) (ht : Scoped P 0 df.type) :
    GoodIn (env.addDefEq df) P := by
  refine ⟨⟨fun h => hG.1.1 h, fun {df'} h => ?_⟩, ⟨fun h => hG.2.1 h, fun {df'} h => ?_⟩⟩
  · rcases h with rfl | h
    · exact ⟨⟨hl.1, ht.1⟩, ⟨hr.1, ht.1⟩⟩
    · exact hG.1.2 h
  · rcases h with rfl | h
    · exact ⟨⟨hl.2, ht.2⟩, ⟨hr.2, ht.2⟩⟩
    · exact hG.2.2 h

theorem foldl_addDefEq_in {M : CInterp V} {P : Name → Prop} :
    ∀ {dfs : List VDefEq} {env : VEnv}, IsModel M env → GoodIn env P →
    (∀ df ∈ dfs, (∀ ls : List Nat, ls.length = df.uvars → ∀ ρ,
      interp M ls df.lhs ρ = interp M ls df.rhs ρ ∧ interp M ls df.lhs ρ ∈ˢ interp M ls df.type ρ) ∧
      Scoped P 0 df.lhs ∧ Scoped P 0 df.rhs ∧ Scoped P 0 df.type) →
    IsModel M (dfs.foldl VEnv.addDefEq env) ∧ GoodIn (dfs.foldl VEnv.addDefEq env) P
  | [], _, hM, hG, _ => ⟨hM, hG⟩
  | df :: dfs, env, hM, hG, h => by
    obtain ⟨hlaw, hl, hr, ht⟩ := h df (.head _)
    exact foldl_addDefEq_in (dfs := dfs) (env := env.addDefEq df) (IsModel.addDefEq hM hlaw)
      (hG.addDefEq hl hr ht) fun df' hdf' => h df' (List.mem_cons_of_mem _ hdf')

theorem iotaFold_eq (b : SBlock) (env : VEnv) : iotaFold b env =
    ((List.range b.ntypes).flatMap fun d =>
      (List.range (b.types[d]!).ctors.length).map (b.iota d)).foldl VEnv.addDefEq env := by
  unfold iotaFold
  rw [List.foldl_flatMap]
  simp only [List.foldl_map]

theorem constants_foldl_addDefEq : ∀ (dfs : List VDefEq) (e : VEnv),
    (dfs.foldl VEnv.addDefEq e).constants = e.constants
  | [], _ => rfl
  | df :: dfs, e => constants_foldl_addDefEq dfs (e.addDefEq df)

theorem constants_iotaFold (b : SBlock) (e : VEnv) : (iotaFold b e).constants = e.constants := by
  rw [iotaFold_eq]; exact constants_foldl_addDefEq _ _

theorem dom_iotaFold {b : SBlock} {e : VEnv} {x : Name} : Dom (iotaFold b e) x ↔ Dom e x := by
  unfold Dom; rw [constants_iotaFold]

namespace Setting
variable {M : CInterp V} {env env₁ : VEnv} {b : SBlock} (S : Setting M env env₁ b)
include S
variable {env₂ env₃ : VEnv} (h2 : addFold env₁ (ctorConsts b) = some env₂)
  (h3 : addFold env₂ (recConsts b) = some env₃)

omit [SetTheory V] S in
include h2 in
theorem ctor_nodup : (b.ctors.map (·.name)).Nodup := by
  have := (addFold_spec h2).2.2.2.2.1
  simpa [ctorConsts, List.map_map, Function.comp_def] using this

omit [SetTheory V] S in
include h2 in
theorem ctor_fresh {x : Name} (hx : x ∈ b.ctors.map (·.name)) : ¬ Dom env₁ x := by
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
  have := (addFold_spec h2).1 (c.name, _) (List.mem_map.mpr ⟨c, hc, rfl⟩)
  simp [Dom, this]

omit [SetTheory V] S in
include h2 in
theorem ctor_dom {x : Name} (hx : x ∈ b.ctors.map (·.name)) : Dom env₂ x := by
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
  obtain ⟨ci, hci⟩ := (addFold_spec h2).2.2.2.2.2 (c.name, _) (List.mem_map.mpr ⟨c, hc, rfl⟩)
  simp [Dom, hci]

omit [SetTheory V] S in
include h3 in
theorem rec_nodup : ((List.range b.ntypes).map b.recName).Nodup := by
  have := (addFold_spec h3).2.2.2.2.1
  simpa [recConsts, List.map_map, Function.comp_def] using this

omit [SetTheory V] S in
include h3 in
theorem rec_fresh {x : Name} (hx : x ∈ (List.range b.ntypes).map b.recName) : ¬ Dom env₂ x := by
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hx
  have := (addFold_spec h3).1 (b.recName d, _) (List.mem_map.mpr ⟨d, hd, rfl⟩)
  simp [Dom, this]

omit [SetTheory V] S in
include h3 in
theorem rec_dom {x : Name} (hx : x ∈ (List.range b.ntypes).map b.recName) : Dom env₃ x := by
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hx
  obtain ⟨ci, hci⟩ := (addFold_spec h3).2.2.2.2.2 (b.recName d, _) (List.mem_map.mpr ⟨d, hd, rfl⟩)
  simp [Dom, hci]

omit S in
include h2 in
theorem hag₂ : ∀ x, Dom env₁ x → M₂ M b x = Mc M b x := fun _ hx =>
  M₂_other fun hm => BlockModel.Setting.ctor_fresh h2 hm hx

include h2 in
theorem model₂₁ : IsModel (M₂ M b) env₁ :=
  IsModel.congr (S.model₁ (carrier_tupleFn M b)).1 S.good₁ (BlockModel.Setting.hag₂ h2)

omit S in
include h2 in
theorem hctor₂ : ∀ j < b.ntypes, ∀ (q : Nat) (c : SCtor), (ctorsOf b j)[q]? = some c →
    M₂ M b c.name = fun ls => ctorVal b (Mc M b) ls q c :=
  fun _ _ _ _ hcq => M₂_ctor (BlockModel.Setting.ctor_nodup h2) hcq

theorem ctor_type_scoped {j q : Nat} {c : SCtor} (hcq : (ctorsOf b j)[q]? = some c) :
    Scoped (Dom env₁) 0 c.type := by
  have hj := lt_of_ctor hcq
  obtain ⟨_, hT⟩ := (S.ctorOK j hj c (List.mem_of_getElem? hcq)).typed
  exact ⟨(hT.closedN' S.good₁.1 trivial).1, (IsDefEq.constsIn S.good₁.2 hT nofun).1⟩

include h2 in
theorem model₂ : IsModel (M₂ M b) env₂ ∧ Good env₂ := by
  have hle := (addFold_spec h2).2.2.1
  refine ⟨IsModel.addFold (S.model₂₁ h2) S.good₁ h2 (fun _ _ => rfl) ?_, Good.addFold S.good₁ h2 ?_⟩
  · intro x hx ls hl ρ
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
    obtain ⟨j, q, hcq⟩ := mem_ctors hc
    have hsc := S.ctor_type_scoped hcq
    simp only []
    rw [interp_closed _ _ hsc.1 ρ, interp_congr (hsc.2.mono (BlockModel.Setting.hag₂ h2)),
        BlockModel.Setting.hctor₂ h2 _ (lt_of_ctor hcq) q c hcq]
    exact S.ctor_typed hl (lt_of_ctor hcq) hcq
  · intro x hx
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
    obtain ⟨j, q, hcq⟩ := mem_ctors hc
    have hsc := S.ctor_type_scoped hcq
    exact ⟨hsc.1, hsc.2.mono fun _ h => Dom.mono hle h⟩

omit S in
include h3 in
theorem hag₃ : ∀ x, Dom env₂ x → M₃ M b x = M₂ M b x := fun _ hx =>
  M₃_other fun hm => BlockModel.Setting.rec_fresh h3 hm hx

include h2 in
theorem rec_type_scoped {Q : Name → Prop} (hQ : ∀ x, Dom env₂ x → Q x) {d : Nat}
    (hd : d < b.ntypes) : Scoped Q 0 (b.recType d) := by
  have hle := (addFold_spec h2).2.2.1
  exact S.recType_scoped (fun x hx => hQ x (Dom.mono hle hx))
    (fun j _ q c hcq => hQ _ (BlockModel.Setting.ctor_dom h2 (mem_ctors_name hcq))) hd

include h2 h3 in
theorem model₃ : IsModel (M₃ M b) env₃ ∧ Good env₃ := by
  have hM₃₂ := IsModel.congr (S.model₂ h2).1 (S.model₂ h2).2 (BlockModel.Setting.hag₃ h3)
  have hle := (addFold_spec h3).2.2.1
  refine ⟨IsModel.addFold hM₃₂ (S.model₂ h2).2 h3 (fun _ _ => rfl) ?_,
    Good.addFold (S.model₂ h2).2 h3 ?_⟩
  · intro x hx ls _ ρ
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hx
    rw [List.mem_range] at hd
    have hsc := S.rec_type_scoped h2 (fun _ h => h) hd
    simp only []
    rw [interp_closed _ _ hsc.1 ρ, interp_congr (hsc.2.mono (BlockModel.Setting.hag₃ h3)),
      M₃_rec (BlockModel.Setting.rec_nodup h3) hd]
    exact S.rec_typed (BlockModel.Setting.hag₂ h2) (S.model₂₁ h2)
        (BlockModel.Setting.hctor₂ h2) ls hd
  · intro x hx
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hx
    rw [List.mem_range] at hd
    exact S.rec_type_scoped h2 (fun _ h => Dom.mono hle h) hd

include h2 h3 in
theorem iota_scoped₃ {d q : Nat} {c : SCtor} (hcq : (ctorsOf b d)[q]? = some c) :
    Scoped (Dom env₃) 0 (b.iota d q).lhs ∧ Scoped (Dom env₃) 0 (b.iota d q).rhs ∧
      Scoped (Dom env₃) 0 (b.iota d q).type := by
  have hle2 := (addFold_spec h2).2.2.1
  have hle3 := (addFold_spec h3).2.2.1
  exact S.iota_scoped (fun x hx => Dom.mono hle3 (Dom.mono hle2 hx))
    (fun j _ q c hcq => Dom.mono hle3 (BlockModel.Setting.ctor_dom h2 (mem_ctors_name hcq)))
    (fun k hk => BlockModel.Setting.rec_dom h3 (List.mem_map.mpr
        ⟨k, List.mem_range.mpr hk, rfl⟩)) hcq

include h2 h3 in
theorem model_add_of_iota
    (hiota : ∀ d q (c : SCtor), (ctorsOf b d)[q]? = some c → ∀ ls : List Nat, ls.length =
        b.recUvars →
      ∀ ρ, interp (M₃ M b) ls (b.iota d q).lhs ρ = interp (M₃ M b) ls (b.iota d q).rhs ρ ∧
        interp (M₃ M b) ls (b.iota d q).lhs ρ ∈ˢ interp (M₃ M b) ls (b.iota d q).type ρ) :
    IsModel (M₃ M b) (iotaFold b env₃) ∧ Good (iotaFold b env₃) := by
  rw [iotaFold_eq]
  obtain ⟨hM, hG⟩ := S.model₃ h2 h3
  refine foldl_addDefEq hM hG fun df hdf => ?_
  obtain ⟨d, hd, hdf⟩ := List.mem_flatMap.mp hdf
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hdf
  rw [List.mem_range] at hq
  have hcq : (ctorsOf b d)[q]? = some (ctorsOf b d)[q] := List.getElem?_eq_getElem hq
  exact ⟨hiota d q _ hcq, S.iota_scoped₃ h2 h3 hcq⟩

end Setting

end BlockModel
end Soulgem
