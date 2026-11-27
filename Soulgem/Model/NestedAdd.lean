import Soulgem.Model.BlockFinal
import Soulgem.Model.Restore

/-! # The environment a nested declaration produces -/

namespace Soulgem.Nested
open ConLeche ConLeche.SetTheory ConLeche.SetTheory.Tower Lean4Lean Spec BlockSem BlockModel

universe u
variable {V : Type u} [SetTheory V]

theorem addFold_some : ∀ {cs : List (Name × VConstant)} {env : VEnv}, (cs.map (·.1)).Nodup →
    (∀ x ∈ cs, env.constants x.1 = none) → ∃ e, addFold env cs = some e
  | [], env, _, _ => ⟨env, rfl⟩
  | x :: cs, env, hnd, hfr => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    have hx := hfr x (.head _)
    let e₁ : VEnv :=
        { env with constants := fun n => if x.1 = n then some x.2 else env.constants n }
    have he₁ : env.addConst x.1 x.2 = some e₁ := by unfold VEnv.addConst; rw [hx]
    obtain ⟨e, he⟩ := addFold_some (env := e₁) hnd.2 fun y hy => by
      have hne : x.1 ≠ y.1 := fun h => hnd.1 ⟨y, hy, h.symm⟩
      simp only [e₁, ite_eq_right hne]; exact hfr y (.tail _ hy)
    exact ⟨e, by rw [addFold_cons, he₁]; exact he⟩

def nTypeConsts (b : SBlock) (nuser : Nat) : List (Name × VConstant) :=
  (b.types.take nuser).map fun t => (t.name, { uvars := b.uvars, type := t.type })

def nCtorConsts (tr : Translated) (b : SBlock) (nuser : Nat) : List (Name × VConstant) :=
  ((b.types.take nuser).flatMap (·.ctors)).map fun c =>
    (c.name, { uvars := b.uvars, type := tr.restore [] b.nparams c.type })

def nRecConsts (tr : Translated) (b : SBlock) (nuser : Nat) : List (Name × VConstant) :=
  (nestedRecs tr b nuser).map fun r => (r.name, { uvars := b.recUvars, type := r.type })

def nIotaFold (tr : Translated) (b : SBlock) (nuser : Nat) (env : VEnv) : VEnv :=
  ((nestedRecs tr b nuser).flatMap (·.iota)).foldl (fun e df => e.addDefEq df) env

theorem addNested_spec {tr : Translated} {b : SBlock} {nuser : Nat} {env env' : VEnv}
    (h : addNested tr b nuser env = some env') :
    ∃ e₁ e₂ e₃, addFold env (nTypeConsts b nuser) = some e₁ ∧
      addFold e₁ (nCtorConsts tr b nuser) = some e₂ ∧
      addFold e₂ (nRecConsts tr b nuser) = some e₃ ∧ env' = nIotaFold tr b nuser e₃ := by
  unfold addNested at h
  simp only [bind, Option.bind] at h
  split at h; · cases h
  rename_i e₁ h1
  simp only [] at h
  split at h; · cases h
  rename_i e₂ h2
  simp only [] at h
  split at h; · cases h
  rename_i e₃ h3
  simp only [pure] at h
  refine ⟨e₁, e₂, e₃, ?_, ?_, ?_, ?_⟩
  · simpa [addFold, nTypeConsts, List.foldlM_map, ← List.map_take] using h1
  · simpa [addFold, nCtorConsts, List.foldlM_map] using h2
  · simpa [addFold, nRecConsts, List.foldlM_map] using h3
  · cases h; rfl

theorem nestedRecs_length (tr : Translated) (b : SBlock) (nuser : Nat) :
    (nestedRecs tr b nuser).length = b.ntypes := by
  simp [nestedRecs]

theorem auxRecTable_length (b : SBlock) (nuser : Nat) :
    (auxRecTable b nuser).length = b.ntypes - nuser := by
  simp [auxRecTable]

theorem nestedRecs_name (tr : Translated) (b : SBlock) (nuser : Nat) {d : Nat} (hd : d < b.ntypes) :
    ((nestedRecs tr b nuser)[d]'(by rw [nestedRecs_length]; exact hd)).name =
      if d < nuser then b.recName d else ((auxRecTable b nuser)[d - nuser]!).2 := by
  simp [nestedRecs]

section Fresh
variable {M : CInterp V} {env env₁ : VEnv} {b : SBlock} (S : Setting M env env₁ b)
include S

theorem env₁_none {c : Name} (hn : c ∉ b.names) (he : env.constants c = none) :
    env₁.constants c = none := by
  have h := S.hwt; rw [withTypes_eq] at h
  obtain ⟨_, _, _, hcs, _, _⟩ := addFold_spec h
  cases hc : env₁.constants c with
  | none => rfl
  | some ci =>
    rcases hcs c ci hc with ⟨x, hx, rfl, _⟩ | hc'
    · obtain ⟨j, hj, rfl⟩ := mem_typeConsts hx
      exact absurd (List.mem_map.mpr ⟨_, List.getElem_mem hj, rfl⟩) hn
    · rw [he] at hc'; cases hc'

end Fresh

structure RecNamesSpec (b : SBlock) (nuser : Nat) : Prop where
  fin_nodup : ((auxRecTable b nuser).map (·.2)).Nodup
  rec_nodup : ((List.range b.ntypes).map b.recName).Nodup
  fin_names : ∀ x ∈ (auxRecTable b nuser).map (·.2), x ∉ b.names
  fin_ctors : ∀ x ∈ (auxRecTable b nuser).map (·.2), x ∉ b.ctors.map (·.name)
  fin_recs : ∀ x ∈ (auxRecTable b nuser).map (·.2), x ∉ (List.range b.ntypes).map b.recName
  rec_names : ∀ x ∈ (List.range b.ntypes).map b.recName, x ∉ b.names
  rec_ctors : ∀ x ∈ (List.range b.ntypes).map b.recName, x ∉ b.ctors.map (·.name)

theorem RecNames.spec {b : SBlock} {nuser : Nat} (h : RecNames b nuser = true) :
    RecNamesSpec b nuser := by
  unfold RecNames at h
  have h := of_decide_eq_true h
  rw [List.nodup_append, List.nodup_append, List.nodup_append] at h
  obtain ⟨⟨⟨hF, hN, hFN⟩, hC, hFNC⟩, hR, hFNCR⟩ := h
  refine ⟨hF, hR, fun x hx hn => hFN x hx x hn rfl, fun x hx hc => ?_, fun x hx hr => ?_,
    fun x hx hn => ?_, fun x hx hc => ?_⟩
  · exact hFNC x (List.mem_append_left _ hx) x hc rfl
  · exact hFNCR x (List.mem_append_left _ (List.mem_append_left _ hx)) x hr rfl
  · exact hFNCR x (List.mem_append_left _ (List.mem_append_right _ hn)) x hx rfl
  · exact hFNCR x (List.mem_append_right _ hc) x hx rfl

theorem recName_mem {b : SBlock} {d : Nat} (hd : d < b.ntypes) :
    b.recName d ∈ (List.range b.ntypes).map b.recName :=
  List.mem_map.mpr ⟨d, List.mem_range.mpr hd, rfl⟩

theorem none_of_le {e e' : VEnv} (hle : e ≤ e') {c : Name} (h : e'.constants c = none) :
    e.constants c = none := by
  cases hc : e.constants c with
  | none => rfl
  | some ci => rw [hle.constants hc] at h; cases h

section Trans
variable {M : CInterp V} {env env₁ : VEnv} {b : SBlock} (S : Setting M env env₁ b)
  {tr : Translated} {nuser : Nat} {e₁ e₂ e₃ : VEnv}
  (hle₁ : env ≤ e₁) (hC : addFold e₁ (nCtorConsts tr b nuser) = some e₂)
  (hR : addFold e₂ (nRecConsts tr b nuser) = some e₃)
  (hAF : AuxFresh b nuser env) (hRN : RecNames b nuser = true)
include S

include hle₁ hC hAF in
theorem trans_ctors : ∃ e, addFold env₁ (ctorConsts b) = some e := by
  have hnd := S.hwf.syn.nodup
  refine addFold_some (by
      simpa [ctorConsts, List.map_map, Function.comp_def] using (List.nodup_append.mp hnd).2.1)
    fun x hx => ?_
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
  have hnn : c.name ∉ b.names := fun hn =>
    (List.nodup_append.mp hnd).2.2 _ hn _ (List.mem_map.mpr ⟨c, hc, rfl⟩) rfl
  refine env₁_none S hnn ?_
  have hct : c ∈ (b.types.take nuser).flatMap (·.ctors) ++
      (b.types.drop nuser).flatMap (·.ctors) := by
    rw [← List.flatMap_append, List.take_append_drop]; exact hc
  rcases List.mem_append.mp hct with hu | ha
  · have := (addFold_spec hC).1 (c.name, _) (List.mem_map.mpr ⟨c, hu, rfl⟩)
    exact none_of_le hle₁ this
  · obtain ⟨t, ht, hct⟩ := List.mem_flatMap.mp ha
    have h1 := List.all_eq_true.mp (of_decide_eq_true (decide_eq_true hAF.1)) t ht
    have h2 := List.all_eq_true.mp h1 c hct
    simpa using h2

include hle₁ hC hR hAF hRN in
theorem trans_recs {e₂T : VEnv} (h2 : addFold env₁ (ctorConsts b) = some e₂T) :
    ∃ e, addFold e₂T (recConsts b) = some e := by
  have RN := RecNames.spec hRN
  refine addFold_some (by simpa [recConsts, List.map_map, Function.comp_def] using RN.rec_nodup)
      fun x hx => ?_
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hx
  have hd := List.mem_range.mp hd
  have hm := recName_mem hd
  obtain ⟨_, _, _, hcs, _, _⟩ := addFold_spec h2
  cases hc : e₂T.constants (b.recName d) with
  | none => rfl
  | some ci =>
    exfalso
    rcases hcs _ ci hc with ⟨y, hy, hy1, _⟩ | hc'
    · obtain ⟨c, hcm, rfl⟩ := List.mem_map.mp hy
      exact RN.rec_ctors _ hm (List.mem_map.mpr ⟨c, hcm, hy1⟩)
    · have hnone : env.constants (b.recName d) = none := by
        by_cases hdu : d < nuser
        · have hlt : d < (nestedRecs tr b nuser).length := by
            rw [nestedRecs_length]; exact hd
          have hmem : ((nestedRecs tr b nuser)[d]'hlt).name ∈
              (nRecConsts tr b nuser).map (·.1) := by
            simp only [nRecConsts, List.map_map]
            exact List.mem_map.mpr ⟨_, List.getElem_mem hlt, rfl⟩
          obtain ⟨y, hy, hy1⟩ := List.mem_map.mp hmem
          have := (addFold_spec hR).1 y hy
          rw [hy1, nestedRecs_name tr b _ hd, ite_eq_left hdu] at this
          exact none_of_le (hle₁.trans (addFold_spec hC).2.2.1) this
        · have h1 := List.all_eq_true.mp (of_decide_eq_true (decide_eq_true hAF.2)) (d - nuser)
            (List.mem_range.mpr (by omega))
          rw [show nuser + (d - nuser) = d by omega] at h1
          simpa using h1
      rw [env₁_none S (RN.rec_names _ hm) hnone] at hc'; cases hc'

end Trans

end Soulgem.Nested
