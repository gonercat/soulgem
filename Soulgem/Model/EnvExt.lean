import Soulgem.Extend

/-! # Extending a model by a batch of fresh constants -/

namespace Soulgem
open ConLeche ConLeche.SetTheory Lean4Lean

universe u
variable {V : Type u} [SetTheory V]

def addFold (env : VEnv) (cs : List (Name × VConstant)) : Option VEnv :=
  cs.foldlM (fun e x => e.addConst x.1 x.2) env

theorem addFold_cons {env : VEnv} {x : Name × VConstant} {cs : List (Name × VConstant)} :
    addFold env (x :: cs) = (env.addConst x.1 x.2).bind fun e => addFold e cs := by
  simp only [addFold, List.foldlM_cons]; rfl

theorem addFold_spec : ∀ {cs : List (Name × VConstant)} {env env₁ : VEnv},
    addFold env cs = some env₁ →
    (∀ x ∈ cs, env.constants x.1 = none) ∧ env₁.defeqs = env.defeqs ∧ env ≤ env₁ ∧
    (∀ c ci, env₁.constants c = some ci → (∃ x ∈ cs, x.1 = c ∧ x.2 = ci) ∨
        env.constants c = some ci) ∧
    (cs.map (·.1)).Nodup ∧ ∀ x ∈ cs, ∃ ci, env₁.constants x.1 = some ci
  | [], env, env₁, h => by
    cases h; exact ⟨nofun, rfl, .rfl, fun _ _ h => .inr h, .nil, nofun⟩
  | x :: cs, env, env₁, h => by
    rw [addFold_cons, Option.bind_eq_some_iff] at h
    obtain ⟨e, he, hrest⟩ := h
    obtain ⟨hfr, hdf, hle, hcs, hnd, hin⟩ := addFold_spec hrest
    have hx : env.constants x.1 = none := by
      unfold VEnv.addConst at he; split at he <;> simp_all
    have hce := addConst_constants he
    refine ⟨?_, ?_, (VEnv.addConst_le he).trans hle, ?_, ?_, ?_⟩
    · intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hx
      · have := hfr y hy; rw [hce] at this; simp only at this
        split at this
        · cases this
        · exact this
    · rw [hdf, addConst_defeqs he]
    · intro c ci hc
      rcases hcs c ci hc with ⟨y, hy, h1, h2⟩ | hc
      · exact .inl ⟨y, .tail _ hy, h1, h2⟩
      · rw [hce] at hc; simp only at hc
        split at hc
        · rename_i h; cases hc; exact .inl ⟨x, .head _, h, rfl⟩
        · exact .inr hc
    · refine List.nodup_cons.mpr ⟨fun hm => ?_, hnd⟩
      obtain ⟨y, hy, hyx⟩ := List.mem_map.mp hm
      have := hfr y hy; rw [hce] at this; simp only [hyx] at this; simp at this
    · intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact ⟨_, hle.constants (VEnv.addConst_self he)⟩
      · exact hin y hy

theorem IsModel.addFold {M M' : CInterp V} {env env₁ : VEnv} {cs : List (Name × VConstant)}
    (hM : IsModel M env) (hG : Good env) (hadd : addFold env cs = some env₁)
    (hagree : ∀ c, Dom env c → M' c = M c)
    (hnew : ∀ x ∈ cs, ∀ ls : List Nat, ls.length = x.2.uvars → ∀ ρ,
      M' x.1 ls ∈ˢ interp M' ls x.2.type ρ) :
    IsModel M' env₁ := by
  obtain ⟨_, hdf, _, hcs, _, _⟩ := addFold_spec hadd
  have hag : ∀ e, ConstsIn (Dom env) e → ∀ ls ρ, interp M' ls e ρ = interp M ls e ρ :=
    fun e he ls ρ => interp_congr (he.mono fun c hc => hagree c hc) ρ
  refine ⟨fun {c ci} h ls hl ρ => ?_, fun {df} h ls hl ρ => ?_⟩
  · rcases hcs c ci h with ⟨x, hx, rfl, rfl⟩ | h
    · exact hnew x hx ls hl ρ
    · obtain ⟨_, hT, -⟩ := hG.2.1 h
      rw [hagree c (by simp [Dom, h]), hag _ hT]
      exact hM.const h ls hl ρ
  · rw [hdf] at h
    obtain ⟨⟨hl', hT'⟩, hr', -⟩ := hG.2.2 h
    rw [hag _ hl', hag _ hr', hag _ hT']
    exact hM.defeq h ls hl ρ

theorem IsModel.addFold_same {M : CInterp V} {env env₁ : VEnv} {cs : List (Name × VConstant)}
    (hM : IsModel M env) (hadd : Soulgem.addFold env cs = some env₁)
    (hnew : ∀ x ∈ cs, ∀ ls : List Nat, ls.length = x.2.uvars → ∀ ρ,
      M x.1 ls ∈ˢ interp M ls x.2.type ρ) :
    IsModel M env₁ := by
  obtain ⟨_, hdf, _, hcs, _, _⟩ := addFold_spec hadd
  refine ⟨fun {c ci} h ls hl ρ => ?_, fun {df} h => ?_⟩
  · rcases hcs c ci h with ⟨x, hx, rfl, rfl⟩ | h
    · exact hnew x hx ls hl ρ
    · exact hM.const h ls hl ρ
  · rw [hdf] at h; exact hM.defeq h

theorem Good.addFold {env env₁ : VEnv} {cs : List (Name × VConstant)} (hG : Good env)
    (hadd : addFold env cs = some env₁)
    (hnew : ∀ x ∈ cs, x.2.type.ClosedN ∧ ConstsIn (Dom env₁) x.2.type) : Good env₁ := by
  obtain ⟨_, hdf, hle, hcs, _, _⟩ := addFold_spec hadd
  refine ⟨⟨fun {c ci} h => ?_, fun {df} h => ?_⟩, ⟨fun {c ci} h => ?_, fun {df} h => ?_⟩⟩
  · rcases hcs c ci h with ⟨x, hx, rfl, rfl⟩ | h
    · exact ⟨.zero, (hnew x hx).1, trivial⟩
    · exact hG.1.1 h
  · rw [hdf] at h; exact hG.1.2 h
  · rcases hcs c ci h with ⟨x, hx, rfl, rfl⟩ | h
    · exact ⟨.zero, (hnew x hx).2, trivial⟩
    · obtain ⟨u, h1, h2⟩ := hG.2.1 h
      exact ⟨u, h1.mono fun _ => Dom.mono hle, h2.mono fun _ => Dom.mono hle⟩
  · rw [hdf] at h
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hG.2.2 h
    exact ⟨⟨h1.mono fun _ => Dom.mono hle, h2.mono fun _ => Dom.mono hle⟩,
      h3.mono fun _ => Dom.mono hle, h4.mono fun _ => Dom.mono hle⟩

theorem IsModel.addDefEq {M : CInterp V} {env : VEnv} {df : VDefEq} (hM : IsModel M env)
    (hdf : ∀ ls : List Nat, ls.length = df.uvars → ∀ ρ,
      interp M ls df.lhs ρ = interp M ls df.rhs ρ ∧ interp M ls df.lhs ρ ∈ˢ interp M ls df.type ρ) :
    IsModel M (env.addDefEq df) :=
  ⟨hM.const, fun {df'} h => by
    rcases h with rfl | h
    · exact hdf
    · exact hM.defeq h⟩

end Soulgem
