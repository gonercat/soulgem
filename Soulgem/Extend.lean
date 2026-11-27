import Soulgem.Main

/-! # `Good` is kept by adding a well-formed constant or definition -/

namespace Soulgem
open ConLeche ConLeche.SetTheory Lean4Lean

universe u
variable {V : Type u} [SetTheory V]

theorem addConst_defeqs {env env' : VEnv} {n ci} (h : env.addConst n ci = some env') :
    env'.defeqs = env.defeqs := by
  unfold VEnv.addConst at h; split at h <;> cases h; rfl

theorem Good.addConst {env env' : VEnv} (hG : Good env) {ci : VDefVal} (hci : DefWF env ci)
    (hadd : env.addConst ci.name ci.toVConstant = some env') : Good env' := by
  have hle := VEnv.addConst_le hadd
  have mono : ∀ {e}, ConstsIn (Dom env) e → ConstsIn (Dom env') e :=
    fun h => h.mono fun _ => Dom.mono hle
  obtain ⟨-, -, hTc⟩ := hci.closedN' hG.1 trivial
  obtain ⟨-, -, hT⟩ := IsDefEq.constsIn hG.2 hci nofun
  have hdf := addConst_defeqs hadd
  refine ⟨⟨fun {n ci'} h => ?_, fun {df} h => ?_⟩, ⟨fun {n ci'} h => ?_, fun {df} h => ?_⟩⟩
  · rw [addConst_constants hadd] at h; simp only at h; split at h
    · cases h; exact ⟨.zero, hTc, trivial⟩
    · exact hG.1.1 h
  · rw [hdf] at h; exact hG.1.2 h
  · rw [addConst_constants hadd] at h; simp only at h; split at h
    · cases h; exact ⟨.zero, mono hT, trivial⟩
    · obtain ⟨u, h1, h2⟩ := hG.2.1 h; exact ⟨u, mono h1, mono h2⟩
  · rw [hdf] at h; obtain ⟨⟨a, b⟩, c, d⟩ := hG.2.2 h; exact ⟨⟨mono a, mono b⟩, mono c, mono d⟩

theorem Good.addDef {env env' : VEnv} (hG : Good env) {ci : VDefVal} (hci : DefWF env ci)
    (hadd : env.addConst ci.name ci.toVConstant = some env') :
    Good (env'.addDefEq ci.toDefEq) := by
  have hG' := hG.addConst hci hadd
  have hle := VEnv.addConst_le hadd
  have mono : ∀ {e}, ConstsIn (Dom env) e → ConstsIn (Dom env') e :=
    fun h => h.mono fun _ => Dom.mono hle
  obtain ⟨hvc, -, hTc⟩ := hci.closedN' hG.1 trivial
  obtain ⟨hv, -, hT⟩ := IsDefEq.constsIn hG.2 hci nofun
  have hself : Dom env' ci.name := by
    unfold Dom; rw [VEnv.addConst_self hadd]; simp
  refine ⟨⟨hG'.1.1, fun {df} h => ?_⟩, ⟨hG'.2.1, fun {df} h => ?_⟩⟩
  · rcases h with rfl | h
    · exact ⟨⟨trivial, hTc⟩, hvc, hTc⟩
    · exact hG'.1.2 h
  · rcases h with rfl | h
    · exact ⟨⟨hself, mono hT⟩, mono hv, mono hT⟩
    · exact hG'.2.2 h

end Soulgem
