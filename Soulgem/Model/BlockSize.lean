import Soulgem.Model.BlockFit

/-! # The operator's size hypotheses from the specification -/

namespace Soulgem.BlockModel
open ConLeche ConLeche.SetTheory ConLeche.SetTheory.Tower Lean4Lean Spec BlockSem

universe u
variable {V : Type u} [SetTheory V]

variable (M : CInterp V) (b : SBlock) in
noncomputable def patch (ls₀ : List Nat) (ρ₀ : List V) (X : Nat → V) :
    List Nat → List V → Nat → V :=
  open Classical in fun ls ρ => if ls = ls₀ ∧ ρ = ρ₀ then X else carrier M ls b ρ

theorem patch_at {M : CInterp V} {b : SBlock} {ls₀ : List Nat} {ρ₀ : List V} {X : Nat → V} :
    patch M b ls₀ ρ₀ X ls₀ ρ₀ = X := by
  simp [patch]

theorem patch_tupleFn {M : CInterp V} {b : SBlock} {ls₀ : List Nat} {ρ₀ : List V} {X : Nat → V}
    (hX : InTupleSpace (lev ls₀ b) b.ntypes (Is M ls₀ b ρ₀) X) :
        TupleFn M b (patch M b ls₀ ρ₀ X) := by
  intro ls ρ
  by_cases h : ls = ls₀ ∧ ρ = ρ₀
  · obtain ⟨rfl, rfl⟩ := h; rw [patch_at]; exact hX
  · simp only [patch, ite_eq_right h]; exact carrier_mem

namespace Setting
variable {M : CInterp V} {env env₁ : VEnv} {b : SBlock} (S : Setting M env env₁ b)
include S

theorem hK : HK b := by
  intro m hm c hc f hf xs k idx hcert
  obtain ⟨a, ha, rfl⟩ := List.mem_iff_getElem.mp hf
  have hok := S.field_full hm hc ha
  have eget : c.fields[a]! = c.fields[a] := by
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem ha]; rfl
  rw [eget] at hok
  unfold Setting.FieldFull at hok
  rw [hcert] at hok
  exact hok.1

theorem fdom_mem {ls : List Nat} (hl : ls.length = b.uvars) {ps : List V}
    (hps : Ext M ls b.params [] ps) {X : Nat → V}
    (hX : InTupleSpace (lev ls b) b.ntypes (Is M ls b ps.reverse) X)
    {j : Nat} (hj : j < b.ntypes) {c : SCtor} (hc : c ∈ (b.types[j]!).ctors)
    {a : Nat} (ha : a < c.fields.length) {fs : List V} (hfs : fs.length = a)
    (hfit : FFit M ls X (c.fields.take a) ps.reverse fs) :
    fdom M ls X (c.fields[a]!) (fs.reverse ++ ps.reverse) ∈ˢ
      (univ ((c.fields[a]!).sort.eval ls) : V) := by
  have hC := patch_tupleFn (M := M) (b := b) hX
  have hsat := (S.ffit_iff_sat hC hl hj hc hps a (Nat.le_of_lt ha) fs hfs).mp
    (by rw [patch_at]; exact hfit)
  have hplen : ps.length = b.nparams := by rw [Ext.length_eq M ls hps]; rfl
  have e := S.interp_field hC hl hj hc ha (zs := ps ++ fs) (by simp [hplen, hfs])
    (by simpa using hsat) (by rw [List.take_append_of_le_length (by omega),
      List.take_of_length_le (by omega)]; exact hps)
  rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega), patch_at,
    List.reverse_append] at e
  rw [← e]
  have := ((S.model₁ hC).1.sound (S.field_ok hj hc ha).1 ls _ hsat).2
  simpa [interp] using this

theorem sort_le {ls : List Nat} (h0 : lev ls b ≠ 0) {j : Nat} (hj : j < b.ntypes) {c : SCtor}
    (hc : c ∈ (b.types[j]!).ctors) {a : Nat} (ha : a < c.fields.length) :
    (c.fields[a]!).sort.eval ls ≤ lev ls b := by
  rcases (S.field_ok hj hc ha).2.2.1 with hz | hle
  · exact absurd (VLevel.eval_of_isAlwaysZero hz) h0
  · exact hle ls

theorem hSmall {ls : List Nat} (hl : ls.length = b.uvars) {ps : List V}
    (hps : Ext M ls b.params [] ps) : HSmall M ls b ps.reverse := by
  intro h0 X hX m hm c hc
  have key : ∀ r a, a + r = c.fields.length → ∀ fs : List V, fs.length = a →
      FFit M ls X (c.fields.take a) ps.reverse fs →
      BoundS (lev ls b) (telF M ls X (c.fields.drop a) (fs.reverse ++ ps.reverse)) := by
    intro r
    induction r with
    | zero =>
      intro a ha fs _ _
      rw [List.drop_eq_nil_of_le (by omega)]; trivial
    | succ r ih =>
      intro a ha fs hfs hfit
      have hlt : a < c.fields.length := by omega
      rw [List.drop_eq_getElem_cons hlt]
      have eget : c.fields[a]! = c.fields[a] := by
        rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hlt]; rfl
      refine ⟨?_, fun x hx => ?_⟩
      · have := S.fdom_mem hl hps hX hm hc hlt hfs hfit
        rw [eget] at this
        exact univ_mono (eget ▸ S.sort_le h0 hm hc hlt) _ this
      · have h' := ih (a + 1) (by omega) (fs ++ [x]) (by simp [hfs])
          (by
            rw [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some,
              FFit.append (by simp [hfs, Nat.min_eq_left (Nat.le_of_lt hlt)]), FFit.single]
            exact ⟨hfit, hx⟩)
        simpa using h'
  exact key c.fields.length 0 (by simp) [] rfl .nil

end Setting
end Soulgem.BlockModel
