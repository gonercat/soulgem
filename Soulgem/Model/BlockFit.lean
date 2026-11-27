import Soulgem.Model.BlockSetting

/-! # Fitting fields and satisfied contexts -/

namespace Soulgem.BlockModel
open ConLeche ConLeche.SetTheory ConLeche.SetTheory.Tower Lean4Lean Spec BlockSem

universe u
variable {V : Type u} [SetTheory V]

theorem _root_.Lean4Lean.VLevel.eval_of_isAlwaysZero {ls : List Nat} {l : VLevel}
    (h : l.isAlwaysZero = true) : l.eval ls = 0 := by
  induction l with
  | zero => rfl
  | param _ | succ _ => simp [VLevel.isAlwaysZero] at h
  | max a b iha ihb =>
    simp only [VLevel.isAlwaysZero, Bool.and_eq_true] at h
    simp [VLevel.eval, iha h.1, ihb h.2]
  | imax a b _ ihb =>
    simp only [VLevel.isAlwaysZero] at h
    simp [VLevel.eval, ihb h, Lean.Nat.imax]

theorem interp_eq_of_agree {M : CInterp V} {ls : List Nat} :
    ∀ (e : VExpr) {ρ ρ' : List V}, (∀ i, SBlock.hasVar e i = true → ρ.getD i pt = ρ'.getD i pt) →
    interp M ls e ρ = interp M ls e ρ'
  | .bvar j, ρ, ρ', h => h j (by simp [SBlock.hasVar])
  | .sort _, _, _, _ => rfl
  | .const _ _, _, _, _ => rfl
  | .app f a, ρ, ρ', h => by
    simp only [interp]
    rw [interp_eq_of_agree f fun i hi => h i (by simp [SBlock.hasVar, hi]),
      interp_eq_of_agree a fun i hi => h i (by simp [SBlock.hasVar, hi])]
  | .lam A b, ρ, ρ', h => by
    simp only [interp]
    rw [interp_eq_of_agree A fun i hi => h i (by simp [SBlock.hasVar, hi])]
    congr 1; funext x
    refine interp_eq_of_agree b fun i hi => ?_
    cases i with
    | zero => rfl
    | succ i => exact h i (by simp [SBlock.hasVar, hi])
  | .forallE A b, ρ, ρ', h => by
    simp only [interp]
    rw [interp_eq_of_agree A fun i hi => h i (by simp [SBlock.hasVar, hi])]
    congr 1; funext x
    refine interp_eq_of_agree b fun i hi => ?_
    cases i with
    | zero => rfl
    | succ i => exact h i (by simp [SBlock.hasVar, hi])

theorem FFit.append {M : CInterp V} {ls : List Nat} {X : Nat → V} :
    ∀ {L1 L2 : List SField} {ρ xs1 xs2 : List V}, xs1.length = L1.length →
    (FFit M ls X (L1 ++ L2) ρ (xs1 ++ xs2) ↔
      FFit M ls X L1 ρ xs1 ∧ FFit M ls X L2 (xs1.reverse ++ ρ) xs2)
  | [], L2, ρ, [], xs2, _ => by simp; exact fun _ => .nil
  | [], _, _, _ :: _, _, hl => by simp at hl
  | _ :: _, _, _, [], _, hl => by simp at hl
  | f :: L1, L2, ρ, x :: xs1, xs2, hl => by
    have ih := FFit.append (M := M) (ls := ls) (X := X) (L1 := L1) (L2 := L2) (ρ := x :: ρ)
        (xs1 := xs1) (xs2 := xs2)
      (by simpa using hl)
    constructor
    · intro h
      cases h with
      | cons hx h =>
        obtain ⟨h1, h2⟩ := ih.mp h
        exact ⟨.cons hx h1, by simpa using h2⟩
    · intro ⟨h1, h2⟩
      cases h1 with
      | cons hx h1 => exact .cons hx (ih.mpr ⟨h1, by simpa using h2⟩)

theorem FFit.single {M : CInterp V} {ls : List Nat} {X : Nat → V} {f : SField}
    {ρ : List V} {x : V} : FFit M ls X [f] ρ [x] ↔ x ∈ˢ fdom M ls X f ρ :=
  ⟨fun | .cons h .nil => h, fun h => .cons h .nil⟩

namespace Setting
variable {M : CInterp V} {env env₁ : VEnv} {b : SBlock} (S : Setting M env env₁ b)
include S

theorem ffit_iff_sat {C : List Nat → List V → Nat → V} (hC : TupleFn M b C) {ls : List Nat}
    (hl : ls.length = b.uvars) {j : Nat} (hj : j < b.ntypes) {c : SCtor}
    (hc : c ∈ (b.types[j]!).ctors) {ps : List V} (hps : Ext M ls b.params [] ps) :
    ∀ a ≤ c.fields.length, ∀ fs : List V, fs.length = a →
      (FFit M ls (C ls ps.reverse) (c.fields.take a) ps.reverse fs ↔
        Sat (M₁ M b C) ls (fctx b c a) (fs.reverse ++ ps.reverse)) := by
  have hpsat : Sat (M₁ M b C) ls b.params.reverse ps.reverse := by
    have := Sat.of_ext (Γ := []) (ρ := []) trivial
      ((Ext.congrM (fun _ h => h) fun A hA => (S.free₀ (C := C) (S.params_consts' A hA)).mono
        fun _ h => h.symm).mp hps)
    simpa using this
  have hplen : ps.length = b.nparams := by rw [Ext.length_eq M ls hps]; rfl
  intro a
  induction a with
  | zero =>
    intro _ fs hfs
    cases fs with
    | nil => simp only [List.take_zero, fctx, List.map_nil, List.append_nil, List.reverse_nil,
        List.nil_append]; exact ⟨fun _ => hpsat, fun _ => .nil⟩
    | cons => simp at hfs
  | succ a ih =>
    intro ha fs hfs
    have hlt : a < c.fields.length := by omega
    obtain ⟨fs', x, rfl⟩ : ∃ fs' x, fs = fs' ++ [x] := by
      refine ⟨fs.take a, fs[a]'(by omega), ?_⟩
      conv => lhs; rw [← List.take_append_drop a fs]
      congr 1
      rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_nil_of_le (by omega)]
    have hfs' : fs'.length = a := by simpa using hfs
    rw [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some,
      FFit.append (by simp [hfs', Nat.min_eq_left (Nat.le_of_lt hlt)]), FFit.single,
          ih (by omega) fs' hfs']
    have hctx : fctx b c (a + 1) = (c.fields[a]).ty :: fctx b c a := by
      unfold fctx
      rw [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some, List.map_append,
        ← List.append_assoc, List.reverse_append]
      rfl
    rw [hctx, List.reverse_append]
    show _ ↔ Sat (M₁ M b C) ls (fctx b c a) (fs'.reverse ++ ps.reverse) ∧
      x ∈ˢ interp (M₁ M b C) ls (c.fields[a]).ty (fs'.reverse ++ ps.reverse)
    constructor
    · intro ⟨hs, hx⟩
      refine ⟨hs, ?_⟩
      have e := S.interp_field hC hl hj hc hlt (zs := ps ++ fs') (by simp [hplen, hfs'])
        (by simpa using hs) (by rw [List.take_append_of_le_length (by omega),
          List.take_of_length_le (by omega)]; exact hps)
      rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)] at e
      have eget : c.fields[a]! = c.fields[a] := by
        rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hlt]; rfl
      rw [eget] at e
      simp only [List.reverse_append] at e
      rw [e]; exact hx
    · intro ⟨hs, hx⟩
      refine ⟨hs, ?_⟩
      have e := S.interp_field hC hl hj hc hlt (zs := ps ++ fs') (by simp [hplen, hfs'])
        (by simpa using hs) (by rw [List.take_append_of_le_length (by omega),
          List.take_of_length_le (by omega)]; exact hps)
      rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)] at e
      have eget : c.fields[a]! = c.fields[a] := by
        rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hlt]; rfl
      rw [eget] at e
      simp only [List.reverse_append] at e
      rw [← e]; exact hx

end Setting
end Soulgem.BlockModel
