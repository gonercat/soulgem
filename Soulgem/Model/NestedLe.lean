import Soulgem.Model.NestedField

/-! # Nested blocks: auxiliary fields read as container fields -/

namespace Soulgem.Nested
open ConLeche ConLeche.SetTheory Lean4Lean Spec BlockSem BlockModel

universe u
variable {V : Type u} [SetTheory V]

section Keys
variable {M : CInterp V} {env env₁ : VEnv} {b : SBlock} (S : Setting M env env₁ b)
  {MJ : CInterp V} {envJ envJ₁ : VEnv} {r : RBlock} {lv : List VLevel} {Ds : List VExpr}

include S in
theorem keyArgs_ext (cJ : CanonR M env r MJ envJ envJ₁) {E : VEnv} {MT : CInterp V}
    (hMT : IsModel MT E) (hTenv : ∀ c, Dom env c → MT c = M c)
    (hkt : ArgsTyped E b.uvars b.params.reverse (r.b.params.map (·.instL lv)) Ds)
    {X : List Nat → List V → Nat → V}
    (hag : ∀ D ∈ Ds, ConstsIn (fun c => M₁ M b X c = MT c) D) {ls : List Nat} {ps : List V}
    (hps : Ext M ls b.params [] ps) :
    Ext MJ (lv.map (VLevel.eval ls)) r.b.params [] (Ds.map (interp (M₁ M b X) ls ·
        ps.reverse)) := by
  have SJ := cJ.setting
  rw [List.map_congr_left fun D hD => interp_congr (hag D hD) ps.reverse]
  have hsat : Sat MT ls b.params.reverse ps.reverse := by
    have := Sat.of_ext (Γ := []) (ρ := []) trivial
      ((Ext.congrM (fun c h => h) fun A hA => (S.params_consts' A hA).mono
        fun c h => (hTenv c h).symm).mp hps)
    simpa using this
  obtain ⟨hlen, hty⟩ := hkt
  refine Ext.of_get (by simp [hlen]) fun i h1 h2 => ?_
  have hi : i < Ds.length := by simpa using h2
  have hiP : i < r.b.nparams := h1
  have hmem := (hMT.sound (hty i hi (by simpa [hlen] using hi)) ls ps.reverse hsat).2
  simp only [List.getElem_map] at hmem
  have hcl : (r.b.params[i]).ClosedN (0 + i) := by
    rw [Nat.zero_add, getElem_eq_getElem! hiP]
    exact (SJ.params_scoped (P := Dom envJ₁) (fun _ h => h) hiP).1
  have e := interp_subst MT ls (argSubst (Ds.take i)) ((r.b.params[i]).instL lv)
    0 i [] ps.reverse
    (((Ds.map (interp MT ls · ps.reverse)).take i).reverse) hcl.instL rfl fun j hj => by
      have hji : j < (Ds.take i).length := by simp; omega
      rw [argSubst, dite_eq_left hji, List.getD_eq_getElem?_getD, ← List.map_take,
          ← List.map_reverse,
        List.getElem?_map, List.getElem?_eq_getElem (by simpa using hji), Option.map_some,
        Option.getD_some]
  simp only [List.nil_append] at e
  erw [e] at hmem; rw [interp_instL] at hmem
  have hc : ConstsIn (Dom envJ) r.b.params[i] := by
    rw [getElem_eq_getElem! hiP]; exact SJ.params_consts' _ (getElem!_mem' hiP)
  rw [interp_congr (hc.mono fun c h => (hTenv c (Dom.mono cJ.le h)).trans (cJ.agree c h))] at hmem
  simp only [List.getElem_map]
  rw [List.append_nil]; exact hmem

end Keys

/-! ## Keys, auxiliary members and auxiliary constructors -/

section Aux
variable {M : CInterp V} {env env₁ : VEnv} {b : SBlock} (S : Setting M env env₁ b)
  {M' : CInterp V} {env' : VEnv}
  {rec : List RBlock} {n : Nat} {tr : Translated} {a : Aux} {J : Name} {lv : List VLevel}
  {Ds : List VExpr} {r : RBlock} {m d : Nat}

include S in
theorem key_closed (cJ : CanonR M' env' r MJ envJ envJ₁)
    (hs : Slot rec n tr b nuser fams a J lv Ds r m d) {E : VEnv} (hGE : Good E)
    (hkt : ArgsTyped E b.uvars b.params.reverse (r.b.params.map (·.instL lv)) Ds) :
    a.key.ClosedN b.nparams := by
  obtain ⟨k, -, he, hc, -⟩ := hs.read cJ
  have hD : ∀ D ∈ Ds, D.ClosedN b.nparams := fun D hD => by
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hD
    have := ((hkt.2 i hi (by simpa [hkt.1] using hi)).closedN' hGE.1 S.params_ctx_closed).1
    rwa [List.length_reverse] at this
  refine EqL.closedN he ?_
  unfold atKey
  have := closedN_subst (f := argSubst Ds) (N := Ds.length) (n := b.nparams) (k := 0)
    (fun i hi => by
        unfold argSubst; rw [dite_eq_left hi]; exact hD _ (List.mem_reverse.mp
            (List.getElem_mem _)))
    (e := k.instL lv) (by rw [Nat.zero_add, hs.nDs]; exact hc.instL)
  simpa using this

end Aux

/-! ## Restore-safety of the auxiliary constructor fields -/

theorem restoreSafe_forallTel (ns ms : List Name) (us : List VLevel) (n : Nat) :
    ∀ (As : List VExpr) (X : VExpr) (d : Nat), restoreSafe ns ms us n
        (Spec.forallTel As X) d = true →
      (∀ k < As.length, restoreSafe ns ms us n As[k]! (d + k) = true) ∧
        restoreSafe ns ms us n X (d + As.length) = true
  | [], X, d, h => ⟨fun k hk => absurd hk (by simp), by simpa [Spec.forallTel] using h⟩
  | A :: As, X, d, h => by
    simp only [Spec.forallTel, restoreSafe, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := restoreSafe_forallTel ns ms us n As X (d + 1) h.2
    refine ⟨fun k hk => ?_, by simpa [Nat.add_assoc, Nat.add_comm 1] using h2⟩
    cases k with
    | zero => simpa using h.1
    | succ k =>
      have := h1 k (by simpa using hk)
      simpa [Nat.add_assoc, Nat.add_comm 1] using this

theorem restoreSafeTop_forallTel (ns ms : List Name) (us : List VLevel) (n : Nat) :
    ∀ (Ps : List VExpr) (X : VExpr) (d : Nat),
      restoreSafeTop.go ns ms us n Ps.length (Spec.forallTel Ps X) d = true →
        restoreSafe ns ms us n X (d + Ps.length) = true
  | [], X, d, h => by simpa [restoreSafeTop.go, Spec.forallTel] using h
  | P :: Ps, X, d, h => by
    simp only [Spec.forallTel, List.length_cons, restoreSafeTop.go, Bool.and_eq_true] at h
    have := restoreSafeTop_forallTel ns ms us n Ps X (d + 1) h.2
    simpa [Nat.add_assoc, Nat.add_comm 1] using this

end Soulgem.Nested
