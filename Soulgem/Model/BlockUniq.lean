import Soulgem.Model.BlockBound
import Soulgem.Model.Level

/-! # Subsingleton elimination: `HUniq` from the large-elimination criterion -/

namespace Soulgem.BlockModel
open ConLeche ConLeche.SetTheory ConLeche.SetTheory.Tower Lean4Lean Spec BlockSem

universe u
variable {V : Type u} [SetTheory V]

theorem var_inj {d L L' : Nat} (hL : L < d) (hL' : L' < d) (h : var d L = var d L') : L = L' := by
  simp only [var, VExpr.bvar.injEq] at h; omega

theorem expr_eq (e e' : VExpr) (h : (e == e') = true) : e = e' := eq_of_beq h

theorem default_ctors : (default : SType).ctors = [] := rfl

namespace Setting
variable {M : CInterp V} {env env₁ : VEnv} {b : SBlock} (S : Setting M env env₁ b)
include S

theorem hUniq {ls : List Nat} (hl : ls.length = b.uvars) {ps : List V}
    (hps : Ext M ls b.params [] ps) (h0 : lev ls b = 0) (hlarge : b.large = true) :
    HUniq M ls b ps.reverse := by
  intro m i q q' fs fs' hB hB'
  unfold SBlock.large at hlarge
  simp only [Bool.or_eq_true] at hlarge
  rcases hlarge with hnz | hcrit
  · exact absurd h0 (VLevel.eval_ne_zero_of_isNeverZero hnz)
  obtain ⟨c, hcq, hfit, hidx⟩ := hB
  obtain ⟨c', hcq', hfit', hidx'⟩ := hB'
  split at hcrit
  · rename_i t ht
    have hm : m = 0 := by
      rcases m with _ | m
      · rfl
      · exfalso
        have e : b.types[m + 1]! = default := by
          rw [List.getElem!_eq_getElem?_getD, ht]; rfl
        simp [ctorsOf, e, default_ctors] at hcq
    subst hm
    have ht0 : b.types[0]! = t := by
      rw [List.getElem!_eq_getElem?_getD, ht]; rfl
    have hj : 0 < b.ntypes := by simp [SBlock.ntypes, ht]
    have hcmem : c ∈ (b.types[0]!).ctors := List.mem_of_getElem? hcq
    simp only [ctorsOf, ht0] at hcq hcq'
    split at hcrit
    · rename_i hnil; rw [hnil] at hcq; simp at hcq
    · rename_i c₀ hone
      rw [hone] at hcq hcq'
      have hq : q = 0 := by
        rcases q with _ | q
        · rfl
        · simp at hcq
      have hq' : q' = 0 := by
        rcases q' with _ | q'
        · rfl
        · simp at hcq'
      subst hq hq'
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hcq hcq'
      subst hcq hcq'
      refine ⟨rfl, ?_⟩
      have hl1 := hfit.length_eq
      have hl2 := hfit'.length_eq
      have hplen : ps.length = b.nparams := by rw [Ext.length_eq M ls hps]; rfl
      have hix : c₀.idx.map (interp M ls · (fs.reverse ++ ps.reverse)) =
          c₀.idx.map (interp M ls · (fs'.reverse ++ ps.reverse)) := by
        have e := hidx.trans hidx'.symm
        exact mkTower_inj (by simp) e
      refine List.ext_getElem (by rw [hl1, hl2]) fun a ha ha' => ?_
      have haf : a < c₀.fields.length := by rw [← hl1]; exact ha
      simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true] at hcrit
      rcases hcrit a haf with hz | hres
      ·
        have pt_of : ∀ gs : List V, FFit M ls (carrier M ls b ps.reverse) c₀.fields ps.reverse gs →
            (h : a < gs.length) → gs[a] = pt := by
          intro gs hg h
          have hgl := hg.length_eq
          have hpre : FFit M ls (carrier M ls b ps.reverse) (c₀.fields.take a) ps.reverse
              (gs.take a) := by
            have e1 : c₀.fields = c₀.fields.take a ++ c₀.fields.drop a :=
                (List.take_append_drop a _).symm
            have e2 : gs = gs.take a ++ gs.drop a := (List.take_append_drop a _).symm
            rw [e1, e2] at hg
            exact ((FFit.append (by simp; omega)).mp hg).1
          have hdom := S.fdom_mem hl hps carrier_mem hj hcmem haf (by simp; omega) hpre
          rw [VLevel.eval_of_isAlwaysZero hz, BlockModel.Setting.getElem!_fields haf] at hdom
          exact mem_univ_zero hdom (hg.get a haf h)
        rw [pt_of fs hfit ha, pt_of fs' hfit' ha']
      ·
        obtain ⟨y, hy, hyb⟩ := List.contains_iff_exists_mem_beq.mp hres
        have hye := expr_eq _ _ hyb
        subst hye
        rw [List.mem_append] at hy
        rcases hy with hp | hi
        · obtain ⟨i', hi', he⟩ := List.mem_map.mp hp
          rw [List.mem_range] at hi'
          have := var_inj (by omega) (by omega) he
          omega
        · obtain ⟨l, hl', he⟩ := List.mem_iff_getElem.mp hi
          have hx := congrArg (fun L => L[l]?) hix
          simp only [List.getElem?_map, List.getElem?_eq_getElem hl', he, Option.map_some,
            Option.some.injEq] at hx
          have rev : ∀ gs : List V, gs.reverse ++ ps.reverse = (ps ++ gs).reverse := by simp
          rw [rev, rev, interp_var M ls (by simp [hplen, hl1]) (by omega),
            interp_var M ls (by simp [hplen, hl2]) (by omega)] at hx
          rw [getD_append_right' (by omega), getD_append_right' (by omega)] at hx
          simpa [hplen, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ha,
            List.getElem?_eq_getElem ha'] using hx
    · simp at hcrit
  · simp at hcrit

end Setting
end Soulgem.BlockModel
