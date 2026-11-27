import Soulgem.Model.BlockOp
import Soulgem.Model.Level
import Soulgem.Model.Subst

/-! # Placed fragments -/

namespace Soulgem
open Lean4Lean Spec

namespace Spec
theorem remap_bvar (g : Nat → Nat) (i k : Nat) : ∃ j, remap g (.bvar i) k = .bvar j := by
  simp only [remap]; split
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩
theorem consumeAnn_remap (g : Nat → Nat) (k : Nat) (e : VExpr) :
    consumeAnn (remap g e k) = remap g (consumeAnn e) k := by
  fun_induction consumeAnn e <;> try simp_all [remap, consumeAnn]
  rename_i e h1 h2 h3 h4
  rcases e with i | _ | ⟨c, us⟩ | ⟨f, a⟩ | _ | _
  · obtain ⟨j, hj⟩ := remap_bvar g i k; rw [hj]; simp [consumeAnn]
  · simp [remap, consumeAnn]
  · simp [remap, consumeAnn]
  · rcases f with i | _ | ⟨c, us⟩ | ⟨f1, a1⟩ | _ | _
    · obtain ⟨j, hj⟩ := remap_bvar g i k
      have e1 : consumeAnn (.app (.bvar j) (remap g a k)) = .app (.bvar j) (remap g a k) := by
        simp [consumeAnn]
      have e2 : consumeAnn (.app (.bvar i) a) = .app (.bvar i) a := by simp [consumeAnn]
      show consumeAnn (.app (remap g (.bvar i) k) (remap g a k)) =
          remap g (consumeAnn (.app (.bvar i) a)) k
      rw [hj, e1, e2]; show _ = VExpr.app (remap g (.bvar i) k) (remap g a k); rw [hj]
    · simp [remap, consumeAnn]
    · have ho : c ≠ ``outParam := fun e => h3 us a (by rw [e])
      have hs : c ≠ ``semiOutParam := fun e => h4 us a (by rw [e])
      simp [remap, consumeAnn.eq_def, ho, hs]
    · rcases f1 with i | _ | ⟨c, us⟩ | _ | _ | _
      · obtain ⟨j, hj⟩ := remap_bvar g i k
        have e1 : consumeAnn (.app (.app (.bvar j) (remap g a1 k)) (remap g a k)) =
            .app (.app (.bvar j) (remap g a1 k)) (remap g a k) := by simp [consumeAnn]
        have e2 : consumeAnn (.app (.app (.bvar i) a1) a) = .app (.app (.bvar i) a1) a := by
          simp [consumeAnn]
        show consumeAnn (.app (.app (remap g (.bvar i) k) (remap g a1 k)) (remap g a k)) =
          remap g (consumeAnn (.app (.app (.bvar i) a1) a)) k
        rw [hj, e1, e2]
        show _ = VExpr.app (.app (remap g (.bvar i) k) (remap g a1 k)) (remap g a k); rw [hj]
      · simp [remap, consumeAnn]
      · have ho : c ≠ ``optParam := fun e => h1 us a1 a (by rw [e])
        have hs : c ≠ ``autoParam := fun e => h2 us a1 a (by rw [e])
        simp [remap, consumeAnn.eq_def, ho, hs]
      all_goals simp [remap, consumeAnn]
    · simp [remap, consumeAnn]
    · simp [remap, consumeAnn]
  · simp [remap, consumeAnn]
  · simp [remap, consumeAnn]
theorem consumeAnn_instL (us₀ : List VLevel) (e : VExpr) :
    consumeAnn (e.instL us₀) = (consumeAnn e).instL us₀ := by
  fun_induction consumeAnn e <;> try simp_all [VExpr.instL, consumeAnn]
  rename_i e h1 h2 h3 h4
  rcases e with i | _ | ⟨c, us⟩ | ⟨f, a⟩ | _ | _
  · simp [VExpr.instL, consumeAnn]
  · simp [VExpr.instL, consumeAnn]
  · simp [VExpr.instL, consumeAnn]
  · rcases f with i | _ | ⟨c, us⟩ | ⟨f1, a1⟩ | _ | _
    · simp [VExpr.instL, consumeAnn]
    · simp [VExpr.instL, consumeAnn]
    · have ho : c ≠ ``outParam := fun e => h3 us a (by rw [e])
      have hs : c ≠ ``semiOutParam := fun e => h4 us a (by rw [e])
      simp [VExpr.instL, consumeAnn.eq_def, ho, hs]
    · rcases f1 with i | _ | ⟨c, us⟩ | _ | _ | _
      · simp [VExpr.instL, consumeAnn]
      · simp [VExpr.instL, consumeAnn]
      · have ho : c ≠ ``optParam := fun e => h1 us a1 a (by rw [e])
        have hs : c ≠ ``autoParam := fun e => h2 us a1 a (by rw [e])
        simp [VExpr.instL, consumeAnn.eq_def, ho, hs]
      all_goals simp [VExpr.instL, consumeAnn]
    · simp [VExpr.instL, consumeAnn]
    · simp [VExpr.instL, consumeAnn]
  · simp [VExpr.instL, consumeAnn]
  · simp [VExpr.instL, consumeAnn]

theorem consumeAnn_place (d0 : Nat) (σ : Nat → Nat) (d : Nat) (e : VExpr) :
    consumeAnn (place d0 σ d e) = place d0 σ d (consumeAnn e) :=
  consumeAnn_remap _ 0 e

end Spec

namespace BlockModel
open ConLeche ConLeche.SetTheory BlockSem

universe u
variable {V : Type u} [SetTheory V]

theorem interp_sh_place (M' : CInterp V) (ls' : List Nat) (b : SBlock) (d0 : Nat) (σ : Nat → Nat)
    (d : Nat) (e : VExpr) (xs : List V) (hc : e.ClosedN d0) (hd : xs.length = d)
    (hσ : ∀ L < d0, σ L < d) :
    interp M' ls' (b.sh (place d0 σ d e)) xs.reverse =
      interp M' (b.blockLevels.map (VLevel.eval ls')) e
        ((List.range d0).map fun L => xs.getD (σ L) pt).reverse := by
  unfold SBlock.sh
  rw [interp_instL, interp_place _ _ d0 σ d e xs hc hd hσ]

theorem interp_binder_place {M' : CInterp V} {env : VEnv} (hM : IsModel M' env)
    (hcl : env.OnTypes fun _ e A => e.ClosedN ∧ A.ClosedN)
    (ls' : List Nat) (b : SBlock) {U : Nat} {Γ0 : List VExpr} (hΓ : CtxClosed Γ0)
    (d0 : Nat) (hd0 : Γ0.length = d0) (σ : Nat → Nat) (d : Nat) (e : VExpr)
    (hann : AnnOK env U Γ0 e) (xs : List V) (hd : xs.length = d) (hσ : ∀ L < d0, σ L < d)
    (hsat : Sat M' (b.blockLevels.map (VLevel.eval ls')) Γ0
      ((List.range d0).map fun L => xs.getD (σ L) pt).reverse) :
    interp M' ls' (b.binder (place d0 σ d e)) xs.reverse =
      interp M' (b.blockLevels.map (VLevel.eval ls')) e
        ((List.range d0).map fun L => xs.getD (σ L) pt).reverse := by
  obtain ⟨_, hdf⟩ := hann
  have hcl' := (hdf.closedN' hcl hΓ)
  unfold SBlock.binder SBlock.sh
  rw [consumeAnn_instL, consumeAnn_place, interp_instL,
    interp_place _ _ d0 σ d _ xs (hd0 ▸ hcl'.2.1) hd hσ]
  exact ((hM.sound hdf _ _ hsat).1).symm

end BlockModel
end Soulgem
