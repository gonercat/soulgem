import Soulgem.Model.BlockIota
import Soulgem.Model.NestedLe

/-! # Restoration of whole declarations -/

namespace Soulgem.Nested
open ConLeche ConLeche.SetTheory ConLeche.SetTheory.Tower Lean4Lean Spec BlockSem BlockModel

universe u
variable {V : Type u} [SetTheory V]

theorem lamTel_append : ∀ (As Bs : List VExpr) (X : VExpr),
    Spec.lamTel (As ++ Bs) X = Spec.lamTel As (Spec.lamTel Bs X)
  | [], _, _ => rfl
  | A :: As, Bs, X => by simp only [List.cons_append, Spec.lamTel, lamTel_append As Bs X]

theorem restore_strip_lam : ∀ (As : List VExpr) (X : VExpr),
    Translated.restore.strip As.length (Spec.lamTel As X) = (As, X)
  | [], _ => by simp [Translated.restore.strip, Spec.lamTel]
  | A :: As, X => by simp [Spec.lamTel, Translated.restore.strip, restore_strip_lam As X]

theorem restore_lamTel {tr : Translated} {auxRec : List (Name × Name)} {n : Nat}
    (As : List VExpr) (X : VExpr) (h : As.length = n) :
    tr.restore auxRec n (Spec.lamTel As X) = Spec.lamTel As (tr.restoreBody auxRec n X n) := by
  subst h
  unfold Translated.restore
  rw [restore_strip_lam]
  cases As with
  | nil => simp only [Spec.lamTel, Spec.forallTel]; split <;> rfl
  | cons A As => simp only [Spec.lamTel]

theorem restoreSafeTop_tel (ns ms : List Name) (us : List VLevel) (n : Nat) (lam : Bool) :
    ∀ (Ps : List VExpr) (X : VExpr) (d : Nat),
      restoreSafeTop.go ns ms us n Ps.length
        (if lam then Spec.lamTel Ps X else Spec.forallTel Ps X) d = true →
        (∀ P ∈ Ps, mentions ms P = false) ∧ restoreSafe ns ms us n X (d + Ps.length) = true
  | [], X, d, h => by cases lam <;> simpa [restoreSafeTop.go, Spec.forallTel, Spec.lamTel] using h
  | P :: Ps, X, d, h => by
    have h' : !mentions ms P && restoreSafeTop.go ns ms us n Ps.length
        (if lam then Spec.lamTel Ps X else Spec.forallTel Ps X) (d + 1) = true := by
      cases lam <;> simpa [Spec.forallTel, Spec.lamTel, restoreSafeTop.go] using h
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h'
    obtain ⟨hP, hPs⟩ := restoreSafeTop_tel ns ms us n lam Ps X (d + 1) h'.2
    refine ⟨fun Q hQ => ?_, by simpa [Nat.add_assoc, Nat.add_comm 1] using hPs⟩
    rcases List.mem_cons.mp hQ with rfl | hQ
    · exact h'.1
    · exact hP Q hQ

section
variable {M M' : CInterp V} {ls : List Nat} {tr : Translated} {auxRec : List (Name × Name)}
  {ns ms : List Name} {us : List VLevel} {n : Nat} {Q : List V → Prop}

theorem RestoreHyp.interp_restore_tel (H : RestoreHyp M M' ls tr auxRec ns ms us n Q) (lam : Bool)
    (As : List VExpr) (X : VExpr) (hn : As.length = n)
    (hs : restoreSafeTop ns ms us n (if lam then Spec.lamTel As X else Spec.forallTel As X) = true)
    (hQ : ∀ ys, Ext M ls As [] ys → Q ys) :
    interp M' ls (tr.restore auxRec n (if lam then Spec.lamTel As X else Spec.forallTel As X)) [] =
      interp M ls (if lam then Spec.lamTel As X else Spec.forallTel As X) [] := by
  have hs' := restoreSafeTop_tel ns ms us n lam As X 0 (by
      unfold restoreSafeTop at hs; rw [hn]; exact hs)
  rw [Nat.zero_add, hn] at hs'
  have hpt : ∀ i (h : i < As.length) (h' : i < As.length) (ys : List V),
      Ext M ls (As.take i) [] ys →
      interp M' ls As[i] (ys.reverse ++ []) = interp M ls As[i] (ys.reverse ++ []) :=
    fun i h _ ys _ => (H.interp_free (hs'.1 _ (List.getElem_mem h)) _).symm
  have hbody : ∀ ys, Ext M ls As [] ys →
      interp M' ls (tr.restoreBody auxRec n X n) (ys.reverse ++ []) =
          interp M ls X (ys.reverse ++ []) := by
    intro ys hys
    have hyl : ys.length = n := by rw [Ext.length_eq _ _ hys, hn]
    refine H.interp_restoreBody X (Nat.le_refl _) (by simp [hyl]) ?_ hs'.2
    rw [List.append_nil, List.reverse_reverse, List.take_of_length_le (by omega)]
    exact hQ ys hys
  cases lam with
  | true =>
    simp only [ite_true] at *
    rw [restore_lamTel As X hn, interp_lamTel', interp_lamTel']
    exact lamTel_transfer rfl hpt hbody
  | false =>
    simp only [Bool.false_eq_true, ite_false] at *
    rw [restore_forallTel tr auxRec n As X hn, interp_forallTel, interp_forallTel]
    exact piTel_transfer rfl hpt hbody

end
end Soulgem.Nested
