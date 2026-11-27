import Lean4Lean.Theory.Quot
import Soulgem.Sound

/-! # The quotient primitives -/

namespace Soulgem
open ConLeche ConLeche.SetTheory Lean4Lean

universe u
variable {V : Type u} [SetTheory V]

/-! ## The binder types, kept folded -/

def relTy : VExpr := .forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero))

def cTy : VExpr :=
  .forallE (.bvar 3) (.forallE (.bvar 4) (.forallE (.app (.app (.bvar 4) (.bvar 1)) (.bvar 0))
    (.app (.app (.app (.const `Eq [.param 1]) (.bvar 4)) (.app (.bvar 3) (.bvar 2)))
      (.app (.bvar 3) (.bvar 1)))))

theorem defeq_eq : quotDefEq = {
    uvars := 2
    lhs := .lam (.sort (.param 0)) (.lam relTy (.lam (.sort (.param 1))
      (.lam (.forallE (.bvar 2) (.bvar 1)) (.lam cTy (.lam (.bvar 4)
        (.app (.app (.app (.app (.app (.app (.const `Quot.lift [.param 0, .param 1]) (.bvar 5))
          (.bvar 4)) (.bvar 3)) (.bvar 2)) (.bvar 1))
          (.app (.app (.app (.const `Quot.mk [.param 0]) (.bvar 5)) (.bvar 4)) (.bvar 0))))))))
    rhs := .lam (.sort (.param 0)) (.lam relTy (.lam (.sort (.param 1))
      (.lam (.forallE (.bvar 2) (.bvar 1)) (.lam cTy (.lam (.bvar 4)
        (.app (.bvar 2) (.bvar 0)))))))
    type := .forallE (.sort (.param 0)) (.forallE relTy (.forallE (.sort (.param 1))
      (.forallE (.forallE (.bvar 2) (.bvar 1)) (.forallE cTy (.forallE (.bvar 4) (.bvar 3)))))) } :=
  rfl

/-! ## The model -/

noncomputable def relSet (α : V) : V := cpi α fun _ => cpi α fun _ => univ 0

section
variable (M : CInterp V)

theorem interp_relTy (M : CInterp V) (ls) (α : V) (ρ) : interp M ls relTy (α :: ρ) = relSet α := by
  simp [relTy, interp, relSet, VLevel.eval]

end

end Soulgem
