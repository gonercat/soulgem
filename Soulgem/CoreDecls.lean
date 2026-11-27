import Soulgem.Tel

/-! # Declarations of Lean's core logic -/

namespace Soulgem.Core
open Lean4Lean Soulgem

def Eq_ty : VExpr :=
  (.forallE (.sort (.param 0)) (.forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero))))

def Eq_c : VConstVal := { uvars := 1, type := Eq_ty, name := `Eq }

def Eq_tel : List VExpr :=
  [(.sort (.param 0)),
    (.bvar 0),
    (.bvar 1)]

def Eq_res : VExpr := (.sort .zero)

theorem Eq_ty_eq : Eq_ty = forallTel Eq_tel Eq_res := rfl

def Eq_refl_ty : VExpr :=
  (.forallE (.sort (.param 0)) (.forallE (.bvar 0) (.app (.app
      (.app (.const `Eq [(.param 0)]) (.bvar 1)) (.bvar 0)) (.bvar 0))))

def Eq_refl_c : VConstVal := { uvars := 1, type := Eq_refl_ty, name := `Eq.refl }

def Eq_refl_tel : List VExpr :=
  [(.sort (.param 0)),
    (.bvar 0)]

def Eq_refl_res : VExpr := (.app (.app (.app (.const `Eq [(.param 0)]) (.bvar 1))
    (.bvar 0)) (.bvar 0))

theorem Eq_refl_ty_eq : Eq_refl_ty = forallTel Eq_refl_tel Eq_refl_res := rfl

def Eq_rec_ty : VExpr :=
  (.forallE (.sort (.param 1)) (.forallE (.bvar 0) (.forallE (.forallE (.bvar 1)
      (.forallE (.app (.app (.app (.const `Eq [(.param 1)]) (.bvar 2)) (.bvar 1)) (.bvar 0))
      (.sort (.param 0)))) (.forallE (.app (.app (.bvar 0) (.bvar 1))
      (.app (.app (.const `Eq.refl [(.param 1)]) (.bvar 2)) (.bvar 1)))
      (.forallE (.bvar 3) (.forallE (.app (.app (.app (.const `Eq [(.param 1)]) (.bvar 4))
      (.bvar 3)) (.bvar 0)) (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0))))))))

def Eq_rec_c : VConstVal := { uvars := 2, type := Eq_rec_ty, name := `Eq.rec }

def Eq_rec_tel : List VExpr :=
  [(.sort (.param 1)),
    (.bvar 0),
    (.forallE (.bvar 1) (.forallE (.app (.app (.app (.const `Eq [(.param 1)]) (.bvar 2)) (.bvar 1))
        (.bvar 0)) (.sort (.param 0)))),
    (.app (.app (.bvar 0) (.bvar 1)) (.app (.app (.const `Eq.refl [(.param 1)]) (.bvar 2))
        (.bvar 1))),
    (.bvar 3),
    (.app (.app (.app (.const `Eq [(.param 1)]) (.bvar 4)) (.bvar 3)) (.bvar 0))]

def Eq_rec_res : VExpr := (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0))

theorem Eq_rec_ty_eq : Eq_rec_ty = forallTel Eq_rec_tel Eq_rec_res := rfl

def Iff_ty : VExpr :=
  (.forallE (.sort .zero) (.forallE (.sort .zero) (.sort .zero)))

def Iff_c : VConstVal := { uvars := 0, type := Iff_ty, name := `Iff }

def Iff_tel : List VExpr :=
  [(.sort .zero),
    (.sort .zero)]

def Iff_res : VExpr := (.sort .zero)

theorem Iff_ty_eq : Iff_ty = forallTel Iff_tel Iff_res := rfl

def Iff_intro_ty : VExpr :=
  (.forallE (.sort .zero) (.forallE (.sort .zero) (.forallE (.forallE (.bvar 1) (.bvar 1))
      (.forallE (.forallE (.bvar 1) (.bvar 3)) (.app (.app (.const `Iff []) (.bvar 3))
      (.bvar 2))))))

def Iff_intro_c : VConstVal := { uvars := 0, type := Iff_intro_ty, name := `Iff.intro }

def Iff_intro_tel : List VExpr :=
  [(.sort .zero),
    (.sort .zero),
    (.forallE (.bvar 1) (.bvar 1)),
    (.forallE (.bvar 1) (.bvar 3))]

def Iff_intro_res : VExpr := (.app (.app (.const `Iff []) (.bvar 3)) (.bvar 2))

theorem Iff_intro_ty_eq : Iff_intro_ty = forallTel Iff_intro_tel Iff_intro_res := rfl

def Iff_rec_ty : VExpr :=
  (.forallE (.sort .zero) (.forallE (.sort .zero) (.forallE (.forallE
      (.app (.app (.const `Iff []) (.bvar 1)) (.bvar 0)) (.sort (.param 0)))
      (.forallE (.forallE (.forallE (.bvar 2) (.bvar 2)) (.forallE (.forallE (.bvar 2) (.bvar 4))
      (.app (.bvar 2) (.app (.app (.app (.app (.const `Iff.intro []) (.bvar 4)) (.bvar 3))
      (.bvar 1)) (.bvar 0))))) (.forallE (.app (.app (.const `Iff []) (.bvar 3)) (.bvar 2))
      (.app (.bvar 2) (.bvar 0)))))))

def Iff_rec_c : VConstVal := { uvars := 1, type := Iff_rec_ty, name := `Iff.rec }

def Iff_rec_tel : List VExpr :=
  [(.sort .zero),
    (.sort .zero),
    (.forallE (.app (.app (.const `Iff []) (.bvar 1)) (.bvar 0)) (.sort (.param 0))),
    (.forallE (.forallE (.bvar 2) (.bvar 2)) (.forallE (.forallE (.bvar 2) (.bvar 4))
        (.app (.bvar 2) (.app (.app (.app (.app (.const `Iff.intro []) (.bvar 4)) (.bvar 3))
        (.bvar 1)) (.bvar 0))))),
    (.app (.app (.const `Iff []) (.bvar 3)) (.bvar 2))]

def Iff_rec_res : VExpr := (.app (.bvar 2) (.bvar 0))

theorem Iff_rec_ty_eq : Iff_rec_ty = forallTel Iff_rec_tel Iff_rec_res := rfl

def Nonempty_ty : VExpr :=
  (.forallE (.sort (.param 0)) (.sort .zero))

def Nonempty_c : VConstVal := { uvars := 1, type := Nonempty_ty, name := `Nonempty }

def Nonempty_tel : List VExpr :=
  [(.sort (.param 0))]

def Nonempty_res : VExpr := (.sort .zero)

theorem Nonempty_ty_eq : Nonempty_ty = forallTel Nonempty_tel Nonempty_res := rfl

def Nonempty_intro_ty : VExpr :=
  (.forallE (.sort (.param 0)) (.forallE (.bvar 0) (.app (.const `Nonempty [(.param 0)])
      (.bvar 1))))

def Nonempty_intro_c : VConstVal :=
    { uvars := 1, type := Nonempty_intro_ty, name := `Nonempty.intro }

def Nonempty_intro_tel : List VExpr :=
  [(.sort (.param 0)),
    (.bvar 0)]

def Nonempty_intro_res : VExpr := (.app (.const `Nonempty [(.param 0)]) (.bvar 1))

theorem Nonempty_intro_ty_eq : Nonempty_intro_ty = forallTel Nonempty_intro_tel
    Nonempty_intro_res := rfl

def Nonempty_rec_ty : VExpr :=
  (.forallE (.sort (.param 0)) (.forallE (.forallE (.app (.const `Nonempty [(.param 0)]) (.bvar 0))
      (.sort .zero)) (.forallE (.forallE (.bvar 1) (.app (.bvar 1)
      (.app (.app (.const `Nonempty.intro [(.param 0)]) (.bvar 2)) (.bvar 0))))
      (.forallE (.app (.const `Nonempty [(.param 0)]) (.bvar 2)) (.app (.bvar 2) (.bvar 0))))))

def Nonempty_rec_c : VConstVal := { uvars := 1, type := Nonempty_rec_ty, name := `Nonempty.rec }

def Nonempty_rec_tel : List VExpr :=
  [(.sort (.param 0)),
    (.forallE (.app (.const `Nonempty [(.param 0)]) (.bvar 0)) (.sort .zero)),
    (.forallE (.bvar 1) (.app (.bvar 1) (.app (.app (.const `Nonempty.intro [(.param 0)]) (.bvar 2))
        (.bvar 0)))),
    (.app (.const `Nonempty [(.param 0)]) (.bvar 2))]

def Nonempty_rec_res : VExpr := (.app (.bvar 2) (.bvar 0))

theorem Nonempty_rec_ty_eq : Nonempty_rec_ty = forallTel Nonempty_rec_tel Nonempty_rec_res := rfl

def propext_ty : VExpr :=
  (.forallE (.sort .zero) (.forallE (.sort .zero) (.forallE (.app (.app (.const `Iff []) (.bvar 1))
      (.bvar 0)) (.app (.app (.app (.const `Eq [(.succ .zero)]) (.sort .zero)) (.bvar 2))
      (.bvar 1)))))

def propext_c : VConstVal := { uvars := 0, type := propext_ty, name := `propext }

def propext_tel : List VExpr :=
  [(.sort .zero),
    (.sort .zero),
    (.app (.app (.const `Iff []) (.bvar 1)) (.bvar 0))]

def propext_res : VExpr := (.app (.app (.app (.const `Eq [(.succ .zero)]) (.sort .zero))
    (.bvar 2)) (.bvar 1))

theorem propext_ty_eq : propext_ty = forallTel propext_tel propext_res := rfl

def Classical_choice_ty : VExpr :=
  (.forallE (.sort (.param 0)) (.forallE (.app (.const `Nonempty [(.param 0)])
      (.bvar 0)) (.bvar 1)))

def Classical_choice_c : VConstVal :=
    { uvars := 1, type := Classical_choice_ty, name := `Classical.choice }

def Classical_choice_tel : List VExpr :=
  [(.sort (.param 0)),
    (.app (.const `Nonempty [(.param 0)]) (.bvar 0))]

def Classical_choice_res : VExpr := (.bvar 1)

theorem Classical_choice_ty_eq : Classical_choice_ty = forallTel Classical_choice_tel
    Classical_choice_res := rfl

def Quot_sound_ty : VExpr :=
  (.forallE (.sort (.param 0)) (.forallE (.forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)))
      (.forallE (.bvar 1) (.forallE (.bvar 2) (.forallE (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0))
      (.app (.app (.app (.const `Eq [(.param 0)]) (.app (.app (.const `Quot [(.param 0)]) (.bvar 4))
      (.bvar 3))) (.app (.app (.app (.const `Quot.mk [(.param 0)]) (.bvar 4)) (.bvar 3)) (.bvar 2)))
      (.app (.app (.app (.const `Quot.mk [(.param 0)]) (.bvar 4)) (.bvar 3)) (.bvar 1))))))))

def Quot_sound_c : VConstVal := { uvars := 1, type := Quot_sound_ty, name := `Quot.sound }

def Quot_sound_tel : List VExpr :=
  [(.sort (.param 0)),
    (.forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero))),
    (.bvar 1),
    (.bvar 2),
    (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0))]

def Quot_sound_res : VExpr := (.app (.app (.app (.const `Eq [(.param 0)])
    (.app (.app (.const `Quot [(.param 0)]) (.bvar 4)) (.bvar 3)))
    (.app (.app (.app (.const `Quot.mk [(.param 0)]) (.bvar 4)) (.bvar 3)) (.bvar 2)))
    (.app (.app (.app (.const `Quot.mk [(.param 0)]) (.bvar 4)) (.bvar 3)) (.bvar 1)))

theorem Quot_sound_ty_eq : Quot_sound_ty = forallTel Quot_sound_tel Quot_sound_res := rfl

def Eq_rec_iota0 : VDefEq where
  uvars := 2
  lhs := (.lam (.sort (.param 1)) (.lam (.bvar 0) (.lam (.forallE (.bvar 1)
      (.forallE (.app (.app (.app (.const `Eq [(.param 1)]) (.bvar 2)) (.bvar 1)) (.bvar 0))
      (.sort (.param 0)))) (.lam (.app (.app (.bvar 0) (.bvar 1))
      (.app (.app (.const `Eq.refl [(.param 1)]) (.bvar 2)) (.bvar 1)))
      (.app (.app (.app (.app (.app (.app (.const `Eq.rec [(.param 0), (.param 1)]) (.bvar 3))
      (.bvar 2)) (.bvar 1)) (.bvar 0)) (.bvar 2)) (.app (.app (.const `Eq.refl [(.param 1)])
      (.bvar 3)) (.bvar 2)))))))
  rhs := (.lam (.sort (.param 1)) (.lam (.bvar 0) (.lam (.forallE (.bvar 1)
      (.forallE (.app (.app (.app (.const `Eq [(.param 1)]) (.bvar 2)) (.bvar 1)) (.bvar 0))
      (.sort (.param 0)))) (.lam (.app (.app (.bvar 0) (.bvar 1))
      (.app (.app (.const `Eq.refl [(.param 1)]) (.bvar 2)) (.bvar 1))) (.bvar 0)))))
  type := (.forallE (.sort (.param 1)) (.forallE (.bvar 0) (.forallE
      (.forallE (.bvar 1) (.forallE (.app (.app (.app (.const `Eq [(.param 1)]) (.bvar 2))
      (.bvar 1)) (.bvar 0)) (.sort (.param 0)))) (.forallE (.app (.app (.bvar 0) (.bvar 1))
      (.app (.app (.const `Eq.refl [(.param 1)]) (.bvar 2)) (.bvar 1)))
      (.app (.app (.bvar 1) (.bvar 2)) (.app (.app (.const `Eq.refl [(.param 1)]) (.bvar 3))
      (.bvar 2)))))))

def Eq_rec_iota0_tel : List VExpr :=
  [(.sort (.param 1)),
    (.bvar 0),
    (.forallE (.bvar 1) (.forallE (.app (.app (.app (.const `Eq [(.param 1)]) (.bvar 2)) (.bvar 1))
        (.bvar 0)) (.sort (.param 0)))),
    (.app (.app (.bvar 0) (.bvar 1)) (.app (.app (.const `Eq.refl [(.param 1)]) (.bvar 2))
        (.bvar 1)))]

def Eq_rec_iota0_lhsb : VExpr := (.app (.app (.app (.app (.app
    (.app (.const `Eq.rec [(.param 0), (.param 1)]) (.bvar 3)) (.bvar 2)) (.bvar 1)) (.bvar 0))
    (.bvar 2)) (.app (.app (.const `Eq.refl [(.param 1)]) (.bvar 3)) (.bvar 2)))

def Eq_rec_iota0_rhsb : VExpr := (.bvar 0)

def Eq_rec_iota0_res : VExpr := (.app (.app (.bvar 1) (.bvar 2))
    (.app (.app (.const `Eq.refl [(.param 1)]) (.bvar 3)) (.bvar 2)))

theorem Eq_rec_iota0_eq : Eq_rec_iota0.lhs = lamTelE Eq_rec_iota0_tel Eq_rec_iota0_lhsb ∧
    Eq_rec_iota0.rhs = lamTelE Eq_rec_iota0_tel Eq_rec_iota0_rhsb ∧ Eq_rec_iota0.type =
    forallTel Eq_rec_iota0_tel Eq_rec_iota0_res :=
  ⟨rfl, rfl, rfl⟩

def Iff_rec_iota0 : VDefEq where
  uvars := 1
  lhs := (.lam (.sort .zero) (.lam (.sort .zero) (.lam (.forallE
      (.app (.app (.const `Iff []) (.bvar 1)) (.bvar 0)) (.sort (.param 0)))
      (.lam (.forallE (.forallE (.bvar 2) (.bvar 2)) (.forallE (.forallE (.bvar 2) (.bvar 4))
      (.app (.bvar 2) (.app (.app (.app (.app (.const `Iff.intro []) (.bvar 4)) (.bvar 3))
      (.bvar 1)) (.bvar 0))))) (.lam (.forallE (.bvar 3) (.bvar 3))
      (.lam (.forallE (.bvar 3) (.bvar 5)) (.app (.app (.app (.app
      (.app (.const `Iff.rec [(.param 0)]) (.bvar 5)) (.bvar 4)) (.bvar 3)) (.bvar 2))
      (.app (.app (.app (.app (.const `Iff.intro []) (.bvar 5)) (.bvar 4)) (.bvar 1))
      (.bvar 0)))))))))
  rhs := (.lam (.sort .zero) (.lam (.sort .zero) (.lam (.forallE
      (.app (.app (.const `Iff []) (.bvar 1)) (.bvar 0)) (.sort (.param 0)))
      (.lam (.forallE (.forallE (.bvar 2) (.bvar 2)) (.forallE (.forallE (.bvar 2) (.bvar 4))
      (.app (.bvar 2) (.app (.app (.app (.app (.const `Iff.intro []) (.bvar 4)) (.bvar 3))
      (.bvar 1)) (.bvar 0))))) (.lam (.forallE (.bvar 3) (.bvar 3))
      (.lam (.forallE (.bvar 3) (.bvar 5)) (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0))))))))
  type := (.forallE (.sort .zero) (.forallE (.sort .zero) (.forallE
      (.forallE (.app (.app (.const `Iff []) (.bvar 1)) (.bvar 0)) (.sort (.param 0)))
      (.forallE (.forallE (.forallE (.bvar 2) (.bvar 2)) (.forallE (.forallE (.bvar 2) (.bvar 4))
      (.app (.bvar 2) (.app (.app (.app (.app (.const `Iff.intro []) (.bvar 4)) (.bvar 3))
      (.bvar 1)) (.bvar 0))))) (.forallE (.forallE (.bvar 3) (.bvar 3))
      (.forallE (.forallE (.bvar 3) (.bvar 5)) (.app (.bvar 3) (.app
      (.app (.app (.app (.const `Iff.intro []) (.bvar 5)) (.bvar 4)) (.bvar 1)) (.bvar 0)))))))))

def Iff_rec_iota0_tel : List VExpr :=
  [(.sort .zero),
    (.sort .zero),
    (.forallE (.app (.app (.const `Iff []) (.bvar 1)) (.bvar 0)) (.sort (.param 0))),
    (.forallE (.forallE (.bvar 2) (.bvar 2)) (.forallE (.forallE (.bvar 2) (.bvar 4))
        (.app (.bvar 2) (.app (.app (.app (.app (.const `Iff.intro []) (.bvar 4)) (.bvar 3))
        (.bvar 1)) (.bvar 0))))),
    (.forallE (.bvar 3) (.bvar 3)),
    (.forallE (.bvar 3) (.bvar 5))]

def Iff_rec_iota0_lhsb : VExpr := (.app (.app (.app (.app (.app (.const `Iff.rec [(.param 0)])
    (.bvar 5)) (.bvar 4)) (.bvar 3)) (.bvar 2)) (.app (.app (.app
    (.app (.const `Iff.intro []) (.bvar 5)) (.bvar 4)) (.bvar 1)) (.bvar 0)))

def Iff_rec_iota0_rhsb : VExpr := (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0))

def Iff_rec_iota0_res : VExpr := (.app (.bvar 3) (.app (.app
    (.app (.app (.const `Iff.intro []) (.bvar 5)) (.bvar 4)) (.bvar 1)) (.bvar 0)))

theorem Iff_rec_iota0_eq : Iff_rec_iota0.lhs = lamTelE Iff_rec_iota0_tel Iff_rec_iota0_lhsb ∧
    Iff_rec_iota0.rhs = lamTelE Iff_rec_iota0_tel Iff_rec_iota0_rhsb ∧ Iff_rec_iota0.type =
    forallTel Iff_rec_iota0_tel Iff_rec_iota0_res :=
  ⟨rfl, rfl, rfl⟩

def Nonempty_rec_iota0 : VDefEq where
  uvars := 1
  lhs := (.lam (.sort (.param 0)) (.lam (.forallE (.app (.const `Nonempty [(.param 0)]) (.bvar 0))
      (.sort .zero)) (.lam (.forallE (.bvar 1) (.app (.bvar 1) (.app
      (.app (.const `Nonempty.intro [(.param 0)]) (.bvar 2)) (.bvar 0))))
      (.lam (.bvar 2) (.app (.app (.app (.app (.const `Nonempty.rec [(.param 0)]) (.bvar 3))
      (.bvar 2)) (.bvar 1)) (.app (.app (.const `Nonempty.intro [(.param 0)]) (.bvar 3))
      (.bvar 0)))))))
  rhs := (.lam (.sort (.param 0)) (.lam (.forallE (.app (.const `Nonempty [(.param 0)]) (.bvar 0))
      (.sort .zero)) (.lam (.forallE (.bvar 1) (.app (.bvar 1) (.app
      (.app (.const `Nonempty.intro [(.param 0)]) (.bvar 2)) (.bvar 0))))
      (.lam (.bvar 2) (.app (.bvar 1) (.bvar 0))))))
  type := (.forallE (.sort (.param 0)) (.forallE (.forallE (.app (.const `Nonempty [(.param 0)])
      (.bvar 0)) (.sort .zero)) (.forallE (.forallE (.bvar 1) (.app (.bvar 1)
      (.app (.app (.const `Nonempty.intro [(.param 0)]) (.bvar 2)) (.bvar 0))))
      (.forallE (.bvar 2) (.app (.bvar 2) (.app (.app (.const `Nonempty.intro [(.param 0)])
      (.bvar 3)) (.bvar 0)))))))

def Nonempty_rec_iota0_tel : List VExpr :=
  [(.sort (.param 0)),
    (.forallE (.app (.const `Nonempty [(.param 0)]) (.bvar 0)) (.sort .zero)),
    (.forallE (.bvar 1) (.app (.bvar 1) (.app (.app (.const `Nonempty.intro [(.param 0)]) (.bvar 2))
        (.bvar 0)))),
    (.bvar 2)]

def Nonempty_rec_iota0_lhsb : VExpr := (.app (.app (.app (.app (.const `Nonempty.rec [(.param 0)])
    (.bvar 3)) (.bvar 2)) (.bvar 1)) (.app (.app (.const `Nonempty.intro [(.param 0)])
    (.bvar 3)) (.bvar 0)))

def Nonempty_rec_iota0_rhsb : VExpr := (.app (.bvar 1) (.bvar 0))

def Nonempty_rec_iota0_res : VExpr := (.app (.bvar 2) (.app (.app
    (.const `Nonempty.intro [(.param 0)]) (.bvar 3)) (.bvar 0)))

theorem Nonempty_rec_iota0_eq : Nonempty_rec_iota0.lhs = lamTelE Nonempty_rec_iota0_tel
    Nonempty_rec_iota0_lhsb ∧ Nonempty_rec_iota0.rhs = lamTelE Nonempty_rec_iota0_tel
    Nonempty_rec_iota0_rhsb ∧ Nonempty_rec_iota0.type = forallTel Nonempty_rec_iota0_tel
    Nonempty_rec_iota0_res :=
  ⟨rfl, rfl, rfl⟩

end Soulgem.Core
