import Soulgem.Spec.Cert

/-! Spec facts the checker uses that no root reaches. -/

namespace Soulgem.Spec.SBlock
variable (b : SBlock)

instance (f : SField) : Decidable (b.FieldSyn f) := by
  unfold FieldSyn; split <;> infer_instance

instance (j : Nat) (c : SCtor) : Decidable (b.CtorSyn j c) :=
  decidable_of_iff (_ ∧ _ ∧ _ ∧ _ ∧ _)
    ⟨fun ⟨a, b, c, d, e⟩ => ⟨a, b, c, d, e⟩, fun ⟨a, b, c, d, e⟩ => ⟨a, b, c, d, e⟩⟩

instance : Decidable b.Syn :=
  decidable_of_iff (_ ∧ _ ∧ _)
    ⟨fun ⟨a, b, c⟩ => ⟨a, b, c⟩, fun ⟨a, b, c⟩ => ⟨a, b, c⟩⟩

end Soulgem.Spec.SBlock

namespace Soulgem.Spec
open Lean Lean4Lean

variable (tr : Translated) (b : SBlock) (nuser : Nat)

theorem certKey_of_none {rec : List RBlock} {fams : List Fam}
    (h : ∀ F ∈ fams, F.kernelDs = none) (g : Nat) : certKey rec fams g = none := by
  unfold certKey
  exact List.findSome?_eq_none_iff.mpr fun F hF => by simp [h F hF]

theorem certTr_of_none {rec : List RBlock} {fams : List Fam}
    (h : ∀ F ∈ fams, F.kernelDs = none) : certTr tr rec fams = tr := by
  unfold certTr
  simp only [certKey_of_none h, Option.getD_none]
  have : ∀ l : List Aux, l.mapIdx (fun _ a => { a with key := a.key }) = l := fun l => by
    apply List.ext_getElem (by simp); intro i h₁ h₂; simp
  cases tr; simp only [this]

theorem addCertified_of_none {rec : List RBlock} {fams : List Fam}
    (h : ∀ F ∈ fams, F.kernelDs = none) (env' : VEnv) : addCertified tr b nuser rec fams env'
        = env' := by
  unfold addCertified certTypings
  rw [ite_eq_left (List.all_eq_true.mpr fun F hF => by simp [h F hF]), List.foldl_nil]

end Soulgem.Spec
