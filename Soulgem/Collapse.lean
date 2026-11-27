import ConLeche.SetTheory.Basic
import Lean.Level

/-! # Collapsed function spaces -/

namespace Soulgem
open ConLeche ConLeche.SetTheory

universe u
variable {V : Type u} [SetTheory V]

open Classical in
noncomputable def clam (A : V) (F : V → V) : V :=
  if ∀ x, x ∈ˢ A → F x = pt then pt else graph F A

open Classical in
noncomputable def collapse (A f : V) : V :=
  if ∀ x, x ∈ˢ A → app f x = pt then pt else f

noncomputable def cpi (A : V) (B : V → V) : V := image (collapse A) (piSet A B)

theorem app_collapse {A f a : V} (ha : a ∈ˢ A) : app (collapse A f) a = app f a := by
  unfold collapse; split
  · rename_i h; rw [app_pt, h a ha]
  · rfl

theorem collapse_graph {A : V} {F : V → V} : collapse A (graph F A) = clam A F := by
  unfold collapse clam
  have : (∀ x, x ∈ˢ A → app (graph F A) x = pt) ↔ (∀ x, x ∈ˢ A → F x = pt) :=
    forall_congr' fun x => imp_congr_right fun hx => by rw [app_graph hx]
  by_cases h : ∀ x, x ∈ˢ A → F x = pt
  · rw [ite_eq_left (this.mpr h), ite_eq_left h]
  · rw [ite_eq_right (mt this.mp h), ite_eq_right h]

theorem app_clam {A a : V} {F : V → V} (ha : a ∈ˢ A) : app (clam A F) a = F a := by
  rw [← collapse_graph, app_collapse ha, app_graph ha]

theorem clam_congr {A : V} {F F' : V → V} (h : ∀ x, x ∈ˢ A → F x = F' x) :
    clam A F = clam A F' := by
  rw [← collapse_graph, ← collapse_graph, graph_congr h]

theorem mem_cpi {A f : V} {B : V → V} :
    f ∈ˢ cpi A B ↔ ∃ g, g ∈ˢ piSet A B ∧ f = collapse A g := by
  unfold cpi; rw [mem_image]

theorem clam_mem_cpi {A : V} {B F : V → V} (h : ∀ x, x ∈ˢ A → F x ∈ˢ B x) :
    clam A F ∈ˢ cpi A B :=
  mem_cpi.mpr ⟨_, graph_mem_piSet h, collapse_graph.symm⟩

theorem app_mem_cpi {A f a : V} {B : V → V} (hf : f ∈ˢ cpi A B) (ha : a ∈ˢ A) :
    app f a ∈ˢ B a := by
  obtain ⟨g, hg, rfl⟩ := mem_cpi.mp hf
  rw [app_collapse ha]; exact app_mem_of_mem_piSet hg ha

theorem clam_app_eta {A f : V} {B : V → V} (hf : f ∈ˢ cpi A B) :
    clam A (fun x => app f x) = f := by
  obtain ⟨g, hg, rfl⟩ := mem_cpi.mp hf
  rw [clam_congr (F' := fun x => app g x) fun x hx => app_collapse hx,
    ← collapse_graph, eq_graph_app_of_mem_piSet hg]

theorem cpi_congr {A : V} {B B' : V → V} (h : ∀ x, x ∈ˢ A → B x = B' x) :
    cpi A B = cpi A B' := by
  unfold cpi; rw [piSet_congr h]

theorem pt_mem_univ {n : Nat} (hn : n ≠ 0) : (pt : V) ∈ˢ univ n :=
  (univ_isTGUniverse hn).transitive (unitSet_mem_univ _) pt_mem_unitSet

theorem cpi_mem_univ {A : V} {B : V → V} {u v : Nat} (hA : A ∈ˢ univ u)
    (hB : ∀ x, x ∈ˢ A → B x ∈ˢ univ v) : cpi A B ∈ˢ univ (Lean.Nat.imax u v) := by
  unfold Lean.Nat.imax; split
  · rename_i hv; subst hv
    rw [univ_zero, mem_univZero]
    intro f hf
    obtain ⟨g, hg, rfl⟩ := mem_cpi.mp hf
    have : ∀ x, x ∈ˢ A → app g x = pt := fun x hx =>
      mem_univ_zero (hB x hx) (app_mem_of_mem_piSet hg hx)
    unfold collapse; rw [ite_eq_left this]; exact pt_mem_unitSet
  · rename_i hv
    have hw : u.max v ≠ 0 :=
      Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.pos_of_ne_zero hv) (Nat.le_max_right u v))
    have hU := univ_isTGUniverse (V := V) hw
    have hA' : A ∈ˢ univ (u.max v) := univ_mono (Nat.le_max_left u v) A hA
    have hB' : ∀ x, x ∈ˢ A → B x ∈ˢ univ (u.max v) := fun x hx =>
      univ_mono (Nat.le_max_right u v) _ (hB x hx)
    have hP := hU.piSet_mem hA' hB'
    refine hU.image_mem hP fun g hg => ?_
    unfold collapse; split
    · exact pt_mem_univ hw
    · exact hU.transitive hP hg

theorem cpi_prop_id_empty {f : V} : ¬ f ∈ˢ cpi (univ 0) (fun x => x) := fun hf =>
  not_mem_empty _ (app_mem_cpi hf (empty_mem_univ 0))

end Soulgem
