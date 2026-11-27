import Soulgem.Model.Admits
import Soulgem.NatBlock
/-! # Soundness, and the model's natural numbers are the true ones -/
namespace Soulgem.Nested
open ConLeche ConLeche.SetTheory ConLeche.SetTheory.Tower Lean4Lean Spec BlockSem BlockModel
open Soulgem.Core (coreM app_Eq lookupC_ne_none coreConsts)

universe u

variable {V : Type u} [SetTheory V]

def StdNat (X z s : V) : Prop :=
  ∃ f : Nat → V, f 0 = z ∧ (∀ n, f (n + 1) = app s (f n)) ∧ (∀ n, f n ∈ˢ X) ∧
    Function.Injective f ∧ ∀ x, x ∈ˢ X → ∃ n, x = f n

theorem _root_.Soulgem.IsModel.prop_inhabited {M : CInterp V} {env : VEnv}
    (hM : IsModel M env) {U : Nat} {e p : VExpr} (he : env.HasType U [] e p) (ls : List Nat) :
    ∃ x, x ∈ˢ interp M ls p [] :=
  ⟨_, (hM.sound he ls [] trivial).2⟩

theorem CanonR.stdNat {M : CInterp V} {env : VEnv} {r : RBlock} {MJ : CInterp V}
    {envJ envJ₁ : VEnv} (C : CanonR M env r MJ envJ envJ₁) (hb : r.b = natBlock)
    (hn : 0 < r.nuser) : StdNat (M `Nat []) (M `Nat.zero []) (M `Nat.succ []) := by
  obtain ⟨k, hk, -, -, -, hkv⟩ := C.slots 0 (by rw [hb]; decide)
  have hk' : k = .const `Nat [] := by
    simp [RBlock.slotKey, hn, hb, natBlock, ownLevels, vars, appN] at hk; exact hk.symm
  subst hk'
  have hT := hkv [] [] (by rw [hb]; rfl) (by rw [hb]; exact .nil)
  have hZ := (C.slotCtors 0 (by rw [hb]; decide) 0 _ (by rw [hb]; rfl) _ hk `Nat [] [] rfl).2 [] []
    (by rw [hb]; rfl) (by rw [hb]; exact .nil)
  have hS := (C.slotCtors 0 (by rw [hb]; decide) 1 _ (by rw [hb]; rfl) _ hk `Nat [] [] rfl).2 [] []
    (by rw [hb]; rfl) (by rw [hb]; exact .nil)
  have Sg := C.setting
  revert hT hZ hS Sg
  generalize r.b = b at *
  intro hT hZ hS Sg
  have e1 : b.ntypes = 1 := by subst hb; rfl
  have e2 : b.names = [`Nat] := by subst hb; rfl
  have e3 : (b.types[0]!).name = `Nat := by subst hb; rfl
  have e4 : b.params = [] := by subst hb; rfl
  have e5 : (b.types[0]!).indices = [] := by subst hb; rfl
  have e5' : (b.types[0]?.getD default).indices = [] := by subst hb; rfl
  have e6 : b.level = .succ .zero := by subst hb; rfl
  have e7 : ctorsOf b 0 = [⟨`Nat.zero, .const `Nat [], [], []⟩,
      ⟨`Nat.succ, .forallE (.const `Nat []) (.const `Nat []),
        [⟨.const `Nat [], .succ .zero, .recursive [] 0 []⟩], []⟩] := by subst hb; rfl
  have hpre0 : (`Nat.zero : Name).replacePrefix `Nat `Nat = `Nat.zero := by decide
  have hpre1 : (`Nat.succ : Name).replacePrefix `Nat `Nat = `Nat.succ := by decide
  have hlev : lev [] b ≠ 0 := by simp [lev, e6, VLevel.eval]
  have hT0 : mkTower [] ∈ˢ Is MJ [] b [] 0 := by
    show _ ∈ˢ extSet MJ [] _ []; rw [e5]; exact (mem_extSet MJ []).mpr ⟨[], .nil, rfl⟩
  have hl : ([] : List Nat).length = b.uvars := by subst hb; rfl
  have hps : Ext MJ [] b.params [] ([] : List V) := by rw [e4]; exact .nil
  have hm : 0 < b.ntypes := by rw [e1]; decide
  have hs := Sg.hSmall hl hps
  have hB := Sg.hBound hl hps
  simp only [List.reverse_nil] at hs hB
  have hMc : Setting.Mc MJ b `Nat [] = (app (carrier MJ [] b [] 0) (mkTower [])) := by
    simp only [Setting.Mc, M₁, e2, findName, ite_eq_left, former, e4, e5, Soulgem.lamTel,
      List.take_nil, List.reverse_nil]; simp [e1]
  have hMT : M `Nat [] = (app (carrier MJ [] b [] 0) (mkTower [])) := by
    simp only [interp, List.foldl, M₁, e2, e3, findName, former, e4,
      Soulgem.lamTel, carrierFn] at hT
    simpa [e1, e5', Soulgem.lamTel, nidx] using hT
  have hMZ : M `Nat.zero [] = inj 0 (mkTower []) := by
    simp only [interp, appN, List.foldl, List.reverse_nil, List.map_nil, e3, hpre0] at hZ
    rw [hZ]; simp [Setting.ctorVal, e4, Soulgem.lamTel, enc, hlev]
  have hMS : M `Nat.succ [] = clam (app (carrier MJ [] b [] 0) (mkTower [])) fun y =>
      inj 1 (mkTower [y]) := by
    simp only [interp, appN, List.foldl, List.reverse_nil, List.map_nil, e3, hpre1] at hS
    rw [hS]; simp [Setting.ctorVal, e4, Soulgem.lamTel, enc, hlev, interp, hMc]
  have hfib : ∀ {Y : Nat → V} {x : V}, x ∈ˢ fib MJ [] b [] Y 0 (mkTower []) →
      x = inj 0 (mkTower []) ∨ ∃ y, y ∈ˢ app (Y 0) (mkTower []) ∧ x = inj 1 (mkTower [y]) := by
    intro Y x hx
    obtain ⟨q, fs, ⟨c, hc, hfit, -⟩, rfl⟩ := (mem_fib_pos hlev).mp hx
    rw [e7] at hc
    match q, hc with
    | 0, hc =>
      cases Option.some.inj hc; cases hfit; exact .inl rfl
    | 1, hc =>
      cases Option.some.inj hc
      obtain _ | ⟨hy, hrest⟩ := hfit
      cases hrest
      exact .inr ⟨_, by simpa [fdom, piTel] using hy, rfl⟩
    | n + 2, hc => simp at hc
  have hKfib : ∀ x, x ∈ˢ (app (carrier MJ [] b [] 0) (mkTower [])) ↔ x ∈ˢ
      fib MJ [] b [] (carrier MJ [] b []) 0 (mkTower []) := fun x => by
    rw [app_carrier Sg.hK hs hB hm hT0]
  have hzK : inj 0 (mkTower []) ∈ˢ (app (carrier MJ [] b [] 0) (mkTower [])) := by
    rw [hKfib]; exact (mem_fib_pos hlev).mpr ⟨0, [], ⟨_, by rw [e7]; rfl, .nil, rfl⟩, rfl⟩
  have hsK : ∀ y, y ∈ˢ (app (carrier MJ [] b [] 0) (mkTower [])) → inj 1 (mkTower [y]) ∈ˢ
      (app (carrier MJ [] b [] 0) (mkTower [])) := fun y hy => by
    rw [hKfib]
    exact (mem_fib_pos hlev).mpr ⟨1, [y], ⟨_, by rw [e7]; rfl,
      .cons (f := ⟨.const `Nat [], .succ .zero, .recursive [] 0 []⟩)
        (by simpa [fdom, piTel] using hy) .nil, rfl⟩, rfl⟩
  let f : Nat → V := fun n => Nat.rec (inj 0 (mkTower [])) (fun _ y => inj 1 (mkTower [y])) n
  have hfK : ∀ n, f n ∈ˢ (app (carrier MJ [] b [] 0) (mkTower [])) := fun n => by
    induction n with
    | zero => exact hzK
    | succ n ih => exact hsK _ ih
  refine ⟨f, hMZ.symm, fun n => ?_, fun n => hMT ▸ hfK n, fun n m h => ?_, fun x hx => ?_⟩
  · rw [hMS, app_clam (hfK n)]
  · induction n generalizing m with
    | zero => cases m with
      | zero => rfl
      | succ m => exact absurd (inj_inj h).1 (by decide)
    | succ n ih => cases m with
      | zero => exact absurd (inj_inj h).1 (by decide)
      | succ m =>
        have := mkTower_inj (as := [f n]) (bs := [f m]) rfl (inj_inj h).2
        exact congrArg (· + 1) (ih m (List.cons.inj this).1)
  ·
    rw [hMT] at hx
    have key := lfpTuple_induction (BlockSem.closed Sg.hK hs hB)
      (BlockSem.mono Sg.hK) (fun _ _ x => ∃ n, x = f n) ?_ 0 hm _ hT0 x hx
    · exact key
    intro m' hm' i hi y hy
    have hm0 : m' = 0 := by rw [e1] at hm'; omega
    subst hm0
    have hi0 : i = mkTower [] := by
      obtain ⟨xs, hxs, rfl⟩ := (mem_extSet MJ []).mp (show i ∈ˢ extSet MJ [] _ [] from hi)
      rw [e5] at hxs; cases hxs; rfl
    subst hi0
    rw [app_Φ hT0] at hy
    rcases hfib hy with rfl | ⟨z, hz, rfl⟩
    · exact ⟨0, rfl⟩
    · unfold sepTuple at hz; rw [app_graph hT0, mem_sep] at hz
      obtain ⟨-, n, rfl⟩ := hz
      exact ⟨n + 1, rfl⟩

def eqNat (s t : VExpr) : VExpr :=
  .app (.app (.app (.const `Eq [.succ .zero]) (.const `Nat [])) s) t

/-- `eqNat_sound` from the two sides' membership in the model's `Nat`, not from their typings. -/
theorem _root_.Soulgem.IsModel.eqNat_sound_mem {M : CInterp V} {env : VEnv} (hM : IsModel M env)
    (hEq : M `Eq = coreM `Eq)
    (hc : env.constants `Nat = some { uvars := 0, type := .sort (.succ .zero) })
    {U : Nat} {e s t : VExpr} (hs' : interp M [] s [] ∈ˢ M `Nat [])
    (ht' : interp M [] t [] ∈ˢ M `Nat []) (he : env.HasType U [] e (eqNat s t)) :
    interp M [] s [] = interp M [] t [] := by
  have hα : M `Nat [] ∈ˢ (univ 1 : V) := by
    simpa [interp, VLevel.eval] using hM.const hc [] rfl []
  have he' := (hM.sound he [] [] trivial).2
  simp only [eqNat, interp, List.map, VLevel.eval, hEq] at he'
  rw [app_Eq hα hs' ht'] at he'
  exact (mem_truthVal.mp he').1

theorem _root_.Soulgem.IsModel.eqNat_sound {M : CInterp V} {env : VEnv} (hM : IsModel M env)
    (hEq : M `Eq = coreM `Eq)
    (hc : env.constants `Nat = some { uvars := 0, type := .sort (.succ .zero) })
    {U : Nat} {e s t : VExpr} (hs : env.HasType U [] s (.const `Nat []))
    (ht : env.HasType U [] t (.const `Nat [])) (he : env.HasType U [] e (eqNat s t)) :
    interp M [] s [] = interp M [] t [] :=
  hM.eqNat_sound_mem hEq hc (by simpa [interp] using (hM.sound hs [] [] trivial).2)
    (by simpa [interp] using (hM.sound ht [] [] trivial).2) he

/-- A recorded `natBlock` declares `Nat : Type`. -/
theorem nat_const_of_admits {env : VEnv} {rec : List RBlock} (H : Admits Core.coreEnv env rec)
    {r : RBlock} (hr : r ∈ rec) (hb : r.b = natBlock) (hn : 0 < r.nuser) :
    env.constants `Nat = some { uvars := 0, type := .sort (.succ .zero) } := by
  obtain ⟨k, hk⟩ : ∃ k, r.nuser = k + 1 := ⟨r.nuser - 1, by omega⟩
  have ht : (natBlock.types[0]'(by decide)) ∈ r.b.types.take r.nuser := by
    rw [hb, hk]; simp [natBlock]
  have := (admits_recTypes H).1 r hr _ ht
  rw [hb] at this
  simpa [natBlock] using this

/-- Each environment admitted over `Core.coreEnv` with a `Nat` block has a standard-`Nat` model. -/
theorem Core.sound_standard (V : Type u) [SetTheory V] {env : VEnv} {rec : List RBlock}
    (H : Admits Core.coreEnv env rec) {r : RBlock} (hr : r ∈ rec) (hb : r.b = natBlock)
    (hn : 0 < r.nuser) :
    ∃ M : CInterp V, IsModel M env ∧
      (∀ {U e p}, env.HasType U [] e p → ∀ ls, ∃ x, x ∈ˢ interp M ls p []) ∧
      StdNat (M `Nat []) (M `Nat.zero []) (M `Nat.succ []) ∧
      (∀ {U e s t}, env.HasType U [] s (.const `Nat []) → env.HasType U [] t (.const `Nat []) →
        env.HasType U [] e (eqNat s t) → interp M [] s [] = interp M [] t []) := by
  obtain ⟨M, MJf, envJf, envJ₁f, hM, -, I, -, hfr⟩ :=
    Admits.model (Core.coreM_model (V := V)) Core.coreEnv_good H
  have hEq : M `Eq = coreM `Eq :=
    hfr _ (lookupC_ne_none (by simp [coreConsts]))
  exact ⟨M, hM, fun he ls => hM.prop_inhabited he ls, (I.canon r hr).stdNat hb hn,
    fun hs ht he => hM.eqNat_sound hEq (nat_const_of_admits H hr hb hn) hs ht he⟩

/-- Under `sound_standard`'s hypotheses, `Nat.succ Nat.zero = Nat.zero` is not provable. -/
theorem Core.not_succ_zero_eq_zero (V : Type u) [SetTheory V] {env : VEnv} {rec : List RBlock}
    (H : Admits Core.coreEnv env rec) {r : RBlock} (hr : r ∈ rec) (hb : r.b = natBlock)
    (hn : 0 < r.nuser) {U : Nat} :
    ¬ ∃ e, env.HasType U [] e (eqNat (.app (.const `Nat.succ []) (.const `Nat.zero []))
      (.const `Nat.zero [])) := by
  rintro ⟨e, he⟩
  obtain ⟨M, MJf, envJf, envJ₁f, hM, -, I, -, hfr⟩ :=
    Admits.model (Core.coreM_model (V := V)) Core.coreEnv_good H
  have hEq : M `Eq = coreM `Eq :=
    hfr _ (lookupC_ne_none (by simp [coreConsts]))
  obtain ⟨f, h0, hS, hmem, hinj, -⟩ := (I.canon r hr).stdNat hb hn
  have hz : interp M [] (.const `Nat.zero []) [] ∈ˢ M `Nat [] := by
    simp only [interp, List.map]; rw [← h0]; exact hmem 0
  have hsz : interp M [] (.app (.const `Nat.succ []) (.const `Nat.zero [])) [] ∈ˢ M `Nat [] := by
    simp only [interp, List.map]; rw [← h0, ← hS 0]; exact hmem 1
  have := hM.eqNat_sound_mem hEq (nat_const_of_admits H hr hb hn) hsz hz he
  simp only [interp, List.map] at this
  rw [← h0, ← hS 0] at this
  exact absurd (hinj this) (by decide)

end Soulgem.Nested
