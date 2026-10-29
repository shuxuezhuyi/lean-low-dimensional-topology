module

public import LowDimensionalTopology.Geometry.Surfaces.AdmissibleCurveClassStraightening
public import Mathlib.Dynamics.PeriodicPts.Defs

/-!
# Reduction from an actual periodic simple-curve class orbit

An actual finite circle family supplies the members of a periodic free-class
orbit. The minimal period removes repeated classes. Its remaining disjoint
embedded circles form an original admissible multicurve, and the existing
straightening criterion turns class invariance into geometric reducibility.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set

namespace LowDimensionalTopology.Geometry.Surfaces

/-- A periodic actual class orbit with simultaneous disjoint representatives
gives an original reducibility witness under the explicit straightening input. -/
theorem isReducible_of_disjoint_periodic_freeClass_orbit
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hStraight : LowDimensionalTopology.Unproved.Surfaces.SimultaneousAdmissibleCurveStraightening
      R g)
    (f : X ≃ₜ X) (a : EssentialSimpleFreeClass X) {n : ℕ} (hn : 0 < n)
    (hperiod : Function.IsPeriodicPt (essentialSimpleFreeClassEquiv f) n a)
    (cs : Fin n → EssentialSimpleCircle X)
    (hclasses : ∀ i, (cs i).freeClass = ((essentialSimpleFreeClassEquiv f)^[i.val]) a)
    (hdisjoint : ∀ i j, (cs i).freeClass ≠ (cs j).freeClass →
      Disjoint (range (cs i).val) (range (cs j).val)) :
    IsReducible f := by
  classical
  let T := essentialSimpleFreeClassEquiv f
  let k := Function.minimalPeriod T a
  have hkpos : 0 < k := hperiod.minimalPeriod_pos hn
  have hkle : k ≤ n := hperiod.minimalPeriod_le hn
  let index : Fin k → Fin n := fun i => ⟨i.val, i.isLt.trans_le hkle⟩
  let ds : Fin k → EssentialSimpleCircle X := fun i => cs (index i)
  have hds (i : Fin k) : (ds i).freeClass = (T^[i.val]) a := hclasses (index i)
  have hclassinj : Function.Injective (fun i : Fin k => (ds i).freeClass) := by
    intro i j hij
    apply Fin.ext
    exact Function.iterate_injOn_Iio_minimalPeriod (f := T) (x := a) i.isLt j.isLt
      ((hds i).symm.trans (hij.trans (hds j)))
  let embed : Fin k ↪ EssentialSimpleCircle X :=
    ⟨ds, fun i j hij => hclassinj (congrArg EssentialSimpleCircle.freeClass hij)⟩
  let C : AdmissibleMulticurve X :=
    { curves := Finset.univ.map embed
      nonempty := by
        refine ⟨ds ⟨0, hkpos⟩, ?_⟩
        exact Finset.mem_map.mpr ⟨⟨0, hkpos⟩, Finset.mem_univ _, rfl⟩
      disjoint := by
        intro c hc d hd hcd
        obtain ⟨i, _hi, rfl⟩ := Finset.mem_map.mp hc
        obtain ⟨j, _hj, rfl⟩ := Finset.mem_map.mp hd
        exact hdisjoint (index i) (index j)
          (fun heq => hcd (congrArg ds (hclassinj heq)))
      classes_injective := by
        intro c hc d hd hcd
        obtain ⟨i, _hi, rfl⟩ := Finset.mem_map.mp hc
        obtain ⟨j, _hj, rfl⟩ := Finset.mem_map.mp hd
        exact congrArg ds (hclassinj hcd) }
  have hforward : ∀ b ∈ C.freeClasses, T b ∈ C.freeClasses := by
    rintro b ⟨c, rfl⟩
    obtain ⟨i, _hi, hi⟩ := Finset.mem_map.mp c.property
    let j : Fin k := ⟨(i.val + 1) % k, Nat.mod_lt _ hkpos⟩
    have hnext : T (ds i).freeClass = (ds j).freeClass := by
      rw [hds i, hds j]
      change T ((T^[i.val]) a) = (T^[(i.val + 1) % k]) a
      rw [← Function.iterate_succ_apply' T i.val a]
      exact (Function.iterate_mod_minimalPeriod_eq
        (f := T) (x := a) (n := i.val + 1)).symm
    refine ⟨⟨ds j, Finset.mem_map.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩, ?_⟩
    change (ds j).freeClass = T c.val.freeClass
    rw [← hi]
    exact hnext.symm
  let : Fintype C.freeClasses :=
    (Set.finite_range (fun c : C.curves => c.val.freeClass)).fintype
  let nextClass : C.freeClasses → C.freeClasses :=
    fun b => ⟨T b.val, hforward b.val b.property⟩
  have hinj : Function.Injective nextClass := by
    intro b d hbd
    apply Subtype.ext
    exact T.injective (congrArg Subtype.val hbd)
  have hsurj : Function.Surjective nextClass := Finite.surjective_of_injective hinj
  have hinvariant : T '' C.freeClasses = C.freeClasses := by
    ext b
    constructor
    · rintro ⟨d, hd, rfl⟩
      exact hforward d hd
    · intro hb
      obtain ⟨d, hd⟩ := hsurj ⟨b, hb⟩
      exact ⟨d.val, d.property, congrArg Subtype.val hd⟩
  exact isReducible_of_preserves_admissibleFreeClasses_of_straightening
    R hg hgenus hStraight f C hinvariant

end LowDimensionalTopology.Geometry.Surfaces
