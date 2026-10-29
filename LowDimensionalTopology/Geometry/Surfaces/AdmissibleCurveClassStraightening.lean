module

public import LowDimensionalTopology.Unproved.Surfaces.SimultaneousAdmissibleCurveStraightening
public import LowDimensionalTopology.Geometry.Surfaces.EssentialSimpleClassHomeomorph
public import Mathlib.Data.Finset.Image
public import Mathlib.Logic.Equiv.Set

/-!
# Reducibility from straightening original admissible curve families

Postcomposition by an actual homeomorphism retains every member of the
finite curve family. Class-set invariance produces a matching index
equivalence. The explicit classical straightening input then corrects the
actual image family by a homeomorphism homotopic to the identity.
The conclusion is the original geometric-union reducibility predicate.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Surfaces

variable {X : Type} [TopologicalSpace X]

/-- The actual injective postcomposition map on essential embedded circles. -/
def circleMapEmbedding (f : X ≃ₜ X) :
    EssentialSimpleCircle X ↪ EssentialSimpleCircle X where
  toFun c := c.mapHomeomorph f
  inj' := by
    intro c d h
    have hh := congrArg (fun a : EssentialSimpleCircle X => a.mapHomeomorph f.symm) h
    simpa only [EssentialSimpleCircle.mapHomeomorph_symm] using hh

namespace AdmissibleMulticurve

/-- Postcompose every original member with the supplied actual homeomorphism. -/
def mapHomeomorph (C : AdmissibleMulticurve X) (f : X ≃ₜ X) :
    AdmissibleMulticurve X where
  curves := C.curves.map (circleMapEmbedding f)
  nonempty := by
    obtain ⟨c, hc⟩ := C.nonempty
    exact ⟨c.mapHomeomorph f, Finset.mem_map.mpr ⟨c, hc, rfl⟩⟩
  disjoint := by
    intro c hc d hd hcd
    change c ∈ C.curves.map (circleMapEmbedding f) at hc
    change d ∈ C.curves.map (circleMapEmbedding f) at hd
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hc
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hd
    have hab : a ≠ b := by
      intro h
      subst b
      exact hcd rfl
    have hdisjoint := C.disjoint ha hb hab
    apply Set.disjoint_left.mpr
    rintro x ⟨z, hz⟩ ⟨w, hw⟩
    have heq : a.val z = b.val w := f.injective (hz.trans hw.symm)
    exact Set.disjoint_left.mp hdisjoint ⟨z, rfl⟩ ⟨w, heq.symm⟩
  classes_injective := by
    intro c hc d hd hclass
    change c ∈ C.curves.map (circleMapEmbedding f) at hc
    change d ∈ C.curves.map (circleMapEmbedding f) at hd
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hc
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hd
    change essentialSimpleFreeClassEquiv f a.freeClass =
      essentialSimpleFreeClassEquiv f b.freeClass at hclass
    exact congrArg (circleMapEmbedding f)
      (C.classes_injective ha hb ((essentialSimpleFreeClassEquiv f).injective hclass))

theorem mem_mapHomeomorph_iff (C : AdmissibleMulticurve X) (f : X ≃ₜ X)
    (d : EssentialSimpleCircle X) :
    d ∈ (C.mapHomeomorph f).curves ↔
      ∃ c ∈ C.curves, c.mapHomeomorph f = d := by
  change d ∈ C.curves.map (circleMapEmbedding f) ↔ _
  exact Finset.mem_map

/-- The entire geometric union is the actual image of the original union. -/
theorem carrier_mapHomeomorph (C : AdmissibleMulticurve X) (f : X ≃ₜ X) :
    (C.mapHomeomorph f).carrier = f '' C.carrier := by
  ext x
  simp only [carrier, Set.mem_iUnion, Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨d, hd, z, hzx⟩
    obtain ⟨c, hc, rfl⟩ := (C.mem_mapHomeomorph_iff f d).mp hd
    exact ⟨c.val z, ⟨c, hc, z, rfl⟩, hzx⟩
  · rintro ⟨y, ⟨c, hc, z, hzy⟩, hfy⟩
    exact ⟨c.mapHomeomorph f, (C.mem_mapHomeomorph_iff f _).mpr ⟨c, hc, rfl⟩,
      z, (congrArg f hzy).trans hfy⟩

/-- The finite set of original unoriented classes of all supplied members. -/
def freeClasses (C : AdmissibleMulticurve X) : Set (EssentialSimpleFreeClass X) :=
  Set.range (fun c : C.curves => c.val.freeClass)

theorem freeClasses_mapHomeomorph (C : AdmissibleMulticurve X) (f : X ≃ₜ X) :
    (C.mapHomeomorph f).freeClasses = essentialSimpleFreeClassEquiv f '' C.freeClasses := by
  ext a
  constructor
  · rintro ⟨d, rfl⟩
    obtain ⟨c, hc, hcd⟩ := (C.mem_mapHomeomorph_iff f d.val).mp d.property
    refine ⟨c.freeClass, ⟨⟨c, hc⟩, rfl⟩, ?_⟩
    change (c.mapHomeomorph f).freeClass = d.val.freeClass
    exact congrArg EssentialSimpleCircle.freeClass hcd
  · rintro ⟨a, ⟨c, rfl⟩, rfl⟩
    refine ⟨⟨c.val.mapHomeomorph f, ?_⟩, rfl⟩
    exact (C.mem_mapHomeomorph_iff f _).mpr ⟨c.val, c.property, rfl⟩

private def freeClassEquiv (C : AdmissibleMulticurve X) : C.curves ≃ C.freeClasses :=
  Equiv.ofBijective (fun c : C.curves => ⟨c.val.freeClass, ⟨c, rfl⟩⟩) (by
    constructor
    · intro c d h
      apply Subtype.ext
      exact C.classes_injective c.property d.property (congrArg Subtype.val h)
    · rintro ⟨a, ⟨c, rfl⟩⟩
      exact ⟨c, rfl⟩)

private theorem image_carrier_of_matching (C D : AdmissibleMulticurve X)
    (e : C.curves ≃ D.curves) (h : X ≃ₜ X)
    (hcurves : ∀ c : C.curves, h '' Set.range c.val.val = Set.range (e c).val.val) :
    h '' C.carrier = D.carrier := by
  ext x
  simp only [carrier, Set.mem_iUnion, Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨y, ⟨c, hc, z, hczy⟩, hxy⟩
    have hx : x ∈ h '' Set.range c.val := ⟨y, ⟨z, hczy⟩, hxy⟩
    rw [hcurves ⟨c, hc⟩] at hx
    obtain ⟨w, hw⟩ := hx
    exact ⟨(e ⟨c, hc⟩).val, (e ⟨c, hc⟩).property, w, hw⟩
  · rintro ⟨d, hd, z, hzx⟩
    have hx : x ∈ Set.range (e (e.symm ⟨d, hd⟩)).val.val := by
      rw [e.apply_symm_apply]
      exact ⟨z, hzx⟩
    rw [← hcurves (e.symm ⟨d, hd⟩)] at hx
    obtain ⟨y, ⟨w, hw⟩, hy⟩ := hx
    exact ⟨y, ⟨(e.symm ⟨d, hd⟩).val, (e.symm ⟨d, hd⟩).property, w, hw⟩, hy⟩

end AdmissibleMulticurve

/-- Class-set invariance of a genuine admissible family implies the original
reducibility predicate under the independent simultaneous-straightening input. -/
theorem isReducible_of_preserves_admissibleFreeClasses_of_straightening
    (R : ClosedRiemannSurface X) {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hStraight : LowDimensionalTopology.Unproved.Surfaces.SimultaneousAdmissibleCurveStraightening R g)
    (f : X ≃ₜ X) (C : AdmissibleMulticurve X)
    (hclasses : essentialSimpleFreeClassEquiv f '' C.freeClasses = C.freeClasses) :
    IsReducible f := by
  let D := C.mapHomeomorph f
  have hDC : D.freeClasses = C.freeClasses :=
    (C.freeClasses_mapHomeomorph f).trans hclasses
  let e : D.curves ≃ C.curves :=
    (D.freeClassEquiv.trans (Set.equivOfEq hDC)).trans C.freeClassEquiv.symm
  have hmatch (d : D.curves) : d.val.freeClass = (e d).val.freeClass := by
    exact (congrArg Subtype.val (C.freeClassEquiv.apply_symm_apply
      ((Set.equivOfEq hDC) (D.freeClassEquiv d)))).symm
  obtain ⟨h, hh, hcurves⟩ := hStraight hg hgenus D C e hmatch
  have hcarrier : h '' D.carrier = C.carrier :=
    D.image_carrier_of_matching C e h hcurves
  refine ⟨f.trans h, ?_, C, ?_⟩
  · exact (hh.comp (ContinuousMap.Homotopic.refl (_root_.toContinuousMap f))).symm
  · change (h ∘ f) '' C.carrier = C.carrier
    calc
      (h ∘ f) '' C.carrier = h '' (f '' C.carrier) :=
        (Set.image_image h f C.carrier).symm
      _ = h '' D.carrier :=
        congrArg (fun s : Set X => h '' s) (C.carrier_mapHomeomorph f).symm
      _ = C.carrier := hcarrier

end LowDimensionalTopology.Geometry.Surfaces
