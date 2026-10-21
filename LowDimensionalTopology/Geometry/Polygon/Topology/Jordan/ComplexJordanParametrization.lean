module
public import LowDimensionalTopology.Geometry.Polygon.Topology.Jordan.JordanPolygonRegions
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Instances.AddCircle.Defs
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Topology
namespace LowDimensionalTopology.Geometry.Polygon

/-- Every original actual Jordan loop admits a genuine continuous injective unit-circle
parametrization, not merely an existential separation datum. -/
theorem complexJordan_exists_circle_parametrization {C : Set ℂ} (hC : IsComplexJordanCurve C) :
    ∃f : Circle→ℂ,Continuous f ∧Function.Injective f ∧range f=C := by
  obtain ⟨γ,hγ,hRange⟩:=hC
  let k : AddCircle (1 : ℝ)→Schoenflies.Plane:=AddCircle.liftIco 1 0 γ
  have hkc : Continuous k := AddCircle.liftIco_zero_continuous hγ.closes hγ.continuousOn
  have hki : Function.Injective k := by
    intro a b hab
    apply (AddCircle.equivIco (1 : ℝ) 0).injective
    apply Subtype.ext
    apply hγ.injOn
    · simpa only [zero_add] using (AddCircle.equivIco (1 : ℝ) 0 a).property
    · simpa only [zero_add] using (AddCircle.equivIco (1 : ℝ) 0 b).property
    · exact hab
  have hkr : range k=γ '' Icc (0 : ℝ) 1 := by
    ext z
    constructor
    · rintro ⟨a,rfl⟩
      let t:=AddCircle.equivIco (1 : ℝ) 0 a
      refine ⟨t.val,?_,rfl⟩
      exact ⟨t.property.1,le_of_lt (by simpa only [zero_add] using t.property.2)⟩
    · intro hz
      obtain ⟨t,ht,ht1,hγt⟩:=hγ.parameter_before_finish hz
      refine ⟨(t : AddCircle (1 : ℝ)),?_⟩
      change AddCircle.liftIco 1 0 γ (t : AddCircle (1 : ℝ))=z
      rw [AddCircle.liftIco_zero_coe_apply ⟨ht.1,lt_of_le_of_ne ht.2 ht1⟩]
      exact hγt
  let e:=AddCircle.homeomorphCircle (T := (1 : ℝ)) (by norm_num)
  let f : Circle→ℂ:=fun u=>complexJordanPlaneHomeomorph.symm (k (e.symm u))
  have hfc : Continuous f:=complexJordanPlaneHomeomorph.symm.continuous.comp (hkc.comp e.symm.continuous)
  have hfi : Function.Injective f:=complexJordanPlaneHomeomorph.symm.injective.comp (hki.comp e.symm.injective)
  refine ⟨f,hfc,hfi,?_⟩
  ext z
  constructor
  · rintro ⟨u,rfl⟩
    have hz : k (e.symm u)∈range k:=mem_range_self _
    rw [hkr,hRange] at hz
    obtain ⟨w,hw,hew⟩:=hz
    change complexJordanPlaneHomeomorph.symm (k (e.symm u))∈C
    rw [←hew,complexJordanPlaneHomeomorph.symm_apply_apply]
    exact hw
  · intro hz
    have hm : complexJordanPlaneHomeomorph z∈range k := by
      rw [hkr,hRange]
      exact mem_image_of_mem _ hz
    obtain ⟨a,ha⟩:=hm
    refine ⟨e a,?_⟩
    change complexJordanPlaneHomeomorph.symm (k (e.symm (e a)))=z
    rw [e.symm_apply_apply,ha,complexJordanPlaneHomeomorph.symm_apply_apply]

/-- The actual original complex Jordan boundary is homeomorphic to the unit circle. -/
def complexJordanCircleHomeomorph {C : Set ℂ} (hC : IsComplexJordanCurve C) : Circle≃ₜC := by
  let hex:=complexJordan_exists_circle_parametrization hC
  let f:=Classical.choose hex
  have hc : Continuous f:=(Classical.choose_spec hex).1
  have hi : Function.Injective f:=(Classical.choose_spec hex).2.1
  have hr : range f=C:=(Classical.choose_spec hex).2.2
  let F : Circle→C:=fun u=>⟨f u,hr ▸ mem_range_self u⟩
  have hF : Continuous F := hc.subtype_mk _
  have hbij : Function.Bijective F := by
    constructor
    · intro u v huv
      exact hi (congrArg Subtype.val huv)
    · intro z
      obtain ⟨u,hu⟩:=(show z.val∈range f by rw [hr];exact z.property)
      exact ⟨u,Subtype.ext hu⟩
  exact Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective F hbij) hF

end LowDimensionalTopology.Geometry.Polygon
