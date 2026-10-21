/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Ford.ShiftedFordCycles
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped Topology OnePoint Pointwise UpperHalfPlane Complex.UnitDisc BigOperators
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Auxiliary.Analysis
/-- The literal representatives of an actual original Ford cycle in the
specified half-open unit strip. -/
def fordHalfOpenVertexCycle (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (x₀ : ℝ) (z
  : ℍ) : Set ℍ:=
  _root_.LowDimensionalTopology.Geometry.Fuchsian.mobiusFordVertexCycle H x₀ z∩{u | x₀≤u.re ∧ u.re<x₀+1}

/-- The literal half-open cycle is carried to the literal translated one. -/
theorem fordHalfOpenVertexCycle_translate_mem (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (t x₀ : ℝ) (z w : ℍ) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t•w∈fordHalfOpenVertexCycle (fordTranslatedGroup H
      t) (x₀+t) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t•z) ↔
      w∈fordHalfOpenVertexCycle H x₀ z := by
  change (_∧x₀+t≤(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t•w).re ∧
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t•w).re<x₀+t+1) ↔
    (_∧x₀≤w.re ∧ w.re<x₀+1)
  rw [fordTranslatedGroup_cycle_mem,fordTranslation_re]
  constructor <;> rintro ⟨hc,hl,hr⟩ <;> exact ⟨hc,by linarith only [hl],by linarith only [hr]⟩

/-- Its original native actual-point image is exact. -/
theorem fordHalfOpenVertexCycle_translate_image (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (t x₀ : ℝ) (z : ℍ) :
    (Homeomorph.smul (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL
      t)) '' fordHalfOpenVertexCycle H x₀ z=
      fordHalfOpenVertexCycle (fordTranslatedGroup H t) (x₀+t) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t•z) := by
  ext w
  constructor
  · rintro ⟨u,hu,rfl⟩
    exact (fordHalfOpenVertexCycle_translate_mem H t x₀ z u).mpr hu
  · intro hw
    refine ⟨(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t)⁻¹•w,?_,?_⟩
    · apply (fordHalfOpenVertexCycle_translate_mem H t x₀ z _).mp
      simpa only [smul_inv_smul] using hw
    · change _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t•((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t)⁻¹•w)=w
      exact smul_inv_smul _ _

/-- The actual half-open representative count is a genuine conjugacy invariant. -/
theorem fordHalfOpenVertexCycle_translate_ncard (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (t x₀ : ℝ) (z : ℍ) :
    (fordHalfOpenVertexCycle (fordTranslatedGroup H t) (x₀+t)
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t•z)).ncard=
      (fordHalfOpenVertexCycle H x₀ z).ncard := by
  rw [←fordHalfOpenVertexCycle_translate_image]
  exact Set.ncard_image_of_injective _ (Homeomorph.smul
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t)).injective

/-- Exactly one actual point of the closed cycle lies on the deleted period
edge, so the original half-open count is the augmented count minus one. -/
theorem fordHalfOpenVertexCycle_normalized_ncard {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (hp : IsPrimitive H
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1)) (z : ℍ)
    (hz : z∈closure (parabolicFordDomain H)) (hre : z.re=0) :
    (fordHalfOpenVertexCycle H 0 z).ncard=(_root_.LowDimensionalTopology.Geometry.Fuchsian.mobiusFordVertexCycle H 0 z).ncard-1 := by
  let C:=_root_.LowDimensionalTopology.Geometry.Fuchsian.mobiusFordVertexCycle H 0 z
  let w:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1•z
  obtain ⟨_h0,hw⟩:=parabolicFord_cycle_endpoint_pair P hp.mem z hz hre
  have hwr : w.re=1:=by rw [fordTranslation_re,hre,zero_add]
  have hEq : fordHalfOpenVertexCycle H 0 z=C\{w}:=by
    ext u
    constructor
    · rintro ⟨hu,hl,hr⟩
      refine ⟨hu,?_⟩
      intro he
      have heq : u=w:=he
      rw [heq,hwr] at hr
      exact (lt_irrefl (1:ℝ)) (by simpa only [zero_add] using hr)
    · rintro ⟨hu,hnw⟩
      have huS : u∈parabolicFordClosedStrip H:=by
        have huc:=hu.1
        rw [←parabolicFordDomain_eq_mobiusFordDomain H,closure_parabolicFordDomain H P.discrete hp.mem] at huc
        exact huc
      refine ⟨hu,huS.1,?_⟩
      rw [zero_add]
      apply lt_of_le_of_ne huS.2.1
      intro he
      have heq : u=w:=parabolicFord_cycle_re_injective P z hz hu hw (he.trans hwr.symm)
      exact hnw heq
  rw [hEq]
  exact Set.ncard_sdiff_singleton_of_mem hw

/-- The source's half-open representative count and closed cycle count are
related exactly for the original arbitrary-position strip. -/
theorem fordHalfOpenVertexCycle_ncard {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (hp : IsPrimitive H
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1)) (x₀ : ℝ) (z : ℍ)
    (hz : z∈closure (_root_.LowDimensionalTopology.Geometry.Fuchsian.mobiusFordDomain H x₀)) (hre : z.re=x₀) :
    (fordHalfOpenVertexCycle H x₀ z).ncard=(_root_.LowDimensionalTopology.Geometry.Fuchsian.mobiusFordVertexCycle H x₀ z).ncard-1 := by
  let Q:=fordTranslatedData P (-x₀)
  let w:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (-x₀)•z
  have hp':=fordTranslatedGroup_primitive H (-x₀) hp
  have hwe : w.re=0:=by rw [fordTranslation_re,hre,add_neg_cancel]
  have hw : w∈closure (parabolicFordDomain (fordTranslatedGroup H (-x₀))):=by
    rw [parabolicFordDomain_eq_mobiusFordDomain]
    simpa only [add_neg_cancel] using (fordTranslatedGroup_closure_mem H (-x₀) x₀ z).mpr hz
  have hc:=fordHalfOpenVertexCycle_normalized_ncard Q hp' w hw hwe
  have hhalf : (fordHalfOpenVertexCycle (fordTranslatedGroup H (-x₀)) 0 w).ncard=
      (fordHalfOpenVertexCycle H x₀ z).ncard:=by
    simpa only [add_neg_cancel] using fordHalfOpenVertexCycle_translate_ncard H (-x₀) x₀ z
  have hfull : (_root_.LowDimensionalTopology.Geometry.Fuchsian.mobiusFordVertexCycle (fordTranslatedGroup H (-x₀)) 0
    w).ncard=
      (_root_.LowDimensionalTopology.Geometry.Fuchsian.mobiusFordVertexCycle H x₀ z).ncard:=by
    simpa only [add_neg_cancel] using fordTranslatedGroup_cycle_ncard H (-x₀) x₀ z
  rwa [hhalf,hfull] at hc

/-- The source's finite real height estimate, with its literal original
half-open cycle count, follows from the actual original group and polygon. -/
theorem ford_boundary_vertex_height_le_cycleHeightBound {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (hp : IsPrimitive H
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1)) (x₀ : ℝ) (z : ℍ)
    (hz : z∈closure (_root_.LowDimensionalTopology.Geometry.Fuchsian.mobiusFordDomain H x₀)) (hre : z.re=x₀)
    (hqn : 2<fordPointOrder H z*(fordHalfOpenVertexCycle H x₀ z).ncard) :
    z.im≤cycleHeightBound (fordPointOrder H z) (fordHalfOpenVertexCycle H x₀ z).ncard := by
  rw [fordHalfOpenVertexCycle_ncard P hp x₀ z hz hre] at hqn ⊢
  exact parabolicFord_shifted_cycle_height_bound P hp x₀ z hz hre hqn

/--
With the actual half-open count condition explicit:
closed-cycle length at least three alone does not imply this condition.
-/
theorem ford_boundary_accidental_vertex_height_bound_and_translationSinh_lower_bound {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (hp : IsPrimitive H
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1)) (x₀ : ℝ) (z : ℍ)
    (hz : z∈closure (_root_.LowDimensionalTopology.Geometry.Fuchsian.mobiusFordDomain H x₀)) (hre : z.re=x₀)
    (hq : fordPointOrder H z=1) (hn : 3≤(fordHalfOpenVertexCycle H x₀ z).ncard) :
    z.im≤1/(2*Real.sqrt 3) ∧
      Real.sqrt 3≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1)) z := by
  have hqn : 2<fordPointOrder H z*(fordHalfOpenVertexCycle H x₀ z).ncard:=by
    rw [hq,one_mul]
    omega
  have hh:=ford_boundary_vertex_height_le_cycleHeightBound P hp x₀ z hz hre hqn
  rw [hq] at hh
  have hheight:=hh.trans (cycleHeightBound_accidental_le _ hn)
  refine ⟨hheight,?_⟩
  have hdisp:=unitTranslation_half_displacement_lower_of_height z (1/(2*Real.sqrt 3)) hheight
  have he : 1/(2*(1/(2*Real.sqrt 3)))=Real.sqrt 3:=by
    have hs : Real.sqrt 3≠0:=ne_of_gt (by positivity)
    field_simp
  rwa [he] at hdisp

end LowDimensionalTopology.Geometry.Fuchsian
