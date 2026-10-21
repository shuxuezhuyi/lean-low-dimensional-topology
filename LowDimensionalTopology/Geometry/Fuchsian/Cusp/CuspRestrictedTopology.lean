/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.Fuchsian.Cusp.CuspNormalizationGeometry
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology
open scoped OnePoint UpperHalfPlane MatrixGroups
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The unchanged literal inclusion of an admissible sphere subset into the genuine all-cusp augmented domain. -/
def fuchsianCuspSubsetInclusion {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D :
  FuchsianDisc H)
    (K : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    (hK : ∀z∈K,z∈D.carrier∨∃(c : FuchsianCyclicConjugacyClasses D .parabolic)(g : H),
      g.val.val (fuchsianParabolicPointRepresentative D c).val=z) :
    K→_root_.LowDimensionalTopology.Geometry.Surfaces.MultipleCuspAugmentedDomain (fuchsianCuspChartNormalization D) :=
  fun z=>⟨z.val,hK z.val z.property⟩

/-- The literal inclusion is continuous at every original-domain point; both the original sphere and original quotient topology are retained. -/
theorem fuchsianCuspSubsetInclusion_continuousAt_old {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (K : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    (hK : ∀z∈K,z∈D.carrier∨∃(c : FuchsianCyclicConjugacyClasses D .parabolic)(g : H),
      g.val.val (fuchsianParabolicPointRepresentative D c).val=z)
    (z : K) (hz : z.val∈D.carrier) :
    ContinuousAt (fuchsianCuspSubsetInclusion D K hK) z := by
  let A : Set K:={z | z.val∈D.carrier}
  have hAo : IsOpen A:=D.isDisc.isOpen.preimage continuous_subtype_val
  let f : A→D.domain.carrier:=fun z=>⟨z.val.val,z.property⟩
  have hf : Continuous f:=(continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  have hc : ContinuousOn (fuchsianCuspSubsetInclusion D K hK) A:=by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have he : A.domRestrict (fuchsianCuspSubsetInclusion D K hK)=
        _root_.LowDimensionalTopology.Geometry.Surfaces.multipleCuspAugmentedOld (fuchsianCuspChartNormalization
          D) ∘ f:=rfl
    rw [he]
    exact (_root_.LowDimensionalTopology.Geometry.Surfaces.multipleCuspAugmentedOld_continuous
      (fuchsianCuspChartNormalization D)).comp hf
  exact hc.continuousAt (hAo.mem_nhds hz)

/-- Actual uniform real and lower-imaginary bounds in each genuine cusp chart imply continuity of the literal sphere subset inclusion for the genuine uniform-height augmented cusp topology. The geometric bounds are explicit auxiliary hypotheses, to be discharged by actual finite polygon geometry. -/
theorem fuchsianCuspSubsetInclusion_continuous_of_cusp_bounds {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (K : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    (hK : ∀z∈K,z∈D.carrier∨∃(c : FuchsianCyclicConjugacyClasses D .parabolic)(g : H),
      g.val.val (fuchsianParabolicPointRepresentative D c).val=z)
    (hb : ∀(c : FuchsianCyclicConjugacyClasses D .parabolic)(g : H),∃M h : ℝ,
      ∀z∈K,∀w : ℂ,((fuchsianCuspChartNormalization D
        c).normalizer*g.val⁻¹).val z=(w:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)→
        |w.re|≤M∧h≤w.im) :
    Continuous (fuchsianCuspSubsetInclusion D K hK) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  rcases hK x.val x.property with hxD|⟨c,g,hg⟩
  · exact fuchsianCuspSubsetInclusion_continuousAt_old D K hK x hxD
  · let C:=fuchsianCuspChartNormalization D
    let f:=fuchsianCuspSubsetInclusion D K hK
    let q:=(C c).normalizer*g.val⁻¹
    have hqp : q.val x.val=∞:=by
      change (C c).normalizer.val (g.val.val.symm x.val)=∞
      have hinv : g.val.val.symm x.val=(fuchsianParabolicPointRepresentative D c).val:=by
        rw [←hg,Equiv.symm_apply_apply]
      rw [hinv,(C c).cusp_eq]
    have hfx : f x=_root_.LowDimensionalTopology.Geometry.Surfaces.multipleCuspAugmentedPiece C c
        (_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusCuspAugmentedCusp (C c) g
          (_root_.LowDimensionalTopology.Geometry.Surfaces.stableCuspCompletionInfinity (C
          c).height)):=Subtype.ext hg.symm
    obtain ⟨M,h,hbound⟩:=hb c g
    show Tendsto f (𝓝 x) (𝓝 (f x))
    apply tendsto_def.mpr
    intro V hV
    rw [hfx] at hV
    obtain ⟨t,ht,hsub⟩:=(_root_.LowDimensionalTopology.Geometry.Surfaces.multipleCusp_mem_nhds_iff C D.discontinuous
      (fuchsianParabolicPointRepresentative_orbits_distinct D)
      (fuchsianCuspChart_full_stabilizer D) c g V).mp hV
    obtain ⟨U,hU,hxU,hhigh⟩:=cusp_height_tail_sphere_neighborhood K q x.val hqp M h hbound t
    have hUn : (Subtype.val : K→_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ⁻¹' U∈𝓝 x:=
      (hU.preimage continuous_subtype_val).mem_nhds hxU
    apply mem_of_superset hUn
    intro z hz
    apply hsub
    rcases hhigh z.val ⟨z.property,hz⟩ with hInf|⟨w,hw,hqw⟩
    · left
      apply q.val.injective
      change q.val z.val=q.val (g.val.val (fuchsianParabolicPointRepresentative D c).val)
      rw [hInf]
      change (∞:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=(C c).normalizer • (g.val⁻¹ • (g.val •
        (fuchsianParabolicPointRepresentative D c).val))
      rw [inv_smul_smul]
      exact (C c).cusp_eq.symm
    · right
      refine ⟨w,hw,?_⟩
      apply q.val.injective
      change ((C c).normalizer*g.val⁻¹) • (g.val • ((C c).normalizer⁻¹ •
        (w:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)))=q.val z.val
      simp only [mul_smul,inv_smul_smul,smul_inv_smul]
      exact hqw.symm

/-- The actual orbit projection of the unchanged inclusion into the genuine all-cusp completion. -/
def fuchsianCuspSubsetProjection {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D :
  FuchsianDisc H)
    (K : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    (hK : ∀z∈K,z∈D.carrier∨∃(c : FuchsianCyclicConjugacyClasses D .parabolic)(g : H),
      g.val.val (fuchsianParabolicPointRepresentative D c).val=z) : K→FuchsianCuspCompletion D :=
  Quotient.mk _ ∘ fuchsianCuspSubsetInclusion D K hK

/-- The actual completion projection is continuous whenever the proved genuine cusp-coordinate bounds hold. -/
theorem fuchsianCuspSubsetProjection_continuous {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (K : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    (hK : ∀z∈K,z∈D.carrier∨∃(c : FuchsianCyclicConjugacyClasses D .parabolic)(g : H),
      g.val.val (fuchsianParabolicPointRepresentative D c).val=z)
    (hb : ∀(c : FuchsianCyclicConjugacyClasses D .parabolic)(g : H),∃M h : ℝ,
      ∀z∈K,∀w : ℂ,((fuchsianCuspChartNormalization D
        c).normalizer*g.val⁻¹).val z=(w:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)→
        |w.re|≤M∧h≤w.im) :
    Continuous (fuchsianCuspSubsetProjection D K hK) :=
  continuous_quot_mk.comp (fuchsianCuspSubsetInclusion_continuous_of_cusp_bounds D K hK hb)

/-- Meeting every actual augmented orbit makes the literal subset projection onto the genuine completion. -/
theorem fuchsianCuspSubsetProjection_surjective {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (K : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    (hK : ∀z∈K,z∈D.carrier∨∃(c : FuchsianCyclicConjugacyClasses D .parabolic)(g : H),
      g.val.val (fuchsianParabolicPointRepresentative D c).val=z)
    (hcover : ∀z : _root_.LowDimensionalTopology.Geometry.Surfaces.MultipleCuspAugmentedDomain
      (fuchsianCuspChartNormalization D),
      ∃w∈K,∃g : H,g.val.val z.val=w) :
    Function.Surjective (fuchsianCuspSubsetProjection D K hK) := by
  intro x
  induction x using Quotient.inductionOn with
  | h z=>
    obtain ⟨w,hw,g,hg⟩:=hcover z
    refine ⟨⟨w,hw⟩,?_⟩
    exact Quotient.sound ⟨g,Subtype.ext hg⟩

/-- A genuine compact sphere subset, actual cusp-coordinate bounds and actual orbit coverage imply compactness of the unchanged all-cusp completion. Each explicit auxiliary hypothesis still needs a geometric proof in a finite-area application. -/
theorem fuchsianCuspCompletion_compact_of_bounded_compact_cover {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (K : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hcompact : IsCompact
      K)
    (hK : ∀z∈K,z∈D.carrier∨∃(c : FuchsianCyclicConjugacyClasses D .parabolic)(g : H),
      g.val.val (fuchsianParabolicPointRepresentative D c).val=z)
    (hb : ∀(c : FuchsianCyclicConjugacyClasses D .parabolic)(g : H),∃M h : ℝ,
      ∀z∈K,∀w : ℂ,((fuchsianCuspChartNormalization D
        c).normalizer*g.val⁻¹).val z=(w:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)→
        |w.re|≤M∧h≤w.im)
    (hcover : ∀z : _root_.LowDimensionalTopology.Geometry.Surfaces.MultipleCuspAugmentedDomain
      (fuchsianCuspChartNormalization D),
      ∃w∈K,∃g : H,g.val.val z.val=w) : CompactSpace (FuchsianCuspCompletion D) := by
  let :=isCompact_iff_compactSpace.mp hcompact
  have hc:=isCompact_univ.image (fuchsianCuspSubsetProjection_continuous D K hK hb)
  rw [image_univ,(fuchsianCuspSubsetProjection_surjective D K hK hcover).range_eq] at hc
  exact isCompact_univ_iff.mp hc

end LowDimensionalTopology.Geometry.Fuchsian
