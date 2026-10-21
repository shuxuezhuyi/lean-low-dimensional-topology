/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Cusp.CuspRestrictedTopology
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

/-- The literal original sphere orbit relation restricted to a sphere subset; the subset need not be invariant. -/
def sphereSubsetOrbitSetoid (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (K : Set
  _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) : Setoid K:=
  Setoid.comap Subtype.val (MulAction.orbitRel H _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)

/-- The genuine quotient topology of the original restricted sphere orbit relation. -/
abbrev SphereSubsetOrbitQuotient (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (K :
  Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) :=
  Quotient (sphereSubsetOrbitSetoid H K)

/-- The genuine completion identifies two subset representatives exactly when they are related by an original whole-group sphere transformation. -/
theorem fuchsianCuspSubsetProjection_eq_iff {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (K : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    (hK : ∀z∈K,z∈D.carrier∨∃(c : FuchsianCyclicConjugacyClasses D .parabolic)(g : H),
      g.val.val (fuchsianParabolicPointRepresentative D c).val=z) (x y : K) :
    fuchsianCuspSubsetProjection D K hK x=fuchsianCuspSubsetProjection D K hK y ↔
      sphereSubsetOrbitSetoid H K x y := by
  constructor
  · intro he
    obtain ⟨g,hg⟩:=Quotient.exact he
    exact ⟨g,congrArg Subtype.val hg⟩
  · rintro ⟨g,hg⟩
    exact Quotient.sound ⟨g,Subtype.ext hg⟩

/-- The actual restricted orbit quotient maps to the unchanged genuine all-cusp completion. -/
def fuchsianCuspSubsetOrbitMap {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (K : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    (hK : ∀z∈K,z∈D.carrier∨∃(c : FuchsianCyclicConjugacyClasses D .parabolic)(g : H),
      g.val.val (fuchsianParabolicPointRepresentative D c).val=z) :
    SphereSubsetOrbitQuotient H K→FuchsianCuspCompletion D :=
  Quotient.lift (fuchsianCuspSubsetProjection D K hK)
    (fun x y hxy=>(fuchsianCuspSubsetProjection_eq_iff D K hK x y).mpr hxy)

/-- Its projection agrees with the actual original representatives. -/
theorem fuchsianCuspSubsetOrbitMap_projection {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (K : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    (hK : ∀z∈K,z∈D.carrier∨∃(c : FuchsianCyclicConjugacyClasses D .parabolic)(g : H),
      g.val.val (fuchsianParabolicPointRepresentative D c).val=z) (z : K) :
    fuchsianCuspSubsetOrbitMap D K hK (Quotient.mk _ z)=fuchsianCuspSubsetProjection D K hK z := rfl

/-- No additional relation is introduced by the genuine completion map. -/
theorem fuchsianCuspSubsetOrbitMap_injective {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (K : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    (hK : ∀z∈K,z∈D.carrier∨∃(c : FuchsianCyclicConjugacyClasses D .parabolic)(g : H),
      g.val.val (fuchsianParabolicPointRepresentative D c).val=z) :
    Function.Injective (fuchsianCuspSubsetOrbitMap D K hK) := by
  intro x y
  induction x using Quotient.inductionOn with
  | h x=>
    induction y using Quotient.inductionOn with
    | h y=>
      intro hxy
      exact Quotient.sound ((fuchsianCuspSubsetProjection_eq_iff D K hK x y).mp hxy)

/-- Actual orbit coverage makes the restricted quotient map onto. -/
theorem fuchsianCuspSubsetOrbitMap_surjective {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (K : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    (hK : ∀z∈K,z∈D.carrier∨∃(c : FuchsianCyclicConjugacyClasses D .parabolic)(g : H),
      g.val.val (fuchsianParabolicPointRepresentative D c).val=z)
    (hcover : ∀z : _root_.LowDimensionalTopology.Geometry.Surfaces.MultipleCuspAugmentedDomain
      (fuchsianCuspChartNormalization D),
      ∃w∈K,∃g : H,g.val.val z.val=w) : Function.Surjective (fuchsianCuspSubsetOrbitMap D K hK) := by
  intro x
  obtain ⟨z,hz⟩:=fuchsianCuspSubsetProjection_surjective D K hK hcover x
  exact ⟨Quotient.mk _ z,hz⟩

/-- Genuine cusp-coordinate bounds give continuity for the actual restricted quotient topology. -/
theorem fuchsianCuspSubsetOrbitMap_continuous {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (K : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    (hK : ∀z∈K,z∈D.carrier∨∃(c : FuchsianCyclicConjugacyClasses D .parabolic)(g : H),
      g.val.val (fuchsianParabolicPointRepresentative D c).val=z)
    (hb : ∀(c : FuchsianCyclicConjugacyClasses D .parabolic)(g : H),∃M h : ℝ,
      ∀z∈K,∀w : ℂ,((fuchsianCuspChartNormalization D
        c).normalizer*g.val⁻¹).val z=(w:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)→
        |w.re|≤M∧h≤w.im) : Continuous (fuchsianCuspSubsetOrbitMap D K hK) :=
  (fuchsianCuspSubsetProjection_continuous D K hK hb).quotient_lift _

/-- A compact actual sphere subset meeting all augmented orbits identifies the literal restricted orbit quotient homeomorphically with the original all-cusp completion. All geometric auxiliary hypotheses remain explicit. -/
def fuchsianCuspSubsetOrbitHomeomorph {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
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
      ∃w∈K,∃g : H,g.val.val z.val=w) :
    SphereSubsetOrbitQuotient H K≃ₜFuchsianCuspCompletion D := by
  let :=isCompact_iff_compactSpace.mp hcompact
  let :=fuchsianCuspCompletion_t2Space D
  exact IsHomeomorph.homeomorph _ (isHomeomorph_iff_continuous_bijective.mpr
    ⟨fuchsianCuspSubsetOrbitMap_continuous D K hK hb,
      fuchsianCuspSubsetOrbitMap_injective D K hK,fuchsianCuspSubsetOrbitMap_surjective D K hK hcover⟩)

/-- The genuine homeomorphism keeps the unchanged original projection on every literal compact representative. -/
theorem fuchsianCuspSubsetOrbitHomeomorph_projection {H : Subgroup
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
      ∃w∈K,∃g : H,g.val.val z.val=w) (z : K) :
    fuchsianCuspSubsetOrbitHomeomorph D K hcompact hK hb hcover (Quotient.mk _ z)=
      fuchsianCuspSubsetProjection D K hK z := rfl

/-- At an actual original-domain representative the restricted quotient map is the unchanged original quotient inclusion. -/
theorem fuchsianCuspSubsetOrbitMap_old {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (K : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    (hK : ∀z∈K,z∈D.carrier∨∃(c : FuchsianCyclicConjugacyClasses D .parabolic)(g : H),
      g.val.val (fuchsianParabolicPointRepresentative D c).val=z) (z : K) (hz : z.val∈D.carrier) :
    fuchsianCuspSubsetOrbitMap D K hK (Quotient.mk _ z)=
      fuchsianCuspCompletionOld D (_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainProjection D.domain
        ⟨z.val,hz⟩) := rfl

/-- At every actual original parabolic orbit representative the restricted quotient retains its exact actual cusp-class label. -/
theorem fuchsianCuspSubsetOrbitMap_cusp {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (K : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    (hK : ∀z∈K,z∈D.carrier∨∃(c : FuchsianCyclicConjugacyClasses D .parabolic)(g : H),
      g.val.val (fuchsianParabolicPointRepresentative D c).val=z) (z : K)
    (c : FuchsianCyclicConjugacyClasses D .parabolic) (g : H)
    (hg : g.val.val (fuchsianParabolicPointRepresentative D c).val=z.val) :
    fuchsianCuspSubsetOrbitMap D K hK (Quotient.mk _ z)=fuchsianCuspCompletionPoint D c := by
  apply Quotient.sound
  refine ⟨g,Subtype.ext ?_⟩
  change g • ((1:H) • (fuchsianParabolicPointRepresentative D c).val)=z.val
  rw [one_smul]
  exact hg

end LowDimensionalTopology.Geometry.Fuchsian
