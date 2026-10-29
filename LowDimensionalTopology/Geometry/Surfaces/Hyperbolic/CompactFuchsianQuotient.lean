module

public import LowDimensionalTopology.Geometry.Fuchsian.Generation.ThreeHalfTurns.SmallLambdaTriangleReduction
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.FirstKindShortSignatures
public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.QuotientMetric

/-!
# Compact free Fuchsian quotients contain only hyperbolic nonidentity elements

Actual compactness rules out parabolic cusp classes. The existing equivalence
between geometric element types and maximal cyclic classes then rules out
parabolic elements themselves. The remaining type is hyperbolic because the
whole action preserves a genuine complex disc.
-/

@[expose] public section

namespace LowDimensionalTopology.Geometry.Fuchsian

open LowDimensionalTopology.Geometry

/-- No actual parabolic element survives in a compact Fuchsian quotient. -/
theorem FuchsianDisc.not_parabolic_of_compact_quotient
    {H : Subgroup Mobius.complexMobiusGroup} (D : FuchsianDisc H)
    [CompactSpace (Surfaces.MobiusDomainQuotient D.domain)]
    (f : Mobius.complexMobiusGroup) (hf : f ∈ H) :
    ¬Mobius.MobiusParabolic f :=
  (fuchsianCyclicConjugacyClasses_isEmpty_iff D .parabolic).mp
    (compactCusps_classes_isEmpty_of_compact_quotient D) f hf

/-- For an actual free compact Fuchsian quotient, every nonidentity element is
hyperbolic, without a selected polygon or chosen generator system. -/
theorem FuchsianDisc.hyperbolic_of_compact_quotient
    {H : Subgroup Mobius.complexMobiusGroup} (D : FuchsianDisc H)
    [CompactSpace (Surfaces.MobiusDomainQuotient D.domain)]
    (hno : ∀ f ∈ H, ¬Mobius.MobiusElliptic f)
    (f : Mobius.complexMobiusGroup) (hf : f ∈ H) (hfn : f ≠ 1) :
    Mobius.MobiusHyperbolic f := by
  rcases Mobius.mobius_nonidentity_type_trichotomy f hfn with hp | hl | he
  · exact (D.not_parabolic_of_compact_quotient f hf hp).elim
  · exact D.loxodromic_hyperbolic ⟨f, hf⟩ hl
  · exact (hno f hf he).elim

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Surfaces

open LowDimensionalTopology.Geometry

/-- Every actual Fuchsian model of a compact original surface contains only
hyperbolic nonidentity elements. The proof retains the given original quotient
homeomorphism and does not replace the model by a selected polygon group. -/
theorem HyperbolicSurfaceModel.hyperbolic_of_compact
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {R : RiemannSurface X} (M : HyperbolicSurfaceModel R)
    (f : Mobius.complexMobiusGroup) (hf : f ∈ M.group) (hfn : f ≠ 1) :
    Mobius.MobiusHyperbolic f := by
  let D : Fuchsian.FuchsianDisc M.group :=
    { carrier := Hyperbolic.extendedUnitDisc
      isDisc := DiscreteGroups.extendedUnitDisc_isComplexOpenDisc
      invariant := M.invariant
      discontinuous := M.discontinuous }
  let : CompactSpace (MobiusDomainQuotient D.domain) := M.homeomorph.compactSpace
  apply D.hyperbolic_of_compact_quotient
    (fun g hg he => M.no_elliptic g hg he.1 he) f hf hfn

end LowDimensionalTopology.Geometry.Surfaces
