module

public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.TubularGeodesicNeighborhood
public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.CyclicHyperbolicAnnulus
public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.OriginalSimpleClosedGeodesic

/-!
# Embedded intrinsic collars in an actual complete cyclic cylinder

The cylinder is the whole original disc quotient by the cyclic subgroup of an
actual full-period deck element. The collar map inverts the actual cyclic
covering on the two tubes, identifies the actual core, and preserves the full
native length of every rectifiable path in both directions.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped ENNReal unitInterval

namespace LowDimensionalTopology.Geometry.Surfaces
open LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.DiscreteGroups

variable {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}

/-- The actual whole disc is invariant under the original element's powers. -/
theorem HyperbolicSurfaceModel.cyclicQuotientInvariant
    (M : HyperbolicSurfaceModel R) (f : M.group) :
    ∀ (g : Subgroup.zpowers f.val) z, z ∈ extendedUnitDisc → g • z ∈ extendedUnitDisc :=
  fun g z hz => M.invariant
    ⟨g.val, (Subgroup.zpowers_le.mpr f.property) g.property⟩ z hz

/-- The cyclic quotient uses the entire original covering disc. -/
def HyperbolicSurfaceModel.cyclicQuotientDomain
    (M : HyperbolicSurfaceModel R) (f : M.group) :
    MobiusInvariantDomain (Subgroup.zpowers f.val) :=
  unitDiscMobiusInvariantDomain _ (M.cyclicQuotientInvariant f)

/-- Compact-hit discontinuity is inherited from the original actual group. -/
theorem HyperbolicSurfaceModel.cyclicQuotientDiscontinuous
    (M : HyperbolicSurfaceModel R) (f : M.group) :
    IsMobiusDiscontinuousOn (Subgroup.zpowers f.val) extendedUnitDisc := by
  intro K hK hKD
  let i : Subgroup.zpowers f.val → M.group :=
    fun g => ⟨g.val, (Subgroup.zpowers_le.mpr f.property) g.property⟩
  have hi : Function.Injective i := by
    intro a b hab
    exact Subtype.ext (congrArg (fun g : M.group => g.val) hab)
  exact Set.Finite.preimage (f := i) hi.injOn (M.discontinuous K hK hKD)

/-- The literal cyclic quotient has its actual quotient Riemann atlas. -/
def HyperbolicSurfaceModel.cyclicQuotientSurface
    (M : HyperbolicSurfaceModel R) (f : M.group) :
    RiemannSurface (MobiusDomainQuotient (M.cyclicQuotientDomain f)) :=
  mobiusQuotientRiemannSurface (M.cyclicQuotientDomain f) (M.cyclicQuotientDiscontinuous f)

/-- Native hyperbolic length on the cyclic quotient uses the identity model. -/
def HyperbolicSurfaceModel.cyclicQuotientModel
    (M : HyperbolicSurfaceModel R) (f : M.group) :
    HyperbolicSurfaceModel (M.cyclicQuotientSurface f) where
  group := Subgroup.zpowers f.val
  invariant := M.cyclicQuotientInvariant f
  discontinuous := M.cyclicQuotientDiscontinuous f
  no_elliptic := fun g hg hne =>
    M.no_elliptic g ((Subgroup.zpowers_le.mpr f.property) hg) hne
  homeomorph := Homeomorph.refl _
  analytic := RiemannAnalyticMap.id _

/-- One complete original geodesic period lifts from a point to its image
under the specified actual disc deck transformation. -/
def OriginalClosedGeodesic.HasDiscPeriod
    {M : HyperbolicSurfaceModel R} (q : OriginalClosedGeodesic M)
    (f : complexMobiusGroup) : Prop :=
  ∃ c : C(I, extendedUnitDisc),
    (∀ t : I, M.discCover (c t) = q.toLoop.2 t) ∧
      (c 1).val = f • (c 0).val

/-- An embedded collar identifies the actual original tube with the same-width
core tube of its complete cyclic cylinder, with normalized conformal modulus
and preservation of all original rectifiable path lengths. -/
def OriginalClosedGeodesic.AdmitsEmbeddedDeltaCollar
    {M : HyperbolicSurfaceModel R} (q : OriginalClosedGeodesic M) (δ : ℝ) : Prop :=
  Function.Injective (q.periodic.lift : AddCircle (1 : ℝ) → X) ∧ 0 < δ ∧
    ∃ f : M.group, MobiusHyperbolic f.val ∧ q.HasDiscPeriod f.val ∧
      let S := M.cyclicQuotientSurface f
      let N := M.cyclicQuotientModel f
      let C := MobiusDomainQuotient (M.cyclicQuotientDomain f)
      ∃ core : OriginalClosedGeodesic N,
        core.HasDiscPeriod f.val ∧
        Function.Injective (core.periodic.lift : AddCircle (1 : ℝ) → C) ∧
        core.length = q.length ∧
        let r := Real.exp (2 * Real.pi ^ 2 / q.length.toReal)
        Real.log r / (2 * Real.pi) = Real.pi / q.length.toReal ∧
        ∃ hr : 1 < r, ∃ a : C ≃ₜ LiZhongQC.annulus 1 r,
          RiemannAnalyticMap S.toRiemannAtlas (roundAnnulusSurface r hr).toRiemannAtlas a ∧
          ∃ F : C(C, X), IsCoveringMap F ∧
            RiemannAnalyticMap S.toRiemannAtlas R.toRiemannAtlas F ∧
            (∀ z : extendedUnitDisc, F (N.discCover z) = M.discCover z) ∧
            let U := q.tubularNeighborhood δ
            let V := core.tubularNeighborhood δ
            ∃ E : U ≃ₜ V,
              (∀ x : U, F (E x : C) = (x : X)) ∧
              E '' {x : U | (x : X) ∈ Set.range q.curve} =
                {y : V | (y : C) ∈ Set.range core.curve} ∧
              ∀ α : C(I, U),
                let αX := (ContinuousMap.subtypeVal U).comp α
                let αC := (ContinuousMap.subtypeVal V).comp
                  ((_root_.toContinuousMap E).comp α)
                (R.toRiemannAtlas.IsRectifiableCurve αX ↔
                  S.toRiemannAtlas.IsRectifiableCurve αC) ∧
                ∀ (hX : R.toRiemannAtlas.IsRectifiableCurve αX)
                  (hC : S.toRiemannAtlas.IsRectifiableCurve αC),
                  M.rectifiableCurveLength ⟨αX, hX⟩ = N.rectifiableCurveLength ⟨αC, hC⟩

end LowDimensionalTopology.Geometry.Surfaces
