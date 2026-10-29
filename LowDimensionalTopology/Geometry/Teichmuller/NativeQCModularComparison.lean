module

public import LowDimensionalTopology.Geometry.Teichmuller.MappingClassGroup
public import LowDimensionalTopology.Geometry.Teichmuller.SourceMarking
public import LowDimensionalTopology.Geometry.Teichmuller.SourceQCModularAction
public import LowDimensionalTopology.Geometry.Teichmuller.NativeTeichmullerMetric

/-!
# The original smooth mapping classes inside the full QC modular group

The compact smooth-to-QC theorem retains the underlying homeomorphism.
Both actual quotient relations are free homotopy, so this gives an injective
group homomorphism. The unchanged marking maps identify the two inverse
precomposition actions. Consequently the original full-log distance and its
conjugated displacement are preserved. No new smoothing or marking premise
is used.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces

variable {X : Type} [TopologicalSpace X]

namespace OrientedSurfaceAut

variable {R : ClosedRiemannSurface X}

/-- The same original positive smooth automorphism, with its existing QC proof. -/
def toQC (f : OrientedSurfaceAut R) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    SourceQCModular.Aut X := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R.compactSpace
  exact ⟨f.toHomeomorph, f.smooth.isQCRS_of_compact f.orientation_preserving⟩

/-- Retaining that actual homeomorphism preserves the composition group law. -/
def toQCHom (R : ClosedRiemannSurface X) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    OrientedSurfaceAut R →* SourceQCModular.Aut X := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  exact
    { toFun := toQC
      map_one' := rfl
      map_mul' := fun _ _ => rfl }

end OrientedSurfaceAut

namespace MappingClassGroup

/-- The native smooth mapping class has its actual full-QC homotopy class. -/
def toQCModular (R : ClosedRiemannSurface X) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    MappingClassGroup R →* SourceQCModular.ModularGroup X := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  exact QuotientGroup.map (OrientedSurfaceAut.homotopyIdentitySubgroup R)
    (SourceQCModular.homotopyIdentitySubgroup X) (OrientedSurfaceAut.toQCHom R)
    (by intro f hf; exact hf)

/-- The descended homomorphism keeps the precise original representative. -/
@[simp] theorem toQCModular_mk (R : ClosedRiemannSurface X)
    (f : OrientedSurfaceAut R) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    toQCModular R (mk f) = SourceQCModular.mk f.toQC := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  rfl

/-- The two quotients identify exactly the same actual smooth representatives. -/
theorem toQCModular_injective (R : ClosedRiemannSurface X) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    Function.Injective (toQCModular R) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  intro a b
  refine Quotient.inductionOn₂ a b ?_
  intro f g h
  change mk f = mk g
  apply (mk_eq_mk_iff_homotopic f g).2
  change SourceQCModular.mk f.toQC = SourceQCModular.mk g.toQC at h
  exact (SourceQCModular.mk_eq_mk_iff_homotopic f.toQC g.toQC).1 h

end MappingClassGroup

namespace TeichmullerSpace

/-- Forgetting smoothness intertwines the two actual inverse-precomposition actions. -/
theorem toSource_smul (R : ClosedRiemannSurface X) (χ : MappingClassGroup R)
    (p : TeichmullerSpace.{0, 0} R) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    toSource R (χ • p) = MappingClassGroup.toQCModular R χ • toSource R p := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  refine Quotient.inductionOn₂ χ p ?_
  intro f M
  rfl

/-- The native mapping class action preserves the original full-log QC distance. -/
theorem fromQCDistance_smul (R : ClosedRiemannSurface X) (χ : MappingClassGroup R)
    (p q : TeichmullerSpace.{0, 0} R) :
    fromQCDistance R (χ • p) (χ • q) = fromQCDistance R p q := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  change QCBookMetric.bookDistance (toSource R (χ • p)) (toSource R (χ • q)) =
    QCBookMetric.bookDistance (toSource R p) (toSource R q)
  rw [toSource_smul, toSource_smul, SourceQCModular.bookDistance_smul]

/-- Adjusting the actual marked point conjugates its full-QC displacement
by the same native mapping class, in the original full-log convention. -/
theorem bookDistance_conjugate_toSource_smul (R : ClosedRiemannSurface X)
    (χ : MappingClassGroup R) (p : TeichmullerSpace.{0, 0} R) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    ∀ γ : SourceQCModular.ModularGroup X,
      QCBookMetric.bookDistance (toSource R (χ • p))
          ((MappingClassGroup.toQCModular R χ * γ *
              (MappingClassGroup.toQCModular R χ)⁻¹) • toSource R (χ • p)) =
        QCBookMetric.bookDistance (toSource R p) (γ • toSource R p) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  intro γ
  simp only [toSource_smul, mul_smul, inv_smul_smul]
  exact SourceQCModular.bookDistance_smul (MappingClassGroup.toQCModular R χ)
    (toSource R p) (γ • toSource R p)

end TeichmullerSpace

end LowDimensionalTopology.Geometry.Teichmuller
