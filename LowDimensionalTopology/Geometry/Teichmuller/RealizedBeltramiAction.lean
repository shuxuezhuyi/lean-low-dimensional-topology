module

public import LowDimensionalTopology.Geometry.Teichmuller.RealizedBeltrami
public import LowDimensionalTopology.Geometry.Teichmuller.Moduli
public import Mathlib.Algebra.Group.Subgroup.Actions

/-!
# The diffeomorphism action on actually realized Beltrami coefficients

The action is inverse precomposition of a smooth marking. Independence of the
chosen realizing marking uses an analytic target homeomorphism carrying the
markings exactly; equality of Teichmüller classes alone would not suffice.
The acting group and its homotopy identity subgroup are the existing genuine
orientation-preserving smooth automorphisms of the reference surface.
-/

@[expose] public section

noncomputable section

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces

universe u v

namespace MarkedRiemannSurface

variable {X : Type u} [TopologicalSpace X] {R : ClosedRiemannSurface X}

/-- An analytic target change carrying the markings exactly preserves their
literal continuous Beltrami coefficients. -/
theorem beltramiCoefficient_eq_of_analytic_homeomorph
    (M N : MarkedRiemannSurface.{u, v} R) (h : M.carrier ≃ₜ N.carrier)
    (hh : RiemannAnalyticMap M.surface.toRiemannAtlas N.surface.toRiemannAtlas h)
    (hmark : ∀ x : X, h (M.marking.toHomeomorph x) = N.marking.toHomeomorph x) :
    M.beltramiCoefficient = N.beltramiCoefficient := by
  apply (M.beltramiCoefficient_eq_iff N).2
  change M.marking.beltrami M.orientation_preserving =
    N.marking.beltrami N.orientation_preserving
  exact (M.marking.beltrami_eq_iff_exists_analytic_homeomorph N.marking
    M.orientation_preserving N.orientation_preserving).2
    ⟨h, hh, riemannAnalyticMap_homeomorph_symm h hh, hmark⟩

/-- Literal coefficient equality is preserved by every common smooth oriented
precomposition, even though its actual realizing targets may differ. -/
theorem beltramiCoefficient_precompose_eq
    (f : SmoothSurfaceEquiv R.toRiemannSurface R.toRiemannSurface)
    (hf : PreservesComplexOrientation R.toRiemannAtlas R.toRiemannAtlas f.toHomeomorph)
    {M N : MarkedRiemannSurface.{u, v} R}
    (hMN : M.beltramiCoefficient = N.beltramiCoefficient) :
    (precompose f hf M).beltramiCoefficient = (precompose f hf N).beltramiCoefficient := by
  have hμ : M.marking.beltrami M.orientation_preserving =
      N.marking.beltrami N.orientation_preserving :=
    (M.beltramiCoefficient_eq_iff N).1 hMN
  obtain ⟨h, hh, _hhInv, hmark⟩ :=
    (M.marking.beltrami_eq_iff_exists_analytic_homeomorph N.marking
      M.orientation_preserving N.orientation_preserving).1 hμ
  apply beltramiCoefficient_eq_of_analytic_homeomorph
    (precompose f hf M) (precompose f hf N) h hh
  intro x
  exact hmark (f.toHomeomorph x)

/-- Change a marking by the inverse of a genuine oriented automorphism. -/
def changeMarking (a : OrientedSurfaceAut R) (M : MarkedRiemannSurface.{u, v} R) :
    MarkedRiemannSurface.{u, v} R :=
  precompose (a⁻¹).smooth (a⁻¹).orientation_preserving M

@[simp]
theorem changeMarking_one (M : MarkedRiemannSurface.{u, v} R) :
    changeMarking 1 M = M := by
  change precompose (SmoothSurfaceEquiv.refl R.toRiemannSurface)
    (preservesComplexOrientation_id R.toRiemannAtlas) M = M
  exact precompose_refl M

/-- The composition order agrees with the left diffeomorphism action. -/
theorem changeMarking_mul (a b : OrientedSurfaceAut R)
    (M : MarkedRiemannSurface.{u, v} R) :
    changeMarking (a * b) M = changeMarking a (changeMarking b M) := by
  symm
  exact precompose_trans (a⁻¹).smooth (b⁻¹).smooth
    (a⁻¹).orientation_preserving (b⁻¹).orientation_preserving M

/-- Changing the reference marking leaves its target unchanged. -/
theorem targetEquivalent_changeMarking (a : OrientedSurfaceAut R)
    (M : MarkedRiemannSurface.{u, v} R) : TargetEquivalent (changeMarking a M) M :=
  targetEquivalent_precompose (a⁻¹).smooth (a⁻¹).orientation_preserving M

end MarkedRiemannSurface

namespace RealizedBeltramiCoefficients

variable {X : Type u} [TopologicalSpace X] {R : ClosedRiemannSurface X}

/-- The selected realization has precisely the original realized coefficient. -/
@[simp]
theorem ofMarked_representative (μ : RealizedBeltramiCoefficients.{u, v} R) :
    ofMarked μ.representative = μ := by
  apply Subtype.ext
  exact μ.representative_coefficient

/-- Every actual coefficient is the coefficient of an actual marking. -/
theorem ofMarked_surjective : Function.Surjective
    (ofMarked : MarkedRiemannSurface.{u, v} R → RealizedBeltramiCoefficients.{u, v} R) := by
  intro μ
  exact ⟨μ.representative, ofMarked_representative μ⟩

/-- Apply inverse precomposition to a selected actual realization. -/
def changeReference (a : OrientedSurfaceAut R) (μ : RealizedBeltramiCoefficients.{u, v} R) :
    RealizedBeltramiCoefficients.{u, v} R :=
  ofMarked (MarkedRiemannSurface.changeMarking a μ.representative)

/-- The action is independent of the realization, because exact analytic target
changes commute with common precomposition of the markings. -/
theorem changeReference_ofMarked (a : OrientedSurfaceAut R)
    (M : MarkedRiemannSurface.{u, v} R) :
    changeReference a (ofMarked M) = ofMarked (MarkedRiemannSurface.changeMarking a M) := by
  apply Subtype.ext
  exact MarkedRiemannSurface.beltramiCoefficient_precompose_eq
    (a⁻¹).smooth (a⁻¹).orientation_preserving
    (representative_coefficient (ofMarked M))

/-- The genuine left action `a ⋆ μ_f = μ_(f ∘ a⁻¹)`. -/
instance (R : ClosedRiemannSurface X) :
    MulAction (OrientedSurfaceAut R) (RealizedBeltramiCoefficients.{u, v} R) where
  smul := changeReference
  one_smul μ := by
    obtain ⟨M, rfl⟩ := ofMarked_surjective μ
    change changeReference 1 (ofMarked M) = ofMarked M
    rw [changeReference_ofMarked, MarkedRiemannSurface.changeMarking_one]
  mul_smul a b μ := by
    obtain ⟨M, rfl⟩ := ofMarked_surjective μ
    change changeReference (a * b) (ofMarked M) =
      changeReference a (changeReference b (ofMarked M))
    simp only [changeReference_ofMarked, MarkedRiemannSurface.changeMarking_mul]

/-- Compute the diffeomorphism action using any actual realizing marking. -/
@[simp]
theorem smul_ofMarked (a : OrientedSurfaceAut R) (M : MarkedRiemannSurface.{u, v} R) :
    a • ofMarked M = ofMarked (MarkedRiemannSurface.changeMarking a M) :=
  changeReference_ofMarked a M

/-- The coefficient projection respects the already constructed genuine
diffeomorphism action on native Teichmüller classes. -/
@[simp]
theorem beta_smul (a : OrientedSurfaceAut R) (μ : RealizedBeltramiCoefficients.{u, v} R) :
    beta (a • μ) = a • beta μ := by
  obtain ⟨M, rfl⟩ := ofMarked_surjective μ
  simp only [smul_ofMarked, beta_ofMarked]
  rfl

/-- The homotopy identity subgroup acts within each fiber of the actual
coefficient projection to Teichmüller space. -/
@[simp]
theorem beta_homotopyIdentity_smul
    (a : OrientedSurfaceAut.homotopyIdentitySubgroup R)
    (μ : RealizedBeltramiCoefficients.{u, v} R) : beta (a • μ) = beta μ := by
  change beta ((a : OrientedSurfaceAut R) • μ) = beta μ
  rw [beta_smul]
  change TeichmullerSpace.precompose
    ((a : OrientedSurfaceAut R)⁻¹).smooth
    ((a : OrientedSurfaceAut R)⁻¹).orientation_preserving (beta μ) = beta μ
  have hinv : ContinuousMap.Homotopic
      ((a : OrientedSurfaceAut R)⁻¹).continuousMap (ContinuousMap.id X) :=
    (OrientedSurfaceAut.homotopyIdentitySubgroup R).inv_mem a.property
  exact (TeichmullerSpace.precompose_eq_of_homotopic
    ((a : OrientedSurfaceAut R)⁻¹).smooth
    (SmoothSurfaceEquiv.refl R.toRiemannSurface)
    ((a : OrientedSurfaceAut R)⁻¹).orientation_preserving
    (preservesComplexOrientation_id R.toRiemannAtlas) hinv (beta μ)).trans
      (TeichmullerSpace.precompose_refl (beta μ))

end RealizedBeltramiCoefficients

end LowDimensionalTopology.Geometry.Teichmuller
