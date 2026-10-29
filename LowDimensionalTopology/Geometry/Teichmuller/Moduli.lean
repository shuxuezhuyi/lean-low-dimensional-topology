module

public import LowDimensionalTopology.Geometry.Teichmuller.ConformalSmooth
public import Mathlib.GroupTheory.GroupAction.Defs

/-!
# Forgetting markings and the mapping class group quotient

The unmarked objects here are precisely the targets of the marked surfaces
already under consideration. Their equivalence is actual biholomorphic
homeomorphism. No assertion that every surface of a given genus admits such
a marking is needed for the comparison with mapping class group orbits.
-/

@[expose] public section

noncomputable section

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces

universe u v

namespace MarkedRiemannSurface

variable {X : Type u} [TopologicalSpace X] {R : ClosedRiemannSurface X}

/-- The target Riemann surfaces are biholomorphic, independently of their markings. -/
def TargetEquivalent (M N : MarkedRiemannSurface.{u, v} R) : Prop :=
  ∃ h : M.carrier ≃ₜ N.carrier,
    RiemannAnalyticMap M.surface.toRiemannAtlas N.surface.toRiemannAtlas h

theorem targetEquivalent_refl (M : MarkedRiemannSurface.{u, v} R) :
    TargetEquivalent M M :=
  ⟨Homeomorph.refl _, RiemannAnalyticMap.id _⟩

theorem targetEquivalent_symm {M N : MarkedRiemannSurface.{u, v} R}
    (hMN : TargetEquivalent M N) : TargetEquivalent N M := by
  obtain ⟨h, hh⟩ := hMN
  exact ⟨h.symm, riemannAnalyticMap_homeomorph_symm h hh⟩

theorem targetEquivalent_trans {M N P : MarkedRiemannSurface.{u, v} R}
    (hMN : TargetEquivalent M N) (hNP : TargetEquivalent N P) : TargetEquivalent M P := by
  obtain ⟨h, hh⟩ := hMN
  obtain ⟨k, hk⟩ := hNP
  exact ⟨h.trans k, hk.comp hh⟩

/-- Teichmüller equivalent markings have biholomorphic targets. -/
theorem Equivalent.targetEquivalent {M N : MarkedRiemannSurface.{u, v} R}
    (hMN : Equivalent M N) : TargetEquivalent M N := by
  obtain ⟨h, hh, _⟩ := hMN
  exact ⟨h, hh⟩

/-- The target relation ignores every change of the marking. -/
theorem targetEquivalent_precompose
    (f : SmoothSurfaceEquiv R.toRiemannSurface R.toRiemannSurface)
    (hf : PreservesComplexOrientation R.toRiemannAtlas R.toRiemannAtlas f.toHomeomorph)
    (M : MarkedRiemannSurface.{u, v} R) : TargetEquivalent (precompose f hf M) M :=
  ⟨Homeomorph.refl _, RiemannAnalyticMap.id _⟩

/-- Biholomorphic equivalence of the targets of actual marked surfaces. -/
def targetSetoid (R : ClosedRiemannSurface X) : Setoid (MarkedRiemannSurface.{u, v} R) where
  r := TargetEquivalent
  iseqv := ⟨targetEquivalent_refl, targetEquivalent_symm, targetEquivalent_trans⟩

/-- The comparison of two markings through a biholomorphism of their targets.
Its underlying map is `N.marking⁻¹ ∘ h ∘ M.marking`. -/
def markingComparison (M N : MarkedRiemannSurface.{u, v} R)
    (h : M.carrier ≃ₜ N.carrier)
    (hh : RiemannAnalyticMap M.surface.toRiemannAtlas N.surface.toRiemannAtlas h) :
    OrientedSurfaceAut R where
  smooth := SmoothSurfaceEquiv.trans
    (SmoothSurfaceEquiv.trans M.marking
      (SmoothSurfaceEquiv.ofConformalHomeomorph
        M.surface.toRiemannSurface N.surface.toRiemannSurface h hh))
    (SmoothSurfaceEquiv.symm N.marking)
  orientation_preserving :=
    (PreservesComplexOrientation.homeomorph_symm
      N.marking.toHomeomorph N.orientation_preserving).comp
      ((SmoothSurfaceEquiv.ofConformalHomeomorph_preservesComplexOrientation
        M.surface.toRiemannSurface N.surface.toRiemannSurface h hh).comp
          M.orientation_preserving M.marking.toHomeomorph.continuous)
      (SmoothSurfaceEquiv.trans M.marking
        (SmoothSurfaceEquiv.ofConformalHomeomorph
          M.surface.toRiemannSurface N.surface.toRiemannSurface h hh)).toHomeomorph.continuous

@[simp]
theorem markingComparison_apply (M N : MarkedRiemannSurface.{u, v} R)
    (h : M.carrier ≃ₜ N.carrier)
    (hh : RiemannAnalyticMap M.surface.toRiemannAtlas N.surface.toRiemannAtlas h) (x : X) :
    (markingComparison M N h hh).toHomeomorph x =
      N.marking.toHomeomorph.symm (h (M.marking.toHomeomorph x)) := rfl

/-- Inverse precomposition by the comparison of the markings makes the given
biholomorphism compatible with the markings, even before passing to homotopy. -/
theorem equivalent_precompose_markingComparison_inv
    (M N : MarkedRiemannSurface.{u, v} R) (h : M.carrier ≃ₜ N.carrier)
    (hh : RiemannAnalyticMap M.surface.toRiemannAtlas N.surface.toRiemannAtlas h) :
    Equivalent
      (precompose ((markingComparison M N h hh)⁻¹).smooth
        ((markingComparison M N h hh)⁻¹).orientation_preserving M) N := by
  let a := markingComparison M N h hh
  refine ⟨h, hh, ?_⟩
  have hcancel : (_root_.toContinuousMap h).comp
      (precompose (a⁻¹).smooth (a⁻¹).orientation_preserving M).markingMap = N.markingMap := by
    ext x
    change h (M.marking.toHomeomorph (a.toHomeomorph.symm x)) = N.marking.toHomeomorph x
    calc
      h (M.marking.toHomeomorph (a.toHomeomorph.symm x)) =
          N.marking.toHomeomorph (N.marking.toHomeomorph.symm
            (h (M.marking.toHomeomorph (a.toHomeomorph.symm x)))) :=
        (N.marking.toHomeomorph.apply_symm_apply _).symm
      _ = N.marking.toHomeomorph (a.toHomeomorph (a.toHomeomorph.symm x)) := rfl
      _ = N.marking.toHomeomorph x :=
        congrArg N.marking.toHomeomorph (a.toHomeomorph.apply_symm_apply x)
  change ContinuousMap.Homotopic
    ((_root_.toContinuousMap h).comp
      (precompose (a⁻¹).smooth (a⁻¹).orientation_preserving M).markingMap) N.markingMap
  exact hcancel.symm ▸ ContinuousMap.Homotopic.refl N.markingMap

end MarkedRiemannSurface

/-- Biholomorphism classes of targets admitting one of the chosen smooth oriented markings.
This definition does not assert a classification by genus or a complex analytic structure. -/
def ModuliSpace {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X) :=
  Quotient (MarkedRiemannSurface.targetSetoid.{u, v} R)

namespace ModuliSpace

variable {X : Type u} [TopologicalSpace X] {R : ClosedRiemannSurface X}

/-- Forget the marking of a representative, retaining its actual complex surface. -/
def mk (M : MarkedRiemannSurface.{u, v} R) : ModuliSpace.{u, v} R :=
  Quotient.mk (MarkedRiemannSurface.targetSetoid R) M

theorem mk_eq_mk_iff (M N : MarkedRiemannSurface.{u, v} R) :
    mk M = mk N ↔ MarkedRiemannSurface.TargetEquivalent M N := by
  constructor
  · exact Quotient.exact
  · intro h
    exact @Quotient.sound _ (MarkedRiemannSurface.targetSetoid R) M N h

@[simp]
theorem mk_precompose
    (f : SmoothSurfaceEquiv R.toRiemannSurface R.toRiemannSurface)
    (hf : PreservesComplexOrientation R.toRiemannAtlas R.toRiemannAtlas f.toHomeomorph)
    (M : MarkedRiemannSurface.{u, v} R) : mk (MarkedRiemannSurface.precompose f hf M) = mk M :=
  (mk_eq_mk_iff _ _).2 (MarkedRiemannSurface.targetEquivalent_precompose f hf M)

end ModuliSpace

namespace TeichmullerSpace

variable {X : Type u} [TopologicalSpace X] {R : ClosedRiemannSurface X}

/-- Forget the marking of a Teichmüller point. -/
def forgetMarking : TeichmullerSpace.{u, v} R → ModuliSpace.{u, v} R :=
  Quotient.map id (fun _ _ h ↦ h.targetEquivalent)

@[simp]
theorem forgetMarking_mk (M : MarkedRiemannSurface.{u, v} R) :
    forgetMarking (mk M) = ModuliSpace.mk M := rfl

/-- Every target class in this moduli space has a marked representative by definition. -/
theorem forgetMarking_surjective : Function.Surjective (forgetMarking.{u, v} (R := R)) := by
  intro m
  refine Quotient.inductionOn m ?_
  intro M
  exact ⟨mk M, rfl⟩

@[simp]
theorem forgetMarking_precompose
    (f : SmoothSurfaceEquiv R.toRiemannSurface R.toRiemannSurface)
    (hf : PreservesComplexOrientation R.toRiemannAtlas R.toRiemannAtlas f.toHomeomorph)
    (p : TeichmullerSpace.{u, v} R) : forgetMarking (precompose f hf p) = forgetMarking p := by
  refine Quotient.inductionOn p ?_
  intro M
  exact ModuliSpace.mk_precompose f hf M

@[simp]
theorem forgetMarking_smul (γ : MappingClassGroup R) (p : TeichmullerSpace.{u, v} R) :
    forgetMarking (γ • p) = forgetMarking p := by
  refine Quotient.inductionOn γ ?_
  intro f
  change forgetMarking (precompose (f⁻¹).smooth (f⁻¹).orientation_preserving p) =
    forgetMarking p
  exact forgetMarking_precompose _ _ p

/-- Mapping classes connect precisely the marked surfaces with biholomorphic targets. -/
theorem exists_mappingClass_smul_eq_iff_targetEquivalent
    (M N : MarkedRiemannSurface.{u, v} R) :
    (∃ γ : MappingClassGroup R, γ • mk M = mk N) ↔
      MarkedRiemannSurface.TargetEquivalent M N := by
  constructor
  · rintro ⟨γ, hγ⟩
    have he : forgetMarking (mk M) = forgetMarking (mk N) := by
      calc
        forgetMarking (mk M) = forgetMarking (γ • mk M) :=
          (forgetMarking_smul γ (mk M)).symm
        _ = forgetMarking (mk N) := congrArg forgetMarking hγ
    exact (ModuliSpace.mk_eq_mk_iff M N).1 he
  · rintro ⟨h, hh⟩
    refine ⟨MappingClassGroup.mk (MarkedRiemannSurface.markingComparison M N h hh), ?_⟩
    change mk (MarkedRiemannSurface.precompose
      ((MarkedRiemannSurface.markingComparison M N h hh)⁻¹).smooth
      ((MarkedRiemannSurface.markingComparison M N h hh)⁻¹).orientation_preserving M) = mk N
    exact (mk_eq_mk_iff _ _).2
      (MarkedRiemannSurface.equivalent_precompose_markingComparison_inv M N h hh)

/-- The fibers of forgetting the marking are exactly the mapping class group orbits. -/
theorem forgetMarking_eq_iff_exists_mappingClass
    (p q : TeichmullerSpace.{u, v} R) :
    forgetMarking p = forgetMarking q ↔ ∃ γ : MappingClassGroup R, γ • p = q := by
  refine Quotient.inductionOn p ?_
  intro M
  refine Quotient.inductionOn q ?_
  intro N
  exact (ModuliSpace.mk_eq_mk_iff M N).trans
    (exists_mappingClass_smul_eq_iff_targetEquivalent M N).symm

end TeichmullerSpace

/-- The actual orbit quotient for the mapping class group action. -/
def MappingClassOrbitSpace {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X) :=
  Quotient (MulAction.orbitRel (MappingClassGroup R) (TeichmullerSpace.{u, v} R))

namespace MappingClassOrbitSpace

variable {X : Type u} [TopologicalSpace X] {R : ClosedRiemannSurface X}

/-- The mapping class group orbit of a Teichmüller point. -/
def mk (p : TeichmullerSpace.{u, v} R) : MappingClassOrbitSpace.{u, v} R :=
  Quotient.mk (MulAction.orbitRel (MappingClassGroup R) (TeichmullerSpace.{u, v} R)) p

/-- Forgetting the marking descends to the orbit quotient. -/
def toModuli : MappingClassOrbitSpace.{u, v} R → ModuliSpace.{u, v} R :=
  Quotient.lift TeichmullerSpace.forgetMarking (by
    intro p q hpq
    change p ∈ MulAction.orbit (MappingClassGroup R) q at hpq
    obtain ⟨γ, hγ⟩ := MulAction.mem_orbit_iff.mp hpq
    calc
      TeichmullerSpace.forgetMarking p = TeichmullerSpace.forgetMarking (γ • q) :=
        congrArg TeichmullerSpace.forgetMarking hγ.symm
      _ = TeichmullerSpace.forgetMarking q := TeichmullerSpace.forgetMarking_smul γ q)

@[simp]
theorem toModuli_mk (p : TeichmullerSpace.{u, v} R) :
    toModuli (mk p) = TeichmullerSpace.forgetMarking p := rfl

theorem toModuli_injective : Function.Injective (toModuli.{u, v} (R := R)) := by
  intro a b
  refine Quotient.inductionOn₂ a b ?_
  intro p q hpq
  apply @Quotient.sound _
    (MulAction.orbitRel (MappingClassGroup R) (TeichmullerSpace.{u, v} R)) p q
  change p ∈ MulAction.orbit (MappingClassGroup R) q
  exact MulAction.mem_orbit_iff.mpr
    ((TeichmullerSpace.forgetMarking_eq_iff_exists_mappingClass q p).1 hpq.symm)

theorem toModuli_surjective : Function.Surjective (toModuli.{u, v} (R := R)) := by
  intro m
  obtain ⟨p, rfl⟩ := TeichmullerSpace.forgetMarking_surjective m
  exact ⟨mk p, rfl⟩

/-- The mapping class group quotient is exactly the quotient by biholomorphism
of the targets that admit the specified smooth oriented markings. -/
def equivModuli (R : ClosedRiemannSurface X) :
    MappingClassOrbitSpace.{u, v} R ≃ ModuliSpace.{u, v} R :=
  Equiv.ofBijective toModuli ⟨toModuli_injective, toModuli_surjective⟩

@[simp]
theorem equivModuli_apply_mk (R : ClosedRiemannSurface X)
    (p : TeichmullerSpace.{u, v} R) :
    equivModuli R (mk p) = TeichmullerSpace.forgetMarking p := rfl

end MappingClassOrbitSpace

end LowDimensionalTopology.Geometry.Teichmuller
