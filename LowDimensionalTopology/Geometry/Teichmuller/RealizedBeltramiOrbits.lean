module

public import LowDimensionalTopology.Geometry.Teichmuller.RealizedBeltramiAction

/-!
# Diffeomorphism orbits of realized coefficients

Two actual smooth coefficients are in the same orientation-preserving
diffeomorphism orbit precisely when their target Riemann surfaces are
biholomorphic. Restricting to diffeomorphisms freely homotopic to the identity
gives precisely native Teichmüller equivalence. The reverse implications use
the genuine comparison of the two markings through the given biholomorphism.
-/

@[expose] public section

noncomputable section

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces

universe u v

namespace MarkedRiemannSurface

variable {X : Type u} [TopologicalSpace X] {R : ClosedRiemannSurface X}

/-- Inverse precomposition by the actual comparison makes the target
biholomorphism carry the markings exactly, before passing to homotopy. -/
theorem markingComparison_carries_changeMarking
    (M N : MarkedRiemannSurface.{u, v} R) (h : M.carrier ≃ₜ N.carrier)
    (hh : RiemannAnalyticMap M.surface.toRiemannAtlas N.surface.toRiemannAtlas h)
    (x : X) :
    h ((changeMarking (markingComparison M N h hh) M).marking.toHomeomorph x) =
      N.marking.toHomeomorph x := by
  let a := markingComparison M N h hh
  change h (M.marking.toHomeomorph (a.toHomeomorph.symm x)) = N.marking.toHomeomorph x
  calc
    h (M.marking.toHomeomorph (a.toHomeomorph.symm x)) =
        N.marking.toHomeomorph (N.marking.toHomeomorph.symm
          (h (M.marking.toHomeomorph (a.toHomeomorph.symm x)))) :=
      (N.marking.toHomeomorph.apply_symm_apply _).symm
    _ = N.marking.toHomeomorph (a.toHomeomorph (a.toHomeomorph.symm x)) := rfl
    _ = N.marking.toHomeomorph x :=
      congrArg N.marking.toHomeomorph (a.toHomeomorph.apply_symm_apply x)

/-- The comparison aligns actual coefficients, rather than just their
Teichmüller classes. -/
theorem beltramiCoefficient_changeMarking_markingComparison
    (M N : MarkedRiemannSurface.{u, v} R) (h : M.carrier ≃ₜ N.carrier)
    (hh : RiemannAnalyticMap M.surface.toRiemannAtlas N.surface.toRiemannAtlas h) :
    (changeMarking (markingComparison M N h hh) M).beltramiCoefficient =
      N.beltramiCoefficient :=
  beltramiCoefficient_eq_of_analytic_homeomorph
    (changeMarking (markingComparison M N h hh) M) N h hh
    (markingComparison_carries_changeMarking M N h hh)

/-- Compatibility of the given biholomorphism with the markings up to free
homotopy is exactly the homotopy identity condition on their comparison. -/
theorem markingComparison_mem_homotopyIdentity_iff
    (M N : MarkedRiemannSurface.{u, v} R) (h : M.carrier ≃ₜ N.carrier)
    (hh : RiemannAnalyticMap M.surface.toRiemannAtlas N.surface.toRiemannAtlas h) :
    markingComparison M N h hh ∈ OrientedSurfaceAut.homotopyIdentitySubgroup R ↔
      ContinuousMap.Homotopic ((_root_.toContinuousMap h).comp M.markingMap) N.markingMap := by
  constructor
  · intro ha
    change ContinuousMap.Homotopic (markingComparison M N h hh).continuousMap
      (ContinuousMap.id X) at ha
    have hc := (ContinuousMap.Homotopic.refl N.markingMap).comp ha
    have hleft : N.markingMap.comp (markingComparison M N h hh).continuousMap =
        (_root_.toContinuousMap h).comp M.markingMap := by
      ext x
      exact N.marking.toHomeomorph.apply_symm_apply _
    rw [hleft] at hc
    exact hc
  · intro hhom
    change ContinuousMap.Homotopic (markingComparison M N h hh).continuousMap
      (ContinuousMap.id X)
    have hc := (ContinuousMap.Homotopic.refl
      (_root_.toContinuousMap N.marking.toHomeomorph.symm)).comp hhom
    have hcancel : (_root_.toContinuousMap N.marking.toHomeomorph.symm).comp N.markingMap =
        ContinuousMap.id X := by
      ext x
      exact N.marking.toHomeomorph.symm_apply_apply x
    rw [hcancel] at hc
    exact hc

end MarkedRiemannSurface

namespace RealizedBeltramiCoefficients

variable {X : Type u} [TopologicalSpace X] {R : ClosedRiemannSurface X}

/-- The existing smooth marking comparison realizes the actual coefficient
orbit equality through any specified biholomorphic target change. -/
theorem markingComparison_smul_ofMarked
    (M N : MarkedRiemannSurface.{u, v} R) (h : M.carrier ≃ₜ N.carrier)
    (hh : RiemannAnalyticMap M.surface.toRiemannAtlas N.surface.toRiemannAtlas h) :
    MarkedRiemannSurface.markingComparison M N h hh • ofMarked M = ofMarked N := by
  rw [smul_ofMarked]
  apply Subtype.ext
  exact MarkedRiemannSurface.beltramiCoefficient_changeMarking_markingComparison M N h hh

/-- The Diff⁺ orbit criterion: only the biholomorphic type of the actual target
survives arbitrary smooth orientation-preserving changes of reference marking. -/
theorem exists_smul_ofMarked_eq_iff_targetEquivalent
    (M N : MarkedRiemannSurface.{u, v} R) :
    (∃ a : OrientedSurfaceAut R, a • ofMarked M = ofMarked N) ↔
      MarkedRiemannSurface.TargetEquivalent M N := by
  constructor
  · rintro ⟨a, ha⟩
    rw [smul_ofMarked] at ha
    have hcoeff : (MarkedRiemannSurface.changeMarking a M).beltramiCoefficient =
        N.beltramiCoefficient := congrArg Subtype.val ha
    have hMN := MarkedRiemannSurface.equivalent_of_beltramiCoefficient_eq hcoeff
    exact MarkedRiemannSurface.targetEquivalent_trans
      (MarkedRiemannSurface.targetEquivalent_symm
        (MarkedRiemannSurface.targetEquivalent_changeMarking a M)) hMN.targetEquivalent
  · rintro ⟨h, hh⟩
    exact ⟨MarkedRiemannSurface.markingComparison M N h hh,
      markingComparison_smul_ofMarked M N h hh⟩

/-- The Diff₀ orbit criterion: free homotopy of markings is precisely the
restriction of the coefficient action to the genuine homotopy identity subgroup. -/
theorem exists_homotopyIdentity_smul_ofMarked_eq_iff_equivalent
    (M N : MarkedRiemannSurface.{u, v} R) :
    (∃ a : OrientedSurfaceAut.homotopyIdentitySubgroup R,
      a • ofMarked M = ofMarked N) ↔ MarkedRiemannSurface.Equivalent M N := by
  constructor
  · rintro ⟨a, ha⟩
    have hβ := congrArg (beta (R := R)) ha
    have hmk : TeichmullerSpace.mk M = TeichmullerSpace.mk N := by
      simpa only [beta_homotopyIdentity_smul, beta_ofMarked] using hβ
    exact (TeichmullerSpace.mk_eq_mk_iff M N).1 hmk
  · rintro ⟨h, hh, hhom⟩
    have ha : MarkedRiemannSurface.markingComparison M N h hh ∈
        OrientedSurfaceAut.homotopyIdentitySubgroup R :=
      (MarkedRiemannSurface.markingComparison_mem_homotopyIdentity_iff M N h hh).2 hhom
    refine ⟨⟨MarkedRiemannSurface.markingComparison M N h hh, ha⟩, ?_⟩
    change MarkedRiemannSurface.markingComparison M N h hh • ofMarked M = ofMarked N
    exact markingComparison_smul_ofMarked M N h hh

/-- Every fiber of the concrete coefficient projection is a Diff₀ orbit. -/
theorem beta_eq_iff_exists_homotopyIdentity
    (μ ν : RealizedBeltramiCoefficients.{u, v} R) :
    beta μ = beta ν ↔ ∃ a : OrientedSurfaceAut.homotopyIdentitySubgroup R, a • μ = ν := by
  obtain ⟨M, rfl⟩ := ofMarked_surjective μ
  obtain ⟨N, rfl⟩ := ofMarked_surjective ν
  exact (beta_ofMarked_eq_iff M N).trans
    (exists_homotopyIdentity_smul_ofMarked_eq_iff_equivalent M N).symm

/-- Forget both the representative realizing a coefficient and its marking. -/
def forgetMarking (μ : RealizedBeltramiCoefficients.{u, v} R) : ModuliSpace.{u, v} R :=
  TeichmullerSpace.forgetMarking (beta μ)

@[simp]
theorem forgetMarking_ofMarked (M : MarkedRiemannSurface.{u, v} R) :
    forgetMarking (ofMarked M) = ModuliSpace.mk M := by
  unfold forgetMarking
  rw [beta_ofMarked, TeichmullerSpace.forgetMarking_mk]

/-- Arbitrary reference changes preserve the unmarked target class. -/
@[simp]
theorem forgetMarking_smul (a : OrientedSurfaceAut R)
    (μ : RealizedBeltramiCoefficients.{u, v} R) : forgetMarking (a • μ) = forgetMarking μ := by
  obtain ⟨M, rfl⟩ := ofMarked_surjective μ
  simp only [smul_ofMarked, forgetMarking_ofMarked]
  exact ModuliSpace.mk_precompose (a⁻¹).smooth (a⁻¹).orientation_preserving M

theorem forgetMarking_surjective : Function.Surjective
    (forgetMarking : RealizedBeltramiCoefficients.{u, v} R → ModuliSpace.{u, v} R) :=
  TeichmullerSpace.forgetMarking_surjective.comp beta_surjective

/-- Every fiber of the unmarked coefficient projection is a Diff⁺ orbit. -/
theorem forgetMarking_eq_iff_exists_smul
    (μ ν : RealizedBeltramiCoefficients.{u, v} R) :
    forgetMarking μ = forgetMarking ν ↔ ∃ a : OrientedSurfaceAut R, a • μ = ν := by
  obtain ⟨M, rfl⟩ := ofMarked_surjective μ
  obtain ⟨N, rfl⟩ := ofMarked_surjective ν
  rw [forgetMarking_ofMarked, forgetMarking_ofMarked]
  exact (ModuliSpace.mk_eq_mk_iff M N).trans
    (exists_smul_ofMarked_eq_iff_targetEquivalent M N).symm

end RealizedBeltramiCoefficients

end LowDimensionalTopology.Geometry.Teichmuller
