module

public import LowDimensionalTopology.Geometry.Teichmuller.CompactGenusThickPart
public import LowDimensionalTopology.Geometry.Teichmuller.MarkedGeodesicLength
public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.OriginalClosedGeodesicExistence

/-!
# Original systole invariance and the full moduli thick-part criterion

Actual biholomorphic changes preserve every original closed-geodesic length,
using the existing free-class length law and existing geodesic representative.
The entire spectrum is retained, including full traversals and proper powers.
No new metric, model transport or marking construction is used.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces

private theorem original_spectrum_subset_of_analyticHomeomorph
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (R : ClosedRiemannSurface X) (S : ClosedRiemannSurface Y)
    (M : HyperbolicSurfaceModel R.toRiemannSurface)
    (N : HyperbolicSurfaceModel S.toRiemannSurface)
    (f : X ≃ₜ Y) (hf : RiemannAnalyticMap R.toRiemannAtlas S.toRiemannAtlas f) :
    originalClosedGeodesicLengthSpectrum M ⊆ originalClosedGeodesicLengthSpectrum N := by
  let := R.compactSpace
  let := S.compactSpace
  rintro ℓ ⟨q, rfl⟩
  let β : LiZhongQC.Loop Y := ⟨f q.toLoop.1, q.toLoop.2.map f.continuous⟩
  have hnon : ¬ IsNullHomotopicLoop β := by
    rintro ⟨y, hy⟩
    have hback := LiZhongQC.s30b_fh_map f.symm.continuous hy
    have hleft : LiZhongQC.FreelyHomotopic q.toLoop
        ⟨f.symm β.1, β.2.map f.symm.continuous⟩ := by
      apply LiZhongQC.s30b_fh_of_eq
      intro t
      exact (f.symm_apply_apply (q.toLoop.2 t)).symm
    have hright : LiZhongQC.FreelyHomotopic
        ⟨f.symm (constantLoop y).1, (constantLoop y).2.map f.symm.continuous⟩
        (constantLoop (f.symm y)) := by
      apply LiZhongQC.s30b_fh_of_eq
      intro t
      rfl
    exact q.not_isNullHomotopicLoop ⟨f.symm y,
      LiZhongQC.s30b_fh_trans hleft (LiZhongQC.s30b_fh_trans hback hright)⟩
  obtain ⟨r, hr⟩ := N.exists_original_closed_geodesic_of_not_null β hnon
  refine ⟨r, ?_⟩
  apply congrArg ENNReal.toReal
  exact r.length_eq_freeHomotopyLength.trans
    ((LiZhongQC.s30b_fhl_congr N.halfPlaneCover hr).symm.trans
      ((freeLength_eq_of_analyticHomeomorph R.toRiemannSurface S.toRiemannSurface
        M N f hf q.toLoop).trans q.length_eq_freeHomotopyLength.symm))

/-- The whole original closed-geodesic spectrum is unchanged by an actual
biholomorphism, for any genuine models on those same original surfaces. -/
theorem originalClosedGeodesicLengthSpectrum_eq_of_analyticHomeomorph
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (R : ClosedRiemannSurface X) (S : ClosedRiemannSurface Y)
    (M : HyperbolicSurfaceModel R.toRiemannSurface)
    (N : HyperbolicSurfaceModel S.toRiemannSurface)
    (f : X ≃ₜ Y) (hf : RiemannAnalyticMap R.toRiemannAtlas S.toRiemannAtlas f) :
    originalClosedGeodesicLengthSpectrum M = originalClosedGeodesicLengthSpectrum N :=
  Set.Subset.antisymm
    (original_spectrum_subset_of_analyticHomeomorph R S M N f hf)
    (original_spectrum_subset_of_analyticHomeomorph S R N M f.symm
      (riemannAnalyticMap_homeomorph_symm f hf))

/-- The original hyperbolic systole is independent of the genuine model and
is preserved by the original biholomorphic equivalence. -/
theorem originalHyperbolicSystole_eq_of_analyticHomeomorph
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (R : ClosedRiemannSurface X) (S : ClosedRiemannSurface Y)
    (M : HyperbolicSurfaceModel R.toRiemannSurface)
    (N : HyperbolicSurfaceModel S.toRiemannSurface)
    (f : X ≃ₜ Y) (hf : RiemannAnalyticMap R.toRiemannAtlas S.toRiemannAtlas f) :
    originalHyperbolicSystole R M = originalHyperbolicSystole S N := by
  unfold originalHyperbolicSystole
  rw [originalClosedGeodesicLengthSpectrum_eq_of_analyticHomeomorph R S M N f hf]

/-- Every actual compact-genus representative has exactly the original
systole threshold prescribed by its moduli class's thick-part membership. -/
theorem compactGenusThickPart_mk_iff {g : ℕ} (hg : 2 ≤ g) (ε : ℝ)
    (S : CompactGenusSurface g) :
    CompactGenusModuliSpace.mk S ∈ compactGenusThickPart hg ε ↔
      ε ≤ originalHyperbolicSystole S.surface
        (S.surface.hyperbolicOfGenusGeTwo hg S.hasGenus).model := by
  change (∃ T : CompactGenusSurface g,
    ε ≤ originalHyperbolicSystole T.surface
      (T.surface.hyperbolicOfGenusGeTwo hg T.hasGenus).model ∧
      CompactGenusModuliSpace.mk T = CompactGenusModuliSpace.mk S) ↔
    ε ≤ originalHyperbolicSystole S.surface
      (S.surface.hyperbolicOfGenusGeTwo hg S.hasGenus).model
  constructor
  · rintro ⟨T, hT, hTS⟩
    obtain ⟨f, hf, hbij⟩ := (CompactGenusModuliSpace.mk_eq_mk_iff T S).mp hTS
    have heq := originalHyperbolicSystole_eq_of_analyticHomeomorph T.surface S.surface
      (T.surface.hyperbolicOfGenusGeTwo hg T.hasGenus).model
      (S.surface.hyperbolicOfGenusGeTwo hg S.hasGenus).model
      (hf.toHomeomorph hbij) hf
    rw [heq] at hT
    exact hT
  · intro hS
    exact ⟨S, hS, rfl⟩

end LowDimensionalTopology.Geometry.Teichmuller
