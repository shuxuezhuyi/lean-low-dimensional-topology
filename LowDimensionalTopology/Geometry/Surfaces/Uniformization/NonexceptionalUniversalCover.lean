/-
Copyright (c) 2026 The gpt-lean-low-dimensional-topology authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The gpt-lean-low-dimensional-topology authors

Separation and uniformization reuse Will (Ziang) Li's
Uniformization code, pinned upstream 6e306deb8169e834e9cc6662160c70231a7e2a83;
the analytic Cayley equivalence reuses the credited LiZhongQC S22 module.
-/
module

public import LowDimensionalTopology.Geometry.Surfaces.Riemann.ExceptionalRiemannSurfaces
public import LowDimensionalTopology.Geometry.Surfaces.Uniformization.Uniformization
public import LowDimensionalTopology.External.LiZhongQC.Ch06.S22_RiemannSurfaces

public section
noncomputable section

open scoped Manifold ContDiff UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Surfaces

local instance : ConnectedSpace RiemannDynamics.unitDiscOpens :=
  isConnected_iff_connectedSpace.mp (Metric.isConnected_ball (E := ℂ) zero_lt_one)

/-- The actual plane and inherited disc atlases are not conformally equivalent. -/
theorem complexPlane_not_conformallyEquivalent_disc :
    ¬ RiemannConformallyEquivalent complexPlaneRiemannSurface discRiemannSurface := by
  intro h
  have hn := complexPlaneRiemannSurface_conformallyEquivalent_manifold.symm.trans
    (h.trans discRiemannSurface_conformallyEquivalent_standardUnitDisc)
  exact RiemannDynamics.not_nonempty_diffeomorph_complex_unitDisc
    (riemannConformallyEquivalent_ofManifold_iff_nonempty_diffeomorph.mp hn)

/-- The actual sphere and inherited disc atlases are not conformally equivalent. -/
theorem sphere_not_conformallyEquivalent_disc :
    ¬ RiemannConformallyEquivalent sphereRiemannSurface discRiemannSurface := by
  intro h
  have hn := sphereRiemannSurface_conformallyEquivalent_native.symm.trans
    (h.trans discRiemannSurface_conformallyEquivalent_standardUnitDisc)
  exact RiemannDynamics.not_nonempty_diffeomorph_sphere_unitDisc
    (riemannConformallyEquivalent_ofManifold_iff_nonempty_diffeomorph.mp hn)

/-- Any given original universal cover has disc type exactly for a nonexceptional
base surface. No compactness, genus, or additional uniformization premise occurs. -/
theorem RiemannUniversalCover.disc_model_iff_not_isExceptional
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    (C : RiemannUniversalCover R) :
    @RiemannConformallyEquivalent C.space _ C.topology _ C.surface
      discRiemannSurface ↔ ¬ R.IsExceptional := by
  let : TopologicalSpace C.space := C.topology
  constructor
  · intro hd he
    rcases C.isExceptional_iff_sphere_or_plane.mp he with hs | hp
    · exact sphere_not_conformallyEquivalent_disc (hs.symm.trans hd)
    · exact complexPlane_not_conformallyEquivalent_disc (hp.symm.trans hd)
  · intro hn
    rcases C.uniformization with hd | hp | hs
    · exact hd
    · exact (hn (C.isExceptional_iff_sphere_or_plane.mpr (Or.inr hp))).elim
    · exact (hn (C.isExceptional_iff_sphere_or_plane.mpr (Or.inl hs))).elim

/-- The native upper-half-plane manifold is analytically equivalent to the
inherited disc atlas, via the actual Cayley diffeomorphism. -/
theorem upperHalfPlane_conformallyEquivalent_disc :
    RiemannConformallyEquivalent (RiemannSurface.ofManifold ℍ)
      discRiemannSurface := by
  obtain ⟨e, _, _⟩ := LiZhongQC.s22c6_cayley_diffeomorph
  have h : RiemannConformallyEquivalent (RiemannSurface.ofManifold ℍ)
      standardUnitDiscRiemannSurface :=
    riemannConformallyEquivalent_ofManifold_iff_nonempty_diffeomorph.mpr ⟨e⟩
  exact h.trans discRiemannSurface_conformallyEquivalent_standardUnitDisc.symm

/-- The nonexceptional criterion in the original surface language, for the same cover:
its universal covering surface is the upper half-plane iff the base is not one
of the four exceptional conformal types. -/
theorem RiemannUniversalCover.halfPlane_model_iff_not_isExceptional
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    (C : RiemannUniversalCover R) :
    @RiemannConformallyEquivalent C.space ℍ C.topology _ C.surface
      (RiemannSurface.ofManifold ℍ) ↔ ¬ R.IsExceptional := by
  let : TopologicalSpace C.space := C.topology
  constructor
  · intro hh
    exact C.disc_model_iff_not_isExceptional.mp
      (hh.trans upperHalfPlane_conformallyEquivalent_disc)
  · intro hn
    exact (C.disc_model_iff_not_isExceptional.mpr hn).trans
      upperHalfPlane_conformallyEquivalent_disc.symm

/-- A surface has an actual analytic upper-half-plane universal cover exactly
when it is not one of the four exceptional conformal types. -/
theorem RiemannSurface.exists_halfPlane_universalCover_iff_not_isExceptional
    {X : Type*} [TopologicalSpace X] (R : RiemannSurface X) :
    (∃ C : RiemannUniversalCover R,
      @RiemannConformallyEquivalent C.space ℍ C.topology _ C.surface
        (RiemannSurface.ofManifold ℍ)) ↔ ¬ R.IsExceptional := by
  constructor
  · rintro ⟨C, hC⟩
    exact C.halfPlane_model_iff_not_isExceptional.mp hC
  · intro hn
    obtain ⟨C⟩ := riemannSurface_nonempty_universalCover R
    exact ⟨C, C.halfPlane_model_iff_not_isExceptional.mpr hn⟩

end LowDimensionalTopology.Geometry.Surfaces
