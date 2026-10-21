/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov

Adapted polar-cap and path-perturbation proof from LeanPool.JacobianDiffgeo.SphereTopology.SimplyConnectedP1,
LeanPool/lean-pool revision86da5902e640ceb44e53f88c4a04f870dc062126.
Original SHA256: 70429619ccdd711da813f529496b3ae242adcc50c1f41328b47b1e45cea7cb35
Uses this project's original sphere atlas/reciprocal homeomorphism; no second sphere atlas is added.
Local additions prove compactness consequences and genus-zero conformal classification from project uniformization.
-/
module
public import LowDimensionalTopology.Geometry.Surfaces.Riemann.RiemannManifold
public import LowDimensionalTopology.External.LeanPool.JacobianDiffgeo.Path.Perturb
public import LowDimensionalTopology.Geometry.Surfaces.Uniformization.Uniformization
public import Mathlib.Topology.Compactification.OnePoint.Sphere
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
@[expose] public section
noncomputable section
open Set Topology OnePoint Metric
open scoped Manifold ContDiff
namespace LowDimensionalTopology.Geometry.Surfaces

theorem riemannSphere_punctured_infty_simplyConnected :
    IsSimplyConnected ({(∞ : OnePoint ℂ)}ᶜ) := by
  have hu : IsSimplyConnected (Set.univ : Set ℂ) :=
    (Homeomorph.Set.univ ℂ).toHomotopyEquiv.simplyConnectedSpace
  have him := (isOpenEmbedding_coe.isEmbedding.isSimplyConnected_image
    (s := (Set.univ : Set ℂ))).mpr hu
  rw [Set.image_univ] at him
  rwa [compl_infty]

theorem riemannSphere_punctured_zero_simplyConnected :
    IsSimplyConnected ({((0 : ℂ) : OnePoint ℂ)}ᶜ) := by
  have heq : ({((0 : ℂ) : OnePoint ℂ)}ᶜ : Set (OnePoint ℂ)) =
      sphereReciprocalHomeomorph ⁻¹' ({(∞ : OnePoint ℂ)}ᶜ) := by
    ext z
    change (z ≠ ((0 : ℂ) : OnePoint ℂ)) ↔ sphereReciprocal z ≠ (∞ : OnePoint ℂ)
    exact not_congr (sphereReciprocal_eq_infty_iff z).symm
  rw [heq]
  exact (Homeomorph.isSimplyConnected_preimage sphereReciprocalHomeomorph).mpr
    riemannSphere_punctured_infty_simplyConnected

theorem riemannSphere_simplyConnected : SimplyConnectedSpace (OnePoint ℂ) := by
  let := sphereRiemannAtlas.toChartedSpace
  let := sphereRiemannAtlas.isManifold
  let : PathConnectedSpace (OnePoint ℂ) := sphereRiemannSurface.pathConnectedSpace
  rw [simply_connected_iff_loops_nullhomotopic]
  refine ⟨inferInstance, fun x γ => ?_⟩
  by_cases hx : x = (∞ : OnePoint ℂ)
  · subst hx
    obtain ⟨γ', hγγ', hdisj⟩ := RS.Loop.exists_homotopic_avoiding γ
      (S := ({((0 : ℂ) : OnePoint ℂ)} : Set (OnePoint ℂ))) (Set.finite_singleton _) (by simp)
    have hmem : ∀ t, γ' t ∈ ({((0 : ℂ) : OnePoint ℂ)}ᶜ : Set (OnePoint ℂ)) := fun t =>
      Set.disjoint_left.mp hdisj (Set.mem_range_self t)
    obtain ⟨F, -⟩ := (isSimplyConnected_iff_exists_homotopy_refl_forall_mem.mp
      riemannSphere_punctured_zero_simplyConnected).2 _ γ' hmem
    exact hγγ'.trans ⟨F⟩
  · obtain ⟨γ', hγγ', hdisj⟩ := RS.Loop.exists_homotopic_avoiding γ
      (S := ({(∞ : OnePoint ℂ)} : Set (OnePoint ℂ))) (Set.finite_singleton _) (by simpa using hx)
    have hmem : ∀ t, γ' t ∈ ({(∞ : OnePoint ℂ)}ᶜ : Set (OnePoint ℂ)) := fun t =>
      Set.disjoint_left.mp hdisj (Set.mem_range_self t)
    obtain ⟨F, -⟩ := (isSimplyConnected_iff_exists_homotopy_refl_forall_mem.mp
      riemannSphere_punctured_infty_simplyConnected).2 _ γ' hmem
    exact hγγ'.trans ⟨F⟩

theorem not_compactSpace_standardUnitDisc : ¬CompactSpace standardUnitDiscOpens := by
  intro hc
  have hb : IsCompact (ball (0 : ℂ) 1) := isCompact_iff_compactSpace.mpr hc
  have hcl : closure (ball (0 : ℂ) 1) = ball (0 : ℂ) 1 := hb.isClosed.closure_eq
  rw [closure_ball (0 : ℂ) one_ne_zero] at hcl
  have h1 : (1 : ℂ) ∈ closedBall (0 : ℂ) 1 := by simp [mem_closedBall, dist_eq_norm]
  rw [hcl] at h1
  simp [mem_ball, dist_eq_norm] at h1

theorem RiemannConformallyEquivalent.not_disc_of_compact {X : Type*}
    [TopologicalSpace X] [CompactSpace X] (R : RiemannSurface X) :
    ¬RiemannConformallyEquivalent R discRiemannSurface := by
  intro h
  obtain ⟨f, hf, hbij⟩ := h.trans discRiemannSurface_conformallyEquivalent_standardUnitDisc
  exact not_compactSpace_standardUnitDisc (hf.toHomeomorph hbij).compactSpace

/-- A compact simply connected surface is conformally the genuine Riemann sphere. -/
theorem riemannSurface_compact_simplyConnected_conformallyEquivalent_sphere {X : Type*}
    [TopologicalSpace X] [CompactSpace X] [SimplyConnectedSpace X] (R : RiemannSurface X) :
    RiemannConformallyEquivalent R sphereRiemannSurface := by
  rcases riemannSurface_uniformization R with h | h | h
  · exact (_root_.LowDimensionalTopology.Geometry.Surfaces.RiemannConformallyEquivalent.not_disc_of_compact R h).elim
  · exact (_root_.LowDimensionalTopology.Geometry.Surfaces.RiemannConformallyEquivalent.not_plane_of_compact R h).elim
  · exact h

/-- Genus-zero topology is sufficient: the exact underlying sphere homeomorphism
implies conformal equivalence, rather than being assumed analytic. -/
theorem riemannSurface_conformallyEquivalent_sphere_iff_homeomorphic_sphere {X : Type*}
    [TopologicalSpace X] (R : RiemannSurface X) :
    RiemannConformallyEquivalent R sphereRiemannSurface ↔ Nonempty (X ≃ₜ OnePoint ℂ) := by
  constructor
  · rintro ⟨f, hf, hbij⟩
    exact ⟨hf.toHomeomorph hbij⟩
  · rintro ⟨e⟩
    let := riemannSphere_simplyConnected
    let : CompactSpace X := e.symm.compactSpace
    let : SimplyConnectedSpace X := e.toHomotopyEquiv.simplyConnectedSpace
    exact riemannSurface_compact_simplyConnected_conformallyEquivalent_sphere R

/-- The same genus-zero statement uses the literal Euclidean unit two-sphere. -/
theorem riemannSurface_conformallyEquivalent_sphere_iff_homeomorphic_twoSphere {X : Type*}
    [TopologicalSpace X] (R : RiemannSurface X) :
    RiemannConformallyEquivalent R sphereRiemannSurface ↔
      Nonempty (X ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) := by
  let E : OnePoint ℂ ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
    onePointEquivSphereOfFinrankEq (by simp [Complex.finrank_real_complex])
  rw [riemannSurface_conformallyEquivalent_sphere_iff_homeomorphic_sphere]
  exact ⟨fun ⟨e⟩ => ⟨e.trans E⟩, fun ⟨e⟩ => ⟨e.trans E.symm⟩⟩

end LowDimensionalTopology.Geometry.Surfaces
