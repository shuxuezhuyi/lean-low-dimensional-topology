module

public import LowDimensionalTopology.Geometry.Quasiconformal.BeltramiConformal
public import LowDimensionalTopology.Geometry.Quasiconformal.MeasurableRiemannMapping
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Tactic.Linarith

/-!
# Jordan boundary extensions and the conformal type of quasiconformal plane domains

The boundary extension is an actual continuous bijection of the compactified
closures. A quasiconformal map on the entire plane has unbounded image: the
normalized solution with its coefficient turns it into an actual entire
injective holomorphic map, to which Mathlib's Liouville theorem applies.

The analytic proofs reused here are due to Wu Xiaobin, from commit
1c0d5473c020b66ed5106331a38a61536760b9b2; the external provenance manifest
retains the source, license and local compatibility changes.
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory
open LiZhongQC

namespace LowDimensionalTopology.Geometry.Quasiconformal

/-- The genuine unit disk is a Jordan domain with the usual circle boundary. -/
theorem unitDisc_isJordanDomain : IsJordanDomain unitDisc := by
  refine ⟨isOpen_ball, isConnected_ball one_pos, ?_⟩
  rw [frontier_toExt_of_isBounded' (A := unitDisc) isBounded_ball isOpen_ball,
    unitDisc, frontier_ball (0 : ℂ) one_ne_zero]
  refine ⟨fun θ => ((θ : ℂ) : ExtPlane), ?_, ?_, ?_⟩
  · exact OnePoint.continuous_coe.comp continuous_subtype_val
  · exact fun a b hab => Circle.coe_injective (OnePoint.coe_injective hab)
  · unfold toExt
    ext w
    simp only [Set.mem_range, Set.mem_image]
    constructor
    · rintro ⟨θ, rfl⟩
      exact ⟨(θ : ℂ), mem_sphere_zero_iff_norm.2 (Circle.norm_coe θ), rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨z, hz⟩, rfl⟩

/-- A quasiconformal equivalence between actual Jordan domains extends to a
continuous bijection of their closures, agreeing with the original map inside. -/
theorem quasiconformal_jordan_boundary_extension
    {f : ℂ → ℂ} {D E : Set ℂ} {K : ℝ}
    (hD : IsJordanDomain D) (hE : IsJordanDomain E)
    (hf : IsKQC f D K) (himage : f '' D = E) :
    ∃ F : ExtPlane → ExtPlane, IsHomeoExtension f D E F :=
  thm13_3_boundary_correspondence hD hE ⟨K, hf⟩ himage

/-- The disk-to-Jordan version uses the actual circle boundary, without an
extra Jordan-domain assumption on the disk. -/
theorem quasiconformal_disc_jordan_boundary_extension
    {f : ℂ → ℂ} {D : Set ℂ} {K : ℝ}
    (hD : IsJordanDomain D) (hf : IsKQC f unitDisc K) (himage : f '' unitDisc = D) :
    ∃ F : ExtPlane → ExtPlane, IsHomeoExtension f unitDisc D F :=
  quasiconformal_jordan_boundary_extension unitDisc_isJordanDomain hD hf himage

/-- Every quasiconformal map defined on the entire plane has unbounded image. -/
theorem quasiconformal_plane_range_unbounded {f : ℂ → ℂ} {K : ℝ}
    (hf : IsKQC f univ K) : ¬ Bornology.IsBounded (range f) := by
  intro hb
  have hK : 1 ≤ K := hf.2.1
  have hk₀ : 0 ≤ (K - 1) / (K + 1) := div_nonneg (by linarith) (by linarith)
  have hk : (K - 1) / (K + 1) < 1 := (div_lt_one (by linarith)).mpr (by linarith)
  obtain ⟨g, ⟨hgn, hgK, _hgACL, _hgGen⟩, _⟩ :=
    normalized_beltrami_homeomorph_existsUnique hk₀ hk
      (thm10_2_genHomeoSolution_of_isKQC hf).1
  let H : ℂ → ℂ := f ∘ Function.invFunOn g univ
  have hH : IsConformalOnto H univ (f '' univ) := by
    have hcoeff : complexDilatation g =ᵐ[volume.restrict (univ : Set ℂ)]
        complexDilatation f := by
      rw [Measure.restrict_univ]
      filter_upwards [hgn.2.2.2.2] with z hz
      exact hz
    have hc := equal_dilatation_relative_conformal hgK hf hcoeff
    rw [Set.image_univ_of_surjective g.surjective] at hc
    exact hc
  have hRange : range H = range f := by simpa only [Set.image_univ] using hH.2.2
  have hbH : Bornology.IsBounded (range H) := hRange.symm ▸ hb
  have h01 : H 0 = H 1 :=
    (differentiableOn_univ.mp hH.1).apply_eq_apply_of_bounded hbH 0 1
  exact zero_ne_one (hH.2.1 (mem_univ 0) (mem_univ 1) h01)

/-- There is no quasiconformal equivalence from the plane onto the unit disk. -/
theorem not_quasiconformal_plane_to_disc {f : ℂ → ℂ} {K : ℝ}
    (hf : IsKQC f univ K) (himage : f '' univ = unitDisc) : False := by
  apply quasiconformal_plane_range_unbounded hf
  have hrange : range f = unitDisc := by simpa only [Set.image_univ] using himage
  rw [hrange]
  exact isBounded_ball

/-- There is no quasiconformal equivalence from the unit disk onto the plane. -/
theorem not_quasiconformal_disc_to_plane {f : ℂ → ℂ} {K : ℝ}
    (hf : IsKQC f unitDisc K) (himage : f '' unitDisc = univ) : False := by
  have hinv : IsKQC (Function.invFunOn f unitDisc) univ K := by
    simpa only [himage] using quasiconformal_inverse hf
  have hinvImage : Function.invFunOn f unitDisc '' univ = unitDisc := by
    rw [← himage]
    exact hf.2.2.1.2.1.leftInvOn_invFunOn.image_image
  exact not_quasiconformal_plane_to_disc hinv hinvImage

end LowDimensionalTopology.Geometry.Quasiconformal
