/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Metric.PointLineFormulas
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.HalfPlane.IsometryClassification
public import Mathlib.Analysis.SpecialFunctions.Artanh

/-!
# Actual hypercyclic regions are true point-line distance sublevels
-/

@[expose] public section
open Set
open scoped UpperHalfPlane Topology Complex.UnitDisc MatrixGroups
namespace LowDimensionalTopology.Geometry.Hyperbolic
noncomputable section

theorem tanh_lt_tanh_iff (x y : ℝ) : Real.tanh x < Real.tanh y ↔ x < y := by
  rw [Real.tanh_eq_sinh_div_cosh,Real.tanh_eq_sinh_div_cosh,
    div_lt_div_iff₀ (Real.cosh_pos x) (Real.cosh_pos y)]
  have he : 0 < Real.sinh (y-x) ↔ x < y := by rw [Real.sinh_pos_iff,sub_pos]
  rw [Real.sinh_sub] at he
  constructor
  · intro h
    apply he.mp
    nlinarith
  · intro h
    have hh := he.mpr h
    nlinarith

def hypercyclicWidthAngle (k : ℝ) : ℝ := Real.arcsin (Real.tanh k)

theorem hypercyclicWidthAngle_mem_Ioo {k : ℝ} (hk : 0 < k) :
    hypercyclicWidthAngle k ∈ Ioo (0 : ℝ) (Real.pi / 2) := by
  have ht : 0 < Real.tanh k := by
    have h := (tanh_lt_tanh_iff 0 k).mpr hk
    simpa only [Real.tanh_zero] using h
  exact ⟨Real.arcsin_pos.mpr ht,Real.arcsin_lt_pi_div_two.mpr (Real.tanh_lt_one k)⟩

theorem sin_hypercyclicWidthAngle (k : ℝ) :
    Real.sin (hypercyclicWidthAngle k) = Real.tanh k :=
  Real.sin_arcsin (Real.neg_one_lt_tanh k).le (Real.tanh_lt_one k).le

theorem verticalLine_distance_lt_iff_strip (k : ℝ) (hk : 0 < k) (z : ℍ) :
    (HalfPlaneLine.vertical 0).pointDist z < k ↔ z ∈ hypercyclicStrip (hypercyclicWidthAngle k) := by
  have ha := hypercyclicWidthAngle_mem_Ioo hk
  have hz := verticalInclination_mem_Ico 0 z
  have hzi : verticalInclination 0 z ∈ Icc (-(Real.pi/2)) (Real.pi/2) := by
    constructor <;> linarith [hz.1,hz.2,Real.pi_pos]
  have hai : hypercyclicWidthAngle k ∈ Icc (-(Real.pi/2)) (Real.pi/2) := by
    constructor <;> linarith [ha.1,ha.2,Real.pi_pos]
  rw [← tanh_lt_tanh_iff,verticalLine_pointDist_tanh_inclination,← sin_hypercyclicWidthAngle k]
  rw [Real.strictMonoOn_sin.lt_iff_lt hzi hai,verticalInclination_zero_eq_arg]
  rfl

def HalfPlaneLine.distanceSublevel (L : HalfPlaneLine) (k : ℝ) : Set ℍ := {z | L.pointDist z < k}

theorem verticalLine_distanceSublevel (k : ℝ) (hk : 0 < k) :
    (HalfPlaneLine.vertical 0).distanceSublevel k = hypercyclicStrip (hypercyclicWidthAngle k) := by
  ext z
  exact verticalLine_distance_lt_iff_strip k hk z

theorem HalfPlaneLine.pointDist_isometry_image (L M : HalfPlaneLine) (f : ℍ → ℍ)
    (hf : Isometry f) (he : f '' L.carrier = M.carrier) (z : ℍ) :
    M.pointDist (f z) = L.pointDist z := by
  unfold HalfPlaneLine.pointDist
  rw [← he]
  exact Metric.infDist_image hf

theorem HalfPlaneLine.distanceSublevel_image_isometry (L M : HalfPlaneLine) (f : ℍ → ℍ)
    (hf : Isometry f) (he : f '' L.carrier = M.carrier) (k : ℝ) :
    f '' L.distanceSublevel k = M.distanceSublevel k := by
  ext z
  constructor
  · rintro ⟨w,hw,rfl⟩
    change M.pointDist (f w) < k
    rw [L.pointDist_isometry_image M f hf he]
    exact hw
  · intro hz
    obtain ⟨w,rfl⟩ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.Isometry.halfPlane_surjective hf z
    refine ⟨w,?_,rfl⟩
    change L.pointDist w < k
    rw [← L.pointDist_isometry_image M f hf he]
    exact hz


theorem exists_hypercyclic_width {θ : ℝ} (hθ : 0 < θ) (hθ' : θ < Real.pi / 2) :
    ∃ k : ℝ, 0 < k ∧ hypercyclicWidthAngle k = θ := by
  have hd : θ ∈ Icc (-(Real.pi/2)) (Real.pi/2) := by
    constructor <;> linarith [Real.pi_pos]
  have hp : Real.pi/2 ∈ Icc (-(Real.pi/2)) (Real.pi/2) := by
    constructor <;> linarith [Real.pi_pos]
  have hs0 : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ (by linarith [Real.pi_pos])
  have hs1 : Real.sin θ < 1 := by
    have h := Real.strictMonoOn_sin hd hp hθ'
    simpa only [Real.sin_pi_div_two] using h
  refine ⟨Real.artanh (Real.sin θ),Real.artanh_pos ⟨hs0,hs1⟩,?_⟩
  unfold hypercyclicWidthAngle
  rw [Real.tanh_artanh ⟨by linarith,hs1⟩,Real.arcsin_sin hd.1 hd.2]

theorem HalfPlaneLine.distanceSublevel_hypercyclic (L : HalfPlaneLine) (k : ℝ) (hk : 0 < k) :
    IsHHypercyclicRegion (L.distanceSublevel k) := by
  obtain ⟨g,_,he⟩ := (HalfPlaneLine.vertical 0).exists_mobius_map L
  have ha := hypercyclicWidthAngle_mem_Ioo hk
  refine ⟨hypercyclicWidthAngle k,ha.1,ha.2,(fun z : ℍ => g • z),realGL_isometry g,?_⟩
  rw [← verticalLine_distanceSublevel k hk]
  exact ((HalfPlaneLine.vertical 0).distanceSublevel_image_isometry L _ (realGL_isometry g) he k).symm

theorem isHHypercyclicRegion_iff_distanceSublevel (S : Set ℍ) :
    IsHHypercyclicRegion S ↔ ∃ (L : HalfPlaneLine) (k : ℝ), 0 < k ∧ S = L.distanceSublevel k := by
  constructor
  · rintro ⟨θ,hθ,hθ',f,hf,hS⟩
    obtain ⟨k,hk,heθ⟩ := exists_hypercyclic_width hθ hθ'
    obtain ⟨L, heL⟩ :=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.Isometry.halfPlane_image_hLine hf (HalfPlaneLine.vertical 0)
    refine ⟨L,k,hk,?_⟩
    rw [hS,← heθ,← verticalLine_distanceSublevel k hk]
    exact (HalfPlaneLine.vertical 0).distanceSublevel_image_isometry L f hf heL k
  · rintro ⟨L,k,hk,rfl⟩
    exact L.distanceSublevel_hypercyclic k hk


theorem isDiscHypercyclicRegion_cayley_iff (S : Set ℍ) :
    IsDiscHypercyclicRegion (halfPlaneToDisc '' S) ↔ IsHHypercyclicRegion S := by
  let := discHyperbolicMetric
  constructor
  · rintro ⟨θ,hθ,hθ',f,hf,hS⟩
    refine ⟨θ,hθ,hθ',discMapConjugate f,disc_isometry_conjugate hf,?_⟩
    rw [disc_map_cayley_image] at hS
    exact cayleyHomeomorph.injective.image_injective hS
  · rintro ⟨θ,hθ,hθ',f,hf,hS⟩
    let g : 𝔻 → 𝔻 := halfPlaneToDisc ∘ f ∘ discToHalfPlane
    have hg : Isometry g := cayley_isometry.comp (hf.comp inverse_cayley_isometry)
    have he : discMapConjugate g = f := by
      funext z
      change discToHalfPlane (halfPlaneToDisc (f (discToHalfPlane (halfPlaneToDisc z)))) = f z
      rw [discToHalfPlane_halfPlaneToDisc,discToHalfPlane_halfPlaneToDisc]
    refine ⟨θ,hθ,hθ',g,hg,?_⟩
    rw [disc_map_cayley_image,he,← hS]

def DiscLine.distanceSublevel (L : DiscLine) (k : ℝ) : Set 𝔻 := {z | L.pointDist z < k}

theorem DiscLine.distanceSublevel_eq_cayley (L : DiscLine) (k : ℝ) :
    L.distanceSublevel k = halfPlaneToDisc '' L.toHalfPlane.distanceSublevel k := by
  ext z
  constructor
  · intro hz
    refine ⟨discToHalfPlane z,?_,halfPlaneToDisc_discToHalfPlane z⟩
    change L.toHalfPlane.pointDist (discToHalfPlane z) < k
    rw [← L.pointDist_eq_halfPlane]
    exact hz
  · rintro ⟨x,hx,rfl⟩
    change L.pointDist (halfPlaneToDisc x) < k
    rw [L.pointDist_eq_halfPlane,discToHalfPlane_halfPlaneToDisc]
    exact hx

theorem HalfPlaneLine.cayley_image_distanceSublevel (L : HalfPlaneLine) (k : ℝ) :
    halfPlaneToDisc '' L.distanceSublevel k = L.toDiscLine.distanceSublevel k := by
  rw [L.toDiscLine.distanceSublevel_eq_cayley,L.toDiscLine_toHalfPlane]

theorem DiscLine.distanceSublevel_hypercyclic (L : DiscLine) (k : ℝ) (hk : 0 < k) :
    IsDiscHypercyclicRegion (L.distanceSublevel k) := by
  rw [L.distanceSublevel_eq_cayley]
  exact (isDiscHypercyclicRegion_cayley_iff _).mpr (L.toHalfPlane.distanceSublevel_hypercyclic k hk)

theorem isDiscHypercyclicRegion_iff_distanceSublevel (S : Set 𝔻) :
    IsDiscHypercyclicRegion S ↔ ∃ (L : DiscLine) (k : ℝ), 0 < k ∧ S = L.distanceSublevel k := by
  constructor
  · intro hS
    have he : halfPlaneToDisc '' (discToHalfPlane '' S) = S := cayley_image_inverse_image S
    have hH : IsHHypercyclicRegion (discToHalfPlane '' S) := by
      apply (isDiscHypercyclicRegion_cayley_iff _).mp
      rwa [he]
    obtain ⟨L,k,hk,hL⟩ := (isHHypercyclicRegion_iff_distanceSublevel _).mp hH
    refine ⟨L.toDiscLine,k,hk,?_⟩
    rw [← he,hL,L.cayley_image_distanceSublevel]
  · rintro ⟨L,k,hk,rfl⟩
    exact L.distanceSublevel_hypercyclic k hk

end
end LowDimensionalTopology.Geometry.Hyperbolic
