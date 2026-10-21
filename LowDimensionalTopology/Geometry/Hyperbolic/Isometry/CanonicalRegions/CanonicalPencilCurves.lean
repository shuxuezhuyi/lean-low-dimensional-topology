/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.CanonicalRegions.CanonicalPairRecovery
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.CanonicalRegions.CanonicalConstruction
public import LowDimensionalTopology.Geometry.Hyperbolic.Metric.DistanceLevelFrontiers
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.Pencils.NativeEllipticPencils
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.Pencils.HyperbolicPencilTransport
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane MatrixGroups OnePoint ComplexConjugate Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Inversive LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The elliptic boundary is one regular curve of the complementary pencil family,
with the genuine half-turn singleton recorded separately. -/
theorem hCanonicalRegion_elliptic_frontier (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : Mobius.MobiusElliptic (realSLMobius A)) :
    let v := hEllipticCenter A ((realSLMobius_elliptic_iff A hA.1).mp hA)
    (Matrix.trace A.val=0 ∧ frontier (hCanonicalRegion A)={v}) ∨
      (Matrix.trace A.val≠0 ∧ frontier (hCanonicalRegion A)∈hMetricCircleFamily v) := by
  rcases hCanonicalRegion_elliptic_ball A hA with ⟨ht,he⟩ | ⟨r,hr,ht,he⟩
  · left
    refine ⟨ht,?_⟩
    rw [he,h_frontier_singleton]
  · right
    refine ⟨ht,r,hr,?_⟩
    rw [he,hMetric_ball_frontier _ r hr]
    rfl

/-- The parabolic canonical frontier is an actual horocycle at the genuine fixed ideal point. -/
theorem hCanonicalRegion_parabolic_frontier (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : Mobius.MobiusParabolic (realSLMobius A)) :
    ∃ w : Mobius.ExtendedComplex, (realSLMobius A).val w=w ∧
      IsHHorocycleAt w (frontier (hCanonicalRegion A)) := by
  obtain ⟨q,t,ht,he⟩ := realSLMobius_parabolic_normal_form A hA
  let H := (hSLIsometry q).toHomeomorph
  have hreg : H '' hCanonicalRegion A=horizontalHorocyclicRegion (|t|/2) := by
    change (fun z : ℍ=>q • z) '' hCanonicalRegion A= _
    rw [← hCanonicalRegion_conjugation A q]
    rcases he with he | he
    · rw [he,hCanonicalRegion_translation]
      rfl
    · rw [he,hCanonicalRegion_neg,hCanonicalRegion_translation]
      rfl
  have hback : H.symm '' horizontalHorocyclicRegion (|t|/2)=hCanonicalRegion A := by
    rw [←hreg]
    exact H.toEquiv.symm_image_image _
  have hfront : frontier (hCanonicalRegion A)=H.symm '' horizontalHorocycle (|t|/2) := by
    calc
      frontier (hCanonicalRegion A)=frontier (H.symm '' horizontalHorocyclicRegion (|t|/2)) := by rw [hback]
      _=H.symm '' frontier (horizontalHorocyclicRegion (|t|/2)) := (H.symm.image_frontier _).symm
      _=H.symm '' horizontalHorocycle (|t|/2) := by rw [horizontalHorocycle_eq_actual_boundary];rfl
  let g := Matrix.SpecialLinearGroup.mapGL ℝ q⁻¹
  have hg : 0<g.val.det := by change 0<(q⁻¹).val.det;rw [(q⁻¹).det_coe];norm_num
  have hS := (horizontalHorocycle_isHHorocycleAt (|t|/2) (by exact div_pos (abs_pos.mpr ht) (by norm_num))).realGL_image g hg
  have hw : Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) ∞=(realSLMobius q⁻¹).val ∞ := by
    rw [realSLMobius,MonoidHom.comp_apply,Mobius.invariantDisc_specialLinear_action,realSLMobius_matrix]
  rw [hw] at hS
  have hSin : IsHHorocycleAt ((realSLMobius q⁻¹).val ∞) (frontier (hCanonicalRegion A)) := by
    rw [hfront]
    exact hS
  refine ⟨(realSLMobius q⁻¹).val ∞,?_,hSin⟩
  have hT : (realSLMobius (q*A*q⁻¹)).val ∞=∞ := by
    rcases he with he | he
    · rw [he]
      simp [realSLMobius_real_infty,hTranslationSL]
    · rw [he,realSLMobius_neg]
      simp [realSLMobius_real_infty,hTranslationSL]
  have hqw : (realSLMobius q).val ((realSLMobius q⁻¹).val ∞)=∞ := by
    rw [map_inv]
    exact Equiv.apply_symm_apply _ _
  apply (realSLMobius_conjugate_fixed_iff A q _).mp
  rw [hqw]
  exact hT

/-- The hyperbolic canonical frontier is the actual positive distance level of its actual axis. -/
theorem hCanonicalRegion_hyperbolic_frontier (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : realSLMobius A≠1) (ht : 4<(Matrix.trace A.val)^2) :
    ∃r : ℝ,0<r ∧ frontier (hCanonicalRegion A)={z : ℍ | (hHyperbolicAxis A hA ht).pointDist z=r} := by
  obtain ⟨r,hr,he⟩ := hCanonicalRegion_hyperbolic_strip A hA ht
  exact ⟨r,hr,by rw [he,HalfPlaneLine.distanceSublevel_frontier _ r hr]⟩

/-- The full hyperbolic canonical boundary is exactly two distinct disjoint actual complementary branches. -/
theorem hCanonicalRegion_hyperbolic_frontier_two_branches
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : realSLMobius A≠1)
    (ht : 4<(Matrix.trace A.val)^2) :
    ∃ S T : Set ℍ, IsHHypercycleBranch (hHyperbolicAxis A hA ht) S ∧
      IsHHypercycleBranch (hHyperbolicAxis A hA ht) T ∧ Disjoint S T ∧ S≠T ∧
      frontier (hCanonicalRegion A)=S∪T := by
  obtain ⟨r,hr,hfront⟩ := hCanonicalRegion_hyperbolic_frontier A hA ht
  obtain ⟨S,T,hS,hT,hd,hne,hlevel⟩ :=
    (hHyperbolicAxis A hA ht).distance_level_two_hypercycleBranches r hr
  exact ⟨S,T,hS,hT,hd,hne,hfront.trans hlevel⟩

/-- Every actual nonidentity conformal isometry has the source complementary-curve boundary,
with the necessary genuine singleton convention for a half-turn. -/
theorem hCanonicalRegion_frontier_complementary_curves
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : realSLMobius A≠1) :
    (∃ hE : Mobius.MobiusElliptic (realSLMobius A),
      let v := hEllipticCenter A ((realSLMobius_elliptic_iff A hE.1).mp hE)
      (Matrix.trace A.val=0 ∧ frontier (hCanonicalRegion A)={v}) ∨
        (Matrix.trace A.val≠0 ∧ frontier (hCanonicalRegion A)∈hMetricCircleFamily v)) ∨
    (∃ _hP : Mobius.MobiusParabolic (realSLMobius A), ∃ w : Mobius.ExtendedComplex,
      (realSLMobius A).val w=w ∧ IsHHorocycleAt w (frontier (hCanonicalRegion A))) ∨
    (∃ ht : 4<(Matrix.trace A.val)^2, ∃ S T : Set ℍ,
      IsHHypercycleBranch (hHyperbolicAxis A hA ht) S ∧
      IsHHypercycleBranch (hHyperbolicAxis A hA ht) T ∧ Disjoint S T ∧ S≠T ∧
      frontier (hCanonicalRegion A)=S∪T) := by
  rcases lt_trichotomy ((Matrix.trace A.val)^2) 4 with ht | ht | ht
  · have hE := (realSLMobius_elliptic_iff A hA).mpr ht
    exact Or.inl ⟨hE,hCanonicalRegion_elliptic_frontier A hE⟩
  · have hP := (realSLMobius_parabolic_iff A hA).mpr ht
    exact Or.inr (Or.inl ⟨hP,hCanonicalRegion_parabolic_frontier A hP⟩)
  · exact Or.inr (Or.inr ⟨ht,hCanonicalRegion_hyperbolic_frontier_two_branches A hA ht⟩)

end LowDimensionalTopology.Geometry.Hyperbolic
