/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.ModelMaps.HalfPlaneH3
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.EllipticFree.EllipticFreeParabolicBound
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.CanonicalRegion.CanonicalRegionFormulas
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The actual vertical-plane embedding preserves the genuine Euclidean separation. -/
theorem halfPlaneH3Embed_euclidean_dist_sq (z w : ℍ) :
    dist (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed z).val (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed w).val ^2=‖(z:ℂ)-w‖^2 := by
  rw [dist_eq_norm]
  change ‖((_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed z).val:Quaternion
    ℝ)-((_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed w).val:Quaternion ℝ)‖^2=_
  rw [pow_two,←Quaternion.normSq_eq_norm_mul_self,←Complex.normSq_eq_norm_sq]
  simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed,_root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.upperHalfSpacePoint,_root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.quaternionThreePoint,Quaternion.normSq_def',
    Complex.normSq_apply]
  ring

/-- The embedding preserves the actual hyperbolic path metric, not merely the topology. -/
theorem halfPlaneH3Embed_pathDist (z w : ℍ) :
    _root_.LowDimensionalTopology.Geometry.Mobius.upperHalfSpacePathDist (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed z) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed w)=dist z w := by
  apply Real.cosh_injOn (show 0≤_root_.LowDimensionalTopology.Geometry.Mobius.upperHalfSpacePathDist _ _ from
    ENNReal.toReal_nonneg)
    dist_nonneg
  rw [_root_.LowDimensionalTopology.Geometry.Mobius.upperHalfSpacePathDist,_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfSpacePathDist_cosh (by norm_num : 1≤2),
    _root_.LowDimensionalTopology.Geometry.Mobius.upperHalfSpaceHyperbolicHomeomorph_val,_root_.LowDimensionalTopology.Geometry.Mobius.upperHalfSpaceHyperbolicHomeomorph_val,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfSpaceHeight_apply,_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfSpaceHeight_apply,_root_.LowDimensionalTopology.Geometry.Mobius.euclideanThreeQuaternion_symm_height,
    _root_.LowDimensionalTopology.Geometry.Mobius.euclideanThreeQuaternion_symm_height]
  rw [←dist_eq_norm,←_root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.dist_map,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.apply_symm_apply,_root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.apply_symm_apply,
    halfPlaneH3Embed_euclidean_dist_sq]
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlane_cosh_dist_eq_norm_sq_formula]
  rfl

/-- Every original real-Mobius half-displacement is the genuine H3 displacement at the embedded point. -/
theorem halfPlaneH3Embed_sinh_displacement (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : ℍ) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusSinhDisplacement (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed z)=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) z := by
  unfold _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusSinhDisplacement
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed_realSL,halfPlaneH3Embed_pathDist]
  rfl

/-- Actual parabolics without a common boundary fixed point generate a non-elementary group. -/
theorem parabolic_pair_nonElementary_of_no_common_fixed (f g :
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hf : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f) (hn : ¬∃ p :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex,f.val p=p ∧ g.val p=p) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({f,g} : Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)) := by
  intro he
  have hfmem : f∈Subgroup.closure ({f,g} : Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hgmem : g∈Subgroup.closure ({f,g} : Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  obtain ⟨p,_,hall⟩:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.elementary_parabolic_common_fixedPoint _ he f hfmem hf
  exact hn ⟨p,hall ⟨f,hfmem⟩,hall ⟨g,hgmem⟩⟩

/-- The sharp elliptic-free product bound holds at every actual point of the native plane. -/
theorem native_ellipticFree_parabolic_product (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hD : _root_.LowDimensionalTopology.Geometry.Mobius.HasInvariantComplexDisc H) (hE :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree H)
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hAm : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A∈H) (hBm :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B∈H)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A))
    (hn : ¬∃ p : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex,(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val p=p ∧ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B).val p=p) (z : ℍ) :
    1≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) z*_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B) z := by
  have hb:=ellipticFree_parabolic_displacement H hD hE ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
    A,hAm⟩
    ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      B,hBm⟩ hA (parabolic_pair_nonElementary_of_no_common_fixed _ _ hA hn)
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed z)
  change 1≤_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusSinhDisplacement (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed z)*
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusSinhDisplacement (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed z) at hb
  rwa [halfPlaneH3Embed_sinh_displacement,halfPlaneH3Embed_sinh_displacement] at hb

/-- The original native canonical regions of distinct parabolic ends are disjoint. -/
theorem canonical_parabolic_regions_disjoint (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hD : _root_.LowDimensionalTopology.Geometry.Mobius.HasInvariantComplexDisc H) (hE :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree H)
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hAm : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A∈H) (hBm :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B∈H)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (hB :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (hn : ¬∃ p : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex,(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val p=p ∧ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B).val p=p) :
    Disjoint (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion A) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion B) := by
  apply Set.disjoint_left.mpr
  intro z hzA hzB
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.canonical_region_parabolic A hA] at hzA
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.canonical_region_parabolic B hB] at hzB
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) z<1 at hzA
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B) z<1 at hzB
  have hp:=native_ellipticFree_parabolic_product H hD hE A B hAm hBm hA hn z
  have hm : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) z*_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B) z<1 := by
    calc
      _≤1*_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B) z :=
        mul_le_mul_of_nonneg_right hzA.le (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement_nonneg _
          _)
      _<1 := by simpa only [one_mul] using hzB
  exact (not_lt_of_ge hp) hm

/-- Distinct actual parabolic fixed points imply precisely the no-common-fixed condition. -/
theorem parabolic_fixed_points_no_common (f g : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hf : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f) (hg :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic g) (p q :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    (hp : f.val p=p) (hq : g.val q=q) (hne : p≠q) :
    ¬∃ r : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex,f.val r=r ∧ g.val r=r := by
  rintro ⟨r,hrf,hrg⟩
  obtain ⟨a,ha⟩:=hf.2
  obtain ⟨b,hb⟩:=hg.2
  have hpr : p=r := ((ha p).mp hp).trans ((ha r).mp hrf).symm
  have hqr : q=r := ((hb q).mp hq).trans ((hb r).mp hrg).symm
  exact hne (hpr.trans hqr.symm)

/-- The literal distinct-fixed-point formulation. -/
theorem canonical_parabolic_regions_disjoint_fixed_points (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hD : _root_.LowDimensionalTopology.Geometry.Mobius.HasInvariantComplexDisc H) (hE :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree H)
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hAm : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A∈H) (hBm :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B∈H)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (hB :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (p q : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hp :
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val p=p) (hq :
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B).val q=q)
    (hpq : p≠q) : Disjoint (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion
      A) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion B) :=
  canonical_parabolic_regions_disjoint H hD hE A B hAm hBm hA hB
    (parabolic_fixed_points_no_common _ _ hA hB p q hp hq hpq)

end LowDimensionalTopology.Geometry.Fuchsian
