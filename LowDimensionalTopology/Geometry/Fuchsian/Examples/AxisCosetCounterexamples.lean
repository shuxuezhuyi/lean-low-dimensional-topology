module
public import LowDimensionalTopology.Geometry.Mobius.Affine.Basic
public import LowDimensionalTopology.Geometry.Fuchsian.Axis.PrimitiveAxisIntersection
public import LowDimensionalTopology.Geometry.DiscreteGroups.Domain.MobiusOrbitCounterexamples
@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set
open scoped OnePoint Pointwise UpperHalfPlane Topology
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The concrete dilation by two is an actual positive native-axis generator. -/
theorem axisCounterexampleDilation_eq_stable :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.orbitCounterexampleDilation = _root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation (Real.log 2) := by
  change _root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling _ = _root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling _
  apply congrArg _root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling
  apply Units.ext
  simp only [Units.val_mk0,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.orbitCounterexampleDilationUnit,Real.exp_log (by norm_num : (0:ℝ)<2)]
  norm_num

/-- Every concrete power has its genuine positive real coefficient, including negative powers. -/
theorem axisCounterexampleDilation_zpow_real (n : ℤ) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.orbitCounterexampleDilation^n =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL ((2:ℝ)^n) (zpow_pos (by norm_num) n)) := by
  rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.orbitCounterexampleDilation_zpow,realSLMobius_verticalDilation]
  apply congrArg _root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling
  apply Units.ext
  simp only [Units.val_zpow_eq_zpow_val,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.orbitCounterexampleDilationUnit,Units.val_mk0]
  exact (Complex.ofReal_zpow 2 n).symm

/-- The counterexample uses a genuine discrete original half-plane group. -/
theorem axisCounterexampleGroupData : HalfPlaneFuchsianGroup _root_.LowDimensionalTopology.Geometry.DiscreteGroups.orbitCounterexampleDilationGroup where
  preserves g := by
    obtain ⟨n,hn⟩ := Subgroup.mem_zpowers_iff.mp g.property
    rw [←hn,axisCounterexampleDilation_zpow_real]
    exact realSLMobius_image_openHalfPlane _
  discrete := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.orbitCounterexampleDilationGroup_discrete

/-- The square is still a genuine hyperbolic element of the original group. -/
theorem axisCounterexampleSquare_hyperbolic : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.orbitCounterexampleDilation^2) := by
  have he : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.orbitCounterexampleDilation^2 = _root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation (2*Real.log 2) := by
    change (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScalingHom _root_.LowDimensionalTopology.Geometry.DiscreteGroups.orbitCounterexampleDilationUnit)^2 = _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScalingHom _
    rw [←map_pow]
    apply congrArg _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScalingHom
    apply Units.ext
    simp only [Units.val_pow_eq_pow_val,Units.val_mk0,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.orbitCounterexampleDilationUnit]
    rw [show 2*Real.log (2:ℝ) = Real.log 2+Real.log 2 by ring,Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<2)]
    norm_num
  rw [he]
  exact _root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation_hyperbolic _ (mul_pos (by norm_num) (Real.log_pos (by norm_num)))

/-- Actual simplicity does not imply that the chosen cyclic subgroup is the full axis stabilizer. -/
theorem axisCounterexampleSquare_simple :
    IsSimple _root_.LowDimensionalTopology.Geometry.DiscreteGroups.orbitCounterexampleDilationGroup (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.orbitCounterexampleDilation^2) := by
  refine ⟨Subgroup.npow_mem_zpowers _ _,axisCounterexampleSquare_hyperbolic,?_⟩
  intro g hg
  obtain ⟨n,rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  left
  rw [←_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusGeodesicAxis_conjugation]
  have hc : Commute (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.orbitCounterexampleDilation^n) (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.orbitCounterexampleDilation^2) :=
    ((Commute.refl _root_.LowDimensionalTopology.Geometry.DiscreteGroups.orbitCounterexampleDilation).zpow_left
      n).pow_right 2
  rw [hc.eq,mul_assoc,mul_inv_cancel,mul_one]

/-- The genuine dilation generator is outside the cyclic subgroup generated by its square. -/
theorem axisCounterexampleDilation_not_square_zpowers :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.orbitCounterexampleDilation ∉ Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.orbitCounterexampleDilation^2) := by
  have hh : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic _root_.LowDimensionalTopology.Geometry.DiscreteGroups.orbitCounterexampleDilation := by
    rw [axisCounterexampleDilation_eq_stable]
    exact _root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation_hyperbolic _ (Real.log_pos (by norm_num))
  have ho : orderOf _root_.LowDimensionalTopology.Geometry.DiscreteGroups.orbitCounterexampleDilation = 0 := orderOf_eq_zero_iff.mpr
    (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobius_parabolic_or_loxodromic_not_isOfFinOrder _ (Or.inr
      hh.1))
  rw [mem_zpowers_pow_iff,ho]
  norm_num

/-- The omitted cyclic coset contains an element preserving the entire true native axis. -/
theorem axisCounterexampleDilation_image_axis :
    letI := axisCounterexampleGroupData.nativeAction
    let g : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.orbitCounterexampleDilationGroup := ⟨_root_.LowDimensionalTopology.Geometry.DiscreteGroups.orbitCounterexampleDilation,Subgroup.mem_zpowers _⟩
    (g • ·) '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).carrier = (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).carrier := by
  let nativeAxisCounterexampleAction := axisCounterexampleGroupData.nativeAction
  let g : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.orbitCounterexampleDilationGroup := ⟨_root_.LowDimensionalTopology.Geometry.DiscreteGroups.orbitCounterexampleDilation,Subgroup.mem_zpowers _⟩
  have he (z : ℍ) : g • z = _root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL 2 (by norm_num) • z := by
    apply axisCounterexampleGroupData.nativeAction_realSL
    exact (realSLMobius_verticalDilation 2 (by norm_num)).trans rfl
  change (g • ·) '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical
    0).carrier = (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).carrier
  rw [show (g • · : ℍ → ℍ) = (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL 2 (by norm_num) • ·) from funext he]
  exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL_axis_image 2 (by norm_num)

/-- For the original bare cyclic choice the literal strict source intersection is empty, despite genuine discreteness and simplicity. -/
theorem axisCounterexample_cyclic_nearest_region_empty :
    letI := axisCounterexampleGroupData.nativeAction
    {z : ℍ | ∀ g : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.orbitCounterexampleDilationGroup,
      g.val ∉ Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.orbitCounterexampleDilation^2) →
        Metric.infDist z (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).carrier <
          Metric.infDist z ((g • ·) '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).carrier)} = ∅ := by
  let nativeAxisCounterexampleNearestAction := axisCounterexampleGroupData.nativeAction
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro z hz
  let g : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.orbitCounterexampleDilationGroup := ⟨_root_.LowDimensionalTopology.Geometry.DiscreteGroups.orbitCounterexampleDilation,Subgroup.mem_zpowers _⟩
  have hh := hz g axisCounterexampleDilation_not_square_zpowers
  rw [axisCounterexampleDilation_image_axis] at hh
  exact lt_irrefl _ hh

end LowDimensionalTopology.Geometry.Fuchsian
