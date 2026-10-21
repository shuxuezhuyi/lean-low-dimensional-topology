module
public import LowDimensionalTopology.Geometry.Mobius.Affine.Basic
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.FiniteRotationFundamentalDomains
@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology OnePoint Pointwise Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Inversive LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
local instance ellipticCounterSphereMeasurable : MeasurableSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := borel _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex
local instance ellipticCounterSphereBorel : BorelSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := ⟨rfl⟩
/-! Actual proper-subgroup obstruction for the elliptic example. -/

theorem ellipticCounter_rotation_two : (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator 2 : ℂ) = -1 := by
  have hp : _root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod 2 = Real.pi := by dsimp [_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod];ring
  rw [_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator,hp,Circle.coe_exp]
  exact Complex.exp_pi_mul_I

theorem ellipticCounter_rotation_four : (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator 4 : ℂ) = Complex.I := by
  have hp : _root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod 4 = Real.pi / 2 := by dsimp [_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod];ring
  rw [_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator,hp,Circle.coe_exp]
  simpa only [Complex.ofReal_div,Complex.ofReal_ofNat] using Complex.exp_pi_div_two_mul_I

/-- The order-two literal open angular sector is exactly the upper half-disc direction. -/
theorem ellipticCounter_sector_two : _root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPlaneSector 2 = {z : ℂ | 0 < z.im} := by
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.finiteRotationPlaneSector_eq_halfPlanes 2 (by decide)]
  have hp : _root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod 2 = Real.pi := by dsimp [_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod];ring
  have he : (Circle.exp (-Real.pi) : ℂ) = -1 := by
    rw [Circle.exp_neg,Circle.coe_inv]
    have hm : (Circle.exp Real.pi : ℂ) = -1 := by rw [Circle.coe_exp,Complex.exp_pi_mul_I]
    rw [hm]
    norm_num
  ext z
  simp only [mem_ofPred_eq,hp,he,neg_one_mul,Complex.neg_im,neg_lt_zero,and_self]

/-- A genuine quarter-turn is outside the proper half-turn subgroup. -/
theorem ellipticCounter_quarter_not_half :
    finiteMobiusRotationHom (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator 4) ∉ finiteMobiusRotationGroup 2 := by
  intro hg
  obtain ⟨i,hi⟩ := finiteMobiusRotation_mem_fin 2 (by decide) ⟨_,hg⟩
  have he := congrArg (fun f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup => f.val
    ((1:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) hi
  change (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling (Circle.toUnits
    (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator
    4))).val ((1:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) =
    (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling (Circle.toUnits
      (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator 2 ^
      i.val))).val ((1:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) at he
  simp only [_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling_coe,mul_one] at he
  have hc := OnePoint.coe_injective he
  change (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator 4 :
    ℂ) = (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator 2 ^ i.val : Circle) at hc
  rw [ellipticCounter_rotation_four,Circle.coe_pow,ellipticCounter_rotation_two] at hc
  have hi2 := i.isLt
  interval_cases i.val <;> have hh := congrArg Complex.im hc <;> norm_num at hh

/-- The proper half-turn subgroup is genuinely contained in the actual quarter-turn group. -/
theorem ellipticCounter_half_le_quarter : finiteMobiusRotationGroup 2 ≤ finiteMobiusRotationGroup 4 := by
  apply Subgroup.zpowers_le.mpr
  have hr : _root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator 2 = _root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator 4 ^ 2 := by
    apply Circle.coe_injective
    rw [Circle.coe_pow,ellipticCounter_rotation_two,ellipticCounter_rotation_four,Complex.I_sq]
  rw [hr,map_pow]
  exact (finiteMobiusRotationGroup 4).pow_mem (Subgroup.mem_zpowers _) 2

/-- The original pi-wide sector fails the genuine orbit-selector condition for a discrete quarter-turn group. -/
theorem ellipticCounter_half_sector_not_fundamental :
    ¬ IsFuchsianFundamentalDomain (finiteMobiusRotationData 4 (by decide))
      ((finiteMobiusRotationData 4 (by decide)).finiteCoordinate ⁻¹' _root_.LowDimensionalTopology.Geometry.Hyperbolic.finiteRotationDiscSector 2) := by
  let P := finiteMobiusRotationData 4 (by decide)
  let u : Complex.UnitDisc := Complex.UnitDisc.mk ((1+Complex.I)/4) (by
    calc ‖(1+Complex.I)/4‖ = ‖(1:ℂ)+Complex.I‖ / 4 := by rw [norm_div];norm_num
         _ ≤ (‖(1:ℂ)‖+‖Complex.I‖)/4 := div_le_div_of_nonneg_right (norm_add_le _ _) (by norm_num)
         _ < 1 := by norm_num)
  let v : Complex.UnitDisc := Complex.UnitDisc.mk (Complex.I * (u:ℂ)) (by
    rw [norm_mul,Complex.norm_I,one_mul]
    exact u.norm_lt_one)
  let x := P.finiteCoordinate.symm u
  let y := P.finiteCoordinate.symm v
  let g : finiteMobiusRotationGroup 4 :=
    ⟨finiteMobiusRotationHom (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator
      4),Subgroup.mem_zpowers _⟩
  have hx : x ∈ P.finiteCoordinate ⁻¹' _root_.LowDimensionalTopology.Geometry.Hyperbolic.finiteRotationDiscSector 2 := by
    change (P.finiteCoordinate (P.finiteCoordinate.symm u) :
      ℂ) ∈ _root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPlaneSector 2
    rw [P.finiteCoordinate.apply_symm_apply,ellipticCounter_sector_two]
    norm_num [u,Complex.div_im]
  have hy : y ∈ P.finiteCoordinate ⁻¹' _root_.LowDimensionalTopology.Geometry.Hyperbolic.finiteRotationDiscSector 2 := by
    change (P.finiteCoordinate (P.finiteCoordinate.symm v) :
      ℂ) ∈ _root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPlaneSector 2
    rw [P.finiteCoordinate.apply_symm_apply,ellipticCounter_sector_two]
    norm_num [v,u,Complex.div_im,Complex.mul_im,Complex.div_re]
  have hgy : g • x = y := by
    apply P.finiteCoordinate.injective
    apply Complex.UnitDisc.coe_injective
    have h := finiteMobiusRotation_finite_action 4 (by decide) 1 x
    simp only [pow_one,ellipticCounter_rotation_four] at h
    calc
      _ = Complex.I * (P.finiteCoordinate x : ℂ) := h
      _ = _ := by
        change Complex.I * (P.finiteCoordinate (P.finiteCoordinate.symm u) : ℂ) =
          (P.finiteCoordinate (P.finiteCoordinate.symm v) : ℂ)
        rw [P.finiteCoordinate.apply_symm_apply,P.finiteCoordinate.apply_symm_apply]
        rfl
  intro hF
  have he : y = x := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain.eq_of_mem _ _ hF hy hx (Quotient.sound ⟨g,hgy⟩)
  have hr := congrArg (fun z => (P.finiteCoordinate z : ℂ).re) he
  norm_num [x,y,v,u,Complex.mul_re,Complex.div_re,Complex.div_im] at hr

/-- The counterexample's entire original quarter-turn subgroup is genuinely discrete. -/
theorem ellipticCounter_quarter_discrete : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (finiteMobiusRotationGroup 4) :=
  (finiteMobiusRotationData 4 (by decide)).discrete

/-- The chosen proper subgroup is generated by a genuine nonidentity elliptic element. -/
theorem ellipticCounter_half_elliptic : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (finiteMobiusRotationHom (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator 2)) := by
  let finiteSectorCounterFinite := finiteMobiusRotation_finite 2 (by decide)
  let g : finiteMobiusRotationGroup 2 := ⟨_,Subgroup.mem_zpowers _⟩
  have hg : g.val ≠ 1 := by
    intro he
    have hh := congrArg (fun f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup => f.val
      ((1:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) he
    change (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling (Circle.toUnits
      (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator
      2))).val ((1:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) =
      ((1:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) at hh
    rw [_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling_coe,mul_one] at hh
    have hc : (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator 2 :
      ℂ) = 1 := OnePoint.coe_injective hh
    rw [ellipticCounter_rotation_two] at hc
    norm_num at hc
  obtain ⟨n,hn,he⟩ := isOfFinOrder_iff_pow_eq_one.mp (isOfFinOrder_of_finite g)
  exact _root_.LowDimensionalTopology.Geometry.Mobius.mobius_finite_order_elliptic g.val hg
    (isOfFinOrder_iff_pow_eq_one.mpr ⟨n,hn,congrArg Subtype.val he⟩)

/-- Every actual element of the counterexample group fixes the original center. -/
theorem ellipticCounter_center_fixed (g : finiteMobiusRotationGroup 4) :
    g • (finiteMobiusRotationData 4 (by decide)).finiteCoordinate.symm 0 =
      (finiteMobiusRotationData 4 (by decide)).finiteCoordinate.symm 0 := by
  let P := finiteMobiusRotationData 4 (by decide)
  obtain ⟨i,hi⟩ := finiteMobiusRotation_mem_fin 4 (by decide) g
  have hg : g = ⟨finiteMobiusRotationHom (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator 4 ^
    i.val),
      finiteMobiusRotation_power_mem 4 i.val⟩ := Subtype.ext hi
  rw [hg]
  apply P.finiteCoordinate.injective
  apply Complex.UnitDisc.coe_injective
  rw [finiteMobiusRotation_finite_action 4 (by decide) i.val,
    P.finiteCoordinate.apply_symm_apply]
  simp only [Complex.UnitDisc.coe_zero,mul_zero]

/-- There are no moving-center cuts here: the geometric common exterior is the entire disc. -/
theorem ellipticCounter_moving_center_region_univ :
    stabilizerDirichletRegion (finiteMobiusRotationData 4 (by decide))
      ((finiteMobiusRotationData 4 (by decide)).finiteCoordinate.symm 0) = univ := by
  apply eq_univ_of_forall
  intro x g hmove
  exact False.elim (hmove (ellipticCounter_center_fixed g))

end LowDimensionalTopology.Geometry.Fuchsian
