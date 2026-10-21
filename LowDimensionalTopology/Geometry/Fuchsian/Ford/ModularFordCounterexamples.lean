/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.ModularTriangleExample
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.NativeFuchsianPolygons
public import LowDimensionalTopology.Geometry.Fuchsian.CanonicalRegion.PrimitiveCanonicalRegions
public import LowDimensionalTopology.Geometry.Surfaces.Quotient.StableSets
public import LowDimensionalTopology.Geometry.Fuchsian.Modular.ModularShiftedCycles
public import LowDimensionalTopology.Geometry.Fuchsian.Modular.ModularShiftedStraightAngle
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.Elliptic.EllipticPointHeights
public import LowDimensionalTopology.Geometry.Fuchsian.Ford.FordHalfOpenCycles
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Side.PolygonSideInteriors
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane OnePoint MatrixGroups Topology
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Auxiliary.Analysis

/-- The genuine integral modular action fixes infinity exactly when its
original integer matrix has lower-left coefficient zero. -/
theorem modularIntegral_fix_infty_iff (A : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    (integralHalfPlaneMobiusHom A).val ∞=∞ ↔ A 1 0=0 := by
  change (_root_.LowDimensionalTopology.Geometry.Mobius.specialLinearProjection
    (Matrix.SpecialLinearGroup.map Complex.ofRealHom
      (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)
        A)):Equiv.Perm _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∞=∞ ↔ _
  rw [_root_.LowDimensionalTopology.Geometry.Mobius.Classification.specialLinear_fixes_infty_iff]
  simp [Matrix.SpecialLinearGroup.map_apply_coe,RingHom.mapMatrix_apply,Matrix.map_apply]

/-- A literal unipotent integral matrix projects to the corresponding
integer power of the actual unit translation. -/
theorem modularIntegral_upper_unit_projection (A : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (hc : A 1 0=0) (ha : A 0 0=1) (hd : A 1 1=1) :
    integralHalfPlaneMobiusHom A=(_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1)^(A 0 1) := by
  have hR : Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) A=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (A 0 1:ℝ):=by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.SpecialLinearGroup.map_apply_coe,RingHom.mapMatrix_apply,Matrix.map_apply,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL,hc,ha,hd]
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (Matrix.SpecialLinearGroup.map (Int.castRingHom
    ℝ) A)=_
  rw [hR,←_root_.LowDimensionalTopology.Geometry.Fuchsian.realSLMobius_unitTranslation,←map_zpow,hTranslationSL_zpow]
  simp

/-- Opposite integral determinant-one representatives have the same actual
original Mobius action. -/
theorem modularIntegral_neg_projection (A : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    integralHalfPlaneMobiusHom (-A)=integralHalfPlaneMobiusHom A := by
  have hR : Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) (-A)=
      -(Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) A):=by
    ext i j
    simp [Matrix.SpecialLinearGroup.map_apply_coe,RingHom.mapMatrix_apply,Matrix.map_apply]
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (Matrix.SpecialLinearGroup.map (Int.castRingHom
    ℝ) (-A))=_
  rw [hR,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_neg]
  rfl

/-- The full original modular infinity stabilizer contains exactly the
actual integer powers of the unit translation. -/
theorem modularIntegral_infty_stabilizer :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessGroup ∞=Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1) := by
  have hT : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1∈_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessGroup:=
    Subgroup.subset_closure (by exact Or.inl rfl)
  apply le_antisymm
  · intro f hf
    obtain ⟨hfG,hfi⟩:=(_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer _ _ _).mp hf
    rw [←integralHalfPlaneMobiusHom_range] at hfG
    obtain ⟨A,rfl⟩:=hfG
    have hc:=(modularIntegral_fix_infty_iff A).mp hfi
    have hdet : A 0 0*A 1 1=1:=by
      have h:=A.property
      rwa [Matrix.det_fin_two,hc,mul_zero,sub_zero] at h
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdet with ⟨ha,hd⟩|⟨ha,hd⟩
    · rw [modularIntegral_upper_unit_projection A hc ha hd]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _
    · have hc' : (-A) 1 0=0:=by simp [hc]
      have ha' : (-A) 0 0=1:=by simp [ha]
      have hd' : (-A) 1 1=1:=by simp [hd]
      rw [←modularIntegral_neg_projection A,modularIntegral_upper_unit_projection (-A) hc' ha' hd']
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _
  · apply Subgroup.zpowers_le.mpr
    exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer _ _
      _).mpr ⟨hT,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_infty 1⟩

/-- The actual unit translation is primitive in the full genuine modular
group, including the original entire infinity stabilizer condition. -/
theorem modularIntegral_unitTranslation_primitive :
    IsPrimitive _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessGroup (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1) := by
  apply (primitive_iff_of_parabolic ((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_parabolic_iff 1).mpr (by norm_num))).mpr
  refine ⟨Subgroup.subset_closure (by exact Or.inl rfl),?_⟩
  intro p hp
  cases p using OnePoint.rec with
  | infty => exact modularIntegral_infty_stabilizer.symm
  | coe z =>
      have he : z+1=z:=by
        exact OnePoint.coe_injective ((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_coe 1
          z).symm.trans hp)
      have hr:=congrArg Complex.re he
      simp only [Complex.add_re,Complex.one_re] at hr
      linarith

/-- The original full modular group has genuine discrete half-plane data. -/
theorem modularIntegral_halfPlaneData : HalfPlaneFuchsianGroup _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessGroup where
  preserves g:=by
    have hg : g.val∈integralHalfPlaneMobiusHom.range:=
      (show _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessGroup ≤ integralHalfPlaneMobiusHom.range by
        rw [integralHalfPlaneMobiusHom_range]) g.property
    obtain ⟨A,he⟩:=hg
    rw [←he]
    exact realSLMobius_image_openHalfPlane (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) A)
  discrete:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessGroup_discrete
/-- The full integral Mobius map acts on every actual native point by the
same faithful modular isometry used in the original polygon computations. -/
theorem modularIntegral_boundary_action (A : Matrix.SpecialLinearGroup (Fin 2) ℤ) (z : ℍ) :
    (integralHalfPlaneMobiusHom A).val ((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=
      (((modularNativeHom A z:ℍ):ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) :=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action (Matrix.SpecialLinearGroup.map (Int.castRingHom
    ℝ) A) z

/-- The actual whole modular sphere orbit is exactly its genuine native
half-plane orbit, with no orbit-membership assumption substituted. -/
theorem modularIntegral_boundary_orbit (z w : ℍ) :
    ((w:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈MulAction.orbit _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessGroup ((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ↔
      w∈MulAction.orbit modularNativeHom.range z := by
  constructor
  · rintro ⟨g,hg⟩
    have hgR : g.val∈integralHalfPlaneMobiusHom.range:=
      (show _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessGroup ≤ integralHalfPlaneMobiusHom.range by
        rw [integralHalfPlaneMobiusHom_range]) g.property
    obtain ⟨A,hA⟩:=hgR
    refine ⟨⟨modularNativeHom A,⟨A,rfl⟩⟩,?_⟩
    apply UpperHalfPlane.ext
    apply OnePoint.coe_injective
    change g.val.val ((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=((w:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) at hg
    rw [←hA,modularIntegral_boundary_action] at hg
    exact hg
  · rintro ⟨g,hg⟩
    obtain ⟨A,hA⟩:=g.property
    have hAM : integralHalfPlaneMobiusHom A∈_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessGroup:=by
      rw [←integralHalfPlaneMobiusHom_range]
      exact ⟨A,rfl⟩
    refine ⟨⟨integralHalfPlaneMobiusHom A,hAM⟩,?_⟩
    change (integralHalfPlaneMobiusHom A).val ((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=((w:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    rw [modularIntegral_boundary_action,hA]
    exact congrArg (fun u:ℍ=>((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) hg

/-- The original actual modular stabilizer is trivial at the cut point. -/
theorem modularIntegral_cut_stabilizer_trivial (a : ℝ) (ha₁ : -(1/2)<a) (ha₂ : a<0)
    (f : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessGroup
      ((modularCutPoint a ha₁ ha₂:ℍ):ℂ)) : f=1 := by
  obtain ⟨hf,hfix⟩:=(_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer _ _
    _).mp f.property
  have hfR : f.val∈integralHalfPlaneMobiusHom.range:=by
    rw [integralHalfPlaneMobiusHom_range]
    exact hf
  obtain ⟨A,hA⟩:=hfR
  have hnative : modularNativeHom A (modularCutPoint a ha₁ ha₂)=modularCutPoint a ha₁ ha₂:=by
    apply UpperHalfPlane.ext
    apply OnePoint.coe_injective
    rw [←modularIntegral_boundary_action,hA]
    exact hfix
  have hg:=modularCutPoint_stabilizer_trivial a ha₁ ha₂
    ⟨modularNativeHom A,⟨A,rfl⟩⟩ hnative
  have hAid : integralHalfPlaneMobiusHom A=1:=by
    apply mobius_ext_on_halfPlane
    intro z
    rw [modularIntegral_boundary_action]
    have he:=congrArg (fun g:modularNativeHom.range=>g.val z) hg
    exact congrArg (fun u:ℍ=>((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) he
  apply Subtype.ext
  exact hA.symm.trans hAid

/-- Its independently defined original point-stabilizer order is exactly one. -/
theorem modularIntegral_cut_pointOrder (a : ℝ) (ha₁ : -(1/2)<a) (ha₂ : a<0) :
    fordPointOrder _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessGroup (modularCutPoint a ha₁ ha₂)=1 := by
  let K:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessGroup
    ((modularCutPoint a ha₁ ha₂:ℍ):ℂ)
  let modularIntegralCutUnique : Unique K:=⟨⟨1⟩,fun f=>modularIntegral_cut_stabilizer_trivial a ha₁ ha₂ f⟩
  exact Nat.card_unique

/-- Every original modular fundamental-region point maximizes its actual
height in its whole integral orbit; this is derived from the integer matrix
bottom row rather than imposed as a reduction hypothesis. -/
theorem modularIntegral_fd_height_max (A : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (z : ℍ) (hz : z∈ModularGroup.fd) : (A•z).im≤z.im := by
  have hrow : A 1 0≠0 ∨ A 1 1≠0:=by
    by_contra hh
    push Not at hh
    have hd : A 0 0*A 1 1-A 0 1*A 1 0=1:=by
      simpa only [Matrix.det_fin_two] using A.property
    simp only [hh.1,hh.2,mul_zero,sub_zero] at hd
    norm_num at hd
  have hbase:=integral_pair_quadratic_lower (A 1 0) (A 1 1) hrow
  let c : ℝ:=A 1 0
  let d : ℝ:=A 1 1
  have hcx : |(c*d)*(2*z.re)|≤|c*d|:=by
    rw [abs_mul]
    have hx : |2*z.re|≤1:=by
      rw [abs_mul]
      norm_num
      linarith only [hz.2]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hx (abs_nonneg (c*d))
  have hlo:= (abs_le.mp hcx).1
  have hprod : 0≤c^2*(Complex.normSq (z:ℂ)-1):=
    mul_nonneg (sq_nonneg c) (sub_nonneg.mpr hz.1)
  rw [ModularGroup.im_smul_eq_div_normSq]
  apply div_le_self z.im_pos.le
  change 1≤Complex.normSq ((A 1 0:ℂ)*(z:ℂ)+(A 1 1:ℂ))
  have hf : Complex.normSq ((A 1 0:ℂ)*(z:ℂ)+(A 1 1:ℂ))=
      c^2*Complex.normSq (z:ℂ)+2*c*d*z.re+d^2:=by
    simp [Complex.normSq_apply,c,d]
    ring
  rw [hf]
  change 1≤c^2+d^2-|c*d| at hbase
  nlinarith only [hbase,hlo,hprod]

/-- A native modular reduced point belongs to the literal common exterior
of every real lift of the full original Mobius modular group. -/
theorem modularIntegral_exterior_of_fd (z : ℍ) (hz : z∈ModularGroup.fd) :
    z∈_root_.LowDimensionalTopology.Geometry.Fuchsian.mobiusFordExterior _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessGroup := by
  intro A
  have hAR : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A.val∈integralHalfPlaneMobiusHom.range:=by
    rw [integralHalfPlaneMobiusHom_range]
    exact A.property
  obtain ⟨B,hB⟩:=hAR
  have hact : A.val•z=B•z:=by
    apply UpperHalfPlane.ext
    apply OnePoint.coe_injective
    rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action]
    change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      A.val).val ((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=
      (((modularNativeHom B z:ℍ):ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    rw [←hB,modularIntegral_boundary_action]
  apply (parabolicFord_im_le_iff_denominator A.val z).mp
  rw [hact]
  exact modularIntegral_fd_height_max B z hz

/-- Every point of the true shifted modular polygon lies in the literal
all-circle common exterior for the full original group. -/
theorem modularIntegral_shifted_subset_exterior (a : ℝ) (ha₁ : -(1/2)<a) (ha₂ : a<0) :
    modularShiftedPolygon a⊆_root_.LowDimensionalTopology.Geometry.Fuchsian.mobiusFordExterior _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessGroup := by
  intro z hz
  have hred:=(modularShiftReduced_spec a ha₁ ha₂ z hz).1
  have he:=modularIntegral_exterior_of_fd (modularShiftReduced z) hred
  by_cases hc : z.re≤1/2
  · simpa only [modularShiftReduced,modularShiftFold,ite_eq_left hc,one_smul] using he
  · have hT : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1∈_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessGroup:=
      Subgroup.subset_closure (by exact Or.inl rfl)
    have ht:=parabolicFordExterior_integer_translate _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessGroup hT (modularShiftReduced z) he 1
    have hact : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1•modularShiftReduced z=z:=by
      simp only [modularShiftReduced,modularShiftFold,ite_eq_right hc]
      apply UpperHalfPlane.ext
      rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL_coe,←zpow_neg_one,ModularGroup.coe_T_zpow_smul_eq]
      simp
    simpa only [Int.cast_one,hact] using ht

/-- True interior points lie strictly outside every genuine non-affine
integral isometric circle of the whole original modular group. -/
theorem modularIntegral_interior_den_strict (A : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (hc : A 1 0≠0) (z : ℍ)
    (hz : z∈interior (_root_.LowDimensionalTopology.Geometry.Fuchsian.mobiusFordExterior
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessGroup)) :
    1<‖_root_.LowDimensionalTopology.Geometry.Fuchsian.realSLDenominator (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) A) z‖ := by
  let R:=Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) A
  have hR : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius R∈_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessGroup:=by
    rw [←integralHalfPlaneMobiusHom_range]
    exact ⟨A,rfl⟩
  have hcR : R 1 0≠0:=by
    change (A 1 0:ℝ)≠0
    exact_mod_cast hc
  have hsub : _root_.LowDimensionalTopology.Geometry.Fuchsian.mobiusFordExterior _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessGroup⊆
      (fun u:ℍ=>‖_root_.LowDimensionalTopology.Geometry.Fuchsian.realSLDenominator R u‖) ⁻¹' Ici (1:ℝ):=by
    intro u hu
    exact hu ⟨R,hR⟩
  have hh:=interior_mono hsub hz
  have hcont : Continuous (fun u:ℍ=>‖_root_.LowDimensionalTopology.Geometry.Fuchsian.realSLDenominator R u‖):=by
    unfold _root_.LowDimensionalTopology.Geometry.Fuchsian.realSLDenominator UpperHalfPlane.denom
    fun_prop
  rw [←(parabolicFord_denominator_isOpenMap R hcR).preimage_interior_eq_interior_preimage hcont,
    interior_Ici] at hh
  exact hh

/-- The entire literal common-circle Ford domain is exactly the shifted
two-circle modular polygon previously proved fundamental. -/
theorem modularIntegral_Ford_domain_eq (a : ℝ) (ha₁ : -(1/2)<a) (ha₂ : a<0) :
    _root_.LowDimensionalTopology.Geometry.Fuchsian.mobiusFordDomain _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessGroup a=modularShiftedPolygon a := by
  ext z
  constructor
  · rintro ⟨hz,hl,hr⟩
    have hS:=modularIntegral_interior_den_strict ModularGroup.S (by decide) z hz
    have hDS : _root_.LowDimensionalTopology.Geometry.Fuchsian.realSLDenominator
        (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) ModularGroup.S) z=(z:ℂ):=by
      change (((ModularGroup.S 1 0:ℤ):ℝ):ℂ)*(z:ℂ)+
        (((ModularGroup.S 1 1:ℤ):ℝ):ℂ)=(z:ℂ)
      norm_num [ModularGroup.S]
    rw [hDS] at hS
    let A:=ModularGroup.S*ModularGroup.T⁻¹
    have hAc : A 1 0≠0:=by
      norm_num [A,ModularGroup.S,Matrix.SpecialLinearGroup.coe_mul,
        ModularGroup.coe_T_inv,Matrix.mul_apply,Fin.sum_univ_two]
    have hA:=modularIntegral_interior_den_strict A hAc z hz
    have hden : _root_.LowDimensionalTopology.Geometry.Fuchsian.realSLDenominator (Matrix.SpecialLinearGroup.map
      (Int.castRingHom ℝ) A) z=
        (z:ℂ)-1:=by
      change ((((A 1 0:ℤ):ℝ):ℂ)*(z:ℂ)+(((A 1 1:ℤ):ℝ):ℂ))=(z:ℂ)-1
      norm_num [A,ModularGroup.S,Matrix.SpecialLinearGroup.coe_mul,
        ModularGroup.coe_T_inv,Matrix.mul_apply,Fin.sum_univ_two]
      ring
    rw [hden] at hA
    refine ⟨hl,hr,?_,?_⟩
    · rw [Complex.normSq_eq_norm_sq]
      nlinarith only [hS,norm_nonneg (z:ℂ)]
    · rw [Complex.normSq_eq_norm_sq]
      nlinarith only [hA,norm_nonneg ((z:ℂ)-1)]
  · intro hz
    refine ⟨?_,hz.1,hz.2.1⟩
    exact interior_maximal (modularIntegral_shifted_subset_exterior a ha₁ ha₂)
      (modularShiftedPolygon_isOpen a) hz

/-- The actual original-group closed Ford cycle is the genuine native
modular polygon cycle at every point. -/
theorem modularIntegral_Ford_cycle_eq_native (a : ℝ) (ha₁ : -(1/2)<a) (ha₂ : a<0) (z : ℍ) :
    _root_.LowDimensionalTopology.Geometry.Fuchsian.mobiusFordVertexCycle _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessGroup a z=
      modularNativePolygonCycle (modularShiftedPolygon a) z := by
  ext u
  exact and_congr (by rw [modularIntegral_Ford_domain_eq a ha₁ ha₂])
    (modularIntegral_boundary_orbit z u)

/-- The actual modular closed polygon cycle has only two representatives
in its literal half-open unit strip, even though its closed-cycle cardinal is three. -/
theorem modular_cut_cycle_halfOpen (a : ℝ) (ha₁ : -(1/2)<a) (ha₂ : a<0) :
    let w:=modularCutPoint a ha₁ ha₂
    modularNativePolygonCycle (modularShiftedPolygon a) w ∩ {u:ℍ | a≤u.re ∧ u.re<a+1}=
      {w,ModularGroup.S•w} := by
  let w:=modularCutPoint a ha₁ ha₂
  have hp:=modularCutPoint_properties a ha₁ ha₂
  have hSr : (ModularGroup.S•w).re=a:=by
    change (((ModularGroup.S•w:ℍ):ℂ)).re=a
    rw [modular_S_unit_circle w hp.2.1,Complex.neg_re,Complex.conj_re,UpperHalfPlane.coe_re,hp.1]
    ring
  have hTr : ((ModularGroup.T*ModularGroup.S)•w).re=a+1:=by
    rw [mul_smul,(modular_T_coordinates _).1,hSr]
  change modularNativePolygonCycle (modularShiftedPolygon a) w∩{u:ℍ | a≤u.re ∧ u.re<a+1}=
    {w,ModularGroup.S•w}
  rw [modular_cut_cycle]
  ext u
  simp only [Set.mem_inter_iff,Set.mem_insert_iff,Set.mem_singleton_iff,Set.mem_ofPred_eq]
  constructor
  · rintro ⟨rfl|rfl|rfl,h⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact False.elim ((lt_irrefl (a+1)) (hTr ▸ h.2))
  · rintro (rfl|rfl)
    · exact ⟨Or.inl rfl,by rw [hp.1];constructor <;> linarith only [ha₁,ha₂]⟩
    · exact ⟨Or.inr (Or.inl rfl),by rw [hSr];constructor <;> linarith⟩

/-- This is a genuine two-point half-open cycle, not a scalar counting model. -/
theorem modular_cut_cycle_halfOpen_card (a : ℝ) (ha₁ : -(1/2)<a) (ha₂ : a<0) :
    let w:=modularCutPoint a ha₁ ha₂
    (modularNativePolygonCycle (modularShiftedPolygon a) w ∩ {u:ℍ | a≤u.re ∧ u.re<a+1}).ncard=2 := by
  dsimp only
  rw [modular_cut_cycle_halfOpen]
  apply Set.ncard_pair
  intro he
  have hh:=congrArg UpperHalfPlane.re he
  have hp:=modularCutPoint_properties a ha₁ ha₂
  change (modularCutPoint a ha₁ ha₂).re=((ModularGroup.S•modularCutPoint a ha₁ ha₂:ℍ):ℂ).re at hh
  rw [modular_S_unit_circle _ hp.2.1,Complex.neg_re,Complex.conj_re,UpperHalfPlane.coe_re] at hh
  linarith only [hh,hp.2.2.1]

/-- The actual modular cut-point height strictly exceeds the claimed
accidental-cycle universal height when the closed and half-open counts are confused. -/
theorem modular_cut_height_gt_accidental_bound (a : ℝ) (ha₁ : -(1/2)<a) (ha₂ : a<0) :
    Real.sqrt 3/6<(modularCutPoint a ha₁ ha₂).im := by
  let w:=modularCutPoint a ha₁ ha₂
  have hp:=modularCutPoint_properties a ha₁ ha₂
  have hn:=hp.2.1
  rw [Complex.normSq_apply,UpperHalfPlane.coe_re,UpperHalfPlane.coe_im] at hn
  have him : 1/2<w.im:=by
    nlinarith only [hn,w.im_pos,hp.2.2.1,hp.2.2.2,sq_nonneg (w.re-1/2)]
  have hs : Real.sqrt 3<3:=by
    nlinarith only [Real.sq_sqrt (by norm_num : (0:ℝ)≤3),Real.sqrt_nonneg 3]
  linarith only [him,hs]

/-- The source expression at q*n=2 has a real tangent pole. Mathlib's
totalized real tangent value cannot stand for an infinite upper bound. -/
theorem cycleHeightBound_pole : cycleHeightBound 1 2=0 := by
  norm_num [cycleHeightBound,Real.tan_pi_div_two]

/-- The actual modular point is a strict counterexample to using the
source's pole formula as an ordinary totalized real inequality. -/
theorem modular_cut_height_not_le_pole (a : ℝ) (ha₁ : -(1/2)<a) (ha₂ : a<0) :
    ¬(modularCutPoint a ha₁ ha₂).im≤cycleHeightBound 1 2 := by
  rw [cycleHeightBound_pole]
  exact not_le_of_gt (modularCutPoint a ha₁ ha₂).im_pos

/-- A real fundamental-domain example simultaneously has a free original
point, closed-cycle cardinal three, half-open cardinal two, genuine angle pi
and height strictly above the accidental-cycle numerical claim. -/
theorem modular_actual_halfOpen_count_counterexample :
    ∃a:ℝ,∃ha₁:-(1/2)<a,∃ha₂:a<0,
      let w:=modularCutPoint a ha₁ ha₂
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain modularNativeHom.range ℍ MeasureTheory.volume (modularShiftedPolygon a) ∧
      (∀g:modularNativeHom.range,g.val w=w→g=1) ∧
      (modularNativePolygonCycle (modularShiftedPolygon a) w).ncard=3 ∧
      (modularNativePolygonCycle (modularShiftedPolygon a) w∩{u:ℍ | a≤u.re ∧ u.re<a+1}).ncard=2 ∧
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngle (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc '' closure (modularShiftedPolygon a))
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc w)=Real.pi ∧ Real.sqrt 3/6<w.im := by
  refine ⟨-1/10,by norm_num,by norm_num,modularShiftedPolygon_fundamental _ (by norm_num) (by norm_num),
    modularCutPoint_stabilizer_trivial _ _ _,modular_cut_cycle_card _ _ _,
    modular_cut_cycle_halfOpen_card _ _ _,?_,modular_cut_height_gt_accidental_bound _ _ _⟩
  rw [modularShiftedPolygon_closure]
  exact modularCutPoint_subtendedAngle _ _ _

/-- The first (left-edge) representative belongs to the same literal
original-group cycle as the modular cut point. -/
theorem modularIntegral_Ford_cycle_at_left (a : ℝ) (ha₁ : -(1/2)<a) (ha₂ : a<0) :
    let w:=modularCutPoint a ha₁ ha₂
    _root_.LowDimensionalTopology.Geometry.Fuchsian.mobiusFordVertexCycle _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessGroup a (ModularGroup.S•w)=
      modularNativePolygonCycle (modularShiftedPolygon a) w := by
  dsimp only
  rw [modularIntegral_Ford_cycle_eq_native a ha₁ ha₂]
  unfold modularNativePolygonCycle
  congr 1
  apply MulAction.orbit_eq_iff.mpr
  exact ⟨⟨modularNativeHom ModularGroup.S,⟨ModularGroup.S,rfl⟩⟩,rfl⟩

/-- Closed cycle length three at an actual accidental point forces the
source's genuine triple-tile vertex condition. -/
theorem parabolicFord_accidental_vertex_of_cycle_three {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (hp : IsPrimitive H
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1)) (z : ℍ)
    (hz : z∈closure (parabolicFordDomain H)) (hq : fordPointOrder H z=1)
    (hc : (_root_.LowDimensionalTopology.Geometry.Fuchsian.mobiusFordVertexCycle H 0 z).ncard=3) :
    IsFuchsianPolygonVertex P.cayleyData (P.cayleyCoordinate '' parabolicFordDomain H)
      (P.cayleyCoordinate z) := by
  let D:=P.cayleyCoordinate '' parabolicFordDomain H
  let x:=P.cayleyCoordinate z
  have hD:=primitive_unitTranslation_Ford_polygon P hp
  have hx : x∈closure D:=by
    rw [←P.cayleyCoordinate.image_closure]
    exact mem_image_of_mem _ hz
  have ho : fuchsianPointOrder P.cayleyData x=1:=by
    rw [parabolicFord_cayley_pointOrder,hq]
  have hn : fuchsianPolygonCycleLength P.cayleyData (fuchsianPolygonCycle P.cayleyData D x)=3:=by
    change (fuchsianPolygonCycle P.cayleyData D x).ncard=3
    rw [parabolicFord_cycle_cayley,Set.ncard_image_of_injective _ P.cayleyCoordinate.injective,hc]
  have hnx : x∉D:=by
    intro hi
    have h1:=((hD.interior_iff_order_one_and_cycle_length_one hx).mp hi).2
    exact (by decide : (3:ℕ)≠1) (hn.symm.trans h1)
  have hf : x∈frontier D:=by
    have hDo:=((isFuchsianFundamentalDomain_iff P.cayleyData D).mp hD.locallyFinite.fundamental).1
    rw [hDo.frontier_eq]
    exact ⟨hx,hnx⟩
  by_contra hnv
  have h2:=(hD.accidental_two_cycle_iff_boundary_nonvertex hx
    ((isAccidentalFuchsianPoint_iff_pointOrder_one _ _).mpr ho)).mpr ⟨hf,hnv⟩
  exact (by decide : (3:ℕ)≠2) (hn.symm.trans h2)

/-- An original discrete Mobius group with primitive entire infinity
stabilizer has a genuine accidental Ford vertex, closed cycle three and
half-open count two, above the printed accidental-cycle height bound. -/
theorem modular_original_Ford_counterexample :
    ∃H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup,∃P:HalfPlaneFuchsianGroup H,
      ∃_hp:IsPrimitive H (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1),∃z:ℍ,
        z∈closure (parabolicFordDomain H) ∧ z.re=0 ∧ fordPointOrder H z=1 ∧
        (_root_.LowDimensionalTopology.Geometry.Fuchsian.mobiusFordVertexCycle H 0 z).ncard=3 ∧
        (fordHalfOpenVertexCycle H 0 z).ncard=2 ∧
        IsFuchsianPolygonVertex P.cayleyData (P.cayleyCoordinate '' parabolicFordDomain H)
          (P.cayleyCoordinate z) ∧ Real.sqrt 3/6<z.im := by
  let a : ℝ:= -1/10
  have ha₁ : -(1/2)<a:=by norm_num [a]
  have ha₂ : a<0:=by norm_num [a]
  let w:=modularCutPoint a ha₁ ha₂
  let u:=ModularGroup.S•w
  let H:=fordTranslatedGroup _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessGroup (-a)
  let P:=fordTranslatedData modularIntegral_halfPlaneData (-a)
  have hp : IsPrimitive H (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1):=
    fordTranslatedGroup_primitive _ _ modularIntegral_unitTranslation_primitive
  let z:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (-a)•u
  have hw:=modularCutPoint_properties a ha₁ ha₂
  have hur : u.re=a:=by
    change (((ModularGroup.S•w:ℍ):ℂ)).re=a
    rw [modular_S_unit_circle w hw.2.1,Complex.neg_re,Complex.conj_re,UpperHalfPlane.coe_re,hw.1]
    ring
  have hui : u.im=w.im:=by
    change (((ModularGroup.S•w:ℍ):ℂ)).im=w.im
    rw [modular_S_unit_circle w hw.2.1,Complex.neg_im,Complex.conj_im,UpperHalfPlane.coe_im,neg_neg]
  have hu : u∈closure (_root_.LowDimensionalTopology.Geometry.Fuchsian.mobiusFordDomain _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessGroup a):=by
    rw [modularIntegral_Ford_domain_eq a ha₁ ha₂,modularShiftedPolygon_closure]
    exact (modular_cut_cycle_points_closed a ha₁ ha₂).2.1
  have hz : z∈closure (parabolicFordDomain H):=by
    rw [parabolicFordDomain_eq_mobiusFordDomain]
    simpa only [add_neg_cancel] using (fordTranslatedGroup_closure_mem
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessGroup (-a) a u).mpr hu
  have hzr : z.re=0:=by rw [fordTranslation_re,hur,add_neg_cancel]
  have hc : (_root_.LowDimensionalTopology.Geometry.Fuchsian.mobiusFordVertexCycle H 0 z).ncard=3:=by
    have he:=fordTranslatedGroup_cycle_ncard _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessGroup (-a) a u
    rw [modularIntegral_Ford_cycle_at_left a ha₁ ha₂,modular_cut_cycle_card] at he
    simpa only [add_neg_cancel] using he
  have hq : fordPointOrder H z=1:=by
    rw [fordTranslatedGroup_pointOrder]
    have hS : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (Matrix.SpecialLinearGroup.map
      (Int.castRingHom ℝ) ModularGroup.S)
        ∈_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessGroup:=by
      rw [←integralHalfPlaneMobiusHom_range]
      exact ⟨ModularGroup.S,rfl⟩
    have huR : (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) ModularGroup.S)•w=u:=by
      exact modularNativeHom_apply ModularGroup.S w
    rw [←huR,fordPointOrder_realSL_orbit _ _ hS]
    exact modularIntegral_cut_pointOrder a ha₁ ha₂
  have hn : (fordHalfOpenVertexCycle H 0 z).ncard=2:=by
    rw [fordHalfOpenVertexCycle_normalized_ncard P hp z hz hzr,hc]
  refine ⟨H,P,hp,z,hz,hzr,hq,hc,hn,
    parabolicFord_accidental_vertex_of_cycle_three P hp z hz hq hc,?_⟩
  rw [fordTranslation_im,hui]
  exact modular_cut_height_gt_accidental_bound a ha₁ ha₂

/-- The unqualified totalized-real tangent formula is false under the
literal original primitive-group and genuine Ford-vertex hypotheses. -/
theorem modular_original_Ford_real_pole_counterexample :
    ¬∀(H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (P:HalfPlaneFuchsianGroup H)
      (_hp:IsPrimitive H (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1)) (z:ℍ),
      z∈closure (parabolicFordDomain H) → z.re=0 →
      IsFuchsianPolygonVertex P.cayleyData (P.cayleyCoordinate '' parabolicFordDomain H)
        (P.cayleyCoordinate z) →
      z.im≤cycleHeightBound (fordPointOrder H z) (fordHalfOpenVertexCycle H 0 z).ncard := by
  intro hall
  obtain ⟨H,P,hp,z,hz,hr,hq,_hc,hn,hv,_hb⟩:=modular_original_Ford_counterexample
  have hh:=hall H P hp z hz hr hv
  rw [hq,hn,cycleHeightBound_pole] at hh
  exact (not_le_of_gt z.im_pos) hh

/-- The printed accidental-cycle height assertion fails even for a genuine
primitive whole group and its actual convex locally finite Ford polygon. -/
theorem modular_original_Ford_accidental_bound_counterexample :
    ¬∀(H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (P:HalfPlaneFuchsianGroup H)
      (_hp:IsPrimitive H (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1)) (z:ℍ),
      z∈closure (parabolicFordDomain H) → z.re=0 →
      IsFuchsianPolygonVertex P.cayleyData (P.cayleyCoordinate '' parabolicFordDomain H)
        (P.cayleyCoordinate z) → fordPointOrder H z=1 → z.im≤Real.sqrt 3/6 := by
  intro hall
  obtain ⟨H,P,hp,z,hz,hr,hq,_hc,_hn,hv,hb⟩:=modular_original_Ford_counterexample
  exact (not_le_of_gt hb) (hall H P hp z hz hr hv hq)

end LowDimensionalTopology.Geometry.Fuchsian
