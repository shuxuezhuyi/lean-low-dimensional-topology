/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Mobius.Affine.Basic
public import LowDimensionalTopology.Geometry.Fuchsian.CanonicalRegion.PrimitiveCanonicalTransport
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.Products.EllipticProducts
public import LowDimensionalTopology.Geometry.Hyperbolic.ModelMaps.HalfPlaneH3
public import LowDimensionalTopology.Geometry.DiscreteGroups.Elementary.AlternativeElementarity
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane MatrixGroups OnePoint
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- A finite subgroup of the actual complex units is the full root group of its own cardinality. -/
theorem primitive_finite_complexUnits_eq_rootsOfUnity (K : Subgroup ℂˣ) [Finite K] :
    K=rootsOfUnity (Nat.card K) ℂ := by
  let n:=Nat.card K
  have hn : n≠0 := Nat.card_pos.ne'
  let : NeZero n:=⟨hn⟩
  have hle : K ≤ rootsOfUnity n ℂ := by
    intro u hu
    rw [mem_rootsOfUnity]
    exact congrArg (fun v : K=> v.val) (pow_card_eq_one' (x:=(⟨u,hu⟩:K)))
  apply Subgroup.eq_of_le_of_card_ge hle
  rw [Complex.card_rootsOfUnity]

/-- Nonidentity roots have the exact nonzero residue angles required by the canonical ball comparison. -/
theorem primitive_complexUnitRoot_residue {n : ℕ} (hn : n≠0)
    (u : ℂˣ) (hu : u∈rootsOfUnity n ℂ) (hu1 : u≠1) :
    ∃i : ℕ,0 < i ∧ i < n ∧ Complex.exp (2*Real.pi*Complex.I*((i:ℂ)/n))=(u:ℂ) := by
  let : NeZero n:=⟨hn⟩
  obtain ⟨i,hi,he⟩ := (Complex.mem_rootsOfUnity n u).mp hu
  refine ⟨i,?_,hi,he⟩
  by_contra hnot
  have hi0 : i=0 := Nat.eq_zero_of_not_pos hnot
  apply hu1
  apply Units.ext
  rw [hi0] at he
  simpa only [Nat.cast_zero,zero_div,mul_zero,Complex.exp_zero,Units.val_one] using he.symm

/-- Folding the residue angle into the first quadrant gives the exact least sine bound. -/
theorem primitive_root_halfAngle_sin_le (n i : ℕ) (hn : 1 < n) (hi : 0 < i) (hin : i < n) :
    Real.sin (Real.pi/n) ≤ Real.sin (Real.pi*(i:ℝ)/n) := by
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast Nat.succ_le_of_lt hn
  have hnP : (0:ℝ) < n := lt_of_lt_of_le (by norm_num) hnR
  have hiR : (1:ℝ) ≤ i := by exact_mod_cast hi
  have hinR : (i:ℝ) < n := by exact_mod_cast hin
  have hbase : Real.pi/n∈Icc (-(Real.pi/2)) (Real.pi/2) := by
    constructor
    · have h:=div_pos Real.pi_pos hnP;linarith [Real.pi_pos]
    · apply (div_le_iff₀ hnP).mpr
      nlinarith [Real.pi_pos]
  by_cases hhalf : (i:ℝ) ≤ n/2
  · apply Real.strictMonoOn_sin.monotoneOn hbase
    · constructor
      · have hz : 0 ≤ Real.pi*(i:ℝ)/n := by positivity
        linarith [Real.pi_pos]
      · apply (div_le_iff₀ hnP).mpr
        nlinarith [Real.pi_pos]
    · exact (div_le_div_iff_of_pos_right hnP).mpr (by nlinarith [Real.pi_pos])
  · rw [←Real.sin_pi_sub (Real.pi*(i:ℝ)/n)]
    apply Real.strictMonoOn_sin.monotoneOn hbase
    · constructor
      · have hlt : Real.pi*(i:ℝ)/n < Real.pi :=
          (div_lt_iff₀ hnP).mpr (by nlinarith [Real.pi_pos])
        linarith [Real.pi_pos]
      · have hh : n/2 < (i:ℝ) := lt_of_not_ge hhalf
        have hlt : Real.pi/2 < Real.pi*(i:ℝ)/n :=
          (lt_div_iff₀ hnP).mpr (by nlinarith [Real.pi_pos])
        linarith
    · have hie : (i:ℝ)+1 ≤ n := by exact_mod_cast Nat.succ_le_of_lt hin
      apply (le_sub_iff_add_le).mpr
      rw [show Real.pi/n+Real.pi*(i:ℝ)/n=Real.pi*((i:ℝ)+1)/n by ring]
      exact (div_le_iff₀ hnP).mpr (by nlinarith [Real.pi_pos])

/-- The real circle polynomial of an elliptic is centered at its genuine fixed center. -/
theorem hCanonicalQuadratic_elliptic_center
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (z : ℍ) :
    let v:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA)
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalQuadratic A z=A 1 0*((z.re-v.re)^2+z.im^2+v.im^2) := by
  obtain ⟨ha,hd,hb,_hu,_hc⟩:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_elliptic_center_coefficients A hA
  simp only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalQuadratic]
  rw [ha,hd,hb]
  ring

/-- An elliptic canonical region always contains its actual native center, including a half-turn. -/
theorem hEllipticCenter_mem_canonicalRegion
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA)∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion A := by
  let v:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA)
  have hv : A•v=v := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_elliptic_fixed_iff A _ v).mpr rfl
  by_cases ht : Matrix.trace A.val=0
  · rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion_of_trace_zero _ ht]
    exact hv
  · rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion_of_trace_ne_zero _ ht]
    change Real.sinh (dist v (A•v)/2) < _
    rw [hv,dist_self,zero_div,Real.sinh_zero]
    exact div_pos (abs_pos.mpr ht) (by norm_num)

/-- At a common genuine center, larger squared trace gives a no-smaller actual canonical region. -/
theorem hCanonicalRegion_elliptic_subset_of_trace_sq_le
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (hB :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (hv : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA)=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB))
    (ht : (Matrix.trace A.val)^2≤(Matrix.trace B.val)^2) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion A⊆_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion B := by
  let v:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA)
  by_cases ha0 : Matrix.trace A.val=0
  · rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion_of_trace_zero A ha0]
    intro z hz
    have hzv : z=v := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_elliptic_fixed_iff A _ z).mp hz
    rw [hzv]
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A _∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion B
    rw [hv]
    exact hEllipticCenter_mem_canonicalRegion B hB
  · have hb0 : Matrix.trace B.val≠0 := by
      intro hb
      rw [hb,zero_pow (by norm_num : (2:ℕ)≠0)] at ht
      exact not_le_of_gt (sq_pos_of_ne_zero ha0) ht
    have hc : |B 1 0|≤|A 1 0| := by
      obtain ⟨_ha,_hd,_hb,hu,_hc⟩:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_elliptic_center_coefficients A hA
      obtain ⟨_ha',_hd',_hb',hu',_hc'⟩:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_elliptic_center_coefficients B hB
      rw [←hv] at hu'
      have hcsq : (B 1 0)^2≤(A 1 0)^2 := by
        have hp : 0 < v.im^2 := sq_pos_of_pos v.im_pos
        change (Matrix.trace A.val/2)^2+(A 1 0*v.im)^2=1 at hu
        change (Matrix.trace B.val/2)^2+(B 1 0*v.im)^2=1 at hu'
        rw [mul_pow] at hu hu'
        nlinarith
      exact (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mp (by simpa only [sq_abs] using hcsq)
    intro z hz
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion_mem_quadratic A
      ha0,hCanonicalQuadratic_elliptic_center A hA z] at hz
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion_mem_quadratic B
      hb0,hCanonicalQuadratic_elliptic_center B hB z,←hv]
    change |B 1 0*((z.re-v.re)^2+z.im^2+v.im^2)| < _
    change |A 1 0*((z.re-v.re)^2+z.im^2+v.im^2)| < _ at hz
    rw [abs_mul] at hz ⊢
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hc (abs_nonneg _)) hz

/-- Exact squared trace for the genuine standard element of a prescribed real rotation angle. -/
theorem mobiusStandardElement_exp_squaredTrace (θ : ℝ) (u : ℂˣ)
    (hu : (u:ℂ)=Complex.exp ((2*θ:ℝ)*Complex.I)) :
    _root_.LowDimensionalTopology.Geometry.Mobius.mobiusSquaredTrace (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusStandardElement u)=(4*(Real.cos θ)^2:ℝ) := by
  rw [_root_.LowDimensionalTopology.Geometry.Mobius.mobiusStandardElement_squaredTrace,hu,←Complex.exp_neg]
  have hneg : -((2*θ:ℝ)*Complex.I)=((-2*θ:ℝ):ℂ)*Complex.I := by push_cast;ring
  rw [hneg,Complex.exp_ofReal_mul_I,Complex.exp_ofReal_mul_I]
  apply Complex.ext <;>
    simp [Real.cos_two_mul] <;> ring

/-- Among nonidentity residue rotations, the smallest positive angle maximizes squared real trace. -/
theorem primitive_root_halfAngle_cos_sq_le (n i : ℕ) (hn : 1 < n) (hi : 0 < i) (hin : i < n) :
    (Real.cos (Real.pi*(i:ℝ)/n))^2≤(Real.cos (Real.pi/n))^2 := by
  have hs:=primitive_root_halfAngle_sin_le n i hn hi hin
  have h0 : 0≤Real.sin (Real.pi/n) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · positivity
    · apply (div_le_iff₀ (show (0:ℝ)<n by exact_mod_cast Nat.zero_lt_of_lt hn)).mpr
      have hnR : (1:ℝ)≤n := by exact_mod_cast Nat.le_of_lt hn
      nlinarith [Real.pi_pos]
  nlinarith [Real.sin_sq_add_cos_sq (Real.pi*(i:ℝ)/n),Real.sin_sq_add_cos_sq (Real.pi/n)]

/-- Every actual finite common-fixed-pair group has the full root-of-unity rotation model. -/
theorem primitive_finite_fixed_pair_full_root_model
    (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) [Finite H]
    (a b : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hab : a≠b) (hfix : ∀f∈H,f.val a=a ∧ f.val
      b=b) :
    ∃q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup,∀g : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup,
      g∈_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H ↔
        ∃u : ℂˣ,u∈rootsOfUnity (Nat.card H) ℂ ∧ g=_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling u := by
  obtain ⟨q,hfin,_hcyc,hmodel⟩ := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.finiteMobius_common_pair_conjugate_cyclic_rotations H a b hab hfix
  let K:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H
  let : Finite K:=hfin
  have hi : K≤_root_.LowDimensionalTopology.Geometry.Mobius.mobiusInftyStabilizer := by
    intro g hg
    obtain ⟨u,_hu,he⟩:=hmodel g hg
    change g.val ∞=∞
    rw [he,_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling_infty]
  have hz : ∀g∈K,g.val (0:ℂ)=(0:ℂ) := by
    intro g hg
    obtain ⟨u,_hu,he⟩:=hmodel g hg
    rw [he,_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling_coe,mul_zero]
  let φ:=_root_.LowDimensionalTopology.Geometry.Mobius.subgroupMultiplierHom K hi
  have hφ : Function.Injective φ:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.subgroupMultiplierHom_injective_of_fix_zero K hi hz
  let e:=MonoidHom.ofInjective hφ
  let : Finite φ.range:=Finite.of_surjective e e.surjective
  have hc : Nat.card φ.range=Nat.card H :=
    (Nat.card_congr e.toEquiv).symm.trans
      (Nat.card_congr (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence
        q H).toEquiv).symm
  have hR : φ.range=rootsOfUnity (Nat.card H) ℂ := by
    rw [primitive_finite_complexUnits_eq_rootsOfUnity φ.range,hc]
  refine ⟨q,?_⟩
  intro g
  constructor
  · intro hg
    let f : K:=⟨g,hg⟩
    refine ⟨φ f,?_,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.dilation_multiplier_representation K hi hz f⟩
    rw [←hR]
    exact ⟨f,rfl⟩
  · rintro ⟨u,hu,rfl⟩
    rw [←hR] at hu
    obtain ⟨f,rfl⟩:=hu
    rw [←_root_.LowDimensionalTopology.Geometry.DiscreteGroups.dilation_multiplier_representation K hi hz f]
    exact f.property

/-- Discreteness makes the genuine normalized stabilizer of every actual interior point finite. -/
theorem FuchsianDisc.normalized_interior_stabilizer_finite
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D : FuchsianDisc H) (z : ℍ) :
    Finite (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer D.normalizedGroup ((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) := by
  let K:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer D.normalizedGroup ((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
  have hle : K≤D.normalizedGroup:=fun f hf =>
    ((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer D.normalizedGroup
      ((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) f).mp hf).1
  apply _root_.LowDimensionalTopology.Geometry.DiscreteGroups.discreteMobius_finite_of_common_H3_fixed K
    (discreteMobius_subgroup_of_le _ _ D.normalizedGroup_discrete
      hle) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed z)
  intro f hf
  obtain ⟨B,hB⟩:=D.normalizedGroup_exists_realSL f (hle hf)
  have hfix := ((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer D.normalizedGroup
    ((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) f).mp hf).2
  rw [←hB,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action] at hfix
  have hzB : B•z=z := UpperHalfPlane.ext (OnePoint.coe_eq_coe.mp hfix)
  rw [←hB,_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed_realSL,hzB]

/-- A nontrivial finite genuine cyclic Mobius group has its entire standard root-group model. -/
theorem primitive_finite_cyclic_full_root_model
    (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) [Finite H] [IsCyclic H]
    (f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hf : f∈H) (hf0 : f≠1) :
    ∃q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup,∀g : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup,
      g∈_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H ↔
        ∃u : ℂˣ,u∈rootsOfUnity (Nat.card H) ℂ ∧ g=_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling u := by
  obtain ⟨g,hg⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top H).mp inferInstance
  have hgH : g∈H := by rw [←hg];exact Subgroup.mem_zpowers g
  have hg0 : g≠1 := by
    intro he
    have hmem : f∈Subgroup.zpowers g := hg ▸ hf
    obtain ⟨n,hn⟩:=Subgroup.mem_zpowers_iff.mp hmem
    rw [he,one_zpow] at hn
    exact hf0 hn.symm
  obtain ⟨a,b,hab,hfix⟩ := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.finiteMobius_nonidentity_two_fixed H (⟨g,hgH⟩:H)
    (by intro he;exact hg0 (congrArg Subtype.val he))
  apply primitive_finite_fixed_pair_full_root_model H a b hab
  intro k hk
  have hmem : k∈Subgroup.zpowers g := hg ▸ hk
  obtain ⟨n,rfl⟩:=Subgroup.mem_zpowers_iff.mp hmem
  exact ⟨primitive_mobius_zpow_fixed ((hfix a).mpr (Or.inl rfl)) n,
    primitive_mobius_zpow_fixed ((hfix b).mpr (Or.inr rfl)) n⟩

/-- A finite cyclic group contains its actual least-angle rotation, which generates the entire group. -/
theorem primitive_finite_cyclic_exists_least_rotation
    (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) [Finite H] [IsCyclic H]
    (f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hf : f∈H) (hf0 : f≠1) :
    ∃g∈H,Subgroup.zpowers g=H ∧ HasLeastEllipticRotation g ∧
      _root_.LowDimensionalTopology.Geometry.Mobius.mobiusSquaredTrace g=(4*(Real.cos (Real.pi/Nat.card H))^2:ℝ) ∧
      ∃q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup,∀k : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup,
        k∈_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H ↔
          ∃u : ℂˣ,u∈rootsOfUnity (Nat.card H) ℂ ∧ k=_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling u := by
  obtain ⟨q,hmodel⟩ := primitive_finite_cyclic_full_root_model H f hf hf0
  let N:=Nat.card H
  have hN : 1 < N := by
    have hm : (⟨f,hf⟩:H)≠1 := by intro he;exact hf0 (congrArg Subtype.val he)
    let : Nontrivial H:=⟨⟨_,_,hm⟩⟩
    let : Fintype H:=Fintype.ofFinite _
    change 1 < Nat.card H
    simpa only [Nat.card_eq_fintype_card] using (Fintype.one_lt_card : 1 < Fintype.card H)
  have hN0 : N≠0 := by omega
  let : NeZero N:=⟨hN0⟩
  let u : ℂˣ:=Units.mk0 (Complex.exp (2*Real.pi*Complex.I/N)) (Complex.exp_ne_zero _)
  have hu : IsPrimitiveRoot u N := IsPrimitiveRoot.coe_units_iff.mp (Complex.isPrimitiveRoot_exp N hN0)
  have hu0 : (u:ℂ)≠1 := by
    intro he
    have hu1 : u=1 := Units.ext he
    have horder:=hu.eq_orderOf
    rw [hu1,orderOf_one] at horder
    omega
  have hum : u∈rootsOfUnity N ℂ := by rw [mem_rootsOfUnity];exact hu.pow_eq_one
  have hscaled : _root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling u∈_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H :=
    (hmodel _).mpr ⟨u,hum,rfl⟩
  obtain ⟨g,hg,hgq⟩ := (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q
    H _).mp hscaled
  have hgen : Subgroup.zpowers g=H := by
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hg)
    rw [Nat.card_zpowers]
    have ho : orderOf g=N := by
      have hc := (MulAut.conj q).orderOf_eq g
      change orderOf (q*g*q⁻¹)=orderOf g at hc
      rw [hgq] at hc
      change orderOf (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScalingHom u)=orderOf g at hc
      rw [orderOf_injective _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScalingHom
        _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScaling_parameter_injective] at hc
      exact hc.symm.trans hu.eq_orderOf.symm
    rw [ho]
  have hleast : HasLeastEllipticRotation g := by
    refine ⟨N,hN,u,?_,rfl⟩
    apply isConj_iff.mpr
    refine ⟨q,?_⟩
    exact hgq.trans (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScaling_eq_standard u hu0)
  refine ⟨g,hg,hgen,hleast,?_,q,hmodel⟩
  rw [←_root_.LowDimensionalTopology.Geometry.Mobius.mobiusSquaredTrace_conjugation g
    q,hgq,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScaling_eq_standard u hu0]
  apply mobiusStandardElement_exp_squaredTrace
  dsimp [u]
  congr 1
  push_cast
  ring

/-- The full finite root model bounds the squared trace of every genuine nonidentity real lift. -/
theorem primitive_realSL_trace_bound_of_full_root_model
    (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hN : 1 < Nat.card H) (q :
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hmodel : ∀g : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup,g∈_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H ↔
      ∃u : ℂˣ,u∈rootsOfUnity (Nat.card H) ℂ ∧ g=_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling u)
    (B : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hB : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      B∈H) (hB0 : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B≠1) :
    (Matrix.trace B.val)^2≤4*(Real.cos (Real.pi/Nat.card H))^2 := by
  let N:=Nat.card H
  have hN0 : N≠0 := by omega
  have hm : q*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B*q⁻¹∈_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H :=
    (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q H
      _).mpr ⟨_,hB,rfl⟩
  obtain ⟨u,hu,he⟩ := (hmodel _).mp hm
  have hu0 : u≠1 := by
    intro hu1
    rw [hu1,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScaling_one] at he
    apply hB0
    have hh:=congrArg (fun g : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup=>q⁻¹*g*q) he
    simpa only [mul_assoc,inv_mul_cancel_left,mul_inv_cancel_left,inv_mul_cancel,mul_one] using hh
  obtain ⟨i,hi,hin,hui⟩ := primitive_complexUnitRoot_residue hN0 u hu hu0
  have huC : (u:ℂ)≠1 := fun he=>hu0 (Units.ext he)
  have ht : _root_.LowDimensionalTopology.Geometry.Mobius.mobiusSquaredTrace (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)=(4*(Real.cos (Real.pi*(i:ℝ)/N))^2:ℝ) := by
    rw [←_root_.LowDimensionalTopology.Geometry.Mobius.mobiusSquaredTrace_conjugation
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)
      q,he,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScaling_eq_standard u huC]
    apply mobiusStandardElement_exp_squaredTrace
    rw [←hui]
    congr 1
    push_cast
    ring
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_squaredTrace] at ht
  have htr : (Matrix.trace B.val)^2=4*(Real.cos (Real.pi*(i:ℝ)/N))^2 := Complex.ofReal_injective ht
  rw [htr]
  exact mul_le_mul_of_nonneg_left (primitive_root_halfAngle_cos_sq_le N i hN hi hin) (by norm_num)

/-- In a group with cyclic point stabilizers, any two fixed points of a nonidentity element
have the very same genuine stabilizer. -/
theorem primitive_stabilizers_eq_of_fixed_points
    (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hcyclic : ∀p :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex,IsCyclic
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H p))
    (f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hfH : f∈H) (hf : f≠1)
    (p q : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hfp : f.val p=p) (hfq : f.val q=q) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H p=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H q := by
  have hle (p q : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hfp : f.val p=p) (hfq : f.val q=q) :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H p≤_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H q := by
    let K:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H p
    let : IsCyclic K:=hcyclic p
    have hfK : f∈K := (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H p
      f).mpr ⟨hfH,hfp⟩
    intro g hg
    obtain ⟨hgH,hgp⟩ := (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H p g).mp hg
    refine (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H q g).mpr ⟨hgH,?_⟩
    by_cases hg0 : g=1
    · rw [hg0];rfl
    have hc : Commute f g := by
      have h := congrArg (fun k : K=>k.val) (IsMulCommutative.is_comm.comm (⟨f,hfK⟩:K) ⟨g,hg⟩)
      exact h
    rcases (_root_.LowDimensionalTopology.Geometry.Mobius.mobius_commute_iff_preserves_fixed_points_and_configuration f
      g hf hg0).2.mp hc with hs | ⟨_,_,_,_,hd⟩
    · exact (hs q).mp hfq
    · exact False.elim (Set.disjoint_left.mp hd hfp hgp)
  exact le_antisymm (hle p q hfp hfq) (hle q p hfq hfp)

/-- The least-angle elliptic condition has a lift-independent exact trace determined by its true order. -/
theorem HasLeastEllipticRotation.squaredTrace_order {f :
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (h : HasLeastEllipticRotation f) :
    _root_.LowDimensionalTopology.Geometry.Mobius.mobiusSquaredTrace f=(4*(Real.cos (Real.pi/orderOf f))^2:ℝ) := by
  obtain ⟨n,hn,u,hconj,hu⟩:=h
  have hn0 : n≠0 := by omega
  have hroot : IsPrimitiveRoot u n := IsPrimitiveRoot.coe_units_iff.mp
    (hu ▸ Complex.isPrimitiveRoot_exp n hn0)
  have hu0 : (u:ℂ)≠1 := by
    intro he
    have horder:=hroot.eq_orderOf
    have hu1 : u=1:=Units.ext he
    rw [hu1,orderOf_one] at horder
    omega
  obtain ⟨q,hq⟩:=isConj_iff.mp hconj
  have ho : orderOf f=n := by
    have he := (MulAut.conj q).orderOf_eq f
    change orderOf (q*f*q⁻¹)=orderOf f at he
    rw [hq,←_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScaling_eq_standard u hu0] at he
    change orderOf (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScalingHom u)=orderOf f at he
    rw [orderOf_injective _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScalingHom
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScaling_parameter_injective] at he
    exact he.symm.trans hroot.eq_orderOf.symm
  rw [ho,←_root_.LowDimensionalTopology.Geometry.Mobius.mobiusSquaredTrace_conjugation f q,hq]
  apply mobiusStandardElement_exp_squaredTrace
  rw [hu]
  congr 1
  push_cast
  ring

/-- In cyclic point stabilizers, generation at any one fixed point is generation at all of them. -/
theorem primitive_of_generating_one_elliptic_stabilizer
    (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hcyclic : ∀p :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex,IsCyclic
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H p))
    (f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hfH : f∈H) (hf :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f)
    (p : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hfp : f.val p=p)
    (hgen : Subgroup.zpowers f=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H p)
    (hleast : HasLeastEllipticRotation f) : IsPrimitive H f := by
  refine (primitive_iff_of_elliptic hf).mpr ⟨hfH,?_,hleast⟩
  intro q hfq
  exact hgen.trans (primitive_stabilizers_eq_of_fixed_points H hcyclic f hfH hf.1 p q hfp hfq)

/-- A finite genuine subgroup element is either the identity or a true elliptic. -/
theorem primitive_elliptic_of_finite_subgroup
    (K : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) [Finite K] (g :
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hg : g∈K) (hg0 : g≠1) :
    _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic g := by
  apply _root_.LowDimensionalTopology.Geometry.Mobius.mobius_finite_order_elliptic g hg0
  obtain ⟨n,hn,he⟩ := (isOfFinOrder_of_finite (⟨g,hg⟩:K)).exists_pow_eq_one
  apply isOfFinOrder_iff_pow_eq_one.mpr
  exact ⟨n,hn,congrArg (fun k : K=>k.val) he⟩

/-- Every nonidentity real lift fixing an interior point has that same genuine elliptic center. -/
theorem primitive_realSL_elliptic_center_eq
    (B : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hB : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (z : ℍ) (hz : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B).val ((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB)=z := by
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action] at hz
  exact ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_elliptic_fixed_iff B _ z).mp (UpperHalfPlane.ext
    (OnePoint.coe_eq_coe.mp hz))).symm

/-- Every actual elliptic in a normalized Fuchsian group has a genuine primitive canonical dominator. -/
theorem FuchsianDisc.elliptic_exists_primitive_canonical_maximum
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D : FuchsianDisc H)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A))
    (hAH : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A∈D.normalizedGroup) :
    ∃B : Matrix.SpecialLinearGroup (Fin
      2) ℝ,IsPrimitive D.normalizedGroup (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B) ∧
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B) ∧
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
        B).val (((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A
        ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp
        hA)):ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=
        (((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A
          ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp
          hA)):ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∧
      HasMaximalCanonicalRegion D.normalizedGroup B ∧ _root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion A⊆_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion B := by
  let z:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA)
  let p : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex:=((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
  let K:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer D.normalizedGroup p
  let : Finite K:=D.normalized_interior_stabilizer_finite z
  let : IsCyclic K:=D.normalized_stabilizer_isCyclic p
  have hAz : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val p=p := by
    change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val ((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action,(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_elliptic_fixed_iff A _ z).mpr rfl]
  have hAK : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A∈K := (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer _ p _).mpr ⟨hAH,hAz⟩
  have hN : 1 < Nat.card K := by
    have hn : (⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,hAK⟩:K)≠1 := by intro he;exact hA.1 (congrArg Subtype.val he)
    let : Nontrivial K:=⟨⟨_,_,hn⟩⟩
    let : Fintype K:=Fintype.ofFinite _
    simpa only [Nat.card_eq_fintype_card] using (Fintype.one_lt_card : 1 < Fintype.card K)
  obtain ⟨g,hg,hgen,hleast,htrace,q,hmodel⟩ := primitive_finite_cyclic_exists_least_rotation K
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) hAK hA.1
  have hg0 : g≠1 := by
    intro hg1
    have hm : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A∈Subgroup.zpowers g := hgen ▸ hAK
    obtain ⟨n,hn⟩:=Subgroup.mem_zpowers_iff.mp hm
    rw [hg1,one_zpow] at hn
    exact hA.1 hn.symm
  obtain ⟨hgH,hgp⟩ := (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer _ p g).mp hg
  obtain ⟨B,hB⟩:=D.normalizedGroup_exists_realSL g hgH
  have hBE : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B) := hB ▸ primitive_elliptic_of_finite_subgroup K g hg hg0
  have hBz := primitive_realSL_elliptic_center_eq B hBE z (hB ▸ hgp)
  have hpB : IsPrimitive D.normalizedGroup (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B) := by
    apply primitive_of_generating_one_elliptic_stabilizer D.normalizedGroup D.normalized_stabilizer_isCyclic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B) (hB ▸ hgH) hBE p (hB ▸ hgp)
    · simpa only [hB] using hgen
    · exact hB ▸ hleast
  have hBtrace : (Matrix.trace B.val)^2=4*(Real.cos (Real.pi/Nat.card K))^2 := by
    rw [←hB,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_squaredTrace] at htrace
    exact Complex.ofReal_injective htrace
  have hsub (C : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hCK :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C∈K)
      (hC0 : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C≠1) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion C⊆_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion B := by
    have hCE:=primitive_elliptic_of_finite_subgroup K (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      C) hCK hC0
    have hCp:=((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer _ p _).mp hCK).2
    have hCz:=primitive_realSL_elliptic_center_eq C hCE z hCp
    apply hCanonicalRegion_elliptic_subset_of_trace_sq_le C B hCE hBE (hCz.trans hBz.symm)
    rw [hBtrace]
    exact primitive_realSL_trace_bound_of_full_root_model K hN q hmodel C hCK hC0
  refine ⟨B,hpB,hBE,(hB ▸ hgp),?_,hsub A hAK hA.1⟩
  intro w hBw C hCH hCw hC0
  have he : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer D.normalizedGroup w=K :=
    primitive_stabilizers_eq_of_fixed_points D.normalizedGroup D.normalized_stabilizer_isCyclic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B) hpB.mem hBE.1 w p hBw (hB ▸ hgp)
  apply hsub C
  · rw [←he]
    exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer _ w _).mpr ⟨hCH,hCw⟩
  · exact hC0

/-- Inversion preserves the actual primitive elliptic property, including the least unsigned angle. -/
theorem IsPrimitive.elliptic_inverse
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (A : Matrix.SpecialLinearGroup (Fin
      2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (hp : IsPrimitive H
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) :
    IsPrimitive H (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A⁻¹) := by
  have hi : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A⁻¹≠1 := by rw [map_inv];exact inv_ne_one.mpr hA.1
  have hc : IsConj (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
    A) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A⁻¹) :=
    (_root_.LowDimensionalTopology.Geometry.Mobius.mobius_isConj_iff_squaredTrace_eq _ _ hA.1 hi).mpr (by
      rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_squaredTrace,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_squaredTrace,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_trace_inverse])
  have hE := (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusElliptic_isConj hc).mp hA
  apply (primitive_iff_of_elliptic hE).mpr
  refine ⟨?_,?_,(hasLeastEllipticRotation_isConj hc).mp ((primitive_iff_of_elliptic hA).mp hp).2.2⟩
  · rw [map_inv]
    exact H.inv_mem hp.mem
  · intro z hz
    have hzA : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val z=z := by
      have h:=_root_.LowDimensionalTopology.Geometry.Mobius.mobius_inv_fixed hz
      simpa only [←map_inv,inv_inv] using h
    simpa only [map_inv,Subgroup.zpowers_inv] using hp.generates z hzA

/-- Every genuine primitive elliptic has maximal canonical region in the whole normalized group. -/
theorem FuchsianDisc.primitive_elliptic_maximalCanonicalRegion
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D : FuchsianDisc H)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A))
    (hpA : IsPrimitive D.normalizedGroup (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) :
    HasMaximalCanonicalRegion D.normalizedGroup A := by
  obtain ⟨B,hpB,hBE,hzB,hmaxB,_hAB⟩:=D.elliptic_exists_primitive_canonical_maximum A hA hpA.mem
  let z:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA)
  have hzA : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val ((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action,(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_elliptic_fixed_iff A _ z).mpr rfl]
  have hBA:=primitive_realSL_elliptic_center_eq B hBE z hzB
  have hgenA :=hpA.generates ((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) hzA
  have hgenB :=hpB.generates ((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) hzB
  have ho : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)=orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B) := by
    rw [←Nat.card_zpowers,←Nat.card_zpowers,hgenA,hgenB]
  have htr : (Matrix.trace B.val)^2=(Matrix.trace A.val)^2 := by
    apply Complex.ofReal_injective
    rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_squaredTrace,←_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_squaredTrace,
      ((primitive_iff_of_elliptic hA).mp hpA).2.2.squaredTrace_order,
      ((primitive_iff_of_elliptic hBE).mp hpB).2.2.squaredTrace_order,ho]
  have hsub : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion B⊆_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion A :=
    hCanonicalRegion_elliptic_subset_of_trace_sq_le B A hBE hA hBA htr.le
  intro p hAp C hCH hCp hC0
  have he :=primitive_stabilizers_eq_of_fixed_points D.normalizedGroup D.normalized_stabilizer_isCyclic
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      A) hpA.mem hA.1 ((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) p hzA hAp
  have hBp : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B).val p=p := by
    have hm : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B∈_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer D.normalizedGroup ((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) :=
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer _ _ _).mpr ⟨hpB.mem,hzB⟩
    rw [he] at hm
    exact ((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer _ p _).mp hm).2
  exact (hmaxB p hBp C hCH hCp hC0).trans hsub

/-- A normalized elliptic element is primitive exactly when its canonical region is maximal. -/
theorem FuchsianDisc.primitive_elliptic_iff_maximalCanonicalRegion
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D : FuchsianDisc H)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A))
    (hAH : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A∈D.normalizedGroup) :
    IsPrimitive D.normalizedGroup (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) ↔ HasMaximalCanonicalRegion D.normalizedGroup A := by
  constructor
  · exact D.primitive_elliptic_maximalCanonicalRegion A hA
  · intro hmax
    obtain ⟨B,hpB,hBE,hzB,_hmaxB,hAB⟩:=D.elliptic_exists_primitive_canonical_maximum A hA hAH
    let z:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA)
    have hzA : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val ((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
      rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action,(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_elliptic_fixed_iff A _ z).mpr rfl]
    have hBA':=hmax ((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) hzA B hpB.mem hzB hBE.1
    have he :=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion_eq_iff_inverse_pair B A
      hBE.1).mp (le_antisymm hBA' hAB)
    rcases he with he | he
    · rwa [he]
    · have hi:=hpB.elliptic_inverse B hBE
      simpa only [map_inv,←he] using hi

end LowDimensionalTopology.Geometry.Fuchsian
