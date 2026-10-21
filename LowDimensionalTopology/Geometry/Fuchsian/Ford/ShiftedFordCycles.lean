/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.NativeFuchsianPolygons
public import LowDimensionalTopology.Geometry.Fuchsian.CanonicalRegion.PrimitiveCanonicalTransport
public import LowDimensionalTopology.Geometry.Fuchsian.Ford.HorocyclicFordCycles
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped Topology OnePoint Pointwise UpperHalfPlane Complex.UnitDisc BigOperators
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Auxiliary.Analysis

/-- Native horizontal translations preserve the original height exactly. -/
theorem fordTranslation_im (t : ℝ) (z : ℍ) : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t•z).im=z.im := by
  change ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t•z:ℍ):ℂ).im=z.im
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL_coe]
  simp

/-- Its real coordinate changes by the literal chosen amount. -/
theorem fordTranslation_re (t : ℝ) (z : ℍ) : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t•z).re=z.re+t := by
  change ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t•z:ℍ):ℂ).re=z.re+t
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL_coe]
  simp

/-- The translated whole group is defined by actual Mobius conjugation. -/
def fordTranslatedGroup (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (t :
  ℝ) : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup:=
  _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t)) H

/-- Membership in the translated whole lift is exact matrix conjugation. -/
theorem fordTranslatedGroup_lift_mem (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (t
  : ℝ)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A∈fordTranslatedGroup H t ↔
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t)⁻¹*A*_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t)∈H := by
  let T:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t
  let q:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius T
  constructor
  · intro hA
    obtain ⟨g,hg,he⟩:=(_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q
      H _).mp hA
    have hh : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (T⁻¹*A*T)=g:=by
      rw [map_mul,map_mul,map_inv]
      change q⁻¹*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A*q=g
      rw [←he]
      group
    rwa [hh]
  · intro hA
    apply (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q H _).mpr
    refine ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (T⁻¹*A*T),hA,?_⟩
    rw [map_mul,map_mul,map_inv]
    change q*(q⁻¹*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      A*q)*q⁻¹=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A
    group

/-- The original common Ford exterior is carried onto the exact common
Ford exterior of the translated original group. -/
theorem fordTranslatedGroup_exterior (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (t
  : ℝ) (z : ℍ) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t•z∈_root_.LowDimensionalTopology.Geometry.Fuchsian.mobiusFordExterior (fordTranslatedGroup H t) ↔
      z∈_root_.LowDimensionalTopology.Geometry.Fuchsian.mobiusFordExterior H := by
  let T:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t
  constructor
  · intro hz A
    let B:=T*A.val*T⁻¹
    have hB : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B∈fordTranslatedGroup H t:=by
      apply (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff _ H _).mpr
      refine ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A.val,A.property,?_⟩
      simp only [B,T,map_mul,map_inv]
    have hh:=_root_.LowDimensionalTopology.Geometry.Fuchsian.realSL_im_le_of_denominator B (T•z) (hz ⟨B,hB⟩)
    have hact : B•(T•z)=T•(A.val•z):=by
      simp only [B,mul_smul,inv_smul_smul]
    rw [hact,fordTranslation_im,fordTranslation_im] at hh
    exact (parabolicFord_im_le_iff_denominator A.val z).mp hh
  · intro hz A
    let B:=T⁻¹*A.val*T
    have hB : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B∈H:=(fordTranslatedGroup_lift_mem H t
      A.val).mp A.property
    have hh:=_root_.LowDimensionalTopology.Geometry.Fuchsian.realSL_im_le_of_denominator B z (hz ⟨B,hB⟩)
    have hact : T•(B•z)=A.val•(T•z):=by
      simp only [B,mul_smul,smul_inv_smul]
    have hh' : (A.val•(T•z)).im≤(T•z).im:=by
      rw [←hact,fordTranslation_im,fordTranslation_im]
      exact hh
    exact (parabolicFord_im_le_iff_denominator A.val (T•z)).mp hh'
/-- The translated exterior is the exact homeomorphic image of the
original exterior, including its genuine boundary circles. -/
theorem fordTranslatedGroup_exterior_image (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (t : ℝ) :
    (Homeomorph.smul (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL
      t)) '' _root_.LowDimensionalTopology.Geometry.Fuchsian.mobiusFordExterior H=
      _root_.LowDimensionalTopology.Geometry.Fuchsian.mobiusFordExterior (fordTranslatedGroup H t) := by
  ext u
  constructor
  · rintro ⟨z,hz,rfl⟩
    exact (fordTranslatedGroup_exterior H t z).mpr hz
  · intro hu
    refine ⟨(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t)⁻¹•u,?_,?_⟩
    · apply (fordTranslatedGroup_exterior H t _).mp
      simpa only [smul_inv_smul] using hu
    · change _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t•((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t)⁻¹•u)=u
      exact smul_inv_smul _ _

/-- A horizontal translation takes the literal width-one Ford strip to
the literal translated strip of the translated original group. -/
theorem fordTranslatedGroup_domain_mem (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (t x₀ : ℝ) (z : ℍ) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t•z∈_root_.LowDimensionalTopology.Geometry.Fuchsian.mobiusFordDomain (fordTranslatedGroup H t) (x₀+t) ↔
      z∈_root_.LowDimensionalTopology.Geometry.Fuchsian.mobiusFordDomain H x₀ := by
  let F : ℍ≃ₜℍ:=Homeomorph.smul (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t)
  have hi : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t•z∈interior (_root_.LowDimensionalTopology.Geometry.Fuchsian.mobiusFordExterior (fordTranslatedGroup H t)) ↔
      z∈interior (_root_.LowDimensionalTopology.Geometry.Fuchsian.mobiusFordExterior H):=by
    rw [←fordTranslatedGroup_exterior_image H t,←F.image_interior]
    exact F.injective.mem_set_image
  change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t•z∈interior
    (_root_.LowDimensionalTopology.Geometry.Fuchsian.mobiusFordExterior (fordTranslatedGroup H t)) ∧
    x₀+t<(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL
      t•z).re ∧ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t•z).re<x₀+t+1) ↔
    (z∈interior (_root_.LowDimensionalTopology.Geometry.Fuchsian.mobiusFordExterior H) ∧ x₀<z.re ∧ z.re<x₀+1)
  rw [hi,fordTranslation_re]
  constructor <;> rintro ⟨he,hl,hr⟩ <;> exact ⟨he,by linarith only [hl],by linarith only [hr]⟩

/-- The literal original Ford domains are related by the actual native homeomorphism. -/
theorem fordTranslatedGroup_domain_image (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (t x₀ : ℝ) :
    (Homeomorph.smul (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL
      t)) '' _root_.LowDimensionalTopology.Geometry.Fuchsian.mobiusFordDomain H x₀=
      _root_.LowDimensionalTopology.Geometry.Fuchsian.mobiusFordDomain (fordTranslatedGroup H t) (x₀+t) := by
  ext u
  constructor
  · rintro ⟨z,hz,rfl⟩
    exact (fordTranslatedGroup_domain_mem H t x₀ z).mpr hz
  · intro hu
    refine ⟨(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t)⁻¹•u,?_,?_⟩
    · apply (fordTranslatedGroup_domain_mem H t x₀ _).mp
      simpa only [smul_inv_smul] using hu
    · change _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t•((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t)⁻¹•u)=u
      exact smul_inv_smul _ _

/-- The same actual correspondence holds for the closed original domains. -/
theorem fordTranslatedGroup_closure_mem (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (t x₀ : ℝ) (z : ℍ) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t•z∈closure (_root_.LowDimensionalTopology.Geometry.Fuchsian.mobiusFordDomain (fordTranslatedGroup H t) (x₀+t)) ↔
      z∈closure (_root_.LowDimensionalTopology.Geometry.Fuchsian.mobiusFordDomain H x₀) := by
  let F : ℍ≃ₜℍ:=Homeomorph.smul (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t)
  rw [←fordTranslatedGroup_domain_image H t x₀,←F.image_closure]
  exact F.injective.mem_set_image

/-- All horizontal translation lifts commute as actual determinant-one matrices. -/
theorem fordTranslation_commute (s t : ℝ) : Commute (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL s) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t) := by
  change hTranslationSLHom (Multiplicative.ofAdd s)*hTranslationSLHom (Multiplicative.ofAdd t)=
    hTranslationSLHom (Multiplicative.ofAdd t)*hTranslationSLHom (Multiplicative.ofAdd s)
  rw [←hTranslationSLHom.map_mul,←hTranslationSLHom.map_mul,mul_comm]


/-- The actual unit parabolic stays primitive in the whole translated group. -/
theorem fordTranslatedGroup_primitive (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (t
  : ℝ)
    (hp : IsPrimitive H (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1)) :
    IsPrimitive (fordTranslatedGroup H t) (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1) := by
  let T:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t
  let q:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius T
  have hc : q*_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1*q⁻¹=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1:=by
    rw [←_root_.LowDimensionalTopology.Geometry.Fuchsian.realSLMobius_unitTranslation,←map_inv,←map_mul,←map_mul]
    congr 1
    dsimp only [T]
    rw [(fordTranslation_commute t 1).eq]
    group
  have hh:=(isPrimitive_conjugation_iff H (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1)
    q).mpr hp
  rwa [hc] at hh

/-- Horizontal conjugation preserves the actual original Fuchsian data. -/
theorem fordTranslatedData {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (t : ℝ) : HalfPlaneFuchsianGroup (fordTranslatedGroup H t) where
  preserves g:=by
    let T:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t
    let q:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius T
    obtain ⟨f,hf,he⟩:=(_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q
      H g.val).mp g.property
    have hq : q.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet:=realSLMobius_image_openHalfPlane T
    have hqi : q⁻¹.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet:=by
      change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius T)⁻¹.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet
      rw [←map_inv]
      exact realSLMobius_image_openHalfPlane T⁻¹
    rw [←he]
    change (fun x=>q.val (f.val (q⁻¹.val x))) '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet
    calc
      _=q.val '' (f.val '' (q⁻¹.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet)):=by
        rw [image_image,image_image]
      _=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet:=by rw [hqi,P.preserves ⟨f,hf⟩,hq]
  discrete:=by
    let fordTranslatedOriginalDiscrete : DiscreteTopology H:=P.discrete
    exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.MatrixGroups.conjugateSubgroup_discrete (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t)) H

/-- Horizontal conjugation transports the original actual sphere orbit
in both directions, using the whole original group. -/
theorem fordTranslatedGroup_orbit (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (t :
  ℝ) (z w : ℍ) :
    (((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL
      t•w:ℍ):ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈
      MulAction.orbit (fordTranslatedGroup H t) (((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL
        t•z:ℍ):ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ↔
      ((w:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈MulAction.orbit H ((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
  let q:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t)
  have hq (u : ℍ) : (((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t•u:ℍ):ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=q.val ((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex):=
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t) u).symm
  rw [hq w,hq z]
  constructor
  · rintro ⟨g,hg⟩
    obtain ⟨f,hf,hfg⟩:=(_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q
      H g.val).mp g.property
    refine ⟨⟨f,hf⟩,q.val.injective ?_⟩
    change g.val.val (q.val ((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex))=q.val ((w:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) at hg
    rw [←hfg] at hg
    change q•(f•((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex))=q•((w:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    change (q*f*q⁻¹)•(q•((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex))=q•((w:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) at hg
    simpa only [mul_smul,inv_smul_smul] using hg
  · rintro ⟨g,hg⟩
    refine ⟨⟨q*g.val*q⁻¹,(_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff
      q H _).mpr ⟨g.val,g.property,rfl⟩⟩,?_⟩
    change (q*g.val*q⁻¹)•(q•((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex))=q•((w:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    simp only [mul_smul,inv_smul_smul]
    exact congrArg q.val hg

/-- The literal original closed-strip cycle is preserved by the actual
horizontal translation and simultaneous whole-group conjugation. -/
theorem fordTranslatedGroup_cycle_mem (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (t x₀ : ℝ) (z w : ℍ) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t•w∈_root_.LowDimensionalTopology.Geometry.Fuchsian.mobiusFordVertexCycle (fordTranslatedGroup H t) (x₀+t)
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t•z) ↔ w∈_root_.LowDimensionalTopology.Geometry.Fuchsian.mobiusFordVertexCycle H x₀ z := by
  exact and_congr (fordTranslatedGroup_closure_mem H t x₀ w) (fordTranslatedGroup_orbit H t z w)

/-- Exact actual finite-cycle image, without changing which group orbit is used. -/
theorem fordTranslatedGroup_cycle_image (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (t x₀ : ℝ) (z : ℍ) :
    (Homeomorph.smul (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL
      t)) '' _root_.LowDimensionalTopology.Geometry.Fuchsian.mobiusFordVertexCycle H x₀ z=
      _root_.LowDimensionalTopology.Geometry.Fuchsian.mobiusFordVertexCycle (fordTranslatedGroup H t) (x₀+t) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t•z) := by
  ext w
  constructor
  · rintro ⟨u,hu,rfl⟩
    exact (fordTranslatedGroup_cycle_mem H t x₀ z u).mpr hu
  · intro hw
    refine ⟨(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t)⁻¹•w,?_,?_⟩
    · apply (fordTranslatedGroup_cycle_mem H t x₀ z _).mp
      simpa only [smul_inv_smul] using hw
    · change _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t•((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t)⁻¹•w)=w
      exact smul_inv_smul _ _

/-- The actual one-period cycle cardinal is unchanged by the actual conjugacy. -/
theorem fordTranslatedGroup_cycle_ncard (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (t x₀ : ℝ) (z : ℍ) :
    (_root_.LowDimensionalTopology.Geometry.Fuchsian.mobiusFordVertexCycle (fordTranslatedGroup H t) (x₀+t)
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t•z)).ncard=
      (_root_.LowDimensionalTopology.Geometry.Fuchsian.mobiusFordVertexCycle H x₀ z).ncard := by
  rw [←fordTranslatedGroup_cycle_image]
  exact Set.ncard_image_of_injective _ (Homeomorph.smul
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t)).injective

/-- The actual original point-stabilizer order is preserved under the same
horizontal whole-group conjugacy. -/
theorem fordTranslatedGroup_pointOrder (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (t : ℝ) (z : ℍ) :
    fordPointOrder (fordTranslatedGroup H t) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t•z)=fordPointOrder H z := by
  unfold fordPointOrder
  change Nat.card (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer
    (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t)) H)
    (((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL
      t•z:ℍ):ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex))=_
  rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action,primitive_boundaryStabilizer_conjugation]
  exact (Nat.card_congr
    (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t))
    (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H
      ((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex))).toEquiv).symm

/-- The real, finite-tangent part of the source height inequality holds for
the actual original group and its actual arbitrarily positioned unit strip.
Every geometric and cycle-angle premise is derived, rather than supplied. -/
theorem parabolicFord_shifted_cycle_height_bound {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (hp : IsPrimitive H
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1)) (x₀ : ℝ) (z : ℍ)
    (hz : z∈closure (_root_.LowDimensionalTopology.Geometry.Fuchsian.mobiusFordDomain H x₀)) (hre : z.re=x₀)
    (hqn : 2<fordPointOrder H z*((_root_.LowDimensionalTopology.Geometry.Fuchsian.mobiusFordVertexCycle H x₀
      z).ncard-1)) :
    z.im≤cycleHeightBound (fordPointOrder H z) ((_root_.LowDimensionalTopology.Geometry.Fuchsian.mobiusFordVertexCycle H x₀ z).ncard-1) := by
  let Q:=fordTranslatedData P (-x₀)
  let w:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (-x₀)•z
  have hprim:=fordTranslatedGroup_primitive H (-x₀) hp
  have hwe : w.re=0:=by
    rw [fordTranslation_re,hre,add_neg_cancel]
  have hw : w∈closure (parabolicFordDomain (fordTranslatedGroup H (-x₀))):=by
    rw [parabolicFordDomain_eq_mobiusFordDomain]
    have hh:=(fordTranslatedGroup_closure_mem H (-x₀) x₀ z).mpr hz
    simpa only [add_neg_cancel] using hh
  have hc : (_root_.LowDimensionalTopology.Geometry.Fuchsian.mobiusFordVertexCycle (fordTranslatedGroup H (-x₀)) 0
    w).ncard=
      (_root_.LowDimensionalTopology.Geometry.Fuchsian.mobiusFordVertexCycle H x₀ z).ncard:=by
    simpa only [add_neg_cancel] using fordTranslatedGroup_cycle_ncard H (-x₀) x₀ z
  have ho : fordPointOrder (fordTranslatedGroup H (-x₀)) w=fordPointOrder H z:=
    fordTranslatedGroup_pointOrder H (-x₀) z
  have hqn' : 2<fordPointOrder (fordTranslatedGroup H (-x₀)) w*
      ((_root_.LowDimensionalTopology.Geometry.Fuchsian.mobiusFordVertexCycle (fordTranslatedGroup H (-x₀)) 0 w).ncard-1):=by
    rwa [ho,hc]
  have hh:=parabolicFord_original_cycle_height_bound Q hprim w hw hwe hqn'
  rw [ho,hc] at hh
  simpa only [w,fordTranslation_im] using hh

end LowDimensionalTopology.Geometry.Fuchsian
