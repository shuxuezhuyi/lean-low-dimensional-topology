module
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disc.ExtendedCarrier
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Vertex.ParabolicIdealCycles
public import Mathlib.Order.Filter.AtTopBot.Basic
@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Topology Filter
open scoped UpperHalfPlane Complex.UnitDisc Pointwise OnePoint

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- Equal genuine horocyclic regions have the same actual ideal basepoint. -/
theorem realSL_horocyclic_image_eq_endpoint (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (k : ℝ) (hk : 0 < k)
    (he : (fun z : ℍ => A • z) '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.horizontalHorocyclicRegion k =
      (fun z : ℍ => B • z) '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.horizontalHorocyclicRegion k) :
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val ∞ = (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B).val ∞ := by
  have hh := congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTraceIdealEndpoints he
  rw [realSL_horocyclic_region_idealEndpoints A k hk,
    realSL_horocyclic_region_idealEndpoints B k hk] at hh
  exact singleton_injective hh

/-- Genuine discreteness and a unit translation force every infinity-fixing group member
to preserve actual height, rather than merely mapping horocycles to horocycles. -/
theorem discrete_unitTranslation_fix_infty_preserves_height
    (N : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hd :
      _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup N)
    (hT : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1 ∈ N) (A : Matrix.SpecialLinearGroup
      (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A ∈ N) (hi :
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val ∞ = ∞) (z : ℍ) :
    (A • z : ℍ).im = z.im := by
  have hc := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_fixed_infty_iff A).mp hi
  have hden := discrete_unitTranslation_affine_denominator N hd hT A hA hc
  rw [realSL_im_action]
  have he : Complex.normSq (realSLDenominator A z) = 1 := by
    change Complex.normSq ((A 1 0 : ℂ)*(z : ℂ)+(A 1 1 : ℂ)) = 1
    simp only [hc,Complex.ofReal_zero,zero_mul,zero_add,Complex.normSq_ofReal]
    nlinarith [sq_abs (A 1 1)]
  rw [he,div_one]

/-- Unbounded genuine heights imply convergence to the actual sphere point infinity,
without any horizontal-coordinate bound. -/
theorem halfPlane_coe_tendsto_infty_of_height (z : ℕ → ℍ)
    (hz : Tendsto (fun n => (z n).im) atTop atTop) :
    Tendsto (fun n => (((z n : ℍ) : ℂ) : OnePoint ℂ)) atTop (𝓝 (∞ : OnePoint ℂ)) := by
  have hn : Tendsto (fun n => ‖(z n : ℂ)‖) atTop atTop :=
    tendsto_atTop_mono (fun n => Complex.im_le_norm (z n : ℂ)) hz
  have hc : Tendsto (fun n => (z n : ℂ)) atTop (coclosedCompact ℂ) := by
    rw [coclosedCompact_eq_cocompact,←Metric.cobounded_eq_cocompact]
    exact tendsto_norm_atTop_iff_cobounded.mp hn
  exact OnePoint.tendsto_coe_infty.comp hc

/-- A genuine whole-group closed covering and genuine finite horoball incidence give
an actual group translate of infinity in the actual sphere closure. -/
theorem normalized_parabolic_boundary_representative
    (N : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hd :
      _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup N)
    (hT : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1 ∈ N) (S : Set ℍ)
    (hcover : ∀ z : ℍ, ∃ B : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B ∈ N ∧ B • z ∈ closure S)
    (hfinite : {L : Set ℍ | ∃ B : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B ∈ N ∧ L = (fun z : ℍ => B •
        z) '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.horizontalHorocyclicRegion 1 ∧
        (closure S ∩ L).Nonempty}.Finite) :
    ∃ A : Matrix.SpecialLinearGroup (Fin 2) ℝ, _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A ∈ N ∧
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val ∞ ∈ closure ((fun z : ℍ => ((z : ℂ) : OnePoint ℂ)) '' S) := by
  classical
  let u (n : ℕ) := _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 ((n : ℝ)+2) (by positivity)
  choose B hBN hBS using (fun n : ℕ => hcover (u n))
  let L (n : ℕ) := (fun z : ℍ => B n •
    z) '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.horizontalHorocyclicRegion 1
  let F : Set (Set ℍ) := {K | ∃ B : Matrix.SpecialLinearGroup (Fin 2) ℝ,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B ∈ N ∧ K = (fun z : ℍ => B •
      z) '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.horizontalHorocyclicRegion 1 ∧
      (closure S ∩ K).Nonempty}
  have hLF (n : ℕ) : L n ∈ F := by
    refine ⟨B n,hBN n,rfl,B n • u n,hBS n,u n,?_,rfl⟩
    change 1 < (n : ℝ)+2
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hfreq : ∃ᶠ n : ℕ in atTop, ∃ K ∈ F,L n = K :=
    Frequently.of_forall (fun n => ⟨L n,hLF n,rfl⟩)
  obtain ⟨K,hK,hfrequent⟩ := hfinite.frequently_exists.mp hfreq
  obtain ⟨φ,hφ,hconstant⟩ := extraction_of_frequently_atTop hfrequent
  obtain ⟨A,hAN,hAK,_hmeet⟩ := hK
  let v (n : ℕ) : ℍ := A⁻¹ • (B (φ n) • u (φ n))
  have hv (n : ℕ) : (v n).im = (φ n : ℝ)+2 := by
    have he : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      A).val ∞ = (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (B (φ n))).val ∞ :=
      realSL_horocyclic_image_eq_endpoint A (B (φ n)) 1 zero_lt_one
        ((hconstant n).trans hAK).symm
    have hfix : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (A⁻¹*B (φ n))).val ∞ = ∞ := by
      rw [map_mul,map_inv]
      change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
        A).val.symm ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (B (φ n))).val ∞) = ∞
      rw [←he,Equiv.symm_apply_apply]
    have hC : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (A⁻¹*B (φ n)) ∈ N := by
      rw [map_mul,map_inv]
      exact N.mul_mem (N.inv_mem hAN) (hBN (φ n))
    have hh := discrete_unitTranslation_fix_infty_preserves_height N hd hT
      (A⁻¹*B (φ n)) hC hfix (u (φ n))
    simpa only [v,u,mul_smul,_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe,UpperHalfPlane.im,UpperHalfPlane.coe_mk] using hh
  have hlim : Tendsto (fun n => (((v n : ℍ) : ℂ) : OnePoint ℂ)) atTop (𝓝 (∞ : OnePoint ℂ)) := by
    apply halfPlane_coe_tendsto_infty_of_height
    simp_rw [hv]
    have hbase : Tendsto (fun n : ℕ => (φ n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp hφ.tendsto_atTop
    exact tendsto_atTop_mono (fun _ => le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 2)) hbase
  have hAlim := (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryHomeomorph
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)).continuous.continuousAt.tendsto.comp hlim
  have hAlim' : Tendsto (fun n => (((B (φ n) • u (φ n) : ℍ) : ℂ) : OnePoint ℂ))
      atTop (𝓝 ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val ∞)) := by
    convert hAlim using 1
    funext n
    change _ = (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val (((v n : ℍ) : ℂ) : OnePoint ℂ)
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action]
    change (((B (φ n) • u (φ n) : ℍ) : ℂ) : OnePoint ℂ) =
      (((A • (A⁻¹ • (B (φ n) • u (φ n))) : ℍ) : ℂ) : OnePoint ℂ)
    rw [smul_inv_smul]
    rfl
  refine ⟨A,hAN,?_⟩
  apply isClosed_closure.mem_of_tendsto hAlim'
  apply Filter.Eventually.of_forall
  intro n
  exact image_closure_subset_closure_image
    (OnePoint.continuous_coe.comp UpperHalfPlane.continuous_coe)
      ⟨B (φ n) • u (φ n),hBS (φ n),rfl⟩

/--
Every actual parabolic fixed-point orbit meets the actual ambient
closure of every genuine locally finite fundamental domain.
-/
theorem IsLocallyFiniteFuchsianDomain.parabolic_fixedPoint_orbit_mem_closure
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H} {D :
      Set P.domain.carrier}
    (hD : IsLocallyFiniteFuchsianDomain P D) (f : H) (hf : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic
      f.val)
    (ξ : OnePoint ℂ) (hfix : f.val.val ξ = ξ) :
    ∃ g : H, g.val.val ξ ∈ closure ((Subtype.val : P.domain.carrier → OnePoint ℂ) '' D) := by
  obtain ⟨q,hq,hT,hqξ⟩ := parabolic_unit_halfPlane_normalizer P f hf ξ hfix
  obtain ⟨A,hA⟩ := halfPlane_chart_real_lift q hq
  let N := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H
  let F := fordSLNativeHom A
  let ψ : P.domain.carrier ≃ₜ ℍ := P.halfPlaneCoordinate.trans F.toHomeomorph
  let S := F '' (P.halfPlaneCoordinate '' D)
  have hS : S = ψ '' D := by
    change F '' (P.halfPlaneCoordinate '' D) = ψ '' D
    rw [image_image]
    rfl
  have hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup N := by
    let : DiscreteTopology H := P.discrete
    exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.MatrixGroups.conjugateSubgroup_discrete q H
  have hcover (z : ℍ) : ∃ B : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B ∈ N ∧ B • z ∈ closure S := by
    let x := ψ.symm z
    have hx : x ∈ (⋃ g : H,(fun y : P.domain.carrier => g • y) '' closure D) := by
      rw [hD.fundamental.closure_cover]
      trivial
    obtain ⟨g,w,hw,hgw⟩ := mem_iUnion.mp hx
    have hpres : (q*(g⁻¹).val*q⁻¹).val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet = _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet := by
      rw [←hq,_root_.LowDimensionalTopology.Geometry.Surfaces.cusp_conjugate_image,P.image_eq g⁻¹]
    obtain ⟨B,hB⟩ := mobius_preserves_halfPlane_exists_SL _ hpres
    have hBN : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B ∈ N :=
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q H
        _).mpr ⟨(g⁻¹).val,(g⁻¹).property,hB.symm⟩
    have hconj := halfPlane_chart_action_conjugate P q A hA g⁻¹ B hB
    have hBz : B • z = ψ w := by
      have he := congrArg (fun e : ℍ ≃ᵢ ℍ => e z) hconj
      change B • z = F (P.halfPlaneAction g⁻¹ (F.symm z)) at he
      rw [he,P.halfPlaneAction_apply]
      change F (P.halfPlaneCoordinate (g⁻¹ • x)) = F (P.halfPlaneCoordinate w)
      rw [←hgw,inv_smul_smul]
    refine ⟨B,hBN,?_⟩
    rw [hBz,hS,←ψ.image_closure D]
    exact ⟨w,hw,rfl⟩
  have hfinite : {L : Set ℍ | ∃ B : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B ∈ N ∧ L = (fun z : ℍ => B •
        z) '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.horizontalHorocyclicRegion 1 ∧
        (closure S ∩ L).Nonempty}.Finite := by
    apply (hD.normalized_horocyclic_images_finite q hq A hA hT 1 zero_lt_one).subset
    rintro L ⟨B,hBN,rfl,hmeet⟩
    refine ⟨⟨fordSLNativeHom B,(mem_fordNativeGroup N _).mpr ⟨B,hBN,rfl⟩⟩,rfl,hmeet⟩
  obtain ⟨B,hBN,hBcl⟩ := normalized_parabolic_boundary_representative N hd hT S hcover hfinite
  obtain ⟨g,hg,hgB⟩ := (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q
    H _).mp hBN
  let gH : H := ⟨g,hg⟩
  have hpoint : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B).val ∞ = q.val (g.val ξ) := by
    rw [←hgB]
    change q.val (g.val (q.val.symm ∞)) = q.val (g.val ξ)
    rw [←hqξ,Equiv.symm_apply_apply]
  have him : (fun z : ℍ => ((z : ℂ) : OnePoint ℂ)) '' S =
      (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryHomeomorph q) '' ((Subtype.val : P.domain.carrier → OnePoint ℂ) '' D) := by
    apply Set.Subset.antisymm
    · rintro _ ⟨_,⟨_,⟨x,hx,rfl⟩,rfl⟩,rfl⟩
      exact ⟨x.val,⟨x,hx,rfl⟩,halfPlane_chart_coordinate_extended P q A hA x⟩
    · rintro _ ⟨_,⟨x,hx,rfl⟩,rfl⟩
      exact ⟨F (P.halfPlaneCoordinate x),⟨P.halfPlaneCoordinate x,⟨x,hx,rfl⟩,rfl⟩,
        (halfPlane_chart_coordinate_extended P q A hA x).symm⟩
  rw [him,←(_root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryHomeomorph q).image_closure] at hBcl
  obtain ⟨ζ,hζ,hζB⟩ := hBcl
  have he : ζ = g.val ξ := q.val.injective (hζB.trans hpoint)
  exact ⟨gH,he ▸ hζ⟩

/-- The original Euclidean-closure conclusion, in the actual finite unit-disc coordinate.
The representative lies in the literal ideal boundary, not merely a model compactification. -/
theorem IsLocallyFiniteFuchsianDomain.parabolic_fixedPoint_orbit_mem_idealBoundary
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H} {D :
      Set P.domain.carrier}
    (hD : IsLocallyFiniteFuchsianDomain P D) (f : H) (hf : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic
      f.val)
    (ξ : OnePoint ℂ) (hfix : f.val.val ξ = ξ) :
    ∃ (g : H) (η : ℂ), g.val.val ξ = (η : OnePoint ℂ) ∧ η ∈ fuchsianPolygonIdealBoundary P D := by
  obtain ⟨g,hcl⟩ := hD.parabolic_fixedPoint_orbit_mem_closure f hf ξ hfix
  let f' : H := g*f*g⁻¹
  have hpar : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f'.val :=
    (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusParabolic_isConj (isConj_iff.mpr ⟨g.val,rfl⟩)).mp hf
  have hfix' : f'.val.val (g.val.val ξ) = g.val.val ξ := by
    change g.val.val (f.val.val (g.val.val.symm (g.val.val ξ))) = g.val.val ξ
    rw [Equiv.symm_apply_apply,hfix]
  have hfront := _root_.LowDimensionalTopology.Geometry.Mobius.mobiusParabolic_fixed_mem_disc_frontier f'.val hpar
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.extendedUnitDisc_isComplexOpenDisc (P.image_eq f') hfix'
  have hex (p : OnePoint ℂ) (hp : p ∈ frontier _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc) :
      ∃ η : ℂ, (η : OnePoint ℂ) = p ∧ ‖η‖ = 1 := by
    induction p using OnePoint.rec with
    | infty => exact False.elim (_root_.LowDimensionalTopology.Geometry.Mobius.complexCircle_infty 0 1
      (_root_.LowDimensionalTopology.Geometry.Mobius.frontier_extendedUnitDisc_eq_circle ▸ hp))
    | coe η =>
      refine ⟨η,rfl,?_⟩
      simpa only [_root_.LowDimensionalTopology.Geometry.Mobius.frontier_extendedUnitDisc_eq_circle,_root_.LowDimensionalTopology.Geometry.Mobius.complexCircle_coe,sub_zero] using hp
  obtain ⟨η,hη,hn⟩ := hex (g.val.val ξ) hfront
  refine ⟨g,η,hη.symm,(mem_fuchsianPolygonIdealBoundary_iff_extendedClosure P D η).mpr ⟨hn,?_⟩⟩
  rwa [hη]

/-- Every actual parabolic fixed-point orbit has a nonempty genuine ideal-boundary cycle
in any original locally finite fundamental domain. -/
theorem IsLocallyFiniteFuchsianDomain.parabolic_idealCycle_nonempty
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H} {D :
      Set P.domain.carrier}
    (hD : IsLocallyFiniteFuchsianDomain P D) (f : H) (hf : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic
      f.val)
    (ξ : OnePoint ℂ) (hfix : f.val.val ξ = ξ) :
    (fuchsianPolygonIdealCycle P D ξ).Nonempty := by
  obtain ⟨g,η,hg,hη⟩ := hD.parabolic_fixedPoint_orbit_mem_idealBoundary f hf ξ hfix
  exact ⟨(η : OnePoint ℂ),⟨η,hη,rfl⟩,MulAction.mem_orbit_iff.mpr ⟨g,hg⟩⟩

end LowDimensionalTopology.Geometry.Fuchsian
