/- Actual non-elementarity in the realization for, 2026-10-20. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.Realization.GeneralSignatureTargetMobius
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.Realization.GeneralSignatureBoundaryLabels
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.Realization.GeneralSignatureBoundaryTranslation
public import LowDimensionalTopology.Geometry.Fuchsian.Covolume.FiniteAreaFirstKind
public import LowDimensionalTopology.Geometry.Fuchsian.Ford.FordOrdinaryAdapters
public import LowDimensionalTopology.Geometry.Fuchsian.Axis.SimpleDilationPrimitiveRoot
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped UpperHalfPlane Topology OnePoint Pointwise MatrixGroups
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- A genuine finite-area original fundamental domain forces non-elementarity.
This is consumed below by the actual auxiliary polygon, without assigning
that auxiliary signature to the retained subgroup. -/
theorem generalSignature_finite_native_area_nonElementary
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H)
    (F : Set ℍ) :
    letI := P.nativeAction
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain H ℍ volume F → volume F ≠ ⊤ → _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary H := by
  let actualNativeAction := P.nativeAction
  intro hF harea hE
  let actualCountable : Countable H := _root_.LowDimensionalTopology.Geometry.Mobius.discreteMobius_countable H P.discrete
  let bad : Set ℝ := ⋃ g : {g : H // g ≠ 1},
    {r : ℝ | g.val.val.val ((r : ℂ) : Mobius.ExtendedComplex) = ((r : ℂ) : Mobius.ExtendedComplex)}
  have hcount : bad.Countable := by
    apply Set.countable_iUnion
    intro g
    have hgn : g.val.val ≠ 1 := fun he => g.property (Subtype.ext he)
    exact (mobius_boundary_fixed_finite g.val.val hgn).countable.preimage
      (OnePoint.coe_injective.comp Complex.ofReal_injective)
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p ∉ bad := by
    by_contra hn
    push Not at hn
    have he : bad = univ := Set.eq_univ_iff_forall.mpr hn
    exact not_countable_univ (he ▸ hcount)
  have hfree : ∀ g : H, g • ((p : ℂ) : Mobius.ExtendedComplex) = ((p : ℂ) : Mobius.ExtendedComplex) → g = 1 := by
    intro g hfix
    by_contra hg
    exact hp (mem_iUnion.mpr ⟨⟨g, hg⟩, hfix⟩)
  obtain ⟨U, hU, hpU, hsep⟩ :=
    separatingMobiusNeighborhood_of_elementary H P.discrete hE _ hfree
  exact native_finite_area_no_boundary_wandering P hF harea U hU hsep p hpU

/-- The actual dilation normal form supplies the original matrix and its
actual complete cut axis; hyperbolicity is derived from positive translation. -/
theorem generalSignature_translation_matrix_axis
    (f : ℍ ≃ᵢ ℍ)
    (K : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine)
    (q : Matrix.SpecialLinearGroup (Fin 2) ℝ) (l : ℝ) (hl : 0 < l)
    (hK : K.realGLMap (Matrix.SpecialLinearGroup.mapGL ℝ q) = _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0)
    (htrans : ∀ z : ℍ, q • f z = signatureBoundaryShift l (q • z)) :
    ∃ A : Matrix.SpecialLinearGroup (Fin 2) ℝ, _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A = f ∧
      ∃ hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A ≠ 1, ∃ htA : 4 < (Matrix.trace A.val)^2,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA = K := by
  let D := _root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL (Real.exp l) (Real.exp_pos l)
  let A := q⁻¹ * D * q
  have hAact : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A = f := by
    apply IsometryEquiv.ext
    intro z
    apply (MulAction.injective q)
    change q • (A • z) = q • f z
    rw [htrans]
    dsimp only [A]
    simp only [mul_smul, smul_inv_smul]
    rfl
  have hC : q * A * q⁻¹ = D := by dsimp only [A]; group
  have hD : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius D = _root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l := realSLMobius_verticalDilation _ _
  have hAhyp : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) := by
    have hh := _root_.LowDimensionalTopology.Geometry.Mobius.mobiusHyperbolic_conjugation_forward (_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q)⁻¹
      (_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation_hyperbolic l hl)
    simpa only [A, map_mul, map_inv, hD, inv_inv] using hh
  have hAn : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A ≠ 1 := hAhyp.1.1
  have htA : 4 < (Matrix.trace A.val)^2 := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff A hAn).mp hAhyp
  refine ⟨A, hAact, hAn, htA, ?_⟩
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.realGLMap_injective (Matrix.SpecialLinearGroup.mapGL ℝ q)
  change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hAn htA).realGLMap _ = K.realGLMap _
  rw [hK, ← _root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis_conjugation A q hAn htA]
  apply dilation_hyperbolic_axis_eq_vertical _ _ _ l
  rw [hC, hD]

/-- The actual real-SL action preserves a complete native line exactly when
its genuine boundary action preserves that line's actual ideal endpoints. -/
theorem generalSignature_SL_line_invariance (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (L : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) :
    ((A • · : ℍ → ℍ) '' L.carrier = L.carrier) ↔
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val '' L.idealEndpoints = L.idealEndpoints := by
  let a := Matrix.SpecialLinearGroup.mapGL ℝ A
  have hpos : 0 < a.val.det := by change 0 < A.val.det; rw [A.det_coe]; norm_num
  have hends := L.idealEndpoints_realGL_image (L.realGLMap a) a hpos
    (L.realGLMap_carrier a).symm
  have hfrac : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val = _root_.LowDimensionalTopology.Geometry.Mobius.fractionalLinear (_root_.LowDimensionalTopology.Geometry.Hyperbolic.complexifiedRealMobiusMatrix a) := by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius, MonoidHom.comp_apply,
      _root_.LowDimensionalTopology.Geometry.Mobius.invariantDisc_specialLinear_action,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_matrix]
  rw [← hfrac] at hends
  constructor
  · intro hline
    have he : L.realGLMap a = L := _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.carrier_injective
      ((L.realGLMap_carrier a).trans hline)
    rw [he] at hends
    exact hends.symm
  · intro he
    have hline : L.realGLMap a = L := _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.idealEndpoints_injective (hends.trans he)
    change (fun z : ℍ => a • z) '' L.carrier = L.carrier
    rw [← L.realGLMap_carrier a, hline]

/-- An actual self-paired side preserves its genuine complete support
line. Two distinct native side points determine that line even for ideal polygons. -/
theorem generalSignature_self_pairing_support {n : ℕ} (θ : Fin n → ℝ) (d : ℝ)
    (hθ : ∀ i, θ i ∈ Ico (0 : ℝ) Real.pi) (hd : 0 < d)
    (hb : _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d = Real.pi) (i : Fin n)
    (hnext : θ i = θ (finRotate n i)) :
    let Q := _root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
    cofiniteTangentPairingElement θ d hθ hd hb i i '' (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q i).carrier =
      (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q i).carrier := by
  let Q := _root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
  let f := cofiniteTangentPairingElement θ d hθ hd hb i i
  let L := _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q i
  obtain ⟨A, hA⟩ := cofiniteTangentPairingElement_conformal θ d hθ hd hb i i
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A = f at hA
  have hside : f '' _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide Q i = _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide Q i :=
    cofiniteTangentPairingElement_side_image θ d hθ hd hb i i hnext hnext.symm
  obtain ⟨u, hu, v, hv, huv⟩ := _root_.LowDimensionalTopology.Geometry.Polygon.nativeCompactifiedSide_nontrivial
    (Q.vertices i) (Q.vertices (finRotate n i))
    (Q.vertices_injective.ne (Q.next_ne_self i).symm)
  have huL : u ∈ L.carrier := _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide_subset_line Q i hu
  have hvL : v ∈ L.carrier := _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide_subset_line Q i hv
  have hfu : f u ∈ L.carrier := _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide_subset_line Q i
    (hside ▸ mem_image_of_mem f hu)
  have hfv : f v ∈ L.carrier := _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide_subset_line Q i
    (hside ▸ mem_image_of_mem f hv)
  have he : L.realGLMap (Matrix.SpecialLinearGroup.mapGL ℝ A) = L := by
    apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.eq_of_two_points _ _ (f.injective.ne huv)
    · rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.realGLMap_carrier]
      exact ⟨u, huL, congrArg (fun e : ℍ ≃ᵢ ℍ => e u) hA⟩
    · rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.realGLMap_carrier]
      exact ⟨v, hvL, congrArg (fun e : ℍ ≃ᵢ ℍ => e v) hA⟩
    · exact hfu
    · exact hfv
  change f '' L.carrier = L.carrier
  rw [← hA]
  exact (L.realGLMap_carrier _).symm.trans (congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.carrier he)

section ActualGroups
variable (g : ℕ) (orders : List ℕ) (s t : ℕ)
    (ho : ∀ m ∈ orders, 2 ≤ m) (hdef : 0 < generalCoreDeficit g orders s t)
    (d : ℝ) (hd : 0 < d) (hb : _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance (generalCoreTheta g orders s t) d = Real.pi)
local notation "θ₀" => generalCoreTheta g orders s t
local notation "hθ₀" => generalCoreTheta_mem g orders s t ho hdef
local notation "ρ₀" => generalCoreAuxPairing g orders s t
local notation "hρ₀" => generalCoreAuxPairing_involutive g orders s t
local notation "hθρ₀" => generalCoreAuxPairing_angle_profile g orders s t
local notation "hp₀" => generalCoreAux_positive_angular_periods g orders s t ho hdef
local notation "Γ₀" => cofiniteMixedTangentialMobiusGroup θ₀ d hθ₀ hd hb ρ₀ hρ₀ hθρ₀
local notation "PΓ₀" => cofiniteMixedTangentialHalfPlaneData θ₀ d hθ₀ hd hb ρ₀ hρ₀ hθρ₀ hp₀
local notation "Q₀" => _root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ₀ d hθ₀ hd hb
local notation "S₀" => generalCoreAuxSidePairing g orders s t ho hdef d hd hb
local notation "H₀" => generalCoreTargetGroup g orders s t ho hdef d hd hb
local notation "G₀" => generalCoreTargetMobiusGroup g orders s t ho hdef d hd hb
local notation "PG₀" => generalCoreTargetMobiusData g orders s t ho hdef d hd hb

/-- The actual auxiliary cofinite group is non-elementary, from the actual
polygon's finite physical area and genuine original-group fundamental domain. -/
theorem generalCoreAuxMobius_nonElementary : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary Γ₀ := by
  let F := _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc ⁻¹' (Q₀).interior
  have ha : volume F ≠ ⊤ := by
    have he : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane '' (Q₀).interior = F := _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.symm.toEquiv.image_eq_preimage_symm _
    have hq := (Q₀).area_lt_top
    rw [_root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon.area, _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicArea_eq_halfPlane_volume _ (Q₀).interior_measurable, he] at hq
    exact ne_of_lt hq
  apply generalSignature_finite_native_area_nonElementary PΓ₀ F
  · exact cofiniteMixedTangential_projective_native_fundamental θ₀ d hθ₀ hd hb ρ₀ hρ₀ hθρ₀ hp₀
  · exact ha

/-- Every physical boundary block gives an actual retained hyperbolic
matrix with precisely its own actual complete cut axis. -/
theorem generalCoreTarget_boundary_matrix_axis (j : Fin t) :
    ∃ A : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A = generalCoreTargetGenerator g orders s t ho hdef d hd hb
        (generalCoreBoundarySideIndex g orders s t j 0) ∧ _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A ∈ G₀ ∧
      ∃ hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A ≠ 1, ∃ htA : 4 < (Matrix.trace A.val)^2,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA = _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine (Q₀)
          (generalCoreBoundarySideIndex g orders s t j 1) := by
  let i := generalCoreBoundarySideIndex g orders s t j 0
  have hk : θ₀ (finRotate _ i) = Real.pi/2 := by
    rw [generalCoreBoundarySideIndex_next_zero, generalCoreBoundarySideIndex_angle]
    norm_num
  have hj : θ₀ (finRotate _ (finRotate _ i)) = Real.pi/2 := by
    rw [generalCoreBoundarySideIndex_next_zero, generalCoreBoundarySideIndex_next_one,
      generalCoreBoundarySideIndex_angle]
    norm_num
  obtain ⟨u, v, q, l, _hu, _hv, _huv, hl, _hqu, _hqv, hK, ht⟩ :=
    generalSignature_boundary_triple_translation θ₀ d hθ₀ hd hb i hk hj
  rw [generalCoreBoundarySideIndex_next_zero] at hK
  have hgen : cofiniteTangentPairingElement θ₀ d hθ₀ hd hb i
      (finRotate _ (finRotate _ i)) =
      generalCoreTargetGenerator g orders s t ho hdef d hd hb i := by
    simp only [i, generalCoreTargetGenerator, generalCoreBoundarySideIndex_pair_zero,
      generalCoreBoundarySideIndex_next_zero, generalCoreBoundarySideIndex_next_one]
  obtain ⟨A, hAact, hAn, hAt, hAxis⟩ := generalSignature_translation_matrix_axis
    (generalCoreTargetGenerator g orders s t ho hdef d hd hb i) _ q l hl hK
    (by rw [← hgen]; exact ht)
  refine ⟨A, hAact, ?_, hAn, hAt, hAxis⟩
  exact nativeConformalSubgroupMobiusGroup_matrix_mem _
    (generalCoreTargetGroup_conformal g orders s t ho hdef d hd hb) A
    (hAact ▸ generalCoreBoundarySideIndex_generator_mem g orders s t ho hdef d hd hb j)

/-- The actual retained original group is non-elementary for every
positive boundary count. No target signature, target core or target census
is supplied: elementarity would force every auxiliary generator to preserve
one true cut axis, contrary to the actual auxiliary finite-area result. -/
theorem generalCoreTargetMobius_nonElementary
    (ht : 0 < t) : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary G₀ := by
  let j₀ : Fin t := ⟨0, ht⟩
  let K := _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine (Q₀) (generalCoreBoundarySideIndex g orders s t j₀ 1)
  obtain ⟨A₀, hA₀act, hA₀mem, hA₀n, hA₀t, hAxis₀⟩ :=
    generalCoreTarget_boundary_matrix_axis g orders s t ho hdef d hd hb j₀
  have hA₀hyp : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A₀) :=
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff A₀ hA₀n).mpr hA₀t
  intro hE
  obtain ⟨a, b, hab, ha, hb', hpair⟩ := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.discrete_elementary_loxodromic_fixed_pair
    G₀ (PG₀).discrete hE (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A₀) hA₀mem hA₀hyp.1
  have hEnds : K.idealEndpoints = ({a, b} : Set Mobius.ExtendedComplex) := by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A₀ hA₀n hA₀t = K at hAxis₀
    rw [← hAxis₀, _root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis_idealEndpoints]
    ext z
    change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A₀).val z = z ↔ z ∈ ({a, b} : Set Mobius.ExtendedComplex)
    constructor
    · intro hz
      by_cases hza : z = a
      · exact Or.inl hza
      · by_cases hzb : z = b
        · exact Or.inr hzb
        · exact False.elim (hA₀n (_root_.LowDimensionalTopology.Geometry.Mobius.mobius_eq_one_of_three_fixed _ a b z hab
            (Ne.symm hza) (Ne.symm hzb) ha hb' hz))
    · rintro (rfl | rfl)
      · exact ha
      · exact hb'
  have htarget (f : ℍ ≃ᵢ ℍ) (hf : f ∈ H₀) : f '' K.carrier = K.carrier := by
    obtain ⟨A, hA⟩ := generalCoreTargetGroup_conformal g orders s t ho hdef d hd hb hf
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A = f at hA
    have hAm : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A ∈ H₀ := hA.symm ▸ hf
    let F : G₀ := generalCoreTargetMobiusEquiv g orders s t ho hdef d hd hb ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A, hAm⟩
    have hF : F.val = _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A := nativeConformalSubgroupMobiusHom_matrix _ _ A hAm
    have he := hpair F
    rw [hF, ← hEnds] at he
    have hline := (generalSignature_SL_line_invariance A K).mpr he
    rw [← hA]
    exact hline
  have hcut (j : Fin t) :
      _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine (Q₀) (generalCoreBoundarySideIndex g orders s t j 1) = K := by
    obtain ⟨A, hAact, _hAm, hAn, hAt, hAxis⟩ :=
      generalCoreTarget_boundary_matrix_axis g orders s t ho hdef d hd hb j
    have hline : ((A • · : ℍ → ℍ) '' K.carrier) = K.carrier := by
      change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A : ℍ → ℍ) '' K.carrier = K.carrier
      rw [hAact]
      exact htarget _ (generalCoreBoundarySideIndex_generator_mem g orders s t ho hdef d hd hb j)
    exact hAxis.symm.trans (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis_unique_invariant A hAn hAt K hline).symm
  let stab : Subgroup (ℍ ≃ᵢ ℍ) := {
    carrier := {f | f '' K.carrier = K.carrier}
    one_mem' := by
      change (fun z : ℍ => z) '' K.carrier = K.carrier
      exact image_id' _
    mul_mem' := by
      intro f k hf hk
      change (fun z : ℍ => f (k z)) '' K.carrier = K.carrier
      rw [← image_image, hk, hf]
    inv_mem' := by
      intro f hf
      change f.symm '' K.carrier = K.carrier
      have hh := congrArg (fun U : Set ℍ => f.symm '' U) hf
      simpa only [image_image, f.symm_apply_apply, image_id'] using hh.symm }
  have haux : (S₀).Generated ≤ stab := by
    apply (Subgroup.closure_le stab).mpr
    rintro _ ⟨side, rfl⟩
    obtain ⟨i, rfl⟩ := (_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv (Q₀)).surjective side
    change (S₀).element ((_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv (Q₀)) i) '' K.carrier = K.carrier
    change cofiniteTangentPairingElement θ₀ d hθ₀ hd hb
      ((_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv (Q₀)).symm ((_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv (Q₀)) i))
      (ρ₀ ((_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv (Q₀)).symm ((_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv (Q₀)) i))) ''
        K.carrier = K.carrier
    simp only [Equiv.symm_apply_apply]
    by_cases hi : generalCoreIsCutSide g orders s t i
    · obtain ⟨j, rfl⟩ := (generalCoreIsCutSide_iff g orders s t i).mp hi
      rw [generalCoreBoundarySideIndex_pair_one]
      have hnext : θ₀ (generalCoreBoundarySideIndex g orders s t j 1) =
          θ₀ (finRotate _ (generalCoreBoundarySideIndex g orders s t j 1)) := by
        rw [generalCoreBoundarySideIndex_next_one, generalCoreBoundarySideIndex_angle,
          generalCoreBoundarySideIndex_angle]
        norm_num
      have hh := generalSignature_self_pairing_support θ₀ d hθ₀ hd hb
        (generalCoreBoundarySideIndex g orders s t j 1) hnext
      dsimp only at hh
      rwa [hcut j] at hh
    · exact htarget _ (generalCoreTargetGenerator_mem g orders s t ho hdef d hd hb i hi)
  apply generalCoreAuxMobius_nonElementary g orders s t ho hdef d hd hb
  apply _root_.LowDimensionalTopology.Geometry.DiscreteGroups.isElementary_of_invariant_pair Γ₀ a b
  intro γ
  let E := cofiniteMixedTangentialGroupEquiv θ₀ d hθ₀ hd hb ρ₀ hρ₀ hθρ₀
  let f := E.symm γ
  obtain ⟨A, hA⟩ := cofiniteMixedTangentialGenerated_conformal θ₀ d hθ₀ hd hb ρ₀ hρ₀ hθρ₀ f.property
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A = f.val at hA
  have hAm : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A ∈ (S₀).Generated := hA.symm ▸ f.property
  have hf : (⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A, hAm⟩ : (S₀).Generated) = f := Subtype.ext hA
  have hγ : γ.val = _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A := by
    have hh : (E ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A, hAm⟩).val = _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A :=
      nativeConformalSubgroupMobiusHom_matrix _ _ A hAm
    rw [hf, E.apply_symm_apply] at hh
    exact hh
  have hline : ((A • · : ℍ → ℍ) '' K.carrier) = K.carrier := haux hAm
  have he := (generalSignature_SL_line_invariance A K).mp hline
  rw [hEnds, ← hγ] at he
  exact he

/-- The same entire actual target in its genuine Cayley disc is non-elementary. -/
theorem generalCoreTargetCayley_nonElementary (ht : 0 < t) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius G₀) :=
  (generalCoreTargetMobius_nonElementary g orders s t ho hdef d hd hb ht).conjugation _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius

end ActualGroups
end LowDimensionalTopology.Geometry.Fuchsian
