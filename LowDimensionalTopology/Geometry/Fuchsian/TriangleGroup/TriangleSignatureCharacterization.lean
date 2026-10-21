/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Mobius.Circle.IdealBoundaryAction
public import LowDimensionalTopology.Geometry.Mobius.Affine.Basic
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.ThreeMarkedSignatureRigidity
public import LowDimensionalTopology.Geometry.Fuchsian.Covolume.OriginalFirstKindArea
public import LowDimensionalTopology.Geometry.Fuchsian.Covolume.LowGenusSignatureArea
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.ClosedTriangleSignaturePatterns
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.TriangleTypeGeometry
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.MobiusTriangleGroups
public import LowDimensionalTopology.Geometry.Fuchsian.Elementary.DihedralInvariantDiscs
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.MobiusTriangleFirstKind
public import LowDimensionalTopology.Geometry.Fuchsian.Cusp.CuspCompletionConjugacy
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.ClosedTriangleCovolume
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Boundary.FiniteAreaPolygonSides
public import LowDimensionalTopology.Geometry.Fuchsian.Covolume.CompactSignatureFiniteGeneration
@[expose] public section


noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Topology
open scoped OnePoint
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
local instance triangleDeficitSphereMeasurable : MeasurableSpace Mobius.ExtendedComplex := borel Mobius.ExtendedComplex
local instance triangleDeficitSphereBorel : BorelSpace Mobius.ExtendedComplex := ⟨rfl⟩

/-- A genuine original hyperbolic fundamental domain has positive area.
The argument uses the true countable closed-tile cover and invariant area. -/
theorem fuchsianFundamentalDomain_area_ne_zero
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) {L : Set P.domain.carrier}
    (hL : IsFuchsianFundamentalDomain P L) : P.area L ≠ 0 := by
  let : Countable H := P.countable
  intro hzero
  have hc : P.area (closure L) = 0 := by
    rw [← _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain.measure_eq_of_between H P.domain.carrier hL
      subset_closure (Subset.refl _), hzero]
  have hu : P.area (univ : Set P.domain.carrier) = 0 := by
    rw [← hL.iUnion_image_closure_eq_univ]
    apply measure_iUnion_null
    intro g
    rw [P.area_image g (closure L) isClosed_closure.measurableSet, hc]
  exact (Measure.measure_univ_ne_zero.mpr (fuchsian_original_area_ne_zero P)) hu

/-- The original finite-generation and first-kind hypotheses, with the
actual genus-zero signature, force positive hyperbolic signature deficit.
Neither positivity nor finite area is supplied as an extra assumption. -/
theorem firstKind_finitelyGenerated_genus_zero_signature_deficit_pos
    {H : Subgroup Mobius.complexMobiusGroup} (D : FuchsianDisc H)
    (hFG : H.FG) (hfirst : D.IsFirstKind) (orders : List ℕ) (cusps : ℕ)
    (hSig : HasCofiniteFuchsianSignature D 0 orders cusps) :
    0 < -2 + (cusps : ℝ) + (orders.map (fun n : ℕ => 1 - 1 / (n : ℝ))).sum := by
  let P := geometricDiscData D
  obtain ⟨w, hw, _hgood⟩ := exists_actual_dirichlet_horocycle_good_center P
  let L := dirichletDomain P w
  have hL : IsFuchsianFundamentalDomain P L := dirichletDomain_fundamental P w hw
  let F := geometricDiscHomeomorph D ⁻¹' L
  have hF : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain H (fuchsianGeometricDomain D).carrier
      (geometricModelArea D) F := geometricModel_fundamentalDomain_of_disc D hL
  have ha := firstKind_finitelyGenerated_geometricArea_ne_top D hfirst hFG F hF
  have he := geometricDisc_fundamental_area_eq_original D F hF hL
  have hn : geometricModelArea D F ≠ 0 := by
    rw [← he]
    exact fuchsianFundamentalDomain_area_ne_zero P hL
  have hp := ENNReal.toReal_pos hn ha
  have hformula := cofinite_signature_area_of_genus_le_one D F hF ha 0 cusps orders hSig (by omega)
  rw [hformula] at hp
  norm_num only [Nat.cast_zero, mul_zero, zero_sub] at hp
  exact (mul_pos_iff_of_pos_left (mul_pos (by norm_num) Real.pi_pos)).mp hp

end LowDimensionalTopology.Geometry.Fuchsian


noncomputable section
set_option maxHeartbeats 800000
open Set Topology
open scoped UpperHalfPlane OnePoint
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Polygon

/-- Positive hyperbolic signature deficit constructs a genuine triangle
with exactly the prescribed three actual special classes. This is a
geometric existence lemma, not a numerical definition of a signature. -/
theorem exists_actual_triangle_of_three_mark_signature_deficit
    (orders : List ℕ) (cusps : ℕ) (horders : ∀ n ∈ orders, 2 ≤ n)
    (hthree : orders.length + cusps = 3)
    (hdef : 0 < -2 + (cusps : ℝ) + (orders.map (fun n : ℕ => 1 - 1 / (n : ℝ))).sum) :
    ∃ (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) (ha : IsIntegralTriangleAngle T.alpha)
      (hb : IsIntegralTriangleAngle T.beta) (hc : IsIntegralTriangleAngle T.gamma),
      HasCofiniteFuchsianSignature (closedTriangleMobiusData T ha hb hc).asFuchsianDisc 0 orders cusps := by
  rcases orders with _ | ⟨n, l⟩
  · have hc : cusps = 3 := by simpa only [List.length_nil, zero_add] using hthree
    subst cusps
    let T := prescribedIdealHTriangle 0 0 le_rfl le_rfl (by simpa using Real.pi_pos)
    obtain ⟨hα, hβ, hγ⟩ := prescribedIdealHTriangle_angles 0 0 le_rfl le_rfl (by simpa using Real.pi_pos)
    exact ⟨T, Or.inl hα, Or.inl hβ, Or.inl hγ,
      closedTriangle_actual_signature_three_ideal T hα hβ hγ _⟩
  rcases l with _ | ⟨m, l⟩
  · have hc : cusps = 2 := by simp only [List.length_cons, List.length_nil] at hthree; omega
    subst cusps
    have hn : 2 ≤ n := horders n (by simp)
    have hα : 0 < Real.pi / (n : ℝ) := div_pos Real.pi_pos (by positivity)
    have hαπ : Real.pi / (n : ℝ) < Real.pi :=
      div_lt_self Real.pi_pos (by exact_mod_cast (show 1 < n by omega))
    let T := prescribedIdealHTriangle (Real.pi / n) 0 hα.le le_rfl (by simpa using hαπ)
    obtain ⟨hTα, hTβ, hTγ⟩ := prescribedIdealHTriangle_angles (Real.pi / n) 0 hα.le le_rfl
      (by simpa using hαπ)
    exact ⟨T, Or.inr ⟨n, hn, hTα⟩, Or.inl hTβ, Or.inl hTγ,
      closedTriangle_actual_signature_two_ideal T n hn hTα hTβ hTγ _⟩
  rcases l with _ | ⟨k, l⟩
  · have hc : cusps = 1 := by simp only [List.length_cons, List.length_nil] at hthree; omega
    subst cusps
    have hn : 2 ≤ n := horders n (by simp)
    have hm : 2 ≤ m := horders m (by simp)
    have hα : 0 < Real.pi / (n : ℝ) := div_pos Real.pi_pos (by positivity)
    have hβ : 0 < Real.pi / (m : ℝ) := div_pos Real.pi_pos (by positivity)
    have hsum : Real.pi / n + Real.pi / m < Real.pi := by
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.cast_one] at hdef
      have hp := mul_pos Real.pi_pos hdef
      simp only [div_eq_mul_inv] at hp ⊢
      nlinarith only [hp]
    let T := prescribedIdealHTriangle (Real.pi / n) (Real.pi / m) hα.le hβ.le hsum
    obtain ⟨hTα, hTβ, hTγ⟩ := prescribedIdealHTriangle_angles (Real.pi / n) (Real.pi / m) hα.le hβ.le hsum
    exact ⟨T, Or.inr ⟨n, hn, hTα⟩, Or.inr ⟨m, hm, hTβ⟩, Or.inl hTγ,
      closedTriangle_actual_signature_one_ideal T n m hn hm hTα hTβ hTγ _⟩
  have hl : l = [] := by simp only [List.length_cons] at hthree; exact List.length_eq_zero_iff.mp (by omega)
  subst l
  have hc : cusps = 0 := by simp only [List.length_cons, List.length_nil] at hthree; omega
  subst cusps
  have hn : 2 ≤ n := horders n (by simp)
  have hm : 2 ≤ m := horders m (by simp)
  have hk : 2 ≤ k := horders k (by simp)
  have hα : 0 < Real.pi / (n : ℝ) := div_pos Real.pi_pos (by positivity)
  have hβ : 0 < Real.pi / (m : ℝ) := div_pos Real.pi_pos (by positivity)
  have hγ : 0 < Real.pi / (k : ℝ) := div_pos Real.pi_pos (by positivity)
  have hsum : Real.pi / n + Real.pi / m + Real.pi / k < Real.pi := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.cast_zero] at hdef
    have hp := mul_pos Real.pi_pos hdef
    simp only [div_eq_mul_inv] at hp ⊢
    nlinarith only [hp]
  obtain ⟨Q, hQα, hQβ, hQγ⟩ := exists_finite_triangle_with_angles _ _ _ hα hβ hγ hsum
  let T := Q.toClosedHTriangle
  have hTα : T.alpha = Real.pi / n := Q.closed_angles.1.trans hQα
  have hTβ : T.beta = Real.pi / m := Q.closed_angles.2.1.trans hQβ
  have hTγ : T.gamma = Real.pi / k := Q.closed_angles.2.2.trans hQγ
  exact ⟨T, Or.inr ⟨n, hn, hTα⟩, Or.inr ⟨m, hm, hTβ⟩, Or.inr ⟨k, hk, hTγ⟩,
    closedTriangle_actual_signature_finite T n m k hn hm hk hTα hTβ hTγ _⟩

/--
Integral actual corner angles provide the literal finite-or-infinite
orders in the geometric triangle-group predicate.
-/
theorem integral_triangle_angle_exists_order (α : ℝ) (hα : IsIntegralTriangleAngle α) :
    ∃ n : ℕ∞, 2 ≤ n ∧ triangleOrderAngle n = α := by
  rcases hα with h | ⟨n, hn, he⟩
  · exact ⟨⊤, le_top, triangleOrderAngle_top.trans h.symm⟩
  · exact ⟨n, by exact_mod_cast hn, (triangleOrderAngle_nat n).trans he.symm⟩

/-- The actual whole Mobius image of every integral triangle is a genuine
Mobius triangle group. -/
theorem closedTriangleMobiusGroup_isMobiusTriangleGroup
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) (ha : IsIntegralTriangleAngle T.alpha)
    (hb : IsIntegralTriangleAngle T.beta) (hc : IsIntegralTriangleAngle T.gamma) :
    IsMobiusTriangleGroup (closedTriangleMobiusGroup T) := by
  obtain ⟨p, hp, hpa⟩ := integral_triangle_angle_exists_order T.alpha ha
  obtain ⟨q, hq, hqb⟩ := integral_triangle_angle_exists_order T.beta hb
  obtain ⟨r, hr, hrc⟩ := integral_triangle_angle_exists_order T.gamma hc
  apply isMobiusTriangleGroup_native_image _ inf_le_right
  exact ⟨p, q, r, hp, hq, hr, T, hpa.symm, hqb.symm, hrc.symm, rfl⟩

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  Set

/-- The original first-kind finite-generation context and an actual
three-mark genus-zero signature identify the entire group and physical
disc with a literal reciprocal-angle hyperbolic triangle group. -/
theorem firstKind_three_marked_signature_exists_actual_triangle
    {H : Subgroup Mobius.complexMobiusGroup} (D : FuchsianDisc H)
    (hFG : H.FG) (hfirst : D.IsFirstKind) (orders : List ℕ) (cusps : ℕ)
    (hSig : HasCofiniteFuchsianSignature D 0 orders cusps)
    (hthree : orders.length + cusps = 3) :
    ∃ (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) (ha : IsIntegralTriangleAngle T.alpha)
      (hb : IsIntegralTriangleAngle T.beta) (hc : IsIntegralTriangleAngle T.gamma),
      HasCofiniteFuchsianSignature (closedTriangleMobiusData T ha hb hc).asFuchsianDisc
        0 orders cusps ∧
      ∃ M : Mobius.complexMobiusGroup,
        _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate M H = closedTriangleMobiusGroup T ∧
        M.val '' D.carrier = _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet := by
  have hdef := firstKind_finitelyGenerated_genus_zero_signature_deficit_pos D hFG hfirst
    orders cusps hSig
  obtain ⟨T, ha, hb, hc, hT⟩ := exists_actual_triangle_of_three_mark_signature_deficit
    orders cusps (fun _ hn => hSig.orders_two_le hn) hthree hdef
  obtain ⟨M, hM, hD⟩ := same_three_marked_signature_mobius_conjugate D
    (closedTriangleMobiusData T ha hb hc).asFuchsianDisc hSig hT hthree
  exact ⟨T, ha, hb, hc, hT, M, hM, hD⟩

/--
Reverse implication in the geometric actual
finite-generation signature context. Elliptic stabilizers are retained.
-/
theorem firstKind_three_marked_signature_isMobiusTriangleGroup
    {H : Subgroup Mobius.complexMobiusGroup} (D : FuchsianDisc H)
    (hFG : H.FG) (hfirst : D.IsFirstKind) (orders : List ℕ) (cusps : ℕ)
    (hSig : HasCofiniteFuchsianSignature D 0 orders cusps)
    (hthree : orders.length + cusps = 3) : IsMobiusTriangleGroup H := by
  obtain ⟨T, ha, hb, hc, _hT, M, hM, _hD⟩ :=
    firstKind_three_marked_signature_exists_actual_triangle D hFG hfirst orders cusps hSig hthree
  apply isMobiusTriangleGroup_of_conjugate H M
  rw [hM]
  exact closedTriangleMobiusGroup_isMobiusTriangleGroup T ha hb hc

end LowDimensionalTopology.Geometry.Fuchsian


noncomputable section
open Set Topology
open scoped UpperHalfPlane OnePoint
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Auxiliary.Analysis

theorem nativeConformalSubgroupMobiusHom_extension
    (K : Subgroup (ℍ ≃ᵢ ℍ))
    (hK : K ≤ _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup)
    (g : K) :
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.nativeHalfPlaneExtension g.val).val = (nativeConformalSubgroupMobiusHom K hK g).val := rfl

/-- Boundary conjugation takes the lower physical half-plane onto the upper one. -/
theorem complexConjugation_image_lowerHalfPlane :
    _root_.LowDimensionalTopology.Geometry.Mobius.complexConjugation '' dihedralLowerHalfPlane = _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet := by
  have hInf : (∞ : Mobius.ExtendedComplex) ∉ _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet := by
    rintro ⟨z, _hz, he⟩
    exact OnePoint.coe_ne_infty z he
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    cases w using OnePoint.rec with
    | infty =>
      obtain ⟨w,hw,hwe⟩ := hw
      have he : w=∞ := (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling (-1)).val.injective (hwe.trans (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling_infty _).symm)
      exact False.elim (hInf (he ▸ hw))
    | coe w =>
      rw [dihedralLowerHalfPlane_coe] at hw
      rw [_root_.LowDimensionalTopology.Geometry.Mobius.complexConjugation_coe,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.coe_mem_openHalfPlaneSet]
      simpa only [Complex.conj_im] using neg_pos.mpr hw
  · intro hz
    cases z using OnePoint.rec with
    | infty => exact False.elim (hInf hz)
    | coe z =>
      refine ⟨((starRingEnd ℂ) z : ℂ), ?_, ?_⟩
      · rw [dihedralLowerHalfPlane_coe]
        simpa only [Complex.conj_im] using neg_neg_of_pos ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.coe_mem_openHalfPlaneSet z).mp hz)
      · simp only [_root_.LowDimensionalTopology.Geometry.Mobius.complexConjugation_coe, Complex.conj_conj]

/-- A side mirror, followed by real-boundary reflection, is a genuine
holomorphic Mobius normalizer exchanging the two actual invariant discs
of the entire conformal triangle group. -/
theorem closedTriangle_opposite_disc_normalizer
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) :
    ∃ M : Mobius.complexMobiusGroup,
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate M (closedTriangleMobiusGroup T) = closedTriangleMobiusGroup T ∧
      M.val '' dihedralLowerHalfPlane = _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet := by
  let L := T.sideLineA
  let r := _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry L
  let F := nativeConformalSubgroupMobiusHom (triangleConformalGroup T) inf_le_right
  have hr : r ∈ triangleReflectionGroup T :=
    Subgroup.subset_closure ⟨L, by simp [triangleReflectionSides, L], rfl⟩
  let M : Mobius.complexMobiusGroup := ⟨_root_.LowDimensionalTopology.Geometry.Mobius.euclideanToComplexHom L.realReflection * _root_.LowDimensionalTopology.Geometry.Mobius.complexConjugation,
    by rw [_root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup_eq_fractionalLinearGroup]; exact _root_.LowDimensionalTopology.Geometry.Mobius.reflection_complex_anti L.realReflection_isReflection⟩
  have hR : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.nativeHalfPlaneExtension r).val = _root_.LowDimensionalTopology.Geometry.Mobius.euclideanToComplexHom L.realReflection :=
    nativeHalfPlaneExtension_reflection L
  have hconj (g : triangleConformalGroup T) :
      M * F g * M⁻¹ = F ⟨r * g.val * r⁻¹,
        closedTriangle_conformal_conjugate_mem T r hr g.val g.property⟩ := by
    have hpres := _root_.LowDimensionalTopology.Geometry.Hyperbolic.nativeHalfPlaneExtension_preserves g.val
    rw [nativeConformalSubgroupMobiusHom_extension _ inf_le_right g] at hpres
    obtain ⟨A, hA⟩ := mobius_preserves_halfPlane_exists_SL (F g) hpres
    have hcomm : (F g).val * _root_.LowDimensionalTopology.Geometry.Mobius.complexConjugation = _root_.LowDimensionalTopology.Geometry.Mobius.complexConjugation * (F g).val := by
      apply Equiv.ext
      intro z
      rw [← hA]
      exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_complexConjugation A z
    apply Subtype.ext
    change M.val * (F g).val * M.val⁻¹ = (_root_.LowDimensionalTopology.Geometry.Hyperbolic.nativeHalfPlaneExtension (r * g.val * r⁻¹)).val
    rw [map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
      nativeConformalSubgroupMobiusHom_extension _ inf_le_right g, hR]
    change (_root_.LowDimensionalTopology.Geometry.Mobius.euclideanToComplexHom L.realReflection * _root_.LowDimensionalTopology.Geometry.Mobius.complexConjugation) * (F g).val *
      (_root_.LowDimensionalTopology.Geometry.Mobius.euclideanToComplexHom L.realReflection * _root_.LowDimensionalTopology.Geometry.Mobius.complexConjugation)⁻¹ =
        _root_.LowDimensionalTopology.Geometry.Mobius.euclideanToComplexHom L.realReflection * (F g).val * (_root_.LowDimensionalTopology.Geometry.Mobius.euclideanToComplexHom L.realReflection)⁻¹
    calc
      _ = _root_.LowDimensionalTopology.Geometry.Mobius.euclideanToComplexHom L.realReflection *
          (_root_.LowDimensionalTopology.Geometry.Mobius.complexConjugation * (F g).val) * (_root_.LowDimensionalTopology.Geometry.Mobius.euclideanToComplexHom L.realReflection * _root_.LowDimensionalTopology.Geometry.Mobius.complexConjugation)⁻¹ := by group
      _ = _root_.LowDimensionalTopology.Geometry.Mobius.euclideanToComplexHom L.realReflection *
          ((F g).val * _root_.LowDimensionalTopology.Geometry.Mobius.complexConjugation) * (_root_.LowDimensionalTopology.Geometry.Mobius.euclideanToComplexHom L.realReflection * _root_.LowDimensionalTopology.Geometry.Mobius.complexConjugation)⁻¹ := by rw [hcomm]
      _ = _ := by group
  refine ⟨M, ?_, ?_⟩
  · apply le_antisymm
    · intro f hf
      obtain ⟨f, ⟨g, rfl⟩, rfl⟩ := (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff M _ f).mp hf
      exact hconj g ▸ ⟨_, rfl⟩
    · rintro f ⟨g, rfl⟩
      let g' : triangleConformalGroup T := ⟨r⁻¹ * g.val * r,
        by simpa only [inv_inv] using (closedTriangle_conformal_conjugate_mem T r⁻¹
          ((triangleReflectionGroup T).inv_mem hr) g.val g.property)⟩
      apply (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff M _ _).mpr
      refine ⟨F g', ⟨g', rfl⟩, ?_⟩
      rw [hconj]
      congr 1
      apply Subtype.ext
      change r * (r⁻¹ * g.val * r) * r⁻¹ = g.val
      group
  · change (_root_.LowDimensionalTopology.Geometry.Mobius.euclideanToComplexHom L.realReflection * _root_.LowDimensionalTopology.Geometry.Mobius.complexConjugation) '' _ = _
    rw [Equiv.Perm.coe_mul, Function.comp_def, ← image_image,
      complexConjugation_image_lowerHalfPlane, ← hR]
    exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.nativeHalfPlaneExtension_preserves r

/-- Every original invariant disc of a genuine Mobius triangle group can
be normalized together with the whole group. The opposite disc is handled
by an actual side-mirror normalizer, rather than being silently discarded. -/
theorem mobiusTriangleGroup_exists_whole_disc_triangle_model
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (ht : IsMobiusTriangleGroup H) :
    ∃ (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) (_ha : IsIntegralTriangleAngle T.alpha)
      (_hb : IsIntegralTriangleAngle T.beta) (_hc : IsIntegralTriangleAngle T.gamma)
      (M : Mobius.complexMobiusGroup),
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate M H = closedTriangleMobiusGroup T ∧
        M.val '' D.carrier = _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet := by
  obtain ⟨K, _hK, hTri, m, hm⟩ := ht
  obtain ⟨p,q,r,hp,hq,hr,T,hα,hβ,hγ,hK⟩ := hTri
  subst K
  have ha : IsIntegralTriangleAngle T.alpha := hα ▸ triangleOrderAngle_isIntegral p hp
  have hb : IsIntegralTriangleAngle T.beta := hβ ▸ triangleOrderAngle_isIntegral q hq
  have hc : IsIntegralTriangleAngle T.gamma := hγ ▸ triangleOrderAngle_isIntegral r hr
  let P := closedTriangleMobiusData T ha hb hc
  have hm' : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate m H = closedTriangleMobiusGroup T := hm
  have hi (f : closedTriangleMobiusGroup T) :
      f.val.val '' (m.val '' D.carrier) = m.val '' D.carrier := by
    have hf : f.val ∈ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate m H := hm'.symm ▸ f.property
    obtain ⟨g,hg,he⟩ := (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff m H f.val).mp hf
    rw [← he, _root_.LowDimensionalTopology.Geometry.Mobius.stableAxis_conjugate_image, D.image_eq ⟨g,hg⟩]
  have hbound : frontier (m.val '' D.carrier) = _root_.LowDimensionalTopology.Geometry.Mobius.complexRealAxis := by
    have he := _root_.LowDimensionalTopology.Geometry.Mobius.invariantComplexDiscs_frontier_eq (closedTriangleMobiusGroup T)
      (closedTriangle_nonElementary T ha hb hc P) (D.isDisc.image m) P.asFuchsianDisc.isDisc
      hi P.preserves
    exact he.trans (nielsen_openHalfPlane_frontier.trans _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneIdealBoundary_eq_realAxis)
  rcases complexDisc_real_frontier_sides (D.isDisc.image m) hbound with hu | hl
  · exact ⟨T,ha,hb,hc,m,hm',hu⟩
  · obtain ⟨s,hs,hDisc⟩ := closedTriangle_opposite_disc_normalizer T
    refine ⟨T,ha,hb,hc,s*m,?_,?_⟩
    · rw [← _root_.LowDimensionalTopology.Geometry.DiscreteGroups.dilation_subgroupConjugate_compose, hm', hs]
    · change (fun z => s.val (m.val z)) '' D.carrier = _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet
      rw [← image_image, hl, hDisc]

/-- Forward signature statement for every original disc model of an
actual triangle group, with the complete repeated-order list and all cusps. -/
theorem mobiusTriangleGroup_actual_three_marked_signature
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (ht : IsMobiusTriangleGroup H) :
    ∃ orders : List ℕ, ∃ cusps : ℕ,
      HasCofiniteFuchsianSignature D 0 orders cusps ∧ orders.length + cusps = 3 := by
  obtain ⟨T,ha,hb,hc,M,hM,hDisc⟩ := mobiusTriangleGroup_exists_whole_disc_triangle_model D ht
  let P := closedTriangleMobiusData T ha hb hc
  let orders := closedTriangleFiniteCornerOrderList T ha hb hc
  let cusps := Nat.card {i : Fin 3 | closedTriangleCornerAngle T i=0}
  have hS := closedTriangle_actual_cofinite_signature T ha hb hc P
  have hInv : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate M⁻¹ (closedTriangleMobiusGroup T)=H := by
    rw [← hM, _root_.LowDimensionalTopology.Geometry.DiscreteGroups.dilation_subgroupConjugate_compose]
    simp only [inv_mul_cancel]
    ext f
    simp [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff]
  have hImage : M.val.symm '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=D.carrier := by
    rw [← hDisc, M.val.symm_image_image]
  refine ⟨orders,cusps,cofinite_signature_of_conjugate_group P.asFuchsianDisc D M⁻¹
    hInv hImage 0 cusps orders hS,?_⟩
  change (closedTriangleFiniteCornerOrderList T ha hb hc).length + cusps = 3
  simp only [closedTriangleFiniteCornerOrderList, List.length_ofFn]
  simpa only [cusps, Nat.card_eq_fintype_card] using closedTriangle_finite_ideal_card_sum T

/-- Actual geometric triangle groups are finitely generated; finite area
is obtained from the proved geometric domain, not added to the statement. -/
theorem mobiusTriangleGroup_finitelyGenerated
    {H : Subgroup Mobius.complexMobiusGroup}
    (ht : IsMobiusTriangleGroup H) : H.FG := by
  obtain ⟨K,hK,hTri,q,hq⟩ := ht
  obtain ⟨p,r,s,hp,hr,hs,T,hα,hβ,hγ,hT⟩ := hTri
  subst K
  let ha := hα ▸ triangleOrderAngle_isIntegral p hp
  let hb := hβ ▸ triangleOrderAngle_isIntegral r hr
  let hc := hγ ▸ triangleOrderAngle_isIntegral s hs
  let P := closedTriangleMobiusData T ha hb hc
  obtain ⟨F,hF,harea⟩ := closedTriangle_geometric_finite_domain T ha hb hc P
  have hFG : (closedTriangleMobiusGroup T).FG := finite_area_group_finitelyGenerated
    P.asFuchsianDisc F hF harea
  have hFG' : (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H).FG := hq.symm ▸ hFG
  let : Group.FG (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H) :=
    (Group.fg_iff_subgroup_fg _).mpr hFG'
  let E := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence q H
  exact (Group.fg_iff_subgroup_fg H).mp
    (Group.fg_of_surjective (f := E.symm.toMonoidHom) E.symm.surjective)

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  Set

/--
The actual whole-group triangle characterization, in the original
finite-generation context used to define signatures.
-/
theorem mobiusTriangleGroup_iff_firstKind_three_marked_signature
    {H : Subgroup Mobius.complexMobiusGroup} (D : FuchsianDisc H) :
    IsMobiusTriangleGroup H ↔ H.FG ∧ D.IsFirstKind ∧
      ∃ orders : List ℕ, ∃ cusps : ℕ,
        HasCofiniteFuchsianSignature D 0 orders cusps ∧ orders.length + cusps = 3 := by
  constructor
  · intro ht
    exact ⟨mobiusTriangleGroup_finitelyGenerated ht, mobiusTriangleGroup_actual_firstKind D ht,
      mobiusTriangleGroup_actual_three_marked_signature D ht⟩
  · rintro ⟨hFG, hfirst, orders, cusps, hSig, hthree⟩
    exact firstKind_three_marked_signature_isMobiusTriangleGroup D hFG hfirst orders cusps hSig hthree

/--
With all original orders retained. The left
side uses the literal triangle's reciprocal-angle denominators, including
their multiplicities, and counts its actual zero-angle ideal corners.
The same Mobius transformation carries both the whole group and the
whole original hyperbolic-plane model.
-/
theorem triangle_conjugacy_with_orders_cusps_iff_fg_firstKind_genus_zero_three_marks
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (orders : List ℕ)
    (cusps : ℕ) :
    (∃ (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) (ha : IsIntegralTriangleAngle T.alpha)
      (hb : IsIntegralTriangleAngle T.beta) (hc : IsIntegralTriangleAngle T.gamma),
      (closedTriangleFiniteCornerOrderList T ha hb hc).Perm orders ∧
      Nat.card {i : Fin 3 | closedTriangleCornerAngle T i=0} = cusps ∧
      ∃ M : Mobius.complexMobiusGroup,
        _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate M H = closedTriangleMobiusGroup T ∧
          M.val '' D.carrier = _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet) ↔
      H.FG ∧ D.IsFirstKind ∧ HasCofiniteFuchsianSignature D 0 orders cusps ∧
        orders.length + cusps = 3 := by
  constructor
  · rintro ⟨T,ha,hb,hc,hList,hCount,M,hM,hDisc⟩
    have ht : IsMobiusTriangleGroup H := by
      apply isMobiusTriangleGroup_of_conjugate H M
      rw [hM]
      exact closedTriangleMobiusGroup_isMobiusTriangleGroup T ha hb hc
    let P := closedTriangleMobiusData T ha hb hc
    have hs := closedTriangle_actual_cofinite_signature T ha hb hc P
    have hS : HasCofiniteFuchsianSignature P.asFuchsianDisc 0 orders cusps := {
      ellipticClassesFinite := hs.ellipticClassesFinite
      parabolicClassesFinite := hs.parabolicClassesFinite
      compact := hs.compact
      topologicalGenus := hs.topologicalGenus
      ellipticOrders := hList.symm.trans hs.ellipticOrders
      cuspCount := hCount.symm.trans hs.cuspCount }
    have hInv : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate M⁻¹ (closedTriangleMobiusGroup T)=H := by
      rw [← hM, _root_.LowDimensionalTopology.Geometry.DiscreteGroups.dilation_subgroupConjugate_compose]
      simp only [inv_mul_cancel]
      ext f
      simp [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff]
    have hImage : M.val.symm '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=D.carrier := by
      rw [← hDisc, M.val.symm_image_image]
    have hSig := cofinite_signature_of_conjugate_group P.asFuchsianDisc D M⁻¹
      hInv hImage 0 cusps orders hS
    have hthree : orders.length + cusps = 3 := by
      rw [← hList.length_eq, ← hCount]
      simp only [closedTriangleFiniteCornerOrderList, List.length_ofFn]
      simpa only [Nat.card_eq_fintype_card] using closedTriangle_finite_ideal_card_sum T
    exact ⟨mobiusTriangleGroup_finitelyGenerated ht, mobiusTriangleGroup_actual_firstKind D ht,
      hSig, hthree⟩
  · rintro ⟨hFG,hfirst,hSig,hthree⟩
    obtain ⟨T,ha,hb,hc,hs,M,hM,hDisc⟩ :=
      firstKind_three_marked_signature_exists_actual_triangle D hFG hfirst orders cusps hSig hthree
    have hT := closedTriangle_actual_cofinite_signature T ha hb hc (closedTriangleMobiusData T ha hb hc)
    exact ⟨T,ha,hb,hc,hT.ellipticOrders.trans hs.ellipticOrders.symm,
      hT.cuspCount.trans hs.cuspCount.symm,M,hM,hDisc⟩

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  Set

/--
directly from the original first-kind property
and the actual three-mark signature. Finite generation is derived from
the true compact cusp completion and finite actual cusp classes.
-/
theorem triangle_conjugacy_with_orders_cusps_iff_firstKind_genus_zero_three_marks
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (orders : List ℕ)
    (cusps : ℕ) :
    (∃ (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) (ha : IsIntegralTriangleAngle T.alpha)
      (hb : IsIntegralTriangleAngle T.beta) (hc : IsIntegralTriangleAngle T.gamma),
      (closedTriangleFiniteCornerOrderList T ha hb hc).Perm orders ∧
      Nat.card {i : Fin 3 | closedTriangleCornerAngle T i=0} = cusps ∧
      ∃ M : Mobius.complexMobiusGroup,
        _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate M H = closedTriangleMobiusGroup T ∧
          M.val '' D.carrier = _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet) ↔
      D.IsFirstKind ∧ HasCofiniteFuchsianSignature D 0 orders cusps ∧
        orders.length + cusps = 3 := by
  rw [triangle_conjugacy_with_orders_cusps_iff_fg_firstKind_genus_zero_three_marks]
  constructor
  · rintro ⟨_hFG,hfirst,hSig,hthree⟩
    exact ⟨hfirst,hSig,hthree⟩
  · rintro ⟨hfirst,hSig,hthree⟩
    exact ⟨hSig.finitelyGenerated,hfirst,hSig,hthree⟩

end LowDimensionalTopology.Geometry.Fuchsian
