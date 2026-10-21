/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.Elliptic.EllipticTraceTriangleGeometry
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.Elliptic.EllipticTriangleSignatureProfile
public import LowDimensionalTopology.Geometry.Fuchsian.Generation.TwoParabolics.ParabolicActualSignatures
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane OnePoint MatrixGroups

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/--
The exact original triangle exceptions. The elliptic
order divides the third actual cone order; only the other two are sorted.
-/
def IsEllipticTraceTriangleException {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) (n:ℕ) : Prop :=
  ∃a b c:ℕ,2≤a ∧a≤b ∧2≤c ∧n∣c ∧
    HasCofiniteFuchsianSignature D 0 [a,b,c] 0 ∧
    (a=2 ∨a=3 ∧(b=3 ∨b=4 ∨b=5))

/-- Both original trace inequalities outside precisely the listed
actual triangle signatures, retaining the original elliptic order. -/
theorem HalfPlaneFuchsianGroup.elliptic_trace_bounds_outside_triangle_exceptions
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P:HalfPlaneFuchsianGroup H)
    (A B:Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (hlA:HasLeastEllipticRotation
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A))
    (hAH:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      A∈H) (hBH:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B∈H)
    (hNE:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B}:Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (n:ℕ) (hn:3≤n) (horder:orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)=n)
    (hNo:¬IsEllipticTraceTriangleException P.asFuchsianDisc n) :
    2+4*(Real.cos (Real.pi/n))^2≤Matrix.trace (A*B*A⁻¹*B⁻¹).val ∧
      3≤Matrix.trace (A*B*A⁻¹*B⁻¹).val ∧
      4≤|(Matrix.trace A.val)^2-4|+|Matrix.trace (A*B*A⁻¹*B⁻¹).val-2| := by
  have hbound:2+4*(Real.cos (Real.pi/n))^2≤Matrix.trace (A*B*A⁻¹*B⁻¹).val:=by
    by_contra hh
    obtain ⟨r,hr,K,hKH,hTK,halt⟩:=
      _root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.ellipticTrace_failed_least_bound_triangle_signatures
        P A B hA hlA hAH hBH hNE n hn horder (lt_of_not_ge hh)
    exact hNo (elliptic_triangle_signature_profile P.asFuchsianDisc
      ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,hAH⟩
      hA n r hn hr (by simpa only [Subgroup.orderOf_mk] using horder) K hKH hTK halt)
  have hcos:=elliptic_order_cos_ge_half n hn
  have hthree:3≤Matrix.trace (A*B*A⁻¹*B⁻¹).val:=by
    nlinarith [sq_nonneg (Real.cos (Real.pi/n)-1/2)]
  have htr:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA
  have htrace:(Matrix.trace A.val)^2=4*(Real.cos (Real.pi/n))^2:=by
    have h:=hlA.squaredTrace_order
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_squaredTrace,horder] at h
    exact Complex.ofReal_injective h
  refine ⟨hbound,hthree,?_⟩
  rw [abs_of_neg (by linarith : (Matrix.trace A.val)^2-4<0),
    abs_of_nonneg (by linarith : 0≤Matrix.trace (A*B*A⁻¹*B⁻¹).val-2)]
  linarith

/--
on the actual original Fuchsian disc, with
its exact rotation hypothesis and actual whole-group triangle exclusions.
-/
theorem fuchsian_leastRotation_commutatorTrace_and_jorgensenDefect_lower_bounds {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) (g f:H) (hg:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic g.val)
    (hgleast:HasLeastEllipticRotation g.val) (n:ℕ) (hn:3≤n) (horder:orderOf g.val=n)
    (hNE:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({g.val,f.val}:Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (hNo:¬IsEllipticTraceTriangleException D n) :
    2+4*(Real.cos (Real.pi/n))^2≤(_root_.LowDimensionalTopology.Geometry.Mobius.mobiusCommutatorTrace f.val g.val).re ∧
      3≤(_root_.LowDimensionalTopology.Geometry.Mobius.mobiusCommutatorTrace f.val g.val).re ∧
      4≤‖_root_.LowDimensionalTopology.Geometry.Mobius.mobiusSquaredTrace g.val-4‖+‖_root_.LowDimensionalTopology.Geometry.Mobius.mobiusCommutatorTrace f.val g.val-2‖ := by
  let A:=D.normalizedLift g
  let B:=D.normalizedLift f
  let q:=D.halfPlaneNormalizer
  let P:HalfPlaneFuchsianGroup D.normalizedGroup:=
    ⟨fun k=>D.normalizedGroup_preserves_halfPlane k.val k.property,D.normalizedGroup_discrete⟩
  have hA:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A):=by
    rw [D.normalizedLift_spec]
    exact (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusElliptic_conjugation g.val q).mpr hg
  have hlA:HasLeastEllipticRotation (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A):=by
    rw [D.normalizedLift_spec]
    exact (hasLeastEllipticRotation_isConj (isConj_iff.mpr ⟨q,rfl⟩)).mp hgleast
  have hmem (k:H):_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (D.normalizedLift k)∈D.normalizedGroup:=by
    rw [D.normalizedLift_spec]
    exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff _ _
      _).mpr ⟨k.val,k.property,rfl⟩
  have horderA:orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)=n:=by
    rw [D.normalizedLift_spec]
    exact ((MulAut.conj q).orderOf_eq g.val).trans horder
  have hNEA:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)):=by
    have h:=hNE.conjugation q
    rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensen_generated_conjugation] at h
    rwa [←D.normalizedLift_spec g,←D.normalizedLift_spec f] at h
  have hNoA:¬IsEllipticTraceTriangleException P.asFuchsianDisc n:=by
    rintro ⟨a,b,c,ha,hab,hc,hdiv,hSig,hcase⟩
    apply hNo
    refine ⟨a,b,c,ha,hab,hc,hdiv,?_,hcase⟩
    exact cofinite_signature_of_whole_disc_model D P.asFuchsianDisc q rfl
      D.halfPlaneNormalizer_image 0 0 [a,b,c] hSig
  have h:=_root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.elliptic_trace_bounds_outside_triangle_exceptions
    P A B hA hlA (hmem g) (hmem f) hNEA n hn horderA hNoA
  have hswap:Matrix.trace (B*A*B⁻¹*A⁻¹).val=Matrix.trace (A*B*A⁻¹*B⁻¹).val:=by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_commutator_trace,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_commutator_trace]
    have hp:Matrix.trace (B*A).val=Matrix.trace (A*B).val:=Matrix.trace_mul_comm B.val A.val
    rw [hp];ring
  have hcomm:_root_.LowDimensionalTopology.Geometry.Mobius.mobiusCommutatorTrace f.val g.val=((Matrix.trace (A*B*A⁻¹*B⁻¹).val:ℝ):ℂ):=by
    rw [←_root_.LowDimensionalTopology.Geometry.DiscreteGroups.ellipticFree_commutatorTrace_conjugation f.val g.val q,
      ←D.normalizedLift_spec f,←D.normalizedLift_spec g,realSLMobius_commutatorTrace,hswap]
  have htrace:_root_.LowDimensionalTopology.Geometry.Mobius.mobiusSquaredTrace g.val=((Matrix.trace A.val)^2:ℝ):=by
    rw [←_root_.LowDimensionalTopology.Geometry.Mobius.mobiusSquaredTrace_conjugation g.val q,←D.normalizedLift_spec
      g,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_squaredTrace]
  refine ⟨by simpa only [hcomm,Complex.ofReal_re] using h.1,
    by simpa only [hcomm,Complex.ofReal_re] using h.2.1,?_⟩
  rw [htrace,hcomm]
  simpa only [←Complex.ofReal_ofNat,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using h.2.2

/-- The literal two-generator formulation. -/
theorem leastRotation_commutatorTrace_and_jorgensenDefect_lower_bounds (f
  g:_root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (D:FuchsianDisc (Subgroup.closure ({f,g}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (hg:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic g) (hgleast:HasLeastEllipticRotation g)
    (n:ℕ) (hn:3≤n) (horder:orderOf g=n)
    (hNE:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({f,g}:Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (hNo:¬IsEllipticTraceTriangleException D n) :
    2+4*(Real.cos (Real.pi/n))^2≤(_root_.LowDimensionalTopology.Geometry.Mobius.mobiusCommutatorTrace f g).re ∧
      3≤(_root_.LowDimensionalTopology.Geometry.Mobius.mobiusCommutatorTrace f g).re ∧
      4≤‖_root_.LowDimensionalTopology.Geometry.Mobius.mobiusSquaredTrace g-4‖+‖_root_.LowDimensionalTopology.Geometry.Mobius.mobiusCommutatorTrace f g-2‖ := by
  apply fuchsian_leastRotation_commutatorTrace_and_jorgensenDefect_lower_bounds D
    ⟨g,Subgroup.subset_closure (by simp)⟩ ⟨f,Subgroup.subset_closure (by simp)⟩
    hg hgleast n hn horder
  · rwa [Set.pair_comm]
  · exact hNo

end LowDimensionalTopology.Geometry.Fuchsian
