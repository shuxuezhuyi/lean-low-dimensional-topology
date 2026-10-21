/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.Hecke.HeckeActualSignatures
public import LowDimensionalTopology.Geometry.Fuchsian.Generation.TwoParabolics.ParabolicWholeDiscModels
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane OnePoint MatrixGroups
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

/-- The true two-ideal triangle quotient has the original elliptic order and two actual cusps. -/
theorem twoIdeal_actual_signature (p:ℕ) (hp:2≤p)
    (P:HalfPlaneFuchsianGroup (closedTriangleMobiusGroup (twoIdealIntegralTriangle p hp))) :
    HasCofiniteFuchsianSignature P.asFuchsianDisc 0 [p] 2 := by
  obtain ⟨ha,hb,hc⟩:=twoIdealIntegralTriangle_angles p hp
  exact closedTriangle_actual_signature_two_ideal _ p hp ha hb hc P

/-- A genuine whole-disc model transports its actual quotient signature back to the original group. -/
theorem cofinite_signature_of_whole_disc_model
    {H K:Subgroup Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) (E:FuchsianDisc K) (q:Mobius.complexMobiusGroup)
    (hG:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H=K)
    (hE:q.val '' D.carrier=E.carrier)
    (genus cusps:ℕ) (orders:List ℕ)
    (h:HasCofiniteFuchsianSignature E genus orders cusps) :
    HasCofiniteFuchsianSignature D genus orders cusps := by
  apply cofinite_signature_of_conjugate_group E D q⁻¹ ?_ ?_ genus cusps orders h
  · rw [←hG,_root_.LowDimensionalTopology.Geometry.Hyperbolic.subgroupConjugate_inv_cancel]
  · change q.val.symm '' E.carrier=D.carrier
    rw [←hE]
    exact q.val.symm_image_image D.carrier

/-- The complete original-disc alternatives, including genuine topological signatures. -/
theorem parabolic_pair_commutatorTrace_large_or_exceptional_signature
    (f g:Mobius.complexMobiusGroup)
    (D:FuchsianDisc (Subgroup.closure ({f,g}:Set Mobius.complexMobiusGroup)))
    (hf:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f)
    (hg:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic g)
    (hne:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({f,g}:Set Mobius.complexMobiusGroup))) :
    18≤(_root_.LowDimensionalTopology.Geometry.Mobius.mobiusCommutatorTrace f g).re ∨
      (∃n:ℕ,3≤n ∧ Odd n ∧
        _root_.LowDimensionalTopology.Geometry.Mobius.mobiusCommutatorTrace f g=((2+16*(Real.cos (Real.pi/(n:ℝ)))^4:ℝ):ℂ) ∧
        HasCofiniteFuchsianSignature D 0 [2,n] 1) ∨
      (∃p:ℕ,2≤p ∧
        _root_.LowDimensionalTopology.Geometry.Mobius.mobiusCommutatorTrace f g=((2+16*(Real.cos (Real.pi/(2*(p:ℝ))))^4:ℝ):ℂ) ∧
        HasCofiniteFuchsianSignature D 0 [p] 2) := by
  by_cases hbig:18≤(_root_.LowDimensionalTopology.Geometry.Mobius.mobiusCommutatorTrace f g).re
  · exact Or.inl hbig
  obtain ⟨q,hq,hmodel⟩:=fuchsian_two_parabolic_whole_disc_models f g D hf hg hne (lt_of_not_ge hbig)
  right
  rcases hmodel with ⟨n,hn,hodd,hG,htrace⟩|⟨p,hp,hG,htrace⟩
  · left
    refine ⟨n,hn,hodd,htrace,?_⟩
    exact cofinite_signature_of_whole_disc_model D
      (unitHeckeMobiusData n (by exact_mod_cast hn)).asFuchsianDisc q hG hq
      0 1 [2,n] (unitHecke_actual_signature n hn)
  · right
    obtain ⟨ha,hb,hc⟩:=twoIdealIntegralTriangle_angles p hp
    let P:=closedTriangleMobiusData (twoIdealIntegralTriangle p hp)
      (Or.inr ⟨p,hp,ha⟩) (Or.inl hb) (Or.inl hc)
    exact ⟨p,hp,htrace,cofinite_signature_of_whole_disc_model D P.asFuchsianDisc q hG hq
      0 2 [p] (twoIdeal_actual_signature p hp P)⟩

/-- The small-trace branch has its genuine original quotient signature. -/
theorem fuchsian_one_parabolic_small_trace_actual_signature
    (f g:Mobius.complexMobiusGroup)
    (D:FuchsianDisc (Subgroup.closure ({f,g}:Set Mobius.complexMobiusGroup)))
    (hf:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f)
    (hne:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({f,g}:Set Mobius.complexMobiusGroup)))
    (hsmall:(_root_.LowDimensionalTopology.Geometry.Mobius.mobiusCommutatorTrace f g).re<6) :
    ∃n:ℕ,3≤n ∧
      _root_.LowDimensionalTopology.Geometry.Mobius.mobiusCommutatorTrace f g=((4+2*Real.cos (2*Real.pi/(n:ℝ)):ℝ):ℂ) ∧
      HasCofiniteFuchsianSignature D 0 [2,n] 1 := by
  obtain ⟨q,hq,n,hn,hG,htrace⟩:=fuchsian_one_parabolic_whole_disc_model f g D hf hne hsmall
  exact ⟨n,hn,htrace,cofinite_signature_of_whole_disc_model D
    (unitHeckeMobiusData n (by exact_mod_cast hn)).asFuchsianDisc q hG hq
    0 1 [2,n] (unitHecke_actual_signature n hn)⟩

/-- All three original-disc conclusions, with the actual real trace and quotient. -/
theorem parabolic_commutatorTrace_lower_bound_small_trace_signature_and_elliptic
    (f g:Mobius.complexMobiusGroup)
    (D:FuchsianDisc (Subgroup.closure ({f,g}:Set Mobius.complexMobiusGroup)))
    (hf:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f)
    (hne:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({f,g}:Set Mobius.complexMobiusGroup))) :
    ∃t:ℝ,_root_.LowDimensionalTopology.Geometry.Mobius.mobiusCommutatorTrace f g=(t:ℂ) ∧3≤t ∧
      (t<6→∃n:ℕ,3≤n ∧t=4+2*Real.cos (2*Real.pi/(n:ℝ)) ∧
        HasCofiniteFuchsianSignature D 0 [2,n] 1) ∧
      (t<18→∃u∈Subgroup.closure ({f,g}:Set Mobius.complexMobiusGroup),_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic u) := by
  obtain ⟨_q,A,B,_hq,_hA,_hB,_hG,htrace⟩:=fuchsian_pair_real_lifts_with_whole_disc f g D
  refine ⟨(_root_.LowDimensionalTopology.Geometry.Mobius.mobiusCommutatorTrace f g).re,?_,fuchsian_parabolic_commutator_trace_ge_three f g D hf hne,?_,?_⟩
  · rw [htrace,Complex.ofReal_re]
  · intro hsmall
    obtain ⟨n,hn,htr,hSig⟩:=fuchsian_one_parabolic_small_trace_actual_signature f g D hf hne hsmall
    exact ⟨n,hn,by rw [htr,Complex.ofReal_re],hSig⟩
  · exact fuchsian_parabolic_small_trace_has_elliptic f g D hf hne

end LowDimensionalTopology.Geometry.Fuchsian
