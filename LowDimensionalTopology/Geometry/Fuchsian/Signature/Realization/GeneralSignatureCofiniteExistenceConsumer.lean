/- Actual cofinite realization consumer for, 2026-10-20. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.CofinitePolygonLowerSharpness
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.RegularPolygon.RegularPolygonLowerSharpness
public import LowDimensionalTopology.Geometry.Fuchsian.Nielsen.CofiniteNielsenSignatureBridge
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Topology
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
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- Every admissible cofinite signature is realized by one actual original
group. Both genuine completed-surface signatures and an actual convex locally
finite fundamental polygon belong to that same group; no desired area or genus
is supplied to the construction. -/
theorem generalSignature_cofinite_realization_exists
    (g : ℕ) (orders : List ℕ) (s : ℕ) (horders : ∀m∈orders,2≤m)
    (hdef : 0<2*(g:ℝ)-2+(s:ℝ)+(orders.map (fun m:ℕ=>1-1/(m:ℝ))).sum) :
    ∃H:Subgroup Mobius.complexMobiusGroup,∃P:UnitDiscFuchsianGroup H,
      ∃hFG:H.FG,∃hfirst:P.asFuchsianDisc.IsFirstKind,
        HasNielsenFuchsianSignature P (P.asFuchsianDisc.firstKind_nonElementary hfirst) hFG
          g orders s 0 ∧
        HasCofiniteFuchsianSignature P.asFuchsianDisc g orders s ∧
        ∃D:Set P.domain.carrier,IsConvexFuchsianPolygon P D := by
  have finish {H:Subgroup Mobius.complexMobiusGroup} (P:UnitDiscFuchsianGroup H)
      (hFG:H.FG) (hfirst:P.asFuchsianDisc.IsFirstKind)
      (hSig:HasCofiniteFuchsianSignature P.asFuchsianDisc g orders s)
      (D:Set P.domain.carrier) (hD:IsConvexFuchsianPolygon P D) :
      ∃K:Subgroup Mobius.complexMobiusGroup,∃Q:UnitDiscFuchsianGroup K,
        ∃hFK:K.FG,∃hfirstK:Q.asFuchsianDisc.IsFirstKind,
          HasNielsenFuchsianSignature Q (Q.asFuchsianDisc.firstKind_nonElementary hfirstK) hFK
            g orders s 0 ∧
          HasCofiniteFuchsianSignature Q.asFuchsianDisc g orders s ∧
          ∃E:Set Q.domain.carrier,IsConvexFuchsianPolygon Q E :=
    ⟨H,P,hFG,hfirst,hSig.toNielsen hfirst hFG,hSig,D,hD⟩
  by_cases hs:s=0
  · subst s
    by_cases ho:orders=[]
    · subst orders
      have hg:2≤g := by
        have hh:1<(g:ℝ) := by
          norm_num only [List.map_nil,List.sum_nil,Nat.cast_zero,add_zero] at hdef
          linarith only [hdef]
        have hn:1<g := by exact_mod_cast hh
        omega
      obtain ⟨hSig,hFG,hfirst,hD,_hSelf,_hCount⟩:=regularPolygon_lower_side_bound_attained g hg
      exact finish (regularPolygonDiscData g hg) hFG hfirst hSig (regularPolygonDiscDomain g hg) hD
    · obtain ⟨H,P,hFG,hfirst,hSig,D,hD,_hCount⟩:=
        cofiniteConstruction_nonempty_finite_lower_side_bound_attained g orders ho horders
          (by simpa only [Nat.cast_zero,add_zero] using hdef)
      exact finish P hFG hfirst hSig D hD
  · obtain ⟨H,P,hFG,hfirst,hSig,D,hD,_hCount⟩:=
      cofiniteConstruction_cusped_lower_side_bound_attained g orders s horders (by omega) hdef
    exact finish P hFG hfirst hSig D hD

/-- A signature with zero boundary count and positive deficit is realized by a finitely
generated first-kind unit-disc Fuchsian group. -/
theorem FuchsianSignature.cofinite_realization_exists (σ:FuchsianSignature)
    (hboundary:σ.boundaryHyperbolicEnds=0) (hdef:0<σ.deficit) :
    ∃H:Subgroup Mobius.complexMobiusGroup,∃P:UnitDiscFuchsianGroup H,
      ∃hFG:H.FG,∃hfirst:P.asFuchsianDisc.IsFirstKind,
        HasNielsenFuchsianSignature P (P.asFuchsianDisc.firstKind_nonElementary hfirst) hFG
          σ.genus σ.ellipticOrders σ.parabolicEnds σ.boundaryHyperbolicEnds ∧
        HasCofiniteFuchsianSignature P.asFuchsianDisc σ.genus σ.ellipticOrders σ.parabolicEnds ∧
        ∃D:Set P.domain.carrier,IsConvexFuchsianPolygon P D := by
  rw [hboundary]
  apply generalSignature_cofinite_realization_exists σ.genus σ.ellipticOrders σ.parabolicEnds
    σ.ellipticOrders_two_le
  simpa only [_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianSignature.deficit, hboundary, Nat.cast_zero,
    add_zero] using hdef

end LowDimensionalTopology.Geometry.Fuchsian
