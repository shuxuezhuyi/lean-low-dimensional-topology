/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Nielsen.NielsenSharpArea
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Topology
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Polygon

/-- A genuine signature has positive deficit, from the positive physical
Nielsen area of that same original group and its actual filled surface. -/
theorem HasNielsenFuchsianSignature.deficit_pos
    {H : Subgroup Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary H} {hFG : H.FG}
    {g : ℕ} {orders : List ℕ} {s t : ℕ}
    (h : HasNielsenFuchsianSignature P hNE hFG g orders s t) :
    0 < 2*(g:ℝ)-2+s+t+(orders.map (fun m : ℕ => 1-1/(m:ℝ))).sum := by
  obtain ⟨w, hw, _⟩ := exists_dirichlet_center_in_nielsenCore P hNE
  have hD := dirichletDomain_fundamental P w hw
  have hpos := ENNReal.toReal_pos
    (ne_of_gt (finitelyGenerated_nielsenCoreArea_pos P hNE hFG hD))
    (finitelyGenerated_nielsenCoreArea_ne_top P hNE hFG hD)
  rw [h.area hD] at hpos
  have hp := (mul_pos_iff_of_pos_left (show 0 < 2*Real.pi by positivity)).mp hpos
  convert hp using 1
  ring

/-- Constructing the true whole-group order/end census and physical Nielsen
area identifies the genus of the already constructed actual filled surface.
No surface genus or signature is defined by an area budget. -/
theorem hasNielsenSignature_of_actual_census_and_area
    {H : Subgroup Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary H) (hFG : H.FG)
    (g : ℕ) (orders : List ℕ) (s t : ℕ)
    [Finite (FuchsianCyclicConjugacyClasses P.asFuchsianDisc .elliptic)]
    (horders : orders.Perm (fuchsianEllipticOrderList P.asFuchsianDisc))
    (hcusps : s = Nat.card (FuchsianCyclicConjugacyClasses P.asFuchsianDisc .parabolic))
    (hboundary : t = Nat.card (FuchsianBoundaryHyperbolicCyclicConjugacyClasses P.asFuchsianDisc))
    (D : Set P.domain.carrier) (hD : IsFuchsianFundamentalDomain P D)
    (harea : (fuchsianNielsenCoreArea P hNE D).toReal =
      2*Real.pi*(2*(g:ℝ)-2+s+t+(orders.map (fun m : ℕ => 1-1/(m:ℝ))).sum)) :
    HasNielsenFuchsianSignature P hNE hFG g orders s t := by
  obtain ⟨g', orders', s', t', hsignature⟩ := finitelyGenerated_hasNielsenFuchsianSignature P hNE hFG
  have hcopy := hsignature
  obtain ⟨_w, _hw, _hwN, _J, _hc, _hv, _n, _S, _hr, _hg, ho, hs, ht⟩ := hcopy
  have heS : s' = s := hs.trans hcusps.symm
  have heT : t' = t := ht.trans hboundary.symm
  rw [heS, heT] at hsignature
  have hactual := hsignature.perm_orders (ho.trans horders.symm)
  have ha := hactual.area hD
  rw [harea] at ha
  have hgenus : (g':ℝ) = (g:ℝ) := by nlinarith [Real.pi_pos]
  have hg : g' = g := by exact_mod_cast hgenus
  exact hg ▸ hactual

end LowDimensionalTopology.Geometry.Fuchsian
