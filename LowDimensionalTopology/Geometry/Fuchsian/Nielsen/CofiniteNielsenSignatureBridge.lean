/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Nielsen.QuotientSignature
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.Area.OriginalSignatureArea
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
local instance cofiniteNielsenBridgeSphereMeasurable : MeasurableSpace Mobius.ExtendedComplex := borel Mobius.ExtendedComplex
local instance cofiniteNielsenBridgeSphereBorel : BorelSpace Mobius.ExtendedComplex := ⟨rfl⟩

set_option maxHeartbeats 0 in
/-- A first-kind original group has no genuine boundary-hyperbolic cyclic class. -/
theorem firstKind_boundaryHyperbolicClasses_card_zero
    {H : Subgroup Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (hfirst : P.asFuchsianDisc.IsFirstKind) :
    Nat.card (FuchsianBoundaryHyperbolicCyclicConjugacyClasses P.asFuchsianDisc) = 0 := by
  have hEmpty : IsEmpty (fuchsianMaximalBoundaryHyperbolicCyclicSubgroups P.asFuchsianDisc) := by
    refine ⟨?_⟩
    intro K
    obtain ⟨f, _hfK, hf⟩ := K.property.2
    obtain ⟨I, hI, _hInv⟩ := hf.2
    obtain ⟨p, hp, _hIp⟩ := hI.1
    exact hp.2 (hfirst.symm ▸ hp.1)
  let := hEmpty
  have hQuotientEmpty : IsEmpty
      (FuchsianBoundaryHyperbolicCyclicConjugacyClasses P.asFuchsianDisc) :=
    ⟨fun q => Quotient.inductionOn q (fun a => isEmptyElim a)⟩
  exact @Nat.card_of_isEmpty _ hQuotientEmpty

set_option maxHeartbeats 0 in
/-- The genuine cofinite completion genus agrees with the genuine Nielsen
signature genus. This supplies the actual general-signature consumer for the
cofinite realization branch, with zero true boundary-hyperbolic ends. -/
theorem HasCofiniteFuchsianSignature.toNielsen
    {H : Subgroup Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    (hfirst : P.asFuchsianDisc.IsFirstKind) (hFG : H.FG)
    {g : ℕ} {orders : List ℕ} {cusps : ℕ}
    (hSig : HasCofiniteFuchsianSignature P.asFuchsianDisc g orders cusps) :
    HasNielsenFuchsianSignature P (P.asFuchsianDisc.firstKind_nonElementary hfirst) hFG
      g orders cusps 0 := by
  let hNE := P.asFuchsianDisc.firstKind_nonElementary hfirst
  obtain ⟨k, os, p, t, hN⟩ := finitelyGenerated_hasNielsenFuchsianSignature P hNE hFG
  have hNsave := hN
  obtain ⟨w, hw, hwN, J, hc, hv, n, S, hr, hg, ho, hp, ht⟩ := hN
  have hCore : fuchsianNielsenCore P hNE = univ := by
    ext x
    simp only [mem_univ, iff_true]
    change (x : Mobius.ExtendedComplex) ∈ P.asFuchsianDisc.nielsenRegion hNE
    rw [P.asFuchsianDisc.nielsenRegion_firstKind hNE hfirst]
    exact x.property
  have hpeq : p = cusps := hp.trans hSig.cuspCount.symm
  have htzero : t = 0 := ht.trans (firstKind_boundaryHyperbolicClasses_card_zero P hfirst)
  have hsum :
      (os.map (fun m : ℕ => 1 - 1 / (m : ℝ))).sum =
        (orders.map (fun m : ℕ => 1 - 1 / (m : ℝ))).sum := by
    let := hSig.ellipticClassesFinite
    exact ((ho.trans hSig.ellipticOrders.symm).map (fun m : ℕ => 1 - 1 / (m : ℝ))).sum_eq
  have hNarea := hNsave.area (dirichletDomain_fundamental P w hw)
  simp only [fuchsianNielsenCoreArea, hCore, inter_univ, htzero, hpeq,
    Nat.cast_zero, add_zero] at hNarea
  rw [hsum] at hNarea
  have hD : DiscreteGroups.Action.IsFundamentalDomain H
      (fuchsianGeometricDomain P.asFuchsianDisc).carrier (geometricModelArea P.asFuchsianDisc)
      (dirichletDomain P w) := by
    rw [geometricModelArea_asUnitDisc]
    exact dirichletDomain_fundamental P w hw
  have hCarea := cofinite_area_eq_two_pi_mul_signatureDeficit P.asFuchsianDisc hfirst hFG
    (dirichletDomain P w) hD g cusps orders hSig
  rw [geometricModelArea_asUnitDisc] at hCarea
  have hDelta := mul_left_cancel₀ (by positivity : (2 : ℝ) * Real.pi ≠ 0)
    (hNarea.symm.trans hCarea)
  have hkgR : (k : ℝ) = (g : ℝ) := by linarith only [hDelta]
  have hkg : k = g := by exact_mod_cast hkgR
  subst k
  refine ⟨w, hw, hwN, J, hc, hv, n, S, hr, hg, ?_, hSig.cuspCount, ?_⟩
  · exact hSig.ellipticOrders
  · exact (firstKind_boundaryHyperbolicClasses_card_zero P hfirst).symm

end LowDimensionalTopology.Geometry.Fuchsian
