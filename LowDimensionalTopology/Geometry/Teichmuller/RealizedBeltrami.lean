module

public import LowDimensionalTopology.Geometry.Teichmuller.BeltramiBanach
public import LowDimensionalTopology.Geometry.Teichmuller.BeltramiCompactBounds
public import LowDimensionalTopology.Geometry.Teichmuller.BeltramiConformalEquivalence
public import Mathlib.Topology.Maps.Basic

/-!
# Realized smooth Beltrami coefficients and their Teichmüller projection

For a fixed closed Riemann surface, the coefficient domain is the actual range
of smooth orientation-preserving markings with variable closed target surfaces.
It inherits the uniform-norm subspace topology from the genuine continuous
Beltrami Banach space. The range is proved to lie in the open unit ball; no
realization theorem for every point of that ball is asserted.

Two markings with the same actual coefficient differ by an actual biholomorphic
target change, so their Teichmüller classes agree. This gives a well-defined
surjection beta from realized coefficients to the native marked-surface quotient.
The topology introduced below is precisely the coinduced topology of this map.
Comparison with any metric topology and identification of its fibers with a
Diff0 action are separate mathematical statements.

The coefficient comparison uses the native pointwise results derived from
Wu Xiaobin's LiZhongQC, fixed source commit
1c0d5473c020b66ed5106331a38a61536760b9b2, as acknowledged in the imported modules.
-/

@[expose] public section

noncomputable section

open Set Topology

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces

universe u v w

namespace MarkedRiemannSurface

variable {X : Type u} [TopologicalSpace X] {R : ClosedRiemannSurface X}

/-- The actual continuous tensor of a given marked complex surface. -/
def beltramiTensor (M : MarkedRiemannSurface.{u, v} R) :
    BeltramiDifferential R.toRiemannAtlas :=
  M.marking.beltrami M.orientation_preserving

/-- Regard the realized tensor as an element of the genuine uniform Banach space. -/
def beltramiCoefficient (M : MarkedRiemannSurface.{u, v} R) :
    BeltramiDifferential.BanachSpace R.toRiemannAtlas := by
  let := R.compactSpace
  exact BeltramiDifferential.ofTensor M.beltramiTensor

/-- Changing the presentation to the compact Banach model does not change equality. -/
theorem beltramiCoefficient_eq_iff (M N : MarkedRiemannSurface.{u, v} R) :
    M.beltramiCoefficient = N.beltramiCoefficient ↔ M.beltramiTensor = N.beltramiTensor := by
  let := R.compactSpace
  constructor
  · intro h
    have ht := congrArg (BeltramiDifferential.toTensor (A := R.toRiemannAtlas)) h
    simpa only [beltramiCoefficient, BeltramiDifferential.toTensor_ofTensor] using ht
  · intro h
    change BeltramiDifferential.ofTensor M.beltramiTensor =
      BeltramiDifferential.ofTensor N.beltramiTensor
    exact congrArg BeltramiDifferential.ofTensor h

/-- Compactness and the actual positive Jacobian give a strict uniform bound. -/
theorem beltramiCoefficient_norm_lt_one (M : MarkedRiemannSurface.{u, v} R) :
    ‖M.beltramiCoefficient‖ < 1 := by
  let := R.compactSpace
  apply (BeltramiDifferential.norm_lt_one_iff M.beltramiCoefficient).2
  intro e z
  simpa only [beltramiCoefficient, BeltramiDifferential.toTensor_ofTensor,
    beltramiTensor] using M.marking.beltrami_coeff_norm_lt_one M.orientation_preserving e z

/-- Equal literal coefficients imply native Teichmüller equivalence, witnessed
by an actual analytic target homeomorphism and a constant marking homotopy. -/
theorem equivalent_of_beltramiCoefficient_eq
    {M N : MarkedRiemannSurface.{u, v} R}
    (h : M.beltramiCoefficient = N.beltramiCoefficient) : Equivalent M N := by
  have ht : M.marking.beltrami M.orientation_preserving =
      N.marking.beltrami N.orientation_preserving :=
    (M.beltramiCoefficient_eq_iff N).1 h
  obtain ⟨e, he, _heInv, hmark⟩ :=
    (M.marking.beltrami_eq_iff_exists_analytic_homeomorph N.marking
      M.orientation_preserving N.orientation_preserving).1 ht
  refine ⟨e, he, ?_⟩
  have hmaps : (_root_.toContinuousMap e).comp M.markingMap = N.markingMap := by
    ext x
    exact hmark x
  rw [hmaps]

end MarkedRiemannSurface

variable {X : Type u} [TopologicalSpace X]

/-- The actual smooth-realization range inside the continuous Beltrami Banach space.
The target-carrier universe is explicit, just as in native marked surfaces. -/
def realizedBeltramiSet (R : ClosedRiemannSurface X) :
    Set (BeltramiDifferential.BanachSpace R.toRiemannAtlas) :=
  Set.range (MarkedRiemannSurface.beltramiCoefficient (R := R) :
    MarkedRiemannSurface.{u, v} R → BeltramiDifferential.BanachSpace R.toRiemannAtlas)

/-- The book's realized coefficient domain, with its actual uniform-norm subspace
 topology. It is a range subtype, rather than the whole open unit ball. -/
abbrev RealizedBeltramiCoefficients (R : ClosedRiemannSurface X) :=
  ↥(realizedBeltramiSet.{u, v} R)

namespace RealizedBeltramiCoefficients

variable {R : ClosedRiemannSurface X}

/-- The realized coefficient of a particular actual marking. -/
def ofMarked (M : MarkedRiemannSurface.{u, v} R) : RealizedBeltramiCoefficients.{u, v} R :=
  ⟨M.beltramiCoefficient, M, rfl⟩

/-- Every element is strictly inside the Banach unit ball because it is realized. -/
theorem norm_lt_one (μ : RealizedBeltramiCoefficients.{u, v} R) : ‖μ.val‖ < 1 := by
  obtain ⟨M, hM⟩ := μ.property
  rw [← hM]
  exact M.beltramiCoefficient_norm_lt_one

/-- Select one actual marking realizing the given coefficient. -/
def representative (μ : RealizedBeltramiCoefficients.{u, v} R) :
    MarkedRiemannSurface.{u, v} R :=
  μ.property.choose

/-- The selected marking realizes precisely the original coefficient. -/
theorem representative_coefficient (μ : RealizedBeltramiCoefficients.{u, v} R) :
    μ.representative.beltramiCoefficient = μ.val :=
  μ.property.choose_spec

/-- The natural projection from realized coefficients to native Teichmüller classes. -/
def beta (μ : RealizedBeltramiCoefficients.{u, v} R) : TeichmullerSpace.{u, v} R :=
  TeichmullerSpace.mk μ.representative

/-- The projection is independent of the chosen actual realizing marking. -/
theorem beta_eq_mk_of_coefficient
    (μ : RealizedBeltramiCoefficients.{u, v} R) (M : MarkedRiemannSurface.{u, v} R)
    (hM : M.beltramiCoefficient = μ.val) : beta μ = TeichmullerSpace.mk M := by
  apply (TeichmullerSpace.mk_eq_mk_iff _ _).2
  apply MarkedRiemannSurface.equivalent_of_beltramiCoefficient_eq
  exact μ.representative_coefficient.trans hM.symm

/-- Computing the projection on the coefficient of any actual marking. -/
@[simp]
theorem beta_ofMarked (M : MarkedRiemannSurface.{u, v} R) :
    beta (ofMarked M) = TeichmullerSpace.mk M :=
  beta_eq_mk_of_coefficient (ofMarked M) M rfl

/-- Every native Teichmüller point has a realized smooth coefficient above it. -/
theorem beta_surjective : Function.Surjective
    (beta : RealizedBeltramiCoefficients.{u, v} R → TeichmullerSpace.{u, v} R) := by
  intro p
  induction p using Quotient.inductionOn with
  | h M => exact ⟨ofMarked M, beta_ofMarked M⟩

/-- Fibers over coefficients of actual markings are exactly native marking equivalence.
This does not replace the distinct literal-coefficient equality relation. -/
theorem beta_ofMarked_eq_iff (M N : MarkedRiemannSurface.{u, v} R) :
    beta (ofMarked M) = beta (ofMarked N) ↔ MarkedRiemannSurface.Equivalent M N := by
  rw [beta_ofMarked, beta_ofMarked]
  exact TeichmullerSpace.mk_eq_mk_iff M N

end RealizedBeltramiCoefficients

namespace TeichmullerSpace

/-- The quotient topology from the uniform-norm space of actually realized
smooth coefficients. The displayed projection is concrete and already surjective. -/
@[instance_reducible]
def beltramiTopology (R : ClosedRiemannSurface X) :
    TopologicalSpace (TeichmullerSpace.{u, v} R) :=
  TopologicalSpace.coinduced
    (RealizedBeltramiCoefficients.beta (R := R) :
      RealizedBeltramiCoefficients.{u, v} R → TeichmullerSpace.{u, v} R)
    inferInstance

/-- The native topology is the realized-coefficient quotient topology. -/
instance instTopologicalSpace (R : ClosedRiemannSurface X) :
    TopologicalSpace (TeichmullerSpace.{u, v} R) :=
  beltramiTopology R

end TeichmullerSpace

namespace RealizedBeltramiCoefficients

variable {R : ClosedRiemannSurface X}

/-- The actual coefficient projection is a quotient map for the defined topology. -/
theorem isQuotientMap_beta : Topology.IsQuotientMap
    (beta : RealizedBeltramiCoefficients.{u, v} R → TeichmullerSpace.{u, v} R) :=
  ⟨⟨rfl⟩, beta_surjective⟩

/-- The realized-coefficient projection is continuous in the uniform-norm topology. -/
@[continuity]
theorem continuous_beta : Continuous
    (beta : RealizedBeltramiCoefficients.{u, v} R → TeichmullerSpace.{u, v} R) :=
  isQuotientMap_beta.continuous

/-- Openness in the defined Teichmüller topology is tested on actual coefficient preimages. -/
theorem isOpen_iff_beta_preimage (s : Set (TeichmullerSpace.{u, v} R)) :
    IsOpen s ↔ IsOpen ((beta : RealizedBeltramiCoefficients.{u, v} R →
      TeichmullerSpace.{u, v} R) ⁻¹' s) :=
  isQuotientMap_beta.isCoinducing.isOpen_preimage.symm

/-- The universal property of this concrete coefficient quotient topology. -/
theorem continuous_from_teichmuller_iff
    {Y : Type w} [TopologicalSpace Y] (f : TeichmullerSpace.{u, v} R → Y) :
    Continuous f ↔ Continuous (f ∘ (beta : RealizedBeltramiCoefficients.{u, v} R →
      TeichmullerSpace.{u, v} R)) :=
  isQuotientMap_beta.continuous_iff

end RealizedBeltramiCoefficients

end LowDimensionalTopology.Geometry.Teichmuller
