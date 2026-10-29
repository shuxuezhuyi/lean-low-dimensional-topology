module

public import LowDimensionalTopology.Geometry.Teichmuller.CompactGenusModuli
public import LowDimensionalTopology.Geometry.Teichmuller.Moduli
public import LowDimensionalTopology.Geometry.Teichmuller.NativeTeichmullerMetric
public import LowDimensionalTopology.Geometry.Surfaces.Topology.Genus.HandleGenusBridge
public import LowDimensionalTopology.Unproved.Teichmuller.PositiveSmoothMarkability
public import Mathlib.Topology.Maps.Basic

/-!
# The QC quotient topology on the full compact-genus moduli set

Forgetting a native marking retains the actual target surface. The positive
smooth marking premise supplies surjectivity onto every original compact
target of the given genus. The fibers are exactly the existing mapping
class orbits. The topology is explicitly coinduced from the native full-log
QC metric for the one fixed reference surface.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces

variable {X : Type} [TopologicalSpace X] {R : ClosedRiemannSurface X} {g : ℕ}

namespace MarkedRiemannSurface

/-- The unchanged target of a marking, with the reference genus transported
through its actual underlying homeomorphism. -/
def toCompactGenusSurface (hgenus : R.HasGenus g)
    (M : MarkedRiemannSurface.{0, 0} R) : CompactGenusSurface g where
  carrier := M.carrier
  topology := M.topology
  surface := M.surface
  hasGenus := by
    obtain ⟨e⟩ := hgenus
    exact ⟨M.marking.toHomeomorph.symm.trans e⟩

end MarkedRiemannSurface

namespace TeichmullerSpace

/-- Forget the marking into the biholomorphic quotient of all original
compact targets of the reference genus. -/
def toCompactGenusModuli (R : ClosedRiemannSurface X) (hgenus : R.HasGenus g) :
    TeichmullerSpace.{0, 0} R → CompactGenusModuliSpace g :=
  Quotient.lift
    (fun M => CompactGenusModuliSpace.mk (M.toCompactGenusSurface hgenus)) (by
      intro M N hMN
      obtain ⟨f, hf, _⟩ := hMN
      apply (CompactGenusModuliSpace.mk_eq_mk_iff _ _).2
      exact ⟨f, hf, f.bijective⟩)

@[simp]
theorem toCompactGenusModuli_mk (hgenus : R.HasGenus g)
    (M : MarkedRiemannSurface.{0, 0} R) :
    toCompactGenusModuli R hgenus (mk M) =
      CompactGenusModuliSpace.mk (M.toCompactGenusSurface hgenus) := rfl

/-- The independent positive smooth marking premise reaches every actual
compact target, not merely those already packaged with a marking. -/
theorem toCompactGenusModuli_surjective (R : ClosedRiemannSurface X)
    (hgenus : R.HasGenus g)
    (hmark : LowDimensionalTopology.Unproved.Teichmuller.PositiveSmoothMarkability R) :
    Function.Surjective (toCompactGenusModuli R hgenus) := by
  intro q
  refine Quotient.inductionOn q ?_
  intro S
  obtain ⟨F, hF⟩ := hmark S.surface g hgenus S.hasGenus
  let M : MarkedRiemannSurface.{0, 0} R :=
    { carrier := S.carrier
      topology := S.topology
      surface := S.surface
      marking := F
      orientation_preserving := hF }
  refine ⟨mk M, ?_⟩
  apply (CompactGenusModuliSpace.mk_eq_mk_iff _ S).2
  exact RiemannConformallyEquivalent.refl S.surface.toRiemannSurface

/-- The full target quotient has exactly the same fibers as the existing
forget-marking map, before any markability premise is used. -/
theorem toCompactGenusModuli_eq_iff_forgetMarking_eq (hgenus : R.HasGenus g)
    (p q : TeichmullerSpace.{0, 0} R) :
    toCompactGenusModuli R hgenus p = toCompactGenusModuli R hgenus q ↔
      forgetMarking p = forgetMarking q := by
  refine Quotient.inductionOn₂ p q ?_
  intro M N
  change toCompactGenusModuli R hgenus (mk M) =
      toCompactGenusModuli R hgenus (mk N) ↔
    forgetMarking (mk M) = forgetMarking (mk N)
  rw [toCompactGenusModuli_mk, toCompactGenusModuli_mk,
    CompactGenusModuliSpace.mk_eq_mk_iff, forgetMarking_mk, forgetMarking_mk,
    ModuliSpace.mk_eq_mk_iff]
  constructor
  · rintro ⟨f, hf, hbij⟩
    exact ⟨hf.toHomeomorph hbij, hf⟩
  · rintro ⟨f, hf⟩
    exact ⟨f, hf, f.bijective⟩

/-- The actual fibers of the full target projection are precisely the full
mapping class group orbits on the original native Teichmüller space. -/
theorem toCompactGenusModuli_eq_iff_exists_mappingClass (hgenus : R.HasGenus g)
    (p q : TeichmullerSpace.{0, 0} R) :
    toCompactGenusModuli R hgenus p = toCompactGenusModuli R hgenus q ↔
      ∃ γ : MappingClassGroup R, γ • p = q :=
  (toCompactGenusModuli_eq_iff_forgetMarking_eq hgenus p q).trans
    (forgetMarking_eq_iff_exists_mappingClass p q)

end TeichmullerSpace

namespace CompactGenusModuliSpace

/-- The topology coinduced by the actual full-log native QC metric and the
actual target projection, for this fixed reference surface. -/
@[instance_reducible] def qcTopology (R : ClosedRiemannSurface X) (hg : 1 < g) (hgenus : R.HasGenus g) :
    TopologicalSpace (CompactGenusModuliSpace g) :=
  letI : MetricSpace (TeichmullerSpace.{0, 0} R) :=
    TeichmullerSpace.fromQCMetricSpace R hg hgenus (canonicalHandleGroupPresentation g)
  TopologicalSpace.coinduced (TeichmullerSpace.toCompactGenusModuli R hgenus) inferInstance

/-- With the old marking premise explicit, the full target projection is a
genuine quotient map for the displayed native QC topology. -/
theorem isQuotientMap_toCompactGenusModuli (R : ClosedRiemannSurface X)
    (hg : 1 < g) (hgenus : R.HasGenus g)
    (hmark : LowDimensionalTopology.Unproved.Teichmuller.PositiveSmoothMarkability R) :
    letI : MetricSpace (TeichmullerSpace.{0, 0} R) :=
      TeichmullerSpace.fromQCMetricSpace R hg hgenus (canonicalHandleGroupPresentation g)
    letI : TopologicalSpace (CompactGenusModuliSpace g) := qcTopology R hg hgenus
    Topology.IsQuotientMap (TeichmullerSpace.toCompactGenusModuli R hgenus) := by
  let : MetricSpace (TeichmullerSpace.{0, 0} R) :=
    TeichmullerSpace.fromQCMetricSpace R hg hgenus (canonicalHandleGroupPresentation g)
  let : TopologicalSpace (CompactGenusModuliSpace g) := qcTopology R hg hgenus
  exact
    { eq_coinduced := rfl
      surjective := TeichmullerSpace.toCompactGenusModuli_surjective R hgenus hmark }

end CompactGenusModuliSpace

end LowDimensionalTopology.Geometry.Teichmuller
