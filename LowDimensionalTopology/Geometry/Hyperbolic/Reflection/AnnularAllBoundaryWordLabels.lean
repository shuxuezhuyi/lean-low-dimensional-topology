module

public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.AnnularBoundaryClassInjection
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.AnnularPairNonElementary
public import LowDimensionalTopology.Geometry.Fuchsian.Nielsen.QuotientSignature
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# The three original annular words label every actual boundary cyclic class

The cardinality is derived inside the proof from the genuine signature of
this same original Cayley group. No class-count or surjectivity premise is added.
-/

@[expose] public section
noncomputable section
namespace LowDimensionalTopology.Geometry.Hyperbolic
open Fuchsian

variable (E r x : ℝ) (hE : 1 < E) (hr : 0 < r)
  (hin : 1 + r < x) (hout : x + r < E)
local notation "P" => HalfPlaneFuchsianGroup.cayleyData
  (annularPairReflectionHalfPlaneData E r x hE hr hin hout)
local notation "hNE" => annularPairReflectionDiscGroup_nonElementary E r x hE hr hin
local notation "hFG" => annularPairReflectionDiscGroup_fg E r x hE hr hin hout
local notation "g" => annularDiscPeripheralWord E r x hE hr hin hout

/-- The fixed whole-group injection is onto all actual boundary cyclic classes
when this same group's genuine signature has exactly three boundary ends. -/
theorem annularBoundaryWordClass_bijective
    (hB : ∀ i : Fin 3, IsBoundaryHyperbolic (P).asFuchsianDisc (g i))
    (hsig : HasNielsenFuchsianSignature P hNE hFG 0 [] 0 3) :
    Function.Bijective (annularBoundaryWordClass E r x hE hr hin hout hB) := by
  let : Finite (FuchsianBoundaryHyperbolicCyclicConjugacyClasses (P).asFuchsianDisc) :=
    finitelyGenerated_boundary_cyclic_classes_finite P hFG
  have hcard : Nat.card (Fin 3) = Nat.card (FuchsianBoundaryHyperbolicCyclicConjugacyClasses (P).asFuchsianDisc) := by
    obtain ⟨_w, _hw, _hwN, _J, _hc, _hv, _n, _S, _hr, _hg, _ho, _hp, hb⟩ := hsig
    simpa using hb
  exact (Nat.bijective_iff_injective_and_card _).mpr
    ⟨annularBoundaryWordClass_injective E r x hE hr hin hout hB, hcard⟩

/-- All actual boundary cyclic classes, labelled by the unchanged three words. -/
def annularBoundaryWordClassEquiv
    (hB : ∀ i : Fin 3, IsBoundaryHyperbolic (P).asFuchsianDisc (g i))
    (hsig : HasNielsenFuchsianSignature P hNE hFG 0 [] 0 3) :
    Fin 3 ≃ FuchsianBoundaryHyperbolicCyclicConjugacyClasses (P).asFuchsianDisc :=
  Equiv.ofBijective (annularBoundaryWordClass E r x hE hr hin hout hB)
    (annularBoundaryWordClass_bijective E r x hE hr hin hout hB hsig)

@[simp] theorem annularBoundaryWordClassEquiv_apply
    (hB : ∀ i : Fin 3, IsBoundaryHyperbolic (P).asFuchsianDisc (g i))
    (hsig : HasNielsenFuchsianSignature P hNE hFG 0 [] 0 3) (i : Fin 3) :
    annularBoundaryWordClassEquiv E r x hE hr hin hout hB hsig i =
      annularBoundaryWordClass E r x hE hr hin hout hB i := rfl

end LowDimensionalTopology.Geometry.Hyperbolic
