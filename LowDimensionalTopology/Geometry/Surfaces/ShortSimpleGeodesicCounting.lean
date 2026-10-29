module

public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.ShortOriginalClosedGeodesics
public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.GeodesicDecomposingSystemExistence
public import LowDimensionalTopology.Unproved.Surfaces.ClosedDecomposingSystemCardinalities
public import Mathlib.Data.Fintype.Pigeonhole

/-!
# Repetition among short simple geodesics on the original surface

Short distinct geometric images are disjoint. An actual maximal simple
geodesic family containing them and its explicit cardinality bound therefore
force repetition in a list with one additional member.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set

namespace LowDimensionalTopology.Geometry.Surfaces

/-- An actual list of one more than the maximal number of short simple
geodesic images contains two equal geometric images. -/
theorem exists_equal_geodesic_trace_of_short_simple_list
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {g : ℕ} (hg : 2 ≤ g) (hgenus : R.HasGenus g)
    (M : HyperbolicSurfaceModel R.toRiemannSurface)
    (hCard : LowDimensionalTopology.Unproved.Surfaces.ClosedDecomposingSystemCardinalities
      R hg hgenus M)
    (qs : Fin (3 * g - 3 + 1) → OriginalClosedGeodesic M)
    (hsimple : ∀ i, Function.Injective ((qs i).periodic.lift : AddCircle (1 : ℝ) → X))
    (hshort : ∀ i, (qs i).length.toReal < shortClosedGeodesicCutoff) :
    ∃ i j, i < j ∧ range (qs i).curve = range (qs j).curve := by
  classical
  let L : Set (Set X) := range (fun i => range (qs i).curve)
  have hL : IsSimpleGeodesicFamily M L := by
    constructor
    · rintro C ⟨i, rfl⟩
      exact ⟨qs i, hsimple i, rfl⟩
    · rintro C ⟨i, rfl⟩ D ⟨j, rfl⟩ hneq
      exact ((qs i).trace_eq_or_disjoint_of_length_lt_shortCutoff (qs j)
        (hshort i) (hshort j)).resolve_left hneq
  obtain ⟨E, hLE, hE⟩ := hL.exists_decomposingSystem_superset
  obtain ⟨hEfinite, _hComplementFinite, hEcard, _hComplementCard⟩ := hCard E hE
  let : Fintype E := hEfinite.fintype
  let toE : Fin (3 * g - 3 + 1) → E :=
    fun i => ⟨range (qs i).curve, hLE ⟨i, rfl⟩⟩
  have hsize : Fintype.card E < Fintype.card (Fin (3 * g - 3 + 1)) := by
    rw [Set.fintypeCard_eq_ncard, hEcard, Fintype.card_fin]
    exact Nat.lt_succ_self _
  obtain ⟨i, j, hij, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt toE hsize
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact ⟨i, j, hlt, congrArg Subtype.val heq⟩
  · exact ⟨j, i, hgt, (congrArg Subtype.val heq).symm⟩

end LowDimensionalTopology.Geometry.Surfaces
