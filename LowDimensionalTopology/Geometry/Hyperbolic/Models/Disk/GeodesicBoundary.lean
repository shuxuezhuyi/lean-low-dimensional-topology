module
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disk.Geodesic
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.HalfPlane.GeodesicBoundary

/-!
# Native disc ideal endpoints
Endpoints are actual closure points of the native Euclidean disc-line carriers.
The source's terminology is used literally: sharing one ideal endpoint is
parallelism; when the ideal ends are disjoint, interior intersection separates
the intersecting and disjoint cases.
-/

@[expose] public section
noncomputable section
open Set Filter
open scoped UpperHalfPlane Complex.UnitDisc OnePoint Topology
namespace LowDimensionalTopology.Geometry.Hyperbolic

/-- Ideal ends are defined by the actual closure of a native disc carrier. -/
def DiscLine.idealEndpoints (L : DiscLine) : Set (OnePoint ℂ) :=
  closure (extendedDiscPoint '' L.carrier) ∩ extendedDiscIdealBoundary

/-- The native circle arc is exactly the previously established actual Cayley carrier. -/
theorem DiscLine.carrier_eq_cayleyHLineCarrier (L : DiscLine) :
    L.carrier = cayleyHLineCarrier L.toHalfPlane := by
  have h := L.toHalfPlane.discCarrier_eq_cayley_image
  change L.toHalfPlane.toDiscLine.carrier = cayleyHLineCarrier L.toHalfPlane at h
  rwa [L.toHalfPlane_spec] at h

/-- The native closure definition agrees with the actual ideal-set construction, rather than a line label. -/
theorem DiscLine.idealEndpoints_eq_cayleyHLineIdealEndpoints (L : DiscLine) :
    L.idealEndpoints = cayleyHLineIdealEndpoints L.toHalfPlane := by
  unfold DiscLine.idealEndpoints cayleyHLineIdealEndpoints
  rw [L.carrier_eq_cayleyHLineCarrier]

/-- Actual native ideal endpoints are the actual extended Cayley images of the half-plane endpoints. -/
theorem DiscLine.idealEndpoints_eq_cayley_image (L : DiscLine) :
    L.idealEndpoints = extendedCayley '' L.toHalfPlane.idealEndpoints := by
  rw [L.idealEndpoints_eq_cayleyHLineIdealEndpoints, cayleyHLineIdealEndpoints_eq_image]

theorem DiscLine.toHalfPlane_injective : Function.Injective DiscLine.toHalfPlane := by
  intro L M h
  rw [← L.toHalfPlane_spec, ← M.toHalfPlane_spec, h]

/-- Each native disc h-line has precisely two genuine ideal boundary endpoints. -/
theorem DiscLine.ncard_idealEndpoints (L : DiscLine) : L.idealEndpoints.ncard = 2 := by
  rw [L.idealEndpoints_eq_cayley_image, Set.ncard_image_of_injective _ extendedCayley.injective,
    L.toHalfPlane.ncard_idealEndpoints]

theorem DiscLine.exists_idealEndpoints_pair (L : DiscLine) :
    ∃ a b : OnePoint ℂ, a ≠ b ∧ a ∈ extendedDiscIdealBoundary ∧ b ∈ extendedDiscIdealBoundary ∧
      L.idealEndpoints = {a,b} := by
  obtain ⟨a,b,_,hab,ha,hb,he,_⟩ := L.toHalfPlane.exists_idealEndpoints_pair
  refine ⟨extendedCayley a, extendedCayley b, extendedCayley.injective.ne hab,
    (idealBoundary_cayley_iff a).mp ha, (idealBoundary_cayley_iff b).mp hb, ?_⟩
  rw [L.idealEndpoints_eq_cayley_image, he, Set.image_pair]

/-- A native disc h-line is determined by its actual two ideal endpoints. -/
theorem DiscLine.idealEndpoints_injective : Function.Injective DiscLine.idealEndpoints := by
  intro L M h
  apply DiscLine.toHalfPlane_injective
  apply HalfPlaneLine.idealEndpoints_injective
  apply (Set.image_injective.mpr extendedCayley.injective)
  rwa [← L.idealEndpoints_eq_cayley_image, ← M.idealEndpoints_eq_cayley_image]

/-- Different native lines share at most one actual ideal endpoint. -/
theorem DiscLine.idealEndpoints_inter_subsingleton (L M : DiscLine) (hne : L ≠ M) :
    (L.idealEndpoints ∩ M.idealEndpoints).Subsingleton := by
  rw [L.idealEndpoints_eq_cayley_image, M.idealEndpoints_eq_cayley_image,
    ← Set.image_inter extendedCayley.injective]
  exact (L.toHalfPlane.idealEndpoints_inter_subsingleton M.toHalfPlane
    (DiscLine.toHalfPlane_injective.ne hne)).image extendedCayley

/-- A shared native interior point and a shared actual ideal endpoint force equality. -/
theorem DiscLine.eq_of_shared_ideal_and_interior (L M : DiscLine) (z : 𝔻)
    (hzL : z ∈ L.carrier) (hzM : z ∈ M.carrier) (p : OnePoint ℂ)
    (hpL : p ∈ L.idealEndpoints) (hpM : p ∈ M.idealEndpoints) : L = M := by
  rw [L.idealEndpoints_eq_cayley_image] at hpL
  rw [M.idealEndpoints_eq_cayley_image] at hpM
  obtain ⟨a,ha,hea⟩ := hpL
  obtain ⟨b,hb,heb⟩ := hpM
  have hab : a = b := extendedCayley.injective (hea.trans heb.symm)
  subst b
  apply DiscLine.toHalfPlane_injective
  exact L.toHalfPlane.eq_of_shared_ideal_and_interior M.toHalfPlane (discToHalfPlane z)
    ((L.mem_carrier z).mp hzL) ((M.mem_carrier z).mp hzM) a ha hb

/-- native disc lines are parallel exactly when they share one ideal endpoint. -/
def DiscLine.Parallel (L M : DiscLine) : Prop :=
  L ≠ M ∧ ∃ p : OnePoint ℂ, L.idealEndpoints ∩ M.idealEndpoints = {p}

/-- intersecting lines have disjoint ideal ends and an interior meeting point. -/
def DiscLine.Intersecting (L M : DiscLine) : Prop :=
  L ≠ M ∧ Disjoint L.idealEndpoints M.idealEndpoints ∧ (L.carrier ∩ M.carrier).Nonempty

/-- disjoint lines share neither an ideal nor an interior point. -/
def DiscLine.HDisjoint (L M : DiscLine) : Prop :=
  L ≠ M ∧ Disjoint L.idealEndpoints M.idealEndpoints ∧ Disjoint L.carrier M.carrier

/-- Parallel native lines have no common interior point. -/
theorem DiscLine.Parallel.disjoint_carriers {L M : DiscLine} (h : L.Parallel M) :
    Disjoint L.carrier M.carrier := by
  apply Set.disjoint_left.mpr
  intro z hzL hzM
  obtain ⟨p,he⟩ := h.2
  have hp : p ∈ L.idealEndpoints ∩ M.idealEndpoints := he.symm ▸ mem_singleton p
  exact h.1 (L.eq_of_shared_ideal_and_interior M z hzL hzM p hp.1 hp.2)

/-- For distinct native lines, meeting in the actual disc is exactly the source intersecting case. -/
theorem DiscLine.intersecting_iff (L M : DiscLine) (hne : L ≠ M) :
    L.Intersecting M ↔ (L.carrier ∩ M.carrier).Nonempty := by
  constructor
  · exact fun h => h.2.2
  · intro hmeet
    obtain ⟨z,hzL,hzM⟩ := hmeet
    refine ⟨hne, Set.disjoint_left.mpr ?_, ⟨z,hzL,hzM⟩⟩
    intro p hpL hpM
    exact hne (L.eq_of_shared_ideal_and_interior M z hzL hzM p hpL hpM)

/-- Every distinct pair of native disc h-lines has one of the source's three positions. -/
theorem DiscLine.classification (L M : DiscLine) (hne : L ≠ M) :
    L.Parallel M ∨ L.Intersecting M ∨ L.HDisjoint M := by
  by_cases hends : (L.idealEndpoints ∩ M.idealEndpoints).Nonempty
  · obtain ⟨p,hp⟩ := hends
    refine Or.inl ⟨hne,p,Set.eq_singleton_iff_unique_mem.mpr ⟨hp,?_⟩⟩
    intro q hq
    exact L.idealEndpoints_inter_subsingleton M hne hq hp
  · have hd : Disjoint L.idealEndpoints M.idealEndpoints :=
      Set.disjoint_left.mpr (fun p hpL hpM => hends ⟨p,hpL,hpM⟩)
    by_cases hmeet : (L.carrier ∩ M.carrier).Nonempty
    · exact Or.inr (Or.inl ⟨hne,hd,hmeet⟩)
    · exact Or.inr (Or.inr ⟨hne,hd,Set.disjoint_left.mpr (fun z hzL hzM => hmeet ⟨z,hzL,hzM⟩)⟩)

/-- The actual native-disc cases are exhaustive and mutually exclusive. -/
theorem DiscLine.classification_exclusive (L M : DiscLine) (hne : L ≠ M) :
    (L.Parallel M ∨ L.Intersecting M ∨ L.HDisjoint M) ∧
      ¬(L.Parallel M ∧ L.Intersecting M) ∧ ¬(L.Parallel M ∧ L.HDisjoint M) ∧
      ¬(L.Intersecting M ∧ L.HDisjoint M) := by
  refine ⟨L.classification M hne, ?_, ?_, ?_⟩
  · rintro ⟨hp,hi⟩
    obtain ⟨p,he⟩ := hp.2
    have hm : p ∈ L.idealEndpoints ∩ M.idealEndpoints := he.symm ▸ mem_singleton p
    exact Set.disjoint_left.mp hi.2.1 hm.1 hm.2
  · rintro ⟨hp,hd⟩
    obtain ⟨p,he⟩ := hp.2
    have hm : p ∈ L.idealEndpoints ∩ M.idealEndpoints := he.symm ▸ mem_singleton p
    exact Set.disjoint_left.mp hd.2.1 hm.1 hm.2
  · rintro ⟨hi,hd⟩
    obtain ⟨z,hzL,hzM⟩ := hi.2.2
    exact Set.disjoint_left.mp hd.2.2 hzL hzM

end LowDimensionalTopology.Geometry.Hyperbolic
