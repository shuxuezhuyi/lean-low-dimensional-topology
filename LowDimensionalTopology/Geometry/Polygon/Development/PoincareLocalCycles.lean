/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Polygon.Development.PoincareDevelopmentLocal
public import Mathlib.Tactic
@[expose] public section
noncomputable section
open Set
namespace LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing
universe u v
variable {X : Type u} {Γ : Type v} [Group Γ] [MulAction Γ X]
variable {P : _root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon X} (S :
  _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing Γ P)

/-- Closure under elementary side gluings is preserved under the actual full generated equivalence relation. -/
theorem gluing_membership_iff_of_step_closed (F : Set S.Copy)
    (hs : ∀ b ∈ F,∀ c : S.Copy,S.Step b c → c ∈ F)
    {a b : S.Copy} (hab : Relation.EqvGen S.Step a b) : a ∈ F ↔ b ∈ F := by
  induction hab with
  | rel a b h => exact ⟨fun ha => hs a ha b h,fun hb => hs b hb a (S.step_symm h)⟩
  | refl a => rfl
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- A candidate set closed under each literal side step contains the whole original glued fiber. -/
theorem project_fiber_subset_of_step_closed (F : Set S.Copy) (a : S.Copy) (ha : a ∈ F)
    (hs : ∀ b ∈ F,∀ c : S.Copy,S.Step b c → c ∈ F) :
    S.project ⁻¹' {S.project a} ⊆ F := by
  intro b hb
  have he : S.project b = S.project a := hb
  exact (S.gluing_membership_iff_of_step_closed F hs ((S.project_eq_iff _ _).mp he)).mpr ha

/-- Finite side-step closure proves finiteness of the genuine whole quotient fiber,
without assuming the desired finite-class conclusion. -/
theorem finite_project_fiber_of_step_closed (F : Set S.Copy) (hF : F.Finite)
    (a : S.Copy) (ha : a ∈ F) (hs : ∀ b ∈ F,∀ c : S.Copy,S.Step b c → c ∈ F) :
    (S.project ⁻¹' {S.project a}).Finite :=
  hF.subset (S.project_fiber_subset_of_step_closed F a ha hs)

/-- If each candidate is reached by actual gluings and no elementary step leaves,
the candidate list is exactly the original whole glued class. -/
theorem project_fiber_eq_of_step_closed (F : Set S.Copy) (a : S.Copy) (ha : a ∈ F)
    (hs : ∀ b ∈ F,∀ c : S.Copy,S.Step b c → c ∈ F)
    (hr : ∀ b ∈ F,Relation.EqvGen S.Step b a) : S.project ⁻¹' {S.project a} = F := by
  apply Set.Subset.antisymm (S.project_fiber_subset_of_step_closed F a ha hs)
  intro b hb
  exact (S.project_eq_iff _ _).mpr (hr b hb)


/-- An actual interior representative has exactly its literal singleton gluing class. -/
theorem project_fiber_eq_singleton_of_interior (a : S.Copy) (ha : a.2.val ∈ P.interior) :
    S.project ⁻¹' {S.project a} = {a} := by
  ext b
  constructor
  · intro hb
    exact S.gluing_interior_rigid ((S.project_eq_iff _ _).mp hb) (Or.inr ha)
  · rintro rfl
    rfl

variable [MetricSpace X]

/-- At an interior point the actual local union is the single indexed polygon ball. -/
theorem copyNeighborhood_eq_of_interior (a : S.Copy) (ha : a.2.val ∈ P.interior) (r : ℝ) :
    S.copyNeighborhood a r = {b | b.1 = a.1 ∧ dist b.2.val a.2.val < r} := by
  ext b
  constructor
  · rintro ⟨c,hc,hg,hd⟩
    have hca := S.gluing_interior_rigid ((S.project_eq_iff _ _).mp hc) (Or.inr ha)
    subst c
    exact ⟨hg,hd⟩
  · rintro ⟨hg,hd⟩
    exact ⟨a,rfl,hg,hd⟩

/-- The original interior case of local tessellation holds on each ambient ball genuinely contained in the polygon interior. -/
theorem localTessellation_of_interior_ball (x : P.Point) (hx : x.val ∈ P.interior)
    (r : ℝ) (hball : Metric.ball x.val r ⊆ P.interior) : S.LocalTessellation (1,x) r := by
  have hW := S.copyNeighborhood_eq_of_interior (1,x) hx r
  constructor
  · ext z
    constructor
    · rintro ⟨b,hb,rfl⟩
      rw [hW] at hb
      change dist (b.1 • b.2.val) ((1 : S.Generated) • x.val) < r
      rw [hb.1,one_smul,one_smul]
      exact hb.2
    · intro hz
      have hz' : z ∈ Metric.ball x.val r := by
        rw [Metric.mem_ball]
        change dist z ((1 : S.Generated) • x.val) < r at hz
        simpa only [one_smul] using hz
      let y : P.Point := ⟨z,P.interior_subset_carrier (hball hz')⟩
      refine ⟨(1,y),?_,?_⟩
      · rw [hW]
        exact ⟨rfl,hz'⟩
      · exact one_smul S.Generated z
  · intro b hb c
    have hb' := hb
    rw [hW] at hb'
    have hbI : b.2.val ∈ P.interior := hball hb'.2
    constructor
    · intro he
      have hcb := S.gluing_interior_rigid ((S.project_eq_iff _ _).mp he) (Or.inr hbI)
      subst c
      exact ⟨hb,rfl⟩
    · rintro ⟨hc,he⟩
      rw [hW] at hc
      have hv : c.2.val = b.2.val := by
        change c.1 • c.2.val = b.1 • b.2.val at he
        simpa only [hc.1,hb'.1,one_smul] using he
      have hcb : c = b := Prod.ext (hc.1.trans hb'.1.symm) (Subtype.ext hv)
      exact congrArg S.project hcb

/-- Openness supplies all sufficiently small genuine local tessellation stars at every interior point. -/
theorem interior_local_radius (hP : IsOpen P.interior) (x : P.Point) (hx : x.val ∈ P.interior) :
    ∃ r₀ : ℝ,0 < r₀ ∧ ∀ r : ℝ,0 < r → r ≤ r₀ → S.LocalTessellation (1,x) r := by
  obtain ⟨r₀,hr₀,ht⟩ := Metric.isOpen_iff.mp hP x.val hx
  exact ⟨r₀,hr₀,fun r _hr hrr => S.localTessellation_of_interior_ball x hx r
    ((Metric.ball_subset_ball hrr).trans ht)⟩

end LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing
