module
public import LowDimensionalTopology.Geometry.Polygon.Development.PoincarePairedSideStars
public import Mathlib.Tactic
@[expose] public section
noncomputable section
open Set
namespace LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing
universe u v
variable {X : Type u} {Γ : Type v} [Group Γ] [MulAction Γ X] [MetricSpace X]
variable {P : _root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon X} (S :
  _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing Γ P)

/-- The literal image of the original radius-r polygon neighborhood in an indexed copy. -/
def vertexCyclePiece (a : S.Copy) (r : ℝ) : Set X :=
  (fun z : X => a.1 • z) '' (P.carrier ∩ Metric.ball a.2.val r)

/-- Its actual open-polygon part, used for the original nonoverlap condition. -/
def vertexCycleInteriorPiece (a : S.Copy) (r : ℝ) : Set X :=
  (fun z : X => a.1 • z) '' (P.interior ∩ Metric.ball a.2.val r)

/-- The original finite vertex-cycle data: literal side crossings close cyclically,
and the actual indexed polygon neighborhoods cover a true ball without interior overlap.
The parameter V is the original polygon's geometric vertex set. -/
structure VertexCycle (V : Set P.Point) (x : P.Point) (r : ℝ) where
  radius_pos : 0 < r
  lengthPred : ℕ
  copies : Fin (lengthPred+1) → S.Copy
  base : copies 0 = (1,x)
  vertices : ∀ i,(copies i).2 ∈ V
  adjacent : ∀ i : Fin lengthPred,∃ s : P.Side,
    (copies i.castSucc).2.val ∈ s.val ∧
    (copies i.succ).2.val=S.generator s • (copies i.castSucc).2.val ∧
    (copies i.castSucc).1=(copies i.succ).1*S.generator s
  closing : ∃ s : P.Side,(copies (Fin.last lengthPred)).2.val ∈ s.val ∧
    (copies 0).2.val=S.generator s • (copies (Fin.last lengthPred)).2.val ∧
    (copies (Fin.last lengthPred)).1=(copies 0).1*S.generator s
  covers : (⋃ i,S.vertexCyclePiece (copies i) r)=Metric.ball x.val r
  nonoverlap : Pairwise (fun i j => Disjoint
    (S.vertexCycleInteriorPiece (copies i) r) (S.vertexCycleInteriorPiece (copies j) r))

/--
Condition vertex-cycle is stated using actual finite cycles at the original vertices,
without assuming whole gluing classes, local charts or the local tessellation conclusion.
-/
def FiniteVertexCycleCondition (V : Set P.Point) : Prop :=
  ∀ x ∈ V,∃ r : ℝ,Nonempty (S.VertexCycle V x r)

/-- The original cycle condition is vacuous when the original polygon has no ambient vertices. -/
theorem finiteVertexCycleCondition_empty : S.FiniteVertexCycleCondition ∅ := by
  intro x hx
  exact hx.elim

theorem finiteVertexCycleCondition_of_no_vertices (V : Set P.Point) (hV : V=∅) :
    S.FiniteVertexCycleCondition V := by
  rw [hV]
  exact S.finiteVertexCycleCondition_empty

/-- Every chosen genuine cycle representative belongs to the true original gluing class. -/
theorem VertexCycle.project_eq {V : Set P.Point} {x : P.Point} {r : ℝ}
    (h : S.VertexCycle V x r) (i : Fin (h.lengthPred+1)) :
    S.project (h.copies i)=S.project (1,x) := by
  induction i using Fin.induction with
  | zero => rw [h.base]
  | succ i ih =>
    have hs : S.Step (h.copies i.castSucc) (h.copies i.succ) := Or.inr (h.adjacent i)
    have he := (S.project_eq_iff _ _).mpr (Relation.EqvGen.rel _ _ hs)
    exact he.symm.trans ih

/-- Actual evaluation puts every chosen original vertex at the original ball center. -/
theorem VertexCycle.evaluation_eq {V : Set P.Point} {x : P.Point} {r : ℝ}
    (h : S.VertexCycle V x r) (i : Fin (h.lengthPred+1)) :
    S.copyEvaluation (h.copies i)=x.val := by
  have he := congrArg S.evaluation (h.project_eq S i)
  change S.copyEvaluation (h.copies i)=S.copyEvaluation (1,x) at he
  simpa only [copyEvaluation,one_smul] using he

/-- The finite original cycle is contained in the true fiber; this does not
replace the separate proof that it exhausts the whole original equivalence class. -/
theorem VertexCycle.copies_subset_fiber {V : Set P.Point} {x : P.Point} {r : ℝ}
    (h : S.VertexCycle V x r) : range h.copies ⊆ S.project ⁻¹' {S.project (1,x)} := by
  rintro a ⟨i,rfl⟩
  exact h.project_eq S i

theorem vertexCyclePiece_mono (a : S.Copy) {r t : ℝ} (hrt : r ≤ t) :
    S.vertexCyclePiece a r ⊆ S.vertexCyclePiece a t := by
  apply image_mono
  exact inter_subset_inter_right _ (Metric.ball_subset_ball hrt)

theorem vertexCycleInteriorPiece_mono (a : S.Copy) {r t : ℝ} (hrt : r ≤ t) :
    S.vertexCycleInteriorPiece a r ⊆ S.vertexCycleInteriorPiece a t := by
  apply image_mono
  exact inter_subset_inter_right _ (Metric.ball_subset_ball hrt)

/-- Literal indexed ball pieces shrink by intersection with the actual target ball. -/
theorem vertexCyclePiece_eq_inter_ball [IsIsometricSMul S.Generated X]
    (a : S.Copy) {x : X} (hx : S.copyEvaluation a=x) {r t : ℝ} (hrt : r ≤ t) :
    S.vertexCyclePiece a r=S.vertexCyclePiece a t ∩ Metric.ball x r := by
  have hd : ∀ z : X,dist (a.1 • z) x=dist z a.2.val := by
    intro z
    rw [←hx]
    exact (isometry_smul X a.1).dist_eq z a.2.val
  apply subset_antisymm
  · rintro z ⟨y,⟨hy,hr⟩,rfl⟩
    exact ⟨S.vertexCyclePiece_mono a hrt ⟨y,⟨hy,hr⟩,rfl⟩,by
      change dist (a.1 • y) x < r
      rwa [hd]⟩
  · rintro z ⟨⟨y,⟨hy,_ht⟩,rfl⟩,hr⟩
    refine ⟨y,⟨hy,?_⟩,rfl⟩
    change dist (a.1 • y) x < r at hr
    rwa [hd] at hr

/-- The same actual finite side cycle works at every smaller positive radius. -/
def VertexCycle.mono [IsIsometricSMul S.Generated X]
    {V : Set P.Point} {x : P.Point} {r t : ℝ} (h : S.VertexCycle V x t)
    (hr : 0 < r) (hrt : r ≤ t) : S.VertexCycle V x r where
  radius_pos := hr
  lengthPred := h.lengthPred
  copies := h.copies
  base := h.base
  vertices := h.vertices
  adjacent := h.adjacent
  closing := h.closing
  covers := by
    simp_rw [S.vertexCyclePiece_eq_inter_ball _ (h.evaluation_eq S _) hrt]
    rw [←iUnion_inter,h.covers]
    exact inter_eq_right.mpr (Metric.ball_subset_ball hrt)
  nonoverlap := by
    intro i j hij
    exact (h.nonoverlap hij).mono
      (S.vertexCycleInteriorPiece_mono _ hrt) (S.vertexCycleInteriorPiece_mono _ hrt)

/--
Under the original isometry condition every actual indexed original star maps
inside the corresponding true ambient ball, independently of local tessellation.
-/
theorem copyNeighborhood_image_subset_ball [IsIsometricSMul S.Generated X]
    (a : S.Copy) (r : ℝ) :
    S.copyEvaluation '' S.copyNeighborhood a r ⊆ Metric.ball (S.copyEvaluation a) r := by
  rintro z ⟨b,⟨c,hc,hg,hd⟩,rfl⟩
  have he := congrArg S.evaluation hc
  change S.copyEvaluation c=S.copyEvaluation a at he
  change dist (S.copyEvaluation b) (S.copyEvaluation a) < r
  rw [←he]
  change dist (b.1 • b.2.val) (c.1 • c.2.val) < r
  rw [hg,(isometry_smul X c.1).dist_eq]
  exact hd

/-- Each literal cycle piece is the evaluation of genuinely equivalent original indexed points. -/
theorem VertexCycle.piece_subset_star_image {V : Set P.Point} {x : P.Point} {r : ℝ}
    (h : S.VertexCycle V x r) (i : Fin (h.lengthPred+1)) :
    S.vertexCyclePiece (h.copies i) r ⊆ S.copyEvaluation '' S.copyNeighborhood (1,x) r := by
  rintro z ⟨y,⟨hy,hd⟩,rfl⟩
  exact ⟨((h.copies i).1,⟨y,hy⟩),⟨h.copies i,h.project_eq S i,rfl,hd⟩,rfl⟩

/--
The original finite cyclic ball cover proves the full image clause of local tessellation
for the genuine whole original star, without assuming its fiber or chart conclusion.
-/
theorem VertexCycle.image_eq [IsIsometricSMul S.Generated X]
    {V : Set P.Point} {x : P.Point} {r : ℝ} (h : S.VertexCycle V x r) :
    S.copyEvaluation '' S.copyNeighborhood (1,x) r=Metric.ball x.val r := by
  apply subset_antisymm
  · simpa only [copyEvaluation,one_smul] using S.copyNeighborhood_image_subset_ball (1,x) r
  · intro z hz
    have hz' : z ∈ ⋃ i,S.vertexCyclePiece (h.copies i) r := h.covers.symm ▸ hz
    obtain ⟨i,hi⟩ := mem_iUnion.mp hz'
    exact h.piece_subset_star_image S i hi

omit [MetricSpace X] in
/-- An elementary original step is identity or the literal original neighbor
across one of the actually incident sides. -/
theorem step_eq_or_sideMate (a b : S.Copy) (hab : S.Step a b) :
    b=a ∨ ∃ s : P.Side,∃ hx : a.2.val ∈ s.val,b=S.sideMateCopy a s hx := by
  rcases hab with he | ⟨s,hs,hy,hg⟩
  · exact Or.inl he.symm
  · right
    refine ⟨s,hs,?_⟩
    apply Prod.ext
    · change b.1=a.1*(S.generator s)⁻¹
      rw [hg]
      group
    · exact Subtype.ext hy

/-- Checking every original incident side crossing in a finite vertex cycle
proves that it exhausts the whole original gluing class. -/
theorem VertexCycle.fiber_eq_of_incidence_complete {V : Set P.Point} {x : P.Point} {r : ℝ}
    (h : S.VertexCycle V x r)
    (hc : ∀ i : Fin (h.lengthPred+1),∀ s : P.Side,∀ hx : (h.copies i).2.val ∈ s.val,
      S.sideMateCopy (h.copies i) s hx ∈ range h.copies) :
    S.project ⁻¹' {S.project (1,x)}=range h.copies := by
  apply S.project_fiber_eq_of_step_closed (range h.copies) (1,x) ⟨0,h.base⟩
  · rintro a ⟨i,rfl⟩ b hab
    rcases S.step_eq_or_sideMate (h.copies i) b hab with he | ⟨s,hs,he⟩
    · exact he ▸ mem_range_self i
    · rw [he]
      exact hc i s hs
  · rintro a ⟨i,rfl⟩
    exact (S.project_eq_iff _ _).mp (h.project_eq S i)

/-- Finiteness here is a conclusion of the explicit finite incident-side check,
not an input about the entire gluing equivalence class. -/
theorem VertexCycle.finite_fiber_of_incidence_complete {V : Set P.Point} {x : P.Point} {r : ℝ}
    (h : S.VertexCycle V x r)
    (hc : ∀ i : Fin (h.lengthPred+1),∀ s : P.Side,∀ hx : (h.copies i).2.val ∈ s.val,
      S.sideMateCopy (h.copies i) s hx ∈ range h.copies) :
    (S.project ⁻¹' {S.project (1,x)}).Finite := by
  rw [h.fiber_eq_of_incidence_complete S hc]
  exact Set.finite_range _

end LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing
