module
public import LowDimensionalTopology.Geometry.Polygon.Development.PoincareVertexIncidences
public import Mathlib.Tactic
@[expose] public section
noncomputable section
open Set Filter Topology
namespace LowDimensionalTopology.Geometry.Polygon

/-- An open piece of a pairwise disjoint open family cannot meet the closure of another piece. -/
theorem open_piece_index_eq_of_mem_closure {Y I : Type*} [TopologicalSpace Y]
    (A : I → Set Y) (ho : ∀ i,IsOpen (A i))
    (hd : Pairwise (fun i j=>Disjoint (A i) (A j)))
    {i j : I} {z : Y} (hi : z ∈ A i) (hj : z ∈ closure (A j)) : i=j := by
  by_contra hij
  exact Set.disjoint_left.mp ((hd hij).closure_right (ho i)) hi hj

/-- If two closed pieces fill a genuine neighborhood, no third disjoint open piece can have
that point in its closure. This detects original side adjacency without a quotient hypothesis. -/
theorem open_piece_index_eq_or_of_two_closures_nhds {Y I : Type*} [TopologicalSpace Y]
    (A : I → Set Y) (ho : ∀ i,IsOpen (A i))
    (hd : Pairwise (fun i j=>Disjoint (A i) (A j)))
    {i j k : I} {z : Y} (hz : z ∈ closure (A j))
    (hn : closure (A i) ∪ closure (A k) ∈ 𝓝 z) : j=i ∨ j=k := by
  by_contra h
  push Not at h
  have hji : Disjoint (A j) (closure (A i)) := (hd h.1).closure_right (ho j)
  have hjk : Disjoint (A j) (closure (A k)) := (hd h.2).closure_right (ho j)
  obtain ⟨y,hy,hyn⟩ := ((mem_closure_iff_frequently.mp hz).and_eventually hn).exists
  rcases hyn with hi | hk
  · exact Set.disjoint_left.mp hji hy hi
  · exact Set.disjoint_left.mp hjk hy hk

namespace PoincareSidePairing
universe u v
variable {X : Type u} {Γ : Type v} [Group Γ] [MulAction Γ X] [MetricSpace X]
variable {P : _root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon X} (S :
  _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing Γ P)

/-- The actual open polygon part of an indexed metric-ball piece is genuinely open. -/
theorem vertexCycleInteriorPiece_isOpen [IsIsometricSMul S.Generated X]
    (ho : IsOpen P.interior) (a : S.Copy) (r : ℝ) :
    IsOpen (S.vertexCycleInteriorPiece a r) := by
  exact (Homeomorph.smul a.1).isOpenMap _ (ho.inter Metric.isOpen_ball)

/-- A closed original polygon piece lies in the closure of its actual open polygon part. -/
theorem vertexCyclePiece_subset_closure_interior [IsIsometricSMul S.Generated X]
    (hc : P.carrier ⊆ closure P.interior) (a : S.Copy) (r : ℝ) :
    S.vertexCyclePiece a r ⊆ closure (S.vertexCycleInteriorPiece a r) := by
  rintro z ⟨p,⟨hp,hpr⟩,rfl⟩
  have hd : p ∈ closure (P.interior ∩ Metric.ball a.2.val r) :=
    Metric.isOpen_ball.closure_inter ⟨hc hp,hpr⟩
  exact image_closure_subset_closure_image (isometry_smul X a.1).continuous ⟨p,hd,rfl⟩

/-- The actual two paired polygon pieces fill an ambient neighborhood of every regular side point
inside a larger vertex ball. The radius comes from the true side germ and its actual metric margin. -/
theorem vertexCyclePiece_union_sideMate_mem_nhds [IsIsometricSMul S.Generated X]
    (a : S.Copy) (p : P.Point) (s : P.Side) (ha : a.2.val∈s.val)
    {r ρ : ℝ} (hp : dist p.val a.2.val<r) (hs : S.PairedSideNeighborhood p s ρ) :
    S.vertexCyclePiece a r ∪ S.vertexCyclePiece (S.sideMateCopy a s ha) r ∈ 𝓝 (a.1 • p.val) := by
  let δ := min ρ (r-dist p.val a.2.val)
  have hδ : 0<δ := lt_min hs.positive (sub_pos.mpr hp)
  apply Filter.mem_of_superset (Metric.ball_mem_nhds (a.1 • p.val) hδ)
  intro z hz
  let q := a.1⁻¹ • z
  have hq : dist q p.val<δ := by
    have he := (isometry_smul X a.1⁻¹).dist_eq z (a.1 • p.val)
    simpa only [inv_smul_smul] using he.trans_lt hz
  have hqr : dist q a.2.val<r := by
    have hmargin : δ≤r-dist p.val a.2.val := min_le_right _ _
    have ht := dist_triangle q p.val a.2.val
    linarith
  have hsmall : dist q p.val<ρ := lt_of_lt_of_le hq (min_le_left _ _)
  rcases hs.cover q hsmall with hP | hP
  · exact Or.inl ⟨q,⟨hP,hqr⟩,smul_inv_smul a.1 z⟩
  · right
    refine ⟨S.generator s • q,⟨hP,?_⟩,?_⟩
    · change dist (S.generator s • q) (S.generator s • a.2.val)<r
      rwa [(isometry_smul X (S.generator s)).dist_eq]
    · change (a.1*(S.generator s)⁻¹) • (S.generator s • q)=z
      simp only [mul_smul,inv_smul_smul,smul_inv_smul,q]

/-- The entire original vertex neighborhood is the union of its actual cycle-indexed polygon balls. -/
theorem VertexCycle.copyNeighborhood_eq_of_incidence_complete {V : Set P.Point} {x : P.Point} {r : ℝ}
    (h : S.VertexCycle V x r)
    (hc : ∀ i : Fin (h.lengthPred+1),∀ s : P.Side,∀ hx : (h.copies i).2.val ∈ s.val,
      S.sideMateCopy (h.copies i) s hx ∈ range h.copies) :
    S.copyNeighborhood (1,x) r={b | ∃i,b.1=(h.copies i).1 ∧ dist b.2.val (h.copies i).2.val<r} := by
  ext b
  constructor
  · rintro ⟨c,hcF,hbi,hd⟩
    have hcR : c ∈ range h.copies := by
      rw [←h.fiber_eq_of_incidence_complete S hc]
      exact hcF
    obtain ⟨i,rfl⟩ := hcR
    exact ⟨i,hbi,hd⟩
  · rintro ⟨i,hbi,hd⟩
    exact ⟨h.copies i,h.project_eq S i,hbi,hd⟩

/-- Avoidance of nonincident original sides propagates every original side step inside the full vertex star. -/
theorem VertexCycle.step_closed_of_incidence_complete [IsIsometricSMul S.Generated X]
    {V : Set P.Point} {x : P.Point} {r : ℝ} (h : S.VertexCycle V x r)
    (hc : ∀ i : Fin (h.lengthPred+1),∀ s : P.Side,∀ hx : (h.copies i).2.val ∈ s.val,
      S.sideMateCopy (h.copies i) s hx ∈ range h.copies)
    (hNear : ∀i,∀p ∈ P.carrier,dist p (h.copies i).2.val<r →
      ∀s : P.Side,p∈s.val → (h.copies i).2.val∈s.val) :
    ∀b ∈ S.copyNeighborhood (1,x) r,∀c : S.Copy,S.Step b c → c∈S.copyNeighborhood (1,x) r := by
  intro b hb c hbc
  rw [h.copyNeighborhood_eq_of_incidence_complete S hc] at hb ⊢
  obtain ⟨i,hbi,hbd⟩ := hb
  rcases S.step_eq_or_sideMate b c hbc with he | ⟨s,hbs,rfl⟩
  · subst c
    exact ⟨i,hbi,hbd⟩
  · have his := hNear i b.2.val b.2.property hbd s hbs
    obtain ⟨j,hj⟩ := hc i s his
    refine ⟨j,?_,?_⟩
    · change b.1*(S.generator s)⁻¹=(h.copies j).1
      rw [hbi]
      exact (congrArg Prod.fst hj).symm
    · have hp : (h.copies j).2.val=S.generator s • (h.copies i).2.val :=
        congrArg (fun a : S.Copy=>a.2.val) hj
      change dist (S.generator s • b.2.val) (h.copies j).2.val<r
      rw [hp,(isometry_smul X (S.generator s)).dist_eq]
      exact hbd

/-- Genuine regular-side half-neighborhoods force all coincidences of closed vertex pieces
to be exactly original side gluings, using only the original disjoint open interiors. -/
theorem VertexCycle.project_eq_of_evaluation_of_regular_sides [IsIsometricSMul S.Generated X]
    {V : Set P.Point} {x : P.Point} {r : ℝ} (h : S.VertexCycle V x r)
    (ho : IsOpen P.interior) (hcl : P.carrier ⊆ closure P.interior)
    (hc : ∀ i : Fin (h.lengthPred+1),∀ s : P.Side,∀ hx : (h.copies i).2.val ∈ s.val,
      S.sideMateCopy (h.copies i) s hx ∈ range h.copies)
    (hNear : ∀i,∀p ∈ P.carrier,dist p (h.copies i).2.val<r →
      ∀s : P.Side,p∈s.val → (h.copies i).2.val∈s.val)
    (hRegular : ∀i,∀p : P.Point,dist p.val (h.copies i).2.val<r →
      p.val≠(h.copies i).2.val →
      p.val∈P.interior ∨ ∃s : P.Side,∃ρ : ℝ,S.PairedSideNeighborhood p s ρ)
    (b : S.Copy) (hb : b∈S.copyNeighborhood (1,x) r)
    (c : S.Copy) (hcW : c∈S.copyNeighborhood (1,x) r)
    (he : S.copyEvaluation c=S.copyEvaluation b) : S.project c=S.project b := by
  rw [h.copyNeighborhood_eq_of_incidence_complete S hc] at hb hcW
  obtain ⟨i,hbi,hbd⟩ := hb
  obtain ⟨j,hcj,hcd⟩ := hcW
  have hcPiece : S.copyEvaluation c∈S.vertexCyclePiece (h.copies j) r := by
    refine ⟨c.2.val,⟨c.2.property,hcd⟩,?_⟩
    change (h.copies j).1 • c.2.val=c.1 • c.2.val
    rw [hcj]
  have hcClosure : S.copyEvaluation b∈closure (S.vertexCycleInteriorPiece (h.copies j) r) := by
    rw [←he]
    exact S.vertexCyclePiece_subset_closure_interior hcl _ _ hcPiece
  by_cases hcenter : b.2.val=(h.copies i).2.val
  · have hbc : b=h.copies i := Prod.ext hbi (Subtype.ext hcenter)
    have hcb : c=h.copies j := by
      apply S.copy_eq_of_evaluation_same_index hcj
      calc S.copyEvaluation c=S.copyEvaluation b := he
           _=x.val := by rw [hbc];exact h.evaluation_eq S i
           _=S.copyEvaluation (h.copies j) := (h.evaluation_eq S j).symm
    rw [hbc,hcb,h.project_eq S i,h.project_eq S j]
  · rcases hRegular i b.2 hbd hcenter with hbInt | ⟨s,ρ,hs⟩
    · have hbOpen : S.copyEvaluation b∈S.vertexCycleInteriorPiece (h.copies i) r := by
        refine ⟨b.2.val,⟨hbInt,hbd⟩,?_⟩
        change (h.copies i).1 • b.2.val=b.1 • b.2.val
        rw [hbi]
      have hij : i=j := _root_.LowDimensionalTopology.Geometry.Polygon.open_piece_index_eq_of_mem_closure
        (fun k=>S.vertexCycleInteriorPiece (h.copies k) r)
        (fun k=>S.vertexCycleInteriorPiece_isOpen ho (h.copies k) r) h.nonoverlap hbOpen hcClosure
      exact congrArg S.project (S.copy_eq_of_evaluation_same_index
        (hcj.trans (hij ▸ hbi.symm)) he)
    · have his : (h.copies i).2.val∈s.val := hNear i b.2.val b.2.property hbd s hs.start_mem
      obtain ⟨k,hk⟩ := hc i s his
      have hnPiece : S.vertexCyclePiece (h.copies i) r ∪ S.vertexCyclePiece (h.copies k) r ∈
          𝓝 (S.copyEvaluation b) := by
        have hn := S.vertexCyclePiece_union_sideMate_mem_nhds (h.copies i) b.2 s his hbd hs
        rw [←hk] at hn
        change _∈𝓝 ((h.copies i).1 • b.2.val) at hn
        simpa only [copyEvaluation,hbi] using hn
      have hnClosure : closure (S.vertexCycleInteriorPiece (h.copies i) r) ∪
          closure (S.vertexCycleInteriorPiece (h.copies k) r)∈𝓝 (S.copyEvaluation b) := by
        apply Filter.mem_of_superset hnPiece
        exact union_subset_union (S.vertexCyclePiece_subset_closure_interior hcl _ _)
          (S.vertexCyclePiece_subset_closure_interior hcl _ _)
      have hji := _root_.LowDimensionalTopology.Geometry.Polygon.open_piece_index_eq_or_of_two_closures_nhds
        (fun k=>S.vertexCycleInteriorPiece (h.copies k) r)
        (fun k=>S.vertexCycleInteriorPiece_isOpen ho (h.copies k) r) h.nonoverlap hcClosure hnClosure
      rcases hji with hji | hjk
      · exact congrArg S.project (S.copy_eq_of_evaluation_same_index
          (hcj.trans (hji ▸ hbi.symm)) he)
      · have hck : c.1=(S.sideMateCopy b s hs.start_mem).1 := by
          rw [hcj,hjk]
          have hki := congrArg Prod.fst hk
          change (h.copies k).1=b.1*(S.generator s)⁻¹
          rw [hki]
          change (h.copies i).1*(S.generator s)⁻¹=b.1*(S.generator s)⁻¹
          rw [hbi]
        have hstep := S.step_sideMateCopy b s hs.start_mem
        have hraw : c=S.sideMateCopy b s hs.start_mem := S.copy_eq_of_evaluation_same_index hck
          (he.trans (S.step_evaluation hstep))
        rw [hraw]
        exact (S.project_eq_iff _ _).mpr (Relation.EqvGen.rel _ _ (S.step_symm hstep))

/--
Original finite cyclic coverage and true regular-side geometry imply the complete local
condition local tessellation, including boundary identifications, with no local injectivity conclusion as input.
-/
theorem VertexCycle.localTessellation_of_regular_sides [IsIsometricSMul S.Generated X]
    {V : Set P.Point} {x : P.Point} {r : ℝ} (h : S.VertexCycle V x r)
    (ho : IsOpen P.interior) (hcl : P.carrier ⊆ closure P.interior)
    (hc : ∀ i : Fin (h.lengthPred+1),∀ s : P.Side,∀ hx : (h.copies i).2.val ∈ s.val,
      S.sideMateCopy (h.copies i) s hx ∈ range h.copies)
    (hNear : ∀i,∀p ∈ P.carrier,dist p (h.copies i).2.val<r →
      ∀s : P.Side,p∈s.val → (h.copies i).2.val∈s.val)
    (hRegular : ∀i,∀p : P.Point,dist p.val (h.copies i).2.val<r →
      p.val≠(h.copies i).2.val →
      p.val∈P.interior ∨ ∃s : P.Side,∃ρ : ℝ,S.PairedSideNeighborhood p s ρ) :
    S.LocalTessellation (1,x) r := by
  apply S.localTessellation_of_step_closed
  · simpa only [copyEvaluation,one_smul] using h.image_eq S
  · exact h.step_closed_of_incidence_complete S hc hNear
  · exact h.project_eq_of_evaluation_of_regular_sides S ho hcl hc hNear hRegular

/--
The same actual finite cycle supplies a finite whole fiber and all sufficiently small
local local tessellation balls. Both assertions are conclusions of original polygon side geometry.
-/
theorem VertexCycle.local_radius_of_regular_sides [IsIsometricSMul S.Generated X]
    {V : Set P.Point} {x : P.Point} {r : ℝ} (h : S.VertexCycle V x r)
    (ho : IsOpen P.interior) (hcl : P.carrier ⊆ closure P.interior)
    (hc : ∀ i : Fin (h.lengthPred+1),∀ s : P.Side,∀ hx : (h.copies i).2.val ∈ s.val,
      S.sideMateCopy (h.copies i) s hx ∈ range h.copies)
    (hNear : ∀i,∀p ∈ P.carrier,dist p (h.copies i).2.val<r →
      ∀s : P.Side,p∈s.val → (h.copies i).2.val∈s.val)
    (hRegular : ∀i,∀p : P.Point,dist p.val (h.copies i).2.val<r →
      p.val≠(h.copies i).2.val →
      p.val∈P.interior ∨ ∃s : P.Side,∃ρ : ℝ,S.PairedSideNeighborhood p s ρ) :
    (S.project ⁻¹' {S.project (1,x)}).Finite ∧
      ∃r₀ : ℝ,0<r₀ ∧ ∀t : ℝ,0<t → t≤r₀ → S.LocalTessellation (1,x) t := by
  refine ⟨h.finite_fiber_of_incidence_complete S hc,r,h.radius_pos,?_⟩
  intro t ht htr
  exact (h.mono S ht htr).localTessellation_of_regular_sides S ho hcl hc
    (fun i p hp hd=>hNear i p hp (lt_of_lt_of_le hd htr))
    (fun i p hd=>hRegular i p (lt_of_lt_of_le hd htr))

end PoincareSidePairing
end LowDimensionalTopology.Geometry.Polygon
