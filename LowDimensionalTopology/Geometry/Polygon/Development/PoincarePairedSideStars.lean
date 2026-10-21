module
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.SideNormalGeometry
public import LowDimensionalTopology.Geometry.Polygon.Development.PoincareLocalCycles
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.HalfPlaneLorentzReflections
public import Mathlib.Tactic
@[expose] public section
noncomputable section
open Set
namespace LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing
universe u v
variable {X : Type u} {Γ : Type v} [Group Γ] [MulAction Γ X]
variable {P : _root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon X} (S :
  _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing Γ P)

/-- The actual neighboring indexed copy obtained by crossing a specified original paired side. -/
def sideMateCopy (a : S.Copy) (s : P.Side) (hx : a.2.val ∈ s.val) : S.Copy :=
  (a.1*(S.generator s)⁻¹,⟨S.generator s • a.2.val,P.side_subset_carrier (S.paired s) (by
    rw [←S.generator_side_image s]
    exact ⟨a.2.val,hx,rfl⟩)⟩)

/-- Crossing an actual paired side is precisely one of the original elementary gluing steps. -/
theorem step_sideMateCopy (a : S.Copy) (s : P.Side) (hx : a.2.val ∈ s.val) :
    S.Step a (S.sideMateCopy a s hx) := by
  refine Or.inr ⟨s,hx,rfl,?_⟩
  change a.1 = (a.1*(S.generator s)⁻¹)*S.generator s
  simp only [inv_mul_cancel_right]

/-- The true mate lies on the actual paired side. -/
theorem sideMateCopy_mem_paired (a : S.Copy) (s : P.Side) (hx : a.2.val ∈ s.val) :
    (S.sideMateCopy a s hx).2.val ∈ (S.paired s).val := by
  rw [←S.generator_side_image s]
  exact ⟨a.2.val,hx,rfl⟩

/-- The original inverse-pair rule brings an actual paired-side neighbor back to its literal original copy. -/
theorem sideMateCopy_paired (a : S.Copy) (s : P.Side) (hx : a.2.val ∈ s.val) :
    S.sideMateCopy (S.sideMateCopy a s hx) (S.paired s) (S.sideMateCopy_mem_paired a s hx) = a := by
  apply Prod.ext
  · change (a.1*(S.generator s)⁻¹)*(S.generator (S.paired s))⁻¹ = a.1
    rw [S.generator_paired,inv_inv,inv_mul_cancel_right]
  · apply Subtype.ext
    change S.generator (S.paired s) • (S.generator s • a.2.val) = a.2.val
    rw [S.generator_paired,inv_smul_smul]

/-- At a point lying on only one original side, every actual elementary gluing is the identity or the specified mate. -/
theorem step_eq_or_sideMate_of_unique_side (a : S.Copy) (s : P.Side) (hx : a.2.val ∈ s.val)
    (hu : ∀ t : P.Side,a.2.val ∈ t.val → t = s) (b : S.Copy) (hstep : S.Step a b) :
    b = a ∨ b = S.sideMateCopy a s hx := by
  rcases hstep with he | ⟨t,ht,hy,hg⟩
  · exact Or.inl he.symm
  · have hts := hu t ht
    subst t
    right
    apply Prod.ext
    · change b.1 = a.1*(S.generator s)⁻¹
      rw [hg]
      group
    · exact Subtype.ext hy

/-- Two original unique paired-side incidences determine the entire true gluing class,
not just a selected pair of equivalent representatives. -/
theorem project_fiber_eq_side_pair (a : S.Copy) (s : P.Side) (hx : a.2.val ∈ s.val)
    (hu : ∀ t : P.Side,a.2.val ∈ t.val → t = s)
    (hv : ∀ t : P.Side,(S.sideMateCopy a s hx).2.val ∈ t.val → t = S.paired s) :
    S.project ⁻¹' {S.project a} = {a,S.sideMateCopy a s hx} := by
  let b := S.sideMateCopy a s hx
  have hb : b.2.val ∈ (S.paired s).val := S.sideMateCopy_mem_paired a s hx
  have hba : S.sideMateCopy b (S.paired s) hb = a := S.sideMateCopy_paired a s hx
  apply S.project_fiber_eq_of_step_closed {a,b} a (by simp)
  · intro c hc d hcd
    simp only [mem_insert_iff,mem_singleton_iff] at hc
    rcases hc with hc | hc
    · subst c
      change d = a ∨ d = b
      exact S.step_eq_or_sideMate_of_unique_side a s hx hu d hcd
    · subst c
      have hd := S.step_eq_or_sideMate_of_unique_side b (S.paired s) hb hv d hcd
      rw [hba] at hd
      change d = a ∨ d = b
      exact hd.symm
  · intro c hc
    simp only [mem_insert_iff,mem_singleton_iff] at hc
    rcases hc with hca | hc
    · subst c
      exact Relation.EqvGen.refl a
    · subst c
      exact Relation.EqvGen.rel _ _ (S.step_symm (S.step_sideMateCopy a s hx))

/-- The genuine side-interior class is finite, including the self-paired case. -/
theorem finite_project_fiber_of_unique_paired_sides (a : S.Copy) (s : P.Side)
    (hx : a.2.val ∈ s.val) (hu : ∀ t : P.Side,a.2.val ∈ t.val → t = s)
    (hv : ∀ t : P.Side,(S.sideMateCopy a s hx).2.val ∈ t.val → t = S.paired s) :
    (S.project ⁻¹' {S.project a}).Finite := by
  rw [S.project_fiber_eq_side_pair a s hx hu hv]
  exact Set.toFinite _


variable [MetricSpace X]

/-- The two actual representatives give exactly two literal indexed polygon balls. -/
theorem copyNeighborhood_eq_side_pair (a : S.Copy) (s : P.Side) (hx : a.2.val ∈ s.val)
    (hu : ∀ t : P.Side,a.2.val ∈ t.val → t = s)
    (hv : ∀ t : P.Side,(S.sideMateCopy a s hx).2.val ∈ t.val → t = S.paired s) (r : ℝ) :
    S.copyNeighborhood a r = {b | (b.1 = a.1 ∧ dist b.2.val a.2.val < r) ∨
      (b.1 = (S.sideMateCopy a s hx).1 ∧ dist b.2.val (S.sideMateCopy a s hx).2.val < r)} := by
  have he := S.project_fiber_eq_side_pair a s hx hu hv
  have hm : S.project (S.sideMateCopy a s hx) = S.project a :=
    (S.project_eq_iff _ _).mpr (Relation.EqvGen.rel _ _ (S.step_symm (S.step_sideMateCopy a s hx)))
  ext b
  constructor
  · rintro ⟨c,hc,hg,hd⟩
    have hcF : c ∈ ({a,S.sideMateCopy a s hx} : Set S.Copy) := by rw [←he];exact hc
    simp only [mem_insert_iff,mem_singleton_iff] at hcF
    rcases hcF with hca | hcm
    · subst c
      exact Or.inl ⟨hg,hd⟩
    · subst c
      exact Or.inr ⟨hg,hd⟩
  · rintro (⟨hg,hd⟩ | ⟨hg,hd⟩)
    · exact ⟨a,rfl,hg,hd⟩
    · exact ⟨S.sideMateCopy a s hx,hm,hg,hd⟩

/-- A local gluing union closed under all true side steps is saturated under every original gluing. -/
theorem localTessellation_of_step_closed {a : S.Copy} {r : ℝ}
    (hcover : S.copyEvaluation '' S.copyNeighborhood a r = Metric.ball (S.copyEvaluation a) r)
    (hstep : ∀ b ∈ S.copyNeighborhood a r,∀ c : S.Copy,S.Step b c → c ∈ S.copyNeighborhood a r)
    (hsep : ∀ b ∈ S.copyNeighborhood a r,∀ c ∈ S.copyNeighborhood a r,
      S.copyEvaluation c = S.copyEvaluation b → S.project c = S.project b) :
    S.LocalTessellation a r := by
  refine ⟨hcover,?_⟩
  intro b hb c
  constructor
  · intro he
    refine ⟨?_,S.gluing_evaluation ((S.project_eq_iff _ _).mp he)⟩
    exact (S.gluing_membership_iff_of_step_closed (S.copyNeighborhood a r) hstep
      ((S.project_eq_iff _ _).mp he)).mpr hb
  · rintro ⟨hc,he⟩
    exact hsep b hb c hc he


/-- Literal opposite-side neighborhood data: no additional side enters either ball,
and the two original closed polygon pieces cover with intersection only on the given side. -/
structure PairedSideNeighborhood (x : P.Point) (s : P.Side) (r : ℝ) : Prop where
  positive : 0 < r
  start_mem : x.val ∈ s.val
  start_only : ∀ t : P.Side,∀ y ∈ t.val,dist y x.val < r → t = s
  mate_only : ∀ t : P.Side,∀ y ∈ t.val,dist y (S.generator s • x.val) < r → t = S.paired s
  cover : ∀ z : X,dist z x.val < r → z ∈ P.carrier ∨ S.generator s • z ∈ P.carrier
  overlap : ∀ z : X,dist z x.val < r → z ∈ P.carrier →
    S.generator s • z ∈ P.carrier → z ∈ s.val

/-- Geometric local absence of other sides determines the two actual raw neighborhood pieces. -/
theorem PairedSideNeighborhood.copyNeighborhood_eq {x : P.Point} {s : P.Side} {r : ℝ}
    (h : S.PairedSideNeighborhood x s r) :
    S.copyNeighborhood (1,x) r = {b | (b.1 = 1 ∧ dist b.2.val x.val < r) ∨
      (b.1 = (S.generator s)⁻¹ ∧ dist b.2.val (S.generator s • x.val) < r)} := by
  have hu : ∀ t : P.Side,x.val ∈ t.val → t = s := by
    intro t ht
    exact h.start_only t x.val ht (by simpa only [dist_self] using h.positive)
  have hv : ∀ t : P.Side,(S.sideMateCopy (1,x) s h.start_mem).2.val ∈ t.val → t = S.paired s := by
    intro t ht
    exact h.mate_only t (S.generator s • x.val) ht (by simpa only [dist_self] using h.positive)
  simpa only [sideMateCopy,one_mul] using S.copyNeighborhood_eq_side_pair (1,x) s h.start_mem hu hv r

/-- The actual two polygon half-neighborhoods are closed under every original elementary side gluing. -/
theorem PairedSideNeighborhood.step_closed [IsIsometricSMul S.Generated X]
    {x : P.Point} {s : P.Side} {r : ℝ} (h : S.PairedSideNeighborhood x s r) :
    ∀ b ∈ S.copyNeighborhood (1,x) r,∀ c : S.Copy,S.Step b c → c ∈ S.copyNeighborhood (1,x) r := by
  intro b hb c hbc
  rcases hbc with rfl | ⟨t,ht,hy,hg⟩
  · exact hb
  · rw [h.copyNeighborhood_eq S] at hb ⊢
    rcases hb with ⟨hbi,hd⟩ | ⟨hbi,hd⟩
    · have hts := h.start_only t b.2.val ht hd
      subst t
      right
      constructor
      · have he : c.1*(S.generator s) = 1 := hg.symm.trans hbi
        calc c.1 = (c.1*S.generator s)*(S.generator s)⁻¹ := by group
             _ = (S.generator s)⁻¹ := by rw [he,one_mul]
      · rw [hy,(isometry_smul X (S.generator s)).dist_eq]
        exact hd
    · have hts := h.mate_only t b.2.val ht hd
      subst t
      left
      constructor
      · rw [S.generator_paired] at hg
        have he : c.1*(S.generator s)⁻¹ = (S.generator s)⁻¹ := hg.symm.trans hbi
        exact mul_right_cancel (he.trans (one_mul _).symm)
      · rw [S.generator_paired] at hy
        rw [hy]
        have he := (isometry_smul X (S.generator s)⁻¹).dist_eq b.2.val (S.generator s • x.val)
        simpa only [inv_smul_smul] using he.trans_lt hd

/-- Actual two-piece coverage and isometry of the paired map give exactly the full ambient ball image. -/
theorem PairedSideNeighborhood.image_eq [IsIsometricSMul S.Generated X]
    {x : P.Point} {s : P.Side} {r : ℝ} (h : S.PairedSideNeighborhood x s r) :
    S.copyEvaluation '' S.copyNeighborhood (1,x) r = Metric.ball (S.copyEvaluation (1,x)) r := by
  ext z
  constructor
  · rintro ⟨b,hb,rfl⟩
    rw [h.copyNeighborhood_eq S] at hb
    change dist (b.1 • b.2.val) ((1 : S.Generated) • x.val) < r
    rw [one_smul]
    rcases hb with ⟨hbi,hd⟩ | ⟨hbi,hd⟩
    · simpa only [hbi,one_smul] using hd
    · rw [hbi]
      have he := (isometry_smul X (S.generator s)⁻¹).dist_eq b.2.val (S.generator s • x.val)
      simpa only [inv_smul_smul] using he.trans_lt hd
  · intro hz
    have hd : dist z x.val < r := by
      change dist z ((1 : S.Generated) • x.val) < r at hz
      simpa only [one_smul] using hz
    rcases h.cover z hd with hP | hP
    · let y : P.Point := ⟨z,hP⟩
      refine ⟨(1,y),?_,one_smul _ _⟩
      rw [h.copyNeighborhood_eq S]
      exact Or.inl ⟨rfl,hd⟩
    · let y : P.Point := ⟨S.generator s • z,hP⟩
      refine ⟨((S.generator s)⁻¹,y),?_,inv_smul_smul _ _⟩
      rw [h.copyNeighborhood_eq S]
      right
      refine ⟨rfl,?_⟩
      exact ((isometry_smul X (S.generator s)).dist_eq z x.val).trans_lt hd


omit [MetricSpace X] in
/-- Equal original evaluation in the same actual indexed copy determines the original point. -/
theorem copy_eq_of_evaluation_same_index {a b : S.Copy} (hi : a.1 = b.1)
    (he : S.copyEvaluation a = S.copyEvaluation b) : a = b := by
  apply Prod.ext hi
  apply Subtype.ext
  apply MulAction.injective b.1
  change a.1 • a.2.val = b.1 • b.2.val at he
  rwa [hi] at he

/-- The only overlaps of the two actual half-neighborhood pieces are identified
by a literal original side step; no local injectivity conclusion is assumed. -/
theorem PairedSideNeighborhood.project_eq_of_evaluation [IsIsometricSMul S.Generated X]
    {x : P.Point} {s : P.Side} {r : ℝ} (h : S.PairedSideNeighborhood x s r)
    (b : S.Copy) (hb : b ∈ S.copyNeighborhood (1,x) r)
    (c : S.Copy) (hc : c ∈ S.copyNeighborhood (1,x) r)
    (he : S.copyEvaluation c = S.copyEvaluation b) : S.project c = S.project b := by
  rw [h.copyNeighborhood_eq S] at hb hc
  rcases hb with hb | hb
  · rcases hc with hc | hc
    · exact congrArg S.project (S.copy_eq_of_evaluation_same_index (hc.1.trans hb.1.symm) he)
    · have he₀ := he
      change c.1 • c.2.val = b.1 • b.2.val at he₀
      rw [hc.1,hb.1,one_smul] at he₀
      have hp : c.2.val = S.generator s • b.2.val := by
        have hh := congrArg (fun z : X => S.generator s • z) he₀
        simpa only [smul_inv_smul] using hh
      have hbs : b.2.val ∈ s.val := h.overlap b.2.val hb.2 b.2.property (by rw [←hp];exact c.2.property)
      have hstep : S.Step b c := Or.inr ⟨s,hbs,hp,by rw [hb.1,hc.1,inv_mul_cancel]⟩
      exact (S.project_eq_iff _ _).mpr (Relation.EqvGen.rel _ _ (S.step_symm hstep))
  · rcases hc with hc | hc
    · have he₀ := he
      change c.1 • c.2.val = b.1 • b.2.val at he₀
      rw [hc.1,hb.1,one_smul] at he₀
      have hp : b.2.val = S.generator s • c.2.val := by
        have hh := congrArg (fun z : X => S.generator s • z) he₀
        simpa only [smul_inv_smul] using hh.symm
      have hcs : c.2.val ∈ s.val := h.overlap c.2.val hc.2 c.2.property (by rw [←hp];exact b.2.property)
      have hstep : S.Step c b := Or.inr ⟨s,hcs,hp,by rw [hc.1,hb.1,inv_mul_cancel]⟩
      exact (S.project_eq_iff _ _).mpr (Relation.EqvGen.rel _ _ hstep)
    · exact congrArg S.project (S.copy_eq_of_evaluation_same_index (hc.1.trans hb.1.symm) he)

/-- Genuine opposite paired half-neighborhood geometry proves the full original local tessellation condition at this radius. -/
theorem PairedSideNeighborhood.localTessellation [IsIsometricSMul S.Generated X]
    {x : P.Point} {s : P.Side} {r : ℝ} (h : S.PairedSideNeighborhood x s r) :
    S.LocalTessellation (1,x) r :=
  S.localTessellation_of_step_closed (h.image_eq S) (h.step_closed S)
    (h.project_eq_of_evaluation S)

/-- The true side-neighborhood geometry persists when its positive radius is decreased. -/
theorem PairedSideNeighborhood.mono {x : P.Point} {s : P.Side} {r t : ℝ}
    (h : S.PairedSideNeighborhood x s r) (ht : 0 < t) (htr : t ≤ r) :
    S.PairedSideNeighborhood x s t where
  positive := ht
  start_mem := h.start_mem
  start_only a y hy hd := h.start_only a y hy (hd.trans_le htr)
  mate_only a y hy hd := h.mate_only a y hy (hd.trans_le htr)
  cover y hy := h.cover y (hy.trans_le htr)
  overlap y hy hP hQ := h.overlap y (hy.trans_le htr) hP hQ

/-- Genuine side-interior geometry supplies the original sufficiently-small-radius local tessellation statement. -/
theorem PairedSideNeighborhood.local_radius [IsIsometricSMul S.Generated X]
    {x : P.Point} {s : P.Side} {r : ℝ} (h : S.PairedSideNeighborhood x s r) :
    ∃ r₀ : ℝ,0 < r₀ ∧ ∀ t : ℝ,0 < t → t ≤ r₀ → S.LocalTessellation (1,x) t :=
  ⟨r,h.positive,fun _ ht htr => (h.mono S ht htr).localTessellation S⟩

/-- The actual whole side-interior class remains finite independently of the radius. -/
theorem PairedSideNeighborhood.finite_class {x : P.Point} {s : P.Side} {r : ℝ}
    (h : S.PairedSideNeighborhood x s r) : (S.project ⁻¹' {S.project (1,x)}).Finite := by
  apply S.finite_project_fiber_of_unique_paired_sides (1,x) s h.start_mem
  · intro t ht
    exact h.start_only t x.val ht (by simpa only [dist_self] using h.positive)
  · intro t ht
    exact h.mate_only t (S.generator s • x.val) ht (by simpa only [dist_self] using h.positive)

/-- With no finite vertices, genuine original interior/paired-side geometry proves all of local tessellation. -/
theorem finiteFiberLocalTessellationCondition_of_regular_sides [IsIsometricSMul S.Generated X]
    (ho : IsOpen P.interior)
    (hreg : ∀ x : P.Point,x.val ∈ P.interior ∨ ∃ s : P.Side,∃ r : ℝ,S.PairedSideNeighborhood x s r) :
    S.FiniteFiberLocalTessellationCondition where
  finite_class x := by
    rcases hreg x with hx | ⟨s,r,hs⟩
    · rw [S.project_fiber_eq_singleton_of_interior (1,x) hx]
      exact Set.finite_singleton _
    · exact hs.finite_class S
  local_radius x := by
    rcases hreg x with hx | ⟨s,r,hs⟩
    · exact S.interior_local_radius ho x hx
    · exact hs.local_radius S

end LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing

namespace LowDimensionalTopology.Geometry.Polygon
open InnerProductGeometry
open scoped UpperHalfPlane

/-- Reflection changes the sign of the actual normalized Lorentz side coordinate. -/
theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.normalTimeAt_self_reflection (N :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) (z : ℍ) :
    N.normalTimeAt (N.reflection z) = -N.normalTimeAt z := by
  have hu := N.incenterNormal_lorentz_unit
  have hn : N.normalPairing N = 1 := by
    unfold _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.normalPairing
    rw [real_inner_self_eq_norm_sq]
    nlinarith only [hu]
  rw [N.normalTimeAt_reflection,hn]
  ring

end LowDimensionalTopology.Geometry.Polygon

namespace LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing
open LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Polygon
open scoped UpperHalfPlane
variable {Γ : Type*} [Group Γ] [MulAction Γ ℍ]
variable {P : _root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon ℍ} (S :
  _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing Γ P)

/-- The genuine signed closed-half-plane germ and its actual reflection supply
both pieces and their exact boundary overlap; no gluing-class or chart conclusion is assumed. -/
theorem pairedSideNeighborhood_of_halfPlaneReflection
    {x : P.Point} {s : P.Side} {r σ : ℝ} (N : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine)
    (hr : 0 < r) (hσ : σ ≠ 0) (hx : x.val ∈ s.val)
    (hs : s.val ⊆ N.carrier) (hp : S.paired s = s)
    (he : ∀ z : ℍ,S.generator s • z = N.reflection z)
    (ho : ∀ t : P.Side,∀ y ∈ t.val,dist y x.val < r → t = s)
    (hP : ∀ z : ℍ,dist z x.val < r → (z ∈ P.carrier ↔ 0 ≤ σ*N.normalTimeAt z))
    (hZ : ∀ z : ℍ,dist z x.val < r → N.normalTimeAt z = 0 → z ∈ s.val) :
    S.PairedSideNeighborhood x s r := by
  have hf : N.reflection x.val = x.val := (N.reflection_fixed_iff x.val).mpr (hs hx)
  have hd : ∀ z : ℍ,dist (N.reflection z) x.val = dist z x.val := by
    intro z
    calc
      dist (N.reflection z) x.val = dist (N.reflection z) (N.reflection x.val) := by rw [hf]
      _ = dist z x.val := N.reflection_isometry.dist_eq z x.val
  refine ⟨hr,hx,ho,?_,?_,?_⟩
  · intro t y hy hdy
    rw [he,hf] at hdy
    rw [hp]
    exact ho t y hy hdy
  · intro z hz
    rcases le_total 0 (σ*N.normalTimeAt z) with hpos | hneg
    · exact Or.inl ((hP z hz).mpr hpos)
    · right
      rw [he]
      apply (hP (N.reflection z) (by rwa [hd])).mpr
      rw [N.normalTimeAt_self_reflection,mul_neg]
      linarith
  · intro z hz hzP hzR
    rw [he] at hzR
    have ha := (hP z hz).mp hzP
    have hb := (hP (N.reflection z) (by rwa [hd])).mp hzR
    rw [N.normalTimeAt_self_reflection,mul_neg] at hb
    have hzero : σ*N.normalTimeAt z = 0 := by linarith
    exact hZ z hz ((mul_eq_zero.mp hzero).resolve_left hσ)

end LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing
