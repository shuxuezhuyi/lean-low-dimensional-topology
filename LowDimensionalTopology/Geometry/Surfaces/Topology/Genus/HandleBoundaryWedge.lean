/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Surfaces.Topology.Genus.HandleBoundary
public import LowDimensionalTopology.External.TauCeti.AlgebraicTopology.FundamentalGroup.WedgeSum
public import LowDimensionalTopology.External.TauCeti.AlgebraicTopology.FundamentalGroup.Homeomorph
public import Mathlib.Topology.Homeomorph.Lemmas
@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Metric Topology
namespace LowDimensionalTopology.Geometry.Surfaces.HandlePresentation

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

/-- The actual positive a- and b-sides of the polygon. -/
abbrev Edge (g : ℕ) := HandleCW.Edge g

/-- The boundary graph modeled as the wedge of its actual positive sides. -/
abbrev BoundaryBouquet (g : ℕ) :=
  TauCeti.WedgeSum (fun _ : Edge g => (1 : Circle))

/-- The actual side path, with both endpoints the single polygon vertex. -/
def intervalEdge {g : ℕ} (d : Edge g) : C(unitInterval, Boundary g) :=
  ⟨fun t => ⟨projection g (HandleSeparation.sidePoint (HandleCW.edgeSide d) t),
    ⟨_, HandleCW.sidePoint_norm_one _ _, rfl⟩⟩,
    ((projection_continuous g).comp
      (HandleSeparation.sidePoint_continuous (HandleCW.edgeSide d))).subtype_mk _⟩

@[simp] theorem intervalEdge_zero {g : ℕ} (d : Edge g) :
    intervalEdge d 0 = boundaryBase g := by
  apply Subtype.ext
  exact (HandleSeparation.sidePoint_endpoint_quotient_zero (HandleCW.edgeSide d) 0
    (Or.inl rfl)).trans (by simp [canonicalHandleVertex, boundaryBase, projection])

@[simp] theorem intervalEdge_one {g : ℕ} (d : Edge g) :
    intervalEdge d 1 = boundaryBase g := by
  apply Subtype.ext
  exact (HandleSeparation.sidePoint_endpoint_quotient_zero (HandleCW.edgeSide d) 1
    (Or.inr rfl)).trans (by simp [canonicalHandleVertex, boundaryBase, projection])

/-- No interior point of a positive side is identified with the common vertex. -/
theorem intervalEdge_eq_base_iff {g : ℕ} (d : Edge g) (t : unitInterval) :
    intervalEdge d t = boundaryBase g ↔ t = 0 ∨ t = 1 := by
  constructor
  · intro h
    by_cases h0 : t = 0
    · exact Or.inl h0
    by_cases h1 : t = 1
    · exact Or.inr h1
    have ht : 0 < t.val ∧ t.val < 1 :=
      ⟨lt_of_le_of_ne t.property.1 (fun he => h0 (Subtype.ext he.symm)),
        lt_of_le_of_ne t.property.2 (fun he => h1 (Subtype.ext he))⟩
    have hq : projection g (HandleSeparation.sidePoint (HandleCW.edgeSide d) 0) =
        projection g (HandleSeparation.sidePoint (HandleCW.edgeSide d) t) :=
      congrArg Subtype.val ((intervalEdge_zero d).trans h.symm)
    have he := (HandleCW.edge_core_quotient_fiber d d t 0 ht hq).2
    have hv := congrArg (fun u : unitInterval => u.val) he
    exact False.elim (ht.1.ne (by simpa only [Icc.coe_zero] using hv))
  · rintro (rfl | rfl) <;> simp

/-- The period-one circle coordinate, with its distinguished point at parameter zero. -/
def circleParameter (t : unitInterval) : Circle :=
  AddCircle.homeomorphCircle one_ne_zero (t.val : AddCircle (1 : ℝ))

@[simp] theorem circleParameter_zero : circleParameter 0 = 1 := by
  simp [circleParameter, AddCircle.homeomorphCircle_apply]

@[simp] theorem circleParameter_one : circleParameter 1 = 1 := by
  simp [circleParameter, AddCircle.coe_period, AddCircle.homeomorphCircle_apply]

/-- Every circle point has a parameter in the half-open interval. -/
theorem circleParameter_representative (z : Circle) :
    ∃ t : unitInterval, t.val < 1 ∧ circleParameter t = z := by
  let e := AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero
  have hm : e.symm z ∈ ((↑) : ℝ → AddCircle (1 : ℝ)) '' Ico 0 (0 + 1) := by
    rw [AddCircle.coe_image_Ico_eq]
    exact Set.mem_univ _
  obtain ⟨r, hr, he⟩ := hm
  refine ⟨⟨r, ⟨hr.1, (by simpa using hr.2.le)⟩⟩,
    (by simpa using hr.2), ?_⟩
  change e (r : AddCircle (1 : ℝ)) = z
  rw [he, e.apply_symm_apply]

/-- A clamped real parameter is used only to descend the continuous side path to a circle. -/
def realEdge {g : ℕ} (d : Edge g) : C(ℝ, Boundary g) :=
  (intervalEdge d).comp ⟨Set.projIcc 0 1 zero_le_one, continuous_projIcc⟩

@[simp] theorem realEdge_of_mem {g : ℕ} (d : Edge g) (t : unitInterval) :
    realEdge d t.val = intervalEdge d t := by
  change intervalEdge d (Set.projIcc 0 1 zero_le_one t.val) = intervalEdge d t
  rw [Set.projIcc_of_mem zero_le_one t.property]

@[simp] theorem realEdge_zero {g : ℕ} (d : Edge g) :
    realEdge d 0 = boundaryBase g := by
  simpa only [Icc.coe_zero] using (realEdge_of_mem d 0).trans (intervalEdge_zero d)

@[simp] theorem realEdge_one {g : ℕ} (d : Edge g) :
    realEdge d 1 = boundaryBase g := by
  simpa only [Icc.coe_one] using (realEdge_of_mem d 1).trans (intervalEdge_one d)

/-- The positive polygon edge as a genuine continuous circle map. -/
def circleEdge {g : ℕ} (d : Edge g) : C(Circle, Boundary g) :=
  ⟨AddCircle.liftIco (1 : ℝ) 0 (realEdge d) ∘
      (AddCircle.homeomorphCircle one_ne_zero).symm,
    (AddCircle.liftIco_zero_continuous
      (show realEdge d 0 = realEdge d 1 by simp)
      (realEdge d).continuous.continuousOn).comp
        (AddCircle.homeomorphCircle one_ne_zero).symm.continuous⟩

theorem circleEdge_parameter {g : ℕ} (d : Edge g) (t : unitInterval) :
    circleEdge d (circleParameter t) = intervalEdge d t := by
  change AddCircle.liftIco (1 : ℝ) 0 (realEdge d)
    ((AddCircle.homeomorphCircle one_ne_zero).symm
      (AddCircle.homeomorphCircle one_ne_zero (t.val : AddCircle (1 : ℝ)))) = _
  rw [Homeomorph.symm_apply_apply]
  by_cases ht : t = 1
  · subst t
    rw [Icc.coe_one, AddCircle.coe_period]
    rw [show (0 : AddCircle (1 : ℝ)) = ((0 : ℝ) : AddCircle (1 : ℝ)) by rfl,
      AddCircle.liftIco_coe_apply (by norm_num : (0 : ℝ) ∈ Ico 0 (0 + 1))]
    simp
  · have hlt : t.val < 1 :=
      lt_of_le_of_ne t.property.2 (fun he => ht (Subtype.ext he))
    rw [AddCircle.liftIco_coe_apply
      (show t.val ∈ Ico 0 (0 + 1) from
        ⟨t.property.1, by simpa only [zero_add] using hlt⟩)]
    exact realEdge_of_mem d t

@[simp] theorem circleEdge_one {g : ℕ} (d : Edge g) :
    circleEdge d 1 = boundaryBase g := by
  simpa using (circleEdge_parameter d 0)

@[simp] theorem circleEdge_eq_base_iff {g : ℕ} (d : Edge g) (z : Circle) :
    circleEdge d z = boundaryBase g ↔ z = 1 := by
  constructor
  · intro h
    obtain ⟨t, ht, rfl⟩ := circleParameter_representative z
    rw [circleEdge_parameter] at h
    rcases (intervalEdge_eq_base_iff d t).mp h with h0 | h1
    · subst t
      exact circleParameter_zero
    · subst t
      exact False.elim (lt_irrefl (1 : ℝ) ht)
  · rintro rfl
    exact circleEdge_one d

/-- Distinct open positive edges have disjoint images; only their endpoints are glued. -/
theorem circleEdge_eq_circleEdge_iff {g : ℕ} (d e : Edge g) (z w : Circle) :
    circleEdge d z = circleEdge e w ↔
      (z = 1 ∧ w = 1) ∨ (d = e ∧ z = w) := by
  constructor
  · intro h
    by_cases hz : z = 1
    · left
      refine ⟨hz, (circleEdge_eq_base_iff e w).mp ?_⟩
      rw [← h, hz, circleEdge_one]
    · obtain ⟨t, ht, htz⟩ := circleParameter_representative z
      obtain ⟨u, hu, huw⟩ := circleParameter_representative w
      have ht0 : 0 < t.val := by
        apply lt_of_le_of_ne t.property.1
        intro he
        have ht' : t = 0 := Subtype.ext he.symm
        have hp : circleParameter t = 1 := by rw [ht', circleParameter_zero]
        exact hz (htz.symm.trans hp)
      have hh : projection g (HandleSeparation.sidePoint (HandleCW.edgeSide e) u) =
          projection g (HandleSeparation.sidePoint (HandleCW.edgeSide d) t) := by
        have h' := h
        rw [← htz, ← huw, circleEdge_parameter, circleEdge_parameter] at h'
        exact congrArg Subtype.val h'.symm
      obtain ⟨hed, hut⟩ := HandleCW.edge_core_quotient_fiber d e t u ⟨ht0, ht⟩ hh
      exact Or.inr ⟨hed.symm, htz.symm.trans (hut ▸ huw)⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp

/-- The map from the bouquet to the actual quotient boundary, specified on every circle. -/
def bouquetToBoundary (g : ℕ) : C(BoundaryBouquet g, Boundary g) :=
  TauCeti.WedgeSum.lift (fun d => circleEdge d) (boundaryBase g) circleEdge_one

@[simp] theorem bouquetToBoundary_base (g : ℕ) :
    bouquetToBoundary g (TauCeti.WedgeSum.base _) = boundaryBase g :=
  TauCeti.WedgeSum.lift_base (fun d => circleEdge d) (boundaryBase g) circleEdge_one

@[simp] theorem bouquetToBoundary_incl {g : ℕ} (d : Edge g) (z : Circle) :
    bouquetToBoundary g (TauCeti.WedgeSum.incl _ d z) = circleEdge d z :=
  TauCeti.WedgeSum.lift_incl (fun d => circleEdge d) (boundaryBase g) circleEdge_one d z

theorem bouquetToBoundary_injective (g : ℕ) :
    Function.Injective (bouquetToBoundary g) := by
  intro x y h
  induction x using TauCeti.WedgeSum.ind with
  | base =>
    induction y using TauCeti.WedgeSum.ind with
    | base => rfl
    | incl e w =>
      simp only [bouquetToBoundary_base, bouquetToBoundary_incl] at h
      have hw : w = 1 := (circleEdge_eq_base_iff e w).mp h.symm
      subst w
      exact (TauCeti.WedgeSum.incl_apply_self e).symm
  | incl d z =>
    induction y using TauCeti.WedgeSum.ind with
    | base =>
      simp only [bouquetToBoundary_base, bouquetToBoundary_incl] at h
      have hz : z = 1 := (circleEdge_eq_base_iff d z).mp h
      subst z
      exact TauCeti.WedgeSum.incl_apply_self d
    | incl e w =>
      simp only [bouquetToBoundary_incl] at h
      rcases (circleEdge_eq_circleEdge_iff d e z w).mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact (TauCeti.WedgeSum.incl_apply_self d).trans
          (TauCeti.WedgeSum.incl_apply_self e).symm
      · rfl

theorem bouquetToBoundary_surjective {g : ℕ} (hg : 0 < g) :
    Function.Surjective (bouquetToBoundary g) := by
  rintro ⟨x, z, hz, hzx⟩
  obtain ⟨d, v, hv, hdv⟩ := HandleCW.boundary_quotient_edge_cover hg hz
  refine ⟨TauCeti.WedgeSum.incl _ d (circleParameter (HandleCW.edgeIntervalParam v)), ?_⟩
  rw [bouquetToBoundary_incl]
  apply Subtype.ext
  change (circleEdge d (circleParameter (HandleCW.edgeIntervalParam v))).val = x
  rw [circleEdge_parameter]
  exact hdv.trans hzx

instance boundaryBouquetCompactSpace (g : ℕ) : CompactSpace (BoundaryBouquet g) := by
  have h := TauCeti.WedgeSum.isQuotientMap_sumElim
    (x := fun _ : Edge g => (1 : Circle))
  exact Function.Surjective.compactSpace h.continuous h.surjective

/-- The actual polygon boundary is homeomorphic to the wedge of its `2g` positive circles.
This equivalence is proved from the literal quotient fibers, not postulated from a cell count. -/
def bouquetHomeomorphBoundary (g : ℕ) (hg : 0 < g) :
    BoundaryBouquet g ≃ₜ Boundary g :=
  IsHomeomorph.homeomorph (bouquetToBoundary g)
    (isHomeomorph_iff_continuous_bijective.mpr
      ⟨(bouquetToBoundary g).continuous,
        bouquetToBoundary_injective g, bouquetToBoundary_surjective hg⟩)

@[simp] theorem bouquetHomeomorphBoundary_base (g : ℕ) (hg : 0 < g) :
    bouquetHomeomorphBoundary g hg (TauCeti.WedgeSum.base _) = boundaryBase g :=
  bouquetToBoundary_base g

@[simp] theorem bouquetHomeomorphBoundary_incl (g : ℕ) (hg : 0 < g)
    (d : Edge g) (z : Circle) :
    bouquetHomeomorphBoundary g hg (TauCeti.WedgeSum.incl _ d z) = circleEdge d z :=
  bouquetToBoundary_incl d z

/-- The fundamental group of the actual geometric polygon boundary, on the actual positive edges. -/
def boundaryFundamentalGroupMulEquiv (g : ℕ) (hg : 0 < g) :
    FundamentalGroup (Boundary g) (boundaryBase g) ≃* FreeGroup (Edge g) :=
  (TauCeti.FundamentalGroup.homeomorphMulEquivOfEq
    (bouquetHomeomorphBoundary g hg) (bouquetHomeomorphBoundary_base g hg)).symm.trans
      (TauCeti.WedgeSum.circleFundamentalGroupMulEquiv (Edge g))

end LowDimensionalTopology.Geometry.Surfaces.HandlePresentation
