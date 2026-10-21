module
public import LowDimensionalTopology.Geometry.Polygon.Development.FinitePolygonPoincareData
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.NativeSegmentEndpoints
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Tactic
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Topology
open scoped UpperHalfPlane Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Polygon
open LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces

/-- The actual two incident original sides exhaust the original finite polygon vertex. -/
theorem finitePolygon_vertex_incident_sides {m : ℕ} (Q : DiscPolygon m)
    (hf : ∀i,‖(Q.vertices i : ℂ)‖<1) (i : Fin m)
    (s : (finiteDiscPoincarePolygon Q hf).Side) (hs : finitePolygonVertex Q hf i∈s.val) :
    s=finitePolygonSideEquiv Q hf ((finRotate m).symm i) ∨s=finitePolygonSideEquiv Q hf i := by
  obtain ⟨j,rfl⟩:=(finitePolygonSideEquiv Q hf).surjective s
  exact ((finitePolygonVertex_side_iff Q hf i j).mp hs).imp
    (congrArg (finitePolygonSideEquiv Q hf)) (congrArg (finitePolygonSideEquiv Q hf))

/-- The actual other original incident side, with original side labels retained at straight corners. -/
def finitePolygonVertexOtherSide {m : ℕ} (Q : DiscPolygon m)
    (hf : ∀i,‖(Q.vertices i : ℂ)‖<1) (i : Fin m)
    (s : (finiteDiscPoincarePolygon Q hf).Side) : (finiteDiscPoincarePolygon Q hf).Side := by
  classical
  exact if s=finitePolygonSideEquiv Q hf i then finitePolygonSideEquiv Q hf ((finRotate m).symm i)
  else finitePolygonSideEquiv Q hf i

theorem finitePolygonVertexOtherSide_incident {m : ℕ} (Q : DiscPolygon m)
    (hf : ∀i,‖(Q.vertices i : ℂ)‖<1) (i : Fin m)
    (s : (finiteDiscPoincarePolygon Q hf).Side) :
    finitePolygonVertex Q hf i∈(finitePolygonVertexOtherSide Q hf i s).val := by
  by_cases hs : s=finitePolygonSideEquiv Q hf i
  · simp only [finitePolygonVertexOtherSide,hs,ite_true]
    exact (finitePolygonVertex_side_iff Q hf i _).mpr (Or.inl rfl)
  · simp only [finitePolygonVertexOtherSide,hs,ite_false]
    exact finitePolygonSide_left_mem Q hf i

theorem finitePolygonVertexOtherSide_ne {m : ℕ} (Q : DiscPolygon m)
    (hf : ∀i,‖(Q.vertices i : ℂ)‖<1) (i : Fin m)
    (s : (finiteDiscPoincarePolygon Q hf).Side) : finitePolygonVertexOtherSide Q hf i s≠s := by
  have hne : finitePolygonSideEquiv Q hf ((finRotate m).symm i)≠finitePolygonSideEquiv Q hf i :=
    (finitePolygonSideEquiv Q hf).injective.ne (Q.prev_ne_self i)
  by_cases hs : s=finitePolygonSideEquiv Q hf i
  · simpa only [finitePolygonVertexOtherSide,hs,ite_true] using hne
  · simpa only [finitePolygonVertexOtherSide,hs,ite_false] using (Ne.symm hs)

/-- Choosing the other original incident side is truly involutive on actual vertex-side flags. -/
theorem finitePolygonVertexOtherSide_involutive {m : ℕ} (Q : DiscPolygon m)
    (hf : ∀i,‖(Q.vertices i : ℂ)‖<1) (i : Fin m)
    (s : (finiteDiscPoincarePolygon Q hf).Side) (hs : finitePolygonVertex Q hf i∈s.val) :
    finitePolygonVertexOtherSide Q hf i (finitePolygonVertexOtherSide Q hf i s)=s := by
  have hne : finitePolygonSideEquiv Q hf ((finRotate m).symm i)≠finitePolygonSideEquiv Q hf i :=
    (finitePolygonSideEquiv Q hf).injective.ne (Q.prev_ne_self i)
  rcases finitePolygon_vertex_incident_sides Q hf i s hs with rfl | rfl
  · simp only [finitePolygonVertexOtherSide,hne,ite_false,ite_true]
  · simp only [finitePolygonVertexOtherSide,hne,ite_false,ite_true]

/-- Every actual incidence is precisely the chosen original side or its true other side. -/
theorem finitePolygonVertexOtherSide_exhaustive {m : ℕ} (Q : DiscPolygon m)
    (hf : ∀i,‖(Q.vertices i : ℂ)‖<1) (i : Fin m)
    (s t : (finiteDiscPoincarePolygon Q hf).Side)
    (hs : finitePolygonVertex Q hf i∈s.val) (ht : finitePolygonVertex Q hf i∈t.val) :
    t=s ∨t=finitePolygonVertexOtherSide Q hf i s := by
  have hne : finitePolygonSideEquiv Q hf ((finRotate m).symm i)≠finitePolygonSideEquiv Q hf i :=
    (finitePolygonSideEquiv Q hf).injective.ne (Q.prev_ne_self i)
  rcases finitePolygon_vertex_incident_sides Q hf i s hs with rfl | rfl <;>
    rcases finitePolygon_vertex_incident_sides Q hf i t ht with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (by simp only [finitePolygonVertexOtherSide,hne,ite_false])
  · exact Or.inr (by simp only [finitePolygonVertexOtherSide,ite_true])
  · exact Or.inl rfl

/-- A flag consists of a literal original finite vertex and one actual original incident side. -/
def FinitePolygonVertexFlag {m : ℕ} (Q : DiscPolygon m) (hf : ∀i,‖(Q.vertices i : ℂ)‖<1) :=
  {a : Fin m×(finiteDiscPoincarePolygon Q hf).Side|finitePolygonVertex Q hf a.1∈a.2.val}

/-- The true other-side operation is an actual permutation of original vertex-side flags. -/
def finitePolygonVertexOtherFlag {m : ℕ} (Q : DiscPolygon m)
    (hf : ∀i,‖(Q.vertices i : ℂ)‖<1) :
    FinitePolygonVertexFlag Q hf≃FinitePolygonVertexFlag Q hf :=
  Function.Involutive.toPerm (fun a=>⟨(a.val.1,finitePolygonVertexOtherSide Q hf a.val.1 a.val.2),
    finitePolygonVertexOtherSide_incident Q hf a.val.1 a.val.2⟩) (by
      intro a
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · exact finitePolygonVertexOtherSide_involutive Q hf a.val.1 a.val.2 a.property)

/-- The literal original finite cyclic side is exactly the native closed h-segment
between its two actual original endpoints. -/
theorem finitePolygonSide_eq_closedHSegment {m : ℕ} (Q : DiscPolygon m)
    (hf : ∀i,‖(Q.vertices i : ℂ)‖<1) (i : Fin m) :
    finitePolygonSide Q i=_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHSegment (finitePolygonVertex Q hf i)
      (finitePolygonVertex Q hf (finRotate m i)) := by
  ext x
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc x)∈
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment (Q.vertices i) (Q.vertices (finRotate m
      i)) ↔_
  rw [←finitePolygonVertex_coordinate Q hf i,←finitePolygonVertex_coordinate Q hf (finRotate m i),
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment_interior,_root_.LowDimensionalTopology.Geometry.Hyperbolic.isEmbedding_discToClosedModel.injective.mem_set_image]
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc x)∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHSegment
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (finitePolygonVertex Q hf i)))
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (finitePolygonVertex Q hf (finRotate m i)))) ↔_
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc]

/-- The original endpoint-transport property of a genuine side pairing. -/
def FinitePolygonPairingPreservesVertices {m : ℕ} (Q : DiscPolygon m)
    (hf : ∀i,‖(Q.vertices i : ℂ)‖<1)
    (S : PoincareSidePairing (ℍ≃ᵢℍ) (finiteDiscPoincarePolygon Q hf)) : Prop :=
  ∀i : Fin m,∀s : (finiteDiscPoincarePolygon Q hf).Side,
    finitePolygonVertex Q hf i∈s.val →∃j : Fin m,
      finitePolygonVertex Q hf j=S.element s (finitePolygonVertex Q hf i)

/-- Cross the actual original paired side at a literal original vertex-side flag. -/
def finitePolygonCrossFlagMap {m : ℕ} (Q : DiscPolygon m)
    (hf : ∀i,‖(Q.vertices i : ℂ)‖<1)
    (S : PoincareSidePairing (ℍ≃ᵢℍ) (finiteDiscPoincarePolygon Q hf))
    (hV : FinitePolygonPairingPreservesVertices Q hf S) (a : FinitePolygonVertexFlag Q hf) :
    FinitePolygonVertexFlag Q hf := by
  let j:=Classical.choose (hV a.val.1 a.val.2 a.property)
  have hj : finitePolygonVertex Q hf j=S.element a.val.2 (finitePolygonVertex Q hf a.val.1) :=
    Classical.choose_spec (hV a.val.1 a.val.2 a.property)
  refine ⟨(j,S.paired a.val.2),?_⟩
  change finitePolygonVertex Q hf j∈(S.paired a.val.2).val
  rw [hj,←S.side_image]
  exact ⟨finitePolygonVertex Q hf a.val.1,a.property,rfl⟩

theorem finitePolygonCrossFlagMap_vertex {m : ℕ} (Q : DiscPolygon m)
    (hf : ∀i,‖(Q.vertices i : ℂ)‖<1)
    (S : PoincareSidePairing (ℍ≃ᵢℍ) (finiteDiscPoincarePolygon Q hf))
    (hV : FinitePolygonPairingPreservesVertices Q hf S) (a : FinitePolygonVertexFlag Q hf) :
    finitePolygonVertex Q hf (finitePolygonCrossFlagMap Q hf S hV a).val.1=
      S.element a.val.2 (finitePolygonVertex Q hf a.val.1) :=
  Classical.choose_spec (hV a.val.1 a.val.2 a.property)

theorem finitePolygonCrossFlagMap_side {m : ℕ} (Q : DiscPolygon m)
    (hf : ∀i,‖(Q.vertices i : ℂ)‖<1)
    (S : PoincareSidePairing (ℍ≃ᵢℍ) (finiteDiscPoincarePolygon Q hf))
    (hV : FinitePolygonPairingPreservesVertices Q hf S) (a : FinitePolygonVertexFlag Q hf) :
    (finitePolygonCrossFlagMap Q hf S hV a).val.2=S.paired a.val.2 := rfl

/-- Crossing the actual paired side twice returns the exact original flag, including its original label. -/
theorem finitePolygonCrossFlagMap_involutive {m : ℕ} (Q : DiscPolygon m)
    (hf : ∀i,‖(Q.vertices i : ℂ)‖<1)
    (S : PoincareSidePairing (ℍ≃ᵢℍ) (finiteDiscPoincarePolygon Q hf))
    (hV : FinitePolygonPairingPreservesVertices Q hf S) :
    Function.Involutive (finitePolygonCrossFlagMap Q hf S hV) := by
  intro a
  apply Subtype.ext
  apply Prod.ext
  · apply finitePolygonVertex_injective Q hf
    rw [finitePolygonCrossFlagMap_vertex,finitePolygonCrossFlagMap_vertex,
      finitePolygonCrossFlagMap_side,S.element_paired]
    change (S.element a.val.2).symm ((S.element a.val.2) (finitePolygonVertex Q hf a.val.1))=_
    exact (S.element a.val.2).symm_apply_apply _
  · rw [finitePolygonCrossFlagMap_side,finitePolygonCrossFlagMap_side,S.involutive]

/-- Actual paired-side crossing is an original-label-preserving permutation of the literal flags. -/
def finitePolygonCrossFlag {m : ℕ} (Q : DiscPolygon m)
    (hf : ∀i,‖(Q.vertices i : ℂ)‖<1)
    (S : PoincareSidePairing (ℍ≃ᵢℍ) (finiteDiscPoincarePolygon Q hf))
    (hV : FinitePolygonPairingPreservesVertices Q hf S) :
    FinitePolygonVertexFlag Q hf≃FinitePolygonVertexFlag Q hf :=
  Function.Involutive.toPerm _ (finitePolygonCrossFlagMap_involutive Q hf S hV)

/-- A lifted flag retains the genuine original generated-group index. -/
def FinitePolygonFlagState {m : ℕ} (Q : DiscPolygon m) (hf : ∀i,‖(Q.vertices i : ℂ)‖<1)
    (S : PoincareSidePairing (ℍ≃ᵢℍ) (finiteDiscPoincarePolygon Q hf)) :=
  S.Generated×FinitePolygonVertexFlag Q hf

/-- Paired-side crossing of lifted flags uses the exact original Poincare copy index relation. -/
def finitePolygonCrossStateMap {m : ℕ} (Q : DiscPolygon m)
    (hf : ∀i,‖(Q.vertices i : ℂ)‖<1)
    (S : PoincareSidePairing (ℍ≃ᵢℍ) (finiteDiscPoincarePolygon Q hf))
    (hV : FinitePolygonPairingPreservesVertices Q hf S) (a : FinitePolygonFlagState Q hf S) :
    FinitePolygonFlagState Q hf S :=
  (a.1*(S.generator a.2.val.2)⁻¹,finitePolygonCrossFlagMap Q hf S hV a.2)

theorem finitePolygonCrossStateMap_involutive {m : ℕ} (Q : DiscPolygon m)
    (hf : ∀i,‖(Q.vertices i : ℂ)‖<1)
    (S : PoincareSidePairing (ℍ≃ᵢℍ) (finiteDiscPoincarePolygon Q hf))
    (hV : FinitePolygonPairingPreservesVertices Q hf S) :
    Function.Involutive (finitePolygonCrossStateMap Q hf S hV) := by
  intro a
  apply Prod.ext
  · change (a.1*(S.generator a.2.val.2)⁻¹)*
      (S.generator (finitePolygonCrossFlagMap Q hf S hV a.2).val.2)⁻¹=a.1
    rw [finitePolygonCrossFlagMap_side,S.generator_paired,inv_inv]
    group
  · exact finitePolygonCrossFlagMap_involutive Q hf S hV a.2

/-- The canonical natural vertex walk crosses its actual outgoing side and then takes the
other original incident side; its lifted state motion is genuinely invertible. -/
def finitePolygonNaturalVertexStep {m : ℕ} (Q : DiscPolygon m)
    (hf : ∀i,‖(Q.vertices i : ℂ)‖<1)
    (S : PoincareSidePairing (ℍ≃ᵢℍ) (finiteDiscPoincarePolygon Q hf))
    (hV : FinitePolygonPairingPreservesVertices Q hf S) :
    FinitePolygonFlagState Q hf S≃FinitePolygonFlagState Q hf S :=
  (Function.Involutive.toPerm _ (finitePolygonCrossStateMap_involutive Q hf S hV)).trans
    (Equiv.prodCongr (Equiv.refl _) (finitePolygonVertexOtherFlag Q hf))

/-- Forgetting the oriented side flag leaves precisely the original literal indexed polygon copy. -/
def finitePolygonFlagStateCopy {m : ℕ} (Q : DiscPolygon m)
    (hf : ∀i,‖(Q.vertices i : ℂ)‖<1)
    (S : PoincareSidePairing (ℍ≃ᵢℍ) (finiteDiscPoincarePolygon Q hf))
    (a : FinitePolygonFlagState Q hf S) : S.Copy :=
  (a.1,finitePolygonPoincareVertex Q hf a.2.val.1)

/-- Each actual natural step is the exact original side-mate copy, not an arbitrary closed walk. -/
theorem finitePolygonNaturalVertexStep_sideMate {m : ℕ} (Q : DiscPolygon m)
    (hf : ∀i,‖(Q.vertices i : ℂ)‖<1)
    (S : PoincareSidePairing (ℍ≃ᵢℍ) (finiteDiscPoincarePolygon Q hf))
    (hV : FinitePolygonPairingPreservesVertices Q hf S) (a : FinitePolygonFlagState Q hf S) :
    S.sideMateCopy (finitePolygonFlagStateCopy Q hf S a) a.2.val.2 a.2.property=
      finitePolygonFlagStateCopy Q hf S (finitePolygonNaturalVertexStep Q hf S hV a) := by
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    change S.element a.2.val.2 (finitePolygonVertex Q hf a.2.val.1)=
      finitePolygonVertex Q hf (finitePolygonCrossFlagMap Q hf S hV a.2).val.1
    exact (finitePolygonCrossFlagMap_vertex Q hf S hV a.2).symm

/-- The incoming side of the canonical next flag is exactly the original paired outgoing side. -/
theorem finitePolygonNaturalVertexStep_incoming {m : ℕ} (Q : DiscPolygon m)
    (hf : ∀i,‖(Q.vertices i : ℂ)‖<1)
    (S : PoincareSidePairing (ℍ≃ᵢℍ) (finiteDiscPoincarePolygon Q hf))
    (hV : FinitePolygonPairingPreservesVertices Q hf S) (a : FinitePolygonFlagState Q hf S) :
    finitePolygonVertexOtherSide Q hf
      (finitePolygonNaturalVertexStep Q hf S hV a).2.val.1
      (finitePolygonNaturalVertexStep Q hf S hV a).2.val.2=S.paired a.2.val.2 := by
  change finitePolygonVertexOtherSide Q hf (finitePolygonCrossFlagMap Q hf S hV a.2).val.1
    (finitePolygonVertexOtherSide Q hf (finitePolygonCrossFlagMap Q hf S hV a.2).val.1
      (finitePolygonCrossFlagMap Q hf S hV a.2).val.2)=S.paired a.2.val.2
  rw [finitePolygonVertexOtherSide_involutive,finitePolygonCrossFlagMap_side]
  exact (finitePolygonCrossFlagMap Q hf S hV a.2).property

/-- The actual inverse-pair identity reverses any explicitly specified original side step. -/
theorem finitePolygon_sideMate_reverse {m : ℕ} (Q : DiscPolygon m)
    (hf : ∀i,‖(Q.vertices i : ℂ)‖<1)
    (S : PoincareSidePairing (ℍ≃ᵢℍ) (finiteDiscPoincarePolygon Q hf))
    (a b : S.Copy) (s : (finiteDiscPoincarePolygon Q hf).Side)
    (ha : a.2.val∈s.val) (hb : b.2.val∈(S.paired s).val) (he : S.sideMateCopy a s ha=b) :
    S.sideMateCopy b (S.paired s) hb=a := by
  subst b
  exact S.sideMateCopy_paired a s ha

/-- Every actual original incidence of a bidirectionally invariant natural-state family
stays in that actual family; no saturation or full gluing-class conclusion is assumed. -/
theorem finitePolygonNaturalVertexStep_incidence_closed {m : ℕ} (Q : DiscPolygon m)
    (hf : ∀i,‖(Q.vertices i : ℂ)‖<1)
    (S : PoincareSidePairing (ℍ≃ᵢℍ) (finiteDiscPoincarePolygon Q hf))
    (hV : FinitePolygonPairingPreservesVertices Q hf S)
    (U : Set (FinitePolygonFlagState Q hf S))
    (hnext : ∀a∈U,finitePolygonNaturalVertexStep Q hf S hV a∈U)
    (hprev : ∀a∈U,(finitePolygonNaturalVertexStep Q hf S hV).symm a∈U)
    (a : FinitePolygonFlagState Q hf S) (ha : a∈U)
    (s : (finiteDiscPoincarePolygon Q hf).Side)
    (hs : (finitePolygonFlagStateCopy Q hf S a).2.val∈s.val) :
    S.sideMateCopy (finitePolygonFlagStateCopy Q hf S a) s hs∈
      finitePolygonFlagStateCopy Q hf S '' U := by
  let σ:=finitePolygonNaturalVertexStep Q hf S hV
  rcases finitePolygonVertexOtherSide_exhaustive Q hf a.2.val.1 a.2.val.2 s a.2.property hs with hout | hin
  · subst s
    exact ⟨σ a,hnext a ha,(finitePolygonNaturalVertexStep_sideMate Q hf S hV a).symm⟩
  · let b:=σ.symm a
    have hb : b∈U:=hprev a ha
    have hba : σ b=a:=σ.apply_symm_apply a
    have hi : finitePolygonVertexOtherSide Q hf a.2.val.1 a.2.val.2=S.paired b.2.val.2 := by
      rw [←hba]
      exact finitePolygonNaturalVertexStep_incoming Q hf S hV b
    have hsEq : s=S.paired b.2.val.2:=hin.trans hi
    have hMate : S.sideMateCopy (finitePolygonFlagStateCopy Q hf S b) b.2.val.2 b.2.property=
        finitePolygonFlagStateCopy Q hf S a := by
      rw [finitePolygonNaturalVertexStep_sideMate Q hf S hV b,hba]
    refine ⟨b,hb,?_⟩
    cases hsEq
    exact (finitePolygon_sideMate_reverse Q hf S _ _ _ b.2.property hs hMate).symm

/-- A finite natural lifted-state family proves finiteness of the entire original quotient class;
the incoming and outgoing original incidences are derived from the canonical state motion. -/
theorem finitePolygonNaturalVertexStep_finite_fiber {m : ℕ} (Q : DiscPolygon m)
    (hf : ∀i,‖(Q.vertices i : ℂ)‖<1)
    (S : PoincareSidePairing (ℍ≃ᵢℍ) (finiteDiscPoincarePolygon Q hf))
    (hV : FinitePolygonPairingPreservesVertices Q hf S)
    (U : Set (FinitePolygonFlagState Q hf S)) (hU : U.Finite)
    (hnext : ∀a∈U,finitePolygonNaturalVertexStep Q hf S hV a∈U)
    (hprev : ∀a∈U,(finitePolygonNaturalVertexStep Q hf S hV).symm a∈U)
    (a : FinitePolygonFlagState Q hf S) (ha : a∈U) :
    (S.project ⁻¹' {S.project (finitePolygonFlagStateCopy Q hf S a)}).Finite := by
  apply S.finite_project_fiber_of_step_closed (finitePolygonFlagStateCopy Q hf S '' U)
    (hU.image _) _ (mem_image_of_mem _ ha)
  rintro b ⟨c,hc,rfl⟩ d hd
  rcases hd with he | ⟨s,hs,hy,hg⟩
  · exact he ▸ mem_image_of_mem _ hc
  · have he:=S.sideMateCopy_eq_of_side_step _ d s hs hy hg
    rw [←he]
    exact finitePolygonNaturalVertexStep_incidence_closed Q hf S hV U hnext hprev c hc s hs

/-- A genuine periodic permutation orbit has its literal cyclic successor at every finite index. -/
theorem equiv_iterate_finRotate_of_period {A : Type*} (e : A≃A) (a : A) (n : ℕ)
    (hclose : (e^[n+1]) a=a) (i : Fin (n+1)) :
    e ((e^[i.val]) a)=(e^[(finRotate (n+1) i).val]) a := by
  refine Fin.lastCases ?_ (fun j=>?_) i
  · rw [finRotate_last]
    simpa only [Fin.val_last,Fin.val_zero,Function.iterate_zero_apply,
      Function.iterate_succ_apply'] using hclose
  · have he : finRotate (n+1) j.castSucc=j.succ:=finRotate_of_lt j.isLt
    rw [he]
    exact (Function.iterate_succ_apply' e j.val a).symm

/-- A literal finite periodic permutation orbit is closed under both true successor and predecessor. -/
theorem equiv_periodic_range_invariant {A : Type*} (e : A≃A) (a : A) (n : ℕ)
    (hclose : (e^[n+1]) a=a) :
    (∀b∈range (fun i : Fin (n+1)=>(e^[i.val]) a),e b∈range (fun i : Fin (n+1)=>(e^[i.val]) a)) ∧
    (∀b∈range (fun i : Fin (n+1)=>(e^[i.val]) a),e.symm b∈range (fun i : Fin (n+1)=>(e^[i.val]) a)) := by
  constructor
  · rintro b ⟨i,rfl⟩
    exact ⟨finRotate (n+1) i,(equiv_iterate_finRotate_of_period e a n hclose i).symm⟩
  · rintro b ⟨i,rfl⟩
    let j:=(finRotate (n+1)).symm i
    refine ⟨j,?_⟩
    apply e.injective
    rw [e.apply_symm_apply]
    have hh:=equiv_iterate_finRotate_of_period e a n hclose j
    rw [(finRotate (n+1)).apply_symm_apply i] at hh
    exact hh

/-- An actual periodic canonical natural walk has a finite entire original glued class;
this is proved from its original side motion without any prior class finiteness assumption. -/
theorem finitePolygonNaturalVertexStep_periodic_fiber {m : ℕ} (Q : DiscPolygon m)
    (hf : ∀i,‖(Q.vertices i : ℂ)‖<1)
    (S : PoincareSidePairing (ℍ≃ᵢℍ) (finiteDiscPoincarePolygon Q hf))
    (hV : FinitePolygonPairingPreservesVertices Q hf S)
    (a : FinitePolygonFlagState Q hf S) (n : ℕ)
    (hclose : ((finitePolygonNaturalVertexStep Q hf S hV)^[n+1]) a=a) :
    (S.project ⁻¹' {S.project (finitePolygonFlagStateCopy Q hf S a)}).Finite := by
  let σ:=finitePolygonNaturalVertexStep Q hf S hV
  let U:Set (FinitePolygonFlagState Q hf S):=range (fun i : Fin (n+1)=>(σ^[i.val]) a)
  obtain ⟨hnext,hprev⟩:=equiv_periodic_range_invariant σ a n hclose
  exact finitePolygonNaturalVertexStep_finite_fiber Q hf S hV U (Set.finite_range _) hnext hprev a ⟨0,rfl⟩

/-- The exact original side-crossing equations of the canonical natural vertex step. -/
theorem finitePolygonNaturalVertexStep_side_step {m : ℕ} (Q : DiscPolygon m)
    (hf : ∀i,‖(Q.vertices i : ℂ)‖<1)
    (S : PoincareSidePairing (ℍ≃ᵢℍ) (finiteDiscPoincarePolygon Q hf))
    (hV : FinitePolygonPairingPreservesVertices Q hf S) (a : FinitePolygonFlagState Q hf S) :
    ∃s : (finiteDiscPoincarePolygon Q hf).Side,
      (finitePolygonFlagStateCopy Q hf S a).2.val∈s.val ∧
      (finitePolygonFlagStateCopy Q hf S (finitePolygonNaturalVertexStep Q hf S hV a)).2.val=
        S.generator s •(finitePolygonFlagStateCopy Q hf S a).2.val ∧
      (finitePolygonFlagStateCopy Q hf S a).1=
        (finitePolygonFlagStateCopy Q hf S (finitePolygonNaturalVertexStep Q hf S hV a)).1*S.generator s := by
  refine ⟨a.2.val.2,a.2.property,?_,?_⟩
  · have he:=congrArg (fun b : S.Copy=>b.2.val) (finitePolygonNaturalVertexStep_sideMate Q hf S hV a)
    exact he.symm
  · change a.1=(a.1*(S.generator a.2.val.2)⁻¹)*S.generator a.2.val.2
    group

/-- A complete actual periodic natural vertex walk and its original ball-cover/nonoverlap
clauses construct the original finite VertexCycle, retaining its exact original side steps. -/
def finitePolygonNaturalVertexCycle {m : ℕ} (Q : DiscPolygon m)
    (hf : ∀i,‖(Q.vertices i : ℂ)‖<1)
    (S : PoincareSidePairing (ℍ≃ᵢℍ) (finiteDiscPoincarePolygon Q hf))
    (hV : FinitePolygonPairingPreservesVertices Q hf S)
    (f : FinitePolygonVertexFlag Q hf) (n : ℕ) (r : ℝ) (hr : 0<r)
    (hclose : ((finitePolygonNaturalVertexStep Q hf S hV)^[n+1]) (1,f)=(1,f))
    (hcover : (⋃j : Fin (n+1),S.vertexCyclePiece
      (finitePolygonFlagStateCopy Q hf S (((finitePolygonNaturalVertexStep Q hf S hV)^[j.val]) (1,f))) r)=
        Metric.ball (finitePolygonVertex Q hf f.val.1) r)
    (hdisj : Pairwise (fun (i j : Fin (n+1))=>Disjoint
      (S.vertexCycleInteriorPiece (finitePolygonFlagStateCopy Q hf S
        (((finitePolygonNaturalVertexStep Q hf S hV)^[i.val]) (1,f))) r)
      (S.vertexCycleInteriorPiece (finitePolygonFlagStateCopy Q hf S
        (((finitePolygonNaturalVertexStep Q hf S hV)^[j.val]) (1,f))) r))) :
    S.VertexCycle {p : (finiteDiscPoincarePolygon Q hf).Point|p.val∈range (finitePolygonVertex Q hf)}
      (finitePolygonPoincareVertex Q hf f.val.1) r where
  radius_pos:=hr
  lengthPred:=n
  copies j:=finitePolygonFlagStateCopy Q hf S (((finitePolygonNaturalVertexStep Q hf S hV)^[j.val]) (1,f))
  base:=rfl
  vertices j:=⟨_,rfl⟩
  adjacent j:=by
    have h:=finitePolygonNaturalVertexStep_side_step Q hf S hV
      (((finitePolygonNaturalVertexStep Q hf S hV)^[j.val]) (1,f))
    simpa only [Fin.val_castSucc,Fin.val_succ,Function.iterate_succ_apply'] using h
  closing:=by
    let σ:=finitePolygonNaturalVertexStep Q hf S hV
    have he : σ ((σ^[n]) (1,f))=(1,f):=by
      simpa only [Function.iterate_succ_apply'] using hclose
    have h:=finitePolygonNaturalVertexStep_side_step Q hf S hV ((σ^[n]) (1,f))
    rw [he] at h
    exact h
  covers:=hcover
  nonoverlap:=hdisj

/-- A complete natural finite period exhausts both original side incidences at every actual
cycle position; this is a proved property of the original side motion, not an extra cycle hypothesis. -/
theorem finitePolygonNaturalVertexStep_periodic_incidence {m : ℕ} (Q : DiscPolygon m)
    (hf : ∀i,‖(Q.vertices i : ℂ)‖<1)
    (S : PoincareSidePairing (ℍ≃ᵢℍ) (finiteDiscPoincarePolygon Q hf))
    (hV : FinitePolygonPairingPreservesVertices Q hf S)
    (a : FinitePolygonFlagState Q hf S) (n : ℕ)
    (hclose : ((finitePolygonNaturalVertexStep Q hf S hV)^[n+1]) a=a)
    (i : Fin (n+1)) (s : (finiteDiscPoincarePolygon Q hf).Side)
    (hs : (finitePolygonFlagStateCopy Q hf S
      (((finitePolygonNaturalVertexStep Q hf S hV)^[i.val]) a)).2.val∈s.val) :
    S.sideMateCopy (finitePolygonFlagStateCopy Q hf S
      (((finitePolygonNaturalVertexStep Q hf S hV)^[i.val]) a)) s hs∈
      range (fun j : Fin (n+1)=>finitePolygonFlagStateCopy Q hf S
        (((finitePolygonNaturalVertexStep Q hf S hV)^[j.val]) a)) := by
  let σ:=finitePolygonNaturalVertexStep Q hf S hV
  let U:Set (FinitePolygonFlagState Q hf S):=range (fun j : Fin (n+1)=>(σ^[j.val]) a)
  obtain ⟨hnext,hprev⟩:=equiv_periodic_range_invariant σ a n hclose
  obtain ⟨b,⟨j,rfl⟩,he⟩:=finitePolygonNaturalVertexStep_incidence_closed Q hf S hV U hnext hprev
    ((σ^[i.val]) a) ⟨i,rfl⟩ s hs
  exact ⟨j,he⟩

/-- Every actual original native side pairing sends original finite polygon endpoints to
actual original endpoints, by its true segment image and native isometry alone. -/
theorem finitePolygonPairing_preserves_vertices {m : ℕ} (Q : DiscPolygon m)
    (hf : ∀i,‖(Q.vertices i : ℂ)‖<1)
    (S : PoincareSidePairing (ℍ≃ᵢℍ) (finiteDiscPoincarePolygon Q hf)) :
    FinitePolygonPairingPreservesVertices Q hf S := by
  intro i s hi
  let e:=finitePolygonSideEquiv Q hf
  let j:=e.symm s
  let k:=e.symm (S.paired s)
  have hs : finitePolygonSide Q j=s.val:=congrArg Subtype.val (e.apply_symm_apply s)
  have hp : finitePolygonSide Q k=(S.paired s).val:=congrArg Subtype.val (e.apply_symm_apply (S.paired s))
  have hImage : (S.element s) '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHSegment (finitePolygonVertex Q
    hf j)
      (finitePolygonVertex Q hf (finRotate m j))=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHSegment (finitePolygonVertex Q hf k) (finitePolygonVertex Q hf (finRotate m k)) := by
    rw [←finitePolygonSide_eq_closedHSegment Q hf j,←finitePolygonSide_eq_closedHSegment Q hf k,hs,hp]
    exact S.side_image s
  have hEndpoints:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.native_closedHSegment_image_endpoints (S.element s)
    (finitePolygonVertex Q hf j) (finitePolygonVertex Q hf (finRotate m j))
    (finitePolygonVertex Q hf k) (finitePolygonVertex Q hf (finRotate m k)) hImage
  have hmem : S.element s (finitePolygonVertex Q hf i)∈
      ({S.element s (finitePolygonVertex Q hf j),S.element s (finitePolygonVertex Q hf (finRotate m j))}:Set ℍ) := by
    have hij : finitePolygonVertex Q hf i∈finitePolygonSide Q j:=hs.symm ▸ hi
    rcases (finitePolygonVertex_side_iff Q hf i j).mp hij with hj | hj
    · have hNext : finRotate m j=i :=by rw [hj,(finRotate m).apply_symm_apply]
      rw [hNext]
      exact Or.inr rfl
    · rw [hj]
      exact Or.inl rfl
  rw [hEndpoints] at hmem
  rcases hmem with h | h
  · exact ⟨k,h.symm⟩
  · exact ⟨finRotate m k,h.symm⟩

/-- The actual canonical natural step for any given original side pairing, with endpoint
transport proved from the original true segment image and no extra vertex-map hypothesis. -/
def finitePolygonCanonicalVertexStep {m : ℕ} (Q : DiscPolygon m)
    (hf : ∀i,‖(Q.vertices i : ℂ)‖<1)
    (S : PoincareSidePairing (ℍ≃ᵢℍ) (finiteDiscPoincarePolygon Q hf)) :
    FinitePolygonFlagState Q hf S≃FinitePolygonFlagState Q hf S :=
  finitePolygonNaturalVertexStep Q hf S (finitePolygonPairing_preserves_vertices Q hf S)

/-- A genuine original canonical period alone gives a finite whole gluing class,
without assuming endpoint transport, incidence exhaustion or class finiteness. -/
theorem finitePolygonCanonicalVertexCycle_finite_fiber {m : ℕ} (Q : DiscPolygon m)
    (hf : ∀i,‖(Q.vertices i : ℂ)‖<1)
    (S : PoincareSidePairing (ℍ≃ᵢℍ) (finiteDiscPoincarePolygon Q hf))
    (a : FinitePolygonFlagState Q hf S) (n : ℕ)
    (hclose : ((finitePolygonCanonicalVertexStep Q hf S)^[n+1]) a=a) :
    (S.project ⁻¹' {S.project (finitePolygonFlagStateCopy Q hf S a)}).Finite :=
  finitePolygonNaturalVertexStep_periodic_fiber Q hf S
    (finitePolygonPairing_preserves_vertices Q hf S) a n hclose

/-- The literal original canonical cycle automatically exhausts every original side incidence. -/
theorem finitePolygonCanonicalVertexCycle_incidence {m : ℕ} (Q : DiscPolygon m)
    (hf : ∀i,‖(Q.vertices i : ℂ)‖<1)
    (S : PoincareSidePairing (ℍ≃ᵢℍ) (finiteDiscPoincarePolygon Q hf))
    (a : FinitePolygonFlagState Q hf S) (n : ℕ)
    (hclose : ((finitePolygonCanonicalVertexStep Q hf S)^[n+1]) a=a)
    (i : Fin (n+1)) (s : (finiteDiscPoincarePolygon Q hf).Side)
    (hs : (finitePolygonFlagStateCopy Q hf S
      (((finitePolygonCanonicalVertexStep Q hf S)^[i.val]) a)).2.val∈s.val) :
    S.sideMateCopy (finitePolygonFlagStateCopy Q hf S
      (((finitePolygonCanonicalVertexStep Q hf S)^[i.val]) a)) s hs∈
      range (fun j : Fin (n+1)=>finitePolygonFlagStateCopy Q hf S
        (((finitePolygonCanonicalVertexStep Q hf S)^[j.val]) a)) :=
  finitePolygonNaturalVertexStep_periodic_incidence Q hf S
    (finitePolygonPairing_preserves_vertices Q hf S) a n hclose i s hs

/-- A closed canonical flag cycle with ball coverage and disjoint interior pieces
has a finite project fiber and a local tessellation radius. Nonvertex paired-side
neighborhoods supply the regularity assumption. -/
theorem finitePolygonCanonicalVertexCycle_local_radius {m : ℕ} (Q : DiscPolygon m)
    (hf : ∀i,‖(Q.vertices i : ℂ)‖<1)
    (S : PoincareSidePairing (ℍ≃ᵢℍ) (finiteDiscPoincarePolygon Q hf))
    (f : FinitePolygonVertexFlag Q hf) (n : ℕ) (r : ℝ) (hr : 0<r)
    (hclose : ((finitePolygonCanonicalVertexStep Q hf S)^[n+1]) (1,f)=(1,f))
    (hcover : (⋃j : Fin (n+1),S.vertexCyclePiece
      (finitePolygonFlagStateCopy Q hf S (((finitePolygonCanonicalVertexStep Q hf S)^[j.val]) (1,f))) r)=
        Metric.ball (finitePolygonVertex Q hf f.val.1) r)
    (hdisj : Pairwise (fun (i j : Fin (n+1))=>Disjoint
      (S.vertexCycleInteriorPiece (finitePolygonFlagStateCopy Q hf S
        (((finitePolygonCanonicalVertexStep Q hf S)^[i.val]) (1,f))) r)
      (S.vertexCycleInteriorPiece (finitePolygonFlagStateCopy Q hf S
        (((finitePolygonCanonicalVertexStep Q hf S)^[j.val]) (1,f))) r)))
    (hReg : ∀p : (finiteDiscPoincarePolygon Q hf).Point,p.val∉range (finitePolygonVertex Q hf) →
      p.val∈(finiteDiscPoincarePolygon Q hf).interior ∨∃s : (finiteDiscPoincarePolygon Q hf).Side,
        ∃ρ : ℝ,S.PairedSideNeighborhood p s ρ) :
    (S.project ⁻¹' {S.project (1,finitePolygonPoincareVertex Q hf f.val.1)}).Finite ∧
      ∃r₀ : ℝ,0<r₀ ∧ ∀t : ℝ,0<t → t ≤ r₀ →
        S.LocalTessellation (1,finitePolygonPoincareVertex Q hf f.val.1) t := by
  let : IsIsometricSMul S.Generated ℍ:=⟨fun g=>g.val.isometry⟩
  let hV:=finitePolygonPairing_preserves_vertices Q hf S
  let c:=finitePolygonNaturalVertexCycle Q hf S hV f n r hr hclose hcover hdisj
  have hc : ∀i : Fin (c.lengthPred+1),∀s : (finiteDiscPoincarePolygon Q hf).Side,
      ∀hs : (c.copies i).2.val∈s.val,S.sideMateCopy (c.copies i) s hs∈range c.copies := by
    intro i s hs
    exact finitePolygonCanonicalVertexCycle_incidence Q hf S (1,f) n hclose i s hs
  exact c.local_radius_of_locally_finite_sides S (range (finitePolygonVertex Q hf))
    (finitePolygonVertices_isDiscrete Q hf) (finiteDiscPoincarePolygon_locallyFiniteSides Q hf)
    (finiteDiscPoincarePolygon_closedSides Q hf) (finiteDiscPoincarePolygon_interior_isOpen Q hf)
    (finiteDiscPoincarePolygon_carrier Q hf).le hReg hc

end LowDimensionalTopology.Geometry.Polygon
