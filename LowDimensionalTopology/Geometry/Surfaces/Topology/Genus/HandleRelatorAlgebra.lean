/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Surfaces.Topology.Genus.HandleBoundaryWedge
public import LowDimensionalTopology.External.LiZhongQC.Ch06.S22_RiemannSurfaces
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Data.List.OfFn
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Tactic.FinCases

/-!
# Algebra of the oriented handle boundary

Positive geometric edges are sent to inverse standard generators. This convention
accounts for the order reversal between chronological path concatenation and the
endomorphism-group product. Inverting the entire boundary relator leaves its normal
closure unchanged. The resulting presentation is the existing `LiZhongQC.surfaceGroup`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Surfaces.HandlePresentation

/-- The standard a- and b-labels, in the same order as the existing surface presentation. -/
abbrev StandardLabels (g : ℕ) := Fin g ⊕ Fin g

/-- The positive geometric a- and b-sides have precisely the standard labels. -/
def edgeLabelEquiv (g : ℕ) : Edge g ≃ StandardLabels g where
  toFun d := if d.2 = 0 then Sum.inl d.1 else Sum.inr d.1
  invFun := Sum.elim (fun i => (i, 0)) (fun i => (i, 1))
  left_inv := by
    rintro ⟨i, j⟩
    fin_cases j <;> simp
  right_inv := by
    intro d
    cases d <;> simp

@[simp] theorem edgeLabelEquiv_a {g : ℕ} (i : Fin g) :
    edgeLabelEquiv g (i, 0) = Sum.inl i := by
  simp [edgeLabelEquiv]

@[simp] theorem edgeLabelEquiv_b {g : ℕ} (i : Fin g) :
    edgeLabelEquiv g (i, 1) = Sum.inr i := by
  simp [edgeLabelEquiv]

/-- Relabeling and inverting each free generator is a genuine group isomorphism.
It is not inversion of arbitrary group elements, which would reverse products. -/
def generatorInvertingCongr {α β : Type*} (e : α ≃ β) :
    FreeGroup α ≃* FreeGroup β where
  toFun := FreeGroup.lift (fun a => (FreeGroup.of (e a))⁻¹)
  invFun := FreeGroup.lift (fun b => (FreeGroup.of (e.symm b))⁻¹)
  left_inv x := by
    have h :
        (FreeGroup.lift (fun b => (FreeGroup.of (e.symm b))⁻¹)).comp
          (FreeGroup.lift (fun a => (FreeGroup.of (e a))⁻¹)) =
            MonoidHom.id (FreeGroup α) := by
      apply FreeGroup.ext_hom
      intro a
      simp
    exact DFunLike.congr_fun h x
  right_inv x := by
    have h :
        (FreeGroup.lift (fun a => (FreeGroup.of (e a))⁻¹)).comp
          (FreeGroup.lift (fun b => (FreeGroup.of (e.symm b))⁻¹)) =
            MonoidHom.id (FreeGroup β) := by
      apply FreeGroup.ext_hom
      intro b
      simp
    exact DFunLike.congr_fun h x
  map_mul' := (FreeGroup.lift (fun a => (FreeGroup.of (e a))⁻¹)).map_mul

@[simp] theorem generatorInvertingCongr_of {α β : Type*} (e : α ≃ β) (a : α) :
    generatorInvertingCongr e (FreeGroup.of a) = (FreeGroup.of (e a))⁻¹ := by
  change (FreeGroup.lift (fun x : α => (FreeGroup.of (e x))⁻¹)) (FreeGroup.of a) = _
  exact FreeGroup.lift_apply_of

@[simp] theorem generatorInvertingCongr_symm_of {α β : Type*} (e : α ≃ β) (b : β) :
    (generatorInvertingCongr e).symm (FreeGroup.of b) =
      (FreeGroup.of (e.symm b))⁻¹ := by
  change (FreeGroup.lift (fun x : β => (FreeGroup.of (e.symm x))⁻¹)) (FreeGroup.of b) = _
  exact FreeGroup.lift_apply_of

/-- The free-group isomorphism appropriate to the actual polygon's positive sides. -/
def edgeFreeGroupEquiv (g : ℕ) : FreeGroup (Edge g) ≃* FreeGroup (StandardLabels g) :=
  generatorInvertingCongr (edgeLabelEquiv g)

@[simp] theorem edgeFreeGroupEquiv_of {g : ℕ} (d : Edge g) :
    edgeFreeGroupEquiv g (FreeGroup.of d) = (FreeGroup.of (edgeLabelEquiv g d))⁻¹ :=
  generatorInvertingCongr_of _ _

@[simp] theorem edgeFreeGroupEquiv_a {g : ℕ} (i : Fin g) :
    edgeFreeGroupEquiv g (FreeGroup.of (i, 0)) =
      (FreeGroup.of (Sum.inl i : StandardLabels g))⁻¹ := by
  simp

@[simp] theorem edgeFreeGroupEquiv_b {g : ℕ} (i : Fin g) :
    edgeFreeGroupEquiv g (FreeGroup.of (i, 1)) =
      (FreeGroup.of (Sum.inr i : StandardLabels g))⁻¹ := by
  simp

/-- The literal ordered commutator product used in the existing surface group. -/
def standardRelator (g : ℕ) : FreeGroup (StandardLabels g) :=
  (List.ofFn fun i : Fin g =>
    FreeGroup.of (Sum.inl i : Fin g ⊕ Fin g) * FreeGroup.of (Sum.inr i) *
      (FreeGroup.of (Sum.inl i))⁻¹ * (FreeGroup.of (Sum.inr i))⁻¹).prod

/-- The commutator product in positively oriented geometric edge generators. -/
def inverseBoundaryEdgeWord (g : ℕ) : FreeGroup (Edge g) :=
  (List.ofFn fun i : Fin g =>
    (FreeGroup.of (i, (0 : Fin 2)))⁻¹ * (FreeGroup.of (i, (1 : Fin 2)))⁻¹ *
      FreeGroup.of (i, (0 : Fin 2)) * FreeGroup.of (i, (1 : Fin 2))).prod

/-- Generator inversion turns the inverse boundary word into the standard relator. -/
@[simp] theorem edgeFreeGroupEquiv_inverseBoundaryEdgeWord (g : ℕ) :
    edgeFreeGroupEquiv g (inverseBoundaryEdgeWord g) = standardRelator g := by
  unfold inverseBoundaryEdgeWord standardRelator
  rw [map_list_prod, List.map_ofFn]
  apply congrArg List.prod
  apply congrArg List.ofFn
  funext i
  simp only [Function.comp_apply, map_mul, map_inv, edgeFreeGroupEquiv_a,
    edgeFreeGroupEquiv_b, inv_inv]

/-- The whole boundary word therefore maps to the inverse of the standard relator. -/
@[simp] theorem edgeFreeGroupEquiv_boundaryEdgeWord (g : ℕ) :
    edgeFreeGroupEquiv g ((inverseBoundaryEdgeWord g)⁻¹) = (standardRelator g)⁻¹ := by
  rw [map_inv, edgeFreeGroupEquiv_inverseBoundaryEdgeWord]

/-- A relator and its inverse generate exactly the same normal subgroup. -/
theorem normalClosure_singleton_inv {G : Type*} [Group G] (r : G) :
    Subgroup.normalClosure ({r⁻¹} : Set G) = Subgroup.normalClosure ({r} : Set G) := by
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    intro x hx
    have hx' : x = r⁻¹ := Set.mem_singleton_iff.mp hx
    rw [hx']
    exact (Subgroup.normalClosure ({r} : Set G)).inv_mem
      (Subgroup.subset_normalClosure (Set.mem_singleton r))
  · apply Subgroup.normalClosure_le_normal
    intro x hx
    have hx' : x = r := Set.mem_singleton_iff.mp hx
    rw [hx']
    have hr : r⁻¹ ∈ Subgroup.normalClosure ({r⁻¹} : Set G) :=
      Subgroup.subset_normalClosure (Set.mem_singleton (r⁻¹))
    change r ∈ Subgroup.normalClosure ({r⁻¹} : Set G)
    exact (Subgroup.inv_mem_iff (Subgroup.normalClosure ({r⁻¹} : Set G))).mp hr

/-- Quotienting by the inverse relator recovers the actual existing surface group. -/
def inverseRelatorQuotientEquivSurfaceGroup (g : ℕ) :
    PresentedGroup ({(standardRelator g)⁻¹} : Set (FreeGroup (StandardLabels g))) ≃*
      LiZhongQC.surfaceGroup g := by
  change
    (FreeGroup (StandardLabels g) ⧸
      Subgroup.normalClosure ({(standardRelator g)⁻¹} : Set _)) ≃*
    (FreeGroup (StandardLabels g) ⧸
      Subgroup.normalClosure ({standardRelator g} : Set _))
  exact QuotientGroup.quotientMulEquivOfEq (normalClosure_singleton_inv (standardRelator g))

@[simp] theorem inverseRelatorQuotientEquivSurfaceGroup_mk (g : ℕ)
    (x : FreeGroup (StandardLabels g)) :
    inverseRelatorQuotientEquivSurfaceGroup g
      (PresentedGroup.mk ({(standardRelator g)⁻¹} : Set _) x) =
        (PresentedGroup.mk ({standardRelator g} : Set _) x : LiZhongQC.surfaceGroup g) :=
  rfl

/-- Relabeling the actual geometric free group transports a concrete boundary relation.
The word identity is supplied by the geometric boundary-path calculation. -/
def quotientByEdgeRelatorEquivSurfaceGroup (g : ℕ) (w : FreeGroup (Edge g))
    (hw : edgeFreeGroupEquiv g w = (standardRelator g)⁻¹) :
    PresentedGroup ({w} : Set (FreeGroup (Edge g))) ≃* LiZhongQC.surfaceGroup g := by
  refine (QuotientGroup.congr
    (Subgroup.normalClosure ({w} : Set (FreeGroup (Edge g))))
    (Subgroup.normalClosure ({(standardRelator g)⁻¹} :
      Set (FreeGroup (StandardLabels g)))) (edgeFreeGroupEquiv g) ?_).trans
        (inverseRelatorQuotientEquivSurfaceGroup g)
  change (Subgroup.normalClosure ({w} : Set (FreeGroup (Edge g)))).map
    (edgeFreeGroupEquiv g).toMonoidHom = _
  calc _ = Subgroup.normalClosure ((edgeFreeGroupEquiv g).toMonoidHom '' {w}) :=
      Subgroup.map_normalClosure _ (edgeFreeGroupEquiv g).toMonoidHom
        (edgeFreeGroupEquiv g).surjective
    _ = _ := by
      rw [Set.image_singleton]
      change Subgroup.normalClosure ({edgeFreeGroupEquiv g w} :
        Set (FreeGroup (StandardLabels g))) = _
      exact congrArg (fun x : FreeGroup (StandardLabels g) =>
        Subgroup.normalClosure ({x} : Set (FreeGroup (StandardLabels g)))) hw

@[simp] theorem quotientByEdgeRelatorEquivSurfaceGroup_mk (g : ℕ)
    (w : FreeGroup (Edge g)) (hw : edgeFreeGroupEquiv g w = (standardRelator g)⁻¹)
    (x : FreeGroup (Edge g)) :
    quotientByEdgeRelatorEquivSurfaceGroup g w hw (PresentedGroup.mk ({w} : Set _) x) =
      (PresentedGroup.mk ({standardRelator g} : Set _) (edgeFreeGroupEquiv g x) :
        LiZhongQC.surfaceGroup g) :=
  rfl

/-- The concrete geometric boundary presentation has the standard surface group. -/
def boundaryEdgePresentationEquivSurfaceGroup (g : ℕ) :
    PresentedGroup ({(inverseBoundaryEdgeWord g)⁻¹} : Set (FreeGroup (Edge g))) ≃*
      LiZhongQC.surfaceGroup g :=
  quotientByEdgeRelatorEquivSurfaceGroup g _ (edgeFreeGroupEquiv_boundaryEdgeWord g)

end LowDimensionalTopology.Geometry.Surfaces.HandlePresentation
