/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Hyperboloid.Basic
public import LowDimensionalTopology.Geometry.Inversive.UnitBall.Subgroup
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Hyperboloid.Isometry
public import LowDimensionalTopology.Geometry.Inversive.UnitBall.TranslationCoordinates
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Ball.IsometryClassification
public import Mathlib.Topology.Algebra.Group.Matrix
public import Mathlib.Topology.Algebra.Group.OpenMapping
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Star.Unitary
public import Mathlib.Topology.Baire.LocallyCompactRegular
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Lorentz matrices and the topology of the actual Möbius group

The finite-frame proof uses right multiplication of row vectors; taking the inverse of that matrix gives a homomorphism for the standard left composition of maps. Both sides carry their native, previously established topologies.
-/

@[expose] public section
noncomputable section
open Set Matrix Filter Topology Module
open scoped MatrixGroups InnerProductSpace
namespace LowDimensionalTopology.Geometry.Hyperbolic
variable {n : ℕ}

instance lorentzMatrix_locallyCompactSpace (n : ℕ) :
    LocallyCompactSpace (Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :=
  inferInstanceAs (LocallyCompactSpace (Fin (n+1) → Fin (n+1) → ℝ))

instance lorentzMatrix_sigmaCompactSpace (n : ℕ) :
    SigmaCompactSpace (Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :=
  inferInstanceAs (SigmaCompactSpace (Fin (n+1) → Fin (n+1) → ℝ))

/-- The positive Lorentz condition is closed because its time entry is at least one. -/
theorem lorentzPositive_time_ge_one {A : GL (Fin (n+1)) ℝ}
    (hA : A ∈ lorentzPositiveOrthogonalGroup n) : 1 ≤ A 0 0 := by
  obtain ⟨hO,hp⟩ := (mem_lorentzPositiveOrthogonalGroup A).mp hA
  have h := lorentzOrthogonal_preserves_form hO (lorentzTimeUnit n) (lorentzTimeUnit n)
  rw [lorentzForm_self,lorentzRowLinearMap_timeUnit_time] at h
  have hq : A 0 0 ^ 2 - ‖(lorentzRowLinearMap A.val (lorentzTimeUnit n)).2‖ ^ 2 = 1 := by
    simpa [lorentzTimeUnit,lorentzForm] using h
  nlinarith [sq_nonneg ‖(lorentzRowLinearMap A.val (lorentzTimeUnit n)).2‖]

theorem lorentzPositiveOrthogonalGroup_isClosed (n : ℕ) :
    IsClosed (lorentzPositiveOrthogonalGroup n : Set (GL (Fin (n+1)) ℝ)) := by
  have he : (lorentzPositiveOrthogonalGroup n : Set (GL (Fin (n+1)) ℝ)) =
      {A | A.val * lorentzJ n * A.valᵀ = lorentzJ n} ∩ {A | 1 ≤ A 0 0} := by
    ext A
    constructor
    · intro h
      exact ⟨h.1,lorentzPositive_time_ge_one h⟩
    · rintro ⟨hO,hp⟩
      exact ⟨hO,lt_of_lt_of_le zero_lt_one hp⟩
  rw [he]
  apply IsClosed.inter
  · exact isClosed_eq (by fun_prop) continuous_const
  · exact isClosed_le continuous_const (by fun_prop)

instance lorentzPositive_locallyCompactSpace (n : ℕ) :
    LocallyCompactSpace (lorentzPositiveOrthogonalGroup n) :=
  (lorentzPositiveOrthogonalGroup_isClosed n).locallyCompactSpace

theorem lorentzRowLinearMap_joint_continuous (n : ℕ) :
    Continuous (fun p : Matrix (Fin (n+1)) (Fin (n+1)) ℝ × LorentzVector n =>
      lorentzRowLinearMap p.1 p.2) := by
  change Continuous (fun p : Matrix (Fin (n+1)) (Fin (n+1)) ℝ × LorentzVector n => (lorentzCoordinates n).symm
    ((lorentzCoordinates n p.2) ᵥ* p.1))
  apply (lorentzCoordinates n).symm.continuous_of_finiteDimensional.comp
  apply continuous_pi
  intro i
  simp only [Matrix.vecMul,dotProduct]
  apply continuous_finsetSum
  intro j _
  exact ((continuous_apply j).comp
    ((lorentzCoordinates n).continuous_of_finiteDimensional.comp continuous_snd)).mul
      ((continuous_apply i).comp ((continuous_apply j).comp continuous_fst))

theorem lorentzHyperboloidMap_joint_continuous (n : ℕ) :
    Continuous (fun p : lorentzPositiveOrthogonalGroup n × Hyperboloid n =>
      lorentzHyperboloidMap p.1 p.2) := by
  apply Continuous.subtype_mk
  exact (lorentzRowLinearMap_joint_continuous n).comp
    ((Units.continuous_val.comp (continuous_subtype_val.comp continuous_fst)).prodMk
      (continuous_subtype_val.comp continuous_snd))

/-- The subgroup topology on positive Lorentz matrices is exactly its matrix-entry topology. -/
theorem lorentzPositive_matrix_isEmbedding (n : ℕ) :
    IsEmbedding (fun A : lorentzPositiveOrthogonalGroup n => A.val.val) := by
  let h : Matrix (Fin (n+1)) (Fin (n+1)) ℝ →
      Matrix (Fin (n+1)) (Fin (n+1)) ℝ × (Matrix (Fin (n+1)) (Fin (n+1)) ℝ)ᵐᵒᵖ :=
    fun M => (M,MulOpposite.op ((lorentzJ n * M * lorentzJ n)ᵀ))
  have hh : Continuous h := continuous_id.prodMk
    (MulOpposite.continuous_op.comp ((continuous_const.mul continuous_id).mul continuous_const).matrix_transpose)
  have he : h ∘ (fun A : lorentzPositiveOrthogonalGroup n => A.val.val) =
      Units.embedProduct (Matrix (Fin (n+1)) (Fin (n+1)) ℝ) ∘ Subtype.val := by
    funext A
    change (A.val.val,MulOpposite.op ((lorentzJ n * A.val.val * lorentzJ n)ᵀ)) =
      (A.val.val,MulOpposite.op A.val.inv)
    exact congrArg (fun M : Matrix (Fin (n+1)) (Fin (n+1)) ℝ => (A.val.val,MulOpposite.op M))
      (lorentzOrthogonal_inverse_matrix ((mem_lorentzPositiveOrthogonalGroup A.val).mp A.property).1).symm

  apply IsEmbedding.of_comp (Units.continuous_val.comp continuous_subtype_val) hh
  change IsEmbedding (h ∘ (fun A : lorentzPositiveOrthogonalGroup n => A.val.val))
  rw [he]
  exact Units.isEmbedding_embedProduct.comp IsEmbedding.subtypeVal


theorem lorentzPositive_tendsto_iff_matrix_entries {α : Type*} {p : Filter α}
    (F : α → lorentzPositiveOrthogonalGroup n) (A : lorentzPositiveOrthogonalGroup n) :
    Tendsto F p (𝓝 A) ↔ ∀ i j : Fin (n+1),
      Tendsto (fun a => (F a).val.val i j) p (𝓝 (A.val.val i j)) := by
  rw [(lorentzPositive_matrix_isEmbedding n).tendsto_nhds_iff]
  change Tendsto (fun a (i j : Fin (n+1)) => (F a).val.val i j) p
    (𝓝 (fun i j : Fin (n+1) => A.val.val i j)) ↔ _
  simp only [tendsto_pi_nhds]


section BoundaryTopology
variable [NeZero n]
attribute [local instance] Inversive.pureTranslationBoundaryChordalMetric Inversive.pureTranslationBoundaryMobiusMetric
  Inversive.pureTranslationBallMobiusMetric Inversive.pureTranslationBallPseudoMetric
  Inversive.pureTranslationBallPseudoEMetric
  Inversive.pureTranslationBallDist Inversive.pureTranslationBallEDist Inversive.pureTranslationBallUniform
  Inversive.pureTranslationBallTopology

instance ballMobius_sigmaCompactSpace : SigmaCompactSpace (Inversive.ballPreservingSubgroup n) := by
  let : SigmaCompactSpace (Matrix.orthogonalGroup (Fin (n+1)) ℝ) :=
    (isClosed_unitary (R := Matrix (Fin (n+1)) (Fin (n+1)) ℝ)).sigmaCompactSpace
  let : LocallyCompactSpace (unitBallDomain (n+1)) :=
    (unitBallDomain (n+1)).isOpen.locallyCompactSpace
  let : SigmaCompactSpace (unitBallDomain (n+1)) := inferInstance
  have h := isSigmaCompact_range (Inversive.orthogonalMatrixBallHomeomorph n).symm.continuous
  apply isSigmaCompact_univ_iff.mp
  simpa only [(Inversive.orthogonalMatrixBallHomeomorph n).symm.surjective.range_eq] using h

def ballMobiusEvaluation (f : Inversive.ballPreservingSubgroup n) (x : unitBallDomain (n+1)) :
    unitBallDomain (n+1) := ballHomeomorph f.val.val f.property x

omit [NeZero n] in
theorem ballMobiusEvaluation_coe (f : Inversive.ballPreservingSubgroup n) (x : unitBallDomain (n+1)) :
    ((ballMobiusEvaluation f x).val : Inversive.ExtendedEuclidean (n+1)) = f.val.val x.val :=
  ballHomeomorph_coe f.val.val f.property x

omit [NeZero n] in
theorem ballMobiusEvaluation_origin_translate (f : Inversive.ballPreservingSubgroup n)
    (x : unitBallDomain (n+1)) :
    ballMobiusEvaluation f x = Inversive.ballMobiusOrigin (f * (Inversive.pureTranslationBall x)⁻¹) := by
  apply Subtype.ext
  apply OnePoint.coe_injective
  have hx := congrArg (fun a : unitBallDomain (n+1) => (a.val : Inversive.ExtendedEuclidean (n+1)))
    (Inversive.ballMobiusOrigin_pureTranslation_inv x)
  have hzero : ((Inversive.ballMobiusOrigin ((Inversive.pureTranslationBall x)⁻¹)).val : Inversive.ExtendedEuclidean
    (n+1)) =
      ((Inversive.pureTranslationBall x)⁻¹).val.val (0 : Inversive.Euclidean (n+1)) :=
    ballHomeomorph_coe ((Inversive.pureTranslationBall x)⁻¹).val.val ((Inversive.pureTranslationBall x)⁻¹).property _
  have hprod : ((Inversive.ballMobiusOrigin (f * (Inversive.pureTranslationBall x)⁻¹)).val : Inversive.ExtendedEuclidean
    (n+1)) =
      f.val.val (((Inversive.pureTranslationBall x)⁻¹).val.val (0 : Inversive.Euclidean (n+1))) :=
    ballHomeomorph_coe (f * (Inversive.pureTranslationBall x)⁻¹).val.val (f * (Inversive.pureTranslationBall
      x)⁻¹).property _
  exact (ballMobiusEvaluation_coe f x).trans
    ((congrArg f.val.val (hx.symm.trans hzero)).trans hprod.symm)

theorem ballMobiusEvaluation_continuous (x : unitBallDomain (n+1)) :
    Continuous (fun f : Inversive.ballPreservingSubgroup n => ballMobiusEvaluation f x) := by
  simpa only [ballMobiusEvaluation_origin_translate,Function.comp_def,Pi.mul_apply,id_eq] using
    Inversive.ballMobiusOrigin_continuous.comp (continuous_id.mul continuous_const)

/-- The same actual ball action in the native positive hyperboloid model. -/
def ballMobiusHyperboloidMap (f : Inversive.ballPreservingSubgroup n) :
    Hyperboloid (n+1) → Hyperboloid (n+1) :=
  fun x => (hyperboloidBallHomeomorph (n+1)).symm
    (ballMobiusEvaluation f (hyperboloidBallHomeomorph (n+1) x))

omit [NeZero n] in
theorem ballMobiusEvaluation_one (x : unitBallDomain (n+1)) :
    ballMobiusEvaluation (1 : Inversive.ballPreservingSubgroup n) x = x := by
  apply Subtype.ext
  apply OnePoint.coe_injective
  exact ballHomeomorph_coe (1 : Inversive.ExtendedHomeomorph (n+1)) _ x

omit [NeZero n] in
theorem ballMobiusEvaluation_mul (f g : Inversive.ballPreservingSubgroup n)
    (x : unitBallDomain (n+1)) :
    ballMobiusEvaluation (f*g) x = ballMobiusEvaluation f (ballMobiusEvaluation g x) := by
  apply Subtype.ext
  apply OnePoint.coe_injective
  rw [ballMobiusEvaluation_coe,ballMobiusEvaluation_coe,ballMobiusEvaluation_coe]
  rfl

omit [NeZero n] in
theorem ballMobiusHyperboloidMap_one :
    ballMobiusHyperboloidMap (1 : Inversive.ballPreservingSubgroup n) = id := by
  funext x
  simp only [ballMobiusHyperboloidMap,ballMobiusEvaluation_one,Homeomorph.symm_apply_apply,id_eq]

omit [NeZero n] in
theorem ballMobiusHyperboloidMap_mul (f g : Inversive.ballPreservingSubgroup n)
    (x : Hyperboloid (n+1)) :
    ballMobiusHyperboloidMap (f*g) x = ballMobiusHyperboloidMap f (ballMobiusHyperboloidMap g x) := by
  simp only [ballMobiusHyperboloidMap,Homeomorph.apply_symm_apply,ballMobiusEvaluation_mul]

omit [NeZero n] in
theorem ballMobiusHyperboloidMap_isometry (f : Inversive.ballPreservingSubgroup n) :
    IsHyperboloidIsometry (ballMobiusHyperboloidMap f) := by
  apply (isHyperboloidIsometry_iff_dist _).mpr
  intro x y
  simp only [hyperboloidPathDist_eq_ballPathDist,ballMobiusHyperboloidMap,
    show hyperboloidProject = hyperboloidBallHomeomorph (n+1) from rfl,
    Homeomorph.apply_symm_apply,ballMobiusEvaluation]
  exact ballDensity_pathDist_invariant f.val.val f.val.property f.property _ _

theorem ballMobiusHyperboloidMap_continuous (x : Hyperboloid (n+1)) :
    Continuous (fun f : Inversive.ballPreservingSubgroup n => ballMobiusHyperboloidMap f x) :=
  (hyperboloidBallHomeomorph (n+1)).symm.continuous.comp
    (ballMobiusEvaluation_continuous (hyperboloidBallHomeomorph (n+1) x))

/-- The inverse of the row-action matrix: inversion makes the correspondence multiplicative
for the usual left composition law on transformations. -/
def ballMobiusLorentzMatrix (f : Inversive.ballPreservingSubgroup n) :
    lorentzPositiveOrthogonalGroup (n+1) :=
  (Classical.choose (hyperboloid_isometry_existsUnique_lorentzMatrix
    (ballMobiusHyperboloidMap_isometry f)))⁻¹

omit [NeZero n] in
theorem ballMobiusLorentzMatrix_spec (f : Inversive.ballPreservingSubgroup n)
    (x : Hyperboloid (n+1)) :
    lorentzHyperboloidMap (ballMobiusLorentzMatrix f)⁻¹ x = ballMobiusHyperboloidMap f x := by
  apply Subtype.ext
  change lorentzRowLinearMap
    ((Classical.choose (hyperboloid_isometry_existsUnique_lorentzMatrix
      (ballMobiusHyperboloidMap_isometry f)))⁻¹⁻¹).val.val x.val = _
  rw [inv_inv]
  exact ((Classical.choose_spec (hyperboloid_isometry_existsUnique_lorentzMatrix
    (ballMobiusHyperboloidMap_isometry f))).1 x).symm

omit [NeZero n] in
theorem ballMobiusLorentzMatrix_one :
    ballMobiusLorentzMatrix (1 : Inversive.ballPreservingSubgroup n) = 1 := by
  apply inv_injective
  apply lorentzHyperboloidMap_injective (n+1)
  funext x
  rw [ballMobiusLorentzMatrix_spec,ballMobiusHyperboloidMap_one,inv_one,lorentzHyperboloidMap_one]

omit [NeZero n] in
theorem ballMobiusLorentzMatrix_mul (f g : Inversive.ballPreservingSubgroup n) :
    ballMobiusLorentzMatrix (f*g) = ballMobiusLorentzMatrix f * ballMobiusLorentzMatrix g := by
  apply inv_injective
  apply lorentzHyperboloidMap_injective (n+1)
  funext x
  rw [ballMobiusLorentzMatrix_spec,_root_.mul_inv_rev,lorentzHyperboloidMap_mul,
    ballMobiusLorentzMatrix_spec,ballMobiusLorentzMatrix_spec,ballMobiusHyperboloidMap_mul]

def ballMobiusLorentzHom : Inversive.ballPreservingSubgroup n →* lorentzPositiveOrthogonalGroup (n+1) where
  toFun := ballMobiusLorentzMatrix
  map_one' := ballMobiusLorentzMatrix_one
  map_mul' := ballMobiusLorentzMatrix_mul

theorem lorentzRowMatrix_apply {m : ℕ} (T : LorentzVector m →ₗ[ℝ] LorentzVector m)
    (i j : Fin (m+1)) :
    lorentzRowMatrix T i j =
      lorentzCoordinates m (T ((lorentzCoordinates m).symm (Pi.single i 1))) j := by
  simp [lorentzRowMatrix,LinearMap.toMatrix'_apply]

omit [NeZero n] in
theorem ballMobiusLorentzMatrix_inv_matrix (f : Inversive.ballPreservingSubgroup n) :
    ((ballMobiusLorentzMatrix f)⁻¹).val.val =
      lorentzRowMatrix (hyperboloidFrameExtension (ballMobiusHyperboloidMap f)) := by
  apply lorentzRowLinearMap_injective (n+1)
  rw [lorentzRowLinearMap_rowMatrix]
  apply hyperboloidFrameExtension_unique
  intro x
  exact congrArg Subtype.val (ballMobiusLorentzMatrix_spec f x)

theorem ballMobiusFrameExtension_continuous (v : LorentzVector (n+1)) :
    Continuous (fun f : Inversive.ballPreservingSubgroup n =>
      hyperboloidFrameExtension (ballMobiusHyperboloidMap f) v) := by
  simp only [hyperboloidFrameExtension,Basis.constr_apply_fintype]
  apply continuous_finsetSum
  intro i _
  exact (continuous_const (y := ((hyperboloidFrameBasis (n+1)).equivFun v i : ℝ))).smul (continuous_subtype_val.comp
    (ballMobiusHyperboloidMap_continuous (hyperboloidFrame (n+1) i)))

theorem ballMobiusLorentzMatrix_inv_val_continuous :
    Continuous (fun f : Inversive.ballPreservingSubgroup n => ((ballMobiusLorentzMatrix f)⁻¹).val.val) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  simp only [ballMobiusLorentzMatrix_inv_matrix,lorentzRowMatrix_apply]
  exact (continuous_apply j).comp ((lorentzCoordinates (n+1)).continuous_of_finiteDimensional.comp
    (ballMobiusFrameExtension_continuous _))

theorem ballMobiusLorentzMatrix_val_continuous :
    Continuous (fun f : Inversive.ballPreservingSubgroup n => (ballMobiusLorentzMatrix f).val.val) := by
  have he : ∀ f : Inversive.ballPreservingSubgroup n,
      (ballMobiusLorentzMatrix f).val.val =
        (lorentzJ (n+1) * ((ballMobiusLorentzMatrix f)⁻¹).val.val * lorentzJ (n+1))ᵀ := by
    intro f
    have h := lorentzOrthogonal_inverse_matrix
      ((mem_lorentzPositiveOrthogonalGroup ((ballMobiusLorentzMatrix f)⁻¹).val).mp
        ((ballMobiusLorentzMatrix f)⁻¹).property).1
    change (((ballMobiusLorentzMatrix f)⁻¹)⁻¹).val.val = _ at h
    simpa only [inv_inv] using h
  simp only [he]
  exact ((continuous_const.mul ballMobiusLorentzMatrix_inv_val_continuous).mul continuous_const).matrix_transpose

theorem ballMobiusLorentzMatrix_continuous : Continuous (ballMobiusLorentzMatrix (n:=n)) := by
  apply Continuous.subtype_mk
  apply Units.continuous_iff.mpr
  exact ⟨ballMobiusLorentzMatrix_val_continuous,ballMobiusLorentzMatrix_inv_val_continuous⟩


/-- The genuine ball action determines its actual Möbius transformation. -/
theorem ballMobiusEvaluation_injective :
    Function.Injective (ballMobiusEvaluation (n:=n)) := by
  intro f g h
  have hball : EqOn f.val.val g.val.val (Inversive.extendedUnitBall : Set (Inversive.ExtendedEuclidean (n+1))) := by
    rintro z ⟨x,hx,rfl⟩
    have hx' : x ∈ unitBallDomain (n+1) := by simpa only [unitBallDomain,TopologicalSpace.Opens.mem_mk,Metric.mem_ball,dist_zero_right] using hx
    exact (ballMobiusEvaluation_coe f ⟨x,hx'⟩).symm.trans
      ((congrArg (fun a : unitBallDomain (n+1) => (a.val : Inversive.ExtendedEuclidean (n+1)))
        (congrFun h ⟨x,hx'⟩)).trans (ballMobiusEvaluation_coe g ⟨x,hx'⟩))
  have hclosed := hball.closure f.val.val.continuous g.val.val.continuous
  rw [Inversive.closure_extendedUnitBall] at hclosed
  apply (cayleyPoincareEquiv (n:=n)).symm.injective
  apply Subtype.ext
  apply Homeomorph.ext
  intro z
  rw [Inversive.cayleyPoincareEquiv_symm_boundary,Inversive.cayleyPoincareEquiv_symm_boundary]
  apply (Inversive.extendedEquatorialEmbedding_injective n)
  apply (cayleyBall n).injective
  have hf := ballBoundaryAction_transport f.val.val f.property z
  have hg := ballBoundaryAction_transport g.val.val g.property z
  apply hf.trans
  apply Eq.trans _ hg.symm
  apply hclosed
  rw [← boundarySphereHomeomorph_coe]
  obtain ⟨x,hx,hxe⟩ := (boundarySphereHomeomorph n z).property
  exact ⟨x,Metric.sphere_subset_closedBall hx,hxe⟩

theorem ballMobiusHyperboloidMap_injective :
    Function.Injective (ballMobiusHyperboloidMap (n:=n)) := by
  intro f g h
  apply ballMobiusEvaluation_injective
  funext x
  have he := congrArg (fun k => hyperboloidBallHomeomorph (n+1)
    (k ((hyperboloidBallHomeomorph (n+1)).symm x))) h
  simpa only [ballMobiusHyperboloidMap,Homeomorph.apply_symm_apply] using he

theorem ballMobiusLorentzMatrix_injective :
    Function.Injective (ballMobiusLorentzMatrix (n:=n)) := by
  intro f g h
  apply ballMobiusHyperboloidMap_injective
  funext x
  rw [← ballMobiusLorentzMatrix_spec,← ballMobiusLorentzMatrix_spec,h]


/-- The action of a genuine positive Lorentz matrix in the hyperbolic ball.
The inverse is required by the source's row-vector convention. -/
def lorentzBallMap (A : lorentzPositiveOrthogonalGroup (n+1)) :
    unitBallDomain (n+1) → unitBallDomain (n+1) :=
  fun x => hyperboloidBallHomeomorph (n+1)
    (lorentzHyperboloidMap A⁻¹ ((hyperboloidBallHomeomorph (n+1)).symm x))

omit [NeZero n] in
theorem lorentzBallMap_pathDist (A : lorentzPositiveOrthogonalGroup (n+1))
    (x y : unitBallDomain (n+1)) :
    (ballDensity (n+1)).pathDist (lorentzBallMap A x) (lorentzBallMap A y) =
      (ballDensity (n+1)).pathDist x y := by
  have h := (isHyperboloidIsometry_iff_dist _).mp (lorentzHyperboloidMap_isometry A⁻¹)
    ((hyperboloidBallHomeomorph (n+1)).symm x) ((hyperboloidBallHomeomorph (n+1)).symm y)
  simpa only [hyperboloidPathDist_eq_ballPathDist,
    show hyperboloidProject = hyperboloidBallHomeomorph (n+1) from rfl,
    Homeomorph.apply_symm_apply,lorentzBallMap] using h

omit [NeZero n] in
theorem lorentzBallMap_one :
    lorentzBallMap (1 : lorentzPositiveOrthogonalGroup (n+1)) = id := by
  funext x
  simp only [lorentzBallMap,inv_one,lorentzHyperboloidMap_one,id_eq,Homeomorph.apply_symm_apply]

omit [NeZero n] in
theorem lorentzBallMap_mul (A B : lorentzPositiveOrthogonalGroup (n+1))
    (x : unitBallDomain (n+1)) :
    lorentzBallMap (A*B) x = lorentzBallMap A (lorentzBallMap B x) := by
  simp only [lorentzBallMap,_root_.mul_inv_rev,lorentzHyperboloidMap_mul,Homeomorph.symm_apply_apply]

omit [NeZero n] in
theorem ballMobiusLorentzMatrix_surjective :
    Function.Surjective (ballMobiusLorentzMatrix (n:=n)) := by
  intro A
  obtain ⟨g,hg⟩ := ball_pathDist_preserver_exists_mobius (lorentzBallMap A)
    (lorentzBallMap_pathDist A)
  refine ⟨g,?_⟩
  apply inv_injective
  apply lorentzHyperboloidMap_injective (n+1)
  funext x
  rw [ballMobiusLorentzMatrix_spec]
  apply (hyperboloidBallHomeomorph (n+1)).injective
  have he := hg (hyperboloidBallHomeomorph (n+1) x)
  simpa only [ballMobiusHyperboloidMap,Homeomorph.apply_symm_apply,
    lorentzBallMap,Homeomorph.symm_apply_apply,ballMobiusEvaluation] using he

theorem ballMobiusLorentzHom_isOpenMap
    :
    IsOpenMap (ballMobiusLorentzHom (n:=n)) :=
  MonoidHom.isOpenMap_of_sigmaCompact ballMobiusLorentzHom ballMobiusLorentzMatrix_surjective ballMobiusLorentzMatrix_continuous

/-- The actual ball Möbius group is the positive Lorentz matrix group. -/
def ballMobiusLorentzEquiv :
    Inversive.ballPreservingSubgroup n ≃* lorentzPositiveOrthogonalGroup (n+1) :=
  MulEquiv.ofBijective ballMobiusLorentzHom ⟨ballMobiusLorentzMatrix_injective,ballMobiusLorentzMatrix_surjective⟩

def ballMobiusLorentzTopologicalEquiv :
    Inversive.ballPreservingSubgroup n ≃ₜ* lorentzPositiveOrthogonalGroup (n+1) where
  toMulEquiv := ballMobiusLorentzEquiv
  continuous_toFun := ballMobiusLorentzMatrix_continuous
  continuous_invFun := (ballMobiusLorentzEquiv.toEquiv.toHomeomorphOfContinuousOpen
    ballMobiusLorentzMatrix_continuous ballMobiusLorentzHom_isOpenMap).symm.continuous


def cayleyPoincareTopologicalEquiv : Inversive.GM n ≃ₜ* Inversive.ballPreservingSubgroup n where
  toMulEquiv := cayleyPoincareEquiv
  continuous_toFun := Inversive.cayleyPoincareEquiv_isometry.continuous
  continuous_invFun := Inversive.cayleyPoincareEquiv_symm_isometry.continuous

def mobiusLorentzTopologicalEquiv :
    Inversive.GM n ≃ₜ* lorentzPositiveOrthogonalGroup (n+1) :=
  cayleyPoincareTopologicalEquiv.trans ballMobiusLorentzTopologicalEquiv

theorem mobius_tendstoUniformly_iff_lorentzMatrix_entries
    {α : Type*} {p : Filter α} (F : α → Inversive.GM n) (f : Inversive.GM n) :
    TendstoUniformly (fun a x => (F a : Inversive.ExtendedHomeomorph n) x)
      (fun x => (f : Inversive.ExtendedHomeomorph n) x) p ↔
      ∀ i j : Fin (n+2), Tendsto
        (fun a => (mobiusLorentzTopologicalEquiv (F a)).val.val i j) p
        (𝓝 ((mobiusLorentzTopologicalEquiv f).val.val i j)) := by
  rw [← Inversive.mobius_tendsto_iff_tendstoUniformly]
  rw [mobiusLorentzTopologicalEquiv.toHomeomorph.isEmbedding.tendsto_nhds_iff]
  exact lorentzPositive_tendsto_iff_matrix_entries _ _


def ballMobiusLorentzHomeomorph :
    Inversive.ballPreservingSubgroup n ≃ₜ lorentzPositiveOrthogonalGroup (n+1) :=
  ballMobiusLorentzTopologicalEquiv.toHomeomorph

theorem mobiusLorentzTopologicalEquiv_apply (g : Inversive.GM n) :
    mobiusLorentzTopologicalEquiv g = ballMobiusLorentzMatrix (cayleyPoincareEquiv g) := rfl

/-- With the actual groups and their established topologies. -/
def mobiusLorentzContinuousMulEquiv : Inversive.GM n ≃ₜ* lorentzPositiveOrthogonalGroup (n+1) :=
  mobiusLorentzTopologicalEquiv


omit [NeZero n] in
/-- Compatibility with the actual native ball action, not merely an abstract isomorphism. -/
theorem lorentzBallMap_ballMobiusLorentzMatrix (f : Inversive.ballPreservingSubgroup n)
    (x : unitBallDomain (n+1)) :
    lorentzBallMap (ballMobiusLorentzMatrix f) x = ballMobiusEvaluation f x := by
  simp only [lorentzBallMap,ballMobiusLorentzMatrix_spec,ballMobiusHyperboloidMap,
    Homeomorph.apply_symm_apply]

/-- The matrix acting on row vectors, before the inversion used by the group isomorphism. -/
def mobiusLorentzRowMatrix (g : Inversive.GM n) : Matrix (Fin (n+2)) (Fin (n+2)) ℝ :=
  ((mobiusLorentzTopologicalEquiv g)⁻¹).val.val

theorem mobiusLorentzRowMatrix_action (g : Inversive.GM n) (x : Hyperboloid (n+1)) :
    lorentzRowLinearMap (mobiusLorentzRowMatrix g) x.val =
      (ballMobiusHyperboloidMap (cayleyPoincareEquiv g) x).val :=
  congrArg Subtype.val (ballMobiusLorentzMatrix_spec (cayleyPoincareEquiv g) x)

theorem mobius_tendstoUniformly_iff_rowMatrix_entries
    {α : Type*} {p : Filter α} (F : α → Inversive.GM n) (f : Inversive.GM n) :
    TendstoUniformly (fun a x => (F a : Inversive.ExtendedHomeomorph n) x)
      (fun x => (f : Inversive.ExtendedHomeomorph n) x) p ↔
      ∀ i j : Fin (n+2), Tendsto (fun a => mobiusLorentzRowMatrix (F a) i j) p
        (𝓝 (mobiusLorentzRowMatrix f i j)) := by
  rw [← Inversive.mobius_tendsto_iff_tendstoUniformly]
  rw [mobiusLorentzTopologicalEquiv.toHomeomorph.isEmbedding.tendsto_nhds_iff]
  rw [(Homeomorph.inv (lorentzPositiveOrthogonalGroup (n+1))).isEmbedding.tendsto_nhds_iff]
  exact lorentzPositive_tendsto_iff_matrix_entries _ _

theorem mobius_tendstoUniformly_iff_rowMatrix
    {α : Type*} {p : Filter α} (F : α → Inversive.GM n) (f : Inversive.GM n) :
    TendstoUniformly (fun a x => (F a : Inversive.ExtendedHomeomorph n) x)
      (fun x => (f : Inversive.ExtendedHomeomorph n) x) p ↔
      Tendsto (fun a => mobiusLorentzRowMatrix (F a)) p (𝓝 (mobiusLorentzRowMatrix f)) := by
  rw [mobius_tendstoUniformly_iff_rowMatrix_entries]
  change _ ↔ Tendsto (fun a (i j : Fin (n+2)) => mobiusLorentzRowMatrix (F a) i j) p
    (𝓝 (fun i j : Fin (n+2) => mobiusLorentzRowMatrix f i j))
  simp only [tendsto_pi_nhds]


end BoundaryTopology
end LowDimensionalTopology.Geometry.Hyperbolic
