module
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.Conjugacy.ConjugacyClasses
public import LowDimensionalTopology.Geometry.Hyperbolic.Triangle.HalfPlaneIncenter
public import LowDimensionalTopology.Geometry.Hyperbolic.Triangle.IdealTriangleData
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.ReflectionProductTraces
public import LowDimensionalTopology.Geometry.Hyperbolic.Triangle.TwoIdealTriangles
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.HalfPlane.FullHalfPlaneIsometries
public import Mathlib.Algebra.Group.Subgroup.Pointwise
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane OnePoint
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

theorem halfPlaneLineReflectionIsometry_sq (L : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry L ^ 2 = 1 := by
  apply IsometryEquiv.ext
  exact L.reflection_involutive

theorem halfPlaneLineReflectionIsometry_inv (L : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) :
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry L)⁻¹ = _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry L := by
  apply inv_eq_of_mul_eq_one_right
  simpa only [pow_two] using halfPlaneLineReflectionIsometry_sq L

theorem nativeHalfPlaneExtension_hSL (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.nativeHalfPlaneExtension (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) = _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusToFull (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) := by
  let F : _root_.LowDimensionalTopology.Geometry.Hyperbolic.fullHalfPlaneGroup :=
    ⟨_root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusToFull (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A), realSLMobius_image_openHalfPlane A⟩
  have hF : _root_.LowDimensionalTopology.Geometry.Hyperbolic.fullHalfPlaneIsometryEquiv F = _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A := by
    apply IsometryEquiv.ext
    intro z
    apply _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint_injective
    exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.fullHalfPlaneNativeEquiv_action F z).symm.trans (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action A z)
  change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.fullHalfPlaneIsometryEquiv.symm (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A)).val = F.val
  rw [← hF, _root_.LowDimensionalTopology.Geometry.Hyperbolic.fullHalfPlaneIsometryEquiv.symm_apply_apply]

theorem nativeHalfPlaneExtension_reflection (L : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) :
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.nativeHalfPlaneExtension (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry L)).val =
      _root_.LowDimensionalTopology.Geometry.Mobius.euclideanToComplexHom L.realReflection := by
  let R : _root_.LowDimensionalTopology.Geometry.Mobius.complexGeneralMobiusGroup :=
    ⟨_root_.LowDimensionalTopology.Geometry.Mobius.euclideanToComplexHom L.realReflection,
      ⟨L.realReflection, L.realReflection_isReflection.mem_generalMobiusGroup, rfl⟩⟩
  have hR : R.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet = _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet := by
    rw [← _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneBoundaryPoint_range]
    ext p
    constructor
    · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
      exact ⟨L.reflection z, (L.realReflection_coe z).symm⟩
    · rintro ⟨z, rfl⟩
      refine ⟨_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint (L.reflection z), mem_range_self _, ?_⟩
      exact (L.realReflection_coe (L.reflection z)).trans
        (congrArg _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint (L.reflection_involutive z))
  let F : _root_.LowDimensionalTopology.Geometry.Hyperbolic.fullHalfPlaneGroup := ⟨R, hR⟩
  have hF : _root_.LowDimensionalTopology.Geometry.Hyperbolic.fullHalfPlaneIsometryEquiv F = _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry L := by
    apply IsometryEquiv.ext
    intro z
    apply _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint_injective
    exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.fullHalfPlaneNativeEquiv_action F z).symm.trans (L.realReflection_coe z)
  change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.fullHalfPlaneIsometryEquiv.symm (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry L)).val.val = R.val
  rw [← hF, _root_.LowDimensionalTopology.Geometry.Hyperbolic.fullHalfPlaneIsometryEquiv.symm_apply_apply]

/-- Native conformality is exactly the genuine orientation condition of its global extension. -/
theorem halfPlane_native_conformal_iff (f : ℍ ≃ᵢ ℍ) :
    f ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup ↔
      _root_.LowDimensionalTopology.Geometry.Mobius.PreservesComplexOrientation (_root_.LowDimensionalTopology.Geometry.Hyperbolic.nativeHalfPlaneExtension f).val := by
  constructor
  · rintro ⟨A, rfl⟩
    change _root_.LowDimensionalTopology.Geometry.Mobius.PreservesComplexOrientation (_root_.LowDimensionalTopology.Geometry.Hyperbolic.nativeHalfPlaneExtension (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A)).val
    rw [nativeHalfPlaneExtension_hSL]
    exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).property.2
  · intro h
    let M : Mobius.complexMobiusGroup :=
      ⟨(_root_.LowDimensionalTopology.Geometry.Hyperbolic.nativeHalfPlaneExtension f).val, (_root_.LowDimensionalTopology.Geometry.Hyperbolic.nativeHalfPlaneExtension f).property, h⟩
    obtain ⟨A, hA⟩ := mobius_preserves_halfPlane_exists_SL M
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.nativeHalfPlaneExtension_preserves f)
    refine ⟨A, ?_⟩
    apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.nativeHalfPlaneExtension_injective
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.nativeHalfPlaneExtension (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) = _root_.LowDimensionalTopology.Geometry.Hyperbolic.nativeHalfPlaneExtension f
    rw [nativeHalfPlaneExtension_hSL, hA]
    rfl

theorem halfPlaneLineReflectionIsometry_not_conformal
    (L : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry L ∉ _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup := by
  rw [halfPlane_native_conformal_iff, nativeHalfPlaneExtension_reflection,
    _root_.LowDimensionalTopology.Geometry.Mobius.preservesOrientation_coordinates_iff]
  exact L.realReflection_isReflection.not_preservesOrientation

def triangleReflectionSides (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) : Set _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine :=
  {T.sideLineA, T.sideLineB, T.sideLineC}

/-- The group generated by the three genuine side reflections, with ideal vertices allowed. -/
def triangleReflectionGroup
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) : Subgroup (ℍ ≃ᵢ ℍ) :=
  Subgroup.closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry '' triangleReflectionSides T)

/-- Triangle reflection groups in the native hyperbolic plane. -/
def IsTriangleReflectionType (G : Subgroup (ℍ ≃ᵢ ℍ)) (α β γ : ℝ) : Prop :=
  ∃ T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle, T.alpha = α ∧ T.beta = β ∧ T.gamma = γ ∧
    G = triangleReflectionGroup T

/-- The actual conformal part of the original three-reflection group. -/
def triangleConformalGroup
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) : Subgroup (ℍ ≃ᵢ ℍ) :=
  triangleReflectionGroup T ⊓ _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup

def IsConformalTriangleType (G : Subgroup (ℍ ≃ᵢ ℍ)) (α β γ : ℝ) : Prop :=
  ∃ T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle, T.alpha = α ∧ T.beta = β ∧ T.gamma = γ ∧
    G = triangleConformalGroup T

/-- Every element is a finite word in the actual three side reflections. -/
theorem triangleReflectionGroup_mem_iff_word
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (f : ℍ ≃ᵢ ℍ) :
    f ∈ triangleReflectionGroup T ↔ ∃ l : List _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine,
      (∀ L ∈ l, L ∈ triangleReflectionSides T) ∧
        (l.map _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry).prod = f := by
  constructor
  · intro hf
    change f ∈ Subgroup.closure _ at hf
    refine Subgroup.closure_induction_left ?_ ?_ ?_ hf
    · exact ⟨[], by simp, rfl⟩
    · rintro x ⟨L, hL, rfl⟩ y _ ⟨l, hl, he⟩
      exact ⟨L :: l, by simpa only [List.mem_cons, forall_eq_or_imp] using And.intro hL hl,
        by simp only [List.map_cons, List.prod_cons, he]⟩
    · rintro x ⟨L, hL, rfl⟩ y _ ⟨l, hl, he⟩
      refine ⟨L :: l, by simpa only [List.mem_cons, forall_eq_or_imp] using And.intro hL hl, ?_⟩
      simp only [List.map_cons, List.prod_cons, he, halfPlaneLineReflectionIsometry_inv]
  · rintro ⟨l, hl, rfl⟩
    apply (triangleReflectionGroup T).list_prod_mem
    intro f hf
    obtain ⟨L, hL, rfl⟩ := List.mem_map.mp hf
    exact Subgroup.subset_closure ⟨L, hl L hL, rfl⟩

/-- The native reflection word has the same genuine global sphere action. -/
theorem nativeHalfPlaneExtension_reflectionWord
    (l : List _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) :
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.nativeHalfPlaneExtension (l.map _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry).prod).val =
      _root_.LowDimensionalTopology.Geometry.Mobius.euclideanToComplexHom (l.map _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.realReflection).prod := by
  induction l with
  | nil => simp
  | cons L l ih =>
    simp only [List.map_cons, List.prod_cons, map_mul, Subgroup.coe_mul,
      nativeHalfPlaneExtension_reflection, ih]

/-- Even length is equivalent to actual derivative-based conformality, independent of the word. -/
theorem halfPlane_reflectionWord_conformal_iff_even
    (l : List _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) :
    (l.map _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry).prod ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup ↔
      Even l.length := by
  rw [halfPlane_native_conformal_iff, nativeHalfPlaneExtension_reflectionWord,
    _root_.LowDimensionalTopology.Geometry.Mobius.preservesOrientation_coordinates_iff]
  have hr : ∀ f ∈ l.map _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.realReflection, _root_.LowDimensionalTopology.Geometry.Inversive.IsReflection f := by
    rintro f hf
    obtain ⟨L, _, rfl⟩ := List.mem_map.mp hf
    exact L.realReflection_isReflection
  simpa only [List.length_map] using
    _root_.LowDimensionalTopology.Geometry.Mobius.reflectionWord_preservesOrientation_iff_even (l.map _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.realReflection) hr

theorem triangleConformalGroup_mem_iff_even_word
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (f : ℍ ≃ᵢ ℍ) :
    f ∈ triangleConformalGroup T ↔ ∃ l : List _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine,
      (∀ L ∈ l, L ∈ triangleReflectionSides T) ∧
        (l.map _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry).prod = f ∧ Even l.length := by
  constructor
  · rintro ⟨hf, hc⟩
    obtain ⟨l, hl, rfl⟩ := (triangleReflectionGroup_mem_iff_word T f).mp hf
    exact ⟨l, hl, rfl, (halfPlane_reflectionWord_conformal_iff_even l).mp hc⟩
  · rintro ⟨l, hl, rfl, he⟩
    exact ⟨(triangleReflectionGroup_mem_iff_word T _).mpr ⟨l, hl, rfl⟩,
      (halfPlane_reflectionWord_conformal_iff_even l).mpr he⟩

/-- The geometric two actual conformal generators. -/
def trianglePairProductGroup
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) : Subgroup (ℍ ≃ᵢ ℍ) :=
  Subgroup.closure {_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry T.sideLineA *
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry T.sideLineB,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry T.sideLineC * _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry T.sideLineB}

theorem trianglePairProductGroup_pair_mem
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (L M : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine)
    (hL : L ∈ triangleReflectionSides T) (hM : M ∈ triangleReflectionSides T) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry L * _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry M ∈
      trianglePairProductGroup T := by
  let a := _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry T.sideLineA
  let b := _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry T.sideLineB
  let c := _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry T.sideLineC
  let K := trianglePairProductGroup T
  have hab : a * b ∈ K := Subgroup.subset_closure (Or.inl rfl)
  have hcb : c * b ∈ K := Subgroup.subset_closure (Or.inr (mem_singleton _))
  have ha : a⁻¹ = a := halfPlaneLineReflectionIsometry_inv _
  have hb : b⁻¹ = b := halfPlaneLineReflectionIsometry_inv _
  have hc : c⁻¹ = c := halfPlaneLineReflectionIsometry_inv _
  have haa : a * a = 1 := by simpa only [pow_two] using halfPlaneLineReflectionIsometry_sq T.sideLineA
  have hbb : b * b = 1 := by simpa only [pow_two] using halfPlaneLineReflectionIsometry_sq T.sideLineB
  have hcc : c * c = 1 := by simpa only [pow_two] using halfPlaneLineReflectionIsometry_sq T.sideLineC
  have hba : b * a ∈ K := by simpa only [mul_inv_rev, ha, hb] using K.inv_mem hab
  have hbc : b * c ∈ K := by simpa only [mul_inv_rev, hb, hc] using K.inv_mem hcb
  simp only [triangleReflectionSides, mem_insert_iff, mem_singleton_iff] at hL hM
  rcases hL with rfl | rfl | rfl <;> rcases hM with rfl | rfl | rfl
  · change a * a ∈ K
    rw [haa]
    exact K.one_mem
  · exact hab
  · have h := K.mul_mem hab hbc
    change a * c ∈ K
    rwa [mul_assoc, ← mul_assoc b b, hbb, one_mul] at h
  · exact hba
  · change b * b ∈ K
    rw [hbb]
    exact K.one_mem
  · exact hbc
  · have h := K.mul_mem hcb hba
    change c * a ∈ K
    rwa [mul_assoc, ← mul_assoc b b, hbb, one_mul] at h
  · exact hcb
  · change c * c ∈ K
    rw [hcc]
    exact K.one_mem

theorem triangle_even_word_mem_pairProductGroup
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (l : List _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine)
    (hl : ∀ L ∈ l, L ∈ triangleReflectionSides T) (he : Even l.length) :
    (l.map _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry).prod ∈ trianglePairProductGroup T := by
  induction l using List.twoStepInduction with
  | nil => simp
  | singleton L => simp at he
  | cons_cons L M l ih _ =>
    have hpair := trianglePairProductGroup_pair_mem T L M (hl L (by simp)) (hl M (by simp))
    have htail := ih (fun N hN => hl N (by simp [hN]))
      (by simpa only [List.length_cons, Nat.even_add_one, not_not] using he)
    simpa only [List.map_cons, List.prod_cons, mul_assoc] using
      (trianglePairProductGroup T).mul_mem hpair htail

/-- The conformal subgroup is generated by the two stated products of side reflections. -/
theorem triangleConformalGroup_eq_pairProductGroup
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) :
    triangleConformalGroup T = trianglePairProductGroup T := by
  apply le_antisymm
  · intro f hf
    obtain ⟨l, hl, rfl, he⟩ := (triangleConformalGroup_mem_iff_even_word T f).mp hf
    exact triangle_even_word_mem_pairProductGroup T l hl he
  · apply (Subgroup.closure_le _).mpr
    intro f hf
    simp only [mem_insert_iff, mem_singleton_iff] at hf
    rcases hf with rfl | rfl
    · exact (triangleConformalGroup_mem_iff_even_word T _).mpr
        ⟨[T.sideLineA, T.sideLineB], by simp [triangleReflectionSides], by simp, by simp⟩
    · exact (triangleConformalGroup_mem_iff_even_word T _).mpr
        ⟨[T.sideLineC, T.sideLineB], by simp [triangleReflectionSides], by simp, by simp⟩

/-- The original conformal subgroup viewed inside its actual full reflection group. -/
def triangleConformalKernel
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) : Subgroup (triangleReflectionGroup T) :=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup.subgroupOf (triangleReflectionGroup T)

theorem triangleConformalKernel_index_two (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) :
    (triangleConformalKernel T).index = 2 := by
  apply Subgroup.index_eq_two_iff.mpr
  have ha : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry T.sideLineA ∈ triangleReflectionGroup T :=
    Subgroup.subset_closure ⟨T.sideLineA, by simp [triangleReflectionSides], rfl⟩
  refine ⟨⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry T.sideLineA, ha⟩, ?_⟩
  intro b
  change Xor (b.val * _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry T.sideLineA ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup)
    (b.val ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup)
  obtain ⟨l, _, he⟩ := (triangleReflectionGroup_mem_iff_word T b.val).mp b.property
  have hw : ((l ++ [T.sideLineA]).map _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry).prod =
      b.val * _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry T.sideLineA := by
    simp only [List.map_append, List.prod_append, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one, he]
  rw [← hw, ← he, halfPlane_reflectionWord_conformal_iff_even,
    halfPlane_reflectionWord_conformal_iff_even, xor_iff_iff_not]
  simp only [List.length_append, List.length_singleton, Nat.even_add_one]

/-- The infinite-order convention uses a zero angle at an ideal vertex. -/
def triangleOrderAngle (p : ℕ∞) : ℝ :=
  if p = ⊤ then 0 else Real.pi / (p.toNat : ℝ)

/-- Triangle groups of prescribed corner orders, including ideal vertices through the infinite-order convention. -/
def IsTriangleGroupOfOrders (G : Subgroup (ℍ ≃ᵢ ℍ)) (p q r : ℕ∞) : Prop :=
  2 ≤ p ∧ 2 ≤ q ∧ 2 ≤ r ∧
    IsConformalTriangleType G (triangleOrderAngle p) (triangleOrderAngle q) (triangleOrderAngle r)

def IsTriangleGroup (G : Subgroup (ℍ ≃ᵢ ℍ)) : Prop :=
  ∃ p q r : ℕ∞, IsTriangleGroupOfOrders G p q r

theorem triangleOrderAngle_top : triangleOrderAngle ⊤ = 0 := by
  simp [triangleOrderAngle]

theorem triangleOrderAngle_nat (p : ℕ) : triangleOrderAngle p = Real.pi / p := by
  simp [triangleOrderAngle]

theorem triangleConformalGroup_type (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) :
    IsConformalTriangleType (triangleConformalGroup T) T.alpha T.beta T.gamma :=
  ⟨T, rfl, rfl, rfl, rfl⟩

theorem triangleReflectionGroup_type (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) :
    IsTriangleReflectionType (triangleReflectionGroup T) T.alpha T.beta T.gamma :=
  ⟨T, rfl, rfl, rfl, rfl⟩

theorem reflectionProductSL_native (L M : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry L * _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry M =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL L M) := by
  apply IsometryEquiv.ext
  intro z
  exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL_action L M z).symm

theorem reflectionProductSL_nonidentity
    (L M : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine)
    (hLM : L ≠ M) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL L M) ≠ 1 := by
  intro he
  have hnat : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL L M) = 1 := by
    apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.nativeHalfPlaneExtension_injective
    rw [nativeHalfPlaneExtension_hSL, he, map_one, map_one]
  have hprod : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry L * _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry M = 1 :=
    (reflectionProductSL_native L M).trans hnat
  have hsame : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry L = _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry M := by
    calc
      _ = (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry L * _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry M) *
          _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry M := by
        rw [mul_assoc, ← pow_two, halfPlaneLineReflectionIsometry_sq, mul_one]
      _ = _ := by rw [hprod, one_mul]
  apply hLM
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflection_injective
  exact congrArg (fun f : ℍ ≃ᵢ ℍ => (f : ℍ → ℍ)) hsame

theorem reflectionProductSL_common_ideal_parabolic
    (L M : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine)
    (hLM : L ≠ M)
    (p : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHalfPlaneModel)
    (hp : p.val ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneIdealBoundary)
    (hL : p ∈ L.closedCarrier) (hM : p ∈ M.closedCarrier) :
    _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL L M)) := by
  have heL := (L.closedCarrier_mem_ideal_iff p hp).mp hL
  have heM := (M.closedCarrier_mem_ideal_iff p hp).mp hM
  have hpar : M.Parallel L := by
    refine ⟨hLM.symm, p.val, Set.eq_singleton_iff_unique_mem.mpr ⟨⟨heM, heL⟩, ?_⟩⟩
    intro q hq
    exact M.idealEndpoints_inter_subsingleton L hLM.symm hq ⟨heM, heL⟩
  exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSL_parallel_reflections_parabolic _ (reflectionProductSL_nonidentity L M hLM) M L hpar
    (funext (_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL_action L M))

theorem reflectionProductSL_common_finite_elliptic
    (L M : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine)
    (hLM : L ≠ M)
    (p : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHalfPlaneModel)
    (hp : p.val ∉ _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneIdealBoundary)
    (hL : p ∈ L.closedCarrier) (hM : p ∈ M.closedCarrier) :
    _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL L M)) := by
  have hopen : p.val ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet := by
    have hc := (Set.ext_iff.mp _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHalfPlaneSet_eq_open_union_boundary p.val).mp p.property
    exact hc.resolve_right hp
  obtain ⟨z, hz, he⟩ := hopen
  let v : ℍ := ⟨z, hz⟩
  have hpv : p = _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToClosedModel v := Subtype.ext he.symm
  rw [hpv] at hL hM
  exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSL_reflection_intersection_elliptic _ (reflectionProductSL_nonidentity L M hLM) M L v
    ((M.closedCarrier_mem_interior_iff v).mp hM) ((L.closedCarrier_mem_interior_iff v).mp hL)
    (funext (_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL_action L M))

/-- Two distinct actual lines through any finite or ideal vertex give an elliptic or parabolic map. -/
theorem reflectionProductSL_common_closed_vertex_type
    (L M : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine)
    (hLM : L ≠ M)
    (p : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHalfPlaneModel)
    (hL : p ∈ L.closedCarrier)
    (hM : p ∈ M.closedCarrier) :
    _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL L M)) ∨
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL L M)) := by
  by_cases hp : p.val ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneIdealBoundary
  · exact Or.inr (reflectionProductSL_common_ideal_parabolic L M hLM p hp hL hM)
  · exact Or.inl (reflectionProductSL_common_finite_elliptic L M hLM p hp hL hM)

theorem triangle_sideLineAB_distinct
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) : T.sideLineA ≠ T.sideLineB := by
  intro h
  have he := congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.toDiscLine h
  change T.toDiscTriangle.sideLineA.toHalfPlane.toDiscLine =
    T.toDiscTriangle.sideLineB.toHalfPlane.toDiscLine at he
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.toHalfPlane_spec,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.toHalfPlane_spec] at he
  exact T.toDiscTriangle.b_not_mem_sideLineB (he ▸ T.toDiscTriangle.b_mem_sideLineA)

theorem triangle_sideLineCB_distinct
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) : T.sideLineC ≠ T.sideLineB :=
  T.toDiscTriangle.sideLineC_toHalfPlane_ne_sideLineB

/-- The first stated generator fixes the actual opposite vertex, which may be ideal. -/
theorem triangle_first_generator_type (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) :
    _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL T.sideLineA T.sideLineB)) ∨
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL T.sideLineA T.sideLineB)) := by
  apply reflectionProductSL_common_closed_vertex_type _ _ (triangle_sideLineAB_distinct T) T.c
  · exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.closedCarrier_cayley_mem _ T.c).mp T.toDiscTriangle.c_mem_sideLineA
  · exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.closedCarrier_cayley_mem _ T.c).mp T.toDiscTriangle.c_mem_sideLineB

/-- The second stated generator fixes the actual opposite vertex, which may be ideal. -/
theorem triangle_second_generator_type (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) :
    _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL T.sideLineC T.sideLineB)) ∨
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL T.sideLineC T.sideLineB)) := by
  apply reflectionProductSL_common_closed_vertex_type _ _ (triangle_sideLineCB_distinct T) T.a
  · exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.closedCarrier_cayley_mem _ T.a).mp T.toDiscTriangle.a_mem_sideLineC
  · exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.closedCarrier_cayley_mem _ T.a).mp T.toDiscTriangle.a_mem_sideLineB

theorem triangleConformalGroup_exists_two_elliptic_or_parabolic_generators
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) :
    ∃ A B : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      (_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) ∨ _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) ∧
      (_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B) ∨ _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)) ∧
      triangleConformalGroup T =
        Subgroup.closure {_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A, _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B} := by
  refine ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL T.sideLineA T.sideLineB,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL T.sideLineC T.sideLineB,
    triangle_first_generator_type T, triangle_second_generator_type T, ?_⟩
  rw [triangleConformalGroup_eq_pairProductGroup]
  simp only [trianglePairProductGroup, reflectionProductSL_native]

end LowDimensionalTopology.Geometry.Fuchsian
